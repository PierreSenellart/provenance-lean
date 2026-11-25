#!/usr/bin/env python3
"""Check ProvSQL's Boolean provenance on the conformance queries, world by world.

For every instance of conformance/instances.sql, every query of
conformance/queries.sql is run once by ProvSQL over the instance with every
table provenance-tracked. Then, for a set of worlds (subsets of the base rows),
the rows of ProvSQL's answer whose provenance is true in the world, with each
aggregate value read in that world, are compared, as a multiset, with what
PostgreSQL returns on the plain instance of that world.

That is the possible-world reading of Boolean provenance: a tuple's annotation
is true in a world exactly when the tuple is in the answer of the query on that
world. A semantics that commutes with semiring homomorphisms and agrees with SQL
over the Boolean semiring has it, however the query is spelled.

Which rows a world keeps is decided by ProvSQL itself (sr_boolean under a
mapping of the input tokens). The value of an aggregate in a world is read off
its circuit here: agg gates over semimod children, whose provenance sr_boolean
evaluates, and the arith and case gates over them, a case guard being evaluated
by sr_boolean too. An aggregate whose circuit has another gate, a guard that
sr_boolean does not evaluate, or an aggregate function not listed in AGGS is
not compared, and the report says so. An answer with no provsql column reads no
tracked data, and each of its rows is taken as present in every world.

Usage: scripts/provsql_worlds.py [--worlds N] [--seed S] [--only q1,q2] DSN
The database DSN must have the provsql extension; the script works in schemas
of its own, dropped at the end.
"""
import argparse
import importlib.util
import random
import re
import sys
from collections import Counter
from decimal import Decimal
from pathlib import Path

import psycopg

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("conformance", ROOT / "scripts" / "conformance.py")
conf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conf)

TRK, PLN = "worlds_trk", "worlds_pln"

# Aggregate functions whose value in a world is computed here, by name.
AGGS = {
    # ProvSQL's count is a sum of 0/1 values: 1 for a row counted, 0 for a
    # NULL argument or a row a FILTER leaves out
    "count": lambda vs: sum(v for v in vs if v is not None),
    "sum": lambda vs: sum(v for v in vs if v is not None) if any(v is not None for v in vs) else None,
    "min": lambda vs: min((v for v in vs if v is not None), default=None),
    "max": lambda vs: max((v for v in vs if v is not None), default=None),
    "choose": "choose",
}
INT_TYPES = {20, 21, 23}  # int8, int2, int4


class Unevaluable(Exception):
    pass


def norm(v):
    """A value as compared: integers whatever their SQL type, NULL as None."""
    if v is None:
        return None
    if isinstance(v, (int, bool)):
        return int(v)
    if isinstance(v, (Decimal, float)):
        if v == int(v):
            return int(v)
        return Decimal(v).normalize()
    if isinstance(v, str) and re.fullmatch(r"-?\d+", v):
        return int(v)
    return v


class Circuit:
    """The gates under the aggregate tokens of one answer, read once."""

    def __init__(self, cur):
        self.cur = cur
        self.gates = {}
        self.aggname = {}

    def load(self, roots):
        todo = [r for r in roots if r not in self.gates]
        while todo:
            self.cur.execute(
                "SELECT u, provsql.get_gate_type(u)::text, provsql.get_children(u),"
                " provsql.get_infos(u)::text, provsql.get_extra(u)"
                " FROM unnest(%s::uuid[]) u", (todo,))
            nxt = []
            for u, t, ch, infos, extra in self.cur.fetchall():
                i1, i2 = (int(x) for x in infos.strip("()").split(","))
                ch = [str(c) for c in ch or []]
                self.gates[str(u)] = (t, ch, i1, i2, extra)
                if t in ("agg", "arith"):
                    nxt += [c for c in ch if c not in self.gates]
                elif t == "case":
                    # (guard, value) pairs, then the else value: the guards
                    # are evaluated by sr_boolean, only the values followed
                    nxt += [c for k, c in enumerate(ch)
                            if (k % 2 == 1 or k == len(ch) - 1) and c not in self.gates]
                elif t == "semimod":
                    # the provenance child is evaluated by sr_boolean; only
                    # the value child is followed
                    nxt += [c for c in ch[1:] if c not in self.gates]
            todo = list(dict.fromkeys(nxt))
        aggs = [g[2] for g in self.gates.values() if g[0] == "agg" and g[2] not in self.aggname]
        if aggs:
            self.cur.execute("SELECT f, f::regproc::text FROM unnest(%s::oid[]) f", (list(set(aggs)),))
            for f, name in self.cur.fetchall():
                self.aggname[f] = name.split(".")[-1]

    def prov_tokens(self):
        """The provenance tokens of the semimod gates and the guards of the
        case gates, for sr_boolean."""
        out = {g[1][0] for g in self.gates.values() if g[0] == "semimod"}
        for g in self.gates.values():
            if g[0] == "case":
                ch = g[1]
                out |= {c for k, c in enumerate(ch) if k % 2 == 0 and k < len(ch) - 1}
        return out

    def value(self, u, truth):
        t, ch, i1, i2, extra = self.gates[u]
        if t == "value":
            return norm(extra) if extra not in (None, "") else None
        if t == "agg":
            name = self.aggname.get(i1)
            if name not in AGGS:
                raise Unevaluable(f"aggregate {name}")
            vals = []
            for c in ch:
                ct = self.gates[c]
                if ct[0] != "semimod":
                    raise Unevaluable(f"agg child {ct[0]}")
                prov, val = ct[1][0], ct[1][1]
                if truth[prov]:
                    vals.append(self.value(val, truth))
            if name == "choose":
                # any of the values: compared only where they agree
                vs = set(vals)
                if len(vs) > 1:
                    raise Unevaluable("choose over different values")
                return vs.pop() if vs else None
            return AGGS[name](vals)
        if t == "case":
            for k in range(0, len(ch) - 1, 2):
                if ch[k] not in truth:
                    raise Unevaluable("case guard that sr_boolean does not evaluate")
                if truth[ch[k]]:
                    return self.value(ch[k + 1], truth)
            return self.value(ch[-1], truth) if len(ch) % 2 == 1 else None
        if t == "arith":
            xs = [self.value(c, truth) for c in ch]
            op = i1
            if op in (5, 6):  # GREATEST / LEAST skip nulls
                xs = [x for x in xs if x is not None]
                return (max if op == 5 else min)(xs) if xs else None
            if any(x is None for x in xs):
                return None
            if op == 0:
                return sum(xs)
            if op == 1:
                r = 1
                for x in xs:
                    r *= x
                return r
            if op == 2:
                return xs[0] - xs[1]
            if op == 3:
                if xs[1] == 0:
                    raise Unevaluable("division by zero")
                if i2 in INT_TYPES:
                    q = abs(xs[0]) // abs(xs[1])
                    return q if (xs[0] >= 0) == (xs[1] >= 0) else -q
                return norm(Decimal(xs[0]) / Decimal(xs[1]))
            if op == 4:
                return -xs[0]
            raise Unevaluable(f"arith op {op}")
        raise Unevaluable(f"gate {t}")


def boolean_evaluable(cur, u):
    """Whether sr_boolean evaluates the token (it refuses, e.g., a comparison
    of values, which a case guard over aggregates can be)."""
    cur.execute("SAVEPOINT b")
    try:
        cur.execute(f"SELECT provsql.sr_boolean(%s::uuid, '{TRK}.worlds_map')", (u,))
    except psycopg.Error:
        cur.execute("ROLLBACK TO SAVEPOINT b")
        return False
    cur.execute("RELEASE SAVEPOINT b")
    return True


def setup_tracked(cur, schema_sql, inserts, tables):
    cur.execute(f"DROP SCHEMA IF EXISTS {TRK} CASCADE; CREATE SCHEMA {TRK}")
    cur.execute(f"SET search_path TO {TRK}, public, provsql")
    cur.execute(schema_sql.replace("CREATE TEMP TABLE", "CREATE TABLE"))
    if inserts.strip():
        cur.execute(inserts)
    for t, _ in tables:
        cur.execute("SELECT provsql.add_provenance(%s::regclass)", (f"{TRK}.{t}",))
    rows = []  # (table, token, values)
    for t, _ in tables:
        # tracked, a plain selection gives each row its own token as provsql
        cur.execute(f"SELECT * FROM {TRK}.{t}")
        names = [c.name for c in cur.description]
        pi = names.index("provsql")
        for r in cur.fetchall():
            rows.append((t, str(r[pi]), tuple(v for k, v in enumerate(r) if k != pi)))
    cur.execute(f"CREATE TABLE {TRK}.worlds_map(provenance uuid, value boolean)")
    cur.execute(f"INSERT INTO {TRK}.worlds_map SELECT tok, true FROM unnest(%s::uuid[]) tok",
                ([r[1] for r in rows],))
    return rows


def run_tracked(conn, cur, name, sql):
    """ProvSQL's answer: (regular rows with their token and agg columns, warnings)
    or an error message."""
    warnings = []

    def on_notice(d):
        if d.severity_nonlocalized == "WARNING":
            warnings.append(d.message_primary)

    conn.add_notice_handler(on_notice)
    cur.execute("SAVEPOINT q")
    try:
        body = sql.rstrip().rstrip(";")
        # the output columns, named c1, c2, ... so that duplicate names
        # (count, count) make a table; the provsql column keeps its name
        cur.execute(body)
        n = len([c for c in cur.description if c.name != "provsql"])
        names = ", ".join(f"c{k + 1}" for k in range(n))
        cur.execute(f"CREATE TABLE {TRK}.res_{name} ({names}) AS {body}")
    except psycopg.Error as e:
        cur.execute("ROLLBACK TO SAVEPOINT q")
        return None, f"{e.diag.message_primary}", warnings
    finally:
        conn.remove_notice_handler(on_notice)
    cur.execute("RELEASE SAVEPOINT q")
    cur.execute(
        "SELECT a.attname, a.atttypid = 'provsql.agg_token'::regtype FROM pg_attribute a"
        " WHERE a.attrelid = %s::regclass AND a.attnum > 0 AND NOT a.attisdropped ORDER BY a.attnum",
        (f"{TRK}.res_{name}",))
    cols = cur.fetchall()
    if not any(c == "provsql" for c, _ in cols):
        # no tracked data: every row is certain, as provenance() says
        cur.execute(f"SELECT * FROM {TRK}.res_{name}")
        one = "certain"
        return ([(one, list(r)) for r in cur.fetchall()], [False] * len(cols)), None, warnings
    # tracked, a plain selection gives each row its own token as provsql, and
    # an aggregate column its token as text
    cur.execute("SET provsql.aggtoken_text_as_uuid TO on")
    cur.execute(f"SELECT * FROM {TRK}.res_{name}")
    names = [c.name for c in cur.description]
    data = cur.fetchall()
    cur.execute("RESET provsql.aggtoken_text_as_uuid")
    agg = dict(cols)
    pi = names.index("provsql")
    isagg = [agg.get(n, False) for k, n in enumerate(names) if k != pi]
    rows = [(str(r[pi]), [str(v) if a and v is not None else v
                     for v, a in zip((v for k, v in enumerate(r) if k != pi), isagg)])
            for r in data]
    return (rows, isagg), None, warnings


def build_world(cur, schema_sql, tables, base_rows, world):
    cur.execute(f"DROP SCHEMA IF EXISTS {PLN} CASCADE; CREATE SCHEMA {PLN}")
    cur.execute(f"SET search_path TO {PLN}, public")
    cur.execute(schema_sql.replace("CREATE TEMP TABLE", "CREATE TABLE"))
    for t, cols in tables:
        vals = [v for (tt, tok, v) in base_rows if tt == t and tok in world]
        if vals:
            n = len(vals[0])
            cur.executemany(f"INSERT INTO {PLN}.{t} VALUES ({', '.join(['%s'] * n)})", vals)


def plain_answer(cur, sql):
    cur.execute("SAVEPOINT p")
    try:
        cur.execute(sql)
        out = Counter(tuple(norm(v) for v in r) for r in cur.fetchall())
    except psycopg.Error as e:
        cur.execute("ROLLBACK TO SAVEPOINT p")
        return None, e.diag.message_primary
    cur.execute("RELEASE SAVEPOINT p")
    return out, None


def worlds_for(tokens, n, rng):
    """The full and empty worlds, each world missing one row, and n random ones."""
    full = frozenset(tokens)
    ws = [full, frozenset()] + [full - {t} for t in tokens]
    ws += [frozenset(t for t in tokens if rng.random() < 0.5) for _ in range(n)]
    return list(dict.fromkeys(ws))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dsn")
    ap.add_argument("--worlds", type=int, default=64, help="random worlds per instance")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--only", default="", help="comma-separated query names")
    ap.add_argument("--show", type=int, default=2, help="mismatching worlds shown per query")
    args = ap.parse_args()

    queries = conf.parse_queries((ROOT / "conformance" / "queries.sql").read_text())
    if args.only:
        keep = set(args.only.split(","))
        queries = [(n, s) for n, s in queries if n in keep]
    schema_sql, instances = conf.parse_instances((ROOT / "conformance" / "instances.sql").read_text())
    tables = re.findall(r"CREATE TEMP TABLE (\w+)\(([^)]*)\)", schema_sql)
    rng = random.Random(args.seed)

    report = {n: {"status": "ok", "worlds": 0, "fail": [], "skipped": set(), "warn": set()}
              for n, _ in queries}
    with psycopg.connect(args.dsn, autocommit=False) as conn:
        cur = conn.cursor()
        cur.execute("SET client_min_messages TO warning")
        for iname, inserts in instances:
            base_rows = setup_tracked(cur, schema_sql, inserts, tables)
            answers = {}
            for name, sql in queries:
                ans, err, warns = run_tracked(conn, cur, name, sql)
                report[name]["warn"] |= set(warns)
                if err:
                    if report[name]["status"] == "ok":
                        report[name]["status"] = f"refused on {iname}: {err}"
                    continue
                circ = Circuit(cur)
                rows, isagg = ans
                circ.load([v for _, r in rows for v, a in zip(r, isagg) if a and v is not None])
                toks = sorted(({tok for tok, _ in rows} - {"certain"}) | circ.prov_tokens())
                toks = [u for u in toks if boolean_evaluable(cur, u)]
                answers[name] = (rows, isagg, circ, toks)
            tokens = [tok for _, tok, _ in base_rows]

            def absent(world, base_rows=base_rows):
                return [f"{t}{v}" for t, tok, v in base_rows if tok not in world]
            for world in worlds_for(tokens, args.worlds, rng):
                cur.execute(f"UPDATE {TRK}.worlds_map SET value = (provenance = ANY(%s::uuid[]))",
                            (list(world),))
                build_world(cur, schema_sql, tables, base_rows, world)
                for name, sql in queries:
                    if name not in answers:
                        continue
                    rows, isagg, circ, toks = answers[name]
                    cur.execute(f"SET search_path TO {TRK}, public, provsql")
                    cur.execute("SET provsql.active TO off")
                    cur.execute(f"SELECT u, provsql.sr_boolean(u, '{TRK}.worlds_map') FROM unnest(%s::uuid[]) u",
                                (toks,))
                    truth = {str(u): b for u, b in cur.fetchall()}
                    truth["certain"] = True
                    got = Counter()
                    for tok, r in rows:
                        if not truth[tok]:
                            continue
                        vals = []
                        for k, (v, a) in enumerate(zip(r, isagg)):
                            if not a:
                                vals.append(norm(v))
                            elif v is None:
                                vals.append(None)
                            else:
                                try:
                                    vals.append(circ.value(v, truth))
                                except Unevaluable as e:
                                    report[name]["skipped"].add(f"column {k + 1}: {e}")
                                    vals.append("?")
                        got[tuple(vals)] += 1
                    cur.execute(f"SET search_path TO {PLN}, public")
                    cur.execute("SET provsql.active TO on")
                    want, perr = plain_answer(cur, sql)
                    report[name]["worlds"] += 1
                    if perr:
                        report[name]["fail"].append((iname, absent(world), f"plain error: {perr}", None, None))
                        continue
                    # a column not evaluated is compared on the other columns only
                    skip = {k for k, a in enumerate(isagg) if a and "?" in [g[k] for g in got]}
                    if skip:
                        cut = lambda c: Counter({tuple(x for k, x in enumerate(t) if k not in skip): m
                                                 for t, m in c.items()})
                        g2, w2 = cut(got), cut(want)
                    else:
                        g2, w2 = got, want
                    if g2 != w2:
                        report[name]["fail"].append((iname, absent(world), None, g2 - w2, w2 - g2))
            conn.rollback()

    bad = 0
    for name, _ in queries:
        r = report[name]
        status = r["status"]
        if status == "ok" and r["fail"]:
            status = f"MISMATCH in {len(r['fail'])} of {r['worlds']} worlds"
            bad += 1
        elif status == "ok":
            status = f"ok ({r['worlds']} worlds)"
        print(f"{name}: {status}")
        for w in sorted(r["warn"]):
            print(f"    warning: {w}")
        for s in sorted(r["skipped"]):
            print(f"    not compared: {s}")
        for iname, gone, perr, extra, missing in r["fail"][:args.show]:
            desc = ", ".join(gone) if len(gone) <= 4 else f"{len(gone)} rows"
            print(f"    instance {iname}, world without {desc or 'any row missing'}:")
            if perr:
                print(f"      {perr}")
            else:
                print(f"      ProvSQL only: {dict(extra)}")
                print(f"      PostgreSQL only: {dict(missing)}")
    print(f"{len(queries)} queries, {bad} with a mismatch")


if __name__ == "__main__":
    main()
