#!/usr/bin/env python3
"""Run the conformance queries in ProvSQL and write their annotations as Lean data.

Reads conformance/instances.sql and conformance/queries.sql, runs each query in
ProvSQL over each instance with every table provenance-tracked, and writes
Provenance/Conformance/ExpectedAnn.lean: for each query and instance, the rows
ProvSQL returns with their annotation

* in the counting semiring, row k of the table at position p of the schema
  being annotated 2 + k + 10 p (sr_counting);
* in the Boolean semiring, under each valuation of VALUATIONS (sr_boolean).

Rows annotated zero are left out, as the semantics keeps tuples that no world
has where ProvSQL does not. An aggregate column is left blank (NULL): its
value with every row present is the plain answer, which the plain suite checks
against PostgreSQL, and in the other worlds it has no single value; except
where the Lean term of the query reads the column as a key (EXPLODE), where
the answer is exploded into one row per value. A query ProvSQL
refuses, or answers with a warning that it is not tracked, is left out, with
the reason in a comment; the other warnings ProvSQL gives on a query are kept
in the documentation of its answers.

Usage: scripts/conformance_ann.py DSN
The database DSN must have the provsql extension (1.15 or later, for
provenance() over no tracked relation); the script works in a schema of its
own, in a transaction it rolls back.
"""
import importlib.util
import re
import sys
from pathlib import Path

import psycopg

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "Provenance" / "Conformance" / "ExpectedAnn.lean"
spec = importlib.util.spec_from_file_location("conformance", ROOT / "scripts" / "conformance.py")
conf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conf)

SCHEMA = "conformance_ann"


def weight(p, k):
    """The counting annotation of row k of the table at position p."""
    return 2 + k + 10 * p


# The Boolean valuations, as functions of (p, k); their Lean counterparts are
# written below as valB.
VALUATIONS = [
    lambda p, k: (k + p) % 2 == 0,
    lambda p, k: (k + 2 * p) % 3 != 0,
]
VALUATIONS_LEAN = [
    "(k + p) % 2 == 0",
    "(k + 2 * p) % 3 != 0",
]


# The aggregate columns (numbered from 1) that the Lean term of a query reads as
# a key, through AggQueryIn.Explode: there ProvSQL's answer is exploded the way
# ProvSQL explodes an aggregate read as data (rewrite_explode_agg_values), one
# row per value the aggregate takes over the possible worlds, annotated with
# the comparison [c = v].
EXPLODE = {
    "rank_over_count": [2],
    "limit_on_count": [2],
}


def explode_sql(table, cols, arity):
    """The rows of table, its columns cols exploded into one row per value."""
    sel = ", ".join(f"v{k}::bigint AS c{k}" if k in cols else f"r.c{k}"
                    for k in range(1, arity + 1))
    lat = "".join(f", LATERAL unnest(provsql.agg_possible_values(r.c{k})) AS v{k}" for k in cols)
    cond = " AND ".join(f"((v{k} IS NULL AND r.c{k} IS NULL) OR r.c{k} = v{k}::bigint)"
                        for k in cols)
    return f"SELECT {sel} FROM {table} r{lat} WHERE {cond}"


def lean_value(v):
    if v is None:
        return "nil"
    if isinstance(v, bool):
        v = int(v)
    n = int(v)
    if n != v or n < 0:
        raise ValueError(f"value {v}: the value domain is the naturals")
    return f"val {n}"


def lean_ann(a):
    if isinstance(a, bool):
        return "true" if a else "false"
    return str(int(a))


def lean_rows(rows, arity, ktype):
    if not rows:
        return f"([] : List (Tuple V {arity} × {ktype}))"
    body = ",\n    ".join("(![" + ", ".join(lean_value(v) for v in r) + f"], {lean_ann(a)})"
                          for r, a in rows)
    return f"([{body}]\n    : List (Tuple V {arity} × {ktype}))"


def unagg(v):
    """The value of an aggregate column with every row present."""
    if v is None:
        return None
    if v.endswith(" (*)"):
        v = v[:-len(" (*)")]
    if v == "":
        return None
    if not re.fullmatch(r"\d+", v):
        raise ValueError(f"aggregate column printed as {v!r}")
    return int(v)


class Refused(Exception):
    pass


def query_warnings(dsn, schema_sql, inserts, tables, queries):
    """The warnings ProvSQL gives on each query, as a dictionary from the
    name of the query to the list of its warnings.

    Read in a session of their own that runs the queries only, so that the
    warnings are those of the queries and not of the semiring evaluations."""
    found = {}
    with psycopg.connect(dsn, prepare_threshold=None) as conn:
        cur = conn.cursor()
        warnings = []
        conn.add_notice_handler(
            lambda d: warnings.append((d.message_primary or "", d.message_detail or ""))
            if d.severity_nonlocalized == "WARNING" else None)
        cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA}_w CASCADE; CREATE SCHEMA {SCHEMA}_w")
        cur.execute(f"SET search_path TO {SCHEMA}_w, public, provsql")
        cur.execute(schema_sql.replace("CREATE TEMP TABLE", "CREATE TABLE"))
        if inserts.strip():
            cur.execute(inserts)
        for t, _ in tables:
            cur.execute("SELECT provsql.add_provenance(%s::regclass)", (f"{SCHEMA}_w.{t}",))
        for name, sql in queries:
            warnings.clear()
            cur.execute("SAVEPOINT q")
            try:
                cur.execute(sql.rstrip().rstrip(";"))
            except psycopg.Error:
                pass
            cur.execute("ROLLBACK TO SAVEPOINT q")
            cur.execute("RELEASE SAVEPOINT q")
            if warnings:
                found[name] = [f"{m} ({d})" if d else m for m, d in warnings]
        conn.rollback()
    return found


def main():
    dsn = sys.argv[1] if len(sys.argv) > 1 else ""
    queries = conf.parse_queries((ROOT / "conformance" / "queries.sql").read_text())
    schema_sql, instances = conf.parse_instances((ROOT / "conformance" / "instances.sql").read_text())
    tables = re.findall(r"CREATE TEMP TABLE (\w+)\(([^)]*)\)", schema_sql)
    # answers[name][i] = (arity, counting rows, [boolean rows per valuation])
    answers = {n: [None] * len(instances) for n, _ in queries}
    reasons = {}
    # warnings[name]: the warnings ProvSQL gives on the query, over all instances
    warnings_of = {n: [] for n, _ in queries}
    # no prepared statements: the same text reads answer tables of different types
    with psycopg.connect(dsn, prepare_threshold=None) as conn:
        cur = conn.cursor()
        cur.execute("SET client_min_messages TO warning")
        warnings = []
        conn.add_notice_handler(
            lambda d: warnings.append((d.message_primary or "", d.message_detail or ""))
            if d.severity_nonlocalized == "WARNING" else None)
        cur.execute("SELECT extversion FROM pg_extension WHERE extname = 'provsql'")
        provsql_version = cur.fetchone()[0]
        cur.execute("SHOW server_version")
        pg_version = cur.fetchone()[0]
        for i, (_, inserts) in enumerate(instances):
            warned = query_warnings(dsn, schema_sql, inserts, tables, queries)
            for n, ws in warned.items():
                warnings_of[n] += [w for w in ws if w not in warnings_of[n]]
            untracked = {n: next(w for w in ws if "not tracked" in w)
                         for n, ws in warned.items() if any("not tracked" in w for w in ws)}
            cur.execute(f"DROP SCHEMA IF EXISTS {SCHEMA} CASCADE; CREATE SCHEMA {SCHEMA}")
            cur.execute(f"SET search_path TO {SCHEMA}, public, provsql")
            cur.execute(schema_sql.replace("CREATE TEMP TABLE", "CREATE TABLE"))
            if inserts.strip():
                cur.execute(inserts)
            cur.execute(f"CREATE TABLE {SCHEMA}.map_n(provenance uuid, value int)")
            for j in range(len(VALUATIONS)):
                cur.execute(f"CREATE TABLE {SCHEMA}.map_b{j}(provenance uuid, value boolean)")
            for p, (t, _) in enumerate(tables):
                cur.execute("SELECT provsql.add_provenance(%s::regclass)", (f"{SCHEMA}.{t}",))
                # tracked, a plain selection gives each row its own token, in
                # the order the plain conformance data lists the rows
                cur.execute(f"SELECT provsql FROM {SCHEMA}.{t}")
                for k, (tok,) in enumerate(cur.fetchall()):
                    cur.execute(f"INSERT INTO {SCHEMA}.map_n VALUES (%s, %s)", (tok, weight(p, k)))
                    for j, val in enumerate(VALUATIONS):
                        cur.execute(f"INSERT INTO {SCHEMA}.map_b{j} VALUES (%s, %s)", (tok, val(p, k)))
            for name, sql in queries:
                body = sql.rstrip().rstrip(";")
                warnings.clear()
                cur.execute("SAVEPOINT q")
                try:
                    cur.execute(body)
                    arity = len([c for c in cur.description if c.name != "provsql"])
                    cols = [f"c{k + 1}" for k in range(arity)]
                    cur.execute(f"CREATE TABLE {SCHEMA}.res ({', '.join(cols)}) AS {body}")
                    if name in untracked:
                        raise Refused(untracked[name])
                    if name in EXPLODE:
                        cur.execute(f"CREATE TABLE {SCHEMA}.res_x AS "
                                    + explode_sql(f"{SCHEMA}.res", EXPLODE[name], arity))
                        cur.execute(f"DROP TABLE {SCHEMA}.res")
                        cur.execute(f"ALTER TABLE {SCHEMA}.res_x RENAME TO res")
                    cur.execute(
                        "SELECT attname, atttypid = 'provsql.agg_token'::regtype FROM pg_attribute"
                        " WHERE attrelid = %s::regclass AND attnum > 0 AND NOT attisdropped"
                        " AND attname <> 'provsql' ORDER BY attnum", (f"{SCHEMA}.res",))
                    kinds = cur.fetchall()
                    cur.execute(f"SELECT 1 FROM pg_attribute WHERE attrelid = '{SCHEMA}.res'::regclass"
                                " AND attname = 'provsql'")
                    has_prov = cur.fetchone() is not None
                    sel = ", ".join(f"{c}::text" if agg else c for c, agg in kinds)
                    if has_prov:
                        semirings = ([f"provsql.sr_counting(provsql, '{SCHEMA}.map_n')"]
                                     + [f"provsql.sr_boolean(provsql, '{SCHEMA}.map_b{j}')"
                                        for j in range(len(VALUATIONS))])
                    else:
                        # no tracked data: every row is certain
                        semirings = ["1"] + ["true"] * len(VALUATIONS)
                    cur.execute(f"SELECT {sel} FROM {SCHEMA}.res")
                    tuples = cur.fetchall()
                    # each semiring on its own: one may refuse what another evaluates
                    columns = []
                    for e in semirings:
                        cur.execute("SAVEPOINT s")
                        try:
                            cur.execute(f"SELECT {e} FROM {SCHEMA}.res")
                            columns.append([r[0] for r in cur.fetchall()])
                        except psycopg.Error as err:
                            cur.execute("ROLLBACK TO SAVEPOINT s")
                            cur.execute("RELEASE SAVEPOINT s")
                            columns.append(err.diag.message_primary)
                        else:
                            cur.execute("RELEASE SAVEPOINT s")
                    data = [(t, [c if isinstance(c, str) else c[k] for c in columns])
                            for k, t in enumerate(tuples)]
                except psycopg.Error as e:
                    cur.execute("ROLLBACK TO SAVEPOINT q")
                    cur.execute("RELEASE SAVEPOINT q")
                    reasons.setdefault(name, f"refused by ProvSQL: {e.diag.message_primary}")
                    continue
                except Refused as e:
                    cur.execute("ROLLBACK TO SAVEPOINT q")
                    cur.execute("RELEASE SAVEPOINT q")
                    reasons.setdefault(name, f"not tracked by ProvSQL: {e}")
                    continue
                cur.execute("ROLLBACK TO SAVEPOINT q")
                cur.execute("RELEASE SAVEPOINT q")
                isagg = [agg for _, agg in kinds]

                # An aggregate column is left blank (NULL): its value with
                # every row present is the plain answer, which the plain suite
                # checks, and in the other worlds it is no single value.
                def tup(r):
                    for v, a in zip(r[:arity], isagg):
                        if a:
                            unagg(v)  # still read, to refuse an unreadable one
                    return [None if a else v for v, a in zip(r[:arity], isagg)]

                try:
                    tups = [tup(t) for t, _ in data]
                except ValueError as e:
                    reasons.setdefault(name, f"not read here: {e}")
                    continue

                def rows_of(j, value):
                    # a semiring ProvSQL refused is recorded as its message
                    if isinstance(columns[j], str):
                        return columns[j]
                    return [(u, value(a[j])) for u, (_, a) in zip(tups, data) if a[j]]

                nrows = rows_of(0, lambda a: a)
                brows = [rows_of(1 + j, lambda a: True) for j in range(len(VALUATIONS))]
                answers[name][i] = (arity, nrows, brows)
        conn.rollback()

    L = []
    L.append("/-\n  Released under the MIT license as described in the file LICENSE.\n"
             "  Authors: Pierre Senellart\n-/\nmodule\n\npublic import Provenance.Conformance.Expected\n")
    L.append("/-!\n# What ProvSQL answers on the conformance queries, with annotations\n\n"
             "Generated by `scripts/conformance_ann.py` from `conformance/instances.sql` and\n"
             f"`conformance/queries.sql`, with ProvSQL {provsql_version} on PostgreSQL {pg_version};\n"
             "not edited by hand. Every table is provenance-tracked, and each answer is\n"
             "given, instance by instance, as the rows ProvSQL returned with their\n"
             "annotation, rows annotated zero left out:\n\n"
             "* in the counting semiring, row `k` of the table at position `p` of the schema\n"
             "  annotated `2 + k + 10 p` (`weightN`);\n"
             "* in the Boolean semiring, under each valuation `valB j` of the rows.\n\n"
             "An aggregate column is left blank (null): its value with every row present\n"
             "is the plain answer, which the plain suite checks; where the Lean term reads\n"
             "it as a key (`AggQueryIn.Explode`), the answer has one row per value it\n"
             "takes, annotated with ProvSQL's comparison of the aggregate with it.\n"
             "Queries ProvSQL refuses or does not track are left out, with the reason;\n"
             "the warnings ProvSQL gives on a query it answers are in the documentation\n"
             "of its answers.\n-/\n")
    L.append("@[expose] public section\n\nnamespace Conformance\n\nopen WithNull\n")
    L.append("/-- The counting annotation of row `k` of the table at position `p`. -/\n"
             "abbrev weightN (p k : ℕ) : ℕ := 2 + k + 10 * p\n")
    L.append(f"/-- The Boolean valuations of the rows, by their index. -/\n"
             f"abbrev Val := Fin {len(VALUATIONS)}\n")
    cases = "\n".join(f"  | ⟨{j}, _⟩, p, k => {e}" for j, e in enumerate(VALUATIONS_LEAN))
    L.append("/-- The truth of row `k` of the table at position `p` under valuation `j`. -/\n"
             f"def valB : Val → ℕ → ℕ → Bool\n{cases}\n")
    for name, _ in queries:
        warned = "".join(f"\n\nProvSQL warns: {w}" for w in warnings_of[name])
        if name in reasons:
            L.append(f"-- {name}: {reasons[name]}\n")
            continue
        a = answers[name][0][0]
        refusedN = [ans[1] for ans in answers[name] if isinstance(ans[1], str)]
        if refusedN:
            L.append(f"-- {name}, counting semiring: refused by ProvSQL: {refusedN[0]}\n")
        else:
            n_body = "![" + ",\n   ".join(lean_rows(ans[1], a, "ℕ") for ans in answers[name]) + "]"
            L.append(f"/-- ProvSQL's annotations over the counting semiring for `{name}`.{warned} -/\n"
                     f"abbrev {name}_annN : Inst → List (Tuple V {a} × ℕ) :=\n  {n_body}\n")
        refusedB = [b for ans in answers[name] for b in ans[2] if isinstance(b, str)]
        if refusedB:
            L.append(f"-- {name}, Boolean semiring: refused by ProvSQL: {refusedB[0]}\n")
        else:
            per_val = ",\n  ".join(
                "![" + ",\n   ".join(lean_rows(ans[2][j], a, "Bool") for ans in answers[name]) + "]"
                for j in range(len(VALUATIONS)))
            L.append(f"/-- ProvSQL's annotations over the Boolean semiring for `{name}`.{warned} -/\n"
                     f"abbrev {name}_annB : Val → Inst → List (Tuple V {a} × Bool) :=\n  ![{per_val}]\n")
    L.append("end Conformance\n")
    OUT.write_text("\n".join(L))
    done = len(queries) - len(reasons)
    print(f"{done} of {len(queries)} queries on {len(instances)} instances,"
          f" ProvSQL {provsql_version}, PostgreSQL {pg_version} -> {OUT.relative_to(ROOT)}")
    for n, r in reasons.items():
        print(f"  {n}: {r}")
    for n, ws in warnings_of.items():
        if n not in reasons:
            for w in ws:
                print(f"  {n}: warns: {w}")


if __name__ == "__main__":
    main()
