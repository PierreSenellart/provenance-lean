#!/usr/bin/env python3
"""Run the conformance queries on PostgreSQL and write what it answers as Lean data.

Reads conformance/instances.sql and conformance/queries.sql, runs each query on
each instance in a PostgreSQL session over temporary tables, and writes
Provenance/Conformance/Expected.lean: the instances as plain relations, and the
answers to each query as lists of tuples. Values are non-negative integers and
NULL.

Usage: scripts/conformance.py [psql connection arguments]
       scripts/conformance.py --check
The second form checks that every query has its term or theorem in a module
Provenance/Conformance/F*.lean, with its SQL text in the docstring.
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INSTANCES = ROOT / "conformance" / "instances.sql"
QUERIES = ROOT / "conformance" / "queries.sql"
OUT = ROOT / "Provenance" / "Conformance" / "Expected.lean"
MARK = "-----8<-----"


def lean_value(v):
    if v == "NULL":
        return "nil"
    n = int(v)
    if n < 0:
        raise ValueError(f"negative value {n}: the value domain is the naturals")
    return f"val {n}"


def lean_rows(rows, arity):
    if not rows:
        return f"([] : List (Tuple V {arity}))"
    body = ",\n    ".join("![" + ", ".join(lean_value(v) for v in r) + "]" for r in rows)
    return f"([{body}]\n    : List (Tuple V {arity}))"


def parse_queries(text):
    out, name, buf = [], None, []
    for line in text.splitlines():
        m = re.match(r"--\s*name:\s*(\w+)\s*$", line)
        if m:
            if name:
                out.append((name, "\n".join(buf).strip()))
            name, buf = m.group(1), []
        elif name and line.strip():
            buf.append(line)
    if name:
        out.append((name, "\n".join(buf).strip()))
    return out


def psql(script, args):
    r = subprocess.run(["psql", "-X", "-q", "-A", "-F", "|", "-v", "ON_ERROR_STOP=1",
                        "-P", "null=NULL", "-P", "footer=off", *args],
                       input=script, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(r.stderr)
    return r.stdout


def parse_instances(text):
    """The schema, and the named instances with their INSERT statements."""
    schema, instances, cur = [], [], None
    for line in text.splitlines():
        m = re.match(r"--\s*instance:\s*(\w+)\s*$", line)
        if m:
            cur = (m.group(1), [])
            instances.append(cur)
        elif line.startswith("--") or not line.strip():
            continue
        elif cur is None:
            schema.append(line)
        else:
            cur[1].append(line)
    return "\n".join(schema) + "\n", [(n, "\n".join(ls) + "\n") for n, ls in instances]


def norm(sql):
    return " ".join(sql.split())


def lean_decls(root):
    """Every declaration of the conformance modules, with the docstring before it."""
    out = {}
    for f in sorted((root / "Provenance" / "Conformance").glob("F*.lean")):
        text = f.read_text()
        for m in re.finditer(r"/--(.*?)-/\s*(?:set_option[^\n]*\n)?(?:noncomputable )?"
                             r"(?:abbrev|def|theorem)\s+(\w+)", text, re.S):
            out[m.group(2)] = (f.name, norm(m.group(1)))
    return out


def check(queries):
    """Every query has its term or theorem in a module, with its SQL beside it."""
    decls = lean_decls(ROOT)
    bad = 0
    for name, sql in queries:
        hit = [d for d in (name + "_q", name + "_ok") if d in decls]
        if not hit:
            print(f"{name}: no {name}_q or {name}_ok in Provenance/Conformance/F*.lean")
            bad += 1
        elif not any(norm(sql) in decls[d][1] for d in hit):
            print(f"{name}: the SQL text is not in the docstring of {hit[0]} ({decls[hit[0]][0]})")
            bad += 1
    names = {n for n, _ in queries}
    for d, (f, _) in decls.items():
        if d.endswith("_ok") and d[:-3] not in names:
            print(f"{d} ({f}): no query of that name in conformance/queries.sql")
            bad += 1
    print(f"{len(queries)} queries checked against the modules, {bad} problem(s)")
    return bad


def main():
    args = [a for a in sys.argv[1:] if a != "--check"]
    queries = parse_queries(QUERIES.read_text())
    if "--check" in sys.argv[1:]:
        sys.exit(1 if check(queries) else 0)
    schema, instances = parse_instances(INSTANCES.read_text())
    tables = re.findall(r"CREATE TEMP TABLE (\w+)\(([^)]*)\)", schema)
    arities = [len(cols.split(",")) for _, cols in tables]
    k = len(instances)
    # results[j][i]: the rows of block j (tables, then queries) on instance i
    results = [[None] * k for _ in range(len(tables) + len(queries))]
    widths = [None] * (len(tables) + len(queries))
    for i, (_, inserts) in enumerate(instances):
        script = "BEGIN;\n" + schema + inserts
        for t, _ in tables:
            script += f"\\echo {MARK}\nSELECT * FROM {t};\n"
        for _, sql in queries:
            script += f"\\echo {MARK}\n{sql}\n"
        script += "ROLLBACK;\n"
        blocks = psql(script, args).split(MARK + "\n")[1:]
        assert len(blocks) == len(results)
        for j, b in enumerate(blocks):
            lines = b.splitlines()
            # the first line is the header, which gives the arity of an empty answer too
            widths[j] = len(lines[0].split("|"))
            results[j][i] = [line.split("|") for line in lines[1:]]
    version = psql("SHOW server_version;\n", args).splitlines()[1].strip()

    def per_instance(blocks, a):
        return "![" + ",\n   ".join(lean_rows(rows, a) for rows in blocks) + "]"

    L = []
    L.append("/-\n  Released under the MIT license as described in the file LICENSE.\n"
             "  Authors: Pierre Senellart\n-/\nmodule\n\npublic import Provenance.AggQuery\n")
    L.append("/-!\n# What PostgreSQL answers on the conformance queries\n\n"
             "Generated by `scripts/conformance.py` from `conformance/instances.sql` and\n"
             f"`conformance/queries.sql`, on PostgreSQL {version}; not edited by hand. Each\n"
             "instance is given as plain relations, and each answer, instance by instance,\n"
             "as the list of the tuples PostgreSQL returned, in the order it returned\n"
             "them, which the theorems read as a multiset. The instances are, in order:\n"
             + ", ".join(f"`{n}`" for n, _ in instances) + ".\n-/\n")
    L.append("@[expose] public section\n\nnamespace Conformance\n\nopen WithNull\n")
    L.append("/-- The value domain: the naturals and SQL's null. -/\nabbrev V := WithNull ℕ\n")
    L.append(f"/-- An instance, by its position in `conformance/instances.sql`. -/\n"
             f"abbrev Inst := Fin {k}\n")
    for j, ((t, cols), a) in enumerate(zip(tables, arities)):
        L.append(f"/-- The table `{t}({cols.strip()})`, instance by instance. -/\n"
                 f"abbrev {t}Rows : Inst → List (Tuple V {a}) :=\n  {per_instance(results[j], a)}\n")
    db = ", ".join(f'("{t}", ⟨{a}, ({t}Rows i : Multiset (Tuple V {a}))⟩)'
                   for (t, _), a in zip(tables, arities))
    L.append(f"/-- The instances. -/\nabbrev db (i : Inst) : Database V :=\n  [{db}]\n")
    for j, (name, sql) in enumerate(queries, start=len(tables)):
        a = widths[j]
        doc = sql.replace("-/", "- /")
        L.append(f"/-- PostgreSQL's answers to\n```sql\n{doc}\n```\n-/\n"
                 f"abbrev {name} : Inst → List (Tuple V {a}) :=\n  {per_instance(results[j], a)}\n")
    L.append("end Conformance\n")
    OUT.write_text("\n".join(L))
    print(f"{len(queries)} queries on {k} instances, PostgreSQL {version} -> {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
