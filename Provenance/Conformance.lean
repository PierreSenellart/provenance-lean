/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Conformance.F0
public import Provenance.Conformance.F1
public import Provenance.Conformance.F2
public import Provenance.Conformance.F3
public import Provenance.Conformance.F4
public import Provenance.Conformance.F5
public import Provenance.Conformance.F6
public import Provenance.Conformance.F7
public import Provenance.Conformance.F8
public import Provenance.Conformance.F9

/-!
# Conformance of the plain semantics with PostgreSQL

A suite of SQL queries, each written in the algebra, with the theorem that
the plain evaluator returns on a few small instances exactly the multiset
PostgreSQL returned. The queries are in `conformance/queries.sql`, the
instances in `conformance/instances.sql`, and PostgreSQL's answers in
`Provenance.Conformance.Expected`, which `scripts/conformance.py` generates
from the two.

There is one module per level of the chain of fragments. On the first three
levels a query is a term of the fragment syntax `FragQueryIn` and its
membership in the level is stated with it.

What the suite tests is the evaluator and the translation of each query as
a person wrote it down: the SQL and its term are paired by name, with the
SQL text in the docstring, and nothing derives one from the other.

The value domain is the naturals with a null, so what needs another domain
is left out: `avg`, `percent_rank` and `cume_dist`, whose values are not
integers; `ARRAY` subqueries and `array_agg`, whose values are arrays; and
the functions on strings and dates. Set-returning functions are left out
too.

Most proofs are a `decide`. Where a derived operator does not reduce in the
kernel – a cast on its column kinds, or the enumeration of a grouping set –
the proof first rewrites with the lemma of `Provenance.Derived` that says
what the operator computes, so that the test is still of the operator the
library defines.
-/
