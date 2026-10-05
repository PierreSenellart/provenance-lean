The formal results of the ICDE 2026 paper on ProvSQL, a system that keeps
track of the provenance and probability of data inside PostgreSQL, from
the provenance-lean library. The paper carried here is its arXiv version
(2504.12058, version 3), which the authors distribute under CC BY 4.0. The paper's claims live on an annotated
relational algebra: semirings with monus as annotations, relations as
finite multisets of tuples each carrying an annotation, and the operators
of the relational algebra with multiset semantics, projection, selection,
cross product, multiset sum, duplicate elimination and multiset
difference. Why-provenance is an m-semiring under union, pairwise union
and set difference of families of witnesses.

The main theorem is the correctness of the paper's provenance-aware
rewriting: a query over data is rewritten, operator by operator through
rules (R1) to (R4), into a query over the composite domain of data and
annotations whose last column carries the annotation, and the rewritten
query evaluated under multiset semantics computes exactly the annotated
semantics of the original query. The rewriting rules and the two
semantics are stated clause by clause as the paper gives them. A second
theorem, formalized after the paper, is the justification of ProvSQL's
intensional probabilistic query evaluation: on a database annotated with
Boolean functions over independent random variables, the marginal
probability of a tuple in the answer of a query is the probability of the
annotation of that tuple in the annotated answer.

The concepts restate the definitions of the library at its last commit on
the archive's toolchain, six after version 1.1.0, with the proofs of the
instances they carry; the proofs are the library's, sliced to what these
statements use, except for the grouping of duplicates, defined here
directly and shown to agree with the library's.
The library and its documentation are at
<https://github.com/PierreSenellart/provenance-lean> and
<https://provsql.org/lean-docs/Provenance.html>. The Lean code was
written with the assistance of several Claude models; the design and the
statements are the author's.
