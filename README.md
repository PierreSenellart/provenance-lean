# Lean4 formalization of some provenance notions

[![Continuous Integration](https://github.com/PierreSenellart/provenance-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/PierreSenellart/provenance-lean/actions/workflows/lean.yml)

This repository includes some Lean4 formal definitions and proofs
relevant for provenance in databases. One of the goal of this project is
to provide a formal semantics to the operations performed in the
provenance-aware relational database extension
[ProvSQL](https://github.com/PierreSenellart/provsql). This also
complements the description of the data model of ProvSQL provided in [a
technical paper](https://arxiv.org/abs/2504.12058).

This is work in progress. For now:

- [Database.lean](Provenance/Database.lean) defines tuples, relations,
  and (regular) databases
- [Query.lean](Provenance/Query.lean) defines the relational
  algebra
- [AnnotatedDatabase.lean](Provenance/AnnotatedDatabase.lean) defines annotated
  databases
- [SemiringWithMonus.lean](Provenance/SemiringWithMonus.lean) contains
  the definition of a *semiring with monus* (or *m-semiring*), along with
  some classical and useful theorems
- [QueryAnnotatedDatabase.lean](Provenance/QueryAnnotatedDatabase.lean) defines
  the semantics of relational algebra queries over annotated databases through m-semirings
- [QueryRewriting.lean](Provenance/QueryRewriting.lean) defines an
approach to query evaluation on annotated relations through query
rewriting; a proof (partially written at this point) that this
rewriting is correct is provided
- We include proofs that some common provenance m-semirings are indeed
  m-semirings:
  - [Bool.lean](Provenance/Semirings/Bool.lean): the Boolean m-semiring
  - [BoolFunc.lean](Provenance/Semirings/BoolFunc.lean): the Bool\[X\] m-semiring of Boolean functions over a set X of Boolean variables
  - [MinMax.lean](Provenance/Semirings/MinMax.lean): the min-max semiring over any bounded linear order, such as the security semiring or (the dual of) the fuzzy semiring
  - [Nat.lean](Provenance/Semirings/Nat.lean): the counting m-semiring
  - [Tropical.lean](Provenance/Semirings/Tropical.lean): the tropical m-semiring (for any linearly ordered commutative monoid with an additively absorbing ⊤ element, e.g., natural integers or reals with ∞ as ⊤)
  - [Which.lean](Provenance/Semirings/Which.lean): the Which\[X\] m-semiring (also called lineage or Lin\[X\])
  - [Why.lean](Provenance/Semirings/Why.lean): the Why\[X\] m-semiring

See [Example.lean](Provenance/Example.lean) for an example computation.

## License

These formal definitions and proofs are provided as open-source software under the MIT License. See [LICENSE](LICENSE).

## Contact

<https://github.com/PierreSenellart/provenance-lean>

Pierre Senellart <pierre@senellart.com>

Bug reports and feature requests are
preferably sent through the *Issues* feature of GitHub.
