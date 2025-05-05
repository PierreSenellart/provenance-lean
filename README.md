# Lean4 formalization of some provenance notions

This repository includes some Lean4 formal definitions proofs relevant
for provenance in databases.

This is work in progress. For now:

- [Provenance/SemiringWithMonus.lean](SemiringWithMonus.lean) contains
  the definition of a *semiring with monus* (or *m-semiring*)
- We include proofs that some common provenance m-semirings are indeed
  m-semirings:
  - [Provenance/Semirings/Bool.lean](Bool.lean): the Boolean m-semiring
  - [Provenance/Semirings/Nat.lean](Nat.lean): the counting m-semiring
  - [Provenance/Semirings/Why.lean](Why.lean): the Why[X] m-semiring
  - [Provenance/Semirings/Tropical.lean](Tropical.lean): the tropical m-semiring of natural numbers

## License

These formal definitions and proofs are provided as open-source software under the MIT License. See [LICENSE](LICENSE).

## Contact

<https://github.com/PierreSenellart/provenance-lean

Pierre Senellart <pierre@senellart.com>

Bug reports and feature requests are
preferably sent through the *Issues* feature of GitHub.
