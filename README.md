# Lean4 formalization of some provenance notions

This repository includes some Lean4 formal definitions proofs relevant
for provenance in databases.

This is work in progress. For now:

- [SemiringWithMonus.lean](Provenance/SemiringWithMonus.lean) contains
  the definition of a *semiring with monus* (or *m-semiring*), along with
  some classical and useful theorems
- We include proofs that some common provenance m-semirings are indeed
  m-semirings:
  - [Bool.lean](Provenance/Semirings/Bool.lean): the Boolean m-semiring
  - [Nat.lean](Provenance/Semirings/Nat.lean): the counting m-semiring
  - [Tropical.lean](Provenance/Semirings/Tropical.lean): the tropical m-semiring of natural numbers
  - [Which.lean](Provenance/Semirings/Why.lean): the Which\[X\] m-semiring (also called lineage or Lin\[X\])
  - [Why.lean](Provenance/Semirings/Why.lean): the Why\[X\] m-semiring

## License

These formal definitions and proofs are provided as open-source software under the MIT License. See [LICENSE](LICENSE).

## Contact

<https://github.com/PierreSenellart/provenance-lean>

Pierre Senellart <pierre@senellart.com>

Bug reports and feature requests are
preferably sent through the *Issues* feature of GitHub.
