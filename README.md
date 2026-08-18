# Provenance in databases, in Lean 4

[![CI](https://github.com/PierreSenellart/provenance-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/PierreSenellart/provenance-lean/actions/workflows/ci.yml)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.0-blue)](https://github.com/leanprover-community/mathlib4/releases/tag/v4.33.0)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21809151-007ec6)](https://doi.org/10.5281/zenodo.21809151)
[![Archived in Software Heritage](https://archive.softwareheritage.org/badge/origin/https://github.com/PierreSenellart/provenance-lean/)](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/PierreSenellart/provenance-lean)

A Lean 4 formalization of *database provenance* in the semiring framework of
Green, Karvounarakis and Tannen: relations whose tuples are annotated with
values from a semiring, an annotated relational algebra with difference and
aggregation, and the query rewriting by which
[ProvSQL](https://provsql.org/) computes provenance inside PostgreSQL.

The point of the library is to give those constructions a machine-checked
semantics, so that a claim made in a paper can be followed to a theorem the Lean
kernel has verified. **Full API documentation:**
<https://provsql.org/lean-docs/Provenance.html>.

## Papers

[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*, ICDE 2026](https://arxiv.org/abs/2504.12058)
links its definitions and results into the API documentation of this library.

Such links live in a PDF and cannot be fixed after the fact, so each published
paper gets a frozen module under `Provenance/Papers/`, restating its claims and
proving them by applying the declarations it cites: a weakened statement breaks
the build, and the anchors are checked separately by
[`scripts/check-anchors.sh`](scripts/check-anchors.sh).

## What is formalized

Everything below is proved in the library, whether or not it supports a
published paper. `lake build` is the test suite: there is no separate one, and
the development is `sorry`-free.

| Result | Module | Entry point |
| --- | --- | --- |
| m-semirings: monus from its Galois connection, the `δ` support operator, homomorphisms | `Provenance/SemiringWithMonus.lean` | `SemiringWithMonus`, `SemiringWithMonusHom` |
| twelve concrete provenance m-semirings: `𝔹`, `𝔹[X]`, `Why[X]`, `Lin[X]`, `ℕ[X]`, `ℕ`, tropical, Viterbi, min-max, Łukasiewicz, intervals and interval unions | `Provenance/Semirings/` | one file per semiring |
| annotated relational algebra with difference, and its provenance-aware rewriting into a plain query over `T ⊕ K` | `Provenance/QueryRewriting.lean` | `Query.rewriting_valid` |
| query evaluation commutes with any m-semiring homomorphism on `RA⁺(∖)` – the formal counterpart of ProvSQL's compile-once/evaluate-many architecture | `Provenance/QueryAnnotatedDatabaseHom.lean` | `Query.evaluateAnnotated_hom` |
| data-part adequacy of the annotated semantics against the plain one, and `𝔹`-support adequacy with transfer along monus homomorphisms | `Provenance/QueryAdequacy.lean`, `Provenance/SupportAdequacy.lean` | `Nat.counterexample_diff_adequacy` bounds it |
| probabilistic query evaluation: random worlds, the possible-worlds reading of `𝔹[X]` annotations, categorical blocks with deterministic-OR soundness | `Provenance/Probability.lean`, `Provenance/CategoricalBlock.lean` | `randomWorld_evaluateAnnotated` |
| Boolean provenance circuits, read-once and deterministic-decomposable correctness, and the Tseitin CNF encoding | `Provenance/Circuit.lean`, `Provenance/Tseitin.lean` | `Circuit`, `tseitin_equisat` |
| a **kind-indexed general query syntax** whose three column kinds (regular values, aggregate tokens, provenance values) mirror ProvSQL's regular / `agg_token` / uuid types, so the scope restrictions on aggregate results are static typing rather than side conditions | `Provenance/AggQuery.lean` | `AggQuery` |
| symbolic aggregate tokens and their semantics, invariant under permutations of tied group elements | `Provenance/AggValue.lean`, `Provenance/AggValueCongr.lean` | `AggValue`, `AggValue.predProv_congr` |
| the rewriting stated natively on that syntax, the rewriting of a bare `GROUP BY`, the `HAVING` site for a predicate mixing aggregate and regular atoms, and their **compositional closure** over arbitrary token-bearing plans | `Provenance/AggQueryRewriting.lean`, `Provenance/AggQueryGroupRewriting.lean`, `Provenance/AggQueryClosure.lean` | `AggQuery.rewritesTo_valid` |
| provenance of `HAVING`: its possible-world semantics, the algebraic identities behind counting aggregates, the corresponding probability identities under independence, a scan-computable form for `MIN`/`MAX`/`PICKFIRST`, and the enumeration algorithms with their correctness | `Provenance/HavingSemantics.lean`, `Provenance/Having.lean`, `Provenance/HavingProbability.lean`, `Provenance/HavingMinMax.lean`, `Provenance/Algorithms/` | `Having.havingProv` |
| complexity: non-zero `HAVING SUM` provenance is NP-complete in data complexity, with hardness by a first-order reduction and a size-honest encoding of concrete groups | `Provenance/HavingComplexity.lean` | `havingSumProv_ne_zero_iff`, `havingSumNonzeroHow_faithful` |

`Provenance/Example.lean` works a full annotated-database computation end to
end, in both the classical and the kind-indexed syntax; it is built as part of
the library, so its `#eval!`s double as executable regression checks.

## Layers

The library is layered, and the core ripples downward when touched:

1. **Algebra** – `SemiringWithMonus` and the concrete semirings under
   `Provenance/Semirings/`.
2. **Data** – `Database.lean` (tuples, relations, plain databases) and
   `AnnotatedDatabase.lean` (the same, annotated in an m-semiring `K`).
3. **Queries** – `Query.lean` (the classical syntax and its plain semantics),
   `QueryAnnotatedDatabase.lean` (the annotated semantics),
   `QueryRewriting.lean` (the rewriting into `T ⊕ K`).
4. **The general framework** – the `AggQuery*` family: the kind-indexed syntax,
   its evaluator, and the aggregation and `HAVING` results. This is the primary
   interface; the classical layer remains the proven engine several of its
   results reuse internally.
5. **Applications** – probability, circuits, algorithms, complexity.

## Releases

Version numbers are the library's own and follow
[semantic versioning](https://semver.org/). There is no compatibility contract
to state: nothing depends on this library, and `lean-toolchain` **at each tag is
authoritative** for the Mathlib the tag was checked against.

What a tag is for here is freezing a citable state, one that stays reachable
after the code has moved on. A citation should name a *version* DOI below
rather than the concept DOI, so that it points at a specific state of the code.

<!-- release-table -->
| Tag | Toolchain | Version DOI |
| --- | --- | --- |
| `v1.1.0` | `leanprover/lean4:v4.33.0` | – |
| `v1.0.0` | `leanprover/lean4:v4.33.0-rc1` | [10.5281/zenodo.21809152](https://doi.org/10.5281/zenodo.21809152) |
| `main` | see `lean-toolchain` | – |

## Building

The toolchain in `lean-toolchain` must match the pinned Mathlib version.

```
lake exe cache get   # fetch the Mathlib build cache
lake build           # build the whole library; this is the test suite
```

There is no separate test suite: correctness *is* the Lean kernel checking the
proofs, and the library is `sorry`-free.

Building the documentation is a separate project, `docbuild/`; see its
`Makefile`.

## Use as a dependency

Nothing is expected to depend on this library, but nothing prevents it either.
In a `lakefile.lean`:

```lean
require "provenance" from git
  "https://github.com/PierreSenellart/provenance-lean" @ "v1.1.0"
```

Pin a tag or a commit rather than `main`, for reproducible builds. Then
`import Provenance` brings in everything; import individual modules to keep
build times down. Besides Mathlib, the library depends on
[descriptive-complexity](https://github.com/PierreSenellart/descriptive-complexity/releases/tag/v1.2.0),
used to state the complexity results; Lake resolves one Mathlib per workspace,
so both must sit on the same pin.

One caveat: this package sets `backward.isDefEq.respectTransparency false`,
because its carriers (`Tuple`, `Relation`, `Database`, …) are deliberately
opaque `def`s that instance search must nevertheless see through. Package
options do **not** propagate to dependants, so a downstream project that
manipulates those carriers directly may need to set it too.

## Citing

Use the metadata in [`CITATION.cff`](CITATION.cff), and cite the version DOI of
the tag you used rather than the concept DOI, so that the citation names a
specific state of the code.

## Licence

MIT. See [LICENSE](LICENSE).

## Contact

Pierre Senellart <pierre@senellart.com> –
<https://github.com/PierreSenellart/provenance-lean>

Bug reports are welcome through GitHub *Issues*.
