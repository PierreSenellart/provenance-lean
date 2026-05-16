/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/

/- Queries on annotated relations -/
import Provenance.QueryAnnotatedDatabase
import Provenance.QueryAnnotatedDatabaseHom

/- K-semimodules and the free K-tensor (aggregation foundation) -/
import Provenance.KSemiModule

/- HAVING algebraic identities -/
import Provenance.Having

/- Probability distributions over Boolean variables -/
import Provenance.Probability

/- Algorithms (HAVING enumeration) -/
import Provenance.Algorithms.CountEnum
import Provenance.Algorithms.SumDP

/- Various semirings -/
import Provenance.Semirings.Bool
import Provenance.Semirings.BoolFunc
import Provenance.Semirings.How
import Provenance.Semirings.IntervalUnion
import Provenance.Semirings.Lukasiewicz
import Provenance.Semirings.MinMax
import Provenance.Semirings.Nat
import Provenance.Semirings.Tropical
import Provenance.Semirings.Viterbi
import Provenance.Semirings.Which
import Provenance.Semirings.Why

/- Example -/
import Provenance.Example

/-!
# Provenance in databases

This Lean 4 library provides formal definitions and proofs relevant for *provenance in
databases*, following the semiring framework of
[Green, Karvounarakis & Tannen][green2007provenance] and
[Green & Tannen][green2017provenance].

One of the goals of this library is to provide a formal, machine-checked semantics for
the provenance-aware relational database system
[ProvSQL](https://provsql.org/) described in
[Sen, Maniu & Senellart][sen2026provsql].

## Contents

**Core theory**

- `Provenance.SemiringWithMonus` — definition of a *semiring with monus* (m-semiring),
  the algebraic structure underlying annotated database semantics, together with general
  theorems about it
- `Provenance.Database` — tuples, relations, and plain databases
- `Provenance.Query` — relational algebra (select, project, join, union, difference…)
- `Provenance.AnnotatedDatabase` — databases annotated with values in an m-semiring `K`
- `Provenance.QueryAnnotatedDatabase` — semantics of relational algebra over annotated
  databases via m-semiring operations
- `Provenance.QueryAnnotatedDatabaseHom` – evaluation commutes with m-semiring
  homomorphisms ([Green, Karvounarakis & Tannen][green2007provenance],
  Proposition 3.5; [Geerts & Poggi][geerts2010database], Proposition 1)
- `Provenance.QueryRewriting` — alternative query evaluation by rewriting plain queries
  on `T ⊕ K`; implements rules (R1)–(R5) of [Sen, Maniu & Senellart][sen2026provsql];
  correctness proof partially formalised
- `Provenance.KSemiModule` — the `KSemiModule K M` typeclass (left action of a
  `CommSemiringWithMonus K` on a commutative monoid `M`) and the free `K`-tensor
  data structure `KTensor K M`, used to interpret the aggregation operator on
  `K`-annotated relations
  ([Amsterdamer, Deutch & Tannen][amsterdamer2011aggregate])
- `Provenance.Having` — algebraic identities behind `HAVING (count)` aggregate
  provenance: include/exclude recurrences for the JOIN and possible-world expressions,
  and the upward-expansion bound
- `Provenance.Probability` — intensional probabilistic query evaluation: probability
  distribution over Boolean valuations, probability of a `BoolFunc X`, and the
  statement of Theorem 12 of [Sen, Maniu & Senellart][sen2026provsql] reducing
  `Pr(t ∈ q(Î))` to `Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`; the proof is reduced to a single
  structural commutation lemma `randomWorld_evaluateAnnotated`

**Algorithms**

- `Provenance.Algorithms.CompOp` — shared comparison-operator type used by the
  HAVING enumeration algorithms
- `Provenance.Algorithms.CountEnum` — enumeration of valid possible worlds for
  `HAVING count op C` predicates: definitions of `combinations`, `addExact`, and
  `countEnum`, together with the correctness theorem `countEnum_correct`
  ([Sen, Maniu & Senellart][sen2026provsql], Algorithm 2)
- `Provenance.Algorithms.SumDP` — subset-sum enumeration of valid possible
  worlds for `HAVING sum(t) op C` predicates: definition of `sumExact` and
  `sumDP`, together with the correctness theorem `sumDP_correct`
  ([Sen, Maniu & Senellart][sen2026provsql], Algorithm 1)

**Concrete m-semirings** (`Provenance.Semirings.*`)

- `Provenance.Semirings.Bool` — the Boolean m-semiring `𝔹`
- `Provenance.Semirings.BoolFunc` — the Boolean-function m-semiring `𝔹[X]`
- `Provenance.Semirings.Why` — the Why[X] m-semiring (sets of witness sets)
- `Provenance.Semirings.Which` — the Which[X] m-semiring (lineage / Lin[X])
- `Provenance.Semirings.How` — the ℕ[X] m-semiring of multivariate polynomials; the universal provenance
  semiring
- `Provenance.Semirings.Nat` — the counting m-semiring `ℕ`
- `Provenance.Semirings.Tropical` — the tropical m-semiring (min-plus) over `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, or
  `ℝ ∪ {∞}`; the `ℚ` instance is also used as a counterexample showing that the absorptive
  hypothesis of `Having.F_eq_S` is genuinely required (idempotent + `⊗`-over-`⊖` distributive
  is not enough)
- `Provenance.Semirings.Viterbi` — the Viterbi m-semiring (max-times) over `[0,1]`
- `Provenance.Semirings.MinMax` — the min-max semiring over any bounded linear order (security / access
  control semiring and dual fuzzy semiring)
- `Provenance.Semirings.Lukasiewicz` — the Łukasiewicz (fuzzy logic) m-semiring over `ℚ ∩ [0,1]`
- `Provenance.Semirings.Interval`, `Provenance.Semirings.IntervalUnion` — intervals and finite unions of intervals over a dense
  linear order, used for temporal databases

See `Provenance.Example` for an example annotated database computation.

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Geerts & Poggi, *On database query languages for K-relations*][geerts2010database]
* [Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance]
* [Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the Provenance and Probability of Data*][sen2026provsql]
-/
