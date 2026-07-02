/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/

/- Queries on annotated relations -/
import Provenance.QueryAnnotatedDatabase
import Provenance.QueryAnnotatedDatabaseHom

/- Data-part adequacy of the annotated semantics -/
import Provenance.QueryAdequacy

/- K-semimodules and the free K-tensor (aggregation foundation) -/
import Provenance.KSemiModule

/- The V_K-lifted value type and the rewriting evaluator -/
import Provenance.LiftedTK
import Provenance.QueryEvaluateInVK
import Provenance.QueryEvaluateInVKHom

/- Annotated semantics of the aggregation operator (sum, top-level) -/
import Provenance.QueryAggregation
import Provenance.QueryAggregationHom

/- HAVING algebraic identities -/
import Provenance.Having

/- Probability distributions over Boolean variables -/
import Provenance.Probability

/- Support adequacy over 𝔹 and transfer along monus homomorphisms -/
import Provenance.SupportAdequacy

/- Boolean circuits, read-once and d-D correctness -/
import Provenance.Circuit

/- Categorical-block probability and deterministic-OR (mulinput) soundness -/
import Provenance.CategoricalBlock

/- Probability identities for HAVING aggregate comparisons under independence -/
import Provenance.HavingProbability

/- Tseitin CNF encoding (equisatisfiability) -/
import Provenance.Tseitin

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

- `Provenance.SemiringWithMonus` – definition of a *semiring with monus* (m-semiring),
  the algebraic structure underlying annotated database semantics, together with general
  theorems about it
- `Provenance.Database` – tuples, relations, and plain databases
- `Provenance.Query` – relational algebra (select, project, join, union, difference…)
- `Provenance.AnnotatedDatabase` – databases annotated with values in an m-semiring `K`
- `Provenance.QueryAnnotatedDatabase` – semantics of relational algebra over annotated
  databases via m-semiring operations
- `Provenance.QueryAnnotatedDatabaseHom` – evaluation commutes with m-semiring
  homomorphisms ([Green, Karvounarakis & Tannen][green2007provenance],
  Proposition 3.5; [Geerts & Poggi][geerts2010database], Proposition 1)
- `Provenance.QueryAdequacy` – data-part adequacy of the annotated semantics:
  forgetting annotations turns annotated evaluation into plain evaluation of
  the difference-stripped query, exactly on the positive fragment (the
  annotation-generic analogue of the `ℕ`-adequacy theorem of
  [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini][benzaken2021coq])
  and as a sub-multiset inclusion in general
- `Provenance.QueryRewriting` – alternative query evaluation by rewriting plain queries
  on `T ⊕ K`; implements rules (R1)–(R5) of [Sen, Maniu & Senellart][sen2026provsql];
  `Query.rewriting_valid` proves the (R1)–(R4) cases, and the (R5) case is
  handled by `Query.rewriting_valid_full` in `Provenance.QueryEvaluateInVK`
- `Provenance.KSemiModule` – the `KSemiModule K M` typeclass (left action of a
  `CommSemiringWithMonus K` on a commutative monoid `M`) and the free `K`-tensor
  data structure `KTensor K M`, used to interpret the aggregation operator on
  `K`-annotated relations
  ([Amsterdamer, Deutch & Tannen][amsterdamer2011aggregate])
- `Provenance.QueryAggregation` – annotated semantics of the aggregation
  operator: `Query.evaluateAggSum` produces one row per group with per-aggregated
  -column `(value, K-tensor)` annotations, matching Definition 7 of
  [Sen, Maniu & Senellart][sen2026provsql]. First-cut scope: top-level
  aggregation only, `AggFunc.sum` only.
- `Provenance.QueryAggregationHom` – hom commutation for `evaluateAggSum`:
  pushing the database forward along a `SemiringWithMonusHom h : K → K'`
  is the same as pushing the K-tensor coefficients of the aggregated
  result forward along `h.toRingHom`.
- `Provenance.QueryEvaluateInVKHom` – **unified hom commutation** for the
  Definition 7 annotated semantics: `Query.evaluateAnnotatedFull_hom`
  subsumes both `Query.evaluateAnnotated_hom` (non-Agg) and
  `Query.evaluateAggSum_hom` (Agg) into a single theorem on the lifted
  output, exploiting the new `SemiringWithMonusHom.map_delta` field
  for the δ-applied row-annotation column.
- `Provenance.LiftedTK` – the value type `LiftedTK T K` extending `T ⊕ K` with
  K-tensor monomials, used as the V_K interpretation domain for the rewriting
  of aggregate queries.
- `Provenance.QueryEvaluateInVK` – `Query.evaluateInVK`, the V_K-aware
  evaluator that interprets a rewritten query (in particular the (R5)
  aggregation rewriting) in `LiftedTK`-valued tuples; together with
  `Query.evaluateAnnotatedFull` (the unified Definition 7 annotated
  semantics) and `Query.rewritingFull` (the unified rewriting of (R1)–(R5)
  in `Provenance.QueryRewriting`), this realises the single rewriting
  correctness theorem `Query.rewriting_valid_full`. R1–R3 are proven by
  reduction to `Query.rewriting_valid` (the legacy non-Agg theorem,
  retained as a helper); R5 is proven directly using the
  `Term.castToAnnotatedTuple_evalInVK`, `Term.evalInVK_index_last`,
  `LiftedTK.fold_add_ann`, `LiftedTK.fold_add_ktensor_nonempty`,
  and `KTensor.sum_map_embed` helpers.
- `Provenance.Having` – algebraic identities behind `HAVING (count)` aggregate
  provenance: include/exclude recurrences for the JOIN and possible-world expressions,
  and the upward-expansion bound
- `Provenance.Probability` – intensional probabilistic query evaluation: probability
  distribution over Boolean valuations, probability of a `BoolFunc X`, and the
  statement of Theorem 12 of [Sen, Maniu & Senellart][sen2026provsql] reducing
  `Pr(t ∈ q(Î))` to `Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`; the proof is reduced to a single
  structural commutation lemma `randomWorld_evaluateAnnotated`
- `Provenance.SupportAdequacy` – support adequacy over `𝔹`, for the full
  non-aggregation fragment (difference and duplicate elimination included):
  the support of the `𝔹`-annotated evaluation is the plain evaluation of the
  support of the database, and this transfers along any m-semiring
  homomorphism `K → 𝔹`. This is the equality that replaces `ℕ`-adequacy
  ([Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini][benzaken2021coq])
  beyond the positive fragment.
- `Provenance.Circuit` – Boolean circuits with structural predicates and
  two recursive bottom-up probability evaluators: the **read-once**
  evaluator with the inclusion-exclusion correction at OR gates
  (`Circuit.prob`), and the **d-D** evaluator with direct summation at
  OR gates under decomposability + determinism (`Circuit.probDD`). Both
  evaluators are proved correct against the sum-over-valuations
  semantics ([Sen, Maniu & Senellart][sen2026provsql], Section V-D
  step 1).
- `Provenance.CategoricalBlock` – the categorical-block counterpart of
  `Provenance.Circuit`'s d-D weighted-model-counting correctness: an
  independent re-proof over **categorical block variables** (the **free
  Boolean** case is the `κ ≡ fun _ => Bool` instance). A `CatAssignment`
  gives each block its own categorical distribution, `CatCircuit` has
  block-outcome literals,
  and `CatCircuit.dD_eventProb_eq_probDD` proves the direct-summation
  evaluator correct on decomposable + deterministic categorical circuits.
  The three block lemmas (`CatAssignment.mulin_disjoint`, `mulin_or_prob`,
  `mulin_none`) and `singleBlock_detOR_sound` back ProvSQL's trust in the
  deterministic-OR (`plus(mulinputs)`) mark and the `1 - Σ pᵢ` none-branch
  of the bounded-treewidth `repair_key` / BID route (`evaluateCertifiedIsland`).
- `Provenance.HavingProbability` – probability identities for evaluating
  `HAVING`-style aggregate comparisons under contributor independence:
  given pairwise-disjoint contributor variable supports (so contributors
  are independent Bernoullis with marginals `p i = P.funcProb (α i)`),
  the MAX / MIN factorisation formulas (`funcProb_maxLeOnNonempty` /
  `funcProb_minGeOnNonempty`) and the COUNT / SUM Poisson-binomial-style
  recurrences (`countMass_insert_zero` / `countMass_insert_succ` /
  `sumMass_insert_of_le` / `sumMass_insert_of_lt`).
- `Provenance.Tseitin` – the Tseitin CNF transformation encoding a
  circuit as an equisatisfiable CNF over `X ⊕ Circuit X`. Provides
  syntactic `Literal` / `Clause` / `CNF` types, the Tseitin encoder,
  and the bidirectional **equisatisfiability** theorem
  `Circuit.tseitin_equisat` ([Sen, Maniu & Senellart][sen2026provsql],
  Section V-D step 3, before the knowledge compiler is invoked).

**Algorithms**

- `Provenance.Algorithms.CompOp` – shared comparison-operator type used by the
  HAVING enumeration algorithms
- `Provenance.Algorithms.CountEnum` – enumeration of valid possible worlds for
  `HAVING count op C` predicates: definitions of `combinations`, `addExact`, and
  `countEnum`, together with the correctness theorem `countEnum_correct`
- `Provenance.Algorithms.SumDP` – subset-sum enumeration of valid possible
  worlds for `HAVING sum(t) op C` predicates: definition of `sumExact` and
  `sumDP`, together with the correctness theorem `sumDP_correct`

**Concrete m-semirings** (`Provenance.Semirings.*`)

- `Provenance.Semirings.Bool` – the Boolean m-semiring `𝔹`
- `Provenance.Semirings.BoolFunc` – the Boolean-function m-semiring `𝔹[X]`
- `Provenance.Semirings.Why` – the Why[X] m-semiring (sets of witness sets)
- `Provenance.Semirings.Which` – the Which[X] m-semiring (lineage / Lin[X])
- `Provenance.Semirings.How` – the ℕ[X] m-semiring of multivariate polynomials; the universal provenance
  semiring
- `Provenance.Semirings.Nat` – the counting m-semiring `ℕ`
- `Provenance.Semirings.Tropical` – the tropical m-semiring (min-plus) over `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, or
  `ℝ ∪ {∞}`; the `ℚ` instance is also used as a counterexample showing that the absorptive
  hypothesis of `Having.F_eq_S` is genuinely required (idempotent + `⊗`-over-`⊖` distributive
  is not enough)
- `Provenance.Semirings.Viterbi` – the Viterbi m-semiring (max-times) over `[0,1]`
- `Provenance.Semirings.MinMax` – the min-max semiring over any bounded linear order (security / access
  control semiring and dual fuzzy semiring)
- `Provenance.Semirings.Lukasiewicz` – the Łukasiewicz (fuzzy logic) m-semiring over `ℚ ∩ [0,1]`
- `Provenance.Semirings.Interval`, `Provenance.Semirings.IntervalUnion` – intervals and finite unions of intervals over a dense
  linear order, used for temporal databases

See `Provenance.Example` for an example annotated database computation.

## Related formalizations

[Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini][benzaken2021coq]
formalize K-relations in Coq/Rocq, for the *positive* relational algebra extended
with a single top-level aggregate, and prove an adequacy theorem: at `K = ℕ`,
the annotated semantics computes exactly the standard bag semantics of the
relational algebra. Their positivity restriction is essential to that theorem:
`ℕ`-adequacy fails as soon as monus-based difference interacts with duplicate
elimination (`Nat.counterexample_diff_adequacy` in
`Provenance.QueryAdequacy`). This library covers the non-monotone m-semiring
extension instead – monus difference, duplicate elimination, compositional
aggregation – and therefore anchors correctness differently: through
homomorphism commutation (`Provenance.QueryAnnotatedDatabaseHom`), the
rewriting correctness theorems (`Query.rewriting_valid`,
`Query.rewriting_valid_full`), the possible-worlds adequacy of the
Boolean-function annotated semantics (`randomWorld_evaluateAnnotated` in
`Provenance.Probability`), the `𝔹`-support adequacy and its transfer along
monus homomorphisms (`Provenance.SupportAdequacy`), and the data-part
adequacy results of `Provenance.QueryAdequacy`. Conversely, this library
does not treat NULL
values, correlated subqueries, or a SQL surface syntax, which the Coq/Rocq
development inherits from Datacert.

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Geerts & Poggi, *On database query languages for K-relations*][geerts2010database]
* [Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance]
* [Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the Provenance and Probability of Data*][sen2026provsql]
* [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini, *A Coq formalization of data provenance*][benzaken2021coq]
-/
