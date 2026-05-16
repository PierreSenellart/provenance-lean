/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.LiftedTK
import Provenance.QueryAggregation
import Provenance.QueryAnnotatedDatabase
import Provenance.QueryRewriting

/-!
# Evaluating rewritten queries in the V_K-lifted semantics

This file defines `Query.evaluateInVK`, the V_K interpretation of a
rewritten query `q̂ : Query (T ⊕ K) n` evaluated against the composite
encoding `Î.toComposite` of a K-annotated database `Î`. It is the
"corrected" target of the rewriting rule (R5) of
[Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql], avoiding the
information loss that the plain `T ⊕ K` `Mul` introduces on mixed
operands.

## Why a separate evaluator

The rules (R1)–(R4) of `Query.rewriting` produce queries that only
multiply same-kind values (data × data or annotation × annotation), so
evaluating them via the standard `Query.evaluate` on `Î.toComposite`
yields the right semantics — the mixed `Mul` rule is never exercised.

The aggregation rule (R5) is different. Its per-column rewritten term is
`tⱼ * #(k+1)`, which evaluates `Sum.inl v * Sum.inr α` on the composite
tuple — and the existing `ValueType (T ⊕ K)` `Mul` collapses this to
`Sum.inl v`, dropping the K-side `α` before the aggregator ever sees it.
The paper resolves this by interpreting the rewritten aggregation in the
K-semimodule `V_K`, where the product is the K-tensor monomial `α ⊗ v`.

`Query.evaluateInVK` realises that interpretation:

* The result type is `Multiset (Tuple (LiftedTK T K) n)` rather than
  `Multiset (Tuple (T ⊕ K) n)`.
* For all non-`Agg` constructors, evaluation reduces to
  `Query.evaluate ∘ Î.toComposite` followed by a pointwise
  `LiftedTK.ofSum` lift. The two evaluators agree there because mixed
  `Mul` never fires.
* For `Agg`, the aggregator works directly on `LiftedTK` values: the
  per-row term is evaluated via `Term.evalInVK` (which uses `LiftedTK`'s
  K-tensor-producing `Mul`), and the per-column aggregator is interpreted
  in V_K — `AggFunc.sum` is multiset union on `KTensor K T`, and
  `AggFunc.sumDelta` is the same followed by a δ application on the K
  side.

## Scope

* Aggregation is assumed to occur at the **root only**, matching both the
  ICDE paper's convention and the constraint of the existing
  `Query.evaluateAggSum`. Nested aggregations (an `Agg` inside an
  `Agg`) are not exercised here.
* Filter predicates (`Sel`) inside the rewritten query operate on
  data-side values that were produced by `castToAnnotatedTuple`, so they
  never compare `ktensor` values. The reduction to the plain `evaluate`
  on `T ⊕ K` is safe for these.

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section IV-B,
  Definition 7, R5)
* [Amsterdamer, Deutch & Tannen][amsterdamer2011aggregate]
-/

universe u

variable {T : Type} [ValueType T]
variable {K : Type} [HasAltLinearOrder K] [CommSemiringWithMonus K] [DecidableEq K]

/-! ## Term evaluation in V_K -/

/-- Evaluate a term `Term (T ⊕ K) n` in V_K semantics, against a tuple of
`LiftedTK T K` values. The crucial point is that the `mul` case uses
`LiftedTK`'s `Mul`, which produces a `ktensor` monomial on mixed
`data v × ann α` operands. -/
def Term.evalInVK : Term (T ⊕ K) n → Tuple (LiftedTK T K) n → LiftedTK T K
  | .const x, _ => LiftedTK.ofSum x
  | .index k, tuple => tuple k
  | .add t₁ t₂, tuple => Term.evalInVK t₁ tuple + Term.evalInVK t₂ tuple
  | .sub t₁ t₂, tuple => Term.evalInVK t₁ tuple - Term.evalInVK t₂ tuple
  | .mul t₁ t₂, tuple => Term.evalInVK t₁ tuple * Term.evalInVK t₂ tuple

/-! ## δ on `LiftedTK` -/

namespace LiftedTK

/-- Apply the K-semiring's δ to the K-side of a `LiftedTK` value. Identity
on `data v`; applies `SemiringWithMonus.delta` on `ann α`; identity on
`ktensor t` (the un-quotiented representation does not support δ on
tensors, and the (R5) rewriting does not require it). -/
def applyDelta : LiftedTK T K → LiftedTK T K
  | .data v => .data v
  | .ann α => .ann (SemiringWithMonus.delta α)
  | .ktensor t => .ktensor t

end LiftedTK

/-! ## Query evaluation in V_K -/

namespace Query

/-- V_K interpretation of a rewritten query. See file docstring for
the design rationale and the scope (aggregation-at-root only). -/
noncomputable def evaluateInVK : ∀ {n}, Query (T ⊕ K) n →
    AnnotatedDatabase T K → Multiset (Tuple (LiftedTK T K) n)
  | _, @Query.Agg _ m n₁ n₂ is ts as q_inner, d =>
      -- Dispatch on whether the aggregation requires the V_K interpretation.
      -- Aggregations produced by (R3) and (R4) only use `AggFunc.sum`
      -- (because their aggregator is the plain K-side `⊕`); for those we
      -- fall through to the standard `evaluate ∘ toComposite ∘ ofSum-lift`,
      -- which is correctness-preserving. Aggregations produced by (R5) have
      -- at least one `AggFunc.sumDelta` aggregator (the δ-applied row
      -- annotation column), signalling that the V_K-specific interpretation
      -- is required to recover the K-tensor information.
      if _h : ∃ k : Fin n₂, as k = AggFunc.sumDelta then
        let r_inner_TK : Multiset (Tuple (T ⊕ K) m) := q_inner.evaluate d.toComposite
        let r_inner_VK : Multiset (Tuple (LiftedTK T K) m) :=
          r_inner_TK.map (fun tuple => fun k => LiftedTK.ofSum (tuple k))
        let groupKeys : Multiset (Tuple (LiftedTK T K) n₁) :=
          Multiset.dedup (r_inner_VK.map (fun tuple => fun k => tuple (is k)))
        groupKeys.map (fun g =>
          let matching : Multiset (Tuple (LiftedTK T K) m) :=
            r_inner_VK.filter (fun tuple => ∀ k', tuple (is k') = g k')
          let aggValues : Tuple (LiftedTK T K) n₂ := fun k =>
            let perRow : Multiset (LiftedTK T K) :=
              matching.map (fun u => (ts k).evalInVK u)
            let summed : LiftedTK T K := perRow.fold (· + ·) 0
            match as k with
            | AggFunc.sum => summed
            | AggFunc.sumDelta => LiftedTK.applyDelta summed
          Fin.append g aggValues)
      else
        ((@Query.Agg _ m n₁ n₂ is ts as q_inner).evaluate d.toComposite).map
          (fun tuple => fun k => LiftedTK.ofSum (tuple k))
  | _, q, d =>
      (q.evaluate d.toComposite).map (fun tuple => fun k => LiftedTK.ofSum (tuple k))

end Query

/-! ## Unified annotated semantics

`Query.evaluateAnnotatedFull` is the single annotated semantics that
matches the rewriting target. For non-aggregating queries it coincides
(via `AnnotatedRelation.toLifted`) with the existing
`Query.evaluateAnnotated`, and for top-level aggregations it is the
Definition 7 semantics of [Sen, Maniu & Senellart][sen2026provsql]:
each output row carries `n₁` grouping data values, `n₂` K-tensor
annotations (`Σ αᵤ ⊗ value_u_k`), and one δ-applied K annotation
(`δ(Σ αᵤ)`). The shared output type is
`Multiset (Tuple (LiftedTK T K) (n + 1))`. -/

/-- Unified `K`-annotated semantics in `LiftedTK` form. Dispatches on
whether the query is a top-level aggregation; otherwise lifts
`Query.evaluateAnnotated`. -/
noncomputable def Query.evaluateAnnotatedFull [AddCommSemigroup T] [Zero T] :
    ∀ {n}, (q : Query T n) → q.wellFormed → AnnotatedDatabase T K →
      Multiset (Tuple (LiftedTK T K) (n + 1))
  | _, @Query.Agg _ m n₁ n₂ is ts _as q_inner, h, Î =>
      -- Definition 7 (Sen-Maniu-Senellart): the per-column aggregator `f̂_k`
      -- is fixed to K-tensor sum (multiset union) and the row-annotation
      -- column is `δ(⊕)`; the user-specified `as` is irrelevant at this
      -- semantic level (its only role is in the rewriting target, where it
      -- distinguishes R3-style `sum` from R5-style `sumDelta`).
      let r_inner : Multiset (Tuple T m × K) := q_inner.evaluateAnnotated h Î
      let groupKeys : Multiset (Tuple T n₁) :=
        Multiset.dedup (r_inner.map (fun p => fun k : Fin n₁ => p.fst (is k)))
      groupKeys.map (fun g =>
        let matching : Multiset (Tuple T m × K) :=
          r_inner.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')
        Fin.append
          (Fin.append
            (fun k : Fin n₁ => LiftedTK.data (g k))
            (fun k : Fin n₂ =>
              LiftedTK.ktensor
                (matching.map (fun p => (p.snd, (ts k).eval p.fst)))))
          ![LiftedTK.ann (SemiringWithMonus.delta (matching.map Prod.snd).sum)])
  | _, Query.Rel n s, h, Î => ((Query.Rel n s).evaluateAnnotated h Î).toLifted
  | _, Query.Proj ts q', h, Î => ((Query.Proj ts q').evaluateAnnotated h Î).toLifted
  | _, Query.Sel φ q', h, Î => ((Query.Sel φ q').evaluateAnnotated h Î).toLifted
  | _, @Query.Prod _ _ _ _ hn q₁ q₂, h, Î =>
      ((@Query.Prod _ _ _ _ hn q₁ q₂).evaluateAnnotated h Î).toLifted
  | _, Query.Sum q₁ q₂, h, Î => ((Query.Sum q₁ q₂).evaluateAnnotated h Î).toLifted
  | _, Query.Dedup q', h, Î => ((Query.Dedup q').evaluateAnnotated h Î).toLifted
  | _, Query.Diff q₁ q₂, h, Î => ((Query.Diff q₁ q₂).evaluateAnnotated h Î).toLifted

/-! ## Unified rewriting correctness

The single theorem `Query.rewriting_valid_full` packages both the
(R1)–(R4) correctness (existing `Query.rewriting_valid`, parked R4
`sorry`s carried over) and the (R5) correctness (parked `sorry`) into a
uniform statement: for any well-formed query (no aggregation, or a
top-level aggregation with a non-aggregating inner query), the
`LiftedTK`-form annotated semantics agrees with the V_K interpretation
of the rewriting. -/

/-- **Unified rewriting correctness.** For any well-formed query `q`
(non-aggregating, or top-level aggregation with non-aggregating inner
query), the Def-7-style annotated semantics of `q` on `Î` matches the
V_K interpretation of the rewritten query on `Î.toComposite`. R1-R3 are
proven via the existing `Query.rewriting_valid` plus the bridge between
`AnnotatedRelation.toLifted` and the composite-then-lift on tuples; R4
and R5 are parked as `sorry`s alongside the existing ones. -/
theorem Query.rewriting_valid_full
    [AddCommSemigroup T] [Zero T]
    [HasAltLinearOrder K] {n : ℕ} (q : Query T n) (hq : q.wellFormed)
    (Î : AnnotatedDatabase T K) :
    Query.evaluateAnnotatedFull q hq Î
      = Query.evaluateInVK (Query.rewritingFull (K := K) q hq) Î := by
  -- For non-aggregating constructors, the unified evaluator is the existing
  -- `evaluateAnnotated` lifted via `toLifted`, and `evaluateInVK` on the
  -- rewriting is `(evaluate ∘ toComposite) ∘ map ofSum-on-tuples`. The
  -- `AnnotatedRelation.toLifted_eq_map_ofSum_toComposite` bridge plus the
  -- existing `Query.rewriting_valid` close every case mechanically.
  --
  -- The Agg case is parked alongside the existing R4/R5 sorries.
  induction q with
  | Rel n s =>
      show ((Query.Rel n s).evaluateAnnotated hq Î).toLifted = _
      rw [AnnotatedRelation.toLifted_eq_map_ofSum_toComposite,
          Query.rewriting_valid (Query.Rel n s) hq Î]
      rfl
  | Proj ts q' _ =>
      show ((Query.Proj ts q').evaluateAnnotated hq Î).toLifted = _
      rw [AnnotatedRelation.toLifted_eq_map_ofSum_toComposite,
          Query.rewriting_valid (Query.Proj ts q') hq Î]
      rfl
  | Sel φ q' _ =>
      show ((Query.Sel φ q').evaluateAnnotated hq Î).toLifted = _
      rw [AnnotatedRelation.toLifted_eq_map_ofSum_toComposite,
          Query.rewriting_valid (Query.Sel φ q') hq Î]
      rfl
  | @Prod n₁ n₂ n hn q₁ q₂ _ _ =>
      show ((@Query.Prod _ n₁ n₂ n hn q₁ q₂).evaluateAnnotated hq Î).toLifted = _
      rw [AnnotatedRelation.toLifted_eq_map_ofSum_toComposite,
          Query.rewriting_valid (@Query.Prod _ n₁ n₂ n hn q₁ q₂) hq Î]
      rfl
  | Sum q₁ q₂ _ _ =>
      show ((Query.Sum q₁ q₂).evaluateAnnotated hq Î).toLifted = _
      rw [AnnotatedRelation.toLifted_eq_map_ofSum_toComposite,
          Query.rewriting_valid (Query.Sum q₁ q₂) hq Î]
      rfl
  | Dedup q' _ =>
      show ((Query.Dedup q').evaluateAnnotated hq Î).toLifted = _
      rw [AnnotatedRelation.toLifted_eq_map_ofSum_toComposite,
          Query.rewriting_valid (Query.Dedup q') hq Î]
      rfl
  | Diff q₁ q₂ _ _ =>
      show ((Query.Diff q₁ q₂).evaluateAnnotated hq Î).toLifted = _
      rw [AnnotatedRelation.toLifted_eq_map_ofSum_toComposite,
          Query.rewriting_valid (Query.Diff q₁ q₂) hq Î]
      rfl
  | Agg _ _ _ _ _ =>
      -- (R5) case, parked.
      sorry
