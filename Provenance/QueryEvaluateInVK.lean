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
      -- By scope, `q_inner` is non-Agg and can be evaluated via the standard
      -- `evaluate` on the composite database; we lift the resulting tuples
      -- to `LiftedTK` pointwise.
      let r_inner_TK : Multiset (Tuple (T ⊕ K) m) := q_inner.evaluate d.toComposite
      let r_inner_VK : Multiset (Tuple (LiftedTK T K) m) :=
        r_inner_TK.map (fun tuple => fun k => LiftedTK.ofSum (tuple k))
      -- Group keys: distinct projections of `r_inner_VK` to the columns `is`.
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
  | _, q, d =>
      (q.evaluate d.toComposite).map (fun tuple => fun k => LiftedTK.ofSum (tuple k))

end Query

/-! ## (R5) Correctness (parked)

The intended statement of (R5)'s correctness is

```
⟪Agg is ts as q_inner⟫_Î = evaluateInVK (rewritingAgg is ts as q_inner hq_inner) Î
```

where `⟪·⟫` is the paper's Definition 7 annotated semantics in the
K-semimodule `V_K`. The codebase currently realises Definition 7
partially: `Query.evaluateAggSum` carries the K-tensor information
column-by-column but does not emit the δ-applied row-annotation column,
and its output type
`Multiset (Tuple T n₁ × Tuple (T × KTensor K T) n₂)` differs from
`evaluateInVK`'s `Multiset (Tuple (LiftedTK T K) (n₁ + n₂ + 1))`. Stating
a precise equality therefore requires a small bookkeeping bridge between
the two representations that is left for future work.

We park a *cardinality* form of the correctness theorem below as a
`sorry`: every group produces one row in both representations, so the
multiset cardinalities agree. The full structural equality lifts this to
agreement on data, K-tensor, and δ-applied annotation columns. -/

/-- (R5) correctness, cardinality form. The rewriting in V_K produces the
same number of output rows as `evaluateAggSum` (one per distinct group
key). The full structural equality is left as future work. -/
theorem Query.rewritingAgg_valid_card {m n₁ n₂ : ℕ}
    [AddCommSemigroup T] [Zero T]
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂) (as : Tuple AggFunc n₂)
    (q_inner : Query T m) (hq_inner : q_inner.noAgg)
    (Î : AnnotatedDatabase T K) :
    Multiset.card
        (Query.evaluateInVK (Query.rewritingAgg (K := K) is ts as q_inner hq_inner) Î)
      = Multiset.card (Query.evaluateAggSum is ts q_inner hq_inner Î) := by
  sorry
