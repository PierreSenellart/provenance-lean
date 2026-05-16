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
“corrected” target of the rewriting rule (R5) of
[Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql], avoiding the
information loss that the plain `T ⊕ K` `Mul` introduces on mixed
operands.

## Why a separate evaluator

The rules (R1)–(R4) of `Query.rewriting` produce queries that only
multiply same-kind values (data × data or annotation × annotation), so
evaluating them via the standard `Query.evaluate` on `Î.toComposite`
yields the right semantics – the mixed `Mul` rule is never exercised.

The aggregation rule (R5) is different. Its per-column rewritten term is
`tⱼ * #(k+1)`, which evaluates `Sum.inl v * Sum.inr α` on the composite
tuple – and the existing `ValueType (T ⊕ K)` `Mul` collapses this to
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
  in V_K – `AggFunc.sum` is multiset union on `KTensor K T`, and
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

/-! ## Helper lemmas for the (R5) correctness proof

These lemmas isolate the small algebraic facts that make the V_K
interpretation of the rewritten aggregation match the Definition 7
annotated semantics:

* `Term.castToAnnotatedTuple_evalInVK` / `Term.evalInVK_index_last` –
  evaluating the rewritten per-column term `tⱼ * #(k+1)` on a `toLifted`
  tuple sees data on the left and an `ann α` on the right, so its V_K
  product produces the K-tensor monomial `α ⊗ vⱼ`.
* `fold_add_ann` / `fold_add_ktensor_nonempty` – folding a multiset of
  `LiftedTK.ann` (resp. non-empty `LiftedTK.ktensor`) cells with `(· + ·)`
  collapses to a single `ann` (resp. `ktensor`) wrapping the underlying
  carrier's sum.
* `KTensor.sum_map_embed` – summing a multiset of single-monomial
  K-tensors `α ⊗ v` recovers the underlying multiset of pairs `(α, v)`.

Together with the rewriting-correctness theorem on the inner query and
the bridge `toLifted_eq_map_ofSum_toComposite`, these reduce the per-key
body of the V_K-interpreted rewriting to the Definition 7 form. -/

omit [HasAltLinearOrder K] [DecidableEq K] in
/-- The V_K interpretation of a `castToAnnotatedTuple`-lifted term on a
`toLifted` tuple is the data-side evaluation: the original term ranges
over the first `m` data columns of `p.toLifted`, which are exactly the
`LiftedTK.data` wrappings of `p.fst`. -/
theorem Term.castToAnnotatedTuple_evalInVK
    {m : ℕ} (t : Term T m) (p : AnnotatedTuple T K m) :
    (Term.castToAnnotatedTuple (K := K) t).evalInVK p.toLifted
      = LiftedTK.data (t.eval p.fst) := by
  induction t with
  | const c =>
      show LiftedTK.ofSum (Sum.inl c) = _
      rfl
  | index k =>
      show p.toLifted (k.castLT _) = LiftedTK.data (p.fst k)
      unfold AnnotatedTuple.toLifted
      have h : k.castLT (k.val_lt_of_le (Nat.le_add_right m 1)) = Fin.castAdd 1 k := rfl
      rw [h, Fin.append_left]
  | add t₁ t₂ ih₁ ih₂ =>
      show HAdd.hAdd ((Term.castToAnnotatedTuple t₁).evalInVK p.toLifted)
            ((Term.castToAnnotatedTuple t₂).evalInVK p.toLifted) = _
      rw [ih₁, ih₂]
      rfl
  | sub t₁ t₂ ih₁ ih₂ =>
      show HSub.hSub ((Term.castToAnnotatedTuple t₁).evalInVK p.toLifted)
            ((Term.castToAnnotatedTuple t₂).evalInVK p.toLifted) = _
      rw [ih₁, ih₂]
      rfl
  | mul t₁ t₂ ih₁ ih₂ =>
      show HMul.hMul ((Term.castToAnnotatedTuple t₁).evalInVK p.toLifted)
            ((Term.castToAnnotatedTuple t₂).evalInVK p.toLifted) = _
      rw [ih₁, ih₂]
      rfl

omit [HasAltLinearOrder K] [DecidableEq K] in
/-- The V_K interpretation of the K-side index `#(m+1)` on a `toLifted`
tuple is the row's `LiftedTK.ann` annotation. -/
theorem Term.evalInVK_index_last
    {m : ℕ} (p : AnnotatedTuple T K m) :
    (Term.index (Fin.last m) : Term (T ⊕ K) (m + 1)).evalInVK p.toLifted
      = LiftedTK.ann p.snd := by
  show p.toLifted (Fin.last m) = _
  unfold AnnotatedTuple.toLifted
  show Fin.append _ _ (Fin.last m) = _
  have h : Fin.last m = Fin.natAdd m (0 : Fin 1) := rfl
  rw [h, Fin.append_right]
  rfl

omit [ValueType T] [HasAltLinearOrder K] [DecidableEq K] in
/-- Folding `(· + ·)` over a multiset of `LiftedTK.ann` cells (starting
from the additive identity `ann 0`) collapses to a single `ann` wrapping
the K-side multiset sum. -/
theorem LiftedTK.fold_add_ann [AddCommSemigroup T] (s : Multiset K) :
    ((s.map (LiftedTK.ann : K → LiftedTK T K)).fold (· + ·) 0
        : LiftedTK T K)
      = LiftedTK.ann s.sum := by
  induction s using Multiset.induction_on with
  | empty =>
      show (0 : LiftedTK T K) = LiftedTK.ann (0 : K)
      rfl
  | cons _ _ ih =>
      rw [Multiset.map_cons, Multiset.fold_cons_left, ih, Multiset.sum_cons]
      rfl

omit [ValueType T] [HasAltLinearOrder K] [DecidableEq K] in
/-- Folding `(· + ·)` over a non-empty multiset of `LiftedTK.ktensor` cells
collapses to a single `ktensor` wrapping the underlying `KTensor` sum.
Non-emptiness is required because the empty fold would return the
initial `ann 0`, which is not of the form `ktensor _`. -/
theorem LiftedTK.fold_add_ktensor_nonempty [AddCommSemigroup T]
    (s : Multiset (KTensor K T)) (h : s ≠ 0) :
    ((s.map (LiftedTK.ktensor : KTensor K T → LiftedTK T K)).fold (· + ·) 0
        : LiftedTK T K)
      = LiftedTK.ktensor s.sum := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl h
  | @cons a t ih =>
      rw [Multiset.map_cons, Multiset.fold_cons_left, Multiset.sum_cons]
      by_cases ht : t = 0
      · subst ht
        rw [Multiset.map_zero, Multiset.fold_zero, Multiset.sum_zero, add_zero]
        rfl
      · rw [ih ht]
        rfl

omit [ValueType T] [HasAltLinearOrder K] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A `simp`-friendly restatement of the
`toComposite + ofSum-on-tuples ↔ toLifted` bridge.

The lambda's return-type annotation `Tuple (LiftedTK T K) (m + 1)` is
load-bearing: without it, the lambda elaborates with the unfolded
function-type codomain `(k : Fin (m+1)) → LiftedTK T K`, which prevents
`rw`/`simp` from finding the pattern in `Query.evaluateInVK`'s goal,
whose `Multiset.map` carries the unfolded `Tuple`-named codomain. With
this annotation, `simp only [Multiset.map_ofSum_toComposite]` fires
reliably in the (R5) correctness proof. -/
@[simp] theorem Multiset.map_ofSum_toComposite {m : ℕ}
    (ar : AnnotatedRelation T K m) :
    @Multiset.map (Tuple (T ⊕ K) (m + 1)) (Tuple (LiftedTK T K) (m + 1))
        (fun tuple k => LiftedTK.ofSum (tuple k)) ar.toComposite
      = ar.toLifted :=
  (AnnotatedRelation.toLifted_eq_map_ofSum_toComposite ar).symm

omit [ValueType T] [CommSemiringWithMonus K] [HasAltLinearOrder K] [DecidableEq K] in
/-- Summing a multiset of single-monomial K-tensors `α ⊗ v` recovers the
underlying multiset of pairs `(α, v)`. -/
theorem KTensor.sum_map_embed {α : Type} (s : Multiset α) (f : α → K) (g : α → T) :
    (s.map (fun x => KTensor.embed (f x) (g x))).sum
      = (s.map (fun x => (f x, g x)) : Multiset (K × T)) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons a t ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons]
      show ({(f a, g a)} : Multiset (K × T)) + t.map (fun x => (f x, g x))
        = (f a, g a) ::ₘ t.map (fun x => (f x, g x))
      rw [Multiset.singleton_add]

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
`sorry`s carried over) and the (R5) correctness into a uniform
statement: for any well-formed query (no aggregation, or a top-level
aggregation with a non-aggregating inner query), the `LiftedTK`-form
annotated semantics agrees with the V_K interpretation of the
rewriting. -/

omit [HasAltLinearOrder K] in
/-- **Unified rewriting correctness.** For any well-formed query `q`
(non-aggregating, or top-level aggregation with non-aggregating inner
query), the Def-7-style annotated semantics of `q` on `Î` matches the
V_K interpretation of the rewritten query on `Î.toComposite`.

R1–R3 are proven via the existing `Query.rewriting_valid` plus the
bridge between `AnnotatedRelation.toLifted` and the composite-then-lift
on tuples; R4 is parked as a `sorry` (carried over from
`Query.rewriting_valid`). R5 is fully proved: the dedup/projection
factor via `liftData : g k ↦ data (g k)`, the matching multisets bridge
via `Multiset.filter_map` and `LiftedTK.data` injectivity, and the
per-column body equality follows from `Term.castToAnnotatedTuple_evalInVK`,
`Term.evalInVK_index_last`, `LiftedTK.fold_add_ann`,
`LiftedTK.fold_add_ktensor_nonempty`, and `KTensor.sum_map_embed`. -/
theorem Query.rewriting_valid_full
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
  -- The Agg case (R5) is proved directly using the per-row formulas
  -- `Term.castToAnnotatedTuple_evalInVK`, `Term.evalInVK_index_last`,
  -- `LiftedTK.fold_add_ann`, `LiftedTK.fold_add_ktensor_nonempty`, and
  -- `KTensor.sum_map_embed`.
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
  | @Agg m n₁ n₂ is ts as q_inner _ =>
      -- (R5) case. `hq : (Query.Agg is ts as q_inner).wellFormed`
      -- definitionally reduces to `q_inner.noAgg`; reuse it directly.
      -- The V_K evaluator on the rewritten Agg lands in the
      -- `∃ k, as' k = sumDelta` branch (witness: `Fin.last n₂`).
      have h_sumDelta_exists :
          ∃ k : Fin (n₂ + 1),
            (fun k : Fin (n₂ + 1) =>
              if h : ↑k < n₂ then as ⟨k, h⟩ else AggFunc.sumDelta) k
              = AggFunc.sumDelta := by
        refine ⟨Fin.last n₂, ?_⟩
        simp [Fin.last]
      unfold Query.evaluateAnnotatedFull
      unfold Query.rewritingFull Query.rewritingAgg Query.evaluateInVK
      simp only [dif_pos h_sumDelta_exists]
      -- Substitute the rewriting-correctness equality for the inner query,
      -- and bridge `toComposite + ofSum-on-tuples` to `toLifted`.
      rw [← Query.rewriting_valid q_inner hq Î]
      simp only [Multiset.map_ofSum_toComposite]
      -- We now reason purely over `r_inner.toLifted` on the RHS. Abbreviate.
      set r_inner : AnnotatedRelation T K m := q_inner.evaluateAnnotated hq Î
        with hr_inner
      -- The dedup of group keys on the RHS is `r_inner.toLifted` projected
      -- through `is'`-lookup; that lookup factors as data-side `is`-lookup
      -- composed with `liftData : g k ↦ data (g k)`.
      have h_keys_map :
          @Multiset.map (Tuple (LiftedTK T K) (m + 1)) (Tuple (LiftedTK T K) n₁)
              (fun u k => u ((is k).castLE (Nat.le_succ m))) r_inner.toLifted
            = @Multiset.map (Tuple T n₁) (Tuple (LiftedTK T K) n₁)
                (fun g k => LiftedTK.data (g k))
                (Multiset.map (fun (p : AnnotatedTuple T K m) (k : Fin n₁) =>
                    p.fst (is k)) r_inner) := by
        unfold AnnotatedRelation.toLifted
        rw [Multiset.map_map, Multiset.map_map]
        apply Multiset.map_congr rfl
        intro p _
        funext k
        simp only [Function.comp]
        unfold AnnotatedTuple.toLifted
        have hk : (is k).castLE (Nat.le_succ m) = Fin.castAdd 1 (is k) := rfl
        rw [hk, Fin.append_left]
      have h_liftData_inj :
          Function.Injective
            (fun (g : Tuple T n₁) => (fun k => LiftedTK.data (g k) : Tuple (LiftedTK T K) n₁)) := by
        intro g₁ g₂ h
        funext k
        exact LiftedTK.data.inj (congrFun h k)
      -- Push the RHS's `r_inner.toLifted`-projected group keys back through
      -- `liftData : g k ↦ data (g k)`, then commute `dedup` past the injective
      -- `liftData` and merge into a single map.
      have h_keys_dedup :
          (@Multiset.map (Tuple (LiftedTK T K) (m + 1)) (Tuple (LiftedTK T K) n₁)
              (fun u k => u ((is k).castLE (Nat.le_succ m)))
              r_inner.toLifted).dedup
            = (Multiset.map (fun (p : AnnotatedTuple T K m) (k : Fin n₁) =>
                  p.fst (is k)) r_inner).dedup.map
                (fun (g : Tuple T n₁) => (fun k => LiftedTK.data (g k) : Tuple (LiftedTK T K) n₁)) := by
        rw [h_keys_map]
        exact Multiset.dedup_map_of_injective h_liftData_inj _
      rw [h_keys_dedup, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro g hg
      -- Beta-reduce the composed function on the RHS so the bound name
      -- inside the per-group body equals the introduced `g_lifted` literal.
      simp only [Function.comp]
      -- Per-group body. Bridge the V_K-side matching multiset
      -- (filtering `r_inner.toLifted`) to the LHS matching multiset
      -- (filtering `r_inner`, then `toLifted`-mapping).
      have h_matching :
          Multiset.filter
              (fun (u : Tuple (LiftedTK T K) (m + 1)) =>
                ∀ k' : Fin n₁, u ((is k').castLE (Nat.le_succ m)) = LiftedTK.data (g k'))
              r_inner.toLifted
            = Multiset.map AnnotatedTuple.toLifted
                (Multiset.filter
                  (fun (p : AnnotatedTuple T K m) =>
                    ∀ k' : Fin n₁, p.fst (is k') = g k') r_inner) := by
        change Multiset.filter _ (Multiset.map AnnotatedTuple.toLifted r_inner) = _
        rw [Multiset.filter_map]
        congr 1
        apply Multiset.filter_congr
        intro p _
        constructor
        · intro hu k'
          have := hu k'
          have hcast : (is k').castLE (Nat.le_succ m) = Fin.castAdd 1 (is k') := rfl
          rw [hcast] at this
          unfold AnnotatedTuple.toLifted at this
          rw [Fin.append_left] at this
          exact LiftedTK.data.inj this
        · intro hp k'
          have hcast : (is k').castLE (Nat.le_succ m) = Fin.castAdd 1 (is k') := rfl
          rw [hcast]
          unfold AnnotatedTuple.toLifted
          rw [Fin.append_left]
          exact congrArg LiftedTK.data (hp k')
      rw [h_matching]
      -- Bind the LHS matching multiset by abbreviation.
      set matching : AnnotatedRelation T K m :=
        Multiset.filter (fun p : AnnotatedTuple T K m =>
            ∀ k' : Fin n₁, p.fst (is k') = g k') r_inner with hmatching_def
      -- Matching is non-empty because `g` came from `dedup`.
      have h_matching_nonempty : matching ≠ 0 := by
        intro h_empty
        rw [hmatching_def] at h_empty
        have h_empty' := (Multiset.eq_zero_iff_forall_notMem
          (s := (Multiset.filter (fun (p : AnnotatedTuple T K m) =>
              ∀ k' : Fin n₁, p.fst (is k') = g k') r_inner
              : Multiset (AnnotatedTuple T K m)))).mp h_empty
        have hg' : g ∈ Multiset.map (fun (p : AnnotatedTuple T K m) =>
              fun k : Fin n₁ => p.fst (is k)) r_inner :=
          Multiset.mem_dedup.mp hg
        obtain ⟨p₀, hp₀_mem, hp₀_eq⟩ := Multiset.mem_map.mp hg'
        exact h_empty' p₀
          (Multiset.mem_filter.mpr ⟨hp₀_mem, fun k' => congrFun hp₀_eq k'⟩)
      -- Cellwise: split `k : Fin (n₁ + (n₂ + 1))` via the RHS's outer
      -- `Fin.append` into a Fin n₁ (data column) or a Fin (n₂ + 1) (aggregated column).
      funext k
      refine Fin.addCases (m := n₁) (n := n₂ + 1) (fun i => ?_) (fun j => ?_) k
      · -- Data column: `i : Fin n₁`. Both sides give `LiftedTK.data (g i)`.
        rw [Fin.append_left]
        show
          Fin.append (Fin.append (fun k : Fin n₁ => (LiftedTK.data (g k) : LiftedTK T K)) _) _
              (Fin.castAdd 1 (Fin.castAdd n₂ i)) = _
        rw [Fin.append_left, Fin.append_left]
      · -- Agg column: `j : Fin (n₂ + 1)`. Split on `j.val < n₂` or `j = Fin.last n₂`.
        rw [Fin.append_right]
        by_cases hj : j.val < n₂
        · -- ktensor column: `j = Fin.castAdd 1 ⟨j.val, hj⟩`.
          -- LHS lookup: at `Fin.natAdd n₁ j`. This equals
          --   `Fin.castAdd 1 (Fin.natAdd n₁ ⟨j.val, hj⟩) : Fin (n₁ + n₂ + 1)`.
          have hLcast : (Fin.natAdd n₁ j : Fin (n₁ + n₂ + 1))
                = Fin.castAdd 1 (Fin.natAdd n₁ (⟨j.val, hj⟩ : Fin n₂)) := by
            ext; simp
          show
            @Fin.append (n₁ + n₂) 1 _
                (Fin.append (fun k : Fin n₁ => (LiftedTK.data (g k) : LiftedTK T K))
                  (fun k : Fin n₂ =>
                    LiftedTK.ktensor
                      (Multiset.map (fun p : AnnotatedTuple T K m =>
                          (p.snd, (ts k).eval p.fst)) matching)))
                ![LiftedTK.ann (SemiringWithMonus.delta
                    (Multiset.map Prod.snd matching).sum)]
                (Fin.natAdd n₁ j) = _
          rw [hLcast, Fin.append_left, Fin.append_right]
          -- RHS: simplify the dif on `j.val < n₂`.
          simp only [dif_pos hj]
          -- Compute the per-row term on a `toLifted` tuple:
          --   `data (...) * ann α = ktensor (embed α (...))`.
          have h_perRow : ∀ p : AnnotatedTuple T K m,
              ((ts ⟨j.val, hj⟩).castToAnnotatedTuple.mul (Term.index (Fin.last m))).evalInVK
                  p.toLifted
                = LiftedTK.ktensor (KTensor.embed p.snd ((ts ⟨j.val, hj⟩).eval p.fst)) := by
            intro p
            show
              (Term.castToAnnotatedTuple (ts ⟨j.val, hj⟩)).evalInVK p.toLifted *
                  (Term.index (Fin.last m) : Term (T ⊕ K) (m + 1)).evalInVK p.toLifted
                = _
            rw [Term.castToAnnotatedTuple_evalInVK, Term.evalInVK_index_last]
            rfl
          -- Compute the fold of ktensors to a single ktensor of the sum.
          have h_fold :
              Multiset.fold (· + ·) (0 : LiftedTK T K)
                  (Multiset.map (fun x : Tuple (LiftedTK T K) (m + 1) =>
                    ((ts ⟨j.val, hj⟩).castToAnnotatedTuple.mul (Term.index (Fin.last m))).evalInVK x)
                  (Multiset.map AnnotatedTuple.toLifted matching))
                = LiftedTK.ktensor
                    (Multiset.map (fun p : AnnotatedTuple T K m =>
                      (p.snd, (ts ⟨j.val, hj⟩).eval p.fst)) matching) := by
            rw [Multiset.map_map]
            simp only [Function.comp]
            rw [show (fun (x : AnnotatedTuple T K m) =>
                    ((ts ⟨j.val, hj⟩).castToAnnotatedTuple.mul
                        (Term.index (Fin.last m))).evalInVK x.toLifted)
                  = (LiftedTK.ktensor : KTensor K T → LiftedTK T K) ∘
                    (fun x : AnnotatedTuple T K m =>
                      KTensor.embed x.snd ((ts ⟨j.val, hj⟩).eval x.fst)) from
                funext fun p => h_perRow p]
            rw [← Multiset.map_map]
            rw [LiftedTK.fold_add_ktensor_nonempty _
                (by intro h
                    apply h_matching_nonempty
                    exact Multiset.map_eq_zero.mp h)]
            congr 1
            exact KTensor.sum_map_embed matching (fun p => p.snd)
              (fun p => (ts ⟨j.val, hj⟩).eval p.fst)
          -- Branch on the user-supplied aggregator: `sum` keeps `ktensor`,
          -- `sumDelta` collapses to `applyDelta ktensor = ktensor`.
          rcases h_as : as ⟨j.val, hj⟩ with _ | _
          · -- AggFunc.sum: match reduces to the fold; the fold collapses to `ktensor`.
            change LiftedTK.ktensor _ = Multiset.fold _ _ _
            exact h_fold.symm
          · -- AggFunc.sumDelta: match reduces to `applyDelta (fold)`; fold is `ktensor`;
            -- `applyDelta (ktensor t) = ktensor t`.
            change LiftedTK.ktensor _ = LiftedTK.applyDelta (Multiset.fold _ _ _)
            rw [h_fold]
            rfl
        · -- δ-annotation column: `j = Fin.last n₂`.
          have hj_val : j.val = n₂ := by
            have h1 : j.val ≤ n₂ := Nat.lt_succ_iff.mp j.isLt
            omega
          -- LHS lookup: at `Fin.natAdd n₁ j`. This equals
          --   `Fin.natAdd (n₁ + n₂) (0 : Fin 1) : Fin (n₁ + n₂ + 1)`.
          have hLcast : (Fin.natAdd n₁ j : Fin (n₁ + n₂ + 1))
                = Fin.natAdd (n₁ + n₂) (0 : Fin 1) := by
            ext; simp [hj_val]
          show
            @Fin.append (n₁ + n₂) 1 _
                (Fin.append (fun k : Fin n₁ => (LiftedTK.data (g k) : LiftedTK T K))
                  (fun k : Fin n₂ =>
                    LiftedTK.ktensor
                      (Multiset.map (fun p : AnnotatedTuple T K m =>
                          (p.snd, (ts k).eval p.fst)) matching)))
                ![LiftedTK.ann (SemiringWithMonus.delta
                    (Multiset.map Prod.snd matching).sum)]
                (Fin.natAdd n₁ j) = _
          rw [hLcast, Fin.append_right]
          show LiftedTK.ann _ = _
          -- RHS: the dif fails (j ≥ n₂), so `as'` is `AggFunc.sumDelta`.
          have h_not_lt : ¬ (j.val < n₂) := hj
          simp only [dif_neg h_not_lt]
          -- Compute the fold of ann-α's to a single ann-Σα.
          have h_fold :
              Multiset.fold (· + ·) (0 : LiftedTK T K)
                  (Multiset.map (fun u : Tuple (LiftedTK T K) (m + 1) =>
                    (Term.index (Fin.last m) : Term (T ⊕ K) (m + 1)).evalInVK u)
                  (Multiset.map AnnotatedTuple.toLifted matching))
                = LiftedTK.ann (Multiset.map Prod.snd matching).sum := by
            rw [Multiset.map_map]
            simp only [Function.comp]
            rw [show (fun (x : AnnotatedTuple T K m) =>
                    (Term.index (Fin.last m) : Term (T ⊕ K) (m + 1)).evalInVK x.toLifted)
                  = (LiftedTK.ann : K → LiftedTK T K) ∘
                    (fun x : AnnotatedTuple T K m => x.snd) from
                funext fun p => Term.evalInVK_index_last p]
            rw [← Multiset.map_map]
            exact LiftedTK.fold_add_ann _
          rw [h_fold]
          rfl
