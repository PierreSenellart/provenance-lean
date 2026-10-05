import Mathlib.Data.Fin.VecNotation

import Lax392996Proofs.Provenance.AnnotatedDatabase
import Lax392996Proofs.Provenance.Query
import Lax392996Proofs.Provenance.QueryAnnotatedDatabase
import Lax392996Proofs.Provenance.Util.ValueType
import Lax392996.AnnotatedDatabases
import Lax392996.AnnotatedSemantics
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.MultisetSemantics
import Lax392996.ProbabilisticDatabases
import Lax392996.RelationalAlgebra
import Lax392996.RewritingRules
import Lax392996.SemiringsWithMonus
import Lax392996.WhyProvenance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation
end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple
end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace Lax392996.AnnotatedSemantics.Selection
end Lax392996.AnnotatedSemantics.Selection

namespace Lax392996.Databases.Relation
end Lax392996.Databases.Relation

namespace Lax392996.Databases.Tuple
end Lax392996.Databases.Tuple

namespace Lax392996.MultisetSemantics.Query
end Lax392996.MultisetSemantics.Query

namespace Lax392996.RelationalAlgebra.Query
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Selection
end Lax392996.RelationalAlgebra.Selection

namespace Lax392996.RewritingRules.Query
end Lax392996.RewritingRules.Query

namespace Lax392996Proofs.Foreign
end Lax392996Proofs.Foreign

namespace Lax392996Proofs.Foreign.AnnotatedRelation
end Lax392996Proofs.Foreign.AnnotatedRelation

namespace Lax392996Proofs.Foreign.AnnotatedTuple
end Lax392996Proofs.Foreign.AnnotatedTuple

namespace Lax392996Proofs.Foreign.Multiset
end Lax392996Proofs.Foreign.Multiset

namespace Lax392996Proofs.Foreign.Query
end Lax392996Proofs.Foreign.Query

namespace Lax392996Proofs.Foreign.Relation
end Lax392996Proofs.Foreign.Relation

namespace Lax392996Proofs.Foreign.Selection
end Lax392996Proofs.Foreign.Selection

namespace Lax392996Proofs.Foreign.Sum
end Lax392996Proofs.Foreign.Sum

namespace Lax392996Proofs.Foreign.Tuple
end Lax392996Proofs.Foreign.Tuple

namespace Lax392996.RelationalAlgebra.Query
export Lax392996.MultisetSemantics.Query (evaluate)
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query
export Lax392996.RewritingRules.Query (rewriting)
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Selection
export Lax392996.AnnotatedSemantics.Selection (evalDecidableAnnotated)
end Lax392996.RelationalAlgebra.Selection

/-!
# Query evaluation by rewriting

This file provides an alternative approach to evaluating queries on annotated databases:
instead of directly interpreting operators over annotated tuples, a query on `T` is
rewritten into a query on `T ⊕ K` that operates on plain tuples whose values encode
both data and provenance.

The rewriting implemented here realizes rules (R1)–(R5) from
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the Provenance
and Probability of Data*][sen2026provsql].

A correctness proof that `Query.rewriting` agrees with `Query.evaluateAnnotated` is
fully formalized for rules (R1)–(R4): each operator is machine-checked end-to-end.
The `Diff` case splits into an `unmatched_eq` half (proved via the semijoin
identity `Multiset.semijoin_proj_eq_filter`, after bridging the
`LinearOrder.toDecidableEq` vs `instDecidableEqSum` mismatch on the inner dedup
via `Query.rewriting_valid_diff_inner_dd_inst`) and a `matched_eq` half (proved
via the keyed-projection semijoin `Multiset.semijoin_keyed_proj_eq_filter`, after
substituting the inner aggregation with the closed-form
`Query.evaluate_agg_rewriting_eq`). Rule (R5) – aggregation – is not part of
this classical rewriting: it lives on the general syntax, in
`Provenance.AggQueryGroupRewriting`, where an aggregate output is a symbolic
token rather than a quotiented K-tensor.

## References

* [Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
  Provenance and Probability of Data*][sen2026provsql]
-/

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
lemma _root_.Lax392996Proofs.Foreign.Query.rewriting_valid_prod_heqn (hn: n₁+n₂=n): n₁+1 + (n₂+1) = n+2 := by omega

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid_prod_heqn)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid_prod_heqn)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
lemma _root_.Lax392996Proofs.Foreign.Query.rewriting_valid_prod0 [Mul K] {n₁ n₂ n: ℕ}
  (hn: n₁+n₂=n)
  (heq : (Fin (n₁ + n₂) → T) = (Fin n → T)):
  ∀ (ar₁: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n₁) (ar₂: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n₂), Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
  (Multiset.map (fun x ↦ (cast heq (Fin.append x.1.1 x.2.1), x.1.2 * x.2.2))
    (Multiset.product (ar₁) (ar₂))) = (
      Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
      (Multiset.map (fun x ↦ (Fin.append x.1.1 x.2.1, x.1.2 * x.2.2))
        (Multiset.product (ar₁) (ar₂)))).cast (by simp[hn]) := by
        intro ar₁ ar₂
        subst n
        rw[Lax392996Proofs.Foreign.AnnotatedRelation.cast_toComposite]
        congr
        rfl

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid_prod0)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid_prod0)
end Query

lemma _root_.Lax392996Proofs.Foreign.cast_apply
  (f: Lax392996.Databases.Tuple T n → α)
  (t: Lax392996.Databases.Tuple T m)
  (hn: n=m) :
    @cast (Lax392996.Databases.Tuple T n → α) (Lax392996.Databases.Tuple T m → α) (by simp[hn]) f t
  = f (t.cast (Eq.symm hn)) := by
    subst hn
    simp[Lax392996Proofs.Foreign.Tuple.cast]

export Lax392996Proofs.Foreign (cast_apply)

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
lemma _root_.Lax392996Proofs.Foreign.Query.rewriting_valid_prod1 {n₁ n:ℕ} [Lax392996.Databases.ValueType (T⊕K)]
  (hn: n₁+1+(n₂+1)=n+2)
  (f: (Lax392996.Databases.Tuple (T ⊕ K) (n + 2)) → (Lax392996.Databases.Tuple (T ⊕ K) (n + 1))):
  ∀ (r: Lax392996.Databases.Relation (T⊕K) (n₁+1+(n₂+1))),
  (r.cast hn).map f = r.map (λ t ↦ f (t.cast hn))
    := by
  intro r
  congr 1
  . simp[hn]
  . refine Function.hfunext ?_ ?_
    . simp[hn]
    . intro t t' heq
      rw[Lax392996Proofs.Foreign.Tuple.apply_cast hn f t']
      simp
      rw[Lax392996Proofs.Foreign.cast_apply]
      simp[Lax392996Proofs.Foreign.Tuple.cast]
      apply congrArg
      rw[eq_comm]
      rw[eqRec_eq_cast]
      rw[cast_eq_iff_heq]
      exact (HEq.symm heq)
      simp[hn]
  . exact eqRec_heq _ _

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid_prod1)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid_prod1)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- `Tuple.cast`-flavored variant of `rewriting_append_left`. Both `Tuple.cast`'s and `▸`'s
`Eq.rec` motives must syntactically agree for `rw` to fire on Lean v4.29; this version
matches the motive produced by `Tuple.cast`. -/
lemma _root_.Lax392996Proofs.Foreign.Query.tupleCast_append_left
  (t₁: Lax392996.Databases.Tuple T n₁)
  (t₂: Lax392996.Databases.Tuple T n₂)
  (hn: n₁+n₂=n)
  (k: Fin n)
  (hk: ↑k<n₁):
  Lax392996Proofs.Foreign.Tuple.cast hn (Fin.append t₁ t₂) k = t₁ (k.castLT hk) := by
  subst hn
  unfold Lax392996Proofs.Foreign.Tuple.cast
  simp[Fin.append,Fin.addCases,hk]

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (tupleCast_append_left)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (tupleCast_append_left)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- `Tuple.cast`-flavored variant of `rewriting_append_right`. -/
lemma _root_.Lax392996Proofs.Foreign.Query.tupleCast_append_right
  (t₁: Lax392996.Databases.Tuple T n₁)
  (t₂: Lax392996.Databases.Tuple T n₂)
  (hn: n₁+n₂=n)
  (k: Fin n)
  (hk: ¬↑k<n₁):
  Lax392996Proofs.Foreign.Tuple.cast hn (Fin.append t₁ t₂) k = t₂ ⟨↑k-n₁, by omega⟩ := by
  subst hn
  unfold Lax392996Proofs.Foreign.Tuple.cast
  simp[Fin.append,Fin.addCases,hk]
  apply congrArg
  refine Fin.eq_of_val_eq ?_
  simp

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (tupleCast_append_right)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (tupleCast_append_right)
end Query

/-!
### Helper lemmas for the `Dedup` case of `rewriting_valid`
-/

open Lax392996Proofs.Foreign.Multiset in
/-- Folding `addFn` over a multiset of `Sum.inr k` values in `T⊕K` reduces to the
`Multiset.sum` in `K`, wrapped in `Sum.inr`. -/
lemma _root_.Lax392996Proofs.Foreign.Multiset.fold_addFn_map_inr
    {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K]
    (m: Multiset K):
  Multiset.fold (@Lax392996.MultisetSemantics.addFn (T⊕K) _) (0: T⊕K) (m.map (fun k ↦ (Sum.inr k: T⊕K)))
  = (Sum.inr m.sum: T⊕K) := by
  induction m using Multiset.induction with
  | empty =>
    simp
    rfl
  | cons hd tl ih =>
    rw[Multiset.map_cons, Multiset.fold_cons_left, ih, Multiset.sum_cons]
    show Lax392996.MultisetSemantics.addFn (Sum.inr hd : T⊕K) (Sum.inr tl.sum) = Sum.inr (hd + tl.sum)
    rfl

namespace Multiset
export Lax392996Proofs.Foreign.Multiset (fold_addFn_map_inr)
end Multiset

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

open Lax392996Proofs.Foreign.AnnotatedRelation in
/-- Filtering `ar.toComposite` by “first-n columns match `Sum.inl ∘ v`” and projecting to the
last column yields the `Sum.inr`-wrapped annotations of the matching entries of `ar`. -/
lemma _root_.Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_filter_map_last
  {T K: Type} [Lax392996.Databases.ValueType T] [DecidableEq K] {n: ℕ}
  (ar: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) (v: Lax392996.Databases.Tuple T n):
  Multiset.map (fun u: Lax392996.Databases.Tuple (T⊕K) (n+1) ↦ u (Fin.last n))
    (Multiset.filter
      (fun u: Lax392996.Databases.Tuple (T⊕K) (n+1) ↦
        ∀ k': Fin n, u (k'.castLE (Nat.le_succ n)) = (Sum.inl (v k'): T⊕K))
      ar.toComposite)
  = Multiset.map (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ (Sum.inr p.2: T⊕K))
      (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) ar) := by
  unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
  rw[Multiset.filter_map, Multiset.map_map]
  -- Show filters and maps are equal by pointwise agreement
  have hfilter : Multiset.filter
      ((fun u: Lax392996.Databases.Tuple (T⊕K) (n+1) ↦
         ∀ k': Fin n, u (k'.castLE (Nat.le_succ n)) = (Sum.inl (v k'): T⊕K))
        ∘ Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite) ar
    = Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) ar := by
    apply Multiset.filter_congr
    intro p _
    unfold Function.comp Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
    constructor
    · intro h
      funext k
      have hk := h k
      have hcast : k.castLE (Nat.le_succ n) = Fin.castAdd 1 k := rfl
      rw[hcast] at hk
      rw[Fin.append_left] at hk
      simp at hk
      exact hk
    · intro h k
      subst h
      have hcast : k.castLE (Nat.le_succ n) = Fin.castAdd 1 k := rfl
      rw[hcast, Fin.append_left]
  rw[hfilter]
  -- Now show the map functions agree on filtered entries
  apply Multiset.map_congr rfl
  intro p _
  simp only [Function.comp]
  unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
  have : Fin.last n = Fin.natAdd n (0: Fin 1) := by
    apply Fin.eq_of_val_eq; simp
  rw[this, Fin.append_right]
  rfl

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_filter_map_last)

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace AnnotatedRelation
export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_filter_map_last)
end AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

open Lax392996Proofs.Foreign.AnnotatedRelation in
/-- The dedup of the first-n projection of `ar.toComposite` is the `Sum.inl`-image of the dedup
of the first-projection of `ar`. -/
lemma _root_.Lax392996Proofs.Foreign.AnnotatedRelation.dedup_toComposite_proj_first_n
  {T K: Type} [Lax392996.Databases.ValueType T] [DecidableEq K] {n: ℕ}
  (ar: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) (h: n ≤ n+1):
  Multiset.dedup
    ((Multiset.map (fun u k ↦ u (Fin.castLE h k)) ar.toComposite: Multiset (Lax392996.Databases.Tuple (T⊕K) n)))
  = Multiset.map (fun v ↦ (fun k: Fin n ↦ (Sum.inl (v k): T⊕K) : Lax392996.Databases.Tuple (T⊕K) n))
      (Multiset.dedup (Multiset.map Prod.fst ar)) := by
  -- Work around higher-order unification by doing a single change-of-representation.
  -- We show both sides equal `Multiset.map (Sum.inl-lift) (Multiset.map Prod.fst ar).dedup`.
  have h_inj : Function.Injective
      (fun (v : Lax392996.Databases.Tuple T n) (k : Fin n) => (Sum.inl (v k) : T⊕K)) := by
    intro v₁ v₂ heq
    funext k
    exact Sum.inl.inj (congrFun heq k)
  have hmap_inner : ∀ p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n,
      (fun k : Fin n ↦ p.toComposite (Fin.castLE h k))
    = (fun k : Fin n ↦ (Sum.inl (p.1 k) : T⊕K)) := by
    intro p
    funext k
    unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
    have hcast : k.castLE h = Fin.castAdd 1 k := rfl
    rw [hcast, Fin.append_left]
  calc Multiset.dedup
        ((Multiset.map (fun u k ↦ u (Fin.castLE h k)) ar.toComposite
          : Multiset (Lax392996.Databases.Tuple (T⊕K) n)))
      = Multiset.dedup (Multiset.map
          (fun v ↦ (fun k : Fin n ↦ (Sum.inl (v k) : T⊕K) : Lax392996.Databases.Tuple (T⊕K) n))
          (Multiset.map Prod.fst ar)) := by
          congr 1
          unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
          rw [Multiset.map_map, Multiset.map_map]
          exact Multiset.map_congr rfl (fun p _ => hmap_inner p)
    _ = Multiset.map (fun v ↦ (fun k : Fin n ↦ (Sum.inl (v k) : T⊕K) : Lax392996.Databases.Tuple (T⊕K) n))
          (Multiset.map Prod.fst ar).dedup :=
        Multiset.dedup_map_of_injective h_inj _

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

export Lax392996Proofs.Foreign.AnnotatedRelation (dedup_toComposite_proj_first_n)

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace AnnotatedRelation
export Lax392996Proofs.Foreign.AnnotatedRelation (dedup_toComposite_proj_first_n)
end AnnotatedRelation

/-- Auxiliary: key set of `groupByKey ar` equals first-projection keys of `ar`. -/
lemma _root_.Lax392996Proofs.Foreign.groupByKey_key_iff
  {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) (v: Lax392996.Databases.Tuple T n):
  (∃ w, (v, w) ∈ (Lax392996Proofs.Foreign.groupByKey ar).val) ↔ v ∈ Multiset.map Prod.fst ar := by
  induction ar using Multiset.induction_on with
  | empty =>
    -- Empty case: both sides are empty.
    have hval : (Lax392996Proofs.Foreign.groupByKey (0 : Lax392996.AnnotatedDatabases.AnnotatedRelation T K n)).val = [] := by
      unfold Lax392996Proofs.Foreign.groupByKey; rfl
    refine ⟨?_, ?_⟩
    · rintro ⟨w, hmem⟩
      have : ¬ (v, w) ∈ (Lax392996Proofs.Foreign.groupByKey (0 : Lax392996.AnnotatedDatabases.AnnotatedRelation T K n)).val := by
        rw [hval]; exact List.not_mem_nil
      exact absurd hmem this
    · rintro ⟨x, hx⟩
  | @cons p tl ih =>
    have hkv : (Lax392996Proofs.Foreign.groupByKey (p ::ₘ tl)).val = (Lax392996Proofs.Foreign.groupByKey tl).val.addKV p.1 p.2 := by
      unfold Lax392996Proofs.Foreign.groupByKey; rw[Multiset.foldr_cons]; rfl
    show (∃ w, (v, w) ∈ (Lax392996Proofs.Foreign.groupByKey (p ::ₘ tl)).val) ↔
         v ∈ (Multiset.map Prod.fst (p ::ₘ tl) : Multiset (Lax392996.Databases.Tuple T n))
    rw[hkv]
    simp only [Multiset.map_cons, Multiset.mem_cons]
    constructor
    · rintro ⟨w, hw⟩
      rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec _ (Lax392996Proofs.Foreign.groupByKey tl).property] at hw
      rcases hw with ⟨_, hmem⟩ | ⟨heq, _⟩
      · right; exact ih.mp ⟨w, hmem⟩
      · left; exact heq
    · rintro (hpeq | hv)
      · obtain ⟨w, hw⟩ := Lax392996Proofs.Foreign.KeyValueList.addKV_mem _ (Lax392996Proofs.Foreign.groupByKey tl).property p.1 p.2
        refine ⟨w, ?_⟩
        rw[hpeq]
        exact hw
      · obtain ⟨w, hw⟩ := ih.mpr hv
        by_cases hpv : p.1 = v
        · obtain ⟨w', hw'⟩ := Lax392996Proofs.Foreign.KeyValueList.addKV_mem _ (Lax392996Proofs.Foreign.groupByKey tl).property p.1 p.2
          refine ⟨w', ?_⟩
          rw[← hpv]; exact hw'
        · refine ⟨w, ?_⟩
          rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec _ (Lax392996Proofs.Foreign.groupByKey tl).property]
          left
          refine ⟨fun h ↦ hpv h.symm, hw⟩

export Lax392996Proofs.Foreign (groupByKey_key_iff)

/-- Auxiliary: if `(v, w) ∈ (groupByKey ar).val`, then `w` is the semiring-sum of annotations
of entries in `ar` with key `v`. -/
lemma _root_.Lax392996Proofs.Foreign.groupByKey_value
  {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) (v: Lax392996.Databases.Tuple T n) (w: K):
  (v, w) ∈ (Lax392996Proofs.Foreign.groupByKey ar).val →
    w = (Multiset.map Prod.snd
          (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) ar)).sum := by
  induction ar using Multiset.induction_on generalizing w with
  | empty =>
    have hval : (Lax392996Proofs.Foreign.groupByKey (0 : Lax392996.AnnotatedDatabases.AnnotatedRelation T K n)).val = [] := by
      unfold Lax392996Proofs.Foreign.groupByKey; rfl
    intro hmem
    exfalso
    have hnm : ¬ (v, w) ∈ (Lax392996Proofs.Foreign.groupByKey (0 : Lax392996.AnnotatedDatabases.AnnotatedRelation T K n)).val := by
      rw [hval]; exact List.not_mem_nil
    exact hnm hmem
  | @cons p tl ih =>
    intro hmem
    have hkv : (Lax392996Proofs.Foreign.groupByKey (p ::ₘ tl)).val = (Lax392996Proofs.Foreign.groupByKey tl).val.addKV p.1 p.2 := by
      unfold Lax392996Proofs.Foreign.groupByKey; rw[Multiset.foldr_cons]; rfl
    change (v, w) ∈ (Lax392996Proofs.Foreign.groupByKey (p ::ₘ tl)).val at hmem
    rw[hkv] at hmem
    rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec _ (Lax392996Proofs.Foreign.groupByKey tl).property] at hmem
    by_cases hpv : p.1 = v
    · -- p.1 = v
      show w = (Multiset.map Prod.snd (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v)
        ((p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) ::ₘ (tl : Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n))))).sum
      rw [Multiset.filter_cons, if_pos hpv, Multiset.map_add, Multiset.sum_add,
          Multiset.map_singleton, Multiset.sum_singleton]
      rcases hmem with ⟨hne, _⟩ | ⟨_, hdisj⟩
      · exact absurd hpv.symm hne
      · rcases hdisj with ⟨hnone, hw⟩ | ⟨z, hz, hw⟩
        · -- (v, w) = (p.1, p.2) and no entry with key p.1 in groupByKey tl
          have hw_eq : w = p.2 := ((Prod.mk.injEq _ _ _ _).mp hw).2
          -- The remaining filter over `tl` is empty.
          have hnokey : ¬ v ∈ Multiset.map Prod.fst tl := by
            intro h
            apply hnone
            rw [hpv]
            exact (Lax392996Proofs.Foreign.groupByKey_key_iff tl v).mpr h
          have hfilter_eq : Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) tl = 0 :=
            Multiset.filter_eq_nil.mpr (fun q hq hq1 =>
              hnokey (Multiset.mem_map.mpr ⟨q, hq, hq1⟩))
          have hmap_filter_empty : (Multiset.map Prod.snd
              (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) tl)).sum = 0 := by
            convert Multiset.sum_zero
            convert Multiset.map_zero (Prod.snd : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n → K)
          rw [hmap_filter_empty, add_zero]
          exact hw_eq
        · -- (v, w) = (p.1, p.2 + z) with (p.1, z) ∈ groupByKey tl
          have hv_eq : v = p.1 := ((Prod.mk.injEq _ _ _ _).mp hw).1
          have hw_eq : w = p.2 + z := ((Prod.mk.injEq _ _ _ _).mp hw).2
          have hz' : (v, z) ∈ (Lax392996Proofs.Foreign.groupByKey tl).val := hv_eq ▸ hz
          rw[hw_eq, ih z hz']
    · -- p.1 ≠ v
      show w = (Multiset.map Prod.snd (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v)
        ((p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) ::ₘ (tl : Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n))))).sum
      rw [Multiset.filter_cons, if_neg hpv, zero_add]
      rcases hmem with ⟨_, hmem⟩ | ⟨heq, _⟩
      · exact ih w hmem
      · exact absurd heq.symm hpv

export Lax392996Proofs.Foreign (groupByKey_value)

/-- `groupByKey ar`, as a multiset, equals the dedup of the first-projection of `ar`, with each
key paired with the semiring-sum of annotations sharing that key. -/
lemma _root_.Lax392996Proofs.Foreign.groupByKey_multiset_eq
  {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n):
  (Multiset.ofList (Lax392996Proofs.Foreign.groupByKey ar).val: Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n))
  = Multiset.map
      (fun v: Lax392996.Databases.Tuple T n ↦
        (v, (Multiset.map Prod.snd
              (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) ar)).sum))
      (Multiset.dedup (Multiset.map Prod.fst ar)) := by
  have hLNodup : (Multiset.ofList (Lax392996Proofs.Foreign.groupByKey ar).val :
      Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n)).Nodup := by
    rw[Multiset.coe_nodup]
    exact Lax392996Proofs.Foreign.KeyValueList.nodup _ (Lax392996Proofs.Foreign.groupByKey ar).property
  have hRNodup : (Multiset.map
      (fun v: Lax392996.Databases.Tuple T n ↦ (v, (Multiset.map Prod.snd (Multiset.filter (fun p ↦ p.1 = v) ar)).sum))
      (Multiset.dedup (Multiset.map Prod.fst ar))).Nodup := by
    apply Multiset.Nodup.map
    · intro v₁ v₂ heq
      exact (Prod.mk.injEq _ _ _ _).mp heq |>.1
    · exact Multiset.nodup_dedup _
  refine (Multiset.Nodup.ext hLNodup hRNodup).mpr ?_
  rintro ⟨v, w⟩
  show (v, w) ∈ (Multiset.ofList (Lax392996Proofs.Foreign.groupByKey ar).val : Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n)) ↔
       (v, w) ∈ Multiset.map (fun v: Lax392996.Databases.Tuple T n ↦
         (v, (Multiset.map Prod.snd (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) ar)).sum))
         (Multiset.dedup (Multiset.map Prod.fst ar))
  simp only [Multiset.mem_map]
  constructor
  · intro hmem
    refine ⟨v, ?_, ?_⟩
    · rw[Multiset.mem_dedup]
      exact (Lax392996Proofs.Foreign.groupByKey_key_iff ar v).mp ⟨w, hmem⟩
    · have hw := Lax392996Proofs.Foreign.groupByKey_value ar v w hmem
      congr 1
      exact hw.symm
  · rintro ⟨v', hv', heq⟩
    rw[Multiset.mem_dedup] at hv'
    obtain ⟨w', hw'⟩ := (Lax392996Proofs.Foreign.groupByKey_key_iff ar v').mpr hv'
    have hval := Lax392996Proofs.Foreign.groupByKey_value ar v' w' hw'
    injection heq with heq1 heq2
    subst heq1
    have : w = w' := heq2.symm.trans hval.symm
    rw[this]
    exact hw'

export Lax392996Proofs.Foreign (groupByKey_multiset_eq)

/-!
### Helper lemmas for the `Diff` case of `rewriting_valid`
-/

namespace Lax392996.RelationalAlgebra.Selection

open Lax392996Proofs.Foreign.Selection in
/-- Folded `Selection.And` over a mapped list is equivalent to the universal conjunction. -/
lemma _root_.Lax392996Proofs.Foreign.Selection.eval_foldr_and_map {T: Type} [Lax392996.Databases.ValueType T] {N: ℕ} {α : Type*}
  (list: List α) (f: α → Lax392996.RelationalAlgebra.Selection T N) (t: Lax392996.Databases.Tuple T N):
  Lax392996.RelationalAlgebra.Selection.eval
    ((list.map f).foldr (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True) t
  ↔ ∀ x ∈ list, Lax392996.RelationalAlgebra.Selection.eval (f x) t := by
  induction list with
  | nil => simp [Lax392996.RelationalAlgebra.Selection.eval]
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldr_cons, Lax392996.RelationalAlgebra.Selection.eval, List.mem_cons]
    rw[ih]
    constructor
    · rintro ⟨hhd, htl⟩ x (rfl | hx)
      · exact hhd
      · exact htl x hx
    · intro h
      exact ⟨h hd (Or.inl rfl), fun x hx ↦ h x (Or.inr hx)⟩

end Lax392996.RelationalAlgebra.Selection

namespace Lax392996.RelationalAlgebra.Selection

export Lax392996Proofs.Foreign.Selection (eval_foldr_and_map)

end Lax392996.RelationalAlgebra.Selection

namespace Selection
export Lax392996Proofs.Foreign.Selection (eval_foldr_and_map)
end Selection

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- The folded join condition `(#k == #(k+n+1))` for `k ∈ List.range n` evaluates true iff the
tuple's values at indices `ofNat k` and `ofNat (k+n+1)` agree for every `k < n`. -/
lemma _root_.Lax392996Proofs.Foreign.Query.rewriting_valid_joinCond_eval
  {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K]
  {N n: ℕ} [NeZero N] (t: Lax392996.Databases.Tuple (T⊕K) N):
  Lax392996.RelationalAlgebra.Selection.eval
    (((List.range n).map
      (λ k ↦ @Lax392996.RelationalAlgebra.Selection.BT (T⊕K) N
        (#(Fin.ofNat N k) == #(Fin.ofNat N (k+n+1))))).foldr
      (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True) t
  ↔ ∀ k: Fin n, t (@Fin.ofNat N _ k)
              = t (@Fin.ofNat N _ (k+n+1)) := by
  rw[Lax392996Proofs.Foreign.Selection.eval_foldr_and_map]
  simp only [List.mem_range]
  constructor
  · intro h k
    have := h k.val k.isLt
    simpa [Lax392996.RelationalAlgebra.Selection.eval, Lax392996.RelationalAlgebra.BoolTerm.eval, Lax392996.RelationalAlgebra.Term.eval] using this
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa [Lax392996.RelationalAlgebra.Selection.eval, Lax392996.RelationalAlgebra.BoolTerm.eval, Lax392996.RelationalAlgebra.Term.eval] using this

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid_joinCond_eval)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid_joinCond_eval)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- Semiring-sum over the filter, via `groupByKey.find?`-based lookup. -/
lemma _root_.Lax392996Proofs.Foreign.Query.rewriting_valid_find_getD_eq_sum
  {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) (u: Lax392996.Databases.Tuple T n):
  (((Lax392996Proofs.Foreign.groupByKey ar).val.find? (·.1 = u)).map Prod.snd).getD 0
  = (Multiset.map Prod.snd
      (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = u) ar)).sum := by
  cases hfind : (Lax392996Proofs.Foreign.groupByKey ar).val.find? (·.1 = u) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    -- u is not a key of ar, so filter is empty, sum is 0
    have hnone : ¬ ∃ w, (u, w) ∈ (Lax392996Proofs.Foreign.groupByKey ar).val := by
      intro ⟨w, hmem⟩
      rw[List.find?_eq_none] at hfind
      have := hfind (u, w) hmem
      simp at this
    have hnotinkeys : u ∉ Multiset.map Prod.fst ar :=
      fun h ↦ hnone ((Lax392996Proofs.Foreign.groupByKey_key_iff ar u).mpr h)
    -- Avoid `rw` on `filter` (DecidablePred instance divergence with `Tuple` def).
    -- Instead work at the `sum`/`map` level via `convert`.
    have hfilter_eq : Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = u) ar = 0 :=
      Multiset.filter_eq_nil.mpr (fun q hq hq1 =>
        hnotinkeys (Multiset.mem_map.mpr ⟨q, hq, hq1⟩))
    have hmap_filter_empty : (Multiset.map Prod.snd
        (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = u) ar)).sum = 0 := by
      convert Multiset.sum_zero
      convert Multiset.map_zero (Prod.snd : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n → K)
    exact hmap_filter_empty.symm
  | some vw =>
    simp only [Option.map_some, Option.getD_some]
    -- vw ∈ groupByKey and vw.1 = u
    have hmem : vw ∈ (Lax392996Proofs.Foreign.groupByKey ar).val := List.mem_of_find?_eq_some hfind
    have hcond : vw.1 = u := by
      have := List.find?_some hfind
      simpa using this
    obtain ⟨v, w⟩ := vw
    simp at hcond
    subst hcond
    exact Lax392996Proofs.Foreign.groupByKey_value ar v w hmem

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid_find_getD_eq_sum)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid_find_getD_eq_sum)
end Query

open Lax392996Proofs.Foreign.Sum in
/-- `Sum.inl`-lift of tuples is injective. -/
lemma _root_.Lax392996Proofs.Foreign.Sum.inl_lift_injective {T K: Type} {n: ℕ}:
  Function.Injective (fun (v: Lax392996.Databases.Tuple T n) (k: Fin n) ↦ (Sum.inl (v k): T⊕K)) := by
  intro v₁ v₂ heq
  funext k
  exact Sum.inl.inj (congrFun heq k)

namespace Sum
export Lax392996Proofs.Foreign.Sum (inl_lift_injective)
end Sum

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple

open Lax392996Proofs.Foreign.AnnotatedTuple in
/-- Helper: the data part `Tuple.fromComposite` and `AnnotatedTuple.toComposite` agree on data. -/
lemma _root_.Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE
  {T K: Type} [Zero K] {n: ℕ} (p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) (k: Fin n):
  p.toComposite (k.castLE (Nat.le_succ n)) = Sum.inl (p.1 k) := by
  unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
  have hcast : k.castLE (Nat.le_succ n) = Fin.castAdd 1 k := rfl
  rw[hcast, Fin.append_left]

end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple

export Lax392996Proofs.Foreign.AnnotatedTuple (toComposite_castLE)

end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace AnnotatedTuple
export Lax392996Proofs.Foreign.AnnotatedTuple (toComposite_castLE)
end AnnotatedTuple

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple

open Lax392996Proofs.Foreign.AnnotatedTuple in
/-- The annotation part of `p.toComposite` is `Sum.inr p.2`. -/
lemma _root_.Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_last
  {T K: Type} [Zero K] {n: ℕ} (p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n):
  p.toComposite (Fin.last n) = (Sum.inr p.2: T⊕K) := by
  unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
  have : Fin.last n = Fin.natAdd n (0: Fin 1) := by
    apply Fin.eq_of_val_eq; simp
  rw[this, Fin.append_right]
  rfl

end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple

export Lax392996Proofs.Foreign.AnnotatedTuple (toComposite_last)

end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace AnnotatedTuple
export Lax392996Proofs.Foreign.AnnotatedTuple (toComposite_last)
end AnnotatedTuple

namespace Lax392996.Databases.Tuple

open Lax392996Proofs.Foreign.Tuple in
/-- Roundtrip: `Tuple.fromComposite ∘ AnnotatedTuple.toComposite = id`. The
composite encoding loses no information: peeling the data columns and the
annotation column back out reconstructs the original annotated tuple. -/
lemma _root_.Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite
  {T K: Type} [Lax392996.Databases.ValueType T] [Zero K] {n: ℕ} (p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n):
  Lax392996Proofs.Foreign.Tuple.fromComposite p.toComposite = p := by
  apply Prod.ext
  · funext k
    show (match p.toComposite (k.castLE (Nat.le_succ n)) with
            | Sum.inl x => x | Sum.inr _ => 0) = p.1 k
    rw [Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE]
  · show (match p.toComposite (Fin.last n) with
            | Sum.inl _ => 0 | Sum.inr x => x) = p.2
    rw [Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_last]

end Lax392996.Databases.Tuple

namespace Lax392996.Databases.Tuple

export Lax392996Proofs.Foreign.Tuple (fromComposite_toComposite)

end Lax392996.Databases.Tuple

namespace Tuple
export Lax392996Proofs.Foreign.Tuple (fromComposite_toComposite)
end Tuple

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- Reduction of the inner `Dedup ∘ Diff ∘ Proj` block of the `Diff` rewriting:
    deduping the difference of first-`n` projections of `AR₁.toComposite` and `AR₂.toComposite`
    yields the `Sum.inl`-lift of the deduped “unmatched-keys” filter over the data part.
    Stated using `Fin.castLE` (function form) and dot notation (`.dedup`) so the LHS
    pattern matches what `simp only [evaluate]` produces in the `Diff` case of
    `rewriting_valid`. -/
lemma _root_.Lax392996Proofs.Foreign.Query.rewriting_valid_diff_inner_dd
  {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] {n: ℕ}
  (AR₁ AR₂: Lax392996.AnnotatedDatabases.AnnotatedRelation T K n):
  (Multiset.filter
    (fun u: Lax392996.Databases.Tuple (T⊕K) n ↦
      u ∉ Multiset.map
            (fun (u': Lax392996.Databases.Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
            AR₂.toComposite)
    (Multiset.map
      (fun (u': Lax392996.Databases.Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
      AR₁.toComposite)).dedup
  = Multiset.map (fun (v: Lax392996.Databases.Tuple T n) (k: Fin n) ↦ (Sum.inl (v k): T⊕K))
      (Multiset.filter (fun v ↦ v ∉ Multiset.map Prod.fst AR₂)
        (Multiset.map Prod.fst AR₁)).dedup := by
  -- Unfold toComposite, fuse Multiset.map, simplify pointwise via `hcomp`.
  unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
  simp only [Multiset.map_map, Function.comp_def]
  have hcomp : ∀ (p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) (k : Fin n),
      p.toComposite (k.castLE (Nat.le_succ n)) = (Sum.inl (p.1 k) : T⊕K) :=
    fun p k => Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE p k
  simp only [hcomp]
  -- Now both inner `map`s have the curried form `λp k. Sum.inl (p.1 k)`.
  -- We need to convert this into `(Sum.inl-lift) ∘ Prod.fst` form so that injectivity applies.
  -- `rw` is fragile here (HOU on Lean v4.29); fall back to `Multiset.Nodup.ext`.
  refine (Multiset.Nodup.ext (Multiset.nodup_dedup _) ?_).mpr ?_
  · exact (Multiset.nodup_dedup _).map (fun _ _ heq => Lax392996Proofs.Foreign.Sum.inl_lift_injective heq)
  intro u
  constructor
  · intro hLHS
    have hmem₁ := Multiset.mem_dedup.mp hLHS
    rw [Multiset.mem_filter] at hmem₁
    obtain ⟨hmem_map, hnot⟩ := hmem₁
    obtain ⟨p, hp, hp_eq⟩ := Multiset.mem_map.mp hmem_map
    refine Multiset.mem_map.mpr ⟨p.1, ?_, hp_eq⟩
    refine Multiset.mem_dedup.mpr ?_
    rw [Multiset.mem_filter]
    refine ⟨?_, ?_⟩
    · refine Multiset.mem_map.mpr ⟨p, hp, rfl⟩
    · intro hmem₂
      apply hnot
      obtain ⟨q, hq, hq_eq⟩ := Multiset.mem_map.mp hmem₂
      refine Multiset.mem_map.mpr ⟨q, hq, ?_⟩
      funext k
      rw [← hp_eq]
      exact congrArg (fun (v: Lax392996.Databases.Tuple T n) ↦ (Sum.inl (v k) : T⊕K)) hq_eq
  · intro hRHS
    obtain ⟨v, hv, hv_eq⟩ := Multiset.mem_map.mp hRHS
    have hv₁ := Multiset.mem_dedup.mp hv
    rw [Multiset.mem_filter] at hv₁
    obtain ⟨hv_in_keys, hnot⟩ := hv₁
    obtain ⟨p, hp, hpv⟩ := Multiset.mem_map.mp hv_in_keys
    refine Multiset.mem_dedup.mpr ?_
    rw [Multiset.mem_filter]
    refine ⟨?_, ?_⟩
    · refine Multiset.mem_map.mpr ⟨p, hp, ?_⟩
      funext k
      rw [← hv_eq, ← hpv]
    · intro hmem₂
      apply hnot
      obtain ⟨q, hq, hq_eq⟩ := Multiset.mem_map.mp hmem₂
      refine Multiset.mem_map.mpr ⟨q, hq, ?_⟩
      funext k
      apply Sum.inl.inj
      have : (fun k ↦ (Sum.inl (q.1 k) : T⊕K)) = u := hq_eq
      rw [← hv_eq] at this
      exact congrFun this k

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid_diff_inner_dd)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid_diff_inner_dd)
end Query

namespace Lax392996.Databases.Relation

open Lax392996Proofs.Foreign.Relation in
/-- `Relation.cast` rewrites to a `Multiset.map` of `Tuple.cast`. -/
lemma _root_.Lax392996Proofs.Foreign.Relation.cast_eq_map {T : Type} {n m : ℕ} (h : n = m) (r : Lax392996.Databases.Relation T n) :
    r.cast h = r.map (Lax392996Proofs.Foreign.Tuple.cast h) := (Lax392996Proofs.Foreign.Relation.cast_eq r _ h).mp rfl

end Lax392996.Databases.Relation

namespace Lax392996.Databases.Relation

export Lax392996Proofs.Foreign.Relation (cast_eq_map)

end Lax392996.Databases.Relation

namespace Relation
export Lax392996Proofs.Foreign.Relation (cast_eq_map)
end Relation

/-- Projecting the first `n+1` columns of `Tuple.cast h (Fin.append p q)` (for
`p : Tuple α (n+1)`, `q : Tuple α n`, `h : n+1+n = 2*n+1`) returns `p`. -/
lemma _root_.Lax392996Proofs.Foreign.proj_outer_cast_append_eq_fst {α : Type} {n : ℕ}
    (h : n+1+n = 2*n+1) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α n) :
    (fun (k : Fin (n+1)) ↦ Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (k.castLE (by omega))) = p := by
  funext k
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  have hlt : ((k.castLE (by omega : n+1 ≤ 2*n+1)).cast h.symm).val < n + 1 := by
    simp [k.isLt]
  simp only [Fin.append, Fin.addCases, hlt, dif_pos]
  apply congrArg
  exact Fin.eq_of_val_eq rfl

export Lax392996Proofs.Foreign (proj_outer_cast_append_eq_fst)

/-- Reading `Tuple.cast h (Fin.append p q)` at index `Fin.ofNat _ k.val` (for `k : Fin n`)
returns `p k.castSucc`. -/
lemma _root_.Lax392996Proofs.Foreign.cast_append_at_ofNat_left {α : Type} {n : ℕ}
    (h : n+1+n = 2*n+1) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α n) (k : Fin n)
    [NeZero (2*n+1)] :
    Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (Fin.ofNat _ k.val) = p (k.castLE (Nat.le_succ n)) := by
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  have hk_mod : k.val % (2*n+1) = k.val := Nat.mod_eq_of_lt (by omega)
  have hlt : ((Fin.ofNat (2*n+1) k.val).cast h.symm).val < n + 1 := by
    show k.val % (2*n+1) < n + 1
    rw [hk_mod]; exact Nat.lt_succ_of_lt k.isLt
  simp only [Fin.append, Fin.addCases, hlt, dif_pos]
  apply congrArg
  apply Fin.eq_of_val_eq
  show k.val % (2*n+1) = k.val
  exact hk_mod

export Lax392996Proofs.Foreign (cast_append_at_ofNat_left)

/-- Reading `Tuple.cast h (Fin.append p q)` at index `Fin.ofNat _ (k.val+n+1)` (for
`k : Fin n`) returns `q k`. -/
lemma _root_.Lax392996Proofs.Foreign.cast_append_at_ofNat_right {α : Type} {n : ℕ}
    (h : n+1+n = 2*n+1) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α n) (k : Fin n)
    [NeZero (2*n+1)] :
    Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (Fin.ofNat _ (k.val + n + 1)) = q k := by
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  have hbnd : k.val + n + 1 < 2*n + 1 := by omega
  have hmod : (k.val + n + 1) % (2*n+1) = k.val + n + 1 := Nat.mod_eq_of_lt hbnd
  -- Show the recast index equals `Fin.natAdd (n+1) k`, then close with `Fin.append_right`.
  have hidx_eq : (Fin.ofNat (2*n+1) (k.val + n + 1)).cast h.symm
      = Fin.natAdd (n+1) k := by
    apply Fin.eq_of_val_eq
    show (k.val + n + 1) % (2*n+1) = (n+1) + k.val
    rw [hmod]; omega
  rw [hidx_eq, Fin.append_right]

export Lax392996Proofs.Foreign (cast_append_at_ofNat_right)

/-- `selFilter` on `Tuple.cast h (Fin.append p q)` characterizes the first-`n`
projection equality between `p` and `q`. -/
lemma _root_.Lax392996Proofs.Foreign.selFilter_cast_append_iff {T K : Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K]
    [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] {n : ℕ}
    (h : n+1+n = 2*n+1) (p : Lax392996.Databases.Tuple (T⊕K) (n+1)) (q : Lax392996.Databases.Tuple (T⊕K) n)
    [NeZero (2*n+1)] :
    Lax392996.RelationalAlgebra.Selection.eval (((List.range n).map
      (λ k ↦ @Lax392996.RelationalAlgebra.Selection.BT (T⊕K) (2*n+1)
        (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
      (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True) (Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q))
    ↔ (fun (k : Fin n) ↦ p (k.castLE (Nat.le_succ n))) = q := by
  classical
  rw [Lax392996Proofs.Foreign.Query.rewriting_valid_joinCond_eval]
  constructor
  · intro hForall
    funext k
    have := hForall k
    rw [Lax392996Proofs.Foreign.cast_append_at_ofNat_left, Lax392996Proofs.Foreign.cast_append_at_ofNat_right] at this
    exact this
  · intro heq k
    rw [Lax392996Proofs.Foreign.cast_append_at_ofNat_left, Lax392996Proofs.Foreign.cast_append_at_ofNat_right]
    exact congrFun heq k

export Lax392996Proofs.Foreign (selFilter_cast_append_iff)

/-- Arity-`(2n+2)` analogue of `cast_append_at_ofNat_left`: reading
`Tuple.cast h (Fin.append p q)` at index `Fin.ofNat _ k.val` (for `k : Fin n`)
returns `p (k.castLE (Nat.le_succ n))`. Here `q : Tuple α (n+1)` (rather than
`Tuple α n`). -/
lemma _root_.Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_left {α : Type} {n : ℕ}
    (h : (n+1)+(n+1) = 2*n+2) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α (n+1)) (k : Fin n)
    [NeZero (2*n+2)] :
    Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (Fin.ofNat _ k.val) = p (k.castLE (Nat.le_succ n)) := by
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  have hk_mod : k.val % (2*n+2) = k.val := Nat.mod_eq_of_lt (by omega)
  have hlt : ((Fin.ofNat (2*n+2) k.val).cast h.symm).val < n + 1 := by
    show k.val % (2*n+2) < n + 1
    rw [hk_mod]; exact Nat.lt_succ_of_lt k.isLt
  simp only [Fin.append, Fin.addCases, hlt, dif_pos]
  apply congrArg
  apply Fin.eq_of_val_eq
  show k.val % (2*n+2) = k.val
  exact hk_mod

export Lax392996Proofs.Foreign (cast_append_2n2_at_ofNat_left)

/-- Arity-`(2n+2)` analogue of `cast_append_at_ofNat_right`: reading
`Tuple.cast h (Fin.append p q)` at index `Fin.ofNat _ (k.val+n+1)` (for
`k : Fin n`) returns `q (k.castLE (Nat.le_succ n))`. -/
lemma _root_.Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_right {α : Type} {n : ℕ}
    (h : (n+1)+(n+1) = 2*n+2) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α (n+1)) (k : Fin n)
    [NeZero (2*n+2)] :
    Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (Fin.ofNat _ (k.val + n + 1)) = q (k.castLE (Nat.le_succ n)) := by
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  have hbnd : k.val + n + 1 < 2*n + 2 := by omega
  have hmod : (k.val + n + 1) % (2*n+2) = k.val + n + 1 := Nat.mod_eq_of_lt hbnd
  -- Show the recast index equals `Fin.natAdd (n+1) (k.castLE _)`, then close
  -- with `Fin.append_right`.
  have hidx_eq : (Fin.ofNat (2*n+2) (k.val + n + 1)).cast h.symm
      = Fin.natAdd (n+1) (k.castLE (Nat.le_succ n)) := by
    apply Fin.eq_of_val_eq
    show (k.val + n + 1) % (2*n+2) = (n+1) + k.val
    rw [hmod]; omega
  rw [hidx_eq, Fin.append_right]

export Lax392996Proofs.Foreign (cast_append_2n2_at_ofNat_right)

/-- Arity-`(2n+2)` helper: reading `Tuple.cast h (Fin.append p q)` at index
`Fin.ofNat _ n` returns `p (Fin.last n)`. -/
lemma _root_.Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_n {α : Type} {n : ℕ}
    (h : (n+1)+(n+1) = 2*n+2) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α (n+1))
    [NeZero (2*n+2)] :
    Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (Fin.ofNat _ n) = p (Fin.last n) := by
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  have hn_mod : n % (2*n+2) = n := Nat.mod_eq_of_lt (by omega)
  have hlt : ((Fin.ofNat (2*n+2) n).cast h.symm).val < n + 1 := by
    show n % (2*n+2) < n + 1
    rw [hn_mod]; exact Nat.lt_succ_self _
  simp only [Fin.append, Fin.addCases, hlt, dif_pos]
  apply congrArg
  apply Fin.eq_of_val_eq
  show n % (2*n+2) = n
  exact hn_mod

export Lax392996Proofs.Foreign (cast_append_2n2_at_ofNat_n)

/-- Arity-`(2n+2)` helper: reading `Tuple.cast h (Fin.append p q)` at index
`Fin.last (2*n+1)` (the last index of `Fin (2*n+2)`) returns `q (Fin.last n)`. -/
lemma _root_.Lax392996Proofs.Foreign.cast_append_2n2_at_last {α : Type} {n : ℕ}
    (h : (n+1)+(n+1) = 2*n+2) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α (n+1)) :
    Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (Fin.last (2*n+1)) = q (Fin.last n) := by
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  -- The recast index has value `2*n+1`; it falls in the `q` side at offset `n`.
  have hidx_eq : (Fin.last (2*n+1)).cast h.symm
      = Fin.natAdd (n+1) (Fin.last n) := by
    apply Fin.eq_of_val_eq
    show 2*n+1 = (n+1) + n
    omega
  rw [hidx_eq, Fin.append_right]

export Lax392996Proofs.Foreign (cast_append_2n2_at_last)

/-- Arity-`(2n+2)` projection helper: reading `Tuple.cast h (Fin.append p q)` at index
`k.castLE _` (for `k : Fin (n+1)`) returns `p k`. This is the analogue of
`proj_outer_cast_append_eq_fst` for the `2n+2` case (i.e., `q : Tuple α (n+1)`). -/
lemma _root_.Lax392996Proofs.Foreign.proj_outer_2n2_cast_append_eq_fst {α : Type} {n : ℕ}
    (h : (n+1)+(n+1) = 2*n+2) (p : Lax392996.Databases.Tuple α (n+1)) (q : Lax392996.Databases.Tuple α (n+1)) (k : Fin (n+1)) :
    Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q) (k.castLE (by omega : n+1 ≤ 2*n+2)) = p k := by
  rw [Lax392996Proofs.Foreign.Tuple.cast_get]
  have hlt : ((k.castLE (by omega : n+1 ≤ 2*n+2)).cast h.symm).val < n + 1 := by
    simp [k.isLt]
  simp only [Fin.append, Fin.addCases, hlt, dif_pos]
  apply congrArg
  exact Fin.eq_of_val_eq rfl

export Lax392996Proofs.Foreign (proj_outer_2n2_cast_append_eq_fst)

/-- Arity-`(2n+2)` analogue of `selFilter_cast_append_iff`: the join condition
on `Tuple.cast h (Fin.append p q)` with `q : Tuple (T⊕K) (n+1)` characterizes
equality of the first-`n` projections of `p` and `q`. -/
lemma _root_.Lax392996Proofs.Foreign.selFilter_cast_append_2n2_iff {T K : Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K]
    [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] {n : ℕ}
    (h : (n+1)+(n+1) = 2*n+2) (p : Lax392996.Databases.Tuple (T⊕K) (n+1)) (q : Lax392996.Databases.Tuple (T⊕K) (n+1))
    [NeZero (2*n+2)] :
    Lax392996.RelationalAlgebra.Selection.eval (((List.range n).map
      (λ k ↦ @Lax392996.RelationalAlgebra.Selection.BT (T⊕K) (2*n+2)
        (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
      (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True) (Lax392996Proofs.Foreign.Tuple.cast h (Fin.append p q))
    ↔ (fun (k : Fin n) ↦ p (k.castLE (Nat.le_succ n)))
      = (fun (k : Fin n) ↦ q (k.castLE (Nat.le_succ n))) := by
  classical
  rw [Lax392996Proofs.Foreign.Query.rewriting_valid_joinCond_eval]
  constructor
  · intro hForall
    funext k
    have := hForall k
    rw [Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_left, Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_right] at this
    exact this
  · intro heq k
    rw [Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_left, Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_right]
    exact congrFun heq k

export Lax392996Proofs.Foreign (selFilter_cast_append_2n2_iff)

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

open Lax392996Proofs.Foreign.AnnotatedRelation in
/-- Selection pushes through `AnnotatedRelation.toComposite` via the
`Tuple.fromComposite ∘ AnnotatedTuple.toComposite = id` roundtrip:
filtering before taking the composite encoding equals filtering the composite
encoding by the same predicate composed with `Tuple.fromComposite`. -/
lemma _root_.Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_filter
    {T K : Type} [Lax392996.Databases.ValueType T] [Zero K] {n : ℕ}
    (ar : Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) (pred : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n → Prop)
    [DecidablePred pred] :
    Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite (Multiset.filter pred ar)
    = ar.toComposite.filter (fun t : Lax392996.Databases.Tuple (T⊕K) (n+1) ↦ pred (Lax392996Proofs.Foreign.Tuple.fromComposite t)) := by
  unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
  rw [Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro p _
  rw [Function.comp_apply, Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite]

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation

export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_filter)

end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace AnnotatedRelation
export Lax392996Proofs.Foreign.AnnotatedRelation (toComposite_filter)
end AnnotatedRelation

open Lax392996Proofs.Foreign.Multiset in
/-- **Semijoin reduction.** Given multisets `r : Multiset α` and `s : Multiset β` and
a key function `g : α → β`, with `s` `Nodup`, the projection-after-filter of the
cartesian product (keeping pairs whose `g`-image matches) coincides with filtering
`r` to those `a` whose `g a` belongs to `s`. This is the multiset version of the
relational semijoin and is the structural identity behind the `unmatched_eq`
half of the `Diff`-case rewriting correctness. -/
lemma _root_.Lax392996Proofs.Foreign.Multiset.semijoin_proj_eq_filter {α β : Type*} [DecidableEq β]
    (r : Multiset α) (s : Multiset β) (g : α → β) (hs : s.Nodup) :
    ((Multiset.product r s).filter (fun pair : α × β ↦ g pair.1 = pair.2)).map Prod.fst
    = r.filter (fun a ↦ g a ∈ s) := by
  show ((r ×ˢ s).filter (fun pair : α × β ↦ g pair.1 = pair.2)).map Prod.fst
       = r.filter (fun a ↦ g a ∈ s)
  induction r using Multiset.induction with
  | empty => simp
  | cons hd tl ih =>
    rw [Multiset.cons_product, Multiset.filter_add, Multiset.map_add, ih,
        Multiset.filter_cons]
    congr 1
    -- Show ((s.map (Prod.mk hd)).filter (fun pair => g pair.1 = pair.2)).map Prod.fst
    --    = if g hd ∈ s then {hd} else 0
    rw [Multiset.filter_map, Multiset.map_map]
    -- Goal: (s.filter (fun b => g hd = b)).map (Prod.fst ∘ Prod.mk hd) = ...
    show (s.filter (fun b ↦ g hd = b)).map (fun _ ↦ hd) = _
    by_cases hgmem : g hd ∈ s
    · -- s.filter (g hd = ·) = {g hd} since s is Nodup; map by constant gives {hd}.
      rw [if_pos hgmem]
      have hcount : s.count (g hd) = 1 := Multiset.count_eq_one_of_mem hs hgmem
      -- Convert filter to count.
      have hfilter_eq : s.filter (fun b ↦ g hd = b) = {g hd} := by
        ext b
        rw [Multiset.count_filter, Multiset.count_singleton]
        by_cases hb : g hd = b
        · subst hb
          rw [if_pos rfl]
          exact hcount.trans (if_pos rfl).symm
        · simp [hb, Ne.symm hb]
      rw [hfilter_eq, Multiset.map_singleton]
    · -- s.filter (g hd = ·) = 0 since g hd ∉ s; map gives 0.
      rw [if_neg hgmem]
      have hfilter_eq : s.filter (fun b ↦ g hd = b) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro b hb heq
        exact hgmem (heq ▸ hb)
      rw [hfilter_eq, Multiset.map_zero]

namespace Multiset
export Lax392996Proofs.Foreign.Multiset (semijoin_proj_eq_filter)
end Multiset

open Lax392996Proofs.Foreign.Multiset in
/-- **Keyed-projection semijoin.** Generalizes `Multiset.semijoin_proj_eq_filter` in two
directions: the right multiset is the image `S.map val` of a `Nodup` keyset `S` under a
value function `val : β → γ`, and the projection is an arbitrary `mk : α → γ → δ` rather
than `Prod.fst`. The compatibility hypothesis `h_val` asserts that `key_s ∘ val` is the
identity on `S` (i.e., `val` reconstructs an element whose `key_s`-image is the original
key). The semijoin then reduces to filtering `r` by `key_r a ∈ S` and projecting through
`mk a (val (key_r a))` (the unique matching `γ`-value). This is the structural identity
behind the `matched_eq` half of the `Diff`-case rewriting correctness. -/
lemma _root_.Lax392996Proofs.Foreign.Multiset.semijoin_keyed_proj_eq_filter
    {α γ δ : Type*} {β : Type*} [DecidableEq β]
    (r : Multiset α) (S : Multiset β) (val : β → γ)
    (key_r : α → β) (key_s : γ → β) (mk : α → γ → δ)
    (hS : S.Nodup)
    (h_val : ∀ v ∈ S, key_s (val v) = v) :
    ((Multiset.product r (S.map val)).filter
        (fun pair : α × γ ↦ key_r pair.1 = key_s pair.2)).map
      (fun pair ↦ mk pair.1 pair.2)
    = (r.filter (fun a ↦ key_r a ∈ S)).map (fun a ↦ mk a (val (key_r a))) := by
  show ((r ×ˢ (S.map val)).filter (fun pair : α × γ ↦ key_r pair.1 = key_s pair.2)).map
        (fun pair ↦ mk pair.1 pair.2)
      = (r.filter (fun a ↦ key_r a ∈ S)).map (fun a ↦ mk a (val (key_r a)))
  induction r using Multiset.induction with
  | empty => simp
  | cons hd tl ih =>
    rw [Multiset.cons_product, Multiset.filter_add, Multiset.map_add, ih,
        Multiset.filter_cons, Multiset.map_add]
    congr 1
    -- First term: handle the head's contribution.
    -- LHS: Multiset.map (fun pair ↦ mk pair.1 pair.2)
    --        (Multiset.filter cond ((S.map val).map (Prod.mk hd)))
    rw [Multiset.filter_map, Multiset.map_map]
    show ((S.map val).filter (fun b ↦ key_r hd = key_s b)).map (fun b ↦ mk hd b) = _
    rw [Multiset.filter_map]
    -- Convert `key_r hd = key_s (val v)` to `key_r hd = v` on `S` via `h_val`.
    have hcong : Multiset.filter (fun v ↦ key_r hd = key_s (val v)) S
               = Multiset.filter (fun v ↦ key_r hd = v) S := by
      apply Multiset.filter_congr
      intro v hv
      rw [h_val v hv]
    show (Multiset.map val
            (Multiset.filter ((fun b ↦ key_r hd = key_s b) ∘ val) S)).map (fun b ↦ mk hd b) = _
    simp only [Function.comp]
    rw [hcong, Multiset.map_map]
    show (S.filter (fun v ↦ key_r hd = v)).map (fun v ↦ mk hd (val v)) = _
    by_cases hmem : key_r hd ∈ S
    · -- `S.filter (key_r hd = ·) = {key_r hd}` since `S` is `Nodup`.
      rw [if_pos hmem]
      have hcount : S.count (key_r hd) = 1 := Multiset.count_eq_one_of_mem hS hmem
      have hfilter_eq : S.filter (fun v ↦ key_r hd = v) = {key_r hd} := by
        ext b
        rw [Multiset.count_filter, Multiset.count_singleton]
        by_cases hb : key_r hd = b
        · subst hb
          rw [if_pos rfl]
          exact hcount.trans (if_pos rfl).symm
        · simp [hb, Ne.symm hb]
      rw [hfilter_eq, Multiset.map_singleton, Multiset.map_singleton]
    · rw [if_neg hmem]
      have hfilter_eq : S.filter (fun v ↦ key_r hd = v) = 0 :=
        Multiset.filter_eq_nil.mpr (fun v hv heq ↦ hmem (heq ▸ hv))
      rw [hfilter_eq, Multiset.map_zero, Multiset.map_zero]

namespace Multiset
export Lax392996Proofs.Foreign.Multiset (semijoin_keyed_proj_eq_filter)
end Multiset

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- The `ProvSum` of `q.rewriting` (the inner ⊕-gate creation used in both
the `Dedup` and `Diff` rewritings) evaluates to a map over the deduped
data-projection of the inner annotated relation, with each row paired (via
`AnnotatedTuple.toComposite`) with the semiring sum of the matching
annotations. -/
lemma _root_.Lax392996Proofs.Foreign.Query.evaluate_agg_rewriting_eq
    {T K : Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K]
    {n : ℕ} (q : Lax392996.RelationalAlgebra.Query T n) (hq : q.source) (d : Lax392996.AnnotatedDatabases.AnnotatedDatabase T K)
    (ih : (q.evaluateAnnotated hq d).toComposite
        = (q.rewriting hq).evaluate d.toComposite) :
    Lax392996.MultisetSemantics.Query.evaluate (Lax392996.RelationalAlgebra.Query.ProvSum (fun k : Fin n ↦ k.castLE (Nat.le_succ n))
                #(Fin.last n) (q.rewriting hq)) d.toComposite
    = Multiset.map (fun v : Lax392996.Databases.Tuple T n ↦ Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
          (v, (Multiset.map Prod.snd
                (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v)
                  (q.evaluateAnnotated hq d))).sum))
        ((q.evaluateAnnotated hq d).map Prod.fst).dedup := by
  -- This proof mirrors `rhs_eq` in the `Dedup` case below.
  unfold Lax392996.MultisetSemantics.Query.evaluate
  simp only [Lax392996.MultisetSemantics.Query.evaluate, Lax392996.RelationalAlgebra.Term.eval]
  rw [← ih]
  apply Eq.trans (b := Multiset.map _
    (Multiset.map (fun v ↦ (fun k : Fin _ ↦ (Sum.inl (v k) : T⊕K)))
      (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq d)))))
  · apply congrArg
    convert Lax392996Proofs.Foreign.AnnotatedRelation.dedup_toComposite_proj_first_n
      (q.evaluateAnnotated hq d) (Nat.le_succ _) using 2
  · rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro v _hv
    simp only [Function.comp]
    rw [Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_filter_map_last]
    rw [show (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ (Sum.inr p.2 : T⊕K))
          = (fun k ↦ (Sum.inr k : T⊕K)) ∘ Prod.snd from rfl]
    unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
    funext k
    by_cases hk : k = Fin.last n
    · subst hk
      simp [Fin.append, Fin.addCases]
      show Multiset.fold Lax392996.MultisetSemantics.addFn (0 : T⊕K)
          (Multiset.map (fun x : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ (Sum.inr x.2 : T⊕K))
            (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
              (q.evaluateAnnotated hq d)))
        = (Sum.inr (Multiset.map Prod.snd (Multiset.filter
            (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
            (q.evaluateAnnotated hq d))).sum : T⊕K)
      rw [show Multiset.map (fun x : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ (Sum.inr x.2 : T⊕K))
            (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
              (q.evaluateAnnotated hq d))
          = Multiset.map (fun k : K ↦ (Sum.inr k : T⊕K))
              (Multiset.map Prod.snd
                (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
                  (q.evaluateAnnotated hq d))) from
        (Multiset.map_map _ _ _).symm]
      exact Lax392996Proofs.Foreign.Multiset.fold_addFn_map_inr _
    · have hlt : (k : ℕ) < n := Fin.val_lt_last hk
      simp [Fin.append, Fin.addCases, hlt]

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (evaluate_agg_rewriting_eq)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (evaluate_agg_rewriting_eq)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
/-- Instance-polymorphic restatement of `Query.rewriting_valid_diff_inner_dd`.
Inside the `Diff` case of `rewriting_valid`, Lean's instance synthesis picks
inconsistent `DecidableEq (T⊕K)` instances at different positions in the goal:
the inner `Multiset.dedup` is elaborated with `LinearOrder.toDecidableEq` (via
`ValueType (T⊕K)`), while the surrounding `Multiset.filter`'s `decidableMem`
uses `instDecidableEqSum`. This wrapper accepts both as explicit parameters and
bridges to the canonical helper via `Subsingleton.elim`. -/
lemma _root_.Lax392996Proofs.Foreign.Query.rewriting_valid_diff_inner_dd_inst
  {T K: Type} [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K] {n: ℕ}
  (AR₁ AR₂ : Lax392996.AnnotatedDatabases.AnnotatedRelation T K n)
  (instA : DecidableEq (Lax392996.Databases.Tuple (T⊕K) n))
  (instDP : DecidablePred (fun u : Lax392996.Databases.Tuple (T⊕K) n ↦
      u ∉ @Multiset.map (Lax392996.Databases.Tuple (T⊕K) (n+1)) (Lax392996.Databases.Tuple (T⊕K) n)
            (fun (u': Lax392996.Databases.Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
            AR₂.toComposite)) :
  @Multiset.dedup _ instA
    (@Multiset.filter _ _ instDP
      (@Multiset.map (Lax392996.Databases.Tuple (T⊕K) (n+1)) (Lax392996.Databases.Tuple (T⊕K) n)
        (fun (u': Lax392996.Databases.Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
        AR₁.toComposite))
  = Multiset.map (fun (v: Lax392996.Databases.Tuple T n) (k: Fin n) ↦ (Sum.inl (v k): T⊕K))
      (Multiset.filter (fun v ↦ v ∉ Multiset.map Prod.fst AR₂)
        (Multiset.map Prod.fst AR₁)).dedup := by
  convert Lax392996Proofs.Foreign.Query.rewriting_valid_diff_inner_dd AR₁ AR₂ using 4

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid_diff_inner_dd_inst)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid_diff_inner_dd_inst)
end Query

namespace Lax392996.RelationalAlgebra.Query

open Lax392996Proofs.Foreign.Query in
theorem _root_.Lax392996Proofs.Foreign.Query.rewriting_valid
  [Lax392996.Databases.ValueType T] [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K] [Lax392996.SemiringsWithMonus.HasAltLinearOrder K]
  (q: Lax392996.RelationalAlgebra.Query T n) (hq: q.source) :
  ∀ (d: Lax392996.AnnotatedDatabases.AnnotatedDatabase T K), (q.evaluateAnnotated hq d).toComposite = (q.rewriting hq).evaluate d.toComposite := by
  intro d
  induction q with
  | Rel n s =>
    unfold Lax392996Proofs.Foreign.Query.evaluateAnnotated Lax392996.MultisetSemantics.Query.evaluate Lax392996.RewritingRules.Query.rewriting
    simp
    match ha: Lax392996.AnnotatedDatabases.AnnotatedDatabase.find n s d with
    | none =>
      rw[Lax392996Proofs.Foreign.AnnotatedDatabase.find_toComposite_none] at ha
      rw[ha]
      simp[Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite]
    | some rn =>
      rw[Lax392996Proofs.Foreign.AnnotatedDatabase.find_toComposite_some] at ha
      rw[ha]
  | @Proj m n' ts q ih =>
    unfold Lax392996Proofs.Foreign.Query.evaluateAnnotated Lax392996.MultisetSemantics.Query.evaluate Lax392996.RewritingRules.Query.rewriting
    simp
    rw[← ih (Lax392996Proofs.Foreign.Query.sourceProj hq rfl)]
    unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
    simp
    apply congrFun
    apply congrArg
    funext t k
    by_cases hkn' : k=Fin.last n'
    . simp[hkn']
      simp[Lax392996.RelationalAlgebra.Term.eval]
      unfold Lax392996.RelationalAlgebra.Query.arity
      have : ∀ x, Fin.last x = Fin.natAdd (Fin.last x) 0 := by
        simp
        intro x
        rfl
      rw[this n',this m]
      unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
      simp [Fin.append_right]
    . simp at hkn'
      have hlt := Fin.val_lt_last hkn'
      simp[hlt]
      have : k = (Fin.castAdd 1 (k.castLT hlt): Fin (n'+1)) := by simp
      rewrite (occs := [1]) [this]
      unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
      rw [Fin.append_left]
      rw[Lax392996Proofs.Foreign.Term.castToAnnotatedTuple_eval]
      rfl
  | Sel φ q' ih =>
    unfold Lax392996Proofs.Foreign.Query.evaluateAnnotated Lax392996.MultisetSemantics.Query.evaluate Lax392996.RewritingRules.Query.rewriting
    simp
    rw[← ih (Lax392996Proofs.Foreign.Query.sourceSel hq rfl)]
    unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
    rw[Multiset.filter_map]
    apply congrArg
    apply congrFun
    simp[Function.comp_def]
    unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
    conv =>
      rhs
      congr
      . ext x
        rw[Lax392996Proofs.Foreign.Selection.castToAnnotatedTuple_eval φ]
        skip
      . apply φ.evalDecidableAnnotated
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    unfold Lax392996Proofs.Foreign.Query.evaluateAnnotated Lax392996.MultisetSemantics.Query.evaluate Lax392996.RewritingRules.Query.rewriting
    simp
    have heq : (Fin (n₁ + n₂) → T) = (Fin n → T) := by simp[hn]
    rw[Lax392996Proofs.Foreign.Query.rewriting_valid_prod0 hn heq]
    rw[Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_map_product]
    rw[ih₁ (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).left]
    rw[ih₂ (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).right]
    simp
    rw[eq_comm]
    rw[Lax392996Proofs.Foreign.Relation.cast_eq]
    conv_lhs =>
      unfold Lax392996.MultisetSemantics.Query.evaluate
      simp[(·*·)]
      skip
    rw[Lax392996Proofs.Foreign.Query.rewriting_valid_prod1 (Lax392996Proofs.Foreign.Query.rewriting_valid_prod_heqn hn)]
    -- Lean v4.29's pattern unifier cannot find `Multiset.map (Multiset.map ...)` in either
    -- side because `Tuple.cast`/`Fin.append` hide the codomain through their motives.
    -- Reduce both sides to a single `Multiset.map` by exposing the head structure via
    -- `Eq.trans` with the desired `Multiset.map_map` instance – letting Lean infer the
    -- specific function arguments avoids the failing higher-order match.
    refine Eq.trans (Multiset.map_map _ _ _) (Eq.trans ?_ (Multiset.map_map _ _ _).symm)
    apply Multiset.map_congr rfl
    intro p _
    simp only [Function.comp]
    funext k
    rw[Lax392996Proofs.Foreign.Tuple.cast_get]
    subst hn
    by_cases hlt₁: ↑k < n₁
    . simp[hlt₁]
      simp only[Lax392996.RelationalAlgebra.Term.eval]
      have hksucc : ↑(Fin.castLE (by omega : n₁+n₂+1 ≤ n₁+n₂+2) k) < n₁+1 := by simp; omega
      rw[Lax392996Proofs.Foreign.Query.tupleCast_append_left (n:=n₁+n₂+2) p.1 p.2 (by omega) _ hksucc]
      apply congrArg
      refine Fin.eq_of_val_eq ?_
      simp[Fin.castLT]
    . by_cases hlt: ↑k < n₁+n₂
      . simp[hlt₁,hlt]
        simp only[Lax392996.RelationalAlgebra.Term.eval]
        simp only [← Fin.ofNat_eq_cast]
        have hk₁₂: ((k:ℕ)+1)<n₁+n₂+2 := by omega
        rw[Lax392996Proofs.Foreign.Query.tupleCast_append_right (n:=n₁+n₂+2) p.1 p.2 (by omega)
              (Fin.ofNat (n₁+n₂+2) ((k:ℕ)+1))
              (by simp [Fin.ofNat, Nat.mod_eq_of_lt hk₁₂]; omega)]
        apply congrArg
        refine Fin.eq_of_val_eq ?_
        have hkn1 : ((k:ℕ)-n₁)<n₂+1 := by omega
        simp [Fin.ofNat, Nat.mod_eq_of_lt hk₁₂, Nat.mod_eq_of_lt hkn1]
      . simp[hlt₁,hlt]
        simp only[Lax392996.RelationalAlgebra.Term.eval]
        simp only [← Fin.ofNat_eq_cast]
        have hn1 : n₁<n₁+n₂+2 := by omega
        rw[Lax392996Proofs.Foreign.Query.tupleCast_append_left (n:=n₁+n₂+2) p.1 p.2 (by omega)
              (Fin.ofNat (n₁+n₂+2) n₁) (by simp [Fin.ofNat, Nat.mod_eq_of_lt hn1])]
        rw[Lax392996Proofs.Foreign.Query.tupleCast_append_right (n:=n₁+n₂+2) p.1 p.2 (by omega)
              (Fin.last (n₁+n₂+1)) (by simp)]
        congr
        . apply congrArg
          apply Fin.eq_of_val_eq
          simp [Fin.castLT, Fin.ofNat, Nat.mod_eq_of_lt hn1]
        . apply congrArg
          apply Fin.eq_of_val_eq
          simp
  | Sum q₁ q₂ ih₁ ih₂ =>
    unfold Lax392996Proofs.Foreign.Query.evaluateAnnotated Lax392996.MultisetSemantics.Query.evaluate Lax392996.RewritingRules.Query.rewriting
    simp
    rw[ih₁ (Lax392996Proofs.Foreign.Query.sourceSum hq rfl).left]
    rw[ih₂ (Lax392996Proofs.Foreign.Query.sourceSum hq rfl).right]
  | Dedup q ih =>
    have hq' := Lax392996Proofs.Foreign.Query.sourceDedup hq rfl
    have ih' := ih hq'
    -- LHS = common form
    have lhs_eq :
      Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
        (Multiset.ofList (Lax392996Proofs.Foreign.groupByKey (q.evaluateAnnotated hq' d)).val :
          Lax392996.AnnotatedDatabases.AnnotatedRelation T K _)
      = Multiset.map
          (fun v: Lax392996.Databases.Tuple T _ ↦
            Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
              (v, (Multiset.map Prod.snd
                    (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
                      (q.evaluateAnnotated hq' d))).sum))
          (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq' d))) := by
      unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
      rw[Lax392996Proofs.Foreign.groupByKey_multiset_eq]
      exact Multiset.map_map _ _ _
    -- RHS = common form
    have rhs_eq :
      Lax392996.MultisetSemantics.Query.evaluate ((Lax392996.RelationalAlgebra.Query.Dedup q).rewriting hq) d.toComposite
      = Multiset.map
          (fun v: Lax392996.Databases.Tuple T _ ↦
            Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
              (v, (Multiset.map Prod.snd
                    (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
                      (q.evaluateAnnotated hq' d))).sum))
          (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq' d))) := by
      unfold Lax392996.RewritingRules.Query.rewriting Lax392996.MultisetSemantics.Query.evaluate
      simp only [Lax392996.MultisetSemantics.Query.evaluate, Lax392996.RelationalAlgebra.Term.eval]
      rw[← ih']
      apply Eq.trans (b := Multiset.map _
        (Multiset.map (fun v ↦ (fun k: Fin _ ↦ (Sum.inl (v k): T⊕K)))
          (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq' d)))))
      · apply congrArg
        convert Lax392996Proofs.Foreign.AnnotatedRelation.dedup_toComposite_proj_first_n
          (q.evaluateAnnotated hq' d) (Nat.le_succ _) using 2
      · rw[Multiset.map_map]
        apply Multiset.map_congr rfl
        intro v _hv
        simp only [Function.comp]
        rw[Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_filter_map_last]
        rw[show (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ (Sum.inr p.2: T⊕K))
              = (fun k ↦ (Sum.inr k: T⊕K)) ∘ Prod.snd from rfl]
        -- Prove both sides equal via pointwise funext into the Fin.append/toComposite structure.
        unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
        funext k
        rename_i n
        by_cases hk: k = Fin.last n
        · subst hk
          simp [Fin.append, Fin.addCases]
          -- Under the last component, we need fold-addFn-map-inr applied.
          show Multiset.fold Lax392996.MultisetSemantics.addFn (0 : T⊕K)
              (Multiset.map (fun x : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ (Sum.inr x.2 : T⊕K))
                (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
                  (q.evaluateAnnotated hq' d)))
            = (Sum.inr (Multiset.map Prod.snd (Multiset.filter
                (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
                (q.evaluateAnnotated hq' d))).sum : T⊕K)
          rw [show Multiset.map (fun x : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ (Sum.inr x.2 : T⊕K))
                (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
                  (q.evaluateAnnotated hq' d))
              = Multiset.map (fun k : K ↦ (Sum.inr k : T⊕K))
                  (Multiset.map Prod.snd
                    (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ p.1 = v)
                      (q.evaluateAnnotated hq' d))) from
            (Multiset.map_map _ _ _).symm]
          exact Lax392996Proofs.Foreign.Multiset.fold_addFn_map_inr _
        · have hlt : (k: ℕ) < n := Fin.val_lt_last hk
          simp [Fin.append, Fin.addCases, hlt]
    rw[← lhs_eq] at rhs_eq
    unfold Lax392996Proofs.Foreign.Query.evaluateAnnotated
    exact rhs_eq.symm
  | Diff q₁ q₂ ih₁ ih₂ =>
    have hq'₁ := (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).left
    have hq'₂ := (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).right
    have ih'₁ := ih₁ hq'₁
    have ih'₂ := ih₂ hq'₂
    -- LHS: (ar₁.map (fun (u,α) ↦ (u, α - β_u))).toComposite
    -- where β_u = sum of annotations of u in ar₂.
    -- Rewrite β_u via find?/getD using our helper.
    -- Common form: each tuple from ar₁ with its annotation minus ar₂'s matching sum.
    have lhs_eq :
      Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
        ((q₁.evaluateAnnotated hq'₁ d).map (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦
          (p.1, p.2 - (Multiset.map Prod.snd
            (Multiset.filter (fun q: Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d))).sum)))
      = ((Lax392996.RelationalAlgebra.Query.Diff q₁ q₂).evaluateAnnotated hq d).toComposite := by
      show _ = Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite _
      congr 1
      apply Multiset.map_congr rfl
      intro p _
      congr 1
      rw[← Lax392996Proofs.Foreign.Query.rewriting_valid_find_getD_eq_sum (q₂.evaluateAnnotated hq'₂ d) p.1]
    -- RHS = evaluate (Sum (Proj ts₁ prod₁) (Proj ts₂ prod₂)) d.toComposite
    rename_i n -- bring the arity variable into scope as `n`
    -- The unmatched part of the rewriting (coming from `Proj ts₁ prod₁`).
    have unmatched_eq :
      Lax392996.MultisetSemantics.Query.evaluate
        (Lax392996.RelationalAlgebra.Query.Proj (fun (k: Fin (n+1)) ↦ #(k.castLE (by omega)))
          (Lax392996.RelationalAlgebra.Query.Sel (((List.range n).map
              (λ k ↦ @Lax392996.RelationalAlgebra.Selection.BT (T⊕K) (2*n+1)
                (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
              (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True)
            (@Lax392996.RelationalAlgebra.Query.Prod _ (n+1) n (2*n+1) (by omega) (q₁.rewriting hq'₁)
              (Lax392996.RelationalAlgebra.Query.Dedup (Lax392996.RelationalAlgebra.Query.Diff
                (Lax392996.RelationalAlgebra.Query.Proj (λ (k: Fin n) ↦ Lax392996.RelationalAlgebra.Term.index (k.castLE (Nat.le_succ _)))
                  (q₁.rewriting hq'₁))
                (Lax392996.RelationalAlgebra.Query.Proj (λ (k: Fin n) ↦ Lax392996.RelationalAlgebra.Term.index (k.castLE (Nat.le_succ _)))
                  (q₂.rewriting hq'₂)))))))
        d.toComposite
      = Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
          (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦
            p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
            (q₁.evaluateAnnotated hq'₁ d)) := by
      -- Abbreviations for the two evaluated annotated relations.
      set AR₁ := q₁.evaluateAnnotated hq'₁ d with hAR₁
      set AR₂ := q₂.evaluateAnnotated hq'₂ d with hAR₂
      -- Unfold `evaluate` and reduce the inner subqueries via the induction hypotheses.
      simp only [Lax392996.MultisetSemantics.Query.evaluate, Lax392996.RelationalAlgebra.Term.eval]
      rw[← ih'₁, ← ih'₂]
      -- The goal contains the inner-Diff form
      --   (Multiset.filter (· ∉ Multiset.map proj_n AR₂.toComposite)
      --     (Multiset.map proj_n AR₁.toComposite)).dedup
      -- which is `Query.rewriting_valid_diff_inner_dd`'s LHS. A direct `rw`/`simp only`
      -- with that helper fails because the goal's `.dedup` is elaborated with
      -- `LinearOrder.toDecidableEq` (via ValueType (T⊕K)) while the helper's `.dedup`
      -- uses `instDecidableEqSum`; the instances are propositionally equal but not
      -- syntactically. The bridge `Query.rewriting_valid_diff_inner_dd_inst` accepts both
      -- `DecidableEq` and `DecidablePred` instances explicitly and discharges the gap
      -- via `Subsingleton.elim` (its proof is `convert ... using 4`), letting `simp_rw`
      -- finally fire here.
      simp_rw [Lax392996Proofs.Foreign.Query.rewriting_valid_diff_inner_dd_inst AR₁ AR₂]
      -- The remaining goal is a semijoin reduction:
      --   map proj_outer (filter selFilter (Relation.cast _ (AR₁.toComposite * Big)))
      --   = AnnotatedRelation.toComposite (filter (· ∉ map fst AR₂) AR₁)
      -- where Big = map (Sum.inl-lift) (filter (· ∉ map fst AR₂) (map fst AR₁)).dedup.
      -- Move the RHS filter inside `toComposite` via `AnnotatedRelation.toComposite_filter`
      -- so both sides become filters on `AR₁.toComposite`.
      rw [Lax392996Proofs.Foreign.AnnotatedRelation.toComposite_filter, Lax392996Proofs.Foreign.Relation.cast_eq_map]
      simp only [(·*·), Mul.mul, Multiset.map_map]
      rw [Multiset.filter_map, Multiset.map_map]
      simp only [Function.comp_def]
      -- Rewrite the outer map function to `Prod.fst` via the projection helper.
      conv_lhs =>
        rw [Multiset.map_congr (rfl) (fun x _ ↦ Lax392996Proofs.Foreign.proj_outer_cast_append_eq_fst (by omega) x.1 x.2)]
      -- Rewrite the filter predicate to `fun x => first_n x.1 = x.2` via the selFilter helper.
      have hNeZero : NeZero (2 * n + 1) := ⟨by omega⟩
      -- The product of multisets; we will filter and project it.
      set Prod1 : Multiset (Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) n) := Multiset.product AR₁.toComposite
        (Multiset.map (fun (v : Lax392996.Databases.Tuple T n) (k : Fin n) ↦ (Sum.inl (v k) : T⊕K))
          (Multiset.filter (fun v ↦ v ∉ Multiset.map Prod.fst AR₂)
            (Multiset.map Prod.fst AR₁)).dedup) with hProd1
      -- Provide DecidablePred instances for both predicates.
      let dp1 : DecidablePred (fun x : Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) n =>
          Lax392996.RelationalAlgebra.Selection.eval (((List.range n).map
            (λ k ↦ @Lax392996.RelationalAlgebra.Selection.BT (T⊕K) (2*n+1)
              (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
            (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True) (Lax392996Proofs.Foreign.Tuple.cast (by omega) (Fin.append x.1 x.2))) :=
        fun x => Lax392996.RelationalAlgebra.Selection.evalDecidable _ _
      let dp2 : DecidablePred (fun x : Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) n =>
          (fun k : Fin n ↦ x.1 (k.castLE (Nat.le_succ n))) = x.2) :=
        fun x => decEq _ _
      have hcong : @Multiset.filter _ _ dp1 Prod1 = @Multiset.filter _ _ dp2 Prod1 :=
        Multiset.filter_congr (fun x _ ↦ Lax392996Proofs.Foreign.selFilter_cast_append_iff (by omega) x.1 x.2)
      -- Apply hcong via `change` + `rw`. First normalize `Nat.mul 2 n` to `2 * n` so the
      -- LHS predicate matches.
      change Multiset.map Prod.fst
        (@Multiset.filter _ _ dp1 Prod1) = _
      rw [hcong]
      -- Apply the semijoin lemma. Need `Big.Nodup`.
      have hBig_nodup :
        (Multiset.map (fun (v : Lax392996.Databases.Tuple T n) (k : Fin n) ↦ (Sum.inl (v k) : T⊕K))
          (Multiset.filter (fun v ↦ v ∉ Multiset.map Prod.fst AR₂)
            (Multiset.map Prod.fst AR₁)).dedup).Nodup :=
        (Multiset.nodup_dedup _).map Lax392996Proofs.Foreign.Sum.inl_lift_injective
      rw [hProd1]
      refine (Lax392996Proofs.Foreign.Multiset.semijoin_proj_eq_filter AR₁.toComposite _
            (fun (p : Lax392996.Databases.Tuple (T⊕K) (n+1)) (k : Fin n) ↦ p (k.castLE (Nat.le_succ n)))
            hBig_nodup).trans ?_
      -- Show the two filter predicates are equivalent on AR₁.toComposite.
      apply Multiset.filter_congr
      intro t ht
      -- t ∈ AR₁.toComposite: t = ap.toComposite for some ap ∈ AR₁.
      obtain ⟨ap, hap, hap_eq⟩ := Multiset.mem_map.mp ht
      subst hap_eq
      -- Now t = ap.toComposite. Compute the first-n projection.
      have hfirst_n :
          (fun (k : Fin n) ↦ ap.toComposite (k.castLE (Nat.le_succ n)))
          = fun (k : Fin n) ↦ (Sum.inl (ap.fst k) : T⊕K) := by
        funext k
        exact Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE ap k
      rw [hfirst_n, Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite]
      -- Goal: Sum.inl-lift ap.fst ∈ Big_lifted ↔ ap.fst ∉ map fst AR₂
      constructor
      · intro hmem hcontra
        obtain ⟨v, hv_in, hv_eq⟩ := Multiset.mem_map.mp hmem
        rw [Multiset.mem_dedup, Multiset.mem_filter] at hv_in
        -- v ∈ map fst AR₁ ∧ v ∉ map fst AR₂
        have hv_eq_fst : v = ap.fst := Lax392996Proofs.Foreign.Sum.inl_lift_injective hv_eq
        rw [hv_eq_fst] at hv_in
        exact hv_in.2 hcontra
      · intro hnotin
        refine Multiset.mem_map.mpr ⟨ap.fst, ?_, rfl⟩
        rw [Multiset.mem_dedup, Multiset.mem_filter]
        refine ⟨?_, hnotin⟩
        exact Multiset.mem_map.mpr ⟨ap, hap, rfl⟩
    -- The matched part of the rewriting (coming from `Proj ts₂ prod₂`).
    have matched_eq :
      Lax392996.MultisetSemantics.Query.evaluate
        (Lax392996.RelationalAlgebra.Query.Proj (fun (k: Fin (n+1)) ↦
            if ↑k < n then #(k.castLE (by omega))
            else Lax392996.RelationalAlgebra.Term.sub #(Fin.ofNat _ n) #(Fin.last (2*n+1)))
          (Lax392996.RelationalAlgebra.Query.Sel (((List.range n).map
              (λ k ↦ @Lax392996.RelationalAlgebra.Selection.BT (T⊕K) (2*n+2)
                (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
              (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True)
            (@Lax392996.RelationalAlgebra.Query.Prod _ (n+1) (n+1) (2*n+2) (by omega) (q₁.rewriting hq'₁)
              (Lax392996.RelationalAlgebra.Query.ProvSum (fun k: Fin n ↦ k.castLE (by simp))
                #(Fin.last n) (q₂.rewriting hq'₂)))))
        d.toComposite
      = (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦
            p.1 ∈ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
          (q₁.evaluateAnnotated hq'₁ d)).map
          (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
            (p.1, p.2 - (Multiset.map Prod.snd
              (Multiset.filter (fun q: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ q.1 = p.1)
                (q₂.evaluateAnnotated hq'₂ d))).sum)) := by
      set AR₁ := q₁.evaluateAnnotated hq'₁ d with hAR₁
      set AR₂ := q₂.evaluateAnnotated hq'₂ d with hAR₂
      -- Derive the unfolded-form Agg equation: after `simp only [evaluate, Term.eval]`,
      -- the inner `evaluate (Agg ...) d.toComposite` matches the helper's LHS after
      -- the same simp. Pre-compute it here so we can `rw` once the outer Proj/Sel/Prod
      -- have been unfolded.
      have hAggForm := Lax392996Proofs.Foreign.Query.evaluate_agg_rewriting_eq q₂ hq'₂ d ih'₂
      simp only [Lax392996.MultisetSemantics.Query.evaluate, Lax392996.RelationalAlgebra.Term.eval] at hAggForm
      rw [← ih'₂] at hAggForm
      -- Unfold the outer Proj/Sel/Prod (and the inner Agg, which gets re-folded via
      -- `hAggForm`).
      simp only [Lax392996.MultisetSemantics.Query.evaluate, Lax392996.RelationalAlgebra.Term.eval]
      rw [← ih'₁, ← ih'₂]
      -- Substitute the unfolded Agg form with its closed form via `hAggForm`.
      rw [hAggForm]
      -- Now: map (proj_outer) (filter (selFilter)
      --   (Relation.cast h (AR₁.toComposite * AggOutput))) = RHS
      rw [Lax392996Proofs.Foreign.Relation.cast_eq_map]
      simp only [(·*·), Mul.mul, Multiset.map_map]
      rw [Multiset.filter_map, Multiset.map_map]
      simp only [Function.comp_def]
      have hNeZero : NeZero (2 * n + 2) := ⟨by omega⟩
      -- Provide DecidablePred instances for both filter predicates explicitly.
      let dp1 : DecidablePred (fun x : Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) (n+1) =>
          Lax392996.RelationalAlgebra.Selection.eval (((List.range n).map
            (λ k ↦ @Lax392996.RelationalAlgebra.Selection.BT (T⊕K) (2*n+2)
              (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
            (λ t t' ↦ Lax392996.RelationalAlgebra.Selection.And t t') Lax392996.RelationalAlgebra.Selection.True) (Lax392996Proofs.Foreign.Tuple.cast (by omega) (Fin.append x.1 x.2))) :=
        fun x => Lax392996.RelationalAlgebra.Selection.evalDecidable _ _
      let dp2 : DecidablePred (fun x : Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) (n+1) =>
          (fun k : Fin n ↦ x.1 (k.castLE (Nat.le_succ n)))
          = (fun k : Fin n ↦ x.2 (k.castLE (Nat.le_succ n)))) :=
        fun x => decEq _ _
      -- Name the product of multisets for clarity.
      set Prod2 : Multiset (Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) (n+1)) :=
        Multiset.product AR₁.toComposite
          (Multiset.map (fun v : Lax392996.Databases.Tuple T n ↦ Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
              (v, (Multiset.map Prod.snd
                    (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) AR₂)).sum))
            ((AR₂.map Prod.fst).dedup)) with hProd2_def
      -- Rewrite the filter cond using selFilter_cast_append_2n2_iff.
      have hcong : @Multiset.filter _ _ dp1 Prod2 = @Multiset.filter _ _ dp2 Prod2 :=
        Multiset.filter_congr (fun x _ ↦ Lax392996Proofs.Foreign.selFilter_cast_append_2n2_iff (by omega) x.1 x.2)
      change Multiset.map (fun (x : Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) (n+1)) (k : Fin (n+1)) ↦
              (if ↑k < n then (#((Fin.castLE (by omega : n+1 ≤ 2*n+2)) k) : Lax392996.RelationalAlgebra.Term (T⊕K) (2*n+2))
                else Lax392996.RelationalAlgebra.Term.sub (#(Fin.ofNat (2*n+2) n)) (#(Fin.last (2*n+1)))).eval
                  (Lax392996Proofs.Foreign.Tuple.cast (by omega : (n+1)+(n+1) = 2*n+2) (Fin.append x.1 x.2)))
            (@Multiset.filter _ _ dp1 Prod2) = _
      rw [hcong]
      -- Convert filter cond from `first-n p = first-n q` (in `Tuple (T⊕K) n`) to
      -- `(fromComposite p).1 = (fromComposite q).1` (in `Tuple T n`) via Sum.inl-lift
      -- injectivity, valid for pairs in `Prod2`.
      let dp3 : DecidablePred (fun x : Lax392996.Databases.Tuple (T⊕K) (n+1) × Lax392996.Databases.Tuple (T⊕K) (n+1) =>
          (Lax392996Proofs.Foreign.Tuple.fromComposite x.1).1 = (Lax392996Proofs.Foreign.Tuple.fromComposite x.2).1) :=
        fun x => decEq _ _
      have hcong2 : @Multiset.filter _ _ dp2 Prod2 = @Multiset.filter _ _ dp3 Prod2 := by
        apply Multiset.filter_congr
        intro pair hpair
        rw [hProd2_def] at hpair
        obtain ⟨hp1, hp2⟩ := Multiset.mem_product.mp hpair
        obtain ⟨ap, _, hp1_eq⟩ := Multiset.mem_map.mp hp1
        obtain ⟨v, _, hq_eq⟩ := Multiset.mem_map.mp hp2
        have hfrom_p1 : (Lax392996Proofs.Foreign.Tuple.fromComposite pair.1).1 = ap.1 := by
          rw [← hp1_eq, Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite]
        have hfrom_p2 : (Lax392996Proofs.Foreign.Tuple.fromComposite pair.2).1 = v := by
          rw [← hq_eq, Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite]
        constructor
        · intro heq
          have hlift_eq :
              (fun k : Fin n ↦ (Sum.inl (ap.1 k) : T⊕K))
            = (fun k : Fin n ↦ (Sum.inl (v k) : T⊕K)) := by
            funext k
            have hcastle1 : pair.1 (k.castLE (Nat.le_succ n))
                          = (Sum.inl (ap.1 k) : T⊕K) := by
              rw [← hp1_eq]; exact Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE ap k
            have hcastle2 : pair.2 (k.castLE (Nat.le_succ n))
                          = (Sum.inl (v k) : T⊕K) := by
              rw [← hq_eq]
              exact Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE
                (v, (Multiset.map Prod.snd
                  (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) AR₂)).sum) k
            calc (Sum.inl (ap.1 k) : T⊕K)
                _ = pair.1 (k.castLE (Nat.le_succ n)) := hcastle1.symm
                _ = pair.2 (k.castLE (Nat.le_succ n)) := congrFun heq k
                _ = (Sum.inl (v k) : T⊕K) := hcastle2
          have hap_eq_v : ap.1 = v := Lax392996Proofs.Foreign.Sum.inl_lift_injective hlift_eq
          rw [hfrom_p1, hfrom_p2, hap_eq_v]
        · intro heq
          rw [hfrom_p1, hfrom_p2] at heq
          funext k
          have hcastle1 : pair.1 (k.castLE (Nat.le_succ n))
                        = (Sum.inl (ap.1 k) : T⊕K) := by
            rw [← hp1_eq]; exact Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE ap k
          have hcastle2 : pair.2 (k.castLE (Nat.le_succ n))
                        = (Sum.inl (v k) : T⊕K) := by
            rw [← hq_eq]
            exact Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_castLE
              (v, (Multiset.map Prod.snd
                (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) AR₂)).sum) k
          rw [hcastle1, hcastle2, heq]
      rw [hcong2]
      -- Apply the keyed-projection semijoin lemma with:
      --   r = AR₁.toComposite, S = (AR₂.map Prod.fst).dedup,
      --   val v = ATC (v, sum_β v), key_r p = (fromComposite p).1, key_s q = (fromComposite q).1,
      --   mk p q = the projection function we have.
      rw [hProd2_def]
      have hS_nodup : ((AR₂.map Prod.fst).dedup : Multiset (Lax392996.Databases.Tuple T n)).Nodup :=
        Multiset.nodup_dedup _
      have h_val_eq : ∀ v ∈ ((AR₂.map Prod.fst).dedup : Multiset (Lax392996.Databases.Tuple T n)),
          (Lax392996Proofs.Foreign.Tuple.fromComposite
            (Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
              (v, (Multiset.map Prod.snd
                    (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) AR₂)).sum))).1
            = v := by
        intro v _
        rw [Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite]
      have hsemi := @Lax392996Proofs.Foreign.Multiset.semijoin_keyed_proj_eq_filter
        (Lax392996.Databases.Tuple (T⊕K) (n+1)) (Lax392996.Databases.Tuple (T⊕K) (n+1)) (Lax392996.Databases.Tuple (T⊕K) (n+1))
        (Lax392996.Databases.Tuple T n) _
        AR₁.toComposite ((AR₂.map Prod.fst).dedup)
        (fun v : Lax392996.Databases.Tuple T n ↦ Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
          (v, (Multiset.map Prod.snd
                (Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ p.1 = v) AR₂)).sum))
        (fun p : Lax392996.Databases.Tuple (T⊕K) (n+1) ↦ (Lax392996Proofs.Foreign.Tuple.fromComposite p).1)
        (fun q : Lax392996.Databases.Tuple (T⊕K) (n+1) ↦ (Lax392996Proofs.Foreign.Tuple.fromComposite q).1)
        (fun (p q : Lax392996.Databases.Tuple (T⊕K) (n+1)) ↦
          fun (k : Fin (n+1)) ↦
            (if ↑k < n then (#((Fin.castLE (by omega : n+1 ≤ 2*n+2)) k) : Lax392996.RelationalAlgebra.Term (T⊕K) (2*n+2))
              else Lax392996.RelationalAlgebra.Term.sub (#(Fin.ofNat (2*n+2) n)) (#(Fin.last (2*n+1)))).eval
                (Lax392996Proofs.Foreign.Tuple.cast (by omega : (n+1)+(n+1) = 2*n+2) (Fin.append p q)))
        hS_nodup h_val_eq
      -- Chain via hsemi.trans.
      refine hsemi.trans ?_
      -- Now: (AR₁.toComposite.filter (·.fromComposite.1 ∈ S)).map mk_after = RHS
      -- where mk_after p = (proj_curry (p, val (fromComposite p).1)).
      -- Unfold AR₁.toComposite = AR₁.map ATC and push filter/map through.
      unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
      rw [Multiset.filter_map, Multiset.map_map]
      -- After filter_map: (AR₁.filter (cond ∘ ATC)).map ATC.map(mk_after)
      -- After map_map: (AR₁.filter (cond ∘ ATC)).map (mk_after ∘ ATC)
      -- The filter predicate (cond ∘ ATC) ap = (fromComposite (ATC ap)).1 ∈ dedup
      --                                      = ap.1 ∈ dedup
      have hfilter_eq :
          Multiset.filter
            ((fun p : Lax392996.Databases.Tuple (T⊕K) (n+1) ↦ (Lax392996Proofs.Foreign.Tuple.fromComposite p).1 ∈ (AR₂.map Prod.fst).dedup)
              ∘ Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite) AR₁
          = Multiset.filter (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦
              p.1 ∈ Multiset.map Prod.fst AR₂) AR₁ := by
        apply Multiset.filter_congr
        intro ap _
        rw [Function.comp_apply, Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite, Multiset.mem_dedup]
      rw [hfilter_eq]
      apply Multiset.map_congr rfl
      intro ap _
      -- Compute mk_after applied to ATC ap.
      simp only [Function.comp, Lax392996Proofs.Foreign.Tuple.fromComposite_toComposite]
      funext k
      by_cases hk : ↑k < n
      · -- Data case: result is Sum.inl (ap.1 k).
        simp only [hk, if_pos, Lax392996.RelationalAlgebra.Term.eval]
        rw [Lax392996Proofs.Foreign.proj_outer_2n2_cast_append_eq_fst]
        -- Goal: ATC ap k = ATC (ap.1, ap.2 - sum_β ap.1) k for k.val < n.
        -- Both reduce to Sum.inl (ap.1 ⟨k.val, hk⟩); the .2 component is unused.
        unfold Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
        have hkcast : k = (Fin.castAdd 1 (k.castLT hk) : Fin (n+1)) :=
          Fin.eq_of_val_eq rfl
        rw [hkcast, Fin.append_left, Fin.append_left]
      · -- Annotation case: result is Sum.inr (ap.2 - sum_β ap.1).
        have hk_eq : k = Fin.last n := by
          apply Fin.eq_of_val_eq
          rw [Fin.val_last]
          have h1 : k.val < n + 1 := k.isLt
          have h2 : ¬ k.val < n := hk
          omega
        subst hk_eq
        simp only [Fin.val_last, lt_self_iff_false, if_false, Lax392996.RelationalAlgebra.Term.eval]
        rw [Lax392996Proofs.Foreign.cast_append_2n2_at_ofNat_n, Lax392996Proofs.Foreign.cast_append_2n2_at_last]
        -- Show: ATC ap (Fin.last n) - ATC (ap.1, sum_β ap.1) (Fin.last n)
        --     = ATC (ap.1, ap.2 - sum_β ap.1) (Fin.last n)
        rw [Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_last, Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_last,
            Lax392996Proofs.Foreign.AnnotatedTuple.toComposite_last]
        rfl
    have rhs_eq :
      Lax392996.MultisetSemantics.Query.evaluate ((Lax392996.RelationalAlgebra.Query.Diff q₁ q₂).rewriting hq) d.toComposite
      = Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
        ((q₁.evaluateAnnotated hq'₁ d).map (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦
          (p.1, p.2 - (Multiset.map Prod.snd
            (Multiset.filter (fun q: Lax392996.AnnotatedDatabases.AnnotatedTuple T K _ ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d))).sum))) := by
      unfold Lax392996.RewritingRules.Query.rewriting Lax392996.MultisetSemantics.Query.evaluate
      simp only []
      rw[unmatched_eq, matched_eq]
      -- Split ar₁ via filter
      have hsplit :
          q₁.evaluateAnnotated hq'₁ d
          = Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦
              p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d)
            + Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦
              p.1 ∈ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d) := by
        rw[add_comm]
        exact (Multiset.filter_add_not _ _).symm
      -- Show unmatched.toComposite equals the map form (since β = 0 on unmatched, α - 0 = α)
      have h_unmatched_toComp :
          Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
            (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦
              p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d))
        = Multiset.map
            (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ Lax392996.AnnotatedDatabases.AnnotatedTuple.toComposite
              (p.1, p.2 - (Multiset.map Prod.snd
                (Multiset.filter (fun q: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ q.1 = p.1)
                  (q₂.evaluateAnnotated hq'₂ d))).sum))
            (Multiset.filter (fun p: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦
              p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d)) := by
        unfold Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite
        apply Multiset.map_congr rfl
        intro p hp
        have hunmatched : p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d) :=
          (Multiset.mem_filter.mp hp).2
        have hfilter_empty :
            Multiset.filter (fun q: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d) = 0 :=
          Multiset.filter_eq_nil.mpr (fun q hq hqeq =>
            hunmatched (Multiset.mem_map.mpr ⟨q, hq, hqeq⟩))
        -- Avoid direct `rw` on filter (DecidablePred instance divergence).
        -- Convert sum to 0 instead.
        have hsum_zero : (Multiset.map Prod.snd
            (Multiset.filter (fun q: Lax392996.AnnotatedDatabases.AnnotatedTuple T K n ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d))).sum = 0 := by
          convert Multiset.sum_zero
          convert Multiset.map_zero (Prod.snd : Lax392996.AnnotatedDatabases.AnnotatedTuple T K n → K)
        rw[hsum_zero]
        have hp2 : HSub.hSub p.2 (0: K) = p.2 := by
          apply le_antisymm
          · rw[Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]; simp
          · simpa using (Lax392996Proofs.Foreign.monus_smallest p.2 0).left
        rw[hp2]
        rfl
      rw[h_unmatched_toComp]
      conv_rhs => rw[Lax392996.AnnotatedDatabases.AnnotatedRelation.toComposite, Multiset.map_map, hsplit, Multiset.map_add]
      rfl
    exact lhs_eq.symm.trans rhs_eq.symm
  | ProvSum _ _ _ => simp[Lax392996.RelationalAlgebra.Query.source] at hq
  | Having _ _ _ _ _ _ _ => simp[Lax392996.RelationalAlgebra.Query.source] at hq

end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query

export Lax392996Proofs.Foreign.Query (rewriting_valid)

end Lax392996.RelationalAlgebra.Query

namespace Query
export Lax392996Proofs.Foreign.Query (rewriting_valid)
end Query


