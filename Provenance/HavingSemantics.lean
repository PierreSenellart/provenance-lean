/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Fin
import Provenance.HavingMinMax
import Provenance.QueryAdequacy
import Provenance.QueryAnnotatedDatabase

/-!
# Possible-world semantics of the fused `Having` operator

This file gives the `K`-annotated semantics of the fused `HAVING` operator
`Query.Having` – a grouping `γ^≼` whose output is filtered by a comparison
between an aggregate value and a regular term – in an arbitrary commutative
m-semiring, together with the *bridge* between its possible worlds and the
`Finset`-of-positions representation on which the algebraic development of
`Provenance.Having` and `Provenance.HavingMinMax` is built.

## Possible worlds

The occurrences of a group are extracted as a sequence `U` (a list of
annotated tuples, ordered by the canonical lexicographic order – the
ordering `≼` along which non-commutative aggregates read their input, with
an arbitrary fixed tie-break on the annotations). A *possible world* of `U`
is a subsequence `W ⊑ U`; its annotation is, in factored form,

`ann_U(W) = (⊗_{(u,α) ∈ W} α) ⊗ (𝟙 ⊖ ⊕_{(u,α) ∈ U∖W} α)`.

## The bridge

Formally, worlds are represented as **sets of positions**
`W : Finset (Fin U.length)`; `seqOf U W` is the subsequence of `U` they
select. This representation is faithful: `seqOf U W` is always a sublist of
`U` (`seqOf_sublist`), every sublist arises this way (`sublist_eq_seqOf`),
and when the occurrences of `U` are pairwise distinct the correspondence is
a bijection (`seqOf_injective`). Because annotations and aggregate values
factor through positions, the possible-world `⊕`-sum below is taken over
`Finset (Fin U.length)` – which is exactly the index representation used by
`Provenance.Having` – and the whole algebraic development attaches to the
semantics through `worldAnn_eq_T` and `havingProv_eq_prov` (and, for the
`≥` comparisons, which need no distributivity, through `worldAnn_eq_ann`).

## The semantics

For a group with occurrence sequence `U` and an atomic aggregate comparison
`f(t) op s`, the *predicate provenance* is

`⊕_{∅ ≠ W ⊑ U} ann_U(W) ⊗ χ_op(agg_{t,f}(W), s(g))`,

where `agg_{t,f}(W)` applies the sequence aggregate `f` to the `t`-values
of the occurrences of `W` (in order) and `χ_op` sends a true comparison to
`𝟙` and a false one to `𝟘`. The sum ranges over non-empty worlds only, so
it already enforces group existence. The general evaluator's `HAVING`
site (`AggQueryIn.havingSite`, in `Provenance.AggQueryBridges`) has exactly
this closed form: one row per group of the inner query, whose data part
carries the group key and the (whole-group) aggregate values, and whose
annotation is the predicate provenance of its group.
Boolean combinations of aggregate comparisons are interpreted by
`HavingPred.prov`: `∧ ↦ ⊗`, `∨ ↦ ⊕`, and `¬` is pushed to the atoms by
De Morgan duality, complementing the comparison operator of an atom (as
in ProvSQL's implementation).
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]

namespace Having

/-! ### Positions and subsequences: the bridge -/

section Bridge

variable {β : Type}

/-- The subsequence of `U` selected by a set of positions, in order. -/
def seqOf : (U : List β) → Finset (Fin U.length) → List β
  | [], _ => []
  | a :: U, W =>
      (if (0 : Fin (U.length + 1)) ∈ W then [a] else [])
        ++ seqOf U (Finset.univ.filter (fun i => i.succ ∈ W))

/-- A set of positions selects a sublist. -/
theorem seqOf_sublist : ∀ (U : List β) (W : Finset (Fin U.length)),
    (seqOf U W).Sublist U
  | [], _ => List.Sublist.refl []
  | a :: U, W => by
    rw [seqOf]
    split_ifs with h0
    · exact (seqOf_sublist U _).cons_cons a
    · exact (seqOf_sublist U _).cons a

/-- Every sublist is selected by some set of positions. -/
theorem sublist_eq_seqOf {U L : List β} (h : L.Sublist U) :
    ∃ W : Finset (Fin U.length), seqOf U W = L := by
  induction h with
  | slnil => exact ⟨∅, rfl⟩
  | @cons L U a _ ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨W.image Fin.succ, ?_⟩
    rw [seqOf, ite_eq_right (by
      intro h0
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h0
      exact (Fin.succ_ne_zero i) hi)]
    rw [show Finset.univ.filter (fun i => i.succ ∈ W.image Fin.succ) = W by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun ⟨j, hj, hij⟩ => (Fin.succ_injective _ hij) ▸ hj,
        fun hi => ⟨i, hi, rfl⟩⟩]
    rw [hW]
    rfl
  | @cons_cons L U a _ ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨insert 0 (W.image Fin.succ), ?_⟩
    rw [seqOf, ite_eq_left (Finset.mem_insert_self _ _)]
    rw [show Finset.univ.filter
          (fun i => i.succ ∈ insert 0 (W.image Fin.succ)) = W by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_image]
      constructor
      · rintro (h | ⟨j, hj, hij⟩)
        · exact absurd h (Fin.succ_ne_zero i)
        · exact (Fin.succ_injective _ hij) ▸ hj
      · exact fun hi => Or.inr ⟨i, hi, rfl⟩]
    rw [hW]
    rfl

/-- The length of the selected subsequence is the number of selected
positions: `Finset.card` is the `COUNT` aggregate of the bridge. -/
theorem seqOf_length : ∀ (U : List β) (W : Finset (Fin U.length)),
    (seqOf U W).length = W.card
  | [], W => by
    have hW : W = ∅ := by
      ext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    subst hW
    rfl
  | a :: U, W => by
    rw [seqOf, List.length_append, seqOf_length U _]
    have hsplit : W.card
        = (if (0 : Fin (U.length + 1)) ∈ W then 1 else 0)
          + (Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W)).card := by
      calc W.card = (Finset.univ.filter (fun i => i ∈ W)).card :=
            (congrArg Finset.card (Finset.filter_univ_mem W)).symm
        _ = ∑ i : Fin (U.length + 1), if i ∈ W then 1 else 0 :=
            Finset.card_filter _ _
        _ = (if (0 : Fin (U.length + 1)) ∈ W then 1 else 0)
              + ∑ i : Fin U.length, if i.succ ∈ W then 1 else 0 :=
            Fin.sum_univ_succ _
        _ = (if (0 : Fin (U.length + 1)) ∈ W then 1 else 0)
              + (Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W)).card := by
            rw [Finset.card_filter]
    rw [hsplit]
    split_ifs with h0
    · simp
    · simp

/-- Under occurrence-uniqueness (`U.Nodup`), the position representation is
faithful: distinct sets of positions select distinct subsequences. -/
theorem seqOf_injective : ∀ {U : List β}, U.Nodup →
    Function.Injective (seqOf U)
  | [], _ => fun W₁ W₂ _ => by
    have hempty : ∀ W : Finset (Fin ([] : List β).length), W = ∅ := by
      intro W
      ext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    rw [hempty W₁, hempty W₂]
  | a :: U, hnodup => by
    have haU : a ∉ U := (List.nodup_cons.mp hnodup).1
    have hU : U.Nodup := (List.nodup_cons.mp hnodup).2
    intro W₁ W₂ heq
    rw [seqOf, seqOf] at heq
    have hmem : ∀ {W : Finset (Fin (U.length + 1))},
        a ∉ seqOf U (Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W)) := by
      intro W ha
      exact haU ((seqOf_sublist U _).mem ha)
    have h0 : ((0 : Fin (U.length + 1)) ∈ W₁) ↔ ((0 : Fin (U.length + 1)) ∈ W₂) := by
      constructor
      · intro h₁
        by_contra h₂
        rw [ite_eq_left h₁, ite_eq_right h₂, List.nil_append] at heq
        have ha : a ∈ [a] ++ seqOf U
            (Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W₁)) := by simp
        rw [heq] at ha
        exact hmem ha
      · intro h₂
        by_contra h₁
        rw [ite_eq_right h₁, ite_eq_left h₂, List.nil_append] at heq
        have ha : a ∈ [a] ++ seqOf U
            (Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W₂)) := by simp
        rw [← heq] at ha
        exact hmem ha
    have htail : Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W₁)
        = Finset.univ.filter (fun i : Fin U.length => i.succ ∈ W₂) := by
      by_cases h₁ : (0 : Fin (U.length + 1)) ∈ W₁
      · have h₂ := h0.mp h₁
        rw [ite_eq_left h₁, ite_eq_left h₂] at heq
        exact seqOf_injective hU (List.append_cancel_left heq)
      · have h₂ := fun h => h₁ (h0.mpr h)
        rw [ite_eq_right h₁, ite_eq_right h₂, List.nil_append, List.nil_append] at heq
        exact seqOf_injective hU heq
    ext i
    refine Fin.cases ?_ ?_ i
    · exact h0
    · intro j
      have := Finset.ext_iff.mp htail j
      simpa using this

/-- Membership in the selected subsequence: the elements of `seqOf U W` are
exactly the entries of `U` at the positions in `W`. -/
theorem mem_seqOf : ∀ (U : List β) (W : Finset (Fin U.length)) (x : β),
    x ∈ seqOf U W ↔ ∃ i ∈ W, U.get i = x
  | [], _, _ => by
    simp only [seqOf, List.not_mem_nil, false_iff]
    rintro ⟨i, -, -⟩
    exact i.elim0
  | a :: U, W, x => by
    rw [seqOf, List.mem_append, mem_seqOf U]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · split_ifs at h with h0
        · exact ⟨0, h0, (List.mem_singleton.mp h).symm⟩
        · simp at h
      · exact ⟨i.succ, (Finset.mem_filter.mp hi).2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      revert hi
      refine Fin.cases ?_ ?_ i
      · intro h0
        exact Or.inl (by rw [ite_eq_left h0]; exact List.mem_singleton.mpr rfl)
      · intro j hj
        exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

end Bridge

/-! ### The world annotation, in factored form -/

/-- The `K`-annotation of a possible world, in the factored form of the
possible-world semantics: the product of the annotations of the kept
occurrences times `𝟙 ⊖` the sum of the annotations of the discarded ones.
`worldAnn_eq_T` normalizes it into the `Having.T` form used by the
algebraic development. -/
def worldAnn {N : ℕ} (α : Fin N → K) (W : Finset (Fin N)) : K :=
  (∏ i ∈ W, α i) * (1 - ∑ i ∈ Wᶜ, α i)

omit [DecidableEq K] in
/-- **The empty world is annotated `𝟙 ⊖ ⊕ᵢ αᵢ`**: nothing of the group is
present. -/
@[simp] theorem worldAnn_empty {N : ℕ} (α : Fin N → K) :
    worldAnn α ∅ = 1 - ∑ i, α i := by
  unfold worldAnn
  rw [Finset.prod_empty, one_mul, Finset.compl_empty]

omit [DecidableEq K] in
/-- In an m-semiring where `⊗` left-distributes over `⊖`, the factored
world annotation coincides with the exactly-`W` contribution `Having.T`
over the full universe of positions. This is the *only* place the
distributivity hypothesis enters the correspondence between the semantics
and the query-free algebra; cf. `ChainFive`, where the two forms differ. -/
theorem worldAnn_eq_T (h_distrib : mul_sub_left_distributive K)
    {N : ℕ} (α : Fin N → K) (W : Finset (Fin N)) :
    worldAnn α W = Having.T α Finset.univ W := by
  rw [Having.T_eq_mul_one_monus_sum α h_distrib, worldAnn, Having.A,
    Finset.compl_eq_univ_sdiff]

omit [DecidableEq K] in
/-- The factored world annotation is `Having.ann` over the full universe
of positions, unconditionally: this is the attachment the `≥` case uses,
where distributivity is not available (or not needed). -/
theorem worldAnn_eq_ann {N : ℕ} (α : Fin N → K) (W : Finset (Fin N)) :
    worldAnn α W = Having.ann α Finset.univ W := by
  rw [worldAnn, Having.ann, Having.A, Finset.compl_eq_univ_sdiff]

/-- The annotation a world gives the part of an occurrence family lying
in `S`: the product of the annotations it keeps there against the monus
of those it drops there. `worldAnn` is the case `S = univ`, and the
point of the relative form is that it composes. -/
def relAnn {N : ℕ} (α : Fin N → K) (S W : Finset (Fin N)) : K :=
  (∏ i ∈ W ∩ S, α i) * (1 - ∑ i ∈ S \ W, α i)

omit [DecidableEq K] in
theorem relAnn_univ {N : ℕ} (α : Fin N → K) (W : Finset (Fin N)) :
    relAnn α Finset.univ W = worldAnn α W := by
  rw [relAnn, worldAnn, Finset.inter_univ, ← Finset.compl_eq_univ_sdiff]

omit [DecidableEq K] in
/-- **The relative annotation splits along any subset**: the part inside
`T` and the part outside contribute independently, when the semiring is
complemented. Iterating it splits a family into as many parts as one
likes – the shared part of two overlapping families and their two
private parts, for one. -/
theorem relAnn_split (hc : complemented K) {N : ℕ} (α : Fin N → K)
    (S T W : Finset (Fin N)) :
    relAnn α S W = relAnn α (S ∩ T) W * relAnn α (S \ T) W := by
  have he₁ : W ∩ (S ∩ T) = (W ∩ S) ∩ T := by
    ext x; simp only [Finset.mem_inter]; tauto
  have he₂ : W ∩ (S \ T) = (W ∩ S) \ T := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
  have he₃ : (S ∩ T) \ W = (S \ W) ∩ T := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
  have he₄ : (S \ T) \ W = (S \ W) \ T := by
    ext x; simp only [Finset.mem_sdiff]; tauto
  have hprod : (∏ i ∈ W ∩ (S ∩ T), α i) * (∏ i ∈ W ∩ (S \ T), α i)
      = ∏ i ∈ W ∩ S, α i := by
    rw [he₁, he₂]
    exact Finset.prod_inter_mul_prod_sdiff (W ∩ S) T α
  have hsum : (∑ i ∈ (S ∩ T) \ W, α i) + (∑ i ∈ (S \ T) \ W, α i)
      = ∑ i ∈ S \ W, α i := by
    rw [he₃, he₄]
    exact Finset.sum_inter_add_sum_sdiff (S \ W) T α
  rw [relAnn, relAnn, relAnn, mul_mul_mul_comm, hprod, ← hc, hsum]

omit [DecidableEq K] in
/-- **The three parts of two overlapping families.** A world's
annotation over the union of two families is the annotation of the
shared part times those of the two private ones. With the families
disjoint the shared part is empty and this is the disjoint split; with
them equal the private parts are, and it says nothing – which is the
regime `AggValue.predProvOf_mul_predProvOf` governs instead. -/
theorem relAnn_split_union (hc : complemented K) {N : ℕ} (α : Fin N → K)
    (V₁ V₂ W : Finset (Fin N)) :
    relAnn α (V₁ ∪ V₂) W
      = relAnn α (V₁ ∩ V₂) W * relAnn α (V₁ \ V₂) W
        * relAnn α (V₂ \ V₁) W := by
  have h₁ : (V₁ ∪ V₂) ∩ V₁ = V₁ := by
    ext x; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  have h₂ : (V₁ ∪ V₂) \ V₁ = V₂ \ V₁ := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
  rw [relAnn_split hc α (V₁ ∪ V₂) V₁ W, h₁, h₂, relAnn_split hc α V₁ V₂ W]

omit [DecidableEq K] in
/-- **A world's annotation splits along a partition of its family** when
the semiring is complemented: the occurrences inside `S` and those
outside contribute independently. It is what lets a predicate whose
atoms read disjoint families be evaluated atom by atom rather than over
the union of the families, and `complemented` is exactly what it needs –
the product part splits in any semiring, the `𝟙 ⊖ ·` part only there. -/
theorem worldAnn_split (hc : complemented K) {N : ℕ} (α : Fin N → K)
    (S W : Finset (Fin N)) :
    worldAnn α W
      = ((∏ i ∈ W ∩ S, α i) * (1 - ∑ i ∈ S \ W, α i))
        * ((∏ i ∈ W ∩ Sᶜ, α i) * (1 - ∑ i ∈ Sᶜ \ W, α i)) := by
  have hprod : (∏ i ∈ W ∩ S, α i) * (∏ i ∈ W ∩ Sᶜ, α i) = ∏ i ∈ W, α i := by
    rw [← Finset.sdiff_eq_inter_compl]
    exact Finset.prod_inter_mul_prod_sdiff W S α
  have hsum : (∑ i ∈ S \ W, α i) + (∑ i ∈ Sᶜ \ W, α i) = ∑ i ∈ Wᶜ, α i := by
    rw [show S \ W = Wᶜ ∩ S by
        rw [Finset.sdiff_eq_inter_compl, Finset.inter_comm],
      show Sᶜ \ W = Wᶜ \ S by
        rw [Finset.sdiff_eq_inter_compl, Finset.sdiff_eq_inter_compl,
          Finset.inter_comm]]
    exact Finset.sum_inter_add_sum_sdiff Wᶜ S α
  rw [mul_mul_mul_comm, hprod, ← hc, hsum]
  rfl

omit [DecidableEq K] in
/-- A relative world annotation reads only the part of the world inside
the family. -/
theorem relAnn_inter {N : ℕ} (α : Fin N → K) (S W : Finset (Fin N)) :
    relAnn α S W = relAnn α S (W ∩ S) := by
  unfold relAnn
  rw [show W ∩ S ∩ S = W ∩ S by ext x; simp only [Finset.mem_inter]; tauto,
    show S \ (W ∩ S) = S \ W by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto]

omit [DecidableEq K] in
/-- **Summing over the worlds of a family is summing over the pairs of
worlds of its two halves.** -/
theorem sum_split {N : ℕ} (S : Finset (Fin N))
    (F : Finset (Fin N) → Finset (Fin N) → K) :
    ∑ W : Finset (Fin N), F (W ∩ S) (W ∩ Sᶜ)
      = ∑ A ∈ S.powerset, ∑ B ∈ Sᶜ.powerset, F A B := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun W => (W ∩ S, W ∩ Sᶜ)) (fun p => p.1 ∪ p.2)
    (fun W _ => ?_) (fun p hp => Finset.mem_univ _) (fun W _ => ?_)
    (fun p hp => ?_) (fun W _ => rfl)
  · refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;>
      exact Finset.mem_powerset.mpr Finset.inter_subset_right
  · ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    tauto
  · obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_powerset] at hA hB
    refine Prod.ext ?_ ?_ <;> ext x <;>
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
    · exact ⟨fun h => h.1.resolve_right
          (fun hc => absurd h.2 (Finset.mem_compl.mp (hB hc))),
        fun h => ⟨Or.inl h, hA h⟩⟩
    · exact ⟨fun h => h.1.resolve_left (fun hc => h.2 (hA hc)),
        fun h => ⟨Or.inr h, Finset.mem_compl.mp (hB h)⟩⟩

omit [DecidableEq K] in
/-- **Two atoms reading disjoint families may be read one at a time.**
The product of the two families' world-sums is the single sum over the
worlds of their union, when the semiring is complemented – which is
what makes `worldAnn` split and is the only thing this needs of `K`.

It is the disjoint half of the `∧` rule: over *one* family the product
is not that sum, and what it takes there is exclusivity with an
idempotent `⊗` (`AggValue.predProvOf_mul_predProvOf`). -/
theorem sum_mul_sum_of_split (hc : complemented K) {N : ℕ} (α : Fin N → K)
    (S : Finset (Fin N)) (χ₁ χ₂ : Finset (Fin N) → K) :
    (∑ A ∈ S.powerset, relAnn α S A * χ₁ A)
        * (∑ B ∈ Sᶜ.powerset, relAnn α Sᶜ B * χ₂ B)
      = ∑ W : Finset (Fin N),
          worldAnn α W * (χ₁ (W ∩ S) * χ₂ (W ∩ Sᶜ)) := by
  rw [Finset.sum_mul_sum, ← sum_split S
    (fun A B => relAnn α S A * χ₁ A * (relAnn α Sᶜ B * χ₂ B))]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  rw [worldAnn_split hc α S W, ← relAnn_inter, ← relAnn_inter, mul_mul_mul_comm]
  rfl

omit [DecidableEq K] in
/-- **Summing over the worlds of a union of two disjoint families is
summing over the pairs.** `sum_split` is the case where the two halves
are a subset and its complement. -/
theorem sum_split_of_union {N : ℕ} {A B : Finset (Fin N)}
    (hd : Disjoint A B) (F : Finset (Fin N) → Finset (Fin N) → K) :
    ∑ W ∈ (A ∪ B).powerset, F (W ∩ A) (W ∩ B)
      = ∑ X ∈ A.powerset, ∑ Y ∈ B.powerset, F X Y := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun W => (W ∩ A, W ∩ B)) (fun p => p.1 ∪ p.2)
    (fun W _ => ?_) (fun p hp => ?_) (fun W hW => ?_) (fun p hp => ?_)
    (fun W _ => rfl)
  · refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;>
      exact Finset.mem_powerset.mpr Finset.inter_subset_right
  · obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_powerset] at hA hB ⊢
    exact Finset.union_subset (hA.trans Finset.subset_union_left)
      (hB.trans Finset.subset_union_right)
  · have hW' := Finset.mem_powerset.mp hW
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases Finset.mem_union.mp (hW' h) with hx | hx
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
  · obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_powerset] at hA hB
    refine Prod.ext ?_ ?_ <;> ext x <;>
      simp only [Finset.mem_inter, Finset.mem_union]
    · constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd (hB h) (Finset.disjoint_left.mp hd hx)
      · exact fun h => ⟨Or.inl h, hA h⟩
    · constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd hx (Finset.disjoint_left.mp hd (hA h))
        · exact h
      · exact fun h => ⟨Or.inr h, hB h⟩

omit [DecidableEq K] in
/-- **Distinct worlds of a sub-family annihilate each other** in an
exclusive m-semiring: the relative counterpart of
`worldAnn_mul_eq_zero_of_ne`, which is its case `S = univ`. -/
theorem relAnn_mul_eq_zero_of_ne (hexcl : exclusive K) {N : ℕ}
    (α : Fin N → K) (S : Finset (Fin N)) {X X' : Finset (Fin N)}
    (hX : X ⊆ S) (hX' : X' ⊆ S) (h : X ≠ X') :
    relAnn α S X * relAnn α S X' = 0 := by
  have key : ∀ (V V' : Finset (Fin N)), V ⊆ S → V' ⊆ S → ∀ u : Fin N,
      u ∈ V → u ∉ V' → relAnn α S V * relAnn α S V' = 0 := by
    intro V V' hV hV' u huV huV'
    have hVS : V ∩ S = V := Finset.inter_eq_left.mpr hV
    have hV'S : V' ∩ S = V' := Finset.inter_eq_left.mpr hV'
    have hprod : ∏ i ∈ V ∩ S, α i = α u * ∏ i ∈ V.erase u, α i := by
      rw [hVS]
      exact (Finset.mul_prod_erase V α huV).symm
    have hsum : ∑ i ∈ S \ V', α i = α u + ∑ i ∈ (S \ V').erase u, α i :=
      (Finset.add_sum_erase (S \ V') α
        (Finset.mem_sdiff.mpr ⟨hV huV, huV'⟩)).symm
    have hzero : α u * (1 - (α u + ∑ i ∈ (S \ V').erase u, α i)) = 0 :=
      mul_one_monus_add_eq_zero hexcl _ _
    have hring : (α u * ∏ i ∈ V.erase u, α i) * (1 - ∑ i ∈ S \ V, α i) *
          ((∏ i ∈ V' ∩ S, α i) * (1 - (α u + ∑ i ∈ (S \ V').erase u, α i)))
        = ((∏ i ∈ V.erase u, α i) * (1 - ∑ i ∈ S \ V, α i) *
            ∏ i ∈ V' ∩ S, α i) *
          (α u * (1 - (α u + ∑ i ∈ (S \ V').erase u, α i))) := by
      simp [mul_comm, mul_assoc, mul_left_comm]
    rw [relAnn, relAnn, hprod, hsum, hring, hzero, mul_zero]
  rw [Ne, Finset.ext_iff, not_forall] at h
  obtain ⟨u, hu⟩ := h
  by_cases huX : u ∈ X
  · exact key X X' hX hX' u huX (by tauto)
  · rw [mul_comm]
    exact key X' X hX' hX u (by tauto) huX

omit [DecidableEq K] in
theorem inter_union_sdiff_self {N : ℕ} (V T : Finset (Fin N)) :
    ((V ∩ T) ∪ (V \ T) : Finset (Fin N)) = V := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [DecidableEq K] in
theorem disjoint_inter_sdiff {N : ℕ} (V T : Finset (Fin N)) :
    Disjoint (V ∩ T) (V \ T) :=
  Finset.disjoint_left.mpr (fun _x hx hx' =>
    (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2)

omit [DecidableEq K] in
/-- **A family's world-sum splits along any subset**: the worlds of `V`
are the pairs of a world of `V ∩ T` and a world of `V \ T`, and the
annotation splits with them when the semiring is complemented. -/
theorem sum_family_split (hc : complemented K) {N : ℕ} (α : Fin N → K)
    (V T : Finset (Fin N)) (χ : Finset (Fin N) → K) :
    ∑ A ∈ V.powerset, relAnn α V A * χ A
      = ∑ X ∈ (V ∩ T).powerset, ∑ Y ∈ (V \ T).powerset,
          relAnn α (V ∩ T) X * relAnn α (V \ T) Y * χ (X ∪ Y) := by
  rw [← sum_split_of_union (disjoint_inter_sdiff V T)
    (fun X Y => relAnn α (V ∩ T) X * relAnn α (V \ T) Y * χ (X ∪ Y)),
    inter_union_sdiff_self]
  refine Finset.sum_congr rfl (fun W hW => ?_)
  have hWV := Finset.mem_powerset.mp hW
  have hsplit : ((W ∩ (V ∩ T)) ∪ (W ∩ (V \ T)) : Finset (Fin N)) = W := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hx : x ∈ T
      · exact Or.inl ⟨h, hWV h, hx⟩
      · exact Or.inr ⟨h, hWV h, hx⟩
  rw [hsplit, relAnn_split hc α V T W, ← relAnn_inter, ← relAnn_inter]

omit [DecidableEq K] in
theorem overlap_sets {N : ℕ} (V₁ V₂ : Finset (Fin N)) :
    ((V₁ ∪ V₂) ∩ (V₁ ∩ V₂) : Finset (Fin N)) = V₁ ∩ V₂
    ∧ ((V₁ ∪ V₂) \ (V₁ ∩ V₂) : Finset (Fin N)) = (V₁ \ V₂) ∪ (V₂ \ V₁)
    ∧ (((V₁ \ V₂) ∪ (V₂ \ V₁)) ∩ (V₁ \ V₂) : Finset (Fin N)) = V₁ \ V₂
    ∧ (((V₁ \ V₂) ∪ (V₂ \ V₁)) \ (V₁ \ V₂) : Finset (Fin N)) = V₂ \ V₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x <;>
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] <;> tauto

omit [DecidableEq K] in
theorem overlap_tests {N : ℕ} (V₁ V₂ X Y₁ Y₂ : Finset (Fin N))
    (hX : X ⊆ V₁ ∩ V₂) (hY₁ : Y₁ ⊆ V₁ \ V₂) (hY₂ : Y₂ ⊆ V₂ \ V₁) :
    ((X ∪ (Y₁ ∪ Y₂)) ∩ V₁ : Finset (Fin N)) = X ∪ Y₁
    ∧ ((X ∪ (Y₁ ∪ Y₂)) ∩ V₂ : Finset (Fin N)) = X ∪ Y₂ := by
  have hX' := fun {x} (h : x ∈ X) => Finset.mem_inter.mp (hX h)
  have hY₁' := fun {x} (h : x ∈ Y₁) => Finset.mem_sdiff.mp (hY₁ h)
  have hY₂' := fun {x} (h : x ∈ Y₂) => Finset.mem_sdiff.mp (hY₂ h)
  constructor <;> ext x <;>
    simp only [Finset.mem_inter, Finset.mem_union] <;>
    constructor
  · rintro ⟨h | h | h, hv⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hv (hY₂' h).2
  · rintro (h | h)
    · exact ⟨Or.inl h, (hX' h).1⟩
    · exact ⟨Or.inr (Or.inl h), (hY₁' h).1⟩
  · rintro ⟨h | h | h, hv⟩
    · exact Or.inl h
    · exact absurd hv (hY₁' h).2
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨Or.inl h, (hX' h).2⟩
    · exact ⟨Or.inr (Or.inr h), (hY₂' h).1⟩

omit [DecidableEq K] in
/-- The three-part counterpart of `sum_split_of_union`. -/
theorem sum_split_of_union3 {N : ℕ} {A B C : Finset (Fin N)}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (F : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → K) :
    ∑ W ∈ ((A ∪ (B ∪ C) : Finset (Fin N))).powerset,
        F (W ∩ A) (W ∩ B) (W ∩ C)
      = ∑ X ∈ A.powerset, ∑ Y ∈ B.powerset, ∑ Z ∈ C.powerset, F X Y Z := by
  have hA : Disjoint A ((B ∪ C : Finset (Fin N))) :=
    Finset.disjoint_union_right.mpr ⟨hAB, hAC⟩
  have step2 : ∀ X : Finset (Fin N),
      ∑ Z' ∈ ((B ∪ C : Finset (Fin N))).powerset, F X (Z' ∩ B) (Z' ∩ C)
        = ∑ Y ∈ B.powerset, ∑ Z ∈ C.powerset, F X Y Z := by
    intro X
    rw [← sum_split_of_union hBC (fun Y Z => F X Y Z)]
  have step1 : ∑ W ∈ ((A ∪ (B ∪ C) : Finset (Fin N))).powerset,
        F (W ∩ A) (W ∩ B) (W ∩ C)
      = ∑ X ∈ A.powerset,
          ∑ Z' ∈ ((B ∪ C : Finset (Fin N))).powerset, F X (Z' ∩ B) (Z' ∩ C) := by
    rw [← sum_split_of_union hA (fun X Z' => F X (Z' ∩ B) (Z' ∩ C))]
    refine Finset.sum_congr rfl (fun W _ => ?_)
    have hB : (W ∩ (B ∪ C) ∩ B : Finset (Fin N)) = W ∩ B := by
      ext x; simp only [Finset.mem_inter, Finset.mem_union]; tauto
    have hC : (W ∩ (B ∪ C) ∩ C : Finset (Fin N)) = W ∩ C := by
      ext x; simp only [Finset.mem_inter, Finset.mem_union]; tauto
    rw [hB, hC]
  rw [step1]
  exact Finset.sum_congr rfl (fun X _ => step2 X)

omit [DecidableEq K] in
/-- **Two atoms reading families that overlap without being equal.**
The product of the two families' world-sums is the single sum over the
worlds of their union, under the hypotheses of *both* settled regimes,
each on the part it governs: `complemented` splits the two private
parts off, and exclusivity with an idempotent `⊗` collapses the shared
part, which each side reads. The disjoint case is the one where the
shared part is empty, the same-family case the one where the private
parts are. -/
theorem sum_mul_sum_of_overlap (hc : complemented K) (hexcl : exclusive K)
    (hidem : mulIdempotent K) {N : ℕ} (α : Fin N → K)
    (V₁ V₂ : Finset (Fin N)) (χ₁ χ₂ : Finset (Fin N) → K) :
    (∑ A ∈ V₁.powerset, relAnn α V₁ A * χ₁ A)
        * (∑ B ∈ V₂.powerset, relAnn α V₂ B * χ₂ B)
      = ∑ W ∈ ((V₁ ∪ V₂ : Finset (Fin N))).powerset,
          relAnn α (V₁ ∪ V₂) W * (χ₁ (W ∩ V₁) * χ₂ (W ∩ V₂)) := by
  set M : Finset (Fin N) := V₁ ∩ V₂ with hM
  set P₁ : Finset (Fin N) := V₁ \ V₂ with hP₁
  set P₂ : Finset (Fin N) := V₂ \ V₁ with hP₂
  have hdMP₁ : Disjoint M P₁ := Finset.disjoint_left.mpr (fun x hx hx' =>
    (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2)
  have hdMP₂ : Disjoint M P₂ := Finset.disjoint_left.mpr (fun x hx hx' =>
    (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).1)
  have hdP : Disjoint P₁ P₂ := Finset.disjoint_left.mpr (fun x hx hx' =>
    (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1)
  have hUnion : ((V₁ ∪ V₂ : Finset (Fin N))) = M ∪ (P₁ ∪ P₂) := by
    ext x
    simp only [hM, hP₁, hP₂, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hV₁ : ∀ W : Finset (Fin N),
      (W ∩ V₁ : Finset (Fin N)) = (W ∩ M) ∪ (W ∩ P₁) := by
    intro W; ext x
    simp only [hM, hP₁, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hV₂ : ∀ W : Finset (Fin N),
      (W ∩ V₂ : Finset (Fin N)) = (W ∩ M) ∪ (W ∩ P₂) := by
    intro W; ext x
    simp only [hM, hP₂, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hR : (∑ W ∈ ((V₁ ∪ V₂ : Finset (Fin N))).powerset,
        relAnn α (V₁ ∪ V₂) W * (χ₁ (W ∩ V₁) * χ₂ (W ∩ V₂)))
      = ∑ X ∈ M.powerset, ∑ Y₁ ∈ P₁.powerset, ∑ Y₂ ∈ P₂.powerset,
          relAnn α M X * relAnn α P₁ Y₁ * relAnn α P₂ Y₂ *
            (χ₁ (X ∪ Y₁) * χ₂ (X ∪ Y₂)) := by
    rw [← sum_split_of_union3 hdMP₁ hdMP₂ hdP
      (fun X Y₁ Y₂ => relAnn α M X * relAnn α P₁ Y₁ * relAnn α P₂ Y₂ *
        (χ₁ (X ∪ Y₁) * χ₂ (X ∪ Y₂))), ← hUnion]
    refine Finset.sum_congr rfl (fun W _ => ?_)
    rw [relAnn_split_union hc α V₁ V₂ W, ← hM, ← hP₁, ← hP₂,
      hV₁ W, hV₂ W, relAnn_inter α M W, relAnn_inter α P₁ W,
      relAnn_inter α P₂ W]
  have hL1 : (∑ A ∈ V₁.powerset, relAnn α V₁ A * χ₁ A)
      = ∑ X ∈ M.powerset, ∑ Y₁ ∈ P₁.powerset,
          relAnn α M X * relAnn α P₁ Y₁ * χ₁ (X ∪ Y₁) :=
    sum_family_split hc α V₁ V₂ χ₁
  have hL2 : (∑ B ∈ V₂.powerset, relAnn α V₂ B * χ₂ B)
      = ∑ X ∈ M.powerset, ∑ Y₂ ∈ P₂.powerset,
          relAnn α M X * relAnn α P₂ Y₂ * χ₂ (X ∪ Y₂) := by
    have h := sum_family_split hc α V₂ V₁ χ₂
    rwa [show (V₂ ∩ V₁ : Finset (Fin N)) = M from Finset.inter_comm V₂ V₁] at h
  rw [hL1, hL2, hR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun X hX => ?_)
  have hXM := Finset.mem_powerset.mp hX
  rw [Finset.sum_eq_single X]
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun Y₁ _ => Finset.sum_congr rfl (fun Y₂ _ => ?_))
    rw [show relAnn α M X * relAnn α P₁ Y₁ * χ₁ (X ∪ Y₁) *
          (relAnn α M X * relAnn α P₂ Y₂ * χ₂ (X ∪ Y₂))
        = (relAnn α M X * relAnn α M X) *
          (relAnn α P₁ Y₁ * relAnn α P₂ Y₂ *
            (χ₁ (X ∪ Y₁) * χ₂ (X ∪ Y₂))) by
      simp [mul_assoc, mul_left_comm], hidem]
    simp [mul_assoc]
  · intro X' hX' hne
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero (fun Y₁ _ => Finset.sum_eq_zero (fun Y₂ _ => ?_))
    rw [show relAnn α M X * relAnn α P₁ Y₁ * χ₁ (X ∪ Y₁) *
          (relAnn α M X' * relAnn α P₂ Y₂ * χ₂ (X' ∪ Y₂))
        = (relAnn α M X * relAnn α M X') *
          (relAnn α P₁ Y₁ * relAnn α P₂ Y₂ *
            (χ₁ (X ∪ Y₁) * χ₂ (X' ∪ Y₂))) by
      simp [mul_assoc, mul_left_comm],
      relAnn_mul_eq_zero_of_ne hexcl α M hXM (Finset.mem_powerset.mp hX')
        (Ne.symm hne), zero_mul]
  · intro h
    exact absurd hX h

omit [DecidableEq K] in
/-- **Distinct worlds of one occurrence family annihilate each other**, in an
exclusive m-semiring. A position kept by one world and dropped by the other
contributes a factor `α u` to the first annotation and a factor
`𝟙 ⊖ (α u ⊕ …)` to the second, and exclusivity makes that pair `𝟘`.

This is what makes the alternatives of an occurrence mutually exclusive when
an aggregate value is read as a key, and the same identity governs the
worlds of a frame that contains its current row. It fails in `How`
(`How.not_exclusive`), which is the universal semiring every provenance
circuit is built in, so the spurious terms are carried by the circuit and
die only on evaluation into an exclusive semiring, homomorphisms commuting
with `⊖`. -/
theorem worldAnn_mul_eq_zero_of_ne (hexcl : exclusive K) {N : ℕ}
    (α : Fin N → K) {W W' : Finset (Fin N)} (h : W ≠ W') :
    worldAnn α W * worldAnn α W' = 0 := by
  -- One direction of the asymmetry; the statement follows by commutativity.
  have key : ∀ (V V' : Finset (Fin N)) (u : Fin N), u ∈ V → u ∉ V' →
      worldAnn α V * worldAnn α V' = 0 := by
    intro V V' u huV huV'
    have hprod : ∏ i ∈ V, α i = α u * ∏ i ∈ V.erase u, α i :=
      (Finset.mul_prod_erase V α huV).symm
    have hsum : ∑ i ∈ V'ᶜ, α i = α u + ∑ i ∈ (V'ᶜ).erase u, α i :=
      (Finset.add_sum_erase (V'ᶜ) α (Finset.mem_compl.mpr huV')).symm
    have hzero : α u * (1 - (α u + ∑ i ∈ (V'ᶜ).erase u, α i)) = 0 :=
      mul_one_monus_add_eq_zero hexcl _ _
    -- Collect the two offending factors next to each other, then kill them.
    have hring : (α u * ∏ i ∈ V.erase u, α i) * (1 - ∑ i ∈ Vᶜ, α i) *
          ((∏ i ∈ V', α i) * (1 - (α u + ∑ i ∈ (V'ᶜ).erase u, α i)))
        = ((∏ i ∈ V.erase u, α i) * (1 - ∑ i ∈ Vᶜ, α i) * ∏ i ∈ V', α i) *
          (α u * (1 - (α u + ∑ i ∈ (V'ᶜ).erase u, α i))) := by
      simp [mul_comm, mul_assoc, mul_left_comm]
    rw [worldAnn, worldAnn, hprod, hsum, hring, hzero, mul_zero]
  rw [Ne, Finset.ext_iff, not_forall] at h
  obtain ⟨u, hu⟩ := h
  by_cases huW : u ∈ W
  · exact key W W' u huW (by tauto)
  · rw [mul_comm]
    exact key W' W u (by tauto) huW

/-! ### Group extraction and aggregate values -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- Folding `sortedInsert` over a multiset sorts it without changing its
elements: the underlying multiset of the resulting list is the original
multiset. (`Multiset.sort` would serve the same purpose but is defined by
well-founded recursion and does not reduce in the kernel.) -/
theorem foldr_sortedInsert_coe {α' : Type} [LinearOrder α'] (s : Multiset α') :
    (↑((s.foldr sortedInsert ⟨[], by simp⟩).val) : Multiset α') = s := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.foldr_cons]
    calc (↑((sortedInsert a (s.foldr sortedInsert ⟨[], by simp⟩)).val) : Multiset α')
        = ↑(a :: (s.foldr sortedInsert ⟨[], by simp⟩).val) :=
          Multiset.coe_eq_coe.mpr (List.perm_orderedInsert _ a _)
      _ = a ::ₘ ↑((s.foldr sortedInsert ⟨[], by simp⟩).val) := rfl
      _ = a ::ₘ s := by rw [ih]

/-- The occurrence sequence `U^≼` of the group of key `g`: the annotated
tuples of `r` whose grouping columns match `g`, as a list sorted by the
lexicographic order on annotated tuples – by the canonical order on the
value part first (the ordering `≼` along which the group sequence is
read), then by the alternative order of `HasAltLinearOrder` on the
annotation, an arbitrary fixed tie-break, matching the possible-world
semantics where occurrences with equal value parts are ordered
arbitrarily. -/
def havingGroup [HasAltLinearOrder K] (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    List (AnnotatedTuple T K m) :=
  letI : LinearOrder K := HasAltLinearOrder.altOrder
  letI ord : LinearOrder (AnnotatedTuple T K m) :=
    inferInstanceAs (LinearOrder (Tuple T m ×ₗ K))
  -- Insertion sort via `sortedInsert` rather than `Multiset.sort`: the
  -- latter is defined by well-founded recursion (merge sort) and does not
  -- reduce in the kernel, which would prevent `decide`-checked instances.
  ((Multiset.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k') r).foldr
    sortedInsert ⟨[], by simp⟩).val

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The group sequence is a permutation of the group multiset: as a
multiset, `havingGroup is r g` is the sub-multiset of `r` matching the
key `g`. -/
theorem havingGroup_coe [HasAltLinearOrder K] (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    (↑(havingGroup is r g) : Multiset (AnnotatedTuple T K m))
      = Multiset.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k') r := by
  let : LinearOrder K := HasAltLinearOrder.altOrder
  let : LinearOrder (AnnotatedTuple T K m) :=
    inferInstanceAs (LinearOrder (Tuple T m ×ₗ K))
  exact foldr_sortedInsert_coe _

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The group sequence is sorted: on consecutive occurrences, the tuple
part is strictly increasing or equal (ties on the tuple part being broken
by the alternative order on the annotations). -/
theorem havingGroup_pairwise [HasAltLinearOrder K] (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    (havingGroup is r g).Pairwise
      (fun p q => (p.fst < q.fst) ∨ p.fst = q.fst) := by
  let : LinearOrder K := HasAltLinearOrder.altOrder
  let ord : LinearOrder (AnnotatedTuple T K m) :=
    inferInstanceAs (LinearOrder (Tuple T m ×ₗ K))
  refine List.Pairwise.imp ?_
    (((Multiset.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k') r).foldr
      sortedInsert ⟨[], by simp⟩).property)
  intro a b hab
  rcases Prod.Lex.le_iff.mp hab with h | ⟨heq, -⟩
  · exact Or.inl h
  · exact Or.inr heq

/-- The aggregate value of `f` over the term `t` in the world `W`: `f`
applied to the sequence of `t`-values of the kept occurrences, in order.
No algebraic structure on `f` is required. -/
def aggValOn (U : List (AnnotatedTuple T K m)) (t : Term T m)
    (f : SeqAggFunc T) (W : Finset (Fin U.length)) : T :=
  f ((seqOf U W).map (fun p => t.eval p.fst))

/-! ### Predicate provenance -/

/-- `χ_op`: the characteristic value of a comparison, `𝟙` if it holds and
`𝟘` otherwise – and `𝟘` also when it is *unknown*, a comparison with a
`NULL` operand being neither true nor false. A row on which a comparison is
unknown is selected by neither the comparison nor its negation, and
contributes nothing to either provenance. -/
def chi (op : CompOp) (a b : T) : K :=
  if op.eval3 a b = Kleene.true then 1 else 0

/-- `χ_P`: the characteristic value of an arbitrary three-valued test on
a value, `𝟙` where the test is true and `𝟘` where it is false or
unknown. `chi` is the case of a comparison against a constant, and the
general form is what an atom carrying a test – a range, for one – reads
its token through. -/
def chiOf (P : T → Kleene) (a : T) : K :=
  if P a = Kleene.true then 1 else 0

omit [DecidableEq K] in
theorem chi_eq_chiOf (op : CompOp) (a b : T) :
    (chi op a b : K) = chiOf (fun v => op.eval3 v b) a := rfl

omit [ValueType T] [DecidableEq K] in
/-- **Two tests conjoin by `⊗`**, the characteristic values being
`{𝟘, 𝟙}`-valued. -/
theorem chiOf_mul_chiOf (P Q : T → Kleene) (a : T) :
    (chiOf P a : K) * chiOf Q a = chiOf (fun v => (P v).and (Q v)) a := by
  unfold chiOf
  cases hP : P a <;> cases hQ : Q a <;> simp [Kleene.and, hP, hQ]

omit [DecidableEq K] in
/-- **Away from the null the indicator is the two-valued one.** The
statements proved before the null was introduced are this case, and over a
domain where nothing is null it is the definition. -/
theorem chi_eq_ite (op : CompOp) {a b : T}
    (ha : ValueType.isNull a = false) (hb : ValueType.isNull b = false) :
    (chi op a b : K) = if op.eval a b then 1 else 0 := by
  unfold chi
  by_cases h : op.eval a b
  · rw [ite_eq_left ((CompOp.eval3_eq_true_iff op ha hb).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((CompOp.eval3_eq_true_iff op ha hb).mp hc)),
      ite_eq_right h]

omit [DecidableEq K] in
@[simp] theorem chi_eq_ite_of_noNulls [NoNulls T] (op : CompOp) (a b : T) :
    (chi op a b : K) = if op.eval a b then 1 else 0 :=
  chi_eq_ite op (isNull_eq_false a) (isNull_eq_false b)

omit [DecidableEq K] in
/-- A null-strict comparison with a `NULL` operand contributes nothing. -/
@[simp] theorem chi_of_isNull_left {op : CompOp} (hs : op.strict = true)
    {a : T} (h : ValueType.isNull a = true) (b : T) : (chi op a b : K) = 0 := by
  simp [chi, CompOp.eval3_of_isNull_left hs h]

omit [DecidableEq K] in
@[simp] theorem chi_of_isNull_right {op : CompOp} (hs : op.strict = true)
    (a : T) {b : T} (h : ValueType.isNull b = true) : (chi op a b : K) = 0 := by
  simp [chi, CompOp.eval3_of_isNull_right hs a h]

/-- **Predicate provenance of an atomic aggregate comparison** on the
occurrence sequence `U` of one group: the `⊕`-sum, over the non-empty
possible worlds of `U`, of the world annotation times the characteristic
value of the comparison between the aggregate value in the world and the
regular value `c`. The sum ranges over non-empty worlds only: it thereby
already enforces group existence, which is why the fused selection
semantics drops the annotation of the grouped row itself. -/
def havingProv (U : List (AnnotatedTuple T K m)) (t : Term T m)
    (f : SeqAggFunc T) (op : CompOp) (c : T) : K :=
  ∑ W ∈ Finset.univ.filter (fun W : Finset (Fin U.length) => W.Nonempty),
    worldAnn (fun i => (U.get i).snd) W * chi op (aggValOn U t f W) c

omit [DecidableEq K] in
/-- **Attachment of the algebra to the semantics.** In an m-semiring where
`⊗` left-distributes over `⊖`, the predicate provenance is exactly the
possible-world provenance `Having.prov` of the predicate
“`f(t) op c` holds in the world”, over the universe of positions of `U`
annotated by the occurrence annotations. All the collapse results of
`Provenance.Having` and `Provenance.HavingMinMax` (`F_eq_S`,
`G_eq_S_monus_S`, `collapse_to_minimal`, `minScan_correct` …) thereby
apply to the fused operator's semantics. -/
theorem havingProv_eq_prov3 (h_distrib : mul_sub_left_distributive K)
    (U : List (AnnotatedTuple T K m)) (t : Term T m) (f : SeqAggFunc T)
    (op : CompOp) (c : T) :
    havingProv U t f op c
      = prov (fun i => (U.get i).snd) Finset.univ
          (fun W => op.eval3 (aggValOn U t f W) c = Kleene.true) := by
  unfold havingProv prov
  rw [Finset.powerset_univ, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hne : W.Nonempty
  · by_cases hP : op.eval3 (aggValOn U t f W) c = Kleene.true
    · simp only [hne, hP, ite_true, true_and, chi, mul_one,
        worldAnn_eq_T h_distrib]
    · simp only [hne, hP, ite_true, ite_false, true_and, chi, mul_zero]
  · simp only [hne, ite_false, false_and]

omit [DecidableEq K] in
/-- The same over a domain where nothing is null, where the comparison is
two-valued. This is the form the `COUNT` algebra over `ℕ` uses. -/
theorem havingProv_eq_prov [NoNulls T] (h_distrib : mul_sub_left_distributive K)
    (U : List (AnnotatedTuple T K m)) (t : Term T m) (f : SeqAggFunc T)
    (op : CompOp) (c : T) :
    havingProv U t f op c
      = prov (fun i => (U.get i).snd) Finset.univ
          (fun W => op.eval (aggValOn U t f W) c) := by
  rw [havingProv_eq_prov3 h_distrib]
  exact prov_congr _ _ (fun W _ =>
    CompOp.eval3_eq_true_iff op (isNull_eq_false _) (isNull_eq_false _))

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The `COUNT(*)` specialization: on the world `W`, the sequence aggregate
`List.length` computes `|W|`, so a `COUNT` comparison depends on the world
only through its cardinality. Together with `havingProv_eq_prov` this
attaches the `Having.F`/`Having.G` algebra to the fused semantics. -/
theorem aggValOn_count
    (U : List (AnnotatedTuple ℕ K m)) (t : Term ℕ m)
    (W : Finset (Fin U.length)) :
    aggValOn U t SeqAggFunc.count W = W.card := by
  unfold aggValOn SeqAggFunc.count
  rw [List.length_map, seqOf_length]

omit [DecidableEq K] in
/-- **`COUNT(*) ≥ C` case of the fused semantics.** In an absorptive
m-semiring, the predicate provenance of `COUNT(*) ≥ C + 1` on the group
sequence `U` is the join-side `Having.S`, the `⊕`-sum of the monomials of
the worlds of size exactly `C + 1`. Unlike the `=` and `≤` cases, no
distributivity of `⊗` over `⊖` is needed: the factored world annotations
are summed directly through `Having.Fann_eq_S`, whose proof never rewrites
them into the `Having.T` form. -/
theorem havingProv_count_ge (h_abs : absorptive K)
    (U : List (AnnotatedTuple ℕ K m)) (t : Term ℕ m) (C : ℕ) :
    havingProv U t SeqAggFunc.count CompOp.ge (C + 1)
      = S (fun i => (U.get i).snd) Finset.univ (C + 1) := by
  rw [← Fann_eq_S h_abs]
  unfold havingProv Fann
  rw [Finset.powerset_univ, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [chi_eq_ite_of_noNulls, CompOp.eval, aggValOn_count, ge_iff_le,
    worldAnn_eq_ann]
  by_cases hC : C + 1 ≤ W.card
  · have hne : W.Nonempty := Finset.card_pos.mp (by omega)
    simp [hC, hne]
  · have hne : ¬ (W.Nonempty ∧ C + 1 ≤ W.card) := fun h => hC h.2
    by_cases hW : W.Nonempty <;> simp [hC, hW]

omit [DecidableEq K] in
/-- **`COUNT(*) = C` case of the fused semantics.** The predicate
provenance of `COUNT(*) = C + 1` is `Having.G` – hence, by
`Having.G_eq_S_monus_S`, the join-side difference
`S_{C+1} ⊖ S_{C+2}`. -/
theorem havingProv_count_eq (h_distrib : mul_sub_left_distributive K)
    (U : List (AnnotatedTuple ℕ K m)) (t : Term ℕ m) (C : ℕ) :
    havingProv U t SeqAggFunc.count CompOp.eq (C + 1)
      = G (fun i => (U.get i).snd) Finset.univ (C + 1) := by
  rw [havingProv_eq_prov h_distrib]
  unfold prov G
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext W
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
    CompOp.eval, aggValOn_count]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, Finset.card_pos.mp (by omega), h.2⟩

omit [DecidableEq K] in
/-- **`COUNT(*) ≤ C` case of the fused semantics.** The predicate
provenance of `COUNT(*) ≤ C` is the `⊕`-sum of world annotations over the
worlds of size between `1` and `C` – hence, by
`Having.atMost_eq_S_monus_S`, the join-side difference `S_1 ⊖ S_{C+1}`. -/
theorem havingProv_count_le (h_distrib : mul_sub_left_distributive K)
    (U : List (AnnotatedTuple ℕ K m)) (t : Term ℕ m) (C : ℕ) :
    havingProv U t SeqAggFunc.count CompOp.le C
      = ∑ W ∈ Finset.univ.powerset.filter
          (fun W : Finset (Fin U.length) => 1 ≤ W.card ∧ W.card ≤ C),
          Having.T (fun i => (U.get i).snd) Finset.univ W := by
  rw [havingProv_eq_prov h_distrib]
  unfold prov
  refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) fun _ _ => rfl
  simp only [CompOp.eval, aggValOn_count]
  constructor
  · exact fun h => ⟨Finset.card_pos.mpr h.1, h.2⟩
  · exact fun h => ⟨Finset.card_pos.mp (by omega), h.2⟩

omit [DecidableEq K] in
/-- `COUNT(*) > c` is `COUNT(*) ≥ c + 1`. -/
theorem havingProv_count_gt (U : List (AnnotatedTuple ℕ K m)) (t : Term ℕ m)
    (c : ℕ) :
    havingProv U t SeqAggFunc.count CompOp.gt c
      = havingProv U t SeqAggFunc.count CompOp.ge (c + 1) := rfl

omit [DecidableEq K] in
/-- `COUNT(*) < c + 1` is `COUNT(*) ≤ c`. -/
theorem havingProv_count_lt (U : List (AnnotatedTuple ℕ K m)) (t : Term ℕ m)
    (c : ℕ) :
    havingProv U t SeqAggFunc.count CompOp.lt (c + 1)
      = havingProv U t SeqAggFunc.count CompOp.le c := by
  unfold havingProv
  refine Finset.sum_congr rfl fun W _ => ?_
  congr 1
  rw [chi_eq_ite_of_noNulls, chi_eq_ite_of_noNulls]
  exact if_congr (by rw [aggValOn_count]; exact Nat.lt_succ_iff) rfl rfl

omit [DecidableEq K] in
/-- **The `≠` comparison splits.** For any aggregate and any m-semiring,
the predicate provenance of `f(t) ≠ c` is the `⊕`-sum of those of
`f(t) < c` and `f(t) > c`: the characteristic values agree world by
world, by trichotomy of the linear order on the value domain. -/
theorem havingProv_ne_split (U : List (AnnotatedTuple T K m)) (t : Term T m)
    (f : SeqAggFunc T) (c : T) :
    havingProv U t f CompOp.ne c
      = havingProv U t f CompOp.lt c + havingProv U t f CompOp.gt c := by
  unfold havingProv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [← mul_add]
  congr 1
  -- with a null operand all three comparisons are unknown and contribute
  -- nothing; otherwise the characteristic values agree by trichotomy
  by_cases hna : ValueType.isNull (aggValOn U t f W) = true
  · rw [chi_of_isNull_left (op := CompOp.ne) rfl hna,
      chi_of_isNull_left (op := CompOp.lt) rfl hna,
      chi_of_isNull_left (op := CompOp.gt) rfl hna, add_zero]
  by_cases hnc : ValueType.isNull c = true
  · rw [chi_of_isNull_right (op := CompOp.ne) rfl _ hnc,
      chi_of_isNull_right (op := CompOp.lt) rfl _ hnc,
      chi_of_isNull_right (op := CompOp.gt) rfl _ hnc, add_zero]
  rw [chi_eq_ite _ (by simpa using hna) (by simpa using hnc),
    chi_eq_ite _ (by simpa using hna) (by simpa using hnc),
    chi_eq_ite _ (by simpa using hna) (by simpa using hnc)]
  rcases lt_trichotomy (aggValOn U t f W) c with h | h | h
  · rw [ite_eq_left (show CompOp.ne.eval _ c from ne_of_lt h),
      ite_eq_left (show CompOp.lt.eval _ c from h),
      ite_eq_right (show ¬ CompOp.gt.eval _ c from not_lt.mpr h.le), add_zero]
  · rw [ite_eq_right (show ¬ CompOp.ne.eval _ c from not_not_intro h),
      ite_eq_right (show ¬ CompOp.lt.eval _ c from not_lt.mpr h.ge),
      ite_eq_right (show ¬ CompOp.gt.eval _ c from not_lt.mpr h.le), add_zero]
  · rw [ite_eq_left (show CompOp.ne.eval _ c from ne_of_gt h),
      ite_eq_right (show ¬ CompOp.lt.eval _ c from not_lt.mpr h.le),
      ite_eq_left (show CompOp.gt.eval _ c from h), zero_add]

omit [DecidableEq K] in
/-- **`COUNT(*) ≥ 1` collapses to the group annotation sum.** In an
absorptive m-semiring, the fused `COUNT(*) ≥ 1` predicate provenance of a
group sequence is the `⊕`-sum of the annotations of its occurrences (the
`C = 1` instance of the join correspondence: `S_1` is the sum of the
singleton monomials). -/
theorem havingProv_count_ge_one (h_abs : absorptive K)
    (U : List (AnnotatedTuple ℕ K m)) (t : Term ℕ m) :
    havingProv U t SeqAggFunc.count CompOp.ge 1
      = (U.map (fun p => p.snd)).sum := by
  have h := havingProv_count_ge h_abs U t 0
  refine h.trans ?_
  show S (fun i => (U.get i).snd) Finset.univ 1 = (U.map (fun p => p.snd)).sum
  unfold S
  rw [Finset.powersetCard_one, Finset.sum_map]
  have hsum : (U.map (fun p => p.snd)).sum = ∑ i : Fin U.length, (U.get i).snd := by
    conv_lhs => rw [← List.ofFn_get U]
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [A]

/-! ### Existential aggregate comparisons: `MIN` and `MAX`

A comparison `f(t) op c` is *existential* when, on a non-empty sequence,
it holds iff some element of the sequence satisfies `x op c`: this is the
case of `MIN(t) ≤ c`, `MIN(t) < c`, `MAX(t) ≥ c` and `MAX(t) > c`. The
valid worlds of such a comparison are those meeting the set of qualifying
occurrences, and `Having.sum_ann_meet` collapses the predicate provenance
to the `⊕`-sum of the qualifying occurrences' annotations, in every
absorptive m-semiring and without distributivity of `⊗` over `⊖`. -/

/-- Summing `f` over the entries of a list satisfying `P`, as a sum over
positions. -/
theorem sum_map_filter_coe {β γ : Type} [AddCommMonoid γ] (P : β → Prop)
    [DecidablePred P] (f : β → γ) :
    ∀ U : List β, ((Multiset.filter P (↑U : Multiset β)).map f).sum
      = ∑ i : Fin U.length, if P (U.get i) then f (U.get i) else 0
  | [] => by simp
  | a :: U => by
    have ih := sum_map_filter_coe P f U
    rw [Multiset.filter_coe, Multiset.map_coe, Multiset.sum_coe] at ih ⊢
    -- `(a :: U).length` is `U.length + 1` only definitionally, so split the
    -- sum through an explicitly typed instance of `Fin.sum_univ_succ`.
    have hsplit : (∑ i : Fin (a :: U).length,
          if P ((a :: U).get i) then f ((a :: U).get i) else 0)
        = (if P a then f a else 0)
          + ∑ i : Fin U.length, if P (U.get i) then f (U.get i) else 0 :=
      Fin.sum_univ_succ _
    rw [hsplit, ← ih, List.filter_cons]
    by_cases hP : P a
    · simp [hP]
    · simp [hP]

/-- A sequence aggregate `f` is *existential* for the comparison `op` when,
on non-empty sequences, `f L op c` holds iff some element `x` of `L`
satisfies `x op c`. -/
def Existential (f : SeqAggFunc T) (op : CompOp) : Prop :=
  ∀ (L : List T) (c : T), L ≠ [] → (op.eval (f L) c ↔ ∃ x ∈ L, op.eval x c)

/-- **An aggregate comparison is existential in a predicate on values**:
on a non-empty sequence, `f L op c` is *true* exactly when some element of
`L` satisfies `P`. -/
def ExistentialOn (f : SeqAggFunc T) (op : CompOp) (c : T) (P : T → Prop) :
    Prop :=
  ∀ L : List T, L ≠ [] → (op.eval3 (f L) c = Kleene.true ↔ ∃ x ∈ L, P x)

/-- **An aggregate comparison is existential, read three-valuedly**: on a
non-empty sequence, `f L op c` is *true* exactly when some element `x` of
`L` makes `x op c` true. This is the reading SQL's aggregates need: the
aggregate skips the nulls while the comparison is unknown on them, and both
readings agree on this – an occurrence whose value is null neither reaches
the aggregate nor satisfies the comparison. -/
def Existential3 (f : SeqAggFunc T) (op : CompOp) : Prop :=
  ∀ (L : List T) (c : T), L ≠ [] →
    (op.eval3 (f L) c = Kleene.true ↔ ∃ x ∈ L, op.eval3 x c = Kleene.true)

/-- Where nothing is null the two readings agree. -/
theorem Existential.to3 [NoNulls T] {f : SeqAggFunc T} {op : CompOp}
    (hf : Existential f op) : Existential3 f op := by
  intro L c hL
  rw [CompOp.eval3_eq_true_iff_noNulls]
  refine Iff.trans (hf L c hL) (exists_congr (fun x => ?_))
  exact and_congr Iff.rfl (CompOp.eval3_eq_true_iff_noNulls op x c).symm

/-- **A counting aggregate compared to zero is existential in
non-nullness**: `COUNT(t) ≠ 0` holds exactly when some occurrence has a
non-null `t`-value. This is not a comparison of that value against `0` – a
non-null value may well be zero – which is why the collapse of an
existential `HAVING` has to be stated against a predicate on values. -/
theorem existentialOn_counting {cnt : SeqAggFunc T}
    (hc : SeqAggFunc.Counts cnt) :
    ExistentialOn cnt CompOp.ne 0
      (fun x => ValueType.isNull x = false) := by
  intro L _
  rw [CompOp.eval3_eq_true_iff CompOp.ne (hc.not_null L) ValueType.isNull_zero]
  show ¬ (cnt L = 0) ↔ _
  rw [hc.eq_zero]
  constructor
  · intro h
    by_contra hc'
    exact h (fun x hx => by
      by_contra hn
      exact hc' ⟨x, hx, by simpa using hn⟩)
  · rintro ⟨x, hx, hxn⟩ hall
    rw [hall x hx] at hxn
    exact Bool.noConfusion hxn

omit [DecidableEq K] in
/-- **An existential comparison collapses to the qualifying occurrences.**
In an absorptive m-semiring, the predicate provenance of `f(t) op c` on the
group sequence `U`, when the comparison holds exactly of the sequences with
a `P`-value, is the `⊕`-sum of the annotations of the occurrences whose
`t`-value satisfies `P`. No distributivity of `⊗` over `⊖` is needed
(`Having.sum_ann_meet`).

The witness is a predicate on values rather than the comparison itself,
because the two need not coincide: SQL's `COUNT(t) ≠ 0` holds exactly when
some occurrence has a *non-null* `t`-value, which is not a comparison of
that value against `0`. -/
theorem havingProv_existentialOn (h_abs : absorptive K)
    {f : SeqAggFunc T} {op : CompOp} {c : T} {P : T → Prop} [DecidablePred P]
    (hf : ExistentialOn f op c P) (U : List (AnnotatedTuple T K m))
    (t : Term T m) :
    havingProv U t f op c
      = ((Multiset.filter (fun p : AnnotatedTuple T K m => P (t.eval p.fst))
          (↑U : Multiset (AnnotatedTuple T K m))).map Prod.snd).sum := by
  set H : Finset (Fin U.length) :=
    Finset.univ.filter (fun i => P (t.eval (U.get i).fst))
    with hH
  -- the comparison holds in a non-empty world iff the world meets `H`
  have hiff : ∀ W : Finset (Fin U.length), W.Nonempty →
      (op.eval3 (aggValOn U t f W) c = Kleene.true ↔ (W ∩ H).Nonempty) := by
    intro W hW
    have hne : ((seqOf U W).map (fun p => t.eval p.fst)) ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_map, seqOf_length]
      exact Finset.card_pos.mpr hW
    unfold aggValOn
    rw [hf _ hne]
    constructor
    · rintro ⟨x, hx, hxc⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hiW, rfl⟩ := (mem_seqOf U W p).mp hp
      exact ⟨i, Finset.mem_inter.mpr ⟨hiW, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxc⟩⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨hiW, hiH⟩ := Finset.mem_inter.mp hi
      exact ⟨t.eval (U.get i).fst,
        List.mem_map.mpr ⟨U.get i, (mem_seqOf U W _).mpr ⟨i, hiW, rfl⟩, rfl⟩,
        (Finset.mem_filter.mp hiH).2⟩
  have hsum : havingProv U t f op c
      = ∑ W ∈ Finset.univ.powerset.filter
          (fun W : Finset (Fin U.length) => (W ∩ H).Nonempty),
          ann (fun i => (U.get i).snd) Finset.univ W := by
    unfold havingProv
    rw [Finset.powerset_univ, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hW : W.Nonempty
    · rw [ite_eq_left hW, worldAnn_eq_ann]
      simp only [chi]
      by_cases hmeet : (W ∩ H).Nonempty
      · rw [ite_eq_left hmeet, ite_eq_left ((hiff W hW).mpr hmeet), mul_one]
      · rw [ite_eq_right hmeet, ite_eq_right (fun h => hmeet ((hiff W hW).mp h)), mul_zero]
    · rw [ite_eq_right hW, ite_eq_right]
      exact fun hmeet => hW (hmeet.mono Finset.inter_subset_left)
  rw [hsum, sum_ann_meet h_abs _ (Finset.subset_univ H), hH, Finset.sum_filter,
    sum_map_filter_coe]

omit [DecidableEq K] in
/-- **Existential comparisons collapse to the qualifying occurrences.** In
an absorptive m-semiring, the predicate provenance of an existential
comparison `f(t) op c` on the group sequence `U` is the `⊕`-sum of the
annotations of the occurrences whose `t`-value makes `x op c` *true*. No
distributivity of `⊗` over `⊖` is needed (`Having.sum_ann_meet`).

An occurrence whose value is null contributes nothing, and rightly: SQL's
aggregate skips it and the comparison is unknown on it, so it is in no
world's reason for the predicate holding. -/
theorem havingProv_existential3 (h_abs : absorptive K)
    {f : SeqAggFunc T} {op : CompOp}
    (hf : Existential3 f op) (U : List (AnnotatedTuple T K m)) (t : Term T m)
    (c : T) :
    havingProv U t f op c
      = ((Multiset.filter (fun p : AnnotatedTuple T K m =>
            op.eval3 (t.eval p.fst) c = Kleene.true)
          (↑U : Multiset (AnnotatedTuple T K m))).map Prod.snd).sum :=
  havingProv_existentialOn h_abs (P := fun x => op.eval3 x c = Kleene.true)
    (fun L hL => hf L c hL) U t

omit [DecidableEq K] in
/-- The same over a domain where nothing is null, the comparison then being
two-valued. -/
theorem havingProv_existential [NoNulls T] (h_abs : absorptive K)
    {f : SeqAggFunc T} {op : CompOp}
    (hf : Existential f op) (U : List (AnnotatedTuple T K m)) (t : Term T m)
    (c : T) :
    havingProv U t f op c
      = ((Multiset.filter (fun p : AnnotatedTuple T K m => op.eval (t.eval p.fst) c)
          (↑U : Multiset (AnnotatedTuple T K m))).map Prod.snd).sum := by
  rw [havingProv_existential3 (K := K) h_abs hf.to3 U t c]
  refine congrArg (fun M : Multiset (AnnotatedTuple T K m) =>
    (M.map Prod.snd).sum) ?_
  exact Multiset.filter_congr (fun q _ =>
    CompOp.eval3_eq_true_iff_noNulls op (t.eval q.fst) c)

/-- `MIN` over a non-empty sequence is below `c` iff some element is. -/
theorem foldr_min_le_iff {V : Type} [LinearOrder V] (x c : V) :
    ∀ xs : List V, xs.foldr min x ≤ c ↔ x ≤ c ∨ ∃ y ∈ xs, y ≤ c
  | [] => by simp
  | y :: ys => by
    rw [List.foldr_cons, min_le_iff, foldr_min_le_iff x c ys]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-- `MIN` over a non-empty sequence is strictly below `c` iff some element is. -/
theorem foldr_min_lt_iff {V : Type} [LinearOrder V] (x c : V) :
    ∀ xs : List V, (xs.foldr min x < c) ↔ (x < c) ∨ ∃ y ∈ xs, (y < c)
  | [] => by simp
  | y :: ys => by
    rw [List.foldr_cons, min_lt_iff, foldr_min_lt_iff x c ys]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-- `MAX` over a non-empty sequence is above `c` iff some element is. -/
theorem le_foldr_max_iff {V : Type} [LinearOrder V] (x c : V) :
    ∀ xs : List V, c ≤ xs.foldr max x ↔ c ≤ x ∨ ∃ y ∈ xs, c ≤ y
  | [] => by simp
  | y :: ys => by
    rw [List.foldr_cons, le_max_iff, le_foldr_max_iff x c ys]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-- `MAX` over a non-empty sequence is strictly above `c` iff some element is. -/
theorem lt_foldr_max_iff {V : Type} [LinearOrder V] (x c : V) :
    ∀ xs : List V, (c < xs.foldr max x) ↔ (c < x) ∨ ∃ y ∈ xs, (c < y)
  | [] => by simp
  | y :: ys => by
    rw [List.foldr_cons, lt_max_iff, lt_foldr_max_iff x c ys]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-- `MIN(t) ≤ c` is existential. -/
theorem existential_min_le : Existential (SeqAggFunc.min (T := T)) CompOp.le := by
  intro L c hL
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    show xs.foldr min x ≤ c ↔ ∃ y ∈ x :: xs, y ≤ c
    rw [foldr_min_le_iff]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- `MIN(t) < c` is existential. -/
theorem existential_min_lt : Existential (SeqAggFunc.min (T := T)) CompOp.lt := by
  intro L c hL
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    show (xs.foldr min x < c) ↔ ∃ y ∈ x :: xs, (y < c)
    rw [foldr_min_lt_iff]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- `MAX(t) ≥ c` is existential. -/
theorem existential_max_ge : Existential (SeqAggFunc.max (T := T)) CompOp.ge := by
  intro L c hL
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    show c ≤ xs.foldr max x ↔ ∃ y ∈ x :: xs, c ≤ y
    rw [le_foldr_max_iff]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- `MAX(t) > c` is existential. -/
theorem existential_max_gt : Existential (SeqAggFunc.max (T := T)) CompOp.gt := by
  intro L c hL
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    show (c < xs.foldr max x) ↔ ∃ y ∈ x :: xs, (c < y)
    rw [lt_foldr_max_iff]
    simp only [List.mem_cons, exists_eq_or_imp]

/-! ### SQL's aggregates are existential too

`MIN` and `MAX` as SQL reads them skip the nulls and answer `NULL` over what
is left of nothing. That does not disturb the collapse: the values the
aggregate skips are exactly the values a strict comparison is unknown on, so
the occurrences that qualify are the same either way. -/

/-- **SQL's reading of an aggregate that returns one of its inputs is
existential**, three-valuedly, whenever the aggregate is. The two ways a
null can enter agree: it is dropped before the aggregate sees it, and it
makes the comparison unknown. -/
theorem Existential.sqlOf3 {V : Type} [ValueTypeNull V] {f : SeqAggFunc V}
    {op : CompOp} (hs : op.strict = true)
    (hmem : ∀ {L : List V}, L ≠ [] → f L ∈ L)
    (hf : Existential f op) : Existential3 f.sqlOf op := by
  intro L c _
  by_cases hc : ValueType.isNull c = true
  · rw [CompOp.eval3_of_isNull_right hs _ hc]
    constructor
    · exact fun h => Kleene.noConfusion h
    · rintro ⟨x, -, hx⟩
      rw [CompOp.eval3_of_isNull_right hs _ hc] at hx
      exact Kleene.noConfusion hx
  -- an occurrence with a null value neither reaches the aggregate nor
  -- satisfies the comparison
  have hnull : ∀ x : V, x = ValueTypeNull.null → op.eval3 x c ≠ Kleene.true := by
    intro x hx h
    rw [hx, CompOp.eval3_of_isNull_left hs ValueTypeNull.isNull_null] at h
    exact Kleene.noConfusion h
  rcases SeqAggFunc.sqlOf_mem_or_null f hmem L with hq | ⟨hqmem, hqne⟩
  · -- the aggregate is null: nothing of the sequence is left for it
    rw [hq, CompOp.eval3_of_isNull_left hs ValueTypeNull.isNull_null]
    constructor
    · exact fun h => Kleene.noConfusion h
    · have hemp : L.filter (fun a => decide (a ≠ ValueTypeNull.null)) = [] := by
        by_contra hne
        have hm := hmem hne
        have hnn : f (L.filter (fun a => decide (a ≠ ValueTypeNull.null)))
            ≠ ValueTypeNull.null := by simpa using (List.mem_filter.mp hm).2
        have hsq : f.sqlOf L
            = f (L.filter (fun a => decide (a ≠ ValueTypeNull.null))) := by
          unfold SeqAggFunc.sqlOf
          rw [ite_eq_right (by simpa using hne)]
        exact hnn (hsq.symm.trans hq)
      rintro ⟨x, hxL, hx⟩
      have hxn : x = ValueTypeNull.null := by
        by_contra hxc
        have hmem' : x ∈ L.filter (fun a => decide (a ≠ ValueTypeNull.null)) :=
          List.mem_filter.mpr ⟨hxL, by simpa using hxc⟩
        rw [hemp] at hmem'
        exact absurd hmem' (List.not_mem_nil)
      exact absurd hx (hnull x hxn)
  · -- the aggregate is one of the non-null values
    have hqnn : ValueType.isNull (f.sqlOf L) = false := by
      rw [ValueTypeNull.isNull_iff]; simpa using hqne
    have hcnn : ValueType.isNull c = false := by simpa using hc
    have hfil : L.filter (fun a => decide (a ≠ ValueTypeNull.null)) ≠ [] := by
      intro hc'
      apply hqne
      unfold SeqAggFunc.sqlOf
      rw [hc']
      rfl
    have hsq : f.sqlOf L = f (L.filter (fun a => decide (a ≠ ValueTypeNull.null))) := by
      unfold SeqAggFunc.sqlOf
      rw [ite_eq_right (by simpa using hfil)]
    rw [CompOp.eval3_eq_true_iff op hqnn hcnn, hsq, hf _ c hfil]
    constructor
    · rintro ⟨x, hx, hxc⟩
      obtain ⟨hxL, hxn⟩ := List.mem_filter.mp hx
      refine ⟨x, hxL, ?_⟩
      rw [CompOp.eval3_eq_true_iff op (by rw [ValueTypeNull.isNull_iff]; simpa using hxn) hcnn]
      exact hxc
    · rintro ⟨x, hxL, hxc⟩
      have hxn : ¬ (x = ValueTypeNull.null) := fun hx => hnull x hx hxc
      refine ⟨x, List.mem_filter.mpr ⟨hxL, by simpa using hxn⟩, ?_⟩
      rw [CompOp.eval3_eq_true_iff op (by rw [ValueTypeNull.isNull_iff]; simpa using hxn)
        hcnn] at hxc
      exact hxc

/-- SQL's `MIN(t) ≤ c` is existential. -/
theorem existential3_sqlOf_min_le {V : Type} [ValueTypeNull V] :
    Existential3 (SeqAggFunc.min (T := V)).sqlOf CompOp.le :=
  Existential.sqlOf3 rfl (fun h => SeqAggFunc.min_mem h) existential_min_le

/-- SQL's `MIN(t) < c` is existential. -/
theorem existential3_sqlOf_min_lt {V : Type} [ValueTypeNull V] :
    Existential3 (SeqAggFunc.min (T := V)).sqlOf CompOp.lt :=
  Existential.sqlOf3 rfl (fun h => SeqAggFunc.min_mem h) existential_min_lt

/-- SQL's `MAX(t) ≥ c` is existential. -/
theorem existential3_sqlOf_max_ge {V : Type} [ValueTypeNull V] :
    Existential3 (SeqAggFunc.max (T := V)).sqlOf CompOp.ge :=
  Existential.sqlOf3 rfl (fun h => SeqAggFunc.max_mem h) existential_max_ge

/-- SQL's `MAX(t) > c` is existential. -/
theorem existential3_sqlOf_max_gt {V : Type} [ValueTypeNull V] :
    Existential3 (SeqAggFunc.max (T := V)).sqlOf CompOp.gt :=
  Existential.sqlOf3 rfl (fun h => SeqAggFunc.max_mem h) existential_max_gt

end Having

/-! ### Boolean combinations of aggregate comparisons -/

/-- Boolean combinations of fused aggregate comparisons: atoms compare a
sequence aggregate of a term over the group to a regular term over the
group key; combinations are negation, conjunction and disjunction. -/
inductive HavingPred (T : Type) (m n₁ : ℕ) where
  | cmp : Term T m → SeqAggFunc T → CompOp → Term T n₁ → HavingPred T m n₁
  | not : HavingPred T m n₁ → HavingPred T m n₁
  | and : HavingPred T m n₁ → HavingPred T m n₁ → HavingPred T m n₁
  | or : HavingPred T m n₁ → HavingPred T m n₁ → HavingPred T m n₁

/-- Worker for `HavingPred.prov`, carrying the polarity of the enclosing
negations (mirroring ProvSQL's rewriting of `HAVING` predicates, which
pushes `NOT` through Boolean combinations by De Morgan duality and
complements the comparison operator at the leaves). Under `negated`,
conjunction becomes `⊕`, disjunction becomes `⊗`, and an atom's operator
is complemented; since `χ_op` is `{𝟘, 𝟙}`-valued, complementing the
operator is the same as interpreting `¬` world-wise inside the
possible-world sum, which keeps the nonempty-world guard (an outer
`𝟙 ⊖ ·` interpretation would instead hold on worlds where the group is
empty, although the grouping outputs no row there). -/
def HavingPred.provAux (U : List (AnnotatedTuple T K m)) (g : Tuple T n₁)
    (negated : Bool) : HavingPred T m n₁ → K
  | cmp t f op s =>
      Having.havingProv U t f (if negated then op.negate else op) (s.eval g)
  | not ψ => ψ.provAux U g (!negated)
  | and ψ₁ ψ₂ =>
      if negated then ψ₁.provAux U g negated + ψ₂.provAux U g negated
      else ψ₁.provAux U g negated * ψ₂.provAux U g negated
  | or ψ₁ ψ₂ =>
      if negated then ψ₁.provAux U g negated * ψ₂.provAux U g negated
      else ψ₁.provAux U g negated + ψ₂.provAux U g negated

/-- Predicate provenance of a Boolean combination of aggregate
comparisons, on the occurrence sequence `U` of the group of key `g`:
conjunction is interpreted by `⊗`, disjunction by `⊕`, and negation by
pushing it to the atoms (De Morgan duality, complementing the comparison
operator of an atom), as ProvSQL does. -/
def HavingPred.prov (U : List (AnnotatedTuple T K m)) (g : Tuple T n₁)
    (ψ : HavingPred T m n₁) : K :=
  ψ.provAux U g false

/-- **Three-valued evaluation of a `HAVING` predicate on one possible
world**: a plain occurrence sequence `L` (the tuples of one group, in
`≼`-order) with group key `g`. An atom applies the sequence aggregate to the
`t`-values of `L` and compares with the regular term evaluated on the key, in
Kleene's three-valued logic – a comparison with a `NULL` operand is neither
true nor false. `∧`, `∨` and `¬` are Kleene's. -/
def HavingPred.evalOnSeq (L : List (Tuple T m)) (g : Tuple T n₁) :
    HavingPred T m n₁ → Kleene
  | cmp t f op s => op.eval3 (f (L.map t.eval)) (s.eval g)
  | not ψ => (ψ.evalOnSeq L g).not
  | and ψ₁ ψ₂ => (ψ₁.evalOnSeq L g).and (ψ₂.evalOnSeq L g)
  | or ψ₁ ψ₂ => (ψ₁.evalOnSeq L g).or (ψ₂.evalOnSeq L g)

/-- The groups a `HAVING` predicate keeps in one world: those on which it is
*true*. A group on which it is unknown is kept by neither the predicate nor
its negation. -/
def HavingPred.holdsOnSeq (L : List (Tuple T m)) (g : Tuple T n₁)
    (ψ : HavingPred T m n₁) : Prop := ψ.evalOnSeq L g = Kleene.true

instance HavingPred.decidableHoldsOnSeq (L : List (Tuple T m)) (g : Tuple T n₁)
    (ψ : HavingPred T m n₁) : Decidable (ψ.holdsOnSeq L g) :=
  inferInstanceAs (Decidable (_ = _))

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **Where nothing is null the reading is two-valued.** No `HAVING`
predicate is ever unknown there, so the statements proved before the null
was introduced keep saying what they said. -/
theorem HavingPred.evalOnSeq_ne_unknown [NoNulls T] (L : List (Tuple T m))
    (g : Tuple T n₁) : ∀ ψ : HavingPred T m n₁,
      ψ.evalOnSeq L g ≠ Kleene.unknown
  | cmp t f op s => by
    rw [HavingPred.evalOnSeq, CompOp.eval3_eq_ofBool]
    cases h : decide (op.eval (f (L.map t.eval)) (s.eval g)) <;> simp [Kleene.ofBool]
  | not ψ => by
    have := evalOnSeq_ne_unknown L g ψ
    cases h : ψ.evalOnSeq L g <;> simp_all [HavingPred.evalOnSeq, Kleene.not]
  | and ψ₁ ψ₂ => by
    have h₁ := evalOnSeq_ne_unknown L g ψ₁
    have h₂ := evalOnSeq_ne_unknown L g ψ₂
    cases e₁ : ψ₁.evalOnSeq L g <;> cases e₂ : ψ₂.evalOnSeq L g <;>
      simp_all [HavingPred.evalOnSeq, Kleene.and]
  | or ψ₁ ψ₂ => by
    have h₁ := evalOnSeq_ne_unknown L g ψ₁
    have h₂ := evalOnSeq_ne_unknown L g ψ₂
    cases e₁ : ψ₁.evalOnSeq L g <;> cases e₂ : ψ₂.evalOnSeq L g <;>
      simp_all [HavingPred.evalOnSeq, Kleene.or]

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- Negation is classical where nothing is null. -/
theorem HavingPred.holdsOnSeq_not_iff [NoNulls T] (L : List (Tuple T m))
    (g : Tuple T n₁) (ψ : HavingPred T m n₁) :
    (HavingPred.not ψ).holdsOnSeq L g ↔ ¬ ψ.holdsOnSeq L g := by
  have h := evalOnSeq_ne_unknown L g ψ
  show (ψ.evalOnSeq L g).not = Kleene.true ↔ ¬ (ψ.evalOnSeq L g = Kleene.true)
  cases e : ψ.evalOnSeq L g <;> simp_all [Kleene.not]

/-- Plain possible-world satisfaction of a Boolean `HAVING` query: the
query grouping the output of `q` by the columns `is` and keeping the
groups satisfying `ψ` holds on the database `d` iff some realized group
key satisfies `ψ` – equivalently, iff its output is non-empty. -/
def HavingPred.modelsBoolean (d : Database T) (q : Query T m)
    (is : Tuple (Fin m) n₁) (ψ : HavingPred T m n₁) : Prop :=
  ∃ g ∈ (q.evaluate d).map (fun u => fun k => u (is k)),
    ψ.holdsOnSeq (Relation.groupSeq is (q.evaluate d) g) g

instance HavingPred.decidableModelsBoolean (d : Database T) (q : Query T m)
    (is : Tuple (Fin m) n₁) (ψ : HavingPred T m n₁) :
    Decidable (ψ.modelsBoolean d q is) :=
  haveI : Decidable (∀ g ∈ (q.evaluate d).map (fun u => fun k => u (is k)),
      ¬ ψ.holdsOnSeq (Relation.groupSeq is (q.evaluate d) g) g) :=
    Multiset.decidableForallMultiset
  decidable_of_iff
    (¬ ∀ g ∈ (q.evaluate d).map (fun u => fun k => u (is k)),
        ¬ ψ.holdsOnSeq (Relation.groupSeq is (q.evaluate d) g) g)
    (Iff.intro
      (fun h => Classical.byContradiction fun hne =>
        h fun g hg hP => hne ⟨g, hg, hP⟩)
      (fun hex hall => match hex with
        | ⟨g, hg, hP⟩ => hall g hg hP))

/-- Boolean provenance of a Boolean `HAVING` query – the `⊕`-sum of the
annotations of the output rows of `σ_ψ(γ^≼(q))`: one summand per
distinct group key of the inner query, carrying the predicate provenance
of its group. -/
def HavingPred.booleanProv [HasAltLinearOrder K] (q : Query T m) (hq : q.source)
    (d : AnnotatedDatabase T K) (is : Tuple (Fin m) n₁)
    (ψ : HavingPred T m n₁) : K :=
  (((q.evaluateAnnotated hq d).map (fun p => fun k => p.fst (is k))).dedup.map
    (fun g => ψ.prov (Having.havingGroup is (q.evaluateAnnotated hq d) g) g)).sum
