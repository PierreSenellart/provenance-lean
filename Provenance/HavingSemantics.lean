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
site (`AggQuery.havingSite`, in `Provenance.AggQueryBridges`) has exactly
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
/-- A comparison with a `NULL` operand contributes nothing. -/
@[simp] theorem chi_of_isNull_left (op : CompOp) {a : T}
    (h : ValueType.isNull a = true) (b : T) : (chi op a b : K) = 0 := by
  simp [chi, h]

omit [DecidableEq K] in
@[simp] theorem chi_of_isNull_right (op : CompOp) (a : T) {b : T}
    (h : ValueType.isNull b = true) : (chi op a b : K) = 0 := by
  simp [chi, h]

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
  · rw [chi_of_isNull_left _ hna, chi_of_isNull_left _ hna,
      chi_of_isNull_left _ hna, add_zero]
  by_cases hnc : ValueType.isNull c = true
  · rw [chi_of_isNull_right _ _ hnc, chi_of_isNull_right _ _ hnc,
      chi_of_isNull_right _ _ hnc, add_zero]
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

-- `Existential` is two-valued, so the collapse below is stated over a
-- domain where nothing is null. What an existential comparison collapses to
-- when the aggregated values may be null is a separate question: the
-- aggregate skips them (`SeqAggFunc.sqlOf`) while the comparison does not.

omit [DecidableEq K] in
/-- **Existential comparisons collapse to the qualifying occurrences.** In
an absorptive m-semiring, the predicate provenance of an existential
comparison `f(t) op c` on the group sequence `U` is the `⊕`-sum of the
annotations of the occurrences whose `t`-value satisfies `x op c`. No
distributivity of `⊗` over `⊖` is needed (`Having.sum_ann_meet`). -/
theorem havingProv_existential [NoNulls T] (h_abs : absorptive K)
    {f : SeqAggFunc T} {op : CompOp}
    (hf : Existential f op) (U : List (AnnotatedTuple T K m)) (t : Term T m) (c : T) :
    havingProv U t f op c
      = ((Multiset.filter (fun p : AnnotatedTuple T K m => op.eval (t.eval p.fst) c)
          (↑U : Multiset (AnnotatedTuple T K m))).map Prod.snd).sum := by
  set H : Finset (Fin U.length) :=
    Finset.univ.filter (fun i => op.eval (t.eval (U.get i).fst) c) with hH
  -- the comparison holds in a non-empty world iff the world meets `H`
  have hiff : ∀ W : Finset (Fin U.length), W.Nonempty →
      (op.eval (aggValOn U t f W) c ↔ (W ∩ H).Nonempty) := by
    intro W hW
    have hne : ((seqOf U W).map (fun p => t.eval p.fst)) ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_map, seqOf_length]
      exact Finset.card_pos.mpr hW
    unfold aggValOn
    rw [hf _ c hne]
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
    · rw [ite_eq_left hW, chi_eq_ite_of_noNulls, worldAnn_eq_ann]
      by_cases hmeet : (W ∩ H).Nonempty
      · rw [ite_eq_left hmeet, ite_eq_left ((hiff W hW).mpr hmeet), mul_one]
      · rw [ite_eq_right hmeet, ite_eq_right (fun h => hmeet ((hiff W hW).mp h)), mul_zero]
    · rw [ite_eq_right hW, ite_eq_right]
      exact fun hmeet => hW (hmeet.mono Finset.inter_subset_left)
  rw [hsum, sum_ann_meet h_abs _ (Finset.subset_univ H), hH, Finset.sum_filter,
    sum_map_filter_coe]

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
