/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.SubWorlds
public import Provenance.AggQuery
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Provenance.AggQueryBridges

/-!
# The joint reading of a family, and homomorphisms

A selection comparing several aggregate values of one family reads them
in one world of the family (`classWorlds`). Under a homomorphism the
family's listing is reordered among tied occurrences – the evaluator
lists a group by its rows and then by the annotations, and the
annotations are not the same on the two sides – and a joint reading is
blind to that only if every value of the family is reordered *together*.

This holds when every value of the family is built from **one listing**
of the family's occurrences by a function of the occurrence's row: a
`LeafSpec` says how a value reads an occurrence (what each of its leaves
reads, whether it is in the leaf's group, whether the leaf's clause keeps
it), and `LeafSpec.build` is the value it builds from a listing. Then a
world of the family is read off the sequence of rows it selects
(`classWorlds_presented`), the bag of those is blind to a tie-block
permutation of the listing (`subWorlds_tiePerm`), and the joint worlds of
the two sides correspond (`classWorlds_hom`).
-/

@[expose] public section

/-- **How an aggregate value reads an occurrence of its family**, as a
function of the occurrence's row `ρ`: the value each leaf reads, whether
the occurrence is in each leaf's group, whether each leaf's clause keeps
it – and the leaves' aggregates, conventions and combining function. -/
structure LeafSpec (ρ T : Type) where
  arity : ℕ
  V : ρ → Fin arity → T
  Fr : ρ → Fin arity → Bool
  Kp : ρ → Fin arity → Bool
  aggs : Fin arity → SeqAggFunc T
  scalar : Fin arity → Bool
  g : (Fin arity → T) → T

namespace LeafSpec

variable {ρ T β K : Type}

/-- The value built from a listing `L` of the family, an occurrence being
read through its row `str` and annotated by `ann`. -/
def build (sp : LeafSpec ρ T) (L : List β) (ann : β → K) (str : β → ρ) (φ : FamId T) :
    AggExpr T K :=
  ⟨sp.arity, L.map (fun b => (sp.V (str b), ann b, sp.Fr (str b), sp.Kp (str b))),
    sp.aggs, sp.scalar, sp.g, φ, []⟩

/-- Whether a selected sequence of rows is a world of the value. -/
def okL (sp : LeafSpec ρ T) (s : List ρ) : Prop :=
  ∀ j, sp.scalar j = false → ∃ r ∈ s, sp.Fr r j = true

/-- The value on a selected sequence of rows. -/
def valL (sp : LeafSpec ρ T) (s : List ρ) : T :=
  sp.g (fun j => sp.aggs j ((s.filter (fun r => sp.Fr r j && sp.Kp r j)).map (fun r => sp.V r j)))

/-- **A world of a built value is read off the rows it selects.** -/
theorem isWorld_build (sp : LeafSpec ρ T) (L : List β) (ann : β → K) (str : β → ρ)
    {e : AggExpr T K} {φ : FamId T} (he : e = sp.build L ann str φ)
    (h : L.length = e.occs.length) (W : Finset (Fin L.length)) :
    e.IsWorld (W.map (finCongr h).toEmbedding) ↔ sp.okL ((Having.seqOf L W).map str) := by
  subst he
  rw [AggExpr.isWorld_iff_okSeq]
  unfold build at h ⊢
  dsimp only at h ⊢
  rw [AggValue.seqOf_map _ L h W]
  unfold AggExpr.okSeq okL
  simp only [List.mem_map, exists_exists_and_eq_and]

/-- **So is its value.** -/
theorem valOn_build (sp : LeafSpec ρ T) (L : List β) (ann : β → K) (str : β → ρ)
    {e : AggExpr T K} {φ : FamId T} (he : e = sp.build L ann str φ)
    (h : L.length = e.occs.length) (W : Finset (Fin L.length)) :
    e.valOn (W.map (finCongr h).toEmbedding) = sp.valL ((Having.seqOf L W).map str) := by
  subst he
  rw [AggExpr.valOn_eq_valSeq]
  unfold build at h ⊢
  dsimp only at h ⊢
  rw [AggValue.seqOf_map _ L h W]
  unfold AggExpr.valSeq valL
  simp only [List.filter_map, List.map_map]
  rfl

/-- **The annotations of a built value are the listing's.** -/
theorem anns_build (sp : LeafSpec ρ T) (L : List β) (ann : β → K) (str : β → ρ)
    {e : AggExpr T K} {φ : FamId T} (he : e = sp.build L ann str φ)
    (h : L.length = e.occs.length) (i : Fin L.length) :
    e.anns (finCongr h i) = ann (L.get i) := by
  subst he
  simp [AggExpr.anns, build]

end LeafSpec

/-- **An aggregate expression presented by a listing**: its occurrences
are the listing's, position for position, with the listing's
annotations, and its world condition and its value are read off the rows
a world selects, through `ok` and `val`. This is all a joint reading
asks of a value of a family. -/
def AggExpr.PresBy {ρ β T K : Type} (e : AggExpr T K) (L : List β) (ann : β → K)
    (str : β → ρ) (ok : List ρ → Prop) (val : List ρ → T) : Prop :=
  ∃ h : L.length = e.occs.length, (∀ i, e.anns (finCongr h i) = ann (L.get i))
    ∧ (∀ W : Finset (Fin L.length),
        e.IsWorld (W.map (finCongr h).toEmbedding) ↔ ok ((Having.seqOf L W).map str))
    ∧ ∀ W : Finset (Fin L.length),
        e.valOn (W.map (finCongr h).toEmbedding) = val ((Having.seqOf L W).map str)

/-- A value built by a `LeafSpec` is presented by its listing. -/
theorem LeafSpec.presBy_build {ρ β T K : Type} (sp : LeafSpec ρ T) (L : List β) (ann : β → K)
    (str : β → ρ) {e : AggExpr T K} {φ : FamId T} (he : e = sp.build L ann str φ) :
    e.PresBy L ann str sp.okL sp.valL := by
  have h : L.length = e.occs.length := by rw [he]; simp [LeafSpec.build]
  exact ⟨h, sp.anns_build L ann str he h, sp.isWorld_build L ann str he h,
    sp.valOn_build L ann str he h⟩

/-! ## Two lists related position by position -/

namespace List.Forall₂

variable {α α' κ κ' : Type} {R : α' → α → Prop}

theorem exists_of_mem_left {l' : List α'} {l : List α} (h : Forall₂ R l' l) {a' : α'}
    (ha : a' ∈ l') : ∃ a ∈ l, R a' a := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | @cons b' b t' t hb _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨a, haa, hr⟩ := ih ha
      exact ⟨a, List.mem_cons_of_mem _ haa, hr⟩

theorem exists_of_mem_right {l' : List α'} {l : List α} (h : Forall₂ R l' l) {a : α}
    (ha : a ∈ l) : ∃ a' ∈ l', R a' a := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | @cons b' b t' t hb _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b', List.mem_cons_self, hb⟩
    · obtain ⟨a', haa, hr⟩ := ih ha
      exact ⟨a', List.mem_cons_of_mem _ haa, hr⟩

/-- Searching two related lists by corresponding tests. -/
theorem find?_rel {l' : List α'} {l : List α} (h : Forall₂ R l' l) {P' : α' → Bool}
    {P : α → Bool} (hP : ∀ a' a, R a' a → (P' a' = P a)) :
    Option.Rel R (l'.find? P') (l.find? P) := by
  induction h with
  | nil => exact Option.Rel.none
  | @cons a' a t' t ha _ ih =>
    rw [List.find?_cons, List.find?_cons, hP a' a ha]
    cases P a
    · exact ih
    · exact Option.Rel.some ha

/-- Filtering two related lists by corresponding tests. -/
theorem filter_rel {l' : List α'} {l : List α} (h : Forall₂ R l' l) {P' : α' → Bool}
    {P : α → Bool} (hP : ∀ a' a, R a' a → (P' a' = P a)) :
    Forall₂ R (l'.filter P') (l.filter P) := by
  induction h with
  | nil => exact Forall₂.nil
  | @cons a' a t' t ha _ ih =>
    rw [List.filter_cons, List.filter_cons, hP a' a ha]
    cases P a
    · exact ih
    · exact Forall₂.cons ha ih

/-- **Deduplicating the keys of two related lists**, when related elements
are keyed alike: the surviving keys correspond, each to a key of
related elements. -/
theorem dedup_map_rel [DecidableEq κ] [DecidableEq κ'] {g' : α' → κ'} {g : α → κ}
    {l' : List α'} {l : List α} (h : Forall₂ R l' l)
    (hk : ∀ a' a b' b, R a' a → R b' b → (g' a' = g' b' ↔ g a = g b)) :
    Forall₂ (fun φ' φ => ∃ a' a, R a' a ∧ a' ∈ l' ∧ a ∈ l ∧ g' a' = φ' ∧ g a = φ)
      (l'.map g').dedup (l.map g).dedup := by
  induction h with
  | nil => exact Forall₂.nil
  | @cons a' a t' t ha ht ih =>
    have hmem : g' a' ∈ t'.map g' ↔ g a ∈ t.map g := by
      simp only [List.mem_map]
      constructor
      · rintro ⟨b', hb', hbe⟩
        obtain ⟨b, hb, hr⟩ := ht.exists_of_mem_left hb'
        exact ⟨b, hb, ((hk b' b a' a hr ha).mp hbe)⟩
      · rintro ⟨b, hb, hbe⟩
        obtain ⟨b', hb', hr⟩ := ht.exists_of_mem_right hb
        exact ⟨b', hb', ((hk b' b a' a hr ha).mpr hbe)⟩
    have ih' : Forall₂ (fun φ' φ => ∃ b' b, R b' b ∧ b' ∈ a' :: t' ∧ b ∈ a :: t
        ∧ g' b' = φ' ∧ g b = φ) (t'.map g').dedup (t.map g).dedup :=
      ih.imp (fun {φ' φ} ⟨b', b, hr, hb', hb, he', he⟩ =>
        ⟨b', b, hr, List.mem_cons_of_mem _ hb', List.mem_cons_of_mem _ hb, he', he⟩)
    rw [List.map_cons, List.map_cons]
    by_cases hin : g a ∈ t.map g
    · rw [List.dedup_cons_of_mem hin, List.dedup_cons_of_mem (hmem.mpr hin)]
      exact ih'
    · rw [List.dedup_cons_of_notMem hin, List.dedup_cons_of_notMem (fun h => hin (hmem.mp h))]
      exact Forall₂.cons ⟨a', a, ha, List.mem_cons_self, List.mem_cons_self, rfl, rfl⟩ ih'

end List.Forall₂

section ClassWorlds

variable {T K : Type} [CommSemiringWithMonus K]

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

/-- The subsets of positions of a list, reindexed along a length
equality. -/
theorem univ_val_reindex {a b : ℕ} (h : a = b) :
    (Finset.univ : Finset (Finset (Fin b))).val
      = (Finset.univ : Finset (Finset (Fin a))).val.map
          (fun W => W.map (finCongr h).toEmbedding) := by
  subst h
  simp

/-- Reading a reindexed world in another listing of the same length. -/
theorem trW_map {a b c : ℕ} (h₁ : c = a) (h₂ : c = b) (W : Finset (Fin c)) :
    trW (a := a) (b := b) (W.map (finCongr h₁).toEmbedding)
      = W.map (finCongr h₂).toEmbedding := by
  ext i
  simp only [trW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
  constructor
  · rintro ⟨j, hj, hji⟩
    convert hj using 1
    exact Fin.ext (by simp [hji])
  · intro hi
    exact ⟨finCongr h₁ ((finCongr h₂).symm i), by simpa using hi, by simp⟩

theorem compl_map_finCongr {a b : ℕ} (h : a = b) (W : Finset (Fin a)) :
    (W.map (finCongr h).toEmbedding)ᶜ = Wᶜ.map (finCongr h).toEmbedding := by
  ext i
  simp [Finset.mem_map_equiv]

open Classical in
/-- **A family built from one listing reads its worlds off the listing.**
If every column of `M` holds a value presented by the listing `L` (each
read through its own `ok` and `val`), and so does the value `x₀` the
family is listed by, then the family's worlds are the subfamilies of `L`,
each read through the rows it selects. -/
theorem classWorlds_presented [ValueType T] [DecidableEq K] {ρ β : Type} {n : ℕ}
    (u : Tuple (GenValue T K) n)
    (M : List (Fin n)) (L : List β) (ann : β → K) (str : β → ρ)
    (ok : Fin n → List ρ → Prop) (val : Fin n → List ρ → T)
    (hM : ∀ k ∈ M, ∃ y, u k = Sum.inr y ∧ y.flatExpr.PresBy L ann str (ok k) (val k))
    (x₀ : AggTok T K) (hx₀ : x₀.isNested = false) (ok₀ : List ρ → Prop) (val₀ : List ρ → T)
    (hx₀b : x₀.flatExpr.PresBy L ann str ok₀ val₀) :
    classWorlds u M x₀
      = ((((subWorlds ann L).map (fun w => (w.1, w.2.1, w.2.2.map str))).filter
          (fun w => ∀ k ∈ M, ok k w.2.2)).map
          (fun w => (w.1, w.2.1, fun k => if k ∈ M then some (val k w.2.2) else none))) := by
  have hdef : classWorlds u M x₀
      = ((Finset.univ.filter (fun W : Finset (Fin x₀.flatExpr.occs.length) =>
          flatOk u M W = true)).val.map
        (fun W => (∏ i ∈ W, x₀.flatExpr.anns i, ∑ i ∈ Wᶜ, x₀.flatExpr.anns i,
          fun k => if k ∈ M then
            (match u k with
              | Sum.inr y => some (y.flatExpr.valOn (trW W))
              | _ => none) else none))) := by
    cases x₀ with
    | nest a => simp [AggTok.isNested] at hx₀
    | tok a => rfl
    | expr a => rfl
  obtain ⟨h₀, hann₀, -, -⟩ := hx₀b
  rw [hdef, Finset.filter_val, univ_val_reindex h₀, Multiset.filter_map, Multiset.map_map,
    ← univ_map_eq_subWorlds ann L, Multiset.map_map, Multiset.filter_map, Multiset.map_map]
  have hcol : ∀ k ∈ M, ∀ W' : Finset (Fin L.length), ∃ y, u k = Sum.inr y ∧
      (y.flatExpr.IsWorld (trW (a := x₀.flatExpr.occs.length) (W'.map (finCongr h₀).toEmbedding))
        ↔ ok k ((Having.seqOf L W').map str))
      ∧ y.flatExpr.valOn (trW (a := x₀.flatExpr.occs.length) (W'.map (finCongr h₀).toEmbedding))
        = val k ((Having.seqOf L W').map str) := by
    intro k hk W'
    obtain ⟨y, hy, hk', -, hw, hv⟩ := hM k hk
    refine ⟨y, hy, ?_, ?_⟩
    · rw [trW_map h₀ hk']
      exact hw W'
    · rw [trW_map h₀ hk']
      exact hv W'
  rw [Multiset.filter_congr (q := fun W' : Finset (Fin L.length) =>
    ∀ k ∈ M, ok k ((Having.seqOf L W').map str))]
  · refine Multiset.map_congr rfl (fun W' _ => ?_)
    simp only [Function.comp]
    refine Prod.ext ?_ (Prod.ext ?_ (funext fun k => ?_))
    · rw [Finset.prod_map]
      exact Finset.prod_congr rfl (fun i _ => hann₀ i)
    · rw [compl_map_finCongr, Finset.sum_map]
      exact Finset.sum_congr rfl (fun i _ => hann₀ i)
    · dsimp only
      by_cases hk : k ∈ M
      · rw [ite_eq_left hk, ite_eq_left hk]
        obtain ⟨y, hy, -, hv⟩ := hcol k hk W'
        rw [hy]
        exact congrArg some hv
      · rw [ite_eq_right hk, ite_eq_right hk]
  · intro W' _
    simp only [Function.comp, flatOk_iff]
    refine forall₂_congr (fun k hk => ?_)
    obtain ⟨y, hy, hw, -⟩ := hcol k hk W'
    constructor
    · intro h; exact hw.mp (h y hy)
    · intro h y' hy'
      rw [hy] at hy'
      cases hy'
      exact hw.mpr h

/-- **The joint worlds of a family under a homomorphism.** On the two
sides the family's values are presented, through the same readings, by
two listings, the second a tie-block permutation of the first pushed
through `f` – occurrences swapped only where their rows read alike. Then
the family's worlds correspond, annotations pushed through `f` and every
value unchanged: the values of the family are reordered together. -/
theorem classWorlds_hom [ValueType T] [DecidableEq K] {K' : Type} [CommSemiringWithMonus K']
    [DecidableEq K'] (f : K →+* K')
    {ρ β β' : Type} {n : ℕ} (u : Tuple (GenValue T K) n) (u' : Tuple (GenValue T K') n)
    (M : List (Fin n)) (L : List β) (ann : β → K) (str : β → ρ)
    (L' : List β') (ann' : β' → K') (str' : β' → ρ) (e : β → β')
    {eqv : β' → β' → Prop} (heqv : ∀ {a b}, eqv a b → str' a = str' b)
    (hperm : TiePerm eqv L' (L.map e))
    (hstr : ∀ b, str' (e b) = str b) (hann : ∀ b, ann' (e b) = f (ann b))
    (ok : Fin n → List ρ → Prop) (val : Fin n → List ρ → T)
    (hM : ∀ k ∈ M, ∃ y, u k = Sum.inr y ∧ y.flatExpr.PresBy L ann str (ok k) (val k))
    (hM' : ∀ k ∈ M, ∃ y, u' k = Sum.inr y ∧ y.flatExpr.PresBy L' ann' str' (ok k) (val k))
    (x₀ : AggTok T K) (hx₀ : x₀.isNested = false) (ok₀ : List ρ → Prop) (val₀ : List ρ → T)
    (hx₀b : x₀.flatExpr.PresBy L ann str ok₀ val₀)
    (x₀' : AggTok T K') (hx₀' : x₀'.isNested = false)
    (hx₀b' : x₀'.flatExpr.PresBy L' ann' str' ok₀ val₀) :
    classWorlds u' M x₀' = (classWorlds u M x₀).map (fun w => (f w.1, f w.2.1, w.2.2)) := by
  rw [classWorlds_presented u M L ann str ok val hM x₀ hx₀ ok₀ val₀ hx₀b,
    classWorlds_presented u' M L' ann' str' ok val hM' x₀' hx₀' ok₀ val₀ hx₀b',
    subWorlds_tiePerm ann' str' heqv hperm, subWorlds_map f ann ann' e hann L]
  simp only [Multiset.map_map, Multiset.filter_map, Function.comp_def, List.map_map, hstr]

theorem multiset_map_product_map {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (s : Multiset α) (t : Multiset β) :
    (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.cons_product, Multiset.cons_product, ih, Multiset.map_add,
      Multiset.map_map, Multiset.map_map]
    rfl

omit [CommSemiringWithMonus K] in
/-- The aggregate columns of two rows that hold aggregate values at the
same columns, paired by column. -/
theorem tokCols_rel {K' : Type} {n : ℕ} (u : Tuple (GenValue T K) n)
    (u' : Tuple (GenValue T K') n) (cols : List (Fin n))
    (hagg : ∀ k ∈ cols, (∃ x, u k = Sum.inr x) ↔ (∃ x', u' k = Sum.inr x')) :
    List.Forall₂ (fun (p' : Fin n × AggTok T K') (p : Fin n × AggTok T K) => p'.1 = p.1)
      (tokCols u' cols) (tokCols u cols) := by
  induction cols with
  | nil => exact List.Forall₂.nil
  | cons k t ih =>
    have ih' := ih (fun k' hk' => hagg k' (List.mem_cons_of_mem _ hk'))
    have hk := hagg k List.mem_cons_self
    unfold tokCols at ih' ⊢
    rw [List.filterMap_cons, List.filterMap_cons]
    rcases hu : u k with v | x <;> rcases hu' : u' k with v' | x'
    · exact ih'
    · exact absurd (hk.mpr ⟨x', hu'⟩) (by rintro ⟨y, hy⟩; rw [hu] at hy; cases hy)
    · exact absurd (hk.mp ⟨x, hu⟩) (by rintro ⟨y, hy⟩; rw [hu'] at hy; cases hy)
    · exact List.Forall₂.cons rfl ih'

open Classical in
/-- **The joint worlds of a row under a homomorphism.** If the two rows
hold aggregate values at the same compared columns, group them into
families alike, and each family's worlds correspond, so do the joint
worlds. -/
theorem jointWorlds_hom [ValueType T] [DecidableEq K] {K' : Type} [CommSemiringWithMonus K']
    [DecidableEq K'] (f : K →+* K') {n : ℕ}
    (u : Tuple (GenValue T K) n) (u' : Tuple (GenValue T K') n) (cols : List (Fin n))
    (hagg : ∀ k ∈ cols, (∃ x, u k = Sum.inr x) ↔ (∃ x', u' k = Sum.inr x'))
    (hkey : ∀ k ∈ cols, ∀ l ∈ cols, ∀ x y x' y', u k = Sum.inr x → u l = Sum.inr y →
      u' k = Sum.inr x' → u' l = Sum.inr y' →
      (x'.classKey = y'.classKey ↔ x.classKey = y.classKey))
    (hclass : ∀ k ∈ cols, ∀ x x', u k = Sum.inr x → u' k = Sum.inr x' →
      classWorlds u' (((tokCols u cols).filter (fun p => decide (p.2.classKey = x.classKey))).map
          Prod.fst) x'
        = (classWorlds u (((tokCols u cols).filter
            (fun p => decide (p.2.classKey = x.classKey))).map
          Prod.fst) x).map (fun w => (f w.1, f w.2.1, w.2.2))) :
    jointWorlds u' cols = (jointWorlds u cols).map (fun w => (f w.1, f w.2.1, w.2.2)) := by
  classical
  set R : Fin n × AggTok T K' → Fin n × AggTok T K → Prop := fun p' p =>
    p'.1 = p.1 ∧ p' ∈ tokCols u' cols ∧ p ∈ tokCols u cols with hRdef
  have hR : List.Forall₂ R (tokCols u' cols) (tokCols u cols) := by
    have h := tokCols_rel u u' cols hagg
    have hsub : ∀ {l' l}, List.Forall₂ (fun (p' : Fin n × AggTok T K') (p : Fin n × AggTok T K) =>
        p'.1 = p.1) l' l → l' ⊆ tokCols u' cols → l ⊆ tokCols u cols → List.Forall₂ R l' l := by
      intro l' l h hl' hl
      induction h with
      | nil => exact List.Forall₂.nil
      | cons hab _ ih =>
        exact List.Forall₂.cons ⟨hab, hl' List.mem_cons_self, hl List.mem_cons_self⟩
          (ih (fun _ hx => hl' (List.mem_cons_of_mem _ hx))
            (fun _ hx => hl (List.mem_cons_of_mem _ hx)))
    exact hsub h (fun _ h => h) (fun _ h => h)
  have hkR : ∀ a' a b' b, R a' a → R b' b →
      (a'.2.classKey = b'.2.classKey ↔ a.2.classKey = b.2.classKey) := by
    rintro a' a b' b ⟨ha1, ha', ha⟩ ⟨hb1, hb', hb⟩
    obtain ⟨hac, hau⟩ := mem_tokCols ha
    obtain ⟨-, hau'⟩ := mem_tokCols ha'
    obtain ⟨hbc, hbu⟩ := mem_tokCols hb
    obtain ⟨-, hbu'⟩ := mem_tokCols hb'
    rw [ha1] at hau'
    rw [hb1] at hbu'
    exact hkey a.1 hac b.1 hbc a.2 b.2 a'.2 b'.2 hau hbu hau' hbu'
  have hD := List.Forall₂.dedup_map_rel (g' := fun p : Fin n × AggTok T K' => p.2.classKey)
    (g := fun p : Fin n × AggTok T K => p.2.classKey) hR hkR
  have hfst : ∀ {l' l}, List.Forall₂ R l' l → l'.map Prod.fst = l.map Prod.fst := by
    intro l' l h
    induction h with
    | nil => rfl
    | cons hab _ ih => rw [List.map_cons, List.map_cons, hab.1, ih]
  unfold jointWorlds
  generalize ((tokCols u' cols).map (fun p => p.2.classKey)).dedup = D' at hD
  generalize ((tokCols u cols).map (fun p => p.2.classKey)).dedup = D at hD
  induction hD with
  | nil => simp
  | @cons φ' φ D' D hφ _ ih =>
    obtain ⟨a', a, hra, -, -, rfl, rfl⟩ := hφ
    rw [List.foldr_cons, List.foldr_cons]
    have hfind := List.Forall₂.find?_rel hR (P' := fun p => decide (p.2.classKey = a'.2.classKey))
      (P := fun p => decide (p.2.classKey = a.2.classKey))
      (fun q' q hq => decide_eq_decide.mpr (hkR q' q a' a hq hra))
    revert hfind
    generalize hF' : (tokCols u' cols).find? (fun p => decide (p.2.classKey = a'.2.classKey)) = o'
    generalize hF : (tokCols u cols).find? (fun p => decide (p.2.classKey = a.2.classKey)) = o
    intro hfind
    cases hfind with
    | none => exact ih
    | @some p₀' p₀ hp =>
      obtain ⟨h1, hp₀', hp₀⟩ := hp
      have hk₀ : p₀.2.classKey = a.2.classKey := by simpa using List.find?_some hF
      have hk₀' : p₀'.2.classKey = a'.2.classKey := by simpa using List.find?_some hF'
      obtain ⟨hc, hu⟩ := mem_tokCols hp₀
      obtain ⟨-, hu'⟩ := mem_tokCols hp₀'
      rw [h1] at hu'
      have hM : ((tokCols u' cols).filter (fun p => decide (p.2.classKey = a'.2.classKey))).map
            Prod.fst
          = ((tokCols u cols).filter (fun p => decide (p.2.classKey = p₀.2.classKey))).map
            Prod.fst := by
        rw [hk₀]
        exact hfst (List.Forall₂.filter_rel hR (fun q' q hq =>
          decide_eq_decide.mpr (hkR q' q a' a hq hra)))
      show Multiset.map _ (classWorlds u' _ p₀'.2 ×ˢ _) = Multiset.map _ (Multiset.map _ (
        classWorlds u _ p₀.2 ×ˢ _))
      rw [ih, hM, hclass p₀.1 hc p₀.2 p₀'.2 hu hu', ← hk₀, multiset_map_product_map,
        Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl (fun w _ => ?_)
      simp only [Function.comp, Prod.map, combineW, map_mul, map_add]

end ClassWorlds


/-! ## Families presented on both sides

What the joint reading of a row needs under a homomorphism, collected
over a set `S` of pairs of corresponding values (the target's and the
source's): that the two sides group them into families alike, and that
each family is *presented* – its flat values built from one listing on
each side, the two listings tie-block permuted (`ListingRel`), or its
nested values having corresponding worlds (`NestedValue.WCorr`). -/

section FamPres

variable {T K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

/-- **Two listings of a family's occurrences, related by a
homomorphism**: the target's is a tie-block permutation of the source's
pushed through `f`, occurrences swapped only where their rows read
alike. -/
structure ListingRel (f : K →+* K') (T : Type) where
  ρ : Type
  β : Type
  β' : Type
  L : List β
  ann : β → K
  str : β → ρ
  L' : List β'
  ann' : β' → K'
  str' : β' → ρ
  e : β → β'
  eqv : β' → β' → Prop
  heqv : ∀ {a b}, eqv a b → str' a = str' b
  hperm : TiePerm eqv L' (L.map e)
  hstr : ∀ b, str' (e b) = str b
  hann : ∀ b, ann' (e b) = f (ann b)

/-- A pair of flat values presented by a related pair of listings,
through the same readings. -/
def ListingRel.Member {f : K →+* K'} (D : ListingRel f T) (y' : AggTok T K')
    (y : AggTok T K) : Prop :=
  y.isNested = false ∧ y'.isNested = false ∧ ∃ (ok : List D.ρ → Prop) (val : List D.ρ → T),
    y.flatExpr.PresBy D.L D.ann D.str ok val ∧ y'.flatExpr.PresBy D.L' D.ann' D.str' ok val

/-- **The worlds of two nested values correspond under a homomorphism**:
both enumerations are images of one bag of indices, and at each index the
two worlds keep and leave out annotations related by `f`, read the same
inner values, and ask the same of what they keep. This is all a reading of
a nested value asks of its worlds – its admissibility, its value and its
weight – and it reads only the storey and the occurrences of the two
values, so a term over a nested column keeps it. -/
def NestedValue.WCorr [DecidableEq T] [DecidableEq K] [DecidableEq K'] (f : K →+* K')
    (b' : NestedValue T K') (b : NestedValue T K) : Prop :=
  ∃ (ι : Type) (I : Multiset ι) (φ : ι → NestedValue.World T K b.lev)
    (φ' : ι → NestedValue.World T K' b'.lev),
    b.worlds = I.map φ ∧ b'.worlds = I.map φ' ∧ ∀ i ∈ I,
      (φ' i).presentProd = f (φ i).presentProd ∧ (φ' i).absentSum = f (φ i).absentSum
      ∧ (φ' i).kept = (φ i).kept
      ∧ ((∀ m ∈ (φ' i).root, m.2.2 = true → NestInner.ok (φ' i).dec b'.lev m.1)
        ↔ (∀ m ∈ (φ i).root, m.2.2 = true → NestInner.ok (φ i).dec b.lev m.1))

/-- A pair of nested values with the same outer aggregate and
convention. -/
def NestMember (y' : AggTok T K') (y : AggTok T K) : Prop :=
  ∃ b b', y = .nest b ∧ y' = .nest b' ∧ b'.agg = b.agg ∧ b'.scalar = b.scalar

/-- **A set of corresponding values whose families are presented on both
sides.** -/
def FamPres [DecidableEq T] [DecidableEq K] [DecidableEq K'] (f : K →+* K')
    (S : AggTok T K' × AggTok T K → Prop) : Prop :=
  (∀ p q, S p → S q → (p.1.classKey = q.1.classKey ↔ p.2.classKey = q.2.classKey))
  ∧ ∀ p₀, S p₀ →
    (∃ D : ListingRel f T, ∀ q, S q → q.2.classKey = p₀.2.classKey → D.Member q.1 q.2)
    ∨ ((∃ b₀ b₀', p₀.2 = .nest b₀ ∧ p₀.1 = .nest b₀' ∧ NestedValue.WCorr f b₀' b₀)
      ∧ ∀ q, S q → q.2.classKey = p₀.2.classKey → NestMember q.1 q.2)

omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
/-- **Corresponding worlds are admissible alike**, for two values with the
same convention. -/
theorem NestedValue.WCorr.isWorld_iff [DecidableEq T] [DecidableEq K] [DecidableEq K']
    [CommSemiringWithMonus K] [CommSemiringWithMonus K'] {d d' : ℕ}
    {W : NestedValue.World T K d} {W' : NestedValue.World T K' d'}
    {c : NestedValue T K} {c' : NestedValue T K'} (hsc : c'.scalar = c.scalar)
    (hk : W'.kept = W.kept)
    (hok : (∀ m ∈ W'.root, m.2.2 = true → NestInner.ok W'.dec d' m.1)
      ↔ (∀ m ∈ W.root, m.2.2 = true → NestInner.ok W.dec d m.1)) :
    W'.IsWorld c' ↔ W.IsWorld c := by
  unfold NestedValue.World.IsWorld NestedValue.World.IsWorldWith
  rw [hk, hsc]
  exact and_congr Iff.rfl (and_congr hok Iff.rfl)

open Classical in
/-- **A nested family's worlds under a homomorphism.** If the
representatives' worlds correspond and every column of the family holds a
nested value with the same outer aggregate and convention on both sides,
the family's worlds correspond, the pair pushed through `f`. -/
theorem classWorlds_of_wcorr [ValueType T] [DecidableEq K] [DecidableEq K'] (f : K →+* K')
    {n : ℕ} (u : Tuple (GenValue T K) n) (u' : Tuple (GenValue T K') n) (M : List (Fin n))
    (a : NestedValue T K) (a' : NestedValue T K') (hw : NestedValue.WCorr f a' a)
    (hM : ∀ k ∈ M, ∃ b b', u k = Sum.inr (.nest b) ∧ u' k = Sum.inr (.nest b')
      ∧ b'.agg = b.agg ∧ b'.scalar = b.scalar) :
    classWorlds u' M (.nest a')
      = (classWorlds u M (.nest a)).map (fun w => (f w.1, f w.2.1, w.2.2)) := by
  obtain ⟨ι, I, φ, φ', h1, h2, hi⟩ := hw
  simp only [classWorlds]
  rw [h1, h2, Multiset.filter_map, Multiset.filter_map, Multiset.map_map, Multiset.map_map,
    Multiset.map_map]
  have hok : ∀ i ∈ I, nestOk u' M (φ' i) = nestOk u M (φ i) := by
    intro i hiI
    obtain ⟨-, -, hk, hr⟩ := hi i hiI
    rw [Bool.eq_iff_iff, nestOk_iff, nestOk_iff]
    refine forall₂_congr (fun k hkM => ?_)
    obtain ⟨b, b', hb, hb', -, hsc⟩ := hM k hkM
    constructor
    · intro hall b₁ hb₁
      rw [hb] at hb₁; cases hb₁
      exact (NestedValue.WCorr.isWorld_iff hsc hk hr).mp (hall b' hb')
    · intro hall b₁ hb₁
      rw [hb'] at hb₁; cases hb₁
      exact (NestedValue.WCorr.isWorld_iff hsc hk hr).mpr (hall b hb)
  rw [Multiset.filter_congr (p := (fun W => nestOk u' M W = true) ∘ φ')
    (q := (fun W => nestOk u M W = true) ∘ φ) (fun i hiI => by
      simp only [Function.comp_apply, hok i hiI])]
  refine Multiset.map_congr rfl (fun i hiI => ?_)
  obtain ⟨hp, ha, hk, -⟩ := hi i (Multiset.mem_of_mem_filter hiI)
  simp only [Function.comp_apply]
  refine Prod.ext hp (Prod.ext ha (funext fun k => ?_))
  dsimp only
  by_cases hkM : k ∈ M
  · rw [ite_eq_left hkM, ite_eq_left hkM]
    obtain ⟨b, b', hb, hb', hagg, -⟩ := hM k hkM
    rw [hb, hb']
    show some (b'.agg (φ' i).kept) = some (b.agg (φ i).kept)
    rw [hagg, hk]
  · rw [ite_eq_right hkM, ite_eq_right hkM]

theorem FamPres.mono [DecidableEq T] [DecidableEq K] [DecidableEq K'] {f : K →+* K'}
    {S S' : AggTok T K' × AggTok T K → Prop}
    (h : FamPres f S) (hS : ∀ p, S' p → S p) : FamPres f S' :=
  ⟨fun p q hp hq => h.1 p q (hS p hp) (hS q hq), fun p₀ hp₀ =>
    (h.2 p₀ (hS p₀ hp₀)).imp
      (fun ⟨D, hD⟩ => ⟨D, fun q hq hk => hD q (hS q hq) hk⟩)
      (fun ⟨hO, hm⟩ => ⟨hO, fun q hq hk => hm q (hS q hq) hk⟩)⟩

namespace Multiset

/-- **Related bags are listed by related lists.** -/
theorem exists_forall₂_of_rel {α β : Type} {R : α → β → Prop} {s : Multiset α}
    {t : Multiset β} (h : Multiset.Rel R s t) :
    ∃ (l : List α) (l' : List β), s = (l : Multiset α) ∧ t = (l' : Multiset β)
      ∧ List.Forall₂ R l l' := by
  induction h with
  | zero => exact ⟨[], [], rfl, rfl, List.Forall₂.nil⟩
  | @cons a b s t hab _ ih =>
    obtain ⟨l, l', rfl, rfl, hl⟩ := ih
    exact ⟨a :: l, b :: l', rfl, rfl, List.Forall₂.cons hab hl⟩

/-- Related lists list related bags. -/
theorem rel_of_forall₂ {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : Multiset.Rel R (l : Multiset α) (l' : Multiset β) := by
  induction h with
  | nil => exact Multiset.Rel.zero
  | @cons a b l l' hab _ ih =>
    rw [← Multiset.cons_coe, ← Multiset.cons_coe]
    exact Multiset.Rel.cons hab ih

/-- Related lists are the two sides of one list of pairs. -/
theorem exists_zip_of_forall₂ {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') :
    ∃ u : List (α × β), u.map Prod.fst = l ∧ u.map Prod.snd = l' ∧ ∀ p ∈ u, R p.1 p.2 := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, fun p hp => absurd hp List.not_mem_nil⟩
  | @cons a b l l' hab _ ih =>
    obtain ⟨u, h1, h2, h3⟩ := ih
    refine ⟨(a, b) :: u, by simp [h1], by simp [h2], fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hab
    · exact h3 p hp

end Multiset


omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
/-- The aggregate column of a row, with its value, is in its token
columns. -/
theorem mem_tokCols_of {n : ℕ} {u : Tuple (GenValue T K) n} {cols : List (Fin n)} {k : Fin n}
    (hk : k ∈ cols) {x : AggTok T K} (hx : u k = Sum.inr x) : (k, x) ∈ tokCols u cols := by
  unfold tokCols
  exact List.mem_filterMap.mpr ⟨k, hk, by rw [hx]⟩

open Classical in
/-- **The joint worlds of a row whose families are presented on both
sides correspond.** -/
theorem jointWorlds_of_famPres [ValueType T] [DecidableEq K] [DecidableEq K']
    (f : K →+* K') {n : ℕ} (u : Tuple (GenValue T K) n) (u' : Tuple (GenValue T K') n)
    (cols : List (Fin n))
    (hagg : ∀ k ∈ cols, (∃ x, u k = Sum.inr x) ↔ (∃ x', u' k = Sum.inr x'))
    (hF : FamPres f (fun p => ∃ k ∈ cols, u' k = Sum.inr p.1 ∧ u k = Sum.inr p.2)) :
    jointWorlds u' cols = (jointWorlds u cols).map (fun w => (f w.1, f w.2.1, w.2.2)) := by
  refine jointWorlds_hom f u u' cols hagg ?_ ?_
  · intro k hk l hl x y x' y' hx hy hx' hy'
    exact hF.1 (x', x) (y', y) ⟨k, hk, hx', hx⟩ ⟨l, hl, hy', hy⟩
  · intro k₀ hk₀ x x' hx hx'
    set M := ((tokCols u cols).filter (fun p => decide (p.2.classKey = x.classKey))).map
      Prod.fst with hMdef
    have hmem : ∀ k ∈ M, k ∈ cols ∧ ∃ y y', u k = Sum.inr y ∧ u' k = Sum.inr y'
        ∧ y.classKey = x.classKey := by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      obtain ⟨hp, hpk⟩ := List.mem_filter.mp hp
      obtain ⟨hc, hu⟩ := mem_tokCols hp
      obtain ⟨y', hy'⟩ := (hagg p.1 hc).mp ⟨p.2, hu⟩
      exact ⟨hc, p.2, y', hu, hy', by simpa using hpk⟩
    rcases hF.2 (x', x) ⟨k₀, hk₀, hx', hx⟩ with ⟨D, hD⟩ | hrest
    · -- a flat family
      have hmemb : ∀ k ∈ M, ∃ okv : (List D.ρ → Prop) × (List D.ρ → T), ∃ y y',
          u k = Sum.inr y ∧ u' k = Sum.inr y'
          ∧ y.flatExpr.PresBy D.L D.ann D.str okv.1 okv.2
          ∧ y'.flatExpr.PresBy D.L' D.ann' D.str' okv.1 okv.2 := by
        intro k hk
        obtain ⟨hc, y, y', hy, hy', hky⟩ := hmem k hk
        obtain ⟨-, -, ok, val, hb, hb'⟩ := hD (y', y) ⟨k, hc, hy', hy⟩ hky
        exact ⟨(ok, val), y, y', hy, hy', hb, hb'⟩
      obtain ⟨hn₀, hn₀', ok₀, val₀, hb₀, hb₀'⟩ := hD (x', x) ⟨k₀, hk₀, hx', hx⟩ rfl
      let okv : Fin n → (List D.ρ → Prop) × (List D.ρ → T) := fun k =>
        if h : ∃ okv : (List D.ρ → Prop) × (List D.ρ → T), ∃ y y',
            u k = Sum.inr y ∧ u' k = Sum.inr y'
            ∧ y.flatExpr.PresBy D.L D.ann D.str okv.1 okv.2
            ∧ y'.flatExpr.PresBy D.L' D.ann' D.str' okv.1 okv.2
        then Classical.choose h else (ok₀, val₀)
      have hsp : ∀ k ∈ M, ∃ y y', u k = Sum.inr y ∧ u' k = Sum.inr y'
          ∧ y.flatExpr.PresBy D.L D.ann D.str (okv k).1 (okv k).2
          ∧ y'.flatExpr.PresBy D.L' D.ann' D.str' (okv k).1 (okv k).2 := by
        intro k hk
        have h := hmemb k hk
        simp only [okv, dite_eq_left h]
        exact Classical.choose_spec h
      exact classWorlds_hom f u u' M D.L D.ann D.str D.L' D.ann' D.str' D.e D.heqv D.hperm
        D.hstr D.hann (fun k => (okv k).1) (fun k => (okv k).2)
        (fun k hk => by
          obtain ⟨y, y', hy, -, hb, -⟩ := hsp k hk
          exact ⟨y, hy, hb⟩)
        (fun k hk => by
          obtain ⟨y, y', -, hy', -, hb'⟩ := hsp k hk
          exact ⟨y', hy', hb'⟩)
        x hn₀ ok₀ val₀ hb₀ x' hn₀' hb₀'
    · -- a nested family
      obtain ⟨⟨b₀, b₀', hb₀, hb₀', hw⟩, hN⟩ := hrest
      dsimp only at hb₀ hb₀'
      subst hb₀ hb₀'
      refine classWorlds_of_wcorr f u u' M b₀ b₀' hw (fun k hk => ?_)
      obtain ⟨hc, y, y', hy, hy', hky⟩ := hmem k hk
      obtain ⟨b, b', rfl, rfl, hagg', hsc⟩ := hN (y', y) ⟨k, hc, hy', hy⟩ hky
      exact ⟨b, b', hy, hy', hagg', hsc⟩

/-! ### Closure under terms

A term over an aggregate column (`AggTok.postcompTerm`) composes the
value's outer function and keeps its family: the same occurrences, the
same group key, a family identifier recording the term. So it stays in
its class, and a presented family stays presented. -/

variable [ValueType T]

omit [CommSemiringWithMonus K'] in
theorem AggTok.classKey_postcompTerm (t : TermIn T 1 0) (x : AggTok T K) :
    (x.postcompTerm t).classKey = x.classKey := by
  cases x <;> simp [AggTok.postcompTerm, AggTok.classKey, AggTok.postcomp, AggTok.setFam,
    AggTok.annList, AggTok.fam, NestedValue.postcomp, AggExpr.annList, AggExpr.postcomp]

omit [ValueType T] [CommSemiringWithMonus K'] in
theorem AggTok.classKey_postcomp (gf : T → T) (x : AggTok T K) :
    (x.postcomp gf).classKey = x.classKey := by
  cases x <;> simp [AggTok.classKey, AggTok.postcomp, AggTok.annList, AggTok.fam,
    NestedValue.postcomp, AggExpr.annList, AggExpr.postcomp]

omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
theorem AggTok.isNested_postcompTerm (t : TermIn T 1 0) (x : AggTok T K) :
    (x.postcompTerm t).isNested = x.isNested := by
  cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
/-- A function keeps a value presented, reading its value through it. -/
theorem AggExpr.PresBy.postcomp {ρ β : Type} {x : AggTok T K} (hx : x.isNested = false)
    {L : List β} {ann : β → K} {str : β → ρ} {ok : List ρ → Prop} {val : List ρ → T}
    (gf : T → T) (hP : x.flatExpr.PresBy L ann str ok val) :
    (x.postcomp gf).flatExpr.PresBy L ann str ok (fun s => gf (val s)) := by
  obtain ⟨h, ha, hw, hv⟩ := hP
  cases x with
  | nest a => simp [AggTok.isNested] at hx
  | tok a => exact ⟨h, ha, hw, fun W => by show _ = gf (val _); rw [← hv W]; rfl⟩
  | expr a => exact ⟨h, ha, hw, fun W => by show _ = gf (val _); rw [← hv W]; rfl⟩

omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
/-- A term keeps a value presented, reading its value through the term. -/
theorem AggExpr.PresBy.postcompTerm {ρ β : Type} {x : AggTok T K} (hx : x.isNested = false)
    {L : List β} {ann : β → K} {str : β → ρ} {ok : List ρ → Prop} {val : List ρ → T}
    (t : TermIn T 1 0) (hP : x.flatExpr.PresBy L ann str ok val) :
    (x.postcompTerm t).flatExpr.PresBy L ann str ok (fun s => t.unary (val s)) := by
  obtain ⟨h, ha, hw, hv⟩ := hP
  cases x with
  | nest a => simp [AggTok.isNested] at hx
  | tok a => exact ⟨h, ha, hw, fun W => by show _ = t.unary (val _); rw [← hv W]; rfl⟩
  | expr a => exact ⟨h, ha, hw, fun W => by show _ = t.unary (val _); rw [← hv W]; rfl⟩

/-- **The closure of a set of corresponding values under terms**, taken
on both sides alike. -/
inductive PCl (S : AggTok T K' × AggTok T K → Prop) : AggTok T K' × AggTok T K → Prop
  | base {p} : S p → PCl S p
  | step {p} (t : TermIn T 1 0) : PCl S p → PCl S (p.1.postcompTerm t, p.2.postcompTerm t)
  | stepF {p} (gf : T → T) : PCl S p → PCl S (p.1.postcomp gf, p.2.postcomp gf)

theorem PCl.exists_base {S : AggTok T K' × AggTok T K → Prop} {p} (hp : PCl S p) :
    ∃ q, S q ∧ p.1.classKey = q.1.classKey ∧ p.2.classKey = q.2.classKey := by
  induction hp with
  | base h => exact ⟨_, h, rfl, rfl⟩
  | step t _ ih =>
    obtain ⟨q, hq, h1, h2⟩ := ih
    exact ⟨q, hq, by rw [AggTok.classKey_postcompTerm, h1],
      by rw [AggTok.classKey_postcompTerm, h2]⟩
  | stepF gf _ ih =>
    obtain ⟨q, hq, h1, h2⟩ := ih
    exact ⟨q, hq, by rw [AggTok.classKey_postcomp, h1], by rw [AggTok.classKey_postcomp, h2]⟩

omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
theorem PCl.mono {S S' : AggTok T K' × AggTok T K → Prop} (hS : ∀ p, S p → S' p) {p}
    (hp : PCl S p) : PCl S' p := by
  induction hp with
  | base h => exact PCl.base (hS _ h)
  | step t _ ih => exact PCl.step t ih
  | stepF gf _ ih => exact PCl.stepF gf ih

omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
/-- **A term over a nested pair with corresponding worlds keeps them**:
the worlds of a nested value read only its storey and its occurrences,
which a term over it leaves alone. -/
theorem PCl.wcorr [DecidableEq T] [DecidableEq K] [DecidableEq K'] [CommSemiringWithMonus K]
    [CommSemiringWithMonus K'] {f : K →+* K'} {S : AggTok T K' × AggTok T K → Prop}
    (hS : ∀ p, S p → p.2.isNested = true →
      ∃ b₀ b₀', p.2 = .nest b₀ ∧ p.1 = .nest b₀' ∧ NestedValue.WCorr f b₀' b₀) {p}
    (hp : PCl S p) (hn : p.2.isNested = true) :
    ∃ b₀ b₀', p.2 = .nest b₀ ∧ p.1 = .nest b₀' ∧ NestedValue.WCorr f b₀' b₀ := by
  induction hp with
  | base h => exact hS _ h hn
  | @step r t hr ih =>
    rw [AggTok.isNested_postcompTerm] at hn
    obtain ⟨b, b', h₁, h₂, hw⟩ := ih hn
    obtain ⟨r₁, r₂⟩ := r
    dsimp only at h₁ h₂ ⊢
    subst h₁ h₂
    exact ⟨_, _, rfl, rfl, hw⟩
  | @stepF r gf hr ih =>
    rw [AggTok.isNested_postcomp] at hn
    obtain ⟨b, b', h₁, h₂, hw⟩ := ih hn
    obtain ⟨r₁, r₂⟩ := r
    dsimp only at h₁ h₂ ⊢
    subst h₁ h₂
    exact ⟨_, _, rfl, rfl, hw⟩

/-- **Presented families stay presented under terms.** -/
theorem FamPres.pcl [DecidableEq T] [DecidableEq K] [DecidableEq K'] {f : K →+* K'}
    {S : AggTok T K' × AggTok T K → Prop} (h : FamPres f S) :
    FamPres f (PCl S) := by
  refine ⟨fun p q hp hq => ?_, fun p₀ hp₀ => ?_⟩
  · obtain ⟨p', hp', h1, h2⟩ := hp.exists_base
    obtain ⟨q', hq', h3, h4⟩ := hq.exists_base
    rw [h1, h2, h3, h4]
    exact h.1 p' q' hp' hq'
  · obtain ⟨p', hp', -, h2⟩ := hp₀.exists_base
    rcases h.2 p' hp' with ⟨D, hD⟩ | ⟨⟨b₀, b₀', hb₀, -, -⟩, hN⟩
    · refine Or.inl ⟨D, fun q hq hk => ?_⟩
      induction hq with
      | base hb => exact hD _ hb (hk.trans h2)
      | @step r t hr ih =>
        rw [AggTok.classKey_postcompTerm] at hk
        obtain ⟨hn, hn', ok, val, hP, hP'⟩ := ih hk
        exact ⟨by rw [AggTok.isNested_postcompTerm]; exact hn,
          by rw [AggTok.isNested_postcompTerm]; exact hn', ok, fun s => t.unary (val s),
          hP.postcompTerm hn t, hP'.postcompTerm hn' t⟩
      | @stepF r gf hr ih =>
        rw [AggTok.classKey_postcomp] at hk
        obtain ⟨hn, hn', ok, val, hP, hP'⟩ := ih hk
        exact ⟨by rw [AggTok.isNested_postcomp]; exact hn,
          by rw [AggTok.isNested_postcomp]; exact hn', ok, fun s => gf (val s),
          hP.postcomp hn gf, hP'.postcomp hn' gf⟩
    · -- the class holds nested values only, since its key says so
      have hnest : p₀.2.isNested = true := by
        have hk : p₀.2.classKey.2.2.isSome = p'.2.classKey.2.2.isSome := by rw [h2]
        rw [hb₀] at hk
        cases hx : p₀.2 with
        | nest a => rfl
        | tok a => rw [hx] at hk; exact absurd hk (by simp [AggTok.classKey])
        | expr a => rw [hx] at hk; exact absurd hk (by simp [AggTok.classKey])
      refine Or.inr ⟨PCl.wcorr (fun p hp hn => ?_) hp₀ hnest, fun q hq hk => ?_⟩
      · rcases h.2 p hp with ⟨D, hD⟩ | ⟨hw, -⟩
        · exact absurd (hD p hp rfl).1 (by rw [hn]; decide)
        · exact hw
      · induction hq with
        | base hb => exact hN _ hb (hk.trans h2)
        | @step r t hr ih =>
          rw [AggTok.classKey_postcompTerm] at hk
          obtain ⟨b, b', h₁, h₂, hagg, hsc⟩ := ih hk
          obtain ⟨r₁, r₂⟩ := r
          dsimp only at h₁ h₂ ⊢
          subst h₁ h₂
          refine ⟨{ b.postcomp t.unary with fam := (AggTok.nest b).fam.addTerm t },
            { b'.postcomp t.unary with fam := (AggTok.nest b').fam.addTerm t }, rfl, rfl,
            ?_, hsc⟩
          show (fun s => t.unary (b'.agg s)) = (fun s => t.unary (b.agg s))
          rw [hagg]
        | @stepF r gf hr ih =>
          rw [AggTok.classKey_postcomp] at hk
          obtain ⟨b, b', h₁, h₂, hagg, hsc⟩ := ih hk
          obtain ⟨r₁, r₂⟩ := r
          dsimp only at h₁ h₂ ⊢
          subst h₁ h₂
          refine ⟨b.postcomp gf, b'.postcomp gf, rfl, rfl, ?_, hsc⟩
          show (fun s => gf (b'.agg s)) = (fun s => gf (b.agg s))
          rw [hagg]

/-! ### The operator a family records -/

/-- The label of the operator a family identifier records. -/
def FamId.lab : FamId T → ℕ
  | .mk l _ _ _ _ => l

/-- The label of the operator that built an aggregate value. -/
def AggTok.lab (x : AggTok T K) : ℕ := x.fam.lab

omit [ValueType T] in
/-- **A value presented by its own occurrences.** Two flat values with
the same leaves, whose families differ by a tie-block permutation – the
target's a permutation of the source's pushed through `f`, occurrences
swapped only where they carry the same values and flags – are presented
by those families. -/
theorem ListingRel.exists_of_tie (f : K →+* K') {q : ℕ}
    {occs : List ((Fin q → T) × K × (Fin q → Bool) × (Fin q → Bool))}
    {occs' : List ((Fin q → T) × K' × (Fin q → Bool) × (Fin q → Bool))}
    (aggs : Fin q → SeqAggFunc T) (sc : Fin q → Bool) (g : (Fin q → T) → T)
    (htie : TiePerm (fun z z' => z.1 = z'.1 ∧ z.2.2 = z'.2.2) occs'
      (occs.map (fun z => (z.1, f z.2.1, z.2.2)))) :
    ∃ D : ListingRel f T, ∀ (x : AggTok T K) (x' : AggTok T K') (φ φ' : FamId T),
      x.isNested = false → x'.isNested = false →
      x.flatExpr = ⟨q, occs, aggs, sc, g, φ, []⟩
        → x'.flatExpr = ⟨q, occs', aggs, sc, g, φ', []⟩ →
      D.Member x' x := by
  let sp : LeafSpec ((Fin q → T) × (Fin q → Bool) × (Fin q → Bool)) T :=
    ⟨q, fun r => r.1, fun r => r.2.1, fun r => r.2.2, aggs, sc, g⟩
  refine ⟨ListingRel.mk (ρ := (Fin q → T) × (Fin q → Bool) × (Fin q → Bool))
    (β := (Fin q → T) × K × (Fin q → Bool) × (Fin q → Bool))
    (β' := (Fin q → T) × K' × (Fin q → Bool) × (Fin q → Bool))
    (L := occs) (ann := fun z => z.2.1) (str := fun z => (z.1, z.2.2))
    (L' := occs') (ann' := fun z => z.2.1) (str' := fun z => (z.1, z.2.2))
    (e := fun z => (z.1, f z.2.1, z.2.2))
    (eqv := fun z z' => z.1 = z'.1 ∧ z.2.2 = z'.2.2)
    (heqv := fun h => Prod.ext h.1 h.2) (hperm := htie) (hstr := fun _ => rfl)
    (hann := fun _ => rfl), ?_⟩
  intro x x' φ φ' hn hn' hx hx'
  refine ⟨hn, hn', sp.okL, sp.valL, sp.presBy_build _ _ _ (φ := φ) ?_,
    sp.presBy_build _ _ _ (φ := φ') ?_⟩
  · rw [hx]; simp [LeafSpec.build, sp]
  · rw [hx']; simp [LeafSpec.build, sp]

omit [ValueType T] in
/-- **The values built from one group, presented by it.** A group's rows,
listed on the two sides by a tie-block permutation of the pushed-forward
listing, present every value a `LeafSpec` builds from them. -/
theorem ListingRel.exists_group (f : K →+* K') {m : ℕ} (U : List (AnnotatedTuple T K m))
    (U' : List (AnnotatedTuple T K' m))
    (hp : TiePerm (fun p q : AnnotatedTuple T K' m => p.fst = q.fst)
      (U.map (fun p => ((p.fst, f p.snd) : AnnotatedTuple T K' m))) U') :
    ∃ D : ListingRel f T, ∀ (x : AggTok T K) (x' : AggTok T K') (sp : LeafSpec (Tuple T m) T)
      (φ φ' : FamId T), x.isNested = false → x'.isNested = false →
      x.flatExpr = sp.build U Prod.snd Prod.fst φ →
      x'.flatExpr = sp.build U' Prod.snd Prod.fst φ' → D.Member x' x := by
  refine ⟨ListingRel.mk (ρ := Tuple T m) (β := AnnotatedTuple T K m)
    (β' := AnnotatedTuple T K' m) (L := U) (ann := Prod.snd) (str := Prod.fst)
    (L' := U') (ann' := Prod.snd) (str' := Prod.fst)
    (e := fun p => ((p.fst, f p.snd) : AnnotatedTuple T K' m))
    (eqv := fun p q => p.fst = q.fst) (heqv := id)
    (hperm := TiePerm.symm (fun h => h.symm) hp) (hstr := fun _ => rfl)
    (hann := fun _ => rfl), ?_⟩
  intro x x' sp φ φ' hn hn' hx hx'
  exact ⟨hn, hn', sp.okL, sp.valL, sp.presBy_build _ _ _ hx, sp.presBy_build _ _ _ hx'⟩

end FamPres

/-! ## The operators' labels

The hom commutation reads several values of one family in one world, so
what it asks of a query is that two operators building values never
share a label (`AggQueryIn.labelsDistinct`): values of different operators
are then in different families, and an identifier determines its value
across every evaluation the query performs
(`AggQueryIn.builds_coherent`). -/

section Labels

variable {T : Type}

/-- **An operator's label, where it builds a column**: an aggregation with
no aggregate builds no value, so its label is not one of a value. -/
def labCons {α : Type} (w : ℕ) (lab : α) (L : List α) : List α :=
  if w = 0 then L else lab :: L

theorem labCons_of_ne {α : Type} {w : ℕ} (h : w ≠ 0) (lab : α) (L : List α) :
    labCons w lab L = lab :: L := by
  simp [labCons, h]

theorem labCons_zero {α : Type} (lab : α) (L : List α) : labCons 0 lab L = L := by
  simp [labCons]

theorem labCons_nodup {α : Type} {w : ℕ} {lab : α} {L : List α} (h : (labCons w lab L).Nodup) :
    L.Nodup := by
  unfold labCons at h
  split at h
  · exact h
  · exact (List.nodup_cons.mp h).2

theorem mem_labCons_of_mem {α : Type} {w : ℕ} {lab : α} {L : List α} {x : α} (h : x ∈ L) :
    x ∈ labCons w lab L := by
  unfold labCons
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

/-- **The labels of the operators that build aggregate values**, an
aggregation with no aggregate building none (`labCons`). -/
def AggQueryIn.labels : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → List ℕ
  | _, _, _, _, .Rel _ _ => []
  | _, _, _, _, .Hole _ _ _ => []
  | _, _, _, _, .Param _ _ => []
  | _, _, _, _, .Empty => []
  | _, _, _, _, .Proj _ q => q.labels
  | _, _, _, _, .Sel _ q _ => q.labels
  | _, _, _, _, .Prod q₁ q₂ => q₁.labels ++ q₂.labels
  | _, _, _, _, .Apply q₁ q₂ => q₁.labels ++ q₂.labels
  | _, _, _, _, .Sum q₁ q₂ => q₁.labels ++ q₂.labels
  | _, _, _, _, .Dedup q => q.labels
  | _, _, _, _, .Diff q₁ q₂ => q₁.labels ++ q₂.labels
  | _, _, _, _, .Explode _ _ q => q.labels
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.labels ++ q₁.labels
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.labels ++ q₁.labels
  | _, _, _, _, @AggQueryIn.Gamma _ _ _ _ n₂ lab _ _ _ _ q _ _ => labCons n₂ lab q.labels
  | _, _, _, _, @AggQueryIn.GammaScalar _ _ _ n₂ lab _ _ _ q _ => labCons n₂ lab q.labels
  | _, _, _, _, @AggQueryIn.GammaNest _ _ _ _ _ lab _ _ _ _ _ q => lab :: q.labels
  | _, _, _, _, .ProvSum _ _ _ q => q.labels
  | _, _, _, _, .Retag _ q => q.labels
  | _, _, _, _, @AggQueryIn.GammaTok _ _ _ _ n₂ _ lab _ _ _ _ _ _ q _ => labCons n₂ lab q.labels
  | _, _, _, _, @AggQueryIn.Win _ _ _ _ _ _ lab _ _ _ _ _ _ _ _ q _ _ _ => lab :: q.labels
  | _, _, _, _, @AggQueryIn.WinExpr _ _ _ _ _ _ lab _ _ _ _ _ _ _ _ _ q _ => lab :: q.labels

/-- **No two operators building aggregate values share a label.** -/
def AggQueryIn.labelsDistinct {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) : Prop :=
  q.labels.Nodup

end Labels

/-! ## An expression's world statistics under a homomorphism -/

section WorldStats

variable {T K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

open Classical in
/-- **The world statistics read off the subfamilies of the listing.** -/
theorem AggExpr.worldStats_eq_subWorlds (e : AggExpr T K) :
    e.worldStats = (subWorlds (fun z => z.2.1) e.occs).map
      (fun w => (w.1, w.2.1, e.valSeq w.2.2, decide (e.okSeq w.2.2))) := by
  unfold AggExpr.worldStats
  rw [← univ_map_eq_subWorlds, Multiset.map_map]
  refine Multiset.map_congr rfl (fun W _ => ?_)
  simp only [Function.comp, AggExpr.valOn_eq_valSeq]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  exact decide_eq_decide.mpr (AggExpr.isWorld_iff_okSeq e W)

/-- **The world statistics of an expression pushed through a
homomorphism**: the products and sums pushed through it, the values and
world conditions unchanged. -/
theorem AggExpr.worldStats_mapAnn (f : K →+* K') (e : AggExpr T K) :
    (e.mapAnn f).worldStats = e.worldStats.map (fun z => (f z.1, f z.2.1, z.2.2.1, z.2.2.2)) := by
  obtain ⟨q, occs, aggs, sc, g, φ⟩ := e
  rw [AggExpr.worldStats_eq_subWorlds, AggExpr.worldStats_eq_subWorlds]
  dsimp only [AggExpr.mapAnn]
  have hsw := subWorlds_map f
    (fun z : (Fin q → T) × K × (Fin q → Bool) × (Fin q → Bool) => z.2.1)
    (fun z : (Fin q → T) × K' × (Fin q → Bool) × (Fin q → Bool) => z.2.1)
    (fun o => (o.1, f o.2.1, o.2.2)) (fun _ => rfl) occs
  erw [hsw]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun w _ => ?_)
  simp only [Function.comp]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · show g _ = g _
    simp only [List.filter_map, List.map_map]
    rfl
  · refine decide_eq_decide.mpr ?_
    simp only [AggExpr.okSeq, List.mem_map, exists_exists_and_eq_and]

end WorldStats
