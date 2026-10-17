/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryBridges
import Provenance.SubWorlds

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
    sp.aggs, sp.scalar, sp.g, φ⟩

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
If every column of `M` holds a value built from the listing `L` (each by
its own `LeafSpec`), and so does the value `x₀` the family is listed by,
then the family's worlds are the subfamilies of `L`, each read through
the rows it selects. -/
theorem classWorlds_presented {ρ β : Type} {n : ℕ} (u : Tuple (GenValue T K) n)
    (M : List (Fin n)) (L : List β) (ann : β → K) (str : β → ρ) (sp : Fin n → LeafSpec ρ T)
    (hM : ∀ k ∈ M, ∃ y φ, u k = Sum.inr y ∧ y.flatExpr = (sp k).build L ann str φ)
    (x₀ : AggTok T K) (hx₀ : x₀.isNested = false) (sp₀ : LeafSpec ρ T) (φ₀ : FamId T)
    (hx₀b : x₀.flatExpr = sp₀.build L ann str φ₀) :
    classWorlds u M x₀
      = ((((subWorlds ann L).map (fun w => (w.1, w.2.1, w.2.2.map str))).filter
          (fun w => ∀ k ∈ M, (sp k).okL w.2.2)).map
          (fun w => (w.1, w.2.1, fun k => if k ∈ M then some ((sp k).valL w.2.2) else none))) := by
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
  have h₀ : L.length = x₀.flatExpr.occs.length := by rw [hx₀b]; simp [LeafSpec.build]
  rw [hdef, Finset.filter_val, univ_val_reindex h₀, Multiset.filter_map, Multiset.map_map,
    ← univ_map_eq_subWorlds ann L, Multiset.map_map, Multiset.filter_map, Multiset.map_map]
  have hcol : ∀ k ∈ M, ∀ W' : Finset (Fin L.length), ∃ y, u k = Sum.inr y ∧
      (y.flatExpr.IsWorld (trW (a := x₀.flatExpr.occs.length) (W'.map (finCongr h₀).toEmbedding))
        ↔ (sp k).okL ((Having.seqOf L W').map str))
      ∧ y.flatExpr.valOn (trW (a := x₀.flatExpr.occs.length) (W'.map (finCongr h₀).toEmbedding))
        = (sp k).valL ((Having.seqOf L W').map str) := by
    intro k hk W'
    obtain ⟨y, φ, hy, hyb⟩ := hM k hk
    have hk' : L.length = y.flatExpr.occs.length := by rw [hyb]; simp [LeafSpec.build]
    refine ⟨y, hy, ?_, ?_⟩
    · rw [trW_map h₀ hk']
      exact (sp k).isWorld_build L ann str hyb hk' W'
    · rw [trW_map h₀ hk']
      exact (sp k).valOn_build L ann str hyb hk' W'
  rw [Multiset.filter_congr (q := fun W' : Finset (Fin L.length) =>
    ∀ k ∈ M, (sp k).okL ((Having.seqOf L W').map str))]
  · refine Multiset.map_congr rfl (fun W' _ => ?_)
    simp only [Function.comp]
    refine Prod.ext ?_ (Prod.ext ?_ (funext fun k => ?_))
    · rw [Finset.prod_map]
      exact Finset.prod_congr rfl (fun i _ => sp₀.anns_build L ann str hx₀b h₀ i)
    · rw [compl_map_finCongr, Finset.sum_map]
      exact Finset.sum_congr rfl (fun i _ => sp₀.anns_build L ann str hx₀b h₀ i)
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
sides the family's values are built by the same `LeafSpec`s from two
listings, the second a tie-block permutation of the first pushed through
`f` – occurrences swapped only where their rows read alike. Then the
family's worlds correspond, annotations pushed through `f` and every
value unchanged: the values of the family are reordered together. -/
theorem classWorlds_hom {K' : Type} [CommSemiringWithMonus K'] (f : K →+* K')
    {ρ β β' : Type} {n : ℕ} (u : Tuple (GenValue T K) n) (u' : Tuple (GenValue T K') n)
    (M : List (Fin n)) (L : List β) (ann : β → K) (str : β → ρ)
    (L' : List β') (ann' : β' → K') (str' : β' → ρ) (e : β → β')
    {eqv : β' → β' → Prop} (heqv : ∀ {a b}, eqv a b → str' a = str' b)
    (hperm : TiePerm eqv L' (L.map e))
    (hstr : ∀ b, str' (e b) = str b) (hann : ∀ b, ann' (e b) = f (ann b))
    (sp : Fin n → LeafSpec ρ T)
    (hM : ∀ k ∈ M, ∃ y φ, u k = Sum.inr y ∧ y.flatExpr = (sp k).build L ann str φ)
    (hM' : ∀ k ∈ M, ∃ y φ, u' k = Sum.inr y ∧ y.flatExpr = (sp k).build L' ann' str' φ)
    (x₀ : AggTok T K) (hx₀ : x₀.isNested = false) (sp₀ : LeafSpec ρ T) (φ₀ : FamId T)
    (hx₀b : x₀.flatExpr = sp₀.build L ann str φ₀)
    (x₀' : AggTok T K') (hx₀' : x₀'.isNested = false) (φ₀' : FamId T)
    (hx₀b' : x₀'.flatExpr = sp₀.build L' ann' str' φ₀') :
    classWorlds u' M x₀' = (classWorlds u M x₀).map (fun w => (f w.1, f w.2.1, w.2.2)) := by
  rw [classWorlds_presented u M L ann str sp hM x₀ hx₀ sp₀ φ₀ hx₀b,
    classWorlds_presented u' M L' ann' str' sp hM' x₀' hx₀' sp₀ φ₀' hx₀b',
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
        = (classWorlds u (((tokCols u cols).filter (fun p => decide (p.2.classKey = x.classKey))).map
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
          (ih (fun _ hx => hl' (List.mem_cons_of_mem _ hx)) (fun _ hx => hl (List.mem_cons_of_mem _ hx)))
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

/-! ## The worlds of a nested family, read off its occurrences' statistics

A world of a nested value is weighed by the product of what it keeps and
the sum of what it leaves out, the monus being taken once over every
family a selection reads. So what the joint reading asks of a nested
family is, per world, the *pair* – not the weight `World.ann` folds it
into – together with the bag of inner values it reads and whether it is a
world. Each of the four is accumulated occurrence by occurrence
(`summaryU`), so the worlds' data run over the occurrences' statistics
(`foldr_addOcc_map_summaryU`), and those are the inner value's
`AggExpr.worldStats` and the occurrence's annotation (`occStatsU_eq`). -/

namespace NestedValue

section Unsplit

variable {T K : Type} [CommSemiringWithMonus K]

/-- What one decision about an occurrence contributes: to the product of
what is kept, to the sum of what is left out, the inner value it reads if
present, and whether it is a world of its own expression. -/
def statOfDecU (d : WorldOcc T K) : K × K × Option T × Bool :=
  ((if d.present = true then d.occ.2 else 1) * ∏ j ∈ d.sub, d.occ.1.anns j,
    (if d.present = true then 0 else d.occ.2) + ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j,
    if d.present = true then some (d.occ.1.valOn d.sub) else none,
    if d.present = true then decide (d.occ.1.IsWorld d.sub) else true)

/-- The data available at one occurrence, unsplit. -/
def occStatsU (o : AggExpr T K × K) : Multiset (K × K × Option T × Bool) :=
  (decisions o).map statOfDecU

/-- One more occurrence, on the data. -/
def addChoiceU (st : Multiset (K × K × Option T × Bool))
    (cs : Multiset (Multiset T × K × K × Bool)) : Multiset (Multiset T × K × K × Bool) :=
  st.bind (fun z => cs.map (fun c =>
    ((match z.2.2.1 with | none => c.1 | some v => v ::ₘ c.1),
      z.1 * c.2.1, z.2.1 + c.2.2.1, z.2.2.2 && c.2.2.2)))

instance : LeftCommutative (addChoiceU (T := T) (K := K)) where
  left_comm st₁ st₂ cs := by
    unfold addChoiceU
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    refine Multiset.bind_congr (fun z₂ _ => Multiset.bind_congr
      (fun z₁ _ => Multiset.map_congr rfl (fun c _ => ?_)))
    refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩⟩
    · cases z₁.2.2.1 <;> cases z₂.2.2.1 <;> simp [Multiset.cons_swap]
    · exact mul_left_comm _ _ _
    · exact add_left_comm _ _ _
    · cases z₁.2.2.2 <;> cases z₂.2.2.2 <;> simp

/-- The choices a bag of data allows, unsplit. -/
def choicesU (ss : Multiset (Multiset (K × K × Option T × Bool))) :
    Multiset (Multiset T × K × K × Bool) :=
  Multiset.foldr addChoiceU {(0, 1, 0, true)} ss

/-- **What a world amounts to, unsplit**: the inner values it reads, the
product of what it keeps, the sum of what it leaves out, and whether each
present occurrence's decision is a world of it. -/
def summaryU (W : Multiset (WorldOcc T K)) : Multiset T × K × K × Bool :=
  ((W.filter (fun d => d.present = true)).map (fun d => d.occ.1.valOn d.sub),
    (W.map (fun d => (statOfDecU d).1)).prod,
    (W.map (fun d => (statOfDecU d).2.1)).sum,
    decide (∀ d ∈ W, d.present = true → d.occ.1.IsWorld d.sub))

theorem summaryU_cons (d : WorldOcc T K) (W : Multiset (WorldOcc T K)) :
    summaryU (d ::ₘ W)
      = ((match (statOfDecU d).2.2.1 with
            | none => (summaryU W).1
            | some v => v ::ₘ (summaryU W).1),
          (statOfDecU d).1 * (summaryU W).2.1,
          (statOfDecU d).2.1 + (summaryU W).2.2.1,
          (statOfDecU d).2.2.2 && (summaryU W).2.2.2) := by
  have hall : (∀ x ∈ d ::ₘ W, x.present = true → x.occ.1.IsWorld x.sub)
      ↔ ((d.present = true → d.occ.1.IsWorld d.sub)
        ∧ ∀ x ∈ W, x.present = true → x.occ.1.IsWorld x.sub) := by
    constructor
    · intro h
      exact ⟨h d (Multiset.mem_cons_self _ _),
        fun x hx => h x (Multiset.mem_cons_of_mem hx)⟩
    · rintro ⟨hd, hW⟩ x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx'
      · exact hd
      · exact hW x hx'
  unfold summaryU
  refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩⟩
  · by_cases hp : d.present = true
    · simp only [statOfDecU, hp, ite_true]
      rw [Multiset.filter_cons_of_pos (p := fun x : WorldOcc T K => x.present = true) W hp,
        Multiset.map_cons]
    · simp only [statOfDecU, hp]
      rw [Multiset.filter_cons_of_neg (p := fun x : WorldOcc T K => x.present = true) W hp]
      rfl
  · simp only [Multiset.map_cons, Multiset.prod_cons]
  · simp only [Multiset.map_cons, Multiset.sum_cons]
  · dsimp only
    rw [decide_eq_decide.mpr hall, Bool.decide_and]
    refine congrArg₂ (fun x y : Bool => x && y) ?_ rfl
    by_cases hp : d.present = true <;> simp [statOfDecU, hp]

/-- **The worlds' data run over the occurrences' statistics.** -/
theorem foldr_addOcc_map_summaryU :
    ∀ s : Multiset (AggExpr T K × K),
      (Multiset.foldr addOcc {0} s).map summaryU = choicesU (s.map occStatsU) := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.foldr_zero, Multiset.map_zero, Multiset.map_singleton]
    show {summaryU 0} = choicesU 0
    unfold summaryU choicesU
    simp
  | cons o s ih =>
    rw [Multiset.foldr_cons, Multiset.map_cons, choicesU, Multiset.foldr_cons,
      addOcc, addChoiceU, occStatsU, Multiset.map_bind, Multiset.bind_map]
    refine Multiset.bind_congr (fun d _ => ?_)
    rw [Multiset.map_map, ← choicesU, ← ih, Multiset.map_map]
    exact Multiset.map_congr rfl (fun W _ => summaryU_cons d W)

theorem World.presentProd_eq_summaryU (W : World T K) :
    W.presentProd = (summaryU W.occs).2.1 := by
  unfold World.presentProd summaryU statOfDecU
  rw [← Multiset.prod_map_mul]

theorem World.absentSum_eq_summaryU (W : World T K) :
    W.absentSum = (summaryU W.occs).2.2.1 := by
  unfold World.absentSum summaryU statOfDecU
  rw [← Multiset.sum_map_add]

/-- **The data at an occurrence are its column's statistics**, unsplit:
taken once present and once absent. -/
theorem occStatsU_eq (o : AggExpr T K × K) :
    occStatsU o
      = o.1.worldStats.map (fun z => (o.2 * z.1, z.2.1, some z.2.2.1, z.2.2.2))
        + o.1.worldStats.map (fun z => (z.1, o.2 + z.2.1, none, true)) := by
  have huniv : (Finset.univ
        : Finset (Bool × Finset (Fin o.1.occs.length))).val
      = ((Finset.univ : Finset (Finset (Fin o.1.occs.length))).val.map
          (fun S => ((true : Bool), S)))
        + ((Finset.univ : Finset (Finset (Fin o.1.occs.length))).val.map
          (fun S => ((false : Bool), S))) := by
    rw [show (Finset.univ : Finset (Bool × Finset (Fin o.1.occs.length)))
        = (Finset.univ : Finset Bool) ×ˢ
          (Finset.univ : Finset (Finset (Fin o.1.occs.length))) from
      (Finset.univ_product_univ).symm, Finset.product_val]
    show (Finset.univ : Finset Bool).val.bind _ = _
    rw [show (Finset.univ : Finset Bool).val = {true, false} from rfl]
    simp [Multiset.cons_bind]
  unfold occStatsU decisions AggExpr.worldStats
  rw [Multiset.map_map, huniv, Multiset.map_add, Multiset.map_map,
    Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg₂ (fun x y : Multiset (K × K × Option T × Bool) => x + y) ?_ ?_
  · exact Multiset.map_congr rfl (fun S _ => by simp [statOfDecU])
  · exact Multiset.map_congr rfl (fun S _ => by simp [statOfDecU])

/-- **The choices commute with a homomorphism** of the annotations. -/
theorem choicesU_map {K' : Type} [CommSemiringWithMonus K'] (f : K →+* K') :
    ∀ ss : Multiset (Multiset (K × K × Option T × Bool)),
      choicesU (ss.map (Multiset.map (fun z => (f z.1, f z.2.1, z.2.2.1, z.2.2.2))))
        = (choicesU ss).map (fun c => (c.1, f c.2.1, f c.2.2.1, c.2.2.2)) := by
  intro ss
  induction ss using Multiset.induction_on with
  | empty => simp [choicesU]
  | cons st ss ih =>
    rw [Multiset.map_cons]
    simp only [choicesU, Multiset.foldr_cons] at ih ⊢
    rw [ih]
    unfold addChoiceU
    rw [Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun z _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun c _ => ?_)
    simp only [Function.comp, map_mul, map_add]

open Classical in
/-- **The worlds of a nested family, read off the statistics.** A
member's world condition and value depend on a world only through the
inner values it reads and whether its decisions are worlds; the pair a
joint reading weighs it by is the product of what it keeps and the sum of
what it leaves out. -/
theorem classWorlds_nest_eq {n : ℕ} (u : Tuple (GenValue T K) n) (M : List (Fin n))
    (a : NestedValue T K) :
    classWorlds u M (.nest a)
      = ((choicesU (a.occs.map occStatsU)).filter (fun c =>
          ∀ k ∈ M, ∀ b, u k = Sum.inr (.nest b) →
            (b.scalar = true ∨ 0 < Multiset.card c.1) ∧ c.2.2.2 = true)).map
        (fun c => (c.2.1, c.2.2.1, fun k => if k ∈ M then
          (match u k with
            | Sum.inr (.nest b) => some (b.agg c.1)
            | _ => none) else none)) := by
  rw [← foldr_addOcc_map_summaryU, classWorlds, NestedValue.worlds, Multiset.filter_map,
    Multiset.map_map, Multiset.filter_map, Multiset.map_map]
  rw [Multiset.filter_congr (q := (fun c : Multiset T × K × K × Bool =>
      ∀ k ∈ M, ∀ b, u k = Sum.inr (.nest b) →
        (b.scalar = true ∨ 0 < Multiset.card c.1) ∧ c.2.2.2 = true) ∘ summaryU)
    (fun Wo _ => ?_)]
  · refine Multiset.map_congr rfl (fun Wo _ => ?_)
    simp only [Function.comp, World.presentProd_eq_summaryU, World.absentSum_eq_summaryU]
    rfl
  · simp only [Function.comp, nestOk_iff]
    refine forall₂_congr (fun k _ => forall_congr' (fun b => imp_congr_right (fun _ => ?_)))
    unfold World.IsWorld World.IsWorldWith summaryU World.kept
    simp only [Multiset.card_map, and_true, decide_eq_true_eq]

open Classical in
/-- **A nested family's worlds under a homomorphism.** If the two sides'
occurrences carry corresponding statistics, and every column of the family
holds a nested value with the same outer aggregate and convention on both
sides, the worlds correspond, the pair pushed through `f`. -/
theorem classWorlds_hom_nest {K' : Type} [CommSemiringWithMonus K'] (f : K →+* K') {n : ℕ}
    (u : Tuple (GenValue T K) n) (u' : Tuple (GenValue T K') n) (M : List (Fin n))
    (a : NestedValue T K) (a' : NestedValue T K')
    (hO : a'.occs.map occStatsU
      = a.occs.map (fun o => (occStatsU o).map (fun z => (f z.1, f z.2.1, z.2.2.1, z.2.2.2))))
    (hM : ∀ k ∈ M, ∃ b b', u k = Sum.inr (.nest b) ∧ u' k = Sum.inr (.nest b')
      ∧ b'.agg = b.agg ∧ b'.scalar = b.scalar) :
    classWorlds u' M (.nest a') = (classWorlds u M (.nest a)).map (fun w => (f w.1, f w.2.1, w.2.2)) := by
  rw [classWorlds_nest_eq, classWorlds_nest_eq, hO,
    show a.occs.map (fun o => (occStatsU o).map (fun z => (f z.1, f z.2.1, z.2.2.1, z.2.2.2)))
      = (a.occs.map occStatsU).map
          (Multiset.map (fun z => (f z.1, f z.2.1, z.2.2.1, z.2.2.2))) from
      (Multiset.map_map _ _ _).symm, choicesU_map,
    Multiset.filter_map, Multiset.map_map, Multiset.map_map]
  rw [Multiset.filter_congr (q := fun c : Multiset T × K × K × Bool =>
    ∀ k ∈ M, ∀ b, u k = Sum.inr (.nest b) →
      (b.scalar = true ∨ 0 < Multiset.card c.1) ∧ c.2.2.2 = true) (fun c _ => ?_)]
  · refine Multiset.map_congr rfl (fun c _ => ?_)
    simp only [Function.comp]
    refine Prod.ext rfl (Prod.ext rfl (funext fun k => ?_))
    dsimp only
    by_cases hk : k ∈ M
    · rw [ite_eq_left hk, ite_eq_left hk]
      obtain ⟨b, b', hb, hb', hagg, -⟩ := hM k hk
      rw [hb, hb']
      exact congrArg (fun g => some (g c.1)) hagg
    · rw [ite_eq_right hk, ite_eq_right hk]
  · simp only [Function.comp]
    refine forall₂_congr (fun k hk => ?_)
    obtain ⟨b, b', hb, hb', -, hsc⟩ := hM k hk
    constructor
    · intro h₁ b₁ hb₁
      rw [hb] at hb₁
      cases hb₁
      have := h₁ b' hb'
      rwa [hsc] at this
    · intro h₁ b₁ hb₁
      rw [hb'] at hb₁
      cases hb₁
      have := h₁ b hb
      rwa [hsc]

end Unsplit

end NestedValue

/-! ## Families presented on both sides

What the joint reading of a row needs under a homomorphism, collected
over a set `S` of pairs of corresponding values (the target's and the
source's): that the two sides group them into families alike, and that
each family is *presented* – its flat values built from one listing on
each side, the two listings tie-block permuted (`ListingRel`), or its
nested values sharing one bag of occurrences on each side, the two bags
carrying corresponding statistics (`NestRel`). -/

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

/-- A pair of flat values built from a related pair of listings by one
`LeafSpec`. -/
def ListingRel.Member {f : K →+* K'} (D : ListingRel f T) (y' : AggTok T K')
    (y : AggTok T K) : Prop :=
  y.isNested = false ∧ y'.isNested = false ∧ ∃ (sp : LeafSpec D.ρ T) (φ φ' : FamId T),
    y.flatExpr = sp.build D.L D.ann D.str φ ∧ y'.flatExpr = sp.build D.L' D.ann' D.str' φ'

/-- **Two bags of nested occurrences, related by a homomorphism**: their
statistics correspond, pushed through `f`. -/
def NestRel (f : K →+* K') (O' : Multiset (AggExpr T K' × K')) (O : Multiset (AggExpr T K × K)) :
    Prop :=
  O'.map NestedValue.occStatsU
    = O.map (fun o => (NestedValue.occStatsU o).map (fun z => (f z.1, f z.2.1, z.2.2.1, z.2.2.2)))

/-- A pair of nested values over a related pair of bags, with the same
outer aggregate and convention. -/
def NestMember (O' : Multiset (AggExpr T K' × K')) (O : Multiset (AggExpr T K × K))
    (y' : AggTok T K') (y : AggTok T K) : Prop :=
  ∃ b b', y = .nest b ∧ y' = .nest b' ∧ b.occs = O ∧ b'.occs = O'
    ∧ b'.agg = b.agg ∧ b'.scalar = b.scalar

/-- **A set of corresponding values whose families are presented on both
sides.** -/
def FamPres (f : K →+* K') (S : AggTok T K' × AggTok T K → Prop) : Prop :=
  (∀ p q, S p → S q → (p.1.classKey = q.1.classKey ↔ p.2.classKey = q.2.classKey))
  ∧ ∀ p₀, S p₀ →
    (∃ D : ListingRel f T, ∀ q, S q → q.2.classKey = p₀.2.classKey → D.Member q.1 q.2)
    ∨ (∃ O O', NestRel f O' O ∧ ∀ q, S q → q.2.classKey = p₀.2.classKey → NestMember O' O q.1 q.2)

theorem FamPres.mono {f : K →+* K'} {S S' : AggTok T K' × AggTok T K → Prop}
    (h : FamPres f S) (hS : ∀ p, S' p → S p) : FamPres f S' :=
  ⟨fun p q hp hq => h.1 p q (hS p hp) (hS q hq), fun p₀ hp₀ =>
    (h.2 p₀ (hS p₀ hp₀)).imp
      (fun ⟨D, hD⟩ => ⟨D, fun q hq hk => hD q (hS q hq) hk⟩)
      (fun ⟨O, O', hO, hm⟩ => ⟨O, O', hO, fun q hq hk => hm q (hS q hq) hk⟩)⟩

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
    rcases hF.2 (x', x) ⟨k₀, hk₀, hx', hx⟩ with ⟨D, hD⟩ | ⟨O, O', hO, hN⟩
    · -- a flat family
      have hmemb : ∀ k ∈ M, ∃ sp : LeafSpec D.ρ T, ∃ y y' φ φ', u k = Sum.inr y ∧ u' k = Sum.inr y'
          ∧ y.flatExpr = sp.build D.L D.ann D.str φ
          ∧ y'.flatExpr = sp.build D.L' D.ann' D.str' φ' := by
        intro k hk
        obtain ⟨hc, y, y', hy, hy', hky⟩ := hmem k hk
        obtain ⟨-, -, sp, φ, φ', hb, hb'⟩ := hD (y', y) ⟨k, hc, hy', hy⟩ hky
        exact ⟨sp, y, y', φ, φ', hy, hy', hb, hb'⟩
      obtain ⟨hn₀, hn₀', sp₀, φ₀, φ₀', hb₀, hb₀'⟩ := hD (x', x) ⟨k₀, hk₀, hx', hx⟩ rfl
      let sp : Fin n → LeafSpec D.ρ T := fun k =>
        if h : ∃ sp : LeafSpec D.ρ T, ∃ y y' φ φ', u k = Sum.inr y ∧ u' k = Sum.inr y'
            ∧ y.flatExpr = sp.build D.L D.ann D.str φ
            ∧ y'.flatExpr = sp.build D.L' D.ann' D.str' φ'
        then Classical.choose h else sp₀
      have hsp : ∀ k ∈ M, ∃ y y' φ φ', u k = Sum.inr y ∧ u' k = Sum.inr y'
          ∧ y.flatExpr = (sp k).build D.L D.ann D.str φ
          ∧ y'.flatExpr = (sp k).build D.L' D.ann' D.str' φ' := by
        intro k hk
        have h := hmemb k hk
        simp only [sp, dite_eq_left h]
        exact Classical.choose_spec h
      exact classWorlds_hom f u u' M D.L D.ann D.str D.L' D.ann' D.str' D.e D.heqv D.hperm
        D.hstr D.hann sp
        (fun k hk => by
          obtain ⟨y, y', φ, φ', hy, -, hb, -⟩ := hsp k hk
          exact ⟨y, φ, hy, hb⟩)
        (fun k hk => by
          obtain ⟨y, y', φ, φ', -, hy', -, hb'⟩ := hsp k hk
          exact ⟨y', φ', hy', hb'⟩)
        x hn₀ sp₀ φ₀ hb₀ x' hn₀' φ₀' hb₀'
    · -- a nested family
      obtain ⟨b₀, b₀', rfl, rfl, ho₀, ho₀', -, -⟩ := hN (x', x) ⟨k₀, hk₀, hx', hx⟩ rfl
      refine NestedValue.classWorlds_hom_nest f u u' M b₀ b₀' (by rw [ho₀, ho₀']; exact hO)
        (fun k hk => ?_)
      obtain ⟨hc, y, y', hy, hy', hky⟩ := hmem k hk
      obtain ⟨b, b', rfl, rfl, -, -, hagg', hsc⟩ := hN (y', y) ⟨k, hc, hy', hy⟩ hky
      exact ⟨b, b', hy, hy', hagg', hsc⟩

end FamPres
