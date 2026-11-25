/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.AggExpr
public import Provenance.SubWorlds
import all Provenance.AggValue
import all Provenance.AggExpr
import all Provenance.HavingSemantics
import all Provenance.SubWorlds

/-!
# An expression over several aggregate values of one family

Two aggregates of one group read the same occurrences: `sum(x)` and
`count(*)` over a group are two functions of one family. A term over
both, `sum(x) + count(*)`, is then one aggregate expression over that
family, whose leaves are the two aggregates (`AggExpr`).

`AggExpr.ofValues` builds it from finished values. An `AggValue` keeps,
per occurrence, the value its term takes there and the occurrence's
annotation; values of one family list the same occurrences in the same
order (`AggValue.Aligned`), so the expression's occurrence carries, leaf
by leaf, the value each of them recorded at that position. Its
deterministic reading is the term of the readings of its values
(`AggExpr.collapse_ofValues`), its worlds are theirs
(`AggExpr.isWorld_ofValues`) and its value in a world is the term of their
values in that world (`AggExpr.valOn_ofValues`).

`AggExpr.pair` does the same for two expressions, which is what a term
over columns that are already expressions needs; `AggExpr.PresBy.pair`, in
`Provenance.JointHom`, says that two expressions presented by one listing
of the family are presented together by it.
-/

@[expose] public section

variable {T K : Type}

/-- **Values of one family**: they list as many occurrences as the first,
with the same annotations in the same order. -/
def AggValue.Aligned {p : ℕ} (a : Fin (p + 1) → AggValue T K) : Prop :=
  ∀ j, (a j).occs.map Prod.snd = (a 0).occs.map Prod.snd

namespace AggExpr

/-- **The expression `g(a₀, …, a_p)` over the family the values share.**
Its occurrences are those of the first value; at each, leaf `j` reads the
value `a j` recorded at that position, and every leaf has every occurrence
in its group, none being filtered. Where the values are not aligned the
positions past a shorter one read the first value's, which no result
relies on. -/
def ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K) (g : (Fin (p + 1) → T) → T) :
    AggExpr T K where
  arity := p + 1
  occs := List.ofFn (fun i : Fin (a 0).occs.length =>
    ((fun j => (((a j).occs[(i : ℕ)]?).map Prod.fst).getD ((a 0).occs.get i).fst),
      ((a 0).occs.get i).snd, (fun _ => true), (fun _ => true)))
  aggs := fun j => (a j).agg
  scalar := fun j => (a j).scalar
  g := g
  fam := (a 0).fam
  oids := (a 0).oids

@[simp] theorem arity_ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) : (ofValues a g).arity = p + 1 := rfl

/-- The expression has the occurrences of the first value. -/
@[simp] theorem length_occs_ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) : (ofValues a g).occs.length = (a 0).occs.length := by
  simp [ofValues]

/-- **What leaf `j` reads over the whole family** is what the value `a j`
recorded, when the values are aligned. -/
theorem occs_map_leaf_ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) (ha : AggValue.Aligned a) (j : Fin (p + 1)) :
    (ofValues a g).occs.map (fun o => o.fst j) = (a j).occs.map Prod.fst := by
  have hlen : (a j).occs.length = (a 0).occs.length := by
    have := congrArg List.length (ha j)
    simpa using this
  apply List.ext_getElem
  · simp [ofValues, hlen]
  · intro i h₁ h₂
    have hi : i < (a j).occs.length := by simpa using h₂
    simp [ofValues, List.getElem?_eq_getElem hi]

/-- **The deterministic reading of the expression is the term of the
readings of its values.** -/
theorem collapse_ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) (ha : AggValue.Aligned a) :
    (ofValues a g).collapse = g (fun j => (a j).collapse) := by
  unfold collapse valOn
  refine congrArg g (funext fun j => ?_)
  show (a j).agg ((ofValues a g).leafSeq j Finset.univ) = (a j).agg ((a j).occs.map Prod.fst)
  have hreads : (ofValues a g).reads j = Finset.univ := by
    ext i
    simp [reads, ofValues]
  rw [leafSeq, Finset.univ_inter, hreads, Having.seqOf_univ, occs_map_leaf_ofValues a g ha j]

/-- Two lists with the same image select the same image, the positions
being carried to each along its length. -/
theorem seqOf_map_eq {α β γ : Type} {L₁ : List α} {L₂ : List β} (f : α → γ)
    (g' : β → γ) (h : L₁.map f = L₂.map g') {N : ℕ} (h₁ : N = L₁.length)
    (h₂ : N = L₂.length) (S : Finset (Fin N)) :
    (Having.seqOf L₁ (S.map (finCongr h₁).toEmbedding)).map f
      = (Having.seqOf L₂ (S.map (finCongr h₂).toEmbedding)).map g' := by
  subst h₁
  have e₁ : L₁.length = (L₁.map f).length := by simp
  have e₂ : L₂.length = (L₂.map g').length := by simp
  rw [← AggValue.seqOf_map f L₁ e₁, ← AggValue.seqOf_map g' L₂ e₂, Having.seqOf_congr_list h]
  refine congrArg _ ?_
  ext x
  simp only [Finset.mem_map_equiv, finCongr_symm, finCongr_apply]
  rfl

/-- The lengths of aligned values agree. -/
theorem _root_.AggValue.Aligned.length_eq {p : ℕ} {a : Fin (p + 1) → AggValue T K}
    (ha : AggValue.Aligned a) (j : Fin (p + 1)) :
    (a 0).occs.length = (a j).occs.length := by
  have := congrArg List.length (ha j)
  simpa using this.symm

/-- **The value of the expression in a world is the term of the values of
its leaves in that world**: every aggregate is read in the same one. -/
theorem valOn_ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) (ha : AggValue.Aligned a)
    (W : Finset (Fin (a 0).occs.length)) :
    (ofValues a g).valOn (W.map (finCongr (length_occs_ofValues a g).symm).toEmbedding)
      = g (fun j => (a j).valOn (W.map (finCongr (ha.length_eq j)).toEmbedding)) := by
  unfold valOn
  refine congrArg g (funext fun j => ?_)
  show (a j).agg ((ofValues a g).leafSeq j _) = (a j).agg _
  refine congrArg (a j).agg ?_
  have hreads : (ofValues a g).reads j = Finset.univ := by
    ext i
    simp [reads, ofValues]
  rw [leafSeq, hreads, Finset.inter_univ]
  exact seqOf_map_eq (L₁ := (ofValues a g).occs) (L₂ := (a j).occs) (fun o => o.fst j) Prod.fst
    (occs_map_leaf_ofValues a g ha j) _ _ W

/-- **The worlds of the expression** are the non-empty subfamilies, and
the empty one too when every leaf is scalar. -/
theorem isWorld_ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) (W : Finset (Fin (ofValues a g).occs.length)) :
    (ofValues a g).IsWorld W ↔ ((∀ j, (a j).scalar = true) ∨ W.Nonempty) := by
  have hframe : ∀ j, (ofValues a g).inFrame j = Finset.univ := fun j => by
    ext i
    simp [inFrame, ofValues]
  unfold IsWorld
  simp only [hframe, Finset.inter_univ]
  constructor
  · intro h
    by_cases hs : ∀ j, (a j).scalar = true
    · exact Or.inl hs
    · obtain ⟨j, hj⟩ := not_forall.mp hs
      have hj' : (a j).scalar = false := by simpa using hj
      exact Or.inr (h j hj')
  · rintro (hs | hW) j hj
    · have hj' : (a j).scalar = false := hj
      rw [hs j] at hj'
      exact absurd hj' (by decide)
    · exact hW

/-- The annotations of the expression's occurrences are those of the first
value's. -/
theorem anns_ofValues {p : ℕ} (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) (i : Fin (a 0).occs.length) :
    (ofValues a g).anns (finCongr (length_occs_ofValues a g).symm i) = (a 0).anns i := by
  simp [anns, ofValues, AggValue.anns]

/-- **Mapping the annotations commutes with the construction**: the
expression over the mapped values is the mapped expression. It is what a
homomorphism of semirings does to both, and it asks nothing of the map. -/
theorem mapAnn_ofValues {K' : Type} {p : ℕ} (h : K → K') (a : Fin (p + 1) → AggValue T K)
    (g : (Fin (p + 1) → T) → T) :
    (ofValues a g).mapAnn h = ofValues (fun j => (a j).mapAnn h) g := by
  unfold ofValues AggExpr.mapAnn AggValue.mapAnn
  simp only [AggExpr.mk.injEq, heq_eq_eq, true_and, and_true]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp
    funext j
    cases (a j).occs[i]? <;> rfl

/-- Aligned values stay aligned under a map of the annotations. -/
theorem _root_.AggValue.Aligned.mapAnn {K' : Type} {p : ℕ} (h : K → K')
    {a : Fin (p + 1) → AggValue T K} (ha : AggValue.Aligned a) :
    AggValue.Aligned (fun j => (a j).mapAnn h) := by
  intro j
  have := congrArg (List.map h) (ha j)
  simpa [AggValue.mapAnn, List.map_map, Function.comp_def] using this

end AggExpr

/-! ## Two expressions of one family as one

`AggExpr.ofValues` takes finished values. A term may also combine columns
that are expressions already – an aggregate read through a `FILTER`
clause, a term over an aggregate – and those have several leaves, with
their own flags. `AggExpr.pair` puts two expressions over one family side
by side: the leaves of the first, then those of the second, each
occurrence carrying what both recorded there, and the function applied to
the two values. -/

namespace AggExpr

/-- An occurrence of an expression of arity `p`: what each leaf reads, the
annotation, and the two families of flags. -/
abbrev Occ (T K : Type) (p : ℕ) := (Fin p → T) × K × (Fin p → Bool) × (Fin p → Bool)

/-- What the first expression recorded at an occurrence of the pair. -/
def occLeft {p q : ℕ} (z : Occ T K (p + q)) : Occ T K p :=
  (fun j => z.1 (Fin.castAdd q j), z.2.1, fun j => z.2.2.1 (Fin.castAdd q j),
    fun j => z.2.2.2 (Fin.castAdd q j))

/-- What the second recorded there, under the pair's annotation. -/
def occRight {p q : ℕ} (z : Occ T K (p + q)) : Occ T K q :=
  (fun j => z.1 (Fin.natAdd p j), z.2.1, fun j => z.2.2.1 (Fin.natAdd p j),
    fun j => z.2.2.2 (Fin.natAdd p j))

/-- **The expression `g₂(e₁, e₂)` over the family the two share.** -/
def pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) : AggExpr T K where
  arity := e₁.arity + e₂.arity
  occs := List.zipWith (fun o₁ o₂ =>
    ((Fin.append o₁.1 o₂.1, o₁.2.1, Fin.append o₁.2.2.1 o₂.2.2.1,
      Fin.append o₁.2.2.2 o₂.2.2.2) : Occ T K (e₁.arity + e₂.arity))) e₁.occs e₂.occs
  aggs := Fin.append e₁.aggs e₂.aggs
  scalar := Fin.append e₁.scalar e₂.scalar
  g := fun v => g₂ (e₁.g (fun j => v (Fin.castAdd e₂.arity j)))
    (e₂.g (fun j => v (Fin.natAdd e₁.arity j)))
  fam := e₁.fam
  oids := e₁.oids

/-- **Two expressions of one family**: as many occurrences, with the same
annotations in the same order. -/
def SameFamily (e₁ e₂ : AggExpr T K) : Prop :=
  e₂.occs.map (fun o => o.2.1) = e₁.occs.map (fun o => o.2.1)

theorem SameFamily.length_eq {e₁ e₂ : AggExpr T K} (h : SameFamily e₁ e₂) :
    e₁.occs.length = e₂.occs.length := by
  have := congrArg List.length h
  simpa using this.symm

/-- The pair's occurrences, read on the left, are the first expression's. -/
theorem pair_occs_map_left (e₁ e₂ : AggExpr T K) (g₂ : T → T → T)
    (h : SameFamily e₁ e₂) : (pair e₁ e₂ g₂).occs.map occLeft = e₁.occs := by
  apply List.ext_getElem
  · simp [pair, h.length_eq]
  · intro i h₁ h₂
    simp only [pair, List.getElem_map, List.getElem_zipWith, occLeft, Fin.append_left]

/-- Read on the right, they are the second's. -/
theorem pair_occs_map_right (e₁ e₂ : AggExpr T K) (g₂ : T → T → T)
    (h : SameFamily e₁ e₂) : (pair e₁ e₂ g₂).occs.map occRight = e₂.occs := by
  apply List.ext_getElem
  · simp [pair, h.length_eq]
  · intro i h₁ h₂
    have hi₁ : i < e₁.occs.length := by simpa [pair, h.length_eq] using h₁
    have hi₂ : i < e₂.occs.length := h₂
    have hann : (e₁.occs[i]).2.1 = (e₂.occs[i]).2.1 := by
      have := congrArg (fun l => l[i]?) h
      simpa [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂] using this.symm
    simp only [pair, List.getElem_map, List.getElem_zipWith, occRight, Fin.append_right, hann]

/-- **A selected sequence is a world of the pair** when it is one of each
side. -/
theorem okSeq_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T)
    (s : List (Occ T K (e₁.arity + e₂.arity))) :
    (pair e₁ e₂ g₂).okSeq s ↔ e₁.okSeq (s.map occLeft) ∧ e₂.okSeq (s.map occRight) := by
  unfold okSeq
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · obtain ⟨z, hz, hf⟩ := h (Fin.castAdd e₂.arity j) (by
        show Fin.append e₁.scalar e₂.scalar _ = false
        rw [Fin.append_left]; exact hj)
      exact ⟨occLeft z, List.mem_map_of_mem hz, hf⟩
    · obtain ⟨z, hz, hf⟩ := h (Fin.natAdd e₁.arity j) (by
        show Fin.append e₁.scalar e₂.scalar _ = false
        rw [Fin.append_right]; exact hj)
      exact ⟨occRight z, List.mem_map_of_mem hz, hf⟩
  · rintro ⟨h₁, h₂⟩ j
    refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) j
    · have hj' : e₁.scalar j = false := by
        have : Fin.append e₁.scalar e₂.scalar (Fin.castAdd e₂.arity j) = false := hj
        rwa [Fin.append_left] at this
      obtain ⟨z, hz, hf⟩ := h₁ j hj'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact ⟨w, hw, hf⟩
    · have hj' : e₂.scalar j = false := by
        have : Fin.append e₁.scalar e₂.scalar (Fin.natAdd e₁.arity j) = false := hj
        rwa [Fin.append_right] at this
      obtain ⟨z, hz, hf⟩ := h₂ j hj'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact ⟨w, hw, hf⟩

/-- **The value of the pair on a selected sequence** is the function of
the two sides' values on it. -/
theorem valSeq_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T)
    (s : List (Occ T K (e₁.arity + e₂.arity))) :
    (pair e₁ e₂ g₂).valSeq s
      = g₂ (e₁.valSeq (s.map occLeft)) (e₂.valSeq (s.map occRight)) := by
  unfold valSeq
  show g₂ (e₁.g _) (e₂.g _) = _
  congr 1
  · refine congrArg e₁.g (funext fun j => ?_)
    show Fin.append e₁.aggs e₂.aggs (Fin.castAdd e₂.arity j) _ = _
    rw [Fin.append_left, List.filter_map, List.map_map]
    rfl
  · refine congrArg e₂.g (funext fun j => ?_)
    show Fin.append e₁.aggs e₂.aggs (Fin.natAdd e₁.arity j) _ = _
    rw [Fin.append_right, List.filter_map, List.map_map]
    rfl

/-- The pair has the occurrences of the first expression. -/
theorem length_occs_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) (h : SameFamily e₁ e₂) :
    e₁.occs.length = (pair e₁ e₂ g₂).occs.length := by
  simp [pair, h.length_eq]

/-- **A subfamily is a world of the pair** when it is one of each side. -/
theorem isWorld_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) (h : SameFamily e₁ e₂)
    (W : Finset (Fin e₁.occs.length)) :
    (pair e₁ e₂ g₂).IsWorld (W.map (finCongr (length_occs_pair e₁ e₂ g₂ h)).toEmbedding)
      ↔ e₁.IsWorld W ∧ e₂.IsWorld (W.map (finCongr h.length_eq).toEmbedding) := by
  rw [isWorld_iff_okSeq, isWorld_iff_okSeq, isWorld_iff_okSeq, okSeq_pair]
  have hl := seqOf_map_eq (L₁ := (pair e₁ e₂ g₂).occs) (L₂ := e₁.occs) occLeft id
    (by rw [pair_occs_map_left e₁ e₂ g₂ h, List.map_id]) (length_occs_pair e₁ e₂ g₂ h) rfl W
  have hr := seqOf_map_eq (L₁ := (pair e₁ e₂ g₂).occs) (L₂ := e₂.occs) occRight id
    (by rw [pair_occs_map_right e₁ e₂ g₂ h, List.map_id]) (length_occs_pair e₁ e₂ g₂ h)
    h.length_eq W
  rw [hl, hr, List.map_id, List.map_id]
  have : W.map (finCongr (rfl : e₁.occs.length = e₁.occs.length)).toEmbedding = W := by
    ext x; simp
  rw [this]

/-- **The value of the pair in a world** is the function of the two
sides' values in that world. -/
theorem valOn_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) (h : SameFamily e₁ e₂)
    (W : Finset (Fin e₁.occs.length)) :
    (pair e₁ e₂ g₂).valOn (W.map (finCongr (length_occs_pair e₁ e₂ g₂ h)).toEmbedding)
      = g₂ (e₁.valOn W) (e₂.valOn (W.map (finCongr h.length_eq).toEmbedding)) := by
  rw [valOn_eq_valSeq, valOn_eq_valSeq, valOn_eq_valSeq, valSeq_pair]
  have hl := seqOf_map_eq (L₁ := (pair e₁ e₂ g₂).occs) (L₂ := e₁.occs) occLeft id
    (by rw [pair_occs_map_left e₁ e₂ g₂ h, List.map_id]) (length_occs_pair e₁ e₂ g₂ h) rfl W
  have hr := seqOf_map_eq (L₁ := (pair e₁ e₂ g₂).occs) (L₂ := e₂.occs) occRight id
    (by rw [pair_occs_map_right e₁ e₂ g₂ h, List.map_id]) (length_occs_pair e₁ e₂ g₂ h)
    h.length_eq W
  rw [hl, hr, List.map_id, List.map_id]
  have : W.map (finCongr (rfl : e₁.occs.length = e₁.occs.length)).toEmbedding = W := by
    ext x; simp
  rw [this]

/-- **The world a valuation realizes in the pair** is the one it realizes
in the first expression: the pair carries its annotations. -/
theorem realizedWorld_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) (h : SameFamily e₁ e₂)
    (ν : K → Bool) :
    (pair e₁ e₂ g₂).realizedWorld ν
      = (e₁.realizedWorld ν).map (finCongr (length_occs_pair e₁ e₂ g₂ h)).toEmbedding := by
  ext i
  simp only [realizedWorld, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
    finCongr_symm, anns, List.get_eq_getElem, finCongr_apply, Fin.val_cast]
  simp only [pair, List.getElem_zipWith]

/-- And in the second, whose annotations are the same. -/
theorem realizedWorld_right {e₁ e₂ : AggExpr T K} (h : SameFamily e₁ e₂) (ν : K → Bool) :
    e₂.realizedWorld ν = (e₁.realizedWorld ν).map (finCongr h.length_eq).toEmbedding := by
  ext i
  simp only [realizedWorld, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
    finCongr_symm, anns, List.get_eq_getElem, finCongr_apply, Fin.val_cast]
  have hi : i.val < e₁.occs.length := by rw [h.length_eq]; exact i.isLt
  have := congrArg (fun l => l[i.val]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq] at this
  rw [this]

/-- **The realized world is a world of the pair** when it is one of each
side. -/
theorem isWorld_realized_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) (h : SameFamily e₁ e₂)
    (ν : K → Bool) :
    (pair e₁ e₂ g₂).IsWorld ((pair e₁ e₂ g₂).realizedWorld ν)
      ↔ e₁.IsWorld (e₁.realizedWorld ν) ∧ e₂.IsWorld (e₂.realizedWorld ν) := by
  rw [realizedWorld_pair e₁ e₂ g₂ h, isWorld_pair e₁ e₂ g₂ h, realizedWorld_right h]

/-- **The pair, in the world a valuation realizes**, is the function of
the two sides there. -/
theorem specialize_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) (h : SameFamily e₁ e₂)
    (ν : K → Bool) :
    (pair e₁ e₂ g₂).specialize ν = g₂ (e₁.specialize ν) (e₂.specialize ν) := by
  unfold specialize
  rw [realizedWorld_pair e₁ e₂ g₂ h, valOn_pair e₁ e₂ g₂ h, realizedWorld_right h]

/-- The pair is read in the scalar convention when both sides are. -/
theorem isScalar_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T) :
    (pair e₁ e₂ g₂).isScalar = (e₁.isScalar && e₂.isScalar) := by
  rw [Bool.eq_iff_iff]
  simp only [isScalar, List.all_eq_true, Bool.and_eq_true]
  constructor
  · intro hall
    refine ⟨fun j _ => ?_, fun j _ => ?_⟩
    · have := hall (Fin.castAdd e₂.arity j) (List.mem_finRange _)
      simpa [pair, Fin.append_left] using this
    · have := hall (Fin.natAdd e₁.arity j) (List.mem_finRange _)
      simpa [pair, Fin.append_right] using this
  · rintro ⟨h1, h2⟩ j _
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := h1 i (List.mem_finRange _)
      simpa [pair, Fin.append_left] using this
    · have := h2 i (List.mem_finRange _)
      simpa [pair, Fin.append_right] using this

/-- The value on a sequence does not look at the annotations. -/
theorem valSeq_congr_strip (e : AggExpr T K) {K₂ : Type}
    {s : List (Occ T K e.arity)} {s' : List (Occ T K₂ e.arity)}
    (h : s.map (fun z => (z.1, z.2.2)) = s'.map (fun z => (z.1, z.2.2))) :
    e.g (fun j => e.aggs j ((s.filter (fun z => z.2.2.1 j && z.2.2.2 j)).map (fun z => z.1 j)))
      = e.g (fun j => e.aggs j
          ((s'.filter (fun z => z.2.2.1 j && z.2.2.2 j)).map (fun z => z.1 j))) := by
  refine congrArg e.g (funext fun j => congrArg (e.aggs j) ?_)
  have key : ∀ {K₀ : Type} (l : List (Occ T K₀ e.arity)),
      (l.filter (fun z => z.2.2.1 j && z.2.2.2 j)).map (fun z => z.1 j)
        = ((l.map (fun z => (z.1, z.2.2))).filter (fun w => w.2.1 j && w.2.2 j)).map
            (fun w => w.1 j) := by
    intro K₀ l
    rw [List.filter_map, List.map_map]
    rfl
  rw [key s, key s', h]

/-- **The deterministic reading of a pair** of expressions with as many
occurrences is the function of the two readings. The annotations play no
part, so the two need not be of one family. -/
theorem collapse_pair (e₁ e₂ : AggExpr T K) (g₂ : T → T → T)
    (h : e₁.occs.length = e₂.occs.length) :
    (pair e₁ e₂ g₂).collapse = g₂ e₁.collapse e₂.collapse := by
  unfold collapse
  rw [valOn_eq_valSeq, valOn_eq_valSeq, valOn_eq_valSeq, Having.seqOf_univ, Having.seqOf_univ,
    Having.seqOf_univ, valSeq_pair]
  have hl : (pair e₁ e₂ g₂).occs.map occLeft = e₁.occs := by
    apply List.ext_getElem
    · simp [pair, h]
    · intro i h₁ h₂
      simp only [pair, List.getElem_map, List.getElem_zipWith, occLeft, Fin.append_left]
  have hr : ((pair e₁ e₂ g₂).occs.map occRight).map (fun z => (z.1, z.2.2))
      = e₂.occs.map (fun z => (z.1, z.2.2)) := by
    apply List.ext_getElem
    · simp [pair, h]
    · intro i h₁ h₂
      simp only [pair, List.getElem_map, List.getElem_zipWith, occRight, Fin.append_right]
  rw [hl]
  exact congrArg (g₂ _) (valSeq_congr_strip e₂ hr)

end AggExpr

/-! ## An instance

`sum(x) + count(*)` over a group of three rows holding `100`, `100` and
`90`: the expression reads `293` over the whole group, and `101` in the
world that holds the first row alone – one value per world, both
aggregates read in the same one. -/

/-- The sum and the count of one group of three rows, as finished values. -/
def sumAndCount : Fin 2 → AggValue ℕ ℕ :=
  ![⟨SeqAggFunc.sum, [(100, 1), (100, 1), (90, 1)], false, FamId.none, []⟩,
    ⟨SeqAggFunc.count, [(1, 1), (1, 1), (1, 1)], false, FamId.none, []⟩]

/-- Over the whole group the expression is the sum of the two aggregates. -/
theorem sumAndCount_collapse :
    (AggExpr.ofValues sumAndCount (fun v => v 0 + v 1)).collapse = 293 := by decide

/-- In the world of the first row alone both aggregates read that row. -/
theorem sumAndCount_first_row :
    (AggExpr.ofValues sumAndCount (fun v => v 0 + v 1)).valOn {⟨0, by decide⟩} = 101 := by
  decide
