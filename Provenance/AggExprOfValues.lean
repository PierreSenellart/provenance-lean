/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.AggExpr
import all Provenance.AggValue
import all Provenance.AggExpr
import all Provenance.HavingSemantics

/-!
# An expression over several aggregate values of one family

Two aggregates of one group read the same occurrences: `sum(x)` and
`count(*)` over a group are two functions of one family. A term over
both, `sum(x) + count(*)`, is then one aggregate expression over that
family, whose leaves are the two aggregates (`AggExpr`).

`AggExpr.ofValues` builds it from the finished values. An `AggValue` keeps,
per occurrence, the value its term takes there and the occurrence's
annotation; values of one family list the same occurrences in the same
order (`AggValue.Aligned`), so the expression's occurrence carries, leaf
by leaf, the value each of them recorded at that position.

`AggExpr.collapse_ofValues` says the expression is read deterministically
as the term of the readings of its values: over plain relations the
column is the term applied to the aggregates, which is what SQL computes.
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
private theorem seqOf_map_eq {α β γ : Type} {L₁ : List α} {L₂ : List β} (f : α → γ)
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
