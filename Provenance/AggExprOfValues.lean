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
