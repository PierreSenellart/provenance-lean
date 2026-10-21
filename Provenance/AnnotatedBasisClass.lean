/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Semirings.How
public import Provenance.Semirings.Which
public import Mathlib.SetTheory.Cardinal.Order
public import Provenance.AnnotatedDiffRow
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Provenance.AnnotatedChains
import Provenance.AnnotatedEpsRow

/-!
# The annotated basis over a class of semirings

The nine classes `{∅, Π, σ, apply, γ, win, μ^⊎, ε, −}` are a basis of the
annotated algebra over the m-semirings where `δ` is the support map and a
linear set recursion settles within twice the size of its tuple set
(`PathSum.SettlesLinear`, which holds of `ℕ`, `ℕ[X]` and the lineage
semiring), or where `δ` is the identity (`AnnBasisClass`): they generate
it over every such semiring (`generatesAnn_annEpsOps_of_class`), and no
proper subset does over all of them (`annEpsOps_minimal_in_class`). The
why-provenance semiring `Why[X]` has the support map but not the bound:
a cycle over an edge carrying `m` witnesses settles only after `m` rounds.

The generation half is `generatesAnn_annEpsOps_of_support` and
`generatesAnn_annEpsOps_of_delta_id`. For minimality every row needs a
witness inside the class. `ℕ` is in it and carries all of them but the
difference's: `ℕ × ℕ`, where the difference row was first checked, has
zero divisors and is not absorptive. The difference's witness inside the
class is `ℕ[x, y]` (`PolyXY`): on one instance, `R` holding a tuple
annotated `x ⊕ y` and `S` holding it annotated `y`, `R − S` gives `x`,
while every annotation a query without a difference builds has an
`x`-coefficient at most its `y`-coefficient (`PolyXY.annClosed_xLeY`) – a
property of `𝟘`, `𝟙`, sums and products, of `δ` and of `𝟙 ⊖ ·`, the last
two giving constants.
-/

@[expose] public section

/-! ## `ℕ[x, y]` -/

/-- **Polynomials in two variables `x = X 0` and `y = X 1`**, with
coefficients in `ℕ`: How-provenance over two tokens. -/
abbrev PolyXY := MvPolynomial (Fin 2) ℕ

namespace PolyXY

open Classical in
/-- Any linear order serves to list the occurrences of a family. -/
noncomputable instance : HasAltLinearOrder PolyXY := ⟨linearOrderOfSTO WellOrderingRel⟩

theorem delta_eq (p : PolyXY) : SemiringWithMonus.delta p = if p = 0 then 0 else 1 := rfl

theorem settlesEarly : PathSum.SettlesEarly PolyXY :=
  Or.inr ⟨fun _ _ h => add_eq_left.mp h, inferInstance⟩

/-- The coefficient of a variable in a product. -/
theorem coeff_single_mul (i : Fin 2) (p q : PolyXY) :
    (p * q).coeff (Finsupp.single i 1)
      = p.coeff 0 * q.coeff (Finsupp.single i 1) + p.coeff (Finsupp.single i 1) * q.coeff 0 := by
  rw [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ]

theorem single_ne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
  rw [Ne, Finsupp.single_left_inj one_ne_zero]
  decide

theorem coeff_add' (a b : PolyXY) (m : Fin 2 →₀ ℕ) : (a + b).coeff m = a.coeff m + b.coeff m :=
  by simp

/-- **The `x`-coefficient is at most the `y`-coefficient.** -/
def XLeY (p : PolyXY) : Prop :=
  p.coeff (Finsupp.single 0 1) ≤ p.coeff (Finsupp.single 1 1)

theorem xLeY_of_const (p : PolyXY) (h : ∀ i : Fin 2, p.coeff (Finsupp.single i 1) = 0) :
    XLeY p := by
  unfold XLeY; rw [h 0, h 1]

theorem coeff_one_single (i : Fin 2) : (1 : PolyXY).coeff (Finsupp.single i 1) = 0 := by
  rw [MvPolynomial.coeff_one, ite_eq_right]
  intro h
  exact absurd (congrArg (fun f => f i) h) (by simp)

/-- **Every operator but the difference keeps it.** -/
theorem annClosed_xLeY : AnnClosed XLeY := by
  refine ⟨xLeY_of_const 0 fun i => by simp, xLeY_of_const 1 coeff_one_single,
    fun a b ha hb => ?_, fun a b ha hb => ?_, fun a _ => ?_, fun a _ => ?_⟩
  · unfold XLeY at *
    rw [coeff_add', coeff_add']
    exact Nat.add_le_add ha hb
  · unfold XLeY at *
    rw [coeff_single_mul, coeff_single_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_right _ ha)
  · rw [delta_eq]
    split_ifs
    · exact xLeY_of_const 0 fun i => by simp
    · exact xLeY_of_const 1 coeff_one_single
  · refine xLeY_of_const _ fun i => ?_
    rw [coeff_sub, coeff_one_single]
    exact Nat.zero_sub _

end PolyXY

/-! ## The difference row inside the class -/

/-- **The instance**: `R` holds `0` annotated `x ⊕ y`, and `S` holds it
annotated `y`. -/
noncomputable def dDiffXY : AnnotatedDatabase ℕ PolyXY :=
  AnnotatedDatabase.assign "R"
    (({(((fun _ => 0) : Tuple ℕ 1), MvPolynomial.X 0 + MvPolynomial.X 1)}
      : Multiset (AnnotatedTuple ℕ PolyXY 1)) : AnnotatedRelation ℕ PolyXY 1)
    (AnnotatedDatabase.assign "S"
      (({(((fun _ => 0) : Tuple ℕ 1), MvPolynomial.X 1)}
        : Multiset (AnnotatedTuple ℕ PolyXY 1)) : AnnotatedRelation ℕ PolyXY 1) [])

theorem dDiffXY_xLeY : ∀ k t (r : AnnotatedRelation ℕ PolyXY k), dDiffXY.find k t = some r →
    ∀ a ∈ r, PolyXY.XLeY a.2 := by
  intro k t r hr a ha
  unfold dDiffXY at hr
  by_cases h₁ : k = 1 ∧ t = "R"
  · obtain ⟨rfl, rfl⟩ := h₁
    rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
    subst hr
    rw [Multiset.mem_singleton] at ha
    subst ha
    show PolyXY.XLeY (MvPolynomial.X 0 + MvPolynomial.X 1)
    unfold PolyXY.XLeY
    simp [MvPolynomial.coeff_X, PolyXY.single_ne.symm]
  · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h₁] at hr
    by_cases h₂ : k = 1 ∧ t = "S"
    · obtain ⟨rfl, rfl⟩ := h₂
      rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
      subst hr
      rw [Multiset.mem_singleton] at ha
      subst ha
      show PolyXY.XLeY (MvPolynomial.X 1)
      unfold PolyXY.XLeY
      simp [MvPolynomial.coeff_X, PolyXY.single_ne.symm]
    · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h₂] at hr
      exact absurd hr (by
        rw [show AnnotatedDatabase.find k t ([] : AnnotatedDatabase ℕ PolyXY) = none from rfl]
        simp)

/-- **`R − S` there**: `(x ⊕ y) ⊖ y = x`. -/
theorem evaluateAnnotated_diffWitness_xy :
    diffWitness.evaluateAnnotated dDiffXY (fun _ => 0)
      = ({(((fun _ => 0) : Tuple ℕ 1), MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 1)}
        : Multiset (AnnotatedTuple ℕ PolyXY 1)) := by
  show diffWitness.ann dDiffXY (fun _ => 0) {} = _
  rw [diffWitness, AggQueryIn.ann_diff, AggQueryIn.ann_Rel, AggQueryIn.ann_Rel, dDiffXY,
    AnnotatedDatabase.find_assign,
    AnnotatedDatabase.find_assign_of_ne _ _ _ _ (by decide), AnnotatedDatabase.find_assign]
  simp only [Multiset.map_singleton]
  congr 1
  refine Prod.ext rfl ?_
  dsimp only
  congr 1
  unfold PathSum.wt
  erw [Multiset.filter_singleton, ite_eq_left rfl, Multiset.map_singleton,
    Multiset.sum_singleton]

theorem not_xLeY_x : ¬ PolyXY.XLeY (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 1) := by
  unfold PolyXY.XLeY
  rw [coeff_sub, coeff_sub]
  simp [MvPolynomial.coeff_X, PolyXY.single_ne, PolyXY.single_ne.symm]

/-- **`−` is in every set generating the annotated algebra over
`ℕ[x, y]`**, which is in the class of `AnnBasisClass`. -/
theorem diff_mem_of_generatesAnn_xy {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnn ℕ PolyXY schemaRS cnt S) : OpKind.diff ∈ S := by
  by_contra hS
  obtain ⟨q', -, hu', hi', ha', -, hm⟩ := h diffWitness overSchema_diffWitness
    usesOnly_diffWitness ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
  obtain ⟨-, he⟩ := hm dDiffXY (fun _ => 0) ⟨trivial, trivial⟩
  have hmem : ((((fun _ => 0) : Tuple ℕ 1),
      MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 1) : AnnotatedTuple ℕ PolyXY 1)
      ∈ q'.evaluateAnnotated dDiffXY (fun _ => 0) := by
    rw [he, evaluateAnnotated_diffWitness_xy]
    exact Multiset.mem_singleton_self _
  obtain ⟨r, hr, hre⟩ := Multiset.mem_map.1 hmem
  have hz := (annIn_evaluate PolyXY.annClosed_xLeY hS dDiffXY_xLeY q' hu' hi' ha'
    (fun _ => 0) {} (fun k => k.elim0) (fun p hp => absurd hp List.not_mem_nil)
    r hr).finalize PolyXY.annClosed_xLeY
  have hfin : r.snd.finalize = MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 1 :=
    congrArg Prod.snd hre
  rw [hfin] at hz
  exact not_xLeY_x hz

/-! ## The class, and the basis theorem -/

/-- **The m-semirings the basis theorem is about**: `δ` the support map
with linear set recursions settling within twice the size of their tuple
set, or `δ` the identity. -/
def AnnBasisClass (K : Type) [CommSemiringWithMonus K] : Prop :=
  ((∀ a : K, a ≠ 0 → SemiringWithMonus.delta a = 1) ∧ PathSum.SettlesLinear K)
    ∨ ∀ a : K, SemiringWithMonus.delta a = a

theorem annBasisClass_nat : AnnBasisClass ℕ := by
  refine Or.inl ⟨fun a ha => ?_, Or.inl (Or.inr ⟨fun _ _ h => add_eq_left.mp h, inferInstance⟩)⟩
  have := SemiringWithMonus.delta_natCast_pos (α := ℕ) (Nat.pos_of_ne_zero ha)
  rwa [Nat.cast_id] at this

theorem annBasisClass_polyXY : AnnBasisClass PolyXY := by
  refine Or.inl ⟨fun a ha => ?_, Or.inl PolyXY.settlesEarly⟩
  rw [PolyXY.delta_eq, ite_eq_right ha]

/-- **In the lineage semiring `⊗` is `⊕` on non-zero values**, both being
union, and `⊕` is idempotent. -/
theorem Which.unionLike {α : Type} [DecidableEq α] : PathSum.UnionLike (Which α) := by
  refine ⟨fun a => ?_, fun a b ha hb => ?_⟩
  · cases a with
    | wbot => rfl
    | wset s => show Which.wset (s ∪ s) = Which.wset s; rw [Finset.union_self]
  · cases a with
    | wbot => exact absurd rfl ha
    | wset s =>
      cases b with
      | wbot => exact absurd rfl hb
      | wset t => rfl

/-- **The lineage semiring is in the class**: `δ` is the support map, and `⊗`
is `⊕` on non-zero values. -/
theorem annBasisClass_which {α : Type} [DecidableEq α] : AnnBasisClass (Which α) := by
  refine Or.inl ⟨fun a ha => ?_, Or.inr Which.unionLike⟩
  cases a with
  | wbot => exact absurd rfl ha
  | wset s => rfl

/-- **The nine classes generate the annotated algebra over every semiring
of the class.** -/
theorem generatesAnn_annEpsOps_of_class {T : Type} [ValueType T] {K : Type}
    [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] (hK : AnnBasisClass K)
    (sch : Schema) (cnt : SeqAggFunc T) : GeneratesAnn T K sch cnt annEpsOps := by
  rcases hK with ⟨hδ, hR⟩ | hδ
  · exact generatesAnn_annEpsOps_of_support sch cnt hδ hR
  · exact generatesAnn_annEpsOps_of_delta_id sch cnt hδ

/-- **No proper subset of the nine classes generates the annotated algebra
over every semiring of the class**, with the counting aggregate: `ℕ`
carries every row but the difference's, which `ℕ[x, y]` carries. -/
theorem annEpsOps_minimal_in_class {S : Set OpKind} (hS : S ⊆ annEpsOps)
    (h : ∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
      AnnBasisClass K → ∀ sch : Schema, GeneratesAnn ℕ K sch SeqAggFunc.count S) :
    S = annEpsOps := by
  have hN := h ℕ annBasisClass_nat
  have hP := h PolyXY annBasisClass_polyXY
  refine Set.Subset.antisymm hS fun x hx => ?_
  have hout : ∀ y, y ∈ S → y ∉ annEpsOps → False := fun y hy hn => hn (hS hy)
  obtain ⟨he, hp, hg, hmu, hw, hsel, hpa⟩ := required_mem_of_generatesAnn hN
  cases x with
  | empty => exact he
  | proj => exact hp
  | sel => exact hsel
  | prod => exact absurd hx (by simp [annEpsOps])
  | apply =>
    rcases hpa with h | h
    · exact (hout _ h (by simp [annEpsOps])).elim
    · exact h
  | union => exact absurd hx (by simp [annEpsOps])
  | dedup =>
    rcases dedup_or_muSet_mem_of_generatesAnn (hN schemaR) with h | h
    · exact h
    · exact (hout _ h (by simp [annEpsOps])).elim
  | diff => exact diff_mem_of_generatesAnn_xy (hP schemaRS)
  | gamma => exact hg
  | win => exact hw
  | muBag => exact hmu
  | muSet => exact absurd hx (by simp [annEpsOps])

/-- **The annotated basis theorem over the class**: the nine classes
generate the annotated algebra over every semiring of `AnnBasisClass`, and
no proper subset of them does over all of those semirings. -/
theorem annEpsOps_isBasis_in_class :
    (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
      AnnBasisClass K → ∀ sch : Schema, GeneratesAnn ℕ K sch SeqAggFunc.count annEpsOps)
    ∧ ∀ S ⊆ annEpsOps,
      (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
        AnnBasisClass K → ∀ sch : Schema, GeneratesAnn ℕ K sch SeqAggFunc.count S) →
      S = annEpsOps :=
  ⟨fun _ _ _ _ hK sch => generatesAnn_annEpsOps_of_class hK sch _,
    fun _ hS h => annEpsOps_minimal_in_class hS h⟩
