/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import DescriptiveComplexity.Decoding
import DescriptiveComplexity.Encoding.BinarySubsetSum
import DescriptiveComplexity.Problems.Knapsack
import Provenance.Having
import Provenance.Semirings.BoolFunc
import Provenance.Semirings.How

/-!
# NP-completeness of deciding non-zero `HAVING` provenance

Deciding whether the provenance of a `HAVING SUM` query over an `ℕ[X]`- or
`𝔹[X]`-instance is non-`𝟘` is NP-complete, already in data complexity: the
query `SELECT DISTINCT 1 FROM R GROUP BY b HAVING SUM(v) = b` is fixed and
only the instance varies.

The development is in three parts.

* The **bridges** (`havingSumProv_ne_zero_iff`,
  `havingSumProvBool_ne_zero_iff`): over `ℕ[X] = MvPolynomial X ℕ` and over
  `𝔹[X] = BoolFunc X`, with pairwise distinct variables as annotations, the
  possible-world provenance of `SUM(t) = B` on a group `U` is non-`𝟘`
  exactly when some non-empty `W ⊆ U` satisfies `∑ i ∈ W, t i = B`. Over
  `ℕ[X]` the monus factor of a world annotation collapses to `𝟙` and the
  surviving monomials are pairwise distinct, so no cancellation occurs;
  over `𝔹[X]` the valuation realizing exactly the occurrences of a
  witnessing world satisfies the provenance, whose satisfiability is
  non-`𝟘`-ness.
* The **complexity** half: that combinatorial condition, read off a
  `Language.binWeights` structure, is a decision problem `HavingSumNonzero`,
  and it is NP-complete. Hardness is an FO reduction from `Knapsack`
  (subset-sum with binary weights), so it is stronger than a Karp reduction.
* The **encoding** half, which joins the two: a concrete group is a list of
  aggregate values and a constant, encoded by
  `DescriptiveComplexity.binarySubsetSumEncoding`, whose declared size is the
  total *bit length* and whose no-padding/no-compression bounds are discharged
  at construction. `havingSumNonzeroHow_faithful` and
  `havingSumNonzeroBool_faithful` prove that `HavingSumNonzero` computes
  exactly non-zero provenance on every encoded group, and
  `exists_concreteNonemptySubsetSum_iff` – through the computable decoder of
  `DescriptiveComplexity.bwDecode` – that *every* structure is such a group,
  so both halves of the NP-completeness below are statements about concrete
  groups.

That last half is not bookkeeping. Values written in *unary* would make the
problem tractable – `Provenance.Algorithms.SumDP` is the very dynamic program
that solves it, and `DescriptiveComplexity.no_unary_encoding` shows the size
bounds reject that reading – so the representation is part of the statement,
and the encoding is where it is pinned down.

Hardness is a *padding* interpretation: keep the instance and add one
weight-zero item per element of the universe. Those items change no reachable
total, but they make a solution non-empty, which is what the possible-world
semantics requires: `Having.havingProv` sums over the *non-empty* sub-worlds
of a group only.

## Main results

* `havingSumProv_ne_zero_iff`, `havingSumProvBool_ne_zero_iff` – the two
  bridges;
* `HavingSumNonzero` – the bundled decision problem;
* `hasNonemptySubsetSum_iff` – it is `Knapsack` cut down by one FO sentence;
* `knapsack_fo_reduction_havingSumNonzero` – the padding FO reduction;
* **`havingSumNonzero_NP_complete`** – NP-completeness, in data
  complexity;
* `havingSumNonzeroHow_faithful`, `havingSumNonzeroBool_faithful` – the
  encoding of concrete groups is faithful, which carries *membership* to
  concrete groups;
* `havingSumNonzeroDecoding` and `exists_concreteNonemptySubsetSum_iff` – the
  computable decoding back, which carries *hardness*: the problem is nowhere
  hard on structures that are not groups.
-/

namespace Provenance.Complexity

open Finset MvPolynomial

/-! ### Step 1: the provenance of a `HAVING SUM` predicate -/

section Provenance

variable {ι K : Type} [DecidableEq ι] [CommSemiringWithMonus K]

/-- Provenance of `HAVING SUM(t) = B` on the group of occurrences `U`, in the
possible-world semantics: the `⊕`-sum, over the non-empty worlds whose
aggregate equals `B`, of the world annotations `Having.T`. -/
noncomputable def havingSumProv (α : ι → K) (U : Finset ι) (t : ι → ℕ) (B : ℕ) : K :=
  ∑ W ∈ U.powerset.filter (fun W => W.Nonempty ∧ ∑ i ∈ W, t i = B), Having.T α U W

end Provenance

/-! ### Step 2: `ℕ[X]` with distinct variables – no cancellation -/

section How

variable {ι X : Type} [DecidableEq ι] [DecidableEq X]

/-- The exponent vector of a world: with pairwise distinct variables, the
annotation `A_W` is the monomial with this exponent. -/
noncomputable def expo (x : ι → X) (W : Finset ι) : X →₀ ℕ :=
  ∑ i ∈ W, Finsupp.single (x i) 1

theorem expo_apply (x : ι → X) (hx : Function.Injective x) (W : Finset ι) (j : ι) :
    (expo x W) (x j) = if j ∈ W then 1 else 0 := by
  classical
  unfold expo
  rw [Finset.sum_apply']
  simp [Finsupp.single_apply, hx.eq_iff, Finset.sum_ite_eq']

/-- Distinct worlds carry distinct exponent vectors. -/
theorem expo_inj (x : ι → X) (hx : Function.Injective x) :
    Function.Injective (expo x) := by
  intro W W' h
  ext j
  have := congrArg (fun f => f (x j)) h
  simp only [expo_apply x hx] at this
  by_cases hj : j ∈ W <;> by_cases hj' : j ∈ W' <;> simp_all

/-- With pairwise distinct variables, `A_W` is a single monomial. -/
theorem A_eq_monomial (x : ι → X) (W : Finset ι) :
    Having.A (fun i => (MvPolynomial.X (x i) : MvPolynomial X ℕ)) W
      = monomial (expo x W) 1 := by
  classical
  unfold Having.A expo
  induction W using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
        show (MvPolynomial.X (x a) : MvPolynomial X ℕ)
            = monomial (Finsupp.single (x a) 1) 1 from rfl,
        monomial_mul, one_mul]

/-- The monus factor of a world annotation collapses: the subtracted
one-step extensions of `W` are monomials of degree `|W| + 1`, so they do not
meet the support of `A_W`. -/
theorem T_eq_A (x : ι → X) (hx : Function.Injective x) (U W : Finset ι) :
    Having.T (fun i => (MvPolynomial.X (x i) : MvPolynomial X ℕ)) U W
      = Having.A (fun i => (MvPolynomial.X (x i) : MvPolynomial X ℕ)) W := by
  classical
  ext m
  rw [Having.T, coeff_sub, A_eq_monomial]
  have hsum : (∑ y ∈ U \ W, Having.A (fun i => (MvPolynomial.X (x i) : MvPolynomial X ℕ))
                (insert y W)).coeff m
      = ∑ y ∈ U \ W, (if expo x (insert y W) = m then (1:ℕ) else 0) := by
    rw [MvPolynomial.coeff_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [A_eq_monomial, MvPolynomial.coeff_monomial]
  rw [hsum, MvPolynomial.coeff_monomial]
  by_cases hm : expo x W = m
  · subst hm
    have hzero : ∀ y ∈ U \ W, (if expo x (insert y W) = expo x W then (1:ℕ) else 0) = 0 := by
      intro y hy
      have hyW : y ∉ W := (Finset.mem_sdiff.mp hy).2
      have hne : insert y W ≠ W := fun h => hyW (h ▸ Finset.mem_insert_self y W)
      exact if_neg fun h => hne (expo_inj x hx h)
    rw [Finset.sum_congr rfl hzero]
    simp
  · simp [hm]

/-- **The bridge.** Over `ℕ[X]` with pairwise distinct variables as
annotations, the possible-world provenance of `SUM(t) = B` on a group `U` is
non-`𝟘` exactly when some non-empty sub-world of `U` has aggregate `B`. -/
theorem havingSumProv_ne_zero_iff (x : ι → X) (hx : Function.Injective x)
    (U : Finset ι) (t : ι → ℕ) (B : ℕ) :
    havingSumProv (fun i => (MvPolynomial.X (x i) : MvPolynomial X ℕ)) U t B ≠ 0
      ↔ ∃ W ⊆ U, W.Nonempty ∧ ∑ i ∈ W, t i = B := by
  classical
  set P : Finset ι → Prop := fun W => W.Nonempty ∧ ∑ i ∈ W, t i = B with hP
  have hrw : ∀ W ∈ U.powerset.filter P,
      Having.T (fun i => (MvPolynomial.X (x i) : MvPolynomial X ℕ)) U W
        = monomial (expo x W) 1 := fun W _ => by rw [T_eq_A x hx, A_eq_monomial]
  rw [havingSumProv, Finset.sum_congr rfl hrw]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hempty : U.powerset.filter P = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun W hW =>
        fun hPW => (hc W (Finset.mem_powerset.mp hW) hPW.1) hPW.2
    rw [hempty] at h
    simp at h
  · rintro ⟨W₀, hW₀U, hW₀P⟩
    have hmem : W₀ ∈ U.powerset.filter P :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hW₀U, hW₀P⟩
    intro h
    have hco := congrArg (fun p => MvPolynomial.coeff (expo x W₀) p) h
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_zero] at hco
    have key : (∑ W ∈ U.powerset.filter P, (if expo x W = expo x W₀ then (1:ℕ) else 0))
        = ∑ W ∈ U.powerset.filter P, (if W = W₀ then (1:ℕ) else 0) := by
      refine Finset.sum_congr rfl fun W _ => ?_
      by_cases hW : W = W₀
      · simp [hW]
      · rw [if_neg fun hh => hW (expo_inj x hx hh), if_neg hW]
    rw [key] at hco
    simp [Finset.sum_ite_eq', hmem] at hco

end How

/-! ### Step 2': `𝔹[X]` with distinct variables – the same characterization -/

section BoolProv

variable {ι X : Type} [DecidableEq ι] [DecidableEq X]

omit [DecidableEq X] in
private lemma boolFunc_sum_eval (J : Finset ι) (β : ι → BoolFunc X)
    (v : X → Bool) :
    (∑ i ∈ J, β i) v = true ↔ ∃ i ∈ J, β i v = true := by
  classical
  induction J using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    exact iff_of_false (fun h => Bool.noConfusion h)
      (fun ⟨i, hi, _⟩ => absurd hi (Finset.notMem_empty i))
  | insert i J hi ih =>
    rw [Finset.sum_insert hi]
    show (β i v || (∑ j ∈ J, β j) v) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨i, Finset.mem_insert_self i J, h⟩
      · exact ⟨j, Finset.mem_insert_of_mem hj, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Finset.mem_insert.mp hj with rfl | hjJ
      · exact Or.inl h
      · exact Or.inr ⟨j, hjJ, h⟩

omit [DecidableEq X] in
private lemma boolFunc_prod_eval (J : Finset ι) (β : ι → BoolFunc X)
    (v : X → Bool) :
    (∏ i ∈ J, β i) v = true ↔ ∀ i ∈ J, β i v = true := by
  classical
  induction J using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact iff_of_true rfl fun i hi => absurd hi (Finset.notMem_empty i)
  | insert i J hi ih =>
    rw [Finset.prod_insert hi]
    show (β i v && (∏ j ∈ J, β j) v) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h₁, h₂⟩ j hj
      rcases Finset.mem_insert.mp hj with rfl | hjJ
      · exact h₁
      · exact h₂ j hjJ
    · intro h
      exact ⟨h i (Finset.mem_insert_self i J),
        fun j hj => h j (Finset.mem_insert_of_mem hj)⟩

/-- **The bridge, over `𝔹[X]`.** With pairwise distinct variables as
annotations, the possible-world provenance of `SUM(t) = B` on a group `U`
is non-`𝟘` in `𝔹[X]` exactly when some non-empty sub-world of `U` has
aggregate `B`: the valuation making true exactly the variables of a
witnessing world satisfies precisely that world's annotation. The
combinatorial characterization is the same as over `ℕ[X]`
(`havingSumProv_ne_zero_iff`), so the NP-completeness of the underlying
decision problem covers both semirings. -/
theorem havingSumProvBool_ne_zero_iff (x : ι → X) (hx : Function.Injective x)
    (U : Finset ι) (t : ι → ℕ) (B : ℕ) :
    havingSumProv (fun i => BoolFunc.var (x i)) U t B ≠ 0
      ↔ ∃ W ⊆ U, W.Nonempty ∧ ∑ i ∈ W, t i = B := by
  classical
  constructor
  · intro h
    have hex : ∃ v : X → Bool,
        havingSumProv (fun i => BoolFunc.var (x i)) U t B v = true := by
      by_contra hc
      push Not at hc
      exact h (funext fun v => Bool.eq_false_iff.mpr (hc v))
    obtain ⟨v, hv⟩ := hex
    rw [havingSumProv] at hv
    obtain ⟨W, hWmem, -⟩ := (boolFunc_sum_eval _ _ v).mp hv
    obtain ⟨hWpow, hWP⟩ := Finset.mem_filter.mp hWmem
    exact ⟨W, Finset.mem_powerset.mp hWpow, hWP.1, hWP.2⟩
  · rintro ⟨W₀, hW₀U, hW₀ne, hW₀sum⟩
    intro h
    set v : X → Bool := fun y => decide (∃ i ∈ W₀, x i = y) with hvdef
    have hA : (Having.A (fun i => BoolFunc.var (x i)) W₀) v = true :=
      (boolFunc_prod_eval _ _ v).mpr fun i hi => by
        show v (x i) = true
        rw [hvdef]
        exact decide_eq_true ⟨i, hi, rfl⟩
    have hSub : ((∑ y ∈ U \ W₀,
        Having.A (fun i => BoolFunc.var (x i)) (insert y W₀)) v) = false := by
      cases hb : ((∑ y ∈ U \ W₀,
          Having.A (fun i => BoolFunc.var (x i)) (insert y W₀)) v) with
      | false => rfl
      | true =>
        obtain ⟨y, hy, hyv⟩ := (boolFunc_sum_eval _ _ v).mp hb
        have hyx : v (x y) = true :=
          (boolFunc_prod_eval _ _ v).mp hyv y (Finset.mem_insert_self y W₀)
        rw [hvdef] at hyx
        obtain ⟨j, hjW, hjx⟩ := of_decide_eq_true hyx
        exact absurd (hx hjx ▸ hjW) (Finset.mem_sdiff.mp hy).2
    have hT : (Having.T (fun i => BoolFunc.var (x i)) U W₀) v = true := by
      show ((Having.A (fun i => BoolFunc.var (x i)) W₀) v
        && !((∑ y ∈ U \ W₀,
              Having.A (fun i => BoolFunc.var (x i)) (insert y W₀)) v)) = true
      rw [hA, hSub]
      rfl
    have hmem : W₀ ∈ U.powerset.filter
        (fun W => W.Nonempty ∧ ∑ i ∈ W, t i = B) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hW₀U, hW₀ne, hW₀sum⟩
    have htrue : (havingSumProv (fun i => BoolFunc.var (x i)) U t B) v = true := by
      rw [havingSumProv]
      exact (boolFunc_sum_eval _ _ v).mpr ⟨W₀, hmem, hT⟩
    rw [h] at htrue
    exact Bool.noConfusion htrue

end BoolProv

/-! ### Step 3: the decision problem and its membership in NP -/

open DescriptiveComplexity FirstOrder Language Structure

section Problem
variable (A : Type) [Language.binWeights.Structure A]

/-- Some **non-empty** set of items has weights summing to the target. -/
def HasNonemptySubsetSum : Prop :=
  Finite A ∧ IsLinOrd (BWLe (A := A)) ∧
    ∃ S : A → Prop, (∃ i, S i) ∧ (∀ i, S i → BWItem i) ∧
      (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A

end Problem

section Iso
variable {A B : Type} [Language.binWeights.Structure A] [Language.binWeights.Structure B]

private theorem hasNonemptySubsetSum_of_iso (e : A ≃[Language.binWeights] B)
    (h : HasNonemptySubsetSum A) : HasNonemptySubsetSum B := by
  obtain ⟨hfin, hlin, S, ⟨i₀, hi₀⟩, hSi, hsum⟩ := h
  have hle : ∀ a a' : A, BWLe a a' ↔ BWLe (e a) (e a') := fun a a' => relMap_equiv₂ e bwLe a a'
  have hposn : ∀ a : A, BWPosn a ↔ BWPosn (e a) := fun a => relMap_equiv₁ e bwPosn a
  have hitem : ∀ a : A, BWItem a ↔ BWItem (e a) := fun a => relMap_equiv₁ e bwItem a
  have htgt : ∀ a : A, BWTgt a ↔ BWTgt (e a) := fun a => relMap_equiv₁ e bwTgt a
  have hbit : ∀ a a' : A, BWBit a a' ↔ BWBit (e a) (e a') := fun a a' => relMap_equiv₂ e bwBit a a'
  refine ⟨e.toEquiv.finite_iff.mp hfin, IsLinOrd.of_equiv e.toEquiv hle hlin,
    fun b => S (e.toEquiv.symm b), ⟨e.toEquiv i₀, by simpa using hi₀⟩, fun b hb => ?_, ?_⟩
  · have hb' : e.toEquiv (e.toEquiv.symm b) = b := e.toEquiv.apply_symm_apply b
    rw [← hb']
    exact (hitem _).mp (hSi _ hb)
  · have hw : ∀ a : A, BWWeight a = BWWeight (e a) := fun a =>
      binNum_equiv e.toEquiv hle hposn (hbit a)
    have htarget : BWTarget A = BWTarget B := binNum_equiv e.toEquiv hle hposn htgt
    rw [← htarget, ← hsum]
    refine (finsum_mem_eq_of_bijOn e.toEquiv ?_ fun a _ => hw a).symm
    refine ⟨fun a ha => ?_, e.toEquiv.injective.injOn,
      fun b hb => ⟨e.toEquiv.symm b, hb, e.toEquiv.apply_symm_apply b⟩⟩
    simpa using ha

theorem hasNonemptySubsetSum_iso (e : A ≃[Language.binWeights] B) :
    HasNonemptySubsetSum A ↔ HasNonemptySubsetSum B :=
  ⟨hasNonemptySubsetSum_of_iso e, hasNonemptySubsetSum_of_iso e.symm⟩

end Iso

/-- The decision problem behind the NP-completeness of non-zero `HAVING SUM`
provenance: the isomorphism-invariant bundling of `HasNonemptySubsetSum`. -/
def HavingSumNonzero : DecisionProblem Language.binWeights where
  Holds := fun A inst => @HasNonemptySubsetSum A inst
  iso_invariant := fun e => hasNonemptySubsetSum_iso e

open DescriptiveComplexity FirstOrder Language Structure

/-- The target is non-zero. -/
noncomputable def targetNonzeroF : Language.binWeights.Sentence :=
  Formula.iExs (Fin 1)
    (Relations.formula₁ bwPosn (Term.var (Sum.inr 0)) ⊓
      Relations.formula₁ bwTgt (Term.var (Sum.inr 0)))

/-- Some item has weight zero. -/
noncomputable def zeroItemF : Language.binWeights.Sentence :=
  Formula.iExs (Fin 1)
    (Relations.formula₁ bwItem (Term.var (Sum.inr 0)) ⊓
      Formula.iAlls Unit
        ((Relations.formula₁ bwPosn (Term.var (Sum.inr ()))).imp
          (∼(Relations.formula₂ bwBit (Term.var (Sum.inl (Sum.inr 0)))
              (Term.var (Sum.inr ()))))))

noncomputable def hsnSentence : Language.binWeights.Sentence := targetNonzeroF ⊔ zeroItemF

theorem realize_hsnSentence (A : Type) [Language.binWeights.Structure A] :
    Sentence.Realize (M := A) hsnSentence ↔
      ((∃ p : A, BWPosn p ∧ BWTgt p) ∨
        ∃ i : A, BWItem i ∧ ∀ p : A, BWPosn p → ¬BWBit i p) := by
  simp only [hsnSentence, targetNonzeroF, zeroItemF, Sentence.Realize,
    Formula.realize_sup, Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
    Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_rel₁, Formula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, BWPosn, BWTgt, BWItem, BWBit]
  constructor
  · rintro (⟨w, h1, h2⟩ | ⟨w, h1, h2⟩)
    · exact Or.inl ⟨w 0, h1, h2⟩
    · exact Or.inr ⟨w 0, h1, fun p hp => h2 (fun _ => p) hp⟩
  · rintro (⟨p, h1, h2⟩ | ⟨i, h1, h2⟩)
    · exact Or.inl ⟨fun _ => p, h1, h2⟩
    · exact Or.inr ⟨fun _ => i, h1, fun q hq => h2 (q ()) hq⟩
open DescriptiveComplexity FirstOrder Language Structure

variable {A : Type} [Language.binWeights.Structure A]

theorem binNum_eq_zero_iff [Finite A] (hlin : IsLinOrd (BWLe (A := A))) (b : A → Prop) :
    binNum (BWLe (A := A)) BWPosn b = 0 ↔ ∀ p, BWPosn p → ¬b p := by
  constructor
  · intro h p hp hb
    exact (binNum_inj_on hlin _ BWPosn rfl b (fun _ => False) (by rw [h, binNum_bot]) p hp).mp hb
  · intro h
    rw [binNum_congr_on (b' := fun _ => False) fun p hp => ⟨fun hb => h p hp hb, False.elim⟩,
      binNum_bot]

/-- A single selected item's weight is at most the total. -/
theorem weight_le_sum [Finite A] {S : A → Prop} {i₀ : A} (hi₀ : S i₀) :
    BWWeight i₀ ≤ ∑ᶠ i ∈ {i | S i}, BWWeight i := by
  classical
  have hset : {i : A | S i} = {i₀} ∪ {i : A | S i ∧ i ≠ i₀} := by
    ext i; constructor
    · intro hi; by_cases h : i = i₀
      · exact Or.inl h
      · exact Or.inr ⟨hi, h⟩
    · rintro (h | ⟨h, -⟩)
      · exact h ▸ hi₀
      · exact h
  have hdisj : Disjoint ({i₀} : Set A) {i : A | S i ∧ i ≠ i₀} := by
    rw [Set.disjoint_left]; rintro a rfl ⟨-, h⟩; exact h rfl
  rw [hset, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _), finsum_mem_singleton]
  exact Nat.le_add_right _ _
/-- `HavingSumNonzero` is `Knapsack` cut down by one first-order sentence:
a solution can be taken non-empty exactly when the target is non-zero (any
solution is then non-empty) or some item has weight zero (which can be added
to a solution). -/
theorem hasNonemptySubsetSum_iff [Finite A] :
    HasNonemptySubsetSum A ↔ (Sentence.Realize (M := A) hsnSentence ∧ HasSubsetSum A) := by
  rw [realize_hsnSentence]
  constructor
  · rintro ⟨hfin, hlin, S, ⟨i₀, hi₀⟩, hSi, hsum⟩
    refine ⟨?_, hfin, hlin, S, hSi, hsum⟩
    by_cases htgt : BWTarget A = 0
    · refine Or.inr ⟨i₀, hSi i₀ hi₀, ?_⟩
      have hw : BWWeight i₀ = 0 :=
        Nat.le_zero.mp (by rw [← htgt, ← hsum]; exact weight_le_sum hi₀)
      exact (binNum_eq_zero_iff hlin (BWBit i₀)).mp hw
    · refine Or.inl ?_
      by_contra hc
      push Not at hc
      exact htgt ((binNum_eq_zero_iff hlin BWTgt).mpr fun p hp => hc p hp)
  · rintro ⟨hphi, hfin, hlin, S, hSi, hsum⟩
    by_cases hne : ∃ i, S i
    · exact ⟨hfin, hlin, S, hne, hSi, hsum⟩
    · push Not at hne
      have hempty : {i : A | S i} = (∅ : Set A) := by ext i; simp [hne i]
      have htgt : BWTarget A = 0 := by rw [← hsum, hempty, finsum_mem_empty]
      rcases hphi with ⟨p, hp, htg⟩ | ⟨i₀, hitem, hbits⟩
      · exact absurd ((binNum_eq_zero_iff hlin BWTgt).mp htgt p hp) (not_not.mpr htg)
      · refine ⟨hfin, hlin, (· = i₀), ⟨i₀, rfl⟩, fun i hi => hi ▸ hitem, ?_⟩
        have hs : {i : A | i = i₀} = ({i₀} : Set A) := by ext i; simp
        rw [hs, finsum_mem_singleton, htgt]
        exact (binNum_eq_zero_iff hlin (BWBit i₀)).mpr hbits

/-- `HavingSumNonzero` is in NP: it is `Knapsack`, whose `Σ₁` definition is
the binary adder of `knapsackKernel`, conjoined with a first-order sentence. -/
theorem havingSumNonzero_mem_NP : HavingSumNonzero ∈ NP := by
  have h : (DecisionProblem.ofSentence hsnSentence ⊓ Knapsack) ∈ NP :=
    knapsack_sigmaSODefinable.inf_ofSentence hsnSentence
  exact (NP.mem_congr_finite (fun A _ _ => hasNonemptySubsetSum_iff)).mpr h


/-! ### Step 4: NP-hardness, by FO reduction from `Knapsack` -/

/-- Tags of the padding interpretation: the original instance, plus a copy of
the universe turned into items of weight zero. -/
inductive HTag : Type
  | orig
  | pad
  deriving DecidableEq

instance : Fintype HTag := ⟨{HTag.orig, HTag.pad}, fun t => by cases t <;> decide⟩
instance : Nonempty HTag := ⟨HTag.orig⟩

namespace HRed

def hItemF : HTag → Language.binWeights.Formula (Fin 1 × Fin 1)
  | .orig => Relations.formula₁ bwItem (Term.var (0, 0))
  | .pad => ⊤

def hPosnF : HTag → Language.binWeights.Formula (Fin 1 × Fin 1)
  | .orig => Relations.formula₁ bwPosn (Term.var (0, 0))
  | .pad => ⊥

def hTgtF : HTag → Language.binWeights.Formula (Fin 1 × Fin 1)
  | .orig => Relations.formula₁ bwTgt (Term.var (0, 0))
  | .pad => ⊥

def hBitF : HTag → HTag → Language.binWeights.Formula (Fin 2 × Fin 1)
  | .orig, .orig => Relations.formula₂ bwBit (Term.var (0, 0)) (Term.var (1, 0))
  | _, _ => ⊥

def hLeF : HTag → HTag → Language.binWeights.Formula (Fin 2 × Fin 1)
  | .orig, .pad => ⊤
  | .pad, .orig => ⊥
  | _, _ => Relations.formula₂ bwLe (Term.var (0, 0)) (Term.var (1, 0))

/-- The padding interpretation: keep the instance, and add one weight-zero
item per element of the universe. -/
def hInterp : FOInterpretation Language.binWeights Language.binWeights HTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .item => fun t => hItemF (t 0)
    | _, .posn => fun t => hPosnF (t 0)
    | _, .bit  => fun t => hBitF (t 0) (t 1)
    | _, .tgt  => fun t => hTgtF (t 0)
    | _, .le   => fun t => hLeF (t 0) (t 1)

variable {A : Type} [Language.binWeights.Structure A]

/-- A point of the interpreted universe. -/
def hPt (t : HTag) (a : A) : hInterp.Map A := (t, fun _ => a)

omit [Language.binWeights.Structure A] in
theorem hPt_surj (q : hInterp.Map A) : ∃ t a, q = hPt t a := by
  obtain ⟨t, w⟩ := q
  refine ⟨t, w 0, ?_⟩
  simp only [hPt]
  congr 1
  exact funext fun i => by fin_cases i; rfl

omit [Language.binWeights.Structure A] in
theorem hPt_inj {t t' : HTag} {a a' : A} : hPt t a = hPt t' a' ↔ t = t' ∧ a = a' := by
  constructor
  · intro h
    rw [hPt, hPt, Prod.mk.injEq] at h
    exact ⟨h.1, congrFun h.2 0⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem bwItem_orig (a : A) : BWItem (hPt .orig a) ↔ BWItem a := by
  rw [BWItem, hPt, FOInterpretation.relMap_map]; simp [hInterp, hItemF, BWItem]

@[simp] theorem bwItem_pad (a : A) : BWItem (hPt .pad a) := by
  rw [BWItem, hPt, FOInterpretation.relMap_map]; simp [hInterp, hItemF]

@[simp] theorem bwPosn_orig (a : A) : BWPosn (hPt .orig a) ↔ BWPosn a := by
  rw [BWPosn, hPt, FOInterpretation.relMap_map]; simp [hInterp, hPosnF, BWPosn]

@[simp] theorem bwPosn_pad (a : A) : ¬BWPosn (hPt .pad a) := by
  rw [BWPosn, hPt, FOInterpretation.relMap_map]; simp [hInterp, hPosnF]

@[simp] theorem bwTgt_orig (a : A) : BWTgt (hPt .orig a) ↔ BWTgt a := by
  rw [BWTgt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hTgtF, BWTgt]

@[simp] theorem bwTgt_pad (a : A) : ¬BWTgt (hPt .pad a) := by
  rw [BWTgt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hTgtF]

@[simp] theorem bwBit_orig_orig (a b : A) :
    BWBit (hPt .orig a) (hPt .orig b) ↔ BWBit a b := by
  rw [BWBit, hPt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hBitF, BWBit]

@[simp] theorem bwBit_pad_left (t : HTag) (a b : A) : ¬BWBit (hPt .pad a) (hPt t b) := by
  rw [BWBit, hPt, hPt, FOInterpretation.relMap_map]; cases t <;> simp [hInterp, hBitF]

@[simp] theorem bwBit_orig_pad (a b : A) : ¬BWBit (hPt .orig a) (hPt .pad b) := by
  rw [BWBit, hPt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hBitF]



@[simp] theorem bwLe_orig_orig (a b : A) :
    BWLe (hPt .orig a) (hPt .orig b) ↔ BWLe a b := by
  rw [BWLe, hPt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hLeF, BWLe]

@[simp] theorem bwLe_pad_pad (a b : A) :
    BWLe (hPt .pad a) (hPt .pad b) ↔ BWLe a b := by
  rw [BWLe, hPt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hLeF, BWLe]

@[simp] theorem bwLe_orig_pad (a b : A) : BWLe (hPt .orig a) (hPt .pad b) := by
  rw [BWLe, hPt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hLeF]

@[simp] theorem bwLe_pad_orig (a b : A) : ¬BWLe (hPt .pad a) (hPt .orig b) := by
  rw [BWLe, hPt, hPt, FOInterpretation.relMap_map]; simp [hInterp, hLeF]

omit [Language.binWeights.Structure A] in
theorem hPt_orig_inj : Function.Injective (hPt (A := A) .orig) :=
  fun _ _ h => (hPt_inj.mp h).2

/-- Positions live only in the original copy. -/
theorem posn_image (bm : hInterp.Map A → Prop) :
    {q : hInterp.Map A | BWPosn q ∧ bm q}
      = hPt .orig '' {a : A | BWPosn a ∧ bm (hPt .orig a)} := by
  ext q
  obtain ⟨t, a, rfl⟩ := hPt_surj q
  cases t
  · constructor
    · rintro ⟨hp, hb⟩
      exact ⟨a, ⟨(bwPosn_orig a).mp hp, hb⟩, rfl⟩
    · rintro ⟨c, ⟨hc, hb⟩, hEq⟩
      have hca : c = a := (hPt_inj.mp hEq).2
      rw [hca] at hc hb
      exact ⟨(bwPosn_orig a).mpr hc, hb⟩
  · constructor
    · rintro ⟨hp, -⟩; exact absurd hp (bwPosn_pad a)
    · rintro ⟨c, -, hEq⟩; exact absurd (hPt_inj.mp hEq).1 (by simp)

theorem bitRank_orig (p : A) :
    bitRank (BWLe (A := hInterp.Map A)) BWPosn (hPt .orig p)
      = bitRank (BWLe (A := A)) BWPosn p := by
  unfold bitRank
  have hset : {q : hInterp.Map A | BWPosn q ∧ BWLe q (hPt .orig p) ∧ q ≠ hPt .orig p}
      = hPt .orig '' {a : A | BWPosn a ∧ BWLe a p ∧ a ≠ p} := by
    ext q
    obtain ⟨t, a, rfl⟩ := hPt_surj q
    cases t
    · constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨a, ⟨(bwPosn_orig a).mp h1, (bwLe_orig_orig a p).mp h2,
          fun h => h3 (by rw [h])⟩, rfl⟩
      · rintro ⟨c, ⟨h1, h2, h3⟩, hEq⟩
        have hca : c = a := (hPt_inj.mp hEq).2
        rw [hca] at h1 h2 h3
        exact ⟨(bwPosn_orig a).mpr h1, (bwLe_orig_orig a p).mpr h2,
          fun h => h3 (hPt_inj.mp h).2⟩
    · constructor
      · rintro ⟨h1, -, -⟩; exact absurd h1 (bwPosn_pad a)
      · rintro ⟨c, -, hEq⟩; exact absurd (hPt_inj.mp hEq).1 (by simp)
  rw [hset, Set.ncard_image_of_injective _ hPt_orig_inj]

/-- Any binary number read off the interpreted structure is the number read
off the original one. -/
theorem binNum_map (bm : hInterp.Map A → Prop) :
    binNum (BWLe (A := hInterp.Map A)) BWPosn bm
      = binNum (BWLe (A := A)) BWPosn (fun a => bm (hPt .orig a)) := by
  unfold binNum
  rw [posn_image bm, finsum_mem_image hPt_orig_inj.injOn]
  exact finsum_mem_congr rfl fun a _ => by rw [bitRank_orig]

@[simp] theorem bwWeight_orig (a : A) : BWWeight (hPt .orig a) = BWWeight a := by
  rw [BWWeight, binNum_map]
  exact binNum_congr fun p => bwBit_orig_orig a p

@[simp] theorem bwWeight_pad (a : A) : BWWeight (hPt (A := A) .pad a) = 0 := by
  rw [BWWeight, binNum_map]
  rw [binNum_congr (b' := fun _ => False) fun p =>
    ⟨fun h => absurd h (bwBit_pad_left .orig a p), False.elim⟩, binNum_bot]

@[simp] theorem bwTarget_map : BWTarget (hInterp.Map A) = BWTarget A := by
  rw [BWTarget, BWTarget, binNum_map]
  exact binNum_congr fun p => bwTgt_orig p



/-- The padded order is the lexicographic order: linear exactly when the
original one is. -/
theorem isLinOrd_map_iff :
    IsLinOrd (BWLe (A := hInterp.Map A)) ↔ IsLinOrd (BWLe (A := A)) := by
  constructor
  · rintro ⟨hrefl, htrans, hanti, htot⟩
    refine ⟨fun a => (bwLe_orig_orig a a).mp (hrefl _), fun a b c hab hbc => ?_,
      fun a b hab hba => ?_, fun a b => ?_⟩
    · exact (bwLe_orig_orig a c).mp (htrans (hPt .orig a) (hPt .orig b) (hPt .orig c)
        ((bwLe_orig_orig a b).mpr hab) ((bwLe_orig_orig b c).mpr hbc))
    · exact (hPt_inj.mp (hanti (hPt .orig a) (hPt .orig b)
        ((bwLe_orig_orig a b).mpr hab) ((bwLe_orig_orig b a).mpr hba))).2
    · rcases htot (hPt .orig a) (hPt .orig b) with h | h
      · exact Or.inl ((bwLe_orig_orig a b).mp h)
      · exact Or.inr ((bwLe_orig_orig b a).mp h)
  · rintro ⟨hrefl, htrans, hanti, htot⟩
    refine ⟨fun q => ?_, fun q r s hqr hrs => ?_, fun q r hqr hrq => ?_, fun q r => ?_⟩
    · obtain ⟨t, a, rfl⟩ := hPt_surj q
      cases t <;> simp [hrefl a]
    · obtain ⟨t1, a, rfl⟩ := hPt_surj q
      obtain ⟨t2, b, rfl⟩ := hPt_surj r
      obtain ⟨t3, c, rfl⟩ := hPt_surj s
      cases t1 <;> cases t2 <;> cases t3 <;> simp_all <;> exact htrans _ _ _ ‹_› ‹_›
    · obtain ⟨t1, a, rfl⟩ := hPt_surj q
      obtain ⟨t2, b, rfl⟩ := hPt_surj r
      cases t1 <;> cases t2 <;> simp_all [hPt_inj] <;> exact hanti _ _ ‹_› ‹_›
    · obtain ⟨t1, a, rfl⟩ := hPt_surj q
      obtain ⟨t2, b, rfl⟩ := hPt_surj r
      cases t1 <;> cases t2 <;> simp_all



/-- Padded items weigh nothing, so a selection's total weight is that of its
original part. -/
theorem weights_split [Finite A] (S' : hInterp.Map A → Prop) :
    (∑ᶠ q ∈ {q : hInterp.Map A | S' q}, BWWeight q)
      = ∑ᶠ a ∈ {a : A | S' (hPt .orig a)}, BWWeight a := by
  classical
  have : Finite (hInterp.Map A) := hInterp.map_finite A
  have hset : {q : hInterp.Map A | S' q}
      = (hPt .orig '' {a : A | S' (hPt .orig a)})
        ∪ (hPt .pad '' {a : A | S' (hPt .pad a)}) := by
    ext q
    obtain ⟨t, a, rfl⟩ := hPt_surj q
    cases t
    · constructor
      · intro h; exact Or.inl ⟨a, h, rfl⟩
      · rintro (⟨c, hc, hEq⟩ | ⟨c, -, hEq⟩)
        · have hca : c = a := (hPt_inj.mp hEq).2
          rw [hca] at hc; exact hc
        · exact absurd (hPt_inj.mp hEq).1 (by simp)
    · constructor
      · intro h; exact Or.inr ⟨a, h, rfl⟩
      · rintro (⟨c, -, hEq⟩ | ⟨c, hc, hEq⟩)
        · exact absurd (hPt_inj.mp hEq).1 (by simp)
        · have hca : c = a := (hPt_inj.mp hEq).2
          rw [hca] at hc; exact hc
  have hdisj : Disjoint (hPt (A := A) .orig '' {a : A | S' (hPt .orig a)})
      (hPt (A := A) .pad '' {a : A | S' (hPt .pad a)}) := by
    rw [Set.disjoint_left]
    rintro q ⟨c, -, rfl⟩ ⟨d, -, hEq⟩
    exact absurd (hPt_inj.mp hEq).1 (by simp)
  have hpad : (∑ᶠ q ∈ hPt (A := A) .pad '' {a : A | S' (hPt .pad a)}, BWWeight q) = 0 := by
    rw [finsum_mem_image (fun x _ y _ h => (hPt_inj.mp h).2)]
    simp
  rw [hset, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _), hpad, add_zero,
    finsum_mem_image hPt_orig_inj.injOn]
  exact finsum_mem_congr rfl fun a _ => bwWeight_orig a



/-- **Correctness of the reduction.** Padding with weight-zero items makes a
solution non-empty without changing which totals are reachable. -/
theorem hasSubsetSum_iff_map (A : Type) [Language.binWeights.Structure A] [Nonempty A] :
    HasSubsetSum A ↔ HasNonemptySubsetSum (hInterp.Map A) := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty A›
  constructor
  · rintro ⟨hfin, hlin, S, hSi, hsum⟩
    have := hfin
    refine ⟨hInterp.map_finite A, isLinOrd_map_iff.mpr hlin,
      fun q => q.1 = HTag.pad ∨ S (q.2 0), ⟨hPt .pad a₀, Or.inl rfl⟩, ?_, ?_⟩
    · rintro q h
      obtain ⟨t, a, rfl⟩ := hPt_surj q
      cases t
      · rcases h with h | h
        · exact absurd h (by simp [hPt])
        · exact (bwItem_orig a).mpr (hSi a h)
      · exact bwItem_pad a
    · rw [weights_split, bwTarget_map, ← hsum]
      exact finsum_mem_congr (by ext a; simp [hPt]) fun _ _ => rfl
  · rintro ⟨hfin, hlin, S', -, hSi, hsum⟩
    have : Finite A := Finite.of_injective (hPt (A := A) .orig) hPt_orig_inj
    refine ⟨inferInstance, isLinOrd_map_iff.mp hlin, fun a => S' (hPt .orig a),
      fun a ha => (bwItem_orig a).mp (hSi _ ha), ?_⟩
    rw [← weights_split S', hsum, bwTarget_map]

end HRed

open HRed in
/-- **`Knapsack` FO-reduces to `HavingSumNonzero`**, so the latter is NP-hard
in data complexity: the reduction outputs an instance, the query being
fixed. -/
def knapsack_fo_reduction_havingSumNonzero : Knapsack ≤ᶠᵒ HavingSumNonzero where
  Tag := HTag
  dim := 1
  toInterpretation := hInterp
  correct A _ _ := hasSubsetSum_iff_map A

theorem havingSumNonzero_NP_hard : NP.Hard HavingSumNonzero :=
  NP.hard_of_foReduction knapsack_fo_reduction_havingSumNonzero knapsack_NP_hard

/-- **NP-completeness of non-zero `HAVING SUM` provenance**, in data
complexity: membership and FO-hardness from `Knapsack`. Read through the
bridges `havingSumProv_ne_zero_iff` and `havingSumProvBool_ne_zero_iff`, and
through the faithful encoding of Step 5 below, this is the NP-completeness of
deciding non-`𝟘` provenance of a concrete group over `ℕ[X]`- and
`𝔹[X]`-instances, the values written in binary. -/
theorem havingSumNonzero_NP_complete : NP.Complete HavingSumNonzero :=
  ⟨havingSumNonzero_mem_NP, havingSumNonzero_NP_hard⟩

/-! ### Step 5: the concrete groups the theorem is about

A `Language.binWeights` structure is not what a user has in hand: a `HAVING
SUM` group is a list of aggregate values and the constant the predicate
compares against. That is exactly
`DescriptiveComplexity.SubsetSumInstance`, and
`DescriptiveComplexity.binarySubsetSumEncoding` encodes it – with the two size
obligations, no padding and no compression, discharged at construction against
a declared size that counts *bit length*. What remains is the semantic
obligation, `DescriptiveComplexity.Encoding.Faithful`: that the decision
problem above computes non-zero provenance on every encoded group. Both
semirings get it from the same encoding, the bridges having shown they have
the same combinatorial content.
-/

section Concrete

open DescriptiveComplexity

/-- A concrete `HAVING SUM` group: the aggregate values of its occurrences,
and the constant the predicate compares against. This is literally
`DescriptiveComplexity.SubsetSumInstance`; naming it here records what the
components mean on this side of the bridge. -/
abbrev HavingSumInstance : Type := SubsetSumInstance

/-- Some non-empty sub-world of the group aggregates to the constant: the
combinatorial content the two bridges give the provenance, on concrete data.
Non-emptiness is the possible-world semantics' exclusion of the empty world,
not a technicality. -/
def ConcreteNonemptySubsetSum (i : HavingSumInstance) : Prop :=
  ∃ J : Finset (Fin i.1.length), J.Nonempty ∧ ∑ j ∈ J, i.1.get j = i.2

/-- Non-zero `HAVING SUM` provenance of a concrete group over `ℕ[X]`, its
occurrences annotated by pairwise distinct variables. -/
def HavingSumNonzeroHow (i : HavingSumInstance) : Prop :=
  havingSumProv (fun j : Fin i.1.length => (MvPolynomial.X j : MvPolynomial (Fin i.1.length) ℕ))
    Finset.univ (fun j => i.1.get j) i.2 ≠ 0

/-- Non-zero `HAVING SUM` provenance of a concrete group over `𝔹[X]`, its
occurrences annotated by pairwise distinct variables. -/
def HavingSumNonzeroBool (i : HavingSumInstance) : Prop :=
  havingSumProv (fun j : Fin i.1.length => BoolFunc.var j) Finset.univ
    (fun j => i.1.get j) i.2 ≠ 0

/-- The `⊆ univ` of the bridge is vacuous on a concrete group: its
occurrences are all of `Fin i.1.length`. -/
private theorem subsetSum_univ_iff (i : HavingSumInstance) :
    (∃ W ⊆ (Finset.univ : Finset (Fin i.1.length)), W.Nonempty ∧ ∑ j ∈ W, i.1.get j = i.2)
      ↔ ConcreteNonemptySubsetSum i := by
  constructor
  · rintro ⟨W, -, hne, hsum⟩
    exact ⟨W, hne, hsum⟩
  · rintro ⟨J, hne, hsum⟩
    exact ⟨J, Finset.subset_univ J, hne, hsum⟩

theorem havingSumNonzeroHow_iff (i : HavingSumInstance) :
    HavingSumNonzeroHow i ↔ ConcreteNonemptySubsetSum i :=
  (havingSumProv_ne_zero_iff id Function.injective_id _ _ _).trans (subsetSum_univ_iff i)

theorem havingSumNonzeroBool_iff (i : HavingSumInstance) :
    HavingSumNonzeroBool i ↔ ConcreteNonemptySubsetSum i :=
  (havingSumProvBool_ne_zero_iff id Function.injective_id _ _ _).trans (subsetSum_univ_iff i)

/-- **The problem, read along an indexing of the items.** A selection of items
is a set of indices, and conversely, with the same total and the same
emptiness – the two halves of `selection_toIndex`/`selection_ofIndex`. This
serves both the encoding (indexing by `itemPt`) and the decoding (indexing by
a listing of a presented structure's items). -/
theorem hasNonemptySubsetSum_iff_index {A : Type} [Language.binWeights.Structure A] [Finite A]
    {n : ℕ} (f : Fin n → A) (hf : Function.Injective f)
    (hrange : ∀ a, BWItem a ↔ ∃ j, f j = a) (hlin : IsLinOrd (BWLe (A := A))) :
    HasNonemptySubsetSum A
      ↔ ∃ J : Finset (Fin n), J.Nonempty ∧ ∑ j ∈ J, BWWeight (f j) = BWTarget A := by
  constructor
  · rintro ⟨-, -, S, hSne, hSi, hsum⟩
    obtain ⟨J, hJ, hne⟩ := selection_toIndex f hf hrange S hSi
    exact ⟨J, hne.mp hSne, by rw [← hJ, hsum]⟩
  · rintro ⟨J, hJne, hJ⟩
    obtain ⟨S, hSi, hsum, hne⟩ := selection_ofIndex f hf (fun j => (hrange _).mpr ⟨j, rfl⟩) J
    exact ⟨inferInstance, hlin, S, hne.mpr hJne, hSi, by rw [hsum, hJ]⟩

theorem concreteNonemptySubsetSum_iff (i : HavingSumInstance) :
    ConcreteNonemptySubsetSum i ↔ HasNonemptySubsetSum (binarySubsetSumEncoding.Univ i) := by
  refine Iff.symm ((hasNonemptySubsetSum_iff_index (BinarySubsetSum.itemPt i)
    BinarySubsetSum.itemPt_injective BinarySubsetSum.item_iff_range
    BinarySubsetSum.isLinOrd).trans ?_)
  simp only [BinarySubsetSum.weight_itemPt, BinarySubsetSum.target]
  exact Iff.rfl

/-- **The encoding is faithful, over `ℕ[X]`**: on every encoded group,
`HavingSumNonzero` computes exactly non-zero provenance of the concrete
group. With the size bounds discharged at construction, this is what makes
`havingSumNonzero_NP_complete` a statement about lists of binary-written
aggregate values – and not about the unary reading, which
`Provenance.Algorithms.SumDP` solves. -/
theorem havingSumNonzeroHow_faithful :
    binarySubsetSumEncoding.Faithful HavingSumNonzeroHow HavingSumNonzero :=
  fun i => (havingSumNonzeroHow_iff i).trans (concreteNonemptySubsetSum_iff i)

/-- **The encoding is faithful, over `𝔹[X]`**: the same encoding serves the
Boolean-function semiring, the two bridges having given the same
combinatorial characterization. -/
theorem havingSumNonzeroBool_faithful :
    binarySubsetSumEncoding.Faithful HavingSumNonzeroBool HavingSumNonzero :=
  fun i => (havingSumNonzeroBool_iff i).trans (concreteNonemptySubsetSum_iff i)

end Concrete

/-! ### Step 6: reading the hardness back on concrete groups

Faithfulness carries *membership* to concrete groups; hardness needs the
converse – that the problem is not hard only on structures no group encodes.
The decoder of `DescriptiveComplexity.bwDecode` is problem-independent, so it
serves here unchanged: only its soundness has to be restated against
`HavingSumNonzero`. There is again no junk to exclude, whence
`exists_concreteNonemptySubsetSum_iff` for every nonempty finite structure.
-/

section Decoding

open DescriptiveComplexity

/-- Reindexing a decoded weight list, for the non-empty variant. -/
theorem concreteNonemptySubsetSum_map {α : Type} (l : List α) (g : α → ℕ) (t : ℕ) :
    ConcreteNonemptySubsetSum (l.map g, t)
      ↔ ∃ J : Finset (Fin l.length), J.Nonempty ∧ ∑ j ∈ J, g (l.get j) = t := by
  have h : (l.map g).length = l.length := l.length_map g
  have key : ∀ J : Finset (Fin (l.map g).length),
      ∑ j ∈ J, (l.map g).get j = ∑ j ∈ J.map (finCongr h).toEmbedding, g (l.get j) := fun J => by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ => by simp [List.get_eq_getElem, List.getElem_map]
  change (∃ J : Finset (Fin (l.map g).length), J.Nonempty ∧ ∑ j ∈ J, (l.map g).get j = t) ↔ _
  constructor
  · rintro ⟨J, hne, hJ⟩
    exact ⟨J.map (finCongr h).toEmbedding, hne.map, (key J).symm.trans hJ⟩
  · rintro ⟨J, hne, hJ⟩
    refine ⟨J.map (finCongr h.symm).toEmbedding, hne.map, (key _).trans ?_⟩
    rw [← hJ]
    exact Finset.sum_congr (by ext j; simp) fun _ _ => rfl

/-- A group with no occurrences cannot aggregate to a positive constant – what
the decoder returns on a structure that is a no-instance for lack of a linear
order. -/
theorem not_concreteNonemptySubsetSum_empty : ¬ ConcreteNonemptySubsetSum ([], 1) := by
  rintro ⟨J, hne, -⟩
  obtain ⟨j, -⟩ := hne
  exact j.elim0

theorem bwDecode_sound_nonempty (S : FinPresentation Language.binWeights)
    (i : SubsetSumInstance) (hi : i ∈ bwDecode S) :
    ConcreteNonemptySubsetSum i ↔ HavingSumNonzero (Fin S.card) := by
  unfold bwDecode at hi
  split at hi
  · next hlin =>
    rw [Option.mem_def, Option.some.injEq] at hi
    subst hi
    rw [concreteNonemptySubsetSum_map]
    refine Iff.symm ((hasNonemptySubsetSum_iff_index (BinarySubsetSum.items S).get
      BinarySubsetSum.items_get_injective BinarySubsetSum.items_range
      ((BinarySubsetSum.isLinOrdB_iff S).mp hlin)).trans ?_)
    simp only [BinarySubsetSum.numB_bit, BinarySubsetSum.numB_tgt]
  · next hlin =>
    rw [Option.mem_def, Option.some.injEq] at hi
    subst hi
    refine iff_of_false not_concreteNonemptySubsetSum_empty ?_
    rintro ⟨-, hl, -⟩
    exact hlin ((BinarySubsetSum.isLinOrdB_iff S).mpr hl)

/-- **The computable decoding of binary-weighted structures, for non-zero
`HAVING SUM` provenance.** Every nonempty finite structure decodes, so the
NP-hardness above is nowhere hardness on junk alone. -/
def havingSumNonzeroDecoding : Decoding Language.binWeights
    (DecisionProblem.ofSentence ⊤) ConcreteNonemptySubsetSum HavingSumNonzero where
  dec := bwDecode
  sound := bwDecode_sound_nonempty
  total := bwDecode_total

/-- **Hardness reads back to concrete groups**: every nonempty finite
binary-weighted structure is decided by `HavingSumNonzero` exactly as some
concrete group is by the non-empty subset-sum condition – equivalently, by the
two bridges, as some concrete group's provenance is non-`𝟘`. -/
theorem exists_concreteNonemptySubsetSum_iff (A : Type) [Language.binWeights.Structure A]
    [Finite A] [Nonempty A] : ∃ i, ConcreteNonemptySubsetSum i ↔ HavingSumNonzero A :=
  havingSumNonzeroDecoding.exists_conc_iff A (by simp)

end Decoding


end Provenance.Complexity
