/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Tactic.NormNum
import Provenance.Having
import Provenance.HavingProbability
import Provenance.Semirings.BoolFunc

/-!
# Worked examples: HAVING provenance and probability on a three-occurrence group

Two fully computed examples on a group with three occurrences.

* **`SUM(a) ≥ 5` collapse in `𝔹[X]`.** With attribute values `a = (3, 2, 2)`
  and annotations the distinct variables `x₁, x₂, x₃`, the valid non-empty
  worlds are `{1,2}`, `{1,3}` and `{1,2,3}`, and the possible-world
  provenance sums their world annotations. Since `𝔹[X]` is absorptive, this
  collapses to the `⊕`-sum over the two *minimal* valid worlds `{1,2}` and
  `{1,3}` alone (the general statement is `Having.sum_ge_collapse`); both
  sides compute – by kernel evaluation on all `2³` valuations – to
  `x₁ ∧ (x₂ ∨ x₃)`.

* **Poisson-binomial `COUNT(*) ≥ 2`.** With independent contributors of
  marginals `p₁ = 1/2`, `p₂ = 1/4`, `p₃ = 1/3`, the point masses computed by
  the recurrence (`HavingProbability.countMass_insert_zero` /
  `countMass_insert_succ`) are `ρ₃(2) = 1/4` and `ρ₃(3) = 1/24`, and the CDF
  assembly (`HavingProbability.funcProb_count_filter`) gives
  `Pr[COUNT(*) ≥ 2] = 1/4 + 1/24 = 7/24`.
-/

namespace HavingExample

open Having

/-! ### The `SUM(a) ≥ 5` collapse in `𝔹[X]` -/

/-- Attribute values of the three occurrences: `a(u₁) = 3`, `a(u₂) = a(u₃) = 2`. -/
def t : Fin 3 → ℕ := fun i => if i.val = 0 then 3 else 2

/-- Annotations: the distinct Boolean variables `x₁, x₂, x₃` of `𝔹[X]`. -/
def α : Fin 3 → BoolFunc (Fin 3) := BoolFunc.var

/-- **Possible-world provenance of `SUM(a) ≥ 5`**: the `⊕`-sum of the world
annotations `T_U(W)` over the valid worlds `{1,2}`, `{1,3}`, `{1,2,3}`
computes to `x₁ ∧ (x₂ ∨ x₃)`. -/
theorem sum_ge_five_prov :
    ∑ W ∈ (Finset.univ : Finset (Fin 3)).powerset.filter
        (fun W => 5 ≤ ∑ i ∈ W, t i), T α Finset.univ W
      = BoolFunc.var 0 * (BoolFunc.var 1 + BoolFunc.var 2) :=
  funext (by decide)

/-- **Collapse to minimal worlds**: the `⊕`-sum of the monomials `A_V` over
the two minimal valid worlds `{1,2}` and `{1,3}` computes to the same
`x₁ ∧ (x₂ ∨ x₃)`, as predicted by `Having.sum_ge_collapse` since `𝔹[X]` is
absorptive. -/
theorem sum_ge_five_minimal :
    ∑ V ∈ ((Finset.univ : Finset (Fin 3)).powerset.filter
          (fun W => 5 ≤ ∑ i ∈ W, t i)).filter
        (fun V => ∀ V' ⊂ V, ¬ (5 ≤ ∑ i ∈ V', t i)), A α V
      = BoolFunc.var 0 * (BoolFunc.var 1 + BoolFunc.var 2) :=
  funext (by decide)

/-! ### The Poisson-binomial `COUNT(*) ≥ 2` example -/

/-- Independent contributor marginals `p₁ = 1/2`, `p₂ = 1/4`, `p₃ = 1/3`. -/
def P : ProbAssignment (Fin 3) where
  prob := fun i => if i.val = 0 then 1/2 else if i.val = 1 then 1/4 else 1/3
  prob_nonneg := fun i => by split_ifs <;> norm_num
  prob_le_one := fun i => by split_ifs <;> norm_num

/-- Per-contributor variable supports: contributor `i` depends on `xᵢ` only. -/
def S : Fin 3 → Finset (Fin 3) := fun i => {i}

lemma hdep : ∀ i, (α i).DependsOn (S i) := fun i => BoolFunc.DependsOn.var i

lemma hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)) := by
  intro i _ j _ hij
  rw [Finset.disjoint_left]
  intro a ha ha'
  exact hij ((Finset.mem_singleton.mp ha).symm.trans (Finset.mem_singleton.mp ha'))

lemma funcProb_α (i : Fin 3) : P.funcProb (α i) = P.prob i :=
  P.funcProb_var i

lemma prob_0 : P.prob 0 = 1/2 := rfl
lemma prob_1 : P.prob 1 = 1/4 := rfl
lemma prob_2 : P.prob 2 = 1/3 := rfl

open HavingProbability

/-- Base of the recurrence: over no contributors, the count is `0` with
probability `1`. -/
lemma mass_empty_zero :
    P.funcProb (countEqIndicator α (∅ : Finset (Fin 3)) 0) = 1 := by
  have h : countEqIndicator α (∅ : Finset (Fin 3)) 0 = 1 := funext fun v => rfl
  rw [h, P.funcProb_one]

/-- Base of the recurrence: over no contributors, a positive count has
probability `0`. -/
lemma mass_empty_succ (j : ℕ) :
    P.funcProb (countEqIndicator α (∅ : Finset (Fin 3)) (j + 1)) = 0 := by
  have h : countEqIndicator α (∅ : Finset (Fin 3)) (j + 1) = 0 :=
    funext fun v => decide_eq_false (by simp)
  rw [h, P.funcProb_zero]

/- The table of the Poisson-binomial recurrence, built one contributor at a
time (last contributor first: `{x₃}`, then `{x₂, x₃}`, then all three). -/

lemma mass_1_0 :
    P.funcProb (countEqIndicator α (insert 2 (∅ : Finset (Fin 3))) 0) = 2/3 := by
  rw [countMass_insert_zero P α S hdep hdisj (by decide), mass_empty_zero,
    funcProb_α, prob_2]
  norm_num

lemma mass_1_1 :
    P.funcProb (countEqIndicator α (insert 2 (∅ : Finset (Fin 3))) 1) = 1/3 := by
  rw [countMass_insert_succ P α S hdep hdisj (by decide) 0, mass_empty_zero,
    mass_empty_succ, funcProb_α, prob_2]
  norm_num

lemma mass_1_2 :
    P.funcProb (countEqIndicator α (insert 2 (∅ : Finset (Fin 3))) 2) = 0 := by
  rw [countMass_insert_succ P α S hdep hdisj (by decide) 1, mass_empty_succ,
    mass_empty_succ]
  ring

lemma mass_1_3 :
    P.funcProb (countEqIndicator α (insert 2 (∅ : Finset (Fin 3))) 3) = 0 := by
  rw [countMass_insert_succ P α S hdep hdisj (by decide) 2, mass_empty_succ,
    mass_empty_succ]
  ring

lemma mass_2_1 :
    P.funcProb (countEqIndicator α
      (insert 1 (insert 2 (∅ : Finset (Fin 3)))) 1) = 5/12 := by
  rw [countMass_insert_succ P α S hdep hdisj (by decide) 0, mass_1_0, mass_1_1,
    funcProb_α, prob_1]
  norm_num

lemma mass_2_2 :
    P.funcProb (countEqIndicator α
      (insert 1 (insert 2 (∅ : Finset (Fin 3)))) 2) = 1/12 := by
  rw [countMass_insert_succ P α S hdep hdisj (by decide) 1, mass_1_1, mass_1_2,
    funcProb_α, prob_1]
  norm_num

lemma mass_2_3 :
    P.funcProb (countEqIndicator α
      (insert 1 (insert 2 (∅ : Finset (Fin 3)))) 3) = 0 := by
  rw [countMass_insert_succ P α S hdep hdisj (by decide) 2, mass_1_2, mass_1_3]
  ring

private lemma huniv : (Finset.univ : Finset (Fin 3))
    = insert 0 (insert 1 (insert 2 (∅ : Finset (Fin 3)))) := by decide

/-- Point mass `ρ₃(2) = 1/4`: probability that exactly two of the three
contributors are present. -/
theorem mass_3_2 :
    P.funcProb (countEqIndicator α (Finset.univ : Finset (Fin 3)) 2) = 1/4 := by
  rw [huniv, countMass_insert_succ P α S hdep hdisj (by decide) 1, mass_2_1,
    mass_2_2, funcProb_α, prob_0]
  norm_num

/-- Point mass `ρ₃(3) = 1/24`: probability that all three contributors are
present. -/
theorem mass_3_3 :
    P.funcProb (countEqIndicator α (Finset.univ : Finset (Fin 3)) 3) = 1/24 := by
  rw [huniv, countMass_insert_succ P α S hdep hdisj (by decide) 2, mass_2_2,
    mass_2_3, funcProb_α, prob_0]
  norm_num

/-- **`Pr[COUNT(*) ≥ 2] = 7/24`**: the tail of the Poisson-binomial CDF,
assembled from the point masses `ρ₃(2) + ρ₃(3) = 1/4 + 1/24`. -/
theorem count_ge_two_prob :
    P.funcProb (fun v => decide
        (2 ≤ ((Finset.univ : Finset (Fin 3)).filter
          (fun i => α i v = true)).card))
      = 7/24 := by
  have h := funcProb_count_filter P α (Finset.univ : Finset (Fin 3))
    (fun n => 2 ≤ n)
  rw [h,
    show (Finset.range ((Finset.univ : Finset (Fin 3)).card + 1)).filter
        (fun n => 2 ≤ n) = {2, 3} from by decide,
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)),
    Finset.sum_singleton, mass_3_2, mass_3_3]
  norm_num

end HavingExample
