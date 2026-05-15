import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

import Provenance.Semirings.BoolFunc

/-!
# Probability distributions over Boolean variables

This file defines the intensional probability semantics underlying ProvSQL's
probabilistic query evaluation, following Section IV-D of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of
the Provenance and Probability of Data*][sen2026provsql].

Given a finite set `X` of Boolean variables and an assignment `Pr : X → ℚ`
of probabilities (with values in `[0, 1]`), we extend `Pr` to:

* a probability distribution over valuations `v : X → Bool`, assuming the
  variables are independent: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`;
* a probability of a Boolean function `f : BoolFunc X`, defined as the sum of
  `Pr(v)` over satisfying valuations: `Pr(f) = ∑_{v ⊨ f} Pr(v)`.

This is the foundation needed to state and prove Theorem 12 of the paper
(intensional probabilistic query evaluation correctness): for any
non-aggregation query `q`, any `BoolFunc X`-instance `Î` and any tuple `t`,
`Pr(t ∈ q(Î)) = Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`. The theorem itself is stated below
and the algebraic-bridge lemmas are developed; the full proof depends on a
"Bool-annotated semantics tracks plain semantics on the boolean-true support"
result that is left as future work.

## Main definitions

* `ProbAssignment X` — a probability assignment to each variable, bundled
  with `0 ≤ Pr(x) ≤ 1`.
* `ProbAssignment.valProb` — `Pr(v)` for a single valuation `v : X → Bool`.
* `ProbAssignment.funcProb` — `Pr(f)` for a Boolean function `f : BoolFunc X`.

## Main results

* `ProbAssignment.valProb_nonneg`, `valProb_le_one`, `sum_valProb_eq_one` —
  basic properties of the valuation distribution.
* `ProbAssignment.funcProb_zero`, `funcProb_one`, `funcProb_nonneg`,
  `funcProb_le_one` — basic properties of `Pr(f)`.
* `ProbAssignment.funcProb_congr` — pointwise-equal Boolean functions have
  equal probabilities.

## References

* [Sen, Maniu & Senellart][sen2026provsql] (Section IV-D)
-/

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A probability assignment to a finite set `X` of Boolean variables: each
variable is assigned a rational probability in `[0, 1]`. -/
structure ProbAssignment (X : Type) where
  /-- The probability assigned to each variable. -/
  prob : X → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities are at most `1`. -/
  prob_le_one : ∀ x, prob x ≤ 1

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Probability of a single valuation `v : X → Bool`, under the independence
assumption: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`. -/
def valProb (v : X → Bool) : ℚ :=
  ∏ x, if v x then P.prob x else 1 - P.prob x

omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is non-negative. -/
private lemma valProb_factor_nonneg (v : X → Bool) (x : X) :
    0 ≤ (if v x then P.prob x else 1 - P.prob x) := by
  by_cases hv : v x
  · simp [hv]; exact P.prob_nonneg x
  · simp [hv]
    have := P.prob_le_one x
    linarith

omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is at most `1`. -/
private lemma valProb_factor_le_one (v : X → Bool) (x : X) :
    (if v x then P.prob x else 1 - P.prob x) ≤ 1 := by
  by_cases hv : v x
  · simp [hv]; exact P.prob_le_one x
  · simp [hv]
    have := P.prob_nonneg x
    linarith

omit [DecidableEq X] in
theorem valProb_nonneg (v : X → Bool) : 0 ≤ P.valProb v :=
  Finset.prod_nonneg (fun x _ => P.valProb_factor_nonneg v x)

omit [DecidableEq X] in
theorem valProb_le_one (v : X → Bool) : P.valProb v ≤ 1 := by
  unfold valProb
  calc ∏ x, (if v x then P.prob x else 1 - P.prob x)
      ≤ ∏ _x : X, (1 : ℚ) :=
        Finset.prod_le_prod
          (fun x _ => P.valProb_factor_nonneg v x)
          (fun x _ => P.valProb_factor_le_one v x)
    _ = 1 := by simp

omit [Fintype X] [DecidableEq X] in
/-- For any `x : X`, `Pr(x) + (1 - Pr(x)) = 1`: summing the two cases of the
factor at `x` over `Bool` gives `1`. -/
private lemma sum_factor_at (x : X) :
    ∑ b : Bool, (if b then P.prob x else 1 - P.prob x) = 1 := by
  -- Bool's univ is {false, true}; enumerate explicitly.
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
      Finset.sum_singleton]
  simp

/-- The valuations form a probability distribution: `∑ v, Pr(v) = 1`. -/
theorem sum_valProb_eq_one : ∑ v : X → Bool, P.valProb v = 1 := by
  -- Reduce ∑_v ∏_x f(x, v x) to ∏_x ∑_b f(x, b) via Fintype.prod_sum, then
  -- close via `sum_factor_at`.
  have hps :
      (∏ x : X, ∑ b : Bool, (if b then P.prob x else 1 - P.prob x))
        = ∑ v : X → Bool, ∏ x : X, (if v x then P.prob x else 1 - P.prob x) :=
    Fintype.prod_sum (fun (x : X) (b : Bool) => if b then P.prob x else 1 - P.prob x)
  unfold valProb
  rw [← hps]
  simp_rw [P.sum_factor_at]
  simp


/-- Probability of a Boolean function: `Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : BoolFunc X) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0

theorem funcProb_nonneg (f : BoolFunc X) : 0 ≤ P.funcProb f := by
  unfold funcProb
  apply Finset.sum_nonneg
  intro v _
  by_cases hv : f v
  · simp [hv]; exact P.valProb_nonneg v
  · simp [hv]

/-- `Pr(f) ≤ ∑_v Pr(v) = 1`. -/
theorem funcProb_le_one (f : BoolFunc X) : P.funcProb f ≤ 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold funcProb
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : f v
  · simp [hv]
  · simp [hv]; exact P.valProb_nonneg v

/-- `Pr(0) = 0`: the constant-false function has probability zero. -/
theorem funcProb_zero : P.funcProb (0 : BoolFunc X) = 0 := by
  unfold funcProb
  apply Finset.sum_eq_zero
  intro v _
  show (if (0 : BoolFunc X) v then P.valProb v else 0) = 0
  -- (0 : BoolFunc X) v = false
  have h : (0 : BoolFunc X) v = false := rfl
  rw [h]
  simp

/-- `Pr(1) = 1`: the constant-true function has probability one. -/
theorem funcProb_one : P.funcProb (1 : BoolFunc X) = 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold funcProb
  apply Finset.sum_congr rfl
  intro v _
  have h : (1 : BoolFunc X) v = true := rfl
  rw [h]
  simp

/-- Pointwise-equal Boolean functions have equal probabilities. -/
theorem funcProb_congr {f g : BoolFunc X} (h : ∀ v, f v = g v) :
    P.funcProb f = P.funcProb g := by
  unfold funcProb
  apply Finset.sum_congr rfl
  intro v _
  rw [h v]

/-- Reformulation: `Pr(f)` as a sum over the satisfying valuations. -/
theorem funcProb_eq_filter_sum (f : BoolFunc X) :
    P.funcProb f = ∑ v ∈ Finset.univ.filter (fun v => f v = true), P.valProb v := by
  unfold funcProb
  rw [← Finset.sum_filter]

/-! ## Theorem 12: intensional probabilistic query evaluation

The paper's Theorem 12 (Section IV-D of
[Sen, Maniu & Senellart][sen2026provsql]) states:

> For any finite set of variables `X`, probability distribution `Pr` over `X`,
> `B[X]`-relation `Î` and relational algebra query `q` without aggregation,
> for any tuple `t` with same arity as `q`,
> `Pr(t ∈ q(Î)) = Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`.

The right-hand side is `Pr(f)` where `f` is the disjunction of the annotations
of all annotated tuples in `⟪q⟫^Î` whose data part equals `t`.

The left-hand side `Pr(t ∈ q(Î))` is the marginal probability that `t` appears
in the output of `q` evaluated on the random subinstance of `Î`. Formalising
this requires (i) a notion of subinstance / random world and (ii) the plain
semantics of `q` on the data side. The pointwise reformulation that the proof
of Theorem 12 actually uses is:

> for every valuation `v : X → Bool` and every tuple `t`,
> `(⋁_{(t,α) ∈ ⟪q⟫^Î} α)(v) = true ↔ t ∈ ⟦q⟧(J(v))`

where `J(v) := { (u, α) ∈ Î | α(v) = true }` is the random world selected by
`v`. The forward implication follows from the m-semiring homomorphism
`v* : BoolFunc X → Bool` (already in `Bool.homomorphism_to_BoolFunc`) and
`Query.evaluateAnnotated_hom`. The remaining content — agreement of the
`Bool`-annotated semantics with the plain semantics on the boolean-true
support — is left as future work; it is a structural induction on the query
shape, with the `Diff` and `Dedup` cases requiring care over multisets.

Once the pointwise version is in place, summing both sides times `Pr(v)`
gives the paper's formulation, since
`Pr(f) = ∑_v [f(v) = ⊤] · Pr(v)` by definition of `funcProb`. -/

end ProbAssignment
