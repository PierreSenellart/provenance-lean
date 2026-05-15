import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc

/-!
# Counting m-semiring

This file shows that `ℕ` (with standard addition and multiplication) is a commutative
m-semiring. The monus is truncated subtraction (`Nat.sub`). Unlike most provenance
semirings, `ℕ` is neither idempotent nor absorptive.

The natural order is the usual order on natural numbers, and monus coincides with
Mathlib's `Nat.sub`.
-/

/-- ProvSQL's `Counting::delta`: the support indicator. -/
private def Nat.deltaInd (n : ℕ) : ℕ := if n = 0 then 0 else 1

private theorem Nat.deltaInd_isIndicator : IsDeltaIndicator Nat.deltaInd where
  zero := rfl
  nonzero := fun a ha => by simp [Nat.deltaInd, ha]

/-- `ℕ` is a commutative m-semiring. The natural order is the usual order on
natural numbers, and the monus is truncated subtraction. The δ operator matches
ProvSQL's `Counting::delta`: the support indicator (`0 ↦ 0`, positive ↦ `1`). -/
instance : SemiringWithMonus Nat where
  monus_spec := by
    intro a b c
    apply Iff.intro
    . intro h
      simp at h
      rw[add_comm]
      exact h

    . intro h
      induction b with
      | zero =>
        simp at h
        simp[h]
      | succ n ih =>
        apply eq_or_lt_of_le at h
        cases h with
        | inl hl =>
          simp[hl]
        | inr hr =>
          rw[add_comm, ← add_assoc] at hr
          apply Nat.le_of_lt_succ at hr
          rw[add_comm] at hr
          have h : a - n ≤ c := by {
            apply ih
            exact hr
          }
          simp at h
          simp
          apply Nat.le_succ_of_le
          exact h
  delta := Nat.deltaInd
  delta_zero := Nat.deltaInd_isIndicator.zero
  delta_natCast_pos := delta_natCast_pos_indicator Nat.deltaInd_isIndicator
  delta_regrouping := delta_regrouping_indicator Nat.deltaInd_isIndicator

instance : HasAltLinearOrder Nat where
  altOrder := inferInstance

theorem Nat.mul_sub_left_distributive : mul_sub_left_distributive Nat :=
  Nat.mul_sub_left_distrib

theorem Nat.not_idempotent : ¬ (idempotent Nat) := by
  simp
  use 1
  simp

theorem Nat.not_absorptive : ¬ (absorptive Nat) := by
  by_contra h
  exact Nat.not_idempotent (idempotent_of_absorptive h)

/-- `ℕ` has characteristic 0: it satisfies `CharZero`, hence `CharP ℕ 0` via
`CharP.ofCharZero`. -/
theorem Nat.charP_zero : CharP Nat 0 := inferInstance

/-- There is no semiring homomorphism from `BoolFunc X` to `ℕ` sending the
variables to arbitrary values: `ℕ` is not absorptive (`1 + 1 = 2 ≠ 1`),
which contradicts `var i + 1 = 1` in `BoolFunc X`. -/
theorem Nat.no_hom_from_BoolFunc {X : Type} [Inhabited X] :
    ∃ ν : X → ℕ, ¬ ∃ φ : BoolFunc X →+* ℕ, ∀ i : X, φ (BoolFunc.var i) = ν i :=
  BoolFunc.no_hom_of_not_absorptive Nat.not_absorptive

/-- Over `ℕ`, the two natural expansions of `HAVING (count = 2)` for a
three-tuple group, `(t₁ ⊗ t₂) ⊗ (𝟙 ⊖ t₃) ⊕ (t₁ ⊗ t₃) ⊗ (𝟙 ⊖ t₂) ⊕
(t₂ ⊗ t₃) ⊗ (𝟙 ⊖ t₁)` and `(t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)`, differ.
With `t₁ = t₂ = t₃ = 1`, the first expression evaluates to `0` while the
second evaluates to `3`. -/
theorem Nat.counterexample_having :
    let t₁ : ℕ := 1
    let t₂ : ℕ := 1
    let t₃ : ℕ := 1
    (t₁ * t₂) * (1 - t₃) + (t₁ * t₃) * (1 - t₂) + (t₂ * t₃) * (1 - t₁)
      ≠ t₁ * t₂ + t₁ * t₃ + t₂ * t₃ := by decide
