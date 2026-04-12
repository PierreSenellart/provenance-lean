import Provenance.SemiringWithMonus

/-!
# Counting m-semiring

This file shows that `ℕ` (with standard addition and multiplication) is a commutative
m-semiring. The monus is truncated subtraction (`Nat.sub`). Unlike most provenance
semirings, `ℕ` is neither idempotent nor absorptive.

The natural order is the usual order on natural numbers, and monus coincides with
Mathlib's `Nat.sub`.
-/

/-- `ℕ` is a commutative m-semiring. The natural order is the usual order on
natural numbers, and the monus is truncated subtraction. -/
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
