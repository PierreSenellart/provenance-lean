import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.ToDFinsupp

import Provenance.SemiringWithMonus

variable {α: Type} [DecidableEq α]

instance : LE (MvPolynomial α ℕ) where
  le a b := ∀ m, a.coeff m ≤ b.coeff m


instance : Sub (MvPolynomial α ℕ) where
  sub a b :=
    let aDF := a.toDFinsupp
    let bDF := b.toDFinsupp
    let rDF := DFinsupp.zipWith (λ m x y ↦ x - y) (by simp) aDF bDF
    rDF.toFinsupp


instance : PartialOrder (MvPolynomial α ℕ) where
  le_refl := by
    simp only[(· ≤ ·)]
    simp

  le_antisymm := by
    intro a b hab hba
    ext m
    exact le_antisymm (hab m) (hba m)

  le_trans := by
    intro a b c hab hbc m
    exact le_trans (hab m) (hbc m)


instance : IsOrderedAddMonoid (MvPolynomial α ℕ) where
  add_le_add_left := by
    intro a b hab c m
    rw[MvPolynomial.coeff_add]
    simp
    exact hab m


instance : CanonicallyOrderedAdd (MvPolynomial α ℕ) where
  exists_add_of_le := by
    intro a b hab
    use Finsupp.zipWith (· - ·) (by simp) b a
    ext m
    exact (Nat.sub_eq_iff_eq_add' (hab m)).mp rfl

  le_self_add := by
    intro a b m
    exact le_add_of_nonneg_right (by simp)

  le_add_self := by
    intro a b m
    exact le_add_of_nonneg_left (by simp)


/-- Marked as noncomputable only because the proof that `MvPolynomial` is a
`CommutativeSemiring` is done in a non-computable way in Mathlib. We
could redefine `MvPolynomial` to provide computable proofs. -/
noncomputable instance : SemiringWithMonus (MvPolynomial α ℕ) where
  monus_spec := by
    intro a b c
    apply Iff.intro
    . intro h m
      exact Nat.sub_le_iff_le_add'.mp (h m)
    . intro h m
      exact Nat.sub_le_iff_le_add'.mpr (h m)

theorem How.not_idempotent : ¬(idempotent (MvPolynomial α ℕ)) := by
  simp
  use (MvPolynomial.C 1)
  rw[← MvPolynomial.C_add]
  rw[MvPolynomial.C_inj _ _]
  simp

theorem How.not_absorptive : ¬(absorptive (MvPolynomial α ℕ)) := by
  have h₁ := @idempotent_of_absorptive (MvPolynomial α ℕ) _
  have h₂ : ¬(idempotent (MvPolynomial α ℕ)) := How.not_idempotent
  tauto
