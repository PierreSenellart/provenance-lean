import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.ToDFinsupp

import Provenance.SemiringWithMonus
import Provenance.Semirings.Nat

variable {X: Type} [DecidableEq X]

instance : LE (MvPolynomial X ℕ) where
  le a b := ∀ m, a.coeff m ≤ b.coeff m


instance : Sub (MvPolynomial X ℕ) where
  sub a b :=
    let aDF := a.toDFinsupp
    let bDF := b.toDFinsupp
    let rDF := DFinsupp.zipWith (λ m x y ↦ x - y) (by simp) aDF bDF
    rDF.toFinsupp


theorem coeff_sub (p q : MvPolynomial X ℕ) (n : X →₀ ℕ) :
  (p-q).coeff n = p.coeff n - q.coeff n := by
    simp only[HSub.hSub, Sub.sub]
    simp [MvPolynomial.coeff, DFinsupp.toFinsupp, DFinsupp.zipWith]


instance : PartialOrder (MvPolynomial X ℕ) where
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


instance : IsOrderedAddMonoid (MvPolynomial X ℕ) where
  add_le_add_left := by
    intro a b hab c m
    rw[MvPolynomial.coeff_add]
    simp
    exact hab m


instance : CanonicallyOrderedAdd (MvPolynomial X ℕ) where
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
noncomputable instance : SemiringWithMonus (MvPolynomial X ℕ) where
  monus_spec := by
    intro a b c
    apply Iff.intro
    . intro h m
      exact Nat.sub_le_iff_le_add'.mp (h m)
    . intro h m
      exact Nat.sub_le_iff_le_add'.mpr (h m)

theorem How.not_idempotent : ¬(idempotent (MvPolynomial X ℕ)) := by
  simp
  use (MvPolynomial.C 1)
  rw[← MvPolynomial.C_add]
  rw[MvPolynomial.C_inj _ _]
  simp

theorem How.not_absorptive : ¬(absorptive (MvPolynomial X ℕ)) := by
  have h₁ := @idempotent_of_absorptive (MvPolynomial X ℕ) _
  have h₂ : ¬(idempotent (MvPolynomial X ℕ)) := How.not_idempotent
  tauto


/-- The How[X] semiring is universal among commutative semirings. This
  was observed in [Green, Karnouvarakis, Tannen, *Provenance
  Semirings*, Proposition 4.2][green2007provenance]. -/
theorem How.universal (K: Type) [CommSemiring K] :
  ∀ ν: X → K, ∃ h: RingHom (MvPolynomial X ℕ) K, ∀ i: X, h (MvPolynomial.X i) = ν i := by
    intro ν
    use MvPolynomial.eval₂Hom (Nat.castRingHom K) ν
    simp[MvPolynomial.eval₂Hom_X']

/-- The How[X] semiring is not universal among commutative m-semirings, as
long as there is at least one variable in X (if there is none, the notion
of universality is trivial). This was shown in
[Geerts & Poggi, *On database query languages for K-relations*, Example
10][geerts2010database]. -/
theorem How.not_universal_m [Inhabited X] :
  ∃ ν: X → ℕ, ¬(∃ h: SemiringWithMonusHom (MvPolynomial X ℕ) ℕ, ∀ i: X, h (MvPolynomial.X i) = ν i) := by
    let ν : X → ℕ := fun i => 1
    use ν
    intro h_exists
    rcases h_exists with ⟨h, hX⟩

    let x: MvPolynomial X ℕ := MvPolynomial.X (default: X)

    have hx : h x = 1 := by
      simpa using hX _

    have h₁: h (x*x - x) = 0 := by
      simp[h.map_sub (x*x) x]
      simp[hx]

    have hxx: x*x = (MvPolynomial.X default)^2 := by
      simp[x, pow_two]

    have h₂: x*x - x = x*x := by
      simp[hxx]
      ext m
      simp[coeff_sub]
      simp[x]
      rw[MvPolynomial.coeff_X_pow]
      by_cases hm : Finsupp.single default 2 = m
      . simp[← hm]
      . by_cases hm': Finsupp.single default 1 = m
        . simp[← hm']
          simp[Finsupp.single]
        . simp[hm]

    have h₂': h (x*x - x) = 1 := by
      simp[h₂]
      exact hx

    simp[h₁] at h₂'
