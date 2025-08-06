import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Real.Basic

import Provenance.SemiringWithMonus

instance [ToString α] : ToString (WithTop α) where
  toString x := match x with | none => "⊤" | some x => toString x

instance [ToString α] : ToString (Tropical α) where
  toString x := toString ((x.untrop: α))

/-- In the tropicalization of a linear order, `a ≥ b` if and only if
`a+b = b`. -/
theorem tropical_order_ge [LinearOrder α] :
  ∀ a b: Tropical α, a.untrop ≥ b.untrop ↔ a+b = b := by
    intro a b
    exact Tropical.add_eq_right_iff.symm

/-- The tropical semiring is an m-semiring. The natural order of the
semiring is the reverse of the usual order. The monus `a-b` is defined as
`⊤` if `a≥b` (for the usual order, not the natural semiring order), and
as `a` otherwise. -/
instance [LinearOrderedAddCommMonoidWithTop α] : SemiringWithMonus (Tropical α) where
  sub a b := if (Tropical.untrop a ≥ Tropical.untrop b) then ⊤ else a
  le a b := Tropical.untrop a ≥ Tropical.untrop b
  lt a b := a+b = b ∧ a ≠ b
  lt_iff_le_not_ge := by
    intro a b
    rw[tropical_order_ge,tropical_order_ge]
    apply Iff.intro
    . intro h
      constructor
      . tauto
      . obtain ⟨h₁, h₂⟩ := h
        rw[add_comm, h₁]
        tauto
    . intro h
      obtain ⟨h₁, h₂⟩ := h
      constructor
      . tauto
      . rw[add_comm, h₁] at h₂
        tauto

  le_refl := by simp
  le_trans := by
    intro a b c hab hbc
    rw[tropical_order_ge]
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hbc
    calc
      a + c = a + b + c := by simp[hbc,add_assoc]
          _ = b + c     := by simp[hab]
              _ = c     := by simp[hbc]

  le_antisymm := by
    intro a b hab hba
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hba
    calc
      a = b + a := by simp[hba]
      _ = a + b := by simp[add_comm]
      _ = b     := by simp[hab]

  add_le_add_left := by
    intro a b h c

    rw[tropical_order_ge]
    rw[tropical_order_ge] at h

    calc
      c + a + (c + b) = c + (a + (c + b)) := by rw[add_assoc]
                    _ = c + (a + c + b)   := by rw[add_assoc]
                    _ = c + (c + a + b)   := by rw[add_comm a c]
                    _ = c + (c + (a + b)) := by rw[add_assoc]
                    _ = c + (c + b)       := by rw[h]
                    _ = c + c + b         := by rw[add_assoc]
                    _ = c + b             := by simp

  exists_add_of_le := by
    intro a b h
    rw[tropical_order_ge] at h
    use b
    simp[h]

  le_self_add := by
    intro a b
    rw[tropical_order_ge]
    calc
      a + (a + b) = a + a + b := by rw[add_assoc]
                _ = a + b     := by simp

  monus_spec := by
    intro a b c
    simp[(· - ·)]
    split_ifs with h
    . simp
      left
      simp at h
      exact h
    . simp at h
      apply Iff.intro
      . tauto
      . intro h'
        cases h' with
        | inl h'' =>
          apply lt_of_lt_of_le h at h''
          apply lt_irrefl at h''
          contradiction
        | inr h'' =>
          exact h''

/-- The tropical semiring over `ℕ ∪ {∞}` is a semiring with monus. -/
instance : SemiringWithMonus (Tropical (WithTop ℕ)) := inferInstance
/-- The tropical semiring over `ℚ ∪ {∞}` is a semiring with monus. -/
instance : SemiringWithMonus (Tropical (WithTop ℚ)) := inferInstance

/-- The tropical semiring over `ℝ ∪ {∞}` is a semiring with monus. Note
that this contradicts [Geerts & Poggi, *On database query languages for
K-relations*, Example 4][geerts2010database] which claims this semiring
cannot be extended to a semiring with monus: indeed, that paper gives
a wrong definition of the monus operator in the tropical semiring. -/
noncomputable instance : SemiringWithMonus (Tropical (WithTop ℝ)) := inferInstance
