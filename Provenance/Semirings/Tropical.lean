import Mathlib.Algebra.Tropical.Basic
import Provenance.SemiringWithMonus

abbrev ℕinf := WithTop Nat

def sub_tropical (a b: Tropical ℕinf) :=
  if (Tropical.untrop a ≥ Tropical.untrop b) then ⊤ else a

theorem tropical_order_ge [LinearOrder α] :
  ∀ a b: Tropical α, Tropical.untrop a ≥ Tropical.untrop b ↔ a+b = b := by {
    intro a b
    exact Tropical.add_eq_right_iff.symm
  }

instance : SemiringWithMonus (Tropical ℕinf) where
  sub := sub_tropical
  le a b := Tropical.untrop a ≥ Tropical.untrop b
  lt a b := a+b = b ∧ a ≠ b
  lt_iff_le_not_le := by {
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
  }
  le_refl := by simp
  le_trans := by {
    intro a b c hab hbc
    rw[tropical_order_ge]
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hbc
    calc
      a + c = a + b + c := by simp[hbc,add_assoc]
          _ = b + c     := by simp[hab]
              _ = c     := by simp[hbc]
  }
  le_antisymm := by {
    intro a b hab hba
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hba
    calc
      a = b + a := by simp[hba]
      _ = a + b := by simp[add_comm]
      _ = b     := by simp[hab]
  }
  add_le_add_left := by {
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
  }
  exists_add_of_le := by {
    intro a b h
    rw[tropical_order_ge] at h
    use b
    simp[h]
  }
  le_self_add := by {
    intro a b
    rw[tropical_order_ge]
    calc
      a + (a + b) = a + a + b := by rw[add_assoc]
                _ = a + b     := by simp
  }

  monus_spec := by {
    intro a b c
    simp
    change c ≤ (sub_tropical a b) ↔ b ≤ a ∨ c ≤ a
    unfold sub_tropical
    split_ifs with h
    . simp
      left
      simp[tropical_order_ge] at h
      exact h
    . simp[tropical_order_ge] at h
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
  }
