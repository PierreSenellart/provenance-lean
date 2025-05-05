import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/-- A `SemiringWithMonus` is a naturally ordered semiring
with a monus operation that is compatible with the natural order.
We do not require the semiring to be necessarily commutative -/
class SemiringWithMonus (α : Type)
  extends Semiring α, PartialOrder α, IsOrderedAddMonoid α, CanonicallyOrderedAdd α, Sub α where
  monus_spec : ∀ a b c : α, a - b ≤ c ↔ a ≤ b + c

theorem monus_smallest [K : SemiringWithMonus α] :
  ∀ a b : α, a ≤ b + (a - b) ∧ ∀ c: α, a ≤ b + c → a - b ≤ c := by {
    intro a b
    constructor
    . rw [← SemiringWithMonus.monus_spec]
    . intro c h
      rw [SemiringWithMonus.monus_spec]
      exact h
  }

theorem monus_self (K : SemiringWithMonus α) :
  ∀ a : α, a - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

theorem zero_monus (K : SemiringWithMonus α) :
  ∀ a : α, 0 - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

theorem add_monus (K : SemiringWithMonus α) :
  ∀ a b : α, a + (b - a) = b + (a - b) := by {
    intro a b

    have h : ∀ a b c : α, (a ≤ c ∧ b ≤ c) → a+(b-a) ≤ c := by {
        intro a b c hc
        rcases hc with ⟨ha, hb⟩
        rcases (exists_add_of_le ha) with ⟨d, ha'⟩
        rw [ha'] at hb
        rw [← SemiringWithMonus.monus_spec] at hb
        apply add_le_add_left at hb
        specialize hb a
        simp [ha', hb]
      }

    apply le_antisymm

    . apply h a b (b+(a-b))
      constructor
      . simp [← SemiringWithMonus.monus_spec]
      . simp

    . apply h b a (a+(b-a))
      constructor
      . simp [← SemiringWithMonus.monus_spec]
      . simp
  }

theorem monus_add (K: SemiringWithMonus α) :
  ∀ a b c : α, a - (b + c) = a - b - c := by {
    intro a b c

    have h1 : ∀ x : α, (a ≤ b+c+x) → a - (b+c) ≤ x := by {
      intro x
      apply ((monus_smallest a (b+c)).right x)
    }

    have h2 : ∀ x : α, (a ≤ b+c+x) → a - b - c ≤ x := by {
      intro x hx
      rw [SemiringWithMonus.monus_spec]
      rw [SemiringWithMonus.monus_spec]
      rw [← add_assoc]
      exact hx
    }

    apply le_antisymm
    . apply h1
      calc
        a ≤ b + (a-b)       := by rw [← SemiringWithMonus.monus_spec a b (a-b)]
        _ ≤ b + c + (a-b-c) := by {
          rw [add_assoc]
          apply add_le_add_left
          rw [← SemiringWithMonus.monus_spec (a-b) c (a-b-c)]
        }

    . apply h2
      rw [← SemiringWithMonus.monus_spec]
  }
