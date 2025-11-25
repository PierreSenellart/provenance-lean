/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/-!
# Semirings with monus

This file defines semirings with monus and introduces their main
properties.

Many semirings relevant for provenance can be equipped with a monus -
operator, resulting in what is called a semiring with monus, or
m-semiring. This is standard in semiring theory [amer1984equationally] and was
introduced in the setting of provenance semirings by Geerts and Poggi
[geerts2010database].

## References

* [Amer, *Equationally complete classes of commutative monoids with
monus*][amer1984equationally]
* [Geerts & Poggi, *On database query languages for
K-relations*][geerts2010database]

-/

section SemiringWithMonus

/-! ## Definition of a `SemiringWithMonus` -/

/-- A `SemiringWithMonus` is a naturally ordered semiring
with a monus operation that is compatible with the natural order.
We do not require the semiring to be necessarily commutative. -/
class SemiringWithMonus (α : Type)
  extends Semiring α, PartialOrder α, IsOrderedAddMonoid α, CanonicallyOrderedAdd α, Sub α where
  monus_spec : ∀ a b c : α, a - b ≤ c ↔ a ≤ b + c

/-! ## Main properties -/

/-- In a `SemiringWithMonus`, `a - b` is the smallest element `c`
satisfying `a ≤ b + c`. -/
theorem monus_smallest [K : SemiringWithMonus α] :
  ∀ a b : α, a ≤ b + (a - b) ∧ ∀ c: α, a ≤ b + c → a - b ≤ c := by {
    intro a b
    constructor
    . rw [← SemiringWithMonus.monus_spec]
    . intro c h
      rw [SemiringWithMonus.monus_spec]
      exact h
  }

theorem monus_self [K : SemiringWithMonus α] :
  ∀ a : α, a - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

theorem zero_monus [K : SemiringWithMonus α] :
  ∀ a : α, 0 - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

theorem add_monus [K : SemiringWithMonus α] :
  ∀ a b : α, a + (b - a) = b + (a - b) := by
    intro a b

    have h : ∀ a b c : α, (a ≤ c ∧ b ≤ c) → a+(b-a) ≤ c := by
      intro a b c hc
      rcases hc with ⟨ha, hb⟩
      rcases (exists_add_of_le ha) with ⟨d, ha'⟩
      rw [ha'] at hb
      rw [← SemiringWithMonus.monus_spec] at hb
      apply add_le_add_left at hb
      specialize hb a
      rw[add_comm]
      simp [ha']
      nth_rewrite 2 [add_comm]
      assumption

    apply le_antisymm

    . apply h a b (b+(a-b))
      constructor
      . simp [← SemiringWithMonus.monus_spec]
      . simp

    . apply h b a (a+(b-a))
      constructor
      . simp [← SemiringWithMonus.monus_spec]
      . simp

theorem monus_add [K: SemiringWithMonus α] :
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
          apply add_le_add_right
          rw [← SemiringWithMonus.monus_spec (a-b) c (a-b-c)]
        }

    . apply h2
      rw [← SemiringWithMonus.monus_spec]
  }

abbrev idempotent (α) [Semiring α] := ∀ a : α, a + a = a

abbrev absorptive (α) [Semiring α] := ∀ a : α, 1 + a = 1

abbrev mul_sub_left_distributive (α) [SemiringWithMonus α] := ∀ a b c : α, a * (b - c) = a*b - a*c

theorem idempotent_of_absorptive [K: Semiring α] :
  absorptive α → idempotent α := by
    intro habs a
    nth_rewrite 1 2 [← mul_one a]
    rw[← mul_add]
    simp[habs 1]

theorem le_iff_add_eq [K: SemiringWithMonus α] (h: idempotent α) :
  ∀ a b: α, a<=b ↔ a+b = b := by
    intro a b
    apply Iff.intro
    . intro hab
      have := le_iff_exists_add.mp hab
      rcases this with ⟨c,hc⟩
      nth_rewrite 1 [hc]
      rw[← add_assoc]
      rw[h a]
      tauto
    . intro hab
      rw[← hab]
      exact le_self_add

theorem plus_is_join [K: SemiringWithMonus α] (h: idempotent α) :
  ∀ a b: α, ((a ≤ a+b) ∧ (b ≤ a+b)) ∧ (∀ u: α, (a ≤ u) ∧ (b ≤ u) → a+b ≤ u) := by
    intro a b
    constructor
    . constructor
      . exact le_self_add
      . rw[add_comm]
        exact le_self_add
    . intro u hu
      have ha := (le_iff_add_eq h _ _).mp hu.1
      have hb := (le_iff_add_eq h _ _).mp hu.2
      apply (le_iff_add_eq h _ _).mpr
      rw[add_assoc]
      rw[hb]
      exact ha

theorem idempotent_of_add_monus
  [K: SemiringWithMonus α]
  (h: ∀ a b c : α, (a + b) - c = (a - c) + (b - c)) : idempotent α := by
      intro a
      have ha := h a a a
      simp[monus_self] at ha
      have h₁ : a + a ≤ a := by
        have := (K.monus_spec _ _ _).mp (le_of_eq ha)
        simp at this
        assumption
      have h₂ : a ≤ a + a := by
        exact le_self_add
      exact eq_of_le_of_ge h₁ h₂

theorem add_monus_of_idempotent [K: SemiringWithMonus α] (h: idempotent α) :
  ∀ a b c : α, (a + b) - c = (a - c) + (b - c) := by
    intro a b c
    have h₁ : (a + b) - c ≤ (a - c) + (b - c) := by
      apply (K.monus_spec _ _ _).mpr
      have ha : a ≤ c + (a - c) := (monus_smallest _ _).1
      have hb : b ≤ c + (b - c) := (monus_smallest _ _).1
      have := add_le_add ha hb
      apply le_trans this
      simp[← add_assoc]
      rw[add_assoc c _ c]
      rw[add_comm (a-c) c]
      simp[← add_assoc]
      rw[h c]

    have h₂ : (a - c) + (b - c) ≤ (a + b) - c := by
      suffices h₂' : (a-c) ≤ (a + b) - c ∧ (b-c) ≤ (a + b) - c from
        (plus_is_join h (a-c) (b-c)).2 _ h₂'
      constructor
      . have hab := @le_self_add _ _ _ _ a b
        have habc := le_trans hab (monus_smallest (a+b) c).1
        exact (K.monus_spec _ _ _).mpr habc
      . have hab := @le_self_add _ _ _ _ b a
        rw[add_comm] at hab
        have habc := le_trans hab (monus_smallest (a+b) c).1
        exact (K.monus_spec _ _ _).mpr habc

    exact eq_of_le_of_ge h₁ h₂

class HasAltLinearOrder (α : Type u) where
  altOrder : LinearOrder α

end SemiringWithMonus
