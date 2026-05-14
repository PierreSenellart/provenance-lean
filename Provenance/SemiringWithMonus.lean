/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
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
We do not require the semiring to be necessarily commutative.

In addition to monus, the class carries a `δ : α → α` operator subject
to two axioms (`delta_zero` and `delta_natCast_pos`). This is the
duplicate-eliminating support operator used to interpret aggregation
in the framework of
[Amsterdamer, Deutch & Tannen, *Provenance for aggregate queries*][amsterdamer2011aggregate],
mirroring ProvSQL's `Semiring::delta`. -/
class SemiringWithMonus (α : Type)
  extends Semiring α, PartialOrder α, IsOrderedAddMonoid α, CanonicallyOrderedAdd α, Sub α where
  monus_spec : ∀ a b c : α, a - b ≤ c ↔ a ≤ b + c
  /-- Duplicate-eliminating support operator. Sends `0` to `0` and any
  positive integer iterate of `1` to `1`. -/
  delta : α → α
  /-- `δ` sends `0` to `0`. -/
  delta_zero : delta 0 = 0
  /-- `δ` sends every positive integer iterate of `1` (i.e., every
  positive natural-number cast) to `1`. -/
  delta_natCast_pos : ∀ {n : ℕ}, 0 < n → delta ((n : α)) = 1

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

/-- In a `SemiringWithMonus`, `δ 1 = 1`. -/
theorem delta_one [K : SemiringWithMonus α] : K.delta 1 = 1 := by
  have h := K.delta_natCast_pos (n := 1) Nat.zero_lt_one
  simpa using h

/-- In a `SemiringWithMonus`, `a - a = 0`. -/
theorem monus_self [K : SemiringWithMonus α] :
  ∀ a : α, a - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

/-- In a `SemiringWithMonus`, `0 - a = 0`. -/
theorem zero_monus [K : SemiringWithMonus α] :
  ∀ a : α, 0 - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

/-- In a `SemiringWithMonus`, `a - 0 = a`. -/
theorem monus_zero [K : SemiringWithMonus α] :
  ∀ a : α, a - 0 = a := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]; simp
    . have h := (monus_smallest a 0).1
      simpa using h
  }

/-- In a `SemiringWithMonus`, `a + (b -a) = b + (a - b)`. -/
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

/-- In a `SemiringWithMonus`, monus is left-distributive over plus. -/
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

/-! ## Additional properties

The following properties do not always hold in an arbitrary m-semiring.
-/

/-- A `Semiring` is idempotent if `a + a = a`. -/
abbrev idempotent (α) [Semiring α] := ∀ a : α, a + a = a

/-- A `Semiring` is absorptive (also called 0-closed or 0-bounded) if `1 + a = a`. -/
abbrev absorptive (α) [Semiring α] := ∀ a : α, 1 + a = 1

/-- We define left-distributivity of times over monus in a `SemiringWithMonus`. -/
abbrev mul_sub_left_distributive (α) [SemiringWithMonus α] := ∀ a b c : α, a * (b - c) = a*b - a*c

/-- Absorptivity implies idempotence -/
theorem idempotent_of_absorptive [K: Semiring α] :
  absorptive α → idempotent α := by
    intro habs a
    nth_rewrite 1 2 [← mul_one a]
    rw[← mul_add]
    simp[habs 1]

/-- In an idempotent `SemiringWithMonus`, `a ≤ b` iff `a + b = b`. -/
theorem le_iff_add_eq [K: SemiringWithMonus α] (h: idempotent α) :
  ∀ a b: α, a ≤ b ↔ a+b = b := by
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

/-- In an idempotent `SemiringWithMonus`, plus is the join of the
  semilattice -/
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

/-- In a `SemiringWithMonus`, right-distributivity of monus
  over plus implies idempotence. -/
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

/-- In a `SemiringWithMonus`, idempotence implies right-distributivity of monus
  over plus. -/
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

/-- A `SemiringWithMonus` is idempotent iff monus is right-distributive
  over plus. -/
theorem idempotent_iff_add_monus [SemiringWithMonus α] :
  idempotent α ↔ ∀ a b c : α, (a + b) - c = (a - c) + (b - c)
    := ⟨add_monus_of_idempotent, idempotent_of_add_monus⟩

theorem monus_le [SemiringWithMonus α] :
  ∀ a b : α, a - b ≤ a := by
    simp[SemiringWithMonus.monus_spec]

theorem le_plus_monus [SemiringWithMonus α] :
  ∀ a b : α, a ≤ b + (a - b) := by
    simp[← SemiringWithMonus.monus_spec]

/-! ## Characteristic of idempotent semirings

In an idempotent semiring (`a + a = a`), every positive natural-number cast
collapses to `1`. With `1 ≠ 0` this yields `CharP K 0`. Note that this is
strictly weaker than `CharZero K`, which fails for idempotent semirings since
the cast `ℕ → K` is not injective. -/

/-- In a semiring with idempotent addition, the cast of any positive natural
number equals `1`. -/
theorem natCast_pos_eq_one_of_idempotent {K : Type} [Semiring K] (h : idempotent K) :
  ∀ {n : ℕ}, 0 < n → (n : K) = 1 := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      match Nat.eq_zero_or_pos m with
      | .inl hm => subst hm; simp
      | .inr hm => rw [Nat.cast_succ, ih hm, h 1]

/-- A nontrivial idempotent semiring has characteristic 0 in the `CharP` sense.
Unlike `CharZero`, this does not require the natural-number cast to be injective:
in an idempotent semiring every positive natural maps to `1`, but `1 ≠ 0` still
suffices to give `CharP K 0`. -/
theorem CharP.zero_of_idempotent {K : Type} [Semiring K] [Nontrivial K]
  (h : idempotent K) : CharP K 0 := by
    refine ⟨fun x => ?_⟩
    rw [zero_dvd_iff]
    refine ⟨fun hx => ?_, fun hx => by rw [hx]; exact Nat.cast_zero⟩
    by_contra hne
    rw [natCast_pos_eq_one_of_idempotent h (Nat.pos_of_ne_zero hne)] at hx
    exact one_ne_zero hx

/-! ## Homomorphisms of `SemiringWithMonus`s
-/

/-- Definition of a homomorphism of `SemiringWithMonus`s -/
class SemiringWithMonusHom (α β : Type) [SemiringWithMonus α] [SemiringWithMonus β]
  extends RingHom α β where
  map_sub : ∀ (x y: α), toRingHom (x - y) = toRingHom x - toRingHom y

instance (α β) [SemiringWithMonus α] [SemiringWithMonus β] :
CoeFun (SemiringWithMonusHom α β) (fun _ ↦ α → β) where
  coe f := fun x => f.toRingHom x

/-- If ν is an injective m-semiring homomorphism from α to β,
  and β is idempotent, so is α. -/
theorem idempotent_of_injective_homomorphism_idempotent
  [SemiringWithMonus α]
  [SemiringWithMonus β]
  (ν: SemiringWithMonusHom α β)
  (hνi : Function.Injective ν) :
  idempotent β → idempotent α := by
    intro hβ x
    apply hνi
    simp
    exact hβ _

/-- If ν is an m-semiring homomorphism from α onto β,
  and α is idempotent, so is β. -/
theorem idempotent_of_surjective_homomorphism_idempotent
  [SemiringWithMonus α]
  [SemiringWithMonus β]
  (ν: SemiringWithMonusHom α β)
  (hνs : Function.Surjective ν) :
  idempotent α → idempotent β := by
    intro hα x
    have ⟨a,ha⟩ := hνs x
    rw[← ha]
    rw[← RingHom.map_add]
    simp[hα]

/-- If ν is an injective m-semiring homomorphism from α to β,
  and β has left-distributivity of times over monus, so has α. -/
theorem mul_sub_left_of_injective_homomorphism_mul_sub_left
   [SemiringWithMonus α]
   [SemiringWithMonus β]
   (ν: SemiringWithMonusHom α β)
  (hνi : Function.Injective ν) :
  mul_sub_left_distributive β → mul_sub_left_distributive α := by
    intro hβ a b c
    apply hνi
    simp[SemiringWithMonusHom.map_sub]
    exact hβ _ _ _

/-- If ν is an m-semiring homomorphism from α onto β,
  and α has left-distributivity of times over monus, so has β. -/
theorem mul_sub_left_of_surjective_homomorphism_mul_sub_left
  [SemiringWithMonus α]
  [SemiringWithMonus β]
  (ν: SemiringWithMonusHom α β)
  (hνs : Function.Surjective ν) :
  mul_sub_left_distributive α → mul_sub_left_distributive β := by
    intro hα x y z
    have ⟨a,ha⟩ := hνs x
    have ⟨b,hb⟩ := hνs y
    have ⟨c,hc⟩ := hνs z
    rw[← ha, ← hb, ← hc]
    simp only[← SemiringWithMonusHom.map_sub, ← RingHom.map_mul]
    simp[hα]

/-! ## Miscellaneous
-/

class HasAltLinearOrder (α : Type u) where
  altOrder : LinearOrder α


end SemiringWithMonus
