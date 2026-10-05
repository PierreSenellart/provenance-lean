import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Lax392996.SemiringsWithMonus

/-!
---
title: Boolean functions as an m-semiring
type: definition
---
The m-semiring $\mathcal{B}[X]$ of Boolean functions over a set $X$ of
Boolean variables: elements are the functions $(X \to \{\bot, \top\}) \to
\{\bot, \top\}$, with pointwise $\lor$ as $\oplus$, pointwise $\land$ as
$\otimes$, the constant functions $\bot$ and $\top$ as $\mathbb{0}$ and
$\mathbb{1}$, pointwise implication as the natural order and $(a, b) \mapsto
a \land \lnot b$ as $\ominus$; $\delta$ is the identity. Equality of two
Boolean functions is decidable classically, which is what the annotated
semantics requires of an annotation type.
-/

namespace Lax392996.BooleanFunctions

open Lax392996.SemiringsWithMonus

variable {X : Type}

/-- The type of Boolean functions over Boolean assignments to `X`:
`(X → Bool) → Bool` with pointwise operations. -/
def BoolFunc (X : Type) := (X → Bool) → Bool

instance instZeroBoolFunc : Zero (BoolFunc X) := ⟨λ _ ↦ False⟩

instance instAddBoolFunc : Add  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) || (f₂ ν)⟩

instance instOneBoolFunc : One  (BoolFunc X) := ⟨λ _ ↦ True⟩

instance instMulBoolFunc : Mul  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && (f₂ ν)⟩

instance instLEBoolFunc : LE   (BoolFunc X) := ⟨λ f₁ f₂ ↦ ∀ ν : X → Bool, (f₁ ν) ≤ (f₂ ν)⟩

instance instSubBoolFunc : Sub  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && !(f₂ ν)⟩

instance instCommSemiringBoolFunc : CommSemiring (BoolFunc X) where
  add_assoc := by
    intro a b c
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_assoc _ _ _

  add_comm := by
    intro a b
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_comm _ _

  zero_add := by tauto

  add_zero := by
    simp[(· + ·),Add.add]
    intro a
    apply funext
    simp
    tauto

  nsmul := nsmulRec

  left_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_left _ _ _

  right_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_right _ _ _

  zero_mul := by tauto

  mul_zero := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto

  mul_assoc := by
    intro a b c
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_assoc _ _ _

  mul_comm := by
    intro a b
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_comm _ _

  one_mul := by tauto

  mul_one := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto

/-- `BoolFunc X` is a commutative m-semiring with pointwise `||` as addition,
pointwise `&&` as multiplication, and pointwise implication as natural order. -/
instance instSemiringWithMonusBoolFunc : SemiringWithMonus (BoolFunc X) where
  le_refl := by tauto

  le_trans := by tauto

  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    apply funext
    intro ν
    exact Bool.le_antisymm (hab ν) (hba ν)

  le_self_add := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  le_add_self := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  add_le_add_left := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  exists_add_of_le := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    intro a b h
    use b
    apply funext
    intro x
    cases ha : a x
    . tauto
    . apply (h x) ha

  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· ≤ ·),(· - ·),Sub.sub]
    apply Iff.intro
    . intro h ν ha
      cases hb : b ν <;> simp
      . exact h ν ha hb
    . intro h ν ha hb
      have h' : b ν = true ∨ c ν = true := h ν ha
      simp[hb] at h'
      exact h'

  delta := id
  delta_zero := rfl
  delta_natCast_pos := by
    have hidem : ∀ a : BoolFunc X, a + a = a := fun a => funext fun ν => by
      show (a ν || a ν) = a ν
      simp
    have hcast : ∀ {n : ℕ}, 0 < n → (n : BoolFunc X) = 1 := by
      intro n hn
      induction n with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm]; simp
        · rw [Nat.cast_succ, ih hm, hidem 1]
    intro n hn
    exact hcast hn
  delta_absorb := fun a b => funext fun ν => by
    show (a ν && (a ν || b ν)) = a ν
    cases a ν <;> cases b ν <;> rfl

/-- For finite `X`, equality of Boolean functions `(X → Bool) → Bool` is
decidable in principle, the function space being finite. The classical
decidability instance is what the annotated semantics, which requires
`[DecidableEq K]`, is invoked with for `K = BoolFunc X`. -/
noncomputable instance instDecidableEqBoolFunc : DecidableEq (BoolFunc X) :=
  Classical.decEq _

end Lax392996.BooleanFunctions
