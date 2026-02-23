import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Ring.Basic

import Provenance.SemiringWithMonus

open scoped Classical

/--
Viterbi semiring (max-times) over probabilities in `[0,1]`.
-/
def Viterbi : Type := { p : NNReal // p ≤ 1 }

namespace Viterbi

instance : Coe Viterbi NNReal := ⟨Subtype.val⟩

@[ext] theorem ext {a b : Viterbi} (h : (a: NNReal) = (b: NNReal)) : a = b :=
  Subtype.ext h

@[simp] theorem coe_mk (p : NNReal) (hp : p ≤ 1) : ((⟨p, hp⟩ : Viterbi) : NNReal) = p := rfl

instance : Zero Viterbi := ⟨⟨0, by simp⟩⟩
instance : One  Viterbi := ⟨⟨1, le_rfl⟩⟩

instance : Add Viterbi :=
  ⟨fun a b => ⟨max (a : NNReal) (b : NNReal), by
    exact max_le a.property b.property⟩⟩

instance : Mul Viterbi :=
  ⟨fun a b => ⟨(a : NNReal) * (b : NNReal), by
    calc
      (a : NNReal) * (b : NNReal) ≤ (1 : NNReal) * (1 : NNReal) := by
        exact mul_le_mul a.property b.property (by simp) (by simp)
      _ = (1 : NNReal) := by simp⟩⟩

@[simp] theorem zero_def :
    ((0: Viterbi) : NNReal) = 0 := rfl

@[simp] theorem one_def :
    ((1: Viterbi) : NNReal) = 1 := rfl

@[simp] theorem add_def (a b : Viterbi) :
    ((a + b : Viterbi) : NNReal) = max (a : NNReal) (b : NNReal) := rfl

@[simp] theorem mul_def (a b : Viterbi) :
    ((a * b : Viterbi) : NNReal) = (a : NNReal) * (b : NNReal) := rfl

instance : CommSemiring Viterbi where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)

  add_assoc a b c := by ext; simp [max_assoc]
  add_comm  a b   := by ext; simp [max_comm]
  zero_add  a     := by ext; simp
  add_zero  a     := by ext; simp

  mul_assoc a b c := by ext; simp [mul_assoc]
  mul_comm  a b   := by ext; simp [mul_comm]

  one_mul a := by ext; simp
  mul_one a := by ext; simp
  zero_mul a := by ext; simp
  mul_zero a := by ext; simp

  left_distrib a b c := by ext; simp [mul_max]
  right_distrib a b c := by ext; simp [max_mul]

  nsmul := nsmulRec
  nsmul_zero := by intro a; rfl
  nsmul_succ := by intro n a; rfl

theorem viterbi_order_le : ∀ a b : Viterbi, (a : NNReal) ≤ (b : NNReal) ↔ a + b = b := by
  intro a b
  constructor
  · intro hab
    ext
    simp [max_eq_right hab]
  · intro h
    have := congrArg (fun x : Viterbi => (x : NNReal)) h
    simp at this
    exact this

instance : PartialOrder Viterbi where
  le a b := (a : NNReal) ≤ (b : NNReal)
  le_refl := by intro a; exact le_rfl
  le_trans := by intro a b c hab hbc; exact le_trans hab hbc
  le_antisymm := by
    intro a b hab hba
    apply Subtype.ext
    exact le_antisymm hab hba

@[simp] theorem le_def (a b : Viterbi) :
    a ≤ b ↔ (a: NNReal) ≤ (b: NNReal) := by simp

noncomputable
instance : SemiringWithMonus Viterbi where
  sub a b := if (a : NNReal) ≤ (b : NNReal) then 0 else a
  lt a b := a + b = b ∧ a ≠ b
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := by intro a b c; exact le_trans
  le_antisymm := by intro a b; exact le_antisymm

  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro h
      rcases h with ⟨hab, hne⟩
      have hle : (a : NNReal) ≤ (b : NNReal) := (viterbi_order_le a b).2 hab
      have hnot : ¬ (b : NNReal) ≤ (a : NNReal) := by
        intro hba
        exact hne (Subtype.ext (le_antisymm hle hba))
      exact ⟨hle, hnot⟩
    · intro h
      rcases h with ⟨hle, hnot⟩
      have hab : a + b = b := (viterbi_order_le a b).1 hle
      have hne : a ≠ b := by
        intro heq
        apply hnot
        simp [heq]
      exact ⟨hab, hne⟩

  add_le_add_left := by
    intro a b hab c
    simpa using max_le_max hab (le_rfl : (c : NNReal) ≤ c)

  exists_add_of_le := by
    intro a b hab
    refine ⟨b, ?_⟩
    symm
    exact (viterbi_order_le a b).1 hab

  le_self_add := by
    intro a b
    simp

  le_add_self := by
    intro a b
    simp

  monus_spec := by
    intro a b c
    -- unfold the definition of `sub` and split on `a ≤ b`
    simp[(· - ·), Sub.sub]
    by_cases hab : (a : NNReal) ≤ (b : NNReal) <;> simp at hab
    · simp [hab]
      refine Subtype.coe_le_coe.mp ?_
      simp
    · have : ¬a≤b := by by_contra h; have := (lt_self_iff_false _).mp (lt_of_lt_of_le hab h); assumption
      simp [this]

theorem absorptive : absorptive Viterbi := by
  intro a
  ext
  simp [a.property]

theorem idempotent : idempotent Viterbi := idempotent_of_absorptive absorptive

theorem mul_sub_left_distributive : mul_sub_left_distributive Viterbi := by
  intro a b c
  ext
  simp [(· - ·), Sub.sub, mul_def]
  by_cases hbc : (b : NNReal) ≤ (c : NNReal) <;> simp at hbc
  · simp[hbc]
    have habc : (a : NNReal) * (b : NNReal) ≤ (a : NNReal) * (c : NNReal) :=
      @mul_le_mul_right Viterbi _ _ _ _ _ hbc (a: Viterbi)
    simp [habc]
  . have : ¬b≤c := by by_contra h; have := (lt_self_iff_false _).mp (lt_of_lt_of_le hbc h); assumption
    simp[this]
    by_cases ha0 : (a : NNReal) = 0
    · simp [ha0]
    · have hnot : ¬ (a : NNReal) * (b : NNReal) ≤ (a : NNReal) * (c : NNReal) := by
        intro habc
        have ha_pos : (0 : NNReal) < (a : NNReal) := lt_of_le_of_ne (by simp) (Ne.symm ha0)
        have : (b : NNReal) ≤ (c : NNReal) := le_of_mul_le_mul_left habc ha_pos
        exact (lt_self_iff_false _).mp (lt_of_le_of_lt this hbc)
      simp [hnot]

end Viterbi
