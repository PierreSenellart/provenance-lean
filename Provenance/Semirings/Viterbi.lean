import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Ring.Basic

import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc

open scoped Classical

/-!
# Viterbi m-semiring

This file defines the *Viterbi* semiring over non-negative reals in `[0,1]`.
Addition is `max`, multiplication is the usual product, zero is `0`, and one is `1`.

The Viterbi semiring is absorptive and idempotent, and satisfies left-distributivity
of multiplication over monus.

This semiring is discussed in
[Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance].

## References

* [Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance]
-/

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
    a ≤ b ↔ (a: NNReal) ≤ (b: NNReal) := Iff.rfl

noncomputable instance : Sub Viterbi :=
  ⟨fun a b => if (a : NNReal) ≤ (b : NNReal) then 0 else a⟩

instance : IsOrderedAddMonoid Viterbi where
  add_le_add_left := by
    intro a b hab c
    simpa using max_le_max hab (le_rfl : (c : NNReal) ≤ c)

instance : CanonicallyOrderedAdd Viterbi where
  exists_add_of_le := by
    intro a b hab
    refine ⟨b, ?_⟩
    symm
    exact (viterbi_order_le a b).1 hab
  le_self_add := by intro a b; simp
  le_add_self := by intro a b; simp

instance instNontrivial : Nontrivial Viterbi :=
  ⟨0, 1, fun h => zero_ne_one (Subtype.ext_iff.mp h)⟩

theorem absorptive' : absorptive Viterbi := by intro a; ext; simp [a.property]

theorem idempotent' : idempotent Viterbi := idempotent_of_absorptive absorptive'

/-- `Viterbi` has characteristic 0 in the `CharP` sense: it is idempotent and
nontrivial. -/
instance instCharPZero' : CharP Viterbi 0 := CharP.zero_of_idempotent idempotent'

/-- ProvSQL's `Viterbi::delta`: the support indicator. -/
private noncomputable def Viterbi.deltaInd (a : Viterbi) : Viterbi :=
  if a = 0 then 0 else 1

private theorem Viterbi.deltaInd_isIndicator : IsDeltaIndicator Viterbi.deltaInd where
  zero := by simp [Viterbi.deltaInd]
  nonzero := fun a ha => by simp [Viterbi.deltaInd, ha]

/-- `Viterbi` is a commutative m-semiring. The natural order is the usual order on
`[0,1]`, and the monus is `a` if `a > b`, `0` if `a ≤ b`. -/
noncomputable
instance : SemiringWithMonus Viterbi where
  monus_spec := by
    intro a b c
    show (if (a : NNReal) ≤ (b : NNReal) then (0 : Viterbi) else a) ≤ c ↔
         (a : NNReal) ≤ max (b : NNReal) (c : NNReal)
    split_ifs with hab
    · constructor
      · intro _
        exact le_max_of_le_left hab
      · intro _
        show (0 : NNReal) ≤ (c : NNReal)
        simp
    · refine ⟨fun h => le_max_of_le_right h, fun h => ?_⟩
      rcases max_le_iff.mp (le_of_eq (rfl : max (b : NNReal) (c : NNReal) = _)) with _
      rcases le_or_gt (a : NNReal) (c : NNReal) with hac | hac
      · exact hac
      · exfalso
        have hab' : (a : NNReal) ≤ (b : NNReal) := by
          rcases le_total (b : NNReal) (c : NNReal) with hbc | hbc
          · rw [max_eq_right hbc] at h; exact absurd (lt_of_lt_of_le hac h) (lt_irrefl _)
          · rw [max_eq_left hbc] at h; exact h
        exact hab hab'
  delta := Viterbi.deltaInd
  delta_zero := Viterbi.deltaInd_isIndicator.zero
  delta_natCast_pos := delta_natCast_pos_indicator Viterbi.deltaInd_isIndicator
  delta_regrouping := delta_regrouping_indicator Viterbi.deltaInd_isIndicator

theorem absorptive : absorptive Viterbi := absorptive'

theorem idempotent : idempotent Viterbi := idempotent'

/-- Viterbi multiplication is not idempotent: `(1/2) * (1/2) = 1/4 ≠ 1/2`. -/
theorem not_mul_idempotent : ¬ ∀ a : Viterbi, a * a = a := by
  push Not
  have hle : ((1 : NNReal) / 2) ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)]; norm_num
  refine ⟨⟨(1 : NNReal) / 2, hle⟩, ?_⟩
  intro h
  have h' : ((1 : NNReal) / 2) * ((1 : NNReal) / 2) = (1 : NNReal) / 2 :=
    congrArg Subtype.val h
  field_simp at h'
  norm_num at h'

/-- There is no semiring homomorphism from `BoolFunc Y` to `Viterbi` sending the
variables to arbitrary values: Viterbi multiplication (ordinary product on
`[0,1]`) is not idempotent, contradicting `var i * var i = var i` in
`BoolFunc Y`. -/
theorem no_hom_from_BoolFunc {Y : Type} [Inhabited Y] :
    ∃ ν : Y → Viterbi,
      ¬ ∃ φ : BoolFunc Y →+* Viterbi, ∀ i : Y, φ (BoolFunc.var i) = ν i :=
  BoolFunc.no_hom_of_not_mul_idem not_mul_idempotent

theorem mul_sub_left_distributive : mul_sub_left_distributive Viterbi := by
  intro a b c
  ext
  simp only [(· - ·), Sub.sub, mul_def]
  split_ifs with hbc habc habc
  · simp
  · exfalso
    exact habc (mul_le_mul_of_nonneg_left hbc (zero_le _))
  · by_cases ha0 : (a : NNReal) = 0
    · simp [ha0]
    · have ha_pos : (0 : NNReal) < (a : NNReal) := lt_of_le_of_ne (zero_le _) (Ne.symm ha0)
      exact absurd (le_of_mul_le_mul_left habc ha_pos) hbc
  · rfl

end Viterbi
