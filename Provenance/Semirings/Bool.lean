import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc

section Bool

open Bool

instance : Zero (Bool) := ⟨false⟩
instance : Add  (Bool) := ⟨or⟩
instance : One  (Bool) := ⟨true⟩
instance : Mul  (Bool) := ⟨and⟩
instance : Sub  (Bool) := ⟨(· && !·)⟩


instance : CommSemiring Bool where
  add_assoc := or_assoc
  add_comm := or_comm
  zero_add := false_or
  add_zero := or_false
  mul_assoc := and_assoc
  one_mul := true_and
  mul_one := and_true
  left_distrib := and_or_distrib_left
  right_distrib := and_or_distrib_right
  zero_mul := false_and
  mul_zero := and_false
  mul_comm := and_comm
  nsmul := nsmulRec


instance : SemiringWithMonus Bool where
  le_self_add := by decide
  le_add_self := by decide
  add_le_add_left := by decide
  exists_add_of_le := by decide
  monus_spec := by decide


theorem Bool.absorptive : absorptive Bool := by decide

theorem Bool.idempotent : idempotent Bool := by decide

theorem Bool.mul_sub_left_distributive : mul_sub_left_distributive Bool := by decide

/-- Injective m-semiring homomorphism from Bool to Bool[X] -/
theorem Bool.homomorphism_from_BoolFunc :
  ∃ ν: SemiringWithMonusHom Bool (BoolFunc X), Function.Injective ν := by
    use {
      toFun     := fun b => fun _ => b
      map_zero' := rfl
      map_one'  := rfl
      map_add'  := by intro a b; rfl
      map_mul'  := by intro a b; rfl
      map_sub   := by intro a b; rfl
    }
    simp
    by_contra heq
    have := congrFun heq default
    tauto

end Bool
