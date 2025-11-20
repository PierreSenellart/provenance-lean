import Provenance.SemiringWithMonus

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
  -- natural order
  le_self_add := by
    intro a b
    cases a <;> tauto

  add_le_add_left := by
    intro a b h c
    cases a <;> cases b <;> cases c <;> tauto

  exists_add_of_le := by
    intro a b h
    rw[le_iff_exists_sup] at h
    exact h

  monus_spec := by
    intro a b c
    apply Iff.intro <;> cases a <;> cases b <;> tauto

theorem Bool.absorptive : absorptive Bool := by
  simp
  tauto

theorem Bool.idempotent : idempotent Bool :=
  idempotent_of_absorptive (Bool.absorptive)

end Bool
