import Provenance.SemiringWithMonus

import Mathlib.Order.BoundedOrder.Basic

section MinMax

variable {α: Type} [LinearOrder α] [OrderBot α] [OrderTop α]

@[ext]
structure MinMax (α: Type) where
  val: α

instance : Coe (MinMax α) α := ⟨MinMax.val⟩

instance : Top  (MinMax α) := ⟨⟨⊤⟩⟩
instance : Bot  (MinMax α) := ⟨⟨⊥⟩⟩
instance : LE   (MinMax α) := ⟨λ a b ↦ b.val ≤ a.val⟩

instance : LinearOrder (MinMax α) where
  le_refl := by simp[(· ≤ ·)]
  le_trans := by
    simp[(· ≤ ·)]
    intro a b c hba hcb
    exact Preorder.le_trans c.val b.val a.val hcb hba
  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    ext
    apply le_antisymm <;> assumption
  le_total := by simp[(· ≤ ·)]; intro a b; apply le_total
  toDecidableLE := inferInstance

instance : Zero (MinMax α) := ⟨⊤⟩
instance : Add  (MinMax α) := ⟨λ a b ↦ ⟨min a.val b.val⟩⟩
instance : One  (MinMax α) := ⟨⊥⟩
instance : Mul  (MinMax α) := ⟨λ a b ↦ ⟨max a.val b.val⟩⟩
instance : Sub  (MinMax α) := ⟨λ a b ↦ if a.val ≥ b.val then ⟨⊤⟩ else ⟨a.val⟩⟩

instance : CommSemiring (MinMax α) where
  add_assoc := by
    intro a b c
    simp[(· + ·),Add.add]
    exact min_assoc _ _ _

  add_comm := by
    intro a b
    simp[(· + ·),Add.add]
    exact min_comm _ _

  zero_add  := by
    intro a
    ext
    simp[(· + ·),Add.add]
    exact OrderTop.le_top _
  add_zero := by
    intro a
    ext
    simp[(· + ·),Add.add]
    exact OrderTop.le_top _

  nsmul := nsmulRec
  mul_assoc := by
    intro a b c
    simp[(· * ·),Mul.mul]
    exact max_assoc _ _ _
  mul_comm := by
    intro a b
    simp[(· * ·),Mul.mul]
    exact max_comm _ _

  left_distrib := by
    intro a b c
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    exact sup_inf_left _ _ _

  right_distrib := by
    intro a b c
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    exact sup_inf_right _ _ _

  one_mul := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderBot.bot_le _
  mul_one := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderBot.bot_le _

  zero_mul := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderTop.le_top _
  mul_zero := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderTop.le_top _

instance : SemiringWithMonus (MinMax α) where
  add_le_add_left := by
    intro a b hab c
    simp[(· + ·),Add.add,(· ≤ ·)]
    exact Or.inr hab

  exists_add_of_le := by
    intro a b hab
    use b
    ext
    simp[(· + ·),Add.add]
    exact hab

  le_self_add := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]

  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· ≤ ·),(· - ·),Sub.sub]
    split_ifs with h <;> simp <;> tauto
