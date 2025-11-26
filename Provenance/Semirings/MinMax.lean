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
    exact Or.inl hab

  exists_add_of_le := by
    intro a b hab
    use b
    ext
    simp[(· + ·),Add.add]
    exact hab

  le_self_add := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]

  le_add_self := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]

  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· ≤ ·),(· - ·),Sub.sub]
    split_ifs with h <;> simp <;> tauto

theorem MinMax.absorptive : absorptive (MinMax α) := by
  intro a
  simp[(· + ·), Add.add]
  congr
  simp
  left
  rfl

theorem MinMax.idempotent : idempotent (MinMax α) :=
  idempotent_of_absorptive MinMax.absorptive

abbrev MaxMin (α : Type) := MinMax (OrderDual α)

instance : CommSemiring (MaxMin α) :=
  inferInstanceAs (CommSemiring (MinMax (OrderDual α)))

instance : SemiringWithMonus (MaxMin α) :=
  inferInstanceAs (SemiringWithMonus (MinMax (OrderDual α)))

inductive TVL
| bot
| unknown
| top
deriving DecidableEq, Repr, Ord

instance : LE TVL where
  le := λ a b => (compare a b).isLE

instance : LinearOrder TVL where
  le_refl := by intro a; cases a <;> decide
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by intro a b; cases a <;> cases b <;> decide
  le_total := by intro a b; cases a <;> cases b <;> decide
  toDecidableLE := inferInstance

instance : OrderBot TVL where
  bot := TVL.bot
  bot_le := by intro a; cases a <;> decide

instance : OrderTop TVL where
  top := TVL.top
  le_top := by intro a; cases a <;> decide

instance : CommSemiring (MaxMin TVL) :=
  inferInstance

instance : SemiringWithMonus (MaxMin TVL) :=
  inferInstance

theorem TVL.not_mul_sub_left_distributive : ¬(mul_sub_left_distributive (MaxMin TVL)) := by
  simp
  use ⟨TVL.unknown⟩, ⟨TVL.top⟩, ⟨TVL.unknown⟩
  decide
