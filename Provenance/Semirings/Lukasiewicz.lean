import Provenance.SemiringWithMonus
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Order.Ring.Rat

abbrev Interval01 := {q : ℚ // 0 ≤ q ∧ q ≤ 1}

@[ext]
structure Lukasiewicz where
  carrier : Interval01

instance : Coe Lukasiewicz Interval01 := ⟨Lukasiewicz.carrier⟩

instance : Zero Lukasiewicz where
  zero := ⟨⟨0, by simp⟩⟩

instance : One Lukasiewicz where
  one := ⟨⟨1, by simp⟩⟩

instance : Add Lukasiewicz where
  add a b := ⟨max a.carrier b.carrier⟩

instance : Mul Lukasiewicz where
  mul a b :=
  let raw := max (a.carrier.val+b.carrier.val-1) 0
  have h : raw ≥ 0 ∧ raw ≤ 1 := by
    have ha := a.carrier.property
    have hb := b.carrier.property
    unfold raw
    constructor
    . simp
    . simp
      calc
        a.carrier + b.carrier ≤ (1: ℚ) + b.carrier := by simp[ha.right]
                            _ ≤ (1: ℚ) + 1         := by simp[hb.right]
  ⟨raw, h⟩

instance : Sub Lukasiewicz where
  sub a b := if a.carrier≤b.carrier then ⟨⟨0, by simp⟩⟩ else a

instance : CommSemiring Lukasiewicz where
  add_assoc := by
    intro a b c
    simp[(· + ·),Add.add]
    apply max_assoc

  add_comm := by
    intro a b
    simp[(· + ·),Add.add]
    apply max_comm

  zero_add := by
    intro a
    simp[(· + ·),Add.add]
    have ha := a.carrier.property.left
    ext
    simp
    apply eq_of_le_of_le
    . simp
      exact ha
    . simp

  add_zero := by
    intro a
    simp[(· + ·),Add.add]
    have ha := a.carrier.property.left
    ext
    simp
    apply eq_of_le_of_le
    . simp
      exact ha
    . simp

  mul_assoc := by
    intro a b c
    have ha := a.carrier.property
    have hb := b.carrier.property
    have hc := c.carrier.property
    simp[(· * ·), Mul.mul]
    rw[add_max,max_add]
    simp
    sorry
