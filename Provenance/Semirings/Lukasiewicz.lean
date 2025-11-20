import Provenance.SemiringWithMonus
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring.RingNF

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

instance : CommMagma Lukasiewicz where
  mul_comm := by
    intro a b
    have ha := a.carrier.property
    have hb := b.carrier.property
    simp[(· * ·), Mul.mul]
    rw[add_comm]

instance instLeftDistribClassLukasiweicz : LeftDistribClass Lukasiewicz where
  left_distrib := by
    intro a b c
    simp[(· * ·), (· + ·), Mul.mul, Add.add]
    by_cases hbc: b.carrier ≤ c.carrier
    . simp[hbc]
      by_cases hab: a.carrier.val + b.carrier.val ≤ 1
      . right
        exact hab
      . left
        constructor
        . exact add_le_add (le_of_eq rfl) hbc
        . simp at hab
          have := add_le_add (le_of_eq rfl: a.carrier.val ≤ a.carrier.val) hbc
          exact le_of_lt (lt_of_lt_of_le hab this)
    . simp at hbc
      simp[le_of_lt hbc]
      by_cases hac: a.carrier.val + c.carrier.val ≤ 1
      . right
        exact hac
      . left
        constructor
        . exact add_le_add (le_of_eq rfl) (le_of_lt hbc)
        . simp at hac
          have := add_le_add (le_of_eq rfl: a.carrier.val ≤ a.carrier.val) (le_of_lt hbc)
          exact le_of_lt (lt_of_lt_of_le hac this)

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
    apply eq_of_le_of_ge
    . simp
      exact ha
    . simp

  add_zero := by
    intro a
    simp[(· + ·),Add.add]
    have ha := a.carrier.property.left
    ext
    simp
    apply eq_of_le_of_ge
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
    by_cases h₁ : c.carrier.val ≤ a.carrier.val + b.carrier.val - 1 + c.carrier.val
    . rw[max_eq_left h₁]
      by_cases h₂ : a.carrier.val ≤ a.carrier.val + (b.carrier.val + c.carrier.val - 1)
      . rw[max_eq_left h₂]
        ring_nf
      . rw[max_eq_right (le_of_not_ge h₂)]
        simp at h₂
        have : a.carrier.val - 1 ≤ 0 := by simp[ha.2]
        rw[max_eq_right this]
        simp
        ring_nf
        have bound : a.carrier.val + b.carrier.val + c.carrier.val < 2 := by
          calc
            a.carrier.val + b.carrier.val + c.carrier.val
              = a.carrier.val + (b.carrier.val + c.carrier.val) := by ring
            _ < a.carrier.val + 1 := add_lt_add_left h₂ a.carrier.val
            _ ≤ 1 + 1 := by simp[ha.2]
            _ = 2 := by norm_num
        have := add_lt_add_left bound (-1)
        ring_nf at this
        exact (le_of_lt this)
    . rw[max_eq_right (le_of_not_ge h₁)]
      simp at h₁
      by_cases h₂ : a.carrier.val ≤ a.carrier.val + (b.carrier.val + c.carrier.val - 1)
      . rw[max_eq_left h₂]
        simp at h₂
        have : c.carrier.val - 1 ≤ 0 := by simp[hc.2]
        rw[max_eq_right this]
        simp
        ring_nf
        have bound : a.carrier.val + b.carrier.val + c.carrier.val < 2 := by
          calc
            a.carrier.val + b.carrier.val + c.carrier.val
            _ < 1 + c.carrier.val := add_lt_add_right h₁ c.carrier.val
            _ ≤ 1 + 1 := by simp[hc.2]
            _ = 2 := by norm_num
        have := add_lt_add_left bound (-1)
        ring_nf at this
        exact (le_of_lt this)
      . rw[max_eq_right (le_of_not_ge h₂)]
        simp at h₂
        have : a.carrier.val - 1 ≤ 0 := by simp[ha.2]
        rw[max_eq_right this]
        simp
        exact hc.2

  nsmul := nsmulRec

  zero_mul := by
    intro a
    simp[(· * ·), Mul.mul]
    congr
    simp
    exact add_le_of_nonpos_of_le rfl a.carrier.property.2

  mul_zero := by
    intro a
    have ha := a.carrier.property
    simp[(· * ·), Mul.mul]
    congr
    simp
    rw[add_comm]
    exact add_le_of_nonpos_of_le rfl a.carrier.property.2

  one_mul := by
    intro a
    simp[(· * ·), Mul.mul]
    congr
    have : (Lukasiewicz.carrier 1).val = 1 := by rfl
    rw[this]
    simp
    exact a.carrier.property.1

  mul_one := by
    intro a
    simp[(· * ·), Mul.mul]
    congr
    have : (Lukasiewicz.carrier 1).val = 1 := by rfl
    rw[this]
    simp
    exact a.carrier.property.1

  left_distrib := instLeftDistribClassLukasiweicz.left_distrib

  right_distrib := by
    intro a b c
    rw[mul_comm (a+b) c,mul_comm a c,mul_comm b c]
    exact left_distrib c a b

instance : LinearOrder Lukasiewicz where
  le a b := a.carrier ≤ b.carrier
  le_refl := by simp
  le_antisymm := by
    intro a b hab hba
    ext
    have := le_antisymm hab hba
    exact congrArg _ this
  le_trans := by
    intro a b c hab hbc
    exact le_trans hab hbc
  le_total := by
    intro a b
    exact le_total _ _
  toDecidableLE := inferInstance

instance : IsOrderedAddMonoid Lukasiewicz where
  add_le_add_left := by
    intro a b hab c
    simp[(· + ·),Add.add]
    by_cases hca : c.carrier ≤ a.carrier
    . rw[max_eq_right hca]
      rw[max_eq_right (le_trans hca hab)]
      exact hab
    . simp at hca
      rw[max_eq_left (le_of_lt hca)]
      exact le_max_left c.carrier b.carrier

instance : CanonicallyOrderedAdd Lukasiewicz where
  exists_add_of_le := by
    intro a b hab
    simp[(· + ·), Add.add]
    use b
    rw[@max_eq_right _ _ a.carrier b.carrier hab]

  le_self_add := by
    intro a b
    simp[(· + ·), Add.add]
    exact le_max_left a.carrier b.carrier

instance : SemiringWithMonus Lukasiewicz where
  monus_spec := by
    intro a b c
    simp[(· - ·),Sub.sub,(· + ·),Add.add]
    apply Iff.intro
    . intro h
      by_cases hab: a.carrier ≤ b.carrier
      . apply le_trans hab
        exact le_max_left b.carrier c.carrier
      . simp[hab] at h
        simp at hab
        have hbc : b.carrier ≤ c.carrier := le_trans (le_of_lt hab) h
        simp[hbc]
        exact h
    . intro h
      by_cases hab: a.carrier ≤ b.carrier
      . simp[hab]
        exact c.carrier.property.1
      . simp[hab]
        by_cases hbc: b.carrier ≤ c.carrier
        . simp[hbc] at h
          exact h
        . simp at hbc
          simp[le_of_lt hbc] at h
          contradiction

theorem Lukasiewicz.absorptive : absorptive Lukasiewicz := by
  intro a
  simp[(· + ·), Add.add]
  congr
  refine max_eq_left ?_
  have h₁ := a.1.2.2
  have h₂ : (One.one: Lukasiewicz).1.1 = (1: ℚ) := by
    rfl
  simp[← h₂] at h₁
  exact h₁

theorem Lukasiewicz.idempotent : idempotent Lukasiewicz :=
  idempotent_of_absorptive (Lukasiewicz.absorptive)
