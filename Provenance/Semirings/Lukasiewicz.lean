import Provenance.SemiringWithMonus
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring.RingNF

abbrev Lukasiewicz := {q : ℚ // 0 ≤ q ∧ q ≤ 1}

instance : Zero Lukasiewicz where
  zero := ⟨0, by simp⟩

instance : One Lukasiewicz where
  one := ⟨1, by simp⟩

instance : Add Lukasiewicz where
  add a b := max a b

instance : Mul Lukasiewicz where
  mul a b :=
  let raw := max (a.val+b.val-1) 0
  have h : raw ≥ 0 ∧ raw ≤ 1 := by
    have ha := a.property
    have hb := b.property
    unfold raw
    constructor
    . simp
    . simp
      calc
        a + b ≤ (1: ℚ) + b := by simp[ha.right]
            _ ≤ (1: ℚ) + 1 := by simp[hb.right]
  ⟨raw, h⟩

instance : Sub Lukasiewicz where
  sub a b := if a≤b then ⟨0, by simp⟩ else a

theorem Lukasiewicz.sub_def (a b: Lukasiewicz) :
  a - b = if a≤b then ⟨0, by simp⟩ else a := by rfl

instance : CommMagma Lukasiewicz where
  mul_comm := by
    intro a b
    have ha := a.property
    have hb := b.property
    simp[(· * ·), Mul.mul]
    rw[add_comm]

instance instLeftDistribClassLukasiweicz : LeftDistribClass Lukasiewicz where
  left_distrib := by
    intro a b c
    simp[(· * ·), (· + ·), Mul.mul, Add.add]
    by_cases hbc: b ≤ c
    . simp[hbc]
      by_cases hab: a.val + b.val ≤ 1
      . right
        exact hab
      . left
        constructor
        . exact add_le_add (le_of_eq rfl) hbc
        . simp at hab
          have := add_le_add (le_of_eq rfl: a.val ≤ a.val) hbc
          exact le_of_lt (lt_of_lt_of_le hab this)
    . simp at hbc
      simp[le_of_lt hbc]
      by_cases hac: a.val + c.val ≤ 1
      . right
        exact hac
      . left
        constructor
        . exact add_le_add (le_of_eq rfl) (le_of_lt hbc)
        . simp at hac
          have := add_le_add (le_of_eq rfl: a.val ≤ a.val) (le_of_lt hbc)
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
    have ha := a.property.left
    simp
    apply eq_of_le_of_ge
    . simp
      exact Bool.le_of_eq ha
    . simp

  add_zero := by
    intro a
    simp[(· + ·),Add.add]
    have ha := a.property.left
    simp
    apply eq_of_le_of_ge
    . simp
      exact Bool.le_of_eq ha
    . simp

  mul_assoc := by
    intro a b c
    have ha := a.property
    have hb := b.property
    have hc := c.property
    simp[(· * ·), Mul.mul]
    rw[add_max,max_add]
    simp
    by_cases h₁ : c.val ≤ a.val + b.val - 1 + c.val
    . rw[max_eq_left h₁]
      by_cases h₂ : a.val ≤ a.val + (b.val + c.val - 1)
      . rw[max_eq_left h₂]
        ring_nf
      . rw[max_eq_right (le_of_not_ge h₂)]
        simp at h₂
        have : a.val - 1 ≤ 0 := by simp[ha.2]
        rw[max_eq_right this]
        simp
        ring_nf
        have bound : a.val + b.val + c.val < 2 := by
          calc
            a.val + b.val + c.val
              = a.val + (b.val + c.val) := by ring
            _ < a.val + 1 := add_lt_add_right h₂ a.val
            _ ≤ 1 + 1 := by simp[ha.2]
            _ = 2 := by norm_num
        have := add_lt_add_left bound (-1)
        ring_nf at this
        exact (le_of_lt this)
    . rw[max_eq_right (le_of_not_ge h₁)]
      simp at h₁
      by_cases h₂ : a.val ≤ a.val + (b.val + c.val - 1)
      . rw[max_eq_left h₂]
        simp at h₂
        have : c.val - 1 ≤ 0 := by simp[hc.2]
        rw[max_eq_right this]
        simp
        ring_nf
        have bound : a.val + b.val + c.val < 2 := by
          calc
            a.val + b.val + c.val
            _ < 1 + c.val := add_lt_add_left h₁ c.val
            _ ≤ 1 + 1 := by simp[hc.2]
            _ = 2 := by norm_num
        have := add_lt_add_left bound (-1)
        ring_nf at this
        exact (le_of_lt this)
      . rw[max_eq_right (le_of_not_ge h₂)]
        simp at h₂
        have : a.val - 1 ≤ 0 := by simp[ha.2]
        rw[max_eq_right this]
        simp
        exact hc.2

  nsmul := nsmulRec

  zero_mul := by
    intro a
    simp[(· * ·), Mul.mul]
    congr
    simp
    exact add_le_of_nonpos_of_le rfl a.property.2

  mul_zero := by
    intro a
    have ha := a.property
    simp[(· * ·), Mul.mul]
    congr
    simp
    rw[add_comm]
    exact add_le_of_nonpos_of_le rfl a.property.2

  one_mul := by
    intro a
    simp[(· * ·), Mul.mul]
    congr
    have : (1: Lukasiewicz).val = 1 := by rfl
    rw[this]
    simp
    exact a.property.1

  mul_one := by
    intro a
    simp[(· * ·), Mul.mul]
    congr
    have : (1: Lukasiewicz).val = 1 := by rfl
    rw[this]
    simp
    exact a.property.1

  left_distrib := instLeftDistribClassLukasiweicz.left_distrib

  right_distrib := by
    intro a b c
    rw[mul_comm (a+b) c,mul_comm a c,mul_comm b c]
    exact left_distrib c a b

instance : LinearOrder Lukasiewicz where
  le a b := a ≤ b
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
  lt_iff_le_not_ge := by
    intro a b
    exact Std.LawfulOrderLT.lt_iff a b
  min_def := by
    intro a b
    exact Std.min_eq_if
  max_def := by
    intro a b
    exact LinearOrder.max_def a b
  compare_eq_compareOfLessAndEq := by
    intro a b
    unfold compareOfLessAndEq compare
    by_cases hab: a<b <;> simp[hab]
    . sorry
    . sorry

instance : IsOrderedAddMonoid Lukasiewicz where
  add_le_add_left := by
    intro a b hab c
    simp[(· + ·),Add.add]
    by_cases hca : c ≤ a
    left
    . constructor
      . exact hab
      . exact Std.IsPreorder.le_trans c a b hca hab
    . simp at hca
      right
      exact Std.le_of_lt hca

instance : CanonicallyOrderedAdd Lukasiewicz where
  exists_add_of_le := by
    intro a b hab
    simp[(· + ·), Add.add]
    use b.val, b.property
    exact right_eq_sup.mpr hab

  le_self_add := by
    intro a b
    simp[(· + ·), Add.add]

  le_add_self := by
    intro a b
    simp[(· + ·), Add.add]

instance : SemiringWithMonus Lukasiewicz where
  monus_spec := by
    intro a b c
    simp[(· - ·),Sub.sub,(· + ·),Add.add]
    apply Iff.intro
    . intro h
      by_cases hab: a ≤ b
      . left
        exact hab
      . simp[hab] at h
        right
        exact h
    . intro h
      by_cases hab: a ≤ b
      . simp[hab]
        exact c.property.1
      . simp[hab] at h
        by_cases hbc: b ≤ c <;> simp[hab] <;> exact h

theorem Lukasiewicz.absorptive : absorptive Lukasiewicz := by
  intro a
  simp[(· + ·), Add.add]
  exact a.property.2

theorem Lukasiewicz.idempotent : idempotent Lukasiewicz :=
  idempotent_of_absorptive (Lukasiewicz.absorptive)

theorem Lukasiewicz.mul_sub_left_distributive :
  mul_sub_left_distributive Lukasiewicz := by
    intro a b c
    by_cases hbc: b ≤ c <;> simp[(· * ·),Mul.mul]
    . have : b-c = 0 := by
        simp[(· - ·),Sub.sub,hbc]
        rfl
      simp[this]
      have : (0: Lukasiewicz) = (0: ℚ) := rfl
      simp[this]
      have : max (a.val - 1) 0 = 0 := by
        simp[a.property]
      simp[Lukasiewicz.sub_def,this]
      intro h₁ h₂
      have h₃ := h₁ hbc
      have h₄ : a.val + b.val ≤ a.val + c.val := by
        exact Rat.add_le_add_left.mpr hbc
      have := lt_of_le_of_lt h₄ h₃
      exact le_of_lt this
    . have : b-c = b := by
        simp[(· - ·),Sub.sub,hbc]
      simp[this]
      simp at hbc
      simp[Lukasiewicz.sub_def]
      simp[not_le_of_gt hbc]
