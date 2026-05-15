import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring.RingNF

/-!
# Łukasiewicz m-semiring

This file defines the *Łukasiewicz* (fuzzy logic) semiring over rationals `[0,1]`.
Addition is `max`, multiplication is the Łukasiewicz t-norm `max(a + b - 1, 0)`,
zero is `0`, and one is `1`.

The Łukasiewicz semiring is absorptive and idempotent, and satisfies left-distributivity
of multiplication over monus.

This semiring is discussed as a provenance semiring in
[Grädel & Tannen, *Provenance Analysis and Semiring Semantics for First-Order Logic*][gradel2005provenance].

## References

* [Grädel & Tannen, *Provenance Analysis and Semiring Semantics for First-Order Logic*][gradel2005provenance]
-/

/-- The Łukasiewicz semiring: rationals in `[0,1]` with `max` as addition and the
Łukasiewicz t-norm `max(a + b - 1, 0)` as multiplication. -/
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
    unfold compareOfLessAndEq
    by_cases hab: a<b <;> simp[hab]
    . apply compare_lt_iff_lt.mpr
      exact hab
    . by_cases habeq: a=b <;> simp[habeq]
      . apply compare_gt_iff_gt.mpr
        simp at hab
        exact lt_of_le_of_ne hab (fun a ↦ habeq (id (Eq.symm a)))

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

instance : Nontrivial Lukasiewicz :=
  ⟨0, 1, fun h => zero_ne_one (Subtype.ext_iff.mp h)⟩

theorem Lukasiewicz.absorptive : absorptive Lukasiewicz := by
  intro a
  simp[(· + ·), Add.add]
  exact a.property.2

theorem Lukasiewicz.idempotent : idempotent Lukasiewicz :=
  idempotent_of_absorptive (Lukasiewicz.absorptive)

/-- `Lukasiewicz` has characteristic 0 in the `CharP` sense: it is idempotent and
nontrivial, so every positive natural-number cast equals `1`. -/
instance Lukasiewicz.instCharPZero : CharP Lukasiewicz 0 :=
  CharP.zero_of_idempotent Lukasiewicz.idempotent

/-- ProvSQL's `Lukasiewicz::delta`: the support indicator. -/
private def Lukasiewicz.deltaInd (a : Lukasiewicz) : Lukasiewicz :=
  if a = 0 then 0 else 1

private theorem Lukasiewicz.deltaInd_isIndicator : IsDeltaIndicator Lukasiewicz.deltaInd where
  zero := by simp [Lukasiewicz.deltaInd]
  nonzero := fun a ha => by simp [Lukasiewicz.deltaInd, ha]

/-- `Lukasiewicz` is a commutative m-semiring. The natural order is the usual rational
order, and the monus is `a` if `a > b`, `0` if `a ≤ b`. The δ operator matches ProvSQL's
`Lukasiewicz::delta`: the support indicator. -/
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
  delta := Lukasiewicz.deltaInd
  delta_zero := Lukasiewicz.deltaInd_isIndicator.zero
  delta_natCast_pos := delta_natCast_pos_indicator Lukasiewicz.deltaInd_isIndicator
  delta_regrouping := delta_regrouping_indicator Lukasiewicz.deltaInd_isIndicator

/-- Łukasiewicz multiplication is not idempotent: `(1/2) * (1/2) = max(0, 0) = 0 ≠ 1/2`. -/
theorem Lukasiewicz.not_mul_idempotent : ¬ ∀ a : Lukasiewicz, a * a = a := by
  push Not
  have h0 : (0 : ℚ) ≤ (1 : ℚ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]; norm_num
  have h1 : (1 : ℚ) / 2 ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 2)]; norm_num
  refine ⟨⟨(1 : ℚ) / 2, ⟨h0, h1⟩⟩, ?_⟩
  intro h
  have h' := congrArg Subtype.val h
  simp [(· * ·), Mul.mul] at h'
  have hmax : max ((2 : ℚ)⁻¹ + (2 : ℚ)⁻¹ - 1) 0 = 0 :=
    max_eq_right (by norm_num)
  rw [hmax] at h'
  have hpos : (0 : ℚ) < (2 : ℚ)⁻¹ := by
    rw [inv_pos]; norm_num
  exact hpos.ne h'

/-- There is no semiring homomorphism from `BoolFunc Y` to the Łukasiewicz
semiring sending the variables to arbitrary values: Łukasiewicz multiplication
is not idempotent (`(1/2) ⊗ (1/2) = 0 ≠ 1/2`), contradicting
`var i * var i = var i` in `BoolFunc Y`. -/
theorem Lukasiewicz.no_hom_from_BoolFunc {Y : Type} [Inhabited Y] :
    ∃ ν : Y → Lukasiewicz,
      ¬ ∃ φ : BoolFunc Y →+* Lukasiewicz, ∀ i : Y, φ (BoolFunc.var i) = ν i :=
  BoolFunc.no_hom_of_not_mul_idem Lukasiewicz.not_mul_idempotent

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
