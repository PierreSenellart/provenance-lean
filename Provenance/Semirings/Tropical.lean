import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Real.Basic

import Provenance.SemiringWithMonus

/-!
# Tropical m-semiring

This file shows that the tropicalization of any linearly ordered additive commutative
monoid with an absorbing top element (e.g., `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, `ℝ ∪ {∞}`) is a
commutative m-semiring. Addition is `min` (inherited from the tropical structure in
Mathlib), multiplication is the original addition of the monoid, zero is `⊤`, and one
is `0`.

The tropical semiring is absorptive and idempotent, and satisfies left-distributivity
of multiplication over monus.

The tropical semiring is used as a provenance semiring in
[Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance].

Note: [Geerts & Poggi, *On database query languages for K-relations*, Example 4][geerts2010database]
claims that the tropical semiring cannot be extended to an m-semiring. That claim is
incorrect: the paper gives a wrong definition of the monus operator.

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Geerts & Poggi, *On database query languages for K-relations*][geerts2010database]
-/

instance [ToString α] : ToString (WithTop α) where
  toString x := match x with | none => "⊤" | some x => toString x

instance [ToString α] : ToString (Tropical α) where
  toString x := toString ((x.untrop: α))

/-- In the tropicalization of a linear order, `a ≥ b` if and only if
`a+b = b`. -/
theorem tropical_order_ge [LinearOrder α] :
  ∀ a b: Tropical α, a.untrop ≥ b.untrop ↔ a+b = b := by
    intro a b
    exact Tropical.add_eq_right_iff.symm

/-- The tropical semiring is an m-semiring. The natural order of the
semiring is the reverse of the usual order. The monus `a-b` is defined as
`⊤` if `a≥b` (for the usual order, not the natural semiring order), and
as `a` otherwise. -/
instance [LinearOrderedAddCommMonoidWithTop α] : SemiringWithMonus (Tropical α) where
  sub a b := if (Tropical.untrop a ≥ Tropical.untrop b) then ⊤ else a
  le a b := Tropical.untrop a ≥ Tropical.untrop b
  lt a b := a+b = b ∧ a ≠ b
  lt_iff_le_not_ge := by
    intro a b
    rw[tropical_order_ge,tropical_order_ge]
    apply Iff.intro
    . intro h
      constructor
      . tauto
      . obtain ⟨h₁, h₂⟩ := h
        rw[add_comm, h₁]
        tauto
    . intro h
      obtain ⟨h₁, h₂⟩ := h
      constructor
      . tauto
      . rw[add_comm, h₁] at h₂
        tauto

  le_refl := by simp
  le_trans := by
    intro a b c hab hbc
    rw[tropical_order_ge]
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hbc
    calc
      a + c = a + b + c := by simp[hbc,add_assoc]
          _ = b + c     := by simp[hab]
              _ = c     := by simp[hbc]

  le_antisymm := by
    intro a b hab hba
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hba
    calc
      a = b + a := by simp[hba]
      _ = a + b := by simp[add_comm]
      _ = b     := by simp[hab]

  add_le_add_left := by
    intro a b h c

    rw[tropical_order_ge]
    rw[tropical_order_ge] at h

    calc
      a + c + (b + c) = c + a + (c + b)   := by simp[add_comm]
                    _ = c + (a + (c + b)) := by rw[add_assoc]
                    _ = c + (a + c + b)   := by rw[add_assoc]
                    _ = c + (c + a + b)   := by rw[add_comm a c]
                    _ = c + (c + (a + b)) := by rw[add_assoc]
                    _ = c + (c + b)       := by rw[h]
                    _ = c + c + b         := by rw[add_assoc]
                    _ = c + b             := by simp

    simp[add_comm]

  exists_add_of_le := by
    intro a b h
    rw[tropical_order_ge] at h
    use b
    simp[h]

  le_self_add := by
    intro a b
    rw[tropical_order_ge]
    calc
      a + (a + b) = a + a + b := by rw[add_assoc]
                _ = a + b     := by simp

  le_add_self := by
    simp[add_comm]

  monus_spec := by
    intro a b c
    simp[(· - ·)]
    split_ifs with h
    . simp
      left
      simp at h
      exact h
    . simp at h
      apply Iff.intro
      . tauto
      . intro h'
        cases h' with
        | inl h'' =>
          apply lt_of_lt_of_le h at h''
          apply lt_irrefl at h''
          contradiction
        | inr h'' =>
          exact h''

/-- The tropical semiring over `ℕ ∪ {∞}` is a semiring with monus. -/
instance : SemiringWithMonus (Tropical (WithTop ℕ)) := inferInstance
/-- The tropical semiring over `ℚ ∪ {∞}` is a semiring with monus. -/
instance : SemiringWithMonus (Tropical (WithTop ℚ)) := inferInstance

/-- The tropical semiring over `ℝ ∪ {∞}` is a semiring with monus. Note
that this contradicts [Geerts & Poggi, *On database query languages for
K-relations*, Example 4][geerts2010database] which claims this semiring
cannot be extended to a semiring with monus: indeed, that paper gives
a wrong definition of the monus operator in the tropical semiring. -/
noncomputable instance : SemiringWithMonus (Tropical (WithTop ℝ)) := inferInstance

/-- The tropical semiring is absorptive, as long as the order in the
  addition monoid corresponds to a canonical order (e.g., as in ℕ) --/
theorem Tropical.absorptive [LinearOrderedAddCommMonoidWithTop α] [CanonicallyOrderedAdd α] : absorptive (Tropical α) := by
  intro a
  simp only[(· + ·), Add.add]
  congr
  simp[untrop_one]

theorem TropicalN.absorptive : absorptive (Tropical (WithTop ℕ)) := by
  exact Tropical.absorptive

/-- Times distributes over monus on tropical semirings made of an order
  strictly compatible with addition, with an additional top element. -/
theorem Tropical.mul_sub_left_distributive
  [LinearOrder α] [AddCancelCommMonoid α] [IsOrderedAddMonoid α] [AddLeftStrictMono α]:
  mul_sub_left_distributive (Tropical (WithTop α)) := by
    intro a b c
    simp[(· - ·), Sub.sub]
    split_ifs with h₁ h₂ h₃
    . exact mul_zero _
    . simp at *
      simp only[(· ≤ ·)] at h₁
      have h' := add_le_add_right h₁ (untrop a)
      have contradiction := lt_of_lt_of_le h₂ h'
      simp at contradiction
    . simp only[(· ≤ ·)] at h₁
      have h : untrop b < untrop c := by
        exact lt_of_not_ge h₁
      by_cases ha: untrop a = ⊤
      . simp only[ha,(· * ·),Mul.mul]
        rfl
      . have h_lt : untrop a + untrop b < untrop a + untrop c :=
          WithTop.add_lt_add_left ha h
        have contradiction := lt_of_lt_of_le h_lt h₃
        simp at contradiction
    . rfl

theorem TropicalN.mul_sub_left_distributive : mul_sub_left_distributive (Tropical (WithTop ℕ)) := by
  exact Tropical.mul_sub_left_distributive
theorem TropicalQ.mul_sub_left_distributive : mul_sub_left_distributive (Tropical (WithTop ℚ)) := by
  exact Tropical.mul_sub_left_distributive
theorem TropicalR.mul_sub_left_distributive : mul_sub_left_distributive (Tropical (WithTop ℝ)) := by
  exact Tropical.mul_sub_left_distributive

/-- The tropical semiring is idempotent --/
theorem Tropical.idempotent [LinearOrderedAddCommMonoidWithTop α] : idempotent (Tropical α) := by
  intro a
  simp[(· + ·), Add.add]

/-- The tropical semiring over `WithTop R` (for any `R` with `Zero R`) has characteristic 0
in the `CharP` sense: it is idempotent, and `(0 : Tropical (WithTop R)) = trop ⊤` differs from
`(1 : Tropical (WithTop R)) = trop 0` since `⊤ ≠ 0` in `WithTop R`. -/
instance TropicalN.instCharPZero : CharP (Tropical (WithTop ℕ)) 0 :=
  CharP.zero_of_idempotent Tropical.idempotent
instance TropicalQ.instCharPZero : CharP (Tropical (WithTop ℚ)) 0 :=
  CharP.zero_of_idempotent Tropical.idempotent
noncomputable instance TropicalR.instCharPZero : CharP (Tropical (WithTop ℝ)) 0 :=
  CharP.zero_of_idempotent Tropical.idempotent
