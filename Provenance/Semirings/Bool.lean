import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc

/-!
# Boolean m-semiring

This file shows that `Bool` (with `||` as addition and `&&` as multiplication) is a
commutative m-semiring. It is the simplest m-semiring and serves as the target of the
natural homomorphism from `BoolFunc X`.

The semiring is absorptive (`true || a = true`), idempotent, and satisfies
left-distributivity of multiplication over monus.
-/

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


/-- The Boolean semiring (`Bool`, `||`, `&&`) is an m-semiring. The natural order is
the usual Boolean order (`false ≤ true`), and the monus is `a && !b`. The δ operator
matches ProvSQL's `Boolean::delta`: it is the identity. -/
instance : SemiringWithMonus Bool where
  le_self_add := by decide
  le_add_self := by decide
  add_le_add_left := by decide
  exists_add_of_le := by decide
  monus_spec := by decide
  delta := id
  delta_zero := rfl
  delta_natCast_pos := fun hn => delta_natCast_pos_id (by decide) hn
  delta_regrouping := delta_regrouping_id

instance : CommSemiringWithMonus Bool where
  mul_comm := mul_comm


theorem Bool.absorptive : absorptive Bool := by decide

theorem Bool.idempotent : idempotent Bool := by decide

theorem Bool.mul_sub_left_distributive : mul_sub_left_distributive Bool := by decide

/-- `Bool` has characteristic 0 in the `CharP` sense: it is idempotent and nontrivial
(`true ≠ false`), so every positive natural-number cast equals `1 = true`. It is not
`CharZero` since the cast `ℕ → Bool` is not injective. -/
instance Bool.instCharPZero : CharP Bool 0 := CharP.zero_of_idempotent Bool.idempotent

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
      map_delta := by intro a; rfl
    }
    simp
    by_contra heq
    have := congrFun heq default
    tauto

/-- For any assignment `ν : X → Bool` of Boolean variables to Booleans, the
evaluation map `f ↦ f ν` is an m-semiring homomorphism `BoolFunc X → Bool`
sending each variable `BoolFunc.var i` to `ν i`. -/
theorem Bool.homomorphism_to_BoolFunc {X : Type} :
    ∀ ν : X → Bool,
      ∃ h : SemiringWithMonusHom (BoolFunc X) Bool,
        ∀ i : X, h (BoolFunc.var i) = ν i := by
  intro ν
  refine ⟨{
    toFun     := fun f => f ν
    map_zero' := rfl
    map_one'  := rfl
    map_add'  := by intro a b; rfl
    map_mul'  := by intro a b; rfl
    map_sub   := by intro a b; rfl
    map_delta := by intro a; rfl
  }, ?_⟩
  intro i
  rfl

end Bool
