/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Util.ValueType
import Provenance.Util.Kleene
import Provenance.Algorithms.CompOp

/-!
# Value domains with a null

SQL's `NULL` is a value of the domain like any other, and it is the same
value in every possible world: it is not an unknown ranging over values.
What sets it apart is how the operations treat it. Arithmetic is
*null-strict* – a `NULL` operand makes the result `NULL` – and a comparison
with a `NULL` operand is neither true nor false but `unknown`
(`Provenance.Util.Kleene`).

Two equalities follow, as in SQL. *Comparison* equality is the three-valued
one, `CompOp.eval3 CompOp.eq`, which is never true of a `NULL`. *Syntactic*
equality is `=` on the domain, under which two `NULL`s are identical; it is
what grouping, partitioning, duplicate elimination and difference use, and
it is two-valued. The library already decides those four with `DecidableEq`,
so they need nothing new: what this module adds is the null, the strictness
it obeys, and the three-valued comparison.

`ValueTypeNull` extends `ValueType` rather than replacing it, so that the
statements proved over a domain without a null stay true as stated, and
`WithNull T` builds the canonical instance over any value type: a copy of
`T` with one further value, where strictness holds by construction.
-/

/-- A value domain with a null: null-strict arithmetic, and a null distinct
from the zero of the domain. -/
class ValueTypeNull (T : Type) extends ValueType T where
  /-- The distinguished value. -/
  null : T
  /-- The domain's null test is the test for that value. -/
  isNull_iff : ∀ a : T, ValueType.isNull a = decide (a = null)
  /-- The null is not the domain's zero: an aggregate over no row is not an
  aggregate that came out zero. -/
  null_ne_zero : null ≠ 0
  /-- Addition is null-strict. -/
  null_add : ∀ a : T, null + a = null
  /-- Subtraction is null-strict on the left. -/
  null_sub : ∀ a : T, null - a = null
  /-- Subtraction is null-strict on the right. -/
  sub_null : ∀ a : T, a - null = null
  /-- Multiplication is null-strict on the left. -/
  null_mul : ∀ a : T, null * a = null
  /-- Multiplication is null-strict on the right. -/
  mul_null : ∀ a : T, a * null = null

namespace ValueTypeNull

variable {T : Type} [ValueTypeNull T]

/-- Addition is null-strict on the right, by commutativity. -/
theorem add_null (a : T) : a + null = (null : T) := by
  rw [add_comm]; exact null_add a

end ValueTypeNull

/-! ## The three-valued comparison -/

/-- **Three-valued evaluation of a comparison**: `unknown` as soon as an
operand is `NULL`, and the two-valued answer otherwise. -/
def CompOp.eval3 {T : Type} [ValueType T] (op : CompOp) (a b : T) : Kleene :=
  if ValueType.isNull a ∨ ValueType.isNull b then Kleene.unknown
  else Kleene.ofBool (decide (op.eval a b))

section Comparison

variable {T : Type} [ValueType T]

@[simp] theorem CompOp.eval3_of_isNull_left (op : CompOp) {a : T}
    (h : ValueType.isNull a = true) (b : T) : op.eval3 a b = Kleene.unknown := by
  simp [CompOp.eval3, h]

@[simp] theorem CompOp.eval3_of_isNull_right (op : CompOp) (a : T) {b : T}
    (h : ValueType.isNull b = true) : op.eval3 a b = Kleene.unknown := by
  simp [CompOp.eval3, h]

/-- **Away from the null the three-valued reading is the two-valued one.**
This is what lets the statements proved under two-valued logic be recovered:
they are the null-free case. -/
theorem CompOp.eval3_eq_true_iff (op : CompOp) {a b : T}
    (ha : ValueType.isNull a = false) (hb : ValueType.isNull b = false) :
    op.eval3 a b = Kleene.true ↔ op.eval a b := by
  simp [CompOp.eval3, ha, hb]

/-- **On a domain where nothing is null the comparison is two-valued.** -/
theorem CompOp.eval3_eq_ofBool [NoNulls T] (op : CompOp) (a b : T) :
    op.eval3 a b = Kleene.ofBool (decide (op.eval a b)) := by
  simp [CompOp.eval3, isNull_eq_false a, isNull_eq_false b]

/-- **The negator is the three-valued negation**, and unconditionally so.
Away from the null it is the Boolean complement; at the null both readings
are `unknown`, and Kleene negation fixes `unknown` – so the equality holds
there not because the negator complements anything but because there is
nothing to complement. Pushing `NOT` through a comparison by PostgreSQL's
operator negator is therefore sound as it stands. -/
@[simp] theorem CompOp.negate_eval3 (op : CompOp) (a b : T) :
    op.negate.eval3 a b = (op.eval3 a b).not := by
  unfold CompOp.eval3
  by_cases h : ValueType.isNull a ∨ ValueType.isNull b
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, Kleene.not_ofBool]
    refine congrArg Kleene.ofBool ?_
    by_cases hop : op.eval a b
    · simp [hop, CompOp.negate_eval]
    · simp [hop, CompOp.negate_eval]

end Comparison

section Null

variable {T : Type} [ValueTypeNull T]

@[simp] theorem ValueTypeNull.isNull_null :
    ValueType.isNull (ValueTypeNull.null : T) = true := by
  simp [ValueTypeNull.isNull_iff]

@[simp] theorem CompOp.eval3_null_left (op : CompOp) (b : T) :
    op.eval3 (ValueTypeNull.null : T) b = Kleene.unknown :=
  CompOp.eval3_of_isNull_left op ValueTypeNull.isNull_null b

@[simp] theorem CompOp.eval3_null_right (op : CompOp) (a : T) :
    op.eval3 a (ValueTypeNull.null : T) = Kleene.unknown :=
  CompOp.eval3_of_isNull_right op a ValueTypeNull.isNull_null

/-- **Syntactic equality**, SQL's `IS NOT DISTINCT FROM`: the two values are
the same value, two nulls being the same value. It is two-valued, and it is
what grouping, partitioning, duplicate elimination and difference use. -/
theorem synEq_iff (a b : T) :
    a = b ↔ (CompOp.eq.eval3 a b = Kleene.true
      ∨ (a = ValueTypeNull.null ∧ b = ValueTypeNull.null)) := by
  have hn : ∀ x : T, ValueType.isNull x = decide (x = ValueTypeNull.null) :=
    ValueTypeNull.isNull_iff
  by_cases ha : a = ValueTypeNull.null
  · subst ha
    by_cases hb : b = ValueTypeNull.null
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  · by_cases hb : b = ValueTypeNull.null
    · subst hb; simp [ha]
    · rw [CompOp.eval3_eq_true_iff CompOp.eq (by simp [hn, ha]) (by simp [hn, hb])]
      simp [ha, CompOp.eval]


end Null

/-! ## The canonical null-bearing domain

Adjoining one value to a value type gives a `ValueTypeNull`, with strictness
holding by construction: the operations are defined only where both operands
are. This is the domain the examples use, and the one an implementation's
nullable column has. -/

/-- A value type with one further value adjoined, the null. -/
def WithNull (T : Type) := Option T

namespace WithNull

/-- The adjoined value. -/
def nil : WithNull T := none

/-- A value of the domain, read in the adjoined domain. -/
def val (x : T) : WithNull T := some x

instance [DecidableEq T] : DecidableEq (WithNull T) :=
  inferInstanceAs (DecidableEq (Option T))

/-- The canonical order, with the null first. It orders group and frame
sequences and has no `ORDER BY` meaning, so where the null falls in it is
immaterial. -/
instance [LinearOrder T] : LinearOrder (WithNull T) :=
  inferInstanceAs (LinearOrder (WithBot T))

instance [Zero T] : Zero (WithNull T) := ⟨val 0⟩

instance [Add T] : Add (WithNull T) where
  add a b := Option.map₂ (· + ·) a b

instance [Sub T] : Sub (WithNull T) where
  sub a b := Option.map₂ (· - ·) a b

instance [Mul T] : Mul (WithNull T) where
  mul a b := Option.map₂ (· * ·) a b

instance [AddCommSemigroup T] : AddCommSemigroup (WithNull T) where
  add_assoc a b c := by
    rcases a with _ | x <;> rcases b with _ | y <;> rcases c with _ | z <;>
      first | rfl | exact congrArg some (add_assoc x y z)
  add_comm a b := by
    rcases a with _ | x <;> rcases b with _ | y <;>
      first | rfl | exact congrArg some (add_comm x y)

/-- The adjoined value is the null, and nothing else is. -/
instance instValueType [ValueType T] : ValueType (WithNull T) where
  isNull a := (a : Option T).isNone

instance [ValueType T] : ValueTypeNull (WithNull T) where
  null := nil
  isNull_iff a := by
    rcases a with _ | x
    · rfl
    · simp [ValueType.isNull, nil]
  null_ne_zero := by
    show (none : Option T) ≠ (some 0 : Option T)
    simp
  null_add _ := rfl
  null_sub _ := rfl
  sub_null a := by rcases a with _ | x <;> rfl
  null_mul _ := rfl
  mul_null a := by rcases a with _ | x <;> rfl

@[simp] theorem null_eq_nil [ValueType T] :
    (ValueTypeNull.null : WithNull T) = nil := rfl

@[simp] theorem val_ne_null [ValueType T] (x : T) :
    (val x : WithNull T) ≠ ValueTypeNull.null := by
  simp [val, nil]

end WithNull

namespace WithNull

instance [ToString T] : ToString (WithNull T) where
  toString a := match (a : Option T) with
    | none => "NULL"
    | some x => toString x

end WithNull
