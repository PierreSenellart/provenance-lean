import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs.LinearOrder

import Provenance.SemiringWithMonus

/-- A value domain. The `isNull` predicate says which of its values is
SQL's `NULL`; a domain without one answers `false` everywhere, which is the
default, and the three-valued semantics is then the two-valued one. Carrying
the test here rather than in a stronger class is what lets one semantics
serve both: the results proved over `ℕ`, where nothing is null, keep saying
what they said. -/
class ValueType (T : Type) extends Zero T, AddCommSemigroup T, Sub T, Mul T, LinearOrder T where
  /-- Whether a value is the null. -/
  isNull : T → Bool := fun _ => false
  /-- The domain's zero is not its null: an aggregate over no row is not an
  aggregate that came out zero. -/
  isNull_zero : isNull 0 = false := by rfl

/-- A value domain in which nothing is null. The three-valued semantics
agrees with the two-valued one there, which is why every statement proved
before the null was introduced keeps saying what it said. -/
class NoNulls (T : Type) [ValueType T] : Prop where
  /-- No value is the null. -/
  isNull_eq_false : ∀ a : T, ValueType.isNull a = false

export NoNulls (isNull_eq_false)

instance [ValueType V] [HasAltLinearOrder K] [SemiringWithMonus K] : ValueType (V⊕K) where
  zero := Sum.inr 0

  -- the rewriting domain inherits its nulls from the data side; a
  -- provenance value is never null
  isNull a := match a with
  | Sum.inl v => ValueType.isNull v
  | Sum.inr _ => false

  add a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'+b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'+b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  sub a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'-b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'-b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  mul a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'*b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'*b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp[(· + ·)] <;> exact add_assoc _ _ _

  add_comm a b := by
    cases a <;> cases b <;> simp[(· + ·)] <;> exact add_comm _ _

  le a b := match a,b with
  | Sum.inl a', Sum.inl b' => a'≤b'
  | Sum.inr a', Sum.inr b' => HasAltLinearOrder.altOrder.le a' b'
  | Sum.inl a', Sum.inr b' => True
  | Sum.inr a', Sum.inl b' => False

  le_refl a := by
    cases a <;> simp

  le_antisymm a b := by
    cases a <;> cases b <;> simp
    . exact le_antisymm
    . exact HasAltLinearOrder.altOrder.le_antisymm _ _

  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp
    . exact le_trans
    . exact HasAltLinearOrder.altOrder.le_trans _ _ _

  le_total a b := by
    cases a <;> cases b <;> simp
    . exact le_total _ _
    . rename_i x y
      exact HasAltLinearOrder.altOrder.le_total x y

  toDecidableLE :=
    λ a b ↦ match a, b with
    | Sum.inl a', Sum.inl b' => inferInstance
    | Sum.inr a', Sum.inr b' => inferInstance
    | Sum.inl a', Sum.inr b' => isTrue (trivial)
    | Sum.inr a', Sum.inl b' => isFalse (id)

instance [ToString V] [ToString K] : ToString (V⊕K) where
  toString a := match a with
  | Sum.inl a => toString a
  | Sum.inr a => toString a

instance [ValueType V] [NoNulls V] [HasAltLinearOrder K] [SemiringWithMonus K] :
    NoNulls (V⊕K) where
  isNull_eq_false a := by
    cases a with
    | inl v => exact isNull_eq_false v
    | inr _ => rfl


