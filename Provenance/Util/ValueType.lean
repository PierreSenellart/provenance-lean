module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Defs.LinearOrder

public import Provenance.SemiringWithMonus
import Mathlib.Tactic.Bound.Init

@[expose] public section

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
  /-- **A value of its own**: one that is neither the zero nor the null. A
  domain of SQL has one, and a query needs one to mark a row with – which
  is what the difference does when it tags the two sides of a union to
  tell them apart afterwards. -/
  nonzero : T
  /-- It is not the zero. -/
  nonzero_ne_zero : nonzero ≠ 0
  /-- And it is not the null. -/
  isNull_nonzero : isNull nonzero = false := by rfl
  /-- **The domain's null, named.** SQL's `NULL` is one value of the
  domain, so `isNull` recognizes at most one value and a query may compare
  against it: `IS NULL` is `IS NOT DISTINCT FROM` that value. A domain
  without a null – `ℕ`, `String` – answers `none`, which is the default. -/
  nullVal : Option T := none
  /-- `isNull` recognizes exactly that value. -/
  isNull_iff_nullVal : ∀ a : T, isNull a = true ↔ nullVal = some a := by
    intro a
    simp

/-- A value domain in which nothing is null. The three-valued semantics
agrees with the two-valued one there, which is why every statement proved
before the null was introduced keeps saying what it said. -/
class NoNulls (T : Type) [ValueType T] : Prop where
  /-- No value is the null. -/
  isNull_eq_false : ∀ a : T, ValueType.isNull a = false

export NoNulls (isNull_eq_false)

namespace ValueType

variable {T : Type} [ValueType T]

/-- **A domain that names no null has none.** -/
theorem isNull_eq_false_of_nullVal_none
    (h : (ValueType.nullVal : Option T) = none) (a : T) :
    ValueType.isNull a = false := by
  rcases hb : ValueType.isNull a with _ | _
  · rfl
  · exact absurd ((ValueType.isNull_iff_nullVal a).mp hb) (by rw [h]; simp)

/-- A domain that names no null is a domain with no null. -/
theorem noNulls_of_nullVal_none
    (h : (ValueType.nullVal : Option T) = none) : NoNulls T :=
  ⟨isNull_eq_false_of_nullVal_none h⟩

/-- **The named value is null.** -/
theorem isNull_nullVal {ν : T} (h : (ValueType.nullVal : Option T) = some ν) :
    ValueType.isNull ν = true :=
  (ValueType.isNull_iff_nullVal ν).mpr h

/-- **And it is the only one**, which is what lets a comparison against it
read `IS NULL`. -/
theorem eq_nullVal_of_isNull {ν a : T}
    (h : (ValueType.nullVal : Option T) = some ν)
    (ha : ValueType.isNull a = true) : a = ν :=
  Option.some.inj (((ValueType.isNull_iff_nullVal a).mp ha).symm.trans h)

end ValueType

instance [ValueType V] [HasAltLinearOrder K] [SemiringWithMonus K] : ValueType (V⊕K) where
  zero := Sum.inr 0

  -- a value of the data side, which the provenance zero is not
  nonzero := Sum.inl ValueType.nonzero
  nonzero_ne_zero := by
    intro h
    exact absurd h (by simp)
  isNull_nonzero := ValueType.isNull_nonzero

  -- the rewriting domain inherits its nulls from the data side; a
  -- provenance value is never null
  isNull a := match a with
  | Sum.inl v => ValueType.isNull v
  | Sum.inr _ => false
  nullVal := (ValueType.nullVal : Option V).map Sum.inl
  isNull_iff_nullVal a := by
    cases a with
    | inl v =>
      show ValueType.isNull v = true ↔ _
      rw [ValueType.isNull_iff_nullVal v]
      constructor
      · intro h; rw [h]; rfl
      · intro h
        obtain ⟨w, hw, hwv⟩ := Option.map_eq_some_iff.mp h
        rw [hw, Sum.inl.inj hwv]
    | inr k =>
      show (false : Bool) = true ↔ _
      constructor
      · exact fun h => absurd h (by simp)
      · intro h
        obtain ⟨w, -, hwv⟩ := Option.map_eq_some_iff.mp h
        exact absurd hwv (by simp)

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


