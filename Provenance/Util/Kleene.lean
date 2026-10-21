/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Basic.Logic.Basic

/-!
# Kleene's three-valued logic

A comparison with a `NULL` operand is neither true nor false but *unknown*,
and SQL evaluates predicates in Kleene's strong three-valued logic. A row on
which a predicate is unknown is not selected, and neither is it selected by
the predicate's negation: `unknown` is a fixed point of negation, which is
what no two-valued reading can imitate.

The connectives are the minimum and maximum of the order
`false < unknown < true`, with negation exchanging the two definite values.
Every law of a De Morgan algebra holds; what fails is the excluded middle,
`a ⊔ ¬a = true`, exactly at `unknown`.
-/

/-- A three-valued truth value. -/
inductive Kleene where
  /-- Definitely false. -/
  | false
  /-- Neither: a comparison with a `NULL` operand. -/
  | unknown
  /-- Definitely true. -/
  | true
  deriving DecidableEq, Repr

namespace Kleene

/-- A two-valued truth value read as a three-valued one. -/
def ofBool : Bool → Kleene
  | Bool.false => Kleene.false
  | Bool.true => Kleene.true

/-- Whether the value is definitely true. This is the reading a selection
takes: a row on which the predicate is unknown is not selected. -/
def isTrue : Kleene → Bool
  | Kleene.true => Bool.true
  | _ => Bool.false

/-- Kleene negation: it exchanges the definite values and fixes
`unknown`. -/
def not : Kleene → Kleene
  | Kleene.false => Kleene.true
  | Kleene.unknown => Kleene.unknown
  | Kleene.true => Kleene.false

/-- Kleene conjunction: the minimum in `false < unknown < true`. -/
def and : Kleene → Kleene → Kleene
  | Kleene.false, _ => Kleene.false
  | _, Kleene.false => Kleene.false
  | Kleene.unknown, _ => Kleene.unknown
  | _, Kleene.unknown => Kleene.unknown
  | Kleene.true, Kleene.true => Kleene.true

/-- Kleene disjunction: the maximum in `false < unknown < true`. -/
def or : Kleene → Kleene → Kleene
  | Kleene.true, _ => Kleene.true
  | _, Kleene.true => Kleene.true
  | Kleene.unknown, _ => Kleene.unknown
  | _, Kleene.unknown => Kleene.unknown
  | Kleene.false, Kleene.false => Kleene.false

@[simp] theorem not_not (a : Kleene) : a.not.not = a := by cases a <;> rfl

@[simp] theorem not_and (a b : Kleene) : (a.and b).not = a.not.or b.not := by
  cases a <;> cases b <;> rfl

@[simp] theorem not_or (a b : Kleene) : (a.or b).not = a.not.and b.not := by
  cases a <;> cases b <;> rfl

@[simp] theorem and_eq_true_iff (a b : Kleene) :
    a.and b = Kleene.true ↔ a = Kleene.true ∧ b = Kleene.true := by
  cases a <;> cases b <;> simp [and]

@[simp] theorem or_eq_true_iff (a b : Kleene) :
    a.or b = Kleene.true ↔ a = Kleene.true ∨ b = Kleene.true := by
  cases a <;> cases b <;> simp [or]

@[simp] theorem and_eq_false_iff (a b : Kleene) :
    a.and b = Kleene.false ↔ a = Kleene.false ∨ b = Kleene.false := by
  cases a <;> cases b <;> simp [and]

@[simp] theorem or_eq_false_iff (a b : Kleene) :
    a.or b = Kleene.false ↔ a = Kleene.false ∧ b = Kleene.false := by
  cases a <;> cases b <;> simp [or]

@[simp] theorem not_eq_true_iff (a : Kleene) :
    a.not = Kleene.true ↔ a = Kleene.false := by cases a <;> simp [not]

@[simp] theorem not_eq_false_iff (a : Kleene) :
    a.not = Kleene.false ↔ a = Kleene.true := by cases a <;> simp [not]

@[simp] theorem isTrue_ofBool (b : Bool) : (ofBool b).isTrue = b := by
  cases b <;> rfl

@[simp] theorem ofBool_eq_true_iff {b : Bool} :
    ofBool b = Kleene.true ↔ b = Bool.true := by
  cases b <;> simp [ofBool]

@[simp] theorem not_ofBool (b : Bool) : (ofBool b).not = ofBool (!b) := by
  cases b <;> rfl

/-- **Unknown is neither true nor false.** A row on which a predicate is
unknown is selected by neither the predicate nor its negation, which is the
one thing a two-valued reading cannot say. -/
theorem isTrue_unknown_and_not : Kleene.unknown.isTrue = Bool.false
    ∧ Kleene.unknown.not.isTrue = Bool.false := ⟨rfl, rfl⟩

/-- The excluded middle fails, and exactly at `unknown`. -/
theorem or_not_eq_true_iff (a : Kleene) : a.or a.not = Kleene.true ↔ a ≠ Kleene.unknown := by
  cases a <;> simp [or, not]

end Kleene
