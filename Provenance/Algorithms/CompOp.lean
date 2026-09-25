/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder

/-!
# Comparison operator for HAVING enumeration algorithms

Shared definition used by `Provenance.Algorithms.CountEnum`,
`Provenance.Algorithms.SumDP` and `Provenance.HavingMinMax`. The operator
parameter is `op ∈ {=, ≠, <, ≤, >, ≥}`.
-/

/-- Comparison operator, as used by the HAVING enumeration algorithms.

`syneq` and `synne` are SQL's `IS NOT DISTINCT FROM` and `IS DISTINCT
FROM`: they compare values as values, two nulls being the same value, and
so are never unknown. Every other comparison is null-strict
(`CompOp.strict`). The distinction is what grouping, partitioning,
duplicate elimination and difference need, since they key on values and
not on the three-valued equality. -/
inductive CompOp where
  | eq | ne | lt | le | gt | ge
  /-- `IS NOT DISTINCT FROM`. -/
  | syneq
  /-- `IS DISTINCT FROM`. -/
  | synne
  deriving DecidableEq, Repr

/-- Whether the comparison is null-strict, that is, unknown as soon as an
operand is null. All of SQL's comparisons are, except the two syntactic
ones. -/
def CompOp.strict : CompOp → Bool
  | .syneq | .synne => false
  | _ => true

/-- Semantics of a comparison operator over any linearly ordered value
domain (the aggregate values compared by a `HAVING` predicate; the
enumeration algorithms use it at `V = ℕ`). -/
def CompOp.eval {V : Type*} [LinearOrder V] : CompOp → V → V → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b
  | .syneq, a, b => a = b
  | .synne, a, b => a ≠ b

instance {V : Type*} [LinearOrder V] (op : CompOp) (a b : V) : Decidable (op.eval a b) := by
  cases op <;> simp only [CompOp.eval] <;> infer_instance

/-- The complementary comparison operator: `op.negate` holds exactly when
`op` does not. This is how ProvSQL interprets `NOT` over an aggregate
comparison (PostgreSQL's operator negator), with `NOT` pushed through
Boolean combinations by De Morgan duality. -/
def CompOp.negate : CompOp → CompOp
  | .eq => .ne
  | .ne => .eq
  | .lt => .ge
  | .le => .gt
  | .gt => .le
  | .ge => .lt
  | .syneq => .synne
  | .synne => .syneq

/-- `op.negate` evaluates to the classical negation of `op`. -/
theorem CompOp.negate_eval {V : Type*} [LinearOrder V] (op : CompOp) (a b : V) :
    op.negate.eval a b ↔ ¬ op.eval a b := by
  cases op <;> simp only [CompOp.eval, CompOp.negate, ne_eq, not_not,
    not_lt, not_le, ge_iff_le, gt_iff_lt]

/-- Negation preserves strictness: the negator of a null-strict comparison
is null-strict, and the negator of a syntactic one is syntactic. -/
@[simp] theorem CompOp.strict_negate (op : CompOp) :
    op.negate.strict = op.strict := by
  cases op <;> rfl
