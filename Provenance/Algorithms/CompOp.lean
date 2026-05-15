/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Init

/-!
# Comparison operator for HAVING enumeration algorithms

Shared definition used by both `Provenance.Algorithms.CountEnum` and
`Provenance.Algorithms.SumDP`. Matches the operator parameter
`op ∈ {=, ≠, <, ≤, >, ≥}` of the algorithms in the HAVING / ProvSQL
paper.
-/

/-- Comparison operator on natural numbers, as used by the HAVING
enumeration algorithms. -/
inductive CompOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Semantics of a comparison operator on natural numbers. -/
def CompOp.eval : CompOp → ℕ → ℕ → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

instance (op : CompOp) (a b : ℕ) : Decidable (op.eval a b) := by
  cases op <;> simp [CompOp.eval] <;> infer_instance
