import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Nat
import Lax392996.SemiringsWithMonus

/-!
---
title: The counting semiring is an m-semiring
type: definition
---
The counting semiring $(\mathbb{N}, +, \times, 0, 1)$ is an m-semiring: its
natural order is the usual order on natural numbers, its monus is truncated
subtraction, and its operator $\delta$ is the support indicator, $0$ on $0$
and $1$ elsewhere. Unlike most provenance semirings it is neither idempotent
nor absorptive. Its usual order also serves as the alternative linear order
that lets counts share a column with data values.
-/

namespace Lax392996.CountingSemiring

open Lax392996.SemiringsWithMonus

/-- The support indicator: `0 ↦ 0`, positive `↦ 1`. -/
def Nat.deltaInd (n : ℕ) : ℕ := if n = 0 then 0 else 1

/-- `ℕ` is an m-semiring: the natural order is the usual one, the monus is
truncated subtraction, and `δ` is the support indicator. -/
instance instSemiringWithMonusNat : SemiringWithMonus ℕ where
  monus_spec := by
    intro a b c
    omega
  delta := Nat.deltaInd
  delta_zero := rfl
  delta_natCast_pos := by
    intro n hn
    simp [Nat.deltaInd, Nat.pos_iff_ne_zero.mp hn]
  delta_absorb := by
    intro a b
    by_cases ha : a = 0
    · simp [ha, Nat.deltaInd]
    · simp [Nat.deltaInd, ha]

instance instHasAltLinearOrderNat : HasAltLinearOrder ℕ where
  altOrder := inferInstance

end Lax392996.CountingSemiring
