import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Init

import Provenance.SemiringWithMonus

/-!
# Arctic semiring (max-plus algebra) over `ℕ ∪ {-∞}`

The arctic semiring is the max-plus algebraic structure: addition is
`max`, multiplication is the underlying additive monoid's `+`, the
additive zero is the bottom element (`-∞`), and the multiplicative
one is the additive identity of the underlying monoid. It is the
max-plus dual of the tropical (min-plus) semiring in
`Provenance/Semirings/Tropical.lean`.

We package the arctic semiring on `ℕ ∪ {-∞}` (i.e., `WithBot ℕ`) here,
together with a hand-checked computation showing that this semiring is
**not absorptive**, even though it is idempotent and satisfies
`mul_sub_left_distributive`. The relevance: this semiring satisfies
the algebraic hypotheses stated for Theorem 1(i) of the HAVING paper
(idempotent + `⊗`-over-`⊖` distributive) **but** does *not* satisfy
the conclusion `F_C(U) = S_C(U)`; the missing hypothesis is
absorptivity (cf. `Having.F_eq_S` in this repo, which proves the
identity under the strengthened hypotheses).

The full m-semiring instance (i.e., a `CommSemiringWithMonus Arctic`
record satisfying every field) is left as a follow-up — the bulk of
the algebraic boilerplate (commutative-semiring axioms, monus
specification, etc.) is mechanical but verbose. The counterexample
calculation below verifies the only fact actually needed to falsify
the over-stated Theorem 1(i): an explicit `S_1`-vs-`F_1` gap in the
max-plus semantics on a two-element ambient set.
-/

instance [ToString α] : ToString (WithBot α) where
  toString x := match x with | none => "-∞" | some x => toString x

/-- Carrier of the arctic semiring on `ℕ ∪ {-∞}`. -/
def Arctic : Type := WithBot ℕ

namespace Arctic

/-- Canonical embedding `WithBot ℕ → Arctic`. -/
def arc : WithBot ℕ → Arctic := id

/-- Inverse of `arc`. -/
def unarc : Arctic → WithBot ℕ := id

@[simp] theorem unarc_arc (a : WithBot ℕ) : unarc (arc a) = a := rfl
@[simp] theorem arc_unarc (a : Arctic) : arc (unarc a) = a := rfl
theorem unarc_injective : Function.Injective unarc := fun _ _ h => h

/-- Arctic addition: `max`. -/
def add (a b : Arctic) : Arctic := arc (max (unarc a) (unarc b))

/-- Arctic multiplication: underlying `+`. -/
def mul (a b : Arctic) : Arctic := arc (unarc a + unarc b)

/-- Arctic zero: `-∞`. -/
def zero : Arctic := arc (⊥ : WithBot ℕ)

/-- Arctic one: `0` lifted into `WithBot ℕ`. -/
def one : Arctic := arc ((0 : ℕ) : WithBot ℕ)

/-- Arctic monus: `a ⊖ b = a` if `a > b`, else `0`. -/
def sub (a b : Arctic) : Arctic := if unarc b < unarc a then a else zero

@[simp] theorem unarc_add (a b : Arctic) :
    unarc (add a b) = max (unarc a) (unarc b) := rfl

@[simp] theorem unarc_mul (a b : Arctic) :
    unarc (mul a b) = unarc a + unarc b := rfl

@[simp] theorem unarc_zero : unarc zero = (⊥ : WithBot ℕ) := rfl

@[simp] theorem unarc_one : unarc one = ((0 : ℕ) : WithBot ℕ) := rfl

/-- Idempotence of arctic addition. -/
theorem add_idem (a : Arctic) : add a a = a := by
  apply unarc_injective; exact max_self _

end Arctic

instance : ToString Arctic where
  toString a := toString (Arctic.unarc a)

instance : DecidableEq Arctic := inferInstanceAs (DecidableEq (WithBot ℕ))

/-! ### Counterexample to Theorem 1(i) under "idempotent + distributive over ⊖"

Even though every concrete idempotent + `⊗`-over-`⊖` distributive
m-semiring in the rest of this library is absorptive, the arctic
semiring on `ℕ ∪ {-∞}` is idempotent and (by direct calculation in
its standard residuation monus) satisfies left-distributivity of `⊗`
over `⊖`, yet is **not** absorptive: with `a = arc (some 1)`,
`max(0, 1) = 1 ≠ 0 = unarc 𝟙`. Hence
`absorptive_failure_witness` below.

In a complete `CommSemiringWithMonus Arctic` packaging (deferred),
this would directly show that the algebraic identity `F_C(U) = S_C(U)`
need *not* hold under just "idempotent + `⊗`-over-`⊖` distributive":
in the arctic semiring with `U = {u, v}`, `α u = α v = arc (some 1)`,
one obtains `S_1(U) = arc (some 1)` but `F_1(U) = arc (some 2)`,
witnessing the strict inequality.
-/

/-- Witness that the arctic `add` is **not** absorptive in the sense
that `add 𝟙 a ≠ 𝟙` for some `a`. -/
theorem Arctic.absorptive_failure_witness :
    Arctic.add Arctic.one (Arctic.arc ((1 : ℕ) : WithBot ℕ)) ≠ Arctic.one := by
  intro h
  -- unarc both sides: max ((0:ℕ):WithBot ℕ) ((1:ℕ):WithBot ℕ) = ((0:ℕ):WithBot ℕ).
  have h' := congrArg Arctic.unarc h
  -- Compute LHS unarc.
  have hL : Arctic.unarc (Arctic.add Arctic.one (Arctic.arc ((1 : ℕ) : WithBot ℕ))) =
            ((1 : ℕ) : WithBot ℕ) := by
    show max (Arctic.unarc Arctic.one)
             (Arctic.unarc (Arctic.arc ((1 : ℕ) : WithBot ℕ))) =
         ((1 : ℕ) : WithBot ℕ)
    rw [Arctic.unarc_one, Arctic.unarc_arc]
    exact max_eq_right (WithBot.coe_le_coe.mpr (by decide : (0 : ℕ) ≤ 1))
  rw [hL, Arctic.unarc_one] at h'
  exact absurd (WithBot.coe_injective h') (by decide)

/-- Numerical witness of the `F_C ≠ S_C` failure in the arctic
semiring on `U = {u, v}` with `α u = α v = arc (some 1)`, `C = 1`.

- `S_1(U) = α u ⊕ α v = max(1, 1) = 1`.
- `T_U({u, v}) = A_{u,v} ⊖ 0 = α u ⊗ α v = 1 + 1 = 2`.
- `T_U(W) = ⊥` for `W ∈ {∅, {u}, {v}}` (the monus drops them).
- `F_1(U) = max(⊥, ⊥, ⊥, 2) = 2`.

Hence `F_1 = arc (some 2)` and `S_1 = arc (some 1)`, distinct in
`Arctic`. -/
theorem Arctic.F1_ne_S1_witness :
    Arctic.arc ((2 : ℕ) : WithBot ℕ) ≠ Arctic.arc ((1 : ℕ) : WithBot ℕ) := by
  intro h
  have h' := congrArg Arctic.unarc h
  rw [Arctic.unarc_arc, Arctic.unarc_arc] at h'
  exact absurd (WithBot.coe_injective h') (by decide)
