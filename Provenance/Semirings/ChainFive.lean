/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Tactic.DeriveFintype
import Provenance.Having

/-!
# A five-element chain m-semiring where `⊗` does not distribute over `⊖`

This file defines `ChainFive`, a commutative m-semiring on the five-element
chain `𝟘 < lo < mid < hi < 𝟙` with `⊕ = max`, the chain monus
(`a ⊖ b = 𝟘` if `a ≤ b`, else `a`), and the commutative multiplication
determined by

* `hi ⊗ hi = hi`,
* `hi ⊗ mid = hi ⊗ lo = lo`,
* every other product of elements strictly between `𝟘` and `𝟙` is `𝟘`.

`ChainFive` is absorptive (hence idempotent) but does **not** satisfy
`mul_sub_left_distributive`: `hi ⊗ (𝟙 ⊖ hi) = hi` while
`hi ⊗ 𝟙 ⊖ hi ⊗ hi = 𝟘`.

## Why this semiring exists

Its purpose is to show that the `mul_sub_left_distributive` hypothesis of
`Having.world_bound` – and hence of `Having.G_eq_S_monus_S` and
`Having.atMost_eq_S_monus_S`, which rest on it – is genuinely needed and
cannot be weakened away as it can for `Having.F_eq_S` (which needs only
absorptivity, via `Having.upward_closed_collapse`).

The witness is the family `α = (mid, hi, hi)` on a three-element universe
`U`, with `W = {0}` and `C = 1`:

* the exactly-`W` annotation is
  `T_U(W) = mid ⊖ (mid⊗hi ⊕ mid⊗hi) = mid ⊖ lo = mid`, but
* `S_1(U) ⊖ S_2(U) = (mid ⊕ hi ⊕ hi) ⊖ (lo ⊕ lo ⊕ hi) = hi ⊖ hi = 𝟘`,

so the bound `T_U(W) ≤ S_1(U) ⊖ S_2(U)` of `Having.world_bound` fails
(`ChainFive.not_world_bound`), and with it the `HAVING count = 1` identity
`G_1(U) = S_1(U) ⊖ S_2(U)` (`ChainFive.G_ne_S_monus_S`) and the
`HAVING count ≤ 1` identity (`ChainFive.atMost_ne_S_monus_S`).

Intuitively, in the factored form `T_U(W) = A_W ⊗ (𝟙 ⊖ E_W)` the failure
disappears: `𝟙 ⊖ E_W = 𝟙 ⊖ hi = 𝟙` and `mid ⊗ 𝟙 = mid`, but the world of
size `2` extending `W` by one `hi`-occurrence has annotation `lo`, which the
chain monus of the *unfactored* form `A_W ⊖ ⊕_x A_{W∪{x}}` fails to cancel
against `mid`. The two forms of the world annotation coincide exactly when
`⊗` distributes over `⊖`; `ChainFive` is where they part company.

All proofs are by `decide`: the carrier is a five-element enumeration with
derived decidable equality and order.
-/

/-- The five-element chain `𝟘 < lo < mid < hi < 𝟙` (constructor order is the
chain order), carrying the m-semiring structure described in the module
docstring. -/
inductive ChainFive
  | zero
  | lo
  | mid
  | hi
  | one
deriving DecidableEq, Repr, Ord, Fintype

namespace ChainFive

instance : LE ChainFive where
  le := fun a b => (compare a b).isLE

instance : LinearOrder ChainFive where
  le_refl := by intro a; cases a <;> decide
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by intro a b; cases a <;> cases b <;> decide
  le_total := by intro a b; cases a <;> cases b <;> decide
  toDecidableLE := inferInstance

instance : Zero ChainFive := ⟨.zero⟩
instance : One ChainFive := ⟨.one⟩

/-- Addition is `max` (the chain join). -/
instance : Add ChainFive := ⟨fun a b => max a b⟩

/-- The commutative multiplication: `𝟙` is neutral, `𝟘` absorbing,
`hi ⊗ hi = hi`, `hi ⊗ mid = hi ⊗ lo = lo`, and all other products of
non-unit elements are `𝟘`. -/
instance : Mul ChainFive :=
  ⟨fun a b => match a, b with
    | .one, x => x
    | x, .one => x
    | .hi, .hi => .hi
    | .hi, .mid => .lo
    | .mid, .hi => .lo
    | .hi, .lo => .lo
    | .lo, .hi => .lo
    | _, _ => .zero⟩

/-- The chain monus: `a ⊖ b = 𝟘` if `a ≤ b`, and `a` otherwise. -/
instance : Sub ChainFive := ⟨fun a b => if a ≤ b then .zero else a⟩

instance : CommSemiring ChainFive where
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_zero := by decide
  nsmul := nsmulRec
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide

instance : SemiringWithMonus ChainFive where
  add_le_add_left := by decide
  exists_add_of_le := by decide
  le_self_add := by decide
  le_add_self := by decide
  monus_spec := by decide
  /- δ is the identity, as in every idempotent m-semiring of the library. -/
  delta := id
  delta_zero := rfl
  delta_natCast_pos := fun hn => delta_natCast_pos_id (by decide) hn
  delta_regrouping := delta_regrouping_id

instance : CommSemiringWithMonus ChainFive where
  mul_comm := by decide

instance : HasAltLinearOrder ChainFive := ⟨inferInstance⟩

end ChainFive

theorem ChainFive.absorptive : absorptive ChainFive := by decide

theorem ChainFive.idempotent : idempotent ChainFive :=
  idempotent_of_absorptive ChainFive.absorptive

/-- `ChainFive` does not satisfy left-distributivity of `⊗` over `⊖`:
`hi ⊗ (𝟙 ⊖ hi) = hi ⊗ 𝟙 = hi`, while `hi ⊗ 𝟙 ⊖ hi ⊗ hi = hi ⊖ hi = 𝟘`. -/
theorem ChainFive.not_mul_sub_left_distributive :
    ¬ mul_sub_left_distributive ChainFive := by decide

namespace ChainFive

/-- The witness family `α = (mid, hi, hi)` on a three-element universe. -/
def alphaCE : Fin 3 → ChainFive := fun i => if i.val = 0 then .mid else .hi

/-- **`Having.world_bound` fails without `mul_sub_left_distributive`.**
In the absorptive m-semiring `ChainFive`, the per-world upper bound
`T_U(W) ≤ S_j(U) ⊖ S_{C+1}(U)` (for `j ≤ |W| ≤ C`) does not hold: with
`α = (mid, hi, hi)`, `W = {0}` and `j = C = 1`, the left-hand side is `mid`
and the right-hand side is `𝟘`. Together with
`ChainFive.not_mul_sub_left_distributive` and `ChainFive.absorptive`, this
shows the distributivity hypothesis of `Having.world_bound` is essential,
in contrast with `Having.F_eq_S` where it can be dropped. -/
theorem not_world_bound :
    ¬ (∀ (α : Fin 3 → ChainFive) (U W : Finset (Fin 3)), W ⊆ U →
        ∀ j C : ℕ, j ≤ W.card → W.card ≤ C →
          Having.T α U W ≤ Having.S α U j - Having.S α U (C + 1)) := by
  intro h
  have := h alphaCE Finset.univ {0} (by decide) 1 1 (by decide) (by decide)
  revert this
  decide

/-- **`Having.G_eq_S_monus_S` fails without `mul_sub_left_distributive`.**
The `HAVING count = 1` identity `G_1(U) = S_1(U) ⊖ S_2(U)` does not hold in
`ChainFive` for `α = (mid, hi, hi)`: the left-hand side is `mid`, the
right-hand side `𝟘`. -/
theorem G_ne_S_monus_S :
    Having.G alphaCE (Finset.univ : Finset (Fin 3)) 1 ≠
      Having.S alphaCE Finset.univ 1 - Having.S alphaCE Finset.univ 2 := by
  decide

/-- **`Having.atMost_eq_S_monus_S` fails without `mul_sub_left_distributive`.**
The `HAVING count ≤ 1` identity does not hold in `ChainFive` for
`α = (mid, hi, hi)`: the left-hand side is `mid`, the right-hand side `𝟘`. -/
theorem atMost_ne_S_monus_S :
    ∑ W ∈ (Finset.univ : Finset (Fin 3)).powerset.filter
        (fun W => 1 ≤ W.card ∧ W.card ≤ 1),
      Having.T alphaCE Finset.univ W ≠
        Having.S alphaCE Finset.univ 1 - Having.S alphaCE Finset.univ 2 := by
  decide

end ChainFive
