/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Lax392996.AnnotatedDatabases
import Lax392996.AnnotatedSemantics
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.MultisetSemantics
import Lax392996.ProbabilisticDatabases
import Lax392996.RelationalAlgebra
import Lax392996.RewritingRules
import Lax392996.SemiringsWithMonus
import Lax392996.WhyProvenance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace Lax392996Proofs.Foreign
end Lax392996Proofs.Foreign

/-!
# Semirings with monus

This file defines semirings with monus and introduces their main
properties.

Many semirings relevant for provenance can be equipped with a monus -
operator, resulting in what is called a semiring with monus, or
m-semiring. This is standard in semiring theory [amer1984equationally] and was
introduced in the setting of provenance semirings by Geerts and Poggi
[geerts2010database]. The class is the algebraic structure underlying the
annotated query semantics of Section IV-A of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql] (Definition 5).

## References

* [Amer, *Equationally complete classes of commutative monoids with
monus*][amer1984equationally]
* [Geerts & Poggi, *On database query languages for
K-relations*][geerts2010database]
* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Definition 5)

-/

section SemiringWithMonus

/-! ## Definition of a `SemiringWithMonus` -/

/-! ## Main properties -/

/-- In a `SemiringWithMonus`, `a - b` is the smallest element `c`
satisfying `a ≤ b + c`. -/
theorem _root_.Lax392996Proofs.Foreign.monus_smallest [K : Lax392996.SemiringsWithMonus.SemiringWithMonus α] :
  ∀ a b : α, a ≤ b + (a - b) ∧ ∀ c: α, a ≤ b + c → a - b ≤ c := by {
    intro a b
    constructor
    . rw [← Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
    . intro c h
      rw [Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
      exact h
  }

export Lax392996Proofs.Foreign (monus_smallest)

/-- In a `SemiringWithMonus`, `a - a = 0`. -/
theorem _root_.Lax392996Proofs.Foreign.monus_self [K : Lax392996.SemiringsWithMonus.SemiringWithMonus α] :
  ∀ a : α, a - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
      simp
    . simp
  }

export Lax392996Proofs.Foreign (monus_self)

/-- In a `SemiringWithMonus`, `0 - a = 0`. -/
theorem _root_.Lax392996Proofs.Foreign.zero_monus [K : Lax392996.SemiringsWithMonus.SemiringWithMonus α] :
  ∀ a : α, 0 - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
      simp
    . simp
  }

export Lax392996Proofs.Foreign (zero_monus)

/-- In a `SemiringWithMonus`, `a + (b -a) = b + (a - b)`. -/
theorem _root_.Lax392996Proofs.Foreign.add_monus [K : Lax392996.SemiringsWithMonus.SemiringWithMonus α] :
  ∀ a b : α, a + (b - a) = b + (a - b) := by
    intro a b

    have h : ∀ a b c : α, (a ≤ c ∧ b ≤ c) → a+(b-a) ≤ c := by
      intro a b c hc
      rcases hc with ⟨ha, hb⟩
      rcases (exists_add_of_le ha) with ⟨d, ha'⟩
      rw [ha'] at hb
      rw [← Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec] at hb
      apply add_le_add_left at hb
      specialize hb a
      rw[add_comm]
      simp [ha']
      nth_rewrite 2 [add_comm]
      assumption

    apply le_antisymm

    . apply h a b (b+(a-b))
      constructor
      . simp [← Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
      . simp

    . apply h b a (a+(b-a))
      constructor
      . simp [← Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
      . simp

export Lax392996Proofs.Foreign (add_monus)

/-- In a `SemiringWithMonus`, monus is left-distributive over plus. -/
theorem _root_.Lax392996Proofs.Foreign.monus_add [K: Lax392996.SemiringsWithMonus.SemiringWithMonus α] :
  ∀ a b c : α, a - (b + c) = a - b - c := by {
    intro a b c

    have h1 : ∀ x : α, (a ≤ b+c+x) → a - (b+c) ≤ x := by {
      intro x
      apply ((Lax392996Proofs.Foreign.monus_smallest a (b+c)).right x)
    }

    have h2 : ∀ x : α, (a ≤ b+c+x) → a - b - c ≤ x := by {
      intro x hx
      rw [Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
      rw [Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
      rw [← add_assoc]
      exact hx
    }

    apply le_antisymm
    . apply h1
      calc
        a ≤ b + (a-b)       := by rw [← Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec a b (a-b)]
        _ ≤ b + c + (a-b-c) := by {
          rw [add_assoc]
          apply add_le_add_right
          rw [← Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec (a-b) c (a-b-c)]
        }

    . apply h2
      rw [← Lax392996.SemiringsWithMonus.SemiringWithMonus.monus_spec]
  }

export Lax392996Proofs.Foreign (monus_add)

/-! ## Additional properties

The following properties do not always hold in an arbitrary m-semiring.
-/

/-- A `Semiring` is idempotent if `a + a = a`. -/
abbrev _root_.Lax392996Proofs.Foreign.idempotent (α) [Semiring α] := ∀ a : α, a + a = a

export Lax392996Proofs.Foreign (idempotent)

/-- A `Semiring` is absorptive (also called 0-closed or 0-bounded) if `1 + a = 1`. -/
abbrev _root_.Lax392996Proofs.Foreign.absorptive (α) [Semiring α] := ∀ a : α, 1 + a = 1

export Lax392996Proofs.Foreign (absorptive)

/-- Absorptivity implies idempotence -/
theorem _root_.Lax392996Proofs.Foreign.idempotent_of_absorptive [K: Semiring α] :
  Lax392996Proofs.Foreign.absorptive α → Lax392996Proofs.Foreign.idempotent α := by
    intro habs a
    nth_rewrite 1 2 [← mul_one a]
    rw[← mul_add]
    simp[habs 1]

export Lax392996Proofs.Foreign (idempotent_of_absorptive)

/-! ## Exclusivity

`exclusive` says `a ⊗ (𝟙 ⊖ a) = 𝟘`. The possible-world arguments consume a
two-argument form, `a ⊗ (𝟙 ⊖ (a ⊕ b)) = 𝟘`: an occurrence present in one
world and absent from another contributes `a` to the first world's annotation
and `𝟙 ⊖ (a ⊕ b)` to the second's. The two forms are equivalent, so the
one-argument form is what a semiring is checked against and the two-argument
form is what the proofs use. -/

/-! ### Exclusivity against absorptivity

An absorptive m-semiring has `𝟙` at the top of its natural order, so `𝟙 ⊖ a`
is the least element joining with `a` to `𝟙` – the least relative complement.
Exclusivity then asks that least complement to be orthogonal to `a`, which a
chain cannot deliver: there the join of two elements is one of them, so the
only complement of a non-`𝟙` element is `𝟙` itself. -/

/-! ## Characteristic of idempotent semirings

In an idempotent semiring (`a + a = a`), every positive natural-number cast
collapses to `1`. With `1 ≠ 0` this yields `CharP K 0`. Note that this is
strictly weaker than `CharZero K`, which fails for idempotent semirings since
the cast `ℕ → K` is not injective. -/

/-- In a semiring with idempotent addition, the cast of any positive natural
number equals `1`. -/
theorem _root_.Lax392996Proofs.Foreign.natCast_pos_eq_one_of_idempotent {K : Type} [Semiring K] (h : Lax392996Proofs.Foreign.idempotent K) :
  ∀ {n : ℕ}, 0 < n → (n : K) = 1 := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      match Nat.eq_zero_or_pos m with
      | .inl hm => subst hm; simp
      | .inr hm => rw [Nat.cast_succ, ih hm, h 1]

export Lax392996Proofs.Foreign (natCast_pos_eq_one_of_idempotent)

/-! ## Generic constructions of `δ`

In the m-semirings used for provenance the `δ` operator is invariably
realized in one of two ways: as the identity (when the semiring is
idempotent, so every positive natural cast already equals `1`) or as the
indicator-of-nonzero (`a ↦ if a = 0 then 0 else 1`). The lemmas below
package the proofs of the `δ` axioms for both candidates so each
concrete instance can plug them in directly. -/

/-- `δ := id` satisfies `delta_natCast_pos` in any idempotent semiring:
every positive natural-number cast collapses to `1`. -/
theorem _root_.Lax392996Proofs.Foreign.delta_natCast_pos_id {K : Type} [Semiring K] (h : Lax392996Proofs.Foreign.idempotent K)
    {n : ℕ} (hn : 0 < n) : (id ((n : K)) : K) = 1 :=
  Lax392996Proofs.Foreign.natCast_pos_eq_one_of_idempotent h hn

export Lax392996Proofs.Foreign (delta_natCast_pos_id)

/-! ## Admissibility of a candidate `δ`

`δ` is not determined by the axioms, and the two operators used in practice
are the identity and the support indicator. `IsDelta` states the axioms as a
predicate on a *candidate* operator, so that a semiring can record which of
the two it must use: the identity is preferred where it is admissible, and
the indicator is forced exactly where `¬ IsDelta id` holds. The three
`not_isDelta_id_of_*` lemmas below cover the three ways the identity fails,
in increasing order of subtlety. -/

/-! ## Existence of a `δ`-like operator

This is the abstract counterpart of the `SemiringWithMonus` δ-axioms: we
characterize, in an arbitrary nontrivial semiring (no order assumed), when
a function `δ : K → K` satisfying `δ 0 = 0` and `δ ((n : K)) = 1` for
`0 < n` can exist. The class also demands `delta_absorb`, which the iff
below ignores, so it should be read as a statement about how much of the
ProvSQL δ interface is consistent with a given characteristic, not as a
full existence proof for the class. (Constructing a witness for
`delta_absorb` requires more structure: in a canonically ordered semiring
the indicator works, see `delta_absorb_indicator`.) -/

/-! ## Commutative `SemiringWithMonus`s

`SemiringWithMonus` is intentionally not assumed to be commutative; however, every
provenance semiring used in this library is in fact commutative, and the algebraic
identities that drive HAVING-style aggregate provenance (see `Provenance.Having`)
require it. `CommSemiringWithMonus` packages a `SemiringWithMonus` together with
the commutativity axiom, producing a `CommMonoid` instance whose `Mul` matches
the one already supplied by `SemiringWithMonus`, so no `Mul` diamond appears when
`Finset.prod` is used.
-/

/-! ## Homomorphisms of `SemiringWithMonus`s
-/

/-! ## Miscellaneous
-/

end SemiringWithMonus


