import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Defs.LinearOrder

/-!
---
title: Semirings with monus
type: definition
---
A semiring with monus, or m-semiring, is a semiring $(\mathbb{K}, \oplus,
\otimes, \mathbb{0}, \mathbb{1})$ with a further binary operation $\ominus$.
Here it is axiomatized through the natural order of a canonically ordered
semiring, $a \le b$ when $b = a \oplus c$ for some $c$, by the Galois
connection $a \ominus b \le c \iff a \le b \oplus c$; the three equations of
the paper's definition, $a \oplus (b \ominus a) = b \oplus (a \ominus b)$,
$(a \ominus b) \ominus c = a \ominus (b \oplus c)$ and $a \ominus a = \mathbb{0}
\ominus a = \mathbb{0}$, follow and are the claims of this module. The class
also carries the duplicate-eliminating operator $\delta$ of Amsterdamer,
Deutch and Tannen (2011), with $\delta(\mathbb{0}) = \mathbb{0}$,
$\delta(\mathbb{1} \oplus \dots \oplus \mathbb{1}) = \mathbb{1}$ and $a
\otimes \delta(a \oplus b) = a$, which the paper's rewriting of aggregation
uses. An alternative linear order on an annotation type is bundled
separately: it is what makes a type of annotations usable as a value type
once data and annotations share a column.
-/

universe u

namespace Lax392996.SemiringsWithMonus

/-- A `SemiringWithMonus` is a naturally ordered semiring
with a monus operation that is compatible with the natural order.
The semiring is not required to be commutative.

In addition to monus, the class carries a `δ : α → α` operator subject
to three axioms (`delta_zero`, `delta_natCast_pos`, and
`delta_absorb`). This is the duplicate-eliminating support
operator used to interpret aggregation in the framework of
[Amsterdamer, Deutch & Tannen, *Provenance for aggregate queries*][amsterdamer2011aggregate]. -/
class SemiringWithMonus (α : Type)
  extends Semiring α, PartialOrder α, IsOrderedAddMonoid α, CanonicallyOrderedAdd α, Sub α where
  monus_spec : ∀ a b c : α, a - b ≤ c ↔ a ≤ b + c
  /-- Duplicate-eliminating support operator. Sends `0` to `0` and any
  positive integer iterate of `1` to `1`. -/
  delta : α → α
  /-- `δ` sends `0` to `0`. -/
  delta_zero : delta 0 = 0
  /-- `δ` sends every positive integer iterate of `1` (i.e., every
  positive natural-number cast) to `1`. -/
  delta_natCast_pos : ∀ {n : ℕ}, 0 < n → delta ((n : α)) = 1
  /-- A δ-guard is absorbed by any multiple of one of its summands:
  `a ⊗ δ(a ⊕ b) = a`. This is what makes a group-existence factor
  redundant next to any provenance that already contains an occurrence
  of the group: `δ` acts as “the group exists” and nothing more. -/
  delta_absorb : ∀ (a b : α), a * delta (a + b) = a

/-- An alternative linear order on a type, used to order annotations when
they share a column with data values. -/
class HasAltLinearOrder (α : Type u) where
  altOrder : LinearOrder α

/-- The paper's m-semiring axiom (i): `a ⊕ (b ⊖ a) = b ⊕ (a ⊖ b)`. -/
axiom msemiring_axiom_i : ∀ {K : Type} [SemiringWithMonus K] (a b : K),
  a + (b - a) = b + (a - b)

/-- The paper's m-semiring axiom (ii): `(a ⊖ b) ⊖ c = a ⊖ (b ⊕ c)`. -/
axiom msemiring_axiom_ii : ∀ {K : Type} [SemiringWithMonus K] (a b c : K),
  ((a - b) - c) = (a - (b + c))

/-- The paper's m-semiring axiom (iii): `a ⊖ a = 𝟘 ⊖ a = 𝟘`. -/
axiom msemiring_axiom_iii : ∀ {K : Type} [SemiringWithMonus K] (a : K),
  ((a - a) = 0) ∧ (((0 : K) - a) = 0)

/-- The paper's δ-semiring axiom (i): `δ(𝟘) = 𝟘`. -/
axiom delta_axiom_i : ∀ {K : Type} [SemiringWithMonus K],
  SemiringWithMonus.delta (0 : K) = 0

/-- The paper's δ-semiring axiom (ii): `δ(𝟙 ⊕ ⋯ ⊕ 𝟙) = 𝟙`, whatever the
positive number of `𝟙`s. -/
axiom delta_axiom_ii : ∀ {K : Type} [SemiringWithMonus K] {j : ℕ}, 0 < j →
  SemiringWithMonus.delta ((j : K)) = 1

end Lax392996.SemiringsWithMonus
