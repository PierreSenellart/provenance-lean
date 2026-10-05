import Lax392996Proofs.Provenance.SemiringWithMonus
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

namespace Lax392996Proofs.Foreign.BoolFunc
end Lax392996Proofs.Foreign.BoolFunc

/-!
# Boolean-function m-semiring `Bool[X]`

This file defines the semiring `BoolFunc X` of Boolean functions over a set `X` of
Boolean variables. Concretely, `BoolFunc X = (X → Bool) → Bool`: elements are functions
from Boolean assignments to Booleans, with pointwise operations.

Addition is pointwise `||`, multiplication is pointwise `&&`, and the natural order
is `f ≤ g ↔ ∀ a, f a → g a` (pointwise implication).

`BoolFunc X` is absorptive, idempotent, and left-distributive.

This semiring is used in
[Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance] and
surveyed in [Senellart, *Provenance and Probabilities in Relational
Databases*][senellart2017provenance].

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Senellart, *Provenance and Probabilities in Relational Databases*][senellart2017provenance]
-/

instance _root_.Lax392996Proofs.Foreign.instNontrivialBoolFunc : Nontrivial (Lax392996.BooleanFunctions.BoolFunc X) := ⟨0, 1, by
  intro h
  have : (0 : Lax392996.BooleanFunctions.BoolFunc X) (fun _ => false) = (1 : Lax392996.BooleanFunctions.BoolFunc X) (fun _ => false) := by rw [h]
  exact Bool.false_ne_true this⟩

/-! ## Universal property obstructions

The variable functions `BoolFunc.var i` satisfy two algebraic identities in
`BoolFunc X` that constrain the target of any semiring homomorphism:

* `1 + var i = 1` (`BoolFunc.absorptive`)
* `var i * var i = var i` (multiplicative idempotence)

If the target `K` is **not** absorptive (there exists `a : K` with
`1 + a ≠ 1`), assigning that `a` to any variable makes a semiring
homomorphism `BoolFunc X →+* K` impossible. Similarly if `K`'s multiplication
is not idempotent. -/


