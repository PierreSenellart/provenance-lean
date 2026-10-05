/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
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

namespace Lax392996Proofs.Foreign.CompOp
end Lax392996Proofs.Foreign.CompOp

/-!
# Comparison operator for HAVING enumeration algorithms

Shared definition used by `Provenance.Algorithms.CountEnum`,
`Provenance.Algorithms.SumDP` and `Provenance.HavingMinMax`. The operator
parameter is `op ∈ {=, ≠, <, ≤, >, ≥}`.
-/


