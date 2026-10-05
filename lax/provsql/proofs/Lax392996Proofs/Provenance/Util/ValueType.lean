import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs.LinearOrder

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

instance _root_.Lax392996Proofs.Foreign.instToStringSum_provenance [ToString V] [ToString K] : ToString (V⊕K) where
  toString a := match a with
  | Sum.inl a => toString a
  | Sum.inr a => toString a


