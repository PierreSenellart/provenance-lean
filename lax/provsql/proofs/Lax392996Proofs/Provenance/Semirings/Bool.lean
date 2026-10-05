import Lax392996Proofs.Provenance.SemiringWithMonus
import Lax392996Proofs.Provenance.Semirings.BoolFunc
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

/-!
# Boolean m-semiring

This file shows that `Bool` (with `||` as addition and `&&` as multiplication) is a
commutative m-semiring. It is the simplest m-semiring and serves as the target of the
natural homomorphism from `BoolFunc X`.

The semiring is absorptive (`true || a = true`), idempotent, and satisfies
left-distributivity of multiplication over monus.
-/

section Bool

open Bool

instance _root_.Lax392996Proofs.Foreign.instZeroBool_provenance : Zero (Bool) := ⟨false⟩

instance _root_.Lax392996Proofs.Foreign.instAddBool_provenance : Add  (Bool) := ⟨or⟩

instance _root_.Lax392996Proofs.Foreign.instOneBool_provenance : One  (Bool) := ⟨true⟩

instance _root_.Lax392996Proofs.Foreign.instMulBool_provenance : Mul  (Bool) := ⟨and⟩

instance _root_.Lax392996Proofs.Foreign.instSubBool_provenance : Sub  (Bool) := ⟨(· && !·)⟩

instance _root_.Lax392996Proofs.Foreign.instCommSemiringBool_provenance : CommSemiring Bool where
  add_assoc := or_assoc
  add_comm := or_comm
  zero_add := false_or
  add_zero := or_false
  mul_assoc := and_assoc
  one_mul := true_and
  mul_one := and_true
  left_distrib := and_or_distrib_left
  right_distrib := and_or_distrib_right
  zero_mul := false_and
  mul_zero := and_false
  mul_comm := and_comm
  nsmul := nsmulRec

/-- The Boolean semiring (`Bool`, `||`, `&&`) is an m-semiring. The natural order is
the usual Boolean order (`false ≤ true`), and the monus is `a && !b`. The δ operator
matches ProvSQL's `Boolean::delta`: it is the identity. -/
instance _root_.Lax392996Proofs.Foreign.instSemiringWithMonusBool : Lax392996.SemiringsWithMonus.SemiringWithMonus Bool where
  le_self_add := by decide
  le_add_self := by decide
  add_le_add_left := by decide
  exists_add_of_le := by decide
  monus_spec := by decide
  delta := id
  delta_zero := rfl
  delta_natCast_pos := fun hn => Lax392996Proofs.Foreign.delta_natCast_pos_id (by decide) hn
  delta_absorb := by decide

end Bool


