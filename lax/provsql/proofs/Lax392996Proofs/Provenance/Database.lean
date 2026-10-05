import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind

import Lax392996Proofs.Provenance.Util.ValueType
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

namespace Lax392996.Databases.Relation
end Lax392996.Databases.Relation

namespace Lax392996.Databases.Tuple
end Lax392996.Databases.Tuple

namespace Lax392996Proofs.Foreign.Relation
end Lax392996Proofs.Foreign.Relation

namespace Lax392996Proofs.Foreign.Tuple
end Lax392996Proofs.Foreign.Tuple

/-!
# Tuples, relations, and databases

This file defines the basic relational model used throughout the library.

## Main definitions

* `Tuple T n` – a tuple of arity `n` over value type `T`, represented as a function
  `Fin n → T`
* `Relation T n` – a multiset of tuples of arity `n`
* `Database T` – a mapping from relation names (strings) to relations of the
  corresponding arities
-/

variable {T: Type} [Lax392996.Databases.ValueType T]

namespace Lax392996.Databases.Tuple

open Lax392996Proofs.Foreign.Tuple in
def _root_.Lax392996Proofs.Foreign.Tuple.cast (heq : n=m) (t: Lax392996.Databases.Tuple T n): Lax392996.Databases.Tuple T m := by
  subst heq
  exact t

end Lax392996.Databases.Tuple

namespace Lax392996.Databases.Tuple

export Lax392996Proofs.Foreign.Tuple (cast)

end Lax392996.Databases.Tuple

namespace Tuple
export Lax392996Proofs.Foreign.Tuple (cast)
end Tuple

namespace Lax392996.Databases.Tuple

open Lax392996Proofs.Foreign.Tuple in
theorem _root_.Lax392996Proofs.Foreign.Tuple.apply_cast {T: Type} (heq: n=m) (f: Lax392996.Databases.Tuple T m → α) (t: Lax392996.Databases.Tuple T n) :
  f (t.cast heq) = (@_root_.cast (Lax392996.Databases.Tuple T m → α) (Lax392996.Databases.Tuple T n → α) (by simp[heq]) f) t := by
  subst heq
  rfl

end Lax392996.Databases.Tuple

namespace Lax392996.Databases.Tuple

export Lax392996Proofs.Foreign.Tuple (apply_cast)

end Lax392996.Databases.Tuple

namespace Tuple
export Lax392996Proofs.Foreign.Tuple (apply_cast)
end Tuple

namespace Lax392996.Databases.Tuple

open Lax392996Proofs.Foreign.Tuple in
theorem _root_.Lax392996Proofs.Foreign.Tuple.cast_get {T: Type} (heq: n=m) (t: Lax392996.Databases.Tuple T n) (k: Fin m) :
  t.cast heq k = t (k.cast (Eq.symm heq)) := by
    subst heq
    rfl

end Lax392996.Databases.Tuple

namespace Lax392996.Databases.Tuple

export Lax392996Proofs.Foreign.Tuple (cast_get)

end Lax392996.Databases.Tuple

namespace Tuple
export Lax392996Proofs.Foreign.Tuple (cast_get)
end Tuple

instance _root_.Lax392996Proofs.Foreign.instZeroTuple : Zero (Lax392996.Databases.Tuple T n) := ⟨λ _ ↦ 0⟩

instance _root_.Lax392996Proofs.Foreign.instToStringTuple [ToString T] : ToString (Lax392996.Databases.Tuple T n) where
  toString t :=
    "(" ++ String.intercalate ", " (List.ofFn (fun i => toString (t i))) ++ ")"

namespace Lax392996.Databases.Relation

open Lax392996Proofs.Foreign.Relation in
theorem _root_.Lax392996Proofs.Foreign.Relation.cast_eq {S: Type} (r: Lax392996.Databases.Relation S n) (s: Lax392996.Databases.Relation S m) (heq: n=m) :
  s = r.cast heq ↔ s = r.map (λ t ↦ t.cast heq)
  := by
    simp[Lax392996.Databases.Relation.cast, Lax392996Proofs.Foreign.Tuple.cast]
    subst heq
    simp

end Lax392996.Databases.Relation

namespace Lax392996.Databases.Relation

export Lax392996Proofs.Foreign.Relation (cast_eq)

end Lax392996.Databases.Relation

namespace Relation
export Lax392996Proofs.Foreign.Relation (cast_eq)
end Relation

instance _root_.Lax392996Proofs.Foreign.instSubRelation : Sub (Lax392996.Databases.Relation T arity) := inferInstanceAs (Sub (Multiset (Lax392996.Databases.Tuple T arity)))

instance _root_.Lax392996Proofs.Foreign.instZeroRelation : Zero (Lax392996.Databases.Relation T n) where zero := (∅: Multiset (Lax392996.Databases.Tuple T n))

instance _root_.Lax392996Proofs.Foreign.instZeroSigmaNatRelation : Zero ((n : ℕ) × Lax392996.Databases.Relation T n) where zero := ⟨0,(∅: Multiset (Lax392996.Databases.Tuple T 0))⟩


