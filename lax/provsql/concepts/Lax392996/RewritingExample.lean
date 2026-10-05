import Mathlib.Data.Fin.VecNotation
import Lax392996.Databases
import Lax392996.RelationalAlgebra
import Lax392996.RewritingRules
import Lax392996.PersonnelExample

/-!
---
title: The Personnel example, rewritten
type: example
---
The paper's Example 11: the rewriting rules applied bottom up to
$q_{\mathrm{city}}$, for any annotation type $\mathbb{K}$, give
$\gamma_1[\#2 : \oplus](\Pi_{\#4, \#9}(\sigma_{\#4 = \#8 \wedge \#1 < \#5}
(\Pi_{\#1, \dots, \#4, \#6, \dots, \#9, \#5 \otimes \#10}(P \times P))))$,
the cross product rewritten by (R2), the projection by (R1) and the
duplicate elimination by (R3), the selection carried over to the composite
tuples. The claim is that equation, on the queries as syntax; the equality
of its two semantics is an instance of the correctness theorem. Attributes
are numbered from 0 here, from 1 in the paper.
-/

namespace Lax392996.RewritingExample

open Lax392996.Databases Lax392996.RelationalAlgebra Lax392996.RewritingRules
open Lax392996.PersonnelExample

/-- The rewritten query, as the paper traces it. -/
def qcityRewritten (K : Type) : Query (String ⊕ K) 2 :=
  Query.ProvSum (fun k : Fin 1 => k.castLE (by omega)) (Term.index 1)
    (Query.Proj ![Term.index 3, Term.index 8]
      (Query.Sel (Selection.And (Selection.BT (BoolTerm.EQ (Term.index 3) (Term.index 7)))
                                (Selection.BT (BoolTerm.LT (Term.index 0) (Term.index 4))))
        (Query.Proj ![Term.index 0, Term.index 1, Term.index 2, Term.index 3,
                      Term.index 5, Term.index 6, Term.index 7, Term.index 8,
                      Term.mul (Term.index 4) (Term.index 9)]
          (@Query.Prod _ 5 5 10 rfl (Query.Rel 5 "Personnel") (Query.Rel 5 "Personnel")))))

/-- Example 11: the rewriting of `q_city` is the traced query. -/
axiom qcity_rewriting : ∀ (K : Type) (hq : qcity.source),
  Query.rewriting (K := K) qcity hq = qcityRewritten K

end Lax392996.RewritingExample
