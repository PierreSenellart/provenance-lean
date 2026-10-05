import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.String.Basic
import Mathlib.Data.Multiset.Basic
import Lax392996.Databases
import Lax392996.RelationalAlgebra
import Lax392996.MultisetSemantics

/-!
---
title: The Personnel example
type: example
---
The running example of the paper: the relation $\mathit{Personnel}$ of
arity 4 with seven tuples, giving an id, a name, a position and a city
(1, Juma, Director, Nairobi; 2, Paul, Janitor, Nairobi; 3, David, Analyst,
Paris; 4, Ellen, Field agent, Beijing; 5, Aaheli, Double agent, Paris;
6, Nancy, HR, Paris; 7, Jing, Analyst, Beijing), the database $I$ holding
it, and the query asking for the cities where at least two persons work,
$q_{\mathrm{city}} = \varepsilon(\Pi_{\#4}(\mathit{Personnel}
\bowtie_{\#4 = \#8 \wedge \#1 < \#5} \mathit{Personnel}))$, the join being
a selection over a cross product. Values are strings, ordered as strings;
the claim is Example 2, $[\![q_{\mathrm{city}}]\!]_I = \{\!|(\mathrm{Nairobi}),
(\mathrm{Paris}), (\mathrm{Beijing})|\!\}$.
-/

namespace Lax392996.PersonnelExample

open Lax392996.Databases Lax392996.RelationalAlgebra Lax392996.MultisetSemantics

/-- Strings as values, ordered as strings; the arithmetic of terms, which
the example does not use, is trivial on them. -/
instance instValueTypeString : ValueType String where
  zero := ""
  add _ _ := ""
  sub _ _ := ""
  mul _ _ := ""
  add_comm _ _ := rfl
  add_assoc _ _ _ := rfl

/-- The relation `Personnel` of the paper's Table 1: id, name, position, city. -/
def personnel : Relation String 4 := Multiset.ofList [
  !["1", "Juma", "Director", "Nairobi"],
  !["2", "Paul", "Janitor", "Nairobi"],
  !["3", "David", "Analyst", "Paris"],
  !["4", "Ellen", "Field agent", "Beijing"],
  !["5", "Aaheli", "Double agent", "Paris"],
  !["6", "Nancy", "HR", "Paris"],
  !["7", "Jing", "Analyst", "Beijing"]]

/-- The database `I`, with its one relation. -/
def instanceI : Database String := [("Personnel", ⟨4, personnel⟩)]

/-- The query `q_city`: the cities where at least two persons work, as
duplicate elimination of a projection of a selection over the cross
product of `Personnel` with itself. Attributes are numbered from 0 here,
from 1 in the paper. -/
def qcity : Query String 1 :=
  Query.Dedup (Query.Proj ![Term.index 3]
    (Query.Sel (Selection.And (Selection.BT (BoolTerm.EQ (Term.index 3) (Term.index 7)))
                              (Selection.BT (BoolTerm.LT (Term.index 0) (Term.index 4))))
      (@Query.Prod _ 4 4 8 rfl (Query.Rel 4 "Personnel") (Query.Rel 4 "Personnel"))))

/-- Example 2: the answer of `q_city` on `I`. -/
axiom qcity_answer :
  Query.evaluate qcity instanceI = Multiset.ofList [!["Nairobi"], !["Paris"], !["Beijing"]]

end Lax392996.PersonnelExample
