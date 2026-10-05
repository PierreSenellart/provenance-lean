import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Prod.Lex
import Lax392996.SemiringsWithMonus
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra
import Lax392996.AnnotatedSemantics
import Lax392996.ProbabilisticDatabases
import Lax392996.PersonnelExample

/-!
---
title: The Personnel example, annotated
type: example
---
The $\mathcal{B}[X]$-instance $\hat I$ of the paper's Example 9, for
$X = \{t_1, \dots, t_7\}$: the tuple with id $i$ of $\mathit{Personnel}$
annotated by the variable $t_i$. The annotated answer
$\langle\!\langle q_{\mathrm{city}} \rangle\!\rangle_{\hat I}$ has the three
cities as data parts, and their annotations are the Boolean functions
$t_1 \wedge t_2$ for Nairobi, $(t_3 \wedge t_5) \vee (t_5 \wedge t_6) \vee
(t_3 \wedge t_6)$ for Paris and $t_4 \wedge t_7$ for Beijing, the claims
being stated pointwise on the valuations of $X$. Variables are numbered
from 0 here, from 1 in the paper.
-/

namespace Lax392996.ProvenanceExample

open Lax392996.SemiringsWithMonus Lax392996.BooleanFunctions Lax392996.Databases
open Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra Lax392996.AnnotatedSemantics
open Lax392996.ProbabilisticDatabases Lax392996.PersonnelExample

/-- The variable `t_i`, as the Boolean function reading it off a valuation. -/
def t (i : Fin 7) : BoolFunc (Fin 7) := fun ν => ν i

/-- `Personnel` annotated: the tuple with id `i` carries `t_i`. -/
def personnelB : AnnotatedRelation String (BoolFunc (Fin 7)) 4 := Multiset.ofList [
  toLex (!["1", "Juma", "Director", "Nairobi"], t 0),
  toLex (!["2", "Paul", "Janitor", "Nairobi"], t 1),
  toLex (!["3", "David", "Analyst", "Paris"], t 2),
  toLex (!["4", "Ellen", "Field agent", "Beijing"], t 3),
  toLex (!["5", "Aaheli", "Double agent", "Paris"], t 4),
  toLex (!["6", "Nancy", "HR", "Paris"], t 5),
  toLex (!["7", "Jing", "Analyst", "Beijing"], t 6)]

/-- The `B[X]`-instance `Î`. -/
def instanceB : AnnotatedDatabase String (BoolFunc (Fin 7)) := [("Personnel", ⟨4, personnelB⟩)]

/-- Example 9, the data: the annotated answer has the three cities as data parts. -/
axiom data_answer : ∀ hq : qcity.source,
  Multiset.map Prod.fst (Query.evaluateAnnotated qcity hq instanceB)
    = Multiset.ofList [!["Nairobi"], !["Paris"], !["Beijing"]]

/-- Example 9, Nairobi: annotated by `t_1 ∧ t_2`. -/
axiom nairobi_annotation : ∀ (hq : qcity.source) (ν : Fin 7 → Bool),
  tupleAnnotation (Query.evaluateAnnotated qcity hq instanceB) !["Nairobi"] ν = (ν 0 && ν 1)

/-- Example 9, Paris: annotated by `(t_3 ∧ t_5) ∨ (t_5 ∧ t_6) ∨ (t_3 ∧ t_6)`. -/
axiom paris_annotation : ∀ (hq : qcity.source) (ν : Fin 7 → Bool),
  tupleAnnotation (Query.evaluateAnnotated qcity hq instanceB) !["Paris"] ν
    = ((ν 2 && ν 4) || (ν 4 && ν 5) || (ν 2 && ν 5))

/-- Example 9, Beijing: annotated by `t_4 ∧ t_7`. -/
axiom beijing_annotation : ∀ (hq : qcity.source) (ν : Fin 7 → Bool),
  tupleAnnotation (Query.evaluateAnnotated qcity hq instanceB) !["Beijing"] ν = (ν 3 && ν 6)

end Lax392996.ProvenanceExample
