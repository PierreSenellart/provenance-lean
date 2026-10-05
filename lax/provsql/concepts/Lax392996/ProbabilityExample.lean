import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra
import Lax392996.ProbabilisticDatabases
import Lax392996.PersonnelExample
import Lax392996.ProvenanceExample

/-!
---
title: The Personnel example, with probabilities
type: example
---
The paper's Example 14: each tuple $t_i$ of the $\mathcal{B}[X]$-instance
$\hat I$ is kept with an independent probability, $\Pr(t_1) = 0.5$ and
$\Pr(t_2) = 0.7$ (the others, unspecified in the paper, are $0.5$ here),
and the probability that Nairobi is in the answer of $q_{\mathrm{city}}$ is
$\Pr(t_1 \wedge t_2) = 0.5 \cdot 0.7 = 0.35$. Variables are numbered from 0
here, from 1 in the paper.
-/

namespace Lax392996.ProbabilityExample

open Lax392996.BooleanFunctions Lax392996.Databases Lax392996.AnnotatedDatabases
open Lax392996.RelationalAlgebra Lax392996.ProbabilisticDatabases
open Lax392996.PersonnelExample Lax392996.ProvenanceExample

/-- The probabilities of the tuples: `0.5`, except `0.7` for the second one. -/
def P : ProbAssignment (Fin 7) where
  prob x := if x = 1 then 7/10 else 1/2
  prob_nonneg := by
    intro x
    split <;> norm_num
  prob_le_one := by
    intro x
    split <;> norm_num

/-- Example 14: the probability that Nairobi is an answer is `0.35`. -/
axiom nairobi_probability :
  ProbAssignment.marginalProb P qcity instanceB !["Nairobi"] = 7/20

end Lax392996.ProbabilityExample
