import Lax392996.SemiringsWithMonus
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra
import Lax392996.MultisetSemantics
import Lax392996.RewritingRules
import Lax392996.ProbabilisticDatabases

/-!
---
title: Probabilistic query evaluation by the rewritten query
type: theorem
---
For a probability assignment $P$ on a finite set $X$ of variables, a
$\mathcal{B}[X]$-instance $\hat I$, a source query $q$ and a tuple $t$,
if $\hat q$ is the query rewritten from $q$ by the rules (R1) to (R4), then
$\Pr(t \in q(\hat I)) = \Pr\big(\bigvee_{(t, \alpha) \in [\![\hat q]\!]_{\hat I}}
\alpha\big)$: the marginal probability of $t$ is the probability of its
annotation in the plain evaluation of $\hat q$ on the composite reading of
$\hat I$, each answer tuple read back as an annotated one. This is the
paper's Corollary 13, combining the correctness of the rewriting with the
theorem on probabilistic evaluation; as for the former, the paper states it
with the aggregation rule (R5) included, which this submission does not
cover.
-/

namespace Lax392996.ProbabilisticEvaluationByRewriting

open Lax392996.SemiringsWithMonus Lax392996.BooleanFunctions Lax392996.Databases
open Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra Lax392996.MultisetSemantics
open Lax392996.RewritingRules Lax392996.ProbabilisticDatabases

/-- **Corollary 13.** The marginal probability of a tuple is the probability
of its annotation in the answer of the rewritten query. -/
axiom corollary_13 : ∀ {X : Type} [Fintype X] [DecidableEq X] {T : Type} [ValueType T]
    (P : ProbAssignment X) [HasAltLinearOrder (BoolFunc X)] {n : ℕ} (q : Query T n) (hq : q.source)
    (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n),
  ProbAssignment.marginalProb P q Î t
    = ProbAssignment.funcProb P (tupleAnnotation
        (Multiset.map Tuple.fromComposite (Query.evaluate (Query.rewriting q hq) Î.toComposite)) t)

end Lax392996.ProbabilisticEvaluationByRewriting
