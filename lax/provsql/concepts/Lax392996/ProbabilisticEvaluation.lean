import Lax392996.SemiringsWithMonus
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra
import Lax392996.MultisetSemantics
import Lax392996.AnnotatedSemantics
import Lax392996.ProbabilisticDatabases

/-!
---
title: Probabilistic query evaluation through provenance
type: theorem
---
For a probability assignment $P$ on a finite set $X$ of variables, a source
query $q$, a $\mathcal{B}[X]$-instance $\hat I$ and a tuple $t$, the
marginal probability that $t$ appears in the answer of $q$ on a random
world of $\hat I$ equals the probability of the annotation of $t$ in the
annotated answer $\langle\!\langle q \rangle\!\rangle_{\hat I}$: $\Pr(t \in
q(\hat I)) = \Pr\big(\bigvee_{(t, \alpha) \in \langle\!\langle q
\rangle\!\rangle_{\hat I}} \alpha\big)$. This is the paper's Theorem 12,
the justification of intensional probabilistic query evaluation: evaluate
the query once over Boolean-function annotations and take the probability
of the resulting function.
-/

namespace Lax392996.ProbabilisticEvaluation

open Lax392996.SemiringsWithMonus Lax392996.BooleanFunctions Lax392996.Databases
open Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra Lax392996.MultisetSemantics
open Lax392996.AnnotatedSemantics Lax392996.ProbabilisticDatabases

/-- **Theorem 12.** The marginal probability of a tuple is the probability
of its disjunctive annotation in the annotated answer. -/
axiom theorem_12 : ∀ {X : Type} [Fintype X] [DecidableEq X] {T : Type} [ValueType T]
    (P : ProbAssignment X) {n : ℕ} (q : Query T n) (hq : q.source)
    (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n),
  ProbAssignment.marginalProb P q Î t
    = ProbAssignment.funcProb P (tupleAnnotation (Query.evaluateAnnotated q hq Î) t)

end Lax392996.ProbabilisticEvaluation
