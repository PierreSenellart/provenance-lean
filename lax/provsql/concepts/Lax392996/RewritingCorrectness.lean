import Lax392996.SemiringsWithMonus
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra
import Lax392996.MultisetSemantics
import Lax392996.AnnotatedSemantics
import Lax392996.RewritingRules

/-!
---
title: Correctness of the provenance-aware rewriting
type: theorem
---
Let $q$ be a source query, $\mathbb{K}$ an m-semiring with decidable
equality and an alternative linear order, $\hat I$ a $\mathbb{K}$-instance,
and $\hat q$ the query obtained from $q$ by applying the rewriting rules
bottom up. Then $\langle\!\langle q \rangle\!\rangle_{\hat I} = [\![\hat
q]\!]_{\hat I}$: the annotated semantics of $q$ on $\hat I$, read as a plain
relation with the annotation in the last column, is the multiset semantics
of $\hat q$ on the composite reading of $\hat I$. This is the theorem of the
paper for rules (R1) to (R4).
-/

namespace Lax392996.RewritingCorrectness

open Lax392996.SemiringsWithMonus Lax392996.Databases Lax392996.AnnotatedDatabases
open Lax392996.RelationalAlgebra Lax392996.MultisetSemantics Lax392996.AnnotatedSemantics
open Lax392996.RewritingRules

/-- `⟪q⟫_Î = ⟦q̂⟧_Î`, for `q` in the fragment the rules (R1)–(R4) cover. -/
axiom rewriting_valid : ∀ {T : Type} [ValueType T] {K : Type} {n : ℕ}
    [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
    (q : Query T n) (hq : q.source) (d : AnnotatedDatabase T K),
  (Query.evaluateAnnotated q hq d).toComposite
    = Query.evaluate (Query.rewriting q hq) d.toComposite

end Lax392996.RewritingCorrectness
