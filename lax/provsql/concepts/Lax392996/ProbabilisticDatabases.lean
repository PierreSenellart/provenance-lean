import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Rat.Defs
import Lax392996.SemiringsWithMonus
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.AnnotatedDatabases
import Lax392996.RelationalAlgebra
import Lax392996.MultisetSemantics

/-!
---
title: Probabilistic databases and marginal probabilities
type: definition
---
A probability assignment on a finite set $X$ of Boolean variables gives each
variable a rational probability in $[0, 1]$, the variables being
independent: a valuation $\nu : X \to \{\bot, \top\}$ has probability
$\Pr(\nu) = \prod_{\nu(x) = \top} \Pr(x) \cdot \prod_{\nu(x) = \bot} (1 -
\Pr(x))$, and a Boolean function $f$ has probability $\Pr(f) = \sum_{\nu
\models f} \Pr(\nu)$. A $\mathcal{B}[X]$-instance $\hat I$ is a
probabilistic database: its random world under $\nu$ is the plain database
of the tuples whose annotation holds at $\nu$. The marginal probability of
a tuple $t$ in the answer of a query $q$ is $\sum_\nu \Pr(\nu) \cdot
[t \in [\![q]\!]_{\hat I(\nu)}]$, and the annotation of $t$ in an
annotated relation is the disjunction $\bigvee_{(t, \alpha)} \alpha$ of
the annotations of its copies.
-/

namespace Lax392996.ProbabilisticDatabases

open Lax392996.SemiringsWithMonus Lax392996.BooleanFunctions Lax392996.Databases
open Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra Lax392996.MultisetSemantics

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A probability assignment to a finite set `X` of Boolean variables: each
variable is assigned a rational probability in `[0, 1]`. -/
structure ProbAssignment (X : Type) where
  /-- The probability assigned to each variable. -/
  prob : X → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities are at most `1`. -/
  prob_le_one : ∀ x, prob x ≤ 1

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Probability of a single valuation `v : X → Bool`, under the independence
assumption: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`. -/
def valProb (v : X → Bool) : ℚ :=
  ∏ x, if v x then P.prob x else 1 - P.prob x

/-- Probability of a Boolean function: `Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : BoolFunc X) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0

end ProbAssignment

/-- Membership of a tuple in a relation, that of multisets. -/
instance instMembershipRelation {T : Type} {n : ℕ} :
    Membership (Tuple T n) (Relation T n) := by
  show Membership (Tuple T n) (Multiset (Tuple T n))
  infer_instance

/-- Decidability of membership of a tuple in a relation. -/
instance instDecidableMemRelation {T : Type} [ValueType T] {n : ℕ}
    (t : Tuple T n) (r : Relation T n) : Decidable (t ∈ r) :=
  Multiset.decidableMem t r

variable {T : Type} [ValueType T]

/-- The disjunctive tuple annotation `tupleAnnotation r t = ⋁_{(t,α) ∈ r} α`:
the OR over the annotations of all annotated tuples in `r` whose data part
equals `t`. -/
def tupleAnnotation {n : ℕ} (r : AnnotatedRelation T (BoolFunc X) n) (t : Tuple T n) :
    BoolFunc X :=
  (Multiset.map Prod.snd
    (@Multiset.filter _ (fun p : AnnotatedTuple T (BoolFunc X) n => p.fst = t)
      (fun p => instDecidableEqTuple p.fst t) r)).sum

/-- The random world of a `BoolFunc X`-annotated relation under a valuation
`v`: the plain relation consisting of the data parts of the annotated tuples
whose annotation evaluates to `true` at `v`. -/
def randomWorld {n : ℕ} (v : X → Bool) (r : AnnotatedRelation T (BoolFunc X) n) :
    Multiset (Tuple T n) :=
  Multiset.map Prod.fst
    (@Multiset.filter _ (fun p : AnnotatedTuple T (BoolFunc X) n => p.snd v = true)
      (fun p => instDecidableEqBool (p.snd v) true) r)

/-- The random world of a `BoolFunc X`-annotated database: each annotated
relation is replaced by its random world. -/
def AnnotatedDatabase.randomWorld
    (v : X → Bool) (Î : AnnotatedDatabase T (BoolFunc X)) : Database T :=
  Î.map (fun e => (e.fst, ⟨e.snd.fst, Lax392996.ProbabilisticDatabases.randomWorld v e.snd.snd⟩))

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Marginal probability that the tuple `t` appears in the output of `q`
when evaluated on a random world of `Î`. -/
noncomputable def marginalProb {n : ℕ}
    (q : Query T n) (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) : ℚ :=
  ∑ v : X → Bool,
    if t ∈ Query.evaluate q (AnnotatedDatabase.randomWorld v Î) then P.valProb v else 0

end ProbAssignment

end Lax392996.ProbabilisticDatabases
