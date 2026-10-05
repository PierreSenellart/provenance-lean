import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

import Lax392996Proofs.Provenance.QueryAnnotatedDatabase
import Lax392996Proofs.Provenance.QueryRewriting
import Lax392996Proofs.Provenance.QueryRewriting
import Lax392996Proofs.Provenance.Semirings.Bool
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

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase
end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.AnnotatedSemantics.Selection
end Lax392996.AnnotatedSemantics.Selection

namespace Lax392996.MultisetSemantics.Query
end Lax392996.MultisetSemantics.Query

namespace Lax392996.ProbabilisticDatabases.AnnotatedDatabase
end Lax392996.ProbabilisticDatabases.AnnotatedDatabase

namespace Lax392996.ProbabilisticDatabases.ProbAssignment
end Lax392996.ProbabilisticDatabases.ProbAssignment

namespace Lax392996.RewritingRules.Query
end Lax392996.RewritingRules.Query

namespace Lax392996Proofs.Foreign
end Lax392996Proofs.Foreign

namespace Lax392996Proofs.Foreign.AnnotatedDatabase
end Lax392996Proofs.Foreign.AnnotatedDatabase

namespace Lax392996Proofs.Foreign.ProbAssignment
end Lax392996Proofs.Foreign.ProbAssignment

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase
export Lax392996.ProbabilisticDatabases.AnnotatedDatabase (randomWorld)
end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.RelationalAlgebra.Query
export Lax392996.MultisetSemantics.Query (evaluate)
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Query
export Lax392996.RewritingRules.Query (rewriting)
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Selection
export Lax392996.AnnotatedSemantics.Selection (evalDecidableAnnotated)
end Lax392996.RelationalAlgebra.Selection

/-!
# Probability distributions over Boolean variables

This file defines the intensional probability semantics underlying ProvSQL's
probabilistic query evaluation, following Section IV-D of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of
the Provenance and Probability of Data*][sen2026provsql].

Given a finite set `X` of Boolean variables and an assignment `Pr : X → ℚ`
of probabilities (with values in `[0, 1]`), we extend `Pr` to:

* a probability distribution over valuations `v : X → Bool`, assuming the
  variables are independent: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`;
* a probability of a Boolean function `f : BoolFunc X`, defined as the sum of
  `Pr(v)` over satisfying valuations: `Pr(f) = ∑_{v ⊨ f} Pr(v)`.

This is the foundation for Theorem 12 of the paper (intensional
probabilistic query evaluation correctness), proved below as
`ProbAssignment.theorem_12`: for any non-aggregation query `q`, any
`BoolFunc X`-instance `Î` and any tuple `t`,
`Pr(t ∈ q(Î)) = Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`. Its structural core is
`randomWorld_evaluateAnnotated`, the commutation of annotated evaluation
with random-world projection, which doubles as the adequacy theorem of the
annotated semantics for the full non-aggregation fragment (difference and
duplicate elimination included); see the section
“The structural commutation theorem” below for how this relates to the
`ℕ`-adequacy theorem of [benzaken2021coq].

## Main definitions

* `ProbAssignment X` – a probability assignment to each variable, bundled
  with `0 ≤ Pr(x) ≤ 1`.
* `ProbAssignment.valProb` – `Pr(v)` for a single valuation `v : X → Bool`.
* `ProbAssignment.funcProb` – `Pr(f)` for a Boolean function `f : BoolFunc X`.

## Main results

* `ProbAssignment.valProb_nonneg`, `valProb_le_one`, `sum_valProb_eq_one` –
  basic properties of the valuation distribution.
* `ProbAssignment.funcProb_zero`, `funcProb_one`, `funcProb_nonneg`,
  `funcProb_le_one` – basic properties of `Pr(f)`.
* `ProbAssignment.funcProb_congr` – pointwise-equal Boolean functions have
  equal probabilities.
* `randomWorld_evaluateAnnotated` – annotated evaluation commutes with
  random-world projection (adequacy of the `BoolFunc X`-annotated semantics).
* `ProbAssignment.theorem_12`, `corollary_13` – correctness of intensional
  probabilistic query evaluation, on the annotated and on the plain rewritten
  query respectively.

## References

* [Sen, Maniu & Senellart][sen2026provsql] (Section IV-D)
* [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini][benzaken2021coq]
-/

variable {X : Type} [Fintype X] [DecidableEq X]

namespace ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

end ProbAssignment

/-- Membership in `AnnotatedRelation` (a `def`-wrapped `Multiset`). -/
instance _root_.Lax392996Proofs.Foreign.instMembershipAnnotatedRelation {T K : Type} {n : ℕ} :
    Membership (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) (Lax392996.AnnotatedDatabases.AnnotatedRelation T K n) :=
  inferInstanceAs (Membership (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n) (Multiset (Lax392996.AnnotatedDatabases.AnnotatedTuple T K n)))

export Lax392996Proofs.Foreign (instMembershipAnnotatedRelation)

/-! ## Random worlds and the disjunctive tuple annotation

We now move toward Theorem 12 of the paper. Two pieces of infrastructure are
needed: the **random world** of a `BoolFunc X`-annotated relation under a
valuation `v : X → Bool` (the plain relation containing exactly the data
parts of the annotated tuples whose annotation evaluates to `true` at `v`),
and the **disjunctive tuple annotation** `⋁_{(t,α) ∈ r} α` (a single Boolean
function summarizing all the ways `t` can appear in `r`). -/

variable {T : Type} [Lax392996.Databases.ValueType T]

/-! ### Pointwise meaning of `tupleAnnotation`

`(tupleAnnotation r t)(v) = true` iff some annotated tuple `(t, α) ∈ r` has
`α(v) = true`. This is the connection between the disjunction-on-the-right
of Theorem 12 and the random-world picture on the left. -/

omit [Fintype X] [DecidableEq X] in
/-- `Multiset.sum` of a multiset of `BoolFunc X` evaluated at `v` equals the
sum (in `Bool`) of the pointwise evaluations: this just pushes evaluation at
`v` through the additive monoid hom. -/
lemma _root_.Lax392996Proofs.Foreign.boolFunc_multiset_sum_apply
    (s : Multiset (Lax392996.BooleanFunctions.BoolFunc X)) (v : X → Bool) :
    s.sum v = (s.map (fun f => f v)).sum := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons f t ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih]
    rfl

export Lax392996Proofs.Foreign (boolFunc_multiset_sum_apply)

/-- A multiset sum in `Bool` (where `+` is OR) equals `true` iff some element
of the multiset is `true`. -/
lemma _root_.Lax392996Proofs.Foreign.bool_multiset_sum_eq_true (s : Multiset Bool) :
    s.sum = true ↔ ∃ b ∈ s, b = true := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    rw [Multiset.sum_cons]
    show (b + t.sum) = true ↔ ∃ b' ∈ b ::ₘ t, b' = true
    constructor
    · intro h
      have : b = true ∨ t.sum = true := by
        have hb : (b + t.sum) = (b || t.sum) := rfl
        rw [hb, Bool.or_eq_true] at h
        exact h
      rcases this with hb | ht
      · exact ⟨b, Multiset.mem_cons_self _ _, hb⟩
      · obtain ⟨b', hb', heq⟩ := ih.mp ht
        exact ⟨b', Multiset.mem_cons_of_mem hb', heq⟩
    · rintro ⟨b', hb', heq⟩
      rcases Multiset.mem_cons.mp hb' with rfl | hb''
      · show (b' || t.sum) = true
        rw [heq]; rfl
      · have : t.sum = true := ih.mpr ⟨b', hb'', heq⟩
        show (b || t.sum) = true
        rw [this]; simp

export Lax392996Proofs.Foreign (bool_multiset_sum_eq_true)

omit [Fintype X] [DecidableEq X] in
/-- **Pointwise reading of `tupleAnnotation`.** `(tupleAnnotation r t)(v) = true`
exactly when the random world at `v` of `r` contains `t`. -/
theorem _root_.Lax392996Proofs.Foreign.tupleAnnotation_apply_eq_true_iff
    (r : Lax392996.AnnotatedDatabases.AnnotatedRelation T (Lax392996.BooleanFunctions.BoolFunc X) n) (t : Lax392996.Databases.Tuple T n) (v : X → Bool) :
    (Lax392996.ProbabilisticDatabases.tupleAnnotation r t) v = true ↔ t ∈ Lax392996.ProbabilisticDatabases.randomWorld v r := by
  unfold Lax392996.ProbabilisticDatabases.tupleAnnotation Lax392996.ProbabilisticDatabases.randomWorld
  rw [Lax392996Proofs.Foreign.boolFunc_multiset_sum_apply, Lax392996Proofs.Foreign.bool_multiset_sum_eq_true]
  constructor
  · rintro ⟨b, hb_mem, hb_true⟩
    -- b ∈ map (fun f => f v) (map snd (filter (·.fst = t) r)) and b = true
    rw [Multiset.mem_map] at hb_mem
    obtain ⟨α, hα_mem, hα_eq⟩ := hb_mem
    rw [Multiset.mem_map] at hα_mem
    obtain ⟨p, hp_mem, hp_snd⟩ := hα_mem
    rw [Multiset.mem_filter] at hp_mem
    -- hp_mem : p ∈ r ∧ p.fst = t
    -- Goal: t ∈ map fst (filter (·.snd v = true) r)
    rw [Multiset.mem_map]
    refine ⟨p, ?_, hp_mem.2⟩
    rw [Multiset.mem_filter]
    refine ⟨hp_mem.1, ?_⟩
    -- Need p.snd v = true. We have hp_snd : p.snd = α, hα_eq : α v = b, hb_true : b = true.
    rw [hp_snd, hα_eq, hb_true]
  · rintro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨p, hp_mem, hp_fst⟩ := hmem
    rw [Multiset.mem_filter] at hp_mem
    -- hp_mem : p ∈ r ∧ p.snd v = true
    refine ⟨p.snd v, ?_, hp_mem.2⟩
    rw [Multiset.mem_map]
    refine ⟨p.snd, ?_, rfl⟩
    rw [Multiset.mem_map]
    refine ⟨p, ?_, rfl⟩
    rw [Multiset.mem_filter]
    exact ⟨hp_mem.1, hp_fst⟩

export Lax392996Proofs.Foreign (tupleAnnotation_apply_eq_true_iff)

/-! ## Marginal probability and the statement of Theorem 12

The marginal probability `Pr(t ∈ q(Î))` is defined as the sum over valuations
`v` of `Pr(v)` indexed by whether `t` appears in `q.evaluate (Î.randomWorld v)`.
This is the standard “intensional” definition: enumerate possible worlds,
weight each by its probability, and accumulate the indicator that the query
output contains `t`.

The paper writes the same thing as `∑_J [t ∈ ⟦q⟧(J)] · Pr(J)` over
sub-instances `J ⊆ Î`. The two sums agree because, for each valuation `v`,
the unique `J` whose characteristic Boolean function `Φ_J(Î)` is satisfied at
`v` is exactly `J(v) = { (u, α) ∈ Î | α(v) = true }`, whose data side is
`Î.randomWorld v`. -/

namespace ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

end ProbAssignment

/-! ### Random worlds commute with annotated query evaluation

The structural heart of Theorem 12 is the following commutation: for any
non-aggregation query `q`, taking the random world of the annotated query
result gives the same multiset as evaluating `q` on the plain random-world
database.

```
  randomWorld v (evaluateAnnotated q Î)  =  q.evaluate (Î.randomWorld v)
```

Once this holds, Theorem 12 follows by summing `Pr(v)` weighted by the
matching indicators over `v`, using `tupleAnnotation_apply_eq_true_iff` on
the right-hand side and the definition of `marginalProb` on the left. -/

attribute [instance] Lax392996.RelationalAlgebra.Selection.evalDecidable Lax392996.AnnotatedSemantics.Selection.evalDecidableAnnotated

/-! ### Helper lemmas: random-world commutes with Multiset operations -/

omit [Fintype X] [DecidableEq X] [Lax392996.Databases.ValueType T] in
@[simp] lemma _root_.Lax392996Proofs.Foreign.randomWorld_zero (v : X → Bool) :
    Lax392996.ProbabilisticDatabases.randomWorld v (0 : Lax392996.AnnotatedDatabases.AnnotatedRelation T (Lax392996.BooleanFunctions.BoolFunc X) n) = 0 := rfl

export Lax392996Proofs.Foreign (randomWorld_zero)

omit [Fintype X] [DecidableEq X] [Lax392996.Databases.ValueType T] in
/-- `randomWorld` is additive on relations: filtering and projecting the
data side commutes with multiset sum. -/
lemma _root_.Lax392996Proofs.Foreign.randomWorld_add (v : X → Bool)
    (r₁ r₂ : Lax392996.AnnotatedDatabases.AnnotatedRelation T (Lax392996.BooleanFunctions.BoolFunc X) n) :
    Lax392996.ProbabilisticDatabases.randomWorld v (r₁ + r₂) = Lax392996.ProbabilisticDatabases.randomWorld v r₁ + Lax392996.ProbabilisticDatabases.randomWorld v r₂ := by
  unfold Lax392996.ProbabilisticDatabases.randomWorld
  exact (congr_arg (Multiset.map Prod.fst)
          (Multiset.filter_add (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n => p.snd v = true)
            r₁ r₂)).trans
    (Multiset.map_add _ _ _)

export Lax392996Proofs.Foreign (randomWorld_add)

omit [Fintype X] [DecidableEq X] [Lax392996.Databases.ValueType T] in
/-- Filtering the data side commutes with `randomWorld v`. -/
lemma _root_.Lax392996Proofs.Foreign.randomWorld_filter_data (v : X → Bool)
    (φ : Lax392996.Databases.Tuple T n → Prop) [DecidablePred φ]
    (r : Lax392996.AnnotatedDatabases.AnnotatedRelation T (Lax392996.BooleanFunctions.BoolFunc X) n) :
    Multiset.filter φ (Lax392996.ProbabilisticDatabases.randomWorld v r) =
      Lax392996.ProbabilisticDatabases.randomWorld v (Multiset.filter (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => φ p.fst) r) := by
  let r' : Multiset (Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X) := r
  show Multiset.filter φ
        (Multiset.map Prod.fst
          (Multiset.filter (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r'))
      = Multiset.map Prod.fst
          (Multiset.filter (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true)
            (Multiset.filter (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => φ p.fst) r'))
  induction r' using Multiset.induction_on with
  | empty => rfl
  | cons q s ih =>
    by_cases hq : q.snd v = true
    · by_cases hφ : φ q.fst
      · -- both filters pos
        rw [Multiset.filter_cons_of_pos
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s hq,
            Multiset.map_cons,
            Multiset.filter_cons_of_pos (p := φ) _ hφ,
            Multiset.filter_cons_of_pos
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => φ p.fst) s hφ,
            Multiset.filter_cons_of_pos
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ hq,
            Multiset.map_cons, ih]
      · -- snd-filter pos, fst-filter neg
        rw [Multiset.filter_cons_of_pos
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s hq,
            Multiset.map_cons,
            Multiset.filter_cons_of_neg (p := φ) _ hφ,
            Multiset.filter_cons_of_neg
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => φ p.fst) s hφ, ih]
    · by_cases hφ : φ q.fst
      · -- snd-filter neg, fst-filter pos
        rw [Multiset.filter_cons_of_neg
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s hq,
            Multiset.filter_cons_of_pos
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => φ p.fst) s hφ,
            Multiset.filter_cons_of_neg
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ hq, ih]
      · rw [Multiset.filter_cons_of_neg
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s hq,
            Multiset.filter_cons_of_neg
              (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => φ p.fst) s hφ, ih]

export Lax392996Proofs.Foreign (randomWorld_filter_data)

omit [Fintype X] [DecidableEq X] [Lax392996.Databases.ValueType T] in
/-- Mapping the data side commutes with `randomWorld v`. Proved by
`Multiset.induction_on`, with all `Multiset.filter` / `Multiset.map` lemmas
called with named `(p := ...)` / explicit-type arguments so Lean's HOU does
not pick a wrong decomposition and so the underlying `Lex`-unfolded carrier
type matches between goal and rewrite. -/
lemma _root_.Lax392996Proofs.Foreign.randomWorld_map_data (v : X → Bool) (f : Lax392996.Databases.Tuple T n → Lax392996.Databases.Tuple T m)
    (r : Lax392996.AnnotatedDatabases.AnnotatedRelation T (Lax392996.BooleanFunctions.BoolFunc X) n) :
    Multiset.map f (Lax392996.ProbabilisticDatabases.randomWorld v r) =
      Lax392996.ProbabilisticDatabases.randomWorld v (r.map (fun p : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n => (f p.fst, p.snd))) := by
  -- Work with the underlying plain-`Prod` carrier so that all subterms agree
  -- on the syntactic representation of the tuple type.
  let r' : Multiset (Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X) := r
  show Multiset.map f
        (Multiset.map Prod.fst
          (Multiset.filter (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r'))
      = Multiset.map Prod.fst
          (Multiset.filter (fun p : Lax392996.Databases.Tuple T m × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true)
            (Multiset.map (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => (f p.fst, p.snd)) r'))
  induction r' using Multiset.induction_on with
  | empty => rfl
  | cons q s ih =>
    by_cases hq : q.snd v = true
    · have hq' : (f q.fst, q.snd).snd v = true := hq
      rw [Multiset.map_cons (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => (f p.fst, p.snd)) q s,
          Multiset.filter_cons_of_pos
            (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s hq,
          Multiset.filter_cons_of_pos
            (p := fun p : Lax392996.Databases.Tuple T m × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ hq',
          Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, ih]
    · have hq' : ¬ (f q.fst, q.snd).snd v = true := hq
      rw [Multiset.map_cons (fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => (f p.fst, p.snd)) q s,
          Multiset.filter_cons_of_neg
            (p := fun p : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s hq,
          Multiset.filter_cons_of_neg
            (p := fun p : Lax392996.Databases.Tuple T m × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ hq', ih]

export Lax392996Proofs.Foreign (randomWorld_map_data)

/-! ### Random world commutes with `find` -/

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase

open Lax392996Proofs.Foreign.AnnotatedDatabase in
omit [Fintype X] [DecidableEq X] [Lax392996.Databases.ValueType T] in
lemma _root_.Lax392996Proofs.Foreign.AnnotatedDatabase.find_randomWorld
    (n : ℕ) (s : String) (Î : Lax392996.AnnotatedDatabases.AnnotatedDatabase T (Lax392996.BooleanFunctions.BoolFunc X)) (v : X → Bool) :
    (Î.randomWorld v).find n s = (Î.find n s).map (Lax392996.ProbabilisticDatabases.randomWorld v) := by
  induction Î with
  | nil => rfl
  | cons hd tl ih =>
    unfold Lax392996.ProbabilisticDatabases.AnnotatedDatabase.randomWorld Lax392996.AnnotatedDatabases.AnnotatedDatabase.find Lax392996.AnnotatedDatabases.AnnotatedDatabase.find.f
            Lax392996.Databases.Database.find Lax392996.Databases.Database.find.f
    by_cases hcond : n = hd.snd.fst ∧ s = hd.fst
    · simp [hcond]
      have := hcond.left; subst this
      rfl
    · simp [hcond]
      unfold Lax392996.ProbabilisticDatabases.AnnotatedDatabase.randomWorld Lax392996.AnnotatedDatabases.AnnotatedDatabase.find at ih
      exact ih

end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase

export Lax392996Proofs.Foreign.AnnotatedDatabase (find_randomWorld)

end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace AnnotatedDatabase
export Lax392996Proofs.Foreign.AnnotatedDatabase (find_randomWorld)
end AnnotatedDatabase

/-! ### Diff annotation helper

For the `Diff` case of the structural commutation theorem we need to
characterize when the annotation subtracted from `r₁`'s entries evaluates to
`false` at the valuation `v`: this happens exactly when the data tuple is
not in the random world of `r₂`. -/

omit [Fintype X] [DecidableEq X] in
/-- The `Diff` subtraction-annotation evaluates to `false` at `v` iff the
data tuple is absent from the random world of the subtracted relation. -/
lemma _root_.Lax392996Proofs.Foreign.diff_annotation_eq_false_iff
    (v : X → Bool) (r₂ : Lax392996.AnnotatedDatabases.AnnotatedRelation T (Lax392996.BooleanFunctions.BoolFunc X) n) (u : Lax392996.Databases.Tuple T n) :
    ((((Lax392996Proofs.Foreign.groupByKey r₂).val.find?
        (fun q : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => q.1 = u)).map Prod.snd).getD 0 : Lax392996.BooleanFunctions.BoolFunc X) v = false
      ↔ u ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂ := by
  -- Bridge: u ∉ rw v r₂ iff no annotated tuple p ∈ r₂ with p.fst = u has p.snd v = true.
  have hnotin_iff : u ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂
      ↔ ∀ p : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n, p ∈ r₂
          → ¬ (p.fst = u ∧ p.snd v = true) := by
    unfold Lax392996.ProbabilisticDatabases.randomWorld
    constructor
    · intro h p hp ⟨hfst, hsnd⟩
      apply h
      rw [Multiset.mem_map]
      refine ⟨p, ?_, hfst⟩
      rw [Multiset.mem_filter]
      exact ⟨hp, hsnd⟩
    · intro h hmem
      rw [Multiset.mem_map] at hmem
      obtain ⟨p, hp, hpfst⟩ := hmem
      rw [Multiset.mem_filter] at hp
      exact h p hp.1 ⟨hpfst, hp.2⟩
  cases h_find : (Lax392996Proofs.Foreign.groupByKey r₂).val.find?
        (fun q : Lax392996.Databases.Tuple T n × Lax392996.BooleanFunctions.BoolFunc X => q.1 = u) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [show (0 : Lax392996.BooleanFunctions.BoolFunc X) v = false from rfl]
    rw [hnotin_iff]
    rw [List.find?_eq_none] at h_find
    refine ⟨?_, ?_⟩
    · intro _ p hp ⟨hfst, _⟩
      have hu_mem : u ∈ Multiset.map Prod.fst r₂ := by
        rw [Multiset.mem_map]; exact ⟨p, hp, hfst⟩
      obtain ⟨w, hw⟩ := (Lax392996Proofs.Foreign.groupByKey_key_iff r₂ u).mpr hu_mem
      exact h_find _ hw (by simp)
    · intro _; rfl
  | some uw =>
    obtain ⟨u', w⟩ := uw
    have hu' : u' = u := by
      have := List.find?_some h_find; simp at this; exact this
    -- Substitute the find?-returned key with u everywhere.
    rw [hu'] at h_find
    have hw_in : (u, w) ∈ (Lax392996Proofs.Foreign.groupByKey r₂).val := List.mem_of_find?_eq_some h_find
    have hw_val : w = (Multiset.map Prod.snd
          (Multiset.filter (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n ↦ q.fst = u) r₂)).sum :=
      Lax392996Proofs.Foreign.groupByKey_value r₂ u w hw_in
    show (((Option.map Prod.snd _).getD 0) : Lax392996.BooleanFunctions.BoolFunc X) v = false ↔ u ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂
    rw [hu', Option.map_some, Option.getD_some]
    -- The `(u, ...).2` projects to the sum; reduce, then apply
    -- `boolFunc_multiset_sum_apply`.
    show w v = false ↔ u ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂
    rw [hw_val, Lax392996Proofs.Foreign.boolFunc_multiset_sum_apply, hnotin_iff]
    refine ⟨?_, ?_⟩
    · intro hw_v p hp ⟨hfst, hsnd⟩
      have htrue_in : true ∈ Multiset.map (fun f : Lax392996.BooleanFunctions.BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n => q.fst = u) r₂)) := by
        rw [Multiset.mem_map]
        refine ⟨p.snd, ?_, hsnd⟩
        rw [Multiset.mem_map]
        refine ⟨p, ?_, rfl⟩
        rw [Multiset.mem_filter]; exact ⟨hp, hfst⟩
      have hsum : (Multiset.map (fun f : Lax392996.BooleanFunctions.BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n => q.fst = u) r₂))).sum = true := by
        rw [Lax392996Proofs.Foreign.bool_multiset_sum_eq_true]
        exact ⟨true, htrue_in, rfl⟩
      rw [hsum] at hw_v
      exact Bool.false_ne_true hw_v.symm
    · intro hall
      have hall_false : ∀ b ∈ Multiset.map (fun f : Lax392996.BooleanFunctions.BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n => q.fst = u) r₂)),
          b = false := by
        intro b hb
        rw [Multiset.mem_map] at hb
        obtain ⟨α, hα_in, hα_eq⟩ := hb
        rw [Multiset.mem_map] at hα_in
        obtain ⟨p, hp_in, hp_snd⟩ := hα_in
        rw [Multiset.mem_filter] at hp_in
        obtain ⟨hp_r, hp_fst⟩ := hp_in
        rw [← hα_eq, ← hp_snd]
        cases h : p.snd v
        · rfl
        · exfalso; exact hall p hp_r ⟨hp_fst, h⟩
      have hne_true : (Multiset.map (fun f : Lax392996.BooleanFunctions.BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n => q.fst = u) r₂))).sum ≠ true := by
        intro h
        rw [Lax392996Proofs.Foreign.bool_multiset_sum_eq_true] at h
        obtain ⟨b, hb_in, hb_true⟩ := h
        rw [hall_false b hb_in] at hb_true
        exact Bool.false_ne_true hb_true
      cases h : (Multiset.map (fun f : Lax392996.BooleanFunctions.BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) n => q.fst = u) r₂))).sum
      · rfl
      · exact absurd h hne_true

export Lax392996Proofs.Foreign (diff_annotation_eq_false_iff)

/-! ### The structural commutation theorem

Random-world projection commutes with annotated query evaluation: for any
non-aggregation query `q`, taking the random world `v` of the annotated
result is the same as evaluating `q` on the random-world database. The proof
is a structural induction on `q`, covering all non-aggregation constructors
(including `Prod`, `Dedup`, and `Diff`).

This is the adequacy theorem for the non-monotone fragment: a bag-level
equality between the annotated semantics (specialized to a possible world)
and the plain semantics, valid in the presence of difference and duplicate
elimination. It is the `𝔹`-valuation counterpart of the `ℕ`-adequacy theorem
of [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini, *A Coq
Formalization of Data Provenance*][benzaken2021coq], which is restricted to
the positive fragment – necessarily so, since `ℕ`-adequacy fails as soon as
monus-based difference interacts with duplicate elimination (see
`Nat.counterexample_diff_adequacy` in `Provenance.QueryAdequacy`). -/

variable {K : Type} [Lax392996.SemiringsWithMonus.SemiringWithMonus K] [DecidableEq K]

omit [Fintype X] [DecidableEq X] in
theorem _root_.Lax392996Proofs.Foreign.randomWorld_evaluateAnnotated :
    ∀ {n} (q : Lax392996.RelationalAlgebra.Query T n) (hq : q.source)
      (Î : Lax392996.AnnotatedDatabases.AnnotatedDatabase T (Lax392996.BooleanFunctions.BoolFunc X)) (v : X → Bool),
    Lax392996.ProbabilisticDatabases.randomWorld v (q.evaluateAnnotated hq Î) = q.evaluate (Î.randomWorld v) := by
  intro n q
  induction q with
  | Rel n s =>
    intro hq Î v
    simp only [Lax392996Proofs.Foreign.Query.evaluateAnnotated, Lax392996.MultisetSemantics.Query.evaluate]
    rw [Lax392996Proofs.Foreign.AnnotatedDatabase.find_randomWorld]
    cases hf : Î.find n s
    · rfl
    · simp
  | Proj ts q' ih =>
    intro hq Î v
    simp only [Lax392996Proofs.Foreign.Query.evaluateAnnotated, Lax392996.MultisetSemantics.Query.evaluate]
    rw [← Lax392996Proofs.Foreign.randomWorld_map_data v (fun u : Lax392996.Databases.Tuple T _ => fun k => (ts k).eval u),
        ih (Lax392996Proofs.Foreign.Query.sourceProj hq rfl) Î v]
  | Sel φ q' ih =>
    intro hq Î v
    simp only [Lax392996Proofs.Foreign.Query.evaluateAnnotated, Lax392996.MultisetSemantics.Query.evaluate]
    rw [← ih (Lax392996Proofs.Foreign.Query.sourceSel hq rfl) Î v]
    generalize q'.evaluateAnnotated (Lax392996Proofs.Foreign.Query.sourceSel hq rfl) Î = r
    -- Goal: `randomWorld v (filter_Lex r) = filter φ.eval (randomWorld v r)`.
    -- `randomWorld_filter_data` gives the same equation with a different
    -- `DecidablePred` instance on the inner filter; bridge via
    -- `Subsingleton.elim` (`Decidable` is subsingleton-extensional).
    have h := (Lax392996Proofs.Foreign.randomWorld_filter_data v φ.eval r).symm
    have hinst : (fun a : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) _ => φ.evalDecidable a.fst)
                  = φ.evalDecidableAnnotated := Subsingleton.elim _ _
    rw [hinst] at h
    exact h
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq Î v
    simp only [Lax392996Proofs.Foreign.Query.evaluateAnnotated, Lax392996.MultisetSemantics.Query.evaluate]
    rw [Lax392996Proofs.Foreign.randomWorld_add, ih₁ (Lax392996Proofs.Foreign.Query.sourceSum hq rfl).left Î v,
        ih₂ (Lax392996Proofs.Foreign.Query.sourceSum hq rfl).right Î v]
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    intro hq Î v
    simp only [Lax392996Proofs.Foreign.Query.evaluateAnnotated, Lax392996.MultisetSemantics.Query.evaluate]
    rw [← ih₁ (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).left Î v,
        ← ih₂ (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).right Î v]
    set r₁ := q₁.evaluateAnnotated (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).left Î with hr₁
    set r₂ := q₂.evaluateAnnotated (Lax392996Proofs.Foreign.Query.sourceProd hq rfl).right Î with hr₂
    -- After `subst hn`, the `Eq.mp` cast inside the LHS map and the
    -- `Relation.cast` on the RHS both reduce to identity.
    subst hn
    -- Local helper: `randomWorld v (a ::ₘ t)` is an `if` on `a.snd v`. Stated
    -- in the bare-Multiset (unfolded `randomWorld`) form so all filters are
    -- Prod-typed and the Lex/Prod typeclass mismatch never arises.
    have hrw_cons : ∀ {k : ℕ} (a : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X)
        (t : Multiset (Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X)),
        Multiset.map Prod.fst
            (Multiset.filter (fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) (a ::ₘ t))
          = if a.snd v = true then
              a.fst ::ₘ Multiset.map Prod.fst
                  (Multiset.filter (fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) t)
            else Multiset.map Prod.fst
                  (Multiset.filter (fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) t) := by
      intro k a t
      by_cases ha : a.snd v = true
      · rw [Multiset.filter_cons_of_pos
              (p := fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ ha,
            Multiset.map_cons]
        simp [ha]
      · rw [Multiset.filter_cons_of_neg
              (p := fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ ha]
        simp [ha]
    -- Helper for the cons-head: fixing the left annotated tuple `p`, the
    -- random world of the product slice `Multiset.product {p} r₂'` matches
    -- `Multiset.product {p.fst} (randomWorld v r₂')` (when `p.snd v = true`)
    -- or vanishes (when `p.snd v = false`). Stated in fully unfolded form on
    -- both sides so all filters are Prod-typed.
    have h_head : ∀ (p : Lax392996.Databases.Tuple T n₁ × Lax392996.BooleanFunctions.BoolFunc X)
        (r₂' : Multiset (Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X)),
        Multiset.map Prod.fst
            (Multiset.filter (fun q : Lax392996.Databases.Tuple T (n₁ + n₂) × Lax392996.BooleanFunctions.BoolFunc X => q.snd v = true)
              (Multiset.map (fun pq : (Lax392996.Databases.Tuple T n₁ × Lax392996.BooleanFunctions.BoolFunc X) × (Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X) =>
                  ((Fin.append pq.fst.fst pq.snd.fst : Lax392996.Databases.Tuple T (n₁ + n₂)),
                    pq.fst.snd * pq.snd.snd))
                (Multiset.map (Prod.mk p) r₂')))
          = if p.snd v = true then
              Multiset.map (fun pq : Lax392996.Databases.Tuple T n₁ × Lax392996.Databases.Tuple T n₂ => Fin.append pq.fst pq.snd)
                (Multiset.map (Prod.mk p.fst)
                  (Multiset.map Prod.fst
                    (Multiset.filter (fun q : Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X => q.snd v = true) r₂')))
            else 0 := by
      intro p r₂'
      induction r₂' using Multiset.induction_on with
      | empty =>
        by_cases hp : p.snd v = true
        · rw [if_pos hp]; rfl
        · rw [if_neg hp]; rfl
      | cons q t ih_q =>
        rw [Multiset.map_cons, Multiset.map_cons]
        by_cases hpv : p.snd v = true
        · by_cases hqv : q.snd v = true
          · -- both annotations hold at v: head term survives both filters
            have h_combined : (p.snd * q.snd) v = true := by
              show (p.snd v && q.snd v) = true
              rw [hpv, hqv]; rfl
            rw [Multiset.filter_cons_of_pos
                  (p := fun q : Lax392996.Databases.Tuple T (n₁ + n₂) × Lax392996.BooleanFunctions.BoolFunc X => q.snd v = true)
                  _ h_combined,
                Multiset.map_cons]
            rw [if_pos hpv] at ih_q
            rw [ih_q, if_pos hpv]
            rw [Multiset.filter_cons_of_pos
                  (p := fun q : Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X => q.snd v = true) _ hqv,
                Multiset.map_cons, Multiset.map_cons, Multiset.map_cons]
          · -- p annotation true, q annotation false: head filtered out both sides
            have h_combined : ¬ (p.snd * q.snd) v = true := by
              show ¬ (p.snd v && q.snd v) = true
              rw [hpv]; simp [hqv]
            rw [Multiset.filter_cons_of_neg
                  (p := fun q : Lax392996.Databases.Tuple T (n₁ + n₂) × Lax392996.BooleanFunctions.BoolFunc X => q.snd v = true)
                  _ h_combined]
            rw [if_pos hpv] at ih_q
            rw [ih_q, if_pos hpv]
            rw [Multiset.filter_cons_of_neg
                  (p := fun q : Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X => q.snd v = true) _ hqv]
        · -- p annotation false: every combined annotation is false, total is 0
          have hpv_false : p.snd v = false := by
            cases h : p.snd v
            · rfl
            · exact absurd h hpv
          have h_combined : ¬ (p.snd * q.snd) v = true := by
            show ¬ (p.snd v && q.snd v) = true
            rw [hpv_false]; simp
          rw [Multiset.filter_cons_of_neg
                (p := fun q : Lax392996.Databases.Tuple T (n₁ + n₂) × Lax392996.BooleanFunctions.BoolFunc X => q.snd v = true)
                _ h_combined]
          rw [if_neg hpv] at ih_q
          rw [ih_q, if_neg hpv]
    -- Now induct on r₁ at the bare-Multiset carrier; also expose `r₂` so its
    -- type matches the helper signatures and the `Multiset.product` arguments.
    let r₁' : Multiset (Lax392996.Databases.Tuple T n₁ × Lax392996.BooleanFunctions.BoolFunc X) := r₁
    let r₂' : Multiset (Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X) := r₂
    show Multiset.map Prod.fst
          (Multiset.filter (fun p : Lax392996.Databases.Tuple T (n₁ + n₂) × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true)
            (Multiset.map (fun p : (Lax392996.Databases.Tuple T n₁ × Lax392996.BooleanFunctions.BoolFunc X) × (Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X) =>
                ((Fin.append p.fst.fst p.snd.fst : Lax392996.Databases.Tuple T (n₁ + n₂)), p.fst.snd * p.snd.snd))
              (Multiset.product r₁' r₂'))) =
        Multiset.map (fun p : Lax392996.Databases.Tuple T n₁ × Lax392996.Databases.Tuple T n₂ => Fin.append p.fst p.snd)
          (Multiset.product
            (Multiset.map Prod.fst
              (Multiset.filter (fun p : Lax392996.Databases.Tuple T n₁ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r₁'))
            (Multiset.map Prod.fst
              (Multiset.filter (fun p : Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r₂')))
    induction r₁' using Multiset.induction_on with
    | empty => rfl
    | cons p s ih =>
      -- `Multiset.cons_product` from Mathlib is stated with `×ˢ` notation; the
      -- goal uses `.product` (the underlying `def`). They are definitionally
      -- equal, so unfold `Multiset.product` to `bind` and use `cons_bind`.
      have hcp_left : Multiset.product (p ::ₘ s) r₂'
          = Multiset.map (Prod.mk p) r₂' + Multiset.product s r₂' := by
        unfold Multiset.product
        rw [Multiset.cons_bind]
      -- LHS: distribute product/map/filter over the cons of `r₁`.
      rw [hcp_left, Multiset.map_add, Multiset.filter_add, Multiset.map_add]
      -- RHS: factor `randomWorld v (p ::ₘ s)` via `hrw_cons` and apply `h_head`.
      rw [hrw_cons p s, h_head p r₂']
      by_cases hpv : p.snd v = true
      · -- Same form for the RHS product after `if_pos hpv` exposes a cons.
        have hcp_rhs : Multiset.product (p.fst ::ₘ Multiset.map Prod.fst
              (Multiset.filter (fun p : Lax392996.Databases.Tuple T n₁ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s))
            (Multiset.map Prod.fst
              (Multiset.filter (fun p : Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r₂'))
          = Multiset.map (Prod.mk p.fst) (Multiset.map Prod.fst
              (Multiset.filter (fun p : Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r₂'))
            + Multiset.product (Multiset.map Prod.fst
                (Multiset.filter (fun p : Lax392996.Databases.Tuple T n₁ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) s))
              (Multiset.map Prod.fst
                (Multiset.filter (fun p : Lax392996.Databases.Tuple T n₂ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r₂')) := by
          unfold Multiset.product
          rw [Multiset.cons_bind]
        rw [if_pos hpv, if_pos hpv, hcp_rhs, Multiset.map_add, ih]
      · rw [if_neg hpv, if_neg hpv]
        rw [ih]
        exact (Multiset.zero_add _)
  | Dedup q' ih =>
    intro hq Î v
    simp only [Lax392996Proofs.Foreign.Query.evaluateAnnotated, Lax392996.MultisetSemantics.Query.evaluate]
    rw [← ih (Lax392996Proofs.Foreign.Query.sourceDedup hq rfl) Î v]
    set r := q'.evaluateAnnotated (Lax392996Proofs.Foreign.Query.sourceDedup hq rfl) Î with hr
    -- Both sides are `Nodup` multisets of `Tuple T n`. We show element
    -- equivalence: t ∈ LHS ↔ ∃ (t', α') ∈ r with t' = t and α' v = true ↔ t ∈ RHS.
    have hgbk_nodup : (Multiset.ofList (Lax392996Proofs.Foreign.groupByKey r).val :
        Multiset (Lax392996.Databases.Tuple T _ × Lax392996.BooleanFunctions.BoolFunc X)).Nodup := by
      rw [Multiset.coe_nodup]
      exact Lax392996Proofs.Foreign.KeyValueList.nodup _ (Lax392996Proofs.Foreign.groupByKey r).property
    have hLNodup : (Lax392996.ProbabilisticDatabases.randomWorld v (Multiset.ofList (Lax392996Proofs.Foreign.groupByKey r).val)).Nodup := by
      show (Multiset.map Prod.fst _).Nodup
      apply Multiset.Nodup.map_on
      · -- Local injectivity: same-key entries of `groupByKey` agree.
        intro p hp q hq hpq
        rw [Multiset.mem_filter] at hp hq
        have hp_list : p ∈ (Lax392996Proofs.Foreign.groupByKey r).val := Multiset.mem_coe.mp hp.1
        have hq_list : q ∈ (Lax392996Proofs.Foreign.groupByKey r).val := Multiset.mem_coe.mp hq.1
        have hsnd := Lax392996Proofs.Foreign.KeyValueList.functional _ (Lax392996Proofs.Foreign.groupByKey r).property
          p hp_list q hq_list hpq
        exact Prod.ext hpq hsnd
      · exact Multiset.Nodup.filter _ hgbk_nodup
    have hRNodup : (Multiset.dedup (Lax392996.ProbabilisticDatabases.randomWorld v r)).Nodup := Multiset.nodup_dedup _
    rw [Multiset.Nodup.ext hLNodup hRNodup]
    intro t
    -- The membership condition on both sides reduces to:
    -- `∃ (t', α') ∈ r with t' = t and α' v = true`.
    constructor
    · rintro ht
      show t ∈ Multiset.dedup (Lax392996.ProbabilisticDatabases.randomWorld v r)
      rw [Multiset.mem_dedup]
      -- ht : t ∈ randomWorld v (ofList (groupByKey r).val)
      show t ∈ Lax392996.ProbabilisticDatabases.randomWorld v r
      unfold Lax392996.ProbabilisticDatabases.randomWorld at ht ⊢
      rw [Multiset.mem_map] at ht
      obtain ⟨p, hp, hpfst⟩ := ht
      rw [Multiset.mem_filter] at hp
      obtain ⟨hp_in, hp_snd⟩ := hp
      have hp_list : p ∈ (Lax392996Proofs.Foreign.groupByKey r).val := Multiset.mem_coe.mp hp_in
      -- (p.fst, p.snd) ∈ (groupByKey r).val so groupByKey_value applies.
      have hp_val : p.snd = (Multiset.map Prod.snd
            (Multiset.filter (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) _ ↦ q.fst = p.fst) r)).sum :=
        Lax392996Proofs.Foreign.groupByKey_value r p.fst p.snd hp_list
      rw [hp_val, Lax392996Proofs.Foreign.boolFunc_multiset_sum_apply, Lax392996Proofs.Foreign.bool_multiset_sum_eq_true] at hp_snd
      obtain ⟨b, hb_in, hb_true⟩ := hp_snd
      rw [Multiset.mem_map] at hb_in
      obtain ⟨α, hα_in, hα_eq⟩ := hb_in
      rw [Multiset.mem_map] at hα_in
      obtain ⟨α_pair, hα_pair_in, hα_pair_snd⟩ := hα_in
      rw [Multiset.mem_filter] at hα_pair_in
      obtain ⟨hα_r, hα_fst⟩ := hα_pair_in
      -- α_pair ∈ r with α_pair.fst = p.fst and α_pair.snd v = true
      rw [Multiset.mem_map]
      refine ⟨α_pair, ?_, ?_⟩
      · rw [Multiset.mem_filter]
        refine ⟨hα_r, ?_⟩
        rw [hα_pair_snd, hα_eq, hb_true]
      · rw [hα_fst, hpfst]
    · rintro ht
      rw [Multiset.mem_dedup] at ht
      show t ∈ Lax392996.ProbabilisticDatabases.randomWorld v (Multiset.ofList (Lax392996Proofs.Foreign.groupByKey r).val)
      unfold Lax392996.ProbabilisticDatabases.randomWorld at ht ⊢
      rw [Multiset.mem_map] at ht
      obtain ⟨α_pair, hα_in, hα_fst⟩ := ht
      rw [Multiset.mem_filter] at hα_in
      obtain ⟨hα_r, hα_v⟩ := hα_in
      -- α_pair ∈ r with α_pair.fst = t and α_pair.snd v = true
      have hmem_map : t ∈ Multiset.map Prod.fst r := by
        rw [Multiset.mem_map]; exact ⟨α_pair, hα_r, hα_fst⟩
      obtain ⟨w, hw_in⟩ := (Lax392996Proofs.Foreign.groupByKey_key_iff r t).mpr hmem_map
      have hw_val : w = (Multiset.map Prod.snd
            (Multiset.filter (fun q : Lax392996.AnnotatedDatabases.AnnotatedTuple T (Lax392996.BooleanFunctions.BoolFunc X) _ ↦ q.fst = t) r)).sum :=
        Lax392996Proofs.Foreign.groupByKey_value r t w hw_in
      have hw_v_true : w v = true := by
        rw [hw_val, Lax392996Proofs.Foreign.boolFunc_multiset_sum_apply, Lax392996Proofs.Foreign.bool_multiset_sum_eq_true]
        refine ⟨α_pair.snd v, ?_, hα_v⟩
        rw [Multiset.mem_map]
        refine ⟨α_pair.snd, ?_, rfl⟩
        rw [Multiset.mem_map]
        refine ⟨α_pair, ?_, rfl⟩
        rw [Multiset.mem_filter]
        exact ⟨hα_r, hα_fst⟩
      rw [Multiset.mem_map]
      refine ⟨(t, w), ?_, rfl⟩
      rw [Multiset.mem_filter]
      exact ⟨Multiset.mem_coe.mpr hw_in, hw_v_true⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq Î v
    simp only [Lax392996Proofs.Foreign.Query.evaluateAnnotated, Lax392996.MultisetSemantics.Query.evaluate]
    rw [← ih₁ (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).left Î v,
        ← ih₂ (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).right Î v]
    set r₁ := q₁.evaluateAnnotated (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).left Î with hr₁
    set r₂ := q₂.evaluateAnnotated (Lax392996Proofs.Foreign.Query.sourceDiff hq rfl).right Î with hr₂
    -- Local helper: random-world of a cons splits via if-then-else.
    -- Stated in the bare-Multiset form (the unfolded `randomWorld`) so the
    -- pattern matches the goal's Lex-coerced filter+map term.
    have hrw_cons : ∀ {k : ℕ} (a : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X)
        (t : Multiset (Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X)),
        Multiset.map Prod.fst
            (Multiset.filter (fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) (a ::ₘ t))
          = if a.snd v = true then
              a.fst ::ₘ Multiset.map Prod.fst
                  (Multiset.filter (fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) t)
            else Multiset.map Prod.fst
                  (Multiset.filter (fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) t) := by
      intro k a t
      by_cases ha : a.snd v = true
      · rw [Multiset.filter_cons_of_pos
              (p := fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ ha,
            Multiset.map_cons]
        simp [ha]
      · rw [Multiset.filter_cons_of_neg
              (p := fun p : Lax392996.Databases.Tuple T k × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) _ ha]
        simp [ha]
    -- Induct on r₁ at the Prod-type carrier. We must override `randomWorld`
    -- to accept `Multiset (Tuple T _ × BoolFunc X)` directly so the pattern
    -- in the recursive `hrw_cons` call matches the goal's coerced form.
    let r₁' : Multiset (Lax392996.Databases.Tuple T _ × Lax392996.BooleanFunctions.BoolFunc X) := r₁
    show Multiset.map Prod.fst
          (Multiset.filter (fun p : Lax392996.Databases.Tuple T _ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true)
            (r₁'.map (fun p : Lax392996.Databases.Tuple T _ × Lax392996.BooleanFunctions.BoolFunc X =>
              (p.fst, p.snd -
                (((Lax392996Proofs.Foreign.groupByKey r₂).val.find? (fun q => q.1 = p.fst)).map Prod.snd).getD 0))))
        = Multiset.filter (fun t => t ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂)
            (Multiset.map Prod.fst
              (Multiset.filter (fun p : Lax392996.Databases.Tuple T _ × Lax392996.BooleanFunctions.BoolFunc X => p.snd v = true) r₁'))
    induction r₁' using Multiset.induction_on with
    | empty => rfl
    | cons p s ih =>
      -- Set β to the diff annotation for `p.fst`. We define β AFTER
      -- `Multiset.map_cons` fires so the goal's term contains β by construction.
      rw [Multiset.map_cons]
      set β : Lax392996.BooleanFunctions.BoolFunc X :=
          ((List.find? (fun q : Lax392996.Databases.Tuple T _ × Lax392996.BooleanFunctions.BoolFunc X => decide (q.1 = p.fst))
            (Lax392996Proofs.Foreign.groupByKey r₂).val).map Prod.snd).getD 0 with hβ_def
      have hβ_iff : β v = false ↔ p.fst ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂ :=
        Lax392996Proofs.Foreign.diff_annotation_eq_false_iff v r₂ p.fst
      -- Pull cons through randomWorld on both LHS and RHS.
      rw [hrw_cons (a := (p.fst, p.snd - β))]
      conv_rhs => rw [hrw_cons (a := p) (t := s)]
      -- The cons-head's snd-at-v on the LHS reduces to `p.snd v && !(β v)`.
      have hlhs_eq : (p.fst, p.snd - β).snd v = (p.snd v && !(β v)) := rfl
      by_cases hpv : p.snd v = true
      · -- p.snd v = true. Case on β v.
        by_cases hbv : β v = false
        · -- β v = false ⇒ p.fst ∉ rw v r₂.
          have hp_notin : p.fst ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂ := hβ_iff.mp hbv
          have hcond_lhs : (p.snd - β) v = true := by
            rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv, hbv]; rfl
          rw [if_pos hcond_lhs, if_pos hpv, ih]
          rw [Multiset.filter_cons_of_pos
                (p := fun t : Lax392996.Databases.Tuple T _ => t ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂) _ hp_notin]
        · -- β v ≠ false, so β v = true; p.fst ∈ rw v r₂.
          have hbv_true : β v = true := by
            cases h : β v
            · exact absurd h hbv
            · rfl
          have hp_in : ¬ p.fst ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂ := by
            intro h; exact absurd (hβ_iff.mpr h) hbv
          have hcond_lhs : ¬ (p.snd - β) v = true := by
            rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv, hbv_true]
            simp
          rw [if_neg hcond_lhs, if_pos hpv, ih]
          rw [Multiset.filter_cons_of_neg
                (p := fun t : Lax392996.Databases.Tuple T _ => t ∉ Lax392996.ProbabilisticDatabases.randomWorld v r₂) _ hp_in]
      · -- p.snd v = false: cond on LHS reduces to `false`.
        have hpv_false : p.snd v = false := by
          cases h : p.snd v
          · rfl
          · exact absurd h hpv
        have hcond_lhs : ¬ (p.snd - β) v = true := by
          rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv_false]; simp
        rw [if_neg hcond_lhs, if_neg hpv]
        exact ih
  | ProvSum _ _ _ =>
    intro hq _ _
    exact False.elim (by simp [Lax392996.RelationalAlgebra.Query.source] at hq)
  | Having _ _ _ _ _ _ _ =>
    intro hq _ _
    exact False.elim (by simp [Lax392996.RelationalAlgebra.Query.source] at hq)

export Lax392996Proofs.Foreign (randomWorld_evaluateAnnotated)

namespace ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

end ProbAssignment

namespace Lax392996.ProbabilisticDatabases.ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

open Lax392996Proofs.Foreign.ProbAssignment in
/-- **Theorem 12** ([Sen, Maniu & Senellart][sen2026provsql], Section IV-D).
For any non-aggregation query `q`, any `BoolFunc X`-annotated database `Î`
and any tuple `t`, the marginal probability that `t` appears in the random
output of `q` equals the probability of the disjunctive tuple annotation
of `t` in the annotated query result `⟪q⟫^Î`.

This is the formal justification for ProvSQL's intensional approach to
probabilistic query evaluation: instead of enumerating exponentially-many
possible worlds, evaluate the query once over `BoolFunc X`-annotations and
take the probability of the resulting Boolean function.

The proof reduces to (a) `tupleAnnotation_apply_eq_true_iff`, the pointwise
reading of the disjunctive annotation, and (b) `randomWorld_evaluateAnnotated`,
the commutation of plain query evaluation with random-world projection. -/
theorem _root_.Lax392996Proofs.Foreign.ProbAssignment.theorem_12
    (q : Lax392996.RelationalAlgebra.Query T n) (hq : q.source)
    (Î : Lax392996.AnnotatedDatabases.AnnotatedDatabase T (Lax392996.BooleanFunctions.BoolFunc X)) (t : Lax392996.Databases.Tuple T n) :
    P.marginalProb q Î t
      = P.funcProb (Lax392996.ProbabilisticDatabases.tupleAnnotation (q.evaluateAnnotated hq Î) t) := by
  unfold Lax392996.ProbabilisticDatabases.ProbAssignment.marginalProb Lax392996.ProbabilisticDatabases.ProbAssignment.funcProb
  apply Finset.sum_congr rfl
  intro v _
  -- Both indicators are the same: t ∈ randomWorld v (⟪q⟫_Î) ↔ tupleAnnotation _ _ v
  have hcond :
      t ∈ q.evaluate (Î.randomWorld v)
        ↔ (Lax392996.ProbabilisticDatabases.tupleAnnotation (q.evaluateAnnotated hq Î) t) v = true := by
    rw [← Lax392996Proofs.Foreign.randomWorld_evaluateAnnotated q hq Î v]
    exact (Lax392996Proofs.Foreign.tupleAnnotation_apply_eq_true_iff _ _ _).symm
  by_cases h : (Lax392996.ProbabilisticDatabases.tupleAnnotation (q.evaluateAnnotated hq Î) t) v = true
  · simp [h, hcond.mpr h]
  · have hmem : ¬ t ∈ q.evaluate (Î.randomWorld v) :=
      fun hm => h (hcond.mp hm)
    have hf : (Lax392996.ProbabilisticDatabases.tupleAnnotation (q.evaluateAnnotated hq Î) t) v = false := by
      cases h' : (Lax392996.ProbabilisticDatabases.tupleAnnotation (q.evaluateAnnotated hq Î) t) v
      · rfl
      · exact absurd h' h
    simp [hmem, hf]

end Lax392996.ProbabilisticDatabases.ProbAssignment

namespace ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

end ProbAssignment

namespace Lax392996.ProbabilisticDatabases.ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

export Lax392996Proofs.Foreign.ProbAssignment (theorem_12)

end Lax392996.ProbabilisticDatabases.ProbAssignment

namespace ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

export Lax392996Proofs.Foreign.ProbAssignment (theorem_12)

end ProbAssignment

/-! ## Corollary 13: probability via the plain rewritten query

Theorem 12 expresses the marginal probability `Pr(t ∈ q(Î))` as the
probability of the disjunctive tuple annotation of `t` in the annotated query
result `⟪q⟫^Î`. Combining it with the rewriting-correctness theorem
`Query.rewriting_valid` (Theorem 10 of [Sen, Maniu & Senellart][sen2026provsql],
rules R1–R5) gives the same identity using the **plain** rewritten query
`q̂ = q.rewriting hq` evaluated on the composite-encoded database
`Î.toComposite`. This is the form ProvSQL actually runs against PostgreSQL.

The corollary statement requires `[HasAltLinearOrder (BoolFunc X)]` purely so
that `Î.toComposite : Database (T ⊕ BoolFunc X)` typechecks (via the
`ValueType (T ⊕ K)` instance in `Provenance.Util.ValueType`); any
noncomputable linear order on `BoolFunc X` will do. -/

namespace ProbAssignment

variable (P : Lax392996.ProbabilisticDatabases.ProbAssignment X)

end ProbAssignment


