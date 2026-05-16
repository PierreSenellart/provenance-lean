import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

import Provenance.QueryAnnotatedDatabase
import Provenance.QueryAnnotatedDatabaseHom
import Provenance.QueryRewriting
import Provenance.Semirings.Bool
import Provenance.Semirings.BoolFunc

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

This is the foundation needed to state and prove Theorem 12 of the paper
(intensional probabilistic query evaluation correctness): for any
non-aggregation query `q`, any `BoolFunc X`-instance `Î` and any tuple `t`,
`Pr(t ∈ q(Î)) = Pr(⋁_{(t,α) ∈ ⟪q⟫^Î} α)`. The theorem itself is stated below
and the algebraic-bridge lemmas are developed; the full proof depends on a
"Bool-annotated semantics tracks plain semantics on the boolean-true support"
result that is left as future work.

## Main definitions

* `ProbAssignment X` — a probability assignment to each variable, bundled
  with `0 ≤ Pr(x) ≤ 1`.
* `ProbAssignment.valProb` — `Pr(v)` for a single valuation `v : X → Bool`.
* `ProbAssignment.funcProb` — `Pr(f)` for a Boolean function `f : BoolFunc X`.

## Main results

* `ProbAssignment.valProb_nonneg`, `valProb_le_one`, `sum_valProb_eq_one` —
  basic properties of the valuation distribution.
* `ProbAssignment.funcProb_zero`, `funcProb_one`, `funcProb_nonneg`,
  `funcProb_le_one` — basic properties of `Pr(f)`.
* `ProbAssignment.funcProb_congr` — pointwise-equal Boolean functions have
  equal probabilities.

## References

* [Sen, Maniu & Senellart][sen2026provsql] (Section IV-D)
-/

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

omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is non-negative. -/
private lemma valProb_factor_nonneg (v : X → Bool) (x : X) :
    0 ≤ (if v x then P.prob x else 1 - P.prob x) := by
  by_cases hv : v x
  · simp [hv]; exact P.prob_nonneg x
  · simp [hv]
    have := P.prob_le_one x
    linarith

omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is at most `1`. -/
private lemma valProb_factor_le_one (v : X → Bool) (x : X) :
    (if v x then P.prob x else 1 - P.prob x) ≤ 1 := by
  by_cases hv : v x
  · simp [hv]; exact P.prob_le_one x
  · simp [hv]
    have := P.prob_nonneg x
    linarith

omit [DecidableEq X] in
theorem valProb_nonneg (v : X → Bool) : 0 ≤ P.valProb v :=
  Finset.prod_nonneg (fun x _ => P.valProb_factor_nonneg v x)

omit [DecidableEq X] in
theorem valProb_le_one (v : X → Bool) : P.valProb v ≤ 1 := by
  unfold valProb
  calc ∏ x, (if v x then P.prob x else 1 - P.prob x)
      ≤ ∏ _x : X, (1 : ℚ) :=
        Finset.prod_le_prod
          (fun x _ => P.valProb_factor_nonneg v x)
          (fun x _ => P.valProb_factor_le_one v x)
    _ = 1 := by simp

omit [Fintype X] [DecidableEq X] in
/-- For any `x : X`, `Pr(x) + (1 - Pr(x)) = 1`: summing the two cases of the
factor at `x` over `Bool` gives `1`. -/
private lemma sum_factor_at (x : X) :
    ∑ b : Bool, (if b then P.prob x else 1 - P.prob x) = 1 := by
  -- Bool's univ is {false, true}; enumerate explicitly.
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
      Finset.sum_singleton]
  simp

/-- The valuations form a probability distribution: `∑ v, Pr(v) = 1`. -/
theorem sum_valProb_eq_one : ∑ v : X → Bool, P.valProb v = 1 := by
  -- Reduce ∑_v ∏_x f(x, v x) to ∏_x ∑_b f(x, b) via Fintype.prod_sum, then
  -- close via `sum_factor_at`.
  have hps :
      (∏ x : X, ∑ b : Bool, (if b then P.prob x else 1 - P.prob x))
        = ∑ v : X → Bool, ∏ x : X, (if v x then P.prob x else 1 - P.prob x) :=
    Fintype.prod_sum (fun (x : X) (b : Bool) => if b then P.prob x else 1 - P.prob x)
  unfold valProb
  rw [← hps]
  simp_rw [P.sum_factor_at]
  simp


/-- Probability of a Boolean function: `Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : BoolFunc X) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0

theorem funcProb_nonneg (f : BoolFunc X) : 0 ≤ P.funcProb f := by
  unfold funcProb
  apply Finset.sum_nonneg
  intro v _
  by_cases hv : f v
  · simp [hv]; exact P.valProb_nonneg v
  · simp [hv]

/-- `Pr(f) ≤ ∑_v Pr(v) = 1`. -/
theorem funcProb_le_one (f : BoolFunc X) : P.funcProb f ≤ 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold funcProb
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : f v
  · simp [hv]
  · simp [hv]; exact P.valProb_nonneg v

/-- `Pr(0) = 0`: the constant-false function has probability zero. -/
theorem funcProb_zero : P.funcProb (0 : BoolFunc X) = 0 := by
  unfold funcProb
  apply Finset.sum_eq_zero
  intro v _
  show (if (0 : BoolFunc X) v then P.valProb v else 0) = 0
  -- (0 : BoolFunc X) v = false
  have h : (0 : BoolFunc X) v = false := rfl
  rw [h]
  simp

/-- `Pr(1) = 1`: the constant-true function has probability one. -/
theorem funcProb_one : P.funcProb (1 : BoolFunc X) = 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold funcProb
  apply Finset.sum_congr rfl
  intro v _
  have h : (1 : BoolFunc X) v = true := rfl
  rw [h]
  simp

/-- Pointwise-equal Boolean functions have equal probabilities. -/
theorem funcProb_congr {f g : BoolFunc X} (h : ∀ v, f v = g v) :
    P.funcProb f = P.funcProb g := by
  unfold funcProb
  apply Finset.sum_congr rfl
  intro v _
  rw [h v]

/-- Reformulation: `Pr(f)` as a sum over the satisfying valuations. -/
theorem funcProb_eq_filter_sum (f : BoolFunc X) :
    P.funcProb f = ∑ v ∈ Finset.univ.filter (fun v => f v = true), P.valProb v := by
  unfold funcProb
  rw [← Finset.sum_filter]

end ProbAssignment

/-- For finite `X`, equality of Boolean functions `(X → Bool) → Bool` is
decidable in principle (since the function space is finite). We expose the
classical decidability instance so that `Query.evaluateAnnotated`, which
requires `[DecidableEq K]`, can be invoked for `K = BoolFunc X`. -/
noncomputable instance instDecidableEqBoolFunc : DecidableEq (BoolFunc X) :=
  Classical.decEq _

/-- `Relation T n` is a `def` for `Multiset (Tuple T n)`, so the standard
`Membership` instance does not propagate automatically. Re-expose it so that
`t ∈ q.evaluate d` typechecks. (We deliberately do *not* use this instance
inside the body of `randomWorld`, which returns a bare `Multiset` so that
`Multiset.mem_map` rewrites apply cleanly.) -/
instance instMembershipRelation {T : Type} {n : ℕ} :
    Membership (Tuple T n) (Relation T n) :=
  inferInstanceAs (Membership (Tuple T n) (Multiset (Tuple T n)))

/-- Decidability of `t ∈ q.evaluate d` (with `[ValueType T]`). -/
instance instDecidableMemRelation {T : Type} [ValueType T] {n : ℕ}
    (t : Tuple T n) (r : Relation T n) : Decidable (t ∈ r) :=
  Multiset.decidableMem t r

/-- Membership in `AnnotatedRelation` (a `def`-wrapped `Multiset`). -/
instance instMembershipAnnotatedRelation {T K : Type} {n : ℕ} :
    Membership (AnnotatedTuple T K n) (AnnotatedRelation T K n) :=
  inferInstanceAs (Membership (AnnotatedTuple T K n) (Multiset (AnnotatedTuple T K n)))

/-! ## Random worlds and the disjunctive tuple annotation

We now move toward Theorem 12 of the paper. Two pieces of infrastructure are
needed: the **random world** of a `BoolFunc X`-annotated relation under a
valuation `v : X → Bool` (the plain relation containing exactly the data
parts of the annotated tuples whose annotation evaluates to `true` at `v`),
and the **disjunctive tuple annotation** `⋁_{(t,α) ∈ r} α` (a single Boolean
function summarising all the ways `t` can appear in `r`). -/

variable {T : Type} [ValueType T]

/-- The disjunctive tuple annotation `tupleAnnotation r t = ⋁_{(t,α) ∈ r} α`:
the OR over the annotations of all annotated tuples in `r` whose data part
equals `t`. In the m-semiring `BoolFunc X`, multiset sum is pointwise OR, so
this is exactly the disjunction the paper writes inside `Pr(·)` on the
right-hand side of Theorem 12. -/
def tupleAnnotation (r : AnnotatedRelation T (BoolFunc X) n) (t : Tuple T n) :
    BoolFunc X :=
  (Multiset.map Prod.snd
    (Multiset.filter (fun p : AnnotatedTuple T (BoolFunc X) n => p.fst = t) r)).sum

/-- The random world of a `BoolFunc X`-annotated relation under a valuation
`v`: the plain relation consisting of the data parts of the annotated tuples
whose annotation evaluates to `true` at `v`. The return type is a bare
`Multiset (Tuple T n)` (rather than `Relation T n`) so that `Multiset` lemmas
apply without an extra unfolding step. -/
def randomWorld (v : X → Bool) (r : AnnotatedRelation T (BoolFunc X) n) :
    Multiset (Tuple T n) :=
  Multiset.map Prod.fst
    (Multiset.filter (fun p : AnnotatedTuple T (BoolFunc X) n => p.snd v = true) r)

/-- Pointwise random world of a `BoolFunc X`-annotated database: each
annotated relation is replaced by its plain random-world projection. -/
def AnnotatedDatabase.randomWorld
    (v : X → Bool) (Î : AnnotatedDatabase T (BoolFunc X)) : Database T :=
  Î.map (fun e => (e.fst, ⟨e.snd.fst, _root_.randomWorld v e.snd.snd⟩))

/-! ### Pointwise meaning of `tupleAnnotation`

`(tupleAnnotation r t)(v) = true` iff some annotated tuple `(t, α) ∈ r` has
`α(v) = true`. This is the connection between the disjunction-on-the-right
of Theorem 12 and the random-world picture on the left. -/

omit [Fintype X] [DecidableEq X] in
/-- `Multiset.sum` of a multiset of `BoolFunc X` evaluated at `v` equals the
sum (in `Bool`) of the pointwise evaluations: this just pushes evaluation at
`v` through the additive monoid hom. -/
private lemma boolFunc_multiset_sum_apply
    (s : Multiset (BoolFunc X)) (v : X → Bool) :
    s.sum v = (s.map (fun f => f v)).sum := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons f t ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih]
    rfl

/-- A multiset sum in `Bool` (where `+` is OR) equals `true` iff some element
of the multiset is `true`. -/
private lemma bool_multiset_sum_eq_true (s : Multiset Bool) :
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

omit [Fintype X] [DecidableEq X] in
/-- **Pointwise reading of `tupleAnnotation`.** `(tupleAnnotation r t)(v) = true`
exactly when the random world at `v` of `r` contains `t`. -/
theorem tupleAnnotation_apply_eq_true_iff
    (r : AnnotatedRelation T (BoolFunc X) n) (t : Tuple T n) (v : X → Bool) :
    (tupleAnnotation r t) v = true ↔ t ∈ randomWorld v r := by
  unfold tupleAnnotation randomWorld
  rw [boolFunc_multiset_sum_apply, bool_multiset_sum_eq_true]
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

/-! ## Marginal probability and the statement of Theorem 12

The marginal probability `Pr(t ∈ q(Î))` is defined as the sum over valuations
`v` of `Pr(v)` indexed by whether `t` appears in `q.evaluate (Î.randomWorld v)`.
This is the standard "intensional" definition: enumerate possible worlds,
weight each by its probability, and accumulate the indicator that the query
output contains `t`.

The paper writes the same thing as `∑_J [t ∈ ⟦q⟧(J)] · Pr(J)` over
sub-instances `J ⊆ Î`. The two sums agree because, for each valuation `v`,
the unique `J` whose characteristic Boolean function `Φ_J(Î)` is satisfied at
`v` is exactly `J(v) = { (u, α) ∈ Î | α(v) = true }`, whose data side is
`Î.randomWorld v`. -/

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Marginal probability that the tuple `t` appears in the output of `q`
when evaluated on a random world of `Î`. -/
noncomputable def marginalProb
    (q : Query T n) (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) : ℚ :=
  ∑ v : X → Bool,
    if t ∈ q.evaluate (Î.randomWorld v) then P.valProb v else 0

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

-- Make `Filter.eval`'s decidability available as an instance (by default it
-- is a `@[reducible] def`), so that `Multiset.filter`-by-`φ.eval` inside the
-- query semantics can match `Multiset.filter`-by-`φ.eval` inside our helpers.
attribute [instance] Filter.evalDecidable Filter.evalDecidableAnnotated

/-! ### Helper lemmas: random-world commutes with Multiset operations -/

omit [Fintype X] [DecidableEq X] in
@[simp] lemma randomWorld_zero (v : X → Bool) :
    randomWorld v (0 : AnnotatedRelation T (BoolFunc X) n) = 0 := rfl

omit [Fintype X] [DecidableEq X] in
/-- `randomWorld` is additive on relations: filtering and projecting the
data side commutes with multiset sum. -/
lemma randomWorld_add (v : X → Bool)
    (r₁ r₂ : AnnotatedRelation T (BoolFunc X) n) :
    randomWorld v (r₁ + r₂) = randomWorld v r₁ + randomWorld v r₂ := by
  unfold randomWorld
  exact (congr_arg (Multiset.map Prod.fst)
          (Multiset.filter_add (fun p : AnnotatedTuple T (BoolFunc X) n => p.snd v = true)
            r₁ r₂)).trans
    (Multiset.map_add _ _ _)

omit [Fintype X] [DecidableEq X] in
/-- Filtering the data side commutes with `randomWorld v`. -/
lemma randomWorld_filter_data (v : X → Bool)
    (φ : Tuple T n → Prop) [DecidablePred φ]
    (r : AnnotatedRelation T (BoolFunc X) n) :
    Multiset.filter φ (randomWorld v r) =
      randomWorld v (Multiset.filter (fun p : Tuple T n × BoolFunc X => φ p.fst) r) := by
  let r' : Multiset (Tuple T n × BoolFunc X) := r
  show Multiset.filter φ
        (Multiset.map Prod.fst
          (Multiset.filter (fun p : Tuple T n × BoolFunc X => p.snd v = true) r'))
      = Multiset.map Prod.fst
          (Multiset.filter (fun p : Tuple T n × BoolFunc X => p.snd v = true)
            (Multiset.filter (fun p : Tuple T n × BoolFunc X => φ p.fst) r'))
  induction r' using Multiset.induction_on with
  | empty => rfl
  | cons q s ih =>
    by_cases hq : q.snd v = true
    · by_cases hφ : φ q.fst
      · -- both filters pos
        rw [Multiset.filter_cons_of_pos
              (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) s hq,
            Multiset.map_cons,
            Multiset.filter_cons_of_pos (p := φ) _ hφ,
            Multiset.filter_cons_of_pos
              (p := fun p : Tuple T n × BoolFunc X => φ p.fst) s hφ,
            Multiset.filter_cons_of_pos
              (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) _ hq,
            Multiset.map_cons, ih]
      · -- snd-filter pos, fst-filter neg
        rw [Multiset.filter_cons_of_pos
              (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) s hq,
            Multiset.map_cons,
            Multiset.filter_cons_of_neg (p := φ) _ hφ,
            Multiset.filter_cons_of_neg
              (p := fun p : Tuple T n × BoolFunc X => φ p.fst) s hφ, ih]
    · by_cases hφ : φ q.fst
      · -- snd-filter neg, fst-filter pos
        rw [Multiset.filter_cons_of_neg
              (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) s hq,
            Multiset.filter_cons_of_pos
              (p := fun p : Tuple T n × BoolFunc X => φ p.fst) s hφ,
            Multiset.filter_cons_of_neg
              (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) _ hq, ih]
      · rw [Multiset.filter_cons_of_neg
              (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) s hq,
            Multiset.filter_cons_of_neg
              (p := fun p : Tuple T n × BoolFunc X => φ p.fst) s hφ, ih]

omit [Fintype X] [DecidableEq X] in
/-- Mapping the data side commutes with `randomWorld v`. Proved by
`Multiset.induction_on`, with all `Multiset.filter` / `Multiset.map` lemmas
called with named `(p := ...)` / explicit-type arguments so Lean's HOU does
not pick a wrong decomposition and so the underlying `Lex`-unfolded carrier
type matches between goal and rewrite. -/
lemma randomWorld_map_data (v : X → Bool) (f : Tuple T n → Tuple T m)
    (r : AnnotatedRelation T (BoolFunc X) n) :
    Multiset.map f (randomWorld v r) =
      randomWorld v (r.map (fun p : AnnotatedTuple T (BoolFunc X) n => (f p.fst, p.snd))) := by
  -- Work with the underlying plain-`Prod` carrier so that all subterms agree
  -- on the syntactic representation of the tuple type.
  let r' : Multiset (Tuple T n × BoolFunc X) := r
  show Multiset.map f
        (Multiset.map Prod.fst
          (Multiset.filter (fun p : Tuple T n × BoolFunc X => p.snd v = true) r'))
      = Multiset.map Prod.fst
          (Multiset.filter (fun p : Tuple T m × BoolFunc X => p.snd v = true)
            (Multiset.map (fun p : Tuple T n × BoolFunc X => (f p.fst, p.snd)) r'))
  induction r' using Multiset.induction_on with
  | empty => rfl
  | cons q s ih =>
    by_cases hq : q.snd v = true
    · have hq' : (f q.fst, q.snd).snd v = true := hq
      rw [Multiset.map_cons (fun p : Tuple T n × BoolFunc X => (f p.fst, p.snd)) q s,
          Multiset.filter_cons_of_pos
            (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) s hq,
          Multiset.filter_cons_of_pos
            (p := fun p : Tuple T m × BoolFunc X => p.snd v = true) _ hq',
          Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, ih]
    · have hq' : ¬ (f q.fst, q.snd).snd v = true := hq
      rw [Multiset.map_cons (fun p : Tuple T n × BoolFunc X => (f p.fst, p.snd)) q s,
          Multiset.filter_cons_of_neg
            (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) s hq,
          Multiset.filter_cons_of_neg
            (p := fun p : Tuple T m × BoolFunc X => p.snd v = true) _ hq', ih]

/-! ### Random world commutes with `find` -/

omit [Fintype X] [DecidableEq X] in
lemma AnnotatedDatabase.find_randomWorld
    (n : ℕ) (s : String) (Î : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool) :
    (Î.randomWorld v).find n s = (Î.find n s).map (_root_.randomWorld v) := by
  induction Î with
  | nil => rfl
  | cons hd tl ih =>
    unfold AnnotatedDatabase.randomWorld AnnotatedDatabase.find AnnotatedDatabase.find.f
            Database.find Database.find.f
    by_cases hcond : n = hd.snd.fst ∧ s = hd.fst
    · simp [hcond]
      have := hcond.left; subst this
      rfl
    · simp [hcond]
      unfold AnnotatedDatabase.randomWorld AnnotatedDatabase.find at ih
      exact ih

/-! ### Diff annotation helper

For the `Diff` case of the structural commutation theorem we need to
characterise when the annotation subtracted from `r₁`'s entries evaluates to
`false` at the valuation `v`: this happens exactly when the data tuple is
not in the random world of `r₂`. -/

omit [Fintype X] [DecidableEq X] in
/-- The `Diff` subtraction-annotation evaluates to `false` at `v` iff the
data tuple is absent from the random world of the subtracted relation. -/
lemma diff_annotation_eq_false_iff
    (v : X → Bool) (r₂ : AnnotatedRelation T (BoolFunc X) n) (u : Tuple T n) :
    ((((groupByKey r₂).val.find?
        (fun q : Tuple T n × BoolFunc X => q.1 = u)).map Prod.snd).getD 0 : BoolFunc X) v = false
      ↔ u ∉ randomWorld v r₂ := by
  -- Bridge: u ∉ rw v r₂ iff no annotated tuple p ∈ r₂ with p.fst = u has p.snd v = true.
  have hnotin_iff : u ∉ randomWorld v r₂
      ↔ ∀ p : AnnotatedTuple T (BoolFunc X) n, p ∈ r₂
          → ¬ (p.fst = u ∧ p.snd v = true) := by
    unfold randomWorld
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
  cases h_find : (groupByKey r₂).val.find?
        (fun q : Tuple T n × BoolFunc X => q.1 = u) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [show (0 : BoolFunc X) v = false from rfl]
    rw [hnotin_iff]
    rw [List.find?_eq_none] at h_find
    refine ⟨?_, ?_⟩
    · intro _ p hp ⟨hfst, _⟩
      have hu_mem : u ∈ Multiset.map Prod.fst r₂ := by
        rw [Multiset.mem_map]; exact ⟨p, hp, hfst⟩
      obtain ⟨w, hw⟩ := (groupByKey_key_iff r₂ u).mpr hu_mem
      exact h_find _ hw (by simp)
    · intro _; rfl
  | some uw =>
    obtain ⟨u', w⟩ := uw
    have hu' : u' = u := by
      have := List.find?_some h_find; simp at this; exact this
    -- Substitute the find?-returned key with u everywhere.
    rw [hu'] at h_find
    have hw_in : (u, w) ∈ (groupByKey r₂).val := List.mem_of_find?_eq_some h_find
    have hw_val : w = (Multiset.map Prod.snd
          (Multiset.filter (fun q : AnnotatedTuple T (BoolFunc X) n ↦ q.fst = u) r₂)).sum :=
      groupByKey_value r₂ u w hw_in
    show (((Option.map Prod.snd _).getD 0) : BoolFunc X) v = false ↔ u ∉ randomWorld v r₂
    rw [hu', Option.map_some, Option.getD_some]
    -- The `(u, ...).2` projects to the sum; reduce, then apply
    -- `boolFunc_multiset_sum_apply`.
    show w v = false ↔ u ∉ randomWorld v r₂
    rw [hw_val, boolFunc_multiset_sum_apply, hnotin_iff]
    refine ⟨?_, ?_⟩
    · intro hw_v p hp ⟨hfst, hsnd⟩
      have htrue_in : true ∈ Multiset.map (fun f : BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : AnnotatedTuple T (BoolFunc X) n => q.fst = u) r₂)) := by
        rw [Multiset.mem_map]
        refine ⟨p.snd, ?_, hsnd⟩
        rw [Multiset.mem_map]
        refine ⟨p, ?_, rfl⟩
        rw [Multiset.mem_filter]; exact ⟨hp, hfst⟩
      have hsum : (Multiset.map (fun f : BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : AnnotatedTuple T (BoolFunc X) n => q.fst = u) r₂))).sum = true := by
        rw [bool_multiset_sum_eq_true]
        exact ⟨true, htrue_in, rfl⟩
      rw [hsum] at hw_v
      exact Bool.false_ne_true hw_v.symm
    · intro hall
      have hall_false : ∀ b ∈ Multiset.map (fun f : BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : AnnotatedTuple T (BoolFunc X) n => q.fst = u) r₂)),
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
      have hne_true : (Multiset.map (fun f : BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : AnnotatedTuple T (BoolFunc X) n => q.fst = u) r₂))).sum ≠ true := by
        intro h
        rw [bool_multiset_sum_eq_true] at h
        obtain ⟨b, hb_in, hb_true⟩ := h
        rw [hall_false b hb_in] at hb_true
        exact Bool.false_ne_true hb_true
      cases h : (Multiset.map (fun f : BoolFunc X => f v)
          (Multiset.map Prod.snd (Multiset.filter
            (fun q : AnnotatedTuple T (BoolFunc X) n => q.fst = u) r₂))).sum
      · rfl
      · exact absurd h hne_true

/-! ### The structural commutation theorem

Random-world projection commutes with annotated query evaluation: for any
non-aggregation query `q`, taking the random world `v` of the annotated
result is the same as evaluating `q` on the random-world database. The proof
is a structural induction, with the `Prod`, `Dedup`, and `Diff` cases still
to be discharged. -/

variable {K : Type} [SemiringWithMonus K] [DecidableEq K]

theorem randomWorld_evaluateAnnotated :
    ∀ {n} (q : Query T n) (hq : q.noAgg)
      (Î : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool),
    randomWorld v (q.evaluateAnnotated hq Î) = q.evaluate (Î.randomWorld v) := by
  intro n q
  induction q with
  | Rel n s =>
    intro hq Î v
    simp only [Query.evaluateAnnotated, Query.evaluate]
    rw [AnnotatedDatabase.find_randomWorld]
    cases hf : Î.find n s
    · rfl
    · simp
  | Proj ts q' ih =>
    intro hq Î v
    simp only [Query.evaluateAnnotated, Query.evaluate]
    rw [← randomWorld_map_data v (fun u : Tuple T _ => fun k => (ts k).eval u),
        ih (Query.noAggProj hq rfl) Î v]
  | Sel φ q' ih =>
    intro hq Î v
    simp only [Query.evaluateAnnotated, Query.evaluate]
    rw [← ih (Query.noAggSel hq rfl) Î v]
    generalize q'.evaluateAnnotated (Query.noAggSel hq rfl) Î = r
    -- Goal: `randomWorld v (filter_Lex r) = filter φ.eval (randomWorld v r)`.
    -- `randomWorld_filter_data` gives the same equation with a different
    -- `DecidablePred` instance on the inner filter; bridge via
    -- `Subsingleton.elim` (`Decidable` is subsingleton-extensional).
    have h := (randomWorld_filter_data v φ.eval r).symm
    have hinst : (fun a : AnnotatedTuple T (BoolFunc X) _ => φ.evalDecidable a.fst)
                  = φ.evalDecidableAnnotated := Subsingleton.elim _ _
    rw [hinst] at h
    exact h
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq Î v
    simp only [Query.evaluateAnnotated, Query.evaluate]
    rw [randomWorld_add, ih₁ (Query.noAggSum hq rfl).left Î v,
        ih₂ (Query.noAggSum hq rfl).right Î v]
    rfl
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    intro _ _ _; sorry
  | Dedup q' ih =>
    intro hq Î v
    simp only [Query.evaluateAnnotated, Query.evaluate]
    rw [← ih (Query.noAggDedup hq rfl) Î v]
    set r := q'.evaluateAnnotated (Query.noAggDedup hq rfl) Î with hr
    -- Both sides are `Nodup` multisets of `Tuple T n`. We show element
    -- equivalence: t ∈ LHS ↔ ∃ (t', α') ∈ r with t' = t and α' v = true ↔ t ∈ RHS.
    have hgbk_nodup : (Multiset.ofList (groupByKey r).val :
        Multiset (Tuple T _ × BoolFunc X)).Nodup := by
      rw [Multiset.coe_nodup]
      exact KeyValueList.nodup _ (groupByKey r).property
    have hLNodup : (randomWorld v (Multiset.ofList (groupByKey r).val)).Nodup := by
      show (Multiset.map Prod.fst _).Nodup
      apply Multiset.Nodup.map_on
      · -- Local injectivity: same-key entries of `groupByKey` agree.
        intro p hp q hq hpq
        rw [Multiset.mem_filter] at hp hq
        have hp_list : p ∈ (groupByKey r).val := Multiset.mem_coe.mp hp.1
        have hq_list : q ∈ (groupByKey r).val := Multiset.mem_coe.mp hq.1
        have hsnd := KeyValueList.functional _ (groupByKey r).property
          p hp_list q hq_list hpq
        exact Prod.ext hpq hsnd
      · exact Multiset.Nodup.filter _ hgbk_nodup
    have hRNodup : (Multiset.dedup (randomWorld v r)).Nodup := Multiset.nodup_dedup _
    rw [Multiset.Nodup.ext hLNodup hRNodup]
    intro t
    -- The membership condition on both sides reduces to:
    -- `∃ (t', α') ∈ r with t' = t and α' v = true`.
    constructor
    · rintro ht
      show t ∈ Multiset.dedup (randomWorld v r)
      rw [Multiset.mem_dedup]
      -- ht : t ∈ randomWorld v (ofList (groupByKey r).val)
      show t ∈ randomWorld v r
      unfold randomWorld at ht ⊢
      rw [Multiset.mem_map] at ht
      obtain ⟨p, hp, hpfst⟩ := ht
      rw [Multiset.mem_filter] at hp
      obtain ⟨hp_in, hp_snd⟩ := hp
      have hp_list : p ∈ (groupByKey r).val := Multiset.mem_coe.mp hp_in
      -- (p.fst, p.snd) ∈ (groupByKey r).val so groupByKey_value applies.
      have hp_val : p.snd = (Multiset.map Prod.snd
            (Multiset.filter (fun q : AnnotatedTuple T (BoolFunc X) _ ↦ q.fst = p.fst) r)).sum :=
        groupByKey_value r p.fst p.snd hp_list
      rw [hp_val, boolFunc_multiset_sum_apply, bool_multiset_sum_eq_true] at hp_snd
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
      show t ∈ randomWorld v (Multiset.ofList (groupByKey r).val)
      unfold randomWorld at ht ⊢
      rw [Multiset.mem_map] at ht
      obtain ⟨α_pair, hα_in, hα_fst⟩ := ht
      rw [Multiset.mem_filter] at hα_in
      obtain ⟨hα_r, hα_v⟩ := hα_in
      -- α_pair ∈ r with α_pair.fst = t and α_pair.snd v = true
      have hmem_map : t ∈ Multiset.map Prod.fst r := by
        rw [Multiset.mem_map]; exact ⟨α_pair, hα_r, hα_fst⟩
      obtain ⟨w, hw_in⟩ := (groupByKey_key_iff r t).mpr hmem_map
      have hw_val : w = (Multiset.map Prod.snd
            (Multiset.filter (fun q : AnnotatedTuple T (BoolFunc X) _ ↦ q.fst = t) r)).sum :=
        groupByKey_value r t w hw_in
      have hw_v_true : w v = true := by
        rw [hw_val, boolFunc_multiset_sum_apply, bool_multiset_sum_eq_true]
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
    simp only [Query.evaluateAnnotated, Query.evaluate]
    rw [← ih₁ (Query.noAggDiff hq rfl).left Î v,
        ← ih₂ (Query.noAggDiff hq rfl).right Î v]
    set r₁ := q₁.evaluateAnnotated (Query.noAggDiff hq rfl).left Î with hr₁
    set r₂ := q₂.evaluateAnnotated (Query.noAggDiff hq rfl).right Î with hr₂
    -- Local helper: random-world of a cons splits via if-then-else.
    -- Stated in the bare-Multiset form (the unfolded `randomWorld`) so the
    -- pattern matches the goal's Lex-coerced filter+map term.
    have hrw_cons : ∀ {k : ℕ} (a : Tuple T k × BoolFunc X)
        (t : Multiset (Tuple T k × BoolFunc X)),
        Multiset.map Prod.fst
            (Multiset.filter (fun p : Tuple T k × BoolFunc X => p.snd v = true) (a ::ₘ t))
          = if a.snd v = true then
              a.fst ::ₘ Multiset.map Prod.fst
                  (Multiset.filter (fun p : Tuple T k × BoolFunc X => p.snd v = true) t)
            else Multiset.map Prod.fst
                  (Multiset.filter (fun p : Tuple T k × BoolFunc X => p.snd v = true) t) := by
      intro k a t
      by_cases ha : a.snd v = true
      · rw [Multiset.filter_cons_of_pos
              (p := fun p : Tuple T k × BoolFunc X => p.snd v = true) _ ha,
            Multiset.map_cons]
        simp [ha]
      · rw [Multiset.filter_cons_of_neg
              (p := fun p : Tuple T k × BoolFunc X => p.snd v = true) _ ha]
        simp [ha]
    -- Induct on r₁ at the Prod-type carrier. We must override `randomWorld`
    -- to accept `Multiset (Tuple T _ × BoolFunc X)` directly so the pattern
    -- in the recursive `hrw_cons` call matches the goal's coerced form.
    let r₁' : Multiset (Tuple T _ × BoolFunc X) := r₁
    show Multiset.map Prod.fst
          (Multiset.filter (fun p : Tuple T _ × BoolFunc X => p.snd v = true)
            (r₁'.map (fun p : Tuple T _ × BoolFunc X =>
              (p.fst, p.snd -
                (((groupByKey r₂).val.find? (fun q => q.1 = p.fst)).map Prod.snd).getD 0))))
        = Multiset.filter (fun t => t ∉ randomWorld v r₂)
            (Multiset.map Prod.fst
              (Multiset.filter (fun p : Tuple T _ × BoolFunc X => p.snd v = true) r₁'))
    induction r₁' using Multiset.induction_on with
    | empty => rfl
    | cons p s ih =>
      -- Set β to the diff annotation for `p.fst`. We define β AFTER
      -- `Multiset.map_cons` fires so the goal's term contains β by construction.
      rw [Multiset.map_cons]
      set β : BoolFunc X :=
          ((List.find? (fun q : Tuple T _ × BoolFunc X => decide (q.1 = p.fst))
            (groupByKey r₂).val).map Prod.snd).getD 0 with hβ_def
      have hβ_iff : β v = false ↔ p.fst ∉ randomWorld v r₂ :=
        diff_annotation_eq_false_iff v r₂ p.fst
      -- Pull cons through randomWorld on both LHS and RHS.
      rw [hrw_cons (a := (p.fst, p.snd - β))]
      conv_rhs => rw [hrw_cons (a := p) (t := s)]
      -- The cons-head's snd-at-v on the LHS reduces to `p.snd v && !(β v)`.
      have hlhs_eq : (p.fst, p.snd - β).snd v = (p.snd v && !(β v)) := rfl
      by_cases hpv : p.snd v = true
      · -- p.snd v = true. Case on β v.
        by_cases hbv : β v = false
        · -- β v = false ⇒ p.fst ∉ rw v r₂.
          have hp_notin : p.fst ∉ randomWorld v r₂ := hβ_iff.mp hbv
          have hcond_lhs : (p.snd - β) v = true := by
            rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv, hbv]; rfl
          rw [if_pos hcond_lhs, if_pos hpv, ih]
          rw [Multiset.filter_cons_of_pos
                (p := fun t : Tuple T _ => t ∉ randomWorld v r₂) _ hp_notin]
        · -- β v ≠ false, so β v = true; p.fst ∈ rw v r₂.
          have hbv_true : β v = true := by
            cases h : β v
            · exact absurd h hbv
            · rfl
          have hp_in : ¬ p.fst ∉ randomWorld v r₂ := by
            intro h; exact absurd (hβ_iff.mpr h) hbv
          have hcond_lhs : ¬ (p.snd - β) v = true := by
            rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv, hbv_true]
            simp
          rw [if_neg hcond_lhs, if_pos hpv, ih]
          rw [Multiset.filter_cons_of_neg
                (p := fun t : Tuple T _ => t ∉ randomWorld v r₂) _ hp_in]
      · -- p.snd v = false: cond on LHS reduces to `false`.
        have hpv_false : p.snd v = false := by
          cases h : p.snd v
          · rfl
          · exact absurd h hpv
        have hcond_lhs : ¬ (p.snd - β) v = true := by
          rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv_false]; simp
        rw [if_neg hcond_lhs, if_neg hpv]
        exact ih
  | Agg _ _ _ _ =>
    intro hq _ _
    exact False.elim (by simp [Query.noAgg] at hq)

namespace ProbAssignment

variable (P : ProbAssignment X)

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
theorem theorem_12
    (q : Query T n) (hq : q.noAgg)
    (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) :
    P.marginalProb q Î t
      = P.funcProb (tupleAnnotation (q.evaluateAnnotated hq Î) t) := by
  unfold marginalProb funcProb
  apply Finset.sum_congr rfl
  intro v _
  -- Both indicators are the same: t ∈ randomWorld v (⟪q⟫_Î) ↔ tupleAnnotation _ _ v
  have hcond :
      t ∈ q.evaluate (Î.randomWorld v)
        ↔ (tupleAnnotation (q.evaluateAnnotated hq Î) t) v = true := by
    rw [← randomWorld_evaluateAnnotated q hq Î v]
    exact (tupleAnnotation_apply_eq_true_iff _ _ _).symm
  by_cases h : (tupleAnnotation (q.evaluateAnnotated hq Î) t) v = true
  · simp [h, hcond.mpr h]
  · have hmem : ¬ t ∈ q.evaluate (Î.randomWorld v) :=
      fun hm => h (hcond.mp hm)
    have hf : (tupleAnnotation (q.evaluateAnnotated hq Î) t) v = false := by
      cases h' : (tupleAnnotation (q.evaluateAnnotated hq Î) t) v
      · rfl
      · exact absurd h' h
    simp [hmem, hf]

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

variable (P : ProbAssignment X)

/-- **Corollary 13** ([Sen, Maniu & Senellart][sen2026provsql], Section IV-D).
For any non-aggregation query `q`, any `BoolFunc X`-annotated database `Î`
and any tuple `t`, the marginal probability that `t` appears in the random
output of `q` equals the probability of the disjunctive annotation of `t`
in the result of evaluating the **plain rewritten query** `q̂` on the
composite-encoded database.

Combines `theorem_12` and `Query.rewriting_valid`. -/
theorem corollary_13 [HasAltLinearOrder (BoolFunc X)]
    (q : Query T n) (hq : q.noAgg)
    (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) :
    P.marginalProb q Î t
      = P.funcProb (tupleAnnotation
          (Multiset.map Tuple.fromComposite
            ((q.rewriting hq).evaluate Î.toComposite)) t) := by
  rw [P.theorem_12 q hq Î t,
      ← Query.rewriting_valid q hq Î,
      AnnotatedRelation.map_fromComposite_toComposite]

end ProbAssignment
