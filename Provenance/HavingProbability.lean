/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Union
import Provenance.Circuit
import Provenance.Probability
import Provenance.Semirings.BoolFunc

set_option linter.unusedSectionVars false

/-!
# Probability identities for HAVING aggregate comparisons under independence

This file formalises the algebraic identities for evaluating
`HAVING`-style aggregate comparisons when the contributors are
independent. Given a `B[X]`-instance in which each contributor
`i : ι` carries an annotation `α i : BoolFunc X` and the annotations
have pairwise disjoint variable supports (so the contributors are
*independent* Bernoullis with marginals `p i = P.funcProb (α i)`), we
give closed-form / recurrence expressions for the probability that the
aggregate-comparison atom holds on the contributors of a single group:

* **MAX / MIN factorisation**
  (`funcProb_maxLeOnNonempty`, `funcProb_minGeOnNonempty`):
  `Pr[max ≤ C on nonempty] = (∏_{t i > C}(1 - p i)) · (1 - ∏_{t i ≤ C}(1 - p i))`
  and the dual for `min`.
* **COUNT (Poisson-binomial) recurrence**
  (`countMass_insert_succ`, `countMass_insert_zero`):
  `ρ_{J ⊔ {i}}(j+1) = (1 - p i) · ρ_J(j+1) + p i · ρ_J(j)`,
  `ρ_{J ⊔ {i}}(0) = (1 - p i) · ρ_J(0)`.
* **SUM (weighted Poisson-binomial) recurrence**
  (`sumMass_insert`):
  `σ_{J ⊔ {i}}(s) = (1 - p i) · σ_J(s) + p i · σ_J(s - t i)`
  (with the convention that `σ_J` at a negative-shifted index is `0`).

All four results follow the same template: the underlying event factors
as a Boolean combination of the per-contributor indicators, and the
disjoint-supports hypothesis turns that combination into a product of
marginal probabilities via `ProbAssignment.funcProb_mul_disjoint`.
-/

namespace BoolFunc

variable {X : Type}

/-- The constant `0` Boolean function depends on the empty support
(equivalently on any support). -/
lemma DependsOn.zero {S : Finset X} : (0 : BoolFunc X).DependsOn S :=
  fun _ _ _ => rfl

/-- The constant `1` Boolean function depends on the empty support
(equivalently on any support). -/
lemma DependsOn.one {S : Finset X} : (1 : BoolFunc X).DependsOn S :=
  fun _ _ _ => rfl

/-- A variable depends on the singleton of its index. -/
lemma DependsOn.var [DecidableEq X] (i : X) :
    (BoolFunc.var i).DependsOn ({i} : Finset X) := by
  intro v₁ v₂ hv
  have hi : i ∈ ({i} : Finset X) := Finset.mem_singleton.mpr rfl
  show v₁ i = v₂ i
  exact hv i hi

/-- `f * g` depends on `S ∪ T` whenever `f` depends on `S` and `g` on `T`.
Multiplication in `BoolFunc X` is pointwise `&&`. -/
lemma DependsOn.mul [DecidableEq X] {f g : BoolFunc X} {S T : Finset X}
    (hf : f.DependsOn S) (hg : g.DependsOn T) :
    (f * g).DependsOn (S ∪ T : Finset X) := by
  intro v₁ v₂ hv
  show (f v₁ && g v₁) = (f v₂ && g v₂)
  rw [hf v₁ v₂ (fun x hx => hv x (Finset.mem_union_left T hx)),
      hg v₁ v₂ (fun x hx => hv x (Finset.mem_union_right S hx))]

/-- `f + g` depends on `S ∪ T`. Addition in `BoolFunc X` is pointwise `||`. -/
lemma DependsOn.add [DecidableEq X] {f g : BoolFunc X} {S T : Finset X}
    (hf : f.DependsOn S) (hg : g.DependsOn T) :
    (f + g).DependsOn (S ∪ T : Finset X) := by
  intro v₁ v₂ hv
  show (f v₁ || g v₁) = (f v₂ || g v₂)
  rw [hf v₁ v₂ (fun x hx => hv x (Finset.mem_union_left T hx)),
      hg v₁ v₂ (fun x hx => hv x (Finset.mem_union_right S hx))]

/-- `1 - f` depends on the same support as `f`. Subtraction here is pointwise
`(1 v) && !(f v) = !(f v)`. -/
lemma DependsOn.one_sub {f : BoolFunc X} {S : Finset X}
    (hf : f.DependsOn S) : (1 - f).DependsOn S := by
  intro v₁ v₂ hv
  show ((1 : BoolFunc X) v₁ && !(f v₁)) = ((1 : BoolFunc X) v₂ && !(f v₂))
  rw [hf v₁ v₂ hv]
  rfl

/-- Enlarging the support preserves `DependsOn`. -/
lemma DependsOn.mono {f : BoolFunc X} {S T : Finset X}
    (hf : f.DependsOn S) (hST : S ⊆ T) : f.DependsOn T :=
  fun v₁ v₂ hv => hf v₁ v₂ (fun x hx => hv x (hST hx))

/-- `Finset.prod` of `BoolFunc`s depends on the `biUnion` of the per-factor
supports. -/
lemma DependsOn.prod [DecidableEq X] {ι : Type} [DecidableEq ι]
    {β : ι → BoolFunc X} {S : ι → Finset X}
    (h : ∀ i, (β i).DependsOn (S i)) (J : Finset ι) :
    (∏ i ∈ J, β i).DependsOn (J.biUnion S) := by
  classical
  induction J using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact DependsOn.one
  | insert i J hi ih =>
    rw [Finset.prod_insert hi, Finset.biUnion_insert]
    exact (h i).mul ih

end BoolFunc

namespace ProbAssignment

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Iterated independence: if `(β i)` depends on `S i` and the supports are
pairwise disjoint, then the probability of `∏ i ∈ J, β i` factors as the
product of the marginal probabilities `P.funcProb (β i)`. -/
theorem funcProb_prod_disjoint (P : ProbAssignment X)
    {ι : Type} [DecidableEq ι]
    (β : ι → BoolFunc X) (S : ι → Finset X)
    (hdep : ∀ i, (β i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))
    (J : Finset ι) :
    P.funcProb (∏ i ∈ J, β i) = ∏ i ∈ J, P.funcProb (β i) := by
  classical
  induction J using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, P.funcProb_one]
  | insert i J hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hprod : (∏ j ∈ J, β j).DependsOn (J.biUnion S) :=
      BoolFunc.DependsOn.prod hdep J
    have hdisj_si : Disjoint (S i) (J.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj (Set.mem_univ i) (Set.mem_univ j) (fun heq => hi (heq ▸ hj))
    rw [P.funcProb_mul_disjoint (hdep i) hprod hdisj_si, ih]

end ProbAssignment

/-! ## Common setup for the four results

We fix a probability assignment `P` over Boolean variables `X`, a finite
type `ι` of contributors, an annotation `α : ι → BoolFunc X`, supports
`S : ι → Finset X` that are pairwise disjoint, and a hypothesis
`hdep : ∀ i, (α i).DependsOn (S i)`. The contributor marginal is
`p i := P.funcProb (α i)`. -/

namespace HavingProbability

open BoolFunc

variable {X : Type} [Fintype X] [DecidableEq X]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (P : ProbAssignment X) (α : ι → BoolFunc X)

/-- Pointwise evaluation of a Finset product of `BoolFunc`s: the product
evaluates to `true` iff every factor does. -/
lemma prod_eval_eq_true_iff {ι : Type} [DecidableEq ι]
    (J : Finset ι) (β : ι → BoolFunc X) (v : X → Bool) :
    (∏ i ∈ J, β i) v = true ↔ ∀ i ∈ J, β i v = true := by
  classical
  induction J using Finset.induction with
  | empty =>
    constructor
    · intro _ i hi
      exact absurd hi (Finset.notMem_empty i)
    · intro _
      show (1 : BoolFunc X) v = true
      rfl
  | insert i J hi ih =>
    rw [Finset.prod_insert hi]
    show (β i v && (∏ j ∈ J, β j) v) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Finset.mem_insert.mp hk with rfl | hkJ
      · exact h1
      · exact h2 k hkJ
    · intro h
      refine ⟨h i (Finset.mem_insert_self i J), ?_⟩
      intro k hk
      exact h k (Finset.mem_insert_of_mem hk)

/-! ## MAX factorisation -/

section MaxMin

variable {V : Type} [LinearOrder V]
variable (t : ι → V)

/-- "Random world contains no contributor with value > C": the AND over the
indicators `1 - α i` for all contributors with `t i > C`. Evaluates to `true`
iff every such contributor's annotation is `false`. -/
def maxNoneAbove (C : V) : BoolFunc X :=
  ∏ i ∈ Finset.univ.filter (fun i => C < t i), (1 - α i)

/-- "Random world contains some contributor with value ≤ C": the OR over
the indicators `α i` for all contributors with `t i ≤ C`, expressed as
`1 - ∏ (1 - α i)`. -/
def someAtMost (C : V) : BoolFunc X :=
  1 - ∏ i ∈ Finset.univ.filter (fun i => t i ≤ C), (1 - α i)

/-- "Random world is nonempty and `max_{i ∈ world} t i ≤ C`": the conjunction
of the two pieces above. The semantic meaning is recorded in
`maxLeOnNonempty_eval_iff`. -/
def maxLeOnNonempty (C : V) : BoolFunc X :=
  maxNoneAbove α t C * someAtMost α t C

/-- Semantic reading of `maxNoneAbove`. -/
lemma maxNoneAbove_eval_iff (C : V) (v : X → Bool) :
    (maxNoneAbove α t C) v = true ↔ ∀ i, α i v = true → t i ≤ C := by
  unfold maxNoneAbove
  rw [prod_eval_eq_true_iff]
  constructor
  · intro h i hi
    by_contra hlt
    have hCi : C < t i := lt_of_not_ge hlt
    have hmem : i ∈ Finset.univ.filter (fun i => C < t i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hCi⟩
    have h1 : (1 - α i) v = true := h i hmem
    have h1' : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      simp [hi]
    exact Bool.false_ne_true (h1' ▸ h1)
  · intro h i hi
    have hi' : C < t i := (Finset.mem_filter.mp hi).2
    show ((1 : BoolFunc X) v && !(α i v)) = true
    have h1v : (1 : BoolFunc X) v = true := rfl
    rw [h1v, Bool.true_and]
    by_cases hav : α i v = true
    · exfalso
      exact absurd hi' (not_lt.mpr (h i hav))
    · have hf : α i v = false := by cases h : α i v; rfl; exact absurd h hav
      rw [hf]; rfl

/-- Semantic reading of `someAtMost`. -/
lemma someAtMost_eval_iff (C : V) (v : X → Bool) :
    (someAtMost α t C) v = true ↔ ∃ i, t i ≤ C ∧ α i v = true := by
  unfold someAtMost
  show ((1 : BoolFunc X) v && !((∏ i ∈ _, (1 - α i)) v)) = true ↔ _
  have h1v : (1 : BoolFunc X) v = true := rfl
  rw [h1v, Bool.true_and]
  -- Goal: !((∏ ...) v) = true ↔ ∃ i, t i ≤ C ∧ α i v = true
  constructor
  · -- !(p v) = true means p v ≠ true, i.e. p v = false. So some factor is false,
    -- i.e. some `(1 - α i) v = false`, i.e. some `α i v = true`.
    intro hnot
    have hp_false : (∏ i ∈ Finset.univ.filter (fun i => t i ≤ C), (1 - α i)) v = false := by
      cases hp : (∏ i ∈ Finset.univ.filter (fun i => t i ≤ C), (1 - α i)) v with
      | true => rw [hp] at hnot; exact absurd hnot (by decide)
      | false => rfl
    by_contra hne
    push Not at hne
    have hall : ∀ i ∈ Finset.univ.filter (fun i => t i ≤ C),
        (1 - α i) v = true := by
      intro i hi
      have hi' : t i ≤ C := (Finset.mem_filter.mp hi).2
      have hαi : α i v = false := by
        cases h : α i v with
        | true => exact absurd h (hne i hi')
        | false => rfl
      show ((1 : BoolFunc X) v && !(α i v)) = true
      rw [h1v, Bool.true_and, hαi]; rfl
    rw [(prod_eval_eq_true_iff _ _ _).mpr hall] at hp_false
    exact absurd hp_false (by decide)
  · rintro ⟨i, hi, hαi⟩
    have hne : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      rw [h1v, Bool.true_and, hαi]; rfl
    have hp_false : (∏ j ∈ Finset.univ.filter (fun i => t i ≤ C), (1 - α j)) v = false := by
      by_contra hp
      have hp_true :
          (∏ j ∈ Finset.univ.filter (fun i => t i ≤ C), (1 - α j)) v = true := by
        cases h : (∏ j ∈ Finset.univ.filter (fun i => t i ≤ C), (1 - α j)) v with
        | true => rfl
        | false => exact absurd h hp
      have hall := (prod_eval_eq_true_iff _ _ _).mp hp_true
      have hmem : i ∈ Finset.univ.filter (fun i => t i ≤ C) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hall i hmem] at hne
      exact absurd hne (by decide)
    rw [hp_false]; rfl

/-- Full semantic reading: the BoolFunc `maxLeOnNonempty α t C` evaluates to
`true` at `v` iff the random world `{i : α i v = true}` is nonempty and its
maximum-of-`t` is at most `C`. -/
theorem maxLeOnNonempty_eval_iff (C : V) (v : X → Bool) :
    (maxLeOnNonempty α t C) v = true ↔
      (∃ i, α i v = true) ∧ ∀ i, α i v = true → t i ≤ C := by
  unfold maxLeOnNonempty
  show ((maxNoneAbove α t C) v && (someAtMost α t C) v) = true ↔ _
  rw [Bool.and_eq_true, maxNoneAbove_eval_iff, someAtMost_eval_iff]
  constructor
  · rintro ⟨hall, ⟨i, _, hαi⟩⟩
    exact ⟨⟨i, hαi⟩, hall⟩
  · rintro ⟨⟨i, hαi⟩, hall⟩
    exact ⟨hall, i, hall i hαi, hαi⟩

/-- Probability of `maxNoneAbove`: by iterated independence applied to
`(1 - α i)`'s, this is the product of `(1 - p i)` over contributors above `C`. -/
lemma funcProb_maxNoneAbove (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) (C : V) :
    P.funcProb (maxNoneAbove α t C) =
      ∏ i ∈ Finset.univ.filter (fun i => C < t i),
        (1 - P.funcProb (α i)) := by
  unfold maxNoneAbove
  rw [P.funcProb_prod_disjoint (fun i => 1 - α i) S
        (fun i => (hdep i).one_sub) hdisj]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact P.funcProb_sub_self_const_one (α i)

/-- Probability of `someAtMost`: the complement of the product. -/
lemma funcProb_someAtMost (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) (C : V) :
    P.funcProb (someAtMost α t C) =
      1 - ∏ i ∈ Finset.univ.filter (fun i => t i ≤ C),
        (1 - P.funcProb (α i)) := by
  unfold someAtMost
  rw [P.funcProb_sub_self_const_one,
      P.funcProb_prod_disjoint (fun i => 1 - α i) S
        (fun i => (hdep i).one_sub) hdisj]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  exact P.funcProb_sub_self_const_one (α i)

/-- **MAX factorisation under independence.** The probability of the
"`max ≤ C` on a nonempty world" event factors as a product of an "all
above-`C` contributors are absent" term and a "some at-most-`C` contributor
is present" term. -/
theorem funcProb_maxLeOnNonempty (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) (C : V) :
    P.funcProb (maxLeOnNonempty α t C) =
      (∏ i ∈ Finset.univ.filter (fun i => C < t i),
          (1 - P.funcProb (α i)))
        * (1 - ∏ i ∈ Finset.univ.filter (fun i => t i ≤ C),
            (1 - P.funcProb (α i))) := by
  unfold maxLeOnNonempty
  have h_above : (maxNoneAbove α t C).DependsOn
      ((Finset.univ.filter (fun i => C < t i)).biUnion S) := by
    unfold maxNoneAbove
    exact BoolFunc.DependsOn.prod (fun i => (hdep i).one_sub) _
  have h_below : (someAtMost α t C).DependsOn
      ((Finset.univ.filter (fun i => t i ≤ C)).biUnion S) := by
    unfold someAtMost
    exact (BoolFunc.DependsOn.prod (fun i => (hdep i).one_sub) _).one_sub
  have h_disj :
      Disjoint ((Finset.univ.filter (fun i => C < t i)).biUnion S)
               ((Finset.univ.filter (fun i => t i ≤ C)).biUnion S) := by
    rw [Finset.disjoint_biUnion_left]
    intro i hi
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    have hi' : C < t i := (Finset.mem_filter.mp hi).2
    have hj' : t j ≤ C := (Finset.mem_filter.mp hj).2
    have hij : i ≠ j := by
      intro heq
      rw [heq] at hi'
      exact absurd hi' (not_lt.mpr hj')
    exact hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  rw [P.funcProb_mul_disjoint h_above h_below h_disj,
      funcProb_maxNoneAbove P α t S hdep hdisj C,
      funcProb_someAtMost P α t S hdep hdisj C]

/-! ## MIN factorisation -/

/-- "Random world contains no contributor with value < C": the AND over the
indicators `1 - α i` for all contributors with `t i < C`. -/
def minNoneBelow (C : V) : BoolFunc X :=
  ∏ i ∈ Finset.univ.filter (fun i => t i < C), (1 - α i)

/-- "Random world contains some contributor with value ≥ C". -/
def someAtLeast (C : V) : BoolFunc X :=
  1 - ∏ i ∈ Finset.univ.filter (fun i => C ≤ t i), (1 - α i)

/-- "Random world is nonempty and `min_{i ∈ world} t i ≥ C`". -/
def minGeOnNonempty (C : V) : BoolFunc X :=
  minNoneBelow α t C * someAtLeast α t C

lemma minNoneBelow_eval_iff (C : V) (v : X → Bool) :
    (minNoneBelow α t C) v = true ↔ ∀ i, α i v = true → C ≤ t i := by
  unfold minNoneBelow
  rw [prod_eval_eq_true_iff]
  constructor
  · intro h i hi
    by_contra hlt
    have hCi : t i < C := lt_of_not_ge hlt
    have hmem : i ∈ Finset.univ.filter (fun i => t i < C) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hCi⟩
    have h1 : (1 - α i) v = true := h i hmem
    have h1' : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      simp [hi]
    exact Bool.false_ne_true (h1' ▸ h1)
  · intro h i hi
    have hi' : t i < C := (Finset.mem_filter.mp hi).2
    show ((1 : BoolFunc X) v && !(α i v)) = true
    have h1v : (1 : BoolFunc X) v = true := rfl
    rw [h1v, Bool.true_and]
    by_cases hav : α i v = true
    · exfalso
      exact absurd hi' (not_lt.mpr (h i hav))
    · have hf : α i v = false := by cases h : α i v; rfl; exact absurd h hav
      rw [hf]; rfl

lemma someAtLeast_eval_iff (C : V) (v : X → Bool) :
    (someAtLeast α t C) v = true ↔ ∃ i, C ≤ t i ∧ α i v = true := by
  unfold someAtLeast
  show ((1 : BoolFunc X) v && !((∏ i ∈ _, (1 - α i)) v)) = true ↔ _
  have h1v : (1 : BoolFunc X) v = true := rfl
  rw [h1v, Bool.true_and]
  constructor
  · intro hnot
    have hp_false : (∏ i ∈ Finset.univ.filter (fun i => C ≤ t i), (1 - α i)) v = false := by
      cases hp : (∏ i ∈ Finset.univ.filter (fun i => C ≤ t i), (1 - α i)) v with
      | true => rw [hp] at hnot; exact absurd hnot (by decide)
      | false => rfl
    by_contra hne
    push Not at hne
    have hall : ∀ i ∈ Finset.univ.filter (fun i => C ≤ t i),
        (1 - α i) v = true := by
      intro i hi
      have hi' : C ≤ t i := (Finset.mem_filter.mp hi).2
      have hαi : α i v = false := by
        cases h : α i v with
        | true => exact absurd h (hne i hi')
        | false => rfl
      show ((1 : BoolFunc X) v && !(α i v)) = true
      rw [h1v, Bool.true_and, hαi]; rfl
    rw [(prod_eval_eq_true_iff _ _ _).mpr hall] at hp_false
    exact absurd hp_false (by decide)
  · rintro ⟨i, hi, hαi⟩
    have hne : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      rw [h1v, Bool.true_and, hαi]; rfl
    have hp_false : (∏ j ∈ Finset.univ.filter (fun i => C ≤ t i), (1 - α j)) v = false := by
      by_contra hp
      have hp_true :
          (∏ j ∈ Finset.univ.filter (fun i => C ≤ t i), (1 - α j)) v = true := by
        cases h : (∏ j ∈ Finset.univ.filter (fun i => C ≤ t i), (1 - α j)) v with
        | true => rfl
        | false => exact absurd h hp
      have hall := (prod_eval_eq_true_iff _ _ _).mp hp_true
      have hmem : i ∈ Finset.univ.filter (fun i => C ≤ t i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hall i hmem] at hne
      exact absurd hne (by decide)
    rw [hp_false]; rfl

theorem minGeOnNonempty_eval_iff (C : V) (v : X → Bool) :
    (minGeOnNonempty α t C) v = true ↔
      (∃ i, α i v = true) ∧ ∀ i, α i v = true → C ≤ t i := by
  unfold minGeOnNonempty
  show ((minNoneBelow α t C) v && (someAtLeast α t C) v) = true ↔ _
  rw [Bool.and_eq_true, minNoneBelow_eval_iff, someAtLeast_eval_iff]
  constructor
  · rintro ⟨hall, ⟨i, _, hαi⟩⟩
    exact ⟨⟨i, hαi⟩, hall⟩
  · rintro ⟨⟨i, hαi⟩, hall⟩
    exact ⟨hall, i, hall i hαi, hαi⟩

lemma funcProb_minNoneBelow (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) (C : V) :
    P.funcProb (minNoneBelow α t C) =
      ∏ i ∈ Finset.univ.filter (fun i => t i < C),
        (1 - P.funcProb (α i)) := by
  unfold minNoneBelow
  rw [P.funcProb_prod_disjoint (fun i => 1 - α i) S
        (fun i => (hdep i).one_sub) hdisj]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact P.funcProb_sub_self_const_one (α i)

lemma funcProb_someAtLeast (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) (C : V) :
    P.funcProb (someAtLeast α t C) =
      1 - ∏ i ∈ Finset.univ.filter (fun i => C ≤ t i),
        (1 - P.funcProb (α i)) := by
  unfold someAtLeast
  rw [P.funcProb_sub_self_const_one,
      P.funcProb_prod_disjoint (fun i => 1 - α i) S
        (fun i => (hdep i).one_sub) hdisj]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  exact P.funcProb_sub_self_const_one (α i)

/-- **MIN factorisation under independence.** -/
theorem funcProb_minGeOnNonempty (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) (C : V) :
    P.funcProb (minGeOnNonempty α t C) =
      (∏ i ∈ Finset.univ.filter (fun i => t i < C),
          (1 - P.funcProb (α i)))
        * (1 - ∏ i ∈ Finset.univ.filter (fun i => C ≤ t i),
            (1 - P.funcProb (α i))) := by
  unfold minGeOnNonempty
  have h_below : (minNoneBelow α t C).DependsOn
      ((Finset.univ.filter (fun i => t i < C)).biUnion S) := by
    unfold minNoneBelow
    exact BoolFunc.DependsOn.prod (fun i => (hdep i).one_sub) _
  have h_above : (someAtLeast α t C).DependsOn
      ((Finset.univ.filter (fun i => C ≤ t i)).biUnion S) := by
    unfold someAtLeast
    exact (BoolFunc.DependsOn.prod (fun i => (hdep i).one_sub) _).one_sub
  have h_disj :
      Disjoint ((Finset.univ.filter (fun i => t i < C)).biUnion S)
               ((Finset.univ.filter (fun i => C ≤ t i)).biUnion S) := by
    rw [Finset.disjoint_biUnion_left]
    intro i hi
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    have hi' : t i < C := (Finset.mem_filter.mp hi).2
    have hj' : C ≤ t j := (Finset.mem_filter.mp hj).2
    have hij : i ≠ j := by
      intro heq
      rw [heq] at hi'
      exact absurd hi' (not_lt.mpr hj')
    exact hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  rw [P.funcProb_mul_disjoint h_below h_above h_disj,
      funcProb_minNoneBelow P α t S hdep hdisj C,
      funcProb_someAtLeast P α t S hdep hdisj C]

end MaxMin

/-! ## COUNT (Poisson-binomial) recurrence -/

section Count

/-- Indicator BoolFunc: evaluates to `true` at a valuation `v` iff exactly
`j` of the indices `i ∈ J` have `α i v = true`. -/
def countEqIndicator (J : Finset ι) (j : ℕ) : BoolFunc X :=
  fun v => decide ((J.filter (fun i => α i v = true)).card = j)

/-- `countEqIndicator α J j` depends on `⋃ i ∈ J, S i`: its value at `v`
only references `α i v` for `i ∈ J`. -/
lemma countEqIndicator_dependsOn (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i)) (J : Finset ι) (j : ℕ) :
    (countEqIndicator α J j).DependsOn (J.biUnion S) := by
  intro v₁ v₂ hv
  show (decide ((J.filter (fun i => α i v₁ = true)).card = j) : Bool)
      = decide ((J.filter (fun i => α i v₂ = true)).card = j)
  have heq : J.filter (fun i => α i v₁ = true) = J.filter (fun i => α i v₂ = true) :=
    Finset.filter_congr (fun i hi => by
      have : α i v₁ = α i v₂ := hdep i v₁ v₂ (fun x hx =>
        hv x (Finset.mem_biUnion.mpr ⟨i, hi, hx⟩))
      rw [this])
  rw [heq]

/-- Decomposition for `j = 0`: at most `0` of the indices in `insert i J`
have `α k v = true` iff `α i v = false` and at most `0` of the indices in
`J` have `α k v = true`. -/
lemma countEqIndicator_insert_zero {i : ι} {J : Finset ι} (hi : i ∉ J) :
    countEqIndicator α (insert i J) 0
      = (1 - α i) * countEqIndicator α J 0 := by
  funext v
  show (decide (((insert i J).filter (fun k => α k v = true)).card = 0) : Bool)
      = ((1 - α i) v && decide ((J.filter (fun k => α k v = true)).card = 0))
  rw [Finset.filter_insert]
  by_cases h : α i v = true
  · rw [if_pos h]
    have hifJ : i ∉ J.filter (fun k => α k v = true) :=
      fun hin => hi (Finset.mem_filter.mp hin).1
    rw [Finset.card_insert_of_notMem hifJ]
    have h1sub : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h]; rfl
    rw [h1sub, Bool.false_and]
    -- Goal: decide ((J.filter ·).card + 1 = 0) = false
    have : (J.filter (fun k => α k v = true)).card + 1 ≠ 0 := Nat.succ_ne_zero _
    exact decide_eq_false this
  · have h' : α i v = false := by cases h' : α i v; rfl; exact absurd h' h
    rw [if_neg ?_]
    swap; · rw [h']; decide
    have h1sub : (1 - α i) v = true := by
      show ((1 : BoolFunc X) v && !(α i v)) = true
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h']; rfl
    rw [h1sub, Bool.true_and]

/-- Decomposition for `j = j' + 1`: exactly `j' + 1` indices in `insert i J`
have `α k v = true` iff either `α i v = true` and exactly `j'` indices in
`J` do, or `α i v = false` and exactly `j' + 1` indices in `J` do. -/
lemma countEqIndicator_insert_succ {i : ι} {J : Finset ι} (hi : i ∉ J) (j : ℕ) :
    countEqIndicator α (insert i J) (j + 1)
      = α i * countEqIndicator α J j
        + (1 - α i) * countEqIndicator α J (j + 1) := by
  funext v
  show (decide (((insert i J).filter (fun k => α k v = true)).card = j + 1) : Bool)
      = ((α i v && decide ((J.filter (fun k => α k v = true)).card = j))
          || ((1 - α i) v
              && decide ((J.filter (fun k => α k v = true)).card = j + 1)))
  rw [Finset.filter_insert]
  by_cases h : α i v = true
  · rw [if_pos h]
    have hifJ : i ∉ J.filter (fun k => α k v = true) :=
      fun hin => hi (Finset.mem_filter.mp hin).1
    rw [Finset.card_insert_of_notMem hifJ]
    have h1sub : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h]; rfl
    rw [h, h1sub, Bool.true_and, Bool.false_and, Bool.or_false]
    -- Goal: decide ((J.filter ·).card + 1 = j + 1) = decide ((J.filter ·).card = j)
    by_cases heq : (J.filter (fun k => α k v = true)).card = j
    · rw [decide_eq_true (by omega :
            (J.filter (fun k => α k v = true)).card + 1 = j + 1),
          decide_eq_true heq]
    · have h1 : (J.filter (fun k => α k v = true)).card + 1 ≠ j + 1 :=
        fun heq' => heq (Nat.succ_injective heq')
      rw [decide_eq_false h1, decide_eq_false heq]
  · have h' : α i v = false := by cases h' : α i v; rfl; exact absurd h' h
    rw [if_neg ?_]
    swap; · rw [h']; decide
    have h1sub : (1 - α i) v = true := by
      show ((1 : BoolFunc X) v && !(α i v)) = true
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h']; rfl
    rw [h', h1sub, Bool.false_and, Bool.true_and, Bool.false_or]

variable (S : ι → Finset X)

/-- **COUNT Poisson-binomial recurrence (succ case).** For `i ∉ J` and
`j : ℕ`, the probability that exactly `j + 1` of the contributors in
`insert i J` are present factors as `(1 − p i) · ρ_J(j+1) + p i · ρ_J(j)`. -/
theorem countMass_insert_succ
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))
    {i : ι} {J : Finset ι} (hi : i ∉ J) (j : ℕ) :
    P.funcProb (countEqIndicator α (insert i J) (j + 1)) =
      (1 - P.funcProb (α i)) * P.funcProb (countEqIndicator α J (j + 1))
      + P.funcProb (α i) * P.funcProb (countEqIndicator α J j) := by
  rw [countEqIndicator_insert_succ α hi j]
  have hSi_disjoint_J : Disjoint (S i) (J.biUnion S) := by
    rw [Finset.disjoint_biUnion_right]
    intro k hk
    exact hdisj (Set.mem_univ i) (Set.mem_univ k) (fun heq => hi (heq ▸ hk))
  have hcE_dep : ∀ j', (countEqIndicator α J j').DependsOn (J.biUnion S) :=
    fun j' => countEqIndicator_dependsOn α S hdep J j'
  -- Independence: Pr((α i) * cE) = p i * Pr(cE)
  have h_mul_succ : P.funcProb (α i * countEqIndicator α J j) =
      P.funcProb (α i) * P.funcProb (countEqIndicator α J j) :=
    P.funcProb_mul_disjoint (hdep i) (hcE_dep j) hSi_disjoint_J
  have h_mul_curr : P.funcProb ((1 - α i) * countEqIndicator α J (j + 1)) =
      P.funcProb (1 - α i) * P.funcProb (countEqIndicator α J (j + 1)) :=
    P.funcProb_mul_disjoint ((hdep i).one_sub) (hcE_dep (j + 1)) hSi_disjoint_J
  -- Sum decomposition: Pr(f + g) = Pr(f) + Pr(g) - Pr(f * g).
  -- f * g = (α i * cE_j) * ((1 - α i) * cE_{j+1}) involves α i * (1 - α i) = 0,
  -- so Pr(f * g) = Pr(0) = 0.
  have h_fg_zero : (α i * countEqIndicator α J j)
      * ((1 - α i) * countEqIndicator α J (j + 1)) = 0 := by
    calc (α i * countEqIndicator α J j) * ((1 - α i) * countEqIndicator α J (j + 1))
        = (α i * (1 - α i))
            * (countEqIndicator α J j * countEqIndicator α J (j + 1)) := by ring
      _ = 0 * (countEqIndicator α J j * countEqIndicator α J (j + 1)) := by
            rw [BoolFunc.mul_sub_self]
      _ = 0 := by ring
  have h_fg_pr : P.funcProb ((α i * countEqIndicator α J j)
      * ((1 - α i) * countEqIndicator α J (j + 1))) = 0 := by
    rw [h_fg_zero, P.funcProb_zero]
  rw [P.funcProb_add_eq, h_fg_pr, sub_zero, h_mul_succ, h_mul_curr,
      P.funcProb_sub_self_const_one]
  ring

/-- **COUNT Poisson-binomial recurrence (zero case).** For `i ∉ J`, the
probability that exactly `0` contributors in `insert i J` are present is
`(1 − p i) · ρ_J(0)`. -/
theorem countMass_insert_zero
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))
    {i : ι} {J : Finset ι} (hi : i ∉ J) :
    P.funcProb (countEqIndicator α (insert i J) 0) =
      (1 - P.funcProb (α i)) * P.funcProb (countEqIndicator α J 0) := by
  rw [countEqIndicator_insert_zero α hi]
  have hSi_disjoint_J : Disjoint (S i) (J.biUnion S) := by
    rw [Finset.disjoint_biUnion_right]
    intro k hk
    exact hdisj (Set.mem_univ i) (Set.mem_univ k) (fun heq => hi (heq ▸ hk))
  have hcE_dep : (countEqIndicator α J 0).DependsOn (J.biUnion S) :=
    countEqIndicator_dependsOn α S hdep J 0
  rw [P.funcProb_mul_disjoint ((hdep i).one_sub) hcE_dep hSi_disjoint_J,
      P.funcProb_sub_self_const_one]

end Count

/-! ## SUM (weighted Poisson-binomial) recurrence -/

section Sum

variable (t : ι → ℕ)

/-- Indicator BoolFunc: evaluates to `true` at a valuation `v` iff the
sum of `t i` over indices `i ∈ J` with `α i v = true` equals `s`. -/
def sumEqIndicator (J : Finset ι) (s : ℕ) : BoolFunc X :=
  fun v => decide ((J.filter (fun i => α i v = true)).sum t = s)

/-- Support lemma for `sumEqIndicator`. -/
lemma sumEqIndicator_dependsOn (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i)) (J : Finset ι) (s : ℕ) :
    (sumEqIndicator α t J s).DependsOn (J.biUnion S) := by
  intro v₁ v₂ hv
  show (decide ((J.filter (fun i => α i v₁ = true)).sum t = s) : Bool)
      = decide ((J.filter (fun i => α i v₂ = true)).sum t = s)
  have heq : J.filter (fun i => α i v₁ = true) = J.filter (fun i => α i v₂ = true) :=
    Finset.filter_congr (fun i hi => by
      have : α i v₁ = α i v₂ := hdep i v₁ v₂ (fun x hx =>
        hv x (Finset.mem_biUnion.mpr ⟨i, hi, hx⟩))
      rw [this])
  rw [heq]

/-- Decomposition when the new contributor's weight exceeds the target: if
`t i > s`, the sum cannot reach `s` once `i` is included, so the only way to
hit `s` is to leave `i` out. -/
lemma sumEqIndicator_insert_of_lt {i : ι} {J : Finset ι} (hi : i ∉ J)
    {s : ℕ} (hs : s < t i) :
    sumEqIndicator α t (insert i J) s
      = (1 - α i) * sumEqIndicator α t J s := by
  funext v
  show (decide (((insert i J).filter (fun k => α k v = true)).sum t = s) : Bool)
      = ((1 - α i) v && decide ((J.filter (fun k => α k v = true)).sum t = s))
  rw [Finset.filter_insert]
  by_cases h : α i v = true
  · rw [if_pos h]
    have hifJ : i ∉ J.filter (fun k => α k v = true) :=
      fun hin => hi (Finset.mem_filter.mp hin).1
    rw [Finset.sum_insert hifJ]
    have h1sub : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h]; rfl
    rw [h1sub, Bool.false_and]
    have hne : t i + (J.filter (fun k => α k v = true)).sum t ≠ s := by
      intro heq
      have : t i ≤ s := heq ▸ Nat.le_add_right _ _
      exact absurd this (not_le.mpr hs)
    exact decide_eq_false hne
  · have h' : α i v = false := by cases h' : α i v; rfl; exact absurd h' h
    rw [if_neg ?_]
    swap; · rw [h']; decide
    have h1sub : (1 - α i) v = true := by
      show ((1 : BoolFunc X) v && !(α i v)) = true
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h']; rfl
    rw [h1sub, Bool.true_and]

/-- Decomposition when the new contributor's weight fits: if `t i ≤ s`, the
target sum is reachable either without `i` (target stays `s`) or with `i`
(target becomes `s − t i` on the remaining contributors). -/
lemma sumEqIndicator_insert_of_le {i : ι} {J : Finset ι} (hi : i ∉ J)
    {s : ℕ} (hs : t i ≤ s) :
    sumEqIndicator α t (insert i J) s
      = α i * sumEqIndicator α t J (s - t i)
        + (1 - α i) * sumEqIndicator α t J s := by
  funext v
  show (decide (((insert i J).filter (fun k => α k v = true)).sum t = s) : Bool)
      = ((α i v && decide ((J.filter (fun k => α k v = true)).sum t = s - t i))
          || ((1 - α i) v
              && decide ((J.filter (fun k => α k v = true)).sum t = s)))
  rw [Finset.filter_insert]
  by_cases h : α i v = true
  · rw [if_pos h]
    have hifJ : i ∉ J.filter (fun k => α k v = true) :=
      fun hin => hi (Finset.mem_filter.mp hin).1
    rw [Finset.sum_insert hifJ]
    have h1sub : (1 - α i) v = false := by
      show ((1 : BoolFunc X) v && !(α i v)) = false
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h]; rfl
    rw [h, h1sub, Bool.true_and, Bool.false_and, Bool.or_false]
    -- Goal: decide (t i + (J.filter ·).sum t = s) = decide ((J.filter ·).sum t = s - t i)
    by_cases heq : (J.filter (fun k => α k v = true)).sum t = s - t i
    · rw [decide_eq_true (by omega :
            t i + (J.filter (fun k => α k v = true)).sum t = s),
          decide_eq_true heq]
    · have h1 : t i + (J.filter (fun k => α k v = true)).sum t ≠ s := by
        intro heq'
        apply heq
        omega
      rw [decide_eq_false h1, decide_eq_false heq]
  · have h' : α i v = false := by cases h' : α i v; rfl; exact absurd h' h
    rw [if_neg ?_]
    swap; · rw [h']; decide
    have h1sub : (1 - α i) v = true := by
      show ((1 : BoolFunc X) v && !(α i v)) = true
      have h1v : (1 : BoolFunc X) v = true := rfl
      rw [h1v, h']; rfl
    rw [h', h1sub, Bool.false_and, Bool.true_and, Bool.false_or]

variable (S : ι → Finset X)

/-- **SUM weighted Poisson-binomial recurrence (weight fits).** For `i ∉ J`
and `t i ≤ s`, the probability that the weighted sum over `insert i J`
equals `s` factors as `(1 − p i) · σ_J(s) + p i · σ_J(s − t i)`. -/
theorem sumMass_insert_of_le
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))
    {i : ι} {J : Finset ι} (hi : i ∉ J)
    {s : ℕ} (hs : t i ≤ s) :
    P.funcProb (sumEqIndicator α t (insert i J) s) =
      (1 - P.funcProb (α i)) * P.funcProb (sumEqIndicator α t J s)
      + P.funcProb (α i) * P.funcProb (sumEqIndicator α t J (s - t i)) := by
  rw [sumEqIndicator_insert_of_le α t hi hs]
  have hSi_disjoint_J : Disjoint (S i) (J.biUnion S) := by
    rw [Finset.disjoint_biUnion_right]
    intro k hk
    exact hdisj (Set.mem_univ i) (Set.mem_univ k) (fun heq => hi (heq ▸ hk))
  have hsE_dep : ∀ s', (sumEqIndicator α t J s').DependsOn (J.biUnion S) :=
    fun s' => sumEqIndicator_dependsOn α t S hdep J s'
  have h_mul_shifted : P.funcProb (α i * sumEqIndicator α t J (s - t i)) =
      P.funcProb (α i) * P.funcProb (sumEqIndicator α t J (s - t i)) :=
    P.funcProb_mul_disjoint (hdep i) (hsE_dep _) hSi_disjoint_J
  have h_mul_keep : P.funcProb ((1 - α i) * sumEqIndicator α t J s) =
      P.funcProb (1 - α i) * P.funcProb (sumEqIndicator α t J s) :=
    P.funcProb_mul_disjoint ((hdep i).one_sub) (hsE_dep s) hSi_disjoint_J
  have h_fg_zero : (α i * sumEqIndicator α t J (s - t i))
      * ((1 - α i) * sumEqIndicator α t J s) = 0 := by
    calc (α i * sumEqIndicator α t J (s - t i)) * ((1 - α i) * sumEqIndicator α t J s)
        = (α i * (1 - α i))
            * (sumEqIndicator α t J (s - t i) * sumEqIndicator α t J s) := by ring
      _ = 0 * (sumEqIndicator α t J (s - t i) * sumEqIndicator α t J s) := by
            rw [BoolFunc.mul_sub_self]
      _ = 0 := by ring
  have h_fg_pr : P.funcProb ((α i * sumEqIndicator α t J (s - t i))
      * ((1 - α i) * sumEqIndicator α t J s)) = 0 := by
    rw [h_fg_zero, P.funcProb_zero]
  rw [P.funcProb_add_eq, h_fg_pr, sub_zero, h_mul_shifted, h_mul_keep,
      P.funcProb_sub_self_const_one]
  ring

/-- **SUM weighted Poisson-binomial recurrence (weight too large).** For
`i ∉ J` and `s < t i`, the probability collapses to the keep-out branch:
`σ_{insert i J}(s) = (1 − p i) · σ_J(s)`. -/
theorem sumMass_insert_of_lt
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))
    {i : ι} {J : Finset ι} (hi : i ∉ J)
    {s : ℕ} (hs : s < t i) :
    P.funcProb (sumEqIndicator α t (insert i J) s) =
      (1 - P.funcProb (α i)) * P.funcProb (sumEqIndicator α t J s) := by
  rw [sumEqIndicator_insert_of_lt α t hi hs]
  have hSi_disjoint_J : Disjoint (S i) (J.biUnion S) := by
    rw [Finset.disjoint_biUnion_right]
    intro k hk
    exact hdisj (Set.mem_univ i) (Set.mem_univ k) (fun heq => hi (heq ▸ hk))
  have hsE_dep : (sumEqIndicator α t J s).DependsOn (J.biUnion S) :=
    sumEqIndicator_dependsOn α t S hdep J s
  rw [P.funcProb_mul_disjoint ((hdep i).one_sub) hsE_dep hSi_disjoint_J,
      P.funcProb_sub_self_const_one]

end Sum

end HavingProbability
