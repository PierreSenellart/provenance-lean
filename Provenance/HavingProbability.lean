/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Union
import Provenance.Circuit
import Provenance.HavingSemantics
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

/-- Additivity over pairwise-incompatible events: the probability of a
`⊕`-sum (pointwise OR) of Boolean functions whose pairwise products vanish
is the sum of the probabilities. -/
theorem funcProb_sum_incompatible (P : ProbAssignment X)
    {ι : Type} [DecidableEq ι]
    (β : ι → BoolFunc X) (J : Finset ι)
    (hpair : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → β i * β j = 0) :
    P.funcProb (∑ i ∈ J, β i) = ∑ i ∈ J, P.funcProb (β i) := by
  classical
  induction J using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, P.funcProb_zero]
  | insert i J hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hmulzero : β i * ∑ j ∈ J, β j = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      exact hpair i (Finset.mem_insert_self i J) j (Finset.mem_insert_of_mem hj)
        (fun heq => hi (heq ▸ hj))
    rw [P.funcProb_add_eq, hmulzero, P.funcProb_zero, sub_zero,
      ih fun a ha b hb hab => hpair a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_insert_of_mem hb) hab]

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

/-! ## The remaining MIN / MAX comparison operators

`funcProb_maxLeOnNonempty` and `funcProb_minGeOnNonempty` treat `MAX ≤ C`
and `MIN ≥ C`. The remaining comparisons all follow from two generic
events: `guardedSome r q` – "no present contributor satisfies `r`, and
some present contributor satisfies `q`" – and its unguarded special case
`someOf q`. Under the disjoint-supports hypothesis, their probabilities
factor exactly as before, and each remaining comparison is an instance:

* `MAX < C` – guard `r i := C ≤ t i`, witness `q i := t i < C`;
* `MAX = C` – guard `r i := C < t i`, witness `q i := t i = C`;
* `MAX ≥ C` / `MAX > C` – unguarded witness `q i := C ≤ t i` / `C < t i`
  (non-emptiness is implied by the witness);
* `MAX ≠ C` on non-empty worlds – the disjoint union of `MAX < C` and
  `MAX > C`, whose probabilities add;

and dually for `MIN`. -/

/-- Pointwise evaluation of `1 - f`: Boolean negation. -/
lemma one_sub_eval (f : BoolFunc X) (v : X → Bool) : (1 - f) v = !(f v) := rfl

section Guarded

variable (r q : ι → Prop) [DecidablePred r] [DecidablePred q]

/-- "No present contributor satisfies `r`": AND of the negated indicators
over the contributors satisfying `r`. -/
def noneOf : BoolFunc X :=
  ∏ i ∈ Finset.univ.filter r, (1 - α i)

/-- "Some present contributor satisfies `q`": OR of the indicators over the
contributors satisfying `q`, expressed as `1 - ∏ (1 - α i)`. -/
def someOf : BoolFunc X :=
  1 - ∏ i ∈ Finset.univ.filter q, (1 - α i)

/-- "No present contributor satisfies `r`, and some present contributor
satisfies `q`". Every `MIN`/`MAX` aggregate comparison on non-empty random
worlds is an instance of this event. -/
def guardedSome : BoolFunc X :=
  noneOf α r * someOf α q

/-- Semantic reading of `noneOf`. -/
lemma noneOf_eval_iff (v : X → Bool) :
    (noneOf α r) v = true ↔ ∀ i, r i → α i v = false := by
  unfold noneOf
  rw [prod_eval_eq_true_iff]
  constructor
  · intro h i hri
    have := h i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hri⟩)
    rwa [one_sub_eval, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  · intro h i hi
    rw [one_sub_eval, h i (Finset.mem_filter.mp hi).2]
    rfl

/-- Semantic reading of `someOf`. -/
lemma someOf_eval_iff (v : X → Bool) :
    (someOf α q) v = true ↔ ∃ i, q i ∧ α i v = true := by
  unfold someOf
  rw [one_sub_eval, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hall : ∀ i ∈ Finset.univ.filter q, (1 - α i) v = true := by
      intro i hi
      rw [one_sub_eval, Bool.not_eq_eq_eq_not, Bool.not_true]
      cases hα : α i v with
      | false => rfl
      | true => exact absurd hα (hne i (Finset.mem_filter.mp hi).2)
    rw [(prod_eval_eq_true_iff _ _ _).mpr hall] at h
    exact Bool.noConfusion h
  · rintro ⟨i, hqi, hαi⟩
    cases hp : (∏ i ∈ Finset.univ.filter q, (1 - α i)) v with
    | false => rfl
    | true =>
      have := (prod_eval_eq_true_iff _ _ _).mp hp i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hqi⟩)
      rw [one_sub_eval, hαi] at this
      exact Bool.noConfusion this

/-- Semantic reading of `guardedSome`. -/
lemma guardedSome_eval_iff (v : X → Bool) :
    (guardedSome α r q) v = true ↔
      (∀ i, r i → α i v = false) ∧ (∃ i, q i ∧ α i v = true) := by
  show ((noneOf α r) v && (someOf α q) v) = true ↔ _
  rw [Bool.and_eq_true, noneOf_eval_iff, someOf_eval_iff]

variable (S : ι → Finset X)

/-- Probability of `noneOf` under independence. -/
lemma funcProb_noneOf
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) :
    P.funcProb (noneOf α r) =
      ∏ i ∈ Finset.univ.filter r, (1 - P.funcProb (α i)) := by
  unfold noneOf
  rw [P.funcProb_prod_disjoint (fun i => 1 - α i) S
        (fun i => (hdep i).one_sub) hdisj]
  exact Finset.prod_congr rfl fun i _ => P.funcProb_sub_self_const_one (α i)

/-- Probability of `someOf` under independence. -/
lemma funcProb_someOf
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j))) :
    P.funcProb (someOf α q) =
      1 - ∏ i ∈ Finset.univ.filter q, (1 - P.funcProb (α i)) := by
  unfold someOf
  rw [P.funcProb_sub_self_const_one,
      P.funcProb_prod_disjoint (fun i => 1 - α i) S
        (fun i => (hdep i).one_sub) hdisj]
  congr 1
  exact Finset.prod_congr rfl fun i _ => P.funcProb_sub_self_const_one (α i)

/-- **Factorisation of `guardedSome` under independence.** When the guard
`r` and the witness `q` are mutually exclusive, the probability of
`guardedSome r q` is the product of an "every `r`-contributor is absent"
term and a "some `q`-contributor is present" term. -/
theorem funcProb_guardedSome
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))
    (hrq : ∀ i, r i → q i → False) :
    P.funcProb (guardedSome α r q) =
      (∏ i ∈ Finset.univ.filter r, (1 - P.funcProb (α i)))
        * (1 - ∏ i ∈ Finset.univ.filter q, (1 - P.funcProb (α i))) := by
  unfold guardedSome
  have h_r : (noneOf α r).DependsOn ((Finset.univ.filter r).biUnion S) := by
    unfold noneOf
    exact BoolFunc.DependsOn.prod (fun i => (hdep i).one_sub) _
  have h_q : (someOf α q).DependsOn ((Finset.univ.filter q).biUnion S) := by
    unfold someOf
    exact (BoolFunc.DependsOn.prod (fun i => (hdep i).one_sub) _).one_sub
  have h_disj :
      Disjoint ((Finset.univ.filter r).biUnion S)
               ((Finset.univ.filter q).biUnion S) := by
    rw [Finset.disjoint_biUnion_left]
    intro i hi
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    have hij : i ≠ j := fun heq =>
      hrq i (Finset.mem_filter.mp hi).2 (heq ▸ (Finset.mem_filter.mp hj).2)
    exact hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  rw [P.funcProb_mul_disjoint h_r h_q h_disj,
      funcProb_noneOf P α r S hdep hdisj,
      funcProb_someOf P α q S hdep hdisj]

end Guarded

section MaxMinRemaining

variable {V : Type} [LinearOrder V] (t : ι → V)

/-- "Non-empty random world with `MAX(t) < C`". -/
def maxLtOnNonempty (C : V) : BoolFunc X :=
  guardedSome α (fun i => C ≤ t i) (fun i => t i < C)

/-- "Non-empty random world with `MAX(t) = C`". -/
def maxEqOnNonempty (C : V) : BoolFunc X :=
  guardedSome α (fun i => C < t i) (fun i => t i = C)

/-- "Random world with `MAX(t) > C`" (such a world is non-empty). -/
def someAbove (C : V) : BoolFunc X :=
  someOf α (fun i => C < t i)

/-- "Random world with `MAX(t) < C`" (such a world is non-empty). -/
def someBelow (C : V) : BoolFunc X :=
  someOf α (fun i => t i < C)

/-- "Non-empty random world with `MAX(t) ≠ C`": disjoint union of
`MAX < C` and `MAX > C`. -/
def maxNeOnNonempty (C : V) : BoolFunc X :=
  maxLtOnNonempty α t C + someAbove α t C

/-- "Non-empty random world with `MIN(t) > C`". -/
def minGtOnNonempty (C : V) : BoolFunc X :=
  guardedSome α (fun i => t i ≤ C) (fun i => C < t i)

/-- "Non-empty random world with `MIN(t) = C`". -/
def minEqOnNonempty (C : V) : BoolFunc X :=
  guardedSome α (fun i => t i < C) (fun i => t i = C)

/-- "Non-empty random world with `MIN(t) ≠ C`": disjoint union of
`MIN < C` (i.e. some contributor below `C` is present) and `MIN > C`. -/
def minNeOnNonempty (C : V) : BoolFunc X :=
  minGtOnNonempty α t C + someBelow α t C

/-- Semantic reading of `maxLtOnNonempty`. -/
theorem maxLtOnNonempty_eval_iff (C : V) (v : X → Bool) :
    (maxLtOnNonempty α t C) v = true ↔
      (∃ i, α i v = true) ∧ ∀ i, α i v = true → t i < C := by
  rw [maxLtOnNonempty, guardedSome_eval_iff]
  constructor
  · rintro ⟨hall, i, -, hαi⟩
    refine ⟨⟨i, hαi⟩, fun j hαj => ?_⟩
    by_contra hnot
    rw [hall j (not_lt.mp hnot)] at hαj
    exact Bool.noConfusion hαj
  · rintro ⟨⟨i, hαi⟩, hall⟩
    refine ⟨fun j hrj => ?_, i, hall i hαi, hαi⟩
    cases hα : α j v with
    | false => rfl
    | true => exact absurd (hall j hα) (not_lt.mpr hrj)

/-- Semantic reading of `maxEqOnNonempty`: no present contributor exceeds
`C` and some present contributor attains it. -/
theorem maxEqOnNonempty_eval_iff (C : V) (v : X → Bool) :
    (maxEqOnNonempty α t C) v = true ↔
      (∀ i, α i v = true → t i ≤ C) ∧ ∃ i, t i = C ∧ α i v = true := by
  rw [maxEqOnNonempty, guardedSome_eval_iff]
  constructor
  · rintro ⟨hall, hex⟩
    refine ⟨fun j hαj => ?_, hex⟩
    by_contra hnot
    rw [hall j (not_le.mp hnot)] at hαj
    exact Bool.noConfusion hαj
  · rintro ⟨hall, hex⟩
    refine ⟨fun j hrj => ?_, hex⟩
    cases hα : α j v with
    | false => rfl
    | true => exact absurd (hall j hα) (not_le.mpr hrj)

/-- Semantic reading of `minGtOnNonempty`. -/
theorem minGtOnNonempty_eval_iff (C : V) (v : X → Bool) :
    (minGtOnNonempty α t C) v = true ↔
      (∃ i, α i v = true) ∧ ∀ i, α i v = true → C < t i := by
  rw [minGtOnNonempty, guardedSome_eval_iff]
  constructor
  · rintro ⟨hall, i, -, hαi⟩
    refine ⟨⟨i, hαi⟩, fun j hαj => ?_⟩
    by_contra hnot
    rw [hall j (not_lt.mp hnot)] at hαj
    exact Bool.noConfusion hαj
  · rintro ⟨⟨i, hαi⟩, hall⟩
    refine ⟨fun j hrj => ?_, i, hall i hαi, hαi⟩
    cases hα : α j v with
    | false => rfl
    | true => exact absurd (hall j hα) (not_lt.mpr hrj)

/-- Semantic reading of `minEqOnNonempty`: no present contributor is below
`C` and some present contributor attains it. -/
theorem minEqOnNonempty_eval_iff (C : V) (v : X → Bool) :
    (minEqOnNonempty α t C) v = true ↔
      (∀ i, α i v = true → C ≤ t i) ∧ ∃ i, t i = C ∧ α i v = true := by
  rw [minEqOnNonempty, guardedSome_eval_iff]
  constructor
  · rintro ⟨hall, hex⟩
    refine ⟨fun j hαj => ?_, hex⟩
    by_contra hnot
    rw [hall j (not_le.mp hnot)] at hαj
    exact Bool.noConfusion hαj
  · rintro ⟨hall, hex⟩
    refine ⟨fun j hrj => ?_, hex⟩
    cases hα : α j v with
    | false => rfl
    | true => exact absurd (hall j hα) (not_le.mpr hrj)

variable (S : ι → Finset X)
variable (hdep : ∀ i, (α i).DependsOn (S i))
variable (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))

include hdep hdisj

/-- **`MAX < C` factorisation under independence.** -/
theorem funcProb_maxLtOnNonempty (C : V) :
    P.funcProb (maxLtOnNonempty α t C) =
      (∏ i ∈ Finset.univ.filter (fun i => C ≤ t i),
          (1 - P.funcProb (α i)))
        * (1 - ∏ i ∈ Finset.univ.filter (fun i => t i < C),
            (1 - P.funcProb (α i))) :=
  funcProb_guardedSome P α _ _ S hdep hdisj
    (fun _ h1 h2 => absurd h2 (not_lt.mpr h1))

/-- **`MAX = C` factorisation under independence.** -/
theorem funcProb_maxEqOnNonempty (C : V) :
    P.funcProb (maxEqOnNonempty α t C) =
      (∏ i ∈ Finset.univ.filter (fun i => C < t i),
          (1 - P.funcProb (α i)))
        * (1 - ∏ i ∈ Finset.univ.filter (fun i => t i = C),
            (1 - P.funcProb (α i))) :=
  funcProb_guardedSome P α _ _ S hdep hdisj
    (fun _ h1 h2 => absurd (h2 ▸ h1) (lt_irrefl _))

/-- **`MAX > C` under independence**: the complement of "every contributor
above `C` is absent". -/
theorem funcProb_someAbove (C : V) :
    P.funcProb (someAbove α t C) =
      1 - ∏ i ∈ Finset.univ.filter (fun i => C < t i),
        (1 - P.funcProb (α i)) :=
  funcProb_someOf P α _ S hdep hdisj

/-- **`MIN < C` (equivalently `MAX`-dual) under independence**: the
complement of "every contributor below `C` is absent". -/
theorem funcProb_someBelow (C : V) :
    P.funcProb (someBelow α t C) =
      1 - ∏ i ∈ Finset.univ.filter (fun i => t i < C),
        (1 - P.funcProb (α i)) :=
  funcProb_someOf P α _ S hdep hdisj

/-- **`MIN > C` factorisation under independence.** -/
theorem funcProb_minGtOnNonempty (C : V) :
    P.funcProb (minGtOnNonempty α t C) =
      (∏ i ∈ Finset.univ.filter (fun i => t i ≤ C),
          (1 - P.funcProb (α i)))
        * (1 - ∏ i ∈ Finset.univ.filter (fun i => C < t i),
            (1 - P.funcProb (α i))) :=
  funcProb_guardedSome P α _ _ S hdep hdisj
    (fun _ h1 h2 => absurd h1 (not_le.mpr h2))

/-- **`MIN = C` factorisation under independence.** -/
theorem funcProb_minEqOnNonempty (C : V) :
    P.funcProb (minEqOnNonempty α t C) =
      (∏ i ∈ Finset.univ.filter (fun i => t i < C),
          (1 - P.funcProb (α i)))
        * (1 - ∏ i ∈ Finset.univ.filter (fun i => t i = C),
            (1 - P.funcProb (α i))) :=
  funcProb_guardedSome P α _ _ S hdep hdisj
    (fun _ h1 h2 => absurd (h2 ▸ h1) (lt_irrefl _))

omit hdep hdisj in
/-- The events `MAX < C` (on non-empty worlds) and `MAX > C` are
incompatible: their product is the `𝟘` function. -/
lemma maxLt_mul_someAbove_eq_zero (C : V) :
    maxLtOnNonempty α t C * someAbove α t C = 0 := by
  funext v
  show ((maxLtOnNonempty α t C) v && (someAbove α t C) v) = (0 : BoolFunc X) v
  cases hlt : (maxLtOnNonempty α t C) v with
  | false => rfl
  | true =>
    rw [Bool.true_and]
    obtain ⟨-, hall⟩ := (maxLtOnNonempty_eval_iff α t C v).mp hlt
    cases hab : (someAbove α t C) v with
    | false => rfl
    | true =>
      obtain ⟨i, hCi, hαi⟩ := (someOf_eval_iff α _ v).mp hab
      exact absurd (hall i hαi) (not_lt.mpr (le_of_lt hCi))

omit hdep hdisj in
/-- The events `MIN > C` (on non-empty worlds) and `MIN < C` are
incompatible: their product is the `𝟘` function. -/
lemma minGt_mul_someBelow_eq_zero (C : V) :
    minGtOnNonempty α t C * someBelow α t C = 0 := by
  funext v
  show ((minGtOnNonempty α t C) v && (someBelow α t C) v) = (0 : BoolFunc X) v
  cases hgt : (minGtOnNonempty α t C) v with
  | false => rfl
  | true =>
    rw [Bool.true_and]
    obtain ⟨-, hall⟩ := (minGtOnNonempty_eval_iff α t C v).mp hgt
    cases hab : (someBelow α t C) v with
    | false => rfl
    | true =>
      obtain ⟨i, hCi, hαi⟩ := (someOf_eval_iff α _ v).mp hab
      exact absurd (hall i hαi) (not_lt.mpr (le_of_lt hCi))

/-- **`MAX ≠ C` on non-empty worlds under independence**: probabilities of
the two disjoint cases `MAX < C` and `MAX > C` add. -/
theorem funcProb_maxNeOnNonempty (C : V) :
    P.funcProb (maxNeOnNonempty α t C) =
      P.funcProb (maxLtOnNonempty α t C) + P.funcProb (someAbove α t C) := by
  rw [maxNeOnNonempty, P.funcProb_add_eq,
    maxLt_mul_someAbove_eq_zero α t C, P.funcProb_zero, sub_zero]

/-- **`MIN ≠ C` on non-empty worlds under independence**: probabilities of
the two disjoint cases `MIN > C` and `MIN < C` add. -/
theorem funcProb_minNeOnNonempty (C : V) :
    P.funcProb (minNeOnNonempty α t C) =
      P.funcProb (minGtOnNonempty α t C) + P.funcProb (someBelow α t C) := by
  rw [minNeOnNonempty, P.funcProb_add_eq,
    minGt_mul_someBelow_eq_zero α t C, P.funcProb_zero, sub_zero]

end MaxMinRemaining

/-! ## CDF assembly for COUNT

The recurrences `countMass_insert_zero` / `countMass_insert_succ` compute
the point masses `ρ_J(j)`. The results below assemble them into the
probability of an arbitrary comparison: the satisfying counts form a
subset of `{0, …, |J|}` (an interval, for the six comparison operators)
and the corresponding point masses add; the empty-world mass is
`∏ (1 - p i)`; and the upper tail can be computed as a lower tail of the
complemented contributors (`Pr[B ≥ C] = Pr[B' ≤ N − C]`), which is the
shorter of the two summations when `C > N/2`. -/

section CountCDF

/-- Pointwise evaluation of a `Finset.sum` of `BoolFunc`s: the sum (OR)
evaluates to `true` iff some summand does. -/
lemma sum_eval_eq_true_iff {ι' : Type} [DecidableEq ι']
    (J : Finset ι') (β : ι' → BoolFunc X) (v : X → Bool) :
    (∑ i ∈ J, β i) v = true ↔ ∃ i ∈ J, β i v = true := by
  classical
  induction J using Finset.induction with
  | empty =>
    constructor
    · intro h
      exact Bool.noConfusion h
    · rintro ⟨i, hi, -⟩
      exact absurd hi (Finset.notMem_empty i)
  | insert i J hi ih =>
    rw [Finset.sum_insert hi]
    show (β i v || (∑ j ∈ J, β j) v) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨i, Finset.mem_insert_self i J, h⟩
      · exact ⟨j, Finset.mem_insert_of_mem hj, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Finset.mem_insert.mp hj with rfl | hjJ
      · exact Or.inl h
      · exact Or.inr ⟨j, hjJ, h⟩

/-- Distinct count indicators are incompatible. -/
lemma countEqIndicator_mul_eq_zero (J : Finset ι) {j j' : ℕ} (h : j ≠ j') :
    countEqIndicator α J j * countEqIndicator α J j' = 0 := by
  funext v
  show ((countEqIndicator α J j) v && (countEqIndicator α J j') v)
      = (0 : BoolFunc X) v
  by_cases hj : (J.filter (fun i => α i v = true)).card = j
  · rw [show (countEqIndicator α J j) v = true from decide_eq_true hj,
      Bool.true_and]
    exact decide_eq_false fun hj' => h (hj.symm.trans hj')
  · rw [show (countEqIndicator α J j) v = false from decide_eq_false hj,
      Bool.false_and]
    rfl

/-- **CDF assembly.** For any predicate `g` on counts, the probability that
the number of present contributors satisfies `g` is the sum of the point
masses `ρ_J(j)` over the satisfying counts `j ∈ {0, …, |J|}`. For the six
comparison operators the satisfying set is an interval. -/
theorem funcProb_count_filter (J : Finset ι) (g : ℕ → Prop) [DecidablePred g] :
    P.funcProb (fun v => decide (g ((J.filter (fun i => α i v = true)).card)))
      = ∑ j ∈ (Finset.range (J.card + 1)).filter g,
          P.funcProb (countEqIndicator α J j) := by
  have hfun : (fun v => decide (g ((J.filter (fun i => α i v = true)).card))
        : BoolFunc X)
      = ∑ j ∈ (Finset.range (J.card + 1)).filter g, countEqIndicator α J j := by
    funext v
    set n := (J.filter (fun i => α i v = true)).card with hn
    by_cases hg : g n
    · rw [decide_eq_true hg]
      symm
      rw [sum_eval_eq_true_iff]
      refine ⟨n, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
          (le_trans (Finset.card_filter_le _ _) le_rfl)), hg⟩, ?_⟩
      exact decide_eq_true rfl
    · rw [decide_eq_false hg]
      symm
      cases hs : (∑ j ∈ (Finset.range (J.card + 1)).filter g,
          countEqIndicator α J j) v with
      | false => rfl
      | true =>
        obtain ⟨j, hj, hjv⟩ := (sum_eval_eq_true_iff _ _ v).mp hs
        have hnj : n = j := of_decide_eq_true hjv
        exact absurd (hnj ▸ (Finset.mem_filter.mp hj).2) hg
  rw [hfun,
    P.funcProb_sum_incompatible _ _
      (fun j _ j' _ hne => countEqIndicator_mul_eq_zero α J hne)]

/-- **Empty-world mass.** The probability that no contributor of `J` is
present is `∏_{i ∈ J} (1 - p i)`. -/
theorem countMass_zero (S : ι → Finset X)
    (hdep : ∀ i, (α i).DependsOn (S i))
    (hdisj : Set.Pairwise Set.univ (fun i j => Disjoint (S i) (S j)))
    (J : Finset ι) :
    P.funcProb (countEqIndicator α J 0) = ∏ i ∈ J, (1 - P.funcProb (α i)) := by
  have hind : countEqIndicator α J 0 = ∏ i ∈ J, (1 - α i) := by
    funext v
    show (decide ((J.filter (fun i => α i v = true)).card = 0) : Bool)
        = (∏ i ∈ J, (1 - α i)) v
    by_cases hall : ∀ i ∈ J, α i v = false
    · have hfe : J.filter (fun i => α i v = true) = ∅ :=
        Finset.filter_false_of_mem fun i hi => by
          rw [hall i hi]; exact Bool.false_ne_true
      rw [decide_eq_true (by rw [hfe]; rfl :
            (J.filter (fun i => α i v = true)).card = 0)]
      symm
      exact (prod_eval_eq_true_iff _ _ _).mpr fun i hi => by
        rw [one_sub_eval, hall i hi]; rfl
    · push Not at hall
      obtain ⟨i, hiJ, hαi⟩ := hall
      have hαi' : α i v = true := by
        cases h : α i v with
        | false => exact absurd h hαi
        | true => rfl
      have hne : (J.filter (fun i => α i v = true)).card ≠ 0 :=
        Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨hiJ, hαi'⟩)
      rw [decide_eq_false hne]
      symm
      cases hp : (∏ i ∈ J, (1 - α i)) v with
      | false => rfl
      | true =>
        have := (prod_eval_eq_true_iff _ _ _).mp hp i hiJ
        rw [one_sub_eval, hαi'] at this
        exact Bool.noConfusion this
  rw [hind, P.funcProb_prod_disjoint (fun i => 1 - α i) S
    (fun i => (hdep i).one_sub) hdisj]
  exact Finset.prod_congr rfl fun i _ => P.funcProb_sub_self_const_one (α i)

/-- **Shorter-tail identity, event form.** Counting the present
contributors down from `C` is counting the absent contributors up to
`|J| - C`: the two indicator functions coincide. -/
theorem count_ge_eq_absent_le (J : Finset ι) {C : ℕ} (hC : C ≤ J.card) :
    (fun v => decide (C ≤ (J.filter (fun i => α i v = true)).card) : BoolFunc X)
      = fun v =>
          decide ((J.filter (fun i => (1 - α i) v = true)).card ≤ J.card - C) := by
  funext v
  have hcompl : J.filter (fun i => (1 - α i) v = true)
      = J.filter (fun i => ¬ (α i v = true)) :=
    Finset.filter_congr fun i _ => by rw [one_sub_eval]; simp
  have hsplit : (J.filter (fun i => α i v = true)).card
      + (J.filter (fun i => (1 - α i) v = true)).card = J.card := by
    rw [hcompl]
    exact Finset.card_filter_add_card_filter_not _
  by_cases h : C ≤ (J.filter (fun i => α i v = true)).card
  · rw [decide_eq_true h, decide_eq_true (by omega :
      (J.filter (fun i => (1 - α i) v = true)).card ≤ J.card - C)]
  · rw [decide_eq_false h, decide_eq_false (by omega :
        ¬ (J.filter (fun i => (1 - α i) v = true)).card ≤ J.card - C)]

/-- **Shorter-tail identity, probability form**: `Pr[B ≥ C] = Pr[B' ≤ N − C]`
where `B` counts the present contributors and `B'` the absent ones. The
right-hand side assembles from the point masses of the complemented
contributors (`1 - α i`, marginals `1 - p i`), which is the shorter
summation when `C` exceeds `N/2`. -/
theorem funcProb_count_ge_eq_absent_le (J : Finset ι) {C : ℕ} (hC : C ≤ J.card) :
    P.funcProb (fun v => decide (C ≤ (J.filter (fun i => α i v = true)).card))
      = P.funcProb (fun v =>
          decide ((J.filter (fun i => (1 - α i) v = true)).card ≤ J.card - C)) := by
  rw [count_ge_eq_absent_le α J hC]

end CountCDF

/-! ## The possible-world HAVING provenance under a valuation

The predicate provenance of an aggregate comparison
(`Having.havingProv`, over `𝔹[X]`) is a `⊕`-sum of one disjunct per
non-empty possible world. Under a fixed valuation of the Boolean
variables, **exactly one** disjunct survives: the one of the *realised*
world, formed of the occurrences whose annotation is true. Consequently
the predicate provenance evaluates to true exactly when the realised
world is non-empty and satisfies the comparison – the bridge between the
intensional possible-world semantics and probabilistic query evaluation:
the probability of the predicate provenance is the probability that the
realised world is non-empty and satisfies the comparison.

The section culminates in `booleanHaving_pqe`: for a Boolean query made
of a Boolean combination of aggregate comparisons (`HavingPred`) applied
on top of a non-aggregation query over a tuple-independent probabilistic
database, the probability that a random world satisfies the query
(`booleanHavingProb`, via the plain semantics `HavingPred.modelsBoolean`)
equals the probability of its Boolean provenance
(`HavingPred.booleanProv`). The non-aggregation operators are handled by
`randomWorld_evaluateAnnotated` and the comparisons by the
exactly-one-disjunct bridge, composed through the sorted-sublist
identity `groupSeq_randomWorld` between the plain group sequence of a
random world and the realised subsequence of the annotated group
sequence. -/

section HavingPQE

open Having

variable {T : Type} [ValueType T]

/-- The world realised by a valuation `v`: the positions of the group
sequence whose annotation evaluates to true under `v`. -/
def realizedWorld {m : ℕ} (U : List (AnnotatedTuple T (BoolFunc X) m))
    (v : X → Bool) : Finset (Fin U.length) :=
  Finset.univ.filter (fun i => (U.get i).snd v = true)

/-- **Exactly one world annotation survives**: under a valuation `v`, the
factored world annotation of `W` is true iff `W` is the realised world. -/
theorem worldAnn_eval_iff {N : ℕ} (α : Fin N → BoolFunc X)
    (W : Finset (Fin N)) (v : X → Bool) :
    (worldAnn α W) v = true ↔ W = Finset.univ.filter (fun i => α i v = true) := by
  show ((∏ i ∈ W, α i) v && ((1 - ∑ i ∈ Wᶜ, α i) v)) = true ↔ _
  rw [Bool.and_eq_true, prod_eval_eq_true_iff, one_sub_eval,
    Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨hall, hnone⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hi => hall i hi
    · intro hi
      by_contra hiW
      have hmem : (∑ j ∈ Wᶜ, α j) v = true :=
        (sum_eval_eq_true_iff _ _ _).mpr ⟨i, Finset.mem_compl.mpr hiW, hi⟩
      rw [hmem] at hnone
      exact Bool.noConfusion hnone
  · rintro rfl
    refine ⟨fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
    cases hs : (∑ j ∈ (Finset.univ.filter (fun i => α i v = true))ᶜ, α j) v with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjv⟩ := (sum_eval_eq_true_iff _ _ _).mp hs
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjv⟩)
        (Finset.mem_compl.mp hj)

/-- Evaluation of the comparison characteristic `χ_op`. -/
lemma chi_eval_iff (op : CompOp) (a c : T) (v : X → Bool) :
    (Having.chi (K := BoolFunc X) op a c) v = true ↔ op.eval a c := by
  unfold Having.chi
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (fun hh => Bool.noConfusion hh) h

/-- **PQE bridge for aggregate comparisons.** Under a valuation `v`, the
predicate provenance of `f(t) op c` on the group sequence `U` evaluates to
true iff the realised world is non-empty and its aggregate value satisfies
the comparison. Composed with the probability semantics, the probability
of the predicate provenance is the probability, over random worlds, that a
non-empty realised group satisfies the `HAVING` comparison. -/
theorem havingProv_eval_iff {m : ℕ} (U : List (AnnotatedTuple T (BoolFunc X) m))
    (t : Term T m) (f : SeqAggFunc T) (op : CompOp) (c : T) (v : X → Bool) :
    (havingProv U t f op c) v = true
      ↔ (realizedWorld U v).Nonempty
        ∧ op.eval (aggValOn U t f (realizedWorld U v)) c := by
  unfold havingProv
  rw [sum_eval_eq_true_iff]
  constructor
  · rintro ⟨W, hW, hWv⟩
    obtain ⟨-, hne⟩ := Finset.mem_filter.mp hW
    have hsplit : ((worldAnn (fun i => (U.get i).snd) W) v
        && (Having.chi (K := BoolFunc X) op (aggValOn U t f W) c) v) = true := hWv
    rw [Bool.and_eq_true] at hsplit
    have hWeq : W = realizedWorld U v :=
      (worldAnn_eval_iff _ W v).mp hsplit.1
    subst hWeq
    exact ⟨hne, (chi_eval_iff op _ c v).mp hsplit.2⟩
  · rintro ⟨hne, hP⟩
    refine ⟨realizedWorld U v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, ?_⟩
    have hgoal : ((worldAnn (fun i => (U.get i).snd) (realizedWorld U v)) v
        && (Having.chi (K := BoolFunc X) op
              (aggValOn U t f (realizedWorld U v)) c) v) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(worldAnn_eval_iff _ _ v).mpr rfl, (chi_eval_iff op _ c v).mpr hP⟩
    exact hgoal


/-- Pointwise evaluation of a `Multiset.sum` of `BoolFunc`s: the sum (OR)
evaluates to true iff some summand does. -/
lemma multiset_sum_eval_eq_true_iff (s : Multiset (BoolFunc X)) (v : X → Bool) :
    s.sum v = true ↔ ∃ f ∈ s, f v = true := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.sum_zero]
    exact iff_of_false (fun h => Bool.noConfusion h)
      (fun ⟨f, hf, _⟩ => absurd hf (Multiset.notMem_zero f))
  | cons a s ih =>
    rw [Multiset.sum_cons]
    show (a v || s.sum v) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨f, hf, h⟩)
      · exact ⟨a, Multiset.mem_cons_self a s, h⟩
      · exact ⟨f, Multiset.mem_cons_of_mem hf, h⟩
    · rintro ⟨f, hf, h⟩
      rcases Multiset.mem_cons.mp hf with rfl | hfs
      · exact Or.inl h
      · exact Or.inr ⟨f, hfs, h⟩

/-- Selecting the positions whose element satisfies a Boolean predicate
yields the filtered list. -/
theorem seqOf_filter_positions {β : Type} (P : β → Bool) :
    ∀ U : List β,
      seqOf U (Finset.univ.filter (fun i => P (U.get i) = true)) = U.filter P
  | [] => rfl
  | a :: U => by
    rw [seqOf]
    have h0 : ((0 : Fin (U.length + 1)) ∈ Finset.univ.filter
        (fun i => P ((a :: U).get i) = true)) ↔ P a = true := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_cons_zero]
    have hsucc : Finset.univ.filter
          (fun i : Fin U.length => i.succ ∈ Finset.univ.filter
            (fun j => P ((a :: U).get j) = true))
        = Finset.univ.filter (fun i => P (U.get i) = true) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.succ,
        List.get_cons_succ]
    rw [hsucc, seqOf_filter_positions P U]
    by_cases hPa : P a = true
    · rw [if_pos (h0.mpr hPa), List.filter_cons_of_pos hPa]
      rfl
    · rw [if_neg (fun h => hPa (h0.mp h)),
        List.filter_cons_of_neg (by simpa using hPa), List.nil_append]

/-- The subsequence selected by the realised world is the sublist of
occurrences whose annotation is true under the valuation. -/
theorem seqOf_realizedWorld {m : ℕ} (U : List (AnnotatedTuple T (BoolFunc X) m))
    (v : X → Bool) :
    seqOf U (realizedWorld U v) = U.filter (fun p => p.snd v) := by
  unfold realizedWorld
  exact seqOf_filter_positions (fun p => p.snd v) U

/-- The realised world of a group is non-empty iff some occurrence of the
group survives the valuation. -/
theorem realizedWorld_nonempty_iff {m : ℕ}
    (U : List (AnnotatedTuple T (BoolFunc X) m)) (v : X → Bool) :
    (realizedWorld U v).Nonempty ↔ ∃ p ∈ U, p.snd v = true := by
  unfold realizedWorld
  rw [Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨U.get i, U.get_mem i, hi⟩
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    exact ⟨i, Finset.mem_univ i, by rw [hi]; exact hpv⟩

/-- **The plain group sequence of a random world is the realised
subsequence of the annotated group sequence**: both are lists of the same
multiset (the realised occurrences of the group), sorted along `≼`. -/
theorem groupSeq_randomWorld {m n₁ : ℕ} [HasAltLinearOrder (BoolFunc X)]
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T (BoolFunc X) m)
    (g : Tuple T n₁) (v : X → Bool) :
    Relation.groupSeq is (randomWorld v r) g
      = (seqOf (havingGroup is r g) (realizedWorld (havingGroup is r g) v)).map
          Prod.fst := by
  rw [seqOf_realizedWorld]
  have hpair : ((havingGroup is r g).filter (fun p => p.snd v)).Pairwise
      (fun p q : AnnotatedTuple T (BoolFunc X) m => p.fst ≤ q.fst) :=
    List.Pairwise.sublist List.filter_sublist
      ((havingGroup_pairwise is r g).imp fun h => h.elim le_of_lt le_of_eq)
  have hsorted : (((havingGroup is r g).filter (fun p => p.snd v)).map
      Prod.fst).Pairwise (· ≤ ·) := List.pairwise_map.mpr hpair
  have hcoe : (↑((havingGroup is r g).filter (fun p => p.snd v))
        : Multiset (AnnotatedTuple T (BoolFunc X) m))
      = Multiset.filter (fun p : AnnotatedTuple T (BoolFunc X) m =>
          p.snd v = true)
        (↑(havingGroup is r g) : Multiset (AnnotatedTuple T (BoolFunc X) m)) := by
    rw [Multiset.filter_coe]
    exact congrArg (fun l : List (AnnotatedTuple T (BoolFunc X) m) =>
        (↑l : Multiset (AnnotatedTuple T (BoolFunc X) m)))
      (List.filter_congr fun p _ => by cases p.snd v <;> rfl)
  have hmul : Multiset.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')
        (randomWorld v r)
      = ↑(((havingGroup is r g).filter (fun p => p.snd v)).map Prod.fst) :=
    calc Multiset.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')
          (randomWorld v r)
        = Multiset.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')
            (Multiset.map Prod.fst
              (Multiset.filter (fun p : AnnotatedTuple T (BoolFunc X) m =>
                p.snd v = true) r)) := rfl
      _ = Multiset.map Prod.fst (Multiset.filter
            ((fun u => ∀ k' : Fin n₁, u (is k') = g k') ∘ Prod.fst)
            (Multiset.filter (fun p : AnnotatedTuple T (BoolFunc X) m =>
              p.snd v = true) r)) :=
          Multiset.filter_map _ _ _
      _ = Multiset.map Prod.fst (Multiset.filter
            (fun p : AnnotatedTuple T (BoolFunc X) m =>
              (∀ k' : Fin n₁, p.fst (is k') = g k') ∧ p.snd v = true) r) :=
          congrArg _ (Multiset.filter_filter _ _ _)
      _ = Multiset.map Prod.fst (Multiset.filter
            (fun p : AnnotatedTuple T (BoolFunc X) m =>
              p.snd v = true ∧ ∀ k' : Fin n₁, p.fst (is k') = g k') r) :=
          congrArg _ (Multiset.filter_congr fun p _ => and_comm)
      _ = Multiset.map Prod.fst (Multiset.filter
            (fun p : AnnotatedTuple T (BoolFunc X) m => p.snd v = true)
            (Multiset.filter (fun p : AnnotatedTuple T (BoolFunc X) m =>
              ∀ k' : Fin n₁, p.fst (is k') = g k') r)) :=
          congrArg _ (Multiset.filter_filter _ _ _).symm
      _ = Multiset.map Prod.fst (Multiset.filter
            (fun p : AnnotatedTuple T (BoolFunc X) m => p.snd v = true)
            (↑(havingGroup is r g)
              : Multiset (AnnotatedTuple T (BoolFunc X) m))) := by
          rw [havingGroup_coe]
      _ = Multiset.map Prod.fst
            (↑((havingGroup is r g).filter (fun p => p.snd v))
              : Multiset (AnnotatedTuple T (BoolFunc X) m)) := by rw [hcoe]
      _ = ↑(((havingGroup is r g).filter (fun p => p.snd v)).map Prod.fst) :=
          Multiset.map_coe _ _
  show Multiset.sort _ (· ≤ ·) = _
  exact List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hsorted
    (Multiset.coe_eq_coe.mp (by rw [Multiset.sort_eq]; exact hmul))

/-- A key is realised in the random world iff the realised world of its
group sequence is non-empty. -/
theorem randomWorld_key_mem_iff {m n₁ : ℕ} [HasAltLinearOrder (BoolFunc X)]
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T (BoolFunc X) m)
    (g : Tuple T n₁) (v : X → Bool) :
    g ∈ Multiset.map (fun u => fun k => u (is k)) (randomWorld v r)
      ↔ (realizedWorld (havingGroup is r g) v).Nonempty := by
  rw [realizedWorld_nonempty_iff]
  constructor
  · intro hg
    obtain ⟨u, hu, hgu⟩ := Multiset.mem_map.mp hg
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hu
    obtain ⟨hpr, hpv⟩ := Multiset.mem_filter.mp hp
    refine ⟨p, ?_, hpv⟩
    rw [← Multiset.mem_coe, havingGroup_coe]
    exact Multiset.mem_filter.mpr ⟨hpr, fun k' => congrFun hgu k'⟩
  · rintro ⟨p, hpU, hpv⟩
    have hp : p ∈ Multiset.filter
        (fun p : AnnotatedTuple T (BoolFunc X) m =>
          ∀ k' : Fin n₁, p.fst (is k') = g k') r := by
      rw [← havingGroup_coe is r g]
      exact Multiset.mem_coe.mpr hpU
    obtain ⟨hpr, hkey⟩ := Multiset.mem_filter.mp hp
    exact Multiset.mem_map.mpr ⟨p.fst,
      Multiset.mem_map.mpr ⟨p, Multiset.mem_filter.mpr ⟨hpr, hpv⟩, rfl⟩,
      funext hkey⟩

/-- **PQE bridge for Boolean combinations, with polarity.** Under a
valuation, the polarity-aware predicate provenance of `ψ` is true iff the
realised world of the group is non-empty and `ψ` (negated according to
the polarity) holds classically on the realised occurrence sequence. -/
theorem HavingPred.provAux_eval_iff {m n₁ : ℕ}
    (U : List (AnnotatedTuple T (BoolFunc X) m)) (g : Tuple T n₁)
    (v : X → Bool) :
    ∀ (negated : Bool) (ψ : HavingPred T m n₁),
    (ψ.provAux U g negated) v = true
      ↔ (realizedWorld U v).Nonempty
        ∧ (if negated
            then ¬ ψ.holdsOnSeq ((seqOf U (realizedWorld U v)).map Prod.fst) g
            else ψ.holdsOnSeq ((seqOf U (realizedWorld U v)).map Prod.fst) g)
  | negated, .cmp t f op s => by
    show (havingProv U t f (if negated then op.negate else op) (s.eval g)) v
        = true ↔ _
    rw [havingProv_eval_iff]
    have hagg : f (((seqOf U (realizedWorld U v)).map Prod.fst).map t.eval)
        = aggValOn U t f (realizedWorld U v) := by
      rw [List.map_map]
      rfl
    cases negated with
    | false =>
      rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      simp only [HavingPred.holdsOnSeq]
      rw [hagg]
    | true =>
      rw [if_pos rfl, if_pos rfl]
      simp only [HavingPred.holdsOnSeq]
      rw [CompOp.negate_eval, hagg]
  | negated, .not ψ => by
    show (ψ.provAux U g (!negated)) v = true ↔ _
    rw [HavingPred.provAux_eval_iff U g v (!negated) ψ]
    simp only [HavingPred.holdsOnSeq]
    cases negated with
    | false =>
      rw [Bool.not_false, if_pos rfl, if_neg Bool.false_ne_true]
    | true =>
      rw [Bool.not_true, if_neg Bool.false_ne_true, if_pos rfl, not_not]
  | negated, .and ψ₁ ψ₂ => by
    have h₁ := HavingPred.provAux_eval_iff U g v negated ψ₁
    have h₂ := HavingPred.provAux_eval_iff U g v negated ψ₂
    cases negated with
    | false =>
      rw [if_neg Bool.false_ne_true] at h₁ h₂
      show ((ψ₁.provAux U g false) v && (ψ₂.provAux U g false) v) = true ↔ _
      rw [Bool.and_eq_true, h₁, h₂, if_neg Bool.false_ne_true]
      simp only [HavingPred.holdsOnSeq]
      tauto
    | true =>
      rw [if_pos rfl] at h₁ h₂
      show ((ψ₁.provAux U g true) v || (ψ₂.provAux U g true) v) = true ↔ _
      rw [Bool.or_eq_true, h₁, h₂, if_pos rfl]
      simp only [HavingPred.holdsOnSeq]
      tauto
  | negated, .or ψ₁ ψ₂ => by
    have h₁ := HavingPred.provAux_eval_iff U g v negated ψ₁
    have h₂ := HavingPred.provAux_eval_iff U g v negated ψ₂
    cases negated with
    | false =>
      rw [if_neg Bool.false_ne_true] at h₁ h₂
      show ((ψ₁.provAux U g false) v || (ψ₂.provAux U g false) v) = true ↔ _
      rw [Bool.or_eq_true, h₁, h₂, if_neg Bool.false_ne_true]
      simp only [HavingPred.holdsOnSeq]
      tauto
    | true =>
      rw [if_pos rfl] at h₁ h₂
      show ((ψ₁.provAux U g true) v && (ψ₂.provAux U g true) v) = true ↔ _
      rw [Bool.and_eq_true, h₁, h₂, if_pos rfl]
      simp only [HavingPred.holdsOnSeq]
      tauto

/-- **PQE bridge for Boolean combinations of aggregate comparisons.**
Under a valuation, the predicate provenance of `ψ` on the group sequence
`U` is true iff the realised world is non-empty and `ψ` holds classically
on the realised occurrence sequence. -/
theorem HavingPred.prov_eval_iff {m n₁ : ℕ}
    (U : List (AnnotatedTuple T (BoolFunc X) m)) (g : Tuple T n₁)
    (v : X → Bool) (ψ : HavingPred T m n₁) :
    (ψ.prov U g) v = true
      ↔ (realizedWorld U v).Nonempty
        ∧ ψ.holdsOnSeq ((seqOf U (realizedWorld U v)).map Prod.fst) g := by
  have h := HavingPred.provAux_eval_iff U g v false ψ
  rw [if_neg Bool.false_ne_true] at h
  exact h

/-- **Characteristic property of the Boolean provenance.** Under a
valuation, the Boolean provenance of a Boolean `HAVING` query is true iff
the query holds on the corresponding possible world. -/
theorem HavingPred.booleanProv_eval_iff [HasAltLinearOrder (BoolFunc X)]
    {m n₁ : ℕ} (q : Query T m) (hq : q.source)
    (Î : AnnotatedDatabase T (BoolFunc X)) (is : Tuple (Fin m) n₁)
    (ψ : HavingPred T m n₁) (v : X → Bool) :
    (ψ.booleanProv q hq Î is) v = true
      ↔ ψ.modelsBoolean (Î.randomWorld v) q is := by
  unfold HavingPred.booleanProv HavingPred.modelsBoolean
  rw [← randomWorld_evaluateAnnotated q hq Î v, multiset_sum_eval_eq_true_iff]
  constructor
  · rintro ⟨fb, hfb, hfbv⟩
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hfb
    rw [HavingPred.prov_eval_iff] at hfbv
    obtain ⟨hne, hhold⟩ := hfbv
    exact ⟨g, (randomWorld_key_mem_iff is _ g v).mpr hne,
      by rw [groupSeq_randomWorld]; exact hhold⟩
  · rintro ⟨g, hgmem, hhold⟩
    have hkey : g ∈ ((q.evaluateAnnotated hq Î).map
        (fun p => fun k => p.fst (is k))).dedup := by
      rw [Multiset.mem_dedup]
      obtain ⟨u, hu, hg⟩ := Multiset.mem_map.mp hgmem
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hu
      exact Multiset.mem_map.mpr ⟨p, (Multiset.mem_filter.mp hp).1, hg⟩
    refine ⟨ψ.prov (havingGroup is (q.evaluateAnnotated hq Î) g) g,
      Multiset.mem_map.mpr ⟨g, hkey, rfl⟩, ?_⟩
    rw [HavingPred.prov_eval_iff]
    exact ⟨(randomWorld_key_mem_iff is _ g v).mp hgmem,
      by rw [← groupSeq_randomWorld]; exact hhold⟩

/-- Probability that a random world of `Î` satisfies a Boolean `HAVING`
query: the sum of `Pr(v)` over the valuations whose possible world does. -/
noncomputable def booleanHavingProb {m n₁ : ℕ} (q : Query T m)
    (Î : AnnotatedDatabase T (BoolFunc X)) (is : Tuple (Fin m) n₁)
    (ψ : HavingPred T m n₁) : ℚ :=
  ∑ v : X → Bool,
    if ψ.modelsBoolean (Î.randomWorld v) q is then P.valProb v else 0

/-- **Probabilistic query evaluation through the `HAVING` provenance.**
For a Boolean query made of a Boolean combination `ψ` of aggregate
comparisons applied on top of a non-aggregation query `q` grouped by
`is`, over a tuple-independent probabilistic database, the probability
that a random world satisfies the query equals the probability of its
Boolean provenance (the `⊕`-sum, over the group keys, of the predicate
provenance of `ψ`). The non-aggregation operators of `q` are handled by
the correctness of intensional probabilistic query evaluation
(`ProbAssignment.theorem_12` machinery via
`randomWorld_evaluateAnnotated`), and the aggregate comparison by the
exactly-one-disjunct bridge `HavingPred.prov_eval_iff`. -/
theorem booleanHaving_pqe [HasAltLinearOrder (BoolFunc X)] {m n₁ : ℕ}
    (q : Query T m) (hq : q.source) (Î : AnnotatedDatabase T (BoolFunc X))
    (is : Tuple (Fin m) n₁) (ψ : HavingPred T m n₁) :
    booleanHavingProb P q Î is ψ = P.funcProb (ψ.booleanProv q hq Î is) := by
  unfold booleanHavingProb ProbAssignment.funcProb
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : ψ.modelsBoolean (Î.randomWorld v) q is
  · have hf : (ψ.booleanProv q hq Î is) v = true :=
      (HavingPred.booleanProv_eval_iff q hq Î is ψ v).mpr h
    rw [if_pos h, if_pos hf]
  · have hf : ¬ (ψ.booleanProv q hq Î is) v = true :=
      fun hf => h ((HavingPred.booleanProv_eval_iff q hq Î is ψ v).mp hf)
    rw [if_neg h, if_neg hf]

end HavingPQE

end HavingProbability
