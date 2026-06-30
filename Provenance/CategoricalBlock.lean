/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false

/-!
# Categorical-block probability and deterministic-OR soundness

This file is the categorical-block counterpart of `Provenance.Circuit`'s
decomposable + deterministic weighted-model-counting correctness theorem
(`Circuit.dD_funcProb_eq_probDD`): the same result re-proved over
**categorical block variables** instead of **free Boolean variables**. It is
an independent development (it shares no code with `Provenance.Circuit`; the
Boolean case is the `κ ≡ fun _ => Bool` instance of this one).

It is the formal counterpart of the *verified mulinput-OR certificate*
correctness-hardening item for ProvSQL's bounded-treewidth route (the
`repair_key` / BID block consumed by `evaluateCertifiedIsland`): that
evaluator marks a block's `plus(mulinputs)` *deterministic* and trusts the
mark: it plain-sums the alternatives, registers the block key once, and
reads the none-branch as `monus(one, plus(mulinputs)) = 1 - Σ pᵢ`. The
determinism of those state ORs is a global property the C++ does not check
locally. This development is the spec backing that trust, in the
probability / weighted-model-counting semantics.

## Modeling choice (the crux)

A block is modeled as **one categorical random variable**, *not* as
independent Booleans with an at-most-one constraint. Concretely we work
over a finite index `ι` of blocks, each block `b : ι` carrying a finite
outcome type `κ b`; a `CatAssignment` gives, per block, a probability
distribution `P.prob b : κ b → ℚ` summing to `1`. A valuation
`v : (b : ι) → κ b` draws one outcome per block, with the blocks
*independent*: `valProb v = ∏ b, P.prob b (v b)`.

A *mulinput* `mᵢ` of a block `b` is the event `{v | v b = i}`; the
*none-branch* is `{v | v b = o}` for a designated outcome `o : κ b`. With
this model the three block facts the C++ relies on are near-immediate
(`mulin_disjoint`, `mulin_or_prob`, `mulin_none`), and the deterministic-OR
sum is exact (`singleBlock_detOR_sound`).

## Main definitions

* `CatAssignment κ` – a per-block categorical probability distribution.
* `CatAssignment.valProb` – `Pr(v)` for a categorical valuation, blocks
  independent.
* `CatAssignment.eventProb` – `Pr(E)` for an event `E : ((b : ι) → κ b) → Bool`.
* `EventDependsOn` – support of an event (a `Finset` of blocks).
* `CatCircuit ι κ` – Boolean circuits whose leaves are block-outcome
  literals `lit b i` (the event `{v b = i}`).
* `CatCircuit.Decomposable` / `Deterministic` / `probDD` – the d-D
  structural predicates and the direct-summation evaluator, exactly as in
  `Provenance.Circuit` but over categorical blocks.

## Main results

* `CatAssignment.eventProb_and_disjoint` – **independence**:
  `Pr(E ∧ F) = Pr(E)·Pr(F)` when `E`, `F` depend on disjoint block sets.
* `CatAssignment.eventProb_or`, `eventProb_not` – inclusion-exclusion and
  complement.
* `CatAssignment.eventProb_lit`, `eventProb_block_mem` – leaf / marginal:
  `Pr(v b = i) = pᵢ` and `Pr(v b ∈ S) = Σ_{i∈S} pᵢ`.
* `CatCircuit.dD_eventProb_eq_probDD` – **the lifted d-D soundness theorem**:
  `Pr(⟦c⟧) = probDD c` for decomposable + deterministic categorical circuits.
* `CatAssignment.mulin_disjoint`, `mulin_or_prob`, `mulin_none` – the three
  block lemmas backing the deterministic-OR mark and the `1 - Σ pᵢ`
  none-branch.
* `CatAssignment.singleBlock_detOR_sound` – single-block soundness: the
  plain sum of a block's mulinput marginals equals the probability the
  block fires.

## References

* [Sen, Maniu & Senellart][sen2026provsql] (Section V-D)
* [Amarilli, Bourhis & Senellart][amarilli2015provenance], *Provenance Circuits
  for Trees and Treelike Instances* (ICALP 2015)
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type} [∀ b, Fintype (κ b)] [∀ b, DecidableEq (κ b)]

/-- A **categorical assignment**: for each block `b : ι`, a probability
distribution `prob b : κ b → ℚ` over that block's finite outcome type. This
is the categorical analogue of `ProbAssignment` (where every block would be
a single `Bool`). -/
structure CatAssignment (κ : ι → Type) [∀ b, Fintype (κ b)] where
  /-- The probability assigned to each outcome of each block. -/
  prob : (b : ι) → κ b → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ b i, 0 ≤ prob b i
  /-- Each block's outcome probabilities sum to `1`. -/
  sum_prob : ∀ b, ∑ i, prob b i = 1

namespace CatAssignment

variable (P : CatAssignment κ)

/-- Each individual outcome probability is at most `1` (it is one summand of
a sum of non-negatives equal to `1`). -/
theorem prob_le_one (b : ι) (i : κ b) : P.prob b i ≤ 1 := by
  have h := Finset.single_le_sum (f := fun j => P.prob b j)
    (fun j _ => P.prob_nonneg b j) (Finset.mem_univ i)
  rwa [P.sum_prob b] at h

/-- Probability of a categorical valuation `v`, the blocks independent:
`Pr(v) = ∏ b, P.prob b (v b)`. -/
def valProb (v : (b : ι) → κ b) : ℚ := ∏ b, P.prob b (v b)

/-- Probability of an event `E` over categorical valuations:
`Pr(E) = ∑_{v ⊨ E} Pr(v)`. -/
def eventProb (E : ((b : ι) → κ b) → Bool) : ℚ :=
  ∑ v : (b : ι) → κ b, if E v then P.valProb v else 0

theorem valProb_nonneg (v : (b : ι) → κ b) : 0 ≤ P.valProb v := by
  unfold valProb
  exact Finset.prod_nonneg (fun b _ => P.prob_nonneg b (v b))

/-- The categorical valuations form a probability distribution:
`∑ v, Pr(v) = 1`. -/
theorem sum_valProb_eq_one : ∑ v : (b : ι) → κ b, P.valProb v = 1 := by
  have hps : (∏ b : ι, ∑ i : κ b, P.prob b i)
      = ∑ v : (b : ι) → κ b, ∏ b : ι, P.prob b (v b) :=
    Fintype.prod_sum (fun (b : ι) (i : κ b) => P.prob b i)
  unfold valProb
  rw [← hps]
  simp_rw [P.sum_prob]
  simp

theorem eventProb_nonneg (E : ((b : ι) → κ b) → Bool) : 0 ≤ P.eventProb E := by
  unfold eventProb
  apply Finset.sum_nonneg
  intro v _
  by_cases hv : E v
  · simp [hv]; exact P.valProb_nonneg v
  · simp [hv]

theorem eventProb_le_one (E : ((b : ι) → κ b) → Bool) : P.eventProb E ≤ 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold eventProb
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : E v
  · simp [hv]
  · simp [hv]; exact P.valProb_nonneg v

/-- `Pr(false) = 0`. -/
theorem eventProb_false : P.eventProb (fun _ => false) = 0 := by
  unfold eventProb
  apply Finset.sum_eq_zero
  intro v _
  simp

/-- `Pr(true) = 1`. -/
theorem eventProb_true : P.eventProb (fun _ => true) = 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold eventProb
  apply Finset.sum_congr rfl
  intro v _
  simp

/-- Pointwise-equal events have equal probabilities. -/
theorem eventProb_congr {E F : ((b : ι) → κ b) → Bool} (h : ∀ v, E v = F v) :
    P.eventProb E = P.eventProb F := by
  unfold eventProb
  apply Finset.sum_congr rfl
  intro v _
  rw [h v]

end CatAssignment

/-! ### Support of an event -/

/-- `E` depends only on the blocks in `S`: any two valuations agreeing on
`S` give `E` the same value. The categorical analogue of
`BoolFunc.DependsOn`. -/
def EventDependsOn (E : ((b : ι) → κ b) → Bool) (S : Finset ι) : Prop :=
  ∀ v₁ v₂ : (b : ι) → κ b, (∀ b ∈ S, v₁ b = v₂ b) → E v₁ = E v₂

namespace CatAssignment

variable (P : CatAssignment κ)

/-! ### Leaf / marginal probabilities -/

/-- **Marginal.** The probability that block `b`'s outcome lies in a finset
`S` of outcomes is the sum of the corresponding marginals. The categorical
analogue of `funcProb_var`, proved by the same `Fintype.prod_sum`
column-swap. -/
theorem eventProb_block_mem (b : ι) (S : Finset (κ b)) :
    P.eventProb (fun v => decide (v b ∈ S)) = ∑ i ∈ S, P.prob b i := by
  -- `t` restricts block `b` to the outcomes in `S`, leaving every other block free.
  let t : (b' : ι) → Finset (κ b') :=
    Function.update (fun b' => (Finset.univ : Finset (κ b'))) b S
  have ht_b : t b = S := by simp [t]
  have ht_ne : ∀ b', b' ≠ b → t b' = Finset.univ := by intro b' hb'; simp [t, hb']
  -- The product of per-block sums collapses to the single `b`-factor.
  have hcollapse : (∏ b' : ι, ∑ j ∈ t b', P.prob b' j) = ∑ j ∈ S, P.prob b j := by
    rw [Finset.prod_eq_single (a := b)
          (fun b' _ hb' => by rw [ht_ne b' hb']; exact P.sum_prob b')
          (fun h => absurd (Finset.mem_univ b) h)]
    rw [ht_b]
  -- Rewriting the product-of-sums as a sum-over-`piFinset` of products (= valProb's).
  have hsum : (∑ x ∈ Fintype.piFinset t, ∏ b' : ι, P.prob b' (x b')) = ∑ j ∈ S, P.prob b j := by
    rw [← Finset.prod_univ_sum t (fun b' j => P.prob b' j)]; exact hcollapse
  rw [← hsum]
  unfold eventProb
  -- `piFinset t` is exactly the set of valuations with `v b ∈ S`.
  have hfilter : Fintype.piFinset t
      = Finset.univ.filter (fun v : (b' : ι) → κ b' => v b ∈ S) := by
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx; have hb := hx b; rwa [ht_b] at hb
    · intro hx b'; rcases eq_or_ne b' b with rfl | hb'
      · rwa [ht_b]
      · rw [ht_ne b' hb']; exact Finset.mem_univ _
  rw [hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v b ∈ S <;> simp [hv, valProb]

/-- **Leaf.** `Pr(v b = i) = pᵢ`. -/
theorem eventProb_lit (b : ι) (i : κ b) :
    P.eventProb (fun v => decide (v b = i)) = P.prob b i := by
  have h := P.eventProb_block_mem b {i}
  simp only [Finset.sum_singleton] at h
  rw [← h]
  apply P.eventProb_congr
  intro v
  simp [Finset.mem_singleton]

/-! ### Independence, inclusion-exclusion, complement -/

/-- **Independence lemma.** If `E` depends on block set `S` and `F` on block
set `T` with `S`, `T` disjoint, then `Pr(E ∧ F) = Pr(E) · Pr(F)`. The
categorical analogue of `funcProb_mul_disjoint`; the deterministic-AND /
decomposability soundness. -/
theorem eventProb_and_disjoint {E F : ((b : ι) → κ b) → Bool} {S T : Finset ι}
    (hE : EventDependsOn E S) (hF : EventDependsOn F T) (hST : Disjoint S T) :
    P.eventProb (fun v => E v && F v) = P.eventProb E * P.eventProb F := by
  -- `sum_prob` forces every block's outcome type to be nonempty.
  have hne : ∀ b', Nonempty (κ b') := by
    intro b'
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    haveI := hcon
    have h1 : (∑ i : κ b', P.prob b' i) = 0 := by rw [Finset.univ_eq_empty, Finset.sum_empty]
    rw [P.sum_prob b'] at h1
    exact one_ne_zero h1
  -- Split valuations along `S`.
  let e : ((b : ι) → κ b) ≃ ((x : {x // x ∈ S}) → κ ↑x) × ((x : {x // x ∉ S}) → κ ↑x) :=
    Equiv.piEquivPiSubtypeProd (fun b => b ∈ S) κ
  let glue : ((x : {x // x ∈ S}) → κ ↑x) → ((x : {x // x ∉ S}) → κ ↑x) → ((b : ι) → κ b) :=
    fun vS vR => e.symm (vS, vR)
  let v0S : (x : {x // x ∈ S}) → κ ↑x := fun x => (hne ↑x).some
  let v0R : (x : {x // x ∉ S}) → κ ↑x := fun x => (hne ↑x).some
  let eS : ((x : {x // x ∈ S}) → κ ↑x) → Bool := fun vS => E (glue vS v0R)
  let fR : ((x : {x // x ∉ S}) → κ ↑x) → Bool := fun vR => F (glue v0S vR)
  let pS : ((x : {x // x ∈ S}) → κ ↑x) → ℚ := fun vS => ∏ x : {x // x ∈ S}, P.prob ↑x (vS x)
  let pR : ((x : {x // x ∉ S}) → κ ↑x) → ℚ := fun vR => ∏ x : {x // x ∉ S}, P.prob ↑x (vR x)
  have hglue_in : ∀ vS vR (x : ι) (hx : x ∈ S), glue vS vR x = vS ⟨x, hx⟩ := by
    intro vS vR x hx
    show (e.symm (vS, vR)) x = vS ⟨x, hx⟩
    simp [e, Equiv.piEquivPiSubtypeProd, hx]
  have hglue_out : ∀ vS vR (x : ι) (hx : x ∉ S), glue vS vR x = vR ⟨x, hx⟩ := by
    intro vS vR x hx
    show (e.symm (vS, vR)) x = vR ⟨x, hx⟩
    simp [e, Equiv.piEquivPiSubtypeProd, hx]
  have hEeq : ∀ vS vR, E (glue vS vR) = eS vS := fun vS vR =>
    hE _ _ fun x hxS => by rw [hglue_in _ _ _ hxS, hglue_in _ _ _ hxS]
  have hFeq : ∀ vS vR, F (glue vS vR) = fR vR := fun vS vR =>
    hF _ _ fun x hxT => by
      have hxnS : x ∉ S := Finset.disjoint_right.mp hST hxT
      rw [hglue_out _ _ _ hxnS, hglue_out _ _ _ hxnS]
  have hval_split : ∀ vS vR, P.valProb (glue vS vR) = pS vS * pR vR := by
    intro vS vR
    show (∏ x, P.prob x ((glue vS vR) x))
          = (∏ x : {x // x ∈ S}, P.prob ↑x (vS x)) * (∏ x : {x // x ∉ S}, P.prob ↑x (vR x))
    rw [← Finset.prod_mul_prod_compl S (fun x => P.prob x ((glue vS vR) x))]
    congr 1
    · rw [Finset.prod_subtype (s := S) (p := fun x => x ∈ S) (fun _ => Iff.rfl)]
      refine Finset.prod_congr rfl ?_
      rintro ⟨x, hx⟩ _
      rw [hglue_in _ _ _ hx]
    · rw [Finset.prod_subtype (s := Sᶜ) (p := fun x => x ∉ S) (fun _ => by simp)]
      refine Finset.prod_congr rfl ?_
      rintro ⟨x, hx⟩ _
      rw [hglue_out _ _ _ hx]
  have sum_pS_eq_one : (∑ vS : (x : {x // x ∈ S}) → κ ↑x, pS vS) = 1 := by
    show (∑ vS : (x : {x // x ∈ S}) → κ ↑x, ∏ x : {x // x ∈ S}, P.prob ↑x (vS x)) = 1
    rw [← Fintype.prod_sum (fun (x : {x // x ∈ S}) (i : κ ↑x) => P.prob ↑x i)]
    exact Finset.prod_eq_one (fun x _ => P.sum_prob ↑x)
  have sum_pR_eq_one : (∑ vR : (x : {x // x ∉ S}) → κ ↑x, pR vR) = 1 := by
    show (∑ vR : (x : {x // x ∉ S}) → κ ↑x, ∏ x : {x // x ∉ S}, P.prob ↑x (vR x)) = 1
    rw [← Fintype.prod_sum (fun (x : {x // x ∉ S}) (i : κ ↑x) => P.prob ↑x i)]
    exact Finset.prod_eq_one (fun x _ => P.sum_prob ↑x)
  have hsum_iterated : ∀ G : ((b : ι) → κ b) → ℚ,
      (∑ v : (b : ι) → κ b, G v) = ∑ vS, ∑ vR, G (glue vS vR) := by
    intro G
    have h1 : (∑ v : (b : ι) → κ b, G v)
        = ∑ p : ((x : {x // x ∈ S}) → κ ↑x) × ((x : {x // x ∉ S}) → κ ↑x), G (e.symm p) :=
      (Equiv.sum_comp e.symm G).symm
    rw [h1]
    exact Fintype.sum_prod_type' (fun vS vR => G (glue vS vR))
  have hPr_E : P.eventProb E = ∑ vS, (if eS vS then pS vS else 0) := by
    show (∑ v, if E v then P.valProb v else 0) = ∑ vS, (if eS vS then pS vS else 0)
    rw [hsum_iterated (fun v => if E v then P.valProb v else 0)]
    refine Finset.sum_congr rfl ?_
    intro vS _
    simp_rw [hEeq vS, hval_split vS]
    by_cases hes : eS vS
    · simp_rw [if_pos hes]
      rw [← Finset.mul_sum, sum_pR_eq_one, mul_one]
    · simp_rw [if_neg hes]; simp
  have hPr_F : P.eventProb F = ∑ vR, (if fR vR then pR vR else 0) := by
    show (∑ v, if F v then P.valProb v else 0) = ∑ vR, (if fR vR then pR vR else 0)
    rw [hsum_iterated (fun v => if F v then P.valProb v else 0)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro vR _
    simp_rw [hFeq _ vR, hval_split _ vR]
    by_cases hfs : fR vR
    · simp_rw [if_pos hfs]
      rw [← Finset.sum_mul, sum_pS_eq_one, one_mul]
    · simp_rw [if_neg hfs]; simp
  show (∑ v, if (E v && F v) then P.valProb v else 0) = P.eventProb E * P.eventProb F
  rw [hsum_iterated (fun v => if (E v && F v) then P.valProb v else 0)]
  rw [hPr_E, hPr_F, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro vS _
  refine Finset.sum_congr rfl ?_
  intro vR _
  have hcomb : ((E (glue vS vR)) && (F (glue vS vR))) = (eS vS && fR vR) := by
    rw [hEeq, hFeq]
  rw [hcomb, hval_split]
  cases hf' : eS vS <;> cases hg' : fR vR <;> simp

/-- **Inclusion-exclusion.** `Pr(E ∨ F) = Pr(E) + Pr(F) - Pr(E ∧ F)`, with no
disjointness hypothesis. The categorical analogue of `funcProb_add_eq`. -/
theorem eventProb_or (E F : ((b : ι) → κ b) → Bool) :
    P.eventProb (fun v => E v || F v)
      = P.eventProb E + P.eventProb F - P.eventProb (fun v => E v && F v) := by
  unfold eventProb
  have hpoint : ∀ v : (b : ι) → κ b,
      (if (E v || F v) then P.valProb v else 0)
      = (if E v then P.valProb v else 0) + (if F v then P.valProb v else 0)
        - (if (E v && F v) then P.valProb v else 0) := by
    intro v
    cases hev : E v <;> cases hfv : F v <;> simp
  rw [show (∑ v : (b : ι) → κ b, if (E v || F v) then P.valProb v else 0)
        = ∑ v : (b : ι) → κ b,
            ((if E v then P.valProb v else 0) + (if F v then P.valProb v else 0)
            - (if (E v && F v) then P.valProb v else 0)) from
    Finset.sum_congr rfl (fun v _ => hpoint v)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-- **Complement.** `Pr(¬E) = 1 - Pr(E)`. -/
theorem eventProb_not (E : ((b : ι) → κ b) → Bool) :
    P.eventProb (fun v => !(E v)) = 1 - P.eventProb E := by
  unfold eventProb
  have hstep : (∑ v : (b : ι) → κ b, if (!(E v)) then P.valProb v else 0)
      = ∑ v : (b : ι) → κ b, (P.valProb v - (if E v then P.valProb v else 0)) := by
    apply Finset.sum_congr rfl
    intro v _
    cases hev : E v <;> simp
  rw [hstep, Finset.sum_sub_distrib, P.sum_valProb_eq_one]

end CatAssignment

/-! ## Categorical circuits and d-D soundness -/

/-- A Boolean circuit whose variable leaves are **block-outcome literals**:
`lit b i` denotes the event `{v | v b = i}`. Otherwise identical to
`Circuit`. -/
inductive CatCircuit (ι : Type) (κ : ι → Type) where
  /-- A Boolean constant. -/
  | const : Bool → CatCircuit ι κ
  /-- The leaf event `{v | v b = i}`. -/
  | lit : (b : ι) → κ b → CatCircuit ι κ
  /-- Logical negation. -/
  | not : CatCircuit ι κ → CatCircuit ι κ
  /-- Logical conjunction. -/
  | and : CatCircuit ι κ → CatCircuit ι κ → CatCircuit ι κ
  /-- Logical disjunction. -/
  | or : CatCircuit ι κ → CatCircuit ι κ → CatCircuit ι κ

namespace CatCircuit

/-- Evaluate a categorical circuit under a categorical valuation. -/
def eval : CatCircuit ι κ → ((b : ι) → κ b) → Bool
  | .const x, _ => x
  | .lit b i, v => decide (v b = i)
  | .not c, v => !(c.eval v)
  | .and c d, v => c.eval v && d.eval v
  | .or c d, v => c.eval v || d.eval v

/-- The event a circuit denotes. -/
def toEvent (c : CatCircuit ι κ) : ((b : ι) → κ b) → Bool := c.eval

/-- The set of blocks a circuit reads (the categorical "variable support"). -/
def blocks : CatCircuit ι κ → Finset ι
  | .const _ => ∅
  | .lit b _ => {b}
  | .not c => c.blocks
  | .and c d => c.blocks ∪ d.blocks
  | .or c d => c.blocks ∪ d.blocks

/-- **Decomposable**: every AND gate has children reading disjoint block
sets. -/
inductive Decomposable : CatCircuit ι κ → Prop
  | const : ∀ x, Decomposable (.const x)
  | lit : ∀ b i, Decomposable (.lit b i)
  | not : ∀ {c}, Decomposable c → Decomposable (.not c)
  | and : ∀ {c d}, Decomposable c → Decomposable d →
      Disjoint c.blocks d.blocks → Decomposable (.and c d)
  | or : ∀ {c d}, Decomposable c → Decomposable d → Decomposable (.or c d)

/-- **Deterministic**: every OR gate has children that are mutually exclusive
*as events* (their conjunction is unsatisfiable). This is the categorical
deterministic-OR mark: for the mulinput-OR of one block it is supplied by
`mulin_disjoint`. -/
inductive Deterministic : CatCircuit ι κ → Prop
  | const : ∀ x, Deterministic (.const x)
  | lit : ∀ b i, Deterministic (.lit b i)
  | not : ∀ {c}, Deterministic c → Deterministic (.not c)
  | and : ∀ {c d}, Deterministic c → Deterministic d → Deterministic (.and c d)
  | or : ∀ {c d}, Deterministic c → Deterministic d →
      (∀ v, (c.eval v && d.eval v) = false) → Deterministic (.or c d)

/-- The d-D direct-summation evaluator (categorical). Differs from a
read-once evaluator only at OR gates, which sum directly. -/
def probDD (P : CatAssignment κ) : CatCircuit ι κ → ℚ
  | .const true => 1
  | .const false => 0
  | .lit b i => P.prob b i
  | .not c => 1 - c.probDD P
  | .and c d => c.probDD P * d.probDD P
  | .or c d => c.probDD P + d.probDD P

/-- A circuit's event depends only on the blocks it reads. -/
lemma toEvent_dependsOn_blocks (c : CatCircuit ι κ) :
    EventDependsOn c.toEvent c.blocks := by
  intro v₁ v₂ heq
  unfold toEvent
  induction c with
  | const x => rfl
  | lit b i =>
    have hb : b ∈ (CatCircuit.lit b i).blocks := Finset.mem_singleton.mpr rfl
    show decide (v₁ b = i) = decide (v₂ b = i)
    rw [heq b hb]
  | not c ih =>
    change Bool.not (c.eval v₁) = Bool.not (c.eval v₂)
    rw [ih heq]
  | and c₁ c₂ ih₁ ih₂ =>
    have h₁ : ∀ x ∈ c₁.blocks, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_left _ hx)
    have h₂ : ∀ x ∈ c₂.blocks, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_right _ hx)
    show (c₁.eval v₁ && c₂.eval v₁) = (c₁.eval v₂ && c₂.eval v₂)
    rw [ih₁ h₁, ih₂ h₂]
  | or c₁ c₂ ih₁ ih₂ =>
    have h₁ : ∀ x ∈ c₁.blocks, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_left _ hx)
    have h₂ : ∀ x ∈ c₂.blocks, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_right _ hx)
    show (c₁.eval v₁ || c₂.eval v₁) = (c₁.eval v₂ || c₂.eval v₂)
    rw [ih₁ h₁, ih₂ h₂]

/-- **Lifted d-D soundness theorem.** For any decomposable + deterministic
categorical circuit `c`, the direct-summation evaluator `c.probDD P` agrees
with the weighted-model-counting semantics `Pr(⟦c⟧)`. This is
`Circuit.dD_funcProb_eq_probDD` lifted from free Boolean variables to
categorical block variables: AND uses `eventProb_and_disjoint`
(decomposability), OR uses `eventProb_or` with the determinism hypothesis
collapsing the inclusion-exclusion term, NOT uses `eventProb_not`. -/
theorem dD_eventProb_eq_probDD (P : CatAssignment κ) (c : CatCircuit ι κ)
    (hd : c.Decomposable) (hdet : c.Deterministic) :
    P.eventProb c.toEvent = c.probDD P := by
  induction c with
  | const x =>
    cases x
    · show P.eventProb (fun _ => false) = 0
      exact P.eventProb_false
    · show P.eventProb (fun _ => true) = 1
      exact P.eventProb_true
  | lit b i =>
    show P.eventProb (fun v => decide (v b = i)) = P.prob b i
    exact P.eventProb_lit b i
  | not c ih =>
    cases hd with
    | not hd' =>
      cases hdet with
      | not hdet' =>
        show P.eventProb (fun v => !(c.toEvent v)) = 1 - c.probDD P
        rw [P.eventProb_not c.toEvent, ih hd' hdet']
  | and c₁ c₂ ih₁ ih₂ =>
    cases hd with
    | and hd₁ hd₂ hdisj =>
      cases hdet with
      | and hdet₁ hdet₂ =>
        show P.eventProb (fun v => c₁.toEvent v && c₂.toEvent v) = c₁.probDD P * c₂.probDD P
        rw [P.eventProb_and_disjoint
              (toEvent_dependsOn_blocks c₁) (toEvent_dependsOn_blocks c₂) hdisj,
            ih₁ hd₁ hdet₁, ih₂ hd₂ hdet₂]
  | or c₁ c₂ ih₁ ih₂ =>
    cases hd with
    | or hd₁ hd₂ =>
      cases hdet with
      | or hdet₁ hdet₂ hexcl =>
        show P.eventProb (fun v => c₁.toEvent v || c₂.toEvent v) = c₁.probDD P + c₂.probDD P
        rw [P.eventProb_or c₁.toEvent c₂.toEvent]
        have hz : P.eventProb (fun v => c₁.toEvent v && c₂.toEvent v) = 0 := by
          rw [P.eventProb_congr (E := fun v => c₁.toEvent v && c₂.toEvent v)
                (F := fun _ => false) hexcl]
          exact P.eventProb_false
        rw [hz, sub_zero, ih₁ hd₁ hdet₁, ih₂ hd₂ hdet₂]

end CatCircuit

/-! ## The three block lemmas and single-block soundness

The payload backing `evaluateCertifiedIsland`'s trust in the
deterministic-OR mark of a `repair_key` block. A block is `b : ι`; its
outcomes are `κ b`, with a designated none-outcome `o : κ b` and the
*mulinputs* being all other outcomes `i ∈ univ.erase o`, with marginals
`pᵢ = P.prob b i`. -/

namespace CatAssignment

variable (P : CatAssignment κ)

/-- **`mulin_disjoint`.** Distinct mulinputs of one block are mutually
exclusive events: this is what licenses marking the block's mulinput-OR
deterministic (`CatCircuit.Deterministic.or`). -/
theorem mulin_disjoint (b : ι) {i j : κ b} (h : i ≠ j) :
    ∀ v : (b : ι) → κ b,
      ((CatCircuit.lit b i).eval v && (CatCircuit.lit b j).eval v) = false := by
  intro v
  show (decide (v b = i) && decide (v b = j)) = false
  by_cases hi : v b = i <;> by_cases hj : v b = j <;> simp_all

/-- **`mulin_or_prob`.** The probability that block `b` fires *some* mulinput
(its outcome is not the none-outcome `o`) is the exact sum of the mulinput
marginals: the plain sum `evaluateCertifiedIsland` computes is exact. -/
theorem mulin_or_prob (b : ι) (o : κ b) :
    P.eventProb (fun v => decide (v b ≠ o))
      = ∑ i ∈ Finset.univ.erase o, P.prob b i := by
  rw [← P.eventProb_block_mem b (Finset.univ.erase o)]
  apply P.eventProb_congr
  intro v
  simp [Finset.mem_erase]

/-- **`mulin_none`.** The none-branch probability is `1 - Σ pᵢ`, the
`monus(one, plus(mulinputs))` the evaluator reads. -/
theorem mulin_none (b : ι) (o : κ b) :
    P.eventProb (fun v => decide (v b = o))
      = 1 - ∑ i ∈ Finset.univ.erase o, P.prob b i := by
  rw [P.eventProb_lit b o]
  have hsplit : P.prob b o + ∑ i ∈ Finset.univ.erase o, P.prob b i = 1 := by
    rw [Finset.add_sum_erase Finset.univ (fun i => P.prob b i) (Finset.mem_univ o)]
    exact P.sum_prob b
  linarith

/-- **Single-block soundness.** Plain-summing the marginals of a block's
mulinputs (exactly what `evaluateCertifiedIsland` does for the marked
deterministic OR) equals the probability that the block fires. Combines
`eventProb_lit` and `mulin_or_prob`; it is the single-block instance of
`CatCircuit.dD_eventProb_eq_probDD`. -/
theorem singleBlock_detOR_sound (b : ι) (o : κ b) :
    (∑ i ∈ Finset.univ.erase o, P.eventProb (fun v => decide (v b = i)))
      = P.eventProb (fun v => decide (v b ≠ o)) := by
  rw [P.mulin_or_prob b o]
  apply Finset.sum_congr rfl
  intro i _
  exact P.eventProb_lit b i

end CatAssignment
