import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod

import Provenance.Probability
import Provenance.Semirings.BoolFunc

/-!
# Boolean circuits and read-once correctness

This file formalises Boolean circuits over a set `X` of variables, together
with a recursive bottom-up probability evaluator and the **read-once
correctness theorem**: for any read-once circuit, the recursive evaluator
(`Pr(c) = ⊙(Pr(c₁), Pr(c₂))` with `⊙` depending on the gate type) agrees with
the sum-over-valuations probabilistic semantics of its denotation as a
`BoolFunc X` (i.e., `Pr(c.toBoolFunc) = ∑_{v ⊨ c} Pr(v)`).

This is the formal counterpart of Section V-D step 1 of [Sen, Maniu &
Senellart, *ProvSQL: A General System for Keeping Track of the Provenance
and Probability of Data*][sen2026provsql]: on a read-once Boolean circuit,
each gate's probability is computed in `O(1)` from those of its two
children. The bottom-up evaluator is correct under the independence
induced by the read-once structure.

## Main definitions

* `Circuit X` – inductive Boolean circuit (constants, variables, NOT,
  AND, OR).
* `Circuit.eval` – evaluation under a valuation `v : X → Bool`.
* `Circuit.toBoolFunc` – view a circuit as a `BoolFunc X`.
* `Circuit.vars` – the variables used by a circuit (as a `Finset`).
* `Circuit.ReadOnce` – the gate-by-gate disjoint-supports predicate.
* `Circuit.prob` – the recursive bottom-up probability evaluator.

## Main results

* `BoolFunc.DependsOn` – `f` depends only on a Finset of variables.
* `Circuit.toBoolFunc_dependsOn_vars` – a circuit's denotation depends
  only on its variables.
* `ProbAssignment.funcProb_mul_disjoint` – the **independence lemma**:
  `Pr(f * g) = Pr(f) * Pr(g)` whenever `f`, `g` depend on disjoint
  variable supports.
* `Circuit.readOnce_funcProb_eq_prob` – the **read-once correctness
  theorem**: for any `ReadOnce` circuit `c`,
  `Pr(c.toBoolFunc) = c.prob P`.

## References

* [Sen, Maniu & Senellart][sen2026provsql] (Section V-D step 1)
-/

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Boolean circuit over a set `X` of variables. -/
inductive Circuit (X : Type) where
  /-- A Boolean constant. -/
  | const : Bool → Circuit X
  /-- A variable leaf. -/
  | var : X → Circuit X
  /-- Logical negation. -/
  | not : Circuit X → Circuit X
  /-- Logical conjunction. -/
  | and : Circuit X → Circuit X → Circuit X
  /-- Logical disjunction. -/
  | or : Circuit X → Circuit X → Circuit X
  deriving Repr

namespace Circuit

/-- Evaluate a circuit under a Boolean valuation. -/
def eval {X : Type} : Circuit X → (X → Bool) → Bool
  | .const b, _ => b
  | .var x, v => v x
  | .not c, v => !(c.eval v)
  | .and c₁ c₂, v => c₁.eval v && c₂.eval v
  | .or c₁ c₂, v => c₁.eval v || c₂.eval v

/-- A circuit's denotation as a `BoolFunc`. -/
def toBoolFunc {X : Type} (c : Circuit X) : BoolFunc X := c.eval

/-- The variables used by a circuit, as a `Finset`. -/
def vars : Circuit X → Finset X
  | .const _ => ∅
  | .var x => {x}
  | .not c => c.vars
  | .and c₁ c₂ => c₁.vars ∪ c₂.vars
  | .or c₁ c₂ => c₁.vars ∪ c₂.vars

/-- A circuit is **read-once** when each gate's two children have disjoint
variable supports. Constants and variables are read-once by definition;
NOT is read-once if its argument is. -/
inductive ReadOnce : Circuit X → Prop
  | const : ∀ b, ReadOnce (.const b)
  | var : ∀ x, ReadOnce (.var x)
  | not : ∀ {c}, ReadOnce c → ReadOnce (.not c)
  | and : ∀ {c₁ c₂}, ReadOnce c₁ → ReadOnce c₂ →
      Disjoint c₁.vars c₂.vars → ReadOnce (.and c₁ c₂)
  | or : ∀ {c₁ c₂}, ReadOnce c₁ → ReadOnce c₂ →
      Disjoint c₁.vars c₂.vars → ReadOnce (.or c₁ c₂)

/-- The recursive bottom-up probability evaluator. Each gate combines the
probabilities of its children in `O(1)`, with the formula depending on the
gate type. -/
def prob {X : Type} (P : ProbAssignment X) : Circuit X → ℚ
  | .const true => 1
  | .const false => 0
  | .var x => P.prob x
  | .not c => 1 - c.prob P
  | .and c₁ c₂ => c₁.prob P * c₂.prob P
  | .or c₁ c₂ => c₁.prob P + c₂.prob P - c₁.prob P * c₂.prob P

end Circuit

/-! ### `BoolFunc.DependsOn`: support of a Boolean function -/

/-- `f` depends only on the variables in `S`: any two valuations agreeing
on `S` produce the same value. This is the standard notion of "support". -/
def BoolFunc.DependsOn {X : Type} (f : BoolFunc X) (S : Finset X) : Prop :=
  ∀ v₁ v₂ : X → Bool, (∀ x ∈ S, v₁ x = v₂ x) → f v₁ = f v₂

namespace Circuit

end Circuit

/-! ### Auxiliary `funcProb` lemmas

These bridge the recursive evaluator `Circuit.prob` to the sum-over-valuations
semantics `ProbAssignment.funcProb`. They are stated for arbitrary `BoolFunc X`,
not specifically for circuit denotations, so that `Circuit.readOnce_funcProb_eq_prob`
can be obtained by case analysis on the `ReadOnce` derivation.
-/

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- `Pr(var i) = Pr(i)`: the probability of the single-variable Boolean function
equals the variable's own probability. Proved by reorganising the sum
`∑_v if v i then valProb v else 0` as a product `∏_y h_y(v y)` and applying
`Fintype.prod_sum` (the same swap used in `sum_valProb_eq_one`). -/
theorem funcProb_var (i : X) :
    P.funcProb (BoolFunc.var i) = P.prob i := by
  -- Local helper: factor at y, depending on v y.
  -- For y = i: contributes `b ↦ if b then Pr(i) else 0` (kills the `v i = false` case).
  -- For y ≠ i: contributes the usual `P̃_y(b)`.
  let h : X → Bool → ℚ := fun y b =>
    if y = i then (if b then P.prob i else 0)
    else (if b then P.prob y else 1 - P.prob y)
  -- The product ∏_y h y (v y) equals (if v i then valProb v else 0).
  have hprod : ∀ v : X → Bool,
      (∏ y, h y (v y)) = if (v i : Bool) then P.valProb v else 0 := by
    intro v
    by_cases hvi : v i = true
    · -- v i = true: factor at i is P.prob i = P̃_i(true), so the product reduces to valProb v.
      simp only [hvi, if_true]
      unfold valProb
      apply Finset.prod_congr rfl
      intro y _
      by_cases hy : y = i
      · subst hy
        simp only [h, if_pos rfl, hvi, if_true]
      · simp only [h, if_neg hy]
    · -- v i = false: factor at i is 0, so the product vanishes.
      have hvi' : v i = false := by
        cases hv : v i
        · rfl
        · exact absurd hv hvi
      simp only [hvi']
      apply Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
      simp only [h, if_pos rfl, hvi']
      rfl
  -- Per-variable sum: contributes `P.prob i` at `y = i`, and `1` elsewhere.
  have hsum : ∀ y, (∑ b, h y b) = if y = i then P.prob i else 1 := by
    intro y
    by_cases hy : y = i
    · subst hy
      simp only [h, if_pos rfl]
      have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
          Finset.sum_singleton]
      simp
    · simp only [h, if_neg hy]
      have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
          Finset.sum_singleton]
      simp
  -- Apply Fintype.prod_sum (∏∑ = ∑∏) in reverse.
  have hswap : (∑ v : X → Bool, ∏ y, h y (v y)) = ∏ y, ∑ b, h y b :=
    (Fintype.prod_sum h).symm
  -- Goal: rewrite funcProb's sum to match.
  show (∑ v : X → Bool, if (BoolFunc.var i v : Bool) then P.valProb v else 0) = P.prob i
  have hvar : ∀ v : X → Bool, BoolFunc.var i v = v i := fun _ => rfl
  have hstep1 : (∑ v : X → Bool, if (BoolFunc.var i v : Bool) then P.valProb v else 0)
              = ∑ v : X → Bool, ∏ y, h y (v y) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [hvar v, ← hprod v]
  rw [hstep1, hswap]
  -- Now: ∏ y, ∑ b, h y b = P.prob i
  have hstep2 : (∏ y, ∑ b, h y b) = ∏ y, if y = i then P.prob i else (1 : ℚ) := by
    apply Finset.prod_congr rfl
    intro y _
    exact hsum y
  rw [hstep2]
  rw [Finset.prod_ite_eq' Finset.univ i (fun _ => P.prob i)]
  simp

/-- `Pr(¬f) = 1 - Pr(f)`: probability of a Boolean complement. In `BoolFunc X`,
`1 - f` is pointwise `f v && !(f v)`-style Boolean subtraction, which on the
constant-true `1` reduces to `Bool.not ∘ f`. The proof splits each summand by
`f v` and uses `sum_valProb_eq_one`. -/
theorem funcProb_sub_self_const_one (f : BoolFunc X) :
    P.funcProb (1 - f) = 1 - P.funcProb f := by
  unfold funcProb
  -- Rewrite each `(1 - f) v` to `!(f v)` and split the sum by cases on `f v`.
  have hsub : ∀ v : X → Bool, (1 - f : BoolFunc X) v = !(f v) := by
    intro v
    show ((1 : BoolFunc X) v && !(f v) : Bool) = !(f v)
    have h1 : (1 : BoolFunc X) v = true := rfl
    rw [h1]; simp
  have hstep :
      (∑ v : X → Bool, if ((1 - f : BoolFunc X) v : Bool) then P.valProb v else 0)
      = ∑ v : X → Bool, (P.valProb v - (if (f v : Bool) then P.valProb v else 0)) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [hsub v]
    by_cases hfv : f v = true
    · simp [hfv]
    · have hfv' : f v = false := by
        cases h : f v with
        | false => rfl
        | true => exact absurd h hfv
      simp [hfv']
  rw [hstep, Finset.sum_sub_distrib, P.sum_valProb_eq_one]

/-! ### Independence lemma

The independence lemma `funcProb_mul_disjoint` is the technical heart of the
read-once correctness theorem: `Pr(f * g) = Pr(f) * Pr(g)` whenever `f` and `g`
depend on disjoint variable supports. The proof requires splitting
`(X → Bool) ≃ ({x // x ∈ S} → Bool) × ({x // x ∉ S} → Bool)` via
`Equiv.piEquivPiSubtypeProd` and factoring the valuation probability over the
partition. The full Lean formalisation is currently parked as a `sorry`; the
mathematical argument is documented below. -/

/-- **Independence lemma (parked).** If `f`, `g : BoolFunc X` depend on disjoint
variable supports `S`, `T`, then `Pr(f * g) = Pr(f) * Pr(g)`.

**Proof sketch.** Use `Equiv.piEquivPiSubtypeProd` to split each valuation
`v : X → Bool` into `(v|S, v|Sᶜ)`. The valuation probability factors as
`valProb v = (∏_{x ∈ S} P̃_x(v x)) · (∏_{x ∉ S} P̃_x(v x))`
via `Finset.prod_compl_mul_prod`. Since `f` depends only on `S`, the truth
value of `f v` only depends on `v|S`; similarly `g v` only depends on
`v|T ⊆ v|Sᶜ`. The double sum then factors as
`Pr(f * g) = (∑_{vS} (∏_S P̃) · 1_f(vS)) · (∑_{vR} (∏_Sᶜ P̃) · 1_g(vR))
           = Pr(f) · Pr(g)`,
using `sum_valProb_eq_one` restricted to subsets for the marginalisation. -/
theorem funcProb_mul_disjoint {f g : BoolFunc X} {S T : Finset X}
    (_hf : f.DependsOn S) (_hg : g.DependsOn T) (_hST : Disjoint S T) :
    P.funcProb (f * g) = P.funcProb f * P.funcProb g := by
  sorry

/-- `Pr(f + g) = Pr(f) + Pr(g) - Pr(f * g)`: the universal inclusion-exclusion
identity for the BoolFunc disjunction (`+`) and conjunction (`*`). No
disjointness hypothesis is needed; the formula holds pointwise on each summand
via the Bool identity `(b₁ || b₂).toℚ = b₁.toℚ + b₂.toℚ - (b₁ && b₂).toℚ`. -/
theorem funcProb_add_eq (f g : BoolFunc X) :
    P.funcProb (f + g) = P.funcProb f + P.funcProb g - P.funcProb (f * g) := by
  unfold funcProb
  -- The Bool identity, lifted to the ℚ-weighted sum.
  have hpoint : ∀ v : X → Bool,
      (if ((f + g : BoolFunc X) v : Bool) then P.valProb v else 0)
      = (if (f v : Bool) then P.valProb v else 0)
        + (if (g v : Bool) then P.valProb v else 0)
        - (if ((f * g : BoolFunc X) v : Bool) then P.valProb v else 0) := by
    intro v
    show (if (f v || g v : Bool) then P.valProb v else 0)
        = (if (f v : Bool) then P.valProb v else 0)
          + (if (g v : Bool) then P.valProb v else 0)
          - (if ((f v && g v : Bool)) then P.valProb v else 0)
    cases hfv : f v <;> cases hgv : g v <;> simp
  rw [show (∑ v : X → Bool, if ((f + g : BoolFunc X) v : Bool) then P.valProb v else 0)
        = ∑ v : X → Bool,
            ((if (f v : Bool) then P.valProb v else 0)
            + (if (g v : Bool) then P.valProb v else 0)
            - (if ((f * g : BoolFunc X) v : Bool) then P.valProb v else 0)) from
    Finset.sum_congr rfl (fun v _ => hpoint v)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

end ProbAssignment

namespace Circuit

omit [Fintype X] in
/-- A circuit's denotation depends only on its variables. -/
lemma toBoolFunc_dependsOn_vars (c : Circuit X) :
    c.toBoolFunc.DependsOn c.vars := by
  intro v₁ v₂ heq
  unfold toBoolFunc
  induction c with
  | const b => rfl
  | var x =>
    have hx : x ∈ vars (.var x : Circuit X) := Finset.mem_singleton.mpr rfl
    exact heq x hx
  | not c ih =>
    change Bool.not (c.eval v₁) = Bool.not (c.eval v₂)
    rw [ih heq]
  | and c₁ c₂ ih₁ ih₂ =>
    have h₁ : ∀ x ∈ c₁.vars, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_left _ hx)
    have h₂ : ∀ x ∈ c₂.vars, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_right _ hx)
    change (c₁.eval v₁ && c₂.eval v₁ : Bool) = (c₁.eval v₂ && c₂.eval v₂ : Bool)
    rw [ih₁ h₁, ih₂ h₂]
  | or c₁ c₂ ih₁ ih₂ =>
    have h₁ : ∀ x ∈ c₁.vars, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_left _ hx)
    have h₂ : ∀ x ∈ c₂.vars, v₁ x = v₂ x :=
      fun x hx => heq x (Finset.mem_union_right _ hx)
    change (c₁.eval v₁ || c₂.eval v₁ : Bool) = (c₁.eval v₂ || c₂.eval v₂ : Bool)
    rw [ih₁ h₁, ih₂ h₂]

/-! ### Read-once correctness -/

/-- **Read-once correctness theorem.** For any read-once Boolean circuit `c`,
the recursive bottom-up probability evaluator `c.prob P` agrees with the
sum-over-valuations semantics `Pr(c.toBoolFunc)`. Proved by induction on the
`ReadOnce` derivation, using:

* `ProbAssignment.funcProb_var` for the variable leaves;
* `ProbAssignment.funcProb_sub_self_const_one` for NOT (`Pr(¬f) = 1 - Pr(f)`);
* `ProbAssignment.funcProb_mul_disjoint` for AND (independence under disjoint
  supports);
* `ProbAssignment.funcProb_add_eq` together with the independence lemma for OR. -/
theorem readOnce_funcProb_eq_prob (c : Circuit X) (hc : c.ReadOnce) :
    P.funcProb c.toBoolFunc = c.prob P := by
  induction hc with
  | const b =>
    cases b
    · show P.funcProb (0 : BoolFunc X) = 0
      exact P.funcProb_zero
    · show P.funcProb (1 : BoolFunc X) = 1
      exact P.funcProb_one
  | var x =>
    show P.funcProb (BoolFunc.var x) = P.prob x
    exact P.funcProb_var x
  | @not c _ ih =>
    show P.funcProb (1 - c.toBoolFunc) = 1 - c.prob P
    rw [P.funcProb_sub_self_const_one c.toBoolFunc, ih]
  | @and c₁ c₂ _ _ hdisj ih₁ ih₂ =>
    show P.funcProb (c₁.toBoolFunc * c₂.toBoolFunc) = c₁.prob P * c₂.prob P
    rw [P.funcProb_mul_disjoint
          (toBoolFunc_dependsOn_vars c₁)
          (toBoolFunc_dependsOn_vars c₂)
          hdisj, ih₁, ih₂]
  | @or c₁ c₂ _ _ hdisj ih₁ ih₂ =>
    show P.funcProb (c₁.toBoolFunc + c₂.toBoolFunc)
        = c₁.prob P + c₂.prob P - c₁.prob P * c₂.prob P
    rw [P.funcProb_add_eq c₁.toBoolFunc c₂.toBoolFunc]
    rw [P.funcProb_mul_disjoint
          (toBoolFunc_dependsOn_vars c₁)
          (toBoolFunc_dependsOn_vars c₂)
          hdisj]
    rw [ih₁, ih₂]

end Circuit
