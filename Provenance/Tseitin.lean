import Provenance.Circuit

/-!
# Tseitin CNF encoding of Boolean circuits

This file formalises the **Tseitin transformation**, which encodes a Boolean
circuit `c : Circuit X` as an equisatisfiable CNF over the extended variable
set `X ⊕ Circuit X`. Each sub-circuit becomes an auxiliary variable, and the
CNF clauses encode `aux(g) ↔ <gate operation on aux variables of children>`.

The transformation is purely structural and produces a CNF whose size is
linear in the size of the circuit. It is the standard pre-processing step
used before feeding a Boolean formula to a SAT solver or a knowledge
compiler (`c2d`, `d4`, `DSHARP`); see Section V-D step 3 of [Sen, Maniu &
Senellart, *ProvSQL: A General System for Keeping Track of the Provenance
and Probability of Data*][sen2026provsql].

The main correctness result is `Circuit.tseitin_equisat`: a circuit is
satisfiable iff its Tseitin CNF encoding is satisfiable. The proof is the
explicit bijection between models of the circuit and models of the CNF:
each valuation `v : X → Bool` lifts uniquely to a `(X ⊕ Circuit X) → Bool`
that satisfies the CNF iff `c.eval v = true`, and any model of the CNF
restricted to the original variables is a model of the circuit.

## Main definitions

* `Literal X`, `Clause X`, `CNF X` – syntactic CNF infrastructure with
  `eval` semantics.
* `Circuit.gateClauses` – per-gate Tseitin clauses encoding
  `aux(c) ↔ ...` (no recursion into sub-circuits).
* `Circuit.tseitinClauses` – the full recursive clause set covering every
  sub-circuit.
* `Circuit.tseitin` – the Tseitin CNF: gate clauses plus a unit clause
  asserting that the root's aux variable is `true`.
* `Circuit.tseitinValuation` – the canonical lift of a valuation
  `v : X → Bool` to `(X ⊕ Circuit X) → Bool` (aux variables receive their
  sub-circuit's evaluation under `v`).

## Main results

* `Circuit.tseitin_eval_tseitinValuation` – `CNF.eval c.tseitin
  (tseitinValuation v) = c.eval v`: the lifted valuation always satisfies
  the per-gate clauses, and the root assertion exactly tracks the
  circuit's truth value.
* `Circuit.tseitin_models_restrict` – any model `w` of `c.tseitin`
  restricts (via `Sum.inl`) to a model of `c`.
* `Circuit.tseitin_equisat` – the bidirectional **equisatisfiability**
  theorem.

## References

* [Sen, Maniu & Senellart][sen2026provsql] (Section V-D step 3)
-/

/-- A literal: a variable together with a polarity flag. `isPos = true`
means the positive literal `var`, `isPos = false` means the negative
literal `¬var`. -/
structure Literal (X : Type) where
  /-- The variable underlying the literal. -/
  var : X
  /-- Polarity: `true` for positive, `false` for negative. -/
  isPos : Bool
  deriving Repr

namespace Literal

/-- Evaluate a literal under a valuation. -/
def eval {X : Type} (l : Literal X) (v : X → Bool) : Bool :=
  if l.isPos then v l.var else !(v l.var)

end Literal

/-- A clause: a disjunction of literals, represented as a `List`. The
empty clause is unsatisfiable. -/
abbrev Clause (X : Type) := List (Literal X)

namespace Clause

/-- A clause is satisfied iff some literal in it evaluates to `true`. -/
def eval {X : Type} (c : Clause X) (v : X → Bool) : Bool :=
  c.any (fun l => l.eval v)

end Clause

/-- A CNF formula: a conjunction of clauses. The empty conjunction is
satisfied vacuously (equal to `true`). -/
abbrev CNF (X : Type) := List (Clause X)

namespace CNF

/-- A CNF formula is satisfied iff every clause is satisfied. -/
def eval {X : Type} (φ : CNF X) (v : X → Bool) : Bool :=
  φ.all (fun c => Clause.eval c v)

/-- The Boolean function denoted by a CNF formula. -/
def toBoolFunc {X : Type} (φ : CNF X) : BoolFunc X := eval φ

@[simp] lemma eval_nil {X : Type} (v : X → Bool) :
    CNF.eval ([] : CNF X) v = true := rfl

@[simp] lemma eval_cons {X : Type} (c : Clause X) (φ : CNF X) (v : X → Bool) :
    CNF.eval (c :: φ : CNF X) v = (Clause.eval c v && CNF.eval φ v) := rfl

lemma eval_append {X : Type} (φ ψ : CNF X) (v : X → Bool) :
    CNF.eval (φ ++ ψ : CNF X) v = (CNF.eval φ v && CNF.eval ψ v) := by
  show List.all (φ ++ ψ) _ = _
  rw [List.all_append]
  rfl

end CNF

namespace Circuit

variable {X : Type}

/-- Per-gate Tseitin clauses encoding `aux(c) ↔ <gate operation on aux of children>`.
Does not recurse into sub-circuits — see `Circuit.tseitinClauses` for the
full recursive collection. -/
def gateClauses : Circuit X → CNF (X ⊕ Circuit X)
  | .const true =>
      [ [⟨Sum.inr (.const true), true⟩] ]
  | .const false =>
      [ [⟨Sum.inr (.const false), false⟩] ]
  | .var x =>
      [ [⟨Sum.inr (.var x), false⟩, ⟨Sum.inl x, true⟩],
        [⟨Sum.inr (.var x), true⟩, ⟨Sum.inl x, false⟩] ]
  | .not c' =>
      [ [⟨Sum.inr (.not c'), false⟩, ⟨Sum.inr c', false⟩],
        [⟨Sum.inr (.not c'), true⟩, ⟨Sum.inr c', true⟩] ]
  | .and c₁ c₂ =>
      [ [⟨Sum.inr (.and c₁ c₂), false⟩, ⟨Sum.inr c₁, true⟩],
        [⟨Sum.inr (.and c₁ c₂), false⟩, ⟨Sum.inr c₂, true⟩],
        [⟨Sum.inr (.and c₁ c₂), true⟩, ⟨Sum.inr c₁, false⟩, ⟨Sum.inr c₂, false⟩] ]
  | .or c₁ c₂ =>
      [ [⟨Sum.inr (.or c₁ c₂), true⟩, ⟨Sum.inr c₁, false⟩],
        [⟨Sum.inr (.or c₁ c₂), true⟩, ⟨Sum.inr c₂, false⟩],
        [⟨Sum.inr (.or c₁ c₂), false⟩, ⟨Sum.inr c₁, true⟩, ⟨Sum.inr c₂, true⟩] ]

/-- The full recursive Tseitin clause set: per-gate clauses for the current
node, plus all the clauses for its sub-circuits. -/
def tseitinClauses : Circuit X → CNF (X ⊕ Circuit X)
  | .const b => (Circuit.const b : Circuit X).gateClauses
  | .var x => (Circuit.var x : Circuit X).gateClauses
  | .not c' => (Circuit.not c').gateClauses ++ c'.tseitinClauses
  | .and c₁ c₂ =>
      (Circuit.and c₁ c₂).gateClauses ++ c₁.tseitinClauses ++ c₂.tseitinClauses
  | .or c₁ c₂ =>
      (Circuit.or c₁ c₂).gateClauses ++ c₁.tseitinClauses ++ c₂.tseitinClauses

/-- The **Tseitin CNF encoding**: a unit clause asserting that the root's
aux variable is `true`, followed by all per-gate sub-circuit clauses. -/
def tseitin (c : Circuit X) : CNF (X ⊕ Circuit X) :=
  [⟨Sum.inr c, true⟩] :: c.tseitinClauses

/-- The canonical lift of an original-variable valuation `v : X → Bool` to
the Tseitin variable space `X ⊕ Circuit X`: original variables map to
their `v`-value, aux variables map to the corresponding sub-circuit's
evaluation under `v`. -/
def tseitinValuation (v : X → Bool) : (X ⊕ Circuit X) → Bool
  | Sum.inl x => v x
  | Sum.inr c => c.eval v

@[simp] lemma tseitinValuation_inl (v : X → Bool) (x : X) :
    tseitinValuation v (Sum.inl x) = v x := rfl

@[simp] lemma tseitinValuation_inr (v : X → Bool) (c : Circuit X) :
    tseitinValuation v (Sum.inr c) = c.eval v := rfl

/-! ### Forward direction: every model of the circuit lifts to a model of
the Tseitin CNF. -/

/-- Every per-gate Tseitin clause is satisfied by the lifted valuation.
The proof is structural induction on the circuit, with each case
discharged by case analysis on the Boolean value of the children. -/
lemma tseitinClauses_eval_tseitinValuation (c : Circuit X) (v : X → Bool) :
    CNF.eval c.tseitinClauses (tseitinValuation v) = true := by
  induction c with
  | const b =>
    cases b <;>
      simp [tseitinClauses, gateClauses, CNF.eval, Clause.eval, Literal.eval,
            tseitinValuation, Circuit.eval]
  | var x =>
    simp only [tseitinClauses, gateClauses, CNF.eval, Clause.eval, Literal.eval,
               tseitinValuation, Circuit.eval, List.all_cons, List.all_nil,
               List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
    cases v x <;> simp
  | not c' ih =>
    rw [tseitinClauses, CNF.eval_append]
    refine (Bool.and_eq_true_iff).mpr ⟨?_, ih⟩
    -- Per-gate clauses for `not c'`: tautology in `c'.eval v` under tseitinValuation.
    simp only [gateClauses, CNF.eval, Clause.eval, Literal.eval,
               tseitinValuation, Circuit.eval, List.all_cons, List.all_nil,
               List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
    cases c'.eval v <;> simp
  | and c₁ c₂ ih₁ ih₂ =>
    rw [tseitinClauses, CNF.eval_append, CNF.eval_append]
    refine (Bool.and_eq_true_iff).mpr ⟨(Bool.and_eq_true_iff).mpr ⟨?_, ih₁⟩, ih₂⟩
    simp only [gateClauses, CNF.eval, Clause.eval, Literal.eval,
               tseitinValuation, Circuit.eval, List.all_cons, List.all_nil,
               List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
    cases c₁.eval v <;> cases c₂.eval v <;> simp
  | or c₁ c₂ ih₁ ih₂ =>
    rw [tseitinClauses, CNF.eval_append, CNF.eval_append]
    refine (Bool.and_eq_true_iff).mpr ⟨(Bool.and_eq_true_iff).mpr ⟨?_, ih₁⟩, ih₂⟩
    simp only [gateClauses, CNF.eval, Clause.eval, Literal.eval,
               tseitinValuation, Circuit.eval, List.all_cons, List.all_nil,
               List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
    cases c₁.eval v <;> cases c₂.eval v <;> simp

/-- The Tseitin CNF evaluates under the lifted valuation to exactly the
circuit's truth value: the unit root clause `[(aux(c), +)]` is satisfied
iff `c.eval v = true`, and all other clauses are tautologically satisfied
under the lift. -/
theorem tseitin_eval_tseitinValuation (c : Circuit X) (v : X → Bool) :
    CNF.eval c.tseitin (tseitinValuation v) = c.eval v := by
  show CNF.eval ([⟨Sum.inr c, true⟩] :: c.tseitinClauses) (tseitinValuation v)
        = c.eval v
  rw [CNF.eval_cons, tseitinClauses_eval_tseitinValuation, Bool.and_true]
  -- The remaining root clause `[(aux(c), +)]` evaluates to aux(c) = c.eval v.
  simp [Clause.eval, Literal.eval, tseitinValuation]

/-! ### Backward direction: every model of the Tseitin CNF restricts to a
model of the circuit. -/

/-- If the per-gate Tseitin clauses for a circuit `c` are all satisfied by
a valuation `w`, then `w` correctly evaluates `c`'s root aux variable to
`c.eval (w ∘ Sum.inl)`. Proved by induction on `c`: each gate's clauses
encode the iff `aux(c) ↔ <gate on children's aux>`, and the IH supplies
the children's correctness. -/
lemma tseitinClauses_imp_root (c : Circuit X)
    (w : (X ⊕ Circuit X) → Bool)
    (hw : CNF.eval c.tseitinClauses w = true) :
    w (Sum.inr c) = c.eval (fun x => w (Sum.inl x)) := by
  induction c with
  | const b =>
    cases b
    · -- const false: gate clause `[(aux, -)]` forces aux to be false.
      have h := hw
      simp only [tseitinClauses, gateClauses, CNF.eval, Clause.eval,
                 List.all_cons, List.all_nil, List.any_cons, List.any_nil,
                 Literal.eval, Bool.and_true, Bool.or_false] at h
      show w (Sum.inr (Circuit.const false : Circuit X)) = false
      cases hwc : w (Sum.inr (Circuit.const false : Circuit X)) <;>
        simp [hwc] at h
      rfl
    · -- const true: gate clause `[(aux, +)]` forces aux to be true.
      have h := hw
      simp only [tseitinClauses, gateClauses, CNF.eval, Clause.eval,
                 List.all_cons, List.all_nil, List.any_cons, List.any_nil,
                 Literal.eval, Bool.and_true, Bool.or_false] at h
      show w (Sum.inr (Circuit.const true : Circuit X)) = true
      exact h
  | var x =>
    -- Two biconditional clauses for `aux ↔ x`.
    have h := hw
    simp only [tseitinClauses, gateClauses, CNF.eval, Clause.eval,
               List.all_cons, List.all_nil, List.any_cons, List.any_nil,
               Literal.eval, Bool.and_true, Bool.or_false] at h
    show w (Sum.inr (Circuit.var x : Circuit X)) = w (Sum.inl x)
    cases hwa : w (Sum.inr (Circuit.var x : Circuit X)) <;>
      cases hwx : w (Sum.inl x) <;>
      simp [hwa, hwx] at h
    all_goals rfl
  | not c' ih =>
    rw [tseitinClauses, CNF.eval_append] at hw
    obtain ⟨hgate, hsub⟩ := Bool.and_eq_true_iff.mp hw
    have ih' := ih hsub
    simp only [gateClauses, CNF.eval, Clause.eval,
               List.all_cons, List.all_nil, List.any_cons, List.any_nil,
               Literal.eval, Bool.and_true, Bool.or_false] at hgate
    show w (Sum.inr (Circuit.not c')) = !(c'.eval (fun x => w (Sum.inl x)))
    rw [← ih']
    cases hwn : w (Sum.inr (Circuit.not c')) <;>
      cases hwc : w (Sum.inr c') <;>
      simp [hwn, hwc] at hgate
    all_goals rfl
  | and c₁ c₂ ih₁ ih₂ =>
    rw [tseitinClauses, CNF.eval_append, CNF.eval_append] at hw
    obtain ⟨hgate_sub₁, hsub₂⟩ := Bool.and_eq_true_iff.mp hw
    obtain ⟨hgate, hsub₁⟩ := Bool.and_eq_true_iff.mp hgate_sub₁
    have ih₁' := ih₁ hsub₁
    have ih₂' := ih₂ hsub₂
    simp only [gateClauses, CNF.eval, Clause.eval,
               List.all_cons, List.all_nil, List.any_cons, List.any_nil,
               Literal.eval, Bool.and_true, Bool.or_false] at hgate
    show w (Sum.inr (Circuit.and c₁ c₂))
          = (c₁.eval (fun x => w (Sum.inl x)) && c₂.eval (fun x => w (Sum.inl x)))
    rw [← ih₁', ← ih₂']
    cases hwa : w (Sum.inr (Circuit.and c₁ c₂)) <;>
      cases hwc1 : w (Sum.inr c₁) <;>
      cases hwc2 : w (Sum.inr c₂) <;>
      simp [hwa, hwc1, hwc2] at hgate
    all_goals rfl
  | or c₁ c₂ ih₁ ih₂ =>
    rw [tseitinClauses, CNF.eval_append, CNF.eval_append] at hw
    obtain ⟨hgate_sub₁, hsub₂⟩ := Bool.and_eq_true_iff.mp hw
    obtain ⟨hgate, hsub₁⟩ := Bool.and_eq_true_iff.mp hgate_sub₁
    have ih₁' := ih₁ hsub₁
    have ih₂' := ih₂ hsub₂
    simp only [gateClauses, CNF.eval, Clause.eval,
               List.all_cons, List.all_nil, List.any_cons, List.any_nil,
               Literal.eval, Bool.and_true, Bool.or_false] at hgate
    show w (Sum.inr (Circuit.or c₁ c₂))
          = (c₁.eval (fun x => w (Sum.inl x)) || c₂.eval (fun x => w (Sum.inl x)))
    rw [← ih₁', ← ih₂']
    cases hwa : w (Sum.inr (Circuit.or c₁ c₂)) <;>
      cases hwc1 : w (Sum.inr c₁) <;>
      cases hwc2 : w (Sum.inr c₂) <;>
      simp [hwa, hwc1, hwc2] at hgate
    all_goals rfl

/-- Any model `w` of the full Tseitin CNF `c.tseitin` restricts (via
`Sum.inl`) to a model of the original circuit `c`. The root unit clause
forces `w (Sum.inr c) = true`, and the gate clauses force this to equal
`c.eval (w ∘ Sum.inl)` via `tseitinClauses_imp_root`. -/
theorem tseitin_models_restrict (c : Circuit X)
    (w : (X ⊕ Circuit X) → Bool) (hw : CNF.eval c.tseitin w = true) :
    c.eval (fun x => w (Sum.inl x)) = true := by
  -- Split into the root assertion clause and the per-gate clauses.
  rw [tseitin, CNF.eval_cons] at hw
  obtain ⟨hroot, hgate⟩ := Bool.and_eq_true_iff.mp hw
  -- Root clause forces aux(c) = true.
  have hroot_w : w (Sum.inr c) = true := by
    simp [Clause.eval, Literal.eval] at hroot
    exact hroot
  -- Gate clauses force aux(c) = c.eval (w ∘ Sum.inl).
  have hsub := tseitinClauses_imp_root c w hgate
  rw [hroot_w] at hsub
  exact hsub.symm

/-! ### Equisatisfiability -/

/-- **Tseitin equisatisfiability.** A Boolean circuit `c : Circuit X` is
satisfiable iff its Tseitin CNF encoding `c.tseitin : CNF (X ⊕ Circuit X)`
is satisfiable. The forward direction lifts a circuit-satisfying valuation
`v` via `tseitinValuation v`; the backward direction restricts a
CNF-satisfying valuation `w` via `Sum.inl`. -/
theorem tseitin_equisat (c : Circuit X) :
    (∃ v : X → Bool, c.eval v = true) ↔
    (∃ w : (X ⊕ Circuit X) → Bool, CNF.eval c.tseitin w = true) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨tseitinValuation v, ?_⟩
    rw [tseitin_eval_tseitinValuation, hv]
  · rintro ⟨w, hw⟩
    exact ⟨fun x => w (Sum.inl x), tseitin_models_restrict c w hw⟩

end Circuit
