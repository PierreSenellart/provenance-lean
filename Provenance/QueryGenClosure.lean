/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryGenAggRewriting

/-!
# The compositional closure of the rewriting rules

ProvSQL rewrites whole queries in which classical blocks, `GROUP BY …
HAVING` blocks and bare `GROUP BY` blocks occur as subqueries. The
relation `QueryGen.RewritesTo` below closes the three base rewritings –
the classical rules (`QueryGen.rewritingGenOf`), the `HAVING` site
(`QueryGen.havingPredRew`, the aggregate-exposing shape ProvSQL actually
emits, for an arbitrary Boolean combination of aggregate comparisons) and
the bare grouping (`QueryGen.gammaRew`) – under the operators that may sit
above them, and
`QueryGen.rewritesTo_valid` extends the correctness to every query so
obtained.

## Token-bearing outputs

The base rules no longer share an output shape: a classical or `HAVING`
block produces all-regular data columns, whereas a bare grouping produces
aggregate-token columns. The relation is therefore indexed by the
rewritten query's own kind vector, and correctness is stated at the token
level, through `GenRow.toCompositeRow`. On all-regular outputs this
specialises to the earlier statement, `QueryGen.rewritesTo_valid_reg`.

The natural rewritten kind vector of a query of kinds `κ` is
`ColKind.rewKindsOf κ` – the source kinds followed by the provenance
column. Casting terms, predicates and projection columns into it is
*uniform*: a column keeps its kind, so no all-regular hypothesis is
needed anywhere (`TermG.castRew` and friends), unlike the composite casts
of the classical rewriting. The gate `TermG.cmpAgg`, whose generic
semantics is the junk value `𝟘`, casts to that constant.

## Scope

Selection, projection and union close over arbitrary kinds – in
particular over a bare grouping, which is the `SELECT … FROM (GROUP BY …)`
shape. Deduplication closes over any subquery whose output is
all-regular, which is what the kind discipline permits: the rewritten
rule `QueryGen.dedupRew` is ProvSQL's `ε` (group by the data columns,
`⊕`-sum the provenance column), proven correct against an arbitrary
rewritten subquery rather than only against `rewritingGen`'s output.

Product closes over arbitrary kinds too. Reassembling a join needs a
projection column whose kind is read off the operand's kind vector –
`ProjCol.copy`, which dispatches on that kind – and its faithfulness
needs the operands' rows to conform; that comes for free from the
subderivations, since their rows are embeddings of rows of the general
evaluator, which conforms by `QueryGen.evaluateGen_conform`.

Difference closes as well (`QueryGen.diffRew`). The closure is therefore
complete for the operators the kind discipline admits above a grouping:
there is no remaining structural gap.
-/

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K]
  [DecidableEq K] [HasAltLinearOrder K]

/-! ## The rewritten kind vector -/

/-- The rewritten kind vector of a query of kinds `κ`: the source kinds,
followed by the provenance column. -/
abbrev ColKind.rewKindsOf {n : ℕ} (κ : Fin n → ColKind) :
    Fin (n + 1) → ColKind :=
  Fin.append κ (fun _ : Fin 1 => ColKind.prov)

@[simp] theorem ColKind.rewKindsOf_castAdd {n : ℕ} (κ : Fin n → ColKind)
    (k : Fin n) : ColKind.rewKindsOf κ (Fin.castAdd 1 k) = κ k :=
  Fin.append_left _ _ k

@[simp] theorem ColKind.rewKindsOf_last {n : ℕ} (κ : Fin n → ColKind) :
    ColKind.rewKindsOf κ (Fin.last n) = ColKind.prov := by
  show Fin.append κ _ (Fin.last n) = _
  rw [show (Fin.last n) = Fin.natAdd n (0 : Fin 1) from Fin.ext (by simp),
    Fin.append_right]

/-- On all-regular kinds the uniform rewritten kind vector agrees
pointwise with the classical rewriting's `ColKind.rewKinds`. -/
theorem ColKind.rewKindsOf_base_of_reg {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) (k : Fin (n + 1)) :
    (ColKind.rewKindsOf κ k).base = ColKind.reg := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [ColKind.rewKindsOf_castAdd, hκ i]; rfl
  · rw [show Fin.natAdd n i = Fin.last n from Fin.ext (by
      simp [Subsingleton.elim i (0 : Fin 1)]), ColKind.rewKindsOf_last]
    rfl

/-! ## Uniform casts into the rewritten world -/

/-- A term over the source kinds, read on the rewritten schema: every
column keeps its kind and its position, so no all-regular hypothesis is
needed. The gate, whose generic semantics is the junk value `𝟘`, casts to
that constant. -/
def TermG.castRew {n : ℕ} {κ : Fin n → ColKind} :
    TermG T κ → TermG (T ⊕ K) (ColKind.rewKindsOf κ)
  | .const a => .const (Sum.inl a)
  | .index k h =>
      .index (Fin.castAdd 1 k) ((ColKind.rewKindsOf_castAdd κ k).trans h)
  | .provIndex k h =>
      .provIndex (Fin.castAdd 1 k) ((ColKind.rewKindsOf_castAdd κ k).trans h)
  | .cmpAgg _ _ _ _ => .const (Sum.inl 0)
  | .add t₁ t₂ => .add t₁.castRew t₂.castRew
  | .sub t₁ t₂ => .sub t₁.castRew t₂.castRew
  | .mul t₁ t₂ => .mul t₁.castRew t₂.castRew

/-- An aggregate-atom-free predicate is unnecessary here: the cast is
total, aggregate atoms comparing a token's deterministic reading. -/
def GenPred.castRew {n : ℕ} {κ : Fin n → ColKind} :
    GenPred T κ → GenPred (T ⊕ K) (ColKind.rewKindsOf κ)
  | .cmp op t₁ t₂ => .cmp op t₁.castRew t₂.castRew
  | .aggCmp k h op t =>
      .aggCmp (Fin.castAdd 1 k) ((ColKind.rewKindsOf_castAdd κ k).trans h)
        op t.castRew
  | .and φ ψ => .and φ.castRew ψ.castRew
  | .or φ ψ => .or φ.castRew ψ.castRew
  | .not φ => .not φ.castRew

/-- A projection column, read on the rewritten schema. -/
def ProjCol.castRew {n : ℕ} {κ : Fin n → ColKind} :
    ProjCol T κ → ProjCol (T ⊕ K) (ColKind.rewKindsOf κ)
  | .term t => .term t.castRew
  | .token k h =>
      .token (Fin.castAdd 1 k) ((ColKind.rewKindsOf_castAdd κ k).trans h)
  | .provTerm t => .provTerm t.castRew

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem ProjCol.castRew_kind {n : ℕ} {κ : Fin n → ColKind}
    (p : ProjCol T κ) :
    (p.castRew (K := K)).kind = p.kind := by
  cases p <;> rfl

/-! ## The casts evaluate faithfully -/

theorem TermG.castRew_evalRew {n : ℕ} {κ : Fin n → ColKind}
    (t : TermG T κ) (r : GenRow T K n) :
    t.castRew.evalRew r.toCompositeRow = Sum.inl (t.eval r.fst) := by
  induction t with
  | const a => rfl
  | index k h =>
    show AggValue.collapseSum (r.toCompositeRow (Fin.castAdd 1 k)) = _
    rw [GenRow.toCompositeRow_castAdd, AggValue.collapseSum_toComposite]
    rfl
  | provIndex k h =>
    show AggValue.collapseSum (r.toCompositeRow (Fin.castAdd 1 k)) = _
    rw [GenRow.toCompositeRow_castAdd, AggValue.collapseSum_toComposite]
    rfl
  | cmpAgg k h op c ih => rfl
  | add t₁ t₂ ih₁ ih₂ => show _ + _ = _; rw [ih₁, ih₂]; rfl
  | sub t₁ t₂ ih₁ ih₂ =>
    show HSub.hSub _ _ = _
    rw [ih₁, ih₂]
    rfl
  | mul t₁ t₂ ih₁ ih₂ => show _ * _ = _; rw [ih₁, ih₂]; rfl

theorem GenPred.castRew_holdsRew {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (r : GenRow T K n) :
    φ.castRew.holdsRew r.toCompositeRow ↔ φ.holds r.fst := by
  induction φ with
  | cmp op t₁ t₂ =>
    show CompOp.eval _ _ _ ↔ _
    rw [t₁.castRew_evalRew r, t₂.castRew_evalRew r]
    exact CompOp.eval_inl op _ _
  | aggCmp k h op t =>
    show CompOp.eval _ (AggValue.collapseSum
      (r.toCompositeRow (Fin.castAdd 1 k))) _ ↔ _
    rw [GenRow.toCompositeRow_castAdd, AggValue.collapseSum_toComposite,
      t.castRew_evalRew r]
    exact CompOp.eval_inl op _ _
  | and φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ => exact or_congr ihφ ihψ
  | not φ ihφ => exact not_congr ihφ

theorem ProjCol.castRew_evalRew {n : ℕ} {κ : Fin n → ColKind}
    (p : ProjCol T κ) (r : GenRow T K n) :
    p.castRew.evalRew r.toCompositeRow
      = GenValue.toComposite (p.eval r.fst) := by
  cases p with
  | term t => exact congrArg Sum.inl (t.castRew_evalRew r)
  | token k h => exact GenRow.toCompositeRow_castAdd r k
  | provTerm t => exact congrArg Sum.inl (t.castRew_evalRew r)

/-- On an all-regular query the token-aware embedding is the embedding of
the classical and `HAVING`-site correctness statements. -/
theorem QueryGen.map_toCompositeRow_of_reg {n : ℕ} {κ : Fin n → ColKind}
    (q : QueryGen T n κ) (hκ : ∀ k, κ k = ColKind.reg)
    (d : AnnotatedDatabase T K) :
    (q.evaluateGen d).map GenRow.toCompositeRow
      = Multiset.map (fun t : Tuple (T ⊕ K) (n + 1) =>
          ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) (n + 1)))
        ((q.evaluateAnnotatedGen d).toComposite) := by
  unfold QueryGen.evaluateAnnotatedGen AnnotatedRelation.toComposite
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  exact GenRow.toCompositeRow_of_reg r (fun k =>
    (QueryGen.evaluateGen_conform q d r hr k).trans
      (congrArg ColKind.base (hκ k)))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- A data column of a rewritten kind vector, positionally. -/
theorem ColKind.rewKindsOf_of_lt {n : ℕ} (κ : Fin n → ColKind)
    {j : Fin (n + 1)} (h : (j : ℕ) < n) :
    ColKind.rewKindsOf κ j = κ ⟨(j : ℕ), h⟩ :=
  (congrArg (ColKind.rewKindsOf κ)
    (Fin.ext rfl : j = Fin.castAdd 1 (⟨(j : ℕ), h⟩ : Fin n))).trans
    (ColKind.rewKindsOf_castAdd κ _)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- The trailing column of a rewritten kind vector. -/
theorem ColKind.rewKindsOf_of_not_lt {n : ℕ} (κ : Fin n → ColKind)
    {j : Fin (n + 1)} (h : ¬ ((j : ℕ) < n)) :
    ColKind.rewKindsOf κ j = ColKind.prov :=
  (congrArg (ColKind.rewKindsOf κ)
    (Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      : j = Fin.last n)).trans (ColKind.rewKindsOf_last κ)

/-! ## Copying a column of unknown kind -/

/-- Copy the `i`-th column verbatim, whatever its kind: a regular or
provenance column is read as a value term, a token column is a verbatim
token copy. This is the projection column a join reassembly needs, since
the operand's kind vector is not statically known there. -/
def ProjCol.copy {T' : Type} {N : ℕ} {κ' : Fin N → ColKind} (i : Fin N) :
    ProjCol T' κ' :=
  match h : κ' i with
  | ColKind.reg => ProjCol.term (TermG.index i h)
  | ColKind.agg => ProjCol.token i h
  | ColKind.prov => ProjCol.provTerm (TermG.provIndex i h)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
@[simp] theorem ProjCol.copy_kind {T' : Type} {N : ℕ}
    {κ' : Fin N → ColKind} (i : Fin N) :
    (ProjCol.copy (T' := T') (κ' := κ') i).kind = κ' i := by
  unfold ProjCol.copy
  split
  · rename_i h; exact h.symm
  · rename_i h; exact h.symm
  · rename_i h; exact h.symm

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The kind of a transported value is the kind of the value. -/
@[simp] theorem GenValue.kindOf_toComposite (v : GenValue T K) :
    GenValue.kindOf (GenValue.toComposite v) = GenValue.kindOf v := by
  cases v <;> rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **Kind conformance of the token-aware embedding**: a row conforming
to `κ` embeds to one conforming to `ColKind.rewKindsOf κ`. -/
theorem GenRow.toCompositeRow_conform {n : ℕ} {κ : Fin n → ColKind}
    (r : GenRow T K n) (hr : ∀ k, GenValue.kindOf (r.fst k) = (κ k).base)
    (j : Fin (n + 1)) :
    GenValue.kindOf (r.toCompositeRow j)
      = (ColKind.rewKindsOf κ j).base := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [GenRow.toCompositeRow_castAdd, GenValue.kindOf_toComposite,
      ColKind.rewKindsOf_castAdd]
    exact hr i
  · rw [show Fin.natAdd n i = Fin.last n from Fin.ext (by
      simp [Subsingleton.elim i (0 : Fin 1)]), GenRow.toCompositeRow_last,
      ColKind.rewKindsOf_last]
    rfl

/-- A copied column evaluates to the column, on a conformant row. -/
theorem ProjCol.copy_evalRew {N : ℕ} {κ' : Fin N → ColKind} (i : Fin N)
    (u : Tuple (GenValue (T ⊕ K) K) N)
    (hu : GenValue.kindOf (u i) = (κ' i).base) :
    (ProjCol.copy (T' := T ⊕ K) (κ' := κ') i).evalRew u = u i := by
  have hval : ∀ c : ColKind, κ' i = c → c ≠ ColKind.agg →
      ∃ v, u i = Sum.inl v := by
    intro c hc hne
    cases hv : u i with
    | inl v => exact ⟨v, rfl⟩
    | inr a =>
      rw [hv] at hu
      rw [hc, ColKind.base_eq_reg_of_ne_agg hne] at hu
      exact absurd hu (by simp [GenValue.kindOf])
  unfold ProjCol.copy
  split
  · rename_i h
    obtain ⟨v, hv⟩ := hval _ h (fun hc => ColKind.noConfusion hc)
    show Sum.inl (AggValue.collapseSum (u i)) = u i
    rw [hv]
    rfl
  · rfl
  · rename_i h
    obtain ⟨v, hv⟩ := hval _ h (fun hc => ColKind.noConfusion hc)
    show Sum.inl (AggValue.collapseSum (u i)) = u i
    rw [hv]
    rfl

/-! ## Aggregate-only `HAVING` predicates as gate terms

The `HAVING` site rewriting of `Provenance.QueryGenHavingRewriting` takes
one aggregate comparison. An arbitrary Boolean combination of aggregate
comparisons is just as expressible: the predicate provenance `predsem`
is `∧ ↦ ⊗`, `∨ ↦ ⊕` and `¬` pushed to the atoms by De Morgan duality
with operator complementation, and the rewritten world's terms have
`mul`, `add` and the `provsql_having` gate. `GenPred.gateTerm` is that
translation.

Predicates mixing in a *regular* atom are still out of scope: `predsem`
gives such an atom its characteristic value `χ`, for which the term
grammar has no primitive. They also behave differently on the group
guard – `GenPred.entailsExistence` is false for them, so the `δ` factor
survives – whereas an aggregate-only predicate always entails the
group's existence and supersedes it. -/

/-- A predicate all of whose atoms are aggregate comparisons. -/
def GenPred.aggOnly {n : ℕ} {κ : Fin n → ColKind} : GenPred T κ → Bool
  | .cmp _ _ _ => false
  | .aggCmp _ _ _ _ => true
  | .and φ ψ | .or φ ψ => φ.aggOnly && ψ.aggOnly
  | .not φ => φ.aggOnly

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- An aggregate-only predicate entails its groups' existence, whatever
the polarity: every atom does, and both connectives preserve that. -/
theorem GenPred.aggOnly_entailsExistence {n : ℕ} {κ : Fin n → ColKind} :
    ∀ (φ : GenPred T κ), φ.aggOnly = true → ∀ neg,
      φ.entailsExistence neg = true
  | .cmp _ _ _, hφ, _ => Bool.noConfusion hφ
  | .aggCmp _ _ _ _, _, _ => rfl
  | .and φ ψ, hφ, neg => by
    have h := Bool.and_eq_true_iff.mp hφ
    simp only [GenPred.entailsExistence, aggOnly_entailsExistence φ h.1 neg,
      aggOnly_entailsExistence ψ h.2 neg]
    split <;> rfl
  | .or φ ψ, hφ, neg => by
    have h := Bool.and_eq_true_iff.mp hφ
    simp only [GenPred.entailsExistence, aggOnly_entailsExistence φ h.1 neg,
      aggOnly_entailsExistence ψ h.2 neg]
    split <;> rfl
  | .not φ, hφ, neg => aggOnly_entailsExistence φ hφ (!neg)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- An aggregate-only predicate compares at least one token column. -/
theorem GenPred.aggOnly_comparedCols_nonempty {n : ℕ} {κ : Fin n → ColKind} :
    ∀ (φ : GenPred T κ), φ.aggOnly = true → φ.comparedCols.Nonempty
  | .cmp _ _ _, hφ => Bool.noConfusion hφ
  | .aggCmp k _ _ _, _ => ⟨k, Finset.mem_singleton_self k⟩
  | .and φ ψ, hφ => by
    obtain ⟨k, hk⟩ := aggOnly_comparedCols_nonempty φ
      (Bool.and_eq_true_iff.mp hφ).1
    exact ⟨k, Finset.mem_union_left _ hk⟩
  | .or φ ψ, hφ => by
    obtain ⟨k, hk⟩ := aggOnly_comparedCols_nonempty φ
      (Bool.and_eq_true_iff.mp hφ).1
    exact ⟨k, Finset.mem_union_left _ hk⟩
  | .not φ, hφ => aggOnly_comparedCols_nonempty φ hφ

/-- **The predicate provenance as a rewritten term**: the `predsem`
algebra – aggregate atoms to `provsql_having` gates, `∧ ↦ ⊗`, `∨ ↦ ⊕`,
`¬` pushed down with operator complementation. Regular atoms have no
counterpart and get the junk constant; `GenPred.gateTerm_evalRew` is
stated on aggregate-only predicates. -/
def GenPred.gateTerm {n : ℕ} {κ : Fin n → ColKind} :
    GenPred T κ → Bool → TermG (T ⊕ K) (ColKind.rewKindsOf κ)
  | .cmp _ _ _, _ => .const 0
  | .aggCmp k h op t, neg =>
      .cmpAgg (Fin.castAdd 1 k) ((ColKind.rewKindsOf_castAdd κ k).trans h)
        (if neg then op.negate else op) t.castRew
  | .and φ ψ, neg =>
      if neg then .add (φ.gateTerm neg) (ψ.gateTerm neg)
      else .mul (φ.gateTerm neg) (ψ.gateTerm neg)
  | .or φ ψ, neg =>
      if neg then .mul (φ.gateTerm neg) (ψ.gateTerm neg)
      else .add (φ.gateTerm neg) (ψ.gateTerm neg)
  | .not φ, neg => φ.gateTerm (!neg)

/-- **The gate term computes the predicate provenance.** -/
theorem GenPred.gateTerm_evalRew {n : ℕ} {κ : Fin n → ColKind} :
    ∀ (φ : GenPred T κ), φ.aggOnly = true → ∀ (neg : Bool)
      (r : GenRow T K n),
      (φ.gateTerm neg).evalRew r.toCompositeRow
        = Sum.inr (φ.predsem neg r.fst)
  | .cmp _ _ _, hφ, _, _ => Bool.noConfusion hφ
  | .aggCmp k h op t, _, neg, r => by
    show (match r.toCompositeRow (Fin.castAdd 1 k) with
      | Sum.inl _ => (Sum.inr 0 : T ⊕ K)
      | Sum.inr a => Sum.inr (a.predProv (if neg then op.negate else op)
          (t.castRew.evalRew r.toCompositeRow))) = _
    rw [GenRow.toCompositeRow_castAdd, t.castRew_evalRew r]
    show _ = Sum.inr (match r.fst k with
      | Sum.inl _ => 0
      | Sum.inr a => a.predProv (if neg then op.negate else op) (t.eval r.fst))
    cases r.fst k with
    | inl v => rfl
    | inr a =>
      show (Sum.inr (AggValue.toComposite a |>.predProv _ _) : T ⊕ K) = _
      rw [AggValue.predProv_toComposite]
  | .and φ ψ, hφ, neg, r => by
    have h := Bool.and_eq_true_iff.mp hφ
    show TermG.evalRew (if neg then _ else _) _ = _
    show _ = Sum.inr (if neg then _ + _ else _ * _)
    cases neg with
    | false =>
      show TermG.evalRew (TermG.mul _ _) _ = _
      show TermG.evalRew _ _ * TermG.evalRew _ _ = _
      rw [gateTerm_evalRew φ h.1 false r, gateTerm_evalRew ψ h.2 false r]
      rfl
    | true =>
      show TermG.evalRew (TermG.add _ _) _ = _
      show TermG.evalRew _ _ + TermG.evalRew _ _ = _
      rw [gateTerm_evalRew φ h.1 true r, gateTerm_evalRew ψ h.2 true r]
      rfl
  | .or φ ψ, hφ, neg, r => by
    have h := Bool.and_eq_true_iff.mp hφ
    cases neg with
    | false =>
      show TermG.evalRew (TermG.add _ _) _ = _
      show TermG.evalRew _ _ + TermG.evalRew _ _ = _
      rw [gateTerm_evalRew φ h.1 false r, gateTerm_evalRew ψ h.2 false r]
      rfl
    | true =>
      show TermG.evalRew (TermG.mul _ _) _ = _
      show TermG.evalRew _ _ * TermG.evalRew _ _ = _
      rw [gateTerm_evalRew φ h.1 true r, gateTerm_evalRew ψ h.2 true r]
      rfl
  | .not φ, hφ, neg, r => gateTerm_evalRew φ hφ (!neg) r

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- An aggregate-only predicate has an aggregate atom. -/
theorem GenPred.aggOnly_hasAggAtom {n : ℕ} {κ : Fin n → ColKind} :
    ∀ (φ : GenPred T κ), φ.aggOnly = true → φ.hasAggAtom = true
  | .cmp _ _ _, hφ => Bool.noConfusion hφ
  | .aggCmp _ _ _ _, _ => rfl
  | .and φ ψ, hφ => by
    rw [GenPred.hasAggAtom, aggOnly_hasAggAtom φ (Bool.and_eq_true_iff.mp hφ).1]
    rfl
  | .or φ ψ, hφ => by
    rw [GenPred.hasAggAtom, aggOnly_hasAggAtom φ (Bool.and_eq_true_iff.mp hφ).1]
    rfl
  | .not φ, hφ => aggOnly_hasAggAtom φ hφ

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Compared columns are token columns – by construction of the aggregate
atom. -/
theorem GenPred.comparedCols_agg {n : ℕ} {κ : Fin n → ColKind} :
    ∀ (φ : GenPred T κ) {k : Fin n}, k ∈ φ.comparedCols → κ k = ColKind.agg
  | .cmp _ _ _, k, hk => absurd hk (by simp [GenPred.comparedCols])
  | .aggCmp k' h _ _, k, hk => by
    rw [show k = k' from Finset.mem_singleton.mp hk]
    exact h
  | .and φ ψ, k, hk => by
    rcases Finset.mem_union.mp hk with h | h
    · exact comparedCols_agg φ h
    · exact comparedCols_agg ψ h
  | .or φ ψ, k, hk => by
    rcases Finset.mem_union.mp hk with h | h
    · exact comparedCols_agg φ h
    · exact comparedCols_agg ψ h
  | .not φ, k, hk => comparedCols_agg φ hk

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Kind conformance of a grouping row. -/
theorem gammaRow_conform {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggValue T K) (k : Fin (n₁ + n₂)) :
    GenValue.kindOf (Fin.append (fun i => (Sum.inl (g i) : GenValue T K))
        (fun j => Sum.inr (h j)) k)
      = (ColKind.gammaKinds n₁ n₂ k).base := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left, ColKind.gammaKinds, Fin.append_left]
    rfl
  · rw [Fin.append_right, ColKind.gammaKinds, Fin.append_right]
    rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- Kind conformance of the embedding of a grouping row. -/
theorem GenRow.toCompositeRow_gammaRow_conform {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggValue T K) (a : GenAnn K) (i : Fin (n₁ + n₂ + 1)) :
    GenValue.kindOf (GenRow.toCompositeRow
        ((Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun j => Sum.inr (h j)), a) : GenRow T K (n₁ + n₂)) i)
      = (ColKind.gammaRewKinds n₁ n₂ i).base :=
  GenRow.toCompositeRow_conform _ (fun k => gammaRow_conform g h k) i

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A token column of a grouping row carries the group's annotation
list. -/
theorem gammaRow_agg_col {m n₁ n₂ : ℕ} (g : Tuple T n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (U : List (AnnotatedTuple T K m)) {k : Fin (n₁ + n₂)}
    (hk : ColKind.gammaKinds n₁ n₂ k = ColKind.agg) :
    ∃ a : AggValue T K,
      Fin.append (fun i => (Sum.inl (g i) : GenValue T K))
          (fun j => Sum.inr (AggValue.ofGroup (fs j) (ts j) U)) k = Sum.inr a
        ∧ a.occs.map Prod.snd = U.map Prod.snd := by
  revert hk
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · intro hk
    rw [ColKind.gammaKinds, Fin.append_left] at hk
    exact ColKind.noConfusion hk
  · exact fun _ => ⟨AggValue.ofGroup (fs j) (ts j) U,
      Fin.append_right _ _ j, AggValue.annList_ofGroup _ _ _⟩

omit [HasAltLinearOrder K] in
/-- **Superseding the group guard**: when the compared occurrence lists
are non-empty and all equal to the single pending group's list, the
selection's filter removes that group factor, so the row finalizes to its
concrete part. -/
theorem GenAnn.finalize_supersede (b : K) (l₀ : List K)
    (C : Multiset (List K)) (hne : C ≠ 0) (hall : ∀ l' ∈ C, l' = l₀) :
    GenAnn.finalize (⟨b, Multiset.filter
        (fun l => ¬(C ≠ 0 ∧ ∀ l' ∈ C, l' = l))
        ({l₀} : Multiset (List K))⟩ : GenAnn K) = b := by
  rw [Multiset.filter_singleton, if_neg (not_not.mpr ⟨hne, hall⟩)]
  simp [GenAnn.finalize]

/-! ## The general `HAVING` site -/

/-- The output columns of a general `HAVING` site: the group keys and the
aggregate tokens copied verbatim, and the predicate's gate term in the
provenance column. -/
def QueryGen.havingPredCols {n₁ n₂ : ℕ}
    (φ : GenPred T (ColKind.gammaKinds n₁ n₂)) :
    Tuple (ProjCol (T ⊕ K) (ColKind.gammaRewKinds n₁ n₂)) (n₁ + n₂ + 1) :=
  fun j =>
    if hj : (j : ℕ) < n₁ + n₂ then
      ProjCol.copy (Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin (n₁ + n₂)))
    else
      ProjCol.provTerm (φ.gateTerm false)

omit [DecidableEq K] in
/-- The site's output columns have exactly the rewritten `Gamma` kinds. -/
theorem QueryGen.havingPredCols_kind {n₁ n₂ : ℕ}
    (φ : GenPred T (ColKind.gammaKinds n₁ n₂)) (j : Fin (n₁ + n₂ + 1)) :
    (QueryGen.havingPredCols (K := K) φ j).kind
      = ColKind.gammaRewKinds n₁ n₂ j := by
  unfold QueryGen.havingPredCols
  by_cases hj : (((j : ℕ) < n₁ + n₂) : Prop)
  · rw [dif_pos hj, ProjCol.copy_kind]
    exact congrArg (ColKind.gammaRewKinds n₁ n₂)
      (Fin.ext rfl : Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin (n₁ + n₂)) = j)
  · rw [dif_neg hj]
    exact (ColKind.rewKindsOf_of_not_lt (ColKind.gammaKinds n₁ n₂) hj).symm

/-- **The rewritten `HAVING` site**, for an arbitrary aggregate-only
predicate: the token-building grouping of `QueryGen.gammaRew`, with a
projection keeping the group keys and the aggregate tokens and replacing
the group-existence guard by the predicate's gate term. -/
def QueryGen.havingPredRew {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (φ : GenPred T (ColKind.gammaKinds n₁ n₂))
    (qg : QueryGen T m (ColKind.allReg m)) (hq : qg.classical) :
    QueryGen (T ⊕ K) (n₁ + n₂ + 1) (ColKind.gammaRewKinds n₁ n₂) :=
  QueryGen.Retag
    (fun j => congrArg ColKind.base (QueryGen.havingPredCols_kind φ j))
    (QueryGen.Proj (QueryGen.havingPredCols φ)
      (QueryGen.gammaRew is ts fs qg hq))

/-- **Correctness of the general `HAVING` site rewriting**, relative to
the gate primitive: an aggregate-only predicate always entails its
group's existence, so its predicate provenance supersedes the group
guard, and the gate term computes exactly that provenance. -/
theorem QueryGen.havingPredRew_valid {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (φ : GenPred T (ColKind.gammaKinds n₁ n₂)) (hφ : φ.aggOnly = true)
    (qg : QueryGen T m (ColKind.allReg m)) (hq : qg.classical)
    (d : AnnotatedDatabase T K) :
    ((QueryGen.Sel φ (QueryGen.Gamma is ts fs qg)).evaluateGen d).map
        GenRow.toCompositeRow
      = (QueryGen.havingPredRew is ts fs φ qg hq).evaluateRew
          d.toComposite := by
  unfold QueryGen.havingPredRew
  show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) d.toComposite
  simp only [QueryGen.evaluateRew]
  rw [← QueryGen.gammaRew_valid is ts fs qg hq d]
  show Multiset.map _ (QueryGen.evaluateGen (QueryGen.Sel _ _) d) = _
  simp only [QueryGen.evaluateGen]
  rw [if_pos (GenPred.aggOnly_hasAggAtom φ hφ)]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl (fun kv _ => ?_)
  simp only [Function.comp_apply]
  funext j
  rw [GenRow.toCompositeRow_coord]
  show _ = ProjCol.evalRew (QueryGen.havingPredCols φ j) _
  unfold QueryGen.havingPredCols
  by_cases hj : (((j : ℕ) < n₁ + n₂) : Prop)
  · rw [dif_pos hj, dif_pos hj,
      ProjCol.copy_evalRew _ _
        (GenRow.toCompositeRow_gammaRow_conform _ _ _ _),
      GenRow.toCompositeRow_castAdd]
  · rw [dif_neg hj, dif_neg hj]
    show Sum.inl (Sum.inr (GenAnn.finalize ⟨1 * _, _⟩))
      = Sum.inl (TermG.evalRew _ _)
    rw [GenPred.aggOnly_entailsExistence φ hφ false, if_pos rfl]
    refine Eq.trans (congrArg (fun v => (Sum.inl (Sum.inr v)
      : GenValue (T ⊕ K) K)) (GenAnn.finalize_supersede _ _ _ ?_ ?_)) ?_
    · intro h0
      obtain ⟨k, hk⟩ := GenPred.aggOnly_comparedCols_nonempty φ hφ
      obtain ⟨a, ha, hann⟩ := gammaRow_agg_col kv.fst ts fs
        (Having.havingGroup is
          (Multiset.map GenRow.toAnnotated (qg.evaluateGen d)) kv.fst)
        (GenPred.comparedCols_agg φ hk)
      refine absurd ?_ (Multiset.notMem_zero
        (List.map Prod.snd (Having.havingGroup is
          (Multiset.map GenRow.toAnnotated (qg.evaluateGen d)) kv.fst)))
      rw [← h0]
      refine (Multiset.mem_filterMap _ _).mpr ⟨k, Finset.mem_val.mpr hk, ?_⟩
      rw [ha]
      exact congrArg some hann
    · intro l' hl'
      obtain ⟨k, hk, hfk⟩ := (Multiset.mem_filterMap _ _).mp hl'
      obtain ⟨a, ha, hann⟩ := gammaRow_agg_col kv.fst ts fs
        (Having.havingGroup is
          (Multiset.map GenRow.toAnnotated (qg.evaluateGen d)) kv.fst)
        (GenPred.comparedCols_agg φ (Finset.mem_val.mp hk))
      rw [ha] at hfk
      exact (Option.some.inj hfk).symm.trans hann
    · rw [one_mul]
      refine congrArg Sum.inl ?_
      symm
      exact GenPred.gateTerm_evalRew (K := K) φ hφ false _

/-! ## Duplicate elimination in the rewritten world -/

omit [DecidableEq K] in
/-- Folding embedded annotations with the value-type addition is the
annotation sum. -/
theorem fold_addFn_inr {α : Type} (f : α → K) (M : Multiset α) :
    ((M.map (fun x => (Sum.inr (f x) : T ⊕ K))).fold addFn 0)
      = Sum.inr (M.map f).sum := by
  induction M using Multiset.induction with
  | empty => rfl
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.fold_cons_left, ih, Multiset.map_cons,
      Multiset.sum_cons]
    rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- The embedding of a row rebuilt from an annotated tuple. -/
theorem GenRow.toCompositeRow_ofAnnotated {n : ℕ} (p : AnnotatedTuple T K n) :
    (GenRow.ofAnnotated p).toCompositeRow
      = Fin.append (fun k => (Sum.inl (Sum.inl (p.fst k))
          : GenValue (T ⊕ K) K))
        (fun _ : Fin 1 => Sum.inl (Sum.inr p.snd)) := by
  unfold GenRow.toCompositeRow GenRow.ofAnnotated
  simp only [GenAnn.finalize_of_pending_zero]
  rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- The data reading of an embedded row is the embedded data reading. -/
theorem GenRow.plainTuple_toCompositeRow {n : ℕ} (r : GenRow T K n)
    (k : Fin n) :
    GenRow.plainTuple r.toCompositeRow (Fin.castAdd 1 k)
      = Sum.inl (GenRow.plainTuple r.fst k) := by
  show AggValue.collapseSum (r.toCompositeRow (Fin.castAdd 1 k)) = _
  rw [GenRow.toCompositeRow_castAdd, AggValue.collapseSum_toComposite]
  rfl

/-- The provenance column of an embedded row is its finalized
annotation. -/
theorem TermG.evalRew_provLast_toCompositeRow {n : ℕ} (r : GenRow T K n) :
    (TermG.provIndex (Fin.last n)
        (ColKind.rewKindsOf_last (ColKind.allReg n))).evalRew
      r.toCompositeRow = Sum.inr r.snd.finalize := by
  show AggValue.collapseSum (r.toCompositeRow (Fin.last n)) = _
  rw [GenRow.toCompositeRow_last]
  rfl

/-- **The rewritten duplicate elimination**: ProvSQL's `ε` rule – group by
the data columns and `⊕`-sum the provenance column – applied to an
arbitrary rewritten subquery, as `QueryGen.rewritingGen` does for the
classical fragment. -/
def QueryGen.dedupRew {n : ℕ}
    (q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n))) :
    QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n)) :=
  QueryGen.Retag
    (κ' := ColKind.rewKindsOf (ColKind.allReg n))
    (fun j => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left, ColKind.rewKindsOf_castAdd]
      · rw [Fin.append_right,
          show Fin.natAdd n i = Fin.last n from Fin.ext (by
            simp [Subsingleton.elim i (0 : Fin 1)]),
          ColKind.rewKindsOf_last])
    (QueryGen.ProvSum (fun k : Fin n => Fin.castAdd 1 k)
      (fun k => by
        rw [ColKind.rewKindsOf_castAdd]
        exact fun hc => ColKind.noConfusion hc)
      (TermG.provIndex (Fin.last n)
        (ColKind.rewKindsOf_last (ColKind.allReg n)))
      q')

/-- **Correctness of the rewritten duplicate elimination**, for an
arbitrary rewritten subquery. -/
theorem QueryGen.dedupRew_valid {n : ℕ} {q : QueryGen T n (ColKind.allReg n)}
    {q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n))}
    (d : AnnotatedDatabase T K)
    (ih : (q.evaluateGen d).map GenRow.toCompositeRow
      = q'.evaluateRew d.toComposite) :
    ((QueryGen.Dedup q).evaluateGen d).map GenRow.toCompositeRow
      = (QueryGen.dedupRew q').evaluateRew d.toComposite := by
  unfold QueryGen.dedupRew
  show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) d.toComposite
  simp only [QueryGen.evaluateRew]
  rw [← ih]
  show Multiset.map _ (QueryGen.evaluateGen (QueryGen.Dedup _) d) = _
  simp only [QueryGen.evaluateGen]
  rw [groupByKey_eq_dedup_map]
  -- the rewritten side's keys are the `inl`-embedding of the annotated ones
  rw [show (Multiset.map (fun (x : Tuple (GenValue (T ⊕ K) K) (n + 1))
          (k : Fin n) => GenRow.plainTuple x (Fin.castAdd 1 k))
        (Multiset.map GenRow.toCompositeRow (q.evaluateGen d))).dedup
      = Multiset.map (fun (v : Tuple T n) (k : Fin n) => (Sum.inl (v k) : T ⊕ K))
          ((Multiset.map (fun r : GenRow T K n => GenRow.plainTuple r.fst)
            (q.evaluateGen d)).dedup) from by
    rw [Multiset.map_map,
      show ((fun (x : Tuple (GenValue (T ⊕ K) K) (n + 1)) (k : Fin n) =>
            GenRow.plainTuple x (Fin.castAdd 1 k)) ∘ GenRow.toCompositeRow)
          = ((fun (v : Tuple T n) (k : Fin n) => (Sum.inl (v k) : T ⊕ K))
            ∘ (fun r : GenRow T K n => GenRow.plainTuple r.fst)) from
        funext (fun r => funext (fun k =>
          GenRow.plainTuple_toCompositeRow r k)),
      ← Multiset.map_map,
      Multiset.dedup_map_of_injective
        (f := fun (v : Tuple T n) (k : Fin n) => (Sum.inl (v k) : T ⊕ K))
        (fun v w h => funext (fun k => Sum.inl.inj (congrFun h k)))]]
  simp only [Multiset.map_map]
  refine Multiset.map_congr
    (congrArg (fun M : Multiset (Tuple T n) => M.dedup)
      (Multiset.map_congr rfl (fun r _ => rfl))) (fun u _ => ?_)
  simp only [Function.comp_apply]
  rw [GenRow.toCompositeRow_ofAnnotated]
  refine congrArg₂ Fin.append rfl (funext (fun _ => congrArg Sum.inl ?_))
  dsimp only
  -- the ⊕-sum of the provenance column is the grouped annotation
  refine Eq.symm ?_
  rw [Multiset.filter_map, Multiset.map_map,
    show ((fun x : Tuple (GenValue (T ⊕ K) K) (n + 1) =>
          (TermG.provIndex (Fin.last n)
            (ColKind.rewKindsOf_last (ColKind.allReg n))).evalRew x)
        ∘ GenRow.toCompositeRow)
      = (fun r : GenRow T K n => (Sum.inr (GenRow.toAnnotated r).snd : T ⊕ K))
      from funext (fun r => TermG.evalRew_provLast_toCompositeRow r),
    fold_addFn_inr, Multiset.filter_map, Multiset.map_map]
  refine congrArg (fun M : Multiset (GenRow T K n) =>
    (Sum.inr ((M.map (fun r => (GenRow.toAnnotated r).snd)).sum) : T ⊕ K)) ?_
  refine Multiset.filter_congr (fun r _ => ?_)
  simp only [Function.comp_apply]
  constructor
  · intro h
    exact funext (fun k => Sum.inl.inj
      ((GenRow.plainTuple_toCompositeRow r k).symm.trans (h k)))
  · intro h k
    exact (GenRow.plainTuple_toCompositeRow r k).trans
      (congrArg (fun v : Tuple T n => (Sum.inl (v k) : T ⊕ K)) h)

/-! ## Products of token-bearing blocks -/

/-- The reassembly columns of a rewritten product: the two operands' data
columns copied verbatim (whatever their kinds), and the product of the
two provenance columns. -/
def QueryGen.prodRewCols {n₁ n₂ : ℕ} (κ₁ : Fin n₁ → ColKind)
    (κ₂ : Fin n₂ → ColKind) :
    Tuple (ProjCol (T ⊕ K)
        (Fin.append (ColKind.rewKindsOf κ₁) (ColKind.rewKindsOf κ₂)))
      (n₁ + n₂ + 1) :=
  fun j =>
    if hj₁ : (j : ℕ) < n₁ then
      ProjCol.copy (Fin.castAdd (n₂ + 1)
        (⟨(j : ℕ), Nat.lt_succ_of_lt hj₁⟩ : Fin (n₁ + 1)))
    else if hj₂ : (j : ℕ) < n₁ + n₂ then
      ProjCol.copy (Fin.natAdd (n₁ + 1)
        (⟨(j : ℕ) - n₁, by omega⟩ : Fin (n₂ + 1)))
    else
      ProjCol.provTerm (TermG.mul
        (TermG.provIndex (Fin.castAdd (n₂ + 1) (Fin.last n₁))
          ((Fin.append_left _ _ _).trans (ColKind.rewKindsOf_last κ₁)))
        (TermG.provIndex (Fin.natAdd (n₁ + 1) (Fin.last n₂))
          ((Fin.append_right _ _ _).trans (ColKind.rewKindsOf_last κ₂))))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- The reassembly columns have the rewritten kinds of the product. -/
theorem QueryGen.prodRewCols_kind {n₁ n₂ : ℕ} (κ₁ : Fin n₁ → ColKind)
    (κ₂ : Fin n₂ → ColKind) (j : Fin (n₁ + n₂ + 1)) :
    (QueryGen.prodRewCols (T := T) (K := K) κ₁ κ₂ j).kind
      = ColKind.rewKindsOf (Fin.append κ₁ κ₂) j := by
  unfold QueryGen.prodRewCols
  by_cases hj₁ : (((j : ℕ) < n₁) : Prop)
  · rw [dif_pos hj₁, ProjCol.copy_kind, Fin.append_left,
      ColKind.rewKindsOf_of_lt κ₁ (show LT.lt (j : ℕ) n₁ from hj₁),
      ColKind.rewKindsOf_of_lt (Fin.append κ₁ κ₂)
        (show LT.lt (j : ℕ) (n₁ + n₂) from by omega),
      show (⟨(j : ℕ), by omega⟩ : Fin (n₁ + n₂))
          = Fin.castAdd n₂ (⟨(j : ℕ), hj₁⟩ : Fin n₁) from Fin.ext rfl,
      Fin.append_left]
  · by_cases hj₂ : (((j : ℕ) < n₁ + n₂) : Prop)
    · rw [dif_neg hj₁, dif_pos hj₂, ProjCol.copy_kind, Fin.append_right,
        ColKind.rewKindsOf_of_lt κ₂
          (show LT.lt ((j : ℕ) - n₁) n₂ from by omega),
        ColKind.rewKindsOf_of_lt (Fin.append κ₁ κ₂) hj₂,
        show (⟨(j : ℕ), hj₂⟩ : Fin (n₁ + n₂))
            = Fin.natAdd n₁ (⟨(j : ℕ) - n₁, by omega⟩ : Fin n₂) from
          Fin.ext (by simp only [Fin.val_natAdd]; omega),
        Fin.append_right]
    · rw [dif_neg hj₁, dif_neg hj₂,
        ColKind.rewKindsOf_of_not_lt (Fin.append κ₁ κ₂) hj₂]
      rfl

/-- **The rewritten product**, over operands of arbitrary kinds: the two
rewritten blocks joined, the data columns reassembled by kind-preserving
copies, and the provenance columns multiplied. -/
def QueryGen.prodRew {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind}
    (q₁' : QueryGen (T ⊕ K) (n₁ + 1) (ColKind.rewKindsOf κ₁))
    (q₂' : QueryGen (T ⊕ K) (n₂ + 1) (ColKind.rewKindsOf κ₂)) :
    QueryGen (T ⊕ K) (n₁ + n₂ + 1)
      (ColKind.rewKindsOf (Fin.append κ₁ κ₂)) :=
  QueryGen.Retag
    (fun j => congrArg ColKind.base (QueryGen.prodRewCols_kind κ₁ κ₂ j))
    (QueryGen.Proj (QueryGen.prodRewCols κ₁ κ₂) (QueryGen.Prod q₁' q₂'))

/-- **Correctness of the rewritten product**, for arbitrary operand
kinds: conformance of the operands' rows makes the kind-dispatched
column copies faithful. -/
theorem QueryGen.prodRew_valid {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {q₁ : QueryGen T n₁ κ₁} {q₂ : QueryGen T n₂ κ₂}
    {q₁' : QueryGen (T ⊕ K) (n₁ + 1) (ColKind.rewKindsOf κ₁)}
    {q₂' : QueryGen (T ⊕ K) (n₂ + 1) (ColKind.rewKindsOf κ₂)}
    (d : AnnotatedDatabase T K)
    (ih₁ : (q₁.evaluateGen d).map GenRow.toCompositeRow
      = q₁'.evaluateRew d.toComposite)
    (ih₂ : (q₂.evaluateGen d).map GenRow.toCompositeRow
      = q₂'.evaluateRew d.toComposite) :
    ((QueryGen.Prod q₁ q₂).evaluateGen d).map GenRow.toCompositeRow
      = (QueryGen.prodRew q₁' q₂').evaluateRew d.toComposite := by
  unfold QueryGen.prodRew
  show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) d.toComposite
  simp only [QueryGen.evaluateRew]
  rw [← ih₁, ← ih₂]
  show Multiset.map _ (QueryGen.evaluateGen (QueryGen.Prod _ _) d) = _
  simp only [QueryGen.evaluateGen]
  rw [Multiset.map_product_map]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl (fun xy hxy => ?_)
  obtain ⟨hx, hy⟩ := Multiset.mem_product.mp hxy
  have hu : ∀ i, GenValue.kindOf (Fin.append (GenRow.toCompositeRow xy.1)
        (GenRow.toCompositeRow xy.2) i)
      = (Fin.append (ColKind.rewKindsOf κ₁) (ColKind.rewKindsOf κ₂) i).base := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · rw [Fin.append_left, Fin.append_left]
      exact GenRow.toCompositeRow_conform xy.1
        (QueryGen.evaluateGen_conform q₁ d xy.1 hx) a
    · rw [Fin.append_right, Fin.append_right]
      exact GenRow.toCompositeRow_conform xy.2
        (QueryGen.evaluateGen_conform q₂ d xy.2 hy) b
  simp only [Function.comp_apply, Prod.map]
  funext j
  rw [GenRow.toCompositeRow_coord]
  show _ = ProjCol.evalRew (QueryGen.prodRewCols κ₁ κ₂ j) _
  unfold QueryGen.prodRewCols
  by_cases hj₁ : (((j : ℕ) < n₁) : Prop)
  · rw [dif_pos (show LT.lt (j : ℕ) (n₁ + n₂) from by omega), dif_pos hj₁,
      ProjCol.copy_evalRew _ _ (hu _), Fin.append_left]
    dsimp only
    rw [show (⟨(j : ℕ), by omega⟩ : Fin (n₁ + n₂))
        = Fin.castAdd n₂ (⟨(j : ℕ), hj₁⟩ : Fin n₁) from Fin.ext rfl,
      Fin.append_left,
      show (⟨(j : ℕ), Nat.lt_succ_of_lt hj₁⟩ : Fin (n₁ + 1))
        = Fin.castAdd 1 (⟨(j : ℕ), hj₁⟩ : Fin n₁) from Fin.ext rfl,
      GenRow.toCompositeRow_castAdd]
  · by_cases hj₂ : (((j : ℕ) < n₁ + n₂) : Prop)
    · rw [dif_pos hj₂, dif_neg hj₁, dif_pos hj₂,
        ProjCol.copy_evalRew _ _ (hu _), Fin.append_right]
      dsimp only
      rw [show (⟨(j : ℕ), hj₂⟩ : Fin (n₁ + n₂))
          = Fin.natAdd n₁ (⟨(j : ℕ) - n₁, by omega⟩ : Fin n₂) from
        Fin.ext (by simp only [Fin.val_natAdd]; omega), Fin.append_right,
        show (⟨(j : ℕ) - n₁, by omega⟩ : Fin (n₂ + 1))
          = Fin.castAdd 1 (⟨(j : ℕ) - n₁, by omega⟩ : Fin n₂) from
        Fin.ext rfl, GenRow.toCompositeRow_castAdd]
    · rw [dif_neg hj₂, dif_neg hj₁, dif_neg hj₂]
      dsimp only
      rw [GenAnn.finalize_prod]
      show _ = Sum.inl (TermG.evalRew _ _ * TermG.evalRew _ _)
      rw [show TermG.evalRew (TermG.provIndex
            (Fin.castAdd (n₂ + 1) (Fin.last n₁))
            ((Fin.append_left _ _ _).trans (ColKind.rewKindsOf_last κ₁)))
              (Fin.append (GenRow.toCompositeRow xy.1)
                (GenRow.toCompositeRow xy.2))
          = (Sum.inr xy.1.snd.finalize : T ⊕ K) from by
        show AggValue.collapseSum (Fin.append _ _
          (Fin.castAdd (n₂ + 1) (Fin.last n₁))) = _
        rw [Fin.append_left, GenRow.toCompositeRow_last]
        rfl,
        show TermG.evalRew (TermG.provIndex
            (Fin.natAdd (n₁ + 1) (Fin.last n₂))
            ((Fin.append_right _ _ _).trans (ColKind.rewKindsOf_last κ₂)))
              (Fin.append (GenRow.toCompositeRow xy.1)
                (GenRow.toCompositeRow xy.2))
          = (Sum.inr xy.2.snd.finalize : T ⊕ K) from by
        show AggValue.collapseSum (Fin.append _ _
          (Fin.natAdd (n₁ + 1) (Fin.last n₂))) = _
        rw [Fin.append_right, GenRow.toCompositeRow_last]
        rfl]
      rfl

/-! ## Difference in the rewritten world

The general evaluator keeps every row of the left operand, rewriting its
annotation to `α ⊖ Σβ` – the monus against the `⊕`-sum of the matching
rows on the right. ProvSQL's rewriting encodes that missing left outer
join as a union of two branches: rows whose data part is *absent* from
the right operand keep their annotation, rows whose data part is present
are joined against the per-key sums and subtract them. The rewritten
world's `TermG.sub` supplies the monus directly, so both branches are
plain projections of joins, and the two semijoin identities of
`Provenance.QueryRewriting` reduce them to filters of the left operand. -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- The `inl` embedding commutes with appending rows. -/
theorem inl_append {n m : ℕ} (t : Tuple (T ⊕ K) n) (s : Tuple (T ⊕ K) m) :
    Fin.append ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) n)
        ((fun k => Sum.inl (s k)) : Tuple (GenValue (T ⊕ K) K) m)
      = fun k => Sum.inl (Fin.append t s k) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- The embedding of a rebuilt annotated row is the `inl`-image of its
composite encoding. -/
theorem GenRow.toCompositeRow_ofAnnotated_inl {n : ℕ}
    (p : AnnotatedTuple T K n) :
    (GenRow.ofAnnotated p).toCompositeRow = fun k => Sum.inl (p.toComposite k) := by
  rw [GenRow.toCompositeRow_ofAnnotated]
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]
    show _ = Sum.inl (AnnotatedTuple.toComposite p (Fin.castAdd 1 i))
    rw [AnnotatedTuple.toComposite, Fin.append_left]
  · rw [Fin.append_right]
    show _ = Sum.inl (AnnotatedTuple.toComposite p (Fin.natAdd n i))
    rw [AnnotatedTuple.toComposite, Fin.append_right]
    simp only [Matrix.cons_val_fin_one]

/-- The data columns of a rewritten block, as an all-regular query: the
provenance column dropped. -/
def QueryGen.diffKeyProj {n : ℕ}
    (q : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n))) :
    QueryGen (T ⊕ K) n (ColKind.allReg n) :=
  QueryGen.Retag (fun _ => rfl)
    (QueryGen.Proj
      (fun j : Fin n => ProjCol.term (TermG.index (Fin.castAdd 1 j)
        ((ColKind.rewKindsOf_castAdd (ColKind.allReg n) j).trans rfl)))
      q)

/-- The output columns of the *unmatched* branch: the left block copied
verbatim, provenance column included. -/
def QueryGen.diffColsU {n : ℕ} :
    Tuple (ProjCol (T ⊕ K)
        (Fin.append (ColKind.rewKindsOf (ColKind.allReg n))
          (ColKind.allReg n))) (n + 1) :=
  fun j =>
    if hj : (j : ℕ) < n then
      ProjCol.term (TermG.index
        (Fin.castAdd n (Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin n)))
        ((Fin.append_left _ _ _).trans
          ((ColKind.rewKindsOf_castAdd (ColKind.allReg n) _).trans rfl)))
    else
      ProjCol.provTerm (TermG.provIndex (Fin.castAdd n (Fin.last n))
        ((Fin.append_left _ _ _).trans
          (ColKind.rewKindsOf_last (ColKind.allReg n))))

/-- The output columns of the *matched* branch: the left block's data
columns, and the monus of the two provenance columns. -/
def QueryGen.diffColsM {n : ℕ} :
    Tuple (ProjCol (T ⊕ K)
        (Fin.append (ColKind.rewKindsOf (ColKind.allReg n))
          (ColKind.rewKindsOf (ColKind.allReg n)))) (n + 1) :=
  fun j =>
    if hj : (j : ℕ) < n then
      ProjCol.term (TermG.index
        (Fin.castAdd (n + 1) (Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin n)))
        ((Fin.append_left _ _ _).trans
          ((ColKind.rewKindsOf_castAdd (ColKind.allReg n) _).trans rfl)))
    else
      ProjCol.provTerm (TermG.sub
        (TermG.provIndex (Fin.castAdd (n + 1) (Fin.last n))
          ((Fin.append_left _ _ _).trans
            (ColKind.rewKindsOf_last (ColKind.allReg n))))
        (TermG.provIndex (Fin.natAdd (n + 1) (Fin.last n))
          ((Fin.append_right _ _ _).trans
            (ColKind.rewKindsOf_last (ColKind.allReg n)))))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
theorem QueryGen.diffColsU_kind {n : ℕ} (j : Fin (n + 1)) :
    (QueryGen.diffColsU (T := T) (K := K) j).kind
      = ColKind.rewKindsOf (ColKind.allReg n) j := by
  unfold QueryGen.diffColsU
  by_cases hj : (((j : ℕ) < n) : Prop)
  · rw [dif_pos hj]
    exact (ColKind.rewKindsOf_of_lt (ColKind.allReg n) hj).symm
  · rw [dif_neg hj]
    exact (ColKind.rewKindsOf_of_not_lt (ColKind.allReg n) hj).symm

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
theorem QueryGen.diffColsM_kind {n : ℕ} (j : Fin (n + 1)) :
    (QueryGen.diffColsM (T := T) (K := K) j).kind
      = ColKind.rewKindsOf (ColKind.allReg n) j := by
  unfold QueryGen.diffColsM
  by_cases hj : (((j : ℕ) < n) : Prop)
  · rw [dif_pos hj]
    exact (ColKind.rewKindsOf_of_lt (ColKind.allReg n) hj).symm
  · rw [dif_neg hj]
    exact (ColKind.rewKindsOf_of_not_lt (ColKind.allReg n) hj).symm

/-- The unmatched branch: left rows whose data part is among the
surviving keys, keeping their annotation. -/
def QueryGen.diffBranchU {n : ℕ}
    (q₁' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n)))
    (qs : QueryGen (T ⊕ K) n (ColKind.allReg n)) :
    QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n)) :=
  QueryGen.Retag (fun j => congrArg ColKind.base (QueryGen.diffColsU_kind j))
    (QueryGen.Proj QueryGen.diffColsU
      (QueryGen.Sel
        (keyJoinCond
          (posL := fun k : Fin n => Fin.castAdd n (Fin.castAdd 1 k))
          (posR := fun k : Fin n => Fin.natAdd (n + 1) k)
          (fun k => (Fin.append_left _ _ _).trans
            ((ColKind.rewKindsOf_castAdd (ColKind.allReg n) k).trans rfl))
          (fun _ => (Fin.append_right _ _ _).trans rfl))
        (QueryGen.Prod q₁' qs)))

/-- The matched branch: left rows joined against the per-key `⊕`-sums,
subtracting them. -/
def QueryGen.diffBranchM {n : ℕ}
    (q₁' qs : QueryGen (T ⊕ K) (n + 1)
      (ColKind.rewKindsOf (ColKind.allReg n))) :
    QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n)) :=
  QueryGen.Retag (fun j => congrArg ColKind.base (QueryGen.diffColsM_kind j))
    (QueryGen.Proj QueryGen.diffColsM
      (QueryGen.Sel
        (keyJoinCond
          (posL := fun k : Fin n => Fin.castAdd (n + 1) (Fin.castAdd 1 k))
          (posR := fun k : Fin n => Fin.natAdd (n + 1) (Fin.castAdd 1 k))
          (fun k => (Fin.append_left _ _ _).trans
            ((ColKind.rewKindsOf_castAdd (ColKind.allReg n) k).trans rfl))
          (fun k => (Fin.append_right _ _ _).trans
            ((ColKind.rewKindsOf_castAdd (ColKind.allReg n) k).trans rfl)))
        (QueryGen.Prod q₁' qs)))

/-- **The rewritten difference.** -/
def QueryGen.diffRew {n : ℕ}
    (q₁' q₂' : QueryGen (T ⊕ K) (n + 1)
      (ColKind.rewKindsOf (ColKind.allReg n))) :
    QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n)) :=
  QueryGen.Sum
    (QueryGen.diffBranchU q₁'
      (QueryGen.Dedup (QueryGen.Diff (QueryGen.diffKeyProj q₁')
        (QueryGen.diffKeyProj q₂'))))
    (QueryGen.diffBranchM q₁' (QueryGen.dedupRew q₂'))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- The data embedding of tuples is injective. -/
theorem inlTuple_injective {n : ℕ} :
    Function.Injective (fun (u : Tuple T n) (k : Fin n) => (Sum.inl (u k) : T ⊕ K)) :=
  fun _ _ h => funext (fun k => Sum.inl.inj (congrFun h k))

/-- The data projection of a rewritten block. -/
theorem QueryGen.diffKeyProj_evaluateRew {n : ℕ}
    (q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n)))
    (D : Database (T ⊕ K)) (A : AnnotatedRelation T K n)
    (h : q'.evaluateRew D
      = A.map (fun p => ((fun k => Sum.inl (p.toComposite k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1)))) :
    (QueryGen.diffKeyProj q').evaluateRew D
      = A.map (fun p => ((fun k => Sum.inl (Sum.inl (p.fst k)))
          : Tuple (GenValue (T ⊕ K) K) n)) := by
  unfold QueryGen.diffKeyProj
  show QueryGen.evaluateRew (QueryGen.Retag _ _) D = _
  simp only [QueryGen.evaluateRew]
  rw [h, Multiset.map_map]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  simp only [Function.comp_apply]
  funext j
  show Sum.inl (AggValue.collapseSum
    (Sum.inl (AnnotatedTuple.toComposite p (Fin.castAdd 1 j)))) = _
  rw [AnnotatedTuple.toComposite, Fin.append_left]
  rfl

/-- The surviving keys: the deduplicated data tuples of the left operand
absent from the right one. -/
theorem QueryGen.diffSurvivors_evaluateRew {n : ℕ}
    (q₁' q₂' : QueryGen (T ⊕ K) (n + 1)
      (ColKind.rewKindsOf (ColKind.allReg n)))
    (D : Database (T ⊕ K)) (A₁ A₂ : AnnotatedRelation T K n)
    (h₁ : q₁'.evaluateRew D
      = A₁.map (fun p => ((fun k => Sum.inl (p.toComposite k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1))))
    (h₂ : q₂'.evaluateRew D
      = A₂.map (fun p => ((fun k => Sum.inl (p.toComposite k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1)))) :
    (QueryGen.Dedup (QueryGen.Diff (QueryGen.diffKeyProj q₁')
        (QueryGen.diffKeyProj q₂'))).evaluateRew D
      = (((A₁.map Prod.fst).filter
            (fun u => u ∉ A₂.map Prod.fst)).dedup).map
          (fun u => ((fun k => Sum.inl (Sum.inl (u k)))
            : Tuple (GenValue (T ⊕ K) K) n)) := by
  have hcollapse : ∀ A : AnnotatedRelation T K n,
      Multiset.map (fun u : Tuple (GenValue (T ⊕ K) K) n =>
          (GenRow.plainTuple u : Tuple (T ⊕ K) n))
        (A.map (fun p => ((fun k => Sum.inl (Sum.inl (p.fst k)))
          : Tuple (GenValue (T ⊕ K) K) n)))
        = (A.map Prod.fst).map
            (fun (u : Tuple T n) (k : Fin n) => (Sum.inl (u k) : T ⊕ K)) := by
    intro A
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun p _ => rfl)
  have hpred : Multiset.filter
      ((fun t : Tuple (T ⊕ K) n => t ∉ Multiset.map
          (fun (u : Tuple T n) (k : Fin n) => (Sum.inl (u k) : T ⊕ K))
          (Multiset.map Prod.fst A₂))
        ∘ (fun (u : Tuple T n) (k : Fin n) => (Sum.inl (u k) : T ⊕ K)))
      (Multiset.map Prod.fst A₁)
      = Multiset.filter (fun u => u ∉ Multiset.map Prod.fst A₂)
          (Multiset.map Prod.fst A₁) :=
    Multiset.filter_congr (fun u _ =>
      not_congr (Multiset.mem_map_of_injective inlTuple_injective))
  show QueryGen.evaluateRew (QueryGen.Dedup _) D = _
  simp only [QueryGen.evaluateRew]
  rw [QueryGen.diffKeyProj_evaluateRew q₁' D A₁ h₁,
    QueryGen.diffKeyProj_evaluateRew q₂' D A₂ h₂,
    map_plainTuple_map_inl, hcollapse A₁, hcollapse A₂,
    Multiset.filter_map, hpred,
    Multiset.dedup_map_of_injective inlTuple_injective, Multiset.map_map]
  rfl

/-- **The unmatched branch**: by the semijoin identity, the left rows
whose data part is a surviving key, with their annotation. -/
theorem QueryGen.diffBranchU_evaluateRew {n : ℕ}
    (q₁' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n)))
    (qs : QueryGen (T ⊕ K) n (ColKind.allReg n)) (D : Database (T ⊕ K))
    (A₁ : AnnotatedRelation T K n) (S : Multiset (Tuple T n)) (hS : S.Nodup)
    (h₁ : q₁'.evaluateRew D
      = A₁.map (fun p => ((fun k => Sum.inl (p.toComposite k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1))))
    (hs : qs.evaluateRew D
      = S.map (fun u => ((fun k => Sum.inl (Sum.inl (u k)))
          : Tuple (GenValue (T ⊕ K) K) n))) :
    (QueryGen.diffBranchU q₁' qs).evaluateRew D
      = (A₁.filter (fun p => p.fst ∈ S)).map
          (fun p => ((fun k => Sum.inl (p.toComposite k))
            : Tuple (GenValue (T ⊕ K) K) (n + 1))) := by
  unfold QueryGen.diffBranchU
  show QueryGen.evaluateRew (QueryGen.Retag _ _) D = _
  simp only [QueryGen.evaluateRew]
  rw [h₁, hs, Multiset.map_product_map]
  simp only [Multiset.filter_map, Multiset.map_map]
  refine Eq.trans (?_ : _ = Multiset.map
      (fun pr : AnnotatedTuple T K n × Tuple T n =>
        ((fun k => Sum.inl (pr.1.toComposite k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1)))
      (Multiset.filter (fun pr : AnnotatedTuple T K n × Tuple T n =>
        pr.1.fst = pr.2) (Multiset.product A₁ S))) ?_
  · refine Multiset.map_congr (Multiset.filter_congr (fun pr _ => ?_))
      (fun pr _ => ?_)
    · simp only [Function.comp_apply, Prod.map]
      rw [show Fin.append
            ((fun k => Sum.inl (pr.1.toComposite k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))
            ((fun k => Sum.inl (Sum.inl (pr.2 k)))
              : Tuple (GenValue (T ⊕ K) K) n)
          = fun k => Sum.inl (Fin.append pr.1.toComposite
              ((fun k => Sum.inl (pr.2 k)) : Tuple (T ⊕ K) n) k) from
        inl_append _ _]
      refine Iff.trans (GenPred.holdsRew_inl _ _) ?_
      refine Iff.trans (keyJoinCond_holdsPlain _ _ _ _ _) ?_
      constructor
      · intro h
        funext k
        have hk := h k
        rw [Fin.append_left, Fin.append_right, AnnotatedTuple.toComposite,
          Fin.append_left] at hk
        exact Sum.inl.inj hk
      · intro h k
        rw [Fin.append_left, Fin.append_right, AnnotatedTuple.toComposite,
          Fin.append_left, h]
    · simp only [Function.comp_apply, Prod.map]
      rw [show Fin.append
            ((fun k => Sum.inl (pr.1.toComposite k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))
            ((fun k => Sum.inl (Sum.inl (pr.2 k)))
              : Tuple (GenValue (T ⊕ K) K) n)
          = fun k => Sum.inl (Fin.append pr.1.toComposite
              ((fun k => Sum.inl (pr.2 k)) : Tuple (T ⊕ K) n) k) from
        inl_append _ _]
      funext j
      show ProjCol.evalRew (QueryGen.diffColsU j) _ = _
      unfold QueryGen.diffColsU
      by_cases hj : (((j : ℕ) < n) : Prop)
      · rw [dif_pos hj]
        show Sum.inl (AggValue.collapseSum (Sum.inl (Fin.append _ _
          (Fin.castAdd n (Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin n)))))) = _
        rw [Fin.append_left]
        exact congrArg (fun i => Sum.inl (pr.1.toComposite i)) (Fin.ext rfl)
      · rw [dif_neg hj]
        show Sum.inl (AggValue.collapseSum (Sum.inl (Fin.append _ _
          (Fin.castAdd n (Fin.last n))))) = _
        rw [Fin.append_left]
        exact congrArg (fun i => Sum.inl (pr.1.toComposite i))
          (Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega))
  · rw [show (fun pr : AnnotatedTuple T K n × Tuple T n =>
          ((fun k => Sum.inl (pr.1.toComposite k))
            : Tuple (GenValue (T ⊕ K) K) (n + 1)))
        = ((fun p : AnnotatedTuple T K n =>
            ((fun k => Sum.inl (p.toComposite k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1)))
          ∘ Prod.fst) from rfl,
      ← Multiset.map_map,
      Multiset.semijoin_proj_eq_filter A₁ S (fun p => p.fst) hS]

/-- **The matched branch**: by the keyed-projection semijoin, the left
rows whose data part carries a per-key sum, with that sum subtracted. -/
theorem QueryGen.diffBranchM_evaluateRew {n : ℕ}
    (q₁' qs : QueryGen (T ⊕ K) (n + 1)
      (ColKind.rewKindsOf (ColKind.allReg n)))
    (D : Database (T ⊕ K)) (A₁ : AnnotatedRelation T K n)
    (S : Multiset (Tuple T n)) (hS : S.Nodup) (V : Tuple T n → K)
    (h₁ : q₁'.evaluateRew D
      = A₁.map (fun p => ((fun k => Sum.inl (p.toComposite k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1))))
    (hs : qs.evaluateRew D
      = S.map (fun u => ((fun k =>
          Sum.inl (AnnotatedTuple.toComposite (⟨u, V u⟩ : AnnotatedTuple T K n) k))
            : Tuple (GenValue (T ⊕ K) K) (n + 1)))) :
    (QueryGen.diffBranchM q₁' qs).evaluateRew D
      = (A₁.filter (fun p => p.fst ∈ S)).map
          (fun p => ((fun k =>
            Sum.inl (AnnotatedTuple.toComposite (⟨p.fst, p.snd - V p.fst⟩ : AnnotatedTuple T K n) k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))) := by
  unfold QueryGen.diffBranchM
  show QueryGen.evaluateRew (QueryGen.Retag _ _) D = _
  simp only [QueryGen.evaluateRew]
  rw [h₁, show qs.evaluateRew D
      = (S.map (fun u => (⟨u, V u⟩ : AnnotatedTuple T K n))).map
          (fun p : AnnotatedTuple T K n =>
            ((fun k => Sum.inl (AnnotatedTuple.toComposite p k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))) from by
    rw [Multiset.map_map]; exact hs,
    Multiset.map_product_map]
  simp only [Multiset.filter_map, Multiset.map_map]
  refine Eq.trans (?_ : _ = Multiset.map
      (fun pr : AnnotatedTuple T K n × AnnotatedTuple T K n =>
        ((fun k => Sum.inl (AnnotatedTuple.toComposite (⟨pr.1.fst, pr.1.snd - pr.2.snd⟩
            : AnnotatedTuple T K n) k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1)))
      (Multiset.filter (fun pr : AnnotatedTuple T K n × AnnotatedTuple T K n =>
        pr.1.fst = pr.2.fst)
        (Multiset.product A₁
          (S.map (fun u => (⟨u, V u⟩ : AnnotatedTuple T K n)))))) ?_
  · refine Multiset.map_congr (Multiset.filter_congr (fun pr _ => ?_))
      (fun pr _ => ?_)
    · simp only [Function.comp_apply, Prod.map]
      rw [show Fin.append
            ((fun k => Sum.inl (pr.1.toComposite k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))
            ((fun k => Sum.inl (pr.2.toComposite k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))
          = fun k => Sum.inl (Fin.append pr.1.toComposite
              pr.2.toComposite k) from inl_append _ _]
      refine Iff.trans (GenPred.holdsRew_inl _ _) ?_
      refine Iff.trans (keyJoinCond_holdsPlain _ _ _ _ _) ?_
      constructor
      · intro h
        funext k
        have hk := h k
        rw [Fin.append_left, Fin.append_right, AnnotatedTuple.toComposite,
          AnnotatedTuple.toComposite, Fin.append_left, Fin.append_left] at hk
        exact Sum.inl.inj hk
      · intro h k
        rw [Fin.append_left, Fin.append_right, AnnotatedTuple.toComposite,
          AnnotatedTuple.toComposite, Fin.append_left, Fin.append_left, h]
    · simp only [Function.comp_apply, Prod.map]
      rw [show Fin.append
            ((fun k => Sum.inl (pr.1.toComposite k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))
            ((fun k => Sum.inl (pr.2.toComposite k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))
          = fun k => Sum.inl (Fin.append pr.1.toComposite
              pr.2.toComposite k) from inl_append _ _]
      funext j
      show ProjCol.evalRew (QueryGen.diffColsM j) _ = _
      unfold QueryGen.diffColsM
      by_cases hj : (((j : ℕ) < n) : Prop)
      · rw [dif_pos hj]
        show Sum.inl (AggValue.collapseSum (Sum.inl (Fin.append _ _
          (Fin.castAdd (n + 1)
            (Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin n)))))) = _
        rw [Fin.append_left]
        show Sum.inl (AnnotatedTuple.toComposite pr.1
          (Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin n))) = _
        refine congrArg Sum.inl ?_
        refine Eq.trans ((AnnotatedTuple.toComposite_coord pr.1
          (Fin.castAdd 1 (⟨(j : ℕ), hj⟩ : Fin n))).trans
          (dif_pos (show LT.lt (j : ℕ) n from hj))) ?_
        refine Eq.trans (congrArg (fun i => Sum.inl (pr.1.fst i))
          (Fin.ext rfl)) ?_
        exact ((AnnotatedTuple.toComposite_coord
          (⟨pr.1.fst, pr.1.snd - pr.2.snd⟩ : AnnotatedTuple T K n) j).trans
          (dif_pos hj)).symm
      · rw [dif_neg hj]
        show Sum.inl (TermG.evalRew _ _ - TermG.evalRew _ _) = _
        rw [show TermG.evalRew (TermG.provIndex
              (Fin.castAdd (n + 1) (Fin.last n))
              ((Fin.append_left _ _ _).trans
                (ColKind.rewKindsOf_last (ColKind.allReg n))))
                ((fun k => Sum.inl (Fin.append pr.1.toComposite
                  pr.2.toComposite k))
                  : Tuple (GenValue (T ⊕ K) K) (n + 1 + (n + 1)))
            = (Sum.inr pr.1.snd : T ⊕ K) from by
          show AggValue.collapseSum (Sum.inl (Fin.append _ _
            (Fin.castAdd (n + 1) (Fin.last n)))) = _
          rw [Fin.append_left]
          exact (AnnotatedTuple.toComposite_coord _ _).trans
            (dif_neg (by simp only [Fin.val_last]; omega)),
          show TermG.evalRew (TermG.provIndex
              (Fin.natAdd (n + 1) (Fin.last n))
              ((Fin.append_right _ _ _).trans
                (ColKind.rewKindsOf_last (ColKind.allReg n))))
                ((fun k => Sum.inl (Fin.append pr.1.toComposite
                  pr.2.toComposite k))
                  : Tuple (GenValue (T ⊕ K) K) (n + 1 + (n + 1)))
            = (Sum.inr pr.2.snd : T ⊕ K) from by
          show AggValue.collapseSum (Sum.inl (Fin.append _ _
            (Fin.natAdd (n + 1) (Fin.last n)))) = _
          rw [Fin.append_right]
          exact (AnnotatedTuple.toComposite_coord _ _).trans
            (dif_neg (by simp only [Fin.val_last]; omega))]
        refine congrArg Sum.inl ?_
        have hsub : HSub.hSub (Sum.inr pr.1.snd : T ⊕ K) (Sum.inr pr.2.snd)
            = (Sum.inr (pr.1.snd - pr.2.snd) : T ⊕ K) := rfl
        exact hsub.trans
          ((AnnotatedTuple.toComposite_coord
            (⟨pr.1.fst, pr.1.snd - pr.2.snd⟩ : AnnotatedTuple T K n) j).trans
            (dif_neg hj)).symm
  · exact Multiset.semijoin_keyed_proj_eq_filter A₁ S
      (fun u => (⟨u, V u⟩ : AnnotatedTuple T K n))
      (fun p => p.fst) (fun p => p.fst)
      (fun p q : AnnotatedTuple T K n =>
        ((fun k => Sum.inl (AnnotatedTuple.toComposite
            (⟨p.fst, p.snd - q.snd⟩ : AnnotatedTuple T K n) k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1)))
      hS (fun v _ => rfl)

/-- **Correctness of the rewritten difference**, for arbitrary rewritten
operands: the two branches partition the left operand by whether its data
part occurs on the right, and on the unmatched part the subtracted sum is
`𝟘`. -/
theorem QueryGen.diffRew_valid {n : ℕ}
    {q₁ q₂ : QueryGen T n (ColKind.allReg n)}
    {q₁' q₂' : QueryGen (T ⊕ K) (n + 1)
      (ColKind.rewKindsOf (ColKind.allReg n))}
    (d : AnnotatedDatabase T K)
    (ih₁ : (q₁.evaluateGen d).map GenRow.toCompositeRow
      = q₁'.evaluateRew d.toComposite)
    (ih₂ : (q₂.evaluateGen d).map GenRow.toCompositeRow
      = q₂'.evaluateRew d.toComposite) :
    ((QueryGen.Diff q₁ q₂).evaluateGen d).map GenRow.toCompositeRow
      = (QueryGen.diffRew q₁' q₂').evaluateRew d.toComposite := by
  have hE : ∀ (q : QueryGen T n (ColKind.allReg n))
      (q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf (ColKind.allReg n))),
      (q.evaluateGen d).map GenRow.toCompositeRow = q'.evaluateRew d.toComposite →
      q'.evaluateRew d.toComposite
        = (q.evaluateAnnotatedGen d).map (fun p =>
            ((fun k => Sum.inl (AnnotatedTuple.toComposite p k))
              : Tuple (GenValue (T ⊕ K) K) (n + 1))) := by
    intro q q' ih
    rw [← ih, QueryGen.map_toCompositeRow_of_reg q (fun _ => rfl) d]
    unfold AnnotatedRelation.toComposite
    rw [Multiset.map_map]
    rfl
  have hE₁ := hE q₁ q₁' ih₁
  have hE₂ := hE q₂ q₂' ih₂
  -- the two branch computations
  have hU := QueryGen.diffBranchU_evaluateRew q₁'
    (QueryGen.Dedup (QueryGen.Diff (QueryGen.diffKeyProj q₁')
      (QueryGen.diffKeyProj q₂'))) d.toComposite
    (q₁.evaluateAnnotatedGen d)
    ((((q₁.evaluateAnnotatedGen d).map Prod.fst).filter
      (fun u => u ∉ (q₂.evaluateAnnotatedGen d).map Prod.fst)).dedup)
    (Multiset.nodup_dedup _) hE₁
    (QueryGen.diffSurvivors_evaluateRew q₁' q₂' d.toComposite
      (q₁.evaluateAnnotatedGen d) (q₂.evaluateAnnotatedGen d) hE₁ hE₂)
  have hsums : (QueryGen.dedupRew q₂').evaluateRew d.toComposite
      = ((q₂.evaluateAnnotatedGen d).map Prod.fst).dedup.map (fun u =>
          ((fun k => Sum.inl (AnnotatedTuple.toComposite
            (⟨u, (Multiset.map Prod.snd (Multiset.filter
              (fun q : AnnotatedTuple T K n => q.1 = u)
              (q₂.evaluateAnnotatedGen d))).sum⟩ : AnnotatedTuple T K n) k))
            : Tuple (GenValue (T ⊕ K) K) (n + 1))) := by
    rw [← QueryGen.dedupRew_valid d ih₂]
    show Multiset.map GenRow.toCompositeRow
      (QueryGen.evaluateGen (QueryGen.Dedup q₂) d) = _
    simp only [QueryGen.evaluateGen]
    rw [show (Multiset.map GenRow.toAnnotated (q₂.evaluateGen d))
        = q₂.evaluateAnnotatedGen d from rfl, groupByKey_eq_dedup_map,
      Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ =>
      GenRow.toCompositeRow_ofAnnotated_inl _)
  have hM := QueryGen.diffBranchM_evaluateRew q₁' (QueryGen.dedupRew q₂')
    d.toComposite (q₁.evaluateAnnotatedGen d)
    (((q₂.evaluateAnnotatedGen d).map Prod.fst).dedup)
    (Multiset.nodup_dedup _)
    (fun u => (Multiset.map Prod.snd (Multiset.filter
      (fun q : AnnotatedTuple T K n => q.1 = u)
      (q₂.evaluateAnnotatedGen d))).sum) hE₁ hsums
  -- assemble
  show Multiset.map GenRow.toCompositeRow
    (QueryGen.evaluateGen (QueryGen.Diff q₁ q₂) d)
      = QueryGen.evaluateRew (QueryGen.Sum _ _) d.toComposite
  simp only [QueryGen.evaluateGen, QueryGen.evaluateRew]
  rw [hU, hM]
  rw [show (Multiset.map GenRow.toAnnotated (q₁.evaluateGen d))
      = q₁.evaluateAnnotatedGen d from rfl,
    show (Multiset.map GenRow.toAnnotated (q₂.evaluateGen d))
      = q₂.evaluateAnnotatedGen d from rfl]
  rw [Multiset.map_map]
  -- the unmatched filter is the complement of the matched one
  rw [show (Multiset.filter (fun p : AnnotatedTuple T K n =>
        p.fst ∈ (((q₁.evaluateAnnotatedGen d).map Prod.fst).filter
          (fun u => u ∉ (q₂.evaluateAnnotatedGen d).map Prod.fst)).dedup)
        (q₁.evaluateAnnotatedGen d))
      = Multiset.filter (fun p : AnnotatedTuple T K n =>
          ¬ (p.fst ∈ (q₂.evaluateAnnotatedGen d).map Prod.fst))
        (q₁.evaluateAnnotatedGen d) from
    Multiset.filter_congr (fun p hp => by
      rw [Multiset.mem_dedup, Multiset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Multiset.mem_map_of_mem _ hp, h⟩⟩)]
  rw [show (Multiset.filter (fun p : AnnotatedTuple T K n =>
        p.fst ∈ ((q₂.evaluateAnnotatedGen d).map Prod.fst).dedup)
        (q₁.evaluateAnnotatedGen d))
      = Multiset.filter (fun p : AnnotatedTuple T K n =>
          p.fst ∈ (q₂.evaluateAnnotatedGen d).map Prod.fst)
        (q₁.evaluateAnnotatedGen d) from
    Multiset.filter_congr (fun p _ => Multiset.mem_dedup)]
  -- on the unmatched rows the subtracted sum is `𝟘`
  rw [show Multiset.map (fun p : AnnotatedTuple T K n =>
        ((fun k => Sum.inl (AnnotatedTuple.toComposite p k))
          : Tuple (GenValue (T ⊕ K) K) (n + 1)))
        (Multiset.filter (fun p : AnnotatedTuple T K n =>
          ¬ (p.fst ∈ (q₂.evaluateAnnotatedGen d).map Prod.fst))
          (q₁.evaluateAnnotatedGen d))
      = Multiset.map (fun p : AnnotatedTuple T K n =>
          ((fun k => Sum.inl (AnnotatedTuple.toComposite
            (⟨p.fst, p.snd - (Multiset.map Prod.snd (Multiset.filter
              (fun q : AnnotatedTuple T K n => q.1 = p.fst)
              (q₂.evaluateAnnotatedGen d))).sum⟩ : AnnotatedTuple T K n) k))
            : Tuple (GenValue (T ⊕ K) K) (n + 1)))
          (Multiset.filter (fun p : AnnotatedTuple T K n =>
            ¬ (p.fst ∈ (q₂.evaluateAnnotatedGen d).map Prod.fst))
            (q₁.evaluateAnnotatedGen d)) from
    Multiset.map_congr rfl (fun p hp => by
      have hp' := (Multiset.mem_filter.mp hp).2
      rw [show (Multiset.filter (fun q : AnnotatedTuple T K n => q.1 = p.fst)
            (q₂.evaluateAnnotatedGen d)) = 0 from
        Multiset.filter_eq_nil.mpr (fun q hq hqe =>
          hp' (hqe ▸ Multiset.mem_map_of_mem Prod.fst hq))]
      rw [Multiset.map_zero, Multiset.sum_zero, monus_zero]
      rfl)]
  have hsplit : Multiset.filter (fun p : AnnotatedTuple T K n =>
        ¬ (p.fst ∈ (q₂.evaluateAnnotatedGen d).map Prod.fst))
        (q₁.evaluateAnnotatedGen d)
      + Multiset.filter (fun p : AnnotatedTuple T K n =>
          p.fst ∈ (q₂.evaluateAnnotatedGen d).map Prod.fst)
        (q₁.evaluateAnnotatedGen d)
      = q₁.evaluateAnnotatedGen d := by
    rw [add_comm]
    exact Multiset.filter_add_not _ _
  rw [← Multiset.map_add, hsplit]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  simp only [Function.comp_apply]
  rw [GenRow.toCompositeRow_ofAnnotated_inl]
  refine congrArg (fun v : K => ((fun k => Sum.inl
    (AnnotatedTuple.toComposite (⟨p.fst, v⟩ : AnnotatedTuple T K n) k))
      : Tuple (GenValue (T ⊕ K) K) (n + 1))) ?_
  exact congrArg (fun v : K => p.snd - v)
    (groupByKey_find_eq_filter_sum (q₂.evaluateAnnotatedGen d) p.fst)

/-! ## The classical rewriting at the uniform kind vector -/

/-- The classical rewriting, retagged to `ColKind.rewKindsOf κ`.
`QueryGen.rewritingGen` targets `ColKind.rewKinds n` – the per-index
`if k < n` form – which is only *pointwise* equal to the uniform
`Fin.append κ prov` the congruences below consume. Retagging once here
(semantically the identity) lets a congruence sit directly above the
classical base rule instead of threading an explicit `retag` step. -/
def QueryGen.rewritingGenOf {n : ℕ} {κ : Fin n → ColKind}
    (q : QueryGen T n κ) (hq : q.classical) :
    QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf κ) :=
  QueryGen.Retag
    (fun k => (ColKind.rewKinds_base k).trans
      (ColKind.rewKindsOf_base_of_reg (QueryGen.classical_kinds q hq) k).symm)
    (q.rewritingGen hq)

/-! ## The closure -/

/-- **The compositional closure of the rewriting rules**: the three base
rewritings – classical blocks, fused `HAVING` sites and bare groupings –
composed under union, selection, projection, deduplication, product and
difference, with the kind-retagging of `QueryGen.Retag` available to
adapt a subderivation's output kinds. The `HAVING`-site rule
`havingPred` keeps the group keys and the aggregate tokens as output
columns and admits any aggregate-only predicate. -/
inductive QueryGen.RewritesTo :
    {n : ℕ} → {κ : Fin n → ColKind} → {κ' : Fin (n + 1) → ColKind} →
    QueryGen T n κ → QueryGen (T ⊕ K) (n + 1) κ' → Prop
  | classical {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (hq : q.classical) :
      RewritesTo q (q.rewritingGenOf hq)
  | gamma {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
      (fs : Tuple (SeqAggFunc T) n₂) (qg : QueryGen T m (ColKind.allReg m))
      (hq : qg.classical) :
      RewritesTo (QueryGen.Gamma is ts fs qg)
        (QueryGen.gammaRew is ts fs qg hq)
  | havingPred {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
      (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
      (φ : GenPred T (ColKind.gammaKinds n₁ n₂)) (hφ : φ.aggOnly = true)
      (qg : QueryGen T m (ColKind.allReg m)) (hq : qg.classical) :
      RewritesTo (QueryGen.Sel φ (QueryGen.Gamma is ts fs qg))
        (QueryGen.havingPredRew is ts fs φ qg hq)
  | retag {n : ℕ} {κ : Fin n → ColKind} {κ' κ'' : Fin (n + 1) → ColKind}
      {q : QueryGen T n κ} {q' : QueryGen (T ⊕ K) (n + 1) κ'}
      (h : ∀ k, (κ' k).base = (κ'' k).base) :
      RewritesTo q q' → RewritesTo q (QueryGen.Retag h q')
  | sum {n : ℕ} {κ : Fin n → ColKind} {κ' : Fin (n + 1) → ColKind}
      {q₁ q₂ : QueryGen T n κ}
      {q₁' q₂' : QueryGen (T ⊕ K) (n + 1) κ'} :
      RewritesTo q₁ q₁' → RewritesTo q₂ q₂' →
      RewritesTo (QueryGen.Sum q₁ q₂) (QueryGen.Sum q₁' q₂')
  | dedup {n : ℕ} {q : QueryGen T n (ColKind.allReg n)}
      {q' : QueryGen (T ⊕ K) (n + 1)
        (ColKind.rewKindsOf (ColKind.allReg n))} :
      RewritesTo q q' →
      RewritesTo (QueryGen.Dedup q) (QueryGen.dedupRew q')
  | diff {n : ℕ} {q₁ q₂ : QueryGen T n (ColKind.allReg n)}
      {q₁' q₂' : QueryGen (T ⊕ K) (n + 1)
        (ColKind.rewKindsOf (ColKind.allReg n))} :
      RewritesTo q₁ q₁' → RewritesTo q₂ q₂' →
      RewritesTo (QueryGen.Diff q₁ q₂) (QueryGen.diffRew q₁' q₂')
  | sel {n : ℕ} {κ : Fin n → ColKind} {q : QueryGen T n κ}
      {q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf κ)}
      (φ : GenPred T κ) (hφ : φ.hasAggAtom = false) :
      RewritesTo q q' →
      RewritesTo (QueryGen.Sel φ q) (QueryGen.Sel φ.castRew q')
  | proj {n m : ℕ} {κ : Fin n → ColKind} {q : QueryGen T n κ}
      {q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKindsOf κ)}
      (ps : Tuple (ProjCol T κ) m) :
      RewritesTo q q' →
      RewritesTo (QueryGen.Proj ps q)
        (QueryGen.Retag
          (κ' := ColKind.rewKindsOf (fun j' => (ps j').kind))
          (fun j => by
            by_cases hj : (j : ℕ) < m
            · rw [dif_pos hj, ProjCol.castRew_kind,
                show ColKind.rewKindsOf (fun j' => (ps j').kind) j
                  = (ps ⟨(j : ℕ), hj⟩).kind from
                  (congrArg (ColKind.rewKindsOf _)
                    (Fin.ext rfl : j = Fin.castAdd 1 ⟨(j : ℕ), hj⟩)).trans
                    (ColKind.rewKindsOf_castAdd _ _)]
            · rw [dif_neg hj,
                show ColKind.rewKindsOf (fun j' => (ps j').kind) j
                  = ColKind.prov from
                  (congrArg (ColKind.rewKindsOf _)
                    (Fin.ext (by simp only [Fin.val_last]; omega)
                      : j = Fin.last m)).trans
                    (ColKind.rewKindsOf_last _)]
              rfl)
          (QueryGen.Proj
            (fun j : Fin (m + 1) =>
              if hj : (j : ℕ) < m then (ps ⟨(j : ℕ), hj⟩).castRew
              else ProjCol.provTerm (TermG.provIndex (Fin.last n)
                (ColKind.rewKindsOf_last κ)))
            q'))
  | prod {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
      {q₁ : QueryGen T n₁ κ₁} {q₂ : QueryGen T n₂ κ₂}
      {q₁' : QueryGen (T ⊕ K) (n₁ + 1) (ColKind.rewKindsOf κ₁)}
      {q₂' : QueryGen (T ⊕ K) (n₂ + 1) (ColKind.rewKindsOf κ₂)} :
      RewritesTo q₁ q₁' → RewritesTo q₂ q₂' →
      RewritesTo (QueryGen.Prod q₁ q₂) (QueryGen.prodRew q₁' q₂')

/-- **Whole-query correctness of the compositional rewriting**: along the
closure, the general evaluator's rows, embedded token-aware into the
composite domain, are exactly the rewritten world's evaluation. -/
theorem QueryGen.rewritesTo_valid {n : ℕ} {κ : Fin n → ColKind}
    {κ' : Fin (n + 1) → ColKind} {q : QueryGen T n κ}
    {q' : QueryGen (T ⊕ K) (n + 1) κ'}
    (h : QueryGen.RewritesTo q q') (d : AnnotatedDatabase T K) :
    (q.evaluateGen d).map GenRow.toCompositeRow
      = q'.evaluateRew d.toComposite := by
  induction h with
  | classical q hq =>
    show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) _
    simp only [QueryGen.evaluateRew]
    rw [QueryGen.map_toCompositeRow_of_reg q (QueryGen.classical_kinds q hq) d,
      QueryGen.rewritingGen_valid q hq d,
      QueryGen.evaluateRew_plain _ (QueryGen.rewritingGen_noGammaTok q hq)]
  | gamma is ts fs qg hq =>
    exact QueryGen.gammaRew_valid is ts fs qg hq d
  | havingPred is ts fs φ hφ qg hq =>
    exact QueryGen.havingPredRew_valid is ts fs φ hφ qg hq d
  | retag h₀ _ ih => exact ih
  | sum h₁ h₂ ih₁ ih₂ =>
    show Multiset.map _ (QueryGen.evaluateGen (QueryGen.Sum _ _) d) = _
    simp only [QueryGen.evaluateGen, QueryGen.evaluateRew]
    rw [Multiset.map_add]
    exact congrArg₂ (· + ·) ih₁ ih₂
  | dedup h ih => exact QueryGen.dedupRew_valid d ih
  | diff h₁ h₂ ih₁ ih₂ => exact QueryGen.diffRew_valid d ih₁ ih₂
  | sel φ hφ h ih =>
    show Multiset.map _ (QueryGen.evaluateGen (QueryGen.Sel _ _) d) = _
    simp only [QueryGen.evaluateGen, QueryGen.evaluateRew]
    rw [if_neg (by simp [hφ]), ← ih, Multiset.filter_map]
    exact congrArg _ (Multiset.filter_congr (fun r _ =>
      (φ.castRew_holdsRew r).symm))
  | @proj n m κ q q' ps h ih =>
    show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) _
    simp only [QueryGen.evaluateRew]
    rw [← ih]
    show Multiset.map _ (QueryGen.evaluateGen (QueryGen.Proj _ _) d) = _
    simp only [QueryGen.evaluateGen, Multiset.map_map]
    refine Multiset.map_congr rfl (fun r _ => ?_)
    simp only [Function.comp_apply]
    funext j
    rw [GenRow.toCompositeRow_coord]
    by_cases hj : (j : ℕ) < m
    · rw [dif_pos hj, dif_pos hj]
      exact ((ps ⟨(j : ℕ), hj⟩).castRew_evalRew r).symm
    · rw [dif_neg hj, dif_neg hj]
      refine Eq.trans (congrArg (fun v => (Sum.inl (Sum.inr v)
          : GenValue (T ⊕ K) K))
        (GenAnn.finalize_cash _ _ _ Multiset.inter_le_left)) ?_
      show _ = Sum.inl (AggValue.collapseSum
        (GenRow.toCompositeRow r (Fin.last n)))
      rw [GenRow.toCompositeRow_last]
      rfl
  | prod h₁ h₂ ih₁ ih₂ => exact QueryGen.prodRew_valid d ih₁ ih₂

/-- On an all-regular source the correctness specialises to the shape of
the classical and `HAVING`-site statements: the annotated semantics,
folded into composite tuples and embedded by `inl`. -/
theorem QueryGen.rewritesTo_valid_reg {n : ℕ} {κ : Fin n → ColKind}
    {κ' : Fin (n + 1) → ColKind} {q : QueryGen T n κ}
    {q' : QueryGen (T ⊕ K) (n + 1) κ'}
    (h : QueryGen.RewritesTo q q') (hκ : ∀ k, κ k = ColKind.reg)
    (d : AnnotatedDatabase T K) :
    Multiset.map (fun t : Tuple (T ⊕ K) (n + 1) =>
        ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) (n + 1)))
      ((q.evaluateAnnotatedGen d).toComposite)
      = q'.evaluateRew d.toComposite :=
  (QueryGen.map_toCompositeRow_of_reg q hκ d).symm.trans
    (QueryGen.rewritesTo_valid h d)
