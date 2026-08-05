/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggValue

/-!
# Kind-indexed general queries and their annotated semantics

The general (non-fused) HAVING semantics: aggregate values produced by a
grouping operator `γ^≼` are carried through further operators – projection,
join, union, additional selections – as symbolic tokens (`AggValue`) in
dedicated *columns*, and compared downstream, the possible worlds of such a
comparison being those of the *originating* group.

## Kind-indexed syntax

Queries are indexed by a column-kind vector `κ : Fin n → ColKind`
(regular vs aggregate-token), so that the scope conditions are enforced
statically and no theorem carries a well-formedness hypothesis:

* `Gamma` (the decomposed `γ^≼`) takes an all-regular input – no
  aggregation *over* aggregate values;
* `Dedup` and `Diff` exist only at all-regular kind vectors – no
  deduplication or difference over token columns (ProvSQL rejects these);
* projection columns are either regular terms over regular columns
  (`ProjCol.term`) or verbatim copies of token columns (`ProjCol.token`) –
  no arithmetic over tokens (the constant-folded normal form);
* selection atoms are regular comparisons over regular columns, or a
  comparison of one bare token column against a regular term
  (the normal form after ProvSQL's `normalize_agg_comparison`).

## Factored annotations and the σ/predsem combination

The row annotation of the general evaluator is kept in *factored* form
`GenAnn`: a concrete part `base : K` together with `pending`, a multiset
of group-existence factors – one entry per `γ`-group whose tokens have
not yet been compared, recorded as the group's occurrence-annotation list
`l` and worth `δ(⊕ l)`. The effective annotation of a row is
`base ⊗ ⊗_{l ∈ pending} δ(⊕ l)` (`GenAnn.finalize`).

This factoring implements the *replace-the-δ-factor* combination rule:

* `Gamma` outputs rows with `base = 𝟙` and the group's factor pending –
  an uncompared group row finalizes to `δ(⊕ U)`, as in ProvSQL;
* a selection with aggregate atoms multiplies the predicate provenance
  `predsem(ψ)` into `base` and removes a pending group factor exactly
  when the compared occurrences are that whole group – every compared
  token carries the factor's annotation list. In that case the predicate
  provenance ranges over the non-empty worlds of the very same
  occurrences, so it subsumes the group-existence factor, and conjoining
  both would count it twice in a non-idempotent semiring. A predicate
  comparing tokens of *several* groups keeps every group factor: its
  predicate provenance does not entail each group's existence (a
  disjunction guards only the disjunct that fires), and likewise a
  predicate that does not *entail existence* at all
  (`GenPred.entailsExistence` – e.g. an aggregate atom `∨`-mixed with a
  regular atom, whose `χ` can fire in worlds where the group is empty)
  supersedes nothing. This mirrors ProvSQL's structural supersede
  (`cmp_supersede.cpp` with `having_entails_group_existence`), which
  drops a δ only when its ⊕-operands are exactly the compared
  aggregates' occurrence tokens and the predicate entails existence.
  Annotations accumulated from traversed operators (join partners in
  `base`, other groups' pending entries) are always preserved;
* a second selection comparing the same group's tokens finds no pending
  entry left and simply multiplies: repeated comparisons yield the
  `⊗`-product of their predicate provenances, matching the circuits
  ProvSQL builds (`times` of `cmp` gates) – which coincides with the
  joint possible-world reading in idempotent semirings;
* a projection dropping the last copy of a token column cashes the
  group's factor into `base` (the group can never be compared again).

`∧ ↦ ⊗`, `∨ ↦ ⊕` and `¬` pushed down to the atoms by De Morgan duality
with comparison-operator complementation, exactly as in `HavingPred` and
in ProvSQL. A selection whose predicate contains *no* aggregate atom
filters classically, matching `Query.evaluateAnnotated`.

Scalar aggregation (aggregation without grouping, whose empty input is a
real possible world in ProvSQL) is out of scope: `Gamma` is the grouped
operator only.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-- The kind of a column: a regular value or an aggregate token. -/
inductive ColKind where
  | reg | agg | prov
  deriving DecidableEq

/-- The value-arm kind of a column kind: `prov` columns hold ordinary
values (as ProvSQL's uuid columns do), so their conformance arm is
`reg`. -/
def ColKind.base : ColKind → ColKind
  | ColKind.agg => ColKind.agg
  | _ => ColKind.reg

theorem ColKind.base_eq_reg_of_ne_agg {c : ColKind} (h : c ≠ ColKind.agg) :
    c.base = ColKind.reg := by
  cases c
  · rfl
  · exact absurd rfl h
  · rfl


/-- A lifted column value: a regular value or an aggregate token. -/
abbrev GenValue (T K : Type) := T ⊕ AggValue T K

/-- The factored annotation of a row of the general evaluator: the
concrete part `base`, and one pending group-existence factor per
`γ`-group whose tokens have not been compared yet, recorded as the
group's occurrence-annotation list. -/
structure GenAnn (K : Type) where
  /-- The concrete annotation accumulated so far. -/
  base : K
  /-- The occurrence-annotation lists of the uncompared groups. -/
  pending : Multiset (List K)

/-- The effective annotation: the concrete part times the pending
group-existence factors `δ(⊕ l)`. -/
def GenAnn.finalize (a : GenAnn K) : K :=
  a.base * (a.pending.map (fun l => SemiringWithMonus.delta l.sum)).prod

/-- A row of the general evaluator. -/
abbrev GenRow (T K : Type) (n : ℕ) := Tuple (GenValue T K) n × GenAnn K

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- A row with nothing pending finalizes to its concrete part. -/
@[simp] theorem GenAnn.finalize_of_pending_zero (b : K) :
    (⟨b, 0⟩ : GenAnn K).finalize = b := by
  simp [GenAnn.finalize]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- An uncompared `γ`-row (concrete part `𝟙`, its group factor pending)
finalizes to `δ(⊕ U)` – the ProvSQL annotation of a plain `GROUP BY`
output row. -/
@[simp] theorem GenAnn.finalize_gamma (l : List K) :
    (⟨1, {l}⟩ : GenAnn K).finalize = SemiringWithMonus.delta l.sum := by
  simp [GenAnn.finalize]

/-! ## Terms over regular columns -/

/-- A term over the regular columns of a kind-indexed tuple: the `index`
constructor requires its column to be regular, so terms over token
columns are unrepresentable. -/
inductive TermG (T : Type) {n : ℕ} (κ : Fin n → ColKind) where
  | const : T → TermG T κ
  | index : (k : Fin n) → κ k = ColKind.reg → TermG T κ
  | provIndex : (k : Fin n) → κ k = ColKind.prov → TermG T κ
  /-- The aggregate-comparison gate (ProvSQL's `provsql_having`): the
  predicate provenance of comparing the token in column `k` against the
  term. Its faithful semantics lives in the rewritten world's term
  evaluator; the generic evaluators give it a total junk value, and on
  token-free kinds the constructor is unrepresentable. -/
  | cmpAgg : (k : Fin n) → κ k = ColKind.agg → CompOp → TermG T κ →
      TermG T κ
  /-- The regular-comparison indicator gate: the characteristic value
  `χ` of a comparison between two regular terms – `𝟙` if it holds on the
  row, `𝟘` otherwise. It is the primitive a `HAVING` predicate
  needs for its *regular* atoms, and like `cmpAgg` its faithful semantics
  lives in the rewritten world's term evaluator – the generic evaluators
  give it a total junk value. Unlike `cmpAgg` it carries no kind
  constraint, so it is representable over all-regular columns: the
  fragment on which the rewritten world's evaluator collapses to the
  plain semantics is cut out by `TermG.chiFree` instead. -/
  | chiGate : CompOp → TermG T κ → TermG T κ → TermG T κ
  | add : TermG T κ → TermG T κ → TermG T κ
  | sub : TermG T κ → TermG T κ → TermG T κ
  | mul : TermG T κ → TermG T κ → TermG T κ

/-- Evaluation of a term on a lifted tuple. On the regular columns the
kind index guarantees a regular value; the token arm of `collapseSum` is
never reached on kind-conformant tuples and merely keeps the function
total. -/
def TermG.eval {κ : Fin n → ColKind} (t : TermG T κ)
    (u : Tuple (GenValue T K) n) : T :=
  match t with
  | .const a => a
  | .index k _ => AggValue.collapseSum (u k)
  | .provIndex k _ => AggValue.collapseSum (u k)
  | .cmpAgg _ _ _ _ => 0
  | .chiGate _ _ _ => 0
  | .add t₁ t₂ => t₁.eval u + t₂.eval u
  | .sub t₁ t₂ => t₁.eval u - t₂.eval u
  | .mul t₁ t₂ => t₁.eval u * t₂.eval u

/-! ## Generalized selection predicates -/

/-- A generalized selection predicate: regular comparisons between terms
over regular columns, aggregate comparisons of one bare token column
against a regular term (the constant-folded normal form), and Boolean
structure. -/
inductive GenPred (T : Type) {n : ℕ} (κ : Fin n → ColKind) where
  /-- Regular atom: comparison of two terms over regular columns. -/
  | cmp : CompOp → TermG T κ → TermG T κ → GenPred T κ
  /-- Aggregate atom: the token in column `k` compared against a regular
  term (a per-group constant: query constant or group-key attribute). -/
  | aggCmp : (k : Fin n) → κ k = ColKind.agg → CompOp → TermG T κ →
      GenPred T κ
  | and : GenPred T κ → GenPred T κ → GenPred T κ
  | or : GenPred T κ → GenPred T κ → GenPred T κ
  | not : GenPred T κ → GenPred T κ

namespace GenPred

variable {n : ℕ} {κ : Fin n → ColKind}

/-- Does the predicate contain an aggregate atom? Selections without one
filter classically. -/
def hasAggAtom : GenPred T κ → Bool
  | cmp _ _ _ => false
  | aggCmp _ _ _ _ => true
  | and φ ψ | or φ ψ => φ.hasAggAtom || ψ.hasAggAtom
  | not φ => φ.hasAggAtom

/-- Classical (per-tuple) truth of a predicate, reading a compared token
through its deterministic collapse. Used by the evaluator only on
aggregate-atom-free predicates, where tokens are never consulted. -/
def holds (φ : GenPred T κ) (u : Tuple (GenValue T K) n) : Prop :=
  match φ with
  | cmp op t₁ t₂ => op.eval (t₁.eval u) (t₂.eval u)
  | aggCmp k _ op t => op.eval (AggValue.collapseSum (u k)) (t.eval u)
  | and φ ψ => φ.holds u ∧ ψ.holds u
  | or φ ψ => φ.holds u ∨ ψ.holds u
  | not φ => ¬ φ.holds u

/-- Structural decidability of `holds`. -/
def decHolds (φ : GenPred T κ) (u : Tuple (GenValue T K) n) :
    Decidable (φ.holds u) :=
  match φ with
  | cmp op _ _ => inferInstanceAs (Decidable (op.eval _ _))
  | aggCmp _ _ op _ => inferInstanceAs (Decidable (op.eval _ _))
  | and φ ψ => @instDecidableAnd _ _ (φ.decHolds u) (ψ.decHolds u)
  | or φ ψ => @instDecidableOr _ _ (φ.decHolds u) (ψ.decHolds u)
  | not φ => @instDecidableNot _ (φ.decHolds u)

instance (φ : GenPred T κ) : DecidablePred (φ.holds (K := K)) := φ.decHolds

/-- **Predicate provenance** of a generalized predicate on a row, with
`¬` pushed down to the atoms by De Morgan duality (the `neg` flag):
a regular atom contributes its characteristic value `χ`, an aggregate
atom the predicate provenance `predProv` of the comparison over its
token's group, `∧ ↦ ⊗` and `∨ ↦ ⊕` (swapped under `neg`), and negated
atoms complement their comparison operator, as in ProvSQL. -/
def predsem (φ : GenPred T κ) (neg : Bool)
    (u : Tuple (GenValue T K) n) : K :=
  match φ with
  | cmp op t₁ t₂ =>
      Having.chi (if neg then op.negate else op) (t₁.eval u) (t₂.eval u)
  | aggCmp k _ op t =>
      match u k with
      | Sum.inl _ => 0
      | Sum.inr a => a.predProv (if neg then op.negate else op) (t.eval u)
  | and φ ψ =>
      if neg then φ.predsem neg u + ψ.predsem neg u
      else φ.predsem neg u * ψ.predsem neg u
  | or φ ψ =>
      if neg then φ.predsem neg u * ψ.predsem neg u
      else φ.predsem neg u + ψ.predsem neg u
  | not φ => φ.predsem (!neg) u

/-- The token columns compared by the predicate's aggregate atoms. -/
def comparedCols : GenPred T κ → Finset (Fin n)
  | cmp _ _ _ => ∅
  | aggCmp k _ _ _ => {k}
  | and φ ψ | or φ ψ => φ.comparedCols ∪ ψ.comparedCols
  | not φ => φ.comparedCols

/-- Does the predicate provenance entail the compared groups' existence
(under the polarity `neg` of the enclosing negations)? An aggregate atom
does – its predicate provenance ranges over non-empty worlds only – while
a regular atom's `χ` does not. A conjunction (`∧` positively, `∨` under
negation) entails as soon as one factor does; a disjunction only if every
disjunct does. Mirrors ProvSQL's `having_entails_group_existence`: the
supersede of the group-existence factor is licensed only when this holds,
since e.g. `agg-atom ∨ regular-atom` can fire in worlds where the group
is empty. -/
def entailsExistence : GenPred T κ → Bool → Bool
  | cmp _ _ _, _ => false
  | aggCmp _ _ _ _, _ => true
  | and φ ψ, neg =>
      if neg then φ.entailsExistence neg && ψ.entailsExistence neg
      else φ.entailsExistence neg || ψ.entailsExistence neg
  | or φ ψ, neg =>
      if neg then φ.entailsExistence neg || ψ.entailsExistence neg
      else φ.entailsExistence neg && ψ.entailsExistence neg
  | not φ, neg => φ.entailsExistence (!neg)

end GenPred

/-! ## Projection columns -/

/-- One output column of a generalized projection: a regular term over
the regular input columns, or a verbatim copy of a token column (no
arithmetic over tokens: the normal form). -/
inductive ProjCol (T : Type) {n : ℕ} (κ : Fin n → ColKind) where
  | term : TermG T κ → ProjCol T κ
  | token : (k : Fin n) → κ k = ColKind.agg → ProjCol T κ
  | provTerm : TermG T κ → ProjCol T κ

/-- The kind of the output column. -/
def ProjCol.kind {κ : Fin n → ColKind} : ProjCol T κ → ColKind
  | term _ => ColKind.reg
  | token _ _ => ColKind.agg
  | provTerm _ => ColKind.prov

/-- Evaluation of a projection column on a lifted tuple. -/
def ProjCol.eval {κ : Fin n → ColKind} (p : ProjCol T κ)
    (u : Tuple (GenValue T K) n) : GenValue T K :=
  match p with
  | term t => Sum.inl (t.eval u)
  | token k _ => u k
  | provTerm t => Sum.inl (t.eval u)

/-! ## Kind-indexed queries -/

/-- The all-regular kind vector. -/
def ColKind.allReg (n : ℕ) : Fin n → ColKind := fun _ => ColKind.reg

/-- Kind-indexed general queries. The index discipline enforces the
scope conditions: `Gamma` aggregates an all-regular input, `Dedup` and
`Diff` require all-regular kinds, and the projection/selection grammars
never compute over tokens. -/
inductive AggQuery (T : Type) : (n : ℕ) → (Fin n → ColKind) → Type where
  /-- Base relation (all-regular). -/
  | Rel : (n : ℕ) → String → AggQuery T n (ColKind.allReg n)
  /-- Generalized projection. -/
  | Proj : {n m : ℕ} → {κ : Fin n → ColKind} →
      (ps : Tuple (ProjCol T κ) m) → AggQuery T n κ →
      AggQuery T m (fun j => (ps j).kind)
  /-- Generalized selection. -/
  | Sel : {n : ℕ} → {κ : Fin n → ColKind} →
      GenPred T κ → AggQuery T n κ → AggQuery T n κ
  /-- Cartesian product (join). -/
  | Prod : {n₁ n₂ : ℕ} → {κ₁ : Fin n₁ → ColKind} → {κ₂ : Fin n₂ → ColKind} →
      AggQuery T n₁ κ₁ → AggQuery T n₂ κ₂ →
      AggQuery T (n₁ + n₂) (Fin.append κ₁ κ₂)
  /-- Union (all). -/
  | Sum : {n : ℕ} → {κ : Fin n → ColKind} →
      AggQuery T n κ → AggQuery T n κ → AggQuery T n κ
  /-- Duplicate elimination – all-regular only. -/
  | Dedup : {n : ℕ} → AggQuery T n (ColKind.allReg n) →
      AggQuery T n (ColKind.allReg n)
  /-- Difference – all-regular only. -/
  | Diff : {n : ℕ} → AggQuery T n (ColKind.allReg n) →
      AggQuery T n (ColKind.allReg n) → AggQuery T n (ColKind.allReg n)
  /-- The decomposed grouping operator `γ^≼`: group the (all-regular)
  input by the key columns `is`; one output row per group, carrying the
  key followed by one aggregate token per `(term, aggregate)` pair. -/
  | Gamma : {m n₁ n₂ : ℕ} →
      (is : Tuple (Fin m) n₁) → (ts : Tuple (Term T m) n₂) →
      (fs : Tuple (SeqAggFunc T) n₂) → AggQuery T m (ColKind.allReg m) →
      AggQuery T (n₁ + n₂)
        (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg))
  /-- Provenance aggregation: group by the key columns `is` (none of
  which may be a token column) and `⊕`-sum the term `t` over each group
  into a single `prov` output column – the abstract counterpart of
  ProvSQL's `⊕`-gate creation in rewritten plans. -/
  | ProvSum : {m n₁ : ℕ} → {κ : Fin m → ColKind} →
      (is : Tuple (Fin m) n₁) → (his : ∀ k, κ (is k) ≠ ColKind.agg) →
      (t : TermG T κ) → AggQuery T m κ →
      AggQuery T (n₁ + 1)
        (Fin.append (fun k => κ (is k)) (fun _ : Fin 1 => ColKind.prov))
  /-- Retag value columns between the value-armed kinds (`reg` and
  `prov`): semantically the identity, it declares which value columns
  carry provenance – the typing act of casting a value column to
  ProvSQL's uuid type. Token columns cannot be retagged. -/
  | Retag : {n : ℕ} → {κ κ' : Fin n → ColKind} →
      (h : ∀ k, (κ k).base = (κ' k).base) → AggQuery T n κ →
      AggQuery T n κ'
  /-- Token-building grouping (ProvSQL's `provsql_agg`): group by the
  key columns `is`, output the keys, one aggregate token per
  `(term, aggregate)` pair whose occurrence annotations are the values
  of the explicit annotation term `a` (in rewritten plans: the
  provenance column of the subquery), and a trailing `prov` column
  carrying the group-existence guard. Its faithful semantics lives in
  the rewritten world's evaluator; the generic evaluators give it total
  modeling semantics, and the world-faithfulness exclusions
  (`noProvSum`) rule it out of source queries. -/
  | GammaTok : {m n₁ n₂ : ℕ} → {κ : Fin m → ColKind} →
      (is : Tuple (Fin m) n₁) → (his : ∀ k, κ (is k) ≠ ColKind.agg) →
      (ts : Tuple (Term T m) n₂) → (fs : Tuple (SeqAggFunc T) n₂) →
      (a : TermG T κ) → AggQuery T m κ →
      AggQuery T (n₁ + n₂ + 1)
        (Fin.append
          (Fin.append (fun k => κ (is k)) (fun _ => ColKind.agg))
          (fun _ : Fin 1 => ColKind.prov))

/-- Transport a query along an equality of kind vectors (kind vectors
arising from projections are rarely definitionally all-regular). -/
def AggQuery.castKind {n : ℕ} {κ κ' : Fin n → ColKind} (h : κ = κ') :
    AggQuery T n κ → AggQuery T n κ' := h ▸ id

/-! ## The general evaluator -/

/-- The regular-value reading of a lifted tuple (token columns collapse;
on the all-regular rows fed to `Dedup`, `Diff` and `Gamma` no token
occurs). -/
def GenRow.plainTuple {n : ℕ} (u : Tuple (GenValue T K) n) : Tuple T n :=
  fun k => AggValue.collapseSum (u k)

/-- Finalize a general row into an annotated tuple: collapse the tuple
to its regular reading and cash the pending group factors. -/
def GenRow.toAnnotated {n : ℕ} (r : GenRow T K n) : AnnotatedTuple T K n :=
  ⟨GenRow.plainTuple r.fst, r.snd.finalize⟩

/-- Embed an annotated tuple as a general row (all-regular, nothing
pending). -/
def GenRow.ofAnnotated {n : ℕ} (p : AnnotatedTuple T K n) : GenRow T K n :=
  ⟨fun k => Sum.inl (p.fst k), ⟨p.snd, 0⟩⟩

/-- The multiset of occurrence-annotation lists of the token columns of a
tuple (used by projection to detect dropped groups). -/
def tokenLists {n : ℕ} (u : Tuple (GenValue T K) n) : Multiset (List K) :=
  (Finset.univ.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => some (a.occs.map Prod.snd)))

def TermG.evalPlain {κ : Fin n → ColKind} (t : TermG T κ)
    (u : Tuple T n) : T :=
  match t with
  | .const a => a
  | .index k _ => u k
  | .provIndex k _ => u k
  | .cmpAgg _ _ _ _ => 0
  | .chiGate _ _ _ => 0
  | .add t₁ t₂ => t₁.evalPlain u + t₂.evalPlain u
  | .sub t₁ t₂ => t₁.evalPlain u - t₂.evalPlain u
  | .mul t₁ t₂ => t₁.evalPlain u * t₂.evalPlain u

/-! ## The gate-free fragment

The indicator gate `TermG.chiGate` is the one term constructor whose
faithful reading needs the rewritten world: it produces a provenance
value out of a comparison between regular values, which the generic
evaluators – having no annotation to return – can only approximate by
the junk constant. The `cmpAgg` gate escapes the same fate only because
its kind constraint keeps it off the columns the plain semantics sees.
The predicates below cut out the fragment where no indicator gate occurs,
on which the rewritten world's evaluator is the plain semantics
(`AggQuery.evaluateRew_plain`). -/

/-- No indicator gate in a term. -/
def TermG.chiFree {T' : Type} {κ : Fin n → ColKind} : TermG T' κ → Prop
  | .const _ | .index _ _ | .provIndex _ _ => True
  | .cmpAgg _ _ _ t => t.chiFree
  | .chiGate _ _ _ => False
  | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ => t₁.chiFree ∧ t₂.chiFree

/-- No indicator gate in a predicate. -/
def GenPred.chiFree {T' : Type} {κ : Fin n → ColKind} : GenPred T' κ → Prop
  | .cmp _ t₁ t₂ => t₁.chiFree ∧ t₂.chiFree
  | .aggCmp _ _ _ t => t.chiFree
  | .and φ ψ | .or φ ψ => φ.chiFree ∧ ψ.chiFree
  | .not φ => φ.chiFree

/-- No indicator gate in a projection column. -/
def ProjCol.chiFree {T' : Type} {κ : Fin n → ColKind} : ProjCol T' κ → Prop
  | .term t | .provTerm t => t.chiFree
  | .token _ _ => True

/-- **The general annotated evaluator.** All operators preserve the
factored-annotation discipline described in the module docstring. -/
def AggQuery.evaluate : {n : ℕ} → {κ : Fin n → ColKind} →
    AggQuery T n κ → AnnotatedDatabase T K → Multiset (GenRow T K n)
  | n, _, Rel _ s, d =>
    match d.find n s with
    | none => (∅ : Multiset (GenRow T K n))
    | some rn => (rn : Multiset (AnnotatedTuple T K n)).map GenRow.ofAnnotated
  | _, _, @Proj _ n m κ ps q, d =>
    (q.evaluate d).map (fun r =>
      let u' : Tuple (GenValue T K) m := fun j => (ps j).eval r.fst
      -- groups all of whose token columns are dropped are cashed
      let kept := r.snd.pending ∩ tokenLists u'
      ⟨u', ⟨r.snd.base *
          ((r.snd.pending - kept).map
            (fun l => SemiringWithMonus.delta l.sum)).prod,
        kept⟩⟩)
  | _, _, Sel φ q, d =>
    let r := q.evaluate d
    if φ.hasAggAtom then
      r.map (fun r =>
        -- the comparison supersedes a pending group factor only when the
        -- compared occurrences are exactly that group: every compared token
        -- carries the factor's annotation list (mirroring ProvSQL's
        -- structural supersede, which drops a δ only when its ⊕-operands
        -- are exactly the compared aggregates' occurrence tokens; a
        -- multi-group predicate keeps every group factor)
        let compared : Multiset (List K) :=
          φ.comparedCols.val.filterMap (fun k =>
            match r.fst k with
            | Sum.inl _ => none
            | Sum.inr a => some (a.occs.map Prod.snd))
        ⟨r.fst, ⟨r.snd.base * φ.predsem false r.fst,
          if φ.entailsExistence false then
            r.snd.pending.filter
              (fun l => ¬(compared ≠ 0 ∧ ∀ l' ∈ compared, l' = l))
          else r.snd.pending⟩⟩)
    else
      r.filter (fun r => φ.holds r.fst)
  | _, _, Prod q₁ q₂, d =>
    ((q₁.evaluate d).product (q₂.evaluate d)).map (fun (x, y) =>
      ⟨Fin.append x.fst y.fst,
        ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩)
  | _, _, Sum q₁ q₂, d => q₁.evaluate d + q₂.evaluate d
  | _, _, Dedup q, d =>
    let r : AnnotatedRelation T K _ := (q.evaluate d).map GenRow.toAnnotated
    (Multiset.ofList (groupByKey r).val).map GenRow.ofAnnotated
  | _, _, Diff q₁ q₂, d =>
    let r₁ : AnnotatedRelation T K _ := (q₁.evaluate d).map GenRow.toAnnotated
    let r₂ : AnnotatedRelation T K _ := (q₂.evaluate d).map GenRow.toAnnotated
    let grouped₂ := groupByKey r₂
    (r₁.map (fun (u, α) =>
      (⟨u, α - (((grouped₂.val.find? (·.1 = u)).map Prod.snd).getD 0)⟩ :
        AnnotatedTuple T K _))).map GenRow.ofAnnotated
  | _, _, @Gamma _ m n₁ n₂ is ts fs q, d =>
    let r : AnnotatedRelation T K m := (q.evaluate d).map GenRow.toAnnotated
    -- one row per group key (the closed form is `havingSite_evaluateAnnotated`)
    (Multiset.ofList (groupByKey (r.map (fun p => (fun k => p.fst (is k), p.snd)
        : AnnotatedTuple T K m → AnnotatedTuple T K n₁))).val).map (fun kv =>
      let g : Tuple T n₁ := kv.fst
      let U := Having.havingGroup is r g
      ⟨Fin.append (fun k => Sum.inl (g k))
        (fun j => Sum.inr (AggValue.ofGroup (fs j) (ts j) U)),
       ⟨1, {U.map Prod.snd}⟩⟩)
  | _, _, Retag _ q, d => q.evaluate d
  | _, _, @ProvSum _ _m n₁ _κ is _his t q, d =>
    let r : AnnotatedRelation T K _ := (q.evaluate d).map GenRow.toAnnotated
    let keys := (r.map (fun p => (fun k => p.fst (is k) : Tuple T n₁))).dedup
    keys.map (fun g =>
      (⟨Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun _ : Fin 1 => Sum.inl
            (((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
              (fun p => t.evalPlain p.fst)).fold addFn 0)),
        ⟨((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
            Prod.snd).sum, 0⟩⟩ : GenRow T K (n₁ + 1)))
  | _, _, @GammaTok _ m n₁ n₂ _κ is _his ts fs a q, d =>
    let r : AnnotatedRelation T K m := (q.evaluate d).map GenRow.toAnnotated
    (Multiset.ofList (groupByKey (r.map (fun p => (fun k => p.fst (is k), p.snd)
        : AnnotatedTuple T K m → AnnotatedTuple T K n₁))).val).map (fun kv =>
      let g : Tuple T n₁ := kv.fst
      let U := Having.havingGroup is r g
      ⟨Fin.append
        (Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun j => Sum.inr (AggValue.ofGroup (fs j) (ts j) U)))
        (fun _ : Fin 1 => Sum.inl
          (((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
            (fun p => a.evalPlain p.fst)).fold addFn 0)),
       ⟨1, {U.map Prod.snd}⟩⟩)

/-- The final annotated relation computed by a general query: evaluate,
then finalize every row. -/
def AggQuery.evaluateAnnotated {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ) (d : AnnotatedDatabase T K) :
    AnnotatedRelation T K n :=
  (q.evaluate d).map GenRow.toAnnotated

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- Embedding then finalizing is the identity on annotated tuples. -/
@[simp] theorem GenRow.toAnnotated_ofAnnotated {n : ℕ}
    (p : AnnotatedTuple T K n) :
    GenRow.toAnnotated (GenRow.ofAnnotated p) = p := by
  unfold GenRow.toAnnotated GenRow.ofAnnotated GenRow.plainTuple
  simp [AggValue.collapseSum]

/-! ## The plain evaluator

The classical (per-instance) semantics of a general query: aggregate
columns hold the computed aggregate values, and every selection filters
classically – including aggregate comparisons, evaluated on the computed
values. This is the semantics the data-part adequacy connects to the
annotated evaluator through `AggValue.collapse` (the annotated side keeps
classically-failing rows with annotation `𝟘`, exactly as ProvSQL emits
them, so adequacy is stated on the query stripped of its aggregate
selections and differences, `stripAgg`). -/

namespace GenPred

variable {n : ℕ} {κ : Fin n → ColKind}

/-- Classical truth of a predicate on a regular tuple: aggregate atoms
compare the computed aggregate value of their column. -/
def holdsPlain (φ : GenPred T κ) (u : Tuple T n) : Prop :=
  match φ with
  | cmp op t₁ t₂ => op.eval (t₁.evalPlain u) (t₂.evalPlain u)
  | aggCmp k _ op t => op.eval (u k) (t.evalPlain u)
  | and φ ψ => φ.holdsPlain u ∧ ψ.holdsPlain u
  | or φ ψ => φ.holdsPlain u ∨ ψ.holdsPlain u
  | not φ => ¬ φ.holdsPlain u

/-- Structural decidability of `holdsPlain`. -/
def decHoldsPlain (φ : GenPred T κ) (u : Tuple T n) :
    Decidable (φ.holdsPlain u) :=
  match φ with
  | cmp op _ _ => inferInstanceAs (Decidable (op.eval _ _))
  | aggCmp _ _ op _ => inferInstanceAs (Decidable (op.eval _ _))
  | and φ ψ => @instDecidableAnd _ _ (φ.decHoldsPlain u) (ψ.decHoldsPlain u)
  | or φ ψ => @instDecidableOr _ _ (φ.decHoldsPlain u) (ψ.decHoldsPlain u)
  | not φ => @instDecidableNot _ (φ.decHoldsPlain u)

instance (φ : GenPred T κ) : DecidablePred φ.holdsPlain := φ.decHoldsPlain

end GenPred

/-- Plain evaluation of a projection column. -/
def ProjCol.evalPlain {κ : Fin n → ColKind} (p : ProjCol T κ)
    (u : Tuple T n) : T :=
  match p with
  | .term t => t.evalPlain u
  | .token k _ => u k
  | .provTerm t => t.evalPlain u

/-- **The plain evaluator**: standard multiset semantics, with `Gamma`
computing the aggregate of each group's full occurrence sequence (in the
canonical `≼` order of `Relation.groupSeq`) and every selection filtering
classically. `Diff` is the all-or-nothing difference of
`Query.evaluate`. -/
def AggQuery.evaluatePlain : {n : ℕ} → {κ : Fin n → ColKind} →
    AggQuery T n κ → Database T → Relation T n
  | n, _, Rel _ s, d =>
    match d.find n s with
    | none => (∅ : Multiset (Tuple T n))
    | some rn => rn
  | _, _, @Proj _ n _ κ ps q, d =>
    (q.evaluatePlain d).map (fun u => (fun j => (ps j).evalPlain u))
  | _, _, Sel φ q, d =>
    @Multiset.filter _ φ.holdsPlain φ.decHoldsPlain (q.evaluatePlain d)
  | _, _, Prod q₁ q₂, d => q₁.evaluatePlain d * q₂.evaluatePlain d
  | _, _, Sum q₁ q₂, d => q₁.evaluatePlain d + q₂.evaluatePlain d
  | _, _, Dedup q, d => (q.evaluatePlain d).dedup
  | _, _, Diff q₁ q₂, d =>
    let r₂ : Multiset (Tuple T _) := q₂.evaluatePlain d
    (q₁.evaluatePlain d).filter (fun t => t ∉ r₂)
  | _, _, @Gamma _ _m n₁ n₂ is ts fs q, d =>
    let r := q.evaluatePlain d
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append g
      (fun j => (fs j) ((Relation.groupSeq is r g).map (ts j).eval)))
  | _, _, Retag _ q, d => q.evaluatePlain d
  | _, _, @ProvSum _ _m n₁ _κ is _his t q, d =>
    let r := q.evaluatePlain d
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append g (fun _ : Fin 1 =>
      ((r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map
        (fun u => t.evalPlain u)).fold addFn 0))
  | _, _, @GammaTok _ _m n₁ n₂ _κ is _his ts fs a q, d =>
    let r := q.evaluatePlain d
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append
      (Fin.append g
        (fun j => (fs j) ((Relation.groupSeq is r g).map (ts j).eval)))
      (fun _ : Fin 1 =>
        ((r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map
          (fun u => a.evalPlain u)).fold addFn 0))

/-- Strip a general query of the constructs whose annotated data part
keeps rows the classical semantics removes: differences (annotated `Diff`
never removes tuple slots) and selections containing an aggregate atom
(the annotated evaluator keeps classically-failing rows annotated `𝟘`,
as ProvSQL emits them). The data-part adequacy of `evaluateAnnotated`
is stated against the plain evaluation of the stripped query, mirroring
`Query.stripDiff` in `Provenance.QueryAdequacy`. -/
def AggQuery.stripAgg : {n : ℕ} → {κ : Fin n → ColKind} →
    AggQuery T n κ → AggQuery T n κ
  | _, _, Rel n s => Rel n s
  | _, _, Proj ps q => Proj ps q.stripAgg
  | _, _, Sel φ q =>
    if φ.hasAggAtom then q.stripAgg else Sel φ q.stripAgg
  | _, _, Prod q₁ q₂ => Prod q₁.stripAgg q₂.stripAgg
  | _, _, Sum q₁ q₂ => Sum q₁.stripAgg q₂.stripAgg
  | _, _, Dedup q => Dedup q.stripAgg
  | _, _, Diff q₁ _ => q₁.stripAgg
  | _, _, Gamma is ts fs q => Gamma is ts fs q.stripAgg
  | _, _, ProvSum is his t q => ProvSum is his t q.stripAgg
  | _, _, Retag h q => Retag h q.stripAgg
  | _, _, GammaTok is his ts fs a q => GammaTok is his ts fs a q.stripAgg

/-- No plan-level provenance aggregation. The possible-world
metatheorems (random-world commutation, PQE) are about source queries;
`ProvSum` is a rewriting-target operator whose deterministic group sum
is not world-faithful – exactly as the classical `Agg` was excluded from
the annotated evaluators. -/
def AggQuery.noProvSum : {n : ℕ} → {κ : Fin n → ColKind} →
    AggQuery T n κ → Prop
  | _, _, .Rel _ _ => True
  | _, _, .Proj _ q => q.noProvSum
  | _, _, .Sel _ q => q.noProvSum
  | _, _, .Prod q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, .Sum q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, .Dedup q => q.noProvSum
  | _, _, .Diff q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, .Gamma _ _ _ q => q.noProvSum
  | _, _, .ProvSum _ _ _ _ => False
  | _, _, .Retag _ q => q.noProvSum
  | _, _, .GammaTok _ _ _ _ _ _ => False

/-! ## Kind conformance

Rows produced by the general evaluator conform to the query's kind
vector: regular columns hold regular values, token columns hold tokens.
This is an invariant *lemma*, not a hypothesis: the kind-indexed syntax
makes it hold by construction, and downstream theorems (the random-world
commutation in particular) invoke it instead of assuming wellformedness. -/

/-- The kind of a lifted value. -/
def GenValue.kindOf : GenValue T K → ColKind
  | Sum.inl _ => ColKind.reg
  | Sum.inr _ => ColKind.agg


/-- **Kind conformance of the general evaluator.** -/
theorem AggQuery.evaluate_conform :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ)
      (d : AnnotatedDatabase T K) (r : GenRow T K n),
      r ∈ q.evaluate d → ∀ k, GenValue.kindOf (r.fst k) = (κ k).base := by
  intro n κ q
  induction q with
  | Rel n s =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    cases hf : d.find n s with
    | none => rw [hf] at hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      rw [hf] at hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      rfl
  | Proj ps q ih =>
    intro d r hr j
    simp only [AggQuery.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
    cases hp : ps j with
    | term t => simp [ProjCol.eval, hp, ProjCol.kind, GenValue.kindOf,
        ColKind.base]
    | provTerm t => simp [ProjCol.eval, hp, ProjCol.kind, GenValue.kindOf,
        ColKind.base]
    | token k hk =>
      have := ih d r₀ hr₀ k
      rw [hk] at this
      simp only [ProjCol.eval, hp, ProjCol.kind]
      cases hu : r₀.fst k with
      | inl v =>
        rw [hu] at this
        exact absurd this (by simp [GenValue.kindOf, ColKind.base])
      | inr a => rfl
  | Sel φ q ih =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    by_cases hφ : φ.hasAggAtom
    · rw [if_pos hφ] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      exact ih d r₀ hr₀ k
    · rw [if_neg hφ] at hr
      exact ih d r (Multiset.mem_of_mem_filter hr) k
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Multiset.mem_map.mp hr
    have hx := Multiset.mem_product.mp hxy
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact (congrArg GenValue.kindOf (Fin.append_left x.fst y.fst i)).trans
        ((ih₁ d x hx.left i).trans
          (congrArg ColKind.base (Fin.append_left _ _ i).symm))
    · exact (congrArg GenValue.kindOf (Fin.append_right x.fst y.fst j)).trans
        ((ih₂ d y hx.right j).trans
          (congrArg ColKind.base (Fin.append_right _ _ j).symm))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    rcases Multiset.mem_add.mp hr with h | h
    · exact ih₁ d r h k
    · exact ih₂ d r h k
  | Dedup q ih =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Gamma is ts fs q ih =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact (congrArg GenValue.kindOf
        (Fin.append_left (fun k => (Sum.inl (kv.fst k) : GenValue T K))
          (fun j' => (Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              (Multiset.map GenRow.toAnnotated (q.evaluate d)) kv.fst))
            : GenValue T K)) i)).trans
        (congrArg ColKind.base
          (Fin.append_left (fun _ => ColKind.reg)
            (fun _ => ColKind.agg) i).symm)
    · exact (congrArg GenValue.kindOf
        (Fin.append_right (fun k => (Sum.inl (kv.fst k) : GenValue T K))
          (fun j' => (Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              (Multiset.map GenRow.toAnnotated (q.evaluate d)) kv.fst))
            : GenValue T K)) j)).trans
        (congrArg ColKind.base
          (Fin.append_right (fun _ => ColKind.reg)
            (fun _ => ColKind.agg) j).symm)
  | ProvSum is his t q ih =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · dsimp only
      rw [Fin.append_left, Fin.append_left]
      exact (ColKind.base_eq_reg_of_ne_agg (his i)).symm
    · dsimp only
      rw [Fin.append_right, Fin.append_right]
      rfl
  | Retag h q ih =>
    intro d r hr k
    exact (ih d r hr k).trans (congrArg id (h k))
  | GammaTok is his ts fs a q ih =>
    intro d r hr k
    simp only [AggQuery.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
      · dsimp only
        rw [Fin.append_left, Fin.append_left, Fin.append_left,
          Fin.append_left]
        exact (ColKind.base_eq_reg_of_ne_agg (his i')).symm
      · dsimp only
        rw [Fin.append_left, Fin.append_left, Fin.append_right,
          Fin.append_right]
        rfl
    · dsimp only
      rw [Fin.append_right, Fin.append_right]
      rfl
