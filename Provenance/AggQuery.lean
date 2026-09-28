/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggExpr
import Provenance.Frame

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
  (`ProjColIn.term`) or verbatim copies of token columns (`ProjColIn.token`) –
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
  (`GenPredIn.entailsExistence` – e.g., an aggregate atom `∨`-mixed with a
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
inductive TermGIn (T : Type) (c : ℕ) {n : ℕ} (κ : Fin n → ColKind) where
  | const : T → TermGIn T c κ
  /-- An *outer* column: a column of the query this one is applied to,
  read as a value. It is what makes a query open, and there are none of
  them in a closed query, `c` being `0` there. -/
  | outer : Fin c → TermGIn T c κ
  | index : (k : Fin n) → κ k = ColKind.reg → TermGIn T c κ
  | provIndex : (k : Fin n) → κ k = ColKind.prov → TermGIn T c κ
  /-- The aggregate-comparison gate (ProvSQL's `provsql_having`): the
  predicate provenance of comparing the token in column `k` against the
  term. Its faithful semantics lives in the rewritten world's term
  evaluator; the generic evaluators give it a total junk value, and on
  token-free kinds the constructor is unrepresentable. -/
  | cmpAgg : (k : Fin n) → κ k = ColKind.agg → CompOp → TermGIn T c κ →
      TermGIn T c κ
  /-- The regular-comparison indicator gate: the characteristic value
  `χ` of a comparison between two regular terms – `𝟙` if it holds on the
  row, `𝟘` otherwise. It is the primitive a `HAVING` predicate
  needs for its *regular* atoms, and like `cmpAgg` its faithful semantics
  lives in the rewritten world's term evaluator – the generic evaluators
  give it a total junk value. Unlike `cmpAgg` it carries no kind
  constraint, so it is representable over all-regular columns: the
  fragment on which the rewritten world's evaluator collapses to the
  plain semantics is cut out by `TermGIn.chiFree` instead. -/
  | chiGate : CompOp → TermGIn T c κ → TermGIn T c κ → TermGIn T c κ
  | add : TermGIn T c κ → TermGIn T c κ → TermGIn T c κ
  | sub : TermGIn T c κ → TermGIn T c κ → TermGIn T c κ
  | mul : TermGIn T c κ → TermGIn T c κ → TermGIn T c κ
  /-- SQL's searched `CASE`, as `TermIn.caseWhen`. -/
  | caseWhen : CompOp → TermGIn T c κ → TermGIn T c κ → TermGIn T c κ →
      TermGIn T c κ → TermGIn T c κ
  /-- SQL's `COALESCE`, as `TermIn.coalesce`. -/
  | coalesce : TermGIn T c κ → TermGIn T c κ → TermGIn T c κ

/-- A term of a closed query: no outer column to read. -/
abbrev TermG (T : Type) {n : ℕ} (κ : Fin n → ColKind) := TermGIn T 0 κ

/-- Evaluation of a term on a lifted tuple. On the regular columns the
kind index guarantees a regular value; the token arm of `collapseSum` is
never reached on kind-conformant tuples and merely keeps the function
total. -/
def TermGIn.eval {c : ℕ} {κ : Fin n → ColKind} (t : TermGIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin c → T := fun _ => 0) : T :=
  match t with
  | .const a => a
  | .outer k => γ k
  | .index k _ => AggValue.collapseSum (u k)
  | .provIndex k _ => AggValue.collapseSum (u k)
  | .cmpAgg _ _ _ _ => 0
  | .chiGate _ _ _ => 0
  | .add t₁ t₂ => t₁.eval u γ + t₂.eval u γ
  | .sub t₁ t₂ => t₁.eval u γ - t₂.eval u γ
  | .mul t₁ t₂ => t₁.eval u γ * t₂.eval u γ
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    if op.eval3 (t₁.eval u γ) (t₂.eval u γ) = Kleene.true then t₃.eval u γ
    else t₄.eval u γ
  | .coalesce t₁ t₂ =>
    if ValueType.isNull (t₁.eval u γ) then t₂.eval u γ else t₁.eval u γ

/-! ## Generalized selection predicates -/

/-- A generalized selection predicate: regular comparisons between terms
over regular columns, aggregate comparisons of one bare token column
against a regular term (the constant-folded normal form), and Boolean
structure. -/
inductive GenPredIn (T : Type) (c : ℕ) {n : ℕ} (κ : Fin n → ColKind) where
  /-- Regular atom: comparison of two terms over regular columns. -/
  | cmp : CompOp → TermGIn T c κ → TermGIn T c κ → GenPredIn T c κ
  /-- Aggregate atom: the token in column `k` compared against a regular
  term (a per-group constant: query constant or group-key attribute). -/
  | aggCmp : (k : Fin n) → κ k = ColKind.agg → CompOp → TermGIn T c κ →
      GenPredIn T c κ
  /-- **A range atom**: the token in column `k` compared against two
  regular terms at once, read as *one* atom and not as the conjunction
  of two. The difference is not in what it says on a row – the two agree
  classically – but in what it annotates: one `⊕`-sum over the worlds
  where both comparisons hold, which is what a truncation's
  `m < #(k+1) ≤ m+c` asks for. A conjunction of two atoms instead
  multiplies two sums, and that is the same value only when the
  m-semiring is exclusive with an idempotent `⊗`
  (`AggValue.predProvOf_mul_predProvOf_with`). -/
  | aggRange : (k : Fin n) → κ k = ColKind.agg → CompOp → TermGIn T c κ →
      CompOp → TermGIn T c κ → GenPredIn T c κ
  | and : GenPredIn T c κ → GenPredIn T c κ → GenPredIn T c κ
  | or : GenPredIn T c κ → GenPredIn T c κ → GenPredIn T c κ
  | not : GenPredIn T c κ → GenPredIn T c κ

/-- A predicate of a closed query. -/
abbrev GenPred (T : Type) {n : ℕ} (κ : Fin n → ColKind) := GenPredIn T 0 κ

namespace GenPredIn

variable {c n : ℕ} {κ : Fin n → ColKind}

/-- Does the predicate contain an aggregate atom? Selections without one
filter classically. -/
def hasAggAtom : GenPredIn T c κ → Bool
  | cmp _ _ _ => false
  | aggCmp _ _ _ _ => true
  | aggRange _ _ _ _ _ _ => true
  | and φ ψ | or φ ψ => φ.hasAggAtom || ψ.hasAggAtom
  | not φ => φ.hasAggAtom

/-- Classical (per-tuple) truth of a predicate, reading a compared token
through its deterministic collapse. Used by the evaluator only on
aggregate-atom-free predicates, where tokens are never consulted. -/
def eval3 (φ : GenPredIn T c κ) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T := fun _ => 0) : Kleene :=
  match φ with
  | cmp op t₁ t₂ => op.eval3 (t₁.eval u γ) (t₂.eval u γ)
  | aggCmp k _ op t => op.eval3 (AggValue.collapseSum (u k)) (t.eval u γ)
  | aggRange k _ op₁ t₁ op₂ t₂ =>
    (op₁.eval3 (AggValue.collapseSum (u k)) (t₁.eval u γ)).and
      (op₂.eval3 (AggValue.collapseSum (u k)) (t₂.eval u γ))
  | and φ ψ => (φ.eval3 u γ).and (ψ.eval3 u γ)
  | or φ ψ => (φ.eval3 u γ).or (ψ.eval3 u γ)
  | not φ => (φ.eval3 u γ).not

/-- The rows a selection keeps: those on which the predicate is *true*. A
row on which it is unknown is kept by neither the predicate nor its
negation. -/
def holds (φ : GenPredIn T c κ) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T := fun _ => 0) : Prop :=
  φ.eval3 u γ = Kleene.true

/-- Structural decidability of `holds`. -/
def decHolds (φ : GenPredIn T c κ) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T := fun _ => 0) : Decidable (φ.holds u γ) :=
  inferInstanceAs (Decidable (_ = _))

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem holds_and (φ ψ : GenPred T κ) (u : Tuple (GenValue T K) n) :
    (GenPredIn.and φ ψ).holds u ↔ φ.holds u ∧ ψ.holds u :=
  Kleene.and_eq_true_iff _ _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem holds_or (φ ψ : GenPred T κ) (u : Tuple (GenValue T K) n) :
    (GenPredIn.or φ ψ).holds u ↔ φ.holds u ∨ ψ.holds u :=
  Kleene.or_eq_true_iff _ _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Where nothing is null no predicate is ever unknown**, so the reading
is the two-valued one and every statement proved before the null was
introduced keeps saying what it said. -/
theorem eval3_ne_unknown [NoNulls T] (u : Tuple (GenValue T K) n) :
    ∀ φ : GenPred T κ, φ.eval3 u ≠ Kleene.unknown
  | cmp op t₁ t₂ => by
    rw [GenPredIn.eval3, CompOp.eval3_eq_ofBool]
    cases decide (op.eval (t₁.eval u) (t₂.eval u)) <;> simp [Kleene.ofBool]
  | aggCmp k h op t => by
    rw [GenPredIn.eval3, CompOp.eval3_eq_ofBool]
    cases decide (op.eval (AggValue.collapseSum (u k)) (t.eval u)) <;>
      simp [Kleene.ofBool]
  | aggRange k h op₁ t₁ op₂ t₂ => by
    rw [GenPredIn.eval3, CompOp.eval3_eq_ofBool, CompOp.eval3_eq_ofBool]
    cases decide (op₁.eval (AggValue.collapseSum (u k)) (t₁.eval u)) <;>
      cases decide (op₂.eval (AggValue.collapseSum (u k)) (t₂.eval u)) <;>
      simp [Kleene.ofBool, Kleene.and]
  | and φ ψ => by
    have h₁ := eval3_ne_unknown u φ
    have h₂ := eval3_ne_unknown u ψ
    cases e₁ : φ.eval3 u <;> cases e₂ : ψ.eval3 u <;>
      simp_all [GenPredIn.eval3, Kleene.and]
  | or φ ψ => by
    have h₁ := eval3_ne_unknown u φ
    have h₂ := eval3_ne_unknown u ψ
    cases e₁ : φ.eval3 u <;> cases e₂ : ψ.eval3 u <;>
      simp_all [GenPredIn.eval3, Kleene.or]
  | not φ => by
    have h := eval3_ne_unknown u φ
    cases e : φ.eval3 u <;> simp_all [GenPredIn.eval3, Kleene.not]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Negation is classical where nothing is null. -/
theorem holds_not_iff [NoNulls T] (φ : GenPred T κ)
    (u : Tuple (GenValue T K) n) :
    (GenPredIn.not φ).holds u ↔ ¬ φ.holds u := by
  have h := eval3_ne_unknown u φ
  show (φ.eval3 u).not = Kleene.true ↔ ¬ (φ.eval3 u = Kleene.true)
  cases e : φ.eval3 u <;> simp_all [Kleene.not]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **A row is kept by `NOT φ` when `φ` is false**, which is not the same as
`φ` failing to be true: a row on which `φ` is unknown is kept by neither. -/
@[simp] theorem holds_not (φ : GenPred T κ) (u : Tuple (GenValue T K) n) :
    (GenPredIn.not φ).holds u ↔ φ.eval3 u = Kleene.false :=
  Kleene.not_eq_true_iff _

instance (φ : GenPredIn T c κ) (γ : Fin c → T) (u : Tuple (GenValue T K) n) :
    Decidable (φ.holds u γ) := φ.decHolds u γ

/-- **Predicate provenance** of a generalized predicate on a row, with
`¬` pushed down to the atoms by De Morgan duality (the `neg` flag):
a regular atom contributes its characteristic value `χ`, an aggregate
atom the predicate provenance `predProv` of the comparison over its
token's group, `∧ ↦ ⊗` and `∨ ↦ ⊕` (swapped under `neg`), and negated
atoms complement their comparison operator, as in ProvSQL.

**These rules are a short cut, and what they are a short cut for is the
joint evaluation of the predicate's Boolean function in every world**:
the `⊕`, over the worlds of the union of the families the predicate
reads, of the world's annotation times the function's truth there,
which is `AggExpr.predProv`. That is the semantics, for ProvSQL as for
the library; computing it structurally is what an m-semiring with the
right properties permits, and the properties are the content of the
theorems. On one atom the two always agree
(`AggExpr.predProv_ofValue`). On a conjunction the product is a
decomposition of the joint reading under complementedness, exclusivity
and an idempotent `⊗` (`Having.sum_mul_sum_of_overlap`, and
`complemented` alone where the families are disjoint). On a disjunction
there is no such theorem: the `⊕` fires in worlds where one group is
empty, which are no worlds of the predicate, and `𝔹` and `ℕ` both
witness the difference (`bool_or_ne_joint`, `nat_or_ne_joint`), so
there the sum has to be computed rather than short cut. A range is the
same point for `∧` on one family, which is why `aggRange` is an atom of
its own rather than two atoms conjoined. -/
def predsem (φ : GenPredIn T c κ) (neg : Bool)
    (u : Tuple (GenValue T K) n) (γ : Fin c → T := fun _ => 0) : K :=
  match φ with
  | cmp op t₁ t₂ =>
      Having.chi (if neg then op.negate else op) (t₁.eval u γ) (t₂.eval u γ)
  | aggCmp k _ op t =>
      match u k with
      | Sum.inl _ => 0
      | Sum.inr a => a.predProvOf (if neg then op.negate else op) (t.eval u γ)
  | aggRange k _ op₁ t₁ op₂ t₂ =>
      match u k with
      | Sum.inl _ => 0
      | Sum.inr a => a.predProvOfWith (fun v =>
          if neg then ((op₁.eval3 v (t₁.eval u γ)).and
              (op₂.eval3 v (t₂.eval u γ))).not
          else (op₁.eval3 v (t₁.eval u γ)).and (op₂.eval3 v (t₂.eval u γ)))
  | and φ ψ =>
      if neg then φ.predsem neg u γ + ψ.predsem neg u γ
      else φ.predsem neg u γ * ψ.predsem neg u γ
  | or φ ψ =>
      if neg then φ.predsem neg u γ * ψ.predsem neg u γ
      else φ.predsem neg u γ + ψ.predsem neg u γ
  | not φ => φ.predsem (!neg) u γ

/-- The token columns compared by the predicate's aggregate atoms. -/
def comparedCols : GenPredIn T c κ → Finset (Fin n)
  | cmp _ _ _ => ∅
  | aggCmp k _ _ _ => {k}
  | aggRange k _ _ _ _ _ => {k}
  | and φ ψ | or φ ψ => φ.comparedCols ∪ ψ.comparedCols
  | not φ => φ.comparedCols

/-- Does the predicate provenance entail the compared groups' existence
(under the polarity `neg` of the enclosing negations)? An aggregate atom
does – its predicate provenance ranges over non-empty worlds only – while
a regular atom's `χ` does not. A conjunction (`∧` positively, `∨` under
negation) entails as soon as one factor does; a disjunction only if every
disjunct does. Mirrors ProvSQL's `having_entails_group_existence`: the
supersede of the group-existence factor is licensed only when this holds,
since e.g., `agg-atom ∨ regular-atom` can fire in worlds where the group
is empty. -/
def entailsExistence : GenPredIn T c κ → Bool → Bool
  | cmp _ _ _, _ => false
  | aggCmp _ _ _ _, _ => true
  | aggRange _ _ _ _ _ _, _ => true
  | and φ ψ, neg =>
      if neg then φ.entailsExistence neg && ψ.entailsExistence neg
      else φ.entailsExistence neg || ψ.entailsExistence neg
  | or φ ψ, neg =>
      if neg then φ.entailsExistence neg || ψ.entailsExistence neg
      else φ.entailsExistence neg && ψ.entailsExistence neg
  | not φ, neg => φ.entailsExistence (!neg)

end GenPredIn

/-! ## Projection columns -/

/-- One output column of a generalized projection: a regular term over
the regular input columns, or a verbatim copy of a token column (no
arithmetic over tokens: the normal form). -/
inductive ProjColIn (T : Type) (c : ℕ) {n : ℕ} (κ : Fin n → ColKind) where
  | term : TermGIn T c κ → ProjColIn T c κ
  | token : (k : Fin n) → κ k = ColKind.agg → ProjColIn T c κ
  /-- **A term over one aggregate column**: the column the term names,
  read through `gf`. It is again an aggregate column – the unary
  aggregate expression `gf(a)` of `Provenance.AggExpr`, which
  `AggValue.postcomp` represents – and it is what SQL's `count(*) + 1`
  and the ranks produce. Only the value of `gf` in each world is used,
  so any deterministic function of SQL can be one. -/
  | aggTerm : (k : Fin n) → κ k = ColKind.agg → (T → T) → ProjColIn T c κ
  | provTerm : TermGIn T c κ → ProjColIn T c κ

/-- A projection column of a closed query. -/
abbrev ProjCol (T : Type) {n : ℕ} (κ : Fin n → ColKind) := ProjColIn T 0 κ

/-- The kind of the output column. -/
def ProjColIn.kind {c : ℕ} {κ : Fin n → ColKind} : ProjColIn T c κ → ColKind
  | term _ => ColKind.reg
  | token _ _ => ColKind.agg
  | aggTerm _ _ _ => ColKind.agg
  | provTerm _ => ColKind.prov

/-- Evaluation of a projection column on a lifted tuple. -/
def ProjColIn.eval {c : ℕ} {κ : Fin n → ColKind} (p : ProjColIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin c → T := fun _ => 0) :
    GenValue T K :=
  match p with
  | term t => Sum.inl (t.eval u γ)
  | token k _ => u k
  | aggTerm k _ gf => Sum.map gf (AggValue.postcomp gf) (u k)
  | provTerm t => Sum.inl (t.eval u γ)

/-! ## Kind-indexed queries -/

/-- The all-regular kind vector. -/
def ColKind.allReg (n : ℕ) : Fin n → ColKind := fun _ => ColKind.reg

/-- Kind-indexed general queries. The index discipline enforces the
scope conditions: `Gamma` aggregates an all-regular input, `Dedup` and
`Diff` require all-regular kinds, and the projection/selection grammars
never compute over tokens. -/
inductive AggQueryIn (T : Type) : (c n : ℕ) → (Fin n → ColKind) → Type where
  /-- Base relation (all-regular). -/
  | Rel : {c : ℕ} → (n : ℕ) → String → AggQueryIn T c n (ColKind.allReg n)
  /-- Generalized projection. -/
  | Proj : {c n m : ℕ} → {κ : Fin n → ColKind} →
      (ps : Tuple (ProjColIn T c κ) m) → AggQueryIn T c n κ →
      AggQueryIn T c m (fun j => (ps j).kind)
  /-- Generalized selection. -/
  | Sel : {c n : ℕ} → {κ : Fin n → ColKind} →
      GenPredIn T c κ → AggQueryIn T c n κ → AggQueryIn T c n κ
  /-- Cartesian product (join). -/
  | Prod : {c n₁ n₂ : ℕ} → {κ₁ : Fin n₁ → ColKind} → {κ₂ : Fin n₂ → ColKind} →
      AggQueryIn T c n₁ κ₁ → AggQueryIn T c n₂ κ₂ →
      AggQueryIn T c (n₁ + n₂) (Fin.append κ₁ κ₂)
  /-- **Apply** – SQL's `LATERAL`, the operator of Galindo-Legaria and
  Joshi: a product whose right side is read once per row of the left and
  may read that row's columns. The right side's context is the left
  side's columns followed by the ambient outer ones, so in a closed
  apply the right side reads exactly the left arity. Its output pairs
  each row `u` of the left with each row of the right read at `u`, and
  multiplies their annotations.

  It is not derivable from the cross product once annotations are there:
  the product reads its right side once, the apply once per row of the
  left, and it is the apply that a correlated subquery needs. -/
  | Apply : {c n₁ n₂ : ℕ} → {κ₂ : Fin n₂ → ColKind} →
      AggQueryIn T c n₁ (ColKind.allReg n₁) →
      AggQueryIn T (n₁ + c) n₂ κ₂ →
      AggQueryIn T c (n₁ + n₂) (Fin.append (ColKind.allReg n₁) κ₂)
  /-- Union (all). -/
  | Sum : {c n : ℕ} → {κ : Fin n → ColKind} →
      AggQueryIn T c n κ → AggQueryIn T c n κ → AggQueryIn T c n κ
  /-- Duplicate elimination – all-regular only. -/
  | Dedup : {c n : ℕ} → AggQueryIn T c n (ColKind.allReg n) →
      AggQueryIn T c n (ColKind.allReg n)
  /-- Difference – all-regular only. -/
  | Diff : {c n : ℕ} → AggQueryIn T c n (ColKind.allReg n) →
      AggQueryIn T c n (ColKind.allReg n) → AggQueryIn T c n (ColKind.allReg n)
  /-- **Recursion with duplicate-preserving rounds**: SQL's
  `WITH RECURSIVE … UNION ALL`. The relation name `s` of arity `n` is
  bound to the previous round inside `q₁`, so the rounds are
  `M₀ = ⟦q₀⟧` and `M_{i+1} = ⟦q₁⟧_{d[s ↦ Mᵢ]}`, and the query is their
  multiset sum.

  The operator of the semantics is *partial*: it is defined where some
  round is empty, which is where SQL's own iteration ends. A total
  evaluator cannot decide that, so the number of rounds is in the
  syntax – `Mu b` sums the rounds up to `b`. Where some round `i ≤ b` is
  empty this is the semantics' `⨄_{i≥0} Mᵢ`, and then it does not depend
  on `b` (`AggQueryIn.evaluate_Mu_eq_of_le`); where no round is empty,
  `Mu b` says what SQL says after `b` rounds and the semantics' operator
  says nothing. -/
  | Mu : {c n : ℕ} → (b : ℕ) → (s : String) →
      AggQueryIn T c n (ColKind.allReg n) →
      AggQueryIn T c n (ColKind.allReg n) →
      AggQueryIn T c n (ColKind.allReg n)
  /-- **Recursion up to duplicates**: SQL's `WITH RECURSIVE … UNION`.
  Read as the least fixpoint the semantics says it is: `X₀` empty and
  `X_{j+1} = ⟦ε(q₀ ⊎ q₁)⟧_{d[s ↦ X_j]}`, annotations included, and the
  query is `X_b`. Where the iteration stabilizes at some `j ≤ b` this is
  the semantics' value and does not depend on `b`
  (`AggQueryIn.evaluate_MuSet_eq_of_le`); the semantics says nothing
  where it does not stabilize. Unlike `Mu` it stabilizes whenever no
  tuple has a derivation through itself, and in an absorptive semiring
  with such derivations too. -/
  | MuSet : {c n : ℕ} → (b : ℕ) → (s : String) →
      AggQueryIn T c n (ColKind.allReg n) →
      AggQueryIn T c n (ColKind.allReg n) →
      AggQueryIn T c n (ColKind.allReg n)
  /-- The decomposed grouping operator `γ^≼`: group the (all-regular)
  input by the key columns `is`; one output row per group, carrying the
  key followed by one aggregate token per `(term, aggregate)` pair. -/
  | Gamma : {c m n₁ n₂ : ℕ} →
      (is : Tuple (Fin m) n₁) → (ts : Tuple (TermIn T c m) n₂) →
      (fs : Tuple (SeqAggFunc T) n₂) → AggQueryIn T c m (ColKind.allReg m) →
      AggQueryIn T c (n₁ + n₂)
        (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg))
  /-- Aggregation without grouping: one output row whatever the input,
  its aggregates reading the whole of it.

  It is not `Gamma` with no keys. SQL forms a single group here that exists
  even over no row, so the row is annotated `𝟙` and carries no
  group-existence factor, and its tokens have the empty world among their
  worlds (`AggValue.ofScalarGroup`): an aggregate over an empty input has a
  value, and a comparison against it has to be given one. -/
  | GammaScalar : {c m n₂ : ℕ} →
      (ts : Tuple (TermIn T c m) n₂) → (fs : Tuple (SeqAggFunc T) n₂) →
      AggQueryIn T c m (ColKind.allReg m) →
      AggQueryIn T c n₂ (fun _ => ColKind.agg)
  /-- Provenance aggregation: group by the key columns `is` (none of
  which may be a token column) and `⊕`-sum the term `t` over each group
  into a single `prov` output column – the abstract counterpart of
  ProvSQL's `⊕`-gate creation in rewritten plans. -/
  | ProvSum : {c m n₁ : ℕ} → {κ : Fin m → ColKind} →
      (is : Tuple (Fin m) n₁) → (his : ∀ k, κ (is k) ≠ ColKind.agg) →
      (t : TermGIn T c κ) → AggQueryIn T c m κ →
      AggQueryIn T c (n₁ + 1)
        (Fin.append (fun k => κ (is k)) (fun _ : Fin 1 => ColKind.prov))
  /-- Retag value columns between the value-armed kinds (`reg` and
  `prov`): semantically the identity, it declares which value columns
  carry provenance – the typing act of casting a value column to
  ProvSQL's uuid type. Token columns cannot be retagged. -/
  | Retag : {c n : ℕ} → {κ κ' : Fin n → ColKind} →
      (h : ∀ k, (κ k).base = (κ' k).base) → AggQueryIn T c n κ →
      AggQueryIn T c n κ'
  /-- Token-building grouping (ProvSQL's `provsql_agg`): group by the
  key columns `is`, output the keys, one aggregate token per
  `(term, aggregate)` pair whose occurrence annotations are the values
  of the explicit annotation term `a` (in rewritten plans: the
  provenance column of the subquery), and a trailing `prov` column
  carrying the group-existence guard. Its faithful semantics lives in
  the rewritten world's evaluator; the generic evaluators give it total
  modeling semantics, and the world-faithfulness exclusions
  (`noProvSum`) rule it out of source queries. -/
  | GammaTok : {c m n₁ n₂ : ℕ} → {κ : Fin m → ColKind} →
      (is : Tuple (Fin m) n₁) → (his : ∀ k, κ (is k) ≠ ColKind.agg) →
      (ts : Tuple (TermIn T c m) n₂) → (fs : Tuple (SeqAggFunc T) n₂) →
      (a : TermGIn T c κ) → AggQueryIn T c m κ →
      AggQueryIn T c (n₁ + n₂ + 1)
        (Fin.append
          (Fin.append (fun k => κ (is k)) (fun _ => ColKind.agg))
          (fun _ : Fin 1 => ColKind.prov))
  /-- **The window operator.** Every occurrence of the input keeps its row
  and its annotation and gains one column: the aggregate of `t` under `f`
  over that occurrence's frame, given by the partition columns `P`, the
  order columns `O`, the `ORDER BY` clause `o` and a frame `w` determined by
  values. The clause does two things SQL asks of it and the domain's order
  cannot: it bounds a `RANGE` or `GROUPS` frame, and it fixes the order the
  frame is read in, which is what an aggregate that is not symmetric
  depends on.

  It removes no row, merges none and changes no annotation, so it creates no
  group and produces no group-existence factor. Which occurrence a row is
  matters – two occurrences carrying the same row may have different frames,
  which is what `EXCLUDE CURRENT ROW` asks for – and the convention in which
  a row reads its token is decided per row, by whether the row is in its own
  frame (`ValueFrame.token`).

  `dist` says whether the aggregate reads the frame's *distinct* values:
  one occurrence per class of equal values, carrying the `⊕` of the
  class's members and read in the order the domain gives their values
  (`AggValue.mergeByValue`), which no reading of the unmerged token
  recovers, so the operator has to carry it. Over plain relations it is
  `SeqAggFunc.distinct`, and the order being a function of the values is
  what makes the reading world by world sound with no condition on the
  aggregate (`AggValue.specialize_mergeByValue`). It defaults to
  `false`, so a window written without it means what it meant. -/
  | Win : {c n m p : ℕ} →
      (P : Tuple (Fin n) m) → (O : Tuple (Fin n) p) → (o : OrderSpec p) →
      (w : ValueFrame T p) →
      (t : TermIn T c n) → (f : SeqAggFunc T) →
      AggQueryIn T c n (ColKind.allReg n) → (dist : Bool := false) →
      AggQueryIn T c (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg)

/-- A closed query: one that reads no outer column. -/
abbrev AggQuery (T : Type) (n : ℕ) (κ : Fin n → ColKind) := AggQueryIn T 0 n κ

/-- Transport a query along an equality of kind vectors (kind vectors
arising from projections are rarely definitionally all-regular). -/
def AggQueryIn.castKind {c n : ℕ} {κ κ' : Fin n → ColKind} (h : κ = κ') :
    AggQueryIn T c n κ → AggQueryIn T c n κ' := h ▸ id

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

def TermGIn.evalPlain {c : ℕ} {κ : Fin n → ColKind} (t : TermGIn T c κ)
    (u : Tuple T n) (γ : Fin c → T := fun _ => 0) : T :=
  match t with
  | .const a => a
  | .outer k => γ k
  | .index k _ => u k
  | .provIndex k _ => u k
  | .cmpAgg _ _ _ _ => 0
  | .chiGate _ _ _ => 0
  | .add t₁ t₂ => t₁.evalPlain u γ + t₂.evalPlain u γ
  | .sub t₁ t₂ => t₁.evalPlain u γ - t₂.evalPlain u γ
  | .mul t₁ t₂ => t₁.evalPlain u γ * t₂.evalPlain u γ
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    if op.eval3 (t₁.evalPlain u γ) (t₂.evalPlain u γ) = Kleene.true
    then t₃.evalPlain u γ else t₄.evalPlain u γ
  | .coalesce t₁ t₂ =>
    if ValueType.isNull (t₁.evalPlain u γ) then t₂.evalPlain u γ
    else t₁.evalPlain u γ

/-- **A term over regular columns read as a general term**: the same term,
the kind index witnessing that every column it reads is regular. It is
what a projection needs to carry a term of the aggregation grammar, whose
input is all-regular. -/
def TermIn.toGen {c n : ℕ} : TermIn T c n → TermGIn T c (ColKind.allReg n)
  | .const a => .const a
  | .outer k => .outer k
  | .index k => .index k rfl
  | .add t₁ t₂ => .add t₁.toGen t₂.toGen
  | .sub t₁ t₂ => .sub t₁.toGen t₂.toGen
  | .mul t₁ t₂ => .mul t₁.toGen t₂.toGen
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    .caseWhen op t₁.toGen t₂.toGen t₃.toGen t₄.toGen
  | .coalesce t₁ t₂ => .coalesce t₁.toGen t₂.toGen

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Reading a term as a general term does not change what it computes. -/
@[simp] theorem TermIn.evalPlain_toGen {c n : ℕ} (t : TermIn T c n)
    (u : Tuple T n) (γ : Fin c → T) : t.toGen.evalPlain u γ = t.eval u γ := by
  induction t with
  | const a => rfl
  | outer k => rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

/-! ## The gate-free fragment

The indicator gate `TermGIn.chiGate` is the one term constructor whose
faithful reading needs the rewritten world: it produces a provenance
value out of a comparison between regular values, which the generic
evaluators – having no annotation to return – can only approximate by
the junk constant. The `cmpAgg` gate escapes the same fate only because
its kind constraint keeps it off the columns the plain semantics sees.
The predicates below cut out the fragment where no indicator gate occurs,
on which the rewritten world's evaluator is the plain semantics
(`AggQueryIn.evaluateRew_plain`). -/

/-- No indicator gate in a term. -/
def TermGIn.chiFree {T' : Type} {c : ℕ} {κ : Fin n → ColKind} :
    TermGIn T' c κ → Prop
  | .const _ | .outer _ | .index _ _ | .provIndex _ _ => True
  | .cmpAgg _ _ _ t => t.chiFree
  | .chiGate _ _ _ => False
  | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ | .coalesce t₁ t₂ =>
      t₁.chiFree ∧ t₂.chiFree
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      t₁.chiFree ∧ t₂.chiFree ∧ t₃.chiFree ∧ t₄.chiFree

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- A term over regular columns has no indicator gate: the grammar of
`TermIn` has none to build. -/
theorem TermIn.chiFree_toGen {c n : ℕ} (t : TermIn T c n) : t.toGen.chiFree := by
  induction t with
  | const a => exact trivial
  | outer k => exact trivial
  | index k => exact trivial
  | add t₁ t₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | sub t₁ t₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | mul t₁ t₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ => exact ⟨ih₁, ih₂, ih₃, ih₄⟩
  | coalesce t₁ t₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

/-- No indicator gate in a predicate. -/
def GenPredIn.chiFree {T' : Type} {c : ℕ} {κ : Fin n → ColKind} :
    GenPredIn T' c κ → Prop
  | .cmp _ t₁ t₂ => t₁.chiFree ∧ t₂.chiFree
  | .aggCmp _ _ _ t => t.chiFree
  | .aggRange _ _ _ t₁ _ t₂ => t₁.chiFree ∧ t₂.chiFree
  | .and φ ψ | .or φ ψ => φ.chiFree ∧ ψ.chiFree
  | .not φ => φ.chiFree

/-- No indicator gate in a projection column. -/
def ProjColIn.chiFree {T' : Type} {c : ℕ} {κ : Fin n → ColKind} :
    ProjColIn T' c κ → Prop
  | .term t | .provTerm t => t.chiFree
  | .token _ _ | .aggTerm _ _ _ => True

/-! ## The rounds of a recursion

Both recursions iterate a step on relations; neither needs the query
syntax, so both are plain recursions on the round number with their own
lemmas. `muSum` collects the rounds of `Mu` – their multiset sum –
and `muIter` runs the fixpoint iteration of `MuSet`.

What the semantics calls “some round is empty” is in force here as the
hypothesis `step 0 = 0`: the sum `⨄_{i≥0} Mᵢ` over *all* rounds is a
relation only because an empty round is a fixpoint of the round
function, which is what SQL's requirement that the recursive reference
occur in the body buys. Nothing in this syntax enforces that, so it is
asked for where it is used. -/

/-- The multiset sum of the first `b + 1` iterates of `step` from `M`. -/
def muSum {α : Type} (step : Multiset α → Multiset α) :
    ℕ → Multiset α → Multiset α
  | 0, M => M
  | b + 1, M => M + muSum step b (step M)

/-- The `b`-th iterate of `step` from the empty relation. -/
def muIter {α : Type} (step : Multiset α → Multiset α) : ℕ → Multiset α
  | 0 => 0
  | b + 1 => step (muIter step b)

/-- One more round adds one more iterate. -/
theorem muSum_succ {α : Type} (step : Multiset α → Multiset α) (b : ℕ)
    (M : Multiset α) :
    muSum step (b + 1) M = muSum step b M + step^[b + 1] M := by
  induction b generalizing M with
  | zero => simp [muSum]
  | succ b ih =>
    rw [muSum, ih (step M), ← add_assoc, Function.iterate_succ_apply]
    rfl

/-- **An empty round stays empty.** -/
theorem iterate_eq_zero_of_le {α : Type} {step : Multiset α → Multiset α}
    (h0 : step 0 = 0) {M : Multiset α} {i : ℕ} (hi : step^[i] M = 0)
    {j : ℕ} (hij : i ≤ j) : step^[j] M = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_comm, Function.iterate_add_apply, hi, Function.iterate_fixed h0]

/-- **Past an empty round the sum no longer grows**: once the `i`-th
round is empty, every bound at least `i` gives the same value. This is
what makes `Mu b` the semantics' `⨄_{i≥0} Mᵢ` – on the fragment where
the rounds end, the bound is not part of what the query means. -/
theorem muSum_eq_of_le {α : Type} {step : Multiset α → Multiset α}
    (h0 : step 0 = 0) {M : Multiset α} {i : ℕ} (hi : step^[i] M = 0)
    {b b' : ℕ} (hb : i ≤ b) (hbb : b ≤ b') :
    muSum step b' M = muSum step b M := by
  induction b' with
  | zero => rw [Nat.le_zero.mp hbb]
  | succ b' ih =>
    rcases Nat.lt_or_ge b (b' + 1) with h | h
    · have hb' : b ≤ b' := Nat.lt_succ_iff.mp h
      rw [muSum_succ, ih hb',
        iterate_eq_zero_of_le h0 hi (hb.trans (hb'.trans (Nat.le_succ b'))),
        add_zero]
    · rw [le_antisymm hbb h]

/-- **Past the fixpoint the iteration no longer moves**: once a round
repeats, every bound at least that one gives the same value. -/
theorem muIter_eq_of_le {α : Type} {step : Multiset α → Multiset α} {j : ℕ}
    (hj : step (muIter step j) = muIter step j) {b : ℕ} (hb : j ≤ b) :
    muIter step b = muIter step j := by
  induction b with
  | zero => rw [Nat.le_zero.mp hb]
  | succ b ih =>
    rcases Nat.lt_or_ge j (b + 1) with h | h
    · rw [muIter, ih (Nat.lt_succ_iff.mp h), hj]
    · rw [le_antisymm hb h]

/-- Rounds built from the same step on the same seed agree. -/
theorem muSum_congr {α : Type} {step step' : Multiset α → Multiset α}
    (h : ∀ X, step X = step' X) (b : ℕ) :
    ∀ {M M' : Multiset α}, M = M' → muSum step b M = muSum step' b M' := by
  induction b with
  | zero => intro M M' hM; exact hM
  | succ b ih =>
    intro M M' hM
    rw [muSum, muSum, hM]
    exact congrArg _ (ih (h M'))

/-- Iterations of the same step agree. -/
theorem muIter_congr {α : Type} {step step' : Multiset α → Multiset α}
    (h : ∀ X, step X = step' X) (b : ℕ) : muIter step b = muIter step' b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [muIter, muIter, ih, h]

/-- **An additive map commutes with the rounds of `Mu`**: forgetting
annotations, or applying a semiring homomorphism, round by round is the
same as doing it to the sum. -/
theorem muSum_map {α β : Type} {h : Multiset α → Multiset β}
    (hadd : ∀ x y, h (x + y) = h x + h y)
    {step : Multiset α → Multiset α} {stepP : Multiset β → Multiset β}
    (hstep : ∀ X, h (step X) = stepP (h X)) (b : ℕ) (M : Multiset α) :
    h (muSum step b M) = muSum stepP b (h M) := by
  induction b generalizing M with
  | zero => rfl
  | succ b ih => rw [muSum, hadd, ih, hstep, muSum]

/-- **A map sending the empty relation to the empty relation commutes
with the iteration of `MuSet`.** -/
theorem muIter_map {α β : Type} {h : Multiset α → Multiset β} (h0 : h 0 = 0)
    {step : Multiset α → Multiset α} {stepP : Multiset β → Multiset β}
    (hstep : ∀ X, h (step X) = stepP (h X)) (b : ℕ) :
    h (muIter step b) = muIter stepP b := by
  induction b with
  | zero => exact h0
  | succ b ih => rw [muIter, hstep, ih, muIter]

/-- Duplicate elimination on an annotated relation: one slot per tuple,
annotated by the `⊕` of its copies – what `Dedup` computes, named for
the rounds of `MuSet`. -/
def AnnotatedRelation.dedupAnn {n : ℕ} (r : AnnotatedRelation T K n) :
    AnnotatedRelation T K n := Multiset.ofList (groupByKey r).val

/-- **The general annotated evaluator.** All operators preserve the
factored-annotation discipline described in the module docstring. -/
def AggQueryIn.evaluate {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) : Multiset (GenRow T K n) :=
  match c, n, κ, q, d, γ with
  | _, n, _, Rel _ s, d, _ =>
    match d.find n s with
    | none => (∅ : Multiset (GenRow T K n))
    | some rn => (rn : Multiset (AnnotatedTuple T K n)).map GenRow.ofAnnotated
  | _, _, _, @Proj _ _ n m κ ps q, d, γ =>
    (q.evaluate d γ).map (fun r =>
      let u' : Tuple (GenValue T K) m := fun j => (ps j).eval r.fst γ
      -- groups all of whose token columns are dropped are cashed
      let kept := r.snd.pending ∩ tokenLists u'
      ⟨u', ⟨r.snd.base *
          ((r.snd.pending - kept).map
            (fun l => SemiringWithMonus.delta l.sum)).prod,
        kept⟩⟩)
  | _, _, _, Sel φ q, d, γ =>
    let r := q.evaluate d γ
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
        -- and only when none of them is scalar: a scalar token holds in the
        -- empty world, so a comparison against it entails no group's
        -- existence and must not remove any group's factor, whatever
        -- occurrences it happens to carry
        let comparedScalar : Multiset (List K) :=
          φ.comparedCols.val.filterMap (fun k =>
            match r.fst k with
            | Sum.inl _ => none
            | Sum.inr a => if a.scalar then some (a.occs.map Prod.snd) else none)
        ⟨r.fst, ⟨r.snd.base * φ.predsem false r.fst γ,
          if φ.entailsExistence false then
            r.snd.pending.filter
              (fun l => ¬(comparedScalar = 0 ∧ compared ≠ 0
                ∧ ∀ l' ∈ compared, l' = l))
          else r.snd.pending⟩⟩)
    else
      r.filter (fun r => φ.holds r.fst γ)
  | _, _, _, Prod q₁ q₂, d, γ =>
    ((q₁.evaluate d γ).product (q₂.evaluate d γ)).map (fun (x, y) =>
      ⟨Fin.append x.fst y.fst,
        ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩)
  | _, _, _, @Apply _ _ n₁ _ _ q₁ q₂, d, γ =>
    -- the right side is read once per row of the left, under that row
    (q₁.evaluate d γ).bind (fun x =>
      (q₂.evaluate d (Fin.append (GenRow.plainTuple x.fst) γ)).map (fun y =>
        (⟨Fin.append x.fst y.fst,
          ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
            : GenRow T K (n₁ + _))))
  | _, _, _, Sum q₁ q₂, d, γ => q₁.evaluate d γ + q₂.evaluate d γ
  | _, _, _, Dedup q, d, γ =>
    let r : AnnotatedRelation T K _ := (q.evaluate d γ).map GenRow.toAnnotated
    (Multiset.ofList (groupByKey r).val).map GenRow.ofAnnotated
  | _, _, _, Mu b s q₀ q₁, d, γ =>
    (muSum (fun X => (q₁.evaluate (d.assign s X) γ).map GenRow.toAnnotated) b
      ((q₀.evaluate d γ).map GenRow.toAnnotated)).map GenRow.ofAnnotated
  | _, _, _, MuSet b s q₀ q₁, d, γ =>
    (muIter (fun X =>
      AnnotatedRelation.dedupAnn
        (((q₀.evaluate (d.assign s X) γ).map GenRow.toAnnotated)
          + ((q₁.evaluate (d.assign s X) γ).map GenRow.toAnnotated))) b).map
      GenRow.ofAnnotated
  | _, _, _, Diff q₁ q₂, d, γ =>
    let r₁ : AnnotatedRelation T K _ := (q₁.evaluate d γ).map GenRow.toAnnotated
    let r₂ : AnnotatedRelation T K _ := (q₂.evaluate d γ).map GenRow.toAnnotated
    let grouped₂ := groupByKey r₂
    (r₁.map (fun (u, α) =>
      (⟨u, α - (((grouped₂.val.find? (·.1 = u)).map Prod.snd).getD 0)⟩ :
        AnnotatedTuple T K _))).map GenRow.ofAnnotated
  | _, _, _, @Gamma _ _ m n₁ n₂ is ts fs q, d, γ =>
    let r : AnnotatedRelation T K m := (q.evaluate d γ).map GenRow.toAnnotated
    -- one row per group key (the closed form is `havingSite_evaluateAnnotated`)
    (Multiset.ofList (groupByKey (r.map (fun p => (fun k => p.fst (is k), p.snd)
        : AnnotatedTuple T K m → AnnotatedTuple T K n₁))).val).map (fun kv =>
      let g : Tuple T n₁ := kv.fst
      let U := Having.havingGroup is r g
      ⟨Fin.append (fun k => Sum.inl (g k))
        (fun j => Sum.inr (AggValue.ofGroup (fs j) (ts j) U γ)),
       ⟨1, {U.map Prod.snd}⟩⟩)
  | _, _, _, @GammaScalar _ _ m n₂ ts fs q, d, γ =>
    let r : AnnotatedRelation T K m := (q.evaluate d γ).map GenRow.toAnnotated
    -- one row whatever the input; the whole of it is the occurrence sequence
    let U := Having.havingGroup (fun k : Fin 0 => k.elim0) r (fun k : Fin 0 => k.elim0)
    {(⟨fun j => Sum.inr (AggValue.ofScalarGroup (fs j) (ts j) U γ), ⟨1, 0⟩⟩
      : GenRow T K n₂)}
  | _, _, _, Retag _ q, d, γ => q.evaluate d γ
  | _, _, _, @ProvSum _ _ _m n₁ _κ is _his t q, d, γ =>
    let r : AnnotatedRelation T K _ := (q.evaluate d γ).map GenRow.toAnnotated
    let keys := (r.map (fun p => (fun k => p.fst (is k) : Tuple T n₁))).dedup
    keys.map (fun g =>
      (⟨Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun _ : Fin 1 => Sum.inl
            (((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
              (fun p => t.evalPlain p.fst γ)).fold addFn 0)),
        ⟨((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
            Prod.snd).sum, 0⟩⟩ : GenRow T K (n₁ + 1)))
  | _, _, _, @GammaTok _ _ m n₁ n₂ _κ is _his ts fs a q, d, γ =>
    let r : AnnotatedRelation T K m := (q.evaluate d γ).map GenRow.toAnnotated
    (Multiset.ofList (groupByKey (r.map (fun p => (fun k => p.fst (is k), p.snd)
        : AnnotatedTuple T K m → AnnotatedTuple T K n₁))).val).map (fun kv =>
      let g : Tuple T n₁ := kv.fst
      let U := Having.havingGroup is r g
      ⟨Fin.append
        (Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun j => Sum.inr (AggValue.ofGroup (fs j) (ts j) U γ)))
        (fun _ : Fin 1 => Sum.inl
          (((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
            (fun p => a.evalPlain p.fst γ)).fold addFn 0)),
       ⟨1, {U.map Prod.snd}⟩⟩)
  | _, _, _, @Win _ _ n _m _p P O o w t f q dist, d, γ =>
    let r : AnnotatedRelation T K n := (q.evaluate d γ).map GenRow.toAnnotated
    -- the canonical indexing: an occurrence is what a frame is computed for,
    -- and two occurrences carrying the same row may have different frames
    let occ := OccFam.ofSorted r
    -- each occurrence keeps its row and its annotation, and gains its token;
    -- no row is removed and no group is created, so nothing goes pending
    (OccFam.mk occ.size (fun i =>
      (⟨Fin.snoc (fun k => (Sum.inl ((occ.row i).fst k) : GenValue T K))
          (Sum.inr (ValueFrame.tokenDist P O o w t f dist occ i γ)),
        ⟨(occ.row i).snd, 0⟩⟩ : GenRow T K (n + 1)))).toMultiset
termination_by structural q

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Appending nothing: a closed query's apply gives its right side the
left row and nothing else. -/
theorem Fin.append_nil {α : Sort*} {m : ℕ} (u : Fin m → α) (v : Fin 0 → α) :
    Fin.append u v = u := by
  funext k
  exact Fin.append_left u v k

/-- **The apply, read off the two sides.** Each occurrence of the left
side is paired with each row the right side gives *under that
occurrence's values*, and the annotations are multiplied. -/
theorem AggQueryIn.evaluate_Apply {n₁ n₂ : ℕ} {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁)) (q₂ : AggQueryIn T n₁ n₂ κ₂)
    (d : AnnotatedDatabase T K) :
    (AggQueryIn.Apply q₁ q₂).evaluate d
      = (q₁.evaluate d).bind (fun x =>
          (q₂.evaluate d (GenRow.plainTuple x.fst)).map (fun y =>
            (⟨Fin.append x.fst y.fst,
              ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
              : GenRow T K (n₁ + n₂)))) := by
  simp only [AggQueryIn.evaluate, Fin.append_nil]

/-- The final annotated relation computed by a general query: evaluate,
then finalize every row. -/
def AggQueryIn.evaluateAnnotated {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) : AnnotatedRelation T K n :=
  (q.evaluate d γ).map GenRow.toAnnotated

/-! ## What the recursions compute, and when the bound drops out -/

/-- The round function of `Mu`: the body read with the name bound to the
previous round. -/
def AggQueryIn.muStep {c n : ℕ} (s : String)
    (q₁ : AggQueryIn T c n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) :
    AnnotatedRelation T K n → AnnotatedRelation T K n :=
  fun X => q₁.evaluateAnnotated (d.assign s X) γ

/-- The round function of `MuSet`: `ε(q₀ ⊎ q₁)` read with the name bound
to the previous round. -/
def AggQueryIn.muSetStep {c n : ℕ} (s : String)
    (q₀ q₁ : AggQueryIn T c n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) :
    AnnotatedRelation T K n → AnnotatedRelation T K n :=
  fun X => AnnotatedRelation.dedupAnn
    (q₀.evaluateAnnotated (d.assign s X) γ
      + q₁.evaluateAnnotated (d.assign s X) γ)

/-- `Mu` is the multiset sum of its rounds. -/
theorem AggQueryIn.evaluate_Mu {c n : ℕ} (b : ℕ) (s : String)
    (q₀ q₁ : AggQueryIn T c n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) :
    (AggQueryIn.Mu b s q₀ q₁).evaluate d γ
      = (muSum (AggQueryIn.muStep s q₁ d γ) b (q₀.evaluateAnnotated d γ)).map
          GenRow.ofAnnotated :=
  rfl

/-- `MuSet` is the `b`-th step of its fixpoint iteration. -/
theorem AggQueryIn.evaluate_MuSet {c n : ℕ} (b : ℕ) (s : String)
    (q₀ q₁ : AggQueryIn T c n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) :
    (AggQueryIn.MuSet b s q₀ q₁).evaluate d γ
      = (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ) b).map GenRow.ofAnnotated :=
  rfl

/-- **The bound drops out of `Mu` where the rounds end.** Given a round
that is empty and a round function that keeps an empty round empty –
which is what the semantics asks for in asking that some round be empty –
every bound past that round computes the same relation, so on that
fragment `Mu b` is the semantics' `⨄_{i≥0} Mᵢ` and the bound is not part
of what the query means. -/
theorem AggQueryIn.evaluate_Mu_eq_of_le {c n : ℕ} {b b' i : ℕ} (s : String)
    (q₀ q₁ : AggQueryIn T c n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (h0 : AggQueryIn.muStep s q₁ d γ 0 = 0)
    (hi : (AggQueryIn.muStep s q₁ d γ)^[i] (q₀.evaluateAnnotated d γ) = 0)
    (hb : i ≤ b) (hbb : b ≤ b') :
    (AggQueryIn.Mu b' s q₀ q₁).evaluate d γ
      = (AggQueryIn.Mu b s q₀ q₁).evaluate d γ := by
  rw [AggQueryIn.evaluate_Mu, AggQueryIn.evaluate_Mu,
    muSum_eq_of_le h0 hi hb hbb]

/-- **The bound drops out of `MuSet` where the iteration stabilizes.** -/
theorem AggQueryIn.evaluate_MuSet_eq_of_le {c n : ℕ} {b b' j : ℕ} (s : String)
    (q₀ q₁ : AggQueryIn T c n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (γ : Fin c → T)
    (hj : AggQueryIn.muSetStep s q₀ q₁ d γ
        (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ) j)
      = muIter (AggQueryIn.muSetStep s q₀ q₁ d γ) j)
    (hb : j ≤ b) (hbb : b ≤ b') :
    (AggQueryIn.MuSet b' s q₀ q₁).evaluate d γ
      = (AggQueryIn.MuSet b s q₀ q₁).evaluate d γ := by
  rw [AggQueryIn.evaluate_MuSet, AggQueryIn.evaluate_MuSet,
    muIter_eq_of_le hj (hb.trans hbb), muIter_eq_of_le hj hb]

/-- The row a window gives a row of its input relation: the row itself, one
column longer, with the token the relation gives it, its annotation kept and
nothing pending – a window creates no group. -/
def ValueFrame.windowRow {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (X : AnnotatedRelation T K n)
    (x : AnnotatedTuple T K n) (γ : Fin c → T := fun _ => 0)
    (dist : Bool := false) :
    GenRow T K (n + 1) :=
  ⟨Fin.snoc (fun k => (Sum.inl (x.fst k) : GenValue T K))
      (Sum.inr (ValueFrame.tokenOfDist P O o w t f dist X x γ)), ⟨x.snd, 0⟩⟩

/-- **The `Win` case of the evaluator, read off the relation.** The output is
the input relation mapped row by row, each row gaining the token its relation
gives it. This is the form every theorem about the operator uses; that it is
legitimate – that an occurrence's token is determined by the relation even
though its frame is not determined by its row – is `ValueFrame.tokenOf`. -/
theorem AggQueryIn.evaluate_Win_eq {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) {γ : Fin c → T} :
    (AggQueryIn.Win P O o w t f q dist).evaluate d γ
      = (q.evaluateAnnotated d γ).map
          (fun x => ValueFrame.windowRow P O o w t f
            (q.evaluateAnnotated d γ) x γ dist) := by
  conv_rhs => rw [← OccFam.toMultiset_ofSorted (q.evaluateAnnotated d γ)]
  rw [OccFam.toMultiset_map]
  refine congrArg OccFam.toMultiset (OccFam.ext_cast rfl (fun i => ?_))
  show (_ : GenRow T K (n + 1)) = ValueFrame.windowRow P O o w t f _ _ _ dist
  unfold ValueFrame.windowRow ValueFrame.tokenOfDist ValueFrame.tokenDist
    AggQueryIn.evaluateAnnotated
  dsimp only [Fin.cast_eq_self]
  rw [ValueFrame.token_eq_tokenOf, OccFam.toMultiset_ofSorted]

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

namespace GenPredIn

variable {n : ℕ} {κ : Fin n → ColKind}

/-- Classical truth of a predicate on a regular tuple: aggregate atoms
compare the computed aggregate value of their column. -/
def evalPlain3 (φ : GenPredIn T c κ) (u : Tuple T n)
    (γ : Fin c → T := fun _ => 0) : Kleene :=
  match φ with
  | cmp op t₁ t₂ => op.eval3 (t₁.evalPlain u γ) (t₂.evalPlain u γ)
  | aggCmp k _ op t => op.eval3 (u k) (t.evalPlain u γ)
  | aggRange k _ op₁ t₁ op₂ t₂ =>
    (op₁.eval3 (u k) (t₁.evalPlain u γ)).and (op₂.eval3 (u k) (t₂.evalPlain u γ))
  | and φ ψ => (φ.evalPlain3 u γ).and (ψ.evalPlain3 u γ)
  | or φ ψ => (φ.evalPlain3 u γ).or (ψ.evalPlain3 u γ)
  | not φ => (φ.evalPlain3 u γ).not

/-- The rows a selection keeps classically: those on which the predicate is
*true*. -/
def holdsPlain (φ : GenPredIn T c κ) (u : Tuple T n)
    (γ : Fin c → T := fun _ => 0) : Prop :=
  φ.evalPlain3 u γ = Kleene.true

/-- Structural decidability of `holdsPlain`. -/
def decHoldsPlain (φ : GenPredIn T c κ) (u : Tuple T n)
    (γ : Fin c → T := fun _ => 0) : Decidable (φ.holdsPlain u γ) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] theorem holdsPlain_and (φ ψ : GenPred T κ) (u : Tuple T n) :
    (GenPredIn.and φ ψ).holdsPlain u ↔ φ.holdsPlain u ∧ ψ.holdsPlain u :=
  Kleene.and_eq_true_iff _ _

@[simp] theorem holdsPlain_or (φ ψ : GenPred T κ) (u : Tuple T n) :
    (GenPredIn.or φ ψ).holdsPlain u ↔ φ.holdsPlain u ∨ ψ.holdsPlain u :=
  Kleene.or_eq_true_iff _ _

@[simp] theorem holdsPlain_not (φ : GenPred T κ) (u : Tuple T n) :
    (GenPredIn.not φ).holdsPlain u ↔ φ.evalPlain3 u = Kleene.false :=
  Kleene.not_eq_true_iff _

/-- Where nothing is null no predicate is ever unknown on a plain row. -/
theorem evalPlain3_ne_unknown [NoNulls T] (u : Tuple T n) :
    ∀ φ : GenPred T κ, φ.evalPlain3 u ≠ Kleene.unknown
  | cmp op t₁ t₂ => by
    rw [GenPredIn.evalPlain3, CompOp.eval3_eq_ofBool]
    cases decide (op.eval (t₁.evalPlain u) (t₂.evalPlain u)) <;>
      simp [Kleene.ofBool]
  | aggCmp k h op t => by
    rw [GenPredIn.evalPlain3, CompOp.eval3_eq_ofBool]
    cases decide (op.eval (u k) (t.evalPlain u)) <;> simp [Kleene.ofBool]
  | aggRange k h op₁ t₁ op₂ t₂ => by
    rw [GenPredIn.evalPlain3, CompOp.eval3_eq_ofBool, CompOp.eval3_eq_ofBool]
    cases decide (op₁.eval (u k) (t₁.evalPlain u)) <;>
      cases decide (op₂.eval (u k) (t₂.evalPlain u)) <;>
      simp [Kleene.ofBool, Kleene.and]
  | and φ ψ => by
    have h₁ := evalPlain3_ne_unknown u φ
    have h₂ := evalPlain3_ne_unknown u ψ
    cases e₁ : φ.evalPlain3 u <;> cases e₂ : ψ.evalPlain3 u <;>
      simp_all [GenPredIn.evalPlain3, Kleene.and]
  | or φ ψ => by
    have h₁ := evalPlain3_ne_unknown u φ
    have h₂ := evalPlain3_ne_unknown u ψ
    cases e₁ : φ.evalPlain3 u <;> cases e₂ : ψ.evalPlain3 u <;>
      simp_all [GenPredIn.evalPlain3, Kleene.or]
  | not φ => by
    have h := evalPlain3_ne_unknown u φ
    cases e : φ.evalPlain3 u <;> simp_all [GenPredIn.evalPlain3, Kleene.not]

/-- Negation is classical on a plain row where nothing is null. -/
theorem holdsPlain_not_iff [NoNulls T] (φ : GenPred T κ) (u : Tuple T n) :
    (GenPredIn.not φ).holdsPlain u ↔ ¬ φ.holdsPlain u := by
  have h := evalPlain3_ne_unknown u φ
  show (φ.evalPlain3 u).not = Kleene.true ↔ ¬ (φ.evalPlain3 u = Kleene.true)
  cases e : φ.evalPlain3 u <;> simp_all [Kleene.not]

instance (φ : GenPredIn T c κ) (γ : Fin c → T) (u : Tuple T n) :
    Decidable (φ.holdsPlain u γ) := φ.decHoldsPlain u γ

end GenPredIn

/-- Plain evaluation of a projection column. -/
def ProjColIn.evalPlain {c : ℕ} {κ : Fin n → ColKind} (p : ProjColIn T c κ)
    (u : Tuple T n) (γ : Fin c → T := fun _ => 0) : T :=
  match p with
  | .term t => t.evalPlain u γ
  | .token k _ => u k
  | .aggTerm k _ gf => gf (u k)
  | .provTerm t => t.evalPlain u γ

/-- **The plain evaluator**: standard multiset semantics, with `Gamma`
computing the aggregate of each group's full occurrence sequence (in the
canonical `≼` order of `Relation.groupSeq`) and every selection filtering
classically. `Diff` is the all-or-nothing difference of
`Query.evaluate`. -/
def AggQueryIn.evaluatePlain : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Database T →
    (γ : Fin c → T := fun _ => 0) → Relation T n
  | _, n, _, Rel _ s, d, _ =>
    match d.find n s with
    | none => (∅ : Multiset (Tuple T n))
    | some rn => rn
  | _, _, _, @Proj _ _ n _ κ ps q, d, γ =>
    (q.evaluatePlain d γ).map (fun u => (fun j => (ps j).evalPlain u γ))
  | _, _, _, Sel φ q, d, γ =>
    @Multiset.filter _ (fun u => φ.holdsPlain u γ)
      (fun u => φ.decHoldsPlain u γ) (q.evaluatePlain d γ)
  | _, _, _, Prod q₁ q₂, d, γ => q₁.evaluatePlain d γ * q₂.evaluatePlain d γ
  | _, _, _, @Apply _ _ n₁ _ _ q₁ q₂, d, γ =>
    (q₁.evaluatePlain d γ).bind (fun u =>
      (q₂.evaluatePlain d (Fin.append u γ)).map (fun v =>
        (Fin.append u v : Tuple T (n₁ + _))))
  | _, _, _, Sum q₁ q₂, d, γ => q₁.evaluatePlain d γ + q₂.evaluatePlain d γ
  | _, _, _, Dedup q, d, γ => (q.evaluatePlain d γ).dedup
  | _, _, _, Mu b s q₀ q₁, d, γ =>
    muSum (fun X => q₁.evaluatePlain (d.assign s X) γ) b (q₀.evaluatePlain d γ)
  | _, _, _, MuSet b s q₀ q₁, d, γ =>
    muIter (fun X => (q₀.evaluatePlain (d.assign s X) γ
      + q₁.evaluatePlain (d.assign s X) γ).dedup) b
  | _, _, _, Diff q₁ q₂, d, γ =>
    let r₂ : Multiset (Tuple T _) := q₂.evaluatePlain d γ
    (q₁.evaluatePlain d γ).filter (fun t => t ∉ r₂)
  | _, _, _, @Gamma _ _ _m n₁ n₂ is ts fs q, d, γ =>
    let r := q.evaluatePlain d γ
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append g
      (fun j => (fs j)
        ((Relation.groupSeq is r g).map (fun v => (ts j).eval v γ))))
  | _, _, _, @GammaScalar _ _ _m n₂ ts fs q, d, γ =>
    let r := q.evaluatePlain d γ
    (Multiset.ofList [(fun j => (fs j)
      ((Relation.groupSeq (fun k : Fin 0 => k.elim0) r
        (fun k : Fin 0 => k.elim0)).map (fun v => (ts j).eval v γ))
          : Tuple T n₂)] : Relation T n₂)
  | _, _, _, Retag _ q, d, γ => q.evaluatePlain d γ
  | _, _, _, @ProvSum _ _ _m n₁ _κ is _his t q, d, γ =>
    let r := q.evaluatePlain d γ
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append g (fun _ : Fin 1 =>
      ((r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map
        (fun u => t.evalPlain u γ)).fold addFn 0))
  | _, _, _, @GammaTok _ _ _m n₁ n₂ _κ is _his ts fs a q, d, γ =>
    let r := q.evaluatePlain d γ
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append
      (Fin.append g
        (fun j => (fs j)
          ((Relation.groupSeq is r g).map (fun v => (ts j).eval v γ))))
      (fun _ : Fin 1 =>
        ((r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map
          (fun u => a.evalPlain u γ)).fold addFn 0))
  | _, _, _, @Win _ _ n _m _p P O o w t f q dist, d, γ =>
    -- the canonical indexing again; a frame is computed for an occurrence
    let occ := OccFam.ofSorted (q.evaluatePlain d γ)
    (OccFam.mk occ.size (fun i =>
      (Fin.snoc (occ.row i)
        ((if dist then f.distinct else f)
          ((ValueFrame.frameSeqOn (α := Tuple T n) id P O o w occ i).map
            (fun v => t.eval v γ)))
        : Tuple T (n + 1)))).toMultiset

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Plain counterpart of `AggQueryIn.evaluate_Apply`. -/
theorem AggQueryIn.evaluatePlain_Apply {n₁ n₂ : ℕ} {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁)) (q₂ : AggQueryIn T n₁ n₂ κ₂)
    (D : Database T) :
    (AggQueryIn.Apply q₁ q₂).evaluatePlain D
      = (q₁.evaluatePlain D).bind (fun u =>
          (q₂.evaluatePlain D u).map (fun v =>
            (Fin.append u v : Tuple T (n₁ + n₂)))) := by
  simp only [AggQueryIn.evaluatePlain, Fin.append_nil]

/-- The value a window's added column takes on a row of a plain relation:
the aggregate of the term over that row's frame, read off the relation. -/
def ValueFrame.windowValue {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (R : Relation T n) (u : Tuple T n)
    (γ : Fin c → T := fun _ => 0) : T :=
  f ((ValueFrame.frameListOf (α := Tuple T n) id P O o w R u).map
    (fun v => t.eval v γ))

/-- **Where the aggregate is symmetric the sequence a frame is read in does
not matter**: any listing of the frame gives the value the window gives, so
the canonical order the library sorts by is as good as the order an `ORDER
BY` asks for. It is for an aggregate that is not symmetric – `PICKFIRST` –
that the two have to be the same order. -/
theorem ValueFrame.windowValue_of_perm {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n)
    {f : SeqAggFunc T} (hf : f.Symmetric) (R : Relation T n) (u : Tuple T n)
    (L : List (Tuple T n)) {γ : Fin c → T}
    (hL : (L : Multiset (Tuple T n))
      = ValueFrame.frameOf (α := Tuple T n) id P O w R u) :
    f (L.map (fun x => t.eval x γ))
      = ValueFrame.windowValue P O o w t f R u γ := by
  unfold ValueFrame.windowValue ValueFrame.frameListOf
  refine hf (List.Perm.map _ (List.Perm.trans ?_ (OrderSpec.sortSeq_perm _).symm))
  rw [← Multiset.coe_eq_coe, hL, sortList_coe]

/-- **The `Win` case of the plain evaluator, read off the relation.** -/
theorem AggQueryIn.evaluatePlain_Win_eq {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (q : AggQueryIn T c n (ColKind.allReg n)) (d : Database T)
    {γ : Fin c → T} :
    (AggQueryIn.Win P O o w t f q dist).evaluatePlain d γ
      = (q.evaluatePlain d γ).map (fun u : Tuple T n =>
          (Fin.snoc u
            (ValueFrame.windowValue P O o w t
              (if dist then f.distinct else f) (q.evaluatePlain d γ) u γ)
            : Tuple T (n + 1))) := by
  conv_rhs => rw [← OccFam.toMultiset_ofSorted (q.evaluatePlain d γ)]
  rw [OccFam.toMultiset_map]
  refine congrArg OccFam.toMultiset (OccFam.ext_cast rfl (fun i => ?_))
  show (_ : Tuple T (n + 1))
    = Fin.snoc _ (ValueFrame.windowValue P O o w t
        (if dist then f.distinct else f) _ _ _)
  unfold ValueFrame.windowValue
  dsimp only [Fin.cast_eq_self]
  rw [ValueFrame.frameSeqOn_eq_frameListOf, OccFam.toMultiset_ofSorted]

/-- Strip a general query of the constructs whose annotated data part
keeps rows the classical semantics removes: differences (annotated `Diff`
never removes tuple slots) and selections containing an aggregate atom
(the annotated evaluator keeps classically-failing rows annotated `𝟘`,
as ProvSQL emits them). The data-part adequacy of `evaluateAnnotated`
is stated against the plain evaluation of the stripped query, mirroring
`Query.stripDiff` in `Provenance.QueryAdequacy`. -/
def AggQueryIn.stripAgg : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → AggQueryIn T c n κ
  | _, _, _, Rel n s => Rel n s
  | _, _, _, Proj ps q => Proj ps q.stripAgg
  | _, _, _, Sel φ q =>
    if φ.hasAggAtom then q.stripAgg else Sel φ q.stripAgg
  | _, _, _, Prod q₁ q₂ => Prod q₁.stripAgg q₂.stripAgg
  | _, _, _, Apply q₁ q₂ => Apply q₁.stripAgg q₂.stripAgg
  | _, _, _, Sum q₁ q₂ => Sum q₁.stripAgg q₂.stripAgg
  | _, _, _, Dedup q => Dedup q.stripAgg
  | _, _, _, Diff q₁ _ => q₁.stripAgg
  | _, _, _, Mu b s q₀ q₁ => Mu b s q₀.stripAgg q₁.stripAgg
  | _, _, _, MuSet b s q₀ q₁ => MuSet b s q₀.stripAgg q₁.stripAgg
  | _, _, _, Gamma is ts fs q => Gamma is ts fs q.stripAgg
  | _, _, _, GammaScalar ts fs q => GammaScalar ts fs q.stripAgg
  | _, _, _, ProvSum is his t q => ProvSum is his t q.stripAgg
  | _, _, _, Retag h q => Retag h q.stripAgg
  | _, _, _, GammaTok is his ts fs a q => GammaTok is his ts fs a q.stripAgg
  | _, _, _, Win P O o w t f q dist => Win P O o w t f q.stripAgg dist

/-- No plan-level provenance aggregation. The possible-world
metatheorems (random-world commutation, PQE) are about source queries;
`ProvSum` is a rewriting-target operator whose deterministic group sum
is not world-faithful – exactly as the classical `Agg` was excluded from
the annotated evaluators. -/
def AggQueryIn.noProvSum : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Proj _ q => q.noProvSum
  | _, _, _, .Sel _ q => q.noProvSum
  | _, _, _, .Prod q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, .Apply q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, .Sum q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, .Dedup q => q.noProvSum
  | _, _, _, .Diff q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, .Mu _ _ q₀ q₁ => q₀.noProvSum ∧ q₁.noProvSum
  | _, _, _, .MuSet _ _ q₀ q₁ => q₀.noProvSum ∧ q₁.noProvSum
  | _, _, _, .Gamma _ _ _ q => q.noProvSum
  | _, _, _, .GammaScalar _ _ q => q.noProvSum
  | _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, .Retag _ q => q.noProvSum
  | _, _, _, .GammaTok _ _ _ _ _ _ => False
  | _, _, _, .Win _ _ _ _ _ _ q _ => q.noProvSum

/-! ## Join conditions on key columns -/

/-- The conjunction of key equalities between two blocks of regular columns
(the join condition of the `Diff` rewriting).

The atoms are SQL's `IS NOT DISTINCT FROM`, not `=`: a key join keys on
values, two nulls being the same key, where `NULL = NULL` is unknown and
would drop the row. -/
def keyJoinCond {T' : Type} [Zero T'] {n m : ℕ} {κ : Fin m → ColKind}
    (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ (posL k) = ColKind.reg)
    (hR : ∀ k, κ (posR k) = ColKind.reg) :
    GenPred T' κ :=
  ((List.finRange n).map (fun k =>
    GenPredIn.cmp CompOp.syneq (TermGIn.index (posL k) (hL k))
      (TermGIn.index (posR k) (hR k)))).foldr GenPredIn.and
    (GenPredIn.cmp CompOp.syneq (.const 0) (.const 0))

/-- The join condition is a conjunction of column equalities: no
indicator gate. -/
theorem keyJoinCond_chiFree {T' : Type} [Zero T'] {n m : ℕ}
    {κ : Fin m → ColKind} (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ (posL k) = ColKind.reg)
    (hR : ∀ k, κ (posR k) = ColKind.reg) :
    (keyJoinCond (T' := T') posL posR hL hR).chiFree := by
  unfold keyJoinCond
  induction List.finRange n with
  | nil => exact ⟨trivial, trivial⟩
  | cons k l ih => exact ⟨⟨trivial, trivial⟩, ih⟩

theorem GenPredIn.holdsPlain_foldr_and {T' : Type} [ValueType T'] {N : ℕ}
    {κ' : Fin N → ColKind} {α : Type} (l : List α)
    (f : α → GenPred T' κ') (base : GenPred T' κ') (u : Tuple T' N) :
    (((l.map f).foldr GenPredIn.and base).holdsPlain u)
      ↔ (∀ x ∈ l, (f x).holdsPlain u) ∧ base.holdsPlain u := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.foldr_cons, GenPredIn.holdsPlain_and, ih]
    constructor
    · rintro ⟨hhd, htl, hb⟩
      exact ⟨fun x hx => (List.mem_cons.mp hx).elim (fun he => he ▸ hhd)
        (htl x), hb⟩
    · rintro ⟨hall, hb⟩
      exact ⟨hall hd (List.mem_cons_self), fun x hx => hall x (List.mem_cons_of_mem hd hx), hb⟩

/-- **The join condition holds exactly when the two blocks of key columns
carry the same values** – nulls included, the atoms being syntactic. -/
theorem keyJoinCond_holdsPlain {T' : Type} [ValueType T']
    {n m : ℕ} {κ' : Fin m → ColKind} (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ' (posL k) = ColKind.reg)
    (hR : ∀ k, κ' (posR k) = ColKind.reg) (u : Tuple T' m) :
    (keyJoinCond posL posR hL hR).holdsPlain u
      ↔ ∀ k, u (posL k) = u (posR k) := by
  have hatom : ∀ k, (GenPredIn.cmp (c := 0) (κ := κ') CompOp.syneq
      (TermGIn.index (posL k) (hL k))
      (TermGIn.index (posR k) (hR k))).holdsPlain u ↔ u (posL k) = u (posR k) := by
    intro k
    show CompOp.syneq.eval3 (u (posL k)) (u (posR k)) = Kleene.true ↔ _
    rw [CompOp.syneq_eval3_eq_true_iff]
  unfold keyJoinCond
  rw [GenPredIn.holdsPlain_foldr_and]
  constructor
  · rintro ⟨hall, -⟩ k
    exact (hatom k).mp (hall k (List.mem_finRange k))
  · intro h
    refine ⟨fun k _ => (hatom k).mpr (h k), ?_⟩
    show CompOp.syneq.eval3 (0 : T') 0 = Kleene.true
    rw [CompOp.syneq_eval3_eq_true_iff]

/-- The join condition has no aggregate atom: it filters classically. -/
theorem keyJoinCond_hasAggAtom {T' : Type} [Zero T'] {n m : ℕ}
    {κ : Fin m → ColKind} (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ (posL k) = ColKind.reg)
    (hR : ∀ k, κ (posR k) = ColKind.reg) :
    (keyJoinCond (T' := T') posL posR hL hR).hasAggAtom = false := by
  unfold keyJoinCond
  induction List.finRange n with
  | nil => rfl
  | cons k l ih => simpa [GenPredIn.hasAggAtom] using ih

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenPredIn.holds_foldr_and {N : ℕ} {κ' : Fin N → ColKind} {α : Type}
    (l : List α) (f : α → GenPred T κ') (base : GenPred T κ')
    (u : Tuple (GenValue T K) N) :
    (((l.map f).foldr GenPredIn.and base).holds u)
      ↔ (∀ x ∈ l, (f x).holds u) ∧ base.holds u := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.foldr_cons, GenPredIn.holds_and, ih]
    constructor
    · rintro ⟨hhd, htl, hb⟩
      exact ⟨fun x hx => (List.mem_cons.mp hx).elim (fun he => he ▸ hhd)
        (htl x), hb⟩
    · rintro ⟨hall, hb⟩
      exact ⟨hall hd List.mem_cons_self,
        fun x hx => hall x (List.mem_cons_of_mem hd hx), hb⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- On a lifted tuple the join condition says what it says on the collapsed
one: its columns are regular, so no token is read. -/
theorem keyJoinCond_holds {n m : ℕ} {κ' : Fin m → ColKind}
    (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ' (posL k) = ColKind.reg)
    (hR : ∀ k, κ' (posR k) = ColKind.reg) (u : Tuple (GenValue T K) m) :
    (keyJoinCond posL posR hL hR).holds u
      ↔ ∀ k, GenRow.plainTuple u (posL k) = GenRow.plainTuple u (posR k) := by
  have hatom : ∀ k, (GenPredIn.cmp (c := 0) (κ := κ') CompOp.syneq
      (TermGIn.index (posL k) (hL k))
      (TermGIn.index (posR k) (hR k))).holds u
      ↔ GenRow.plainTuple u (posL k) = GenRow.plainTuple u (posR k) := by
    intro k
    show CompOp.syneq.eval3 (GenRow.plainTuple u (posL k))
      (GenRow.plainTuple u (posR k)) = Kleene.true ↔ _
    rw [CompOp.syneq_eval3_eq_true_iff]
  unfold keyJoinCond
  rw [GenPredIn.holds_foldr_and]
  constructor
  · rintro ⟨hall, -⟩ k
    exact (hatom k).mp (hall k (List.mem_finRange k))
  · intro h
    refine ⟨fun k _ => (hatom k).mpr (h k), ?_⟩
    show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true
    rw [CompOp.syneq_eval3_eq_true_iff]

/-- Kind transport is transparent to evaluation (row types do not mention
the kind vector). -/
theorem AggQueryIn.evaluate_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    (h : κ = κ') (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K)
    {γ : Fin c → T} :
    (q.castKind h).evaluate d γ = q.evaluate d γ := by
  subst h; rfl

/-- The kind vector of a `Gamma` output: key columns then token columns. -/
abbrev ColKind.gammaKinds (n₁ n₂ : ℕ) : Fin (n₁ + n₂) → ColKind :=
  Fin.append (fun _ : Fin n₁ => ColKind.reg) (fun _ : Fin n₂ => ColKind.agg)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Kind transport is transparent to plain evaluation too. -/
theorem AggQueryIn.evaluatePlain_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    (h : κ = κ') (q : AggQueryIn T c n κ) (d : Database T)
    {γ : Fin c → T} :
    (q.castKind h).evaluatePlain d γ = q.evaluatePlain d γ := by
  subst h; rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- The token lists of a row with a single token, in its last column: the
one token's occurrence annotations. -/
theorem tokenLists_snoc {n : ℕ} (u : Tuple T n) (a : AggValue T K) :
    tokenLists (Fin.snoc (fun k => (Sum.inl (u k) : GenValue T K))
        (Sum.inr a) : Tuple (GenValue T K) (n + 1))
      = {a.occs.map Prod.snd} := by
  unfold tokenLists
  rw [Fin.univ_castSuccEmb]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

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
theorem AggQueryIn.evaluate_conform :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (d : AnnotatedDatabase T K) {γ : Fin c → T} (r : GenRow T K n),
      r ∈ q.evaluate d γ → ∀ k, GenValue.kindOf (r.fst k) = (κ k).base := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    cases hf : d.find n s with
    | none => rw [hf] at hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      rw [hf] at hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      rfl
  | Proj ps q ih =>
    intro d γ r hr j
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
    cases hp : ps j with
    | term t => simp [ProjColIn.eval, hp, ProjColIn.kind, GenValue.kindOf,
        ColKind.base]
    | provTerm t => simp [ProjColIn.eval, hp, ProjColIn.kind, GenValue.kindOf,
        ColKind.base]
    | token k hk =>
      have := ih d r₀ hr₀ k
      rw [hk] at this
      simp only [ProjColIn.eval, hp, ProjColIn.kind]
      cases hu : r₀.fst k with
      | inl v =>
        rw [hu] at this
        exact absurd this (by simp [GenValue.kindOf, ColKind.base])
      | inr a => rfl
    | aggTerm k hk gf =>
      have := ih d r₀ hr₀ k
      rw [hk] at this
      simp only [ProjColIn.eval, hp, ProjColIn.kind]
      cases hu : r₀.fst k with
      | inl v =>
        rw [hu] at this
        exact absurd this (by simp [GenValue.kindOf, ColKind.base])
      | inr a => rfl
  | Sel φ q ih =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      exact ih d r₀ hr₀ k
    · rw [ite_eq_right hφ] at hr
      exact ih d r (Multiset.mem_of_mem_filter hr) k
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Multiset.mem_map.mp hr
    have hx := Multiset.mem_product.mp hxy
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact (congrArg GenValue.kindOf (Fin.append_left x.fst y.fst i)).trans
        ((ih₁ d x hx.left i).trans
          (congrArg ColKind.base (Fin.append_left _ _ i).symm))
    · exact (congrArg GenValue.kindOf (Fin.append_right x.fst y.fst j)).trans
        ((ih₂ d y hx.right j).trans
          (congrArg ColKind.base (Fin.append_right _ _ j).symm))
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hx, hr⟩ := Multiset.mem_bind.mp hr
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact (congrArg GenValue.kindOf (Fin.append_left x.fst y.fst i)).trans
        ((ih₁ d x hx i).trans
          (congrArg ColKind.base (Fin.append_left _ _ i).symm))
    · exact (congrArg GenValue.kindOf (Fin.append_right x.fst y.fst j)).trans
        ((ih₂ d y hy j).trans
          (congrArg ColKind.base (Fin.append_right _ _ j).symm))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.mp hr with h | h
    · exact ih₁ d r h k
    · exact ih₂ d r h k
  | Dedup q ih =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Gamma is ts fs q ih =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · exact (congrArg GenValue.kindOf
        (Fin.append_left (fun k => (Sum.inl (kv.fst k) : GenValue T K))
          (fun j' => (Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              (Multiset.map GenRow.toAnnotated (q.evaluate d γ)) kv.fst) γ)
            : GenValue T K)) i)).trans
        (congrArg ColKind.base
          (Fin.append_left (fun _ => ColKind.reg)
            (fun _ => ColKind.agg) i).symm)
    · exact (congrArg GenValue.kindOf
        (Fin.append_right (fun k => (Sum.inl (kv.fst k) : GenValue T K))
          (fun j' => (Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              (Multiset.map GenRow.toAnnotated (q.evaluate d γ)) kv.fst) γ)
            : GenValue T K)) j)).trans
        (congrArg ColKind.base
          (Fin.append_right (fun _ => ColKind.reg)
            (fun _ => ColKind.agg) j).symm)
  | ProvSum is his t q ih =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · dsimp only
      rw [Fin.append_left, Fin.append_left]
      exact (ColKind.base_eq_reg_of_ne_agg (his i)).symm
    · dsimp only
      rw [Fin.append_right, Fin.append_right]
      rfl
  | Retag h q ih =>
    intro d γ r hr k
    exact (ih d r hr k).trans (congrArg id (h k))
  | GammaScalar ts fs q ih =>
    -- one row, every column a token
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    rw [Multiset.mem_singleton] at hr
    subst hr
    rfl
  | GammaTok is his ts fs a q ih =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
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
  | Win P O o w t f q ih =>
    intro d γ r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · dsimp only
      rw [Fin.snoc_last, Fin.snoc_last]
      rfl
    · dsimp only
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl
