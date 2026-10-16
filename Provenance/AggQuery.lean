/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Order.Lattice.Nat
import Provenance.AggExpr
import Provenance.Nested
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


/-- A lifted column value: a regular value or an aggregate token, the
token being an ordinary one or a nested one (`AggTok`). -/
abbrev GenValue (T K : Type) := T ⊕ AggTok T K

/-- The deterministic reading of a lifted value. -/
def GenValue.collapse : GenValue T K → T :=
  Sum.elim id AggTok.collapse

/-- **How a lifted value is read as the inner reading of a nested
aggregation**: an aggregate expression is itself – a term over several
aggregate columns is one, and `sec:aggcols` reads it as such – an
ordinary token is the expression of itself (`AggExpr.ofValue`), and a
regular value reads no occurrence and returns itself
(`NestedValue.constInner`), so that aggregating a regular column nests
nothing. A *nested* column is read through its collapse: a second level
of nesting is what resolution takes innermost first, and this is the
total modeling semantics `GammaTok` is given too. -/
def GenValue.innerValue : GenValue T K → AggExpr T K
  | Sum.inl v => NestedValue.constInner v
  | Sum.inr (AggTok.tok a) => AggExpr.ofValue a
  | Sum.inr (AggTok.nest a) => NestedValue.constInner a.collapse
  | Sum.inr (AggTok.expr e) => e

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- **The inner reading of a pushed-forward column is the pushforward of
its inner reading**: the reading is built out of the column's own family,
and the pushforward moves the annotations through it. -/
@[simp] theorem GenValue.innerValue_mapAnnSum {K' : Type} (hm : K → K')
    (x : GenValue T K) :
    GenValue.innerValue (AggValue.mapAnnSum hm x)
      = (GenValue.innerValue x).mapAnn hm := by
  cases x with
  | inl v => rfl
  | inr y =>
    cases y with
    | tok a =>
      show AggExpr.ofValue (a.mapAnn hm) = (AggExpr.ofValue a).mapAnn hm
      unfold AggExpr.ofValue AggExpr.mapAnn AggValue.mapAnn
      simp only [AggExpr.mk.injEq, heq_eq_eq, true_and, and_true]
      rw [List.map_map, List.map_map]
      rfl
    | nest b =>
      show NestedValue.constInner (NestedValue.collapse (b.mapAnn hm)) = _
      rw [show NestedValue.collapse (b.mapAnn hm) = b.collapse from by
        show (b.mapAnn hm).agg _ = _
        refine congrArg b.agg ?_
        show (b.occs.map (fun o => (o.fst.mapAnn hm, hm o.snd))).map
            (fun o => o.fst.collapse) = _
        rw [Multiset.map_map]
        exact Multiset.map_congr rfl
          (fun o _ => AggExpr.collapse_mapAnn hm o.1)]
      rfl
    | expr e => rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- **The inner value of a lifted value collapses to its collapse**: the
deterministic reading does not see the nesting. -/
@[simp] theorem NestedValue.collapse_innerValue (x : GenValue T K) :
    (GenValue.innerValue x).collapse = AggValue.collapseSum x := by
  cases x with
  | inl v =>
    show (NestedValue.constInner v).collapse = v
    rw [NestedValue.constInner, AggExpr.collapse_ofValue]
    rfl
  | inr x =>
    cases x with
    | tok a => exact AggExpr.collapse_ofValue a
    | nest b =>
      show (NestedValue.constInner b.collapse).collapse = b.collapse
      rw [NestedValue.constInner, AggExpr.collapse_ofValue]
      rfl
    | expr e => rfl

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

/-! ### The worlds a predicate is read in

A predicate reading aggregate values is read in every world of the
families they read, one world per family: values of one family share
their occurrences and are read in one world, values of different
families in independent ones. A world of a joint reading carries the
product of its present annotations, the sum of its absent ones – the
monus is taken once, over all the families – and the value each compared
column takes there. -/

namespace AggTok

/-- **The value as an aggregate expression over its occurrence family**:
an ordinary token is the one-leaf expression, an expression is itself.
A nested value is read through its own worlds and never here. -/
def flatExpr : AggTok T K → AggExpr T K
  | .tok a => AggExpr.ofValue a
  | .expr e => e
  | .nest a => AggExpr.ofValue ⟨fun _ => a.collapse, [], true, a.fam⟩

end AggTok

/-- A subfamily of one listing of a family read in another: the positions
with the same index. -/
def trW {a b : ℕ} (W : Finset (Fin a)) : Finset (Fin b) :=
  Finset.univ.filter (fun i => ∃ j ∈ W, (j : ℕ) = i)

section JointWorlds

variable {n : ℕ}

/-- Whether a subfamily of a flat family is a world of every value of it
the columns `M` hold. -/
def flatOk (u : Tuple (GenValue T K) n) (M : List (Fin n)) {m : ℕ} (W : Finset (Fin m)) :
    Bool :=
  M.all (fun k => match u k with
    | Sum.inr y => decide (y.flatExpr.IsWorld (trW W))
    | _ => true)

/-- Whether a world of a nested family is a world of every nested value
the columns `M` hold. -/
def nestOk (u : Tuple (GenValue T K) n) (M : List (Fin n)) (W : NestedValue.World T K) :
    Bool :=
  M.all (fun k => match u k with
    | Sum.inr (.nest b) => decide (W.IsWorld b)
    | _ => true)

/-- **The worlds of one family**, read at the columns `M` of the row that
hold its values: per world, the product of the present annotations, the
sum of the absent ones, and the value of each of those columns. The
family is listed by the first of them, `x₀`; a world is one every value
of the family accepts – one meeting the group of each grouped value. -/
def classWorlds (u : Tuple (GenValue T K) n) (M : List (Fin n)) :
    AggTok T K → Multiset (K × K × (Fin n → Option T))
  | .nest a =>
    (a.worlds.filter (fun W => nestOk u M W = true)).map
      (fun W => (W.presentProd, W.absentSum, fun k => if k ∈ M then
        (match u k with
          | Sum.inr (.nest b) => some (b.valOn W)
          | _ => none) else none))
  | x =>
    ((Finset.univ : Finset (Finset (Fin x.flatExpr.occs.length))).filter
        (fun W => flatOk u M W = true)).val.map
      (fun W => (∏ i ∈ W, x.flatExpr.anns i, ∑ i ∈ Wᶜ, x.flatExpr.anns i,
        fun k => if k ∈ M then
          (match u k with
            | Sum.inr y => some (y.flatExpr.valOn (trW W))
            | _ => none) else none))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem flatOk_iff (u : Tuple (GenValue T K) n) (M : List (Fin n)) {m : ℕ} (W : Finset (Fin m)) :
    flatOk u M W = true ↔ ∀ k ∈ M, ∀ y, u k = Sum.inr y → y.flatExpr.IsWorld (trW W) := by
  unfold flatOk
  rw [List.all_eq_true]
  refine forall₂_congr fun k _ => ?_
  cases u k with
  | inl w => simp
  | inr y => simp

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem nestOk_iff (u : Tuple (GenValue T K) n) (M : List (Fin n)) (W : NestedValue.World T K) :
    nestOk u M W = true ↔ ∀ k ∈ M, ∀ b, u k = Sum.inr (.nest b) → W.IsWorld b := by
  unfold nestOk
  rw [List.all_eq_true]
  refine forall₂_congr fun k _ => ?_
  rcases u k with w | y
  · simp
  · cases y <;> simp

/-- The aggregate columns among `cols`, with their values. -/
def tokCols (u : Tuple (GenValue T K) n) (cols : List (Fin n)) : List (Fin n × AggTok T K) :=
  cols.filterMap (fun k => match u k with
    | Sum.inr x => some (k, x)
    | Sum.inl _ => none)

/-- Two joint worlds read together: products multiply, absent sums add,
and each column takes its value from the one that gives it one. -/
def combineW (w₁ w₂ : K × K × (Fin n → Option T)) : K × K × (Fin n → Option T) :=
  (w₁.1 * w₂.1, w₁.2.1 + w₂.2.1, fun k => (w₁.2.2 k).or (w₂.2.2 k))

/-- **What groups two values of a row into one family of a joint
reading**: the family they were stamped with, together with their
occurrence annotations and kind. Tokens of one family produced by one
evaluation carry the same occurrences, so in a query whose operators bear distinct
labels this is the family; the occurrences' annotations (and, for a
nested value, its occurrences themselves) are part of the key so that
the reading is defined on every row, a family being read in the worlds of
the occurrences its members actually carry. -/
def AggTok.classKey (x : AggTok T K) :
    FamId T × List K × Option (Multiset (AggExpr T K × K)) :=
  (x.fam, x.annList, match x with
    | .nest a => some a.occs
    | _ => none)

open Classical in
/-- **The joint worlds of the columns `cols` of a row**: one world of each
family they hold. -/
noncomputable def jointWorlds (u : Tuple (GenValue T K) n) (cols : List (Fin n)) :
    Multiset (K × K × (Fin n → Option T)) :=
  ((tokCols u cols).map (fun p => p.2.classKey)).dedup.foldr
    (fun φ acc =>
      match (tokCols u cols).find? (fun p => p.2.classKey = φ) with
      | none => acc
      | some p₀ =>
        ((classWorlds u (((tokCols u cols).filter (fun p => p.2.classKey = φ)).map Prod.fst) p₀.2)
          ×ˢ acc).map (fun w => combineW w.1 w.2))
    {(1, 0, fun _ => none)}

theorem trW_self {m : ℕ} (W : Finset (Fin m)) : trW (a := m) (b := m) W = W := by
  ext i
  simp only [trW, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hji⟩
    rwa [show j = i from Fin.ext hji] at hj
  · exact fun h => ⟨i, h, rfl⟩

omit [HasAltLinearOrder K] in
theorem classWorlds_sum_single {n : ℕ} (u : Tuple (GenValue T K) n) (k : Fin n) (x : AggTok T K)
    (hu : u k = Sum.inr x) (P : T → Kleene) :
    ((classWorlds u [k] x).map (fun w => w.1 * (1 - w.2.1) *
      (w.2.2 k).elim (0 : K) (Having.chiOf P))).sum
      = x.predProvOfWith P := by
  have hflat : ∀ e : AggExpr T K, ((((Finset.univ : Finset (Finset (Fin e.occs.length))).filter
      (fun W => e.IsWorld W)).val).map (fun W => (∏ i ∈ W, e.anns i) * (1 - ∑ i ∈ Wᶜ, e.anns i) *
        Having.chiOf P (e.valOn W))).sum = e.predProvWith P := by
    intro e
    unfold AggExpr.predProvWith
    rw [Finset.sum_eq_multiset_sum]
    congr 2
  cases x with
  | nest a =>
    simp only [classWorlds, nestOk, List.all_cons, List.all_nil, Bool.and_true,
      decide_eq_true_eq, hu, List.mem_singleton, Multiset.map_map,
      Function.comp_def, ite_true]
    show _ = NestedValue.predProvWith a P
    unfold NestedValue.predProvWith
    congr 2
  | tok a =>
    simp only [classWorlds, flatOk, List.all_cons, List.all_nil, Bool.and_true,
      decide_eq_true_eq, hu, List.mem_singleton, Multiset.map_map,
      Function.comp_def, ite_true, trW_self]
    rw [AggTok.predProvOfWith_tok, ← AggExpr.predProvWith_ofValue, ← hflat]
    congr 2
  | expr e =>
    simp only [classWorlds, flatOk, List.all_cons, List.all_nil, Bool.and_true,
      decide_eq_true_eq, hu, List.mem_singleton, Multiset.map_map,
      Function.comp_def, ite_true, trW_self]
    show _ = e.predProvWith P
    rw [← hflat]
    congr 2

end JointWorlds

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

omit [HasAltLinearOrder K] in
/-- **The structural rule makes a chain of selections and one selection
on the conjunction agree.** `Sel ψ₁ (Sel ψ₂ q)` multiplies the two
predicates' structural provenances into the row's concrete part one
after the other, and `Sel (ψ₁ ∧ ψ₂) q` multiplies their product in one
go, so in a commutative `K` the two spellings give the same concrete
part. Under the joint reading they need not: there the conjunction is
one sum over the worlds of the union while the chain is still a
product, so the two spellings agree exactly where the conjunction
decomposes (`Having.sum_mul_sum_of_overlap`) and part where it does
not – over `ℕ` on a single family, `4` against `2`
(`natRangeToken_mul_ne_and`). Whether a chain of selections over one
family is read as one predicate is therefore not a free choice once the
joint reading is the definition: it is the same question as whether the
decomposition is licensed. -/
theorem predsem_and (φ ψ : GenPredIn T c κ) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T) :
    (GenPredIn.and φ ψ).predsem false u γ
      = φ.predsem false u γ * ψ.predsem false u γ := rfl

omit [HasAltLinearOrder K] in
/-- The disjunction's structural rule, named rather than unfolded for
the same reason: it is `⊕`, and `bool_or_ne_joint` and `nat_or_ne_joint`
say it is not the joint reading. -/
theorem predsem_or (φ ψ : GenPredIn T c κ) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T) :
    (GenPredIn.or φ ψ).predsem false u γ
      = φ.predsem false u γ + ψ.predsem false u γ := rfl

/-- The token columns compared by the predicate's aggregate atoms. -/
def comparedCols : GenPredIn T c κ → Finset (Fin n)
  | cmp _ _ _ => ∅
  | aggCmp k _ _ _ => {k}
  | aggRange k _ _ _ _ _ => {k}
  | and φ ψ | or φ ψ => φ.comparedCols ∪ ψ.comparedCols
  | not φ => φ.comparedCols


/-- The predicate's truth when each compared column takes the value `v`
gives it. -/
def eval3W (φ : GenPredIn T c κ) (v : Fin n → Option T) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T) : Kleene :=
  match φ with
  | cmp op t₁ t₂ => op.eval3 (t₁.eval u γ) (t₂.eval u γ)
  | aggCmp k _ op t => (v k).elim Kleene.unknown (fun a => op.eval3 a (t.eval u γ))
  | aggRange k _ op₁ t₁ op₂ t₂ => (v k).elim Kleene.unknown
      (fun a => (op₁.eval3 a (t₁.eval u γ)).and (op₂.eval3 a (t₂.eval u γ)))
  | and φ ψ => (φ.eval3W v u γ).and (ψ.eval3W v u γ)
  | or φ ψ => (φ.eval3W v u γ).or (ψ.eval3W v u γ)
  | not φ => (φ.eval3W v u γ).not

/-- **The joint predicate provenance**: over the joint worlds of the
families the predicate reads, the world's annotation times the truth of
the predicate there (its falsity under `neg`). -/
noncomputable def predsemJ (φ : GenPredIn T c κ) (neg : Bool) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T) : K :=
  ((jointWorlds u ((List.finRange n).filter (· ∈ φ.comparedCols))).map
    (fun w => w.1 * (1 - w.2.1) *
      (if φ.eval3W w.2.2 u γ = (if neg then Kleene.false else Kleene.true) then 1 else 0))).sum

theorem filter_finRange_singleton (k : Fin n) :
    (List.finRange n).filter (· ∈ ({k} : Finset (Fin n))) = [k] := by
  have h : (List.finRange n).filter (· ∈ ({k} : Finset (Fin n)))
      = (List.finRange n).filter (fun x => x == k) := by
    congr 1; funext x; simp only [Finset.mem_singleton]; rfl
  rw [h, List.filter_beq, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange k)]
  rfl

omit [HasAltLinearOrder K] in
theorem jointWorlds_single (u : Tuple (GenValue T K) n) (k : Fin n) (x : AggTok T K)
    (hu : u k = Sum.inr x) :
    jointWorlds u [k] = (classWorlds u [k] x).map (fun w => combineW w (1, 0, fun _ => none)) := by
  have ht : tokCols u [k] = [(k, x)] := by simp [tokCols, hu]
  unfold jointWorlds
  rw [ht]
  simp only [List.map_cons, List.map_nil, List.dedup_cons_of_notMem List.not_mem_nil,
    List.dedup_nil, List.foldr_cons, List.foldr_nil, List.find?_cons, decide_true,
    List.filter_cons, List.filter_nil,
    ite_true, List.map_cons, List.map_nil]
  rw [← Multiset.cons_zero, Multiset.product_cons, Multiset.product_zero, add_zero,
    Multiset.map_map]
  rfl

omit [HasAltLinearOrder K] in
theorem predsemJ_aggCmp (k : Fin n) (h : κ k = ColKind.agg) (op : CompOp) (t : TermGIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin c → T) (x : AggTok T K) (hu : u k = Sum.inr x)
    (neg : Bool) :
    (aggCmp k h op t).predsemJ neg u γ
      = x.predProvOf (if neg then op.negate else op) (t.eval u γ) := by
  unfold predsemJ
  rw [show (aggCmp k h op t : GenPredIn T c κ).comparedCols = {k} from rfl,
    filter_finRange_singleton, jointWorlds_single u k x hu, Multiset.map_map]
  rw [AggTok.predProvOf, ← classWorlds_sum_single u k x hu]
  congr 1
  refine Multiset.map_congr rfl (fun w _ => ?_)
  simp only [Function.comp_apply, combineW, mul_one, add_zero, Option.or_none, eval3W]
  obtain ⟨p, sa, v⟩ := w
  dsimp only
  rcases Option.eq_none_or_eq_some (v k) with hv | ⟨a, hv⟩ <;> simp only [hv, Option.elim] <;>
    cases neg <;> simp [Having.chiOf]


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

/-- **The function a term over one variable computes.** A column that
reads an aggregate column reads it through a term, as `sec:aggexpr` has
it – "`g` is the function the term computes" – and this is that
function. -/
def TermIn.unary (t : TermIn T 1 0) : T → T :=
  fun x => t.eval (fun j => j.elim0) (fun _ => x)

/-- **A unary term reading a column**: the same term with the column in
place of its variable. It is how a term over an aggregate column re-types
– read on the column as a regular one – and `TermIn.evalPlain_atCol`
says the two compute the same value. -/
def TermIn.atCol {c k : ℕ} {κ : Fin k → ColKind} (i : Fin k)
    (h : κ i = ColKind.reg) : TermIn T 1 0 → TermGIn T c κ
  | .const a => .const a
  | .outer _ => .index i h
  | .index j => j.elim0
  | .add t₁ t₂ => .add (t₁.atCol i h) (t₂.atCol i h)
  | .sub t₁ t₂ => .sub (t₁.atCol i h) (t₂.atCol i h)
  | .mul t₁ t₂ => .mul (t₁.atCol i h) (t₂.atCol i h)
  | .caseWhen op t₁ t₂ t₃ t₄ =>
      .caseWhen op (t₁.atCol i h) (t₂.atCol i h) (t₃.atCol i h) (t₄.atCol i h)
  | .coalesce t₁ t₂ => .coalesce (t₁.atCol i h) (t₂.atCol i h)

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
  /-- **A term over one aggregate column**, which is the shape the source
  language has: the column the term names, read through a term of the
  language, `TermIn.unary` being the function it computes. `sec:aggexpr`
  reads such a column as "a term that mentions a column of aggregate
  kind", with `g` the function the term computes, so this is the
  document's column and `aggTerm` is wider. Being a term, it re-types
  like any other column: the same term reads a regular column. -/
  | aggTermOf : (k : Fin n) → κ k = ColKind.agg → TermIn T 1 0 →
      ProjColIn T c κ
  | provTerm : TermGIn T c κ → ProjColIn T c κ

/-- **Whether a column is one the source language writes.** Every column
is, except the one carrying an arbitrary function of an aggregate column:
that one belongs to the rewritten world, where the cast of a column has
to act on the data arm of a composite value and leave the annotation arm
alone. `AggQueryIn.usesOnly` asks for it, as it asks a query to be free
of the other operators of that world. -/
def ProjColIn.sourceCol {c : ℕ} {κ : Fin n → ColKind} :
    ProjColIn T c κ → Bool
  | .term _ => true
  | .token _ _ => true
  | .aggTerm _ _ _ => false
  | .aggTermOf _ _ _ => true
  | .provTerm _ => true

/-- A projection column of a closed query. -/
abbrev ProjCol (T : Type) {n : ℕ} (κ : Fin n → ColKind) := ProjColIn T 0 κ

/-- The kind of the output column. -/
def ProjColIn.kind {c : ℕ} {κ : Fin n → ColKind} : ProjColIn T c κ → ColKind
  | term _ => ColKind.reg
  | token _ _ => ColKind.agg
  | aggTerm _ _ _ => ColKind.agg
  | aggTermOf _ _ _ => ColKind.agg
  | provTerm _ => ColKind.prov

/-- Evaluation of a projection column on a lifted tuple. -/
def ProjColIn.eval {c : ℕ} {κ : Fin n → ColKind} (p : ProjColIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin c → T := fun _ => 0) :
    GenValue T K :=
  match p with
  | term t => Sum.inl (t.eval u γ)
  | token k _ => u k
  | aggTerm k _ gf => Sum.map gf (AggTok.postcomp gf) (u k)
  | aggTermOf k _ t => Sum.map t.unary (AggTok.postcomp t.unary) (u k)
  | provTerm t => Sum.inl (t.eval u γ)

/-! ## An `ORDER BY` inside an aggregation

SQL writes one inside the aggregate – `array_agg(x ORDER BY y)`,
`string_agg`, the ordered-set aggregates – and a *symmetric* aggregate
does not need it: `count` and `sum` read the same value whichever order
their group comes in. `GroupOrder.unord` says there is no clause, and
then the group is read in the domain's canonical order, which is what
every aggregation of this library did before the clause existed. -/

/-- **The order an aggregate reads its group in.** A clause's ties are
broken by the row, as a window's are (`OrderSpec.readLe`), so the
sequence is a function of the group and not of any listing of it. -/
inductive GroupOrder (T : Type) (m : ℕ) where
  /-- No clause: the group is read in the domain's canonical order. -/
  | unord : GroupOrder T m
  /-- The group is read in the clause `spec` on the columns `cols`. -/
  | byCols {p : ℕ} (cols : Tuple (Fin m) p) (spec : OrderSpec p) :
      GroupOrder T m

/-- **The rows of a group in the order its aggregate reads them.** -/
def Relation.groupSeqOrd {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : Relation T m) (g : Tuple T n₁) :
    List (Tuple T m) :=
  match ord with
  | .unord => Relation.groupSeq is r g
  | .byCols cols spec =>
      OrderSpec.sortSeq (Tuple.key cols) (id : Tuple T m → Tuple T m) spec
        (Relation.groupSeq is r g)

@[simp] theorem Relation.groupSeqOrd_unord {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (r : Relation T m) (g : Tuple T n₁) :
    Relation.groupSeqOrd is GroupOrder.unord r g = Relation.groupSeq is r g :=
  rfl

/-- Reading a group in a clause's order is reading a listing of it: the
rows are the same, in another order. -/
theorem Relation.groupSeqOrd_perm {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : Relation T m) (g : Tuple T n₁) :
    (Relation.groupSeqOrd is ord r g).Perm (Relation.groupSeq is r g) := by
  cases ord with
  | unord => exact List.Perm.refl _
  | byCols cols spec => exact OrderSpec.sortSeq_perm _

/-- **The same, cut by a `FILTER` clause** where the aggregate carries
one: the clause cuts what the aggregate reads, and the order is the
aggregate's own. -/
def Relation.groupSeqOptOrd {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : Relation T m) (g : Tuple T n₁)
    (keep : Option (Selection T m)) : List (Tuple T m) :=
  match keep with
  | none => Relation.groupSeqOrd is ord r g
  | some φ => (Relation.groupSeqOrd is ord r g).filter φ.keeps

@[simp] theorem Relation.groupSeqOptOrd_unord {m n₁ : ℕ}
    (is : Tuple (Fin m) n₁) (r : Relation T m) (g : Tuple T n₁)
    (keep : Option (Selection T m)) :
    Relation.groupSeqOptOrd is GroupOrder.unord r g keep
      = Relation.groupSeqOpt is r g keep := by
  cases keep <;> rfl

@[simp] theorem Relation.groupSeqOptOrd_none {m n₁ : ℕ}
    (is : Tuple (Fin m) n₁) (ord : GroupOrder T m) (r : Relation T m)
    (g : Tuple T n₁) :
    Relation.groupSeqOptOrd is ord r g none = Relation.groupSeqOrd is ord r g :=
  rfl

/-- **The annotated group in the order its aggregate reads it**: the
occurrence sequence a token is built over. The clause reads the data
columns, so it moves no annotation between occurrences carrying
different rows. -/
def Having.havingGroupOrd {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    List (AnnotatedTuple T K m) :=
  match ord with
  | .unord => Having.havingGroup is r g
  | .byCols cols spec =>
      OrderSpec.sortSeq (Tuple.key cols)
        (Prod.fst : AnnotatedTuple T K m → Tuple T m) spec
        (Having.havingGroup is r g)

omit [CommSemiringWithMonus K] [DecidableEq K] in
@[simp] theorem Having.havingGroupOrd_unord {m n₁ : ℕ}
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    Having.havingGroupOrd is GroupOrder.unord r g = Having.havingGroup is r g :=
  rfl

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The ordered reading is a listing of the group. -/
theorem Having.havingGroupOrd_perm {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    (Having.havingGroupOrd is ord r g).Perm (Having.havingGroup is r g) := by
  cases ord with
  | unord => exact List.Perm.refl _
  | byCols cols spec => exact OrderSpec.sortSeq_perm _

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- An occurrence of the group is one of its ordered reading. -/
@[simp] theorem Having.mem_havingGroupOrd {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (ord : GroupOrder T m) (r : AnnotatedRelation T K m) (g : Tuple T n₁)
    (x : AnnotatedTuple T K m) :
    x ∈ Having.havingGroupOrd is ord r g ↔ x ∈ Having.havingGroup is r g :=
  (Having.havingGroupOrd_perm is ord r g).mem_iff

/-! ## Kind-indexed queries -/

/-- The all-regular kind vector. -/
def ColKind.allReg (n : ℕ) : Fin n → ColKind := fun _ => ColKind.reg

/-- **A term reads regular columns only.** An aggregate column holds a
token, and a plain term reading one would read it through its
deterministic collapse – the value SQL prints for it, but not what it
reads in a given world. A window asks this of its aggregate term
(`WinReadsReg`); the way to read an aggregate column *as a value* is
`AggQueryIn.Explode`, which turns it into a regular one. -/
def TermIn.regOnly {c n : ℕ} (κ : Fin n → ColKind) : TermIn T c n → Bool
  | .const _ => true
  | .outer _ => true
  | .index k => (κ k).base == ColKind.reg
  | .add t₁ t₂ => t₁.regOnly κ && t₂.regOnly κ
  | .sub t₁ t₂ => t₁.regOnly κ && t₂.regOnly κ
  | .mul t₁ t₂ => t₁.regOnly κ && t₂.regOnly κ
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      t₁.regOnly κ && t₂.regOnly κ && t₃.regOnly κ && t₄.regOnly κ
  | .coalesce t₁ t₂ => t₁.regOnly κ && t₂.regOnly κ

omit [ValueType T] in
/-- Over all-regular columns the condition asks nothing. -/
@[simp] theorem TermIn.regOnly_allReg {c n : ℕ} (t : TermIn T c n) :
    t.regOnly (ColKind.allReg n) = true := by
  induction t with
  | const a => rfl
  | outer k => rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermIn.regOnly, ih₁, ih₂, Bool.and_self]
  | sub t₁ t₂ ih₁ ih₂ => rw [TermIn.regOnly, ih₁, ih₂, Bool.and_self]
  | mul t₁ t₂ ih₁ ih₂ => rw [TermIn.regOnly, ih₁, ih₂, Bool.and_self]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    rw [TermIn.regOnly, ih₁, ih₂, ih₃, ih₄, Bool.and_self, Bool.and_self,
      Bool.and_self]
  | coalesce t₁ t₂ ih₁ ih₂ => rw [TermIn.regOnly, ih₁, ih₂, Bool.and_self]

/-- **What a window may read of its input**: its `PARTITION BY`, its
`ORDER BY` and its aggregate term read regular columns only. An aggregate
column of the input – that of an earlier window of the same `SELECT`, say
– is carried through unchanged and read by nothing, the determinized peer
order included (`ColKind.readTuple`). That is what makes the column read
in a world what the plain window reads of that world: an aggregate column
can order two occurrences one way in one world and the other way in the
next, so a window that read one would not commute with the possible
worlds. Ordering or partitioning by an aggregate reads it as a key,
through `AggQueryIn.Explode`. -/
def WinReadsReg {c n m p : ℕ} (κ : Fin n → ColKind) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (t : TermIn T c n) : Prop :=
  (∀ k, (κ (P k)).base = ColKind.reg) ∧ (∀ k, (κ (O k)).base = ColKind.reg)
    ∧ t.regOnly κ = true

omit [ValueType T] in
/-- An all-regular input satisfies it with nothing to check. -/
theorem winReadsReg_allReg {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (t : TermIn T c n) :
    WinReadsReg (ColKind.allReg n) P O t :=
  ⟨fun _ => rfl, fun _ => rfl, TermIn.regOnly_allReg t⟩

/-! A multi-frame window (`AggQueryIn.WinExpr`) asks no such condition,
because its input is all-regular: its column is indexed by *occurrence*
rather than determined by the row, and an occurrence of the relation a
window reads does not determine the row it came from – two rows differing
only in an aggregate column read alike – so carrying an aggregate column
through one would need a canonical listing of general rows, which is an
order on `AggTok`. -/

/-- **What a selection on a recursive term asks of its predicate**: no
aggregate atom. On a closed query – no hole – it asks nothing, and
`trivial` discharges it, which is what lets a closed selection be
written without a proof. -/
def SelOK (l : List (String × ℕ)) {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) : Prop :=
  match l with
  | [] => True
  | _ :: _ => φ.hasAggAtom = false

omit [ValueType T] in
/-- A predicate with no aggregate atom is fine on any term. -/
theorem SelOK.of_noAggAtom {l : List (String × ℕ)} {c n : ℕ} {κ : Fin n → ColKind}
    {φ : GenPredIn T c κ} (h : φ.hasAggAtom = false) : SelOK l φ := by
  cases l with
  | nil => trivial
  | cons _ _ => exact h

omit [ValueType T] in
/-- The condition is read off the predicate's atoms only. -/
theorem SelOK.of_eq {l : List (String × ℕ)} {c n c' n' : ℕ} {κ : Fin n → ColKind}
    {κ' : Fin n' → ColKind} {φ : GenPredIn T c κ} {φ' : GenPredIn T c' κ'}
    (h : φ'.hasAggAtom = φ.hasAggAtom) (hφ : SelOK l φ) : SelOK l φ' := by
  cases l with
  | nil => trivial
  | cons _ _ => exact h.trans hφ

omit [ValueType T] in
theorem SelOK.noAggAtom {l : List (String × ℕ)} {c n : ℕ} {κ : Fin n → ColKind}
    {φ : GenPredIn T c κ} (hφ : SelOK l φ) (hl : l ≠ []) : φ.hasAggAtom = false := by
  cases l with
  | nil => exact absurd rfl hl
  | cons _ _ => exact hφ

omit [ValueType T] in
/-- A conjunction of two admissible predicates is admissible. -/
theorem SelOK.and {l : List (String × ℕ)} {c n : ℕ} {κ : Fin n → ColKind}
    {φ ψ : GenPredIn T c κ} (hφ : SelOK l φ) (hψ : SelOK l ψ) : SelOK l (.and φ ψ) := by
  cases l with
  | nil => trivial
  | cons _ _ =>
    show (φ.hasAggAtom || ψ.hasAggAtom) = false
    rw [show φ.hasAggAtom = false from hφ, show ψ.hasAggAtom = false from hψ]
    rfl

-- an aggregating operator's label names it; nothing in its type reads the label
set_option linter.unusedVariables false in
/-- Kind-indexed general queries. The index discipline enforces the
scope conditions: `Gamma` aggregates an all-regular input, `Dedup` and
`Diff` require all-regular kinds, and the projection/selection grammars
never compute over tokens. -/
inductive AggQueryIn (T : Type) : (c n : ℕ) → (Fin n → ColKind) →
    (l : List (String × ℕ) := []) → Type where
  /-- Base relation (all-regular). -/
  | Rel : {c : ℕ} → (n : ℕ) → String → AggQueryIn T c n (ColKind.allReg n)
  /-- **The recursive reference**: the relation name `s` of arity `n`
  bound by the enclosing recursion, which is the one hole a recursive
  term holds. The last index of the syntax lists a term's holes, so a
  closed query has none, a recursion's term has exactly this one, and
  the operators a hole may sit under are those whose typing passes the
  index through: a projection, a selection with no aggregate atom, either
  side of a product, the left side of an apply, either side of a union,
  the alternatives and a retagging. Everything else is closed. This is
  the restriction on recursive terms of `sec:plain`, in the type rather
  than beside it. -/
  | Hole : {c : ℕ} → (n : ℕ) → (s : String) → (κ : Fin n → ColKind := ColKind.allReg n) →
      AggQueryIn T c n κ [(s, n)]
  /-- **Parameters, as a relation**: one row annotated `𝟙`, column `k`
  being the parameter `pv k` of the context – or the constant it names –
  with kind `ρ k`. In the right side of an apply the context starts with
  the row of its left side, and an aggregate column of that row is here an
  aggregate value, with its occurrences, read as any aggregate column is:
  a token column of a projection, an aggregate atom of a selection, a
  nested aggregation's term. That is how the semantics reads an aggregate
  parameter, world by world; a term's `outer k` reads a parameter as a
  plain value, and only a non-aggregate one (`AggQueryIn.wellKinded`).
  The parameters are addressed by position, like `outer`, so the leaf
  substitutes as a term does. -/
  | Param : {c m : ℕ} → (pv : Fin m → T ⊕ Fin c) → (ρ : Fin m → ColKind) →
      AggQueryIn T c m ρ
  /-- **The empty relation of arity `0`**, empty on every instance. It is
  the one leaf that belongs to the *query* and not to the instance, which
  is what makes it the base of everything a query can build from nowhere:
  the unit relation is the scalar aggregation of it with no aggregate
  (`Derived.unit`, one empty tuple annotated `𝟙`, which is PostgreSQL's
  `SELECT;`), and SQL's `VALUES` is a union of projections of that onto
  constants (`Derived.values`). A constant relation therefore needs no
  leaf of its own, and this one needs no side condition: non-emptiness is
  a condition of the derived notation, not of the syntax.

  Keeping it at arity `0` is what leaves `GammaScalar` alone in its
  class: every other operator is empty on an empty instance, and the
  scalar aggregation is the one that emits a row regardless. -/
  | Empty : {c : ℕ} → AggQueryIn T c 0 (ColKind.allReg 0)
  /-- Generalized projection. -/
  | Proj : {c n m : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
      (ps : Tuple (ProjColIn T c κ) m) → AggQueryIn T c n κ l →
      AggQueryIn T c m (fun j => (ps j).kind) l
  /-- Generalized selection. On a recursive term – one with a hole – the
  predicate carries no aggregate atom, which the trailing proof says; on
  a closed query it says nothing, and the tactic finds it. -/
  | Sel : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
      (φ : GenPredIn T c κ) → AggQueryIn T c n κ l →
      (hφ : SelOK l φ := by first | trivial | assumption) →
      AggQueryIn T c n κ l
  /-- Cartesian product (join). -/
  | Prod : {c n₁ n₂ : ℕ} → {κ₁ : Fin n₁ → ColKind} → {κ₂ : Fin n₂ → ColKind} →
      {l₁ l₂ : List (String × ℕ)} →
      AggQueryIn T c n₁ κ₁ l₁ → AggQueryIn T c n₂ κ₂ l₂ →
      AggQueryIn T c (n₁ + n₂) (Fin.append κ₁ κ₂) (l₁ ++ l₂)
  /-- **Apply** – SQL's `LATERAL`, the operator of Galindo-Legaria and
  Joshi: a product whose right side is read once per row of the left and
  may read that row's columns. The right side's context is the left
  side's columns followed by the ambient outer ones, so in a closed
  apply the right side reads exactly the left arity. Its output pairs
  each row `u` of the left with each row of the right read at `u`, and
  multiplies their annotations.

  It is not derivable from the cross product once annotations are there:
  the product reads its right side once, the apply once per row of the
  left, and it is the apply that a correlated subquery needs.

  The left side may carry aggregate columns, so that a product of two
  token-carrying relations is an apply too. The right side reads such a
  column as the paper does, world by world: the left row's values, tokens
  included, are the context of the environment the evaluator carries
  (`EvalEnv`), and the leaf `AggQueryIn.Param` reads them into columns of
  the same kinds. A term reads a parameter as a plain value only where it
  is not aggregate (`AggQueryIn.wellKinded`). -/
  | Apply : {c n₁ n₂ : ℕ} → {κ₁ : Fin n₁ → ColKind} → {κ₂ : Fin n₂ → ColKind} →
      {l : List (String × ℕ)} →
      AggQueryIn T c n₁ κ₁ l →
      AggQueryIn T (n₁ + c) n₂ κ₂ →
      AggQueryIn T c (n₁ + n₂) (Fin.append κ₁ κ₂) l
  /-- Union (all). -/
  | Sum : {c n : ℕ} → {κ : Fin n → ColKind} → {l₁ l₂ : List (String × ℕ)} →
      AggQueryIn T c n κ l₁ → AggQueryIn T c n κ l₂ → AggQueryIn T c n κ (l₁ ++ l₂)
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

  The operator is **partial**: it means the sum of the rounds up to the
  first empty one, and means nothing where no round is empty
  (`MuSettles`). The evaluator is total and says `⨄_{i<n} Mᵢ` for that
  `n` where there is one, junk elsewhere, which is why every result about
  a recursion carries `AggQueryIn.recSettles`; a bounded computation
  witnesses the value through `AggQueryIn.evaluate_Mu_of_empty`. The
  round count is *not* part of the query: a recursion that stops at a
  count rather than at its own rounds is not this operator.

  The rows a round carries may hold aggregate columns, with their
  aggregate values: the annotated evaluator binds the round in an
  environment of general rows (`EvalEnv`), not in the database. The
  recursive term reads them as the restriction on it allows – carried by a
  projection, as a token or under a term (`aggTermOf`), but never compared,
  its selections reading regular columns only (`SelOK`). -/
  | Mu : {c n : ℕ} → {κ : Fin n → ColKind} → (s : String) →
      AggQueryIn T c n κ → AggQueryIn T c n κ [(s, n)] → AggQueryIn T c n κ
  /-- **Recursion up to duplicates**: SQL's `WITH RECURSIVE … UNION`.
  The least fixpoint the semantics says it is: `X₀` empty,
  `X_{j+1} = ⟦ε(q₀ ⊎ q₁)⟧_{d[s ↦ X_j]}` with annotations, and the query
  is `X_j` for the first `j` with `X_{j+1} = X_j`.

  **Partial**, like `Mu`: it means nothing where the rounds never settle
  (`MuSetSettles`), the evaluator says junk there, and results carry
  `AggQueryIn.recSettles`;
  `AggQueryIn.evaluate_MuSet_of_fix` turns a round that repeats into the
  value. It settles whenever no tuple has a derivation through itself,
  and in an absorptive semiring with such derivations too. -/
  | MuSet : {c n : ℕ} → (s : String) →
      AggQueryIn T c n (ColKind.allReg n) →
      AggQueryIn T c n (ColKind.allReg n) [(s, n)] →
      AggQueryIn T c n (ColKind.allReg n)
  /-- **Exploding an aggregate column: reading it as a key.** Every
  operator here that compares keys – `Dedup`, `Diff`, the grouping and
  partition indices – takes regular columns, so a query that groups on
  a count or deduplicates on an aggregate is written by first reading
  the column as a key: the occurrence is replaced by its alternatives,
  one per value the column takes, each carrying `[a ≐ v]`, and the
  column becomes regular (`GenRow.alternativesAt`). This is ProvSQL's
  `rewrite_explode_agg_value` (one row per value the aggregate takes
  over the possible worlds) and the semantics paper's reading of an
  aggregate column as a key, as against the reading as a value, which
  the aggregate atoms and terms have world by world and which needs no
  operator. Over a plain relation an aggregate value is a value and
  this is the identity – it is a typing device there, charged to no
  class by `usesOnly`; in the annotated semantics it is an operator of
  its own, out of the language the annotated classification is about
  (`noExplode`). -/
  | Explode : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} → (k : Fin n) →
      κ k = ColKind.agg → AggQueryIn T c n κ l →
      AggQueryIn T c n (Function.update κ k ColKind.reg) l
  /-- The decomposed grouping operator `γ^≼`: group the (all-regular)
  input by the key columns `is`; one output row per group, carrying the
  key followed by one aggregate token per `(term, aggregate)` pair.

  Each pair may carry a **`FILTER` clause**, `keep j`, which cuts what
  that aggregate *reads* of its group – and nothing else. A filtered
  aggregate's column is therefore an aggregate *expression* over the
  whole group (`AggExpr.ofGroupWhen`): the worlds are the group's
  non-empty subfamilies, as with no clause, every occurrence carrying its
  annotation to them, and the leaf reads `f []` in a world holding only
  rejected rows – the row SQL emits for a group all of whose rows the
  clause rejects. `none` is the aggregate with no clause, and the clause
  that keeps everything reads exactly as `none` does. The clause reads
  the group's input row and no outer column, as SQL's does.

  It reads **regular columns only**, and not by convention: SQL forbids
  an aggregate inside the `FILTER` of an aggregate, so a clause is a
  predicate of the plain value domain and not an atom over a token. Two
  consequences the metatheory lives off. Its truth at an occurrence is
  the same in every world, which is why no result here carries a
  hypothesis about what a clause reads – the worlds it cuts are the
  occurrence's own. And it is preserved by any transport that keeps the
  data columns, which is why the rewriting can carry a clause unchanged
  (`Selection.castToAnnotatedTuple`) with nothing to prove about it.

  Its `ord` is the `ORDER BY` *inside* the aggregates, which SQL writes
  as `array_agg(x ORDER BY y)`: the group is read in that clause's order
  rather than in the domain's canonical one, and `GroupOrder.unord` – the
  default – says there is no clause. A symmetric aggregate reads the same
  value either way; it is for `array_agg`, `string_agg` and the
  order-dependent picks that the clause is the aggregate's own. The
  group's occurrence sequence, its existence factor and the rewritten
  world's reading all follow it (`Having.havingGroupOrd`,
  `Relation.groupSeqOrd`). -/
  | Gamma : {c m n₁ n₂ : ℕ} → {lab : ℕ} →
      {rd : Fin c → Bool} →
      (is : Tuple (Fin m) n₁) → (ts : Tuple (TermIn T c m) n₂) →
      (fs : Tuple (SeqAggFunc T) n₂) → AggQueryIn T c m (ColKind.allReg m) →
      (keep : Fin n₂ → Option (Selection T m) := fun _ => none) →
      (ord : GroupOrder T m := GroupOrder.unord) →
      AggQueryIn T c (n₁ + n₂)
        (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg))
  /-- Aggregation without grouping: one output row whatever the input,
  its aggregates reading the whole of it.

  It is not `Gamma` with no keys. SQL forms a single group here that exists
  even over no row, so the row is annotated `𝟙` and carries no
  group-existence factor, and its tokens have the empty world among their
  worlds (`AggValue.ofScalarGroup`): an aggregate over an empty input has a
  value, and a comparison against it has to be given one. -/
  | GammaScalar : {c m n₂ : ℕ} → {lab : ℕ} →
      {rd : Fin c → Bool} →
      (ts : Tuple (TermIn T c m) n₂) → (fs : Tuple (SeqAggFunc T) n₂) →
      AggQueryIn T c m (ColKind.allReg m) →
      (ord : GroupOrder T m := GroupOrder.unord) →
      AggQueryIn T c n₂ (fun _ => ColKind.agg)
  /-- **Second-level aggregation** (`sec:aggcols`, "as values"): group by
  the key columns `is`, none of which may be an aggregate column, and
  aggregate the projection column `p` over each group under `f`. Because
  `p` may read an *aggregate* column, the token this builds is
  **nested**: its occurrences are the group's rows, and what each carries
  is the aggregate value read there rather than a value
  (`AggTok.nest`).

  Its occurrences are a **bag**. They carry tokens, which `≼` does not
  order – that order is an order on plain tuples – so there is no
  sequence for an order-dependent `f` to read, and the outer aggregate is
  a function of the bag. An order-dependent outer aggregate has no
  reading of this kind and needs none: it goes through `Explode`, after which
  the column read is regular and the aggregation is an ordinary `Gamma`.

  Where `p` reads a regular column the nesting degenerates – each
  occurrence carries an inner value that reads nothing
  (`GenValue.innerValue`) – and the token is `Gamma`'s own, read over the
  bag instead of over the `≼`-sorted sequence.

  One output token and not `n₂` of them: two nested values over one group
  read it as two families, which is the joint reading `AggExpr` gives an
  expression and not a product of two tokens. -/
  | GammaNest : {c m n₁ : ℕ} → {κ : Fin m → ColKind} → {lab : ℕ} →
      {rd : Fin c → Bool} →
      (is : Tuple (Fin m) n₁) → (his : ∀ k, κ (is k) ≠ ColKind.agg) →
      (p : ProjColIn T c κ) → (f : Multiset T → T) →
      AggQueryIn T c m κ →
      AggQueryIn T c (n₁ + 1)
        (Fin.append (fun k => κ (is k)) (fun _ : Fin 1 => ColKind.agg))
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
  | Retag : {c n : ℕ} → {κ κ' : Fin n → ColKind} → {l : List (String × ℕ)} →
      (h : ∀ k, (κ k).base = (κ' k).base) → AggQueryIn T c n κ l →
      AggQueryIn T c n κ' l
  /-- Token-building grouping (ProvSQL's `provsql_agg`): group by the
  key columns `is`, output the keys, one aggregate token per
  `(term, aggregate)` pair whose occurrence annotations are the values
  of the explicit annotation term `a` (in rewritten plans: the
  provenance column of the subquery), and a trailing `prov` column
  carrying the group-existence guard. Its faithful semantics lives in
  the rewritten world's evaluator; the generic evaluators give it total
  modeling semantics, and the world-faithfulness exclusions
  (`noProvSum`) rule it out of source queries.

  Its `keep` is the same clause as `AggQueryIn.Gamma`'s, read the same
  way: it cuts what an aggregate reads and leaves the family and the
  guard whole, so a filtered aggregate's column is an aggregate
  expression (`AggExpr.ofGroupWhen`) and not an ordinary token. The
  rewriting carries the source's clause into it unchanged
  (`Selection.castToAnnotatedTuple`), a clause asking the rewriting for
  no rule of its own.

  A clause over the rewritten schema could also compare the *provenance*
  column, which the transport never produces and which the semantics
  permits in one form only: as an evaluation of the annotation in `𝔹`
  whose result does not enter an annotation, the way the displayed-value
  aggregate reads the rows whose token holds under `hTop`. Anything else
  would be evaluating an annotation while building one. -/
  | GammaTok : {c m n₁ n₂ : ℕ} → {κ : Fin m → ColKind} → {lab : ℕ} →
      {rd : Fin c → Bool} →
      (is : Tuple (Fin m) n₁) → (his : ∀ k, κ (is k) ≠ ColKind.agg) →
      (ts : Tuple (TermIn T c m) n₂) → (fs : Tuple (SeqAggFunc T) n₂) →
      (a : TermGIn T c κ) → AggQueryIn T c m κ →
      (keep : Fin n₂ → Option (Selection T m) := fun _ => none) →
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
  `false`, so a window written without it means what it meant.

  **Its input need not be all-regular**, which is what a second window of
  one `SELECT` needs: `rank() OVER (…), avg(x) OVER (…)` is two windows,
  the second over a relation that already holds the first one's aggregate
  column. Such a column is carried through unchanged and read by nothing
  – `WinReadsReg` asks the partition, the order and the term to read
  regular columns, and `ColKind.readTuple` keeps an aggregate column out
  of the determinized peer order as well. Both halves are needed: an
  aggregate column can order two peers one way in one world and the other
  way in the next, so a window reading one would not commute with the
  possible worlds. Ordering or partitioning *by* an aggregate reads it as
  a key, through `AggQueryIn.Explode`. -/
  | Win : {c n m p : ℕ} → {κ : Fin n → ColKind} → {lab : ℕ} →
      {rd : Fin c → Bool} →
      (P : Tuple (Fin n) m) → (O : Tuple (Fin n) p) → (o : OrderSpec p) →
      (w : ValueFrame T p) →
      (t : TermIn T c n) → (f : SeqAggFunc T) →
      AggQueryIn T c n κ → WinReadsReg κ P O t → (dist : Bool := false) →
      (keep : Option (Selection T n) := none) →
      AggQueryIn T c (n + 1) (Fin.snoc κ ColKind.agg)
  /-- **A window over several frames of one partition**, whose column is
  an aggregate *expression* and not an aggregate: leaf `l` aggregates
  `ts l` with `fs l` over the frame `ws l`, and `g` combines the leaves'
  values. SQL's distribution functions are this operator – `(r-1)/(N-1)`
  for `percent_rank`, `c/N` for `cume_dist`, the bucket arithmetic for
  `ntile` – each reading two frames of one partition.

  It reads the union of its frames as one family and records per leaf
  which of those occurrences that leaf reads (`ValueFrame.exprOf`). The
  two families are *nested* – `w_≺` inside the partition – so a reading
  that cannot tell which occurrences the two share invents worlds: a
  rank of three beside a count of one. Everything is indexed by
  occurrence, so an `EXCLUDE CURRENT ROW` frame is as exact here as a
  single-frame window's.

  **Why this is an operator and not a projection, here.** It is a
  primitive of *this* syntax and not of the semantics. An aggregate
  value read as `⟨f, t, U⟩`, carrying the occurrence sequence itself,
  makes a projection forming a term over two window columns denote the
  right aggregate expression over `U₁ ∪ U₂` already, with nothing to
  reconstruct. `AggValue` keeps a *value* per occurrence instead
  of `U` (the term is applied when the token is built), so two finished
  columns can no longer be related, and the sharing has to be recorded
  where it is still known. `AggExpr.occs` does record it – the value
  each leaf reads at each occurrence – but only for a leaf set fixed
  when the family is built, which is what an operator has and a
  projection does not.

  Like `Win` it removes no row, merges none and changes no annotation,
  so it creates no group and leaves nothing pending. It is the one
  operator of the syntax that builds a non-`tok` column, which is why
  `AggQueryIn.evaluate_ordinaryTokens` is conditional on
  `noWinExpr`.

  **Its input is all-regular, where `Win`'s need not be, and that is a
  limit of the representation rather than of the semantics.** A window
  over one frame carries an aggregate column of its input through
  unchanged, because its token is a function of the relation and of the
  row alone (`ValueFrame.tokenOf`) and needs no indexing; here the
  column is a function of the *occurrence*, which is what keeps
  `EXCLUDE CURRENT ROW` exact, and an occurrence is a position in a
  listing of the rows. A listing of a bag has to be independent of the
  listing it is computed from, so it is taken in the domain's order
  (`OccFam.ofSorted`) – and rows holding aggregate values have no order
  to be listed by, a token carrying functions. A family indexed by
  occurrences as primitive objects, in the manner of
  `NestedValue.World`, would carry such a column with nothing further to
  prove: nothing here fails world by world, the reading a window takes
  of its input being the same in every world either way
  (`ColKind.readTuple`). -/
  | WinExpr : {c n m p q : ℕ} → {lab : ℕ} →
      {rd : Fin c → Bool} →
      (P : Tuple (Fin n) m) → (O : Tuple (Fin n) p) → (o : OrderSpec p) →
      (ws : Fin q → ValueFrame T p) →
      (ts : Fin q → TermIn T c n) → (fs : Fin q → SeqAggFunc T) →
      (g : (Fin q → T) → T) →
      AggQueryIn T c n (ColKind.allReg n) →
      (keeps : Fin q → Option (Selection T n) := fun _ => none) →
      AggQueryIn T c (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg)

/-- A closed query: one that reads no outer column. -/
abbrev AggQuery (T : Type) (n : ℕ) (κ : Fin n → ColKind) := AggQueryIn T 0 n κ

/-- Transport a query along an equality of kind vectors (kind vectors
arising from projections are rarely definitionally all-regular). -/
def AggQueryIn.castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List (String × ℕ)}
    (h : κ = κ') : AggQueryIn T c n κ l → AggQueryIn T c n κ' l := h ▸ id

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

/-- **What a window reads of a plain row**: its regular columns, and a
constant where the kinds put an aggregate column. Nothing of an aggregate
column is read – not even to break a tie in the `ORDER BY`, which is why
the determinized peer order is the same in every world (`WinReadsReg`
says why that is what a window must do). On all-regular columns it is the
row itself. -/
def ColKind.readTuple {n : ℕ} (κ : Fin n → ColKind) (u : Tuple T n) :
    Tuple T n :=
  fun k => match (κ k).base with
    | ColKind.agg => 0
    | _ => u k

/-- What a window reads of a general row: `ColKind.readTuple` of its
columns, which is their collapse wherever a regular column sits. -/
def GenRow.readTuple {n : ℕ} (κ : Fin n → ColKind)
    (u : Tuple (GenValue T K) n) : Tuple T n :=
  fun k => match (κ k).base with
    | ColKind.agg => 0
    | _ => AggValue.collapseSum (u k)

/-- **What a term reading regular columns reads of a row is what it
reads of the window's reading of that row.** The nulling a window
applies to its input (`ColKind.readTuple`) touches only the aggregate
columns, and such a term names none of them – so the aggregated term,
and with it the partition and order keys below, are blind to it. What
the nulling is *for* is the rest: the canonical order on rows, by which
a listing of a frame is determinized, and which would otherwise tell
two rows apart by an aggregate column – reading differently in each
world. -/
theorem TermIn.eval_readTuple {c n : ℕ} {κ : Fin n → ColKind}
    (t : TermIn T c n) (hr : t.regOnly κ = true) (u : Tuple T n)
    (γ : Fin c → T) : t.eval (ColKind.readTuple κ u) γ = t.eval u γ := by
  induction t with
  | const a => rfl
  | outer k => rfl
  | index k =>
    show ColKind.readTuple κ u k = u k
    have hk : (κ k).base = ColKind.reg := by
      have := hr
      rw [TermIn.regOnly, beq_iff_eq] at this
      exact this
    show (match (κ k).base with
      | ColKind.agg => (0 : T)
      | _ => u k) = u k
    rw [hk]
  | add t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hr
    exact congrArg₂ (fun a b : T => a + b) (ih₁ h₁) (ih₂ h₂)
  | sub t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hr
    exact congrArg₂ (fun a b : T => a - b) (ih₁ h₁) (ih₂ h₂)
  | mul t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hr
    exact congrArg₂ (fun a b : T => a * b) (ih₁ h₁) (ih₂ h₂)
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    obtain ⟨h₁₂₃, h₄⟩ := Bool.and_eq_true_iff.mp hr
    obtain ⟨h₁₂, h₃⟩ := Bool.and_eq_true_iff.mp h₁₂₃
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h₁₂
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁ h₁, ih₂ h₂, ih₃ h₃, ih₄ h₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hr
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁ h₁, ih₂ h₂]
    rfl

/-- **And a key of regular columns is blind to it too.** -/
theorem Tuple.key_readTuple {n m : ℕ} {κ : Fin n → ColKind}
    (is : Tuple (Fin n) m) (hr : ∀ k, (κ (is k)).base = ColKind.reg)
    (u : Tuple T n) :
    Tuple.key is (ColKind.readTuple κ u) = Tuple.key is u := by
  funext k
  show (match (κ (is k)).base with
    | ColKind.agg => (0 : T)
    | _ => u (is k)) = u (is k)
  rw [hr k]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The two readings agree: what a window reads of a row is what it reads
of its regular reading. -/
theorem ColKind.readTuple_plainTuple {n : ℕ} (κ : Fin n → ColKind)
    (u : Tuple (GenValue T K) n) :
    ColKind.readTuple κ (GenRow.plainTuple u) = GenRow.readTuple κ u := rfl

/-- The occurrence a window's input relation gives a row of its input:
what the window reads of the row, carrying the row's annotation. -/
def GenRow.readAnnotated {n : ℕ} (κ : Fin n → ColKind) (r : GenRow T K n) :
    AnnotatedTuple T K n :=
  ⟨GenRow.readTuple κ r.fst, r.snd.finalize⟩

omit [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem GenRow.readAnnotated_allReg {n : ℕ} (r : GenRow T K n) :
    GenRow.readAnnotated (ColKind.allReg n) r = GenRow.toAnnotated r := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem ColKind.readTuple_allReg {n : ℕ} (u : Tuple T n) :
    ColKind.readTuple (ColKind.allReg n) u = u := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- An all-regular relation is read whole: the window reads every column
of every row. -/
@[simp] theorem ColKind.map_readTuple_allReg {n : ℕ}
    (M : Multiset (Tuple T n)) :
    M.map (ColKind.readTuple (ColKind.allReg n)) = M :=
  Eq.trans (Multiset.map_congr rfl (fun _ _ => rfl)) (Multiset.map_id M)

omit [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem GenRow.map_readAnnotated_allReg {n : ℕ}
    (M : Multiset (GenRow T K n)) :
    M.map (GenRow.readAnnotated (ColKind.allReg n))
      = M.map GenRow.toAnnotated := rfl

/-- **The row a window gives a row of its input**: the row itself, one
column longer, carrying the token the relation gives it – or, under a
`FILTER` clause, the aggregate expression over the whole frame whose leaf
reads what the clause keeps.

Its own columns go through untouched, aggregate columns included: a
window reads regular columns and rewrites none of them. So do its
annotation and its pending factors, a window creating no group. -/
def ValueFrame.windowGenRow {c n m p : ℕ} (lab : ℕ) (ck : List T) (κ : Fin n → ColKind)
    (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (keep : Option (Selection T n))
    (X : AnnotatedRelation T K n) (x : GenRow T K n)
    (γ : Fin c → T := fun _ => 0) (dist : Bool := false) :
    GenRow T K (n + 1) :=
  ⟨Fin.snoc x.fst (Sum.inr ((match keep with
      | none =>
          AggTok.tok (ValueFrame.tokenOfDist P O o w t f dist X
            (GenRow.readAnnotated κ x) γ)
      | some φ =>
          AggTok.expr (ValueFrame.exprWhenOf P O o w t f dist φ.keeps X
            (GenRow.readAnnotated κ x) γ)).setFam
        (lab, List.ofFn (GenRow.readAnnotated κ x).fst, ck))),
    x.snd⟩

/-- Embed an annotated tuple as a general row (all-regular, nothing
pending). -/
def GenRow.ofAnnotated {n : ℕ} (p : AnnotatedTuple T K n) : GenRow T K n :=
  ⟨fun k => Sum.inl (p.fst k), ⟨p.snd, 0⟩⟩

/-- **The alternatives of an occurrence at one aggregate column**: one
row per value the column's aggregate value takes, the column made
regular and the annotation multiplied by `[a ≐ v]`
(`AggValue.altProv`). A column already regular has the occurrence
itself as its only alternative. This is how an operator that compares
keys reads an aggregate column. -/
def GenRow.alternativesAt {n : ℕ} (r : GenRow T K n) (i : Fin n) :
    Multiset (GenRow T K n) :=
  match r.fst i with
  | Sum.inl _ => {r}
  | Sum.inr a =>
    a.vals.val.map (fun v =>
      (Function.update r.fst i (Sum.inl v),
        (⟨r.snd.base * a.altProv v, r.snd.pending⟩ : GenAnn K)))

/-- The multiset of occurrence-annotation lists of the token columns of a
tuple (used by projection to detect dropped groups). -/
def tokenLists {n : ℕ} (u : Tuple (GenValue T K) n) : Multiset (List K) :=
  (Finset.univ.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => some a.annList))

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

theorem TermIn.evalPlain_atCol {c k : ℕ} {κ : Fin k → ColKind} (i : Fin k)
    (h : κ i = ColKind.reg) (u : Tuple T k) (γ : Fin c → T) :
    ∀ t : TermIn T 1 0, (t.atCol i h).evalPlain u γ = t.unary (u i)
  | .const a => rfl
  | .outer _ => rfl
  | .index j => j.elim0
  | .add t₁ t₂ => congrArg₂ (fun a b : T => a + b)
      (evalPlain_atCol i h u γ t₁) (evalPlain_atCol i h u γ t₂)
  | .sub t₁ t₂ => congrArg₂ (fun a b : T => a - b)
      (evalPlain_atCol i h u γ t₁) (evalPlain_atCol i h u γ t₂)
  | .mul t₁ t₂ => congrArg₂ (fun a b : T => a * b)
      (evalPlain_atCol i h u γ t₁) (evalPlain_atCol i h u γ t₂)
  | .caseWhen op t₁ t₂ t₃ t₄ => by
    show (if (op.eval3 _ _) = Kleene.true then _ else _) = _
    rw [evalPlain_atCol i h u γ t₁, evalPlain_atCol i h u γ t₂,
      evalPlain_atCol i h u γ t₃, evalPlain_atCol i h u γ t₄]
    rfl
  | .coalesce t₁ t₂ => by
    show (if ValueType.isNull _ then _ else _) = _
    rw [evalPlain_atCol i h u γ t₁, evalPlain_atCol i h u γ t₂]
    rfl

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
  | .token _ _ | .aggTerm _ _ _ | .aggTermOf _ _ _ => True

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

/-! ### What the recursions mean: the rounds settling

`muSum` and `muIter` run a *given* number of rounds, which is a tool and
not the semantics: a recursion means the value its rounds settle at, and
means nothing where they do not settle. `MuSetSettles` and `MuSettles`
say when there is such a value, `muFix` and `muSumFix` are it, and the
two transfer lemmas below are how a bounded computation witnesses it –
reach a round that repeats, or an empty one, and the semantics is that
value. -/

/-- **A set recursion settles** when some round equals the next. The
rounds are then constant from there on, so the value is well defined. -/
def MuSetSettles {α : Type} (step : Multiset α → Multiset α) : Prop :=
  ∃ j, step^[j + 1] 0 = step^[j] 0

/-- **A duplicate-preserving recursion settles** when some round past
the first is empty, which is where SQL's own iteration stops. -/
def MuSettles {α : Type} (step : Multiset α → Multiset α)
    (M : Multiset α) : Prop :=
  ∃ k, step^[k + 1] M = 0

/-- The first round at which a set recursion repeats; `0` where it never
does (`Nat.sInf_empty`), which is junk and is what makes the total
function below say nothing where the semantics says nothing. -/
noncomputable def muFixIdx {α : Type} (step : Multiset α → Multiset α) : ℕ :=
  sInf {j | step^[j + 1] 0 = step^[j] 0}

/-- The number of rounds a duplicate-preserving recursion sums: up to the
first empty one, `0` where there is none. -/
noncomputable def muRounds {α : Type} (step : Multiset α → Multiset α)
    (M : Multiset α) : ℕ :=
  sInf {k | step^[k + 1] M = 0}

/-- **The value a set recursion settles at** – `X_j` for the first `j`
with `X_{j+1} = X_j`. Junk (`∅`) where the rounds never settle, which no
statement about it may read: a result about a set recursion carries
`MuSetSettles` as a hypothesis. -/
noncomputable def muFix {α : Type} (step : Multiset α → Multiset α) :
    Multiset α :=
  muIter step (muFixIdx step)

/-- **The value a duplicate-preserving recursion settles at** – the sum
of the rounds up to the first empty one. Junk where no round is empty. -/
noncomputable def muSumFix {α : Type} (step : Multiset α → Multiset α)
    (M : Multiset α) : Multiset α :=
  muSum step (muRounds step M) M

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

/-- `muIter` is iteration from the empty relation. -/
theorem muIter_eq_iterate {α : Type} (step : Multiset α → Multiset α) (j : ℕ) :
    muIter step j = step^[j] 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [muIter, ih, Function.iterate_succ_apply']

/-- **A round that repeats witnesses the value a set recursion settles
at**: `muFix` is that round, whatever later round exhibited it. This is
how a bounded computation establishes the semantics. -/
theorem muFix_eq_of_fix {α : Type} {step : Multiset α → Multiset α} {j : ℕ}
    (hj : step (muIter step j) = muIter step j) :
    muFix step = muIter step j := by
  have hmem : j ∈ {i | step^[i + 1] 0 = step^[i] 0} := by
    show step^[j + 1] 0 = step^[j] 0
    rw [Function.iterate_succ_apply', ← muIter_eq_iterate]
    exact hj
  have hne : {i | step^[i + 1] 0 = step^[i] 0}.Nonempty := ⟨j, hmem⟩
  have hm : step (muIter step (muFixIdx step)) = muIter step (muFixIdx step) := by
    have hspec : step^[muFixIdx step + 1] 0 = step^[muFixIdx step] 0 := by
      rw [muFixIdx]
      exact Nat.sInf_mem hne
    rw [muIter_eq_iterate]
    rw [Function.iterate_succ_apply'] at hspec
    exact hspec
  have hle : muFixIdx step ≤ j := by
    rw [muFixIdx]
    exact Nat.sInf_le hmem
  rw [muFix]
  exact (muIter_eq_of_le hm hle).symm

/-- **An empty round witnesses the value a duplicate-preserving
recursion settles at.** -/
theorem muSumFix_eq_of_empty {α : Type} {step : Multiset α → Multiset α}
    (h0 : step 0 = 0) {M : Multiset α} {k : ℕ} (hk : step^[k + 1] M = 0) :
    muSumFix step M = muSum step k M := by
  have hmem : k ∈ {i | step^[i + 1] M = 0} := hk
  have hne : {i | step^[i + 1] M = 0}.Nonempty := ⟨k, hmem⟩
  have hspec : step^[muRounds step M + 1] M = 0 := by
    rw [muRounds]; exact Nat.sInf_mem hne
  have hle : muRounds step M ≤ k := by
    rw [muRounds]; exact Nat.sInf_le hmem
  rw [muSumFix]
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · rw [heq]
  · have h1 : muSum step k M = muSum step (muRounds step M + 1) M :=
      muSum_eq_of_le h0 hspec (le_refl _) (by omega)
    have h2 : muSum step (muRounds step M + 1) M
        = muSum step (muRounds step M) M := by
      rw [muSum_succ, hspec, add_zero]
    exact h2.symm.trans h1.symm


/-- **The sums of two simulating round sequences simulate each other**:
the rounds are related one by one, so the first empty one is the same on
both sides. -/
theorem muSumFix_rel {α β : Type} {R : β → α → Prop} {step : Multiset α → Multiset α}
    {step' : Multiset β → Multiset β} {M : Multiset α} {M' : Multiset β}
    (hM : Multiset.Rel R M' M)
    (hstep : ∀ (k : ℕ) (X' : Multiset β), Multiset.Rel R X' (step^[k] M) →
      Multiset.Rel R (step' X') (step (step^[k] M))) :
    Multiset.Rel R (muSumFix step' M') (muSumFix step M) := by
  have hit : ∀ k, Multiset.Rel R (step'^[k] M') (step^[k] M) := by
    intro k
    induction k with
    | zero => exact hM
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hstep k _ ih
  have hz : ∀ k, step'^[k] M' = 0 ↔ step^[k] M = 0 := by
    intro k
    constructor
    · intro h0
      have := hit k
      rw [h0] at this
      exact Multiset.rel_zero_left.mp this
    · intro h0
      have := hit k
      rw [h0] at this
      exact Multiset.rel_zero_right.mp this
  have hr : muRounds step' M' = muRounds step M := by
    unfold muRounds
    congr 1
    ext k
    exact hz (k + 1)
  unfold muSumFix
  rw [hr]
  generalize muRounds step M = b
  induction b with
  | zero => exact hM
  | succ b ih =>
    rw [muSum_succ, muSum_succ]
    exact ih.add (hit (b + 1))

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

/-- **The round a set recursion settles at is a fixpoint of its step.** -/
theorem muFix_isFix {α : Type} {step : Multiset α → Multiset α}
    (h : MuSetSettles step) : step (muFix step) = muFix step := by
  have hne : {i | step^[i + 1] 0 = step^[i] 0}.Nonempty := h
  have hspec : step^[muFixIdx step + 1] 0 = step^[muFixIdx step] 0 := by
    rw [muFixIdx]
    exact Nat.sInf_mem hne
  rw [muFix, muIter_eq_iterate]
  rw [Function.iterate_succ_apply'] at hspec
  exact hspec

/-- **A map commutes with the value a set recursion settles at**, where
it settles: the images of the rounds are the rounds of the image, so a
fixpoint maps to a fixpoint, and the image settles no later. This is what
replaces `muIter_map` once the round count is not part of the query. -/
theorem muFix_map {α β : Type} {h : Multiset α → Multiset β} (h0 : h 0 = 0)
    {step : Multiset α → Multiset α} {stepP : Multiset β → Multiset β}
    (hstep : ∀ X, h (step X) = stepP (h X)) (hs : MuSetSettles step) :
    h (muFix step) = muFix stepP := by
  have hfix : step (muIter step (muFixIdx step)) = muIter step (muFixIdx step) :=
    muFix_isFix hs
  have hfixP : stepP (muIter stepP (muFixIdx step))
      = muIter stepP (muFixIdx step) := by
    rw [← muIter_map h0 hstep, ← hstep, hfix]
  rw [muFix, muIter_map h0 hstep, (muFix_eq_of_fix hfixP).symm]

/-- **A map commutes with the value a duplicate-preserving recursion
settles at**, where it settles and an empty round stays empty. -/
theorem muSumFix_map {α β : Type} {h : Multiset α → Multiset β} (h0 : h 0 = 0)
    (hadd : ∀ x y, h (x + y) = h x + h y)
    {step : Multiset α → Multiset α} {stepP : Multiset β → Multiset β}
    (hstep : ∀ X, h (step X) = stepP (h X)) (hz : step 0 = 0)
    {M : Multiset α} (hm : MuSettles step M) :
    h (muSumFix step M) = muSumFix stepP (h M) := by
  have hne : {i | step^[i + 1] M = 0}.Nonempty := hm
  have hspec : step^[muRounds step M + 1] M = 0 := by
    rw [muRounds]
    exact Nat.sInf_mem hne
  have hiter : ∀ i (N : Multiset α), h (step^[i] N) = stepP^[i] (h N) := by
    intro i
    induction i with
    | zero => intro N; rfl
    | succ i ih =>
      intro N
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hstep]
  have hspecP : stepP^[muRounds step M + 1] (h M) = 0 := by
    rw [← hiter, hspec, h0]
  have hzP : stepP 0 = 0 := by rw [← h0, ← hstep, hz, h0]
  rw [muSumFix_eq_of_empty hz hspec, muSumFix_eq_of_empty hzP hspecP,
    muSum_map hadd hstep]

/-- **Steps that agree have the same settling value**, for a
duplicate-preserving recursion. -/
theorem muSumFix_congr {α : Type} {step step' : Multiset α → Multiset α}
    (h : ∀ X, step X = step' X) {M M' : Multiset α} (hM : M = M') :
    muSumFix step M = muSumFix step' M' := by
  subst hM
  exact congrArg (fun f => muSumFix f M) (funext h)

/-- **Steps that agree have the same fixpoint**, for a
duplicate-eliminating recursion. -/
theorem muFix_congr {α : Type} {step step' : Multiset α → Multiset α}
    (h : ∀ X, step X = step' X) : muFix step = muFix step' :=
  congrArg muFix (funext h)

/-- Duplicate elimination on an annotated relation: one slot per tuple,
annotated by the `⊕` of its copies – what `Dedup` computes, named for
the rounds of `MuSet`. -/
def AnnotatedRelation.dedupAnn {n : ℕ} (r : AnnotatedRelation T K n) :
    AnnotatedRelation T K n := Multiset.ofList (groupByKey r).val

/-- The kind of a lifted value. -/
def GenValue.kindOf : GenValue T K → ColKind
  | Sum.inl _ => ColKind.reg
  | Sum.inr _ => ColKind.agg

/-- **A row has the kinds `κ`**: a regular value where `κ` says regular or
provenance, a token where it says aggregate. -/
def GenRow.Conforms {n : ℕ} (κ : Fin n → ColKind) (u : Tuple (GenValue T K) n) : Prop :=
  ∀ k, GenValue.kindOf (u k) = (κ k).base

instance {n : ℕ} (κ : Fin n → ColKind) (u : Tuple (GenValue T K) n) :
    Decidable (GenRow.Conforms κ u) :=
  inferInstanceAs (Decidable (∀ k, GenValue.kindOf (u k) = (κ k).base))

/-- **What the annotated evaluator reads besides the database and the
plain context**: the rounds a recursion binds to its name, as general rows
– a round may carry aggregate columns, which a database cannot hold – and
the context with its aggregate values, which an apply extends with the row
of its left side and the leaf `AggQueryIn.Param` reads. A closed query
reads neither. -/
structure EvalEnv (T K : Type) where
  /-- The round bound to each recursive name, at each arity. -/
  holes : String → (n : ℕ) → Multiset (GenRow T K n) := fun _ _ => 0
  /-- The context, aggregate values included. -/
  ctx : Σ c, Tuple (GenValue T K) c := ⟨0, fun k => k.elim0⟩

/-- Binding a recursive name to a round. -/
def EvalEnv.assignHole (E : EvalEnv T K) (s : String) {n : ℕ}
    (X : Multiset (GenRow T K n)) : EvalEnv T K :=
  { E with holes := fun s' m =>
      if h : s' = s ∧ m = n then
        cast (congrArg (fun k => Multiset (GenRow T K k)) h.2.symm) X
      else E.holes s' m }

/-- The context of arity `c`, aggregate values included: the one the
environment holds when it has that arity, and the plain context read as
regular values otherwise – which is what a context with no aggregate value
is. -/
def EvalEnv.ctxAt (E : EvalEnv T K) (c : ℕ) (γ : Fin c → T) : Tuple (GenValue T K) c :=
  if h : E.ctx.1 = c then fun k => E.ctx.2 (Fin.cast h.symm k)
  else fun k => Sum.inl (γ k)

/-- Setting the context. -/
def EvalEnv.withCtx (E : EvalEnv T K) {c : ℕ} (u : Tuple (GenValue T K) c) :
    EvalEnv T K :=
  { E with ctx := ⟨c, u⟩ }

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem EvalEnv.ctxAt_withCtx (E : EvalEnv T K) {c : ℕ} (u : Tuple (GenValue T K) c)
    (γ : Fin c → T) : (E.withCtx u).ctxAt c γ = u := by
  unfold EvalEnv.ctxAt EvalEnv.withCtx
  rw [dite_eq_left rfl]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.ctxAt_withCtx_cast (E : EvalEnv T K) {c c' : ℕ} (h : c' = c)
    (u : Tuple (GenValue T K) c') (γ : Fin c → T) :
    (E.withCtx u).ctxAt c γ = fun k => u (Fin.cast h.symm k) := by
  subst h
  exact EvalEnv.ctxAt_withCtx E u γ

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem EvalEnv.withCtx_withCtx (E : EvalEnv T K) {c c' : ℕ}
    (u : Tuple (GenValue T K) c) (v : Tuple (GenValue T K) c') :
    (E.withCtx u).withCtx v = E.withCtx v := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem EvalEnv.ctxAt_assignHole (E : EvalEnv T K) (s : String) {n : ℕ}
    (X : Multiset (GenRow T K n)) {c : ℕ} (γ : Fin c → T) :
    (E.assignHole s X).ctxAt c γ = E.ctxAt c γ := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- An environment with no context reads the plain context as regular
values. -/
@[simp] theorem EvalEnv.empty_ctxAt {c : ℕ} (γ : Fin c → T) :
    ({} : EvalEnv T K).ctxAt c γ = fun k => Sum.inl (γ k) := by
  unfold EvalEnv.ctxAt
  split
  · next h =>
    funext k
    have : c = 0 := h.symm
    subst this
    exact k.elim0
  · rfl

/-- What the leaf `AggQueryIn.Param pv ρ` reads: the row whose column `k` is
the parameter or constant `pv k`, when it has the kinds `ρ`, annotated
`𝟙`. -/
def EvalEnv.paramRows (E : EvalEnv T K) {c m : ℕ} (γ : Fin c → T) (pv : Fin m → T ⊕ Fin c)
    (ρ : Fin m → ColKind) : Multiset (GenRow T K m) :=
  let u : Tuple (GenValue T K) m := fun k => Sum.elim Sum.inl (E.ctxAt c γ) (pv k)
  if GenRow.Conforms ρ u then {⟨u, ⟨1, 0⟩⟩} else 0

/-- **Every value the environment holds has the property `Q`**: in the
rows of every round it binds and in its context. -/
def EvalEnv.RowsSat (Q : GenValue T K → Prop) (E : EvalEnv T K) : Prop :=
  (∀ (s : String) (n : ℕ), ∀ r ∈ E.holes s n, ∀ k, Q (r.fst k)) ∧ ∀ k, Q (E.ctx.2 k)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.rowsSat_empty {Q : GenValue T K → Prop} : ({} : EvalEnv T K).RowsSat Q :=
  ⟨fun _ _ r hr => absurd hr (Multiset.notMem_zero r), fun k => k.elim0⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.rowsSat_assignHole {Q : GenValue T K → Prop}
    {E : EvalEnv T K} (hE : E.RowsSat Q) (s : String) {n : ℕ}
    {X : Multiset (GenRow T K n)} (hX : ∀ r ∈ X, ∀ k, Q (r.fst k)) :
    (E.assignHole s X).RowsSat Q := by
  refine ⟨fun s' m r hr => ?_, hE.2⟩
  simp only [EvalEnv.assignHole] at hr
  by_cases h : s' = s ∧ m = n
  · obtain ⟨rfl, rfl⟩ := h
    rw [dite_eq_left ⟨rfl, rfl⟩] at hr
    exact hX r hr
  · rw [dite_eq_right h] at hr
    exact hE.1 s' m r hr

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.rowsSat_ctxAt {Q : GenValue T K → Prop} (hQ : ∀ a, Q (Sum.inl a))
    {E : EvalEnv T K} (hE : E.RowsSat Q) (c : ℕ) (γ : Fin c → T) (k : Fin c) :
    Q (E.ctxAt c γ k) := by
  unfold EvalEnv.ctxAt
  split
  · exact hE.2 _
  · exact hQ _

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.rowsSat_withCtx {Q : GenValue T K → Prop}
    {E : EvalEnv T K} (hE : E.RowsSat Q) {c : ℕ} {u : Tuple (GenValue T K) c}
    (hu : ∀ k, Q (u k)) : (E.withCtx u).RowsSat Q :=
  ⟨hE.1, hu⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Entering an apply's right side at a row of its left side. -/
theorem EvalEnv.rowsSat_enter {Q : GenValue T K → Prop} (hQ : ∀ a, Q (Sum.inl a))
    {E : EvalEnv T K} (hE : E.RowsSat Q) {c n₁ : ℕ} (γ : Fin c → T)
    {x : Tuple (GenValue T K) n₁} (hx : ∀ k, Q (x k)) :
    (E.withCtx (Fin.append x (E.ctxAt c γ))).RowsSat Q :=
  EvalEnv.rowsSat_withCtx hE (fun k => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact EvalEnv.rowsSat_ctxAt hQ hE c γ j)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.rowsSat_hole {Q : GenValue T K → Prop}
    {E : EvalEnv T K} (hE : E.RowsSat Q) {s : String} {n : ℕ} {κ : Fin n → ColKind}
    {r : GenRow T K n} (hr : r ∈ (E.holes s n).filter (fun r => GenRow.Conforms κ r.fst)) :
    ∀ k, Q (r.fst k) :=
  hE.1 s n r (Multiset.mem_of_mem_filter hr)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.rowsSat_param {Q : GenValue T K → Prop} (hQ : ∀ a, Q (Sum.inl a))
    {E : EvalEnv T K} (hE : E.RowsSat Q) {c m : ℕ} {γ : Fin c → T} {pv : Fin m → T ⊕ Fin c}
    {ρ : Fin m → ColKind} {r : GenRow T K m} (hr : r ∈ E.paramRows γ pv ρ) :
    ∀ k, Q (r.fst k) := by
  simp only [EvalEnv.paramRows] at hr
  split at hr
  · rw [Multiset.mem_singleton] at hr
    subst hr
    intro k
    show Q (Sum.elim Sum.inl (E.ctxAt c γ) (pv k))
    cases pv k with
    | inl a => exact hQ a
    | inr j => exact EvalEnv.rowsSat_ctxAt hQ hE c γ j
  · exact absurd hr (Multiset.notMem_zero r)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- The parameter row has the kinds its leaf says. -/
theorem EvalEnv.conforms_of_mem_paramRows {E : EvalEnv T K} {c m : ℕ} {γ : Fin c → T}
    {pv : Fin m → T ⊕ Fin c} {ρ : Fin m → ColKind}
    {r : GenRow T K m} (hr : r ∈ E.paramRows γ pv ρ) : GenRow.Conforms ρ r.fst := by
  simp only [EvalEnv.paramRows] at hr
  split at hr
  · next hc =>
    rw [Multiset.mem_singleton] at hr
    subst hr
    exact hc
  · exact absurd hr (Multiset.notMem_zero r)

/-- A property of the rows that every round keeps holds of every row of the
recursion. -/
theorem forall_mem_muSum {α : Type} {P : α → Prop} {step : Multiset α → Multiset α}
    (hstep : ∀ X : Multiset α, (∀ x ∈ X, P x) → ∀ y ∈ step X, P y) :
    ∀ (b : ℕ) (M : Multiset α), (∀ x ∈ M, P x) → ∀ y ∈ muSum step b M, P y := by
  intro b
  induction b with
  | zero => exact fun M hM => hM
  | succ b ih =>
    intro M hM y hy
    rcases Multiset.mem_add.mp hy with h | h
    · exact hM y h
    · exact ih (step M) (hstep M hM) y h

theorem forall_mem_muSumFix {α : Type} {P : α → Prop} {step : Multiset α → Multiset α}
    (hstep : ∀ X : Multiset α, (∀ x ∈ X, P x) → ∀ y ∈ step X, P y) {M : Multiset α}
    (hM : ∀ x ∈ M, P x) : ∀ y ∈ muSumFix step M, P y :=
  forall_mem_muSum hstep _ M hM

/-! ### The parameters an operator reads

An occurrence belongs to the operator that produces it *and to the values
of the apply parameters that operator reads*: an operator evaluated on the
same inputs produces the same occurrences, and one reading different
parameter values produces different ones. So the family an aggregating
operator stamps on its values records those values, and these functions
say which parameters (outer columns) a term, a predicate or a whole
subquery reads. -/

/-- Does the term read the outer column `k`? -/
def TermIn.readsOuter {c n : ℕ} (k : Fin c) : TermIn T c n → Bool
  | .const _ => false
  | .outer j => decide (j = k)
  | .index _ => false
  | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ | .coalesce t₁ t₂ =>
      t₁.readsOuter k || t₂.readsOuter k
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      t₁.readsOuter k || t₂.readsOuter k || t₃.readsOuter k || t₄.readsOuter k

/-- Does the term read the outer column `k`? -/
def TermGIn.readsOuter {c n : ℕ} {κ : Fin n → ColKind} (k : Fin c) : TermGIn T c κ → Bool
  | .const _ => false
  | .outer j => decide (j = k)
  | .index _ _ => false
  | .provIndex _ _ => false
  | .cmpAgg _ _ _ t => t.readsOuter k
  | .chiGate _ t₁ t₂ | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ | .coalesce t₁ t₂ =>
      t₁.readsOuter k || t₂.readsOuter k
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      t₁.readsOuter k || t₂.readsOuter k || t₃.readsOuter k || t₄.readsOuter k

/-- Does the predicate read the outer column `k`? -/
def GenPredIn.readsOuter {c n : ℕ} {κ : Fin n → ColKind} (k : Fin c) : GenPredIn T c κ → Bool
  | .cmp _ t₁ t₂ => t₁.readsOuter k || t₂.readsOuter k
  | .aggCmp _ _ _ t => t.readsOuter k
  | .aggRange _ _ _ t₁ _ t₂ => t₁.readsOuter k || t₂.readsOuter k
  | .and φ ψ | .or φ ψ => φ.readsOuter k || ψ.readsOuter k
  | .not φ => φ.readsOuter k

/-- Does the projection column read the outer column `k`? -/
def ProjColIn.readsOuter {c n : ℕ} {κ : Fin n → ColKind} (k : Fin c) : ProjColIn T c κ → Bool
  | .term t => t.readsOuter k
  | .token _ _ => false
  | .aggTerm _ _ _ => false
  | .aggTermOf _ _ _ => false
  | .provTerm t => t.readsOuter k

/-- **Does the query read the outer column `k`?** An apply's right side
reads its own parameters after the left row's columns. -/
def AggQueryIn.readsOuter : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Fin c → Bool
  | _, _, _, _, .Rel _ _, _ => false
  | _, _, _, _, .Hole _ _ _, _ => false
  | _, _, _, _, .Param pv _, k =>
      (List.finRange _).any (fun i => _root_.Sum.elim (fun _ => false) (fun j => decide (j = k))
        (pv i))
  | _, _, _, _, .Empty, _ => false
  | _, _, _, _, .Proj ps q, k => (List.finRange _).any (fun j => (ps j).readsOuter k)
      || q.readsOuter k
  | _, _, _, _, .Sel φ q _, k => φ.readsOuter k || q.readsOuter k
  | _, _, _, _, .Prod q₁ q₂, k => q₁.readsOuter k || q₂.readsOuter k
  | _, _, _, _, @Apply _ _ n₁ _ _ _ _ q₁ q₂, k =>
      q₁.readsOuter k || q₂.readsOuter (Fin.natAdd n₁ k)
  | _, _, _, _, .Sum q₁ q₂, k => q₁.readsOuter k || q₂.readsOuter k
  | _, _, _, _, .Dedup q, k => q.readsOuter k
  | _, _, _, _, .Diff q₁ q₂, k => q₁.readsOuter k || q₂.readsOuter k
  | _, _, _, _, .Explode _ _ q, k => q.readsOuter k
  | _, _, _, _, .Mu _ q₀ q₁, k => q₀.readsOuter k || q₁.readsOuter k
  | _, _, _, _, .MuSet _ q₀ q₁, k => q₀.readsOuter k || q₁.readsOuter k
  | _, _, _, _, .Gamma _ ts _ q _ _, k =>
      (List.finRange _).any (fun j => (ts j).readsOuter k) || q.readsOuter k
  | _, _, _, _, .GammaScalar ts _ q _, k =>
      (List.finRange _).any (fun j => (ts j).readsOuter k) || q.readsOuter k
  | _, _, _, _, .GammaNest _ _ p _ q, k => p.readsOuter k || q.readsOuter k
  | _, _, _, _, .ProvSum _ _ t q, k => t.readsOuter k || q.readsOuter k
  | _, _, _, _, .Retag _ q, k => q.readsOuter k
  | _, _, _, _, .GammaTok _ _ ts _ a q _, k =>
      (List.finRange _).any (fun j => (ts j).readsOuter k) || a.readsOuter k || q.readsOuter k
  | _, _, _, _, .Win _ _ _ _ t _ q _ _ _, k => t.readsOuter k || q.readsOuter k
  | _, _, _, _, .WinExpr _ _ _ _ ts _ _ q _, k =>
      (List.finRange _).any (fun j => (ts j).readsOuter k) || q.readsOuter k

/-- **The values of the parameters an operator reads**, in the order of the
context: what a family records besides the operator's label and the key
of the group. -/
def ctxKey {c : ℕ} {α : Type} (r : Fin c → Bool) (γ : Fin c → α) : List α :=
  (List.finRange c).filterMap (fun k => if r k then some (γ k) else none)

@[simp] theorem ctxKey_zero {α : Type} (r : Fin 0 → Bool) (γ : Fin 0 → α) :
    ctxKey r γ = [] := rfl

/-- **The general annotated evaluator.** All operators preserve the
factored-annotation discipline described in the module docstring. -/
noncomputable def AggQueryIn.evaluate {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) (E : EvalEnv T K := {}) : Multiset (GenRow T K n) :=
  match c, n, κ, l, q, d, γ, E with
  | _, n, _, _, Rel _ s, d, _, _ =>
    match d.find n s with
    | none => (∅ : Multiset (GenRow T K n))
    | some rn => (rn : Multiset (AnnotatedTuple T K n)).map GenRow.ofAnnotated
  | _, n, _, _, Hole _ s κ, _, _, E =>
    -- the round bound to the name, whose rows have the kinds the hole says
    (E.holes s n).filter (fun r => GenRow.Conforms κ r.fst)
  | _, _, _, _, Param pv ρ, _, γ, E => E.paramRows γ pv ρ
  | _, _, _, _, Empty, _, _, _ => (∅ : Multiset (GenRow T K 0))
  | _, _, _, _, @Proj _ _ n m κ _ ps q, d, γ, E =>
    (q.evaluate d γ E).map (fun r =>
      let u' : Tuple (GenValue T K) m := fun j => (ps j).eval r.fst γ
      -- groups all of whose token columns are dropped are cashed
      let kept := r.snd.pending ∩ tokenLists u'
      ⟨u', ⟨r.snd.base *
          ((r.snd.pending - kept).map
            (fun l => SemiringWithMonus.delta l.sum)).prod,
        kept⟩⟩)
  | _, _, _, _, Sel φ q _, d, γ, E =>
    let r := q.evaluate d γ E
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
            | Sum.inr a => some a.annList)
        -- and only when none of them is scalar: a scalar token holds in the
        -- empty world, so a comparison against it entails no group's
        -- existence and must not remove any group's factor, whatever
        -- occurrences it happens to carry
        let comparedScalar : Multiset (List K) :=
          φ.comparedCols.val.filterMap (fun k =>
            match r.fst k with
            | Sum.inl _ => none
            | Sum.inr a => if a.scalar then some a.annList else none)
        ⟨r.fst, ⟨r.snd.base * φ.predsemJ false r.fst γ,
          if φ.entailsExistence false then
            r.snd.pending.filter
              (fun l => ¬(comparedScalar = 0 ∧ compared ≠ 0
                ∧ ∀ l' ∈ compared, l' = l))
          else r.snd.pending⟩⟩)
    else
      r.filter (fun r => φ.holds r.fst γ)
  | _, _, _, _, Prod q₁ q₂, d, γ, E =>
    ((q₁.evaluate d γ E).product (q₂.evaluate d γ E)).map (fun (x, y) =>
      ⟨Fin.append x.fst y.fst,
        ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩)
  | _, _, _, _, @Apply _ _ n₁ _ _ _ _ q₁ q₂, d, γ, E =>
    -- the right side is read once per row of the left, under that row
    (q₁.evaluate d γ E).bind (fun x =>
      (q₂.evaluate d (Fin.append (GenRow.plainTuple x.fst) γ)
          (E.withCtx (Fin.append x.fst (E.ctxAt _ γ)))).map
        (fun y =>
        (⟨Fin.append x.fst y.fst,
          ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
            : GenRow T K (n₁ + _))))
  | _, _, _, _, Sum q₁ q₂, d, γ, E => q₁.evaluate d γ E + q₂.evaluate d γ E
  | _, _, _, _, Dedup q, d, γ, E =>
    let r : AnnotatedRelation T K _ := (q.evaluate d γ E).map GenRow.toAnnotated
    (Multiset.ofList (groupByKey r).val).map GenRow.ofAnnotated
  | _, _, _, _, Explode k _ q, d, γ, E =>
    (q.evaluate d γ E).bind (fun r => r.alternativesAt k)
  | _, _, _, _, Mu s q₀ q₁, d, γ, E =>
    -- the rounds up to the first empty one, junk where none is empty
    muSumFix (fun X => q₁.evaluate d γ (E.assignHole s X)) (q₀.evaluate d γ E)
  | _, _, _, _, MuSet s q₀ q₁, d, γ, E =>
    -- the round the iteration settles at, junk where it never settles
    (muFix (fun X =>
      AnnotatedRelation.dedupAnn
        (((q₀.evaluate d γ E).map GenRow.toAnnotated)
          + ((q₁.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))).map
              GenRow.toAnnotated)))).map
      GenRow.ofAnnotated
  | _, _, _, _, Diff q₁ q₂, d, γ, E =>
    let r₁ : AnnotatedRelation T K _ := (q₁.evaluate d γ E).map GenRow.toAnnotated
    let r₂ : AnnotatedRelation T K _ := (q₂.evaluate d γ E).map GenRow.toAnnotated
    let grouped₂ := groupByKey r₂
    (r₁.map (fun (u, α) =>
      (⟨u, α - (((grouped₂.val.find? (·.1 = u)).map Prod.snd).getD 0)⟩ :
        AnnotatedTuple T K _))).map GenRow.ofAnnotated
  | _, _, _, _, @Gamma _ _ m n₁ n₂ lab rd is ts fs q keep ord, d, γ, E =>
    let r : AnnotatedRelation T K m := (q.evaluate d γ E).map GenRow.toAnnotated
    -- one row per group key (the closed form is `havingSite_evaluateAnnotated`)
    (Multiset.ofList (groupByKey (r.map (fun p => (fun k => p.fst (is k), p.snd)
        : AnnotatedTuple T K m → AnnotatedTuple T K n₁))).val).map (fun kv =>
      let g : Tuple T n₁ := kv.fst
      -- the occurrence sequence, read in the aggregation's own order
      let U := Having.havingGroupOrd is ord r g
      -- a filtered aggregate reads its group as an expression: the family
      -- is the whole group, so the worlds are the group's, and the clause
      -- cuts only what the aggregate reads of them. The existence guard
      -- below runs over every occurrence either way
      ⟨Fin.append (fun k => Sum.inl (g k))
        (fun j => Sum.inr ((match keep j with
          | none => AggTok.tok (AggValue.ofGroup (fs j) (ts j) U γ)
          | some φ =>
              AggTok.expr (AggExpr.ofGroupWhen (fs j) (ts j) φ.keeps U γ)).setFam
            (lab, List.ofFn g,
              ctxKey rd γ))),
       ⟨1, {U.map Prod.snd}⟩⟩)
  | _, _, _, _, @GammaScalar _ _ m n₂ lab rd ts fs q ord, d, γ, E =>
    let r : AnnotatedRelation T K m := (q.evaluate d γ E).map GenRow.toAnnotated
    -- one row whatever the input; the whole of it is the occurrence
    -- sequence, read in the aggregation's own order
    let U := Having.havingGroupOrd (fun k : Fin 0 => k.elim0) ord r
      (fun k : Fin 0 => k.elim0)
    {(⟨fun j => Sum.inr ((AggTok.tok (AggValue.ofScalarGroup (fs j) (ts j) U γ)).setFam
        (lab, [], ctxKey rd γ)),
        ⟨1, 0⟩⟩
      : GenRow T K n₂)}
  | _, _, _, _, @GammaNest _ _ m n₁ _κ lab rd is _his p f q, d, γ, E =>
    let rows := q.evaluate d γ E
    -- the key is read off the columns' deterministic values; `his` makes
    -- every key column a value column, so this is the value it holds
    let key : GenRow T K m → Tuple T n₁ :=
      fun row => fun k => AggValue.collapseSum (row.fst (is k))
    ((rows.map key).dedup).map (fun g =>
      -- the group's rows, as a bag: they carry tokens, which nothing
      -- orders, and the outer aggregate asks for no order
      let U : Multiset (AggExpr T K × K) :=
        (rows.filter (fun row => key row = g)).map
          (fun row => (GenValue.innerValue (p.eval row.fst γ),
            row.snd.finalize))
      ⟨Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
        (fun _ : Fin 1 => Sum.inr (AggTok.nest ⟨f, U, false, (lab, List.ofFn g,
          ctxKey rd γ)⟩)),
       -- the group's existence factor, as the one annotation the bag of
       -- occurrences sums to – which is what `AggTok.annList` gives a
       -- nested token, so the supersede test can match the two
       ⟨1, {[(U.map Prod.snd).sum]}⟩⟩)
  | _, _, _, _, Retag _ q, d, γ, E => q.evaluate d γ E
  | _, _, _, _, @ProvSum _ _ _m n₁ _κ is _his t q, d, γ, E =>
    let r : AnnotatedRelation T K _ := (q.evaluate d γ E).map GenRow.toAnnotated
    let keys := (r.map (fun p => (fun k => p.fst (is k) : Tuple T n₁))).dedup
    keys.map (fun g =>
      (⟨Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun _ : Fin 1 => Sum.inl
            (((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
              (fun p => t.evalPlain p.fst γ)).fold addFn 0)),
        ⟨((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
            Prod.snd).sum, 0⟩⟩ : GenRow T K (n₁ + 1)))
  | _, _, _, _, @GammaTok _ _ m n₁ n₂ _κ lab rd is _his ts fs a q keep, d, γ, E =>
    let r : AnnotatedRelation T K m := (q.evaluate d γ E).map GenRow.toAnnotated
    (Multiset.ofList (groupByKey (r.map (fun p => (fun k => p.fst (is k), p.snd)
        : AnnotatedTuple T K m → AnnotatedTuple T K n₁))).val).map (fun kv =>
      let g : Tuple T n₁ := kv.fst
      let U := Having.havingGroup is r g
      -- a filtered aggregate reads its group as an expression, as under
      -- `Gamma`: the family stays the whole group and the clause cuts
      -- only what the aggregate reads of it
      ⟨Fin.append
        (Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun j => Sum.inr ((match keep j with
            | none => AggTok.tok (AggValue.ofGroup (fs j) (ts j) U γ)
            | some φ =>
                AggTok.expr (AggExpr.ofGroupWhen (fs j) (ts j) φ.keeps U γ)).setFam
              (lab, List.ofFn g,
                ctxKey rd γ))))
        (fun _ : Fin 1 => Sum.inl
          (((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
            (fun p => a.evalPlain p.fst γ)).fold addFn 0)),
       ⟨1, {U.map Prod.snd}⟩⟩)
  | _, _, _, _, @Win _ _ n _m _p κ' lab rd P O o w t f q _hrr dist keep, d, γ, E =>
    let rows := q.evaluate d γ E
    -- the relation the token is read over: what the window reads of each
    -- row (`ColKind.readTuple`), carrying the row's annotation
    let r : AnnotatedRelation T K n := rows.map (GenRow.readAnnotated κ')
    -- each row keeps its columns, its annotation and its pending factors,
    -- and gains its token: a window removes no row and creates no group
    rows.map (fun x =>
      ValueFrame.windowGenRow lab
        (ctxKey rd γ)
        κ' P O o w t f keep r x γ dist)
  | _, _, _, _, @WinExpr _ _ n _m _p _na lab rd P O o ws ts fs g q keeps, d, γ, E =>
    let r : AnnotatedRelation T K n := (q.evaluate d γ E).map GenRow.toAnnotated
    let occ := OccFam.ofSorted r
    -- the column is an expression over the union of the frames, which the
    -- operator knows because it is what the frames are computed from; a
    -- leaf's own `FILTER` clause cuts what that leaf reads of the family
    (OccFam.mk occ.size (fun i =>
      (⟨Fin.snoc (fun k => (Sum.inl ((occ.row i).fst k) : GenValue T K))
          (Sum.inr ((AggTok.expr
            (ValueFrame.exprOfWhen P O o ws ts fs g keeps occ i γ)).setFam
              (lab, List.ofFn (occ.row i).fst,
                ctxKey rd
                  γ))),
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
theorem AggQueryIn.evaluate_Apply {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQuery T n₁ κ₁) (q₂ : AggQueryIn T n₁ n₂ κ₂)
    (d : AnnotatedDatabase T K) (E : EvalEnv T K) :
    (AggQueryIn.Apply q₁ q₂).evaluate d (fun _ => 0) E
      = (q₁.evaluate d (fun _ => 0) E).bind (fun x =>
          (q₂.evaluate d (GenRow.plainTuple x.fst)
            (E.withCtx (Fin.append x.fst (E.ctxAt 0 (fun _ => 0))))).map (fun y =>
            (⟨Fin.append x.fst y.fst,
              ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
              : GenRow T K (n₁ + n₂)))) := by
  simp only [AggQueryIn.evaluate, Fin.append_nil]

/-- The final annotated relation computed by a general query: evaluate,
then finalize every row. -/
noncomputable def AggQueryIn.evaluateAnnotated {c n : ℕ} {κ : Fin n → ColKind} {l : List
    (String × ℕ)}
    (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) (E : EvalEnv T K := {}) : AnnotatedRelation T K n :=
  (q.evaluate d γ E).map GenRow.toAnnotated

/-! ## What the recursions compute, and when the bound drops out -/

/-- The round function of `Mu`: the body read with the name bound to the
previous round. A round is a bag of general rows, aggregate columns
included. -/
noncomputable def AggQueryIn.muStep {c n : ℕ} {κ : Fin n → ColKind} (s : String)
    (q₁ : AggQueryIn T c n κ [(s, n)]) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) (E : EvalEnv T K := {}) :
    Multiset (GenRow T K n) → Multiset (GenRow T K n) :=
  fun X => q₁.evaluate d γ (E.assignHole s X)

/-- The round function of `MuSet`: `ε(q₀ ⊎ q₁)` read with the name bound
to the previous round. -/
noncomputable def AggQueryIn.muSetStep {c n : ℕ} (s : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (d : AnnotatedDatabase T K)
    (γ : Fin c → T := fun _ => 0) (E : EvalEnv T K := {}) :
    AnnotatedRelation T K n → AnnotatedRelation T K n :=
  fun X => AnnotatedRelation.dedupAnn
    (q₀.evaluateAnnotated d γ E
      + q₁.evaluateAnnotated d γ (E.assignHole s (X.map GenRow.ofAnnotated)))

/-- `Mu` is the sum of its rounds up to the first empty one. -/
theorem AggQueryIn.evaluate_Mu {c n : ℕ} {κ : Fin n → ColKind} (s : String)
    (q₀ : AggQueryIn T c n κ) (q₁ : AggQueryIn T c n κ [(s, n)])
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.Mu s q₀ q₁).evaluate d γ E
      = muSumFix (AggQueryIn.muStep s q₁ d γ E) (q₀.evaluate d γ E) :=
  rfl

/-- `MuSet` is the round its iteration settles at. -/
theorem AggQueryIn.evaluate_MuSet {c n : ℕ} (s : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.MuSet s q₀ q₁).evaluate d γ E
      = (muFix (AggQueryIn.muSetStep s q₀ q₁ d γ E)).map GenRow.ofAnnotated :=
  rfl

/-- **An empty round computes `Mu`.** Given a round that is empty and a
round function that keeps an empty round empty – which is what the
semantics asks for in asking that some round be empty – the query's value
is the bounded sum up to that round. This is how a computation witnesses
the semantics, the round count being no part of the query. -/
theorem AggQueryIn.evaluate_Mu_of_empty {c n : ℕ} {κ : Fin n → ColKind} {k : ℕ} (s : String)
    (q₀ : AggQueryIn T c n κ) (q₁ : AggQueryIn T c n κ [(s, n)])
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (h0 : AggQueryIn.muStep s q₁ d γ E 0 = 0)
    (hk : (AggQueryIn.muStep s q₁ d γ E)^[k + 1] (q₀.evaluate d γ E) = 0) :
    (AggQueryIn.Mu s q₀ q₁).evaluate d γ E
      = muSum (AggQueryIn.muStep s q₁ d γ E) k (q₀.evaluate d γ E) := by
  rw [AggQueryIn.evaluate_Mu, muSumFix_eq_of_empty h0 hk]

/-- **A repeating round computes `MuSet`.** -/
theorem AggQueryIn.evaluate_MuSet_of_fix {c n : ℕ} {j : ℕ} (s : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K)
    (hj : AggQueryIn.muSetStep s q₀ q₁ d γ E
        (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) j)
      = muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) j) :
    (AggQueryIn.MuSet s q₀ q₁).evaluate d γ E
      = (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) j).map GenRow.ofAnnotated := by
  rw [AggQueryIn.evaluate_MuSet, muFix_eq_of_fix hj]

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
      (Sum.inr (AggTok.tok (ValueFrame.tokenOfDist P O o w t f dist X x γ))), ⟨x.snd, 0⟩⟩

/-- **The `Win` case of the evaluator, read off the relation.** The output is
the input relation mapped row by row, each row gaining the token its relation
gives it. This is the form every theorem about the operator uses; that it is
legitimate – that an occurrence's token is determined by the relation even
though its frame is not determined by its row – is `ValueFrame.tokenOf`. -/
theorem AggQueryIn.evaluate_Win_eq {lab : ℕ} {c n m p : ℕ} {rd : Fin c → Bool} {κ : Fin n → ColKind}
    (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (q : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t)
    (d : AnnotatedDatabase T K) {γ : Fin c → T} {E : EvalEnv T K} :
    (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist).evaluate d γ E
      = (q.evaluate d γ E).map
          (fun x => ValueFrame.windowGenRow lab
            (ctxKey rd γ)
            κ P O o w t f none ((q.evaluate d γ E).map (GenRow.readAnnotated κ)) x γ dist) := rfl

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
  | .aggTermOf k _ t => t.unary (u k)
  | .provTerm t => t.evalPlain u γ

/-- The value a window's added column takes on a row of a plain relation:
the aggregate of the term over that row's frame, read off the relation. -/
def ValueFrame.windowValue {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (R : Relation T n) (u : Tuple T n)
    (γ : Fin c → T := fun _ => 0) : T :=
  f ((ValueFrame.frameListOf (α := Tuple T n) id P O o w R u).map
    (fun v => t.eval v γ))

/-- **The value a window's added column takes under a `FILTER`
clause**: the aggregate over the rows of the frame the clause keeps. -/
def ValueFrame.windowValueWhen {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (keep : Tuple T n → Bool)
    (R : Relation T n) (u : Tuple T n) (γ : Fin c → T := fun _ => 0) : T :=
  f (((ValueFrame.frameListOf (α := Tuple T n) id P O o w R u).filter keep).map
    (fun v => t.eval v γ))

/-- **The value one leaf of a multi-frame window takes**: the aggregate
over its frame, over the part its own `FILTER` clause keeps where it
carries one. -/
def ValueFrame.windowValueOpt {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (keep : Option (Selection T n))
    (R : Relation T n) (u : Tuple T n) (γ : Fin c → T := fun _ => 0) : T :=
  match keep with
  | none => ValueFrame.windowValue P O o w t f R u γ
  | some φ => ValueFrame.windowValueWhen P O o w t f φ.keeps R u γ

@[simp] theorem ValueFrame.windowValueOpt_none {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (R : Relation T n) (u : Tuple T n) (γ : Fin c → T) :
    ValueFrame.windowValueOpt P O o w t f none R u γ
      = ValueFrame.windowValue P O o w t f R u γ := rfl

@[simp] theorem ValueFrame.windowValueOpt_some {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (φ : Selection T n) (R : Relation T n) (u : Tuple T n) (γ : Fin c → T) :
    ValueFrame.windowValueOpt P O o w t f (some φ) R u γ
      = ValueFrame.windowValueWhen P O o w t f φ.keeps R u γ := rfl

/-- A window's value reads the context only through its term. -/
theorem ValueFrame.windowValueOpt_congr_ctx {c n m p : ℕ}
    {P : Tuple (Fin n) m} {O : Tuple (Fin n) p} {o : OrderSpec p}
    {w : ValueFrame T p} {t : TermIn T c n} {f : SeqAggFunc T} {keep : Option (Selection T n)}
    {R : Relation T n} {u : Tuple T n} {γ γ' : Fin c → T} (h : ∀ x, t.eval x γ = t.eval x γ') :
    ValueFrame.windowValueOpt P O o w t f keep R u γ
      = ValueFrame.windowValueOpt P O o w t f keep R u γ' := by
  have hf : (fun x => t.eval x γ) = fun x => t.eval x γ' := funext h
  cases keep <;>
    simp only [ValueFrame.windowValueOpt, ValueFrame.windowValue,
      ValueFrame.windowValueWhen, hf]

/-- The same, without a `FILTER` clause. -/
theorem ValueFrame.windowValue_congr_ctx {c n m p : ℕ}
    {P : Tuple (Fin n) m} {O : Tuple (Fin n) p} {o : OrderSpec p}
    {w : ValueFrame T p} {t : TermIn T c n} {f : SeqAggFunc T}
    {R : Relation T n} {u : Tuple T n} {γ γ' : Fin c → T} (h : ∀ x, t.eval x γ = t.eval x γ') :
    ValueFrame.windowValue P O o w t f R u γ = ValueFrame.windowValue P O o w t f R u γ' :=
  ValueFrame.windowValueOpt_congr_ctx (keep := none) h

/-- And with one. -/
theorem ValueFrame.windowValueWhen_congr_ctx {c n m p : ℕ}
    {P : Tuple (Fin n) m} {O : Tuple (Fin n) p} {o : OrderSpec p}
    {w : ValueFrame T p} {t : TermIn T c n} {f : SeqAggFunc T} {keep : Tuple T n → Bool}
    {R : Relation T n} {u : Tuple T n} {γ γ' : Fin c → T} (h : ∀ x, t.eval x γ = t.eval x γ') :
    ValueFrame.windowValueWhen P O o w t f keep R u γ
      = ValueFrame.windowValueWhen P O o w t f keep R u γ' := by
  have hf : (fun x => t.eval x γ) = fun x => t.eval x γ' := funext h
  simp only [ValueFrame.windowValueWhen, hf]

/-- **The plain evaluator**: standard multiset semantics, with `Gamma`
computing the aggregate of each group's full occurrence sequence (in the
canonical `≼` order of `Relation.groupSeq`) and every selection filtering
classically. `Diff` is the all-or-nothing difference of
`Query.evaluate`. -/
noncomputable def AggQueryIn.evaluatePlain : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List
    (String × ℕ)} →
    AggQueryIn T c n κ l → Database T →
    (γ : Fin c → T := fun _ => 0) → Relation T n
  | _, n, _, _, Rel _ s, d, _ =>
    match d.find n s with
    | none => (∅ : Multiset (Tuple T n))
    | some rn => rn
  | _, n, _, _, Hole _ s _, d, _ =>
    match d.find n s with
    | none => (∅ : Multiset (Tuple T n))
    | some rn => rn
  | _, _, _, _, @Param _ _ m pv _, _, γ =>
    ({(fun k => _root_.Sum.elim id γ (pv k) : Tuple T m)} : Multiset (Tuple T m))
  | _, _, _, _, Empty, _, _ => (0 : Relation T 0)
  | _, _, _, _, @Proj _ _ n _ κ _ ps q, d, γ =>
    (q.evaluatePlain d γ).map (fun u => (fun j => (ps j).evalPlain u γ))
  | _, _, _, _, Sel φ q _, d, γ =>
    @Multiset.filter _ (fun u => φ.holdsPlain u γ)
      (fun u => φ.decHoldsPlain u γ) (q.evaluatePlain d γ)
  | _, _, _, _, Prod q₁ q₂, d, γ => q₁.evaluatePlain d γ * q₂.evaluatePlain d γ
  | _, _, _, _, @Apply _ _ n₁ _ _ _ _ q₁ q₂, d, γ =>
    (q₁.evaluatePlain d γ).bind (fun u =>
      (q₂.evaluatePlain d (Fin.append u γ)).map (fun v =>
        (Fin.append u v : Tuple T (n₁ + _))))
  | _, _, _, _, Sum q₁ q₂, d, γ => q₁.evaluatePlain d γ + q₂.evaluatePlain d γ
  | _, _, _, _, Dedup q, d, γ => (q.evaluatePlain d γ).dedup
  | _, _, _, _, Explode _ _ q, d, γ => q.evaluatePlain d γ
  | _, _, _, _, Mu s q₀ q₁, d, γ =>
    muSumFix (fun X => q₁.evaluatePlain (d.assign s X) γ)
      (q₀.evaluatePlain d γ)
  | _, _, _, _, MuSet s q₀ q₁, d, γ =>
    muFix (fun X => (q₀.evaluatePlain d γ + q₁.evaluatePlain (d.assign s X) γ).dedup)
  | _, _, _, _, Diff q₁ q₂, d, γ =>
    let r₂ : Multiset (Tuple T _) := q₂.evaluatePlain d γ
    (q₁.evaluatePlain d γ).filter (fun t => t ∉ r₂)
  | _, _, _, _, @Gamma _ _ _m n₁ n₂ _lab _rd is ts fs q keep ord, d, γ =>
    let r := q.evaluatePlain d γ
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append g
      (fun j => (fs j)
        ((Relation.groupSeqOptOrd is ord r g (keep j)).map
          (fun v => (ts j).eval v γ))))
  | _, _, _, _, @GammaScalar _ _ _m n₂ _lab _rd ts fs q ord, d, γ =>
    let r := q.evaluatePlain d γ
    (Multiset.ofList [(fun j => (fs j)
      ((Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord r
        (fun k : Fin 0 => k.elim0)).map (fun v => (ts j).eval v γ))
          : Tuple T n₂)] : Relation T n₂)
  | _, _, _, _, @GammaNest _ _ _m n₁ _κ _lab _rd is _his p f q, d, γ =>
    let r := q.evaluatePlain d γ
    let key : Tuple T _ → Tuple T n₁ := fun u => fun k => u (is k)
    ((r.map key).dedup).map (fun g => Fin.append g (fun _ : Fin 1 =>
      -- the group as a bag, which is what the aggregate reads: it is a
      -- function of one, so no `Relation.groupSeq` is needed to list it
      f ((r.filter (fun u => key u = g)).map (fun u => p.evalPlain u γ))))
  | _, _, _, _, Retag _ q, d, γ => q.evaluatePlain d γ
  | _, _, _, _, @ProvSum _ _ _m n₁ _κ is _his t q, d, γ =>
    let r := q.evaluatePlain d γ
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append g (fun _ : Fin 1 =>
      ((r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map
        (fun u => t.evalPlain u γ)).fold addFn 0))
  | _, _, _, _, @GammaTok _ _ _m n₁ n₂ _κ _lab _rd is _his ts fs a q keep, d, γ =>
    let r := q.evaluatePlain d γ
    let keys := (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
    keys.map (fun g => Fin.append
      (Fin.append g
        (fun j => (fs j)
          ((Relation.groupSeqOpt is r g (keep j)).map
            (fun v => (ts j).eval v γ))))
      (fun _ : Fin 1 =>
        ((r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map
          (fun u => a.evalPlain u γ)).fold addFn 0))
  | _, _, _, _, @Win _ _ n _m _p κ' _lab _rd P O o w t f q _hrr dist keep, d, γ =>
    let rows := q.evaluatePlain d γ
    -- the window reads the regular columns of each row, as the annotated
    -- evaluator does, so the two agree on what a frame holds
    let read := rows.map (ColKind.readTuple κ')
    rows.map (fun u =>
      (Fin.snoc u (ValueFrame.windowValueOpt P O o w t
          (if dist then f.distinct else f) keep read
            (ColKind.readTuple κ' u) γ)
        : Tuple T (n + 1)))
  | _, _, _, _, @WinExpr _ _ n _m _p _na _lab _rd P O o ws ts fs g q keeps, d, γ =>
    let occ := OccFam.ofSorted (q.evaluatePlain d γ)
    (OccFam.mk occ.size (fun i =>
      (Fin.snoc (occ.row i)
        (g (fun l => (fs l)
          ((match keeps l with
            | none => ValueFrame.frameSeqOn (α := Tuple T n) id P O o (ws l) occ i
            | some φ =>
                (ValueFrame.frameSeqOn (α := Tuple T n) id P O o (ws l) occ i).filter
                  φ.keeps).map
            (fun v => (ts l).eval v γ))))
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

/-- **The `Gamma` case of the plain evaluator with no `FILTER`
clause**: each group's aggregate reads the whole group, the clause-less
`List.filter` keeping every row. This is the form every result about an
unfiltered grouping uses. -/
theorem AggQueryIn.evaluatePlain_Gamma_eq {lab : ℕ} {c m n₁ n₂ : ℕ} {rd : Fin c → Bool}
    (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (d : Database T)
    {γ : Fin c → T} :
    (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q).evaluatePlain d γ
      = ((q.evaluatePlain d γ).map
          (fun u => (fun k => u (is k) : Tuple T n₁))).dedup.map
        (fun g => Fin.append g (fun j => (fs j)
          ((Relation.groupSeq is (q.evaluatePlain d γ) g).map
            (fun v => (ts j).eval v γ)))) := by
  rw [AggQueryIn.evaluatePlain]
  simp only [Relation.groupSeqOptOrd_none, Relation.groupSeqOrd_unord]

/-- **The `Win` case of the plain evaluator, read off the relation.** -/
theorem AggQueryIn.evaluatePlain_Win_eq {lab : ℕ} {c n m p : ℕ} {rd : Fin c → Bool}
    {κ : Fin n → ColKind}
    (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (q : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t) (d : Database T)
    {γ : Fin c → T} :
    (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist).evaluatePlain d γ
      = (q.evaluatePlain d γ).map (fun u : Tuple T n =>
          (Fin.snoc u
            (ValueFrame.windowValue P O o w t
              (if dist then f.distinct else f)
              ((q.evaluatePlain d γ).map (ColKind.readTuple κ))
              (ColKind.readTuple κ u) γ)
            : Tuple T (n + 1))) := rfl

/-- The row a window gives a row of its input relation under a `FILTER`
clause: as `ValueFrame.windowRow`, with the clause's column – an
aggregate *expression* over the whole frame, the clause cutting what its
leaf reads (`ValueFrame.exprWhenOf`). -/
def ValueFrame.windowRowWhen {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (keep : Tuple T n → Bool)
    (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n)
    (γ : Fin c → T := fun _ => 0) (dist : Bool := false) :
    GenRow T K (n + 1) :=
  ⟨Fin.snoc (fun k => (Sum.inl (x.fst k) : GenValue T K))
      (Sum.inr (AggTok.expr
        (ValueFrame.exprWhenOf P O o w t f dist keep X x γ))),
    ⟨x.snd, 0⟩⟩

/-- **The `Win` case of the evaluator under a `FILTER` clause**, read off
the relation, as `AggQueryIn.evaluate_Win_eq` is without one. -/
theorem AggQueryIn.evaluate_Win_eq_when {lab : ℕ} {c n m p : ℕ} {rd : Fin c → Bool}
    {κ : Fin n → ColKind}
    (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool) (φ : Selection T n)
    (q : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t)
    (d : AnnotatedDatabase T K) {γ : Fin c → T} {E : EvalEnv T K} :
    (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist (some φ)).evaluate d γ E
      = (q.evaluate d γ E).map
          (fun x => ValueFrame.windowGenRow lab
            (ctxKey rd γ)
            κ P O o w t f (some φ) ((q.evaluate d γ E).map (GenRow.readAnnotated κ)) x γ
            dist) := rfl

/-- **The `Win` case of the plain evaluator under a `FILTER` clause.** -/
theorem AggQueryIn.evaluatePlain_Win_eq_when {lab : ℕ} {c n m p : ℕ} {rd : Fin c → Bool}
    {κ : Fin n → ColKind}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (φ : Selection T n) (q : AggQueryIn T c n κ)
    (hrr : WinReadsReg κ P O t)
    (d : Database T) {γ : Fin c → T} :
    (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist (some φ)).evaluatePlain d γ
      = (q.evaluatePlain d γ).map (fun u : Tuple T n =>
          (Fin.snoc u
            (ValueFrame.windowValueWhen P O o w t
              (if dist then f.distinct else f) φ.keeps
              ((q.evaluatePlain d γ).map (ColKind.readTuple κ))
              (ColKind.readTuple κ u) γ)
            : Tuple T (n + 1))) := rfl

/-- **The `Win` case of the plain evaluator, clause or no clause**, which
is the form a recursion over the syntax needs: the frame is read through
`ValueFrame.windowValueOpt`, which is the unfiltered reading where there
is no clause and the cut one where there is. -/
theorem AggQueryIn.evaluatePlain_Win_eq_opt {lab : ℕ} {c n m p : ℕ} {rd : Fin c → Bool}
    {κ : Fin n → ColKind}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (keep : Option (Selection T n))
    (q : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t) (d : Database T)
    {γ : Fin c → T} :
    (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep).evaluatePlain d γ
      = (q.evaluatePlain d γ).map (fun u : Tuple T n =>
          (Fin.snoc u
            (ValueFrame.windowValueOpt P O o w t
              (if dist then f.distinct else f) keep
              ((q.evaluatePlain d γ).map (ColKind.readTuple κ))
              (ColKind.readTuple κ u) γ)
            : Tuple T (n + 1))) := by
  cases keep with
  | none => exact AggQueryIn.evaluatePlain_Win_eq P O o w t f dist q hrr d
  | some φ =>
    exact AggQueryIn.evaluatePlain_Win_eq_when P O o w t f dist φ q hrr d

/-- **The `WinExpr` case of the plain evaluator, read off the
relation**: each leaf aggregates over its own frame, and `g` combines
the values. -/
theorem AggQueryIn.evaluatePlain_WinExpr_eq {lab : ℕ} {c n m p na : ℕ} {rd : Fin c → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin na → ValueFrame T p) (ts : Fin na → TermIn T c n)
    (fs : Fin na → SeqAggFunc T) (g : (Fin na → T) → T)
    (q : AggQueryIn T c n (ColKind.allReg n)) (d : Database T)
    {γ : Fin c → T} :
    (AggQueryIn.WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q).evaluatePlain d γ
      = (q.evaluatePlain d γ).map (fun u : Tuple T n =>
          (Fin.snoc u
            (g (fun l => ValueFrame.windowValue P O o (ws l) (ts l) (fs l)
              (q.evaluatePlain d γ) u γ))
            : Tuple T (n + 1))) := by
  conv_rhs => rw [← OccFam.toMultiset_ofSorted (q.evaluatePlain d γ)]
  rw [OccFam.toMultiset_map]
  refine congrArg OccFam.toMultiset (OccFam.ext_cast rfl (fun i => ?_))
  show (_ : Tuple T (n + 1))
    = Fin.snoc _ (g (fun l => ValueFrame.windowValue P O o (ws l) (ts l)
        (fs l) _ _ _))
  unfold ValueFrame.windowValue
  dsimp only [Fin.cast_eq_self]
  refine congrArg (Fin.snoc _) (congrArg g (funext (fun l => ?_)))
  rw [ValueFrame.frameSeqOn_eq_frameListOf, OccFam.toMultiset_ofSorted]

/-- **The `WinExpr` case of the plain evaluator under `FILTER` clauses**:
each leaf aggregates over the part of its own frame its clause keeps. -/
theorem AggQueryIn.evaluatePlain_WinExpr_eq_when {lab : ℕ} {c n m p na : ℕ} {rd : Fin c → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin na → ValueFrame T p) (ts : Fin na → TermIn T c n)
    (fs : Fin na → SeqAggFunc T) (g : (Fin na → T) → T)
    (keeps : Fin na → Option (Selection T n))
    (q : AggQueryIn T c n (ColKind.allReg n)) (d : Database T)
    {γ : Fin c → T} :
    (AggQueryIn.WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps).evaluatePlain d γ
      = (q.evaluatePlain d γ).map (fun u : Tuple T n =>
          (Fin.snoc u
            (g (fun l => ValueFrame.windowValueOpt P O o (ws l) (ts l) (fs l)
              (keeps l) (q.evaluatePlain d γ) u γ))
            : Tuple T (n + 1))) := by
  conv_rhs => rw [← OccFam.toMultiset_ofSorted (q.evaluatePlain d γ)]
  rw [OccFam.toMultiset_map]
  refine congrArg OccFam.toMultiset (OccFam.ext_cast rfl (fun i => ?_))
  show (_ : Tuple T (n + 1))
    = Fin.snoc _ (g (fun l => ValueFrame.windowValueOpt P O o (ws l) (ts l)
        (fs l) (keeps l) _ _ _))
  dsimp only [Fin.cast_eq_self]
  refine congrArg (Fin.snoc _) (congrArg g (funext (fun l => ?_)))
  cases keeps l with
  | none =>
    unfold ValueFrame.windowValueOpt ValueFrame.windowValue
    rw [ValueFrame.frameSeqOn_eq_frameListOf, OccFam.toMultiset_ofSorted]
  | some φ =>
    unfold ValueFrame.windowValueOpt ValueFrame.windowValueWhen
    rw [ValueFrame.frameSeqOn_eq_frameListOf, OccFam.toMultiset_ofSorted]

/-- Strip a general query of the constructs whose annotated data part
keeps rows the classical semantics removes: differences (annotated `Diff`
never removes tuple slots) and selections containing an aggregate atom
(the annotated evaluator keeps classically-failing rows annotated `𝟘`,
as ProvSQL emits them). The data-part adequacy of `evaluateAnnotated`
is stated against the plain evaluation of the stripped query, mirroring
`Query.stripDiff` in `Provenance.QueryAdequacy`. -/
def AggQueryIn.stripAgg : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → AggQueryIn T c n κ l
  | _, _, _, _, Rel n s => Rel n s
  | _, _, _, _, Hole n s κ => Hole n s κ
  | _, _, _, _, Param pv ρ => Param pv ρ
  | _, _, _, _, Empty => Empty
  | _, _, _, _, Proj ps q => Proj ps q.stripAgg
  | _, _, _, _, Sel φ q hφ =>
    if φ.hasAggAtom then q.stripAgg else Sel φ q.stripAgg hφ
  | _, _, _, _, Prod q₁ q₂ => Prod q₁.stripAgg q₂.stripAgg
  | _, _, _, _, Apply q₁ q₂ => Apply q₁.stripAgg q₂.stripAgg
  | _, _, _, _, Sum q₁ q₂ => Sum q₁.stripAgg q₂.stripAgg
  | _, _, _, _, Dedup q => Dedup q.stripAgg
  | _, _, _, _, Diff q₁ _ => q₁.stripAgg
  | _, _, _, _, Explode k h q => Explode k h q.stripAgg
  | _, _, _, _, Mu s q₀ q₁ => Mu s q₀.stripAgg q₁.stripAgg
  | _, _, _, _, MuSet s q₀ q₁ => MuSet s q₀.stripAgg q₁.stripAgg
  | _, _, _, _, Gamma (lab := lab) (rd := rd) is ts fs q keep ord =>
      Gamma (lab := lab) (rd := rd) is ts fs q.stripAgg keep ord
  | _, _, _, _, GammaScalar (lab := lab) (rd := rd) ts fs q ord =>
      GammaScalar (lab := lab) (rd := rd) ts fs q.stripAgg ord
  | _, _, _, _, GammaNest (lab := lab) (rd := rd) is his p f q =>
      GammaNest (lab := lab) (rd := rd) is his p f q.stripAgg
  | _, _, _, _, ProvSum is his t q => ProvSum is his t q.stripAgg
  | _, _, _, _, Retag h q => Retag h q.stripAgg
  | _, _, _, _, GammaTok (lab := lab) (rd := rd) is his ts fs a q keep =>
      GammaTok (lab := lab) (rd := rd) is his ts fs a q.stripAgg keep
  | _, _, _, _, Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep =>
      Win (lab := lab) (rd := rd) P O o w t f q.stripAgg hrr dist keep
  | _, _, _, _, WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps =>
      WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q.stripAgg keeps

/-- No plan-level provenance aggregation. The possible-world
metatheorems (random-world commutation, PQE) are about source queries;
`ProvSum` is a rewriting-target operator whose deterministic group sum
is not world-faithful – exactly as the classical `Agg` was excluded from
the annotated evaluators. -/
def AggQueryIn.noProvSum : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noProvSum
  | _, _, _, _, .Sel _ q _ => q.noProvSum
  | _, _, _, _, .Prod q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, _, .Apply q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, _, .Sum q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, _, .Dedup q => q.noProvSum
  | _, _, _, _, .Diff q₁ q₂ => q₁.noProvSum ∧ q₂.noProvSum
  | _, _, _, _, .Explode _ _ q => q.noProvSum
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noProvSum ∧ q₁.noProvSum
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noProvSum ∧ q₁.noProvSum
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noProvSum
  | _, _, _, _, .GammaScalar _ _ q _ => q.noProvSum
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noProvSum
  | _, _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, _, .Retag _ q => q.noProvSum
  | _, _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noProvSum
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noProvSum

/-! ## Terms reading the context only where it is plain

A term reads a parameter as a plain value through `outer k`; that is the
right reading only of a parameter that is not aggregate, an aggregate one
being read, world by world, through the leaf `AggQueryIn.Param`.
`outerOk ok` says every `outer k` of a term has `ok k`, and the readings
agree on contexts agreeing there. -/

/-- Every outer column the term reads satisfies `ok`. -/
def TermIn.outerOk {c n : ℕ} (ok : Fin c → Prop) : TermIn T c n → Prop
  | .const _ => True
  | .outer k => ok k
  | .index _ => True
  | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ | .coalesce t₁ t₂ => t₁.outerOk ok ∧ t₂.outerOk ok
  | .caseWhen _ t₁ t₂ t₃ t₄ => t₁.outerOk ok ∧ t₂.outerOk ok ∧ t₃.outerOk ok ∧ t₄.outerOk ok

def TermGIn.outerOk {c n : ℕ} {κ : Fin n → ColKind} (ok : Fin c → Prop) :
    TermGIn T c κ → Prop
  | .const _ => True
  | .outer k => ok k
  | .index _ _ => True
  | .provIndex _ _ => True
  | .cmpAgg _ _ _ t => t.outerOk ok
  | .chiGate _ t₁ t₂ | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ | .coalesce t₁ t₂ =>
      t₁.outerOk ok ∧ t₂.outerOk ok
  | .caseWhen _ t₁ t₂ t₃ t₄ => t₁.outerOk ok ∧ t₂.outerOk ok ∧ t₃.outerOk ok ∧ t₄.outerOk ok

def GenPredIn.outerOk {c n : ℕ} {κ : Fin n → ColKind} (ok : Fin c → Prop) :
    GenPredIn T c κ → Prop
  | .cmp _ t₁ t₂ => t₁.outerOk ok ∧ t₂.outerOk ok
  | .aggCmp _ _ _ t => t.outerOk ok
  | .aggRange _ _ _ t₁ _ t₂ => t₁.outerOk ok ∧ t₂.outerOk ok
  | .and φ ψ | .or φ ψ => φ.outerOk ok ∧ ψ.outerOk ok
  | .not φ => φ.outerOk ok

def ProjColIn.outerOk {c n : ℕ} {κ : Fin n → ColKind} (ok : Fin c → Prop) :
    ProjColIn T c κ → Prop
  | .term t => t.outerOk ok
  | .token _ _ => True
  | .aggTerm _ _ _ => True
  | .aggTermOf _ _ _ => True
  | .provTerm t => t.outerOk ok

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem TermIn.eval_congr_outerOk [ValueType T] {c n : ℕ} {ok : Fin c → Prop} {γ γ' : Fin c → T}
    (hγ : ∀ k, ok k → γ k = γ' k) (u : Tuple T n) :
    ∀ t : TermIn T c n, t.outerOk ok → t.eval u γ = t.eval u γ'
  | .const _, _ => rfl
  | .outer k, h => hγ k h
  | .index _, _ => rfl
  | .add t₁ t₂, h => congrArg₂ (· + ·) (eval_congr_outerOk hγ u t₁ h.1)
      (eval_congr_outerOk hγ u t₂ h.2)
  | .sub t₁ t₂, h => by
    show HSub.hSub _ _ = HSub.hSub _ _
    rw [eval_congr_outerOk hγ u t₁ h.1, eval_congr_outerOk hγ u t₂ h.2]
  | .mul t₁ t₂, h => congrArg₂ (· * ·) (eval_congr_outerOk hγ u t₁ h.1)
      (eval_congr_outerOk hγ u t₂ h.2)
  | .caseWhen op t₁ t₂ t₃ t₄, h => by
    show (if _ then _ else _) = (if _ then _ else _)
    rw [eval_congr_outerOk hγ u t₁ h.1, eval_congr_outerOk hγ u t₂ h.2.1,
      eval_congr_outerOk hγ u t₃ h.2.2.1, eval_congr_outerOk hγ u t₄ h.2.2.2]
  | .coalesce t₁ t₂, h => by
    show (if _ then _ else _) = (if _ then _ else _)
    rw [eval_congr_outerOk hγ u t₁ h.1, eval_congr_outerOk hγ u t₂ h.2]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem TermGIn.evalPlain_congr_outerOk {c n : ℕ} {κ : Fin n → ColKind} {ok : Fin c → Prop}
    {γ γ' : Fin c → T} (hγ : ∀ k, ok k → γ k = γ' k) (u : Tuple T n) :
    ∀ t : TermGIn T c κ, t.outerOk ok → t.evalPlain u γ = t.evalPlain u γ'
  | .const _, _ => rfl
  | .outer k, h => hγ k h
  | .index _ _, _ => rfl
  | .provIndex _ _, _ => rfl
  | .cmpAgg _ _ _ _, _ => rfl
  | .chiGate _ _ _, _ => rfl
  | .add t₁ t₂, h => congrArg₂ (· + ·) (evalPlain_congr_outerOk hγ u t₁ h.1)
      (evalPlain_congr_outerOk hγ u t₂ h.2)
  | .sub t₁ t₂, h => by
    show HSub.hSub _ _ = HSub.hSub _ _
    rw [evalPlain_congr_outerOk hγ u t₁ h.1, evalPlain_congr_outerOk hγ u t₂ h.2]
  | .mul t₁ t₂, h => congrArg₂ (· * ·) (evalPlain_congr_outerOk hγ u t₁ h.1)
      (evalPlain_congr_outerOk hγ u t₂ h.2)
  | .caseWhen op t₁ t₂ t₃ t₄, h => by
    show (if _ then _ else _) = (if _ then _ else _)
    rw [evalPlain_congr_outerOk hγ u t₁ h.1, evalPlain_congr_outerOk hγ u t₂ h.2.1,
      evalPlain_congr_outerOk hγ u t₃ h.2.2.1, evalPlain_congr_outerOk hγ u t₄ h.2.2.2]
  | .coalesce t₁ t₂, h => by
    show (if _ then _ else _) = (if _ then _ else _)
    rw [evalPlain_congr_outerOk hγ u t₁ h.1, evalPlain_congr_outerOk hγ u t₂ h.2]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem ProjColIn.evalPlain_congr_outerOk {c n : ℕ} {κ : Fin n → ColKind} {ok : Fin c → Prop}
    {γ γ' : Fin c → T} (hγ : ∀ k, ok k → γ k = γ' k) (u : Tuple T n) :
    ∀ p : ProjColIn T c κ, p.outerOk ok → p.evalPlain u γ = p.evalPlain u γ'
  | .term t, h => TermGIn.evalPlain_congr_outerOk hγ u t h
  | .token _ _, _ => rfl
  | .aggTerm _ _ _, _ => rfl
  | .aggTermOf _ _ _, _ => rfl
  | .provTerm t, h => TermGIn.evalPlain_congr_outerOk hγ u t h

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenPredIn.evalPlain3_congr_outerOk {c n : ℕ} {κ : Fin n → ColKind} {ok : Fin c → Prop}
    {γ γ' : Fin c → T} (hγ : ∀ k, ok k → γ k = γ' k) (u : Tuple T n) :
    ∀ φ : GenPredIn T c κ, φ.outerOk ok → φ.evalPlain3 u γ = φ.evalPlain3 u γ'
  | .cmp op t₁ t₂, h => by
    show op.eval3 _ _ = op.eval3 _ _
    rw [TermGIn.evalPlain_congr_outerOk hγ u t₁ h.1, TermGIn.evalPlain_congr_outerOk hγ u t₂ h.2]
  | .aggCmp k _ op t, h => by
    show op.eval3 _ _ = op.eval3 _ _
    rw [TermGIn.evalPlain_congr_outerOk hγ u t h]
  | .aggRange k _ op₁ t₁ op₂ t₂, h => by
    show Kleene.and _ _ = Kleene.and _ _
    rw [TermGIn.evalPlain_congr_outerOk hγ u t₁ h.1, TermGIn.evalPlain_congr_outerOk hγ u t₂ h.2]
  | .and φ ψ, h => by
    show Kleene.and _ _ = Kleene.and _ _
    rw [evalPlain3_congr_outerOk hγ u φ h.1, evalPlain3_congr_outerOk hγ u ψ h.2]
  | .or φ ψ, h => by
    show Kleene.or _ _ = Kleene.or _ _
    rw [evalPlain3_congr_outerOk hγ u φ h.1, evalPlain3_congr_outerOk hγ u ψ h.2]
  | .not φ, h => by
    show Kleene.not _ = Kleene.not _
    rw [evalPlain3_congr_outerOk hγ u φ h]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenPredIn.holdsPlain_congr_outerOk {c n : ℕ} {κ : Fin n → ColKind} {ok : Fin c → Prop}
    {γ γ' : Fin c → T} (hγ : ∀ k, ok k → γ k = γ' k) (u : Tuple T n) (φ : GenPredIn T c κ)
    (h : φ.outerOk ok) : φ.holdsPlain u γ ↔ φ.holdsPlain u γ' := by
  unfold GenPredIn.holdsPlain
  rw [GenPredIn.evalPlain3_congr_outerOk hγ u φ h]

/-- The kinds of the rounds each recursive name is bound to. -/
def HoleKinds := String → (n : ℕ) → Fin n → ColKind

/-- No name bound: every round regular. -/
def HoleKinds.empty : HoleKinds := fun _ n => ColKind.allReg n

/-- Binding a recursive name to rounds of kinds `κ`. -/
def HoleKinds.assign (HK : HoleKinds) (s : String) {n : ℕ} (κ : Fin n → ColKind) : HoleKinds :=
  fun s' m => if h : s' = s ∧ m = n then fun k => κ (Fin.cast h.2 k) else HK s' m

/-- **The query is well-kinded** in a context of kinds `ρc`, its recursive
names bound to rounds of kinds `HK`: a hole has the kinds of the rounds of
its name, a parameter leaf the kinds of the parameters it reads (a
constant being regular), and so, inside, at every apply and every
recursion. This is what the kind-indexed syntax cannot say by itself,
the context and the rounds being read through the evaluation's
environment. -/
def AggQueryIn.wellKinded : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → (Fin c → ColKind) → HoleKinds → Prop
  | _, _, _, _, .Rel _ _, _, _ => True
  | _, n, _, _, .Hole _ s κ, _, HK => ∀ k, (κ k).base = (HK s n k).base
  | _, _, _, _, .Param pv ρ, ρc, _ =>
      ∀ k, (ρ k).base = _root_.Sum.elim (fun _ => ColKind.reg) (fun j => (ρc j).base) (pv k)
  | _, _, _, _, .Empty, _, _ => True
  | _, _, _, _, .Proj ps q, ρc, HK =>
      (∀ j, (ps j).outerOk (fun k => (ρc k).base ≠ ColKind.agg)) ∧ q.wellKinded ρc HK
  | _, _, _, _, .Sel φ q _, ρc, HK =>
      φ.outerOk (fun k => (ρc k).base ≠ ColKind.agg) ∧ q.wellKinded ρc HK
  | _, _, _, _, .Prod q₁ q₂, ρc, HK => q₁.wellKinded ρc HK ∧ q₂.wellKinded ρc HK
  | _, _, _, _, @Apply _ _ _ _ κ₁ _ _ q₁ q₂, ρc, HK =>
      q₁.wellKinded ρc HK ∧ q₂.wellKinded (Fin.append κ₁ ρc) HK
  | _, _, _, _, .Sum q₁ q₂, ρc, HK => q₁.wellKinded ρc HK ∧ q₂.wellKinded ρc HK
  | _, _, _, _, .Dedup q, ρc, HK => q.wellKinded ρc HK
  | _, _, _, _, .Diff q₁ q₂, ρc, HK => q₁.wellKinded ρc HK ∧ q₂.wellKinded ρc HK
  | _, _, _, _, .Explode _ _ q, ρc, HK => q.wellKinded ρc HK
  | _, _, _, _, @Mu _ _ _ κ s q₀ q₁, ρc, HK =>
      q₀.wellKinded ρc HK ∧ q₁.wellKinded ρc (HK.assign s κ)
  | _, n, _, _, .MuSet s q₀ q₁, ρc, HK =>
      q₀.wellKinded ρc HK ∧ q₁.wellKinded ρc (HK.assign s (ColKind.allReg n))
  | _, _, _, _, .Gamma _ ts _ q _ _, ρc, HK =>
      (∀ j, (ts j).outerOk (fun k => (ρc k).base ≠ ColKind.agg)) ∧ q.wellKinded ρc HK
  | _, _, _, _, .GammaScalar ts _ q _, ρc, HK =>
      (∀ j, (ts j).outerOk (fun k => (ρc k).base ≠ ColKind.agg)) ∧ q.wellKinded ρc HK
  | _, _, _, _, .GammaNest _ _ p _ q, ρc, HK =>
      p.outerOk (fun k => (ρc k).base ≠ ColKind.agg) ∧ q.wellKinded ρc HK
  | _, _, _, _, .ProvSum _ _ t q, ρc, HK =>
      t.outerOk (fun k => (ρc k).base ≠ ColKind.agg) ∧ q.wellKinded ρc HK
  | _, _, _, _, .Retag _ q, ρc, HK => q.wellKinded ρc HK
  | _, _, _, _, .GammaTok _ _ ts _ a q _, ρc, HK =>
      (∀ j, (ts j).outerOk (fun k => (ρc k).base ≠ ColKind.agg))
        ∧ a.outerOk (fun k => (ρc k).base ≠ ColKind.agg) ∧ q.wellKinded ρc HK
  | _, _, _, _, .Win _ _ _ _ t _ q _ _ _, ρc, HK =>
      t.outerOk (fun k => (ρc k).base ≠ ColKind.agg) ∧ q.wellKinded ρc HK
  | _, _, _, _, .WinExpr _ _ _ _ ts _ _ q _, ρc, HK =>
      (∀ j, (ts j).outerOk (fun k => (ρc k).base ≠ ColKind.agg)) ∧ q.wellKinded ρc HK

/-- **The environment agrees with the kinds**: its context, at the arity
`c`, has the kinds `ρc` and the plain values `γ`, and every round it binds
to a name has the kinds `HK` gives that name. -/
def EvalEnv.Kinded (E : EvalEnv T K) {c : ℕ} (γ : Fin c → T) (ρc : Fin c → ColKind)
    (HK : HoleKinds) : Prop :=
  GenRow.Conforms ρc (E.ctxAt c γ) ∧ GenRow.plainTuple (E.ctxAt c γ) = γ
    ∧ ∀ (s : String) (n : ℕ), ∀ r ∈ E.holes s n, GenRow.Conforms (HK s n) r.fst

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Two kinds with the same base give the same conformance. -/
theorem GenRow.conforms_congr {n : ℕ} {κ κ' : Fin n → ColKind} (h : ∀ k, (κ k).base = (κ' k).base)
    (u : Tuple (GenValue T K) n) : GenRow.Conforms κ u ↔ GenRow.Conforms κ' u :=
  forall_congr' fun k => by rw [h k]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.kinded_empty {c : ℕ} (γ : Fin c → T) :
    ({} : EvalEnv T K).Kinded γ (ColKind.allReg c) HoleKinds.empty := by
  refine ⟨fun k => ?_, ?_, fun _ _ r hr => absurd hr (Multiset.notMem_zero r)⟩
  · rw [EvalEnv.empty_ctxAt]; rfl
  · rw [EvalEnv.empty_ctxAt]; rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Entering an apply's right side** at a row of its left side keeps the
environment kinded. -/
theorem EvalEnv.Kinded.enter {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T} {ρc : Fin c → ColKind}
    {HK : HoleKinds} (hE : E.Kinded γ ρc HK) {n₁ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {x : Tuple (GenValue T K) n₁} (hx : GenRow.Conforms κ₁ x) :
    (E.withCtx (Fin.append x (E.ctxAt c γ))).Kinded (Fin.append (GenRow.plainTuple x) γ)
      (Fin.append κ₁ ρc) HK := by
  refine ⟨fun k => ?_, ?_, hE.2.2⟩
  · rw [EvalEnv.ctxAt_withCtx]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Fin.append_left]; exact hx i
    · rw [Fin.append_right, Fin.append_right]; exact hE.1 j
  · rw [EvalEnv.ctxAt_withCtx]
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [GenRow.plainTuple, Fin.append_left]
    · simp only [GenRow.plainTuple, Fin.append_right]
      exact congrFun hE.2.1 j

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Binding a recursive name** to a round of its kinds keeps the
environment kinded. -/
theorem EvalEnv.Kinded.assignHole {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T}
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hE : E.Kinded γ ρc HK) (s : String) {n : ℕ}
    {κ : Fin n → ColKind} {X : Multiset (GenRow T K n)}
    (hX : ∀ r ∈ X, GenRow.Conforms κ r.fst) :
    (E.assignHole s X).Kinded γ ρc (HK.assign s κ) := by
  refine ⟨hE.1, hE.2.1, fun s' m r hr => ?_⟩
  simp only [EvalEnv.assignHole] at hr
  by_cases h : s' = s ∧ m = n
  · obtain ⟨rfl, rfl⟩ := h
    rw [dite_eq_left ⟨rfl, rfl⟩] at hr
    intro k
    have := hX r hr k
    simpa [HoleKinds.assign] using this
  · rw [dite_eq_right h] at hr
    intro k
    have := hE.2.2 s' m r hr k
    simpa [HoleKinds.assign, h] using this

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- On a kinded environment, a well-kinded hole reads its round whole. -/
theorem EvalEnv.Kinded.hole_filter {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T}
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hE : E.Kinded γ ρc HK) {s : String} {n : ℕ}
    {κ : Fin n → ColKind} (hwk : ∀ k, (κ k).base = (HK s n k).base) :
    (E.holes s n).filter (fun r => GenRow.Conforms κ r.fst) = E.holes s n :=
  Multiset.filter_eq_self.mpr fun r hr =>
    (GenRow.conforms_congr hwk r.fst).mpr (hE.2.2 s n r hr)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- On a kinded environment, a well-kinded parameter leaf reads its one
row. -/
theorem EvalEnv.Kinded.paramRows_eq {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T}
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hE : E.Kinded γ ρc HK) {m : ℕ}
    {pv : Fin m → T ⊕ Fin c} {ρ : Fin m → ColKind}
    (hwk : ∀ k, (ρ k).base = _root_.Sum.elim (fun _ => ColKind.reg) (fun j => (ρc j).base) (pv k)) :
    E.paramRows γ pv ρ
      = {⟨fun k => _root_.Sum.elim Sum.inl (E.ctxAt c γ) (pv k), ⟨1, 0⟩⟩} := by
  unfold EvalEnv.paramRows
  rw [ite_eq_left]
  intro k
  rw [hwk k]
  show GenValue.kindOf (_root_.Sum.elim Sum.inl (E.ctxAt c γ) (pv k)) = _
  cases pv k with
  | inl a => rfl
  | inr j => exact hE.1 j

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- And the plain reading of that row is the plain parameters'. -/
theorem EvalEnv.Kinded.plainTuple_param {E : EvalEnv T K} {c : ℕ} {γ : Fin c → T}
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hE : E.Kinded γ ρc HK) {m : ℕ}
    (pv : Fin m → T ⊕ Fin c) :
    GenRow.plainTuple (fun k => _root_.Sum.elim Sum.inl (E.ctxAt c γ) (pv k))
      = fun k => _root_.Sum.elim id γ (pv k) := by
  funext k
  cases h : pv k with
  | inl a => simp only [GenRow.plainTuple, h]; rfl
  | inr j =>
    simp only [GenRow.plainTuple, h]
    exact congrFun hE.2.1 j

/-- **No aggregate column read as a key.** Reading one produces a row
per value the column takes in *some* world, so the data part of the
annotated evaluation is not the data part of any one world, and the
annotation-forgetting adequacy of `evaluateAnnotated_toPlain` does not
hold for it – unlike the readings that *are* world readings, the
Boolean support and the random world, which `Explode` respects. -/
def AggQueryIn.noExplode {T' : Type} : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T' c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noExplode
  | _, _, _, _, .Sel _ q _ => q.noExplode
  | _, _, _, _, .Prod q₁ q₂ => q₁.noExplode ∧ q₂.noExplode
  | _, _, _, _, .Apply q₁ q₂ => q₁.noExplode ∧ q₂.noExplode
  | _, _, _, _, .Sum q₁ q₂ => q₁.noExplode ∧ q₂.noExplode
  | _, _, _, _, .Dedup q => q.noExplode
  | _, _, _, _, .Diff q₁ q₂ => q₁.noExplode ∧ q₂.noExplode
  | _, _, _, _, .Explode _ _ _ => False
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noExplode ∧ q₁.noExplode
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noExplode ∧ q₁.noExplode
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noExplode
  | _, _, _, _, .GammaScalar _ _ q _ => q.noExplode
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noExplode
  | _, _, _, _, .ProvSum _ _ _ q => q.noExplode
  | _, _, _, _, .Retag _ q => q.noExplode
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noExplode
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noExplode
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noExplode

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
theorem AggQueryIn.evaluate_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K)
    {γ : Fin c → T} {E : EvalEnv T K} :
    (q.castKind h).evaluate d γ E = q.evaluate d γ E := by
  subst h; rfl

/-- The kind vector of a `Gamma` output: key columns then token columns. -/
abbrev ColKind.gammaKinds (n₁ n₂ : ℕ) : Fin (n₁ + n₂) → ColKind :=
  Fin.append (fun _ : Fin n₁ => ColKind.reg) (fun _ : Fin n₂ => ColKind.agg)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Kind transport is transparent to plain evaluation too. -/
theorem AggQueryIn.evaluatePlain_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c n κ l) (d : Database T)
    {γ : Fin c → T} :
    (q.castKind h).evaluatePlain d γ = q.evaluatePlain d γ := by
  subst h; rfl

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- The token lists of a row with a single token, in its last column: the
one token's occurrence annotations. -/
theorem tokenLists_snoc {n : ℕ} (u : Tuple T n) (a : AggTok T K) :
    tokenLists (Fin.snoc (fun k => (Sum.inl (u k) : GenValue T K))
        (Sum.inr a) : Tuple (GenValue T K) (n + 1))
      = {a.annList} := by
  unfold tokenLists
  rw [Fin.univ_castSuccEmb]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

/-! ## Kind conformance

Rows produced by the general evaluator conform to the query's kind
vector: regular columns hold regular values, token columns hold tokens.
This is an invariant *lemma*, not a hypothesis: the kind-indexed syntax
makes it hold by construction, and downstream theorems (the random-world
commutation in particular) invoke it instead of assuming wellformedness. -/


/-- **Every aggregate column of a tuple holds an ordinary token** –
neither a nested value nor an expression over several of them. This is
the metatheory's standing assumption while those two readings are
unproved; on a row the evaluator produces it is a theorem,
`AggQueryIn.evaluate_ordinaryTokens`, so no result on a query carries
it. -/
def GenRow.OrdinaryTokens {n : ℕ} (u : Tuple (GenValue T K) n) : Prop :=
  ∀ (k : Fin n) (a : AggTok T K), u k = Sum.inr a → a.isTok = true

/-- **No column of a tuple holds a *nested* token.** The weaker of the
two fences: the readings of an aggregate *expression* are proved
(`AggExpr.predProvWith_congr`, `_mapAnn`, `_delta_absorb`,
`vals_congr`), so a result need only exclude `nest`, whose readings are
not. `GenRow.OrdinaryTokens` is the stronger fence, for results that
have not yet been extended to an expression. -/
def GenRow.NoNested {n : ℕ} (u : Tuple (GenValue T K) n) : Prop :=
  ∀ (k : Fin n) (a : AggTok T K), u k = Sum.inr a → a.isNested = false

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- An ordinary token is not nested. -/
theorem GenRow.NoNested.of_ordinary {n : ℕ} {u : Tuple (GenValue T K) n}
    (h : GenRow.OrdinaryTokens u) : GenRow.NoNested u := by
  intro k a ha
  obtain ⟨a', rfl⟩ := AggTok.eq_tok_of_isTok (h k a ha)
  rfl

/-- **No `FILTER` clause.** A grouping may cut the occurrence sequence
one of its aggregates reads (`AggQueryIn.Gamma`'s `keep`, and
`AggQueryIn.GammaTok`'s in the rewritten world), a window the part of its
frame it reads (`AggQueryIn.Win`'s `keep`), and a multi-frame window the
part of each leaf's frame (`AggQueryIn.WinExpr`'s `keeps`).

What asks this is `AggQueryIn.evaluate_ordinaryTokens`, and for the
reason that fence exists: a *filtered* aggregate of a grouping or of a
frame builds an aggregate *expression* and not an ordinary token, the
clause cutting what the expression reads and not its family. Nothing
else asks it. In particular the rewritten world's evaluator reads a
clause like the plain one does – both through
`Relation.groupSeqOpt` and `ValueFrame.windowValueOpt` – so
`AggQueryIn.evaluateRew_plain` covers a filtered grouping and a filtered
window, as the evaluators, the hom commutation, the possible-world
reading and the data-part adequacy already did. -/
def AggQueryIn.noFilter : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noFilter
  | _, _, _, _, .Sel _ q _ => q.noFilter
  | _, _, _, _, .Prod q₁ q₂ => q₁.noFilter ∧ q₂.noFilter
  | _, _, _, _, .Apply q₁ q₂ => q₁.noFilter ∧ q₂.noFilter
  | _, _, _, _, .Sum q₁ q₂ => q₁.noFilter ∧ q₂.noFilter
  | _, _, _, _, .Dedup q => q.noFilter
  | _, _, _, _, .Diff q₁ q₂ => q₁.noFilter ∧ q₂.noFilter
  | _, _, _, _, .Explode _ _ q => q.noFilter
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noFilter ∧ q₁.noFilter
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noFilter ∧ q₁.noFilter
  | _, _, _, _, .Gamma _ _ _ q keep _ => (∀ j, keep j = none) ∧ q.noFilter
  | _, _, _, _, .GammaScalar _ _ q _ => q.noFilter
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noFilter
  | _, _, _, _, .ProvSum _ _ _ q => q.noFilter
  | _, _, _, _, .Retag _ q => q.noFilter
  | _, _, _, _, .GammaTok _ _ _ _ _ q keep => (∀ j, keep j = none) ∧ q.noFilter
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ keep => keep = none ∧ q.noFilter
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q keeps => (∀ l, keeps l = none) ∧ q.noFilter

/-- **No second-level aggregation.** `GammaNest` is the one operator of
the syntax that builds a *nested* token, and what this excludes is the
two syntactic token fences it is the counterexample to
(`AggQueryIn.evaluate_noNested`, `AggQueryIn.evaluate_ordinaryTokens`).
Everything else covers it: the evaluators and the kind conformance ask
nothing, the data-part adequacy, the guardedness and the rewritten
world's plain reading are proved, the random world and the PQE results
ask only `AggQueryIn.nestOnce`, and the hom commutation asks only that
the target semiring be complemented
(`AggQueryIn.nestInComplemented`).

**What the hom needs, and what gives it.** A nested world's weight is
not a function of the four readings its occurrences' inner values carry.
`NestedValue.World.ann` is `presentProd ⊗ (𝟙 ⊖ absentSum)` with the
monus taken *once, globally*: `absentSum` adds the absent outer
annotations and, for every occurrence, `Σ_{j ∉ sub} anns j` of its inner
family. `AggExpr.predProvWith` instead bundles a monus *per inner world*,
`∏_{j∈S} anns ⊗ (𝟙 ⊖ Σ_{j∉S} anns)`, and the bundle does not recover the
pair. So what the nested reading asks of an occurrence is, per subfamily
`S` of its inner family, the triple `(∏_{j∈S} anns j, Σ_{j∉S} anns j,
valOn S)` – data about positions, which the four readings do not
determine.

Two things answer it. In a *complemented* semiring the global monus
factors occurrence by occurrence (`NestedValue.World.ann_split`, off
`monus_multiset_sum`), so the weight becomes a product of per-occurrence
statistics; and `GenRow.Sim` now relates an aggregate column by its
`AggExpr.worldStats`, the bag of those triples, which a tie-block
permutation preserves (`AggExpr.worldStats_congr`) and which every
operator's aggregate column therefore gives. -/
def AggQueryIn.noGammaNest : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noGammaNest
  | _, _, _, _, .Sel _ q _ => q.noGammaNest
  | _, _, _, _, .Prod q₁ q₂ => q₁.noGammaNest ∧ q₂.noGammaNest
  | _, _, _, _, .Apply q₁ q₂ => q₁.noGammaNest ∧ q₂.noGammaNest
  | _, _, _, _, .Sum q₁ q₂ => q₁.noGammaNest ∧ q₂.noGammaNest
  | _, _, _, _, .Dedup q => q.noGammaNest
  | _, _, _, _, .Diff q₁ q₂ => q₁.noGammaNest ∧ q₂.noGammaNest
  | _, _, _, _, .Explode _ _ q => q.noGammaNest
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noGammaNest ∧ q₁.noGammaNest
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noGammaNest ∧ q₁.noGammaNest
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noGammaNest
  | _, _, _, _, .GammaScalar _ _ q _ => q.noGammaNest
  | _, _, _, _, .GammaNest _ _ _ _ _ => False
  | _, _, _, _, .ProvSum _ _ _ q => q.noGammaNest
  | _, _, _, _, .Retag _ q => q.noGammaNest
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noGammaNest
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noGammaNest
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noGammaNest

/-- **Every recursion of the query settles.** A recursion means the value
its rounds settle at and means nothing elsewhere, so a result that
evaluates one asks this: at a `MuSet`, that the iteration repeats a round
(`MuSetSettles`); at a `Mu`, that some round is empty (`MuSettles`) and
that an empty round stays empty, which is what SQL's requirement that the
recursive reference occur in the body buys.

It is asked at *every* database, because a nested recursion is evaluated
at the databases its enclosing rounds produce. A query with no recursion
satisfies it with no content, every clause but the two recursions asking
only what its subqueries ask. -/
def AggQueryIn.recSettles : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.recSettles
  | _, _, _, _, .Sel _ q _ => q.recSettles
  | _, _, _, _, .Prod q₁ q₂ => q₁.recSettles ∧ q₂.recSettles
  | _, _, _, _, .Apply q₁ q₂ => q₁.recSettles ∧ q₂.recSettles
  | _, _, _, _, .Sum q₁ q₂ => q₁.recSettles ∧ q₂.recSettles
  | _, _, _, _, .Dedup q => q.recSettles
  | _, _, _, _, .Diff q₁ q₂ => q₁.recSettles ∧ q₂.recSettles
  | _, _, _, _, .Explode _ _ q => q.recSettles
  | _, _, _, _, .Mu s q₀ q₁ =>
      (∀ (d : AnnotatedDatabase T K) γ (E : EvalEnv T K),
          AggQueryIn.muStep s q₁ d γ E 0 = 0
            ∧ MuSettles (AggQueryIn.muStep s q₁ d γ E) (q₀.evaluate d γ E))
        ∧ q₀.recSettles ∧ q₁.recSettles
  | _, _, _, _, .MuSet s q₀ q₁ =>
      (∀ (d : AnnotatedDatabase T K) γ (E : EvalEnv T K),
          MuSetSettles (AggQueryIn.muSetStep s q₀ q₁ d γ E))
        ∧ q₀.recSettles ∧ q₁.recSettles
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.recSettles
  | _, _, _, _, .GammaScalar _ _ q _ => q.recSettles
  | _, _, _, _, .GammaNest _ _ _ _ q => q.recSettles
  | _, _, _, _, .ProvSum _ _ _ q => q.recSettles
  | _, _, _, _, .Retag _ q => q.recSettles
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.recSettles
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.recSettles
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.recSettles

/-- **Every second-level aggregation is read in a complemented
semiring.** This is what the hom commutation asks of `GammaNest` instead
of excluding it: a nested world's weight is one product and one monus
over what the world drops at *both* levels, and it splits into a factor
per occurrence exactly where `𝟙 ⊖ ·` turns `⊕` into `⊗`
(`NestedValue.World.ann_split`). Split that way, what a nested value
reads is a function of its occurrences' columns through
`AggExpr.worldStats`, which a simulation carries – so the commutation
goes through.

It costs nothing where no second-level aggregation occurs, being `True`
there, and nothing in the catalog either: every semiring of it is
complemented. It bites only in an m-semiring that is not, such as the
non-negative rationals, where `𝟙 ⊖ (½ ⊕ ½)` is `𝟘` against `¼`. -/
def AggQueryIn.nestInComplemented : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.nestInComplemented
  | _, _, _, _, .Sel _ q _ => q.nestInComplemented
  | _, _, _, _, .Prod q₁ q₂ => q₁.nestInComplemented ∧ q₂.nestInComplemented
  | _, _, _, _, .Apply q₁ q₂ => q₁.nestInComplemented ∧ q₂.nestInComplemented
  | _, _, _, _, .Sum q₁ q₂ => q₁.nestInComplemented ∧ q₂.nestInComplemented
  | _, _, _, _, .Dedup q => q.nestInComplemented
  | _, _, _, _, .Diff q₁ q₂ => q₁.nestInComplemented ∧ q₂.nestInComplemented
  | _, _, _, _, .Explode _ _ q => q.nestInComplemented
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.nestInComplemented ∧ q₁.nestInComplemented
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.nestInComplemented ∧ q₁.nestInComplemented
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.nestInComplemented
  | _, _, _, _, .GammaScalar _ _ q _ => q.nestInComplemented
  | _, _, _, _, .GammaNest _ _ _ _ q => complemented K ∧ q.nestInComplemented
  | _, _, _, _, .ProvSum _ _ _ q => q.nestInComplemented
  | _, _, _, _, .Retag _ q => q.nestInComplemented
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.nestInComplemented
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.nestInComplemented
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.nestInComplemented

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A query with no second-level aggregation asks nothing of the
semiring. -/
theorem AggQueryIn.nestInComplemented_of_noGammaNest :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noGammaNest → q.nestInComplemented (K := K) := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Param pv ρ => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode k hk q ih => exact ih
  | Mu a q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet a q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact ih
  | GammaScalar ts fs q ord ih => exact ih
  | GammaNest is his p f q ih => exact fun h => absurd h not_false
  | ProvSum is his t q ih => exact ih
  | Retag hk q ih => exact ih
  | GammaTok is his ts fs ann q keep ih => exact ih
  | Win P O o w t f q hrr dist keep ih => exact ih
  | WinExpr P O o ws ts fs g q keeps ih => exact ih

/-- **No second-level aggregation reads a second-level aggregation.**
One level of nesting is what `sec:aggcols` reads as values: an occurrence
of a nested value carries the aggregate *expression* read there, and an
expression's leaves are ordinary aggregate values. A column holding a
*nested* value at such an occurrence is a second level, which
`GenValue.innerValue` reads through its collapse – total, and the
deterministic reading of it is right, but not the world reading. A third
level is what resolution takes innermost first, so the possible-world
results ask this of the query: no `GammaNest` inside a `GammaNest`.

A nested value reaches a second-level aggregation's input through the
context and the rounds of a recursion too, so the condition follows it
there: an apply whose right side aggregates at the second level has a left
side that does not, and a recursive body that aggregates at the second
level binds its name to rounds with no aggregate column.

It is strictly weaker than `AggQueryIn.noGammaNest`, which excludes the
operator outright. -/
def AggQueryIn.nestOnce : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.nestOnce
  | _, _, _, _, .Sel _ q _ => q.nestOnce
  | _, _, _, _, .Prod q₁ q₂ => q₁.nestOnce ∧ q₂.nestOnce
  | _, _, _, _, .Apply q₁ q₂ => q₁.nestOnce ∧ q₂.nestOnce ∧ (q₁.noGammaNest ∨ q₂.noGammaNest)
  | _, _, _, _, .Sum q₁ q₂ => q₁.nestOnce ∧ q₂.nestOnce
  | _, _, _, _, .Dedup q => q.nestOnce
  | _, _, _, _, .Diff q₁ q₂ => q₁.nestOnce ∧ q₂.nestOnce
  | _, _, _, _, .Explode _ _ q => q.nestOnce
  | _, _, _, _, @Mu _ _ _ κ _ q₀ q₁ =>
      q₀.nestOnce ∧ q₁.nestOnce ∧ (q₁.noGammaNest ∨ ∀ k, (κ k).base ≠ ColKind.agg)
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.nestOnce ∧ q₁.nestOnce
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.nestOnce
  | _, _, _, _, .GammaScalar _ _ q _ => q.nestOnce
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noGammaNest
  | _, _, _, _, .ProvSum _ _ _ q => q.nestOnce
  | _, _, _, _, .Retag _ q => q.nestOnce
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.nestOnce
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.nestOnce
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.nestOnce

/-- No window anywhere in the query. -/
def AggQueryIn.noWin : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noWin
  | _, _, _, _, .Sel _ q _ => q.noWin
  | _, _, _, _, .Prod q₁ q₂ => q₁.noWin ∧ q₂.noWin
  | _, _, _, _, .Apply q₁ q₂ => q₁.noWin ∧ q₂.noWin
  | _, _, _, _, .Sum q₁ q₂ => q₁.noWin ∧ q₂.noWin
  | _, _, _, _, .Dedup q => q.noWin
  | _, _, _, _, .Diff q₁ q₂ => q₁.noWin ∧ q₂.noWin
  | _, _, _, _, .Explode _ _ q => q.noWin
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noWin ∧ q₁.noWin
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noWin ∧ q₁.noWin
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noWin
  | _, _, _, _, .GammaScalar _ _ q _ => q.noWin
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noWin
  | _, _, _, _, .ProvSum _ _ _ q => q.noWin
  | _, _, _, _, .Retag _ q => q.noWin
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noWin
  | _, _, _, _, .Win _ _ _ _ _ _ _ _ _ _ => False
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

/-- **No second-level aggregation reads a window's output.** A world of a
nested value decides each outer occurrence's inner family on its own,
which is the paper's reading where the inner families are disjoint – a
grouping's groups, or evaluations kept apart – but not where they
overlap, as the frames of one window partition do: there the paper
decides each shared occurrence once. So a nested value over a window's
output is refused until the worlds of a nested value decide a shared
occurrence once. A window's token reaches a second-level aggregation
through its input, or through the left side of an apply whose right side
aggregates the parameter row. -/
def AggQueryIn.nestNoWin : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.nestNoWin
  | _, _, _, _, .Sel _ q _ => q.nestNoWin
  | _, _, _, _, .Prod q₁ q₂ => q₁.nestNoWin ∧ q₂.nestNoWin
  | _, _, _, _, .Apply q₁ q₂ => q₁.nestNoWin ∧ q₂.nestNoWin ∧ (q₂.noGammaNest ∨ q₁.noWin)
  | _, _, _, _, .Sum q₁ q₂ => q₁.nestNoWin ∧ q₂.nestNoWin
  | _, _, _, _, .Dedup q => q.nestNoWin
  | _, _, _, _, .Diff q₁ q₂ => q₁.nestNoWin ∧ q₂.nestNoWin
  | _, _, _, _, .Explode _ _ q => q.nestNoWin
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.nestNoWin ∧ q₁.nestNoWin
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.nestNoWin ∧ q₁.nestNoWin
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.nestNoWin
  | _, _, _, _, .GammaScalar _ _ q _ => q.nestNoWin
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noWin ∧ q.nestNoWin
  | _, _, _, _, .ProvSum _ _ _ q => q.nestNoWin
  | _, _, _, _, .Retag _ q => q.nestNoWin
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.nestNoWin
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.nestNoWin
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.nestNoWin

omit [ValueType T] in
/-- A query with no second-level aggregation reads no window's output
through one. -/
theorem AggQueryIn.nestNoWin_of_noGammaNest :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noGammaNest → q.nestNoWin := by
  intro c n κ l q
  induction q with
  | GammaNest _ _ _ _ q _ => exact fun h => h.elim
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2, Or.inl h.2⟩
  | _ => simp_all [AggQueryIn.noGammaNest, AggQueryIn.nestNoWin]

/-- **Every aggregating operator records the parameters it reads**: its
read set `rd` is the set of outer columns its subtree reads. This is the
paper's identity of occurrences (an operator evaluated on the same
inputs produces the same occurrences), and it is a condition on the
queries a result is about: the passes keep each operator's recorded set
while rewriting below it, so their outputs record what their sources
read, which can be more than they read themselves. -/
def AggQueryIn.readsRecorded : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.readsRecorded
  | _, _, _, _, .Sel _ q _ => q.readsRecorded
  | _, _, _, _, .Prod q₁ q₂ => q₁.readsRecorded ∧ q₂.readsRecorded
  | _, _, _, _, .Apply q₁ q₂ => q₁.readsRecorded ∧ q₂.readsRecorded
  | _, _, _, _, .Sum q₁ q₂ => q₁.readsRecorded ∧ q₂.readsRecorded
  | _, _, _, _, .Dedup q => q.readsRecorded
  | _, _, _, _, .Diff q₁ q₂ => q₁.readsRecorded ∧ q₂.readsRecorded
  | _, _, _, _, .Explode _ _ q => q.readsRecorded
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.readsRecorded ∧ q₁.readsRecorded
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.readsRecorded ∧ q₁.readsRecorded
  | _, _, _, _, @Gamma _ _ _ _ _ lab rd is ts fs q keep ord =>
      rd = (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).readsOuter
        ∧ q.readsRecorded
  | _, _, _, _, @GammaScalar _ _ _ _ lab rd ts fs q ord =>
      rd = (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).readsOuter
        ∧ q.readsRecorded
  | _, _, _, _, @GammaNest _ _ _ _ _ lab rd is his p f q =>
      rd = (AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).readsOuter
        ∧ q.readsRecorded
  | _, _, _, _, .ProvSum _ _ _ q => q.readsRecorded
  | _, _, _, _, .Retag _ q => q.readsRecorded
  | _, _, _, _, @GammaTok _ _ _ _ _ _ lab rd is his ts fs a q keep =>
      rd = (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).readsOuter
        ∧ q.readsRecorded
  | _, _, _, _, @Win _ _ _ _ _ _ lab rd P O o w t f q hrr dist keep =>
      rd = (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep).readsOuter
        ∧ q.readsRecorded
  | _, _, _, _, @WinExpr _ _ _ _ _ _ lab rd P O o ws ts fs g q keeps =>
      rd = (AggQueryIn.WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps).readsOuter
        ∧ q.readsRecorded

omit [ValueType T] in
/-- A query with no second-level aggregation at all nests at most
once. -/
theorem AggQueryIn.nestOnce_of_noGammaNest :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noGammaNest → q.nestOnce := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Param pv ρ => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2, Or.inl h.1⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode a b q ih => exact ih
  | Mu a q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2, Or.inl h.2⟩
  | MuSet a q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma a b cc q kp od ih => exact ih
  | GammaScalar a b q od ih => exact ih
  | GammaNest a b cc dd q ih => exact fun h => absurd h not_false
  | ProvSum a b cc q ih => exact ih
  | Retag a q ih => exact ih
  | GammaTok a b cc dd e q keep ih => exact ih
  | Win a b cc dd e ff q hrr dist kp ih => exact ih
  | WinExpr a b cc dd e ff gg q kps ih => exact ih

/-- **No multi-frame window.** `WinExpr` is the one operator of the
syntax that builds an aggregate column holding an expression rather than
an ordinary token, so the results proved only for ordinary tokens
exclude it with this – as the possible-world results exclude `ProvSum`
with `noProvSum`.

A result that reads an expression column through the four readings
`AggExpr` provides needs no such fence; the hom commutation asks instead
that the frames be read off the tuples
(`AggQueryIn.framesContainSelf`). -/
def AggQueryIn.noWinExpr : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noWinExpr
  | _, _, _, _, .Sel _ q _ => q.noWinExpr
  | _, _, _, _, .Prod q₁ q₂ => q₁.noWinExpr ∧ q₂.noWinExpr
  | _, _, _, _, .Apply q₁ q₂ => q₁.noWinExpr ∧ q₂.noWinExpr
  | _, _, _, _, .Sum q₁ q₂ => q₁.noWinExpr ∧ q₂.noWinExpr
  | _, _, _, _, .Dedup q => q.noWinExpr
  | _, _, _, _, .Diff q₁ q₂ => q₁.noWinExpr ∧ q₂.noWinExpr
  | _, _, _, _, .Explode _ _ q => q.noWinExpr
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noWinExpr ∧ q₁.noWinExpr
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noWinExpr ∧ q₁.noWinExpr
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noWinExpr
  | _, _, _, _, .GammaScalar _ _ q _ => q.noWinExpr
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noWinExpr
  | _, _, _, _, .ProvSum _ _ _ q => q.noWinExpr
  | _, _, _, _, .Retag _ q => q.noWinExpr
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noWinExpr
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noWinExpr
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

/-- **Every multi-frame window frames by the tuple.** A window
expression lists its shared family by occurrence index, and a change of
annotation semiring re-sorts that index inside blocks of equal rows, so
a reading of the family that told two equal rows apart would not survive
the change. `ValueFrame.ContainsSelf` is what stops it telling them
apart: the frame contains its current row exactly when it contains its
peers, so membership is a test on the tuples
(`ValueFrame.mem_of_containsSelf`).

`RANGE`, the whole partition and the rows strictly before all satisfy
it; `EXCLUDE CURRENT ROW` and `EXCLUDE TIES` are exactly the frames that
do not (`ValueFrame.not_containsSelf_excludeCurrent`), and they are the
ones a multi-frame window needs the occurrences for. Nothing is asked of
a single-frame `Win`, whose token is read off the relation. -/
def AggQueryIn.framesContainSelf : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.framesContainSelf
  | _, _, _, _, .Sel _ q _ => q.framesContainSelf
  | _, _, _, _, .Prod q₁ q₂ => q₁.framesContainSelf ∧ q₂.framesContainSelf
  | _, _, _, _, .Apply q₁ q₂ => q₁.framesContainSelf ∧ q₂.framesContainSelf
  | _, _, _, _, .Sum q₁ q₂ => q₁.framesContainSelf ∧ q₂.framesContainSelf
  | _, _, _, _, .Dedup q => q.framesContainSelf
  | _, _, _, _, .Diff q₁ q₂ => q₁.framesContainSelf ∧ q₂.framesContainSelf
  | _, _, _, _, .Explode _ _ q => q.framesContainSelf
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.framesContainSelf ∧ q₁.framesContainSelf
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.framesContainSelf ∧ q₁.framesContainSelf
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.framesContainSelf
  | _, _, _, _, .GammaScalar _ _ q _ => q.framesContainSelf
  | _, _, _, _, .GammaNest _ _ _ _ q => q.framesContainSelf
  | _, _, _, _, .ProvSum _ _ _ q => q.framesContainSelf
  | _, _, _, _, .Retag _ q => q.framesContainSelf
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.framesContainSelf
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.framesContainSelf
  | _, _, _, _, .WinExpr _ _ _ ws _ _ _ q _ =>
      (∀ l, (ws l).ContainsSelf) ∧ q.framesContainSelf

/-- A query with no multi-frame window asks nothing of its frames. -/
theorem AggQueryIn.framesContainSelf_of_noWinExpr :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noWinExpr → q.framesContainSelf := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Param pv ρ => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hw => ⟨ih₁ hw.1, ih₂ hw.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hw => ⟨ih₁ hw.1, ih₂ hw.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hw => ⟨ih₁ hw.1, ih₂ hw.2⟩
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hw => ⟨ih₁ hw.1, ih₂ hw.2⟩
  | Explode a b q ih => exact ih
  | Mu a q₀ q₁ ih₀ ih₁ => exact fun hw => ⟨ih₀ hw.1, ih₁ hw.2⟩
  | MuSet a q₀ q₁ ih₀ ih₁ => exact fun hw => ⟨ih₀ hw.1, ih₁ hw.2⟩
  | Gamma a b cc q kp od ih => exact ih
  | GammaScalar a b q od ih => exact ih
  | GammaNest a b cc dd q ih => exact ih
  | ProvSum a b cc q ih => exact ih
  | Retag a q ih => exact ih
  | GammaTok a b cc dd e q keep ih => exact ih
  | Win a b cc dd e ff q hrr dist kp ih => exact ih
  | WinExpr a b cc dd e ff gg q kps ih => exact fun hw => absurd hw not_false

/-- **Only `WinExpr` and `GammaNest` build anything but an ordinary
token.** Every aggregate column of every row a query without them
produces holds an ordinary token: the grouping and the window build
their tokens with `AggTok.tok`, a projection copies or post-composes one
– and `AggTok.postcomp` keeps the kind – and everything else carries
rows through or rebuilds them from annotated tuples. A multi-frame
window builds an expression and second-level aggregation a nested value,
which is why both are excluded here.

This is what lets a result proved only for an ordinary token keep its
statement about rows: it gets "every token here is ordinary" from this
lemma, with the two operators excluded on the query. -/
theorem AggQueryIn.evaluate_ordinaryTokens :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noWinExpr → q.noGammaNest → q.noFilter →
      ∀ (d : AnnotatedDatabase T K) {γ : Fin c → T} (E : EvalEnv T K),
        E.RowsSat (fun v => ∀ a, v = Sum.inr a → a.isTok = true) → ∀ (r : GenRow T K n),
      r ∈ q.evaluate d γ E → GenRow.OrdinaryTokens r.fst := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    cases hf : d.find n s with
    | none => rw [hf] at hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      rw [hf] at hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      exact absurd ha (by simp [GenRow.ofAnnotated])
  | Hole n s κ =>
    intro hq hn hfl d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact EvalEnv.rowsSat_hole hE hr
  | Param pv ρ =>
    intro hq hn hfl d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact EvalEnv.rowsSat_param (fun _ _ h => absurd h (by simp)) hE hr
  | Empty =>
    intro _ _ _ d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact absurd hr (Multiset.notMem_zero r)
  | Proj ps q ih =>
    intro hq hn hfl d γ E hE r hr j a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
    cases hp : ps j with
    | term t => exact absurd ha (by simp [ProjColIn.eval, hp])
    | provTerm t => exact absurd ha (by simp [ProjColIn.eval, hp])
    | token k hk =>
      refine ih hq hn hfl d E hE r₀ hr₀ k a ?_
      show r₀.fst k = Sum.inr a
      rw [← ha]
      simp [ProjColIn.eval, hp]
    | aggTerm k hk gf =>
      cases hu : r₀.fst k with
      | inl w => exact absurd ha (by simp [ProjColIn.eval, hp, hu])
      | inr x =>
        have hax : a = x.postcomp gf := by
          have := ha
          simp only [ProjColIn.eval, hp, hu, Sum.map_inr] at this
          exact (Sum.inr.inj this).symm
        rw [hax, AggTok.isTok_postcomp]
        exact ih hq hn hfl d E hE r₀ hr₀ k x hu
    | aggTermOf k hk gf =>
      cases hu : r₀.fst k with
      | inl w => exact absurd ha (by simp [ProjColIn.eval, hp, hu])
      | inr x =>
        have hax : a = x.postcomp gf.unary := by
          have := ha
          simp only [ProjColIn.eval, hp, hu, Sum.map_inr] at this
          exact (Sum.inr.inj this).symm
        rw [hax, AggTok.isTok_postcomp]
        exact ih hq hn hfl d E hE r₀ hr₀ k x hu
  | Sel φ q _ ih =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      exact ih hq hn hfl d E hE r₀ hr₀ k a ha
    · rw [ite_eq_right hφ] at hr
      exact ih hq hn hfl d E hE r (Multiset.mem_of_mem_filter hr) k a ha
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hn hfl d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hr
    obtain ⟨h₁, h₂⟩ := Multiset.mem_product.mp hp
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact ih₁ hq.1 hn.1 hfl.1 d E hE p.1 h₁ i a (by rw [← ha]; exact (Fin.append_left _ _ i).symm)
    · exact ih₂ hq.2 hn.2 hfl.2 d E hE p.2 h₂ j a (by rw [← ha]; exact
          (Fin.append_right _ _ j).symm)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hn hfl d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hx, hy⟩ := Multiset.mem_bind.mp hr
    obtain ⟨y, hy', rfl⟩ := Multiset.mem_map.mp hy
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact ih₁ hq.1 hn.1 hfl.1 d E hE x hx i a (by rw [← ha]; exact (Fin.append_left _ _ i).symm)
    · exact ih₂ hq.2 hn.2 hfl.2 d _ (EvalEnv.rowsSat_enter (fun _ _ h => absurd h (by simp)) hE _
          (ih₁ hq.1 hn.1 hfl.1 d E hE x hx))
        y hy' j a (by rw [← ha]; exact (Fin.append_right _ _ j).symm)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.mp hr with h | h
    · exact ih₁ hq.1 hn.1 hfl.1 d E hE r h k a ha
    · exact ih₂ hq.2 hn.2 hfl.2 d E hE r h k a ha
  | Dedup q ih =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Explode k hk q ih =>
    intro hq hn hfl d γ E hE r hr j a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, hs⟩ := Multiset.mem_bind.mp hr
    cases hfk : r₀.fst k with
    | inl w =>
      rw [GenRow.alternativesAt, hfk, Multiset.mem_singleton] at hs
      subst hs
      exact ih hq hn hfl d E hE _ hr₀ j a ha
    | inr x =>
      rw [GenRow.alternativesAt, hfk] at hs
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hs
      by_cases hj : j = k
      · subst hj
        exact absurd ha (by simp)
      · exact ih hq hn hfl d E hE r₀ hr₀ j a
          ((Function.update_of_ne hj (Sum.inl v) r₀.fst).symm.trans ha)
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hq hn hfl d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact forall_mem_muSumFix (P := fun r : GenRow T K _ => GenRow.OrdinaryTokens r.fst)
      (fun X hX y hy => ih₁ hq.2 hn.2 hfl.2 d _ (EvalEnv.rowsSat_assignHole hE s hX) y hy)
      (fun x hx => ih₀ hq.1 hn.1 hfl.1 d E hE x hx) r hr
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Gamma is ts fs q keep ord ih =>
    intro hq hn hfl d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact absurd ha (by simp [Fin.append_left])
    · -- no aggregate carries a clause, so every column is an ordinary token
      simp only [Fin.append_right, hfl.1 j] at ha
      rw [← Sum.inr.inj ha]
      rfl
  | GammaScalar ts fs q ord ih =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    rw [Multiset.mem_singleton] at hr
    subst hr
    cases a with
    | tok _ => rfl
    | nest _ =>
        exact absurd ha (by simp [AggTok.setFam_tok])
    | expr _ =>
        exact absurd ha (by simp [AggTok.setFam_tok])
  | ProvSum is his t q ih =>
    intro hq hn hfl d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact absurd ha (by simp [Fin.append_left])
    · exact absurd ha (by simp [Fin.append_right])
  | Retag hk q ih =>
    intro hq hn hfl d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    exact ih hq hn hfl d E hE r hr k a ha
  | GammaTok is his ts fs ann q keep ih =>
    intro hq hn hfl d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i <;> intro a ha
      · exact absurd ha (by simp [Fin.append_left])
      · -- no clause here, by `hfl`, so the column is an ordinary token
        cases a with
        | tok _ => rfl
        | nest _ =>
          exact absurd ha (by
            simp [Fin.append_left, Fin.append_right, hfl.1 j', AggTok.setFam_tok])
        | expr _ =>
          exact absurd ha (by
            simp [Fin.append_left, Fin.append_right, hfl.1 j', AggTok.setFam_tok])
    · intro a ha
      exact absurd ha (by simp [Fin.append_right])
  | Win P O o w t f q hrr dist keep ih =>
    intro hq hn hfl d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.lastCases ?_ (fun i' => ?_) k <;> intro a ha
    · -- the window carries no clause, so its own column is an ordinary token
      dsimp only [ValueFrame.windowGenRow] at ha
      rw [Fin.snoc_last, hfl.1] at ha
      rw [← Sum.inr.inj ha]
      rfl
    · -- a column of the input, carried through: the induction hypothesis
      refine ih hq hn hfl.2 d E hE x hx i' a ?_
      have ha' := ha
      dsimp only [ValueFrame.windowGenRow] at ha'
      rwa [Fin.snoc_castSucc] at ha'
  | GammaNest is his p f q ih =>
    -- the one operator that builds a nested token, which `noGammaNest`
    -- excludes
    intro _ hn
    exact absurd hn not_false
  | WinExpr P O o ws ts fs g q keeps ih =>
    -- the one operator that builds an expression, which `noWinExpr` excludes
    intro hq
    exact absurd hq not_false

/-- **Only `GammaNest` builds a *nested* token.** The weaker companion
of `AggQueryIn.evaluate_ordinaryTokens`: the grouping and the window
build ordinary tokens, a multi-frame window builds an aggregate
expression, a projection post-composes one – and `AggTok.postcomp` keeps
the kind – and everything else carries rows through or rebuilds them
from annotated tuples. Second-level aggregation is the one operator that
constructs a nested value, and `noGammaNest` is what excludes it.

This is what a result proved for an expression column as well as an
ordinary one asks of a row. -/
theorem AggQueryIn.evaluate_noNested :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noGammaNest →
      ∀ (d : AnnotatedDatabase T K) {γ : Fin c → T} (E : EvalEnv T K),
        E.RowsSat (fun v => ∀ a, v = Sum.inr a → a.isNested = false) → ∀ (r : GenRow T K n),
      r ∈ q.evaluate d γ E → GenRow.NoNested r.fst := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    cases hf : d.find n s with
    | none => rw [hf] at hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      rw [hf] at hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      exact absurd ha (by simp [GenRow.ofAnnotated])
  | Hole n s κ =>
    intro hn d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact EvalEnv.rowsSat_hole hE hr
  | Param pv ρ =>
    intro hn d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact EvalEnv.rowsSat_param (fun _ _ h => absurd h (by simp)) hE hr
  | Empty =>
    intro _ d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact absurd hr (Multiset.notMem_zero r)
  | Proj ps q ih =>
    intro hn d γ E hE r hr j a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
    cases hp : ps j with
    | term t => exact absurd ha (by simp [ProjColIn.eval, hp])
    | provTerm t => exact absurd ha (by simp [ProjColIn.eval, hp])
    | token k hk =>
      refine ih hn d E hE r₀ hr₀ k a ?_
      show r₀.fst k = Sum.inr a
      rw [← ha]
      simp [ProjColIn.eval, hp]
    | aggTerm k hk gf =>
      cases hu : r₀.fst k with
      | inl w => exact absurd ha (by simp [ProjColIn.eval, hp, hu])
      | inr x =>
        have hax : a = x.postcomp gf := by
          have := ha
          simp only [ProjColIn.eval, hp, hu, Sum.map_inr] at this
          exact (Sum.inr.inj this).symm
        rw [hax, AggTok.isNested_postcomp]
        exact ih hn d E hE r₀ hr₀ k x hu
    | aggTermOf k hk gf =>
      cases hu : r₀.fst k with
      | inl w => exact absurd ha (by simp [ProjColIn.eval, hp, hu])
      | inr x =>
        have hax : a = x.postcomp gf.unary := by
          have := ha
          simp only [ProjColIn.eval, hp, hu, Sum.map_inr] at this
          exact (Sum.inr.inj this).symm
        rw [hax, AggTok.isNested_postcomp]
        exact ih hn d E hE r₀ hr₀ k x hu
  | Sel φ q _ ih =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      exact ih hn d E hE r₀ hr₀ k a ha
    · rw [ite_eq_right hφ] at hr
      exact ih hn d E hE r (Multiset.mem_of_mem_filter hr) k a ha
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hn d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hr
    obtain ⟨h₁, h₂⟩ := Multiset.mem_product.mp hp
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact ih₁ hn.1 d E hE p.1 h₁ i a (by rw [← ha]; exact (Fin.append_left _ _ i).symm)
    · exact ih₂ hn.2 d E hE p.2 h₂ j a (by rw [← ha]; exact (Fin.append_right _ _ j).symm)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hn d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hx, hy⟩ := Multiset.mem_bind.mp hr
    obtain ⟨y, hy', rfl⟩ := Multiset.mem_map.mp hy
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact ih₁ hn.1 d E hE x hx i a (by rw [← ha]; exact (Fin.append_left _ _ i).symm)
    · exact ih₂ hn.2 d _ (EvalEnv.rowsSat_enter (fun _ _ h => absurd h (by simp)) hE _
          (ih₁ hn.1 d E hE x hx))
        y hy' j a (by rw [← ha]; exact (Fin.append_right _ _ j).symm)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.mp hr with h | h
    · exact ih₁ hn.1 d E hE r h k a ha
    · exact ih₂ hn.2 d E hE r h k a ha
  | Dedup q ih =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Explode k hk q ih =>
    intro hn d γ E hE r hr j a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, hs⟩ := Multiset.mem_bind.mp hr
    cases hfk : r₀.fst k with
    | inl w =>
      rw [GenRow.alternativesAt, hfk, Multiset.mem_singleton] at hs
      subst hs
      exact ih hn d E hE _ hr₀ j a ha
    | inr x =>
      rw [GenRow.alternativesAt, hfk] at hs
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hs
      by_cases hj : j = k
      · subst hj
        exact absurd ha (by simp)
      · exact ih hn d E hE r₀ hr₀ j a
          ((Function.update_of_ne hj (Sum.inl v) r₀.fst).symm.trans ha)
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hn d γ E hE r hr
    simp only [AggQueryIn.evaluate] at hr
    exact forall_mem_muSumFix (P := fun r : GenRow T K _ => GenRow.NoNested r.fst)
      (fun X hX y hy => ih₁ hn.2 d _ (EvalEnv.rowsSat_assignHole hE s hX) y hy)
      (fun x hx => ih₀ hn.1 d E hE x hx) r hr
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Gamma is ts fs q keep ord ih =>
    intro hn d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact absurd ha (by simp [Fin.append_left])
    · -- an ordinary token where the aggregate carries no clause, an
      -- expression where it does, and nested in neither case
      simp only [Fin.append_right] at ha
      rw [← Sum.inr.inj ha]
      cases keep j <;> rfl
  | GammaScalar ts fs q ord ih =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    rw [Multiset.mem_singleton] at hr
    subst hr
    cases a with
    | tok _ => rfl
    | nest _ =>
        exact absurd ha (by simp [AggTok.setFam_tok])
    | expr _ =>
        exact absurd ha (by simp [AggTok.setFam_tok])
  | ProvSum is his t q ih =>
    intro hn d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro a ha
    · exact absurd ha (by simp [Fin.append_left])
    · exact absurd ha (by simp [Fin.append_right])
  | Retag hk q ih =>
    intro hn d γ E hE r hr k a ha
    simp only [AggQueryIn.evaluate] at hr
    exact ih hn d E hE r hr k a ha
  | GammaTok is his ts fs ann q keep ih =>
    intro hn d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i <;> intro a ha
      · exact absurd ha (by simp [Fin.append_left])
      · -- a clause makes the column an expression, which is not nested
        cases a with
        | tok _ => rfl
        | nest _ =>
          refine absurd ha ?_
          cases hk : keep j' with
          | none => simp [Fin.append_left, Fin.append_right, hk, AggTok.setFam_tok]
          | some φ => simp [Fin.append_left, Fin.append_right, hk, AggTok.setFam_expr]
        | expr _ => rfl
    · intro a ha
      exact absurd ha (by simp [Fin.append_right])
  | Win P O o w t f q hrr dist keep ih =>
    intro hn d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.lastCases ?_ (fun i' => ?_) k <;> intro a ha
    · -- an ordinary token with no clause, an expression with one, and
      -- nested in neither case
      dsimp only [ValueFrame.windowGenRow] at ha
      rw [Fin.snoc_last] at ha
      rw [← Sum.inr.inj ha]
      cases keep <;> rfl
    · -- a column of the input, carried through
      refine ih hn d E hE x hx i' a ?_
      have ha' := ha
      dsimp only [ValueFrame.windowGenRow] at ha'
      rwa [Fin.snoc_castSucc] at ha'
  | GammaNest is his p f q ih =>
    -- the one operator that builds a nested token, which `noGammaNest`
    -- excludes
    intro hn
    exact absurd hn not_false
  | WinExpr P O o ws ts fs g q keeps ih =>
    -- the column is an expression, which is not nested either
    intro hn d γ E hE r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.lastCases ?_ (fun i' => ?_) k <;> intro a ha
    · cases a with
      | tok _ => rfl
      | expr _ => rfl
      | nest _ =>
        exact absurd ha (by dsimp only; rw [Fin.snoc_last]; simp [AggTok.setFam_expr])
    · exact absurd ha (by dsimp only; rw [Fin.snoc_castSucc]; simp)

/-- **Kind conformance of the general evaluator.** -/
theorem AggQueryIn.evaluate_conform :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (d : AnnotatedDatabase T K) {γ : Fin c → T} {E : EvalEnv T K} (r : GenRow T K n),
      r ∈ q.evaluate d γ E → ∀ k, GenValue.kindOf (r.fst k) = (κ k).base := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    cases hf : d.find n s with
    | none => rw [hf] at hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      rw [hf] at hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      rfl
  | Hole n s κ =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    exact Multiset.of_mem_filter hr k
  | Param pv ρ =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    exact EvalEnv.conforms_of_mem_paramRows hr k
  | Empty =>
    intro d γ E r hr
    simp only [AggQueryIn.evaluate] at hr
    exact absurd hr (Multiset.notMem_zero r)
  | Proj ps q ih =>
    intro d γ E r hr j
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
    | aggTermOf k hk gf =>
      have := ih d r₀ hr₀ k
      rw [hk] at this
      simp only [ProjColIn.eval, hp, ProjColIn.kind]
      cases hu : r₀.fst k with
      | inl v =>
        rw [hu] at this
        exact absurd this (by simp [GenValue.kindOf, ColKind.base])
      | inr a => rfl
  | Sel φ q _ ih =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      exact ih d r₀ hr₀ k
    · rw [ite_eq_right hφ] at hr
      exact ih d r (Multiset.mem_of_mem_filter hr) k
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d γ E r hr k
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
    intro d γ E r hr k
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
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.mp hr with h | h
    · exact ih₁ d r h k
    · exact ih₂ d r h k
  | Dedup q ih =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Explode k hk q ih =>
    intro d γ E r hr j
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, hs⟩ := Multiset.mem_bind.mp hr
    cases hfk : r₀.fst k with
    | inl w =>
      rw [GenRow.alternativesAt, hfk, Multiset.mem_singleton] at hs
      subst hs
      by_cases hj : j = k
      · subst hj; rw [Function.update_self, hfk]; rfl
      · rw [Function.update_of_ne hj]; exact ih d _ hr₀ j
    | inr a =>
      rw [GenRow.alternativesAt, hfk] at hs
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hs
      by_cases hj : j = k
      · subst hj
        show GenValue.kindOf (Function.update r₀.fst j (Sum.inl v) j) = _
        rw [Function.update_self, Function.update_self]; rfl
      · show GenValue.kindOf (Function.update r₀.fst k (Sum.inl v) j) = _
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact ih d r₀ hr₀ j
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d γ E r hr
    simp only [AggQueryIn.evaluate] at hr
    exact forall_mem_muSumFix
      (P := fun r : GenRow T K _ => ∀ k, GenValue.kindOf (r.fst k) = _)
      (fun X _ y hy => ih₁ d y hy) (fun x hx => ih₀ d x hx) r hr
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  | Gamma is ts fs q keep ord ih =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · dsimp only
      rw [Fin.append_left, Fin.append_left]
      rfl
    · dsimp only
      rw [Fin.append_right, Fin.append_right]
      rfl
  | ProvSum is his t q ih =>
    intro d γ E r hr k
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
    intro d γ E r hr k
    exact (ih d r hr k).trans (congrArg id (h k))
  | GammaScalar ts fs q ord ih =>
    -- one row, every column a token
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    rw [Multiset.mem_singleton] at hr
    subst hr
    rfl
  | GammaNest is his p f q ih =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · dsimp only
      rw [Fin.append_left, Fin.append_left]
      exact (ColKind.base_eq_reg_of_ne_agg (his i)).symm
    · dsimp only
      rw [Fin.append_right, Fin.append_right]
      rfl
  | GammaTok is his ts fs a q keep ih =>
    intro d γ E r hr k
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
  | Win P O o w t f q hrr dist keep ih =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · dsimp only [ValueFrame.windowGenRow]
      rw [Fin.snoc_last, Fin.snoc_last]
      rfl
    · dsimp only [ValueFrame.windowGenRow]
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact ih d x hx i'
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro d γ E r hr k
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · dsimp only
      rw [Fin.snoc_last, Fin.snoc_last]
      rfl
    · dsimp only
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl
