/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Tactic.Ring

import Provenance.Derived

/-!
# The plain basis: which operators a query cannot do without

The classification of `sec:basis` grades the operators of the algebra by
what a query *without* them cannot compute. Each row is one invariant:
every query that avoids a class of operators satisfies a property of its
plain semantics, and one query using the class breaks it – so no
generating set can leave the class out.

This file carries the vocabulary the classification is stated in and the
invariants. The scope is the non-recursive queries: `Mu` and `MuSet` are
partial operators whose value is the one their rounds settle at, and the
locality row they belong to is a different argument.

`Alt` and `Retag` are transparent here: both read their argument's plain
semantics unchanged (`AggQueryIn.evaluatePlain`), so a plain-semantics
statement cannot see them, and they are in no class.
-/

variable {T : Type} [ValueType T]

/-- The operator classes the basis classification distinguishes. The
cross product and the apply are separate: a product is an apply whose
right side reads no outer column, so a generating set may contain one
without the other. -/
inductive OpKind where
  /-- The empty relation `∅`. -/
  | empty
  /-- Generalized projection `Π`. -/
  | proj
  /-- Selection `σ`. -/
  | sel
  /-- Cross product `×`. -/
  | prod
  /-- The apply, SQL's `LATERAL`. -/
  | apply
  /-- Union `⊎`. -/
  | union
  /-- Duplicate elimination `ε`. -/
  | dedup
  /-- Difference `−`. -/
  | diff
  /-- Aggregation `γ`, grouped and scalar together. -/
  | gamma
  /-- A window function. -/
  | win
  deriving DecidableEq, Repr

/-- **The classes a query uses are among `S`.** A relation leaf is in no
class, every operator is in its own, and `Alt` and `Retag` are in none,
being transparent to the plain semantics.

Four operators are `False`: this predicate carries the scope of the
classification as well, and the two recursions, the token-building
grouping and the provenance sum are outside it. The last two belong to
the rewritten world – they are what ProvSQL's plans build, not what a
source query is written with – so a classification of the source
language has nothing to say about them. -/
def AggQueryIn.usesOnly (S : Set OpKind) : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Empty => OpKind.empty ∈ S
  | _, _, _, .Proj _ q => OpKind.proj ∈ S ∧ q.usesOnly S
  | _, _, _, .Sel _ q => OpKind.sel ∈ S ∧ q.usesOnly S
  | _, _, _, .Prod q₁ q₂ =>
      OpKind.prod ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, .Apply q₁ q₂ =>
      OpKind.apply ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, .Sum q₁ q₂ =>
      OpKind.union ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, .Dedup q => OpKind.dedup ∈ S ∧ q.usesOnly S
  | _, _, _, .Diff q₁ q₂ =>
      OpKind.diff ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, .Alt _ _ q => q.usesOnly S
  | _, _, _, .Retag _ q => q.usesOnly S
  | _, _, _, .Mu _ _ _ => False
  | _, _, _, .MuSet _ _ _ => False
  | _, _, _, .Gamma _ _ _ q _ _ => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .GammaScalar _ _ q _ => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .GammaNest _ _ _ _ q => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  | _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, .Win _ _ _ _ _ _ q _ _ _ => OpKind.win ∈ S ∧ q.usesOnly S
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => OpKind.win ∈ S ∧ q.usesOnly S

omit [ValueType T] in
/-- Transporting a query along an equality of kind vectors changes no
operator, so it changes nothing `usesOnly` sees. -/
@[simp] theorem AggQueryIn.usesOnly_castKind {c n : ℕ}
    {κ κ' : Fin n → ColKind} (h : κ = κ') (q : AggQueryIn T c n κ)
    (S : Set OpKind) : (q.castKind h).usesOnly S ↔ q.usesOnly S := by
  cases h
  exact Iff.rfl

omit [ValueType T] in
/-- **Substituting the outer columns changes no operator**, so it changes
nothing `usesOnly` sees. This is what carries the classification through
the apply, whose right side is read under a substitution. -/
theorem AggQueryIn.usesOnly_substMap {S : Set OpKind} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).usesOnly S ↔ q.usesOnly S := by
  intro c n κ q
  induction q with
  | Rel n s => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    show (AggQueryIn.castKind _ (AggQueryIn.Proj
      (fun j => (ps j).substMap θ) (q.substMap θ))).usesOnly S ↔ _
    rw [AggQueryIn.usesOnly_castKind]
    exact and_congr Iff.rfl (ih θ)
  | Sel φ q ih => exact fun θ => and_congr Iff.rfl (ih θ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ θ))
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ _))
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ θ))
  | Dedup q ih => exact fun θ => and_congr Iff.rfl (ih θ)
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ θ))
  | Alt k h q ih => exact fun θ => ih θ
  | Retag h q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun θ => Iff.rfl
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun θ => Iff.rfl
  | Gamma is ts fs q keep ord ih =>
    exact fun θ => and_congr Iff.rfl (ih θ)
  | GammaScalar ts fs q ord ih => exact fun θ => and_congr Iff.rfl (ih θ)
  | GammaNest is his pc f q ih => exact fun θ => and_congr Iff.rfl (ih θ)
  | GammaTok is his ts fs a q keep ih => exact fun θ => Iff.rfl
  | ProvSum is his t q ih => exact fun θ => Iff.rfl
  | Win P O o w t f q hrr dist keep ih =>
    exact fun θ => and_congr Iff.rfl (ih θ)
  | WinExpr P O o ws ts fs g q keeps ih =>
    exact fun θ => and_congr Iff.rfl (ih θ)

/-- **Expressibility**: two queries of the same arity are equivalent when
their plain semantics agree on every instance. -/
def AggQueryIn.PlainEquiv {c n : ℕ} {κ κ' : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (q' : AggQueryIn T c n κ') : Prop :=
  ∀ (D : Database T) (γ : Fin c → T), q.evaluatePlain D γ = q'.evaluatePlain D γ

/-- An instance all of whose relations are empty. A name the instance
does not hold reads as the empty relation too, so this is the instance
over which nothing is there. -/
def Database.allEmpty (D : Database T) : Prop :=
  ∀ (k : ℕ) (s : String) (r : Relation T k), D.find k s = some r → r = 0

omit [ValueType T] in
/-- The empty list of relations is such an instance. -/
theorem Database.allEmpty_nil : Database.allEmpty ([] : Database T) := by
  intro k s r h
  have hnone : (none : Option (Relation T k)) = some r := h
  exact (Option.some_ne_none r hnone.symm).elim

/-! ## Schemas, and what a relation reference may name

A reference to a relation the instance does not hold reads as the empty
relation here, `Database.find` returning an `Option` that every
evaluator's `Rel` clause sends to `∅`. That is a convention about
ill-formed queries, not semantics: a query is written against a
*schema*, and the question what `R` means on an instance without `R`
should not arise. These definitions say when it does not, so that a
statement about plain evaluation can ask for a well-formed query and a
conforming instance instead of reading an absent name as empty.

(The same hypotheses are what a reading that made evaluation *partial*
would need: the condition is static, so it belongs in the hypotheses and
not in the evaluator's result type.) -/

/-- A schema: the arity of each relation name it declares. -/
def Schema := String → Option ℕ

/-- The schema declaring nothing. -/
def Schema.empty : Schema := fun _ => none

/-- Declaring one name, as a recursion's rounds do for the name they
bind. -/
def Schema.update (sch : Schema) (s : String) (k : ℕ) : Schema :=
  fun s' => if s' = s then some k else sch s'

/-- **A well-formed query**: every relation reference names a relation the
schema declares, at the arity the schema gives it. A recursion's body is
read in the schema extended by the name its rounds bind. -/
def AggQueryIn.overSchema (sch : Schema) : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Prop
  | _, _, _, .Rel n s => sch s = some n
  | _, _, _, .Empty => True
  | _, _, _, .Proj _ q => q.overSchema sch
  | _, _, _, .Sel _ q => q.overSchema sch
  | _, _, _, .Prod q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, .Apply q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, .Sum q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, .Dedup q => q.overSchema sch
  | _, _, _, .Diff q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, .Alt _ _ q => q.overSchema sch
  | _, _, _, .Retag _ q => q.overSchema sch
  | _, n, _, .Mu s q₀ q₁ =>
      sch s = none ∧ q₀.overSchema sch ∧ q₁.overSchema (sch.update s n)
  | _, n, _, .MuSet s q₀ q₁ =>
      sch s = none ∧ q₀.overSchema (sch.update s n)
        ∧ q₁.overSchema (sch.update s n)
  | _, _, _, .Gamma _ _ _ q _ _ => q.overSchema sch
  | _, _, _, .GammaScalar _ _ q _ => q.overSchema sch
  | _, _, _, .GammaNest _ _ _ _ q => q.overSchema sch
  | _, _, _, .GammaTok _ _ _ _ _ q _ => q.overSchema sch
  | _, _, _, .ProvSum _ _ _ q => q.overSchema sch
  | _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.overSchema sch
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.overSchema sch

/-- **A conforming instance**: it binds every name the schema declares, at
the declared arity. -/
def Database.Conforms (sch : Schema) (D : Database T) : Prop :=
  ∀ (s : String) (k : ℕ), sch s = some k → ∃ r : Relation T k,
    D.find k s = some r

/-- **Expressibility over a schema**: the two queries agree on every
instance *of that schema*, which is what the generation statement asks –
a query is not evaluated on an instance of another schema. Agreement on
every instance is stronger, and gives this one. -/
def AggQueryIn.PlainEquivOn (sch : Schema) {c n : ℕ}
    {κ κ' : Fin n → ColKind} (q : AggQueryIn T c n κ)
    (q' : AggQueryIn T c n κ') : Prop :=
  ∀ D : Database T, Database.Conforms sch D → ∀ γ : Fin c → T,
    q.evaluatePlain D γ = q'.evaluatePlain D γ

theorem AggQueryIn.PlainEquivOn_of_PlainEquiv {sch : Schema} {c n : ℕ}
    {κ κ' : Fin n → ColKind} {q : AggQueryIn T c n κ}
    {q' : AggQueryIn T c n κ'} (h : q.PlainEquiv q') :
    q.PlainEquivOn sch q' := fun D _ γ => h D γ

omit [ValueType T] in
/-- **A reference of a well-formed query resolves.** So the `∅` branch of
the `Rel` clause is unreachable for a well-formed query on a conforming
instance, and nothing in a statement about them reads an absent name as
empty. -/
theorem AggQueryIn.exists_find_of_overSchema {sch : Schema} {D : Database T}
    (hD : Database.Conforms sch D) {c n : ℕ} {s : String}
    (h : (AggQueryIn.Rel (T := T) (c := c) n s).overSchema sch) :
    ∃ r : Relation T n, D.find n s = some r :=
  hD s n h

omit [ValueType T] in
/-- **Binding a round's name keeps the instance conforming.** A
recursion reads its body with the bound name assigned to the previous
round, and `Database.assign` is a cons – so the name is found at the
front. Under well-formedness the bound name is fresh, which is what makes
that shadowing invisible: the schema declares it only in the extended
schema the body is read in. -/
theorem Database.Conforms.assign {sch : Schema} {D : Database T}
    (hD : Database.Conforms sch D) (s : String) {k : ℕ}
    (X : Relation T k) :
    Database.Conforms (sch.update s k) (D.assign s X) := by
  intro s' k' h
  by_cases hs : s' = s
  · subst hs
    rw [Schema.update, ite_eq_left rfl] at h
    obtain rfl : k' = k := (Option.some.inj h).symm
    exact ⟨X, Database.find_assign s' X D⟩
  · rw [Schema.update, ite_eq_right hs] at h
    obtain ⟨r, hr⟩ := hD s' k' h
    exact ⟨r, (Database.find_assign_of_ne s s' X D
      (fun hc => hs hc.2)).trans hr⟩

omit [ValueType T] in
/-- **Over the empty schema nothing can be written without `∅`.** Every
leaf of a query is a relation reference or the empty relation, and the
empty schema declares no name – so the empty relation is the only leaf
there, and a generating set that omits it generates nothing. This is what
the genericity reading of the `∅` row asks: the language is to be defined
for every schema, the empty one included. It is *not* that the unit
relation needs `∅`: with any name in the schema, `γ_∅[](R)` is the unit,
whatever `R` holds. -/
theorem AggQueryIn.usesEmpty_of_overSchema_empty {S : Set OpKind} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.overSchema Schema.empty → q.usesOnly S → OpKind.empty ∈ S := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro h _
    have hnone : (none : Option ℕ) = some n := h
    exact (Option.some_ne_none n hnone.symm).elim
  | Empty => intro _ h; exact h
  | Proj ps q ih => intro h hq; exact ih h hq.2
  | Sel φ q ih => intro h hq; exact ih h hq.2
  | Prod q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Apply q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Sum q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Dedup q ih => intro h hq; exact ih h hq.2
  | Diff q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Alt k hk q ih => intro h hq; exact ih h hq
  | Retag hk q ih => intro h hq; exact ih h hq
  | Mu s q₀ q₁ ih₀ ih₁ => intro _ hq; exact hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => intro _ hq; exact hq.elim
  | Gamma is ts fs q keep ord ih => intro h hq; exact ih h hq.2
  | GammaScalar ts fs q ord ih => intro h hq; exact ih h hq.2
  | GammaNest is his p f q ih => intro h hq; exact ih h hq.2
  | GammaTok is his ts fs a q keep ih => intro _ hq; exact hq.elim
  | ProvSum is his t q ih => intro _ hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih => intro h hq; exact ih h hq.2
  | WinExpr P O o ws ts fs g q keeps ih => intro h hq; exact ih h hq.2

/-! ## Counting rows: two facts the invariants run on -/

/-- The length of a family's canonical indexing is the relation's size. -/
theorem OccFam.size_ofSorted {α : Type} [LinearOrder α] (s : Multiset α) :
    (OccFam.ofSorted s).size = Multiset.card s := by
  rw [← OccFam.card_toMultiset, OccFam.toMultiset_ofSorted]

omit [ValueType T] in
/-- **The size of a join**: the product of the two sizes. -/
theorem Relation.card_hMul {n m : ℕ} (r₁ : Relation T n) (r₂ : Relation T m) :
    Multiset.card (r₁ * r₂) = Multiset.card r₁ * Multiset.card r₂ := by
  show Multiset.card (Multiset.map
    (fun p : Tuple T n × Tuple T m => Fin.append p.1 p.2)
    (Multiset.product r₁ r₂)) = _
  rw [Multiset.card_map]
  exact Multiset.card_product r₁ r₂

omit [ValueType T] in
/-- **The size of a union**: the sum of the two sizes. -/
theorem Relation.card_add {n : ℕ} (r₁ r₂ : Relation T n) :
    Multiset.card (r₁ + r₂) = Multiset.card r₁ + Multiset.card r₂ :=
  Multiset.card_add r₁ r₂

omit [ValueType T] in
/-- Filtering and deduplicating only remove rows. -/
theorem Multiset.card_dedup_le {α : Type} [DecidableEq α] (s : Multiset α) :
    Multiset.card s.dedup ≤ Multiset.card s :=
  Multiset.card_le_card (Multiset.dedup_le s)

/-! ## Union: the one operator that duplicates a row

Without `⊎`, an instance whose relations hold at most one row has an
answer of at most one row: a projection and a window map it row by row, a
selection, duplicate elimination and a difference only remove, a product
and an apply read one row of each side, and an aggregation emits one row
per group – one group, here, or none. -/

/-- An instance no relation of which holds more than one row. -/
def Database.Thin (D : Database T) : Prop :=
  ∀ (k : ℕ) (s : String) (r : Relation T k), D.find k s = some r →
    Multiset.card r ≤ 1

/-- **Without `⊎`, a thin instance has an answer of at most one row.** -/
theorem AggQueryIn.card_le_one_of_thin {S : Set OpKind}
    (hu : OpKind.union ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly S → ∀ (D : Database T), Database.Thin D → ∀ γ : Fin c → T,
      Multiset.card (q.evaluatePlain D γ) ≤ 1 := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro _ D hD γ
    simp only [AggQueryIn.evaluatePlain]
    cases hf : D.find n s with
    | none => exact Nat.zero_le 1
    | some rn => exact hD n s rn hf
  | Empty => intro _ D hD γ; exact Nat.zero_le 1
  | Proj ps q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact ih hq.2 D hD γ
  | Sel φ q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (ih hq.2 D hD γ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    rw [Relation.card_hMul]
    exact le_trans (Nat.mul_le_mul (ih₁ hq.2.1 D hD γ) (ih₂ hq.2.2 D hD γ))
      (le_of_eq (one_mul 1))
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_bind]
    rcases Nat.lt_or_ge (Multiset.card (q₁.evaluatePlain D γ)) 1 with h | h
    · rw [Multiset.card_eq_zero.mp (Nat.lt_one_iff.mp h)]
      exact Nat.zero_le 1
    · obtain ⟨u, hu⟩ :=
        Multiset.card_eq_one.mp (le_antisymm (ih₁ hq.2.1 D hD γ) h)
      rw [hu]
      simp only [Multiset.map_singleton, Multiset.sum_singleton,
        Function.comp_apply, Multiset.card_map]
      exact ih₂ hq.2.2 D hD _
  | Sum q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 hu
  | Dedup q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    exact le_trans (Multiset.card_dedup_le _) (ih hq.2 D hD γ)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (ih₁ hq.2.1 D hD γ)
  | Alt k hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | Retag hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | Mu s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D hD γ)
  | GammaScalar ts fs q ord ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    rfl
  | GammaNest is his p f q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D hD γ)
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact ih hq.2 D hD γ
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, OccFam.card_toMultiset]
    rw [OccFam.size_ofSorted]
    exact ih hq.2 D hD γ

/-- **And a union of two constant rows breaks it**: `{u} ⊎ {u}` holds two
rows on every instance, thin ones included. So no generating set omits
`⊎`. -/
theorem AggQueryIn.card_values_two {k : ℕ} (u : Tuple T k) (D : Database T)
    (γ : Fin 0 → T) :
    Multiset.card ((AggQueryIn.values [u, u] (by simp)).evaluatePlain D γ)
      = 2 := by
  rw [AggQueryIn.evaluatePlain_values [u, u] (by simp) D γ]
  rfl

/-! ## Selection and difference: the two operators that can lose a row

Without `σ` and `−`, a query is either empty on every instance of its
schema, or non-empty on every instance of it whose relations are all
non-empty: nothing else can turn rows away. The disjunction is uniform in
the outer context, which is what the apply needs – without a selection
the outer row enters its right side only through terms, and a term
decides no row's presence. -/

/-- An instance of the schema no relation of which is empty. -/
def Database.Full (sch : Schema) (D : Database T) : Prop :=
  ∀ (s : String) (k : ℕ), sch s = some k → ∃ r : Relation T k,
    D.find k s = some r ∧ r ≠ 0

omit [ValueType T] in
/-- A full instance conforms. -/
theorem Database.Full.conforms {sch : Schema} {D : Database T}
    (h : Database.Full sch D) : Database.Conforms sch D :=
  fun s k hk => let ⟨r, hr, _⟩ := h s k hk; ⟨r, hr⟩

/-- A family stands for no row exactly when it indexes none. -/
theorem OccFam.toMultiset_eq_zero_iff {α : Type} (r : OccFam α) :
    r.toMultiset = 0 ↔ r.size = 0 := by
  rw [← Multiset.card_eq_zero, OccFam.card_toMultiset]

/-- A family built on another's indices stands for no row only if that
one indexes none – the shape a window's answer has. -/
theorem OccFam.size_eq_zero_of_mk_toMultiset {α β : Type} (r : OccFam α)
    (f : Fin r.size → β) (h : (OccFam.mk r.size f).toMultiset = 0) :
    r.size = 0 :=
  (OccFam.toMultiset_eq_zero_iff (OccFam.mk r.size f)).mp h

omit [ValueType T] in
/-- Mapping keeps a relation empty, and keeps it non-empty. -/
theorem Multiset.map_eq_zero_iff {α β : Type} (f : α → β) (s : Multiset α) :
    Multiset.map f s = 0 ↔ s = 0 := by
  constructor
  · intro h
    rw [← Multiset.card_eq_zero, ← Multiset.card_map f s, h]
    rfl
  · intro h; rw [h]; rfl

omit [ValueType T] in
/-- So does deduplicating. -/
theorem Multiset.dedup_eq_zero_iff {α : Type} [DecidableEq α]
    (s : Multiset α) : s.dedup = 0 ↔ s = 0 := by
  constructor
  · intro h
    refine Multiset.eq_zero_of_forall_notMem (fun a ha => ?_)
    have hz : a ∈ (0 : Multiset α) := h ▸ (Multiset.mem_dedup).mpr ha
    exact Multiset.notMem_zero a hz
  · intro h; rw [h]; rfl

/-- **Without `σ` and `−`, a query is empty everywhere or non-empty on
every full instance.** -/
theorem AggQueryIn.zero_or_ne_zero_of_noSelDiff {S : Set OpKind}
    (hsel : OpKind.sel ∉ S) (hdiff : OpKind.diff ∉ S) {sch : Schema} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly S → q.overSchema sch →
      (∀ (D : Database T) (γ : Fin c → T), q.evaluatePlain D γ = 0)
        ∨ (∀ (D : Database T) (γ : Fin c → T), Database.Full sch D →
            q.evaluatePlain D γ ≠ 0) := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro _ hw
    refine Or.inr (fun D γ hD => ?_)
    obtain ⟨r, hr, hne⟩ := hD s n hw
    simp only [AggQueryIn.evaluatePlain, hr]
    exact hne
  | Empty => exact fun _ _ => Or.inl (fun D γ => rfl)
  | Proj ps q ih =>
    intro hq hw
    rcases ih hq.2 hw with h | h
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain, h D γ]
      rfl
    · refine Or.inr (fun D γ hD => ?_)
      simp only [AggQueryIn.evaluatePlain]
      exact fun hc => h D γ hD ((Multiset.map_eq_zero_iff _ _).mp hc)
  | Sel φ q ih => intro hq; exact absurd hq.1 hsel
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hw
    rcases ih₁ hq.2.1 hw.1 with h₁ | h₁
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain]
      refine Multiset.card_eq_zero.mp ?_
      rw [Relation.card_hMul, h₁ D γ, Multiset.card_zero, Nat.zero_mul]
    · rcases ih₂ hq.2.2 hw.2 with h₂ | h₂
      · refine Or.inl (fun D γ => ?_)
        simp only [AggQueryIn.evaluatePlain]
        refine Multiset.card_eq_zero.mp ?_
        rw [Relation.card_hMul, h₂ D γ, Multiset.card_zero, Nat.mul_zero]
      · refine Or.inr (fun D γ hD hc => ?_)
        simp only [AggQueryIn.evaluatePlain] at hc
        have h0 : Multiset.card (q₁.evaluatePlain D γ)
            * Multiset.card (q₂.evaluatePlain D γ) = 0 := by
          rw [← Relation.card_hMul]
          exact Multiset.card_eq_zero.mpr hc
        rcases Nat.mul_eq_zero.mp h0 with hz | hz
        · exact h₁ D γ hD (Multiset.card_eq_zero.mp hz)
        · exact h₂ D γ hD (Multiset.card_eq_zero.mp hz)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hw
    rcases ih₁ hq.2.1 hw.1 with h₁ | h₁
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain, h₁ D γ]
      rfl
    · rcases ih₂ hq.2.2 hw.2 with h₂ | h₂
      · refine Or.inl (fun D γ => ?_)
        simp only [AggQueryIn.evaluatePlain]
        refine Multiset.eq_zero_of_forall_notMem (fun v hv => ?_)
        obtain ⟨u, -, hv'⟩ := Multiset.mem_bind.mp hv
        obtain ⟨w, hw', -⟩ := Multiset.mem_map.mp hv'
        exact absurd (h₂ D (Fin.append u γ)) (fun hc => by
          rw [hc] at hw'; exact Multiset.notMem_zero w hw')
      · refine Or.inr (fun D γ hD hc => ?_)
        simp only [AggQueryIn.evaluatePlain] at hc
        rw [← Multiset.card_eq_zero, Multiset.card_bind] at hc
        obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero (h₁ D γ hD)
        have hzero := (Multiset.sum_eq_zero_iff.mp hc) _
          (Multiset.mem_map.mpr ⟨u, hu, rfl⟩)
        refine h₂ D (Fin.append u γ) hD (Multiset.card_eq_zero.mp ?_)
        simpa only [Function.comp_apply, Multiset.card_map] using hzero
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hw
    rcases ih₁ hq.2.1 hw.1 with h₁ | h₁
    · rcases ih₂ hq.2.2 hw.2 with h₂ | h₂
      · refine Or.inl (fun D γ => ?_)
        simp only [AggQueryIn.evaluatePlain, h₁ D γ, h₂ D γ]
        rfl
      · refine Or.inr (fun D γ hD hc => ?_)
        simp only [AggQueryIn.evaluatePlain] at hc
        refine h₂ D γ hD (Multiset.card_eq_zero.mp ?_)
        have hsum := Multiset.card_add (q₁.evaluatePlain D γ)
          (q₂.evaluatePlain D γ)
        rw [hc, Multiset.card_zero] at hsum
        omega
    · refine Or.inr (fun D γ hD hc => ?_)
      simp only [AggQueryIn.evaluatePlain] at hc
      refine h₁ D γ hD (Multiset.card_eq_zero.mp ?_)
      have hsum := Multiset.card_add (q₁.evaluatePlain D γ)
        (q₂.evaluatePlain D γ)
      rw [hc, Multiset.card_zero] at hsum
      omega
  | Dedup q ih =>
    intro hq hw
    rcases ih hq.2 hw with h | h
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain, h D γ]
      rfl
    · refine Or.inr (fun D γ hD => ?_)
      simp only [AggQueryIn.evaluatePlain]
      exact fun hc => h D γ hD ((Multiset.dedup_eq_zero_iff _).mp hc)
  | Diff q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 hdiff
  | Alt k hk q ih => intro hq hw; exact ih hq hw
  | Retag hk q ih => intro hq hw; exact ih hq hw
  | Mu s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hq hw
    rcases ih hq.2 hw with h | h
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain, h D γ]
      rfl
    · refine Or.inr (fun D γ hD => ?_)
      simp only [AggQueryIn.evaluatePlain]
      exact fun hc => h D γ hD ((Multiset.map_eq_zero_iff _ _).mp
        ((Multiset.dedup_eq_zero_iff _).mp
          ((Multiset.map_eq_zero_iff _ _).mp hc)))
  | GammaScalar ts fs q ord ih =>
    intro hq hw
    refine Or.inr (fun D γ _ => ?_)
    simp only [AggQueryIn.evaluatePlain]
    exact fun hc => absurd (congrArg Multiset.card hc) (by simp)
  | GammaNest is his p f q ih =>
    intro hq hw
    rcases ih hq.2 hw with h | h
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain, h D γ]
      rfl
    · refine Or.inr (fun D γ hD => ?_)
      simp only [AggQueryIn.evaluatePlain]
      exact fun hc => h D γ hD ((Multiset.map_eq_zero_iff _ _).mp
        ((Multiset.dedup_eq_zero_iff _).mp
          ((Multiset.map_eq_zero_iff _ _).mp hc)))
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq hw
    rcases ih hq.2 hw with h | h
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain]
      rw [h D γ]
      rfl
    · refine Or.inr (fun D γ hD hc => ?_)
      simp only [AggQueryIn.evaluatePlain] at hc
      exact h D γ hD ((Multiset.map_eq_zero_iff _ _).mp hc)
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq hw
    rcases ih hq.2 hw with h | h
    · refine Or.inl (fun D γ => ?_)
      simp only [AggQueryIn.evaluatePlain]
      rw [h D γ]
      rfl
    · refine Or.inr (fun D γ hD hc => ?_)
      simp only [AggQueryIn.evaluatePlain] at hc
      refine h D γ hD (Multiset.card_eq_zero.mp ?_)
      exact (OccFam.size_ofSorted (q.evaluatePlain D γ)).symm.trans
        (OccFam.size_eq_zero_of_mk_toMultiset _ _ hc)

/-- The schema of one unary relation, for the witnesses below. -/
def schemaR : Schema := fun s => if s = "R" then some 1 else none

/-- An instance of it holding the row `(1)`. -/
def dOne : Database ℕ := [("R", ⟨1, ({![1]} : Multiset (Tuple ℕ 1))⟩)]

/-- And one holding the row `(0)`. -/
def dZero : Database ℕ := [("R", ⟨1, ({![0]} : Multiset (Tuple ℕ 1))⟩)]

/-- `σ_{#0 = 1}(R)`, the witness of the selection row. -/
def selWitness : AggQuery ℕ 1 (ColKind.allReg 1) :=
  AggQueryIn.Sel (GenPredIn.cmp CompOp.eq (TermGIn.index 0 rfl)
    (TermGIn.const 1)) (AggQueryIn.Rel 1 "R")

theorem full_dOne : Database.Full schemaR dOne := by
  intro s k h
  by_cases hs : s = "R"
  · subst hs
    rw [schemaR, ite_eq_left rfl] at h
    obtain rfl : k = 1 := (Option.some.inj h).symm
    exact ⟨({![1]} : Multiset (Tuple ℕ 1)), rfl, fun hc =>
      absurd (congrArg Multiset.card hc) (by simp)⟩
  · rw [schemaR, ite_eq_right hs] at h
    exact absurd h (fun hc => Option.some_ne_none k hc.symm)

theorem full_dZero : Database.Full schemaR dZero := by
  intro s k h
  by_cases hs : s = "R"
  · subst hs
    rw [schemaR, ite_eq_left rfl] at h
    obtain rfl : k = 1 := (Option.some.inj h).symm
    exact ⟨({![0]} : Multiset (Tuple ℕ 1)), rfl, fun hc =>
      absurd (congrArg Multiset.card hc) (by simp)⟩
  · rw [schemaR, ite_eq_right hs] at h
    exact absurd h (fun hc => Option.some_ne_none k hc.symm)

/-- **And a selection breaks it**: it keeps the row of one full instance
and none of the other's, so it is neither empty everywhere nor non-empty
on every full instance. So no generating set omits `σ` – nor `−`, by the
same witness read through the swap. -/
theorem selWitness_breaks :
    ¬ ((∀ (D : Database ℕ) (γ : Fin 0 → ℕ),
          selWitness.evaluatePlain D γ = 0)
      ∨ (∀ (D : Database ℕ) (γ : Fin 0 → ℕ), Database.Full schemaR D →
          selWitness.evaluatePlain D γ ≠ 0)) := by
  rintro (h | h)
  · exact absurd (congrArg Multiset.card (h dOne (fun j => j.elim0)))
      (by decide)
  · exact h dZero (fun j => j.elim0) full_dZero
      (Multiset.card_eq_zero.mp (by decide))

/-! ## Product and apply: the two operators that multiply

Without them an answer grows linearly in the instance: a projection, a
selection, a window, duplicate elimination, a difference and an
aggregation each give at most as many rows as they read, and a union adds
two such bounds. The `+ 1` is there for the scalar aggregation, whose row
is there even on the empty instance. -/

/-- The number of rows an instance holds. -/
def Database.size (D : Database T) : ℕ :=
  (D.map (fun e => Multiset.card e.2.2)).sum

omit [ValueType T] in
/-- A relation of the instance is no larger than the instance. -/
theorem Database.card_le_size : ∀ (D : Database T) {k : ℕ} {s : String}
    {r : Relation T k}, D.find k s = some r → Multiset.card r ≤ D.size
  | [], k, s, r, h => absurd h (fun hc =>
      Option.some_ne_none r ((show (none : Option (Relation T k)) = some r
        from hc).symm))
  | (s', ⟨m, M⟩) :: tl, k, s, r, h => by
    rw [Database.size, List.map_cons, List.sum_cons]
    by_cases hc : k = m ∧ s = s'
    · obtain ⟨rfl, rfl⟩ := hc
      have h' : Database.find k s ((s, ⟨k, M⟩) :: tl) = some M := by
        show Database.find.f k s ((s, ⟨k, M⟩) :: tl) = some M
        rw [Database.find.f, dite_eq_left ⟨rfl, rfl⟩]
        rfl
      rw [h'] at h
      obtain rfl : r = M := (Option.some.inj h).symm
      exact Nat.le_add_right _ _
    · have htl : Database.find k s tl = some r := by
        have hstep : Database.find k s ((s', ⟨m, M⟩) :: tl)
            = Database.find k s tl := by
          show Database.find.f k s ((s', ⟨m, M⟩) :: tl)
            = Database.find.f k s tl
          rw [Database.find.f, dite_eq_right hc]
        rw [hstep] at h
        exact h
      exact le_trans (Database.card_le_size tl htl) (Nat.le_add_left _ _)

/-- The bound a query gives on its answer's size, per row of the
instance. -/
def AggQueryIn.sizeBound : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → ℕ
  | _, _, _, .Rel _ _ => 1
  | _, _, _, .Empty => 0
  | _, _, _, .Proj _ q => q.sizeBound
  | _, _, _, .Sel _ q => q.sizeBound
  | _, _, _, .Prod _ _ => 0
  | _, _, _, .Apply _ _ => 0
  | _, _, _, .Sum q₁ q₂ => q₁.sizeBound + q₂.sizeBound
  | _, _, _, .Dedup q => q.sizeBound
  | _, _, _, .Diff q₁ _ => q₁.sizeBound
  | _, _, _, .Alt _ _ q => q.sizeBound
  | _, _, _, .Retag _ q => q.sizeBound
  | _, _, _, .Mu _ _ _ => 0
  | _, _, _, .MuSet _ _ _ => 0
  | _, _, _, .Gamma _ _ _ q _ _ => q.sizeBound
  | _, _, _, .GammaScalar _ _ _ _ => 1
  | _, _, _, .GammaNest _ _ _ _ q => q.sizeBound
  | _, _, _, .GammaTok _ _ _ _ _ q _ => q.sizeBound
  | _, _, _, .ProvSum _ _ _ q => q.sizeBound
  | _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.sizeBound
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.sizeBound

/-- **Without `×` and the apply, an answer is linear in the instance.** -/
theorem AggQueryIn.card_le_sizeBound {S : Set OpKind}
    (hp : OpKind.prod ∉ S) (ha : OpKind.apply ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly S → ∀ (D : Database T) (γ : Fin c → T),
      Multiset.card (q.evaluatePlain D γ) ≤ q.sizeBound * (D.size + 1) := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro _ D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, one_mul]
    cases hf : D.find n s with
    | none => exact Nat.zero_le _
    | some rn => exact le_trans (Database.card_le_size D hf) (Nat.le_succ _)
  | Empty => intro _ D γ; exact Nat.zero_le _
  | Proj ps q ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact ih hq.2 D γ
  | Sel φ q ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (ih hq.2 D γ)
  | Prod q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 hp
  | Apply q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 ha
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, Nat.add_mul]
    rw [Relation.card_add]
    exact Nat.add_le_add (ih₁ hq.2.1 D γ) (ih₂ hq.2.2 D γ)
  | Dedup q ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    exact le_trans (Multiset.card_dedup_le _) (ih hq.2 D γ)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (ih₁ hq.2.1 D γ)
  | Alt k hk q ih => intro hq D γ; exact ih hq D γ
  | Retag hk q ih => intro hq D γ; exact ih hq D γ
  | Mu s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D γ)
  | GammaScalar ts fs q ord ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, one_mul]
    exact Nat.succ_le_succ (Nat.zero_le _)
  | GammaNest is his p f q ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D γ)
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact ih hq.2 D γ
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      OccFam.card_toMultiset]
    exact le_trans (le_of_eq (OccFam.size_ofSorted _)) (ih hq.2 D γ)

/-- An instance whose relation holds `m` copies of one row. -/
def dRep (m : ℕ) : Database ℕ :=
  [("R", ⟨1, (Multiset.replicate m ![0] : Multiset (Tuple ℕ 1))⟩)]

theorem size_dRep (m : ℕ) : (dRep m).size = m := by
  rw [Database.size, dRep]
  simp

theorem find_dRep (m : ℕ) :
    (dRep m).find 1 "R" = some (Multiset.replicate m ![0]) := by
  show Database.find.f 1 "R"
    [("R", ⟨1, (Multiset.replicate m ![0] : Multiset (Tuple ℕ 1))⟩)] = _
  rw [Database.find.f, dite_eq_left ⟨rfl, rfl⟩]
  rfl

/-- `R × R`, the witness of the product row. -/
def prodWitness : AggQuery ℕ (1 + 1)
    (Fin.append (ColKind.allReg 1) (ColKind.allReg 1)) :=
  AggQueryIn.Prod (AggQueryIn.Rel 1 "R") (AggQueryIn.Rel 1 "R")

theorem card_prodWitness (m : ℕ) :
    Multiset.card (prodWitness.evaluatePlain (dRep m) (fun j => j.elim0))
      = m * m := by
  show Multiset.card ((AggQueryIn.Rel (T := ℕ) (c := 0) 1 "R").evaluatePlain
      (dRep m) (fun j => j.elim0)
    * (AggQueryIn.Rel (T := ℕ) (c := 0) 1 "R").evaluatePlain (dRep m)
      (fun j => j.elim0)) = m * m
  rw [Relation.card_hMul]
  show Multiset.card (match (dRep m).find 1 "R" with
      | none => (∅ : Multiset (Tuple ℕ 1))
      | some rn => rn) * Multiset.card (match (dRep m).find 1 "R" with
      | none => (∅ : Multiset (Tuple ℕ 1))
      | some rn => rn) = m * m
  rw [find_dRep]
  simp

/-- **And a join of a relation with itself breaks it**: on an instance of
`m` rows it has `m²`, which no multiple of `m + 1` bounds. So no
generating set omits both `×` and the apply. -/
theorem prodWitness_no_linear_bound :
    ¬ ∃ c : ℕ, ∀ D : Database ℕ,
      Multiset.card (prodWitness.evaluatePlain D (fun j => j.elim0))
        ≤ c * (D.size + 1) := by
  rintro ⟨c, h⟩
  have hc := h (dRep (c + 2))
  rw [card_prodWitness, size_dRep] at hc
  refine absurd hc (not_le.mpr ?_)
  calc c * (c + 2 + 1) = c * c + 3 * c := by ring
    _ < c * c + (4 * c + 4) := Nat.add_lt_add_left (by omega) _
    _ = (c + 2) * (c + 2) := by ring

/-! ## Projection: the one operator that merges rows

Without `Π`, a row's multiplicity is bounded by the query alone over an
instance that has no duplicate: a union adds two bounds and a product or
an apply multiplies them, while nothing else raises a multiplicity –
aggregation and duplicate elimination bring it to one, and a selection, a
difference and a window leave it alone. A projection is what merges rows
that differ in a dropped column, and its answer's multiplicity grows with
the instance. -/

/-- An instance no relation of which holds a duplicate. -/
def Database.Nodup (D : Database T) : Prop :=
  ∀ (k : ℕ) (s : String) (r : Relation T k), D.find k s = some r → r.Nodup

omit [ValueType T] in
/-- Summing a function supported at one point over a multiset. -/
theorem Multiset.sum_map_ite_eq {α : Type} [DecidableEq α] (s : Multiset α)
    (a : α) (b : ℕ) :
    (s.map (fun x => if x = a then b else 0)).sum = Multiset.count a s * b := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
    by_cases hx : x = a
    · rw [ite_eq_left hx, ite_eq_left hx.symm, Nat.add_mul, Nat.one_mul,
        Nat.add_comm]
    · rw [ite_eq_right hx, ite_eq_right (fun hc => hx hc.symm), Nat.add_zero,
        Nat.zero_add]

omit [ValueType T] in
/-- A pointwise bound carries to the sums. -/
theorem Multiset.sum_map_le {α : Type} (s : Multiset α) (f g : α → ℕ)
    (h : ∀ x, f x ≤ g x) : (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => exact le_refl 0
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
      Multiset.sum_cons]
    exact Nat.add_le_add (h x) ih

omit [ValueType T] in
/-- **A join read as an apply**: pairing each row of the left with the
rows of the right. -/
theorem Relation.hMul_eq_bind {n m : ℕ} (r₁ : Relation T n)
    (r₂ : Relation T m) :
    r₁ * r₂ = Multiset.bind r₁ (fun a =>
      Multiset.map (fun v => (Fin.append a v : Tuple T (n + m))) r₂) := by
  show Multiset.map (fun p : Tuple T n × Tuple T m => Fin.append p.1 p.2)
      (Multiset.bind r₁ (fun a => Multiset.map (Prod.mk a) r₂)) = _
  rw [Multiset.map_bind]
  exact congrArg _ (funext fun a => Multiset.map_map _ _ _)

/-- **The multiplicity of a row an apply produces**: its left half names
the outer row it came from, so only that row's copies contribute, each at
most the inner bound. -/
theorem Multiset.count_bind_append_le {n m : ℕ} (r : Relation T n)
    (g : Tuple T n → Relation T m) {b₁ b₂ : ℕ}
    (h₁ : ∀ x, Multiset.count x r ≤ b₁)
    (h₂ : ∀ a y, Multiset.count y (g a) ≤ b₂) (u : Tuple T (n + m)) :
    Multiset.count u (Multiset.bind r (fun a =>
        Multiset.map (fun v => (Fin.append a v : Tuple T (n + m))) (g a)))
      ≤ b₁ * b₂ := by
  classical
  rw [Multiset.count_bind]
  refine le_trans (Multiset.sum_map_le r _
    (fun a => if a = (fun i => u (Fin.castAdd m i)) then b₂ else 0)
    (fun a => ?_)) ?_
  · rw [Multiset.count_map]
    by_cases ha : a = (fun i => u (Fin.castAdd m i))
    · rw [ite_eq_left ha]
      refine le_trans (Multiset.card_le_card (Multiset.monotone_filter_right
        (g a) (q := fun v => (fun j => u (Fin.natAdd n j)) = v)
        (fun v hv => ?_))) ?_
      · exact (funext fun j => by rw [hv, Fin.append_right] :
          (fun j => u (Fin.natAdd n j)) = v)
      · exact le_trans
          (le_of_eq (Multiset.count_eq_card_filter_eq (g a) _).symm) (h₂ a _)
    · rw [ite_eq_right ha]
      refine Nat.le_zero.mpr (Multiset.card_eq_zero.mpr ?_)
      refine Multiset.filter_eq_nil.mpr (fun v _ hc => ?_)
      exact ha (funext fun i => by rw [hc, Fin.append_left])
  · rw [Multiset.sum_map_ite_eq]
    exact Nat.mul_le_mul_right b₂ (h₁ _)

/-- **A row of a grouping is one row**: the key can be read back off it,
and the keys are distinct. -/
theorem Multiset.count_map_dedup_le {n₁ nr : ℕ}
    (keys : Multiset (Tuple T n₁)) (f : Tuple T n₁ → Tuple T nr)
    (key : Tuple T nr → Tuple T n₁) (h : ∀ g, key (f g) = g)
    (u : Tuple T nr) : Multiset.count u (keys.dedup.map f) ≤ 1 := by
  classical
  rw [Multiset.count_map]
  refine le_trans (Multiset.card_le_card (Multiset.monotone_filter_right
    keys.dedup (q := fun g => key u = g) (fun g hg => ?_))) ?_
  · rw [hg, h g]
  · exact le_trans
      (le_of_eq (Multiset.count_eq_card_filter_eq keys.dedup _).symm)
      (Multiset.nodup_iff_count_le_one.mp (Multiset.nodup_dedup keys) _)

/-- **A row a window produces is as many as the row it extends**: the
window keeps the row it is computed for, and that row can be read back
off the one it produces. -/
theorem Multiset.count_map_snoc_le {n : ℕ} (rows : Multiset (Tuple T n))
    (g : Tuple T n → T) {b : ℕ}
    (hb : ∀ x, Multiset.count x rows ≤ b) (u : Tuple T (n + 1)) :
    Multiset.count u
        (rows.map (fun v => (Fin.snoc v (g v) : Tuple T (n + 1)))) ≤ b := by
  classical
  rw [Multiset.count_map]
  refine le_trans (Multiset.card_le_card (Multiset.monotone_filter_right rows
    (q := fun v => (fun k => u k.castSucc) = v) (fun v hv => ?_))) ?_
  · exact funext fun k => by rw [hv, Fin.snoc_castSucc]
  · exact le_trans (le_of_eq (Multiset.count_eq_card_filter_eq rows _).symm)
      (hb _)

/-- The same read off a family, which is the form a multi-frame window's
answer has. -/
theorem OccFam.count_mk_toMultiset_le {n nr : ℕ} (r : OccFam (Tuple T n))
    (f : Fin r.size → Tuple T nr) (key : Tuple T nr → Tuple T n)
    (h : ∀ i, key (f i) = r.row i) {b : ℕ}
    (hb : ∀ x, Multiset.count x r.toMultiset ≤ b) (u : Tuple T nr) :
    Multiset.count u ((OccFam.mk r.size f).toMultiset) ≤ b := by
  classical
  show Multiset.count u
    (Multiset.map f (Finset.univ : Finset (Fin r.size)).val) ≤ b
  rw [Multiset.count_map]
  refine le_trans (Multiset.card_le_card (Multiset.monotone_filter_right
    (Finset.univ : Finset (Fin r.size)).val (q := fun i => key u = r.row i)
    (fun i hi => ?_))) ?_
  · rw [hi, h i]
  · refine le_trans (le_of_eq ?_) (hb (key u))
    show _ = Multiset.count (key u)
      (Multiset.map r.row (Finset.univ : Finset (Fin r.size)).val)
    rw [Multiset.count_map]

/-- The bound a query gives on the multiplicity of a row of its answer,
over an instance that has no duplicate. -/
def AggQueryIn.multBound : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → ℕ
  | _, _, _, .Rel _ _ => 1
  | _, _, _, .Empty => 0
  | _, _, _, .Proj _ _ => 0
  | _, _, _, .Sel _ q => q.multBound
  | _, _, _, .Prod q₁ q₂ => q₁.multBound * q₂.multBound
  | _, _, _, .Apply q₁ q₂ => q₁.multBound * q₂.multBound
  | _, _, _, .Sum q₁ q₂ => q₁.multBound + q₂.multBound
  | _, _, _, .Dedup _ => 1
  | _, _, _, .Diff q₁ _ => q₁.multBound
  | _, _, _, .Alt _ _ q => q.multBound
  | _, _, _, .Retag _ q => q.multBound
  | _, _, _, .Mu _ _ _ => 0
  | _, _, _, .MuSet _ _ _ => 0
  | _, _, _, .Gamma _ _ _ _ _ _ => 1
  | _, _, _, .GammaScalar _ _ _ _ => 1
  | _, _, _, .GammaNest _ _ _ _ _ => 1
  | _, _, _, .GammaTok _ _ _ _ _ _ _ => 1
  | _, _, _, .ProvSum _ _ _ _ => 1
  | _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.multBound
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.multBound

/-- **Without `Π`, multiplicities are bounded by the query.** -/
theorem AggQueryIn.count_le_multBound {S : Set OpKind}
    (hpr : OpKind.proj ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly S → ∀ (D : Database T), Database.Nodup D →
      ∀ (γ : Fin c → T) (u : Tuple T n),
      Multiset.count u (q.evaluatePlain D γ) ≤ q.multBound := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro _ D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    cases hf : D.find n s with
    | none => exact Nat.zero_le 1
    | some rn =>
      exact Multiset.nodup_iff_count_le_one.mp (hD n s rn hf) u
  | Empty => intro _ D hD γ u; exact Nat.zero_le 0
  | Proj ps q ih => intro hq; exact absurd hq.1 hpr
  | Sel φ q ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact le_trans (Multiset.count_le_of_le u (Multiset.filter_le _ _))
      (ih hq.2 D hD γ u)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    rw [Relation.hMul_eq_bind]
    exact Multiset.count_bind_append_le _ _ (fun x => ih₁ hq.2.1 D hD γ x)
      (fun _ y => ih₂ hq.2.2 D hD γ y) u
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_bind_append_le _ _ (fun x => ih₁ hq.2.1 D hD γ x)
      (fun a y => ih₂ hq.2.2 D hD (Fin.append a γ) y) u
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    refine le_trans (le_of_eq (Multiset.count_add u _ _)) ?_
    exact Nat.add_le_add (ih₁ hq.2.1 D hD γ u) (ih₂ hq.2.2 D hD γ u)
  | Dedup q ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.nodup_iff_count_le_one.mp (Multiset.nodup_dedup _) u
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact le_trans (Multiset.count_le_of_le u (Multiset.filter_le _ _))
      (ih₁ hq.2.1 D hD γ u)
  | Alt k hk q ih => intro hq D hD γ u; exact ih hq D hD γ u
  | Retag hk q ih => intro hq D hD γ u; exact ih hq D hD γ u
  | Mu s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd _ k)) (fun g => funext fun k => by
        rw [Fin.append_left]) u
  | GammaScalar ts fs q ord ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact le_trans (Multiset.count_le_card u _) (le_of_eq rfl)
  | GammaNest is his p f q ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd _ k)) (fun g => funext fun k => by
        rw [Fin.append_left]) u
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_snoc_le _ _ (fun x => ih hq.2 D hD γ x) u
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    refine OccFam.count_mk_toMultiset_le _ _
      (fun v k => v k.castSucc) (fun i => funext fun k => by
        rw [Fin.snoc_castSucc]) (fun x => ?_) u
    rw [OccFam.toMultiset_ofSorted]
    exact ih hq.2 D hD γ x

/-- An instance whose relation holds `m` distinct rows sharing their
first column. -/
def dShared (m : ℕ) : Database ℕ :=
  [("S", ⟨2, (Multiset.map (fun i => ![0, i]) (Multiset.range m)
    : Multiset (Tuple ℕ 2))⟩)]

theorem find_dShared (m : ℕ) : (dShared m).find 2 "S"
    = some (Multiset.map (fun i => ![0, i]) (Multiset.range m)) := by
  show Database.find.f 2 "S"
    [("S", ⟨2, (Multiset.map (fun i => ![0, i]) (Multiset.range m)
      : Multiset (Tuple ℕ 2))⟩)] = _
  rw [Database.find.f, dite_eq_left ⟨rfl, rfl⟩]
  rfl

theorem nodup_dShared (m : ℕ) : Database.Nodup (dShared m) := by
  intro k s r h
  by_cases hc : k = 2 ∧ s = "S"
  · obtain ⟨rfl, rfl⟩ := hc
    obtain rfl : r = Multiset.map (fun i => ![0, i]) (Multiset.range m) :=
      (Option.some.inj ((find_dShared m).symm.trans h)).symm
    refine Multiset.Nodup.map (fun i j hij => ?_) (Multiset.nodup_range m)
    have := congrFun hij 1
    simpa using this
  · have hstep : Database.find k s (dShared m) = none := by
      show Database.find.f k s
        [("S", ⟨2, (Multiset.map (fun i => ![0, i]) (Multiset.range m)
          : Multiset (Tuple ℕ 2))⟩)] = none
      rw [Database.find.f, dite_eq_right hc]
      rfl
    exact absurd (hstep.symm.trans h)
      (fun hcc => Option.some_ne_none r hcc.symm)

/-- `Π_{#0}(S)`, the witness of the projection row. -/
def projWitness :=
  AggQueryIn.Proj (T := ℕ) (c := 0)
    (![ProjColIn.term (TermGIn.index 0 rfl)]
      : Tuple (ProjColIn ℕ 0 (ColKind.allReg 2)) 1)
    (AggQueryIn.Rel 2 "S")

theorem count_projWitness (m : ℕ) :
    Multiset.count (fun _ => 0 : Tuple ℕ 1)
      (projWitness.evaluatePlain (dShared m) (fun j => j.elim0)) = m := by
  show Multiset.count (fun _ => 0 : Tuple ℕ 1)
    (Multiset.map (fun u : Tuple ℕ 2 =>
        ((fun j => ((![ProjColIn.term (TermGIn.index 0 rfl)]
          : Tuple (ProjColIn ℕ 0 (ColKind.allReg 2)) 1) j).evalPlain u
            (fun j => j.elim0)) : Tuple ℕ 1))
      (match (dShared m).find 2 "S" with
        | none => (∅ : Multiset (Tuple ℕ 2))
        | some rn => rn)) = m
  rw [find_dShared, Multiset.count_map, Multiset.filter_eq_self.mpr,
    Multiset.card_map, Multiset.card_range]
  intro a ha
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
  refine funext fun j => ?_
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  rfl

/-- **And a projection breaks it**: over an instance of `m` distinct rows
sharing a column, projecting onto that column gives one row `m` times.
So no generating set omits `Π`. -/
theorem projWitness_unbounded_multiplicity :
    ¬ ∃ b : ℕ, ∀ D : Database ℕ, Database.Nodup D → ∀ u : Tuple ℕ 1,
      Multiset.count u (projWitness.evaluatePlain D (fun j => j.elim0))
        ≤ b := by
  rintro ⟨b, h⟩
  have hb := h (dShared (b + 1)) (nodup_dShared _) (fun _ => 0)
  rw [count_projWitness] at hb
  omega

/-! ## Generation: where one operator's plain semantics is another's

The invariants above say which classes no generating set may drop. These
are the other half of the classification: identities under which a basis
holding one operator need not hold another, each an equivalence of plain
semantics (`AggQueryIn.PlainEquiv`) and so blind to annotations – the
annotated readings of the two sides of such an identity are a separate
question, and `evaluate_winByJoin` in `Provenance.WindowPartition` is the
one that has both.

What is here: `ε` from `γ` (`dedup_plainEquiv_gamma`), the difference
from a product with a tag aggregate (`diff_plainEquiv_notIn`), a
selection from two differences (`sel_plainEquiv_selByDiff`), and the
product from an apply whose right side reads no outer column
(`apply_plainEquiv_prod`). Together they leave `{∅, Π, σ, ×, ⊎, γ}`
generating everything but the apply and the window.

Two statements of `sec:basis` are *not* here, and the gap is in the
formalization and not in the paper. **Decorrelation** – every query is
equivalent to one whose applies are products – the paper asserts with an
induction sketch, so what the identities above give is the generation
claim with the apply as a further generator. And the **window** case asks
for an aggregation that reads its group in the clause's order, which this
library's `γ` is not: `Relation.groupSeq` sorts a group in the domain's
canonical order while `ValueFrame.frameListOf` reads a frame in the
clause's (`OrderSpec.sortSeq`). The two agree for a symmetric aggregate
(`ValueFrame.windowValue_of_perm`) and for a clause that separates
nothing, which is the case `WindowPartition.evaluate_winByJoin` proves;
an order-dependent window function – `first_value`, `lag`, `nth_value` –
would need the sorted aggregation the syntax does not have. -/

/-- **`ε` from `γ`**: duplicate elimination is the grouping by every
column with no aggregate. The keys a grouping emits are the distinct rows
of its input, and with no aggregate nothing is appended to them, so `ε`
is in no basis that holds `γ`. -/
theorem AggQueryIn.dedup_plainEquiv_gamma {c n : ℕ}
    (q : AggQueryIn T c n (ColKind.allReg n)) :
    (AggQueryIn.Dedup q).PlainEquiv
      (AggQueryIn.Gamma (fun k : Fin n => k) (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0) q) := by
  intro D γ
  show (q.evaluatePlain D γ).dedup
      = Multiset.map _ (Multiset.dedup (Multiset.map _ (q.evaluatePlain D γ)))
  rw [show (fun u : Tuple T n => (fun k => u ((fun k : Fin n => k) k)
        : Tuple T n)) = id from rfl, Multiset.map_id]
  refine Eq.symm (Eq.trans (Multiset.map_congr rfl (fun g _ => ?_))
    (Multiset.map_id _))
  exact Fin.append_nil g _

/-- **A product is a decorrelated apply**: an apply whose right side
reads no column of the left – a query of the ambient context weakened
into the apply's, which `AggQueryIn.substMap` does – is the product. So
`×` is in no basis that holds the apply, while the converse fails: an
apply's right side reads the left row, and no product does. -/
theorem AggQueryIn.apply_plainEquiv_prod {c n₁ n₂ : ℕ}
    {κ₂ : Fin n₂ → ColKind} (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁))
    (q₂ : AggQueryIn T c n₂ κ₂) :
    (AggQueryIn.Apply q₁
        (q₂.substMap (fun k : Fin c => Sum.inr (Fin.natAdd n₁ k)))).PlainEquiv
      (AggQueryIn.Prod q₁ q₂) := by
  intro D γ
  show Multiset.bind (q₁.evaluatePlain D γ) (fun u =>
      Multiset.map _ ((q₂.substMap _).evaluatePlain D (Fin.append u γ)))
    = q₁.evaluatePlain D γ * q₂.evaluatePlain D γ
  rw [Relation.hMul_eq_bind]
  refine Multiset.bind_congr (fun u _ => ?_)
  rw [AggQueryIn.evaluatePlain_substMap,
    show substVal (fun k : Fin c => (Sum.inr (Fin.natAdd n₁ k) : T ⊕ Fin (n₁ + c)))
        (Fin.append u γ) = γ from funext (fun k => Fin.append_right u γ k)]

/-! ### The difference from a product with a tag aggregate

`prop:collapse` reads the difference as SQL's `NOT IN`: a copy of a tuple
of `q₁` survives when `q₂` holds no copy of it, and every copy survives
or none does. The construction tags each side's rows with a constant –
`0` on the left, `a` on the right – unites them, groups by the whole
tuple, and reads the tags with an aggregate that detects zeros. The
aggregate's value is `0` exactly on the tuples `q₂` does not hold, and a
product with the keys matched keeps the copies of those tuples.

What the construction asks of the aggregate is `hzero` below: it reads
`0` on a list of zeros and nothing else. The document's `sum` has it, and
the count-only variant of the construction – two groupings joined on
their counts, which is what the theorem's proof uses where `sum` is not
among the aggregates – is not formalized here. -/

section Difference

variable {k : ℕ}

/-- The projection that tags a row with a constant: its own columns, and
one more holding `a`. The column constructor is outside the case
analysis, so every output column is regular by reduction. -/
def AggQueryIn.tagCols (a : T) :
    Tuple (ProjCol T (ColKind.allReg k)) (k + 1) :=
  fun j => .term (Fin.lastCases (TermGIn.const a)
    (fun i : Fin k => TermGIn.index i rfl) j)

/-- **The two sides tagged and united**: every row of `q₁` with `0`,
every row of `q₂` with `a`. -/
def AggQueryIn.tagUnion (a : T) (q₁ q₂ : AggQuery T k (ColKind.allReg k)) :
    AggQuery T (k + 1) (ColKind.allReg (k + 1)) :=
  .Sum (.Proj (AggQueryIn.tagCols 0) q₁) (.Proj (AggQueryIn.tagCols a) q₂)

/-- **One row per distinct tuple, carrying the aggregate of the tags.** -/
def AggQueryIn.tagAgg (a : T) (f : SeqAggFunc T)
    (q₁ q₂ : AggQuery T k (ColKind.allReg k)) :
    AggQuery T (k + 1)
      (Fin.append (fun _ : Fin k => ColKind.reg)
        (fun _ : Fin 1 => ColKind.agg)) :=
  .Gamma (fun i : Fin k => i.castSucc) ![TermIn.index (Fin.last k)] ![f]
    (AggQueryIn.tagUnion a q₁ q₂)

/-- The kinds of the product the construction selects on. -/
abbrev notInKinds (k : ℕ) : Fin (k + (k + 1)) → ColKind :=
  Fin.append (ColKind.allReg k)
    (Fin.append (fun _ : Fin k => ColKind.reg) (fun _ : Fin 1 => ColKind.agg))

theorem notInKinds_left (k : ℕ) (i : Fin k) :
    notInKinds k (Fin.castAdd (k + 1) i) = ColKind.reg := by
  rw [notInKinds, Fin.append_left]
  rfl

theorem notInKinds_key (k : ℕ) (i : Fin k) :
    notInKinds k (Fin.natAdd k (Fin.castAdd 1 i)) = ColKind.reg := by
  rw [notInKinds, Fin.append_right, Fin.append_left]

theorem notInKinds_agg (k : ℕ) :
    notInKinds k (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))) = ColKind.agg := by
  rw [notInKinds, Fin.append_right, Fin.append_right]

/-- **What the construction selects on**: the two blocks of key columns
agree, and the tag aggregate is `0`. -/
def AggQueryIn.notInCond : GenPred T (notInKinds k) :=
  .and (keyJoinCond (fun i : Fin k => Fin.castAdd (k + 1) i)
      (fun i : Fin k => Fin.natAdd k (Fin.castAdd 1 i))
      (notInKinds_left k) (notInKinds_key k))
    (.aggCmp (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))) (notInKinds_agg k)
      CompOp.syneq (.const 0))

/-- **The difference read as a `NOT IN`**: the copies of `q₁` whose tuple
the tag aggregate reads `0` on. -/
def AggQueryIn.notInDiff (a : T) (f : SeqAggFunc T)
    (q₁ q₂ : AggQuery T k (ColKind.allReg k)) :
    AggQuery T k (ColKind.allReg k) :=
  .Proj (fun i : Fin k =>
      .term (TermGIn.index (Fin.castAdd (k + 1) i) (notInKinds_left k i)))
    (.Sel AggQueryIn.notInCond (.Prod q₁ (AggQueryIn.tagAgg a f q₁ q₂)))

/-- Tagging a row appends the constant to it. -/
private theorem tagCols_eval (a : T) (u : Tuple T k) (j : Fin (k + 1)) :
    (AggQueryIn.tagCols (T := T) (k := k) a j).evalPlain u (fun _ => 0)
      = (Fin.snoc u a : Tuple T (k + 1)) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    show (ProjColIn.term (Fin.lastCases (TermGIn.const a)
      (fun i : Fin k => TermGIn.index i rfl) (Fin.last k))).evalPlain u _ = a
    rw [Fin.lastCases_last]
    rfl
  · rw [Fin.snoc_castSucc]
    show (ProjColIn.term (Fin.lastCases (TermGIn.const a)
      (fun i : Fin k => TermGIn.index i rfl) (Fin.castSucc i))).evalPlain u _
        = u i
    rw [Fin.lastCases_castSucc]
    rfl

/-- **The tagged union, row by row**: the rows of `q₁` with `0` appended
and those of `q₂` with `a`. -/
theorem AggQueryIn.evaluatePlain_tagUnion (a : T)
    (q₁ q₂ : AggQuery T k (ColKind.allReg k)) (D : Database T) :
    (AggQueryIn.tagUnion a q₁ q₂).evaluatePlain D
      = (q₁.evaluatePlain D).map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
        + (q₂.evaluatePlain D).map
            (fun u => (Fin.snoc u a : Tuple T (k + 1))) := by
  show Multiset.map _ (q₁.evaluatePlain D)
      + Multiset.map _ (q₂.evaluatePlain D) = _
  exact congrArg₂ (· + ·)
    (Multiset.map_congr rfl (fun u _ => funext (fun j => tagCols_eval 0 u j)))
    (Multiset.map_congr rfl (fun u _ => funext (fun j => tagCols_eval a u j)))

/-- **The keys the grouping emits**: the distinct tuples of the two sides
together, the tag column being dropped by the key projection. -/
theorem AggQueryIn.tagAgg_keys (a : T)
    (r₁ r₂ : Multiset (Tuple T k)) :
    ((r₁.map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
        + r₂.map (fun u => (Fin.snoc u a : Tuple T (k + 1)))).map
      (fun v => (fun i => v (Fin.castSucc i) : Tuple T k))).dedup
      = (r₁ + r₂).dedup := by
  refine congrArg Multiset.dedup ?_
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Eq.trans (Multiset.map_congr rfl (fun u _ => funext (fun i => by
      show (Fin.snoc u 0 : Tuple T (k + 1)) (Fin.castSucc i) = u i
      rw [Fin.snoc_castSucc]))) (Multiset.map_id' r₁)
  · exact Eq.trans (Multiset.map_congr rfl (fun u _ => funext (fun i => by
      show (Fin.snoc u a : Tuple T (k + 1)) (Fin.castSucc i) = u i
      rw [Fin.snoc_castSucc]))) (Multiset.map_id' r₂)

/-- **What the tag aggregate reads on a tuple**: `0` exactly when the
right side holds no copy of it. A copy from the left carries the tag `0`
and one from the right carries `a`, so a zero-detecting aggregate reads
`0` iff the group holds no copy from the right. -/
theorem AggQueryIn.tagAgg_zero_iff (a : T) (ha : a ≠ 0) (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0)
    (r₁ r₂ : Multiset (Tuple T k)) (g : Tuple T k) :
    f ((Relation.groupSeq (fun i : Fin k => i.castSucc)
        (r₁.map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
          + r₂.map (fun u => (Fin.snoc u a : Tuple T (k + 1)))) g).map
        (fun v => v (Fin.last k))) = 0
      ↔ g ∉ r₂ := by
  rw [hzero]
  constructor
  · intro h hg
    refine ha (h a (List.mem_map.mpr ⟨Fin.snoc g a, ?_, ?_⟩))
    · rw [Relation.groupSeq, mem_sortList, Multiset.mem_filter]
      refine ⟨Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ hg)),
        fun i => ?_⟩
      show (Fin.snoc g a : Tuple T (k + 1)) (Fin.castSucc i) = g i
      rw [Fin.snoc_castSucc]
    · show (Fin.snoc g a : Tuple T (k + 1)) (Fin.last k) = a
      rw [Fin.snoc_last]
  · intro hg x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    rw [Relation.groupSeq, mem_sortList, Multiset.mem_filter] at hv
    obtain ⟨hmem, hkey⟩ := hv
    rcases Multiset.mem_add.mp hmem with h1 | h2
    · obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp h1
      show (Fin.snoc u 0 : Tuple T (k + 1)) (Fin.last k) = 0
      rw [Fin.snoc_last]
    · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp h2
      refine absurd ?_ hg
      have hug : u = g := funext (fun i => by
        have hi : (Fin.snoc u a : Tuple T (k + 1)) (Fin.castSucc i) = g i :=
          hkey i
        rwa [Fin.snoc_castSucc] at hi)
      exact hug ▸ hu

/-- Binding a one-or-no-row choice is filtering. -/
private theorem bind_ite_singleton {α : Type} (s : Multiset α)
    (p : α → Prop) [DecidablePred p] :
    (s.bind (fun a => if p a then ({a} : Multiset α) else 0))
      = s.filter p := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih => rw [Multiset.cons_bind, ih, Multiset.filter_cons]

/-- **What the product with the tag aggregate keeps**: one copy of each
copy of `r₁` whose tuple the aggregate reads `0` on. The keys are
distinct and hold every tuple of `r₁`, so each copy of `r₁` meets
exactly one row of the grouping. The tuple types are spelled unfolded
here, which is what lets the rewrites through the key condition match. -/
private theorem notIn_filter_map (r₁ : Multiset (Fin k → T))
    (keys : Multiset (Fin k → T)) (val : (Fin k → T) → T)
    (hnodup : keys.Nodup) (hmem : ∀ u ∈ r₁, u ∈ keys) :
    (Multiset.filter (fun w : Fin (k + (k + 1)) → T =>
          (∀ i : Fin k, w (Fin.castAdd (k + 1) i)
              = w (Fin.natAdd k (Fin.castAdd 1 i)))
            ∧ w (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))) = 0)
        (r₁.bind (fun u => (keys.map (fun g =>
            (Fin.append g (fun _ : Fin 1 => val g) : Fin (k + 1) → T))).map
          (fun v => (Fin.append u v : Fin (k + (k + 1)) → T))))).map
        (fun w => (fun i => w (Fin.castAdd (k + 1) i) : Fin k → T))
      = Multiset.filter (fun u => val u = 0) r₁ := by
  rw [Multiset.filter_bind, Multiset.map_bind,
    ← bind_ite_singleton r₁ (fun u => val u = 0)]
  refine Multiset.bind_congr (fun u hu => ?_)
  simp only [Multiset.filter_map, Multiset.map_map, Function.comp_def]
  -- the pair's condition keeps `u` itself, and only where the aggregate
  -- reads zero on it
  have hiff : ∀ g : Fin k → T,
      ((∀ i : Fin k, (Fin.append u (Fin.append g
            (fun _ : Fin 1 => val g)) : Fin (k + (k + 1)) → T)
              (Fin.castAdd (k + 1) i)
          = (Fin.append u (Fin.append g (fun _ : Fin 1 => val g))
              : Fin (k + (k + 1)) → T) (Fin.natAdd k (Fin.castAdd 1 i)))
        ∧ (Fin.append u (Fin.append g (fun _ : Fin 1 => val g))
            : Fin (k + (k + 1)) → T)
              (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))) = 0)
      ↔ (g = u ∧ val u = 0) := by
    intro g
    constructor
    · rintro ⟨hk, hz⟩
      have hgu : g = u := funext (fun i => by
        have hi := hk i
        rw [Fin.append_left, Fin.append_right, Fin.append_left] at hi
        exact hi.symm)
      refine ⟨hgu, ?_⟩
      rw [Fin.append_right, Fin.append_right] at hz
      rw [← hgu]
      exact hz
    · rintro ⟨rfl, hz⟩
      refine ⟨fun i => ?_, ?_⟩
      · rw [Fin.append_left, Fin.append_right, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        exact hz
  rw [Multiset.filter_congr (q := fun g : Fin k → T => g = u ∧ val u = 0)
    (fun g _ => hiff g)]
  by_cases hz : val u = 0
  · rw [Multiset.filter_congr (q := fun g : Fin k → T => g = u)
      (fun g _ => and_iff_left hz), Multiset.filter_eq',
      Multiset.count_eq_one_of_mem hnodup (hmem u hu), Multiset.replicate_one,
      Multiset.map_singleton, ite_eq_left hz]
    refine congrArg (fun x => ({x} : Multiset (Fin k → T)))
      (funext (fun i => ?_))
    rw [Fin.append_left]
  · rw [Multiset.filter_eq_nil.mpr (fun g _ h => hz h.2), Multiset.map_zero,
      ite_eq_right hz]

/-- **`−` from `σ`, `×`, `⊎`, `Π` and `γ`** (`prop:collapse`): the
difference is SQL's `NOT IN`. Every copy of a tuple of `q₁` survives when
`q₂` holds no copy of it and none survives otherwise, which is what the
tag aggregate decides: it reads `0` exactly on the tuples `q₂` does not
hold, and the product keeps the copies of those.

The aggregate is a parameter, as it is in the paper: what the
construction asks of it is `hzero`, that it read `0` on a list of zeros
and on no other. The document's `sum` has it. Where the aggregates do not
include a sum, the document's proof joins two counting groupings on their
counts instead; that variant is not formalized here. -/
theorem AggQueryIn.diff_plainEquiv_notIn (a : T) (ha : a ≠ 0)
    (f : SeqAggFunc T) (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0)
    (q₁ q₂ : AggQuery T k (ColKind.allReg k)) :
    (AggQueryIn.Diff q₁ q₂).PlainEquiv (AggQueryIn.notInDiff a f q₁ q₂) := by
  intro D γ
  have hγ : γ = (fun j : Fin 0 => (0 : T)) := funext (fun j => j.elim0)
  subst hγ
  -- the two sides' rows, as multisets, which is what `−` reads
  set r₁ : Multiset (Tuple T k) := q₁.evaluatePlain D with hr₁
  set r₂ : Multiset (Tuple T k) := q₂.evaluatePlain D with hr₂
  -- the tagged union: the rows of `q₁` with `0` and those of `q₂` with `a`
  set tagged : Multiset (Fin (k + 1) → T) :=
    r₁.map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
      + r₂.map (fun u => (Fin.snoc u a : Tuple T (k + 1))) with htagged
  -- the tag of a tuple: the aggregate over the tags of its copies
  set val : (Fin k → T) → T := fun g =>
    f ((Relation.groupSeq (fun i : Fin k => i.castSucc) tagged g).map
      (fun v => v (Fin.last k))) with hval
  -- the grouping's rows: one per distinct tuple, carrying its tag
  have hDr : (AggQueryIn.tagAgg a f q₁ q₂).evaluatePlain D
      = ((r₁ + r₂).dedup).map (fun g =>
          (Fin.append g (fun _ : Fin 1 => val g) : Fin (k + 1) → T)) := by
    show Multiset.map _ (Multiset.dedup (Multiset.map _
        ((AggQueryIn.tagUnion a q₁ q₂).evaluatePlain D))) = _
    rw [AggQueryIn.evaluatePlain_tagUnion]
    refine congrArg₂ Multiset.map (funext (fun g => ?_))
      (AggQueryIn.tagAgg_keys a _ _)
    refine congrArg (Fin.append g) (funext (fun j => ?_))
    rw [Subsingleton.elim j 0]
    rfl
  -- the selection's condition, read on a row of the product
  have hcond : ∀ w : Tuple T (k + (k + 1)),
      (AggQueryIn.notInCond (T := T) (k := k)).holdsPlain w
        ↔ ((∀ i : Fin k, w (Fin.castAdd (k + 1) i)
              = w (Fin.natAdd k (Fin.castAdd 1 i)))
            ∧ w (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))) = 0) := by
    intro w
    rw [AggQueryIn.notInCond, GenPredIn.holdsPlain_and, keyJoinCond_holdsPlain]
    refine and_congr Iff.rfl ?_
    show CompOp.syneq.eval3 (w (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))))
        ((TermGIn.const (0 : T)).evalPlain w (fun _ => 0)) = Kleene.true ↔ _
    rw [CompOp.syneq_eval3_eq_true_iff]
    exact Iff.rfl
  show Multiset.filter (fun t => t ∉ r₂) r₁ = _
  show _ = Multiset.map _ (Multiset.filter
      (fun w => (AggQueryIn.notInCond (T := T) (k := k)).holdsPlain w)
      (q₁.evaluatePlain D * (AggQueryIn.tagAgg a f q₁ q₂).evaluatePlain D))
  rw [hDr, Multiset.filter_congr (fun w _ => hcond w), Relation.hMul_eq_bind]
  refine Eq.symm (Eq.trans (notIn_filter_map r₁ ((r₁ + r₂).dedup) val
    (Multiset.nodup_dedup _)
    (fun u hu => Multiset.mem_dedup.mpr (Multiset.mem_add.mpr (Or.inl hu)))) ?_)
  refine Multiset.filter_congr (fun u _ => ?_)
  rw [hval]
  exact AggQueryIn.tagAgg_zero_iff a ha f hzero _ _ u

/-! ### A selection from the difference

The other direction of the swap, which `sec:basis` states right after
`prop:collapse`: where the comparisons are among the terms, a selection
is a difference. Tag every row with the truth value of the predicate as a
*value* – which is what a `CASE` expression over the comparisons gives –
and tag every row with the constant that reads *true*. A row of the first
is missing from the second exactly where the predicate fails, so removing
that difference from the first leaves the rows the selection keeps.

The term is a parameter of the general statement, with `hterm` saying
that it reads `yes` on the rows the predicate keeps and nothing else;
`GenPredIn.polTerm` builds it from the predicate – which is what "Ω
contains the comparisons" asks for – and
`sel_plainEquiv_selByDiff_polTerm` is the identity with no hypothesis on
the term left. An aggregate atom is excluded: its value is a provenance
and not a truth value. -/

section SelFromDiff

variable {k : ℕ}

/-- The projection that tags a row with the value of a term. -/
def AggQueryIn.tagTermCols (t : TermGIn T 0 (ColKind.allReg k)) :
    Tuple (ProjCol T (ColKind.allReg k)) (k + 1) :=
  fun j => .term (Fin.lastCases t (fun i : Fin k => TermGIn.index i rfl) j)

/-- The projection that drops a tag column. -/
def AggQueryIn.dropTag : Tuple (ProjCol T (ColKind.allReg (k + 1))) k :=
  fun i => .term (TermGIn.index i.castSucc rfl)

/-- **A selection written with a difference**: the rows tagged `yes`,
read as what is left of the tagged rows after removing those that the
constant tagging does not hold. -/
def AggQueryIn.selByDiff (yes : T) (t : TermGIn T 0 (ColKind.allReg k))
    (q : AggQuery T k (ColKind.allReg k)) : AggQuery T k (ColKind.allReg k) :=
  .Proj AggQueryIn.dropTag
    (.Diff (.Proj (AggQueryIn.tagTermCols t) q)
      (.Diff (.Proj (AggQueryIn.tagTermCols t) q)
        (.Proj (AggQueryIn.tagTermCols (TermGIn.const yes)) q)))

/-- Tagging a row with a term appends the term's value to it. -/
private theorem tagTermCols_eval (t : TermGIn T 0 (ColKind.allReg k))
    (u : Tuple T k) (j : Fin (k + 1)) :
    (AggQueryIn.tagTermCols t j).evalPlain u (fun _ => 0)
      = (Fin.snoc u (t.evalPlain u (fun _ => 0)) : Tuple T (k + 1)) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    show (ProjColIn.term (Fin.lastCases t
      (fun i : Fin k => TermGIn.index i rfl) (Fin.last k))).evalPlain u _
        = t.evalPlain u (fun _ => 0)
    rw [Fin.lastCases_last]
    rfl
  · rw [Fin.snoc_castSucc]
    show (ProjColIn.term (Fin.lastCases t
      (fun i : Fin k => TermGIn.index i rfl) (Fin.castSucc i))).evalPlain u _
        = u i
    rw [Fin.lastCases_castSucc]
    rfl

/-- The row map a tagging projection computes. -/
private theorem tagTermCols_fun (t : TermGIn T 0 (ColKind.allReg k)) :
    (fun (u : Tuple T k) (j : Fin (k + 1)) =>
        (AggQueryIn.tagTermCols t j).evalPlain u (fun _ => 0))
      = fun u => (Fin.snoc u (t.evalPlain u (fun _ => 0))
          : Tuple T (k + 1)) :=
  funext (fun u => funext (fun j => tagTermCols_eval t u j))

/-- A constant term reads its constant. -/
private theorem evalPlain_const (a : T) (u : Tuple T k) :
    (TermGIn.const (c := 0) (κ := ColKind.allReg k) a).evalPlain u
        (fun _ => 0) = a := rfl

/-- The row map that drops a tag column. -/
private theorem dropTag_fun :
    (fun (w : Tuple T (k + 1)) (i : Fin k) =>
        (AggQueryIn.dropTag (T := T) (k := k) i).evalPlain w (fun _ => 0))
      = fun w => (fun i => w (Fin.castSucc i) : Tuple T k) := rfl

/-- **The predicate read as a term**: a `CASE` expression over the same
comparisons, reading `yes` exactly where the predicate is true
(`pol = true`) or exactly where it is *false* (`pol = false`), and `0`
elsewhere.

Both polarities are needed because the logic is Kleene's: a negation
holds where its argument is false, which is not where its argument fails
to hold, so a term reading only truth cannot carry a negation. Reading
the two together, a negation is a change of polarity, and the
comparisons change with it (`CompOp.negate`). -/
def GenPredIn.polTerm {c n : ℕ} {κ : Fin n → ColKind} (yes : T) (pol : Bool) :
    GenPredIn T c κ → TermGIn T c κ
  | .cmp op t₁ t₂ =>
      .caseWhen (match pol with | true => op | false => op.negate) t₁ t₂
        (.const yes) (.const 0)
  | .aggCmp _ _ _ _ => .const 0
  | .aggRange _ _ _ _ _ _ => .const 0
  | .and φ ψ =>
      match pol with
      | true => .caseWhen CompOp.syneq (φ.polTerm yes true) (.const yes)
          (ψ.polTerm yes true) (.const 0)
      | false => .caseWhen CompOp.syneq (φ.polTerm yes false) (.const yes)
          (.const yes) (ψ.polTerm yes false)
  | .or φ ψ =>
      match pol with
      | true => .caseWhen CompOp.syneq (φ.polTerm yes true) (.const yes)
          (.const yes) (ψ.polTerm yes true)
      | false => .caseWhen CompOp.syneq (φ.polTerm yes false) (.const yes)
          (ψ.polTerm yes false) (.const 0)
  | .not φ => φ.polTerm yes (!pol)

/-- A guard comparing such a term against `yes` tests the condition the
term reads: the two values it takes are told apart by `≐`, which is never
unknown. -/
private theorem syneq_guard {yes : T} (hyes : yes ≠ 0) {P : Prop}
    [Decidable P] (x y : T) :
    (if CompOp.syneq.eval3 (if P then yes else (0 : T)) yes = Kleene.true
      then x else y) = if P then x else y := by
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left h]
    exact ite_eq_left ((CompOp.syneq_eval3_eq_true_iff yes yes).mpr rfl)
  · rw [ite_eq_right h, ite_eq_right h]
    refine ite_eq_right (fun hc => hyes ?_)
    exact ((CompOp.syneq_eval3_eq_true_iff (0 : T) yes).mp hc).symm

/-- **What the term reads**: `yes` exactly on the rows where the
predicate takes the truth value the polarity asks for, and `0` on the
others. An aggregate atom is excluded – its value is a provenance and not
a truth value, which is what `hasAggAtom` fences off. -/
theorem GenPredIn.evalPlain_polTerm {c n : ℕ} {κ : Fin n → ColKind}
    {yes : T} (hyes : yes ≠ 0) :
    ∀ (φ : GenPredIn T c κ), φ.hasAggAtom = false → ∀ (pol : Bool)
      (u : Tuple T n) (γ : Fin c → T),
      (φ.polTerm yes pol).evalPlain u γ
        = if φ.evalPlain3 u γ = Kleene.ofBool pol then yes else 0 := by
  intro φ
  induction φ with
  | cmp op t₁ t₂ =>
    intro _ pol u γ
    cases pol with
    | true => rfl
    | false =>
      show (if op.negate.eval3 (t₁.evalPlain u γ) (t₂.evalPlain u γ)
          = Kleene.true then yes else (0 : T)) = _
      rw [CompOp.negate_eval3]
      cases h : op.eval3 (t₁.evalPlain u γ) (t₂.evalPlain u γ) <;>
        simp [GenPredIn.evalPlain3, Kleene.not, Kleene.ofBool, h]
  | aggCmp k hk op t => exact fun hag => Bool.noConfusion hag
  | aggRange k hk op₁ t₁ op₂ t₂ => exact fun hag => Bool.noConfusion hag
  | and φ ψ ihφ ihψ =>
    intro hag pol u γ
    obtain ⟨h₁, h₂⟩ := Bool.or_eq_false_iff.mp hag
    cases pol with
    | true =>
      show (if CompOp.syneq.eval3 ((φ.polTerm yes true).evalPlain u γ) yes
          = Kleene.true then (ψ.polTerm yes true).evalPlain u γ
          else (0 : T)) = _
      rw [ihφ h₁ true u γ, syneq_guard hyes, ihψ h₂ true u γ]
      cases hφ : φ.evalPlain3 u γ <;> cases hψ : ψ.evalPlain3 u γ <;>
        simp [GenPredIn.evalPlain3, Kleene.and, Kleene.ofBool, hφ, hψ]
    | false =>
      show (if CompOp.syneq.eval3 ((φ.polTerm yes false).evalPlain u γ) yes
          = Kleene.true then yes
          else (ψ.polTerm yes false).evalPlain u γ) = _
      rw [ihφ h₁ false u γ, syneq_guard hyes, ihψ h₂ false u γ]
      cases hφ : φ.evalPlain3 u γ <;> cases hψ : ψ.evalPlain3 u γ <;>
        simp [GenPredIn.evalPlain3, Kleene.and, Kleene.ofBool, hφ, hψ]
  | or φ ψ ihφ ihψ =>
    intro hag pol u γ
    obtain ⟨h₁, h₂⟩ := Bool.or_eq_false_iff.mp hag
    cases pol with
    | true =>
      show (if CompOp.syneq.eval3 ((φ.polTerm yes true).evalPlain u γ) yes
          = Kleene.true then yes
          else (ψ.polTerm yes true).evalPlain u γ) = _
      rw [ihφ h₁ true u γ, syneq_guard hyes, ihψ h₂ true u γ]
      cases hφ : φ.evalPlain3 u γ <;> cases hψ : ψ.evalPlain3 u γ <;>
        simp [GenPredIn.evalPlain3, Kleene.or, Kleene.ofBool, hφ, hψ]
    | false =>
      show (if CompOp.syneq.eval3 ((φ.polTerm yes false).evalPlain u γ) yes
          = Kleene.true then (ψ.polTerm yes false).evalPlain u γ
          else (0 : T)) = _
      rw [ihφ h₁ false u γ, syneq_guard hyes, ihψ h₂ false u γ]
      cases hφ : φ.evalPlain3 u γ <;> cases hψ : ψ.evalPlain3 u γ <;>
        simp [GenPredIn.evalPlain3, Kleene.or, Kleene.ofBool, hφ, hψ]
  | not φ ih =>
    intro hag pol u γ
    show (φ.polTerm yes (!pol)).evalPlain u γ = _
    rw [ih hag (!pol) u γ]
    cases pol <;> cases hφ : φ.evalPlain3 u γ <;>
      simp [GenPredIn.evalPlain3, Kleene.not, Kleene.ofBool, hφ]

/-- **`σ` from `−`** (the swap of `sec:basis`): a selection whose
predicate is read by a term is the difference of the tagged rows with
what the constant tagging leaves out. -/
theorem AggQueryIn.sel_plainEquiv_selByDiff (yes : T)
    (t : TermGIn T 0 (ColKind.allReg k)) (φ : GenPred T (ColKind.allReg k))
    (hterm : ∀ u : Tuple T k,
      t.evalPlain u (fun _ => 0) = yes ↔ φ.holdsPlain u)
    (q : AggQuery T k (ColKind.allReg k)) :
    (AggQueryIn.Sel φ q).PlainEquiv (AggQueryIn.selByDiff yes t q) := by
  intro D γ
  have hγ : γ = (fun j : Fin 0 => (0 : T)) := funext (fun j => j.elim0)
  subst hγ
  simp only [AggQueryIn.selByDiff, AggQueryIn.evaluatePlain, tagTermCols_fun,
    dropTag_fun, evalPlain_const]
  set r : Multiset (Tuple T k) := q.evaluatePlain D with hr
  set tag : Tuple T k → T := fun u => t.evalPlain u (fun _ => 0) with htag
  set tagged : Multiset (Tuple T (k + 1)) :=
    r.map (fun u => (Fin.snoc u (tag u) : Tuple T (k + 1))) with htagged
  set allYes : Multiset (Tuple T (k + 1)) :=
    r.map (fun u => (Fin.snoc u yes : Tuple T (k + 1))) with hallYes
  -- a tagged row is one of the constant-tagged ones exactly when its tag
  -- reads `yes`
  have hmemYes : ∀ u ∈ r,
      ((Fin.snoc u (tag u) : Tuple T (k + 1)) ∈ allYes ↔ tag u = yes) := by
    intro u hu
    constructor
    · intro hmem
      obtain ⟨v, -, hv⟩ := Multiset.mem_map.mp hmem
      have hlast := congrFun hv (Fin.last k)
      simp only [Fin.snoc_last] at hlast
      exact hlast.symm
    · intro hy
      rw [hy]
      exact Multiset.mem_map_of_mem _ hu
  -- the inner difference: the tagged rows whose tag does not read `yes`
  have hinner : Multiset.filter (fun w => w ∉ allYes) tagged
      = (Multiset.filter (fun u => ¬ tag u = yes) r).map
          (fun u => (Fin.snoc u (tag u) : Tuple T (k + 1))) := by
    rw [htagged, Multiset.filter_map]
    exact congrArg _ (Multiset.filter_congr (fun u hu =>
      not_congr (hmemYes u hu)))
  -- and the outer one keeps exactly the rows whose tag reads `yes`
  have houter : Multiset.filter (fun w => w ∉
        (Multiset.filter (fun u => ¬ tag u = yes) r).map
          (fun u => (Fin.snoc u (tag u) : Tuple T (k + 1)))) tagged
      = (Multiset.filter (fun u => tag u = yes) r).map
          (fun u => (Fin.snoc u (tag u) : Tuple T (k + 1))) := by
    rw [htagged, Multiset.filter_map]
    refine congrArg _ (Multiset.filter_congr (fun u hu => ?_))
    constructor
    · intro hnot
      by_contra hy
      exact hnot (Multiset.mem_map_of_mem _ (Multiset.mem_filter.mpr ⟨hu, hy⟩))
    · intro hy hmem
      obtain ⟨v, hv, hveq⟩ := Multiset.mem_map.mp hmem
      have hlast := congrFun hveq (Fin.last k)
      simp only [Fin.snoc_last] at hlast
      exact (Multiset.mem_filter.mp hv).2 (hlast.trans hy)
  -- the two differences, composed, keep the tagged rows the predicate keeps
  refine Eq.trans ?_ (congrArg
    (Multiset.map (fun (w : Tuple T (k + 1)) (i : Fin k) => w (Fin.castSucc i)))
    (Eq.trans (congrArg (fun M => Multiset.filter (fun x => x ∉ M) tagged)
      hinner) houter)).symm
  rw [Multiset.map_map]
  refine Eq.trans (Multiset.filter_congr (fun u _ => (hterm u).symm))
    (Eq.symm (Eq.trans (Multiset.map_congr rfl (fun u _ => ?_))
      (Multiset.map_id _)))
  show (fun i => (Fin.snoc u (tag u) : Tuple T (k + 1)) (Fin.castSucc i)) = u
  exact funext (fun i => by rw [Fin.snoc_castSucc])

/-- **`σ` from `−`, with the term built from the predicate.** Where the
predicate's atoms are comparisons, the `CASE` expression over them reads
`yes` exactly on the rows it keeps, so the selection is a difference and
nothing is asked of `Ω` beyond the comparisons it already has. -/
theorem AggQueryIn.sel_plainEquiv_selByDiff_polTerm (yes : T) (hyes : yes ≠ 0)
    (φ : GenPred T (ColKind.allReg k)) (hφ : φ.hasAggAtom = false)
    (q : AggQuery T k (ColKind.allReg k)) :
    (AggQueryIn.Sel φ q).PlainEquiv
      (AggQueryIn.selByDiff yes (φ.polTerm yes true) q) := by
  refine AggQueryIn.sel_plainEquiv_selByDiff yes _ φ (fun u => ?_) q
  rw [GenPredIn.evalPlain_polTerm hyes φ hφ true u (fun _ => 0)]
  by_cases h : φ.holdsPlain u
  · rw [ite_eq_left (show φ.evalPlain3 u (fun _ => 0) = Kleene.ofBool true
      from h)]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right (show ¬ (φ.evalPlain3 u (fun _ => 0)
      = Kleene.ofBool true) from h)]
    exact ⟨fun h0 => absurd h0.symm hyes, fun hc => absurd hc h⟩

end SelFromDiff

end Difference





/-! ### A window from an apply

`prop:winderived`: a window whose frame contains its current row exactly
when it contains its peers is an apply – the query with, for each of its
rows, a scalar aggregation over the rows that row's frame holds. The
frame condition is read as a selection comparing the row's keys against
the *current* row's, which the apply supplies as outer columns, and the
aggregation reads its group in the window's own order, which is what the
grouping's `ORDER BY` is for.

Two things are parameters. The frame condition `ρ` is an arbitrary
relation on order values in the library's encoding, so the predicate
reading it is given, with `hρ` saying that it reads it: in SQL it is a
frame clause, and there the predicate *is* the clause. And the frame is
asked to contain its current row (`ValueFrame.ContainsSelf`): `EXCLUDE
CURRENT ROW` and `EXCLUDE TIES` have no such reading, the group a scalar
aggregation reads being determined by the rows and not by the
occurrence. -/

section WinDerived

variable {n m p : ℕ}

/-- **The empty context, as a substitution**: it weakens a closed query
or a closed term into one that reads outer columns and ignores them. -/
def weakenOuter (T : Type) (d : ℕ) : Fin 0 → T ⊕ Fin d := fun k => k.elim0

/-- A closed reading is the reading under any valuation, there being no
outer column to read. -/
@[simp] theorem substVal_weakenOuter (d : ℕ) (γ : Fin d → T) :
    substVal (weakenOuter T d) γ = (fun _ : Fin 0 => (0 : T)) :=
  funext (fun k => k.elim0)

/-- A conjunction holds where both sides do, in any context. -/
private theorem holdsPlain_and_iff {c n' : ℕ} {κ : Fin n' → ColKind}
    (φ ψ : GenPredIn T c κ) (u : Tuple T n') (γ : Fin c → T) :
    (GenPredIn.and φ ψ).holdsPlain u γ
      ↔ (φ.holdsPlain u γ ∧ ψ.holdsPlain u γ) :=
  Kleene.and_eq_true_iff _ _

/-- A conjunction over a list holds where every conjunct does, in any
context. -/
private theorem holdsPlain_foldr_and' {c n' : ℕ} {κ : Fin n' → ColKind}
    {α : Type} (f : α → GenPredIn T c κ) (base : GenPredIn T c κ)
    (u : Tuple T n') (γ : Fin c → T) : ∀ l : List α,
    (((l.map f).foldr GenPredIn.and base).holdsPlain u γ)
      ↔ (∀ x ∈ l, (f x).holdsPlain u γ) ∧ base.holdsPlain u γ := by
  intro l
  induction l with
  | nil => exact ⟨fun h => ⟨fun x hx => absurd hx (List.not_mem_nil), h⟩,
      fun h => h.2⟩
  | cons hd tl ih =>
    rw [List.map_cons, List.foldr_cons, holdsPlain_and_iff, ih]
    constructor
    · rintro ⟨hhd, hall, hb⟩
      refine ⟨fun x hx => ?_, hb⟩
      rcases List.mem_cons.mp hx with rfl | ht
      · exact hhd
      · exact hall x ht
    · rintro ⟨hall, hb⟩
      exact ⟨hall hd List.mem_cons_self, fun x hx =>
        hall x (List.mem_cons_of_mem hd hx), hb⟩

/-- **The key comparison against the outer columns**: the row's columns
`cols` are compared with the row the apply is reading, which it supplies
at the outer positions `outs`. As in a join the comparison is `IS NOT
DISTINCT FROM`, the syntactic equality a window partitions by. -/
def outerKeyCond {c n' m' : ℕ} {κ : Fin n' → ColKind}
    (cols : Tuple (Fin n') m') (h : ∀ k, κ (cols k) = ColKind.reg)
    (outs : Tuple (Fin c) m') : GenPredIn T c κ :=
  ((List.finRange m').map (fun k =>
    GenPredIn.cmp CompOp.syneq (TermGIn.index (cols k) (h k))
      (TermGIn.outer (outs k)))).foldr GenPredIn.and
    (GenPredIn.cmp CompOp.syneq (TermGIn.const 0) (TermGIn.const 0))

/-- It holds exactly where the two keys agree. -/
theorem outerKeyCond_holdsPlain {c n' m' : ℕ} {κ : Fin n' → ColKind}
    (cols : Tuple (Fin n') m') (h : ∀ k, κ (cols k) = ColKind.reg)
    (outs : Tuple (Fin c) m') (u : Tuple T n') (γ : Fin c → T) :
    (outerKeyCond cols h outs).holdsPlain u γ
      ↔ ∀ k, u (cols k) = γ (outs k) := by
  have hatom : ∀ k, (GenPredIn.cmp (c := c) (κ := κ) CompOp.syneq
      (TermGIn.index (cols k) (h k)) (TermGIn.outer (outs k))).holdsPlain u γ
        ↔ u (cols k) = γ (outs k) := by
    intro k
    show CompOp.syneq.eval3 (u (cols k)) (γ (outs k)) = Kleene.true ↔ _
    rw [CompOp.syneq_eval3_eq_true_iff]
  unfold outerKeyCond
  rw [holdsPlain_foldr_and']
  constructor
  · rintro ⟨hall, -⟩ k
    exact (hatom k).mp (hall k (List.mem_finRange k))
  · intro hk
    refine ⟨fun k _ => (hatom k).mpr (hk k), ?_⟩
    show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true
    rw [CompOp.syneq_eval3_eq_true_iff]

/-- A group with no key columns is the whole relation, sorted. -/
@[simp] theorem Relation.groupSeq_emptyKey {m : ℕ}
    (r : Multiset (Tuple T m)) :
    Relation.groupSeq (fun k : Fin 0 => k.elim0) r
        (fun k : Fin 0 => k.elim0) = sortList r := by
  unfold Relation.groupSeq
  rw [Multiset.filter_eq_self.mpr (fun u _ => fun k => k.elim0)]

/-- A scalar aggregation with one aggregate has one row, holding it. -/
private theorem gammaScalar_one {c m' : ℕ} (t' : TermIn T c m')
    (f : SeqAggFunc T) (q' : AggQueryIn T c m' (ColKind.allReg m'))
    (ord : GroupOrder T m') (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.GammaScalar ![t'] ![f] q' ord).evaluatePlain D γ
      = ({fun _ : Fin 1 => f ((Relation.groupSeqOrd
          (fun k : Fin 0 => k.elim0) ord (q'.evaluatePlain D γ)
          (fun k : Fin 0 => k.elim0)).map (fun v => t'.eval v γ))}
        : Multiset (Tuple T 1)) := by
  show (Multiset.ofList [(fun j => (![f] j)
      ((Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) ord
        (q'.evaluatePlain D γ) (fun k : Fin 0 => k.elim0)).map
          (fun v => (![t'] j).eval v γ)) : Tuple T 1)]
      : Multiset (Tuple T 1)) = _
  refine congrArg (fun x : Tuple T 1 => ({x} : Multiset (Tuple T 1))) ?_
  funext j
  obtain rfl : j = 0 := Fin.eq_zero j
  rfl

omit [ValueType T] in
/-- The apply's columns are the query's and the aggregate, as a window's
are. -/
theorem winApplyKinds (n : ℕ) :
    Fin.append (ColKind.allReg n) (fun _ : Fin 1 => ColKind.agg)
      = Fin.snoc (ColKind.allReg n) ColKind.agg := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last,
      show (Fin.last n) = Fin.natAdd n (0 : Fin 1) from rfl, Fin.append_right]
  · rw [Fin.snoc_castSucc,
      show (Fin.castSucc i) = Fin.castAdd 1 i from rfl, Fin.append_left]

/-- **A window written with an apply and a scalar aggregation**: for each
row of the query, the term aggregated over the rows that row's frame
holds, read in the window's own order. -/
def winByApply (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ψ : GenPredIn T n (ColKind.allReg n)) (t : Term T n) (f : SeqAggFunc T)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  AggQueryIn.castKind (winApplyKinds n)
    (AggQueryIn.Apply q
      (AggQueryIn.GammaScalar ![t.substMap (weakenOuter T n)] ![f]
        (AggQueryIn.Sel (GenPredIn.and (outerKeyCond P (fun _ => rfl) P) ψ)
          (q.substMap (weakenOuter T n)))
        (GroupOrder.byCols O o)))

/-- **A window is an apply of a scalar aggregation** (`prop:winderived`),
over plain relations: the rows the selection keeps are the current row's
frame, the clause reads them in the order the window reads them, and the
aggregate is then the window's value. -/
theorem evaluatePlain_winByApply (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) {w : ValueFrame T p} (hc : w.ContainsSelf)
    (ψ : GenPredIn T n (ColKind.allReg n))
    (hρ : ∀ y u : Tuple T n, ψ.holdsPlain y u
      ↔ w.ρ (Tuple.key O y) (Tuple.key O u) = true)
    (t : Term T n) (f : SeqAggFunc T) (q : AggQuery T n (ColKind.allReg n))
    (D : Database T) :
    (winByApply P O o ψ t f q).evaluatePlain D
      = (AggQueryIn.Win P O o w t f q
          (winReadsReg_allReg P O t)).evaluatePlain D := by
  classical
  rw [winByApply, AggQueryIn.evaluatePlain_castKind,
    AggQueryIn.evaluatePlain_Apply, AggQueryIn.evaluatePlain_Win_eq]
  simp only [ColKind.readTuple_allReg, Multiset.map_id', Bool.false_eq_true,
    ite_false]
  refine Eq.trans (Multiset.bind_congr (fun u hu => ?_))
    (Multiset.bind_singleton (s := q.evaluatePlain D) (fun u =>
      (Fin.snoc u (ValueFrame.windowValue P O o w t f (q.evaluatePlain D) u)
        : Tuple T (n + 1))))
  -- the rows the selection keeps are the row's own frame
  have hframe : (AggQueryIn.Sel
        (GenPredIn.and (outerKeyCond P (fun _ => rfl) P) ψ)
        (q.substMap (weakenOuter T n))).evaluatePlain D u
      = ValueFrame.frameOf (α := Tuple T n) id P O w
        (q.evaluatePlain D) u := by
    show Multiset.filter (fun y : Tuple T n =>
        (GenPredIn.and (outerKeyCond P (fun _ => rfl) P) ψ).holdsPlain y u)
        ((q.substMap (weakenOuter T n)).evaluatePlain D u) = _
    rw [AggQueryIn.evaluatePlain_substMap, substVal_weakenOuter,
      ValueFrame.frameOf_of_containsSelf _ _ _ hc _ hu]
    refine Multiset.filter_congr (fun y _ => ?_)
    rw [holdsPlain_and_iff, outerKeyCond_holdsPlain, hρ y u]
    refine and_congr ?_ Iff.rfl
    exact ⟨fun hk => funext (fun k => hk k), fun hk k => congrFun hk k⟩
  rw [gammaScalar_one, hframe, Multiset.map_singleton]
  refine congrArg (fun x : Tuple T (n + 1) => ({x} : Multiset (Tuple T (n + 1))))
    ?_
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last,
      show (Fin.last n) = Fin.natAdd n (0 : Fin 1) from rfl, Fin.append_right]
    -- the aggregate is the window's value: the same rows, in the same order
    unfold ValueFrame.windowValue ValueFrame.frameListOf
    refine congrArg f ?_
    rw [show Relation.groupSeqOrd (fun k : Fin 0 => k.elim0)
          (GroupOrder.byCols O o)
          (ValueFrame.frameOf (α := Tuple T n) id P O w (q.evaluatePlain D) u)
          (fun k : Fin 0 => k.elim0)
        = OrderSpec.sortSeq (Tuple.key O) (id : Tuple T n → Tuple T n) o
          (sortList (ValueFrame.frameOf (α := Tuple T n) id P O w
            (q.evaluatePlain D) u)) from by
      show OrderSpec.sortSeq (Tuple.key O) (id : Tuple T n → Tuple T n) o
          (Relation.groupSeq (fun k : Fin 0 => k.elim0) _
            (fun k : Fin 0 => k.elim0)) = _
      rw [Relation.groupSeq_emptyKey]]
    refine List.map_congr_left (fun v _ => ?_)
    rw [TermIn.eval_substMap, substVal_weakenOuter]
  · rw [Fin.snoc_castSucc,
      show (Fin.castSucc i) = Fin.castAdd 1 i from rfl, Fin.append_left]

/-- **The derived form uses no window**: an apply, a scalar aggregation
and a selection, which is what the generation half of `thm:plainbasis`
asks of it. The apply then goes by the decorrelation. -/
theorem usesOnly_winByApply {S : Set OpKind} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ψ : GenPredIn T n (ColKind.allReg n)) (t : Term T n) (f : SeqAggFunc T)
    {q : AggQuery T n (ColKind.allReg n)} (ha : OpKind.apply ∈ S)
    (hg : OpKind.gamma ∈ S) (hs : OpKind.sel ∈ S) (hq : q.usesOnly S) :
    (winByApply P O o ψ t f q).usesOnly S := by
  rw [winByApply, AggQueryIn.usesOnly_castKind]
  exact ⟨ha, hq, hg, hs, (AggQueryIn.usesOnly_substMap q _).mpr hq⟩

/-- **A window is expressible without one** (`prop:winderived`), as the
equivalence of queries the classification uses. -/
theorem plainEquiv_winByApply (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) {w : ValueFrame T p} (hc : w.ContainsSelf)
    (ψ : GenPredIn T n (ColKind.allReg n))
    (hρ : ∀ y u : Tuple T n, ψ.holdsPlain y u
      ↔ w.ρ (Tuple.key O y) (Tuple.key O u) = true)
    (t : Term T n) (f : SeqAggFunc T) (q : AggQuery T n (ColKind.allReg n)) :
    (AggQueryIn.Win P O o w t f q
        (winReadsReg_allReg P O t)).PlainEquiv (winByApply P O o ψ t f q) := by
  intro D γ
  rw [show γ = (fun j : Fin 0 => (0 : T)) from funext (fun j => j.elim0)]
  exact (evaluatePlain_winByApply P O o hc ψ hρ t f q D).symm

end WinDerived

/-! ## Aggregation: the one operator that makes a row from nothing -/

/-- **Without `γ`, the empty instance has an empty answer.** Every other
operator maps the empty relation to an empty relation: a projection and a
window map it row by row, a selection filters it, a product and an apply
read one row of each side, a union adds, duplicate elimination and
difference only remove. Aggregation is the exception, the scalar form
emitting its row whatever its input. -/
theorem AggQueryIn.evaluatePlain_eq_zero_of_allEmpty {S : Set OpKind}
    (hγ : OpKind.gamma ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly S → ∀ (D : Database T), D.allEmpty → ∀ γ : Fin c → T,
      q.evaluatePlain D γ = 0 := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro _ D hD γ
    simp only [AggQueryIn.evaluatePlain]
    cases hf : D.find n s with
    | none => rfl
    | some rn => exact hD n s rn hf
  | Empty => intro _ D hD γ; rfl
  | Proj ps q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, ih hq.2 D hD γ]
    rfl
  | Sel φ q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, ih hq.2 D hD γ]
    rfl
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.2.1 D hD γ]
    rfl
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.2.1 D hD γ]
    rfl
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.2.1 D hD γ, ih₂ hq.2.2 D hD γ]
    rfl
  | Dedup q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, ih hq.2 D hD γ]
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.2.1 D hD γ]
    rfl
  | Alt k hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | Retag hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | Mu s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => intro hq; exact hq.elim
  | Gamma is ts fs q keep ord ih => intro hq; exact absurd hq.1 hγ
  | GammaScalar ts fs q ord ih => intro hq; exact absurd hq.1 hγ
  | GammaNest is his p f q ih => intro hq; exact absurd hq.1 hγ
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    rw [ih hq.2 D hD γ]
    rfl
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    rw [ih hq.2 D hD γ]
    rfl

/-- **And the unit relation breaks it**: one row on every instance, the
empty one included. So no generating set omits `γ`. -/
theorem AggQueryIn.evaluatePlain_unit_ne_zero (D : Database T)
    (γ : Fin 0 → T) : (AggQueryIn.unit : AggQuery T 0 _).evaluatePlain D γ ≠ 0 := by
  rw [AggQueryIn.evaluatePlain_unit D γ (fun j => j.elim0)]
  exact fun h => absurd (congrArg Multiset.card h) (by simp)
