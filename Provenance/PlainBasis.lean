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
being transparent to the plain semantics. The two recursions are `False`:
this predicate carries the scope of the classification as well, the
recursions being outside it. -/
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
  | _, _, _, .Gamma _ _ _ q _ => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .GammaScalar _ _ q => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .GammaNest _ _ _ _ q => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .GammaTok _ _ _ _ _ q _ => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .ProvSum _ _ _ q => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, .Win _ _ _ _ _ _ q _ _ _ => OpKind.win ∈ S ∧ q.usesOnly S
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => OpKind.win ∈ S ∧ q.usesOnly S

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
  | _, _, _, .Gamma _ _ _ q _ => q.overSchema sch
  | _, _, _, .GammaScalar _ _ q => q.overSchema sch
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
  | Gamma is ts fs q keep ih => intro h hq; exact ih h hq.2
  | GammaScalar ts fs q ih => intro h hq; exact ih h hq.2
  | GammaNest is his p f q ih => intro h hq; exact ih h hq.2
  | GammaTok is his ts fs a q keep ih => intro h hq; exact ih h hq.2
  | ProvSum is his t q ih => intro h hq; exact ih h hq.2
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
  | Gamma is ts fs q keep ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D hD γ)
  | GammaScalar ts fs q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain]
    rfl
  | GammaNest is his p f q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D hD γ)
  | GammaTok is his ts fs a q keep ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D hD γ)
  | ProvSum is his t q ih =>
    intro hq D hD γ
    simp only [AggQueryIn.evaluatePlain, Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D hD γ)
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
  | Gamma is ts fs q keep ih =>
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
  | GammaScalar ts fs q ih =>
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
  | GammaTok is his ts fs a q keep ih =>
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
  | ProvSum is his t q ih =>
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
  | _, _, _, .Gamma _ _ _ q _ => q.sizeBound
  | _, _, _, .GammaScalar _ _ _ => 1
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
  | Gamma is ts fs q keep ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D γ)
  | GammaScalar ts fs q ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, one_mul]
    exact Nat.succ_le_succ (Nat.zero_le _)
  | GammaNest is his p f q ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D γ)
  | GammaTok is his ts fs a q keep ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D γ)
  | ProvSum is his t q ih =>
    intro hq D γ
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 D γ)
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
  | _, _, _, .Gamma _ _ _ _ _ => 1
  | _, _, _, .GammaScalar _ _ _ => 1
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
  | Gamma is ts fs q keep ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd _ k)) (fun g => funext fun k => by
        rw [Fin.append_left]) u
  | GammaScalar ts fs q ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact le_trans (Multiset.count_le_card u _) (le_of_eq rfl)
  | GammaNest is his p f q ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd _ k)) (fun g => funext fun k => by
        rw [Fin.append_left]) u
  | GammaTok is his ts fs a q keep ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd 1 (Fin.castAdd _ k)))
      (fun g => funext fun k => by rw [Fin.append_left, Fin.append_left]) u
  | ProvSum is his t q ih =>
    intro hq D hD γ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd _ k)) (fun g => funext fun k => by
        rw [Fin.append_left]) u
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
  | Gamma is ts fs q keep ih => intro hq; exact absurd hq.1 hγ
  | GammaScalar ts fs q ih => intro hq; exact absurd hq.1 hγ
  | GammaNest is his p f q ih => intro hq; exact absurd hq.1 hγ
  | GammaTok is his ts fs a q keep ih => intro hq; exact absurd hq.1 hγ
  | ProvSum is his t q ih => intro hq; exact absurd hq.1 hγ
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
