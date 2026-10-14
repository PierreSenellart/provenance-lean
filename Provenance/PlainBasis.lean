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

`Explode` and `Retag` are transparent here: both read their argument's plain
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
  /-- The bag recursion `μ^⊎`, SQL's `WITH RECURSIVE … UNION ALL`. -/
  | muBag
  /-- The set recursion `μ^∪`, SQL's `WITH RECURSIVE … UNION`. -/
  | muSet
  deriving DecidableEq, Repr

/-- **The classes a query uses are among `S`.** A relation leaf is in no
class, every operator is in its own, and `Explode` and `Retag` are in none,
being transparent to the plain semantics.

Two operators are `False`: this predicate carries the scope of the
classification as well, and the token-building grouping and the
provenance sum are outside it. They belong to the rewritten world – they
are what ProvSQL's plans build, not what a source query is written with
– so a classification of the source language has nothing to say about
them.

**The two recursions are classes like the others** (`muBag`, `muSet`),
which is what `thm:plainbasis`'s second half grades. A class set holding
neither – `plainOps`, and every basis of `Provenance.BasisAssembly` –
therefore excludes a recursive query exactly as before, so the six rows
of the recursion-free classification are unchanged. -/
def AggQueryIn.usesOnly (S : Set OpKind) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => OpKind.empty ∈ S
  | _, _, _, _, .Proj ps q =>
      (OpKind.proj ∈ S ∧ ∀ j, (ps j).sourceCol = true) ∧ q.usesOnly S
  | _, _, _, _, .Sel _ q _ => OpKind.sel ∈ S ∧ q.usesOnly S
  | _, _, _, _, .Prod q₁ q₂ =>
      OpKind.prod ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, _, .Apply q₁ q₂ =>
      OpKind.apply ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, _, .Sum q₁ q₂ =>
      OpKind.union ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, _, .Dedup q => OpKind.dedup ∈ S ∧ q.usesOnly S
  | _, _, _, _, .Diff q₁ q₂ =>
      OpKind.diff ∈ S ∧ q₁.usesOnly S ∧ q₂.usesOnly S
  | _, _, _, _, .Explode _ _ q => q.usesOnly S
  | _, _, _, _, .Retag _ q => q.usesOnly S
  | _, _, _, _, .Mu _ q₀ q₁ =>
      OpKind.muBag ∈ S ∧ q₀.usesOnly S ∧ q₁.usesOnly S
  | _, _, _, _, .MuSet _ q₀ q₁ =>
      OpKind.muSet ∈ S ∧ q₀.usesOnly S ∧ q₁.usesOnly S
  | _, _, _, _, .Gamma _ _ _ q _ _ => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, _, .GammaScalar _ _ q _ => OpKind.gamma ∈ S ∧ q.usesOnly S
  | _, _, _, _, .GammaNest _ _ p _ q =>
      (OpKind.gamma ∈ S ∧ p.sourceCol = true) ∧ q.usesOnly S
  | _, _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  | _, _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => OpKind.win ∈ S ∧ q.usesOnly S
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => OpKind.win ∈ S ∧ q.usesOnly S

omit [ValueType T] in
/-- Transporting a query along an equality of kind vectors changes no
operator, so it changes nothing `usesOnly` sees. -/
@[simp] theorem AggQueryIn.usesOnly_castKind {c n : ℕ}
    {κ κ' : Fin n → ColKind} {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l)
    (S : Set OpKind) : (q.castKind h).usesOnly S ↔ q.usesOnly S := by
  cases h
  exact Iff.rfl

omit [ValueType T] in
/-- **Substituting the outer columns changes no operator**, so it changes
nothing `usesOnly` sees. This is what carries the classification through
the apply, whose right side is read under a substitution. -/
theorem AggQueryIn.usesOnly_substMap {S : Set OpKind} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).usesOnly S ↔ q.usesOnly S := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ => Iff.rfl
  | Hole n s => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    show (AggQueryIn.castKind _ (AggQueryIn.Proj
      (fun j => (ps j).substMap θ) (q.substMap θ))).usesOnly S ↔ _
    rw [AggQueryIn.usesOnly_castKind]
    exact and_congr (and_congr Iff.rfl (forall_congr' (fun j => by
      rw [ProjColIn.sourceCol_substMap]))) (ih θ)
  | Sel φ q _ ih => exact fun θ => and_congr Iff.rfl (ih θ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ θ))
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ _))
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ θ))
  | Dedup q ih => exact fun θ => and_congr Iff.rfl (ih θ)
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ θ))
  | Explode k h q ih => exact fun θ => ih θ
  | Retag h q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ =>
      exact fun θ => and_congr Iff.rfl (and_congr (ih₀ θ) (ih₁ θ))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
      exact fun θ => and_congr Iff.rfl (and_congr (ih₀ θ) (ih₁ θ))
  | Gamma is ts fs q keep ord ih =>
    exact fun θ => and_congr Iff.rfl (ih θ)
  | GammaScalar ts fs q ord ih => exact fun θ => and_congr Iff.rfl (ih θ)
  | GammaNest is his pc f q ih =>
    intro d θ
    exact and_congr (and_congr Iff.rfl (by rw [ProjColIn.sourceCol_substMap]))
      (ih θ)
  | GammaTok is his ts fs a q keep ih => exact fun θ => Iff.rfl
  | ProvSum is his t q ih => exact fun θ => Iff.rfl
  | Win P O o w t f q hrr dist keep ih =>
    exact fun θ => and_congr Iff.rfl (ih θ)
  | WinExpr P O o ws ts fs g q keeps ih =>
    exact fun θ => and_congr Iff.rfl (ih θ)

omit [ValueType T] in
/-- Carrying an input column through is a column the source language
writes. -/
@[simp] theorem AggQueryIn.sourceCol_carryCol {n : ℕ} (κ : Fin n → ColKind)
    (k : Fin n) : (AggQueryIn.carryCol (T := T) κ k).sourceCol = true := by
  unfold AggQueryIn.carryCol
  split <;> rfl

/-! ## Monotonicity of the classification -/

omit [ValueType T] in
/-- **The classification is monotone in the class set**: a query using
only the classes of `S` uses only those of any larger set. -/
theorem AggQueryIn.usesOnly_mono {S S' : Set OpKind} (hSS : S ⊆ S') :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.usesOnly S' := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun h => hSS h
  | Proj ps q ih => exact fun h => ⟨⟨hSS h.1.1, h.1.2⟩, ih h.2⟩
  | Sel φ q _ ih => exact fun h => ⟨hSS h.1, ih h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨hSS h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨hSS h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨hSS h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | Dedup q ih => exact fun h => ⟨hSS h.1, ih h.2⟩
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨hSS h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | Explode k h q ih => exact fun hq => ih hq
  | Retag h q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ =>
      exact fun h => ⟨hSS h.1, ih₀ h.2.1, ih₁ h.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
      exact fun h => ⟨hSS h.1, ih₀ h.2.1, ih₁ h.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ⟨hSS h.1, ih h.2⟩
  | GammaScalar ts fs q ord ih => exact fun h => ⟨hSS h.1, ih h.2⟩
  | GammaNest is his pc f q ih => exact fun h => ⟨⟨hSS h.1.1, h.1.2⟩, ih h.2⟩
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih => exact fun h => ⟨hSS h.1, ih h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ⟨hSS h.1, ih h.2⟩

/-- **Expressibility**: two queries of the same arity are equivalent when
their plain semantics agree on every instance. -/
def AggQueryIn.PlainEquiv {c n : ℕ} {κ κ' : Fin n → ColKind} {l l' : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (q' : AggQueryIn T c n κ' l') : Prop :=
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

/-- A schema: the arity of each relation name it declares, finitely many
names being declared. -/
structure Schema where
  /-- The arity of a name, or `none` where the schema does not declare it. -/
  decl : String → Option ℕ
  /-- A schema declares finitely many names. -/
  finite : {s | decl s ≠ none}.Finite

instance : CoeFun Schema (fun _ => String → Option ℕ) := ⟨Schema.decl⟩

/-- The schema declaring nothing. -/
def Schema.empty : Schema := ⟨fun _ => none, by simp⟩

@[simp] theorem Schema.empty_apply (s : String) : Schema.empty s = none := rfl

/-- Two schemas declaring the same arities are equal. -/
@[ext] theorem Schema.ext {sch₁ sch₂ : Schema} (h : ∀ s, sch₁ s = sch₂ s) : sch₁ = sch₂ := by
  obtain ⟨d₁, f₁⟩ := sch₁
  obtain ⟨d₂, f₂⟩ := sch₂
  have hd : d₁ = d₂ := funext h
  subst hd
  rfl

/-- Declaring one name, as a recursion's rounds do for the name they
bind. -/
theorem Schema.update_finite (sch : Schema) (s : String) (k : ℕ) :
    {s' | (if s' = s then some k else sch s') ≠ none}.Finite := by
  refine (sch.finite.insert s).subset (fun s' h => ?_)
  by_cases hs : s' = s
  · exact Set.mem_insert_iff.mpr (Or.inl hs)
  · refine Set.mem_insert_iff.mpr (Or.inr ?_)
    rw [Set.mem_ofPred_eq, ite_eq_right hs] at h
    exact h

def Schema.update (sch : Schema) (s : String) (k : ℕ) : Schema :=
  ⟨fun s' => if s' = s then some k else sch s', Schema.update_finite sch s k⟩

@[simp] theorem Schema.update_apply (sch : Schema) (s : String) (k : ℕ) (s' : String) :
    sch.update s k s' = if s' = s then some k else sch s' := rfl

/-- A schema declaring the names of a list, each with an arity. -/
def Schema.ofFn (f : String → Option ℕ) (N : Finset String) (h : ∀ s, f s ≠ none → s ∈ N) :
    Schema :=
  ⟨f, N.finite_toSet.subset (fun s hs => h s hs)⟩

@[simp] theorem Schema.ofFn_apply (f : String → Option ℕ) (N : Finset String)
    (h : ∀ s, f s ≠ none → s ∈ N) (s : String) : Schema.ofFn f N h s = f s := rfl

/-- **The name `s` does not occur in the query.** -/
def AggQueryIn.noMention (s : String) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ s' => s' ≠ s
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noMention s
  | _, _, _, _, .Sel _ q _ => q.noMention s
  | _, _, _, _, .Prod q₁ q₂ => q₁.noMention s ∧ q₂.noMention s
  | _, _, _, _, .Apply q₁ q₂ => q₁.noMention s ∧ q₂.noMention s
  | _, _, _, _, .Sum q₁ q₂ => q₁.noMention s ∧ q₂.noMention s
  | _, _, _, _, .Dedup q => q.noMention s
  | _, _, _, _, .Diff q₁ q₂ => q₁.noMention s ∧ q₂.noMention s
  | _, _, _, _, .Explode _ _ q => q.noMention s
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noMention s ∧ q₁.noMention s
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noMention s ∧ q₁.noMention s
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noMention s
  | _, _, _, _, .GammaScalar _ _ q _ => q.noMention s
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noMention s
  | _, _, _, _, .ProvSum _ _ _ q => q.noMention s
  | _, _, _, _, .Retag _ q => q.noMention s
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noMention s
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noMention s
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noMention s

omit [ValueType T] in
@[simp] theorem AggQueryIn.noMention_castKind {s : String} {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).noMention s ↔ q.noMention s := by
  cases h; exact Iff.rfl

omit [ValueType T] in
/-- Substituting the context does not change what is mentioned. -/
theorem AggQueryIn.noMention_substMap {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).noMention s ↔ q.noMention s := by
  intro c n κ l q
  induction q with
  | Rel n s' => exact fun θ => Iff.rfl
  | Hole n s' => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.noMention_castKind]
    exact ih θ
  | Sel φ q _ ih => exact fun θ => ih θ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ _)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Dedup q ih => exact fun θ => ih θ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Explode k hk q ih => exact fun θ => ih θ
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | Gamma is ts fs q keep ord ih => exact fun θ => ih θ
  | GammaScalar ts fs q ord ih => exact fun θ => ih θ
  | GammaNest is his p fn q ih => exact fun θ => ih θ
  | ProvSum is his t q ih => exact fun θ => ih θ
  | GammaTok is his ts fs a q keep ih => exact fun θ => ih θ
  | Win P O o w t fw q hrr dist keep ih => exact fun θ => ih θ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => ih θ

/-- **A well-formed query**: every relation reference names a relation the
schema declares, at the arity the schema gives it. A recursion binds a
name the schema does not declare, its base is over the schema, and its
term is over the schema extended by that name – which its hole reads –
and names it nowhere else (`AggQueryIn.noMention`): the hole is the one
reference to the round, as the typing of the term asks, and a free
reference to the bound name would be a second one. -/
def AggQueryIn.overSchema (sch : Schema) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel n s => sch s = some n
  | _, _, _, _, .Hole n s => sch s = some n
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.overSchema sch
  | _, _, _, _, .Sel _ q _ => q.overSchema sch
  | _, _, _, _, .Prod q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, _, .Apply q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, _, .Sum q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, _, .Dedup q => q.overSchema sch
  | _, _, _, _, .Diff q₁ q₂ => q₁.overSchema sch ∧ q₂.overSchema sch
  | _, _, _, _, .Explode _ _ q => q.overSchema sch
  | _, _, _, _, .Retag _ q => q.overSchema sch
  | _, n, _, _, .Mu s q₀ q₁ =>
      sch s = none ∧ q₀.overSchema sch ∧ q₁.noMention s ∧ q₁.overSchema (sch.update s n)
  | _, n, _, _, .MuSet s q₀ q₁ =>
      sch s = none ∧ q₀.overSchema sch ∧ q₁.noMention s ∧ q₁.overSchema (sch.update s n)
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.overSchema sch
  | _, _, _, _, .GammaScalar _ _ q _ => q.overSchema sch
  | _, _, _, _, .GammaNest _ _ _ _ q => q.overSchema sch
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.overSchema sch
  | _, _, _, _, .ProvSum _ _ _ q => q.overSchema sch
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.overSchema sch
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.overSchema sch

/-- **A conforming instance**: it binds every name the schema declares, at
the declared arity. -/
def Database.Conforms (sch : Schema) (D : Database T) : Prop :=
  ∀ (s : String) (k : ℕ), sch s = some k → ∃ r : Relation T k,
    D.find k s = some r

omit [ValueType T] in
/-- Transporting along an equality of kind vectors names the same
relations. -/
@[simp] theorem AggQueryIn.overSchema_castKind {sch : Schema} {c n : ℕ}
    {κ κ' : Fin n → ColKind} {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).overSchema sch ↔ q.overSchema sch := by
  cases h
  exact Iff.rfl

/-- **Expressibility over a schema**: the two queries agree on every
instance *of that schema*, which is what the generation statement asks –
a query is not evaluated on an instance of another schema. Agreement on
every instance is stronger, and gives this one. -/
def AggQueryIn.PlainEquivOn (sch : Schema) {c n : ℕ}
    {κ κ' : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
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
    rw [Schema.update_apply, ite_eq_left rfl] at h
    obtain rfl : k' = k := (Option.some.inj h).symm
    exact ⟨X, Database.find_assign s' X D⟩
  · rw [Schema.update_apply, ite_eq_right hs] at h
    obtain ⟨r, hr⟩ := hD s' k' h
    exact ⟨r, (Database.find_assign_of_ne s s' X D
      (fun hc => hs hc.2)).trans hr⟩

omit [ValueType T] in
omit [ValueType T] in
/-- **Substituting the outer columns names the same relations**: it
changes no leaf. -/
theorem AggQueryIn.overSchema_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d) (sch : Schema),
      (q.substMap θ).overSchema sch ↔ q.overSchema sch := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ sch => Iff.rfl
  | Hole n s => exact fun θ sch => Iff.rfl
  | Empty => exact fun θ sch => Iff.rfl
  | Proj ps q ih =>
    intro d θ sch
    show (AggQueryIn.castKind _ (AggQueryIn.Proj
      (fun j => (ps j).substMap θ) (q.substMap θ))).overSchema sch ↔ _
    rw [AggQueryIn.overSchema_castKind]
    exact ih θ sch
  | Sel φ q _ ih => exact fun θ sch => ih θ sch
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun θ sch => and_congr (ih₁ θ sch) (ih₂ θ sch)
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun θ sch => and_congr (ih₁ θ sch) (ih₂ _ sch)
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun θ sch => and_congr (ih₁ θ sch) (ih₂ θ sch)
  | Dedup q ih => exact fun θ sch => ih θ sch
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun θ sch => and_congr (ih₁ θ sch) (ih₂ θ sch)
  | Explode k h q ih => exact fun θ sch => ih θ sch
  | Retag h q ih => exact fun θ sch => ih θ sch
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact fun θ sch => and_congr Iff.rfl
      (and_congr (ih₀ θ sch) (and_congr (AggQueryIn.noMention_substMap q₁ θ)
        (ih₁ θ (Schema.update sch s _))))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun θ sch => and_congr Iff.rfl
      (and_congr (ih₀ θ sch) (and_congr (AggQueryIn.noMention_substMap q₁ θ)
        (ih₁ θ (Schema.update sch s _))))
  | Gamma is ts fs q keep ord ih => exact fun θ sch => ih θ sch
  | GammaScalar ts fs q ord ih => exact fun θ sch => ih θ sch
  | GammaNest is his pc f q ih => exact fun θ sch => ih θ sch
  | GammaTok is his ts fs a q keep ih => exact fun θ sch => ih θ sch
  | ProvSum is his t q ih => exact fun θ sch => ih θ sch
  | Win P O o w t f q hrr dist keep ih => exact fun θ sch => ih θ sch
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ sch => ih θ sch

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
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.overSchema Schema.empty → q.usesOnly S → OpKind.empty ∈ S := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro h _
    have hnone : (none : Option ℕ) = some n := h
    exact (Option.some_ne_none n hnone.symm).elim
  | Hole n s =>
    intro h _
    have hnone : (none : Option ℕ) = some n := h
    exact (Option.some_ne_none n hnone.symm).elim
  | Empty => intro _ h; exact h
  | Proj ps q ih => intro h hq; exact ih h hq.2
  | Sel φ q _ ih => intro h hq; exact ih h hq.2
  | Prod q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Apply q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Sum q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Dedup q ih => intro h hq; exact ih h hq.2
  | Diff q₁ q₂ ih₁ ih₂ => intro h hq; exact ih₁ h.1 hq.2.1
  | Explode k hk q ih => intro h hq; exact ih h hq
  | Retag hk q ih => intro h hq; exact ih h hq
  | Mu s q₀ q₁ ih₀ ih₁ => intro h hq; exact ih₀ h.2.1 hq.2.1
  | MuSet s q₀ q₁ ih₀ ih₁ => intro h hq; exact ih₀ h.2.1 hq.2.1
  | Gamma is ts fs q keep ord ih => intro h hq; exact ih h hq.2
  | GammaScalar ts fs q ord ih => intro h hq; exact ih h hq.2
  | GammaNest is his p f q ih => intro h hq; exact ih h hq.2
  | GammaTok is his ts fs a q keep ih => intro _ hq; exact hq.elim
  | ProvSum is his t q ih => intro _ hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih => intro h hq; exact ih h hq.2
  | WinExpr P O o ws ts fs g q keeps ih => intro h hq; exact ih h hq.2

/-! ## The signature: which functions and which aggregates

`sec:prelim`'s signature `𝒜(Ω, Θ)` is a parameter of the *language* and
not of the semantics: `Ω` says which functions a term may apply to
values, `Θ` which aggregate functions are available. The classification's
rows for `win` and for `μ^⊎` are the two that depend on it – they hold in
the **minimal signature** `𝒜(∅, {count})`, where a term is a column or a
constant and the only aggregate is a count – so the predicates below are
what those rows are stated against. The other rows hold for every `Ω` and
every `Θ` containing a count, and the generation half is stated over
every signature, aggregates being arbitrary function parameters of the
syntax: that is why `AggQueryIn.exists_basisOps_plainEquiv` asks only for
a counting aggregate and nothing else.

`Ω = ∅` cannot be arranged by instantiating a parameter – the
vocabulary `+`, `-`, `*`, `CASE` and `COALESCE` is built into `TermIn` –
so it is a predicate on terms (`noFun`). `Θ` is a set the aggregates are
asked to belong to. -/

/-- **A term that applies no function to values**: a column, an outer
column, or a constant. `Ω = ∅` of the minimal signature. -/
def TermIn.noFun {c k : ℕ} : TermIn T c k → Bool
  | .const _ => true
  | .outer _ => true
  | .index _ => true
  | .add _ _ => false
  | .sub _ _ => false
  | .mul _ _ => false
  | .caseWhen _ _ _ _ _ => false
  | .coalesce _ _ => false

/-- The same over the kind-indexed terms. A gate term – a comparison
read as a value (`cmpAgg`, `chiGate`) – is a function on values too, and
belongs to the rewritten world besides. -/
def TermGIn.noFun {c k : ℕ} {κ : Fin k → ColKind} : TermGIn T c κ → Bool
  | .const _ => true
  | .outer _ => true
  | .index _ _ => true
  | .provIndex _ _ => true
  | .cmpAgg _ _ _ _ => false
  | .chiGate _ _ _ => false
  | .add _ _ => false
  | .sub _ _ => false
  | .mul _ _ => false
  | .caseWhen _ _ _ _ _ => false
  | .coalesce _ _ => false

/-- A classical term reads no function either. -/
def BoolTerm.noFun {k : ℕ} (b : BoolTerm T k) : Bool :=
  (b.args).1.noFun && (b.args).2.noFun

/-- And a classical selection: the comparisons are the signature's
predicates, which the minimal signature keeps; what it asks is that
their arguments be columns and constants. -/
def Selection.noFun {k : ℕ} : Selection T k → Bool
  | .BT b => b.noFun
  | .Not φ => φ.noFun
  | .And φ ψ => φ.noFun && ψ.noFun
  | .Or φ ψ => φ.noFun && ψ.noFun
  | .True => true

/-- A clause, or none. -/
def Selection.noFunOpt {k : ℕ} : Option (Selection T k) → Bool
  | none => true
  | some φ => φ.noFun

/-- A predicate of the general syntax: its comparisons are the
signature's own, so what is asked is of their terms. -/
def GenPredIn.noFun {c k : ℕ} {κ : Fin k → ColKind} :
    GenPredIn T c κ → Bool
  | .cmp _ t₁ t₂ => t₁.noFun && t₂.noFun
  | .aggCmp _ _ _ t => t.noFun
  | .aggRange _ _ _ t₁ _ t₂ => t₁.noFun && t₂.noFun
  | .and φ ψ => φ.noFun && ψ.noFun
  | .or φ ψ => φ.noFun && ψ.noFun
  | .not φ => φ.noFun

/-- An output column: a term of the signature, a token column carried
through, or a term over an aggregate column. The rewritten world's
column, which applies an arbitrary function, is in no signature. -/
def ProjColIn.noFun {c k : ℕ} {κ : Fin k → ColKind} :
    ProjColIn T c κ → Bool
  | .term t => t.noFun
  | .token _ _ => true
  | .aggTerm _ _ _ => false
  | .aggTermOf _ _ t => t.noFun
  | .provTerm t => t.noFun

/-- **The query is in the signature `𝒜(Ω, Θ)`**, for `Ω` read as
`noFun` – no function on values – and `Θ` the aggregates it may use. A
second-level aggregation reads its group as a bag, so its outer
aggregate is asked to be a symmetric member of `Θ` read that way
(`SeqAggFunc.onBag`).

Three operators are `False` **because they apply a function to values**,
which `Ω` does not hold: the two of the rewritten world fold the
domain's `+` into their provenance column (`ProvSum`, `GammaTok`), and a
multi-frame window combines its leaves by an arbitrary function – which
is why SQL's distribution functions take their arithmetic as a parameter
here. So a value of the result of a query in the signature is a value of
the instance, a constant of the query, or an aggregate of one of `Θ`,
which is what the row of `μ^⊎` reads. -/
def AggQueryIn.inSig (Θ : Set (SeqAggFunc T)) : {c n : ℕ} →
    {κ : Fin n → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj ps q =>
      (∀ j, (ps j).noFun = true) ∧ q.inSig Θ
  | _, _, _, _, .Sel φ q _ => φ.noFun = true ∧ q.inSig Θ
  | _, _, _, _, .Prod q₁ q₂ => q₁.inSig Θ ∧ q₂.inSig Θ
  | _, _, _, _, .Apply q₁ q₂ => q₁.inSig Θ ∧ q₂.inSig Θ
  | _, _, _, _, .Sum q₁ q₂ => q₁.inSig Θ ∧ q₂.inSig Θ
  | _, _, _, _, .Dedup q => q.inSig Θ
  | _, _, _, _, .Diff q₁ q₂ => q₁.inSig Θ ∧ q₂.inSig Θ
  | _, _, _, _, .Explode _ _ q => q.inSig Θ
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.inSig Θ ∧ q₁.inSig Θ
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.inSig Θ ∧ q₁.inSig Θ
  | _, _, _, _, .Gamma _ ts fs q keep _ =>
      (∀ j, (ts j).noFun = true) ∧ (∀ j, fs j ∈ Θ)
        ∧ (∀ j, Selection.noFunOpt (keep j) = true) ∧ q.inSig Θ
  | _, _, _, _, .GammaScalar ts fs q _ =>
      (∀ j, (ts j).noFun = true) ∧ (∀ j, fs j ∈ Θ) ∧ q.inSig Θ
  | _, _, _, _, .GammaNest _ _ p f q =>
      p.noFun = true
        ∧ (∃ (g : SeqAggFunc T) (hg : g.Symmetric),
            g ∈ Θ ∧ f = SeqAggFunc.onBag g hg)
        ∧ q.inSig Θ
  | _, _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, _, .Retag _ q => q.inSig Θ
  | _, _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  | _, _, _, _, .Win _ _ _ _ t f q _ dist keep =>
      t.noFun = true ∧ (if dist then f.distinct ∈ Θ else f ∈ Θ)
        ∧ Selection.noFunOpt keep = true ∧ q.inSig Θ
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

/-- **The minimal signature** `𝒜(∅, {count})`: no function on values,
and one counting aggregate. The aggregate is a parameter with
`SeqAggFunc.Counts` as its specification, as everywhere else in this
file – `count` is a function of the value domain and not a fixed one. -/
def AggQueryIn.inMinimalSig {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (cnt : SeqAggFunc T) (q : AggQueryIn T c n κ l) : Prop :=
  q.inSig {cnt}

@[simp] theorem AggQueryIn.inSig_castKind {c n : ℕ}
    {κ κ' : Fin n → ColKind} {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l)
    (Θ : Set (SeqAggFunc T)) : (q.castKind h).inSig Θ ↔ q.inSig Θ := by
  cases h
  exact Iff.rfl

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
    (hu : OpKind.union ∉ S) (hmb : OpKind.muBag ∉ S)
    (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → ∀ (D : Database T), Database.Thin D → ∀ γ : Fin c → T,
      Multiset.card (q.evaluatePlain D γ) ≤ 1 := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ D hD γ
    simp only [AggQueryIn.evaluatePlain]
    cases hf : D.find n s with
    | none => exact Nat.zero_le 1
    | some rn => exact hD n s rn hf
  | Hole n s =>
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
  | Sel φ q _ ih =>
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
  | Explode k hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | Retag hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | Mu s q₀ q₁ ih₀ ih₁ => intro hq; exact absurd hq.1 hmb
  | MuSet s q₀ q₁ ih₀ ih₁ => intro hq; exact absurd hq.1 hms
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

/-! ## What a query reads of the instance

The set recursion's case of the invariant runs over the *rounds*, each
read in the instance extended by the previous one, so two facts about
what a query reads of an instance are needed first: that it reads it
only through `Database.find`, and that a query naming nothing of the
recursion is blind to the extension. The second is what bounds a count
*inside* a recursion by a polynomial in the original instance – SQL
forbids the recursive reference under an aggregation, which is what
makes every count inside the body one over a query without it.
-/


/-- **The relations a query reads off the instance**, each with the arity
it reads it at: its leaves, less the one a body reads its own recursive
name at – the name at the recursion's arity, which is bound. A leaf naming
that name at another arity reads the instance and stays free. -/
def AggQueryIn.leaves : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c n κ l →
    List (ℕ × String)
  | _, _, _, _, .Rel k s => [(k, s)]
  | _, _, _, _, .Hole k s => [(k, s)]
  | _, _, _, _, .Empty => []
  | _, _, _, _, .Proj _ q => q.leaves
  | _, _, _, _, .Sel _ q _ => q.leaves
  | _, _, _, _, .Prod q₁ q₂ => q₁.leaves ++ q₂.leaves
  | _, _, _, _, .Apply q₁ q₂ => q₁.leaves ++ q₂.leaves
  | _, _, _, _, .Sum q₁ q₂ => q₁.leaves ++ q₂.leaves
  | _, _, _, _, .Dedup q => q.leaves
  | _, _, _, _, .Diff q₁ q₂ => q₁.leaves ++ q₂.leaves
  | _, _, _, _, .Explode _ _ q => q.leaves
  | _, _, _, _, .Retag _ q => q.leaves
  | _, n, _, _, .Mu s q₀ q₁ => q₀.leaves ++ q₁.leaves.filter (fun p => p ≠ (n, s))
  | _, n, _, _, .MuSet s q₀ q₁ => q₀.leaves ++ q₁.leaves.filter (fun p => p ≠ (n, s))
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.leaves
  | _, _, _, _, .GammaScalar _ _ q _ => q.leaves
  | _, _, _, _, .GammaNest _ _ _ _ q => q.leaves
  | _, _, _, _, .ProvSum _ _ _ q => q.leaves
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.leaves
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.leaves
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.leaves

omit [ValueType T] in
/-- A leaf of a query carrying a name the query does not mention is one of
its holes. -/
theorem AggQueryIn.mem_index_of_mem_leaves {t : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention t → ∀ p ∈ q.leaves, p.2 = t → (p.2, p.1) ∈ l := by
  intro c n κ l q
  induction q with
  | Rel k s =>
    intro h p hp hpt
    rw [List.mem_singleton.mp hp] at hpt
    exact absurd hpt h
  | Hole k s =>
    intro _ p hp _
    rw [List.mem_singleton.mp hp]
    exact List.mem_singleton_self _
  | Empty => exact fun _ p hp => absurd hp List.not_mem_nil
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro h p hp hpt
    exact (List.mem_append.mp hp).elim
      (fun hp => List.mem_append.mpr (Or.inl (ih₁ h.1 p hp hpt)))
      (fun hp => List.mem_append.mpr (Or.inr (ih₂ h.2 p hp hpt)))
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h p hp hpt
    exact (List.mem_append.mp hp).elim (fun hp => ih₁ h.1 p hp hpt)
      (fun hp => absurd (ih₂ h.2 p hp hpt) (by simp))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro h p hp hpt
    exact (List.mem_append.mp hp).elim
      (fun hp => List.mem_append.mpr (Or.inl (ih₁ h.1 p hp hpt)))
      (fun hp => List.mem_append.mpr (Or.inr (ih₂ h.2 p hp hpt)))
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro h p hp hpt
    exact (List.mem_append.mp hp).elim (fun hp => ih₁ h.1 p hp hpt) (fun hp => ih₂ h.2 p hp hpt)
  | Explode k hk q ih => exact ih
  | Retag hk q ih => exact ih
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro h p hp hpt
    refine (List.mem_append.mp hp).elim (fun hp => ih₀ h.1 p hp hpt) (fun hp => ?_)
    have hmem := ih₁ h.2 p (List.mem_of_mem_filter hp) hpt
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (List.mem_singleton.mp hmem)
    exact absurd (Prod.ext h₂ h₁) (of_decide_eq_true (List.mem_filter.mp hp).2)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro h p hp hpt
    refine (List.mem_append.mp hp).elim (fun hp => ih₀ h.1 p hp hpt) (fun hp => ?_)
    have hmem := ih₁ h.2 p (List.mem_of_mem_filter hp) hpt
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (List.mem_singleton.mp hmem)
    exact absurd (Prod.ext h₂ h₁) (of_decide_eq_true (List.mem_filter.mp hp).2)
  | Gamma is ts fs q keep ord ih => exact ih
  | GammaScalar ts fs q ord ih => exact ih
  | GammaNest is his p fn q ih => exact ih
  | ProvSum is his t q ih => exact ih
  | GammaTok is his ts fs a q keep ih => exact ih
  | Win P O o w t fw q hrr dist keep ih => exact ih
  | WinExpr P O o ws ts fs g q keeps ih => exact ih

omit [ValueType T] in
/-- A leaf of a closed query not mentioning a name does not carry it. -/
theorem AggQueryIn.ne_of_noMention_of_mem_leaves {t : String} {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (h : q.noMention t) : ∀ p ∈ q.leaves, p.2 ≠ t :=
  fun p hp hpt => absurd (AggQueryIn.mem_index_of_mem_leaves q h p hp hpt) List.not_mem_nil

/-- **A query reads an instance only through `Database.find`.** -/
theorem AggQueryIn.evaluatePlain_congr_find :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {D D' : Database T},
      (∀ (k : ℕ) (s : String), D.find k s = D'.find k s) → ∀ γ : Fin c → T,
        q.evaluatePlain D γ = q.evaluatePlain D' γ := by
  have hassign : ∀ {D D' : Database T} (s : String) {m : ℕ}
      (X : Relation T m),
      (∀ (k : ℕ) (s : String), D.find k s = D'.find k s) →
      ∀ (k : ℕ) (s' : String),
        (D.assign s X).find k s' = (D'.assign s X).find k s' := by
    intro D D' s m X h k s'
    by_cases hc : k = m ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := hc
      rw [Database.find_assign, Database.find_assign]
    · rw [Database.find_assign_of_ne s s' X D hc,
        Database.find_assign_of_ne s s' X D' hc, h]
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro D D' h γ
    show (match D.find n s with
      | none => (0 : Relation T n) | some rn => rn)
      = (match D'.find n s with
      | none => (0 : Relation T n) | some rn => rn)
    rw [h]
  | Hole n s =>
    intro D D' h γ
    show (match D.find n s with
      | none => (0 : Relation T n) | some rn => rn)
      = (match D'.find n s with
      | none => (0 : Relation T n) | some rn => rn)
    rw [h]
  | Empty => intro _ _ _ _; rfl
  | Proj ps q ih => intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | Sel φ q _ ih => intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih₁ h, ih₂ h]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih₁ h, ih₂ h]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih₁ h, ih₂ h]
  | Dedup q ih => intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih₁ h, ih₂ h]
  | Explode k hk q ih => intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro D D' h γ
    show muSumFix (fun X => q₁.evaluatePlain (D.assign s X) γ)
        (q₀.evaluatePlain D γ)
      = muSumFix (fun X => q₁.evaluatePlain (D'.assign s X) γ)
        (q₀.evaluatePlain D' γ)
    exact congrArg₂ muSumFix (funext (fun X => ih₁ (hassign s X h) γ))
      (ih₀ h γ)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro D D' h γ
    show muFix (fun X => (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup)
      = muFix (fun X => (q₀.evaluatePlain D' γ + q₁.evaluatePlain (D'.assign s X) γ).dedup)
    exact congrArg muFix (funext (fun X => by
      rw [ih₀ h γ, ih₁ (hassign s X h) γ]))
  | Gamma is ts fs q keep ord ih =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | GammaScalar ts fs q ord ih =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | GammaNest is his p f q ih =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | ProvSum is his t q ih =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | Retag hk q ih => intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | GammaTok is his ts fs a q keep ih =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | Win P O o w t f q hrr dist keep ih =>
    intro D D' h γ; simp only [AggQueryIn.evaluatePlain, ih h]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro D D' h γ
    simp only [AggQueryIn.evaluatePlain]
    rw [ih h γ]

/-- **Two instances agreeing away from a name**, the holes of a term
excepted: what a hole reads is the round it stands for, which both
instances hold alike. -/
abbrev Database.AgreeOff (s : String) (l : List (String × ℕ)) (D D' : Database T) : Prop :=
  ∀ (k : ℕ) (t : String), t ≠ s ∨ (t, k) ∈ l → D.find k t = D'.find k t

omit [ValueType T] in
theorem Database.AgreeOff.mono {s : String} {l l' : List (String × ℕ)} {D D' : Database T}
    (hl : ∀ p ∈ l', p ∈ l) (h : Database.AgreeOff s l D D') : Database.AgreeOff s l' D D' :=
  fun k t ht => h k t (ht.imp_right (hl _))

omit [ValueType T] in
/-- Binding a round for the name a term's hole carries keeps two
instances agreeing: away from `s`, and at the hole, which both read as
the round. -/
theorem Database.AgreeOff.assign {s : String} {D D' : Database T} (s' : String) {m : ℕ}
    (Y : Relation T m) (h : Database.AgreeOff s [] D D') :
    Database.AgreeOff s [(s', m)] (D.assign s' Y) (D'.assign s' Y) := by
  intro k t ht
  by_cases hc : k = m ∧ t = s'
  · obtain ⟨rfl, rfl⟩ := hc
    rw [Database.find_assign, Database.find_assign]
  · have ht' : t ≠ s := by
      rcases ht with ht | ht
      · exact ht
      · exact absurd (Prod.mk.inj (List.mem_singleton.mp ht)) (fun h' => hc ⟨h'.2, h'.1⟩)
    rw [Database.find_assign_of_ne s' t Y D hc, Database.find_assign_of_ne s' t Y D' hc,
      h k t (Or.inl ht')]

/-- **A query that does not name `s` is blind to what `s` holds**: two
instances agreeing away from `s` give it the same answer. With
`D' = D.assign s X` this is the non-interference the recursion's case
needs – a count inside the body of a recursion that does not read the
recursive relation is a count over the instance the recursion started
from. -/
theorem AggQueryIn.evaluatePlain_congr_of_noMention {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention s → ∀ {D D' : Database T}, Database.AgreeOff s l D D' →
      ∀ γ : Fin c → T, q.evaluatePlain D γ = q.evaluatePlain D' γ := by
  have hassign : ∀ {D D' : Database T} (s' : String) {m : ℕ} (Y : Relation T m),
      Database.AgreeOff s [] D D' →
      Database.AgreeOff s [(s', m)] (D.assign s' Y) (D'.assign s' Y) :=
    fun s' _ Y h => Database.AgreeOff.assign s' Y h
  have hL : ∀ {l₁ l₂ : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s (l₁ ++ l₂) D D' → Database.AgreeOff s l₁ D D' :=
    fun h => h.mono (fun _ hp => List.mem_append_left _ hp)
  have hR : ∀ {l₁ l₂ : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s (l₁ ++ l₂) D D' → Database.AgreeOff s l₂ D D' :=
    fun h => h.mono (fun _ hp => List.mem_append_right _ hp)
  have hN : ∀ {l : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s l D D' → Database.AgreeOff s [] D D' :=
    fun h => h.mono (fun _ hp => absurd hp List.not_mem_nil)
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro hq D D' h γ
    show (match D.find n s' with
      | none => (0 : Relation T n) | some rn => rn)
      = (match D'.find n s' with
      | none => (0 : Relation T n) | some rn => rn)
    rw [h n s' (Or.inl hq)]
  | Hole n s' =>
    intro _ D D' h γ
    show (match D.find n s' with
      | none => (0 : Relation T n) | some rn => rn)
      = (match D'.find n s' with
      | none => (0 : Relation T n) | some rn => rn)
    rw [h n s' (Or.inr (List.mem_singleton_self _))]
  | Empty => intro _ _ _ _ _; rfl
  | Proj ps q ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | Sel φ q _ ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.1 (hL h), ih₂ hq.2 (hR h)]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.1 h, ih₂ hq.2 (hN h)]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.1 (hL h), ih₂ hq.2 (hR h)]
  | Dedup q ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.1 h, ih₂ hq.2 h]
  | Explode k hk q ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    intro hq D D' h γ
    show muSumFix (fun Y => q₁.evaluatePlain (D.assign s' Y) γ)
        (q₀.evaluatePlain D γ)
      = muSumFix (fun Y => q₁.evaluatePlain (D'.assign s' Y) γ)
        (q₀.evaluatePlain D' γ)
    exact congrArg₂ muSumFix
      (funext (fun Y => ih₁ hq.2 (hassign s' Y h) γ)) (ih₀ hq.1 h γ)
  | MuSet s' q₀ q₁ ih₀ ih₁ =>
    intro hq D D' h γ
    show muFix (fun Y => (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s' Y) γ).dedup)
      = muFix (fun Y => (q₀.evaluatePlain D' γ + q₁.evaluatePlain (D'.assign s' Y) γ).dedup)
    exact congrArg muFix (funext (fun Y => by
      rw [ih₀ hq.1 h γ, ih₁ hq.2 (hassign s' Y h) γ]))
  | Gamma is ts fs q keep ord ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | GammaScalar ts fs q ord ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | GammaNest is his p f q ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | ProvSum is his t q ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | Retag hk q ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | GammaTok is his ts fs a q keep ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | Win P O o w t f q hrr dist keep ih =>
    intro hq D D' h γ; simp only [AggQueryIn.evaluatePlain, ih hq h]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq D D' h γ
    simp only [AggQueryIn.evaluatePlain]
    rw [ih hq h γ]

/-- **And so it is blind to the recursion's own relation.** -/
theorem AggQueryIn.evaluatePlain_assign_of_noMention {s : String} {m : ℕ}
    (X : Relation T m) {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (hq : q.noMention s) (D : Database T)
    (γ : Fin c → T) :
    q.evaluatePlain (D.assign s X) γ = q.evaluatePlain D γ :=
  AggQueryIn.evaluatePlain_congr_of_noMention q hq
    (fun _k s' hs' =>
      Database.find_assign_of_ne s s' X D (fun hc => (hs'.resolve_right List.not_mem_nil) hc.2))
    γ

/-! ## What SQL asks of a recursive term

`WITH RECURSIVE` restricts the recursive term: the self-reference may
not appear under an aggregate or a window function, under `DISTINCT`, or
in an `EXCEPT` (PostgreSQL refuses each of them, and the standard does
too). `AggQueryIn.recGuarded` is that restriction, and the invariant
needs it: a count *inside* a recursion whose input reads the recursive
relation would grow with the rounds, and the values the rounds take
would not close on a set the instance fixes. Under the restriction every
count inside the body is over a query the recursion does not feed, so
`AggQueryIn.evaluatePlain_assign_of_noMention` reads it off the instance
the recursion started from.

The restriction SQL also carries – the self-reference occurring exactly
once, and not in a subquery – is about termination and not about this,
so it is not asked here.
-/

/-- **The recursive relation `s` occurs under no aggregation, window,
duplicate elimination or difference.** -/
def AggQueryIn.recGuarded (s : String) : {c n : ℕ} →
    {κ : Fin n → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.recGuarded s
  | _, _, _, _, .Sel _ q _ => q.recGuarded s
  | _, _, _, _, .Prod q₁ q₂ => q₁.recGuarded s ∧ q₂.recGuarded s
  | _, _, _, _, .Apply q₁ q₂ => q₁.recGuarded s ∧ q₂.recGuarded s
  | _, _, _, _, .Sum q₁ q₂ => q₁.recGuarded s ∧ q₂.recGuarded s
  | _, _, _, _, .Dedup q => q.noMention s
  | _, _, _, _, .Diff q₁ q₂ => q₁.noMention s ∧ q₂.noMention s
  | _, _, _, _, .Explode _ _ q => q.recGuarded s
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.recGuarded s ∧ q₁.recGuarded s
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.recGuarded s ∧ q₁.recGuarded s
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noMention s
  | _, _, _, _, .GammaScalar _ _ q _ => q.noMention s
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noMention s
  | _, _, _, _, .ProvSum _ _ _ q => q.noMention s
  | _, _, _, _, .Retag _ q => q.recGuarded s
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noMention s
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noMention s
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noMention s

omit [ValueType T] in
/-- A query that never names the recursive relation satisfies the
restriction. -/
theorem AggQueryIn.recGuarded_of_noMention {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention s → q.recGuarded s := by
  intro c n κ l q
  induction q with
  | Rel n s' => exact fun _ => trivial
  | Hole n s' => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.1, ih₂ hq.2⟩
  | Dedup q ih => exact fun hq => hq
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => hq
  | Explode k hk q ih => exact ih
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.1, ih₁ hq.2⟩
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.1, ih₁ hq.2⟩
  | Gamma is ts fs q keep ord ih => exact fun hq => hq
  | GammaScalar ts fs q ord ih => exact fun hq => hq
  | GammaNest is his p f q ih => exact fun hq => hq
  | ProvSum is his t q ih => exact fun hq => hq
  | Retag hk q ih => exact ih
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq
  | Win P O o w t f q hrr dist keep ih => exact fun hq => hq
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq => hq

/-! ## How a recursive term may read the recursive relation

`sec:plain` restricts a recursion: in `μR.(q₀, q₁)` the base `q₀` does
not read `R`, and in the body `q₁` the name `R` occurs **once**, and only
under a projection, a selection on regular columns, either side of a
product, the left side of an apply, or a union. That is narrower than the
Lean's syntax, which lets a recursion be written with the name anywhere,
and narrower than `AggQueryIn.recGuarded` – which only keeps `R` out of
an aggregation, a window, a duplicate elimination and a difference. The
rows of `tab:basisclasses` that survive a recursion are stated against
this restriction (relayed by the semantics session, 2026-10-09), so it is
what a result about the whole algebra asks of a query.

What it gives for free is `recGuarded_of_recOnce`: the operators a
recursive term may read `R` under are none of the four the weaker
restriction keeps it out of, so everything proved there applies. What it
does **not** give is one storey of recursion – the *other* side of a
product, and an apply's right side, are arbitrary queries that do not
read `R`, and either may be a recursion of its own. So a body is not
recursion-free, and the value analysis has to reach those sub-recursions
through the outer induction rather than through
`AggQueryIn.exists_valsIn_assign`, which asks `noRec` of what it
aggregates.

`Explode` and `Retag` are on the list here though the document does not name
them: they are the kind discipline's two operators, identities on plain
relations, so they move no value and read no column.
-/

/-- **Every recursion of the query is hygienic**: neither its base nor
its term names the bound relation freely. The typing of the holes says
the rest – that the term reads the relation once and only where it may –
and a query over a schema is hygienic (`AggQueryIn.hygienic_of_overSchema`),
the schema not declaring a bound name; what the predicate carries is the
semantic condition the evaluator's binding of the name needs. -/
def AggQueryIn.hygienic : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.hygienic
  | _, _, _, _, .Sel _ q _ => q.hygienic
  | _, _, _, _, .Prod q₁ q₂ => q₁.hygienic ∧ q₂.hygienic
  | _, _, _, _, .Apply q₁ q₂ => q₁.hygienic ∧ q₂.hygienic
  | _, _, _, _, .Sum q₁ q₂ => q₁.hygienic ∧ q₂.hygienic
  | _, _, _, _, .Dedup q => q.hygienic
  | _, _, _, _, .Diff q₁ q₂ => q₁.hygienic ∧ q₂.hygienic
  | _, _, _, _, .Explode _ _ q => q.hygienic
  | _, _, _, _, .Mu s q₀ q₁ =>
      q₀.noMention s ∧ q₁.noMention s ∧ q₀.hygienic ∧ q₁.hygienic
  | _, _, _, _, .MuSet s q₀ q₁ =>
      q₀.noMention s ∧ q₁.noMention s ∧ q₀.hygienic ∧ q₁.hygienic
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.hygienic
  | _, _, _, _, .GammaScalar _ _ q _ => q.hygienic
  | _, _, _, _, .GammaNest _ _ _ _ q => q.hygienic
  | _, _, _, _, .ProvSum _ _ _ q => q.hygienic
  | _, _, _, _, .Retag _ q => q.hygienic
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.hygienic
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.hygienic
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.hygienic

omit [ValueType T] in
/-- A recursion-free query is hygienic, there being nothing to bind. -/
theorem AggQueryIn.hygienic_of_usesOnly {S : Set OpKind}
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.hygienic := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun hq => ih hq.2
  | Sel φ q _ ih => exact fun hq => ih hq.2
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Dedup q ih => exact fun hq => ih hq.2
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Explode k hk q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hmb
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hms
  | Gamma is ts fs q keep ord ih => exact fun hq => ih hq.2
  | GammaScalar ts fs q ord ih => exact fun hq => ih hq.2
  | GammaNest is his p f q ih => exact fun hq => ih hq.2
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Retag hk q ih => exact fun hq => ih hq
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih => exact fun hq => ih hq.2
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq => ih hq.2

omit [ValueType T] in
/-- A query over a schema not declaring `s` does not name `s`: the one
place a bound name is read is the hole, which is no mention. -/
theorem AggQueryIn.noMention_of_overSchema_none {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (sch : Schema), sch s = none → q.overSchema sch → q.noMention s := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro sch hs h hc
    have h' : sch s' = some n := h
    rw [hc, hs] at h'
    exact Option.some_ne_none n h'.symm
  | Hole n s' => exact fun _ _ _ => trivial
  | Empty => exact fun _ _ _ => trivial
  | Proj ps q ih => exact fun sch hs h => ih sch hs h
  | Sel φ q _ ih => exact fun sch hs h => ih sch hs h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun sch hs h => ⟨ih₁ sch hs h.1, ih₂ sch hs h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun sch hs h => ⟨ih₁ sch hs h.1, ih₂ sch hs h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun sch hs h => ⟨ih₁ sch hs h.1, ih₂ sch hs h.2⟩
  | Dedup q ih => exact fun sch hs h => ih sch hs h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun sch hs h => ⟨ih₁ sch hs h.1, ih₂ sch hs h.2⟩
  | Explode k hk q ih => exact fun sch hs h => ih sch hs h
  | Retag hk q ih => exact fun sch hs h => ih sch hs h
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    intro sch hs h
    refine ⟨ih₀ sch hs h.2.1, ?_⟩
    by_cases hss : s = s'
    · subst hss; exact h.2.2.1
    · refine ih₁ (sch.update s' _) ?_ h.2.2.2
      show (if s = s' then _ else sch s) = none
      rw [ite_eq_right hss]; exact hs
  | MuSet s' q₀ q₁ ih₀ ih₁ =>
    intro sch hs h
    refine ⟨ih₀ sch hs h.2.1, ?_⟩
    by_cases hss : s = s'
    · subst hss; exact h.2.2.1
    · refine ih₁ (sch.update s' _) ?_ h.2.2.2
      show (if s = s' then _ else sch s) = none
      rw [ite_eq_right hss]; exact hs
  | Gamma is ts fs q keep ord ih => exact fun sch hs h => ih sch hs h
  | GammaScalar ts fs q ord ih => exact fun sch hs h => ih sch hs h
  | GammaNest is his p f q ih => exact fun sch hs h => ih sch hs h
  | ProvSum is his t q ih => exact fun sch hs h => ih sch hs h
  | GammaTok is his ts fs a q keep ih => exact fun sch hs h => ih sch hs h
  | Win P O o w t f q hrr dist keep ih => exact fun sch hs h => ih sch hs h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun sch hs h => ih sch hs h

omit [ValueType T] in
/-- **A query over a schema is hygienic**: a recursion binds a name the
schema does not declare, so neither its base nor its term names it. -/
theorem AggQueryIn.hygienic_of_overSchema :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (sch : Schema), q.overSchema sch → q.hygienic := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ _ => trivial
  | Hole n s => exact fun _ _ => trivial
  | Empty => exact fun _ _ => trivial
  | Proj ps q ih => exact fun sch h => ih sch h
  | Sel φ q _ ih => exact fun sch h => ih sch h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun sch h => ⟨ih₁ sch h.1, ih₂ sch h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun sch h => ⟨ih₁ sch h.1, ih₂ sch h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun sch h => ⟨ih₁ sch h.1, ih₂ sch h.2⟩
  | Dedup q ih => exact fun sch h => ih sch h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun sch h => ⟨ih₁ sch h.1, ih₂ sch h.2⟩
  | Explode k hk q ih => exact fun sch h => ih sch h
  | Retag hk q ih => exact fun sch h => ih sch h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact fun sch h => ⟨AggQueryIn.noMention_of_overSchema_none q₀ sch h.1 h.2.1, h.2.2.1,
      ih₀ sch h.2.1, ih₁ _ h.2.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun sch h => ⟨AggQueryIn.noMention_of_overSchema_none q₀ sch h.1 h.2.1, h.2.2.1,
      ih₀ sch h.2.1, ih₁ _ h.2.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun sch h => ih sch h
  | GammaScalar ts fs q ord ih => exact fun sch h => ih sch h
  | GammaNest is his p f q ih => exact fun sch h => ih sch h
  | ProvSum is his t q ih => exact fun sch h => ih sch h
  | GammaTok is his ts fs a q keep ih => exact fun sch h => ih sch h
  | Win P O o w t f q hrr dist keep ih => exact fun sch h => ih sch h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun sch h => ih sch h

/-! ## The constants a query may put in its result -/

/-- The constants of a term lie in `V`. -/
def TermIn.constsIn {c k : ℕ} (V : Finset T) : TermIn T c k → Prop
  | .const a => a ∈ V
  | .outer _ => True
  | .index _ => True
  | .add t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V
  | .sub t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V
  | .mul t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      t₁.constsIn V ∧ t₂.constsIn V ∧ t₃.constsIn V ∧ t₄.constsIn V
  | .coalesce t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V

/-- And of a kind-indexed term. -/
def TermGIn.constsIn {c k : ℕ} {κ : Fin k → ColKind} (V : Finset T) :
    TermGIn T c κ → Prop
  | .const a => a ∈ V
  | .outer _ => True
  | .index _ _ => True
  | .provIndex _ _ => True
  | .cmpAgg _ _ _ t => t.constsIn V
  | .chiGate _ t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V
  | .add t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V
  | .sub t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V
  | .mul t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      t₁.constsIn V ∧ t₂.constsIn V ∧ t₃.constsIn V ∧ t₄.constsIn V
  | .coalesce t₁ t₂ => t₁.constsIn V ∧ t₂.constsIn V

/-- And of an output column. -/
def ProjColIn.constsIn {c k : ℕ} {κ : Fin k → ColKind} (V : Finset T) :
    ProjColIn T c κ → Prop
  | .term t => t.constsIn V
  | .token _ _ => True
  | .aggTerm _ _ _ => True
  | .aggTermOf _ _ t => t.constsIn V
  | .provTerm t => t.constsIn V

/-- **A term of the minimal signature reads a value it was given.** -/
theorem TermIn.eval_mem_of_noFun {c k : ℕ} {V : Finset T} (t : TermIn T c k)
    (h : t.noFun = true) (hc : t.constsIn V) (u : Tuple T k)
    (hu : ∀ j, u j ∈ V) (γ : Fin c → T) (hγ : ∀ j, γ j ∈ V) :
    t.eval u γ ∈ V := by
  cases t with
  | const a => exact hc
  | outer j => exact hγ j
  | index j => exact hu j
  | add _ _ => exact absurd h (by simp [TermIn.noFun])
  | sub _ _ => exact absurd h (by simp [TermIn.noFun])
  | mul _ _ => exact absurd h (by simp [TermIn.noFun])
  | caseWhen _ _ _ _ _ => exact absurd h (by simp [TermIn.noFun])
  | coalesce _ _ => exact absurd h (by simp [TermIn.noFun])

/-- The same for a kind-indexed term. -/
theorem TermGIn.evalPlain_mem_of_noFun {c k : ℕ} {κ : Fin k → ColKind}
    {V : Finset T} (t : TermGIn T c κ) (h : t.noFun = true)
    (hc : t.constsIn V) (u : Tuple T k) (hu : ∀ j, u j ∈ V) (γ : Fin c → T)
    (hγ : ∀ j, γ j ∈ V) : t.evalPlain u γ ∈ V := by
  cases t with
  | const a => exact hc
  | outer j => exact hγ j
  | index j hj => exact hu j
  | provIndex j hj => exact hu j
  | cmpAgg _ _ _ _ => exact absurd h (by simp [TermGIn.noFun])
  | chiGate _ _ _ => exact absurd h (by simp [TermGIn.noFun])
  | add _ _ => exact absurd h (by simp [TermGIn.noFun])
  | sub _ _ => exact absurd h (by simp [TermGIn.noFun])
  | mul _ _ => exact absurd h (by simp [TermGIn.noFun])
  | caseWhen _ _ _ _ _ => exact absurd h (by simp [TermGIn.noFun])
  | coalesce _ _ => exact absurd h (by simp [TermGIn.noFun])

/-- **And an output column of the minimal signature.** A column read over
an aggregate column is a term of one variable there, so it is that
column or a constant. -/
theorem ProjColIn.evalPlain_mem_of_noFun {c k : ℕ} {κ : Fin k → ColKind}
    {V : Finset T} (p : ProjColIn T c κ) (h : p.noFun = true)
    (hc : p.constsIn V) (u : Tuple T k) (hu : ∀ j, u j ∈ V) (γ : Fin c → T)
    (hγ : ∀ j, γ j ∈ V) : p.evalPlain u γ ∈ V := by
  cases p with
  | term t => exact t.evalPlain_mem_of_noFun h hc u hu γ hγ
  | token j hj => exact hu j
  | aggTerm j hj gf => exact absurd h (by simp [ProjColIn.noFun])
  | aggTermOf j hj t =>
    show t.unary (u j) ∈ V
    rw [TermIn.unary]
    exact t.eval_mem_of_noFun h hc (fun i => i.elim0) (fun i => i.elim0)
      (fun _ => u j) (fun _ => hu j)
  | provTerm t => exact t.evalPlain_mem_of_noFun h hc u hu γ hγ

/-- **The constants the query may put in its result lie in `V`.** Only a
projection's columns are asked: the terms an aggregate reads feed a
count, whose value is a function of *how many* values it reads and not
of which, so their constants do not reach the result. -/
def AggQueryIn.constsIn (V : Finset T) : {c n : ℕ} →
    {κ : Fin n → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj ps q =>
      (∀ j, (ps j).constsIn V) ∧ q.constsIn V
  | _, _, _, _, .Sel _ q _ => q.constsIn V
  | _, _, _, _, .Prod q₁ q₂ => q₁.constsIn V ∧ q₂.constsIn V
  | _, _, _, _, .Apply q₁ q₂ => q₁.constsIn V ∧ q₂.constsIn V
  | _, _, _, _, .Sum q₁ q₂ => q₁.constsIn V ∧ q₂.constsIn V
  | _, _, _, _, .Dedup q => q.constsIn V
  | _, _, _, _, .Diff q₁ q₂ => q₁.constsIn V ∧ q₂.constsIn V
  | _, _, _, _, .Explode _ _ q => q.constsIn V
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.constsIn V ∧ q₁.constsIn V
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.constsIn V ∧ q₁.constsIn V
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.constsIn V
  | _, _, _, _, .GammaScalar _ _ q _ => q.constsIn V
  | _, _, _, _, .GammaNest _ _ _ _ q => q.constsIn V
  | _, _, _, _, .ProvSum _ _ _ q => q.constsIn V
  | _, _, _, _, .Retag _ q => q.constsIn V
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.constsIn V
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.constsIn V
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.constsIn V

/-- The constants a term names, as a set. -/
def TermIn.consts {c k : ℕ} : TermIn T c k → Finset T
  | .const a => {a}
  | .outer _ => ∅
  | .index _ => ∅
  | .add t₁ t₂ => Union.union t₁.consts t₂.consts
  | .sub t₁ t₂ => Union.union t₁.consts t₂.consts
  | .mul t₁ t₂ => Union.union t₁.consts t₂.consts
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      Union.union (Union.union (Union.union t₁.consts t₂.consts) t₃.consts)
        t₄.consts
  | .coalesce t₁ t₂ => Union.union t₁.consts t₂.consts

/-- And a kind-indexed term's. -/
def TermGIn.consts {c k : ℕ} {κ : Fin k → ColKind} : TermGIn T c κ → Finset T
  | .const a => {a}
  | .outer _ => ∅
  | .index _ _ => ∅
  | .provIndex _ _ => ∅
  | .cmpAgg _ _ _ t => t.consts
  | .chiGate _ t₁ t₂ => Union.union t₁.consts t₂.consts
  | .add t₁ t₂ => Union.union t₁.consts t₂.consts
  | .sub t₁ t₂ => Union.union t₁.consts t₂.consts
  | .mul t₁ t₂ => Union.union t₁.consts t₂.consts
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      Union.union (Union.union (Union.union t₁.consts t₂.consts) t₃.consts)
        t₄.consts
  | .coalesce t₁ t₂ => Union.union t₁.consts t₂.consts

/-- And an output column's. -/
def ProjColIn.consts {c k : ℕ} {κ : Fin k → ColKind} :
    ProjColIn T c κ → Finset T
  | .term t => t.consts
  | .token _ _ => ∅
  | .aggTerm _ _ _ => ∅
  | .aggTermOf _ _ t => t.consts
  | .provTerm t => t.consts

/-- A term's constants lie in any set holding `consts`. -/
theorem TermIn.constsIn_of_subset {c k : ℕ} {V : Finset T} :
    ∀ (t : TermIn T c k), t.consts ⊆ V → t.constsIn V
  | .const a, h => h (Finset.mem_singleton_self a)
  | .outer _, _ => trivial
  | .index _, _ => trivial
  | .add t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .sub t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .mul t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .caseWhen _ t₁ t₂ t₃ t₄, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left
          (Finset.union_subset_left (Finset.union_subset_left h))),
        t₂.constsIn_of_subset (Finset.union_subset_right
          (Finset.union_subset_left (Finset.union_subset_left h))),
        t₃.constsIn_of_subset (Finset.union_subset_right
          (Finset.union_subset_left h)),
        t₄.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .coalesce t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩

theorem TermGIn.constsIn_of_subset {c k : ℕ} {κ : Fin k → ColKind}
    {V : Finset T} :
    ∀ (t : TermGIn T c κ), t.consts ⊆ V → t.constsIn V
  | .const a, h => h (Finset.mem_singleton_self a)
  | .outer _, _ => trivial
  | .index _ _, _ => trivial
  | .provIndex _ _, _ => trivial
  | .cmpAgg _ _ _ t, h => t.constsIn_of_subset h
  | .chiGate _ t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .add t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .sub t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .mul t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .caseWhen _ t₁ t₂ t₃ t₄, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left
          (Finset.union_subset_left (Finset.union_subset_left h))),
        t₂.constsIn_of_subset (Finset.union_subset_right
          (Finset.union_subset_left (Finset.union_subset_left h))),
        t₃.constsIn_of_subset (Finset.union_subset_right
          (Finset.union_subset_left h)),
        t₄.constsIn_of_subset (Finset.union_subset_right h)⟩
  | .coalesce t₁ t₂, h =>
      ⟨t₁.constsIn_of_subset (Finset.union_subset_left h),
        t₂.constsIn_of_subset (Finset.union_subset_right h)⟩

theorem ProjColIn.constsIn_of_subset {c k : ℕ} {κ : Fin k → ColKind}
    {V : Finset T} :
    ∀ (p : ProjColIn T c κ), p.consts ⊆ V → p.constsIn V
  | .term t, h => t.constsIn_of_subset h
  | .token _ _, _ => trivial
  | .aggTerm _ _ _, _ => trivial
  | .aggTermOf _ _ t, h => t.constsIn_of_subset h
  | .provTerm t, h => t.constsIn_of_subset h

/-- **The constants a query names in its projections**, as a set: what
the value of a row of a recursion-free, function-free query can draw on
beside the instance and the context. -/
def AggQueryIn.consts : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Finset T
  | _, _, _, _, .Rel _ _ => ∅
  | _, _, _, _, .Hole _ _ => ∅
  | _, _, _, _, .Empty => ∅
  | _, _, _, _, .Proj ps q => Union.union (Finset.univ.biUnion fun j => (ps j).consts) q.consts
  | _, _, _, _, .Sel _ q _ => q.consts
  | _, _, _, _, .Prod q₁ q₂ => Union.union q₁.consts q₂.consts
  | _, _, _, _, .Apply q₁ q₂ => Union.union q₁.consts q₂.consts
  | _, _, _, _, .Sum q₁ q₂ => Union.union q₁.consts q₂.consts
  | _, _, _, _, .Dedup q => q.consts
  | _, _, _, _, .Diff q₁ q₂ => Union.union q₁.consts q₂.consts
  | _, _, _, _, .Explode _ _ q => q.consts
  | _, _, _, _, .Mu _ q₀ q₁ => Union.union q₀.consts q₁.consts
  | _, _, _, _, .MuSet _ q₀ q₁ => Union.union q₀.consts q₁.consts
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.consts
  | _, _, _, _, .GammaScalar _ _ q _ => q.consts
  | _, _, _, _, .GammaNest _ _ _ _ q => q.consts
  | _, _, _, _, .ProvSum _ _ _ q => q.consts
  | _, _, _, _, .Retag _ q => q.consts
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.consts
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.consts
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.consts

/-! ## Where a query is defined

A recursion means the value its rounds settle at and nothing where they
do not, so a query with a recursion is a partial function of the
instance. `SettlesAt` says the evaluation at one instance runs only
recursions that settle: at `Mu`, the round function vanishes on the
empty round and the rounds from the base reach an empty one; at `MuSet`,
the iterations from `0` repeat; and the subqueries settle at the
instances the evaluation reads them at – a body at every round, an
apply's right side at every row of its left. This is
`AggQueryIn.recSettles` taken instance by instance and in the plain
semantics: that predicate asks every instance, which a nested recursion
needs, but a result about a *class* of queries has to speak of the
instances where a query is defined, since a recursion that is total is
the exception (the body reads the recursive name under a product with an
instance relation, and a cycle in that relation keeps the rounds going).
A query with no recursion settles everywhere. -/

/-- **The recursions settle at an instance.** -/
def AggQueryIn.SettlesAt : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Database T → (Fin c → T) → Prop
  | _, _, _, _, .Rel _ _, _, _ => True
  | _, _, _, _, .Hole _ _, _, _ => True
  | _, _, _, _, .Empty, _, _ => True
  | _, _, _, _, .Proj _ q, D, γ => q.SettlesAt D γ
  | _, _, _, _, .Sel _ q _, D, γ => q.SettlesAt D γ
  | _, _, _, _, .Prod q₁ q₂, D, γ => q₁.SettlesAt D γ ∧ q₂.SettlesAt D γ
  | _, _, _, _, @AggQueryIn.Apply _ _ n₁ _ _ _ q₁ q₂, D, γ =>
      q₁.SettlesAt D γ
        ∧ ∀ u : Tuple T n₁, Multiset.Mem (q₁.evaluatePlain D γ) u →
            q₂.SettlesAt D (Fin.append u γ)
  | _, _, _, _, .Sum q₁ q₂, D, γ => q₁.SettlesAt D γ ∧ q₂.SettlesAt D γ
  | _, _, _, _, .Dedup q, D, γ => q.SettlesAt D γ
  | _, _, _, _, .Diff q₁ q₂, D, γ => q₁.SettlesAt D γ ∧ q₂.SettlesAt D γ
  | _, _, _, _, .Explode _ _ q, D, γ => q.SettlesAt D γ
  | _, _, _, _, .Retag _ q, D, γ => q.SettlesAt D γ
  | _, n, _, _, .Mu s q₀ q₁, D, γ =>
      q₀.SettlesAt D γ
        ∧ q₁.evaluatePlain (D.assign s (0 : Relation T n)) γ = 0
        ∧ MuSettles (fun X => q₁.evaluatePlain (D.assign s X) γ)
            (q₀.evaluatePlain D γ)
        ∧ ∀ k : ℕ, q₁.SettlesAt
            (D.assign s ((fun X => q₁.evaluatePlain (D.assign s X) γ)^[k]
              (q₀.evaluatePlain D γ))) γ
  | _, _, _, _, .MuSet s q₀ q₁, D, γ =>
      q₀.SettlesAt D γ
        ∧ MuSetSettles (fun X => (q₀.evaluatePlain D γ
            + q₁.evaluatePlain (D.assign s X) γ).dedup)
        ∧ ∀ k : ℕ, q₁.SettlesAt (D.assign s (muIter (fun X =>
            (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup) k)) γ
  | _, _, _, _, .Gamma _ _ _ q _ _, D, γ => q.SettlesAt D γ
  | _, _, _, _, .GammaScalar _ _ q _, D, γ => q.SettlesAt D γ
  | _, _, _, _, .GammaNest _ _ _ _ q, D, γ => q.SettlesAt D γ
  | _, _, _, _, .GammaTok _ _ _ _ _ q _, D, γ => q.SettlesAt D γ
  | _, _, _, _, .ProvSum _ _ _ q, D, γ => q.SettlesAt D γ
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _, D, γ => q.SettlesAt D γ
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _, D, γ => q.SettlesAt D γ

/-- **The partial semantics**: the plain reading where the query is
defined, and nothing where it is not. This is what a query of the whole
algebra denotes; `evaluatePlain` is its total extension by a junk value
where a recursion never settles. -/
noncomputable def AggQueryIn.evaluatePlain? {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    Option (Relation T n) :=
  open Classical in if q.SettlesAt D γ then some (q.evaluatePlain D γ) else none

theorem AggQueryIn.evaluatePlain?_eq_some_iff {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T)
    (r : Relation T n) :
    q.evaluatePlain? D γ = some r ↔ q.SettlesAt D γ ∧ q.evaluatePlain D γ = r := by
  unfold AggQueryIn.evaluatePlain?
  split
  · next h => exact ⟨fun he => ⟨h, Option.some.inj he⟩, fun he => congrArg some he.2⟩
  · next h => exact ⟨fun he => absurd he (by simp), fun he => absurd he.1 h⟩

theorem AggQueryIn.evaluatePlain?_eq_none_iff {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    q.evaluatePlain? D γ = none ↔ ¬ q.SettlesAt D γ := by
  unfold AggQueryIn.evaluatePlain?
  split
  · next h => exact ⟨fun he => absurd he (by simp), fun hn => absurd h hn⟩
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩

/-- **`q'` extends `q` as a partial function**: wherever `q` is defined,
`q'` is defined with the same value. This is what a rewriting of the
whole algebra establishes; `extends_iff_settles` spells it out through
the evaluator and the settling. -/
def AggQueryIn.Extends {c n : ℕ} {κ κ' : Fin n → ColKind} {l l' : List (String × ℕ)}
    (q' : AggQueryIn T c n κ' l') (q : AggQueryIn T c n κ l) : Prop :=
  ∀ (D : Database T) (γ : Fin c → T) (r : Relation T n),
    q.evaluatePlain? D γ = some r → q'.evaluatePlain? D γ = some r

theorem AggQueryIn.extends_iff_settles {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l l' : List (String × ℕ)} (q' : AggQueryIn T c n κ' l') (q : AggQueryIn T c n κ l) :
    q'.Extends q ↔ ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
      q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  constructor
  · intro h D γ hs
    have := (AggQueryIn.evaluatePlain?_eq_some_iff q' D γ _).mp
      (h D γ _ ((AggQueryIn.evaluatePlain?_eq_some_iff q D γ _).mpr ⟨hs, rfl⟩))
    exact ⟨this.1, this.2.symm⟩
  · intro h D γ r hr
    obtain ⟨hs, he⟩ := (AggQueryIn.evaluatePlain?_eq_some_iff q D γ r).mp hr
    exact (AggQueryIn.evaluatePlain?_eq_some_iff q' D γ r).mpr ⟨(h D γ hs).1, (h D γ hs).2 ▸ he⟩

theorem AggQueryIn.Extends.settles {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l l' : List (String × ℕ)} {q' : AggQueryIn T c n κ' l'} {q : AggQueryIn T c n κ l}
    (h : q'.Extends q) : ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
      q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ :=
  (AggQueryIn.extends_iff_settles q' q).mp h

theorem AggQueryIn.Extends.of_settles {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l l' : List (String × ℕ)} {q' : AggQueryIn T c n κ' l'} {q : AggQueryIn T c n κ l}
    (h : ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
      q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ) : q'.Extends q :=
  (AggQueryIn.extends_iff_settles q' q).mpr h

/-- **A query with no recursion settles everywhere.** -/
theorem AggQueryIn.settlesAt_of_usesOnly {S : Set OpKind}
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ _ _ => trivial
  | Hole n s => exact fun _ _ _ => trivial
  | Empty => exact fun _ _ _ => trivial
  | Proj ps q ih => exact fun hq D γ => ih hq.2 D γ
  | Sel φ q _ ih => exact fun hq D γ => ih hq.2 D γ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq D γ => ⟨ih₁ hq.2.1 D γ, ih₂ hq.2.2 D γ⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun hq D γ => ⟨ih₁ hq.2.1 D γ, fun u _ => ih₂ hq.2.2 D _⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq D γ => ⟨ih₁ hq.2.1 D γ, ih₂ hq.2.2 D γ⟩
  | Dedup q ih => exact fun hq D γ => ih hq.2 D γ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq D γ => ⟨ih₁ hq.2.1 D γ, ih₂ hq.2.2 D γ⟩
  | Explode k hk q ih => exact fun hq D γ => ih hq D γ
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hmb
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hms
  | Gamma is ts fs q keep ord ih => exact fun hq D γ => ih hq.2 D γ
  | GammaScalar ts fs q ord ih => exact fun hq D γ => ih hq.2 D γ
  | GammaNest is his p f q ih => exact fun hq D γ => ih hq.2 D γ
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Retag hk q ih => exact fun hq D γ => ih hq D γ
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih => exact fun hq D γ => ih hq.2 D γ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq D γ => ih hq.2 D γ

/-- **A query naming nothing of a recursion settles alike on two instances
agreeing away from its name**: the rounds it evaluates are the same, by
`evaluatePlain_congr_of_noMention`. -/
theorem AggQueryIn.settlesAt_of_noMention {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention s → ∀ {D D' : Database T}, Database.AgreeOff s l D D' →
      ∀ γ : Fin c → T, q.SettlesAt D γ → q.SettlesAt D' γ := by
  have hassign : ∀ {D D' : Database T} (s' : String) {m : ℕ} (Y : Relation T m),
      Database.AgreeOff s [] D D' →
      Database.AgreeOff s [(s', m)] (D.assign s' Y) (D'.assign s' Y) :=
    fun s' _ Y h => Database.AgreeOff.assign s' Y h
  have hL : ∀ {l₁ l₂ : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s (l₁ ++ l₂) D D' → Database.AgreeOff s l₁ D D' :=
    fun h => h.mono (fun _ hp => List.mem_append_left _ hp)
  have hR : ∀ {l₁ l₂ : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s (l₁ ++ l₂) D D' → Database.AgreeOff s l₂ D D' :=
    fun h => h.mono (fun _ hp => List.mem_append_right _ hp)
  have hN : ∀ {l : List (String × ℕ)} {D D' : Database T},
      Database.AgreeOff s l D D' → Database.AgreeOff s [] D D' :=
    fun h => h.mono (fun _ hp => absurd hp List.not_mem_nil)
  intro c n κ l q
  induction q with
  | Rel n s' => intro _ D D' _ _ _; exact trivial
  | Hole n s' => intro _ D D' _ _ _; exact trivial
  | Empty => intro _ D D' _ _ _; exact trivial
  | Proj ps q ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | Sel φ q _ ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ hs; exact ⟨ih₁ hq.1 (hL h) γ hs.1, ih₂ hq.2 (hR h) γ hs.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ hs
    refine ⟨ih₁ hq.1 h γ hs.1, fun u hu => ih₂ hq.2 (hN h) _ (hs.2 u ?_)⟩
    rw [AggQueryIn.evaluatePlain_congr_of_noMention q₁ hq.1 h γ]
    exact hu
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ hs; exact ⟨ih₁ hq.1 (hL h) γ hs.1, ih₂ hq.2 (hR h) γ hs.2⟩
  | Dedup q ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq D D' h γ hs; exact ⟨ih₁ hq.1 h γ hs.1, ih₂ hq.2 h γ hs.2⟩
  | Explode k hk q ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | Retag hk q ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    rename_i c' n'
    intro hq D D' h γ hs
    have hstep : (fun Y : Multiset (Tuple T n') => q₁.evaluatePlain (D'.assign s' Y) γ)
        = (fun Y : Multiset (Tuple T n') => q₁.evaluatePlain (D.assign s' Y) γ) :=
      funext fun Y =>
        (AggQueryIn.evaluatePlain_congr_of_noMention q₁ hq.2 (hassign s' Y h) γ).symm
    have hM : q₀.evaluatePlain D' γ = q₀.evaluatePlain D γ :=
      (AggQueryIn.evaluatePlain_congr_of_noMention q₀ hq.1 h γ).symm
    refine ⟨ih₀ hq.1 h γ hs.1, ?_, ?_, fun k => ?_⟩
    · rw [← AggQueryIn.evaluatePlain_congr_of_noMention q₁ hq.2 (hassign s' _ h) γ]
      exact hs.2.1
    · show MuSettles (fun Y : Multiset (Tuple T n') =>
        q₁.evaluatePlain (D'.assign s' Y) γ) (q₀.evaluatePlain D' γ)
      rw [hstep, hM]
      exact hs.2.2.1
    · show q₁.SettlesAt (D'.assign s' ((fun Y : Multiset (Tuple T n') =>
        q₁.evaluatePlain (D'.assign s' Y) γ)^[k] (q₀.evaluatePlain D' γ))) γ
      rw [hstep, hM]
      exact ih₁ hq.2 (hassign s' _ h) γ (hs.2.2.2 k)
  | MuSet s' q₀ q₁ ih₀ ih₁ =>
    rename_i c' n'
    intro hq D D' h γ hs
    have hstep : (fun Y : Multiset (Tuple T n') => (q₀.evaluatePlain D' γ
          + q₁.evaluatePlain (D'.assign s' Y) γ).dedup)
        = (fun Y : Multiset (Tuple T n') => (q₀.evaluatePlain D γ
          + q₁.evaluatePlain (D.assign s' Y) γ).dedup) :=
      funext fun Y => by
        rw [AggQueryIn.evaluatePlain_congr_of_noMention q₀ hq.1 h γ,
          AggQueryIn.evaluatePlain_congr_of_noMention q₁ hq.2 (hassign s' Y h) γ]
    refine ⟨ih₀ hq.1 h γ hs.1, ?_, fun k => ?_⟩
    · show MuSetSettles (fun Y : Multiset (Tuple T n') =>
        (q₀.evaluatePlain D' γ + q₁.evaluatePlain (D'.assign s' Y) γ).dedup)
      rw [hstep]
      exact hs.2.1
    · show q₁.SettlesAt (D'.assign s' (muIter (fun Y : Multiset (Tuple T n') =>
          (q₀.evaluatePlain D' γ + q₁.evaluatePlain (D'.assign s' Y) γ).dedup) k)) γ
      rw [hstep]
      exact ih₁ hq.2 (hassign s' _ h) γ (hs.2.2 k)
  | Gamma is ts fs q keep ord ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | GammaScalar ts fs q ord ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | GammaNest is his p f q ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | ProvSum is his t q ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | GammaTok is his ts fs a q keep ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | Win P O o w t f q hrr dist keep ih => intro hq D D' h γ hs; exact ih hq h γ hs
  | WinExpr P O o ws ts fs g q keeps ih => intro hq D D' h γ hs; exact ih hq h γ hs

/-- **And so it settles at an instance exactly when it settles at that
instance with the recursion's relation bound.** -/
theorem AggQueryIn.settlesAt_assign_of_noMention {s : String} {m : ℕ}
    (X : Relation T m) {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (hq : q.noMention s) (D : Database T)
    (γ : Fin c → T) (h : q.SettlesAt (D.assign s X) γ) : q.SettlesAt D γ :=
  AggQueryIn.settlesAt_of_noMention q hq
    (fun _k s' hs' =>
      Database.find_assign_of_ne s s' X D (fun hc => (hs'.resolve_right List.not_mem_nil) hc.2))
    γ h

/-! ### What the two fixpoints are when their rounds vanish or do not -/

/-- The sum of the rounds from the empty relation is empty when a round
from it is. -/
theorem muSum_zero_of_step_zero {α : Type}
    {step : Multiset α → Multiset α} (h0 : step 0 = 0) :
    ∀ b : ℕ, muSum step b 0 = 0 := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
    show (0 : Multiset α) + muSum step b (step 0) = 0
    rw [h0, ih, add_zero]

/-- So is the value the duplicate-preserving recursion settles at. -/
theorem muSumFix_zero_of_step_zero {α : Type}
    {step : Multiset α → Multiset α} (h0 : step 0 = 0) :
    muSumFix step 0 = 0 :=
  muSum_zero_of_step_zero h0 _

/-- A set recursion whose first round is empty settles there. -/
theorem muFix_zero_of_step_zero {α : Type}
    {step : Multiset α → Multiset α} (h0 : step 0 = 0) : muFix step = 0 := by
  have hmem : (0 : ℕ) ∈ {j | step^[j + 1] 0 = step^[j] 0} := by
    show step^[1] 0 = step^[0] 0
    simpa using h0
  rw [muFix, muFixIdx, Nat.le_antisymm (Nat.sInf_le hmem) (Nat.zero_le _)]
  rfl

/-- The sum of the rounds holds the base. -/
theorem card_le_card_muSum {α : Type} (step : Multiset α → Multiset α)
    (b : ℕ) (M : Multiset α) :
    Multiset.card M ≤ Multiset.card (muSum step b M) := by
  cases b with
  | zero => exact le_refl _
  | succ b =>
    show Multiset.card M ≤ Multiset.card (M + muSum step b (step M))
    rw [Multiset.card_add]
    exact Nat.le_add_right _ _

/-- **A duplicate-preserving recursion from a non-empty base is
non-empty**, settling or not: the base is one of the summands. -/
theorem muSumFix_ne_zero {α : Type} (step : Multiset α → Multiset α)
    {M : Multiset α} (hM : M ≠ 0) : muSumFix step M ≠ 0 := by
  intro h
  have hc := card_le_card_muSum step (muRounds step M) M
  rw [muSumFix] at h
  rw [h, Multiset.card_zero, Nat.le_zero, Multiset.card_eq_zero] at hc
  exact hM hc

/-- **A set recursion that settles, whose first round is non-empty and
whose rounds keep a non-empty round non-empty, settles at a non-empty
value.** -/
theorem muFix_ne_zero_of_settles {α : Type} {step : Multiset α → Multiset α}
    (hs : MuSetSettles step) (h0 : step 0 ≠ 0)
    (hstep : ∀ k, muIter step k ≠ 0 → step (muIter step k) ≠ 0) :
    muFix step ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hfix : step (muIter step j) = muIter step j := by
    rw [muIter_eq_iterate]
    rw [Function.iterate_succ_apply'] at hj
    exact hj
  rw [muFix_eq_of_fix hfix]
  have hpos : ∀ k, muIter step (k + 1) ≠ 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact hstep (k + 1) ih
  cases j with
  | zero => exact absurd hj h0
  | succ j => exact hpos j

/-! ## Selection and difference: the two operators that can lose a row

Without `σ` and `−`, a query is either empty on every instance of its
schema, or non-empty on every instance of it whose relations are all
non-empty: nothing else can turn rows away. The disjunction is uniform in
the outer context, which is what the apply needs – without a selection
the outer row enters its right side only through terms, and a term
decides no row's presence.

The two recursions keep the invariant, under the one hypothesis that
makes them mean anything (`SettlesAt`), but not by an induction on the
disjunction alone: whether `μ^∪R.(q₀, q₁)` is empty depends on whether
`q₁` is empty at the instance binding `R` to the **empty** relation, which
is not a full instance of the body's schema, so the body's disjunction
says nothing about it. What the induction carries instead is the
disjunction relative to a set `E` of names forced empty
(`AggQueryIn.NonzeroOn`): `q` is non-empty on every instance that is full
off `E`, or empty on every instance that is empty on `E`. At a set
recursion, the first round reads the body with the recursive name in
`E`, and the later rounds read it with the name out of `E` – which the
body's condition at the larger set implies (`NonzeroOn.mono`), the
condition being antitone in `E`. At a bag recursion the base is a
summand of the answer, so the base decides; the rounds from an empty base
vanish because the round function vanishes on the empty round, which is
what `SettlesAt` asks there. -/

/-- An instance of the schema no relation of which is empty. -/
def Database.Full (sch : Schema) (D : Database T) : Prop :=
  ∀ (s : String) (k : ℕ), sch s = some k → ∃ r : Relation T k,
    D.find k s = some r ∧ r ≠ 0

omit [ValueType T] in
/-- A full instance conforms. -/
theorem Database.Full.conforms {sch : Schema} {D : Database T}
    (h : Database.Full sch D) : Database.Conforms sch D :=
  fun s k hk => let ⟨r, hr, _⟩ := h s k hk; ⟨r, hr⟩

/-- **An instance full off a set of names**: every relation the schema
declares under a name outside `E` is bound and non-empty. `Full` is the
case `E = ∅`. -/
def Database.FullOff (sch : Schema) (E : Set String) (D : Database T) :
    Prop :=
  ∀ (s : String) (k : ℕ), sch s = some k → s ∉ E →
    ∃ r : Relation T k, D.find k s = some r ∧ r ≠ 0

/-- **An instance empty on a set of names**: whatever is bound under a
name of `E`, at the arity the schema declares it, is the empty
relation. -/
def Database.EmptyOn (sch : Schema) (E : Set String) (D : Database T) :
    Prop :=
  ∀ (s : String) (k : ℕ) (r : Relation T k), sch s = some k → s ∈ E →
    D.find k s = some r → r = 0

omit [ValueType T] in
theorem Database.Full.fullOff {sch : Schema} {D : Database T}
    (h : Database.Full sch D) (E : Set String) : Database.FullOff sch E D :=
  fun s k hk _ => h s k hk

omit [ValueType T] in
theorem Database.emptyOn_empty (sch : Schema) (D : Database T) :
    Database.EmptyOn sch (∅ : Set String) D :=
  fun _ _ _ _ h _ => h.elim

omit [ValueType T] in
/-- Binding a name the schema does not declare keeps an instance full off
`E`. -/
theorem Database.FullOff.assign_of_none {sch : Schema} {E : Set String}
    {D : Database T} (h : Database.FullOff sch E D) {s : String}
    (hs : sch s = none) {m : ℕ} (X : Relation T m) :
    Database.FullOff sch E (D.assign s X) := by
  intro t k ht hE
  have hne : t ≠ s := fun h' => by rw [h', hs] at ht; cases ht
  rw [Database.find_assign_of_ne s t X D (fun h' => hne h'.2)]
  exact h t k ht hE

omit [ValueType T] in
/-- Binding a name the schema does not declare to a non-empty relation
gives an instance of the extended schema, full off `E` less that name. -/
theorem Database.FullOff.assign_update {sch : Schema} {E : Set String}
    {D : Database T} (h : Database.FullOff sch E D) {s : String}
    (hs : sch s = none) {m : ℕ} {X : Relation T m} (hX : X ≠ 0) :
    Database.FullOff (sch.update s m) (E \ {s}) (D.assign s X) := by
  intro t k ht hE
  by_cases hts : t = s
  · subst hts
    have hk : k = m := by
      simp only [Schema.update_apply, ite_true] at ht
      exact (Option.some.inj ht).symm
    subst hk
    exact ⟨X, Database.find_assign t X D, hX⟩
  · have ht' : sch t = some k := by simpa [Schema.update_apply, hts] using ht
    rw [Database.find_assign_of_ne s t X D (fun h' => hts h'.2)]
    exact h t k ht' (fun hE' => hE ⟨hE', hts⟩)

omit [ValueType T] in
/-- Binding a name to the empty relation gives an instance of the
extended schema, full off `E` with that name. -/
theorem Database.FullOff.assign_update_zero {sch : Schema} {E : Set String}
    {D : Database T} (h : Database.FullOff sch E D) {s : String} (m : ℕ) :
    Database.FullOff (sch.update s m) (insert s E)
      (D.assign s (0 : Relation T m)) := by
  intro t k ht hE
  have hts : t ≠ s := fun h' => hE (h' ▸ Set.mem_insert s E)
  have ht' : sch t = some k := by simpa [Schema.update_apply, hts] using ht
  rw [Database.find_assign_of_ne s t _ D (fun h' => hts h'.2)]
  exact h t k ht' (fun hE' => hE (Set.mem_insert_of_mem s hE'))

omit [ValueType T] in
/-- Binding a name the schema does not declare keeps an instance empty on
`E`. -/
theorem Database.EmptyOn.assign_of_none {sch : Schema} {E : Set String}
    {D : Database T} (h : Database.EmptyOn sch E D) {s : String}
    (hs : sch s = none) {m : ℕ} (X : Relation T m) :
    Database.EmptyOn sch E (D.assign s X) := by
  intro t k r ht hE hf
  have hne : t ≠ s := fun h' => by rw [h', hs] at ht; cases ht
  rw [Database.find_assign_of_ne s t X D (fun h' => hne h'.2)] at hf
  exact h t k r ht hE hf

omit [ValueType T] in
/-- Binding a name to the empty relation gives an instance of the
extended schema, empty on `E` with that name. -/
theorem Database.EmptyOn.assign_update_zero {sch : Schema} {E : Set String}
    {D : Database T} (h : Database.EmptyOn sch E D) {s : String}
    (hs : sch s = none) (m : ℕ) :
    Database.EmptyOn (sch.update s m) (insert s E)
      (D.assign s (0 : Relation T m)) := by
  intro t k r ht hE hf
  by_cases hts : t = s
  · subst hts
    have hk : k = m := by
      simp only [Schema.update_apply, ite_true] at ht
      exact (Option.some.inj ht).symm
    subst hk
    rw [Database.find_assign] at hf
    exact (Option.some.inj hf).symm
  · have ht' : sch t = some k := by simpa [Schema.update_apply, hts] using ht
    rw [Database.find_assign_of_ne s t _ D (fun h' => hts h'.2)] at hf
    exact h t k r ht' ((Set.mem_insert_iff.mp hE).resolve_left hts) hf

/-- **Where a query without `σ` and `−` is non-empty**, read off its
syntax relative to a set `E` of names forced empty: a relation name is
non-empty unless it is in `E`; `∅` never; the one-input operators and
the aggregations inherit, the scalar aggregation always; a product and an
apply need both sides, a union one; a bag recursion is its base; a set
recursion is its base or its body at the instance binding the recursive
name to the empty relation. The two lemmas below say that this is right:
`q.NonzeroOn E` makes `q` non-empty on every instance full off `E`, and
its negation makes `q` empty on every instance empty on `E`. The
selection, the difference and the two operators of the rewritten world
get the value that keeps the lemmas uniform; they are never reached. -/
def AggQueryIn.NonzeroOn (E : Set String) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ s => s ∉ E
  | _, _, _, _, .Hole _ s => s ∉ E
  | _, _, _, _, .Empty => False
  | _, _, _, _, .Proj _ q => q.NonzeroOn E
  | _, _, _, _, .Sel _ q _ => q.NonzeroOn E
  | _, _, _, _, .Prod q₁ q₂ => q₁.NonzeroOn E ∧ q₂.NonzeroOn E
  | _, _, _, _, .Apply q₁ q₂ => q₁.NonzeroOn E ∧ q₂.NonzeroOn E
  | _, _, _, _, .Sum q₁ q₂ => q₁.NonzeroOn E ∨ q₂.NonzeroOn E
  | _, _, _, _, .Dedup q => q.NonzeroOn E
  | _, _, _, _, .Diff q₁ _ => q₁.NonzeroOn E
  | _, _, _, _, .Explode _ _ q => q.NonzeroOn E
  | _, _, _, _, .Retag _ q => q.NonzeroOn E
  | _, _, _, _, .Mu _ q₀ _ => q₀.NonzeroOn E
  | _, _, _, _, .MuSet s q₀ q₁ => q₀.NonzeroOn E ∨ q₁.NonzeroOn (insert s E)
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.NonzeroOn E
  | _, _, _, _, .GammaScalar _ _ _ _ => True
  | _, _, _, _, .GammaNest _ _ _ _ q => q.NonzeroOn E
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.NonzeroOn E
  | _, _, _, _, .ProvSum _ _ _ q => q.NonzeroOn E
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.NonzeroOn E
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.NonzeroOn E

omit [ValueType T] in
/-- **The condition is antitone in the names forced empty.** -/
theorem AggQueryIn.NonzeroOn.mono :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {E E' : Set String}, E ⊆ E' → q.NonzeroOn E' → q.NonzeroOn E := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun hE h hs => h (hE hs)
  | Hole n s => exact fun hE h hs => h (hE hs)
  | Empty => exact fun _ h => h
  | Proj ps q ih => exact fun hE h => ih hE h
  | Sel φ q _ ih => exact fun hE h => ih hE h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hE h => ⟨ih₁ hE h.1, ih₂ hE h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hE h => ⟨ih₁ hE h.1, ih₂ hE h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun hE h => h.elim (fun h => Or.inl (ih₁ hE h))
      (fun h => Or.inr (ih₂ hE h))
  | Dedup q ih => exact fun hE h => ih hE h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hE h => ih₁ hE h
  | Explode k hk q ih => exact fun hE h => ih hE h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hE h => ih₀ hE h
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun hE h => h.elim (fun h => Or.inl (ih₀ hE h))
      (fun h => Or.inr (ih₁ (Set.insert_subset_insert hE) h))
  | Gamma is ts fs q keep ord ih => exact fun hE h => ih hE h
  | GammaScalar ts fs q ord ih => exact fun _ _ => trivial
  | GammaNest is his p f q ih => exact fun hE h => ih hE h
  | ProvSum is his t q ih => exact fun hE h => ih hE h
  | Retag hk q ih => exact fun hE h => ih hE h
  | GammaTok is his ts fs a q keep ih => exact fun hE h => ih hE h
  | Win P O o w t f q hrr dist keep ih => exact fun hE h => ih hE h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hE h => ih hE h

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

omit [ValueType T] in
/-- A sum is empty only if both summands are. -/
theorem Multiset.left_eq_zero_of_add_eq_zero {α : Type} {s t : Multiset α}
    (h : s + t = 0) : s = 0 := by
  have hc := Multiset.card_add s t
  rw [h, Multiset.card_zero] at hc
  exact Multiset.card_eq_zero.mp (by omega)

omit [ValueType T] in
theorem Multiset.right_eq_zero_of_add_eq_zero {α : Type} {s t : Multiset α}
    (h : s + t = 0) : t = 0 := by
  have hc := Multiset.card_add s t
  rw [h, Multiset.card_zero] at hc
  exact Multiset.card_eq_zero.mp (by omega)

/-- **Without `σ` and `−`, a query that is not `NonzeroOn E` is empty on
every instance empty on `E`** where it is defined. -/
theorem AggQueryIn.evaluatePlain_eq_zero_of_not_nonzeroOn {S : Set OpKind}
    (hsel : OpKind.sel ∉ S) (hdiff : OpKind.diff ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → ∀ (sch : Schema) (E : Set String), q.overSchema sch →
      ¬ q.NonzeroOn E →
      ∀ (D : Database T) (γ : Fin c → T), Database.EmptyOn sch E D →
        q.SettlesAt D γ → q.evaluatePlain D γ = 0 := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ sch E hw hnz D γ hD _
    have hs : s ∈ E := not_not.mp hnz
    show (match D.find n s with
      | none => (0 : Multiset (Tuple T n)) | some r => r) = 0
    cases hf : D.find n s with
    | none => rfl
    | some r => exact hD s n r hw hs hf
  | Hole n s =>
    intro _ sch E hw hnz D γ hD _
    have hs : s ∈ E := not_not.mp hnz
    show (match D.find n s with
      | none => (0 : Multiset (Tuple T n)) | some r => r) = 0
    cases hf : D.find n s with
    | none => rfl
    | some r => exact hD s n r hw hs hf
  | Empty => exact fun _ _ _ _ _ _ _ _ _ => rfl
  | Proj ps q ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain, ih hq.2 sch E hw hnz D γ hD hs]
    rfl
  | Sel φ q _ ih => intro hq; exact absurd hq.1 hsel
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    refine Multiset.card_eq_zero.mp ?_
    rw [Relation.card_hMul]
    rcases not_and_or.mp hnz with h | h
    · rw [ih₁ hq.2.1 sch E hw.1 h D γ hD hs.1, Multiset.card_zero, Nat.zero_mul]
    · rw [ih₂ hq.2.2 sch E hw.2 h D γ hD hs.2, Multiset.card_zero, Nat.mul_zero]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    rcases not_and_or.mp hnz with h | h
    · rw [ih₁ hq.2.1 sch E hw.1 h D γ hD hs.1]
      rfl
    · refine Multiset.eq_zero_of_forall_notMem (fun v hv => ?_)
      obtain ⟨u, hu, hv'⟩ := Multiset.mem_bind.mp hv
      obtain ⟨w, hw', -⟩ := Multiset.mem_map.mp hv'
      rw [ih₂ hq.2.2 sch E hw.2 h D (Fin.append u γ) hD (hs.2 u hu)] at hw'
      exact Multiset.notMem_zero w hw'
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq sch E hw hnz D γ hD hs
    obtain ⟨h₁, h₂⟩ := not_or.mp hnz
    simp only [AggQueryIn.evaluatePlain, ih₁ hq.2.1 sch E hw.1 h₁ D γ hD hs.1,
      ih₂ hq.2.2 sch E hw.2 h₂ D γ hD hs.2]
    rfl
  | Dedup q ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain, ih hq.2 sch E hw hnz D γ hD hs]
    rfl
  | Diff q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 hdiff
  | Explode k hk q ih =>
    intro hq sch E hw hnz D γ hD hs; exact ih hq sch E hw hnz D γ hD hs
  | Retag hk q ih =>
    intro hq sch E hw hnz D γ hD hs; exact ih hq sch E hw hnz D γ hD hs
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    rw [ih₀ hq.2.1 sch E hw.2.1 hnz D γ hD hs.1]
    exact muSumFix_zero_of_step_zero hs.2.1
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hq sch E hw hnz D γ hD hs
    obtain ⟨h₀, h₁⟩ := not_or.mp hnz
    simp only [AggQueryIn.evaluatePlain]
    refine muFix_zero_of_step_zero ?_
    show (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s 0) γ).dedup = 0
    rw [ih₀ hq.2.1 sch E hw.2.1 h₀ D γ hD hs.1,
      ih₁ hq.2.2 (sch.update s _) (insert s E) hw.2.2.2 h₁ (D.assign s 0) γ
        (hD.assign_update_zero hw.1 _) (hs.2.2 0)]
    rfl
  | Gamma is ts fs q keep ord ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain, ih hq.2 sch E hw hnz D γ hD hs]
    rfl
  | GammaScalar ts fs q ord ih => intro _ _ _ _ hnz; exact absurd trivial hnz
  | GammaNest is his p f q ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain, ih hq.2 sch E hw hnz D γ hD hs]
    rfl
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    rw [ih hq.2 sch E hw hnz D γ hD hs]
    rfl
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    rw [ih hq.2 sch E hw hnz D γ hD hs]
    rfl

/-- The set recursion's case of the theorem below, with the base's and
the body's cases as hypotheses: the first round is non-empty because the
base is, or the body is at the instance binding the name to the empty
relation; every later round is non-empty because the base is, or the
body is at the instance binding the name to the previous round, the
body's condition at the smaller set of names forced empty following from
its condition at the larger. -/
private theorem AggQueryIn.evaluatePlain_ne_zero_muSet {c n : ℕ} (s : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (ih₀ : ∀ (sch : Schema) (E : Set String), q₀.overSchema sch →
      q₀.NonzeroOn E → ∀ (D : Database T) (γ : Fin c → T),
      Database.FullOff sch E D → q₀.SettlesAt D γ → q₀.evaluatePlain D γ ≠ 0)
    (ih₁ : ∀ (sch : Schema) (E : Set String), q₁.overSchema sch →
      q₁.NonzeroOn E → ∀ (D : Database T) (γ : Fin c → T),
      Database.FullOff sch E D → q₁.SettlesAt D γ → q₁.evaluatePlain D γ ≠ 0)
    (sch : Schema) (E : Set String)
    (hw : (AggQueryIn.MuSet s q₀ q₁).overSchema sch)
    (hnz : (AggQueryIn.MuSet s q₀ q₁).NonzeroOn E)
    (D : Database T) (γ : Fin c → T) (hD : Database.FullOff sch E D)
    (hs : (AggQueryIn.MuSet s q₀ q₁).SettlesAt D γ) :
    (AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ ≠ 0 := by
  simp only [AggQueryIn.evaluatePlain]
  -- A round is non-empty when the base is, or when the body is at it.
  have hround : ∀ (X : Relation T n), Database.FullOff sch E (D.assign s X) →
      (q₀.NonzeroOn E ∨ (X ≠ 0 ∧ q₁.NonzeroOn (E \ {s}))) →
      q₁.SettlesAt (D.assign s X) γ →
      (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup ≠ 0 := by
    intro X hDX h hs₁ hc
    rw [Multiset.dedup_eq_zero_iff] at hc
    rcases h with h | ⟨hX, h⟩
    · exact ih₀ sch E hw.2.1 h _ γ hD hs.1
        (Multiset.left_eq_zero_of_add_eq_zero hc)
    · exact ih₁ (sch.update s n) (E \ {s}) hw.2.2.2 h _ γ
        (hD.assign_update hw.1 hX) hs₁
        (Multiset.right_eq_zero_of_add_eq_zero hc)
  refine muFix_ne_zero_of_settles hs.2.1 ?_ ?_
  · -- The first round.
    show (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s 0) γ).dedup ≠ 0
    intro hc
    rw [Multiset.dedup_eq_zero_iff] at hc
    rcases hnz with h | h
    · exact ih₀ sch E hw.2.1 h _ γ hD hs.1 (Multiset.left_eq_zero_of_add_eq_zero hc)
    · exact ih₁ (sch.update s n) (insert s E) hw.2.2.2 h _ γ
        (hD.assign_update_zero _) (hs.2.2 0)
        (Multiset.right_eq_zero_of_add_eq_zero hc)
  · -- Every later round, from a non-empty one.
    intro k hk
    refine hround _ (hD.assign_of_none hw.1 _) ?_ (hs.2.2 k)
    rcases hnz with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hk, AggQueryIn.NonzeroOn.mono q₁
        (Set.sdiff_subset.trans (Set.subset_insert s E)) h⟩

/-- **Without `σ` and `−`, a query that is `NonzeroOn E` is non-empty on
every instance full off `E`** where it is defined. -/
theorem AggQueryIn.evaluatePlain_ne_zero_of_nonzeroOn {S : Set OpKind}
    (hsel : OpKind.sel ∉ S) (hdiff : OpKind.diff ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → ∀ (sch : Schema) (E : Set String), q.overSchema sch →
      q.NonzeroOn E →
      ∀ (D : Database T) (γ : Fin c → T), Database.FullOff sch E D →
        q.SettlesAt D γ → q.evaluatePlain D γ ≠ 0 := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ sch E hw hnz D γ hD _
    obtain ⟨r, hr, hne⟩ := hD s n hw hnz
    simp only [AggQueryIn.evaluatePlain, hr]
    exact hne
  | Hole n s =>
    intro _ sch E hw hnz D γ hD _
    obtain ⟨r, hr, hne⟩ := hD s n hw hnz
    simp only [AggQueryIn.evaluatePlain, hr]
    exact hne
  | Empty => exact fun _ _ _ _ h => h.elim
  | Proj ps q ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    exact fun hc => ih hq.2 sch E hw hnz D γ hD hs
      ((Multiset.map_eq_zero_iff _ _).mp hc)
  | Sel φ q _ ih => intro hq; exact absurd hq.1 hsel
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq sch E hw hnz D γ hD hs hc
    simp only [AggQueryIn.evaluatePlain] at hc
    have h0 : Multiset.card (q₁.evaluatePlain D γ)
        * Multiset.card (q₂.evaluatePlain D γ) = 0 := by
      rw [← Relation.card_hMul]
      exact Multiset.card_eq_zero.mpr hc
    rcases Nat.mul_eq_zero.mp h0 with hz | hz
    · exact ih₁ hq.2.1 sch E hw.1 hnz.1 D γ hD hs.1 (Multiset.card_eq_zero.mp hz)
    · exact ih₂ hq.2.2 sch E hw.2 hnz.2 D γ hD hs.2 (Multiset.card_eq_zero.mp hz)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq sch E hw hnz D γ hD hs hc
    simp only [AggQueryIn.evaluatePlain] at hc
    rw [← Multiset.card_eq_zero, Multiset.card_bind] at hc
    obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero
      (ih₁ hq.2.1 sch E hw.1 hnz.1 D γ hD hs.1)
    have hzero := (Multiset.sum_eq_zero_iff.mp hc) _
      (Multiset.mem_map.mpr ⟨u, hu, rfl⟩)
    refine ih₂ hq.2.2 sch E hw.2 hnz.2 D (Fin.append u γ)
      (fun t k ht hE => hD t k ht hE) (hs.2 u hu) (Multiset.card_eq_zero.mp ?_)
    simpa only [Function.comp_apply, Multiset.card_map] using hzero
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq sch E hw hnz D γ hD hs hc
    simp only [AggQueryIn.evaluatePlain] at hc
    rcases hnz with h | h
    · exact ih₁ hq.2.1 sch E hw.1 h D γ hD hs.1
        (Multiset.left_eq_zero_of_add_eq_zero hc)
    · exact ih₂ hq.2.2 sch E hw.2 h D γ hD hs.2
        (Multiset.right_eq_zero_of_add_eq_zero hc)
  | Dedup q ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    exact fun hc => ih hq.2 sch E hw hnz D γ hD hs
      ((Multiset.dedup_eq_zero_iff _).mp hc)
  | Diff q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 hdiff
  | Explode k hk q ih =>
    intro hq sch E hw hnz D γ hD hs; exact ih hq sch E hw hnz D γ hD hs
  | Retag hk q ih =>
    intro hq sch E hw hnz D γ hD hs; exact ih hq sch E hw hnz D γ hD hs
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    exact muSumFix_ne_zero _ (ih₀ hq.2.1 sch E hw.2.1 hnz D γ hD hs.1)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hq sch E hw hnz D γ hD hs
    exact AggQueryIn.evaluatePlain_ne_zero_muSet s q₀ q₁ (ih₀ hq.2.1)
      (ih₁ hq.2.2) sch E hw hnz D γ hD hs
  | Gamma is ts fs q keep ord ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    exact fun hc => ih hq.2 sch E hw hnz D γ hD hs
      ((Multiset.map_eq_zero_iff _ _).mp
        ((Multiset.dedup_eq_zero_iff _).mp
          ((Multiset.map_eq_zero_iff _ _).mp hc)))
  | GammaScalar ts fs q ord ih =>
    intro _ _ _ _ _ D γ _ _
    simp only [AggQueryIn.evaluatePlain]
    exact fun hc => absurd (congrArg Multiset.card hc) (by simp)
  | GammaNest is his p f q ih =>
    intro hq sch E hw hnz D γ hD hs
    simp only [AggQueryIn.evaluatePlain]
    exact fun hc => ih hq.2 sch E hw hnz D γ hD hs
      ((Multiset.map_eq_zero_iff _ _).mp
        ((Multiset.dedup_eq_zero_iff _).mp
          ((Multiset.map_eq_zero_iff _ _).mp hc)))
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq sch E hw hnz D γ hD hs hc
    simp only [AggQueryIn.evaluatePlain] at hc
    exact ih hq.2 sch E hw hnz D γ hD hs ((Multiset.map_eq_zero_iff _ _).mp hc)
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq sch E hw hnz D γ hD hs hc
    simp only [AggQueryIn.evaluatePlain] at hc
    refine ih hq.2 sch E hw hnz D γ hD hs (Multiset.card_eq_zero.mp ?_)
    exact (OccFam.size_ofSorted (q.evaluatePlain D γ)).symm.trans
      (OccFam.size_eq_zero_of_mk_toMultiset _ _ hc)

/-- **Without `σ` and `−`, a query is empty everywhere or non-empty on
every full instance**, wherever it is defined – the recursions included,
`NonzeroOn ∅` deciding which. -/
theorem AggQueryIn.zero_or_ne_zero_of_noSelDiff {S : Set OpKind}
    (hsel : OpKind.sel ∉ S) (hdiff : OpKind.diff ∉ S) {sch : Schema}
    {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
    (hq : q.usesOnly S) (hw : q.overSchema sch) :
    (∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
        q.evaluatePlain D γ = 0)
      ∨ (∀ (D : Database T) (γ : Fin c → T), Database.Full sch D →
          q.SettlesAt D γ → q.evaluatePlain D γ ≠ 0) := by
  rcases Classical.em (q.NonzeroOn ∅) with h | h
  · exact Or.inr (fun D γ hD hs =>
      AggQueryIn.evaluatePlain_ne_zero_of_nonzeroOn hsel hdiff q hq sch ∅ hw h
        D γ (hD.fullOff ∅) hs)
  · exact Or.inl (fun D γ hs =>
      AggQueryIn.evaluatePlain_eq_zero_of_not_nonzeroOn hsel hdiff q hq sch ∅
        hw h D γ (Database.emptyOn_empty sch D) hs)

/-- The schema of one unary relation, for the witnesses below. -/
def schemaR : Schema := Schema.ofFn (fun s => if s = "R" then some 1 else none) {"R"}
  (fun s hs => Finset.mem_singleton.mpr (by by_contra hne; exact hs (ite_eq_right hne)))

theorem schemaR_apply (s : String) : schemaR s = if s = "R" then some 1 else none := rfl

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
    rw [schemaR_apply, ite_eq_left rfl] at h
    obtain rfl : k = 1 := (Option.some.inj h).symm
    exact ⟨({![1]} : Multiset (Tuple ℕ 1)), rfl, fun hc =>
      absurd (congrArg Multiset.card hc) (by simp)⟩
  · rw [schemaR_apply, ite_eq_right hs] at h
    exact absurd h (fun hc => Option.some_ne_none k hc.symm)

theorem full_dZero : Database.Full schemaR dZero := by
  intro s k h
  by_cases hs : s = "R"
  · subst hs
    rw [schemaR_apply, ite_eq_left rfl] at h
    obtain rfl : k = 1 := (Option.some.inj h).symm
    exact ⟨({![0]} : Multiset (Tuple ℕ 1)), rfl, fun hc =>
      absurd (congrArg Multiset.card hc) (by simp)⟩
  · rw [schemaR_apply, ite_eq_right hs] at h
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

/-- The number of rounds a recursion of the minimal signature can run
before the orbits of its rows repeat: the size of a row box (below),
plus two. -/
def recBound (c n K : ℕ) : ℕ := (n + c + K) ^ n + 2

/-- The bound a query gives on its answer's size, per row of the
instance. -/
def AggQueryIn.sizeBound : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → ℕ
  | _, _, _, _, .Rel _ _ => 1
  | _, _, _, _, .Hole _ _ => 1
  | _, _, _, _, .Empty => 0
  | _, _, _, _, .Proj _ q => q.sizeBound
  | _, _, _, _, .Sel _ q _ => q.sizeBound
  | _, _, _, _, .Prod _ _ => 0
  | _, _, _, _, .Apply _ _ => 0
  | _, _, _, _, .Sum q₁ q₂ => q₁.sizeBound + q₂.sizeBound
  | _, _, _, _, .Dedup q => q.sizeBound
  | _, _, _, _, .Diff q₁ _ => q₁.sizeBound
  | _, _, _, _, .Explode _ _ q => q.sizeBound
  | _, _, _, _, .Retag _ q => q.sizeBound
  | c, n, _, _, .Mu _ q₀ q₁ => recBound c n q₁.consts.card * q₀.sizeBound
  | c, n, _, _, .MuSet _ q₀ q₁ =>
      recBound c n q₁.consts.card * (q₀.sizeBound + q₁.sizeBound)
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.sizeBound
  | _, _, _, _, .GammaScalar _ _ _ _ => 1
  | _, _, _, _, .GammaNest _ _ _ _ q => q.sizeBound
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.sizeBound
  | _, _, _, _, .ProvSum _ _ _ q => q.sizeBound
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.sizeBound
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.sizeBound

/-! ### A recursive term without `×` and the apply reads the previous round row by row

What the product row needs of a recursion is a bound on the number of
rounds a bag recursion can run before its rounds are empty, and on the
rows a set recursion can accumulate. Without `×` and the apply, a
recursive term in the minimal signature maps each row of the previous
round to **at most one row** – a projection reads a row as columns,
context values and constants, a selection keeps or drops it – and adds
rows that read no round. So each row of the base follows an orbit under
one function `f` on rows; and in the minimal signature that orbit stays
inside the rows built from the row's own values, the context's and the
query's constants, a set of a size the query fixes. An orbit longer than
that repeats, and a repeating orbit never ends: so a bag recursion that
settles does so within that many rounds, and a set recursion's rows are
the first that many points of the orbits of its base rows. Both bounds
fail with arithmetic (`Π_{x+1}` has an orbit as long as the instance
wants), which is why the row is about the minimal signature. -/

/-- The iterates of a partial function: `optIter f j a` is `f` applied
`j` times to `a`, or `none` once an application has failed. -/
def optIter {α : Type} (f : α → Option α) : ℕ → α → Option α
  | 0 => some
  | j + 1 => fun a => (optIter f j a).bind f

omit [ValueType T] in
theorem optIter_add {α : Type} (f : α → Option α) (i : ℕ) :
    ∀ (t : ℕ) (a : α), optIter f (i + t) a = (optIter f i a).bind (optIter f t) := by
  intro t
  induction t with
  | zero => intro a; show optIter f i a = (optIter f i a).bind some; cases optIter f i a <;> rfl
  | succ t ih =>
    intro a
    show (optIter f (i + t) a).bind f = (optIter f i a).bind (fun b => (optIter f t b).bind f)
    rw [ih a, Option.bind_assoc]

omit [ValueType T] in
/-- A failed orbit stays failed. -/
theorem optIter_none_of_le {α : Type} {f : α → Option α} {i j : ℕ} {a : α}
    (h : optIter f i a = none) (hij : i ≤ j) : optIter f j a = none := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [optIter_add, h]
  rfl

omit [ValueType T] in
/-- Two equal points of an orbit are followed by equal points. -/
theorem optIter_periodic {α : Type} {f : α → Option α} {i i' : ℕ} {a : α}
    (h : optIter f i a = optIter f i' a) (t : ℕ) :
    optIter f (i + t) a = optIter f (i' + t) a := by
  rw [optIter_add, optIter_add, h]

omit [ValueType T] in
/-- An orbit from a set closed under `f` stays in it. -/
theorem optIter_mem {α : Type} [DecidableEq α] {f : α → Option α}
    (S : Finset α) (hS : ∀ b ∈ S, ∀ c, f b = some c → c ∈ S) {a : α}
    (ha : a ∈ S) : ∀ j, optIter f j a ∈ insert none (S.image some) := by
  intro j
  induction j with
  | zero => exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem some ha)
  | succ j ih =>
    show (optIter f j a).bind f ∈ _
    cases hj : optIter f j a with
    | none => exact Finset.mem_insert_self _ _
    | some b =>
      rw [hj] at ih
      have hb : b ∈ S := by
        rcases Finset.mem_insert.mp ih with h | h
        · exact absurd h (Option.some_ne_none b)
        · obtain ⟨b', hb', hbb⟩ := Finset.mem_image.mp h
          exact (Option.some.inj hbb) ▸ hb'
      show f b ∈ _
      cases hf : f b with
      | none => exact Finset.mem_insert_self _ _
      | some c =>
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem some (hS b hb c hf))

omit [ValueType T] in
/-- **An orbit in a set of `k` points repeats within its first `k + 2`
points.** -/
theorem optIter_exists_repeat {α : Type} [DecidableEq α] {f : α → Option α}
    (S : Finset α) (hS : ∀ b ∈ S, ∀ c, f b = some c → c ∈ S) {a : α}
    (ha : a ∈ S) :
    ∃ (i i' : ℕ), (i < i') ∧ (i' < S.card + 2) ∧ optIter f i a = optIter f i' a := by
  have hc : (insert none (S.image some)).card < (Finset.range (S.card + 2)).card := by
    rw [Finset.card_range]
    exact Nat.lt_of_le_of_lt (Finset.card_insert_le _ _)
      (Nat.succ_lt_succ (Nat.lt_succ_of_le (Finset.card_image_le)))
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
      (f := fun j => optIter f j a) (fun j _ => optIter_mem S hS ha j)
  rw [Finset.mem_range] at hx hy
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, y, h, hy, hfxy⟩
  · exact ⟨y, x, h, hx, hfxy.symm⟩

omit [ValueType T] in
/-- **Every point of such an orbit is one of its first `k + 2` points.** -/
theorem optIter_exists_lt {α : Type} [DecidableEq α] {f : α → Option α}
    (S : Finset α) (hS : ∀ b ∈ S, ∀ c, f b = some c → c ∈ S) {a : α}
    (ha : a ∈ S) (j : ℕ) :
    ∃ j' : ℕ, (j' < S.card + 2) ∧ optIter f j' a = optIter f j a := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.lt_or_ge j (S.card + 2) with hj | hj
    · exact ⟨j, hj, rfl⟩
    · obtain ⟨i, i', hii', hi', heq⟩ := optIter_exists_repeat S hS ha
      have hle : i' ≤ j := by omega
      have hjj : i + (j - i') < j := by omega
      obtain ⟨j', hj', hj'eq⟩ := ih (i + (j - i')) hjj
      refine ⟨j', hj', hj'eq.trans ?_⟩
      rw [optIter_periodic heq, Nat.add_sub_cancel' hle]

omit [ValueType T] in
/-- **An orbit alive at point `k + 1` never ends.** -/
theorem optIter_ne_none {α : Type} [DecidableEq α] {f : α → Option α}
    (S : Finset α) (hS : ∀ b ∈ S, ∀ c, f b = some c → c ∈ S) {a : α}
    (ha : a ∈ S) (h : optIter f (S.card + 1) a ≠ none) (j : ℕ) :
    optIter f j a ≠ none := by
  intro hn
  obtain ⟨j', hj', heq⟩ := optIter_exists_lt S hS ha j
  exact h (optIter_none_of_le (heq.trans hn) (Nat.lt_succ_iff.mp hj'))

omit [ValueType T] in
/-- The rounds of a set recursion are duplicate-free. -/
theorem nodup_iterate_dedup {α : Type} [DecidableEq α]
    (f : Multiset α → Multiset α) :
    ∀ j : ℕ, ((fun X => (f X).dedup)^[j] 0).Nodup := by
  intro j
  cases j with
  | zero => exact Multiset.nodup_zero
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact Multiset.nodup_dedup _

omit [ValueType T] in
/-- Keeping at most one row per row keeps at most as many rows. -/
theorem Multiset.card_filterMap_le {α β : Type} (f : α → Option β)
    (s : Multiset α) : Multiset.card (Multiset.filterMap f s) ≤ Multiset.card s :=
  Quot.inductionOn s fun l => List.length_filterMap_le f l

omit [ValueType T] in
/-- The sum of `b + 1` rounds, each no larger than the base. -/
theorem card_muSum_le {α : Type} {step : Multiset α → Multiset α}
    (hstep : ∀ X, Multiset.card (step X) ≤ Multiset.card X) (M : Multiset α) :
    ∀ b : ℕ, Multiset.card (muSum step b M) ≤ (b + 1) * Multiset.card M := by
  have hiter : ∀ j, Multiset.card (step^[j] M) ≤ Multiset.card M := by
    intro j
    induction j with
    | zero => exact le_refl _
    | succ j ih => rw [Function.iterate_succ_apply']; exact le_trans (hstep _) ih
  intro b
  induction b with
  | zero => exact le_of_eq (one_mul _).symm
  | succ b ih =>
    rw [muSum_succ, Multiset.card_add, Nat.succ_mul]
    exact Nat.add_le_add ih (hiter _)

private theorem mem_union_right_mono {x : T} {A K K' : Finset T}
    (h : x ∈ Union.union A K) (hK : K ⊆ K') : x ∈ Union.union A K' := by
  rcases Finset.mem_union.mp h with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (hK h)

/-- **Every projection column of the query applies no function to
values** – the half of `inSig` the recursion bounds read, a term being a
column, a context value or a constant. -/
def AggQueryIn.noFunCols : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj ps q => (∀ j, (ps j).noFun = true) ∧ q.noFunCols
  | _, _, _, _, .Sel _ q _ => q.noFunCols
  | _, _, _, _, .Prod q₁ q₂ => q₁.noFunCols ∧ q₂.noFunCols
  | _, _, _, _, .Apply q₁ q₂ => q₁.noFunCols ∧ q₂.noFunCols
  | _, _, _, _, .Sum q₁ q₂ => q₁.noFunCols ∧ q₂.noFunCols
  | _, _, _, _, .Dedup q => q.noFunCols
  | _, _, _, _, .Diff q₁ q₂ => q₁.noFunCols ∧ q₂.noFunCols
  | _, _, _, _, .Explode _ _ q => q.noFunCols
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noFunCols ∧ q₁.noFunCols
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noFunCols ∧ q₁.noFunCols
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noFunCols
  | _, _, _, _, .GammaScalar _ _ q _ => q.noFunCols
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noFunCols
  | _, _, _, _, .ProvSum _ _ _ q => q.noFunCols
  | _, _, _, _, .Retag _ q => q.noFunCols
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noFunCols
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noFunCols
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noFunCols

/-- **Every recursive term of the query applies no function to values.**
This is what the product row asks of a recursion: the bound on its
rounds is a bound on the orbit of a row under a term that can only copy
values, and it is the one place the signature enters the rows. A query
of a signature satisfies it (`recNoFun_of_inSig`), and so does a
recursion-free query (`recNoFun_of_usesOnly`). -/
def AggQueryIn.recNoFun : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.recNoFun
  | _, _, _, _, .Sel _ q _ => q.recNoFun
  | _, _, _, _, .Prod q₁ q₂ => q₁.recNoFun ∧ q₂.recNoFun
  | _, _, _, _, .Apply q₁ q₂ => q₁.recNoFun ∧ q₂.recNoFun
  | _, _, _, _, .Sum q₁ q₂ => q₁.recNoFun ∧ q₂.recNoFun
  | _, _, _, _, .Dedup q => q.recNoFun
  | _, _, _, _, .Diff q₁ q₂ => q₁.recNoFun ∧ q₂.recNoFun
  | _, _, _, _, .Explode _ _ q => q.recNoFun
  | _, _, _, _, .Mu _ q₀ q₁ => q₁.noFunCols ∧ q₀.recNoFun ∧ q₁.recNoFun
  | _, _, _, _, .MuSet _ q₀ q₁ => q₁.noFunCols ∧ q₀.recNoFun ∧ q₁.recNoFun
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.recNoFun
  | _, _, _, _, .GammaScalar _ _ q _ => q.recNoFun
  | _, _, _, _, .GammaNest _ _ _ _ q => q.recNoFun
  | _, _, _, _, .ProvSum _ _ _ q => q.recNoFun
  | _, _, _, _, .Retag _ q => q.recNoFun
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.recNoFun
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.recNoFun
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.recNoFun

theorem AggQueryIn.noFunCols_of_inSig {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig Θ → q.noFunCols := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun h => ⟨h.1, ih h.2⟩
  | Sel φ q _ ih => exact fun h => ih h.2
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode k hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h.2.2.2
  | GammaScalar ts fs q ord ih => exact fun h => ih h.2.2
  | GammaNest is his p f q ih => exact fun h => ih h.2.2
  | ProvSum is his t q ih => exact fun h => h.elim
  | Retag hk q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t f q hrr dist keep ih => exact fun h => ih h.2.2.2
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
theorem AggQueryIn.recNoFun_of_noFunCols :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noFunCols → q.recNoFun := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun h => ih h.2
  | Sel φ q _ ih => exact fun h => ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode k hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨h.2, ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨h.2, ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p f q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t f q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

/-- A query of a signature has function-free recursive terms. -/
theorem AggQueryIn.recNoFun_of_inSig {Θ : Set (SeqAggFunc T)}
    {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
    (h : q.inSig Θ) : q.recNoFun :=
  AggQueryIn.recNoFun_of_noFunCols q (AggQueryIn.noFunCols_of_inSig q h)

omit [ValueType T] in
/-- So does a recursion-free query, having no recursive term. -/
theorem AggQueryIn.recNoFun_of_usesOnly {S : Set OpKind}
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.recNoFun := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun hq => ih hq.2
  | Sel φ q _ ih => exact fun hq => ih hq.2
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Dedup q ih => exact fun hq => ih hq.2
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Explode k hk q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hmb
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hms
  | Gamma is ts fs q keep ord ih => exact fun hq => ih hq.2
  | GammaScalar ts fs q ord ih => exact fun hq => ih hq.2
  | GammaNest is his p f q ih => exact fun hq => ih hq.2
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Retag hk q ih => exact fun hq => ih hq
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih => exact fun hq => ih hq.2
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq => ih hq.2

/-- The values a row of a recursive term may draw on: the row it comes
from, the context, and the term's constants. -/
def rowVals {c n : ℕ} (u : Tuple T n) (γ : Fin c → T) (K : Finset T) : Finset T :=
  Union.union (Union.union (Finset.univ.image u) (Finset.univ.image γ)) K

omit [ValueType T] in
/-- A list splitting into a singleton: one half is it, the other empty. -/
theorem List.append_eq_singleton' {α : Type} {l₁ l₂ : List α} {a : α} (h : l₁ ++ l₂ = [a]) :
    (l₁ = [a] ∧ l₂ = []) ∨ (l₁ = [] ∧ l₂ = [a]) := by
  cases l₁ with
  | nil => exact Or.inr ⟨rfl, h⟩
  | cons x l₁ =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h
    exact Or.inl ⟨rfl, rfl⟩

/-- **Without `×` and the apply, a recursive term of the minimal
signature reads the recursive relation row by row**: its rows are the
rows `f u` of the rows `u` of the relation, `f` a partial function, and
rows `C` that read nothing of it; and the values of `f u` are values of
`u`, of the context, or constants of the term. -/
theorem AggQueryIn.pointwise_of_body {S : Set OpKind}
    (hp : OpKind.prod ∉ S) (ha : OpKind.apply ∉ S) {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      l = [(s, m)] → q.usesOnly S → q.noMention s → q.noFunCols →
      ∀ (D : Database T) (γ : Fin c → T),
      ∃ (f : Tuple T m → Option (Tuple T n)) (C : Multiset (Tuple T n)),
        (∀ X : Multiset (Tuple T m),
          q.evaluatePlain (D.assign s X) γ = Multiset.filterMap f X + C)
        ∧ ∀ v w, f v = some w → ∀ i, w i ∈ rowVals v γ q.consts := by
  intro c n κ l q
  induction q with
  | Rel n' s' => exact fun hl => absurd hl (by simp)
  | Hole n' s' =>
    intro hl _ _ _ D γ
    have hs : s' = s := (Prod.mk.inj (List.singleton_inj.mp hl)).1
    have hn : n' = m := (Prod.mk.inj (List.singleton_inj.mp hl)).2
    subst hs; subst hn
    refine ⟨some, 0, fun X => ?_, fun v w hw i => ?_⟩
    · show (match (D.assign s' X).find n' s' with
        | none => (0 : Multiset (Tuple T n')) | some r => r) = _
      rw [Database.find_assign]
      show X = _
      rw [Multiset.filterMap_some, add_zero]
    · cases hw
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem v (Finset.mem_univ i)))
  | Empty => exact fun hl => absurd hl (by simp)
  | Proj ps q ih =>
    intro hl hq hr hnf D γ
    obtain ⟨f, C, hX, hv⟩ := ih hl hq.2 hr hnf.2 D γ
    refine ⟨fun u => (f u).map (fun v j => (ps j).evalPlain v γ),
      C.map (fun v j => (ps j).evalPlain v γ), fun X => ?_, fun v w hw i => ?_⟩
    · simp only [AggQueryIn.evaluatePlain]
      rw [hX X, Multiset.map_add, Multiset.map_filterMap]
    · obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp hw
      show (ps i).evalPlain v' γ ∈ _
      refine ProjColIn.evalPlain_mem_of_noFun (ps i) (hnf.1 i)
        ((ps i).constsIn_of_subset fun x hx => ?_) v' (fun j => ?_) γ (fun j => ?_)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩))
      · exact mem_union_right_mono (hv v v' hv' j) (Finset.subset_union_right)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem γ (Finset.mem_univ j)))
  | Sel φ q _ ih =>
    intro hl hq hr hnf D γ
    obtain ⟨f, C, hX, hv⟩ := ih hl hq.2 hr hnf D γ
    refine ⟨fun u => (f u).filter (fun v => @decide _ (φ.decHoldsPlain v γ)),
      @Multiset.filter _ (fun v => φ.holdsPlain v γ) (fun v => φ.decHoldsPlain v γ) C,
      fun X => ?_, fun v w hw i => ?_⟩
    · simp only [AggQueryIn.evaluatePlain]
      rw [hX X, Multiset.filter_add, Multiset.filter_filterMap]
    · exact hv v w (Option.filter_eq_some_iff.mp hw).1 i
  | Prod q₁ q₂ ih₁ ih₂ => intro _ hq; exact absurd hq.1 hp
  | Apply q₁ q₂ ih₁ ih₂ => intro _ hq; exact absurd hq.1 ha
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hl hq hr hnf D γ
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      obtain ⟨f, C, hX, hv⟩ := ih₁ h₁ hq.2.1 hr.1 hnf.1 D γ
      refine ⟨f, C + (show Multiset (Tuple T _) from q₂.evaluatePlain D γ),
        fun X => ?_, fun v w hw i => ?_⟩
      · simp only [AggQueryIn.evaluatePlain]
        rw [hX X, AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hr.2 D γ]
        show Multiset.filterMap f X + C
          + (show Multiset (Tuple T _) from q₂.evaluatePlain D γ) = _
        exact add_assoc _ _ _
      · exact mem_union_right_mono (hv v w hw i) (Finset.subset_union_left)
    · subst h₁
      obtain ⟨f, C, hX, hv⟩ := ih₂ h₂ hq.2.2 hr.2 hnf.2 D γ
      refine ⟨f, (show Multiset (Tuple T _) from q₁.evaluatePlain D γ) + C,
        fun X => ?_, fun v w hw i => ?_⟩
      · simp only [AggQueryIn.evaluatePlain]
        rw [hX X, AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hr.1 D γ]
        show (show Multiset (Tuple T _) from q₁.evaluatePlain D γ)
          + (Multiset.filterMap f X + C) = _
        exact add_left_comm _ _ _
      · exact mem_union_right_mono (hv v w hw i) (Finset.subset_union_right)
  | Dedup q ih => exact fun hl => absurd hl (by simp)
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hl => absurd hl (by simp)
  | Explode k hk q ih => intro hl hq hr hnf D γ; exact ih hl hq hr hnf D γ
  | Retag hk q ih => intro hl hq hr hnf D γ; exact ih hl hq hr hnf D γ
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | Gamma is ts fs q keep ord ih => exact fun hl => absurd hl (by simp)
  | GammaScalar ts fs q ord ih => exact fun hl => absurd hl (by simp)
  | GammaNest is his p f q ih => exact fun hl => absurd hl (by simp)
  | ProvSum is his t q ih => exact fun hl => absurd hl (by simp)
  | GammaTok is his ts fs a q keep ih => exact fun hl => absurd hl (by simp)
  | Win P O o w t f q hrr dist keep ih => exact fun hl => absurd hl (by simp)
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hl => absurd hl (by simp)

/-- **The rows a recursive term's orbits stay in**: the rows over the
values of the row the orbit starts from, the context and the term's
constants. Its size is what bounds the rounds. -/
def rowBox {c n : ℕ} (u : Tuple T n) (γ : Fin c → T) (K : Finset T) :
    Finset (Tuple T n) :=
  Fintype.piFinset (fun _ : Fin n => rowVals u γ K)

theorem card_rowBox_le {c n : ℕ} (u : Tuple T n) (γ : Fin c → T)
    (K : Finset T) : (rowBox u γ K).card + 2 ≤ recBound c n K.card := by
  rw [rowBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, recBound]
  refine Nat.add_le_add_right (Nat.pow_le_pow_left ?_ n) 2
  rw [rowVals]
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
  · exact le_trans Finset.card_image_le (le_of_eq (by simp))
  · exact le_trans Finset.card_image_le (le_of_eq (by simp))

/-- A row box is closed under a row-by-row term's function. -/
theorem rowBox_closed {c n : ℕ} {u : Tuple T n} {γ : Fin c → T} {K : Finset T}
    {f : Tuple T n → Option (Tuple T n)}
    (hv : ∀ v w, f v = some w → ∀ i, w i ∈ rowVals v γ K) :
    ∀ v ∈ rowBox u γ K, ∀ w, f v = some w → w ∈ rowBox u γ K := by
  intro v hvbox w hw
  rw [rowBox, Fintype.mem_piFinset] at hvbox ⊢
  intro i
  rcases Finset.mem_union.mp (hv v w hw i) with h | h
  · rcases Finset.mem_union.mp h with h | h
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact hj ▸ hvbox j
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  · exact Finset.mem_union_right _ h

theorem self_mem_rowBox {c n : ℕ} (u : Tuple T n) (γ : Fin c → T)
    (K : Finset T) : u ∈ rowBox u γ K := by
  rw [rowBox, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image_of_mem u (Finset.mem_univ i)))

omit [ValueType T] in
/-- Binding a name to the empty relation does not change an instance's
size. -/
theorem Database.size_assign_zero (D : Database T) (s : String) (m : ℕ) :
    (D.assign s (0 : Relation T m)).size = D.size := by
  show (Multiset.card (0 : Multiset (Tuple T m)) + _) = _
  rw [Multiset.card_zero, Nat.zero_add]
  rfl

/-- **Without `×` and the apply, an answer of the minimal signature is
linear in the instance**, the recursions included wherever they are
defined: a bag recursion's rows are the orbits of its base's rows, ended
within a number of rounds the query fixes, and a set recursion's rows
are the first points of the orbits of its base's and its constant
rows. -/
theorem AggQueryIn.card_le_sizeBound {S : Set OpKind}
    (hp : OpKind.prod ∉ S) (ha : OpKind.apply ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.hygienic → q.recNoFun →
      ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
      Multiset.card (q.evaluatePlain D γ) ≤ q.sizeBound * (D.size + 1) := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ _ D γ _
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, one_mul]
    cases hf : D.find n s with
    | none => exact Nat.zero_le _
    | some rn => exact le_trans (Database.card_le_size D hf) (Nat.le_succ _)
  | Hole n s =>
    intro _ _ _ D γ _
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, one_mul]
    cases hf : D.find n s with
    | none => exact Nat.zero_le _
    | some rn => exact le_trans (Database.card_le_size D hf) (Nat.le_succ _)
  | Empty => intro _ _ _ D γ _; exact Nat.zero_le _
  | Proj ps q ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact ih hq.2 hr hsig D γ hs
  | Sel φ q _ ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (ih hq.2 hr hsig D γ hs)
  | Prod q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 hp
  | Apply q₁ q₂ ih₁ ih₂ => intro hq; exact absurd hq.1 ha
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, Nat.add_mul]
    rw [Relation.card_add]
    exact Nat.add_le_add (ih₁ hq.2.1 hr.1 hsig.1 D γ hs.1)
      (ih₂ hq.2.2 hr.2 hsig.2 D γ hs.2)
  | Dedup q ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    exact le_trans (Multiset.card_dedup_le _) (ih hq.2 hr hsig D γ hs)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    exact le_trans (Multiset.card_le_card (Multiset.filter_le _ _))
      (ih₁ hq.2.1 hr.1 hsig.1 D γ hs.1)
  | Explode k hk q ih => intro hq hr hsig D γ hs; exact ih hq hr hsig D γ hs
  | Retag hk q ih => intro hq hr hsig D γ hs; exact ih hq hr hsig D γ hs
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' n'
    intro hq hr hsig D γ hs
    obtain ⟨f, C, hX, hv⟩ :=
      AggQueryIn.pointwise_of_body hp ha q₁ rfl hq.2.2 hr.2.1 hsig.1 D γ
    have hM := ih₀ hq.2.1 hr.2.2.1 hsig.2.1 D γ hs.1
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    -- The constant rows are none, or no round is ever empty.
    obtain ⟨k, hk⟩ := hs.2.2.1
    have hC : C = 0 := by
      have hk' := hk
      rw [Function.iterate_succ_apply'] at hk'
      exact Multiset.right_eq_zero_of_add_eq_zero ((hX _).symm.trans hk')
    -- So the rounds are the orbits of the base's rows.
    have hiter : ∀ j, (fun X : Multiset (Tuple T n') =>
        q₁.evaluatePlain (D.assign s X) γ)^[j] (q₀.evaluatePlain D γ)
        = Multiset.filterMap (optIter f j) (q₀.evaluatePlain D γ) := by
      intro j
      induction j with
      | zero => exact (Multiset.filterMap_some _).symm
      | succ j ih =>
        rw [Function.iterate_succ_apply', ih]
        show q₁.evaluatePlain (D.assign s _) γ = _
        rw [hX, hC, add_zero, Multiset.filterMap_filterMap]
        rfl
    -- Every orbit has ended by round `k + 1`, hence within the bound.
    have hnone : ∀ u ∈ (show Multiset (Tuple T _) from q₀.evaluatePlain D γ),
        optIter f (k + 1) u = none := by
      intro u hu
      by_contra hne
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
      have hmem : w ∈ Multiset.filterMap (optIter f (k + 1))
          (q₀.evaluatePlain D γ) := (Multiset.mem_filterMap _ _).mpr ⟨u, hu, hw⟩
      rw [← hiter, hk] at hmem
      exact Multiset.notMem_zero w hmem
    have hbound : ∀ u ∈ (show Multiset (Tuple T _) from q₀.evaluatePlain D γ),
        optIter f ((n' + c' + q₁.consts.card) ^ n' + 1) u = none := by
      intro u hu
      by_contra hne
      have hle : (rowBox u γ q₁.consts).card + 1
          ≤ (n' + c' + q₁.consts.card) ^ n' + 1 := by
        have := card_rowBox_le u γ q₁.consts
        rw [recBound] at this
        omega
      exact optIter_ne_none (rowBox u γ q₁.consts) (rowBox_closed hv)
        (self_mem_rowBox u γ q₁.consts) (fun h0 => hne (optIter_none_of_le h0 hle))
        (k + 1) (hnone u hu)
    have hend : (fun X : Multiset (Tuple T n') =>
        q₁.evaluatePlain (D.assign s X) γ)^[(n' + c' + q₁.consts.card) ^ n' + 1]
        (q₀.evaluatePlain D γ) = 0 := by
      rw [hiter]
      exact Multiset.eq_zero_of_forall_notMem fun w hw => by
        obtain ⟨u, hu, h⟩ := (Multiset.mem_filterMap _ _).mp hw
        rw [hbound u hu] at h
        cases h
    rw [muSumFix_eq_of_empty hs.2.1 hend]
    refine le_trans (card_muSum_le (fun X => ?_) _ _) ?_
    · show Multiset.card (q₁.evaluatePlain (D.assign s X) γ) ≤ _
      rw [hX, hC, add_zero]
      exact Multiset.card_filterMap_le f X
    · rw [recBound, Nat.mul_assoc]
      exact Nat.mul_le_mul (Nat.add_le_add_left (Nat.le_succ 1) _) hM
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' n'
    intro hq hr hsig D γ hs
    obtain ⟨f, C, hX, hv⟩ :=
      AggQueryIn.pointwise_of_body hp ha q₁ rfl hq.2.2 hr.2.1 hsig.1 D γ
    have hM : Multiset.card (q₀.evaluatePlain D γ)
        ≤ q₀.sizeBound * (D.size + 1) :=
      ih₀ hq.2.1 hr.2.2.1 hsig.2.1 _ γ hs.1
    have hC : C = q₁.evaluatePlain (D.assign s (0 : Relation T n')) γ := by
      rw [hX, Multiset.filterMap_zero, zero_add]
    have hCcard : Multiset.card C ≤ q₁.sizeBound * (D.size + 1) := by
      rw [hC, ← Database.size_assign_zero D s n']
      exact ih₁ hq.2.2 hr.2.2.2 hsig.2.2 _ γ (hs.2.2 0)
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound]
    -- The rounds, as the orbits of the base's and the constant rows.
    have hstep : ∀ X : Multiset (Tuple T n'),
        (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup
          = ((show Multiset (Tuple T n') from q₀.evaluatePlain D γ)
              + (Multiset.filterMap f X + C)).dedup := by
      intro X
      rw [hX]
    set B := recBound c' n' q₁.consts.card with hB
    set W : Multiset (Tuple T n') :=
      ((show Multiset (Tuple T n') from q₀.evaluatePlain D γ) + C).bind
        (fun u => ((List.range B).filterMap (fun j => optIter f j u)
          : Multiset (Tuple T n'))) with hW
    have hWcard : Multiset.card W
        ≤ Multiset.card ((show Multiset (Tuple T n') from q₀.evaluatePlain D γ)
            + C) * B := by
      rw [hW, Multiset.card_bind]
      refine le_trans (Multiset.sum_le_card_nsmul _ B fun x hx => ?_) ?_
      · obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hx
        show Multiset.card (((List.range B).filterMap
          (fun j => optIter f j u) : List (Tuple T n')) : Multiset (Tuple T n')) ≤ B
        rw [Multiset.coe_card]
        exact le_trans (List.length_filterMap_le _ _) (le_of_eq List.length_range)
      · rw [Multiset.card_map, smul_eq_mul]
    have hround : ∀ j, ∀ v ∈ (fun X : Multiset (Tuple T n') =>
        (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup)^[j]
          (0 : Multiset (Tuple T n')),
        ∃ u ∈ (show Multiset (Tuple T n') from q₀.evaluatePlain D γ) + C,
          ∃ j' : ℕ, (j' < B) ∧ optIter f j' u = some v := by
      intro j
      induction j with
      | zero => intro v hvm; exact absurd hvm (Multiset.notMem_zero v)
      | succ j ih =>
        intro v hvm
        rw [Function.iterate_succ_apply'] at hvm
        have hv' := hvm
        rw [hstep] at hv'
        rcases Multiset.mem_add.mp (Multiset.mem_dedup.mp hv') with h | h
        · exact ⟨v, Multiset.mem_add.mpr (Or.inl h), 0, by rw [hB, recBound]; omega, rfl⟩
        · rcases Multiset.mem_add.mp h with h | h
          · obtain ⟨x, hx, hfx⟩ := (Multiset.mem_filterMap _ _).mp h
            obtain ⟨u, hu, j', -, hj'⟩ := ih x hx
            have hnext : optIter f (j' + 1) u = some v := by
              show (optIter f j' u).bind f = some v
              rw [hj']
              exact hfx
            obtain ⟨j'', hj'', heq⟩ := optIter_exists_lt (rowBox u γ q₁.consts)
              (rowBox_closed hv) (self_mem_rowBox u γ q₁.consts) (j' + 1)
            refine ⟨u, hu, j'', ?_, heq.trans hnext⟩
            have := card_rowBox_le u γ q₁.consts
            rw [hB]
            omega
          · exact ⟨v, Multiset.mem_add.mpr (Or.inr h), 0, by rw [hB, recBound]; omega, rfl⟩
    have hsub : muFix (fun X => (q₀.evaluatePlain D γ
        + q₁.evaluatePlain (D.assign s X) γ).dedup) ⊆ W := by
      intro v hvm
      rw [muFix, muIter_eq_iterate] at hvm
      obtain ⟨u, hu, j', hj', hopt⟩ := hround _ v hvm
      rw [hW]
      refine Multiset.mem_bind.mpr ⟨u, hu, ?_⟩
      rw [Multiset.mem_coe]
      exact List.mem_filterMap.mpr ⟨j', List.mem_range.mpr hj', hopt⟩
    have hnodup : (muFix (fun X => (q₀.evaluatePlain D γ
        + q₁.evaluatePlain (D.assign s X) γ).dedup)).Nodup := by
      rw [muFix, muIter_eq_iterate]
      exact nodup_iterate_dedup _ _
    refine le_trans (Multiset.card_le_card ((Multiset.le_iff_subset hnodup).mpr hsub))
      (le_trans hWcard ?_)
    rw [Multiset.card_add, Nat.mul_comm, Nat.mul_assoc]
    refine Nat.mul_le_mul_left B ?_
    rw [Nat.add_mul]
    exact Nat.add_le_add hM hCcard
  | Gamma is ts fs q keep ord ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 hr hsig D γ hs)
  | GammaScalar ts fs q ord ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound, one_mul]
    exact Nat.succ_le_succ (Nat.zero_le _)
  | GammaNest is his p f q ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact le_trans (le_trans (Multiset.card_dedup_le _)
      (le_of_eq (Multiset.card_map _ _))) (ih hq.2 hr hsig D γ hs)
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      Multiset.card_map]
    exact ih hq.2 hr hsig D γ hs
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq hr hsig D γ hs
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.sizeBound,
      OccFam.card_toMultiset]
    exact le_trans (le_of_eq (OccFam.size_ofSorted _)) (ih hq.2 hr hsig D γ hs)

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
    (h : ∀ x, x ∈ s → f x ≤ g x) : (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => exact le_refl 0
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
      Multiset.sum_cons]
    exact Nat.add_le_add (h x (Multiset.mem_cons_self x s))
      (ih (fun y hy => h y (Multiset.mem_cons_of_mem hy)))

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
theorem Multiset.count_bind_append_le {n m : ℕ} (r : Multiset (Tuple T n))
    (g : Tuple T n → Relation T m) {b₁ b₂ : ℕ}
    (h₁ : ∀ x, Multiset.count x r ≤ b₁)
    (h₂ : ∀ a, a ∈ r → ∀ y, Multiset.count y (g a) ≤ b₂)
    (u : Tuple T (n + m)) :
    Multiset.count u (Multiset.bind r (fun a =>
        Multiset.map (fun v => (Fin.append a v : Tuple T (n + m))) (g a)))
      ≤ b₁ * b₂ := by
  classical
  rw [Multiset.count_bind]
  refine le_trans (Multiset.sum_map_le r _
    (fun a => if a = (fun i => u (Fin.castAdd m i)) then b₂ else 0)
    (fun a hmem => ?_)) ?_
  · rw [Multiset.count_map]
    by_cases ha : a = (fun i => u (Fin.castAdd m i))
    · rw [ite_eq_left ha]
      refine le_trans (Multiset.card_le_card (Multiset.monotone_filter_right
        (g a) (q := fun v => (fun j => u (Fin.natAdd n j)) = v)
        (fun v hv => ?_))) ?_
      · exact (funext fun j => by rw [hv, Fin.append_right] :
          (fun j => u (Fin.natAdd n j)) = v)
      · exact le_trans
          (le_of_eq (Multiset.count_eq_card_filter_eq (g a) _).symm)
          (h₂ a hmem _)
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
def AggQueryIn.multBound : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → ℕ
  | _, _, _, _, .Rel _ _ => 1
  | _, _, _, _, .Hole _ _ => 1
  | _, _, _, _, .Empty => 0
  | _, _, _, _, .Proj _ _ => 0
  | _, _, _, _, .Sel _ q _ => q.multBound
  | _, _, _, _, .Prod q₁ q₂ => q₁.multBound * q₂.multBound
  | _, _, _, _, .Apply q₁ q₂ => q₁.multBound * q₂.multBound
  | _, _, _, _, .Sum q₁ q₂ => q₁.multBound + q₂.multBound
  | _, _, _, _, .Dedup _ => 1
  | _, _, _, _, .Diff q₁ _ => q₁.multBound
  | _, _, _, _, .Explode _ _ q => q.multBound
  | _, _, _, _, .Retag _ q => q.multBound
  | _, _, _, _, .Mu _ q₀ _ => q₀.multBound
  | _, _, _, _, .MuSet _ _ _ => 1
  | _, _, _, _, .Gamma _ _ _ _ _ _ => 1
  | _, _, _, _, .GammaScalar _ _ _ _ => 1
  | _, _, _, _, .GammaNest _ _ _ _ _ => 1
  | _, _, _, _, .GammaTok _ _ _ _ _ _ _ => 1
  | _, _, _, _, .ProvSum _ _ _ _ => 1
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.multBound
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.multBound

/-! ### A recursive term without `Π` reads the previous round tuple by tuple

What the projection row needs of a recursion is that the rounds of a bag
recursion cannot settle past the first: without `Π`, a recursive term
keeps a tuple of the previous round as it is or drops it, and adds
tuples that do not depend on the round at all. So a tuple of one round
is a tuple of the next, a non-empty round is followed by a non-empty one,
and a recursion whose rounds settle settles at once – its value is its
base, whose multiplicities the base's own bound covers. The statement
below is the *affine* form of that: the term's output, as a set, is the
previous round read through a block of the output's columns, cut down by
a condition on the output row, together with a set of rows that read no
round. The block is tracked by its offset, which is what shows it to be
the whole row where the arities agree. -/

omit [ValueType T] in
theorem Multiset.Mem_iff {α : Type} (s : Multiset α) (a : α) :
    a ∈ s ↔ Multiset.Mem s a := Iff.rfl

omit [ValueType T] in
theorem Multiset.Mem_add {α : Type} (s t : Multiset α) (a : α) :
    Multiset.Mem (s + t) a ↔ Multiset.Mem s a ∨ Multiset.Mem t a :=
  Multiset.mem_add

omit [ValueType T] in
theorem Multiset.Mem_filter {α : Type} (p : α → Prop) [DecidablePred p]
    (s : Multiset α) (a : α) :
    Multiset.Mem (Multiset.filter p s) a ↔ Multiset.Mem s a ∧ p a :=
  Multiset.mem_filter

omit [ValueType T] in
/-- A row of a product is a row of each factor. -/
theorem Relation.Mem_hMul {n m : ℕ} (r₁ : Relation T n) (r₂ : Relation T m)
    (u : Tuple T (n + m)) :
    Multiset.Mem (r₁ * r₂) u
      ↔ Multiset.Mem r₁ (fun i => u (Fin.castAdd m i))
        ∧ Multiset.Mem r₂ (fun i => u (Fin.natAdd n i)) := by
  rw [← Multiset.Mem_iff, Relation.hMul_eq_bind, Multiset.mem_bind]
  constructor
  · rintro ⟨x, hx, hu⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hu
    have hl : (fun i => Fin.append x y (Fin.castAdd m i)) = x :=
      funext (Fin.append_left x y)
    have hr : (fun i => Fin.append x y (Fin.natAdd n i)) = y :=
      funext (Fin.append_right x y)
    rw [hl, hr]
    exact ⟨hx, hy⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, h₁, Multiset.mem_map.mpr ⟨_, h₂, Fin.append_castAdd_natAdd⟩⟩

omit [ValueType T] in
/-- A row of an apply is a row of the left side and a row of the right
side read at it. -/
theorem Relation.Mem_applyBind {n m : ℕ} (r₁ : Relation T n)
    (f : Tuple T n → Relation T m) (u : Tuple T (n + m)) :
    Multiset.Mem (Multiset.bind r₁ (fun x =>
        Multiset.map (fun v => (Fin.append x v : Tuple T (n + m))) (f x))) u
      ↔ Multiset.Mem r₁ (fun i => u (Fin.castAdd m i))
        ∧ Multiset.Mem (f (fun i => u (Fin.castAdd m i)))
            (fun i => u (Fin.natAdd n i)) := by
  rw [← Multiset.Mem_iff, Multiset.mem_bind]
  constructor
  · rintro ⟨x, hx, hu⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hu
    have hl : (fun i => Fin.append x y (Fin.castAdd m i)) = x :=
      funext (Fin.append_left x y)
    have hr : (fun i => Fin.append x y (Fin.natAdd n i)) = y :=
      funext (Fin.append_right x y)
    rw [hl, hr]
    exact ⟨hx, hy⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, h₁, Multiset.mem_map.mpr ⟨_, h₂, Fin.append_castAdd_natAdd⟩⟩

omit [ValueType T] in
private theorem affine_and_right {A B C P : Prop} :
    (((A ∧ B) ∨ C) ∧ P) ↔ ((A ∧ (B ∧ P)) ∨ (C ∧ P)) := by tauto

omit [ValueType T] in
private theorem affine_and_left {A B C P : Prop} :
    (P ∧ ((A ∧ B) ∨ C)) ↔ ((A ∧ (P ∧ B)) ∨ (P ∧ C)) := by tauto

omit [ValueType T] in
private theorem affine_or_right {A B C P : Prop} :
    (((A ∧ B) ∨ C) ∨ P) ↔ ((A ∧ B) ∨ (C ∨ P)) := by tauto

omit [ValueType T] in
private theorem affine_or_left {A B C P : Prop} :
    (P ∨ ((A ∧ B) ∨ C)) ↔ ((A ∧ B) ∨ (P ∨ C)) := by tauto

/-- **Without `Π`, a recursive term reads the recursive relation tuple by
tuple**: its rows are the rows `u` whose block `β u` is a row of the
relation and which satisfy a condition `a`, together with rows `k` that
read nothing of it. The block is a run of `m` consecutive columns at
offset `off`, recorded wherever `a` holds. -/
theorem AggQueryIn.affine_of_body {S : Set OpKind} (hpr : OpKind.proj ∉ S)
    {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      l = [(s, m)] → q.usesOnly S → q.noMention s → ∀ (D : Database T) (γ : Fin c → T),
      ∃ (β : Tuple T n → Tuple T m) (a k : Tuple T n → Prop) (off : ℕ),
        (∀ u, a u → ∀ i : Fin m,
          ∃ h : i.val + off < n, β u i = u ⟨i.val + off, h⟩)
        ∧ ∀ (X : Relation T m) (u : Tuple T n),
          Multiset.Mem (q.evaluatePlain (D.assign s X) γ) u
            ↔ ((Multiset.Mem X (β u) ∧ a u) ∨ k u) := by
  intro c n κ l q
  induction q with
  | Rel n' s' => exact fun hl => absurd hl (by simp)
  | Hole n' s' =>
    intro hl _ _ D γ
    have hs : s' = s := (Prod.mk.inj (List.singleton_inj.mp hl)).1
    have hn : n' = m := (Prod.mk.inj (List.singleton_inj.mp hl)).2
    subst hs; subst hn
    refine ⟨id, fun _ => True, fun _ => False, 0,
      fun u _ i => ⟨by omega, congrArg u (Fin.ext (Nat.add_zero _).symm)⟩,
      fun X u => ?_⟩
    show Multiset.Mem (match (D.assign s' X).find n' s' with
      | none => (0 : Multiset (Tuple T n')) | some r => r) u ↔ _
    rw [Database.find_assign]
    show Multiset.Mem X u ↔ _
    simp only [id, and_true, or_false]
  | Empty => exact fun hl => absurd hl (by simp)
  | Proj ps q ih => intro _ hq; exact absurd hq.1.1 hpr
  | Sel φ q _ ih =>
    intro hl hq hr D γ
    obtain ⟨β, a, k, off, hβ, h⟩ := ih hl hq.2 hr D γ
    refine ⟨β, fun u => a u ∧ φ.holdsPlain u γ,
      fun u => k u ∧ φ.holdsPlain u γ, off, fun u hu => hβ u hu.1,
      fun X u => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [Multiset.Mem_filter, h X u]
    exact affine_and_right
  | Prod q₁ q₂ ih₁ ih₂ =>
    rename_i n₁ n₂ κ₁ κ₂ l₁ l₂
    intro hl hq hr D γ
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      obtain ⟨β, a, k, off, hβ, h⟩ := ih₁ h₁ hq.2.1 hr.1 D γ
      refine ⟨fun u => β (fun i => u (Fin.castAdd _ i)),
        fun u => a (fun i => u (Fin.castAdd _ i))
          ∧ Multiset.Mem (q₂.evaluatePlain D γ) (fun i => u (Fin.natAdd _ i)),
        fun u => k (fun i => u (Fin.castAdd _ i))
          ∧ Multiset.Mem (q₂.evaluatePlain D γ) (fun i => u (Fin.natAdd _ i)),
        off, fun u hu i => ?_, fun X u => ?_⟩
      · obtain ⟨hlt, he⟩ := hβ _ hu.1 i
        exact ⟨by omega, he.trans (congrArg u (Fin.ext (Fin.val_castAdd _ _)))⟩
      · simp only [AggQueryIn.evaluatePlain]
        rw [Relation.Mem_hMul, h X,
          AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hr.2 D γ]
        exact affine_and_right
    · subst h₁
      obtain ⟨β, a, k, off, hβ, h⟩ := ih₂ h₂ hq.2.2 hr.2 D γ
      refine ⟨fun u => β (fun i => u (Fin.natAdd _ i)),
        fun u => Multiset.Mem (q₁.evaluatePlain D γ) (fun i => u (Fin.castAdd _ i))
          ∧ a (fun i => u (Fin.natAdd _ i)),
        fun u => Multiset.Mem (q₁.evaluatePlain D γ) (fun i => u (Fin.castAdd _ i))
          ∧ k (fun i => u (Fin.natAdd _ i)),
        off + n₁, fun u hu i => ?_, fun X u => ?_⟩
      · obtain ⟨hlt, he⟩ := hβ _ hu.2 i
        refine ⟨by omega, he.trans (congrArg u (Fin.ext ?_))⟩
        rw [Fin.val_natAdd]
        show n₁ + (i.val + off) = i.val + (off + n₁)
        omega
      · simp only [AggQueryIn.evaluatePlain]
        rw [Relation.Mem_hMul, h X,
          AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hr.1 D γ]
        exact affine_and_left
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hl hq hr D γ
    obtain ⟨β, a, k, off, hβ, h⟩ := ih₁ hl hq.2.1 hr.1 D γ
    refine ⟨fun u => β (fun i => u (Fin.castAdd _ i)),
      fun u => a (fun i => u (Fin.castAdd _ i))
        ∧ Multiset.Mem (q₂.evaluatePlain D (Fin.append (fun i => u (Fin.castAdd _ i)) γ))
            (fun i => u (Fin.natAdd _ i)),
      fun u => k (fun i => u (Fin.castAdd _ i))
        ∧ Multiset.Mem (q₂.evaluatePlain D (Fin.append (fun i => u (Fin.castAdd _ i)) γ))
            (fun i => u (Fin.natAdd _ i)),
      off, fun u hu i => ?_, fun X u => ?_⟩
    · obtain ⟨hlt, he⟩ := hβ _ hu.1 i
      exact ⟨by omega, he.trans (congrArg u (Fin.ext (Fin.val_castAdd _ _)))⟩
    · simp only [AggQueryIn.evaluatePlain]
      rw [Relation.Mem_applyBind, h X,
        AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hr.2 D]
      exact affine_and_right
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hl hq hr D γ
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      obtain ⟨β, a, k, off, hβ, h⟩ := ih₁ h₁ hq.2.1 hr.1 D γ
      refine ⟨β, a, fun u => k u ∨ Multiset.Mem (q₂.evaluatePlain D γ) u, off,
        hβ, fun X u => ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [Multiset.Mem_add, h X u,
        AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hr.2 D γ]
      exact affine_or_right
    · subst h₁
      obtain ⟨β, a, k, off, hβ, h⟩ := ih₂ h₂ hq.2.2 hr.2 D γ
      refine ⟨β, a, fun u => Multiset.Mem (q₁.evaluatePlain D γ) u ∨ k u, off,
        hβ, fun X u => ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [Multiset.Mem_add, h X u,
        AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hr.1 D γ]
      exact affine_or_left
  | Dedup q ih => exact fun hl => absurd hl (by simp)
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hl => absurd hl (by simp)
  | Explode k hk q ih => intro hl hq hr D γ; exact ih hl hq hr D γ
  | Retag hk q ih => intro hl hq hr D γ; exact ih hl hq hr D γ
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | Gamma is ts fs q keep ord ih => exact fun hl => absurd hl (by simp)
  | GammaScalar ts fs q ord ih => exact fun hl => absurd hl (by simp)
  | GammaNest is his p f q ih => exact fun hl => absurd hl (by simp)
  | ProvSum is his t q ih => exact fun hl => absurd hl (by simp)
  | GammaTok is his ts fs a q keep ih => exact fun hl => absurd hl (by simp)
  | Win P O o w t f q hrr dist keep ih => exact fun hl => absurd hl (by simp)
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hl => absurd hl (by simp)

omit [ValueType T] in
/-- **A round function reading the previous round tuple by tuple keeps a
non-empty round non-empty**: a row of one round is, by the block being
the whole row, a row of the next. -/
theorem step_ne_zero_of_affine {m : ℕ}
    {step : Multiset (Tuple T m) → Multiset (Tuple T m)}
    (β : Tuple T m → Tuple T m) (a k : Tuple T m → Prop) (off : ℕ)
    (hβ : ∀ u, a u → ∀ i : Fin m,
      ∃ h : i.val + off < m, β u i = u ⟨i.val + off, h⟩)
    (h : ∀ (X : Multiset (Tuple T m)) u,
      Multiset.Mem (step X) u ↔ ((Multiset.Mem X (β u) ∧ a u) ∨ k u))
    {X : Multiset (Tuple T m)} (hX : step X ≠ 0) : step (step X) ≠ 0 := by
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero hX
  intro h0
  have hβu : ∀ u, a u → β u = u := by
    intro u hau
    funext i
    obtain ⟨hlt, he⟩ := hβ u hau i
    have hi := i.isLt
    obtain ⟨hlt', -⟩ := hβ u hau ⟨m - 1, by omega⟩
    have hlt'' : LT.lt (HSub.hSub m 1 + off) m := hlt'
    have hoff : off = 0 := by omega
    rw [he]
    exact congrArg u (Fin.ext (by simp [hoff]))
  have hmem : Multiset.Mem (step (step X)) u := by
    rw [h]
    rcases (h X u).mp hu with ⟨hb, ha⟩ | hk
    · exact Or.inl ⟨by rw [hβu u ha]; exact hu, ha⟩
    · exact Or.inr hk
  rw [h0] at hmem
  exact Multiset.notMem_zero u hmem

/-- **So a bag recursion with such a round function settles only at its
base**: a non-empty first round would be followed by non-empty rounds
forever. -/
theorem step_eq_zero_of_muSettles_affine {m : ℕ}
    {step : Multiset (Tuple T m) → Multiset (Tuple T m)}
    (β : Tuple T m → Tuple T m) (a k : Tuple T m → Prop) (off : ℕ)
    (hβ : ∀ u, a u → ∀ i : Fin m,
      ∃ h : i.val + off < m, β u i = u ⟨i.val + off, h⟩)
    (h : ∀ (X : Multiset (Tuple T m)) u,
      Multiset.Mem (step X) u ↔ ((Multiset.Mem X (β u) ∧ a u) ∨ k u))
    {M : Multiset (Tuple T m)} (hs : MuSettles step M) : step M = 0 := by
  obtain ⟨j, hj⟩ := hs
  by_contra hne
  have hall : ∀ j, step^[j + 1] M ≠ 0 := by
    intro j
    induction j with
    | zero => exact hne
    | succ j ih =>
      rw [Function.iterate_succ_apply'] at ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact step_ne_zero_of_affine β a k off hβ h ih
  exact hall j hj

/-- **Without `Π`, multiplicities are bounded by the query**, the
recursions included wherever they are defined: a bag recursion settles
at its base, and a set recursion's rounds are duplicate-free. -/
theorem AggQueryIn.count_le_multBound {S : Set OpKind}
    (hpr : OpKind.proj ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.hygienic → ∀ (D : Database T), Database.Nodup D →
      ∀ (γ : Fin c → T), q.SettlesAt D γ → ∀ (u : Tuple T n),
      Multiset.count u (q.evaluatePlain D γ) ≤ q.multBound := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ D hD γ _ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    cases hf : D.find n s with
    | none => exact Nat.zero_le 1
    | some rn =>
      exact Multiset.nodup_iff_count_le_one.mp (hD n s rn hf) u
  | Hole n s =>
    intro _ _ D hD γ _ u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    cases hf : D.find n s with
    | none => exact Nat.zero_le 1
    | some rn =>
      exact Multiset.nodup_iff_count_le_one.mp (hD n s rn hf) u
  | Empty => intro _ _ D hD γ _ u; exact Nat.zero_le 0
  | Proj ps q ih => intro hq; exact absurd hq.1.1 hpr
  | Sel φ q _ ih =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact le_trans (Multiset.count_le_of_le u (Multiset.filter_le _ _))
      (ih hq.2 hr D hD γ hs u)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    rw [Relation.hMul_eq_bind]
    exact Multiset.count_bind_append_le _ _
      (fun x => ih₁ hq.2.1 hr.1 D hD γ hs.1 x)
      (fun _ _ y => ih₂ hq.2.2 hr.2 D hD γ hs.2 y) u
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_bind_append_le _ _
      (fun x => ih₁ hq.2.1 hr.1 D hD γ hs.1 x)
      (fun a ha y => ih₂ hq.2.2 hr.2 D hD (Fin.append a γ) (hs.2 a ha) y) u
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    refine le_trans (le_of_eq (Multiset.count_add u _ _)) ?_
    exact Nat.add_le_add (ih₁ hq.2.1 hr.1 D hD γ hs.1 u)
      (ih₂ hq.2.2 hr.2 D hD γ hs.2 u)
  | Dedup q ih =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.nodup_iff_count_le_one.mp (Multiset.nodup_dedup _) u
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact le_trans (Multiset.count_le_of_le u (Multiset.filter_le _ _))
      (ih₁ hq.2.1 hr.1 D hD γ hs.1 u)
  | Explode k hk q ih => intro hq hr D hD γ hs u; exact ih hq hr D hD γ hs u
  | Retag hk q ih => intro hq hr D hD γ hs u; exact ih hq hr D hD γ hs u
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hq hr D hD γ hs u
    obtain ⟨β, a, k, off, hβ, h⟩ :=
      AggQueryIn.affine_of_body hpr q₁ rfl hq.2.2 hr.2.1 D γ
    have h0 : q₁.evaluatePlain (D.assign s (q₀.evaluatePlain D γ)) γ = 0 :=
      step_eq_zero_of_muSettles_affine
        (step := fun X => q₁.evaluatePlain (D.assign s X) γ) β a k off hβ h
        hs.2.2.1
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    rw [muSumFix_eq_of_empty hs.2.1 (k := 0) (by simpa using h0)]
    exact ih₀ hq.2.1 hr.2.2.1 D hD γ hs.1 u
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    rw [muFix, muIter_eq_iterate]
    exact Multiset.nodup_iff_count_le_one.mp (nodup_iterate_dedup _ _) u
  | Gamma is ts fs q keep ord ih =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd _ k)) (fun g => funext fun k => by
        rw [Fin.append_left]) u
  | GammaScalar ts fs q ord ih =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact le_trans (Multiset.count_le_card u _) (le_of_eq rfl)
  | GammaNest is his p f q ih =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_dedup_le _ _
      (fun v k => v (Fin.castAdd _ k)) (fun g => funext fun k => by
        rw [Fin.append_left]) u
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    exact Multiset.count_map_snoc_le _ _ (fun x => ih hq.2 hr D hD γ hs x) u
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq hr D hD γ hs u
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.multBound]
    refine OccFam.count_mk_toMultiset_le _ _
      (fun v k => v k.castSucc) (fun i => funext fun k => by
        rw [Fin.snoc_castSucc]) (fun x => ?_) u
    rw [OccFam.toMultiset_ofSorted]
    exact ih hq.2 hr D hD γ hs x

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
    {κ₂ : Fin n₂ → ColKind} {l : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁) l)
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
`0` on the left, the domain's non-zero value on the right – unites them,
groups by the whole tuple, and counts the tags carrying that value. The
count is `0` exactly on the tuples `q₂` does not hold, and a product
with the keys matched keeps the copies of those tuples.

The aggregate is a *count*: the grouping's one aggregate counts, through
a `FILTER` clause, the rows carrying the right side's tag. So what the
construction asks of it is `SeqAggFunc.Counts` – SQL's `count(e)`, which
`sec:basis` assumes among the aggregates – and nothing about a sum. The
tag it keys on is the value domain's own non-zero value
(`ValueType.nonzero`), so the construction asks nothing of the domain
either. -/

section Difference

variable {c k : ℕ}

/-- The projection that tags a row with a constant: its own columns, and
one more holding `a`. The column constructor is outside the case
analysis, so every output column is regular by reduction. -/
def AggQueryIn.tagCols (a : T) :
    Tuple (ProjColIn T c (ColKind.allReg k)) (k + 1) :=
  fun j => .term (Fin.lastCases (TermGIn.const a)
    (fun i : Fin k => TermGIn.index i rfl) j)

/-- **The two sides tagged and united**: every row of `q₁` with `0`,
every row of `q₂` with the domain's non-zero value. -/
def AggQueryIn.tagUnion (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c (k + 1) (ColKind.allReg (k + 1)) :=
  .Sum (.Proj (AggQueryIn.tagCols 0) q₁)
    (.Proj (AggQueryIn.tagCols ValueType.nonzero) q₂)

/-- **The clause that keeps the right side's rows**: the ones whose tag
column holds the non-zero value. It is an `IS NOT DISTINCT FROM`, so it
is never unknown, and it reads a regular column as a `FILTER` clause
must. -/
def AggQueryIn.rightTag : Selection T (k + 1) :=
  .BT (.SYNEQ (TermIn.index (Fin.last k)) (TermIn.const ValueType.nonzero))

/-- **One row per distinct tuple, carrying the count of the right side's
copies of it.** -/
def AggQueryIn.tagAgg (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c (k + 1)
      (Fin.append (fun _ : Fin k => ColKind.reg)
        (fun _ : Fin 1 => ColKind.agg)) :=
  .Gamma (fun i : Fin k => i.castSucc) ![TermIn.index (Fin.last k)] ![cnt]
    (AggQueryIn.tagUnion q₁ q₂) ![some AggQueryIn.rightTag]

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
agree, and the tag count is `0`. -/
def AggQueryIn.notInCond : GenPredIn T c (notInKinds k) :=
  .and ((keyJoinCond (T' := T) (fun i : Fin k => Fin.castAdd (k + 1) i)
      (fun i : Fin k => Fin.natAdd k (Fin.castAdd 1 i))
      (notInKinds_left k) (notInKinds_key k)).substMap (fun j : Fin 0 => j.elim0))
    (.aggCmp (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))) (notInKinds_agg k)
      CompOp.syneq (.const 0))

/-- **The difference read as a `NOT IN`**: the copies of `q₁` whose tuple
the tag count reads `0` on. -/
def AggQueryIn.notInDiff (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c k (ColKind.allReg k) :=
  .Proj (fun i : Fin k =>
      .term (TermGIn.index (Fin.castAdd (k + 1) i) (notInKinds_left k i)))
    (.Sel AggQueryIn.notInCond (.Prod q₁ (AggQueryIn.tagAgg cnt q₁ q₂)))

/-- **What the `NOT IN` form uses**: a projection, a selection, a
product, an aggregation and a union – the basis classes, which is the
point of the identity. -/
theorem AggQueryIn.usesOnly_notInDiff {S : Set OpKind}
    (cnt : SeqAggFunc T) {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (hp : OpKind.proj ∈ S) (hs : OpKind.sel ∈ S) (hx : OpKind.prod ∈ S)
    (hu : OpKind.union ∈ S) (hg : OpKind.gamma ∈ S) (h₁ : q₁.usesOnly S)
    (h₂ : q₂.usesOnly S) : (AggQueryIn.notInDiff cnt q₁ q₂).usesOnly S :=
  ⟨⟨hp, fun _ => rfl⟩, hs, hx, h₁, hg, hu, ⟨⟨hp, fun _ => rfl⟩, h₁⟩,
    ⟨⟨hp, fun _ => rfl⟩, h₂⟩⟩

/-- **The `NOT IN` form names the relations its two sides name.** -/
theorem AggQueryIn.overSchema_notInDiff {sch : Schema}
    (cnt : SeqAggFunc T) {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (h₁ : q₁.overSchema sch) (h₂ : q₂.overSchema sch) :
    (AggQueryIn.notInDiff cnt q₁ q₂).overSchema sch :=
  ⟨h₁, h₁, h₂⟩

/-- Tagging a row appends the constant to it. -/
private theorem tagCols_eval {γ : Fin c → T} (a : T) (u : Tuple T k) (j : Fin (k + 1)) :
    (AggQueryIn.tagCols (T := T) (c := c) (k := k) a j).evalPlain u γ
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
theorem AggQueryIn.evaluatePlain_tagUnion
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.tagUnion q₁ q₂).evaluatePlain D γ
      = (q₁.evaluatePlain D γ).map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
        + (q₂.evaluatePlain D γ).map
            (fun u => (Fin.snoc u ValueType.nonzero
              : Tuple T (k + 1))) := by
  show Multiset.map _ (q₁.evaluatePlain D γ)
      + Multiset.map _ (q₂.evaluatePlain D γ) = _
  exact congrArg₂ (· + ·)
    (Multiset.map_congr rfl (fun u _ => funext (fun j => tagCols_eval 0 u j)))
    (Multiset.map_congr rfl (fun u _ =>
      funext (fun j => tagCols_eval ValueType.nonzero u j)))

/-- **The keys the grouping emits**: the distinct tuples of the two sides
together, the tag column being dropped by the key projection. -/
theorem AggQueryIn.tagAgg_keys (r₁ r₂ : Multiset (Tuple T k)) :
    ((r₁.map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
        + r₂.map (fun u => (Fin.snoc u ValueType.nonzero
            : Tuple T (k + 1)))).map
      (fun v => (fun i => v (Fin.castSucc i) : Tuple T k))).dedup
      = (r₁ + r₂).dedup := by
  refine congrArg Multiset.dedup ?_
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Eq.trans (Multiset.map_congr rfl (fun u _ => funext (fun i => by
      show (Fin.snoc u 0 : Tuple T (k + 1)) (Fin.castSucc i) = u i
      rw [Fin.snoc_castSucc]))) (Multiset.map_id' r₁)
  · exact Eq.trans (Multiset.map_congr rfl (fun u _ => funext (fun i => by
      show (Fin.snoc u ValueType.nonzero : Tuple T (k + 1)) (Fin.castSucc i)
          = u i
      rw [Fin.snoc_castSucc]))) (Multiset.map_id' r₂)

/-- **The rows the clause keeps**: those whose tag column holds the
non-zero value. -/
theorem AggQueryIn.rightTag_keeps (v : Tuple T (k + 1)) :
    (AggQueryIn.rightTag (T := T) (k := k)).keeps v = true
      ↔ v (Fin.last k) = ValueType.nonzero := by
  rw [Selection.keeps, decide_eq_true_eq]
  show CompOp.syneq.eval3 ((TermIn.index (Fin.last k) : Term T (k + 1)).eval v)
      ((TermIn.const ValueType.nonzero : Term T (k + 1)).eval v)
    = Kleene.true ↔ _
  rw [CompOp.syneq_eval3_eq_true_iff]
  exact Iff.rfl

/-- **What the tag count reads on a tuple**: `0` exactly when the right
side holds no copy of it. The clause keeps the copies carrying the right
side's tag, and the term it counts is that tag, which is a value and not
a null – so the count is `0` exactly when the clause keeps nothing. -/
theorem AggQueryIn.tagAgg_zero_iff (cnt : SeqAggFunc T)
    (hc : SeqAggFunc.Counts cnt) (r₁ r₂ : Multiset (Tuple T k))
    (g : Tuple T k) :
    cnt (((Relation.groupSeq (fun i : Fin k => i.castSucc)
        (r₁.map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
          + r₂.map (fun u => (Fin.snoc u ValueType.nonzero
              : Tuple T (k + 1)))) g).filter
        (AggQueryIn.rightTag (T := T) (k := k)).keeps).map
        (fun v => v (Fin.last k))) = 0
      ↔ g ∉ r₂ := by
  rw [hc.eq_zero]
  constructor
  · intro h hg
    have hnn : ValueType.isNull (ValueType.nonzero : T) = true := by
      refine h _ (List.mem_map.mpr
        ⟨(Fin.snoc g ValueType.nonzero : Tuple T (k + 1)), ?_, ?_⟩)
      · rw [List.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [Relation.groupSeq, mem_sortList, Multiset.mem_filter]
          refine ⟨Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ hg)),
            fun i => ?_⟩
          show (Fin.snoc g ValueType.nonzero : Tuple T (k + 1))
              (Fin.castSucc i) = g i
          rw [Fin.snoc_castSucc]
        · rw [AggQueryIn.rightTag_keeps]
          show (Fin.snoc g ValueType.nonzero : Tuple T (k + 1)) (Fin.last k)
              = ValueType.nonzero
          rw [Fin.snoc_last]
      · show (Fin.snoc g ValueType.nonzero : Tuple T (k + 1)) (Fin.last k)
            = ValueType.nonzero
        rw [Fin.snoc_last]
    rw [ValueType.isNull_nonzero] at hnn
    exact Bool.noConfusion hnn
  · intro hg x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_filter] at hv
    obtain ⟨hv, hkeep⟩ := hv
    rw [AggQueryIn.rightTag_keeps] at hkeep
    rw [Relation.groupSeq, mem_sortList, Multiset.mem_filter] at hv
    obtain ⟨hmem, hkey⟩ := hv
    rcases Multiset.mem_add.mp hmem with h1 | h2
    · obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp h1
      refine absurd ?_ (ValueType.nonzero_ne_zero (T := T))
      rw [← hkeep, Fin.snoc_last]
    · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp h2
      refine absurd ?_ hg
      have hug : u = g := funext (fun i => by
        have hi : (Fin.snoc u ValueType.nonzero : Tuple T (k + 1))
            (Fin.castSucc i) = g i := hkey i
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

/-- **What the product with the tag count keeps**: one copy of each
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

The aggregate is a parameter, and what the construction asks of it is
`SeqAggFunc.Counts`: it counts the rows a `FILTER` clause keeps, which
are the copies carrying the right side's tag. So the only aggregate the
identity needs is SQL's `count`. -/
theorem AggQueryIn.diff_plainEquiv_notIn (cnt : SeqAggFunc T)
    (hc : SeqAggFunc.Counts cnt)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    (AggQueryIn.Diff q₁ q₂).PlainEquiv (AggQueryIn.notInDiff cnt q₁ q₂) := by
  intro D γ
  -- the two sides' rows, as multisets, which is what `−` reads
  set r₁ : Multiset (Tuple T k) := q₁.evaluatePlain D γ with hr₁
  set r₂ : Multiset (Tuple T k) := q₂.evaluatePlain D γ with hr₂
  -- the tagged union: the rows of `q₁` with `0` and those of `q₂` with `a`
  set tagged : Multiset (Fin (k + 1) → T) :=
    r₁.map (fun u => (Fin.snoc u 0 : Tuple T (k + 1)))
      + r₂.map (fun u => (Fin.snoc u ValueType.nonzero
          : Tuple T (k + 1))) with htagged
  -- the tag of a tuple: the count of the tags the clause keeps
  set val : (Fin k → T) → T := fun g =>
    cnt (((Relation.groupSeq (fun i : Fin k => i.castSucc) tagged g).filter
      (AggQueryIn.rightTag (T := T) (k := k)).keeps).map
      (fun v => v (Fin.last k))) with hval
  -- the grouping's rows: one per distinct tuple, carrying its tag
  have hDr : (AggQueryIn.tagAgg cnt q₁ q₂).evaluatePlain D γ
      = ((r₁ + r₂).dedup).map (fun g =>
          (Fin.append g (fun _ : Fin 1 => val g) : Fin (k + 1) → T)) := by
    show Multiset.map _ (Multiset.dedup (Multiset.map _
        ((AggQueryIn.tagUnion q₁ q₂).evaluatePlain D γ))) = _
    rw [AggQueryIn.evaluatePlain_tagUnion]
    refine congrArg₂ Multiset.map (funext (fun g => ?_))
      (AggQueryIn.tagAgg_keys _ _)
    refine congrArg (Fin.append g) (funext (fun j => ?_))
    rw [Subsingleton.elim j 0]
    rfl
  -- the selection's condition, read on a row of the product
  have hcond : ∀ w : Tuple T (k + (k + 1)),
      (AggQueryIn.notInCond (T := T) (c := c) (k := k)).holdsPlain w γ
        ↔ ((∀ i : Fin k, w (Fin.castAdd (k + 1) i)
              = w (Fin.natAdd k (Fin.castAdd 1 i)))
            ∧ w (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))) = 0) := by
    intro w
    rw [AggQueryIn.notInCond]
    refine (Kleene.and_eq_true_iff _ _).trans ?_
    show (_ : GenPredIn T c (notInKinds k)).holdsPlain w γ
      ∧ (_ : GenPredIn T c (notInKinds k)).holdsPlain w γ ↔ _
    rw [GenPredIn.holdsPlain_substMap,
      show substVal (fun j : Fin 0 => j.elim0) γ = fun _ => 0 from funext fun j => j.elim0,
      keyJoinCond_holdsPlain]
    refine and_congr Iff.rfl ?_
    show CompOp.syneq.eval3 (w (Fin.natAdd k (Fin.natAdd k (0 : Fin 1))))
        ((TermGIn.const (0 : T)).evalPlain w γ) = Kleene.true ↔ _
    rw [CompOp.syneq_eval3_eq_true_iff]
    exact Iff.rfl
  show Multiset.filter (fun t => t ∉ r₂) r₁ = _
  show _ = Multiset.map _ (Multiset.filter
      (fun w => (AggQueryIn.notInCond (T := T) (c := c) (k := k)).holdsPlain w γ)
      (q₁.evaluatePlain D γ * (AggQueryIn.tagAgg cnt q₁ q₂).evaluatePlain D γ))
  rw [hDr, Multiset.filter_congr (fun w _ => hcond w), Relation.hMul_eq_bind]
  refine Eq.symm (Eq.trans (notIn_filter_map r₁ ((r₁ + r₂).dedup) val
    (Multiset.nodup_dedup _)
    (fun u hu => Multiset.mem_dedup.mpr (Multiset.mem_add.mpr (Or.inl hu)))) ?_)
  refine Multiset.filter_congr (fun u _ => ?_)
  rw [hval]
  exact AggQueryIn.tagAgg_zero_iff cnt hc _ _ u

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

omit [ValueType T] in
/-- **What the difference form uses**: a projection and the difference,
which is the point of the swap. -/
theorem AggQueryIn.usesOnly_selByDiff {S : Set OpKind} (yes : T)
    (t : TermGIn T 0 (ColKind.allReg k)) {q : AggQuery T k (ColKind.allReg k)}
    (hp : OpKind.proj ∈ S) (hd : OpKind.diff ∈ S) (hq : q.usesOnly S) :
    (AggQueryIn.selByDiff yes t q).usesOnly S :=
  ⟨⟨hp, fun _ => rfl⟩, hd, ⟨⟨hp, fun _ => rfl⟩, hq⟩, hd,
    ⟨⟨hp, fun _ => rfl⟩, hq⟩, ⟨⟨hp, fun _ => rfl⟩, hq⟩⟩

omit [ValueType T] in
/-- And it names the relations the query names. -/
theorem AggQueryIn.overSchema_selByDiff {sch : Schema} (yes : T)
    (t : TermGIn T 0 (ColKind.allReg k)) {q : AggQuery T k (ColKind.allReg k)}
    (hq : q.overSchema sch) :
    (AggQueryIn.selByDiff yes t q).overSchema sch := ⟨hq, hq, hq⟩

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

/-- And a disjunction where one of them does. -/
private theorem holdsPlain_or_iff {c n' : ℕ} {κ : Fin n' → ColKind}
    (φ ψ : GenPredIn T c κ) (u : Tuple T n') (γ : Fin c → T) :
    (GenPredIn.or φ ψ).holdsPlain u γ
      ↔ (φ.holdsPlain u γ ∨ ψ.holdsPlain u γ) :=
  Kleene.or_eq_true_iff _ _

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

/-- **The substitution the apply's right side reads its context
through**: the left row comes first, so the ambient column `j` sits at
`n + j`. -/
def applyOuter (T : Type) (c n : ℕ) : Fin c → T ⊕ Fin (n + c) :=
  fun j => Sum.inr (Fin.natAdd n j)

omit [ValueType T] in
/-- And what it reads there is the ambient valuation. -/
@[simp] theorem substVal_applyOuter (c n' : ℕ) (u : Tuple T n')
    (γ : Fin c → T) :
    substVal (applyOuter T c n') (Fin.append u γ) = γ :=
  funext (fun j => by
    show (Fin.append u γ : Tuple T (n' + c)) (Fin.natAdd n' j) = γ j
    rw [Fin.append_right])

/-- **A window written with an apply and a scalar aggregation**: for each
row of `q`, the term aggregated over the rows of `qf` that row's frame
holds, read in the window's own order.

The two relations are the same one where the window's input is all
regular. They part where it is not: a window reads what
`ColKind.readTuple` leaves of each row, so the rows the frame holds are
*that* reading of the input, while the rows the apply emits are the
input's own. -/
def winByApplyOn {c : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (ψ : GenPredIn T (n + c) (ColKind.allReg n))
    (t : TermIn T c n) (f : SeqAggFunc T)
    (q qf : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  AggQueryIn.castKind (winApplyKinds n)
    (AggQueryIn.Apply q
      (AggQueryIn.GammaScalar ![t.substMap (applyOuter T c n)] ![f]
        (AggQueryIn.Sel (GenPredIn.and
            (outerKeyCond P (fun _ => rfl) (fun k => Fin.castAdd c (P k))) ψ)
          (qf.substMap (applyOuter T c n)))
        (GroupOrder.byCols O o)))

/-- The same over an all-regular input, where the frame reads the input
itself. -/
def winByApply {c : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (ψ : GenPredIn T (n + c) (ColKind.allReg n))
    (t : TermIn T c n) (f : SeqAggFunc T)
    (q : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  winByApplyOn P O o ψ t f q q

/-- **The nulling of the aggregate columns, as a projection**: what a
window reads of its input (`ColKind.readTuple`), written in the language
over an input whose columns have been re-typed to regular. -/
def nullCols {c k : ℕ} (κ : Fin k → ColKind) :
    Tuple (ProjColIn T c (ColKind.allReg k)) k :=
  fun j => if (κ j).base = ColKind.agg then .term (.const 0)
    else .term (.index j rfl)

theorem evalPlain_nullCols {c k : ℕ} (κ : Fin k → ColKind) (u : Tuple T k)
    (γ : Fin c → T) :
    (fun j => (nullCols (T := T) (c := c) κ j).evalPlain u γ)
      = ColKind.readTuple κ u := by
  funext j
  show (if (κ j).base = ColKind.agg then
      (ProjColIn.term (TermGIn.const 0) : ProjColIn T c (ColKind.allReg k))
    else .term (.index j rfl)).evalPlain u γ = _
  show _ = match (κ j).base with
    | ColKind.agg => (0 : T)
    | _ => u j
  cases h : (κ j).base <;> rfl

/-- **And the rows of the nulled projection are the nulled rows.** -/
theorem evaluatePlain_proj_nullCols {c k : ℕ} (κ : Fin k → ColKind)
    (q : AggQueryIn T c k (ColKind.allReg k)) (D : Database T)
    (γ : Fin c → T) :
    (AggQueryIn.Proj (nullCols κ) q).evaluatePlain D γ
      = (q.evaluatePlain D γ).map (ColKind.readTuple κ) :=
  Multiset.map_congr rfl (fun u _ => evalPlain_nullCols κ u γ)

/-- **What a window's `FILTER` clause keeps**, clause or no clause: with
none, every row of the frame. -/
def Selection.keepsOpt {k : ℕ} : Option (Selection T k) → Tuple T k → Bool
  | none => fun _ => true
  | some φ => φ.keeps

@[simp] theorem Selection.keepsOpt_none {k : ℕ} :
    Selection.keepsOpt (T := T) (k := k) none = fun _ => true := rfl

@[simp] theorem Selection.keepsOpt_some {k : ℕ} (φ : Selection T k) :
    Selection.keepsOpt (some φ) = φ.keeps := rfl

/-! ## A classical selection as a predicate over a context -/

/-- A classical term as a term over all-regular columns, in any context. -/
def TermIn.toRegIn {c k : ℕ} : Term T k → TermGIn T c (ColKind.allReg k)
  | .const a => .const a
  | .outer j => j.elim0
  | .index i => .index i rfl
  | .add t₁ t₂ => .add t₁.toRegIn t₂.toRegIn
  | .sub t₁ t₂ => .sub t₁.toRegIn t₂.toRegIn
  | .mul t₁ t₂ => .mul t₁.toRegIn t₂.toRegIn
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    .caseWhen op t₁.toRegIn t₂.toRegIn t₃.toRegIn t₄.toRegIn
  | .coalesce t₁ t₂ => .coalesce t₁.toRegIn t₂.toRegIn

theorem TermIn.evalPlain_toRegIn {c k : ℕ} (t : Term T k) (y : Tuple T k)
    (γ : Fin c → T) : (t.toRegIn (c := c)).evalPlain y γ = t.eval y := by
  induction t with
  | const a => rfl
  | outer j => exact j.elim0
  | index i => rfl
  | add t₁ t₂ ih₁ ih₂ =>
    exact congrArg₂ (fun a b : T => a + b) ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ =>
    exact congrArg₂ (fun a b : T => a - b) ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ =>
    exact congrArg₂ (fun a b : T => a * b) ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if (op.eval3 _ _) = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

/-- A classical selection as a predicate over all-regular columns, in any
context: the clause of a `FILTER` or of a frame, read where a query
applied to the current row reads it. -/
def Selection.toPredIn {c k : ℕ} : Selection T k →
    GenPredIn T c (ColKind.allReg k)
  | .BT (.EQ t₁ t₂) => .cmp .eq t₁.toRegIn t₂.toRegIn
  | .BT (.NE t₁ t₂) => .cmp .ne t₁.toRegIn t₂.toRegIn
  | .BT (.LE t₁ t₂) => .cmp .le t₁.toRegIn t₂.toRegIn
  | .BT (.LT t₁ t₂) => .cmp .lt t₁.toRegIn t₂.toRegIn
  | .BT (.GE t₁ t₂) => .cmp .ge t₁.toRegIn t₂.toRegIn
  | .BT (.GT t₁ t₂) => .cmp .gt t₁.toRegIn t₂.toRegIn
  | .BT (.SYNEQ t₁ t₂) => .cmp .syneq t₁.toRegIn t₂.toRegIn
  | .BT (.SYNNE t₁ t₂) => .cmp .synne t₁.toRegIn t₂.toRegIn
  | .Not φ => .not φ.toPredIn
  | .And φ₁ φ₂ => .and φ₁.toPredIn φ₂.toPredIn
  | .Or φ₁ φ₂ => .or φ₁.toPredIn φ₂.toPredIn
  | .True => .cmp .eq (.const 0) (.const 0)

theorem Selection.evalPlain3_toPredIn {c k : ℕ} :
    ∀ (φ : Selection T k) (y : Tuple T k) (γ : Fin c → T),
      (φ.toPredIn (c := c)).evalPlain3 y γ = φ.eval3 y
  | .BT b, y, γ => by
    cases b <;>
      (show CompOp.eval3 _ _ _ = _;
       rw [TermIn.evalPlain_toRegIn, TermIn.evalPlain_toRegIn];
       rfl)
  | .Not φ, y, γ => by
    show (GenPredIn.evalPlain3 _ _ _).not = _
    rw [Selection.evalPlain3_toPredIn φ y γ]
    rfl
  | .And φ₁ φ₂, y, γ => by
    show (GenPredIn.evalPlain3 _ _ _).and _ = _
    rw [Selection.evalPlain3_toPredIn φ₁ y γ,
      Selection.evalPlain3_toPredIn φ₂ y γ]
    rfl
  | .Or φ₁ φ₂, y, γ => by
    show (GenPredIn.evalPlain3 _ _ _).or _ = _
    rw [Selection.evalPlain3_toPredIn φ₁ y γ,
      Selection.evalPlain3_toPredIn φ₂ y γ]
    rfl
  | .True, y, γ => by
    show CompOp.eq.eval3 (0 : T) 0 = Kleene.true
    rw [CompOp.eval3_eq_true_iff CompOp.eq ValueType.isNull_zero
      ValueType.isNull_zero]
    rfl

theorem Selection.holdsPlain_toPredIn {c k : ℕ} (φ : Selection T k)
    (y : Tuple T k) (γ : Fin c → T) :
    (φ.toPredIn (c := c)).holdsPlain y γ ↔ φ.keeps y = true := by
  rw [GenPredIn.holdsPlain, Selection.evalPlain3_toPredIn φ y γ,
    Selection.keeps]
  cases h : φ.eval3 y <;> simp

/-! ## A frame clause as a predicate -/

/-- One column of the clause, as a comparison: the direction decides
which way round the two terms are read. -/
def OrderCol.lePred {c m : ℕ} (cl : OrderCol)
    (x y : TermGIn T c (ColKind.allReg m)) :
    GenPredIn T c (ColKind.allReg m) :=
  if cl.desc then .cmp CompOp.le y x else .cmp CompOp.le x y

/-- The same strictly. -/
def OrderCol.ltPred {c m : ℕ} (cl : OrderCol)
    (x y : TermGIn T c (ColKind.allReg m)) :
    GenPredIn T c (ColKind.allReg m) :=
  if cl.desc then .cmp CompOp.lt y x else .cmp CompOp.lt x y

/-- Where nothing is null the clause's comparison is the domain's, read
in the column's direction. -/
theorem OrderCol.le_eq_noNulls [NoNulls T] (cl : OrderCol) (a b : T) :
    cl.le a b = if cl.desc then decide (b ≤ a) else decide (a ≤ b) := by
  unfold OrderCol.le
  rw [isNull_eq_false a, isNull_eq_false b]
  rfl

/-- Every value is at or before itself, null or not. -/
theorem OrderCol.le_self (cl : OrderCol) (a : T) : cl.le a a = true := by
  unfold OrderCol.le
  by_cases ha : ValueType.isNull a = true
  · rw [ha]
    rfl
  · rw [Bool.not_eq_true] at ha
    rw [ha]
    cases cl.desc <;> simp

/-- **Two values are peers exactly when they are the same value**, where
the domain names its null: the clause separates a null from anything
else, whichever way its placement falls. -/
theorem OrderCol.peer_eq_true_iff_of_null (cl : OrderCol) {ν : T}
    (hνu : ∀ a : T, ValueType.isNull a = true → a = ν) (a b : T) :
    cl.peer a b = true ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h, OrderCol.peer, OrderCol.le_self]; rfl⟩
  rw [OrderCol.peer, Bool.and_eq_true] at h
  by_cases ha : ValueType.isNull a = true
  · by_cases hb : ValueType.isNull b = true
    · rw [hνu a ha, hνu b hb]
    · rw [Bool.not_eq_true] at hb
      rw [OrderCol.le, ha, hb] at h
      rw [OrderCol.le, hb, ha] at h
      cases hnf : cl.nullsFirst
      · exact absurd (hnf ▸ h.1) (by simp)
      · exact absurd (hnf ▸ h.2) (by simp)
  · rw [Bool.not_eq_true] at ha
    by_cases hb : ValueType.isNull b = true
    · rw [OrderCol.le, ha, hb] at h
      rw [OrderCol.le, hb, ha] at h
      cases hnf : cl.nullsFirst
      · exact absurd (hnf ▸ h.2) (by simp)
      · exact absurd (hnf ▸ h.1) (by simp)
    · rw [Bool.not_eq_true] at hb
      rw [OrderCol.le, ha, hb] at h
      rw [OrderCol.le, hb, ha] at h
      cases hd : cl.desc
      · rw [hd] at h
        exact le_antisymm (of_decide_eq_true h.1) (of_decide_eq_true h.2)
      · rw [hd] at h
        exact le_antisymm (of_decide_eq_true h.2) (of_decide_eq_true h.1)

theorem OrderCol.peer_eq_true_iff [NoNulls T] (cl : OrderCol) (a b : T) :
    cl.peer a b = true ↔ a = b := by
  rw [OrderCol.peer, Bool.and_eq_true, OrderCol.le_eq_noNulls,
    OrderCol.le_eq_noNulls]
  cases hd : cl.desc
  · simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨le_of_eq h, le_of_eq h.symm⟩⟩
  · simp only [ite_true, decide_eq_true_eq]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩

theorem OrderCol.holdsPlain_lePred_of {c m : ℕ} (cl : OrderCol)
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T)
    (hx : ValueType.isNull (x.evalPlain u γ) = false)
    (hy : ValueType.isNull (y.evalPlain u γ) = false) :
    (cl.lePred x y).holdsPlain u γ
      ↔ cl.le (x.evalPlain u γ) (y.evalPlain u γ) = true := by
  cases hd : cl.desc <;>
    simp [OrderCol.lePred, OrderCol.le, hd, GenPredIn.holdsPlain,
      GenPredIn.evalPlain3, CompOp.eval3_eq_true_iff _ hx hy,
      CompOp.eval3_eq_true_iff _ hy hx, CompOp.eval, hx, hy]

theorem OrderCol.holdsPlain_ltPred_of {c m : ℕ} (cl : OrderCol)
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T)
    (hx : ValueType.isNull (x.evalPlain u γ) = false)
    (hy : ValueType.isNull (y.evalPlain u γ) = false) :
    (cl.ltPred x y).holdsPlain u γ
      ↔ cl.le (y.evalPlain u γ) (x.evalPlain u γ) = false := by
  cases hd : cl.desc <;>
    simp [OrderCol.ltPred, OrderCol.le, hd, GenPredIn.holdsPlain,
      GenPredIn.evalPlain3, CompOp.eval3_eq_true_iff _ hx hy,
      CompOp.eval3_eq_true_iff _ hy hx, CompOp.eval, hx, hy, not_le]

theorem OrderCol.holdsPlain_lePred [NoNulls T] {c m : ℕ} (cl : OrderCol)
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T) :
    (cl.lePred x y).holdsPlain u γ
      ↔ cl.le (x.evalPlain u γ) (y.evalPlain u γ) = true :=
  OrderCol.holdsPlain_lePred_of cl x y u γ (isNull_eq_false _)
    (isNull_eq_false _)

theorem OrderCol.holdsPlain_ltPred [NoNulls T] {c m : ℕ} (cl : OrderCol)
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T) :
    (cl.ltPred x y).holdsPlain u γ
      ↔ cl.le (y.evalPlain u γ) (x.evalPlain u γ) = false :=
  OrderCol.holdsPlain_ltPred_of cl x y u γ (isNull_eq_false _)
    (isNull_eq_false _)

private theorem holdsPlain_syneq {c m : ℕ}
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T) :
    (GenPredIn.cmp CompOp.syneq x y).holdsPlain u γ
      ↔ x.evalPlain u γ = y.evalPlain u γ := by
  show CompOp.syneq.eval3 _ _ = Kleene.true ↔ _
  rw [CompOp.syneq_eval3_eq_true_iff]

private theorem holdsPlain_synne {c m : ℕ}
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T) :
    (GenPredIn.cmp CompOp.synne x y).holdsPlain u γ
      ↔ x.evalPlain u γ ≠ y.evalPlain u γ := by
  show CompOp.synne.eval3 _ _ = Kleene.true ↔ _
  rw [CompOp.eval3_of_not_strict rfl]
  simp [CompOp.eval]

/-- A constant term reads its own value, in any context. -/
@[simp] private theorem evalPlain_constN {c m : ℕ} (a : T) (u : Tuple T m)
    (γ : Fin c → T) :
    (TermGIn.const a : TermGIn T c (ColKind.allReg m)).evalPlain u γ = a := rfl

/-- **One column of the clause where the domain names its null**: the
comparison, guarded by the null tests the clause's placement asks for.
`IS NULL` is spelled `IS NOT DISTINCT FROM ν`, which is why the null has
to be a value the terms can name – `ValueType` has an `isNull`
predicate and no null constant, so the guards cannot be written without
one. -/
def OrderCol.lePredN {c m : ℕ} (cl : OrderCol) (ν : T)
    (x y : TermGIn T c (ColKind.allReg m)) :
    GenPredIn T c (ColKind.allReg m) :=
  if cl.nullsFirst then
    .or (.cmp CompOp.syneq x (.const ν))
      (.and (.cmp CompOp.synne y (.const ν)) (cl.lePred x y))
  else
    .or (.cmp CompOp.syneq y (.const ν))
      (.and (.cmp CompOp.synne x (.const ν)) (cl.lePred x y))

/-- And the strict one: the negation of the comparison the other way
round, which is where the guards swap places. -/
def OrderCol.ltPredN {c m : ℕ} (cl : OrderCol) (ν : T)
    (x y : TermGIn T c (ColKind.allReg m)) :
    GenPredIn T c (ColKind.allReg m) :=
  if cl.nullsFirst then
    .and (.cmp CompOp.synne y (.const ν))
      (.or (.cmp CompOp.syneq x (.const ν)) (cl.ltPred x y))
  else
    .and (.cmp CompOp.synne x (.const ν))
      (.or (.cmp CompOp.syneq y (.const ν)) (cl.ltPred x y))

theorem OrderCol.holdsPlain_lePredN {c m : ℕ} (cl : OrderCol) {ν : T}
    (hν : ValueType.isNull ν = true)
    (hνu : ∀ a : T, ValueType.isNull a = true → a = ν)
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T) :
    (cl.lePredN ν x y).holdsPlain u γ
      ↔ cl.le (x.evalPlain u γ) (y.evalPlain u γ) = true := by
  have hxν : ∀ a : T, ValueType.isNull a = true ↔ a = ν :=
    fun a => ⟨hνu a, fun h => h ▸ hν⟩
  by_cases hxn : ValueType.isNull (x.evalPlain u γ) = true
  · by_cases hyn : ValueType.isNull (y.evalPlain u γ) = true
    · cases hnf : cl.nullsFirst <;>
        simp [OrderCol.lePredN, OrderCol.le, hnf, hν, evalPlain_constN, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hxn, (hxν _).mp hyn]
    · rw [Bool.not_eq_true] at hyn
      have hyν : (y.evalPlain u γ) ≠ ν := fun hc => by
        rw [(hxν _).mpr hc] at hyn
        exact absurd hyn (by simp)
      cases hnf : cl.nullsFirst
      · simp [OrderCol.lePredN, OrderCol.le, hnf, hν, evalPlain_constN, hyn, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hxn, hyν]
      · simp [OrderCol.lePredN, OrderCol.le, hnf, hν, evalPlain_constN, hyn, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hxn, hyν]
  · rw [Bool.not_eq_true] at hxn
    have hxν' : (x.evalPlain u γ) ≠ ν := fun hc => by
      rw [(hxν _).mpr hc] at hxn
      exact absurd hxn (by simp)
    by_cases hyn : ValueType.isNull (y.evalPlain u γ) = true
    · cases hnf : cl.nullsFirst <;>
        simp [OrderCol.lePredN, OrderCol.le, hnf, hν, evalPlain_constN, hxn, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hyn, hxν']
    · rw [Bool.not_eq_true] at hyn
      have hyν : (y.evalPlain u γ) ≠ ν := fun hc => by
        rw [(hxν _).mpr hc] at hyn
        exact absurd hyn (by simp)
      cases hnf : cl.nullsFirst
      · simp [OrderCol.lePredN, hnf, evalPlain_constN, holdsPlain_or_iff, holdsPlain_and_iff,
          holdsPlain_syneq, holdsPlain_synne, hxν', hyν,
          OrderCol.holdsPlain_lePred_of cl x y u γ hxn hyn]
      · simp [OrderCol.lePredN, hnf, evalPlain_constN, holdsPlain_or_iff, holdsPlain_and_iff,
          holdsPlain_syneq, holdsPlain_synne, hxν', hyν,
          OrderCol.holdsPlain_lePred_of cl x y u γ hxn hyn]

theorem OrderCol.holdsPlain_ltPredN {c m : ℕ} (cl : OrderCol) {ν : T}
    (hν : ValueType.isNull ν = true)
    (hνu : ∀ a : T, ValueType.isNull a = true → a = ν)
    (x y : TermGIn T c (ColKind.allReg m)) (u : Tuple T m) (γ : Fin c → T) :
    (cl.ltPredN ν x y).holdsPlain u γ
      ↔ cl.le (y.evalPlain u γ) (x.evalPlain u γ) = false := by
  have hxν : ∀ a : T, ValueType.isNull a = true ↔ a = ν :=
    fun a => ⟨hνu a, fun h => h ▸ hν⟩
  by_cases hxn : ValueType.isNull (x.evalPlain u γ) = true
  · by_cases hyn : ValueType.isNull (y.evalPlain u γ) = true
    · cases hnf : cl.nullsFirst <;>
        simp [OrderCol.ltPredN, OrderCol.le, hnf, hν, evalPlain_constN, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hxn, (hxν _).mp hyn]
    · rw [Bool.not_eq_true] at hyn
      have hyν : (y.evalPlain u γ) ≠ ν := fun hc => by
        rw [(hxν _).mpr hc] at hyn
        exact absurd hyn (by simp)
      cases hnf : cl.nullsFirst
      · simp [OrderCol.ltPredN, OrderCol.le, hnf, hν, evalPlain_constN, hyn, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hxn, hyν]
      · simp [OrderCol.ltPredN, OrderCol.le, hnf, hν, evalPlain_constN, hyn, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hxn, hyν]
  · rw [Bool.not_eq_true] at hxn
    have hxν' : (x.evalPlain u γ) ≠ ν := fun hc => by
      rw [(hxν _).mpr hc] at hxn
      exact absurd hxn (by simp)
    by_cases hyn : ValueType.isNull (y.evalPlain u γ) = true
    · cases hnf : cl.nullsFirst <;>
        simp [OrderCol.ltPredN, OrderCol.le, hnf, hν, evalPlain_constN, hxn, holdsPlain_or_iff,
          holdsPlain_and_iff, holdsPlain_syneq, holdsPlain_synne,
          (hxν _).mp hyn, hxν']
    · rw [Bool.not_eq_true] at hyn
      have hyν : (y.evalPlain u γ) ≠ ν := fun hc => by
        rw [(hxν _).mpr hc] at hyn
        exact absurd hyn (by simp)
      cases hnf : cl.nullsFirst
      · simp [OrderCol.ltPredN, hnf, evalPlain_constN, holdsPlain_or_iff, holdsPlain_and_iff,
          holdsPlain_syneq, holdsPlain_synne, hxν', hyν,
          OrderCol.holdsPlain_ltPred_of cl x y u γ hxn hyn]
      · simp [OrderCol.ltPredN, hnf, evalPlain_constN, holdsPlain_or_iff, holdsPlain_and_iff,
          holdsPlain_syneq, holdsPlain_synne, hxν', hyν,
          OrderCol.holdsPlain_ltPred_of cl x y u γ hxn hyn]

/-- **The clause's comparison as a predicate**: lexicographically, the
columns in the order the clause names them, each column compared by a
predicate of its own – which is where the direction and the null
placement are read. -/
def OrderSpec.lePredOnOf {c m : ℕ}
    (base : Fin p → GenPredIn T c (ColKind.allReg m))
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) :
    List (Fin p) → GenPredIn T c (ColKind.allReg m)
  | [] => .cmp CompOp.syneq (.const 0) (.const 0)
  | k :: ks =>
      .or (.and (.cmp CompOp.syneq (x k) (y k)) (lePredOnOf base x y ks))
        (.and (.cmp CompOp.synne (x k) (y k)) (base k))

/-- And the strict one: what the clause puts *before* the current row's
peers. -/
def OrderSpec.ltPredOnOf {c m : ℕ}
    (base : Fin p → GenPredIn T c (ColKind.allReg m))
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) :
    List (Fin p) → GenPredIn T c (ColKind.allReg m)
  | [] => .cmp CompOp.synne (.const 0) (.const 0)
  | k :: ks =>
      .or (.and (.cmp CompOp.syneq (x k) (y k)) (ltPredOnOf base x y ks))
        (.and (.cmp CompOp.synne (x k) (y k)) (base k))

/-- The clause's comparison where nothing is null: the column's own
comparison, in its own direction. -/
def OrderSpec.lePredOn {c m : ℕ} (o : OrderSpec p)
    (x y : Fin p → TermGIn T c (ColKind.allReg m))
    (ks : List (Fin p)) : GenPredIn T c (ColKind.allReg m) :=
  OrderSpec.lePredOnOf (fun k => (o k).lePred (x k) (y k)) x y ks

/-- And the strict one. -/
def OrderSpec.ltPredOn {c m : ℕ} (o : OrderSpec p)
    (x y : Fin p → TermGIn T c (ColKind.allReg m))
    (ks : List (Fin p)) : GenPredIn T c (ColKind.allReg m) :=
  OrderSpec.ltPredOnOf (fun k => (o k).ltPred (x k) (y k)) x y ks

theorem OrderSpec.holdsPlain_lePredOnOf {c m : ℕ} (o : OrderSpec p)
    (base : Fin p → GenPredIn T c (ColKind.allReg m))
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) (u : Tuple T m)
    (γ : Fin c → T)
    (hbase : ∀ k, (base k).holdsPlain u γ
        ↔ (o k).le ((x k).evalPlain u γ) ((y k).evalPlain u γ) = true)
    (hpeer : ∀ (k : Fin p) (a b : T), (o k).peer a b = true ↔ a = b) :
    ∀ ks : List (Fin p),
      (OrderSpec.lePredOnOf base x y ks).holdsPlain u γ
        ↔ o.leOn ks (fun k => (x k).evalPlain u γ)
            (fun k => (y k).evalPlain u γ) = true
  | [] => by
    show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true ↔ _
    rw [CompOp.syneq_eval3_eq_true_iff]
    show (0 : T) = 0 ↔ true = true
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | k :: ks => by
    rw [show OrderSpec.lePredOnOf base x y (k :: ks)
        = .or (.and (.cmp CompOp.syneq (x k) (y k))
            (OrderSpec.lePredOnOf base x y ks))
          (.and (.cmp CompOp.synne (x k) (y k)) (base k)) from rfl,
      holdsPlain_or_iff, holdsPlain_and_iff, holdsPlain_and_iff,
      OrderSpec.holdsPlain_lePredOnOf o base x y u γ hbase hpeer ks,
      hbase k, holdsPlain_syneq, holdsPlain_synne,
      show OrderSpec.leOn o (k :: ks) (fun k => (x k).evalPlain u γ)
          (fun k => (y k).evalPlain u γ)
        = (if (o k).peer ((x k).evalPlain u γ) ((y k).evalPlain u γ) then
            o.leOn ks (fun k => (x k).evalPlain u γ)
              (fun k => (y k).evalPlain u γ)
          else (o k).le ((x k).evalPlain u γ) ((y k).evalPlain u γ)) from rfl]
    by_cases hxy : (x k).evalPlain u γ = (y k).evalPlain u γ
    · rw [ite_eq_left ((hpeer k _ _).mpr hxy)]
      exact ⟨fun h => h.elim (fun hl => hl.2) (fun hr => absurd hxy hr.1),
        fun h => Or.inl ⟨hxy, h⟩⟩
    · rw [ite_eq_right (fun hp => hxy ((hpeer k _ _).mp hp))]
      exact ⟨fun h => h.elim (fun hl => absurd hl.1 hxy) (fun hr => hr.2),
        fun h => Or.inr ⟨hxy, h⟩⟩

theorem OrderSpec.holdsPlain_ltPredOnOf {c m : ℕ} (o : OrderSpec p)
    (base : Fin p → GenPredIn T c (ColKind.allReg m))
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) (u : Tuple T m)
    (γ : Fin c → T)
    (hbase : ∀ k, (base k).holdsPlain u γ
        ↔ (o k).le ((y k).evalPlain u γ) ((x k).evalPlain u γ) = false)
    (hpeer : ∀ (k : Fin p) (a b : T), (o k).peer a b = true ↔ a = b) :
    ∀ ks : List (Fin p),
      (OrderSpec.ltPredOnOf base x y ks).holdsPlain u γ
        ↔ o.leOn ks (fun k => (y k).evalPlain u γ)
            (fun k => (x k).evalPlain u γ) = false
  | [] => by
    show CompOp.synne.eval3 (0 : T) 0 = Kleene.true ↔ _
    rw [CompOp.eval3_of_not_strict rfl]
    show Kleene.ofBool (decide ((0 : T) ≠ 0)) = Kleene.true ↔ true = false
    simp
  | k :: ks => by
    rw [show OrderSpec.ltPredOnOf base x y (k :: ks)
        = .or (.and (.cmp CompOp.syneq (x k) (y k))
            (OrderSpec.ltPredOnOf base x y ks))
          (.and (.cmp CompOp.synne (x k) (y k)) (base k)) from rfl,
      holdsPlain_or_iff, holdsPlain_and_iff, holdsPlain_and_iff,
      OrderSpec.holdsPlain_ltPredOnOf o base x y u γ hbase hpeer ks,
      hbase k, holdsPlain_syneq, holdsPlain_synne,
      show OrderSpec.leOn o (k :: ks) (fun k => (y k).evalPlain u γ)
          (fun k => (x k).evalPlain u γ)
        = (if (o k).peer ((y k).evalPlain u γ) ((x k).evalPlain u γ) then
            o.leOn ks (fun k => (y k).evalPlain u γ)
              (fun k => (x k).evalPlain u γ)
          else (o k).le ((y k).evalPlain u γ) ((x k).evalPlain u γ)) from rfl]
    by_cases hxy : (x k).evalPlain u γ = (y k).evalPlain u γ
    · rw [ite_eq_left ((hpeer k _ _).mpr hxy.symm)]
      exact ⟨fun h => h.elim (fun hl => hl.2) (fun hr => absurd hxy hr.1),
        fun h => Or.inl ⟨hxy, h⟩⟩
    · rw [ite_eq_right (fun hp => hxy ((hpeer k _ _).mp hp).symm)]
      exact ⟨fun h => h.elim (fun hl => absurd hl.1 hxy) (fun hr => hr.2),
        fun h => Or.inr ⟨hxy, h⟩⟩

theorem OrderSpec.holdsPlain_lePredOn [NoNulls T] {c m : ℕ} (o : OrderSpec p)
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) (u : Tuple T m)
    (γ : Fin c → T) (ks : List (Fin p)) :
    (o.lePredOn x y ks).holdsPlain u γ
      ↔ o.leOn ks (fun k => (x k).evalPlain u γ)
          (fun k => (y k).evalPlain u γ) = true :=
  OrderSpec.holdsPlain_lePredOnOf o _ x y u γ
    (fun k => OrderCol.holdsPlain_lePred (o k) (x k) (y k) u γ)
    (fun k a b => OrderCol.peer_eq_true_iff (o k) a b) ks

theorem OrderSpec.holdsPlain_ltPredOn [NoNulls T] {c m : ℕ} (o : OrderSpec p)
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) (u : Tuple T m)
    (γ : Fin c → T) (ks : List (Fin p)) :
    (o.ltPredOn x y ks).holdsPlain u γ
      ↔ o.leOn ks (fun k => (y k).evalPlain u γ)
          (fun k => (x k).evalPlain u γ) = false :=
  OrderSpec.holdsPlain_ltPredOnOf o _ x y u γ
    (fun k => OrderCol.holdsPlain_ltPred (o k) (x k) (y k) u γ)
    (fun k a b => OrderCol.peer_eq_true_iff (o k) a b) ks

/-! ## The frame condition of the clause-determined frames -/

/-- The row's own order columns, as terms of the derived window's
selection. -/
def frameSelfTerms {c k q : ℕ} (O : Tuple (Fin k) q) :
    Fin q → TermGIn T (k + c) (ColKind.allReg k) :=
  fun j => TermGIn.index (O j) rfl

/-- The current row's, which the apply supplies as outer columns. -/
def frameOuterTerms {c k q : ℕ} (O : Tuple (Fin k) q) :
    Fin q → TermGIn T (k + c) (ColKind.allReg k) :=
  fun j => TermGIn.outer (Fin.castAdd c (O j))

/-- A window's `FILTER` clause as a predicate, or the tautology where
there is none. -/
def clausePredOpt {c k : ℕ} : Option (Selection T k) →
    GenPredIn T c (ColKind.allReg k)
  | none => .cmp CompOp.syneq (.const 0) (.const 0)
  | some φ => φ.toPredIn

theorem holdsPlain_clausePredOpt {c k : ℕ} (keep : Option (Selection T k))
    (y : Tuple T k) (γ : Fin c → T) :
    (clausePredOpt keep).holdsPlain y γ
      ↔ Selection.keepsOpt keep y = true := by
  cases keep with
  | none =>
    show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true ↔ _
    rw [CompOp.syneq_eval3_eq_true_iff]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some φ => exact Selection.holdsPlain_toPredIn φ y γ

/-! #### The predicates built here apply no function to values -/

omit [ValueType T] in
theorem TermIn.noFun_toRegIn {c k : ℕ} (t : Term T k) :
    (t.toRegIn (c := c)).noFun = t.noFun := by
  cases t <;> first | rfl | (rename_i j; exact j.elim0)

theorem Selection.noFun_toPredIn {c k : ℕ} :
    ∀ φ : Selection T k, (φ.toPredIn (c := c)).noFun = φ.noFun
  | .BT b => by
    cases b <;> (show (_ && _) = (_ && _); rw [TermIn.noFun_toRegIn, TermIn.noFun_toRegIn]; try rfl)
  | .Not φ => Selection.noFun_toPredIn φ
  | .And φ₁ φ₂ => by
    show (_ && _) = (_ && _)
    rw [Selection.noFun_toPredIn φ₁, Selection.noFun_toPredIn φ₂]
  | .Or φ₁ φ₂ => by
    show (_ && _) = (_ && _)
    rw [Selection.noFun_toPredIn φ₁, Selection.noFun_toPredIn φ₂]
  | .True => rfl

omit [ValueType T] in
@[simp] theorem TermGIn.noFun_const {c n : ℕ} {κ : Fin n → ColKind} (a : T) :
    (TermGIn.const (c := c) (κ := κ) a).noFun = true := rfl

theorem noFun_clausePredOpt {c k : ℕ} (keep : Option (Selection T k)) :
    (clausePredOpt (c := c) keep).noFun = Selection.noFunOpt keep := by
  cases keep with
  | none => rfl
  | some φ => exact Selection.noFun_toPredIn φ

omit [ValueType T] in
theorem OrderCol.noFun_lePred {c m : ℕ} (cl : OrderCol) {x y : TermGIn T c (ColKind.allReg m)}
    (hx : x.noFun = true) (hy : y.noFun = true) : (cl.lePred x y).noFun = true := by
  unfold OrderCol.lePred
  split <;> (show (_ && _) = true; rw [hx, hy]; rfl)

omit [ValueType T] in
theorem OrderCol.noFun_ltPred {c m : ℕ} (cl : OrderCol) {x y : TermGIn T c (ColKind.allReg m)}
    (hx : x.noFun = true) (hy : y.noFun = true) : (cl.ltPred x y).noFun = true := by
  unfold OrderCol.ltPred
  split <;> (show (_ && _) = true; rw [hx, hy]; rfl)

omit [ValueType T] in
theorem OrderCol.noFun_lePredN {c m : ℕ} (cl : OrderCol) (ν : T)
    {x y : TermGIn T c (ColKind.allReg m)} (hx : x.noFun = true) (hy : y.noFun = true) :
    (cl.lePredN ν x y).noFun = true := by
  unfold OrderCol.lePredN
  split <;> simp only [GenPredIn.noFun, hx, hy, TermGIn.noFun_const,
    OrderCol.noFun_lePred cl hx hy, Bool.and_self]

omit [ValueType T] in
theorem OrderCol.noFun_ltPredN {c m : ℕ} (cl : OrderCol) (ν : T)
    {x y : TermGIn T c (ColKind.allReg m)} (hx : x.noFun = true) (hy : y.noFun = true) :
    (cl.ltPredN ν x y).noFun = true := by
  unfold OrderCol.ltPredN
  split <;> simp only [GenPredIn.noFun, hx, hy, TermGIn.noFun_const,
    OrderCol.noFun_ltPred cl hx hy, Bool.and_self]

theorem OrderSpec.noFun_lePredOnOf {c m : ℕ}
    {base : Fin p → GenPredIn T c (ColKind.allReg m)}
    {x y : Fin p → TermGIn T c (ColKind.allReg m)} (hb : ∀ k, (base k).noFun = true)
    (hx : ∀ k, (x k).noFun = true) (hy : ∀ k, (y k).noFun = true) :
    ∀ ks : List (Fin p), (OrderSpec.lePredOnOf base x y ks).noFun = true
  | [] => rfl
  | k :: ks => by
    simp only [OrderSpec.lePredOnOf, GenPredIn.noFun, hb, hx, hy,
      OrderSpec.noFun_lePredOnOf hb hx hy ks, Bool.and_self]

theorem OrderSpec.noFun_ltPredOnOf {c m : ℕ}
    {base : Fin p → GenPredIn T c (ColKind.allReg m)}
    {x y : Fin p → TermGIn T c (ColKind.allReg m)} (hb : ∀ k, (base k).noFun = true)
    (hx : ∀ k, (x k).noFun = true) (hy : ∀ k, (y k).noFun = true) :
    ∀ ks : List (Fin p), (OrderSpec.ltPredOnOf base x y ks).noFun = true
  | [] => rfl
  | k :: ks => by
    simp only [OrderSpec.ltPredOnOf, GenPredIn.noFun, hb, hx, hy,
      OrderSpec.noFun_ltPredOnOf hb hx hy ks, Bool.and_self]

omit [ValueType T] in
theorem noFun_frameSelfTerms {c k q : ℕ} (O : Tuple (Fin k) q) (j : Fin q) :
    (frameSelfTerms (T := T) (c := c) O j).noFun = true := rfl

omit [ValueType T] in
theorem noFun_frameOuterTerms {c k q : ℕ} (O : Tuple (Fin k) q) (j : Fin q) :
    (frameOuterTerms (T := T) (c := c) O j).noFun = true := rfl

theorem exists_framePred_whole {c : ℕ} (O : Tuple (Fin n) p)
    (keep : Option (Selection T n)) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ ((ValueFrame.whole : ValueFrame T p).ρ (Tuple.key O y)
              (Tuple.key O u) = true ∧ Selection.keepsOpt keep y = true) := by
  refine ⟨clausePredOpt keep, fun hk => by rw [noFun_clausePredOpt]; exact hk, fun y u γ => ?_⟩
  rw [holdsPlain_clausePredOpt]
  exact (and_iff_right rfl).symm

private theorem exists_framePred_rangeUpTo_noNulls [NoNulls T] {c : ℕ} (O : Tuple (Fin n) p)
    (o : OrderSpec p) (keep : Option (Selection T n)) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ ((ValueFrame.rangeUpTo o).ρ (Tuple.key O y)
              (Tuple.key O u) = true ∧ Selection.keepsOpt keep y = true) := by
  refine ⟨GenPredIn.and (o.lePredOn (frameSelfTerms O) (frameOuterTerms O)
      (List.finRange p)) (clausePredOpt keep), fun hk => ?_, fun y u γ => ?_⟩
  · have h1 : (o.lePredOn (frameSelfTerms (T := T) (c := c) O) (frameOuterTerms (c := c) O)
        (List.finRange p)).noFun = true :=
      OrderSpec.noFun_lePredOnOf (fun k => OrderCol.noFun_lePred (o k) (noFun_frameSelfTerms O k)
        (noFun_frameOuterTerms O k)) (noFun_frameSelfTerms O) (noFun_frameOuterTerms O) _
    simp only [GenPredIn.noFun, h1, noFun_clausePredOpt, hk, Bool.and_self]
  rw [holdsPlain_and_iff, holdsPlain_clausePredOpt,
    OrderSpec.holdsPlain_lePredOn o (frameSelfTerms O) (frameOuterTerms O) y
      (Fin.append u γ)]
  refine and_congr (Iff.of_eq (congrArg (fun z => z = true) ?_)) Iff.rfl
  show OrderSpec.leOn o (List.finRange p) _ _ = OrderSpec.le o _ _
  refine congrArg₂ (fun a b : Tuple T p => OrderSpec.leOn o (List.finRange p) a b)
    ?_ ?_
  · rfl
  · exact funext (fun j => Fin.append_left u γ (O j))

private theorem exists_framePred_rangeBefore_noNulls [NoNulls T] {c : ℕ} (O : Tuple (Fin n) p)
    (o : OrderSpec p) (keep : Option (Selection T n)) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ ((ValueFrame.rangeBefore o).ρ (Tuple.key O y)
              (Tuple.key O u) = true ∧ Selection.keepsOpt keep y = true) := by
  refine ⟨GenPredIn.and (o.ltPredOn (frameSelfTerms O) (frameOuterTerms O)
      (List.finRange p)) (clausePredOpt keep), fun hk => ?_, fun y u γ => ?_⟩
  · have h1 : (o.ltPredOn (frameSelfTerms (T := T) (c := c) O) (frameOuterTerms (c := c) O)
        (List.finRange p)).noFun = true :=
      OrderSpec.noFun_ltPredOnOf (fun k => OrderCol.noFun_ltPred (o k) (noFun_frameSelfTerms O k)
        (noFun_frameOuterTerms O k)) (noFun_frameSelfTerms O) (noFun_frameOuterTerms O) _
    simp only [GenPredIn.noFun, h1, noFun_clausePredOpt, hk, Bool.and_self]
  rw [holdsPlain_and_iff, holdsPlain_clausePredOpt,
    OrderSpec.holdsPlain_ltPredOn o (frameSelfTerms O) (frameOuterTerms O) y
      (Fin.append u γ)]
  refine and_congr ?_ Iff.rfl
  show OrderSpec.leOn o (List.finRange p) _ _ = false
    ↔ OrderSpec.lt o (Tuple.key O y) (Tuple.key O u) = true
  rw [show (fun j => (frameOuterTerms (c := c) O j).evalPlain y
        (Fin.append u γ)) = Tuple.key O u from
      funext (fun j => Fin.append_left u γ (O j)),
    show (fun j => (frameSelfTerms (c := c) O j).evalPlain y
        (Fin.append u γ)) = Tuple.key O y from rfl]
  show OrderSpec.le o (Tuple.key O u) (Tuple.key O y) = false ↔ _
  rw [OrderSpec.lt]
  exact ⟨fun h => by rw [h]; rfl, fun h => by
    cases hle : OrderSpec.le o (Tuple.key O u) (Tuple.key O y)
    · rfl
    · rw [hle] at h; exact absurd h (by simp)⟩

/-- **The same two frames over a domain that names its null**, where the
null placement of the clause is read by `IS NOT DISTINCT FROM ν` tests:
`ν` is asked to be a null and the only one, which is SQL's `NULL`. This
is what replaces the `NoNulls` hypothesis for a clause whose columns may
be null. -/
private theorem exists_framePred_rangeUpTo_of_null {c : ℕ} (O : Tuple (Fin n) p)
    (o : OrderSpec p) (keep : Option (Selection T n)) {ν : T}
    (hν : ValueType.isNull ν = true)
    (hνu : ∀ a : T, ValueType.isNull a = true → a = ν) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ ((ValueFrame.rangeUpTo o).ρ (Tuple.key O y)
              (Tuple.key O u) = true ∧ Selection.keepsOpt keep y = true) := by
  refine ⟨GenPredIn.and (OrderSpec.lePredOnOf
      (fun k => (o k).lePredN ν (frameSelfTerms O k) (frameOuterTerms O k))
      (frameSelfTerms O) (frameOuterTerms O) (List.finRange p))
    (clausePredOpt keep), fun hk => ?_, fun y u γ => ?_⟩
  · have h1 : (OrderSpec.lePredOnOf
        (fun k => (o k).lePredN ν (frameSelfTerms (c := c) O k) (frameOuterTerms (c := c) O k))
        (frameSelfTerms (c := c) O) (frameOuterTerms (c := c) O) (List.finRange p)).noFun
          = true :=
      OrderSpec.noFun_lePredOnOf (fun k => OrderCol.noFun_lePredN (o k) ν
        (noFun_frameSelfTerms O k) (noFun_frameOuterTerms O k))
        (noFun_frameSelfTerms O) (noFun_frameOuterTerms O) _
    simp only [GenPredIn.noFun, h1, noFun_clausePredOpt, hk, Bool.and_self]
  rw [holdsPlain_and_iff, holdsPlain_clausePredOpt,
    OrderSpec.holdsPlain_lePredOnOf o _ (frameSelfTerms O) (frameOuterTerms O) y
      (Fin.append u γ)
      (fun k => OrderCol.holdsPlain_lePredN (o k) hν hνu _ _ y (Fin.append u γ))
      (fun k a b => OrderCol.peer_eq_true_iff_of_null (o k) hνu a b)]
  refine and_congr (Iff.of_eq (congrArg (fun z => z = true) ?_)) Iff.rfl
  show OrderSpec.leOn o (List.finRange p) _ _ = OrderSpec.le o _ _
  refine congrArg₂ (fun a b : Tuple T p =>
    OrderSpec.leOn o (List.finRange p) a b) ?_ ?_
  · rfl
  · exact funext (fun j => Fin.append_left u γ (O j))

private theorem exists_framePred_rangeBefore_of_null {c : ℕ} (O : Tuple (Fin n) p)
    (o : OrderSpec p) (keep : Option (Selection T n)) {ν : T}
    (hν : ValueType.isNull ν = true)
    (hνu : ∀ a : T, ValueType.isNull a = true → a = ν) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ ((ValueFrame.rangeBefore o).ρ (Tuple.key O y)
              (Tuple.key O u) = true ∧ Selection.keepsOpt keep y = true) := by
  refine ⟨GenPredIn.and (OrderSpec.ltPredOnOf
      (fun k => (o k).ltPredN ν (frameSelfTerms O k) (frameOuterTerms O k))
      (frameSelfTerms O) (frameOuterTerms O) (List.finRange p))
    (clausePredOpt keep), fun hk => ?_, fun y u γ => ?_⟩
  · have h1 : (OrderSpec.ltPredOnOf
        (fun k => (o k).ltPredN ν (frameSelfTerms (c := c) O k) (frameOuterTerms (c := c) O k))
        (frameSelfTerms (c := c) O) (frameOuterTerms (c := c) O) (List.finRange p)).noFun
          = true :=
      OrderSpec.noFun_ltPredOnOf (fun k => OrderCol.noFun_ltPredN (o k) ν
        (noFun_frameSelfTerms O k) (noFun_frameOuterTerms O k))
        (noFun_frameSelfTerms O) (noFun_frameOuterTerms O) _
    simp only [GenPredIn.noFun, h1, noFun_clausePredOpt, hk, Bool.and_self]
  rw [holdsPlain_and_iff, holdsPlain_clausePredOpt,
    OrderSpec.holdsPlain_ltPredOnOf o _ (frameSelfTerms O) (frameOuterTerms O) y
      (Fin.append u γ)
      (fun k => OrderCol.holdsPlain_ltPredN (o k) hν hνu _ _ y (Fin.append u γ))
      (fun k a b => OrderCol.peer_eq_true_iff_of_null (o k) hνu a b)]
  refine and_congr ?_ Iff.rfl
  show OrderSpec.leOn o (List.finRange p) _ _ = false
    ↔ OrderSpec.lt o (Tuple.key O y) (Tuple.key O u) = true
  rw [show (fun j => (frameOuterTerms (c := c) O j).evalPlain y
        (Fin.append u γ)) = Tuple.key O u from
      funext (fun j => Fin.append_left u γ (O j)),
    show (fun j => (frameSelfTerms (c := c) O j).evalPlain y
        (Fin.append u γ)) = Tuple.key O y from rfl]
  show OrderSpec.le o (Tuple.key O u) (Tuple.key O y) = false ↔ _
  rw [OrderSpec.lt]
  exact ⟨fun h => by rw [h]; rfl, fun h => by
    cases hle : OrderSpec.le o (Tuple.key O u) (Tuple.key O y)
    · rfl
    · rw [hle] at h; exact absurd h (by simp)⟩

/-- **The tautology** as a predicate of the language: `IS NOT DISTINCT
FROM` between two equal constants. -/
def truePred {c k : ℕ} : GenPredIn T c (ColKind.allReg k) :=
  .cmp CompOp.syneq (.const 0) (.const 0)

theorem holdsPlain_truePred {c k : ℕ} (y : Tuple T k) (γ : Fin c → T) :
    (truePred : GenPredIn T c (ColKind.allReg k)).holdsPlain y γ := by
  show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true
  rw [CompOp.syneq_eval3_eq_true_iff]

/-- **And its opposite**, which the value domain's own non-zero value
makes available: the base case of a disjunction over no condition. -/
def falsePred {c k : ℕ} : GenPredIn T c (ColKind.allReg k) :=
  .cmp CompOp.syneq (.const 0) (.const ValueType.nonzero)

theorem holdsPlain_falsePred {c k : ℕ} (y : Tuple T k) (γ : Fin c → T) :
    ¬ (falsePred : GenPredIn T c (ColKind.allReg k)).holdsPlain y γ := by
  show ¬ (CompOp.syneq.eval3 (0 : T) ValueType.nonzero = Kleene.true)
  rw [CompOp.syneq_eval3_eq_true_iff]
  exact fun h => ValueType.nonzero_ne_zero h.symm

/-! #### The two `RANGE` frames, with no hypothesis on the domain

`ValueType` names the domain's null (`ValueType.nullVal`), so the two
readings above are the two cases of one lemma: a domain naming no null
has none, and a domain naming one has it as its only null, which is what
the `IS NOT DISTINCT FROM ν` tests need. Nothing is left for a caller to
supply. -/

/-- **`RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW` is a
predicate.** -/
theorem exists_framePred_rangeUpTo {c : ℕ} (O : Tuple (Fin n) p)
    (o : OrderSpec p) (keep : Option (Selection T n)) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ ((ValueFrame.rangeUpTo o).ρ (Tuple.key O y)
              (Tuple.key O u) = true ∧ Selection.keepsOpt keep y = true) := by
  cases h : (ValueType.nullVal : Option T) with
  | none =>
    have : NoNulls T := ValueType.noNulls_of_nullVal_none h
    exact exists_framePred_rangeUpTo_noNulls O o keep
  | some ν =>
    exact exists_framePred_rangeUpTo_of_null O o keep
      (ValueType.isNull_nullVal h)
      (fun a ha => ValueType.eq_nullVal_of_isNull h ha)

/-- **And the same frame excluding the current row's peers.** -/
theorem exists_framePred_rangeBefore {c : ℕ} (O : Tuple (Fin n) p)
    (o : OrderSpec p) (keep : Option (Selection T n)) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ ((ValueFrame.rangeBefore o).ρ (Tuple.key O y)
              (Tuple.key O u) = true ∧ Selection.keepsOpt keep y = true) := by
  cases h : (ValueType.nullVal : Option T) with
  | none =>
    have : NoNulls T := ValueType.noNulls_of_nullVal_none h
    exact exists_framePred_rangeBefore_noNulls O o keep
  | some ν =>
    exact exists_framePred_rangeBefore_of_null O o keep
      (ValueType.isNull_nullVal h)
      (fun a ha => ValueType.eq_nullVal_of_isNull h ha)

/-! #### Every frame condition is a predicate of the language

A frame *is* a condition on the order values (`FrameCond`), so the
predicate `prop:winderived` spells it out with is not something a caller
has to supply: it is read off the condition. The two strict cases are
conditions of the language and not negations, and reading the clause
backwards is what turns `at or before` into `at or after`
(`OrderSpec.le_reverse`), so the four comparisons are the two lemmas
above at `o` and at `o.reverse`. The `EXCLUDE` modifiers and the union of
the frames of a multi-frame window are the Boolean cases, where the
reading of a conjunction and of a disjunction are the conjunction and the
disjunction of the readings – Kleene's logic agreeing with the two-valued
one on *truth*, which is what a selection keeps a row by. -/

/-- A disjunction over a list of conditions, each of which is a
predicate. -/
private theorem exists_anyPred {c : ℕ} {β : Type} (O : Tuple (Fin n) p)
    (f : β → Tuple T p → Tuple T p → Bool)
    (hf : ∀ b : β, ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      ψ.noFun = true ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ f b (Tuple.key O y) (Tuple.key O u) = true) :
    ∀ L : List β, ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      ψ.noFun = true ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ L.any (fun b => f b (Tuple.key O y) (Tuple.key O u)) = true := by
  intro L
  induction L with
  | nil =>
    refine ⟨falsePred, rfl, fun y u γ => ?_⟩
    exact ⟨fun h => absurd h (holdsPlain_falsePred y _),
      fun h => absurd h (by simp)⟩
  | cons b L ih =>
    obtain ⟨ψ₁, hn₁, hψ₁⟩ := hf b
    obtain ⟨ψ₂, hn₂, hψ₂⟩ := ih
    refine ⟨GenPredIn.or ψ₁ ψ₂, by show (_ && _) = true; rw [hn₁, hn₂]; rfl, fun y u γ => ?_⟩
    rw [holdsPlain_or_iff, hψ₁, hψ₂, List.any_cons]
    simp

/-- **Every frame condition is a predicate of the query language.** -/
theorem FrameCond.exists_condPred {c : ℕ} (O : Tuple (Fin n) p) :
    ∀ fc : FrameCond p,
      ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
        ψ.noFun = true ∧
        ∀ (y u : Tuple T n) (γ : Fin c → T),
          ψ.holdsPlain y (Fin.append u γ)
            ↔ fc.holds (Tuple.key O y) (Tuple.key O u) = true := by
  intro fc
  induction fc with
  | whole =>
    exact ⟨truePred, rfl, fun y u γ =>
      ⟨fun _ => rfl, fun _ => holdsPlain_truePred y _⟩⟩
  | le o =>
    obtain ⟨ψ, hn, hψ⟩ := exists_framePred_rangeUpTo (c := c) O o (none : Option (Selection T n))
    exact ⟨ψ, hn rfl, fun y u γ => (hψ y u γ).trans (and_iff_left rfl)⟩
  | lt o =>
    obtain ⟨ψ, hn, hψ⟩ := exists_framePred_rangeBefore (c := c) O o (none : Option (Selection T n))
    exact ⟨ψ, hn rfl, fun y u γ => (hψ y u γ).trans (and_iff_left rfl)⟩
  | ge o =>
    obtain ⟨ψ, hn, hψ⟩ := exists_framePred_rangeUpTo (c := c) O o.reverse
      (none : Option (Selection T n))
    refine ⟨ψ, hn rfl, fun y u γ => ((hψ y u γ).trans (and_iff_left rfl)).trans ?_⟩
    show OrderSpec.le o.reverse (Tuple.key O y) (Tuple.key O u) = true ↔ _
    rw [OrderSpec.le_reverse]
    exact Iff.rfl
  | gt o =>
    obtain ⟨ψ, hn, hψ⟩ := exists_framePred_rangeBefore (c := c) O o.reverse
      (none : Option (Selection T n))
    refine ⟨ψ, hn rfl, fun y u γ => ((hψ y u γ).trans (and_iff_left rfl)).trans ?_⟩
    show OrderSpec.lt o.reverse (Tuple.key O y) (Tuple.key O u) = true ↔ _
    rw [OrderSpec.lt_reverse]
    exact Iff.rfl
  | and a b iha ihb =>
    obtain ⟨ψ₁, hn₁, hψ₁⟩ := iha
    obtain ⟨ψ₂, hn₂, hψ₂⟩ := ihb
    refine ⟨GenPredIn.and ψ₁ ψ₂, by show (_ && _) = true; rw [hn₁, hn₂]; rfl, fun y u γ => ?_⟩
    rw [holdsPlain_and_iff, hψ₁, hψ₂]
    show _ ↔ (_ && _) = true
    rw [Bool.and_eq_true]
  | or a b iha ihb =>
    obtain ⟨ψ₁, hn₁, hψ₁⟩ := iha
    obtain ⟨ψ₂, hn₂, hψ₂⟩ := ihb
    refine ⟨GenPredIn.or ψ₁ ψ₂, by show (_ && _) = true; rw [hn₁, hn₂]; rfl, fun y u γ => ?_⟩
    rw [holdsPlain_or_iff, hψ₁, hψ₂]
    show _ ↔ (_ || _) = true
    rw [Bool.or_eq_true]
  | orAll cs ih =>
    exact exists_anyPred O (fun j => (cs j).holds) ih _

/-- **A frame and a `FILTER` clause are a predicate of the language**:
what `prop:winderived` spells a window's frame out with, for every frame
the syntax can name and every clause. -/
theorem ValueFrame.exists_framePred {c : ℕ} (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (keep : Option (Selection T n)) :
    ∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
      (Selection.noFunOpt keep = true → ψ.noFun = true) ∧
      ∀ (y u : Tuple T n) (γ : Fin c → T),
        ψ.holdsPlain y (Fin.append u γ)
          ↔ (w.ρ (Tuple.key O y) (Tuple.key O u) = true
              ∧ Selection.keepsOpt keep y = true) := by
  obtain ⟨ψ, hn, hψ⟩ := FrameCond.exists_condPred (T := T) (c := c) O w.cond
  refine ⟨GenPredIn.and ψ (clausePredOpt keep),
    fun hk => by simp only [GenPredIn.noFun, hn, noFun_clausePredOpt, hk, Bool.and_self],
    fun y u γ => ?_⟩
  rw [holdsPlain_and_iff, holdsPlain_clausePredOpt, hψ]
  exact Iff.rfl

/-- **The group of the clause-kept frame reads what the filtered window
reads.** Both are sorted by the window's clause, and cutting a sorted
reading down to what a `FILTER` keeps is the same, on the values read, as
sorting the cut (`OrderSpec.filter_sortSeq_map_eq`); what is left is two
listings of one multiset, which sort alike on those values
(`OrderSpec.sortSeq_map_eq`). -/
theorem ValueFrame.groupSeqOrd_filter_map_eq {c : ℕ} (O : Tuple (Fin n) p)
    (o : OrderSpec p) (t : TermIn T c n) (keep : Tuple T n → Bool)
    (X : Multiset (Tuple T n)) (γ : Fin c → T) :
    (Relation.groupSeqOrd (fun k : Fin 0 => k.elim0) (GroupOrder.byCols O o)
        (Multiset.filter (fun y => keep y = true) X)
        (fun k : Fin 0 => k.elim0)).map (fun v => t.eval v γ)
      = ((OrderSpec.sortSeq (Tuple.key O) (id : Tuple T n → Tuple T n) o
          (sortList X)).filter keep).map (fun v => t.eval v γ) := by
  have hgs : Relation.groupSeqOrd (fun k : Fin 0 => k.elim0)
      (GroupOrder.byCols O o) (Multiset.filter (fun y => keep y = true) X)
      (fun k : Fin 0 => k.elim0)
      = OrderSpec.sortSeq (Tuple.key O) (id : Tuple T n → Tuple T n) o
        (sortList (Multiset.filter (fun y => keep y = true) X)) := by
    show OrderSpec.sortSeq (Tuple.key O) (id : Tuple T n → Tuple T n) o
        (Relation.groupSeq (fun k : Fin 0 => k.elim0) _
          (fun k : Fin 0 => k.elim0)) = _
    rw [Relation.groupSeq_emptyKey]
  rw [hgs]
  refine Eq.trans ?_ (OrderSpec.filter_sortSeq_map_eq (key := Tuple.key O)
    (val := (id : Tuple T n → Tuple T n)) (o := o) (fun v => t.eval v γ) keep
    (sortList X)).symm
  refine OrderSpec.sortSeq_map_eq (key := Tuple.key O)
    (val := (id : Tuple T n → Tuple T n)) (o := o) (fun v => t.eval v γ) ?_
  refine Multiset.coe_eq_coe.mp ?_
  rw [sortList_coe]
  conv_lhs => rw [← sortList_coe X]
  refine Eq.trans (Multiset.filter_coe
    (p := fun y : Tuple T n => keep y = true) (sortList X))
    (congrArg Multiset.ofList ?_)
  exact congrArg (fun pp => List.filter pp (sortList X))
    (funext (fun b => by simp))

/-- **A window is an apply of a scalar aggregation** (`prop:winderived`),
over plain relations, in the generality the document's statement has: the
rows the selection keeps are the current row's frame cut down by the
window's `FILTER` clause, the group reads them in the order the window
reads them, and a `DISTINCT` window is the same with `f^distinct` as the
aggregate. The selection's predicate therefore has to hold exactly where
the frame condition holds *and* the clause keeps the row, which is a
conjunction of two predicates of the language. -/
theorem evaluatePlain_winByApplyOn {c : ℕ} {κ' : Fin n → ColKind}
    (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) {w : ValueFrame T p}
    (hc : w.ContainsSelf) (ψ : GenPredIn T (n + c) (ColKind.allReg n))
    (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (keep : Option (Selection T n))
    (hρ : ∀ (y u : Tuple T n) (γ : Fin c → T),
      ψ.holdsPlain y (Fin.append u γ)
        ↔ (w.ρ (Tuple.key O y) (Tuple.key O u) = true
            ∧ Selection.keepsOpt keep y = true))
    (hrr : WinReadsReg κ' P O t) (qo : AggQueryIn T c n κ')
    (q qf : AggQueryIn T c n (ColKind.allReg n))
    (hq : ∀ (D : Database T) (γ : Fin c → T),
      q.evaluatePlain D γ = qo.evaluatePlain D γ)
    (hqf : ∀ (D : Database T) (γ : Fin c → T),
      qf.evaluatePlain D γ
        = (qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
    (D : Database T) (γ : Fin c → T) :
    (winByApplyOn P O o ψ t (if dist then f.distinct else f) q
        qf).evaluatePlain D γ
      = (AggQueryIn.Win P O o w t f qo hrr dist keep).evaluatePlain D γ := by
  rw [winByApplyOn, AggQueryIn.evaluatePlain_castKind]
  show (q.evaluatePlain D γ).bind (fun u =>
      ((AggQueryIn.GammaScalar ![t.substMap (applyOuter T c n)]
        ![if dist then f.distinct else f]
        (AggQueryIn.Sel (GenPredIn.and
            (outerKeyCond P (fun _ => rfl) (fun k => Fin.castAdd c (P k))) ψ)
          (qf.substMap (applyOuter T c n)))
        (GroupOrder.byCols O o)).evaluatePlain D
          (Fin.append u γ)).map (fun v => (Fin.append u v : Tuple T (n + 1))))
    = (qo.evaluatePlain D γ).map (fun u : Tuple T n =>
      (Fin.snoc u (ValueFrame.windowValueOpt P O o w t
        (if dist then f.distinct else f) keep
        ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
        (ColKind.readTuple κ' u) γ) : Tuple T (n + 1)))
  rw [hq D γ]
  refine Eq.trans (Multiset.bind_congr (fun u hu => ?_))
    (Multiset.bind_singleton (s := qo.evaluatePlain D γ) (fun u =>
      (Fin.snoc u (ValueFrame.windowValueOpt P O o w t
        (if dist then f.distinct else f) keep
        ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
        (ColKind.readTuple κ' u) γ) : Tuple T (n + 1))))
  -- the rows the selection keeps are the frame's rows the clause keeps
  have hframe : (AggQueryIn.Sel
        (GenPredIn.and
          (outerKeyCond P (fun _ => rfl) (fun k => Fin.castAdd c (P k))) ψ)
        (qf.substMap (applyOuter T c n))).evaluatePlain D (Fin.append u γ)
      = Multiset.filter (fun y : Tuple T n =>
          Selection.keepsOpt keep y = true)
        (ValueFrame.frameOf (α := Tuple T n) id P O w
          ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
            (ColKind.readTuple κ' u)) := by
    show Multiset.filter (fun y : Tuple T n =>
        (GenPredIn.and
          (outerKeyCond P (fun _ => rfl) (fun k => Fin.castAdd c (P k)))
          ψ).holdsPlain y (Fin.append u γ))
        ((qf.substMap (applyOuter T c n)).evaluatePlain D (Fin.append u γ)) = _
    rw [AggQueryIn.evaluatePlain_substMap, substVal_applyOuter, hqf D γ,
      ValueFrame.frameOf_of_containsSelf _ _ _ hc _
        (Multiset.mem_map_of_mem (ColKind.readTuple κ') hu),
      Multiset.filter_filter]
    refine Multiset.filter_congr (fun y _ => ?_)
    rw [holdsPlain_and_iff, outerKeyCond_holdsPlain, hρ y u γ,
      show Tuple.key P (id (ColKind.readTuple κ' u)) = Tuple.key P u from
        Tuple.key_readTuple P hrr.1 u,
      show Tuple.key O (id (ColKind.readTuple κ' u)) = Tuple.key O u from
        Tuple.key_readTuple O hrr.2.1 u]
    constructor
    · intro hk
      exact ⟨hk.2.2,
        funext (fun k => (hk.1 k).trans (Fin.append_left u γ (P k))), hk.2.1⟩
    · intro hk
      exact ⟨fun k => (congrFun hk.2.1 k).trans
        (Fin.append_left u γ (P k)).symm, hk.2.2, hk.1⟩
  rw [gammaScalar_one, hframe, Multiset.map_singleton]
  refine congrArg (fun x : Tuple T (n + 1) =>
    ({x} : Multiset (Tuple T (n + 1)))) ?_
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last,
      show (Fin.last n) = Fin.natAdd n (0 : Fin 1) from rfl, Fin.append_right]
    have hmap : (Relation.groupSeqOrd (fun k : Fin 0 => k.elim0)
          (GroupOrder.byCols O o)
          (Multiset.filter (fun y : Tuple T n =>
            Selection.keepsOpt keep y = true)
            (ValueFrame.frameOf (α := Tuple T n) id P O w
              ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
                (ColKind.readTuple κ' u))) (fun k : Fin 0 => k.elim0)).map
          (fun v => (t.substMap (applyOuter T c n)).eval v (Fin.append u γ))
        = (Relation.groupSeqOrd (fun k : Fin 0 => k.elim0)
          (GroupOrder.byCols O o)
          (Multiset.filter (fun y : Tuple T n =>
            Selection.keepsOpt keep y = true)
            (ValueFrame.frameOf (α := Tuple T n) id P O w
              ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
                (ColKind.readTuple κ' u))) (fun k : Fin 0 => k.elim0)).map
          (fun v => t.eval v γ) :=
      List.map_congr_left (fun v _ => by
        rw [TermIn.eval_substMap, substVal_applyOuter])
    rw [hmap]
    · cases keep with
      | none =>
        rw [ValueFrame.windowValueOpt_none]
        unfold ValueFrame.windowValue ValueFrame.frameListOf
        refine congrArg _ (congrArg _ ?_)
        show Relation.groupSeqOrd (fun k : Fin 0 => k.elim0)
            (GroupOrder.byCols O o) _ (fun k : Fin 0 => k.elim0) = _
        rw [show Multiset.filter (fun y : Tuple T n =>
              Selection.keepsOpt (T := T) none y = true)
            (ValueFrame.frameOf (α := Tuple T n) id P O w
              ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
                (ColKind.readTuple κ' u))
            = ValueFrame.frameOf (α := Tuple T n) id P O w
              ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
                (ColKind.readTuple κ' u) from
          Multiset.filter_eq_self.mpr (fun _ _ => rfl)]
        show OrderSpec.sortSeq (Tuple.key O) (id : Tuple T n → Tuple T n) o
            (Relation.groupSeq (fun k : Fin 0 => k.elim0) _
              (fun k : Fin 0 => k.elim0)) = _
        rw [Relation.groupSeq_emptyKey]
      | some φ =>
        rw [ValueFrame.windowValueOpt_some]
        unfold ValueFrame.windowValueWhen ValueFrame.frameListOf
        exact congrArg _ (ValueFrame.groupSeqOrd_filter_map_eq O o t φ.keeps
          (ValueFrame.frameOf (α := Tuple T n) id P O w
            ((qo.evaluatePlain D γ).map (ColKind.readTuple κ'))
              (ColKind.readTuple κ' u)) γ)
  · rw [Fin.snoc_castSucc,
      show (Fin.castSucc i) = Fin.castAdd 1 i from rfl, Fin.append_left]

/-- The all-regular case, which is the shape `prop:winderived` states:
there the frame reads the input itself. -/
theorem evaluatePlain_winByApplyOf {c : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) {w : ValueFrame T p}
    (hc : w.ContainsSelf) (ψ : GenPredIn T (n + c) (ColKind.allReg n))
    (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (keep : Option (Selection T n))
    (hρ : ∀ (y u : Tuple T n) (γ : Fin c → T),
      ψ.holdsPlain y (Fin.append u γ)
        ↔ (w.ρ (Tuple.key O y) (Tuple.key O u) = true
            ∧ Selection.keepsOpt keep y = true))
    (q : AggQueryIn T c n (ColKind.allReg n)) (D : Database T)
    (γ : Fin c → T) :
    (winByApply P O o ψ t (if dist then f.distinct else f) q).evaluatePlain D γ
      = (AggQueryIn.Win P O o w t f q (winReadsReg_allReg P O t) dist
          keep).evaluatePlain D γ :=
  evaluatePlain_winByApplyOn P O o hc ψ t f dist keep hρ
    (winReadsReg_allReg P O t) q q q (fun _ _ => rfl)
    (fun D γ => (ColKind.map_readTuple_allReg (q.evaluatePlain D γ)).symm) D γ
/-- **A window is an apply of a scalar aggregation** (`prop:winderived`),
over plain relations: the rows the selection keeps are the current row's
frame, the clause reads them in the order the window reads them, and the
aggregate is then the window's value. This is the plain form, with
neither `DISTINCT` nor a `FILTER` clause;
`evaluatePlain_winByApplyOf` has both. -/

theorem evaluatePlain_winByApply {c : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) {w : ValueFrame T p}
    (hc : w.ContainsSelf) (ψ : GenPredIn T (n + c) (ColKind.allReg n))
    (hρ : ∀ (y u : Tuple T n) (γ : Fin c → T),
      ψ.holdsPlain y (Fin.append u γ)
        ↔ w.ρ (Tuple.key O y) (Tuple.key O u) = true)
    (t : TermIn T c n) (f : SeqAggFunc T)
    (q : AggQueryIn T c n (ColKind.allReg n)) (D : Database T)
    (γ : Fin c → T) :
    (winByApply P O o ψ t f q).evaluatePlain D γ
      = (AggQueryIn.Win P O o w t f q
          (winReadsReg_allReg P O t)).evaluatePlain D γ := by
  have h := evaluatePlain_winByApplyOf P O o hc ψ t f false none
    (fun y u γ => by
      rw [hρ y u γ]
      exact (and_iff_left rfl).symm) q D γ
  simpa using h

/-- **The derived form uses no window**: an apply, a scalar aggregation
and a selection, which is what the generation half of `thm:plainbasis`
asks of it. The apply then goes by the decorrelation. -/
theorem usesOnly_winByApplyOn {c : ℕ} {S : Set OpKind} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ψ : GenPredIn T (n + c) (ColKind.allReg n)) (t : TermIn T c n)
    (f : SeqAggFunc T) {q qf : AggQueryIn T c n (ColKind.allReg n)}
    (ha : OpKind.apply ∈ S) (hg : OpKind.gamma ∈ S) (hs : OpKind.sel ∈ S)
    (hq : q.usesOnly S) (hqf : qf.usesOnly S) :
    (winByApplyOn P O o ψ t f q qf).usesOnly S := by
  rw [winByApplyOn, AggQueryIn.usesOnly_castKind]
  exact ⟨ha, hq, hg, hs, (AggQueryIn.usesOnly_substMap qf _).mpr hqf⟩

/-- The same where the frame reads the input itself. -/
theorem usesOnly_winByApply {c : ℕ} {S : Set OpKind} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ψ : GenPredIn T (n + c) (ColKind.allReg n)) (t : TermIn T c n)
    (f : SeqAggFunc T) {q : AggQueryIn T c n (ColKind.allReg n)}
    (ha : OpKind.apply ∈ S) (hg : OpKind.gamma ∈ S) (hs : OpKind.sel ∈ S)
    (hq : q.usesOnly S) : (winByApply P O o ψ t f q).usesOnly S :=
  usesOnly_winByApplyOn P O o ψ t f ha hg hs hq hq

/-- **The derived form names the relations the window names.** -/
theorem overSchema_winByApplyOn {c : ℕ} {sch : Schema} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ψ : GenPredIn T (n + c) (ColKind.allReg n)) (t : TermIn T c n)
    (f : SeqAggFunc T) {q qf : AggQueryIn T c n (ColKind.allReg n)}
    (hq : q.overSchema sch) (hqf : qf.overSchema sch) :
    (winByApplyOn P O o ψ t f q qf).overSchema sch := by
  rw [winByApplyOn, AggQueryIn.overSchema_castKind]
  exact ⟨hq, (AggQueryIn.overSchema_substMap qf _ sch).mpr hqf⟩

/-- The same where the frame reads the input itself. -/
theorem overSchema_winByApply {c : ℕ} {sch : Schema} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ψ : GenPredIn T (n + c) (ColKind.allReg n)) (t : TermIn T c n)
    (f : SeqAggFunc T) {q : AggQueryIn T c n (ColKind.allReg n)}
    (hq : q.overSchema sch) : (winByApply P O o ψ t f q).overSchema sch :=
  overSchema_winByApplyOn P O o ψ t f hq hq

/-- **A window is expressible without one** (`prop:winderived`), as the
equivalence of queries the classification uses. -/
theorem plainEquiv_winByApply {c : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) {w : ValueFrame T p}
    (hc : w.ContainsSelf) (ψ : GenPredIn T (n + c) (ColKind.allReg n))
    (hρ : ∀ (y u : Tuple T n) (γ : Fin c → T),
      ψ.holdsPlain y (Fin.append u γ)
        ↔ w.ρ (Tuple.key O y) (Tuple.key O u) = true)
    (t : TermIn T c n) (f : SeqAggFunc T)
    (q : AggQueryIn T c n (ColKind.allReg n)) :
    (AggQueryIn.Win P O o w t f q
        (winReadsReg_allReg P O t)).PlainEquiv (winByApply P O o ψ t f q) :=
  fun D γ => (evaluatePlain_winByApply P O o hc ψ hρ t f q D γ).symm

end WinDerived

/-! ## Aggregation: the one operator that makes a row from nothing -/

omit [ValueType T] in
/-- The instance with a name bound to the empty relation is still
empty. -/
private theorem allEmpty_assign {D : Database T} (hD : D.allEmpty)
    (s : String) (m : ℕ) : (D.assign s (0 : Relation T m)).allEmpty := by
  intro k s' r hf
  by_cases hc : k = m ∧ s' = s
  · obtain ⟨rfl, rfl⟩ := hc
    rw [Database.find_assign] at hf
    exact (Option.some.inj hf).symm
  · rw [Database.find_assign_of_ne s s' _ D hc] at hf
    exact hD k s' r hf

/-- **Without `γ`, the empty instance has an empty answer.** Every other
operator maps the empty relation to an empty relation: a projection and a
window map it row by row, a selection filters it, a product and an apply
read one row of each side, a union adds, duplicate elimination and
difference only remove. Aggregation is the exception, the scalar form
emitting its row whatever its input. -/
theorem AggQueryIn.evaluatePlain_eq_zero_of_allEmpty {S : Set OpKind}
    (hγ : OpKind.gamma ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → ∀ (D : Database T), D.allEmpty → ∀ γ : Fin c → T,
      q.evaluatePlain D γ = 0 := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ D hD γ
    simp only [AggQueryIn.evaluatePlain]
    cases hf : D.find n s with
    | none => rfl
    | some rn => exact hD n s rn hf
  | Hole n s =>
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
  | Sel φ q _ ih =>
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
  | Explode k hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | Retag hk q ih => intro hq D hD γ; exact ih hq D hD γ
  | @Mu _ nm s q₀ q₁ ih₀ ih₁ =>
    intro hq D hD γ
    show muSumFix (fun X => q₁.evaluatePlain (D.assign s X) γ)
        (q₀.evaluatePlain D γ) = 0
    have hstep : (fun X => q₁.evaluatePlain (D.assign s X) γ)
        (0 : Relation T nm) = 0 :=
      ih₁ hq.2.2 (D.assign s (0 : Relation T nm))
        (allEmpty_assign hD s nm) γ
    rw [ih₀ hq.2.1 D hD γ, muSumFix, muSum_zero_of_step_zero hstep]
  | @MuSet _ nm s q₀ q₁ ih₀ ih₁ =>
    intro hq D hD γ
    show muFix (fun X => (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup) = 0
    refine muFix_zero_of_step_zero ?_
    show (q₀.evaluatePlain D γ
      + q₁.evaluatePlain (D.assign s (0 : Relation T nm)) γ).dedup = 0
    rw [ih₀ hq.2.1 D hD γ,
      ih₁ hq.2.2 (D.assign s (0 : Relation T nm))
        (allEmpty_assign hD s nm) γ]
    rfl
  | Gamma is ts fs q keep ord ih => intro hq; exact absurd hq.1 hγ
  | GammaScalar ts fs q ord ih => intro hq; exact absurd hq.1 hγ
  | GammaNest is his p f q ih => intro hq; exact absurd hq.1.1 hγ
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
