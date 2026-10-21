module

public import Provenance.BasisAssembly
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# `⊎` from `μ^⊎` in the minimal universe

`⊎` is in every basis of the recursion-free algebra
(`union_mem_of_generatesOn`), but with a bag recursion the union is a
derived operator. The construction (checked on
PostgreSQL 18): for `R`, `S` of arity `k`, two constants
`p₀ ≠ p₁`, a `k`-tuple `c̄`, and `Z_R`, `Z_S` the two relations with the
tag `p₀` prepended,

* `Q_R := μ^⊎Y.( {(p₀, c̄)},  Π_{p₁, r}(σ_{#0 ≐ #(k+1)}(Y × Z_R)) )`
* `T   := μ^⊎Y.( Q_R,         Π_{p₁, s}(σ_{#0 ≐ #(k+1)}(Y × Z_S)) )`
* `R ⊎ S = Π_{#1..#k}(σ_{#0 ≢ p₀}(T))`.

The rounds of `Q_R`: `{(p₀, c̄)}`, then `{(p₁, r) : r ∈ R}` – each row
derived from `(p₀, c̄)` alone, since only a row of phase `p₀` passes the
selection, so with `r`'s own multiplicity – then `∅`, the phase being
`p₁`. The rounds of `T`: `Q_R`, then `{(p₁, s) : s ∈ S}`, again from
`(p₀, c̄)` alone, then `∅`. Both settle on every instance, in two
rounds; the restriction on recursive terms is met (`Y` once, on the left
of an apply, under a selection on regular columns and a projection; the bases
closed, `Q_R` being a closed query with its own recursion); and the
multiplicities of `R` and `S` add up through the final projection, as
`⊎` wants. What a single recursion cannot do – its body reads one fixed
relation every round – the base `Q_R` does: it supplies the rows of `R`
with their multiplicities *and* one row of multiplicity `1` for the
round that reads `S` to start from.

`AggQueryIn.sumByMu` is the construction, `evaluatePlain_sumByMu` its
evaluation, and `AggQueryIn.exists_sumFree` the pass: every query of the
minimal universe is equivalent, wherever it settles, to one with no `⊎`,
over `{∅, Π, σ, apply, γ, μ^⊎}` and whatever else it used – the product
of each round being written as an apply, since a basis holds one of the
two and the apply is the one a recursive term may sit under. The two bound
names of each construction have to be **fresh** – declared by no
relation of the schema and occurring nowhere in the query, bound names
included – so the pass takes a supply of fresh names, an injective
`f : ℕ → String`, and `AggQueryIn.names` lists what a name must avoid;
`exists_freshSupply` provides the supply for a finitely-supported
schema, `String` being infinite.
-/

@[expose] public section

variable {T : Type} [ValueType T]

/-! ## The names of a query, bound names included -/

/-- **Every name a query mentions**, the names its recursions bind
included: what a fresh name has to avoid. -/
def AggQueryIn.names : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Finset String
  | _, _, _, _, .Rel _ s => {s}
  | _, _, _, _, .Hole _ s _ => {s}
  | _, _, _, _, .Param _ _ => ∅
  | _, _, _, _, .Empty => ∅
  | _, _, _, _, .Proj _ q => q.names
  | _, _, _, _, .Sel _ q _ => q.names
  | _, _, _, _, .Prod q₁ q₂ => Union.union q₁.names q₂.names
  | _, _, _, _, .Apply q₁ q₂ => Union.union q₁.names q₂.names
  | _, _, _, _, .Sum q₁ q₂ => Union.union q₁.names q₂.names
  | _, _, _, _, .Dedup q => q.names
  | _, _, _, _, .Diff q₁ q₂ => Union.union q₁.names q₂.names
  | _, _, _, _, .Explode _ _ q => q.names
  | _, _, _, _, .Retag _ q => q.names
  | _, _, _, _, .Mu s q₀ q₁ => insert s (Union.union q₀.names q₁.names)
  | _, _, _, _, .MuSet s q₀ q₁ => insert s (Union.union q₀.names q₁.names)
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.names
  | _, _, _, _, .GammaScalar _ _ q _ => q.names
  | _, _, _, _, .GammaNest _ _ _ _ q => q.names
  | _, _, _, _, .ProvSum _ _ _ q => q.names
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.names
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.names
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.names

omit [ValueType T] in
/-- A name the query does not mention is not mentioned. -/
theorem AggQueryIn.noMention_of_not_mem_names {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      s ∉ q.names → q.noMention s := by
  intro c n κ l q
  induction q with
  | Rel n s' => exact fun h h' => h (h' ▸ Finset.mem_singleton_self s')
  | Hole n s' => exact fun _ => trivial
  | Param pv ρ => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q _ ih => exact fun h => ih h
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun h => ⟨ih₁ (fun h' => h (Finset.mem_union_left _ h')),
      ih₂ (fun h' => h (Finset.mem_union_right _ h'))⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun h => ⟨ih₁ (fun h' => h (Finset.mem_union_left _ h')),
      ih₂ (fun h' => h (Finset.mem_union_right _ h'))⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun h => ⟨ih₁ (fun h' => h (Finset.mem_union_left _ h')),
      ih₂ (fun h' => h (Finset.mem_union_right _ h'))⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun h => ⟨ih₁ (fun h' => h (Finset.mem_union_left _ h')),
      ih₂ (fun h' => h (Finset.mem_union_right _ h'))⟩
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    exact fun h => ⟨ih₀ (fun h' => h (Finset.mem_insert_of_mem (Finset.mem_union_left _ h'))),
      ih₁ (fun h' => h (Finset.mem_insert_of_mem (Finset.mem_union_right _ h')))⟩
  | MuSet s' q₀ q₁ ih₀ ih₁ =>
    exact fun h => ⟨ih₀ (fun h' => h (Finset.mem_insert_of_mem (Finset.mem_union_left _ h'))),
      ih₁ (fun h' => h (Finset.mem_insert_of_mem (Finset.mem_union_right _ h')))⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p f q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t f q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

/-- Two declarations of distinct names commute. -/
theorem Schema.update_comm (sch : Schema) {s s' : String} (h : s ≠ s') (m m' : ℕ) :
    (sch.update s m).update s' m' = (sch.update s' m').update s m := by
  refine Schema.ext (fun t => ?_)
  simp only [Schema.update_apply]
  by_cases hs : t = s'
  · subst hs; simp [Ne.symm h]
  · by_cases hs' : t = s
    · subst hs'; simp [h]
    · simp [hs, hs']

omit [ValueType T] in
/-- Declaring a name the query does not mention keeps it well-formed. -/
theorem AggQueryIn.overSchema_update_of_not_mem_names {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
        (q : AggQueryIn T c n κ l) {sch : Schema},
      q.overSchema sch → s ∉ q.names → q.overSchema (sch.update s m) := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro sch h hn
    have hne : s' ≠ s := fun h' => hn (h' ▸ Finset.mem_singleton_self s')
    show (if s' = s then some m else sch s') = some n
    rw [ite_eq_right hne]; exact h
  | Hole n s' =>
    intro sch h hn
    have hne : s' ≠ s := fun h' => hn (h' ▸ Finset.mem_singleton_self s')
    show (if s' = s then some m else sch s') = some n
    rw [ite_eq_right hne]; exact h
  | Param pv ρ => exact fun _ _ => trivial
  | Empty => exact fun _ _ => trivial
  | Proj ps q ih => exact fun h hn => ih h hn
  | Sel φ q _ ih => exact fun h hn => ih h hn
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun h hn => ⟨ih₁ h.1 (fun h' => hn (Finset.mem_union_left _ h')),
      ih₂ h.2 (fun h' => hn (Finset.mem_union_right _ h'))⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun h hn => ⟨ih₁ h.1 (fun h' => hn (Finset.mem_union_left _ h')),
      ih₂ h.2 (fun h' => hn (Finset.mem_union_right _ h'))⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun h hn => ⟨ih₁ h.1 (fun h' => hn (Finset.mem_union_left _ h')),
      ih₂ h.2 (fun h' => hn (Finset.mem_union_right _ h'))⟩
  | Dedup q ih => exact fun h hn => ih h hn
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun h hn => ⟨ih₁ h.1 (fun h' => hn (Finset.mem_union_left _ h')),
      ih₂ h.2 (fun h' => hn (Finset.mem_union_right _ h'))⟩
  | Explode k hk q ih => exact fun h hn => ih h hn
  | Retag hk q ih => exact fun h hn => ih h hn
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    intro sch h hn
    have hne : s ≠ s' := fun h' => hn (by rw [h']; exact Finset.mem_insert_self _ _)
    refine ⟨?_, ih₀ h.2.1 (fun h' => hn (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ h'))), h.2.2.1, ?_⟩
    · show (if s' = s then some m else sch s') = none
      rw [ite_eq_right hne.symm]; exact h.1
    · rw [Schema.update_comm sch hne]
      exact ih₁ h.2.2.2 (fun h' => hn (Finset.mem_insert_of_mem (Finset.mem_union_right _ h')))
  | MuSet s' q₀ q₁ ih₀ ih₁ =>
    intro sch h hn
    have hne : s ≠ s' := fun h' => hn (by rw [h']; exact Finset.mem_insert_self _ _)
    refine ⟨?_, ih₀ h.2.1 (fun h' => hn (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ h'))), h.2.2.1, ?_⟩
    · show (if s' = s then some m else sch s') = none
      rw [ite_eq_right hne.symm]; exact h.1
    · rw [Schema.update_comm sch hne]
      exact ih₁ h.2.2.2 (fun h' => hn (Finset.mem_insert_of_mem (Finset.mem_union_right _ h')))
  | Gamma is ts fs q keep ord ih => exact fun h hn => ih h hn
  | GammaScalar ts fs q ord ih => exact fun h hn => ih h hn
  | GammaNest is his p f q ih => exact fun h hn => ih h hn
  | ProvSum is his t q ih => exact fun h hn => ih h hn
  | GammaTok is his ts fs a q keep ih => exact fun h hn => ih h hn
  | Win P O o w t f q hrr dist keep ih => exact fun h hn => ih h hn
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h hn => ih h hn

/-! ### What a kind cast keeps -/

omit [ValueType T] in
@[simp] theorem AggQueryIn.names_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c n κ l) : (q.castKind h).names = q.names := by
  cases h; rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.hygienic_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List
    (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).hygienic ↔ q.hygienic := by
  cases h; exact Iff.rfl

@[simp] theorem AggQueryIn.settlesAt_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List
    (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    (q.castKind h).SettlesAt D γ ↔ q.SettlesAt D γ := by
  cases h; exact Iff.rfl

omit [ValueType T] in
/-- A term with a hole names the hole's relation. -/
theorem AggQueryIn.mem_names_of_index {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (s, m) ∈ l → s ∈ q.names := by
  intro c n κ l q
  induction q with
  | Rel n s' => exact fun h => by simp at h
  | Hole n s' =>
    intro h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (List.mem_singleton.mp h)
    exact Finset.mem_singleton_self _
  | Param pv ρ => exact fun h => by simp at h
  | Empty => exact fun h => by simp at h
  | Proj ps q ih => exact ih
  | Sel φ q _ ih => exact ih
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun h => (List.mem_append.mp h).elim
      (fun h => Finset.mem_union_left _ (ih₁ h)) (fun h => Finset.mem_union_right _ (ih₂ h))
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => Finset.mem_union_left _ (ih₁ h)
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun h => (List.mem_append.mp h).elim
      (fun h => Finset.mem_union_left _ (ih₁ h)) (fun h => Finset.mem_union_right _ (ih₂ h))
  | Dedup q ih => exact fun h => by simp at h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => by simp at h
  | Explode k hk q ih => exact ih
  | Retag hk q ih => exact ih
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => by simp at h
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => by simp at h
  | Gamma is ts fs q keep ord ih => exact fun h => by simp at h
  | GammaScalar ts fs q ord ih => exact fun h => by simp at h
  | GammaNest is his p f q ih => exact fun h => by simp at h
  | ProvSum is his t q ih => exact fun h => by simp at h
  | GammaTok is his ts fs a q keep ih => exact fun h => by simp at h
  | Win P O o w t f q hrr dist keep ih => exact fun h => by simp at h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => by simp at h

/-! ## The restriction, the signature and the names, through a substitution -/

omit [ValueType T] in
theorem TermIn.noFun_substMap {c d n : ℕ} (θ : Fin c → T ⊕ Fin d) (t : TermIn T c n) :
    (t.substMap θ).noFun = t.noFun := by
  cases t <;> try rfl
  rename_i k
  show (Sum.elim TermIn.const TermIn.outer (θ k)).noFun = true
  cases θ k <;> rfl

omit [ValueType T] in
theorem TermGIn.noFun_substMap {c d n : ℕ} {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d)
    (t : TermGIn T c κ) : (t.substMap θ).noFun = t.noFun := by
  cases t <;> try rfl
  rename_i k
  show (Sum.elim TermGIn.const TermGIn.outer (θ k)).noFun = true
  cases θ k <;> rfl

omit [ValueType T] in
theorem ProjColIn.noFun_substMap {c d n : ℕ} {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d)
    (p : ProjColIn T c κ) : (p.substMap θ).noFun = p.noFun := by
  cases p with
  | term t => exact TermGIn.noFun_substMap θ t
  | provTerm t => exact TermGIn.noFun_substMap θ t
  | _ => rfl

omit [ValueType T] in
theorem GenPredIn.noFun_substMap {c d n : ℕ} {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d)
    (φ : GenPredIn T c κ) : (φ.substMap θ).noFun = φ.noFun := by
  induction φ with
  | cmp op t₁ t₂ =>
    show ((t₁.substMap θ).noFun && (t₂.substMap θ).noFun) = (t₁.noFun && t₂.noFun)
    rw [TermGIn.noFun_substMap, TermGIn.noFun_substMap]
  | aggCmp k h op t => exact TermGIn.noFun_substMap θ t
  | aggRange k h op₁ t₁ op₂ t₂ =>
    show ((t₁.substMap θ).noFun && (t₂.substMap θ).noFun) = (t₁.noFun && t₂.noFun)
    rw [TermGIn.noFun_substMap, TermGIn.noFun_substMap]
  | and φ ψ ihφ ihψ =>
    show ((φ.substMap θ).noFun && (ψ.substMap θ).noFun) = (φ.noFun && ψ.noFun)
    rw [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    show ((φ.substMap θ).noFun && (ψ.substMap θ).noFun) = (φ.noFun && ψ.noFun)
    rw [ihφ, ihψ]
  | not φ ih => exact ih

omit [ValueType T] in
/-- A substitution changes no name. -/
theorem AggQueryIn.names_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).names = q.names := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ => rfl
  | Hole n s => exact fun θ => rfl
  | Param pv ρ => exact fun θ => rfl
  | Empty => exact fun θ => rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.names_castKind]
    exact ih θ
  | Sel φ q _ ih => exact fun θ => ih θ
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d θ
    show Union.union _ _ = Union.union _ _
    rw [ih₁ θ, ih₂ θ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d θ
    show Union.union _ _ = Union.union _ _
    rw [ih₁ θ, ih₂ _]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d θ
    show Union.union _ _ = Union.union _ _
    rw [ih₁ θ, ih₂ θ]
  | Dedup q ih => exact fun θ => ih θ
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d θ
    show Union.union _ _ = Union.union _ _
    rw [ih₁ θ, ih₂ θ]
  | Explode k hk q ih => exact fun θ => ih θ
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d θ
    show insert s (Union.union _ _) = insert s (Union.union _ _)
    rw [ih₀ θ, ih₁ θ]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ
    show insert s (Union.union _ _) = insert s (Union.union _ _)
    rw [ih₀ θ, ih₁ θ]
  | Gamma is ts fs q keep ord ih => exact fun θ => ih θ
  | GammaScalar ts fs q ord ih => exact fun θ => ih θ
  | GammaNest is his p fn q ih => exact fun θ => ih θ
  | ProvSum is his t q ih => exact fun θ => ih θ
  | GammaTok is his ts fs a q keep ih => exact fun θ => ih θ
  | Win P O o w t fw q hrr dist keep ih => exact fun θ => ih θ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => ih θ

omit [ValueType T] in
/-- Nor whether the recursions are hygienic. -/
theorem AggQueryIn.hygienic_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).hygienic ↔ q.hygienic := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ => Iff.rfl
  | Hole n s => exact fun θ => Iff.rfl
  | Param pv ρ => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.hygienic_castKind]
    exact ih θ
  | Sel φ q _ ih => exact fun θ => ih θ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ _)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Dedup q ih => exact fun θ => ih θ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Explode k hk q ih => exact fun θ => ih θ
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact fun θ => and_congr (AggQueryIn.noMention_substMap q₀ θ)
      (and_congr (AggQueryIn.noMention_substMap q₁ θ) (and_congr (ih₀ θ) (ih₁ θ)))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun θ => and_congr (AggQueryIn.noMention_substMap q₀ θ)
      (and_congr (AggQueryIn.noMention_substMap q₁ θ) (and_congr (ih₀ θ) (ih₁ θ)))
  | Gamma is ts fs q keep ord ih => exact fun θ => ih θ
  | GammaScalar ts fs q ord ih => exact fun θ => ih θ
  | GammaNest is his p fn q ih => exact fun θ => ih θ
  | ProvSum is his t q ih => exact fun θ => ih θ
  | GammaTok is his ts fs a q keep ih => exact fun θ => ih θ
  | Win P O o w t fw q hrr dist keep ih => exact fun θ => ih θ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => ih θ

/-- Nor the signature: a substitution puts a constant or a column where
an outer column was. -/
theorem AggQueryIn.inSig_substMap {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).inSig Θ ↔ q.inSig Θ := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ => Iff.rfl
  | Hole n s => exact fun θ => Iff.rfl
  | Param pv ρ => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.inSig_castKind]
    exact and_congr (forall_congr' fun j => by rw [ProjColIn.noFun_substMap]) (ih θ)
  | Sel φ q _ ih =>
    exact fun θ => and_congr (by rw [GenPredIn.noFun_substMap]) (ih θ)
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ _)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Dedup q ih => exact fun θ => ih θ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Explode k hk q ih => exact fun θ => ih θ
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | Gamma is ts fs q keep ord ih =>
    exact fun θ => and_congr (forall_congr' fun j => by rw [TermIn.noFun_substMap])
      (and_congr Iff.rfl (and_congr Iff.rfl (ih θ)))
  | GammaScalar ts fs q ord ih =>
    exact fun θ => and_congr (forall_congr' fun j => by rw [TermIn.noFun_substMap])
      (and_congr Iff.rfl (ih θ))
  | GammaNest is his p fn q ih =>
    exact fun θ => and_congr (by rw [ProjColIn.noFun_substMap])
      (and_congr Iff.rfl (ih θ))
  | ProvSum is his t q ih => exact fun θ => Iff.rfl
  | GammaTok is his ts fs a q keep ih => exact fun θ => Iff.rfl
  | Win P O o w t fw q hrr dist keep ih =>
    exact fun θ => and_congr (by rw [TermIn.noFun_substMap])
      (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (ih θ))))
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => Iff.rfl

/-- **A substituted query is defined where the query is**, under the
valuation the substitution induces. -/
theorem AggQueryIn.settlesAt_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d) (D : Database T) (γ : Fin d → T),
      (q.substMap θ).SettlesAt D γ ↔ q.SettlesAt D (substVal θ γ) := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ D γ => Iff.rfl
  | Hole n s => exact fun θ D γ => Iff.rfl
  | Param pv ρ => exact fun θ D γ => Iff.rfl
  | Empty => exact fun θ D γ => Iff.rfl
  | Proj ps q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap, AggQueryIn.settlesAt_castKind]
    exact ih θ D γ
  | Sel φ q _ ih => exact fun θ D γ => ih θ D γ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ D γ => and_congr (ih₁ θ D γ) (ih₂ θ D γ)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d θ D γ
    refine and_congr (ih₁ θ D γ) (forall_congr' fun u => ?_)
    show Multiset.Mem ((q₁.substMap θ).evaluatePlain D γ) u → _
      ↔ (Multiset.Mem (q₁.evaluatePlain D (substVal θ γ)) u → _)
    rw [AggQueryIn.evaluatePlain_substMap]
    exact imp_congr Iff.rfl (by rw [ih₂ _ D (Fin.append u γ), substVal_append])
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ D γ => and_congr (ih₁ θ D γ) (ih₂ θ D γ)
  | Dedup q ih => exact fun θ D γ => ih θ D γ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ D γ => and_congr (ih₁ θ D γ) (ih₂ θ D γ)
  | Explode k hk q ih => exact fun θ D γ => ih θ D γ
  | Retag hk q ih => exact fun θ D γ => ih θ D γ
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.SettlesAt, AggQueryIn.evaluatePlain_substMap, ih₀ θ, ih₁ θ]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.SettlesAt, AggQueryIn.evaluatePlain_substMap, ih₀ θ, ih₁ θ]
  | Gamma is ts fs q keep ord ih => exact fun θ D γ => ih θ D γ
  | GammaScalar ts fs q ord ih => exact fun θ D γ => ih θ D γ
  | GammaNest is his p fn q ih => exact fun θ D γ => ih θ D γ
  | ProvSum is his t q ih => exact fun θ D γ => ih θ D γ
  | GammaTok is his ts fs a q keep ih => exact fun θ D γ => ih θ D γ
  | Win P O o w t fw q hrr dist keep ih => exact fun θ D γ => ih θ D γ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ D γ => ih θ D γ


/-- Nor which windows are derivable. -/
theorem AggQueryIn.winsDerivable_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).WinsDerivable ↔ q.WinsDerivable := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ => Iff.rfl
  | Hole n s => exact fun θ => Iff.rfl
  | Param pv ρ => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.winsDerivable_castKind]
    exact ih θ
  | Sel φ q _ ih => exact fun θ => ih θ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ _)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Dedup q ih => exact fun θ => ih θ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Explode k hk q ih => exact fun θ => ih θ
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | Gamma is ts fs q keep ord ih => exact fun θ => ih θ
  | GammaScalar ts fs q ord ih => exact fun θ => ih θ
  | GammaNest is his p fn q ih => exact fun θ => ih θ
  | ProvSum is his t q ih => exact fun θ => ih θ
  | GammaTok is his ts fs a q keep ih => exact fun θ => ih θ
  | Win P O o w t fw q hrr dist keep ih =>
    exact fun θ => and_congr Iff.rfl (and_congr Iff.rfl (ih θ))
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => Iff.rfl

/-! ## The construction -/

namespace AggQueryIn

variable {c k : ℕ}

/-- The unit relation in a context of `c` outer columns: one empty row,
the scalar aggregation of the empty relation with no aggregate. -/
def unitC : AggQueryIn T c 0 (ColKind.allReg 0) :=
  (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) (fun j : Fin 0 => j.elim0) (fun j : Fin
      0 => j.elim0)
      (AggQueryIn.Empty : AggQueryIn T c 0 (ColKind.allReg 0))).castKind
    (funext fun j => j.elim0)

theorem evaluatePlain_unitC (D : Database T) (γ : Fin c → T) (u : Tuple T 0) :
    (unitC : AggQueryIn T c 0 _).evaluatePlain D γ = ({u} : Multiset (Tuple T 0)) := by
  show ((AggQueryIn.GammaScalar (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
    (AggQueryIn.Empty : AggQueryIn T c 0 (ColKind.allReg 0))).castKind
      (funext fun j => j.elim0)).evaluatePlain D γ = ({u} : Multiset (Tuple T 0))
  rw [AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  exact congrArg (fun v : Tuple T 0 => ({v} : Multiset (Tuple T 0)))
    (funext fun j => j.elim0)

/-- A row with a constant prepended. -/
def tagRow (t : T) (r : Tuple T k) : Tuple T (k + 1) := Fin.cons t r

omit [ValueType T] in
@[simp] theorem tagRow_zero (t : T) (r : Tuple T k) : tagRow t r 0 = t := rfl

omit [ValueType T] in
@[simp] theorem tagRow_succ (t : T) (r : Tuple T k) (i : Fin k) :
    tagRow t r (Fin.succ i) = r i := rfl

/-- The columns of a row with a constant prepended. -/
def withTagCols (t : T) : Fin (k + 1) → ProjColIn T c (ColKind.allReg k) :=
  Fin.cons (α := fun _ => ProjColIn T c (ColKind.allReg k)) (ProjColIn.term (TermGIn.const t))
    (fun i => ProjColIn.term (TermGIn.index i rfl))

omit [ValueType T] in
theorem withTagCols_kind (t : T) :
    (fun j => ((withTagCols (c := c) (k := k) t) j).kind) = ColKind.allReg (k + 1) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · rfl

/-- **A relation with the tag `t` prepended to every row.** -/
def withTag (t : T) (q : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c (k + 1) (ColKind.allReg (k + 1)) :=
  (AggQueryIn.Proj (withTagCols t) q).castKind (withTagCols_kind t)

theorem evaluatePlain_withTag (t : T) (q : AggQueryIn T c k (ColKind.allReg k))
    (D : Database T) (γ : Fin c → T) :
    (withTag t q).evaluatePlain D γ
      = (show Multiset (Tuple T k) from q.evaluatePlain D γ).map
          (tagRow t) := by
  rw [withTag, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  refine congrArg (fun f => Multiset.map f _) (funext fun u => funext fun j => ?_)
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · rfl

/-- **The driver row `(p₀, 0̄)`**, one row of multiplicity one. -/
def driver (p₀ : T) : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1)) :=
  (AggQueryIn.Proj (fun j => ProjColIn.term (TermGIn.const
      (tagRow p₀ (fun _ => 0) j))) unitC).castKind (funext fun _ => rfl)

theorem evaluatePlain_driver (p₀ : T) (D : Database T) (γ : Fin c → T) :
    (driver (k := k) p₀).evaluatePlain D γ
      = ({tagRow p₀ (fun _ => 0)} : Multiset (Tuple T (k + 1))) := by
  rw [driver, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  rw [evaluatePlain_unitC D γ (fun j => j.elim0), Multiset.map_singleton]
  rfl

/-- The product's first column is regular. -/
theorem prodKind_left (j : Fin (k + 1)) :
    Fin.append (ColKind.allReg (k + 1)) (ColKind.allReg (k + 1)) (Fin.castAdd (k + 1) j)
      = ColKind.reg := by
  rw [Fin.append_left]; rfl

theorem prodKind_right (j : Fin (k + 1)) :
    Fin.append (ColKind.allReg (k + 1)) (ColKind.allReg (k + 1)) (Fin.natAdd (k + 1) j)
      = ColKind.reg := by
  rw [Fin.append_right]; rfl

/-- The columns a round's rows are projected to: the tag `p₁`, then the
columns of the right factor past its tag. -/
def roundCols (p₁ : T) :
    Fin (k + 1) → ProjColIn T c (Fin.append (ColKind.allReg (k + 1)) (ColKind.allReg (k + 1))) :=
  Fin.cons (α := fun _ => ProjColIn T c _) (ProjColIn.term (TermGIn.const p₁))
    (fun i => ProjColIn.term (TermGIn.index (Fin.natAdd (k + 1) (Fin.succ i)) (prodKind_right _)))

/-- The row a round emits from a joined row, as one function (named so that
`Multiset.map_map` composes it against the opaque `Tuple`). -/
def roundProj (p₁ : T) (γ : Fin c → T) :
    Tuple T ((k + 1) + (k + 1)) → Tuple T (k + 1) :=
  fun u j => (roundCols p₁ j).evalPlain u γ

omit [ValueType T] in
theorem roundCols_kind (p₁ : T) :
    (fun j => ((roundCols (c := c) (k := k) p₁) j).kind) = ColKind.allReg (k + 1) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · rfl

/-- The selection keeping the pairs whose two tags agree. -/
def sameTag : GenPredIn T c (Fin.append (ColKind.allReg (k + 1)) (ColKind.allReg (k + 1))) :=
  GenPredIn.cmp CompOp.syneq
    (TermGIn.index (Fin.castAdd (k + 1) 0) (prodKind_left _))
    (TermGIn.index (Fin.natAdd (k + 1) 0) (prodKind_right _))

/-- **A round of the construction**: the rows of the recursive relation
of phase `p₀` (the tag of `Z`) each read `Z`, and the rows read are
re-tagged `p₁`. The product is written as an apply whose right side
reads no column of the left – which is what a product is, and keeps the
construction over the classes of a basis holding the apply and not
`×`. -/
def phaseBody (s : String) (p₁ : T) (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) :
    AggQueryIn T c (k + 1) (ColKind.allReg (k + 1)) [(s, k + 1)] :=
  (AggQueryIn.Proj (roundCols p₁)
    (AggQueryIn.Sel sameTag (AggQueryIn.Apply (AggQueryIn.Hole (k + 1) s)
      (Z.substMap (applyOuter T c (k + 1)))))).castKind
    (roundCols_kind p₁)

/-- The selection dropping the rows of phase `p₀`. -/
def notTag (p₀ : T) : GenPredIn T c (ColKind.allReg (k + 1)) :=
  GenPredIn.not (GenPredIn.cmp CompOp.syneq (TermGIn.index 0 rfl) (TermGIn.const p₀))

/-- The columns past the tag. -/
def unwithTagCols : Tuple (ProjColIn T c (ColKind.allReg (k + 1))) k :=
  fun i => ProjColIn.term (TermGIn.index (Fin.succ i) rfl)

/-- **`⊎` from two bag recursions** (see the module heading): `s₁` binds
the recursion listing `q₁`'s rows behind the driver, `s₂` the one adding
`q₂`'s rows to it. The phases are `0` and `ValueType.nonzero`. -/
def sumByMu (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c k (ColKind.allReg k) :=
  (AggQueryIn.Proj unwithTagCols
    (AggQueryIn.Sel (notTag 0)
      (AggQueryIn.Mu s₂
        (AggQueryIn.Mu s₁ (driver 0) (phaseBody s₁ ValueType.nonzero (withTag 0 q₁)))
        (phaseBody s₂ ValueType.nonzero (withTag 0 q₂))))).castKind (funext fun _ => rfl)

end AggQueryIn

/-! ## What the construction computes -/

namespace AggQueryIn

variable {c k : ℕ}

theorem holdsPlain_sameTag (u : Tuple T ((k + 1) + (k + 1))) (γ : Fin c → T) :
    (sameTag (c := c) (k := k)).holdsPlain u γ
      ↔ u (Fin.castAdd (k + 1) 0) = u (Fin.natAdd (k + 1) 0) := by
  show CompOp.eval3 CompOp.syneq (u (Fin.castAdd (k + 1) 0)) (u (Fin.natAdd (k + 1) 0))
    = Kleene.true ↔ _
  simp [CompOp.eval3, CompOp.strict, CompOp.eval]

theorem holdsPlain_notTag (p₀ : T) (u : Tuple T (k + 1)) (γ : Fin c → T) :
    (notTag (c := c) (k := k) p₀).holdsPlain u γ ↔ u 0 ≠ p₀ := by
  show (CompOp.eval3 CompOp.syneq (u 0) p₀).not = Kleene.true ↔ _
  rw [Kleene.not_eq_true_iff]
  by_cases h : u 0 = p₀ <;> simp [CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool, h]

omit [ValueType T] in
/-- Binding a guarded family is binding over the rows kept. -/
theorem Multiset.bind_ite {α β : Type} (p : α → Prop) [DecidablePred p]
    (s : Multiset α) (f : α → Multiset β) :
    (s.bind fun x => if p x then f x else 0) = (s.filter p).bind f := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.filter_cons]
    by_cases h : p a
    · rw [ite_eq_left h, ite_eq_left h, Multiset.singleton_add, Multiset.cons_bind, ih]
    · rw [ite_eq_right h, ite_eq_right h, zero_add, zero_add, ih]

/-- **A round**: every row of phase `p₀` of the recursive relation reads
`Z`'s rows, re-tagged `p₁`. -/
theorem evaluatePlain_phaseBody (s : String) (p₀ p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.noMention s)
    (D : Database T) (γ : Fin c → T) (R : Multiset (Tuple T k))
    (hZv : Z.evaluatePlain D γ = R.map (tagRow p₀))
    (X : Multiset (Tuple T (k + 1))) :
    (phaseBody s p₁ Z).evaluatePlain (D.assign s X) γ
      = (X.filter (fun x => x 0 = p₀)).bind
          (fun _ => R.map (tagRow p₁)) := by
  rw [phaseBody, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u j => (roundCols p₁ j).evalPlain u γ)
    (Multiset.filter (fun u => sameTag.holdsPlain u γ)
      ((AggQueryIn.Apply (AggQueryIn.Hole (k + 1) s)
        (Z.substMap (fun j : Fin c => Sum.inr (Fin.natAdd (k + 1) j)))).evaluatePlain
          (D.assign s X) γ)) = _
  rw [AggQueryIn.apply_plainEquiv_prod (AggQueryIn.Hole (k + 1) s) Z (D.assign s X) γ]
  simp only [AggQueryIn.evaluatePlain]
  rw [AggQueryIn.evaluatePlain_assign_of_noMention X Z hZ D γ, hZv]
  simp only [Database.find_assign, Relation.hMul_eq_bind, Multiset.filter_bind,
    Multiset.map_bind]
  rw [← Multiset.bind_ite (fun x : Tuple T (k + 1) => x 0 = p₀)]
  refine congrArg (Multiset.bind X) (funext fun x => ?_)
  show Multiset.map (roundProj p₁ γ) (Multiset.filter (fun u => sameTag.holdsPlain u γ)
    (Multiset.map (fun v => Fin.append x v) (Multiset.map (tagRow p₀) R))) = _
  simp only [Multiset.filter_map, Multiset.map_map, Function.comp_def]
  have hcond : ∀ z : Tuple T (k + 1),
      sameTag.holdsPlain (Fin.append x z : Tuple T ((k + 1) + (k + 1))) γ ↔ x 0 = z 0 := by
    intro z
    rw [holdsPlain_sameTag, Fin.append_left, Fin.append_right]
  by_cases hx : x 0 = p₀
  · rw [ite_eq_left hx]
    have hf : Multiset.filter (fun r : Tuple T k =>
        sameTag.holdsPlain (Fin.append x (tagRow p₀ r)) γ) R = R :=
      Multiset.filter_eq_self.mpr fun r _ => (hcond _).mpr (by rw [tagRow_zero]; exact hx)
    show Multiset.map _ (Multiset.filter _ R) = _
    simp only [hf]
    refine congrArg (fun f => Multiset.map f R) (funext fun r => funext fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · show (Fin.append x (tagRow p₀ r) : Tuple T _) (Fin.natAdd (k + 1) (Fin.succ i)) = r i
      rw [Fin.append_right, tagRow_succ]
  · rw [ite_eq_right hx]
    have hf : Multiset.filter (fun r : Tuple T k =>
        sameTag.holdsPlain (Fin.append x (tagRow p₀ r)) γ) R = 0 :=
      Multiset.filter_eq_nil.mpr fun r _ h => hx (by
        have := (hcond _).mp h
        rwa [tagRow_zero] at this)
    show Multiset.map _ (Multiset.filter _ R) = _
    simp only [hf, Multiset.map_zero]

omit [ValueType T] in
/-- The rows a round emits all carry the phase `p₁`. -/
theorem mem_round_phase {p₁ : T} {R : Multiset (Tuple T k)} {X : Multiset (Tuple T (k + 1))}
    {p : Tuple T (k + 1) → Prop} [DecidablePred p] {x : Tuple T (k + 1)}
    (hx : x ∈ (X.filter p).bind
      (fun _ => R.map (tagRow p₁))) : x 0 = p₁ := by
  obtain ⟨_, -, hx⟩ := Multiset.mem_bind.mp hx
  obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hx
  rfl

/-- **A phase recursion runs two rounds**: its value is its base plus one
round read from the base's rows of phase `p₀`. -/
theorem evaluatePlain_phaseMu (s : String) {p₀ p₁ : T} (hp : p₁ ≠ p₀)
    (base Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.noMention s)
    (D : Database T) (γ : Fin c → T) (R : Multiset (Tuple T k))
    (hZv : Z.evaluatePlain D γ = R.map (tagRow p₀)) :
    (AggQueryIn.Mu s base (phaseBody s p₁ Z)).evaluatePlain D γ
      = (show Multiset (Tuple T (k + 1)) from base.evaluatePlain D γ)
        + ((show Multiset (Tuple T (k + 1)) from base.evaluatePlain D γ).filter
            (fun x => x 0 = p₀)).bind
          (fun _ => R.map (tagRow p₁)) := by
  simp only [AggQueryIn.evaluatePlain]
  have hstep : ∀ X : Multiset (Tuple T (k + 1)),
      (phaseBody s p₁ Z).evaluatePlain (D.assign s X) γ
        = (X.filter (fun x => x 0 = p₀)).bind
            (fun _ => R.map (tagRow p₁)) :=
    fun X => evaluatePlain_phaseBody s p₀ p₁ Z hZ D γ R hZv X
  have h0 : (phaseBody s p₁ Z).evaluatePlain
      (D.assign s (0 : Multiset (Tuple T (k + 1)))) γ = 0 := by
    rw [hstep, Multiset.filter_zero, Multiset.zero_bind]
  have h2 : (fun X : Multiset (Tuple T (k + 1)) =>
      (phaseBody s p₁ Z).evaluatePlain (D.assign s X) γ)^[1 + 1] (base.evaluatePlain D γ) = 0 := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
    show (phaseBody s p₁ Z).evaluatePlain (D.assign s
      ((phaseBody s p₁ Z).evaluatePlain (D.assign s (base.evaluatePlain D γ)) γ)) γ = 0
    rw [hstep, hstep]
    rw [Multiset.filter_eq_nil.mpr (fun x hx h => hp (Eq.trans (mem_round_phase hx).symm h)),
      Multiset.zero_bind]
  rw [muSumFix_eq_of_empty h0 h2]
  simp only [muSum]
  rw [hstep]

/-- **The construction settles**, on every instance where its two
operands do. -/
theorem settlesAt_phaseMu (s : String) {p₀ p₁ : T} (hp : p₁ ≠ p₀)
    (base Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.noMention s)
    (D : Database T) (γ : Fin c → T) (R : Multiset (Tuple T k))
    (hZv : Z.evaluatePlain D γ = R.map (tagRow p₀))
    (hb : base.SettlesAt D γ) (hZs : Z.SettlesAt D γ) :
    (AggQueryIn.Mu s base (phaseBody s p₁ Z)).SettlesAt D γ := by
  have hstep : ∀ X : Multiset (Tuple T (k + 1)),
      (phaseBody s p₁ Z).evaluatePlain (D.assign s X) γ
        = (X.filter (fun x => x 0 = p₀)).bind
            (fun _ => R.map (tagRow p₁)) :=
    fun X => evaluatePlain_phaseBody s p₀ p₁ Z hZ D γ R hZv X
  refine ⟨hb, ?_, ⟨1, ?_⟩, fun j => ?_⟩
  · rw [hstep, Multiset.filter_zero, Multiset.zero_bind]
  · rw [Function.iterate_succ_apply', Function.iterate_one]
    show (phaseBody s p₁ Z).evaluatePlain (D.assign s
      ((phaseBody s p₁ Z).evaluatePlain (D.assign s (base.evaluatePlain D γ)) γ)) γ = 0
    rw [hstep, hstep]
    rw [Multiset.filter_eq_nil.mpr (fun x hx h => hp (Eq.trans (mem_round_phase hx).symm h)),
      Multiset.zero_bind]
  · rw [phaseBody, AggQueryIn.settlesAt_castKind]
    refine (⟨trivial, fun u _ => ?_⟩ : True ∧ _)
    rw [AggQueryIn.settlesAt_substMap, substVal_applyOuter]
    exact AggQueryIn.settlesAt_of_noMention Z hZ
      (fun _k s' hs' => (Database.find_assign_of_ne s s' _ D
        (fun hc => hs'.elim (fun h => h hc.2) (fun h => by simp at h))).symm) γ hZs

/-- The driver names no relation. -/
theorem noMention_driver (p₀ : T) (s : String) : (driver (c := c) (k := k) p₀).noMention s := by
  rw [driver, AggQueryIn.noMention_castKind]
  show (unitC : AggQueryIn T c 0 _).noMention s
  rw [unitC, AggQueryIn.noMention_castKind]
  trivial

omit [ValueType T] in
theorem noMention_withTag (t : T) (q : AggQueryIn T c k (ColKind.allReg k)) (s : String) :
    (withTag t q).noMention s ↔ q.noMention s := by
  rw [withTag, AggQueryIn.noMention_castKind]
  exact Iff.rfl

omit [ValueType T] in
theorem noMention_phaseBody (s' : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) {s : String}
    (hZ : Z.noMention s) : (phaseBody s' p₁ Z).noMention s := by
  rw [phaseBody, AggQueryIn.noMention_castKind]
  exact ⟨trivial, (AggQueryIn.noMention_substMap Z _).mpr hZ⟩

/-- **The construction is the union**: its value is `q₁ ⊎ q₂` on every
instance and context, the two bound names being fresh. -/
theorem evaluatePlain_sumByMu (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂₂ : q₂.noMention s₂) (D : Database T) (γ : Fin c → T) :
    (sumByMu s₁ s₂ q₁ q₂).evaluatePlain D γ
      = q₁.evaluatePlain D γ + q₂.evaluatePlain D γ := by
  set d : Tuple T (k + 1) := tagRow 0 (fun _ => 0) with hd
  have hd0 : d 0 = 0 := rfl
  have hinner : (AggQueryIn.Mu s₁ (driver 0)
      (phaseBody s₁ ValueType.nonzero (withTag 0 q₁))).evaluatePlain D γ
      = ({d} : Multiset (Tuple T (k + 1)))
        + (show Multiset (Tuple T k) from q₁.evaluatePlain D γ).map
            (tagRow ValueType.nonzero) := by
    rw [evaluatePlain_phaseMu s₁ ValueType.nonzero_ne_zero (driver 0) _
      ((noMention_withTag 0 q₁ s₁).mpr h₁) D γ _ (evaluatePlain_withTag 0 q₁ D γ),
      evaluatePlain_driver]
    show ({d} : Multiset (Tuple T (k + 1))) + (Multiset.filter _ {d}).bind _ = _
    rw [Multiset.filter_singleton, ite_eq_left hd0, Multiset.singleton_bind]
  have houter : (AggQueryIn.Mu s₂
      (AggQueryIn.Mu s₁ (driver 0) (phaseBody s₁ ValueType.nonzero (withTag 0 q₁)))
      (phaseBody s₂ ValueType.nonzero (withTag 0 q₂))).evaluatePlain D γ
      = ({d} : Multiset (Tuple T (k + 1)))
        + (show Multiset (Tuple T k) from q₁.evaluatePlain D γ).map
            (tagRow ValueType.nonzero)
        + (show Multiset (Tuple T k) from q₂.evaluatePlain D γ).map
            (tagRow ValueType.nonzero) := by
    rw [evaluatePlain_phaseMu s₂ ValueType.nonzero_ne_zero _ _
      ((noMention_withTag 0 q₂ s₂).mpr h₂₂) D γ _ (evaluatePlain_withTag 0 q₂ D γ), hinner]
    have hfilter : Multiset.filter (fun x : Tuple T (k + 1) => x 0 = 0)
        (({d} : Multiset (Tuple T (k + 1)))
          + (show Multiset (Tuple T k) from q₁.evaluatePlain D γ).map
              (tagRow ValueType.nonzero))
        = {d} := by
      rw [Multiset.filter_add, Multiset.filter_singleton, ite_eq_left hd0,
        Multiset.filter_eq_nil.mpr (fun x hx h => ?_), add_zero]
      obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hx
      exact ValueType.nonzero_ne_zero (T := T) h
    rw [hfilter, Multiset.singleton_bind]
  rw [sumByMu, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u j => (unwithTagCols j).evalPlain u γ)
    (Multiset.filter (fun u => (notTag 0).holdsPlain u γ)
      ((AggQueryIn.Mu s₂
        (AggQueryIn.Mu s₁ (driver 0) (phaseBody s₁ ValueType.nonzero (withTag 0 q₁)))
        (phaseBody s₂ ValueType.nonzero (withTag 0 q₂))).evaluatePlain D γ)) = _
  simp only [houter]
  have hkeep : ∀ (M : Multiset (Tuple T k)),
      Multiset.filter (fun u : Tuple T (k + 1) => (notTag 0).holdsPlain u γ)
        (M.map (tagRow ValueType.nonzero))
        = M.map (tagRow ValueType.nonzero) := by
    intro M
    refine Multiset.filter_eq_self.mpr fun u hu => ?_
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hu
    rw [holdsPlain_notTag, tagRow_zero]
    exact ValueType.nonzero_ne_zero
  have hdrop : Multiset.filter (fun u : Tuple T (k + 1) => (notTag 0).holdsPlain u γ)
      ({d} : Multiset (Tuple T (k + 1))) = 0 := by
    have hnot : ¬ (notTag 0).holdsPlain d γ := by
      rw [holdsPlain_notTag, hd0]
      exact fun h => h rfl
    rw [Multiset.filter_singleton, ite_eq_right hnot, Multiset.empty_eq_zero]
  simp only [Multiset.filter_add, hdrop, zero_add, hkeep, Multiset.map_add, Multiset.map_map]
  have huntag : ((fun u : Tuple T (k + 1) => fun j : Fin k => (unwithTagCols j).evalPlain u γ)
      ∘ (tagRow ValueType.nonzero)) = id := by
    funext r
    funext i
    show (Fin.cons ValueType.nonzero r : Tuple T (k + 1)) (Fin.succ i) = r i
    exact Fin.cons_succ _ _ _
  simp only [huntag, Multiset.map_id]

/-- **The construction settles wherever its operands do.** -/
theorem settlesAt_sumByMu (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂₂ : q₂.noMention s₂)
    (D : Database T) (γ : Fin c → T) (hs₁ : q₁.SettlesAt D γ) (hs₂ : q₂.SettlesAt D γ) :
    (sumByMu s₁ s₂ q₁ q₂).SettlesAt D γ := by
  rw [sumByMu, AggQueryIn.settlesAt_castKind]
  show (AggQueryIn.Mu s₂ _ _).SettlesAt D γ
  refine settlesAt_phaseMu s₂ ValueType.nonzero_ne_zero _ _
    ((noMention_withTag 0 q₂ s₂).mpr h₂₂) D γ _ (evaluatePlain_withTag 0 q₂ D γ) ?_ ?_
  · refine settlesAt_phaseMu s₁ ValueType.nonzero_ne_zero _ _
      ((noMention_withTag 0 q₁ s₁).mpr h₁) D γ _ (evaluatePlain_withTag 0 q₁ D γ) ?_ ?_
    · rw [driver, AggQueryIn.settlesAt_castKind]
      show (unitC : AggQueryIn T c 0 _).SettlesAt D γ
      rw [unitC, AggQueryIn.settlesAt_castKind]
      trivial
    · rw [withTag, AggQueryIn.settlesAt_castKind]; exact hs₁
  · rw [withTag, AggQueryIn.settlesAt_castKind]; exact hs₂


/-! ## What the construction is made of -/

/-- **The classes the construction uses**: the empty relation and a
scalar aggregation (the unit), projections, selections, applies and bag
recursions. -/
def sumMuOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.sel, OpKind.apply, OpKind.gamma, OpKind.muBag}

omit [ValueType T] in
theorem usesOnly_unitC {S : Set OpKind} (hS : sumMuOps ⊆ S) :
    (unitC : AggQueryIn T c 0 _).usesOnly S := by
  rw [unitC, AggQueryIn.usesOnly_castKind]
  exact ⟨hS (by simp [sumMuOps]), hS (by simp [sumMuOps])⟩

omit [ValueType T] in
theorem usesOnly_withTag {S : Set OpKind} (hS : sumMuOps ⊆ S) (t : T)
    (q : AggQueryIn T c k (ColKind.allReg k)) (hq : q.usesOnly S) :
    (withTag t q).usesOnly S := by
  rw [withTag, AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hS (by simp [sumMuOps]), fun j => ?_⟩, hq⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem usesOnly_driver {S : Set OpKind} (hS : sumMuOps ⊆ S) (p₀ : T) :
    (driver (c := c) (k := k) p₀).usesOnly S := by
  rw [driver, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumMuOps]), fun _ => rfl⟩, usesOnly_unitC hS⟩

omit [ValueType T] in
theorem usesOnly_phaseBody {S : Set OpKind} (hS : sumMuOps ⊆ S) (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.usesOnly S) :
    (phaseBody s p₁ Z).usesOnly S := by
  rw [phaseBody, AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hS (by simp [sumMuOps]), fun j => ?_⟩, hS (by simp [sumMuOps]),
    hS (by simp [sumMuOps]), trivial, (AggQueryIn.usesOnly_substMap Z _).mpr hZ⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- **The construction uses the classes of `sumMuOps`** and its operands'. -/
theorem usesOnly_sumByMu {S : Set OpKind} (hS : sumMuOps ⊆ S) (s₁ s₂ : String)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) (h₁ : q₁.usesOnly S) (h₂ : q₂.usesOnly S) :
    (sumByMu s₁ s₂ q₁ q₂).usesOnly S := by
  rw [sumByMu, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumMuOps]), fun _ => rfl⟩, hS (by simp [sumMuOps]),
    hS (by simp [sumMuOps]),
    ⟨hS (by simp [sumMuOps]), usesOnly_driver hS 0,
      usesOnly_phaseBody hS _ _ _ (usesOnly_withTag hS 0 q₁ h₁)⟩,
    usesOnly_phaseBody hS _ _ _ (usesOnly_withTag hS 0 q₂ h₂)⟩

theorem hygienic_driver (p₀ : T) : (driver (c := c) (k := k) p₀).hygienic := by
  rw [driver, AggQueryIn.hygienic_castKind]
  show (unitC : AggQueryIn T c 0 _).hygienic
  rw [unitC, AggQueryIn.hygienic_castKind]
  trivial

omit [ValueType T] in
theorem hygienic_withTag (t : T) (q : AggQueryIn T c k (ColKind.allReg k)) :
    (withTag t q).hygienic ↔ q.hygienic := by
  rw [withTag, AggQueryIn.hygienic_castKind]
  exact Iff.rfl

omit [ValueType T] in
theorem hygienic_phaseBody (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) :
    (phaseBody s p₁ Z).hygienic ↔ Z.hygienic := by
  rw [phaseBody, AggQueryIn.hygienic_castKind]
  exact ⟨fun h => (AggQueryIn.hygienic_substMap Z _).mp h.2,
    fun h => ⟨trivial, (AggQueryIn.hygienic_substMap Z _).mpr h⟩⟩

/-- **The construction's recursions are hygienic**, given fresh names:
neither operand mentions the name bound over it. -/
theorem hygienic_sumByMu (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂₁ : q₁.noMention s₂) (h₂₂ : q₂.noMention s₂)
    (hr₁ : q₁.hygienic) (hr₂ : q₂.hygienic) :
    (sumByMu s₁ s₂ q₁ q₂).hygienic := by
  rw [sumByMu, AggQueryIn.hygienic_castKind]
  exact ⟨⟨noMention_driver 0 s₂,
      noMention_phaseBody s₁ _ _ ((noMention_withTag 0 q₁ s₂).mpr h₂₁)⟩,
    noMention_phaseBody s₂ _ _ ((noMention_withTag 0 q₂ s₂).mpr h₂₂),
    ⟨noMention_driver 0 s₁, noMention_phaseBody s₁ _ _ ((noMention_withTag 0 q₁ s₁).mpr h₁),
      hygienic_driver 0, (hygienic_phaseBody _ _ _).mpr
        ((hygienic_withTag 0 q₁).mpr hr₁)⟩,
    (hygienic_phaseBody _ _ _).mpr ((hygienic_withTag 0 q₂).mpr hr₂)⟩

theorem inSig_unitC (Θ : Set (SeqAggFunc T)) : (unitC : AggQueryIn T c 0 _).inSig Θ := by
  rw [unitC, AggQueryIn.inSig_castKind]
  exact ⟨fun j => j.elim0, fun j => j.elim0, trivial⟩

theorem inSig_driver (Θ : Set (SeqAggFunc T)) (p₀ : T) :
    (driver (c := c) (k := k) p₀).inSig Θ := by
  rw [driver, AggQueryIn.inSig_castKind]
  exact ⟨fun _ => rfl, inSig_unitC Θ⟩

theorem inSig_withTag (Θ : Set (SeqAggFunc T)) (t : T) (q : AggQueryIn T c k (ColKind.allReg k))
    (hq : q.inSig Θ) : (withTag t q).inSig Θ := by
  rw [withTag, AggQueryIn.inSig_castKind]
  refine ⟨fun j => ?_, hq⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem inSig_phaseBody (Θ : Set (SeqAggFunc T)) (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.inSig Θ) :
    (phaseBody s p₁ Z).inSig Θ := by
  rw [phaseBody, AggQueryIn.inSig_castKind]
  refine ⟨fun j => ?_, rfl, trivial, (AggQueryIn.inSig_substMap Z _).mpr hZ⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- **The construction applies no function and adds no aggregate**: it
is in every signature its operands are in. -/
theorem inSig_sumByMu (Θ : Set (SeqAggFunc T)) (s₁ s₂ : String)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) (h₁ : q₁.inSig Θ) (h₂ : q₂.inSig Θ) :
    (sumByMu s₁ s₂ q₁ q₂).inSig Θ := by
  rw [sumByMu, AggQueryIn.inSig_castKind]
  exact ⟨fun _ => rfl, rfl, ⟨inSig_driver Θ 0, inSig_phaseBody Θ _ _ _ (inSig_withTag Θ 0 q₁ h₁)⟩,
    inSig_phaseBody Θ _ _ _ (inSig_withTag Θ 0 q₂ h₂)⟩

theorem winsDerivable_driver (p₀ : T) : (driver (c := c) (k := k) p₀).WinsDerivable := by
  rw [driver, AggQueryIn.winsDerivable_castKind]
  show (unitC : AggQueryIn T c 0 _).WinsDerivable
  rw [unitC, AggQueryIn.winsDerivable_castKind]
  trivial

theorem winsDerivable_withTag (t : T) (q : AggQueryIn T c k (ColKind.allReg k)) :
    (withTag t q).WinsDerivable ↔ q.WinsDerivable := by
  rw [withTag, AggQueryIn.winsDerivable_castKind]
  exact Iff.rfl

theorem winsDerivable_phaseBody (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) :
    (phaseBody s p₁ Z).WinsDerivable ↔ Z.WinsDerivable := by
  rw [phaseBody, AggQueryIn.winsDerivable_castKind]
  exact ⟨fun h => (AggQueryIn.winsDerivable_substMap Z _).mp h.2,
    fun h => ⟨trivial, (AggQueryIn.winsDerivable_substMap Z _).mpr h⟩⟩

/-- The construction has no window of its own. -/
theorem winsDerivable_sumByMu (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.WinsDerivable) (h₂ : q₂.WinsDerivable) :
    (sumByMu s₁ s₂ q₁ q₂).WinsDerivable := by
  rw [sumByMu, AggQueryIn.winsDerivable_castKind]
  exact ⟨⟨winsDerivable_driver 0, (winsDerivable_phaseBody _ _ _).mpr
      ((winsDerivable_withTag 0 q₁).mpr h₁)⟩,
    (winsDerivable_phaseBody _ _ _).mpr ((winsDerivable_withTag 0 q₂).mpr h₂)⟩

omit [ValueType T] in
theorem overSchema_unitC (sch : Schema) : (unitC : AggQueryIn T c 0 _).overSchema sch := by
  rw [unitC, AggQueryIn.overSchema_castKind]
  trivial

theorem overSchema_driver (sch : Schema) (p₀ : T) :
    (driver (c := c) (k := k) p₀).overSchema sch := by
  rw [driver, AggQueryIn.overSchema_castKind]
  exact overSchema_unitC sch

omit [ValueType T] in
theorem overSchema_withTag (sch : Schema) (t : T) (q : AggQueryIn T c k (ColKind.allReg k)) :
    (withTag t q).overSchema sch ↔ q.overSchema sch := by
  rw [withTag, AggQueryIn.overSchema_castKind]
  exact Iff.rfl

omit [ValueType T] in
theorem overSchema_phaseBody {sch : Schema} {s : String} (hs : sch s = some (k + 1)) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.overSchema sch) :
    (phaseBody s p₁ Z).overSchema sch := by
  rw [phaseBody, AggQueryIn.overSchema_castKind]
  exact ⟨hs, (AggQueryIn.overSchema_substMap Z _ sch).mpr hZ⟩

omit [ValueType T] in
/-- A declaration reads back. -/
theorem Schema.update_self (sch : Schema) (s : String) (m : ℕ) :
    (sch.update s m) s = some m := by
  show (if s = s then some m else sch s) = some m
  rw [ite_eq_left rfl]

/-- **The construction is well-formed over a schema declaring neither
bound name**, its operands being so and naming neither. -/
theorem overSchema_sumByMu (sch : Schema) (s₁ s₂ : String)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (hs₁ : sch s₁ = none) (hs₂ : sch s₂ = none) (hn₁ : s₁ ∉ q₁.names) (hn₂ : s₂ ∉ q₂.names)
    (h₁ : q₁.overSchema sch) (h₂ : q₂.overSchema sch) :
    (sumByMu s₁ s₂ q₁ q₂).overSchema sch := by
  rw [sumByMu, AggQueryIn.overSchema_castKind]
  exact ⟨hs₂, ⟨hs₁, overSchema_driver sch 0,
      noMention_phaseBody s₁ _ _ ((noMention_withTag 0 q₁ s₁).mpr
        (AggQueryIn.noMention_of_not_mem_names q₁ hn₁)),
      overSchema_phaseBody (Schema.update_self sch s₁ (k + 1)) _ _
        ((overSchema_withTag _ 0 q₁).mpr
          (AggQueryIn.overSchema_update_of_not_mem_names q₁ h₁ hn₁))⟩,
    noMention_phaseBody s₂ _ _ ((noMention_withTag 0 q₂ s₂).mpr
      (AggQueryIn.noMention_of_not_mem_names q₂ hn₂)),
    overSchema_phaseBody (Schema.update_self sch s₂ (k + 1)) _ _
      ((overSchema_withTag _ 0 q₂).mpr
        (AggQueryIn.overSchema_update_of_not_mem_names q₂ h₂ hn₂))⟩

/-- **The construction names its two bound names and its operands'.** -/
theorem names_sumByMu (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    (sumByMu s₁ s₂ q₁ q₂).names ⊆ insert s₁ (insert s₂ (Union.union q₁.names q₂.names)) := by
  intro x hx
  rw [sumByMu, AggQueryIn.names_castKind] at hx
  simp only [AggQueryIn.names, phaseBody, withTag, driver, unitC, AggQueryIn.names_castKind,
    AggQueryIn.names_substMap,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    false_or] at hx
  simp only [Finset.mem_insert, Finset.mem_union]
  tauto

/-- The construction names nothing its operands do not, its two bound
names aside. -/
theorem noMention_sumByMu (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    {s : String} (h₁ : q₁.noMention s) (h₂ : q₂.noMention s) :
    (sumByMu s₁ s₂ q₁ q₂).noMention s := by
  rw [sumByMu, AggQueryIn.noMention_castKind]
  exact ⟨⟨noMention_driver 0 s, noMention_phaseBody s₁ _ _
      ((noMention_withTag 0 q₁ s).mpr h₁)⟩,
    noMention_phaseBody s₂ _ _ ((noMention_withTag 0 q₂ s).mpr h₂)⟩

end AggQueryIn

/-! ## The pass: every `⊎` replaced by the construction

A `⊎` *inside a recursive body* cannot be replaced by the construction
as it stands: the restriction on recursive terms, which the syntax carries,
lets the recursive relation be read under a projection, a selection, a
product, the left side of an apply or a union, and under no recursion.
What a body `q₁` with a `⊎` on its recursive path is, though, is a
sum `q₁' + qC` of the body with the non-recursive side of every such
`⊎` dropped and a closed query `qC` (`exists_sumFree_aux`'s second
half): the operators the recursive relation may sit under all
distribute over `⊎`. At a bag recursion that settles, `qC` is empty –
its rows would be in every round – so `q₁'` is the body; at a set
recursion, `qC` moves into the base, which is where the construction
then replaces the `⊎`. -/

namespace AggQueryIn

variable {c : ℕ}

/-- The empty relation of arity `n`, all regular. -/
def emptyRel (n : ℕ) : AggQueryIn T c n (ColKind.allReg n) :=
  (AggQueryIn.Proj (fun _ : Fin n => ProjColIn.term (TermGIn.const 0))
    (AggQueryIn.Empty : AggQueryIn T c 0 (ColKind.allReg 0))).castKind (funext fun _ => rfl)

theorem evaluatePlain_emptyRel (n : ℕ) (D : Database T) (γ : Fin c → T) :
    (emptyRel (T := T) (c := c) n).evaluatePlain D γ = 0 := by
  rw [emptyRel, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  exact Multiset.map_zero _

theorem settlesAt_emptyRel (n : ℕ) (D : Database T) (γ : Fin c → T) :
    (emptyRel (T := T) (c := c) n).SettlesAt D γ := by
  rw [emptyRel, AggQueryIn.settlesAt_castKind]
  trivial

theorem usesOnly_emptyRel {S : Set OpKind} (hS : sumMuOps ⊆ S) (n : ℕ) :
    (emptyRel (T := T) (c := c) n).usesOnly S := by
  rw [emptyRel, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumMuOps]), fun _ => rfl⟩, hS (by simp [sumMuOps])⟩

theorem hygienic_emptyRel (n : ℕ) : (emptyRel (T := T) (c := c) n).hygienic := by
  rw [emptyRel, AggQueryIn.hygienic_castKind]
  trivial

theorem inSig_emptyRel (Θ : Set (SeqAggFunc T)) (n : ℕ) :
    (emptyRel (T := T) (c := c) n).inSig Θ := by
  rw [emptyRel, AggQueryIn.inSig_castKind]
  exact ⟨fun _ => rfl, trivial⟩

theorem winsDerivable_emptyRel (n : ℕ) : (emptyRel (T := T) (c := c) n).WinsDerivable := by
  rw [emptyRel, AggQueryIn.winsDerivable_castKind]
  trivial

theorem overSchema_emptyRel (sch : Schema) (n : ℕ) :
    (emptyRel (T := T) (c := c) n).overSchema sch := by
  rw [emptyRel, AggQueryIn.overSchema_castKind]
  trivial

theorem names_emptyRel (n : ℕ) : (emptyRel (T := T) (c := c) n).names = ∅ := by
  rw [emptyRel, AggQueryIn.names_castKind]
  rfl

theorem noMention_emptyRel (n : ℕ) (s : String) : (emptyRel (T := T) (c := c) n).noMention s := by
  rw [emptyRel, AggQueryIn.noMention_castKind]
  trivial

/-- **An empty relation of any kinds**: a selection that keeps nothing,
over the one constant row of a parameter leaf. A hole of aggregate kinds
needs it, `emptyRel` having regular columns only. -/
def emptyOf {n : ℕ} (κ : Fin n → ColKind) : AggQueryIn T c n κ :=
  AggQueryIn.Sel (GenPredIn.cmp CompOp.syneq (.const 0) (.const ValueType.nonzero))
    (AggQueryIn.Param (fun _ => _root_.Sum.inl 0) κ)

theorem evaluatePlain_emptyOf {n : ℕ} (κ : Fin n → ColKind) (D : Database T) (γ : Fin c → T) :
    (emptyOf (c := c) κ).evaluatePlain D γ = 0 := by
  simp only [emptyOf, AggQueryIn.evaluatePlain]
  refine Multiset.filter_eq_nil.mpr (fun u _ => ?_)
  show ¬ (CompOp.syneq.eval3 (0 : T) ValueType.nonzero = Kleene.true)
  rw [CompOp.syneq_eval3_eq_true_iff]
  exact fun h => ValueType.nonzero_ne_zero h.symm

theorem settlesAt_emptyOf {n : ℕ} (κ : Fin n → ColKind) (D : Database T) (γ : Fin c → T) :
    (emptyOf (c := c) κ).SettlesAt D γ := trivial

theorem usesOnly_emptyOf {S : Set OpKind} (hS : sumMuOps ⊆ S) {n : ℕ} (κ : Fin n → ColKind) :
    (emptyOf (T := T) (c := c) κ).usesOnly S :=
  ⟨hS (by simp [sumMuOps]), hS (by simp [sumMuOps]), hS (by simp [sumMuOps]),
    hS (by simp [sumMuOps])⟩

theorem hygienic_emptyOf {n : ℕ} (κ : Fin n → ColKind) :
    (emptyOf (T := T) (c := c) κ).hygienic := trivial

theorem inSig_emptyOf (Θ : Set (SeqAggFunc T)) {n : ℕ} (κ : Fin n → ColKind) :
    (emptyOf (T := T) (c := c) κ).inSig Θ := ⟨rfl, trivial⟩

theorem winsDerivable_emptyOf {n : ℕ} (κ : Fin n → ColKind) :
    (emptyOf (T := T) (c := c) κ).WinsDerivable := trivial

theorem overSchema_emptyOf (sch : Schema) {n : ℕ} (κ : Fin n → ColKind) :
    (emptyOf (T := T) (c := c) κ).overSchema sch := trivial

theorem names_emptyOf {n : ℕ} (κ : Fin n → ColKind) :
    (emptyOf (T := T) (c := c) κ).names = ∅ := rfl

theorem noMention_emptyOf {n : ℕ} (κ : Fin n → ColKind) (s : String) :
    (emptyOf (T := T) (c := c) κ).noMention s := trivial

end AggQueryIn

/-! ### The two recursions, given a split body -/

/-- Two steps whose iterates agree sum alike. -/
theorem muSum_congr_of_iterate {α : Type} {step step' : Multiset α → Multiset α} :
    ∀ (b : ℕ) {M M' : Multiset α}, (∀ i, i ≤ b → step^[i] M = step'^[i] M') →
      muSum step b M = muSum step' b M'
  | 0, M, M', h => h 0 (le_refl 0)
  | b + 1, M, M', h => by
    have hM : M = M' := h 0 (Nat.zero_le _)
    rw [muSum, muSum, hM]
    refine congrArg _ (muSum_congr_of_iterate b fun i hi => ?_)
    have := h (i + 1) (Nat.succ_le_succ hi)
    rwa [Function.iterate_succ_apply, Function.iterate_succ_apply, hM] at this

/-- Two steps whose rounds agree settle at the same value. -/
theorem muFix_congr_of_iterate {α : Type} {step step' : Multiset α → Multiset α}
    (hs : MuSetSettles step) (h : ∀ k, muIter step k = muIter step' k) :
    muFix step = muFix step' := by
  obtain ⟨j, hj⟩ := hs
  have hfix : step (muIter step j) = muIter step j := by
    rw [muIter_eq_iterate]
    exact (Function.iterate_succ_apply' step j 0).symm.trans hj
  have hfix' : step' (muIter step' j) = muIter step' j := by
    have : muIter step' (j + 1) = muIter step' j := by
      rw [← h, ← h, muIter, hfix]
    exact this
  rw [muFix_eq_of_fix hfix, muFix_eq_of_fix hfix', h]

/-- One summand of an empty sum is empty. -/
theorem Multiset.eq_zero_of_add_eq_zero_left {α : Type} {a b : Multiset α} (h : a + b = 0) :
    a = 0 :=
  Multiset.le_zero.mp (by rw [← h]; exact Multiset.le_add_right _ _)

theorem Multiset.eq_zero_of_add_eq_zero_right {α : Type} {a b : Multiset α} (h : a + b = 0) :
    b = 0 :=
  Multiset.le_zero.mp (by rw [← h]; exact Multiset.le_add_left _ _)

/-- **A bag recursion whose body splits** as `q₁' + qC`, `qC` not reading
the recursive name: where it settles, `qC` is empty – it would be in
every round – so `q₁'` is the body at every round, and the recursion
over `q₁'` and a base agreeing with its own is the same recursion. -/
theorem AggQueryIn.mu_of_split {c n : ℕ} {κ κ' : Fin n → ColKind} (s : String)
    (q₀ : AggQueryIn T c n κ) (q₀' : AggQueryIn T c n κ')
    (q₁ : AggQueryIn T c n κ [(s, n)]) (q₁' : AggQueryIn T c n κ' [(s, n)])
    (qC : AggQueryIn T c n κ') (hC : qC.noMention s)
    (D : Database T) (γ : Fin c → T) (hset : (AggQueryIn.Mu s q₀ q₁).SettlesAt D γ)
    (h₀ : q₀'.SettlesAt D γ ∧ q₀.evaluatePlain D γ = q₀'.evaluatePlain D γ)
    (h₁ : ∀ D' : Database T, q₁.SettlesAt D' γ → q₁'.SettlesAt D' γ ∧ qC.SettlesAt D' γ
      ∧ (q₁.evaluatePlain D' γ : Multiset (Tuple T n))
          = q₁'.evaluatePlain D' γ + qC.evaluatePlain D' γ) :
    (AggQueryIn.Mu s q₀' q₁').SettlesAt D γ
      ∧ (AggQueryIn.Mu s q₀ q₁).evaluatePlain D γ
          = (AggQueryIn.Mu s q₀' q₁').evaluatePlain D γ := by
  obtain ⟨hs₀, h0, ⟨m, hm⟩, hk⟩ := hset
  have hsub : ∀ {X Y : Relation T n}, X = Y →
      q₁.SettlesAt (D.assign s X) γ → q₁.SettlesAt (D.assign s Y) γ :=
    fun h hx => h ▸ hx
  have hkm : q₁.SettlesAt (D.assign s (0 : Relation T n)) γ := hsub hm (hk (m + 1))
  have hsplit0 := (h₁ _ hkm).2.2
  rw [h0] at hsplit0
  have hz₁ : (q₁'.evaluatePlain (D.assign s (0 : Relation T n)) γ : Multiset (Tuple T n)) = 0 :=
    Multiset.eq_zero_of_add_eq_zero_left hsplit0.symm
  have hzC : (qC.evaluatePlain (D.assign s (0 : Relation T n)) γ : Multiset (Tuple T n)) = 0 :=
    Multiset.eq_zero_of_add_eq_zero_right hsplit0.symm
  have hCX : ∀ X : Relation T n,
      (qC.evaluatePlain (D.assign s X) γ : Multiset (Tuple T n)) = 0 := fun X => by
    rw [AggQueryIn.evaluatePlain_assign_of_noMention X qC hC,
      ← AggQueryIn.evaluatePlain_assign_of_noMention (0 : Relation T n) qC hC]
    exact hzC
  have hbody : ∀ X : Relation T n, q₁.SettlesAt (D.assign s X) γ →
      q₁.evaluatePlain (D.assign s X) γ = q₁'.evaluatePlain (D.assign s X) γ := fun X h => by
    rw [(h₁ _ h).2.2, hCX]
    exact add_zero (M := Multiset (Tuple T n)) _
  have hround : ∀ j,
      (fun X : Multiset (Tuple T n) => q₁'.evaluatePlain (D.assign s X) γ)^[j]
          (q₀'.evaluatePlain D γ)
        = (fun X : Multiset (Tuple T n) => q₁.evaluatePlain (D.assign s X) γ)^[j]
          (q₀.evaluatePlain D γ) := by
    intro j
    induction j with
    | zero => exact h₀.2.symm
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact (hbody _ (hk j)).symm
  have hsub' : ∀ {X Y : Relation T n}, X = Y →
      q₁'.SettlesAt (D.assign s X) γ → q₁'.SettlesAt (D.assign s Y) γ :=
    fun h hx => h ▸ hx
  refine ⟨⟨h₀.1, hz₁, ⟨m, (hround (m + 1)).trans hm⟩,
    fun j => hsub' (hround j).symm (h₁ _ (hk j)).1⟩, ?_⟩
  simp only [AggQueryIn.evaluatePlain]
  rw [muSumFix_eq_of_empty h0 hm, muSumFix_eq_of_empty hz₁ ((hround (m + 1)).trans hm)]
  exact muSum_congr_of_iterate m fun i _ => (hround i).symm

/-- **A set recursion whose body splits** as `q₁' + qC`: the sum `qC`
moves into the base – a round is the duplicate elimination of
`q₀ ⊎ q₁' ⊎ qC` either way – so the recursion over a base computing
`q₀ ⊎ qC` and the body `q₁'` is the same recursion. -/
theorem AggQueryIn.muSet_of_split {c n : ℕ} (s : String)
    (q₀ q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁ q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (qC base' : AggQueryIn T c n (ColKind.allReg n)) (hC : qC.noMention s)
    (D : Database T) (γ : Fin c → T) (hset : (AggQueryIn.MuSet s q₀ q₁).SettlesAt D γ)
    (h₀ : ∀ D' : Database T, q₀.SettlesAt D' γ →
      q₀'.SettlesAt D' γ ∧ q₀.evaluatePlain D' γ = q₀'.evaluatePlain D' γ)
    (h₁ : ∀ D' : Database T, q₁.SettlesAt D' γ → q₁'.SettlesAt D' γ ∧ qC.SettlesAt D' γ
      ∧ (q₁.evaluatePlain D' γ : Multiset (Tuple T n))
          = q₁'.evaluatePlain D' γ + qC.evaluatePlain D' γ)
    (hbase : ∀ D' : Database T, q₀'.SettlesAt D' γ → qC.SettlesAt D' γ →
      base'.SettlesAt D' γ
        ∧ (base'.evaluatePlain D' γ : Multiset (Tuple T n))
            = q₀'.evaluatePlain D' γ + qC.evaluatePlain D' γ) :
    (AggQueryIn.MuSet s base' q₁').SettlesAt D γ
      ∧ (AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ
          = (AggQueryIn.MuSet s base' q₁').evaluatePlain D γ := by
  obtain ⟨hs₀, hs, hk⟩ := hset
  have hCD : qC.SettlesAt D γ :=
    AggQueryIn.settlesAt_assign_of_noMention _ qC hC D γ (h₁ _ (hk 0)).2.1
  have hb := hbase D (h₀ D hs₀).1 hCD
  have hround : ∀ j,
      muIter (fun X : Multiset (Tuple T n) => (q₀.evaluatePlain D γ
        + q₁.evaluatePlain (D.assign s X) γ).dedup) j
      = muIter (fun X : Multiset (Tuple T n) => (base'.evaluatePlain D γ
        + q₁'.evaluatePlain (D.assign s X) γ).dedup) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [muIter, muIter, ← ih]
      have e₁ := (h₁ _ (hk j)).2.2
      show Multiset.dedup (_ + _) = Multiset.dedup (_ + _)
      rw [e₁, (h₀ D hs₀).2, hb.2, AggQueryIn.evaluatePlain_assign_of_noMention _ qC hC D γ]
      have hac : ∀ a b c : Multiset (Tuple T n), a + (b + c) = (a + c) + b :=
        fun a b c => by ac_rfl
      exact congrArg Multiset.dedup (hac _ _ _)
  refine ⟨⟨hb.1, ?_, fun j => ?_⟩, ?_⟩
  · obtain ⟨j, hj⟩ := hs
    refine ⟨j, ?_⟩
    rw [← muIter_eq_iterate, ← muIter_eq_iterate, ← hround, ← hround, muIter_eq_iterate,
      muIter_eq_iterate]
    exact hj
  · rw [← hround]
    exact (h₁ _ (hk j)).1
  · simp only [AggQueryIn.evaluatePlain]
    exact muFix_congr_of_iterate hs hround

/-! ### The fence, and what the pass carries -/

/-- **Every `⊎` has all-regular operands.** A recursion is all-regular
(`AggQueryIn.Mu` is), so this is what the construction needs of a `⊎`
it replaces; it is what the re-typing produces, every operator of its
output being over all-regular children. -/
def AggQueryIn.sumsAllReg : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List
    (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.sumsAllReg
  | _, _, _, _, .Sel _ q _ => q.sumsAllReg
  | _, _, _, _, .Prod q₁ q₂ => q₁.sumsAllReg ∧ q₂.sumsAllReg
  | _, _, _, _, .Apply q₁ q₂ => q₁.sumsAllReg ∧ q₂.sumsAllReg
  | _, n, κ, _, .Sum q₁ q₂ => κ = ColKind.allReg n ∧ q₁.sumsAllReg ∧ q₂.sumsAllReg
  | _, _, _, _, .Dedup q => q.sumsAllReg
  | _, _, _, _, .Diff q₁ q₂ => q₁.sumsAllReg ∧ q₂.sumsAllReg
  | _, _, _, _, .Explode _ _ q => q.sumsAllReg
  | _, _, _, _, .Retag _ q => q.sumsAllReg
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.sumsAllReg ∧ q₁.sumsAllReg
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.sumsAllReg ∧ q₁.sumsAllReg
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.sumsAllReg
  | _, _, _, _, .GammaScalar _ _ q _ => q.sumsAllReg
  | _, _, _, _, .GammaNest _ _ _ _ q => q.sumsAllReg
  | _, _, _, _, .ProvSum _ _ _ q => q.sumsAllReg
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.sumsAllReg
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.sumsAllReg
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.sumsAllReg

omit [ValueType T] in
@[simp] theorem AggQueryIn.sumsAllReg_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List
    (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c n κ l) : (q.castKind h).sumsAllReg ↔ q.sumsAllReg := by
  cases h; exact Iff.rfl

omit [ValueType T] in
/-- A substitution changes no `⊎`. -/
theorem AggQueryIn.sumsAllReg_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).sumsAllReg ↔ q.sumsAllReg := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ => Iff.rfl
  | Hole n s => exact fun θ => Iff.rfl
  | Param pv ρ => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.sumsAllReg_castKind]
    exact ih θ
  | Sel φ q _ ih => exact fun θ => ih θ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ _)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr Iff.rfl (and_congr (ih₁ θ) (ih₂ θ))
  | Dedup q ih => exact fun θ => ih θ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Explode k hk q ih => exact fun θ => ih θ
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | Gamma is ts fs q keep ord ih => exact fun θ => ih θ
  | GammaScalar ts fs q ord ih => exact fun θ => ih θ
  | GammaNest is his p fn q ih => exact fun θ => ih θ
  | ProvSum is his t q ih => exact fun θ => ih θ
  | GammaTok is his ts fs a q keep ih => exact fun θ => ih θ
  | Win P O o w t fw q hrr dist keep ih => exact fun θ => ih θ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => ih θ

/-- **What the pass keeps of a query, besides its value**: the classes
of `S` (the construction's being among them), the restriction on
recursive terms, the signature, derivable windows, well-formedness over
a schema declaring none of the fresh names, the names (its own, or
fresh ones), and the names it does not mention (fresh ones aside). -/
structure AggQueryIn.SumFreeOf (S : Set OpKind) (Θ : Set (SeqAggFunc T)) (f : ℕ → String)
    {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (q' : AggQueryIn T c n κ l') : Prop where
  usesOnly : q'.usesOnly S
  hygienic : q'.hygienic
  inSig : q'.inSig Θ
  wins : q.WinsDerivable → q'.WinsDerivable
  over : ∀ sch : Schema, (∀ i, sch (f i) = none) → q.overSchema sch → q'.overSchema sch
  names : ∀ x, x ∈ q'.names → x ∈ q.names ∨ ∃ i, x = f i
  nom : ∀ s, (∀ i, s ≠ f i) → q.noMention s → q'.noMention s

omit [ValueType T] in
/-- Reading a schema with a name it does not mention declared is reading
the schema – for a query whose holes do not carry that name. -/
theorem AggQueryIn.overSchema_of_update_of_noMention {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {sch : Schema}, (∀ k, (s, k) ∉ l) →
      q.noMention s → q.overSchema (sch.update s m) → q.overSchema sch := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro sch _ h ho
    have : (if s' = s then some m else sch s') = some n := ho
    rwa [ite_eq_right h] at this
  | Hole n s' =>
    intro sch hl _ ho
    have hne : s' ≠ s := fun h => hl n (by rw [h]; exact List.mem_singleton_self _)
    have : (if s' = s then some m else sch s') = some n := ho
    rwa [ite_eq_right hne] at this
  | Param pv ρ => exact fun _ _ _ => trivial
  | Empty => exact fun _ _ _ => trivial
  | Proj ps q ih => exact fun hl h ho => ih hl h ho
  | Sel φ q _ ih => exact fun hl h ho => ih hl h ho
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun hl h ho => ⟨ih₁ (fun k hk => hl k (List.mem_append.mpr (Or.inl hk))) h.1 ho.1,
      ih₂ (fun k hk => hl k (List.mem_append.mpr (Or.inr hk))) h.2 ho.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun hl h ho => ⟨ih₁ hl h.1 ho.1, ih₂ (fun _ hk => by simp at hk) h.2 ho.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun hl h ho => ⟨ih₁ (fun k hk => hl k (List.mem_append.mpr (Or.inl hk))) h.1 ho.1,
      ih₂ (fun k hk => hl k (List.mem_append.mpr (Or.inr hk))) h.2 ho.2⟩
  | Dedup q ih => exact fun hl h ho => ih hl h ho
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hl h ho => ⟨ih₁ hl h.1 ho.1, ih₂ hl h.2 ho.2⟩
  | Explode k hk q ih => exact fun hl h ho => ih hl h ho
  | Retag hk q ih => exact fun hl h ho => ih hl h ho
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    intro sch _ h ho
    have hne : s' ≠ s := fun hs => by
      have : (if s' = s then some m else sch s') = none := ho.1
      rw [ite_eq_left hs] at this
      exact Option.some_ne_none m this
    refine ⟨?_, ih₀ (fun _ hk => by simp at hk) h.1 ho.2.1, ho.2.2.1,
      ih₁ (fun k hk => hne (Prod.mk.inj (List.mem_singleton.mp hk)).1.symm) h.2
        (by rw [Schema.update_comm sch hne]; exact ho.2.2.2)⟩
    have : (if s' = s then some m else sch s') = none := ho.1
    rwa [ite_eq_right hne] at this
  | MuSet s' q₀ q₁ ih₀ ih₁ =>
    intro sch _ h ho
    have hne : s' ≠ s := fun hs => by
      have : (if s' = s then some m else sch s') = none := ho.1
      rw [ite_eq_left hs] at this
      exact Option.some_ne_none m this
    refine ⟨?_, ih₀ (fun _ hk => by simp at hk) h.1 ho.2.1, ho.2.2.1,
      ih₁ (fun k hk => hne (Prod.mk.inj (List.mem_singleton.mp hk)).1.symm) h.2
        (by rw [Schema.update_comm sch hne]; exact ho.2.2.2)⟩
    have : (if s' = s then some m else sch s') = none := ho.1
    rwa [ite_eq_right hne] at this
  | Gamma is ts fs q keep ord ih => exact fun hl h ho => ih hl h ho
  | GammaScalar ts fs q ord ih => exact fun hl h ho => ih hl h ho
  | GammaNest is his p fn q ih => exact fun hl h ho => ih hl h ho
  | ProvSum is his t q ih => exact fun hl h ho => ih hl h ho
  | GammaTok is his ts fs a q keep ih => exact fun hl h ho => ih hl h ho
  | Win P O o w t fw q hrr dist keep ih => exact fun hl h ho => ih hl h ho
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hl h ho => ih hl h ho

namespace AggQueryIn

omit [ValueType T] in
private theorem memS {S : Set OpKind} {o : OpKind} (ho : o ≠ OpKind.union)
    (h : o ∈ insert OpKind.union S) : o ∈ S :=
  (Set.mem_insert_iff.mp h).resolve_left ho

/-- The supply past its first two names. -/
private def shift2 (f : ℕ → String) : ℕ → String := fun i => f (i + 2)

private theorem shift2_injective {f : ℕ → String} (hf : Function.Injective f) :
    Function.Injective (shift2 f) :=
  fun _ _ h => Nat.add_right_cancel (hf h)

omit [ValueType T] in
/-- A name of the supply the children did not get is not among a child's
output names. -/
private theorem not_mem_of_shift {f : ℕ → String} (hf : Function.Injective f)
    {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (hn : ∀ x, x ∈ q'.names → x ∈ q.names ∨ ∃ i, x = shift2 f i) {j : ℕ} (hj : j < 2)
    (hfr : f j ∉ q.names) : f j ∉ q'.names := fun h => by
  rcases hn _ h with h' | ⟨i, hi⟩
  · exact hfr h'
  · have := hf hi
    omega

omit [ValueType T] in
private theorem names_shift {f : ℕ → String} {x : String} {A B : Finset String}
    (h : x ∈ A ∨ ∃ i, x = shift2 f i) (hAB : A ⊆ B) : x ∈ B ∨ ∃ i, x = f i :=
  h.imp (fun h => hAB h) (fun ⟨i, hi⟩ => ⟨i + 2, hi⟩)

omit [ValueType T] in
/-- The names clause through a binary operator. -/
private theorem names_union {f : ℕ → String} {A₁ A₂ B₁ B₂ : Finset String}
    (h₁ : ∀ x, x ∈ A₁ → x ∈ B₁ ∨ ∃ i, x = f i) (h₂ : ∀ x, x ∈ A₂ → x ∈ B₂ ∨ ∃ i, x = f i) :
    ∀ x, x ∈ Union.union A₁ A₂ → x ∈ Union.union B₁ B₂ ∨ ∃ i, x = f i :=
  fun x hx => (Finset.mem_union.mp hx).elim
    (fun h => (h₁ x h).imp_left (Finset.mem_union_left _))
    (fun h => (h₂ x h).imp_left (Finset.mem_union_right _))

omit [ValueType T] in
private theorem fresh_shift {f : ℕ → String} {A B : Finset String} (hfr : ∀ i, f i ∉ B)
    (hAB : A ⊆ B) : ∀ i, shift2 f i ∉ A :=
  fun i h => hfr (i + 2) (hAB h)

omit [ValueType T] in
private theorem fresh_sub {f : ℕ → String} {A B : Finset String} (hfr : ∀ i, f i ∉ B)
    (hAB : A ⊆ B) : ∀ i, f i ∉ A :=
  fun i h => hfr i (hAB h)

omit [ValueType T] in
private theorem f01_ne {f : ℕ → String} (hf : Function.Injective f) : f 0 ≠ f 1 :=
  fun h => Nat.zero_ne_one (hf h)

omit [ValueType T] in
private theorem ne_shift_of_mem {f : ℕ → String} {s : String} {B : Finset String}
    (hfr : ∀ i, f i ∉ B) (hs : s ∈ B) : ∀ i, s ≠ shift2 f i :=
  fun i h => hfr (i + 2) (show shift2 f i ∈ B from h ▸ hs)

omit [ValueType T] in
private theorem ne_of_mem {f : ℕ → String} {s : String} {B : Finset String}
    (hfr : ∀ i, f i ∉ B) (hs : s ∈ B) : ∀ i, s ≠ f i :=
  fun i h => hfr i (h ▸ hs)

/-- **The pass**, both halves at once. For every query of the fragment
(the classes of `S` and `⊎`, restricted recursions, the signature `Θ`,
every `⊎` all-regular) and every injective supply of names the query
does not use: a query with no `⊎`, keeping what `SumFreeOf` lists and
defined and equal wherever the query is; and, for a body reading the
name `s` once, a body still reading it once and a closed query the body
is the sum of. -/
theorem exists_sumFree_aux {S : Set OpKind} (hS : sumMuOps ⊆ S) {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly (insert OpKind.union S) → q.hygienic → q.inSig Θ → q.sumsAllReg →
      ∀ (f : ℕ → String), Function.Injective f → (∀ i, f i ∉ q.names) →
        (l = [] → ∃ q' : AggQueryIn T c n κ, SumFreeOf S Θ f q q' ∧
            ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
              q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ)
        ∧ (∀ (s : String) (m : ℕ), l = [(s, m)] → q.noMention s →
            ∃ (q' : AggQueryIn T c n κ l) (qC : AggQueryIn T c n κ), qC.noMention s
              ∧ SumFreeOf S Θ f q q' ∧ SumFreeOf S Θ f q qC
              ∧ ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
                q'.SettlesAt D γ ∧ qC.SettlesAt D γ
                  ∧ (q.evaluatePlain D γ : Multiset (Tuple T n))
                      = q'.evaluatePlain D γ + qC.evaluatePlain D γ) := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro hq hr hi hsa f hf hfr
    exact ⟨fun _ => ⟨AggQueryIn.Rel n s', ⟨trivial, trivial, trivial, id, fun _ _ h => h,
      fun x hx => Or.inl hx, fun _ _ h => h⟩, fun D γ _ => ⟨trivial, rfl⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Hole n s' κh =>
    intro hq hr hi hsa f hf hfr
    refine ⟨fun hl => absurd hl (by simp), fun s m hl _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
    refine ⟨AggQueryIn.Hole n _ κh, emptyOf κh, noMention_emptyOf κh _,
      ⟨trivial, trivial, trivial, id, fun _ _ h => h, fun x hx => Or.inl hx, fun _ _ h => h⟩,
      ⟨usesOnly_emptyOf hS κh, hygienic_emptyOf κh, inSig_emptyOf Θ κh,
        fun _ => winsDerivable_emptyOf κh, fun sch _ _ => overSchema_emptyOf sch κh,
        fun x hx => by rw [names_emptyOf] at hx; exact absurd hx (Finset.notMem_empty x),
        fun s' _ _ => noMention_emptyOf κh s'⟩,
      fun D γ _ => ⟨trivial, settlesAt_emptyOf κh D γ, ?_⟩⟩
    rw [evaluatePlain_emptyOf]
    exact (add_zero (M := Multiset (Tuple T n)) _).symm
  | Param pv ρ =>
    intro hq hr hi hsa f hf hfr
    exact ⟨fun _ => ⟨AggQueryIn.Param pv ρ, ⟨⟨memS nofun hq.1, memS nofun hq.2.1,
      memS nofun hq.2.2⟩, trivial, trivial, id, fun _ _ h => h,
      fun x hx => Or.inl hx, fun _ _ h => h⟩, fun D γ _ => ⟨trivial, rfl⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Empty =>
    intro hq hr hi hsa f hf hfr
    exact ⟨fun _ => ⟨AggQueryIn.Empty, ⟨memS nofun hq, trivial, trivial, id, fun _ _ h => h,
      fun x hx => Or.inl hx, fun _ _ h => h⟩, fun D γ _ => ⟨trivial, rfl⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Proj ps q ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, hb⟩ := ih hq.2 hr hi.2 hsa f hf hfr
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      refine ⟨AggQueryIn.Proj ps q', ⟨⟨⟨memS nofun hq.1.1, hq.1.2⟩, hs.usesOnly⟩,
        hs.hygienic, ⟨hi.1, hs.inSig⟩, hs.wins, hs.over, hs.names, hs.nom⟩,
        fun D γ hset => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ hset
      exact ⟨hs', by simp only [AggQueryIn.evaluatePlain, he']⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      refine ⟨AggQueryIn.Proj ps q', AggQueryIn.Proj ps qC, hCn,
        ⟨⟨⟨memS nofun hq.1.1, hq.1.2⟩, hs.usesOnly⟩, hs.hygienic, ⟨hi.1, hs.inSig⟩,
          hs.wins, hs.over, hs.names, hs.nom⟩,
        ⟨⟨⟨memS nofun hq.1.1, hq.1.2⟩, hsC.usesOnly⟩, hsC.hygienic, ⟨hi.1, hsC.inSig⟩,
          hsC.wins, hsC.over, hsC.names, hsC.nom⟩, fun D γ hset => ?_⟩
      obtain ⟨hs', hsC', he'⟩ := he D γ hset
      refine ⟨hs', hsC', ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [he', Multiset.map_add]
  | Sel φ q hφ ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, hb⟩ := ih hq.2 hr hi.2 hsa f hf hfr
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      subst hl
      refine ⟨AggQueryIn.Sel φ q' hφ, ⟨⟨memS nofun hq.1, hs.usesOnly⟩, hs.hygienic,
        ⟨hi.1, hs.inSig⟩, hs.wins, hs.over, hs.names, hs.nom⟩, fun D γ hset => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ hset
      exact ⟨hs', by simp only [AggQueryIn.evaluatePlain, he']⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      refine ⟨AggQueryIn.Sel φ q' hφ, AggQueryIn.Sel φ qC trivial, hCn,
        ⟨⟨memS nofun hq.1, hs.usesOnly⟩, hs.hygienic, ⟨hi.1, hs.inSig⟩,
          hs.wins, hs.over, hs.names, hs.nom⟩,
        ⟨⟨memS nofun hq.1, hsC.usesOnly⟩, hsC.hygienic, ⟨hi.1, hsC.inSig⟩,
          hsC.wins, hsC.over, hsC.names, hsC.nom⟩, fun D γ hset => ?_⟩
      obtain ⟨hs', hsC', he'⟩ := he D γ hset
      refine ⟨hs', hsC', ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [he', Multiset.filter_add]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hsa f hf hfr
    have hfr₁ := fresh_sub hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_sub hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, hb₁⟩ := ih₁ hq.2.1 hr.1 hi.1 hsa.1 f hf hfr₁
    obtain ⟨hc₂, hb₂⟩ := ih₂ hq.2.2 hr.2 hi.2 hsa.2 f hf hfr₂
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
      obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
      refine ⟨AggQueryIn.Prod q₁' q₂', ⟨⟨memS nofun hq.1, hs₁.usesOnly, hs₂.usesOnly⟩,
        ⟨hs₁.hygienic, hs₂.hygienic⟩, ⟨hs₁.inSig, hs₂.inSig⟩,
        fun hw => ⟨hs₁.wins hw.1, hs₂.wins hw.2⟩,
        fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
        names_union hs₁.names hs₂.names,
        fun s hs hn => ⟨hs₁.nom s hs hn.1, hs₂.nom s hs hn.2⟩⟩, fun D γ hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
      obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
      exact ⟨⟨hs₁', hs₂'⟩, by simp only [AggQueryIn.evaluatePlain, he₁', he₂']⟩
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
        obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hb₁ s m rfl h₁
        refine ⟨AggQueryIn.Prod p₁ q₂', AggQueryIn.Prod pC q₂',
          ⟨hCn, hs₂.nom s ?_ h₂⟩,
          ⟨⟨memS nofun hq.1, hp.usesOnly, hs₂.usesOnly⟩,
            ⟨hp.hygienic, hs₂.hygienic⟩, ⟨hp.inSig, hs₂.inSig⟩,
            fun hw => ⟨hp.wins hw.1, hs₂.wins hw.2⟩,
            fun sch hsch ho => ⟨hp.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
            names_union hp.names hs₂.names,
            fun s hs hn => ⟨hp.nom s hs hn.1, hs₂.nom s hs hn.2⟩⟩,
          ⟨⟨memS nofun hq.1, hpC.usesOnly, hs₂.usesOnly⟩,
            ⟨hpC.hygienic, hs₂.hygienic⟩, ⟨hpC.inSig, hs₂.inSig⟩,
            fun hw => ⟨hpC.wins hw.1, hs₂.wins hw.2⟩,
            fun sch hsch ho => ⟨hpC.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
            names_union hpC.names hs₂.names,
            fun s hs hn => ⟨hpC.nom s hs hn.1, hs₂.nom s hs hn.2⟩⟩, fun D γ hset => ?_⟩
        · exact ne_of_mem hfr (Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁
            (List.mem_singleton_self _)))
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.1
        obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
        refine ⟨⟨hp', hs₂'⟩, ⟨hpC', hs₂'⟩, ?_⟩
        simp only [AggQueryIn.evaluatePlain]
        rw [he', he₂', Relation.hMul_eq_bind, Relation.hMul_eq_bind, Relation.hMul_eq_bind,
          Multiset.add_bind]
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
        obtain ⟨p₂, pC, hCn, hp, hpC, he⟩ := hb₂ s m rfl h₂
        refine ⟨AggQueryIn.Prod q₁' p₂, AggQueryIn.Prod q₁' pC,
          ⟨hs₁.nom s ?_ h₁, hCn⟩,
          ⟨⟨memS nofun hq.1, hs₁.usesOnly, hp.usesOnly⟩,
            ⟨hs₁.hygienic, hp.hygienic⟩, ⟨hs₁.inSig, hp.inSig⟩,
            fun hw => ⟨hs₁.wins hw.1, hp.wins hw.2⟩,
            fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hp.over sch hsch ho.2⟩,
            names_union hs₁.names hp.names,
            fun s hs hn => ⟨hs₁.nom s hs hn.1, hp.nom s hs hn.2⟩⟩,
          ⟨⟨memS nofun hq.1, hs₁.usesOnly, hpC.usesOnly⟩,
            ⟨hs₁.hygienic, hpC.hygienic⟩, ⟨hs₁.inSig, hpC.inSig⟩,
            fun hw => ⟨hs₁.wins hw.1, hpC.wins hw.2⟩,
            fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hpC.over sch hsch ho.2⟩,
            names_union hs₁.names hpC.names,
            fun s hs hn => ⟨hs₁.nom s hs hn.1, hpC.nom s hs hn.2⟩⟩, fun D γ hset => ?_⟩
        · exact ne_of_mem hfr (Finset.mem_union_right _ (AggQueryIn.mem_names_of_index q₂
            (List.mem_singleton_self _)))
        obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.2
        refine ⟨⟨hs₁', hp'⟩, ⟨hs₁', hpC'⟩, ?_⟩
        simp only [AggQueryIn.evaluatePlain]
        rw [he₁', he', Relation.hMul_eq_bind, Relation.hMul_eq_bind, Relation.hMul_eq_bind,
          ← Multiset.bind_add]
        refine Multiset.bind_congr fun a _ => ?_
        exact Multiset.map_add _ _ _
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hsa f hf hfr
    have hfr₁ := fresh_sub hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_sub hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, hb₁⟩ := ih₁ hq.2.1 hr.1 hi.1 hsa.1 f hf hfr₁
    obtain ⟨hc₂, -⟩ := ih₂ hq.2.2 hr.2 hi.2 hsa.2 f hf hfr₂
    obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
    have hmem : ∀ (D : Database T) (γ : Fin _ → T) (l' : List (String × ℕ))
        {κ' : Fin _ → ColKind} (p : AggQueryIn T _ _ κ' l'),
        q₁.evaluatePlain D γ = p.evaluatePlain D γ →
        ∀ u, Multiset.Mem (p.evaluatePlain D γ) u →
          Multiset.Mem (q₁.evaluatePlain D γ) u :=
      fun D γ _ _ p he u hu => by rw [he]; exact hu
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q₁', hs₁, he₁⟩ := hc₁ hl
      refine ⟨AggQueryIn.Apply q₁' q₂', ⟨⟨memS nofun hq.1, hs₁.usesOnly, hs₂.usesOnly⟩,
        ⟨hs₁.hygienic, hs₂.hygienic⟩, ⟨hs₁.inSig, hs₂.inSig⟩,
        fun hw => ⟨hs₁.wins hw.1, hs₂.wins hw.2⟩,
        fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
        names_union hs₁.names hs₂.names,
        fun s hs hn => ⟨hs₁.nom s hs hn.1, hs₂.nom s hs hn.2⟩⟩, fun D γ hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
      refine ⟨⟨hs₁', fun u hu => (he₂ D _ (hset.2 u (hmem D γ _ q₁' he₁' u hu))).1⟩, ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [he₁']
      exact Multiset.bind_congr fun u hu =>
        congrArg _ (he₂ D _ (hset.2 u (hmem D γ _ q₁' he₁' u hu))).2
    · obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hb₁ s m hl hnm.1
      have hs2 : ∀ i, s ≠ f i :=
        ne_of_mem hfr (Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁
          (hl ▸ List.mem_singleton_self _)))
      refine ⟨AggQueryIn.Apply p₁ q₂', AggQueryIn.Apply pC q₂',
        ⟨hCn, hs₂.nom s hs2 hnm.2⟩,
        ⟨⟨memS nofun hq.1, hp.usesOnly, hs₂.usesOnly⟩,
          ⟨hp.hygienic, hs₂.hygienic⟩, ⟨hp.inSig, hs₂.inSig⟩,
          fun hw => ⟨hp.wins hw.1, hs₂.wins hw.2⟩,
          fun sch hsch ho => ⟨hp.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
          names_union hp.names hs₂.names,
          fun s hs hn => ⟨hp.nom s hs hn.1, hs₂.nom s hs hn.2⟩⟩,
        ⟨⟨memS nofun hq.1, hpC.usesOnly, hs₂.usesOnly⟩,
          ⟨hpC.hygienic, hs₂.hygienic⟩, ⟨hpC.inSig, hs₂.inSig⟩,
          fun hw => ⟨hpC.wins hw.1, hs₂.wins hw.2⟩,
          fun sch hsch ho => ⟨hpC.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
          names_union hpC.names hs₂.names,
          fun s hs hn => ⟨hpC.nom s hs hn.1, hs₂.nom s hs hn.2⟩⟩, fun D γ hset => ?_⟩
      obtain ⟨hp', hpC', he'⟩ := he D γ hset.1
      have hmem' : ∀ u, Multiset.Mem (p₁.evaluatePlain D γ) u
          ∨ Multiset.Mem (pC.evaluatePlain D γ) u →
          Multiset.Mem (q₁.evaluatePlain D γ) u :=
        fun u hu => by rw [he']; exact Multiset.mem_add.mpr hu
      refine ⟨⟨hp', fun u hu => (he₂ D _ (hset.2 u (hmem' u (Or.inl hu)))).1⟩,
        ⟨hpC', fun u hu => (he₂ D _ (hset.2 u (hmem' u (Or.inr hu)))).1⟩, ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [he', Multiset.add_bind]
      refine congrArg₂ (· + ·) ?_ ?_
      · exact Multiset.bind_congr fun u hu =>
          congrArg _ (he₂ D _ (hset.2 u (hmem' u (Or.inl hu)))).2
      · exact Multiset.bind_congr fun u hu =>
          congrArg _ (he₂ D _ (hset.2 u (hmem' u (Or.inr hu)))).2
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hκ, hsa₁, hsa₂⟩ := hsa
    subst hκ
    have hfr₁ := fresh_shift hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_shift hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, hb₁⟩ :=
      ih₁ hq.2.1 hr.1 hi.1 hsa₁ (shift2 f) (shift2_injective hf) hfr₁
    obtain ⟨hc₂, hb₂⟩ :=
      ih₂ hq.2.2 hr.2 hi.2 hsa₂ (shift2 f) (shift2_injective hf) hfr₂
    have hf0 : f 0 ∉ (AggQueryIn.Sum q₁ q₂).names := hfr 0
    have hf1 : f 1 ∉ (AggQueryIn.Sum q₁ q₂).names := hfr 1
    have hf0₁ : f 0 ∉ q₁.names := fun h => hf0 (Finset.mem_union_left _ h)
    have hf1₁ : f 1 ∉ q₁.names := fun h => hf1 (Finset.mem_union_left _ h)
    have hf0₂ : f 0 ∉ q₂.names := fun h => hf0 (Finset.mem_union_right _ h)
    have hf1₂ : f 1 ∉ q₂.names := fun h => hf1 (Finset.mem_union_right _ h)
    -- the bundle for a construction over two children's outputs
    have hbundle : ∀ {p₁ p₂ : AggQueryIn T _ _ _},
        SumFreeOf S Θ (shift2 f) q₁ p₁ → SumFreeOf S Θ (shift2 f) q₂ p₂ →
        SumFreeOf S Θ f (AggQueryIn.Sum q₁ q₂) (sumByMu (f 0) (f 1) p₁ p₂) := by
      intro p₁ p₂ hp₁ hp₂
      have hn₁₀ : f 0 ∉ p₁.names := not_mem_of_shift hf hp₁.names (by omega) hf0₁
      have hn₁₁ : f 1 ∉ p₁.names := not_mem_of_shift hf hp₁.names (by omega) hf1₁
      have hn₂₁ : f 1 ∉ p₂.names := not_mem_of_shift hf hp₂.names (by omega) hf1₂
      exact {
        usesOnly := usesOnly_sumByMu hS _ _ _ _ hp₁.usesOnly hp₂.usesOnly
        hygienic := hygienic_sumByMu _ _ _ _
          (AggQueryIn.noMention_of_not_mem_names _ hn₁₀)
          (AggQueryIn.noMention_of_not_mem_names _ hn₁₁)
          (AggQueryIn.noMention_of_not_mem_names _ hn₂₁)
          hp₁.hygienic hp₂.hygienic
        inSig := inSig_sumByMu Θ _ _ _ _ hp₁.inSig hp₂.inSig
        wins := fun hw => winsDerivable_sumByMu _ _ _ _ (hp₁.wins hw.1) (hp₂.wins hw.2)
        over := fun sch hsch ho => overSchema_sumByMu sch _ _ _ _ (hsch 0) (hsch 1) hn₁₀ hn₂₁
          (hp₁.over sch (fun i => hsch (i + 2)) ho.1) (hp₂.over sch (fun i => hsch (i + 2)) ho.2)
        names := fun x hx => by
          rcases Finset.mem_insert.mp (names_sumByMu _ _ _ _ hx) with rfl | hx'
          · exact Or.inr ⟨0, rfl⟩
          rcases Finset.mem_insert.mp hx' with rfl | hx''
          · exact Or.inr ⟨1, rfl⟩
          exact (Finset.mem_union.mp hx'').elim
            (fun h => names_shift (hp₁.names x h) Finset.subset_union_left)
            (fun h => names_shift (hp₂.names x h) Finset.subset_union_right)
        nom := fun s hs hn => noMention_sumByMu _ _ _ _
          (hp₁.nom s (fun i => hs (i + 2)) hn.1) (hp₂.nom s (fun i => hs (i + 2)) hn.2) }
    -- the construction's value and definedness over two children's outputs
    have hval : ∀ {p₁ p₂ : AggQueryIn T _ _ _},
        SumFreeOf S Θ (shift2 f) q₁ p₁ → SumFreeOf S Θ (shift2 f) q₂ p₂ →
        ∀ (D : Database T) (γ : Fin _ → T), p₁.SettlesAt D γ → p₂.SettlesAt D γ →
          (sumByMu (f 0) (f 1) p₁ p₂).SettlesAt D γ
            ∧ ((sumByMu (f 0) (f 1) p₁ p₂).evaluatePlain D γ : Multiset (Tuple T _))
                = p₁.evaluatePlain D γ + p₂.evaluatePlain D γ := by
      intro p₁ p₂ hp₁ hp₂ D γ h₁ h₂
      have hn₁₀ : f 0 ∉ p₁.names := not_mem_of_shift hf hp₁.names (by omega) hf0₁
      have hn₂₁ : f 1 ∉ p₂.names := not_mem_of_shift hf hp₂.names (by omega) hf1₂
      exact ⟨settlesAt_sumByMu _ _ _ _ (AggQueryIn.noMention_of_not_mem_names _ hn₁₀)
          (AggQueryIn.noMention_of_not_mem_names _ hn₂₁) D γ h₁ h₂,
        evaluatePlain_sumByMu _ _ _ _ (AggQueryIn.noMention_of_not_mem_names _ hn₁₀)
          (AggQueryIn.noMention_of_not_mem_names _ hn₂₁) D γ⟩
    -- a child's output, as the output for the sum
    have hleft : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ _ l'},
        SumFreeOf S Θ (shift2 f) q₁ p →
        SumFreeOf S Θ f (AggQueryIn.Sum q₁ q₂) p := fun hp =>
      ⟨hp.usesOnly, hp.hygienic, hp.inSig, fun hw => hp.wins hw.1,
        fun sch hsch ho => hp.over sch (fun i => hsch (i + 2)) ho.1,
        fun x hx => names_shift (hp.names x hx) Finset.subset_union_left,
        fun s hs hn => hp.nom s (fun i => hs (i + 2)) hn.1⟩
    have hright : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ _ l'},
        SumFreeOf S Θ (shift2 f) q₂ p →
        SumFreeOf S Θ f (AggQueryIn.Sum q₁ q₂) p := fun hp =>
      ⟨hp.usesOnly, hp.hygienic, hp.inSig, fun hw => hp.wins hw.2,
        fun sch hsch ho => hp.over sch (fun i => hsch (i + 2)) ho.2,
        fun x hx => names_shift (hp.names x hx) Finset.subset_union_right,
        fun s hs hn => hp.nom s (fun i => hs (i + 2)) hn.2⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
      obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
      refine ⟨sumByMu (f 0) (f 1) q₁' q₂', hbundle hs₁ hs₂, fun D γ hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
      obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
      obtain ⟨hv, hv'⟩ := hval hs₁ hs₂ D γ hs₁' hs₂'
      refine ⟨hv, ?_⟩
      show (q₁.evaluatePlain D γ : Multiset (Tuple T _)) + q₂.evaluatePlain D γ = _
      rw [hv', he₁', he₂']
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
        obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hb₁ s m rfl h₁
        have hss : s ∈ (AggQueryIn.Sum q₁ q₂).names :=
          Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁
            (List.mem_singleton_self _))
        refine ⟨p₁, sumByMu (f 0) (f 1) pC q₂',
          noMention_sumByMu _ _ _ _ hCn
            (hs₂.nom s (ne_shift_of_mem hfr hss) h₂),
          hleft hp, hbundle hpC hs₂, fun D γ hset => ?_⟩
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.1
        obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
        obtain ⟨hv, hv'⟩ := hval hpC hs₂ D γ hpC' hs₂'
        refine ⟨hp', hv, ?_⟩
        show (q₁.evaluatePlain D γ : Multiset (Tuple T _)) + q₂.evaluatePlain D γ = _
        rw [hv', he', he₂']
        show (_ : Multiset (Tuple T _)) + _ + _ = _ + (_ + _)
        exact add_assoc _ _ _
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
        obtain ⟨p₂, pC, hCn, hp, hpC, he⟩ := hb₂ s m rfl h₂
        have hss : s ∈ (AggQueryIn.Sum q₁ q₂).names :=
          Finset.mem_union_right _ (AggQueryIn.mem_names_of_index q₂
            (List.mem_singleton_self _))
        refine ⟨p₂, sumByMu (f 0) (f 1) q₁' pC,
          noMention_sumByMu _ _ _ _
            (hs₁.nom s (ne_shift_of_mem hfr hss) h₁) hCn,
          hright hp, hbundle hs₁ hpC, fun D γ hset => ?_⟩
        obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.2
        obtain ⟨hv, hv'⟩ := hval hs₁ hpC D γ hs₁' hpC'
        refine ⟨hp', hv, ?_⟩
        show (q₁.evaluatePlain D γ : Multiset (Tuple T _)) + q₂.evaluatePlain D γ = _
        rw [hv', he₁', he']
        show (_ : Multiset (Tuple T _)) + (_ + _) = _ + (_ + _)
        exact add_left_comm _ _ _
  | Dedup q ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi hsa f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.Dedup q', ⟨⟨memS nofun hq.1, hs.usesOnly⟩, hs.hygienic,
      hs.inSig, hs.wins, hs.over, hs.names, hs.nom⟩, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he D γ hset
    exact ⟨hs', by simp only [AggQueryIn.evaluatePlain, he']⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hsa f hf hfr
    have hfr₁ := fresh_sub hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_sub hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, -⟩ := ih₁ hq.2.1 hr.1 hi.1 hsa.1 f hf hfr₁
    obtain ⟨hc₂, -⟩ := ih₂ hq.2.2 hr.2 hi.2 hsa.2 f hf hfr₂
    obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
    obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
    refine ⟨fun _ => ⟨AggQueryIn.Diff q₁' q₂', ⟨⟨memS nofun hq.1, hs₁.usesOnly, hs₂.usesOnly⟩,
      ⟨hs₁.hygienic, hs₂.hygienic⟩, ⟨hs₁.inSig, hs₂.inSig⟩,
      fun hw => ⟨hs₁.wins hw.1, hs₂.wins hw.2⟩,
      fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
      fun x hx => (Finset.mem_union.mp hx).elim
        (fun h => (hs₁.names x h).imp_left (Finset.mem_union_left _))
        (fun h => (hs₂.names x h).imp_left (Finset.mem_union_right _)),
      fun s hs hn => ⟨hs₁.nom s hs hn.1, hs₂.nom s hs hn.2⟩⟩, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
    obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
    exact ⟨⟨hs₁', hs₂'⟩, by simp only [AggQueryIn.evaluatePlain, he₁', he₂']⟩
  | Explode k hk q ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, hb⟩ := ih hq hr hi hsa f hf hfr
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      exact ⟨AggQueryIn.Explode k hk q', ⟨hs.usesOnly, hs.hygienic, hs.inSig, hs.wins,
        hs.over, hs.names, hs.nom⟩, fun D γ hset => he D γ hset⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      exact ⟨AggQueryIn.Explode k hk q', AggQueryIn.Explode k hk qC, hCn,
        ⟨hs.usesOnly, hs.hygienic, hs.inSig, hs.wins, hs.over, hs.names, hs.nom⟩,
        ⟨hsC.usesOnly, hsC.hygienic, hsC.inSig, hsC.wins, hsC.over, hsC.names, hsC.nom⟩,
        fun D γ hset => he D γ hset⟩
  | Retag hk q ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, hb⟩ := ih hq hr hi hsa f hf hfr
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      exact ⟨AggQueryIn.Retag hk q', ⟨hs.usesOnly, hs.hygienic, hs.inSig, hs.wins,
        hs.over, hs.names, hs.nom⟩, fun D γ hset => he D γ hset⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      exact ⟨AggQueryIn.Retag hk q', AggQueryIn.Retag hk qC, hCn,
        ⟨hs.usesOnly, hs.hygienic, hs.inSig, hs.wins, hs.over, hs.names, hs.nom⟩,
        ⟨hsC.usesOnly, hsC.hygienic, hsC.inSig, hsC.wins, hsC.over, hsC.names, hsC.nom⟩,
        fun D γ hset => he D γ hset⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hq hr hi hsa f hf hfr
    have hfr₀ : ∀ i, f i ∉ q₀.names :=
      fun i h => hfr i (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hfr₁ : ∀ i, f i ∉ q₁.names :=
      fun i h => hfr i (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hfs : ∀ i, s ≠ f i := ne_of_mem hfr (Finset.mem_insert_self s _)
    obtain ⟨hc₀, -⟩ := ih₀ hq.2.1 hr.2.2.1 hi.1 hsa.1 f hf hfr₀
    obtain ⟨q₀', hs₀, he₀⟩ := hc₀ rfl
    obtain ⟨-, hb₁⟩ := ih₁ hq.2.2 hr.2.2.2 hi.2 hsa.2 f hf hfr₁
    obtain ⟨q₁', qC, hCn, hs₁, hsC, he₁⟩ := hb₁ s _ rfl hr.2.1
    refine ⟨fun _ => ⟨AggQueryIn.Mu s q₀' q₁', ?_, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · exact {
        usesOnly := ⟨memS nofun hq.1, hs₀.usesOnly, hs₁.usesOnly⟩
        hygienic := ⟨hs₀.nom s hfs hr.1, hs₁.nom s hfs hr.2.1, hs₀.hygienic, hs₁.hygienic⟩
        inSig := ⟨hs₀.inSig, hs₁.inSig⟩
        wins := fun hw => ⟨hs₀.wins hw.1, hs₁.wins hw.2⟩
        over := fun sch hsch ho => ⟨ho.1, hs₀.over sch hsch ho.2.1, hs₁.nom s hfs hr.2.1,
          hs₁.over (sch.update s _) (fun i => by
            show (if f i = s then _ else _) = none
            rw [ite_eq_right (hfs i).symm]
            exact hsch i) ho.2.2.2⟩
        names := fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact Or.inl (Finset.mem_insert_self _ _)
          exact (Finset.mem_union.mp hx').elim
            (fun h => (hs₀.names x h).imp_left
              (fun h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
            (fun h => (hs₁.names x h).imp_left
              (fun h => Finset.mem_insert_of_mem (Finset.mem_union_right _ h)))
        nom := fun s' hs' hn => ⟨hs₀.nom s' hs' hn.1, hs₁.nom s' hs' hn.2⟩ }
    · exact AggQueryIn.mu_of_split s q₀ q₀' q₁ q₁' qC hCn D γ hset (he₀ D γ hset.1)
        (fun D' h => he₁ D' γ h)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hq hr hi hsa f hf hfr
    have hfr₀ : ∀ i, shift2 f i ∉ q₀.names :=
      fun i h => hfr (i + 2) (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hfr₁ : ∀ i, shift2 f i ∉ q₁.names :=
      fun i h => hfr (i + 2) (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hfs : ∀ i, s ≠ f i := ne_of_mem hfr (Finset.mem_insert_self s _)
    have hf0₀ : f 0 ∉ q₀.names :=
      fun h => hfr 0 (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hf1₀ : f 1 ∉ q₀.names :=
      fun h => hfr 1 (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hf1₁ : f 1 ∉ q₁.names :=
      fun h => hfr 1 (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    obtain ⟨hc₀, -⟩ :=
      ih₀ hq.2.1 hr.2.2.1 hi.1 hsa.1 (shift2 f) (shift2_injective hf) hfr₀
    obtain ⟨q₀', hs₀, he₀⟩ := hc₀ rfl
    obtain ⟨-, hb₁⟩ := ih₁ hq.2.2 hr.2.2.2 hi.2 hsa.2 (shift2 f) (shift2_injective hf) hfr₁
    obtain ⟨q₁', qC, hCn, hs₁, hsC, he₁⟩ := hb₁ s _ rfl hr.2.1
    have hn₀₀ : f 0 ∉ q₀'.names := not_mem_of_shift hf hs₀.names (by omega) hf0₀
    have hn₀₁ : f 1 ∉ q₀'.names := not_mem_of_shift hf hs₀.names (by omega) hf1₀
    have hnC1 : f 1 ∉ qC.names := not_mem_of_shift hf hsC.names (by omega) hf1₁
    have h₀n : q₀'.noMention s := hs₀.nom s (fun i => hfs (i + 2)) hr.1
    have hbn : (sumByMu (f 0) (f 1) q₀' qC).noMention s :=
      noMention_sumByMu _ _ _ _ h₀n hCn
    have hupd : ∀ (m : ℕ) (sch : Schema), (∀ i, sch (f i) = none) →
        ∀ i, (sch.update s m) (f i) = none := fun m sch hsch i => by
      show (if f i = s then _ else _) = none
      rw [ite_eq_right (hfs i).symm]
      exact hsch i
    refine ⟨fun _ => ⟨AggQueryIn.MuSet s (sumByMu (f 0) (f 1) q₀' qC) q₁', ?_,
      fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    · exact {
        usesOnly := ⟨memS nofun hq.1, usesOnly_sumByMu hS _ _ _ _ hs₀.usesOnly hsC.usesOnly,
          hs₁.usesOnly⟩
        hygienic := ⟨hbn, hs₁.nom s (fun i => hfs (i + 2)) hr.2.1, hygienic_sumByMu _ _ _ _
          (AggQueryIn.noMention_of_not_mem_names _ hn₀₀)
          (AggQueryIn.noMention_of_not_mem_names _ hn₀₁)
          (AggQueryIn.noMention_of_not_mem_names _ hnC1)
          hs₀.hygienic hsC.hygienic, hs₁.hygienic⟩
        inSig := ⟨inSig_sumByMu Θ _ _ _ _ hs₀.inSig hsC.inSig, hs₁.inSig⟩
        wins := fun hw => ⟨winsDerivable_sumByMu _ _ _ _ (hs₀.wins hw.1) (hsC.wins hw.2),
          hs₁.wins hw.2⟩
        over := fun sch hsch ho => ⟨ho.1,
          overSchema_sumByMu sch _ _ _ _ (hsch 0) (hsch 1) hn₀₀ hnC1
            (hs₀.over sch (fun i => hsch (i + 2)) ho.2.1)
            (AggQueryIn.overSchema_of_update_of_noMention qC (fun _ h => by simp at h) hCn
              (hsC.over (sch.update s _) (fun i => hupd _ sch hsch (i + 2)) ho.2.2.2)),
          hs₁.nom s (fun i => hfs (i + 2)) hr.2.1,
          hs₁.over (sch.update s _) (fun i => hupd _ sch hsch (i + 2)) ho.2.2.2⟩
        names := fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact Or.inl (Finset.mem_insert_self _ _)
          rcases Finset.mem_union.mp hx' with h | h
          · rcases Finset.mem_insert.mp (names_sumByMu _ _ _ _ h) with rfl | h'
            · exact Or.inr ⟨0, rfl⟩
            rcases Finset.mem_insert.mp h' with rfl | h''
            · exact Or.inr ⟨1, rfl⟩
            exact (Finset.mem_union.mp h'').elim
              (fun h => names_shift (hs₀.names x h)
                (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)))
              (fun h => names_shift (hsC.names x h)
                (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_right _ hy)))
          · exact names_shift (hs₁.names x h)
              (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_right _ hy))
        nom := fun s' hs' hn => ⟨noMention_sumByMu _ _ _ _
          (hs₀.nom s' (fun i => hs' (i + 2)) hn.1) (hsC.nom s' (fun i => hs' (i + 2)) hn.2),
          hs₁.nom s' (fun i => hs' (i + 2)) hn.2⟩ }
    · exact AggQueryIn.muSet_of_split s q₀ q₀' q₁ q₁' qC _ hCn D γ hset
        (fun D' h => he₀ D' γ h) (fun D' h => he₁ D' γ h)
        (fun D' h₀ hC => ⟨settlesAt_sumByMu _ _ _ _
            (AggQueryIn.noMention_of_not_mem_names _ hn₀₀)
            (AggQueryIn.noMention_of_not_mem_names _ hnC1) D' γ h₀ hC,
          evaluatePlain_sumByMu _ _ _ _
            (AggQueryIn.noMention_of_not_mem_names _ hn₀₀)
            (AggQueryIn.noMention_of_not_mem_names _ hnC1) D' γ⟩)
  | Gamma is ts fs q keep ord ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2.2 hsa f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) is ts fs q' keep ord,
        ⟨⟨memS nofun hq.1,
        hs.usesOnly⟩,
      hs.hygienic, ⟨hi.1, hi.2.1, hi.2.2.1, hs.inSig⟩, hs.wins, hs.over, hs.names,
      hs.nom⟩, fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he D γ hset
    exact ⟨hs', by simp only [AggQueryIn.evaluatePlain, he']⟩
  | GammaScalar ts fs q ord ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2 hsa f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q' ord, ⟨⟨memS
        nofun hq.1,
        hs.usesOnly⟩,
      hs.hygienic, ⟨hi.1, hi.2.1, hs.inSig⟩, hs.wins, hs.over, hs.names,
      hs.nom⟩, fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he D γ hset
    exact ⟨hs', by simp only [AggQueryIn.evaluatePlain, he']⟩
  | GammaNest is his p fn q ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2 hsa f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) is his p fn q',
        ⟨⟨⟨memS nofun hq.1.1, hq.1.2⟩,
        hs.usesOnly⟩,
      hs.hygienic, ⟨hi.1, hi.2.1, hs.inSig⟩, hs.wins, hs.over, hs.names,
      hs.nom⟩, fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he D γ hset
    exact ⟨hs', by simp only [AggQueryIn.evaluatePlain, he']⟩
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t fw q hrr dist keep ih =>
    intro hq hr hi hsa f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2.2.2 hsa f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) P O o
        w t fw q' hrr dist
        keep, ⟨⟨memS nofun hq.1,
        hs.usesOnly⟩,
      hs.hygienic, ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hs.inSig⟩,
      fun hw => ⟨hw.1, hw.2.1, hs.wins hw.2.2⟩, hs.over, hs.names,
      hs.nom⟩, fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he D γ hset
    exact ⟨hs', by simp only [AggQueryIn.evaluatePlain, he']⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ _ hi => hi.elim

/-- **`⊎` is derivable from `μ^⊎` in the minimal universe** (`⊎` is not
needed in a basis of the whole algebra once `μ^⊎` is available): every
query over the classes of `S` and `⊎` –
restricted recursions, the signature `Θ`, every `⊎` all-regular – is
matched, on every instance where it is defined, by one over the classes
of `S` alone, for any `S` holding the construction's classes
(`sumMuOps`: `∅`, `Π`, `σ`, apply, `γ`, `μ^⊎`). The names the
construction binds come from an injective supply the query does not
use, which `exists_freshSupply` provides. -/
theorem exists_sumFree {S : Set OpKind} (hS : sumMuOps ⊆ S) {Θ : Set (SeqAggFunc T)}
    {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
    (hq : q.usesOnly (insert OpKind.union S)) (hr : q.hygienic) (hi : q.inSig Θ)
    (hsa : q.sumsAllReg) (f : ℕ → String) (hf : Function.Injective f)
    (hfr : ∀ i, f i ∉ q.names) :
    ∃ q' : AggQueryIn T c n κ,
      q'.usesOnly S ∧ q'.hygienic ∧ q'.inSig Θ
        ∧ (q.WinsDerivable → q'.WinsDerivable)
        ∧ (∀ sch : Schema, (∀ i, sch (f i) = none) → q.overSchema sch → q'.overSchema sch)
        ∧ ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
            q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  obtain ⟨q', hs, he⟩ := (exists_sumFree_aux hS q hq hr hi hsa f hf hfr).1 rfl
  exact ⟨q', hs.usesOnly, hs.hygienic, hs.inSig, hs.wins, hs.over, he⟩

/-- **A supply of fresh names exists** for a schema declaring finitely
many names and a finite set of names to avoid, `String` being infinite. -/
theorem exists_freshSupply (sch : Schema) (N : Finset String) :
    ∃ f : ℕ → String, Function.Injective f ∧ (∀ i, sch (f i) = none) ∧ ∀ i, f i ∉ N := by
  have hinf : ({s | sch s ≠ none} ∪ (↑N : Set String))ᶜ.Infinite :=
    (sch.finite.union N.finite_toSet).infinite_compl
  let e := hinf.natEmbedding
  refine ⟨fun i => (e i).1, fun a b h => e.injective (Subtype.ext h), fun i => ?_, fun i => ?_⟩
  · have := (e i).2
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe,
      not_or, not_not] at this
    exact this.1
  · have := (e i).2
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe,
      not_or, not_not] at this
    exact this.2

end AggQueryIn
