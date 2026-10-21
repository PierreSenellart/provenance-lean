module

public import Provenance.SelRow
public import Provenance.WinRow
public import Provenance.AggQueryAdequacy
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Provenance.RoundBound
import all Provenance.AggQuery
import all Provenance.AggQueryAdequacy
import all Provenance.AggQuerySubst
import all Provenance.Database
import all Provenance.PlainBasis
import all Provenance.QueryAdequacy
import all Provenance.RecursionBasis
import all Provenance.WinRow

/-!
# The basis of the annotated semantics: the statement and the inherited rows

A set of classes *generates the annotated algebra* over a semiring `K`
(`GeneratesAnn`) when every query of the whole algebra in the minimal
universe that reads no aggregate column as a key is matched, over the
same classes, by a query of the same kinds whose annotated evaluation
agrees with it on every `K`-instance wherever the query's recursions
settle there (`AggQueryIn.AnnSettlesAt`). The equality is of the bags of
annotated tuples the two queries emit, tokens collapsed and group
factors cashed (`AggQueryIn.evaluateAnnotated`); it is finer than
equality up to rows annotated `𝟘` (`GeneratesAnnZ`), so a set that
generates here generates there.

What transfers from the plain classification, for every semiring at
once: the data part of the annotated evaluation is the plain evaluation
of the query stripped of its aggregate selections and differences
(`AggQueryIn.evaluateAnnotated_toPlain`), and the recursions settle
annotated exactly when the stripped query's do plain
(`AggQueryIn.settlesAt_stripAgg_of_annSettlesAt`,
`AggQueryIn.annSettlesAt_of_settlesAt`). So a set generating the
annotated algebra generates, in the plain semantics, every query with
nothing to strip (`generatesAtNoExplode_of_generatesAnn`), which every
witness of the plain rows is: `∅`, `Π`, `γ`, `μ^⊎`, `win`, `σ` and one
of `×`/apply are in every set generating the annotated algebra over
`ℕ` with the counting aggregate (`required_mem_of_generatesAnn`). The
selection row holds outright here, the alternatives being out of the
language. The trivial generating set is every class
(`generatesAnn_plainRecOps`); the smaller ones are the next step.
-/

@[expose] public section

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-! ## A plain instance, annotated `𝟙` -/

/-- Every tuple annotated `𝟙`. -/
def Relation.liftOne {n : ℕ} (r : Relation T n) : AnnotatedRelation T K n :=
  Multiset.map (fun u => (u, (1 : K))) r

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem Relation.toPlain_liftOne {n : ℕ} (r : Relation T n) :
    (Relation.liftOne (K := K) r).toPlain = r := by
  unfold Relation.liftOne AnnotatedRelation.toPlain
  rw [Multiset.map_map]
  exact Multiset.map_id' r

/-- Every tuple of every relation annotated `𝟙`. -/
def Database.liftOne (D : Database T) : AnnotatedDatabase T K :=
  D.map (fun e => (e.fst, ⟨e.snd.fst, Relation.liftOne (K := K) e.snd.snd⟩))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem Database.toPlain_liftOne (D : Database T) : (D.liftOne (K := K)).toPlain = D := by
  unfold Database.liftOne AnnotatedDatabase.toPlain
  rw [List.map_map]
  refine Eq.trans (List.map_congr_left (fun e _ => ?_)) (List.map_id _)
  obtain ⟨s, n, r⟩ := e
  show ((s, ⟨n, (Relation.liftOne (K := K) r).toPlain⟩) : String × Σ n, Relation T n) = (s, ⟨n, r⟩)
  rw [Relation.toPlain_liftOne]

/-! ## Queries with nothing to strip -/

/-- **A query whose annotated reading of a plain instance is faithful to
its plain reading**: no selection on an aggregate value and no
difference, so `stripAgg` removes nothing and the data part of the
annotated evaluation is the plain evaluation of the query itself; and no
set recursion, whose annotated rounds may go on changing annotations
where its plain rounds have settled. Every witness of the plain rows is
one. -/
def AggQueryIn.liftFaithful : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.liftFaithful
  | _, _, _, _, .Sel φ q _ => φ.hasAggAtom = false ∧ q.liftFaithful
  | _, _, _, _, .Prod q₁ q₂ => q₁.liftFaithful ∧ q₂.liftFaithful
  | _, _, _, _, .Apply q₁ q₂ => q₁.liftFaithful ∧ q₂.liftFaithful
  | _, _, _, _, .Sum q₁ q₂ => q₁.liftFaithful ∧ q₂.liftFaithful
  | _, _, _, _, .Dedup q => q.liftFaithful
  | _, _, _, _, .Diff _ _ => False
  | _, _, _, _, .Explode _ _ q => q.liftFaithful
  | _, _, _, _, .Retag _ q => q.liftFaithful
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.liftFaithful ∧ q₁.liftFaithful
  | _, _, _, _, .MuSet _ _ _ => False
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.liftFaithful
  | _, _, _, _, .GammaScalar _ _ q _ => q.liftFaithful
  | _, _, _, _, .GammaNest _ _ _ _ q => q.liftFaithful
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.liftFaithful
  | _, _, _, _, .ProvSum _ _ _ q => q.liftFaithful
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.liftFaithful
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.liftFaithful

omit [ValueType T] in
@[simp] private theorem AggQueryIn.liftFaithful_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).liftFaithful ↔ q.liftFaithful := by
  cases h; exact Iff.rfl

omit [ValueType T] in
@[simp] private theorem AggQueryIn.noExplode_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).noExplode ↔ q.noExplode := by
  cases h; exact Iff.rfl

omit [ValueType T] in
private theorem AggQueryIn.stripAgg_eq_of_liftFaithful :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.liftFaithful → q.stripAgg = q := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ => rfl
  | Hole _ _ => exact fun _ => rfl
  | Param pv ρ => exact fun _ => rfl
  | Empty => exact fun _ => rfl
  | Proj ps q ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | Sel φ q hφ ih =>
    intro h
    rw [AggQueryIn.stripAgg, ite_eq_right (by rw [h.1]; exact Bool.false_ne_true), ih h.2]
  | Prod q₁ q₂ ih₁ ih₂ => intro h; rw [AggQueryIn.stripAgg, ih₁ h.1, ih₂ h.2]
  | Apply q₁ q₂ ih₁ ih₂ => intro h; rw [AggQueryIn.stripAgg, ih₁ h.1, ih₂ h.2]
  | Sum q₁ q₂ ih₁ ih₂ => intro h; rw [AggQueryIn.stripAgg, ih₁ h.1, ih₂ h.2]
  | Dedup q ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | Retag hk q ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | Mu s q₀ q₁ ih₀ ih₁ => intro h; rw [AggQueryIn.stripAgg, ih₀ h.1, ih₁ h.2]
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | GammaScalar ts fs q ord ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | GammaNest is his p f q ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | ProvSum is his t q ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | GammaTok is his ts fs a q keep ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | Win P O o w t f q hrr dist keep ih => intro h; rw [AggQueryIn.stripAgg, ih h]
  | WinExpr P O o ws ts fs g q keeps ih => intro h; rw [AggQueryIn.stripAgg, ih h]

/-! ## What stripping keeps -/

omit [ValueType T] in
private theorem AggQueryIn.usesOnly_stripAgg {S : Set OpKind} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.stripAgg.usesOnly S := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Param pv ρ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ⟨h.1, ih h.2⟩
  | Sel φ q hφ ih =>
    intro h
    rw [AggQueryIn.stripAgg]
    by_cases hφa : φ.hasAggAtom = true
    · rw [ite_eq_left hφa]; exact ih h.2
    · rw [ite_eq_right hφa]; exact ⟨h.1, ih h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | Dedup q ih => exact fun h => ⟨h.1, ih h.2⟩
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.2.1
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨h.1, ih₀ h.2.1, ih₁ h.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨h.1, ih₀ h.2.1, ih₁ h.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ⟨h.1, ih h.2⟩
  | GammaScalar ts fs q ord ih => exact fun h => ⟨h.1, ih h.2⟩
  | GammaNest is his p f q ih => exact fun h => ⟨h.1, ih h.2⟩
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t f q hrr dist keep ih => exact fun h => ⟨h.1, ih h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ⟨h.1, ih h.2⟩

private theorem AggQueryIn.inSig_stripAgg {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig Θ → q.stripAgg.inSig Θ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Param pv ρ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ⟨h.1, ih h.2⟩
  | Sel φ q hφ ih =>
    intro h
    rw [AggQueryIn.stripAgg]
    by_cases hφa : φ.hasAggAtom = true
    · rw [ite_eq_left hφa]; exact ih h.2
    · rw [ite_eq_right hφa]; exact ⟨h.1, ih h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ⟨h.1, h.2.1, h.2.2.1, ih h.2.2.2⟩
  | GammaScalar ts fs q ord ih => exact fun h => ⟨h.1, h.2.1, ih h.2.2⟩
  | GammaNest is his p f q ih => exact fun h => ⟨h.1, h.2.1, ih h.2.2⟩
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t f q hrr dist keep ih => exact fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ih
    h.2.2.2.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
private theorem AggQueryIn.noMention_stripAgg {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention s → q.stripAgg.noMention s := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Param pv ρ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q hφ ih =>
    intro h
    rw [AggQueryIn.stripAgg]
    by_cases hφa : φ.hasAggAtom = true
    · rw [ite_eq_left hφa]; exact ih h
    · rw [ite_eq_right hφa]; exact ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p f q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t f q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

omit [ValueType T] in
private theorem AggQueryIn.overSchema_stripAgg {sch : Schema} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.overSchema sch → q.stripAgg.overSchema sch := by
  intro c n κ l q
  induction q generalizing sch with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Param pv ρ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q hφ ih =>
    intro h
    rw [AggQueryIn.stripAgg]
    by_cases hφa : φ.hasAggAtom = true
    · rw [ite_eq_left hφa]; exact ih h
    · rw [ite_eq_right hφa]; exact ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact fun h => ⟨h.1, ih₀ h.2.1, AggQueryIn.noMention_stripAgg q₁ h.2.2.1, ih₁ h.2.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun h => ⟨h.1, ih₀ h.2.1, AggQueryIn.noMention_stripAgg q₁ h.2.2.1, ih₁ h.2.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p f q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t f q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

omit [ValueType T] in
private theorem AggQueryIn.noExplode_stripAgg :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noExplode → q.stripAgg.noExplode := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Param pv ρ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q hφ ih =>
    intro h
    rw [AggQueryIn.stripAgg]
    by_cases hφa : φ.hasAggAtom = true
    · rw [ite_eq_left hφa]; exact ih h
    · rw [ite_eq_right hφa]; exact ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Explode k hk q ih => exact fun h => h.elim
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p f q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t f q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

/-! ## The settling of the recursions, annotated and plain -/

/-- A closed query settling at a round settles at the empty round: it
reads the round through nothing. -/
private theorem AggQueryIn.settlesAt_assign_zero_of_noMention {s : String} {m : ℕ} (X : Relation T m)
    {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ) (hq : q.noMention s)
    (D : Database T) (γ : Fin c → T) (h : q.SettlesAt (D.assign s X) γ) :
    q.SettlesAt (D.assign s (0 : Relation T m)) γ := by
  refine AggQueryIn.settlesAt_of_noMention q hq (D := D) (D' := D.assign s 0) ?_ γ
    (AggQueryIn.settlesAt_assign_of_noMention X q hq D γ h)
  intro k t ht
  have hne : ¬ (k = m ∧ t = s) := fun hc => (ht.resolve_right List.not_mem_nil) hc.2
  exact (Database.find_assign_of_ne s t _ D hne).symm

/-- **A body settling at a round settles at the empty round**: what it
reads of the round, it reads through its hole once, so the rows the
empty round gives its apply's right sides are among the ones any round
gives. -/
private theorem AggQueryIn.settlesAt_assign_zero_of_body {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      l = [(s, m)] → q.noMention s → ∀ (D : Database T) (γ : Fin c → T) (X : Relation T m),
        q.SettlesAt (D.assign s X) γ → q.SettlesAt (D.assign s (0 : Relation T m)) γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun hl => absurd hl (by simp)
  | Hole _ _ => exact fun _ _ _ _ _ _ => trivial
  | Param pv ρ => exact fun _ _ _ _ _ _ => trivial
  | Empty => exact fun hl => absurd hl (by simp)
  | Proj ps q ih => exact fun hl hr D γ X h => ih hl hr D γ X h
  | Sel φ q hφ ih => exact fun hl hr D γ X h => ih hl hr D γ X h
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hl hr D γ X h
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      exact ⟨ih₁ h₁ hr.1 D γ X h.1,
        AggQueryIn.settlesAt_assign_zero_of_noMention X q₂ hr.2 D γ h.2⟩
    · subst h₁
      exact ⟨AggQueryIn.settlesAt_assign_zero_of_noMention X q₁ hr.1 D γ h.1,
        ih₂ h₂ hr.2 D γ X h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l₁
    intro hl hr D γ X h
    refine ⟨ih₁ hl hr.1 D γ X h.1, fun u hu => ?_⟩
    obtain ⟨F, C, hF⟩ := AggQueryIn.bind_of_body q₁ hl hr.1 D γ
    have hu' : Multiset.Mem (q₁.evaluatePlain (D.assign s X) γ) u := by
      rw [← Multiset.Mem_iff] at hu ⊢
      rw [hF] at hu ⊢
      rw [Multiset.zero_bind, zero_add] at hu
      exact Multiset.mem_of_le (Multiset.le_add_left _ _) hu
    exact AggQueryIn.settlesAt_assign_zero_of_noMention X q₂ hr.2 D _ (h.2 u hu')
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hl hr D γ X h
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      exact ⟨ih₁ h₁ hr.1 D γ X h.1,
        AggQueryIn.settlesAt_assign_zero_of_noMention X q₂ hr.2 D γ h.2⟩
    · subst h₁
      exact ⟨AggQueryIn.settlesAt_assign_zero_of_noMention X q₁ hr.1 D γ h.1,
        ih₂ h₂ hr.2 D γ X h.2⟩
  | Dedup q ih => exact fun hl => absurd hl (by simp)
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hl => absurd hl (by simp)
  | Explode k hk q ih => exact fun hl hr D γ X h => ih hl hr D γ X h
  | Retag hk q ih => exact fun hl hr D γ X h => ih hl hr D γ X h
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun hl => absurd hl (by simp)
  | Gamma is ts fs q keep ord ih => exact fun hl => absurd hl (by simp)
  | GammaScalar ts fs q ord ih => exact fun hl => absurd hl (by simp)
  | GammaNest is his p f q ih => exact fun hl => absurd hl (by simp)
  | ProvSum is his t q ih => exact fun hl => absurd hl (by simp)
  | GammaTok is his ts fs a q keep ih => exact fun hl => absurd hl (by simp)
  | Win P O o w t f q hrr dist keep ih => exact fun hl => absurd hl (by simp)
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hl => absurd hl (by simp)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- The data part of the empty annotated relation. -/
private theorem AnnotatedRelation.toPlain_zero {n : ℕ} :
    (0 : AnnotatedRelation T K n).toPlain = (0 : Multiset (Tuple T n)) :=
  Multiset.map_zero _

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem AnnotatedRelation.toPlain_eq_zero_iff {n : ℕ} (r : AnnotatedRelation T K n) :
    r.toPlain = 0 ↔ r = 0 :=
  Multiset.map_eq_zero

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Stripping the aggregate selections keeps the query well-kinded. -/
private theorem AggQueryIn.wellKinded_stripAgg :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {ρc : Fin c → ColKind} {HK : HoleKinds},
          q.wellKinded ρc HK → q.stripAgg.wellKinded ρc HK := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ _ => exact fun h => h
  | Param _ _ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ⟨h.1, ih h.2⟩
  | Sel φ q hφ ih =>
    intro ρc HK h
    rw [AggQueryIn.stripAgg]
    by_cases hφa : φ.hasAggAtom = true
    · rw [ite_eq_left hφa]; exact ih h.2
    · rw [ite_eq_right hφa]; exact ⟨h.1, ih h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ⟨h.1, ih h.2⟩
  | GammaScalar ts fs q ord ih => exact fun h => ⟨h.1, ih h.2⟩
  | GammaNest is his p f q ih => exact fun h => ⟨h.1, ih h.2⟩
  | ProvSum is his t q ih => exact fun h => ⟨h.1, ih h.2⟩
  | GammaTok is his ts fs a q keep ih => exact fun h => ⟨h.1, h.2.1, ih h.2.2⟩
  | Win P O o w t f q hrr dist keep ih => exact fun h => ⟨h.1, ih h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ⟨h.1, ih h.2⟩

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem map_plainTuple_ofAnnotated {m : ℕ} (X : AnnotatedRelation T K m) :
    (X.map GenRow.ofAnnotated).map (fun r : GenRow T K m => GenRow.plainTuple r.fst)
      = X.toPlain := by
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl (fun p _ => GenRow.plainTuple_ofAnnotated (K := K) p)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem conforms_ofAnnotated {m : ℕ} (X : AnnotatedRelation T K m) :
    ∀ r ∈ X.map GenRow.ofAnnotated, GenRow.Conforms (ColKind.allReg m) r.fst := by
  intro r hr k
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hr
  rfl

/-- **Settling annotated is settling plain, stripped**: where the annotated
evaluation's recursions settle, the stripped query's do on the data
part – under an environment, the plain instance binding each recursive
name to the data part of the round the environment binds it to. -/
private theorem AggQueryIn.settlesAt_stripAgg_of_annSettlesAt_env :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noExplode → q.hygienic → ∀ {ρc : Fin c → ColKind} {HK : HoleKinds},
      q.wellKinded ρc HK →
      ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (D : Database T)
        (N : Set String), E.Kinded γ ρc HK →
      (∀ (n' : ℕ) (s' : String), s' ∉ N →
        D.find n' s' = (d.find n' s').map AnnotatedRelation.toPlain) →
      (∀ s' ∈ N, q.noMention s') →
      (∀ p ∈ l, D.find p.2 p.1
        = some ((E.holes p.1 p.2).map (fun r => GenRow.plainTuple r.fst))) →
      q.AnnSettlesAt d γ E → q.stripAgg.SettlesAt D γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intros; trivial
  | Hole _ _ _ => intros; trivial
  | Param pv ρ => intros; trivial
  | Empty => intros; trivial
  | Proj ps q ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
  | Sel φ q hφ ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    rw [AggQueryIn.stripAgg]
    by_cases hφa : φ.hasAggAtom = true
    · rw [ite_eq_left hφa]; exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
    · rw [ite_eq_right hφa]; exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ⟨ih₁ hq.1 hh.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
        (fun p hp => hH p (List.mem_append_left _ hp)) hr.1,
      ih₂ hq.2 hh.2 hwk.2 d γ E D N hE hD (fun s' h => (hN s' h).2)
        (fun p hp => hH p (List.mem_append_right _ hp)) hr.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    refine ⟨ih₁ hq.1 hh.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1) hH hr.1,
      fun u hu => ?_⟩
    rw [← AggQueryIn.evaluate_toPlain_env q₁ hq.1 hh.1 hwk.1 d E D N hE hD
      (fun s' h => (hN s' h).1) hH hr.1] at hu
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hu
    exact ih₂ hq.2 hh.2 hwk.2 d _ _ D N
      (hE.enter (fun k => AggQueryIn.evaluate_conform q₁ d x hx k)) hD
      (fun s' h => (hN s' h).2) (fun p hp => absurd hp List.not_mem_nil) (hr.2 x hx)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ⟨ih₁ hq.1 hh.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
        (fun p hp => hH p (List.mem_append_left _ hp)) hr.1,
      ih₂ hq.2 hh.2 hwk.2 d γ E D N hE hD (fun s' h => (hN s' h).2)
        (fun p hp => hH p (List.mem_append_right _ hp)) hr.2⟩
  | Dedup q ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk d γ E D N hE hD hN hH hr
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih₁ hq.1 hh.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
      (fun p hp => absurd hp List.not_mem_nil) hr.1
  | Explode k hk q ih => exact fun hq => hq.elim
  | Retag hk q ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk d γ E D N hE hD hN hH hr
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m κ'
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    obtain ⟨h₀, hz, hs, hk, h0⟩ := hr
    have hit : ∀ k, ∀ r ∈ (AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E),
        GenRow.Conforms κ' r.fst := by
      intro k
      induction k with
      | zero => exact fun r hr' k => AggQueryIn.evaluate_conform q₀ d r hr' k
      | succ k _ =>
        intro r hr'
        rw [Function.iterate_succ_apply'] at hr'
        exact fun k => AggQueryIn.evaluate_conform q₁ d r hr' k
    have hnom : ∀ s' ∈ insert s N, q₁.noMention s' := fun s' h =>
      (Set.mem_insert_iff.mp h).elim (fun he => he ▸ hh.2.1) (fun hn => (hN s' hn).2)
    have hholes : ∀ X : Multiset (GenRow T K m), ∀ p ∈ [(s, m)], (D.assign s
        (X.map (fun r : GenRow T K m => GenRow.plainTuple r.fst))).find p.2 p.1
        = some (((E.assignHole s X).holes p.1 p.2).map (fun r => GenRow.plainTuple r.fst)) := by
      intro X p hp
      rw [List.mem_singleton.mp hp]
      show (D.assign s _).find m s = _
      rw [Database.find_assign, EvalEnv.assignHole_holes_self]
    have hM : (q₀.evaluate d γ E).map (fun r => GenRow.plainTuple r.fst)
        = q₀.stripAgg.evaluatePlain D γ :=
      AggQueryIn.evaluate_toPlain_env q₀ hq.1 hh.2.2.1 hwk.1 d E D N hE hD
        (fun s' h => (hN s' h).1) (fun p hp => absurd hp List.not_mem_nil) h₀
    have hbody : ∀ X : Multiset (GenRow T K m), (∀ r ∈ X, GenRow.Conforms κ' r.fst) →
        q₁.AnnSettlesAt d γ (E.assignHole s X) →
        (q₁.evaluate d γ (E.assignHole s X)).map (fun r => GenRow.plainTuple r.fst)
          = q₁.stripAgg.evaluatePlain
              (D.assign s (X.map (fun r : GenRow T K m => GenRow.plainTuple r.fst))) γ :=
      fun X hX hX' => AggQueryIn.evaluate_toPlain_env q₁ hq.2 hh.2.2.2 hwk.2 d _ _ (insert s N)
        (hE.assignHole s hX) (Database.agree_assign hD s _) hnom (hholes X) hX'
    have hcorr : ∀ k, ((AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E)).map
          (fun r => GenRow.plainTuple r.fst)
        = (fun X : Multiset (Tuple T m) => q₁.stripAgg.evaluatePlain (D.assign s X) γ)^[k]
            (q₀.stripAgg.evaluatePlain D γ) := by
      intro k
      induction k with
      | zero => exact hM
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        exact hbody _ (hit k) (hk k)
    have hcast : ∀ {X Y : Relation T m}, X = Y →
        q₁.stripAgg.SettlesAt (D.assign s X) γ → q₁.stripAgg.SettlesAt (D.assign s Y) γ :=
      fun h => h ▸ id
    rw [AggQueryIn.stripAgg]
    refine ⟨ih₀ hq.1 hh.2.2.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
      (fun p hp => absurd hp List.not_mem_nil) h₀, ?_, ?_, fun k => ?_⟩
    · have h := hbody 0 (fun r hr => absurd hr (Multiset.notMem_zero r)) h0
      have hz' : q₁.evaluate d γ (E.assignHole s (0 : Multiset (GenRow T K m))) = 0 := hz
      rw [hz', Multiset.map_zero] at h
      exact h.symm
    · obtain ⟨k, hk'⟩ := hs
      refine ⟨k, ?_⟩
      have := hcorr (k + 1)
      rw [hk', Multiset.map_zero] at this
      exact this.symm
    · exact hcast (hcorr k) (ih₁ hq.2 hh.2.2.2 hwk.2 d γ _ _ (insert s N)
        (hE.assignHole s (hit k)) (Database.agree_assign hD s _) hnom (hholes _) (hk k))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    obtain ⟨h₀, hs, hk⟩ := hr
    have hnom : ∀ s' ∈ insert s N, q₁.noMention s' := fun s' h =>
      (Set.mem_insert_iff.mp h).elim (fun he => he ▸ hh.2.1) (fun hn => (hN s' hn).2)
    have hholes : ∀ X : AnnotatedRelation T K m, ∀ p ∈ [(s, m)], (D.assign s X.toPlain).find p.2 p.1
        = some (((E.assignHole s (X.map GenRow.ofAnnotated)).holes p.1 p.2).map
            (fun r => GenRow.plainTuple r.fst)) := by
      intro X p hp
      rw [List.mem_singleton.mp hp]
      show (D.assign s _).find m s = _
      rw [Database.find_assign, EvalEnv.assignHole_holes_self, map_plainTuple_ofAnnotated]
    have hM : (q₀.evaluateAnnotated d γ E).toPlain = q₀.stripAgg.evaluatePlain D γ := by
      unfold AggQueryIn.evaluateAnnotated AnnotatedRelation.toPlain
      rw [Multiset.map_map]
      exact AggQueryIn.evaluate_toPlain_env q₀ hq.1 hh.2.2.1 hwk.1 d E D N hE hD
        (fun s' h => (hN s' h).1) (fun p hp => absurd hp List.not_mem_nil) h₀
    have hcorr : ∀ k, AnnotatedRelation.toPlain (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)
        = muIter (fun X : Multiset (Tuple T m) => (q₀.stripAgg.evaluatePlain D γ
            + q₁.stripAgg.evaluatePlain (D.assign s X) γ).dedup) k := by
      intro k
      induction k with
      | zero => exact AnnotatedRelation.toPlain_zero
      | succ k ih =>
        show AnnotatedRelation.toPlain (AggQueryIn.muSetStep s q₀ q₁ d γ E
          (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)) = _
        rw [muIter, ← ih]
        show Multiset.map Prod.fst (AnnotatedRelation.dedupAnn (_ + _)) = _
        rw [AnnotatedRelation.dedupAnn, map_fst_groupByKey, Multiset.map_add]
        have h₁ : (q₁.evaluateAnnotated d γ (E.assignHole s
              ((muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k).map GenRow.ofAnnotated))).toPlain
            = q₁.stripAgg.evaluatePlain (D.assign s
                (AnnotatedRelation.toPlain (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k))) γ := by
          unfold AggQueryIn.evaluateAnnotated
          unfold AnnotatedRelation.toPlain
          rw [Multiset.map_map]
          exact AggQueryIn.evaluate_toPlain_env q₁ hq.2 hh.2.2.2 hwk.2 d _ _ (insert s N)
            (hE.assignHole s (conforms_ofAnnotated _)) (Database.agree_assign hD s _) hnom
            (hholes _) (hk k)
        exact congrArg Multiset.dedup (congrArg₂ (· + ·) hM h₁)
    have hcast : ∀ {X Y : Relation T m}, X = Y →
        q₁.stripAgg.SettlesAt (D.assign s X) γ → q₁.stripAgg.SettlesAt (D.assign s Y) γ :=
      fun h => h ▸ id
    rw [AggQueryIn.stripAgg]
    refine ⟨ih₀ hq.1 hh.2.2.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
      (fun p hp => absurd hp List.not_mem_nil) h₀, ?_, fun k => ?_⟩
    · obtain ⟨j, hj⟩ := hs
      refine ⟨j, ?_⟩
      rw [← muIter_eq_iterate, ← muIter_eq_iterate, ← hcorr, ← hcorr, muIter_eq_iterate,
        muIter_eq_iterate]
      exact congrArg AnnotatedRelation.toPlain hj
    · exact hcast (hcorr k) (ih₁ hq.2 hh.2.2.2 hwk.2 d γ _ _ (insert s N)
        (hE.assignHole s (conforms_ofAnnotated _)) (Database.agree_assign hD s _) hnom
        (hholes _) (hk k))
  | Gamma is ts fs q keep ord ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
  | GammaScalar ts fs q ord ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
  | GammaNest is his p f q ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
  | ProvSum is his t q ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
  | GammaTok is his ts fs a q keep ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2.2 d γ E D N hE hD hN hH hr
  | Win P O o w t f q hrr dist keep ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hq hh hwk.2 d γ E D N hE hD hN hH hr

/-- The closed form: settling annotated at `d` is settling plain, stripped,
at its data part. -/
theorem AggQueryIn.settlesAt_stripAgg_of_annSettlesAt {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (hq : q.noExplode) (hh : q.hygienic)
    (hwk : q.wellKinded (ColKind.allReg c) HoleKinds.empty) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (hr : q.AnnSettlesAt d γ {}) : q.stripAgg.SettlesAt d.toPlain γ :=
  AggQueryIn.settlesAt_stripAgg_of_annSettlesAt_env q hq hh hwk d γ {} d.toPlain ∅
    (EvalEnv.kinded_empty γ) (fun n' s' _ => AnnotatedDatabase.find_toPlain n' s' d)
    (fun _ h => absurd h (Set.notMem_empty _)) (fun _ hp => absurd hp List.not_mem_nil) hr

/-- **Settling plain is settling annotated, for a faithful query**: where
the plain evaluation's recursions settle on the data part of an
instance, the annotated evaluation's settle on the instance. A set
recursion is excluded by `liftFaithful`: its annotated rounds may keep
changing where its plain rounds have stopped. -/
private theorem AggQueryIn.annSettlesAt_of_settlesAt_env :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.liftFaithful → q.noExplode → q.hygienic → ∀ {ρc : Fin c → ColKind} {HK : HoleKinds},
      q.wellKinded ρc HK →
      ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (D : Database T)
        (N : Set String), E.Kinded γ ρc HK →
      (∀ (n' : ℕ) (s' : String), s' ∉ N →
        D.find n' s' = (d.find n' s').map AnnotatedRelation.toPlain) →
      (∀ s' ∈ N, q.noMention s') →
      (∀ p ∈ l, D.find p.2 p.1
        = some ((E.holes p.1 p.2).map (fun r => GenRow.plainTuple r.fst))) →
      q.SettlesAt D γ → q.AnnSettlesAt d γ E := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intros; trivial
  | Hole _ _ _ => intros; trivial
  | Param pv ρ => intros; trivial
  | Empty => intros; trivial
  | Proj ps q ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2 d γ E D N hE hD hN hH hr
  | Sel φ q hφ ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf.2 hq hh hwk.2 d γ E D N hE hD hN hH hr
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ⟨ih₁ hf.1 hq.1 hh.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
        (fun p hp => hH p (List.mem_append_left _ hp)) hr.1,
      ih₂ hf.2 hq.2 hh.2 hwk.2 d γ E D N hE hD (fun s' h => (hN s' h).2)
        (fun p hp => hH p (List.mem_append_right _ hp)) hr.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    have h₁ := ih₁ hf.1 hq.1 hh.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1) hH hr.1
    refine ⟨h₁, fun x hx => ?_⟩
    have e := AggQueryIn.evaluate_toPlain_env q₁ hq.1 hh.1 hwk.1 d E D N hE hD
      (fun s' h => (hN s' h).1) hH h₁
    rw [AggQueryIn.stripAgg_eq_of_liftFaithful q₁ hf.1] at e
    have hu : Multiset.Mem (q₁.evaluatePlain D γ) (GenRow.plainTuple x.fst) := by
      rw [← e]; exact Multiset.mem_map_of_mem _ hx
    exact ih₂ hf.2 hq.2 hh.2 hwk.2 d _ _ D N
      (hE.enter (fun k => AggQueryIn.evaluate_conform q₁ d x hx k)) hD
      (fun s' h => (hN s' h).2) (fun p hp => absurd hp List.not_mem_nil) (hr.2 _ hu)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ⟨ih₁ hf.1 hq.1 hh.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
        (fun p hp => hH p (List.mem_append_left _ hp)) hr.1,
      ih₂ hf.2 hq.2 hh.2 hwk.2 d γ E D N hE hD (fun s' h => (hN s' h).2)
        (fun p hp => hH p (List.mem_append_right _ hp)) hr.2⟩
  | Dedup q ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk d γ E D N hE hD hN hH hr
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hf => hf.elim
  | Explode k hk q ih => exact fun _ hq => hq.elim
  | Retag hk q ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk d γ E D N hE hD hN hH hr
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m κ'
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    obtain ⟨h₀, hz, hs, hk⟩ := hr
    have hA₀ := ih₀ hf.1 hq.1 hh.2.2.1 hwk.1 d γ E D N hE hD (fun s' h => (hN s' h).1)
      (fun p hp => absurd hp List.not_mem_nil) h₀
    have hM : (q₀.evaluate d γ E).map (fun r => GenRow.plainTuple r.fst)
        = q₀.evaluatePlain D γ := by
      have := AggQueryIn.evaluate_toPlain_env q₀ hq.1 hh.2.2.1 hwk.1 d E D N hE hD
        (fun s' h => (hN s' h).1) (fun p hp => absurd hp List.not_mem_nil) hA₀
      rwa [AggQueryIn.stripAgg_eq_of_liftFaithful q₀ hf.1] at this
    have hit : ∀ k, ∀ r ∈ (AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E),
        GenRow.Conforms κ' r.fst := by
      intro k
      induction k with
      | zero => exact fun r hr' k => AggQueryIn.evaluate_conform q₀ d r hr' k
      | succ k _ =>
        intro r hr'
        rw [Function.iterate_succ_apply'] at hr'
        exact fun k => AggQueryIn.evaluate_conform q₁ d r hr' k
    have hnom : ∀ s' ∈ insert s N, q₁.noMention s' := fun s' h =>
      (Set.mem_insert_iff.mp h).elim (fun he => he ▸ hh.2.1) (fun hn => (hN s' hn).2)
    have hholes : ∀ X : Multiset (GenRow T K m), ∀ p ∈ [(s, m)], (D.assign s
        (X.map (fun r : GenRow T K m => GenRow.plainTuple r.fst))).find p.2 p.1
        = some (((E.assignHole s X).holes p.1 p.2).map (fun r => GenRow.plainTuple r.fst)) := by
      intro X p hp
      rw [List.mem_singleton.mp hp]
      show (D.assign s _).find m s = _
      rw [Database.find_assign, EvalEnv.assignHole_holes_self]
    have hbodyA : ∀ X : Multiset (GenRow T K m), (∀ r ∈ X, GenRow.Conforms κ' r.fst) →
        q₁.SettlesAt (D.assign s (X.map (fun r : GenRow T K m => GenRow.plainTuple r.fst))) γ →
        q₁.AnnSettlesAt d γ (E.assignHole s X) :=
      fun X hX hP => ih₁ hf.2 hq.2 hh.2.2.2 hwk.2 d γ _ _ (insert s N) (hE.assignHole s hX)
        (Database.agree_assign hD s _) hnom (hholes X) hP
    have hbodyE : ∀ X : Multiset (GenRow T K m), (∀ r ∈ X, GenRow.Conforms κ' r.fst) →
        q₁.AnnSettlesAt d γ (E.assignHole s X) →
        (q₁.evaluate d γ (E.assignHole s X)).map (fun r => GenRow.plainTuple r.fst)
          = q₁.evaluatePlain
              (D.assign s (X.map (fun r : GenRow T K m => GenRow.plainTuple r.fst))) γ := by
      intro X hX hX'
      have := AggQueryIn.evaluate_toPlain_env q₁ hq.2 hh.2.2.2 hwk.2 d _ _ (insert s N)
        (hE.assignHole s hX) (Database.agree_assign hD s _) hnom (hholes X) hX'
      rwa [AggQueryIn.stripAgg_eq_of_liftFaithful q₁ hf.2] at this
    have hcast : ∀ {X Y : Relation T m}, X = Y →
        q₁.SettlesAt (D.assign s X) γ → q₁.SettlesAt (D.assign s Y) γ := fun h => h ▸ id
    -- the rounds correspond, and the body settles annotated at each
    have hrounds : ∀ k,
        ((AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E)).map
            (fun r => GenRow.plainTuple r.fst)
            = (fun X : Multiset (Tuple T m) => q₁.evaluatePlain (D.assign s X) γ)^[k]
                (q₀.evaluatePlain D γ)
          ∧ q₁.AnnSettlesAt d γ (E.assignHole s
              ((AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E))) := by
      intro k
      induction k with
      | zero => exact ⟨hM, hbodyA _ (hit 0) (hcast hM.symm (hk 0))⟩
      | succ k ih =>
        have hstep : ((AggQueryIn.muStep s q₁ d γ E)^[k + 1] (q₀.evaluate d γ E)).map
              (fun r => GenRow.plainTuple r.fst)
            = (fun X : Multiset (Tuple T m) => q₁.evaluatePlain (D.assign s X) γ)^[k + 1]
                (q₀.evaluatePlain D γ) := by
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih.1]
          exact hbodyE _ (hit k) ih.2
        exact ⟨hstep, hbodyA _ (hit (k + 1)) (hcast hstep.symm (hk (k + 1)))⟩
    -- the body settles annotated at the empty round
    have hb0 : q₁.AnnSettlesAt d γ (E.assignHole s (0 : Multiset (GenRow T K m))) :=
      hbodyA 0 (fun r hr => absurd hr (Multiset.notMem_zero r)) (hcast (Multiset.map_zero _).symm
        (AggQueryIn.settlesAt_assign_zero_of_body q₁ rfl hh.2.1 D γ _ (hk 0)))
    refine ⟨hA₀, ?_, ?_, fun k => (hrounds k).2, hb0⟩
    · have h := hbodyE 0 (fun r hr => absurd hr (Multiset.notMem_zero r)) hb0
      rw [Multiset.map_zero] at h
      show q₁.evaluate d γ (E.assignHole s (0 : Multiset (GenRow T K m))) = 0
      rw [← Multiset.map_eq_zero (f := fun r : GenRow T K m => GenRow.plainTuple r.fst), h]
      exact hz
    · obtain ⟨k, hk'⟩ := hs
      refine ⟨k, ?_⟩
      rw [← Multiset.map_eq_zero (f := fun r : GenRow T K m => GenRow.plainTuple r.fst),
        (hrounds (k + 1)).1]
      exact hk'
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hf => hf.elim
  | Gamma is ts fs q keep ord ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2 d γ E D N hE hD hN hH hr
  | GammaScalar ts fs q ord ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2 d γ E D N hE hD hN hH hr
  | GammaNest is his p f q ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2 d γ E D N hE hD hN hH hr
  | ProvSum is his t q ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2 d γ E D N hE hD hN hH hr
  | GammaTok is his ts fs a q keep ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2.2 d γ E D N hE hD hN hH hr
  | Win P O o w t f q hrr dist keep ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2 d γ E D N hE hD hN hH hr
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hf hq hh ρc HK hwk d γ E D N hE hD hN hH hr
    exact ih hf hq hh hwk.2 d γ E D N hE hD hN hH hr

/-- The closed form. -/
theorem AggQueryIn.annSettlesAt_of_settlesAt {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (hf : q.liftFaithful) (hq : q.noExplode) (hh : q.hygienic)
    (hwk : q.wellKinded (ColKind.allReg c) HoleKinds.empty) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (hr : q.SettlesAt d.toPlain γ) : q.AnnSettlesAt d γ {} :=
  AggQueryIn.annSettlesAt_of_settlesAt_env q hf hq hh hwk d γ {} d.toPlain ∅
    (EvalEnv.kinded_empty γ) (fun n' s' _ => AnnotatedDatabase.find_toPlain n' s' d)
    (fun _ h => absurd h (Set.notMem_empty _)) (fun _ hp => absurd hp List.not_mem_nil) hr

/-! ## The generation of the annotated algebra -/

/-- **A set of classes generates the annotated algebra over `K`**: every
query of the whole algebra in the minimal universe, over the schema,
well-kinded and reading no aggregate column as a key, is matched by a
well-kinded query over the classes, of the same kinds, reading none either, whose
annotated evaluation settles and agrees with the query's on every
`K`-instance at which the query's does. The equality is of the bags of
annotated tuples (`AggQueryIn.evaluateAnnotated`), finer than
equality up to rows annotated `𝟘`. -/
def GeneratesAnn (T : Type) [ValueType T] (K : Type) [CommSemiringWithMonus K] [DecidableEq K]
    [HasAltLinearOrder K] (sch : Schema) (cnt : SeqAggFunc T) (S : Set OpKind) : Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ),
    q.overSchema sch → q.usesOnly plainRecOps → q.inMinimalSig cnt → q.noExplode →
      q.wellKinded (ColKind.allReg 0) HoleKinds.empty →
      ∃ q' : AggQuery T n κ,
        q'.overSchema sch ∧ q'.usesOnly S ∧ q'.inMinimalSig cnt ∧ q'.noExplode
          ∧ q'.wellKinded (ColKind.allReg 0) HoleKinds.empty
          ∧ ∀ (d : AnnotatedDatabase T K) (γ : Fin 0 → T), q.AnnSettlesAt d γ {} →
              q'.AnnSettlesAt d γ {} ∧ q'.evaluateAnnotated d γ = q.evaluateAnnotated d γ

/-- Every class generates, trivially: the query is its own match. -/
theorem generatesAnn_plainRecOps (sch : Schema) (cnt : SeqAggFunc T) :
    GeneratesAnn T K sch cnt plainRecOps :=
  fun q ho hu hi ha hp => ⟨q, ho, hu, hi, ha, hp, fun _ _ hs => ⟨hs, rfl⟩⟩

theorem GeneratesAnn.mono {sch : Schema} {cnt : SeqAggFunc T} {S S' : Set OpKind}
    (hSS : S ⊆ S') (h : GeneratesAnn T K sch cnt S) : GeneratesAnn T K sch cnt S' := by
  intro n κ q ho hu hi ha hp
  obtain ⟨q', h₁, h₂, h₃, h₄, h₅, h₆⟩ := h q ho hu hi ha hp
  exact ⟨q', h₁, AggQueryIn.usesOnly_mono hSS q' h₂, h₃, h₄, h₅, h₆⟩

private theorem GeneratesAtNoExplode.toGeneratesAt {sch : Schema} {cnt : SeqAggFunc T} {S : Set OpKind}
    {n : ℕ} {κ : Fin n → ColKind} {q : AggQuery T n κ} (h : GeneratesAtNoExplode T sch cnt S q) :
    GeneratesAt T sch cnt S q := by
  intro ho hu hi
  obtain ⟨κ', q', h₁, h₂, h₃, -, -, h₅⟩ := h ho hu hi
  exact ⟨κ', q', h₁, h₂, h₃, h₅⟩

/-- **The transfer to the plain semantics**: a set generating the annotated
algebra over `K` generates, plainly and without reading aggregate columns
as keys, every faithful query – the matching query, stripped of its
aggregate selections and differences, reads a plain instance annotated
`𝟙` as the query does, on the data part. -/
theorem generatesAtNoExplode_of_generatesAnn {sch : Schema} {cnt : SeqAggFunc T} {S : Set OpKind}
    (h : GeneratesAnn T K sch cnt S) {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ)
    (hf : q.liftFaithful) (ha : q.noExplode)
    (hwk : q.wellKinded (ColKind.allReg 0) HoleKinds.empty) :
    GeneratesAtNoExplode T sch cnt S q := by
  intro ho hu hi
  obtain ⟨q', ho', hu', hi', ha', hwk', he⟩ := h q ho hu hi ha hwk
  have hh := q.hygienic_of_overSchema _ ho
  have hh' := q'.hygienic_of_overSchema _ ho'
  refine ⟨κ, q'.stripAgg, AggQueryIn.overSchema_stripAgg q' ho',
    AggQueryIn.usesOnly_stripAgg q' hu', AggQueryIn.inSig_stripAgg q' hi',
    AggQueryIn.noExplode_stripAgg q' ha',
    AggQueryIn.wellKinded_stripAgg q' hwk', AggQueryIn.Extends.of_settles (fun D γ hD => ?_)⟩
  have hann : q.AnnSettlesAt (D.liftOne (K := K)) γ {} :=
    AggQueryIn.annSettlesAt_of_settlesAt q hf ha hh hwk _ γ
      (by rw [Database.toPlain_liftOne]; exact hD)
  obtain ⟨hs', heq⟩ := he _ γ hann
  refine ⟨?_, ?_⟩
  · have := AggQueryIn.settlesAt_stripAgg_of_annSettlesAt q' ha' hh' hwk' _ γ hs'
    rwa [Database.toPlain_liftOne] at this
  · have h1 := AggQueryIn.evaluateAnnotated_toPlain q' ha' hh' hwk' (D.liftOne (K := K)) hs'
    have h2 := AggQueryIn.evaluateAnnotated_toPlain q ha hh hwk (D.liftOne (K := K)) hann
    rw [Database.toPlain_liftOne] at h1 h2
    rw [AggQueryIn.stripAgg_eq_of_liftFaithful q hf] at h2
    rw [← h2, ← h1, heq]

/-! ## The witnesses are faithful -/

omit [ValueType T] in
private theorem AggQueryIn.liftFaithful_unit : (AggQueryIn.unit : AggQuery T 0 _).liftFaithful := by
  rw [AggQueryIn.unit, AggQueryIn.liftFaithful_castKind]; exact trivial

omit [ValueType T] in
private theorem AggQueryIn.noExplode_unit : (AggQueryIn.unit : AggQuery T 0 _).noExplode := by
  rw [AggQueryIn.unit, AggQueryIn.noExplode_castKind]; exact trivial

omit [ValueType T] in
private theorem AggQueryIn.wellKinded_unit :
    (AggQueryIn.unit : AggQuery T 0 _).wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  rw [AggQueryIn.unit, AggQueryIn.wellKinded_castKind]; exact ⟨fun j => j.elim0, trivial⟩

private theorem liftFaithful_selWitness : selWitness.liftFaithful := ⟨rfl, trivial⟩
private theorem noExplode_selWitness : selWitness.noExplode := trivial
private theorem wellKinded_selWitness : selWitness.wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  simp [selWitness, AggQueryIn.wellKinded, GenPredIn.outerOk, TermGIn.outerOk]
private theorem liftFaithful_projWitness : projWitness.liftFaithful := trivial
private theorem noExplode_projWitness : projWitness.noExplode := trivial
private theorem wellKinded_projWitness : projWitness.wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  simp [projWitness, AggQueryIn.wellKinded, TermGIn.outerOk, ProjColIn.outerOk]
private theorem liftFaithful_prodWitness : prodWitness.liftFaithful := ⟨trivial, trivial⟩
private theorem noExplode_prodWitness : prodWitness.noExplode := ⟨trivial, trivial⟩
private theorem wellKinded_prodWitness : prodWitness.wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  simp [prodWitness, AggQueryIn.wellKinded]
private theorem liftFaithful_chainWitness : chainWitness.liftFaithful := by
  simp [chainWitness, reachStep, AggQueryIn.liftFaithful, GenPredIn.hasAggAtom]
private theorem noExplode_chainWitness : chainWitness.noExplode := by
  simp [chainWitness, reachStep, AggQueryIn.noExplode]
private theorem wellKinded_chainWitness : chainWitness.wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  simp [chainWitness, reachStep, HoleKinds.assign, AggQueryIn.wellKinded, GenPredIn.outerOk,
      TermGIn.outerOk, ProjColIn.outerOk]
private theorem liftFaithful_winWitness : WinRow.winWitness.liftFaithful := trivial
private theorem noExplode_winWitness : WinRow.winWitness.noExplode := trivial
private theorem wellKinded_winWitness : WinRow.winWitness.wellKinded
    (ColKind.allReg 0) HoleKinds.empty := by
  simp [WinRow.winWitness, AggQueryIn.wellKinded, TermIn.outerOk]
private theorem liftFaithful_ltWitness : ltWitness.liftFaithful := ⟨rfl, trivial⟩
private theorem noExplode_ltWitness : ltWitness.noExplode := trivial
private theorem wellKinded_ltWitness : ltWitness.wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  simp [ltWitness, AggQueryIn.wellKinded, GenPredIn.outerOk, TermGIn.outerOk]

/-! ## The inherited rows -/

/-- `∅` is in every set generating the annotated algebra over the empty schema. -/
private theorem empty_mem_of_generatesAnn {cnt : SeqAggFunc T} {S : Set OpKind}
    (h : GeneratesAnn T K Schema.empty cnt S) : OpKind.empty ∈ S :=
  empty_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnn h _
    AggQueryIn.liftFaithful_unit AggQueryIn.noExplode_unit AggQueryIn.wellKinded_unit).toGeneratesAt

/-- `γ` is in every set generating the annotated algebra. -/
private theorem gamma_mem_of_generatesAnn {sch : Schema} {cnt : SeqAggFunc T} {S : Set OpKind}
    (h : GeneratesAnn T K sch cnt S) : OpKind.gamma ∈ S :=
  gamma_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnn h _
    AggQueryIn.liftFaithful_unit AggQueryIn.noExplode_unit AggQueryIn.wellKinded_unit).toGeneratesAt

/-- `Π` is in every set generating the annotated algebra over `ℕ`. -/
private theorem proj_mem_of_generatesAnn {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnn ℕ K schemaS cnt S) : OpKind.proj ∈ S :=
  proj_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnn h _
    liftFaithful_projWitness noExplode_projWitness wellKinded_projWitness).toGeneratesAt

/-- `×` or the apply is in every set generating the annotated algebra over `ℕ`. -/
private theorem prod_or_apply_mem_of_generatesAnn {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnn ℕ K schemaR cnt S) : OpKind.prod ∈ S ∨ OpKind.apply ∈ S :=
  prod_or_apply_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnn h _
    liftFaithful_prodWitness noExplode_prodWitness wellKinded_prodWitness).toGeneratesAt

/-- `μ^⊎` is in every set generating the annotated algebra over `ℕ`. -/
private theorem muBag_mem_of_generatesAnn {cnt : SeqAggFunc ℕ} (hcnt : cnt.ReadsCount) {S : Set OpKind}
    (h : GeneratesAnn ℕ K schemaSE cnt S) : OpKind.muBag ∈ S :=
  muBag_mem_of_generatesAt hcnt (generatesAtNoExplode_of_generatesAnn h _
    liftFaithful_chainWitness noExplode_chainWitness wellKinded_chainWitness).toGeneratesAt

/-- `win` is in every set generating the annotated algebra over `ℕ` with
the counting aggregate. -/
private theorem win_mem_of_generatesAnn {S : Set OpKind}
    (h : GeneratesAnn ℕ K schemaR SeqAggFunc.count S) : OpKind.win ∈ S :=
  win_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnn h _
    liftFaithful_winWitness noExplode_winWitness wellKinded_winWitness).toGeneratesAt

/-- **`σ` is in every set generating the annotated algebra over `ℕ`**: the
alternatives being out of the language, the selection row holds outright,
with no difference to trade it for. -/
private theorem sel_mem_of_generatesAnn {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnn ℕ K schemaS cnt S) : OpKind.sel ∈ S :=
  sel_mem_of_generatesAtNoExplode (generatesAtNoExplode_of_generatesAnn h _
    liftFaithful_ltWitness noExplode_ltWitness wellKinded_ltWitness)

/-- **What every set generating the annotated algebra contains**, over
`ℕ` with the counting aggregate and over every commutative m-semiring:
`∅`, `Π`, `γ`, `μ^⊎`, `win`, `σ`, and one of `×` and the apply – the
plain rows, inherited through the data part, with the selection row no
longer a disjunction. -/
theorem required_mem_of_generatesAnn {S : Set OpKind}
    (h : ∀ sch : Schema, GeneratesAnn ℕ K sch SeqAggFunc.count S) :
    OpKind.empty ∈ S ∧ OpKind.proj ∈ S ∧ OpKind.gamma ∈ S ∧ OpKind.muBag ∈ S
      ∧ OpKind.win ∈ S ∧ OpKind.sel ∈ S ∧ (OpKind.prod ∈ S ∨ OpKind.apply ∈ S) :=
  ⟨empty_mem_of_generatesAnn (h _), proj_mem_of_generatesAnn (h _),
    gamma_mem_of_generatesAnn (h Schema.empty),
    muBag_mem_of_generatesAnn SeqAggFunc.isCount_count_nat.readsCount (h _),
    win_mem_of_generatesAnn (h _), sel_mem_of_generatesAnn (h _),
    prod_or_apply_mem_of_generatesAnn (h _)⟩
