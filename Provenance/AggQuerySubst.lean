/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQuery

/-!
# Substituting the outer columns

The apply is defined by *substitution*: the right side of `q₁ ⋈ᴬ q₂` is
read, for each row `u` of the left, as the closed query `q₂[u]`. The
evaluators of `Provenance.AggQuery` read it under an outer *valuation*
instead, which is what makes them structurally recursive. This module
defines the substitution and proves the two readings agree, so that the
`q₂[u]` form is available as a theorem
(`AggQueryIn.evaluate_Apply_subst`).

`substMap` sends each outer position either to a value or to an outer
position of the target context. That generality is what the `Apply` case
of the recursion needs: the right side of an apply reads its left
neighbour's columns *and* the ambient outer ones, and closing the
ambient part must leave the neighbour's alone. Closing everything is the
special case `subst`.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## The valuation a substitution induces -/

/-- Reading the source context through a substitution: an outer position
sent to a value reads that value, one sent to an outer position of the
target reads the target's valuation there. -/
def substVal {c d : ℕ} (θ : Fin c → T ⊕ Fin d) (γ : Fin d → T) : Fin c → T :=
  fun k => Sum.elim id γ (θ k)

omit [ValueType T] in
/-- Closing a context reads the values it is closed with. -/
@[simp] theorem substVal_inl {c : ℕ} (u : Fin c → T) (γ : Fin 0 → T) :
    substVal (fun k => Sum.inl (u k)) γ = u := rfl

/-! ## Substitution on terms, predicates and projection columns -/

/-- Substitute the outer columns of a term. -/
def TermIn.substMap {c d n : ℕ} (θ : Fin c → T ⊕ Fin d) :
    TermIn T c n → TermIn T d n
  | .const a => .const a
  | .outer k => Sum.elim .const .outer (θ k)
  | .index k => .index k
  | .add t₁ t₂ => .add (t₁.substMap θ) (t₂.substMap θ)
  | .sub t₁ t₂ => .sub (t₁.substMap θ) (t₂.substMap θ)
  | .mul t₁ t₂ => .mul (t₁.substMap θ) (t₂.substMap θ)
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    .caseWhen op (t₁.substMap θ) (t₂.substMap θ) (t₃.substMap θ)
      (t₄.substMap θ)
  | .coalesce t₁ t₂ => .coalesce (t₁.substMap θ) (t₂.substMap θ)

omit [ValueType T] in
/-- Substituting the outer columns reads no column of the row, so what a
term reads of them is unchanged – which is what a window's
`WinReadsReg` asks of its term. -/
@[simp] theorem TermIn.regOnly_substMap {c d n : ℕ} (θ : Fin c → T ⊕ Fin d)
    (κ : Fin n → ColKind) (t : TermIn T c n) :
    (t.substMap θ).regOnly κ = t.regOnly κ := by
  induction t with
  | const a => rfl
  | outer k =>
    show (Sum.elim TermIn.const TermIn.outer (θ k)).regOnly κ = true
    cases θ k with
    | inl a => rfl
    | inr j => rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermIn.substMap, TermIn.regOnly, ih₁, ih₂]; rfl
  | sub t₁ t₂ ih₁ ih₂ => rw [TermIn.substMap, TermIn.regOnly, ih₁, ih₂]; rfl
  | mul t₁ t₂ ih₁ ih₂ => rw [TermIn.substMap, TermIn.regOnly, ih₁, ih₂]; rfl
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    rw [TermIn.substMap, TermIn.regOnly, ih₁, ih₂, ih₃, ih₄]; rfl
  | coalesce t₁ t₂ ih₁ ih₂ => rw [TermIn.substMap, TermIn.regOnly, ih₁, ih₂]; rfl

theorem TermIn.eval_substMap {c d n : ℕ} (θ : Fin c → T ⊕ Fin d)
    (t : TermIn T c n) (u : Tuple T n) (γ : Fin d → T) :
    (t.substMap θ).eval u γ = t.eval u (substVal θ γ) := by
  induction t with
  | const a => rfl
  | outer k =>
    show (Sum.elim TermIn.const TermIn.outer (θ k)).eval u γ = substVal θ γ k
    unfold substVal
    cases θ k <;> rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ => show _ + _ = _ + _; rw [ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => show HSub.hSub _ _ = HSub.hSub _ _; rw [ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => show _ * _ = _ * _; rw [ih₁, ih₂]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

/-- Substitute the outer columns of a generalized term. -/
def TermGIn.substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) : TermGIn T c κ → TermGIn T d κ
  | .const a => .const a
  | .outer k => Sum.elim .const .outer (θ k)
  | .index k h => .index k h
  | .provIndex k h => .provIndex k h
  | .cmpAgg k h op t => .cmpAgg k h op (t.substMap θ)
  | .chiGate op t₁ t₂ => .chiGate op (t₁.substMap θ) (t₂.substMap θ)
  | .add t₁ t₂ => .add (t₁.substMap θ) (t₂.substMap θ)
  | .sub t₁ t₂ => .sub (t₁.substMap θ) (t₂.substMap θ)
  | .mul t₁ t₂ => .mul (t₁.substMap θ) (t₂.substMap θ)
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    .caseWhen op (t₁.substMap θ) (t₂.substMap θ) (t₃.substMap θ)
      (t₄.substMap θ)
  | .coalesce t₁ t₂ => .coalesce (t₁.substMap θ) (t₂.substMap θ)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem TermGIn.eval_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (t : TermGIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin d → T) :
    (t.substMap θ).eval u γ = t.eval u (substVal θ γ) := by
  induction t with
  | const a => rfl
  | outer k =>
    show (Sum.elim TermGIn.const TermGIn.outer (θ k)).eval u γ = substVal θ γ k
    unfold substVal
    cases θ k <;> rfl
  | index k h => rfl
  | provIndex k h => rfl
  | cmpAgg k h op t ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ => show _ + _ = _ + _; rw [ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => show HSub.hSub _ _ = HSub.hSub _ _; rw [ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => show _ * _ = _ * _; rw [ih₁, ih₂]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

theorem TermGIn.evalPlain_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (t : TermGIn T c κ) (u : Tuple T n)
    (γ : Fin d → T) :
    (t.substMap θ).evalPlain u γ = t.evalPlain u (substVal θ γ) := by
  induction t with
  | const a => rfl
  | outer k =>
    show (Sum.elim TermGIn.const TermGIn.outer (θ k)).evalPlain u γ
      = substVal θ γ k
    unfold substVal
    cases θ k <;> rfl
  | index k h => rfl
  | provIndex k h => rfl
  | cmpAgg k h op t ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ => show _ + _ = _ + _; rw [ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => show HSub.hSub _ _ = HSub.hSub _ _; rw [ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => show _ * _ = _ * _; rw [ih₁, ih₂]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

/-- Substitute the outer columns of a generalized predicate. -/
def GenPredIn.substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) : GenPredIn T c κ → GenPredIn T d κ
  | .cmp op t₁ t₂ => .cmp op (t₁.substMap θ) (t₂.substMap θ)
  | .aggCmp k h op t => .aggCmp k h op (t.substMap θ)
  | .aggRange k h op₁ t₁ op₂ t₂ =>
      .aggRange k h op₁ (t₁.substMap θ) op₂ (t₂.substMap θ)
  | .and φ ψ => .and (φ.substMap θ) (ψ.substMap θ)
  | .or φ ψ => .or (φ.substMap θ) (ψ.substMap θ)
  | .not φ => .not (φ.substMap θ)

omit [ValueType T] in
@[simp] theorem GenPredIn.hasAggAtom_substMap {c d n : ℕ}
    {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ) :
    (φ.substMap θ).hasAggAtom = φ.hasAggAtom := by
  induction φ with
  | cmp op t₁ t₂ => rfl
  | aggCmp k h op t => rfl
  | aggRange k h op₁ t₁ op₂ t₂ => rfl
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.substMap, GenPredIn.hasAggAtom, ihφ, ihψ]
  | not φ ih => exact ih

omit [ValueType T] in
@[simp] theorem GenPredIn.comparedCols_substMap {c d n : ℕ}
    {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ) :
    (φ.substMap θ).comparedCols = φ.comparedCols := by
  induction φ with
  | cmp op t₁ t₂ => rfl
  | aggCmp k h op t => rfl
  | aggRange k h op₁ t₁ op₂ t₂ => rfl
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.substMap, GenPredIn.comparedCols, ihφ, ihψ]
  | not φ ih => exact ih

omit [ValueType T] in
@[simp] theorem GenPredIn.entailsExistence_substMap {c d n : ℕ}
    {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ)
    (neg : Bool) :
    (φ.substMap θ).entailsExistence neg = φ.entailsExistence neg := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ => rfl
  | aggCmp k h op t => rfl
  | aggRange k h op₁ t₁ op₂ t₂ => rfl
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.substMap, GenPredIn.entailsExistence, ihφ, ihψ]
  | not φ ih => exact ih (!neg)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenPredIn.eval3_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin d → T) :
    (φ.substMap θ).eval3 u γ = φ.eval3 u (substVal θ γ) := by
  induction φ with
  | cmp op t₁ t₂ =>
    show op.eval3 _ _ = op.eval3 _ _
    rw [TermGIn.eval_substMap, TermGIn.eval_substMap]
  | aggCmp k h op t =>
    show op.eval3 _ _ = op.eval3 _ _
    rw [TermGIn.eval_substMap]
  | aggRange k h op₁ t₁ op₂ t₂ =>
    show Kleene.and _ _ = Kleene.and _ _
    rw [TermGIn.eval_substMap, TermGIn.eval_substMap]
  | and φ ψ ihφ ihψ => show Kleene.and _ _ = Kleene.and _ _; rw [ihφ, ihψ]
  | or φ ψ ihφ ihψ => show Kleene.or _ _ = Kleene.or _ _; rw [ihφ, ihψ]
  | not φ ih => show Kleene.not _ = Kleene.not _; rw [ih]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenPredIn.holds_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin d → T) :
    (φ.substMap θ).holds u γ ↔ φ.holds u (substVal θ γ) := by
  unfold GenPredIn.holds
  rw [GenPredIn.eval3_substMap]

theorem GenPredIn.evalPlain3_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ) (u : Tuple T n)
    (γ : Fin d → T) :
    (φ.substMap θ).evalPlain3 u γ = φ.evalPlain3 u (substVal θ γ) := by
  induction φ with
  | cmp op t₁ t₂ =>
    show op.eval3 _ _ = op.eval3 _ _
    rw [TermGIn.evalPlain_substMap, TermGIn.evalPlain_substMap]
  | aggCmp k h op t =>
    show op.eval3 _ _ = op.eval3 _ _
    rw [TermGIn.evalPlain_substMap]
  | aggRange k h op₁ t₁ op₂ t₂ =>
    show Kleene.and _ _ = Kleene.and _ _
    rw [TermGIn.evalPlain_substMap, TermGIn.evalPlain_substMap]
  | and φ ψ ihφ ihψ => show Kleene.and _ _ = Kleene.and _ _; rw [ihφ, ihψ]
  | or φ ψ ihφ ihψ => show Kleene.or _ _ = Kleene.or _ _; rw [ihφ, ihψ]
  | not φ ih => show Kleene.not _ = Kleene.not _; rw [ih]

theorem GenPredIn.holdsPlain_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ) (u : Tuple T n)
    (γ : Fin d → T) :
    (φ.substMap θ).holdsPlain u γ ↔ φ.holdsPlain u (substVal θ γ) := by
  unfold GenPredIn.holdsPlain
  rw [GenPredIn.evalPlain3_substMap]

omit [HasAltLinearOrder K] in
theorem GenPredIn.predsem_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ) (neg : Bool)
    (u : Tuple (GenValue T K) n) (γ : Fin d → T) :
    (φ.substMap θ).predsem neg u γ = φ.predsem neg u (substVal θ γ) := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ =>
    show Having.chi _ _ _ = Having.chi _ _ _
    rw [TermGIn.eval_substMap, TermGIn.eval_substMap]
  | aggCmp k h op t =>
    simp only [GenPredIn.substMap, GenPredIn.predsem, TermGIn.eval_substMap]
  | aggRange k h op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.substMap, GenPredIn.predsem, TermGIn.eval_substMap]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.substMap, GenPredIn.predsem, ihφ, ihψ]
  | not φ ih => exact ih (!neg)

/-- Substitute the outer columns of a projection column. -/
def ProjColIn.substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) : ProjColIn T c κ → ProjColIn T d κ
  | .term t => .term (t.substMap θ)
  | .token k h => .token k h
  | .aggTerm k h gf => .aggTerm k h gf
  | .aggTermOf k h gf => .aggTermOf k h gf
  | .provTerm t => .provTerm (t.substMap θ)

omit [ValueType T] in
/-- The substitution does not change an output column's kind. -/
@[simp] theorem ProjColIn.kind_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (p : ProjColIn T c κ) :
    (p.substMap θ).kind = p.kind := by
  cases p <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- The substitution does not turn a source column into the rewritten
world's. -/
@[simp] theorem ProjColIn.sourceCol_substMap {c d n : ℕ}
    {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d) (p : ProjColIn T c κ) :
    (p.substMap θ).sourceCol = p.sourceCol := by
  cases p <;> rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem ProjColIn.eval_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (p : ProjColIn T c κ)
    (u : Tuple (GenValue T K) n) (γ : Fin d → T) :
    (p.substMap θ).eval u γ = p.eval u (substVal θ γ) := by
  cases p with
  | term t => exact congrArg Sum.inl (TermGIn.eval_substMap θ t u γ)
  | token k h => rfl
  | aggTerm k h gf => rfl
  | aggTermOf k h gf => rfl
  | provTerm t => exact congrArg Sum.inl (TermGIn.eval_substMap θ t u γ)

theorem ProjColIn.evalPlain_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (p : ProjColIn T c κ) (u : Tuple T n)
    (γ : Fin d → T) :
    (p.substMap θ).evalPlain u γ = p.evalPlain u (substVal θ γ) := by
  cases p with
  | term t => exact TermGIn.evalPlain_substMap θ t u γ
  | token k h => rfl
  | aggTerm k h gf => rfl
  | aggTermOf k h gf => rfl
  | provTerm t => exact TermGIn.evalPlain_substMap θ t u γ

/-! ## Substitution on queries -/

/-- Substitute the outer columns of a query. The right side of an apply
reads its left neighbour's columns first and the ambient outer ones
after, so the substitution passes under it by leaving the neighbour's
block alone and shifting the ambient one. -/
def AggQueryIn.substMap {c d n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (θ : Fin c → T ⊕ Fin d) (q : AggQueryIn T c n κ l) : AggQueryIn T d n κ l :=
  match c, d, n, κ, l, θ, q with
  | _, _, _, _, _, _, .Rel n s => .Rel n s
  | _, _, _, _, _, _, .Hole n s => .Hole n s
  | _, _, _, _, _, _, .Empty => .Empty
  | _, _, _, _, _, θ, .Proj ps q =>
      AggQueryIn.castKind (funext fun j => ProjColIn.kind_substMap θ (ps j))
        (.Proj (fun j => (ps j).substMap θ) (q.substMap θ))
  | _, _, _, _, _, θ, .Sel φ q hφ =>
      .Sel (φ.substMap θ) (q.substMap θ) (SelOK.of_eq (GenPredIn.hasAggAtom_substMap θ φ) hφ)
  | _, _, _, _, _, θ, .Prod q₁ q₂ => .Prod (q₁.substMap θ) (q₂.substMap θ)
  | _, d, _, _, _, θ, @AggQueryIn.Apply _ _ n₁ _ _ _ _ q₁ q₂ =>
      .Apply (q₁.substMap θ)
        (q₂.substMap (Fin.append (fun k => Sum.inr (Fin.castAdd d k))
          (fun j => Sum.map id (Fin.natAdd n₁) (θ j))))
  | _, _, _, _, _, θ, .Sum q₁ q₂ => .Sum (q₁.substMap θ) (q₂.substMap θ)
  | _, _, _, _, _, θ, .Dedup q => .Dedup (q.substMap θ)
  | _, _, _, _, _, θ, .Diff q₁ q₂ => .Diff (q₁.substMap θ) (q₂.substMap θ)
  | _, _, _, _, _, θ, .Explode k h q => .Explode k h (q.substMap θ)
  | _, _, _, _, _, θ, .Mu s q₀ q₁ => .Mu s (q₀.substMap θ) (q₁.substMap θ)
  | _, _, _, _, _, θ, .MuSet s q₀ q₁ =>
      .MuSet s (q₀.substMap θ) (q₁.substMap θ)
  | _, _, _, _, _, θ, .Gamma is ts fs q keep ord =>
      .Gamma is (fun j => (ts j).substMap θ) fs (q.substMap θ) keep ord
  | _, _, _, _, _, θ, .GammaScalar ts fs q ord =>
      .GammaScalar (fun j => (ts j).substMap θ) fs (q.substMap θ) ord
  | _, _, _, _, _, θ, .GammaNest is his p f q =>
      .GammaNest is his (p.substMap θ) f (q.substMap θ)
  | _, _, _, _, _, θ, .ProvSum is his t q =>
      .ProvSum is his (t.substMap θ) (q.substMap θ)
  | _, _, _, _, _, θ, .Retag h q => .Retag h (q.substMap θ)
  | _, _, _, _, _, θ, .GammaTok is his ts fs a q keep =>
      .GammaTok is his (fun j => (ts j).substMap θ) fs (a.substMap θ)
        (q.substMap θ) keep
  | _, _, _, _, _, θ, .Win P O o w t f q hrr dist keep =>
      .Win P O o w (t.substMap θ) f (q.substMap θ)
        ⟨hrr.1, hrr.2.1, by rw [TermIn.regOnly_substMap]; exact hrr.2.2⟩
        dist keep
  | _, _, _, _, _, θ, .WinExpr P O o ws ts fs g q keeps =>
      .WinExpr P O o ws (fun l => (ts l).substMap θ) fs g (q.substMap θ) keeps
termination_by structural q

/-- Close a query: give every outer column a value, written `q[u]`. -/
abbrev AggQueryIn.subst {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (u : Fin c → T)
    (q : AggQueryIn T c n κ l) : AggQueryIn T 0 n κ l :=
  q.substMap (fun k => Sum.inl (u k))

omit [ValueType T] in
/-- Passing a substitution under an apply: the valuation the shifted
substitution induces on the right side is the left row followed by the
substituted ambient valuation. -/
theorem substVal_append {c d n₁ : ℕ} (θ : Fin c → T ⊕ Fin d)
    (v : Fin n₁ → T) (γ : Fin d → T) :
    substVal (Fin.append (fun k => Sum.inr (Fin.castAdd d k))
        (fun j => Sum.map id (Fin.natAdd n₁) (θ j))) (Fin.append v γ)
      = Fin.append v (substVal θ γ) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · show Sum.elim id (Fin.append v γ)
      (Fin.append (fun k => Sum.inr (Fin.castAdd d k)) _ (Fin.castAdd c i))
      = _
    rw [Fin.append_left, Fin.append_left]
    exact Fin.append_left v γ i
  · show Sum.elim id (Fin.append v γ)
      (Fin.append _ (fun j => Sum.map id (Fin.natAdd n₁) (θ j))
        (Fin.natAdd n₁ j)) = _
    rw [Fin.append_right, Fin.append_right]
    show Sum.elim id (Fin.append v γ) (Sum.map id (Fin.natAdd n₁) (θ j))
      = Sum.elim id γ (θ j)
    cases θ j with
    | inl a => rfl
    | inr i => exact Fin.append_right v γ i

/-! ## The two readings agree -/

/-- **Substituting and evaluating is evaluating under the substituted
valuation**, for the plain semantics. -/
theorem AggQueryIn.evaluatePlain_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d) (D : Database T) (γ : Fin d → T),
      (q.substMap θ).evaluatePlain D γ
        = q.evaluatePlain D (substVal θ γ) := by
  intro c n κ l q
  induction q with
  | Rel n s => intro d θ D γ; rfl
  | Hole n s => intro d θ D γ; rfl
  | Empty => intro d θ D γ; rfl
  | Proj ps q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap, AggQueryIn.evaluatePlain_castKind]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    funext j
    exact ProjColIn.evalPlain_substMap θ (ps j) u γ
  | Sel φ q _ ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    exact Multiset.filter_congr
      (fun u _ => GenPredIn.holdsPlain_substMap θ φ u γ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih₁ θ D γ, ih₂ θ D γ]
  | @Apply cI n₁ n₂ κ₁ κ₂ _ q₁ q₂ ih₁ ih₂ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih₁ θ D γ]
    refine Multiset.bind_congr (fun u _ => ?_)
    rw [ih₂ _ D (Fin.append u γ), substVal_append]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih₁ θ D γ, ih₂ θ D γ]
  | Dedup q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih₁ θ D γ, ih₂ θ D γ]
  | Explode k h q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain, ih]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain, ih₀, ih₁]
  | @Gamma cI m n₁ n₂ is ts fs q keep ord ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    refine congrArg (Fin.append g) (funext fun j => congrArg (fs j) ?_)
    exact List.map_congr_left (fun v _ => TermIn.eval_substMap θ (ts j) v γ)
  | @GammaScalar cI m n₂ ts fs q ord ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine congrArg (fun t => (Multiset.ofList [t] : Relation T n₂)) ?_
    funext j
    exact congrArg (fs j)
      (List.map_congr_left (fun v _ => TermIn.eval_substMap θ (ts j) v γ))
  | @GammaNest cI m n₁ κ' is his p f q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    refine congrArg (Fin.append g) (funext fun _ => congrArg f ?_)
    exact Multiset.map_congr rfl
      (fun v _ => ProjColIn.evalPlain_substMap θ p v γ)
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    refine congrArg (Fin.append g) (funext fun _ => ?_)
    exact congrArg (Multiset.fold addFn 0)
      (Multiset.map_congr rfl (fun u _ => TermGIn.evalPlain_substMap θ t u γ))
  | Retag h q ih => intro d θ D γ; rw [AggQueryIn.substMap]; exact ih θ D γ
  | @GammaTok cI m n₁ n₂ κ' is his ts fs a q keep ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    refine congrArg₂ Fin.append ?_ ?_
    · exact congrArg (Fin.append g)
        (funext fun j => congrArg (fs j)
          (List.map_congr_left (fun v _ => TermIn.eval_substMap θ (ts j) v γ)))
    · funext _
      exact congrArg (Multiset.fold addFn 0)
        (Multiset.map_congr rfl
          (fun u _ => TermGIn.evalPlain_substMap θ a u γ))
  | @Win cI n' m' p' κw P O o w t f q hrr dist keep ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    refine congrArg (fun v => (Fin.snoc u v : Tuple T (n' + 1))) ?_
    rcases keep with _ | φ <;>
      exact congrArg (if dist then f.distinct else f)
        (List.map_congr_left (fun v _ => TermIn.eval_substMap θ t v γ))
  | @WinExpr cI n' m' p' na P O o ws ts fs g q keeps ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    exact congrArg OccFam.toMultiset (congrArg (OccFam.mk _) (funext fun i =>
      congrArg (Fin.snoc _) (congrArg g (funext fun l =>
        congrArg (fs l) (List.map_congr_left
          (fun v _ => TermIn.eval_substMap θ (ts l) v γ))))))

/-! ### Tokens under substitution -/

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] [HasAltLinearOrder K] in
theorem AggValue.ofGroup_substMap {c d m : ℕ} (θ : Fin c → T ⊕ Fin d)
    (f : SeqAggFunc T) (t : TermIn T c m) (U : List (AnnotatedTuple T K m))
    (γ : Fin d → T) :
    AggValue.ofGroup f (t.substMap θ) U γ
      = AggValue.ofGroup f t U (substVal θ γ) := by
  simp only [AggValue.ofGroup, TermIn.eval_substMap]

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] [HasAltLinearOrder K] in
/-- The same for the expression a filtered aggregate builds. -/
theorem AggExpr.ofGroupWhen_substMap {c d m : ℕ} (θ : Fin c → T ⊕ Fin d)
    (f : SeqAggFunc T) (t : TermIn T c m) (keep : Tuple T m → Bool)
    (U : List (AnnotatedTuple T K m)) (γ : Fin d → T) :
    AggExpr.ofGroupWhen f (t.substMap θ) keep U γ
      = AggExpr.ofGroupWhen f t keep U (substVal θ γ) := by
  unfold AggExpr.ofGroupWhen AggExpr.ofSeqWhen
  simp only [TermIn.eval_substMap]

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] [HasAltLinearOrder K] in
theorem AggValue.ofScalarGroup_substMap {c d m : ℕ} (θ : Fin c → T ⊕ Fin d)
    (f : SeqAggFunc T) (t : TermIn T c m) (U : List (AnnotatedTuple T K m))
    (γ : Fin d → T) :
    AggValue.ofScalarGroup f (t.substMap θ) U γ
      = AggValue.ofScalarGroup f t U (substVal θ γ) := by
  simp only [AggValue.ofScalarGroup, AggValue.ofGroup_substMap]

omit [DecidableEq K] in
/-- The same for the expression a filtered window builds, merged or
not. -/
theorem ValueFrame.exprWhen_substMap {c d n m p : ℕ} (θ : Fin c → T ⊕ Fin d)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n → Bool) (r : OccFam (AnnotatedTuple T K n))
    (i : Fin r.size) (γ : Fin d → T) :
    ValueFrame.exprWhen P O o w (t.substMap θ) f dist keep r i γ
      = ValueFrame.exprWhen P O o w t f dist keep r i (substVal θ γ) := by
  unfold ValueFrame.exprWhen
  cases dist
  · simp only [Bool.false_eq_true, ite_false]
    unfold AggExpr.ofSeqWhen
    simp only [TermIn.eval_substMap]
  · simp only [ite_true]
    unfold AggExpr.ofSeqDistWhen
    simp only [TermIn.eval_substMap]

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] in
theorem ValueFrame.token_substMap {c d n m p : ℕ} (θ : Fin c → T ⊕ Fin d)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) (γ : Fin d → T) :
    ValueFrame.token P O o w (t.substMap θ) f r i γ
      = ValueFrame.token P O o w t f r i (substVal θ γ) := by
  unfold ValueFrame.token
  split
  · exact AggValue.ofGroup_substMap θ f t _ γ
  · exact AggValue.ofScalarGroup_substMap θ f t _ γ

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] in
/-- The same read off the relation, which is the form the evaluator's
`Win` clause uses. -/
theorem ValueFrame.tokenOf_substMap {c d n m p : ℕ} (θ : Fin c → T ⊕ Fin d)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n)
    (γ : Fin d → T) :
    ValueFrame.tokenOf P O o w (t.substMap θ) f X x γ
      = ValueFrame.tokenOf P O o w t f X x (substVal θ γ) := by
  unfold ValueFrame.tokenOf
  split
  · exact AggValue.ofGroup_substMap θ f t _ γ
  · exact AggValue.ofScalarGroup_substMap θ f t _ γ

omit [DecidableEq K] in
/-- And with `DISTINCT`, which only merges the classes afterwards. -/
theorem ValueFrame.tokenOfDist_substMap {c d n m p : ℕ}
    (θ : Fin c → T ⊕ Fin d) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (X : AnnotatedRelation T K n)
    (x : AnnotatedTuple T K n) (γ : Fin d → T) :
    ValueFrame.tokenOfDist P O o w (t.substMap θ) f dist X x γ
      = ValueFrame.tokenOfDist P O o w t f dist X x (substVal θ γ) := by
  unfold ValueFrame.tokenOfDist
  rw [ValueFrame.tokenOf_substMap]

omit [DecidableEq K] in
/-- And under a `FILTER` clause, whose column is an expression. -/
theorem ValueFrame.exprWhenOf_substMap {c d n m p : ℕ}
    (θ : Fin c → T ⊕ Fin d) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (keep : Tuple T n → Bool)
    (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n)
    (γ : Fin d → T) :
    ValueFrame.exprWhenOf P O o w (t.substMap θ) f dist keep X x γ
      = ValueFrame.exprWhenOf P O o w t f dist keep X x (substVal θ γ) := by
  unfold ValueFrame.exprWhenOf
  cases dist
  · simp only [Bool.false_eq_true, ite_false]
    unfold AggExpr.ofSeqWhen
    simp only [TermIn.eval_substMap]
  · simp only [ite_true]
    unfold AggExpr.ofSeqDistWhen
    simp only [TermIn.eval_substMap]

omit [DecidableEq K] in
/-- **The row a window adds, under a substitution**: the substitution
reaches the aggregated term and nothing else, the row's own columns and
its annotation going through untouched. -/
theorem ValueFrame.windowGenRow_substMap {c d n m p : ℕ}
    (θ : Fin c → T ⊕ Fin d) (κ : Fin n → ColKind) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (keep : Option (Selection T n))
    (X : AnnotatedRelation T K n) (x : GenRow T K n) (γ : Fin d → T)
    (dist : Bool) :
    ValueFrame.windowGenRow κ P O o w (t.substMap θ) f keep X x γ dist
      = ValueFrame.windowGenRow κ P O o w t f keep X x (substVal θ γ) dist := by
  unfold ValueFrame.windowGenRow
  rcases keep with _ | φ
  · dsimp only
    rw [ValueFrame.tokenOfDist_substMap]
  · dsimp only
    rw [ValueFrame.exprWhenOf_substMap]

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] in
/-- The same for the expression a multi-frame window computes: the
substitution reaches its leaves' terms and nothing else. -/
theorem ValueFrame.exprOf_substMap {c d n m p na : ℕ} (θ : Fin c → T ⊕ Fin d)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin na → ValueFrame T p) (ts : Fin na → TermIn T c n)
    (fs : Fin na → SeqAggFunc T) (g : (Fin na → T) → T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) (γ : Fin d → T) :
    ValueFrame.exprOf P O o ws (fun l => (ts l).substMap θ) fs g r i γ
      = ValueFrame.exprOf P O o ws ts fs g r i (substVal θ γ) := by
  unfold ValueFrame.exprOf
  exact ValueFrame.exprOfVals_congr P O o ws r i
    (funext (fun l => funext (fun j =>
      TermIn.eval_substMap θ (ts l) (r.row j).fst γ))) fs g

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] in
/-- The same under `FILTER` clauses: a clause reads the occurrence's own
row, which the substitution does not touch. -/
theorem ValueFrame.exprOfWhen_substMap {c d n m p na : ℕ}
    (θ : Fin c → T ⊕ Fin d)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin na → ValueFrame T p) (ts : Fin na → TermIn T c n)
    (fs : Fin na → SeqAggFunc T) (g : (Fin na → T) → T)
    (keeps : Fin na → Option (Selection T n))
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) (γ : Fin d → T) :
    ValueFrame.exprOfWhen P O o ws (fun l => (ts l).substMap θ) fs g keeps r i γ
      = ValueFrame.exprOfWhen P O o ws ts fs g keeps r i (substVal θ γ) := by
  unfold ValueFrame.exprOfWhen
  exact ValueFrame.exprOfValsWhen_congr P O o ws keeps r i
    (funext (fun l => funext (fun j =>
      TermIn.eval_substMap θ (ts l) (r.row j).fst γ))) fs g

/-- **Substituting and evaluating is evaluating under the substituted
valuation**, for the annotated semantics. -/
theorem AggQueryIn.evaluate_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d) (dB : AnnotatedDatabase T K)
      (γ : Fin d → T),
      (q.substMap θ).evaluate dB γ = q.evaluate dB (substVal θ γ) := by
  intro c n κ l q
  induction q with
  | Rel n s => intro d θ dB γ; rfl
  | Hole n s => intro d θ dB γ; rfl
  | Empty => intro d θ dB γ; rfl
  | Proj ps q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap, AggQueryIn.evaluate_castKind]
    simp only [AggQueryIn.evaluate, ProjColIn.eval_substMap]
    rw [ih θ dB γ]
  | Sel φ q _ ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, GenPredIn.hasAggAtom_substMap,
      GenPredIn.comparedCols_substMap, GenPredIn.entailsExistence_substMap,
      GenPredIn.predsem_substMap]
    rw [ih θ dB γ]
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ, ite_eq_left hφ]
    · rw [ite_eq_right hφ, ite_eq_right hφ]
      exact Multiset.filter_congr
        (fun r _ => GenPredIn.holds_substMap θ φ r.fst γ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ dB γ, ih₂ θ dB γ]
  | @Apply cI n₁ n₂ κ₁ κ₂ _ q₁ q₂ ih₁ ih₂ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ dB γ]
    refine Multiset.bind_congr (fun x _ => ?_)
    rw [ih₂ _ dB (Fin.append (GenRow.plainTuple x.fst) γ), substVal_append]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ dB γ, ih₂ θ dB γ]
  | Dedup q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih θ dB γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ dB γ, ih₂ θ dB γ]
  | Explode k h q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih₀, ih₁]
  | @Gamma cI m n₁ n₂ is ts fs q keep ord ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, AggValue.ofGroup_substMap,
      AggExpr.ofGroupWhen_substMap]
    rw [ih θ dB γ]
  | @GammaScalar cI m n₂ ts fs q ord ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, AggValue.ofScalarGroup_substMap]
    rw [ih θ dB γ]
  | @GammaNest cI m n₁ κ' is his p f q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ProjColIn.eval_substMap]
    rw [ih θ dB γ]
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, TermGIn.evalPlain_substMap]
    rw [ih θ dB γ]
  | Retag h q ih => intro d θ dB γ; rw [AggQueryIn.substMap]; exact ih θ dB γ
  | @GammaTok cI m n₁ n₂ κ' is his ts fs a q keep ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, AggValue.ofGroup_substMap,
      AggExpr.ofGroupWhen_substMap, TermGIn.evalPlain_substMap]
    rw [ih θ dB γ]
  | @Win cI n' m' p' κw P O o w t f q hrr dist keep ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ValueFrame.windowGenRow_substMap]
    rw [ih θ dB γ]
  | @WinExpr cI n' m' p' na P O o ws ts fs g q keeps ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ValueFrame.exprOfWhen_substMap]
    rw [ih θ dB γ]

/-! ## Closing a query: `q[u]` -/

/-- Evaluating a closed instance is evaluating under the values it was
closed with. -/
theorem AggQueryIn.evaluate_subst {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (u : Fin c → T) (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K) :
    (q.subst u).evaluate d = q.evaluate d u :=
  AggQueryIn.evaluate_substMap q _ d _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Plain counterpart of `AggQueryIn.evaluate_subst`. -/
theorem AggQueryIn.evaluatePlain_subst {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (u : Fin c → T) (q : AggQueryIn T c n κ l) (D : Database T) :
    (q.subst u).evaluatePlain D = q.evaluatePlain D u :=
  AggQueryIn.evaluatePlain_substMap q _ D _

/-- Annotated counterpart of `AggQueryIn.evaluate_subst`. -/
theorem AggQueryIn.evaluateAnnotated_subst {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (u : Fin c → T) (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K) :
    (q.subst u).evaluateAnnotated d = q.evaluateAnnotated d u :=
  congrArg (Multiset.map GenRow.toAnnotated)
    (AggQueryIn.evaluate_subst u q d)

/-- **The apply as a substitution**: each row `u` of the left
side is paired with each row of the *closed* query `q₂[u]`, and the
annotations are multiplied. This is the clause
`⟨q₁ ⋈ᴬ q₂⟩ = {(u, v, α₁ ⊗ α₂) ∣ (u, α₁) ∈ ⟨q₁⟩, (v, α₂) ∈ ⟨q₂[u]⟩}`;
that the evaluator reads the right side under a valuation instead is an
implementation of it, not a second semantics. -/
theorem AggQueryIn.evaluate_Apply_subst {n₁ n₂ : ℕ} {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁)) (q₂ : AggQueryIn T n₁ n₂ κ₂)
    (d : AnnotatedDatabase T K) :
    (AggQueryIn.Apply q₁ q₂).evaluate d
      = (q₁.evaluate d).bind (fun x =>
          ((q₂.subst (GenRow.plainTuple x.fst)).evaluate d).map (fun y =>
            (⟨Fin.append x.fst y.fst,
              ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
              : GenRow T K (n₁ + n₂)))) := by
  simp only [AggQueryIn.evaluate]
  refine Multiset.bind_congr (fun x _ => ?_)
  rw [AggQueryIn.evaluate_subst, Fin.append_nil]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Plain counterpart: `⟦q₁ ⋈ᴬ q₂⟧ = {(u, v) ∣ u ∈ ⟦q₁⟧, v ∈ ⟦q₂[u]⟧}`. -/
theorem AggQueryIn.evaluatePlain_Apply_subst {n₁ n₂ : ℕ}
    {κ₂ : Fin n₂ → ColKind} (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQueryIn T n₁ n₂ κ₂) (D : Database T) :
    (AggQueryIn.Apply q₁ q₂).evaluatePlain D
      = (q₁.evaluatePlain D).bind (fun u =>
          ((q₂.subst u).evaluatePlain D).map (fun v =>
            (Fin.append u v : Tuple T (n₁ + n₂)))) := by
  simp only [AggQueryIn.evaluatePlain]
  refine Multiset.bind_congr (fun u _ => ?_)
  rw [AggQueryIn.evaluatePlain_subst, Fin.append_nil]

/-! ## Stripping commutes with substituting -/

omit [ValueType T] in
theorem AggQueryIn.stripAgg_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).stripAgg = q.stripAgg.castKind h := by
  subst h; rfl

omit [ValueType T] in
theorem AggQueryIn.stripAgg_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d),
      (q.substMap θ).stripAgg = q.stripAgg.substMap θ := by
  intro c n κ l q
  induction q with
  | Rel n s => intro d θ; rfl
  | Hole n s => intro d θ; rfl
  | Empty => intro d θ; rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg_castKind, AggQueryIn.stripAgg,
      AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | Sel φ q hφ ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg,
      GenPredIn.hasAggAtom_substMap]
    by_cases h : φ.hasAggAtom
    · rw [ite_eq_left h, ite_eq_left h, ih]
    · rw [ite_eq_right h, ite_eq_right h, ih, AggQueryIn.substMap]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih₁, ih₂,
      AggQueryIn.substMap]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih₁, ih₂,
      AggQueryIn.substMap]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih₁, ih₂,
      AggQueryIn.substMap]
  | Dedup q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih₁]
  | Explode k hk q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | Retag hk q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih₀, ih₁,
      AggQueryIn.substMap]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih₀, ih₁,
      AggQueryIn.substMap]
  | Gamma is ts fs q keep ord ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | GammaScalar ts fs q ord ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | GammaNest is his p f q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | ProvSum is his t q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | GammaTok is his ts fs a q keep ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | Win P O o w t f q hrr dist keep ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.stripAgg, AggQueryIn.stripAgg, ih, AggQueryIn.substMap]

/-! ## What an apply's right side reads of its left row -/

/-- A row with its annotation finalized, its columns kept: what every
reading of an annotated evaluation reads of a row. -/
def GenRow.fin {n : ℕ} (r : GenRow T K n) : Tuple (GenValue T K) n × K :=
  (r.fst, r.snd.finalize)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenRow.fin_eq_iff {n : ℕ} {a b : GenRow T K n} :
    a.fin = b.fin ↔ a.fst = b.fst ∧ a.snd.finalize = b.snd.finalize := Prod.ext_iff

/-- Two bags agreeing under `f` agree under any `g` that `f` determines. -/
theorem Multiset.map_eq_of_factor {α β γ : Type*} {f : α → β} {g : α → γ}
    (hfg : ∀ a b, f a = f b → g a = g b) {R R' : Multiset α} (h : R.map f = R'.map f) :
    R.map g = R'.map g := by
  classical
  by_cases hR : R = 0
  · subst hR
    have hR' : R' = 0 := Multiset.map_eq_zero.mp (by rw [← h, Multiset.map_zero])
    rw [hR']
  · obtain ⟨a₀, -⟩ := Multiset.exists_mem_of_ne_zero hR
    let G : β → γ := fun y => if hy : ∃ a, f a = y then g (Classical.choose hy) else g a₀
    have hG : ∀ a, G (f a) = g a := fun a => by
      have hy : ∃ a', f a' = f a := ⟨a, rfl⟩
      show (if hy : ∃ a', f a' = f a then g (Classical.choose hy) else g a₀) = g a
      rw [dite_eq_left hy]
      exact hfg _ _ (Classical.choose_spec hy)
    have hS : ∀ S : Multiset α, S.map g = (S.map f).map G := fun S => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl (fun a _ => (hG a).symm)
    rw [hS R, hS R', h]

/-- The same for a bind. -/
theorem Multiset.bind_eq_of_factor {α β γ : Type*} {f : α → β} {g : α → Multiset γ}
    (hfg : ∀ a b, f a = f b → g a = g b) {R R' : Multiset α} (h : R.map f = R'.map f) :
    R.bind g = R'.bind g := by
  unfold Multiset.bind
  rw [Multiset.map_eq_of_factor hfg h]

/-- The same for a filter followed by a map. -/
theorem Multiset.map_filter_eq_of_factor {α β γ : Type*} {f : α → β} {p : α → Prop}
    [DecidablePred p] {g : α → γ} (hp : ∀ a b, f a = f b → (p a ↔ p b))
    (hg : ∀ a b, f a = f b → g a = g b) {R R' : Multiset α} (h : R.map f = R'.map f) :
    (R.filter p).map g = (R'.filter p).map g := by
  have hb : ∀ S : Multiset α, (S.filter p).map g = S.bind (fun a => if p a then {g a} else 0) :=
    fun S => by
      induction S using Multiset.induction_on with
      | empty => rfl
      | cons a S ih =>
        rw [Multiset.cons_bind, ← ih]
        by_cases ha : p a
        · rw [Multiset.filter_cons_of_pos _ ha, Multiset.map_cons, ite_eq_left ha,
            Multiset.singleton_add]
        · rw [Multiset.filter_cons_of_neg _ ha, ite_eq_right ha, zero_add]
  rw [hb, hb]
  refine Multiset.bind_eq_of_factor (fun a b hab => ?_) h
  by_cases ha : p a
  · rw [ite_eq_left ha, ite_eq_left ((hp a b hab).mp ha), hg a b hab]
  · rw [ite_eq_right ha, ite_eq_right (fun hb => ha ((hp a b hab).mpr hb))]

/-- Two contexts of an apply's right side agree **away from the aggregate
columns of the left side**: on the left row's other columns and on the
ambient context. -/
def AgreeReg {c n₁ : ℕ} (κ₁ : Fin n₁ → ColKind) (γ γ' : Fin (n₁ + c) → T) : Prop :=
  (∀ i, (κ₁ i).base ≠ ColKind.agg → γ (Fin.castAdd c i) = γ' (Fin.castAdd c i))
    ∧ ∀ j, γ (Fin.natAdd n₁ j) = γ' (Fin.natAdd n₁ j)

/-- **An apply's right side reads no aggregate column of its left side**,
in the plain semantics: two contexts agreeing away from those columns
give the same answer. -/
def AggQueryIn.ReadsRegParamsPlain {c n₁ n₂ : ℕ} (κ₁ : Fin n₁ → ColKind)
    {κ₂ : Fin n₂ → ColKind} (q₂ : AggQueryIn T (n₁ + c) n₂ κ₂) : Prop :=
  ∀ (D : Database T) (γ γ' : Fin (n₁ + c) → T), AgreeReg κ₁ γ γ' →
    q₂.evaluatePlain D γ = q₂.evaluatePlain D γ'

/-- **An apply's right side reads no aggregate column of its left side**:
in the plain semantics, in the plain semantics of its stripped form (the
data part of its annotated reading), and in the annotated semantics over
every semiring, up to finalization.

The evaluators give the right side the deterministic value of an
aggregate column (`GenRow.plainTuple`), where the semantics paper reads an
aggregate parameter world by world, as an aggregate atom reads a column;
on a right side satisfying this the two readings agree, the value being
read nowhere. Reading it would also be an explosion in all but name: a
rank computed by a window and read as a parameter compares two values
with no selection, against a constant, by a difference. -/
def AggQueryIn.ReadsRegParams {c n₁ n₂ : ℕ} (κ₁ : Fin n₁ → ColKind)
    {κ₂ : Fin n₂ → ColKind} (q₂ : AggQueryIn T (n₁ + c) n₂ κ₂) : Prop :=
  AggQueryIn.ReadsRegParamsPlain κ₁ q₂ ∧ AggQueryIn.ReadsRegParamsPlain κ₁ q₂.stripAgg
    ∧ ∀ (K' : Type) [CommSemiringWithMonus K'] [DecidableEq K'] [HasAltLinearOrder K']
        (d : AnnotatedDatabase T K') (γ γ' : Fin (n₁ + c) → T), AgreeReg κ₁ γ γ' →
        (q₂.evaluate d γ).map GenRow.fin = (q₂.evaluate d γ').map GenRow.fin

/-- **No apply's right side reads an aggregate column of its left side**,
in the plain semantics. -/
def AggQueryIn.noAggParamPlain : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noAggParamPlain
  | _, _, _, _, .Sel _ q _ => q.noAggParamPlain
  | _, _, _, _, .Prod q₁ q₂ => q₁.noAggParamPlain ∧ q₂.noAggParamPlain
  | _, _, _, _, @Apply _ _ _ _ κ₁ _ _ q₁ q₂ =>
      q₁.noAggParamPlain ∧ q₂.noAggParamPlain ∧ AggQueryIn.ReadsRegParamsPlain κ₁ q₂
  | _, _, _, _, .Sum q₁ q₂ => q₁.noAggParamPlain ∧ q₂.noAggParamPlain
  | _, _, _, _, .Dedup q => q.noAggParamPlain
  | _, _, _, _, .Diff q₁ q₂ => q₁.noAggParamPlain ∧ q₂.noAggParamPlain
  | _, _, _, _, .Explode _ _ q => q.noAggParamPlain
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noAggParamPlain ∧ q₁.noAggParamPlain
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noAggParamPlain ∧ q₁.noAggParamPlain
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noAggParamPlain
  | _, _, _, _, .GammaScalar _ _ q _ => q.noAggParamPlain
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noAggParamPlain
  | _, _, _, _, .ProvSum _ _ _ q => q.noAggParamPlain
  | _, _, _, _, .Retag _ q => q.noAggParamPlain
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noAggParamPlain
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noAggParamPlain
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noAggParamPlain

/-- **No apply's right side reads an aggregate column of its left side**
(`AggQueryIn.ReadsRegParams` at every apply). On such a query the
evaluators' reading of an aggregate parameter, its deterministic value,
is never used, which is what the random-world commutation needs of an
apply, and what keeps the selection necessary. -/
def AggQueryIn.noAggParam : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noAggParam
  | _, _, _, _, .Sel _ q _ => q.noAggParam
  | _, _, _, _, .Prod q₁ q₂ => q₁.noAggParam ∧ q₂.noAggParam
  | _, _, _, _, @Apply _ _ _ _ κ₁ _ _ q₁ q₂ =>
      q₁.noAggParam ∧ q₂.noAggParam ∧ AggQueryIn.ReadsRegParams κ₁ q₂
  | _, _, _, _, .Sum q₁ q₂ => q₁.noAggParam ∧ q₂.noAggParam
  | _, _, _, _, .Dedup q => q.noAggParam
  | _, _, _, _, .Diff q₁ q₂ => q₁.noAggParam ∧ q₂.noAggParam
  | _, _, _, _, .Explode _ _ q => q.noAggParam
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noAggParam ∧ q₁.noAggParam
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noAggParam ∧ q₁.noAggParam
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.noAggParam
  | _, _, _, _, .GammaScalar _ _ q _ => q.noAggParam
  | _, _, _, _, .GammaNest _ _ _ _ q => q.noAggParam
  | _, _, _, _, .ProvSum _ _ _ q => q.noAggParam
  | _, _, _, _, .Retag _ q => q.noAggParam
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.noAggParam
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.noAggParam
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noAggParam

omit [ValueType T] in
/-- Contexts agreeing away from the aggregate columns of a left side that
has none agree everywhere. -/
theorem AgreeReg.eq_of_noAgg {c n₁ : ℕ} {κ₁ : Fin n₁ → ColKind}
    (hκ : ∀ i, (κ₁ i).base ≠ ColKind.agg) {γ γ' : Fin (n₁ + c) → T}
    (h : AgreeReg κ₁ γ γ') : γ = γ' := by
  funext m
  induction m using Fin.addCases with
  | left i => exact h.1 i (hκ i)
  | right j => exact h.2 j

omit [ValueType T] in
/-- A substitution sending nothing to an aggregate column of the left side
reads two such contexts alike. -/
theorem AgreeReg.substVal_eq {c n₁ d : ℕ} {κ₁ : Fin n₁ → ColKind}
    (θ : Fin d → T ⊕ Fin (n₁ + c))
    (hθ : ∀ k i, θ k = Sum.inr (Fin.castAdd c i) → (κ₁ i).base ≠ ColKind.agg)
    {γ γ' : Fin (n₁ + c) → T} (h : AgreeReg κ₁ γ γ') :
    substVal θ γ = substVal θ γ' := by
  funext k
  unfold substVal
  cases hk : θ k with
  | inl a => rfl
  | inr m =>
    show γ m = γ' m
    induction m using Fin.addCases with
    | left i => exact h.1 i (hθ k i hk)
    | right j => exact h.2 j

/-- An apply whose left side has no aggregate column reads none. -/
theorem AggQueryIn.readsRegParams_of_noAgg {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} (hκ : ∀ i, (κ₁ i).base ≠ ColKind.agg)
    (q₂ : AggQueryIn T (n₁ + c) n₂ κ₂) : AggQueryIn.ReadsRegParams κ₁ q₂ :=
  ⟨fun _ _ _ h => by rw [h.eq_of_noAgg hκ], fun _ _ _ h => by rw [h.eq_of_noAgg hκ],
    fun _ _ _ _ _ _ _ h => by rw [h.eq_of_noAgg hκ]⟩

theorem AggQueryIn.readsRegParams_allReg {c n₁ n₂ : ℕ} {κ₂ : Fin n₂ → ColKind}
    (q₂ : AggQueryIn T (n₁ + c) n₂ κ₂) :
    AggQueryIn.ReadsRegParams (ColKind.allReg n₁) q₂ :=
  AggQueryIn.readsRegParams_of_noAgg (fun _ => (by decide : ColKind.reg.base ≠ ColKind.agg)) q₂

/-- **A substitution instance reading no aggregate column of the left
side reads none.** -/
theorem AggQueryIn.readsRegParams_substMap {c n₁ n₂ d : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} (q : AggQueryIn T d n₂ κ₂)
    (θ : Fin d → T ⊕ Fin (n₁ + c))
    (hθ : ∀ k i, θ k = Sum.inr (Fin.castAdd c i) → (κ₁ i).base ≠ ColKind.agg) :
    AggQueryIn.ReadsRegParams κ₁ (q.substMap θ) := by
  refine ⟨fun D γ γ' h => ?_, fun D γ γ' h => ?_, fun K' _ _ _ dB γ γ' h => ?_⟩
  · rw [AggQueryIn.evaluatePlain_substMap, AggQueryIn.evaluatePlain_substMap,
      h.substVal_eq θ hθ]
  · rw [AggQueryIn.stripAgg_substMap, AggQueryIn.evaluatePlain_substMap,
      AggQueryIn.evaluatePlain_substMap, h.substVal_eq θ hθ]
  · rw [AggQueryIn.evaluate_substMap, AggQueryIn.evaluate_substMap, h.substVal_eq θ hθ]

/-- A right side lifted from the ambient context reads nothing of the left
row. -/
theorem AggQueryIn.readsRegParams_applyOuter {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} (q : AggQueryIn T c n₂ κ₂) :
    AggQueryIn.ReadsRegParams κ₁
      (q.substMap (fun j : Fin c => (Sum.inr (Fin.natAdd n₁ j) : T ⊕ Fin (n₁ + c)))) :=
  AggQueryIn.readsRegParams_substMap q _ (fun k i hk => absurd (Sum.inr.inj hk)
    (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega))

theorem AggQueryIn.ReadsRegParams.plain {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {q₂ : AggQueryIn T (n₁ + c) n₂ κ₂}
    (h : AggQueryIn.ReadsRegParams κ₁ q₂) : AggQueryIn.ReadsRegParamsPlain κ₁ q₂ := h.1

theorem AggQueryIn.ReadsRegParams.evaluate {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {q₂ : AggQueryIn T (n₁ + c) n₂ κ₂}
    (h : AggQueryIn.ReadsRegParams κ₁ q₂) (d : AnnotatedDatabase T K)
    {γ γ' : Fin (n₁ + c) → T} (hγ : AgreeReg κ₁ γ γ') :
    (q₂.evaluate d γ).map GenRow.fin = (q₂.evaluate d γ').map GenRow.fin :=
  h.2.2 K d γ γ' hγ

/-- **Stripping keeps the fence**, in the plain form the stripped query is
read in. -/
theorem AggQueryIn.noAggParamPlain_stripAgg :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noAggParam → q.stripAgg.noAggParamPlain := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ => trivial
  | Hole _ _ => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q hφ ih =>
    intro h
    rw [AggQueryIn.stripAgg]
    by_cases hφ' : φ.hasAggAtom
    · rw [ite_eq_left hφ']; exact ih h
    · rw [ite_eq_right hφ']; exact ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2.1, h.2.2.2.1⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Explode k hk q ih => exact fun h => ih h
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

@[simp] theorem AggQueryIn.noAggParam_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).noAggParam ↔ q.noAggParam := by
  subst h; exact Iff.rfl

@[simp] theorem AggQueryIn.noAggParamPlain_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).noAggParamPlain ↔ q.noAggParamPlain := by
  subst h; exact Iff.rfl

/-- **The fence carries over to anything reading alike**: in the plain
semantics, in that of its stripped form, and up to finalization in the
annotated semantics over every semiring. -/
theorem AggQueryIn.ReadsRegParams.of_eval {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind}
    {p : AggQueryIn T (n₁ + c) n₂ κ₂} {p' : AggQueryIn T (n₁ + c) n₂ κ₂}
    (hp : ∀ D γ, p'.evaluatePlain D γ = p.evaluatePlain D γ)
    (hs : ∀ D γ, p'.stripAgg.evaluatePlain D γ = p.stripAgg.evaluatePlain D γ)
    (ha : ∀ (K' : Type) [CommSemiringWithMonus K'] [DecidableEq K'] [HasAltLinearOrder K']
      (d : AnnotatedDatabase T K') γ,
        (p'.evaluate d γ).map GenRow.fin = (p.evaluate d γ).map GenRow.fin)
    (h : AggQueryIn.ReadsRegParams κ₁ p) : AggQueryIn.ReadsRegParams κ₁ p' :=
  ⟨fun D γ γ' hγ => by rw [hp, hp, h.1 D γ γ' hγ],
    fun D γ γ' hγ => by rw [hs, hs, h.2.1 D γ γ' hγ],
    fun K' _ _ _ d γ γ' hγ => by rw [ha, ha, h.2.2 K' d γ γ' hγ]⟩
