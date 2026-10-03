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
  | .provTerm t => .provTerm (t.substMap θ)

omit [ValueType T] in
/-- The substitution does not change an output column's kind. -/
@[simp] theorem ProjColIn.kind_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (p : ProjColIn T c κ) :
    (p.substMap θ).kind = p.kind := by
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
  | provTerm t => exact congrArg Sum.inl (TermGIn.eval_substMap θ t u γ)

theorem ProjColIn.evalPlain_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (p : ProjColIn T c κ) (u : Tuple T n)
    (γ : Fin d → T) :
    (p.substMap θ).evalPlain u γ = p.evalPlain u (substVal θ γ) := by
  cases p with
  | term t => exact TermGIn.evalPlain_substMap θ t u γ
  | token k h => rfl
  | aggTerm k h gf => rfl
  | provTerm t => exact TermGIn.evalPlain_substMap θ t u γ

/-! ## Substitution on queries -/

/-- Substitute the outer columns of a query. The right side of an apply
reads its left neighbour's columns first and the ambient outer ones
after, so the substitution passes under it by leaving the neighbour's
block alone and shifting the ambient one. -/
def AggQueryIn.substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (q : AggQueryIn T c n κ) : AggQueryIn T d n κ :=
  match c, d, n, κ, θ, q with
  | _, _, _, _, _, .Rel n s => .Rel n s
  | _, _, _, _, θ, .Proj ps q =>
      AggQueryIn.castKind (funext fun j => ProjColIn.kind_substMap θ (ps j))
        (.Proj (fun j => (ps j).substMap θ) (q.substMap θ))
  | _, _, _, _, θ, .Sel φ q => .Sel (φ.substMap θ) (q.substMap θ)
  | _, _, _, _, θ, .Prod q₁ q₂ => .Prod (q₁.substMap θ) (q₂.substMap θ)
  | _, d, _, _, θ, @AggQueryIn.Apply _ _ n₁ _ _ q₁ q₂ =>
      .Apply (q₁.substMap θ)
        (q₂.substMap (Fin.append (fun k => Sum.inr (Fin.castAdd d k))
          (fun j => Sum.map id (Fin.natAdd n₁) (θ j))))
  | _, _, _, _, θ, .Sum q₁ q₂ => .Sum (q₁.substMap θ) (q₂.substMap θ)
  | _, _, _, _, θ, .Dedup q => .Dedup (q.substMap θ)
  | _, _, _, _, θ, .Diff q₁ q₂ => .Diff (q₁.substMap θ) (q₂.substMap θ)
  | _, _, _, _, θ, .Alt k h q => .Alt k h (q.substMap θ)
  | _, _, _, _, θ, .Mu b s q₀ q₁ => .Mu b s (q₀.substMap θ) (q₁.substMap θ)
  | _, _, _, _, θ, .MuSet b s q₀ q₁ =>
      .MuSet b s (q₀.substMap θ) (q₁.substMap θ)
  | _, _, _, _, θ, .Gamma is ts fs q keep =>
      .Gamma is (fun j => (ts j).substMap θ) fs (q.substMap θ) keep
  | _, _, _, _, θ, .GammaScalar ts fs q =>
      .GammaScalar (fun j => (ts j).substMap θ) fs (q.substMap θ)
  | _, _, _, _, θ, .GammaNest is his p f q =>
      .GammaNest is his (p.substMap θ) f (q.substMap θ)
  | _, _, _, _, θ, .ProvSum is his t q =>
      .ProvSum is his (t.substMap θ) (q.substMap θ)
  | _, _, _, _, θ, .Retag h q => .Retag h (q.substMap θ)
  | _, _, _, _, θ, .GammaTok is his ts fs a q =>
      .GammaTok is his (fun j => (ts j).substMap θ) fs (a.substMap θ)
        (q.substMap θ)
  | _, _, _, _, θ, .Win P O o w t f q dist keep =>
      .Win P O o w (t.substMap θ) f (q.substMap θ) dist keep
  | _, _, _, _, θ, .WinExpr P O o ws ts fs g q =>
      .WinExpr P O o ws (fun l => (ts l).substMap θ) fs g (q.substMap θ)
termination_by structural q

/-- Close a query: give every outer column a value. This is the
document's `q[u]`. -/
abbrev AggQueryIn.subst {c n : ℕ} {κ : Fin n → ColKind} (u : Fin c → T)
    (q : AggQueryIn T c n κ) : AggQuery T n κ :=
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
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d) (D : Database T) (γ : Fin d → T),
      (q.substMap θ).evaluatePlain D γ
        = q.evaluatePlain D (substVal θ γ) := by
  intro c n κ q
  induction q with
  | Rel n s => intro d θ D γ; rfl
  | Proj ps q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap, AggQueryIn.evaluatePlain_castKind]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    funext j
    exact ProjColIn.evalPlain_substMap θ (ps j) u γ
  | Sel φ q ih =>
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
  | @Apply cI n₁ n₂ κ₂ q₁ q₂ ih₁ ih₂ =>
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
  | Alt k h q ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain, ih]
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain, ih₀, ih₁]
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain, ih₀, ih₁]
  | @Gamma cI m n₁ n₂ is ts fs q keep ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    refine congrArg (Fin.append g) (funext fun j => congrArg (fs j) ?_)
    exact List.map_congr_left (fun v _ => TermIn.eval_substMap θ (ts j) v γ)
  | @GammaScalar cI m n₂ ts fs q ih =>
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
  | @GammaTok cI m n₁ n₂ κ' is his ts fs a q ih =>
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
  | @Win cI n' m' p' P O o w t f q dist keep ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine congrArg OccFam.toMultiset (congrArg (OccFam.mk _) (funext fun i =>
      congrArg (Fin.snoc _) (congrArg (if dist then f.distinct else f) ?_)))
    exact List.map_congr_left (fun v _ => TermIn.eval_substMap θ t v γ)
  | @WinExpr cI n' m' p' na P O o ws ts fs g q ih =>
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
/-- The clause reads the group's own row, so a substitution of the outer
context moves neither it nor the occurrences it keeps. -/
theorem AggValue.ofGroupWhen_substMap {c d m : ℕ} (θ : Fin c → T ⊕ Fin d)
    (f : SeqAggFunc T) (t : TermIn T c m) (keep : Tuple T m → Bool)
    (U : List (AnnotatedTuple T K m)) (γ : Fin d → T) :
    AggValue.ofGroupWhen f (t.substMap θ) keep U γ
      = AggValue.ofGroupWhen f t keep U (substVal θ γ) := by
  unfold AggValue.ofGroupWhen
  simp only [AggValue.ofScalarGroup, AggValue.ofGroup, TermIn.eval_substMap]

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] [HasAltLinearOrder K] in
theorem AggValue.ofScalarGroup_substMap {c d m : ℕ} (θ : Fin c → T ⊕ Fin d)
    (f : SeqAggFunc T) (t : TermIn T c m) (U : List (AnnotatedTuple T K m))
    (γ : Fin d → T) :
    AggValue.ofScalarGroup f (t.substMap θ) U γ
      = AggValue.ofScalarGroup f t U (substVal θ γ) := by
  simp only [AggValue.ofScalarGroup, AggValue.ofGroup_substMap]

omit [DecidableEq K] in
omit [CommSemiringWithMonus K] in
/-- The clause reads the row, so a substitution of the outer context
moves neither it nor the occurrences of the frame it keeps. -/
theorem ValueFrame.tokenWhen_substMap {c d n m p : ℕ} (θ : Fin c → T ⊕ Fin d)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (keep : Tuple T n → Bool) (r : OccFam (AnnotatedTuple T K n))
    (i : Fin r.size) (γ : Fin d → T) :
    ValueFrame.tokenWhen P O o w (t.substMap θ) f keep r i γ
      = ValueFrame.tokenWhen P O o w t f keep r i (substVal θ γ) := by
  unfold ValueFrame.tokenWhen
  exact AggValue.ofScalarGroup_substMap θ f t _ γ

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

/-- **Substituting and evaluating is evaluating under the substituted
valuation**, for the annotated semantics. -/
theorem AggQueryIn.evaluate_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d) (dB : AnnotatedDatabase T K)
      (γ : Fin d → T),
      (q.substMap θ).evaluate dB γ = q.evaluate dB (substVal θ γ) := by
  intro c n κ q
  induction q with
  | Rel n s => intro d θ dB γ; rfl
  | Proj ps q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap, AggQueryIn.evaluate_castKind]
    simp only [AggQueryIn.evaluate, ProjColIn.eval_substMap]
    rw [ih θ dB γ]
  | Sel φ q ih =>
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
  | @Apply cI n₁ n₂ κ₂ q₁ q₂ ih₁ ih₂ =>
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
  | Alt k h q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih]
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih₀, ih₁]
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih₀, ih₁]
  | @Gamma cI m n₁ n₂ is ts fs q keep ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, AggValue.ofGroup_substMap,
      AggValue.ofGroupWhen_substMap]
    rw [ih θ dB γ]
  | @GammaScalar cI m n₂ ts fs q ih =>
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
  | @GammaTok cI m n₁ n₂ κ' is his ts fs a q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, AggValue.ofGroup_substMap,
      TermGIn.evalPlain_substMap]
    rw [ih θ dB γ]
  | @Win cI n' m' p' P O o w t f q dist keep ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ValueFrame.tokenDist,
      ValueFrame.tokenDistWhen, ValueFrame.token_substMap,
      ValueFrame.tokenWhen_substMap]
    rw [ih θ dB γ]
  | @WinExpr cI n' m' p' na P O o ws ts fs g q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ValueFrame.exprOf_substMap]
    rw [ih θ dB γ]

/-! ## Closing a query: the document's `q[u]` -/

/-- Evaluating a closed instance is evaluating under the values it was
closed with. -/
theorem AggQueryIn.evaluate_subst {c n : ℕ} {κ : Fin n → ColKind}
    (u : Fin c → T) (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K) :
    (q.subst u).evaluate d = q.evaluate d u :=
  AggQueryIn.evaluate_substMap q _ d _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Plain counterpart of `AggQueryIn.evaluate_subst`. -/
theorem AggQueryIn.evaluatePlain_subst {c n : ℕ} {κ : Fin n → ColKind}
    (u : Fin c → T) (q : AggQueryIn T c n κ) (D : Database T) :
    (q.subst u).evaluatePlain D = q.evaluatePlain D u :=
  AggQueryIn.evaluatePlain_substMap q _ D _

/-- Annotated counterpart of `AggQueryIn.evaluate_subst`. -/
theorem AggQueryIn.evaluateAnnotated_subst {c n : ℕ} {κ : Fin n → ColKind}
    (u : Fin c → T) (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K) :
    (q.subst u).evaluateAnnotated d = q.evaluateAnnotated d u :=
  congrArg (Multiset.map GenRow.toAnnotated)
    (AggQueryIn.evaluate_subst u q d)

/-- **The apply, as the document writes it**: each row `u` of the left
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
