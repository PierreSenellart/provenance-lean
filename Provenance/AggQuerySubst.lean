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
defines the substitution and proves the two readings agree – in the plain
semantics for every substitution (`AggQueryIn.evaluatePlain_subst`), and in
the annotated one for a *renaming* (`AggQueryIn.evaluate_substMap`): an
aggregating operator records the values of the parameters it reads in the
family it stamps, and a constant put in a parameter's place is no longer
read as one.

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

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenPredIn.eval3W_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ) (v : Fin n → Option T)
    (u : Tuple (GenValue T K) n) (γ : Fin d → T) :
    (φ.substMap θ).eval3W v u γ = φ.eval3W v u (substVal θ γ) := by
  induction φ with
  | cmp op t₁ t₂ | aggCmp k h op t₁ | aggRange k h op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.substMap, GenPredIn.eval3W, TermGIn.eval_substMap]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.substMap, GenPredIn.eval3W, ihφ, ihψ]
  | not φ ih => simp only [GenPredIn.substMap, GenPredIn.eval3W, ih]

omit [HasAltLinearOrder K] in
/-- **The joint reading under a substitution**: the worlds are the row's,
which the substitution does not touch, and the predicate is read under
the substituted valuation. -/
theorem GenPredIn.predsemJ_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (φ : GenPredIn T c κ) (neg : Bool)
    (u : Tuple (GenValue T K) n) (γ : Fin d → T) :
    (φ.substMap θ).predsemJ neg u γ = φ.predsemJ neg u (substVal θ γ) := by
  unfold GenPredIn.predsemJ
  simp only [GenPredIn.comparedCols_substMap, GenPredIn.eval3W_substMap]

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

omit [ValueType T] in
/-- **The parameters a substituted operator reads**: those the source's
parameters are sent to. -/
def substRd {c d : ℕ} (θ : Fin c → T ⊕ Fin d) (rd : Fin c → Bool) : Fin d → Bool :=
  fun j => decide (∃ k, Sum.elim (fun _ => false) (fun j' => decide (j' = j)) (θ k) = true
    ∧ rd k = true)

/-- Substitute the outer columns of a query. The right side of an apply
reads its left neighbour's columns first and the ambient outer ones
after, so the substitution passes under it by leaving the neighbour's
block alone and shifting the ambient one. -/
def AggQueryIn.substMap {c d n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (θ : Fin c → T ⊕ Fin d) (q : AggQueryIn T c n κ l) : AggQueryIn T d n κ l :=
  match c, d, n, κ, l, θ, q with
  | _, _, _, _, _, _, .Rel n s => .Rel n s
  | _, _, _, _, _, _, .Hole n s κ => .Hole n s κ
  | _, _, _, _, _, θ, .Param pv ρ => .Param (fun k => _root_.Sum.elim Sum.inl θ (pv k)) ρ
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
  | _, _, _, _, _, θ, .Gamma (lab := lab) (rd := rd) is ts fs q keep ord =>
      .Gamma (lab := lab) (rd := substRd θ rd) is (fun j => (ts j).substMap θ) fs (q.substMap
          θ) keep ord
  | _, _, _, _, _, θ, .GammaScalar (lab := lab) (rd := rd) ts fs q ord =>
      .GammaScalar (lab := lab) (rd := substRd θ rd) (fun j => (ts j).substMap θ) fs (q.substMap
          θ) ord
  | _, _, _, _, _, θ, .GammaNest (lab := lab) (rd := rd) is his p f q =>
      .GammaNest (lab := lab) (rd := substRd θ rd) is his (p.substMap θ) f (q.substMap θ)
  | _, _, _, _, _, θ, .ProvSum is his t q =>
      .ProvSum is his (t.substMap θ) (q.substMap θ)
  | _, _, _, _, _, θ, .Retag h q => .Retag h (q.substMap θ)
  | _, _, _, _, _, θ, .GammaTok (lab := lab) (rd := rd) is his ts fs a q keep =>
      .GammaTok (lab := lab) (rd := substRd θ rd) is his (fun j => (ts j).substMap
          θ) fs (a.substMap θ)
        (q.substMap θ) keep
  | _, _, _, _, _, θ, .Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep =>
      .Win (lab := lab) (rd := substRd θ rd) P O o w (t.substMap θ) f (q.substMap θ)
        ⟨hrr.1, hrr.2.1, by rw [TermIn.regOnly_substMap]; exact hrr.2.2⟩
        dist keep
  | _, _, _, _, _, θ, .WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps =>
      .WinExpr (lab := lab) (rd := substRd θ rd) P O o ws (fun l => (ts l).substMap
          θ) fs g (q.substMap θ) keeps
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

/-- Substituting a context of general values: a constant becomes a
regular value. -/
def substCtx {c d : ℕ} (θ : Fin c → T ⊕ Fin d) (u : Tuple (GenValue T K) d) :
    Tuple (GenValue T K) c :=
  fun k => Sum.elim Sum.inl u (θ k)

/-- The environment a substituted query is read in, seen from the source:
its context substituted. -/
def EvalEnv.substEnv {c d : ℕ} (E : EvalEnv T K) (θ : Fin c → T ⊕ Fin d) (γ : Fin d → T) :
    EvalEnv T K :=
  E.withCtx (substCtx θ (E.ctxAt d γ))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem EvalEnv.substEnv_assignHole {c d : ℕ} (E : EvalEnv T K) (θ : Fin c → T ⊕ Fin d)
    (γ : Fin d → T) (s : String) {n : ℕ} (X : Multiset (GenRow T K n)) :
    (E.assignHole s X).substEnv θ γ = (E.substEnv θ γ).assignHole s X := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Passing a substitution under an apply, on a context of general values. -/
theorem substCtx_append {c d n₁ : ℕ} (θ : Fin c → T ⊕ Fin d)
    (x : Tuple (GenValue T K) n₁) (u : Tuple (GenValue T K) d) :
    substCtx (Fin.append (fun k => Sum.inr (Fin.castAdd d k))
        (fun j => Sum.map id (Fin.natAdd n₁) (θ j))) (Fin.append x u)
      = Fin.append x (substCtx θ u) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · show Sum.elim Sum.inl (Fin.append x u)
      (Fin.append (fun k => Sum.inr (Fin.castAdd d k)) _ (Fin.castAdd c i)) = _
    rw [Fin.append_left, Fin.append_left]
    exact Fin.append_left x u i
  · show Sum.elim Sum.inl (Fin.append x u)
      (Fin.append _ (fun j => Sum.map id (Fin.natAdd n₁) (θ j)) (Fin.natAdd n₁ j)) = _
    rw [Fin.append_right, Fin.append_right]
    show Sum.elim Sum.inl (Fin.append x u) (Sum.map id (Fin.natAdd n₁) (θ j))
      = Sum.elim Sum.inl u (θ j)
    cases θ j with
    | inl a => rfl
    | inr i => exact Fin.append_right x u i

/-- **The evaluation reads the environment's context only at its own
arity**: two environments binding the same rounds and giving the same
context there evaluate alike. -/
theorem AggQueryIn.evaluate_congr_env :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (dB : AnnotatedDatabase T K) (γ : Fin c → T) {E E' : EvalEnv T K},
      E.holes = E'.holes → E.ctxAt c γ = E'.ctxAt c γ →
      q.evaluate dB γ E = q.evaluate dB γ E' := by
  intro c n κ l q
  induction q with
  | Rel n s => intro dB γ E E' _ _; rfl
  | Hole n s κ => intro dB γ E E' hh _; simp only [AggQueryIn.evaluate, hh]
  | Param pv ρ =>
    intro dB γ E E' _ hc
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows, hc]
  | Empty => intro dB γ E E' _ _; rfl
  | Proj ps q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Sel φ q _ ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih₁ dB γ hh hc, ih₂ dB γ hh hc]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate, ih₁ dB γ hh hc]
    refine Multiset.bind_congr (fun x _ => ?_)
    rw [ih₂ dB _ (E := E.withCtx (Fin.append x.fst (E.ctxAt _ γ)))
      (E' := E'.withCtx (Fin.append x.fst (E'.ctxAt _ γ))) hh
      (by rw [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_withCtx, hc])]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih₁ dB γ hh hc, ih₂ dB γ hh hc]
  | Dedup q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih₁ dB γ hh hc, ih₂ dB γ hh hc]
  | Explode k h q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate, ih₀ dB γ hh hc]
    exact muSumFix_congr (fun X => ih₁ dB γ (E := E.assignHole s X) (E' := E'.assignHole s X)
      (by simp only [EvalEnv.assignHole, hh]) hc) rfl
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate, ih₀ dB γ hh hc]
    refine congrArg _ (muFix_congr (fun X => ?_))
    rw [ih₁ dB γ (E := E.assignHole s (X.map GenRow.ofAnnotated))
      (E' := E'.assignHole s (X.map GenRow.ofAnnotated))
      (by simp only [EvalEnv.assignHole, hh]) hc]
  | Gamma is ts fs q keep ord ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate,
        ih dB γ hh hc]
  | GammaScalar ts fs q ord ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate,
        ih dB γ hh hc]
  | GammaNest is his p f q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate,
        ih dB γ hh hc]
  | ProvSum is his t q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Retag h q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | GammaTok is his ts fs a q keep ih =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Win P O o w t f q hrr dist keep ih =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate]
    rw [ih dB γ hh hc]

/-- **An apply whose left side has regular columns** reads its right side
as a query with nothing bound, in the plain context of the left row: a
context of regular values is what the environment-free reading gives. -/
theorem AggQueryIn.evaluate_Apply_reg {n₁ n₂ : ℕ} {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁)) (q₂ : AggQueryIn T n₁ n₂ κ₂)
    (d : AnnotatedDatabase T K) :
    (AggQueryIn.Apply q₁ q₂).evaluate d
      = (q₁.evaluate d).bind (fun x =>
          (q₂.evaluate d (GenRow.plainTuple x.fst)).map (fun y =>
            (⟨Fin.append x.fst y.fst,
              ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
              : GenRow T K (n₁ + n₂)))) := by
  rw [AggQueryIn.evaluate_Apply]
  refine Multiset.bind_congr (fun x hx => ?_)
  have hconf := AggQueryIn.evaluate_conform q₁ d x hx
  refine congrArg (Multiset.map _) (AggQueryIn.evaluate_congr_env q₂ d _ rfl ?_)
  rw [EvalEnv.ctxAt_withCtx_cast _ (Nat.add_zero n₁), EvalEnv.empty_ctxAt]
  funext i
  rw [show Fin.cast (Nat.add_zero n₁).symm i = Fin.castAdd 0 i from rfl, Fin.append_left]
  have hk := hconf i
  cases hxi : x.fst i with
  | inl w =>
    rw [EvalEnv.empty_ctxAt]
    simp only [GenRow.plainTuple, hxi]
    rfl
  | inr a => rw [hxi] at hk; cases hk


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
  | Param pv ρ =>
    intro d θ D γ
    simp only [AggQueryIn.substMap, AggQueryIn.evaluatePlain]
    refine congrArg (fun u => ({u} : Multiset _)) (funext fun k => ?_)
    cases pv k <;> rfl
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
  | @Gamma cI m n₁ n₂ _lab _rd is ts fs q keep ord ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun g _ => ?_)
    refine congrArg (Fin.append g) (funext fun j => congrArg (fs j) ?_)
    exact List.map_congr_left (fun v _ => TermIn.eval_substMap θ (ts j) v γ)
  | @GammaScalar cI m n₂ _lab _rd ts fs q ord ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine congrArg (fun t => (Multiset.ofList [t] : Relation T n₂)) ?_
    funext j
    exact congrArg (fs j)
      (List.map_congr_left (fun v _ => TermIn.eval_substMap θ (ts j) v γ))
  | @GammaNest cI m n₁ κ' _lab _rd is his p f q ih =>
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
  | @GammaTok cI m n₁ n₂ κ' _lab _rd is his ts fs a q keep ih =>
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
  | @Win cI n' m' p' κw _lab _rd P O o w t f q hrr dist keep ih =>
    intro d θ D γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluatePlain]
    rw [ih θ D γ]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    refine congrArg (fun v => (Fin.snoc u v : Tuple T (n' + 1))) ?_
    rcases keep with _ | φ <;>
      exact congrArg (if dist then f.distinct else f)
        (List.map_congr_left (fun v _ => TermIn.eval_substMap θ t v γ))
  | @WinExpr cI n' m' p' na _lab _rd P O o ws ts fs g q keeps ih =>
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
theorem ValueFrame.windowGenRow_substMap {c d n m p : ℕ} (lab : ℕ) (ck : List T)
    (θ : Fin c → T ⊕ Fin d) (κ : Fin n → ColKind) (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (keep : Option (Selection T n))
    (X : AnnotatedRelation T K n) (x : GenRow T K n) (γ : Fin d → T)
    (dist : Bool) :
    ValueFrame.windowGenRow lab ck κ P O o w (t.substMap θ) f keep X x γ dist
      = ValueFrame.windowGenRow lab ck κ P O o w t f keep X x (substVal θ γ) dist := by
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

/-! ## The parameters a substituted query reads

A family records the values of the parameters its operator reads, so a
substitution moves the family exactly when it moves those values. A
*renaming* – every outer column sent to an outer column, in order – moves
nothing: the substituted operator reads the renamed columns, which hold
the same values in the same order. That is the substitution an apply's
right side is read through (`applyOuter`). A substitution sending a
parameter to a constant does change the family: the constant is no
parameter of the substituted operator, so its value leaves the family. -/

omit [ValueType T] in
/-- A substitution that renames the outer columns, in order. -/
def IsRenaming {c d : ℕ} (θ : Fin c → T ⊕ Fin d) : Prop :=
  ∃ e : Fin c → Fin d, StrictMono e ∧ ∀ k, θ k = Sum.inr (e k)

omit [ValueType T] in
theorem TermIn.readsOuter_substMap {c d n : ℕ} (θ : Fin c → T ⊕ Fin d) (j : Fin d) :
    ∀ t : TermIn T c n,
      (t.substMap θ).readsOuter j = true ↔ ∃ k, θ k = Sum.inr j ∧ t.readsOuter k = true
  | .const _ => by simp [TermIn.substMap, TermIn.readsOuter]
  | .index _ => by simp [TermIn.substMap, TermIn.readsOuter]
  | .outer k => by
    cases h : θ k with
    | inl a =>
      simp only [TermIn.substMap, h, Sum.elim_inl, TermIn.readsOuter, Bool.false_eq_true,
        false_iff, not_exists, not_and, decide_eq_true_eq]
      rintro k' hk' rfl
      rw [h] at hk'; exact Sum.inl_ne_inr hk'
    | inr i =>
      simp only [TermIn.substMap, h, Sum.elim_inr, TermIn.readsOuter, decide_eq_true_eq]
      constructor
      · rintro rfl; exact ⟨k, h, rfl⟩
      · rintro ⟨k', hk', rfl⟩; rw [h] at hk'; exact Sum.inr.inj hk'
  | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ | .coalesce t₁ t₂ => by
    simp only [TermIn.substMap, TermIn.readsOuter, Bool.or_eq_true,
      TermIn.readsOuter_substMap θ j t₁, TermIn.readsOuter_substMap θ j t₂]
    constructor
    · rintro (⟨k, h, h'⟩ | ⟨k, h, h'⟩) <;> exact ⟨k, h, by simp [h']⟩
    · rintro ⟨k, h, h' | h'⟩
      exacts [Or.inl ⟨k, h, h'⟩, Or.inr ⟨k, h, h'⟩]
  | .caseWhen _ t₁ t₂ t₃ t₄ => by
    simp only [TermIn.substMap, TermIn.readsOuter, Bool.or_eq_true,
      TermIn.readsOuter_substMap θ j t₁, TermIn.readsOuter_substMap θ j t₂,
      TermIn.readsOuter_substMap θ j t₃, TermIn.readsOuter_substMap θ j t₄]
    constructor
    · rintro (((⟨k, h, h'⟩ | ⟨k, h, h'⟩) | ⟨k, h, h'⟩) | ⟨k, h, h'⟩) <;>
        exact ⟨k, h, by simp [h']⟩
    · rintro ⟨k, h, ((h' | h') | h') | h'⟩
      exacts [Or.inl (Or.inl (Or.inl ⟨k, h, h'⟩)), Or.inl (Or.inl (Or.inr ⟨k, h, h'⟩)),
        Or.inl (Or.inr ⟨k, h, h'⟩), Or.inr ⟨k, h, h'⟩]

omit [ValueType T] in
theorem TermGIn.readsOuter_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (j : Fin d) :
    ∀ t : TermGIn T c κ,
      (t.substMap θ).readsOuter j = true ↔ ∃ k, θ k = Sum.inr j ∧ t.readsOuter k = true
  | .const _ => by simp [TermGIn.substMap, TermGIn.readsOuter]
  | .index _ _ => by simp [TermGIn.substMap, TermGIn.readsOuter]
  | .provIndex _ _ => by simp [TermGIn.substMap, TermGIn.readsOuter]
  | .cmpAgg _ _ _ t => by
    simp only [TermGIn.substMap, TermGIn.readsOuter]
    exact TermGIn.readsOuter_substMap θ j t
  | .outer k => by
    cases h : θ k with
    | inl a =>
      simp only [TermGIn.substMap, h, Sum.elim_inl, TermGIn.readsOuter, Bool.false_eq_true,
        false_iff, not_exists, not_and, decide_eq_true_eq]
      rintro k' hk' rfl
      rw [h] at hk'; exact Sum.inl_ne_inr hk'
    | inr i =>
      simp only [TermGIn.substMap, h, Sum.elim_inr, TermGIn.readsOuter, decide_eq_true_eq]
      constructor
      · rintro rfl; exact ⟨k, h, rfl⟩
      · rintro ⟨k', hk', rfl⟩; rw [h] at hk'; exact Sum.inr.inj hk'
  | .chiGate _ t₁ t₂ | .add t₁ t₂ | .sub t₁ t₂ | .mul t₁ t₂ | .coalesce t₁ t₂ => by
    simp only [TermGIn.substMap, TermGIn.readsOuter, Bool.or_eq_true,
      TermGIn.readsOuter_substMap θ j t₁, TermGIn.readsOuter_substMap θ j t₂]
    constructor
    · rintro (⟨k, h, h'⟩ | ⟨k, h, h'⟩) <;> exact ⟨k, h, by simp [h']⟩
    · rintro ⟨k, h, h' | h'⟩
      exacts [Or.inl ⟨k, h, h'⟩, Or.inr ⟨k, h, h'⟩]
  | .caseWhen _ t₁ t₂ t₃ t₄ => by
    simp only [TermGIn.substMap, TermGIn.readsOuter, Bool.or_eq_true,
      TermGIn.readsOuter_substMap θ j t₁, TermGIn.readsOuter_substMap θ j t₂,
      TermGIn.readsOuter_substMap θ j t₃, TermGIn.readsOuter_substMap θ j t₄]
    constructor
    · rintro (((⟨k, h, h'⟩ | ⟨k, h, h'⟩) | ⟨k, h, h'⟩) | ⟨k, h, h'⟩) <;>
        exact ⟨k, h, by simp [h']⟩
    · rintro ⟨k, h, ((h' | h') | h') | h'⟩
      exacts [Or.inl (Or.inl (Or.inl ⟨k, h, h'⟩)), Or.inl (Or.inl (Or.inr ⟨k, h, h'⟩)),
        Or.inl (Or.inr ⟨k, h, h'⟩), Or.inr ⟨k, h, h'⟩]

omit [ValueType T] in
private theorem reads_or {ι : Type} {P : ι → Prop} {A' B' : ι → Prop} {A B : Prop}
    (hA : A ↔ ∃ k, P k ∧ A' k) (hB : B ↔ ∃ k, P k ∧ B' k) :
    (A ∨ B) ↔ ∃ k, P k ∧ (A' k ∨ B' k) := by
  simp only [hA, hB]
  constructor
  · rintro (⟨k, h, h'⟩ | ⟨k, h, h'⟩)
    exacts [⟨k, h, Or.inl h'⟩, ⟨k, h, Or.inr h'⟩]
  · rintro ⟨k, h, h' | h'⟩
    exacts [Or.inl ⟨k, h, h'⟩, Or.inr ⟨k, h, h'⟩]

omit [ValueType T] in
private theorem reads_any {ι : Type} {m : ℕ} {P : ι → Prop} {a : Fin m → ι → Prop}
    {A : Fin m → Prop} (hA : ∀ i, A i ↔ ∃ k, P k ∧ a i k) :
    (∃ i, A i) ↔ ∃ k, P k ∧ ∃ i, a i k := by
  simp only [hA]
  constructor
  · rintro ⟨i, k, h, h'⟩; exact ⟨k, h, i, h'⟩
  · rintro ⟨k, h, i, h'⟩; exact ⟨i, k, h, h'⟩

omit [ValueType T] in
theorem GenPredIn.readsOuter_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (j : Fin d) :
    ∀ φ : GenPredIn T c κ,
      (φ.substMap θ).readsOuter j = true ↔ ∃ k, θ k = Sum.inr j ∧ φ.readsOuter k = true
  | .cmp _ t₁ t₂ => by
    simp only [GenPredIn.substMap, GenPredIn.readsOuter, Bool.or_eq_true]
    exact reads_or (TermGIn.readsOuter_substMap θ j t₁) (TermGIn.readsOuter_substMap θ j t₂)
  | .aggCmp _ _ _ t => by
    simp only [GenPredIn.substMap, GenPredIn.readsOuter]
    exact TermGIn.readsOuter_substMap θ j t
  | .aggRange _ _ _ t₁ _ t₂ => by
    simp only [GenPredIn.substMap, GenPredIn.readsOuter, Bool.or_eq_true]
    exact reads_or (TermGIn.readsOuter_substMap θ j t₁) (TermGIn.readsOuter_substMap θ j t₂)
  | .and φ ψ | .or φ ψ => by
    simp only [GenPredIn.substMap, GenPredIn.readsOuter, Bool.or_eq_true]
    exact reads_or (GenPredIn.readsOuter_substMap θ j φ) (GenPredIn.readsOuter_substMap θ j ψ)
  | .not φ => by
    simp only [GenPredIn.substMap, GenPredIn.readsOuter]
    exact GenPredIn.readsOuter_substMap θ j φ

omit [ValueType T] in
theorem ProjColIn.readsOuter_substMap {c d n : ℕ} {κ : Fin n → ColKind}
    (θ : Fin c → T ⊕ Fin d) (j : Fin d) :
    ∀ p : ProjColIn T c κ,
      (p.substMap θ).readsOuter j = true ↔ ∃ k, θ k = Sum.inr j ∧ p.readsOuter k = true
  | .term t => TermGIn.readsOuter_substMap θ j t
  | .provTerm t => TermGIn.readsOuter_substMap θ j t
  | .token _ _ => by simp [ProjColIn.substMap, ProjColIn.readsOuter]
  | .aggTerm _ _ _ => by simp [ProjColIn.substMap, ProjColIn.readsOuter]
  | .aggTermOf _ _ _ => by simp [ProjColIn.substMap, ProjColIn.readsOuter]

omit [ValueType T] in
@[simp] theorem AggQueryIn.readsOuter_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).readsOuter = q.readsOuter := by
  subst h; rfl

omit [ValueType T] in
/-- The substitution an apply's right side is read through sends an
ambient parameter `k` to `n₁ + k` exactly where the source sends `k` there. -/
theorem lift_eq_inr_natAdd {c d n₁ : ℕ} (θ : Fin c → T ⊕ Fin d) (j : Fin d)
    (k' : Fin (n₁ + c)) :
    Fin.append (fun k => (Sum.inr (Fin.castAdd d k) : T ⊕ Fin (n₁ + d)))
        (fun i => Sum.map id (Fin.natAdd n₁) (θ i)) k' = Sum.inr (Fin.natAdd n₁ j)
      ↔ ∃ k, k' = Fin.natAdd n₁ k ∧ θ k = Sum.inr j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k'
  · rw [Fin.append_left]
    constructor
    · intro h
      have := congrArg Fin.val (Sum.inr.inj h)
      simp at this; omega
    · rintro ⟨k, hk, -⟩
      exact absurd (congrArg Fin.val hk) (by simp; omega)
  · rw [Fin.append_right]
    constructor
    · intro h
      refine ⟨i, rfl, ?_⟩
      cases hθ : θ i with
      | inl a => rw [hθ] at h; exact absurd h (by simp)
      | inr b =>
        rw [hθ] at h
        simp only [Sum.map_inr, Sum.inr.injEq] at h
        rw [Fin.natAdd_inj] at h; rw [h]
    · rintro ⟨k, hk, hθ⟩
      rw [Fin.natAdd_inj] at hk; subst hk
      rw [hθ]; rfl

omit [ValueType T] in
/-- **The parameters a substituted query reads** are the images of those it
read that the substitution sends to parameters. -/
theorem AggQueryIn.readsOuter_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d) (j : Fin d),
      (q.substMap θ).readsOuter j = true ↔ ∃ k, θ k = Sum.inr j ∧ q.readsOuter k = true := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intro d θ j; simp [AggQueryIn.substMap, AggQueryIn.readsOuter]
  | Hole _ _ _ => intro d θ j; simp [AggQueryIn.substMap, AggQueryIn.readsOuter]
  | Empty => intro d θ j; simp [AggQueryIn.substMap, AggQueryIn.readsOuter]
  | Param pv ρ =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, List.any_eq_true,
      List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, hi⟩
      cases hp : pv i with
      | inl a => rw [hp] at hi; simp at hi
      | inr k =>
        rw [hp] at hi
        cases hθ : θ k with
        | inl a => simp [hθ] at hi
        | inr b =>
          simp only [hθ, _root_.Sum.elim_inr, decide_eq_true_eq] at hi
          subst hi
          exact ⟨k, hθ, i, by simp [hp]⟩
    · rintro ⟨k, hθ, i, hi⟩
      refine ⟨i, ?_⟩
      cases hp : pv i with
      | inl a => rw [hp] at hi; simp at hi
      | inr k' =>
        rw [hp] at hi
        simp only [_root_.Sum.elim_inr, decide_eq_true_eq] at hi
        subst hi
        simp [hθ]
  | Proj ps q ih =>
    intro d θ j
    rw [AggQueryIn.substMap, AggQueryIn.readsOuter_castKind]
    simp only [AggQueryIn.readsOuter, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
      true_and]
    exact reads_or (reads_any (fun i => ProjColIn.readsOuter_substMap θ j (ps i))) (ih θ j)
  | Sel φ q _ ih =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true]
    exact reads_or (GenPredIn.readsOuter_substMap θ j φ) (ih θ j)
  | Prod q₁ q₂ ih₁ ih₂ | Sum q₁ q₂ ih₁ ih₂ | Diff q₁ q₂ ih₁ ih₂ =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true]
    exact reads_or (ih₁ θ j) (ih₂ θ j)
  | Mu s q₀ q₁ ih₀ ih₁ | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true]
    exact reads_or (ih₀ θ j) (ih₁ θ j)
  | @Apply cI n₁ n₂ κ₁ κ₂ _ q₁ q₂ ih₁ ih₂ =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true]
    refine reads_or (ih₁ θ j) ((ih₂ _ (Fin.natAdd n₁ j)).trans ?_)
    constructor
    · rintro ⟨k', hk', hr⟩
      obtain ⟨k, rfl, hθ⟩ := (lift_eq_inr_natAdd θ j k').mp hk'
      exact ⟨k, hθ, hr⟩
    · rintro ⟨k, hθ, hr⟩
      exact ⟨Fin.natAdd n₁ k, (lift_eq_inr_natAdd θ j _).mpr ⟨k, rfl, hθ⟩, hr⟩
  | Dedup q ih | Explode _ _ q ih | Retag _ q ih =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter]
    exact ih θ j
  | Gamma is ts fs q keep ord ih | GammaScalar ts fs q ord ih | WinExpr _ _ _ _ ts _ _ q _ ih =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true,
      List.any_eq_true, List.mem_finRange, true_and]
    exact reads_or (reads_any (fun i => TermIn.readsOuter_substMap θ j (ts i))) (ih θ j)
  | GammaNest _ _ p _ q ih =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true]
    exact reads_or (ProjColIn.readsOuter_substMap θ j p) (ih θ j)
  | ProvSum _ _ t q ih =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true]
    exact reads_or (TermGIn.readsOuter_substMap θ j t) (ih θ j)
  | Win _ _ _ _ t _ q _ _ _ ih =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true]
    exact reads_or (TermIn.readsOuter_substMap θ j t) (ih θ j)
  | GammaTok _ _ ts _ a q _ ih =>
    intro d θ j
    simp only [AggQueryIn.substMap, AggQueryIn.readsOuter, Bool.or_eq_true,
      List.any_eq_true, List.mem_finRange, true_and]
    exact reads_or (reads_or (reads_any (fun i => TermIn.readsOuter_substMap θ j (ts i)))
      (TermGIn.readsOuter_substMap θ j a)) (ih θ j)

omit [ValueType T] in
theorem ctxKey_eq_map_filter {c : ℕ} {α : Type} (r : Fin c → Bool) (γ : Fin c → α) :
    ctxKey r γ = ((List.finRange c).filter r).map γ := by
  unfold ctxKey
  induction List.finRange c with
  | nil => rfl
  | cons k l ih =>
    by_cases h : r k = true
    · simp [h, ih]
    · simp [h, ih]

omit [ValueType T] in
/-- **A renaming moves no value of a family**: the substituted operator
reads, in order, the renamed parameters, which hold the same values. -/
theorem ctxKey_of_renaming {c d : ℕ} {α : Type} {e : Fin c → Fin d} (he : StrictMono e)
    (r : Fin c → Bool) (r' : Fin d → Bool) (hr : ∀ j, r' j = true ↔ ∃ k, e k = j ∧ r k = true)
    (γ : Fin d → α) : ctxKey r' γ = ctxKey r (γ ∘ e) := by
  rw [ctxKey_eq_map_filter, ctxKey_eq_map_filter, ← List.map_map]
  congr 1
  refine List.SortedLT.eq_of_mem_iff ?_ ?_ (fun j => ?_)
  · exact List.sortedLT_iff_pairwise.mpr
      ((List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange d)).filter _)
  · refine List.sortedLT_iff_pairwise.mpr (List.Pairwise.map _ (fun a b h => he h) ?_)
    exact (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange c)).filter _
  · simp only [List.mem_filter, List.mem_finRange, true_and, List.mem_map, hr]
    exact ⟨fun ⟨k, h1, h2⟩ => ⟨k, h2, h1⟩, fun ⟨k, h1, h2⟩ => ⟨k, h2, h1⟩⟩

omit [ValueType T] in
/-- The substitution an apply's right side reads through is a renaming
when the outer one is. -/
theorem IsRenaming.lift {c d n₁ : ℕ} {θ : Fin c → T ⊕ Fin d} (hθ : IsRenaming θ) :
    IsRenaming (Fin.append (fun k => (Sum.inr (Fin.castAdd d k) : T ⊕ Fin (n₁ + d)))
      (fun j => Sum.map id (Fin.natAdd n₁) (θ j))) := by
  obtain ⟨e, he, hθe⟩ := hθ
  refine ⟨Fin.append (Fin.castAdd d) (fun j => Fin.natAdd n₁ (e j)), ?_, fun k => ?_⟩
  · intro a b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;>
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) b <;> intro hab <;>
      simp only [Fin.append_left, Fin.append_right] <;>
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hab ⊢
    · exact hab
    · omega
    · omega
    · have h' : e i < e i' := he (Fin.lt_def.mpr (by omega))
      rw [Fin.lt_def] at h'; omega
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]
    · simp only [Fin.append_right, hθe i, Sum.map_inr]

omit [ValueType T] in
/-- **A renamed operator records the values it recorded.** -/
theorem ctxKey_substRd {c d : ℕ} {θ : Fin c → T ⊕ Fin d} (hθ : IsRenaming θ)
    (rd : Fin c → Bool) (γ : Fin d → T) :
    ctxKey (substRd θ rd) γ = ctxKey rd (substVal θ γ) := by
  obtain ⟨e, he, hθe⟩ := hθ
  have hsub : substVal θ γ = γ ∘ e := funext fun k => by simp [substVal, hθe k]
  rw [hsub]
  refine ctxKey_of_renaming he _ _ (fun j => ?_) γ
  simp only [substRd, decide_eq_true_eq, hθe, Sum.elim_inr]

/-- **Substituting and evaluating is evaluating under the substituted
valuation**, for the annotated semantics. -/
theorem AggQueryIn.evaluate_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d) (_hθ : IsRenaming θ) (dB : AnnotatedDatabase T K)
      (γ : Fin d → T) (E : EvalEnv T K),
      (q.substMap θ).evaluate dB γ E = q.evaluate dB (substVal θ γ) (E.substEnv θ γ) := by
  intro c n κ l q
  induction q with
  | Rel n s => intro d θ hθ dB γ E; rfl
  | Hole n s => intro d θ hθ dB γ E; rfl
  | Param pv ρ =>
    intro d θ hθ dB γ E
    simp only [AggQueryIn.substMap, AggQueryIn.evaluate, EvalEnv.paramRows, EvalEnv.substEnv,
      EvalEnv.ctxAt_withCtx]
    have hu : (fun k => _root_.Sum.elim Sum.inl (E.ctxAt d γ)
        (_root_.Sum.elim Sum.inl θ (pv k)) : Tuple (GenValue T K) _)
        = fun k => _root_.Sum.elim Sum.inl (substCtx θ (E.ctxAt d γ)) (pv k) :=
      funext fun k => by cases pv k <;> rfl
    rw [hu]
  | Empty => intro d θ hθ dB γ E; rfl
  | Proj ps q ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap, AggQueryIn.evaluate_castKind]
    simp only [AggQueryIn.evaluate, ProjColIn.eval_substMap]
    rw [ih θ hθ dB γ E]
  | Sel φ q _ ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, GenPredIn.hasAggAtom_substMap,
      GenPredIn.comparedCols_substMap, GenPredIn.entailsExistence_substMap,
      GenPredIn.predsemJ_substMap]
    rw [ih θ hθ dB γ E]
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ, ite_eq_left hφ]
    · rw [ite_eq_right hφ, ite_eq_right hφ]
      exact Multiset.filter_congr
        (fun r _ => GenPredIn.holds_substMap θ φ r.fst γ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ hθ dB γ E, ih₂ θ hθ dB γ E]
  | @Apply cI n₁ n₂ κ₁ κ₂ _ q₁ q₂ ih₁ ih₂ =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ hθ dB γ E]
    refine Multiset.bind_congr (fun x _ => ?_)
    rw [ih₂ _ hθ.lift dB (Fin.append (GenRow.plainTuple x.fst) γ), substVal_append]
    simp only [EvalEnv.substEnv, EvalEnv.ctxAt_withCtx, EvalEnv.withCtx_withCtx,
      substCtx_append]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ hθ dB γ E, ih₂ θ hθ dB γ E]
  | Dedup q ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih θ hθ dB γ E]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate]
    rw [ih₁ θ hθ dB γ E, ih₂ θ hθ dB γ E]
  | Explode k h q ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih θ hθ]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih₀ θ hθ, ih₁ θ hθ, EvalEnv.substEnv_assignHole]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, ih₀ θ hθ, ih₁ θ hθ, EvalEnv.substEnv_assignHole]
  | @Gamma cI m n₁ n₂ _lab rd is ts fs q keep ord ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    have hk := ctxKey_substRd hθ rd γ
    simp only [AggQueryIn.evaluate, hk, AggValue.ofGroup_substMap,
      AggExpr.ofGroupWhen_substMap]
    rw [ih θ hθ dB γ E]
  | @GammaScalar cI m n₂ _lab rd ts fs q ord ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    have hk := ctxKey_substRd hθ rd γ
    simp only [AggQueryIn.evaluate, hk, AggValue.ofScalarGroup_substMap]
    rw [ih θ hθ dB γ E]
  | @GammaNest cI m n₁ κ' _lab rd is his p f q ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    have hk := ctxKey_substRd hθ rd γ
    simp only [AggQueryIn.evaluate, hk, ProjColIn.eval_substMap]
    rw [ih θ hθ dB γ E]
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.evaluate, TermGIn.evalPlain_substMap]
    rw [ih θ hθ dB γ E]
  | Retag h q ih => intro d θ hθ dB γ E; rw [AggQueryIn.substMap]; exact ih θ hθ dB γ E
  | @GammaTok cI m n₁ n₂ κ' _lab rd is his ts fs a q keep ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    have hk := ctxKey_substRd hθ rd γ
    simp only [AggQueryIn.evaluate, hk, AggValue.ofGroup_substMap,
      AggExpr.ofGroupWhen_substMap, TermGIn.evalPlain_substMap]
    rw [ih θ hθ dB γ E]
  | @Win cI n' m' p' κw _lab rd P O o w t f q hrr dist keep ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    have hk := ctxKey_substRd hθ rd γ
    simp only [AggQueryIn.evaluate, hk, ValueFrame.windowGenRow_substMap]
    rw [ih θ hθ dB γ E]
  | @WinExpr cI n' m' p' na _lab rd P O o ws ts fs g q keeps ih =>
    intro d θ hθ dB γ E
    rw [AggQueryIn.substMap]
    have hk := ctxKey_substRd hθ rd γ
    simp only [AggQueryIn.evaluate, hk, ValueFrame.exprOfWhen_substMap]
    rw [ih θ hθ dB γ E]

/-! ## Closing a query: `q[u]` -/

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Evaluating a closed instance is evaluating under the values it was
closed with, in the plain semantics. -/
theorem AggQueryIn.evaluatePlain_subst {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (u : Fin c → T) (q : AggQueryIn T c n κ l) (D : Database T) :
    (q.subst u).evaluatePlain D = q.evaluatePlain D u :=
  AggQueryIn.evaluatePlain_substMap q _ D _

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
  | Param pv ρ => intro d θ; rfl
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

/-! ## Substitution keeps a query well-kinded

A substitution sends a parameter to a constant or to a parameter of the
new context; it keeps the query well-kinded when it sends each parameter
to one of the same kind, a constant being regular. -/

omit [ValueType T] in
theorem TermIn.outerOk_substMap {c d n : ℕ} (θ : Fin c → T ⊕ Fin d) {okc : Fin c → Prop}
    {okd : Fin d → Prop} (hθ : ∀ k, okc k → ∀ j, θ k = Sum.inr j → okd j) :
    ∀ t : TermIn T c n, t.outerOk okc → (t.substMap θ).outerOk okd
  | .const _, _ => trivial
  | .outer k, h => by
    show TermIn.outerOk okd (Sum.elim TermIn.const TermIn.outer (θ k))
    cases hk : θ k with
    | inl a => trivial
    | inr j => exact hθ k h j hk
  | .index _, _ => trivial
  | .add t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩
  | .sub t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩
  | .mul t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩
  | .caseWhen _ t₁ t₂ t₃ t₄, h => ⟨outerOk_substMap θ hθ t₁ h.1,
      outerOk_substMap θ hθ t₂ h.2.1, outerOk_substMap θ hθ t₃ h.2.2.1,
      outerOk_substMap θ hθ t₄ h.2.2.2⟩
  | .coalesce t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩

omit [ValueType T] in
theorem TermGIn.outerOk_substMap {c d n : ℕ} {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d)
    {okc : Fin c → Prop} {okd : Fin d → Prop}
    (hθ : ∀ k, okc k → ∀ j, θ k = Sum.inr j → okd j) :
    ∀ t : TermGIn T c κ, t.outerOk okc → (t.substMap θ).outerOk okd
  | .const _, _ => trivial
  | .outer k, h => by
    show TermGIn.outerOk okd (Sum.elim TermGIn.const TermGIn.outer (θ k))
    cases hk : θ k with
    | inl a => trivial
    | inr j => exact hθ k h j hk
  | .index _ _, _ => trivial
  | .provIndex _ _, _ => trivial
  | .cmpAgg _ _ _ t, h => outerOk_substMap θ hθ t h
  | .chiGate _ t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩
  | .add t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩
  | .sub t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩
  | .mul t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩
  | .caseWhen _ t₁ t₂ t₃ t₄, h => ⟨outerOk_substMap θ hθ t₁ h.1,
      outerOk_substMap θ hθ t₂ h.2.1, outerOk_substMap θ hθ t₃ h.2.2.1,
      outerOk_substMap θ hθ t₄ h.2.2.2⟩
  | .coalesce t₁ t₂, h => ⟨outerOk_substMap θ hθ t₁ h.1, outerOk_substMap θ hθ t₂ h.2⟩

omit [ValueType T] in
theorem GenPredIn.outerOk_substMap {c d n : ℕ} {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d)
    {okc : Fin c → Prop} {okd : Fin d → Prop}
    (hθ : ∀ k, okc k → ∀ j, θ k = Sum.inr j → okd j) :
    ∀ φ : GenPredIn T c κ, φ.outerOk okc → (φ.substMap θ).outerOk okd
  | .cmp _ t₁ t₂, h =>
    ⟨TermGIn.outerOk_substMap θ hθ t₁ h.1, TermGIn.outerOk_substMap θ hθ t₂ h.2⟩
  | .aggCmp _ _ _ t, h => TermGIn.outerOk_substMap θ hθ t h
  | .aggRange _ _ _ t₁ _ t₂, h =>
    ⟨TermGIn.outerOk_substMap θ hθ t₁ h.1, TermGIn.outerOk_substMap θ hθ t₂ h.2⟩
  | .and φ ψ, h => ⟨outerOk_substMap θ hθ φ h.1, outerOk_substMap θ hθ ψ h.2⟩
  | .or φ ψ, h => ⟨outerOk_substMap θ hθ φ h.1, outerOk_substMap θ hθ ψ h.2⟩
  | .not φ, h => outerOk_substMap θ hθ φ h

omit [ValueType T] in
theorem ProjColIn.outerOk_substMap {c d n : ℕ} {κ : Fin n → ColKind} (θ : Fin c → T ⊕ Fin d)
    {okc : Fin c → Prop} {okd : Fin d → Prop}
    (hθ : ∀ k, okc k → ∀ j, θ k = Sum.inr j → okd j) :
    ∀ p : ProjColIn T c κ, p.outerOk okc → (p.substMap θ).outerOk okd
  | .term t, h => TermGIn.outerOk_substMap θ hθ t h
  | .token _ _, _ => trivial
  | .aggTerm _ _ _, _ => trivial
  | .aggTermOf _ _ _, _ => trivial
  | .provTerm t, h => TermGIn.outerOk_substMap θ hθ t h

omit [ValueType T] in
@[simp] theorem AggQueryIn.wellKinded_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) {ρc : Fin c → ColKind}
    {HK : HoleKinds} : (q.castKind h).wellKinded ρc HK ↔ q.wellKinded ρc HK := by
  subst h; exact Iff.rfl

omit [ValueType T] in
/-- **Substitution keeps the query well-kinded**, sending each parameter to
a constant (regular) or to a parameter of the same kind. -/
theorem AggQueryIn.wellKinded_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {d : ℕ} (θ : Fin c → T ⊕ Fin d) {ρc : Fin c → ColKind} {ρd : Fin d → ColKind}
      {HK : HoleKinds},
      (∀ k, (ρc k).base = _root_.Sum.elim (fun _ => ColKind.reg) (fun j => (ρd j).base) (θ k)) →
      q.wellKinded ρc HK → (q.substMap θ).wellKinded ρd HK := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intro d θ ρc ρd HK _ h; exact h
  | Hole _ _ _ => intro d θ ρc ρd HK _ h; exact h
  | Param pv ρ =>
    intro d θ ρc ρd HK hθ h k
    show (ρ k).base = _root_.Sum.elim (fun _ => ColKind.reg) (fun j => (ρd j).base)
      (_root_.Sum.elim Sum.inl θ (pv k))
    rw [h k]
    cases pv k with
    | inl a => rfl
    | inr j => exact hθ j
  | Empty => intro d θ ρc ρd HK _ h; exact h
  | Proj ps q ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    rw [AggQueryIn.substMap, AggQueryIn.wellKinded_castKind]
    exact ⟨fun j => ProjColIn.outerOk_substMap θ hok (ps j) (h.1 j), ih θ hθ h.2⟩
  | Sel φ q hφ ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨GenPredIn.outerOk_substMap θ hok φ h.1, ih θ hθ h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => intro d θ ρc ρd HK hθ h; exact ⟨ih₁ θ hθ h.1, ih₂ θ hθ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l₁
    intro d θ ρc ρd HK hθ h
    refine ⟨ih₁ θ hθ h.1, ih₂ _ (fun k => ?_) h.2⟩
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Fin.append_left]
      show _ = (Fin.append κ₁ ρd (Fin.castAdd d i)).base
      rw [Fin.append_left]
    · rw [Fin.append_right, Fin.append_right, hθ j]
      cases θ j with
      | inl a => rfl
      | inr m =>
        show (ρd m).base = (Fin.append κ₁ ρd (Fin.natAdd n₁ m)).base
        rw [Fin.append_right]
  | Sum q₁ q₂ ih₁ ih₂ => intro d θ ρc ρd HK hθ h; exact ⟨ih₁ θ hθ h.1, ih₂ θ hθ h.2⟩
  | Dedup q ih => intro d θ ρc ρd HK hθ h; exact ih θ hθ h
  | Diff q₁ q₂ ih₁ ih₂ => intro d θ ρc ρd HK hθ h; exact ⟨ih₁ θ hθ h.1, ih₂ θ hθ h.2⟩
  | Explode k hk q ih => intro d θ ρc ρd HK hθ h; exact ih θ hθ h
  | Retag hk q ih => intro d θ ρc ρd HK hθ h; exact ih θ hθ h
  | Mu s q₀ q₁ ih₀ ih₁ => intro d θ ρc ρd HK hθ h; exact ⟨ih₀ θ hθ h.1, ih₁ θ hθ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => intro d θ ρc ρd HK hθ h; exact ⟨ih₀ θ hθ h.1, ih₁ θ hθ h.2⟩
  | Gamma is ts fs q keep ord ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨fun j => TermIn.outerOk_substMap θ hok (ts j) (h.1 j), ih θ hθ h.2⟩
  | GammaScalar ts fs q ord ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨fun j => TermIn.outerOk_substMap θ hok (ts j) (h.1 j), ih θ hθ h.2⟩
  | GammaNest is his p f q ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨ProjColIn.outerOk_substMap θ hok p h.1, ih θ hθ h.2⟩
  | ProvSum is his t q ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨TermGIn.outerOk_substMap θ hok t h.1, ih θ hθ h.2⟩
  | GammaTok is his ts fs a q keep ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨fun j => TermIn.outerOk_substMap θ hok (ts j) (h.1 j),
      TermGIn.outerOk_substMap θ hok a h.2.1, ih θ hθ h.2.2⟩
  | Win P O o w t f q hrr dist keep ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨TermIn.outerOk_substMap θ hok t h.1, ih θ hθ h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro d θ ρc ρd HK hθ h
    have hok : ∀ k, (ρc k).base ≠ ColKind.agg → ∀ j, θ k = Sum.inr j → (ρd j).base ≠ ColKind.agg :=
      fun k hk j hj => by rw [hθ k, hj] at hk; exact hk
    exact ⟨fun j => TermIn.outerOk_substMap θ hok (ts j) (h.1 j), ih θ hθ h.2⟩
