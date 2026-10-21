module

public import Provenance.SymRel
public import Provenance.Genericity
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Terms and predicates over symbolic rows

A term of the minimal signature is a column, a parameter, a value of the
ambient context or a constant (`Sym.CS`, read off a term by
`Sym.termCS`). On a symbolic row each is a cell: a column's cell, the
parameter's cell of the descriptor, or the constant cell of a value of
the context or of the query (`Sym.CS.sa`). Where the values involved are
good – components of the parameter row, values of the cut, or the null –
the cell read on the encoding of a row is the encoding of the term's
value (`Sym.CS.eval_sa`), and a predicate translated cell by cell
(`Sym.transPred`) has the three-valued truth of the original on the
decoded row (`Sym.eval3_transPred`).
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

variable {k c n : ℕ}

/-- **Where a term's value comes from**: a column of the row, a parameter
component, a value of the ambient context, or a constant. -/
inductive CS (T : Type) (k c n : ℕ) where
  | col (i : Fin n) : CS T k c n
  | par (i : Fin k) : CS T k c n
  | amb (j : Fin c) : CS T k c n
  | const (a : T) : CS T k c n

/-- What it reads under a parameter row, a context and an output row. -/
def CS.val (par : Fin k → T) (γ : Fin c → T) (v : Tuple T n) : CS T k c n → T
  | .col i => v i
  | .par i => par i
  | .amb j => γ j
  | .const a => a

/-- **The columns of a concrete cell**, with its value column given. -/
def concCols {m : ℕ} (vcol : SA T c m) : Fin (7 + k) → SA T c m :=
  Fin.append ![.const 0, vcol, .const 0, .const 0, .const 0, .const sLo, .const sHi]
    (fun _ => .const 0)

/-- The column of cell `i`, column `j`, of a symbolic row with `P` more
columns after its cells. -/
def cc {N : ℕ} (P : ℕ) (i : Fin N) (j : Fin (7 + k)) : Fin (N * (7 + k) + P) :=
  Fin.castAdd P (ci i j)

/-- **The cell a source reads**, on a symbolic row of `k + n` cells and
`P` more columns. -/
def CS.sa (P : ℕ) : CS T k c n → Fin (7 + k) → SA T c ((k + n) * (7 + k) + P)
  | .col i => fun j => .col (cc P (Fin.natAdd k i) j)
  | .par i => fun j => .col (cc P (Fin.castAdd n i) j)
  | .amb j => concCols (.amb j)
  | .const a => concCols (.const a)

/-- The symbolic row of a parameter row and an output row, with `P` more
columns. -/
noncomputable def rowEncP (C : Finset T) (par : Fin k → T) (v : Tuple T n) {P : ℕ}
    (e : Tuple T P) : Tuple T ((k + n) * (7 + k) + P) :=
  Fin.append (rowEnc C par v) e

theorem concCols_eval {m : ℕ} (C : Finset T) (vcol : SA T c m) (r : Tuple T m) (γ : Fin c → T)
    (i : Fin (7 + k)) :
    (concCols vcol i).eval r γ = enc C k (.conc (vcol.eval r γ)) i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [concCols, enc, Fin.append_left]
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
  · simp only [concCols, enc, Fin.append_right]; rfl

/-- **A source's cell, read on an encoded row, encodes the source's value**,
where the value is good. -/
theorem CS.eval_sa {C : Finset T} (P : ℕ) (s : CS T k c n) (par : Fin k → T) (γ : Fin c → T)
    (v : Tuple T n) (e : Tuple T P)
    (hs : ∀ a, (s = .amb a → γ a ∈ C ∨ ValueType.isNull (γ a) = true))
    (hc : ∀ a, (s = .const a → a ∈ C ∨ ValueType.isNull a = true)) (i : Fin (7 + k)) :
    (s.sa P i).eval (rowEncP C par v e) γ = enc C k (vcode C par (s.val par γ v)) i := by
  cases s with
  | col j =>
    show (Fin.append (rowEnc C par v) e) (Fin.castAdd P (ci (Fin.natAdd k j) i)) = _
    rw [Fin.append_left]
    show cellOf (rowEnc C par v) (Fin.natAdd k j) i = _
    rw [rowEnc, cellOf_ofCells, Fin.append_right]; rfl
  | par j =>
    show (Fin.append (rowEnc C par v) e) (Fin.castAdd P (ci (Fin.castAdd n j) i)) = _
    rw [Fin.append_left]
    show cellOf (rowEnc C par v) (Fin.castAdd n j) i = _
    rw [rowEnc, cellOf_ofCells, Fin.append_left]
    show _ = enc C k (vcode C par (par j)) i
    rw [vcode_par]
  | amb j =>
    rw [CS.sa, concCols_eval]
    show _ = enc C k (vcode C par (γ j)) i
    rw [vcode_of_mem par (hs j rfl)]; rfl
  | const a =>
    rw [CS.sa, concCols_eval]
    show _ = enc C k (vcode C par a) i
    rw [vcode_of_mem par (hc a rfl)]; rfl

/-! ## Terms -/

/-- A value of the cut, or the null. -/
def CG (C : Finset T) (a : T) : Prop := a ∈ C ∨ ValueType.isNull a = true

/-- **The source of a term**: its column, parameter, context value or
constant. A term with a function (outside the minimal signature) reads
as the constant `0`. -/
def termCS {κ : Fin n → ColKind} : TermGIn T (k + c) κ → CS T k c n
  | .const a => .const a
  | .outer o => Fin.addCases (motive := fun _ => CS T k c n) (fun i => .par i) (fun j => .amb j) o
  | .index i _ => .col i
  | .provIndex i _ => .col i
  | _ => .const 0

theorem termCS_val {κ : Fin n → ColKind} (t : TermGIn T (k + c) κ) (ht : t.noFun = true)
    (par : Fin k → T) (γ : Fin c → T) (v : Tuple T n) :
    (termCS t).val par γ v = t.evalPlain v (Fin.append par γ) := by
  cases t with
  | const a => rfl
  | outer o =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) o
    · show (termCS (TermGIn.outer (Fin.castAdd c i))).val par γ v
        = Fin.append par γ (Fin.castAdd c i)
      rw [Fin.append_left]; simp [termCS, CS.val]
    · show (termCS (TermGIn.outer (Fin.natAdd k j))).val par γ v = Fin.append par γ (Fin.natAdd k j)
      rw [Fin.append_right]; simp [termCS, CS.val]
  | index i _ => rfl
  | provIndex i _ => rfl
  | _ => simp [TermGIn.noFun] at ht

/-- The constant a term's source names is one of the term's. -/
theorem termCS_const {κ : Fin n → ColKind} (t : TermGIn T (k + c) κ) (ht : t.noFun = true)
    {a : T} (h : termCS t = .const a) : a ∈ t.consts := by
  cases t with
  | const b => cases h; exact Finset.mem_singleton_self _
  | outer o =>
    refine Fin.addCases (fun i h => ?_) (fun j h => ?_) o h
    · simp [termCS] at h
    · simp [termCS] at h
  | index i _ => cases h
  | provIndex i _ => cases h
  | _ => simp [TermGIn.noFun] at ht

/-- **The source of a projection column.** A column applying an
arbitrary function (outside every signature) reads as the constant `0`. -/
def projCS {κ : Fin n → ColKind} : ProjColIn T (k + c) κ → CS T k c n
  | .term t => termCS t
  | .token i _ => .col i
  | .aggTerm _ _ _ => .const 0
  | .aggTermOf i _ t =>
    match t with
    | .const a => .const a
    | .outer _ => .col i
    | _ => .const 0
  | .provTerm t => termCS t

theorem projCS_val {κ : Fin n → ColKind} (p : ProjColIn T (k + c) κ) (hp : p.noFun = true)
    (par : Fin k → T) (γ : Fin c → T) (v : Tuple T n) :
    (projCS p).val par γ v = p.evalPlain v (Fin.append par γ) := by
  cases p with
  | term t => exact termCS_val t hp par γ v
  | token i _ => rfl
  | aggTerm _ _ _ => simp [ProjColIn.noFun] at hp
  | aggTermOf i _ t =>
    cases t with
    | const a => rfl
    | outer j =>
      show v i = (TermIn.outer j : TermIn T 1 0).eval (fun j => j.elim0) (fun _ => v i)
      rfl
    | index j => exact j.elim0
    | _ => simp [ProjColIn.noFun, TermIn.noFun] at hp
  | provTerm t => exact termCS_val t hp par γ v

theorem projCS_const {κ : Fin n → ColKind} (p : ProjColIn T (k + c) κ) (hp : p.noFun = true)
    {a : T} (h : projCS p = .const a) : a ∈ p.consts := by
  cases p with
  | term t => exact termCS_const t hp h
  | token i _ => cases h
  | aggTerm _ _ _ => simp [ProjColIn.noFun] at hp
  | aggTermOf i _ t =>
    cases t with
    | const b => cases h; exact Finset.mem_singleton_self _
    | outer j => cases h
    | index j => exact j.elim0
    | _ => simp [ProjColIn.noFun, TermIn.noFun] at hp
  | provTerm t => exact termCS_const t hp h

/-- **A source's value is good** where the row, the context and the
constants are. -/
theorem goodVal_val {C : Finset T} (s : CS T k c n) (par : Fin k → T) (γ : Fin c → T)
    (v : Tuple T n) (hv : ∀ i, GoodVal (C := C) par (v i)) (hamb : ∀ j, CG C (γ j))
    (hc : ∀ a, s = .const a → CG C a) : GoodVal (C := C) par (s.val par γ v) := by
  cases s with
  | col i => exact hv i
  | par i => exact Or.inl ⟨i, rfl⟩
  | amb j => exact Or.inr (hamb j)
  | const a => exact Or.inr (hc a rfl)

/-! ## Predicates -/

/-- **A predicate over a symbolic row**, cell by cell. -/
def transPred (P : ℕ) {κ : Fin n → ColKind} :
    GenPredIn T (k + c) κ → SP T c ((k + n) * (7 + k) + P)
  | .cmp op t₁ t₂ => cellCmp op ((termCS t₁).sa P) ((termCS t₂).sa P)
  | .aggCmp i _ op t => cellCmp op ((CS.col i : CS T k c n).sa P) ((termCS t).sa P)
  | .aggRange i _ op₁ t₁ op₂ t₂ =>
      .and (cellCmp op₁ ((CS.col i : CS T k c n).sa P) ((termCS t₁).sa P))
        (cellCmp op₂ ((CS.col i : CS T k c n).sa P) ((termCS t₂).sa P))
  | .and φ ψ => .and (transPred P φ) (transPred P ψ)
  | .or φ ψ => .or (transPred P φ) (transPred P ψ)
  | .not φ => .not (transPred P φ)

/-- One comparison between two sources, read on an encoded row. -/
theorem eval3_cellCmp_cs {C : Finset T} (P : ℕ) (op : CompOp) (s₁ s₂ : CS T k c n)
    (par : Fin k → T) (γ : Fin c → T) (v : Tuple T n) (e : Tuple T P)
    (hv : ∀ i, GoodVal (C := C) par (v i)) (hamb : ∀ j, CG C (γ j))
    (hc₁ : ∀ a, s₁ = .const a → CG C a) (hc₂ : ∀ a, s₂ = .const a → CG C a) :
    (cellCmp op (s₁.sa P) (s₂.sa P)).eval3 (rowEncP C par v e) γ
      = op.eval3 (s₁.val par γ v) (s₂.val par γ v) := by
  rw [eval3_cellCmp op _ _ _ γ (codeOK_vcode (goodVal_val s₁ par γ v hv hamb hc₁))
    (codeOK_vcode (goodVal_val s₂ par γ v hv hamb hc₂))
    (CS.eval_sa P s₁ par γ v e (fun a h => by cases h; exact hamb a) hc₁)
    (CS.eval_sa P s₂ par γ v e (fun a h => by cases h; exact hamb a) hc₂),
    dec_vcode, dec_vcode]

/-- **The translated predicate has the original's three-valued truth** on
the encoding of a row, where the values involved are good. -/
theorem eval3_transPred {C : Finset T} (P : ℕ) {κ : Fin n → ColKind}
    (φ : GenPredIn T (k + c) κ) (hφ : φ.noFun = true) (hφc : ∀ a ∈ φ.consts, CG C a)
    (par : Fin k → T) (γ : Fin c → T) (v : Tuple T n) (e : Tuple T P)
    (hv : ∀ i, GoodVal (C := C) par (v i)) (hamb : ∀ j, CG C (γ j)) :
    (transPred P φ).eval3 (rowEncP C par v e) γ = φ.evalPlain3 v (Fin.append par γ) := by
  have htc : ∀ (t : TermGIn T (k + c) κ), t.noFun = true → (∀ a ∈ t.consts, CG C a) →
      ∀ a, termCS t = .const a → CG C a := fun t ht htc a h => htc a (termCS_const t ht h)
  induction φ with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    rw [transPred, eval3_cellCmp_cs P op _ _ par γ v e hv hamb
      (htc t₁ hφ.1 (fun a ha => hφc a (Finset.mem_union_left _ ha)))
      (htc t₂ hφ.2 (fun a ha => hφc a (Finset.mem_union_right _ ha))),
      termCS_val _ hφ.1, termCS_val _ hφ.2]
    rfl
  | aggCmp i hi op t =>
    rw [transPred, eval3_cellCmp_cs P op _ _ par γ v e hv hamb (fun a h => by cases h)
      (htc t hφ hφc), termCS_val _ hφ]
    rfl
  | aggRange i hi op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    show (SP.eval3 _ _ _).and (SP.eval3 _ _ _) = _
    rw [eval3_cellCmp_cs P op₁ _ _ par γ v e hv hamb (fun a h => by cases h)
      (htc t₁ hφ.1 (fun a ha => hφc a (Finset.mem_union_left _ ha))),
      eval3_cellCmp_cs P op₂ _ _ par γ v e hv hamb (fun a h => by cases h)
      (htc t₂ hφ.2 (fun a ha => hφc a (Finset.mem_union_right _ ha))),
      termCS_val _ hφ.1, termCS_val _ hφ.2]
    rfl
  | and φ ψ ihφ ihψ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    show (SP.eval3 _ _ _).and (SP.eval3 _ _ _) = _
    rw [ihφ hφ.1 (fun a ha => hφc a (Finset.mem_union_left _ ha)),
      ihψ hφ.2 (fun a ha => hφc a (Finset.mem_union_right _ ha))]
    rfl
  | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.noFun, Bool.and_eq_true] at hφ
    show (SP.eval3 _ _ _).or (SP.eval3 _ _ _) = _
    rw [ihφ hφ.1 (fun a ha => hφc a (Finset.mem_union_left _ ha)),
      ihψ hφ.2 (fun a ha => hφc a (Finset.mem_union_right _ ha))]
    rfl
  | not φ ih =>
    show (SP.eval3 _ _ _).not = _
    rw [ih hφ hφc]
    rfl

/-! ## Classical selections -/

/-- **The source of a term of a classical selection.** -/
def termCST : TermIn T 0 n → CS T k 0 n
  | .const a => .const a
  | .index i => .col i
  | _ => .const 0

theorem termCST_val (t : TermIn T 0 n) (ht : t.noFun = true) (par : Fin k → T)
    (γ : Fin 0 → T) (v : Tuple T n) :
    (termCST (k := k) t).val par γ v = t.eval v := by
  cases t with
  | const a => rfl
  | outer j => exact j.elim0
  | index i => rfl
  | _ => simp [TermIn.noFun] at ht

theorem termCST_const (t : TermIn T 0 n) (ht : t.noFun = true) {a : T}
    (h : termCST (k := k) t = .const a) : a ∈ t.consts := by
  cases t with
  | const b => cases h; exact Finset.mem_singleton_self _
  | outer j => exact j.elim0
  | index i => cases h
  | _ => simp [TermIn.noFun] at ht

/-- **A classical selection over a symbolic row**, cell by cell. -/
def transSel (P : ℕ) : Selection T n → SP T 0 ((k + n) * (7 + k) + P)
  | .BT b => cellCmp b.toCompOp ((termCST (k := k) b.args.1).sa P) ((termCST b.args.2).sa P)
  | .Not φ => .not (transSel P φ)
  | .And φ ψ => .and (transSel P φ) (transSel P ψ)
  | .Or φ ψ => .or (transSel P φ) (transSel P ψ)
  | .True => .tru

/-- **The translated selection keeps the encodings of the rows the
selection keeps**, where the values involved are good. -/
theorem eval3_transSel {C : Finset T} (P : ℕ) (φ : Selection T n) (hφ : φ.noFun = true)
    (hφc : ∀ a ∈ φ.consts, CG C a) (par : Fin k → T) (v : Tuple T n) (e : Tuple T P)
    (hv : ∀ i, GoodVal (C := C) par (v i)) (γ : Fin 0 → T) :
    (transSel P φ).eval3 (rowEncP C par v e) γ = φ.eval3 v := by
  induction φ with
  | BT b =>
    simp only [Selection.noFun, BoolTerm.noFun, Bool.and_eq_true] at hφ
    rw [transSel, eval3_cellCmp_cs P _ _ _ par γ v e hv (fun j => j.elim0)
      (fun a h => hφc a (by
        show a ∈ Union.union _ _
        exact Finset.mem_union_left _ (termCST_const _ hφ.1 h)))
      (fun a h => hφc a (by
        show a ∈ Union.union _ _
        exact Finset.mem_union_right _ (termCST_const _ hφ.2 h))),
      termCST_val _ hφ.1, termCST_val _ hφ.2]
    rfl
  | Not φ ih =>
    show (SP.eval3 _ _ _).not = _
    rw [ih hφ hφc]; rfl
  | And φ ψ ihφ ihψ =>
    simp only [Selection.noFun, Bool.and_eq_true] at hφ
    show (SP.eval3 _ _ _).and (SP.eval3 _ _ _) = _
    rw [ihφ hφ.1 (fun a ha => hφc a (Finset.mem_union_left _ ha)),
      ihψ hφ.2 (fun a ha => hφc a (Finset.mem_union_right _ ha))]
    rfl
  | Or φ ψ ihφ ihψ =>
    simp only [Selection.noFun, Bool.and_eq_true] at hφ
    show (SP.eval3 _ _ _).or (SP.eval3 _ _ _) = _
    rw [ihφ hφ.1 (fun a ha => hφc a (Finset.mem_union_left _ ha)),
      ihψ hφ.2 (fun a ha => hφc a (Finset.mem_union_right _ ha))]
    rfl
  | True => rfl

/-! ## Projections onto symbolic rows -/

/-- **A projection by arguments**: each output column one argument. -/
def projSA {N M : ℕ} (f : Fin M → SA T c N) : Tuple (ProjColIn T c (ColKind.allReg N)) M :=
  fun x => .term (f x).toG

omit [ValueType T] in
theorem projSA_kind {N M : ℕ} (f : Fin M → SA T c N) :
    (fun x => (projSA f x).kind) = ColKind.allReg M := rfl

theorem evalPlain_projSA {N M : ℕ} (f : Fin M → SA T c N) (r : Tuple T N) (γ : Fin c → T)
    (x : Fin M) : (projSA f x).evalPlain r γ = (f x).eval r γ :=
  SA.evalPlain_toG _ r γ

/-- **The argument of an output column of a symbolic projection**: the
descriptor's cells copied, then the sources' cells, then the further
columns copied. -/
def symProjSA (P : ℕ) {m : ℕ} (srcs : Fin m → CS T k c n) :
    Fin ((k + m) * (7 + k) + P) → SA T c ((k + n) * (7 + k) + P) :=
  Fin.addCases
    (fun y => Fin.addCases (motive := fun _ => SA T c ((k + n) * (7 + k) + P))
      (fun i₀ => (CS.par i₀ : CS T k c n).sa P (finProdFinEquiv.symm y).2)
      (fun i₁ => (srcs i₁).sa P (finProdFinEquiv.symm y).2) (finProdFinEquiv.symm y).1)
    (fun z => .col (Fin.natAdd _ z))

theorem rowEncP_cc (C : Finset T) (par : Fin k → T) (v : Tuple T n) {P : ℕ} (e : Tuple T P)
    (i : Fin (k + n)) (j : Fin (7 + k)) :
    rowEncP C par v e (cc P i j)
      = (Fin.append (fun i => enc C k (code C par i))
          (fun j => enc C k (vcode C par (v j))) i) j := by
  show Fin.append (rowEnc C par v) e (Fin.castAdd P (ci i j)) = _
  rw [Fin.append_left]
  show cellOf (rowEnc C par v) i j = _
  rw [rowEnc, cellOf_ofCells]

/-- **A symbolic projection maps the encoding of a row to the encoding of
the projected row**, where the values involved are good. -/
theorem eval_symProjSA {C : Finset T} (P : ℕ) {m : ℕ} (srcs : Fin m → CS T k c n)
    (par : Fin k → T) (γ : Fin c → T) (v : Tuple T n) (e : Tuple T P)
    (hamb : ∀ j, CG C (γ j)) (hc : ∀ j a, srcs j = .const a → CG C a) :
    (fun x => (symProjSA P srcs x).eval (rowEncP C par v e) γ)
      = rowEncP C par (fun j => (srcs j).val par γ v) e := by
  funext x
  refine Fin.addCases (fun y => ?_) (fun z => ?_) x
  · rw [symProjSA, Fin.addCases_left]
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
    rw [Equiv.symm_apply_apply]
    show _ = rowEncP C par (fun j => (srcs j).val par γ v) e (cc P i j)
    rw [rowEncP_cc]
    refine Fin.addCases (fun i₀ => ?_) (fun i₁ => ?_) i
    · rw [Fin.addCases_left, Fin.append_left,
        CS.eval_sa P _ par γ v e (fun _ h => by cases h) (fun _ h => by cases h)]
      show enc C k (vcode C par (par i₀)) j = _
      rw [vcode_par]
    · rw [Fin.addCases_right, Fin.append_right,
        CS.eval_sa P _ par γ v e (fun a h => by rw [h] at *; exact hamb a) (hc i₁)]
  · rw [symProjSA, Fin.addCases_right]
    show Fin.append (rowEnc C par v) e (Fin.natAdd _ z) = Fin.append _ e (Fin.natAdd _ z)
    rw [Fin.append_right, Fin.append_right]

end Sym
