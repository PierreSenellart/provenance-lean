/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.SumByMu

/-!
# A window kept as a window over an all-regular input

A pass that re-types every node to regular columns meets a window over
an input holding aggregate columns. The window reads the regular columns
of each row and nothing of the aggregate ones (`ColKind.readTuple`), its
partition, its order, its term, its clause and the tie-break of its peers
all seeing the nulled row; so the window over the re-typed input, which
reads every column, is a different query – two peers that agree on their
regular columns are ordered by their aggregate values there, which an
order-dependent aggregate reads. The window is kept by **doubling** the
input instead: each row is prefixed by its nulled copy, the window is
written over the first block, and the first block is projected away
afterwards. Peers that agree on the nulled row are then listed in an
order the window cannot tell apart, the values it reads being read off
the first block, and `AggQueryIn.evaluatePlain_winKept` is the equality.
-/

variable {T : Type} [ValueType T]

/-! ## A term over a longer row, reading its first block -/

/-- A term widened to a row with `n'` more columns on the right. -/
def TermIn.widen (n' : ℕ) {c k : ℕ} : TermIn T c k → TermIn T c (k + n')
  | .const a => .const a
  | .outer j => .outer j
  | .index i => .index (Fin.castAdd n' i)
  | .add t₁ t₂ => .add (t₁.widen n') (t₂.widen n')
  | .sub t₁ t₂ => .sub (t₁.widen n') (t₂.widen n')
  | .mul t₁ t₂ => .mul (t₁.widen n') (t₂.widen n')
  | .caseWhen op t₁ t₂ t₃ t₄ =>
      .caseWhen op (t₁.widen n') (t₂.widen n') (t₃.widen n') (t₄.widen n')
  | .coalesce t₁ t₂ => .coalesce (t₁.widen n') (t₂.widen n')

/-- It reads the first block. -/
theorem TermIn.eval_widen (n' : ℕ) {c k : ℕ} (t : TermIn T c k)
    (u : Tuple T k) (v : Tuple T n') (γ : Fin c → T) :
    (t.widen n').eval (Fin.append u v) γ = t.eval u γ := by
  induction t with
  | const a => rfl
  | outer j => rfl
  | index i =>
    show (Fin.append u v : Tuple T (k + n')) (Fin.castAdd n' i) = u i
    rw [Fin.append_left]
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

omit [ValueType T] in
theorem TermIn.noFun_widen (n' : ℕ) {c k : ℕ} (t : TermIn T c k) :
    (t.widen n').noFun = t.noFun := by
  cases t <;> rfl

/-- A comparison widened. -/
def BoolTerm.widen (n' : ℕ) {k : ℕ} : BoolTerm T k → BoolTerm T (k + n')
  | .EQ a b => .EQ (a.widen n') (b.widen n')
  | .NE a b => .NE (a.widen n') (b.widen n')
  | .LE a b => .LE (a.widen n') (b.widen n')
  | .LT a b => .LT (a.widen n') (b.widen n')
  | .GE a b => .GE (a.widen n') (b.widen n')
  | .GT a b => .GT (a.widen n') (b.widen n')
  | .SYNEQ a b => .SYNEQ (a.widen n') (b.widen n')
  | .SYNNE a b => .SYNNE (a.widen n') (b.widen n')

theorem BoolTerm.eval3_widen (n' : ℕ) {k : ℕ} (φ : BoolTerm T k)
    (u : Tuple T k) (v : Tuple T n') :
    (φ.widen n').eval3 (Fin.append u v) = φ.eval3 u := by
  have hargs : ∀ ψ : BoolTerm T k,
      ((ψ.widen n').args.1.eval (Fin.append u v) = ψ.args.1.eval u
        ∧ (ψ.widen n').args.2.eval (Fin.append u v) = ψ.args.2.eval u)
      ∧ (ψ.widen n').toCompOp = ψ.toCompOp := by
    intro ψ
    cases ψ <;>
      exact ⟨⟨TermIn.eval_widen n' _ u v _, TermIn.eval_widen n' _ u v _⟩, rfl⟩
  obtain ⟨⟨h₁, h₂⟩, hop⟩ := hargs φ
  unfold BoolTerm.eval3
  rw [h₁, h₂, hop]

omit [ValueType T] in
theorem BoolTerm.noFun_widen (n' : ℕ) {k : ℕ} (φ : BoolTerm T k) :
    (φ.widen n').noFun = φ.noFun := by
  cases φ <;> exact congrArg₂ (· && ·) (TermIn.noFun_widen n' _) (TermIn.noFun_widen n' _)

/-- A selection widened. -/
def Selection.widen (n' : ℕ) {k : ℕ} : Selection T k → Selection T (k + n')
  | .BT b => .BT (b.widen n')
  | .Not φ => .Not (φ.widen n')
  | .And φ₁ φ₂ => .And (φ₁.widen n') (φ₂.widen n')
  | .Or φ₁ φ₂ => .Or (φ₁.widen n') (φ₂.widen n')
  | .True => .True

/-- It keeps the rows whose first block the selection keeps. -/
theorem Selection.keeps_widen (n' : ℕ) {k : ℕ} (φ : Selection T k)
    (u : Tuple T k) (v : Tuple T n') :
    (φ.widen n').keeps (Fin.append u v) = φ.keeps u := by
  have h3 : ∀ ψ : Selection T k,
      (ψ.widen n').eval3 (Fin.append u v) = ψ.eval3 u := by
    intro ψ
    induction ψ with
    | BT b => exact BoolTerm.eval3_widen n' b u v
    | Not φ ih => exact congrArg Kleene.not ih
    | And φ₁ φ₂ ih₁ ih₂ => exact congrArg₂ Kleene.and ih₁ ih₂
    | Or φ₁ φ₂ ih₁ ih₂ => exact congrArg₂ Kleene.or ih₁ ih₂
    | True => rfl
  unfold Selection.keeps
  rw [h3]

omit [ValueType T] in
theorem Selection.noFun_widen (n' : ℕ) {k : ℕ} (φ : Selection T k) :
    (φ.widen n').noFun = φ.noFun := by
  induction φ with
  | BT b => exact BoolTerm.noFun_widen n' b
  | Not φ ih => exact ih
  | And φ₁ φ₂ ih₁ ih₂ => exact congrArg₂ (· && ·) ih₁ ih₂
  | Or φ₁ φ₂ ih₁ ih₂ => exact congrArg₂ (· && ·) ih₁ ih₂
  | True => rfl

omit [ValueType T] in
theorem Selection.noFunOpt_widen (n' : ℕ) {k : ℕ} (keep : Option (Selection T k)) :
    Selection.noFunOpt (keep.map (fun φ => φ.widen n')) = Selection.noFunOpt keep := by
  cases keep with
  | none => rfl
  | some φ => exact Selection.noFun_widen n' φ

/-! ## The two blocks of a doubled row -/

namespace AggQueryIn

/-- The first block of a doubled row. -/
def blockL (n : ℕ) (x : Tuple T (n + n)) : Tuple T n := fun i => x (Fin.castAdd n i)

/-- Its second block. -/
def blockR (n : ℕ) (x : Tuple T (n + n)) : Tuple T n := fun i => x (Fin.natAdd n i)

omit [ValueType T] in
@[simp] theorem blockL_append (n : ℕ) (u v : Tuple T n) :
    blockL n (Fin.append u v) = u := by
  funext i; exact Fin.append_left u v i

omit [ValueType T] in
@[simp] theorem blockR_append (n : ℕ) (u v : Tuple T n) :
    blockR n (Fin.append u v) = v := by
  funext i; exact Fin.append_right u v i

omit [ValueType T] in
theorem append_blockL_blockR (n : ℕ) (x : Tuple T (n + n)) :
    Fin.append (blockL n x) (blockR n x) = x :=
  Fin.append_castAdd_natAdd

/-- Columns of the first block. -/
def castCols (n : ℕ) {m : ℕ} (P : Tuple (Fin n) m) : Tuple (Fin (n + n)) m :=
  fun k => Fin.castAdd n (P k)

omit [ValueType T] in
theorem key_castCols (n : ℕ) {m : ℕ} (P : Tuple (Fin n) m) (x : Tuple T (n + n)) :
    Tuple.key (castCols n P) x = Tuple.key P (blockL n x) := rfl

/-- **The order of rows restricts to their first block**: where a row is
below another in the domain's order, so is its first block (or they are
equal there). -/
theorem blockL_le_blockL {n : ℕ} {x y : Tuple T (n + n)} (h : x ≤ y) :
    blockL n x ≤ blockL n y := by
  rcases h with ⟨i, hj, hi⟩ | rfl
  · induction i using Fin.addCases with
    | left i' =>
      refine Or.inl ⟨i', fun j hji => ?_, hi⟩
      exact hj (Fin.castAdd n j) (by rw [Fin.lt_def] at hji ⊢; simpa using hji)
    | right i' =>
      refine Or.inr (funext fun j => ?_)
      exact hj (Fin.castAdd n j) (by rw [Fin.lt_def]; simp; omega)
  · exact Or.inr rfl

/-- The clause's reading of a doubled row is its reading of the first
block, ties included. -/
theorem readLe_blockL {n p : ℕ} (O : Tuple (Fin n) p) (o : OrderSpec p)
    {x y : Tuple T (n + n)}
    (h : OrderSpec.readLe (Tuple.key (castCols n O)) id o x y = true) :
    OrderSpec.readLe (Tuple.key O) id o (blockL n x) (blockL n y) = true := by
  have h' : (if o.peer (Tuple.key O (blockL n x)) (Tuple.key O (blockL n y)) = true
      then decide (x ≤ y) else o.le (Tuple.key O (blockL n x)) (Tuple.key O (blockL n y)))
        = true := h
  show (if o.peer (Tuple.key O (blockL n x)) (Tuple.key O (blockL n y)) = true
      then decide (blockL n x ≤ blockL n y)
      else o.le (Tuple.key O (blockL n x)) (Tuple.key O (blockL n y))) = true
  by_cases hp : o.peer (Tuple.key O (blockL n x)) (Tuple.key O (blockL n y)) = true
  · rw [ite_eq_left hp] at h' ⊢
    exact decide_eq_true (blockL_le_blockL (of_decide_eq_true h'))
  · rw [ite_eq_right hp] at h' ⊢
    exact h'


/-! ## The frame and the window value read off the first block -/

/-- **The frame of a doubled row, projected on the first block, is the
frame of its first block** in the first blocks: partition and frame
condition read that block only, and the current row is the one row of
the frame projected onto it. -/
theorem frameOf_blockL {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (M : Multiset (Tuple T (n + n))) {x : Tuple T (n + n)} (hx : x ∈ M) :
    (ValueFrame.frameOf (α := Tuple T (n + n)) id (castCols n P) (castCols n O) w M x).map
        (blockL n)
      = ValueFrame.frameOf (α := Tuple T n) id P O w (M.map (blockL n)) (blockL n x) := by
  unfold ValueFrame.frameOf
  simp only [id, key_castCols]
  rw [Multiset.filter_map]
  have hF : Multiset.filter ((fun y => Tuple.key P y = Tuple.key P (blockL n x)
        ∧ w.ρ (Tuple.key O y) (Tuple.key O (blockL n x)) = true) ∘ blockL n) M
      = Multiset.filter (fun y => Tuple.key P (blockL n y) = Tuple.key P (blockL n x)
        ∧ w.ρ (Tuple.key O (blockL n y)) (Tuple.key O (blockL n x)) = true) M :=
    Multiset.filter_congr (fun _ _ => Iff.rfl)
  -- erasing the current row commutes with the projection: a row of the
  -- filtered bag with the same first block as the current row is in the
  -- bag exactly when the current row is
  have herase : Multiset.map (blockL n)
      ((Multiset.filter (fun y => Tuple.key P (blockL n y) = Tuple.key P (blockL n x)
        ∧ w.ρ (Tuple.key O (blockL n y)) (Tuple.key O (blockL n x)) = true) M).erase x)
      = ((Multiset.filter (fun y => Tuple.key P (blockL n y) = Tuple.key P (blockL n x)
        ∧ w.ρ (Tuple.key O (blockL n y)) (Tuple.key O (blockL n x)) = true) M).map (blockL n)).erase
          (blockL n x) := by
    by_cases hxF : x ∈ Multiset.filter (fun y => Tuple.key P (blockL n y) = Tuple.key P (blockL n x)
        ∧ w.ρ (Tuple.key O (blockL n y)) (Tuple.key O (blockL n x)) = true) M
    · convert Multiset.map_erase_of_mem (blockL n) _ hxF using 2
    · rw [Multiset.erase_instEq _ (fun a b => instDecidableEqTuple a b),
        Multiset.erase_of_notMem hxF,
        Multiset.erase_instEq _ (fun a b => instDecidableEqTuple a b),
        Multiset.erase_of_notMem]
      intro hmem
      obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.mp hmem
      have hyp := (Multiset.mem_filter.mp hy).2
      rw [hyx] at hyp
      exact hxF (Multiset.mem_filter.mpr ⟨hx, hyp⟩)
  rw [hF]
  by_cases hs : w.s (Tuple.key O (blockL n x)) = true
  · rw [ite_eq_left hs, ite_eq_left hs, Multiset.map_cons]
    congr 1
    convert herase using 2
    exact Multiset.erase_instEq _ _ _ _
  · rw [ite_eq_right hs, ite_eq_right hs]
    convert herase using 2
    exact Multiset.erase_instEq _ _ _ _

/-- **The window value of a doubled row is the window value of its first
block** over the first blocks: the two listings of the frame, sorted by
the clause with ties by the row, differ only in the order of rows with
equal first blocks, which read alike. -/
theorem windowValueOpt_blockL {c n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (keep : Option (Selection T n)) (M : Multiset (Tuple T (n + n))) {x : Tuple T (n + n)}
    (hx : x ∈ M) (γ : Fin c → T) :
    ValueFrame.windowValueOpt (castCols n P) (castCols n O) o w (t.widen n) f
        (keep.map (fun φ => φ.widen n)) M x γ
      = ValueFrame.windowValueOpt P O o w t f keep (M.map (blockL n)) (blockL n x) γ := by
  -- the two listings of the frame
  set L₂ : List (Tuple T (n + n)) := ValueFrame.frameListOf (α := Tuple T (n + n)) id
    (castCols n P) (castCols n O) o w M x with hL₂
  set L₁ : List (Tuple T n) := ValueFrame.frameListOf (α := Tuple T n) id P O o w
    (M.map (blockL n)) (blockL n x) with hL₁
  have hperm : (L₂.map (blockL n)).Perm L₁ := by
    have h₂ : ((L₂.map (blockL n) : List (Tuple T n)) : Multiset (Tuple T n))
        = (ValueFrame.frameOf (α := Tuple T (n + n)) id (castCols n P) (castCols n O) w M x).map
            (blockL n) := by
      rw [hL₂, ValueFrame.frameListOf, ← Multiset.map_coe,
        Multiset.coe_eq_coe.mpr (OrderSpec.sortSeq_perm _), sortList_coe]
    have h₁ : ((L₁ : List (Tuple T n)) : Multiset (Tuple T n))
        = ValueFrame.frameOf (α := Tuple T n) id P O w (M.map (blockL n)) (blockL n x) := by
      rw [hL₁, ValueFrame.frameListOf, Multiset.coe_eq_coe.mpr (OrderSpec.sortSeq_perm _),
        sortList_coe]
    exact Multiset.coe_eq_coe.mp (h₂.trans ((frameOf_blockL P O w M hx).trans h₁.symm))
  have hsorted₂ : (L₂.map (blockL n)).Pairwise
      (fun a b => OrderSpec.readLe (Tuple.key O) id o a b = true) :=
    (OrderSpec.sortSeq_sorted _).map _ (fun _ _ h => readLe_blockL O o h)
  have hsorted₁ : L₁.Pairwise (fun a b => OrderSpec.readLe (Tuple.key O) id o a b = true) :=
    OrderSpec.sortSeq_sorted _
  have hval : ∀ v : Tuple T (n + n), (t.widen n).eval v γ = t.eval (blockL n v) γ := by
    intro v
    rw [← append_blockL_blockR n v, TermIn.eval_widen, blockL_append]
  cases keep with
  | none =>
    show f (L₂.map (fun v => (t.widen n).eval v γ)) = f (L₁.map (fun v => t.eval v γ))
    rw [show L₂.map (fun v => (t.widen n).eval v γ)
        = (L₂.map (blockL n)).map (fun v => t.eval v γ) from by
      rw [List.map_map]; exact List.map_congr_left (fun v _ => hval v)]
    exact congrArg f (OrderSpec.map_eq_of_sorted (val := id) (fun v => t.eval v γ) hperm
      hsorted₂ hsorted₁)
  | some φ =>
    show f ((L₂.filter (φ.widen n).keeps).map (fun v => (t.widen n).eval v γ))
      = f ((L₁.filter φ.keeps).map (fun v => t.eval v γ))
    have hkeep : ∀ v : Tuple T (n + n), (φ.widen n).keeps v = φ.keeps (blockL n v) := by
      intro v
      rw [← append_blockL_blockR n v, Selection.keeps_widen, blockL_append]
    rw [show (L₂.filter (φ.widen n).keeps).map (fun v => (t.widen n).eval v γ)
        = ((L₂.map (blockL n)).filter φ.keeps).map (fun v => t.eval v γ) from by
      rw [List.filter_map,
        show List.filter (φ.keeps ∘ blockL n) L₂ = List.filter (φ.widen n).keeps L₂ from
          List.filter_congr (fun v _ => by rw [Function.comp_apply, hkeep])]
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => hval v)]
    exact congrArg f (OrderSpec.map_eq_of_sorted (val := id) (fun v => t.eval v γ)
      (hperm.filter _) (hsorted₂.filter _) (hsorted₁.filter _))


/-! ## The window, kept -/

variable {c : ℕ}

theorem doubled_kinds (n : ℕ) (κ : Fin n → ColKind) :
    (fun j => (Fin.append (nullCols (T := T) (c := c) κ)
        (fun i : Fin n => (ProjColIn.term (TermGIn.index i rfl)
          : ProjColIn T c (ColKind.allReg n))) j).kind)
      = ColKind.allReg (n + n) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    unfold nullCols
    split <;> rfl
  · rw [Fin.append_right]
    rfl

/-- **The doubled input**: each row prefixed by its nulled copy, the
aggregate columns read as `0` as the window reads them. -/
def doubled {n : ℕ} (κ : Fin n → ColKind) (q : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c (n + n) (ColKind.allReg (n + n)) :=
  (AggQueryIn.Proj (Fin.append (nullCols κ)
      (fun i : Fin n => ProjColIn.term (TermGIn.index i rfl))) q).castKind (doubled_kinds n κ)

theorem evaluatePlain_doubled {n : ℕ} (κ : Fin n → ColKind)
    (q : AggQueryIn T c n (ColKind.allReg n)) (D : Database T) (γ : Fin c → T) :
    (doubled κ q).evaluatePlain D γ
      = (q.evaluatePlain D γ : Multiset (Tuple T n)).map
          (fun u => (Fin.append (ColKind.readTuple κ u) u : Tuple T (n + n))) := by
  rw [doubled, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  refine Multiset.map_congr rfl (fun u _ => funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · show (Fin.append (nullCols κ) _ (Fin.castAdd n i)).evalPlain u γ = _
    rw [Fin.append_left, Fin.append_left]
    exact congrFun (evalPlain_nullCols κ u γ) i
  · show (Fin.append (nullCols κ) _ (Fin.natAdd n i)).evalPlain u γ = _
    rw [Fin.append_right, Fin.append_right]
    rfl

/-- The columns kept after the window: the second block and the window's
column. -/
def keptCols (n : ℕ) :
    Tuple (ProjColIn T c (Fin.snoc (ColKind.allReg (n + n)) ColKind.agg)) (n + 1) :=
  Fin.snoc (α := fun _ => ProjColIn T c (Fin.snoc (ColKind.allReg (n + n)) ColKind.agg))
    (fun i : Fin n => ProjColIn.term (TermGIn.index (Fin.castSucc (Fin.natAdd n i))
      (by rw [Fin.snoc_castSucc]; rfl)))
    (ProjColIn.token (Fin.last (n + n)) (Fin.snoc_last _ _))

omit [ValueType T] in
theorem keptCols_kinds (n : ℕ) :
    (fun j => (keptCols (T := T) (c := c) n j).kind) = Fin.snoc (ColKind.allReg n) ColKind.agg := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [keptCols, Fin.snoc_last]; rfl
  · simp only [keptCols, Fin.snoc_castSucc]; rfl

/-- **A window over an input of any kinds, written over an all-regular
input computing the same rows**: the window over the doubled input,
reading its first block – partition, order, term and clause moved there –
and the first block then dropped. -/
def winKept {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (κ : Fin n → ColKind)
    (q : AggQueryIn T c n (ColKind.allReg n)) (dist : Bool) (keep : Option (Selection T n)) :
    AggQueryIn T c (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  (AggQueryIn.Proj (keptCols n)
    (AggQueryIn.Win (lab := 0) (rd := fun _ => false) (castCols n P) (castCols n O) o w (t.widen n)
        f (doubled κ q)
      (winReadsReg_allReg _ _ _) dist (keep.map (fun φ => φ.widen n)))).castKind (keptCols_kinds n)

/-- **It computes the window**, whatever the kinds of the input it stands
for, as long as the rows agree. -/
theorem evaluatePlain_winKept {lab : ℕ} {rd} {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    {κ : Fin n → ColKind} (q₀ : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t)
    (q : AggQueryIn T c n (ColKind.allReg n)) (dist : Bool) (keep : Option (Selection T n))
    (D : Database T) (γ : Fin c → T)
    (hq : (q₀.evaluatePlain D γ : Multiset (Tuple T n)) = q.evaluatePlain D γ) :
    (winKept P O o w t f κ q dist keep).evaluatePlain D γ
      = (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q₀ hrr dist
          keep).evaluatePlain D γ := by
  rw [winKept, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  rw [evaluatePlain_doubled, ColKind.map_readTuple_allReg, Multiset.map_map, Multiset.map_map,
    hq]
  refine Multiset.map_congr rfl (fun u hu => funext fun j => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Function.comp_apply, keptCols, Fin.snoc_last, ProjColIn.evalPlain,
      ColKind.readTuple_allReg]
    rw [windowValueOpt_blockL P O o w t _ keep _ (Multiset.mem_map.mpr ⟨u, hu, rfl⟩) γ,
      Multiset.map_map, blockL_append]
    congr 1
    exact Multiset.map_congr rfl (fun v _ => blockL_append n _ v)
  · simp only [Function.comp_apply, keptCols, Fin.snoc_castSucc, ProjColIn.evalPlain,
      TermGIn.evalPlain, Fin.append_right]


/-! ## What the kept window is made of -/

section KeptStructure

variable {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
  (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (κ : Fin n → ColKind)
  (q : AggQueryIn T c n (ColKind.allReg n)) (dist : Bool) (keep : Option (Selection T n))

theorem usesOnly_winKept {S : Set OpKind} (hwin : OpKind.win ∈ S) (hproj : OpKind.proj ∈ S)
    (hq : q.usesOnly S) : (winKept P O o w t f κ q dist keep).usesOnly S := by
  rw [winKept, AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hproj, fun j => ?_⟩, hwin, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [keptCols, Fin.snoc_last]; rfl
    · simp only [keptCols, Fin.snoc_castSucc]; rfl
  · rw [doubled, AggQueryIn.usesOnly_castKind]
    refine ⟨⟨hproj, fun j => ?_⟩, hq⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      unfold nullCols
      split <;> rfl
    · rw [Fin.append_right]
      rfl

theorem hygienic_winKept (hq : q.hygienic) :
    (winKept P O o w t f κ q dist keep).hygienic := by
  rw [winKept, AggQueryIn.hygienic_castKind]
  show (doubled κ q).hygienic
  rw [doubled, AggQueryIn.hygienic_castKind]
  exact hq

theorem inSig_winKept {Θ : Set (SeqAggFunc T)} (ht : t.noFun = true)
    (hf : if dist then f.distinct ∈ Θ else f ∈ Θ) (hkeep : Selection.noFunOpt keep = true)
    (hq : q.inSig Θ) : (winKept P O o w t f κ q dist keep).inSig Θ := by
  rw [winKept, AggQueryIn.inSig_castKind]
  refine ⟨fun j => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [keptCols, Fin.snoc_last]; rfl
    · simp only [keptCols, Fin.snoc_castSucc]; rfl
  · refine ⟨by rw [TermIn.noFun_widen]; exact ht, hf, by rw [Selection.noFunOpt_widen]; exact hkeep,
      ?_⟩
    rw [doubled, AggQueryIn.inSig_castKind]
    refine ⟨fun j => ?_, hq⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      unfold nullCols
      split <;> rfl
    · rw [Fin.append_right]
      rfl

theorem overSchema_winKept {sch : Schema} (hq : q.overSchema sch) :
    (winKept P O o w t f κ q dist keep).overSchema sch := by
  rw [winKept, AggQueryIn.overSchema_castKind]
  show (doubled κ q).overSchema sch
  rw [doubled, AggQueryIn.overSchema_castKind]
  exact hq

theorem names_winKept : (winKept P O o w t f κ q dist keep).names = q.names := by
  rw [winKept, AggQueryIn.names_castKind]
  show (doubled κ q).names = _
  rw [doubled, AggQueryIn.names_castKind]
  rfl

theorem noMention_winKept (s : String) (hq : q.noMention s) :
    (winKept P O o w t f κ q dist keep).noMention s := by
  rw [winKept, AggQueryIn.noMention_castKind]
  show (doubled κ q).noMention s
  rw [doubled, AggQueryIn.noMention_castKind]
  exact hq

theorem sumsAllReg_winKept (hq : q.sumsAllReg) :
    (winKept P O o w t f κ q dist keep).sumsAllReg := by
  rw [winKept, AggQueryIn.sumsAllReg_castKind]
  show (doubled κ q).sumsAllReg
  rw [doubled, AggQueryIn.sumsAllReg_castKind]
  exact hq

theorem settlesAt_winKept (D : Database T) (γ : Fin c → T) (hq : q.SettlesAt D γ) :
    (winKept P O o w t f κ q dist keep).SettlesAt D γ := by
  rw [winKept, AggQueryIn.settlesAt_castKind]
  show (doubled κ q).SettlesAt D γ
  rw [doubled, AggQueryIn.settlesAt_castKind]
  exact hq

end KeptStructure

end AggQueryIn
