module

public import Provenance.SymCode
public import Provenance.AggQuery
import Mathlib.Data.Sym.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Codes as columns, and comparisons between them

A code (`Provenance.SymCode`) is stored in `7 + k` columns, `k` the number
of parameter components: a flag saying whether the code is fresh, the
value (or the gap's lower bound, the least value of the cut for the gap
below it), a flag for the gap below the least value, the gap's upper bound
and a flag for the gap above the greatest, two columns placing the code
against its value – before it, at it or after it, which is what an order
on cells reads – and the rank written in unary over the two constants `0`
and `ValueType.nonzero` taken in increasing order (`Sym.therm`).

A comparison between two cells is a predicate over their columns
(`Sym.cellCmp`), written in a small syntax of comparisons over columns,
constants and the ambient context (`Sym.SP`) that compiles both to the
general predicates (`Sym.SP.toGen`) and to the classical selections of a
`FILTER` clause (`Sym.SP.toSel`). Its three-valued truth on the
encodings of two codes is exactly that of the comparison between the
values they stand for (`Sym.eval3_cellCmp`), unknown included: a
comparison with the null is unknown whatever the code it is compared
with.
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

/-! ## Comparisons over columns, constants and the context -/

/-- **An argument of a comparison**: a constant, a column, or a value of
the context. -/
inductive SA (T : Type) (c n : ℕ) where
  | const (a : T) : SA T c n
  | col (i : Fin n) : SA T c n
  | amb (j : Fin c) : SA T c n

/-- What an argument reads on a row in a context. -/
def SA.eval {c n : ℕ} : SA T c n → Tuple T n → (Fin c → T) → T
  | .const a, _, _ => a
  | .col i, u, _ => u i
  | .amb j, _, γ => γ j

/-- **A predicate of comparisons**, the shape every translated comparison
has. -/
inductive SP (T : Type) (c n : ℕ) where
  | atom (op : CompOp) (a b : SA T c n) : SP T c n
  | and (p q : SP T c n) : SP T c n
  | or (p q : SP T c n) : SP T c n
  | not (p : SP T c n) : SP T c n
  | tru : SP T c n
  | fls : SP T c n

/-- Its three-valued truth. -/
def SP.eval3 {c n : ℕ} : SP T c n → Tuple T n → (Fin c → T) → Kleene
  | .atom op a b, u, γ => op.eval3 (a.eval u γ) (b.eval u γ)
  | .and p q, u, γ => (p.eval3 u γ).and (q.eval3 u γ)
  | .or p q, u, γ => (p.eval3 u γ).or (q.eval3 u γ)
  | .not p, u, γ => (p.eval3 u γ).not
  | .tru, _, _ => Kleene.true
  | .fls, _, _ => Kleene.false

/-- An argument as a term of the general syntax over regular columns. -/
def SA.toG {c n : ℕ} : SA T c n → TermGIn T c (ColKind.allReg n)
  | .const a => .const a
  | .col i => .index i rfl
  | .amb j => .outer j

theorem SA.evalPlain_toG {c n : ℕ} (a : SA T c n) (u : Tuple T n) (γ : Fin c → T) :
    a.toG.evalPlain u γ = a.eval u γ := by
  cases a <;> rfl

/-- **The predicate in the general syntax.** -/
def SP.toGen {c n : ℕ} : SP T c n → GenPredIn T c (ColKind.allReg n)
  | .atom op a b => .cmp op a.toG b.toG
  | .and p q => .and p.toGen q.toGen
  | .or p q => .or p.toGen q.toGen
  | .not p => .not p.toGen
  | .tru => .cmp .syneq (.const 0) (.const 0)
  | .fls => .cmp .syneq (.const 0) (.const ValueType.nonzero)

theorem SP.evalPlain3_toGen {c n : ℕ} (p : SP T c n) (u : Tuple T n) (γ : Fin c → T) :
    p.toGen.evalPlain3 u γ = p.eval3 u γ := by
  induction p with
  | atom op a b =>
    show op.eval3 (a.toG.evalPlain u γ) (b.toG.evalPlain u γ) = _
    rw [SA.evalPlain_toG, SA.evalPlain_toG]; rfl
  | and p q ihp ihq =>
    show (p.toGen.evalPlain3 u γ).and (q.toGen.evalPlain3 u γ) = _
    rw [ihp, ihq]; rfl
  | or p q ihp ihq =>
    show (p.toGen.evalPlain3 u γ).or (q.toGen.evalPlain3 u γ) = _
    rw [ihp, ihq]; rfl
  | not p ih =>
    show (p.toGen.evalPlain3 u γ).not = _
    rw [ih]; rfl
  | tru =>
    show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true
    simp [CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool]
  | fls =>
    show CompOp.syneq.eval3 (0 : T) ValueType.nonzero = Kleene.false
    simp [CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool,
      (ValueType.nonzero_ne_zero (T := T)).symm]

/-- A translated predicate reads no aggregate column. -/
theorem SP.hasAggAtom_toGen {c n : ℕ} (p : SP T c n) : p.toGen.hasAggAtom = false := by
  induction p with
  | atom op a b => rfl
  | and p q ihp ihq => show (p.toGen.hasAggAtom || q.toGen.hasAggAtom) = false; rw [ihp, ihq]; rfl
  | or p q ihp ihq => show (p.toGen.hasAggAtom || q.toGen.hasAggAtom) = false; rw [ihp, ihq]; rfl
  | not p ih => exact ih
  | tru => rfl
  | fls => rfl

/-- An argument as a term of a classical selection, where there is no
context. -/
def SA.toT {n : ℕ} : SA T 0 n → Term T n
  | .const a => .const a
  | .col i => .index i
  | .amb j => j.elim0

theorem SA.eval_toT {n : ℕ} (a : SA T 0 n) (u : Tuple T n) (γ : Fin 0 → T) :
    a.toT.eval u = a.eval u γ := by
  cases a with
  | const a => rfl
  | col i => rfl
  | amb j => exact j.elim0

/-- A comparison as a Boolean term. -/
def boolOf {n : ℕ} (op : CompOp) (t₁ t₂ : Term T n) : BoolTerm T n :=
  match op with
  | .eq => .EQ t₁ t₂
  | .ne => .NE t₁ t₂
  | .lt => .LT t₁ t₂
  | .le => .LE t₁ t₂
  | .gt => .GT t₁ t₂
  | .ge => .GE t₁ t₂
  | .syneq => .SYNEQ t₁ t₂
  | .synne => .SYNNE t₁ t₂

theorem eval3_boolOf {n : ℕ} (op : CompOp) (t₁ t₂ : Term T n) (u : Tuple T n) :
    (boolOf op t₁ t₂).eval3 u = op.eval3 (t₁.eval u) (t₂.eval u) := by
  cases op <;> rfl

/-- **The predicate as a classical selection.** -/
def SP.toSel {n : ℕ} : SP T 0 n → Selection T n
  | .atom op a b => .BT (boolOf op a.toT b.toT)
  | .and p q => .And p.toSel q.toSel
  | .or p q => .Or p.toSel q.toSel
  | .not p => .Not p.toSel
  | .tru => .True
  | .fls => .Not .True

theorem SP.eval3_toSel {n : ℕ} (p : SP T 0 n) (u : Tuple T n) (γ : Fin 0 → T) :
    p.toSel.eval3 u = p.eval3 u γ := by
  induction p with
  | atom op a b =>
    show (boolOf op a.toT b.toT).eval3 u = _
    rw [eval3_boolOf, SA.eval_toT, SA.eval_toT]; rfl
  | and p q ihp ihq =>
    show (p.toSel.eval3 u).and (q.toSel.eval3 u) = _
    rw [ihp, ihq]; rfl
  | or p q ihp ihq =>
    show (p.toSel.eval3 u).or (q.toSel.eval3 u) = _
    rw [ihp, ihq]; rfl
  | not p ih =>
    show (p.toSel.eval3 u).not = _
    rw [ih]; rfl
  | tru => rfl
  | fls => rfl

/-! ## The columns of a code -/

/-- The smaller of the two constants. -/
def sLo : T := if (0 : T) < ValueType.nonzero then 0 else ValueType.nonzero

/-- The larger of the two constants. -/
def sHi : T := if (0 : T) < ValueType.nonzero then ValueType.nonzero else 0

/-- **A rank in unary**: `k` columns, the first `r` holding the larger of
the two constants and the others the smaller, so that the ranks are
ordered as their columns are, lexicographically. -/
def therm (k r : ℕ) : Fin k → T := fun j => if j.val < r then sHi else sLo


/-- Whether the gap is below the least value. -/
def wbFlag : WithBot T → T
  | ⊥ => ValueType.nonzero
  | (_ : T) => 0

/-- A gap's upper bound as a column (`0` above the greatest value). -/
def wtVal : WithTop T → T
  | ⊤ => 0
  | (a : T) => a

/-- Whether the gap is above the greatest value. -/
def wtFlag : WithTop T → T
  | ⊤ => ValueType.nonzero
  | (_ : T) => 0

variable (C : Finset T)

/-- **The gap's upper bound**: the least non-null value of the cut above
the lower bound. -/
def upOf (l : WithBot T) : WithTop T :=
  (C.filter (fun t : T => ValueType.isNull t = false ∧ LT.lt l (t : WithBot T))).min

/-- **A gap's lower bound as a column**: the least value of the cut for
the gap below it (`0` if the cut holds no non-null value). -/
def lval : WithBot T → T
  | ⊥ => wtVal (upOf C ⊥)
  | (a : T) => a

/-- **Where a code sits against its value column**, first column: before
it (a gap below the least value), at it (a concrete value), after it (a
gap above its lower bound) read as `(sLo, sLo)`, `(sLo, sHi)`,
`(sHi, sLo)`. -/
def posA : Code T → T
  | .conc _ => sLo
  | .fresh ⊥ _ => sLo
  | .fresh (_ : T) _ => sHi

/-- The second column. -/
def posB : Code T → T
  | .conc _ => sHi
  | .fresh _ _ => sLo

/-- **A code as `7 + k` columns.** -/
def enc (k : ℕ) : Code T → Tuple T (7 + k)
  | .conc a => Fin.append ![0, a, 0, 0, 0, sLo, sHi] (fun _ => 0)
  | .fresh l r => Fin.append
      ![ValueType.nonzero, lval C l, wbFlag l, wtVal (upOf C l), wtFlag (upOf C l),
        posA (.fresh l r), posB (.fresh l r)] (therm k r)

/-- The column of the fresh flag. -/
abbrev iF (k : ℕ) : Fin (7 + k) := Fin.castAdd k 0
/-- The column of the value or of the gap's lower bound. -/
abbrev iV (k : ℕ) : Fin (7 + k) := Fin.castAdd k 1
/-- The column of the below-the-least flag. -/
abbrev iB (k : ℕ) : Fin (7 + k) := Fin.castAdd k 2
/-- The column of the gap's upper bound. -/
abbrev iH (k : ℕ) : Fin (7 + k) := Fin.castAdd k 3
/-- The column of the above-the-greatest flag. -/
abbrev iHB (k : ℕ) : Fin (7 + k) := Fin.castAdd k 4
/-- The first column placing the code against its value. -/
abbrev iSA (k : ℕ) : Fin (7 + k) := Fin.castAdd k 5
/-- The second. -/
abbrev iSB (k : ℕ) : Fin (7 + k) := Fin.castAdd k 6
/-- The `j`-th column of the rank. -/
abbrev iR {k : ℕ} (j : Fin k) : Fin (7 + k) := Fin.natAdd 7 j

variable {C}

@[simp] theorem enc_conc_F (k : ℕ) (a : T) : enc C k (.conc a) (iF k) = 0 := rfl
@[simp] theorem enc_conc_V (k : ℕ) (a : T) : enc C k (.conc a) (iV k) = a := rfl
@[simp] theorem enc_conc_B (k : ℕ) (a : T) : enc C k (.conc a) (iB k) = 0 := rfl
@[simp] theorem enc_conc_R (k : ℕ) (a : T) (j : Fin k) : enc C k (.conc a) (iR j) = 0 := by
  simp [enc, iR]
@[simp] theorem enc_fresh_F (k : ℕ) (l : WithBot T) (r : ℕ) :
    enc C k (.fresh l r) (iF k) = ValueType.nonzero := rfl
@[simp] theorem enc_fresh_V (k : ℕ) (l : WithBot T) (r : ℕ) :
    enc C k (.fresh l r) (iV k) = lval C l := rfl
@[simp] theorem enc_fresh_B (k : ℕ) (l : WithBot T) (r : ℕ) :
    enc C k (.fresh l r) (iB k) = wbFlag l := rfl
@[simp] theorem enc_fresh_R (k : ℕ) (l : WithBot T) (r : ℕ) (j : Fin k) :
    enc C k (.fresh l r) (iR j) = therm k r j := by
  simp [enc, iR]

/-! ## Comparing two cells -/

variable {c n : ℕ}

/-- The argument is `0`. -/
def isZ (a : SA T c n) : SP T c n := .atom .syneq a (.const 0)
/-- The argument is `ValueType.nonzero`. -/
def isN (a : SA T c n) : SP T c n := .atom .syneq a (.const ValueType.nonzero)

/-- **A comparison made strict in a concrete value**: unknown where the
value is null, `Q` elsewhere. -/
def wrap (a : SA T c n) (Q : SP T c n) : SP T c n :=
  .and (.atom .eq a a) (.or Q (.not (.atom .eq a a)))

/-- The disjunction of a list. -/
def orAll : List (SP T c n) → SP T c n
  | List.nil => .fls
  | List.cons p ps => .or p (orAll ps)

/-- The conjunction of a list. -/
def andAll : List (SP T c n) → SP T c n
  | List.nil => .tru
  | List.cons p ps => .and p (andAll ps)

variable {k : ℕ}

/-- The argument is the smaller constant. -/
def isLo (a : SA T c n) : SP T c n := .atom .syneq a (.const sLo)
/-- The argument is the larger constant. -/
def isHi (a : SA T c n) : SP T c n := .atom .syneq a (.const sHi)

/-- The first rank below the second. -/
def thLt (x y : Fin (7 + k) → SA T c n) : SP T c n :=
  orAll ((List.finRange k).map (fun j => .and (isLo (x (iR j))) (isHi (y (iR j)))))

/-- The two ranks equal. -/
def thEq (x y : Fin (7 + k) → SA T c n) : SP T c n :=
  andAll ((List.finRange k).map (fun j => .atom .syneq (x (iR j)) (y (iR j))))

/-- A concrete value below a fresh cell. -/
def ltCF (a : SA T c n) (y : Fin (7 + k) → SA T c n) : SP T c n :=
  .and (isZ (y (iB k))) (.atom .le a (y (iV k)))

/-- A fresh cell below a concrete value. -/
def ltFC (x : Fin (7 + k) → SA T c n) (b : SA T c n) : SP T c n :=
  .not (.and (isZ (x (iB k))) (.atom .le b (x (iV k))))

/-- A fresh cell below another. -/
def ltFF (x y : Fin (7 + k) → SA T c n) : SP T c n :=
  .or (.and (isN (x (iB k))) (isZ (y (iB k))))
    (.and (.atom .syneq (x (iB k)) (y (iB k)))
      (.or (.atom .lt (x (iV k)) (y (iV k)))
        (.and (.atom .eq (x (iV k)) (y (iV k))) (thLt x y))))

/-- Two fresh cells equal. -/
def eqFF (x y : Fin (7 + k) → SA T c n) : SP T c n :=
  .and (.atom .syneq (x (iB k)) (y (iB k)))
    (.and (.atom .syneq (x (iV k)) (y (iV k))) (thEq x y))

/-- A concrete value compared with a fresh cell. -/
def branchCF (op : CompOp) (a : SA T c n) (y : Fin (7 + k) → SA T c n) : SP T c n :=
  match op with
  | .eq => wrap a .fls
  | .ne => wrap a .tru
  | .lt => wrap a (ltCF a y)
  | .le => wrap a (ltCF a y)
  | .gt => wrap a (.not (ltCF a y))
  | .ge => wrap a (.not (ltCF a y))
  | .syneq => .fls
  | .synne => .tru

/-- A fresh cell compared with a concrete value. -/
def branchFC (op : CompOp) (x : Fin (7 + k) → SA T c n) (b : SA T c n) : SP T c n :=
  match op with
  | .eq => wrap b .fls
  | .ne => wrap b .tru
  | .lt => wrap b (ltFC x b)
  | .le => wrap b (ltFC x b)
  | .gt => wrap b (.not (ltFC x b))
  | .ge => wrap b (.not (ltFC x b))
  | .syneq => .fls
  | .synne => .tru

/-- Two fresh cells compared. -/
def branchFF (op : CompOp) (x y : Fin (7 + k) → SA T c n) : SP T c n :=
  match op with
  | .eq => eqFF x y
  | .ne => .not (eqFF x y)
  | .lt => ltFF x y
  | .le => .or (ltFF x y) (eqFF x y)
  | .gt => ltFF y x
  | .ge => .or (ltFF y x) (eqFF x y)
  | .syneq => eqFF x y
  | .synne => .not (eqFF x y)

/-- **Two cells compared**: by their values where both are concrete, and
through the bounds and ranks of the codes elsewhere. -/
def cellCmp (op : CompOp) (x y : Fin (7 + k) → SA T c n) : SP T c n :=
  .or (.and (.and (isZ (x (iF k))) (isZ (y (iF k)))) (.atom op (x (iV k)) (y (iV k))))
    (.or (.and (.and (isZ (x (iF k))) (isN (y (iF k)))) (branchCF op (x (iV k)) y))
      (.or (.and (.and (isN (x (iF k))) (isZ (y (iF k)))) (branchFC op x (y (iV k))))
        (.and (.and (isN (x (iF k))) (isN (y (iF k)))) (branchFF op x y))))

/-! ## What a comparison of cells reads -/

theorem nonzero_ne_zero' : (ValueType.nonzero : T) ≠ 0 := ValueType.nonzero_ne_zero

theorem eval3_isZ (a : SA T c n) (u : Tuple T n) (γ : Fin c → T) :
    (isZ a).eval3 u γ = Kleene.ofBool (decide (a.eval u γ = 0)) := by
  show CompOp.syneq.eval3 _ _ = _
  rw [CompOp.eval3_of_not_strict rfl]; rfl

theorem eval3_isN (a : SA T c n) (u : Tuple T n) (γ : Fin c → T) :
    (isN a).eval3 u γ = Kleene.ofBool (decide (a.eval u γ = ValueType.nonzero)) := by
  show CompOp.syneq.eval3 _ _ = _
  rw [CompOp.eval3_of_not_strict rfl]; rfl

theorem eval3_atom_syneq (a b : SA T c n) (u : Tuple T n) (γ : Fin c → T) :
    (SP.atom .syneq a b).eval3 u γ = Kleene.ofBool (decide (a.eval u γ = b.eval u γ)) := by
  show CompOp.syneq.eval3 _ _ = _
  rw [CompOp.eval3_of_not_strict rfl]; rfl

theorem eval3_atom_of_nonNull (op : CompOp) (a b : SA T c n) (u : Tuple T n) (γ : Fin c → T)
    (ha : ValueType.isNull (a.eval u γ) = false) (hb : ValueType.isNull (b.eval u γ) = false) :
    (SP.atom op a b).eval3 u γ = Kleene.ofBool (decide (op.eval (a.eval u γ) (b.eval u γ))) := by
  show CompOp.eval3 _ _ _ = _
  simp [CompOp.eval3, ha, hb]

theorem eval3_orAll (ps : List (SP T c n)) (u : Tuple T n) (γ : Fin c → T)
    (hd : ∀ p ∈ ps, p.eval3 u γ = Kleene.true ∨ p.eval3 u γ = Kleene.false) :
    (orAll ps).eval3 u γ = Kleene.ofBool (decide (∃ p ∈ ps, p.eval3 u γ = Kleene.true)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show (p.eval3 u γ).or ((orAll ps).eval3 u γ) = _
    rw [ih (fun q hq => hd q (List.mem_cons_of_mem _ hq))]
    rcases hd p (List.mem_cons_self) with h | h <;> rw [h]
    · simp [h, Kleene.or, Kleene.ofBool]
    · by_cases hex : ∃ q ∈ ps, q.eval3 u γ = Kleene.true
      · simp [hex, Kleene.or, Kleene.ofBool]
      · have hex' : ¬ ∃ q ∈ p :: ps, q.eval3 u γ = Kleene.true := by
          rintro ⟨q, hq, hqt⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · rw [h] at hqt; exact absurd hqt (by decide)
          · exact hex ⟨q, hq, hqt⟩
        simp only [decide_eq_false hex, decide_eq_false hex']
        rfl

theorem eval3_andAll (ps : List (SP T c n)) (u : Tuple T n) (γ : Fin c → T)
    (hd : ∀ p ∈ ps, p.eval3 u γ = Kleene.true ∨ p.eval3 u γ = Kleene.false) :
    (andAll ps).eval3 u γ = Kleene.ofBool (decide (∀ p ∈ ps, p.eval3 u γ = Kleene.true)) := by
  induction ps with
  | nil => simp [andAll, SP.eval3, Kleene.ofBool]
  | cons p ps ih =>
    show (p.eval3 u γ).and ((andAll ps).eval3 u γ) = _
    rw [ih (fun q hq => hd q (List.mem_cons_of_mem _ hq))]
    rcases hd p (List.mem_cons_self) with h | h <;> rw [h]
    · by_cases hall : ∀ q ∈ ps, q.eval3 u γ = Kleene.true
      · have hall' : ∀ q ∈ p :: ps, q.eval3 u γ = Kleene.true := fun q hq =>
          (List.mem_cons.mp hq).elim (fun h' => h' ▸ h) (hall q)
        simp only [decide_eq_true hall, decide_eq_true hall']
        rfl
      · have hall' : ¬ ∀ q ∈ p :: ps, q.eval3 u γ = Kleene.true :=
          fun h' => hall (fun q hq => h' q (List.mem_cons_of_mem _ hq))
        simp only [decide_eq_false hall, decide_eq_false hall']
        rfl
    · have hall' : ¬ ∀ q ∈ p :: ps, q.eval3 u γ = Kleene.true := fun h' => by
        have := h' p List.mem_cons_self
        rw [h] at this; exact absurd this (by decide)
      simp only [decide_eq_false hall']
      cases decide (∀ q ∈ ps, q.eval3 u γ = Kleene.true) <;> rfl

/-- A unary rank holds its two constants. -/
theorem sLo_ne_sHi : (sLo : T) ≠ sHi := by
  unfold sLo sHi
  split
  · exact nonzero_ne_zero'.symm
  · exact nonzero_ne_zero'

theorem sLo_lt_sHi : LT.lt (sLo : T) sHi := by
  unfold sLo sHi
  split
  · assumption
  · rename_i h
    exact lt_of_le_of_ne (not_lt.mp h) nonzero_ne_zero'

theorem isNull_sLo : ValueType.isNull (sLo : T) = false := by
  unfold sLo; split
  · exact ValueType.isNull_zero
  · exact ValueType.isNull_nonzero

theorem isNull_sHi : ValueType.isNull (sHi : T) = false := by
  unfold sHi; split
  · exact ValueType.isNull_nonzero
  · exact ValueType.isNull_zero

theorem therm_def (k r : ℕ) (j : Fin k) :
    therm (T := T) k r j = sLo ∨ therm (T := T) k r j = sHi := by
  unfold therm; split <;> simp

/-- **Two unary ranks are ordered as the ranks**, below `k`. -/
theorem therm_lt_iff {k r r' : ℕ} (hr : r < k) :
    (∃ j : Fin k, therm (T := T) k r j = sLo ∧ therm (T := T) k r' j = sHi)
      ↔ r < r' := by
  constructor
  · rintro ⟨j, h₁, h₂⟩
    unfold therm at h₁ h₂
    by_cases hj : j.val < r
    · rw [ite_eq_left hj] at h₁; exact absurd h₁.symm sLo_ne_sHi
    · by_cases hj' : j.val < r'
      · omega
      · rw [ite_eq_right hj'] at h₂; exact absurd h₂ sLo_ne_sHi
  · intro h
    refine ⟨⟨r, hr⟩, ?_, ?_⟩
    · unfold therm; rw [ite_eq_right (lt_irrefl r)]
    · unfold therm; rw [ite_eq_left h]

/-- **Two unary ranks are equal as the ranks are**, below `k`. -/
theorem therm_eq_iff {k r r' : ℕ} (hr : r < k) (hr' : r' < k) :
    (∀ j : Fin k, therm (T := T) k r j = therm (T := T) k r' j) ↔ r = r' := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h ⟨r, hr⟩
      unfold therm at this
      rw [ite_eq_right (lt_irrefl r), ite_eq_left hlt] at this
      exact sLo_ne_sHi this
    · have := h ⟨r', hr'⟩
      unfold therm at this
      rw [ite_eq_left hlt, ite_eq_right (lt_irrefl r')] at this
      exact sLo_ne_sHi this.symm
  · rintro rfl _; rfl

theorem wbFlag_def (l : WithBot T) : wbFlag l = 0 ∨ wbFlag l = ValueType.nonzero := by
  cases l <;> simp [wbFlag]

/-- **The order of two lower bounds, read off their columns.** -/
theorem withBot_lt_iff (l l' : WithBot T) :
    LT.lt l l' ↔ (wbFlag l = ValueType.nonzero ∧ wbFlag l' = 0)
      ∨ (wbFlag l = wbFlag l' ∧ LT.lt (lval C l) (lval C l')) := by
  cases l <;> cases l' <;> simp [wbFlag, lval, nonzero_ne_zero', nonzero_ne_zero'.symm,
    WithBot.bot_lt_coe]

/-- **The equality of two lower bounds, read off their columns.** -/
theorem withBot_eq_iff (l l' : WithBot T) :
    l = l' ↔ wbFlag l = wbFlag l' ∧ lval C l = lval C l' := by
  cases l <;> cases l' <;> simp [wbFlag, lval, nonzero_ne_zero', nonzero_ne_zero'.symm]

/-! ## The comparison of two cells is the comparison of their values -/

variable (C) in
/-- **The codes a cell may hold** where the symbolic evaluation is
faithful: the code of a fresh component, a value of the cut, or the
null. -/
def CodeOK (par : Fin k → T) (x : Code T) : Prop :=
  (∃ i, IsFresh C (par i) ∧ x = code C par i)
    ∨ ∃ a, (a ∈ C ∨ ValueType.isNull a = true) ∧ x = Code.conc a

@[simp] theorem Kleene.and_true_left (a : Kleene) : Kleene.true.and a = a := by cases a <;> rfl
@[simp] theorem Kleene.and_false_left (a : Kleene) : Kleene.false.and a = Kleene.false := by
  cases a <;> rfl
@[simp] theorem Kleene.or_false_right (a : Kleene) : a.or Kleene.false = a := by cases a <;> rfl
@[simp] theorem Kleene.or_false_left (a : Kleene) : Kleene.false.or a = a := by cases a <;> rfl

/-- The strict wrapper reads `Q` on a non-null value. -/
theorem eval3_wrap_nonNull (a : SA T c n) (Q : SP T c n) (u : Tuple T n) (γ : Fin c → T)
    (ha : ValueType.isNull (a.eval u γ) = false) :
    (wrap a Q).eval3 u γ = Q.eval3 u γ := by
  have he : (SP.atom .eq a a).eval3 u γ = Kleene.true := by
    show CompOp.eq.eval3 _ _ = _
    simp [CompOp.eval3, ha, CompOp.eval, Kleene.ofBool, CompOp.strict]
  show ((SP.atom .eq a a).eval3 u γ).and ((Q.eval3 u γ).or ((SP.atom .eq a a).eval3 u γ).not) = _
  rw [he]
  show Kleene.true.and ((Q.eval3 u γ).or Kleene.false) = _
  simp

/-- And it is unknown on the null. -/
theorem eval3_wrap_null (a : SA T c n) (Q : SP T c n) (u : Tuple T n) (γ : Fin c → T)
    (ha : ValueType.isNull (a.eval u γ) = true) :
    (wrap a Q).eval3 u γ = Kleene.unknown := by
  have he : (SP.atom .eq a a).eval3 u γ = Kleene.unknown := by
    show CompOp.eq.eval3 _ _ = _
    simp [CompOp.eval3, ha, CompOp.strict]
  show ((SP.atom .eq a a).eval3 u γ).and ((Q.eval3 u γ).or ((SP.atom .eq a a).eval3 u γ).not) = _
  rw [he]
  cases Q.eval3 u γ <;> rfl

@[simp] theorem Kleene.and_ofBool (p q : Bool) :
    (Kleene.ofBool p).and (Kleene.ofBool q) = Kleene.ofBool (p && q) := by
  cases p <;> cases q <;> rfl

@[simp] theorem Kleene.or_ofBool (p q : Bool) :
    (Kleene.ofBool p).or (Kleene.ofBool q) = Kleene.ofBool (p || q) := by
  cases p <;> cases q <;> rfl

theorem ofBool_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    Kleene.ofBool (decide P) = Kleene.ofBool (decide Q) := by
  rw [decide_eq_decide.mpr h]

theorem ofBool_and_congr {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    (h : P ∧ Q ↔ R) : Kleene.ofBool (decide P && decide Q) = Kleene.ofBool (decide R) := by
  rw [← Bool.decide_and]; exact ofBool_congr h

theorem ofBool_nand_congr {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    (h : ¬ (P ∧ Q) ↔ R) : Kleene.ofBool (!(decide P && decide Q)) = Kleene.ofBool (decide R) := by
  rw [← Bool.decide_and, ← decide_not]; exact ofBool_congr h

/-- A gap's lower bound is never null as a column. -/
theorem isNull_lval_lo (a : T) : ValueType.isNull (lval C (lo C a)) = false := by
  cases h : lo C a with
  | bot =>
    show ValueType.isNull (wtVal (upOf C ⊥)) = false
    cases hu : upOf C ⊥ with
    | top => exact ValueType.isNull_zero
    | coe m =>
      have := Finset.mem_of_min hu
      exact (Finset.mem_filter.mp this).2.1
  | coe b => exact (lo_eq_coe h).2.1

/-- **A value at most a lower bound**, read off its columns. -/
theorem coe_le_iff (a : T) (l : WithBot T) :
    LE.le (a : WithBot T) l ↔ (wbFlag l = 0 ∧ LE.le a (lval C l)) := by
  cases l <;> simp [wbFlag, lval, nonzero_ne_zero']

theorem fresh_ne {par : Fin k → T} {i : Fin k} {a : T} (hi : IsFresh C (par i))
    (ha : a ∈ C ∨ ValueType.isNull a = true) : a ≠ par i := by
  rintro rfl
  rcases ha with ha | ha
  · exact hi.1 ha
  · rw [hi.2] at ha; exact absurd ha (by decide)

theorem enc_code_fresh {par : Fin k → T} {i : Fin k} (hi : IsFresh C (par i)) :
    enc C k (code C par i) = enc C k (Code.fresh (lo C (par i)) (rank C par (par i))) := by
  rw [code_of_fresh hi]

/-- **A concrete value of the cut below a fresh cell.** -/
theorem eval3_ltCF {par : Fin k → T} {j : Fin k} (hj : IsFresh C (par j))
    (a : SA T c n) (y : Fin (7 + k) → SA T c n) (u : Tuple T n) (γ : Fin c → T)
    (haC : a.eval u γ ∈ C) (han : ValueType.isNull (a.eval u γ) = false)
    (hy : ∀ i, (y i).eval u γ = enc C k (code C par j) i) :
    (ltCF a y).eval3 u γ = Kleene.ofBool (decide (LT.lt (a.eval u γ) (par j))) := by
  have hy' : ∀ i, (y i).eval u γ = enc C k (Code.fresh (lo C (par j)) (rank C par (par j))) i :=
    fun i => (hy i).trans (by rw [enc_code_fresh hj])
  show ((isZ (y (iB k))).eval3 u γ).and ((SP.atom .le a (y (iV k))).eval3 u γ) = _
  rw [eval3_isZ, eval3_atom_of_nonNull _ _ _ _ _ han (by rw [hy']; exact isNull_lval_lo _),
    hy', hy', enc_fresh_B, enc_fresh_V, Kleene.and_ofBool]
  refine ofBool_and_congr ?_
  rw [lt_iff_le_lo haC han, coe_le_iff]
  rfl

/-- **A fresh cell below a concrete value of the cut.** -/
theorem eval3_ltFC {par : Fin k → T} {i : Fin k} (hi : IsFresh C (par i))
    (x : Fin (7 + k) → SA T c n) (b : SA T c n) (u : Tuple T n) (γ : Fin c → T)
    (hbC : b.eval u γ ∈ C) (hbn : ValueType.isNull (b.eval u γ) = false)
    (hx : ∀ i', (x i').eval u γ = enc C k (code C par i) i') :
    (ltFC x b).eval3 u γ = Kleene.ofBool (decide (LT.lt (par i) (b.eval u γ))) := by
  have hx' : ∀ i', (x i').eval u γ = enc C k (Code.fresh (lo C (par i)) (rank C par (par i))) i' :=
    fun i' => (hx i').trans (by rw [enc_code_fresh hi])
  show (((isZ (x (iB k))).eval3 u γ).and ((SP.atom .le b (x (iV k))).eval3 u γ)).not = _
  rw [eval3_isZ, eval3_atom_of_nonNull _ _ _ _ _ hbn (by rw [hx']; exact isNull_lval_lo _),
    hx', hx', enc_fresh_B, enc_fresh_V, Kleene.and_ofBool, Kleene.not_ofBool]
  refine ofBool_nand_congr ?_
  have hne := fresh_ne hi (Or.inl hbC)
  rw [show (wbFlag (lo C (par i)) = 0 ∧ CompOp.le.eval (b.eval u γ) (lval C (lo C (par i))))
      ↔ LT.lt (b.eval u γ) (par i) from by rw [lt_iff_le_lo hbC hbn, coe_le_iff]; rfl]
  constructor
  · intro h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
  · intro h h'; exact absurd (h.trans h') (lt_irrefl _)

theorem ofBool_definite (b : Bool) :
    Kleene.ofBool b = Kleene.true ∨ Kleene.ofBool b = Kleene.false := by
  cases b <;> simp [Kleene.ofBool]

/-- The unary rank of a fresh cell's code is below `k`. -/
theorem rank_code_lt {par : Fin k → T} (i : Fin k) : rank C par (par i) < k :=
  rank_lt (mem_image par i)

theorem eval3_thEq (x y : Fin (7 + k) → SA T c n) (u : Tuple T n) (γ : Fin c → T)
    {r r' : ℕ} (hx : ∀ j, (x (iR j)).eval u γ = therm k r j)
    (hy : ∀ j, (y (iR j)).eval u γ = therm k r' j) :
    (thEq x y).eval3 u γ = Kleene.ofBool (decide (∀ j, therm (T := T) k r j = therm k r' j)) := by
  unfold thEq
  rw [eval3_andAll _ _ _ (fun p hp => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    rw [eval3_atom_syneq]; exact ofBool_definite _)]
  refine ofBool_congr ?_
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, eval3_atom_syneq, hx, hy, Kleene.ofBool_eq_true_iff,
    decide_eq_true_eq]

theorem eval3_thLt (x y : Fin (7 + k) → SA T c n) (u : Tuple T n) (γ : Fin c → T)
    {r r' : ℕ} (hx : ∀ j, (x (iR j)).eval u γ = therm k r j)
    (hy : ∀ j, (y (iR j)).eval u γ = therm k r' j) :
    (thLt x y).eval3 u γ
      = Kleene.ofBool (decide (∃ j, therm (T := T) k r j = sLo ∧ therm (T := T) k r' j
          = sHi)) := by
  unfold thLt
  rw [eval3_orAll _ _ _ (fun p hp => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    show ((isLo _).eval3 u γ).and ((isHi _).eval3 u γ) = _ ∨ ((isLo _).eval3 u γ).and _ = _
    rw [isLo, isHi, eval3_atom_syneq, eval3_atom_syneq, Kleene.and_ofBool]
    exact ofBool_definite _)]
  refine ofBool_congr ?_
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and]
  refine exists_congr fun j => ?_
  show ((isLo _).eval3 u γ).and ((isHi _).eval3 u γ) = Kleene.true ↔ _
  rw [isLo, isHi, eval3_atom_syneq, eval3_atom_syneq, hx, hy, Kleene.and_eq_true_iff,
    Kleene.ofBool_eq_true_iff, Kleene.ofBool_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq]
  rfl

/-- **Two fresh cells are equal as their values are.** -/
theorem eval3_eqFF {par : Fin k → T} {i j : Fin k} (hi : IsFresh C (par i))
    (hj : IsFresh C (par j)) (x y : Fin (7 + k) → SA T c n) (u : Tuple T n) (γ : Fin c → T)
    (hx : ∀ i', (x i').eval u γ = enc C k (code C par i) i')
    (hy : ∀ i', (y i').eval u γ = enc C k (code C par j) i') :
    (eqFF x y).eval3 u γ = Kleene.ofBool (decide (par i = par j)) := by
  have hx' := fun i' => (hx i').trans (congrFun (enc_code_fresh hi) i')
  have hy' := fun i' => (hy i').trans (congrFun (enc_code_fresh hj) i')
  show ((SP.atom .syneq (x (iB k)) (y (iB k))).eval3 u γ).and
    (((SP.atom .syneq (x (iV k)) (y (iV k))).eval3 u γ).and ((thEq x y).eval3 u γ)) = _
  rw [eval3_atom_syneq, eval3_atom_syneq,
    eval3_thEq x y u γ (fun j' => (hx' (iR j')).trans (enc_fresh_R _ _ _ _))
      (fun j' => (hy' (iR j')).trans (enc_fresh_R _ _ _ _)),
    hx', hy', hx', hy', enc_fresh_B, enc_fresh_B, enc_fresh_V, enc_fresh_V,
    Kleene.and_ofBool, Kleene.and_ofBool, ← Bool.decide_and, ← Bool.decide_and]
  refine ofBool_congr ?_
  rw [therm_eq_iff (rank_code_lt i) (rank_code_lt j), ← and_assoc, ← withBot_eq_iff,
    ← code_eq_code_iff (C := C), code_of_fresh hi, code_of_fresh hj]
  exact ⟨fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl, fun h => by injection h with h₁ h₂; exact ⟨h₁, h₂⟩⟩

/-- **A fresh cell below another, as their values are.** -/
theorem eval3_ltFF {par : Fin k → T} {i j : Fin k} (hi : IsFresh C (par i))
    (hj : IsFresh C (par j)) (x y : Fin (7 + k) → SA T c n) (u : Tuple T n) (γ : Fin c → T)
    (hx : ∀ i', (x i').eval u γ = enc C k (code C par i) i')
    (hy : ∀ i', (y i').eval u γ = enc C k (code C par j) i') :
    (ltFF x y).eval3 u γ = Kleene.ofBool (decide (LT.lt (par i) (par j))) := by
  have hx' := fun i' => (hx i').trans (congrFun (enc_code_fresh hi) i')
  have hy' := fun i' => (hy i').trans (congrFun (enc_code_fresh hj) i')
  show (((isN (x (iB k))).eval3 u γ).and ((isZ (y (iB k))).eval3 u γ)).or
    (((SP.atom .syneq (x (iB k)) (y (iB k))).eval3 u γ).and
      (((SP.atom .lt (x (iV k)) (y (iV k))).eval3 u γ).or
        (((SP.atom .eq (x (iV k)) (y (iV k))).eval3 u γ).and ((thLt x y).eval3 u γ)))) = _
  rw [eval3_isN, eval3_isZ, eval3_atom_syneq,
    eval3_atom_of_nonNull _ _ _ _ _ (by rw [hx']; exact isNull_lval_lo _)
      (by rw [hy']; exact isNull_lval_lo _),
    eval3_atom_of_nonNull _ _ _ _ _ (by rw [hx']; exact isNull_lval_lo _)
      (by rw [hy']; exact isNull_lval_lo _),
    eval3_thLt x y u γ (fun j' => (hx' (iR j')).trans (enc_fresh_R _ _ _ _))
      (fun j' => (hy' (iR j')).trans (enc_fresh_R _ _ _ _)),
    hx', hy', hx', hy', enc_fresh_B, enc_fresh_B, enc_fresh_V, enc_fresh_V]
  simp only [Kleene.and_ofBool, Kleene.or_ofBool, ← Bool.decide_and, ← Bool.decide_or]
  refine ofBool_congr ?_
  have hcl : LT.lt (par i) (par j) ↔ Code.lt (code C par i) (code C par j) := by
    rw [Code.lt_iff (Or.inl ⟨i, hi, rfl⟩) (Or.inl ⟨j, hj, rfl⟩), dec_code, dec_code]
  rw [therm_lt_iff (rank_code_lt i), hcl, code_of_fresh hi, code_of_fresh hj]
  show _ ↔ (LT.lt (lo C (par i)) (lo C (par j)) ∨ (lo C (par i) = lo C (par j) ∧ _))
  rw [withBot_lt_iff, withBot_eq_iff]
  show _ ↔ _ ∨ ((_ ∧ _) ∧ _)
  constructor
  · rintro (h | ⟨h₁, h₂ | ⟨h₃, h₄⟩⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨h₁, h₂⟩)
    · exact Or.inr ⟨⟨h₁, h₃⟩, h₄⟩
  · rintro ((h | ⟨h₁, h₂⟩) | ⟨⟨h₁, h₃⟩, h₄⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h₁, Or.inl h₂⟩
    · exact Or.inr ⟨h₁, Or.inr ⟨h₃, h₄⟩⟩

/-- **A concrete value compared with a fresh cell**, as with its value. -/
theorem eval3_branchCF {par : Fin k → T} {j : Fin k} (hj : IsFresh C (par j)) (op : CompOp)
    (a : SA T c n) (y : Fin (7 + k) → SA T c n) (u : Tuple T n) (γ : Fin c → T)
    (ha : a.eval u γ ∈ C ∨ ValueType.isNull (a.eval u γ) = true)
    (hy : ∀ i, (y i).eval u γ = enc C k (code C par j) i) :
    (branchCF op a y).eval3 u γ = op.eval3 (a.eval u γ) (par j) := by
  have hne : a.eval u γ ≠ par j := fresh_ne hj ha
  have hjn : ValueType.isNull (par j) = false := hj.2
  by_cases hn : ValueType.isNull (a.eval u γ) = true
  · cases op <;>
      first
      | (rw [CompOp.eval3_of_isNull_left rfl hn]; exact eval3_wrap_null _ _ _ _ hn)
      | (simp [branchCF, SP.eval3, CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool, hne])
  · have hnn : ValueType.isNull (a.eval u γ) = false := by simpa using hn
    have haC : a.eval u γ ∈ C := ha.resolve_right hn
    have hlt := eval3_ltCF hj a y u γ haC hnn hy
    have hev : ∀ op' : CompOp, op'.eval3 (a.eval u γ) (par j)
        = Kleene.ofBool (decide (op'.eval (a.eval u γ) (par j))) := fun op' => by
      simp [CompOp.eval3, hnn, hjn]
    cases op <;> rw [hev] <;> simp only [branchCF]
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      exact (ofBool_congr (P := a.eval u γ = par j) (Q := False) ⟨hne, False.elim⟩).symm
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      exact (ofBool_congr (P := a.eval u γ ≠ par j) (Q := True)
        ⟨fun _ => trivial, fun _ => hne⟩).symm
    · rw [eval3_wrap_nonNull _ _ _ _ hnn, hlt]; rfl
    · rw [eval3_wrap_nonNull _ _ _ _ hnn, hlt]
      exact ofBool_congr ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      show (SP.eval3 (ltCF a y) u γ).not = _
      rw [hlt, Kleene.not_ofBool, ← decide_not]
      exact ofBool_congr ⟨fun h => lt_of_le_of_ne (not_lt.mp h) hne.symm, fun h h' =>
        absurd (h.trans h') (lt_irrefl _)⟩
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      show (SP.eval3 (ltCF a y) u γ).not = _
      rw [hlt, Kleene.not_ofBool, ← decide_not]
      exact ofBool_congr ⟨fun h => (not_lt.mp h), fun h h' => absurd (h.trans_lt h') (lt_irrefl _)⟩
    · exact (ofBool_congr (P := a.eval u γ = par j) (Q := False) ⟨hne, False.elim⟩).symm
    · exact (ofBool_congr (P := a.eval u γ ≠ par j) (Q := True)
        ⟨fun _ => trivial, fun _ => hne⟩).symm

/-- **A fresh cell compared with a concrete value**, as its value. -/
theorem eval3_branchFC {par : Fin k → T} {i : Fin k} (hi : IsFresh C (par i)) (op : CompOp)
    (x : Fin (7 + k) → SA T c n) (b : SA T c n) (u : Tuple T n) (γ : Fin c → T)
    (hb : b.eval u γ ∈ C ∨ ValueType.isNull (b.eval u γ) = true)
    (hx : ∀ i', (x i').eval u γ = enc C k (code C par i) i') :
    (branchFC op x b).eval3 u γ = op.eval3 (par i) (b.eval u γ) := by
  have hne : par i ≠ b.eval u γ := (fresh_ne hi hb).symm
  have hin : ValueType.isNull (par i) = false := hi.2
  by_cases hn : ValueType.isNull (b.eval u γ) = true
  · cases op <;>
      first
      | (rw [CompOp.eval3_of_isNull_right rfl _ hn]; exact eval3_wrap_null _ _ _ _ hn)
      | (simp [branchFC, SP.eval3, CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool, hne])
  · have hnn : ValueType.isNull (b.eval u γ) = false := by simpa using hn
    have hbC : b.eval u γ ∈ C := hb.resolve_right hn
    have hlt := eval3_ltFC hi x b u γ hbC hnn hx
    have hev : ∀ op' : CompOp, op'.eval3 (par i) (b.eval u γ)
        = Kleene.ofBool (decide (op'.eval (par i) (b.eval u γ))) := fun op' => by
      simp [CompOp.eval3, hnn, hin]
    cases op <;> rw [hev] <;> simp only [branchFC]
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      exact (ofBool_congr (P := par i = b.eval u γ) (Q := False) ⟨hne, False.elim⟩).symm
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      exact (ofBool_congr (P := par i ≠ b.eval u γ) (Q := True)
        ⟨fun _ => trivial, fun _ => hne⟩).symm
    · rw [eval3_wrap_nonNull _ _ _ _ hnn, hlt]; rfl
    · rw [eval3_wrap_nonNull _ _ _ _ hnn, hlt]
      exact ofBool_congr ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      show (SP.eval3 (ltFC x b) u γ).not = _
      rw [hlt, Kleene.not_ofBool, ← decide_not]
      exact ofBool_congr ⟨fun h => lt_of_le_of_ne (not_lt.mp h) hne.symm, fun h h' =>
        absurd (h.trans h') (lt_irrefl _)⟩
    · rw [eval3_wrap_nonNull _ _ _ _ hnn]
      show (SP.eval3 (ltFC x b) u γ).not = _
      rw [hlt, Kleene.not_ofBool, ← decide_not]
      exact ofBool_congr ⟨fun h => (not_lt.mp h), fun h h' => absurd (h.trans_lt h') (lt_irrefl _)⟩
    · exact (ofBool_congr (P := par i = b.eval u γ) (Q := False) ⟨hne, False.elim⟩).symm
    · exact (ofBool_congr (P := par i ≠ b.eval u γ) (Q := True)
        ⟨fun _ => trivial, fun _ => hne⟩).symm

/-- **Two fresh cells compared**, as their values. -/
theorem eval3_branchFF {par : Fin k → T} {i j : Fin k} (hi : IsFresh C (par i))
    (hj : IsFresh C (par j)) (op : CompOp) (x y : Fin (7 + k) → SA T c n) (u : Tuple T n)
    (γ : Fin c → T) (hx : ∀ i', (x i').eval u γ = enc C k (code C par i) i')
    (hy : ∀ i', (y i').eval u γ = enc C k (code C par j) i') :
    (branchFF op x y).eval3 u γ = op.eval3 (par i) (par j) := by
  have hev : ∀ op' : CompOp, op'.eval3 (par i) (par j)
      = Kleene.ofBool (decide (op'.eval (par i) (par j))) := fun op' => by
    simp [CompOp.eval3, hi.2, hj.2]
  have heq := eval3_eqFF hi hj x y u γ hx hy
  have hlt := eval3_ltFF hi hj x y u γ hx hy
  have hgt := eval3_ltFF hj hi y x u γ hy hx
  cases op <;> rw [hev] <;> simp only [branchFF]
  · exact heq
  · show (SP.eval3 (eqFF x y) u γ).not = _
    rw [heq, Kleene.not_ofBool, ← decide_not]; rfl
  · exact hlt
  · show (SP.eval3 (ltFF x y) u γ).or (SP.eval3 (eqFF x y) u γ) = _
    rw [hlt, heq, Kleene.or_ofBool, ← Bool.decide_or]
    exact ofBool_congr le_iff_lt_or_eq.symm
  · exact hgt
  · show (SP.eval3 (ltFF y x) u γ).or (SP.eval3 (eqFF x y) u γ) = _
    rw [hgt, heq, Kleene.or_ofBool, ← Bool.decide_or]
    exact ofBool_congr ⟨fun h => h.elim le_of_lt (fun h' => h'.symm ▸ le_refl _),
      fun h => (lt_or_eq_of_le h).imp id Eq.symm⟩
  · exact heq
  · show (SP.eval3 (eqFF x y) u γ).not = _
    rw [heq, Kleene.not_ofBool, ← decide_not]; rfl

/-- **The comparison of two cells is the comparison of the values they
stand for**, in all three truth values. -/
theorem eval3_cellCmp {par : Fin k → T} (op : CompOp) (x y : Fin (7 + k) → SA T c n)
    (u : Tuple T n) (γ : Fin c → T) {cx cy : Code T} (hcx : CodeOK C par cx)
    (hcy : CodeOK C par cy) (hx : ∀ i, (x i).eval u γ = enc C k cx i)
    (hy : ∀ i, (y i).eval u γ = enc C k cy i) :
    (cellCmp op x y).eval3 u γ = op.eval3 (dec C par cx) (dec C par cy) := by
  have hF : ∀ (z : Fin (7 + k) → SA T c n) (cz : Code T), CodeOK C par cz →
      (∀ i, (z i).eval u γ = enc C k cz i) →
      ((isZ (z (iF k))).eval3 u γ = Kleene.true ∧ (isN (z (iF k))).eval3 u γ = Kleene.false
          ∧ ∃ a, (a ∈ C ∨ ValueType.isNull a = true) ∧ cz = Code.conc a)
        ∨ ((isZ (z (iF k))).eval3 u γ = Kleene.false ∧ (isN (z (iF k))).eval3 u γ = Kleene.true
          ∧ ∃ i, IsFresh C (par i) ∧ cz = code C par i) := by
    intro z cz hcz hz
    rcases hcz with ⟨i, hi, rfl⟩ | ⟨a, ha, rfl⟩
    · refine Or.inr ⟨?_, ?_, i, hi, rfl⟩
      · rw [eval3_isZ, hz, code_of_fresh hi, enc_fresh_F]
        simp [Kleene.ofBool, nonzero_ne_zero']
      · rw [eval3_isN, hz, code_of_fresh hi, enc_fresh_F]
        simp [Kleene.ofBool]
    · refine Or.inl ⟨?_, ?_, a, ha, rfl⟩
      · rw [eval3_isZ, hz, enc_conc_F]; simp [Kleene.ofBool]
      · rw [eval3_isN, hz, enc_conc_F]; simp [Kleene.ofBool, nonzero_ne_zero'.symm]
  show (((isZ (x (iF k))).eval3 u γ).and ((isZ (y (iF k))).eval3 u γ) |>.and _).or
    ((((isZ (x (iF k))).eval3 u γ).and ((isN (y (iF k))).eval3 u γ) |>.and _).or
      ((((isN (x (iF k))).eval3 u γ).and ((isZ (y (iF k))).eval3 u γ) |>.and _).or
        (((isN (x (iF k))).eval3 u γ).and ((isN (y (iF k))).eval3 u γ) |>.and _))) = _
  rcases hF x cx hcx hx with ⟨hz₁, hn₁, a, ha, rfl⟩ | ⟨hz₁, hn₁, i, hi, rfl⟩ <;>
    rcases hF y cy hcy hy with ⟨hz₂, hn₂, b, hb, rfl⟩ | ⟨hz₂, hn₂, j, hj, rfl⟩ <;>
    rw [hz₁, hn₁, hz₂, hn₂] <;> simp only [Kleene.and_true_left, Kleene.and_false_left,
      Kleene.or_false_left, Kleene.or_false_right]
  · show op.eval3 ((x (iV k)).eval u γ) ((y (iV k)).eval u γ) = _
    rw [hx, hy, enc_conc_V, enc_conc_V]; rfl
  · rw [dec_code, eval3_branchCF hj op _ y u γ (by rw [hx, enc_conc_V]; exact ha) hy, hx,
      enc_conc_V]; rfl
  · rw [dec_code, eval3_branchFC hi op x _ u γ (by rw [hy, enc_conc_V]; exact hb) hx, hy,
      enc_conc_V]; rfl
  · rw [dec_code, dec_code, eval3_branchFF hi hj op x y u γ hx hy]

end Sym
