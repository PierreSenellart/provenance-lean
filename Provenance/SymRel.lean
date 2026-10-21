module

public import Provenance.SymCells
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import all Provenance.SymCells
import all Provenance.SymCode

/-!
# Symbolic rows

A **symbolic relation** for a query whose context starts with `k`
parameter components holds rows of `k + n` cells, each cell `7 + k`
columns (`Provenance.SymCells`): the first `k` cells are the codes of the
parameter row – its **descriptor** – and the other `n` the codes of an
output row. A value of an output row is coded canonically
(`Sym.vcode`): the code of the parameter component it equals where that
component is fresh, itself elsewhere. `Sym.rowEnc` is the symbolic row of
a parameter row and an output row, and what a symbolic evaluation is
asked is that the rows it holds under the descriptor of a parameter row
be the encodings of the output rows at that parameter row.
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

/-! ## Cells of a row -/

/-- The column `j` of cell `i`. -/
def ci {k N : ℕ} (i : Fin N) (j : Fin (7 + k)) : Fin (N * (7 + k)) := finProdFinEquiv (i, j)

/-- **The cell `i` of a row.** -/
def cellOf {k N : ℕ} (r : Tuple T (N * (7 + k))) (i : Fin N) : Tuple T (7 + k) :=
  fun j => r (ci i j)

/-- **A row from its cells.** -/
def ofCells {k N : ℕ} (cs : Fin N → Tuple T (7 + k)) : Tuple T (N * (7 + k)) :=
  fun x => cs (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2

omit [ValueType T] in
@[simp] private theorem cellOf_ofCells {k N : ℕ} (cs : Fin N → Tuple T (7 + k)) (i : Fin N) :
    cellOf (ofCells cs) i = cs i := by
  funext j
  simp [cellOf, ofCells, ci]

omit [ValueType T] in
@[simp] private theorem ofCells_cellOf {k N : ℕ} (r : Tuple T (N * (7 + k))) :
    ofCells (cellOf r) = r := by
  funext x
  simp only [ofCells, cellOf, ci]
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

omit [ValueType T] in
private theorem ofCells_injective {k N : ℕ} : Function.Injective (ofCells (T := T) (k := k) (N := N)) :=
  fun cs cs' h => by
    funext i
    have := congrArg (fun r => cellOf r i) h
    simpa using this

omit [ValueType T] in
private theorem ofCells_eq_iff {k N : ℕ} (cs cs' : Fin N → Tuple T (7 + k)) :
    ofCells cs = ofCells cs' ↔ ∀ i, cs i = cs' i :=
  ⟨fun h i => congrFun (ofCells_injective h) i, fun h => congrArg ofCells (funext h)⟩

/-! ## The canonical code of a value -/

variable (C : Finset T) {k : ℕ}

open Classical in
/-- **The code of a value of an output row**: the code of the parameter
component it is, where that component is fresh; the value itself
elsewhere. -/
noncomputable def vcode (par : Fin k → T) (b : T) : Code T :=
  if h : ∃ i, IsFresh C (par i) ∧ par i = b then code C par h.choose else .conc b

variable {C}

/-- A component's value is coded as the component. -/
private theorem vcode_par (par : Fin k → T) (i : Fin k) : vcode C par (par i) = code C par i := by
  unfold vcode
  by_cases h : ∃ i', IsFresh C (par i') ∧ par i' = par i
  · rw [dite_eq_left h]
    exact code_eq_code_iff.mpr h.choose_spec.2
  · rw [dite_eq_right h, code_of_not_fresh (fun hi => h ⟨i, hi, rfl⟩)]

/-- A value that is no fresh component stands for itself. -/
private theorem vcode_of_not (par : Fin k → T) {b : T} (hb : ∀ i, IsFresh C (par i) → par i ≠ b) :
    vcode C par b = .conc b := by
  unfold vcode
  rw [dite_eq_right (fun ⟨i, hi, he⟩ => hb i hi he)]

/-- A value of the cut, or the null, stands for itself. -/
private theorem vcode_of_mem (par : Fin k → T) {b : T} (hb : b ∈ C ∨ ValueType.isNull b = true) :
    vcode C par b = .conc b :=
  vcode_of_not par (fun _ hi he => fresh_ne hi hb he.symm)

/-- **A value the symbolic evaluation can code**: a component of the
parameter row, a value of the cut, or the null. -/
def GoodVal (par : Fin k → T) (b : T) : Prop :=
  (∃ i, par i = b) ∨ b ∈ C ∨ ValueType.isNull b = true

/-- A good value's code is one a comparison reads faithfully. -/
private theorem codeOK_vcode {par : Fin k → T} {b : T} (hb : GoodVal (C := C) par b) :
    CodeOK C par (vcode C par b) := by
  by_cases h : ∃ i, IsFresh C (par i) ∧ par i = b
  · obtain ⟨i, hi, rfl⟩ := h
    rw [vcode_par]
    exact Or.inl ⟨i, hi, rfl⟩
  · rw [vcode_of_not par (fun i hi he => h ⟨i, hi, he⟩)]
    refine Or.inr ⟨b, ?_, rfl⟩
    rcases hb with ⟨i, rfl⟩ | hb
    · by_cases hn : ValueType.isNull (par i) = true
      · exact Or.inr hn
      · by_contra hc
        exact h ⟨i, ⟨fun hm => hc (Or.inl hm), by simpa using hn⟩, rfl⟩
    · exact hb

/-- **A value's code stands for the value.** -/
private theorem dec_vcode (par : Fin k → T) (b : T) : dec C par (vcode C par b) = b := by
  by_cases h : ∃ i, IsFresh C (par i) ∧ par i = b
  · obtain ⟨i, -, rfl⟩ := h
    rw [vcode_par, dec_code]
  · rw [vcode_of_not par (fun i hi he => h ⟨i, hi, he⟩)]; rfl

private theorem vcode_injective (par : Fin k → T) : Function.Injective (vcode C par) :=
  fun b b' h => by rw [← dec_vcode (C := C) par b, h, dec_vcode]

/-! ## Encodings are injective -/

/-- The fresh codes a row holds have their ranks below `k`. -/
def RankOK (k : ℕ) : Code T → Prop
  | .conc _ => True
  | .fresh _ r => r < k

private theorem rankOK_code (par : Fin k → T) (i : Fin k) : RankOK k (code C par i) := by
  unfold code
  split
  · exact rank_code_lt i
  · trivial

private theorem rankOK_vcode (par : Fin k → T) (b : T) : RankOK k (vcode C par b) := by
  unfold vcode
  split
  · exact rankOK_code par _
  · trivial

/-- **Two codes with ranks below `k` have the same columns only if they
are equal.** -/
private theorem enc_inj {x y : Code T} (hx : RankOK k x) (hy : RankOK k y)
    (h : enc C k x = enc C k y) : x = y := by
  have hF := congrFun h (iF k)
  have hV := congrFun h (iV k)
  cases x with
  | conc a =>
    cases y with
    | conc b => rw [enc_conc_V, enc_conc_V] at hV; rw [hV]
    | fresh l r => rw [enc_conc_F, enc_fresh_F] at hF; exact absurd hF.symm nonzero_ne_zero'
  | fresh l r =>
    cases y with
    | conc b => rw [enc_conc_F, enc_fresh_F] at hF; exact absurd hF nonzero_ne_zero'
    | fresh l' r' =>
      have hB := congrFun h (iB k)
      rw [enc_fresh_V, enc_fresh_V] at hV
      rw [enc_fresh_B, enc_fresh_B] at hB
      have hl : l = l' := (withBot_eq_iff l l').mpr ⟨hB, hV⟩
      have hr : r = r' := (therm_eq_iff (T := T) hx hy).mp (fun j => by
        have := congrFun h (iR j)
        rwa [enc_fresh_R, enc_fresh_R] at this)
      rw [hl, hr]

/-! ## The symbolic row of a parameter row and an output row -/

variable (C) in
/-- **The descriptor of a parameter row**: the codes of its components. -/
def descEnc (par : Fin k → T) : Tuple T (k * (7 + k)) :=
  ofCells (fun i => enc C k (code C par i))

variable (C) in
/-- **The symbolic row** of a parameter row and an output row. -/
noncomputable def rowEnc {n : ℕ} (par : Fin k → T) (v : Tuple T n) : Tuple T ((k + n) * (7 + k)) :=
  ofCells (Fin.append (fun i => enc C k (code C par i)) (fun j => enc C k (vcode C par (v j))))

/-- **The descriptor part of a symbolic row.** -/
def descPart {n : ℕ} (r : Tuple T ((k + n) * (7 + k))) : Tuple T (k * (7 + k)) :=
  ofCells (fun i => cellOf r (Fin.castAdd n i))

/-- **The output part of a symbolic row.** -/
def outPart {n : ℕ} (r : Tuple T ((k + n) * (7 + k))) : Tuple T (n * (7 + k)) :=
  ofCells (fun j => cellOf r (Fin.natAdd k j))

@[simp] private theorem descPart_rowEnc {n : ℕ} (par : Fin k → T) (v : Tuple T n) :
    descPart (rowEnc C par v) = descEnc C par := by
  simp [descPart, rowEnc, descEnc, Fin.append_left]

/-- **The symbolic row determines the output row**, its values being
coded canonically. -/
private theorem rowEnc_injective {n : ℕ} (par : Fin k → T) :
    Function.Injective (rowEnc (n := n) C par) := fun v v' h => by
  funext j
  have h' := (ofCells_eq_iff _ _).mp h (Fin.natAdd k j)
  rw [Fin.append_right, Fin.append_right] at h'
  exact vcode_injective par (enc_inj (rankOK_vcode par _) (rankOK_vcode par _) h')

end Sym
