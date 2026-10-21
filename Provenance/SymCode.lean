module

public import Provenance.SumByProd

/-!
# Codes of parameter values relative to a cut

The right side of an apply inside a recursive term cannot be decorrelated:
the decorrelation would read the recursive relation twice. What replaces
it is a **table** of the right side at every *type* of the parameter row,
computed outside the recursion and joined to the recursive relation. The
type of a parameter `u` is read relative to a finite set `C` of values,
the **cut**: each component either is a value of `C` (or the null), or
lies strictly between two consecutive non-null values of `C` – or below
the least – and then only its **rank** among the components of `u` in the
same gap is recorded. That is the component's **code**.

This file is the value-level part: the codes (`Sym.Code`), the code of a
component (`Sym.code`), and the facts the symbolic evaluation rests on –
two components have the same code exactly when they are equal
(`Sym.code_eq_code_iff`), and the order of the codes, which reads the
bound and the rank and never the value, is the order of the values
wherever the concrete side is in the cut (`Sym.Code.lt_iff`).
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

variable (C : Finset T)

/-- **A fresh value**: non-null and outside the cut. -/
def IsFresh (a : T) : Prop := a ∉ C ∧ ValueType.isNull a = false

instance (a : T) : Decidable (IsFresh C a) := by unfold IsFresh; infer_instance

/-- The non-null values of the cut strictly below `a`. -/
def below (a : T) : Finset T := C.filter (fun t => ValueType.isNull t = false ∧ t < a)

/-- **The gap's lower bound**: the greatest non-null value of the cut below
`a`, `⊥` if there is none. -/
def lo (a : T) : WithBot T := (below C a).max

variable {C}

theorem mem_below {a t : T} : t ∈ below C a ↔ t ∈ C ∧ ValueType.isNull t = false ∧ t < a := by
  unfold below; rw [Finset.mem_filter]

/-- A non-null value of the cut below a value is at most its bound. -/
theorem le_lo {a t : T} (ht : t ∈ C) (hn : ValueType.isNull t = false) (hlt : t < a) :
    (t : WithBot T) ≤ lo C a :=
  Finset.le_max (mem_below.mpr ⟨ht, hn, hlt⟩)

/-- The bound is a non-null value of the cut below the value, if any. -/
theorem lo_eq_coe {a b : T} (h : lo C a = (b : WithBot T)) :
    b ∈ C ∧ ValueType.isNull b = false ∧ b < a :=
  mem_below.mp (Finset.mem_of_max h)

/-- **A value's position against a non-null value of the cut** is
read off its bound: the value of the cut is below exactly when it is at
most the bound. -/
theorem lt_iff_le_lo {a t : T} (ht : t ∈ C) (hn : ValueType.isNull t = false) :
    LT.lt t a ↔ LE.le (t : WithBot T) (lo C a) := by
  constructor
  · exact le_lo ht hn
  · intro h
    cases hlo : lo C a with
    | bot => rw [hlo] at h; exact absurd h (by simp)
    | coe b =>
      rw [hlo] at h
      obtain ⟨-, -, hb⟩ := lo_eq_coe hlo
      exact lt_of_le_of_lt (WithBot.coe_le_coe.mp h) hb

theorem ne_of_fresh {a t : T} (ha : IsFresh C a) (ht : t ∈ C) : t ≠ a :=
  fun h => ha.1 (h ▸ ht)

/-- Two fresh values in increasing order have increasing bounds. -/
theorem lo_mono {a b : T} (hab : a ≤ b) : lo C a ≤ lo C b := by
  unfold lo
  exact Finset.max_mono (fun t ht => by
    obtain ⟨h₁, h₂, h₃⟩ := mem_below.mp ht
    exact mem_below.mpr ⟨h₁, h₂, lt_of_lt_of_le h₃ hab⟩)

/-- **Two fresh values with different bounds** are ordered as their bounds. -/
theorem lt_of_lo_lt {a b : T} (h : lo C a < lo C b) : a < b := by
  by_contra hc
  exact absurd (lo_mono (not_lt.mp hc)) (not_le.mpr h)

variable (C)

/-- **The rank of `a` among the components of `u`**: how many distinct
fresh components share its gap and are below it. -/
def rank {k : ℕ} (u : Fin k → T) (a : T) : ℕ :=
  ((Finset.univ.image u).filter (fun b => IsFresh C b ∧ lo C b = lo C a ∧ b < a)).card

variable {C}

/-- In one gap, the rank orders the components as their values. -/
theorem rank_lt_rank {k : ℕ} {u : Fin k → T} {a b : T} (ha : a ∈ Finset.univ.image u)
    (haf : IsFresh C a) (hab : a < b) (hlo : lo C a = lo C b) :
    rank C u a < rank C u b := by
  unfold rank
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · obtain ⟨hxu, hxf, hxlo, hxa⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxu, hxf, hxlo.trans hlo, hxa.trans hab⟩
  · have := hsub (Finset.mem_filter.mpr ⟨ha, haf, hlo, hab⟩)
    exact lt_irrefl a (Finset.mem_filter.mp this).2.2.2

/-- **In one gap, the rank decides the order.** -/
theorem lt_iff_rank_lt {k : ℕ} {u : Fin k → T} {a b : T} (ha : a ∈ Finset.univ.image u)
    (hb : b ∈ Finset.univ.image u) (haf : IsFresh C a) (hbf : IsFresh C b)
    (hlo : lo C a = lo C b) : LT.lt a b ↔ LT.lt (rank C u a) (rank C u b) := by
  refine ⟨fun h => rank_lt_rank ha haf h hlo, fun h => ?_⟩
  rcases lt_trichotomy a b with h' | h' | h'
  · exact h'
  · subst h'; exact absurd h (lt_irrefl _)
  · exact absurd (rank_lt_rank hb hbf h' hlo.symm) (not_lt.mpr h.le)

/-- **In one gap, the rank decides equality.** -/
theorem eq_iff_rank_eq {k : ℕ} {u : Fin k → T} {a b : T} (ha : a ∈ Finset.univ.image u)
    (hb : b ∈ Finset.univ.image u) (haf : IsFresh C a) (hbf : IsFresh C b)
    (hlo : lo C a = lo C b) : a = b ↔ rank C u a = rank C u b := by
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (ne_of_lt (rank_lt_rank ha haf h' hlo))
  · exact h'
  · exact absurd h (ne_of_gt (rank_lt_rank hb hbf h' hlo.symm))

/-- A rank is less than the number of components. -/
theorem rank_lt {k : ℕ} {u : Fin k → T} {a : T} (ha : a ∈ Finset.univ.image u) :
    rank C u a < k := by
  unfold rank
  have hsub : (Finset.univ.image u).filter (fun b => IsFresh C b ∧ lo C b = lo C a ∧ b < a)
      ⊆ (Finset.univ.image u).erase a := fun x hx => by
    obtain ⟨hxu, -, -, hxa⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨ne_of_lt hxa, hxu⟩
  calc _ ≤ ((Finset.univ.image u).erase a).card := Finset.card_le_card hsub
    _ < (Finset.univ.image u).card := Finset.card_erase_lt_of_mem ha
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

/-! ## Codes -/

/-- **A code**: a value standing for itself, or a gap of the cut (its
lower bound, `⊥` below the least non-null value) with a rank in it. -/
inductive Code (T : Type) where
  | conc (a : T) : Code T
  | fresh (l : WithBot T) (r : ℕ) : Code T
  deriving DecidableEq

variable (C) in
/-- **The code of a component** of the parameter row. -/
def code {k : ℕ} (u : Fin k → T) (i : Fin k) : Code T :=
  if IsFresh C (u i) then Code.fresh (lo C (u i)) (rank C u (u i)) else Code.conc (u i)

theorem code_of_fresh {k : ℕ} {u : Fin k → T} {i : Fin k} (h : IsFresh C (u i)) :
    code C u i = Code.fresh (lo C (u i)) (rank C u (u i)) := by
  unfold code; rw [ite_eq_left h]

theorem code_of_not_fresh {k : ℕ} {u : Fin k → T} {i : Fin k} (h : ¬ IsFresh C (u i)) :
    code C u i = Code.conc (u i) := by
  unfold code; rw [ite_eq_right h]

theorem mem_image {k : ℕ} (u : Fin k → T) (i : Fin k) : u i ∈ Finset.univ.image u :=
  Finset.mem_image_of_mem u (Finset.mem_univ i)

/-- **Two components have the same code exactly when they are equal.** -/
theorem code_eq_code_iff {k : ℕ} {u : Fin k → T} {i j : Fin k} :
    code C u i = code C u j ↔ u i = u j := by
  by_cases hi : IsFresh C (u i) <;> by_cases hj : IsFresh C (u j)
  · rw [code_of_fresh hi, code_of_fresh hj]
    constructor
    · intro h
      injection h with hlo hr
      exact (eq_iff_rank_eq (mem_image u i) (mem_image u j) hi hj hlo).mpr hr
    · intro h; rw [h]
  · rw [code_of_fresh hi, code_of_not_fresh hj]
    refine ⟨fun h => (by cases h), fun h => absurd (h ▸ hi) hj⟩
  · rw [code_of_not_fresh hi, code_of_fresh hj]
    exact ⟨fun h => (by cases h), fun h => absurd (h ▸ hj) hi⟩
  · rw [code_of_not_fresh hi, code_of_not_fresh hj]
    exact ⟨fun h => by injection h, fun h => h ▸ rfl⟩

/-! ## The order of codes -/

/-- **The order of codes**: concrete values by their order; a concrete
value below a gap when it is at most its bound; a gap below a concrete
value when its bound is; two gaps by their bounds, then their ranks. -/
def Code.lt : Code T → Code T → Prop
  | .conc a, .conc b => LT.lt a b
  | .conc a, .fresh l _ => LE.le (a : WithBot T) l
  | .fresh l _, .conc b => LT.lt l (b : WithBot T)
  | .fresh l r, .fresh l' r' => LT.lt l l' ∨ (l = l' ∧ LT.lt r r')

variable (C) in
/-- **A code standing for a value of `u`, or for a value of the cut**:
what a cell holds wherever the symbolic evaluation is faithful. The
null is set aside – a comparison with it is unknown, whatever the code. -/
def Valid {k : ℕ} (u : Fin k → T) (x : Code T) : Prop :=
  (∃ i, IsFresh C (u i) ∧ x = code C u i)
    ∨ ∃ a, a ∈ C ∧ ValueType.isNull a = false ∧ x = Code.conc a

variable (C) in
open Classical in
/-- **The value a code stands for** under the parameter row `u`: a fresh
code reads the component it is the code of. -/
noncomputable def dec {k : ℕ} (u : Fin k → T) : Code T → T
  | .conc a => a
  | .fresh l r =>
    if h : ∃ i, IsFresh C (u i) ∧ lo C (u i) = l ∧ rank C u (u i) = r then u h.choose else 0

/-- **A code decodes to the component it is the code of.** -/
theorem dec_code {k : ℕ} (u : Fin k → T) (i : Fin k) : dec C u (code C u i) = u i := by
  by_cases hi : IsFresh C (u i)
  · rw [code_of_fresh hi]
    have hex : ∃ j, IsFresh C (u j) ∧ lo C (u j) = lo C (u i) ∧ rank C u (u j) = rank C u (u i) :=
      ⟨i, hi, rfl, rfl⟩
    simp only [dec]
    rw [dite_eq_left hex]
    obtain ⟨hf, hl, hr⟩ := hex.choose_spec
    exact (eq_iff_rank_eq (mem_image u _) (mem_image u i) hf hi hl).mpr hr
  · rw [code_of_not_fresh hi]; rfl

/-- **The order of valid codes is the order of the values they stand for.** -/
theorem Code.lt_iff {k : ℕ} {u : Fin k → T} {x y : Code T} (hx : Valid C u x) (hy : Valid C u y) :
    Code.lt x y ↔ LT.lt (dec C u x) (dec C u y) := by
  rcases hx with ⟨i, hi, rfl⟩ | ⟨a, ha, han, rfl⟩ <;>
    rcases hy with ⟨j, hj, rfl⟩ | ⟨b, hb, hbn, rfl⟩
  · rw [dec_code, dec_code, code_of_fresh hi, code_of_fresh hj]
    show (LT.lt (lo C (u i)) (lo C (u j)) ∨ (lo C (u i) = lo C (u j) ∧ _)) ↔ _
    constructor
    · rintro (h | ⟨h, hr⟩)
      · exact lt_of_lo_lt h
      · exact (lt_iff_rank_lt (mem_image u i) (mem_image u j) hi hj h).mpr hr
    · intro h
      rcases (lo_mono h.le).lt_or_eq with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', (lt_iff_rank_lt (mem_image u i) (mem_image u j) hi hj h').mp h⟩
  · rw [dec_code, code_of_fresh hi]
    show LT.lt (lo C (u i)) (b : WithBot T) ↔ LT.lt (u i) b
    constructor
    · intro h
      rcases lt_or_gt_of_ne (ne_of_fresh hi hb).symm with h' | h'
      · exact h'
      · exact absurd ((lt_iff_le_lo hb hbn).mp h') (not_le.mpr h)
    · intro h
      exact not_le.mp (fun h' => absurd h (not_lt.mpr ((lt_iff_le_lo hb hbn).mpr h').le))
  · rw [dec_code, code_of_fresh hj]
    show LE.le (a : WithBot T) (lo C (u j)) ↔ LT.lt a (u j)
    exact (lt_iff_le_lo ha han).symm
  · exact Iff.rfl

/-- **Valid codes are equal exactly when the values they stand for are.** -/
theorem Code.eq_iff {k : ℕ} {u : Fin k → T} {x y : Code T} (hx : Valid C u x) (hy : Valid C u y) :
    x = y ↔ dec C u x = dec C u y := by
  rcases hx with ⟨i, hi, rfl⟩ | ⟨a, ha, han, rfl⟩ <;>
    rcases hy with ⟨j, hj, rfl⟩ | ⟨b, hb, hbn, rfl⟩
  · rw [dec_code, dec_code]; exact code_eq_code_iff
  · rw [dec_code, code_of_fresh hi]
    exact ⟨fun h => (by cases h), fun h => absurd (h ▸ hb) hi.1⟩
  · rw [dec_code, code_of_fresh hj]
    exact ⟨fun h => (by cases h), fun h => absurd (h ▸ ha) hj.1⟩
  · exact ⟨fun h => by injection h, fun h => congrArg Code.conc h⟩

/-- A valid code stands for a non-null value. -/
theorem isNull_dec {k : ℕ} {u : Fin k → T} {x : Code T} (hx : Valid C u x) :
    ValueType.isNull (dec C u x) = false := by
  rcases hx with ⟨i, hi, rfl⟩ | ⟨a, -, han, rfl⟩
  · rw [dec_code]; exact hi.2
  · exact han

end Sym
