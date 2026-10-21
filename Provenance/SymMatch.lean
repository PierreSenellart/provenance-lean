module

public import Provenance.SymEnvBuild
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Recognizing a parameter row's descriptor

The table of an apply's right side holds its rows under every descriptor,
and the apply's left row has to pick out its own: the descriptor whose
cells are the codes of its components. That is a predicate over the row
and a descriptor's cells (`Sym.matchSP`): each cell is a value equal to the
component, or a gap whose bounds enclose it; and the ranks recorded in the
fresh cells of one gap are ordered as their components, without a hole
below any of them. Over cells the cut can produce, it holds exactly of
the row's own descriptor (`Sym.eval3_matchSP`).
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

variable {C : Finset T}

/-! ## Gaps and bounds -/

/-- **A value lies in the gap above `l`**: it is not null, above the
bound, and below the bound above it. -/
theorem fresh_lo_iff {l : WithBot T} (hl : GapOK C l) (a : T) :
    (ValueType.isNull a = false ∧ (∀ t : T, l = (t : WithBot T) → t < a)
      ∧ (∀ h : T, upOf C l = (h : WithTop T) → a < h)) ↔ (IsFresh C a ∧ lo C a = l) := by
  constructor
  · rintro ⟨han, hlo, hup⟩
    -- no non-null value of the cut lies strictly above the bound and at or below `a`
    have hbetween : ∀ c ∈ C, ValueType.isNull c = false → LT.lt l (c : WithBot T) → a < c := by
      intro c hc hcn hlc
      cases hu : upOf C l with
      | top => exact absurd hlc ((upOf_eq_top_iff C l).mp hu c hc hcn)
      | coe h =>
        obtain ⟨-, hmin⟩ := (upOf_eq_coe_iff C l h).mp hu
        exact lt_of_lt_of_le (hup h hu) (hmin c hc hcn hlc)
    have hfresh : a ∉ C := by
      intro haC
      cases l with
      | bot => exact lt_irrefl a (hbetween a haC han (WithBot.bot_lt_coe a))
      | coe t => exact lt_irrefl a (hbetween a haC han (WithBot.coe_lt_coe.mpr (hlo t rfl)))
    refine ⟨⟨hfresh, han⟩, ?_⟩
    refine le_antisymm ?_ ?_
    · refine Finset.max_le fun c hc => ?_
      obtain ⟨hcC, hcn, hca⟩ := mem_below.mp hc
      by_contra hcon
      exact lt_irrefl a (lt_trans (hbetween c hcC hcn (lt_of_not_ge hcon)) hca)
    · cases l with
      | bot => exact bot_le
      | coe t => exact le_lo hl.1 hl.2 (hlo t rfl)
  · rintro ⟨hfr, hlo⟩
    refine ⟨hfr.2, fun t ht => ?_, fun h hu => ?_⟩
    · rw [← hlo] at ht
      exact (lo_eq_coe ht).2.2
    · obtain ⟨⟨hhC, hhn, hlh⟩, -⟩ := (upOf_eq_coe_iff C l h).mp hu
      by_contra hcon
      have hha : h < a := lt_of_le_of_ne (not_lt.mp hcon) (ne_of_fresh hfr hhC)
      have := le_lo hhC hhn hha
      rw [hlo] at this
      exact absurd hlh (not_lt.mpr this)

/-! ## Truth of comparisons over columns -/

section Truth

variable {c N : ℕ}

theorem eval3_atom_true (op : CompOp) (a b : SA T c N) (x : Tuple T N) (γ : Fin c → T) :
    (SP.atom op a b).eval3 x γ = Kleene.true ↔
      ((op.strict = true → ValueType.isNull (a.eval x γ) = false
          ∧ ValueType.isNull (b.eval x γ) = false) ∧ op.eval (a.eval x γ) (b.eval x γ)) := by
  show CompOp.eval3 _ _ _ = _ ↔ _
  unfold CompOp.eval3
  by_cases h : op.strict = true ∧ (ValueType.isNull (a.eval x γ) = true
      ∨ ValueType.isNull (b.eval x γ) = true)
  · rw [ite_eq_left (by simpa using h)]
    constructor
    · intro h'; exact absurd h' (by decide)
    · rintro ⟨hs, -⟩
      obtain ⟨ha, hb⟩ := hs h.1
      rcases h.2 with h2 | h2
      · rw [ha] at h2; exact absurd h2 (by decide)
      · rw [hb] at h2; exact absurd h2 (by decide)
  · rw [ite_eq_right (by simpa using h), Kleene.ofBool_eq_true_iff, decide_eq_true_eq]
    constructor
    · intro he
      refine ⟨fun hs => ?_, he⟩
      push Not at h
      cases ha : ValueType.isNull (a.eval x γ) <;> cases hb : ValueType.isNull (b.eval x γ)
      · exact ⟨rfl, rfl⟩
      · exact absurd (h hs) (by simp [hb])
      · exact absurd (h hs) (by simp [ha])
      · exact absurd (h hs) (by simp [ha])
    · exact fun h' => h'.2

theorem eval3_isZ_true (a : SA T c N) (x : Tuple T N) (γ : Fin c → T) :
    (isZ a).eval3 x γ = Kleene.true ↔ a.eval x γ = 0 := by
  rw [eval3_isZ, Kleene.ofBool_eq_true_iff, decide_eq_true_eq]

theorem eval3_isN_true (a : SA T c N) (x : Tuple T N) (γ : Fin c → T) :
    (isN a).eval3 x γ = Kleene.true ↔ a.eval x γ = ValueType.nonzero := by
  rw [eval3_isN, Kleene.ofBool_eq_true_iff, decide_eq_true_eq]

end Truth

/-! ## A component against its cell -/

section CellMatch

variable {c N k : ℕ}

/-- **The component lies in the cell's gap.** -/
def freshIn (a : SA T c N) (x : Fin (7 + k) → SA T c N) : SP T c N :=
  .and (.atom .eq a a) (.and (.or (isN (x (iB k))) (.atom .lt (x (iV k)) a))
    (.or (isN (x (iHB k))) (.atom .lt a (x (iH k)))))

/-- **The component is what the cell codes**: the value itself, or a value
of its gap. -/
def cellMatch (a : SA T c N) (x : Fin (7 + k) → SA T c N) : SP T c N :=
  .or (.and (isZ (x (iF k))) (.atom .syneq a (x (iV k)))) (.and (isN (x (iF k))) (freshIn a x))

@[simp] theorem enc_conc_H (k : ℕ) (a : T) : enc C k (.conc a) (iH k) = 0 := rfl
@[simp] theorem enc_conc_HB (k : ℕ) (a : T) : enc C k (.conc a) (iHB k) = 0 := rfl
@[simp] theorem enc_fresh_H (k : ℕ) (l : WithBot T) (r : ℕ) :
    enc C k (.fresh l r) (iH k) = wtVal (upOf C l) := rfl
@[simp] theorem enc_fresh_HB (k : ℕ) (l : WithBot T) (r : ℕ) :
    enc C k (.fresh l r) (iHB k) = wtFlag (upOf C l) := rfl

/-- **The codes a cell of a descriptor can hold.** -/
def ShapeOK (C : Finset T) (k : ℕ) : Code T → Prop
  | .conc a => a ∈ C
  | .fresh l r => GapOK C l ∧ r ≤ k

/-- **A value fits a code**: it is the code's value, or a fresh value of the
code's gap. -/
def Fits (C : Finset T) (v : T) : Code T → Prop
  | .conc a => v = a
  | .fresh l _ => IsFresh C v ∧ lo C v = l

theorem eval3_cellMatch_true (a : SA T c N) (x : Fin (7 + k) → SA T c N) (r : Tuple T N)
    (γ : Fin c → T) {cd : Code T} (hcd : ShapeOK C k cd)
    (hx : ∀ j, (x j).eval r γ = enc C k cd j) :
    (cellMatch a x).eval3 r γ = Kleene.true ↔ Fits C (a.eval r γ) cd := by
  show ((((isZ (x (iF k))).eval3 r γ).and ((SP.atom .syneq a (x (iV k))).eval3 r γ)).or
    (((isN (x (iF k))).eval3 r γ).and (((SP.atom .eq a a).eval3 r γ).and
      ((((isN (x (iB k))).eval3 r γ).or ((SP.atom .lt (x (iV k)) a).eval3 r γ)).and
        (((isN (x (iHB k))).eval3 r γ).or ((SP.atom .lt a (x (iH k))).eval3 r γ)))))) = Kleene.true
      ↔ _
  simp only [Kleene.or_eq_true_iff, Kleene.and_eq_true_iff, eval3_isZ_true, eval3_isN_true,
    eval3_atom_true, hx]
  set v := a.eval r γ
  cases cd with
  | conc b =>
    simp only [enc_conc_F, enc_conc_V, Fits, nonzero_ne_zero'.symm, false_and, or_false, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun h' => absurd h' (by decide), h⟩⟩
  | fresh l r' =>
    simp only [enc_fresh_F, enc_fresh_V, enc_fresh_B, enc_fresh_H, enc_fresh_HB, Fits,
      nonzero_ne_zero', false_and, false_or, true_and]
    rw [← fresh_lo_iff hcd.1]
    have hs1 : CompOp.strict CompOp.eq = true := rfl
    have hs2 : CompOp.strict CompOp.lt = true := rfl
    simp only [hs1, hs2, true_implies, CompOp.eval, and_self]
    constructor
    · rintro ⟨⟨hvn, -⟩, hlow, hup⟩
      refine ⟨hvn, fun t ht => ?_, fun h hu => ?_⟩
      · subst ht
        rcases hlow with hb | ⟨-, hlt⟩
        · exact absurd hb (by simp [wbFlag, (nonzero_ne_zero' (T := T)).symm])
        · exact hlt
      · rcases hup with hb | ⟨-, hlt⟩
        · rw [hu] at hb; exact absurd hb (by simp [wtFlag, (nonzero_ne_zero' (T := T)).symm])
        · rw [hu] at hlt; exact hlt
    · rintro ⟨hvn, hlow, hup⟩
      refine ⟨⟨hvn, trivial⟩, ?_, ?_⟩
      · cases l with
        | bot => exact Or.inl rfl
        | coe t => exact Or.inr ⟨⟨hcd.1.2, hvn⟩, hlow t rfl⟩
      · cases hu : upOf C l with
        | top => exact Or.inl rfl
        | coe h =>
          obtain ⟨⟨-, hhn, -⟩, -⟩ := (upOf_eq_coe_iff C l h).mp hu
          exact Or.inr ⟨⟨hvn, hhn⟩, hup h hu⟩

end CellMatch

/-! ## Ranks recorded consistently are the ranks -/

section Ranks

variable {k : ℕ}

/-- The fresh components of a row in a value's gap below it. -/
noncomputable def below' (C : Finset T) (par : Fin k → T) (a : T) : Finset T :=
  (Finset.univ.image par).filter (fun b => IsFresh C b ∧ lo C b = lo C a ∧ b < a)

theorem rank_eq_card (C : Finset T) (par : Fin k → T) (a : T) :
    rank C par a = (below' C par a).card := rfl

/-- **Recorded ranks that are ordered as their components and leave no
hole are the ranks.** -/
theorem ranks_eq (par : Fin k → T) (cd : Fin k → Code T) (hfit : ∀ i, Fits C (par i) (cd i))
    (hshape : ∀ i, ShapeOK C k (cd i))
    (hpair : ∀ i j l r l' r', cd i = .fresh l r → cd j = .fresh l' r' → l = l' →
      ((LT.lt (par i) (par j) ↔ LT.lt r r') ∧ (par i = par j ↔ r = r')))
    (hcontig : ∀ i l r, cd i = .fresh l (r + 1) → ∃ j, cd j = .fresh l r) :
    ∀ i, cd i = code C par i := by
  -- a fresh component's cell is a gap cell
  have hgap : ∀ j, IsFresh C (par j) → ∃ r, cd j = .fresh (lo C (par j)) r := by
    intro j hj
    have hf := hfit j
    have hs := hshape j
    cases hc : cd j with
    | conc a =>
      rw [hc] at hf hs
      exact absurd (hf ▸ hs) hj.1
    | fresh l r =>
      rw [hc] at hf
      exact ⟨r, by rw [hf.2]⟩
  have key : ∀ n i l, cd i = .fresh l n → n = rank C par (par i) := by
    intro n
    induction n with
    | zero =>
      intro i l hi
      rw [rank_eq_card, eq_comm, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro b hb
      obtain ⟨hbu, hbf, hbl, hblt⟩ := Finset.mem_filter.mp hb
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hbu
      obtain ⟨rj, hj⟩ := hgap j hbf
      have hfi := hfit i
      rw [hi] at hfi
      have := (hpair j i _ _ _ _ hj hi (by rw [hbl, hfi.2])).1.mp hblt
      exact Nat.not_lt_zero _ this
    | succ m ih =>
      intro i l hi
      obtain ⟨j, hj⟩ := hcontig i l m hi
      have hfi := hfit i
      have hfj := hfit j
      rw [hi] at hfi
      rw [hj] at hfj
      have hmj := ih j l hj
      have hji : par j < par i := (hpair j i _ _ _ _ hj hi rfl).1.mpr (Nat.lt_succ_self m)
      rw [rank_eq_card]
      have hS : below' C par (par i) = insert (par j) (below' C par (par j)) := by
        ext b
        simp only [below', Finset.mem_insert, Finset.mem_filter, Finset.mem_image,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨l', rfl⟩, hbf, hbl, hblt⟩
          obtain ⟨rl, hl'⟩ := hgap l' hbf
          have hgl : lo C (par l') = l := hbl.trans hfi.2
          have hlt := (hpair l' i _ _ _ _ hl' hi hgl).1.mp hblt
          rcases Nat.lt_or_ge rl m with h | h
          · right
            exact ⟨⟨l', rfl⟩, hbf, hbl.trans (hfi.2.trans hfj.2.symm),
              (hpair l' j _ _ _ _ hl' hj hgl).1.mpr h⟩
          · left
            exact (hpair l' j _ _ _ _ hl' hj hgl).2.mpr (by omega)
        · rintro (rfl | ⟨⟨l', rfl⟩, hbf, hbl, hblt⟩)
          · exact ⟨⟨j, rfl⟩, hfj.1, hfj.2.trans hfi.2.symm, hji⟩
          · exact ⟨⟨l', rfl⟩, hbf, hbl.trans (hfj.2.trans hfi.2.symm), hblt.trans hji⟩
      rw [hS, Finset.card_insert_of_notMem (fun h => lt_irrefl _ (Finset.mem_filter.mp h).2.2.2),
        ← rank_eq_card, ← hmj]
  intro i
  have hf := hfit i
  have hs := hshape i
  cases hc : cd i with
  | conc a =>
    rw [hc] at hf hs
    rw [code_of_not_fresh (fun h => h.1 (hf ▸ hs)), hf]
  | fresh l r =>
    rw [hc] at hf
    rw [code_of_fresh hf.1, hf.2, key r i l hc]

/-- **The ranks of a row's codes are recorded consistently.** -/
theorem code_pair (par : Fin k → T) (i j : Fin k) (l l' : WithBot T) (r r' : ℕ)
    (hi : code C par i = .fresh l r) (hj : code C par j = .fresh l' r') (hl : l = l') :
    (LT.lt (par i) (par j) ↔ LT.lt r r') ∧ (par i = par j ↔ r = r') := by
  have hfi : IsFresh C (par i) := by
    by_contra h; rw [code_of_not_fresh h] at hi; cases hi
  have hfj : IsFresh C (par j) := by
    by_contra h; rw [code_of_not_fresh h] at hj; cases hj
  rw [code_of_fresh hfi] at hi
  rw [code_of_fresh hfj] at hj
  injection hi with hi₁ hi₂
  injection hj with hj₁ hj₂
  subst hi₂ hj₂
  have hlo : lo C (par i) = lo C (par j) := by rw [hi₁, hj₁, hl]
  exact ⟨lt_iff_rank_lt (mem_image par i) (mem_image par j) hfi hfj hlo,
    eq_iff_rank_eq (mem_image par i) (mem_image par j) hfi hfj hlo⟩

/-- **A row's ranks leave no hole.** -/
theorem code_contig (par : Fin k → T) (i : Fin k) (l : WithBot T) (r : ℕ)
    (hi : code C par i = .fresh l (r + 1)) : ∃ j, code C par j = .fresh l r := by
  have hfi : IsFresh C (par i) := by
    by_contra h; rw [code_of_not_fresh h] at hi; cases hi
  rw [code_of_fresh hfi] at hi
  injection hi with hi₁ hi₂
  rw [rank_eq_card] at hi₂
  have hne : (below' C par (par i)).Nonempty := by
    rw [← Finset.card_pos, hi₂]; exact Nat.succ_pos r
  set b := (below' C par (par i)).max' hne with hb
  have hbm : b ∈ below' C par (par i) := Finset.max'_mem _ hne
  obtain ⟨hbu, hbf, hbl, hblt⟩ := Finset.mem_filter.mp hbm
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hbu
  refine ⟨j, ?_⟩
  have hfj : IsFresh C (par j) := hj ▸ hbf
  rw [code_of_fresh hfj, hj, hbl, hi₁]
  congr 1
  -- the components below `b` are those below the row's, `b` excepted
  have hS : below' C par (par i) = insert b (below' C par b) := by
    ext x
    simp only [below', Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨hxu, hxf, hxl, hxlt⟩
      have hxm : x ∈ below' C par (par i) := Finset.mem_filter.mpr ⟨hxu, hxf, hxl, hxlt⟩
      rcases eq_or_lt_of_le (Finset.le_max' (below' C par (par i)) x hxm) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hxu, hxf, hxl.trans hbl.symm, h⟩
    · rintro (rfl | ⟨hxu, hxf, hxl, hxlt⟩)
      · exact ⟨hbu, hbf, hbl, hblt⟩
      · exact ⟨hxu, hxf, hxl.trans hbl, hxlt.trans hblt⟩
  rw [hS, Finset.card_insert_of_notMem (fun h => lt_irrefl _ (Finset.mem_filter.mp h).2.2.2)]
    at hi₂
  rw [rank_eq_card]
  omega

end Ranks

/-! ## Unary ranks up to `k` -/

section Therm

theorem therm_lt_iff' {k r r' : ℕ} (hr' : r' ≤ k) :
    (∃ j : Fin k, therm (T := T) k r j = sLo ∧ therm (T := T) k r' j = sHi) ↔ r < r' := by
  constructor
  · rintro ⟨j, h₁, h₂⟩
    unfold therm at h₁ h₂
    by_cases hj : j.val < r
    · rw [ite_eq_left hj] at h₁; exact absurd h₁.symm sLo_ne_sHi
    · by_cases hj' : j.val < r'
      · omega
      · rw [ite_eq_right hj'] at h₂; exact absurd h₂ sLo_ne_sHi
  · intro h
    refine ⟨⟨r, by omega⟩, ?_, ?_⟩
    · unfold therm; rw [ite_eq_right (lt_irrefl r)]
    · unfold therm; rw [ite_eq_left h]

theorem therm_eq_iff' {k r r' : ℕ} (hr : r ≤ k) (hr' : r' ≤ k) :
    (∀ j : Fin k, therm (T := T) k r j = therm (T := T) k r' j) ↔ r = r' := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h ⟨r, by omega⟩
      unfold therm at this
      rw [ite_eq_right (lt_irrefl r), ite_eq_left hlt] at this
      exact sLo_ne_sHi this
    · have := h ⟨r', by omega⟩
      unfold therm at this
      rw [ite_eq_left hlt, ite_eq_right (lt_irrefl r')] at this
      exact sLo_ne_sHi this.symm
  · rintro rfl _; rfl

theorem therm_zero_iff {k r : ℕ} (hr : r ≤ k) :
    (∀ j : Fin k, therm (T := T) k r j = sLo) ↔ r = 0 := by
  constructor
  · intro h
    by_contra hne
    have := h ⟨0, by omega⟩
    unfold therm at this
    rw [ite_eq_left (Nat.pos_of_ne_zero hne)] at this
    exact sLo_ne_sHi this.symm
  · rintro rfl j
    unfold therm; rw [ite_eq_right (Nat.not_lt_zero _)]

/-- **One unary rank is the next of another**: at one column the first is
low and the second high, and they agree elsewhere. -/
theorem therm_succ_iff {k r r' : ℕ} (hr : r ≤ k) (hr' : r' ≤ k) :
    (∃ m : Fin k, therm (T := T) k r m = sLo ∧ therm (T := T) k r' m = sHi
      ∧ ∀ m' : Fin k, m' ≠ m → therm (T := T) k r m' = therm (T := T) k r' m') ↔ r' = r + 1 := by
  constructor
  · rintro ⟨m, h₁, h₂, h₃⟩
    unfold therm at h₁ h₂ h₃
    have hm₁ : ¬ m.val < r := fun h => by rw [ite_eq_left h] at h₁; exact sLo_ne_sHi h₁.symm
    have hm₂ : m.val < r' := by
      by_contra h; rw [ite_eq_right h] at h₂; exact sLo_ne_sHi h₂
    by_contra hne
    by_cases hmr : m.val = r
    · -- the column after `m` is high in the second and low in the first
      have hlt : r + 1 < r' := by omega
      have := h₃ ⟨r + 1, by omega⟩ (fun h => by rw [Fin.ext_iff] at h; simp at h; omega)
      simp only at this
      rw [ite_eq_right (by omega), ite_eq_left hlt] at this
      exact sLo_ne_sHi this
    · have := h₃ ⟨r, by omega⟩ (fun h => by rw [Fin.ext_iff] at h; simp at h; omega)
      simp only at this
      rw [ite_eq_right (lt_irrefl r), ite_eq_left (by omega)] at this
      exact sLo_ne_sHi this
  · intro h
    subst h
    refine ⟨⟨r, by omega⟩, ?_, ?_, fun m' hm' => ?_⟩
    · unfold therm; rw [ite_eq_right (lt_irrefl r)]
    · unfold therm; rw [ite_eq_left (Nat.lt_succ_self r)]
    · unfold therm
      have : m'.val ≠ r := fun h => hm' (Fin.ext h)
      by_cases h : m'.val < r
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]

end Therm

/-! ## The descriptor of a row, as a predicate -/

section MatchSP

variable {c N k : ℕ}

/-- Two cells are of one gap. -/
def sameGap (x y : Fin (7 + k) → SA T c N) : SP T c N :=
  .and (.atom .syneq (x (iB k)) (y (iB k))) (.atom .syneq (x (iV k)) (y (iV k)))

/-- Two predicates agree. -/
def iffSP (p q : SP T c N) : SP T c N := .or (.and p q) (.and (.not p) (.not q))

/-- **Two fresh cells of one gap record ranks ordered as their
components.** -/
def rankPair (a b : SA T c N) (x y : Fin (7 + k) → SA T c N) : SP T c N :=
  .or (isZ (x (iF k))) (.or (isZ (y (iF k))) (.or (.not (sameGap x y))
    (.and (iffSP (.atom .lt a b) (thLt x y)) (iffSP (.atom .eq a b) (thEq x y)))))

/-- The rank is `0`. -/
def thZero (x : Fin (7 + k) → SA T c N) : SP T c N :=
  andAll ((List.finRange k).map (fun m => isLo (x (iR m))))

/-- The second rank is the next of the first. -/
def thSucc (x y : Fin (7 + k) → SA T c N) : SP T c N :=
  orAll ((List.finRange k).map (fun m => .and (isLo (x (iR m))) (.and (isHi (y (iR m)))
    (andAll ((List.finRange k).map (fun m' =>
      if m' = m then .tru else .atom .syneq (x (iR m')) (y (iR m'))))))))

/-- **A fresh cell's rank leaves no hole below it.** -/
def contigSP (d : Fin k → Fin (7 + k) → SA T c N) (i : Fin k) : SP T c N :=
  .or (isZ (d i (iF k))) (.or (thZero (d i)) (orAll ((List.finRange k).map (fun j =>
    .and (isN (d j (iF k))) (.and (sameGap (d j) (d i)) (thSucc (d j) (d i)))))))

/-- **The descriptor's cells are the codes of the row's components.** -/
def matchSP (u : Fin k → SA T c N) (d : Fin k → Fin (7 + k) → SA T c N) : SP T c N :=
  .and (andAll ((List.finRange k).map (fun i => cellMatch (u i) (d i))))
    (.and (andAll ((List.finRange k).flatMap (fun i => (List.finRange k).map (fun j =>
      rankPair (u i) (u j) (d i) (d j)))))
      (andAll ((List.finRange k).map (fun i => contigSP d i))))

theorem iffSP_ofBool (p q : SP T c N) (x : Tuple T N) (γ : Fin c → T) (P Q : Prop) [Decidable P]
    [Decidable Q] (hp : p.eval3 x γ = Kleene.ofBool (decide P))
    (hq : q.eval3 x γ = Kleene.ofBool (decide Q)) :
    (iffSP p q).eval3 x γ = Kleene.ofBool (decide (P ↔ Q)) := by
  show ((p.eval3 x γ).and (q.eval3 x γ)).or (((p.eval3 x γ).not).and ((q.eval3 x γ).not)) = _
  rw [hp, hq]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, Kleene.ofBool, Kleene.and, Kleene.or,
    Kleene.not]

theorem eval3_sameGap (x y : Fin (7 + k) → SA T c N) (r : Tuple T N) (γ : Fin c → T)
    {l l' : WithBot T} {s s' : ℕ} (hx : ∀ j, (x j).eval r γ = enc C k (.fresh l s) j)
    (hy : ∀ j, (y j).eval r γ = enc C k (.fresh l' s') j) :
    (sameGap x y).eval3 r γ = Kleene.ofBool (decide (l = l')) := by
  show ((SP.atom .syneq _ _).eval3 r γ).and ((SP.atom .syneq _ _).eval3 r γ) = _
  rw [eval3_atom_syneq, eval3_atom_syneq, hx, hx, hy, hy, enc_fresh_B, enc_fresh_B, enc_fresh_V,
    enc_fresh_V, Kleene.and_ofBool, ← Bool.decide_and]
  exact ofBool_congr (withBot_eq_iff (C := C) l l').symm

omit [ValueType T] in
@[simp] theorem SA.eval_const' (a : T) (x : Tuple T N) (γ : Fin c → T) :
    (SA.const a : SA T c N).eval x γ = a := rfl

theorem thR {x : Fin (7 + k) → SA T c N} {r : Tuple T N} {γ : Fin c → T} {l : WithBot T} {s : ℕ}
    (hx : ∀ j, (x j).eval r γ = enc C k (.fresh l s) j) (j : Fin k) :
    (x (iR j)).eval r γ = therm k s j := (hx _).trans (enc_fresh_R _ _ _ _)

theorem eval3_thZero (x : Fin (7 + k) → SA T c N) (r : Tuple T N) (γ : Fin c → T)
    {l : WithBot T} {s : ℕ} (hs : s ≤ k) (hx : ∀ j, (x j).eval r γ = enc C k (.fresh l s) j) :
    (thZero x).eval3 r γ = Kleene.ofBool (decide (s = 0)) := by
  unfold thZero
  rw [eval3_andAll _ _ _ (fun p hp => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hp
    rw [isLo, eval3_atom_syneq]; exact ofBool_definite _)]
  refine ofBool_congr ?_
  rw [← therm_zero_iff (T := T) hs]
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, isLo, eval3_atom_syneq, Kleene.ofBool_eq_true_iff, decide_eq_true_eq,
    SA.eval_const', thR hx]

theorem eval3_thSucc (x y : Fin (7 + k) → SA T c N) (r : Tuple T N) (γ : Fin c → T)
    {l l' : WithBot T} {s s' : ℕ} (hs : s ≤ k) (hs' : s' ≤ k)
    (hx : ∀ j, (x j).eval r γ = enc C k (.fresh l s) j)
    (hy : ∀ j, (y j).eval r γ = enc C k (.fresh l' s') j) :
    (thSucc x y).eval3 r γ = Kleene.ofBool (decide (s' = s + 1)) := by
  have hin : ∀ m : Fin k, (andAll ((List.finRange k).map (fun m' : Fin k =>
      if m' = m then (SP.tru : SP T c N) else .atom .syneq (x (iR m')) (y (iR m'))))).eval3 r γ
      = Kleene.ofBool (decide (∀ m' : Fin k, m' ≠ m → therm (T := T) k s m' = therm k s' m')) := by
    intro m
    rw [eval3_andAll _ _ _ (fun p hp => by
      obtain ⟨m', -, rfl⟩ := List.mem_map.mp hp
      split
      · exact Or.inl rfl
      · rw [eval3_atom_syneq]; exact ofBool_definite _)]
    refine ofBool_congr ⟨fun h m' hm' => ?_, fun h p hp => ?_⟩
    · have := h _ (List.mem_map.mpr ⟨m', List.mem_finRange _, rfl⟩)
      simp only [hm', ite_false, eval3_atom_syneq, Kleene.ofBool_eq_true_iff,
        decide_eq_true_eq, thR hx, thR hy] at this
      exact this
    · obtain ⟨m', -, rfl⟩ := List.mem_map.mp hp
      by_cases hm' : m' = m
      · simp only [hm', ite_true]; rfl
      · simp only [hm', ite_false, eval3_atom_syneq, Kleene.ofBool_eq_true_iff,
          decide_eq_true_eq, thR hx, thR hy]
        exact h m' hm'
  have hterm : ∀ m : Fin k, (SP.and (isLo (x (iR m))) (.and (isHi (y (iR m)))
      (andAll ((List.finRange k).map (fun m' : Fin k =>
        if m' = m then (SP.tru : SP T c N) else .atom .syneq (x (iR m')) (y (iR m'))))))).eval3 r γ
      = Kleene.ofBool (decide (therm (T := T) k s m = sLo ∧ therm (T := T) k s' m = sHi
        ∧ ∀ m' : Fin k, m' ≠ m → therm (T := T) k s m' = therm k s' m')) := by
    intro m
    show ((isLo _).eval3 r γ).and (((isHi _).eval3 r γ).and _) = _
    rw [isLo, isHi, eval3_atom_syneq, eval3_atom_syneq, hin, Kleene.and_ofBool, Kleene.and_ofBool,
      ← Bool.decide_and, ← Bool.decide_and]
    simp only [SA.eval_const', thR hx, thR hy]
  unfold thSucc
  rw [eval3_orAll _ _ _ (fun p hp => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hp
    rw [hterm]
    exact ofBool_definite _)]
  refine ofBool_congr ?_
  rw [← therm_succ_iff (T := T) hs hs']
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and, hterm,
    Kleene.ofBool_eq_true_iff, decide_eq_true_eq]

theorem SP.eval3_and' (p q : SP T c N) (r : Tuple T N) (γ : Fin c → T) :
    (SP.and p q).eval3 r γ = (p.eval3 r γ).and (q.eval3 r γ) := rfl

theorem SP.eval3_or' (p q : SP T c N) (r : Tuple T N) (γ : Fin c → T) :
    (SP.or p q).eval3 r γ = (p.eval3 r γ).or (q.eval3 r γ) := rfl

theorem andAll_true (ps : List (SP T c N)) (r : Tuple T N) (γ : Fin c → T) :
    (andAll ps).eval3 r γ = Kleene.true ↔ ∀ p ∈ ps, p.eval3 r γ = Kleene.true := by
  induction ps with
  | nil => simp [andAll, SP.eval3]
  | cons p ps ih =>
    show ((p.eval3 r γ).and ((andAll ps).eval3 r γ)) = Kleene.true ↔ _
    rw [Kleene.and_eq_true_iff, ih, List.forall_mem_cons]

theorem orAll_true (ps : List (SP T c N)) (r : Tuple T N) (γ : Fin c → T) :
    (orAll ps).eval3 r γ = Kleene.true ↔ ∃ p ∈ ps, p.eval3 r γ = Kleene.true := by
  induction ps with
  | nil => simp [orAll, SP.eval3]
  | cons p ps ih =>
    show ((p.eval3 r γ).or ((orAll ps).eval3 r γ)) = Kleene.true ↔ _
    rw [Kleene.or_eq_true_iff, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem isZ_fresh {x : Fin (7 + k) → SA T c N} {r : Tuple T N} {γ : Fin c → T} {l : WithBot T}
    {s : ℕ} (hx : ∀ j, (x j).eval r γ = enc C k (.fresh l s) j) :
    (isZ (x (iF k))).eval3 r γ = Kleene.false := by
  rw [eval3_isZ, hx, enc_fresh_F]
  simp [Kleene.ofBool, nonzero_ne_zero']

theorem isZ_conc {x : Fin (7 + k) → SA T c N} {r : Tuple T N} {γ : Fin c → T} {a : T}
    (hx : ∀ j, (x j).eval r γ = enc C k (.conc a) j) :
    (isZ (x (iF k))).eval3 r γ = Kleene.true := by
  rw [eval3_isZ, hx, enc_conc_F]; simp [Kleene.ofBool]

/-- **Two fresh cells against their components.** -/
theorem eval3_rankPair_fresh (a b : SA T c N) (x y : Fin (7 + k) → SA T c N) (r : Tuple T N)
    (γ : Fin c → T) {l l' : WithBot T} {s s' : ℕ} (hs : s ≤ k) (hs' : s' ≤ k)
    (hx : ∀ j, (x j).eval r γ = enc C k (.fresh l s) j)
    (hy : ∀ j, (y j).eval r γ = enc C k (.fresh l' s') j)
    (ha : ValueType.isNull (a.eval r γ) = false) (hb : ValueType.isNull (b.eval r γ) = false) :
    (rankPair a b x y).eval3 r γ = Kleene.true ↔
      (l = l' → ((LT.lt (a.eval r γ) (b.eval r γ) ↔ LT.lt s s')
        ∧ (a.eval r γ = b.eval r γ ↔ s = s'))) := by
  have h1 := iffSP_ofBool (.atom .lt a b) (thLt x y) r γ (LT.lt (a.eval r γ) (b.eval r γ))
    (LT.lt s s') (by rw [eval3_atom_of_nonNull _ _ _ _ _ ha hb]; rfl)
    (by rw [eval3_thLt x y r γ (thR hx) (thR hy)]
        exact ofBool_congr (therm_lt_iff' (T := T) hs'))
  have h2 := iffSP_ofBool (.atom .eq a b) (thEq x y) r γ (a.eval r γ = b.eval r γ)
    (s = s') (by rw [eval3_atom_of_nonNull _ _ _ _ _ ha hb]; rfl)
    (by rw [eval3_thEq x y r γ (thR hx) (thR hy)]
        exact ofBool_congr (therm_eq_iff' (T := T) hs hs'))
  show ((isZ (x (iF k))).eval3 r γ).or (((isZ (y (iF k))).eval3 r γ).or
    (((sameGap x y).eval3 r γ).not.or (((iffSP _ _).eval3 r γ).and ((iffSP _ _).eval3 r γ))))
      = Kleene.true ↔ _
  rw [isZ_fresh hx, isZ_fresh hy, eval3_sameGap x y r γ hx hy, h1, h2, Kleene.not_ofBool,
    Kleene.and_ofBool, Kleene.or_ofBool]
  simp only [Kleene.or_false_left, Kleene.ofBool_eq_true_iff, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **A fresh cell's rank against the row's other cells.** -/
theorem eval3_contigSP_fresh (d : Fin k → Fin (7 + k) → SA T c N) (r : Tuple T N) (γ : Fin c → T)
    (cd : Fin k → Code T) (hshape : ∀ i, ShapeOK C k (cd i))
    (hd : ∀ i j, (d i j).eval r γ = enc C k (cd i) j) (i : Fin k) {l : WithBot T} {s : ℕ}
    (hi : cd i = .fresh l s) :
    (contigSP d i).eval3 r γ = Kleene.true ↔ (s = 0 ∨ ∃ j s', cd j = .fresh l s' ∧ s = s' + 1) := by
  have hdi : ∀ j, (d i j).eval r γ = enc C k (.fresh l s) j := fun j => by rw [hd, hi]
  have hsk : s ≤ k := by have := hshape i; rw [hi] at this; exact this.2
  unfold contigSP
  rw [SP.eval3_or', SP.eval3_or', Kleene.or_eq_true_iff, Kleene.or_eq_true_iff, isZ_fresh hdi,
    eval3_thZero _ r γ hsk hdi,
    orAll_true, Kleene.ofBool_eq_true_iff, decide_eq_true_eq]
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and]
  rw [show (Kleene.false = Kleene.true) ↔ False from by decide, false_or]
  refine or_congr_right ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, hj⟩ := h
    rw [SP.eval3_and', SP.eval3_and', Kleene.and_eq_true_iff, Kleene.and_eq_true_iff,
      eval3_isN_true] at hj
    cases hc : cd j with
    | conc a =>
      rw [hd, hc, enc_conc_F] at hj
      exact absurd hj.1 nonzero_ne_zero'.symm
    | fresh l' s' =>
      have hdj : ∀ m, (d j m).eval r γ = enc C k (.fresh l' s') m := fun m => by rw [hd, hc]
      have hsk' : s' ≤ k := by have := hshape j; rw [hc] at this; exact this.2
      rw [eval3_sameGap _ _ r γ hdj hdi, eval3_thSucc _ _ r γ hsk' hsk hdj hdi,
        Kleene.ofBool_eq_true_iff, Kleene.ofBool_eq_true_iff, decide_eq_true_eq,
        decide_eq_true_eq] at hj
      exact ⟨j, s', by rw [hc, hj.2.1], hj.2.2⟩
  · obtain ⟨j, s', hj, hs⟩ := h
    refine ⟨j, ?_⟩
    have hdj : ∀ m, (d j m).eval r γ = enc C k (.fresh l s') m := fun m => by rw [hd, hj]
    have hsk' : s' ≤ k := by have := hshape j; rw [hj] at this; exact this.2
    rw [SP.eval3_and', SP.eval3_and', Kleene.and_eq_true_iff, Kleene.and_eq_true_iff,
      eval3_isN_true, hdj, enc_fresh_F,
      eval3_sameGap _ _ r γ hdj hdi, eval3_thSucc _ _ r γ hsk' hsk hdj hdi,
      Kleene.ofBool_eq_true_iff, Kleene.ofBool_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨rfl, rfl, hs⟩

/-- A value fits its own code. -/
theorem fits_code (par : Fin k → T) (i : Fin k) : Fits C (par i) (code C par i) := by
  by_cases h : IsFresh C (par i)
  · rw [code_of_fresh h]; exact ⟨h, rfl⟩
  · rw [code_of_not_fresh h]; rfl

/-- **Over cells the cut can produce, the predicate holds exactly of a
row's own descriptor.** -/
theorem eval3_matchSP_true (u : Fin k → SA T c N) (d : Fin k → Fin (7 + k) → SA T c N)
    (r : Tuple T N) (γ : Fin c → T) (par : Fin k → T) (cd : Fin k → Code T)
    (hu : ∀ i, (u i).eval r γ = par i) (hd : ∀ i j, (d i j).eval r γ = enc C k (cd i) j)
    (hshape : ∀ i, ShapeOK C k (cd i)) :
    (matchSP u d).eval3 r γ = Kleene.true ↔ ∀ i, cd i = code C par i := by
  have hcell : ∀ i, (cellMatch (u i) (d i)).eval3 r γ = Kleene.true ↔ Fits C (par i) (cd i) :=
    fun i => by rw [eval3_cellMatch_true (u i) (d i) r γ (hshape i) (hd i), hu]
  have hnn : ∀ i l s, Fits C (par i) (cd i) →
      cd i = .fresh l s → ValueType.isNull (par i) = false :=
    fun i l s hf hc => by rw [hc] at hf; exact hf.1.2
  unfold matchSP
  rw [SP.eval3_and', SP.eval3_and', Kleene.and_eq_true_iff, Kleene.and_eq_true_iff, andAll_true,
    andAll_true, andAll_true]
  have hmemC : ∀ i, cellMatch (u i) (d i) ∈
      (List.finRange k).map (fun i => cellMatch (u i) (d i)) :=
    fun i => List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hmemK : ∀ i, contigSP d i ∈ (List.finRange k).map (fun i => contigSP d i) :=
    fun i => List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hmemP : ∀ i j, rankPair (u i) (u j) (d i) (d j) ∈ (List.finRange k).flatMap (fun i =>
      (List.finRange k).map (fun j => rankPair (u i) (u j) (d i) (d j))) :=
    fun i j => List.mem_flatMap.mpr ⟨i, List.mem_finRange _,
      List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩⟩
  constructor
  · rintro ⟨hm', hp, hc'⟩
    have hm : ∀ i, (cellMatch (u i) (d i)).eval3 r γ = Kleene.true := fun i => hm' _ (hmemC i)
    have hc : ∀ i, (contigSP d i).eval3 r γ = Kleene.true := fun i => hc' _ (hmemK i)
    have hfit : ∀ i, Fits C (par i) (cd i) := fun i => (hcell i).mp (hm i)
    refine ranks_eq par cd hfit hshape (fun i j l s l' s' hi hj hl => ?_)
      (fun i l s hi => ?_)
    · have := hp _ (hmemP i j)
      have hdi : ∀ m, (d i m).eval r γ = enc C k (.fresh l s) m := fun m => by rw [hd, hi]
      have hdj : ∀ m, (d j m).eval r γ = enc C k (.fresh l' s') m := fun m => by rw [hd, hj]
      have hsi : s ≤ k := by have := hshape i; rw [hi] at this; exact this.2
      have hsj : s' ≤ k := by have := hshape j; rw [hj] at this; exact this.2
      rw [eval3_rankPair_fresh (u i) (u j) (d i) (d j) r γ hsi hsj hdi hdj
        (by rw [hu]; exact hnn i l s (hfit i) hi) (by rw [hu]; exact hnn j l' s' (hfit j) hj),
        hu, hu] at this
      exact this hl
    · have hdi := hd i
      rcases (eval3_contigSP_fresh d r γ cd hshape hd i hi).mp (hc i) with h | ⟨j, s', hj, hs⟩
      · exact absurd h (Nat.succ_ne_zero s)
      · exact ⟨j, by rw [hj, show s' = s by omega]⟩
  · intro hcd
    refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (hcell i).mpr (hcd i ▸ fits_code par i)
    · obtain ⟨i, -, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      cases hci : cd i with
      | conc a =>
        have hdi : ∀ m, (d i m).eval r γ = enc C k (.conc a) m := fun m => by rw [hd, hci]
        show ((isZ _).eval3 r γ).or _ = Kleene.true
        rw [isZ_conc hdi]; rfl
      | fresh l s =>
        cases hcj : cd j with
        | conc a =>
          have hdi : ∀ m, (d i m).eval r γ = enc C k (.fresh l s) m := fun m => by rw [hd, hci]
          have hdj : ∀ m, (d j m).eval r γ = enc C k (.conc a) m := fun m => by rw [hd, hcj]
          show ((isZ _).eval3 r γ).or (((isZ _).eval3 r γ).or _) = Kleene.true
          rw [isZ_fresh hdi, isZ_conc hdj]; rfl
        | fresh l' s' =>
          have hdi : ∀ m, (d i m).eval r γ = enc C k (.fresh l s) m := fun m => by rw [hd, hci]
          have hdj : ∀ m, (d j m).eval r γ = enc C k (.fresh l' s') m := fun m => by rw [hd, hcj]
          have hsi : s ≤ k := by have := hshape i; rw [hci] at this; exact this.2
          have hsj : s' ≤ k := by have := hshape j; rw [hcj] at this; exact this.2
          have hfi := hcd i ▸ fits_code par i
          have hfj := hcd j ▸ fits_code par j
          rw [eval3_rankPair_fresh (u i) (u j) (d i) (d j) r γ hsi hsj hdi hdj
            (by rw [hu]; exact hnn i l s hfi hci) (by rw [hu]; exact hnn j l' s' hfj hcj), hu, hu]
          exact code_pair par i j l l' s s' (hci ▸ (hcd i).symm) (hcj ▸ (hcd j).symm)
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      cases hci : cd i with
      | conc a =>
        have hdi : ∀ m, (d i m).eval r γ = enc C k (.conc a) m := fun m => by rw [hd, hci]
        show ((isZ _).eval3 r γ).or _ = Kleene.true
        rw [isZ_conc hdi]; rfl
      | fresh l s =>
        rw [eval3_contigSP_fresh d r γ cd hshape hd i hci]
        rcases Nat.eq_zero_or_pos s with h | h
        · exact Or.inl h
        · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
          obtain ⟨j, hj⟩ := code_contig par i l s' (hci ▸ (hcd i).symm)
          exact Or.inr ⟨j, s', by rw [hcd j, hj], rfl⟩

end MatchSP

/-! ## Reading an output cell back as a value -/

section Decode

variable {c N k : ℕ}

/-- Two cells are equal, column by column. -/
def cellEq (x y : Fin (7 + k) → SA T c N) : SP T c N :=
  andAll ((List.finRange (7 + k)).map (fun j => .atom .syneq (x j) (y j)))

/-- **A value is what an output cell codes**: the cell's value, or the
component whose descriptor cell the output cell is. -/
def decCell (w : SA T c N) (x : Fin (7 + k) → SA T c N) (u : Fin k → SA T c N)
    (d : Fin k → Fin (7 + k) → SA T c N) : SP T c N :=
  .or (.and (isZ (x (iF k))) (.atom .syneq w (x (iV k))))
    (.and (isN (x (iF k))) (orAll ((List.finRange k).map (fun i =>
      .and (cellEq x (d i)) (.atom .syneq w (u i))))))

theorem eval3_cellEq_true (x y : Fin (7 + k) → SA T c N) (r : Tuple T N) (γ : Fin c → T) :
    (cellEq x y).eval3 r γ = Kleene.true ↔ ∀ j, (x j).eval r γ = (y j).eval r γ := by
  unfold cellEq
  rw [andAll_true]
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, eval3_atom_syneq, Kleene.ofBool_eq_true_iff, decide_eq_true_eq]

/-- **An output cell decodes to the value it codes.** -/
theorem eval3_decCell_true (w : SA T c N) (x : Fin (7 + k) → SA T c N) (u : Fin k → SA T c N)
    (d : Fin k → Fin (7 + k) → SA T c N) (r : Tuple T N) (γ : Fin c → T) (par : Fin k → T)
    (v : T) (hu : ∀ i, (u i).eval r γ = par i)
    (hd : ∀ i j, (d i j).eval r γ = enc C k (code C par i) j)
    (hx : ∀ j, (x j).eval r γ = enc C k (vcode C par v) j) :
    (decCell w x u d).eval3 r γ = Kleene.true ↔ w.eval r γ = v := by
  unfold decCell
  rw [SP.eval3_or', SP.eval3_and', SP.eval3_and', Kleene.or_eq_true_iff, Kleene.and_eq_true_iff,
    Kleene.and_eq_true_iff, eval3_isZ_true, eval3_isN_true, eval3_atom_syneq, orAll_true,
    Kleene.ofBool_eq_true_iff, decide_eq_true_eq, hx, hx]
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and, SP.eval3_and',
    Kleene.and_eq_true_iff, eval3_cellEq_true, eval3_atom_syneq, Kleene.ofBool_eq_true_iff,
    decide_eq_true_eq, hx, hd, hu]
  by_cases h : ∃ i, IsFresh C (par i) ∧ par i = v
  · obtain ⟨i₀, hi₀, rfl⟩ := h
    rw [vcode_par, code_of_fresh hi₀, enc_fresh_F]
    simp only [nonzero_ne_zero', false_and, false_or, true_and]
    constructor
    · rintro ⟨i, heq, hw⟩
      have hc : code C par i₀ = code C par i := by
        refine enc_inj (C := C) (rankOK_code par i₀) (rankOK_code par i) (funext heq ▸ ?_)
        rw [code_of_fresh hi₀]
      rw [hw]
      exact (code_eq_code_iff.mp hc).symm
    · intro hw
      exact ⟨i₀, fun j => by rw [code_of_fresh hi₀], hw⟩
  · rw [vcode_of_not par (fun i hi he => h ⟨i, hi, he⟩), enc_conc_F, enc_conc_V]
    simp only [true_and, (nonzero_ne_zero' (T := T)).symm, false_and, or_false]

end Decode

end Sym
