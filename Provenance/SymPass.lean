import Provenance.SymOver
import Provenance.RecursionBasisTheorem

/-!
# The apply replaced by products, through a whole query

`Provenance.SymApply` writes one apply with products (`Sym.applyX`), given
its right side in the fragment without the apply and a closed *pool*: a
unary query holding every value of the left side's rows. This module runs
that replacement through a query over `{∅, Π, σ, apply, γ, win, μ^⊎}`,
from the leaves up, so that every query of that fragment is matched by one
over `{∅, Π, σ, ×, γ, win, μ^⊎}` (`Sym.basisProdOps`).

The pool of an apply outside a recursion is the values of its left side.
Inside a recursive term the left side reads the round, so its values are
those of the round and those the term creates; the latter are bounded by a
closed query (`Cr`), built from the leaves up alongside the term: the
constants and context values a projection may emit, and the cut of each
apply's right side. A recursion's rounds then hold only values of its base
and of its body's `Cr`, and that closed union is the pool `W` its body's
applies read. Each recursion is renamed to a name of the supply, as the
copies of its base the pool holds would otherwise nest a recursion inside
one of the same name.
-/

variable {T : Type} [ValueType T]

namespace Sym

/-! ## Reading an instance away from a name -/

theorem settlesAt_assign_of_noMention' {s : String} {m : ℕ} (X : Relation T m) {c n : ℕ}
    {κ : Fin n → ColKind} (q : AggQueryIn T c n κ) (hq : q.noMention s) (D : Database T)
    (γ : Fin c → T) (h : q.SettlesAt D γ) : q.SettlesAt (D.assign s X) γ :=
  AggQueryIn.settlesAt_of_noMention q hq
    (fun _k s' hs' =>
      (Database.find_assign_of_ne s s' X D
          (fun hc => (hs'.resolve_right List.not_mem_nil) hc.2)).symm)
    γ h

theorem evaluatePlain_hole_assign {c m : ℕ} (s : String) (κ : Fin m → ColKind) (X : Relation T m)
    (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.Hole m s κ).evaluatePlain (D.assign s X) γ = X := by
  simp only [AggQueryIn.evaluatePlain, Database.find_assign]

/-! ## A bag recursion under another name -/

/-- **A bag recursion renamed**: its base and body matched, the body at
the rounds of the source (which a predicate `P` on rounds describes), give
the renamed recursion defined and equal wherever the source is. -/
theorem mu_rename {c n : ℕ} {κ κ' : Fin n → ColKind} (s t : String)
    (q₀ : AggQueryIn T c n κ) (q₀' : AggQueryIn T c n κ')
    (q₁ : AggQueryIn T c n κ [(s, n)]) (q₁' : AggQueryIn T c n κ' [(t, n)])
    (D : Database T) (γ : Fin c → T) (hset : (AggQueryIn.Mu s q₀ q₁).SettlesAt D γ)
    (h₀ : q₀'.SettlesAt D γ ∧ q₀.evaluatePlain D γ = q₀'.evaluatePlain D γ)
    (P : Relation T n → Prop) (hP₀ : P (q₀.evaluatePlain D γ)) (hPz : P 0)
    (h₁ : ∀ X : Relation T n, P X → q₁.SettlesAt (D.assign s X) γ →
      q₁'.SettlesAt (D.assign t X) γ
        ∧ q₁.evaluatePlain (D.assign s X) γ = q₁'.evaluatePlain (D.assign t X) γ
        ∧ P (q₁.evaluatePlain (D.assign s X) γ)) :
    (AggQueryIn.Mu t q₀' q₁').SettlesAt D γ
      ∧ (AggQueryIn.Mu s q₀ q₁).evaluatePlain D γ
          = (AggQueryIn.Mu t q₀' q₁').evaluatePlain D γ := by
  obtain ⟨hs₀, h0, ⟨m, hm⟩, hk⟩ := hset
  have hsub : ∀ {X Y : Relation T n}, X = Y →
      q₁.SettlesAt (D.assign s X) γ → q₁.SettlesAt (D.assign s Y) γ :=
    fun h hx => h ▸ hx
  have hPr : ∀ j, P ((fun X : Multiset (Tuple T n) => q₁.evaluatePlain (D.assign s X) γ)^[j]
      (q₀.evaluatePlain D γ)) := by
    intro j
    induction j with
    | zero => exact hP₀
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (h₁ _ ih (hk j)).2.2
  have hround : ∀ j,
      (fun X : Multiset (Tuple T n) => q₁'.evaluatePlain (D.assign t X) γ)^[j]
          (q₀'.evaluatePlain D γ)
        = (fun X : Multiset (Tuple T n) => q₁.evaluatePlain (D.assign s X) γ)^[j]
          (q₀.evaluatePlain D γ) := by
    intro j
    induction j with
    | zero => exact h₀.2.symm
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact (h₁ _ (hPr j) (hk j)).2.1.symm
  have hkm : q₁.SettlesAt (D.assign s (0 : Relation T n)) γ := hsub hm (hk (m + 1))
  have hz₁ : (q₁'.evaluatePlain (D.assign t (0 : Relation T n)) γ : Multiset (Tuple T n)) = 0 := by
    rw [← (h₁ _ hPz hkm).2.1]
    exact h0
  have hsub' : ∀ {X Y : Relation T n}, X = Y →
      q₁'.SettlesAt (D.assign t X) γ → q₁'.SettlesAt (D.assign t Y) γ :=
    fun h hx => h ▸ hx
  refine ⟨⟨h₀.1, hz₁, ⟨m, (hround (m + 1)).trans hm⟩,
    fun j => hsub' (hround j).symm (h₁ _ (hPr j) (hk j)).1⟩, ?_⟩
  simp only [AggQueryIn.evaluatePlain]
  rw [muSumFix_eq_of_empty h0 hm,
    muSumFix_eq_of_empty hz₁ ((hround (m + 1)).trans hm)]
  exact muSum_congr_of_iterate m fun i _ => (hround i).symm

/-! ## The names a term's pass binds around its pool -/

/-- **The names the pass of a recursive term binds around the pool it is
given**: at each apply on the way to the hole, the union building the
apply's pool (slice 4) and the union inside the apply over it (slice 1 of
the apply's own supply); the child on the way to the hole has slice 1. -/
inductive Enc : (ℕ → String) → String → Prop
  | vq (f : ℕ → String) (i : ℕ) : Enc f (part f 4 i)
  | vs (f : ℕ → String) (i : ℕ) : Enc f (part (part f 0) 1 i)
  | down (f : ℕ → String) (x : String) : Enc (part f 1) x → Enc f x

theorem enc_index {f : ℕ → String} {x : String} (h : Enc f x) :
    ∃ i, x = f i ∧ (i % 8 = 4 ∨ i % 64 = 8 ∨ i % 8 = 1) := by
  induction h with
  | vq f i => exact ⟨8 * i + 4, rfl, Or.inl (by omega)⟩
  | vs f i => exact ⟨8 * (8 * i + 1) + 0, rfl, Or.inr (Or.inl (by omega))⟩
  | down f x _ ih =>
    obtain ⟨i, rfl, -⟩ := ih
    exact ⟨8 * i + 1, rfl, Or.inr (Or.inr (by omega))⟩

theorem not_enc {f : ℕ → String} (hf : Function.Injective f) {i : ℕ}
    (hi : i % 8 ≠ 4 ∧ i % 64 ≠ 8 ∧ i % 8 ≠ 1) : ¬ Enc f (f i) := fun h => by
  obtain ⟨j, hj, hj'⟩ := enc_index h
  have := hf hj
  subst this
  omega

/-- A name of slice 1 binding around the pool binds around the pool of
the child. -/
theorem enc_part1 {f : ℕ → String} (hf : Function.Injective f) {j : ℕ}
    (h : Enc f (part f 1 j)) : Enc (part f 1) (part f 1 j) := by
  generalize hx : part f 1 j = x at h
  cases h with
  | vq _ i => exact absurd (hf hx) (by omega)
  | vs _ i => exact absurd (hf hx) (by omega)
  | down _ _ h' => exact h'

/-! ## A window kept is of the fragment -/

theorem fine_winKept {Θ : Set (SeqAggFunc T)} {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (κ : Fin n → ColKind) (q : AggQueryIn T c n (ColKind.allReg n))
    (dist : Bool) (keep : Option (Selection T n)) (ht : t.noFun = true)
    (hf : if dist then f.distinct ∈ Θ else f ∈ Θ) (hkeep : Selection.noFunOpt keep = true)
    (hq : Fine Θ q) : Fine Θ (AggQueryIn.winKept P O o w t f κ q dist keep) := by
  refine ⟨AggQueryIn.usesOnly_winKept P O o w t f κ q dist keep mem_win mem_proj hq.1,
    AggQueryIn.inSig_winKept P O o w t f κ q dist keep ht hf hkeep hq.2.1, ?_,
    AggQueryIn.hygienic_winKept P O o w t f κ q dist keep hq.2.2.2⟩
  rw [AggQueryIn.winKept, winAllReg_castKind]
  refine ⟨rfl, ?_⟩
  rw [AggQueryIn.doubled, winAllReg_castKind]
  exact hq.2.2.1

theorem over_winKept {c n m p : ℕ} {sch : Schema} {A : String → Prop} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (κ : Fin n → ColKind) (q : AggQueryIn T c n (ColKind.allReg n))
    (dist : Bool) (keep : Option (Selection T n)) (hq : Over sch A q) :
    Over sch A (AggQueryIn.winKept P O o w t f κ q dist keep) :=
  ⟨AggQueryIn.overSchema_winKept P O o w t f κ q dist keep hq.1, fun x hx => by
    rw [AggQueryIn.names_winKept] at hx; exact hq.2 x hx⟩

/-! ## The values an apply's right side creates -/

/-- **A value of the right side of an apply, at a parameter row, is a
value of the row or of the right side's cut.** -/
theorem vals_applyRight (Θ : Set (SeqAggFunc T)) {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (g : ℕ → String) {k c n₂ : ℕ} {κ₂ : Fin n₂ → ColKind} (R : AggQueryIn T (k + c) n₂ κ₂)
    (hU : R.usesOnly basisProdOps) (hsrc : SymSrc Θ R) (hg : ∀ i, R.noMention (g i))
    (D : Database T) (γ : Fin c → T) (u : Tuple T k) (hset : R.SettlesAt D (Fin.append u γ))
    (v : Tuple T n₂) (hv : Multiset.Mem (R.evaluatePlain D (Fin.append u γ)) v) (i : Fin n₂) :
    (∃ j, u j = v i) ∨ v i ∈ valsU ((tabEnv cnt g R).CQ.evaluatePlain D γ) := by
  have hgood := (tabQ_correct Θ hc g R hU hsrc hg D γ u hset).2 v hv i
  rcases hgood with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · refine Or.inr ?_
    have hcore : ∀ i, (cutCore cnt (part (part g 1) 1) R).noMention (part (part g 1) 0 i) :=
      fun i => noMention_cutCore cnt _ _ R le_rfl (hg _)
    exact (mem_cutOf (part (part g 1) 0) R.allConsts (cutCore cnt (part (part g 1) 1) R) hcore D
      γ).1 _ h

/-! ## The pass -/

/-- The names a pass with supply `f` gives the values it creates: its
input's, and its supply's away from those binding around a pool. -/
def CrN (A : String → Prop) (f : ℕ → String) : String → Prop :=
  fun x => A x ∨ ∃ i, x = f i ∧ ¬ Enc f x

/-- A value of a row of `X`. -/
def InVals {m : ℕ} (X : Multiset (Tuple T m)) (a : T) : Prop :=
  ∃ u, Multiset.Mem X u ∧ ∃ j, u j = a

section Lift

variable {A B : String → Prop} {f : ℕ → String} {t : String}

theorem crN_part1 (hf : Function.Injective f) {x : String} (hx : CrN A (part f 1) x) :
    CrN A f x := by
  rcases hx with hx | ⟨i, rfl, hi⟩
  · exact Or.inl hx
  · exact Or.inr ⟨_, rfl, fun h => hi (enc_part1 hf h)⟩

theorem encB_part1 (hB : ∀ x, B x → ¬ Enc f x ∧ x ≠ t) :
    ∀ x, B x → ¬ Enc (part f 1) x ∧ x ≠ t :=
  fun x hx => ⟨fun h => (hB x hx).1 (Enc.down f x h), (hB x hx).2⟩

theorem supBt_part (j : ℕ) {x : String} (hx : Sup A (part f j) x ∨ B x ∨ x = t) :
    Sup A f x ∨ B x ∨ x = t := by
  rcases hx with hx | hx
  · exact Or.inl (sup_mono_slice _ hx)
  · exact Or.inr hx

end Lift

theorem fine_selReg {Θ : Set (SeqAggFunc T)} {c N : ℕ} {κ : Fin N → ColKind}
    {l : List (String × ℕ)} (φ : GenPredIn T c κ) (hφ : φ.noFun = true)
    {q : AggQueryIn T c N (ColKind.allReg N) l} (h : Fine Θ q) :
    Fine Θ (AggQueryIn.Sel φ.toReg q (SelOK.of_noAggAtom (GenPredIn.hasAggAtom_toReg φ))) :=
  ⟨⟨mem_sel, h.1⟩, ⟨GenPredIn.noFun_toReg hφ, h.2.1⟩, h.2.2.1, h.2.2.2⟩

theorem evaluatePlain_selReg {c N : ℕ} {κ : Fin N → ColKind} {l : List (String × ℕ)}
    (φ : GenPredIn T c κ) (q : AggQueryIn T c N (ColKind.allReg N) l) (D : Database T)
    (γ : Fin c → T) :
    (AggQueryIn.Sel φ.toReg q (SelOK.of_noAggAtom (GenPredIn.hasAggAtom_toReg φ))).evaluatePlain D γ
      = Multiset.filter (fun u => φ.holdsPlain u γ) (q.evaluatePlain D γ) := by
  simp only [AggQueryIn.evaluatePlain]
  exact Multiset.filter_congr (fun u _ => GenPredIn.holdsPlain_toReg φ u γ)

/-! ## The queries bounding created values -/

section CrPieces

variable {c : ℕ} {sch : Schema} {A : String → Prop} {Θ : Set (SeqAggFunc T)}

omit [ValueType T] in
theorem noMention_of_over {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    {q : AggQueryIn T c n κ l} {P : String → Prop} (h : Over sch P q) {x : String} (hx : ¬ P x) :
    q.noMention x :=
  AggQueryIn.noMention_of_not_mem_names q (fun hm => hx (h.2 x hm))

/-- The names of a slice-indexed part of the supply, away from slice 3,
are names a created-values query may carry beside a union of slice 3. -/
theorem crX3 {f : ℕ → String} (hf : SupOK sch A f) {P : ℕ → Prop}
    (hP : ∀ i, P i → i % 8 ≠ 4 ∧ i % 64 ≠ 8 ∧ i % 8 ≠ 1 ∧ i % 8 ≠ 3) :
    ∀ x, SupP A f P x → CrN A f x ∧ ∀ i, x ≠ part f 3 i := fun x hx => by
  rcases hx with hx | ⟨j, hj, rfl⟩
  · exact ⟨Or.inl hx, fun i h => hf.out _ (h ▸ hx)⟩
  · have := hP j hj
    refine ⟨Or.inr ⟨j, rfl, not_enc hf.inj ⟨this.1, this.2.1, this.2.2.1⟩⟩, fun i h => ?_⟩
    have := hf.inj h
    omega

theorem crX3_part1 {f : ℕ → String} (hf : SupOK sch A f) :
    ∀ x, CrN A (part f 1) x → CrN A f x ∧ ∀ i, x ≠ part f 3 i := fun x hx => by
  refine ⟨crN_part1 hf.inj hx, fun i h => ?_⟩
  rcases hx with hx | ⟨j, rfl, -⟩
  · exact hf.out _ (h ▸ hx)
  · have := hf.inj h
    omega

/-- **A union of created values**, over slice 3. -/
theorem over_crU2 {f : ℕ → String} (hf : SupOK sch A f) {B : String → Prop}
    {a b : AggQueryIn T c 1 (ColKind.allReg 1)} (ha : Over sch B a) (hb : Over sch B b)
    (hB : ∀ x, B x → CrN A f x ∧ ∀ i, x ≠ part f 3 i) : Over sch (CrN A f) (u2 (part f 3) a b) :=
  (over_u2 (part f 3) (B := fun x => CrN A f x ∧ ∀ i, x ≠ part f 3 i) (ha.mono hB) (hb.mono hB)
    ⟨(supOK_of_part hf 3).inj, (supOK_of_part hf 3).fresh, fun i h => h.2 i rfl⟩).mono
    fun x hx => by
      rcases hx with hx | ⟨i, rfl⟩
      · exact hx.1
      · exact Or.inr ⟨_, rfl, not_enc hf.inj (by omega)⟩

/-- **The constants and the context values a projection may emit.** -/
noncomputable def emitQ (f : ℕ → String) (S : Finset T) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  u2 (part f 5) (constsQ (part f 6) S) (ambQ (part f 7) c)

theorem over_emitQ {f : ℕ → String} (S : Finset T) (hf : SupOK sch A f) :
    Over sch (SupP A f (fun i => i % 8 = 5 ∨ i % 8 = 6 ∨ i % 8 = 7)) (emitQ (c := c) f S) := by
  have hA' : ∀ x, A x → SupP A f (fun i => i % 8 = 6 ∨ i % 8 = 7) x := fun x h => Or.inl h
  have hc6 := (over_constsQ (c := c) (part f 6) S (supOK_of_part hf 6)).mono
    (supP_part 6 (fun i => Or.inl (by omega)) hA')
  have ha7 := (over_ambQ (T := T) (c := c) (part f 7) (supOK_of_part hf 7)).mono
    (supP_part 7 (fun i => Or.inr (by omega)) hA')
  refine (over_u2 (part f 5) hc6 ha7 (supOK_part hf 5 fun i h => by omega)).mono fun x hx => ?_
  rcases hx with (hx | ⟨i, hi, rfl⟩) | ⟨i, rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨i, Or.inr hi, rfl⟩
  · exact Or.inr ⟨_, Or.inl (by omega), rfl⟩

theorem fine_emitQ (f : ℕ → String) (S : Finset T) : Fine Θ (emitQ (c := c) f S) := by
  have hamb : Fine Θ (ambQ (T := T) (part f 7) c) :=
    fine_unionFin _ c _ (fun _ _ => noMention_projQ _ _ (AggQueryIn.noMention_unitC _))
      (fun _ => fine_projQ _ fine_unitC)
  have hcs : Fine Θ (constsQ (c := c) (part f 6) S) :=
    fine_unionFin _ _ _ (fun _ _ => noMention_constQ _ _) (fun _ => fine_constQ _)
  exact fine_sumByMuX _ _ hcs hamb (noMention_constsQ _ S _) (noMention_constsQ _ S _)
    (noMention_ambQ _ _)

theorem settlesAt_emitQ (f : ℕ → String) (S : Finset T) (D : Database T) (γ : Fin c → T) :
    (emitQ f S).SettlesAt D γ := by
  have hamb : (ambQ (T := T) (part f 7) c).SettlesAt D γ :=
    settlesAt_unionFin D γ _ c _ (fun _ _ => noMention_projQ _ _ (AggQueryIn.noMention_unitC _))
      (fun _ => settlesAt_projQ _ _ D γ (AggQueryIn.settlesAt_unitC D γ))
  have hcs : (constsQ (c := c) (part f 6) S).SettlesAt D γ :=
    settlesAt_unionFin D γ _ _ _ (fun _ _ => noMention_constQ _ _) (fun _ => settlesAt_constQ D γ _)
  exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_constsQ _ S _) (noMention_ambQ _ _) D γ
    hcs hamb

theorem mem_valsU_emitQ (f : ℕ → String) (S : Finset T) (D : Database T) (γ : Fin c → T)
    (a : T) (ha : a ∈ S ∨ ∃ j, γ j = a) : a ∈ valsU ((emitQ f S).evaluatePlain D γ) := by
  rw [emitQ, valsU_u2 (part f 5) _ _ (noMention_constsQ _ S _) (noMention_ambQ _ _) D γ]
  rcases ha with ha | ⟨j, rfl⟩
  · exact Finset.mem_union_left _ (mem_valsU_constsQ _ S D γ a ha)
  · exact Finset.mem_union_right _ (mem_valsU_ambQ _ D γ j)

end CrPieces

/-! ## A projection re-typed -/

section ProjReg

variable {c N M : ℕ} {κ : Fin N → ColKind}

/-- A projection with its columns read as regular ones. -/
def projReg {l : List (String × ℕ)} (ps : Fin M → ProjColIn T c κ)
    (p : AggQueryIn T c N (ColKind.allReg N) l) : AggQueryIn T c M (ColKind.allReg M) l :=
  (AggQueryIn.Proj (fun j => (ps j).toReg) p).castKind (funext fun j => ProjColIn.kind_toReg (ps j))

theorem fine_projReg {Θ : Set (SeqAggFunc T)} {l : List (String × ℕ)}
    (ps : Fin M → ProjColIn T c κ) (hs : ∀ j, (ps j).sourceCol = true)
    (hn : ∀ j, (ps j).noFun = true) {p : AggQueryIn T c N (ColKind.allReg N) l} (h : Fine Θ p) :
    Fine Θ (projReg ps p) := by
  have := fine_proj (fun j => (ps j).toReg) (fun j => by cases ps j <;> rfl)
    (fun j => ProjColIn.noFun_toReg (hs j) (hn j)) h
  unfold Fine projReg at *
  rw [AggQueryIn.usesOnly_castKind, AggQueryIn.inSig_castKind, winAllReg_castKind,
    AggQueryIn.hygienic_castKind]
  exact this

theorem over_projReg {sch : Schema} {A : String → Prop} {l : List (String × ℕ)}
    (ps : Fin M → ProjColIn T c κ) {p : AggQueryIn T c N (ColKind.allReg N) l}
    (h : Over sch A p) : Over sch A (projReg ps p) := by
  unfold Over projReg
  rw [AggQueryIn.overSchema_castKind, AggQueryIn.names_castKind]
  exact h

theorem noMention_projReg {l : List (String × ℕ)} (ps : Fin M → ProjColIn T c κ)
    {p : AggQueryIn T c N (ColKind.allReg N) l} {t : String} (h : p.noMention t) :
    (projReg ps p).noMention t := by
  unfold projReg
  rw [AggQueryIn.noMention_castKind]
  exact h

theorem evaluatePlain_projReg {l : List (String × ℕ)} (ps : Fin M → ProjColIn T c κ)
    (hs : ∀ j, (ps j).sourceCol = true) (p : AggQueryIn T c N (ColKind.allReg N) l)
    (D : Database T) (γ : Fin c → T) :
    (projReg ps p).evaluatePlain D γ
      = Multiset.map (fun u => (fun j => (ps j).evalPlain u γ : Tuple T M))
          (p.evaluatePlain D γ) := by
  rw [projReg, AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain]
  refine Multiset.map_congr rfl (fun u _ => funext (fun j => ?_))
  exact ProjColIn.evalPlain_toReg (ps j) (hs j) u γ

theorem settlesAt_projReg {l : List (String × ℕ)} (ps : Fin M → ProjColIn T c κ)
    (p : AggQueryIn T c N (ColKind.allReg N) l) (D : Database T) (γ : Fin c → T)
    (h : p.SettlesAt D γ) : (projReg ps p).SettlesAt D γ := by
  rw [projReg, AggQueryIn.settlesAt_castKind]
  exact h

end ProjReg

/-! ## Names of slices -/

section SliceNames

variable {sch : Schema} {A B : String → Prop} {f : ℕ → String}

theorem sup_of_slice {g : ℕ → String} (hg : ∀ i, ∃ j, g i = f j) {x : String} (hx : Sup A g x) :
    Sup A f x := by
  rcases hx with hx | ⟨i, rfl⟩
  · exact Or.inl hx
  · obtain ⟨j, hj⟩ := hg i
    exact Or.inr ⟨j, hj⟩

/-- A name of one slice is no name of another. -/
theorem not_sup_part (hf : SupOK sch A f) {j j' : ℕ} (hjj : j ≠ j') (hj : j < 8) (hj' : j' < 8)
    (i : ℕ) : ¬ Sup A (part f j) (part f j' i) := by
  rintro (h | ⟨i', h⟩)
  · exact hf.out _ h
  · have := hf.inj h
    omega

theorem not_crN_part (hf : SupOK sch A f) {j : ℕ} (hj : j ≠ 1) (hj' : j < 8) (i : ℕ) :
    ¬ CrN A (part f 1) (part f j i) := by
  rintro (h | ⟨i', h, -⟩)
  · exact hf.out _ h
  · have := hf.inj h
    omega

theorem enc_range {g : ℕ → String} {x : String} (h : Enc g x) : ∃ i, x = g i := by
  obtain ⟨i, hi, -⟩ := enc_index h
  exact ⟨i, hi⟩

end SliceNames

/-- **The pass**, both halves at once. A closed query of
`{∅, Π, σ, apply, γ, win, μ^⊎}` is matched by a query of the fragment
with products and without the apply, defined and equal wherever it is.
A recursive term reading the name `s` is matched, given a closed pool `W`
holding the values of the round, by a term reading a name `t` in its
place; and the values it creates are bounded by a closed query `Cr`,
built before the pool is known. -/
theorem exists_prodPass_aux {Θ : Set (SeqAggFunc T)} {cnt : SeqAggFunc T} (hcnt : cnt ∈ Θ)
    (hc : SeqAggFunc.Counts cnt) (hRC : ∀ g ∈ Θ, g.ReadsCount) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly basisRecOps → q.inSig Θ → q.hygienic →
      ∀ (sch : Schema) (A : String → Prop) (f : ℕ → String), SupOK sch A f → RelsIn sch A q →
      (l = [] → ∃ q' : AggQueryIn T c n (ColKind.allReg n), Fine Θ q' ∧ Over sch (Sup A f) q' ∧
          ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
            q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ)
      ∧ (∀ (s : String) (m : ℕ), l = [(s, m)] → q.noMention s →
          ∃ Cr : AggQueryIn T c 1 (ColKind.allReg 1), Fine Θ Cr ∧ Over sch (CrN A f) Cr ∧
            (∀ (D : Database T) (γ : Fin c → T), Cr.SettlesAt D γ) ∧
            (∀ (D : Database T) (γ : Fin c → T) (X : Relation T m),
              q.SettlesAt (D.assign s X) γ →
              ∀ v, Multiset.Mem (q.evaluatePlain (D.assign s X) γ) v → ∀ i,
                InVals X (v i) ∨ v i ∈ valsU (Cr.evaluatePlain D γ)) ∧
            ∀ (t : String) (B : String → Prop) (W : AggQueryIn T c 1 (ColKind.allReg 1)),
              sch t = some m → ¬ A t → (∀ x, B x → ¬ Enc f x ∧ x ≠ t) → Over sch B W →
              Fine Θ W →
              ∃ q' : AggQueryIn T c n (ColKind.allReg n) [(t, m)], Fine Θ q' ∧
                Over sch (fun x => Sup A f x ∨ B x ∨ x = t) q' ∧ q'.noMention t ∧
                ∀ (D : Database T) (γ : Fin c → T) (X : Relation T m),
                  q.SettlesAt (D.assign s X) γ → W.SettlesAt D γ →
                  (∀ u, Multiset.Mem X u → ∀ i, u i ∈ valsU (W.evaluatePlain D γ)) →
                  q'.SettlesAt (D.assign t X) γ
                    ∧ q.evaluatePlain (D.assign s X) γ = q'.evaluatePlain (D.assign t X) γ) := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro hu hi hr sch A f hf hrel
    exact ⟨fun _ => ⟨AggQueryIn.Rel n s', fine_rel n s',
      (over_rel n s' hrel.1 (Or.inl hrel.2)), fun D γ _ => ⟨trivial, rfl⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Hole n s' κh =>
    intro hu hi hr sch A f hf hrel
    refine ⟨fun hl => absurd hl (by simp), fun s m hl _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
    refine ⟨AggQueryIn.emptyRel 1, fine_emptyRel 1, over_emptyRel 1,
      fun D γ => AggQueryIn.settlesAt_emptyRel 1 D γ, fun D γ X _ v hv i => ?_,
      fun t B W ht _ _ _ _ => ⟨AggQueryIn.Hole n t (ColKind.allReg n), fine_hole n t,
        over_hole n t ht (Or.inr (Or.inr rfl)), trivial, fun D γ X _ _ _ => ⟨trivial, ?_⟩⟩⟩
    · rw [evaluatePlain_hole_assign] at hv
      exact Or.inl ⟨v, hv, i, rfl⟩
    · rw [evaluatePlain_hole_assign, evaluatePlain_hole_assign]
  | Param pv ρ =>
    intro hu hi hr sch A f hf hrel
    exact ⟨fun _ => ⟨AggQueryIn.Param pv (ColKind.allReg _), fine_param pv, over_param pv,
      fun D γ _ => ⟨trivial, rfl⟩⟩, fun _ _ hl _ => absurd hl (by simp)⟩
  | Empty =>
    intro hu hi hr sch A f hf hrel
    exact ⟨fun _ => ⟨AggQueryIn.Empty, ⟨mem_empty, trivial, trivial, trivial⟩,
      ⟨trivial, fun x hx => absurd hx (Finset.notMem_empty x)⟩, fun D γ _ => ⟨trivial, rfl⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | @Proj c' N' M' κ' l' ps q ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨hc', hb'⟩ := ih hu.2 hi.2 hr sch A (part f 1) (supOK_of_part hf 1) hrel
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hF, hO, he⟩ := hc' hl
      refine ⟨_, fine_projReg ps hu.1.2 hi.1 hF,
        (over_projReg ps hO).mono fun x hx => sup_mono_slice _ hx, fun D γ hset => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨settlesAt_projReg ps q' D γ hs', ?_⟩
      rw [evaluatePlain_projReg ps hu.1.2, ← he']
      rfl
    obtain ⟨Cr₁, hF, hO, hS, hV, hbody⟩ := hb' s m hl hnm
    have hP : ∀ i, (fun i => i % 8 = 5 ∨ i % 8 = 6 ∨ i % 8 = 7) i →
        i % 8 ≠ 4 ∧ i % 64 ≠ 8 ∧ i % 8 ≠ 1 ∧ i % 8 ≠ 3 := fun i hi => by
      simp only at hi; omega
    have hE := over_emitQ (c := c') (Finset.univ.biUnion fun j => (ps j).consts) hf
    have hn₁ : ∀ i, Cr₁.noMention (part f 3 i) :=
      fun i => noMention_of_over hO fun h => (crX3_part1 hf _ h).2 i rfl
    have hnE : ∀ i, (emitQ (c := c') f (Finset.univ.biUnion fun j => (ps j).consts)).noMention
        (part f 3 i) := fun i => noMention_of_over hE fun h => (crX3 hf hP _ h).2 i rfl
    refine ⟨u2 (part f 3) Cr₁ (emitQ f (Finset.univ.biUnion fun j => (ps j).consts)),
      fine_sumByMuX _ _ hF (fine_emitQ _ _) (hn₁ 0) (hn₁ 1) (hnE 1),
      over_crU2 hf (hO.mono fun x hx => Or.inl hx) (hE.mono fun x hx => Or.inr hx) (fun x hx => by
        rcases hx with hx | hx
        · exact crX3_part1 hf x hx
        · exact crX3 hf hP x hx),
      fun D γ => AggQueryIn.settlesAt_sumByMuX _ _ _ _ (hn₁ 0) (hnE 1) D γ (hS D γ)
        (settlesAt_emitQ _ _ D γ), fun D γ X hset v hv i => ?_, ?_⟩
    · obtain ⟨u, hu', rfl⟩ := Multiset.mem_map.mp hv
      rw [valsU_u2 (part f 3) _ _ (hn₁ 0) (hnE 1) D γ]
      have hmem := ProjColIn.evalPlain_mem_of_noFun (ps i) (hi.1 i)
        (V := Union.union (Finset.univ.image u) (Union.union (Finset.univ.image γ) (ps i).consts))
        (ProjColIn.constsIn_of_subset _ (fun a ha => Finset.mem_union_right _
          (Finset.mem_union_right _ ha))) u
        (fun j => Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ j))) γ
        (fun j => Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem γ (Finset.mem_univ j))))
      rcases Finset.mem_union.mp hmem with h | h
      · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
        show InVals X ((ps i).evalPlain u γ) ∨ (ps i).evalPlain u γ ∈ _
        rw [← hj]
        rcases hV D γ X hset u hu' j with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Finset.mem_union_left _ h')
      · refine Or.inr (Finset.mem_union_right _ (mem_valsU_emitQ _ _ D γ _ ?_))
        rcases Finset.mem_union.mp h with h | h
        · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
          exact Or.inr ⟨j, hj⟩
        · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩)
    · intro t B W ht hAt hB hW hFW
      obtain ⟨q', hF', hO', hn', he⟩ := hbody t B W ht hAt (encB_part1 hB) hW hFW
      refine ⟨projReg ps q', fine_projReg ps hu.1.2 hi.1 hF',
        (over_projReg ps hO').mono fun x hx => supBt_part 1 hx, noMention_projReg ps hn',
        fun D γ X hset hWs hX => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ X hset hWs hX
      refine ⟨settlesAt_projReg ps q' _ γ hs', ?_⟩
      rw [evaluatePlain_projReg ps hu.1.2, ← he']
      rfl
  | Sel φ q hφ ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨hc', hb'⟩ := ih hu.2 hi.2 hr sch A (part f 1) (supOK_of_part hf 1) hrel
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hF, hO, he⟩ := hc' hl
      refine ⟨_, fine_selReg φ hi.1 hF, (over_sel _ _ hO).mono fun x hx => sup_mono_slice _ hx,
        fun D γ hset => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨hs', ?_⟩
      rw [evaluatePlain_selReg, ← he']
      rfl
    · obtain ⟨Cr, hF, hO, hS, hV, hbody⟩ := hb' s m hl hnm
      refine ⟨Cr, hF, hO.mono fun x hx => crN_part1 hf.inj hx, hS,
        fun D γ X hset v hv => hV D γ X hset v (Multiset.mem_of_mem_filter hv), ?_⟩
      intro t B W ht hAt hB hW hFW
      obtain ⟨q', hF', hO', hn', he⟩ := hbody t B W ht hAt (encB_part1 hB) hW hFW
      refine ⟨_, fine_selReg φ hi.1 hF', (over_sel _ _ hO').mono fun x hx => supBt_part 1 hx, hn',
        fun D γ X hset hWs hX => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ X hset hWs hX
      refine ⟨hs', ?_⟩
      rw [evaluatePlain_selReg, ← he']
      rfl
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hu => absurd hu.1 (by simp [basisRecOps, AggQueryIn.sumMuOps])
  | @Apply c' n₁ n₂ κ₁ κ₂ l' q₁ q₂ ih₁ ih₂ =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨hc₁, hb₁⟩ := ih₁ hu.2.1 hi.1 hr.1 sch A (part f 1) (supOK_of_part hf 1) hrel.1
    obtain ⟨hc₂, -⟩ := ih₂ hu.2.2 hi.2 hr.2 sch A (part f 2) (supOK_of_part hf 2) hrel.2
    obtain ⟨R', hFR, hOR, heR⟩ := hc₂ rfl
    -- the right side's names: slice 2
    have hP2 : SupOK sch (SupP A f (fun i => i % 8 = 2)) (part f 0) :=
      supOK_part hf 0 fun i h => by omega
    have hOR' : Over sch (SupP A f (fun i => i % 8 = 2)) R' :=
      hOR.mono (supP_part 2 (fun i => by omega) fun x h => Or.inl h)
    have hrR : RelsIn sch (SupP A f (fun i => i % 8 = 2)) R' :=
      relsIn_of_overSchema R' hOR'.1 hFR.2.2.2 hOR'.2
    have hfR : ∀ i, R'.noMention (part f 0 i) := fun i => noMention_of_over hOR' (hP2.out i)
    have hsrc : SymSrc Θ R' := ⟨hFR.2.1, hRC, hFR.2.2.1, hFR.2.2.2⟩
    -- the apply's value on a left side matching the source's
    have hval : ∀ (D' : Database T) (γ : Fin c' → T) {l'' : List (String × ℕ)}
        (L' : AggQueryIn T c' n₁ (ColKind.allReg n₁) l'')
        (VQ : AggQueryIn T c' 1 (ColKind.allReg 1)),
        VQ.noMention (part (part f 0) 1 0) →
        (∀ u, Multiset.Mem (L'.evaluatePlain D' γ) u → R'.SettlesAt D' (Fin.append u γ)) →
        (∀ u, Multiset.Mem (L'.evaluatePlain D' γ) u → ∀ i, u i ∈ valsU (VQ.evaluatePlain D' γ)) →
        ((applyX cnt (part f 0) L' R' VQ).evaluatePlain D' γ : Multiset (Tuple T (n₁ + n₂)))
          = (L'.evaluatePlain D' γ : Multiset (Tuple T n₁)).bind (fun u =>
              (R'.evaluatePlain D' (Fin.append u γ) : Multiset (Tuple T n₂)).map
                (fun v => (Fin.append u v : Tuple T (n₁ + n₂)))) :=
      fun D' γ _ L' VQ hV hs hv =>
          evaluatePlain_applyX Θ hc (part f 0) L' R' VQ hFR.1 hsrc hfR hV D'
        γ hs hv
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨L', hFL, hOL, heL⟩ := hc₁ hl
      have hL4 : ∀ i, L'.noMention (part f 4 i) :=
        fun i => noMention_of_over hOL (not_sup_part hf (by omega) (by omega) (by omega) i)
      have hOV := over_valsOf (part f 4) (hf.slice_out (fun i => 8 * i + 1) (fun i => 8 * i + 4)
        (fun _ _ => by omega) (fun _ _ h => by simp only at h; omega)) hOL
      have hV1 : ∀ i, (valsOf (part f 4) L').noMention (part (part f 0) 1 i) := fun i =>
        noMention_of_over hOV (by
          rintro ((h | ⟨i', h⟩) | ⟨i', h⟩)
          · exact hf.out _ h
          all_goals (have := hf.inj h; omega))
      refine ⟨applyX cnt (part f 0) L' R' (valsOf (part f 4) L'),
        fine_applyX hcnt (part f 0) hFL hFR.2.1 (fine_valsOf _ hL4 hFL) hfR ⟨hV1 0, hV1 1⟩,
        (over_applyX cnt (part f 0) hP2 hOL hrR hOV (fun i h => ?_)).mono fun x hx => ?_,
        fun D γ hset => ?_⟩
      · rcases h with (h | ⟨i', h⟩) | ⟨i', h⟩
        · exact hf.out _ h
        all_goals (have := hf.inj h; omega)
      · rcases hx with ((hx | ⟨i, -, rfl⟩) | ⟨i, rfl⟩) | (hx | ⟨i, rfl⟩)
          | ((hx | ⟨i, rfl⟩) | ⟨i, rfl⟩)
        all_goals first | exact Or.inl hx | exact Or.inr ⟨_, rfl⟩
      obtain ⟨hsL, heL'⟩ := heL D γ hset.1
      have hRs : ∀ u, Multiset.Mem (L'.evaluatePlain D γ) u →
          R'.SettlesAt D (Fin.append u γ) ∧ q₂.evaluatePlain D (Fin.append u γ)
            = R'.evaluatePlain D (Fin.append u γ) := fun u hu =>
        heR D _ (hset.2 u (by rw [heL']; exact hu))
      refine ⟨settlesAt_applyX hc (part f 0) L' R' _ hfR (hV1 0) D γ hsL
        (settlesAt_valsOf D γ _ L' hL4 hsL), ?_⟩
      rw [hval D γ L' _ (hV1 0) (fun u hu => (hRs u hu).1)
        (fun u hu i => (mem_valsU_valsOf _ L' hL4 D γ _).mpr ⟨u, hu, i, rfl⟩)]
      simp only [AggQueryIn.evaluatePlain]
      rw [heL']
      exact Multiset.bind_congr fun u hu => by rw [(hRs u hu).2]
    -- a recursive left side
    obtain ⟨Cr₁, hF₁, hO₁, hS₁, hV₁, hbody₁⟩ := hb₁ s m hl hnm.1
    have hfR0 : ∀ i, R'.noMention (part (part f 0) 0 i) := fun i => hfR _
    have henvO := envOver_tabEnv cnt (part (part f 0) 0) R' (supOK_of_part hP2 0) hrR
    have henvF := envFine_tabEnv hcnt (part (part f 0) 0) R' hFR.2.1 hfR0
    have henvS := envSettles_tabEnv hc (part (part f 0) 0) R' hfR0
    have hPC : ∀ i, (fun i => i % 8 = 2 ∨ i % 64 = 0) i →
        i % 8 ≠ 4 ∧ i % 64 ≠ 8 ∧ i % 8 ≠ 1 ∧ i % 8 ≠ 3 := fun i hi => by simp only at hi; omega
    have hCQ : Over sch (SupP A f (fun i => i % 8 = 2 ∨ i % 64 = 0))
        (tabEnv cnt (part (part f 0) 0) R').CQ := henvO.cq.mono fun x hx => by
      rcases hx with (hx | ⟨i, hi, rfl⟩) | ⟨i, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, Or.inl hi, rfl⟩
      · exact Or.inr ⟨_, Or.inr (by omega), rfl⟩
    have hn₁ : ∀ i, Cr₁.noMention (part f 3 i) :=
      fun i => noMention_of_over hO₁ fun h => (crX3_part1 hf _ h).2 i rfl
    have hnC : ∀ i, (tabEnv cnt (part (part f 0) 0) R').CQ.noMention (part f 3 i) :=
      fun i => noMention_of_over hCQ fun h => (crX3 hf hPC _ h).2 i rfl
    refine ⟨u2 (part f 3) Cr₁ (tabEnv cnt (part (part f 0) 0) R').CQ,
      fine_sumByMuX _ _ hF₁ henvF.cq (hn₁ 0) (hn₁ 1) (hnC 1),
      over_crU2 hf (hO₁.mono fun x hx => Or.inl hx) (hCQ.mono fun x hx => Or.inr hx)
        (fun x hx => by
          rcases hx with hx | hx
          · exact crX3_part1 hf x hx
          · exact crX3 hf hPC x hx),
      fun D γ => AggQueryIn.settlesAt_sumByMuX _ _ _ _ (hn₁ 0) (hnC 1) D γ (hS₁ D γ)
        (henvS.cq D γ), fun D γ X hset v hv i => ?_, ?_⟩
    · rw [valsU_u2 (part f 3) _ _ (hn₁ 0) (hnC 1) D γ]
      obtain ⟨u, hu, hvu⟩ := Multiset.mem_bind.mp hv
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hvu
      have hleft : ∀ j, InVals X (u j) ∨ u j ∈ Union.union (valsU (Cr₁.evaluatePlain D γ))
          (valsU ((tabEnv cnt (part (part f 0) 0) R').CQ.evaluatePlain D γ)) := fun j => by
        rcases hV₁ D γ X hset.1 u hu j with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_union_left _ h)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact hleft j
      · rw [Fin.append_right]
        have hs2 := AggQueryIn.settlesAt_assign_of_noMention X q₂ hnm.2 D _ (hset.2 u hu)
        rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hnm.2, (heR D _ hs2).2] at hw
        rcases vals_applyRight Θ hc (part (part f 0) 0) R' hFR.1 hsrc hfR0 D γ u (heR D _ hs2).1
          w hw j with ⟨j', hj'⟩ | h
        · rw [← hj']
          exact hleft j'
        · exact Or.inr (Finset.mem_union_right _ h)
    intro t B W ht hAt hB hW hFW
    obtain ⟨L'', hFL, hOL, hnL, heL⟩ := hbody₁ t B W ht hAt (encB_part1 hB) hW hFW
    have hW4 : ∀ i, W.noMention (part f 4 i) :=
      fun i => noMention_of_over hW fun h => (hB _ h).1 (Enc.vq f i)
    have hC4 : ∀ i, Cr₁.noMention (part f 4 i) :=
      fun i => noMention_of_over hO₁ (not_crN_part hf (by omega) (by omega) i)
    have hOV := over_u2 (part f 4) (B := fun x => B x ∨ CrN A (part f 1) x)
      (hW.mono fun x hx => Or.inl hx) (hO₁.mono fun x hx => Or.inr hx)
      ⟨(supOK_of_part hf 4).inj, (supOK_of_part hf 4).fresh, fun i h => by
        rcases h with h | h
        · exact (hB _ h).1 (Enc.vq f i)
        · exact not_crN_part hf (by omega) (by omega) i h⟩
    have hAV : ∀ i, ¬ Sup (fun x => B x ∨ CrN A (part f 1) x) (part f 4) (part (part f 0) 1 i) := by
      rintro i ((h | h) | ⟨i', h⟩)
      · exact (hB _ h).1 (Enc.vs f i)
      · exact not_crN_part hf (j := 0) (by omega) (by omega) (8 * i + 1) h
      · have := hf.inj h
        omega
    have hfV : (u2 (part f 4) W Cr₁).noMention (part (part f 0) 1 0)
        ∧ (u2 (part f 4) W Cr₁).noMention (part (part f 0) 1 1) :=
      ⟨noMention_of_over hOV (hAV 0), noMention_of_over hOV (hAV 1)⟩
    have hft : ∀ i, f i ≠ t := fun i h => by
      have := hf.fresh i
      rw [h, ht] at this
      cases this
    have hRt : R'.noMention t := noMention_of_over hOR' (by
      rintro (h | ⟨i, -, h⟩)
      · exact hAt h
      · exact hft i h.symm)
    have hVt : (u2 (part f 4) W Cr₁).noMention t := noMention_of_over hOV (by
      rintro ((h | (h | ⟨i, h, -⟩)) | ⟨i, h⟩)
      · exact (hB _ h).2 rfl
      · exact hAt h
      · exact hft _ h.symm
      · exact hft _ h.symm)
    refine ⟨applyX cnt (part f 0) L'' R' (u2 (part f 4) W Cr₁),
      fine_applyX hcnt (part f 0) hFL hFR.2.1 (fine_sumByMuX _ _ hFW hF₁ (hW4 0) (hW4 1) (hC4 1))
        hfR hfV,
      (over_applyX cnt (part f 0) hP2 hOL hrR hOV hAV).mono fun x hx => ?_,
      noMention_applyX cnt (part f 0) hnL hRt hVt, fun D γ X hset hWs hX => ?_⟩
    · rcases hx with ((hx | ⟨i, -, rfl⟩) | ⟨i, rfl⟩) | ((hx | ⟨i, rfl⟩) | hx | hx) |
        ((hx | (hx | ⟨i, rfl, -⟩)) | ⟨i, rfl⟩)
      all_goals first
        | exact Or.inl (Or.inl hx)
        | exact Or.inl (Or.inr ⟨_, rfl⟩)
        | exact Or.inr (Or.inl hx)
        | exact Or.inr (Or.inr hx)
    obtain ⟨hsL, heL'⟩ := heL D γ X hset.1 hWs hX
    have hRs : ∀ u, Multiset.Mem (L''.evaluatePlain (D.assign t X) γ) u →
        R'.SettlesAt (D.assign t X) (Fin.append u γ)
          ∧ q₂.evaluatePlain (D.assign s X) (Fin.append u γ)
            = R'.evaluatePlain (D.assign t X) (Fin.append u γ) := fun u hu => by
      rw [← heL'] at hu
      have hs2 := AggQueryIn.settlesAt_assign_of_noMention X q₂ hnm.2 D _ (hset.2 u hu)
      refine ⟨settlesAt_assign_of_noMention' X R' hRt D _ (heR D _ hs2).1, ?_⟩
      rw [AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hnm.2,
        AggQueryIn.evaluatePlain_assign_of_noMention X R' hRt, (heR D _ hs2).2]
    have hVs : (u2 (part f 4) W Cr₁).SettlesAt D γ :=
      AggQueryIn.settlesAt_sumByMuX _ _ _ _ (hW4 0) (hC4 1) D γ hWs (hS₁ D γ)
    have hvalV : ∀ u, Multiset.Mem (L''.evaluatePlain (D.assign t X) γ) u → ∀ i,
        u i ∈ valsU ((u2 (part f 4) W Cr₁).evaluatePlain (D.assign t X) γ) := fun u hu i => by
      rw [← heL'] at hu
      rw [AggQueryIn.evaluatePlain_assign_of_noMention X _ hVt,
        valsU_u2 (part f 4) _ _ (hW4 0) (hC4 1) D γ]
      rcases hV₁ D γ X hset.1 u hu i with ⟨u', hu', j, hj⟩ | h
      · exact Finset.mem_union_left _ (hj ▸ hX u' hu' j)
      · exact Finset.mem_union_right _ h
    refine ⟨settlesAt_applyX hc (part f 0) L'' R' _ hfR hfV.1 _ γ hsL
      (settlesAt_assign_of_noMention' X _ hVt D γ hVs), ?_⟩
    rw [hval _ γ L'' _ hfV.1 (fun u hu => (hRs u hu).1) hvalV]
    simp only [AggQueryIn.evaluatePlain]
    rw [heL']
    exact Multiset.bind_congr fun u hu => by rw [(hRs u hu).2]
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hu => absurd hu.1 (by simp [basisRecOps, AggQueryIn.sumMuOps])
  | Dedup q ih => exact fun hu => absurd hu.1 (by simp [basisRecOps, AggQueryIn.sumMuOps])
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hu => absurd hu.1 (by simp [basisRecOps, AggQueryIn.sumMuOps])
  | Explode k hk q ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨hc', hb'⟩ := ih hu hi hr sch A (part f 1) (supOK_of_part hf 1) hrel
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hF, hO, he⟩ := hc' hl
      exact ⟨q', hF, hO.mono fun x hx => sup_mono_slice _ hx, he⟩
    · obtain ⟨Cr, hF, hO, hS, hV, hbody⟩ := hb' s m hl hnm
      refine ⟨Cr, hF, hO.mono fun x hx => crN_part1 hf.inj hx, hS, hV, ?_⟩
      intro t B W ht hAt hB hW hFW
      obtain ⟨q', hF', hO', hn', he⟩ := hbody t B W ht hAt (encB_part1 hB) hW hFW
      exact ⟨q', hF', hO'.mono fun x hx => supBt_part 1 hx, hn', he⟩
  | Retag hk q ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨hc', hb'⟩ := ih hu hi hr sch A (part f 1) (supOK_of_part hf 1) hrel
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hF, hO, he⟩ := hc' hl
      exact ⟨q', hF, hO.mono fun x hx => sup_mono_slice _ hx, he⟩
    · obtain ⟨Cr, hF, hO, hS, hV, hbody⟩ := hb' s m hl hnm
      refine ⟨Cr, hF, hO.mono fun x hx => crN_part1 hf.inj hx, hS, hV, ?_⟩
      intro t B W ht hAt hB hW hFW
      obtain ⟨q', hF', hO', hn', he⟩ := hbody t B W ht hAt (encB_part1 hB) hW hFW
      exact ⟨q', hF', hO'.mono fun x hx => supBt_part 1 hx, hn', he⟩
  | @Mu c' n' κ' s q₀ q₁ ih₀ ih₁ =>
    intro hu hi hr sch A f hf hrel
    refine ⟨fun _ => ?_, fun _ _ hl _ => absurd hl (by simp)⟩
    have hA0 : ¬ A (f 0) := hf.out 0
    obtain ⟨q₀', hF₀, hO₀, he₀⟩ :=
      (ih₀ hu.2.1 hi.1 hr.2.2.1 sch A (part f 1) (supOK_of_part hf 1) hrel.1).1 rfl
    have hne : ∀ j i, j ≠ 0 → j < 8 → f 0 ≠ part f j i := fun j i hj hj' h => by
      have := hf.inj h
      omega
    have hf2' : SupOK (sch.update (f 0) n') A (part f 2) :=
      ⟨(supOK_of_part hf 2).inj, AggQueryIn.update_fresh (supOK_of_part hf 2).fresh
        (fun i => hne 2 i (by omega) (by omega)), (supOK_of_part hf 2).out⟩
    have hrel₁ : RelsIn (sch.update (f 0) n') A q₁ :=
      (relsIn_update q₁ (noMention_of_relsIn hA0 q₁ hrel.2)).mpr hrel.2
    obtain ⟨Cr₁, hFC, hOC, hSC, hVC, hbody⟩ :=
      (ih₁ hu.2.2 hi.2 hr.2.2.2 _ A (part f 2) hf2' hrel₁).2 s n' rfl hr.2.1
    -- the pool: the base's values and the body's created ones
    have h04 : ∀ i, q₀'.noMention (part f 4 i) :=
      fun i => noMention_of_over hO₀ (not_sup_part hf (by omega) (by omega) (by omega) i)
    have hOV := over_valsOf (part f 4) (hf.slice_out (fun i => 8 * i + 1) (fun i => 8 * i + 4)
      (fun _ _ => by omega) (fun _ _ h => by simp only at h; omega)) hO₀
    have hB' : SupOK (sch.update (f 0) n')
        (fun x => Sup (Sup A (part f 1)) (part f 4) x ∨ CrN A (part f 2) x) (part f 3) :=
      ⟨(supOK_of_part hf 3).inj, AggQueryIn.update_fresh (supOK_of_part hf 3).fresh
        (fun i => hne 3 i (by omega) (by omega)), fun i h => by
          rcases h with ((h | ⟨i', h⟩) | ⟨i', h⟩) | (h | ⟨i', h, -⟩)
          all_goals first | exact hf.out _ h | (have := hf.inj h; omega)⟩
    have hv3 : ∀ i, (valsOf (part f 4) q₀').noMention (part f 3 i) :=
      fun i => noMention_of_over hOV fun h => hB'.out i (Or.inl h)
    have hc3 : ∀ i, Cr₁.noMention (part f 3 i) :=
      fun i => noMention_of_over hOC fun h => hB'.out i (Or.inr h)
    have hOW := over_u2 (part f 3) ((hOV.update (by
        rintro ((h | ⟨i', h⟩) | ⟨i', h⟩)
        · exact hA0 h
        · exact hne 1 i' (by omega) (by omega) h
        · exact hne 4 i' (by omega) (by omega) h) n').mono fun x hx => Or.inl hx)
      (hOC.mono fun x hx => Or.inr hx) hB'
    have hFW : Fine Θ (u2 (part f 3) (valsOf (part f 4) q₀') Cr₁) :=
      fine_sumByMuX _ _ (fine_valsOf _ h04 hF₀) hFC (hv3 0) (hv3 1) (hc3 1)
    have hBenc : ∀ x, Sup (fun x => Sup (Sup A (part f 1)) (part f 4) x ∨ CrN A (part f 2) x)
        (part f 3) x → ¬ Enc (part f 2) x ∧ x ≠ f 0 := by
      have hAc : ∀ x, A x → ¬ Enc (part f 2) x ∧ x ≠ f 0 := fun x h => ⟨fun he => by
          obtain ⟨j, rfl⟩ := enc_range he
          exact hf.out _ h, fun he => hA0 (he ▸ h)⟩
      intro x hx
      rcases hx with (((h | ⟨i, rfl⟩) | ⟨i, rfl⟩) | (h | ⟨i, rfl, hi⟩)) | ⟨i, rfl⟩
      all_goals first
        | exact hAc _ h
        | exact ⟨hi, fun he => hne 2 i (by omega) (by omega) he.symm⟩
        | exact ⟨fun he => by
            obtain ⟨j, hj⟩ := enc_range he
            have := hf.inj hj
            omega, fun he => by
            have := hf.inj he
            omega⟩
    obtain ⟨q₁', hF₁, hO₁, hn₁, he₁⟩ := hbody (f 0) _ _
      (AggQueryIn.Schema.update_self sch (f 0) n') hA0 hBenc hOW hFW
    have h0t : q₀'.noMention (f 0) := noMention_of_over hO₀ (by
      rintro (h | ⟨i, h⟩)
      · exact hA0 h
      · exact hne 1 i (by omega) (by omega) h)
    refine ⟨AggQueryIn.Mu (f 0) q₀' q₁',
      ⟨⟨mem_muBag, hF₀.1, hF₁.1⟩, ⟨hF₀.2.1, hF₁.2.1⟩, ⟨hF₀.2.2.1, hF₁.2.2.1⟩,
        ⟨h0t, hn₁, hF₀.2.2.2, hF₁.2.2.2⟩⟩,
      ⟨⟨hf.fresh 0, hO₀.1, hn₁, hO₁.1⟩, fun x hx => ?_⟩, fun D γ hset => ?_⟩
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr ⟨0, rfl⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · exact sup_mono_slice _ (hO₀.2 x hx)
      rcases hO₁.2 x hx with (h | ⟨i, rfl⟩) | ((((h | ⟨i, rfl⟩) | ⟨i, rfl⟩) | (h | ⟨i, rfl, -⟩)) |
        ⟨i, rfl⟩) | rfl
      all_goals first | exact Or.inl h | exact Or.inr ⟨_, rfl⟩
    -- the rounds hold values of the pool
    have hs₀ := he₀ D γ hset.1
    have hWs : (u2 (part f 3) (valsOf (part f 4) q₀') Cr₁).SettlesAt D γ :=
      AggQueryIn.settlesAt_sumByMuX _ _ _ _ (hv3 0) (hc3 1) D γ
        (settlesAt_valsOf D γ _ q₀' h04 hs₀.1) (hSC D γ)
    have hWv := valsU_u2 (part f 3) _ _ (hv3 0) (hc3 1) D γ
    refine mu_rename s (f 0) q₀ q₀' q₁ q₁' D γ hset hs₀
      (fun X => ∀ u, Multiset.Mem X u → ∀ i,
        u i ∈ valsU ((u2 (part f 3) (valsOf (part f 4) q₀') Cr₁).evaluatePlain D γ))
      (fun u hu i => ?_) (fun u hu => absurd hu (Multiset.notMem_zero u)) (fun X hX hs1 => ?_)
    · rw [hWv]
      refine Finset.mem_union_left _ ((mem_valsU_valsOf _ q₀' h04 D γ _).mpr ⟨u, ?_, i, rfl⟩)
      rw [← hs₀.2]
      exact hu
    obtain ⟨hs', he'⟩ := he₁ D γ X hs1 hWs hX
    refine ⟨hs', he', fun v hv i => ?_⟩
    rcases hVC D γ X hs1 v hv i with ⟨u, hu, j, hj⟩ | h
    · exact hj ▸ hX u hu j
    · rw [hWv]
      exact Finset.mem_union_right _ h
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun hu => absurd hu.1 (by simp [basisRecOps, AggQueryIn.sumMuOps])
  | Gamma is ts fs q keep ord ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨q', hF, hO, he⟩ := (ih hu.2 hi.2.2.2 hr sch A f hf hrel).1 rfl
    refine ⟨fun _ => ⟨(AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) is ts fs q' keep
        ord).allRegOf, ?_, over_allRegOf hO, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · unfold Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_gamma, hF.1⟩, ⟨hi.1, hi.2.1, hi.2.2.1, hF.2.1⟩, hF.2.2.1, hF.2.2.2⟩
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
  | GammaScalar ts fs q ord ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨q', hF, hO, he⟩ := (ih hu.2 hi.2.2 hr sch A f hf hrel).1 rfl
    refine ⟨fun _ => ⟨(AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q'
        ord).allRegOf, ?_, over_allRegOf hO, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · unfold Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_gamma, hF.1⟩, ⟨hi.1, hi.2.1, hF.2.1⟩, hF.2.2.1, hF.2.2.2⟩
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
  | GammaNest is his pc fn q ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨q', hF, hO, he⟩ := (ih hu.2 hi.2.2 hr sch A f hf hrel).1 rfl
    refine ⟨fun _ => ⟨(AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) is
        (fun k hc => ColKind.noConfusion hc) pc.toReg fn q').allRegOf, ?_,
        over_allRegOf (by exact hO),
        fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    · unfold Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨⟨mem_gamma, by cases pc <;> rfl⟩, hF.1⟩,
        ⟨ProjColIn.noFun_toReg hu.1.2 hi.1, hi.2.1, hF.2.1⟩, hF.2.2.1, hF.2.2.2⟩
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
      refine Multiset.map_congr rfl (fun g _ => ?_)
      funext j
      refine Fin.addCases (fun k => ?_) (fun z => ?_) j
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        refine congrArg fn (Multiset.map_congr rfl (fun u _ => ?_))
        exact (ProjColIn.evalPlain_toReg pc hu.1.2 u γ).symm
  | GammaTok is his ts fs a q keep ih => exact fun hu => hu.elim
  | ProvSum is his t q ih => exact fun hu => hu.elim
  | @Win cw nw _mw _pw κw _lab _rd P' O o w t fw q hrr dist keep ih =>
    intro hu hi hr sch A f hf hrel
    obtain ⟨q', hF, hO, he⟩ := (ih hu.2 hi.2.2.2 hr sch A f hf hrel).1 rfl
    refine ⟨fun _ => ⟨(AggQueryIn.winKept P' O o w t fw κw q' dist keep).allRegOf, ?_,
      over_allRegOf (over_winKept P' O o w t fw κw q' dist keep hO), fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · have := fine_winKept P' O o w t fw κw q' dist keep hi.1 hi.2.1 hi.2.2.1 hF
      unfold Fine at this ⊢
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact this
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]
                 exact AggQueryIn.settlesAt_winKept P' O o w t fw κw q' dist keep D γ hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf,
        AggQueryIn.evaluatePlain_winKept P' O o w t fw q hrr q' dist keep D γ he']
  | WinExpr P' O o ws ts fs g q keeps ih => exact fun _ hi => hi.elim

/-! ## The basis with products -/

/-- **`{∅, Π, σ, ×, γ, win, μ^⊎}` generates the whole algebra** in the
minimal universe: every query of the algebra over a schema, in the
signature with a count as its only aggregate, is matched by one over those
seven classes, defined and equal wherever the query is. The product
stands in for the apply: first the query is matched over
`{∅, Π, σ, apply, γ, win, μ^⊎}` (`basisRecOps_generatesOnRec`), then each
apply of the match is written with products (`Sym.exists_prodPass_aux`). -/
theorem basisProdOps_generatesOnRec (sch : Schema) (cnt : SeqAggFunc T) (hcnt : cnt.IsCount) :
    GeneratesOnRec T sch cnt basisProdOps := by
  intro n κ q ho hq hi
  obtain ⟨κ₁, q₁, ho₁, hu₁, hi₁, hx₁⟩ := basisRecOps_generatesOnRec sch cnt hcnt q ho hq hi
  have hr₁ : q₁.hygienic := q₁.hygienic_of_overSchema _ ho₁
  obtain ⟨f, hf, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch q₁.names
  have hrel : RelsIn sch (fun x => x ∈ q₁.names) q₁ :=
    relsIn_of_overSchema q₁ ho₁ hr₁ fun x hx => hx
  obtain ⟨q₂, hF, hO, he⟩ := (exists_prodPass_aux (Θ := {cnt}) (Set.mem_singleton cnt)
    hcnt.counts (fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact hcnt.readsCount) q₁ hu₁
    hi₁ hr₁ sch (fun x => x ∈ q₁.names) f ⟨hf, hfsch, hfr⟩ hrel).1 rfl
  exact ⟨_, q₂, hO.1, hF.1, hF.2.1,
    fun D γ r h => (AggQueryIn.Extends.of_settles fun D γ hs => he D γ hs) D γ r (hx₁ D γ r h)⟩

/-- **No proper subset of `basisProdOps` generates the whole algebra** in
the minimal universe over `ℕ`. The rows of `required_mem_of_generatesOnRec`
force each class: `σ` because `−` is not in the set, and `×` because the
apply is not. -/
theorem basisProdOps_minimal {S : Set OpKind} (hS : S ⊂ basisProdOps) :
    ¬ ∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S := by
  intro hgen
  obtain ⟨he, hp, hg, hm, hwin, hs, ha⟩ := required_mem_of_generatesOnRec hgen
  obtain ⟨x, hx, hxS⟩ := Set.exists_of_ssubset hS
  have hsub := hS.subset
  have hdiff : OpKind.diff ∉ S := fun h => by
    have := hsub h
    simp [basisProdOps] at this
  have happ : OpKind.apply ∉ S := fun h => by
    have := hsub h
    simp [basisProdOps] at this
  simp only [basisProdOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hxS he
  · exact hxS hp
  · exact hxS (hs.resolve_right hdiff)
  · exact hxS (ha.resolve_right happ)
  · exact hxS hg
  · exact hxS hwin
  · exact hxS hm

/-- **`basisProdOps` is a basis of the whole algebra in the minimal
universe over `ℕ`**: it generates over every schema, and no proper subset
does. -/
theorem basisProdOps_isBasis :
    (∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count basisProdOps)
      ∧ ∀ S : Set OpKind, S ⊂ basisProdOps →
          ¬ ∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S :=
  ⟨fun sch => basisProdOps_generatesOnRec sch _ SeqAggFunc.isCount_count_nat,
    fun _ hS => basisProdOps_minimal hS⟩

end Sym
