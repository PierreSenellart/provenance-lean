import Provenance.Genericity
import Mathlib.Analysis.Polynomial.Basic

/-!
# The `win` row of the whole-algebra table

`win` is in every basis of the whole algebra in the minimal universe. The
witness is `count(*) OVER (… EXCLUDE CURRENT ROW)` on a unary relation
holding `n` copies of one value, which writes `n − 1` on every row. A
window-free query of the minimal universe writes, on that family of
instances and for `n` large, only values `p(n)` for finitely many
polynomials `p` with natural coefficients, which `n − 1` is not.

The polynomials are Mathlib's `Polynomial ℕ`; what the invariant needs
of them is that two of them are eventually equal, or eventually strictly
ordered one way, which is read off their real asymptotics.
-/

variable {T : Type} [ValueType T]

namespace WinRow

/-- The instance holding `n` copies of the row `(1)` in `R`. -/
def dRep (n : ℕ) : Database ℕ :=
  [("R", ⟨1, (Multiset.replicate n ![1] : Multiset (Tuple ℕ 1))⟩)]

theorem find_dRep (n : ℕ) :
    (dRep n).find 1 "R" = some (Multiset.replicate n ![1] : Multiset (Tuple ℕ 1)) :=
  Database.find_assign "R" _ []

/-- The whole partition less the current row: `ROWS BETWEEN UNBOUNDED
PRECEDING AND UNBOUNDED FOLLOWING EXCLUDE CURRENT ROW`. -/
def wholeExcludeSelf : ValueFrame ℕ 0 := ⟨FrameCond.whole, false⟩

/-- **The witness**: `count(#1) OVER (EXCLUDE CURRENT ROW)` on `R`. -/
def winWitness : AggQuery ℕ (1 + 1) (Fin.snoc (ColKind.allReg 1) ColKind.agg) :=
  AggQueryIn.Win (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) (OrderSpec.asc 0)
    wholeExcludeSelf (TermIn.index 0) SeqAggFunc.count (AggQueryIn.Rel 1 "R")
    (winReadsReg_allReg _ _ _)

theorem usesOnly_winWitness : winWitness.usesOnly plainRecOps :=
  ⟨by simp [plainRecOps, plainOps], trivial⟩

theorem overSchema_winWitness : winWitness.overSchema schemaR := rfl

theorem inSig_winWitness : winWitness.inMinimalSig SeqAggFunc.count :=
  ⟨rfl, Set.mem_singleton _, rfl, trivial⟩

theorem settlesAt_winWitness (D : Database ℕ) (γ : Fin 0 → ℕ) : winWitness.SettlesAt D γ :=
  trivial

/-- The frame of a row of the instance: every other copy. -/
theorem frameOf_dRep (n : ℕ) :
    ValueFrame.frameOf (α := Tuple ℕ 1) id (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
        wholeExcludeSelf (Multiset.replicate n ![1]) ![1]
      = Multiset.replicate (n - 1) ![1] := by
  unfold ValueFrame.frameOf
  rw [ite_eq_right (by simp [wholeExcludeSelf, ValueFrame.s])]
  have hfilt : (Multiset.replicate n (![1] : Tuple ℕ 1)).filter (fun y =>
      Tuple.key (fun i : Fin 0 => i.elim0) (id y) = Tuple.key (fun i : Fin 0 => i.elim0) (id ![1])
        ∧ wholeExcludeSelf.ρ (Tuple.key (fun i : Fin 0 => i.elim0) (id y))
          (Tuple.key (fun i : Fin 0 => i.elim0) (id ![1])) = true)
      = Multiset.replicate n ![1] :=
    Multiset.filter_eq_self.mpr (fun _ _ => ⟨funext (fun i => i.elim0), rfl⟩)
  rw [hfilt]
  cases n with
  | zero => rfl
  | succ n =>
    rw [Multiset.replicate_succ, Multiset.erase_instEq (α := Tuple ℕ 1)
      (fun a b => LinearOrder.toDecidableEq a b) (fun a b => instDecidableEqTuple a b),
      Multiset.erase_cons_head]
    rfl

/-- **The witness writes `n − 1` on every row.** -/
theorem evaluatePlain_winWitness (n : ℕ) :
    (winWitness.evaluatePlain (dRep n) : Multiset (Tuple ℕ (1 + 1)))
      = Multiset.replicate n (Fin.snoc ![1] (n - 1) : Tuple ℕ (1 + 1)) := by
  simp only [winWitness, AggQueryIn.evaluatePlain, find_dRep, ColKind.map_readTuple_allReg]
  rw [Multiset.map_replicate]
  congr 1
  rw [ValueFrame.windowValueOpt_none, ValueFrame.windowValue]
  congr 1
  show (List.map (fun v => (TermIn.index 0).eval v (fun j : Fin 0 => j.elim0))
    (ValueFrame.frameListOf (α := Tuple ℕ 1) id _ _ _ wholeExcludeSelf _
      (ColKind.readTuple (ColKind.allReg 1) ![1]))).length = n - 1
  rw [List.length_map]
  have := congrArg Multiset.card (ValueFrame.frameListOf_coe (α := Tuple ℕ 1) id
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) (OrderSpec.asc 0) wholeExcludeSelf
    (Multiset.replicate n ![1]) ![1])
  rw [Multiset.coe_card, frameOf_dRep, Multiset.card_replicate] at this
  exact this

end WinRow

/-! ## Eventual comparison of polynomials with natural coefficients -/

namespace WinRow

open Polynomial

/-- A polynomial with natural coefficients, read as a function of `n`. -/
abbrev Poly := Polynomial ℕ

/-- Two such polynomials agreeing on all large `n` are equal. -/
theorem Poly.eq_of_eventually_eq {p q : Poly} (h : ∃ N, ∀ n ≥ N, p.eval n = q.eval n) : p = q := by
  obtain ⟨N, hN⟩ := h
  refine Polynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective ?_
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.Ici_infinite N).image
    Nat.cast_injective.injOn |>.mono ?_)
  rintro x ⟨n, hn, rfl⟩
  show ((p.map (Nat.castRingHom ℤ)).eval (n : ℤ)) = (q.map (Nat.castRingHom ℤ)).eval (n : ℤ)
  rw [Polynomial.eval_natCast_map, Polynomial.eval_natCast_map, Nat.cast_id, hN n hn]

/-- How two polynomials compare from some point on. -/
inductive Poly.Cmp (p q : Poly) (N : ℕ) : Prop where
  | lt (h : ∀ n ≥ N, p.eval n < q.eval n)
  | eq (h : ∀ n ≥ N, p.eval n = q.eval n)
  | gt (h : ∀ n ≥ N, q.eval n < p.eval n)

theorem Poly.Cmp.mono {p q : Poly} {N N' : ℕ} (hN : N ≤ N') (h : Poly.Cmp p q N) :
    Poly.Cmp p q N' := by
  cases h with
  | lt h => exact .lt (fun n hn => h n (le_trans hN hn))
  | eq h => exact .eq (fun n hn => h n (le_trans hN hn))
  | gt h => exact .gt (fun n hn => h n (le_trans hN hn))

/-- The real polynomial a natural one reads as. -/
private noncomputable def toReal (p : Poly) : Polynomial ℝ := p.map (Nat.castRingHom ℝ)

private theorem toReal_eval (p : Poly) (n : ℕ) : (toReal p).eval (n : ℝ) =
    ((p.eval n : ℕ) : ℝ) := by
  unfold toReal
  rw [Polynomial.eval_natCast_map]
  rfl

/-- A real polynomial that tends to infinity is eventually at least one. -/
private theorem exists_ge_one_of_tendsto {P : Polynomial ℝ}
    (h : Filter.Tendsto (fun x => P.eval x) Filter.atTop Filter.atTop) :
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ P.eval (n : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp h 1)
  refine ⟨⌈x₀⌉₊, fun n hn => hx₀ _ ?_⟩
  exact le_trans (Nat.le_ceil x₀) (Nat.cast_le.mpr hn)

/-- **Two polynomials with natural coefficients eventually compare one
way**: they are eventually equal, which makes them equal, or one is
eventually strictly below the other. -/
theorem Poly.exists_cmp (p q : Poly) : ∃ N, Poly.Cmp p q N := by
  classical
  set D : Polynomial ℝ := toReal p - toReal q with hD
  have hval : ∀ n : ℕ, D.eval (n : ℝ) = ((p.eval n : ℕ) : ℝ) - ((q.eval n : ℕ) : ℝ) := by
    intro n
    rw [hD, Polynomial.eval_sub, toReal_eval, toReal_eval]
  by_cases hD0 : D = 0
  · refine ⟨0, .eq (fun n _ => ?_)⟩
    have := hval n
    rw [hD0, Polynomial.eval_zero] at this
    exact_mod_cast (sub_eq_zero.mp this.symm)
  by_cases hdeg : 0 < D.degree
  · rcases lt_or_gt_of_ne (Polynomial.leadingCoeff_ne_zero.mpr hD0) with hneg | hpos
    · -- `-D` tends to infinity: `q` is eventually above `p`
      obtain ⟨N, hN⟩ := exists_ge_one_of_tendsto (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
        (-D) (by rwa [Polynomial.degree_neg]) (by rw [Polynomial.leadingCoeff_neg]; linarith))
      refine ⟨N, .lt (fun n hn => ?_)⟩
      have := hN n hn
      rw [Polynomial.eval_neg, hval] at this
      exact_mod_cast (show ((p.eval n : ℕ) : ℝ) < q.eval n by linarith)
    · obtain ⟨N, hN⟩ := exists_ge_one_of_tendsto (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
        D hdeg (le_of_lt hpos))
      refine ⟨N, .gt (fun n hn => ?_)⟩
      have := hN n hn
      rw [hval] at this
      exact_mod_cast (show ((q.eval n : ℕ) : ℝ) < p.eval n by linarith)
  · -- a non-zero constant
    have hC : D = Polynomial.C (D.coeff 0) := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)
    have hc0 : D.coeff 0 ≠ 0 := fun h => hD0 (by rw [hC, h, Polynomial.C_0])
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · refine ⟨0, .lt (fun n _ => ?_)⟩
      have := hval n
      rw [hC, Polynomial.eval_C] at this
      exact_mod_cast (show ((p.eval n : ℕ) : ℝ) < q.eval n by linarith)
    · refine ⟨0, .gt (fun n _ => ?_)⟩
      have := hval n
      rw [hC, Polynomial.eval_C] at this
      exact_mod_cast (show ((q.eval n : ℕ) : ℝ) < p.eval n by linarith)

/-- A threshold good for finitely many things, each with its own. -/
theorem exists_uniform {ι : Type} (s : Finset ι) (P : ℕ → ι → Prop)
    (hmono : ∀ i N N', N ≤ N' → P N i → P N' i) (h : ∀ i ∈ s, ∃ N, P N i) :
    ∃ N, ∀ i ∈ s, P N i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨N, hN⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨Na, hNa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨max N Na, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hmono _ _ _ (le_max_right _ _) hNa
    · exact hmono _ _ _ (le_max_left _ _) (hN i hi)

/-- **Every pair of a finite set of polynomials is decided from `N` on.** -/
def Decided (V : Set Poly) (N : ℕ) : Prop := ∀ p ∈ V, ∀ q ∈ V, Poly.Cmp p q N

theorem Decided.mono {V : Set Poly} {N N' : ℕ} (hN : N ≤ N') (h : Decided V N) : Decided V N' :=
  fun p hp q hq => (h p hp q hq).mono hN

theorem Decided.subset {V V' : Set Poly} {N : ℕ} (hV : V' ⊆ V) (h : Decided V N) : Decided V' N :=
  fun p hp q hq => h p (hV hp) q (hV hq)

theorem exists_decided {V : Set Poly} (hV : V.Finite) : ∃ N, Decided V N := by
  classical
  obtain ⟨N, hN⟩ := exists_uniform (hV.toFinset ×ˢ hV.toFinset) (fun N pq => Poly.Cmp pq.1 pq.2 N)
    (fun _ _ _ hle h => h.mono hle) (fun pq _ => Poly.exists_cmp pq.1 pq.2)
  exact ⟨N, fun p hp q hq => hN (p, q) (Finset.mem_product.mpr
    ⟨hV.mem_toFinset.mpr hp, hV.mem_toFinset.mpr hq⟩)⟩

/-- Under `Decided`, two polynomials of the set that agree once past the
threshold agree always, and are equal. -/
theorem Decided.eq_of_eval_eq {V : Set Poly} {N : ℕ} (h : Decided V N) {p q : Poly} (hp : p ∈ V)
    (hq : q ∈ V) {n : ℕ} (hn : N ≤ n) (he : p.eval n = q.eval n) : p = q := by
  rcases h p hp q hq with hc | hc | hc
  · exact absurd he (ne_of_lt (hc n hn))
  · exact Poly.eq_of_eventually_eq ⟨N, hc⟩
  · exact absurd he (ne_of_gt (hc n hn))

/-- A comparison reads alike on two pairs that compare alike. -/
theorem _root_.CompOp.eval_congr (op : CompOp) {a b a' b' : ℕ} (hlt : (a < b) ↔ (a' < b'))
    (heq : a = b ↔ a' = b') (hgt : (b < a) ↔ (b' < a')) : op.eval a b ↔ op.eval a' b' := by
  cases op <;> simp only [CompOp.eval]
  · exact heq
  · exact not_congr heq
  · exact hlt
  · rw [← not_lt, ← not_lt]; exact not_congr hgt
  · exact hgt
  · rw [ge_iff_le, ge_iff_le, ← not_lt, ← not_lt]; exact not_congr hlt
  · exact heq
  · exact not_congr heq

/-- Under `Decided`, a comparison between two polynomials of the set reads
alike at every `n` past the threshold. -/
theorem Decided.compOp_eval {V : Set Poly} {N : ℕ} (h : Decided V N) (op : CompOp) {p q : Poly}
    (hp : p ∈ V) (hq : q ∈ V) {n n' : ℕ} (hn : N ≤ n) (hn' : N ≤ n') :
    op.eval (p.eval n) (q.eval n) ↔ op.eval (p.eval n') (q.eval n') := by
  rcases h p hp q hq with hc | hc | hc
  · exact CompOp.eval_congr op (iff_of_true (hc n hn) (hc n' hn'))
      (iff_of_false (ne_of_lt (hc n hn)) (ne_of_lt (hc n' hn')))
      (iff_of_false (not_lt.mpr (le_of_lt (hc n hn))) (not_lt.mpr (le_of_lt (hc n' hn'))))
  · exact CompOp.eval_congr op (iff_of_false (not_lt.mpr (le_of_eq (hc n hn).symm))
        (not_lt.mpr (le_of_eq (hc n' hn').symm)))
      (iff_of_true (hc n hn) (hc n' hn'))
      (iff_of_false (not_lt.mpr (le_of_eq (hc n hn))) (not_lt.mpr (le_of_eq (hc n' hn'))))
  · exact CompOp.eval_congr op
      (iff_of_false (not_lt.mpr (le_of_lt (hc n hn))) (not_lt.mpr (le_of_lt (hc n' hn'))))
      (iff_of_false (ne_of_gt (hc n hn)) (ne_of_gt (hc n' hn')))
      (iff_of_true (hc n hn) (hc n' hn'))

end WinRow

/-! ## Polynomial bags

A relation computed on the instance with `n` copies is, for `n` large, a
bag of finitely many *shapes*: a row of polynomials, each repeated a
polynomial number of times. -/

namespace WinRow

open Polynomial

noncomputable section

/-- A shape: a row of polynomials with a polynomial multiplicity. -/
structure Shape (k : ℕ) where
  mult : Poly
  row : Fin k → Poly

/-- The row of a shape at `n`. -/
def Shape.rowAt {k : ℕ} (s : Shape k) (n : ℕ) : Tuple ℕ k := fun j => (s.row j).eval n

/-- The copies of a shape at `n`. -/
def Shape.inst {k : ℕ} (s : Shape k) (n : ℕ) : Multiset (Tuple ℕ k) :=
  Multiset.replicate (s.mult.eval n) (s.rowAt n)

/-- A bag of shapes. -/
abbrev PolyBag (k : ℕ) := List (Shape k)

/-- The relation a bag of shapes stands for at `n`. -/
def PolyBag.inst {k : ℕ} (L : PolyBag k) (n : ℕ) : Multiset (Tuple ℕ k) :=
  (L.map (fun s => s.inst n)).sum

/-- The polynomials the rows of a bag hold. -/
def PolyBag.vals {k : ℕ} (L : PolyBag k) : Set Poly := {p | ∃ s ∈ L, ∃ j, s.row j = p}

/-- The multiplicities of a bag. -/
def PolyBag.mults {k : ℕ} (L : PolyBag k) : Set Poly := {p | ∃ s ∈ L, s.mult = p}

theorem PolyBag.vals_finite {k : ℕ} (L : PolyBag k) : (PolyBag.vals L).Finite := by
  classical
  have : PolyBag.vals L = ⋃ s ∈ L.toFinset, Set.range s.row := by
    ext p
    simp only [PolyBag.vals, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range, exists_prop,
      List.mem_toFinset]
  rw [this]
  exact Set.Finite.biUnion (L.toFinset.finite_toSet) (fun s _ => Set.finite_range _)

theorem PolyBag.mults_finite {k : ℕ} (L : PolyBag k) : (PolyBag.mults L).Finite := by
  classical
  have : PolyBag.mults L = Shape.mult '' (↑L.toFinset : Set (Shape k)) := by
    ext p
    simp only [PolyBag.mults, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
  rw [this]
  exact L.toFinset.finite_toSet.image _

theorem PolyBag.vals_subset_of_mem {k : ℕ} {L : PolyBag k} {s : Shape k} (hs : s ∈ L) (j : Fin k) :
    s.row j ∈ PolyBag.vals L := ⟨s, hs, j, rfl⟩

@[simp] theorem PolyBag.inst_nil {k : ℕ} (n : ℕ) : PolyBag.inst ([] : PolyBag k) n = 0 := rfl

theorem PolyBag.inst_cons {k : ℕ} (s : Shape k) (L : PolyBag k) (n : ℕ) :
    PolyBag.inst (s :: L) n = s.inst n + PolyBag.inst L n := by
  simp [PolyBag.inst]

theorem PolyBag.inst_append {k : ℕ} (L₁ L₂ : PolyBag k) (n : ℕ) :
    PolyBag.inst (L₁ ++ L₂) n = PolyBag.inst L₁ n + PolyBag.inst L₂ n := by
  simp [PolyBag.inst]

theorem PolyBag.mem_inst {k : ℕ} {L : PolyBag k} {n : ℕ} {u : Tuple ℕ k} :
    u ∈ PolyBag.inst L n ↔ ∃ s ∈ L, s.mult.eval n ≠ 0 ∧ u = s.rowAt n := by
  induction L with
  | nil => simp [PolyBag.inst]
  | cons s L ih =>
    rw [PolyBag.inst_cons, Multiset.mem_add, ih]
    constructor
    · rintro (h | ⟨t, ht, hm, rfl⟩)
      · obtain ⟨hm, rfl⟩ := Multiset.mem_replicate.mp h
        exact ⟨s, List.mem_cons_self, hm, rfl⟩
      · exact ⟨t, List.mem_cons_of_mem _ ht, hm, rfl⟩
    · rintro ⟨t, ht, hm, rfl⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl (Multiset.mem_replicate.mpr ⟨hm, rfl⟩)
      · exact Or.inr ⟨t, ht, hm, rfl⟩

/-- A function over a bag of copies. -/
theorem _root_.Multiset.replicate_bind {α β : Type} (m : ℕ) (a : α) (g : α → Multiset β) :
    (Multiset.replicate m a).bind g = m • g a := by
  induction m with
  | zero => simp
  | succ m ih => rw [Multiset.replicate_succ, Multiset.cons_bind, ih, succ_nsmul, add_comm]

theorem _root_.Multiset.filter_replicate {α : Type} (p : α → Prop) [DecidablePred p] (m : ℕ)
    (a : α) : (Multiset.replicate m a).filter p = if p a then Multiset.replicate m a else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Multiset.replicate_succ, Multiset.filter_cons, ih]
    split
    · simp
    · simp

/-- Scaling every multiplicity. -/
def PolyBag.scale {k : ℕ} (m : Poly) (L : PolyBag k) : PolyBag k :=
  L.map (fun s => ⟨m * s.mult, s.row⟩)

theorem PolyBag.inst_scale {k : ℕ} (m : Poly) (L : PolyBag k) (n : ℕ) :
    (m.eval n) • PolyBag.inst L n = PolyBag.inst (PolyBag.scale m L) n := by
  induction L with
  | nil => simp [PolyBag.inst, PolyBag.scale]
  | cons s L ih =>
    rw [PolyBag.inst_cons, nsmul_add, ih]
    show _ = PolyBag.inst ((⟨m * s.mult, s.row⟩ : Shape k) :: PolyBag.scale m L) n
    rw [PolyBag.inst_cons]
    congr 1
    unfold Shape.inst
    rw [Multiset.nsmul_replicate, Polynomial.eval_mul]
    rfl

/-- Mapping the rows. -/
def PolyBag.mapRows {k k' : ℕ} (f : (Fin k → Poly) → (Fin k' → Poly)) (L : PolyBag k) :
    PolyBag k' := L.map (fun s => ⟨s.mult, f s.row⟩)

theorem PolyBag.inst_mapRows {k k' : ℕ} (f : (Fin k → Poly) → (Fin k' → Poly))
    (g : Tuple ℕ k → Tuple ℕ k') (L : PolyBag k) (n : ℕ)
    (hf : ∀ s ∈ L, g (s.rowAt n) = (⟨s.mult, f s.row⟩ : Shape k').rowAt n) :
    (PolyBag.inst L n).map g = PolyBag.inst (PolyBag.mapRows f L) n := by
  induction L with
  | nil => simp [PolyBag.inst, PolyBag.mapRows]
  | cons s L ih =>
    rw [PolyBag.inst_cons, Multiset.map_add, ih (fun t ht => hf t (List.mem_cons_of_mem _ ht))]
    show _ = PolyBag.inst ((⟨s.mult, f s.row⟩ : Shape k') :: PolyBag.mapRows f L) n
    rw [PolyBag.inst_cons]
    congr 1
    unfold Shape.inst
    rw [Multiset.map_replicate, hf s List.mem_cons_self]

/-- Keeping the shapes a test keeps. -/
theorem PolyBag.inst_filter {k : ℕ} (p : Tuple ℕ k → Prop) (dec : DecidablePred p)
    (P : Shape k → Bool) (L : PolyBag k) (n : ℕ) (hP : ∀ s ∈ L, (p (s.rowAt n) ↔ P s = true)) :
    @Multiset.filter _ p dec (PolyBag.inst L n) = PolyBag.inst (L.filter P) n := by
  induction L with
  | nil => simp [PolyBag.inst]
  | cons s L ih =>
    rw [PolyBag.inst_cons, Multiset.filter_add, ih (fun t ht => hP t (List.mem_cons_of_mem _ ht))]
    unfold Shape.inst
    rw [Multiset.filter_replicate]
    by_cases hs : P s = true
    · rw [ite_eq_left ((hP s List.mem_cons_self).mpr hs), List.filter_cons_of_pos hs,
        PolyBag.inst_cons]
      rfl
    · rw [ite_eq_right (fun h => hs ((hP s List.mem_cons_self).mp h)), List.filter_cons_of_neg hs,
        zero_add]

/-- A bag of shapes under each shape, as an apply reads its right side. -/
def PolyBag.bindShapes {k₁ k₂ : ℕ} (L₁ : PolyBag k₁) (F : Shape k₁ → PolyBag k₂) :
    PolyBag (k₁ + k₂) :=
  L₁.flatMap (fun s => (F s).map (fun t => ⟨s.mult * t.mult, Fin.append s.row t.row⟩))

theorem Shape.rowAt_append {k₁ k₂ : ℕ} (m : Poly) (r₁ : Fin k₁ → Poly) (r₂ : Fin k₂ → Poly)
    (n : ℕ) : (⟨m, Fin.append r₁ r₂⟩ : Shape (k₁ + k₂)).rowAt n
      = Fin.append (fun j => (r₁ j).eval n) (fun j => (r₂ j).eval n) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · show (Fin.append r₁ r₂ (Fin.castAdd k₂ i)).eval n = _
    rw [Fin.append_left, Fin.append_left]
  · show (Fin.append r₁ r₂ (Fin.natAdd k₁ j)).eval n = _
    rw [Fin.append_right, Fin.append_right]

theorem PolyBag.inst_bindShapes {k₁ k₂ : ℕ} (L₁ : PolyBag k₁) (F : Shape k₁ → PolyBag k₂)
    (G : Tuple ℕ k₁ → Multiset (Tuple ℕ k₂)) (n : ℕ)
    (hG : ∀ s ∈ L₁, s.mult.eval n ≠ 0 → G (s.rowAt n) = PolyBag.inst (F s) n) :
    (PolyBag.inst L₁ n).bind (fun u => (G u).map (fun v => (Fin.append u v : Tuple ℕ (k₁ + k₂))))
      = PolyBag.inst (PolyBag.bindShapes L₁ F) n := by
  induction L₁ with
  | nil => simp [PolyBag.inst, PolyBag.bindShapes]
  | cons s L ih =>
    rw [PolyBag.inst_cons, Multiset.add_bind, ih (fun t ht => hG t (List.mem_cons_of_mem _ ht))]
    show _ = PolyBag.inst ((F s).map (fun t => (⟨s.mult * t.mult, Fin.append s.row t.row⟩
      : Shape (k₁ + k₂))) ++ PolyBag.bindShapes L F) n
    rw [PolyBag.inst_append]
    congr 1
    unfold Shape.inst
    rw [Multiset.replicate_bind]
    by_cases hm : s.mult.eval n = 0
    · rw [hm, zero_smul]
      symm
      show ((F s).map _ |>.map (fun t => Shape.inst t n)).sum = 0
      rw [List.map_map]
      refine List.sum_eq_zero (fun M hM => ?_)
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hM
      show Multiset.replicate ((s.mult * t.mult).eval n) _ = 0
      rw [Polynomial.eval_mul, hm, zero_mul, Multiset.replicate_zero]
    · rw [hG s List.mem_cons_self hm]
      have hmap := PolyBag.inst_mapRows (fun r => Fin.append s.row r)
        (fun v : Tuple ℕ k₂ => (Fin.append (fun j => (s.row j).eval n) v : Tuple ℕ (k₁ + k₂)))
        (F s) n (fun t _ => (Shape.rowAt_append _ _ _ n).symm)
      erw [hmap, PolyBag.inst_scale]
      show PolyBag.inst (PolyBag.scale s.mult (PolyBag.mapRows (fun r => Fin.append s.row r)
          (F s))) n = _
      unfold PolyBag.scale PolyBag.mapRows
      rw [List.map_map]
      rfl

end

end WinRow

/-! ## Symbolic terms, and the shift from the threshold

A function-free term over a row of polynomials is a polynomial. A
predicate over decided polynomials reads alike at the threshold and at
every larger `n`, because the values at `n` are the image of the values
at the threshold under a faithful map (`Provenance.Genericity`). -/

namespace WinRow

open Polynomial

noncomputable section

/-- A context of polynomials at `n`. -/
def ctxAt {c : ℕ} (cγ : Fin c → Poly) (n : ℕ) : Fin c → ℕ := fun j => (cγ j).eval n

/-- The constants of a query as polynomials. -/
def Cset (A : Finset ℕ) : Set Poly := (fun a : ℕ => (Polynomial.C a : Poly)) '' ↑A

theorem Cset_finite (A : Finset ℕ) : (Cset A).Finite := A.finite_toSet.image _

theorem mem_Cset {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) : (Polynomial.C a : Poly) ∈ Cset A :=
  ⟨a, ha, rfl⟩

theorem Cset_mono {A A' : Finset ℕ} (h : A ⊆ A') : Cset A ⊆ Cset A' :=
  Set.image_mono (Finset.coe_subset.mpr h)

/-- The polynomial a function-free term reads as. -/
def TermIn.polyOf {c k : ℕ} (t : TermIn ℕ c k) (row : Fin k → Poly) (cγ : Fin c → Poly) : Poly :=
  match t with
  | .const a => Polynomial.C a
  | .outer j => cγ j
  | .index j => row j
  | _ => 0

theorem TermIn.eval_polyOf {c k : ℕ} (t : TermIn ℕ c k) (ht : t.noFun = true) (s : Shape k)
    (cγ : Fin c → Poly) (n : ℕ) :
    t.eval (s.rowAt n) (ctxAt cγ n) = (TermIn.polyOf t s.row cγ).eval n := by
  cases t with
  | const a => simp [TermIn.eval, TermIn.polyOf]
  | outer j => rfl
  | index j => rfl
  | add _ _ | sub _ _ | mul _ _ | caseWhen _ _ _ _ _ | coalesce _ _ =>
    exact absurd ht (by simp [TermIn.noFun])

theorem TermIn.polyOf_mem {c k : ℕ} (t : TermIn ℕ c k) (ht : t.noFun = true) (row : Fin k → Poly)
    (cγ : Fin c → Poly) :
    TermIn.polyOf t row cγ ∈ Union.union (Union.union (Cset t.consts) (Set.range row))
        (Set.range cγ) := by
  cases t with
  | const a => exact Or.inl (Or.inl (mem_Cset (Finset.mem_singleton_self a)))
  | outer j => exact Or.inr ⟨j, rfl⟩
  | index j => exact Or.inl (Or.inr ⟨j, rfl⟩)
  | add _ _ | sub _ _ | mul _ _ | caseWhen _ _ _ _ _ | coalesce _ _ =>
    exact absurd ht (by simp [TermIn.noFun])

/-- The polynomial a function-free term of the general syntax reads as. -/
def TermGIn.polyOf {c k : ℕ} {κ : Fin k → ColKind} (t : TermGIn ℕ c κ) (row : Fin k → Poly)
    (cγ : Fin c → Poly) : Poly :=
  match t with
  | .const a => Polynomial.C a
  | .outer j => cγ j
  | .index j _ => row j
  | .provIndex j _ => row j
  | _ => 0

theorem TermGIn.evalPlain_polyOf {c k : ℕ} {κ : Fin k → ColKind} (t : TermGIn ℕ c κ)
    (ht : t.noFun = true) (s : Shape k) (cγ : Fin c → Poly) (n : ℕ) :
    t.evalPlain (s.rowAt n) (ctxAt cγ n) = (TermGIn.polyOf t s.row cγ).eval n := by
  cases t with
  | const a => simp [TermGIn.evalPlain, TermGIn.polyOf]
  | outer j => rfl
  | index j _ => rfl
  | provIndex j _ => rfl
  | cmpAgg _ _ _ _ | chiGate _ _ _ | add _ _ | sub _ _ | mul _ _ | caseWhen _ _ _ _ _
  | coalesce _ _ => exact absurd ht (by simp [TermGIn.noFun])

theorem TermGIn.polyOf_mem {c k : ℕ} {κ : Fin k → ColKind} (t : TermGIn ℕ c κ)
    (ht : t.noFun = true) (row : Fin k → Poly) (cγ : Fin c → Poly) :
    TermGIn.polyOf t row cγ ∈ Union.union (Union.union (Cset t.consts) (Set.range row))
        (Set.range cγ) := by
  cases t with
  | const a => exact Or.inl (Or.inl (mem_Cset (Finset.mem_singleton_self a)))
  | outer j => exact Or.inr ⟨j, rfl⟩
  | index j _ => exact Or.inl (Or.inr ⟨j, rfl⟩)
  | provIndex j _ => exact Or.inl (Or.inr ⟨j, rfl⟩)
  | cmpAgg _ _ _ _ | chiGate _ _ _ | add _ _ | sub _ _ | mul _ _ | caseWhen _ _ _ _ _
  | coalesce _ _ => exact absurd ht (by simp [TermGIn.noFun])

/-- The polynomial a function-free projection column reads as. -/
def ProjColIn.polyOf {c k : ℕ} {κ : Fin k → ColKind} (p : ProjColIn ℕ c κ) (row : Fin k → Poly)
    (cγ : Fin c → Poly) : Poly :=
  match p with
  | .term t => TermGIn.polyOf t row cγ
  | .token j _ => row j
  | .aggTerm _ _ _ => 0
  | .aggTermOf j _ t => TermIn.polyOf t (fun i => i.elim0) (fun _ => row j)
  | .provTerm t => TermGIn.polyOf t row cγ

theorem ProjColIn.evalPlain_polyOf {c k : ℕ} {κ : Fin k → ColKind} (p : ProjColIn ℕ c κ)
    (hp : p.noFun = true) (s : Shape k) (cγ : Fin c → Poly) (n : ℕ) :
    p.evalPlain (s.rowAt n) (ctxAt cγ n) = (ProjColIn.polyOf p s.row cγ).eval n := by
  cases p with
  | term t => exact TermGIn.evalPlain_polyOf t hp s cγ n
  | token j _ => rfl
  | aggTerm _ _ _ => exact absurd hp (by simp [ProjColIn.noFun])
  | aggTermOf j _ t =>
    show t.unary (s.rowAt n j) = _
    rw [TermIn.unary]
    have he : (fun i : Fin 0 => i.elim0) = (⟨0, fun i : Fin 0 => i.elim0⟩ : Shape 0).rowAt n :=
      funext (fun i => i.elim0)
    rw [he]
    exact TermIn.eval_polyOf t hp ⟨0, fun i : Fin 0 => i.elim0⟩ (fun _ => s.row j) n
  | provTerm t => exact TermGIn.evalPlain_polyOf t hp s cγ n

theorem ProjColIn.polyOf_mem {c k : ℕ} {κ : Fin k → ColKind} (p : ProjColIn ℕ c κ)
    (hp : p.noFun = true) (row : Fin k → Poly) (cγ : Fin c → Poly) :
    ProjColIn.polyOf p row cγ ∈ Union.union (Union.union (Cset p.consts) (Set.range row))
        (Set.range cγ) := by
  cases p with
  | term t => exact TermGIn.polyOf_mem t hp row cγ
  | token j _ => exact Or.inl (Or.inr ⟨j, rfl⟩)
  | aggTerm _ _ _ => exact absurd hp (by simp [ProjColIn.noFun])
  | aggTermOf j _ t =>
    rcases TermIn.polyOf_mem t hp (fun i => i.elim0) (fun _ => row j) with (h | ⟨i, _⟩) | ⟨_, h⟩
    · exact Or.inl (Or.inl h)
    · exact i.elim0
    · exact Or.inl (Or.inr ⟨j, h⟩)
  | provTerm t => exact TermGIn.polyOf_mem t hp row cγ

/-- **The shift from the threshold to `n`** on decided polynomials: the
values at `n` are the image of the values at `N` under a faithful map
that fixes what both evaluate alike. -/
theorem exists_faithful_shift {V : Set Poly} {N : ℕ} (hV : Decided V N) {n : ℕ} (hn : N ≤ n) :
    ∃ τ : ℕ → ℕ, FaithfulOn τ {x | ∃ p ∈ V, p.eval N = x} ∧ ∀ p ∈ V, τ (p.eval N) = p.eval n := by
  classical
  let τ : ℕ → ℕ := fun x =>
    if h : ∃ p ∈ V, p.eval N = x then (Classical.choose h).eval n else x
  have hτ : ∀ p ∈ V, τ (p.eval N) = p.eval n := by
    intro p hp
    have hex : ∃ q ∈ V, q.eval N = p.eval N := ⟨p, hp, rfl⟩
    show (if h : ∃ q ∈ V, q.eval N = p.eval N then (Classical.choose h).eval n else p.eval N)
      = p.eval n
    rw [dite_eq_left hex]
    obtain ⟨hq, hqe⟩ := Classical.choose_spec hex
    rw [hV.eq_of_eval_eq hq hp (le_refl N) hqe]
  refine ⟨τ, ⟨fun a _ => rfl, ?_⟩, hτ⟩
  rintro a ⟨p, hp, rfl⟩ b ⟨q, hq, rfl⟩
  rw [hτ p hp, hτ q hq]
  exact hV.compOp_eval CompOp.le hp hq hn (le_refl N)

/-- A predicate over decided polynomials reads at `n` as at the threshold. -/
theorem GenPredIn.holdsPlain_shift {c k : ℕ} {κ : Fin k → ColKind} (φ : GenPredIn ℕ c κ)
    (hφ : φ.noFun = true) {V : Set Poly} {N : ℕ} (hV : Decided V N)
    (hc : Cset φ.consts ⊆ V) {s : Shape k} (hs : ∀ j, s.row j ∈ V) {cγ : Fin c → Poly}
    (hγ : ∀ j, cγ j ∈ V) {n : ℕ} (hn : N ≤ n) :
    φ.holdsPlain (s.rowAt n) (ctxAt cγ n) ↔ φ.holdsPlain (s.rowAt N) (ctxAt cγ N) := by
  obtain ⟨τ, h, hτ⟩ := exists_faithful_shift hV hn
  have hrow : (τ ∘ s.rowAt N : Tuple ℕ k) = s.rowAt n := funext (fun j => hτ _ (hs j))
  have hctx : (τ ∘ ctxAt cγ N) = ctxAt cγ n := funext (fun j => hτ _ (hγ j))
  rw [← hrow, ← hctx]
  refine h.genPredIn_holdsPlain φ hφ (fun a ha => ?_) (fun j => ⟨_, hs j, rfl⟩)
    (fun j => ⟨_, hγ j, rfl⟩)
  have hC : (Polynomial.C a : Poly) ∈ V := hc (mem_Cset ha)
  refine ⟨?_, ⟨_, hC, by simp⟩⟩
  have := hτ _ hC
  simpa using this

/-- A clause over decided polynomials keeps at `n` what it keeps at the
threshold. -/
theorem Selection.keepsOpt_shift {k : ℕ} (keep : Option (Selection ℕ k))
    (hk : Selection.noFunOpt keep = true) {V : Set Poly} {N : ℕ} (hV : Decided V N)
    (hc : Cset (Selection.constsOpt keep) ⊆ V) {s : Shape k} (hs : ∀ j, s.row j ∈ V) {n : ℕ}
    (hn : N ≤ n) : Selection.keepsOpt keep (s.rowAt n) = Selection.keepsOpt keep (s.rowAt N) := by
  obtain ⟨τ, h, hτ⟩ := exists_faithful_shift hV hn
  have hrow : (τ ∘ s.rowAt N : Tuple ℕ k) = s.rowAt n := funext (fun j => hτ _ (hs j))
  rw [← hrow]
  refine h.selection_keepsOpt keep hk (fun a ha => ?_) (fun j => ⟨_, hs j, rfl⟩)
  have hC : (Polynomial.C a : Poly) ∈ V := hc (mem_Cset ha)
  refine ⟨?_, ⟨_, hC, by simp⟩⟩
  have := hτ _ hC
  simpa using this

/-- A row of decided polynomials equals another at `n` as at the threshold. -/
theorem Shape.rowAt_eq_shift {k : ℕ} {V : Set Poly} {N : ℕ} (hV : Decided V N) {s t : Shape k}
    (hs : ∀ j, s.row j ∈ V) (ht : ∀ j, t.row j ∈ V) {n : ℕ} (hn : N ≤ n) :
    (s.rowAt n = t.rowAt n) ↔ (s.rowAt N = t.rowAt N) := by
  constructor
  · intro h
    funext j
    have := congrFun h j
    show (s.row j).eval N = (t.row j).eval N
    rw [hV.eq_of_eval_eq (hs j) (ht j) hn this]
  · intro h
    funext j
    have := congrFun h j
    show (s.row j).eval n = (t.row j).eval n
    rw [hV.eq_of_eval_eq (hs j) (ht j) (le_refl N) this]

/-- A non-zero polynomial with natural coefficients is positive from `1` on. -/
theorem Poly.eval_pos_of_ne_zero {p : Poly} (hp : p ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    0 < p.eval n := by
  obtain ⟨i, hi⟩ : ∃ i, p.coeff i ≠ 0 := by
    by_contra h
    exact hp (Polynomial.ext (fun i => by
      rw [not_not.mp (not_exists.mp h i), Polynomial.coeff_zero]))
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Polynomial.mem_support_iff.mpr hi))
  exact Nat.mul_pos (Nat.pos_of_ne_zero hi) (pow_pos hn i)

theorem Poly.eval_eq_zero_iff {p : Poly} {n : ℕ} (hn : 1 ≤ n) : p.eval n = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    exact absurd h (ne_of_gt (Poly.eval_pos_of_ne_zero hp hn))
  · rintro rfl
    simp

end

end WinRow

/-! ## The count polynomials of a query

A polynomial is a count polynomial of a query if, for `n` large, its
value is one of the counts the query computes on the instance with `n`
copies (`AggQueryIn.countValsAll`, over every context). There are finitely
many, because the counts a query computes on that instance are at most a
constant in number (`AggQueryIn.exists_polyBound_countTypes` over a base
set of constant size). -/

variable {T : Type} [ValueType T]

/-- A query not mentioning a name computes the same counts on two
instances agreeing away from it. -/
theorem AggQueryIn.countValsAll_congr_of_noMention {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention s → ∀ {D D' : Database T}, Database.AgreeOff s l D D' →
      q.countValsAll D = q.countValsAll D' := by
  intro c n κ l q
  induction q with
  | Rel n s => intro _ D D' _; rfl
  | Hole n s => intro _ D D' _; rfl
  | Param pv ρ => intro _ D D' _; rfl
  | Empty => intro _ D D' _; rfl
  | Proj ps q ih => intro h D D' hD; exact ih h hD
  | Sel φ q _ ih => intro h D D' hD; exact ih h hD
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro h D D' hD
    show Union.union _ _ = Union.union _ _
    rw [ih₁ h.1 (hD.mono (fun p hp => List.mem_append_left _ hp)),
      ih₂ h.2 (hD.mono (fun p hp => List.mem_append_right _ hp))]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h D D' hD
    show Union.union _ _ = Union.union _ _
    rw [ih₁ h.1 hD, ih₂ h.2 (hD.mono (fun p hp => absurd hp List.not_mem_nil))]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro h D D' hD
    show Union.union _ _ = Union.union _ _
    rw [ih₁ h.1 (hD.mono (fun p hp => List.mem_append_left _ hp)),
      ih₂ h.2 (hD.mono (fun p hp => List.mem_append_right _ hp))]
  | Dedup q ih => intro h D D' hD; exact ih h hD
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro h D D' hD
    show Union.union _ _ = Union.union _ _
    rw [ih₁ h.1 hD, ih₂ h.2 hD]
  | Explode k hk q ih => intro h D D' hD; exact ih h hD
  | Retag hk q ih => intro h D D' hD; exact ih h hD
  | Mu s' q₀ q₁ ih₀ ih₁ =>
    intro h D D' hD
    show Union.union _ (Set.iUnion _) = Union.union _ (Set.iUnion _)
    rw [ih₀ h.1 hD]
    congr 1
    exact Set.iUnion_congr (fun X => ih₁ h.2 (hD.assign s' X))
  | MuSet s' q₀ q₁ ih₀ ih₁ =>
    intro h D D' hD
    show Union.union _ (Set.iUnion _) = Union.union _ (Set.iUnion _)
    rw [ih₀ h.1 hD]
    congr 1
    exact Set.iUnion_congr (fun X => ih₁ h.2 (hD.assign s' X))
  | Gamma is ts fs q keep ord ih =>
    intro h D D' hD
    show Union.union _ {v | ∃ γ u, Multiset.Mem
        ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain
      D γ) u ∧ _} = Union.union _ {v | ∃ γ u, Multiset.Mem
        ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain D' γ) u ∧ _}
    rw [ih h hD]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [← AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
  | GammaScalar ts fs q ord ih =>
    intro h D D' hD
    show Union.union _ {v | ∃ γ u, Multiset.Mem ((AggQueryIn.GammaScalar ts fs q ord).evaluatePlain
      D γ) u ∧ _} = Union.union _ {v | ∃ γ u, Multiset.Mem
        ((AggQueryIn.GammaScalar ts fs q ord).evaluatePlain D' γ) u ∧ _}
    rw [ih h hD]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [← AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
  | GammaNest is his p f q ih =>
    intro h D D' hD
    show Union.union _ {v | ∃ γ u, Multiset.Mem ((AggQueryIn.GammaNest is his p f q).evaluatePlain
      D γ) u ∧ _} = Union.union _ {v | ∃ γ u, Multiset.Mem
        ((AggQueryIn.GammaNest is his p f q).evaluatePlain D' γ) u ∧ _}
    rw [ih h hD]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [← AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
  | ProvSum is his t q ih => intro h D D' hD; exact ih h hD
  | GammaTok is his ts fs a q keep ih => intro h D D' hD; exact ih h hD
  | Win P O o w t f q hrr dist keep ih =>
    intro h D D' hD
    show Union.union _ {v | ∃ γ u, Multiset.Mem ((AggQueryIn.Win P O o w t f q hrr dist
      keep).evaluatePlain D γ) u ∧ _} = Union.union _ {v | ∃ γ u, Multiset.Mem
        ((AggQueryIn.Win P O o w t f q hrr dist keep).evaluatePlain D' γ) u ∧ _}
    rw [ih h hD]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [← AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
    · rintro ⟨γ, u, hu, hv⟩
      exact ⟨γ, u, by rwa [AggQueryIn.evaluatePlain_congr_of_noMention _ h hD γ], hv⟩
  | WinExpr P O o ws ts fs g q keeps ih => intro h D D' hD; exact ih h hD

namespace WinRow

open Polynomial

theorem find_dRep_ne (n : ℕ) {k : ℕ} {t : String} (h : ¬ (k = 1 ∧ t = "R")) :
    (dRep n).find k t = none :=
  Database.find_assign_of_ne "R" t _ [] h

/-- The values of the instance with `n` copies, at any name the query may
read, are `1`. -/
theorem dRep_vals (n : ℕ) {k : ℕ} {t : String} {r : Relation ℕ k}
    (hr : (dRep n).find k t = some r) : ∀ u, Multiset.Mem r u → ∀ j, u j = 1 := by
  by_cases h : k = 1 ∧ t = "R"
  · obtain ⟨rfl, rfl⟩ := h
    rw [find_dRep, Option.some.injEq] at hr
    subst hr
    intro u hu j
    rw [Multiset.eq_of_mem_replicate hu]
    exact Fin.fin_one_eq_zero j ▸ rfl
  · rw [find_dRep_ne n h] at hr
    exact absurd hr (by simp)

/-- The count polynomials of a closed query. -/
def CountPolys {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) : Set Poly :=
  {p | ∃ N, ∀ n ≥ N, p.eval n ∈ q.countValsAll (dRep n)}

/-- The count polynomials of a term with a hole, over every binding of it. -/
def CountPolysHole {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) (s : String) (m : ℕ) : Set Poly :=
  {p | ∃ N, ∀ n ≥ N, ∃ X : Relation ℕ m, p.eval n ∈ q.countValsAll ((dRep n).assign s X)}

/-- The base set of the instance family: the instance's value, the zero,
and the query's constants. -/
def baseSet (A : Finset ℕ) : Finset ℕ := insert 0 (insert 1 A)

/-- **Finitely many polynomials take, for `n` large, values in a family of
sets of bounded size.** -/
theorem finite_of_eventually_mem {K : ℕ} (S : ℕ → Set ℕ) (hS : ∀ n, ∃ F : Finset ℕ,
    S n ⊆ ↑F ∧ F.card ≤ K)
    : {p : Poly | ∃ N, ∀ n ≥ N, p.eval n ∈ S n}.Finite := by
  classical
  by_contra hinf
  obtain ⟨F, hF, hcard⟩ := (Set.not_finite.mp hinf).exists_subset_card_eq (K + 1)
  obtain ⟨N₁, hN₁⟩ := exists_uniform F (fun N p => ∀ n ≥ N, p.eval n ∈ S n)
    (fun p N N' hle h n hn => h n (le_trans hle hn)) (fun p hp => hF hp)
  obtain ⟨N₂, hN₂⟩ := exists_decided (F.finite_toSet)
  set n := max N₁ N₂ with hn
  obtain ⟨G, hG, hGK⟩ := hS n
  have hinj : Set.InjOn (fun p : Poly => p.eval n) ↑F := fun p hp q hq he =>
    hN₂.eq_of_eval_eq hp hq (le_max_right _ _) he
  have hmaps : ∀ p ∈ F, p.eval n ∈ G := fun p hp => hG (hN₁ p hp n (le_max_left _ _))
  have := Finset.card_le_card_of_injOn (fun p : Poly => p.eval n) hmaps hinj
  omega

/-- **A closed query has finitely many count polynomials.** -/
theorem CountPolys_finite {c k : ℕ} {κ : Fin k → ColKind} (q : AggQueryIn ℕ c k κ)
    (hs : q.inSig {SeqAggFunc.count}) (hh : q.hygienic) : (CountPolys q).Finite := by
  obtain ⟨f, -, hb⟩ := AggQueryIn.exists_polyBound_countTypes
    SeqAggFunc.isCount_count_nat.readsCount q hs hh (fun p hp => absurd hp List.not_mem_nil)
  refine finite_of_eventually_mem (K := (baseSet q.allConsts).card + f (baseSet q.allConsts).card)
    (fun n => q.countValsAll (dRep n)) (fun n => ?_)
  have hν : ∀ ν : ℕ, ValueType.nullVal = some ν → ν ∈ baseSet q.allConsts :=
    fun ν hν => absurd hν (by simp)
  have h0 : (0 : ℕ) ∈ baseSet q.allConsts := Finset.mem_insert_self _ _
  have hD : ∀ p ∈ q.leaves, (p.2, p.1) ∉ ([] : List (String × ℕ)) → ∀ r : Relation ℕ p.1,
      (dRep n).find p.1 p.2 = some r → ∀ u, Multiset.Mem r u → ∀ j, u j ∈ baseSet q.allConsts :=
    fun p _ _ r hr u hu j => by
      rw [dRep_vals n hr u hu j]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hc : ∀ a ∈ q.allConsts, a ∈ baseSet q.allConsts :=
    fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)
  refine ⟨Union.union (baseSet q.allConsts) (q.countTypes (baseSet q.allConsts) (dRep n)), ?_, ?_⟩
  · exact AggQueryIn.countValsAll_subset SeqAggFunc.isCount_count_nat.readsCount hν h0 q hs hh
      (fun p hp => absurd hp List.not_mem_nil) (dRep n) (dRep n) (fun _ _ _ => rfl) hD hc
  · exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (hb _ _ hν h0 hD hc) _)

/-- **A term with a hole has finitely many count polynomials**, over every
binding of its hole. -/
theorem CountPolysHole_finite {c k m : ℕ} {κ : Fin k → ColKind} {s : String}
    (q : AggQueryIn ℕ c k κ [(s, m)]) (hs : q.inSig {SeqAggFunc.count}) (hh : q.hygienic)
    (hn : q.noMention s) : (CountPolysHole q s m).Finite := by
  have hnm : ∀ p ∈ [(s, m)], q.noMention p.1 := fun p hp => by
    rw [List.mem_singleton.mp hp]; exact hn
  obtain ⟨f, -, hb⟩ := AggQueryIn.exists_polyBound_countTypes
    SeqAggFunc.isCount_count_nat.readsCount q hs hh hnm
  refine (finite_of_eventually_mem (K := (baseSet q.allConsts).card + f (baseSet q.allConsts).card)
    (fun n => ⋃ X : Relation ℕ m, q.countValsAll ((dRep n).assign s X)) (fun n => ?_)).subset
    (fun p ⟨N, hN⟩ => ⟨N, fun n hn => Set.mem_iUnion.mpr (hN n hn)⟩)
  have hν : ∀ ν : ℕ, ValueType.nullVal = some ν → ν ∈ baseSet q.allConsts :=
    fun ν hν => absurd hν (by simp)
  have h0 : (0 : ℕ) ∈ baseSet q.allConsts := Finset.mem_insert_self _ _
  have hD : ∀ p ∈ q.leaves, (p.2, p.1) ∉ [(s, m)] → ∀ r : Relation ℕ p.1,
      (dRep n).find p.1 p.2 = some r → ∀ u, Multiset.Mem r u → ∀ j, u j ∈ baseSet q.allConsts :=
    fun p _ _ r hr u hu j => by
      rw [dRep_vals n hr u hu j]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hc : ∀ a ∈ q.allConsts, a ∈ baseSet q.allConsts :=
    fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)
  refine ⟨Union.union (baseSet q.allConsts) (q.countTypes (baseSet q.allConsts) (dRep n)), ?_, ?_⟩
  · refine Set.iUnion_subset (fun X => ?_)
    refine AggQueryIn.countValsAll_subset SeqAggFunc.isCount_count_nat.readsCount hν h0 q hs hh
      hnm (dRep n) ((dRep n).assign s X) ?_ hD hc
    rintro ⟨k', t⟩ hp hpl
    have hne : ¬ (k' = m ∧ t = s) := fun h => hpl (by
      obtain ⟨rfl, rfl⟩ := h
      exact List.mem_singleton_self _)
    exact Database.find_assign_of_ne s t X (dRep n) hne
  · exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (hb _ _ hν h0 hD hc) _)

end WinRow

/-! ## The invariant's vocabulary -/

namespace WinRow

open Polynomial

noncomputable section

/-- **The values a closed query may write** at a context of polynomials:
its constants, the instance's value, the context, and its counts. -/
def Univ {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)} (q : AggQueryIn ℕ c k κ l)
    (cγ : Fin c → Poly) : Set Poly :=
  Union.union (Union.union (Union.union (Cset q.allConsts) {(1 : Poly)}) (Set.range cγ))
    (CountPolys q)

/-- The same for a term with a hole, its counts taken over every binding. -/
def UnivHole {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)} (q : AggQueryIn ℕ c k κ l)
    (s : String) (m : ℕ) (cγ : Fin c → Poly) : Set Poly :=
  Union.union (Union.union (Union.union (Cset q.allConsts) {(1 : Poly)}) (Set.range cγ))
    (CountPolysHole q s m)

theorem Univ_finite {c k : ℕ} {κ : Fin k → ColKind} (q : AggQueryIn ℕ c k κ)
    (hs : q.inSig {SeqAggFunc.count}) (hh : q.hygienic) (cγ : Fin c → Poly) :
    (Univ q cγ).Finite :=
  (((Cset_finite _).union (Set.finite_singleton _)).union (Set.finite_range _)).union
    (CountPolys_finite q hs hh)

theorem UnivHole_finite {c k m : ℕ} {κ : Fin k → ColKind} {s : String}
    (q : AggQueryIn ℕ c k κ [(s, m)]) (hs : q.inSig {SeqAggFunc.count}) (hh : q.hygienic)
    (hn : q.noMention s) (cγ : Fin c → Poly) : (UnivHole q s m cγ).Finite :=
  (((Cset_finite _).union (Set.finite_singleton _)).union (Set.finite_range _)).union
    (CountPolysHole_finite q hs hh hn)

theorem CountPolys_mono {c k c' k' : ℕ} {κ : Fin k → ColKind} {κ' : Fin k' → ColKind}
    {l l' : List (String × ℕ)} {q : AggQueryIn ℕ c k κ l} {q' : AggQueryIn ℕ c' k' κ' l'}
    (h : ∀ n, q.countValsAll (dRep n) ⊆ q'.countValsAll (dRep n)) : CountPolys q ⊆ CountPolys q' :=
  fun _ ⟨N, hN⟩ => ⟨N, fun n hn => h n (hN n hn)⟩

theorem CountPolysHole_mono {c k c' k' m : ℕ} {κ : Fin k → ColKind} {κ' : Fin k' → ColKind}
    {l l' : List (String × ℕ)} {q : AggQueryIn ℕ c k κ l} {q' : AggQueryIn ℕ c' k' κ' l'}
    {s : String} (h : ∀ n (X : Relation ℕ m),
      q.countValsAll ((dRep n).assign s X) ⊆ q'.countValsAll ((dRep n).assign s X)) :
    CountPolysHole q s m ⊆ CountPolysHole q' s m :=
  fun _ ⟨N, hN⟩ => ⟨N, fun n hn => by
    obtain ⟨X, hX⟩ := hN n hn
    exact ⟨X, h n X hX⟩⟩

/-- A closed query's counts are counts of a term that holds it, over any
binding of the term's hole, when the query does not mention the name. -/
theorem CountPolys_subset_hole {c k m : ℕ} {κ : Fin k → ColKind} (q : AggQueryIn ℕ c k κ)
    {s : String} (hq : q.noMention s) {c' k' : ℕ} {κ' : Fin k' → ColKind}
    {l' : List (String × ℕ)} {q' : AggQueryIn ℕ c' k' κ' l'}
    (h : ∀ n (X : Relation ℕ m), q.countValsAll ((dRep n).assign s X)
      ⊆ q'.countValsAll ((dRep n).assign s X)) : CountPolys q ⊆ CountPolysHole q' s m := by
  rintro p ⟨N, hN⟩
  refine ⟨N, fun n hn => ⟨0, h n 0 ?_⟩⟩
  rw [AggQueryIn.countValsAll_congr_of_noMention q hq (D := (dRep n).assign s (0 : Relation ℕ m))
    (D' := dRep n) (fun k t ht => ?_)]
  · exact hN n hn
  · rcases ht with ht | ht
    · exact Database.find_assign_of_ne s t _ _ (fun h => ht h.2)
    · exact absurd ht List.not_mem_nil

/-- **The invariant for a closed query**: for `n` large its result on the
instance with `n` copies is a bag of shapes, with values in `Univ`, and
whether it settles there does not depend on `n`. -/
def ClosedSym {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)} (q : AggQueryIn ℕ c k κ l)
    (cγ : Fin c → Poly) : Prop :=
  ∃ (N : ℕ) (L : PolyBag k) (b : Prop), PolyBag.vals L ⊆ Univ q cγ ∧ ∀ n ≥ N,
    (q.SettlesAt (dRep n) (ctxAt cγ n) ↔ b)
      ∧ (q.evaluatePlain (dRep n) (ctxAt cγ n) : Multiset (Tuple ℕ k)) = PolyBag.inst L n

/-- **The invariant for a term with a hole**: uniformly in the bag the
hole is bound to, provided its values lie in a given finite set. -/
def BodySym {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)} (q : AggQueryIn ℕ c k κ l)
    (s : String) (m : ℕ) (cγ : Fin c → Poly) (W : Set Poly) : Prop :=
  ∃ N : ℕ, ∀ LX : PolyBag m, PolyBag.vals LX ⊆ W →
    ∃ (L : PolyBag k) (b : Prop), PolyBag.vals L ⊆ Union.union W (UnivHole q s m cγ) ∧ ∀ n ≥ N,
      (q.SettlesAt ((dRep n).assign s (PolyBag.inst LX n)) (ctxAt cγ n) ↔ b)
        ∧ (q.evaluatePlain ((dRep n).assign s (PolyBag.inst LX n)) (ctxAt cγ n)
            : Multiset (Tuple ℕ k)) = PolyBag.inst L n

/-! ### Bag lemmas the cases need -/

theorem PolyBag.vals_append {k : ℕ} (L₁ L₂ : PolyBag k) :
    PolyBag.vals (L₁ ++ L₂) ⊆ Union.union (PolyBag.vals L₁) (PolyBag.vals L₂) := by
  rintro p ⟨s, hs, j, rfl⟩
  rcases List.mem_append.mp hs with h | h
  · exact Or.inl ⟨s, h, j, rfl⟩
  · exact Or.inr ⟨s, h, j, rfl⟩

theorem PolyBag.vals_filter {k : ℕ} (P : Shape k → Bool) (L : PolyBag k) :
    PolyBag.vals (L.filter P) ⊆ PolyBag.vals L := by
  rintro p ⟨s, hs, j, rfl⟩
  exact ⟨s, List.mem_of_mem_filter hs, j, rfl⟩

theorem PolyBag.vals_scale {k : ℕ} (m : Poly) (L : PolyBag k) :
    PolyBag.vals (PolyBag.scale m L) ⊆ PolyBag.vals L := by
  rintro p ⟨s, hs, j, rfl⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact ⟨t, ht, j, rfl⟩

theorem PolyBag.vals_mapRows {k k' : ℕ} (f : (Fin k → Poly) → (Fin k' → Poly)) (L : PolyBag k)
    (V : Set Poly) (hf : ∀ s ∈ L, ∀ j, f s.row j ∈ V) : PolyBag.vals (PolyBag.mapRows f L) ⊆ V := by
  rintro p ⟨s, hs, j, rfl⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact hf t ht j

theorem PolyBag.vals_bindShapes {k₁ k₂ : ℕ} (L₁ : PolyBag k₁) (F : Shape k₁ → PolyBag k₂)
    (V : Set Poly) (h₁ : PolyBag.vals L₁ ⊆ V) (h₂ : ∀ s ∈ L₁, PolyBag.vals (F s) ⊆ V) :
    PolyBag.vals (PolyBag.bindShapes L₁ F) ⊆ V := by
  rintro p ⟨u, hu, j, rfl⟩
  obtain ⟨s, hs, hu⟩ := List.mem_flatMap.mp hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
  show Fin.append s.row t.row j ∈ V
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]; exact h₁ ⟨s, hs, i, rfl⟩
  · rw [Fin.append_right]; exact h₂ s hs ⟨t, ht, i, rfl⟩

/-- Every multiplicity is the zero polynomial: the bag is empty at every `n ≥ 1`. -/
def PolyBag.allZero {k : ℕ} (L : PolyBag k) : Prop := ∀ s ∈ L, s.mult = 0

theorem PolyBag.inst_eq_zero_iff {k : ℕ} (L : PolyBag k) {n : ℕ} (hn : 1 ≤ n) :
    PolyBag.inst L n = 0 ↔ PolyBag.allZero L := by
  constructor
  · intro h s hs
    by_contra hm
    have hmem : s.rowAt n ∈ PolyBag.inst L n :=
      PolyBag.mem_inst.mpr ⟨s, hs, (not_congr (Poly.eval_eq_zero_iff hn)).mpr hm, rfl⟩
    rw [h] at hmem
    exact Multiset.notMem_zero _ hmem
  · intro h
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro u hu
    obtain ⟨s, hs, hm, -⟩ := PolyBag.mem_inst.mp hu
    exact hm ((Poly.eval_eq_zero_iff hn).mpr (h s hs))

/-- A bag of single copies is the list of its rows. -/
theorem PolyBag.inst_of_ones {k : ℕ} (L : PolyBag k) (h : ∀ s ∈ L, s.mult = 1) (n : ℕ) :
    PolyBag.inst L n = (L.map (fun s => s.rowAt n) : Multiset (Tuple ℕ k)) := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    rw [PolyBag.inst_cons, ih (fun t ht => h t (List.mem_cons_of_mem _ ht)), List.map_cons,
      ← Multiset.cons_coe]
    unfold Shape.inst
    rw [h s List.mem_cons_self, Polynomial.eval_one, Multiset.replicate_one]
    rfl

/-- Multiplicities after a filter: the shapes the row test keeps. -/
theorem PolyBag.card_filter_inst {k : ℕ} (p : Tuple ℕ k → Prop) [DecidablePred p] (L : PolyBag k)
    (n : ℕ) :
    Multiset.card ((PolyBag.inst L n).filter p)
      = (L.map (fun s => if p (s.rowAt n) then s.mult.eval n else 0)).sum := by
  induction L with
  | nil => simp [PolyBag.inst]
  | cons s L ih =>
    rw [PolyBag.inst_cons, Multiset.filter_add, Multiset.card_add, ih, List.map_cons, List.sum_cons]
    congr 1
    unfold Shape.inst
    rw [Multiset.filter_replicate]
    split <;> simp

theorem Poly.eval_list_sum (L : List Poly) (n : ℕ) : (L.sum).eval n = (L.map
    (fun p => p.eval n)).sum := by
  induction L with
  | nil => simp
  | cons p L ih => rw [List.sum_cons, Polynomial.eval_add, ih, List.map_cons, List.sum_cons]

/-- **Duplicate elimination at the threshold**: one copy of each row the
shapes of non-zero multiplicity have at `N`, the last of them kept. -/
def dedupAt {k : ℕ} (N : ℕ) : PolyBag k → PolyBag k
  | [] => []
  | s :: L =>
      if s.mult = 0 ∨ ∃ t ∈ L, t.mult ≠ 0 ∧ t.rowAt N = s.rowAt N then dedupAt N L
      else ⟨1, s.row⟩ :: dedupAt N L

theorem dedupAt_mult {k : ℕ} (N : ℕ) (L : PolyBag k) : ∀ t ∈ dedupAt N L, t.mult = 1 := by
  induction L with
  | nil => exact fun t ht => absurd ht List.not_mem_nil
  | cons s L ih =>
    intro t ht
    unfold dedupAt at ht
    split at ht
    · exact ih t ht
    · rcases List.mem_cons.mp ht with rfl | ht
      · rfl
      · exact ih t ht

theorem dedupAt_sub {k : ℕ} (N : ℕ) (L : PolyBag k) :
    ∀ t ∈ dedupAt N L, ∃ s ∈ L, s.mult ≠ 0 ∧ t.row = s.row := by
  induction L with
  | nil => exact fun t ht => absurd ht List.not_mem_nil
  | cons s L ih =>
    intro t ht
    unfold dedupAt at ht
    split at ht
    · obtain ⟨s', hs', hm, hr⟩ := ih t ht
      exact ⟨s', List.mem_cons_of_mem _ hs', hm, hr⟩
    · next h =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨s, List.mem_cons_self, fun h0 => h (Or.inl h0), rfl⟩
      · obtain ⟨s', hs', hm, hr⟩ := ih t ht
        exact ⟨s', List.mem_cons_of_mem _ hs', hm, hr⟩

theorem dedupAt_cover {k : ℕ} (N : ℕ) (L : PolyBag k) :
    ∀ s ∈ L, s.mult ≠ 0 → ∃ t ∈ dedupAt N L, t.rowAt N = s.rowAt N := by
  induction L with
  | nil => exact fun s hs => absurd hs List.not_mem_nil
  | cons s L ih =>
    intro s' hs' hm
    unfold dedupAt
    split
    · next h =>
      rcases List.mem_cons.mp hs' with rfl | hs'
      · rcases h with h | ⟨t, ht, htm, htr⟩
        · exact absurd h hm
        · obtain ⟨t', ht', hr⟩ := ih t ht htm
          exact ⟨t', ht', hr.trans htr⟩
      · exact ih s' hs' hm
    · next h =>
      rcases List.mem_cons.mp hs' with rfl | hs'
      · exact ⟨⟨1, s'.row⟩, List.mem_cons_self, rfl⟩
      · obtain ⟨t', ht', hr⟩ := ih s' hs' hm
        exact ⟨t', List.mem_cons_of_mem _ ht', hr⟩

theorem dedupAt_nodup {k : ℕ} (N : ℕ) (L : PolyBag k) :
    ((dedupAt N L).map (fun t => t.rowAt N)).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons s L ih =>
    unfold dedupAt
    split
    · exact ih
    · next h =>
      rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hmem => h ?_, ih⟩
      obtain ⟨t, ht, hr⟩ := List.mem_map.mp hmem
      obtain ⟨s', hs', hm, hr'⟩ := dedupAt_sub N L t ht
      refine Or.inr ⟨s', hs', hm, ?_⟩
      have e : s'.rowAt N = t.rowAt N := by unfold Shape.rowAt; rw [hr']
      exact e.trans hr

theorem dedupAt_vals {k : ℕ} (N : ℕ) (L : PolyBag k) :
    PolyBag.vals (dedupAt N L) ⊆ PolyBag.vals L := by
  rintro p ⟨t, ht, j, rfl⟩
  obtain ⟨s, hs, -, hr⟩ := dedupAt_sub N L t ht
  exact ⟨s, hs, j, by rw [hr]⟩

/-- **Duplicate elimination commutes with instantiation** from the
threshold on. -/
theorem inst_dedupAt {k : ℕ} {V : Set Poly} {N : ℕ} (hV : Decided V N) (L : PolyBag k)
    (hL : PolyBag.vals L ⊆ V) {n : ℕ} (hn : N ≤ n) (h1 : 1 ≤ n) :
    (PolyBag.inst L n).dedup = PolyBag.inst (dedupAt N L) n := by
  have hrows : ∀ s ∈ L, ∀ j, s.row j ∈ V := fun s hs j => hL ⟨s, hs, j, rfl⟩
  have hrows' : ∀ t ∈ dedupAt N L, ∀ j, t.row j ∈ V :=
    fun t ht j => hL (dedupAt_vals N L ⟨t, ht, j, rfl⟩)
  have hshift : ∀ s t : Shape k, (∀ j, s.row j ∈ V) → (∀ j, t.row j ∈ V) →
      (s.rowAt n = t.rowAt n ↔ s.rowAt N = t.rowAt N) :=
    fun s t hs ht => Shape.rowAt_eq_shift hV hs ht hn
  rw [PolyBag.inst_of_ones (dedupAt N L) (dedupAt_mult N L) n]
  refine (Multiset.Nodup.ext (Multiset.nodup_dedup _) ?_).mpr (fun u => ?_)
  · rw [Multiset.coe_nodup]
    have hN := dedupAt_nodup N L
    refine List.Nodup.map_on (fun t ht t' ht' he => ?_) (hN.of_map _)
    refine List.inj_on_of_nodup_map hN ht ht' ?_
    exact (hshift t t' (hrows' t ht) (hrows' t' ht')).mp he
  · rw [Multiset.mem_dedup, PolyBag.mem_inst, Multiset.mem_coe, List.mem_map]
    constructor
    · rintro ⟨s', hs', hm, rfl⟩
      obtain ⟨t, ht, hr⟩ := dedupAt_cover N L s' hs' ((not_congr (Poly.eval_eq_zero_iff h1)).mp hm)
      exact ⟨t, ht, (hshift t s' (hrows' t ht) (hrows s' hs')).mpr hr⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨s', hs', hm, hr⟩ := dedupAt_sub N L t ht
      refine ⟨s', hs', (not_congr (Poly.eval_eq_zero_iff h1)).mpr hm, ?_⟩
      unfold Shape.rowAt
      rw [hr]

/-- The rows of a bag of multiplicity one at `n` are its rows at `N`,
carried by the shift, so that the nodup list of its rows at `N` gives
the one at `n`. -/
theorem nodup_rows_shift {k : ℕ} {V : Set Poly} {N : ℕ} (hV : Decided V N) (L : PolyBag k)
    (hL : PolyBag.vals L ⊆ V) (hnd : (L.map (fun t => t.rowAt N)).Nodup) {n : ℕ} (hn : N ≤ n) :
    (L.map (fun t => t.rowAt n)).Nodup := by
  rw [List.Nodup, List.pairwise_map] at hnd ⊢
  refine hnd.imp_of_mem (fun {a b} ha hb h he => h ?_)
  exact (Shape.rowAt_eq_shift hV (fun j => hL ⟨a, ha, j, rfl⟩) (fun j => hL ⟨b, hb, j, rfl⟩)
    hn).mp he

/-- **Two duplicate-free bags agree at `n` iff they agree at the
threshold**: both are sets of rows, and the shift carries a row of one
to a row of the other. -/
theorem inst_eq_iff_shift {k : ℕ} {V : Set Poly} {N : ℕ} (hV : Decided V N) (L L' : PolyBag k)
    (hL : PolyBag.vals L ⊆ V) (hL' : PolyBag.vals L' ⊆ V)
    (h1 : ∀ s ∈ L, s.mult = 1) (h1' : ∀ s ∈ L', s.mult = 1)
    (hnd : (L.map (fun t => t.rowAt N)).Nodup) (hnd' : (L'.map (fun t => t.rowAt N)).Nodup)
    {n : ℕ} (hn : N ≤ n) :
    (PolyBag.inst L n = PolyBag.inst L' n) ↔ (PolyBag.inst L N = PolyBag.inst L' N) := by
  have key : ∀ m, N ≤ m → ((PolyBag.inst L m = PolyBag.inst L' m)
      ↔ (∀ s ∈ L, ∃ s' ∈ L', s.rowAt N = s'.rowAt N)
        ∧ (∀ s' ∈ L', ∃ s ∈ L, s'.rowAt N = s.rowAt N)) := by
    intro m hm
    rw [PolyBag.inst_of_ones L h1 m, PolyBag.inst_of_ones L' h1' m,
      Multiset.Nodup.ext (Multiset.coe_nodup.mpr (nodup_rows_shift hV L hL hnd hm))
        (Multiset.coe_nodup.mpr (nodup_rows_shift hV L' hL' hnd' hm))]
    simp only [Multiset.mem_coe, List.mem_map]
    constructor
    · intro h
      refine ⟨fun s hs => ?_, fun s' hs' => ?_⟩
      · obtain ⟨s', hs', he⟩ := (h (s.rowAt m)).mp ⟨s, hs, rfl⟩
        exact ⟨s', hs', (Shape.rowAt_eq_shift hV (fun j => hL ⟨s, hs, j, rfl⟩)
          (fun j => hL' ⟨s', hs', j, rfl⟩) hm).mp he.symm⟩
      · obtain ⟨s, hs, he⟩ := (h (s'.rowAt m)).mpr ⟨s', hs', rfl⟩
        exact ⟨s, hs, (Shape.rowAt_eq_shift hV (fun j => hL' ⟨s', hs', j, rfl⟩)
          (fun j => hL ⟨s, hs, j, rfl⟩) hm).mp he.symm⟩
    · rintro ⟨h₁, h₂⟩ u
      constructor
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨s', hs', he⟩ := h₁ s hs
        exact ⟨s', hs', ((Shape.rowAt_eq_shift hV (fun j => hL' ⟨s', hs', j, rfl⟩)
          (fun j => hL ⟨s, hs, j, rfl⟩) hm).mpr he.symm)⟩
      · rintro ⟨s', hs', rfl⟩
        obtain ⟨s, hs, he⟩ := h₂ s' hs'
        exact ⟨s, hs, ((Shape.rowAt_eq_shift hV (fun j => hL ⟨s, hs, j, rfl⟩)
          (fun j => hL' ⟨s', hs', j, rfl⟩) hm).mpr he.symm)⟩
  rw [key n hn, key N (le_refl N)]

end

end WinRow

/-! ## Universe bookkeeping -/

namespace WinRow

open Polynomial

noncomputable section

theorem range_append_subset {k₁ k₂ : ℕ} (r : Fin k₁ → Poly) (cγ : Fin k₂ → Poly) :
    Set.range (Fin.append r cγ) ⊆ Union.union (Set.range r) (Set.range cγ) := by
  rintro p ⟨j, rfl⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]; exact Or.inl ⟨i, rfl⟩
  · rw [Fin.append_right]; exact Or.inr ⟨i, rfl⟩

theorem Univ_mono {c k k' : ℕ} {κ : Fin k → ColKind} {κ' : Fin k' → ColKind}
    {l l' : List (String × ℕ)} {q : AggQueryIn ℕ c k κ l} {q' : AggQueryIn ℕ c k' κ' l'}
    (hc : q'.allConsts ⊆ q.allConsts)
    (hcv : ∀ n, q'.countValsAll (dRep n) ⊆ q.countValsAll (dRep n)) (cγ : Fin c → Poly) :
    Univ q' cγ ⊆ Univ q cγ := by
  rintro p (((h | h) | h) | h)
  · exact Or.inl (Or.inl (Or.inl (Cset_mono hc h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (CountPolys_mono hcv h)

theorem UnivHole_mono {c k k' m : ℕ} {κ : Fin k → ColKind} {κ' : Fin k' → ColKind}
    {l l' : List (String × ℕ)} {q : AggQueryIn ℕ c k κ l} {q' : AggQueryIn ℕ c k' κ' l'}
    {s : String} (hc : q'.allConsts ⊆ q.allConsts)
    (hcv : ∀ n (X : Relation ℕ m), q'.countValsAll ((dRep n).assign s X)
      ⊆ q.countValsAll ((dRep n).assign s X)) (cγ : Fin c → Poly) :
    UnivHole q' s m cγ ⊆ UnivHole q s m cγ := by
  rintro p (((h | h) | h) | h)
  · exact Or.inl (Or.inl (Or.inl (Cset_mono hc h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (CountPolysHole_mono hcv h)

/-- A closed query's universe lies in that of a term holding it. -/
theorem Univ_subset_hole {c k k' m : ℕ} {κ : Fin k → ColKind} {κ' : Fin k' → ColKind}
    {l : List (String × ℕ)} {q : AggQueryIn ℕ c k κ l} (q' : AggQueryIn ℕ c k' κ') {s : String}
    (hq' : q'.noMention s) (hc : q'.allConsts ⊆ q.allConsts)
    (hcv : ∀ n (X : Relation ℕ m), q'.countValsAll ((dRep n).assign s X)
      ⊆ q.countValsAll ((dRep n).assign s X)) (cγ : Fin c → Poly) :
    Univ q' cγ ⊆ UnivHole q s m cγ := by
  rintro p (((h | h) | h) | h)
  · exact Or.inl (Or.inl (Or.inl (Cset_mono hc h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (CountPolys_subset_hole q' hq' hcv h)

theorem one_mem_Univ {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) (cγ : Fin c → Poly) : (1 : Poly) ∈ Univ q cγ :=
  Or.inl (Or.inl (Or.inr rfl))

theorem range_subset_Univ {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) (cγ : Fin c → Poly) : Set.range cγ ⊆ Univ q cγ :=
  fun _ h => Or.inl (Or.inr h)

theorem Cset_subset_Univ {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) (cγ : Fin c → Poly) : Cset q.allConsts ⊆ Univ q cγ :=
  fun _ h => Or.inl (Or.inl (Or.inl h))

theorem one_mem_UnivHole {c k m : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) (s : String) (cγ : Fin c → Poly) :
    (1 : Poly) ∈ UnivHole q s m cγ :=
  Or.inl (Or.inl (Or.inr rfl))

theorem range_subset_UnivHole {c k m : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) (s : String) (cγ : Fin c → Poly) :
    Set.range cγ ⊆ UnivHole q s m cγ :=
  fun _ h => Or.inl (Or.inr h)

theorem Cset_subset_UnivHole {c k m : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn ℕ c k κ l) (s : String) (cγ : Fin c → Poly) :
    Cset q.allConsts ⊆ UnivHole q s m cγ :=
  fun _ h => Or.inl (Or.inl (Or.inl h))

/-- A closed query not mentioning the name reads the bound instance as the
instance. -/
theorem settlesAt_assign_iff {c k : ℕ} {κ : Fin k → ColKind} (q : AggQueryIn ℕ c k κ)
    {s : String} (hq : q.noMention s) {m : ℕ} (X : Relation ℕ m) (D : Database ℕ) (γ : Fin c → ℕ) :
    q.SettlesAt (D.assign s X) γ ↔ q.SettlesAt D γ :=
  ⟨AggQueryIn.settlesAt_assign_of_noMention X q hq D γ,
    AggQueryIn.settlesAt_of_noMention q hq (fun _ t ht => (Database.find_assign_of_ne s t X D
      (fun h => (ht.resolve_right List.not_mem_nil) h.2)).symm) γ⟩

/-- The context an apply's right side reads, at `n`. -/
theorem ctxAt_append {c n₁ : ℕ} (r : Fin n₁ → Poly) (cγ : Fin c → Poly) (n : ℕ) :
    (Fin.append (fun j => (r j).eval n) (ctxAt cγ n) : Fin (n₁ + c) → ℕ)
      = ctxAt (Fin.append r cγ) n := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · show Fin.append _ _ (Fin.castAdd c i) = (Fin.append r cγ (Fin.castAdd c i)).eval n
    rw [Fin.append_left, Fin.append_left]
  · show Fin.append _ _ (Fin.natAdd n₁ i) = (Fin.append r cγ (Fin.natAdd n₁ i)).eval n
    rw [Fin.append_right, Fin.append_right]
    rfl

/-! ### Counting the rows of a bag -/

theorem PolyBag.card_inst {k : ℕ} (L : PolyBag k) (n : ℕ) :
    Multiset.card (PolyBag.inst L n) = (L.map (fun s => s.mult.eval n)).sum := by
  induction L with
  | nil => simp [PolyBag.inst]
  | cons s L ih =>
    rw [PolyBag.inst_cons, Multiset.card_add, ih, List.map_cons, List.sum_cons]
    unfold Shape.inst
    rw [Multiset.card_replicate]

/-- A conditional sum of multiplicities is the multiplicity sum of the
shapes the condition keeps. -/
theorem sum_if_eq_filter {k : ℕ} (L : PolyBag k) (P : Shape k → Bool) (n : ℕ) :
    (L.map (fun s => if P s = true then s.mult.eval n else 0)).sum
      = (((L.filter P).map Shape.mult).sum).eval n := by
  induction L with
  | nil => simp
  | cons s L ih =>
    rw [List.map_cons, List.sum_cons, ih]
    by_cases hs : P s = true
    · rw [ite_eq_left hs, List.filter_cons_of_pos hs, List.map_cons, List.sum_cons,
        Polynomial.eval_add]
    · rw [ite_eq_right hs, List.filter_cons_of_neg hs, zero_add]

/-- A count over a bag is its number of rows. -/
theorem count_onBag_eq_card (hsym : SeqAggFunc.count.Symmetric) (M : Multiset ℕ) :
    SeqAggFunc.count.onBag hsym M = Multiset.card M := by
  induction M using Quot.inductionOn with
  | h L => rfl

theorem Shape.rowAt_key {k n₁ : ℕ} (is : Tuple (Fin k) n₁) (s : Shape k) (n : ℕ) :
    Tuple.key is (s.rowAt n) = (⟨s.mult, Tuple.key is s.row⟩ : Shape n₁).rowAt n := rfl

theorem PolyBag.vals_mapRows_key {k n₁ : ℕ} (is : Tuple (Fin k) n₁) (L : PolyBag k) :
    PolyBag.vals (PolyBag.mapRows (Tuple.key is) L) ⊆ PolyBag.vals L :=
  PolyBag.vals_mapRows _ L _ (fun s hs j => ⟨s, hs, is j, rfl⟩)

end

end WinRow

/-! ## The invariant -/

namespace WinRow

open Polynomial

/-- **Every window-free query of the minimal universe writes, on the
instance with `n` copies, a bag of shapes for `n` large**, and settles or
not independently of `n`: the closed statement, and the statement for a
term with a hole, uniform in the bag the hole is bound to. -/
theorem sym_aux {S : Set OpKind} (hwin : OpKind.win ∉ S) :
    ∀ {c k : ℕ} {κ : Fin k → ColKind} {l : List (String × ℕ)} (q : AggQueryIn ℕ c k κ l),
      q.usesOnly S → q.inSig {SeqAggFunc.count} → q.hygienic →
      (l = [] → ∀ cγ : Fin c → Poly, ClosedSym q cγ)
      ∧ (∀ (s : String) (m : ℕ), l = [(s, m)] → q.noMention s →
          ∀ (cγ : Fin c → Poly) (W : Set Poly), W.Finite → BodySym q s m cγ W) := by
  classical
  intro c k κ l q
  induction q with
  | Rel k t =>
    refine fun _ _ _ => ⟨fun _ cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    by_cases h : k = 1 ∧ t = "R"
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, [⟨Polynomial.X, fun _ => 1⟩], True, ?_, fun n _ => ⟨Iff.rfl, ?_⟩⟩
      · rintro p ⟨s, hs, j, rfl⟩
        rw [List.mem_singleton.mp hs]
        exact one_mem_Univ _ _
      · rw [AggQueryIn.evaluatePlain, find_dRep]
        show Multiset.replicate n ![1] = PolyBag.inst [⟨Polynomial.X, fun _ => 1⟩] n
        rw [PolyBag.inst_cons, PolyBag.inst_nil, add_zero]
        unfold Shape.inst
        rw [Polynomial.eval_X]
        congr 1
        funext j
        simp [Shape.rowAt, Fin.fin_one_eq_zero j]
    · refine ⟨0, [], True, fun _ ⟨_, hs, _⟩ => absurd hs List.not_mem_nil, fun n _ => ⟨Iff.rfl, ?_⟩⟩
      rw [AggQueryIn.evaluatePlain, find_dRep_ne n h]
      rfl
  | Hole k t =>
    refine fun _ _ _ => ⟨fun hl => absurd hl (by simp), fun s m hl _ cγ W _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
    refine ⟨0, fun LX hLX => ⟨LX, True, fun p hp => Or.inl (hLX hp), fun n _ => ⟨Iff.rfl, ?_⟩⟩⟩
    rw [AggQueryIn.evaluatePlain, Database.find_assign]
  | Param pv ρ =>
    refine fun _ _ _ => ⟨fun _ cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    refine ⟨0, [⟨1, fun j => _root_.Sum.elim (fun a => (Polynomial.C a : Poly)) cγ (pv j)⟩],
      True, ?_, fun n _ => ⟨Iff.rfl, ?_⟩⟩
    · rintro p ⟨s, hs, j, rfl⟩
      rw [List.mem_singleton.mp hs]
      show _root_.Sum.elim (fun a => (Polynomial.C a : Poly)) cγ (pv j) ∈ Univ _ cγ
      cases hk : pv j with
      | inl a =>
        exact Or.inl (Or.inl (Or.inl (mem_Cset (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_univ _, by rw [hk]; exact Finset.mem_singleton_self a⟩))))
      | inr i => exact range_subset_Univ _ cγ ⟨i, rfl⟩
    · simp only [AggQueryIn.evaluatePlain]
      rw [PolyBag.inst_cons, PolyBag.inst_nil, add_zero]
      unfold Shape.inst
      rw [Polynomial.eval_one, Multiset.replicate_one]
      refine congrArg (fun u => ({u} : Multiset (Tuple ℕ _))) (funext fun j => ?_)
      simp only [Shape.rowAt]
      cases pv j with
      | inl a => simp
      | inr i => rfl
  | Empty =>
    refine fun _ _ _ => ⟨fun _ cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    exact ⟨0, [], True, fun _ ⟨_, hs, _⟩ => absurd hs List.not_mem_nil, fun n _ => ⟨Iff.rfl, rfl⟩⟩
  | Proj ps q ih =>
    rename_i c' m' n' κ' l'
    intro hq hs hh
    have hval : ∀ (L : PolyBag m') (cγ : Fin c' → Poly) (n : ℕ) (D : Database ℕ),
        ((q.evaluatePlain D (ctxAt cγ n) : Multiset (Tuple ℕ m')) = PolyBag.inst L n) →
        ((AggQueryIn.Proj ps q).evaluatePlain D (ctxAt cγ n) : Multiset (Tuple ℕ n'))
          = PolyBag.inst (PolyBag.mapRows (fun row => fun j => ProjColIn.polyOf
              (ps j) row cγ) L) n := by
      intro L cγ n D hL
      simp only [AggQueryIn.evaluatePlain]
      rw [hL]
      exact PolyBag.inst_mapRows _ _ L n (fun s _ => funext (fun j =>
        ProjColIn.evalPlain_polyOf (ps j) (hs.1 j) s cγ n))
    have hvals : ∀ (L : PolyBag m') (cγ : Fin c' → Poly) (V : Set Poly), PolyBag.vals L ⊆ V →
        PolyBag.vals (PolyBag.mapRows (fun row => fun j => ProjColIn.polyOf (ps j) row cγ) L)
          ⊆ Union.union (Union.union (Cset (Finset.univ.biUnion (fun j => (ps j).consts))) V)
            (Set.range cγ) := by
      intro L cγ V hV
      refine PolyBag.vals_mapRows _ L _ (fun s hs' j => ?_)
      rcases ProjColIn.polyOf_mem (ps j) (hs.1 j) s.row cγ with (h | ⟨i, hi⟩) | h
      · exact Or.inl (Or.inl (Cset_mono (Finset.subset_biUnion_of_mem _ (Finset.mem_univ j)) h))
      · exact Or.inl (Or.inr (hV ⟨s, hs', i, hi⟩))
      · exact Or.inr h
    refine ⟨fun hl cγ => ?_, fun s m hl hn cγ W hW => ?_⟩
    · obtain ⟨N, L, b, hv, h⟩ := (ih hq.2 hs.2 hh).1 hl cγ
      refine ⟨N, _, b, ?_, fun n hn => ⟨(h n hn).1, hval L cγ n _ (h n hn).2⟩⟩
      refine subset_trans (hvals L cγ _ hv) ?_
      rintro p ((h | h) | h)
      · exact Cset_subset_Univ _ _ (Cset_mono (by exact Finset.subset_union_left) h)
      · exact Univ_mono (q := AggQueryIn.Proj ps q) (q' := q) (by exact Finset.subset_union_right)
          (fun _ => subset_refl _) cγ h
      · exact range_subset_Univ _ _ h
    · obtain ⟨N, hN⟩ := (ih hq.2 hs.2 hh).2 s m hl hn cγ W hW
      refine ⟨N, fun LX hLX => ?_⟩
      obtain ⟨L, b, hv, h⟩ := hN LX hLX
      refine ⟨_, b, ?_, fun n hn => ⟨(h n hn).1, hval L cγ n _ (h n hn).2⟩⟩
      refine subset_trans (hvals L cγ _ hv) ?_
      rintro p ((h | h) | h)
      · exact Or.inr (Cset_subset_UnivHole _ _ _ (Cset_mono (by exact Finset.subset_union_left) h))
      · exact h.imp_right (fun hp => UnivHole_mono (q := AggQueryIn.Proj ps q) (q' := q)
          (by exact Finset.subset_union_right) (fun _ _ => subset_refl _) cγ hp)
      · exact Or.inr (range_subset_UnivHole _ _ _ h)
  | Sel φ q hφ ih =>
    rename_i c' n' κ' l'
    intro hq hs hh
    -- the selection keeps the shapes whose predicate holds at the threshold
    have hval : ∀ (L : PolyBag n') (cγ : Fin c' → Poly) (V : Set Poly) (N : ℕ), Decided V N →
        PolyBag.vals L ⊆ V → Cset φ.consts ⊆ V → Set.range cγ ⊆ V → ∀ n ≥ N,
        ∀ (D : Database ℕ),
        ((q.evaluatePlain D (ctxAt cγ n) : Multiset (Tuple ℕ n')) = PolyBag.inst L n) →
        ((AggQueryIn.Sel φ q).evaluatePlain D (ctxAt cγ n) : Multiset (Tuple ℕ n'))
          = PolyBag.inst (L.filter (fun s => decide (φ.holdsPlain (s.rowAt N)
              (ctxAt cγ N)))) n := by
      intro L cγ V N hV hL hc hγ n hn D hD
      simp only [AggQueryIn.evaluatePlain]
      rw [hD]
      refine PolyBag.inst_filter _ _ _ L n (fun s hs' => ?_)
      rw [decide_eq_true_iff]
      exact GenPredIn.holdsPlain_shift φ hs.1 hV hc (fun j => hL ⟨s, hs', j, rfl⟩)
        (fun j => hγ ⟨j, rfl⟩) hn
    refine ⟨fun hl cγ => ?_, fun s m hl hn cγ W hW => ?_⟩
    · obtain ⟨N, L, b, hv, h⟩ := (ih hq.2 hs.2 hh).1 hl cγ
      obtain ⟨Nd, hNd⟩ := exists_decided (((PolyBag.vals_finite L).union
          (Cset_finite φ.consts)).union
        (Set.finite_range cγ))
      refine ⟨max N Nd, L.filter (fun s => decide (φ.holdsPlain (s.rowAt (max N Nd))
        (ctxAt cγ (max N Nd)))), b, ?_, fun n hn => ⟨(h n (le_trans (le_max_left _ _) hn)).1, ?_⟩⟩
      · refine subset_trans (PolyBag.vals_filter _ L) (subset_trans hv ?_)
        exact Univ_mono (q := AggQueryIn.Sel φ q hφ) (q' := q) (by exact Finset.subset_union_right)
          (fun _ => subset_refl _) cγ
      · exact hval L cγ _ (max N Nd) (hNd.mono (le_max_right _ _))
          (fun p hp => Or.inl (Or.inl hp)) (fun p hp => Or.inl (Or.inr hp))
          (fun p hp => Or.inr hp) n hn _ (h n (le_trans (le_max_left _ _) hn)).2
    · subst hl
      obtain ⟨N, hN⟩ := (ih hq.2 hs.2 hh).2 s m rfl hn cγ W hW
      obtain ⟨Nd, hNd⟩ := exists_decided (((hW.union (UnivHole_finite q hs.2 hh
        (show q.noMention s from hn) cγ)).union (Cset_finite φ.consts)).union (Set.finite_range cγ))
      refine ⟨max N Nd, fun LX hLX => ?_⟩
      obtain ⟨L, b, hv, h⟩ := hN LX hLX
      refine ⟨L.filter (fun s => decide (φ.holdsPlain (s.rowAt (max N Nd)) (ctxAt cγ (max N Nd)))),
        b, ?_, fun n hn => ⟨(h n (le_trans (le_max_left _ _) hn)).1, ?_⟩⟩
      · refine subset_trans (PolyBag.vals_filter _ L) (subset_trans hv ?_)
        exact Set.union_subset_union_right W (UnivHole_mono (q := AggQueryIn.Sel φ q hφ) (q' := q)
          (by exact Finset.subset_union_right) (fun _ _ => subset_refl _) cγ)
      · exact hval L cγ _ (max N Nd) (hNd.mono (le_max_right _ _))
          (fun p hp => Or.inl (Or.inl (hv hp))) (fun p hp => Or.inl (Or.inr hp))
          (fun p hp => Or.inr hp) n hn _ (h n (le_trans (le_max_left _ _) hn)).2
  | Prod q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l₁ l₂
    intro hq hs hh
    have hval : ∀ (L₁ : PolyBag n₁) (L₂ : PolyBag n₂) (D : Database ℕ) (γ : Fin c' → ℕ) (n : ℕ),
        ((q₁.evaluatePlain D γ : Multiset (Tuple ℕ n₁)) = PolyBag.inst L₁ n) →
        ((q₂.evaluatePlain D γ : Multiset (Tuple ℕ n₂)) = PolyBag.inst L₂ n) →
        ((AggQueryIn.Prod q₁ q₂).evaluatePlain D γ : Multiset (Tuple ℕ (n₁ + n₂)))
          = PolyBag.inst (PolyBag.bindShapes L₁ (fun _ => L₂)) n := by
      intro L₁ L₂ D γ n h₁ h₂
      rw [AggQueryIn.evaluatePlain, Relation.hMul_eq_bind, h₁, h₂]
      exact PolyBag.inst_bindShapes L₁ (fun _ => L₂) (fun _ => PolyBag.inst L₂ n) n
        (fun _ _ _ => rfl)
    refine ⟨fun hl cγ => ?_, fun s m hl hn cγ W hW => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      obtain ⟨N₁, L₁, b₁, hv₁, h₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).1 hl₁ cγ
      obtain ⟨N₂, L₂, b₂, hv₂, h₂⟩ := (ih₂ hq.2.2 hs.2 hh.2).1 hl₂ cγ
      refine ⟨max N₁ N₂, PolyBag.bindShapes L₁ (fun _ => L₂), b₁ ∧ b₂, ?_, fun n hn => ?_⟩
      · refine PolyBag.vals_bindShapes L₁ _ _ (subset_trans hv₁ ?_) (fun _ _ => subset_trans hv₂ ?_)
        · exact Univ_mono (q := AggQueryIn.Prod q₁ q₂) (q' := q₁)
            (by exact Finset.subset_union_left) (fun _ => Set.subset_union_left) cγ
        · exact Univ_mono (q := AggQueryIn.Prod q₁ q₂) (q' := q₂)
            (by exact Finset.subset_union_right) (fun _ => Set.subset_union_right) cγ
      · refine ⟨and_congr (h₁ n (le_trans (le_max_left _ _) hn)).1
          (h₂ n (le_trans (le_max_right _ _) hn)).1, ?_⟩
        exact hval L₁ L₂ _ _ n (h₁ n (le_trans (le_max_left _ _) hn)).2
          (h₂ n (le_trans (le_max_right _ _) hn)).2
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁; subst hl₂
        obtain ⟨N₁, hN₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).2 s m rfl hn.1 cγ W hW
        obtain ⟨N₂, L₂, b₂, hv₂, h₂⟩ := (ih₂ hq.2.2 hs.2 hh.2).1 rfl cγ
        refine ⟨max N₁ N₂, fun LX hLX => ?_⟩
        obtain ⟨L₁, b₁, hv₁, h₁⟩ := hN₁ LX hLX
        refine ⟨PolyBag.bindShapes L₁ (fun _ => L₂), b₁ ∧ b₂, ?_, fun n hn' => ?_⟩
        · refine PolyBag.vals_bindShapes L₁ _ _ (subset_trans hv₁ ?_)
            (fun _ _ => subset_trans hv₂ (fun p hp => Or.inr ?_))
          · exact Set.union_subset_union_right W (UnivHole_mono (q := AggQueryIn.Prod q₁ q₂)
              (q' := q₁) (by exact Finset.subset_union_left) (fun _ _ => Set.subset_union_left) cγ)
          · exact Univ_subset_hole (q := AggQueryIn.Prod q₁ q₂) q₂ hn.2
              (by exact Finset.subset_union_right) (fun _ _ => Set.subset_union_right) cγ hp
        · refine ⟨and_congr (h₁ n (le_trans (le_max_left _ _) hn')).1 ?_, ?_⟩
          · rw [settlesAt_assign_iff q₂ hn.2]
            exact (h₂ n (le_trans (le_max_right _ _) hn')).1
          · refine hval L₁ L₂ _ _ n (h₁ n (le_trans (le_max_left _ _) hn')).2 ?_
            rw [AggQueryIn.evaluatePlain_assign_of_noMention _ q₂ hn.2]
            exact (h₂ n (le_trans (le_max_right _ _) hn')).2
      · subst hl₁; subst hl₂
        obtain ⟨N₁, L₁, b₁, hv₁, h₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).1 rfl cγ
        obtain ⟨N₂, hN₂⟩ := (ih₂ hq.2.2 hs.2 hh.2).2 s m rfl hn.2 cγ W hW
        refine ⟨max N₁ N₂, fun LX hLX => ?_⟩
        obtain ⟨L₂, b₂, hv₂, h₂⟩ := hN₂ LX hLX
        refine ⟨PolyBag.bindShapes L₁ (fun _ => L₂), b₁ ∧ b₂, ?_, fun n hn' => ?_⟩
        · refine PolyBag.vals_bindShapes L₁ _ _ (subset_trans hv₁ (fun p hp => Or.inr ?_))
            (fun _ _ => subset_trans hv₂ ?_)
          · exact Univ_subset_hole (q := AggQueryIn.Prod q₁ q₂) q₁ hn.1
              (by exact Finset.subset_union_left) (fun _ _ => Set.subset_union_left) cγ hp
          · exact Set.union_subset_union_right W (UnivHole_mono (q := AggQueryIn.Prod q₁ q₂)
              (q' := q₂) (by exact Finset.subset_union_right)
                  (fun _ _ => Set.subset_union_right) cγ)
        · refine ⟨and_congr ?_ (h₂ n (le_trans (le_max_right _ _) hn')).1, ?_⟩
          · rw [settlesAt_assign_iff q₁ hn.1]
            exact (h₁ n (le_trans (le_max_left _ _) hn')).1
          · refine hval L₁ L₂ _ _ n ?_ (h₂ n (le_trans (le_max_right _ _) hn')).2
            rw [AggQueryIn.evaluatePlain_assign_of_noMention _ q₁ hn.1]
            exact (h₁ n (le_trans (le_max_left _ _) hn')).2
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l'
    intro hq hs hh
    -- the apply's value, given the right side's bag at each shape of the left
    have hval : ∀ (L₁ : PolyBag n₁) (F : Shape n₁ → PolyBag n₂) (D : Database ℕ)
        (cγ : Fin c' → Poly) (n : ℕ),
        ((q₁.evaluatePlain D (ctxAt cγ n) : Multiset (Tuple ℕ n₁)) = PolyBag.inst L₁ n) →
        (∀ s ∈ L₁, s.mult.eval n ≠ 0 →
          (q₂.evaluatePlain D (ctxAt (Fin.append s.row cγ) n) : Multiset (Tuple ℕ n₂))
            = PolyBag.inst (F s) n) →
        ((AggQueryIn.Apply q₁ q₂).evaluatePlain D (ctxAt cγ n) : Multiset (Tuple ℕ (n₁ + n₂)))
          = PolyBag.inst (PolyBag.bindShapes L₁ F) n := by
      intro L₁ F D cγ n h₁ hF
      rw [AggQueryIn.evaluatePlain, h₁]
      refine PolyBag.inst_bindShapes L₁ F
        (fun u => q₂.evaluatePlain D (Fin.append u (ctxAt cγ n))) n (fun s hs' hm => ?_)
      show q₂.evaluatePlain D (Fin.append (s.rowAt n) (ctxAt cγ n)) = _
      rw [show (Fin.append (s.rowAt n) (ctxAt cγ n) : Fin (n₁ + c') → ℕ)
        = ctxAt (Fin.append s.row cγ) n from ctxAt_append s.row cγ n]
      exact hF s hs' hm
    -- and its settling
    have hset : ∀ (L₁ : PolyBag n₁) (bs : Shape n₁ → Prop) (D : Database ℕ) (cγ : Fin c' → Poly)
        (n : ℕ), 1 ≤ n →
        ((q₁.evaluatePlain D (ctxAt cγ n) : Multiset (Tuple ℕ n₁)) = PolyBag.inst L₁ n) →
        (∀ s ∈ L₁, s.mult ≠ 0 → (q₂.SettlesAt D (ctxAt (Fin.append s.row cγ) n) ↔ bs s)) →
        ((∀ u, Multiset.Mem (q₁.evaluatePlain D (ctxAt cγ n)) u →
            q₂.SettlesAt D (Fin.append u (ctxAt cγ n))) ↔ ∀ s ∈ L₁, s.mult ≠ 0 → bs s) := by
      intro L₁ bs D cγ n h1 h₁ hbs
      rw [h₁]
      constructor
      · intro h s hs' hm
        have := h (s.rowAt n) (PolyBag.mem_inst.mpr
          ⟨s, hs', (not_congr (Poly.eval_eq_zero_iff h1)).mpr hm, rfl⟩)
        rw [show (Fin.append (s.rowAt n) (ctxAt cγ n) : Fin (n₁ + c') → ℕ)
          = ctxAt (Fin.append s.row cγ) n from ctxAt_append s.row cγ n] at this
        exact (hbs s hs' hm).mp this
      · intro h u hu
        obtain ⟨s, hs', hm, rfl⟩ := PolyBag.mem_inst.mp hu
        rw [show (Fin.append (s.rowAt n) (ctxAt cγ n) : Fin (n₁ + c') → ℕ)
          = ctxAt (Fin.append s.row cγ) n from ctxAt_append s.row cγ n]
        exact (hbs s hs' ((not_congr (Poly.eval_eq_zero_iff h1)).mp hm)).mpr
          (h s hs' ((not_congr (Poly.eval_eq_zero_iff h1)).mp hm))
    have hc2 : ∀ cγ : Fin c' → Poly, ∀ r : Fin n₁ → Poly, ClosedSym q₂ (Fin.append r cγ) :=
      fun cγ r => (ih₂ hq.2.2 hs.2 hh.2).1 rfl _
    refine ⟨fun hl cγ => ?_, fun s m hl hn cγ W hW => ?_⟩
    · obtain ⟨N₁, L₁, b₁, hv₁, h₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).1 hl cγ
      choose Ns Ls bs hvs hs2 using hc2 cγ
      obtain ⟨N₂, hN₂⟩ := exists_uniform L₁.toFinset (fun N s => Ns s.row ≤ N)
        (fun _ _ _ hle h => le_trans h hle) (fun s _ => ⟨Ns s.row, le_refl _⟩)
      refine ⟨max (max N₁ N₂) 1, PolyBag.bindShapes L₁ (fun s => Ls s.row),
        b₁ ∧ ∀ s ∈ L₁, s.mult ≠ 0 → bs s.row, ?_, fun n hn => ?_⟩
      · refine PolyBag.vals_bindShapes L₁ _ _ (subset_trans hv₁ (Univ_mono
          (q := AggQueryIn.Apply q₁ q₂) (q' := q₁) (by exact Finset.subset_union_left)
          (fun _ => Set.subset_union_left) cγ)) (fun s hs' => subset_trans (hvs s.row) ?_)
        rintro p (((h | h) | h) | h)
        · exact Cset_subset_Univ _ _ (Cset_mono (by exact Finset.subset_union_right) h)
        · rw [Set.mem_singleton_iff.mp h]; exact one_mem_Univ _ _
        · rcases range_append_subset s.row cγ h with ⟨i, hi⟩ | h
          · exact Univ_mono (q := AggQueryIn.Apply q₁ q₂) (q' := q₁)
              (by exact Finset.subset_union_left) (fun _ => Set.subset_union_left) cγ
              (hv₁ ⟨s, hs', i, hi⟩)
          · exact range_subset_Univ _ _ h
        · exact Or.inr (CountPolys_mono (fun _ => Set.subset_union_right) h)
      · have hN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
        have hN₂' : ∀ s ∈ L₁, Ns s.row ≤ n := fun s hs' =>
          le_trans (hN₂ s (List.mem_toFinset.mpr hs'))
            (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
        have h1 : 1 ≤ n := le_trans (le_max_right _ _) hn
        exact ⟨and_congr (h₁ n hN₁).1 (hset L₁ (fun s => bs s.row) _ cγ n h1 (h₁ n hN₁).2
            (fun s hs' _ => (hs2 s.row n (hN₂' s hs')).1)),
          hval L₁ _ _ cγ n (h₁ n hN₁).2 (fun s hs' _ => (hs2 s.row n (hN₂' s hs')).2)⟩
    · subst hl
      obtain ⟨N₁, hN₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).2 s m rfl hn.1 cγ W hW
      choose Ns Ls bs hvs hs2 using hc2 cγ
      have hU : (Union.union W (UnivHole q₁ s m cγ)).Finite :=
        hW.union (UnivHole_finite q₁ hs.1 hh.1 (show q₁.noMention s from hn.1) cγ)
      have hC : {r : Fin n₁ → Poly | ∀ j, r j ∈ Union.union W (UnivHole q₁ s m cγ)}.Finite :=
        Set.Finite.pi' (fun _ => hU)
      obtain ⟨N₂, hN₂⟩ := exists_uniform hC.toFinset (fun N r => Ns r ≤ N)
        (fun _ _ _ hle h => le_trans h hle) (fun r _ => ⟨Ns r, le_refl _⟩)
      refine ⟨max (max N₁ N₂) 1, fun LX hLX => ?_⟩
      obtain ⟨L₁, b₁, hv₁, h₁⟩ := hN₁ LX hLX
      have hrows : ∀ s' ∈ L₁, Ns s'.row ≤ N₂ := fun s' hs' =>
        hN₂ s'.row (hC.mem_toFinset.mpr (fun j => hv₁ ⟨s', hs', j, rfl⟩))
      refine ⟨PolyBag.bindShapes L₁ (fun s' => Ls s'.row),
        b₁ ∧ ∀ s' ∈ L₁, s'.mult ≠ 0 → bs s'.row, ?_, fun n hn' => ?_⟩
      · refine PolyBag.vals_bindShapes L₁ _ _ (subset_trans hv₁ (Set.union_subset_union_right W
          (UnivHole_mono (q := AggQueryIn.Apply q₁ q₂) (q' := q₁)
            (by exact Finset.subset_union_left) (fun _ _ => Set.subset_union_left) cγ)))
          (fun s' hs' => subset_trans (hvs s'.row) ?_)
        rintro p (((h | h) | h) | h)
        · exact Or.inr (Cset_subset_UnivHole _ _ _
            (Cset_mono (by exact Finset.subset_union_right) h))
        · rw [Set.mem_singleton_iff.mp h]; exact Or.inr (one_mem_UnivHole _ _ _)
        · rcases range_append_subset s'.row cγ h with ⟨i, hi⟩ | h
          · exact Set.union_subset_union_right W (UnivHole_mono (q := AggQueryIn.Apply q₁ q₂)
              (q' := q₁) (by exact Finset.subset_union_left) (fun _ _ => Set.subset_union_left) cγ)
              (hv₁ ⟨s', hs', i, hi⟩)
          · exact Or.inr (range_subset_UnivHole _ _ _ h)
        · exact Or.inr (Or.inr (CountPolys_subset_hole q₂ hn.2
            (fun _ _ => Set.subset_union_right) h))
      · have hN₁' : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn'
        have hN₂' : ∀ s' ∈ L₁, Ns s'.row ≤ n := fun s' hs' => le_trans (hrows s' hs')
          (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn')
        have h1 : 1 ≤ n := le_trans (le_max_right _ _) hn'
        refine ⟨and_congr (h₁ n hN₁').1 (hset L₁ (fun s' => bs s'.row) _ cγ n h1 (h₁ n hN₁').2
            (fun s' hs' _ => ?_)), hval L₁ _ _ cγ n (h₁ n hN₁').2 (fun s' hs' _ => ?_)⟩
        · rw [settlesAt_assign_iff q₂ hn.2]
          exact (hs2 s'.row n (hN₂' s' hs')).1
        · rw [AggQueryIn.evaluatePlain_assign_of_noMention _ q₂ hn.2]
          exact (hs2 s'.row n (hN₂' s' hs')).2
  | Sum q₁ q₂ ih₁ ih₂ =>
    rename_i c' n' κ' l₁ l₂
    intro hq hs hh
    have hval : ∀ (L₁ L₂ : PolyBag n') (D : Database ℕ) (γ : Fin c' → ℕ) (n : ℕ),
        ((q₁.evaluatePlain D γ : Multiset (Tuple ℕ n')) = PolyBag.inst L₁ n) →
        ((q₂.evaluatePlain D γ : Multiset (Tuple ℕ n')) = PolyBag.inst L₂ n) →
        ((AggQueryIn.Sum q₁ q₂).evaluatePlain D γ : Multiset (Tuple ℕ n'))
          = PolyBag.inst (L₁ ++ L₂) n := by
      intro L₁ L₂ D γ n h₁ h₂
      rw [AggQueryIn.evaluatePlain]
      show _ + _ = _
      rw [h₁, h₂, PolyBag.inst_append]
    refine ⟨fun hl cγ => ?_, fun s m hl hn cγ W hW => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      obtain ⟨N₁, L₁, b₁, hv₁, h₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).1 hl₁ cγ
      obtain ⟨N₂, L₂, b₂, hv₂, h₂⟩ := (ih₂ hq.2.2 hs.2 hh.2).1 hl₂ cγ
      refine ⟨max N₁ N₂, L₁ ++ L₂, b₁ ∧ b₂, ?_, fun n hn => ?_⟩
      · refine subset_trans (PolyBag.vals_append L₁ L₂) (Set.union_subset (subset_trans hv₁ ?_)
          (subset_trans hv₂ ?_))
        · exact Univ_mono (q := AggQueryIn.Sum q₁ q₂) (q' := q₁)
            (by exact Finset.subset_union_left) (fun _ => Set.subset_union_left) cγ
        · exact Univ_mono (q := AggQueryIn.Sum q₁ q₂) (q' := q₂)
            (by exact Finset.subset_union_right) (fun _ => Set.subset_union_right) cγ
      · exact ⟨and_congr (h₁ n (le_trans (le_max_left _ _) hn)).1
          (h₂ n (le_trans (le_max_right _ _) hn)).1,
          hval L₁ L₂ _ _ n (h₁ n (le_trans (le_max_left _ _) hn)).2
            (h₂ n (le_trans (le_max_right _ _) hn)).2⟩
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁; subst hl₂
        obtain ⟨N₁, hN₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).2 s m rfl hn.1 cγ W hW
        obtain ⟨N₂, L₂, b₂, hv₂, h₂⟩ := (ih₂ hq.2.2 hs.2 hh.2).1 rfl cγ
        refine ⟨max N₁ N₂, fun LX hLX => ?_⟩
        obtain ⟨L₁, b₁, hv₁, h₁⟩ := hN₁ LX hLX
        refine ⟨L₁ ++ L₂, b₁ ∧ b₂, ?_, fun n hn' => ?_⟩
        · refine subset_trans (PolyBag.vals_append L₁ L₂) (Set.union_subset (subset_trans hv₁ ?_)
            (subset_trans hv₂ (fun p hp => Or.inr ?_)))
          · exact Set.union_subset_union_right W (UnivHole_mono (q := AggQueryIn.Sum q₁ q₂)
              (q' := q₁) (by exact Finset.subset_union_left) (fun _ _ => Set.subset_union_left) cγ)
          · exact Univ_subset_hole (q := AggQueryIn.Sum q₁ q₂) q₂ hn.2
              (by exact Finset.subset_union_right) (fun _ _ => Set.subset_union_right) cγ hp
        · refine ⟨and_congr (h₁ n (le_trans (le_max_left _ _) hn')).1 ?_, ?_⟩
          · rw [settlesAt_assign_iff q₂ hn.2]
            exact (h₂ n (le_trans (le_max_right _ _) hn')).1
          · refine hval L₁ L₂ _ _ n (h₁ n (le_trans (le_max_left _ _) hn')).2 ?_
            rw [AggQueryIn.evaluatePlain_assign_of_noMention _ q₂ hn.2]
            exact (h₂ n (le_trans (le_max_right _ _) hn')).2
      · subst hl₁; subst hl₂
        obtain ⟨N₁, L₁, b₁, hv₁, h₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).1 rfl cγ
        obtain ⟨N₂, hN₂⟩ := (ih₂ hq.2.2 hs.2 hh.2).2 s m rfl hn.2 cγ W hW
        refine ⟨max N₁ N₂, fun LX hLX => ?_⟩
        obtain ⟨L₂, b₂, hv₂, h₂⟩ := hN₂ LX hLX
        refine ⟨L₁ ++ L₂, b₁ ∧ b₂, ?_, fun n hn' => ?_⟩
        · refine subset_trans (PolyBag.vals_append L₁ L₂) (Set.union_subset
            (subset_trans hv₁ (fun p hp => Or.inr ?_)) (subset_trans hv₂ ?_))
          · exact Univ_subset_hole (q := AggQueryIn.Sum q₁ q₂) q₁ hn.1
              (by exact Finset.subset_union_left) (fun _ _ => Set.subset_union_left) cγ hp
          · exact Set.union_subset_union_right W (UnivHole_mono (q := AggQueryIn.Sum q₁ q₂)
              (q' := q₂) (by exact Finset.subset_union_right)
                  (fun _ _ => Set.subset_union_right) cγ)
        · refine ⟨and_congr ?_ (h₂ n (le_trans (le_max_right _ _) hn')).1, ?_⟩
          · rw [settlesAt_assign_iff q₁ hn.1]
            exact (h₁ n (le_trans (le_max_left _ _) hn')).1
          · refine hval L₁ L₂ _ _ n ?_ (h₂ n (le_trans (le_max_right _ _) hn')).2
            rw [AggQueryIn.evaluatePlain_assign_of_noMention _ q₁ hn.1]
            exact (h₁ n (le_trans (le_max_left _ _) hn')).2
  | Dedup q ih =>
    rename_i c' n'
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    obtain ⟨N, L, b, hv, h⟩ := (ih hq.2 hs hh).1 hl cγ
    obtain ⟨Nd, hNd⟩ := exists_decided (PolyBag.vals_finite L)
    refine ⟨max (max N Nd) 1, dedupAt (max (max N Nd) 1) L, b, ?_, fun n hn => ?_⟩
    · exact subset_trans (dedupAt_vals _ L) (subset_trans hv (Univ_mono (q := AggQueryIn.Dedup q)
        (q' := q) (subset_refl _) (fun _ => subset_refl _) cγ))
    · have hN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
      refine ⟨(h n hN).1, ?_⟩
      rw [AggQueryIn.evaluatePlain, (h n hN).2]
      exact inst_dedupAt (hNd.mono (le_trans (le_max_right _ _) (le_max_left _ _))) L
        (subset_refl _) hn (le_trans (le_max_right _ _) hn)
  | Diff q₁ q₂ ih₁ ih₂ =>
    rename_i c' n'
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    obtain ⟨N₁, L₁, b₁, hv₁, h₁⟩ := (ih₁ hq.2.1 hs.1 hh.1).1 rfl cγ
    obtain ⟨N₂, L₂, b₂, hv₂, h₂⟩ := (ih₂ hq.2.2 hs.2 hh.2).1 rfl cγ
    obtain ⟨Nd, hNd⟩ := exists_decided ((PolyBag.vals_finite L₁).union (PolyBag.vals_finite L₂))
    set N' := max (max N₁ N₂) (max Nd 1) with hN'
    refine ⟨N', L₁.filter (fun s => decide (¬ ∃ t ∈ L₂, t.mult ≠ 0 ∧ t.rowAt N' = s.rowAt N')),
      b₁ ∧ b₂, ?_, fun n hn => ?_⟩
    · exact subset_trans (PolyBag.vals_filter _ L₁) (subset_trans hv₁
        (Univ_mono (q := AggQueryIn.Diff q₁ q₂) (q' := q₁) (by exact Finset.subset_union_left)
          (fun _ => Set.subset_union_left) cγ))
    · have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
      have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      have hnd : N' ≤ n := hn
      have h1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
      have hNd' : Decided (Union.union (PolyBag.vals L₁) (PolyBag.vals L₂)) N' :=
        hNd.mono (le_trans (le_max_left _ _) (le_max_right _ _))
      refine ⟨and_congr (h₁ n hn₁).1 (h₂ n hn₂).1, ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [(h₁ n hn₁).2, (h₂ n hn₂).2]
      refine PolyBag.inst_filter _ _ _ L₁ n (fun s hs' => ?_)
      rw [decide_eq_true_iff, PolyBag.mem_inst]
      refine not_congr (exists_congr (fun t => and_congr_right (fun ht => and_congr
        (not_congr (Poly.eval_eq_zero_iff h1)) ?_)))
      rw [eq_comm]
      exact Shape.rowAt_eq_shift hNd' (fun j => Or.inr ⟨t, ht, j, rfl⟩)
        (fun j => Or.inl ⟨s, hs', j, rfl⟩) hnd
  | Explode k hk q ih =>
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s m hl hn cγ W hW => ?_⟩
    · obtain ⟨N, L, b, hv, h⟩ := (ih hq hs hh).1 hl cγ
      exact ⟨N, L, b, hv, fun n hn => ⟨(h n hn).1, (h n hn).2⟩⟩
    · obtain ⟨N, hN⟩ := (ih hq hs hh).2 s m hl hn cγ W hW
      refine ⟨N, fun LX hLX => ?_⟩
      obtain ⟨L, b, hv, h⟩ := hN LX hLX
      exact ⟨L, b, hv, fun n hn => ⟨(h n hn).1, (h n hn).2⟩⟩
  | Retag hk q ih =>
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s m hl hn cγ W hW => ?_⟩
    · obtain ⟨N, L, b, hv, h⟩ := (ih hq hs hh).1 hl cγ
      exact ⟨N, L, b, hv, fun n hn => ⟨(h n hn).1, (h n hn).2⟩⟩
    · obtain ⟨N, hN⟩ := (ih hq hs hh).2 s m hl hn cγ W hW
      refine ⟨N, fun LX hLX => ?_⟩
      obtain ⟨L, b, hv, h⟩ := hN LX hLX
      exact ⟨L, b, hv, fun n hn => ⟨(h n hn).1, (h n hn).2⟩⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' k' _
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s' m hl => absurd hl (by simp)⟩
    obtain ⟨N₀, L₀, b₀, hv₀, h₀⟩ := (ih₀ hq.2.1 hs.1 hh.2.2.1).1 rfl cγ
    -- the universe the rounds live in
    obtain ⟨Wst, hWst⟩ : ∃ Wst : Set Poly, Wst = Union.union (PolyBag.vals L₀)
        (UnivHole q₁ s k' cγ) :=
      ⟨_, rfl⟩
    have hWf : Wst.Finite :=
      hWst ▸ (PolyBag.vals_finite L₀).union (UnivHole_finite q₁ hs.2 hh.2.2.2 hh.2.1 cγ)
    obtain ⟨Nb, hNb⟩ := (ih₁ hq.2.2 hs.2 hh.2.2.2).2 s k' rfl hh.2.1 cγ Wst hWf
    -- one symbolic round, on bags over the universe
    have hstep : ∀ LX : {LX : PolyBag k' // PolyBag.vals LX ⊆ Wst},
        ∃ (L : {L : PolyBag k' // PolyBag.vals L ⊆ Wst}) (b : Prop), ∀ n ≥ Nb,
          (q₁.SettlesAt ((dRep n).assign s (PolyBag.inst LX.1 n)) (ctxAt cγ n) ↔ b)
            ∧ (q₁.evaluatePlain ((dRep n).assign s (PolyBag.inst LX.1 n)) (ctxAt cγ n)
                : Multiset (Tuple ℕ k')) = PolyBag.inst L.1 n := by
      intro LX
      obtain ⟨L, b, hv, h⟩ := hNb LX.1 LX.2
      exact ⟨⟨L, subset_trans hv (fun p hp => hp.elim id (fun h => hWst ▸ Or.inr h))⟩, b, h⟩
    choose F bF hF using hstep
    -- the rounds
    obtain ⟨R, hR0, hRs⟩ : ∃ R : ℕ → {L : PolyBag k' // PolyBag.vals L ⊆ Wst},
        R 0 = ⟨L₀, fun p hp => hWst ▸ Or.inl hp⟩ ∧ ∀ j, R (j + 1) = F (R j) :=
      ⟨fun j => Nat.rec ⟨L₀, fun p hp => hWst ▸ Or.inl hp⟩ (fun _ L => F L) j, rfl, fun _ => rfl⟩
    -- the sum of the rounds `j .. j + b`
    obtain ⟨concat, hc0, hcs⟩ : ∃ concat : ℕ → ℕ → PolyBag k',
        (∀ j, concat j 0 = (R j).1) ∧ ∀ j b, concat j (b + 1) = (R j).1 ++ concat (j + 1) b :=
      ⟨fun j b => Nat.rec (motive := fun _ => ℕ → PolyBag k') (fun j => (R j).1)
        (fun _ ih j => (R j).1 ++ ih (j + 1)) b j, fun _ => rfl, fun _ _ => rfl⟩
    have hconcat_vals : ∀ b j, PolyBag.vals (concat j b) ⊆ Wst := by
      intro b
      induction b with
      | zero => exact fun j => hc0 j ▸ (R j).2
      | succ b ih =>
        intro j
        rw [hcs]
        exact subset_trans (PolyBag.vals_append _ _) (Set.union_subset (R j).2 (ih (j + 1)))
    have hcA : (AggQueryIn.Mu s q₀ q₁).allConsts = Union.union q₀.allConsts q₁.allConsts := by
      rw [AggQueryIn.allConsts]
    have hWU : Wst ⊆ Univ (AggQueryIn.Mu s q₀ q₁) cγ := by
      rw [hWst]
      refine Set.union_subset (subset_trans hv₀ (Univ_mono (q := AggQueryIn.Mu s q₀ q₁) (q' := q₀)
        (by rw [hcA]; intro a ha; exact Finset.mem_union_left _ ha)
        (fun _ => Set.subset_union_left) cγ)) ?_
      rintro p (((h | h) | h) | ⟨N, hN⟩)
      · exact Or.inl (Or.inl (Or.inl (Cset_mono (by
          rw [hcA]; intro a ha; exact Finset.mem_union_right _ ha) h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · refine Or.inr ⟨N, fun n hn => ?_⟩
        obtain ⟨X, hX⟩ := hN n hn
        exact Or.inr (Set.mem_iUnion.mpr ⟨X, hX⟩)
    -- the fixpoint index, read off the symbolic rounds
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = sInf {j | PolyBag.allZero (R (j + 1)).1} := ⟨_, rfl⟩
    obtain ⟨N', hN'⟩ : ∃ N', N' = max (max N₀ Nb) 1 := ⟨_, rfl⟩
    have hN₀N : N₀ ≤ N' := hN' ▸ le_trans (le_max_left _ _) (le_max_left _ _)
    have hNbN : Nb ≤ N' := hN' ▸ le_trans (le_max_right _ _) (le_max_left _ _)
    have h1N : 1 ≤ N' := hN' ▸ le_max_right _ _
    refine ⟨N', concat 0 K, b₀ ∧ PolyBag.allZero (F ⟨[], fun _ h => absurd h.choose_spec.1
        List.not_mem_nil⟩).1 ∧ (∃ j, PolyBag.allZero (R (j + 1)).1) ∧ ∀ j, bF (R j),
      subset_trans (hconcat_vals K 0) hWU, fun n hn => ?_⟩
    have hN₀n : N₀ ≤ n := le_trans hN₀N hn
    have hNbn : Nb ≤ n := le_trans hNbN hn
    have h1n : 1 ≤ n := le_trans h1N hn
    -- the rounds at `n`
    obtain ⟨step, hstepdef⟩ : ∃ step : Relation ℕ k' → Relation ℕ k',
        step = fun X => q₁.evaluatePlain ((dRep n).assign s X) (ctxAt cγ n) := ⟨_, rfl⟩
    have hstepR : ∀ j, step (PolyBag.inst (R j).1 n) = PolyBag.inst (R (j + 1)).1 n := by
      intro j
      rw [hstepdef, hRs]
      exact (hF (R j) n hNbn).2
    have hround : ∀ j, step^[j] (PolyBag.inst L₀ n) = PolyBag.inst (R j).1 n := by
      intro j
      induction j with
      | zero => show PolyBag.inst L₀ n = PolyBag.inst (R 0).1 n; rw [hR0]
      | succ j ih => rw [Function.iterate_succ_apply', ih, hstepR]
    have hsum : ∀ b j, muSum step b (step^[j] (PolyBag.inst L₀ n)) = PolyBag.inst
        (concat j b) n := by
      intro b
      induction b with
      | zero => intro j; rw [muSum, hround, hc0]
      | succ b ih =>
        intro j
        rw [muSum, ← Function.iterate_succ_apply' step, ih, hround, hcs, PolyBag.inst_append]
    have hzero : ∀ j, (step^[j + 1] (PolyBag.inst L₀ n) = 0 ↔ PolyBag.allZero (R (j + 1)).1) := by
      intro j
      rw [hround]
      exact PolyBag.inst_eq_zero_iff _ h1n
    have hM : (q₀.evaluatePlain (dRep n) (ctxAt cγ n) : Multiset
        (Tuple ℕ k')) = PolyBag.inst L₀ n :=
      (h₀ n hN₀n).2
    have hK' : muRounds step (PolyBag.inst L₀ n) = K := by
      rw [hK]
      unfold muRounds
      congr 1
      ext j
      exact hzero j
    subst hstepdef
    constructor
    · -- settling
      rw [AggQueryIn.SettlesAt]
      refine and_congr (h₀ n hN₀n).1 (and_congr ?_ (and_congr ?_ ?_))
      · have h0 : (q₁.evaluatePlain ((dRep n).assign s (0 : Relation ℕ k')) (ctxAt cγ n)
            : Multiset (Tuple ℕ k'))
            = PolyBag.inst (F ⟨[], fun _ h => absurd h.choose_spec.1 List.not_mem_nil⟩).1 n :=
          (hF ⟨[], fun _ h => absurd h.choose_spec.1 List.not_mem_nil⟩ n hNbn).2
        rw [h0]
        exact PolyBag.inst_eq_zero_iff _ h1n
      · show MuSettles (fun X : Relation ℕ k' => q₁.evaluatePlain ((dRep n).assign s X)
            (ctxAt cγ n))
          (q₀.evaluatePlain (dRep n) (ctxAt cγ n)) ↔ _
        unfold MuSettles
        rw [hM]
        exact exists_congr (fun j => hzero j)
      · rw [hM]
        refine forall_congr' (fun j => ?_)
        rw [hround]
        exact (hF (R j) n hNbn).1
    · -- the value
      rw [AggQueryIn.evaluatePlain]
      show muSumFix (fun X : Relation ℕ k' => q₁.evaluatePlain ((dRep n).assign s X) (ctxAt cγ n))
        (q₀.evaluatePlain (dRep n) (ctxAt cγ n)) = _
      rw [hM]
      unfold muSumFix
      rw [hK']
      exact hsum K 0
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' k'
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s' m hl => absurd hl (by simp)⟩
    obtain ⟨N₀, L₀, b₀, hv₀, h₀⟩ := (ih₀ hq.2.1 hs.1 hh.2.2.1).1 rfl cγ
    -- the universe the rounds live in
    obtain ⟨Wst, hWst⟩ : ∃ Wst : Set Poly, Wst = Union.union (PolyBag.vals L₀)
        (UnivHole q₁ s k' cγ) :=
      ⟨_, rfl⟩
    have hWf : Wst.Finite :=
      hWst ▸ (PolyBag.vals_finite L₀).union (UnivHole_finite q₁ hs.2 hh.2.2.2 hh.2.1 cγ)
    obtain ⟨Nb, hNb⟩ := (ih₁ hq.2.2 hs.2 hh.2.2.2).2 s k' rfl hh.2.1 cγ Wst hWf
    obtain ⟨Nd, hNd⟩ := exists_decided hWf
    have hL₀W : PolyBag.vals L₀ ⊆ Wst := fun p hp => hWst ▸ Or.inl hp
    -- one symbolic round, on bags over the universe
    have hstep : ∀ LX : {LX : PolyBag k' // PolyBag.vals LX ⊆ Wst},
        ∃ (L : {L : PolyBag k' // PolyBag.vals L ⊆ Wst}) (b : Prop), ∀ n ≥ Nb,
          (q₁.SettlesAt ((dRep n).assign s (PolyBag.inst LX.1 n)) (ctxAt cγ n) ↔ b)
            ∧ (q₁.evaluatePlain ((dRep n).assign s (PolyBag.inst LX.1 n)) (ctxAt cγ n)
                : Multiset (Tuple ℕ k')) = PolyBag.inst L.1 n := by
      intro LX
      obtain ⟨L, b, hv, h⟩ := hNb LX.1 LX.2
      exact ⟨⟨L, subset_trans hv (fun p hp => hp.elim id (fun h => hWst ▸ Or.inr h))⟩, b, h⟩
    choose F bF hF using hstep
    -- the rounds: the base and the body's answer, deduplicated at the threshold
    have hnext : ∀ L : {L : PolyBag k' // PolyBag.vals L ⊆ Wst},
        PolyBag.vals (dedupAt Nd (L₀ ++ (F L).1)) ⊆ Wst :=
      fun L => subset_trans (dedupAt_vals Nd _)
        (subset_trans (PolyBag.vals_append _ _) (Set.union_subset hL₀W (F L).2))
    obtain ⟨R, hR0, hRs⟩ : ∃ R : ℕ → {L : PolyBag k' // PolyBag.vals L ⊆ Wst},
        R 0 = ⟨[], fun _ h => absurd h.choose_spec.1 List.not_mem_nil⟩
          ∧ ∀ j, R (j + 1) = ⟨dedupAt Nd (L₀ ++ (F (R j)).1), hnext (R j)⟩ :=
      ⟨fun j => Nat.rec ⟨[], fun _ h => absurd h.choose_spec.1 List.not_mem_nil⟩
        (fun _ L => ⟨dedupAt Nd (L₀ ++ (F L).1), hnext L⟩) j, rfl, fun _ => rfl⟩
    have hR1 : ∀ j, ∀ t ∈ (R j).1, t.mult = 1 := by
      intro j
      cases j with
      | zero => rw [hR0]; exact fun t ht => absurd ht List.not_mem_nil
      | succ j => rw [hRs]; exact dedupAt_mult Nd _
    have hRnd : ∀ j, ((R j).1.map (fun t => t.rowAt Nd)).Nodup := by
      intro j
      cases j with
      | zero => rw [hR0]; exact List.nodup_nil
      | succ j => rw [hRs]; exact dedupAt_nodup Nd _
    have hcA : (AggQueryIn.MuSet s q₀ q₁).allConsts = Union.union q₀.allConsts q₁.allConsts := by
      rw [AggQueryIn.allConsts]
    have hWU : Wst ⊆ Univ (AggQueryIn.MuSet s q₀ q₁) cγ := by
      rw [hWst]
      refine Set.union_subset (subset_trans hv₀ (Univ_mono (q := AggQueryIn.MuSet s q₀ q₁)
          (q' := q₀)
        (by rw [hcA]; intro a ha; exact Finset.mem_union_left _ ha)
        (fun _ => Set.subset_union_left) cγ)) ?_
      rintro p (((h | h) | h) | ⟨N, hN⟩)
      · exact Or.inl (Or.inl (Or.inl (Cset_mono (by
          rw [hcA]; intro a ha; exact Finset.mem_union_right _ ha) h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · refine Or.inr ⟨N, fun n hn => ?_⟩
        obtain ⟨X, hX⟩ := hN n hn
        exact Or.inr (Set.mem_iUnion.mpr ⟨X, hX⟩)
    -- the fixpoint index, read off the symbolic rounds at the threshold
    obtain ⟨K, hK⟩ : ∃ K : ℕ,
        K = sInf {j | PolyBag.inst (R (j + 1)).1 Nd = PolyBag.inst (R j).1 Nd} := ⟨_, rfl⟩
    obtain ⟨N', hN'⟩ : ∃ N', N' = max (max N₀ Nb) (max Nd 1) := ⟨_, rfl⟩
    have hN₀N : N₀ ≤ N' := hN' ▸ le_trans (le_max_left _ _) (le_max_left _ _)
    have hNbN : Nb ≤ N' := hN' ▸ le_trans (le_max_right _ _) (le_max_left _ _)
    have hNdN : Nd ≤ N' := hN' ▸ le_trans (le_max_left _ _) (le_max_right _ _)
    have h1N : 1 ≤ N' := hN' ▸ le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨N', (R K).1,
      b₀ ∧ (∃ j, PolyBag.inst (R (j + 1)).1 Nd = PolyBag.inst (R j).1 Nd) ∧ ∀ j, bF (R j),
      subset_trans (R K).2 hWU, fun n hn => ?_⟩
    have hN₀n : N₀ ≤ n := le_trans hN₀N hn
    have hNbn : Nb ≤ n := le_trans hNbN hn
    have hNdn : Nd ≤ n := le_trans hNdN hn
    have h1n : 1 ≤ n := le_trans h1N hn
    have hM : (q₀.evaluatePlain (dRep n) (ctxAt cγ n) : Multiset
        (Tuple ℕ k')) = PolyBag.inst L₀ n :=
      (h₀ n hN₀n).2
    -- the rounds at `n`
    obtain ⟨step, hstepdef⟩ : ∃ step : Relation ℕ k' → Relation ℕ k',
        step = fun X => (q₀.evaluatePlain (dRep n) (ctxAt cγ n)
          + q₁.evaluatePlain ((dRep n).assign s X) (ctxAt cγ n)).dedup := ⟨_, rfl⟩
    have hiter : ∀ j, muIter step j = PolyBag.inst (R j).1 n := by
      intro j
      induction j with
      | zero => rw [hR0]; rfl
      | succ j ih =>
        rw [muIter, ih, hstepdef]
        show ((q₀.evaluatePlain (dRep n) (ctxAt cγ n) : Multiset (Tuple ℕ k'))
          + q₁.evaluatePlain ((dRep n).assign s (PolyBag.inst (R j).1 n)) (ctxAt cγ n)).dedup = _
        rw [hM, (hF (R j) n hNbn).2, ← PolyBag.inst_append,
          inst_dedupAt hNd _ (subset_trans (PolyBag.vals_append _ _)
            (Set.union_subset hL₀W (F (R j)).2)) hNdn h1n, hRs]
    have hsame : ∀ j, (step^[j + 1] 0 = step^[j] 0
        ↔ PolyBag.inst (R (j + 1)).1 Nd = PolyBag.inst (R j).1 Nd) := by
      intro j
      rw [← muIter_eq_iterate, ← muIter_eq_iterate, hiter, hiter]
      exact inst_eq_iff_shift hNd _ _ (R (j + 1)).2 (R j).2 (hR1 _) (hR1 _) (hRnd _) (hRnd _) hNdn
    have hK' : muFixIdx step = K := by
      rw [hK]
      unfold muFixIdx
      congr 1
      ext j
      exact hsame j
    subst hstepdef
    constructor
    · -- settling
      rw [AggQueryIn.SettlesAt]
      refine and_congr (h₀ n hN₀n).1 (and_congr ?_ ?_)
      · unfold MuSetSettles
        exact exists_congr (fun j => hsame j)
      · refine forall_congr' (fun j => ?_)
        erw [hiter]
        exact (hF (R j) n hNbn).1
    · -- the value
      rw [AggQueryIn.evaluatePlain]
      unfold muFix
      erw [hK', hiter]
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m' n₁ n₂
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    obtain ⟨N, L, b, hv, h⟩ := (ih hq.2 hs.2.2.2 hh).1 rfl cγ
    have hfs : ∀ j, fs j = SeqAggFunc.count := fun j => Set.mem_singleton_iff.mp (hs.2.1 j)
    obtain ⟨Nd, hNd⟩ := exists_decided (((PolyBag.vals_finite L).union
      (Cset_finite (AggQueryIn.Gamma is ts fs q keep ord).allConsts)).union (Set.finite_range cγ))
    obtain ⟨N', hN'⟩ : ∃ N', N' = max (max N Nd) 1 := ⟨_, rfl⟩
    have hNN : N ≤ N' := hN' ▸ le_trans (le_max_left _ _) (le_max_left _ _)
    have hNdN : Nd ≤ N' := hN' ▸ le_trans (le_max_right _ _) (le_max_left _ _)
    have h1N : 1 ≤ N' := hN' ▸ le_max_right _ _
    have hV : Decided (Union.union (Union.union (PolyBag.vals L)
      (Cset (AggQueryIn.Gamma is ts fs q keep ord).allConsts)) (Set.range cγ)) N' := hNd.mono hNdN
    have hVL : ∀ s ∈ L, ∀ j, s.row j ∈ Union.union (Union.union (PolyBag.vals L)
        (Cset (AggQueryIn.Gamma is ts fs q keep ord).allConsts)) (Set.range cγ) :=
      fun s hs' j => Or.inl (Or.inl ⟨s, hs', j, rfl⟩)
    have hcA : (AggQueryIn.Gamma is ts fs q keep ord).allConsts
        = Union.union (Union.union (TermIn.constsFam ts)
          (Finset.univ.biUnion (fun j => Selection.constsOpt (keep j)))) q.allConsts := by
      rw [AggQueryIn.allConsts]
    have hVk : ∀ j, Cset (Selection.constsOpt (keep j)) ⊆ Union.union (Union.union (PolyBag.vals L)
        (Cset (AggQueryIn.Gamma is ts fs q keep ord).allConsts)) (Set.range cγ) := by
      intro j
      refine subset_trans (Cset_mono (A := Selection.constsOpt (keep j))
        (A' := (AggQueryIn.Gamma is ts fs q keep ord).allConsts) ?_) (fun p hp => Or.inl
            (Or.inr hp))
      rw [hcA]
      intro a ha
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩))
    -- the keys, deduplicated at the threshold, and the counts of their groups
    obtain ⟨KL, hKL⟩ : ∃ KL : PolyBag n₁, KL = dedupAt N' (PolyBag.mapRows (Tuple.key is) L) :=
      ⟨_, rfl⟩
    have hKLv : PolyBag.vals KL ⊆ PolyBag.vals L :=
      hKL ▸ subset_trans (dedupAt_vals _ _) (PolyBag.vals_mapRows_key is L)
    have hKL1 : ∀ g ∈ KL, g.mult = 1 := hKL ▸ dedupAt_mult _ _
    obtain ⟨cnt, hcnt⟩ : ∃ cnt : (Fin n₁ → Poly) → Fin n₂ → Poly, cnt = fun gr j =>
        ((L.filter (fun s => decide (Tuple.key is (s.rowAt N') = (fun i => (gr i).eval N')
          ∧ Selection.keepsOpt (keep j) (s.rowAt N') = true))).map Shape.mult).sum := ⟨_, rfl⟩
    obtain ⟨OUT, hOUT⟩ : ∃ OUT : PolyBag (n₁ + n₂),
        OUT = KL.map (fun g => ⟨1, Fin.append g.row (cnt g.row)⟩) := ⟨_, rfl⟩
    have hOUT1 : ∀ t ∈ OUT, t.mult = 1 := by
      intro t ht
      rw [hOUT] at ht
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp ht
      rfl
    have heval : ∀ n ≥ N', ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain (dRep n)
        (ctxAt cγ n) : Multiset (Tuple ℕ (n₁ + n₂))) = PolyBag.inst OUT n := by
      intro n hn
      have hNn : N ≤ n := le_trans hNN hn
      have h1 : 1 ≤ n := le_trans h1N hn
      simp only [AggQueryIn.evaluatePlain]
      rw [(h n hNn).2]
      have hkeys : (Multiset.map (fun u => (fun k => u (is k) : Tuple ℕ n₁))
          (PolyBag.inst L n)).dedup = PolyBag.inst KL n := by
        rw [PolyBag.inst_mapRows (Tuple.key is) (fun u => (fun k => u (is k) : Tuple ℕ n₁)) L n
          (fun s _ => rfl), hKL]
        exact inst_dedupAt (hV.subset (fun p hp => Or.inl (Or.inl
          (PolyBag.vals_mapRows_key is L hp)))) _ (subset_refl _) hn h1
      erw [hkeys]
      rw [PolyBag.inst_of_ones KL hKL1 n, Multiset.map_coe, PolyBag.inst_of_ones OUT hOUT1 n, hOUT,
        List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left (fun g hg => ?_)
      show Fin.append (g.rowAt n) _
        = (⟨1, Fin.append g.row (cnt g.row)⟩ : Shape (n₁ + n₂)).rowAt n
      rw [Shape.rowAt_append]
      refine congrArg₂ Fin.append rfl ?_
      funext j
      show fs j (List.map (fun v => (ts j).eval v (ctxAt cγ n))
        (Relation.groupSeqOptOrd is ord (PolyBag.inst L n) (g.rowAt n) (keep j)))
        = (cnt g.row j).eval n
      rw [hfs j]
      show (List.map _ _).length = _
      rw [List.length_map, ← Multiset.coe_card, Relation.groupSeqOptOrd_coe, Multiset.filter_filter,
        PolyBag.card_filter_inst, hcnt]
      show _ = ((L.filter _ |>.map Shape.mult).sum).eval n
      rw [← sum_if_eq_filter]
      refine congrArg List.sum (List.map_congr_left (fun s hs' => ?_))
      refine if_congr ?_ rfl rfl
      rw [decide_eq_true_iff, and_comm]
      refine and_congr ?_ ?_
      · show (∀ k', Tuple.key is (s.rowAt n) k' = g.rowAt n k') ↔ _
        rw [← funext_iff]
        show (⟨s.mult, Tuple.key is s.row⟩ : Shape n₁).rowAt n = g.rowAt n
          ↔ (⟨s.mult, Tuple.key is s.row⟩ : Shape n₁).rowAt N' = g.rowAt N'
        exact Shape.rowAt_eq_shift hV (fun i => hVL s hs' (is i))
          (fun i => Or.inl (Or.inl (hKLv ⟨g, hg, i, rfl⟩))) hn
      · rw [Selection.keepsOpt_shift (keep j) (hs.2.2.1 j) hV (hVk j) (hVL s hs') hn]
    refine ⟨N', OUT, b, ?_, fun n hn => ⟨(h n (le_trans hNN hn)).1, heval n hn⟩⟩
    rintro p ⟨t, ht, j, rfl⟩
    rw [hOUT] at ht
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
    show Fin.append g.row (cnt g.row) j ∈ Univ (AggQueryIn.Gamma is ts fs q keep ord) cγ
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact Univ_mono (q := AggQueryIn.Gamma is ts fs q keep ord) (q' := q)
        (by rw [hcA]; intro a ha; exact Finset.mem_union_right _ ha)
            (fun _ => Set.subset_union_left)
        cγ (hv (hKLv ⟨g, hg, i, rfl⟩))
    · rw [Fin.append_right]
      refine Or.inr ⟨N', fun n hn => Or.inr ⟨ctxAt cγ n,
        (⟨1, Fin.append g.row (cnt g.row)⟩ : Shape (n₁ + n₂)).rowAt n, ?_, i, ?_⟩⟩
      · show Multiset.Mem ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain (dRep n)
          (ctxAt cγ n) : Multiset (Tuple ℕ (n₁ + n₂))) _
        rw [heval n hn]
        exact PolyBag.mem_inst.mpr ⟨_, hOUT ▸ List.mem_map.mpr ⟨g, hg, rfl⟩, by simp, rfl⟩
      · rw [Shape.rowAt_append, Fin.append_right]
  | GammaScalar ts fs q ord ih =>
    rename_i c' m' n₂
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    obtain ⟨N, L, b, hv, h⟩ := (ih hq.2 hs.2.2 hh).1 rfl cγ
    have hfs : ∀ j, fs j = SeqAggFunc.count := fun j => Set.mem_singleton_iff.mp (hs.2.1 j)
    obtain ⟨OUT, hOUT⟩ : ∃ OUT : PolyBag n₂, OUT = [⟨1, fun _ => (L.map Shape.mult).sum⟩] :=
      ⟨_, rfl⟩
    have hOUT1 : ∀ t ∈ OUT, t.mult = 1 := by
      intro t ht
      rw [hOUT, List.mem_singleton] at ht
      rw [ht]
    have hvac : ∀ (S : Multiset (Tuple ℕ m')) (P : Tuple ℕ m' → Fin 0 → Prop)
        [DecidablePred fun u => ∀ k', P u k'], S.filter (fun u => ∀ k', P u k') = S :=
      fun S P _ => Multiset.filter_eq_self.mpr (fun u _ k' => k'.elim0)
    have heval : ∀ n ≥ N, ((AggQueryIn.GammaScalar ts fs q ord).evaluatePlain (dRep n)
        (ctxAt cγ n) : Multiset (Tuple ℕ n₂)) = PolyBag.inst OUT n := by
      intro n hn
      simp only [AggQueryIn.evaluatePlain]
      rw [(h n hn).2, PolyBag.inst_of_ones OUT hOUT1 n, hOUT]
      show Multiset.ofList [_] = Multiset.ofList [_]
      congr 2
      funext j
      show fs j _ = ((L.map Shape.mult).sum).eval n
      rw [hfs j]
      show (List.map _ _).length = _
      erw [List.length_map, ← Multiset.coe_card, ← Relation.groupSeqOptOrd_none,
        Relation.groupSeqOptOrd_coe, hvac, Multiset.filter_eq_self.mpr (fun _ _ => rfl),
        PolyBag.card_inst, Poly.eval_list_sum, List.map_map]
      rfl
    refine ⟨N, OUT, b, ?_, fun n hn => ⟨(h n hn).1, heval n hn⟩⟩
    rintro p ⟨t, ht, j, rfl⟩
    rw [hOUT, List.mem_singleton] at ht
    rw [ht]
    refine Or.inr ⟨N, fun n hn => Or.inr ⟨ctxAt cγ n, fun _ => ((L.map Shape.mult).sum).eval n,
      ?_, j, rfl⟩⟩
    show Multiset.Mem ((AggQueryIn.GammaScalar ts fs q ord).evaluatePlain (dRep n)
      (ctxAt cγ n) : Multiset (Tuple ℕ n₂)) _
    rw [heval n hn, hOUT]
    exact PolyBag.mem_inst.mpr ⟨_, List.mem_singleton_self _, by simp, rfl⟩
  | GammaNest is his p f q ih =>
    rename_i c' m' n₁ κ'
    intro hq hs hh
    refine ⟨fun hl cγ => ?_, fun s m hl => absurd hl (by simp)⟩
    obtain ⟨hp, ⟨g', hsym, hmem, rfl⟩, hsq⟩ := hs
    obtain rfl := Set.mem_singleton_iff.mp hmem
    obtain ⟨N, L, b, hv, h⟩ := (ih hq.2 hsq hh).1 rfl cγ
    obtain ⟨Nd, hNd⟩ := exists_decided (PolyBag.vals_finite L)
    obtain ⟨N', hN'⟩ : ∃ N', N' = max (max N Nd) 1 := ⟨_, rfl⟩
    have hNN : N ≤ N' := hN' ▸ le_trans (le_max_left _ _) (le_max_left _ _)
    have hNdN : Nd ≤ N' := hN' ▸ le_trans (le_max_right _ _) (le_max_left _ _)
    have h1N : 1 ≤ N' := hN' ▸ le_max_right _ _
    have hV : Decided (PolyBag.vals L) N' := hNd.mono hNdN
    have hcA : (AggQueryIn.GammaNest is his p (SeqAggFunc.count.onBag hsym) q).allConsts
        = Union.union p.consts q.allConsts := by
      rw [AggQueryIn.allConsts]
    obtain ⟨KL, hKL⟩ : ∃ KL : PolyBag n₁, KL = dedupAt N' (PolyBag.mapRows (Tuple.key is) L) :=
      ⟨_, rfl⟩
    have hKLv : PolyBag.vals KL ⊆ PolyBag.vals L :=
      hKL ▸ subset_trans (dedupAt_vals _ _) (PolyBag.vals_mapRows_key is L)
    have hKL1 : ∀ g ∈ KL, g.mult = 1 := hKL ▸ dedupAt_mult _ _
    obtain ⟨cnt, hcnt⟩ : ∃ cnt : (Fin n₁ → Poly) → Poly, cnt = fun gr =>
        ((L.filter (fun s => decide (Tuple.key is (s.rowAt N') = (fun i => (gr i).eval N')))).map
          Shape.mult).sum := ⟨_, rfl⟩
    obtain ⟨OUT, hOUT⟩ : ∃ OUT : PolyBag (n₁ + 1),
        OUT = KL.map (fun g => ⟨1, Fin.append g.row (fun _ => cnt g.row)⟩) := ⟨_, rfl⟩
    have hOUT1 : ∀ t ∈ OUT, t.mult = 1 := by
      intro t ht
      rw [hOUT] at ht
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp ht
      rfl
    have heval : ∀ n ≥ N', ((AggQueryIn.GammaNest is his p (SeqAggFunc.count.onBag hsym)
        q).evaluatePlain (dRep n) (ctxAt cγ n) : Multiset (Tuple ℕ (n₁ + 1)))
        = PolyBag.inst OUT n := by
      intro n hn
      have hNn : N ≤ n := le_trans hNN hn
      have h1 : 1 ≤ n := le_trans h1N hn
      simp only [AggQueryIn.evaluatePlain]
      rw [(h n hNn).2]
      have hkeys : (Multiset.map (fun u => (fun k => u (is k) : Tuple ℕ n₁))
          (PolyBag.inst L n)).dedup = PolyBag.inst KL n := by
        rw [PolyBag.inst_mapRows (Tuple.key is) (fun u => (fun k => u (is k) : Tuple ℕ n₁)) L n
          (fun s _ => rfl), hKL]
        exact inst_dedupAt (hV.subset (PolyBag.vals_mapRows_key is L)) _ (subset_refl _) hn h1
      erw [hkeys]
      rw [PolyBag.inst_of_ones KL hKL1 n, Multiset.map_coe, PolyBag.inst_of_ones OUT hOUT1 n, hOUT,
        List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left (fun g hg => ?_)
      show Fin.append (g.rowAt n) _
        = (⟨1, Fin.append g.row (fun _ => cnt g.row)⟩ : Shape (n₁ + 1)).rowAt n
      rw [Shape.rowAt_append]
      refine congrArg₂ Fin.append rfl ?_
      funext j
      show SeqAggFunc.count.onBag hsym (Multiset.map (fun u => p.evalPlain u (ctxAt cγ n))
        (Multiset.filter (fun u => (fun k => u (is k) : Tuple ℕ n₁) = g.rowAt n)
          (PolyBag.inst L n))) = (cnt g.row).eval n
      rw [count_onBag_eq_card, Multiset.card_map, PolyBag.card_filter_inst, hcnt]
      show _ = ((L.filter _ |>.map Shape.mult).sum).eval n
      rw [← sum_if_eq_filter]
      refine congrArg List.sum (List.map_congr_left (fun s hs' => ?_))
      refine if_congr ?_ rfl rfl
      rw [decide_eq_true_iff]
      show (⟨s.mult, Tuple.key is s.row⟩ : Shape n₁).rowAt n = g.rowAt n
        ↔ (⟨s.mult, Tuple.key is s.row⟩ : Shape n₁).rowAt N' = g.rowAt N'
      exact Shape.rowAt_eq_shift hV (fun i => ⟨s, hs', is i, rfl⟩)
        (fun i => hKLv ⟨g, hg, i, rfl⟩) hn
    refine ⟨N', OUT, b, ?_, fun n hn => ⟨(h n (le_trans hNN hn)).1, heval n hn⟩⟩
    rintro p ⟨t, ht, j, rfl⟩
    rw [hOUT] at ht
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ht
    show Fin.append g.row (fun _ => cnt g.row) j
      ∈ Univ (AggQueryIn.GammaNest is his p (SeqAggFunc.count.onBag hsym) q) cγ
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact Univ_mono (q := AggQueryIn.GammaNest is his p (SeqAggFunc.count.onBag hsym) q) (q' := q)
        (by rw [hcA]; intro a ha; exact Finset.mem_union_right _ ha)
            (fun _ => Set.subset_union_left)
        cγ (hv (hKLv ⟨g, hg, i, rfl⟩))
    · rw [Fin.append_right]
      refine Or.inr ⟨N', fun n hn => Or.inr ⟨ctxAt cγ n,
        (⟨1, Fin.append g.row (fun _ => cnt g.row)⟩ : Shape (n₁ + 1)).rowAt n, ?_, ?_⟩⟩
      · show Multiset.Mem ((AggQueryIn.GammaNest is his p (SeqAggFunc.count.onBag hsym)
          q).evaluatePlain (dRep n) (ctxAt cγ n) : Multiset (Tuple ℕ (n₁ + 1))) _
        rw [heval n hn]
        exact PolyBag.mem_inst.mpr ⟨_, hOUT ▸ List.mem_map.mpr ⟨g, hg, rfl⟩, by simp, rfl⟩
      · rw [Shape.rowAt_append, Fin.append_right]
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih => exact fun hq => absurd hq.1 hwin
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq => absurd hq.1 hwin

/-! ## The row -/

/-- **`X − 1` is not a polynomial over `ℕ`**: no `p` has `p + 1 = X`, the
constant coefficients being `p(0) + 1` and `0`. -/
theorem Poly.add_one_ne_X (p : Poly) : p + 1 ≠ Polynomial.X := by
  intro h
  have := congrArg (fun q : Poly => q.coeff 0) h
  simp at this

end WinRow

open WinRow in
/-- **The `win` row of `tab:basisclasses` for the whole algebra, in the
minimal universe**: `win` is in every generating set over `ℕ` with the
counting aggregate. Without a window every query reads the instance of
`n` copies of one row as a bag of polynomial shapes (`sym_aux`), and the
witness – `count(*)` over the whole partition excluding the current row
– writes `n − 1`, which no polynomial over `ℕ` is. -/
theorem win_mem_of_generatesAt {S : Set OpKind}
    (hS : GeneratesAt ℕ schemaR SeqAggFunc.count S winWitness) : OpKind.win ∈ S := by
  classical
  by_contra hwin
  obtain ⟨κ', q', hsch, hu', hsig', he⟩ :=
    hS overSchema_winWitness usesOnly_winWitness inSig_winWitness
  obtain ⟨N, L, b, -, hL⟩ := (sym_aux hwin q' hu' hsig' (q'.hygienic_of_overSchema _ hsch)).1 rfl
    (fun i : Fin 0 => i.elim0)
  -- each shape's aggregate column compared with `X`, from one threshold on
  obtain ⟨N₂, hN₂⟩ := exists_uniform L.toFinset
    (fun N s => Poly.Cmp (s.row (Fin.last 1) + 1) Polynomial.X N)
    (fun _ _ _ hle h => h.mono hle) (fun s _ => Poly.exists_cmp _ _)
  -- at `n₀`, some shape reads `n₀ − 1`
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = max (max N N₂) 1 := ⟨_, rfl⟩
  have h1 : 1 ≤ n₀ := hn₀ ▸ le_max_right _ _
  have hNn : N ≤ n₀ := hn₀ ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hN₂n : N₂ ≤ n₀ := hn₀ ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hctx : ctxAt (fun i : Fin 0 => i.elim0) n₀ = fun _ => 0 := funext (fun i => i.elim0)
  have heq := (hL n₀ hNn).2
  rw [hctx, ← (he.settles (WinRow.dRep n₀) (fun _ => 0) (settlesAt_winWitness _ _)).2,
    evaluatePlain_winWitness] at heq
  have hmem : (Fin.snoc ![1] (n₀ - 1) : Tuple ℕ (1 + 1)) ∈ PolyBag.inst L n₀ := by
    rw [← heq]
    exact Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
  obtain ⟨s, hs, -, hu⟩ := PolyBag.mem_inst.mp hmem
  have hval : (s.row (Fin.last 1)).eval n₀ = n₀ - 1 := by
    have := congrFun hu (Fin.last 1)
    rw [Fin.snoc_last] at this
    exact this.symm
  have hX : (s.row (Fin.last 1) + 1).eval n₀ = Polynomial.X.eval n₀ := by
    rw [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, hval]
    exact Nat.sub_add_cancel h1
  -- so its comparison with `X` is the equality, and the column is `X − 1`
  cases hN₂ s (List.mem_toFinset.mpr hs) with
  | lt h => exact absurd hX (ne_of_lt (h n₀ hN₂n))
  | gt h => exact absurd hX (ne_of_gt (h n₀ hN₂n))
  | eq h => exact Poly.add_one_ne_X _ (Poly.eq_of_eventually_eq ⟨N₂, h⟩)

/-- **The `win` row**: `win` is in every basis of the whole algebra over `ℕ`
with the counting aggregate. -/
theorem win_mem_of_generatesOnRec {S : Set OpKind}
    (hS : GeneratesOnRec ℕ schemaR SeqAggFunc.count S) : OpKind.win ∈ S :=
  win_mem_of_generatesAt (hS _)
