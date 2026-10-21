module

public import Provenance.SymOps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Provenance.SymGamma
import all Provenance.AggQuery
import all Provenance.PlainBasis
import all Provenance.SumByMu
import all Provenance.SymCells
import all Provenance.SymGamma
import all Provenance.SymTerms
import all Provenance.Util.Kleene

/-!
# A bag recursion run against a counter

The table a body apply is tabulated by evaluates the right side at every
type of the parameter row, those no row of the recursive relation ever
has included, and a bag recursion inside the right side may run forever
there. Inside the table, every bag recursion is therefore **bounded**: its
rounds carry a counter, the base the least of a list of counters, and
each round moves the counter to its successor, so that the recursion
stops after as many rounds as there are counters, on every instance. As
long as the original recursion settles within that many rounds – which a
restricted recursion over a bounded set of values does
(`AggQueryIn.mu_eq_muSum_of_valsIn`) – the bounded one computes the same
rows, the counter projected away.

The bounded recursion is `Sym.symMuQ`; every row of a round carries that
round's counter and the recursion stops after the last one
(`Sym.simStep_suf`, `Sym.simStep_last`), and over symbolic rows its slice
under a descriptor is the encoding of the recursion's rows
(`Sym.sliceIs_symMu`).
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

variable {N K : ℕ}

/-- The first block of a row. -/
def pre (x : Tuple T (N + K)) : Tuple T N := fun i => x (Fin.castAdd K i)

/-- The second block of a row. -/
def suf (x : Tuple T (N + K)) : Tuple T K := fun i => x (Fin.natAdd N i)

omit [ValueType T] in
@[simp] private theorem pre_append (r : Tuple T N) (c : Tuple T K) : pre (Fin.append r c) = r := by
  funext i; exact Fin.append_left r c i

omit [ValueType T] in
@[simp] private theorem suf_append (r : Tuple T N) (c : Tuple T K) : suf (Fin.append r c) = c := by
  funext i; exact Fin.append_right r c i

omit [ValueType T] in
@[simp] private theorem append_pre_suf (x : Tuple T (N + K)) : Fin.append (pre x) (suf x) = x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- **The successor relation of a list of counters**: each counter with
the next. -/
def succRel (cs : List (Tuple T K)) : Multiset (Tuple T (K + K)) :=
  ((cs.zip cs.tail).map (fun ab => Fin.append ab.1 ab.2) : List (Tuple T (K + K)))

/-- **A round of the bounded recursion**: the round function on the rows,
each output row moved to the successor of its counter. -/
def simStep (B : Multiset (Tuple T (N + K)) → Multiset (Tuple T (N + K)))
    (S : Multiset (Tuple T (K + K))) (Z : Multiset (Tuple T (N + K))) :
    Multiset (Tuple T (N + K)) :=
  (B Z).bind (fun x => (S.filter (fun ab => pre ab = suf x)).map
    (fun ab => Fin.append (pre x) (suf ab)))

/-- The successor pairs of a list, as a list. -/
private theorem succList_filter :
    ∀ (cs : List (Tuple T K)), cs.Nodup → ∀ (j : ℕ) (hj : j < cs.length),
      ((cs.zip cs.tail).map (fun ab => (Fin.append ab.1 ab.2 : Tuple T (K + K)))).filter
          (fun ab => decide (pre ab = cs[j]))
        = if h : j + 1 < cs.length then [Fin.append cs[j] cs[j + 1]] else []
  | List.nil, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | List.cons x List.nil, _, j, hj => by
    have : j = 0 := by simp at hj; omega
    subst this
    simp
  | List.cons x (List.cons y zs), hnd, j, hj => by
    have hx : x ∉ y :: zs := (List.nodup_cons.mp hnd).1
    have hnd' : (y :: zs).Nodup := (List.nodup_cons.mp hnd).2
    have hz : (x :: y :: zs).zip (x :: y :: zs).tail = (x, y) :: (y :: zs).zip (y :: zs).tail := by
      simp
    rw [hz, List.map_cons, List.filter_cons]
    cases j with
    | zero =>
      simp only [pre_append, List.getElem_cons_zero, decide_true, ite_true]
      rw [dite_eq_left (by simp)]
      congr 1
      refine List.filter_eq_nil_iff.mpr (fun ab hab => ?_)
      obtain ⟨⟨a, b⟩, hmem, rfl⟩ := List.mem_map.mp hab
      have ha : a ∈ y :: zs := (List.of_mem_zip hmem).1
      simp only [pre_append, decide_eq_true_eq]
      exact fun h => hx (h ▸ ha)
    | succ j =>
      have hne : ¬ (x = (x :: y :: zs)[j + 1]) := fun h => hx (by
        rw [h, List.getElem_cons_succ]; exact List.getElem_mem _)
      simp only [pre_append, hne, decide_false, Bool.false_eq_true, ite_false]
      have hj' : j < (y :: zs).length := by simp at hj ⊢; omega
      have := succList_filter (y :: zs) hnd' j hj'
      simp only [List.getElem_cons_succ] at this ⊢
      rw [this]
      by_cases hl : j + 1 < (y :: zs).length
      · rw [dite_eq_left hl, dite_eq_left (by simp at hl ⊢; omega)]
      · rw [dite_eq_right hl, dite_eq_right (by simp at hl ⊢; omega)]

/-- **The successors of a counter of the list**: the next one, or none
after the last. -/
private theorem succRel_filter (cs : List (Tuple T K)) (hnd : cs.Nodup) (j : ℕ) (hj : j < cs.length) :
    (succRel cs).filter (fun ab => pre ab = cs[j])
      = if h : j + 1 < cs.length then {Fin.append cs[j] cs[j + 1]} else 0 := by
  unfold succRel
  rw [Multiset.filter_coe, succList_filter cs hnd j hj]
  split <;> rfl

omit [ValueType T] in
private theorem muSum_eq_sum' {α : Type} (step : Multiset α → Multiset α) :
    ∀ (k : ℕ) (M : Multiset α), muSum step k M = ∑ j ∈ Finset.range (k + 1), step^[j] M
  | 0, M => by simp [muSum]
  | k + 1, M => by
    rw [muSum, muSum_eq_sum' step k (step M), Finset.sum_range_succ' _ (k + 1)]
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
    exact add_comm _ _

/-! ## The bounded recursion as a query -/

section Query

variable {c : ℕ}

omit [ValueType T] in
theorem appendKinds (a b : ℕ) :
    Fin.append (ColKind.allReg a) (ColKind.allReg b) = ColKind.allReg (a + b) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- The product of two all-regular queries, all-regular. -/
def prodR {l₁ l₂ : List (String × ℕ)} {a b : ℕ} (q₁ : AggQueryIn T c a (ColKind.allReg a) l₁)
    (q₂ : AggQueryIn T c b (ColKind.allReg b) l₂) : AggQueryIn T c (a + b) (ColKind.allReg (a + b))
    (l₁ ++ l₂) :=
  (AggQueryIn.Prod q₁ q₂).castKind (appendKinds a b)

private theorem evaluatePlain_prodR {l₁ l₂ : List (String × ℕ)} {a b : ℕ}
    (q₁ : AggQueryIn T c a (ColKind.allReg a) l₁) (q₂ : AggQueryIn T c b (ColKind.allReg b) l₂)
    (D : Database T) (γ : Fin c → T) :
    ((prodR q₁ q₂).evaluatePlain D γ : Multiset (Tuple T (a + b)))
      = (q₁.evaluatePlain D γ : Multiset (Tuple T a)).bind (fun r =>
          (q₂.evaluatePlain D γ : Multiset (Tuple T b)).map (fun r' => Fin.append r r')) := by
  rw [prodR, AggQueryIn.evaluatePlain_castKind]
  show q₁.evaluatePlain D γ * q₂.evaluatePlain D γ = _
  rw [Relation.hMul_eq_bind]

/-- **The counters of a round and of the successor agree.** -/
def ctrEqSP : SP T c ((N + K) + (K + K)) :=
  andAll ((List.finRange K).map (fun i =>
    .atom .syneq (.col (Fin.castAdd (K + K) (Fin.natAdd N i)))
      (.col (Fin.natAdd (N + K) (Fin.castAdd K i)))))

private theorem eval3_ctrEqSP (x : Tuple T (N + K)) (ab : Tuple T (K + K)) (γ : Fin c → T) :
    (ctrEqSP (N := N) (K := K)).eval3 (Fin.append x ab) γ
      = Kleene.ofBool (decide (pre ab = suf x)) := by
  unfold ctrEqSP
  rw [eval3_andAll _ _ _ (fun p hp => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    rw [eval3_atom_syneq]; exact ofBool_definite _)]
  refine ofBool_congr ?_
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, eval3_atom_syneq, Kleene.ofBool_eq_true_iff, decide_eq_true_eq,
    SA.eval, Fin.append_left, Fin.append_right]
  constructor
  · intro h; funext i; exact (h i).symm
  · intro h i; exact (congrFun h i).symm

/-- The columns a bounded round keeps: the row's, and the successor's
counter. -/
def stepCols : Fin (N + K) → SA T c ((N + K) + (K + K)) :=
  Fin.addCases (fun i => .col (Fin.castAdd (K + K) (Fin.castAdd K i)))
    (fun z => .col (Fin.natAdd (N + K) (Fin.natAdd K z)))

omit [ValueType T] in
private theorem eval_stepCols (x : Tuple T (N + K)) (ab : Tuple T (K + K)) (γ : Fin c → T) :
    (fun i => (stepCols (N := N) (K := K) i).eval (Fin.append x ab) γ)
      = Fin.append (pre x) (suf ab) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun z => ?_) i
  · simp only [stepCols, Fin.addCases_left, SA.eval, Fin.append_left]; rfl
  · simp only [stepCols, Fin.addCases_right, SA.eval, Fin.append_right]; rfl

/-- **A round of the bounded recursion**, as a query: the body's rows whose
counter has a successor, moved to it. -/
def stepQ (s : String) (Bq : AggQueryIn T c (N + K) (ColKind.allReg (N + K)) [(s, N + K)])
    (Sq : AggQueryIn T c (K + K) (ColKind.allReg (K + K))) :
    AggQueryIn T c (N + K) (ColKind.allReg (N + K)) [(s, N + K)] :=
  (AggQueryIn.Proj (projSA stepCols)
    (AggQueryIn.Sel (ctrEqSP).toGen (prodR Bq Sq)
      (SelOK.of_noAggAtom (SP.hasAggAtom_toGen _)))).castKind
    (projSA_kind _)

private theorem evaluatePlain_stepQ (s : String)
    (Bq : AggQueryIn T c (N + K) (ColKind.allReg (N + K)) [(s, N + K)])
    (Sq : AggQueryIn T c (K + K) (ColKind.allReg (K + K))) (D : Database T) (γ : Fin c → T) :
    ((stepQ s Bq Sq).evaluatePlain D γ : Multiset (Tuple T (N + K)))
      = simStep (fun _ => (Bq.evaluatePlain D γ : Multiset (Tuple T (N + K))))
          (Sq.evaluatePlain D γ) 0 := by
  rw [stepQ, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u j => (projSA stepCols j).evalPlain u γ)
    (Multiset.filter (fun u => ctrEqSP.toGen.holdsPlain u γ)
      ((prodR Bq Sq).evaluatePlain D γ)) = _
  rw [evaluatePlain_prodR, simStep, Multiset.filter_bind, Multiset.map_bind]
  refine Multiset.bind_congr (fun x _ => ?_)
  rw [Multiset.filter_map, Multiset.map_map]
  congr 1
  · funext ab
    simp only [Function.comp, evalPlain_projSA]
    exact eval_stepCols x ab γ
  · refine Multiset.filter_congr (fun ab _ => ?_)
    simp only [Function.comp, GenPredIn.holdsPlain, SP.evalPlain3_toGen, eval3_ctrEqSP,
      Kleene.ofBool_eq_true_iff, decide_eq_true_eq]

/-- **The bounded recursion**: the base paired with the least counter, each
round moved to the next counter, the counter projected away. -/
def symMuQ (s : String) (Q₀ : AggQueryIn T c N (ColKind.allReg N))
    (Bq : AggQueryIn T c (N + K) (ColKind.allReg (N + K)) [(s, N + K)])
    (Lq : AggQueryIn T c K (ColKind.allReg K))
    (Sq : AggQueryIn T c (K + K) (ColKind.allReg (K + K))) :
    AggQueryIn T c N (ColKind.allReg N) :=
  (AggQueryIn.Proj (projSA (fun i : Fin N => (.col (Fin.castAdd K i) : SA T c (N + K))))
    (AggQueryIn.Mu s (prodR Q₀ Lq) (stepQ s Bq Sq))).castKind (projSA_kind _)

/-- **The bounded recursion, read as a fixpoint** of its round on the
rows. -/
private theorem evaluatePlain_symMuQ_fix (s : String) (Q₀ : AggQueryIn T c N (ColKind.allReg N))
    (Bq : AggQueryIn T c (N + K) (ColKind.allReg (N + K)) [(s, N + K)])
    (Lq : AggQueryIn T c K (ColKind.allReg K))
    (Sq : AggQueryIn T c (K + K) (ColKind.allReg (K + K)))
    (hS : Sq.noMention s) (D : Database T) (γ : Fin c → T) :
    ((symMuQ s Q₀ Bq Lq Sq).evaluatePlain D γ : Multiset (Tuple T N))
      = (muSumFix (simStep (fun Z => (Bq.evaluatePlain (D.assign s Z) γ
          : Multiset (Tuple T (N + K)))) (Sq.evaluatePlain D γ))
          ((prodR Q₀ Lq).evaluatePlain D γ)).map pre := by
  rw [symMuQ, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u j => (projSA (fun i : Fin N =>
      (.col (Fin.castAdd K i) : SA T c (N + K))) j).evalPlain u γ)
    (muSumFix (fun X => (stepQ s Bq Sq).evaluatePlain (D.assign s X) γ)
      ((prodR Q₀ Lq).evaluatePlain D γ)) = _
  have hpre : (fun u : Tuple T (N + K) => fun j => (projSA (fun i : Fin N =>
      (.col (Fin.castAdd K i) : SA T c (N + K))) j).evalPlain u γ) = pre := by
    funext u j
    rw [evalPlain_projSA]; rfl
  rw [hpre]
  congr 1
  refine muSumFix_congr (fun X => ?_) rfl
  rw [evaluatePlain_stepQ, simStep, simStep,
    AggQueryIn.evaluatePlain_assign_of_noMention X Sq hS D γ]

end Query

/-! ## The rounds of the bounded recursion, round by round -/

section Rounds

/-- **Every row of a round carries that round's counter**, and there are
no rows past the last counter, as long as the round function keeps each
row's counter. -/
theorem simStep_suf (B : Multiset (Tuple T (N + K)) → Multiset (Tuple T (N + K)))
    (hpres : ∀ Y, ∀ y ∈ B Y, ∃ x ∈ Y, suf x = suf y) (cs : List (Tuple T K)) (hnd : cs.Nodup)
    (Z₀ : Multiset (Tuple T (N + K))) (hne : 0 < cs.length) (h₀ : ∀ z ∈ Z₀, suf z = cs[0]) :
    ∀ j, ∀ z ∈ (simStep B (succRel cs))^[j] Z₀, ∃ h : j < cs.length, suf z = cs[j] := by
  intro j
  induction j with
  | zero => exact fun z hz => ⟨hne, h₀ z hz⟩
  | succ j ih =>
    intro z hz
    rw [Function.iterate_succ_apply'] at hz
    have hz' : z ∈ (B ((simStep B (succRel cs))^[j] Z₀)).bind (fun x =>
        ((succRel cs).filter (fun ab => pre ab = suf x)).map
          (fun ab => Fin.append (pre x) (suf ab))) := hz
    obtain ⟨y, hy, hz⟩ := Multiset.mem_bind.mp hz'
    obtain ⟨x, hx, hxy⟩ := hpres _ y hy
    obtain ⟨hj, hxj⟩ := ih x hx
    rw [hxy] at hxj
    rw [hxj, succRel_filter cs hnd j hj] at hz
    by_cases hj' : j + 1 < cs.length
    · rw [dite_eq_left hj', Multiset.map_singleton, Multiset.mem_singleton] at hz
      exact ⟨hj', by rw [hz, suf_append, suf_append]⟩
    · rw [dite_eq_right hj'] at hz
      exact absurd hz (Multiset.notMem_zero _)

/-- **The bounded recursion stops after the last counter.** -/
theorem simStep_last (B : Multiset (Tuple T (N + K)) → Multiset (Tuple T (N + K)))
    (hpres : ∀ Y, ∀ y ∈ B Y, ∃ x ∈ Y, suf x = suf y) (cs : List (Tuple T K)) (hnd : cs.Nodup)
    (Z₀ : Multiset (Tuple T (N + K))) (hne : 0 < cs.length) (h₀ : ∀ z ∈ Z₀, suf z = cs[0]) :
    (simStep B (succRel cs))^[cs.length] Z₀ = 0 :=
  Multiset.eq_zero_of_forall_notMem (fun z hz => by
    obtain ⟨h, -⟩ := simStep_suf B hpres cs hnd Z₀ hne h₀ _ z hz
    exact lt_irrefl _ h)

end Rounds

/-! ## The symbolic bounded recursion's slices -/

section SliceSim

variable {k c n : ℕ} {C : Finset T}

omit [ValueType T] in
private theorem descP_pre {K' : ℕ} (x : Tuple T ((k + n) * (7 + k) + K')) :
    descP (P := 0) (pre x : Tuple T ((k + n) * (7 + k))) = descP (P := K') x := by
  funext y
  simp only [descP, ofCells, pre]
  rfl

/-- **The rounds of the symbolic bounded recursion, under a descriptor**:
the encodings of the recursion's rounds, each with its counter. -/
private theorem slice_simStep {par : Fin k → T} {K' : ℕ}
    (B : Multiset (Tuple T ((k + n) * (7 + k) + K')) → Multiset (Tuple T ((k + n) * (7 + k) + K')))
    (step : Multiset (Tuple T n) → Multiset (Tuple T n))
    (cs : List (Tuple T K')) (hnd : cs.Nodup) (hne : 0 < cs.length)
    (Z₀ : Multiset (Tuple T ((k + n) * (7 + k) + K'))) (X₀ : Multiset (Tuple T n))
    (hbody : ∀ j, LT.lt (j + 1) cs.length → ∀ (Y : Multiset (Tuple T ((k + n) * (7 + k) + K')))
      (e : Tuple T K'), SliceIs C par Y ((step^[j] X₀).map (fun v => (v, e))) →
      SliceIs C par (B Y) ((step (step^[j] X₀)).map (fun v => (v, e))))
    (h₀ : SliceIs C par Z₀ (X₀.map (fun v => (v, cs[0])))) :
    ∀ j (hj : j < cs.length), SliceIs C par ((simStep B (succRel cs))^[j] Z₀)
      ((step^[j] X₀).map (fun v => (v, cs[j]))) := by
  intro j
  induction j with
  | zero => exact fun _ => h₀
  | succ j ih =>
    intro hj1
    have hj : j < cs.length := by omega
    have hB := hbody j hj1 _ cs[j] (ih hj)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    unfold SliceIs at hB ⊢
    show slice ((B _).bind _) _ = _
    unfold slice at hB ⊢
    rw [Multiset.filter_bind]
    have hpart : ∀ x : Tuple T ((k + n) * (7 + k) + K'),
        Multiset.filter (fun r => descP (P := K') r = descEnc C par)
          (((succRel cs).filter (fun ab => pre ab = suf x)).map
            (fun ab => Fin.append (pre x) (suf ab)))
        = if descP (P := K') x = descEnc C par then
            ((succRel cs).filter (fun ab => pre ab = suf x)).map
              (fun ab => Fin.append (pre x) (suf ab)) else 0 := by
      intro x
      have hd : ∀ ab : Tuple T (K' + K'),
          descP (P := K') (Fin.append (pre x) (suf ab) : Tuple T _) = descP (P := K') x := by
        intro ab
        rw [← descP_pre (Fin.append (pre x) (suf ab) : Tuple T _), pre_append, descP_pre]
      split
      · rename_i h
        exact Multiset.filter_eq_self.mpr (fun r hr => by
          obtain ⟨ab, -, rfl⟩ := Multiset.mem_map.mp hr
          rw [hd]; exact h)
      · rename_i h
        exact Multiset.filter_eq_nil.mpr (fun r hr hr' => by
          obtain ⟨ab, -, rfl⟩ := Multiset.mem_map.mp hr
          rw [hd] at hr'; exact h hr')
    simp only [hpart]
    rw [AggQueryIn.Multiset.bind_ite (fun x => descP (P := K') x = descEnc C par), hB, encAll,
      encAll, Multiset.map_map, Multiset.map_map, Multiset.bind_map]
    rw [← Multiset.bind_singleton]
    refine Multiset.bind_congr (fun v _ => ?_)
    simp only [Function.comp, rowEncP, suf_append, pre_append]
    rw [succRel_filter cs hnd j hj, dite_eq_left hj1, Multiset.map_singleton, suf_append]

/-- A relation with no further columns, its slice as encoded rows. -/
private theorem sliceIs_zero_iff {par : Fin k → T} (Q : Multiset (Tuple T ((k + n) * (7 + k))))
    (X : Multiset (Tuple T n)) :
    SliceIs (P := 0) C par Q (X.map (fun v => (v, (Fin.elim0 : Tuple T 0))))
      ↔ Q.filter (fun r => descP (P := 0) r = descEnc C par) = X.map (rowEnc C par) := by
  unfold SliceIs slice encAll
  rw [Multiset.map_map]
  have : ((fun x : Tuple T n × Tuple T 0 => rowEncP C par x.1 x.2) ∘
      (fun v => (v, (Fin.elim0 : Tuple T 0)))) = rowEnc C par :=
    funext fun v => rowEncP_elim0 C par v
  rw [this]

/-- **The symbolic bounded recursion's slice**: the encodings of the
recursion's rows, wherever the recursion settles within as many rounds as
there are counters and its rounds hold good values. -/
theorem sliceIs_symMu {par : Fin k → T} {K' : ℕ} (s : String)
    (Q₀ : AggQueryIn T c ((k + n) * (7 + k)) (ColKind.allReg ((k + n) * (7 + k))))
    (Bq : AggQueryIn T c ((k + n) * (7 + k) + K') (ColKind.allReg ((k + n) * (7 + k) + K'))
      [(s, (k + n) * (7 + k) + K')])
    (Lq : AggQueryIn T c K' (ColKind.allReg K'))
    (Sq : AggQueryIn T c (K' + K') (ColKind.allReg (K' + K')))
    (hS : Sq.noMention s) (D : Database T) (γ : Fin c → T)
    (step : Multiset (Tuple T n) → Multiset (Tuple T n)) (X₀ : Multiset (Tuple T n))
    (hQ₀ : SliceIs (P := 0) C par (Q₀.evaluatePlain D γ) (X₀.map (fun v => (v, Fin.elim0))))
    (hpres : ∀ (Y : Multiset (Tuple T ((k + n) * (7 + k) + K')))
      (y : Tuple T ((k + n) * (7 + k) + K')), Multiset.Mem (Bq.evaluatePlain (D.assign s Y) γ) y →
      ∃ x ∈ Y, suf x = suf y)
    (cs : List (Tuple T K')) (hnd : cs.Nodup) (hne : 0 < cs.length)
    (hbody : ∀ j, LT.lt (j + 1) cs.length → ∀ (Y : Multiset (Tuple T ((k + n) * (7 + k) + K')))
      (e : Tuple T K'), SliceIs C par Y ((step^[j] X₀).map (fun v => (v, e))) →
      SliceIs C par (Bq.evaluatePlain (D.assign s Y) γ)
        ((step (step^[j] X₀)).map (fun v => (v, e))))
    (hLv : Lq.evaluatePlain D γ = ({cs[0]} : Multiset (Tuple T K')))
    (hSv : Sq.evaluatePlain D γ = (succRel cs : Multiset (Tuple T (K' + K'))))
    (h0 : step 0 = 0) (hset : step^[cs.length] X₀ = 0) :
    SliceIs (P := 0) C par ((symMuQ s Q₀ Bq Lq Sq).evaluatePlain D γ)
      ((muSumFix step X₀).map (fun v => (v, Fin.elim0))) := by
  rw [sliceIs_zero_iff, evaluatePlain_symMuQ_fix s Q₀ Bq Lq Sq hS D γ]
  erw [hSv]
  set B : Multiset (Tuple T ((k + n) * (7 + k) + K')) → Multiset (Tuple T ((k + n) * (7 + k) + K'))
    := fun Z => Bq.evaluatePlain (D.assign s Z) γ with hBdef
  -- the base: the base's rows with the least counter
  have hbase : ((prodR Q₀ Lq).evaluatePlain D γ : Multiset _)
      = (Q₀.evaluatePlain D γ : Multiset (Tuple T ((k + n) * (7 + k)))).map
          (fun r => Fin.append r cs[0]) := by
    rw [evaluatePlain_prodR]
    erw [hLv]
    simp only [Multiset.map_singleton]
    exact Multiset.bind_singleton _ _
  rw [hbase]
  have hsuf0 : ∀ z ∈ (Q₀.evaluatePlain D γ : Multiset (Tuple T ((k + n) * (7 + k)))).map
      (fun r => Fin.append r cs[0]), suf z = cs[0] := by
    intro z hz
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hz
    exact suf_append r _
  have hz0 : SliceIs C par ((Q₀.evaluatePlain D γ : Multiset (Tuple T ((k + n) * (7 + k)))).map
      (fun r => Fin.append r cs[0])) (X₀.map (fun v => (v, cs[0]))) := by
    have h := (sliceIs_zero_iff _ _).mp hQ₀
    unfold SliceIs slice encAll
    rw [Multiset.filter_map]
    have hdesc : Multiset.filter ((fun r => descP (P := K') r = descEnc C par) ∘
        (fun r : Tuple T ((k + n) * (7 + k)) => (Fin.append r cs[0] : Tuple T _)))
          (Q₀.evaluatePlain D γ)
        = Multiset.filter (fun r => descP (P := 0) r = descEnc C par) (Q₀.evaluatePlain D γ) :=
      Multiset.filter_congr (fun r _ => by
        simp only [Function.comp]
        rw [← descP_pre (Fin.append r cs[0] : Tuple T _), pre_append])
    erw [hdesc, h]
    rw [Multiset.map_map, Multiset.map_map]
    rfl
  -- it stops after the last counter
  have hlast := simStep_last B (fun Y y hy => hpres Y y hy) cs hnd _ hne hsuf0
  have hzero : simStep B (succRel cs) 0 = 0 := by
    unfold simStep
    have : B 0 = 0 := Multiset.eq_zero_of_forall_notMem (fun y hy => by
      obtain ⟨x, hx, -⟩ := hpres 0 y hy
      exact Multiset.notMem_zero _ hx)
    rw [this, Multiset.zero_bind]
  have hL : cs.length.pred + 1 = cs.length := Nat.succ_pred_eq_of_pos hne
  erw [muSumFix_eq_of_empty hzero (k := cs.length.pred) (by rw [hL]; exact hlast)]
  rw [muSumFix_eq_of_empty h0 (k := cs.length.pred) (by rw [hL]; exact hset),
    muSum_eq_sum', muSum_eq_sum']
  -- round by round
  have hround := slice_simStep B step cs hnd hne _ X₀ (fun j hj Y e hY => hbody j hj Y e hY) hz0
  have hj : ∀ j, LT.lt j cs.length →
      Multiset.filter (fun r => descP (P := 0) r = descEnc C par)
        (((simStep B (succRel cs))^[j] ((Q₀.evaluatePlain D γ
          : Multiset (Tuple T ((k + n) * (7 + k)))).map (fun r => Fin.append r cs[0]))).map pre)
      = (step^[j] X₀).map (rowEnc C par) := by
    intro j hjl
    have h := hround j hjl
    unfold SliceIs slice encAll at h
    rw [Multiset.filter_map]
    have hf : Multiset.filter ((fun r => descP (P := 0) r = descEnc C par) ∘
        (pre : Tuple T ((k + n) * (7 + k) + K') → Tuple T ((k + n) * (7 + k))))
          ((simStep B (succRel cs))^[j] ((Q₀.evaluatePlain D γ
            : Multiset (Tuple T ((k + n) * (7 + k)))).map (fun r => Fin.append r cs[0])))
        = Multiset.filter (fun r => descP (P := K') r = descEnc C par)
          ((simStep B (succRel cs))^[j] ((Q₀.evaluatePlain D γ
            : Multiset (Tuple T ((k + n) * (7 + k)))).map (fun r => Fin.append r cs[0]))) :=
      Multiset.filter_congr (fun r _ => by simp only [Function.comp, descP_pre])
    rw [hf, h, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    simp only [Function.comp, rowEncP, pre_append]
  have hsum : ∀ L, LE.le (L + 1) cs.length →
      Multiset.filter (fun r => descP (P := 0) r = descEnc C par)
        ((∑ j ∈ Finset.range (L + 1), (simStep B (succRel cs))^[j] ((Q₀.evaluatePlain D γ
          : Multiset (Tuple T ((k + n) * (7 + k)))).map (fun r => Fin.append r cs[0]))).map pre)
      = (∑ j ∈ Finset.range (L + 1), step^[j] X₀).map (rowEnc C par) := by
    intro L hL'
    induction L with
    | zero => simpa using hj 0 hne
    | succ L ih =>
      rw [Finset.sum_range_succ (fun j => (simStep B (succRel cs))^[j] _) (L + 1),
        Finset.sum_range_succ (fun j => step^[j] X₀) (L + 1), Multiset.map_add,
        Multiset.filter_add, Multiset.map_add, ih (by omega), hj (L + 1) (by omega)]
  exact hsum _ (by omega)

end SliceSim

end Sym
