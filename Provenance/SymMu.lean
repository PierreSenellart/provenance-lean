import Provenance.SymWin

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

This file is the multiset-level part: the rounds of the bounded recursion
(`Sym.simStep_iterate`) and its value (`Sym.muSumFix_simStep`), for a
round function that carries the counter untouched.
-/

variable {T : Type} [ValueType T]

namespace Sym

variable {N K : ℕ}

/-- The first block of a row. -/
def pre (x : Tuple T (N + K)) : Tuple T N := fun i => x (Fin.castAdd K i)

/-- The second block of a row. -/
def suf (x : Tuple T (N + K)) : Tuple T K := fun i => x (Fin.natAdd N i)

omit [ValueType T] in
@[simp] theorem pre_append (r : Tuple T N) (c : Tuple T K) : pre (Fin.append r c) = r := by
  funext i; exact Fin.append_left r c i

omit [ValueType T] in
@[simp] theorem suf_append (r : Tuple T N) (c : Tuple T K) : suf (Fin.append r c) = c := by
  funext i; exact Fin.append_right r c i

omit [ValueType T] in
@[simp] theorem append_pre_suf (x : Tuple T (N + K)) : Fin.append (pre x) (suf x) = x := by
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
theorem succList_filter :
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
theorem succRel_filter (cs : List (Tuple T K)) (hnd : cs.Nodup) (j : ℕ) (hj : j < cs.length) :
    (succRel cs).filter (fun ab => pre ab = cs[j])
      = if h : j + 1 < cs.length then {Fin.append cs[j] cs[j + 1]} else 0 := by
  unfold succRel
  rw [Multiset.filter_coe, succList_filter cs hnd j hj]
  split <;> rfl

omit [ValueType T] in
theorem muSum_eq_sum' {α : Type} (step : Multiset α → Multiset α) :
    ∀ (k : ℕ) (M : Multiset α), muSum step k M = ∑ j ∈ Finset.range (k + 1), step^[j] M
  | 0, M => by simp [muSum]
  | k + 1, M => by
    rw [muSum, muSum_eq_sum' step k (step M), Finset.sum_range_succ' _ (k + 1)]
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
    exact add_comm _ _

/-- **The rounds of the bounded recursion**: the underlying rounds, each
with the counter of its index, as long as there is one. -/
theorem simStep_iterate (B : Multiset (Tuple T (N + K)) → Multiset (Tuple T (N + K)))
    (B₀ : Multiset (Tuple T N) → Multiset (Tuple T N))
    (hB : ∀ Y c, B (Y.map (fun r => Fin.append r c)) = (B₀ Y).map (fun r => Fin.append r c))
    (hB0 : B₀ 0 = 0) (cs : List (Tuple T K)) (hnd : cs.Nodup) (hne : 0 < cs.length)
    (P₀ : Multiset (Tuple T N)) :
    ∀ j, (simStep B (succRel cs))^[j] (P₀.map (fun r => Fin.append r cs[0]))
      = if h : j < cs.length then (B₀^[j] P₀).map (fun r => Fin.append r cs[j]) else 0 := by
  have hBz : B 0 = 0 := by
    have := hB 0 cs[0]
    rw [Multiset.map_zero, hB0, Multiset.map_zero] at this
    exact this
  intro j
  induction j with
  | zero => rw [dite_eq_left hne]; rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < cs.length
    · rw [dite_eq_left hj]
      unfold simStep
      rw [hB, Multiset.bind_map, Function.iterate_succ_apply']
      simp only [suf_append, pre_append]
      rw [succRel_filter cs hnd j hj]
      by_cases hj' : j + 1 < cs.length
      · rw [dite_eq_left hj', dite_eq_left hj']
        simp only [Multiset.map_singleton, suf_append, Multiset.bind_singleton]
      · rw [dite_eq_right hj', dite_eq_right (by omega)]
        simp only [Multiset.map_zero, Multiset.bind_zero]
    · rw [dite_eq_right hj, dite_eq_right (by omega)]
      unfold simStep
      rw [hBz, Multiset.zero_bind]

/-- **The bounded recursion is the sum of the underlying rounds**, as many
as there are counters, each with its counter. -/
theorem muSumFix_simStep (B : Multiset (Tuple T (N + K)) → Multiset (Tuple T (N + K)))
    (B₀ : Multiset (Tuple T N) → Multiset (Tuple T N))
    (hB : ∀ Y c, B (Y.map (fun r => Fin.append r c)) = (B₀ Y).map (fun r => Fin.append r c))
    (hB0 : B₀ 0 = 0) (cs : List (Tuple T K)) (hnd : cs.Nodup) (hne : 0 < cs.length)
    (P₀ : Multiset (Tuple T N)) :
    (muSumFix (simStep B (succRel cs)) (P₀.map (fun r => Fin.append r cs[0]))).map pre
      = muSum B₀ cs.length.pred P₀ := by
  have hBz : B 0 = 0 := by
    have := hB 0 cs[0]
    rw [Multiset.map_zero, hB0, Multiset.map_zero] at this
    exact this
  have h0 : simStep B (succRel cs) 0 = 0 := by
    unfold simStep; rw [hBz, Multiset.zero_bind]
  have hlast : (simStep B (succRel cs))^[cs.length.pred + 1] (P₀.map (fun r => Fin.append r cs[0]))
      = 0 := by
    have := Nat.succ_pred_eq_of_pos hne
    rw [simStep_iterate B B₀ hB hB0 cs hnd hne P₀, dite_eq_right (by omega)]
  rw [muSumFix_eq_of_empty h0 hlast, muSum_eq_sum', muSum_eq_sum',
    ← Multiset.mapAddMonoidHom_apply, map_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have := Nat.succ_pred_eq_of_pos hne
  rw [Multiset.mapAddMonoidHom_apply, simStep_iterate B B₀ hB hB0 cs hnd hne P₀,
    dite_eq_left (by omega), Multiset.map_map]
  simp [Function.comp]

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

theorem evaluatePlain_prodR {l₁ l₂ : List (String × ℕ)} {a b : ℕ}
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

theorem eval3_ctrEqSP (x : Tuple T (N + K)) (ab : Tuple T (K + K)) (γ : Fin c → T) :
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
theorem eval_stepCols (x : Tuple T (N + K)) (ab : Tuple T (K + K)) (γ : Fin c → T) :
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

theorem evaluatePlain_stepQ (s : String)
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

/-- **What the bounded recursion computes**: the underlying rounds summed,
as many as there are counters. -/
theorem evaluatePlain_symMuQ (s : String) (Q₀ : AggQueryIn T c N (ColKind.allReg N))
    (Bq : AggQueryIn T c (N + K) (ColKind.allReg (N + K)) [(s, N + K)])
    (Lq : AggQueryIn T c K (ColKind.allReg K))
    (Sq : AggQueryIn T c (K + K) (ColKind.allReg (K + K)))
    (hS : Sq.noMention s) (D : Database T) (γ : Fin c → T)
    (B₀ : Multiset (Tuple T N) → Multiset (Tuple T N))
    (hB : ∀ Y c', (Bq.evaluatePlain (D.assign s (Y.map (fun r => Fin.append r c'))) γ
        : Multiset (Tuple T (N + K))) = (B₀ Y).map (fun r => Fin.append r c'))
    (hB0 : B₀ 0 = 0) (cs : List (Tuple T K)) (hnd : cs.Nodup) (hne : 0 < cs.length)
    (hLv : Lq.evaluatePlain D γ = ({cs[0]} : Multiset (Tuple T K)))
    (hSv : Sq.evaluatePlain D γ = (succRel cs : Multiset (Tuple T (K + K)))) :
    ((symMuQ s Q₀ Bq Lq Sq).evaluatePlain D γ : Multiset (Tuple T N))
      = muSum B₀ cs.length.pred (Q₀.evaluatePlain D γ) := by
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
  have hstep : ∀ X : Relation T (N + K),
      ((stepQ s Bq Sq).evaluatePlain (D.assign s X) γ : Multiset (Tuple T (N + K)))
        = simStep (fun Z => (Bq.evaluatePlain (D.assign s Z) γ : Multiset (Tuple T (N + K))))
            (succRel cs) X := by
    intro X
    rw [evaluatePlain_stepQ, simStep, simStep,
      AggQueryIn.evaluatePlain_assign_of_noMention X Sq hS D γ, hSv]
  have hbase : ((prodR Q₀ Lq).evaluatePlain D γ : Multiset (Tuple T (N + K)))
      = (Q₀.evaluatePlain D γ : Multiset (Tuple T N)).map (fun r => Fin.append r cs[0]) := by
    rw [evaluatePlain_prodR]
    erw [hLv]
    simp only [Multiset.map_singleton]
    exact Multiset.bind_singleton _ _
  rw [muSumFix_congr (fun X => hstep X) hbase]
  exact muSumFix_simStep _ B₀ hB hB0 cs hnd hne _

end Query

/-! ## The bounded recursion over symbolic rows -/

section SliceMu

variable {k c n : ℕ} {C : Finset T}

/-- **The symbolic bounded recursion's rows under a descriptor** are the
encodings of the recursion's rows, wherever the recursion settles within
as many rounds as there are counters and its rounds hold good values. -/
theorem slice_muSum {par : Fin k → T}
    (B₀ : Multiset (Tuple T ((k + n) * (7 + k))) → Multiset (Tuple T ((k + n) * (7 + k))))
    (step : Multiset (Tuple T n) → Multiset (Tuple T n))
    (hbody : ∀ (Y : Multiset (Tuple T ((k + n) * (7 + k)))) (X : Multiset (Tuple T n)),
      (∀ v ∈ X, ∀ i, GoodVal (C := C) par (v i)) →
      Y.filter (fun r => descP (P := 0) r = descEnc C par) = X.map (rowEnc C par) →
      (B₀ Y).filter (fun r => descP (P := 0) r = descEnc C par) = (step X).map (rowEnc C par))
    (P₀ : Multiset (Tuple T ((k + n) * (7 + k)))) (X₀ : Multiset (Tuple T n))
    (h₀ : P₀.filter (fun r => descP (P := 0) r = descEnc C par) = X₀.map (rowEnc C par))
    (hgood : ∀ j, ∀ v ∈ step^[j] X₀, ∀ i, GoodVal (C := C) par (v i)) :
    ∀ L, (muSum B₀ L P₀).filter (fun r => descP (P := 0) r = descEnc C par)
      = (muSum step L X₀).map (rowEnc C par) := by
  have hit : ∀ j, (B₀^[j] P₀).filter (fun r => descP (P := 0) r = descEnc C par)
      = (step^[j] X₀).map (rowEnc C par) := by
    intro j
    induction j with
    | zero => exact h₀
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hbody _ _ (hgood j) ih
  intro L
  rw [muSum_eq_sum', muSum_eq_sum']
  induction L with
  | zero => simpa using hit 0
  | succ L ih =>
    rw [Finset.sum_range_succ (fun j => B₀^[j] P₀) (L + 1),
      Finset.sum_range_succ (fun j => step^[j] X₀) (L + 1), Multiset.filter_add, Multiset.map_add,
      ih, hit]

end SliceMu

end Sym
