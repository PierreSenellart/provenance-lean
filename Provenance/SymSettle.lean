import Provenance.SymCut

/-!
# The symbolic evaluation settles on every instance

A query's table is evaluated at every type of parameter row, including
types no actual row has, where the query itself may not settle. So the
table must settle on every instance, whatever its input: it does, its
recursions being bounded by counters (`Sym.settlesAt_symMuQ`), and so
does everything the environment and the cut are built of
(`Sym.settlesAt_tabQ`).
-/

variable {T : Type} [ValueType T]

namespace Sym

section MuSettle

variable {c N K : ℕ}

/-- **A bounded recursion settles**, whatever its body computes, as long as
its body settles at every round and keeps each row's counter. -/
theorem settlesAt_symMuQ (s : String) (Q₀ : AggQueryIn T c N (ColKind.allReg N))
    (Bq : AggQueryIn T c (N + K) (ColKind.allReg (N + K)) [(s, N + K)])
    (Lq : AggQueryIn T c K (ColKind.allReg K))
    (Sq : AggQueryIn T c (K + K) (ColKind.allReg (K + K)))
    (hS : Sq.noMention s) (D : Database T) (γ : Fin c → T)
    (hQ₀ : Q₀.SettlesAt D γ) (hL : Lq.SettlesAt D γ) (hSs : Sq.SettlesAt D γ)
    (hB : ∀ Y : Relation T (N + K), Bq.SettlesAt (D.assign s Y) γ)
    (hpres : ∀ (Y : Multiset (Tuple T (N + K))) (y : Tuple T (N + K)),
      Multiset.Mem (Bq.evaluatePlain (D.assign s Y) γ) y → ∃ x ∈ Y, suf x = suf y)
    (cs : List (Tuple T K)) (hnd : cs.Nodup) (hne : 0 < cs.length)
    (hLv : Lq.evaluatePlain D γ = ({cs[0]} : Multiset (Tuple T K)))
    (hSv : Sq.evaluatePlain D γ = (succRel cs : Multiset (Tuple T (K + K)))) :
    (symMuQ s Q₀ Bq Lq Sq).SettlesAt D γ := by
  rw [symMuQ, AggQueryIn.settlesAt_castKind]
  have hstep : (fun X => (stepQ s Bq Sq).evaluatePlain (D.assign s X) γ)
      = simStep (fun Z => (Bq.evaluatePlain (D.assign s Z) γ : Multiset (Tuple T (N + K))))
          (succRel cs) := by
    funext X
    rw [evaluatePlain_stepQ, simStep, simStep,
      AggQueryIn.evaluatePlain_assign_of_noMention X Sq hS D γ, hSv]
  have hbase : ∀ z, Multiset.Mem ((prodR Q₀ Lq).evaluatePlain D γ) z → suf z = cs[0] := by
    intro z hz
    rw [evaluatePlain_prodR] at hz
    obtain ⟨r, -, hr⟩ := Multiset.mem_bind.mp hz
    erw [hLv] at hr
    rw [Multiset.map_singleton, Multiset.mem_singleton] at hr
    rw [hr]; exact suf_append r _
  have hlast := simStep_last _ (fun Y y hy => hpres Y y hy) cs hnd _ hne hbase
  have hzero : (stepQ s Bq Sq).evaluatePlain (D.assign s (0 : Relation T (N + K))) γ = 0 := by
    have := congrFun hstep 0
    refine this.trans ?_
    refine Multiset.eq_zero_of_forall_notMem (fun z hz => ?_)
    obtain ⟨y, hy, -⟩ := Multiset.mem_bind.mp hz
    obtain ⟨x, hx, -⟩ := hpres 0 y hy
    exact Multiset.notMem_zero _ hx
  have hL1 : cs.length.pred + 1 = cs.length := Nat.succ_pred_eq_of_pos hne
  refine ⟨by rw [prodR, AggQueryIn.settlesAt_castKind]; exact ⟨hQ₀, hL⟩, hzero,
    ⟨cs.length.pred, ?_⟩, fun j => ?_⟩
  · rw [hL1]
    have := hlast
    rw [← hstep] at this
    exact this
  · rw [stepQ, AggQueryIn.settlesAt_castKind]
    show (prodR Bq Sq).SettlesAt _ γ
    rw [prodR, AggQueryIn.settlesAt_castKind]
    exact ⟨hB _, AggQueryIn.settlesAt_of_noMention Sq hS
      (fun _k s' hs' => (Database.find_assign_of_ne s s' _ D
        (fun hc => (hs'.resolve_right List.not_mem_nil) hc.2)).symm) γ hSs⟩

end MuSettle

/-! ## The symbolic evaluation settles -/

/-- **What the symbolic evaluation asks of its environment to settle**: its
queries settle, and the counters are a list without repetition. -/
structure EnvSettles {k c : ℕ} (env : SymEnv T k c) : Prop where
  cq : ∀ D γ, env.CQ.SettlesAt D γ
  desc : ∀ D γ, env.Desc.SettlesAt D γ
  lq : ∀ D γ n, (env.Lq n).SettlesAt D γ
  sq : ∀ D γ n, (env.Sq n).SettlesAt D γ
  ctr : ∀ D γ n, ∃ cs : List (Tuple T (env.ctrK n)), cs.Nodup ∧ ∃ h : 0 < cs.length,
    (env.Lq n).evaluatePlain D γ = ({cs[0]'h} : Multiset _)
    ∧ (env.Sq n).evaluatePlain D γ = (succRel cs : Multiset _)

theorem settlesAt_projQ {c N M : ℕ} {l : List (String × ℕ)} (F : Fin M → SA T c N)
    (q : AggQueryIn T c N (ColKind.allReg N) l) (D : Database T) (γ : Fin c → T)
    (h : q.SettlesAt D γ) : (projQ F q).SettlesAt D γ := by
  rw [projQ, AggQueryIn.settlesAt_castKind]; exact h

theorem settlesAt_prodR {c a b : ℕ} {l₁ l₂ : List (String × ℕ)}
    (q₁ : AggQueryIn T c a (ColKind.allReg a) l₁) (q₂ : AggQueryIn T c b (ColKind.allReg b) l₂)
    (D : Database T) (γ : Fin c → T) (h₁ : q₁.SettlesAt D γ) (h₂ : q₂.SettlesAt D γ) :
    (prodR q₁ q₂).SettlesAt D γ := by
  rw [prodR, AggQueryIn.settlesAt_castKind]; exact ⟨h₁, h₂⟩

theorem settlesAt_junkB {c N M : ℕ} (s : String) (D : Database T) (γ : Fin c → T) :
    (junkB (T := T) (c := c) N M s).SettlesAt D γ := by
  rw [junkB, AggQueryIn.settlesAt_castKind]; trivial

/-- **The symbolic evaluation settles on every instance.** -/
theorem settlesAt_sym_aux {k c : ℕ} (env : SymEnv T k c) (henv : EnvSettles env) :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N →
      (∀ i, q.noMention (f i) ∧ EnvNoMention env (f i)) →
      ∀ (D : Database T) (γ : Fin c → T),
        (sym env f q).SettlesAt D γ ∧ ∀ P s m, (symB env f P s m q).SettlesAt D γ := by
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hfresh D γ
    cases q with
    | Rel n s' =>
      refine ⟨?_, fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
      rw [sym]
      exact settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ (henv.desc D γ) trivial)
    | Hole n s' κ' =>
      refine ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ, fun P s m => ?_⟩
      rw [symB]
      split
      · rename_i h
        subst h
        trivial
      · exact settlesAt_junkB _ D γ
    | Param pv ρ =>
      refine ⟨?_, fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
      rw [sym]
      exact settlesAt_projQ _ _ D γ (henv.desc D γ)
    | Empty =>
      exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | Proj ps q =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hfresh D γ
      refine ⟨?_, fun P s m => ?_⟩
      · rw [sym]; exact settlesAt_projQ _ _ D γ h₁
      · rw [symB]; exact settlesAt_projQ _ _ D γ (h₂ P s m)
    | Sel φ q hφ =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hfresh D γ
      refine ⟨?_, fun P s m => ?_⟩
      · rw [sym]; exact h₁
      · rw [symB]; exact h₂ P s m
    | Prod q₁ q₂ =>
      rename_i n₁ n₂ κ₁ κ₂ l₁ l₂
      obtain ⟨h₁, h₁'⟩ := ih (AggQueryIn.tri f 1) q₁ (by simp at hq; omega)
        (fun i => ⟨(hfresh _).1.1, (hfresh _).2⟩) D γ
      obtain ⟨h₂, h₂'⟩ := ih (AggQueryIn.tri f 2) q₂ (by simp at hq; omega)
        (fun i => ⟨(hfresh _).1.2, (hfresh _).2⟩) D γ
      refine ⟨?_, fun P s m => ?_⟩
      · rw [sym]; exact settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ h₁ h₂)
      · rw [symB]
        split
        · exact settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ h₁ (h₂' P s m))
        · exact settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ (h₁' P s m) h₂)
    | Explode i hi q =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hfresh D γ
      exact ⟨by rw [sym]; exact h₁, fun P s m => by rw [symB]; exact h₂ P s m⟩
    | Retag h q =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hfresh D γ
      exact ⟨by rw [sym]; exact h₁, fun P s m => by rw [symB]; exact h₂ P s m⟩
    | Mu s' q₀ q₁ =>
      refine ⟨?_, fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
      rw [sym]
      obtain ⟨cs, hcs, hne, hL, hS⟩ := henv.ctr D γ n
      have hS' : (env.Sq n).noMention (AggQueryIn.tri f 0 0) := ((hfresh 0).2.2.2 n).2
      refine settlesAt_symMuQ (AggQueryIn.tri f 0 0) _ _ _ _ hS' D γ
        (ih (AggQueryIn.tri f 1) q₀ (by simp at hq; omega)
          (fun i => ⟨(hfresh _).1.1, (hfresh _).2⟩) D γ).1 (henv.lq D γ n) (henv.sq D γ n)
        (fun Y => (ih (AggQueryIn.tri f 2) q₁ (by simp at hq; omega)
          (fun i => ⟨(hfresh _).1.2, (hfresh _).2⟩) (D.assign (AggQueryIn.tri f 0 0) Y) γ).2 _ _ _)
        (fun Y y hy => symB_pres_aux env _ _ _ _ _ q₁ le_rfl D γ Y y hy) cs hcs hne hL hS
    | Gamma is ts fs q keep ord =>
      obtain ⟨h₁, -⟩ := ih f q (by simp at hq; omega) hfresh D γ
      refine ⟨?_, fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
      rw [sym, AggQueryIn.settlesAt_castKind]
      show (AggQueryIn.allRegOf _).SettlesAt D γ
      rw [AggQueryIn.settlesAt_allRegOf]
      exact h₁
    | GammaScalar ts fs q ord =>
      obtain ⟨h₁, -⟩ := ih (AggQueryIn.tri f 1) q (by simp at hq; omega)
        (fun i => ⟨(hfresh _).1, (hfresh _).2⟩) D γ
      refine ⟨?_, fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
      rw [sym, AggQueryIn.settlesAt_castKind]
      show (AggQueryIn.allRegOf _).SettlesAt D γ
      rw [AggQueryIn.settlesAt_allRegOf]
      refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ ?_ ?_ D γ ?_ ?_
      · rw [AggQueryIn.noMention_castKind]; exact (hfresh _).2.2.1
      · rw [AggQueryIn.noMention_castKind]
        exact noMention_sym env (hfresh _).2 _ q (hfresh _).1
      · rw [AggQueryIn.settlesAt_castKind]; exact henv.desc D γ
      · rw [AggQueryIn.settlesAt_castKind]; exact h₁
    | GammaNest is his p g q =>
      obtain ⟨h₁, -⟩ := ih f q (by simp at hq; omega) hfresh D γ
      refine ⟨?_, fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
      rw [sym, AggQueryIn.settlesAt_castKind]
      show (AggQueryIn.allRegOf _).SettlesAt D γ
      rw [AggQueryIn.settlesAt_allRegOf]
      exact h₁
    | Win P O o w t g q hrr dist keep =>
      obtain ⟨h₁, -⟩ := ih f q (by simp at hq; omega) hfresh D γ
      refine ⟨?_, fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
      rw [sym, AggQueryIn.settlesAt_castKind]
      show (AggQueryIn.allRegOf _).SettlesAt D γ
      rw [AggQueryIn.settlesAt_allRegOf]
      exact h₁
    | Apply => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | Sum => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | Dedup => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | Diff => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | MuSet => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | GammaTok => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | ProvSum => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩
    | WinExpr => exact ⟨by rw [sym]; exact AggQueryIn.settlesAt_emptyRel _ D γ,
        fun P s m => by rw [symB]; exact settlesAt_junkB _ D γ⟩

/-! ## The environment built from a cut settles -/

section EnvSettle

variable {c : ℕ} (D : Database T) (γ : Fin c → T)

theorem settlesAt_ltQ {p : ℕ} (R : AggQueryIn T c p (ColKind.allReg p)) (h : R.SettlesAt D γ) :
    (ltQ R).SettlesAt D γ := settlesAt_prodR R R D γ h h

theorem settlesAt_midQ {p : ℕ} (R : AggQueryIn T c p (ColKind.allReg p)) (h : R.SettlesAt D γ) :
    (midQ R).SettlesAt D γ :=
  settlesAt_projQ _ _ D γ (settlesAt_prodR _ R D γ (settlesAt_prodR R R D γ h h) h)

theorem settlesAt_succQ (s₁ s₂ : String) (cnt : SeqAggFunc T) {p : ℕ}
    (R : AggQueryIn T c p (ColKind.allReg p)) (h₁ : R.noMention s₁) (h₂ : R.noMention s₂)
    (h : R.SettlesAt D γ) : (succQ s₁ s₂ cnt R).SettlesAt D γ :=
  AggQueryIn.settlesAt_notInDiffX _ _ cnt _ _ (noMention_ltQ' h₁) (noMention_midQ' h₂) D γ
    (settlesAt_ltQ D γ R h) (settlesAt_midQ D γ R h)

theorem settlesAt_leastQ (s₁ s₂ : String) (cnt : SeqAggFunc T) {p : ℕ}
    (R : AggQueryIn T c p (ColKind.allReg p)) (h₁ : R.noMention s₁) (h₂ : R.noMention s₂)
    (h : R.SettlesAt D γ) : (leastQ s₁ s₂ cnt R).SettlesAt D γ :=
  AggQueryIn.settlesAt_notInDiffX _ _ cnt _ _ h₁ (noMention_aboveQ' h₂) D γ h
    (settlesAt_projQ _ _ D γ (settlesAt_ltQ D γ R h))

theorem settlesAt_greatestQ (s₁ s₂ : String) (cnt : SeqAggFunc T) {p : ℕ}
    (R : AggQueryIn T c p (ColKind.allReg p)) (h₁ : R.noMention s₁) (h₂ : R.noMention s₂)
    (h : R.SettlesAt D γ) : (greatestQ s₁ s₂ cnt R).SettlesAt D γ :=
  AggQueryIn.settlesAt_notInDiffX _ _ cnt _ _ h₁ (noMention_belowQ' h₂) D γ h
    (settlesAt_projQ _ _ D γ (settlesAt_ltQ D γ R h))

theorem settlesAt_constQ (a : T) : (constQ (c := c) a).SettlesAt D γ := by
  unfold constQ; trivial

theorem settlesAt_alphaQ (f : ℕ → String) (CQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (hf : FreshFor f CQ) (h : CQ.SettlesAt D γ) : (alphaQ f CQ).SettlesAt D γ := by
  rw [alphaQ, AggQueryIn.settlesAt_dedupG]
  exact AggQueryIn.settlesAt_sumByMuX (f 0) (f 1) (nnQ CQ) _ (noMention_nnQ CQ (hf 0))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_constQ _ _) (noMention_constQ _ _)) D γ h
    (AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_constQ _ _) (noMention_constQ _ _) D γ
      (settlesAt_constQ D γ _) (settlesAt_constQ D γ _))

theorem settlesAt_powU (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (h : EQ.SettlesAt D γ) :
    ∀ K, (powU EQ K).SettlesAt D γ
  | 0 => by rw [powU]; exact AggQueryIn.settlesAt_unitC D γ
  | K + 1 => by rw [powU]; exact settlesAt_prodR _ _ D γ (settlesAt_powU EQ h K) h

theorem settlesAt_powX {m : ℕ} (R : AggQueryIn T c m (ColKind.allReg m)) (h : R.SettlesAt D γ) :
    ∀ K, (powX R K).SettlesAt D γ
  | 0 => by rw [powX]; exact AggQueryIn.settlesAt_unitC D γ
  | K + 1 => by rw [powX]; exact settlesAt_prodR _ _ D γ (settlesAt_powX R h K) h

theorem settlesAt_thQ (f : ℕ → String) (k : ℕ) : ∀ r, (thQ (c := c) f k r).SettlesAt D γ
  | 0 => by unfold thQ thRowQ; trivial
  | r + 1 => AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_thQ f k _ r) (noMention_thRowQ _ _ _)
      D γ (settlesAt_thQ f k r) (by unfold thRowQ; trivial)

theorem settlesAt_cellsQ (f : ℕ → String) (cnt : SeqAggFunc T) (k : ℕ)
    (CQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hf : FreshFor f CQ) (h : CQ.SettlesAt D γ) :
    (cellsQ f cnt k CQ).SettlesAt D γ := by
  have hth : (thP (c := c) f k).SettlesAt D γ := settlesAt_thQ D γ _ k k
  have hnn : (nnQ CQ).SettlesAt D γ := h
  have h1 : (concP k CQ).SettlesAt D γ := settlesAt_projQ _ _ D γ h
  have h2 : (succP f cnt k CQ).SettlesAt D γ :=
    settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ (settlesAt_succQ D γ _ _ cnt _
      (noMention_nnQ CQ (hf 8)) (noMention_nnQ CQ (hf 9)) hnn) hth)
  have h3 : (topP f cnt k CQ).SettlesAt D γ :=
    settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ (settlesAt_greatestQ D γ _ _ cnt _
      (noMention_nnQ CQ (hf 10)) (noMention_nnQ CQ (hf 11)) hnn) hth)
  have h4 : (botP f cnt k CQ).SettlesAt D γ :=
    settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ (settlesAt_leastQ D γ _ _ cnt _
      (noMention_nnQ CQ (hf 12)) (noMention_nnQ CQ (hf 13)) hnn) hth)
  have h5 : (botEP f cnt k CQ).SettlesAt D γ :=
    settlesAt_projQ _ _ D γ (settlesAt_prodR _ _ D γ (AggQueryIn.settlesAt_notInDiffX _ _ cnt _ _
      (AggQueryIn.noMention_unitC _) (noMention_projQ _ _ (noMention_nnQ CQ (hf 15))) D γ
      (AggQueryIn.settlesAt_unitC D γ) (settlesAt_projQ _ _ D γ hnn)) hth)
  rw [cellsQ, AggQueryIn.settlesAt_dedupG]
  refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_concP k CQ (hf 0))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_succP f cnt k CQ (hf 1))
      (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_topP f cnt k CQ (hf 1))
        (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hf 1))
          (noMention_botEP f cnt k CQ (hf 1))))) D γ h1 ?_
  refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_succP f cnt k CQ (hf 2))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_topP f cnt k CQ (hf 3))
      (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hf 3))
        (noMention_botEP f cnt k CQ (hf 3)))) D γ h2 ?_
  refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_topP f cnt k CQ (hf 4))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hf 5))
      (noMention_botEP f cnt k CQ (hf 5))) D γ h3 ?_
  exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_botP f cnt k CQ (hf 6))
    (noMention_botEP f cnt k CQ (hf 7)) D γ h4 h5

end EnvSettle

/-- **The environment built from a cut settles** wherever the cut does,
and its counters are always a list without repetition. -/
theorem envSettles_envOf {c : ℕ} (f : ℕ → String) {cnt : SeqAggFunc T}
    (hc : SeqAggFunc.Counts cnt) (k : ℕ) (CQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (hfr : FreshFor f CQ) (h : ∀ D γ, CQ.SettlesAt D γ) : EnvSettles (envOf f cnt k CQ) where
  cq := h
  desc := fun D γ => settlesAt_projQ _ _ D γ (settlesAt_powX D γ _
    (settlesAt_cellsQ D γ _ cnt k CQ (fun i => hfr _) (h D γ)) k)
  lq := fun D γ n => settlesAt_leastQ D γ _ _ cnt _ (noMention_ctrQ _ CQ (hfr _) _)
    (noMention_ctrQ _ CQ (hfr _) _) (settlesAt_powU D γ _
      (settlesAt_alphaQ D γ _ CQ (fun i => hfr _) (h D γ)) _)
  sq := fun D γ n => settlesAt_succQ D γ _ _ cnt _ (noMention_ctrQ _ CQ (hfr _) _)
    (noMention_ctrQ _ CQ (hfr _) _) (settlesAt_powU D γ _
      (settlesAt_alphaQ D γ _ CQ (fun i => hfr _) (h D γ)) _)
  ctr := fun D γ n => by
    obtain ⟨cs, hcs, hne, -, hL, hS⟩ := ctr_ok (fun i => f (2 * i + 1)) hc CQ
        (fun i => hfr _) D γ k n
    exact ⟨cs, hcs, hne, hL, hS⟩

/-! ## The cut settles -/

section CutSettle

variable {c : ℕ} (D : Database T) (γ : Fin c → T)

theorem settlesAt_unionFin (f : ℕ → String) :
    ∀ (n : ℕ) (F : Fin n → AggQueryIn T c 1 (ColKind.allReg 1)), (∀ i j, (F i).noMention (f j)) →
      (∀ i, (F i).SettlesAt D γ) → (unionFin f n F).SettlesAt D γ
  | 0, _, _, _ => by rw [unionFin]; exact AggQueryIn.settlesAt_emptyRel _ D γ
  | n + 1, F, hF, h => by
    rw [unionFin]
    exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ (hF 0 0)
      (noMention_unionFin _ n _ (fun i => hF i.succ 1)) D γ (h 0)
      (settlesAt_unionFin _ n _ (fun i j => hF i.succ (j + 2)) (fun i => h i.succ))

theorem settlesAt_cutOf (f : ℕ → String) (S : Finset T) (core : AggQueryIn T c 1 (ColKind.allReg 1))
    (hcore : ∀ i, core.noMention (f i)) (h : core.SettlesAt D γ) :
    (cutOf f S core).SettlesAt D γ := by
  have hnull : (nullQ (T := T) (c := c)).SettlesAt D γ := by
    unfold nullQ
    split
    · exact settlesAt_constQ D γ _
    · exact AggQueryIn.settlesAt_emptyRel _ D γ
  have hamb : (ambQ (T := T) (part f 2) c).SettlesAt D γ :=
    settlesAt_unionFin D γ _ c _ (fun _ _ => noMention_projQ _ _ (AggQueryIn.noMention_unitC _))
      (fun _ => settlesAt_projQ _ _ D γ (AggQueryIn.settlesAt_unitC D γ))
  have hcs : (constsQ (c := c) (part f 4) S).SettlesAt D γ :=
    settlesAt_unionFin D γ _ _ _ (fun _ _ => noMention_constQ _ _) (fun _ => settlesAt_constQ D γ _)
  rw [cutOf, u2]
  refine AggQueryIn.settlesAt_sumByMuX _ _ _ _
      (noMention_u2 _ (noMention_nullQ _) (noMention_ambQ _ _))
    (noMention_u2 _ (noMention_constsQ _ S _) (hcore _)) D γ ?_ ?_
  · exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_nullQ _) (noMention_ambQ _ _)
      D γ hnull hamb
  · exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_constsQ _ S _) (hcore _) D γ hcs h

theorem settlesAt_colsQ {N p : ℕ} (f : ℕ → String) (q : AggQueryIn T c N (ColKind.allReg N))
    (idx : Fin p → Fin N) (hf : ∀ i, q.noMention (f i)) (h : q.SettlesAt D γ) :
    (colsQ f q idx).SettlesAt D γ :=
  settlesAt_unionFin D γ _ p _ (fun _ j => noMention_projQ _ _ (hf j))
    (fun _ => settlesAt_projQ _ _ D γ h)

theorem settlesAt_valsOf {N : ℕ} (f : ℕ → String) (q : AggQueryIn T c N (ColKind.allReg N))
    (hf : ∀ i, q.noMention (f i)) (h : q.SettlesAt D γ) : (valsOf f q).SettlesAt D γ :=
  settlesAt_colsQ D γ f q id hf h

end CutSettle

/-- **The cut settles on every instance.** -/
theorem settlesAt_cutCore {k c : ℕ} {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N →
      (∀ i, q.noMention (f i)) →
      ∀ (D : Database T) (γ : Fin c → T), (cutCore cnt f q).SettlesAt D γ := by
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hfr D γ
    -- the symbolic evaluation of an input relative to its node's cut settles
    have hsym : ∀ {m : ℕ} {κ' : Fin m → ColKind} (q : AggQueryIn T (k + c) m κ') (S : Finset T)
        (g : ℕ → String), (∀ i, q.noMention (g i)) → sizeOf q ≤ N →
        (∀ i, q.noMention (f i)) →
        (sym (envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) g q).SettlesAt
          D γ := by
      intro m κ' q S g hg hs hfq
      have hcore : ∀ s, q.noMention s →
          (cutOf (part f 4) S (cutCore cnt (part f 1) q)).noMention s :=
        fun s hs' => noMention_cutOf _ S (noMention_cutCore cnt _ _ q le_rfl hs')
      have henv := envSettles_envOf (part f 3) hc k _ (fun i => hcore _ (hfq _))
        (fun D' γ' => settlesAt_cutOf D' γ' _ S _
            (fun i => noMention_cutCore cnt _ _ q le_rfl (hfq _))
          (ih (part f 1) q hs (fun i => hfq _) D' γ'))
      exact (settlesAt_sym_aux _ henv _ g q le_rfl
        (fun i => ⟨hg i, envNoMention_envOf _ cnt k _ (hcore _ (hg i))⟩) D γ).1
    cases q with
    | Rel n s' => rw [cutCore]; exact settlesAt_valsOf D γ f _ hfr trivial
    | Hole => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | Param => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | Empty => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | Proj ps q => rw [cutCore]; exact ih f q (by simp at hq; omega) hfr D γ
    | Sel φ q _ => rw [cutCore]; exact ih f q (by simp at hq; omega) hfr D γ
    | Prod q₁ q₂ =>
      rw [cutCore]
      exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_cutCore cnt _ _ q₁ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₂ le_rfl (hfr _).2) D γ
        (ih _ q₁ (by simp at hq; omega) (fun i => (hfr _).1) D γ)
        (ih _ q₂ (by simp at hq; omega) (fun i => (hfr _).2) D γ)
    | Explode _ _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hfr D γ
    | Retag _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hfr D γ
    | Mu s' q₀ q₁ =>
      rw [cutCore]
      exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_cutCore cnt _ _ q₀ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₁ le_rfl (hfr _).2) D γ
        (ih _ q₀ (by simp at hq; omega) (fun i => (hfr _).1) D γ)
        (ih _ q₁ (by simp at hq; omega) (fun i => (hfr _).2) D γ)
    | Gamma is ts fs q keep ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [cutCore]
      refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ ?_) D γ (ih _ q hs (fun i => hfr _) D γ) ?_
      · unfold gammaRaw; rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f _ q (hfr _)
      · refine settlesAt_colsQ D γ _ _ _ (fun i => ?_) ?_
        · unfold gammaRaw; rw [AggQueryIn.noMention_allRegOf]
          exact noMention_symCut cnt f _ q (hfr _)
        · unfold gammaRaw; rw [AggQueryIn.settlesAt_allRegOf]
          exact hsym q _ _ (fun i => hfr _) hs hfr
    | GammaScalar ts fs q ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hcore : ∀ s, q.noMention s → (cutOf (part f 4)
          (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q ord).allConsts
          (cutCore cnt (part f 1) q)).noMention s :=
        fun s hs' => noMention_cutOf _ _ (noMention_cutCore cnt _ _ q le_rfl hs')
      have hrNM : ∀ s, q.noMention s → (scalarRaw (envOf (part f 3) cnt k (cutOf (part f 4)
          (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q ord).allConsts
          (cutCore cnt (part f 1) q))) (part f 5) ts fs q).noMention s := by
        intro s hs'
        unfold scalarRaw
        rw [AggQueryIn.noMention_allRegOf]
        refine AggQueryIn.noMention_sumByMuX _ _ _ _ ?_ ?_
        · rw [AggQueryIn.noMention_castKind]
          exact (envNoMention_envOf _ cnt k _ (hcore s hs')).2.1
        · rw [AggQueryIn.noMention_castKind]
          exact noMention_sym _ (envNoMention_envOf _ cnt k _ (hcore s hs')) _ q hs'
      rw [cutCore]
      refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ (hrNM _ (hfr _))) D γ (ih _ q hs (fun i => hfr _) D γ) ?_
      refine settlesAt_colsQ D γ _ _ _ (fun i => hrNM _ (hfr _)) ?_
      unfold scalarRaw
      rw [AggQueryIn.settlesAt_allRegOf]
      have henv := envSettles_envOf (part f 3) hc k _ (fun i => hcore _ (hfr _))
        (fun D' γ' => settlesAt_cutOf D' γ' _ _ _
            (fun i => noMention_cutCore cnt _ _ q le_rfl (hfr _))
          (ih (part f 1) q hs (fun i => hfr _) D' γ'))
      refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ ?_ ?_ D γ ?_ ?_
      · rw [AggQueryIn.noMention_castKind]
        exact (envNoMention_envOf _ cnt k _ (hcore _ (hfr _))).2.1
      · rw [AggQueryIn.noMention_castKind]
        exact noMention_sym _ (envNoMention_envOf _ cnt k _ (hcore _ (hfr _))) _ q (hfr _)
      · rw [AggQueryIn.settlesAt_castKind]; exact henv.desc D γ
      · rw [AggQueryIn.settlesAt_castKind]
        exact hsym q _ _ (fun i => hfr _) hs hfr
    | GammaNest is his p g q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [cutCore]
      refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ ?_) D γ (ih _ q hs (fun i => hfr _) D γ) ?_
      · unfold nestRaw; rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f _ q (hfr _)
      · refine settlesAt_colsQ D γ _ _ _ (fun i => ?_) ?_
        · unfold nestRaw; rw [AggQueryIn.noMention_allRegOf]
          exact noMention_symCut cnt f _ q (hfr _)
        · unfold nestRaw; rw [AggQueryIn.settlesAt_allRegOf]
          exact hsym q _ _ (fun i => hfr _) hs hfr
    | Win P O o w t g q hrr dist keep =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      rw [cutCore]
      refine AggQueryIn.settlesAt_sumByMuX _ _ _ _ (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_colsQ _ _ _ ?_) D γ (ih _ q hs (fun i => hfr _) D γ) ?_
      · unfold winRaw; rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f _ q (hfr _)
      · refine settlesAt_colsQ D γ _ _ _ (fun i => ?_) ?_
        · unfold winRaw; rw [AggQueryIn.noMention_allRegOf]
          exact noMention_symCut cnt f _ q (hfr _)
        · unfold winRaw; rw [AggQueryIn.settlesAt_allRegOf]
          exact hsym q _ _ (fun i => hfr _) hs hfr
    | Apply => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | Sum => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | Dedup => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | Diff => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | MuSet => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | GammaTok => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | ProvSum => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ
    | WinExpr => rw [cutCore]; exact AggQueryIn.settlesAt_emptyRel _ D γ

/-- **The table settles on every instance.** -/
theorem settlesAt_tabQ {k c : ℕ} {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt) (f : ℕ → String)
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T (k + c) n κ)
    (hf : ∀ i, q.noMention (f i)) (D : Database T)
    (γ : Fin c → T) : (tabQ cnt f q).SettlesAt D γ := by
  have hcut : ∀ i, (cutQ cnt (part f 1) q).noMention (part f 0 i) :=
    fun i => noMention_cutQ cnt _ q (hf _)
  have henv := envSettles_envOf (part f 0) hc k (cutQ cnt (part f 1) q) hcut
    (fun D' γ' => settlesAt_cutOf D' γ' _ _ _ (fun i => noMention_cutCore cnt _ _ q le_rfl (hf _))
      (settlesAt_cutCore hc _ _ q le_rfl (fun i => hf _) D' γ'))
  exact (settlesAt_sym_aux _ henv _ (part f 2) q le_rfl
    (fun i => ⟨hf _, envNoMention_tabEnv cnt f q (hf _)⟩) D γ).1

theorem envSettles_tabEnv {k c : ℕ} {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T (k + c) n κ)
    (hf : ∀ i, q.noMention (f i)) : EnvSettles (tabEnv cnt f q) :=
  envSettles_envOf (part f 0) hc k (cutQ cnt (part f 1) q)
    (fun _ => noMention_cutQ cnt _ q (hf _))
    (fun D' γ' => settlesAt_cutOf D' γ' _ _ _ (fun _ => noMention_cutCore cnt _ _ q le_rfl (hf _))
      (settlesAt_cutCore hc _ _ q le_rfl (fun _ => hf _) D' γ'))

end Sym
