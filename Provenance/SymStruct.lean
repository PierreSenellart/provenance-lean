import Provenance.SymApply

/-!
# What the apply written with products is made of

The construction of `Provenance.SymApply` must stay in the fragment it is
for: its operators in `{∅, Π, σ, ×, γ, win, μ^⊎}` (`Sym.basisProdOps`),
its terms and aggregates in the signature, its recursions hygienic, and
every window over an all-regular input. `Sym.Fine` bundles the four, and
each construction is shown to keep it.
-/

variable {T : Type} [ValueType T]

namespace Sym

/-- **A query of the fragment the construction lives in.** -/
def Fine {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (Θ : Set (SeqAggFunc T))
    (q : AggQueryIn T c n κ l) : Prop :=
  q.usesOnly basisProdOps ∧ q.inSig Θ ∧ winAllReg q ∧ q.hygienic

theorem sumProdOps_sub : AggQueryIn.sumProdOps ⊆ basisProdOps := by
  intro x hx
  simp only [AggQueryIn.sumProdOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [basisProdOps, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem mem_proj : OpKind.proj ∈ basisProdOps := by simp [basisProdOps]
theorem mem_sel : OpKind.sel ∈ basisProdOps := by simp [basisProdOps]
theorem mem_prod : OpKind.prod ∈ basisProdOps := by simp [basisProdOps]
theorem mem_gamma : OpKind.gamma ∈ basisProdOps := by simp [basisProdOps]
theorem mem_win : OpKind.win ∈ basisProdOps := by simp [basisProdOps]
theorem mem_muBag : OpKind.muBag ∈ basisProdOps := by simp [basisProdOps]
theorem mem_empty : OpKind.empty ∈ basisProdOps := by simp [basisProdOps]

/-! ## Terms and predicates of comparisons -/

section Terms

variable {c N : ℕ}

omit [ValueType T] in
theorem SA.noFun_toG (a : SA T c N) : a.toG.noFun = true := by
  cases a <;> rfl

omit [ValueType T] in
theorem noFun_projSA {M : ℕ} (F : Fin M → SA T c N) (x : Fin M) :
    (projSA F x).noFun = true := SA.noFun_toG _

theorem SP.noFun_toGen (p : SP T c N) : p.toGen.noFun = true := by
  induction p with
  | atom op a b => show (a.toG.noFun && b.toG.noFun) = true; rw [SA.noFun_toG, SA.noFun_toG]; rfl
  | and p q ihp ihq => show (p.toGen.noFun && q.toGen.noFun) = true; rw [ihp, ihq]; rfl
  | or p q ihp ihq => show (p.toGen.noFun && q.toGen.noFun) = true; rw [ihp, ihq]; rfl
  | not p ih => exact ih
  | tru => rfl
  | fls => rfl

omit [ValueType T] in
theorem SA.noFun_toT (a : SA T 0 N) : a.toT.noFun = true := by
  cases a with
  | const a => rfl
  | col i => rfl
  | amb j => exact j.elim0

omit [ValueType T] in
theorem noFun_boolOf (op : CompOp) (t₁ t₂ : Term T N) (h₁ : t₁.noFun = true)
    (h₂ : t₂.noFun = true) : (boolOf op t₁ t₂).noFun = true := by
  cases op <;> exact (by simp [boolOf, BoolTerm.noFun, BoolTerm.args, h₁, h₂])

omit [ValueType T] in
theorem SP.noFun_toSel (p : SP T 0 N) : p.toSel.noFun = true := by
  induction p with
  | atom op a b => exact noFun_boolOf op _ _ (SA.noFun_toT a) (SA.noFun_toT b)
  | and p q ihp ihq => show (p.toSel.noFun && q.toSel.noFun) = true; rw [ihp, ihq]; rfl
  | or p q ihp ihq => show (p.toSel.noFun && q.toSel.noFun) = true; rw [ihp, ihq]; rfl
  | not p ih => exact ih
  | tru => rfl
  | fls => rfl

end Terms

/-! ## The primitive constructions -/

section Prim

variable {c : ℕ} {Θ : Set (SeqAggFunc T)}

omit [ValueType T] in
@[simp] theorem winAllReg_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List (String × ℕ)}
    (h : κ = κ') (q : AggQueryIn T c n κ l) : winAllReg (q.castKind h) ↔ winAllReg q := by
  cases h; exact Iff.rfl

omit [ValueType T] in
@[simp] theorem winAllReg_explodeBelow {c n : ℕ} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      winAllReg (q.explodeBelow m) ↔ winAllReg q := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show winAllReg (q.castKind _) ↔ _
    rw [winAllReg_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.explodeBelow
    split
    · split
      · rw [winAllReg_castKind]
        show winAllReg (AggQueryIn.Explode _ _ (q.explodeBelow m)) ↔ _
        rw [winAllReg]
        exact ih q
      · rw [winAllReg_castKind]
        exact ih q
      · show winAllReg (AggQueryIn.Retag _ (q.explodeBelow m)) ↔ _
        rw [winAllReg]
        exact ih q
    · rw [winAllReg_castKind]
      exact ih q

omit [ValueType T] in
@[simp] theorem winAllReg_allRegOf {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) : winAllReg q.allRegOf ↔ winAllReg q := by
  rw [AggQueryIn.allRegOf, winAllReg_castKind, winAllReg_explodeBelow]

theorem fine_projQ {N M : ℕ} {l : List (String × ℕ)} (F : Fin M → SA T c N)
    {q : AggQueryIn T c N (ColKind.allReg N) l} (h : Fine Θ q) : Fine Θ (projQ F q) := by
  unfold Fine projQ
  rw [AggQueryIn.usesOnly_castKind, AggQueryIn.inSig_castKind, winAllReg_castKind,
    AggQueryIn.hygienic_castKind]
  exact ⟨⟨⟨mem_proj, fun _ => rfl⟩, h.1⟩, ⟨fun _ => SA.noFun_toG _, h.2.1⟩, h.2.2.1, h.2.2.2⟩

theorem fine_prodR {a b : ℕ} {l₁ l₂ : List (String × ℕ)}
    {q₁ : AggQueryIn T c a (ColKind.allReg a) l₁} {q₂ : AggQueryIn T c b (ColKind.allReg b) l₂}
    (h₁ : Fine Θ q₁) (h₂ : Fine Θ q₂) : Fine Θ (prodR q₁ q₂) := by
  unfold Fine prodR
  rw [AggQueryIn.usesOnly_castKind, AggQueryIn.inSig_castKind, winAllReg_castKind,
    AggQueryIn.hygienic_castKind]
  exact ⟨⟨mem_prod, h₁.1, h₂.1⟩, ⟨h₁.2.1, h₂.2.1⟩, ⟨h₁.2.2.1, h₂.2.2.1⟩, ⟨h₁.2.2.2, h₂.2.2.2⟩⟩

theorem fine_selSP {N : ℕ} {l : List (String × ℕ)} (p : SP T c N)
    {q : AggQueryIn T c N (ColKind.allReg N) l} (hφ : SelOK l p.toGen) (h : Fine Θ q) :
    Fine Θ (AggQueryIn.Sel p.toGen q hφ) :=
  ⟨⟨mem_sel, h.1⟩, ⟨SP.noFun_toGen p, h.2.1⟩, h.2.2.1, h.2.2.2⟩

theorem fine_rel (n : ℕ) (s : String) : Fine Θ (AggQueryIn.Rel (T := T) (c := c) n s) :=
  ⟨trivial, trivial, trivial, trivial⟩

theorem fine_hole (n : ℕ) (s : String) :
    Fine Θ (AggQueryIn.Hole (T := T) (c := c) n s (ColKind.allReg n)) :=
  ⟨trivial, trivial, trivial, trivial⟩

theorem fine_param {m : ℕ} (pv : Fin m → T ⊕ Fin c) :
    Fine Θ (AggQueryIn.Param pv (ColKind.allReg m)) :=
  ⟨⟨mem_empty, mem_proj, mem_gamma⟩, trivial, trivial, trivial⟩

theorem fine_constQ (a : T) : Fine Θ (constQ (c := c) a) := fine_param _

theorem fine_emptyRel (n : ℕ) : Fine Θ (AggQueryIn.emptyRel (T := T) (c := c) n) := by
  unfold Fine AggQueryIn.emptyRel
  rw [AggQueryIn.usesOnly_castKind, AggQueryIn.inSig_castKind, winAllReg_castKind,
    AggQueryIn.hygienic_castKind]
  exact ⟨⟨⟨mem_proj, fun _ => rfl⟩, mem_empty⟩, ⟨fun _ => rfl, trivial⟩, trivial, trivial⟩

theorem fine_unitC : Fine Θ (AggQueryIn.unitC (T := T) (c := c)) :=
  ⟨AggQueryIn.usesOnly_unitCX sumProdOps_sub, AggQueryIn.inSig_unitC Θ,
    by unfold AggQueryIn.unitC; rw [winAllReg_castKind]; trivial, AggQueryIn.hygienic_unitC⟩

theorem fine_dedupG {n : ℕ} {q : AggQueryIn T c n (ColKind.allReg n)} (h : Fine Θ q) :
    Fine Θ (AggQueryIn.dedupG q) := by
  refine ⟨AggQueryIn.usesOnly_dedupG (q := q) mem_gamma h.1, AggQueryIn.inSig_dedupG (q := q) h.2.1,
    ?_, AggQueryIn.hygienic_dedupG (q := q) h.2.2.2⟩
  unfold AggQueryIn.dedupG; rw [winAllReg_castKind]; exact h.2.2.1

theorem fine_sumByMuX {n : ℕ} (s₁ s₂ : String) {q₁ q₂ : AggQueryIn T c n (ColKind.allReg n)}
    (h₁ : Fine Θ q₁) (h₂ : Fine Θ q₂) (hm₁ : q₁.noMention s₁) (hm₂₁ : q₁.noMention s₂)
    (hm₂₂ : q₂.noMention s₂) : Fine Θ (AggQueryIn.sumByMuX s₁ s₂ q₁ q₂) := by
  refine ⟨AggQueryIn.usesOnly_sumByMuX sumProdOps_sub s₁ s₂ q₁ q₂ h₁.1 h₂.1,
    AggQueryIn.inSig_sumByMuX Θ s₁ s₂ q₁ q₂ h₁.2.1 h₂.2.1, ?_,
    AggQueryIn.hygienic_sumByMuX s₁ s₂ q₁ q₂ hm₁ hm₂₁ hm₂₂ h₁.2.2.2 h₂.2.2.2⟩
  simp only [AggQueryIn.sumByMuX, AggQueryIn.phaseBodyX, AggQueryIn.withTag, AggQueryIn.driver,
    AggQueryIn.unitC, winAllReg_castKind, winAllReg]
  exact ⟨⟨trivial, trivial, h₁.2.2.1⟩, trivial, h₂.2.2.1⟩

end Prim

/-! ## The order queries and the environment -/

section Env

variable {c : ℕ} {Θ : Set (SeqAggFunc T)} {cnt : SeqAggFunc T}

theorem fine_proj {N M : ℕ} {κ : Fin N → ColKind} {l : List (String × ℕ)}
    (ps : Fin M → ProjColIn T c κ) (hps : ∀ j, (ps j).sourceCol = true)
    (hnf : ∀ j, (ps j).noFun = true) {q : AggQueryIn T c N κ l} (h : Fine Θ q) :
    Fine Θ (AggQueryIn.Proj ps q) := by
  unfold Fine
  simp only [AggQueryIn.usesOnly, AggQueryIn.inSig, winAllReg, AggQueryIn.hygienic]
  exact ⟨⟨⟨mem_proj, hps⟩, h.1⟩, ⟨hnf, h.2.1⟩, h.2.2.1, h.2.2.2⟩

theorem fine_notInDiffX {k : ℕ} (s₁ s₂ : String) (hc : cnt ∈ Θ)
    {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)} (h₁ : Fine Θ q₁) (h₂ : Fine Θ q₂)
    (hm₁ : q₁.noMention s₁) (hm₂₁ : q₁.noMention s₂) (hm₂₂ : q₂.noMention s₂) :
    Fine Θ (AggQueryIn.notInDiffX s₁ s₂ cnt q₁ q₂) := by
  have hs := fine_sumByMuX (Θ := Θ) s₁ s₂ (q₁ := .Proj (AggQueryIn.tagCols 0) q₁)
    (q₂ := .Proj (AggQueryIn.tagCols ValueType.nonzero) q₂)
    (fine_proj _ (fun _ => rfl) (fun j => AggQueryIn.noFun_tagCols 0 j) h₁)
    (fine_proj _ (fun _ => rfl) (fun j => AggQueryIn.noFun_tagCols _ j) h₂)
    (by simp only [AggQueryIn.noMention]; exact hm₁)
    (by simp only [AggQueryIn.noMention]; exact hm₂₁)
    (by simp only [AggQueryIn.noMention]; exact hm₂₂)
  exact ⟨AggQueryIn.usesOnly_notInDiffX sumProdOps_sub s₁ s₂ cnt h₁.1 h₂.1,
    AggQueryIn.inSig_notInDiffX s₁ s₂ hc h₁.2.1 h₂.2.1, ⟨h₁.2.2.1, hs.2.2.1⟩,
    AggQueryIn.hygienic_notInDiffX s₁ s₂ cnt hm₁ hm₂₁ hm₂₂ h₁.2.2.2 h₂.2.2.2⟩

theorem fine_selG {N : ℕ} (φ : GenPredIn T c (ColKind.allReg N)) (hφ : φ.noFun = true)
    {q : AggQueryIn T c N (ColKind.allReg N)} (h : Fine Θ q) :
    Fine Θ (AggQueryIn.Sel φ q trivial) :=
  ⟨⟨mem_sel, h.1⟩, ⟨hφ, h.2.1⟩, h.2.2.1, h.2.2.2⟩

theorem fine_ltQ {p : ℕ} {R : AggQueryIn T c p (ColKind.allReg p)} (h : Fine Θ R) :
    Fine Θ (ltQ R) := fine_selG _ (noFun_ltOn _ _) (fine_prodR h h)

theorem fine_midQ {p : ℕ} {R : AggQueryIn T c p (ColKind.allReg p)} (h : Fine Θ R) :
    Fine Θ (midQ R) := by
  unfold midQ
  refine fine_projQ _ (fine_selG _ ?_ (fine_prodR (fine_prodR h h) h))
  show ((ltOn _ _).noFun && (ltOn _ _).noFun) = true
  rw [noFun_ltOn, noFun_ltOn]; rfl

theorem fine_succQ (s₁ s₂ : String) (hc : cnt ∈ Θ) {p : ℕ} {R : AggQueryIn T c p (ColKind.allReg p)}
    (h : Fine Θ R) (h₁ : R.noMention s₁) (h₂ : R.noMention s₂) : Fine Θ (succQ s₁ s₂ cnt R) :=
  fine_notInDiffX s₁ s₂ hc (fine_ltQ h) (fine_midQ h) (noMention_ltQ' h₁) (noMention_ltQ' h₂)
    (noMention_midQ' h₂)

theorem fine_leastQ (s₁ s₂ : String) (hc : cnt ∈ Θ) {p : ℕ}
    {R : AggQueryIn T c p (ColKind.allReg p)} (h : Fine Θ R) (h₁ : R.noMention s₁)
    (h₂ : R.noMention s₂) : Fine Θ (leastQ s₁ s₂ cnt R) :=
  fine_notInDiffX s₁ s₂ hc h (fine_projQ _ (fine_ltQ h)) h₁ h₂ (noMention_aboveQ' h₂)

theorem fine_greatestQ (s₁ s₂ : String) (hc : cnt ∈ Θ) {p : ℕ}
    {R : AggQueryIn T c p (ColKind.allReg p)} (h : Fine Θ R) (h₁ : R.noMention s₁)
    (h₂ : R.noMention s₂) : Fine Θ (greatestQ s₁ s₂ cnt R) :=
  fine_notInDiffX s₁ s₂ hc h (fine_projQ _ (fine_ltQ h)) h₁ h₂ (noMention_belowQ' h₂)

theorem fine_nnQ {CQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Fine Θ CQ) : Fine Θ (nnQ CQ) :=
  fine_selG _ rfl h

theorem fine_alphaQ (f : ℕ → String) {CQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Fine Θ CQ)
    (hf : FreshFor f CQ) : Fine Θ (alphaQ f CQ) :=
  fine_dedupG (fine_sumByMuX _ _ (fine_nnQ h)
    (fine_sumByMuX _ _ (fine_constQ 0) (fine_constQ _) (noMention_constQ _ _) (noMention_constQ _ _)
      (noMention_constQ _ _)) (noMention_nnQ CQ (hf 0)) (noMention_nnQ CQ (hf 1))
    (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_constQ _ _) (noMention_constQ _ _)))

theorem fine_powU {EQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Fine Θ EQ) :
    ∀ K, Fine Θ (powU EQ K)
  | 0 => by rw [powU]; exact fine_unitC
  | K + 1 => by rw [powU]; exact fine_prodR (fine_powU h K) h

theorem fine_powX {m : ℕ} {R : AggQueryIn T c m (ColKind.allReg m)} (h : Fine Θ R) :
    ∀ K, Fine Θ (powX R K)
  | 0 => by rw [powX]; exact fine_unitC
  | K + 1 => by rw [powX]; exact fine_prodR (fine_powX h K) h

theorem fine_thQ (f : ℕ → String) (k : ℕ) : ∀ r, Fine Θ (thQ (c := c) f k r)
  | 0 => fine_param _
  | r + 1 => fine_sumByMuX _ _ (fine_thQ f k r) (fine_param _) (noMention_thQ f k _ r)
      (noMention_thQ f k _ r) (noMention_thRowQ _ _ _)

/-- **The environment's queries are of the fragment.** -/
structure EnvFine {k : ℕ} (Θ : Set (SeqAggFunc T)) (env : SymEnv T k c) : Prop where
  cq : Fine Θ env.CQ
  desc : Fine Θ env.Desc
  lq : ∀ n, Fine Θ (env.Lq n)
  sq : ∀ n, Fine Θ (env.Sq n)

theorem envFine_envOf (f : ℕ → String) (hc : cnt ∈ Θ) (k : ℕ)
    {CQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Fine Θ CQ) (hf : FreshFor f CQ) :
    EnvFine Θ (envOf f cnt k CQ) := by
  have hf0 : FreshFor (fun i => f (2 * i)) CQ := fun i => hf _
  have hf1 : FreshFor (fun i => f (2 * i + 1)) CQ := fun i => hf _
  have hth : Fine Θ (thP (c := c) (fun i => f (2 * i)) k) := fine_thQ _ k k
  have hnn := fine_nnQ h
  have hcells : Fine Θ (cellsQ (fun i => f (2 * i)) cnt k CQ) := by
    have h1 : Fine Θ (concP k CQ) := fine_projQ _ h
    have h2 : Fine Θ (succP (fun i => f (2 * i)) cnt k CQ) := fine_projQ _ (fine_prodR
      (fine_succQ _ _ hc hnn (noMention_nnQ CQ (hf0 8)) (noMention_nnQ CQ (hf0 9))) hth)
    have h3 : Fine Θ (topP (fun i => f (2 * i)) cnt k CQ) := fine_projQ _ (fine_prodR
      (fine_greatestQ _ _ hc hnn (noMention_nnQ CQ (hf0 10)) (noMention_nnQ CQ (hf0 11))) hth)
    have h4 : Fine Θ (botP (fun i => f (2 * i)) cnt k CQ) := fine_projQ _ (fine_prodR
      (fine_leastQ _ _ hc hnn (noMention_nnQ CQ (hf0 12)) (noMention_nnQ CQ (hf0 13))) hth)
    have h5 : Fine Θ (botEP (fun i => f (2 * i)) cnt k CQ) := fine_projQ _ (fine_prodR
      (fine_notInDiffX _ _ hc fine_unitC (fine_projQ _ hnn) (AggQueryIn.noMention_unitC _)
        (AggQueryIn.noMention_unitC _) (noMention_projQ _ _ (noMention_nnQ CQ (hf0 15)))) hth)
    unfold cellsQ
    refine fine_dedupG (fine_sumByMuX _ _ h1 (fine_sumByMuX _ _ h2 (fine_sumByMuX _ _ h3
      (fine_sumByMuX _ _ h4 h5 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_)
    all_goals first
      | exact noMention_concP k CQ (hf0 _)
      | exact noMention_succP _ cnt k CQ (hf0 _)
      | exact noMention_topP _ cnt k CQ (hf0 _)
      | exact noMention_botP _ cnt k CQ (hf0 _)
      | exact noMention_botEP _ cnt k CQ (hf0 _)
      | exact AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP _ cnt k CQ (hf0 _))
          (noMention_botEP _ cnt k CQ (hf0 _))
      | exact AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_topP _ cnt k CQ (hf0 _))
          (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP _ cnt k CQ (hf0 _))
            (noMention_botEP _ cnt k CQ (hf0 _)))
      | exact AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_succP _ cnt k CQ (hf0 _))
          (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_topP _ cnt k CQ (hf0 _))
            (AggQueryIn.noMention_sumByMuX _ _ _ _ (noMention_botP _ cnt k CQ (hf0 _))
              (noMention_botEP _ cnt k CQ (hf0 _))))
  have hctr : ∀ K, Fine Θ (ctrQ (fun i => f (2 * i + 1)) CQ K) :=
    fun K => fine_powU (fine_alphaQ _ h hf1) K
  refine ⟨h, fine_projQ _ (fine_powX hcells k), fun n => ?_, fun n => ?_⟩
  · exact fine_leastQ _ _ hc (hctr _) (noMention_ctrQ _ CQ (hf1 _) _)
      (noMention_ctrQ _ CQ (hf1 _) _)
  · exact fine_succQ _ _ hc (hctr _) (noMention_ctrQ _ CQ (hf1 _) _) (noMention_ctrQ _ CQ (hf1 _) _)

end Env

/-! ## The symbolic evaluation -/

section SymFine

variable {Θ : Set (SeqAggFunc T)}

theorem noFun_termV {k c m : ℕ} (t : TermIn T (k + c) m) : (termV (k := k) t).noFun = true := by
  cases t with
  | const a => rfl
  | outer o =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) o
    · simp only [termV, Fin.addCases_left]; rfl
    · simp only [termV, Fin.addCases_right]; rfl
  | index i => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl
  | caseWhen => rfl
  | coalesce => rfl

theorem noFun_transSelOpt {k n : ℕ} (keep : Option (Selection T n)) :
    Selection.noFunOpt (keep.map (fun φ => (transSel (k := k) 0 φ).toSel)) = true := by
  cases keep with
  | none => rfl
  | some φ => exact SP.noFun_toSel _

theorem fine_junkB {c N M : ℕ} (s : String) : Fine Θ (junkB (T := T) (c := c) N M s) := by
  unfold Fine junkB
  rw [AggQueryIn.usesOnly_castKind, AggQueryIn.inSig_castKind, winAllReg_castKind,
    AggQueryIn.hygienic_castKind]
  exact ⟨⟨⟨mem_proj, fun _ => rfl⟩, mem_sel, trivial⟩, ⟨fun _ => rfl, rfl, trivial⟩,
    trivial, trivial⟩

/-- **The symbolic evaluation is of the fragment.** -/
theorem fine_sym_aux {k c : ℕ} (env : SymEnv T k c) (henv : EnvFine Θ env) :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N → q.inSig Θ →
      (∀ i, q.noMention (f i) ∧ EnvNoMention env (f i)) →
      Fine Θ (sym env f q) ∧ ∀ P s m, Fine Θ (symB env f P s m q) := by
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hi hfresh
    have hemp : ∀ n', Fine Θ (AggQueryIn.emptyRel (T := T) (c := c) n') := fine_emptyRel
    cases q with
    | Rel n s' =>
      refine ⟨?_, fun P s m => by rw [symB]; exact fine_junkB _⟩
      rw [sym]
      exact fine_projQ _ (fine_prodR henv.desc (fine_rel _ _))
    | Hole n s' κ' =>
      refine ⟨by rw [sym]; exact hemp _, fun P s m => ?_⟩
      rw [symB]
      split
      · rename_i h; subst h; exact fine_hole _ _
      · exact fine_junkB _
    | Param pv ρ =>
      refine ⟨?_, fun P s m => by rw [symB]; exact fine_junkB _⟩
      rw [sym]; exact fine_projQ _ henv.desc
    | Empty => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | Proj ps q =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hi.2 hfresh
      exact ⟨by rw [sym]; exact fine_projQ _ h₁,
          fun P s m => by rw [symB]; exact fine_projQ _ (h₂ P s m)⟩
    | Sel φ q hφ =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hi.2 hfresh
      exact ⟨by rw [sym]; exact fine_selSP _ _ h₁,
          fun P s m => by rw [symB]; exact fine_selSP _ _ (h₂ P s m)⟩
    | Prod q₁ q₂ =>
      obtain ⟨h₁, h₁'⟩ := ih (AggQueryIn.tri f 1) q₁ (by simp at hq; omega) hi.1
        (fun i => ⟨(hfresh _).1.1, (hfresh _).2⟩)
      obtain ⟨h₂, h₂'⟩ := ih (AggQueryIn.tri f 2) q₂ (by simp at hq; omega) hi.2
        (fun i => ⟨(hfresh _).1.2, (hfresh _).2⟩)
      refine ⟨?_, fun P s m => ?_⟩
      · rw [sym]; exact fine_projQ _ (fine_selSP _ _ (fine_prodR h₁ h₂))
      · rw [symB]
        split
        · exact fine_projQ _ (fine_selSP _ _ (fine_prodR h₁ (h₂' P s m)))
        · exact fine_projQ _ (fine_selSP _ _ (fine_prodR (h₁' P s m) h₂))
    | Explode i hi' q =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hi hfresh
      exact ⟨by rw [sym]; exact h₁, fun P s m => by rw [symB]; exact h₂ P s m⟩
    | Retag h q =>
      obtain ⟨h₁, h₂⟩ := ih f q (by simp at hq; omega) hi hfresh
      exact ⟨by rw [sym]; exact h₁, fun P s m => by rw [symB]; exact h₂ P s m⟩
    | Mu s' q₀ q₁ =>
      refine ⟨?_, fun P s m => by rw [symB]; exact fine_junkB _⟩
      obtain ⟨h₀, -⟩ := ih (AggQueryIn.tri f 1) q₀ (by simp at hq; omega) hi.1
        (fun i => ⟨(hfresh _).1.1, (hfresh _).2⟩)
      obtain ⟨-, h₁⟩ := ih (AggQueryIn.tri f 2) q₁ (by simp at hq; omega) hi.2
        (fun i => ⟨(hfresh _).1.2, (hfresh _).2⟩)
      have hb := h₁ (env.ctrK n) (AggQueryIn.tri f 0 0) n
      have hnm₀ : (sym env (AggQueryIn.tri f 1) q₀).noMention (AggQueryIn.tri f 0 0) :=
        noMention_sym env (hfresh 0).2 _ q₀ (hfresh 0).1.1
      have hnm₁ : (symB env (AggQueryIn.tri f 2) (env.ctrK n) (AggQueryIn.tri f 0 0) n
          q₁).noMention (AggQueryIn.tri f 0 0) :=
        (noMention_sym_aux env (hfresh 0).2 _ _ q₁ le_rfl (hfresh 0).1.2).2 _ _ _
      rw [sym, symMuQ]
      unfold Fine
      rw [AggQueryIn.usesOnly_castKind, AggQueryIn.inSig_castKind, winAllReg_castKind,
        AggQueryIn.hygienic_castKind]
      have hbase := fine_prodR h₀ (henv.lq n)
      have hstep : Fine Θ (stepQ (AggQueryIn.tri f 0 0)
          (symB env (AggQueryIn.tri f 2) (env.ctrK n) (AggQueryIn.tri f 0 0) n q₁) (env.Sq n)) := by
        unfold stepQ
        exact fine_projQ _ (fine_selSP _ _ (fine_prodR hb (henv.sq n)))
      refine ⟨⟨⟨mem_proj, fun _ => rfl⟩, mem_muBag, hbase.1, hstep.1⟩,
        ⟨fun x => noFun_projSA _ x, hbase.2.1, hstep.2.1⟩, ⟨hbase.2.2.1, hstep.2.2.1⟩,
        ⟨(noMention_prodR _ _).mpr ⟨hnm₀, ((hfresh 0).2.2.2 n).1⟩, ?_, hbase.2.2.2, hstep.2.2.2⟩⟩
      unfold stepQ
      rw [AggQueryIn.noMention_castKind]
      exact (noMention_prodR _ _).mpr ⟨hnm₁, ((hfresh 0).2.2.2 n).2⟩
    | Gamma is ts fs q keep ord =>
      obtain ⟨h₁, -⟩ := ih f q (by simp at hq; omega) hi.2.2.2 hfresh
      refine ⟨?_, fun P s m => by rw [symB]; exact fine_junkB _⟩
      rw [sym]
      refine fine_projQ _ ?_
      unfold Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_gamma, h₁.1⟩, ⟨fun _ => noFun_termV _, hi.2.1, fun _ => noFun_transSelOpt _,
        h₁.2.1⟩, h₁.2.2.1, h₁.2.2.2⟩
    | GammaScalar ts fs q ord =>
      obtain ⟨h₁, -⟩ := ih (AggQueryIn.tri f 1) q (by simp at hq; omega) hi.2.2
        (fun i => ⟨(hfresh _).1, (hfresh _).2⟩)
      refine ⟨?_, fun P s m => by rw [symB]; exact fine_junkB _⟩
      rw [sym]
      refine fine_projQ _ ?_
      have hsum := fine_sumByMuX (Θ := Θ) (AggQueryIn.tri f 0 0) (AggQueryIn.tri f 0 1)
        (fine_projQ (padSA _) henv.desc) (fine_projQ (tagSA ValueType.nonzero) h₁)
        (noMention_projQ _ _ (hfresh 0).2.2.1) (noMention_projQ _ _ (hfresh 3).2.2.1)
        (noMention_projQ _ _ (noMention_sym env (hfresh 3).2 _ q (hfresh 3).1))
      unfold Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_gamma, hsum.1⟩, ⟨fun _ => by rw [TermIn.noFun_widen]; exact noFun_termV _,
        hi.2.1, fun _ => rfl, hsum.2.1⟩, hsum.2.2.1, hsum.2.2.2⟩
    | GammaNest is his p g q =>
      obtain ⟨h₁, -⟩ := ih f q (by simp at hq; omega) hi.2.2 hfresh
      refine ⟨?_, fun P s m => by rw [symB]; exact fine_junkB _⟩
      rw [sym]
      refine fine_projQ _ ?_
      unfold Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨⟨mem_gamma, rfl⟩, h₁.1⟩, ⟨SA.noFun_toG _, hi.2.1, h₁.2.1⟩, h₁.2.2.1, h₁.2.2.2⟩
    | Win P O o w t g q hrr dist keep =>
      obtain ⟨h₁, -⟩ := ih f q (by simp at hq; omega) hi.2.2.2 hfresh
      refine ⟨?_, fun P s m => by rw [symB]; exact fine_junkB _⟩
      rw [sym]
      refine fine_projQ _ ?_
      unfold Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_win, h₁.1⟩, ⟨noFun_termV _, hi.2.1, noFun_transSelOpt _, h₁.2.1⟩,
        ⟨rfl, h₁.2.2.1⟩, h₁.2.2.2⟩
    | Apply => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | Sum => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | Dedup => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | Diff => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | MuSet => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | GammaTok => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | ProvSum => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩
    | WinExpr => exact ⟨by rw [sym]; exact hemp _, fun P s m => by rw [symB]; exact fine_junkB _⟩

end SymFine

/-! ## The cut -/

section CutFine

variable {c : ℕ} {Θ : Set (SeqAggFunc T)} {cnt : SeqAggFunc T}

theorem fine_unionFin (f : ℕ → String) :
    ∀ (n : ℕ) (F : Fin n → AggQueryIn T c 1 (ColKind.allReg 1)), (∀ i j, (F i).noMention (f j)) →
      (∀ i, Fine Θ (F i)) → Fine Θ (unionFin f n F)
  | 0, _, _, _ => by rw [unionFin]; exact fine_emptyRel 1
  | n + 1, F, hF, h => by
    rw [unionFin]
    exact fine_sumByMuX _ _ (h 0) (fine_unionFin _ n _ (fun i j => hF i.succ (j + 2))
      (fun i => h i.succ)) (hF 0 0) (hF 0 1) (noMention_unionFin _ n _ (fun i => hF i.succ 1))

theorem fine_colsQ {N p : ℕ} (f : ℕ → String) {q : AggQueryIn T c N (ColKind.allReg N)}
    (idx : Fin p → Fin N) (hf : ∀ i, q.noMention (f i)) (h : Fine Θ q) : Fine Θ (colsQ f q idx) :=
  fine_unionFin f p _ (fun _ j => noMention_projQ _ _ (hf j)) (fun _ => fine_projQ _ h)

theorem fine_valsOf {N : ℕ} (f : ℕ → String) {q : AggQueryIn T c N (ColKind.allReg N)}
    (hf : ∀ i, q.noMention (f i)) (h : Fine Θ q) : Fine Θ (valsOf f q) :=
  fine_colsQ f id hf h

theorem fine_cutOf (f : ℕ → String) (S : Finset T) {core : AggQueryIn T c 1 (ColKind.allReg 1)}
    (hcore : ∀ i, core.noMention (f i)) (h : Fine Θ core) : Fine Θ (cutOf f S core) := by
  have hnull : Fine Θ (nullQ (T := T) (c := c)) := by
    unfold nullQ; split
    · exact fine_constQ _
    · exact fine_emptyRel 1
  have hamb : Fine Θ (ambQ (T := T) (part f 2) c) :=
    fine_unionFin _ c _ (fun _ _ => noMention_projQ _ _ (AggQueryIn.noMention_unitC _))
      (fun _ => fine_projQ _ fine_unitC)
  have hcs : Fine Θ (constsQ (c := c) (part f 4) S) :=
    fine_unionFin _ _ _ (fun _ _ => noMention_constQ _ _) (fun _ => fine_constQ _)
  unfold cutOf u2
  exact fine_sumByMuX _ _ (fine_sumByMuX _ _ hnull hamb (noMention_nullQ _) (noMention_nullQ _)
    (noMention_ambQ _ _)) (fine_sumByMuX _ _ hcs h (noMention_constsQ _ S _)
    (noMention_constsQ _ S _) (hcore _))
    (noMention_u2 _ (noMention_nullQ _) (noMention_ambQ _ _))
    (noMention_u2 _ (noMention_nullQ _) (noMention_ambQ _ _))
    (noMention_u2 _ (noMention_constsQ _ S _) (hcore _))

/-- **The cut is of the fragment.** -/
theorem fine_cutCore {k : ℕ} (hc : cnt ∈ Θ) :
    ∀ (N : ℕ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N → q.inSig Θ → (∀ i, q.noMention (f i)) →
      Fine Θ (cutCore cnt f q) := by
  intro N
  induction N with
  | zero =>
    intro f n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f n κ l q hq hi hfr
    -- the symbolic evaluation of an input relative to its node's cut
    have hsym : ∀ {m : ℕ} {κ' : Fin m → ColKind} (q : AggQueryIn T (k + c) m κ') (S : Finset T)
        (g : ℕ → String), (∀ i, q.noMention (g i)) → sizeOf q ≤ N → q.inSig Θ →
        (∀ i, q.noMention (f i)) →
        Fine Θ (sym (envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) g q)
          ∧ EnvFine Θ (envOf (part f 3) cnt k (cutOf (part f 4) S (cutCore cnt (part f 1) q))) := by
      intro m κ' q S g hg hs hiq hfq
      have hcore : ∀ s, q.noMention s →
          (cutOf (part f 4) S (cutCore cnt (part f 1) q)).noMention s :=
        fun s hs' => noMention_cutOf _ S (noMention_cutCore cnt _ _ q le_rfl hs')
      have henv := envFine_envOf (part f 3) hc k (fine_cutOf _ S
        (fun i => noMention_cutCore cnt _ _ q le_rfl (hfq _)) (ih (part f 1) q hs hiq
          (fun i => hfq _))) (fun i => hcore _ (hfq _))
      exact ⟨(fine_sym_aux _ henv _ g q le_rfl hiq
        (fun i => ⟨hg i, envNoMention_envOf _ cnt k _ (hcore _ (hg i))⟩)).1, henv⟩
    cases q with
    | Rel n s' => rw [cutCore]; exact fine_valsOf f hfr (fine_rel _ _)
    | Hole => rw [cutCore]; exact fine_emptyRel 1
    | Param => rw [cutCore]; exact fine_emptyRel 1
    | Empty => rw [cutCore]; exact fine_emptyRel 1
    | Proj ps q => rw [cutCore]; exact ih f q (by simp at hq; omega) hi.2 hfr
    | Sel φ q _ => rw [cutCore]; exact ih f q (by simp at hq; omega) hi.2 hfr
    | Prod q₁ q₂ =>
      rw [cutCore]
      exact fine_sumByMuX _ _ (ih _ q₁ (by simp at hq; omega) hi.1 (fun i => (hfr _).1))
        (ih _ q₂ (by simp at hq; omega) hi.2 (fun i => (hfr _).2))
        (noMention_cutCore cnt _ _ q₁ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₁ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₂ le_rfl (hfr _).2)
    | Explode _ _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hi hfr
    | Retag _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hi hfr
    | Mu s' q₀ q₁ =>
      rw [cutCore]
      exact fine_sumByMuX _ _ (ih _ q₀ (by simp at hq; omega) hi.1 (fun i => (hfr _).1))
        (ih _ q₁ (by simp at hq; omega) hi.2 (fun i => (hfr _).2))
        (noMention_cutCore cnt _ _ q₀ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₀ le_rfl (hfr _).1)
        (noMention_cutCore cnt _ _ q₁ le_rfl (hfr _).2)
    | Gamma is ts fs q keep ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hnm : ∀ s, q.noMention s → (gammaRaw (envOf (part f 3) cnt k (cutOf (part f 4)
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) is ts fs q keep ord).allConsts
          (cutCore cnt (part f 1) q))) (part f 5) is ts fs q keep).noMention s := by
        intro s hs'
        unfold gammaRaw; rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f _ q hs'
      obtain ⟨hsy, -⟩ := hsym q _ _ (fun i => hfr _) hs hi.2.2.2 hfr
      rw [cutCore]
      refine fine_sumByMuX _ _ (ih _ q hs hi.2.2.2 (fun i => hfr _))
        (fine_colsQ _ _ (fun i => hnm _ (hfr _)) ?_) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_cutCore cnt _ _ q le_rfl (hfr _)) (noMention_colsQ _ _ _ (hnm _ (hfr _)))
      unfold gammaRaw Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_gamma, hsy.1⟩, ⟨fun _ => noFun_termV _, hi.2.1, fun _ => noFun_transSelOpt _,
        hsy.2.1⟩, hsy.2.2.1, hsy.2.2.2⟩
    | GammaScalar ts fs q ord =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      obtain ⟨hsy, henv⟩ := hsym q _ (AggQueryIn.tri (part f 5) 1) (fun i => hfr _) hs hi.2.2 hfr
      have hcore : ∀ s, q.noMention s → (cutOf (part f 4)
          (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q ord).allConsts
          (cutCore cnt (part f 1) q)).noMention s :=
        fun s hs' => noMention_cutOf _ _ (noMention_cutCore cnt _ _ q le_rfl hs')
      have hnm : ∀ s, q.noMention s → (scalarRaw (envOf (part f 3) cnt k (cutOf (part f 4)
          (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q ord).allConsts
          (cutCore cnt (part f 1) q))) (part f 5) ts fs q).noMention s := by
        intro s hs'
        unfold scalarRaw; rw [AggQueryIn.noMention_allRegOf]
        refine AggQueryIn.noMention_sumByMuX _ _ _ _ ?_ ?_
        · rw [AggQueryIn.noMention_castKind]
          exact (envNoMention_envOf _ cnt k _ (hcore s hs')).2.1
        · rw [AggQueryIn.noMention_castKind]
          exact noMention_sym _ (envNoMention_envOf _ cnt k _ (hcore s hs')) _ q hs'
      have hsum := fine_sumByMuX (Θ := Θ) (AggQueryIn.tri (part f 5) 0 0)
        (AggQueryIn.tri (part f 5) 0 1) (fine_projQ (padSA _) henv.desc)
        (fine_projQ (tagSA ValueType.nonzero) hsy)
        (noMention_projQ _ _ (envNoMention_envOf _ cnt k _ (hcore _ (hfr _))).2.1)
        (noMention_projQ _ _ (envNoMention_envOf _ cnt k _ (hcore _ (hfr _))).2.1)
        (noMention_projQ _ _ (noMention_sym _ (envNoMention_envOf _ cnt k _ (hcore _ (hfr _))) _ q
          (hfr _)))
      rw [cutCore]
      refine fine_sumByMuX _ _ (ih _ q hs hi.2.2 (fun i => hfr _))
        (fine_colsQ _ _ (fun i => hnm _ (hfr _)) ?_) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_cutCore cnt _ _ q le_rfl (hfr _)) (noMention_colsQ _ _ _ (hnm _ (hfr _)))
      unfold scalarRaw Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_gamma, hsum.1⟩, ⟨fun _ => by rw [TermIn.noFun_widen]; exact noFun_termV _,
        hi.2.1, fun _ => rfl, hsum.2.1⟩, hsum.2.2.1, hsum.2.2.2⟩
    | GammaNest is his p g q =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hnm : ∀ s, q.noMention s → (nestRaw (envOf (part f 3) cnt k (cutOf (part f 4)
          (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) is his p g q).allConsts
          (cutCore cnt (part f 1) q))) (part f 5) is p g q).noMention s := by
        intro s hs'
        unfold nestRaw; rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f _ q hs'
      obtain ⟨hsy, -⟩ := hsym q _ _ (fun i => hfr _) hs hi.2.2 hfr
      rw [cutCore]
      refine fine_sumByMuX _ _ (ih _ q hs hi.2.2 (fun i => hfr _))
        (fine_colsQ _ _ (fun i => hnm _ (hfr _)) ?_) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_cutCore cnt _ _ q le_rfl (hfr _)) (noMention_colsQ _ _ _ (hnm _ (hfr _)))
      unfold nestRaw Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨⟨mem_gamma, rfl⟩, hsy.1⟩, ⟨SA.noFun_toG _, hi.2.1, hsy.2.1⟩, hsy.2.2.1, hsy.2.2.2⟩
    | Win P O o w t g q hrr dist keep =>
      have hs : sizeOf q ≤ N := by simp at hq; omega
      have hnm : ∀ s, q.noMention s → (winRaw (envOf (part f 3) cnt k (cutOf (part f 4)
          (AggQueryIn.Win (lab := 0) (rd := fun _ => false) P O o w t g q hrr dist keep).allConsts
          (cutCore cnt (part f 1) q))) (part f 5) P O o w t g q dist keep).noMention s := by
        intro s hs'
        unfold winRaw; rw [AggQueryIn.noMention_allRegOf]
        exact noMention_symCut cnt f _ q hs'
      obtain ⟨hsy, -⟩ := hsym q _ _ (fun i => hfr _) hs hi.2.2.2 hfr
      rw [cutCore]
      refine fine_sumByMuX _ _ (ih _ q hs hi.2.2.2 (fun i => hfr _))
        (fine_colsQ _ _ (fun i => hnm _ (hfr _)) ?_) (noMention_cutCore cnt _ _ q le_rfl (hfr _))
        (noMention_cutCore cnt _ _ q le_rfl (hfr _)) (noMention_colsQ _ _ _ (hnm _ (hfr _)))
      unfold winRaw Fine
      rw [AggQueryIn.usesOnly_allRegOf, AggQueryIn.inSig_allRegOf, winAllReg_allRegOf,
        AggQueryIn.hygienic_allRegOf]
      exact ⟨⟨mem_win, hsy.1⟩, ⟨noFun_termV _, hi.2.1, noFun_transSelOpt _, hsy.2.1⟩,
        ⟨rfl, hsy.2.2.1⟩, hsy.2.2.2⟩
    | Apply => rw [cutCore]; exact fine_emptyRel 1
    | Sum => rw [cutCore]; exact fine_emptyRel 1
    | Dedup => rw [cutCore]; exact fine_emptyRel 1
    | Diff => rw [cutCore]; exact fine_emptyRel 1
    | MuSet => rw [cutCore]; exact fine_emptyRel 1
    | GammaTok => rw [cutCore]; exact fine_emptyRel 1
    | ProvSum => rw [cutCore]; exact fine_emptyRel 1
    | WinExpr => rw [cutCore]; exact fine_emptyRel 1

end CutFine

/-! ## The table and the apply -/

section ApplyFine

variable {c k : ℕ} {Θ : Set (SeqAggFunc T)} {cnt : SeqAggFunc T}

theorem envFine_tabEnv (hc : cnt ∈ Θ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) (hi : q.inSig Θ) (hf : ∀ i, q.noMention (f i)) :
    EnvFine Θ (tabEnv cnt f q) :=
  envFine_envOf _ hc k (fine_cutOf _ _ (fun _ => noMention_cutCore cnt _ _ q le_rfl (hf _))
    (fine_cutCore hc _ _ q le_rfl hi (fun _ => hf _))) (fun _ => noMention_cutQ cnt _ q (hf _))

theorem fine_tabQ (hc : cnt ∈ Θ) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) (hi : q.inSig Θ) (hf : ∀ i, q.noMention (f i)) :
    Fine Θ (tabQ cnt f q) :=
  (fine_sym_aux _ (envFine_tabEnv hc f q hi hf) _ (part f 2) q le_rfl hi
    (fun _ => ⟨hf _, envNoMention_tabEnv cnt f q (hf _)⟩)).1

theorem fine_valsQ (f : ℕ → String) (env : SymEnv T k c) (henv : EnvFine Θ env)
    {VQ : AggQueryIn T c 1 (ColKind.allReg 1)} (hV : Fine Θ VQ)
    (hVf : VQ.noMention (f 0) ∧ VQ.noMention (f 1))
    (hCf : env.CQ.noMention (f 1)) : Fine Θ (valsQ f env VQ) :=
  fine_dedupG (fine_sumByMuX _ _ hV henv.cq hVf.1 hVf.2 hCf)

/-- **The apply written with products is of the fragment.** -/
theorem fine_applyX (hc : cnt ∈ Θ) (f : ℕ → String) {n₂ : ℕ} {l : List (String × ℕ)}
    {κ₂ : Fin n₂ → ColKind} {L : AggQueryIn T c k (ColKind.allReg k) l}
    {R : AggQueryIn T (k + c) n₂ κ₂} {VQ : AggQueryIn T c 1 (ColKind.allReg 1)}
    (hL : Fine Θ L) (hR : R.inSig Θ) (hV : Fine Θ VQ) (hfR : ∀ i, R.noMention (f i))
    (hfV : VQ.noMention (part f 1 0) ∧ VQ.noMention (part f 1 1)) :
    Fine Θ (applyX cnt f L R VQ) := by
  have henv := envFine_tabEnv hc (part f 0) R hR (fun i => hfR _)
  unfold applyX
  exact fine_projQ _ (fine_selSP _ _ (fine_prodR (fine_prodR (fine_prodR henv.desc
    (fine_tabQ hc _ R hR (fun i => hfR _))) (fine_powU (fine_valsQ _ _ henv hV hfV
      (noMention_cutQ cnt _ R (hfR _))) n₂)) hL))

end ApplyFine

end Sym
