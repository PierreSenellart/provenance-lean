import Provenance.AnnotatedProd

/-!
# The union from the bag recursion, annotated

`q₁ ⊎ q₂` is two bag recursions over one driver row (`sumByMuK`), as in
the plain semantics (`AggQueryIn.sumByMu`), now over operands of any
kinds: a round of a bag recursion carries aggregate columns, read through
the environment the evaluator binds its name in. The driver row's
aggregate columns hold a padding token (a count over the empty relation),
which the construction never reads and drops with the driver.

The rows the construction emits are the operands' rows, each with its
columns and its finalized annotation – the projections that re-tag a row
cash its pending group factors, so the agreement is up to finalization
(`AggQueryIn.FinEq`), which is all the annotated evaluation reads.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-! ## A query reads the environment's rounds only at its holes -/

/-- **A query reads the rounds of the environment only at its holes**, and
its context only at the arity it reads. -/
theorem AggQueryIn.evaluate_congr_holes :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (dB : AnnotatedDatabase T K) (γ : Fin c → T) {E E' : EvalEnv T K},
      (∀ p ∈ l, E.holes p.1 p.2 = E'.holes p.1 p.2) → E.ctxAt c γ = E'.ctxAt c γ →
      q.evaluate dB γ E = q.evaluate dB γ E' := by
  intro c n κ l q
  induction q with
  | Rel n s => intro dB γ E E' _ _; rfl
  | Hole n s κ =>
    intro dB γ E E' hh _
    simp only [AggQueryIn.evaluate, hh (s, n) (List.mem_singleton_self _)]
  | Param pv ρ =>
    intro dB γ E E' _ hc
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows, hc]
  | Empty => intro dB γ E E' _ _; rfl
  | Proj ps q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Sel φ q _ ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate,
      ih₁ dB γ (fun p hp => hh p (List.mem_append_left _ hp)) hc,
      ih₂ dB γ (fun p hp => hh p (List.mem_append_right _ hp)) hc]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate, ih₁ dB γ hh hc]
    refine Multiset.bind_congr (fun x _ => ?_)
    rw [ih₂ dB _ (E := E.withCtx (Fin.append x.fst (E.ctxAt _ γ)))
      (E' := E'.withCtx (Fin.append x.fst (E'.ctxAt _ γ))) (fun _ hp => absurd hp List.not_mem_nil)
      (by rw [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_withCtx, hc])]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate,
      ih₁ dB γ (fun p hp => hh p (List.mem_append_left _ hp)) hc,
      ih₂ dB γ (fun p hp => hh p (List.mem_append_right _ hp)) hc]
  | Dedup q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih₁ dB γ hh hc, ih₂ dB γ hh hc]
  | Explode k h q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate, ih₀ dB γ hh hc]
    exact muSumFix_congr (fun X => ih₁ dB γ (E := E.assignHole s X) (E' := E'.assignHole s X)
      (fun p hp => by rw [List.mem_singleton.mp hp, EvalEnv.assignHole_holes_self,
        EvalEnv.assignHole_holes_self]) hc) rfl
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate, ih₀ dB γ hh hc]
    refine congrArg _ (muFix_congr (fun X => ?_))
    rw [ih₁ dB γ (E := E.assignHole s (X.map GenRow.ofAnnotated))
      (E' := E'.assignHole s (X.map GenRow.ofAnnotated))
      (fun p hp => by rw [List.mem_singleton.mp hp, EvalEnv.assignHole_holes_self,
        EvalEnv.assignHole_holes_self]) hc]
  | Gamma is ts fs q keep ord ih =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, EvalEnv.paramKey, hc, ih dB γ hh hc]
  | GammaScalar ts fs q ord ih =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, EvalEnv.paramKey, hc, ih dB γ hh hc]
  | GammaNest is his p f q ih =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, EvalEnv.paramKey, hc, ih dB γ hh hc]
  | ProvSum is his t q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | Retag h q ih => intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, ih dB γ hh hc]
  | GammaTok is his ts fs a q keep ih =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, EvalEnv.paramKey, hc, ih dB γ hh hc]
  | Win P O o w t f q hrr dist keep ih =>
    intro dB γ E E' hh hc; simp only [AggQueryIn.evaluate, EvalEnv.paramKey, hc, ih dB γ hh hc]
  | WinExpr P O o ws ts fs g q keeps ih =>
    rename_i _ rd
    intro dB γ E E' hh hc
    simp only [AggQueryIn.evaluate]
    rw [ih dB γ hh hc,
      show E.paramKey rd γ = E'.paramKey rd γ by simp only [EvalEnv.paramKey, hc]]

/-- A closed query reads no round. -/
theorem AggQueryIn.evaluate_assignHole_closed {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (dB : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (s : String) {m : ℕ} (X : Multiset (GenRow T K m)) :
    q.evaluate dB γ (E.assignHole s X) = q.evaluate dB γ E :=
  AggQueryIn.evaluate_congr_holes q dB γ (fun _ hp => absurd hp List.not_mem_nil) rfl

/-- **Settling reads the rounds of the environment only at the holes**,
and its context only at the arity it reads. -/
theorem AggQueryIn.annSettlesAt_congr_holes :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (dB : AnnotatedDatabase T K) (γ : Fin c → T) {E E' : EvalEnv T K},
      (∀ p ∈ l, E.holes p.1 p.2 = E'.holes p.1 p.2) → E.ctxAt c γ = E'.ctxAt c γ →
      q.AnnSettlesAt dB γ E → q.AnnSettlesAt dB γ E' := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intros; trivial
  | Hole _ _ _ => intros; trivial
  | Param _ _ => intros; trivial
  | Empty => intros; trivial
  | Proj ps q ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | Sel φ q _ ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun dB γ _ _ hh hc h =>
      ⟨ih₁ dB γ (fun p hp => hh p (List.mem_append_left _ hp)) hc h.1,
        ih₂ dB γ (fun p hp => hh p (List.mem_append_right _ hp)) hc h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro dB γ E E' hh hc h
    refine ⟨ih₁ dB γ hh hc h.1, fun x hx => ?_⟩
    rw [← AggQueryIn.evaluate_congr_holes q₁ dB γ hh hc] at hx
    exact ih₂ dB _ (fun _ hp => absurd hp List.not_mem_nil)
      (by rw [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_withCtx, hc]) (h.2 x hx)
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun dB γ _ _ hh hc h =>
      ⟨ih₁ dB γ (fun p hp => hh p (List.mem_append_left _ hp)) hc h.1,
        ih₂ dB γ (fun p hp => hh p (List.mem_append_right _ hp)) hc h.2⟩
  | Dedup q ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun dB γ _ _ hh hc h => ⟨ih₁ dB γ hh hc h.1, ih₂ dB γ hh hc h.2⟩
  | Explode k hk q ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | Retag hk q ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro dB γ E E' hh hc h
    have hA : ∀ {m : ℕ} (X : Multiset (GenRow T K m)),
        ∀ p ∈ [(s, m)], (E.assignHole s X).holes p.1 p.2 = (E'.assignHole s X).holes p.1 p.2 :=
      fun X p hp => by
        rw [List.mem_singleton.mp hp, EvalEnv.assignHole_holes_self,
          EvalEnv.assignHole_holes_self]
    have hst : AggQueryIn.muStep s q₁ dB γ E = AggQueryIn.muStep s q₁ dB γ E' := by
      funext X
      exact AggQueryIn.evaluate_congr_holes q₁ dB γ (hA X) hc
    have h₀ : q₀.evaluate dB γ E = q₀.evaluate dB γ E' :=
      AggQueryIn.evaluate_congr_holes q₀ dB γ hh hc
    obtain ⟨hs₀, hz, hs, hk, hk0⟩ := h
    refine ⟨ih₀ dB γ hh hc hs₀, by rw [← hst]; exact hz, by rw [← hst, ← h₀]; exact hs,
      fun k => ?_, ih₁ dB γ (hA _) hc hk0⟩
    rw [← hst, ← h₀]
    exact ih₁ dB γ (hA _) hc (hk k)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro dB γ E E' hh hc h
    have hA : ∀ {m : ℕ} (X : Multiset (GenRow T K m)),
        ∀ p ∈ [(s, m)], (E.assignHole s X).holes p.1 p.2 = (E'.assignHole s X).holes p.1 p.2 :=
      fun X p hp => by
        rw [List.mem_singleton.mp hp, EvalEnv.assignHole_holes_self,
          EvalEnv.assignHole_holes_self]
    have hst : AggQueryIn.muSetStep s q₀ q₁ dB γ E = AggQueryIn.muSetStep s q₀ q₁ dB γ E' := by
      funext X
      unfold AggQueryIn.muSetStep AggQueryIn.evaluateAnnotated
      rw [AggQueryIn.evaluate_congr_holes q₀ dB γ hh hc,
        AggQueryIn.evaluate_congr_holes q₁ dB γ (hA _) hc]
    obtain ⟨hs₀, hs, hk⟩ := h
    refine ⟨ih₀ dB γ hh hc hs₀, by rw [← hst]; exact hs, fun k => ?_⟩
    rw [← hst]
    exact ih₁ dB γ (hA _) hc (hk k)
  | Gamma is ts fs q keep ord ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | GammaScalar ts fs q ord ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | GammaNest is his p g q ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | ProvSum is his t q ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | GammaTok is his ts fs a q keep ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | Win P O o w t g q hrr dist keep ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun dB γ _ _ hh hc h => ih dB γ hh hc h

/-- A closed query settles alike at two environments with one context. -/
theorem AggQueryIn.annSettlesAt_closed {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (dB : AnnotatedDatabase T K) (γ : Fin c → T) {E E' : EvalEnv T K}
    (hc : E.ctxAt c γ = E'.ctxAt c γ) (h : q.AnnSettlesAt dB γ E) : q.AnnSettlesAt dB γ E' :=
  AggQueryIn.annSettlesAt_congr_holes q dB γ (fun _ hp => absurd hp List.not_mem_nil) hc h

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Well-kindedness reads the kinds of the rounds only at the holes.** -/
theorem AggQueryIn.wellKinded_congr_holes :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (ρc : Fin c → ColKind) {HK HK' : HoleKinds},
      (∀ p ∈ l, ∀ k, (HK p.1 p.2 k).base = (HK' p.1 p.2 k).base) →
      q.wellKinded ρc HK → q.wellKinded ρc HK' := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intros; trivial
  | Hole n s κ =>
    intro ρc HK HK' hh h k
    rw [h k]
    exact hh (s, n) (List.mem_singleton_self _) k
  | Param _ _ => exact fun _ _ _ _ h => h
  | Empty => intros; trivial
  | Proj ps q ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩
  | Sel φ q _ ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun ρc _ _ hh h =>
      ⟨ih₁ ρc (fun p hp => hh p (List.mem_append_left _ hp)) h.1,
        ih₂ ρc (fun p hp => hh p (List.mem_append_right _ hp)) h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun ρc _ _ hh h => ⟨ih₁ ρc hh h.1, ih₂ _ (fun _ hp => absurd hp List.not_mem_nil) h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun ρc _ _ hh h =>
      ⟨ih₁ ρc (fun p hp => hh p (List.mem_append_left _ hp)) h.1,
        ih₂ ρc (fun p hp => hh p (List.mem_append_right _ hp)) h.2⟩
  | Dedup q ih => exact fun ρc _ _ hh h => ih ρc hh h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun ρc _ _ hh h => ⟨ih₁ ρc hh h.1, ih₂ ρc hh h.2⟩
  | Explode k hk q ih => exact fun ρc _ _ hh h => ih ρc hh h
  | Retag hk q ih => exact fun ρc _ _ hh h => ih ρc hh h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro ρc HK HK' hh h
    refine ⟨ih₀ ρc hh h.1, ih₁ ρc (fun p hp => ?_) h.2⟩
    obtain rfl := List.mem_singleton.mp hp
    intro k
    rw [HoleKinds.assign_self, HoleKinds.assign_self]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro ρc HK HK' hh h
    refine ⟨ih₀ ρc hh h.1, ih₁ ρc (fun p hp => ?_) h.2⟩
    obtain rfl := List.mem_singleton.mp hp
    intro k
    rw [HoleKinds.assign_self, HoleKinds.assign_self]
  | Gamma is ts fs q keep ord ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩
  | GammaScalar ts fs q ord ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩
  | GammaNest is his p g q ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩
  | ProvSum is his t q ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩
  | GammaTok is his ts fs a q keep ih => exact fun ρc _ _ hh h => ⟨h.1, h.2.1, ih ρc hh h.2.2⟩
  | Win P O o w t g q hrr dist keep ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun ρc _ _ hh h => ⟨h.1, ih ρc hh h.2⟩

/-! ## The construction, over operands of any kinds -/

namespace AggQueryIn

variable {c k : ℕ}

/-- The kinds of a tagged row: a regular tag, then the row's own kinds. -/
abbrev tagKind (κ : Fin k → ColKind) : Fin (k + 1) → ColKind := Fin.cons ColKind.reg κ

/-- The columns of a row with a constant tag prepended, the row's own
columns carried through whatever their kinds. -/
def withTagColsK (κ : Fin k → ColKind) (t : T) : Fin (k + 1) → ProjColIn T c κ :=
  Fin.cons (α := fun _ => ProjColIn T c κ) (ProjColIn.term (TermGIn.const t))
    (fun i => carryColIn κ i)

omit [ValueType T] in
theorem withTagColsK_kind (κ : Fin k → ColKind) (t : T) :
    (fun j => ((withTagColsK (c := c) κ t) j).kind) = tagKind κ := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · exact carryColIn_kind κ i

/-- **A relation with the tag `t` prepended to every row.** -/
def withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ) :
    AggQueryIn T c (k + 1) (tagKind κ) :=
  (AggQueryIn.Proj (withTagColsK κ t) q).castKind (withTagColsK_kind κ t)

/-- A padding column of kind `κ i` over a row of aggregate columns: a
constant where the kind holds a value, the row's own token where it holds
an aggregate. -/
def padColK (κ : Fin k → ColKind) (i : Fin k) : ProjColIn T c (fun _ : Fin k => ColKind.agg) :=
  match κ i with
  | ColKind.reg => .term (TermGIn.const 0)
  | ColKind.agg => .token i rfl
  | ColKind.prov => .provTerm (TermGIn.const 0)

theorem padColK_kind (κ : Fin k → ColKind) (i : Fin k) :
    (padColK (T := T) (c := c) κ i).kind = κ i := by
  unfold padColK
  split
  · next h => exact h.symm
  · next h => exact h.symm
  · next h => exact h.symm

theorem driverCols_kind (κ : Fin k → ColKind) (t : T) :
    (fun j => ((Fin.cons (α := fun _ => ProjColIn T c (fun _ : Fin k => ColKind.agg))
      (ProjColIn.term (TermGIn.const t)) (padColK κ) : Fin (k + 1) → _) j).kind) = tagKind κ := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · exact padColK_kind κ i

/-- **The driver row**: tag `t`, the other columns padding – a token of
the count of the empty relation where the kind is aggregate. -/
def driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T) :
    AggQueryIn T c (k + 1) (tagKind κ) :=
  (AggQueryIn.Proj
    (Fin.cons (α := fun _ => ProjColIn T c (fun _ : Fin k => ColKind.agg))
      (ProjColIn.term (TermGIn.const t)) (padColK κ))
    (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) (fun _ : Fin k => TermIn.const 0)
        (fun _ => cnt)
      (AggQueryIn.Empty : AggQueryIn T c 0 (ColKind.allReg 0)))).castKind
    (driverCols_kind κ t)

theorem tagKind_append_left (κ : Fin k → ColKind) :
    Fin.append (tagKind κ) (tagKind κ) (Fin.castAdd (k + 1) 0) = ColKind.reg := by
  rw [Fin.append_left]; rfl

theorem tagKind_append_right (κ : Fin k → ColKind) :
    Fin.append (tagKind κ) (tagKind κ) (Fin.natAdd (k + 1) 0) = ColKind.reg := by
  rw [Fin.append_right]; rfl

/-- The columns a round's rows are projected to: the tag `p₁`, then the
columns of the right factor past its tag, carried through. -/
def roundColsK (κ : Fin k → ColKind) (p₁ : T) :
    Fin (k + 1) → ProjColIn T c (Fin.append (tagKind κ) (tagKind κ)) :=
  Fin.cons (α := fun _ => ProjColIn T c _) (ProjColIn.term (TermGIn.const p₁))
    (fun i => carryColIn (Fin.append (tagKind κ) (tagKind κ)) (Fin.natAdd (k + 1) (Fin.succ i)))

omit [ValueType T] in
theorem roundColsK_kind (κ : Fin k → ColKind) (p₁ : T) :
    (fun j => ((roundColsK (c := c) κ p₁) j).kind) = tagKind κ := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · show (carryColIn _ _).kind = _
    rw [carryColIn_kind, Fin.append_right]

/-- The selection keeping the pairs whose two tags agree. -/
def sameTagK (κ : Fin k → ColKind) : GenPredIn T c (Fin.append (tagKind κ) (tagKind κ)) :=
  GenPredIn.cmp CompOp.syneq
    (TermGIn.index (Fin.castAdd (k + 1) 0) (tagKind_append_left κ))
    (TermGIn.index (Fin.natAdd (k + 1) 0) (tagKind_append_right κ))

/-- **A round of the construction**: the rows of the recursive relation
carrying `Z`'s tag each read `Z`, whose rows are re-tagged `p₁`. -/
def phaseBodyK {κ : Fin k → ColKind} (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) :
    AggQueryIn T c (k + 1) (tagKind κ) [(s, k + 1)] :=
  (AggQueryIn.Proj (roundColsK κ p₁)
    (AggQueryIn.Sel (sameTagK κ) (AggQueryIn.Apply (AggQueryIn.Hole (k + 1) s (tagKind κ))
      (Z.substMap (applyOuter T c (k + 1)))) (SelOK.of_noAggAtom rfl))).castKind
    (roundColsK_kind κ p₁)

/-- The selection dropping the rows tagged `p₀`. -/
def notTagK (κ : Fin k → ColKind) (p₀ : T) : GenPredIn T c (tagKind κ) :=
  GenPredIn.not (GenPredIn.cmp CompOp.syneq (TermGIn.index 0 rfl) (TermGIn.const p₀))

/-- The columns past the tag. -/
def unwithTagColsK (κ : Fin k → ColKind) : Fin k → ProjColIn T c (tagKind κ) :=
  fun i => carryColIn (tagKind κ) (Fin.succ i)

omit [ValueType T] in
theorem unwithTagColsK_kind (κ : Fin k → ColKind) :
    (fun i => ((unwithTagColsK (T := T) (c := c) κ) i).kind) = κ := by
  funext i
  exact carryColIn_kind _ _

/-- **`⊎` from two bag recursions, over operands of any kinds**: `s₁`
binds the recursion listing `q₁`'s rows behind the driver, `s₂` the one
adding `q₂`'s. The phases are `0` and `ValueType.nonzero`. -/
def sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) : AggQueryIn T c k κ :=
  (AggQueryIn.Proj (unwithTagColsK κ)
    (AggQueryIn.Sel (notTagK κ 0)
      (AggQueryIn.Mu s₂
        (AggQueryIn.Mu s₁ (driverK κ cnt 0) (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)))
        (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂))))).castKind (unwithTagColsK_kind κ)

end AggQueryIn

/-! ## What the construction computes, up to finalization -/

namespace AggQueryIn

variable {c k : ℕ}

/-- A row with a regular tag prepended. -/
def tagG (t : T) (u : Tuple (GenValue T K) k) : Tuple (GenValue T K) (k + 1) :=
  Fin.cons (Sum.inl t) u

theorem holdsPlain_sameTagK {κ : Fin k → ColKind} (u : Tuple T ((k + 1) + (k + 1)))
    (γ : Fin c → T) :
    (sameTagK (c := c) κ).holdsPlain u γ
      ↔ u (Fin.castAdd (k + 1) 0) = u (Fin.natAdd (k + 1) 0) := by
  show CompOp.eval3 CompOp.syneq (u (Fin.castAdd (k + 1) 0)) (u (Fin.natAdd (k + 1) 0))
    = Kleene.true ↔ _
  simp [CompOp.eval3, CompOp.strict, CompOp.eval]

theorem holdsPlain_notTagK {κ : Fin k → ColKind} (p₀ : T) (u : Tuple T (k + 1))
    (γ : Fin c → T) : (notTagK (c := c) κ p₀).holdsPlain u γ ↔ u 0 ≠ p₀ := by
  show (CompOp.eval3 CompOp.syneq (u 0) p₀).not = Kleene.true ↔ _
  rw [Kleene.not_eq_true_iff]
  by_cases h : u 0 = p₀ <;> simp [CompOp.eval3, CompOp.strict, CompOp.eval, Kleene.ofBool, h]

omit [HasAltLinearOrder K] in
/-- The finalization of a projected row: its columns, and the
finalization of the row it is projected from. -/
theorem fin_proj {n m : ℕ} {κ : Fin n → ColKind} (ps : Fin m → ProjColIn T c κ)
    (x : GenRow T K n) (γ : Fin c → T) :
    GenRow.fin ((fun j => (ps j).eval x.1 γ,
        (⟨x.2.base * (Multiset.map (fun l => SemiringWithMonus.delta l.sum)
          (x.2.pending - x.2.pending ∩ tokenLists fun j => (ps j).eval x.1 γ)).prod,
          x.2.pending ∩ tokenLists fun j => (ps j).eval x.1 γ⟩ : GenAnn K)) : GenRow T K m)
      = (fun j => (ps j).eval x.1 γ, x.2.finalize) :=
  Prod.ext rfl (GenAnn.finalize_cash' _ _ Multiset.inter_le_left)

/-- **The rows of a tagged relation**: the relation's rows, the tag
prepended, the finalized annotation kept. -/
theorem evaluate_withTagK_fin {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    ((withTagK t q).evaluate d γ E).map GenRow.fin
      = (q.evaluate d γ E).map (fun r => (tagG t r.fst, r.snd.finalize)) := by
  rw [withTagK, AggQueryIn.evaluate_castKind]
  simp only [AggQueryIn.evaluate, Multiset.map_map]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  simp only [Function.comp_apply, fin_proj]
  refine Prod.ext (funext fun j => ?_) rfl
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · show (carryColIn κ i).eval r.fst γ = r.fst i
    exact eval_carryColIn κ i r.fst γ (AggQueryIn.evaluate_conform q d r hr i)

/-- **The driver row**: one row, tagged `t`, its annotation finalizing to
`𝟙`. -/
theorem evaluate_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    ∃ r₀ : GenRow T K (k + 1), (driverK (c := c) κ cnt t).evaluate d γ E = {r₀}
      ∧ GenRow.plainTuple r₀.fst 0 = t ∧ r₀.snd.finalize = 1 := by
  rw [driverK, AggQueryIn.evaluate_castKind]
  simp only [AggQueryIn.evaluate]
  rw [Multiset.map_singleton]
  refine ⟨_, rfl, rfl, ?_⟩
  rw [GenAnn.finalize_cash' _ _ Multiset.inter_le_left]
  simp [GenAnn.finalize]


/-- The rows of a tagged relation carry the tag. -/
theorem tag_of_mem_withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {w : GenRow T K (k + 1)}
    (hw : w ∈ (withTagK t q).evaluate d γ E) : GenRow.plainTuple w.fst 0 = t := by
  have hm : GenRow.fin w ∈ ((withTagK t q).evaluate d γ E).map GenRow.fin :=
    Multiset.mem_map_of_mem _ hw
  rw [evaluate_withTagK_fin] at hm
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hm
  have h1 : w.fst = tagG t r.fst := (congrArg Prod.fst hr).symm
  rw [h1]
  rfl

/-- **One round of the construction**, up to finalization: each row of
the round carrying the tag `t₀` is replaced by the rows of `q`, re-tagged
`p₁`, their annotations multiplied by the row's. -/
theorem evaluate_phaseBodyK_fin {κ : Fin k → ColKind} (s : String) (p₁ t₀ : T)
    (q : AggQueryIn T c k κ) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (X : Multiset (GenRow T K (k + 1))) (hX : ∀ x ∈ X, GenRow.Conforms (tagKind κ) x.fst) :
    ((phaseBodyK s p₁ (withTagK t₀ q)).evaluate d γ (E.assignHole s X)).map GenRow.fin
      = X.bind (fun x => if GenRow.plainTuple x.fst 0 = t₀ then
          (q.evaluate d γ E).map (fun r => (tagG p₁ r.fst, x.snd.finalize * r.snd.finalize))
        else 0) := by
  rw [phaseBodyK, AggQueryIn.evaluate_castKind]
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_right (show ¬ (sameTagK (T := T) (c := c) κ).hasAggAtom = true from
      Bool.false_ne_true), EvalEnv.assignHole_holes_self, Multiset.filter_eq_self.mpr hX]
  simp only [AggQueryIn.evaluate_applyOuter, AggQueryIn.evaluate_assignHole_closed]
  rw [Multiset.filter_bind, Multiset.map_bind, Multiset.map_bind]
  refine Multiset.bind_congr (fun x hx => ?_)
  have hW : ∀ w ∈ (withTagK t₀ q).evaluate d γ E, GenRow.Conforms (tagKind κ) w.fst :=
    fun w hw k => AggQueryIn.evaluate_conform _ d w hw k
  rw [Multiset.filter_map]
  by_cases hx0 : GenRow.plainTuple x.fst 0 = t₀
  · rw [ite_eq_left hx0]
    rw [Multiset.filter_eq_self.mpr (fun w hw => ?_)]
    · rw [Multiset.map_map, Multiset.map_map]
      rw [Multiset.map_congr rfl (fun w hw => ?_)]
      · rw [← Multiset.map_map (fun (p : Tuple (GenValue T K) (k + 1) × K) =>
          ((tagG p₁ (fun i => p.1 (Fin.succ i)) : Tuple (GenValue T K) (k + 1)),
            x.snd.finalize * p.2)) GenRow.fin, evaluate_withTagK_fin, Multiset.map_map]
        rfl
      · simp only [Function.comp_apply]
        refine Prod.ext (funext fun j => ?_) ?_
        · refine Fin.cases ?_ (fun i => ?_) j
          · rfl
          · show (carryColIn (Fin.append (tagKind κ) (tagKind κ))
                (Fin.natAdd (k + 1) (Fin.succ i))).eval (Fin.append x.fst w.fst) γ = _
            rw [eval_carryColIn _ _ _ _ (kindOf_append (hX x hx) (hW w hw) _), Fin.append_right]
            rfl
        · show GenAnn.finalize _ = _
          rw [GenAnn.finalize_cash' (GenAnn.mk (x.snd.base * w.snd.base)
            (x.snd.pending + w.snd.pending)) _ Multiset.inter_le_left]
          exact GenAnn.finalize_mul' x.snd w.snd
    · show (sameTagK κ).holds (Fin.append x.fst w.fst) γ
      rw [GenPredIn.holds_iff_holdsPlain, holdsPlain_sameTagK]
      unfold GenRow.plainTuple
      rw [Fin.append_left, Fin.append_right]
      exact hx0.trans (tag_of_mem_withTagK t₀ q d γ E hw).symm
  · rw [ite_eq_right hx0]
    rw [Multiset.filter_eq_nil.mpr ?_]
    · simp
    intro w hw h
    change (sameTagK κ).holds (Fin.append x.fst w.fst) γ at h
    rw [GenPredIn.holds_iff_holdsPlain, holdsPlain_sameTagK] at h
    unfold GenRow.plainTuple at h
    rw [Fin.append_left, Fin.append_right] at h
    exact hx0 (h.trans (tag_of_mem_withTagK t₀ q d γ E hw))


/-- A bag recursion whose second round is empty is its base and its first
round. -/
theorem muSumFix_two {α : Type} {step : Multiset α → Multiset α} {M : Multiset α}
    (h0 : step 0 = 0) (h2 : step (step M) = 0) : muSumFix step M = M + step M := by
  rw [muSumFix_eq_of_empty (k := 1) h0 h2]
  rfl

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A map reading only a row's finalization factors through it. -/
theorem map_via_fin {n : ℕ} (X : Multiset (GenRow T K n)) {β : Type}
    (G : GenRow T K n → β) (G' : Tuple (GenValue T K) n × K → β)
    (h : ∀ x ∈ X, G x = G' (GenRow.fin x)) : X.map G = (X.map GenRow.fin).map G' := by
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl h

/-- The rows of one round that carry a tag other than the round's operand
read nothing. -/
theorem evaluate_phaseBodyK_of_tags {κ : Fin k → ColKind} (s : String) (p₁ t₀ : T)
    (q : AggQueryIn T c k κ) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (X : Multiset (GenRow T K (k + 1))) (hX : ∀ x ∈ X, GenRow.Conforms (tagKind κ) x.fst)
    (ht : ∀ x ∈ X, GenRow.plainTuple x.fst 0 ≠ t₀) :
    (phaseBodyK s p₁ (withTagK t₀ q)).evaluate d γ (E.assignHole s X) = 0 := by
  refine (Multiset.map_eq_zero (f := GenRow.fin)).mp ?_
  rw [evaluate_phaseBodyK_fin s p₁ t₀ q d γ E X hX]
  rw [Multiset.bind_congr (g := fun _ => 0) (fun x hx => ite_eq_right (ht x hx))]
  simp

/-- The tag of a row of one round. -/
theorem tag_of_mem_phaseBodyK {κ : Fin k → ColKind} (s : String) (p₁ t₀ : T)
    (q : AggQueryIn T c k κ) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (X : Multiset (GenRow T K (k + 1))) (hX : ∀ x ∈ X, GenRow.Conforms (tagKind κ) x.fst)
    {w : GenRow T K (k + 1)} (hw : w ∈ (phaseBodyK s p₁ (withTagK t₀ q)).evaluate d γ
      (E.assignHole s X)) : GenRow.plainTuple w.fst 0 = p₁ := by
  have hm : GenRow.fin w ∈ ((phaseBodyK s p₁ (withTagK t₀ q)).evaluate d γ
      (E.assignHole s X)).map GenRow.fin := Multiset.mem_map_of_mem _ hw
  rw [evaluate_phaseBodyK_fin s p₁ t₀ q d γ E X hX] at hm
  obtain ⟨x, -, hx⟩ := Multiset.mem_bind.mp hm
  split at hx
  · obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hx
    have h1 : w.fst = tagG p₁ r.fst := (congrArg Prod.fst hr).symm
    rw [h1]
    rfl
  · exact absurd hx (Multiset.notMem_zero _)


/-- **What the union by recursion computes**: the rows of both operands,
with their columns and their finalized annotations. -/
theorem evaluate_sumByMuK_fin {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    ((sumByMuK s₁ s₂ cnt q₁ q₂).evaluate d γ E).map GenRow.fin
      = (q₁.evaluate d γ E).map GenRow.fin + (q₂.evaluate d γ E).map GenRow.fin := by
  have hnz : (ValueType.nonzero : T) ≠ 0 := ValueType.nonzero_ne_zero
  obtain ⟨r₀, hM, hr₀t, hr₀f⟩ := evaluate_driverK (c := c) κ cnt (0 : T) d γ E
  have hr₀m : r₀ ∈ (driverK (c := c) κ cnt (0 : T)).evaluate d γ E := by
    rw [hM]; exact Multiset.mem_singleton_self r₀
  have hr₀c : GenRow.Conforms (tagKind κ) r₀.fst := fun j =>
    AggQueryIn.evaluate_conform (driverK κ cnt 0) d r₀ hr₀m j
  have hM₁ : ∀ x ∈ ({r₀} : Multiset (GenRow T K (k + 1))), GenRow.Conforms (tagKind κ) x.fst :=
    fun x hx => by rw [Multiset.mem_singleton.mp hx]; exact hr₀c
  -- a round of either recursion
  have hc : ∀ (s : String) (q : AggQueryIn T c k κ) (X : Multiset (GenRow T K (k + 1))),
      ∀ x ∈ (phaseBodyK s ValueType.nonzero (withTagK 0 q)).evaluate d γ (E.assignHole s X),
        GenRow.Conforms (tagKind κ) x.fst :=
    fun s q X x hx j => AggQueryIn.evaluate_conform _ d x hx j
  have h0 : ∀ (s : String) (q : AggQueryIn T c k κ),
      (phaseBodyK s ValueType.nonzero (withTagK 0 q)).evaluate d γ
        (E.assignHole s (0 : Multiset (GenRow T K (k + 1)))) = 0 :=
    fun s q => evaluate_phaseBodyK_of_tags s _ 0 q d γ E 0
      (fun x hx => absurd hx (Multiset.notMem_zero x))
      (fun x hx => absurd hx (Multiset.notMem_zero x))
  -- the first recursion: the driver, then `q₁`'s rows tagged `nonzero`
  have h2₁ : (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁
      ((phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁ {r₀})))
      = 0 :=
    evaluate_phaseBodyK_of_tags s₁ _ 0 q₁ d γ E _ (hc s₁ q₁ _) (fun x hx => by
      rw [tag_of_mem_phaseBodyK s₁ _ 0 q₁ d γ E _ hM₁ hx]; exact hnz)
  have hin : muSumFix (fun X => (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ
      (E.assignHole s₁ X)) {r₀}
      = {r₀} + (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ
        (E.assignHole s₁ {r₀}) := muSumFix_two (h0 s₁ q₁) h2₁
  have hf₁ : ((phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ
      (E.assignHole s₁ {r₀})).map GenRow.fin
      = (q₁.evaluate d γ E).map (fun r => (tagG ValueType.nonzero r.fst, r.snd.finalize)) := by
    rw [evaluate_phaseBodyK_fin s₁ _ 0 q₁ d γ E _ hM₁, Multiset.singleton_bind,
      ite_eq_left hr₀t, hr₀f]
    simp only [one_mul]
  -- the second recursion, over the first's value
  obtain ⟨B, hB⟩ : ∃ B : Multiset (GenRow T K (k + 1)), B = {r₀}
      + (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁ {r₀}) :=
    ⟨_, rfl⟩
  have hBc : ∀ x ∈ B, GenRow.Conforms (tagKind κ) x.fst := fun x hx => by
    rw [hB] at hx
    exact (Multiset.mem_add.mp hx).elim (hM₁ x) (hc s₁ q₁ _ x)
  have h2₂ : (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ (E.assignHole s₂
      ((phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ (E.assignHole s₂ B)))
      = 0 :=
    evaluate_phaseBodyK_of_tags s₂ _ 0 q₂ d γ E _ (hc s₂ q₂ _) (fun x hx => by
      rw [tag_of_mem_phaseBodyK s₂ _ 0 q₂ d γ E B hBc hx]; exact hnz)
  have hout : muSumFix (fun X => (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ
      (E.assignHole s₂ X)) B
      = B + (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ
        (E.assignHole s₂ B) := muSumFix_two (h0 s₂ q₂) h2₂
  have hf₂ : ((phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ
      (E.assignHole s₂ B)).map GenRow.fin
      = (q₂.evaluate d γ E).map (fun r => (tagG ValueType.nonzero r.fst, r.snd.finalize)) := by
    rw [evaluate_phaseBodyK_fin s₂ _ 0 q₂ d γ E _ hBc]
    conv_lhs => rw [hB]
    rw [Multiset.add_bind, Multiset.singleton_bind, ite_eq_left hr₀t, hr₀f,
      Multiset.bind_congr (g := fun _ => 0) (fun x hx => ite_eq_right (by
        rw [tag_of_mem_phaseBodyK s₁ _ 0 q₁ d γ E _ hM₁ hx]; exact hnz))]
    simp only [one_mul, Multiset.bind_zero, add_zero]
  -- the selection drops the driver, the projection the tag
  rw [sumByMuK, AggQueryIn.evaluate_castKind]
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_right (show ¬ (notTagK (T := T) (c := c) κ 0).hasAggAtom = true from
    Bool.false_ne_true)]
  erw [hM, hin, ← hB, hout]
  have hS₂c := hc s₂ q₂ B
  have hP : ∀ x : GenRow T K (k + 1), (notTagK κ 0).holds x.fst γ
      ↔ GenRow.plainTuple x.fst 0 ≠ 0 := fun x => by
    rw [GenPredIn.holds_iff_holdsPlain, holdsPlain_notTagK]
  rw [Multiset.map_map, map_via_fin _ _
    (fun p : Tuple (GenValue T K) (k + 1) × K =>
      ((fun i => (p.1 : Fin (k + 1) → GenValue T K) (Fin.succ i) : Tuple (GenValue T K) k), p.2))
    ?_]
  · have hfB : B.filter (fun r => (notTagK κ 0).holds r.1 γ)
        = (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ
            (E.assignHole s₁ {r₀}) := by
      rw [hB, Multiset.filter_add, Multiset.filter_singleton,
        ite_eq_right (by rw [hP, hr₀t]; exact fun h => h rfl), Multiset.empty_eq_zero, zero_add,
        Multiset.filter_eq_self.mpr (fun x hx => (hP x).mpr (by
          rw [tag_of_mem_phaseBodyK s₁ _ 0 q₁ d γ E _ hM₁ hx]; exact hnz))]
    rw [Multiset.filter_add, Multiset.map_add, Multiset.map_add, hfB,
      Multiset.filter_eq_self.mpr (fun x hx => (hP x).mpr (by
        rw [tag_of_mem_phaseBodyK s₂ _ 0 q₂ d γ E B hBc hx]; exact hnz)),
      hf₁, hf₂, Multiset.map_map, Multiset.map_map]
    rfl
  · intro x hx
    have hxc : GenRow.Conforms (tagKind κ) x.fst :=
      (Multiset.mem_add.mp (Multiset.mem_of_mem_filter hx)).elim (hBc x) (hS₂c x)
    simp only [Function.comp_apply]
    refine Prod.ext (funext fun i => ?_) (GenAnn.finalize_cash' _ _ Multiset.inter_le_left)
    exact eval_carryColIn (tagKind κ) (Fin.succ i) x.fst γ (hxc _)

end AggQueryIn

/-! ## An empty relation of any kinds -/

namespace AggQueryIn

variable {c k : ℕ}

/-- **An empty relation of any kinds**: the driver row, dropped. Unlike
`AggQueryIn.emptyOf`, whose parameter leaf reads constants, its aggregate
columns hold tokens, so it is well-kinded at every kind vector. -/
def emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) : AggQueryIn T c k κ :=
  (AggQueryIn.Proj (unwithTagColsK κ)
    (AggQueryIn.Sel (notTagK κ 0) (driverK κ cnt 0))).castKind (unwithTagColsK_kind κ)

theorem evaluate_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) : (emptyK κ cnt).evaluate d γ E = 0 := by
  obtain ⟨r₀, hM, hr₀t, -⟩ := evaluate_driverK (c := c) κ cnt (0 : T) d γ E
  rw [emptyK, AggQueryIn.evaluate_castKind]
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_right (show ¬ (notTagK (T := T) (c := c) κ 0).hasAggAtom = true from
    Bool.false_ne_true)]
  erw [hM]
  rw [Multiset.filter_singleton, ite_eq_right (by
    rw [GenPredIn.holds_iff_holdsPlain, holdsPlain_notTagK, hr₀t]; exact fun h => h rfl)]
  rfl

end AggQueryIn

/-! ## What the construction keeps -/

namespace AggQueryIn

variable {c k : ℕ}

theorem padColK_sourceCol (κ : Fin k → ColKind) (i : Fin k) :
    (padColK (T := T) (c := c) κ i).sourceCol = true := by
  unfold padColK; split <;> rfl

theorem padColK_noFun (κ : Fin k → ColKind) (i : Fin k) :
    (padColK (T := T) (c := c) κ i).noFun = true := by
  unfold padColK; split <;> rfl

theorem padColK_outerOk (κ : Fin k → ColKind) (i : Fin k) (ok : Fin c → Prop) :
    (padColK (T := T) (c := c) κ i).outerOk ok := by
  unfold padColK; split <;> trivial

theorem usesOnly_driverK {S : Set OpKind} (hS : sumMuOps ⊆ S) (κ : Fin k → ColKind)
    (cnt : SeqAggFunc T) (t : T) : (driverK (c := c) κ cnt t).usesOnly S := by
  rw [driverK, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumMuOps]), fun j => Fin.cases rfl (padColK_sourceCol κ) j⟩,
    hS (by simp [sumMuOps]), hS (by simp [sumMuOps])⟩

theorem inSig_driverK {Θ : Set (SeqAggFunc T)} (κ : Fin k → ColKind) {cnt : SeqAggFunc T}
    (hcnt : cnt ∈ Θ) (t : T) : (driverK (c := c) κ cnt t).inSig Θ := by
  rw [driverK, AggQueryIn.inSig_castKind]
  exact ⟨fun j => Fin.cases rfl (padColK_noFun κ) j, fun _ => rfl, fun _ => hcnt, trivial⟩

theorem wellKinded_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T)
    (ρc : Fin c → ColKind) (HK : HoleKinds) : (driverK (c := c) κ cnt t).wellKinded ρc HK := by
  rw [driverK, AggQueryIn.wellKinded_castKind]
  exact ⟨fun j => Fin.cases trivial (fun i => padColK_outerOk κ i _) j, fun _ => trivial, trivial⟩

theorem names_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T) :
    (driverK (c := c) κ cnt t).names = ∅ := by
  rw [driverK, AggQueryIn.names_castKind]; rfl

theorem noMention_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T) (s : String) :
    (driverK (c := c) κ cnt t).noMention s := by
  rw [driverK, AggQueryIn.noMention_castKind]; trivial

theorem hygienic_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T) :
    (driverK (c := c) κ cnt t).hygienic := by
  rw [driverK, AggQueryIn.hygienic_castKind]; trivial

theorem noExplode_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T) :
    (driverK (c := c) κ cnt t).noExplode := by
  rw [driverK, AggQueryIn.noExplode_castKind]; trivial

theorem noGammaNest_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T) :
    (driverK (c := c) κ cnt t).noGammaNest := by
  rw [driverK, AggQueryIn.noGammaNest_castKind]; trivial

theorem overSchema_driverK (sch : Schema) (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T) :
    (driverK (c := c) κ cnt t).overSchema sch := by
  rw [driverK, AggQueryIn.overSchema_castKind]; trivial

omit [ValueType T] in
theorem usesOnly_withTagK {S : Set OpKind} (hS : sumMuOps ⊆ S) {κ : Fin k → ColKind} (t : T)
    (q : AggQueryIn T c k κ) (hq : q.usesOnly S) : (withTagK t q).usesOnly S := by
  rw [withTagK, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumMuOps]), fun j => Fin.cases rfl (fun i => carryColIn_sourceCol κ i) j⟩,
    hq⟩

theorem inSig_withTagK {Θ : Set (SeqAggFunc T)} {κ : Fin k → ColKind} (t : T)
    (q : AggQueryIn T c k κ) (hq : q.inSig Θ) : (withTagK t q).inSig Θ := by
  rw [withTagK, AggQueryIn.inSig_castKind]
  exact ⟨fun j => Fin.cases rfl (fun i => carryColIn_noFun κ i) j, hq⟩

omit [ValueType T] in
theorem wellKinded_withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ)
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hq : q.wellKinded ρc HK) :
    (withTagK t q).wellKinded ρc HK := by
  rw [withTagK, AggQueryIn.wellKinded_castKind]
  exact ⟨fun j => Fin.cases trivial (fun i => carryColIn_outerOk κ i _) j, hq⟩

omit [ValueType T] in
theorem names_withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ) :
    (withTagK t q).names = q.names := by
  rw [withTagK, AggQueryIn.names_castKind]; rfl

omit [ValueType T] in
theorem noMention_withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ) (s : String) :
    (withTagK t q).noMention s ↔ q.noMention s := by
  rw [withTagK, AggQueryIn.noMention_castKind]; exact Iff.rfl

omit [ValueType T] in
theorem hygienic_withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ) :
    (withTagK t q).hygienic ↔ q.hygienic := by
  rw [withTagK, AggQueryIn.hygienic_castKind]; exact Iff.rfl

omit [ValueType T] in
theorem noExplode_withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ) :
    (withTagK t q).noExplode ↔ q.noExplode := by
  rw [withTagK, AggQueryIn.noExplode_castKind]; exact Iff.rfl

omit [ValueType T] in
theorem noGammaNest_withTagK {κ : Fin k → ColKind} (t : T) (q : AggQueryIn T c k κ) :
    (withTagK t q).noGammaNest ↔ q.noGammaNest := by
  rw [withTagK, AggQueryIn.noGammaNest_castKind]; exact Iff.rfl

omit [ValueType T] in
theorem overSchema_withTagK (sch : Schema) {κ : Fin k → ColKind} (t : T)
    (q : AggQueryIn T c k κ) : (withTagK t q).overSchema sch ↔ q.overSchema sch := by
  rw [withTagK, AggQueryIn.overSchema_castKind]; exact Iff.rfl

omit [ValueType T] in
theorem usesOnly_phaseBodyK {S : Set OpKind} (hS : sumMuOps ⊆ S) {κ : Fin k → ColKind}
    (s : String) (p₁ : T) (Z : AggQueryIn T c (k + 1) (tagKind κ)) (hZ : Z.usesOnly S) :
    (phaseBodyK s p₁ Z).usesOnly S := by
  rw [phaseBodyK, AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hS (by simp [sumMuOps]), fun j => ?_⟩, hS (by simp [sumMuOps]),
    hS (by simp [sumMuOps]), trivial, (AggQueryIn.usesOnly_substMap Z _).mpr hZ⟩
  exact Fin.cases rfl (fun i => carryColIn_sourceCol _ _) j

theorem inSig_phaseBodyK {Θ : Set (SeqAggFunc T)} {κ : Fin k → ColKind} (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) (hZ : Z.inSig Θ) :
    (phaseBodyK s p₁ Z).inSig Θ := by
  rw [phaseBodyK, AggQueryIn.inSig_castKind]
  exact ⟨fun j => Fin.cases rfl (fun i => carryColIn_noFun _ _) j, rfl, trivial,
    (AggQueryIn.inSig_substMap Z _).mpr hZ⟩

omit [ValueType T] in
theorem wellKinded_phaseBodyK {κ : Fin k → ColKind} (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) {ρc : Fin c → ColKind} {HK : HoleKinds}
    (hs : ∀ i, (tagKind κ i).base = (HK s (k + 1) i).base) (hZ : Z.wellKinded ρc HK) :
    (phaseBodyK s p₁ Z).wellKinded ρc HK := by
  have hθ : ∀ j : Fin c, (ρc j).base
      = _root_.Sum.elim (fun _ => ColKind.reg) (fun i => (Fin.append (tagKind κ) ρc i).base)
          (applyOuter T c (k + 1) j) := fun j => by
    show _ = (Fin.append (tagKind κ) ρc (Fin.natAdd _ j)).base
    rw [Fin.append_right]
  rw [phaseBodyK, AggQueryIn.wellKinded_castKind]
  exact ⟨fun j => Fin.cases trivial (fun i => carryColIn_outerOk _ _ _) j, ⟨trivial, trivial⟩,
    hs, AggQueryIn.wellKinded_substMap Z _ hθ hZ⟩

omit [ValueType T] in
theorem names_phaseBodyK {κ : Fin k → ColKind} (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) :
    (phaseBodyK s p₁ Z).names = Union.union {s} Z.names := by
  rw [phaseBodyK, AggQueryIn.names_castKind]
  simp only [AggQueryIn.names, AggQueryIn.names_substMap]

omit [ValueType T] in
theorem noMention_phaseBodyK {κ : Fin k → ColKind} (s' : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) {s : String} (hZ : Z.noMention s) :
    (phaseBodyK s' p₁ Z).noMention s := by
  rw [phaseBodyK, AggQueryIn.noMention_castKind]
  exact ⟨trivial, (AggQueryIn.noMention_substMap Z _).mpr hZ⟩

omit [ValueType T] in
theorem hygienic_phaseBodyK {κ : Fin k → ColKind} (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) (hZ : Z.hygienic) :
    (phaseBodyK s p₁ Z).hygienic := by
  rw [phaseBodyK, AggQueryIn.hygienic_castKind]
  exact ⟨trivial, (AggQueryIn.hygienic_substMap Z _).mpr hZ⟩

omit [ValueType T] in
theorem noExplode_phaseBodyK {κ : Fin k → ColKind} (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) (hZ : Z.noExplode) :
    (phaseBodyK s p₁ Z).noExplode := by
  rw [phaseBodyK, AggQueryIn.noExplode_castKind]
  exact ⟨trivial, (AggQueryIn.noExplode_substMap Z _).mpr hZ⟩

omit [ValueType T] in
theorem noGammaNest_phaseBodyK {κ : Fin k → ColKind} (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (tagKind κ)) (hZ : Z.noGammaNest) :
    (phaseBodyK s p₁ Z).noGammaNest := by
  rw [phaseBodyK, AggQueryIn.noGammaNest_castKind]
  exact ⟨trivial, (AggQueryIn.noGammaNest_substMap Z _).mpr hZ⟩

omit [ValueType T] in
theorem overSchema_phaseBodyK {sch : Schema} {s : String} {κ : Fin k → ColKind}
    (hs : sch s = some (k + 1)) (p₁ : T) (Z : AggQueryIn T c (k + 1) (tagKind κ))
    (hZ : Z.overSchema sch) : (phaseBodyK s p₁ Z).overSchema sch := by
  rw [phaseBodyK, AggQueryIn.overSchema_castKind]
  exact ⟨hs, (AggQueryIn.overSchema_substMap Z _ sch).mpr hZ⟩

/-- **The construction uses the classes of `sumMuOps`** and its operands'. -/
theorem usesOnly_sumByMuK {S : Set OpKind} (hS : sumMuOps ⊆ S) {κ : Fin k → ColKind}
    (s₁ s₂ : String) (cnt : SeqAggFunc T) (q₁ q₂ : AggQueryIn T c k κ) (h₁ : q₁.usesOnly S)
    (h₂ : q₂.usesOnly S) : (sumByMuK s₁ s₂ cnt q₁ q₂).usesOnly S := by
  rw [sumByMuK, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumMuOps]), fun j => carryColIn_sourceCol _ _⟩, hS (by simp [sumMuOps]),
    hS (by simp [sumMuOps]),
    ⟨hS (by simp [sumMuOps]), usesOnly_driverK hS κ cnt 0,
      usesOnly_phaseBodyK hS _ _ _ (usesOnly_withTagK hS 0 q₁ h₁)⟩,
    usesOnly_phaseBodyK hS _ _ _ (usesOnly_withTagK hS 0 q₂ h₂)⟩

/-- **The construction applies no function**, and adds the one aggregate
its padding row needs. -/
theorem inSig_sumByMuK {Θ : Set (SeqAggFunc T)} {κ : Fin k → ColKind} (s₁ s₂ : String)
    {cnt : SeqAggFunc T} (hcnt : cnt ∈ Θ) (q₁ q₂ : AggQueryIn T c k κ) (h₁ : q₁.inSig Θ)
    (h₂ : q₂.inSig Θ) : (sumByMuK s₁ s₂ cnt q₁ q₂).inSig Θ := by
  rw [sumByMuK, AggQueryIn.inSig_castKind]
  exact ⟨fun _ => carryColIn_noFun _ _, rfl,
    ⟨inSig_driverK κ hcnt 0, inSig_phaseBodyK _ _ _ (inSig_withTagK 0 q₁ h₁)⟩,
    inSig_phaseBodyK _ _ _ (inSig_withTagK 0 q₂ h₂)⟩

theorem noExplode_sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) (h₁ : q₁.noExplode) (h₂ : q₂.noExplode) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).noExplode := by
  rw [sumByMuK, AggQueryIn.noExplode_castKind]
  exact ⟨⟨noExplode_driverK κ cnt 0,
      noExplode_phaseBodyK _ _ _ ((noExplode_withTagK 0 q₁).mpr h₁)⟩,
    noExplode_phaseBodyK _ _ _ ((noExplode_withTagK 0 q₂).mpr h₂)⟩

theorem noGammaNest_sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) (h₁ : q₁.noGammaNest) (h₂ : q₂.noGammaNest) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).noGammaNest := by
  rw [sumByMuK, AggQueryIn.noGammaNest_castKind]
  exact ⟨⟨noGammaNest_driverK κ cnt 0,
      noGammaNest_phaseBodyK _ _ _ ((noGammaNest_withTagK 0 q₁).mpr h₁)⟩,
    noGammaNest_phaseBodyK _ _ _ ((noGammaNest_withTagK 0 q₂).mpr h₂)⟩

/-- **The construction is well-kinded where its operands are**: each
recursion binds its name to rounds of the tagged kinds, and the operands,
being closed, read no round. -/
theorem wellKinded_sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) {ρc : Fin c → ColKind} {HK : HoleKinds}
    (h₁ : q₁.wellKinded ρc HK) (h₂ : q₂.wellKinded ρc HK) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).wellKinded ρc HK := by
  have hcl : ∀ (q : AggQueryIn T c k κ) (HK' : HoleKinds), q.wellKinded ρc HK →
      q.wellKinded ρc HK' := fun q HK' h =>
    AggQueryIn.wellKinded_congr_holes q ρc (fun _ hp => absurd hp List.not_mem_nil) h
  rw [sumByMuK, AggQueryIn.wellKinded_castKind]
  refine ⟨fun _ => carryColIn_outerOk _ _ _, ⟨trivial, trivial⟩,
    ⟨wellKinded_driverK κ cnt 0 ρc HK, wellKinded_phaseBodyK _ _ _ (fun i => by
      rw [HoleKinds.assign_self]) (wellKinded_withTagK 0 q₁ (hcl q₁ _ h₁))⟩,
    wellKinded_phaseBodyK _ _ _ (fun i => by rw [HoleKinds.assign_self])
      (wellKinded_withTagK 0 q₂ (hcl q₂ _ h₂))⟩

/-- **The construction's recursions are hygienic**, given fresh names. -/
theorem hygienic_sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) (h₁ : q₁.noMention s₁) (h₂₁ : q₁.noMention s₂)
    (h₂₂ : q₂.noMention s₂) (hr₁ : q₁.hygienic) (hr₂ : q₂.hygienic) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).hygienic := by
  rw [sumByMuK, AggQueryIn.hygienic_castKind]
  exact ⟨⟨noMention_driverK κ cnt 0 s₂,
      noMention_phaseBodyK s₁ _ _ ((noMention_withTagK 0 q₁ s₂).mpr h₂₁)⟩,
    noMention_phaseBodyK s₂ _ _ ((noMention_withTagK 0 q₂ s₂).mpr h₂₂),
    ⟨noMention_driverK κ cnt 0 s₁,
      noMention_phaseBodyK s₁ _ _ ((noMention_withTagK 0 q₁ s₁).mpr h₁),
      hygienic_driverK κ cnt 0, hygienic_phaseBodyK _ _ _ ((hygienic_withTagK 0 q₁).mpr hr₁)⟩,
    hygienic_phaseBodyK _ _ _ ((hygienic_withTagK 0 q₂).mpr hr₂)⟩

/-- **The construction is well-formed over a schema declaring neither
bound name**, its operands being so and naming neither. -/
theorem overSchema_sumByMuK (sch : Schema) {κ : Fin k → ColKind} (s₁ s₂ : String)
    (cnt : SeqAggFunc T) (q₁ q₂ : AggQueryIn T c k κ)
    (hs₁ : sch s₁ = none) (hs₂ : sch s₂ = none) (hn₁ : s₁ ∉ q₁.names) (hn₂ : s₂ ∉ q₂.names)
    (h₁ : q₁.overSchema sch) (h₂ : q₂.overSchema sch) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).overSchema sch := by
  rw [sumByMuK, AggQueryIn.overSchema_castKind]
  exact ⟨hs₂, ⟨hs₁, overSchema_driverK sch κ cnt 0,
      noMention_phaseBodyK s₁ _ _ ((noMention_withTagK 0 q₁ s₁).mpr
        (AggQueryIn.noMention_of_not_mem_names q₁ hn₁)),
      overSchema_phaseBodyK (Schema.update_self sch s₁ (k + 1)) _ _
        ((overSchema_withTagK _ 0 q₁).mpr
          (AggQueryIn.overSchema_update_of_not_mem_names q₁ h₁ hn₁))⟩,
    noMention_phaseBodyK s₂ _ _ ((noMention_withTagK 0 q₂ s₂).mpr
      (AggQueryIn.noMention_of_not_mem_names q₂ hn₂)),
    overSchema_phaseBodyK (Schema.update_self sch s₂ (k + 1)) _ _
      ((overSchema_withTagK _ 0 q₂).mpr
        (AggQueryIn.overSchema_update_of_not_mem_names q₂ h₂ hn₂))⟩

/-- **The construction names its two bound names and its operands'.** -/
theorem names_sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).names ⊆ insert s₁ (insert s₂ (Union.union q₁.names q₂.names)) := by
  intro x hx
  rw [sumByMuK, AggQueryIn.names_castKind] at hx
  simp only [AggQueryIn.names, names_phaseBodyK, names_withTagK, names_driverK,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    false_or] at hx
  simp only [Finset.mem_insert, Finset.mem_union]
  tauto

theorem noMention_sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) {s : String} (h₁ : q₁.noMention s) (h₂ : q₂.noMention s) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).noMention s := by
  rw [sumByMuK, AggQueryIn.noMention_castKind]
  exact ⟨⟨noMention_driverK κ cnt 0 s, noMention_phaseBodyK s₁ _ _
      ((noMention_withTagK 0 q₁ s).mpr h₁)⟩,
    noMention_phaseBodyK s₂ _ _ ((noMention_withTagK 0 q₂ s).mpr h₂)⟩

theorem usesOnly_emptyK {S : Set OpKind} (hS : sumMuOps ⊆ S) (κ : Fin k → ColKind)
    (cnt : SeqAggFunc T) : (emptyK (c := c) κ cnt).usesOnly S := by
  rw [emptyK, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumMuOps]), fun j => carryColIn_sourceCol _ _⟩, hS (by simp [sumMuOps]),
    usesOnly_driverK hS κ cnt 0⟩

theorem inSig_emptyK {Θ : Set (SeqAggFunc T)} (κ : Fin k → ColKind) {cnt : SeqAggFunc T}
    (hcnt : cnt ∈ Θ) : (emptyK (c := c) κ cnt).inSig Θ := by
  rw [emptyK, AggQueryIn.inSig_castKind]
  exact ⟨fun _ => carryColIn_noFun _ _, rfl, inSig_driverK κ hcnt 0⟩

theorem noExplode_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) :
    (emptyK (c := c) κ cnt).noExplode := by
  rw [emptyK, AggQueryIn.noExplode_castKind]; exact noExplode_driverK κ cnt 0

theorem noGammaNest_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) :
    (emptyK (c := c) κ cnt).noGammaNest := by
  rw [emptyK, AggQueryIn.noGammaNest_castKind]; exact noGammaNest_driverK κ cnt 0

theorem wellKinded_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (ρc : Fin c → ColKind)
    (HK : HoleKinds) : (emptyK κ cnt).wellKinded ρc HK := by
  rw [emptyK, AggQueryIn.wellKinded_castKind]
  exact ⟨fun _ => carryColIn_outerOk _ _ _, ⟨trivial, trivial⟩, wellKinded_driverK κ cnt 0 ρc HK⟩

theorem hygienic_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) :
    (emptyK (c := c) κ cnt).hygienic := by
  rw [emptyK, AggQueryIn.hygienic_castKind]; exact hygienic_driverK κ cnt 0

theorem overSchema_emptyK (sch : Schema) (κ : Fin k → ColKind) (cnt : SeqAggFunc T) :
    (emptyK (c := c) κ cnt).overSchema sch := by
  rw [emptyK, AggQueryIn.overSchema_castKind]; exact overSchema_driverK sch κ cnt 0

theorem names_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) :
    (emptyK (c := c) κ cnt).names = ∅ := by
  rw [emptyK, AggQueryIn.names_castKind]; exact names_driverK κ cnt 0

theorem noMention_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (s : String) :
    (emptyK (c := c) κ cnt).noMention s := by
  rw [emptyK, AggQueryIn.noMention_castKind]; exact noMention_driverK κ cnt 0 s

theorem annSettlesAt_emptyK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) : (emptyK κ cnt).AnnSettlesAt d γ E := by
  rw [emptyK, AggQueryIn.annSettlesAt_castKind]
  show (driverK κ cnt 0).AnnSettlesAt d γ E
  rw [driverK, AggQueryIn.annSettlesAt_castKind]
  trivial

theorem annSettlesAt_driverK (κ : Fin k → ColKind) (cnt : SeqAggFunc T) (t : T)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (driverK κ cnt t).AnnSettlesAt d γ E := by
  rw [driverK, AggQueryIn.annSettlesAt_castKind]
  trivial

/-- A round of the construction settles wherever its operand does under
the same context. -/
theorem annSettlesAt_phaseBodyK_withTagK {κ : Fin k → ColKind} (s : String) (p₁ t : T)
    (q : AggQueryIn T c k κ) (d : AnnotatedDatabase T K) (γ : Fin c → T) {E : EvalEnv T K}
    (hq : q.AnnSettlesAt d γ E) (F : EvalEnv T K) (hF : F.ctxAt c γ = E.ctxAt c γ) :
    (phaseBodyK s p₁ (withTagK t q)).AnnSettlesAt d γ F := by
  rw [phaseBodyK, AggQueryIn.annSettlesAt_castKind]
  refine ⟨trivial, fun x _ => ?_⟩
  rw [AggQueryIn.annSettlesAt_substMap _ _ (isRenaming_applyOuter _ _), substVal_applyOuter,
      withTagK,
    AggQueryIn.annSettlesAt_castKind]
  exact AggQueryIn.annSettlesAt_closed q d γ
    ((ctxAt_substEnv_applyOuter F γ x.fst _).trans hF).symm hq

/-- **The construction settles where its operands do**: each recursion
stops after its second round. -/
theorem annSettlesAt_sumByMuK {κ : Fin k → ColKind} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k κ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (hq₁ : q₁.AnnSettlesAt d γ E) (hq₂ : q₂.AnnSettlesAt d γ E) :
    (sumByMuK s₁ s₂ cnt q₁ q₂).AnnSettlesAt d γ E := by
  have hnz : (ValueType.nonzero : T) ≠ 0 := ValueType.nonzero_ne_zero
  obtain ⟨r₀, hM, hr₀t, hr₀f⟩ := evaluate_driverK (c := c) κ cnt (0 : T) d γ E
  have hr₀m : r₀ ∈ (driverK (c := c) κ cnt (0 : T)).evaluate d γ E := by
    rw [hM]; exact Multiset.mem_singleton_self r₀
  have hr₀c : GenRow.Conforms (tagKind κ) r₀.fst := fun j =>
    AggQueryIn.evaluate_conform (driverK κ cnt 0) d r₀ hr₀m j
  have hM₁ : ∀ x ∈ ({r₀} : Multiset (GenRow T K (k + 1))), GenRow.Conforms (tagKind κ) x.fst :=
    fun x hx => by rw [Multiset.mem_singleton.mp hx]; exact hr₀c
  -- a round of either recursion
  have hc : ∀ (s : String) (q : AggQueryIn T c k κ) (X : Multiset (GenRow T K (k + 1))),
      ∀ x ∈ (phaseBodyK s ValueType.nonzero (withTagK 0 q)).evaluate d γ (E.assignHole s X),
        GenRow.Conforms (tagKind κ) x.fst :=
    fun s q X x hx j => AggQueryIn.evaluate_conform _ d x hx j
  have h0 : ∀ (s : String) (q : AggQueryIn T c k κ),
      (phaseBodyK s ValueType.nonzero (withTagK 0 q)).evaluate d γ
        (E.assignHole s (0 : Multiset (GenRow T K (k + 1)))) = 0 :=
    fun s q => evaluate_phaseBodyK_of_tags s _ 0 q d γ E 0
      (fun x hx => absurd hx (Multiset.notMem_zero x))
      (fun x hx => absurd hx (Multiset.notMem_zero x))
  -- the first recursion: the driver, then `q₁`'s rows tagged `nonzero`
  have h2₁ : (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁
      ((phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁ {r₀})))
      = 0 :=
    evaluate_phaseBodyK_of_tags s₁ _ 0 q₁ d γ E _ (hc s₁ q₁ _) (fun x hx => by
      rw [tag_of_mem_phaseBodyK s₁ _ 0 q₁ d γ E _ hM₁ hx]; exact hnz)
  have hin : muSumFix (fun X => (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ
      (E.assignHole s₁ X)) {r₀}
      = {r₀} + (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ
        (E.assignHole s₁ {r₀}) := muSumFix_two (h0 s₁ q₁) h2₁
  -- the second recursion, over the first's value
  obtain ⟨B, hB⟩ : ∃ B : Multiset (GenRow T K (k + 1)), B = {r₀}
      + (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁ {r₀}) :=
    ⟨_, rfl⟩
  have hBc : ∀ x ∈ B, GenRow.Conforms (tagKind κ) x.fst := fun x hx => by
    rw [hB] at hx
    exact (Multiset.mem_add.mp hx).elim (hM₁ x) (hc s₁ q₁ _ x)
  have h2₂ : (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ (E.assignHole s₂
      ((phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ (E.assignHole s₂ B)))
      = 0 :=
    evaluate_phaseBodyK_of_tags s₂ _ 0 q₂ d γ E _ (hc s₂ q₂ _) (fun x hx => by
      rw [tag_of_mem_phaseBodyK s₂ _ 0 q₂ d γ E B hBc hx]; exact hnz)
  have hout : muSumFix (fun X => (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ
      (E.assignHole s₂ X)) B
      = B + (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ
        (E.assignHole s₂ B) := muSumFix_two (h0 s₂ q₂) h2₂
  rw [sumByMuK, AggQueryIn.annSettlesAt_castKind]
  have hph : ∀ (s : String) (q : AggQueryIn T c k κ), q.AnnSettlesAt d γ E →
      ∀ {m : ℕ} (X : Multiset (GenRow T K m)),
        (phaseBodyK s ValueType.nonzero (withTagK 0 q)).AnnSettlesAt d γ (E.assignHole s X) :=
    fun s q hq _ X => annSettlesAt_phaseBodyK_withTagK s _ 0 q d γ hq _ rfl
  refine ⟨⟨annSettlesAt_driverK κ cnt 0 d γ E, h0 s₁ q₁, ⟨1, ?_⟩, fun _ => hph s₁ q₁ hq₁ _,
      hph s₁ q₁ hq₁ _⟩, h0 s₂ q₂, ⟨1, ?_⟩, fun _ => hph s₂ q₂ hq₂ _, hph s₂ q₂ hq₂ _⟩
  · show (phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁
      ((phaseBodyK s₁ ValueType.nonzero (withTagK 0 q₁)).evaluate d γ
        (E.assignHole s₁ ((driverK κ cnt 0).evaluate d γ E)))) = 0
    rw [hM]
    exact h2₁
  · show (phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ (E.assignHole s₂
      ((phaseBodyK s₂ ValueType.nonzero (withTagK 0 q₂)).evaluate d γ
        (E.assignHole s₂ (muSumFix (fun X => (phaseBodyK s₁ ValueType.nonzero
          (withTagK 0 q₁)).evaluate d γ (E.assignHole s₁ X))
          ((driverK κ cnt 0).evaluate d γ E))))) = 0
    rw [hM, hin, ← hB]
    exact h2₂

end AggQueryIn

/-! ## The two recursions, given a split body -/

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- What the annotated reading reads of a bag of rows is determined by
their finalizations. -/
theorem GenRow.map_toAnnotated_of_fin {n : ℕ} {A B : Multiset (GenRow T K n)}
    (h : A.map GenRow.fin = B.map GenRow.fin) :
    A.map GenRow.toAnnotated = B.map GenRow.toAnnotated :=
  Multiset.map_eq_of_factor (f := GenRow.fin) (fun a b hab => by
    obtain ⟨h₁, h₂⟩ := GenRow.fin_eq_iff.mp hab
    unfold GenRow.toAnnotated
    rw [h₁, h₂]) h

/-- **A bag recursion whose body splits** into a body and a closed part:
where the recursion settles, its body is empty on the empty round, so the
closed part is empty and the body alone gives the same rounds. -/
theorem AggQueryIn.mu_of_splitAnn {c n : ℕ} {κ : Fin n → ColKind} (s : String)
    (q₀ q₀' : AggQueryIn T c n κ) (q₁ q₁' : AggQueryIn T c n κ [(s, n)])
    (qC : AggQueryIn T c n κ) (d : AnnotatedDatabase T K) (γ : Fin c → T) {E E' : EvalEnv T K}
    (hE : E.FinRel γ E') (hset : (AggQueryIn.Mu s q₀ q₁).AnnSettlesAt d γ E)
    (h₀ : q₀'.AnnSettlesAt d γ E'
      ∧ (q₀.evaluate d γ E).map GenRow.fin = (q₀'.evaluate d γ E').map GenRow.fin)
    (h₁ : ∀ F F' : EvalEnv T K, F.FinRel γ F' → q₁.AnnSettlesAt d γ F →
      q₁'.AnnSettlesAt d γ F' ∧ qC.AnnSettlesAt d γ F'
        ∧ (q₁.evaluate d γ F).map GenRow.fin
          = (q₁'.evaluate d γ F').map GenRow.fin + (qC.evaluate d γ F').map GenRow.fin) :
    (AggQueryIn.Mu s q₀' q₁').AnnSettlesAt d γ E'
      ∧ ((AggQueryIn.Mu s q₀ q₁).evaluate d γ E).map GenRow.fin
        = ((AggQueryIn.Mu s q₀' q₁').evaluate d γ E').map GenRow.fin := by
  obtain ⟨hs₀, hz, hs, hk, hk0⟩ := hset
  have hz' : q₁.evaluate d γ (E.assignHole s (0 : Multiset (GenRow T K n))) = 0 := hz
  -- the closed part is empty
  obtain ⟨-, -, e0⟩ := h₁ _ _ (hE.assignHole s (rfl : (0 : Multiset (GenRow T K n)).map
    GenRow.fin = _)) hk0
  rw [hz', Multiset.map_zero] at e0
  have hC0 : ∀ X : Multiset (GenRow T K n), qC.evaluate d γ (E'.assignHole s X) = 0 := fun X => by
    rw [AggQueryIn.evaluate_assignHole_closed]
    have := (Multiset.map_eq_zero (f := GenRow.fin)).mp (Multiset.eq_zero_of_add_eq_zero_right
      e0.symm)
    rwa [AggQueryIn.evaluate_assignHole_closed] at this
  have h1z : q₁'.evaluate d γ (E'.assignHole s (0 : Multiset (GenRow T K n))) = 0 :=
    (Multiset.map_eq_zero (f := GenRow.fin)).mp
      (Multiset.eq_zero_of_add_eq_zero_left e0.symm)
  -- the body alone, round by round
  have hstep : ∀ (X : Multiset (GenRow T K n)) (X' : Multiset (GenRow T K n)),
      X'.map GenRow.fin = X.map GenRow.fin → q₁.AnnSettlesAt d γ (E.assignHole s X) →
        q₁'.AnnSettlesAt d γ (E'.assignHole s X')
          ∧ (q₁'.evaluate d γ (E'.assignHole s X')).map GenRow.fin
            = (q₁.evaluate d γ (E.assignHole s X)).map GenRow.fin := fun X X' hX hX₁ => by
    obtain ⟨hs', -, he⟩ := h₁ _ _ (hE.assignHole s hX.symm) hX₁
    refine ⟨hs', ?_⟩
    rw [he, hC0, Multiset.map_zero, add_zero]
  have hR : ∀ k, ((AggQueryIn.muStep s q₁' d γ E')^[k] (q₀'.evaluate d γ E')).map GenRow.fin
      = ((AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E)).map GenRow.fin := by
    intro k
    induction k with
    | zero => exact h₀.2.symm
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hstep _ _ ih (hk k)).2
  refine ⟨⟨h₀.1, h1z, ?_, fun k => (hstep _ _ (hR k) (hk k)).1, (hstep 0 0 rfl hk0).1⟩, ?_⟩
  · obtain ⟨k, hk'⟩ := hs
    refine ⟨k, (Multiset.map_eq_zero (f := GenRow.fin)).mp ?_⟩
    rw [hR, hk', Multiset.map_zero]
  · simp only [AggQueryIn.evaluate]
    exact (map_eq_of_rel' (muSumFix_rel (R := fun a b : GenRow T K n => GenRow.fin a = GenRow.fin b)
      (rel_of_map_eq h₀.2.symm)
      (fun k X hX => rel_of_map_eq (hstep _ X (map_eq_of_rel' hX) (hk k)).2))).symm

/-- **A set recursion whose body splits** into a body and a closed part:
the closed part moves into the base, where the union by recursion adds it
to the base's rows. -/
theorem AggQueryIn.muSet_of_splitAnn {c n : ℕ} (s : String)
    (q₀ q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁ q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (qC B : AggQueryIn T c n (ColKind.allReg n)) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    {E E' : EvalEnv T K} (hE : E.FinRel γ E') (hset : (AggQueryIn.MuSet s q₀ q₁).AnnSettlesAt d γ E)
    (h₀ : q₀'.AnnSettlesAt d γ E'
      ∧ (q₀.evaluate d γ E).map GenRow.fin = (q₀'.evaluate d γ E').map GenRow.fin)
    (h₁ : ∀ F F' : EvalEnv T K, F.FinRel γ F' → q₁.AnnSettlesAt d γ F →
      q₁'.AnnSettlesAt d γ F' ∧ qC.AnnSettlesAt d γ F'
        ∧ (q₁.evaluate d γ F).map GenRow.fin
          = (q₁'.evaluate d γ F').map GenRow.fin + (qC.evaluate d γ F').map GenRow.fin)
    (hB : qC.AnnSettlesAt d γ E' → B.AnnSettlesAt d γ E'
      ∧ (B.evaluate d γ E').map GenRow.fin
        = (q₀'.evaluate d γ E').map GenRow.fin + (qC.evaluate d γ E').map GenRow.fin) :
    (AggQueryIn.MuSet s B q₁').AnnSettlesAt d γ E'
      ∧ ((AggQueryIn.MuSet s q₀ q₁).evaluate d γ E).map GenRow.fin
        = ((AggQueryIn.MuSet s B q₁').evaluate d γ E').map GenRow.fin := by
  obtain ⟨hs₀, hs, hk⟩ := hset
  have hCs : qC.AnnSettlesAt d γ E' := by
    obtain ⟨-, hC, -⟩ := h₁ _ _ (hE.assignHole s rfl) (hk 0)
    exact AggQueryIn.annSettlesAt_closed qC d γ (E := E'.assignHole s _) (E' := E')
      (EvalEnv.ctxAt_assignHole _ _ _ γ) hC
  obtain ⟨hBs, hBe⟩ := hB hCs
  have hstX : ∀ X : AnnotatedRelation T K n,
      q₁.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated)) →
        AggQueryIn.muSetStep s B q₁' d γ E' X = AggQueryIn.muSetStep s q₀ q₁ d γ E X := by
    intro X hX
    obtain ⟨-, -, he⟩ := h₁ _ _ (hE.assignHole s rfl) hX
    have hm : ((B.evaluate d γ E') + q₁'.evaluate d γ
        (E'.assignHole s (X.map GenRow.ofAnnotated))).map GenRow.toAnnotated
        = ((q₀.evaluate d γ E) + q₁.evaluate d γ
          (E.assignHole s (X.map GenRow.ofAnnotated))).map GenRow.toAnnotated := by
      refine GenRow.map_toAnnotated_of_fin ?_
      rw [Multiset.map_add, Multiset.map_add, hBe, he, h₀.2,
        AggQueryIn.evaluate_assignHole_closed]
      rw [add_assoc, add_comm (Multiset.map GenRow.fin (qC.evaluate d γ E'))]
    unfold AggQueryIn.muSetStep AggQueryIn.evaluateAnnotated
    exact congrArg AnnotatedRelation.dedupAnn
      ((Multiset.map_add _ _ _).symm.trans (hm.trans (Multiset.map_add _ _ _)))
  have hst : ∀ k, AggQueryIn.muSetStep s B q₁' d γ E'
      (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)
      = AggQueryIn.muSetStep s q₀ q₁ d γ E (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k) :=
    fun k => hstX _ (hk k)
  have hiter : ∀ k, muIter (AggQueryIn.muSetStep s B q₁' d γ E') k
      = muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [muIter, ih, hst, muIter]
  have hfix : muFix (AggQueryIn.muSetStep s q₀ q₁ d γ E)
      = muFix (AggQueryIn.muSetStep s B q₁' d γ E') :=
    muFix_map_rounds (h := id) rfl (fun k => (hst k).symm) hs
  refine ⟨⟨hBs, ?_, fun k => ?_⟩, ?_⟩
  · obtain ⟨j, hj⟩ := hs
    refine ⟨j, ?_⟩
    rw [← muIter_eq_iterate, ← muIter_eq_iterate] at hj ⊢
    rw [hiter, hiter]
    exact hj
  · rw [hiter]
    exact (h₁ _ _ (hE.assignHole s rfl) (hk k)).1
  · show ((muFix (AggQueryIn.muSetStep s q₀ q₁ d γ E)).map GenRow.ofAnnotated).map GenRow.fin
      = ((muFix (AggQueryIn.muSetStep s B q₁' d γ E')).map GenRow.ofAnnotated).map GenRow.fin
    rw [hfix]

/-! ## The operators a recursive body may sit under distribute over `⊎` -/

namespace AggQueryIn

variable {c : ℕ}

theorem evaluate_proj_sum {n m : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (ps : Tuple (ProjColIn T c κ) m) (a : AggQueryIn T c n κ l) (b : AggQueryIn T c n κ l')
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.Proj ps (AggQueryIn.Sum a b)).evaluate d γ E
      = (AggQueryIn.Proj ps a).evaluate d γ E + (AggQueryIn.Proj ps b).evaluate d γ E := by
  simp only [AggQueryIn.evaluate, Multiset.map_add]

theorem evaluate_sel_sum {n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (φ : GenPredIn T c κ) (a : AggQueryIn T c n κ l) (b : AggQueryIn T c n κ l')
    (hab : SelOK (l ++ l') φ) (ha : SelOK l φ) (hb : SelOK l' φ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.Sel φ (AggQueryIn.Sum a b) hab).evaluate d γ E
      = (AggQueryIn.Sel φ a ha).evaluate d γ E + (AggQueryIn.Sel φ b hb).evaluate d γ E := by
  simp only [AggQueryIn.evaluate]
  split_ifs <;> simp only [Multiset.map_add, Multiset.filter_add]

theorem evaluate_prod_sum_left {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l l' l₂ : List (String × ℕ)} (a : AggQueryIn T c n₁ κ₁ l) (b : AggQueryIn T c n₁ κ₁ l')
    (q₂ : AggQueryIn T c n₂ κ₂ l₂) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    (AggQueryIn.Prod (AggQueryIn.Sum a b) q₂).evaluate d γ E
      = (AggQueryIn.Prod a q₂).evaluate d γ E + (AggQueryIn.Prod b q₂).evaluate d γ E := by
  simp only [AggQueryIn.evaluate]
  rw [← Multiset.map_add]
  exact congrArg _ (Multiset.add_product _ _ _)

theorem evaluate_prod_sum_right {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l l' : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (a : AggQueryIn T c n₂ κ₂ l)
    (b : AggQueryIn T c n₂ κ₂ l') (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    (AggQueryIn.Prod q₁ (AggQueryIn.Sum a b)).evaluate d γ E
      = (AggQueryIn.Prod q₁ a).evaluate d γ E + (AggQueryIn.Prod q₁ b).evaluate d γ E := by
  simp only [AggQueryIn.evaluate]
  rw [← Multiset.map_add]
  exact congrArg _ (Multiset.product_add _ _ _)

theorem evaluate_apply_sum {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l l' : List (String × ℕ)} (a : AggQueryIn T c n₁ κ₁ l) (b : AggQueryIn T c n₁ κ₁ l')
    (q₂ : AggQueryIn T (n₁ + c) n₂ κ₂) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    (AggQueryIn.Apply (AggQueryIn.Sum a b) q₂).evaluate d γ E
      = (AggQueryIn.Apply a q₂).evaluate d γ E + (AggQueryIn.Apply b q₂).evaluate d γ E := by
  simp only [AggQueryIn.evaluate, Multiset.add_bind]

theorem evaluate_explode_sum {n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (k : Fin n) (hk : κ k = ColKind.agg) (a : AggQueryIn T c n κ l) (b : AggQueryIn T c n κ l')
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.Explode k hk (AggQueryIn.Sum a b)).evaluate d γ E
      = (AggQueryIn.Explode k hk a).evaluate d γ E
        + (AggQueryIn.Explode k hk b).evaluate d γ E := by
  simp only [AggQueryIn.evaluate, Multiset.add_bind]

/-- A split, read as the evaluation of a union. -/
theorem fin_sum_of_split {n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    {a : AggQueryIn T c n κ l} {b : AggQueryIn T c n κ l'} {d : AnnotatedDatabase T K}
    {γ : Fin c → T} {E : EvalEnv T K} {X : Multiset (GenRow T K n)}
    (h : X.map GenRow.fin = (a.evaluate d γ E).map GenRow.fin + (b.evaluate d γ E).map GenRow.fin) :
    X.map GenRow.fin = ((AggQueryIn.Sum a b).evaluate d γ E).map GenRow.fin := by
  rw [h]
  exact (Multiset.map_add _ _ _).symm

end AggQueryIn

/-! ## The pass: every `⊎` replaced by the construction

As in the plain semantics (`AggQueryIn.exists_sumFree_aux`), a `⊎` on the
recursive path of a body cannot be replaced where it stands; the body is
instead the sum of a body with the non-recursive side of every such `⊎`
dropped and a closed query, up to finalization. At a bag recursion that
settles the closed query is empty; at a set recursion it moves into the
base. -/

/-- **What the pass keeps of a query, besides its value**: the classes
of `S`, the restriction on recursive terms, the signature, the absence of
an explosion, the kinds, well-formedness over a schema declaring none of
the fresh names, the names (its own, or fresh ones), and the names it does
not mention (fresh ones aside). -/
structure AggQueryIn.SumFreeAnnOf (S : Set OpKind) (Θ : Set (SeqAggFunc T)) (f : ℕ → String)
    {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (q' : AggQueryIn T c n κ l') : Prop where
  usesOnly : q'.usesOnly S
  hygienic : q'.hygienic
  inSig : q'.inSig Θ
  noExplode : q.noExplode → q'.noExplode
  wellKinded : ∀ (ρc : Fin c → ColKind) (HK : HoleKinds), q.wellKinded ρc HK →
    q'.wellKinded ρc HK
  over : ∀ sch : Schema, (∀ i, sch (f i) = none) → q.overSchema sch → q'.overSchema sch
  names : ∀ x, x ∈ q'.names → x ∈ q.names ∨ ∃ i, x = f i
  nom : ∀ s, (∀ i, s ≠ f i) → q.noMention s → q'.noMention s
  noNest : q.noGammaNest → q'.noGammaNest

/-- **A closed query matched**: wherever it settles, in two environments
agreeing up to finalization, the match settles and gives the same rows up
to finalization. -/
def AggQueryIn.ClosedMatch {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (q' : AggQueryIn T c n κ l') : Prop :=
  ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E E' : EvalEnv T K), E.FinRel γ E' →
    q.AnnSettlesAt d γ E →
      q'.AnnSettlesAt d γ E'
        ∧ (q.evaluate d γ E).map GenRow.fin = (q'.evaluate d γ E').map GenRow.fin

/-- **A body split**: wherever it settles, the body is the sum of the
first query and the closed second one, up to finalization. -/
def AggQueryIn.BodySplit {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (q' : AggQueryIn T c n κ l') (qC : AggQueryIn T c n κ) : Prop :=
  ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E E' : EvalEnv T K), E.FinRel γ E' →
    q.AnnSettlesAt d γ E →
      q'.AnnSettlesAt d γ E' ∧ qC.AnnSettlesAt d γ E'
        ∧ (q.evaluate d γ E).map GenRow.fin
          = (q'.evaluate d γ E').map GenRow.fin + (qC.evaluate d γ E').map GenRow.fin

theorem AggQueryIn.closedMatch_refl {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) : AggQueryIn.ClosedMatch (K := K) q q :=
  fun d γ _ _ hE h =>
    ⟨AggQueryIn.annSettlesAt_finRel q d γ hE h, AggQueryIn.FinEq.refl q d γ _ _ hE⟩

/-- The right side of an apply settles at every row of the match's left
side, those rows being the source's up to finalization. -/
theorem AggQueryIn.apply_right_settles {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {l₁ : List (String × ℕ)} {q₁ : AggQueryIn T c n₁ κ₁ l₁}
    {q₂ q₂' : AggQueryIn T (n₁ + c) n₂ κ₂} (h₂ : AggQueryIn.ClosedMatch (K := K) q₂ q₂')
    {d : AnnotatedDatabase T K} {γ : Fin c → T} {E E' : EvalEnv T K} (hE : E.FinRel γ E')
    (hset : ∀ x ∈ q₁.evaluate d γ E, q₂.AnnSettlesAt d (Fin.append (GenRow.plainTuple x.fst) γ)
      (E.withCtx (Fin.append x.fst (E.ctxAt _ γ))))
    {x' : GenRow T K n₁} (hx' : GenRow.fin x' ∈ (q₁.evaluate d γ E).map GenRow.fin) :
    q₂'.AnnSettlesAt d (Fin.append (GenRow.plainTuple x'.fst) γ)
      (E'.withCtx (Fin.append x'.fst (E'.ctxAt _ γ))) := by
  obtain ⟨x, hx, hxx⟩ := Multiset.mem_map.mp hx'
  have h1 := (GenRow.fin_eq_iff.mp hxx).1
  have := (h₂ d _ _ _ (hE.enter h1 (Fin.append (GenRow.plainTuple x.fst) γ)) (hset x hx)).1
  rwa [h1] at this

namespace AggQueryIn

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem memS {S : Set OpKind} {o : OpKind} (ho : o ≠ OpKind.union)
    (h : o ∈ insert OpKind.union S) : o ∈ S :=
  (Set.mem_insert_iff.mp h).resolve_left ho

/-- The supply past its first two names. -/
private def shift2 (f : ℕ → String) : ℕ → String := fun i => f (i + 2)

private theorem shift2_injective {f : ℕ → String} (hf : Function.Injective f) :
    Function.Injective (shift2 f) :=
  fun _ _ h => Nat.add_right_cancel (hf h)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem not_mem_of_shift {f : ℕ → String} (hf : Function.Injective f)
    {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (hn : ∀ x, x ∈ q'.names → x ∈ q.names ∨ ∃ i, x = shift2 f i) {j : ℕ} (hj : j < 2)
    (hfr : f j ∉ q.names) : f j ∉ q'.names := fun h => by
  rcases hn _ h with h' | ⟨i, hi⟩
  · exact hfr h'
  · have := hf hi
    omega

private theorem names_shift {f : ℕ → String} {x : String} {A B : Finset String}
    (h : x ∈ A ∨ ∃ i, x = shift2 f i) (hAB : A ⊆ B) : x ∈ B ∨ ∃ i, x = f i :=
  h.imp (fun h => hAB h) (fun ⟨i, hi⟩ => ⟨i + 2, hi⟩)

private theorem names_union {f : ℕ → String} {A₁ A₂ B₁ B₂ : Finset String}
    (h₁ : ∀ x, x ∈ A₁ → x ∈ B₁ ∨ ∃ i, x = f i) (h₂ : ∀ x, x ∈ A₂ → x ∈ B₂ ∨ ∃ i, x = f i) :
    ∀ x, x ∈ Union.union A₁ A₂ → x ∈ Union.union B₁ B₂ ∨ ∃ i, x = f i :=
  fun x hx => (Finset.mem_union.mp hx).elim
    (fun h => (h₁ x h).imp_left (Finset.mem_union_left _))
    (fun h => (h₂ x h).imp_left (Finset.mem_union_right _))

private theorem fresh_shift {f : ℕ → String} {A B : Finset String} (hfr : ∀ i, f i ∉ B)
    (hAB : A ⊆ B) : ∀ i, shift2 f i ∉ A :=
  fun i h => hfr (i + 2) (hAB h)

private theorem fresh_sub {f : ℕ → String} {A B : Finset String} (hfr : ∀ i, f i ∉ B)
    (hAB : A ⊆ B) : ∀ i, f i ∉ A :=
  fun i h => hfr i (hAB h)

private theorem ne_shift_of_mem {f : ℕ → String} {s : String} {B : Finset String}
    (hfr : ∀ i, f i ∉ B) (hs : s ∈ B) : ∀ i, s ≠ shift2 f i :=
  fun i h => hfr (i + 2) (show shift2 f i ∈ B from h ▸ hs)

private theorem ne_of_mem {f : ℕ → String} {s : String} {B : Finset String}
    (hfr : ∀ i, f i ∉ B) (hs : s ∈ B) : ∀ i, s ≠ f i :=
  fun i h => hfr i (h ▸ hs)

end AggQueryIn

namespace AggQueryIn

/-- **The pass**, both halves at once. For every query over the classes
of `S` and `⊎` (restricted recursions, the signature `Θ` holding the count
the construction pads with) and every injective supply of names the query
does not use: a query with no `⊎`, keeping what `SumFreeAnnOf` lists and
matching the query wherever it settles; and, for a body reading the name
`s` once, a body still reading it once and a closed query the body is the
sum of. The operands of a `⊎` may carry aggregate columns. -/
theorem exists_sumFreeAnn_aux {S : Set OpKind} (hS : sumMuOps ⊆ S) {Θ : Set (SeqAggFunc T)}
    {cnt : SeqAggFunc T} (hcnt : cnt ∈ Θ) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly (insert OpKind.union S) → q.hygienic → q.inSig Θ →
      ∀ (f : ℕ → String), Function.Injective f → (∀ i, f i ∉ q.names) →
        (l = [] → ∃ q' : AggQueryIn T c n κ, SumFreeAnnOf S Θ f q q'
            ∧ ClosedMatch (K := K) q q')
        ∧ (∀ (s : String) (m : ℕ), l = [(s, m)] → q.noMention s →
            ∃ (q' : AggQueryIn T c n κ l) (qC : AggQueryIn T c n κ), qC.noMention s
              ∧ SumFreeAnnOf S Θ f q q' ∧ SumFreeAnnOf S Θ f q qC
              ∧ BodySplit (K := K) q q' qC) := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro hq hr hi f hf hfr
    exact ⟨fun _ => ⟨AggQueryIn.Rel n s', ⟨trivial, trivial, trivial, id, fun _ _ h => h,
      fun _ _ h => h, fun x hx => Or.inl hx, fun _ _ h => h, id⟩, closedMatch_refl _⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Hole n s' κh =>
    intro hq hr hi f hf hfr
    refine ⟨fun hl => absurd hl (by simp), fun s m hl _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
    refine ⟨AggQueryIn.Hole n _ κh, emptyK κh cnt, noMention_emptyK κh cnt _,
      ⟨trivial, trivial, trivial, id, fun _ _ h => h, fun _ _ h => h, fun x hx => Or.inl hx,
        fun _ _ h => h, id⟩,
      ⟨usesOnly_emptyK hS κh cnt, hygienic_emptyK κh cnt, inSig_emptyK κh hcnt,
        fun _ => noExplode_emptyK κh cnt, fun ρc HK _ => wellKinded_emptyK κh cnt ρc HK,
        fun sch _ _ => overSchema_emptyK sch κh cnt,
        fun x hx => by rw [names_emptyK] at hx; exact absurd hx (Finset.notMem_empty x),
        fun s' _ _ => noMention_emptyK κh cnt s', fun _ => noGammaNest_emptyK κh cnt⟩,
      fun d γ E E' hE _ => ⟨trivial, annSettlesAt_emptyK κh cnt d γ E', ?_⟩⟩
    rw [evaluate_emptyK, Multiset.map_zero, add_zero]
    exact AggQueryIn.FinEq.refl _ d γ E E' hE
  | Param pv ρ =>
    intro hq hr hi f hf hfr
    exact ⟨fun _ => ⟨AggQueryIn.Param pv ρ, ⟨⟨memS nofun hq.1, memS nofun hq.2.1,
      memS nofun hq.2.2⟩, trivial, trivial, id, fun _ _ h => h, fun _ _ h => h,
      fun x hx => Or.inl hx, fun _ _ h => h, id⟩, closedMatch_refl _⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Empty =>
    intro hq hr hi f hf hfr
    exact ⟨fun _ => ⟨AggQueryIn.Empty, ⟨memS nofun hq, trivial, trivial, id, fun _ _ h => h,
      fun _ _ h => h, fun x hx => Or.inl hx, fun _ _ h => h, id⟩, closedMatch_refl _⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Proj ps q ih =>
    intro hq hr hi f hf hfr
    obtain ⟨hc, hb⟩ := ih hq.2 hr hi.2 f hf hfr
    have hbun : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ _ l'}, SumFreeAnnOf S Θ f q p →
        SumFreeAnnOf S Θ f (AggQueryIn.Proj ps q) (AggQueryIn.Proj ps p) := fun hs =>
      ⟨⟨⟨memS nofun hq.1.1, hq.1.2⟩, hs.usesOnly⟩, hs.hygienic, ⟨hi.1, hs.inSig⟩, hs.noExplode,
        fun ρc HK h => ⟨h.1, hs.wellKinded ρc HK h.2⟩, hs.over, hs.names, hs.nom, hs.noNest⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      refine ⟨AggQueryIn.Proj ps q', hbun hs, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs', he'⟩ := he d γ E E' hE hset
      exact ⟨hs', FinAt.proj ps he'⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      refine ⟨AggQueryIn.Proj ps q', AggQueryIn.Proj ps qC, hCn, hbun hs, hbun hsC,
        fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs', hsC', he'⟩ := he d γ E E' hE hset
      refine ⟨hs', hsC', ?_⟩
      rw [FinAt.proj ps (fin_sum_of_split he'), evaluate_proj_sum, Multiset.map_add]
  | Sel φ q hφ ih =>
    rename_i lq
    intro hq hr hi f hf hfr
    obtain ⟨hc, hb⟩ := ih hq.2 hr hi.2 f hf hfr
    have hbun : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ _ l'} (hp : SelOK l' φ),
        SumFreeAnnOf S Θ f q p →
        SumFreeAnnOf S Θ f (AggQueryIn.Sel φ q hφ) (AggQueryIn.Sel φ p hp) := fun _ hs =>
      ⟨⟨memS nofun hq.1, hs.usesOnly⟩, hs.hygienic, ⟨hi.1, hs.inSig⟩, hs.noExplode,
        fun ρc HK h => ⟨h.1, hs.wellKinded ρc HK h.2⟩, hs.over, hs.names, hs.nom, hs.noNest⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      subst hl
      refine ⟨AggQueryIn.Sel φ q' hφ, hbun hφ hs, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs', he'⟩ := he d γ E E' hE hset
      exact ⟨hs', FinAt.sel φ hφ hφ he'⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      refine ⟨AggQueryIn.Sel φ q' hφ, AggQueryIn.Sel φ qC trivial, hCn, hbun hφ hs,
        hbun (l' := []) trivial hsC, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs', hsC', he'⟩ := he d γ E E' hE hset
      refine ⟨hs', hsC', ?_⟩
      have hφ' : SelOK (lq ++ []) φ := by rw [List.append_nil]; exact hφ
      rw [FinAt.sel φ hφ hφ' (fin_sum_of_split he'), evaluate_sel_sum φ q' qC hφ' hφ trivial,
        Multiset.map_add]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi f hf hfr
    have hfr₁ := fresh_sub hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_sub hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, hb₁⟩ := ih₁ hq.2.1 hr.1 hi.1 f hf hfr₁
    obtain ⟨hc₂, hb₂⟩ := ih₂ hq.2.2 hr.2 hi.2 f hf hfr₂
    have hbun : ∀ {l₁' l₂' : List (String × ℕ)} {p₁ : AggQueryIn T _ _ _ l₁'}
        {p₂ : AggQueryIn T _ _ _ l₂'}, SumFreeAnnOf S Θ f q₁ p₁ → SumFreeAnnOf S Θ f q₂ p₂ →
        SumFreeAnnOf S Θ f (AggQueryIn.Prod q₁ q₂) (AggQueryIn.Prod p₁ p₂) := fun hs₁ hs₂ =>
      ⟨⟨memS nofun hq.1, hs₁.usesOnly, hs₂.usesOnly⟩, ⟨hs₁.hygienic, hs₂.hygienic⟩,
        ⟨hs₁.inSig, hs₂.inSig⟩, fun h => ⟨hs₁.noExplode h.1, hs₂.noExplode h.2⟩,
        fun ρc HK h => ⟨hs₁.wellKinded ρc HK h.1, hs₂.wellKinded ρc HK h.2⟩,
        fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
        names_union hs₁.names hs₂.names,
        fun s hs hn => ⟨hs₁.nom s hs hn.1, hs₂.nom s hs hn.2⟩,
        fun h => ⟨hs₁.noNest h.1, hs₂.noNest h.2⟩⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
      obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
      refine ⟨AggQueryIn.Prod q₁' q₂', hbun hs₁ hs₂, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ d γ E E' hE hset.1
      obtain ⟨hs₂', he₂'⟩ := he₂ d γ E E' hE hset.2
      exact ⟨⟨hs₁', hs₂'⟩, FinAt.prod he₁' he₂'⟩
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
        obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hb₁ s m rfl h₁
        refine ⟨AggQueryIn.Prod p₁ q₂', AggQueryIn.Prod pC q₂', ⟨hCn, hs₂.nom s ?_ h₂⟩,
          hbun hp hs₂, hbun hpC hs₂, fun d γ E E' hE hset => ?_⟩
        · exact ne_of_mem hfr (Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁
            (List.mem_singleton_self _)))
        obtain ⟨hp', hpC', he'⟩ := he d γ E E' hE hset.1
        obtain ⟨hs₂', he₂'⟩ := he₂ d γ E E' hE hset.2
        refine ⟨⟨hp', hs₂'⟩, ⟨hpC', hs₂'⟩, ?_⟩
        rw [FinAt.prod (fin_sum_of_split he') he₂', evaluate_prod_sum_left, Multiset.map_add]
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
        obtain ⟨p₂, pC, hCn, hp, hpC, he⟩ := hb₂ s m rfl h₂
        refine ⟨AggQueryIn.Prod q₁' p₂, AggQueryIn.Prod q₁' pC, ⟨hs₁.nom s ?_ h₁, hCn⟩,
          hbun hs₁ hp, hbun hs₁ hpC, fun d γ E E' hE hset => ?_⟩
        · exact ne_of_mem hfr (Finset.mem_union_right _ (AggQueryIn.mem_names_of_index q₂
            (List.mem_singleton_self _)))
        obtain ⟨hs₁', he₁'⟩ := he₁ d γ E E' hE hset.1
        obtain ⟨hp', hpC', he'⟩ := he d γ E E' hE hset.2
        refine ⟨⟨hs₁', hp'⟩, ⟨hs₁', hpC'⟩, ?_⟩
        rw [FinAt.prod he₁' (fin_sum_of_split he'), evaluate_prod_sum_right, Multiset.map_add]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi f hf hfr
    have hfr₁ := fresh_sub hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_sub hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, hb₁⟩ := ih₁ hq.2.1 hr.1 hi.1 f hf hfr₁
    obtain ⟨hc₂, -⟩ := ih₂ hq.2.2 hr.2 hi.2 f hf hfr₂
    obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
    have hbun : ∀ {l₁' : List (String × ℕ)} {p₁ : AggQueryIn T _ _ _ l₁'},
        SumFreeAnnOf S Θ f q₁ p₁ →
        SumFreeAnnOf S Θ f (AggQueryIn.Apply q₁ q₂) (AggQueryIn.Apply p₁ q₂') := fun hs₁ =>
      ⟨⟨memS nofun hq.1, hs₁.usesOnly, hs₂.usesOnly⟩, ⟨hs₁.hygienic, hs₂.hygienic⟩,
        ⟨hs₁.inSig, hs₂.inSig⟩, fun h => ⟨hs₁.noExplode h.1, hs₂.noExplode h.2⟩,
        fun ρc HK h => ⟨hs₁.wellKinded ρc HK h.1, hs₂.wellKinded _ HK h.2⟩,
        fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
        names_union hs₁.names hs₂.names,
        fun s hs hn => ⟨hs₁.nom s hs hn.1, hs₂.nom s hs hn.2⟩,
        fun h => ⟨hs₁.noNest h.1, hs₂.noNest h.2⟩⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q₁', hs₁, he₁⟩ := hc₁ hl
      refine ⟨AggQueryIn.Apply q₁' q₂', hbun hs₁, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ d γ E E' hE hset.1
      refine ⟨⟨hs₁', fun x' hx' => apply_right_settles he₂ hE hset.2 ?_⟩,
        FinAt.apply he₁' (fun x hx => (he₂ d _ _ _ (hE.enter rfl _) (hset.2 x hx)).2)⟩
      rw [he₁']
      exact Multiset.mem_map_of_mem _ hx'
    · obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hb₁ s m hl hnm.1
      have hs2 : ∀ i, s ≠ f i :=
        ne_of_mem hfr (Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁
          (hl ▸ List.mem_singleton_self _)))
      refine ⟨AggQueryIn.Apply p₁ q₂', AggQueryIn.Apply pC q₂', ⟨hCn, hs₂.nom s hs2 hnm.2⟩,
        hbun hp, hbun hpC, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hp', hpC', he'⟩ := he d γ E E' hE hset.1
      refine ⟨⟨hp', fun x' hx' => apply_right_settles he₂ hE hset.2 ?_⟩,
        ⟨hpC', fun x' hx' => apply_right_settles he₂ hE hset.2 ?_⟩, ?_⟩
      · rw [he', Multiset.mem_add]
        exact Or.inl (Multiset.mem_map_of_mem _ hx')
      · rw [he', Multiset.mem_add]
        exact Or.inr (Multiset.mem_map_of_mem _ hx')
      · rw [FinAt.apply (fin_sum_of_split he')
          (fun x hx => (he₂ d _ _ _ (hE.enter rfl _) (hset.2 x hx)).2),
          evaluate_apply_sum, Multiset.map_add]
  | Sum q₁ q₂ ih₁ ih₂ =>
    rename_i c' n' κ' l₁ l₂
    intro hq hr hi f hf hfr
    have hfr₁ := fresh_shift hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_shift hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, hb₁⟩ := ih₁ hq.2.1 hr.1 hi.1 (shift2 f) (shift2_injective hf) hfr₁
    obtain ⟨hc₂, hb₂⟩ := ih₂ hq.2.2 hr.2 hi.2 (shift2 f) (shift2_injective hf) hfr₂
    have hf0 : f 0 ∉ (AggQueryIn.Sum q₁ q₂).names := hfr 0
    have hf1 : f 1 ∉ (AggQueryIn.Sum q₁ q₂).names := hfr 1
    have hf0₁ : f 0 ∉ q₁.names := fun h => hf0 (Finset.mem_union_left _ h)
    have hf1₁ : f 1 ∉ q₁.names := fun h => hf1 (Finset.mem_union_left _ h)
    have hf1₂ : f 1 ∉ q₂.names := fun h => hf1 (Finset.mem_union_right _ h)
    -- the bundle for a construction over two children's outputs
    have hbundle : ∀ {p₁ p₂ : AggQueryIn T c' n' κ'},
        SumFreeAnnOf S Θ (shift2 f) q₁ p₁ → SumFreeAnnOf S Θ (shift2 f) q₂ p₂ →
        SumFreeAnnOf S Θ f (AggQueryIn.Sum q₁ q₂) (sumByMuK (f 0) (f 1) cnt p₁ p₂) := by
      intro p₁ p₂ hp₁ hp₂
      have hn₁₀ : f 0 ∉ p₁.names := not_mem_of_shift hf hp₁.names (by omega) hf0₁
      have hn₁₁ : f 1 ∉ p₁.names := not_mem_of_shift hf hp₁.names (by omega) hf1₁
      have hn₂₁ : f 1 ∉ p₂.names := not_mem_of_shift hf hp₂.names (by omega) hf1₂
      exact {
        usesOnly := usesOnly_sumByMuK hS _ _ cnt _ _ hp₁.usesOnly hp₂.usesOnly
        hygienic := hygienic_sumByMuK _ _ cnt _ _
          (AggQueryIn.noMention_of_not_mem_names _ hn₁₀)
          (AggQueryIn.noMention_of_not_mem_names _ hn₁₁)
          (AggQueryIn.noMention_of_not_mem_names _ hn₂₁)
          hp₁.hygienic hp₂.hygienic
        inSig := inSig_sumByMuK _ _ hcnt _ _ hp₁.inSig hp₂.inSig
        noExplode := fun h => noExplode_sumByMuK _ _ cnt _ _ (hp₁.noExplode h.1)
          (hp₂.noExplode h.2)
        noNest := fun h => noGammaNest_sumByMuK _ _ cnt _ _ (hp₁.noNest h.1)
          (hp₂.noNest h.2)
        wellKinded := fun ρc HK h => wellKinded_sumByMuK _ _ cnt _ _
          (hp₁.wellKinded ρc HK h.1) (hp₂.wellKinded ρc HK h.2)
        over := fun sch hsch ho => overSchema_sumByMuK sch _ _ cnt _ _ (hsch 0) (hsch 1) hn₁₀
          hn₂₁ (hp₁.over sch (fun i => hsch (i + 2)) ho.1)
          (hp₂.over sch (fun i => hsch (i + 2)) ho.2)
        names := fun x hx => by
          rcases Finset.mem_insert.mp (names_sumByMuK _ _ cnt _ _ hx) with rfl | hx'
          · exact Or.inr ⟨0, rfl⟩
          rcases Finset.mem_insert.mp hx' with rfl | hx''
          · exact Or.inr ⟨1, rfl⟩
          exact (Finset.mem_union.mp hx'').elim
            (fun h => names_shift (hp₁.names x h) Finset.subset_union_left)
            (fun h => names_shift (hp₂.names x h) Finset.subset_union_right)
        nom := fun s hs hn => noMention_sumByMuK _ _ cnt _ _
          (hp₁.nom s (fun i => hs (i + 2)) hn.1) (hp₂.nom s (fun i => hs (i + 2)) hn.2) }
    -- the construction's value and settling over two children's outputs
    have hval : ∀ (p₁ p₂ : AggQueryIn T c' n' κ') (d : AnnotatedDatabase T K) (γ : Fin c' → T)
        (E' : EvalEnv T K), p₁.AnnSettlesAt d γ E' → p₂.AnnSettlesAt d γ E' →
          (sumByMuK (f 0) (f 1) cnt p₁ p₂).AnnSettlesAt d γ E'
            ∧ ((sumByMuK (f 0) (f 1) cnt p₁ p₂).evaluate d γ E').map GenRow.fin
                = (p₁.evaluate d γ E').map GenRow.fin + (p₂.evaluate d γ E').map GenRow.fin :=
      fun p₁ p₂ d γ E' h₁ h₂ => ⟨annSettlesAt_sumByMuK _ _ cnt p₁ p₂ d γ E' h₁ h₂,
        evaluate_sumByMuK_fin _ _ cnt p₁ p₂ d γ E'⟩
    have hsum : ∀ (d : AnnotatedDatabase T K) (γ : Fin c' → T) (E : EvalEnv T K),
        ((AggQueryIn.Sum q₁ q₂).evaluate d γ E).map GenRow.fin
          = (q₁.evaluate d γ E).map GenRow.fin + (q₂.evaluate d γ E).map GenRow.fin :=
      fun d γ E => Multiset.map_add _ _ _
    -- a child's output, as the output for the sum
    have hleft : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T c' n' κ' l'},
        SumFreeAnnOf S Θ (shift2 f) q₁ p → SumFreeAnnOf S Θ f (AggQueryIn.Sum q₁ q₂) p :=
      fun hp => ⟨hp.usesOnly, hp.hygienic, hp.inSig, fun h => hp.noExplode h.1,
        fun ρc HK h => hp.wellKinded ρc HK h.1,
        fun sch hsch ho => hp.over sch (fun i => hsch (i + 2)) ho.1,
        fun x hx => names_shift (hp.names x hx) Finset.subset_union_left,
        fun s hs hn => hp.nom s (fun i => hs (i + 2)) hn.1,
        fun h => hp.noNest h.1⟩
    have hright : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T c' n' κ' l'},
        SumFreeAnnOf S Θ (shift2 f) q₂ p → SumFreeAnnOf S Θ f (AggQueryIn.Sum q₁ q₂) p :=
      fun hp => ⟨hp.usesOnly, hp.hygienic, hp.inSig, fun h => hp.noExplode h.2,
        fun ρc HK h => hp.wellKinded ρc HK h.2,
        fun sch hsch ho => hp.over sch (fun i => hsch (i + 2)) ho.2,
        fun x hx => names_shift (hp.names x hx) Finset.subset_union_right,
        fun s hs hn => hp.nom s (fun i => hs (i + 2)) hn.2,
        fun h => hp.noNest h.2⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
      obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
      refine ⟨sumByMuK (f 0) (f 1) cnt q₁' q₂', hbundle hs₁ hs₂, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ d γ E E' hE hset.1
      obtain ⟨hs₂', he₂'⟩ := he₂ d γ E E' hE hset.2
      obtain ⟨hv, hv'⟩ := hval q₁' q₂' d γ E' hs₁' hs₂'
      exact ⟨hv, by rw [hsum, hv', he₁', he₂']⟩
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
        obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hb₁ s m rfl h₁
        have hss : s ∈ (AggQueryIn.Sum q₁ q₂).names :=
          Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁
            (List.mem_singleton_self _))
        refine ⟨p₁, sumByMuK (f 0) (f 1) cnt pC q₂',
          noMention_sumByMuK _ _ cnt _ _ hCn (hs₂.nom s (ne_shift_of_mem hfr hss) h₂),
          hleft hp, hbundle hpC hs₂, fun d γ E E' hE hset => ?_⟩
        obtain ⟨hp', hpC', he'⟩ := he d γ E E' hE hset.1
        obtain ⟨hs₂', he₂'⟩ := he₂ d γ E E' hE hset.2
        obtain ⟨hv, hv'⟩ := hval pC q₂' d γ E' hpC' hs₂'
        refine ⟨hp', hv, ?_⟩
        rw [hsum, hv', he', he₂', add_assoc]
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
        obtain ⟨p₂, pC, hCn, hp, hpC, he⟩ := hb₂ s m rfl h₂
        have hss : s ∈ (AggQueryIn.Sum q₁ q₂).names :=
          Finset.mem_union_right _ (AggQueryIn.mem_names_of_index q₂
            (List.mem_singleton_self _))
        refine ⟨p₂, sumByMuK (f 0) (f 1) cnt q₁' pC,
          noMention_sumByMuK _ _ cnt _ _ (hs₁.nom s (ne_shift_of_mem hfr hss) h₁) hCn,
          hright hp, hbundle hs₁ hpC, fun d γ E E' hE hset => ?_⟩
        obtain ⟨hs₁', he₁'⟩ := he₁ d γ E E' hE hset.1
        obtain ⟨hp', hpC', he'⟩ := he d γ E E' hE hset.2
        obtain ⟨hv, hv'⟩ := hval q₁' pC d γ E' hs₁' hpC'
        refine ⟨hp', hv, ?_⟩
        rw [hsum, hv', he₁', he', add_left_comm]
  | Dedup q ih =>
    intro hq hr hi f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.Dedup q', ⟨⟨memS nofun hq.1, hs.usesOnly⟩, hs.hygienic,
      hs.inSig, hs.noExplode, hs.wellKinded, hs.over, hs.names, hs.nom, hs.noNest⟩,
      fun d γ E E' hE hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he d γ E E' hE hset
    exact ⟨hs', FinAt.dedup he'⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi f hf hfr
    have hfr₁ := fresh_sub hfr (Finset.subset_union_left (s₂ := q₂.names))
    have hfr₂ := fresh_sub hfr (Finset.subset_union_right (s₁ := q₁.names))
    obtain ⟨hc₁, -⟩ := ih₁ hq.2.1 hr.1 hi.1 f hf hfr₁
    obtain ⟨hc₂, -⟩ := ih₂ hq.2.2 hr.2 hi.2 f hf hfr₂
    obtain ⟨q₁', hs₁, he₁⟩ := hc₁ rfl
    obtain ⟨q₂', hs₂, he₂⟩ := hc₂ rfl
    refine ⟨fun _ => ⟨AggQueryIn.Diff q₁' q₂', ⟨⟨memS nofun hq.1, hs₁.usesOnly, hs₂.usesOnly⟩,
      ⟨hs₁.hygienic, hs₂.hygienic⟩, ⟨hs₁.inSig, hs₂.inSig⟩,
      fun h => ⟨hs₁.noExplode h.1, hs₂.noExplode h.2⟩,
      fun ρc HK h => ⟨hs₁.wellKinded ρc HK h.1, hs₂.wellKinded ρc HK h.2⟩,
      fun sch hsch ho => ⟨hs₁.over sch hsch ho.1, hs₂.over sch hsch ho.2⟩,
      names_union hs₁.names hs₂.names,
      fun s hs hn => ⟨hs₁.nom s hs hn.1, hs₂.nom s hs hn.2⟩,
        fun h => ⟨hs₁.noNest h.1, hs₂.noNest h.2⟩⟩, fun d γ E E' hE hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs₁', he₁'⟩ := he₁ d γ E E' hE hset.1
    obtain ⟨hs₂', he₂'⟩ := he₂ d γ E E' hE hset.2
    exact ⟨⟨hs₁', hs₂'⟩, FinAt.diff he₁' he₂'⟩
  | Explode k hk q ih =>
    intro hq hr hi f hf hfr
    obtain ⟨hc, hb⟩ := ih hq hr hi f hf hfr
    have hbun : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ _ l'}, SumFreeAnnOf S Θ f q p →
        SumFreeAnnOf S Θ f (AggQueryIn.Explode k hk q) (AggQueryIn.Explode k hk p) := fun hs =>
      ⟨hs.usesOnly, hs.hygienic, hs.inSig, id, hs.wellKinded, hs.over, hs.names, hs.nom, hs.noNest⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      refine ⟨AggQueryIn.Explode k hk q', hbun hs, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs', he'⟩ := he d γ E E' hE hset
      exact ⟨hs', FinAt.explode k hk he'⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      refine ⟨AggQueryIn.Explode k hk q', AggQueryIn.Explode k hk qC, hCn, hbun hs, hbun hsC,
        fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs', hsC', he'⟩ := he d γ E E' hE hset
      refine ⟨hs', hsC', ?_⟩
      rw [FinAt.explode k hk (fin_sum_of_split he'), evaluate_explode_sum, Multiset.map_add]
  | Retag hk q ih =>
    intro hq hr hi f hf hfr
    obtain ⟨hc, hb⟩ := ih hq hr hi f hf hfr
    have hbun : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ _ l'}, SumFreeAnnOf S Θ f q p →
        SumFreeAnnOf S Θ f (AggQueryIn.Retag hk q) (AggQueryIn.Retag hk p) := fun hs =>
      ⟨hs.usesOnly, hs.hygienic, hs.inSig, hs.noExplode, hs.wellKinded, hs.over, hs.names,
        hs.nom, hs.noNest⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hs, he⟩ := hc hl
      refine ⟨AggQueryIn.Retag hk q', hbun hs, fun d γ E E' hE hset => ?_⟩
      obtain ⟨hs', he'⟩ := he d γ E E' hE hset
      exact ⟨hs', FinAt.retag hk he'⟩
    · obtain ⟨q', qC, hCn, hs, hsC, he⟩ := hb s m hl hnm
      exact ⟨AggQueryIn.Retag hk q', AggQueryIn.Retag hk qC, hCn, hbun hs, hbun hsC,
        fun d γ E E' hE hset => he d γ E E' hE hset⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hq hr hi f hf hfr
    have hfr₀ : ∀ i, f i ∉ q₀.names :=
      fun i h => hfr i (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hfr₁ : ∀ i, f i ∉ q₁.names :=
      fun i h => hfr i (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hfs : ∀ i, s ≠ f i := ne_of_mem hfr (Finset.mem_insert_self s _)
    obtain ⟨hc₀, -⟩ := ih₀ hq.2.1 hr.2.2.1 hi.1 f hf hfr₀
    obtain ⟨q₀', hs₀, he₀⟩ := hc₀ rfl
    obtain ⟨-, hb₁⟩ := ih₁ hq.2.2 hr.2.2.2 hi.2 f hf hfr₁
    obtain ⟨q₁', qC, hCn, hs₁, hsC, he₁⟩ := hb₁ s _ rfl hr.2.1
    refine ⟨fun _ => ⟨AggQueryIn.Mu s q₀' q₁', ?_, fun d γ E E' hE hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · exact {
        usesOnly := ⟨memS nofun hq.1, hs₀.usesOnly, hs₁.usesOnly⟩
        hygienic := ⟨hs₀.nom s hfs hr.1, hs₁.nom s hfs hr.2.1, hs₀.hygienic, hs₁.hygienic⟩
        inSig := ⟨hs₀.inSig, hs₁.inSig⟩
        noExplode := fun h => ⟨hs₀.noExplode h.1, hs₁.noExplode h.2⟩
        noNest := fun h => ⟨hs₀.noNest h.1, hs₁.noNest h.2⟩
        wellKinded := fun ρc HK h => ⟨hs₀.wellKinded ρc HK h.1, hs₁.wellKinded ρc _ h.2⟩
        over := fun sch hsch ho => ⟨ho.1, hs₀.over sch hsch ho.2.1, hs₁.nom s hfs ho.2.2.1,
          hs₁.over (sch.update s _) (fun i => by
            rw [Schema.update_apply, ite_eq_right (hfs i).symm]
            exact hsch i) ho.2.2.2⟩
        names := fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact Or.inl (Finset.mem_insert_self _ _)
          exact (Finset.mem_union.mp hx').elim
            (fun h => (hs₀.names x h).imp_left
              (fun h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
            (fun h => (hs₁.names x h).imp_left
              (fun h => Finset.mem_insert_of_mem (Finset.mem_union_right _ h)))
        nom := fun s' hs' hn => ⟨hs₀.nom s' hs' hn.1, hs₁.nom s' hs' hn.2⟩ }
    · exact AggQueryIn.mu_of_splitAnn s q₀ q₀' q₁ q₁' qC d γ hE hset
        (he₀ d γ E E' hE hset.1) (fun F F' hF h => he₁ d γ F F' hF h)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hq hr hi f hf hfr
    have hfr₀ : ∀ i, shift2 f i ∉ q₀.names :=
      fun i h => hfr (i + 2) (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hfr₁ : ∀ i, shift2 f i ∉ q₁.names :=
      fun i h => hfr (i + 2) (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    have hfs : ∀ i, s ≠ f i := ne_of_mem hfr (Finset.mem_insert_self s _)
    have hf0₀ : f 0 ∉ q₀.names :=
      fun h => hfr 0 (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hf1₀ : f 1 ∉ q₀.names :=
      fun h => hfr 1 (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hf1₁ : f 1 ∉ q₁.names :=
      fun h => hfr 1 (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    obtain ⟨hc₀, -⟩ := ih₀ hq.2.1 hr.2.2.1 hi.1 (shift2 f) (shift2_injective hf) hfr₀
    obtain ⟨q₀', hs₀, he₀⟩ := hc₀ rfl
    obtain ⟨-, hb₁⟩ := ih₁ hq.2.2 hr.2.2.2 hi.2 (shift2 f) (shift2_injective hf) hfr₁
    obtain ⟨q₁', qC, hCn, hs₁, hsC, he₁⟩ := hb₁ s _ rfl hr.2.1
    have hn₀₀ : f 0 ∉ q₀'.names := not_mem_of_shift hf hs₀.names (by omega) hf0₀
    have hn₀₁ : f 1 ∉ q₀'.names := not_mem_of_shift hf hs₀.names (by omega) hf1₀
    have hnC1 : f 1 ∉ qC.names := not_mem_of_shift hf hsC.names (by omega) hf1₁
    have h₀n : q₀'.noMention s := hs₀.nom s (fun i => hfs (i + 2)) hr.1
    have hbn : (sumByMuK (f 0) (f 1) cnt q₀' qC).noMention s :=
      noMention_sumByMuK _ _ cnt _ _ h₀n hCn
    have hupd : ∀ (m : ℕ) (sch : Schema), (∀ i, sch (f i) = none) →
        ∀ i, (sch.update s m) (f i) = none := fun m sch hsch i => by
      rw [Schema.update_apply, ite_eq_right (hfs i).symm]
      exact hsch i
    refine ⟨fun _ => ⟨AggQueryIn.MuSet s (sumByMuK (f 0) (f 1) cnt q₀' qC) q₁', ?_,
      fun d γ E E' hE hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    · exact {
        usesOnly := ⟨memS nofun hq.1, usesOnly_sumByMuK hS _ _ cnt _ _ hs₀.usesOnly
          hsC.usesOnly, hs₁.usesOnly⟩
        hygienic := ⟨hbn, hs₁.nom s (fun i => hfs (i + 2)) hr.2.1,
          hygienic_sumByMuK _ _ cnt _ _
            (AggQueryIn.noMention_of_not_mem_names _ hn₀₀)
            (AggQueryIn.noMention_of_not_mem_names _ hn₀₁)
            (AggQueryIn.noMention_of_not_mem_names _ hnC1)
            hs₀.hygienic hsC.hygienic, hs₁.hygienic⟩
        inSig := ⟨inSig_sumByMuK _ _ hcnt _ _ hs₀.inSig hsC.inSig, hs₁.inSig⟩
        noExplode := fun h => ⟨noExplode_sumByMuK _ _ cnt _ _ (hs₀.noExplode h.1)
          (hsC.noExplode h.2), hs₁.noExplode h.2⟩
        noNest := fun h => ⟨noGammaNest_sumByMuK _ _ cnt _ _ (hs₀.noNest h.1)
          (hsC.noNest h.2), hs₁.noNest h.2⟩
        wellKinded := fun ρc HK h => ⟨wellKinded_sumByMuK _ _ cnt _ _ (hs₀.wellKinded ρc HK h.1)
          (AggQueryIn.wellKinded_congr_holes qC ρc (fun _ hp => absurd hp List.not_mem_nil)
            (hsC.wellKinded ρc _ h.2)), hs₁.wellKinded ρc _ h.2⟩
        over := fun sch hsch ho => ⟨ho.1,
          overSchema_sumByMuK sch _ _ cnt _ _ (hsch 0) (hsch 1) hn₀₀ hnC1
            (hs₀.over sch (fun i => hsch (i + 2)) ho.2.1)
            (AggQueryIn.overSchema_of_update_of_noMention qC (fun _ h => by simp at h) hCn
              (hsC.over (sch.update s _) (fun i => hupd _ sch hsch (i + 2)) ho.2.2.2)),
          hs₁.nom s (fun i => hfs (i + 2)) hr.2.1,
          hs₁.over (sch.update s _) (fun i => hupd _ sch hsch (i + 2)) ho.2.2.2⟩
        names := fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact Or.inl (Finset.mem_insert_self _ _)
          rcases Finset.mem_union.mp hx' with h | h
          · rcases Finset.mem_insert.mp (names_sumByMuK _ _ cnt _ _ h) with rfl | h'
            · exact Or.inr ⟨0, rfl⟩
            rcases Finset.mem_insert.mp h' with rfl | h''
            · exact Or.inr ⟨1, rfl⟩
            exact (Finset.mem_union.mp h'').elim
              (fun h => names_shift (hs₀.names x h)
                (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)))
              (fun h => names_shift (hsC.names x h)
                (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_right _ hy)))
          · exact names_shift (hs₁.names x h)
              (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_right _ hy))
        nom := fun s' hs' hn => ⟨noMention_sumByMuK _ _ cnt _ _
          (hs₀.nom s' (fun i => hs' (i + 2)) hn.1) (hsC.nom s' (fun i => hs' (i + 2)) hn.2),
          hs₁.nom s' (fun i => hs' (i + 2)) hn.2⟩ }
    · have h₀ := he₀ d γ E E' hE hset.1
      exact AggQueryIn.muSet_of_splitAnn s q₀ q₀' q₁ q₁' qC _ d γ hE hset h₀
        (fun F F' hF h => he₁ d γ F F' hF h)
        (fun hC => ⟨annSettlesAt_sumByMuK _ _ cnt q₀' qC d γ E' h₀.1 hC,
          evaluate_sumByMuK_fin _ _ cnt q₀' qC d γ E'⟩)
  | Gamma is ts fs q keep ord ih =>
    rename_i lab rd
    intro hq hr hi f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2.2 f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q' keep ord, ⟨⟨memS nofun
        hq.1,
        hs.usesOnly⟩,
      hs.hygienic, ⟨hi.1, hi.2.1, hi.2.2.1, hs.inSig⟩, hs.noExplode,
      fun ρc HK h => ⟨h.1, hs.wellKinded ρc HK h.2⟩, hs.over, hs.names, hs.nom, hs.noNest⟩,
      fun d γ E E' hE hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he d γ E E' hE hset
    exact ⟨hs', FinAt.gamma is ts fs keep ord he' hE.1⟩
  | GammaScalar ts fs q ord ih =>
    rename_i lab rd
    intro hq hr hi f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2 f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q' ord, ⟨⟨memS nofun
        hq.1,
        hs.usesOnly⟩,
      hs.hygienic, ⟨hi.1, hi.2.1, hs.inSig⟩, hs.noExplode,
      fun ρc HK h => ⟨h.1, hs.wellKinded ρc HK h.2⟩, hs.over, hs.names, hs.nom, hs.noNest⟩,
      fun d γ E E' hE hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he d γ E E' hE hset
    exact ⟨hs', FinAt.gammaScalar ts fs ord he' hE.1⟩
  | GammaNest is his p fn q ih =>
    rename_i lab rd
    intro hq hr hi f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2 f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p fn q', ⟨⟨⟨memS nofun
        hq.1.1,
        hq.1.2⟩,
        hs.usesOnly⟩, hs.hygienic, ⟨hi.1, hi.2.1, hs.inSig⟩, hs.noExplode,
      fun ρc HK h => ⟨h.1, hs.wellKinded ρc HK h.2⟩, hs.over, hs.names, hs.nom,
      fun h => h.elim⟩,
      fun d γ E E' hE hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he d γ E E' hE hset
    exact ⟨hs', FinAt.gammaNest is his p fn he' hE.1⟩
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t fw q hrr dist keep ih =>
    rename_i lab rd
    intro hq hr hi f hf hfr
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2.2 f hf hfr
    obtain ⟨q', hs, he⟩ := hc rfl
    refine ⟨fun _ => ⟨AggQueryIn.Win (lab := lab) (rd := rd) P O o w t fw q' hrr dist keep,
      ⟨⟨memS nofun hq.1, hs.usesOnly⟩, hs.hygienic, ⟨hi.1, hi.2.1, hi.2.2.1, hs.inSig⟩,
        hs.noExplode, fun ρc HK h => ⟨h.1, hs.wellKinded ρc HK h.2⟩, hs.over, hs.names,
        hs.nom, hs.noNest⟩, fun d γ E E' hE hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs', he'⟩ := he d γ E E' hE hset
    exact ⟨hs', FinAt.win P O o w t fw hrr dist keep he' hE.1⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ _ hi => hi.elim

end AggQueryIn

/-! ## `⊎` is dispensable in the annotated algebra -/

/-- **`ε`, `×` and `⊎` are dispensable in the annotated algebra**, over
every schema and every commutative m-semiring: each `ε` is a set
recursion (`dedupFree`), each product an apply (`prodFree`), and then each
`⊎` the union by two bag recursions over a driver row
(`AggQueryIn.sumByMuK`), whose operands may carry aggregate columns, the
rounds of a bag recursion being bound in the environment. A `⊎` on the
recursive path of a body is distributed out of it first, its closed side
moving into the base of a set recursion and vanishing at a bag recursion
that settles (`AggQueryIn.exists_sumFreeAnn_aux`). Every row, its columns
and its finalized annotation are kept, which is all the annotated
evaluation reads. -/
theorem generatesAnn_dedupProdSumFree (sch : Schema) (cnt : SeqAggFunc T) :
    GeneratesAnn T K sch cnt
      (((plainRecOps \ {OpKind.dedup}) \ {OpKind.prod}) \ {OpKind.union}) := by
  intro n κ q ho hu hi ha hp
  obtain ⟨q', ho', hu', hi', ha', hp', he⟩ :=
    generatesAnn_dedupProdFree (K := K) sch cnt q ho hu hi ha hp
  have hS : AggQueryIn.sumMuOps
      ⊆ ((plainRecOps \ {OpKind.dedup}) \ {OpKind.prod}) \ {OpKind.union} := by
    intro o ho
    simp only [AggQueryIn.sumMuOps, Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [plainRecOps, plainOps, basisDD, basisOps]
  have hu'' : q'.usesOnly (insert OpKind.union
      (((plainRecOps \ {OpKind.dedup}) \ {OpKind.prod}) \ {OpKind.union})) :=
    AggQueryIn.usesOnly_mono (fun o h => by
      by_cases hou : o = OpKind.union
      · exact Or.inl hou
      · exact Or.inr ⟨h, hou⟩) q' hu'
  obtain ⟨f, hf, hfs, hfn⟩ := AggQueryIn.exists_freshSupply sch q'.names
  obtain ⟨q'', hs, hm⟩ := (AggQueryIn.exists_sumFreeAnn_aux (K := K) hS
    (Set.mem_singleton cnt) q' hu'' (AggQueryIn.hygienic_of_overSchema q' sch ho') hi'
    f hf hfn).1 rfl
  refine ⟨q'', hs.over sch hfs ho', hs.usesOnly, hs.inSig, hs.noExplode ha',
    hs.wellKinded _ _ hp', fun d γ hset => ?_⟩
  obtain ⟨hs', he'⟩ := he d γ hset
  obtain ⟨hs'', he''⟩ := hm d γ {} {} (EvalEnv.FinRel.refl _) hs'
  exact ⟨hs'', (GenRow.map_toAnnotated_of_fin he'').symm.trans he'⟩
