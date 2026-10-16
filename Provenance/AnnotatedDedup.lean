import Provenance.AnnotatedBasis

/-!
# Duplicate elimination from the set recursion, annotated

`ε(q) = μ^∪R.(q, σ_false(R))` in every semiring, exactly: the first round
of the set recursion is the deduplication of `q`, the recursive term
reads the round and keeps nothing of it, so the second round is the
first and the iteration settles there, with the rows of `ε(q)` and their
annotations (`evaluate_dedupMu`). The recursion always settles
(`annSettlesAt_dedupMu`).

So `ε` is dispensable in the annotated algebra over every commutative
m-semiring: `dedupFree` replaces each `ε` by that recursion under a fresh
name, and `generatesAnn_dedupFree` says the classes other than `ε`
generate the annotated algebra (`GeneratesAnn`). The products go next
(`Provenance.AnnotatedProd`); the unions stay, the recursions' operands
being all-regular by typing and nothing re-typing an aggregate column
without exploding it.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-! ## One duplicate elimination as a set recursion -/

/-- `μ^∪s.(q, σ_false(s))`: the set recursion whose first round is `ε(q)`
and whose term adds nothing. -/
def dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c n (ColKind.allReg n) :=
  AggQueryIn.MuSet s q (AggQueryIn.Sel falsePred (AggQueryIn.Hole n s) (SelOK.of_noAggAtom rfl))

/-- The recursive term reads the round and keeps nothing. -/
theorem evaluate_selFalse_hole {c n : ℕ} (s : String) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.Sel (falsePred : GenPredIn T c (ColKind.allReg n)) (AggQueryIn.Hole n s)
      (SelOK.of_noAggAtom rfl)).evaluate d γ E = 0 := by
  simp only [AggQueryIn.evaluate]
  have hfa : (falsePred : GenPredIn T c (ColKind.allReg n)).hasAggAtom = false := rfl
  rw [ite_eq_right (by rw [hfa]; exact Bool.false_ne_true)]
  exact Multiset.filter_eq_nil.mpr (fun r _ => by
    rw [GenPredIn.holds_iff_holdsPlain]
    exact holdsPlain_falsePred _ _)

/-- The round function of the recursion is constant: the deduplication of
`q`. -/
theorem muSetStep_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    AggQueryIn.muSetStep s q
        (AggQueryIn.Sel falsePred (AggQueryIn.Hole n s) (SelOK.of_noAggAtom rfl))
        d γ E
      = fun _ => AnnotatedRelation.dedupAnn (q.evaluateAnnotated d γ E) := by
  funext X
  have hz : (AggQueryIn.Sel (falsePred : GenPredIn T c (ColKind.allReg n)) (AggQueryIn.Hole n s)
      (SelOK.of_noAggAtom rfl)).evaluateAnnotated d γ
        (E.assignHole s (X.map GenRow.ofAnnotated)) = 0 := by
    simp only [AggQueryIn.evaluateAnnotated, evaluate_selFalse_hole, Multiset.map_zero]
  simp only [AggQueryIn.muSetStep, hz]
  show AnnotatedRelation.dedupAnn (@HAdd.hAdd (Multiset (AnnotatedTuple T K n))
    (Multiset (AnnotatedTuple T K n)) (Multiset (AnnotatedTuple T K n)) instHAdd
    (q.evaluateAnnotated d γ E) 0) = _
  rw [add_zero]

/-- **`ε(q) = μ^∪s.(q, σ_false(s))`, exactly.** -/
theorem evaluate_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (dedupMu s q).evaluate d γ E = (AggQueryIn.Dedup q).evaluate d γ E := by
  rw [dedupMu, AggQueryIn.evaluate]
  refine Eq.trans (congrArg (Multiset.map GenRow.ofAnnotated) (muFix_congr
    (step' := fun _ => AnnotatedRelation.dedupAnn ((q.evaluate d γ E).map GenRow.toAnnotated))
    (fun X => ?_))) ?_
  · show AnnotatedRelation.dedupAnn (_ + ((AggQueryIn.Sel falsePred (AggQueryIn.Hole n s)
      (SelOK.of_noAggAtom rfl)).evaluate d γ
        (E.assignHole s (X.map GenRow.ofAnnotated))).map GenRow.toAnnotated) = _
    rw [evaluate_selFalse_hole, Multiset.map_zero, add_zero]
  · rw [muFix_eq_of_fix (j := 1) rfl]
    rfl

/-- **And it settles**, at its second round. -/
theorem annSettlesAt_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (h : q.AnnSettlesAt d γ E) :
    (dedupMu s q).AnnSettlesAt d γ E := by
  refine ⟨h, ⟨1, ?_⟩, fun _ => trivial⟩
  rw [muSetStep_dedupMu]
  rfl

/-! ## The pass -/

/-- Every `ε` replaced by the set recursion under a fresh name, the
supply split in three at each node. -/
def dedupFree (f : ℕ → String) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → AggQueryIn T c n κ l
  | _, _, _, _, .Rel n s => .Rel n s
  | _, _, _, _, .Hole n s κ => .Hole n s κ
  | _, _, _, _, .Param pv ρ => .Param pv ρ
  | _, _, _, _, .Empty => .Empty
  | _, _, _, _, .Proj ps q => .Proj ps (dedupFree f q)
  | _, _, _, _, .Sel φ q hφ => .Sel φ (dedupFree f q) hφ
  | _, _, _, _, .Prod q₁ q₂ =>
      .Prod (dedupFree (AggQueryIn.tri f 1) q₁) (dedupFree (AggQueryIn.tri f 2) q₂)
  | _, _, _, _, .Apply q₁ q₂ =>
      .Apply (dedupFree (AggQueryIn.tri f 1) q₁) (dedupFree (AggQueryIn.tri f 2) q₂)
  | _, _, _, _, .Sum q₁ q₂ =>
      .Sum (dedupFree (AggQueryIn.tri f 1) q₁) (dedupFree (AggQueryIn.tri f 2) q₂)
  | _, _, _, _, .Dedup q => dedupMu (f 0) (dedupFree (AggQueryIn.tri f 1) q)
  | _, _, _, _, .Diff q₁ q₂ =>
      .Diff (dedupFree (AggQueryIn.tri f 1) q₁) (dedupFree (AggQueryIn.tri f 2) q₂)
  | _, _, _, _, .Explode k h q => .Explode k h (dedupFree f q)
  | _, _, _, _, .Retag h q => .Retag h (dedupFree f q)
  | _, _, _, _, .Mu s q₀ q₁ =>
      .Mu s (dedupFree (AggQueryIn.tri f 1) q₀) (dedupFree (AggQueryIn.tri f 2) q₁)
  | _, _, _, _, .MuSet s q₀ q₁ =>
      .MuSet s (dedupFree (AggQueryIn.tri f 1) q₀) (dedupFree (AggQueryIn.tri f 2) q₁)
  | _, _, _, _, .Gamma (lab := lab) is ts fs q keep ord =>
      .Gamma (lab := lab) is ts fs (dedupFree f q) keep ord
  | _, _, _, _, .GammaScalar (lab := lab) ts fs q ord =>
      .GammaScalar (lab := lab) ts fs (dedupFree f q) ord
  | _, _, _, _, .GammaNest (lab := lab) is his p g q =>
      .GammaNest (lab := lab) is his p g (dedupFree f q)
  | _, _, _, _, .ProvSum is his t q => .ProvSum is his t (dedupFree f q)
  | _, _, _, _, .GammaTok (lab := lab) is his ts fs a q keep =>
      .GammaTok (lab := lab) is his ts fs a (dedupFree f q) keep
  | _, _, _, _, .Win (lab := lab) P O o w t g q hrr dist keep =>
      .Win (lab := lab) P O o w t g (dedupFree f q) hrr dist keep
  | _, _, _, _, .WinExpr (lab := lab) P O o ws ts fs g q keeps =>
      .WinExpr (lab := lab) P O o ws ts fs g (dedupFree f q) keeps

/-- **The pass changes no annotated evaluation.** -/
theorem evaluate_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K),
      (dedupFree f q).evaluate d γ E = q.evaluate d γ E := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ _ => rfl
  | Hole _ _ _ => exact fun _ _ _ _ => rfl
  | Param pv ρ => exact fun _ _ _ _ => rfl
  | Empty => exact fun _ _ _ _ => rfl
  | Proj ps q ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Sel φ q hφ ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Prod q₁ q₂ ih₁ ih₂ => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Apply q₁ q₂ ih₁ ih₂ => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Sum q₁ q₂ ih₁ ih₂ => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Dedup q ih =>
    intro f d γ E
    rw [dedupFree, evaluate_dedupMu, AggQueryIn.evaluate, AggQueryIn.evaluate, ih]
  | Diff q₁ q₂ ih₁ ih₂ => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Explode k hk q ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Retag hk q ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Mu s q₀ q₁ ih₀ ih₁ => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih₀, ih₁]
  | Gamma is ts fs q keep ord ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | GammaScalar ts fs q ord ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | GammaNest is his p g q ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | ProvSum is his t q ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | GammaTok is his ts fs a q keep ih => intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate,
        ih]
  | Win P O o w t g q hrr dist keep ih =>
    intro f d γ E; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro f d γ E
    simp only [dedupFree, AggQueryIn.evaluate]
    rw [ih]

theorem evaluateAnnotated_dedupFree {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (f : ℕ → String) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    (dedupFree f q).evaluateAnnotated d γ E = q.evaluateAnnotated d γ E := by
  simp only [AggQueryIn.evaluateAnnotated, evaluate_dedupFree]

/-! ### Its plain readings -/

/-- `ε(q) = μ^∪s.(q, σ_false(s))` in the plain semantics too. -/
theorem evaluatePlain_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n))
    (D : Database T) (γ : Fin c → T) :
    (dedupMu s q).evaluatePlain D γ = (q.evaluatePlain D γ).dedup := by
  rw [dedupMu, AggQueryIn.evaluatePlain]
  have hz : ∀ X : Relation T n, (AggQueryIn.Sel (falsePred : GenPredIn T c (ColKind.allReg n))
      (AggQueryIn.Hole n s) (SelOK.of_noAggAtom rfl)).evaluatePlain (D.assign s X) γ = 0 :=
    fun X => Multiset.filter_eq_nil.mpr (fun u _ => holdsPlain_falsePred _ _)
  refine Eq.trans (muFix_congr (step' := fun _ => (q.evaluatePlain D γ).dedup)
    (fun X => ?_)) ?_
  · show (@HAdd.hAdd (Multiset (Tuple T n)) (Multiset (Tuple T n)) (Multiset (Tuple T n))
      instHAdd (q.evaluatePlain D γ) _).dedup = _
    rw [hz, add_zero]
  · rw [muFix_eq_of_fix (j := 1) rfl]
    rfl

theorem evaluatePlain_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) (D : Database T) (γ : Fin c → T),
      (dedupFree f q).evaluatePlain D γ = q.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ => rfl
  | Hole _ _ => exact fun _ _ _ => rfl
  | Param pv ρ => exact fun _ _ _ => rfl
  | Empty => exact fun _ _ _ => rfl
  | Proj ps q ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | Sel φ q hφ ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | Prod q₁ q₂ ih₁ ih₂ => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Sum q₁ q₂ ih₁ ih₂ => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Dedup q ih =>
    intro f D γ
    rw [dedupFree, evaluatePlain_dedupMu, ih, AggQueryIn.evaluatePlain]
  | Diff q₁ q₂ ih₁ ih₂ => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Explode k hk q ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | Retag hk q ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih₀, ih₁]
  | Gamma is ts fs q keep ord ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | GammaScalar ts fs q ord ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | GammaNest is his p g q ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | ProvSum is his t q ih => intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | GammaTok is his ts fs a q keep ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | Win P O o w t g q hrr dist keep ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.evaluatePlain, ih]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro f D γ
    simp only [dedupFree, AggQueryIn.evaluatePlain]
    rw [ih]

theorem stripAgg_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n)) :
    (dedupMu s q).stripAgg = dedupMu s q.stripAgg := by
  have hfa : (falsePred : GenPredIn T c (ColKind.allReg n)).hasAggAtom = false := rfl
  rw [dedupMu, dedupMu, AggQueryIn.stripAgg, AggQueryIn.stripAgg,
    ite_eq_right (by rw [hfa]; exact Bool.false_ne_true), AggQueryIn.stripAgg]

/-- And so does its stripped form. -/
theorem evaluatePlain_stripAgg_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) (D : Database T) (γ : Fin c → T),
      (dedupFree f q).stripAgg.evaluatePlain D γ = q.stripAgg.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ => rfl
  | Hole _ _ => exact fun _ _ _ => rfl
  | Param pv ρ => exact fun _ _ _ => rfl
  | Empty => exact fun _ _ _ => rfl
  | Proj ps q ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | Sel φ q hφ ih =>
    intro f D γ
    simp only [dedupFree, AggQueryIn.stripAgg]
    by_cases h : φ.hasAggAtom
    · rw [ite_eq_left h, ite_eq_left h, ih]
    · rw [ite_eq_right h, ite_eq_right h]
      simp only [AggQueryIn.evaluatePlain, ih]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Dedup q ih =>
    intro f D γ
    rw [dedupFree, stripAgg_dedupMu, evaluatePlain_dedupMu, ih, AggQueryIn.stripAgg,
      AggQueryIn.evaluatePlain]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, ih₁]
  | Explode k hk q ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | Retag hk q ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih₀, ih₁]
  | Gamma is ts fs q keep ord ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | GammaScalar ts fs q ord ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | GammaNest is his p g q ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | ProvSum is his t q ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | GammaTok is his ts fs a q keep ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | Win P O o w t g q hrr dist keep ih =>
    intro f D γ; simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain, ih]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro f D γ
    simp only [dedupFree, AggQueryIn.stripAgg, AggQueryIn.evaluatePlain]
    rw [ih]

/-- **The pass settles wherever the query does.** -/
theorem annSettlesAt_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K),
      q.AnnSettlesAt d γ E → (dedupFree f q).AnnSettlesAt d γ E := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ _ _ => trivial
  | Hole _ _ _ => exact fun _ _ _ _ _ => trivial
  | Param pv ρ => exact fun _ _ _ _ _ => trivial
  | Empty => exact fun _ _ _ _ _ => trivial
  | Proj ps q ih => exact fun f d γ E h => ih f d γ E h
  | Sel φ q hφ ih => exact fun f d γ E h => ih f d γ E h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun f d γ E h => ⟨ih₁ _ d γ E h.1, ih₂ _ d γ E h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro f d γ E h
    refine ⟨ih₁ _ d γ E h.1, fun x hx => ih₂ _ d _ _ (h.2 x ?_)⟩
    rw [evaluate_dedupFree] at hx
    exact hx
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f d γ E h => ⟨ih₁ _ d γ E h.1, ih₂ _ d γ E h.2⟩
  | Dedup q ih => exact fun f d γ E h => annSettlesAt_dedupMu _ _ d γ E (ih _ d γ E h)
  | Diff q₁ q₂ ih₁ ih₂ => exact fun f d γ E h => ⟨ih₁ _ d γ E h.1, ih₂ _ d γ E h.2⟩
  | Explode k hk q ih => exact fun f d γ E h => ih f d γ E h
  | Retag hk q ih => exact fun f d γ E h => ih f d γ E h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro f d γ E h
    obtain ⟨h₀, hz, hs, hk, hk0⟩ := h
    have hst : AggQueryIn.muStep s (dedupFree (AggQueryIn.tri f 2) q₁) d γ E
        = AggQueryIn.muStep s q₁ d γ E :=
      funext (fun X => by simp only [AggQueryIn.muStep, evaluate_dedupFree])
    have hb : (dedupFree (AggQueryIn.tri f 1) q₀).evaluate d γ E = q₀.evaluate d γ E :=
      evaluate_dedupFree _ _ d γ E
    show (AggQueryIn.Mu s (dedupFree (AggQueryIn.tri f 1) q₀)
      (dedupFree (AggQueryIn.tri f 2) q₁)).AnnSettlesAt d γ E
    refine ⟨ih₀ _ d γ E h₀, ?_, ?_, fun k => ?_, ?_⟩
    · rw [hst]; exact hz
    · rw [hst, hb]; exact hs
    · rw [hst, hb]; exact ih₁ _ _ γ _ (hk k)
    · exact ih₁ _ _ γ _ hk0
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f d γ E h
    obtain ⟨h₀, hs, hk⟩ := h
    have hst : AggQueryIn.muSetStep s (dedupFree (AggQueryIn.tri f 1) q₀)
        (dedupFree (AggQueryIn.tri f 2) q₁) d γ E = AggQueryIn.muSetStep s q₀ q₁ d γ E :=
      funext (fun X => by simp only [AggQueryIn.muSetStep, evaluateAnnotated_dedupFree])
    show (AggQueryIn.MuSet s (dedupFree (AggQueryIn.tri f 1) q₀)
      (dedupFree (AggQueryIn.tri f 2) q₁)).AnnSettlesAt d γ E
    refine ⟨ih₀ _ d γ E h₀, ?_, fun k => ?_⟩
    · rw [hst]; exact hs
    · rw [hst]; exact ih₁ _ _ γ _ (hk k)
  | Gamma is ts fs q keep ord ih => exact fun f d γ E h => ih f d γ E h
  | GammaScalar ts fs q ord ih => exact fun f d γ E h => ih f d γ E h
  | GammaNest is his p g q ih => exact fun f d γ E h => ih f d γ E h
  | ProvSum is his t q ih => exact fun f d γ E h => ih f d γ E h
  | GammaTok is his ts fs a q keep ih => exact fun f d γ E h => ih f d γ E h
  | Win P O o w t g q hrr dist keep ih => exact fun f d γ E h => ih f d γ E h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f d γ E h => ih f d γ E h

/-! ## What the pass keeps -/

/-- A class of the source other than `ε` is a class of the target. -/
theorem mem_diff_dedup {S : Set OpKind} {op : OpKind} (h : op ∈ S) (hne : op ≠ OpKind.dedup) :
    op ∈ S \ {OpKind.dedup} :=
  ⟨h, fun h' => hne (Set.mem_singleton_iff.mp h')⟩

theorem usesOnly_dedupFree {S : Set OpKind} (hsel : OpKind.sel ∈ S) (hmu : OpKind.muSet ∈ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), q.usesOnly S → (dedupFree f q).usesOnly (S \ {OpKind.dedup}) := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ h => h
  | Hole _ _ => exact fun _ h => h
  | Param pv ρ => exact fun _ h => ⟨mem_diff_dedup h.1 (by decide),
      mem_diff_dedup h.2.1 (by decide), mem_diff_dedup h.2.2 (by decide)⟩
  | Empty => exact fun _ h => mem_diff_dedup h (by decide)
  | Proj ps q ih => exact fun f h => ⟨⟨mem_diff_dedup h.1.1 (by decide), h.1.2⟩, ih f h.2⟩
  | Sel φ q hφ ih => exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih f h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih₁ _ h.2.1, ih₂ _ h.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih₁ _ h.2.1, ih₂ _ h.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih₁ _ h.2.1, ih₂ _ h.2.2⟩
  | Dedup q ih =>
    exact fun f h => ⟨mem_diff_dedup hmu (by decide), ih _ h.2,
      ⟨mem_diff_dedup hsel (by decide), trivial⟩⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih₁ _ h.2.1, ih₂ _ h.2.2⟩
  | Explode k hk q ih => exact fun f h => ih f h
  | Retag hk q ih => exact fun f h => ih f h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih₀ _ h.2.1, ih₁ _ h.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih₀ _ h.2.1, ih₁ _ h.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih f h.2⟩
  | GammaScalar ts fs q ord ih => exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih f h.2⟩
  | GammaNest is his p g q ih =>
    exact fun f h => ⟨⟨mem_diff_dedup h.1.1 (by decide), h.1.2⟩, ih f h.2⟩
  | ProvSum is his t q ih => exact fun _ h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun _ h => h.elim
  | Win P O o w t g q hrr dist keep ih =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih f h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih =>
    exact fun f h => ⟨mem_diff_dedup h.1 (by decide), ih f h.2⟩

theorem inSig_dedupFree {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), q.inSig Θ → (dedupFree f q).inSig Θ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ h => h
  | Hole _ _ => exact fun _ h => h
  | Param pv ρ => exact fun _ h => h
  | Empty => exact fun _ h => h
  | Proj ps q ih => exact fun f h => ⟨h.1, ih f h.2⟩
  | Sel φ q hφ ih => exact fun f h => ⟨h.1, ih f h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Dedup q ih => exact fun f h => ⟨ih _ h, rfl, trivial⟩
  | Diff q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Explode k hk q ih => exact fun f h => ih f h
  | Retag hk q ih => exact fun f h => ih f h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun f h => ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun f h => ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun f h => ⟨h.1, h.2.1, h.2.2.1, ih f h.2.2.2⟩
  | GammaScalar ts fs q ord ih => exact fun f h => ⟨h.1, h.2.1, ih f h.2.2⟩
  | GammaNest is his p g q ih => exact fun f h => ⟨h.1, h.2.1, ih f h.2.2⟩
  | ProvSum is his t q ih => exact fun _ h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun _ h => h.elim
  | Win P O o w t g q hrr dist keep ih => exact fun f h => ⟨h.1, h.2.1, h.2.2.1, ih f h.2.2.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ h => h.elim

theorem noExplode_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), q.noExplode → (dedupFree f q).noExplode := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ h => h
  | Hole _ _ => exact fun _ h => h
  | Param pv ρ => exact fun _ h => h
  | Empty => exact fun _ h => h
  | Proj ps q ih => exact fun f h => ih f h
  | Sel φ q hφ ih => exact fun f h => ih f h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Dedup q ih => exact fun f h => ⟨ih _ h, trivial⟩
  | Diff q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Explode k hk q ih => exact fun _ h => h.elim
  | Retag hk q ih => exact fun f h => ih f h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun f h => ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun f h => ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun f h => ih f h
  | GammaScalar ts fs q ord ih => exact fun f h => ih f h
  | GammaNest is his p g q ih => exact fun f h => ih f h
  | ProvSum is his t q ih => exact fun f h => ih f h
  | GammaTok is his ts fs a q keep ih => exact fun f h => ih f h
  | Win P O o w t g q hrr dist keep ih => exact fun f h => ih f h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f h => ih f h

theorem noMention_dedupFree {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), q.noMention s → (dedupFree f q).noMention s := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ h => h
  | Hole _ _ => exact fun _ h => h
  | Param pv ρ => exact fun _ h => h
  | Empty => exact fun _ h => h
  | Proj ps q ih => exact fun f h => ih f h
  | Sel φ q hφ ih => exact fun f h => ih f h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Dedup q ih => exact fun f h => ⟨ih _ h, trivial⟩
  | Diff q₁ q₂ ih₁ ih₂ => exact fun f h => ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Explode k hk q ih => exact fun f h => ih f h
  | Retag hk q ih => exact fun f h => ih f h
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun f h => ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun f h => ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun f h => ih f h
  | GammaScalar ts fs q ord ih => exact fun f h => ih f h
  | GammaNest is his p g q ih => exact fun f h => ih f h
  | ProvSum is his t q ih => exact fun f h => ih f h
  | GammaTok is his ts fs a q keep ih => exact fun f h => ih f h
  | Win P O o w t g q hrr dist keep ih => exact fun f h => ih f h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f h => ih f h

/-- A name of the pass's output is a name of the query or one of the supply. -/
theorem names_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) (x : String), x ∈ (dedupFree f q).names → x ∈ q.names ∨ ∃ i, x = f i := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ x h => Or.inl h
  | Hole _ _ => exact fun _ x h => Or.inl h
  | Param pv ρ => exact fun _ x h => Or.inl h
  | Empty => exact fun _ x h => Or.inl h
  | Proj ps q ih => exact fun f x h => ih f x h
  | Sel φ q hφ ih => exact fun f x h => ih f x h
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro f x h
    rcases Finset.mem_union.mp h with h | h
    · exact AggQueryIn.names_tri (ih₁ _ x h) Finset.subset_union_left
    · exact AggQueryIn.names_tri (ih₂ _ x h) Finset.subset_union_right
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro f x h
    rcases Finset.mem_union.mp h with h | h
    · exact AggQueryIn.names_tri (ih₁ _ x h) Finset.subset_union_left
    · exact AggQueryIn.names_tri (ih₂ _ x h) Finset.subset_union_right
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro f x h
    rcases Finset.mem_union.mp h with h | h
    · exact AggQueryIn.names_tri (ih₁ _ x h) Finset.subset_union_left
    · exact AggQueryIn.names_tri (ih₂ _ x h) Finset.subset_union_right
  | Dedup q ih =>
    intro f x h
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inr ⟨0, h⟩
    · rcases Finset.mem_union.mp h with h | h
      · exact AggQueryIn.names_tri (ih _ x h) (subset_refl _)
      · exact Or.inr ⟨0, Finset.mem_singleton.mp h⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro f x h
    rcases Finset.mem_union.mp h with h | h
    · exact AggQueryIn.names_tri (ih₁ _ x h) Finset.subset_union_left
    · exact AggQueryIn.names_tri (ih₂ _ x h) Finset.subset_union_right
  | Explode k hk q ih => exact fun f x h => ih f x h
  | Retag hk q ih => exact fun f x h => ih f x h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro f x h
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl h))
    · rcases Finset.mem_union.mp h with h | h
      · exact AggQueryIn.names_tri (ih₀ _ x h)
          (subset_trans Finset.subset_union_left (Finset.subset_insert _ _))
      · exact AggQueryIn.names_tri (ih₁ _ x h)
          (subset_trans Finset.subset_union_right (Finset.subset_insert _ _))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f x h
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl h))
    · rcases Finset.mem_union.mp h with h | h
      · exact AggQueryIn.names_tri (ih₀ _ x h)
          (subset_trans Finset.subset_union_left (Finset.subset_insert _ _))
      · exact AggQueryIn.names_tri (ih₁ _ x h)
          (subset_trans Finset.subset_union_right (Finset.subset_insert _ _))
  | Gamma is ts fs q keep ord ih => exact fun f x h => ih f x h
  | GammaScalar ts fs q ord ih => exact fun f x h => ih f x h
  | GammaNest is his p g q ih => exact fun f x h => ih f x h
  | ProvSum is his t q ih => exact fun f x h => ih f x h
  | GammaTok is his ts fs a q keep ih => exact fun f x h => ih f x h
  | Win P O o w t g q hrr dist keep ih => exact fun f x h => ih f x h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f x h => ih f x h

/-- **The pass is hygienic**: the fresh names are mentioned by no leaf. -/
theorem hygienic_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), Function.Injective f → (∀ i, f i ∉ q.names) → q.hygienic →
        (dedupFree f q).hygienic := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ h => h
  | Hole _ _ => exact fun _ _ _ h => h
  | Param pv ρ => exact fun _ _ _ h => h
  | Empty => exact fun _ _ _ h => h
  | Proj ps q ih => exact fun f hf hfr h => ih f hf hfr h
  | Sel φ q hφ ih => exact fun f hf hfr h => ih f hf hfr h
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun f hf hfr h => ⟨ih₁ _ (AggQueryIn.tri_injective hf 1)
      (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) h.1,
      ih₂ _ (AggQueryIn.tri_injective hf 2)
        (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun f hf hfr h => ⟨ih₁ _ (AggQueryIn.tri_injective hf 1)
      (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) h.1,
      ih₂ _ (AggQueryIn.tri_injective hf 2)
        (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun f hf hfr h => ⟨ih₁ _ (AggQueryIn.tri_injective hf 1)
      (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) h.1,
      ih₂ _ (AggQueryIn.tri_injective hf 2)
        (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) h.2⟩
  | Dedup q ih =>
    intro f hf hfr h
    have hnm : f 0 ∉ (dedupFree (AggQueryIn.tri f 1) q).names :=
      AggQueryIn.tri_notMem hf (j := 0) (j' := 1) (by decide) (by decide) (by decide)
        (fun x hx => names_dedupFree q _ x hx) hfr 0
    exact ⟨AggQueryIn.noMention_of_not_mem_names _ hnm, trivial,
      ih _ (AggQueryIn.tri_injective hf 1) (AggQueryIn.tri_fresh hfr (subset_refl _) 1) h, trivial⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun f hf hfr h => ⟨ih₁ _ (AggQueryIn.tri_injective hf 1)
      (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) h.1,
      ih₂ _ (AggQueryIn.tri_injective hf 2)
        (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) h.2⟩
  | Explode k hk q ih => exact fun f hf hfr h => ih f hf hfr h
  | Retag hk q ih => exact fun f hf hfr h => ih f hf hfr h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro f hf hfr h
    exact ⟨noMention_dedupFree q₀ _ h.1, noMention_dedupFree q₁ _ h.2.1,
      ih₀ _ (AggQueryIn.tri_injective hf 1) (AggQueryIn.tri_fresh hfr
        (subset_trans Finset.subset_union_left (Finset.subset_insert _ _)) 1) h.2.2.1,
      ih₁ _ (AggQueryIn.tri_injective hf 2) (AggQueryIn.tri_fresh hfr
        (subset_trans Finset.subset_union_right (Finset.subset_insert _ _)) 2) h.2.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f hf hfr h
    exact ⟨noMention_dedupFree q₀ _ h.1, noMention_dedupFree q₁ _ h.2.1,
      ih₀ _ (AggQueryIn.tri_injective hf 1) (AggQueryIn.tri_fresh hfr
        (subset_trans Finset.subset_union_left (Finset.subset_insert _ _)) 1) h.2.2.1,
      ih₁ _ (AggQueryIn.tri_injective hf 2) (AggQueryIn.tri_fresh hfr
        (subset_trans Finset.subset_union_right (Finset.subset_insert _ _)) 2) h.2.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun f hf hfr h => ih f hf hfr h
  | GammaScalar ts fs q ord ih => exact fun f hf hfr h => ih f hf hfr h
  | GammaNest is his p g q ih => exact fun f hf hfr h => ih f hf hfr h
  | ProvSum is his t q ih => exact fun f hf hfr h => ih f hf hfr h
  | GammaTok is his ts fs a q keep ih => exact fun f hf hfr h => ih f hf hfr h
  | Win P O o w t g q hrr dist keep ih => exact fun f hf hfr h => ih f hf hfr h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f hf hfr h => ih f hf hfr h

/-- **The pass is well-formed over any schema declaring none of the fresh
names.** -/
theorem overSchema_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), (∀ i, f i ∉ q.names) → ∀ sch : Schema, (∀ i, sch (f i) = none) →
        q.overSchema sch → (dedupFree f q).overSchema sch := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ _ h => h
  | Hole _ _ => exact fun _ _ _ _ h => h
  | Param pv ρ => exact fun _ _ _ _ h => h
  | Empty => exact fun _ _ _ _ h => h
  | Proj ps q ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | Sel φ q hφ ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun f hfr sch hsch h =>
      ⟨ih₁ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) sch
          (AggQueryIn.sch_tri hsch 1) h.1,
        ih₂ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) sch
          (AggQueryIn.sch_tri hsch 2) h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun f hfr sch hsch h =>
      ⟨ih₁ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) sch
          (AggQueryIn.sch_tri hsch 1) h.1,
        ih₂ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) sch
          (AggQueryIn.sch_tri hsch 2) h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun f hfr sch hsch h =>
      ⟨ih₁ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) sch
          (AggQueryIn.sch_tri hsch 1) h.1,
        ih₂ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) sch
          (AggQueryIn.sch_tri hsch 2) h.2⟩
  | Dedup q ih =>
    rename_i c' m
    intro f hfr sch hsch h
    refine ⟨hsch 0,
      ih _ (AggQueryIn.tri_fresh hfr (subset_refl _) 1) sch (AggQueryIn.sch_tri hsch 1) h,
      trivial, ?_⟩
    show (sch.update (f 0) m) (f 0) = some m
    rw [Schema.update_apply, ite_eq_left rfl]
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun f hfr sch hsch h =>
      ⟨ih₁ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_left 1) sch
          (AggQueryIn.sch_tri hsch 1) h.1,
        ih₂ _ (AggQueryIn.tri_fresh hfr Finset.subset_union_right 2) sch
          (AggQueryIn.sch_tri hsch 2) h.2⟩
  | Explode k hk q ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | Retag hk q ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m _
    intro f hfr sch hsch h
    refine ⟨h.1, ih₀ _ (AggQueryIn.tri_fresh hfr
        (subset_trans Finset.subset_union_left (Finset.subset_insert _ _)) 1) sch
        (AggQueryIn.sch_tri hsch 1) h.2.1,
      noMention_dedupFree q₁ _ h.2.2.1, ?_⟩
    refine ih₁ _ (AggQueryIn.tri_fresh hfr
      (subset_trans Finset.subset_union_right (Finset.subset_insert _ _)) 2) (sch.update s m)
      ?_ h.2.2.2
    exact AggQueryIn.update_fresh (AggQueryIn.sch_tri hsch 2)
      (AggQueryIn.ne_tri (AggQueryIn.ne_of_mem_names hfr (Finset.mem_insert_self _ _)) 2)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro f hfr sch hsch h
    refine ⟨h.1, ih₀ _ (AggQueryIn.tri_fresh hfr
        (subset_trans Finset.subset_union_left (Finset.subset_insert _ _)) 1) sch
        (AggQueryIn.sch_tri hsch 1) h.2.1,
      noMention_dedupFree q₁ _ h.2.2.1, ?_⟩
    refine ih₁ _ (AggQueryIn.tri_fresh hfr
      (subset_trans Finset.subset_union_right (Finset.subset_insert _ _)) 2) (sch.update s m)
      ?_ h.2.2.2
    exact AggQueryIn.update_fresh (AggQueryIn.sch_tri hsch 2)
      (AggQueryIn.ne_tri (AggQueryIn.ne_of_mem_names hfr (Finset.mem_insert_self _ _)) 2)
  | Gamma is ts fs q keep ord ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | GammaScalar ts fs q ord ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | GammaNest is his p g q ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | ProvSum is his t q ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | GammaTok is his ts fs a q keep ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | Win P O o w t g q hrr dist keep ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f hfr sch hsch h => ih f hfr sch hsch h

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The pass keeps the query well-kinded**: the set recursion reads its
round through a regular hole. -/
theorem wellKinded_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) {ρc : Fin c → ColKind} {HK : HoleKinds},
      q.wellKinded ρc HK → (dedupFree f q).wellKinded ρc HK := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intro _ _ _ h; exact h
  | Hole _ _ _ => intro _ _ _ h; exact h
  | Param _ _ => intro _ _ _ h; exact h
  | Empty => intro _ _ _ h; exact h
  | Proj ps q ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩
  | Sel φ q hφ ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => intro f _ _ h; exact ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => intro f _ _ h; exact ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => intro f _ _ h; exact ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Dedup q ih =>
    intro f ρc HK h
    refine ⟨ih _ h, ⟨trivial, trivial⟩, fun k => ?_⟩
    simp [HoleKinds.assign]
  | Diff q₁ q₂ ih₁ ih₂ => intro f _ _ h; exact ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | Explode k hk q ih => intro f _ _ h; exact ih f h
  | Retag hk q ih => intro f _ _ h; exact ih f h
  | Mu s q₀ q₁ ih₀ ih₁ => intro f _ _ h; exact ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => intro f _ _ h; exact ⟨ih₀ _ h.1, ih₁ _ h.2⟩
  | Gamma is ts fs q keep ord ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩
  | GammaScalar ts fs q ord ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩
  | GammaNest is his p g q ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩
  | ProvSum is his t q ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩
  | GammaTok is his ts fs a q keep ih => intro f _ _ h; exact ⟨h.1, h.2.1, ih f h.2.2⟩
  | Win P O o w t g q hrr dist keep ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => intro f _ _ h; exact ⟨h.1, ih f h.2⟩

/-! ## The sufficient half: `ε` is dispensable -/

/-- **The classes other than `ε` generate the annotated algebra**, over
every schema and every commutative m-semiring: each `ε` is the set
recursion `μ^∪s.(q, σ_false(s))` under a fresh name, which reads exactly
as `ε(q)` does and always settles. -/
theorem generatesAnn_dedupFree (sch : Schema) (cnt : SeqAggFunc T) :
    GeneratesAnn T K sch cnt (plainRecOps \ {OpKind.dedup}) := by
  intro n κ q ho hu hi ha hp
  obtain ⟨f, hf, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch q.names
  refine ⟨dedupFree f q, overSchema_dedupFree q f hfr sch hfsch ho,
    usesOnly_dedupFree (by simp [plainRecOps, plainOps, basisDD, basisOps])
      (by simp [plainRecOps]) q f hu,
    inSig_dedupFree q f hi, noExplode_dedupFree q f ha, wellKinded_dedupFree q f hp, fun d γ hs =>
      ⟨annSettlesAt_dedupFree q f d γ {} hs, evaluateAnnotated_dedupFree q f d γ {}⟩⟩
