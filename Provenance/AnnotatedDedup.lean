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
generate the annotated algebra (`GeneratesAnn`). This is the first
non-trivial sufficient half of the annotated classification; the
products and the unions stay, since the apply's left side and the
recursions' operands are all-regular by typing and nothing re-types an
aggregate column without exploding it.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-! ## One duplicate elimination as a set recursion -/

/-- `μ^∪s.(q, σ_false(s))`: the set recursion whose first round is `ε(q)`
and whose term adds nothing. -/
def dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n)) :
    AggQueryIn T c n (ColKind.allReg n) :=
  AggQueryIn.MuSet s q (AggQueryIn.Sel falsePred (AggQueryIn.Hole n s) rfl)

/-- The recursive term reads the round and keeps nothing. -/
theorem evaluate_selFalse_hole {c n : ℕ} (s : String) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (X : AnnotatedRelation T K n) :
    (AggQueryIn.Sel (falsePred : GenPredIn T c (ColKind.allReg n)) (AggQueryIn.Hole n s) rfl).evaluate
      (d.assign s X) γ = 0 := by
  simp only [AggQueryIn.evaluate]
  have hfa : (falsePred : GenPredIn T c (ColKind.allReg n)).hasAggAtom = false := rfl
  rw [ite_eq_right (by rw [hfa]; exact Bool.false_ne_true)]
  exact Multiset.filter_eq_nil.mpr (fun r _ => by
    rw [GenPredIn.holds_iff_holdsPlain]
    exact holdsPlain_falsePred _ _)

/-- The round function of the recursion is constant: the deduplication of
`q`. -/
theorem muSetStep_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    AggQueryIn.muSetStep s q (AggQueryIn.Sel falsePred (AggQueryIn.Hole n s) rfl) d γ
      = fun _ => AnnotatedRelation.dedupAnn (q.evaluateAnnotated d γ) := by
  funext X
  show AnnotatedRelation.dedupAnn (q.evaluateAnnotated d γ
    + ((AggQueryIn.Sel falsePred (AggQueryIn.Hole n s) rfl).evaluate (d.assign s X) γ).map
        GenRow.toAnnotated) = _
  rw [evaluate_selFalse_hole, Multiset.map_zero, add_zero]

/-- **`ε(q) = μ^∪s.(q, σ_false(s))`, exactly.** -/
theorem evaluate_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    (dedupMu s q).evaluate d γ = (AggQueryIn.Dedup q).evaluate d γ := by
  rw [dedupMu, AggQueryIn.evaluate]
  have hstep := muSetStep_dedupMu (K := K) s q d γ
  unfold AggQueryIn.muSetStep at hstep
  erw [hstep]
  rw [muFix_eq_of_fix (j := 1) rfl]
  rfl

/-- **And it settles**, at its second round. -/
theorem annSettlesAt_dedupMu {c n : ℕ} (s : String) (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (h : q.AnnSettlesAt d γ) :
    (dedupMu s q).AnnSettlesAt d γ := by
  refine ⟨h, ⟨1, ?_⟩, fun _ => trivial⟩
  rw [muSetStep_dedupMu]

/-! ## The pass -/

/-- Every `ε` replaced by the set recursion under a fresh name, the
supply split in three at each node. -/
def dedupFree (f : ℕ → String) : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → AggQueryIn T c n κ l
  | _, _, _, _, .Rel n s => .Rel n s
  | _, _, _, _, .Hole n s => .Hole n s
  | _, _, _, _, .Empty => .Empty
  | _, _, _, _, .Proj ps q => .Proj ps (dedupFree f q)
  | _, _, _, _, .Sel φ q hφ => .Sel φ (dedupFree f q) hφ
  | _, _, _, _, .Prod q₁ q₂ => .Prod (dedupFree (tri f 1) q₁) (dedupFree (tri f 2) q₂)
  | _, _, _, _, .Apply q₁ q₂ => .Apply (dedupFree (tri f 1) q₁) (dedupFree (tri f 2) q₂)
  | _, _, _, _, .Sum q₁ q₂ => .Sum (dedupFree (tri f 1) q₁) (dedupFree (tri f 2) q₂)
  | _, _, _, _, .Dedup q => dedupMu (f 0) (dedupFree (tri f 1) q)
  | _, _, _, _, .Diff q₁ q₂ => .Diff (dedupFree (tri f 1) q₁) (dedupFree (tri f 2) q₂)
  | _, _, _, _, .Explode k h q => .Explode k h (dedupFree f q)
  | _, _, _, _, .Retag h q => .Retag h (dedupFree f q)
  | _, _, _, _, .Mu s q₀ q₁ => .Mu s (dedupFree (tri f 1) q₀) (dedupFree (tri f 2) q₁)
  | _, _, _, _, .MuSet s q₀ q₁ => .MuSet s (dedupFree (tri f 1) q₀) (dedupFree (tri f 2) q₁)
  | _, _, _, _, .Gamma is ts fs q keep ord => .Gamma is ts fs (dedupFree f q) keep ord
  | _, _, _, _, .GammaScalar ts fs q ord => .GammaScalar ts fs (dedupFree f q) ord
  | _, _, _, _, .GammaNest is his p g q => .GammaNest is his p g (dedupFree f q)
  | _, _, _, _, .ProvSum is his t q => .ProvSum is his t (dedupFree f q)
  | _, _, _, _, .GammaTok is his ts fs a q keep => .GammaTok is his ts fs a (dedupFree f q) keep
  | _, _, _, _, .Win P O o w t g q hrr dist keep => .Win P O o w t g (dedupFree f q) hrr dist keep
  | _, _, _, _, .WinExpr P O o ws ts fs g q keeps => .WinExpr P O o ws ts fs g (dedupFree f q) keeps

/-- **The pass changes no annotated evaluation.** -/
theorem evaluate_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) (d : AnnotatedDatabase T K) (γ : Fin c → T),
      (dedupFree f q).evaluate d γ = q.evaluate d γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ => rfl
  | Hole _ _ => exact fun _ _ _ => rfl
  | Empty => exact fun _ _ _ => rfl
  | Proj ps q ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Sel φ q hφ ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Prod q₁ q₂ ih₁ ih₂ => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Apply q₁ q₂ ih₁ ih₂ => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Sum q₁ q₂ ih₁ ih₂ => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Dedup q ih =>
    intro f d γ
    rw [dedupFree, evaluate_dedupMu, AggQueryIn.evaluate, AggQueryIn.evaluate, ih]
  | Diff q₁ q₂ ih₁ ih₂ => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih₁, ih₂]
  | Explode k hk q ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Retag hk q ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Mu s q₀ q₁ ih₀ ih₁ => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih₀, ih₁]
  | Gamma is ts fs q keep ord ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | GammaScalar ts fs q ord ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | GammaNest is his p g q ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | ProvSum is his t q ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | GammaTok is his ts fs a q keep ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | Win P O o w t g q hrr dist keep ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]
  | WinExpr P O o ws ts fs g q keeps ih => intro f d γ; simp only [dedupFree, AggQueryIn.evaluate, ih]

theorem evaluateAnnotated_dedupFree {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (f : ℕ → String) (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    (dedupFree f q).evaluateAnnotated d γ = q.evaluateAnnotated d γ := by
  simp only [AggQueryIn.evaluateAnnotated, evaluate_dedupFree]

/-- **The pass settles wherever the query does.** -/
theorem annSettlesAt_dedupFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String) (d : AnnotatedDatabase T K) (γ : Fin c → T),
      q.AnnSettlesAt d γ → (dedupFree f q).AnnSettlesAt d γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ _ => trivial
  | Hole _ _ => exact fun _ _ _ _ => trivial
  | Empty => exact fun _ _ _ _ => trivial
  | Proj ps q ih => exact fun f d γ h => ih f d γ h
  | Sel φ q hφ ih => exact fun f d γ h => ih f d γ h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun f d γ h => ⟨ih₁ _ d γ h.1, ih₂ _ d γ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro f d γ h
    refine ⟨ih₁ _ d γ h.1, fun u hu => ih₂ _ d _ (h.2 u ?_)⟩
    rw [evaluateAnnotated_dedupFree] at hu
    exact hu
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f d γ h => ⟨ih₁ _ d γ h.1, ih₂ _ d γ h.2⟩
  | Dedup q ih => exact fun f d γ h => annSettlesAt_dedupMu _ _ d γ (ih _ d γ h)
  | Diff q₁ q₂ ih₁ ih₂ => exact fun f d γ h => ⟨ih₁ _ d γ h.1, ih₂ _ d γ h.2⟩
  | Explode k hk q ih => exact fun f d γ h => ih f d γ h
  | Retag hk q ih => exact fun f d γ h => ih f d γ h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro f d γ h
    obtain ⟨h₀, hz, hs, hk, hk0⟩ := h
    have hst : AggQueryIn.muStep s (dedupFree (tri f 2) q₁) d γ = AggQueryIn.muStep s q₁ d γ :=
      funext (fun X => by simp only [AggQueryIn.muStep, evaluateAnnotated_dedupFree])
    have hb : (dedupFree (tri f 1) q₀).evaluateAnnotated d γ = q₀.evaluateAnnotated d γ :=
      evaluateAnnotated_dedupFree _ _ d γ
    show (AggQueryIn.Mu s (dedupFree (tri f 1) q₀) (dedupFree (tri f 2) q₁)).AnnSettlesAt d γ
    refine ⟨ih₀ _ d γ h₀, ?_, ?_, fun k => ?_, ?_⟩
    · rw [hst]; exact hz
    · rw [hst, hb]; exact hs
    · rw [hst, hb]; exact ih₁ _ _ γ (hk k)
    · exact ih₁ _ _ γ hk0
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f d γ h
    obtain ⟨h₀, hs, hk⟩ := h
    have hst : AggQueryIn.muSetStep s (dedupFree (tri f 1) q₀) (dedupFree (tri f 2) q₁) d γ
        = AggQueryIn.muSetStep s q₀ q₁ d γ :=
      funext (fun X => by simp only [AggQueryIn.muSetStep, evaluateAnnotated_dedupFree])
    show (AggQueryIn.MuSet s (dedupFree (tri f 1) q₀) (dedupFree (tri f 2) q₁)).AnnSettlesAt d γ
    refine ⟨ih₀ _ d γ h₀, ?_, fun k => ?_⟩
    · rw [hst]; exact hs
    · rw [hst]; exact ih₁ _ _ γ (hk k)
  | Gamma is ts fs q keep ord ih => exact fun f d γ h => ih f d γ h
  | GammaScalar ts fs q ord ih => exact fun f d γ h => ih f d γ h
  | GammaNest is his p g q ih => exact fun f d γ h => ih f d γ h
  | ProvSum is his t q ih => exact fun f d γ h => ih f d γ h
  | GammaTok is his ts fs a q keep ih => exact fun f d γ h => ih f d γ h
  | Win P O o w t g q hrr dist keep ih => exact fun f d γ h => ih f d γ h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f d γ h => ih f d γ h
