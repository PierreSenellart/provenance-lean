/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryToAgg
import Provenance.HavingJoinCompositional

/-!
# The compositional JOIN rewriting, on the general syntax

The `HAVING COUNT(*)` site of the compositional rewriting theorem is, in
the general syntax, the key projection of `σ_ψ ∘ Gamma` – all-regular,
since the projection drops the token columns – so it composes under every
operator of the general syntax, and the ProvSQL-legal contexts around a
site are exactly the expressible ones. `GenCountHavingRewrite` replaces
such sites by the embedded padded join query (`Query.toAgg`, from
`Provenance.QueryToAgg`), and
`GenCountHavingRewrite.evaluateGen_eq` proves the replacement preserves
the general evaluator's rows verbatim, in absorptive m-semirings whose
`⊗` distributes over `⊖`. The expressible contexts around a site are
exactly the ProvSQL-legal ones: the kind discipline forbids
deduplicating, differencing or re-grouping aggregate values, matching
the system.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

section GenRewrite

variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- A tuple with no token column has no token annotation lists. -/
theorem tokenLists_eq_zero {n : ℕ} {u : Tuple (GenValue T K) n}
    (h : ∀ k, ∃ v, u k = Sum.inl v) : tokenLists u = 0 := by
  refine Multiset.eq_zero_of_forall_notMem (fun l hl => ?_)
  obtain ⟨k, -, hk⟩ := (Multiset.mem_filterMap _ _).mp hl
  obtain ⟨v, hv⟩ := h k
  rw [hv] at hk
  simp at hk

/-- A `HAVING COUNT(*) op (C + 1)` site on the general syntax: the fused
comparison over the grouping, projected to its group key – all-regular
output. -/
def genCountHavingSite (ts' : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ)
    (g : AggQuery ℕ 3 (ColKind.allReg 3)) : AggQuery ℕ 1 (ColKind.allReg 1) :=
  AggQuery.castKind (funext fun _ => rfl)
    (AggQuery.Proj
      (fun _ : Fin 1 => ProjCol.term
        ((Term.index (⟨0, by omega⟩ : Fin 1)).toGenKey 1))
      (AggQuery.Sel (GenPred.fusedCmp op (0 : Fin 1) (Term.const (C + 1)))
        (AggQuery.Gamma keyIdx ts' (fun _ => SeqAggFunc.count) g)))

omit [HasAltLinearOrder K] in
/-- A projection whose columns are all regular terms embeds each row:
the token lists of the output are empty, so the pending guards are all
cashed and the output annotation is the finalized input annotation. -/
theorem projTerm_row_eq {n m : ℕ} {κ : Fin n → ColKind}
    (ps : Tuple (ProjCol T κ) m) (hps : ∀ j, ∃ t, ps j = ProjCol.term t)
    (r : GenRow T K n) :
    ((fun j => (ps j).eval r.fst),
      (⟨r.snd.base * ((r.snd.pending - r.snd.pending ∩
          tokenLists (fun j => (ps j).eval r.fst)).map
          (fun l => SemiringWithMonus.delta l.sum)).prod,
        r.snd.pending ∩ tokenLists (fun j => (ps j).eval r.fst)⟩ : GenAnn K))
      = GenRow.ofAnnotated
          ((fun j => AggValue.collapseSum ((ps j).eval r.fst)),
            r.snd.finalize) := by
  have hTL : tokenLists (fun j => (ps j).eval r.fst) = (0 : Multiset (List K)) := by
    refine tokenLists_eq_zero (fun k => ?_)
    obtain ⟨t, ht⟩ := hps k
    exact ⟨t.eval r.fst, by rw [ht]; rfl⟩
  refine Prod.ext ?_ ?_
  · funext j
    obtain ⟨t, ht⟩ := hps j
    show (ps j).eval r.fst
      = Sum.inl (AggValue.collapseSum ((ps j).eval r.fst))
    rw [ht]
    rfl
  · show (⟨r.snd.base * ((r.snd.pending - r.snd.pending ∩
        tokenLists (fun j => (ps j).eval r.fst)).map
        (fun l => SemiringWithMonus.delta l.sum)).prod,
      r.snd.pending ∩ tokenLists (fun j => (ps j).eval r.fst)⟩ : GenAnn K)
      = ⟨r.snd.finalize, 0⟩
    rw [hTL, Multiset.inter_zero, tsub_zero]
    rfl

/-- **Site correctness on the general syntax**: the general evaluator on
a `HAVING COUNT(*)` site produces exactly the rows of the embedded padded
join query – as raw evaluator rows, not just after finalization, since
the key projection empties the pending guards on one side and the
embedding image carries none on the other. -/
theorem genCountHavingSite_eval
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (ts' : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ)
    (g : AggQuery ℕ 3 (ColKind.allReg 3)) (q' : Query ℕ 3)
    (hq' : q'.source) (d : AnnotatedDatabase ℕ K)
    (hbridge : g.evaluateAnnotated d = q'.evaluateAnnotated hq' d)
    (hnodup : ((q'.evaluateAnnotated hq' d).map Prod.fst).Nodup) :
    (genCountHavingSite ts' op C g).evaluate d
      = ((joinCountQueryPadded q' op C).toAgg
          (joinCountQueryPadded_source q' hq' op C)).evaluate d := by
  rw [Query.toAgg_evaluate_eq,
    joinCountQueryPadded_correct h_abs h_distrib q' hq' d hnodup ts' op C,
    ← fused_key_proj g q' hq' d hbridge ts' op C]
  refine Eq.trans (Multiset.map_congr rfl (fun r _ =>
    projTerm_row_eq
      (fun _ : Fin 1 => ProjCol.term
        ((Term.index (⟨0, by omega⟩ : Fin 1)).toGenKey 1))
      (fun _ => ⟨_, rfl⟩) r)) ?_
  unfold AggQuery.evaluateAnnotated
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun r _ => rfl)

/-- **The JOIN rewriting on the general syntax**: congruence rules per
operator, and the site rule replacing a `HAVING COUNT(*)` site by the
embedded padded join query built over any classical query with the same
annotated semantics as the site's grouped subquery. -/
inductive GenCountHavingRewrite (d : AnnotatedDatabase ℕ K) :
    {n : ℕ} → {κ : Fin n → ColKind} →
    AggQuery ℕ n κ → AggQuery ℕ n κ → Prop
  | refl {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery ℕ n κ) :
      GenCountHavingRewrite d q q
  | proj {n m : ℕ} {κ : Fin n → ColKind} (ps : Tuple (ProjCol ℕ κ) m)
      {q q' : AggQuery ℕ n κ} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (AggQuery.Proj ps q) (AggQuery.Proj ps q')
  | sel {n : ℕ} {κ : Fin n → ColKind} (φ : GenPred ℕ κ)
      {q q' : AggQuery ℕ n κ} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (AggQuery.Sel φ q) (AggQuery.Sel φ q')
  | prod {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
      {q₁ q₁' : AggQuery ℕ n₁ κ₁} {q₂ q₂' : AggQuery ℕ n₂ κ₂} :
      GenCountHavingRewrite d q₁ q₁' → GenCountHavingRewrite d q₂ q₂' →
      GenCountHavingRewrite d (AggQuery.Prod q₁ q₂)
        (AggQuery.Prod q₁' q₂')
  | sum {n : ℕ} {κ : Fin n → ColKind} {q₁ q₁' q₂ q₂' : AggQuery ℕ n κ} :
      GenCountHavingRewrite d q₁ q₁' → GenCountHavingRewrite d q₂ q₂' →
      GenCountHavingRewrite d (AggQuery.Sum q₁ q₂)
        (AggQuery.Sum q₁' q₂')
  | dedup {n : ℕ} {q q' : AggQuery ℕ n (ColKind.allReg n)} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (AggQuery.Dedup q) (AggQuery.Dedup q')
  | diff {n : ℕ} {q₁ q₁' q₂ q₂' : AggQuery ℕ n (ColKind.allReg n)} :
      GenCountHavingRewrite d q₁ q₁' → GenCountHavingRewrite d q₂ q₂' →
      GenCountHavingRewrite d (AggQuery.Diff q₁ q₂)
        (AggQuery.Diff q₁' q₂')
  | gamma {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (Term ℕ m) n₂)
      (fs : Tuple (SeqAggFunc ℕ) n₂)
      {q q' : AggQuery ℕ m (ColKind.allReg m)} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (AggQuery.Gamma is ts fs q)
        (AggQuery.Gamma is ts fs q')
  | site (ts' : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ)
      {g g' : AggQuery ℕ 3 (ColKind.allReg 3)} (q' : Query ℕ 3)
      (hq' : q'.source) :
      GenCountHavingRewrite d g g' →
      g'.evaluateAnnotated d = q'.evaluateAnnotated hq' d →
      ((q'.evaluateAnnotated hq' d).map Prod.fst).Nodup →
      GenCountHavingRewrite d (genCountHavingSite ts' op C g)
        ((joinCountQueryPadded q' op C).toAgg
          (joinCountQueryPadded_source q' hq' op C))

/-- **Compositional correctness of the JOIN rewriting, general syntax**:
in an absorptive commutative m-semiring whose `⊗` distributes over `⊖`,
rewriting any number of `HAVING COUNT(*)` sites – wherever they occur –
preserves the general evaluator's rows verbatim. -/
theorem GenCountHavingRewrite.evaluateGen_eq
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    {d : AnnotatedDatabase ℕ K} :
    ∀ {n : ℕ} {κ : Fin n → ColKind} {q q' : AggQuery ℕ n κ},
      GenCountHavingRewrite d q q' →
      q.evaluate d = q'.evaluate d := by
  intro n κ q q' hrw
  induction hrw with
  | refl q => rfl
  | proj ps _ ih => simp only [AggQuery.evaluate]; rw [ih]
  | sel φ _ ih => simp only [AggQuery.evaluate]; rw [ih]
  | prod _ _ ih₁ ih₂ => simp only [AggQuery.evaluate]; rw [ih₁, ih₂]
  | sum _ _ ih₁ ih₂ => simp only [AggQuery.evaluate]; rw [ih₁, ih₂]
  | dedup _ ih => simp only [AggQuery.evaluate]; rw [ih]
  | diff _ _ ih₁ ih₂ => simp only [AggQuery.evaluate]; rw [ih₁, ih₂]
  | gamma is ts fs _ ih => simp only [AggQuery.evaluate]; rw [ih]
  | @site ts' op C g g' q' hq' _ hbridge hnodup ih =>
    have hbridge' : g.evaluateAnnotated d
        = q'.evaluateAnnotated hq' d := by
      unfold AggQuery.evaluateAnnotated
      rw [ih]
      exact hbridge
    exact genCountHavingSite_eval h_abs h_distrib ts' op C g q' hq' d
      hbridge' hnodup

/-- The finalized form of the compositional correctness. -/
theorem GenCountHavingRewrite.evaluateAnnotatedGen_eq
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    {d : AnnotatedDatabase ℕ K} {n : ℕ} {κ : Fin n → ColKind}
    {q q' : AggQuery ℕ n κ} (hrw : GenCountHavingRewrite d q q') :
    q.evaluateAnnotated d = q'.evaluateAnnotated d := by
  unfold AggQuery.evaluateAnnotated
  rw [hrw.evaluateGen_eq h_abs h_distrib]

end GenRewrite
