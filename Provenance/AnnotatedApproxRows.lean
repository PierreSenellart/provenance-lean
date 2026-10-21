/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.AnnotatedBasisClass
public import Provenance.AggQueryProbability
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Provenance.AnnotatedChains
import Provenance.AnnotatedEpsRow

/-!
# The necessity rows up to `≈`

Annotated results are compared up to `≈`: rows annotated `𝟘` are
dropped, and so are the occurrences annotated `𝟘` inside aggregate values.
`GeneratesAnnZ` is `GeneratesAnn` with that comparison in place of
equality, so a set generating up to `≈` need not reproduce the rows a
query annotates `𝟘`. This module proves the rows of the annotated basis
against it.

* The comparison (`GenRow.zeroNorm`) keeps the rows whose annotation is
  not `𝟘` and reads each aggregate column in the world of its occurrences
  annotated otherwise (`GenRow.zeroTuple`). It reads a token's value and
  not the token, so it is coarser than the comparison by occurrence
  identity (`GenRow.zeqRen`) on results that carry aggregate values:
  generating up to that one generates up to this one, and the rows below
  are the stronger statements.
* **The rows inherited from the plain basis** cannot go through the
  data part: a match may annotate `𝟘` rows the plain result does not
  hold. They go through the Boolean support instead. Over `𝔹` (`BoolNone`,
  Boolean functions of no variable) the rows `≈` keeps are the realized
  world of an evaluation, which is the plain evaluation of the realized
  world (`AggQueryIn.genRandomWorld_evaluate`), and an instance annotated
  `𝟙` realizes itself (`generatesAtNoExplode_of_generatesAnnZ`). It also
  needs the match to settle plainly on the realized world, which
  `AggQueryIn.settlesAt_randomWorld` proves from its annotated settling.
* **The scope** is the whole algebra, second-level aggregation at every
  storey included: the random-world theorem holds there, a nested world
  deciding each inner occurrence once.
* **The rows proved over `ℕ`, `ℕ × ℕ` and `ℕ[x, y]`** go through as they
  were: their witnesses' rows are annotated otherwise than `𝟘`, so `≈`
  keeps them (`GenRow.exists_finalize_of_zeroNorm`).

`annEpsOps_isBasis_in_class_approx` is the basis theorem up to `≈` over
the class `AnnBasisClass`, which holds `𝔹`, `ℕ` and `ℕ[x, y]`: the nine
classes generate (`generatesAnnZ_annEpsOps_of_class`, the constructions
agreeing with their source row by row up to finalization), and no proper
subset does (`annEpsOps_minimal_in_class_approx`).
-/

@[expose] public section

/-! ## Plain settling on the realized world -/

section RandomWorldSettles

variable {T : Type} [ValueType T]
variable {X : Type} [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)]

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
theorem GenRow.specializeTuple_append {n₁ n₂ : ℕ}
    (u₁ : Tuple (GenValue T (BoolFunc X)) n₁)
    (u₂ : Tuple (GenValue T (BoolFunc X)) n₂) (v : X → Bool) :
    GenRow.specializeTuple v (Fin.append u₁ u₂)
      = Fin.append (GenRow.specializeTuple v u₁) (GenRow.specializeTuple v u₂) := by
  funext k
  unfold GenRow.specializeTuple
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
theorem genRandomWorld_zero' {n : ℕ} (v : X → Bool) :
    genRandomWorld v (0 : Multiset (GenRow T (BoolFunc X) n)) = 0 := by
  unfold genRandomWorld; simp

/-- **A query settling in the annotated semantics settles plainly on the
world a valuation realizes**: its plain rounds are the realized worlds of
its annotated ones (`AggQueryIn.genRandomWorld_evaluate_env`). -/
theorem AggQueryIn.settlesAt_randomWorld_env :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noProvSum → q.hygienic → ∀ {ρc : Fin c → ColKind} {HK : HoleKinds},
      q.wellKinded ρc HK →
      ∀ (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool) {γ : Fin c → T}
        (E : EvalEnv T (BoolFunc X)) (D : Database T) (N : Set String),
      E.Kinded γ ρc HK → E.Guarded v →
      (∀ (n' : ℕ) (s' : String), s' ∉ N → D.find n' s' = (d.randomWorld v).find n' s') →
      (∀ s' ∈ N, q.noMention s') →
      (∀ p ∈ l, D.find p.2 p.1 = some (genRandomWorld v (E.holes p.1 p.2))) →
      q.AnnSettlesAt d γ E →
      q.SettlesAt D (GenRow.specializeTuple v (E.ctxAt c γ)) := by
  intro c n κ l q
  induction q with
  | Rel n s => intros; trivial
  | Hole n s κ => intros; trivial
  | Param pv ρ => intros; trivial
  | Empty => intros; trivial
  | Proj ps q ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk.2 d v E D N hE hG hD hN hH hr
  | Sel φ q _ ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk.2 d v E D N hE hG hD hN hH hr
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ⟨ih₁ hq.1 hh.1 hwk.1 d v E D N hE hG hD
        (fun s' h => (hN s' h).1) (fun p hp => hH p (List.mem_append_left _ hp)) hr.1,
      ih₂ hq.2 hh.2 hwk.2 d v E D N hE hG hD
        (fun s' h => (hN s' h).2) (fun p hp => hH p (List.mem_append_right _ hp)) hr.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    refine ⟨ih₁ hq.1 hh.1 hwk.1 d v E D N hE hG hD
      (fun s' h => (hN s' h).1) hH hr.1, fun u hu => ?_⟩
    have hL := AggQueryIn.genRandomWorld_evaluate_env q₁ hq.1 hh.1 hwk.1 d v E D N hE hG hD (fun s' h => (hN s' h).1)
            hH hr.1
    rw [← hL] at hu
    unfold genRandomWorld at hu
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hu
    obtain ⟨hxf, hfx⟩ := Multiset.mem_filter.1 hx
    have ih₂' := ih₂ hq.2 hh.2 hwk.2 d v _ D N
      (hE.enter (fun k => AggQueryIn.evaluate_conform q₁ d x hxf k))
      (hG.enter γ (fun k a ha =>
        AggQueryIn.evaluate_guarded q₁ d E x hxf v hG hfx k a ha))
      hD (fun s' h => (hN s' h).2) (fun p hp => absurd hp List.not_mem_nil) (hr.2 x hxf)
    rw [EvalEnv.ctxAt_withCtx, GenRow.specializeTuple_append] at ih₂'
    exact ih₂'
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ⟨ih₁ hq.1 hh.1 hwk.1 d v E D N hE hG hD
        (fun s' h => (hN s' h).1) (fun p hp => hH p (List.mem_append_left _ hp)) hr.1,
      ih₂ hq.2 hh.2 hwk.2 d v E D N hE hG hD
        (fun s' h => (hN s' h).2) (fun p hp => hH p (List.mem_append_right _ hp)) hr.2⟩
  | Dedup q ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk d v E D N hE hG hD hN hH
        hr
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ⟨ih₁ hq.1 hh.1 hwk.1 d v E D N hE hG hD
        (fun s' h => (hN s' h).1) (fun p hp => absurd hp List.not_mem_nil) hr.1,
      ih₂ hq.2 hh.2 hwk.2 d v E D N hE hG hD
        (fun s' h => (hN s' h).2) (fun p hp => absurd hp List.not_mem_nil) hr.2⟩
  | Explode k hk q ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk d v E D N hE hG hD hN hH hr
  | Retag h q ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk d v E D N hE hG hD hN hH hr
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m κ'
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    have hit : ∀ k, ∀ r ∈ (AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E),
        GenRow.Conforms κ' r.fst := by
      intro k
      induction k with
      | zero => exact fun r hr' k => AggQueryIn.evaluate_conform q₀ d r hr' k
      | succ k _ =>
        intro r hr'
        rw [Function.iterate_succ_apply'] at hr'
        exact fun k => AggQueryIn.evaluate_conform q₁ d r hr' k
    have hgit : ∀ k, ∀ r ∈ (AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E),
        r.snd.finalize v = true →
          ∀ (k' : Fin m) (a : AggTok T (BoolFunc X)), r.fst k' = Sum.inr a → a.Realized v := by
      intro k
      induction k with
      | zero => exact fun r hr' => AggQueryIn.evaluate_guarded q₀ d E r hr' v hG
      | succ k ihk =>
        intro r hr'
        rw [Function.iterate_succ_apply'] at hr'
        exact AggQueryIn.evaluate_guarded q₁ d _ r hr' v (hG.assignHole s ihk)
    have hbodyAt : ∀ (Y : Multiset (GenRow T (BoolFunc X) m)),
        (∀ r ∈ Y, GenRow.Conforms κ' r.fst) →
        (∀ r ∈ Y, r.snd.finalize v = true →
          ∀ (k' : Fin m) (a : AggTok T (BoolFunc X)), r.fst k' = Sum.inr a → a.Realized v) →
        q₁.AnnSettlesAt d γ (E.assignHole s Y) →
        genRandomWorld v (q₁.evaluate d γ (E.assignHole s Y))
          = q₁.evaluatePlain (D.assign s (genRandomWorld v Y))
              (GenRow.specializeTuple v (E.ctxAt _ γ))
          ∧ q₁.SettlesAt (D.assign s (genRandomWorld v Y))
              (GenRow.specializeTuple v (E.ctxAt _ γ)) := by
      intro Y hY hgY hrY
      have hDY := Database.agree_assign_rw hD s (genRandomWorld v Y)
      have hNY : ∀ s' ∈ insert s N, q₁.noMention s' := fun s' h =>
        (Set.mem_insert_iff.mp h).elim (fun he => he ▸ hh.2.1) (fun hn' => (hN s' hn').2)
      have hHY : ∀ p ∈ [(s, m)], (D.assign s (genRandomWorld v Y)).find p.2 p.1
          = some (genRandomWorld v ((E.assignHole s Y).holes p.1 p.2)) := fun p hp => by
        rw [List.mem_singleton.mp hp]
        show (D.assign s _).find m s = _
        rw [Database.find_assign, EvalEnv.assignHole_holes_self]
      exact ⟨AggQueryIn.genRandomWorld_evaluate_env q₁ hq.2 hh.2.2.2 hwk.2 d v
          (E.assignHole s Y) (D.assign s (genRandomWorld v Y)) (insert s N)
          (hE.assignHole s hY) (hG.assignHole s hgY) hDY hNY hHY hrY,
        ih₁ hq.2 hh.2.2.2 hwk.2 d v (E.assignHole s Y) (D.assign s (genRandomWorld v Y))
          (insert s N) (hE.assignHole s hY)
          (hG.assignHole s hgY) hDY hNY hHY hrY⟩
    have h₀ := AggQueryIn.genRandomWorld_evaluate_env q₀ hq.1 hh.2.2.1 hwk.1 d v E D N hE hG hD (fun s' h => (hN s' h).1)
      (fun p hp => absurd hp List.not_mem_nil) hr.1
    have hround : ∀ k, (fun X => q₁.evaluatePlain (D.assign s X)
          (GenRow.specializeTuple v (E.ctxAt _ γ)))^[k]
          (q₀.evaluatePlain D (GenRow.specializeTuple v (E.ctxAt _ γ)))
        = genRandomWorld v ((AggQueryIn.muStep s q₁ d γ E)^[k] (q₀.evaluate d γ E)) := by
      intro k
      induction k with
      | zero => exact h₀.symm
      | succ k ihk =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihk]
        exact ((hbodyAt _ (hit k) (hgit k) (hr.2.2.2.1 k)).1).symm
    have hz := hbodyAt 0 (fun r hr' => absurd hr' (Multiset.notMem_zero r))
      (fun r hr' => absurd hr' (Multiset.notMem_zero r)) hr.2.2.2.2
    refine ⟨ih₀ hq.1 hh.2.2.1 hwk.1 d v E D N hE hG hD
      (fun s' h => (hN s' h).1) (fun p hp => absurd hp List.not_mem_nil) hr.1, ?_, ?_,
      fun k => ?_⟩
    · have h1 := hz.1
      rw [genRandomWorld_zero'] at h1
      rw [← h1]
      show genRandomWorld v (AggQueryIn.muStep s q₁ d γ E 0) = 0
      rw [hr.2.1, genRandomWorld_zero']
    · obtain ⟨k, hk⟩ := hr.2.2.1
      refine ⟨k, ?_⟩
      erw [hround (k + 1), hk, genRandomWorld_zero']
    · erw [hround k]
      exact (hbodyAt _ (hit k) (hgit k) (hr.2.2.2.1 k)).2
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    have hbodyAt : ∀ k, (q₁.evaluate d γ (E.assignHole s
          ((muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k).map GenRow.ofAnnotated))
          |> genRandomWorld v)
          = q₁.evaluatePlain (D.assign s (_root_.randomWorld v
              (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)))
              (GenRow.specializeTuple v (E.ctxAt _ γ))
        ∧ q₁.SettlesAt (D.assign s (_root_.randomWorld v
              (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)))
              (GenRow.specializeTuple v (E.ctxAt _ γ)) := by
      intro k
      set Xk := muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k with hXk
      have hreg : ∀ r ∈ Xk.map GenRow.ofAnnotated, ∀ (j : Fin m) (a : AggTok T (BoolFunc X)),
          r.fst j = Sum.inr a → False := by
        intro r hr' j a ha
        obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr'
        exact absurd ha (by simp [GenRow.ofAnnotated])
      have hGk := hG.assignHole s (fun r hr' _ j a ha => (hreg r hr' j a ha).elim)
      have hDk := Database.agree_assign_rw hD s (_root_.randomWorld v Xk)
      have hNk' : ∀ s' ∈ insert s N, q₁.noMention s' := fun s' h =>
        (Set.mem_insert_iff.mp h).elim (fun he => he ▸ hh.2.1) (fun hn' => (hN s' hn').2)
      have hHk : ∀ p ∈ [(s, m)], (D.assign s (_root_.randomWorld v Xk)).find p.2 p.1
          = some (genRandomWorld v
              ((E.assignHole s (Xk.map GenRow.ofAnnotated)).holes p.1 p.2)) := fun p hp => by
        rw [List.mem_singleton.mp hp]
        show (D.assign s _).find m s = _
        rw [Database.find_assign, EvalEnv.assignHole_holes_self, genRandomWorld_ofAnnotated]
      exact ⟨AggQueryIn.genRandomWorld_evaluate_env q₁ hq.2 hh.2.2.2 hwk.2 d v
          (E.assignHole s (Xk.map GenRow.ofAnnotated)) (D.assign s (_root_.randomWorld v Xk))
          (insert s N) (hE.assignHole s (fun r hr' k => by
            obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hr'
            rfl)) hGk hDk hNk' hHk (hr.2.2 k),
        ih₁ hq.2 hh.2.2.2 hwk.2 d v (E.assignHole s (Xk.map GenRow.ofAnnotated))
          (D.assign s (_root_.randomWorld v Xk)) (insert s N) (hE.assignHole s (fun r hr' k => by
            obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hr'
            rfl)) hGk hDk hNk' hHk (hr.2.2 k)⟩
    have h₀ := AggQueryIn.genRandomWorld_evaluate_env q₀ hq.1 hh.2.2.1 hwk.1 d v E D N hE hG hD (fun s' h => (hN s' h).1)
      (fun p hp => absurd hp List.not_mem_nil) hr.1
    have hstep : ∀ k, _root_.randomWorld v (AggQueryIn.muSetStep s q₀ q₁ d γ E
          (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k))
        = (fun Y => (q₀.evaluatePlain D (GenRow.specializeTuple v (E.ctxAt _ γ))
            + q₁.evaluatePlain (D.assign s Y) (GenRow.specializeTuple v (E.ctxAt _ γ))).dedup)
          (_root_.randomWorld v (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k)) := by
      intro k
      show _root_.randomWorld v (AnnotatedRelation.dedupAnn (_ + _)) = _
      rw [AnnotatedRelation.dedupAnn, randomWorld_groupByKey, randomWorld_add,
        AggQueryIn.evaluateAnnotated, AggQueryIn.evaluateAnnotated,
        genRandomWorld_allReg, genRandomWorld_allReg, h₀, (hbodyAt k).1]
    have hiter : ∀ k, muIter (fun Y => (q₀.evaluatePlain D (GenRow.specializeTuple v (E.ctxAt _ γ))
            + q₁.evaluatePlain (D.assign s Y) (GenRow.specializeTuple v (E.ctxAt _ γ))).dedup) k
        = _root_.randomWorld v (muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ihk => rw [muIter, muIter, ihk, hstep]
    refine ⟨ih₀ hq.1 hh.2.2.1 hwk.1 d v E D N hE hG hD
      (fun s' h => (hN s' h).1) (fun p hp => absurd hp List.not_mem_nil) hr.1, ?_,
      fun k => ?_⟩
    · obtain ⟨j, hj⟩ := hr.2.1
      refine ⟨j, ?_⟩
      rw [← muIter_eq_iterate, ← muIter_eq_iterate, hiter, hiter]
      rw [← muIter_eq_iterate, ← muIter_eq_iterate] at hj
      rw [hj]
    · rw [hiter k]
      exact (hbodyAt k).2
  | Gamma is ts fs q keep ord ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk.2 d v E D N hE hG hD hN hH
        hr
  | GammaScalar ts fs q ord ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk.2 d v E D N hE hG hD hN hH
        hr
  | GammaNest is his p f q ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk.2 d v E D N hE hG hD hN hH hr
  | ProvSum is his t q ih => intro hq; exact hq.elim
  | GammaTok is his ts fs a q keep ih => intro hq; exact hq.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk.2 d v E D N hE hG hD hN hH
        hr
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro hq hh ρc HK hwk d v γ E D N hE hG hD hN hH hr
    exact ih hq hh hwk.2 d v E D N hE hG hD hN hH
        hr

end RandomWorldSettles

/-- The closed form: an empty environment. -/
theorem AggQueryIn.settlesAt_randomWorld {T : Type} [ValueType T] {X : Type} [Fintype X]
    [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (hq : q.noProvSum) (hh : q.hygienic)
    (hwk : q.wellKinded (ColKind.allReg c) HoleKinds.empty)
    (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool) {γ : Fin c → T}
    (hr : q.AnnSettlesAt d γ {}) : q.SettlesAt (d.randomWorld v) γ := by
  have h := q.settlesAt_randomWorld_env hq hh hwk d v {} (d.randomWorld v) ∅
    (EvalEnv.kinded_empty γ) (EvalEnv.guarded_empty v)
    (fun _ _ _ => rfl) (fun _ h => absurd h (Set.notMem_empty _))
    (fun p hp => absurd hp List.not_mem_nil) hr
  rw [EvalEnv.empty_ctxAt] at h
  exact h

/-! ## The comparison up to `≈` -/

section Approx

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-- **A row's tuple with the occurrences annotated `𝟘` dropped**: each
aggregate column read in the world of its occurrences annotated otherwise. -/
noncomputable def GenRow.zeroTuple {n : ℕ} (u : Tuple (GenValue T K) n) : Tuple T n :=
  fun k => _root_.Sum.elim id (fun a => a.specialize (fun x : K => decide (x ≠ 0))) (u k)

/-- **An evaluation up to `≈`**: its rows annotated otherwise than `𝟘`,
with the occurrences annotated `𝟘` dropped from their aggregate values. -/
noncomputable def GenRow.zeroNorm {n : ℕ} (R : Multiset (GenRow T K n)) : Multiset (AnnotatedTuple T K n) :=
  (R.filter (fun r => r.snd.finalize ≠ 0)).map
    (fun r => ((GenRow.zeroTuple r.fst, r.snd.finalize) : AnnotatedTuple T K n))

omit [HasAltLinearOrder K] in
/-- A row annotated otherwise than `𝟘` on one side has a row of the same
annotation on the other. -/
theorem GenRow.exists_finalize_of_zeroNorm {n : ℕ} {A B : Multiset (GenRow T K n)}
    (h : GenRow.zeroNorm A = GenRow.zeroNorm B) {r : GenRow T K n} (hr : r ∈ B)
    (hz : r.snd.finalize ≠ 0) : ∃ r' ∈ A, r'.snd.finalize = r.snd.finalize := by
  have hm : ((GenRow.zeroTuple r.fst, r.snd.finalize) : AnnotatedTuple T K n)
      ∈ GenRow.zeroNorm A := by
    rw [h]
    exact Multiset.mem_map_of_mem _ (Multiset.mem_filter.2 ⟨hr, hz⟩)
  obtain ⟨r', hr', he⟩ := Multiset.mem_map.1 hm
  exact ⟨r', Multiset.mem_of_mem_filter hr', congrArg Prod.snd he⟩

end Approx

/-- **A set of classes generates the annotated algebra up to `≈`**: every
query of the whole algebra in the minimal universe is matched over the
set, by a query of the same fragment, whose result agrees with the
source's up to `≈` wherever the source settles. The Boolean support of an
evaluation is the plain evaluation of the realized world
(`AggQueryIn.genRandomWorld_evaluate`), which is how the rows inherited
from the plain basis transfer. -/
def GeneratesAnnZ (T : Type) [ValueType T] (K : Type) [CommSemiringWithMonus K] [DecidableEq K]
    [HasAltLinearOrder K] (sch : Schema) (cnt : SeqAggFunc T) (S : Set OpKind) : Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ),
    q.overSchema sch → q.usesOnly plainRecOps → q.inMinimalSig cnt → q.noExplode →
      q.wellKinded (ColKind.allReg 0) HoleKinds.empty →
      ∃ q' : AggQuery T n κ,
        q'.overSchema sch ∧ q'.usesOnly S ∧ q'.inMinimalSig cnt ∧ q'.noExplode
          ∧ q'.wellKinded (ColKind.allReg 0) HoleKinds.empty
          ∧ ∀ (d : AnnotatedDatabase T K) (γ : Fin 0 → T), q.AnnSettlesAt d γ {} →
              q'.AnnSettlesAt d γ {}
                ∧ GenRow.zeroNorm (q'.evaluate d γ) = GenRow.zeroNorm (q.evaluate d γ)

/-! ## The inherited rows, through the Boolean support -/

section Boolean

variable {T : Type} [ValueType T]

/-- **`𝔹`, as Boolean functions of no variable**: `δ` is the identity, and
an annotation is `𝟘` exactly where it is false. -/
abbrev BoolNone := BoolFunc Empty

open Classical in
noncomputable instance : HasAltLinearOrder BoolNone := ⟨linearOrderOfSTO WellOrderingRel⟩

omit [ValueType T] in
theorem AggQueryIn.noProvSum_of_usesOnly {S : Set OpKind} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.noProvSum := by
  intro c n κ l q
  induction q <;> simp_all [AggQueryIn.usesOnly, AggQueryIn.noProvSum]

omit [ValueType T] in
theorem AnnotatedDatabase.randomWorld_liftOne {X : Type} (D : Database T) (v : X → Bool) :
    (D.liftOne (K := BoolFunc X)).randomWorld v = D := by
  unfold Database.liftOne AnnotatedDatabase.randomWorld
  rw [List.map_map]
  conv_rhs => rw [← List.map_id D]
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, id]
  congr
  unfold _root_.randomWorld Relation.liftOne
  rw [Multiset.filter_eq_self.mpr (fun p hp => by
    obtain ⟨u, -, rfl⟩ := Multiset.mem_map.1 hp; rfl), Multiset.map_map]
  exact Multiset.map_id' _

theorem boolNone_ne_zero_iff (f : BoolNone) : f ≠ 0 ↔ f Empty.elim = true := by
  constructor
  · intro h
    by_contra hf
    refine h (funext fun v => ?_)
    rw [Subsingleton.elim v Empty.elim, show (0 : BoolNone) Empty.elim = false from rfl]
    simpa using hf
  · intro h h0
    rw [h0] at h
    exact Bool.false_ne_true h

theorem zeroTuple_boolNone {n : ℕ} (u : Tuple (GenValue T BoolNone) n) :
    GenRow.zeroTuple u = GenRow.specializeTuple Empty.elim u := by
  funext k
  unfold GenRow.zeroTuple GenRow.specializeTuple GenValue.specializeAt
  cases u k with
  | inl w => rfl
  | inr a =>
    show a.specialize _ = a.specialize _
    congr 1
    funext x
    by_cases hx : x = 0
    · subst hx
      rw [show (0 : BoolNone) Empty.elim = false from rfl]
      simp
    · rw [decide_eq_true hx]
      exact ((boolNone_ne_zero_iff x).mp hx).symm

/-- **Over `𝔹`, an evaluation up to `≈` is its realized world.** -/
theorem zeroNorm_fst_boolNone {n : ℕ} (R : Multiset (GenRow T BoolNone n)) :
    (GenRow.zeroNorm R).map Prod.fst = genRandomWorld Empty.elim R := by
  unfold GenRow.zeroNorm genRandomWorld
  rw [Multiset.map_map]
  have hf : R.filter (fun r => r.snd.finalize ≠ 0)
      = R.filter (fun r => r.snd.finalize Empty.elim = true) :=
    Multiset.filter_congr fun r _ => boolNone_ne_zero_iff _
  rw [hf]
  refine Multiset.map_congr rfl fun r _ => ?_
  exact zeroTuple_boolNone r.fst

/-- **The transfer to the plain semantics, up to `≈`**: a set generating the
annotated algebra over `𝔹` up to `≈` generates, plainly and without
reading aggregate columns as keys, every faithful query. Over `𝔹` the
rows `≈` keeps are the realized world of an evaluation, which is the
plain evaluation of the realized world
(`AggQueryIn.genRandomWorld_evaluate`), and an instance annotated `𝟙`
realizes itself. -/
theorem generatesAtNoExplode_of_generatesAnnZ {sch : Schema} {cnt : SeqAggFunc T}
    {S : Set OpKind} (h : GeneratesAnnZ T BoolNone sch cnt S) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ) (hf : q.liftFaithful) (ha : q.noExplode)
    (hwk : q.wellKinded (ColKind.allReg 0) HoleKinds.empty) :
    GeneratesAtNoExplode T sch cnt S q := by
  intro ho hu hi
  obtain ⟨q', ho', hu', hi', ha', hwk', he⟩ := h q ho hu hi ha hwk
  have hh := q.hygienic_of_overSchema _ ho
  have hh' := q'.hygienic_of_overSchema _ ho'
  refine ⟨κ, q', ho', hu', hi', ha', hwk', AggQueryIn.Extends.of_settles (fun D γ hD => ?_)⟩
  have hann : q.AnnSettlesAt (D.liftOne (K := BoolNone)) γ {} :=
    AggQueryIn.annSettlesAt_of_settlesAt q hf ha hh hwk _ γ
      (by rw [Database.toPlain_liftOne]; exact hD)
  obtain ⟨hs', heq⟩ := he _ γ hann
  have hq := AggQueryIn.genRandomWorld_evaluate q (AggQueryIn.noProvSum_of_usesOnly q hu)
    hh hwk (D.liftOne (K := BoolNone)) Empty.elim hann
  have hq' := AggQueryIn.genRandomWorld_evaluate q' (AggQueryIn.noProvSum_of_usesOnly q' hu')
    hh' hwk' (D.liftOne (K := BoolNone)) Empty.elim hs'
  have hs := AggQueryIn.settlesAt_randomWorld q' (AggQueryIn.noProvSum_of_usesOnly q' hu')
    hh' hwk' (D.liftOne (K := BoolNone)) Empty.elim
    hs'
  rw [AnnotatedDatabase.randomWorld_liftOne] at hq hq' hs
  refine ⟨hs, ?_⟩
  rw [← hq, ← hq', ← zeroNorm_fst_boolNone, ← zeroNorm_fst_boolNone, heq]

end Boolean

/-! ## The rows up to `≈` -/

section Rows

variable {T : Type} [ValueType T]

/-- `∅` is in every set generating the annotated algebra over `𝔹` up to `≈`. -/
theorem empty_mem_of_generatesAnnZ {cnt : SeqAggFunc T} {S : Set OpKind}
    (h : GeneratesAnnZ T BoolNone Schema.empty cnt S) : OpKind.empty ∈ S :=
  empty_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnnZ h _
    AggQueryIn.liftFaithful_unit AggQueryIn.noExplode_unit AggQueryIn.wellKinded_unit).toGeneratesAt

/-- `γ` is in every set generating the annotated algebra over `𝔹` up to `≈`. -/
theorem gamma_mem_of_generatesAnnZ {sch : Schema} {cnt : SeqAggFunc T} {S : Set OpKind}
    (h : GeneratesAnnZ T BoolNone sch cnt S) : OpKind.gamma ∈ S :=
  gamma_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnnZ h _
    AggQueryIn.liftFaithful_unit AggQueryIn.noExplode_unit AggQueryIn.wellKinded_unit).toGeneratesAt

/-- `Π` is in every set generating the annotated algebra over `𝔹` up to `≈`. -/
theorem proj_mem_of_generatesAnnZ {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnnZ ℕ BoolNone schemaS cnt S) : OpKind.proj ∈ S :=
  proj_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnnZ h _
    liftFaithful_projWitness noExplode_projWitness wellKinded_projWitness).toGeneratesAt

/-- `×` or the apply is in every set generating the annotated algebra over
`𝔹` up to `≈`. -/
theorem prod_or_apply_mem_of_generatesAnnZ {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnnZ ℕ BoolNone schemaR cnt S) : OpKind.prod ∈ S ∨ OpKind.apply ∈ S :=
  prod_or_apply_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnnZ h _
    liftFaithful_prodWitness noExplode_prodWitness wellKinded_prodWitness).toGeneratesAt

/-- `μ^⊎` is in every set generating the annotated algebra over `𝔹` up to `≈`. -/
theorem muBag_mem_of_generatesAnnZ {cnt : SeqAggFunc ℕ} (hcnt : cnt.ReadsCount)
    {S : Set OpKind} (h : GeneratesAnnZ ℕ BoolNone schemaSE cnt S) : OpKind.muBag ∈ S :=
  muBag_mem_of_generatesAt hcnt (generatesAtNoExplode_of_generatesAnnZ h _
    liftFaithful_chainWitness noExplode_chainWitness wellKinded_chainWitness).toGeneratesAt

/-- `win` is in every set generating the annotated algebra over `𝔹` up to
`≈`, with the counting aggregate. -/
theorem win_mem_of_generatesAnnZ {S : Set OpKind}
    (h : GeneratesAnnZ ℕ BoolNone schemaR SeqAggFunc.count S) : OpKind.win ∈ S :=
  win_mem_of_generatesAt (generatesAtNoExplode_of_generatesAnnZ h _
    liftFaithful_winWitness noExplode_winWitness wellKinded_winWitness).toGeneratesAt

/-- `σ` is in every set generating the annotated algebra over `𝔹` up to `≈`. -/
theorem sel_mem_of_generatesAnnZ {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnnZ ℕ BoolNone schemaS cnt S) : OpKind.sel ∈ S :=
  sel_mem_of_generatesAtNoExplode (generatesAtNoExplode_of_generatesAnnZ h _
    liftFaithful_ltWitness noExplode_ltWitness wellKinded_ltWitness)

/-- **`ε` or `μ^∪` is in every set generating the annotated algebra over `ℕ`
up to `≈`**: the row annotated `2` that `ε(R)` gives is not one `≈` drops. -/
theorem dedup_or_muSet_mem_of_generatesAnnZ {S : Set OpKind}
    (h : GeneratesAnnZ ℕ ℕ schemaR SeqAggFunc.count S) :
    OpKind.dedup ∈ S ∨ OpKind.muSet ∈ S := by
  by_contra hS
  rw [not_or] at hS
  obtain ⟨q', -, hu', hi', ha', -, hm⟩ := h epsWitness overSchema_epsWitness
    usesOnly_epsWitness trivial trivial trivial
  obtain ⟨-, he⟩ := hm dEps (fun _ => 0) trivial
  obtain ⟨r, hr, hre⟩ := Multiset.mem_map.1 mem_evaluateAnnotated_epsWitness
  have hfin : r.snd.finalize = 2 := congrArg Prod.snd hre
  obtain ⟨r', hr', hfin'⟩ := GenRow.exists_finalize_of_zeroNorm he hr (by rw [hfin]; decide)
  have hz := (le1_evaluate hS.1 hS.2 count_distinct_ne dEps_le1 q' hu' hi' ha'
    (fun _ => 0) {} (fun k => k.elim0) (fun p hp => absurd hp List.not_mem_nil)
    r' hr').finalize
  omega

/-- **`−` is in every set generating the annotated algebra over `ℕ × ℕ` up
to `≈`.** -/
theorem diff_mem_of_generatesAnnZ {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnnZ ℕ NatPair schemaRS cnt S) : OpKind.diff ∈ S := by
  by_contra hS
  obtain ⟨q', -, hu', hi', ha', -, hm⟩ := h diffWitness overSchema_diffWitness
    usesOnly_diffWitness ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
  obtain ⟨-, he⟩ := hm dDiff (fun _ => 0) ⟨trivial, trivial⟩
  have hmem : ((((fun _ => 0) : Tuple ℕ 1), NatPair.mk 0 1) : AnnotatedTuple ℕ NatPair 1)
      ∈ diffWitness.evaluateAnnotated dDiff (fun _ => 0) := by
    rw [evaluateAnnotated_diffWitness]
    exact Multiset.mem_singleton_self _
  obtain ⟨r, hr, hre⟩ := Multiset.mem_map.1 hmem
  have hfin : r.snd.finalize = NatPair.mk 0 1 := congrArg Prod.snd hre
  obtain ⟨r', hr', hfin'⟩ := GenRow.exists_finalize_of_zeroNorm he hr (by
    rw [hfin]; intro h0; exact absurd (congrArg Prod.snd h0) (by decide))
  have hz := (annIn_evaluate NatPair.annClosed_zeroPat hS dDiff_zeroPat q' hu' hi' ha'
    (fun _ => 0) {} (fun k => k.elim0) (fun p hp => absurd hp List.not_mem_nil)
    r' hr').finalize NatPair.annClosed_zeroPat
  rw [hfin', hfin] at hz
  exact absurd hz (by simp [NatPair.ZeroPat])

/-- **`−` is in every set generating the annotated algebra over `ℕ[x, y]`
up to `≈`.** -/
theorem diff_mem_of_generatesAnnZ_xy {cnt : SeqAggFunc ℕ} {S : Set OpKind}
    (h : GeneratesAnnZ ℕ PolyXY schemaRS cnt S) : OpKind.diff ∈ S := by
  by_contra hS
  obtain ⟨q', -, hu', hi', ha', -, hm⟩ := h diffWitness overSchema_diffWitness
    usesOnly_diffWitness ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
  obtain ⟨-, he⟩ := hm dDiffXY (fun _ => 0) ⟨trivial, trivial⟩
  have hmem : ((((fun _ => 0) : Tuple ℕ 1),
      MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 1) : AnnotatedTuple ℕ PolyXY 1)
      ∈ diffWitness.evaluateAnnotated dDiffXY (fun _ => 0) := by
    rw [evaluateAnnotated_diffWitness_xy]
    exact Multiset.mem_singleton_self _
  obtain ⟨r, hr, hre⟩ := Multiset.mem_map.1 hmem
  have hfin : r.snd.finalize = MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 1 :=
    congrArg Prod.snd hre
  obtain ⟨r', hr', hfin'⟩ := GenRow.exists_finalize_of_zeroNorm he hr (by
    rw [hfin]; intro h0
    exact not_xLeY_x (h0 ▸ PolyXY.xLeY_of_const 0 fun i => by simp))
  have hz := (annIn_evaluate PolyXY.annClosed_xLeY hS dDiffXY_xLeY q' hu' hi' ha'
    (fun _ => 0) {} (fun k => k.elim0) (fun p hp => absurd hp List.not_mem_nil)
    r' hr').finalize PolyXY.annClosed_xLeY
  rw [hfin', hfin] at hz
  exact not_xLeY_x hz

end Rows

/-! ## The basis up to `≈` -/

theorem annBasisClass_boolNone : AnnBasisClass BoolNone := Or.inr fun _ => rfl

/-- **No proper subset of the nine classes generates the annotated algebra
up to `≈` over every semiring of the class**, with the counting aggregate:
`𝔹` carries the rows inherited from the plain basis, `ℕ` the `ε` row and
`ℕ[x, y]` the difference's. -/
theorem annEpsOps_minimal_in_class_approx {S : Set OpKind} (hS : S ⊆ annEpsOps)
    (h : ∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
      AnnBasisClass K → ∀ sch : Schema, GeneratesAnnZ ℕ K sch SeqAggFunc.count S) :
    S = annEpsOps := by
  have hB := h BoolNone annBasisClass_boolNone
  have hN := h ℕ annBasisClass_nat
  have hP := h PolyXY annBasisClass_polyXY
  refine Set.Subset.antisymm hS fun x hx => ?_
  have hout : ∀ y, y ∈ S → y ∉ annEpsOps → False := fun y hy hn => hn (hS hy)
  cases x with
  | empty => exact empty_mem_of_generatesAnnZ (hB _)
  | proj => exact proj_mem_of_generatesAnnZ (hB _)
  | sel => exact sel_mem_of_generatesAnnZ (hB _)
  | prod => exact absurd hx (by simp [annEpsOps])
  | apply =>
    rcases prod_or_apply_mem_of_generatesAnnZ (hB _) with h | h
    · exact (hout _ h (by simp [annEpsOps])).elim
    · exact h
  | union => exact absurd hx (by simp [annEpsOps])
  | dedup =>
    rcases dedup_or_muSet_mem_of_generatesAnnZ (hN schemaR) with h | h
    · exact h
    · exact (hout _ h (by simp [annEpsOps])).elim
  | diff => exact diff_mem_of_generatesAnnZ_xy (hP schemaRS)
  | gamma => exact gamma_mem_of_generatesAnnZ (hB Schema.empty)
  | win => exact win_mem_of_generatesAnnZ (hB _)
  | muBag => exact muBag_mem_of_generatesAnnZ SeqAggFunc.isCount_count_nat.readsCount (hB _)
  | muSet => exact absurd hx (by simp [annEpsOps])

/-! ## The positive half up to `≈` -/

/-- Two evaluations agreeing row by row up to finalization agree up to `≈`:
`≈` reads a row's columns and its finalized annotation only. -/
theorem GenRow.zeroNorm_eq_of_fin {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K]
    [DecidableEq K] {n : ℕ} {A B : Multiset (GenRow T K n)}
    (h : A.map GenRow.fin = B.map GenRow.fin) : GenRow.zeroNorm A = GenRow.zeroNorm B := by
  have hz : ∀ R : Multiset (GenRow T K n), GenRow.zeroNorm R
      = ((R.map GenRow.fin).filter (fun x => x.2 ≠ 0)).map
          (fun x => ((GenRow.zeroTuple x.1, x.2) : AnnotatedTuple T K n)) := by
    intro R
    unfold GenRow.zeroNorm
    rw [Multiset.filter_map, Multiset.map_map]
    rfl
  rw [hz, hz, h]

/-- **The nine classes generate the annotated algebra up to `≈` over every
semiring of the class**: the constructions agree with their source row by
row up to finalization (`exists_annEpsOps_match`), which is what `≈`
reads. -/
theorem generatesAnnZ_annEpsOps_of_class {T : Type} [ValueType T] {K : Type}
    [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] (hK : AnnBasisClass K)
    (sch : Schema) (cnt : SeqAggFunc T) : GeneratesAnnZ T K sch cnt annEpsOps := by
  intro n κ q ho hu hi ha hp
  obtain ⟨ch, hnc⟩ :
      ∃ ch, AggQueryIn.NodeCorrect cnt ch (fun _ : AnnotatedDatabase T K => True) := by
    rcases hK with ⟨hδ, hR⟩ | hδ
    · exact ⟨false, AggQueryIn.nodeCorrect_succ cnt hδ hR⟩
    · exact ⟨true, AggQueryIn.nodeCorrect_chain cnt hδ⟩
  obtain ⟨q', ho', hu', hi', ha', hp', hm⟩ :=
    exists_annEpsOps_match sch cnt ch hnc q ho hu hi ha hp
  exact ⟨q', ho', hu', hi', ha', hp', fun d γ hs =>
    ⟨(hm d γ trivial hs).1, GenRow.zeroNorm_eq_of_fin (hm d γ trivial hs).2⟩⟩

/-- **The annotated basis theorem up to `≈`, over the class**: the nine
classes generate the annotated algebra up to `≈` over every semiring of
`AnnBasisClass`, and no proper subset of them does over all of those semirings. -/
theorem annEpsOps_isBasis_in_class_approx :
    (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
      AnnBasisClass K → ∀ sch : Schema, GeneratesAnnZ ℕ K sch SeqAggFunc.count annEpsOps)
    ∧ ∀ S ⊆ annEpsOps,
      (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
        AnnBasisClass K → ∀ sch : Schema, GeneratesAnnZ ℕ K sch SeqAggFunc.count S) →
      S = annEpsOps :=
  ⟨fun _ _ _ _ hK sch => generatesAnnZ_annEpsOps_of_class hK sch _,
    fun _ hS h => annEpsOps_minimal_in_class_approx hS h⟩
