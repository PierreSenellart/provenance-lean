/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AnnotatedSum
import Provenance.PathSum
import Provenance.HavingQueryCorrectness

/-!
# The set recursion from the bag recursion and `ε`, in the annotated semantics

A set recursion `μ^∪R.(q₀, q₁)` whose body reads `R` once and through no
union is linear in `R`, and duplicate elimination sums the annotations of
the copies of a tuple without applying `δ`, so its rounds are `ε` of the
truncated sums of the rounds of a bag recursion (`PathSum`). The bounded
simulation of the plain semantics (`MuUnion`) therefore carries over, with
one change: its counter must not multiply the derivations it is paired
with. Here it is a *successor* counter whose rows are annotated `𝟙`, which
a grouping gives where `δ` is the support map and no instance row is
annotated `𝟘`; and the rounds settle within the size of the tuple set
where the semiring is absorptive or cancellative without zero divisors
(`PathSum.SettlesEarly`).

This module works on the annotated relation a query gives, `ann`, which
is all the construction reads: every relation it builds is all-regular.
-/

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-- The commutative semiring underlying a commutative m-semiring, which
`PathSum` speaks in. -/
instance (priority := 50) CommSemiringWithMonus.toCommSemiring' : CommSemiring K :=
  { (inferInstance : Semiring K) with mul_comm := CommSemiringWithMonus.mul_comm }

namespace AggQueryIn

/-- **The annotated relation of a query** in an environment: its rows,
each read as a tuple of values with its finalized annotation. -/
noncomputable def ann {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) : AnnotatedRelation T K n :=
  (q.evaluate d γ E).map GenRow.toAnnotated

theorem ann_castKind {c n : ℕ} {κ κ' : Fin n → ColKind} {l : List (String × ℕ)} (h : κ = κ')
    (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (q.castKind h).ann d γ E = q.ann d γ E := by
  rw [ann, ann, evaluate_castKind]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem plainTuple_append {n₁ n₂ : ℕ} (x : Tuple (GenValue T K) n₁)
    (y : Tuple (GenValue T K) n₂) :
    GenRow.plainTuple (Fin.append x y : Tuple (GenValue T K) (n₁ + n₂))
      = Fin.append (GenRow.plainTuple x) (GenRow.plainTuple y) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [GenRow.plainTuple, Fin.append_left]
  · simp only [GenRow.plainTuple, Fin.append_right]

/-- **The product written as an apply** pairs the rows and multiplies the
annotations. -/
theorem ann_prodA {c n₁ n₂ : ℕ} {l : List (String × ℕ)}
    (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁) l) (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (prodA q₁ q₂).ann d γ E
      = ((q₁.ann d γ E).product (q₂.ann d γ E)).map (fun p =>
          ((Fin.append p.1.1 p.2.1, p.1.2 * p.2.2) : AnnotatedTuple T K (n₁ + n₂))) := by
  rw [prodA, ann_castKind, ann, evaluate_prodApply]
  simp only [evaluate, ann]
  unfold Multiset.product
  simp only [Multiset.map_bind, Multiset.map_map, Multiset.bind_map]
  refine Multiset.bind_congr fun x _ => Multiset.map_congr rfl fun y _ => ?_
  simp only [Function.comp, GenRow.toAnnotated]
  refine Prod.ext (plainTuple_append x.fst y.fst) (GenAnn.finalize_mul' x.snd y.snd)

/-- A selection without an aggregate atom filters. -/
theorem ann_sel {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (φ : GenPredIn T c κ)
    (q : AggQueryIn T c n κ l) (hφ : SelOK l φ) (hφ' : φ.hasAggAtom = false)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (Sel φ q hφ).ann d γ E = (q.ann d γ E).filter (fun p => φ.holdsPlain p.1 γ) := by
  simp only [ann, evaluate, hφ', Bool.false_eq_true, ite_false]
  rw [Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr fun r _ => ?_
  exact GenPredIn.holds_iff_holdsPlain φ r.fst

theorem ann_sum {c n : ℕ} {κ : Fin n → ColKind} {l₁ l₂ : List (String × ℕ)}
    (q₁ : AggQueryIn T c n κ l₁) (q₂ : AggQueryIn T c n κ l₂)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (Sum q₁ q₂).ann d γ E = q₁.ann d γ E + q₂.ann d γ E := by
  simp only [ann, evaluate, Multiset.map_add]

/-- **Duplicate elimination**, in the vocabulary of `PathSum`. -/
theorem ann_dedup {c n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (Dedup q).ann d γ E = PathSum.dedupK (q.ann d γ E) := by
  simp only [ann, evaluate, Multiset.map_map]
  rw [show (GenRow.toAnnotated ∘ GenRow.ofAnnotated : AnnotatedTuple T K n → _) = id from
    funext GenRow.toAnnotated_ofAnnotated, Multiset.map_id, groupByKey_eq_dedup_map]
  rfl

/-- **Difference**, in the vocabulary of `PathSum`: every row of the left
side is kept, its annotation minus the right side's weight on its tuple. -/
theorem ann_diff {c n : ℕ} (q₁ q₂ : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (Diff q₁ q₂).ann d γ E
      = (q₁.ann d γ E).map (fun p => ((p.1, p.2 - PathSum.wt (q₂.ann d γ E) p.1)
          : AnnotatedTuple T K n)) := by
  simp only [ann, evaluate, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp, GenRow.toAnnotated_ofAnnotated]
  generalize p.toAnnotated = x
  obtain ⟨u, α⟩ := x
  exact Prod.ext rfl (congrArg (α - ·) (groupByKey_find_eq_filter_sum _ u))

/-! ## A linear term reads its recursive relation row by row -/

/-- **A linear term reads the recursive relation row by row**, up to
finalization: bound to a relation `Y`, it gives, for each row of `Y`, its
value at that row's tuple annotated `𝟙`, the annotations multiplied by the
row's. -/
theorem evaluate_fin_of_recLinear {s : String} {n : ℕ} :
    ∀ {c m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
      q.recLinear s n → q.noExplode →
      ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
        (Y : AnnotatedRelation T K n),
        (q.evaluate d γ (E.assignHole s (Y.map GenRow.ofAnnotated))).map GenRow.fin
          = Y.bind (fun p => (q.evaluate d γ (E.assignHole s
              ({GenRow.ofAnnotated (p.1, 1)} : Multiset (GenRow T K n)))).map
              (fun r => (r.fst, p.2 * r.snd.finalize))) := by
  intro c m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' κh =>
    rintro ⟨rfl, rfl⟩ - d γ E Y
    simp only [evaluate, EvalEnv.assignHole_holes_self]
    induction Y using Multiset.induction_on with
    | empty => simp
    | cons p Y ih =>
      rw [Multiset.map_cons, Multiset.filter_cons, Multiset.map_add, ih, Multiset.cons_bind,
        Multiset.filter_singleton]
      congr 1
      have hf : (GenRow.ofAnnotated (p.1, (1 : K))).fst = (GenRow.ofAnnotated p).fst := rfl
      rw [hf]
      split_ifs
      · simp [GenRow.fin, GenRow.ofAnnotated, GenAnn.finalize]
      · simp
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih =>
    intro h hx d γ E Y
    simp only [evaluate, Multiset.map_map]
    refine (map_via_fin _ _ (fun u => ((fun j => (ps j).eval u.1 γ, u.2)
        : Tuple (GenValue T K) _ × K)) (fun x _ => fin_proj ps x γ)).trans ?_
    rw [ih h hx d γ E Y, Multiset.map_bind]
    refine Multiset.bind_congr fun p _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp]
    exact Prod.ext rfl (congrArg (p.2 * ·)
      (GenAnn.finalize_cash' r.snd _ Multiset.inter_le_left).symm)
  | Sel φ q hφ ih =>
    rintro ⟨hφ', h⟩ hx d γ E Y
    simp only [evaluate, hφ', Bool.false_eq_true, ite_false]
    have hfm : ∀ X : Multiset (GenRow T K _),
        (X.filter (fun r => φ.holds r.fst γ)).map GenRow.fin
          = (X.map GenRow.fin).filter (fun u => φ.holds u.1 γ) := fun X => by
      rw [Multiset.filter_map]; rfl
    rw [hfm, ih h hx d γ E Y, Multiset.filter_bind]
    refine Multiset.bind_congr fun p _ => ?_
    rw [Multiset.filter_map]
    rfl
  | Prod q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁' n₂' κ₁' κ₂' l₁' l₂'
    have hrow : ∀ {a b : ℕ} (A : Multiset (GenRow T K a)) (B : Multiset (GenRow T K b)),
        ((A.product B).map (fun ((x, y) : GenRow T K a × GenRow T K b) =>
          (⟨Fin.append x.fst y.fst, ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
            : GenRow T K (a + b)))).map GenRow.fin
          = A.bind (fun x => B.map (fun y =>
              ((Fin.append x.fst y.fst, x.snd.finalize * y.snd.finalize)
                : Tuple (GenValue T K) _ × K))) := fun A B => by
      unfold Multiset.product
      simp only [Multiset.map_bind, Multiset.map_map]
      refine Multiset.bind_congr fun x _ => Multiset.map_congr rfl fun y _ => ?_
      exact Prod.ext rfl (GenAnn.finalize_mul' x.snd y.snd)
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) ⟨hx₁, hx₂⟩ d γ E Y
    · simp only [evaluate, evaluate_assignHole_closed q₂]
      rw [hrow]
      have hfac : ∀ X : Multiset (GenRow T K n₁'),
          X.bind (fun x => (q₂.evaluate d γ E).map (fun y =>
            ((Fin.append x.fst y.fst, x.snd.finalize * y.snd.finalize)
              : Tuple (GenValue T K) _ × K)))
          = (X.map GenRow.fin).bind (fun u => (q₂.evaluate d γ E).map (fun y =>
              ((Fin.append u.1 y.fst, u.2 * y.snd.finalize) : Tuple (GenValue T K) _ × K))) :=
        fun X => by rw [Multiset.bind_map]; rfl
      rw [hfac, ih₁ h₁ hx₁ d γ E Y, Multiset.bind_assoc]
      refine Multiset.bind_congr fun p _ => ?_
      unfold Multiset.product
      rw [Multiset.bind_map, Multiset.map_bind, Multiset.map_bind]
      refine Multiset.bind_congr fun x _ => ?_
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun y _ => ?_
      simp only [Function.comp]
      exact Prod.ext rfl (by rw [GenAnn.finalize_mul', mul_assoc])
    · simp only [evaluate, evaluate_assignHole_closed q₁]
      rw [hrow]
      have hfac : ∀ X : Multiset (GenRow T K n₂'),
          (q₁.evaluate d γ E).bind (fun x => X.map (fun y =>
            ((Fin.append x.fst y.fst, x.snd.finalize * y.snd.finalize)
              : Tuple (GenValue T K) _ × K)))
          = (q₁.evaluate d γ E).bind (fun x => (X.map GenRow.fin).map (fun u =>
              ((Fin.append x.fst u.1, x.snd.finalize * u.2) : Tuple (GenValue T K) _ × K))) :=
        fun X => Multiset.bind_congr fun x _ => by rw [Multiset.map_map]; rfl
      rw [hfac]
      simp only [ih₂ h₂ hx₂ d γ E Y, Multiset.map_bind]
      rw [Multiset.bind_bind]
      refine Multiset.bind_congr fun p _ => ?_
      unfold Multiset.product
      rw [Multiset.map_bind, Multiset.map_bind]
      refine Multiset.bind_congr fun x _ => ?_
      rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun y _ => ?_
      simp only [Function.comp]
      exact Prod.ext rfl (by rw [GenAnn.finalize_mul', mul_left_comm])
  | Apply q₁ q₂ ih₁ ih₂ =>
    rintro ⟨h₁, h₂⟩ ⟨hx₁, hx₂⟩ d γ E Y
    have hR : ∀ {k : ℕ} (X : Multiset (GenRow T K k)) (x : GenRow T K _),
        q₂.evaluate d (Fin.append (GenRow.plainTuple x.fst) γ)
            ((E.assignHole s X).withCtx (Fin.append x.fst ((E.assignHole s X).ctxAt _ γ)))
          = q₂.evaluate d (Fin.append (GenRow.plainTuple x.fst) γ)
            (E.withCtx (Fin.append x.fst (E.ctxAt _ γ))) := fun X x => by
      refine evaluate_congr_holes q₂ d _ (fun _ hp => absurd hp List.not_mem_nil) ?_
      simp only [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_assignHole]
    simp only [evaluate, hR, Multiset.map_bind]
    have hfac : ∀ X : Multiset (GenRow T K _),
        X.bind (fun x => ((q₂.evaluate d (Fin.append (GenRow.plainTuple x.fst) γ)
            (E.withCtx (Fin.append x.fst (E.ctxAt _ γ)))).map (fun y =>
          (⟨Fin.append x.fst y.fst, ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
            : GenRow T K _))).map GenRow.fin)
        = (X.map GenRow.fin).bind (fun u => (q₂.evaluate d (Fin.append (GenRow.plainTuple u.1) γ)
            (E.withCtx (Fin.append u.1 (E.ctxAt _ γ)))).map (fun y =>
              ((Fin.append u.1 y.fst, u.2 * y.snd.finalize) : Tuple (GenValue T K) _ × K))) :=
      fun X => by
        rw [Multiset.bind_map]
        refine Multiset.bind_congr fun x _ => ?_
        rw [Multiset.map_map]
        exact Multiset.map_congr rfl fun y _ => Prod.ext rfl (GenAnn.finalize_mul' x.snd y.snd)
    rw [hfac, ih₁ h₁ hx₁ d γ E Y, Multiset.bind_assoc]
    refine Multiset.bind_congr fun p _ => ?_
    rw [Multiset.bind_map]
    refine Multiset.bind_congr fun x _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun y _ => ?_
    simp only [Function.comp]
    exact Prod.ext rfl (by rw [GenAnn.finalize_mul', mul_assoc])
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun _ h => h.elim
  | Retag hk q ih => exact fun h hx d γ E Y => ih h hx d γ E Y
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

/-- **A linear term, in the vocabulary of `PathSum`**: its annotated
relation at a round `Y` is `Y ⊳ G`, `G` reading the term at one tuple
annotated `𝟙`. -/
theorem ann_of_recLinear {s : String} {n c m : ℕ} {κ : Fin m → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T c m κ l) (h : q.recLinear s n)
    (hx : q.noExplode) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (Y : AnnotatedRelation T K n) :
    q.ann d γ (E.assignHole s (Y.map GenRow.ofAnnotated))
      = PathSum.lin (fun u => q.ann d γ (E.assignHole s
          ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))) Y := by
  have hann : ∀ X : Multiset (GenRow T K m), X.map GenRow.toAnnotated
      = (X.map GenRow.fin).map (fun u => ((GenRow.plainTuple u.1, u.2) : AnnotatedTuple T K m)) :=
    fun X => by rw [Multiset.map_map]; rfl
  rw [ann, hann, evaluate_fin_of_recLinear q h hx d γ E Y, Multiset.map_bind]
  unfold PathSum.lin
  refine Multiset.bind_congr fun p _ => ?_
  simp only [ann, Multiset.map_map]
  rfl

omit [HasAltLinearOrder K] in
/-- `ε` of an annotated relation is `PathSum.dedupK`. -/
theorem dedupAnn_eq_dedupK {n : ℕ} (r : AnnotatedRelation T K n) :
    AnnotatedRelation.dedupAnn r = PathSum.dedupK r := by
  rw [AnnotatedRelation.dedupAnn, groupByKey_eq_dedup_map]
  rfl

/-- **A set recursion with a linear body is the set recursion of
`PathSum`**: its value is the settled iterate of `X ↦ ε(B ⊎ X ⊳ G)`. -/
theorem evaluate_MuSet_of_recLinear {c n : ℕ} (s : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (h : q₁.recLinear s n)
    (hx : q₁.noExplode) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (MuSet s q₀ q₁).evaluate d γ E
      = (muFix (PathSum.stepK (q₀.ann d γ E) (fun u => q₁.ann d γ (E.assignHole s
          ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))))).map
          GenRow.ofAnnotated := by
  rw [evaluate_MuSet]
  congr 1
  refine muFix_congr fun X => ?_
  rw [muSetStep, dedupAnn_eq_dedupK, PathSum.stepK]
  congr 2
  exact ann_of_recLinear q₁ h hx d γ E X

/-! ## The recursive relation replaced by the current row -/

/-- The row a `Param` leaf reading `pv` gives, whatever its kinds say. -/
def paramRow {c n : ℕ} (E : EvalEnv T K) (γ : Fin c → T) (pv : Fin n → T ⊕ Fin c) :
    GenRow T K n :=
  ⟨fun k => _root_.Sum.elim Sum.inl (E.ctxAt c γ) (pv k), ⟨1, 0⟩⟩

/-- **Substituting is binding, in the annotated semantics**: the linear
term with its hole replaced by the parameter row reads as the term with
the hole bound to that row alone. -/
theorem evaluate_substRel {s : String} {c n : ℕ} (pv : Fin n → T ⊕ Fin c) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K),
        (substRel s pv q).evaluate d γ E
          = q.evaluate d γ (E.assignHole s ({paramRow E γ pv} : Multiset (GenRow T K n))) := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' κh =>
    rintro ⟨rfl, rfl⟩ d γ E
    rw [substRel, dite_eq_left ⟨rfl, rfl⟩, evaluate_castIdx]
    simp only [evaluate, EvalEnv.assignHole_holes_self, EvalEnv.paramRows,
      Multiset.filter_singleton]
    rfl
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih =>
    intro h d γ E
    simp only [substRel, evaluate]
    rw [ih pv h d γ E]
  | Sel φ q _ ih =>
    intro h d γ E
    simp only [substRel, evaluate]
    rw [ih pv h.2 d γ E]
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) d γ E
    · simp only [substRel, evaluate_castIdx, evaluate]
      rw [ih₁ pv h₁ d γ E, substRel_of_noMention pv q₂ h₂, evaluate_assignHole_closed q₂]
    · simp only [substRel, evaluate_castIdx, evaluate]
      rw [ih₂ pv h₂ d γ E, substRel_of_noMention pv q₁ h₁, evaluate_assignHole_closed q₁]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h d γ E
    simp only [substRel, evaluate]
    rw [ih₁ pv h.1 d γ E]
    refine Multiset.bind_congr fun x _ => ?_
    congr 1
    refine evaluate_congr_holes q₂ d _ (fun _ hp => absurd hp List.not_mem_nil) ?_
    simp only [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_assignHole]
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih =>
    intro h d γ E
    simp only [substRel, evaluate]
    rw [ih pv h d γ E]
  | Retag hk q ih => exact fun h d γ E => ih pv h d γ E
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

/-! ## The successor counter -/

section Counter

variable {c : ℕ}

/-- **A lexicographic comparison of two runs of terms**, read on values
none of which is the null. -/
theorem holdsPlain_ltPredOn_asc {m K : ℕ} (x y : Fin K → TermGIn T c (ColKind.allReg m))
    (u : Tuple T m) (γ : Fin c → T) (hx : ∀ k, ValueType.isNull ((x k).evalPlain u γ) = false)
    (hy : ∀ k, ValueType.isNull ((y k).evalPlain u γ) = false) :
    (OrderSpec.ltPredOn (OrderSpec.asc K) x y (List.finRange K)).holdsPlain u γ
      ↔ ascLt K (fun k => (x k).evalPlain u γ) (fun k => (y k).evalPlain u γ) := by
  rw [OrderSpec.ltPredOn, OrderSpec.holdsPlain_ltPredOnOf (OrderSpec.asc K) _ x y u γ
    (fun k => OrderCol.holdsPlain_ltPred_of (OrderSpec.asc K k) (x k) (y k) u γ (hx k) (hy k))
    (fun k a b => OrderSpec.OrderCol.peer_ASC_iff a b)]
  show OrderSpec.le (OrderSpec.asc K) _ _ = false ↔ _
  unfold ascLt
  rw [OrderSpec.lt_iff]

/-- The first half of a row strictly below its second half. -/
def halvesLt (K : ℕ) : GenPredIn T c (ColKind.allReg (K + K)) :=
  OrderSpec.ltPredOn (OrderSpec.asc K) (fun k => TermGIn.index (Fin.castAdd K k) rfl)
    (fun k => TermGIn.index (Fin.natAdd K k) rfl) (List.finRange K)

/-- The middle third of a row strictly between its first and last. -/
def midLt (K : ℕ) : GenPredIn T c (ColKind.allReg ((K + K) + K)) :=
  GenPredIn.and
    (OrderSpec.ltPredOn (OrderSpec.asc K)
      (fun k => TermGIn.index (Fin.castAdd K (Fin.castAdd K k)) rfl)
      (fun k => TermGIn.index (Fin.castAdd K (Fin.natAdd K k)) rfl) (List.finRange K))
    (OrderSpec.ltPredOn (OrderSpec.asc K)
      (fun k => TermGIn.index (Fin.castAdd K (Fin.natAdd K k)) rfl)
      (fun k => TermGIn.index (Fin.natAdd (K + K) k) rfl) (List.finRange K))

/-- The first half of a row equals the counter of the current row of an
apply, read off its outer columns. -/
def eqOuter (n K : ℕ) : GenPredIn T ((n + K) + c) (ColKind.allReg (K + K)) :=
  ((List.finRange K).map (fun k => GenPredIn.cmp CompOp.syneq
    (TermGIn.index (Fin.castAdd K k) rfl)
    (TermGIn.outer (Fin.castAdd c (Fin.natAdd n k))))).foldr GenPredIn.and truePred

/-- The column of the first and the last third of a row of three counters. -/
def outerThirds (K : ℕ) (j : Fin (K + K)) : Fin ((K + K) + K) :=
  Fin.addCases (fun i => Fin.castAdd K (Fin.castAdd K i)) (fun i => Fin.natAdd (K + K) i) j

/-- Keeping the columns `cols` of an all-regular relation. -/
def keepCols {n m : ℕ} {l : List (String × ℕ)} (cols : Fin m → Fin n)
    (q : AggQueryIn T c n (ColKind.allReg n) l) : AggQueryIn T c m (ColKind.allReg m) l :=
  (Proj (fun j => ProjColIn.term (TermGIn.index (cols j) rfl)) q).castKind
    (funext fun _ => rfl)

/-- **The counters**: the `K`-tuples over the values of `EQ`, each once. -/
def ctr (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c K (ColKind.allReg K) :=
  pow (dedupG EQ) K

/-- The pairs of counters, the first below the second. -/
def ctrLt (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c (K + K) (ColKind.allReg (K + K)) :=
  Sel (halvesLt K) (prodA (ctr EQ K) (ctr EQ K))

/-- The pairs of counters with one counter strictly between, once per
counter between. -/
def ctrMid (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c (K + K) (ColKind.allReg (K + K)) :=
  keepCols (outerThirds K)
    (Sel (midLt K) (prodA (prodA (ctr EQ K) (ctr EQ K)) (ctr EQ K)))

/-- **The successor relation**: the pairs of counters, the first below the
second, annotated `𝟙` where nothing is between and `𝟘` elsewhere. -/
def ctrSucc (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c (K + K) (ColKind.allReg (K + K)) :=
  Diff (ctrLt EQ K) (ctrMid EQ K)

/-- **The least counter**: every counter, annotated `𝟙` where none is
below it and `𝟘` elsewhere. -/
def ctrLeast (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K : ℕ) :
    AggQueryIn T c K (ColKind.allReg K) :=
  Diff (ctr EQ K) (keepCols (fun j => Fin.natAdd K j) (ctrLt EQ K))

/-- **The counters after the current row's**, under an apply over the
simulation's rows: the successor relation's second halves, where the first
half is the current row's counter. -/
def ctrNext (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (n K : ℕ) :
    AggQueryIn T ((n + K) + c) K (ColKind.allReg K) :=
  keepCols (fun j => Fin.natAdd K j)
    (Sel (eqOuter n K) ((ctrSucc EQ K).substMap (applyOuter T c (n + K))))

/-- **One round of the annotated simulation**: for each row, the term at
its tuple part, paired with the counter after the row's. -/
def simBodyA (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) :
    AggQueryIn T c (n + K) (ColKind.allReg (n + K)) [(s', n + K)] :=
  keepCols (fun j => Fin.natAdd (n + K) j)
    ((Apply (Hole (n + K) s')
      (prodA
        (castIdx (subIdx_self s n)
          (substRel s (rowPv n K) (L.substMap (applyOuter T c (n + K)))))
        (ctrNext EQ n K))).castKind (append_allReg (n + K) (n + K)))

/-- **The annotated simulation**: a bag recursion over a tuple and a
counter, from the base paired with the least counter. -/
def simA (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) :
    AggQueryIn T c (n + K) (ColKind.allReg (n + K)) :=
  Mu s' (prodA BQ (ctrLeast EQ K)) (simBodyA s s' n K EQ L)

/-- **Its tuple parts, duplicates eliminated**: the set recursion's value. -/
def simResultA (s s' : String) (n K : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) :
    AggQueryIn T c n (ColKind.allReg n) :=
  Dedup (keepCols (fun i => Fin.castAdd K i) (simA s s' n K EQ BQ L))

end Counter

section CounterAnn

variable {c : ℕ}

/-- **Keeping columns** keeps the rows and their annotations. -/
theorem ann_keepCols {n m : ℕ} {l : List (String × ℕ)} (cols : Fin m → Fin n)
    (q : AggQueryIn T c n (ColKind.allReg n) l) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    (keepCols cols q).ann d γ E
      = (q.ann d γ E).map (fun p => ((fun j => p.1 (cols j), p.2) : AnnotatedTuple T K m)) := by
  rw [keepCols, ann_castKind]
  simp only [ann, evaluate, Multiset.map_map]
  refine Multiset.map_congr rfl fun r _ => ?_
  simp only [Function.comp, GenRow.toAnnotated]
  exact Prod.ext rfl (GenAnn.finalize_cash' r.snd _ Multiset.inter_le_left)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem plainTuple_append_nil {n : ℕ} (g : Tuple T n) (v : Fin 0 → GenValue T K) :
    GenRow.plainTuple (Fin.append (fun k => (Sum.inl (g k) : GenValue T K)) v
      : Tuple (GenValue T K) (n + 0)) = g := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => i.elim0) k
  simp only [GenRow.plainTuple, Fin.append_left]
  rfl

/-- **Grouping by every column with no aggregate**: one row per tuple,
annotated `δ` of its weight. -/
theorem ann_dedupG {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (dedupG q).ann d γ E
      = ((q.ann d γ E).map Prod.fst).dedup.map (fun g =>
          ((g, SemiringWithMonus.delta (PathSum.wt (q.ann d γ E) g)) : AnnotatedTuple T K n)) := by
  rw [dedupG, ann_castKind]
  simp only [ann, evaluate]
  have hkey : (Multiset.map (fun p => ((fun k => p.fst k, p.snd) : AnnotatedTuple T K n))
      ((q.evaluate d γ E).map GenRow.toAnnotated)) = (q.evaluate d γ E).map GenRow.toAnnotated :=
    Multiset.map_id' _
  rw [hkey, groupByKey_eq_dedup_map, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun g _ => ?_
  simp only [Function.comp, GenRow.toAnnotated]
  refine Prod.ext (plainTuple_append_nil g _) ?_
  simp only [GenAnn.finalize, Multiset.map_singleton, Multiset.prod_singleton, one_mul,
    Having.havingGroupOrd_unord]
  congr 1
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Having.havingGroup_coe]
  unfold PathSum.wt
  congr 2
  refine Multiset.filter_congr fun p _ => ?_
  exact ⟨fun h => funext h, fun h k => congrFun h k⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem product_map_map' {α β γ' δ' : Type} (f : α → γ') (g : β → δ')
    (A : Multiset α) (B : Multiset β) :
    (A.map f).product (B.map g) = (A.product B).map (fun p => (f p.1, g p.2)) := by
  unfold Multiset.product
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem product_map_left' {α β γ' : Type} (f : α → γ') (A : Multiset α) (B : Multiset β) :
    (A.map f).product B = (A.product B).map (fun p => (f p.1, p.2)) := by
  unfold Multiset.product
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr fun a _ => ?_
  rw [Multiset.map_map]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem map_filter_congr {α β : Type} {S : Multiset α} {P Q : α → Prop} [DecidablePred P]
    [DecidablePred Q] {F G : α → β} (hPQ : ∀ x ∈ S, P x ↔ Q x)
    (hFG : ∀ x ∈ S, Q x → F x = G x) : (S.filter P).map F = (S.filter Q).map G := by
  rw [Multiset.filter_congr hPQ]
  exact Multiset.map_congr rfl fun x hx => hFG x (Multiset.mem_of_mem_filter hx)
    (Multiset.of_mem_filter hx)

/-- The `K`-tuples over a set of unary rows. -/
def powT (V : Multiset (Tuple T 1)) : (K : ℕ) → Multiset (Tuple T K)
  | 0 => {fun k => k.elim0}
  | K + 1 => ((powT V K).product V).map (fun p => Fin.append p.1 p.2)

theorem ann_unitC (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (unitC : AggQueryIn T c 0 _).ann d γ E
      = ({((fun k => k.elim0, 1) : AnnotatedTuple T K 0)} : Multiset (AnnotatedTuple T K 0)) := by
  rw [unitC, ann_castKind]
  simp only [ann, evaluate, Multiset.map_singleton, GenRow.toAnnotated]
  congr 1
  exact Prod.ext (funext fun k => k.elim0) (by simp [GenAnn.finalize])

/-- **The power of a relation of rows annotated `𝟙`** is the tuples over
its rows, each annotated `𝟙`. -/
theorem ann_pow_ones (C : AggQueryIn T c 1 (ColKind.allReg 1)) (V : Multiset (Tuple T 1))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (hC : C.ann d γ E = V.map (fun v => ((v, 1) : AnnotatedTuple T K 1))) :
    ∀ K', (pow C K').ann d γ E = (powT V K').map (fun v => ((v, 1) : AnnotatedTuple T K K'))
  | 0 => by rw [pow, ann_unitC]; rfl
  | K' + 1 => by
    rw [pow, ann_prodA, ann_pow_ones C V d γ E hC K', hC, product_map_map', Multiset.map_map,
      powT, Multiset.map_map]
    refine Multiset.map_congr rfl fun p _ => ?_
    simp only [Function.comp, mul_one]

omit [ValueType T] in
theorem nodup_powT {V : Multiset (Tuple T 1)} (hV : V.Nodup) : ∀ K', (powT V K').Nodup
  | 0 => Multiset.nodup_singleton _
  | K' + 1 => by
    refine Multiset.Nodup.map_on ?_ (Multiset.Nodup.product (nodup_powT hV K') hV)
    intro p _ q _ h
    have h₁ : p.1 = q.1 := funext fun k => by
      have := congrFun h (Fin.castAdd 1 k); simpa [Fin.append_left] using this
    have h₂ : p.2 = q.2 := funext fun k => by
      have := congrFun h (Fin.natAdd K' k); simpa [Fin.append_right] using this
    exact Prod.ext h₁ h₂

omit [ValueType T] in
theorem mem_powT {V : Multiset (Tuple T 1)} :
    ∀ (K' : ℕ) (u : Tuple T K'), u ∈ powT V K' ↔ ∀ k, (fun _ => u k) ∈ V
  | 0, u => by
    simp only [powT, Multiset.mem_singleton]
    exact ⟨fun _ k => k.elim0, fun _ => funext fun k => k.elim0⟩
  | K' + 1, u => by
    simp only [powT, Multiset.mem_map]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩ k
      obtain ⟨ha, hb⟩ := Multiset.mem_product.1 hab
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]; exact (mem_powT K' a).1 ha i
      · rw [Fin.append_right]
        have : (fun _ : Fin 1 => b i) = b := funext fun j => by
          rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
        rw [this]; exact hb
    · intro h
      refine ⟨(fun i => u (Fin.castAdd 1 i), fun _ => u (Fin.natAdd K' 0)),
        Multiset.mem_product.2 ⟨(mem_powT K' _).2 fun i => h _, h _⟩, ?_⟩
      funext k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]
      · rw [Fin.append_right, Fin.fin_one_eq_zero i]

theorem hasAggAtom_ltPredOnOf {p m : ℕ} (base : Fin p → GenPredIn T c (ColKind.allReg m))
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) (hb : ∀ k, (base k).hasAggAtom = false) :
    ∀ ks : List (Fin p), (OrderSpec.ltPredOnOf base x y ks).hasAggAtom = false
  | [] => rfl
  | k :: ks => by
    simp only [OrderSpec.ltPredOnOf, GenPredIn.hasAggAtom, hb k,
      hasAggAtom_ltPredOnOf base x y hb ks, Bool.or_false]

theorem hasAggAtom_ltPredOn {p m : ℕ} (o : OrderSpec p)
    (x y : Fin p → TermGIn T c (ColKind.allReg m)) (ks : List (Fin p)) :
    (OrderSpec.ltPredOn o x y ks).hasAggAtom = false :=
  hasAggAtom_ltPredOnOf _ x y (fun k => by
    show (OrderCol.ltPred (o k) (x k) (y k)).hasAggAtom = false
    unfold OrderCol.ltPred; split_ifs <;> rfl) ks

theorem hasAggAtom_halvesLt (K' : ℕ) : (halvesLt (c := c) (T := T) K').hasAggAtom = false :=
  hasAggAtom_ltPredOn _ _ _ _

theorem hasAggAtom_midLt (K' : ℕ) : (midLt (c := c) (T := T) K').hasAggAtom = false := by
  simp only [midLt, GenPredIn.hasAggAtom, hasAggAtom_ltPredOn, Bool.or_false]

theorem hasAggAtom_eqOuter (n K' : ℕ) : (eqOuter (c := c) (T := T) n K').hasAggAtom = false := by
  unfold eqOuter
  generalize List.finRange K' = ks
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [List.map_cons, List.foldr_cons, GenPredIn.hasAggAtom, ih,
      Bool.or_false]

theorem holdsPlain_halvesLt (K' : ℕ) (a b : Tuple T K') (γ : Fin c → T)
    (ha : ∀ k, ValueType.isNull (a k) = false) (hb : ∀ k, ValueType.isNull (b k) = false) :
    (halvesLt K').holdsPlain (Fin.append a b) γ ↔ ascLt K' a b := by
  have hx : (fun k => (TermGIn.index (T := T) (c := c) (κ := ColKind.allReg (K' + K'))
      (Fin.castAdd K' k) rfl).evalPlain (Fin.append a b) γ) = a :=
    funext fun k => Fin.append_left a b k
  have hy : (fun k => (TermGIn.index (T := T) (c := c) (κ := ColKind.allReg (K' + K'))
      (Fin.natAdd K' k) rfl).evalPlain (Fin.append a b) γ) = b :=
    funext fun k => Fin.append_right a b k
  rw [halvesLt, holdsPlain_ltPredOn_asc _ _ _ _ (fun k => (congrFun hx k).symm ▸ ha k)
    (fun k => (congrFun hy k).symm ▸ hb k), hx, hy]

/-- **The ordered pairs of counters**, each once, annotated `𝟙`. -/
theorem ann_ctrLt (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) :
    (ctrLt EQ K').ann d γ E
      = ((((W.product W).filter (fun p => ascLt K' p.1 p.2)).map
          (fun p => (Fin.append p.1 p.2 : Tuple T (K' + K')))).map
          (fun u => ((u, 1) : AnnotatedTuple T K (K' + K')))) := by
  rw [ctrLt, ann_sel _ _ _ (hasAggAtom_halvesLt K'), ann_prodA, hW, product_map_map',
    Multiset.map_map, Multiset.filter_map, Multiset.map_map]
  have hf : Multiset.filter ((fun p : AnnotatedTuple T K (K' + K') =>
        (halvesLt K').holdsPlain p.1 γ)
      ∘ ((fun p => ((Fin.append p.1.1 p.2.1, p.1.2 * p.2.2) : AnnotatedTuple T K (K' + K')))
        ∘ fun p => (((p.1, 1) : AnnotatedTuple T K K'), ((p.2, 1) : AnnotatedTuple T K K'))))
      (W.product W) = (W.product W).filter (fun p => ascLt K' p.1 p.2) := by
    refine Multiset.filter_congr fun p hp => ?_
    obtain ⟨h₁, h₂⟩ := Multiset.mem_product.1 hp
    exact holdsPlain_halvesLt K' p.1 p.2 γ (hnn _ h₁) (hnn _ h₂)
  refine (congrArg (Multiset.map _) hf).trans ?_
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp, mul_one]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- **`𝟙` minus the weight of rows annotated `𝟙`** is `𝟙` where there is
none and `𝟘` where there is one. -/
theorem one_sub_wt_ones {α : Type} [DecidableEq α] (X : Multiset (α × K))
    (h1 : ∀ p ∈ X, p.2 = 1) (x : α) :
    ((1 : K) - PathSum.wt X x : K) = if x ∈ PathSum.supp X then 0 else 1 := by
  split_ifs with hx
  · obtain ⟨p, hp, rfl⟩ := PathSum.mem_supp.1 hx
    have hle : (1 : K) ≤ PathSum.wt X p.1 := by
      unfold PathSum.wt
      rw [← h1 p hp]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.snd
        (Multiset.mem_filter.2 ⟨hp, rfl⟩ : p ∈ X.filter (fun q => q.1 = p.1)))
    refine le_antisymm ?_ zero_le
    rw [SemiringWithMonus.monus_spec, add_zero]
    exact hle
  · rw [PathSum.wt_eq_zero_of_notMem hx, monus_zero]

theorem holdsPlain_and' {m : ℕ} (φ ψ : GenPredIn T c (ColKind.allReg m)) (u : Tuple T m)
    (γ : Fin c → T) : (GenPredIn.and φ ψ).holdsPlain u γ ↔ φ.holdsPlain u γ ∧ ψ.holdsPlain u γ :=
  Kleene.and_eq_true_iff _ _

theorem holdsPlain_midLt (K' : ℕ) (a m b : Tuple T K') (γ : Fin c → T)
    (ha : ∀ k, ValueType.isNull (a k) = false) (hm : ∀ k, ValueType.isNull (m k) = false)
    (hb : ∀ k, ValueType.isNull (b k) = false) :
    (midLt K').holdsPlain (Fin.append (Fin.append a m) b) γ ↔ ascLt K' a m ∧ ascLt K' m b := by
  have e₁ : (fun k => (TermGIn.index (T := T) (c := c) (κ := ColKind.allReg ((K' + K') + K'))
      (Fin.castAdd K' (Fin.castAdd K' k)) rfl).evalPlain (Fin.append (Fin.append a m) b) γ) = a :=
    funext fun k => by simp [TermGIn.evalPlain, Fin.append_left]
  have e₂ : (fun k => (TermGIn.index (T := T) (c := c) (κ := ColKind.allReg ((K' + K') + K'))
      (Fin.castAdd K' (Fin.natAdd K' k)) rfl).evalPlain (Fin.append (Fin.append a m) b) γ) = m :=
    funext fun k => by
      show Fin.append (Fin.append a m) b (Fin.castAdd K' (Fin.natAdd K' k)) = m k
      rw [Fin.append_left, Fin.append_right]
  have e₃ : (fun k => (TermGIn.index (T := T) (c := c) (κ := ColKind.allReg ((K' + K') + K'))
      (Fin.natAdd (K' + K') k) rfl).evalPlain (Fin.append (Fin.append a m) b) γ) = b :=
    funext fun k => by simp [TermGIn.evalPlain, Fin.append_right]
  rw [midLt, holdsPlain_and',
    holdsPlain_ltPredOn_asc _ _ _ _ (fun k => (congrFun e₁ k).symm ▸ ha k)
      (fun k => (congrFun e₂ k).symm ▸ hm k),
    holdsPlain_ltPredOn_asc _ _ _ _ (fun k => (congrFun e₂ k).symm ▸ hm k)
      (fun k => (congrFun e₃ k).symm ▸ hb k), e₁, e₂, e₃]

/-- **The pairs of counters with one between**, once per counter between,
annotated `𝟙`. -/
theorem ann_ctrMid (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) :
    (ctrMid EQ K').ann d γ E
      = ((((W.product W).product W).filter
          (fun p => ascLt K' p.1.1 p.1.2 ∧ ascLt K' p.1.2 p.2)).map
          (fun p => (Fin.append p.1.1 p.2 : Tuple T (K' + K')))).map
          (fun u => ((u, 1) : AnnotatedTuple T K (K' + K'))) := by
  rw [ctrMid, ann_keepCols, ann_sel _ _ _ (hasAggAtom_midLt K'), ann_prodA, ann_prodA, hW,
    product_map_map' (fun v => ((v, 1) : AnnotatedTuple T K K'))
      (fun v => ((v, 1) : AnnotatedTuple T K K')) W W, Multiset.map_map,
    product_map_map' _ (fun v => ((v, 1) : AnnotatedTuple T K K')) (W.product W) W,
    Multiset.map_map, Multiset.filter_map, Multiset.map_map, Multiset.map_map]
  apply map_filter_congr
  · intro p hp
    obtain ⟨h₁₂, h₃⟩ := Multiset.mem_product.1 hp
    obtain ⟨h₁, h₂⟩ := Multiset.mem_product.1 h₁₂
    exact holdsPlain_midLt K' _ _ _ γ (hnn _ h₁) (hnn _ h₂) (hnn _ h₃)
  · intro p _ _
    simp only [Function.comp, mul_one]
    refine Prod.ext (funext fun j => ?_) rfl
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · show Fin.append (Fin.append p.1.1 p.1.2) p.2 (outerThirds K' (Fin.castAdd K' i)) = _
      simp only [outerThirds, Fin.addCases_left, Fin.append_left]
    · show Fin.append (Fin.append p.1.1 p.1.2) p.2 (outerThirds K' (Fin.natAdd K' i)) = _
      simp only [outerThirds, Fin.addCases_right, Fin.append_right]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem append_eq_append_iff {a b : ℕ} {x x' : Tuple T a} {y y' : Tuple T b} :
    (Fin.append x y : Tuple T (a + b)) = Fin.append x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    refine ⟨funext fun k => ?_, funext fun k => ?_⟩
    · have := congrFun h (Fin.castAdd b k); rwa [Fin.append_left, Fin.append_left] at this
    · have := congrFun h (Fin.natAdd a k); rwa [Fin.append_right, Fin.append_right] at this
  · rintro ⟨rfl, rfl⟩; rfl

/-- The tuples of the ordered pairs of counters. -/
def ltPairs {K' : ℕ} (W : Multiset (Tuple T K')) : Multiset (Tuple T (K' + K')) :=
  ((W.product W).filter (fun p => ascLt K' p.1 p.2)).map (fun p => Fin.append p.1 p.2)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem mem_ltPairs {K' : ℕ} {W : Multiset (Tuple T K')} (a b : Tuple T K') :
    Fin.append a b ∈ ltPairs W ↔ a ∈ W ∧ b ∈ W ∧ ascLt K' a b := by
  simp only [ltPairs, Multiset.mem_map, Multiset.mem_filter]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨hab, hlt⟩, he⟩
    obtain ⟨ha, hb⟩ := Multiset.mem_product.1 hab
    obtain ⟨rfl, rfl⟩ := append_eq_append_iff.1 he
    exact ⟨ha, hb, hlt⟩
  · rintro ⟨ha, hb, hlt⟩
    exact ⟨(a, b), ⟨Multiset.mem_product.2 ⟨ha, hb⟩, hlt⟩, rfl⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem nodup_ltPairs {K' : ℕ} {W : Multiset (Tuple T K')} (hW : W.Nodup) : (ltPairs W).Nodup :=
  Multiset.Nodup.map_on (fun p _ q _ h => by
    obtain ⟨h₁, h₂⟩ := append_eq_append_iff.1 h; exact Prod.ext h₁ h₂)
    (Multiset.Nodup.filter _ (Multiset.Nodup.product hW hW))

open Classical in
/-- **The successor relation's weights**: `𝟙` on a pair with nothing
between, `𝟘` on any other ordered pair, and no row elsewhere. -/
theorem wt_ctrSucc (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hWn : W.Nodup)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (a b : Tuple T K') :
    PathSum.wt ((ctrSucc EQ K').ann d γ E) (Fin.append a b)
      = if a ∈ W ∧ b ∈ W ∧ ascLt K' a b then
          (if ∃ m ∈ W, ascLt K' a m ∧ ascLt K' m b then 0 else 1) else 0 := by
  have hS : (ctrSucc EQ K').ann d γ E = (ltPairs W).map (fun u =>
      ((u, (1 : K) - PathSum.wt ((ctrMid EQ K').ann d γ E) u) : AnnotatedTuple T K (K' + K'))) := by
    rw [ctrSucc, ann_diff, ann_ctrLt EQ K' d γ E W hW hnn, Multiset.map_map]
    rfl
  rw [hS, PathSum.wt_map_nodup (nodup_ltPairs hWn)]
  have hiff : Fin.append a b ∈ ltPairs W ↔ a ∈ W ∧ b ∈ W ∧ ascLt K' a b := mem_ltPairs a b
  have hones : ∀ p ∈ (ctrMid EQ K').ann d γ E, p.2 = 1 := by
    rw [ann_ctrMid EQ K' d γ E W hW hnn]
    intro p hp
    obtain ⟨_, _, rfl⟩ := Multiset.mem_map.1 hp
    rfl
  have hsupp : Fin.append a b ∈ PathSum.supp ((ctrMid EQ K').ann d γ E)
      ↔ ∃ m ∈ W, a ∈ W ∧ b ∈ W ∧ ascLt K' a m ∧ ascLt K' m b := by
    rw [ann_ctrMid EQ K' d γ E W hW hnn, PathSum.supp_map]
    simp only [Multiset.mem_toFinset, Multiset.map_id', Multiset.mem_map, Multiset.mem_filter]
    constructor
    · rintro ⟨⟨⟨a', m⟩, b'⟩, ⟨hp, h₁m, hm₂⟩, he⟩
      obtain ⟨h₁₂, hb'⟩ := Multiset.mem_product.1 hp
      obtain ⟨ha', hm⟩ := Multiset.mem_product.1 h₁₂
      obtain ⟨rfl, rfl⟩ := append_eq_append_iff.1 he
      exact ⟨m, hm, ha', hb', h₁m, hm₂⟩
    · rintro ⟨m, hm, ha, hb, h₁m, hm₂⟩
      exact ⟨((a, m), b), ⟨Multiset.mem_product.2 ⟨Multiset.mem_product.2 ⟨ha, hm⟩, hb⟩,
        h₁m, hm₂⟩, rfl⟩
  by_cases h₁ : a ∈ W ∧ b ∈ W ∧ ascLt K' a b
  · rw [ite_eq_left (hiff.2 h₁), ite_eq_left h₁, one_sub_wt_ones _ hones]
    by_cases h₂ : ∃ m ∈ W, ascLt K' a m ∧ ascLt K' m b
    · obtain ⟨m, hm, h₁m, hm₂⟩ := h₂
      rw [ite_eq_left (hsupp.2 ⟨m, hm, h₁.1, h₁.2.1, h₁m, hm₂⟩), ite_eq_left ⟨m, hm, h₁m, hm₂⟩]
    · rw [ite_eq_right (fun h => h₂ (by
        obtain ⟨m, hm, -, -, h₁m, hm₂⟩ := hsupp.1 h; exact ⟨m, hm, h₁m, hm₂⟩)), ite_eq_right h₂]
  · rw [ite_eq_right (fun h => h₁ (hiff.1 h)), ite_eq_right h₁]

open Classical in
/-- **The least counter's weights**: `𝟙` on the least counter, `𝟘` on the
others. -/
theorem wt_ctrLeast (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hWn : W.Nodup)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (b : Tuple T K') :
    PathSum.wt ((ctrLeast EQ K').ann d γ E) b
      = if b ∈ W then (if ∃ a ∈ W, ascLt K' a b then 0 else 1) else 0 := by
  set P := (keepCols (fun j => Fin.natAdd K' j) (ctrLt EQ K')).ann d γ E with hP
  have hPe : P = (ltPairs W).map (fun u =>
      (((fun j => u (Fin.natAdd K' j)), 1) : AnnotatedTuple T K K')) := by
    rw [hP, ann_keepCols, ann_ctrLt EQ K' d γ E W hW hnn, Multiset.map_map]
    rfl
  have hL : (ctrLeast EQ K').ann d γ E
      = W.map (fun v => ((v, (1 : K) - PathSum.wt P v) : AnnotatedTuple T K K')) := by
    rw [ctrLeast, ann_diff, hW, Multiset.map_map]
    rfl
  have hones : ∀ p ∈ P, p.2 = 1 := by
    rw [hPe]; intro p hp; obtain ⟨_, _, rfl⟩ := Multiset.mem_map.1 hp; rfl
  have hsupp : b ∈ PathSum.supp P ↔ ∃ a ∈ W, b ∈ W ∧ ascLt K' a b := by
    rw [hPe, PathSum.supp_map]
    simp only [Multiset.mem_toFinset, Multiset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨⟨a', b'⟩, hab, rfl⟩ := Multiset.mem_map.1 hu
      obtain ⟨hp, hlt⟩ := Multiset.mem_filter.1 hab
      obtain ⟨ha', hb'⟩ := Multiset.mem_product.1 hp
      have e : (fun j => (Fin.append a' b' : Tuple T (K' + K')) (Fin.natAdd K' j)) = b' :=
        funext fun j => Fin.append_right a' b' j
      refine ⟨a', ha', ?_, ?_⟩
      · show (fun j => (Fin.append a' b' : Tuple T (K' + K')) (Fin.natAdd K' j)) ∈ W
        rw [e]; exact hb'
      · show ascLt K' a' (fun j => (Fin.append a' b' : Tuple T (K' + K')) (Fin.natAdd K' j))
        rw [e]; exact hlt
    · rintro ⟨a, ha, hb, hlt⟩
      exact ⟨Fin.append a b, (mem_ltPairs a b).2 ⟨ha, hb, hlt⟩,
        funext fun j => Fin.append_right a b j⟩
  rw [hL, PathSum.wt_map_nodup hWn]
  by_cases hb : b ∈ W
  · rw [ite_eq_left hb, ite_eq_left hb, one_sub_wt_ones _ hones]
    by_cases ha : ∃ a ∈ W, ascLt K' a b
    · obtain ⟨a, ha, hlt⟩ := ha
      rw [ite_eq_left (hsupp.2 ⟨a, ha, hb, hlt⟩), ite_eq_left ⟨a, ha, hlt⟩]
    · rw [ite_eq_right (fun h => ha (by obtain ⟨a, ha, -, hlt⟩ := hsupp.1 h; exact ⟨a, ha, hlt⟩)),
        ite_eq_right ha]
  · rw [ite_eq_right hb, ite_eq_right hb]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **Reading the second half of the rows whose first half is `a`.** -/
theorem wt_halves {K' : ℕ} (X : Multiset (Tuple T (K' + K') × K)) (a b : Tuple T K') :
    PathSum.wt ((X.filter (fun p => (fun k => p.1 (Fin.castAdd K' k)) = a)).map
        (fun p => (((fun j => p.1 (Fin.natAdd K' j)), p.2) : Tuple T K' × K))) b
      = PathSum.wt X (Fin.append a b) := by
  unfold PathSum.wt
  rw [Multiset.filter_map, Multiset.map_map, Multiset.filter_filter]
  congr 2
  refine Multiset.filter_congr fun p _ => ?_
  simp only [Function.comp]
  constructor
  · rintro ⟨rfl, rfl⟩; exact Fin.append_castAdd_natAdd.symm
  · rintro he
    rw [he]
    exact ⟨funext fun j => Fin.append_right a b j, funext fun k => Fin.append_left a b k⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem mem_supp_halves {K' : ℕ} (X : Multiset (Tuple T (K' + K') × K)) (a b : Tuple T K') :
    b ∈ PathSum.supp ((X.filter (fun p => (fun k => p.1 (Fin.castAdd K' k)) = a)).map
        (fun p => (((fun j => p.1 (Fin.natAdd K' j)), p.2) : Tuple T K' × K)))
      ↔ Fin.append a b ∈ PathSum.supp X := by
  simp only [PathSum.mem_supp, Multiset.mem_map, Multiset.mem_filter]
  constructor
  · rintro ⟨_, ⟨p, ⟨hp, rfl⟩, rfl⟩, rfl⟩
    exact ⟨p, hp, Fin.append_castAdd_natAdd.symm⟩
  · rintro ⟨p, hp, he⟩
    refine ⟨_, ⟨p, ⟨hp, ?_⟩, rfl⟩, ?_⟩
    · rw [he]; exact funext fun k => Fin.append_left a b k
    · show (fun j => p.1 (Fin.natAdd K' j)) = b
      rw [he]; exact funext fun j => Fin.append_right a b j

theorem holdsPlain_eqOuter (n K' : ℕ) (z : Tuple T (K' + K')) (u : Tuple T (n + K'))
    (γ : Fin c → T) :
    (eqOuter n K').holdsPlain z (Fin.append u γ : Tuple T ((n + K') + c))
      ↔ (fun k => z (Fin.castAdd K' k)) = rightPart n K' u := by
  have key : ∀ ks : List (Fin K'),
      (((ks.map (fun k => GenPredIn.cmp CompOp.syneq
        (TermGIn.index (T := T) (c := (n + K') + c) (κ := ColKind.allReg (K' + K'))
          (Fin.castAdd K' k) rfl)
        (TermGIn.outer (Fin.castAdd c (Fin.natAdd n k))))).foldr GenPredIn.and truePred).holdsPlain
          z (Fin.append u γ) ↔ ∀ k ∈ ks, z (Fin.castAdd K' k) = rightPart n K' u k) := by
    intro ks
    induction ks with
    | nil => simp only [List.map_nil, List.foldr_nil, List.not_mem_nil, false_imp_iff,
        imp_true_iff, iff_true]; exact holdsPlain_truePred z _
    | cons k ks ih =>
      rw [List.map_cons, List.foldr_cons, holdsPlain_and', ih, List.forall_mem_cons]
      apply and_congr_left'
      show CompOp.syneq.eval3 _ _ = Kleene.true ↔ _
      rw [CompOp.syneq_eval3_eq_true_iff]
      show z (Fin.castAdd K' k) = (Fin.append u γ : Tuple T ((n + K') + c))
        (Fin.castAdd c (Fin.natAdd n k)) ↔ _
      rw [Fin.append_left]
      rfl
  rw [eqOuter, key]
  exact ⟨fun h => funext fun k => h k (List.mem_finRange k), fun h k _ => congrFun h k⟩

/-- **The counters after the current row's**, read off the successor
relation. -/
theorem ann_ctrNext (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (n K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E' : EvalEnv T K)
    (x : Tuple (GenValue T K) (n + K')) (u : Tuple T (n + K')) :
    (ctrNext EQ n K').ann d (Fin.append u γ) (E'.withCtx (Fin.append x (E'.ctxAt c γ)))
      = (((ctrSucc EQ K').ann d γ E').filter
          (fun p => (fun k => p.1 (Fin.castAdd K' k)) = rightPart n K' u)).map
          (fun p => (((fun j => p.1 (Fin.natAdd K' j)), p.2) : AnnotatedTuple T K K')) := by
  rw [ctrNext, ann_keepCols, ann_sel _ _ _ (hasAggAtom_eqOuter n K')]
  have h : ((ctrSucc EQ K').substMap (applyOuter T c (n + K'))).ann d (Fin.append u γ)
      (E'.withCtx (Fin.append x (E'.ctxAt c γ))) = (ctrSucc EQ K').ann d γ E' := by
    rw [ann, ann, evaluate_applyOuter]
  rw [h]
  congr 1
  exact Multiset.filter_congr fun p _ => holdsPlain_eqOuter n K' p.1 u γ

end CounterAnn

/-! ## One round of the simulation, and its rounds -/

section SimRounds

variable {c : ℕ}

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A row of regular kinds holds its values. -/
theorem eq_inl_of_conforms {n : ℕ} {u : Tuple (GenValue T K) n}
    (h : GenRow.Conforms (ColKind.allReg n) u) :
    u = fun k => Sum.inl (GenRow.plainTuple u k) := by
  funext k
  have hk := h k
  show u k = Sum.inl (AggValue.collapseSum (u k))
  revert hk
  cases u k with
  | inl a => intro _; rfl
  | inr t => intro hk; exact absurd hk (by simp [GenValue.kindOf, ColKind.allReg, ColKind.base])

/-- The right side of one round of the simulation, at a row `u`: the term
at its tuple part, paired with the counters after its counter. -/
noncomputable def simRow (s : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) (u : Tuple T (n + K')) : AnnotatedRelation T K (n + K') :=
  (prodA (castIdx (subIdx_self s n)
      (substRel s (rowPv n K') (L.substMap (applyOuter T c (n + K')))))
    (ctrNext EQ n K')).ann d (Fin.append u γ)
      (E.withCtx (Fin.append (fun k => (Sum.inl (u k) : GenValue T K)) (E.ctxAt c γ)))

/-- **One round of the simulation is linear**: each row of the previous
round gives `simRow` at its tuple, multiplied by its annotation. -/
theorem ann_simBodyA (s s' : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) (X : Multiset (GenRow T K (n + K')))
    (hX : ∀ x ∈ X, GenRow.Conforms (ColKind.allReg (n + K')) x.fst) :
    (simBodyA s s' n K' EQ L).ann d γ (E.assignHole s' X)
      = PathSum.lin (simRow s n K' EQ L d γ E) (X.map GenRow.toAnnotated) := by
  rw [simBodyA, ann_keepCols, ann_castKind]
  simp only [ann, evaluate, EvalEnv.assignHole_holes_self]
  rw [Multiset.filter_eq_self.2 hX]
  unfold PathSum.lin
  rw [Multiset.bind_map, Multiset.map_bind, Multiset.map_bind]
  refine Multiset.bind_congr fun x hx => ?_
  have hreg := eq_inl_of_conforms (hX x hx)
  have henv : (simRow s n K' EQ L d γ E (GenRow.toAnnotated x).1)
      = ((prodA (castIdx (subIdx_self s n) (substRel s (rowPv n K')
          (L.substMap (applyOuter T c (n + K')))))
        (ctrNext EQ n K')).evaluate d (Fin.append (GenRow.plainTuple x.fst) γ)
          ((E.assignHole s' X).withCtx (Fin.append x.fst ((E.assignHole s' X).ctxAt c γ)))).map
        GenRow.toAnnotated := by
    rw [simRow, ann]
    congr 1
    refine evaluate_congr_holes _ d _ (fun _ hp => absurd hp List.not_mem_nil) ?_
    simp only [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_assignHole]
    exact congrArg (fun v => Fin.append v (E.ctxAt c γ)) hreg.symm
  rw [henv, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun y _ => ?_
  simp only [Function.comp, GenRow.toAnnotated]
  refine Prod.ext (funext fun j => ?_) (GenAnn.finalize_mul' x.snd y.snd)
  simp only [GenRow.plainTuple, Fin.append_right]

/-- **The simulation's rounds, annotated**: the bag recursion of `PathSum`
with the linear step `simRow`, wherever those rounds end. -/
theorem ann_simA (s s' : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (hk : ∃ k, (PathSum.lin (simRow s n K' EQ L d γ E))^[k + 1]
      ((prodA BQ (ctrLeast EQ K')).ann d γ E) = 0) :
    (simA s s' n K' EQ BQ L).ann d γ E
      = muSumFix (PathSum.lin (simRow s n K' EQ L d γ E))
          ((prodA BQ (ctrLeast EQ K')).ann d γ E) := by
  set step : Multiset (GenRow T K (n + K')) → Multiset (GenRow T K (n + K')) :=
    fun X => (simBodyA s s' n K' EQ L).evaluate d γ (E.assignHole s' X) with hstepdef
  set M := (prodA BQ (ctrLeast EQ K')).evaluate d γ E with hM
  have hconf : ∀ i, ∀ x ∈ step^[i] M, GenRow.Conforms (ColKind.allReg (n + K')) x.fst := by
    intro i x hx
    cases i with
    | zero => exact fun k => evaluate_conform _ d x hx k
    | succ i =>
      rw [Function.iterate_succ_apply'] at hx
      exact fun k => evaluate_conform _ d x hx k
  have hiter : ∀ i, (step^[i] M).map GenRow.toAnnotated
      = (PathSum.lin (simRow s n K' EQ L d γ E))^[i] ((prodA BQ (ctrLeast EQ K')).ann d γ E) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact ann_simBodyA s s' n K' EQ L d γ E _ (hconf i)
  have hz : step 0 = 0 := by
    simp only [hstepdef, simBodyA, keepCols, evaluate_castKind, evaluate,
      EvalEnv.assignHole_holes_self, Multiset.filter_zero, Multiset.zero_bind, Multiset.map_zero]
  have hm : MuSettles step M := by
    obtain ⟨k, hk⟩ := hk
    refine ⟨k, ?_⟩
    rw [← hiter] at hk
    exact Multiset.map_eq_zero.1 hk
  show (muSumFix step M).map GenRow.toAnnotated = _
  refine (muSumFix_map_rounds (h := Multiset.map GenRow.toAnnotated) (Multiset.map_zero _)
    (fun x y => Multiset.map_add _ _ _) (fun k => ?_) hz hm)
  exact ann_simBodyA s s' n K' EQ L d γ E _ (hconf k)

/-- The simulation's rounds, as rows, are those of `PathSum.lin` read
through `toAnnotated`. -/
theorem simA_iter (s s' : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    ∀ i, ((muStep s' (simBodyA s s' n K' EQ L) d γ E)^[i]
        ((prodA BQ (ctrLeast EQ K')).evaluate d γ E)).map GenRow.toAnnotated
      = (PathSum.lin (simRow s n K' EQ L d γ E))^[i] ((prodA BQ (ctrLeast EQ K')).ann d γ E) := by
  have hconf : ∀ i, ∀ x ∈ (muStep s' (simBodyA s s' n K' EQ L) d γ E)^[i]
      ((prodA BQ (ctrLeast EQ K')).evaluate d γ E),
      GenRow.Conforms (ColKind.allReg (n + K')) x.fst := by
    intro i x hx
    cases i with
    | zero => exact fun k => evaluate_conform _ d x hx k
    | succ i =>
      rw [Function.iterate_succ_apply'] at hx
      exact fun k => evaluate_conform _ d x hx k
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact ann_simBodyA s s' n K' EQ L d γ E _ (hconf i)

theorem simA_step_zero (s s' : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) : muStep s' (simBodyA s s' n K' EQ L) d γ E 0 = 0 := by
  simp only [muStep, simBodyA, keepCols, evaluate_castKind, evaluate,
    EvalEnv.assignHole_holes_self, Multiset.filter_zero, Multiset.zero_bind, Multiset.map_zero]

end SimRounds

/-! ## The simulation, read as `PathSum.SimSpec` -/

section SimSpecInst

variable {c : ℕ}

/-- **The successor relation**, as one row per ordered pair. -/
theorem ann_ctrSucc_eq (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) :
    (ctrSucc EQ K').ann d γ E = (ltPairs W).map (fun u =>
      ((u, (1 : K) - PathSum.wt ((ctrMid EQ K').ann d γ E) u) : AnnotatedTuple T K (K' + K'))) := by
  rw [ctrSucc, ann_diff, ann_ctrLt EQ K' d γ E W hW hnn, Multiset.map_map]
  rfl

/-- **The least-counter relation**, as one row per counter. -/
theorem ann_ctrLeast_eq (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K'))) :
    ∃ f : Tuple T K' → K, (ctrLeast EQ K').ann d γ E
      = W.map (fun v => ((v, f v) : AnnotatedTuple T K K')) := by
  refine ⟨fun v => (1 : K) - PathSum.wt
    ((keepCols (fun j => Fin.natAdd K' j) (ctrLt EQ K')).ann d γ E) v, ?_⟩
  rw [ctrLeast, ann_diff, hW, Multiset.map_map]
  rfl

theorem supp_ctrSucc (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (a b : Tuple T K') :
    Fin.append a b ∈ PathSum.supp ((ctrSucc EQ K').ann d γ E) ↔ a ∈ W ∧ b ∈ W ∧ ascLt K' a b := by
  rw [ann_ctrSucc_eq EQ K' d γ E W hW hnn, PathSum.supp_map, Multiset.map_id',
    Multiset.mem_toFinset]
  exact mem_ltPairs a b

theorem supp_ctrLeast (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (b : Tuple T K') : b ∈ PathSum.supp ((ctrLeast EQ K').ann d γ E) ↔ b ∈ W := by
  obtain ⟨f, hf⟩ := ann_ctrLeast_eq EQ K' d γ E W hW
  rw [hf, PathSum.supp_map, Multiset.map_id', Multiset.mem_toFinset]

/-- **The term at the current row's tuple**, read through the substitution:
the term with its hole bound to that tuple annotated `𝟙`. -/
theorem ann_substRow (s : String) (n K' : ℕ) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hL : L.recLinear s n) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (u : Tuple T (n + K')) :
    (castIdx (subIdx_self s n) (substRel s (rowPv n K') (L.substMap (applyOuter T c (n + K'))))).ann
        d (Fin.append u γ) (E.withCtx (Fin.append (fun k => (Sum.inl (u k) : GenValue T K))
          (E.ctxAt c γ)))
      = L.ann d γ (E.assignHole s
          ({GenRow.ofAnnotated (leftPart n K' u, 1)} : Multiset (GenRow T K n))) := by
  rw [ann, ann, evaluate_castIdx, evaluate_substRel _ _ ((recLinear_substMap L _).2 hL)]
  have hrow : paramRow (E.withCtx (Fin.append (fun k => (Sum.inl (u k) : GenValue T K))
      (E.ctxAt c γ))) (Fin.append u γ) (rowPv n K')
      = GenRow.ofAnnotated (leftPart n K' u, (1 : K)) := by
    unfold paramRow GenRow.ofAnnotated
    simp only [EvalEnv.ctxAt_withCtx]
    refine Prod.ext (funext fun i => ?_) rfl
    show (Fin.append (fun k => (Sum.inl (u k) : GenValue T K)) (E.ctxAt c γ))
      (Fin.castAdd c (Fin.castAdd K' i)) = _
    rw [Fin.append_left]
    rfl
  rw [hrow]
  have henv : ((E.withCtx (Fin.append (fun k => (Sum.inl (u k) : GenValue T K))
      (E.ctxAt c γ))).assignHole s
        ({GenRow.ofAnnotated (leftPart n K' u, 1)} : Multiset (GenRow T K n)))
      = (E.assignHole s
          ({GenRow.ofAnnotated (leftPart n K' u, 1)} : Multiset (GenRow T K n))).withCtx
          (Fin.append (fun k => (Sum.inl (u k) : GenValue T K))
            ((E.assignHole s ({GenRow.ofAnnotated (leftPart n K' u, 1)}
              : Multiset (GenRow T K n))).ctxAt c γ)) := by
    rw [EvalEnv.ctxAt_assignHole]
    rfl
  rw [henv, evaluate_applyOuter]

/-- Splitting a row of the simulation into its tuple and its counter. -/
def splitRow {n K' : ℕ} (p : AnnotatedTuple T K (n + K')) : (Tuple T n × Tuple T K') × K :=
  ((leftPart n K' p.1, rightPart n K' p.1), p.2)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem lin_map_splitRow {n K' : ℕ} (F : Tuple T (n + K') → AnnotatedRelation T K (n + K'))
    (X : AnnotatedRelation T K (n + K')) :
    PathSum.lin (fun q : Tuple T n × Tuple T K' => (F (Fin.append q.1 q.2)).map splitRow)
        (X.map splitRow)
      = (PathSum.lin F X).map splitRow := by
  unfold PathSum.lin
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ => ?_
  have hp : (Fin.append (leftPart n K' p.1) (rightPart n K' p.1) : Tuple T (n + K')) = p.1 :=
    Fin.append_castAdd_natAdd
  simp only [splitRow, hp, Multiset.map_map]
  rfl

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem rounds_map_splitRow {n K' : ℕ} (F : Tuple T (n + K') → AnnotatedRelation T K (n + K'))
    (X : AnnotatedRelation T K (n + K')) :
    ∀ j, PathSum.rounds (X.map splitRow)
        (fun q : Tuple T n × Tuple T K' => (F (Fin.append q.1 q.2)).map splitRow) j
      = ((PathSum.lin F)^[j] X).map splitRow
  | 0 => rfl
  | j + 1 => by
    rw [PathSum.rounds, rounds_map_splitRow F X j, lin_map_splitRow,
      Function.iterate_succ_apply']

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem muSum_eq_sum {α : Type} (step : Multiset α → Multiset α) :
    ∀ (k : ℕ) (M : Multiset α), muSum step k M = ∑ j ∈ Finset.range (k + 1), step^[j] M
  | 0, M => by simp [muSum]
  | k + 1, M => by
    rw [muSum, muSum_eq_sum step k (step M), Finset.sum_range_succ' _ (k + 1)]
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
    exact add_comm _ _

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **A bag recursion whose `L`-th round is empty is the sum of its first
`L` rounds.** -/
theorem muSumFix_eq_sum {α : Type} {step : Multiset α → Multiset α} (h0 : step 0 = 0)
    {M : Multiset α} {L : ℕ} (hL : step^[L + 1] M = 0) :
    muSumFix step M = ∑ j ∈ Finset.range (L + 1), step^[j] M := by
  rw [muSumFix_eq_of_empty h0 hL, muSum_eq_sum]

theorem evaluate_dedup_eq {c n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (Dedup q).evaluate d γ E = (PathSum.dedupK (q.ann d γ E)).map GenRow.ofAnnotated := by
  simp only [evaluate, ann]
  rw [groupByKey_eq_dedup_map]
  rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem ascLt_irrefl' {K' : ℕ} (x : Tuple T K') : ¬ ascLt K' x x := by
  intro h; unfold ascLt at h; rw [OrderSpec.lt_irrefl] at h; exact absurd h (by simp)

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem ascLt_trans' {K' : ℕ} (x y z : Tuple T K') (h₁ : ascLt K' x y) (h₂ : ascLt K' y z) :
    ascLt K' x z :=
  OrderSpec.lt_trans' (OrderSpec.asc K') h₁ h₂

open Classical in
omit [DecidableEq K] [HasAltLinearOrder K] in
theorem firstInd_eq_of_sorted {K' : ℕ} {W : Multiset (Tuple T K')} {l : List (Tuple T K')}
    (hl : l.Pairwise (ascLt K')) (hmem : ∀ x, x ∈ l ↔ x ∈ W) (b : Tuple T K') :
    (if b ∈ W then (if ∃ a ∈ W, ascLt K' a b then (0 : K) else 1) else 0)
      = PathSum.firstInd l b := by
  unfold PathSum.firstInd
  by_cases hb : b ∈ W
  · rw [ite_eq_left hb]
    have := PathSum.getElem_zero_eq_iff hl ascLt_irrefl' ascLt_trans' ((hmem b).2 hb)
    by_cases ha : ∃ a ∈ W, ascLt K' a b
    · rw [ite_eq_left ha, ite_eq_right (fun h => (this.1 h)
        (by obtain ⟨a, ha, hab⟩ := ha; exact ⟨a, (hmem a).2 ha, hab⟩))]
    · rw [ite_eq_right ha, ite_eq_left (this.2 (fun ⟨a, ha', hab⟩ => ha ⟨a, (hmem a).1 ha', hab⟩))]
  · rw [ite_eq_right hb, ite_eq_right (fun h => hb ((hmem b).1 (List.mem_of_getElem? h)))]

open Classical in
omit [DecidableEq K] [HasAltLinearOrder K] in
theorem succInd_eq_of_sorted {K' : ℕ} {W : Multiset (Tuple T K')} {l : List (Tuple T K')}
    (hl : l.Pairwise (ascLt K')) (hmem : ∀ x, x ∈ l ↔ x ∈ W) {a : Tuple T K'} (ha : a ∈ l)
    (b : Tuple T K') :
    (if a ∈ W ∧ b ∈ W ∧ ascLt K' a b then
        (if ∃ m ∈ W, ascLt K' a m ∧ ascLt K' m b then (0 : K) else 1) else 0)
      = PathSum.succInd l a b := by
  unfold PathSum.succInd
  have hnd := PathSum.nodup_of_sorted hl ascLt_irrefl'
  by_cases hab : a ∈ W ∧ b ∈ W ∧ ascLt K' a b
  · rw [ite_eq_left hab]
    have key := PathSum.getElem_idxOf_succ_eq_iff hl ascLt_irrefl' ascLt_trans' ha
      ((hmem b).2 hab.2.1) hab.2.2
    by_cases hm : ∃ m ∈ W, ascLt K' a m ∧ ascLt K' m b
    · rw [ite_eq_left hm, ite_eq_right (fun h => (key.1 h.2)
        (by obtain ⟨m, hm, h₁, h₂⟩ := hm; exact ⟨m, (hmem m).2 hm, h₁, h₂⟩))]
    · rw [ite_eq_right hm, ite_eq_left ⟨ha, key.2 (fun ⟨m, hm', h₁, h₂⟩ =>
        hm ⟨m, (hmem m).1 hm', h₁, h₂⟩)⟩]
  · rw [ite_eq_right hab, ite_eq_right]
    rintro ⟨-, h⟩
    apply hab
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    rw [hnd.idxOf_getElem] at h
    obtain ⟨hi', he⟩ := List.getElem?_eq_some_iff.1 h
    refine ⟨(hmem _).1 ha, (hmem _).1 (he ▸ List.getElem_mem hi'), ?_⟩
    rw [← he]
    exact (PathSum.sorted_lt_iff hl ascLt_irrefl' ascLt_trans' hi hi').2 (by omega)

/-- **The simulation's rounds are those of `PathSum.SimSpec`**, for a
sorted listing `l` of the counters. -/
theorem simSpec_of (s : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hL : L.recLinear s n) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (W : Multiset (Tuple T K')) (hWn : W.Nodup)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) :
    ∃ l : List (Tuple T K'), l.Pairwise (ascLt K') ∧ l.length = W.card ∧ (∀ x, x ∈ l ↔ x ∈ W) ∧
      PathSum.SimSpec (ascLt K') l (BQ.ann d γ E)
        (fun u => L.ann d γ (E.assignHole s
          ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))))
        (((prodA BQ (ctrLeast EQ K')).ann d γ E).map splitRow)
        (fun q : Tuple T n × Tuple T K' =>
          (simRow s n K' EQ L d γ E (Fin.append q.1 q.2)).map splitRow) := by
  set B := BQ.ann d γ E with hBdef
  set G := fun u => L.ann d γ (E.assignHole s
    ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) with hGdef
  obtain ⟨l, hlsort, hlen, hlmem⟩ := exists_sorted_counters K' W.toFinset
  have hcardW : W.toFinset.card = W.card := Multiset.toFinset_card_of_nodup hWn
  have hlnd : l.Nodup := PathSum.nodup_of_sorted hlsort ascLt_irrefl'
  have hmem : ∀ x, x ∈ l ↔ x ∈ W := by
    have hsub : l.toFinset ⊆ W.toFinset := fun x hx => hlmem x (List.mem_toFinset.1 hx)
    have heq : l.toFinset = W.toFinset := Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hlnd, hlen])
    intro x
    rw [← List.mem_toFinset, heq, Multiset.mem_toFinset]
  refine ⟨l, hlsort, hlen.trans hcardW, hmem, ?_⟩
  set base := (prodA BQ (ctrLeast EQ K')).ann d γ E with hbase
  set F := simRow s n K' EQ L d γ E with hF
  have hpair : ∀ {a b : ℕ} (X : AnnotatedRelation T K a) (Y : AnnotatedRelation T K b),
      ((X.product Y).map (fun p => ((Fin.append p.1.1 p.2.1, p.1.2 * p.2.2)
        : AnnotatedTuple T K (a + b)))).map splitRow
      = (X.product Y).map (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2)) := by
    intro a b X Y
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun p _ => ?_
    simp only [Function.comp, splitRow, leftPart_append, rightPart_append]
  have hB'e : base.map splitRow = (B.product ((ctrLeast EQ K').ann d γ E)).map
      (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2)) := by
    rw [hbase, ann_prodA, hpair]
  have hG'e : ∀ t c₀, (F (Fin.append t c₀)).map splitRow
      = ((G t).product ((((ctrSucc EQ K').ann d γ E).filter
      (fun p => (fun k => p.1 (Fin.castAdd K' k)) = c₀)).map
        (fun p => (((fun j => p.1 (Fin.natAdd K' j)), p.2) : AnnotatedTuple T K K')))).map
      (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2)) := by
    intro t c₀
    rw [hF]
    simp only [simRow]
    rw [ann_prodA, ann_substRow s n K' L hL, ann_ctrNext, hpair, leftPart_append,
      rightPart_append]
    rfl
  refine ⟨hlsort, ascLt_irrefl', ascLt_trans', fun t c₀ => ?_, fun t c₀ => ?_,
    fun t c₀ hc t' c' => ?_, fun t c₀ hc t' c' => ?_⟩
  · rw [hB'e]
    erw [PathSum.wt_product]
    rw [wt_ctrLeast EQ K' d γ E W hWn hW hnn, firstInd_eq_of_sorted hlsort hmem]
  · rw [hB'e]
    erw [PathSum.mem_supp_product]
    rw [supp_ctrLeast EQ K' d γ E W hW, hmem]
  · show PathSum.wt ((F (Fin.append t c₀)).map splitRow) (t', c') = _
    rw [hG'e]
    erw [PathSum.wt_product]
    erw [wt_halves]
    rw [wt_ctrSucc EQ K' d γ E W hWn hW hnn, succInd_eq_of_sorted hlsort hmem hc]
  · show (t', c') ∈ PathSum.supp ((F (Fin.append t c₀)).map splitRow) ↔ _
    rw [hG'e]
    erw [PathSum.mem_supp_product]
    erw [mem_supp_halves]
    rw [supp_ctrSucc EQ K' d γ E W hW hnn, hmem]
    exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, (hmem c₀).1 hc, h.2.1, h.2.2⟩⟩

/-- **The annotated simulation computes the set recursion.** Where the
counters are the `K'`-tuples `W` over values none of which is the null,
each row annotated `𝟙`, and there are at least as many counters as tuples
in a set `S` closed under the recursion's rounds, in a semiring where a
linear recursion settles within `|S|` rounds if at all, the simulation's
value is the set recursion's wherever the latter settles. -/
theorem evaluate_simResultA (s s' : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hL : L.recLinear s n) (hLx : L.noExplode) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (W : Multiset (Tuple T K')) (hWn : W.Nodup)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (S : Finset (Tuple T n))
    (hS : PathSum.Closed S (BQ.ann d γ E) (fun u => L.ann d γ (E.assignHole s
      ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))))
    (hcard : S.card ≤ W.card) (hK : PathSum.SettlesEarly K)
    (hset : MuSetSettles (muSetStep s BQ L d γ E)) :
    (simResultA s s' n K' EQ BQ L).evaluate d γ E = (MuSet s BQ L).evaluate d γ E := by
  set B := BQ.ann d γ E with hBdef
  set G := fun u => L.ann d γ (E.assignHole s
    ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) with hGdef
  have hstep : muSetStep s BQ L d γ E = PathSum.stepK B G := funext fun X => by
    rw [muSetStep, dedupAnn_eq_dedupK, PathSum.stepK]
    congr 2
    exact ann_of_recLinear L hL hLx d γ E X
  rw [hstep] at hset
  obtain ⟨l, -, hlen, -, hspec⟩ := simSpec_of s n K' EQ BQ L hL d γ E W hWn hW hnn
  -- the set recursion, as the `|l|`-th iterate
  rw [evaluate_MuSet_of_recLinear s BQ L hL hLx d γ E]
  have hfix : muFix (PathSum.stepK B G) = (PathSum.stepK B G)^[l.length] 0 := by
    rw [← muIter_eq_iterate]
    apply muFix_eq_of_fix
    have h := PathSum.iterate_succ_eq_of_settles hS hK hset (M := l.length)
      (by rw [hlen]; exact hcard)
    rw [Function.iterate_succ_apply'] at h
    rw [muIter_eq_iterate]
    exact h
  rw [hfix, PathSum.iterate_stepK_eq]
  set base := (prodA BQ (ctrLeast EQ K')).ann d γ E with hbase
  set F := simRow s n K' EQ L d γ E with hF
  -- the simulation's rounds end, and its value is their sum
  have hzero : (PathSum.lin F)^[l.length] base = 0 := by
    have h := hspec.rounds_eq_zero (le_refl l.length)
    rw [rounds_map_splitRow] at h
    exact Multiset.map_eq_zero.1 h
  have hk : ∃ k, (PathSum.lin F)^[k + 1] base = 0 :=
    ⟨l.length, by rw [Function.iterate_succ_apply', hzero, PathSum.lin_zero]⟩
  rw [simResultA, evaluate_dedup_eq, ann_keepCols, ann_simA s s' n K' EQ BQ L d γ E hk,
    muSumFix_eq_sum (PathSum.lin_zero F) (L := l.length)
      (by rw [Function.iterate_succ_apply', hzero, PathSum.lin_zero])]
  congr 1
  have hproj : ∀ X : Multiset (Tuple T (n + K') × K),
      X.map (fun p => ((fun i => p.1 (Fin.castAdd K' i), p.2) : AnnotatedTuple T K n))
        = (X.map splitRow).map PathSum.dropCtr := fun X => by
    rw [Multiset.map_map]; rfl
  have hsum : ∀ (S' : Finset ℕ) (X : ℕ → Multiset (Tuple T (n + K') × K)),
      (∑ j ∈ S', X j).map splitRow = ∑ j ∈ S', (X j).map splitRow := by
    intro S' X
    induction S' using Finset.induction_on with
    | empty => simp
    | insert j S' hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Multiset.map_add, ih]
  erw [hproj, hsum]
  simp only [← rounds_map_splitRow]
  exact hspec.dedupK_rounds hS (Nat.le_succ _)

end SimSpecInst

/-! ## Settling -/

section Settle

/-- **A recursion-free query settles everywhere.** -/
theorem annSettlesAt_of_noRec :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noRec → ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K),
        q.AnnSettlesAt d γ E := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ _ => trivial
  | Hole _ _ _ => exact fun _ _ _ _ => trivial
  | Param _ _ => exact fun _ _ _ _ => trivial
  | Empty => exact fun _ _ _ _ => trivial
  | Proj _ q ih => exact fun h d γ E => ih h d γ E
  | Sel _ q _ ih => exact fun h d γ E => ih h d γ E
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h d γ E => ⟨ih₁ h.1 d γ E, ih₂ h.2 d γ E⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h d γ E => ⟨ih₁ h.1 d γ E, fun _ _ => ih₂ h.2 _ _ _⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h d γ E => ⟨ih₁ h.1 d γ E, ih₂ h.2 d γ E⟩
  | Dedup q ih => exact fun h d γ E => ih h d γ E
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h d γ E => ⟨ih₁ h.1 d γ E, ih₂ h.2 d γ E⟩
  | Explode _ _ q ih => exact fun h d γ E => ih h d γ E
  | Retag _ q ih => exact fun h d γ E => ih h d γ E
  | Mu _ _ _ _ _ => exact fun h => h.elim
  | MuSet _ _ _ _ _ => exact fun h => h.elim
  | Gamma _ _ _ q _ _ ih => exact fun h d γ E => ih h d γ E
  | GammaScalar _ _ q _ ih => exact fun h d γ E => ih h d γ E
  | GammaNest _ _ _ _ q ih => exact fun h d γ E => ih h d γ E
  | ProvSum _ _ _ q ih => exact fun h d γ E => ih h d γ E
  | GammaTok _ _ _ _ _ q _ ih => exact fun h d γ E => ih h d γ E
  | Win _ _ _ _ _ _ q _ _ _ ih => exact fun h d γ E => ih h d γ E
  | WinExpr _ _ _ _ _ _ _ q _ ih => exact fun h d γ E => ih h d γ E

/-- The rows a linear term gives at a round are, in their columns, rows
it gives at any round holding the same tuples and more. -/
theorem exists_row_of_recLinear {s : String} {n c m : ℕ} {κ : Fin m → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T c m κ l) (h : q.recLinear s n) (hx : q.noExplode)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (X Y : AnnotatedRelation T K n) (hXY : PathSum.supp Y ⊆ PathSum.supp X)
    {y : GenRow T K m} (hy : y ∈ q.evaluate d γ (E.assignHole s (Y.map GenRow.ofAnnotated))) :
    ∃ x ∈ q.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated)), x.fst = y.fst := by
  have hy' : GenRow.fin y ∈ (q.evaluate d γ (E.assignHole s (Y.map GenRow.ofAnnotated))).map
      GenRow.fin := Multiset.mem_map_of_mem _ hy
  rw [evaluate_fin_of_recLinear q h hx d γ E Y, Multiset.mem_bind] at hy'
  obtain ⟨p, hp, hr⟩ := hy'
  obtain ⟨r, hr, he⟩ := Multiset.mem_map.1 hr
  obtain ⟨p', hp', hpe⟩ := PathSum.mem_supp.1 (hXY (PathSum.mem_supp.2 ⟨p, hp, rfl⟩))
  have hx' : ((r.fst, p'.2 * r.snd.finalize) : Tuple (GenValue T K) m × K)
      ∈ (q.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))).map GenRow.fin := by
    rw [evaluate_fin_of_recLinear q h hx d γ E X, Multiset.mem_bind]
    exact ⟨p', hp', Multiset.mem_map.2 ⟨r, by rw [hpe]; exact hr, rfl⟩⟩
  obtain ⟨x, hxm, hxe⟩ := Multiset.mem_map.1 hx'
  exact ⟨x, hxm, (congrArg Prod.fst hxe).trans (congrArg Prod.fst he)⟩

/-- **A linear term settling at a round settles at any round holding fewer
tuples**: its recursions are closed, and the right side of an apply on its
recursive side is read at rows whose columns the larger round gives too. -/
theorem annSettlesAt_of_recLinear_subset {s : String} {n : ℕ} :
    ∀ {c m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
      q.recLinear s n → q.noExplode →
      ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
        (X Y : AnnotatedRelation T K n), PathSum.supp Y ⊆ PathSum.supp X →
        q.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated)) →
        q.AnnSettlesAt d γ (E.assignHole s (Y.map GenRow.ofAnnotated)) := by
  intro c m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' κh => exact fun _ _ _ _ _ _ _ _ _ => trivial
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hx d γ E X Y hXY hs => ih h hx d γ E X Y hXY hs
  | Sel φ q _ ih => exact fun h hx d γ E X Y hXY hs => ih h.2 hx d γ E X Y hXY hs
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) ⟨hx₁, hx₂⟩ d γ E X Y hXY ⟨hs₁, hs₂⟩
    · exact ⟨ih₁ h₁ hx₁ d γ E X Y hXY hs₁, annSettlesAt_closed q₂ d γ
        (by rw [EvalEnv.ctxAt_assignHole, EvalEnv.ctxAt_assignHole]) hs₂⟩
    · exact ⟨annSettlesAt_closed q₁ d γ
        (by rw [EvalEnv.ctxAt_assignHole, EvalEnv.ctxAt_assignHole]) hs₁,
        ih₂ h₂ hx₂ d γ E X Y hXY hs₂⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    rintro ⟨h₁, h₂⟩ ⟨hx₁, hx₂⟩ d γ E X Y hXY ⟨hs₁, hs₂⟩
    refine ⟨ih₁ h₁ hx₁ d γ E X Y hXY hs₁, fun y hy => ?_⟩
    obtain ⟨x, hxm, hxe⟩ := exists_row_of_recLinear q₁ h₁ hx₁ d γ E X Y hXY hy
    have := hs₂ x hxm
    rw [hxe] at this
    exact annSettlesAt_congr_holes q₂ d _ (fun _ hp => absurd hp List.not_mem_nil)
      (by simp only [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_assignHole]) this
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun _ h => h.elim
  | Retag hk q ih => exact fun h hx d γ E X Y hXY hs => ih h hx d γ E X Y hXY hs
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

/-- **Settling under an apply's outer columns** is settling under the
ambient context. -/
theorem annSettlesAt_applyOuter {c n₁ n₂ : ℕ} {κ₂ : Fin n₂ → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n₂ κ₂ l) (dB : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (x : Tuple (GenValue T K) n₁) (u : Fin n₁ → T) :
    (q.substMap (applyOuter T c n₁)).AnnSettlesAt dB (Fin.append u γ)
        (E.withCtx (Fin.append x (E.ctxAt c γ))) ↔ q.AnnSettlesAt dB γ E := by
  rw [annSettlesAt_substMap, substVal_applyOuter]
  constructor
  · exact annSettlesAt_congr_holes q dB γ (fun _ _ => rfl) (ctxAt_substEnv_applyOuter E γ x u)
  · exact annSettlesAt_congr_holes q dB γ (fun _ _ => rfl) (ctxAt_substEnv_applyOuter E γ x u).symm

/-- A product written as an apply settles where its factors do. -/
theorem annSettlesAt_prodA {c n₁ n₂ : ℕ} {l : List (String × ℕ)}
    (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁) l) (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (h₁ : q₁.AnnSettlesAt d γ E) (h₂ : q₂.AnnSettlesAt d γ E) :
    (prodA q₁ q₂).AnnSettlesAt d γ E := by
  rw [prodA, annSettlesAt_castKind]
  exact ⟨h₁, fun x _ => (annSettlesAt_applyOuter q₂ d γ E x.fst _).2 h₂⟩

theorem annSettlesAt_keepCols {c n m : ℕ} {l : List (String × ℕ)} (cols : Fin m → Fin n)
    (q : AggQueryIn T c n (ColKind.allReg n) l) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) : (keepCols cols q).AnnSettlesAt d γ E ↔ q.AnnSettlesAt d γ E := by
  rw [keepCols, annSettlesAt_castKind]; exact Iff.rfl

/-- **The substituted term settles where the term does at the one row.** -/
theorem annSettlesAt_substRel {s : String} {c n : ℕ} (pv : Fin n → T ⊕ Fin c) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
        q.recLinear s n →
      ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K),
        q.AnnSettlesAt d γ (E.assignHole s ({paramRow E γ pv} : Multiset (GenRow T K n))) →
        (substRel s pv q).AnnSettlesAt d γ E := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' κh =>
    rintro ⟨rfl, rfl⟩ d γ E _
    rw [substRel, dite_eq_left ⟨rfl, rfl⟩, annSettlesAt_castIdx]
    trivial
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h d γ E hs => ih pv h d γ E hs
  | Sel φ q _ ih => exact fun h d γ E hs => ih pv h.2 d γ E hs
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) d γ E ⟨hs₁, hs₂⟩
    · rw [substRel, annSettlesAt_castIdx, substRel_of_noMention pv q₂ h₂]
      exact ⟨ih₁ pv h₁ d γ E hs₁, annSettlesAt_closed q₂ d γ
        (by rw [EvalEnv.ctxAt_assignHole]) hs₂⟩
    · rw [substRel, annSettlesAt_castIdx, substRel_of_noMention pv q₁ h₁]
      exact ⟨annSettlesAt_closed q₁ d γ (by rw [EvalEnv.ctxAt_assignHole]) hs₁,
        ih₂ pv h₂ d γ E hs₂⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    rintro ⟨h₁, h₂⟩ d γ E ⟨hs₁, hs₂⟩
    refine ⟨ih₁ pv h₁ d γ E hs₁, fun x hx => ?_⟩
    rw [evaluate_substRel pv q₁ h₁] at hx
    exact annSettlesAt_congr_holes q₂ d _ (fun _ hp => absurd hp List.not_mem_nil)
      (by simp only [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_assignHole]) (hs₂ x hx)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun h d γ E hs => ih pv h d γ E hs
  | Retag hk q ih => exact fun h d γ E hs => ih pv h d γ E hs
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

section CtrSettle

variable {c : ℕ} (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
  (hEQ : ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K), EQ.AnnSettlesAt d γ E)
include hEQ

theorem annSettlesAt_ctr (K' : ℕ) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (ctr EQ K').AnnSettlesAt d γ E := by
  induction K' with
  | zero =>
    rw [ctr, pow, unitC, annSettlesAt_castKind]
    trivial
  | succ K' ih =>
    rw [ctr, pow]
    refine annSettlesAt_prodA _ _ d γ E ih ?_
    rw [dedupG, annSettlesAt_castKind]
    exact hEQ d γ E

theorem annSettlesAt_ctrLt (K' : ℕ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) : (ctrLt EQ K').AnnSettlesAt d γ E :=
  annSettlesAt_prodA _ _ d γ E (annSettlesAt_ctr EQ hEQ K' d γ E)
    (annSettlesAt_ctr EQ hEQ K' d γ E)

theorem annSettlesAt_ctrSucc (K' : ℕ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) : (ctrSucc EQ K').AnnSettlesAt d γ E := by
  refine ⟨annSettlesAt_ctrLt EQ hEQ K' d γ E, ?_⟩
  rw [ctrMid, annSettlesAt_keepCols]
  exact annSettlesAt_prodA _ _ d γ E (annSettlesAt_prodA _ _ d γ E
    (annSettlesAt_ctr EQ hEQ K' d γ E) (annSettlesAt_ctr EQ hEQ K' d γ E))
    (annSettlesAt_ctr EQ hEQ K' d γ E)

theorem annSettlesAt_ctrLeast (K' : ℕ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) : (ctrLeast EQ K').AnnSettlesAt d γ E :=
  ⟨annSettlesAt_ctr EQ hEQ K' d γ E,
    (annSettlesAt_keepCols _ _ d γ E).2 (annSettlesAt_ctrLt EQ hEQ K' d γ E)⟩

theorem annSettlesAt_ctrNext (n K' : ℕ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (x : Tuple (GenValue T K) (n + K')) (u : Tuple T (n + K')) :
    (ctrNext EQ n K').AnnSettlesAt d (Fin.append u γ) (E.withCtx (Fin.append x (E.ctxAt c γ))) := by
  rw [ctrNext, annSettlesAt_keepCols]
  exact (annSettlesAt_applyOuter _ d γ E x u).2 (annSettlesAt_ctrSucc EQ hEQ K' d γ E)

end CtrSettle

/-- **The simulation settles wherever the set recursion does**: its rounds
end at the number of counters, and each round reads the term at tuples of
the recursion's rounds, where the term settles. -/
theorem annSettlesAt_simResultA (s s' : String) (n K' : ℕ)
    (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (hEQ : ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K), EQ.AnnSettlesAt d γ E)
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hL : L.recLinear s n) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (W : Multiset (Tuple T K')) (hWn : W.Nodup)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (hBQ : BQ.AnnSettlesAt d γ E)
    (hLrow : ∀ j t, t ∈ PathSum.supp (PathSum.rounds (BQ.ann d γ E)
        (fun u => L.ann d γ (E.assignHole s
          ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))) j) →
      L.AnnSettlesAt d γ (E.assignHole s
        ({GenRow.ofAnnotated (t, 1)} : Multiset (GenRow T K n)))) :
    (simResultA s s' n K' EQ BQ L).AnnSettlesAt d γ E := by
  obtain ⟨l, -, -, -, hspec⟩ := simSpec_of s n K' EQ BQ L hL d γ E W hWn hW hnn
  set base := (prodA BQ (ctrLeast EQ K')).ann d γ E with hbase
  set F := simRow s n K' EQ L d γ E with hF
  have hzero : (PathSum.lin F)^[l.length] base = 0 := by
    have h := hspec.rounds_eq_zero (le_refl l.length)
    rw [rounds_map_splitRow] at h
    exact Multiset.map_eq_zero.1 h
  show (keepCols (fun i => Fin.castAdd K' i) (simA s s' n K' EQ BQ L)).AnnSettlesAt d γ E
  rw [annSettlesAt_keepCols]
  have hiter := simA_iter s s' n K' EQ BQ L d γ E
  refine ⟨annSettlesAt_prodA _ _ d γ E hBQ (annSettlesAt_ctrLeast EQ hEQ K' d γ E),
    simA_step_zero s s' n K' EQ L d γ E, ⟨l.length, ?_⟩, fun k => ?_, ?_⟩
  · have := hiter (l.length + 1)
    rw [Function.iterate_succ_apply' (PathSum.lin F), hzero, PathSum.lin_zero] at this
    exact Multiset.map_eq_zero.1 this
  · set Xk := (muStep s' (simBodyA s s' n K' EQ L) d γ E)^[k]
      ((prodA BQ (ctrLeast EQ K')).evaluate d γ E) with hXk
    rw [simBodyA, annSettlesAt_keepCols, annSettlesAt_castKind]
    refine ⟨trivial, fun x hx => ?_⟩
    simp only [evaluate, EvalEnv.assignHole_holes_self] at hx
    have hxm := Multiset.mem_of_mem_filter hx
    have hreg := eq_inl_of_conforms (fun k => (Multiset.of_mem_filter hx) k)
    set u := GenRow.plainTuple x.fst with hu
    -- the row's tuple is a tuple of the recursion's round `k`
    have hmem : (leftPart n K' u, rightPart n K' u) ∈ PathSum.supp
        (PathSum.rounds (base.map splitRow)
          (fun q : Tuple T n × Tuple T K' => (F (Fin.append q.1 q.2)).map splitRow) k) := by
      rw [rounds_map_splitRow, ← hiter k]
      exact PathSum.mem_supp.2 ⟨splitRow (GenRow.toAnnotated x),
        Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ hxm), rfl⟩
    obtain ⟨ht, -⟩ := (hspec.supp_rounds k _ _).1 hmem
    have hLs := hLrow k _ ht
    refine annSettlesAt_prodA _ _ _ _ _ ?_ (annSettlesAt_ctrNext EQ hEQ n K' d γ _ x.fst u)
    rw [annSettlesAt_castIdx]
    apply annSettlesAt_substRel _ _ ((recLinear_substMap L _).2 hL)
    have hrow : paramRow ((E.assignHole s' Xk).withCtx
        (Fin.append x.fst ((E.assignHole s' Xk).ctxAt c γ))) (Fin.append u γ) (rowPv n K')
        = GenRow.ofAnnotated (leftPart n K' u, (1 : K)) := by
      unfold paramRow GenRow.ofAnnotated
      simp only [EvalEnv.ctxAt_withCtx]
      refine Prod.ext (funext fun i => ?_) rfl
      show (Fin.append x.fst _ : Tuple (GenValue T K) _) (Fin.castAdd c (Fin.castAdd K' i)) = _
      rw [Fin.append_left, hreg]
      rfl
    rw [hrow]
    have henv : (((E.assignHole s' Xk).withCtx
        (Fin.append x.fst ((E.assignHole s' Xk).ctxAt c γ))).assignHole s
        ({GenRow.ofAnnotated (leftPart n K' u, 1)} : Multiset (GenRow T K n)))
        = ((E.assignHole s' Xk).assignHole s
            ({GenRow.ofAnnotated (leftPart n K' u, 1)} : Multiset (GenRow T K n))).withCtx
          (Fin.append x.fst (((E.assignHole s' Xk).assignHole s
            ({GenRow.ofAnnotated (leftPart n K' u, 1)} : Multiset (GenRow T K n))).ctxAt c γ)) := by
      rw [EvalEnv.ctxAt_assignHole]
      rfl
    rw [henv, annSettlesAt_applyOuter]
    refine annSettlesAt_congr_holes L d γ (fun p hp => ?_) (by
      simp only [EvalEnv.ctxAt_assignHole]) hLs
    rw [List.mem_singleton.1 hp]
    simp only [EvalEnv.assignHole_holes_self]
  · rw [simBodyA, annSettlesAt_keepCols, annSettlesAt_castKind]
    refine ⟨trivial, fun x hx => ?_⟩
    simp only [evaluate, EvalEnv.assignHole_holes_self, Multiset.filter_zero] at hx
    exact absurd hx (Multiset.notMem_zero x)

end Settle

/-! ## The counter values: the leaves' values and the constants -/

section ValRel

variable {c : ℕ}

/-- The unary relations the counter values are the union of: each column
of each leaf, and each constant. -/
def valParts (ls : List (ℕ × String)) (cs : List T) : List (AggQueryIn T c 1 (ColKind.allReg 1)) :=
  ls.flatMap (fun p => (List.finRange p.1).map (colRel (Rel p.1 p.2))) ++ cs.map constRel

/-- **The counter values**: the non-null values of the leaves `ls` and of
the constants `cs`. Unlike the plain counter relation it reads no context
value, so it is well-kinded under any context. -/
def valRel (ls : List (ℕ × String)) (cs : List T) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  Sel nonNullPred (listSum (valParts ls cs))

theorem ann_emptyRel (n : ℕ) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (emptyRel (T := T) (c := c) n).ann d γ E = 0 := by
  rw [emptyRel, ann_castKind]
  simp [ann, evaluate]

theorem ann_listSum {n : ℕ} (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    ∀ l : List (AggQueryIn T c n (ColKind.allReg n)),
      (listSum l).ann d γ E = (l.map (fun q => q.ann d γ E)).sum
  | [] => ann_emptyRel n d γ E
  | q :: l => by rw [listSum, ann_sum, ann_listSum d γ E l, List.map_cons, List.sum_cons]

theorem ann_colRel {n : ℕ} (q : AggQueryIn T c n (ColKind.allReg n)) (i : Fin n)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (colRel q i).ann d γ E
      = (q.ann d γ E).map (fun p => ((fun _ => p.1 i, p.2) : AnnotatedTuple T K 1)) := by
  rw [colRel, ann_castKind]
  simp only [ann, evaluate, Multiset.map_map]
  refine Multiset.map_congr rfl fun r _ => ?_
  simp only [Function.comp, GenRow.toAnnotated]
  exact Prod.ext rfl (GenAnn.finalize_cash' r.snd _ Multiset.inter_le_left)

theorem ann_Rel (k : ℕ) (t : String) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    (Rel k t : AggQueryIn T c k (ColKind.allReg k)).ann d γ E
      = match d.find k t with
        | none => 0
        | some r => (r : Multiset (AnnotatedTuple T K k)) := by
  simp only [ann, evaluate]
  cases d.find k t with
  | none => rfl
  | some r =>
    show Multiset.map GenRow.toAnnotated (Multiset.map GenRow.ofAnnotated _) = _
    rw [Multiset.map_map]
    exact (Multiset.map_congr rfl fun p _ => GenRow.toAnnotated_ofAnnotated p).trans
      (Multiset.map_id _)

theorem ann_constRel (a : T) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (constRel (c := c) a).ann d γ E
      = ({((fun _ => a, 1) : AnnotatedTuple T K 1)} : Multiset (AnnotatedTuple T K 1)) := by
  rw [constRel, ann_castKind]
  simp only [ann, evaluate, unitC, evaluate_castKind, Multiset.map_singleton, GenRow.toAnnotated]
  congr 1
  refine Prod.ext rfl ?_
  simp [GenAnn.finalize]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem mem_list_sum' {α : Type} {x : α} :
    ∀ l : List (Multiset α), x ∈ l.sum ↔ ∃ X ∈ l, x ∈ X
  | [] => by simp
  | X :: l => by
    rw [List.sum_cons, Multiset.mem_add, mem_list_sum' l]
    simp

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem holdsPlain_nonNullPred' (y : Tuple T 1) (γ : Fin c → T) :
    (nonNullPred (c := c)).holdsPlain y γ ↔ ValueType.isNull (y 0) = false :=
  holdsPlain_nonNullPred y γ

/-- **The rows of the counter values**: each is non-null, and its
annotation is that of a leaf row or `𝟙`. -/
theorem mem_ann_valRel {ls : List (ℕ × String)} {cs : List T} {d : AnnotatedDatabase T K}
    {γ : Fin c → T} {E : EvalEnv T K} {p : AnnotatedTuple T K 1}
    (hp : p ∈ (valRel ls cs).ann d γ E) :
    ValueType.isNull (p.1 0) = false ∧
      (p.2 = 1 ∨ ∃ q ∈ ls, ∃ r : AnnotatedRelation T K q.1, d.find q.1 q.2 = some r ∧
        ∃ p' ∈ r, p'.2 = p.2) := by
  rw [valRel, ann_sel _ _ _ rfl, ann_listSum, Multiset.mem_filter] at hp
  obtain ⟨hp, hnn⟩ := hp
  refine ⟨(holdsPlain_nonNullPred' p.1 γ).1 hnn, ?_⟩
  obtain ⟨X, hX, hpX⟩ := (mem_list_sum' _).1 hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hX
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨⟨k, t⟩, hkt, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    rw [ann_colRel, ann_Rel] at hpX
    refine Or.inr ⟨(k, t), hkt, ?_⟩
    cases hf : d.find k t with
    | none => rw [hf] at hpX; exact absurd hpX (Multiset.notMem_zero _)
    | some r =>
      rw [hf] at hpX
      obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.1 hpX
      exact ⟨r, rfl, p', hp', rfl⟩
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hq
    rw [ann_constRel, Multiset.mem_singleton] at hpX
    exact Or.inl (congrArg Prod.snd hpX)

/-- A non-null value of a leaf is a counter value. -/
theorem mem_valRel_of_leaf {ls : List (ℕ × String)} {cs : List T} (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) {q : ℕ × String} (hq : q ∈ ls)
    {r : AnnotatedRelation T K q.1} (hr : d.find q.1 q.2 = some r) {p : AnnotatedTuple T K q.1}
    (hp : p ∈ r) (i : Fin q.1) (hnn : ValueType.isNull (p.1 i) = false) :
    (fun _ => p.1 i) ∈ ((valRel ls cs).ann d γ E).map Prod.fst := by
  rw [valRel, ann_sel _ _ _ rfl, ann_listSum]
  refine Multiset.mem_map.2 ⟨(fun _ => p.1 i, p.2), Multiset.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
  · refine (mem_list_sum' _).2 ⟨_, List.mem_map.2 ⟨colRel (Rel q.1 q.2) i,
      List.mem_append_left _ (List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨i, List.mem_finRange i,
        rfl⟩⟩), rfl⟩, ?_⟩
    rw [ann_colRel, ann_Rel, hr]
    exact Multiset.mem_map.2 ⟨p, hp, rfl⟩
  · exact (holdsPlain_nonNullPred' _ γ).2 hnn

/-- A non-null constant is a counter value. -/
theorem mem_valRel_of_const {ls : List (ℕ × String)} {cs : List T} (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) {a : T} (ha : a ∈ cs) (hnn : ValueType.isNull a = false) :
    (fun _ => a) ∈ ((valRel ls cs).ann d γ E).map Prod.fst := by
  rw [valRel, ann_sel _ _ _ rfl, ann_listSum]
  refine Multiset.mem_map.2 ⟨(fun _ => a, 1), Multiset.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
  · refine (mem_list_sum' _).2 ⟨_, List.mem_map.2 ⟨constRel a,
      List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩), rfl⟩, ?_⟩
    rw [ann_constRel]
    exact Multiset.mem_singleton_self _
  · exact (holdsPlain_nonNullPred' _ γ).2 hnn

omit [ValueType T] in
theorem card_powT (V : Multiset (Tuple T 1)) :
    ∀ K', Multiset.card (powT V K') = Multiset.card V ^ K'
  | 0 => by simp [powT]
  | K' + 1 => by
    rw [powT, Multiset.card_map, show (powT V K').product V = powT V K' ×ˢ V from rfl,
      Multiset.card_product, card_powT V K', pow_succ]

/-- **The counters are annotated `𝟙`** where `δ` is the support map and no
row of the instance is annotated `𝟘`: a counter value's weight sums
non-zero annotations of leaf rows and `𝟙`s, so it is non-zero. -/
theorem ann_ctr_valRel (ls : List (ℕ × String)) (cs : List T) (K' : ℕ)
    (hδ : ∀ a : K, a ≠ 0 → SemiringWithMonus.delta a = 1) (d : AnnotatedDatabase T K)
    (hd : ∀ (k : ℕ) (t : String) (r : AnnotatedRelation T K k), d.find k t = some r →
      ∀ p ∈ r, p.2 ≠ 0) (γ : Fin c → T) (E : EvalEnv T K) :
    (ctr (valRel ls cs) K').ann d γ E
      = (powT (((valRel ls cs).ann d γ E).map Prod.fst).dedup K').map
          (fun v => ((v, 1) : AnnotatedTuple T K K')) := by
  apply ann_pow_ones
  rw [ann_dedupG]
  refine Multiset.map_congr rfl fun g hg => ?_
  refine Prod.ext rfl ?_
  show SemiringWithMonus.delta (PathSum.wt ((valRel ls cs).ann d γ E) g) = 1
  by_cases h01 : (1 : K) = 0
  · have : ∀ x : K, x = 0 := fun x => by rw [← mul_one x, h01, mul_zero]
    rw [this (SemiringWithMonus.delta _), this 1]
  · refine hδ _ fun h0 => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_dedup.1 hg)
    unfold PathSum.wt at h0
    rw [Multiset.sum_eq_zero_iff] at h0
    have h := h0 p.2 (Multiset.mem_map_of_mem _ (Multiset.mem_filter.2 ⟨hp, rfl⟩))
    rcases (mem_ann_valRel hp).2 with h1 | ⟨q, -, r, hr, p', hp', he⟩
    · exact h01 (h1 ▸ h)
    · exact hd q.1 q.2 r hr p' hp' (he.trans h)

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem nonNull_powT {V : Multiset (Tuple T 1)} (hV : ∀ v ∈ V, ValueType.isNull (v 0) = false) :
    ∀ (K' : ℕ), ∀ u ∈ powT V K', ∀ k, ValueType.isNull (u k) = false :=
  fun K' u hu k => hV _ ((mem_powT K' u).1 hu k)

end ValRel

/-! ## Iterations that agree, and the settled set -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Two set recursions agreeing along the iteration of one of them** have
the same iterates and the same value. -/
theorem muIter_congr_iter {α : Type} {step step' : Multiset α → Multiset α}
    (h : ∀ k, step' (muIter step k) = step (muIter step k)) :
    ∀ k, muIter step' k = muIter step k
  | 0 => rfl
  | k + 1 => by rw [muIter, muIter, muIter_congr_iter h k, h k]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem muFix_congr_iter {α : Type} {step step' : Multiset α → Multiset α}
    (h : ∀ k, step' (muIter step k) = step (muIter step k)) : muFix step' = muFix step := by
  have hi := muIter_congr_iter h
  have hidx : muFixIdx step' = muFixIdx step := by
    unfold muFixIdx
    congr 1
    ext j
    simp only [Set.mem_ofPred_eq, ← muIter_eq_iterate, hi]
  rw [muFix, muFix, hidx, hi]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem muSetSettles_congr_iter {α : Type} {step step' : Multiset α → Multiset α}
    (h : ∀ k, step' (muIter step k) = step (muIter step k)) (hs : MuSetSettles step) :
    MuSetSettles step' := by
  obtain ⟨j, hj⟩ := hs
  refine ⟨j, ?_⟩
  rw [← muIter_eq_iterate, ← muIter_eq_iterate] at hj ⊢
  rw [muIter_congr_iter h, muIter_congr_iter h]
  exact hj

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **The tuples of the settled value are closed under the rounds.** -/
theorem closed_supp_muFix {n : ℕ} (B : AnnotatedRelation T K n)
    (G : Tuple T n → AnnotatedRelation T K n) (hs : MuSetSettles (PathSum.stepK B G)) :
    PathSum.Closed (PathSum.supp (muFix (PathSum.stepK B G))) B G := by
  have hfix := muFix_isFix hs
  constructor
  · intro u hu
    rw [← hfix, PathSum.stepK, PathSum.supp_dedupK, PathSum.supp_add]
    exact Finset.mem_union_left _ hu
  · intro u hu v hv
    rw [← hfix, PathSum.stepK, PathSum.supp_dedupK, PathSum.supp_add]
    exact Finset.mem_union_right _ (PathSum.mem_supp_lin.2 ⟨u, hu, hv⟩)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- Stripping keeps the recursions hygienic. -/
theorem hygienic_stripAgg :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.hygienic → q.stripAgg.hygienic := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ _ => exact fun h => h
  | Param _ _ => exact fun h => h
  | Empty => exact fun h => h
  | Proj _ q ih => exact fun h => ih h
  | Sel φ q _ ih =>
    intro h
    simp only [stripAgg]
    split_ifs
    · exact ih h
    · exact ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ih₁ h.1
  | Explode _ _ q ih => exact fun h => ih h
  | Retag _ q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨noMention_stripAgg q₀ h.1, noMention_stripAgg q₁ h.2.1,
      ih₀ h.2.2.1, ih₁ h.2.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨noMention_stripAgg q₀ h.1,
      noMention_stripAgg q₁ h.2.1, ih₀ h.2.2.1, ih₁ h.2.2.2⟩
  | Gamma _ _ _ q _ _ ih => exact fun h => ih h
  | GammaScalar _ _ q _ ih => exact fun h => ih h
  | GammaNest _ _ _ _ q ih => exact fun h => ih h
  | ProvSum _ _ _ q ih => exact fun h => ih h
  | GammaTok _ _ _ _ _ q _ ih => exact fun h => ih h
  | Win _ _ _ _ _ _ q _ _ _ ih => exact fun h => ih h
  | WinExpr _ _ _ _ _ _ _ q _ ih => exact fun h => ih h

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem add_le_pow_of_two_le {m : ℕ} (hm : 2 ≤ m) : ∀ c : ℕ, m + c + 2 ≤ m ^ (c + 2)
  | 0 => by
    rw [pow_two]
    nlinarith
  | c + 1 => by
    have ih := add_le_pow_of_two_le hm c
    rw [pow_succ]
    nlinarith

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The counter's width**: `a (|B| + 1)^b` tuples are outrun by
`m^(a + (c + 2) b)` counters, for a value set `B` of at most `m + 1 + c`
elements and `m ≥ 2` counter values. -/
theorem card_bound_arith {a b c m B : ℕ} (hm : 2 ≤ m) (hB : B ≤ m + 1 + c) :
    a * (B + 1) ^ b ≤ m ^ (a + (c + 2) * b) := by
  calc a * (B + 1) ^ b ≤ a * (m + c + 2) ^ b :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ ≤ m ^ a * (m ^ (c + 2)) ^ b :=
        Nat.mul_le_mul (le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hm a))
          (Nat.pow_le_pow_left (add_le_pow_of_two_le hm c) b)
    _ = m ^ (a + (c + 2) * b) := by rw [← pow_mul, ← pow_add]

/-! ## The node: a set recursion replaced by its simulation -/

section Node

variable {c : ℕ}

theorem annSettlesAt_valRel (ls : List (ℕ × String)) (cs : List T) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) (E : EvalEnv T K) : (valRel ls cs).AnnSettlesAt d γ E := by
  show (listSum (valParts ls cs)).AnnSettlesAt d γ E
  have key : ∀ l : List (AggQueryIn T c 1 (ColKind.allReg 1)),
      (∀ q ∈ l, q.AnnSettlesAt d γ E) → (listSum l).AnnSettlesAt d γ E := by
    intro l
    induction l with
    | nil => intro _; rw [listSum, emptyRel, annSettlesAt_castKind]; trivial
    | cons q l ih =>
      intro h
      exact ⟨h q List.mem_cons_self, ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')⟩
  refine key _ fun q hq => ?_
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨p, -, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    rw [colRel, annSettlesAt_castKind]
    trivial
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hq
    rw [constRel, annSettlesAt_castKind]
    show (unitC : AggQueryIn T c 0 _).AnnSettlesAt d γ E
    rw [unitC, annSettlesAt_castKind]
    trivial

/-- The leaves the counter of a set recursion reads. -/
def ctrLeaves {n : ℕ} (s : String) (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) : List (ℕ × String) :=
  (MuSet s q₀.stripAgg q₁.stripAgg).leaves

/-- The constants the counter of a set recursion reads: the recursion's
own, and two more, so that there are at least two counter values. -/
noncomputable def ctrConsts {n : ℕ} (s : String) (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) : List T :=
  (MuSet s q₀.stripAgg q₁.stripAgg).allConsts.toList ++ [0, ValueType.nonzero]

open Classical in
/-- **The width of the counter**: `a + (c + 2) b` for the bound
`a (m + 1)^b` the plain semantics gives on the recursion's rows, over `m`
values (`AggQueryIn.exists_card_bound_muSet`). -/
noncomputable def ctrWidth (cnt : SeqAggFunc T) {n : ℕ} (s : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) : ℕ :=
  if h : cnt.ReadsCount ∧ (MuSet s q₀.stripAgg q₁.stripAgg).inSig {cnt}
      ∧ (MuSet s q₀.stripAgg q₁.stripAgg).hygienic then
    Classical.choose (Classical.choose_spec
        (exists_card_bound_muSet h.1 s q₀.stripAgg q₁.stripAgg h.2.1 h.2.2)).1
      + (c + 2) * Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_card_bound_muSet h.1 s q₀.stripAgg q₁.stripAgg h.2.1 h.2.2)).1)
  else 0

/-- The query a set recursion is replaced by. -/
noncomputable def muSetSim (cnt : SeqAggFunc T) {n : ℕ} (s s' : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) : AggQueryIn T c n (ColKind.allReg n) :=
  simResultA s s' n (ctrWidth cnt s q₀ q₁) (valRel (ctrLeaves s q₀ q₁) (ctrConsts s q₀ q₁)) q₀' q₁'

/-- The support `δ` and the instance fence, which the counter needs. -/
structure CounterOK (d : AnnotatedDatabase T K) : Prop where
  delta : ∀ a : K, a ≠ 0 → SemiringWithMonus.delta a = 1
  fence : ∀ (k : ℕ) (t : String) (r : AnnotatedRelation T K k), d.find k t = some r →
    ∀ p ∈ r, p.2 ≠ 0

/-- **A set recursion is its simulation**, at an instance where it settles,
given matches `q₀'`, `q₁'` of its base and body that agree with them
wherever these settle. -/
theorem muSetSim_correct (cnt : SeqAggFunc T) (hcnt : cnt.ReadsCount)
    (hK : PathSum.SettlesEarly K) {n : ℕ} (s s' : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hq₁ : q₁.recLinear s n) (hq₁x : q₁.noExplode) (hq₁' : q₁'.recLinear s n)
    (hq₁'x : q₁'.noExplode) (hsig : (MuSet s q₀ q₁).inSig {cnt})
    (hhyg : (MuSet s q₀ q₁).hygienic) (hx : (MuSet s q₀ q₁).noExplode)
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hwk : (MuSet s q₀ q₁).wellKinded ρc HK)
    (d : AnnotatedDatabase T K) (hd : CounterOK d) (γ : Fin c → T) (E : EvalEnv T K)
    (hE : E.Kinded γ ρc HK) (hset : (MuSet s q₀ q₁).AnnSettlesAt d γ E)
    (h₀ : q₀'.AnnSettlesAt d γ E ∧ q₀'.evaluate d γ E = q₀.evaluate d γ E)
    (h₁ : ∀ X : AnnotatedRelation T K n,
      q₁.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated)) →
        q₁'.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated))
          ∧ q₁'.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))
            = q₁.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))) :
    (muSetSim cnt s s' q₀ q₁ q₀' q₁').AnnSettlesAt d γ E
      ∧ (muSetSim cnt s s' q₀ q₁ q₀' q₁').evaluate d γ E = (MuSet s q₀ q₁).evaluate d γ E := by
  obtain ⟨hs₀, hsS, hsk⟩ := hset
  -- the two set recursions have the same iterates
  have hiter : ∀ k, muSetStep s q₀' q₁' d γ E (muIter (muSetStep s q₀ q₁ d γ E) k)
      = muSetStep s q₀ q₁ d γ E (muIter (muSetStep s q₀ q₁ d γ E) k) := fun k => by
    have h1 := (h₁ _ (hsk k)).2
    generalize muIter (muSetStep s q₀ q₁ d γ E) k = X at h1 ⊢
    unfold muSetStep evaluateAnnotated
    rw [h₀.2, h1]
  have hfix := muFix_congr_iter hiter
  have hsS' := muSetSettles_congr_iter hiter hsS
  have hMuSet : (MuSet s q₀' q₁').evaluate d γ E = (MuSet s q₀ q₁).evaluate d γ E := by
    rw [evaluate_MuSet, evaluate_MuSet, hfix]
  -- the recursion of `PathSum` the matches give
  set B := q₀'.ann d γ E with hB
  set G := fun u => q₁'.ann d γ (E.assignHole s
    ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) with hG
  have hstep : muSetStep s q₀' q₁' d γ E = PathSum.stepK B G := funext fun X => by
    rw [muSetStep, dedupAnn_eq_dedupK, PathSum.stepK]
    congr 2
    exact ann_of_recLinear q₁' hq₁' hq₁'x d γ E X
  have hsK : MuSetSettles (PathSum.stepK B G) := hstep ▸ hsS'
  -- the counters
  set ls := ctrLeaves s q₀ q₁ with hls
  set cs := ctrConsts s q₀ q₁ with hcs
  set EQ : AggQueryIn T c 1 (ColKind.allReg 1) := valRel ls cs with hEQ
  set K' := ctrWidth cnt s q₀ q₁ with hK'
  set V := ((EQ.ann d γ E).map Prod.fst).dedup with hV
  set W := powT V K' with hW
  have hWn : W.Nodup := nodup_powT (Multiset.nodup_dedup _) K'
  have hWa : (ctr EQ K').ann d γ E = W.map (fun v => ((v, 1) : AnnotatedTuple T K K')) :=
    ann_ctr_valRel ls cs K' hd.delta d hd.fence γ E
  have hVnn : ∀ v ∈ V, ValueType.isNull (v 0) = false := fun v hv => by
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_dedup.1 hv)
    exact (mem_ann_valRel hp).1
  have hnn := nonNull_powT hVnn K'
  -- the tuples of the settled value, and their number
  set S := PathSum.supp (muFix (PathSum.stepK B G)) with hS
  have hSc : PathSum.Closed S B G := closed_supp_muFix B G hsK
  have hcard : S.card ≤ W.card := by
    classical
    -- the plain bound on the recursion's rows
    have hcond : cnt.ReadsCount ∧ (MuSet s q₀.stripAgg q₁.stripAgg).inSig {cnt}
        ∧ (MuSet s q₀.stripAgg q₁.stripAgg).hygienic :=
      ⟨hcnt, inSig_stripAgg (MuSet s q₀ q₁) hsig, hygienic_stripAgg (MuSet s q₀ q₁) hhyg⟩
    have hex := exists_card_bound_muSet hcond.1 s q₀.stripAgg q₁.stripAgg hcond.2.1 hcond.2.2
    have hK'e : K' = Classical.choose (Classical.choose_spec hex).1
        + (c + 2) * Classical.choose (Classical.choose_spec (Classical.choose_spec hex).1) := by
      rw [hK', ctrWidth, dite_eq_left hcond]
    set fb := Classical.choose hex with hfb
    have hbnd := (Classical.choose_spec hex).2
    set a := Classical.choose (Classical.choose_spec hex).1 with ha
    set b := Classical.choose (Classical.choose_spec (Classical.choose_spec hex).1) with hb
    have hab : ∀ m, fb m ≤ a * (m + 1) ^ b :=
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex).1)
    -- the value set
    set Bv : Finset T := Union.union (Union.union (V.map (fun v => v 0)).toFinset
      (ValueType.nullVal : Option T).toFinset) (Finset.univ.image γ) with hBv
    have hinV : ∀ x : T, ValueType.isNull x = false →
        (fun _ => x) ∈ (EQ.ann d γ E).map Prod.fst → x ∈ Bv := fun x _ hx => by
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Multiset.mem_toFinset.2 ?_))
      exact Multiset.mem_map.2 ⟨fun _ => x, Multiset.mem_dedup.2 hx, rfl⟩
    have hnullB : ∀ x : T, ValueType.isNull x = true → x ∈ Bv := fun x hx => by
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [(ValueType.isNull_iff_nullVal x).1 hx]
      exact Finset.mem_singleton_self x
    have hνB : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ Bv := fun ν hν => by
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [hν]; exact Finset.mem_singleton_self ν
    have h0V : (fun _ => (0 : T)) ∈ (EQ.ann d γ E).map Prod.fst :=
      mem_valRel_of_const d γ E (List.mem_append_right _ (by simp)) ValueType.isNull_zero
    have hnzV : (fun _ => (ValueType.nonzero : T)) ∈ (EQ.ann d γ E).map Prod.fst :=
      mem_valRel_of_const d γ E (List.mem_append_right _ (by simp)) ValueType.isNull_nonzero
    have h0B : (0 : T) ∈ Bv := hinV 0 ValueType.isNull_zero h0V
    have hγB : ∀ j, γ j ∈ Bv := fun j =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem γ (Finset.mem_univ j))
    have hDB : ∀ p ∈ (MuSet s q₀.stripAgg q₁.stripAgg).leaves, ∀ r : Relation T p.1,
        d.toPlain.find p.1 p.2 = some r → ∀ u, Multiset.Mem r u → ∀ j, u j ∈ Bv := by
      intro p hp r hr u hu j
      rw [AnnotatedDatabase.find_toPlain] at hr
      obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.1 hu
      cases hnull : ValueType.isNull (p'.1 j)
      · exact hinV _ hnull (mem_valRel_of_leaf d γ E hp hr' hp' j hnull)
      · exact hnullB _ hnull
    have hcB : ∀ x ∈ (MuSet s q₀.stripAgg q₁.stripAgg).allConsts, x ∈ Bv := by
      intro x hx
      cases hnull : ValueType.isNull x
      · exact hinV _ hnull (mem_valRel_of_const d γ E
          (List.mem_append_left _ (Finset.mem_toList.2 hx)) hnull)
      · exact hnullB _ hnull
    have hplain := hbnd Bv d.toPlain γ hνB h0B hγB hDB hcB
    -- the data of the annotated value is the plain value's
    have hadeq := evaluate_toPlain_env (MuSet s q₀ q₁) hx hhyg hwk d E d.toPlain ∅ hE
      (fun n' s' _ => AnnotatedDatabase.find_toPlain n' s' d)
      (fun _ h => absurd h (Set.notMem_empty _)) (fun p hp => absurd hp List.not_mem_nil)
      ⟨hs₀, hsS, hsk⟩
    have hval : (MuSet s q₀' q₁').evaluate d γ E
        = (muFix (PathSum.stepK B G)).map GenRow.ofAnnotated :=
      evaluate_MuSet_of_recLinear s q₀' q₁' hq₁' hq₁'x d γ E
    have hcS : S.card ≤ Multiset.card ((MuSet s q₀.stripAgg q₁.stripAgg).evaluatePlain
        d.toPlain γ : Multiset (Tuple T n)) := by
      rw [show (MuSet s q₀.stripAgg q₁.stripAgg) = (MuSet s q₀ q₁).stripAgg from rfl, ← hadeq,
        ← hMuSet, hval, Multiset.card_map, Multiset.card_map]
      exact le_trans (Multiset.toFinset_card_le _) (by rw [Multiset.card_map])
    -- the arithmetic
    have hm2 : 2 ≤ V.card := by
      rw [← Multiset.toFinset_card_of_nodup (Multiset.nodup_dedup _)]
      refine Finset.one_lt_card.2 ⟨fun _ => 0, Multiset.mem_toFinset.2 (Multiset.mem_dedup.2 h0V),
        fun _ => ValueType.nonzero, Multiset.mem_toFinset.2 (Multiset.mem_dedup.2 hnzV), ?_⟩
      intro h
      exact ValueType.nonzero_ne_zero (congrFun h 0).symm
    have hBcard : Bv.card ≤ V.card + 1 + c := by
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
      · refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
        · exact le_trans (Multiset.toFinset_card_le _) (by rw [Multiset.card_map])
        · cases (ValueType.nullVal : Option T) <;> simp
      · exact le_trans Finset.card_image_le (by simp)
    rw [hW, card_powT, hK'e]
    exact le_trans hcS (le_trans hplain (le_trans (hab _) (card_bound_arith hm2 hBcard)))
  -- the rounds' tuples, where the body settles
  have hLrow : ∀ j t, t ∈ PathSum.supp (PathSum.rounds B G j) →
      q₁'.AnnSettlesAt d γ (E.assignHole s
        ({GenRow.ofAnnotated (t, 1)} : Multiset (GenRow T K n))) := by
    intro j t ht
    have htm : t ∈ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E) (j + 1)) := by
      rw [← muIter_congr_iter hiter, hstep, muIter_eq_iterate, PathSum.iterate_stepK_eq,
        PathSum.supp_dedupK]
      exact PathSum.mem_supp_trunc.2 ⟨j, Nat.lt_succ_self j, ht⟩
    have hsub : PathSum.supp ({((t, 1) : AnnotatedTuple T K n)} : Multiset (AnnotatedTuple T K n))
        ⊆ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E) (j + 1)) := fun v hv => by
      have : v = t := by simpa [PathSum.supp] using hv
      rw [this]; exact htm
    have h1 := annSettlesAt_of_recLinear_subset q₁ hq₁ hq₁x d γ E _ _ hsub (hsk (j + 1))
    exact (h₁ _ h1).1
  refine ⟨annSettlesAt_simResultA s s' n K' EQ (annSettlesAt_valRel ls cs) q₀' q₁' hq₁' d γ E
      W hWn hWa hnn h₀.1 hLrow, ?_⟩
  rw [← hMuSet]
  exact evaluate_simResultA s s' n K' EQ q₀' q₁' hq₁' hq₁'x d γ E W hWn hWa hnn S hSc hcard hK
    hsS'

end Node

/-! ## What the simulation mentions, and that it explodes nothing -/

section SimStructure

variable {c : ℕ}

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_prodA {n₁ n₂ : ℕ} {l : List (String × ℕ)}
    (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁) l) (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂))
    (h₁ : q₁.noExplode) (h₂ : q₂.noExplode) : (prodA q₁ q₂).noExplode := by
  rw [prodA, noExplode_castKind]
  exact ⟨h₁, (noExplode_substMap _ _).2 h₂⟩

theorem noMention_valRel (ls : List (ℕ × String)) (cs : List T) (t : String)
    (hls : ∀ p ∈ ls, p.2 ≠ t) : (valRel (c := c) ls cs).noMention t := by
  show (listSum (valParts ls cs)).noMention t
  refine noMention_listSum t _ fun q hq => ?_
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    rw [colRel, noMention_castKind]
    exact hls p hp
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hq
    rw [constRel, noMention_castKind]
    exact noMention_unitC t

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_valRel (ls : List (ℕ × String)) (cs : List T) :
    (valRel (c := c) ls cs).noExplode := by
  show (listSum (valParts ls cs)).noExplode
  have key : ∀ l : List (AggQueryIn T c 1 (ColKind.allReg 1)), (∀ q ∈ l, q.noExplode) →
      (listSum l).noExplode := by
    intro l
    induction l with
    | nil => intro _; rw [listSum, emptyRel, noExplode_castKind]; trivial
    | cons q l ih => exact fun h => ⟨h q List.mem_cons_self,
        ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')⟩
  refine key _ fun q hq => ?_
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨p, -, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    rw [colRel, noExplode_castKind]
    trivial
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hq
    rw [constRel, noExplode_castKind]
    show (unitC : AggQueryIn T c 0 _).noExplode
    rw [unitC, noExplode_castKind]
    trivial

section Ctr

variable (EQ : AggQueryIn T c 1 (ColKind.allReg 1))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_ctr (h : EQ.noExplode) (K' : ℕ) : (ctr EQ K').noExplode := by
  induction K' with
  | zero => rw [ctr, pow, unitC, noExplode_castKind]; trivial
  | succ K' ih =>
    rw [ctr, pow]
    refine noExplode_prodA _ _ ih ?_
    rw [dedupG, noExplode_castKind]
    exact h

omit [ValueType T] in
theorem noMention_ctr (t : String) (h : EQ.noMention t) (K' : ℕ) : (ctr EQ K').noMention t :=
  noMention_pow _ (noMention_dedupG _ t h) K'

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_ctrSucc (h : EQ.noExplode) (K' : ℕ) : (ctrSucc EQ K').noExplode :=
  ⟨noExplode_prodA _ _ (noExplode_ctr EQ h K') (noExplode_ctr EQ h K'),
    noExplode_prodA _ _ (noExplode_prodA _ _ (noExplode_ctr EQ h K') (noExplode_ctr EQ h K'))
      (noExplode_ctr EQ h K')⟩

theorem noMention_ctrSucc (t : String) (h : EQ.noMention t) (K' : ℕ) :
    (ctrSucc EQ K').noMention t :=
  ⟨noMention_prodA _ _ (noMention_ctr EQ t h K') (noMention_ctr EQ t h K'),
    noMention_prodA _ _ (noMention_prodA _ _ (noMention_ctr EQ t h K') (noMention_ctr EQ t h K'))
      (noMention_ctr EQ t h K')⟩

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_ctrLeast (h : EQ.noExplode) (K' : ℕ) : (ctrLeast EQ K').noExplode :=
  ⟨noExplode_ctr EQ h K', noExplode_prodA _ _ (noExplode_ctr EQ h K') (noExplode_ctr EQ h K')⟩

theorem noMention_ctrLeast (t : String) (h : EQ.noMention t) (K' : ℕ) :
    (ctrLeast EQ K').noMention t :=
  ⟨noMention_ctr EQ t h K', noMention_prodA _ _ (noMention_ctr EQ t h K') (noMention_ctr EQ t h K')⟩

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_ctrNext (h : EQ.noExplode) (n K' : ℕ) : (ctrNext EQ n K').noExplode := by
  show ((ctrSucc EQ K').substMap (applyOuter T c (n + K'))).noExplode
  exact (noExplode_substMap _ _).2 (noExplode_ctrSucc EQ h K')

theorem noMention_ctrNext (t : String) (h : EQ.noMention t) (n K' : ℕ) :
    (ctrNext EQ n K').noMention t := by
  show ((ctrSucc EQ K').substMap (applyOuter T c (n + K'))).noMention t
  exact (noMention_substMap _ _).2 (noMention_ctrSucc EQ t h K')

end Ctr

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_substRel {s : String} {n : ℕ} (pv : Fin n → T ⊕ Fin c) :
    ∀ {m : ℕ} {κ : Fin m → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c m κ l),
      q.recLinear s n → q.noExplode → (substRel s pv q).noExplode := by
  intro m κ l q
  induction q with
  | Rel n' s' => exact fun h => h.elim
  | Hole n' s' κh =>
    rintro ⟨rfl, rfl⟩ _
    rw [substRel, dite_eq_left ⟨rfl, rfl⟩, noExplode_castIdx]
    trivial
  | Param pv ρ => exact fun h => h.elim
  | Empty => exact fun h => h.elim
  | Proj ps q ih => exact fun h hx => ih pv h hx
  | Sel φ q _ ih => exact fun h hx => ih pv h.2 hx
  | Prod q₁ q₂ ih₁ ih₂ =>
    rintro (⟨h₁, rfl, h₂⟩ | ⟨rfl, h₁, h₂⟩) ⟨hx₁, hx₂⟩
    · rw [substRel, noExplode_castIdx, substRel_of_noMention pv q₂ h₂]
      exact ⟨ih₁ pv h₁ hx₁, hx₂⟩
    · rw [substRel, noExplode_castIdx, substRel_of_noMention pv q₁ h₁]
      exact ⟨hx₁, ih₂ pv h₂ hx₂⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h hx => ⟨ih₁ pv h.1 hx.1, hx.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Dedup q ih => exact fun h => h.elim
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => h.elim
  | Explode k hk q ih => exact fun _ h => h.elim
  | Retag hk q ih => exact fun h hx => ih pv h hx
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => h.elim
  | Gamma is ts fs q keep ord ih => exact fun h => h.elim
  | GammaScalar ts fs q ord ih => exact fun h => h.elim
  | GammaNest is his p fn q ih => exact fun h => h.elim
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun h => h.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

end SimStructure

section SimStructure2

variable {c : ℕ}

theorem noMention_muSetSim (cnt : SeqAggFunc T) {n : ℕ} (s s' t : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (hq₁' : q₁'.recLinear s n)
    (h₀ : q₀'.noMention t) (h₁ : q₁'.noMention t) (hls : (MuSet s q₀ q₁).noMention t) :
    (muSetSim cnt s s' q₀ q₁ q₀' q₁').noMention t := by
  have hls' : ∀ p ∈ ctrLeaves s q₀ q₁, p.2 ≠ t :=
    ne_of_noMention_of_mem_leaves _ (noMention_stripAgg (MuSet s q₀ q₁) hls)
  have hEQ := noMention_valRel (c := c) (ctrLeaves s q₀ q₁) (ctrConsts s q₀ q₁) t hls'
  show (keepCols (fun i => Fin.castAdd _ i) (simA s s' n _ _ q₀' q₁')).noMention t
  rw [keepCols, noMention_castKind]
  refine ⟨noMention_prodA _ _ h₀ (noMention_ctrLeast _ t hEQ _), ?_⟩
  rw [simBodyA, keepCols, noMention_castKind]
  refine (noMention_castKind _ _).2
    ⟨trivial, noMention_prodA _ _ ?_ (noMention_ctrNext _ t hEQ n _)⟩
  rw [noMention_castIdx]
  refine noMention_substRel (s := s) (s' := t) (rowPv n _) ?_ _
    ((recLinear_substMap q₁' _).2 hq₁') (Or.inr ((noMention_substMap _ _).2 h₁))
  trivial

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem noExplode_muSetSim (cnt : SeqAggFunc T) {n : ℕ} (s s' : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (hq₁' : q₁'.recLinear s n)
    (h₀ : q₀'.noExplode) (h₁ : q₁'.noExplode) :
    (muSetSim cnt s s' q₀ q₁ q₀' q₁').noExplode := by
  have hEQ := noExplode_valRel (c := c) (ctrLeaves s q₀ q₁) (ctrConsts s q₀ q₁)
  show (keepCols (fun i => Fin.castAdd _ i) (simA s s' n _ _ q₀' q₁')).noExplode
  rw [keepCols, noExplode_castKind]
  refine ⟨noExplode_prodA _ _ h₀ (noExplode_ctrLeast _ hEQ _), ?_⟩
  rw [simBodyA, keepCols, noExplode_castKind]
  refine (noExplode_castKind _ _).2 ⟨trivial, noExplode_prodA _ _ ?_ (noExplode_ctrNext _ hEQ n _)⟩
  rw [noExplode_castIdx]
  exact noExplode_substRel _ _ ((recLinear_substMap q₁' _).2 hq₁')
    ((noExplode_substMap _ _).2 h₁)

end SimStructure2

/-! ## The pass -/

/-- **Every set recursion replaced by its simulation**, the supply split
in three at each node, the recursion's own fresh name the supply's first. -/
noncomputable def muSetFreeA (cnt : SeqAggFunc T) (f : ℕ → String) :
    {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → AggQueryIn T c n κ l
  | _, _, _, _, .Rel n s => .Rel n s
  | _, _, _, _, .Hole n s κ => .Hole n s κ
  | _, _, _, _, .Param pv ρ => .Param pv ρ
  | _, _, _, _, .Empty => .Empty
  | _, _, _, _, .Proj ps q => .Proj ps (muSetFreeA cnt f q)
  | _, _, _, _, .Sel φ q hφ => .Sel φ (muSetFreeA cnt f q) hφ
  | _, _, _, _, .Prod q₁ q₂ =>
      .Prod (muSetFreeA cnt (tri f 1) q₁) (muSetFreeA cnt (tri f 2) q₂)
  | _, _, _, _, .Apply q₁ q₂ =>
      .Apply (muSetFreeA cnt (tri f 1) q₁) (muSetFreeA cnt (tri f 2) q₂)
  | _, _, _, _, .Sum q₁ q₂ =>
      .Sum (muSetFreeA cnt (tri f 1) q₁) (muSetFreeA cnt (tri f 2) q₂)
  | _, _, _, _, .Dedup q => .Dedup (muSetFreeA cnt f q)
  | _, _, _, _, .Diff q₁ q₂ =>
      .Diff (muSetFreeA cnt (tri f 1) q₁) (muSetFreeA cnt (tri f 2) q₂)
  | _, _, _, _, .Explode k h q => .Explode k h (muSetFreeA cnt f q)
  | _, _, _, _, .Retag h q => .Retag h (muSetFreeA cnt f q)
  | _, _, _, _, .Mu s q₀ q₁ =>
      .Mu s (muSetFreeA cnt (tri f 1) q₀) (muSetFreeA cnt (tri f 2) q₁)
  | _, _, _, _, .MuSet s q₀ q₁ =>
      muSetSim cnt s (f 0) q₀ q₁ (muSetFreeA cnt (tri f 1) q₀) (muSetFreeA cnt (tri f 2) q₁)
  | _, _, _, _, .Gamma is ts fs q keep ord => .Gamma is ts fs (muSetFreeA cnt f q) keep ord
  | _, _, _, _, .GammaScalar ts fs q ord => .GammaScalar ts fs (muSetFreeA cnt f q) ord
  | _, _, _, _, .GammaNest is his p g q => .GammaNest is his p g (muSetFreeA cnt f q)
  | _, _, _, _, .ProvSum is his t q => .ProvSum is his t (muSetFreeA cnt f q)
  | _, _, _, _, .GammaTok is his ts fs a q keep =>
      .GammaTok is his ts fs a (muSetFreeA cnt f q) keep
  | _, _, _, _, .Win P O o w t g q hrr dist keep =>
      .Win P O o w t g (muSetFreeA cnt f q) hrr dist keep
  | _, _, _, _, .WinExpr P O o ws ts fs g q keeps =>
      .WinExpr P O o ws ts fs g (muSetFreeA cnt f q) keeps

/-- **The pass keeps a name unmentioned, and a recursive term linear.** The
two go together: a product's closed side must stay unmentioning, and a set
recursion's body must stay linear for its simulation to mention nothing new. -/
theorem muSetFreeA_struct (cnt : SeqAggFunc T) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), q.usesOnly (Set.univ \ {OpKind.union}) → q.hygienic →
        (∀ t, q.noMention t → (muSetFreeA cnt f q).noMention t)
          ∧ (∀ s n', q.recLinear s n' → (muSetFreeA cnt f q).recLinear s n') := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ => ⟨fun _ h => h, fun _ _ h => h⟩
  | Hole _ _ _ => exact fun _ _ _ => ⟨fun _ h => h, fun _ _ h => h⟩
  | Param _ _ => exact fun _ _ _ => ⟨fun _ h => h, fun _ _ h => h⟩
  | Empty => exact fun _ _ _ => ⟨fun _ h => h, fun _ _ h => h⟩
  | Proj ps q ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h, fun s n' h => (ih f hu.2 hh).2 s n' h⟩
  | Sel φ q hφ ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h,
      fun s n' h => ⟨h.1, (ih f hu.2 hh).2 s n' h.2⟩⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro f hu hh
    have i₁ := ih₁ (tri f 1) hu.2.1 hh.1
    have i₂ := ih₂ (tri f 2) hu.2.2 hh.2
    refine ⟨fun t h => ⟨i₁.1 t h.1, i₂.1 t h.2⟩, fun s n' h => ?_⟩
    rcases h with ⟨h₁, hl, h₂⟩ | ⟨hl, h₁, h₂⟩
    · exact Or.inl ⟨i₁.2 s n' h₁, hl, i₂.1 s h₂⟩
    · exact Or.inr ⟨hl, i₁.1 s h₁, i₂.2 s n' h₂⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro f hu hh
    have i₁ := ih₁ (tri f 1) hu.2.1 hh.1
    have i₂ := ih₂ (tri f 2) hu.2.2 hh.2
    exact ⟨fun t h => ⟨i₁.1 t h.1, i₂.1 t h.2⟩, fun s n' h => ⟨i₁.2 s n' h.1, i₂.1 s h.2⟩⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f hu _ => absurd hu.1 (by simp)
  | Dedup q ih => exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h, fun _ _ h => h.elim⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro f hu hh
    exact ⟨fun t h => ⟨(ih₁ _ hu.2.1 hh.1).1 t h.1, (ih₂ _ hu.2.2 hh.2).1 t h.2⟩,
      fun _ _ h => h.elim⟩
  | Explode k hk q ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu hh).1 t h, fun s n' h => (ih f hu hh).2 s n' h⟩
  | Retag hk q ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu hh).1 t h, fun s n' h => (ih f hu hh).2 s n' h⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro f hu hh
    exact ⟨fun t h => ⟨(ih₀ _ hu.2.1 hh.2.2.1).1 t h.1, (ih₁ _ hu.2.2 hh.2.2.2).1 t h.2⟩,
      fun _ _ h => h.elim⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f hu hh
    have i₀ := ih₀ (tri f 1) hu.2.1 hh.2.2.1
    have i₁ := ih₁ (tri f 2) hu.2.2 hh.2.2.2
    have hlin : q₁.recLinear s _ := recLinear_of_usesOnly (by simp) q₁ rfl hh.2.1 hu.2.2
    refine ⟨fun t h => ?_, fun _ _ h => ?_⟩
    · exact noMention_muSetSim cnt s _ t q₀ q₁ _ _ (i₁.2 s _ hlin) (i₀.1 t h.1) (i₁.1 t h.2) h
    · exact absurd h (by simp [recLinear])
  | Gamma is ts fs q keep ord ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h, fun _ _ h => h.elim⟩
  | GammaScalar ts fs q ord ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h, fun _ _ h => h.elim⟩
  | GammaNest is his p g q ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h, fun _ _ h => h.elim⟩
  | ProvSum is his t q ih => exact fun f hu _ => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun f hu _ => hu.elim
  | Win P O o w t g q hrr dist keep ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h, fun _ _ h => h.elim⟩
  | WinExpr P O o ws ts fs g q keeps ih =>
    exact fun f hu hh => ⟨fun t h => (ih f hu.2 hh).1 t h, fun _ _ h => h.elim⟩

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **The pass explodes nothing.** -/
theorem noExplode_muSetFreeA (cnt : SeqAggFunc T) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), q.usesOnly (Set.univ \ {OpKind.union}) → q.hygienic → q.noExplode →
        (muSetFreeA cnt f q).noExplode := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ h => h
  | Hole _ _ _ => exact fun _ _ _ h => h
  | Param _ _ => exact fun _ _ _ h => h
  | Empty => exact fun _ _ _ h => h
  | Proj ps q ih => exact fun f hu hh hx => ih f hu.2 hh hx
  | Sel φ q hφ ih => exact fun f hu hh hx => ih f hu.2 hh hx
  | Prod q₁ q₂ ih₁ ih₂ => exact fun f hu hh hx =>
      ⟨ih₁ _ hu.2.1 hh.1 hx.1, ih₂ _ hu.2.2 hh.2 hx.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun f hu hh hx =>
      ⟨ih₁ _ hu.2.1 hh.1 hx.1, ih₂ _ hu.2.2 hh.2 hx.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f hu _ _ => absurd hu.1 (by simp)
  | Dedup q ih => exact fun f hu hh hx => ih f hu.2 hh hx
  | Diff q₁ q₂ ih₁ ih₂ => exact fun f hu hh hx =>
      ⟨ih₁ _ hu.2.1 hh.1 hx.1, ih₂ _ hu.2.2 hh.2 hx.2⟩
  | Explode k hk q ih => exact fun _ _ _ hx => hx.elim
  | Retag hk q ih => exact fun f hu hh hx => ih f hu hh hx
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun f hu hh hx =>
      ⟨ih₀ _ hu.2.1 hh.2.2.1 hx.1, ih₁ _ hu.2.2 hh.2.2.2 hx.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f hu hh hx
    have hlin : q₁.recLinear s _ := recLinear_of_usesOnly (by simp) q₁ rfl hh.2.1 hu.2.2
    exact noExplode_muSetSim cnt s _ q₀ q₁ _ _
      ((muSetFreeA_struct cnt q₁ _ hu.2.2 hh.2.2.2).2 s _ hlin)
      (ih₀ _ hu.2.1 hh.2.2.1 hx.1) (ih₁ _ hu.2.2 hh.2.2.2 hx.2)
  | Gamma is ts fs q keep ord ih => exact fun f hu hh hx => ih f hu.2 hh hx
  | GammaScalar ts fs q ord ih => exact fun f hu hh hx => ih f hu.2 hh hx
  | GammaNest is his p g q ih => exact fun f hu hh hx => ih f hu.2 hh hx
  | ProvSum is his t q ih => exact fun f hu _ _ => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun f hu _ _ => hu.elim
  | Win P O o w t g q hrr dist keep ih => exact fun f hu hh hx => ih f hu.2 hh hx
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f hu hh hx => ih f hu.2 hh hx

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Two bag recursions agreeing along the rounds of one of them** have the
same rounds and the same value. -/
theorem iterate_congr_iter {α : Type} {step step' : Multiset α → Multiset α} {M : Multiset α}
    (h : ∀ k, step' (step^[k] M) = step (step^[k] M)) : ∀ k, step'^[k] M = step^[k] M
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_congr_iter h k, h k]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem muSumFix_congr_iter {α : Type} {step step' : Multiset α → Multiset α} {M : Multiset α}
    (h : ∀ k, step' (step^[k] M) = step (step^[k] M)) : muSumFix step' M = muSumFix step M := by
  have hi := iterate_congr_iter h
  have hr : muRounds step' M = muRounds step M := by
    unfold muRounds
    congr 1
    ext j
    simp only [Set.mem_ofPred_eq, hi]
  rw [muSumFix, muSumFix, hr, muSum_eq_sum, muSum_eq_sum]
  exact Finset.sum_congr rfl fun j _ => hi j

/-- **The pass changes no annotated evaluation where the query settles**,
and its result settles there too: at an instance passing the counter's
requirements (`CounterOK`), in a semiring of `PathSum.SettlesEarly`, for a
count `cnt` and a query of `𝒜(∅, {cnt})` with no union and no explosion. -/
theorem muSetFreeA_correct (cnt : SeqAggFunc T) (hcnt : cnt.ReadsCount)
    (hK : PathSum.SettlesEarly K) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (f : ℕ → String), q.usesOnly (Set.univ \ {OpKind.union}) → q.inSig {cnt} → q.hygienic →
      q.noExplode → ∀ {ρc : Fin c → ColKind} {HK : HoleKinds}, q.wellKinded ρc HK →
      ∀ (d : AnnotatedDatabase T K), CounterOK d → ∀ (γ : Fin c → T) (E : EvalEnv T K),
        E.Kinded γ ρc HK → q.AnnSettlesAt d γ E →
        (muSetFreeA cnt f q).AnnSettlesAt d γ E
          ∧ (muSetFreeA cnt f q).evaluate d γ E = q.evaluate d γ E := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intro _ _ _ _ _ _ _ _ _ _ _ _ _ hs; exact ⟨hs, rfl⟩
  | Hole _ _ _ => intro _ _ _ _ _ _ _ _ _ _ _ _ _ hs; exact ⟨hs, rfl⟩
  | Param _ _ => intro _ _ _ _ _ _ _ _ _ _ _ _ _ hs; exact ⟨hs, rfl⟩
  | Empty => intro _ _ _ _ _ _ _ _ _ _ _ _ _ hs; exact ⟨hs, rfl⟩
  | Proj ps q ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu.2 hi.2 hh hx hw.2 d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | Sel φ q hφ ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu.2 hi.2 hh hx hw.2 d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨a₁, b₁⟩ := ih₁ _ hu.2.1 hi.1 hh.1 hx.1 hw.1 d hd γ E hE hs.1
    obtain ⟨a₂, b₂⟩ := ih₂ _ hu.2.2 hi.2 hh.2 hx.2 hw.2 d hd γ E hE hs.2
    exact ⟨⟨a₁, a₂⟩, by simp only [muSetFreeA, evaluate, b₁, b₂]⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨a₁, b₁⟩ := ih₁ _ hu.2.1 hi.1 hh.1 hx.1 hw.1 d hd γ E hE hs.1
    have h₂ : ∀ x ∈ q₁.evaluate d γ E, _ := fun x hxm =>
      ih₂ (tri f 2) hu.2.2 hi.2 hh.2 hx.2 hw.2 d hd _ _
        (hE.enter (fun k => evaluate_conform q₁ d x hxm k)) (hs.2 x hxm)
    refine ⟨⟨a₁, fun x hxm => ?_⟩, ?_⟩
    · rw [b₁] at hxm
      exact (h₂ x hxm).1
    · simp only [muSetFreeA, evaluate, b₁]
      exact Multiset.bind_congr fun x hxm => by rw [(h₂ x hxm).2]
  | Sum q₁ q₂ ih₁ ih₂ => exact fun f hu => absurd hu.1 (by simp)
  | Dedup q ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu.2 hi hh hx hw d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨a₁, b₁⟩ := ih₁ _ hu.2.1 hi.1 hh.1 hx.1 hw.1 d hd γ E hE hs.1
    obtain ⟨a₂, b₂⟩ := ih₂ _ hu.2.2 hi.2 hh.2 hx.2 hw.2 d hd γ E hE hs.2
    exact ⟨⟨a₁, a₂⟩, by simp only [muSetFreeA, evaluate, b₁, b₂]⟩
  | Explode k hk q ih => exact fun f _ _ _ hx => hx.elim
  | Retag hk q ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu hi hh hx hw d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' n' κ'
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨hs₀, hz, hm, hk, hk0⟩ := hs
    obtain ⟨a₀, b₀⟩ := ih₀ (tri f 1) hu.2.1 hi.1 hh.2.2.1 hx.1 hw.1 d hd γ E hE hs₀
    set M := q₀.evaluate d γ E with hM
    have hconf : ∀ k, ∀ x ∈ (muStep s q₁ d γ E)^[k] M,
        GenRow.Conforms κ' x.fst := by
      intro k x hxm
      cases k with
      | zero => exact fun j => evaluate_conform q₀ d x hxm j
      | succ k =>
        rw [Function.iterate_succ_apply'] at hxm
        exact fun j => evaluate_conform q₁ d x hxm j
    have h₁ : ∀ k, _ := fun k => ih₁ (tri f 2) hu.2.2 hi.2 hh.2.2.2 hx.2 hw.2 d hd γ _
      (hE.assignHole s (hconf k)) (hk k)
    have h₁0 := ih₁ (tri f 2) hu.2.2 hi.2 hh.2.2.2 hx.2 hw.2 d hd γ _
      (hE.assignHole s (fun x hxm => absurd hxm (Multiset.notMem_zero x))) hk0
    have hst : ∀ k, muStep s (muSetFreeA cnt (tri f 2) q₁) d γ E ((muStep s q₁ d γ E)^[k] M)
        = muStep s q₁ d γ E ((muStep s q₁ d γ E)^[k] M) := fun k => (h₁ k).2
    have hit := iterate_congr_iter hst
    refine ⟨⟨a₀, ?_, ?_, fun k => ?_, h₁0.1⟩, ?_⟩
    · exact h₁0.2.trans hz
    · obtain ⟨j, hj⟩ := hm
      refine ⟨j, ?_⟩
      show (muStep s (muSetFreeA cnt (tri f 2) q₁) d γ E)^[j + 1]
        ((muSetFreeA cnt (tri f 1) q₀).evaluate d γ E) = 0
      rw [b₀, hit]
      exact hj
    · show (muSetFreeA cnt (tri f 2) q₁).AnnSettlesAt d γ (E.assignHole s
        ((muStep s (muSetFreeA cnt (tri f 2) q₁) d γ E)^[k]
          ((muSetFreeA cnt (tri f 1) q₀).evaluate d γ E)))
      rw [b₀, hit]
      exact (h₁ k).1
    · show muSumFix (muStep s (muSetFreeA cnt (tri f 2) q₁) d γ E)
        ((muSetFreeA cnt (tri f 1) q₀).evaluate d γ E) = muSumFix (muStep s q₁ d γ E) M
      rw [b₀]
      exact muSumFix_congr_iter hst
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    have hlin : q₁.recLinear s _ := recLinear_of_usesOnly (by simp) q₁ rfl hh.2.1 hu.2.2
    have hlin' := (muSetFreeA_struct cnt q₁ (tri f 2) hu.2.2 hh.2.2.2).2 s _ hlin
    have hx' := noExplode_muSetFreeA cnt q₁ (tri f 2) hu.2.2 hh.2.2.2 hx.2
    exact muSetSim_correct cnt hcnt hK s (f 0) q₀ q₁ _ _ hlin hx.2 hlin' hx' hi hh hx hw d hd γ
      E hE hs (ih₀ (tri f 1) hu.2.1 hi.1 hh.2.2.1 hx.1 hw.1 d hd γ E hE hs.1)
      (fun X hX => ih₁ (tri f 2) hu.2.2 hi.2 hh.2.2.2 hx.2 hw.2 d hd γ _
        (hE.assignHole s (fun r hr => by
          obtain ⟨p, -, rfl⟩ := Multiset.mem_map.1 hr
          exact fun k => rfl)) hX)
  | Gamma is ts fs q keep ord ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu.2 hi.2.2.2 hh hx hw.2 d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | GammaScalar ts fs q ord ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu.2 hi.2.2 hh hx hw.2 d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | GammaNest is his p g q ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu.2 hi.2.2 hh hx hw.2 d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | ProvSum is his t q ih => exact fun f hu => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun f hu => hu.elim
  | Win P O o w t g q hrr dist keep ih =>
    intro f hu hi hh hx ρc HK hw d hd γ E hE hs
    obtain ⟨h₁, h₂⟩ := ih f hu.2 hi.2.2.2 hh hx hw.2 d hd γ E hE hs
    exact ⟨h₁, by simp only [muSetFreeA, evaluate, h₂]⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun f _ hi => hi.elim

end AggQueryIn
