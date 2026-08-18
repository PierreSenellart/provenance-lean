/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryBridges
import Provenance.AggQueryHom

/-!
# Embedding the classical query syntax into the general evaluator

`Query.toAgg` embeds a non-aggregating classical query into the
kind-indexed general syntax `AggQuery`, over all-regular kinds:
terms, selection predicates and every operator translate one to one.
`Query.toAgg_bridge` proves the embedding faithful – the general
evaluator computes the classical annotated semantics – via a row-wise
invariant `GenRow.Inv` (regular data, finalized annotation) that absorbs
the bookkeeping differences of the factored annotations (a pending
multiset that stays empty, bases multiplied by empty products).

On top of the embedding, `Query.toAggHaving_input` reads the input
relation of a general `HAVING` site over an embedded subquery off the
classical query's annotated semantics, which is what the query-level
`HAVING` correctness results consume.

This module sits *below* the classical `HAVING` correctness files
(`Provenance.HavingQueryCorrectness`,
`Provenance.HavingJoinCompositional`) so that they can state their
theorems over the embedded general query directly, with no side
hypothesis. The compositional JOIN rewriting built on top of the
embedding lives in `Provenance.AggQueryEmbedding`.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## Terms and selections over all-regular kinds -/

/-- A classical term, as a term over all-regular columns. -/
def Term.toGenReg {n : ℕ} : Term T n → TermG T (ColKind.allReg n)
  | .const a => .const a
  | .index k => .index k rfl
  | .add t₁ t₂ => .add t₁.toGenReg t₂.toGenReg
  | .sub t₁ t₂ => .sub t₁.toGenReg t₂.toGenReg
  | .mul t₁ t₂ => .mul t₁.toGenReg t₂.toGenReg

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The embedded term evaluates on a regular-values row as the original
term on the underlying tuple. -/
theorem Term.toGenReg_eval {n : ℕ} (t : Term T n) (x : Tuple T n) :
    (t.toGenReg).eval (fun k => (Sum.inl (x k) : GenValue T K)) = t.eval x := by
  induction t with
  | const a => rfl
  | index k => rfl
  | add t₁ t₂ ih₁ ih₂ => rw [Term.toGenReg, TermG.eval, ih₁, ih₂]; rfl
  | sub t₁ t₂ ih₁ ih₂ => rw [Term.toGenReg, TermG.eval, ih₁, ih₂]; rfl
  | mul t₁ t₂ ih₁ ih₂ => rw [Term.toGenReg, TermG.eval, ih₁, ih₂]; rfl

/-- A comparison atom, as a generalized regular atom. -/
def BoolTerm.toGenPred {n : ℕ} : BoolTerm T n →
    GenPred T (ColKind.allReg n)
  | .EQ t₁ t₂ => .cmp .eq t₁.toGenReg t₂.toGenReg
  | .NE t₁ t₂ => .cmp .ne t₁.toGenReg t₂.toGenReg
  | .LE t₁ t₂ => .cmp .le t₁.toGenReg t₂.toGenReg
  | .LT t₁ t₂ => .cmp .lt t₁.toGenReg t₂.toGenReg
  | .GE t₁ t₂ => .cmp .ge t₁.toGenReg t₂.toGenReg
  | .GT t₁ t₂ => .cmp .gt t₁.toGenReg t₂.toGenReg

/-- A classical selection predicate, as a generalized predicate without
aggregate atoms (`Selection.True` becomes the tautology `𝟘 = 𝟘`). -/
def Selection.toGenPred {n : ℕ} : Selection T n →
    GenPred T (ColKind.allReg n)
  | .BT b => b.toGenPred
  | .Not φ => .not φ.toGenPred
  | .And φ₁ φ₂ => .and φ₁.toGenPred φ₂.toGenPred
  | .Or φ₁ φ₂ => .or φ₁.toGenPred φ₂.toGenPred
  | .True => .cmp .eq (.const 0) (.const 0)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Embedded selections have no aggregate atoms: the evaluator filters
classically. -/
theorem Selection.toGenPred_hasAggAtom {n : ℕ} : ∀ (φ : Selection T n),
    (φ.toGenPred).hasAggAtom = false
  | .BT b => by cases b <;> rfl
  | .Not φ => toGenPred_hasAggAtom φ
  | .And φ₁ φ₂ => by
    show (_ || _) = false
    rw [toGenPred_hasAggAtom φ₁, toGenPred_hasAggAtom φ₂]
    rfl
  | .Or φ₁ φ₂ => by
    show (_ || _) = false
    rw [toGenPred_hasAggAtom φ₁, toGenPred_hasAggAtom φ₂]
    rfl
  | .True => rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The embedded predicate holds on a regular-values row exactly when the
original selection accepts the underlying tuple. -/
theorem Selection.toGenPred_holds {n : ℕ} : ∀ (φ : Selection T n)
    (x : Tuple T n),
    (φ.toGenPred).holds (K := K) (fun k => Sum.inl (x k)) ↔ φ.eval x
  | .BT b, x => by
    cases b <;>
      (simp only [BoolTerm.toGenPred, Selection.toGenPred, GenPred.holds,
        CompOp.eval, BoolTerm.eval, Selection.eval];
       rw [Term.toGenReg_eval, Term.toGenReg_eval])
  | .Not φ, x => by
    show ¬ (φ.toGenPred).holds (K := K) _ ↔ ¬ φ.eval x
    exact not_congr (toGenPred_holds φ x)
  | .And φ₁ φ₂, x => by
    show (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr (toGenPred_holds φ₁ x) (toGenPred_holds φ₂ x)
  | .Or φ₁ φ₂, x => by
    show (_ ∨ _) ↔ (_ ∨ _)
    exact or_congr (toGenPred_holds φ₁ x) (toGenPred_holds φ₂ x)
  | .True, x => by
    show (0 : T) = 0 ↔ (true : Prop)
    simp

/-! ## The embedding -/

omit [ValueType T] in
/-- Appending all-regular kind vectors. -/
theorem ColKind.allReg_append (n₁ n₂ : ℕ) :
    Fin.append (ColKind.allReg n₁) (ColKind.allReg n₂)
      = ColKind.allReg (n₁ + n₂) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]
    rfl
  · rw [Fin.append_right]
    rfl

/-- **The embedding of the non-aggregating fragment**: every classical
operator translates to its general counterpart, over all-regular
kinds. -/
def Query.toAgg : {n : ℕ} → (q : Query T n) → q.source →
    AggQuery T n (ColKind.allReg n)
  | n, .Rel _ s, _ => AggQuery.Rel n s
  | _, .Proj ts q, hq =>
    AggQuery.castKind (funext fun _ => rfl)
      (AggQuery.Proj (fun j => ProjCol.term ((ts j).toGenReg))
        (q.toAgg (Query.sourceProj hq rfl)))
  | _, .Sel φ q, hq =>
    AggQuery.Sel φ.toGenPred (q.toAgg (Query.sourceSel hq rfl))
  | _, @Query.Prod _ n₁ n₂ n hn q₁ q₂, hq =>
    hn ▸ AggQuery.castKind (ColKind.allReg_append n₁ n₂)
      (AggQuery.Prod (q₁.toAgg (Query.sourceProd hq rfl).left)
        (q₂.toAgg (Query.sourceProd hq rfl).right))
  | _, .Sum q₁ q₂, hq =>
    AggQuery.Sum (q₁.toAgg (Query.sourceSum hq rfl).left)
      (q₂.toAgg (Query.sourceSum hq rfl).right)
  | _, .Dedup q, hq => AggQuery.Dedup (q.toAgg (Query.sourceDedup hq rfl))
  | _, .Diff q₁ q₂, hq =>
    AggQuery.Diff (q₁.toAgg (Query.sourceDiff hq rfl).left)
      (q₂.toAgg (Query.sourceDiff hq rfl).right)
  | _, .ProvSum _ _ _, hq => False.elim (by simp [Query.source] at hq)
  | _, .Having _ _ _ _ _ _ _, hq =>
    False.elim (by simp [Query.source] at hq)

/-! ## Faithfulness -/

/-- The row invariant of the embedding: regular data over the classical
tuple, a factored annotation finalizing to the classical one, and no
pending group factors (the embedding image contains no `Gamma`). -/
def GenRow.Inv {n : ℕ} (r : GenRow T K n) (p : AnnotatedTuple T K n) :
    Prop :=
  r.fst = (fun k => Sum.inl (p.fst k)) ∧ r.snd.finalize = p.snd
    ∧ r.snd.pending = 0

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- Invariant rows finalize to their classical counterparts. -/
theorem GenRow.Inv.toAnnotated_eq {n : ℕ} {r : GenRow T K n}
    {p : AnnotatedTuple T K n} (h : GenRow.Inv r p) :
    GenRow.toAnnotated r = p := by
  refine Prod.ext ?_ h.2.1
  funext k
  show AggValue.collapseSum (r.fst k) = p.fst k
  rw [h.1]
  rfl

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- Embedded classical rows satisfy the invariant. -/
theorem rel_inv_ofAnnotated {n : ℕ} (X : AnnotatedRelation T K n) :
    Multiset.Rel GenRow.Inv (X.map GenRow.ofAnnotated) X := by
  rw [show X = X.map id from (Multiset.map_id X).symm, Multiset.map_map]
  refine rel_map_of_forall (fun p _ => ⟨rfl, ?_, rfl⟩)
  show GenAnn.finalize ⟨(id p).snd, 0⟩ = (id p).snd
  rw [GenAnn.finalize_of_pending_zero]

/-- **Faithfulness of the embedding, row for row**: the general evaluator
on the embedded query produces rows satisfying the invariant against the
classical annotated evaluation. -/
theorem Query.toAgg_rel :
    ∀ {n : ℕ} (q : Query T n) (hq : q.source) (d : AnnotatedDatabase T K),
      Multiset.Rel GenRow.Inv ((q.toAgg hq).evaluate d)
        (q.evaluateAnnotated hq d)
  | n, .Rel _ s, hq, d => by
    show Multiset.Rel _ (match d.find n s with
      | none => (∅ : Multiset (GenRow T K n))
      | some rn => rn.map GenRow.ofAnnotated) _
    unfold Query.evaluateAnnotated
    cases d.find n s with
    | none => exact Multiset.Rel.zero
    | some rn => exact rel_inv_ofAnnotated rn
  | _, .Proj ts q, hq, d => by
    show Multiset.Rel _ ((AggQuery.castKind _ _).evaluate d) _
    rw [AggQuery.evaluate_castKind]
    refine rel_map_of_rel (toAgg_rel q (Query.sourceProj hq rfl) d)
      (fun r p hr => ⟨?_, ?_, ?_⟩)
    · funext j
      show Sum.inl (((ts j).toGenReg).eval r.fst)
        = Sum.inl ((ts j).eval p.fst)
      rw [hr.1, Term.toGenReg_eval]
    · exact (GenAnn.finalize_cash _ _ _ Multiset.inter_le_left).trans hr.2.1
    · show r.snd.pending ∩ _ = 0
      rw [hr.2.2]
      exact Multiset.zero_inter _
  | _, .Sel φ q, hq, d => by
    show Multiset.Rel _
      (if (Selection.toGenPred φ).hasAggAtom then _ else
        Multiset.filter _ ((Query.toAgg q
          (Query.sourceSel hq rfl)).evaluate d)) _
    rw [if_neg (by rw [Selection.toGenPred_hasAggAtom]; exact
      Bool.false_ne_true)]
    refine rel_filter_of_iff (toAgg_rel q (Query.sourceSel hq rfl) d)
      (fun r p hr => ?_)
    rw [hr.1]
    exact Selection.toGenPred_holds φ p.fst
  | _, @Query.Prod _ n₁ n₂ n hn q₁ q₂, hq, d => by
    subst hn
    show Multiset.Rel _ ((AggQuery.castKind _
      (AggQuery.Prod (q₁.toAgg (Query.sourceProd hq rfl).left)
        (q₂.toAgg (Query.sourceProd hq rfl).right))).evaluate d) _
    rw [AggQuery.evaluate_castKind]
    refine rel_map_of_rel
      (rel_product (toAgg_rel q₁ (Query.sourceProd hq rfl).left d)
        (toAgg_rel q₂ (Query.sourceProd hq rfl).right d)) ?_
    rintro ⟨x, y⟩ ⟨p, p'⟩ ⟨hx, hy⟩
    refine ⟨?_, ?_, ?_⟩
    · funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · show Fin.append x.fst y.fst (Fin.castAdd n₂ j) = _
        rw [Fin.append_left, hx.1]
        show Sum.inl (p.fst j)
          = Sum.inl (Fin.append p.fst p'.fst (Fin.castAdd n₂ j))
        rw [Fin.append_left]
      · show Fin.append x.fst y.fst (Fin.natAdd n₁ j) = _
        rw [Fin.append_right, hy.1]
        show Sum.inl (p'.fst j)
          = Sum.inl (Fin.append p.fst p'.fst (Fin.natAdd n₁ j))
        rw [Fin.append_right]
    · show GenAnn.finalize ⟨x.snd.base * y.snd.base,
        x.snd.pending + y.snd.pending⟩ = p.snd * p'.snd
      rw [GenAnn.finalize_prod, hx.2.1, hy.2.1]
    · show x.snd.pending + y.snd.pending = 0
      rw [hx.2.2, hy.2.2]
      rfl
  | _, .Sum q₁ q₂, hq, d =>
    Multiset.Rel.add (toAgg_rel q₁ (Query.sourceSum hq rfl).left d)
      (toAgg_rel q₂ (Query.sourceSum hq rfl).right d)
  | _, .Dedup q, hq, d => by
    show Multiset.Rel _ ((Multiset.ofList (groupByKey
      (((q.toAgg (Query.sourceDedup hq rfl)).evaluate d).map
        GenRow.toAnnotated)).val).map GenRow.ofAnnotated) _
    rw [show ((q.toAgg (Query.sourceDedup hq rfl)).evaluate
          d).map GenRow.toAnnotated
        = q.evaluateAnnotated (Query.sourceDedup hq rfl) d from
      (map_eq_of_rel (toAgg_rel q (Query.sourceDedup hq rfl) d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    exact rel_inv_ofAnnotated _
  | _, .Diff q₁ q₂, hq, d => by
    show Multiset.Rel _ ((((((q₁.toAgg
      (Query.sourceDiff hq rfl).left).evaluate d).map
        GenRow.toAnnotated)).map _).map GenRow.ofAnnotated) _
    rw [show ((q₁.toAgg
          (Query.sourceDiff hq rfl).left).evaluate d).map GenRow.toAnnotated
        = q₁.evaluateAnnotated (Query.sourceDiff hq rfl).left d from
      (map_eq_of_rel (toAgg_rel q₁ (Query.sourceDiff hq rfl).left d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [show ((q₂.toAgg
          (Query.sourceDiff hq rfl).right).evaluate d).map GenRow.toAnnotated
        = q₂.evaluateAnnotated (Query.sourceDiff hq rfl).right d from
      (map_eq_of_rel (toAgg_rel q₂ (Query.sourceDiff hq rfl).right d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [Multiset.map_map]
    refine rel_map_of_forall (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    exact ⟨rfl, GenAnn.finalize_of_pending_zero _, rfl⟩

/-- **Faithfulness of the embedding**: the general evaluator computes the
classical annotated semantics on embedded queries. -/
theorem Query.toAgg_bridge {n : ℕ} (q : Query T n) (hq : q.source)
    (d : AnnotatedDatabase T K) :
    (q.toAgg hq).evaluateAnnotated (K := K) d
      = q.evaluateAnnotated hq d := by
  unfold AggQuery.evaluateAnnotated
  exact (map_eq_of_rel (Query.toAgg_rel q hq d)
    (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- An invariant row *is* the embedding of its classical counterpart: the
pending multiset is empty, so the base coincides with the finalized
annotation. -/
theorem GenRow.Inv.row_eq {n : ℕ} {r : GenRow T K n}
    {p : AnnotatedTuple T K n} (h : GenRow.Inv r p) :
    r = GenRow.ofAnnotated p := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨u, b, P⟩ := r
  replace h3 : P = 0 := h3
  subst h3
  replace h2 : GenAnn.finalize ⟨b, 0⟩ = p.snd := h2
  refine Prod.ext h1 ?_
  show GenAnn.mk b 0 = ⟨p.snd, 0⟩
  rw [show b = p.snd from by rw [← h2, GenAnn.finalize_of_pending_zero]]

/-- **The embedding at the row level**: the general evaluator on an
embedded query produces exactly the embedded classical rows. -/
theorem Query.toAgg_evaluate_eq {n : ℕ} (q : Query T n) (hq : q.source)
    (d : AnnotatedDatabase T K) :
    (q.toAgg hq).evaluate d
      = (q.evaluateAnnotated hq d).map GenRow.ofAnnotated :=
  Eq.trans (Multiset.map_id _).symm
    (map_eq_of_rel (Query.toAgg_rel q hq d) (fun _ _ hr => hr.row_eq))

/-! ## The fused `HAVING`, in context -/

/-- **The fused `HAVING` site over an embedded subquery**: its input
relation is the classical subquery's annotated evaluation, so the closed
form `AggQuery.havingSite_evaluateAnnotated` specializes to the
classical setting with no side hypothesis. -/
theorem Query.toAggHaving_input {m : ℕ} (q : Query T m) (hq : q.source)
    (d : AnnotatedDatabase T K) :
    (q.toAgg hq).evaluateAnnotated d = q.evaluateAnnotated hq d :=
  Query.toAgg_bridge q hq d
