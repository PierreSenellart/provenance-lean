/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryGenBridges
import Provenance.QueryGenHom
import Provenance.HavingJoinCompositional

/-!
# Embedding the classical query syntax into the general evaluator

`Query.toGen` embeds a non-aggregating classical query into the
kind-indexed general syntax `QueryGen`, over all-regular kinds:
terms, selection predicates and every operator translate one to one.
`Query.toGen_bridge` proves the embedding faithful – the general
evaluator computes the classical annotated semantics – via a row-wise
invariant `GenRow.Inv` (regular data, finalized annotation) that absorbs
the bookkeeping differences of the factored annotations (a pending
multiset that stays empty, bases multiplied by empty products).

On top of the embedding, the fused `HAVING` operator is bridged in
context (`Query.toGenHaving_bridge`, instantiating the regression bridge
`QueryGen.fused_having_bridge` with the embedded inner query), and the
compositional JOIN rewriting is stated natively on the general syntax:
`GenCountHavingRewrite` replaces `HAVING COUNT(*)` sites – the key
projection of `σ_ψ ∘ Gamma`, an *all-regular* query that composes under
every operator – by the embedded padded join query, and
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
def Query.toGen : {n : ℕ} → (q : Query T n) → q.noAgg →
    QueryGen T n (ColKind.allReg n)
  | n, .Rel _ s, _ => QueryGen.Rel n s
  | _, .Proj ts q, hq =>
    QueryGen.castKind (funext fun _ => rfl)
      (QueryGen.Proj (fun j => ProjCol.term ((ts j).toGenReg))
        (q.toGen (Query.noAggProj hq rfl)))
  | _, .Sel φ q, hq =>
    QueryGen.Sel φ.toGenPred (q.toGen (Query.noAggSel hq rfl))
  | _, @Query.Prod _ n₁ n₂ n hn q₁ q₂, hq =>
    hn ▸ QueryGen.castKind (ColKind.allReg_append n₁ n₂)
      (QueryGen.Prod (q₁.toGen (Query.noAggProd hq rfl).left)
        (q₂.toGen (Query.noAggProd hq rfl).right))
  | _, .Sum q₁ q₂, hq =>
    QueryGen.Sum (q₁.toGen (Query.noAggSum hq rfl).left)
      (q₂.toGen (Query.noAggSum hq rfl).right)
  | _, .Dedup q, hq => QueryGen.Dedup (q.toGen (Query.noAggDedup hq rfl))
  | _, .Diff q₁ q₂, hq =>
    QueryGen.Diff (q₁.toGen (Query.noAggDiff hq rfl).left)
      (q₂.toGen (Query.noAggDiff hq rfl).right)
  | _, .Agg _ _ _ _, hq => False.elim (by simp [Query.noAgg] at hq)
  | _, .Having _ _ _ _ _ _ _, hq =>
    False.elim (by simp [Query.noAgg] at hq)

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
theorem Query.toGen_rel :
    ∀ {n : ℕ} (q : Query T n) (hq : q.noAgg) (d : AnnotatedDatabase T K),
      Multiset.Rel GenRow.Inv ((q.toGen hq).evaluateGen d)
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
    show Multiset.Rel _ ((QueryGen.castKind _ _).evaluateGen d) _
    rw [QueryGen.evaluateGen_castKind]
    refine rel_map_of_rel (toGen_rel q (Query.noAggProj hq rfl) d)
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
        Multiset.filter _ ((Query.toGen q
          (Query.noAggSel hq rfl)).evaluateGen d)) _
    rw [if_neg (by rw [Selection.toGenPred_hasAggAtom]; exact
      Bool.false_ne_true)]
    refine rel_filter_of_iff (toGen_rel q (Query.noAggSel hq rfl) d)
      (fun r p hr => ?_)
    rw [hr.1]
    exact Selection.toGenPred_holds φ p.fst
  | _, @Query.Prod _ n₁ n₂ n hn q₁ q₂, hq, d => by
    subst hn
    show Multiset.Rel _ ((QueryGen.castKind _
      (QueryGen.Prod (q₁.toGen (Query.noAggProd hq rfl).left)
        (q₂.toGen (Query.noAggProd hq rfl).right))).evaluateGen d) _
    rw [QueryGen.evaluateGen_castKind]
    refine rel_map_of_rel
      (rel_product (toGen_rel q₁ (Query.noAggProd hq rfl).left d)
        (toGen_rel q₂ (Query.noAggProd hq rfl).right d)) ?_
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
    Multiset.Rel.add (toGen_rel q₁ (Query.noAggSum hq rfl).left d)
      (toGen_rel q₂ (Query.noAggSum hq rfl).right d)
  | _, .Dedup q, hq, d => by
    show Multiset.Rel _ ((Multiset.ofList (groupByKey
      (((q.toGen (Query.noAggDedup hq rfl)).evaluateGen d).map
        GenRow.toAnnotated)).val).map GenRow.ofAnnotated) _
    rw [show ((q.toGen (Query.noAggDedup hq rfl)).evaluateGen
          d).map GenRow.toAnnotated
        = q.evaluateAnnotated (Query.noAggDedup hq rfl) d from
      (map_eq_of_rel (toGen_rel q (Query.noAggDedup hq rfl) d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    exact rel_inv_ofAnnotated _
  | _, .Diff q₁ q₂, hq, d => by
    show Multiset.Rel _ ((((((q₁.toGen
      (Query.noAggDiff hq rfl).left).evaluateGen d).map
        GenRow.toAnnotated)).map _).map GenRow.ofAnnotated) _
    rw [show ((q₁.toGen
          (Query.noAggDiff hq rfl).left).evaluateGen d).map GenRow.toAnnotated
        = q₁.evaluateAnnotated (Query.noAggDiff hq rfl).left d from
      (map_eq_of_rel (toGen_rel q₁ (Query.noAggDiff hq rfl).left d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [show ((q₂.toGen
          (Query.noAggDiff hq rfl).right).evaluateGen d).map GenRow.toAnnotated
        = q₂.evaluateAnnotated (Query.noAggDiff hq rfl).right d from
      (map_eq_of_rel (toGen_rel q₂ (Query.noAggDiff hq rfl).right d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [Multiset.map_map]
    refine rel_map_of_forall (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    exact ⟨rfl, GenAnn.finalize_of_pending_zero _, rfl⟩

/-- **Faithfulness of the embedding**: the general evaluator computes the
classical annotated semantics on embedded queries. -/
theorem Query.toGen_bridge {n : ℕ} (q : Query T n) (hq : q.noAgg)
    (d : AnnotatedDatabase T K) :
    (q.toGen hq).evaluateAnnotatedGen (K := K) d
      = q.evaluateAnnotated hq d := by
  unfold QueryGen.evaluateAnnotatedGen
  exact (map_eq_of_rel (Query.toGen_rel q hq d)
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
theorem Query.toGen_evaluateGen_eq {n : ℕ} (q : Query T n) (hq : q.noAgg)
    (d : AnnotatedDatabase T K) :
    (q.toGen hq).evaluateGen d
      = (q.evaluateAnnotated hq d).map GenRow.ofAnnotated :=
  Eq.trans (Multiset.map_id _).symm
    (map_eq_of_rel (Query.toGen_rel q hq d) (fun _ _ hr => hr.row_eq))

/-! ## The fused `HAVING`, in context -/

/-- **The fused operator over an embedded subquery**: `σ_ψ ∘ Gamma` over
`q.toGen` computes the fused `HAVING` semantics – the regression bridge
`QueryGen.fused_having_bridge`, with its input hypothesis discharged by
the embedding. -/
theorem Query.toGenHaving_bridge {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (op : CompOp) (l : Fin n₂) (s : Term T n₁) (q : Query T m)
    (hq : q.noAgg) (d : AnnotatedDatabase T K) :
    (QueryGen.Sel (GenPred.fusedCmp op l s)
        (QueryGen.Gamma is ts fs (q.toGen hq))).evaluateAnnotatedGen d
      = Query.evaluateHavingAnnotated is ts fs op l s q hq d :=
  QueryGen.fused_having_bridge is ts fs op l s (q.toGen hq) q hq d
    (Query.toGen_bridge q hq d)

/-! ## The compositional JOIN rewriting, on the general syntax

The `HAVING COUNT(*)` site of the compositional rewriting theorem is,
in the general syntax, the key projection of `σ_ψ ∘ Gamma` – all-regular,
since the projection drops the token columns – so it composes under every
operator of the general syntax, and the ProvSQL-legal contexts around a
site are exactly the expressible ones. The rewrite relation below
replaces such sites by the embedded padded join query; its correctness is
a plain congruence induction whose site case chains the fused-operator
bridge, the multiset-level site correctness of
`Provenance.HavingJoinCompositional`, and the embedding. -/

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
    (g : QueryGen ℕ 3 (ColKind.allReg 3)) : QueryGen ℕ 1 (ColKind.allReg 1) :=
  QueryGen.castKind (funext fun _ => rfl)
    (QueryGen.Proj
      (fun _ : Fin 1 => ProjCol.term
        ((Term.index (⟨0, by omega⟩ : Fin 1)).toGenKey 1))
      (QueryGen.Sel (GenPred.fusedCmp op (0 : Fin 1) (Term.const (C + 1)))
        (QueryGen.Gamma keyIdx ts' (fun _ => SeqAggFunc.count) g)))

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
    (g : QueryGen ℕ 3 (ColKind.allReg 3)) (q' : Query ℕ 3)
    (hq' : q'.noAgg) (d : AnnotatedDatabase ℕ K)
    (hbridge : g.evaluateAnnotatedGen d = q'.evaluateAnnotated hq' d)
    (hnodup : ((q'.evaluateAnnotated hq' d).map Prod.fst).Nodup) :
    (genCountHavingSite ts' op C g).evaluateGen d
      = ((joinCountQueryPadded q' op C).toGen
          (joinCountQueryPadded_noAgg q' hq' op C)).evaluateGen d := by
  rw [Query.toGen_evaluateGen_eq,
    joinCountQueryPadded_correct h_abs h_distrib q' hq' d hnodup ts' op C,
    ← fused_key_proj q' hq' d ts' op C]
  refine Eq.trans (Multiset.map_congr rfl (fun r _ =>
    projTerm_row_eq
      (fun _ : Fin 1 => ProjCol.term
        ((Term.index (⟨0, by omega⟩ : Fin 1)).toGenKey 1))
      (fun _ => ⟨_, rfl⟩) r)) ?_
  rw [show Query.evaluateHavingAnnotated keyIdx ts'
        (fun _ => SeqAggFunc.count) op 0 (Term.const (C + 1)) q' hq' d
      = (QueryGen.Sel (GenPred.fusedCmp op (0 : Fin 1) (Term.const (C + 1)))
          (QueryGen.Gamma keyIdx ts' (fun _ => SeqAggFunc.count)
            g)).evaluateAnnotatedGen d from
    (QueryGen.fused_having_bridge keyIdx ts' (fun _ => SeqAggFunc.count)
      op 0 (Term.const (C + 1)) g q' hq' d hbridge).symm]
  unfold QueryGen.evaluateAnnotatedGen
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun r _ => rfl)

/-- **The JOIN rewriting on the general syntax**: congruence rules per
operator, and the site rule replacing a `HAVING COUNT(*)` site by the
embedded padded join query built over any classical query with the same
annotated semantics as the site's grouped subquery. -/
inductive GenCountHavingRewrite (d : AnnotatedDatabase ℕ K) :
    {n : ℕ} → {κ : Fin n → ColKind} →
    QueryGen ℕ n κ → QueryGen ℕ n κ → Prop
  | refl {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen ℕ n κ) :
      GenCountHavingRewrite d q q
  | proj {n m : ℕ} {κ : Fin n → ColKind} (ps : Tuple (ProjCol ℕ κ) m)
      {q q' : QueryGen ℕ n κ} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (QueryGen.Proj ps q) (QueryGen.Proj ps q')
  | sel {n : ℕ} {κ : Fin n → ColKind} (φ : GenPred ℕ κ)
      {q q' : QueryGen ℕ n κ} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (QueryGen.Sel φ q) (QueryGen.Sel φ q')
  | prod {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
      {q₁ q₁' : QueryGen ℕ n₁ κ₁} {q₂ q₂' : QueryGen ℕ n₂ κ₂} :
      GenCountHavingRewrite d q₁ q₁' → GenCountHavingRewrite d q₂ q₂' →
      GenCountHavingRewrite d (QueryGen.Prod q₁ q₂)
        (QueryGen.Prod q₁' q₂')
  | sum {n : ℕ} {κ : Fin n → ColKind} {q₁ q₁' q₂ q₂' : QueryGen ℕ n κ} :
      GenCountHavingRewrite d q₁ q₁' → GenCountHavingRewrite d q₂ q₂' →
      GenCountHavingRewrite d (QueryGen.Sum q₁ q₂)
        (QueryGen.Sum q₁' q₂')
  | dedup {n : ℕ} {q q' : QueryGen ℕ n (ColKind.allReg n)} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (QueryGen.Dedup q) (QueryGen.Dedup q')
  | diff {n : ℕ} {q₁ q₁' q₂ q₂' : QueryGen ℕ n (ColKind.allReg n)} :
      GenCountHavingRewrite d q₁ q₁' → GenCountHavingRewrite d q₂ q₂' →
      GenCountHavingRewrite d (QueryGen.Diff q₁ q₂)
        (QueryGen.Diff q₁' q₂')
  | gamma {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (Term ℕ m) n₂)
      (fs : Tuple (SeqAggFunc ℕ) n₂)
      {q q' : QueryGen ℕ m (ColKind.allReg m)} :
      GenCountHavingRewrite d q q' →
      GenCountHavingRewrite d (QueryGen.Gamma is ts fs q)
        (QueryGen.Gamma is ts fs q')
  | site (ts' : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ)
      {g g' : QueryGen ℕ 3 (ColKind.allReg 3)} (q' : Query ℕ 3)
      (hq' : q'.noAgg) :
      GenCountHavingRewrite d g g' →
      g'.evaluateAnnotatedGen d = q'.evaluateAnnotated hq' d →
      ((q'.evaluateAnnotated hq' d).map Prod.fst).Nodup →
      GenCountHavingRewrite d (genCountHavingSite ts' op C g)
        ((joinCountQueryPadded q' op C).toGen
          (joinCountQueryPadded_noAgg q' hq' op C))

/-- **Compositional correctness of the JOIN rewriting, general syntax**:
in an absorptive commutative m-semiring whose `⊗` distributes over `⊖`,
rewriting any number of `HAVING COUNT(*)` sites – wherever they occur –
preserves the general evaluator's rows verbatim. -/
theorem GenCountHavingRewrite.evaluateGen_eq
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    {d : AnnotatedDatabase ℕ K} :
    ∀ {n : ℕ} {κ : Fin n → ColKind} {q q' : QueryGen ℕ n κ},
      GenCountHavingRewrite d q q' →
      q.evaluateGen d = q'.evaluateGen d := by
  intro n κ q q' hrw
  induction hrw with
  | refl q => rfl
  | proj ps _ ih => simp only [QueryGen.evaluateGen]; rw [ih]
  | sel φ _ ih => simp only [QueryGen.evaluateGen]; rw [ih]
  | prod _ _ ih₁ ih₂ => simp only [QueryGen.evaluateGen]; rw [ih₁, ih₂]
  | sum _ _ ih₁ ih₂ => simp only [QueryGen.evaluateGen]; rw [ih₁, ih₂]
  | dedup _ ih => simp only [QueryGen.evaluateGen]; rw [ih]
  | diff _ _ ih₁ ih₂ => simp only [QueryGen.evaluateGen]; rw [ih₁, ih₂]
  | gamma is ts fs _ ih => simp only [QueryGen.evaluateGen]; rw [ih]
  | @site ts' op C g g' q' hq' _ hbridge hnodup ih =>
    have hbridge' : g.evaluateAnnotatedGen d
        = q'.evaluateAnnotated hq' d := by
      unfold QueryGen.evaluateAnnotatedGen
      rw [ih]
      exact hbridge
    exact genCountHavingSite_eval h_abs h_distrib ts' op C g q' hq' d
      hbridge' hnodup

/-- The finalized form of the compositional correctness. -/
theorem GenCountHavingRewrite.evaluateAnnotatedGen_eq
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    {d : AnnotatedDatabase ℕ K} {n : ℕ} {κ : Fin n → ColKind}
    {q q' : QueryGen ℕ n κ} (hrw : GenCountHavingRewrite d q q') :
    q.evaluateAnnotatedGen d = q'.evaluateAnnotatedGen d := by
  unfold QueryGen.evaluateAnnotatedGen
  rw [hrw.evaluateGen_eq h_abs h_distrib]

end GenRewrite
