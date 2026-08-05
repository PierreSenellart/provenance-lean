/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryGenAdequacy

/-!
# Regression bridges for the general evaluator

The fused `HAVING` operator is recovered from the decomposed general
syntax: on its fragment – one aggregate comparison directly above the
grouping – the general evaluator `σ_ψ ∘ Gamma` computes exactly the fused
semantics `Query.evaluateHavingAnnotated` (`QueryGen.fused_having_bridge`).
Row by row, the pending group factor introduced by `Gamma` is superseded
by the predicate provenance of the comparison (the token's `predProv`,
which is the fused `Having.havingProv` by `AggValue.predProv_ofGroup`),
and the data part collapses to the whole-group aggregate values.

Every theorem about the fused semantics – the possible-world collapses of
`Provenance.HavingSemantics`, the query-level correctness results – thus
transfers to the general evaluator on this fragment instead of being
reproved.

The bridge is stated against an arbitrary general subquery whose
annotated evaluation matches the fused operator's input relation; the
kind transport `QueryGen.castKind` is transparent to evaluation
(`QueryGen.evaluateGen_castKind`).
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-- Kind transport is transparent to evaluation (row types do not mention
the kind vector). -/
theorem QueryGen.evaluateGen_castKind {n : ℕ} {κ κ' : Fin n → ColKind}
    (h : κ = κ') (q : QueryGen T n κ) (d : AnnotatedDatabase T K) :
    (q.castKind h).evaluateGen d = q.evaluateGen d := by
  subst h; rfl

/-- The kind vector of a `Gamma` output: key columns then token columns. -/
abbrev ColKind.gammaKinds (n₁ n₂ : ℕ) : Fin (n₁ + n₂) → ColKind :=
  Fin.append (fun _ : Fin n₁ => ColKind.reg) (fun _ : Fin n₂ => ColKind.agg)

/-- A term over the group key, embedded as a term over the key columns of
a `Gamma` output. -/
def Term.toGenKey {n₁ : ℕ} (n₂ : ℕ) :
    Term T n₁ → TermG T (ColKind.gammaKinds n₁ n₂)
  | .const a => .const a
  | .index k => .index (Fin.castAdd n₂ k) (by simp [ColKind.gammaKinds])
  | .add t₁ t₂ => .add (t₁.toGenKey n₂) (t₂.toGenKey n₂)
  | .sub t₁ t₂ => .sub (t₁.toGenKey n₂) (t₂.toGenKey n₂)
  | .mul t₁ t₂ => .mul (t₁.toGenKey n₂) (t₂.toGenKey n₂)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The embedded key term evaluates on a `Gamma` output row as the
original term on the group key. -/
theorem Term.toGenKey_eval {n₁ n₂ : ℕ} (s : Term T n₁) (g : Tuple T n₁)
    (h : Fin n₂ → AggValue T K) :
    (s.toGenKey n₂).eval
        (Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun j => Sum.inr (h j)))
      = s.eval g := by
  induction s with
  | const a => rfl
  | index k =>
    show AggValue.collapseSum
        (Fin.append _ _ (Fin.castAdd n₂ k)) = g k
    rw [Fin.append_left]
    rfl
  | add t₁ t₂ ih₁ ih₂ => rw [Term.toGenKey, TermG.eval, ih₁, ih₂]; rfl
  | sub t₁ t₂ ih₁ ih₂ => rw [Term.toGenKey, TermG.eval, ih₁, ih₂]; rfl
  | mul t₁ t₂ ih₁ ih₂ => rw [Term.toGenKey, TermG.eval, ih₁, ih₂]; rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The annotation list of a group token is the group's annotation list. -/
theorem AggValue.annList_ofGroup {m : ℕ} (f : SeqAggFunc T) (t : Term T m)
    (U : List (AnnotatedTuple T K m)) :
    (AggValue.ofGroup f t U).occs.map Prod.snd = U.map Prod.snd := by
  show (U.map (fun p => (t.eval p.fst, p.snd))).map Prod.snd = _
  rw [List.map_map]
  rfl

/-- The fused aggregate comparison, as a generalized selection atom on a
`Gamma` output: the `l`-th token column compared against a term over the
group key. -/
def GenPred.fusedCmp {n₁ n₂ : ℕ} (op : CompOp) (l : Fin n₂)
    (s : Term T n₁) : GenPred T (ColKind.gammaKinds n₁ n₂) :=
  GenPred.aggCmp (Fin.natAdd n₁ l) (by simp [ColKind.gammaKinds]) op
    (s.toGenKey n₂)

/-- **The fused-operator regression bridge.** On its fragment – one
aggregate comparison directly above the grouping – the general evaluator
computes the fused `HAVING` semantics: for any general subquery whose
annotated evaluation is the fused operator's input relation, applying
`Gamma` then the selection `fusedCmp` yields, after finalization, exactly
`Query.evaluateHavingAnnotated`. -/
theorem QueryGen.fused_having_bridge {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (op : CompOp) (l : Fin n₂)
    (s : Term T n₁) (qg : QueryGen T m (ColKind.allReg m))
    (q : Query T m) (hq : q.noAgg) (d : AnnotatedDatabase T K)
    (hin : (qg.evaluateGen d).map GenRow.toAnnotated
      = q.evaluateAnnotated hq d) :
    (QueryGen.Sel (GenPred.fusedCmp op l s)
        (QueryGen.Gamma is ts fs qg)).evaluateAnnotatedGen d
      = Query.evaluateHavingAnnotated is ts fs op l s q hq d := by
  unfold QueryGen.evaluateAnnotatedGen Query.evaluateHavingAnnotated
  simp only [QueryGen.evaluateGen]
  rw [if_pos (show (GenPred.fusedCmp (T := T) op l s).hasAggAtom = true
    from rfl), hin]
  -- collapse the three nested maps on the left, outermost first
  conv_lhs => rw [Multiset.map_map]
  conv_lhs => rw [Multiset.map_map]
  -- identify the two key multisets
  have hkeys : Multiset.map Prod.fst (Multiset.ofList (groupByKey
        ((q.evaluateAnnotated hq d).map (fun p =>
          ((fun k => p.fst (is k), p.snd) : AnnotatedTuple T K n₁)))).val)
      = Multiset.dedup ((q.evaluateAnnotated hq d).map
          (fun p => fun k : Fin n₁ => p.fst (is k))) := by
    rw [map_fst_groupByKey, Multiset.map_map]
    rfl
  rw [← hkeys, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro kv _
  simp only [Function.comp_apply]
  unfold GenRow.toAnnotated
  refine Prod.ext ?_ ?_
  · -- data part: whole-group aggregate values
    exact (GenRow.plainTuple_append kv.fst _).trans
      (congrArg (Fin.append kv.fst)
        (funext fun j => AggValue.collapse_ofGroup (fs j) (ts j) _))
  · -- annotation: the predicate provenance of the comparison
    show GenAnn.finalize ⟨1 * _, _⟩ = _
    simp only [GenPred.fusedCmp, GenPred.predsem, GenPred.comparedCols,
      Finset.singleton_val, ← Multiset.cons_zero, Multiset.filterMap_cons,
      Multiset.filterMap_zero, Fin.append_right, AggValue.annList_ofGroup,
      Option.map_some, Option.getD_some, add_zero,
      Multiset.filter_cons, Multiset.filter_zero, Multiset.cons_ne_zero,
      ne_eq, not_false_eq_true, Multiset.forall_mem_cons,
      Multiset.notMem_zero, IsEmpty.forall_iff, implies_true, and_true,
      true_and, not_true, if_false,
      GenPred.entailsExistence, if_true,
      GenAnn.finalize_of_pending_zero, one_mul, Term.toGenKey_eval,
      Bool.false_eq_true]
    exact AggValue.predProv_ofGroup (fs l) (ts l)
      (Having.havingGroup is (q.evaluateAnnotated hq d) kv.fst) op
      (s.eval kv.fst)
