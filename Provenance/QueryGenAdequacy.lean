/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryGen
import Provenance.QueryAdequacy

/-!
# Data-part adequacy of the general evaluator

Forgetting the annotations of the general annotated evaluation of a query
yields the plain (classical) evaluation of the *stripped* query on the
plain database:

`(q.evaluateAnnotatedGen d).toPlain = q.stripGen.evaluatePlain d.toPlain`

This generalizes `Query.evaluateAnnotated_toPlain` to the kind-indexed
syntax. The stripping removes differences (annotated `Diff` never removes
tuple slots) and aggregate-atom selections (the annotated evaluator keeps
classically-failing rows annotated `𝟘`, as ProvSQL emits them); on the
remaining operators the data parts agree tuple for tuple, the aggregate
tokens contributing through their deterministic `collapse` reading:

* terms, projection columns and predicates evaluated on a lifted tuple
  agree with their plain readings on the collapsed tuple
  (`TermG.eval_eq_evalPlain`, `ProjCol.collapseSum_eval`,
  `GenPred.holds_iff_holdsPlain`);
* the group sequence of the fused semantics projects onto the plain group
  sequence (`havingGroup_map_fst`): both are sorted lists of the same
  multiset of tuples, sorted by the same order on the tuple part – the
  annotation tie-break of `havingGroup` is invisible after projection;
* one output row of `Gamma` per group key, whose aggregate columns
  collapse to the plain aggregates of the whole group.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## Plain readings through `collapse` -/

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A term over regular columns evaluates on a lifted tuple as its plain
reading on the collapsed tuple. -/
theorem TermG.eval_eq_evalPlain {n : ℕ} {κ : Fin n → ColKind}
    (t : TermG T κ) (u : Tuple (GenValue T K) n) :
    (t.eval u : T) = t.evalPlain (GenRow.plainTuple u) := by
  induction t with
  | const a => rfl
  | index k h => rfl
  | provIndex k h => rfl
  | cmpAgg k h op c ih => rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermG.eval, TermG.evalPlain, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => rw [TermG.eval, TermG.evalPlain, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => rw [TermG.eval, TermG.evalPlain, ih₁, ih₂]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A projection column collapses on a lifted tuple to its plain reading
on the collapsed tuple. -/
theorem ProjCol.collapseSum_eval {n : ℕ} {κ : Fin n → ColKind}
    (p : ProjCol T κ) (u : Tuple (GenValue T K) n) :
    AggValue.collapseSum (p.eval u) = p.evalPlain (GenRow.plainTuple u) := by
  cases p with
  | term t =>
    show AggValue.collapseSum (Sum.inl (t.eval u)) = _
    rw [ProjCol.evalPlain, ← TermG.eval_eq_evalPlain]
    rfl
  | token k h => rfl
  | provTerm t =>
    show AggValue.collapseSum (Sum.inl (t.eval u)) = _
    rw [ProjCol.evalPlain, ← TermG.eval_eq_evalPlain]
    rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A predicate holds on a lifted tuple iff its plain reading holds on
the collapsed tuple. -/
theorem GenPred.holds_iff_holdsPlain {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (u : Tuple (GenValue T K) n) :
    φ.holds u ↔ φ.holdsPlain (GenRow.plainTuple u) := by
  induction φ with
  | cmp op t₁ t₂ =>
    rw [GenPred.holds, GenPred.holdsPlain,
      TermG.eval_eq_evalPlain, TermG.eval_eq_evalPlain]
  | aggCmp k h op t =>
    rw [GenPred.holds, GenPred.holdsPlain, TermG.eval_eq_evalPlain]
    rfl
  | and φ ψ ihφ ihψ => rw [GenPred.holds, GenPred.holdsPlain, ihφ, ihψ]
  | or φ ψ ihφ ihψ => rw [GenPred.holds, GenPred.holdsPlain, ihφ, ihψ]
  | not φ ih => rw [GenPred.holds, GenPred.holdsPlain, ih]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The collapsed tuple of an embedded annotated tuple is its data part. -/
@[simp] theorem GenRow.plainTuple_ofAnnotated {n : ℕ}
    (p : AnnotatedTuple T K n) :
    GenRow.plainTuple (GenRow.ofAnnotated p).fst = p.fst := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Collapsing distributes over appending a regular and a token part. -/
theorem GenRow.plainTuple_append {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggValue T K) :
    GenRow.plainTuple
        (Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun j => Sum.inr (h j)))
      = Fin.append g (fun j => (h j).collapse) := by
  funext k
  unfold GenRow.plainTuple
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left, Fin.append_left]; rfl
  · rw [Fin.append_right, Fin.append_right]; rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The collapse of a group token is the plain aggregate of the group's
value sequence. -/
theorem AggValue.collapse_ofGroup {m : ℕ} (f : SeqAggFunc T) (t : Term T m)
    (U : List (AnnotatedTuple T K m)) :
    (AggValue.ofGroup f t U).collapse = f (U.map (fun p => t.eval p.fst)) := by
  unfold AggValue.collapse AggValue.ofGroup
  rw [List.map_map]
  rfl

/-! ## Multiset helpers -/

private lemma map_filter_iff {α β : Type} (f : α → β) (p : α → Prop)
    (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q (f a)) (s : Multiset α) :
    (s.filter p).map f = (s.map f).filter q := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    by_cases hpa : p a
    · rw [Multiset.filter_cons_of_pos _ hpa, Multiset.map_cons,
        Multiset.map_cons, Multiset.filter_cons_of_pos _ ((h a).mp hpa), ih]
    · rw [Multiset.filter_cons_of_neg _ hpa, Multiset.map_cons,
        Multiset.filter_cons_of_neg _ (fun hq => hpa ((h a).mpr hq)), ih]

lemma product_map_map {α₁ α₂ β₁ β₂ : Type} (f : α₁ → β₁)
    (g : α₂ → β₂) (s : Multiset α₁) (t : Multiset α₂) :
    Multiset.product (s.map f) (t.map g)
      = (Multiset.product s t).map (fun x => (f x.fst, g x.snd)) := by
  show (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map _
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.cons_product, Multiset.cons_product,
      Multiset.map_add, ih, Multiset.map_map, Multiset.map_map]
    rfl

omit [HasAltLinearOrder K] in
/-- The keys of `groupByKey` are the deduplicated data parts (factored out
of the `Dedup` case of `Query.evaluateAnnotated_toPlain`). -/
lemma map_fst_groupByKey {n : ℕ} (r : AnnotatedRelation T K n) :
    Multiset.map Prod.fst (Multiset.ofList (groupByKey r).val)
      = (Multiset.map Prod.fst r).dedup := by
  have hL : (Multiset.map Prod.fst
      (Multiset.ofList (groupByKey r).val)).Nodup := by
    apply Multiset.Nodup.map_on
    · intro p hp q hq hpq
      exact Prod.ext hpq
        (KeyValueList.functional _ (groupByKey r).property p
          (Multiset.mem_coe.mp hp) q (Multiset.mem_coe.mp hq) hpq)
    · rw [Multiset.coe_nodup]
      exact KeyValueList.nodup _ (groupByKey r).property
  rw [Multiset.Nodup.ext hL (Multiset.nodup_dedup _)]
  intro t
  constructor
  · intro ht
    rw [Multiset.mem_map] at ht
    obtain ⟨p, hp, hfst⟩ := ht
    rw [Multiset.mem_dedup, ← hfst]
    exact (groupByKey_key_iff r p.fst).mp ⟨p.snd, Multiset.mem_coe.mp hp⟩
  · intro ht
    obtain ⟨w, hw⟩ := (groupByKey_key_iff r t).mpr (Multiset.mem_dedup.mp ht)
    rw [Multiset.mem_map]
    exact ⟨(t, w), Multiset.mem_coe.mpr hw, rfl⟩

/-! ## The group-sequence bridge -/

omit [DecidableEq K] in
/-- The data parts of the fused group sequence form the plain group
sequence: both are lists of the same multiset of tuples, sorted by the
canonical order on tuples – `havingGroup`'s annotation tie-break is
invisible after projection. -/
theorem havingGroup_map_fst {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    (Having.havingGroup is r g).map Prod.fst
      = Relation.groupSeq is (AnnotatedRelation.toPlain r) g := by
  unfold Relation.groupSeq
  letI : LinearOrder K := HasAltLinearOrder.altOrder
  letI : LinearOrder (AnnotatedTuple T K m) :=
    inferInstanceAs (LinearOrder (Tuple T m ×ₗ K))
  have hperm : List.Perm ((Having.havingGroup is r g).map Prod.fst)
      (Multiset.sort
        (Multiset.filter (fun u : Tuple T m => ∀ k' : Fin n₁, u (is k') = g k')
          (AnnotatedRelation.toPlain r)) (· ≤ ·)) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Having.havingGroup_coe,
      Multiset.sort_eq]
    exact map_filter_iff Prod.fst
      (fun p : AnnotatedTuple T K m => ∀ k' : Fin n₁, p.fst (is k') = g k')
      (fun u : Tuple T m => ∀ k' : Fin n₁, u (is k') = g k')
      (fun p => Iff.rfl) r
  refine hperm.eq_of_pairwise' (r := (· ≤ ·)) ?_ (Multiset.pairwise_sort _ _)
  -- sortedness of the projected fused sequence
  refine List.Pairwise.map Prod.fst ?_ (Having.havingGroup_pairwise is r g)
  intro p q hpq
  rcases hpq with h | h
  · exact le_of_lt h
  · exact le_of_eq h

/-! ## The adequacy theorem -/

/-- **Data-part adequacy of the general evaluator.** Forgetting the
annotations of the general annotated evaluation yields the plain
evaluation of the stripped query on the plain database. -/
theorem QueryGen.evaluateAnnotatedGen_toPlain :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (d : AnnotatedDatabase T K),
    (q.evaluateAnnotatedGen d).toPlain = q.stripGen.evaluatePlain d.toPlain := by
  have hplain : ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (d : AnnotatedDatabase T K),
      (q.evaluateAnnotatedGen d).toPlain
        = (q.evaluateGen d).map (fun r => GenRow.plainTuple r.fst) := by
    intro n κ q d
    unfold QueryGen.evaluateAnnotatedGen AnnotatedRelation.toPlain
    rw [Multiset.map_map]
    rfl
  intro n κ q
  induction q with
  | Rel n s =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [AnnotatedDatabase.find_toPlain]
    cases hf : d.find n s
    · rfl
    · rw [Option.map_some, Multiset.map_map]
      rfl
  | Proj ps q ih =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [← ih d, hplain, Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r _
    funext j
    exact ProjCol.collapseSum_eval (ps j) r.fst
  | Sel φ q ih =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen]
    by_cases hφ : φ.hasAggAtom
    · rw [if_pos hφ, if_pos hφ, ← ih d, hplain, Multiset.map_map]
      rfl
    · rw [if_neg hφ, if_neg hφ]
      simp only [QueryGen.evaluatePlain]
      rw [← ih d, hplain]
      exact map_filter_iff _ _ _
        (fun (r : GenRow T K _) => φ.holds_iff_holdsPlain r.fst) _
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [← ih₁ d, ← ih₂ d, hplain, hplain]
    show Multiset.map _ (Multiset.map _ (Multiset.product _ _))
      = Multiset.map _ (Multiset.product
          (Multiset.map (fun r => GenRow.plainTuple r.fst) (q₁.evaluateGen d))
          (Multiset.map (fun r => GenRow.plainTuple r.fst) (q₂.evaluateGen d)))
    rw [Multiset.map_map, product_map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro xy _
    show GenRow.plainTuple (Fin.append xy.fst.fst xy.snd.fst)
      = Fin.append (GenRow.plainTuple xy.fst.fst) (GenRow.plainTuple xy.snd.fst)
    funext k
    unfold GenRow.plainTuple
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [Multiset.map_add, ← ih₁ d, ← ih₂ d, hplain, hplain]
  | Dedup q ih =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [Multiset.map_map, ← ih d, hplain]
    refine Eq.trans
      (Multiset.map_congr rfl
        (fun p _ => GenRow.plainTuple_ofAnnotated (K := K) p)) ?_
    rw [map_fst_groupByKey, Multiset.map_map]
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen]
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map, ← ih₁ d, hplain]
    apply Multiset.map_congr rfl
    intro r _
    rfl
  | @Gamma m n₁ n₂ is ts fs q ih =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [← ih d, hplain]
    -- collapse the nested maps deterministically, outermost first
    conv_lhs => rw [Multiset.map_map]
    conv_lhs => rw [Multiset.map_map]
    conv_rhs => rw [Multiset.map_map]
    -- the plain view of the annotated intermediate relation
    have hview : AnnotatedRelation.toPlain
        ((q.evaluateGen d).map GenRow.toAnnotated)
        = (q.evaluateGen d).map (fun r => GenRow.plainTuple r.fst) := by
      unfold AnnotatedRelation.toPlain
      rw [Multiset.map_map]
      rfl
    -- the key multisets coincide
    have hkeys : ((q.evaluateGen d).map
          ((fun u => (fun k => u (is k) : Tuple T n₁))
            ∘ (fun r : GenRow T K m => GenRow.plainTuple r.fst))).dedup
        = Multiset.map Prod.fst (Multiset.ofList (groupByKey
            ((q.evaluateGen d).map
              ((fun p => ((fun k => p.fst (is k), p.snd)
                  : AnnotatedTuple T K n₁))
                ∘ GenRow.toAnnotated))).val) := by
      rw [map_fst_groupByKey, Multiset.map_map]
      rfl
    rw [hkeys]
    conv_rhs => rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro kv _
    simp only [Function.comp_apply]
    show GenRow.plainTuple (Fin.append _ _) = _
    rw [GenRow.plainTuple_append]
    congr 1
    funext j
    rw [AggValue.collapse_ofGroup]
    have hg := congrArg (List.map (ts j).eval)
      (havingGroup_map_fst is ((q.evaluateGen d).map GenRow.toAnnotated)
        kv.fst)
    rw [List.map_map, hview] at hg
    exact congrArg (fs j) hg
  | @ProvSum m n₁ κ' is his t q ih =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [← ih d, hplain]
    conv_lhs => rw [Multiset.map_map]
    conv_lhs => rw [Multiset.map_map]
    conv_rhs => rw [Multiset.map_map]
    refine Multiset.map_congr
      (congrArg Multiset.dedup (Multiset.map_congr rfl (fun r₀ _ => rfl)))
      (fun g hg => ?_)
    simp only [Function.comp_apply]
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · show AggValue.collapseSum _ = _
      rw [Fin.append_left, Fin.append_left]
      rfl
    · show AggValue.collapseSum _ = _
      rw [Fin.append_right, Fin.append_right]
      show Multiset.fold addFn 0 _ = Multiset.fold addFn 0 _
      refine congrArg (Multiset.fold addFn 0) ?_
      rw [Multiset.filter_map, Multiset.filter_map, Multiset.map_map,
        Multiset.map_map]
      exact Multiset.map_congr (Multiset.filter_congr fun _ _ => Iff.rfl)
        (fun _ _ => rfl)
  | @GammaTok m n₁ n₂ κ' is his ts fs a q ih =>
    intro d
    rw [hplain]
    simp only [QueryGen.evaluateGen, QueryGen.stripGen, QueryGen.evaluatePlain]
    rw [← ih d, hplain]
    conv_lhs => rw [Multiset.map_map]
    conv_lhs => rw [Multiset.map_map]
    conv_rhs => rw [Multiset.map_map]
    have hview : AnnotatedRelation.toPlain
        ((q.evaluateGen d).map GenRow.toAnnotated)
        = (q.evaluateGen d).map (fun r => GenRow.plainTuple r.fst) := by
      unfold AnnotatedRelation.toPlain
      rw [Multiset.map_map]
      rfl
    have hkeys : ((q.evaluateGen d).map
          ((fun u => (fun k => u (is k) : Tuple T n₁))
            ∘ (fun r : GenRow T K m => GenRow.plainTuple r.fst))).dedup
        = Multiset.map Prod.fst (Multiset.ofList (groupByKey
            ((q.evaluateGen d).map
              ((fun p => ((fun k => p.fst (is k), p.snd)
                  : AnnotatedTuple T K n₁))
                ∘ GenRow.toAnnotated))).val) := by
      rw [map_fst_groupByKey, Multiset.map_map]
      rfl
    rw [hkeys]
    conv_rhs => rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro kv _
    simp only [Function.comp_apply]
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
      · show AggValue.collapseSum _ = _
        rw [Fin.append_left, Fin.append_left, Fin.append_left,
          Fin.append_left]
        rfl
      · show AggValue.collapseSum _ = _
        rw [Fin.append_left, Fin.append_left, Fin.append_right,
          Fin.append_right]
        simp only [AggValue.collapseSum, Sum.elim_inr]
        rw [AggValue.collapse_ofGroup]
        have hg := congrArg (List.map (ts j').eval)
          (havingGroup_map_fst is
            ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst)
        rw [List.map_map, hview] at hg
        exact congrArg (fs j') hg
    · show AggValue.collapseSum _ = _
      rw [Fin.append_right, Fin.append_right]
      simp only [AggValue.collapseSum]
      show Multiset.fold addFn 0 _ = Multiset.fold addFn 0 _
      refine congrArg (Multiset.fold addFn 0) ?_
      rw [Multiset.filter_map, Multiset.filter_map, Multiset.map_map,
        Multiset.map_map]
      exact Multiset.map_congr (Multiset.filter_congr fun _ _ => Iff.rfl)
        (fun _ _ => rfl)
  | Retag h q ih =>
    intro d
    rw [hplain]
    show (q.evaluateGen d).map (fun r => GenRow.plainTuple r.fst)
      = (q.stripGen.evaluatePlain d.toPlain : Relation T _)
    rw [← hplain]
    exact ih d
