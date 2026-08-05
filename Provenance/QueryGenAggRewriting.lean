/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryGenHavingRewriting

/-!
# Rewriting a bare grouping: aggregate results as output values

The `HAVING` site rewriting of `Provenance.QueryGenHavingRewriting` covers
the case where the aggregate tokens of a grouping are consumed by a
comparison gate and never leave the site. This module covers the
complementary – and, in SQL, far more common – case: a bare
`GROUP BY` whose aggregate columns flow onward as ordinary output
columns.

Rule (R5) is the classical counterpart. Carrying it over the classical
syntax took a whole new value domain – data, annotation and `K`-tensor
monomials, quotiented – together with its own evaluator. In the general
framework no new value domain is needed: the rewritten
world's evaluator already has aggregate tokens as first-class column
values, and `QueryGen.GammaTok` – ProvSQL's `provsql_agg` – already
materializes exactly the token that the general evaluator's `Gamma`
produces. What was missing is the *correspondence at token level*: the
statement of `QueryGen.havingRewrites_valid` folds an annotated relation
into composite rows through `AnnotatedRelation.toComposite`, which reads
tokens through their deterministic collapse and therefore cannot express
a token-bearing output.

`GenRow.toCompositeRow` supplies that embedding: data columns go through
`Sum.inl`, token columns are transported by `AggValue.toComposite` (values
embedded in the composite domain, occurrence annotations unchanged), and
the row's finalized annotation is appended as the provenance column. On
token-free rows it agrees with the old embedding
(`GenRow.toCompositeRow_of_reg`), so the statement below genuinely
extends the compositional rewriting correctness rather than sitting
beside it.

`QueryGen.gammaRew_valid` is then the (R5) analogue: for a classical
subquery, the general evaluator's grouping – tokens and pending
group-existence factor included – is computed by the rewritten
token-building grouping over the classically rewritten subquery, with the
group guard `δ(⊕ U)` landing in the provenance column.
-/

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K]
  [DecidableEq K] [HasAltLinearOrder K]

/-! ## Tokens in the composite domain -/

/-- Transport a symbolic aggregate token to the composite value domain:
the aggregated values are embedded by `Sum.inl`, the aggregate function is
lifted, and the occurrence annotations are unchanged. -/
def AggValue.toComposite (a : AggValue T K) : AggValue (T ⊕ K) K :=
  ⟨a.agg.liftComposite, a.occs.map (fun o => (Sum.inl o.fst, o.snd))⟩

omit [DecidableEq K] in
/-- The token of a group transports to the token of the composite
embedding of that group – the token the rewritten world's
`QueryGen.GammaTok` builds. -/
theorem AggValue.ofGroup_toComposite {m : ℕ} (f : SeqAggFunc T)
    (t : Term T m) (U : List (AnnotatedTuple T K m)) :
    (AggValue.ofGroup f t U).toComposite
      = AggValue.ofGroup f.liftComposite t.castToAnnotatedTuple
          (U.map (fun p => ((p.toComposite, p.snd)
            : AnnotatedTuple (T ⊕ K) K (m + 1)))) := by
  unfold AggValue.toComposite AggValue.ofGroup
  refine congrArg (AggValue.mk _) ?_
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  exact congrArg (fun v => (v, p.snd))
    (Term.castToAnnotatedTuple_eval t p.fst p.snd).symm

/-- Transport a lifted column value to the composite domain. -/
def GenValue.toComposite : GenValue T K → GenValue (T ⊕ K) K
  | Sum.inl v => Sum.inl (Sum.inl v)
  | Sum.inr a => Sum.inr a.toComposite

/-- **The token-aware composite embedding of a general row**: every
column transported to the composite domain, with the row's finalized
annotation appended as the provenance column. -/
def GenRow.toCompositeRow {n : ℕ} (r : GenRow T K n) :
    Tuple (GenValue (T ⊕ K) K) (n + 1) :=
  Fin.append (fun k => GenValue.toComposite (r.fst k))
    (fun _ : Fin 1 => Sum.inl (Sum.inr r.snd.finalize))

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- On token-free rows the token-aware embedding is the embedding used by
the classical and `HAVING`-site rewriting correctness statements: the
`inl`-image of the composite encoding of the finalized annotated tuple. -/
theorem GenRow.toCompositeRow_of_reg {n : ℕ} (r : GenRow T K n)
    (hr : ∀ k, GenValue.kindOf (r.fst k) = ColKind.reg) :
    r.toCompositeRow
      = fun k => Sum.inl ((GenRow.toAnnotated r).toComposite k) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have hi := hr i
    show Fin.append _ _ (Fin.castAdd 1 i)
      = Sum.inl (AnnotatedTuple.toComposite _ (Fin.castAdd 1 i))
    rw [Fin.append_left, AnnotatedTuple.toComposite, Fin.append_left]
    show GenValue.toComposite (r.fst i)
      = Sum.inl (Sum.inl (AggValue.collapseSum (r.fst i)))
    cases hv : r.fst i with
    | inl v => rfl
    | inr a => rw [hv] at hi; exact absurd hi (by simp [GenValue.kindOf])
  · show Fin.append _ _ (Fin.natAdd n i)
      = Sum.inl (AnnotatedTuple.toComposite _ (Fin.natAdd n i))
    rw [Fin.append_right, AnnotatedTuple.toComposite, Fin.append_right]
    simp only [Matrix.cons_val_fin_one]
    rfl

/-! ## Coordinates of the token-aware embedding -/

omit [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem GenRow.toCompositeRow_castAdd {n : ℕ} (r : GenRow T K n)
    (k : Fin n) :
    r.toCompositeRow (Fin.castAdd 1 k) = GenValue.toComposite (r.fst k) :=
  Fin.append_left _ _ k

omit [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem GenRow.toCompositeRow_last {n : ℕ} (r : GenRow T K n) :
    r.toCompositeRow (Fin.last n) = Sum.inl (Sum.inr r.snd.finalize) := by
  show Fin.append _ _ (Fin.last n) = _
  rw [show (Fin.last n) = Fin.natAdd n (0 : Fin 1) from Fin.ext (by simp),
    Fin.append_right]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The deterministic reading commutes with the token transport. -/
@[simp] theorem AggValue.collapseSum_toComposite (x : GenValue T K) :
    AggValue.collapseSum (GenValue.toComposite x)
      = Sum.inl (AggValue.collapseSum x) := by
  cases x with
  | inl v => rfl
  | inr a =>
    show (AggValue.toComposite a).collapse = Sum.inl a.collapse
    unfold AggValue.toComposite AggValue.collapse
    rw [List.map_map,
      show ((Prod.fst : (T ⊕ K) × K → T ⊕ K)
          ∘ fun o : T × K => ((Sum.inl o.fst, o.snd) : (T ⊕ K) × K))
        = ((Sum.inl : T → T ⊕ K) ∘ Prod.fst) from rfl,
      ← List.map_map]
    exact SeqAggFunc.liftComposite_map_inl a.agg (a.occs.map Prod.fst)

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- Coordinates of the token-aware embedding, in `dite` form. -/
theorem GenRow.toCompositeRow_coord {n : ℕ} (r : GenRow T K n)
    (j : Fin (n + 1)) :
    r.toCompositeRow j
      = if h : (j : ℕ) < n then GenValue.toComposite (r.fst ⟨j, h⟩)
        else Sum.inl (Sum.inr r.snd.finalize) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [GenRow.toCompositeRow_castAdd,
      dif_pos (show ((Fin.castAdd 1 i : Fin (n + 1)) : ℕ) < n from i.isLt)]
    exact congrArg (fun k => GenValue.toComposite (r.fst k)) (Fin.ext rfl)
  · rw [show Fin.natAdd n i = Fin.last n from Fin.ext (by
      simp [Subsingleton.elim i (0 : Fin 1)]), GenRow.toCompositeRow_last,
      dif_neg (by simp only [Fin.val_last]; omega)]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- A key column of the embedding of a grouping row. -/
theorem GenRow.toCompositeRow_gammaRow_left {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggValue T K) (a : GenAnn K) (i : Fin n₁) :
    GenRow.toCompositeRow
        ((Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun i' => Sum.inr (h i')), a) : GenRow T K (n₁ + n₂))
        (Fin.castAdd 1 (Fin.castAdd n₂ i))
      = Sum.inl (Sum.inl (g i)) := by
  rw [GenRow.toCompositeRow_castAdd]
  dsimp only
  rw [Fin.append_left]
  rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- A token column of the embedding of a grouping row. -/
theorem GenRow.toCompositeRow_gammaRow_right {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggValue T K) (a : GenAnn K) (i : Fin n₂) :
    GenRow.toCompositeRow
        ((Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun i' => Sum.inr (h i')), a) : GenRow T K (n₁ + n₂))
        (Fin.castAdd 1 (Fin.natAdd n₁ i))
      = Sum.inr (h i).toComposite := by
  rw [GenRow.toCompositeRow_castAdd]
  dsimp only
  rw [Fin.append_right]
  rfl

/-! ## The rewritten bare grouping -/

/-- The kind vector of a rewritten `Gamma` output: the group keys, the
aggregate tokens, and the provenance column carrying the group guard. -/
abbrev ColKind.gammaRewKinds (n₁ n₂ : ℕ) : Fin (n₁ + n₂ + 1) → ColKind :=
  Fin.append (ColKind.gammaKinds n₁ n₂) (fun _ : Fin 1 => ColKind.prov)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- The kind vector produced by the token-building grouping over a
rewritten subquery is the rewritten `Gamma` kind vector: the key columns
of a rewritten schema are regular. -/
theorem ColKind.gammaTok_rew_kinds {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) :
    Fin.append
        (Fin.append
          (fun k => ColKind.rewKinds m ((is k).castLE (Nat.le_succ m)))
          (fun _ : Fin n₂ => ColKind.agg))
        (fun _ : Fin 1 => ColKind.prov)
      = ColKind.gammaRewKinds n₁ n₂ := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    show _ = Fin.append (ColKind.gammaKinds n₁ n₂) _ (Fin.castAdd 1 i)
    rw [Fin.append_left]
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
    · rw [Fin.append_left]
      show _ = ColKind.gammaKinds n₁ n₂ (Fin.castAdd n₂ i')
      rw [ColKind.gammaKinds, Fin.append_left]
      exact ColKind.rewKinds_lt (is i').isLt
    · rw [Fin.append_right]
      show _ = ColKind.gammaKinds n₁ n₂ (Fin.natAdd n₁ j')
      rw [ColKind.gammaKinds, Fin.append_right]
  · rw [Fin.append_right]
    show _ = Fin.append (ColKind.gammaKinds n₁ n₂) _ (Fin.natAdd (n₁ + n₂) i)
    rw [Fin.append_right]

/-- **The rewritten bare grouping**: ProvSQL's `provsql_agg` grouping over
the classically rewritten subquery, reading the occurrence annotations
off the subquery's provenance column. The output carries the group keys,
one aggregate token per `(term, aggregate)` pair, and the group-existence
guard `δ(⊕ U)` in the provenance column. -/
def QueryGen.gammaRew {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (qg : QueryGen T m (ColKind.allReg m)) (hq : qg.classical) :
    QueryGen (T ⊕ K) (n₁ + n₂ + 1) (ColKind.gammaRewKinds n₁ n₂) :=
  QueryGen.Retag
    (fun k => congrArg ColKind.base
      (congrFun (ColKind.gammaTok_rew_kinds (n₂ := n₂) is) k))
    (QueryGen.GammaTok
      (fun k => (is k).castLE (Nat.le_succ m))
      (fun k => by
        rw [ColKind.rewKinds_lt (is k).isLt]
        exact fun hc => ColKind.noConfusion hc)
      (fun j => (ts j).castToAnnotatedTuple)
      (fun j => (fs j).liftComposite)
      (TermG.provIndex (Fin.last m)
        (ColKind.rewKinds_of_not_lt (lt_irrefl m)))
      (qg.rewritingGen hq))

/-! ## Correctness -/

/-- **Correctness of the bare-grouping rewriting** – the general
framework's rule (R5): for a classical subquery, the general evaluator's
grouping, embedded row-wise into the composite domain (tokens included,
finalized annotation appended), is computed by the rewritten world's
token-building grouping over the classically rewritten subquery. -/
theorem QueryGen.gammaRew_valid {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (qg : QueryGen T m (ColKind.allReg m))
    (hq : qg.classical) (d : AnnotatedDatabase T K) :
    ((QueryGen.Gamma is ts fs qg).evaluateGen d).map GenRow.toCompositeRow
      = (QueryGen.gammaRew is ts fs qg hq).evaluateRew d.toComposite := by
  have hA : Multiset.map GenRow.toAnnotated (qg.evaluateGen d)
      = (qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq) d :=
    QueryGen.strip_bridge qg hq d
  simp only [QueryGen.evaluateGen]
  rw [hA]
  conv_lhs => rw [Multiset.map_map]
  unfold QueryGen.gammaRew
  show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) d.toComposite
  simp only [QueryGen.evaluateRew]
  rw [QueryGen.rewritingGen_provRel qg hq d, map_comp_fst_groupByKey]
  -- the rewritten side's key multiset is the `inl`-embedding of the
  -- annotated side's, so both sides map over the same groups
  simp only [Multiset.map_map]
  rw [show ((Prod.fst : AnnotatedTuple (T ⊕ K) K n₁ → Tuple (T ⊕ K) n₁)
      ∘ ((fun x : AnnotatedTuple (T ⊕ K) K (m + 1) =>
          ((fun k => x.fst ((is k).castLE (Nat.le_succ m)), x.snd)
            : AnnotatedTuple (T ⊕ K) K n₁))
        ∘ (fun p : AnnotatedTuple T K m =>
            ((p.toComposite, p.snd)
              : AnnotatedTuple (T ⊕ K) K (m + 1)))))
    = ((fun g : Tuple T n₁ =>
          ((fun k => Sum.inl (g k)) : Tuple (T ⊕ K) n₁))
        ∘ (fun p : AnnotatedTuple T K m =>
            ((fun k => p.fst (is k)) : Tuple T n₁))) from by
    funext p
    funext k
    show p.toComposite ((is k).castLE (Nat.le_succ m))
      = Sum.inl (p.fst (is k))
    rw [AnnotatedTuple.toComposite_coord,
      dif_pos (show (((is k).castLE (Nat.le_succ m)
        : Fin (m + 1)) : ℕ) < m from (is k).isLt)]
    exact congrArg (fun i => Sum.inl (p.fst i)) (Fin.ext rfl)]
  rw [← Multiset.map_map
      (g := fun g : Tuple T n₁ =>
        ((fun k => Sum.inl (g k)) : Tuple (T ⊕ K) n₁))
      (f := fun p : AnnotatedTuple T K m =>
        ((fun k => p.fst (is k)) : Tuple T n₁)),
    Multiset.dedup_map_of_injective
      (f := fun g : Tuple T n₁ =>
        ((fun k => Sum.inl (g k)) : Tuple (T ⊕ K) n₁))
      (fun g₁ g₂ h => funext (fun k => Sum.inl.inj (congrFun h k))),
    Multiset.map_map]
  -- and back from the deduplicated keys to the grouping
  rw [show (Multiset.map (fun p : AnnotatedTuple T K m =>
        ((fun k => p.fst (is k)) : Tuple T n₁))
        ((qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq) d)).dedup
      = (Multiset.map Prod.fst (Multiset.map
          (fun p : AnnotatedTuple T K m =>
            ((fun k => p.fst (is k), p.snd) : AnnotatedTuple T K n₁))
          ((qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq)
            d))).dedup from by
    rw [Multiset.map_map]
    rfl,
    ← map_fst_groupByKey, Multiset.map_map]
  refine Multiset.map_congr rfl (fun kv _ => ?_)
  simp only [Function.comp_apply]
  rw [Having.havingGroup_toComposite is
    ((qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq) d) kv.fst]
  unfold GenRow.toCompositeRow
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, Fin.append_left]
    dsimp only
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
    · rw [Fin.append_left, Fin.append_left]
      rfl
    · rw [Fin.append_right, Fin.append_right]
      exact congrArg Sum.inr (AggValue.ofGroup_toComposite _ _ _)
  · rw [Fin.append_right, Fin.append_right]
    dsimp only
    rw [GenAnn.finalize_gamma, List.map_map]
    rfl

/-! ## The gate reads a transported token unchanged -/

/-- **The predicate provenance under the token transport**: comparing a
transported token against an embedded value is the original comparison.
The token transport preserves lengths and annotations, lifts the
aggregate faithfully on embedded values, and comparisons restrict along
`inl`. -/
theorem AggValue.predProv_toComposite (a : AggValue T K) (op : CompOp)
    (c : T) :
    a.toComposite.predProv op (Sum.inl c) = a.predProv op c := by
  have hlen : a.occs.length = a.toComposite.occs.length := by
    simp [AggValue.toComposite]
  unfold AggValue.predProv
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (finCongr hlen).finsetCongr
    (fun W => if W.Nonempty
      then Having.worldAnn a.anns W * Having.chi op (a.valOn W) c else 0)
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply]
  by_cases hne : W.Nonempty
  · rw [if_pos hne, if_pos (by rwa [Finset.map_nonempty])]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [AggValue.worldAnn_map_finCongr hlen]
      refine congrArg (fun α : Fin a.occs.length → K =>
        Having.worldAnn α W) (funext (fun i => ?_))
      simp [AggValue.anns, AggValue.toComposite, List.getElem_map]
    · rw [show a.toComposite.valOn (W.map (finCongr hlen).toEmbedding)
          = Sum.inl (a.valOn W) from ?_]
      · exact (Having.chi_inl op _ c).symm
      · show a.agg.liftComposite
            ((Having.seqOf (a.occs.map (fun o : T × K =>
              ((Sum.inl o.fst, o.snd) : (T ⊕ K) × K)))
              (W.map (finCongr hlen).toEmbedding)).map Prod.fst)
          = Sum.inl (a.agg ((Having.seqOf a.occs W).map Prod.fst))
        rw [AggValue.seqOf_map _ a.occs hlen W, List.map_map,
          show ((Prod.fst : (T ⊕ K) × K → T ⊕ K)
              ∘ fun o : T × K => ((Sum.inl o.fst, o.snd) : (T ⊕ K) × K))
            = ((Sum.inl : T → T ⊕ K) ∘ Prod.fst) from rfl,
          ← List.map_map]
        exact SeqAggFunc.liftComposite_map_inl a.agg _
  · rw [if_neg hne, if_neg (by rwa [Finset.map_nonempty])]
