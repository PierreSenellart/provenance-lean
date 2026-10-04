/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryHavingRewriting

/-!
# Rewriting a bare grouping: aggregate results as output values

The `HAVING` site rewriting of `Provenance.AggQueryHavingRewriting` covers
the case where the aggregate tokens of a grouping are consumed by a
comparison gate and never leave the site. This module covers the
complementary – and, in SQL, far more common – case: a bare
`GROUP BY` whose aggregate columns flow onward as ordinary output
columns.

Rule (R5) is the classical counterpart. Carrying it over the classical
syntax took a whole new value domain – data, annotation and `K`-tensor
monomials, quotiented – together with its own evaluator. In the general
framework no new value domain is needed: the rewritten
world's evaluator already has aggregate tokens as ordinary column
values, and `AggQueryIn.GammaTok` – ProvSQL's `provsql_agg` – already
materializes exactly the token that the general evaluator's `Gamma`
produces. What was missing is the *correspondence at token level*: the
statement of `AggQueryIn.havingRewrites_valid` folds an annotated relation
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

`AggQueryIn.gammaRew_valid` is then the (R5) analogue: for a classical
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
  ⟨a.agg.liftComposite, a.occs.map (fun o => (Sum.inl o.fst, o.snd)), a.scalar⟩

omit [DecidableEq K] in
/-- The token of a group transports to the token of the composite
embedding of that group – the token the rewritten world's
`AggQueryIn.GammaTok` builds. -/
theorem AggValue.ofGroup_toComposite {m : ℕ} (f : SeqAggFunc T)
    (t : Term T m) (U : List (AnnotatedTuple T K m)) :
    (AggValue.ofGroup f t U).toComposite
      = AggValue.ofGroup f.liftComposite t.castToAnnotatedTuple
          (U.map (fun p => ((p.toComposite, p.snd)
            : AnnotatedTuple (T ⊕ K) K (m + 1)))) := by
  unfold AggValue.toComposite AggValue.ofGroup
  refine congrArg (fun l => (AggValue.mk _ l false : AggValue (T ⊕ K) K)) ?_
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  exact congrArg (fun v => (v, p.snd))
    (TermIn.castToAnnotatedTuple_eval t p.fst p.snd).symm

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The deterministic reading of a transported token** is the transport
of its reading: the lifted aggregate function agrees with the original on
embedded values. -/
theorem AggValue.collapse_toComposite (a : AggValue T K) :
    a.toComposite.collapse = Sum.inl a.collapse := by
  unfold AggValue.toComposite AggValue.collapse
  rw [List.map_map,
    show ((Prod.fst : (T ⊕ K) × K → T ⊕ K)
        ∘ fun o : T × K => ((Sum.inl o.fst, o.snd) : (T ⊕ K) × K))
      = ((Sum.inl : T → T ⊕ K) ∘ Prod.fst) from rfl,
    ← List.map_map]
  exact SeqAggFunc.liftComposite_map_inl a.agg (a.occs.map Prod.fst)

/-- Lift the function of an aggregate expression to the composite domain,
as `SeqAggFunc.liftComposite` lifts an aggregate: junk on the annotation
arm, faithful on `inl`-embedded values. -/
def AggExprFun.liftComposite {p : ℕ} (g : (Fin p → T) → T) :
    (Fin p → T ⊕ K) → T ⊕ K :=
  fun v => Sum.inl (g (fun j => Sum.elim id (fun _ => 0) (v j)))

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The lifted function on `inl`-embedded arguments. -/
theorem AggExprFun.liftComposite_inl {p : ℕ} (g : (Fin p → T) → T)
    (v : Fin p → T) :
    AggExprFun.liftComposite (K := K) g (fun j => Sum.inl (v j))
      = Sum.inl (g v) := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Embedding the occurrence values leaves the family's length, hence the
index type of a world, where it was. -/
theorem AggExpr.length_inl_occs (a : AggExpr T K) :
    a.occs.length
      = (a.occs.map (fun o => (((fun j => Sum.inl (o.fst j))
          : Fin a.arity → T ⊕ K), o.snd))).length := by
  rw [List.length_map]

/-- **Transport an aggregate expression to the composite domain**: the
occurrence values are embedded by `Sum.inl`, the leaf aggregates and the
expression's own function are lifted, and the occurrence annotations and
the leaf readings are unchanged. -/
def AggExpr.toComposite (a : AggExpr T K) : AggExpr (T ⊕ K) K where
  arity := a.arity
  occs := a.occs.map
    (fun o => ((fun j => Sum.inl (o.fst j)), o.snd.fst, o.snd.snd))
  aggs := fun j => (a.aggs j).liftComposite
  scalar := a.scalar
  g := AggExprFun.liftComposite a.g

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Each leaf reads the embedding of the sequence it read. -/
theorem AggExpr.leafSeq_toComposite (a : AggExpr T K) (j : Fin a.arity)
    (W : Finset (Fin a.occs.length)) :
    a.toComposite.leafSeq j (W.map (finCongr a.length_inl_occs).toEmbedding)
      = (a.leafSeq j W).map Sum.inl := by
  rw [AggExpr.leafSeq_eq_filter, AggExpr.leafSeq_eq_filter,
    show Having.seqOf a.toComposite.occs
          (W.map (finCongr a.length_inl_occs).toEmbedding)
        = (Having.seqOf a.occs W).map
          (fun o => ((fun j => Sum.inl (o.fst j)), o.snd.fst, o.snd.snd)) from
      AggValue.seqOf_map _ a.occs a.length_inl_occs W,
    List.filter_map, List.map_map, List.map_map]
  rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Hence the value in a world is the embedding of the value there. -/
theorem AggExpr.valOn_toComposite (a : AggExpr T K)
    (W : Finset (Fin a.occs.length)) :
    a.toComposite.valOn (W.map (finCongr a.length_inl_occs).toEmbedding)
      = Sum.inl (a.valOn W) := by
  have hleaf : ∀ j, a.toComposite.leafVal j
      (W.map (finCongr a.length_inl_occs).toEmbedding)
      = Sum.inl (a.leafVal j W) := by
    intro j
    show (a.aggs j).liftComposite _ = _
    rw [a.leafSeq_toComposite j W]
    exact SeqAggFunc.liftComposite_map_inl (a.aggs j) (a.leafSeq j W)
  show AggExprFun.liftComposite a.g _ = _
  rw [funext hleaf]
  exact AggExprFun.liftComposite_inl a.g _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- And the deterministic reading with it. -/
@[simp] theorem AggExpr.collapse_toComposite (a : AggExpr T K) :
    a.toComposite.collapse = Sum.inl a.collapse := by
  unfold AggExpr.collapse
  rw [← a.valOn_toComposite Finset.univ]
  exact congrArg a.toComposite.valOn (Finset.map_univ_equiv _).symm

/-- Transport a token to the composite value domain. A nested token
transports its inner values the same way, and an expression its shared
occurrences, its leaf aggregates and its own function. -/
def AggTok.toComposite : AggTok T K → AggTok (T ⊕ K) K
  | .tok a => .tok a.toComposite
  | .nest a => .nest ⟨NestedValue.liftComposite a.agg,
      a.occs.map (fun o => (o.1.toComposite, o.2)), a.scalar⟩
  | .expr a => .expr a.toComposite

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
  | inr x =>
    cases x with
    | tok a => exact AggValue.collapse_toComposite a
    | expr a => exact AggExpr.collapse_toComposite a
    | nest a =>
      show (NestedValue.liftComposite a.agg) _ = Sum.inl (a.agg _)
      rw [Multiset.map_map,
        show ((fun o : AggExpr (T ⊕ K) K × K => o.1.collapse)
            ∘ fun o : AggExpr T K × K => (o.1.toComposite, o.2))
          = ((Sum.inl : T → T ⊕ K) ∘ fun o : AggExpr T K × K => o.1.collapse)
          from funext (fun o => AggExpr.collapse_toComposite o.1),
        ← Multiset.map_map]
      exact NestedValue.liftComposite_map_inl a.agg
        (a.occs.map (fun o => o.1.collapse))

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- Coordinates of the token-aware embedding, in `dite` form. -/
theorem GenRow.toCompositeRow_coord {n : ℕ} (r : GenRow T K n)
    (j : Fin (n + 1)) :
    r.toCompositeRow j
      = if h : (j : ℕ) < n then GenValue.toComposite (r.fst ⟨j, h⟩)
        else Sum.inl (Sum.inr r.snd.finalize) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [GenRow.toCompositeRow_castAdd,
      dite_eq_left (show ((Fin.castAdd 1 i : Fin (n + 1)) : ℕ) < n from i.isLt)]
    exact congrArg (fun k => GenValue.toComposite (r.fst k)) (Fin.ext rfl)
  · rw [show Fin.natAdd n i = Fin.last n from Fin.ext (by
      simp [Subsingleton.elim i (0 : Fin 1)]), GenRow.toCompositeRow_last,
      dite_eq_right (by simp only [Fin.val_last]; omega)]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- A key column of the embedding of a grouping row. -/
theorem GenRow.toCompositeRow_gammaRow_left {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggTok T K) (a : GenAnn K) (i : Fin n₁) :
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
    (h : Fin n₂ → AggTok T K) (a : GenAnn K) (i : Fin n₂) :
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
rewritten subquery is the rewritten `Gamma` kind vector, whatever
rewritten schema the subquery carries: all that is asked of it is that
the key columns be regular, which they are in a rewriting of an
all-regular query. -/
theorem ColKind.gammaTok_rew_kinds_of {m n₁ n₂ : ℕ}
    {κ' : Fin (m + 1) → ColKind} (is : Tuple (Fin m) n₁)
    (hkey : ∀ k, κ' ((is k).castLE (Nat.le_succ m)) = ColKind.reg) :
    Fin.append
        (Fin.append
          (fun k => κ' ((is k).castLE (Nat.le_succ m)))
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
      exact hkey i'
    · rw [Fin.append_right]
      show _ = ColKind.gammaKinds n₁ n₂ (Fin.natAdd n₁ j')
      rw [ColKind.gammaKinds, Fin.append_right]
  · rw [Fin.append_right]
    show _ = Fin.append (ColKind.gammaKinds n₁ n₂) _ (Fin.natAdd (n₁ + n₂) i)
    rw [Fin.append_right]

/-- The classical rewriting's own schema is one such. -/
theorem ColKind.gammaTok_rew_kinds {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) :
    Fin.append
        (Fin.append
          (fun k => ColKind.rewKinds m ((is k).castLE (Nat.le_succ m)))
          (fun _ : Fin n₂ => ColKind.agg))
        (fun _ : Fin 1 => ColKind.prov)
      = ColKind.gammaRewKinds n₁ n₂ :=
  ColKind.gammaTok_rew_kinds_of (n₂ := n₂) is
    (fun k => ColKind.rewKinds_lt (is k).isLt)

/-- **The rewritten grouping over an arbitrary rewritten subquery**: the
same `provsql_agg` grouping as `AggQueryIn.gammaRew`, reading the
occurrence annotations off the subquery's provenance column, but over
*any* query of the rewritten world that computes the subquery's rows –
not only the classical rewriting of a classical one. This is what makes
the rule compositional: a `GROUP BY` whose input is itself a grouping
(its aggregate column cashed by a projection, which is what the kind
discipline asks) is rewritten by composing the two. -/
def AggQueryIn.gammaRewOf {m n₁ n₂ : ℕ} {κ' : Fin (m + 1) → ColKind}
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂)
    (hkey : ∀ k, κ' ((is k).castLE (Nat.le_succ m)) = ColKind.reg)
    (hprov : κ' (Fin.last m) = ColKind.prov)
    (q' : AggQuery (T ⊕ K) (m + 1) κ') :
    AggQuery (T ⊕ K) (n₁ + n₂ + 1) (ColKind.gammaRewKinds n₁ n₂) :=
  AggQueryIn.Retag
    (fun k => congrArg ColKind.base
      (congrFun (ColKind.gammaTok_rew_kinds_of (n₂ := n₂) is hkey) k))
    (AggQueryIn.GammaTok
      (fun k => (is k).castLE (Nat.le_succ m))
      (fun k => by
        rw [hkey k]
        exact fun hc => ColKind.noConfusion hc)
      (fun j => (ts j).castToAnnotatedTuple)
      (fun j => (fs j).liftComposite)
      (TermGIn.provIndex (Fin.last m) hprov)
      q')

/-- **The rewritten bare grouping**: ProvSQL's `provsql_agg` grouping over
the classically rewritten subquery, reading the occurrence annotations
off the subquery's provenance column. The output carries the group keys,
one aggregate token per `(term, aggregate)` pair, and the group-existence
guard `δ(⊕ U)` in the provenance column.

It is `AggQueryIn.gammaRewOf` over the classical rewriting of the
subquery; the general form takes any query of the rewritten world that
computes the subquery's rows. -/
def AggQueryIn.gammaRew {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (qg : AggQuery T m (ColKind.allReg m)) (hq : qg.classical) :
    AggQuery (T ⊕ K) (n₁ + n₂ + 1) (ColKind.gammaRewKinds n₁ n₂) :=
  AggQueryIn.gammaRewOf is ts fs
    (fun k => ColKind.rewKinds_lt (is k).isLt)
    (ColKind.rewKinds_of_not_lt (lt_irrefl m))
    (qg.rewriting hq)

/-! ## Correctness -/

/-- **Correctness of the bare-grouping rewriting, compositionally** –
the general framework's rule (R5) over any rewritten subquery: what is
asked of the subquery is only that the rewritten world's query compute
its rows, as the pairs of a plain tuple and the annotation its
provenance column carries. The grouping itself is the same. -/
theorem AggQueryIn.gammaRewOf_valid {m n₁ n₂ : ℕ}
    {κ' : Fin (m + 1) → ColKind}
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (qg : AggQuery T m (ColKind.allReg m))
    (hkey : ∀ k, κ' ((is k).castLE (Nat.le_succ m)) = ColKind.reg)
    (hprov : κ' (Fin.last m) = ColKind.prov)
    (q' : AggQuery (T ⊕ K) (m + 1) κ') (d : AnnotatedDatabase T K)
    (R : AnnotatedRelation T K m)
    (hR : Multiset.map GenRow.toAnnotated (qg.evaluate d) = R)
    (har : Multiset.map (fun u => ((GenRow.plainTuple u,
          ((TermGIn.provIndex (c := 0) (Fin.last m) hprov).evalRew u).annPart)
            : AnnotatedTuple (T ⊕ K) K (m + 1)))
        (q'.evaluateRew d.toComposite)
      = R.map (fun p => ((p.toComposite, p.snd)
            : AnnotatedTuple (T ⊕ K) K (m + 1)))) :
    ((AggQueryIn.Gamma is ts fs qg).evaluate d).map GenRow.toCompositeRow
      = (AggQueryIn.gammaRewOf is ts fs hkey hprov q').evaluateRew
          d.toComposite := by
  simp only [AggQueryIn.evaluate]
  rw [hR]
  conv_lhs => rw [Multiset.map_map]
  unfold AggQueryIn.gammaRewOf
  show _ = AggQueryIn.evaluateRew (AggQueryIn.Retag _ _) d.toComposite
  simp only [AggQueryIn.evaluateRew]
  rw [har, map_comp_fst_groupByKey]
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
      dite_eq_left (show (((is k).castLE (Nat.le_succ m)
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
        R).dedup
      = (Multiset.map Prod.fst (Multiset.map
          (fun p : AnnotatedTuple T K m =>
            ((fun k => p.fst (is k), p.snd) : AnnotatedTuple T K n₁))
          R)).dedup from by
    rw [Multiset.map_map]
    rfl,
    ← map_fst_groupByKey, Multiset.map_map]
  refine Multiset.map_congr rfl (fun kv _ => ?_)
  simp only [Function.comp_apply]
  rw [Having.havingGroup_toComposite is
    R kv.fst]
  unfold GenRow.toCompositeRow
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, Fin.append_left]
    dsimp only
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
    · rw [Fin.append_left, Fin.append_left]
      rfl
    · rw [Fin.append_right, Fin.append_right]
      exact congrArg (fun a => Sum.inr (AggTok.tok a))
        (AggValue.ofGroup_toComposite _ _ _)
  · rw [Fin.append_right, Fin.append_right]
    dsimp only
    rw [GenAnn.finalize_gamma, List.map_map]
    rfl

/-- **Correctness of the bare-grouping rewriting** – the general
framework's rule (R5): for a classical subquery, the general evaluator's
grouping, embedded row-wise into the composite domain (tokens included,
finalized annotation appended), is computed by the rewritten world's
token-building grouping over the classically rewritten subquery. -/
theorem AggQueryIn.gammaRew_valid {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (qg : AggQuery T m (ColKind.allReg m))
    (hq : qg.classical) (d : AnnotatedDatabase T K) :
    ((AggQueryIn.Gamma is ts fs qg).evaluate d).map GenRow.toCompositeRow
      = (AggQueryIn.gammaRew is ts fs qg hq).evaluateRew d.toComposite :=
  AggQueryIn.gammaRewOf_valid is ts fs qg
    (fun k => ColKind.rewKinds_lt (is k).isLt)
    (ColKind.rewKinds_of_not_lt (lt_irrefl m)) (qg.rewriting hq) d
    ((qg.strip hq).evaluateAnnotated (qg.strip_source hq) d)
    (AggQueryIn.strip_bridge qg hq d)
    (AggQueryIn.rewriting_provRel qg hq d)


/-! ## The gate reads a transported token unchanged -/

/-- The composite transport preserves the scalar reading too: it moves the
values, not the worlds. -/
theorem AggValue.predProvScalar_toComposite (a : AggValue T K) (op : CompOp)
    (c : T) :
    a.toComposite.predProvScalar op (Sum.inl c) = a.predProvScalar op c := by
  have hlen : a.occs.length = a.toComposite.occs.length := by
    simp [AggValue.toComposite]
  unfold AggValue.predProvScalar
  refine (Fintype.sum_equiv (finCongr hlen).finsetCongr
    (fun W => Having.worldAnn a.anns W * Having.chi op (a.valOn W) c)
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply]
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
  · rw [ite_eq_left hne, ite_eq_left (by rwa [Finset.map_nonempty])]
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
  · rw [ite_eq_right hne, ite_eq_right (by rwa [Finset.map_nonempty])]

theorem AggValue.predProvOf_toComposite (a : AggValue T K) (op : CompOp)
    (c : T) :
    a.toComposite.predProvOf op (Sum.inl c) = a.predProvOf op c := by
  unfold AggValue.predProvOf
  rw [show a.toComposite.scalar = a.scalar from rfl]
  cases a.scalar
  · simpa using AggValue.predProv_toComposite a op c
  · simpa using AggValue.predProvScalar_toComposite a op c

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The same length, named by the transported expression's own family. -/
theorem AggExpr.length_toComposite (a : AggExpr T K) :
    a.occs.length = a.toComposite.occs.length := a.length_inl_occs

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The transport leaves an occurrence's annotation where it was. -/
theorem AggExpr.anns_toComposite (a : AggExpr T K)
    (i : Fin a.occs.length) :
    a.toComposite.anns (finCongr a.length_toComposite i) = a.anns i := by
  show (a.toComposite.occs.get _).snd.fst = (a.occs.get i).snd.fst
  simp [AggExpr.toComposite, List.get_eq_getElem, List.getElem_map]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- And an occurrence's membership of a leaf's group, the flags being
carried along with it. -/
theorem AggExpr.mem_inFrame_toComposite (a : AggExpr T K) (j : Fin a.arity)
    (i : Fin a.occs.length) :
    finCongr a.length_toComposite i ∈ a.toComposite.inFrame j
      ↔ i ∈ a.inFrame j := by
  rw [AggExpr.mem_inFrame, AggExpr.mem_inFrame]
  show (a.toComposite.occs.get _).snd.snd.fst j = true ↔ _
  simp [AggExpr.toComposite, List.get_eq_getElem, List.getElem_map]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Hence a transported world is a world exactly when it was one. -/
theorem AggExpr.isWorld_toComposite (a : AggExpr T K)
    (W : Finset (Fin a.occs.length)) :
    a.toComposite.IsWorld (W.map (finCongr a.length_toComposite).toEmbedding)
      ↔ a.IsWorld W := by
  unfold AggExpr.IsWorld
  refine forall_congr' (fun j => imp_congr (Iff.of_eq rfl) ?_)
  constructor
  · rintro ⟨i', hi'⟩
    obtain ⟨hiW, hif⟩ := Finset.mem_inter.mp hi'
    refine ⟨(finCongr a.length_toComposite).symm i', Finset.mem_inter.mpr
      ⟨Finset.mem_map_equiv.mp hiW, ?_⟩⟩
    refine (a.mem_inFrame_toComposite j _).mp ?_
    rwa [Equiv.apply_symm_apply]
  · rintro ⟨i, hi⟩
    obtain ⟨hiW, hif⟩ := Finset.mem_inter.mp hi
    exact ⟨finCongr a.length_toComposite i, Finset.mem_inter.mpr
      ⟨Finset.mem_map_equiv.mpr (by rwa [Equiv.symm_apply_apply]),
        (a.mem_inFrame_toComposite j i).mpr hif⟩⟩

/-- **The reading of a transported expression**: a world of the transport
is a world of the original, carrying the same annotation and reading the
embedding of the value read there, so a test that restricts along `inl`
sees the same thing. -/
theorem AggExpr.predProvWith_toComposite (a : AggExpr T K) (P : T → Kleene)
    (Q : T ⊕ K → Kleene) (hQ : ∀ v, Q (Sum.inl v) = P v) :
    a.toComposite.predProvWith Q = a.predProvWith P := by
  unfold AggExpr.predProvWith
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (finCongr a.length_toComposite).finsetCongr
    (fun W => if a.IsWorld W
      then Having.worldAnn a.anns W * Having.chiOf P (a.valOn W) else 0)
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply]
  by_cases hw : a.IsWorld W
  · rw [ite_eq_left hw, ite_eq_left ((a.isWorld_toComposite W).mpr hw)]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [AggValue.worldAnn_map_finCongr a.length_toComposite]
      exact (congrArg (fun α : Fin a.occs.length → K => Having.worldAnn α W)
        (funext (fun i => a.anns_toComposite i))).symm
    · rw [show a.toComposite.valOn
            (W.map (finCongr a.length_toComposite).toEmbedding)
          = Sum.inl (a.valOn W) from a.valOn_toComposite W]
      unfold Having.chiOf
      rw [hQ]
  · rw [ite_eq_right hw,
      ite_eq_right (fun h => hw ((a.isWorld_toComposite W).mp h))]

/-- Hence a comparison against an embedded constant. -/
theorem AggExpr.predProv_toComposite (a : AggExpr T K) (op : CompOp)
    (c : T) :
    a.toComposite.predProv op (Sum.inl c) = a.predProv op c := by
  rw [AggExpr.predProv_eq_predProvWith, AggExpr.predProv_eq_predProvWith]
  exact a.predProvWith_toComposite _ _ (fun v => CompOp.eval3_inl op v c)

/-- **The gate reads a transported token unchanged**, nested tokens
apart: an ordinary token by `AggValue.predProvOf_toComposite`, an
expression by `AggExpr.predProv_toComposite`. -/
theorem AggTok.predProvOf_toComposite (x : AggTok T K) (hx : x.isNested = false)
    (op : CompOp) (c : T) :
    x.toComposite.predProvOf op (Sum.inl c) = x.predProvOf op c := by
  cases x with
  | tok a => exact AggValue.predProvOf_toComposite a op c
  | nest a => exact absurd hx (by simp [AggTok.isNested])
  | expr a => exact AggExpr.predProv_toComposite a op c

