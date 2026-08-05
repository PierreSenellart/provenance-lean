import Provenance.QueryGenRewriting
import Provenance.QueryGenBridges

/-! # The rewritten world's evaluator: tokens as first-class column values

ProvSQL evaluates rewritten plans over a value universe that contains,
next to the regular values and the provenance identifiers, the aggregate
tokens produced by its `provsql_agg` gate; the `provsql_having` gate then
reads a token and produces the predicate provenance of an aggregate
comparison. The formal counterpart is the evaluator `QueryGen.evaluateRew`
defined here: it runs a rewritten query (a `QueryGen` over the composite
value type `T ⊕ K`) over rows `Tuple (GenValue (T ⊕ K) K) n` – the
lifted-column carrier of the general evaluator, instantiated at the
composite value type – with the kind vector saying which columns hold
tokens.

* On the value-kinded operators the evaluator is the plain semantics
  through the `inl` embedding (`Dedup`, `Diff` and `Gamma` collapse their
  statically all-regular rows to plain tuples, exactly as the general
  evaluator reads them through `GenRow.toAnnotated`).
* `QueryGen.GammaTok` builds tokens: one `AggValue.ofGroup` per
  `(term, aggregate)` pair over the group's occurrence sequence, whose
  annotations are the values of the explicit annotation term – in
  rewritten plans, the provenance column of the subquery – and writes the
  group-existence guard `δ(⊕ occs)` into its `prov` output column.
* `TermG.cmpAgg` is the cmp gate: `TermG.evalRew` interprets it by
  `AggValue.predProv`, the primitive the rewriting's correctness is
  stated against, faithfully to ProvSQL's own gate-relative correctness.

The rewriting rules built on this evaluator live downstream:
`Provenance.QueryGenAggRewriting` (the bare grouping and the `HAVING`
site) and `Provenance.QueryGenClosure` (the compositional closure).
-/

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K]
  [DecidableEq K] [HasAltLinearOrder K]

/-! ## Terms and predicates in the rewritten world -/

/-- The annotation part of a composite value (`𝟘` on data values: a
malformed provenance read carries no worlds). -/
def Sum.annPart : T ⊕ K → K
  | Sum.inl _ => 0
  | Sum.inr k => k

/-- Term evaluation in the rewritten world: as `TermG.eval` on the
value-reading constructors, with the `cmpAgg` gate interpreted by the
predicate provenance of the token against the comparison term. -/
def TermG.evalRew {n : ℕ} {κ : Fin n → ColKind} :
    TermG (T ⊕ K) κ → Tuple (GenValue (T ⊕ K) K) n → T ⊕ K
  | .const a, _ => a
  | .index k _, u => AggValue.collapseSum (u k)
  | .provIndex k _, u => AggValue.collapseSum (u k)
  | .cmpAgg k _ op c, u =>
    match u k with
    | Sum.inl _ => Sum.inr 0
    | Sum.inr a => Sum.inr (a.predProv op (c.evalRew u))
  | .add t₁ t₂, u => t₁.evalRew u + t₂.evalRew u
  | .sub t₁ t₂, u => t₁.evalRew u - t₂.evalRew u
  | .mul t₁ t₂, u => t₁.evalRew u * t₂.evalRew u

/-- Projection-column evaluation in the rewritten world. -/
def ProjCol.evalRew {n : ℕ} {κ : Fin n → ColKind}
    (p : ProjCol (T ⊕ K) κ) (u : Tuple (GenValue (T ⊕ K) K) n) :
    GenValue (T ⊕ K) K :=
  match p with
  | .term t => Sum.inl (t.evalRew u)
  | .token k _ => u k
  | .provTerm t => Sum.inl (t.evalRew u)

/-- Classical truth of a predicate in the rewritten world (compared
tokens read through their deterministic collapse, as in
`GenPred.holds`). -/
def GenPred.holdsRew {n : ℕ} {κ : Fin n → ColKind} :
    GenPred (T ⊕ K) κ → Tuple (GenValue (T ⊕ K) K) n → Prop
  | .cmp op t₁ t₂, u => op.eval (t₁.evalRew u) (t₂.evalRew u)
  | .aggCmp k _ op t, u =>
      op.eval (AggValue.collapseSum (u k)) (t.evalRew u)
  | .and φ ψ, u => φ.holdsRew u ∧ ψ.holdsRew u
  | .or φ ψ, u => φ.holdsRew u ∨ ψ.holdsRew u
  | .not φ, u => ¬ φ.holdsRew u

/-- Structural decidability of `holdsRew`. -/
def GenPred.decHoldsRew {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred (T ⊕ K) κ) (u : Tuple (GenValue (T ⊕ K) K) n) :
    Decidable (φ.holdsRew u) :=
  match φ with
  | .cmp op _ _ => inferInstanceAs (Decidable (op.eval _ _))
  | .aggCmp _ _ op _ => inferInstanceAs (Decidable (op.eval _ _))
  | .and φ ψ => @instDecidableAnd _ _ (φ.decHoldsRew u) (ψ.decHoldsRew u)
  | .or φ ψ => @instDecidableOr _ _ (φ.decHoldsRew u) (ψ.decHoldsRew u)
  | .not φ => @instDecidableNot _ (φ.decHoldsRew u)

instance GenPred.instDecidableHoldsRew {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred (T ⊕ K) κ) : DecidablePred φ.holdsRew :=
  fun u => φ.decHoldsRew u

/-! ## The evaluator -/

/-- **The rewritten world's evaluator**: plain multiset semantics over
token-bearing rows. Value-kinded operators act through the `inl`
embedding; `GammaTok` builds tokens and the group guard; the `cmpAgg`
gate inside terms is interpreted by `predProv`. -/
def QueryGen.evaluateRew : {n : ℕ} → {κ : Fin n → ColKind} →
    QueryGen (T ⊕ K) n κ → Database (T ⊕ K) →
    Multiset (Tuple (GenValue (T ⊕ K) K) n)
  | n, _, .Rel _ s, D =>
    match D.find n s with
    | none => 0
    | some rn => rn.map (fun t =>
        ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) n))
  | _, _, .Proj ps q, D =>
    (q.evaluateRew D).map (fun u => (fun j => (ps j).evalRew u))
  | _, _, .Sel φ q, D =>
    (q.evaluateRew D).filter φ.holdsRew
  | _, _, .Prod q₁ q₂, D =>
    ((q₁.evaluateRew D).product (q₂.evaluateRew D)).map
      (fun (x, y) => Fin.append x y)
  | _, _, .Sum q₁ q₂, D => q₁.evaluateRew D + q₂.evaluateRew D
  | _, _, .Dedup q, D =>
    (((q.evaluateRew D).map
        (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))).dedup).map
      (fun t => (fun k => Sum.inl (t k)))
  | _, _, .Diff q₁ q₂, D =>
    let r₂ := (q₂.evaluateRew D).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))
    ((((q₁.evaluateRew D).map
        (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))).filter
      (fun t => t ∉ r₂)).map (fun t => (fun k => Sum.inl (t k))))
  | _, _, @QueryGen.Gamma _ m n₁ n₂ is ts fs q, D =>
    let r : Relation (T ⊕ K) m := (q.evaluateRew D).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) m))
    let keys := (r.map
      (fun u => (fun k => u (is k) : Tuple (T ⊕ K) n₁))).dedup
    keys.map (fun g => (fun k => Sum.inl (Fin.append g
      (fun j => (fs j) ((Relation.groupSeq is r g).map (ts j).eval)) k)))
  | _, _, .Retag _ q, D => q.evaluateRew D
  | _, _, @QueryGen.ProvSum _ _m n₁ _κ is _his t q, D =>
    let r := q.evaluateRew D
    let keys := (r.map
      (fun u => (fun k => GenRow.plainTuple u (is k)
        : Tuple (T ⊕ K) n₁))).dedup
    keys.map (fun g =>
      Fin.append (fun k => (Sum.inl (g k) : GenValue (T ⊕ K) K))
        (fun _ : Fin 1 => Sum.inl
          (((r.filter (fun u => ∀ k' : Fin n₁,
              GenRow.plainTuple u (is k') = g k')).map
            (fun u => t.evalRew u)).fold addFn 0)))
  | _, _, @QueryGen.GammaTok _ m n₁ n₂ _κ is _his ts fs a q, D =>
    let r := q.evaluateRew D
    let ar : AnnotatedRelation (T ⊕ K) K m :=
      r.map (fun u => (GenRow.plainTuple u, (a.evalRew u).annPart))
    (Multiset.ofList (groupByKey (ar.map (fun p =>
        ((fun k => p.fst (is k), p.snd)
          : AnnotatedTuple (T ⊕ K) K n₁)))).val).map
      ((fun g : Tuple (T ⊕ K) n₁ =>
        Fin.append
          (Fin.append (fun k => (Sum.inl (g k) : GenValue (T ⊕ K) K))
            (fun j => Sum.inr (AggValue.ofGroup (fs j) (ts j)
              (Having.havingGroup is ar g))))
          (fun _ : Fin 1 => Sum.inl
            (Sum.inr (SemiringWithMonus.delta
              ((Having.havingGroup is ar g).map Prod.snd).sum))))
        ∘ Prod.fst)

/-! ## Agreement with the plain semantics off the token operators -/

/-- No token-building grouping: on this fragment the rewritten world's
evaluator is the plain semantics through the `inl` embedding. -/
def QueryGen.noGammaTok {T' : Type} : {n : ℕ} → {κ : Fin n → ColKind} →
    QueryGen T' n κ → Prop
  | _, _, .Rel _ _ => True
  | _, _, .Proj _ q => q.noGammaTok
  | _, _, .Sel _ q => q.noGammaTok
  | _, _, .Prod q₁ q₂ => q₁.noGammaTok ∧ q₂.noGammaTok
  | _, _, .Sum q₁ q₂ => q₁.noGammaTok ∧ q₂.noGammaTok
  | _, _, .Dedup q => q.noGammaTok
  | _, _, .Diff q₁ q₂ => q₁.noGammaTok ∧ q₂.noGammaTok
  | _, _, .Gamma _ _ _ q => q.noGammaTok
  | _, _, .ProvSum _ _ _ q => q.noGammaTok
  | _, _, .Retag _ q => q.noGammaTok
  | _, _, .GammaTok _ _ _ _ _ _ => False

/-- On `inl`-embedded rows every term evaluates in the rewritten world
as its plain evaluation – including the gate, whose junk reading `𝟘` is
definitionally the composite zero. -/
theorem TermG.evalRew_inl {n : ℕ} {κ : Fin n → ColKind}
    (t : TermG (T ⊕ K) κ) (u : Tuple (T ⊕ K) n) :
    t.evalRew (fun k => Sum.inl (u k)) = t.evalPlain u := by
  induction t with
  | const a => rfl
  | index k h => rfl
  | provIndex k h => rfl
  | cmpAgg k h op c ih => rfl
  | add t₁ t₂ ih₁ ih₂ => show _ + _ = _ + _; rw [ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ =>
    show HSub.hSub _ _ = HSub.hSub _ _
    rw [ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => show _ * _ = _ * _; rw [ih₁, ih₂]

/-- Projection columns on `inl`-embedded rows evaluate to the embedded
plain reading. -/
theorem ProjCol.evalRew_inl {n : ℕ} {κ : Fin n → ColKind}
    (p : ProjCol (T ⊕ K) κ) (u : Tuple (T ⊕ K) n) :
    p.evalRew (fun k => Sum.inl (u k)) = Sum.inl (p.evalPlain u) := by
  cases p with
  | term t => exact congrArg Sum.inl (t.evalRew_inl u)
  | token k h => rfl
  | provTerm t => exact congrArg Sum.inl (t.evalRew_inl u)

/-- Predicates on `inl`-embedded rows hold as their plain reading. -/
theorem GenPred.holdsRew_inl {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred (T ⊕ K) κ) (u : Tuple (T ⊕ K) n) :
    φ.holdsRew (fun k => Sum.inl (u k)) ↔ φ.holdsPlain u := by
  induction φ with
  | cmp op t₁ t₂ =>
    simp only [GenPred.holdsRew, GenPred.holdsPlain,
      TermG.evalRew_inl]
  | aggCmp k h op t =>
    simp only [GenPred.holdsRew, GenPred.holdsPlain, TermG.evalRew_inl]
    exact Iff.rfl
  | and φ ψ ihφ ihψ =>
    simp only [GenPred.holdsRew, GenPred.holdsPlain]
    exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ =>
    simp only [GenPred.holdsRew, GenPred.holdsPlain]
    exact or_congr ihφ ihψ
  | not φ ihφ =>
    simp only [GenPred.holdsRew, GenPred.holdsPlain]
    exact not_congr ihφ

/-- Maps push through the multiset product. -/
theorem Multiset.map_product_map {α β α' β' : Type _} (f : α → α')
    (g : β → β') (s : Multiset α) (t : Multiset β) :
    (s.map f).product (t.map g) = (s.product t).map (Prod.map f g) := by
  unfold Multiset.product
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr (fun a _ => ?_)
  rw [Multiset.map_map, Multiset.map_map]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Collapsing `inl`-embedded rows is the identity. -/
theorem map_plainTuple_map_inl {m : ℕ} (X : Multiset (Tuple (T ⊕ K) m)) :
    Multiset.map (fun u : Tuple (GenValue (T ⊕ K) K) m =>
        (GenRow.plainTuple u : Tuple (T ⊕ K) m))
      (X.map (fun t => ((fun k => Sum.inl (t k))
        : Tuple (GenValue (T ⊕ K) K) m)))
      = X := by
  rw [Multiset.map_map]
  exact Eq.trans (Multiset.map_congr rfl (fun t _ =>
    funext (fun k => rfl))) (Multiset.map_id X)

/-- **Plain agreement.** Off the token-building operator, the rewritten
world's evaluator is the plain semantics through the `inl` embedding. -/
theorem QueryGen.evaluateRew_plain :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen (T ⊕ K) n κ)
      (_hq : q.noGammaTok) (D : Database (T ⊕ K)),
      q.evaluateRew D
        = (q.evaluatePlain D).map (fun t =>
            ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) _)) := by
  intro n κ q
  induction q with
  | Rel n s =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    cases hf : D.find n s
    · rfl
    · rfl
  | Proj ps q ih =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih hq D, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun t _ => ?_)
    simp only [Function.comp_apply]
    funext j
    exact (ps j).evalRew_inl t
  | Sel φ q ih =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih hq D]
    simp only [Multiset.filter_map]
    exact congrArg _ (Multiset.filter_congr (fun t _ => φ.holdsRew_inl t))
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih₁ hq.1 D, ih₂ hq.2 D, Multiset.map_product_map, Multiset.map_map]
    rw [show (q₁.evaluatePlain D * q₂.evaluatePlain D)
        = Multiset.map (fun p : Tuple (T ⊕ K) _ × Tuple (T ⊕ K) _ =>
            Fin.append p.1 p.2)
          (Multiset.product (q₁.evaluatePlain D) (q₂.evaluatePlain D))
      from rfl]
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    simp only [Function.comp_apply, Prod.map]
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih₁ hq.1 D, ih₂ hq.2 D, Multiset.map_add]
  | Dedup q ih =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih hq D, map_plainTuple_map_inl]
    congr 1
    exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) _) =>
      @Multiset.dedup _ i (q.evaluatePlain D)) (Subsingleton.elim _ _)
  | @Diff nD q₁ q₂ ih₁ ih₂ =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih₁ hq.1 D, ih₂ hq.2 D, map_plainTuple_map_inl,
      map_plainTuple_map_inl]
    exact congrArg (Multiset.map _)
      (congrArg (fun i : DecidablePred (fun t : Tuple (T ⊕ K) nD =>
          ¬ @Membership.mem _ (Multiset (Tuple (T ⊕ K) nD))
            Multiset.instMembership (q₂.evaluatePlain D) t) =>
        @Multiset.filter _ _ i (q₁.evaluatePlain D))
        (Subsingleton.elim _ _))
  | @Gamma m n₁ n₂ is ts fs q ih =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih hq D, map_plainTuple_map_inl, Multiset.map_map]
    refine Multiset.map_congr ?_ (fun g _ => rfl)
    exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) n₁) =>
      @Multiset.dedup _ i (Multiset.map
        (fun u (k : Fin n₁) => u (is k)) (q.evaluatePlain D)))
      (Subsingleton.elim _ _)
  | Retag h q ih =>
    intro hq D
    exact ih hq D
  | @ProvSum m n₁ κ' is his t q ih =>
    intro hq D
    simp only [QueryGen.evaluateRew, QueryGen.evaluatePlain]
    rw [ih hq D, Multiset.map_map]
    rw [show ((fun u : Tuple (GenValue (T ⊕ K) K) m =>
          ((fun k => GenRow.plainTuple u (is k)) : Tuple (T ⊕ K) n₁))
        ∘ (fun t : Tuple (T ⊕ K) m =>
            ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) m)))
        = (fun u : Tuple (T ⊕ K) m =>
            ((fun k => u (is k)) : Tuple (T ⊕ K) n₁))
      from funext (fun t => funext (fun k => rfl))]
    rw [Multiset.map_map]
    refine Multiset.map_congr ?_ (fun g _ => ?_)
    · exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) n₁) =>
        @Multiset.dedup _ i (Multiset.map
          (fun u (k : Fin n₁) => u (is k)) (q.evaluatePlain D)))
        (Subsingleton.elim _ _)
    · simp only [Function.comp_apply]
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        refine congrArg Sum.inl (congrArg (Multiset.fold addFn 0) ?_)
        rw [Multiset.filter_map, Multiset.map_map]
        refine Eq.trans
          (Multiset.map_congr rfl (fun u _ => t.evalRew_inl u)) ?_
        refine congrArg₂ Multiset.map rfl ?_
        congr 1
  | GammaTok is his ts fs a q ih =>
    intro hq D
    exact hq.elim

/-! ## The fused predicate provenance under the composite embedding

The rewritten site groups composite rows – the `inl`-embedded data with
the annotation appended as the provenance column – while the annotated
site groups the original annotated tuples. The fused predicate
provenance is invariant under this embedding: comparisons restrict along
`inl`, the lifted aggregate computes on the embedded values, and the
occurrence annotations are read off unchanged. -/

/-- Lift a sequence aggregate to the composite domain (junk on the
annotation arm, faithful on `inl`-embedded values). -/
def SeqAggFunc.liftComposite (f : SeqAggFunc T) : SeqAggFunc (T ⊕ K) :=
  fun l => Sum.inl (f (l.map (Sum.elim id (fun _ => 0))))

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The lifted aggregate on `inl`-embedded values. -/
theorem SeqAggFunc.liftComposite_map_inl (f : SeqAggFunc T)
    (l : List T) :
    (f.liftComposite (K := K)) (l.map Sum.inl) = Sum.inl (f l) := by
  unfold SeqAggFunc.liftComposite
  rw [List.map_map]
  rw [show (Sum.elim id (fun _ => (0 : T)) ∘ (Sum.inl : T → T ⊕ K)) = id
    from funext (fun x => rfl)]
  rw [List.map_id]

omit [DecidableEq K] in
/-- Comparison operators restrict along the `inl` embedding. -/
theorem CompOp.eval_inl (op : CompOp) (x y : T) :
    op.eval (Sum.inl x : T ⊕ K) (Sum.inl y) ↔ op.eval x y := by
  have hle : ∀ a b : T, ((Sum.inl a : T ⊕ K) ≤ Sum.inl b) ↔ a ≤ b :=
    fun a b => Iff.rfl
  have hlt : ∀ a b : T, ((Sum.inl a : T ⊕ K) < Sum.inl b) ↔ a < b := by
    intro a b
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
    exact and_congr (hle a b) (not_congr (hle b a))
  have heq : ∀ a b : T, ((Sum.inl a : T ⊕ K) = Sum.inl b) ↔ a = b :=
    fun a b => ⟨Sum.inl.inj, congrArg Sum.inl⟩
  cases op
  case eq => exact heq x y
  case ne => exact not_congr (heq x y)
  case lt => exact hlt x y
  case le => exact hle x y
  case gt => exact hlt y x
  case ge => exact hle y x

omit [DecidableEq K] in
/-- The comparison indicator restricts along the `inl` embedding. -/
theorem Having.chi_inl (op : CompOp) (x y : T) :
    (Having.chi op (Sum.inl x : T ⊕ K) (Sum.inl y) : K)
      = Having.chi op x y := by
  unfold Having.chi
  by_cases h : op.eval x y
  · rw [if_pos ((CompOp.eval_inl op x y).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((CompOp.eval_inl op x y).mp hc)), if_neg h]

/-! ## The classical rewriting stays off the token operators -/

omit [DecidableEq K] in
/-- The classical rewriting emits no token-building grouping. -/
theorem QueryGen.rewritingGen_noGammaTok :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (hq : q.classical),
      ((q.rewritingGen hq
        : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n))).noGammaTok
  | _, _, .Rel _ _, _ => trivial
  | _, _, @QueryGen.Proj _ n m κ ps q, hq =>
    rewritingGen_noGammaTok q hq.2
  | _, _, .Sel _ q, hq => rewritingGen_noGammaTok q hq.2
  | _, _, @QueryGen.Prod _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq =>
    ⟨rewritingGen_noGammaTok q₁ hq.1, rewritingGen_noGammaTok q₂ hq.2⟩
  | _, _, .Sum q₁ q₂, hq =>
    ⟨rewritingGen_noGammaTok q₁ hq.1, rewritingGen_noGammaTok q₂ hq.2⟩
  | _, _, @QueryGen.Dedup _ n q, hq => rewritingGen_noGammaTok q hq
  | _, _, @QueryGen.Diff _ n q₁ q₂, hq =>
    ⟨⟨rewritingGen_noGammaTok q₁ hq.1,
      ⟨rewritingGen_noGammaTok q₁ hq.1, rewritingGen_noGammaTok q₂ hq.2⟩⟩,
     ⟨rewritingGen_noGammaTok q₁ hq.1, rewritingGen_noGammaTok q₂ hq.2⟩⟩
  | _, _, .Gamma _ _ _ _, hq => False.elim hq
  | _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, .Retag _ _, hq => False.elim hq
  | _, _, .GammaTok _ _ _ _ _ _, hq => False.elim hq
termination_by structural _ _ q _ => q

/-! ## The group sequence under the composite embedding -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Coordinates of the composite embedding of an annotated tuple. -/
theorem AnnotatedTuple.toComposite_coord {m : ℕ}
    (p : AnnotatedTuple T K m) (j : Fin (m + 1)) :
    p.toComposite j
      = if h : (j : ℕ) < m then Sum.inl (p.fst ⟨j, h⟩)
        else Sum.inr p.snd := by
  unfold AnnotatedTuple.toComposite
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, dif_pos (by
      simp only [Fin.val_castAdd]
      exact i.isLt)]
    exact congrArg (fun k => Sum.inl (p.fst k)) (Fin.ext rfl)
  · rw [Fin.append_right, dif_neg (by
      simp only [Fin.val_natAdd]
      omega)]
    rw [Subsingleton.elim i (0 : Fin 1)]
    rfl

omit [DecidableEq K] in
/-- The composite order restricts to the value order on `inl`. -/
theorem Sum.inl_lt_inl_composite (x y : T) :
    LT.lt (Sum.inl x : T ⊕ K) (Sum.inl y) ↔ LT.lt x y := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
  exact and_congr Iff.rfl (not_congr Iff.rfl)

omit [DecidableEq K] in
/-- The composite order restricts to the alternative order on `inr`. -/
theorem Sum.inr_lt_inr_composite (x y : K) :
    LT.lt (Sum.inr x : T ⊕ K) (Sum.inr y)
      ↔ HasAltLinearOrder.altOrder.lt x y := by
  rw [lt_iff_le_not_ge, HasAltLinearOrder.altOrder.lt_iff_le_not_ge]
  exact and_congr Iff.rfl (not_congr Iff.rfl)

omit [DecidableEq K] in
/-- **The group sequence under the composite embedding**: embedding the
relation and the key `inl`-wise embeds the group sequence. The embedding
is monotone for the sort's tie-break order (data columns compare on the
`inl` arm, the appended provenance column and the annotation both by the
alternative order), and sorted lists of the same multiset are unique. -/
theorem Having.havingGroup_toComposite {m n₁ : ℕ}
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T K m)
    (g : Tuple T n₁) :
    Having.havingGroup (fun k => (is k).castLE (Nat.le_succ m))
      (r.map (fun p => ((p.toComposite, p.snd)
        : AnnotatedTuple (T ⊕ K) K (m + 1))))
      (fun k => Sum.inl (g k))
      = (Having.havingGroup is r g).map
          (fun p => ((p.toComposite, p.snd)
            : AnnotatedTuple (T ⊕ K) K (m + 1))) := by
  letI : LinearOrder K := HasAltLinearOrder.altOrder
  letI ordm : LinearOrder (AnnotatedTuple T K m) :=
    inferInstanceAs (LinearOrder (Tuple T m ×ₗ K))
  letI ordm1 : LinearOrder (AnnotatedTuple (T ⊕ K) K (m + 1)) :=
    inferInstanceAs (LinearOrder (Tuple (T ⊕ K) (m + 1) ×ₗ K))
  have hmono : ∀ a b : AnnotatedTuple T K m, ordm.le a b →
      ordm1.le ((a.toComposite, a.snd)) ((b.toComposite, b.snd)) := by
    intro a b hab
    rcases hab with ⟨b₁, b₂, h⟩ | @⟨x, b₁, b₂, h⟩
    · obtain ⟨i, hbelow, hi⟩ := h
      refine Prod.Lex.left _ _ ?_
      refine ⟨⟨i, by omega⟩, fun j hj => ?_, ?_⟩
      · have hjm : (j : ℕ) < m := by
          have := (Fin.lt_def.mp hj); omega
        simp only [AnnotatedTuple.toComposite_coord]
        rw [dif_pos hjm, dif_pos hjm]
        exact congrArg Sum.inl (hbelow ⟨j, hjm⟩
          (Fin.lt_def.mpr (Fin.lt_def.mp hj)))
      · have him : ((⟨(i : ℕ), by omega⟩ : Fin (m + 1)) : ℕ) < m :=
          i.isLt
        simp only [AnnotatedTuple.toComposite_coord]
        rw [dif_pos him, dif_pos him]
        exact (Sum.inl_lt_inl_composite _ _).mpr hi
    · rcases eq_or_ne b₁ b₂ with heq2 | hne
      · rw [heq2]
        exact ordm1.le_refl _
      · have hlt : HasAltLinearOrder.altOrder.lt b₁ b₂ :=
          (HasAltLinearOrder.altOrder.lt_iff_le_not_ge b₁ b₂).mpr
            ⟨h, fun hge => hne
              (HasAltLinearOrder.altOrder.le_antisymm _ _ h hge)⟩
        refine Prod.Lex.left _ _ ?_
        refine ⟨Fin.last m, fun j hj => ?_, ?_⟩
        · have hjm : (j : ℕ) < m := by
            have := Fin.lt_def.mp hj
            simp only [Fin.val_last] at this
            exact this
          simp only [AnnotatedTuple.toComposite_coord]
          rw [dif_pos hjm, dif_pos hjm]
        · have hlm : ¬ ((Fin.last m : Fin (m + 1)) : ℕ) < m := by
            simp only [Fin.val_last]; omega
          simp only [AnnotatedTuple.toComposite_coord]
          rw [dif_neg hlm, dif_neg hlm]
          exact (Sum.inr_lt_inr_composite _ _).mpr hlt
  haveI : Std.Antisymm (fun x y : AnnotatedTuple (T ⊕ K) K (m + 1) =>
      ordm1.le x y) :=
    ⟨fun _ _ h₁ h₂ => ordm1.le_antisymm _ _ h₁ h₂⟩
  refine List.Perm.eq_of_pairwise'
    (r := fun x y : AnnotatedTuple (T ⊕ K) K (m + 1) => ordm1.le x y)
    ?_ ?_ (Multiset.coe_eq_coe.mp ?_)
  · unfold Having.havingGroup
    exact List.Pairwise.imp (fun h => h) (Subtype.property _)
  · refine List.Pairwise.map _ (fun {a b} hab => hmono a b hab) ?_
    unfold Having.havingGroup
    exact List.Pairwise.imp (fun h => h) (Subtype.property _)
  · rw [Having.havingGroup_coe,
      show ((↑((((Having.havingGroup is r g).map
          (fun p : AnnotatedTuple T K m => ((p.toComposite, p.snd)
            : AnnotatedTuple (T ⊕ K) K (m + 1))))
          : List (AnnotatedTuple (T ⊕ K) K (m + 1))))
          : Multiset (AnnotatedTuple (T ⊕ K) K (m + 1))))
        = Multiset.map (fun p : AnnotatedTuple T K m =>
            ((p.toComposite, p.snd) : AnnotatedTuple (T ⊕ K) K (m + 1)))
          ((↑(Having.havingGroup is r g))
            : Multiset (AnnotatedTuple T K m)) from
        (Multiset.map_coe _ _).symm,
      Having.havingGroup_coe, Multiset.filter_map]
    congr 1
    congr 1
    funext p
    refine propext (forall_congr' (fun k' => ?_))
    dsimp only
    rw [AnnotatedTuple.toComposite_coord,
      dif_pos (show (((is k').castLE (Nat.le_succ m) : Fin (m + 1)) : ℕ)
        < m from (is k').isLt)]
    exact ⟨fun h => Sum.inl.inj h, fun h => congrArg Sum.inl h⟩

/-! ## Reading a rewritten evaluation back as an annotated relation -/

/-- Mapping a key-only function over a grouped relation is mapping it
over the deduplicated keys (the accumulated annotations are unread). -/
theorem map_comp_fst_groupByKey {n : ℕ} {β : Type}
    (G : Tuple (T ⊕ K) n → β) (Y : AnnotatedRelation (T ⊕ K) K n) :
    Multiset.map (G ∘ Prod.fst) (Multiset.ofList (groupByKey Y).val)
      = Multiset.map G ((Y.map Prod.fst).dedup) := by
  rw [← Multiset.map_map, map_fst_groupByKey]
  exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) n) =>
    Multiset.map G (@Multiset.dedup _ i (Multiset.map Prod.fst Y)))
    (Subsingleton.elim _ _)

/-- **The rewritten world reads back as an annotated relation.** Pairing
the collapsed data columns of the rewritten evaluation of a classical
rewriting with the annotation read off its provenance column recovers the
composite embedding of the classical annotated semantics – the input the
token-building groupings of the rewritten world consume. -/
theorem QueryGen.rewritingGen_provRel {n : ℕ} {κ : Fin n → ColKind}
    (q : QueryGen T n κ) (hq : q.classical) (d : AnnotatedDatabase T K) :
    Multiset.map (fun u => (GenRow.plainTuple u,
        ((TermG.provIndex (Fin.last n)
          (ColKind.rewKinds_of_not_lt (lt_irrefl n))).evalRew u).annPart))
      ((q.rewritingGen hq).evaluateRew d.toComposite)
      = ((q.strip hq).evaluateAnnotated (q.strip_noAgg hq) d).map
          (fun p => ((p.toComposite, p.snd)
            : AnnotatedTuple (T ⊕ K) K (n + 1))) := by
  have hR : (q.rewritingGen hq).evaluateRew d.toComposite
      = Multiset.map (fun t : Tuple (T ⊕ K) (n + 1) =>
          ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) (n + 1)))
        (((q.strip hq).evaluateAnnotated (q.strip_noAgg hq)
          d).toComposite) := by
    rw [QueryGen.evaluateRew_plain _
        (QueryGen.rewritingGen_noGammaTok q hq) _,
      QueryGen.rewritingGen_plain q hq d.toComposite,
      ← Query.rewriting_valid (q.strip hq) (q.strip_noAgg hq) d]
  rw [hR]
  unfold AnnotatedRelation.toComposite
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  refine Prod.ext ?_ ?_
  · funext k
    rfl
  · show (AggValue.collapseSum
        (Sum.inl (p.toComposite (Fin.last n)))).annPart = p.snd
    rw [show p.toComposite (Fin.last n) = Sum.inr p.snd from by
      rw [AnnotatedTuple.toComposite_coord,
        dif_neg (by simp only [Fin.val_last]; omega)]]
    rfl
