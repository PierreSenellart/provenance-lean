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

omit [DecidableEq K] in
/-- **The fused predicate provenance under the composite embedding.** -/
theorem Having.havingProv_toComposite {m : ℕ}
    (U : List (AnnotatedTuple T K m)) (t : Term T m) (f : SeqAggFunc T)
    (op : CompOp) (c : T) :
    Having.havingProv
      (U.map (fun p => ((p.toComposite, p.snd)
        : AnnotatedTuple (T ⊕ K) K (m + 1))))
      (t.castToAnnotatedTuple) (f.liftComposite) op (Sum.inl c)
      = Having.havingProv U t f op c := by
  have hlen : U.length = (U.map (fun p => ((p.toComposite, p.snd)
      : AnnotatedTuple (T ⊕ K) K (m + 1)))).length := by
    rw [List.length_map]
  unfold Having.havingProv
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (finCongr hlen).finsetCongr
    (fun W => if W.Nonempty
      then Having.worldAnn (fun i => (U.get i).snd) W
        * Having.chi op (Having.aggValOn U t f W) c else 0)
    _ (fun W => ?_)).symm
  rw [Equiv.finsetCongr_apply]
  by_cases hne : W.Nonempty
  · rw [if_pos hne, if_pos (by rwa [Finset.map_nonempty])]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [AggValue.worldAnn_map_finCongr hlen]
      exact congrArg (fun α : Fin U.length → K => Having.worldAnn α W)
        (funext (fun i => by simp [List.getElem_map]))
    · rw [show Having.aggValOn
            (U.map (fun p => ((p.toComposite, p.snd)
              : AnnotatedTuple (T ⊕ K) K (m + 1))))
            (t.castToAnnotatedTuple) (f.liftComposite)
            (W.map (finCongr hlen).toEmbedding)
          = Sum.inl (Having.aggValOn U t f W) from ?_]
      · exact (Having.chi_inl op _ c).symm
      · unfold Having.aggValOn
        rw [AggValue.seqOf_map _ U hlen W, List.map_map]
        rw [show ((fun p : AnnotatedTuple (T ⊕ K) K (m + 1) =>
              Term.eval t.castToAnnotatedTuple p.fst)
            ∘ (fun p : AnnotatedTuple T K m =>
                ((p.toComposite, p.snd)
                  : AnnotatedTuple (T ⊕ K) K (m + 1))))
            = (fun p : AnnotatedTuple T K m =>
                Sum.inl (t.eval p.fst)) from
          funext (fun p => Term.castToAnnotatedTuple_eval t p.fst p.snd)]
        rw [show (fun p : AnnotatedTuple T K m =>
              (Sum.inl (t.eval p.fst) : T ⊕ K))
            = (Sum.inl ∘ fun p : AnnotatedTuple T K m => t.eval p.fst)
          from rfl]
        rw [← List.map_map]
        exact SeqAggFunc.liftComposite_map_inl f _
  · rw [if_neg hne, if_neg (by rwa [Finset.map_nonempty])]

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

/-! ## The HAVING site and its rewriting -/

/-- A classical term over the group key, lifted to a composite term
reading designated regular columns of a rewritten schema. -/
def Term.liftKeys {n₁ N : ℕ} {κ' : Fin N → ColKind}
    (pos : Fin n₁ → Fin N) (hpos : ∀ k, κ' (pos k) = ColKind.reg) :
    Term T n₁ → TermG (T ⊕ K) κ'
  | .const c => .const (Sum.inl c)
  | .index k => .index (pos k) (hpos k)
  | .add t₁ t₂ => .add (t₁.liftKeys pos hpos) (t₂.liftKeys pos hpos)
  | .sub t₁ t₂ => .sub (t₁.liftKeys pos hpos) (t₂.liftKeys pos hpos)
  | .mul t₁ t₂ => .mul (t₁.liftKeys pos hpos) (t₂.liftKeys pos hpos)

/-- The lifted key term evaluates in the rewritten world as the original
term on the key, when the designated columns hold the embedded key. -/
theorem Term.liftKeys_evalRew {n₁ N : ℕ} {κ' : Fin N → ColKind}
    (pos : Fin n₁ → Fin N) (hpos : ∀ k, κ' (pos k) = ColKind.reg)
    (s : Term T n₁) (u : Tuple (GenValue (T ⊕ K) K) N) (g : Tuple T n₁)
    (hu : ∀ k, u (pos k) = Sum.inl (Sum.inl (g k))) :
    (s.liftKeys pos hpos).evalRew u = Sum.inl (s.eval g) := by
  induction s with
  | const c => rfl
  | index k =>
    show AggValue.collapseSum (u (pos k)) = Sum.inl (g k)
    rw [hu k]
    rfl
  | add t₁ t₂ ih₁ ih₂ =>
    show TermG.evalRew _ u + TermG.evalRew _ u = _
    rw [ih₁, ih₂]
    rfl
  | sub t₁ t₂ ih₁ ih₂ =>
    show HSub.hSub (TermG.evalRew _ u) (TermG.evalRew _ u) = _
    rw [ih₁, ih₂]
    rfl
  | mul t₁ t₂ ih₁ ih₂ =>
    show TermG.evalRew _ u * TermG.evalRew _ u = _
    rw [ih₁, ih₂]
    rfl


/-- **The rewritten HAVING site**: the token-building grouping over the
rewritten subquery (annotations read off the provenance column), the
group keys projected out, and the cmp gate applied to the `l`-th token
in the provenance output column – the query-level shape of ProvSQL's
rewritten `GROUP BY … HAVING` block. -/
def QueryGen.havingSiteRew {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (op : CompOp) (l : Fin n₂) (s : Term T n₁)
    (qg : QueryGen T m (ColKind.allReg m)) (hq : qg.classical) :
    QueryGen (T ⊕ K) (n₁ + 1) (ColKind.rewKinds n₁) :=
  QueryGen.retagToRew
    (fun j => by
      by_cases hj : (j : ℕ) < n₁
      · rw [dif_pos hj]; rfl
      · rw [dif_neg hj]; rfl)
    (QueryGen.Proj
      (fun j : Fin (n₁ + 1) =>
        if hj : (j : ℕ) < n₁ then
          ProjCol.term (TermG.index
            (Fin.castAdd 1 (Fin.castAdd n₂ (⟨j, hj⟩ : Fin n₁)))
            ((Fin.append_left _ _ _).trans
              ((Fin.append_left _ _ _).trans
                (ColKind.rewKinds_lt (is ⟨j, hj⟩).isLt))))
        else
          ProjCol.provTerm (TermG.cmpAgg
            (Fin.castAdd 1 (Fin.natAdd n₁ l))
            ((Fin.append_left _ _ _).trans (Fin.append_right _ _ _))
            op
            (s.liftKeys
              (fun k => Fin.castAdd 1 (Fin.castAdd n₂ k))
              (fun k => (Fin.append_left _ _ _).trans
                ((Fin.append_left _ _ _).trans
                  (ColKind.rewKinds_lt (is k).isLt))))))
      (QueryGen.GammaTok
        (fun k => (is k).castLE (Nat.le_succ m))
        (fun k => by
          rw [ColKind.rewKinds_lt (is k).isLt]
          exact fun hc => ColKind.noConfusion hc)
        (fun j => (ts j).castToAnnotatedTuple)
        (fun j => (fs j).liftComposite)
        (TermG.provIndex (Fin.last m)
          (ColKind.rewKinds_of_not_lt (lt_irrefl m)))
        (qg.rewritingGen hq)))

/-- Key projections of a grouped result at the annotated level: the data
part restricts to the key columns and the finalized annotation is
unchanged (dropped token columns cash their pending guards). -/
theorem QueryGen.evaluateAnnotatedGen_keyProj {n₁ n₂ : ℕ}
    (X : QueryGen T (n₁ + n₂) (ColKind.gammaKinds n₁ n₂))
    (d : AnnotatedDatabase T K) :
    (QueryGen.Proj
        (fun j : Fin n₁ => ProjCol.term (TermG.index (Fin.castAdd n₂ j)
          (by simp [ColKind.gammaKinds])))
        X).evaluateAnnotatedGen d
      = (X.evaluateAnnotatedGen d).map (fun p =>
          ((fun j => p.fst (Fin.castAdd n₂ j)), p.snd)) := by
  unfold QueryGen.evaluateAnnotatedGen
  simp only [QueryGen.evaluateGen]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun r _ => ?_)
  simp only [Function.comp_apply]
  refine Prod.ext ?_ ?_
  · funext j
    rfl
  · exact GenAnn.finalize_cash _ _ _ Multiset.inter_le_left

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

/-- The gate on a row whose designated column holds a token. -/
theorem TermG.evalRew_cmpAgg_inr {n : ℕ} {κ : Fin n → ColKind}
    (k : Fin n) (hk : κ k = ColKind.agg) (op : CompOp)
    (c : TermG (T ⊕ K) κ) (u : Tuple (GenValue (T ⊕ K) K) n)
    (a : AggValue (T ⊕ K) K) (hu : u k = Sum.inr a) :
    (TermG.cmpAgg k hk op c).evalRew u
      = Sum.inr (a.predProv op (c.evalRew u)) := by
  show (match u k with
    | Sum.inl _ => (Sum.inr 0 : T ⊕ K)
    | Sum.inr a => Sum.inr (a.predProv op (c.evalRew u))) = _
  rw [hu]

/-- **Correctness of the HAVING site rewriting**, relative to the gate
primitive: for a classical subquery, evaluating the annotated fused
`HAVING` site and folding into embedded composite rows agrees with the
rewritten world's evaluation of the rewritten site. -/
theorem QueryGen.havingSiteRew_valid {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (op : CompOp) (l : Fin n₂)
    (s : Term T n₁) (qg : QueryGen T m (ColKind.allReg m))
    (hq : qg.classical) (d : AnnotatedDatabase T K) :
    Multiset.map (fun t : Tuple (T ⊕ K) (n₁ + 1) =>
        ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) (n₁ + 1)))
      ((QueryGen.Proj
          (fun j : Fin n₁ => ProjCol.term (TermG.index (Fin.castAdd n₂ j)
            (by simp [ColKind.gammaKinds])))
          (QueryGen.Sel (GenPred.fusedCmp op l s)
            (QueryGen.Gamma is ts fs qg))).evaluateAnnotatedGen
        d).toComposite
      = (QueryGen.havingSiteRew is ts fs op l s qg hq).evaluateRew
          d.toComposite := by
  rw [QueryGen.evaluateAnnotatedGen_keyProj,
    QueryGen.fused_having_bridge is ts fs op l s qg (qg.strip hq)
      (qg.strip_noAgg hq) d (QueryGen.strip_bridge qg hq d)]
  unfold QueryGen.havingSiteRew QueryGen.retagToRew
  show _ = QueryGen.evaluateRew (QueryGen.Proj _ _) d.toComposite
  simp only [QueryGen.evaluateRew]
  have hR : (qg.rewritingGen hq).evaluateRew d.toComposite
      = Multiset.map (fun t : Tuple (T ⊕ K) (m + 1) =>
          ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) (m + 1)))
        (((qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq)
          d).toComposite) := by
    rw [QueryGen.evaluateRew_plain _
        (QueryGen.rewritingGen_noGammaTok qg hq) _,
      QueryGen.rewritingGen_plain qg hq d.toComposite,
      ← Query.rewriting_valid (qg.strip hq) (qg.strip_noAgg hq) d]
  have har : Multiset.map (fun u => (GenRow.plainTuple u,
        ((TermG.provIndex (Fin.last m)
          (ColKind.rewKinds_of_not_lt (lt_irrefl m))).evalRew u).annPart))
      ((qg.rewritingGen hq).evaluateRew d.toComposite)
    = ((qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq) d).map
        (fun p => ((p.toComposite, p.snd)
          : AnnotatedTuple (T ⊕ K) K (m + 1))) := by
    rw [hR]
    unfold AnnotatedRelation.toComposite
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    refine Prod.ext ?_ ?_
    · funext k
      rfl
    · show (AggValue.collapseSum
          (Sum.inl (p.toComposite (Fin.last m)))).annPart = p.snd
      rw [show p.toComposite (Fin.last m) = Sum.inr p.snd from by
        rw [AnnotatedTuple.toComposite_coord,
          dif_neg (by simp only [Fin.val_last]; omega)]]
      rfl
  rw [har, map_comp_fst_groupByKey]
  simp only [Multiset.map_map]
  rw [show ((Prod.fst
        : AnnotatedTuple (T ⊕ K) K n₁ → Tuple (T ⊕ K) n₁)
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
  unfold Query.evaluateHavingAnnotated AnnotatedRelation.toComposite
  simp only [Multiset.map_map]
  refine Multiset.map_congr ?_ (fun g hg => ?_)
  · rfl
  · simp only [Function.comp_apply]
    funext j
    by_cases hj : (j : ℕ) < n₁
    · rw [dif_pos hj]
      refine Eq.trans (congrArg Sum.inl
        ((AnnotatedTuple.toComposite_coord _ j).trans (dif_pos hj))) ?_
      refine Eq.trans (congrArg (fun v =>
          (Sum.inl (Sum.inl v) : GenValue (T ⊕ K) K))
        (Fin.append_left g
          (fun k => fs k (List.map (fun p => (ts k).eval p.fst)
            (Having.havingGroup is
              ((qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq) d) g)))
          (⟨(j : ℕ), hj⟩ : Fin n₁))) ?_
      symm
      simp only [ProjCol.evalRew, TermG.evalRew]
      rw [Fin.append_left, Fin.append_left]
      rfl
    · rw [dif_neg hj]
      refine Eq.trans (congrArg Sum.inl
        ((AnnotatedTuple.toComposite_coord _ j).trans (dif_neg hj))) ?_
      refine congrArg Sum.inl ?_
      rw [TermG.evalRew_cmpAgg_inr _ _ _ _ _
        (AggValue.ofGroup (fs l).liftComposite
          (ts l).castToAnnotatedTuple
          (Having.havingGroup
            (fun k => (is k).castLE (Nat.le_succ m))
            (Multiset.map (fun p => ((p.toComposite, p.snd)
              : AnnotatedTuple (T ⊕ K) K (m + 1)))
              ((qg.strip hq).evaluateAnnotated (qg.strip_noAgg hq) d))
            (fun k => Sum.inl (g k))))
        ((Fin.append_left _ _ (Fin.natAdd n₁ l)).trans
          (Fin.append_right _ _ l))]
      rw [Term.liftKeys_evalRew _ _ s _ g (fun k =>
        (Fin.append_left _ _ (Fin.castAdd n₂ k)).trans
          (Fin.append_left _ _ k))]
      rw [AggValue.predProv_ofGroup, Having.havingGroup_toComposite,
        Having.havingProv_toComposite]

/-! ## Compositional closure: rewriting queries around HAVING sites

ProvSQL rewrites whole queries in which `GROUP BY … HAVING` blocks occur
as subqueries. The relation below closes the two base rewritings – the
classical rules and the HAVING site – under the classical operators
(mirroring the constructions of `QueryGen.rewritingGen`), and
`QueryGen.havingRewrites_valid` extends the correctness to every query
so obtained. Deduplication and difference *above* a site are not closed
over (they are rarely meaningful over `HAVING` outputs); a site under
them can still be handled by the classical rule when it is itself
classical. -/

/-- Value-kind projection columns strip faithfully. -/
theorem ProjCol.strip_eval {n : ℕ} {κ : Fin n → ColKind} :
    ∀ (p : ProjCol T κ), p.kind = ColKind.reg → ∀ (u : Tuple T n),
      p.strip.eval u = p.evalPlain u
  | .term t, _, u => TermG.strip_eval t u
  | .token _ _, hp, _ => ColKind.noConfusion hp
  | .provTerm _, hp, _ => ColKind.noConfusion hp

/-- One-step-closed rewriting: classical queries and fused `HAVING`
sites rewrite by their base rules, and the classical operators compose
rewritten subqueries exactly as `QueryGen.rewritingGen` does. -/
inductive QueryGen.HavingRewrites :
    {n : ℕ} → {κ : Fin n → ColKind} → QueryGen T n κ →
    QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n) → Prop
  | classical {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (hq : q.classical) :
      HavingRewrites q (q.rewritingGen hq)
  | site {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
      (fs : Tuple (SeqAggFunc T) n₂) (op : CompOp) (l : Fin n₂)
      (s : Term T n₁) (qg : QueryGen T m (ColKind.allReg m))
      (hq : qg.classical) :
      HavingRewrites
        (QueryGen.Proj
          (fun j : Fin n₁ => ProjCol.term (TermG.index (Fin.castAdd n₂ j)
            (by simp [ColKind.gammaKinds])))
          (QueryGen.Sel (GenPred.fusedCmp op l s)
            (QueryGen.Gamma is ts fs qg)))
        (QueryGen.havingSiteRew is ts fs op l s qg hq)
  | sum {n : ℕ} {κ : Fin n → ColKind} {q₁ q₂ : QueryGen T n κ}
      {q₁' q₂' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n)} :
      HavingRewrites q₁ q₁' → HavingRewrites q₂ q₂' →
      HavingRewrites (QueryGen.Sum q₁ q₂) (QueryGen.Sum q₁' q₂')
  | sel {n : ℕ} {κ : Fin n → ColKind} {q : QueryGen T n κ}
      {q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n)}
      (φ : GenPred T κ) (hφ : φ.hasAggAtom = false)
      (hκ : ∀ k, κ k = ColKind.reg) :
      HavingRewrites q q' →
      HavingRewrites (QueryGen.Sel φ q)
        (QueryGen.Sel (φ.castComposite hκ hφ) q')
  | proj {n m : ℕ} {κ : Fin n → ColKind} {q : QueryGen T n κ}
      {q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n)}
      (ps : Tuple (ProjCol T κ) m)
      (hps : ∀ j, (ps j).kind = ColKind.reg)
      (hκ : ∀ k, κ k = ColKind.reg) :
      HavingRewrites q q' →
      HavingRewrites (QueryGen.Proj ps q)
        (QueryGen.retagToRew
          (fun j => by
            by_cases hj : (j : ℕ) < m
            · rw [dif_pos hj, ProjCol.castComposite_kind]
              rfl
            · rw [dif_neg hj]
              rfl)
          (QueryGen.Proj
            (fun j : Fin (m + 1) =>
              if hj : (j : ℕ) < m then
                (ps ⟨j, hj⟩).castComposite hκ (hps ⟨j, hj⟩)
              else
                ProjCol.provTerm (TermG.provIndex (Fin.last n)
                  (ColKind.rewKinds_of_not_lt (lt_irrefl n))))
            q'))
  | prod {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
      {q₁ : QueryGen T n₁ κ₁} {q₂ : QueryGen T n₂ κ₂}
      {q₁' : QueryGen (T ⊕ K) (n₁ + 1) (ColKind.rewKinds n₁)}
      {q₂' : QueryGen (T ⊕ K) (n₂ + 1) (ColKind.rewKinds n₂)} :
      HavingRewrites q₁ q₁' → HavingRewrites q₂ q₂' →
      HavingRewrites (QueryGen.Prod q₁ q₂)
        (QueryGen.retagToRew
          (fun j => by
            by_cases h₁ : (j : ℕ) < n₁
            · rw [dif_pos h₁]; rfl
            · rw [dif_neg h₁]
              by_cases h₂ : (j : ℕ) < n₁ + n₂
              · rw [dif_pos h₂]; rfl
              · rw [dif_neg h₂]; rfl)
          (QueryGen.Proj
            (fun j : Fin (n₁ + n₂ + 1) =>
              if h₁ : (j : ℕ) < n₁ then
                ProjCol.term (TermG.index
                  (Fin.castAdd (n₂ + 1)
                    (⟨j, Nat.lt_succ_of_lt h₁⟩ : Fin (n₁ + 1)))
                  ((Fin.append_left _ _ _).trans (ColKind.rewKinds_lt h₁)))
              else if h₂ : (j : ℕ) < n₁ + n₂ then
                ProjCol.term (TermG.index
                  (Fin.natAdd (n₁ + 1)
                    (⟨(j : ℕ) - n₁, by omega⟩ : Fin (n₂ + 1)))
                  ((Fin.append_right _ _ _).trans
                    (ColKind.rewKinds_lt (by simp; omega))))
              else
                ProjCol.provTerm (TermG.mul
                  (TermG.provIndex (Fin.castAdd (n₂ + 1) (Fin.last n₁))
                    ((Fin.append_left _ _ _).trans
                      (ColKind.rewKinds_of_not_lt (lt_irrefl n₁))))
                  (TermG.provIndex (Fin.natAdd (n₁ + 1) (Fin.last n₂))
                    ((Fin.append_right _ _ _).trans
                      (ColKind.rewKinds_of_not_lt (lt_irrefl n₂))))))
            (QueryGen.Prod q₁' q₂')))

/-- **Whole-query correctness of the compositional HAVING rewriting**:
along the closure, the annotated general semantics folded into embedded
composite rows agrees with the rewritten world's evaluation. -/
theorem QueryGen.havingRewrites_valid {n : ℕ} {κ : Fin n → ColKind}
    {q : QueryGen T n κ}
    {q' : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n)}
    (h : QueryGen.HavingRewrites q q') (d : AnnotatedDatabase T K) :
    Multiset.map (fun t : Tuple (T ⊕ K) (n + 1) =>
        ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) (n + 1)))
      ((q.evaluateAnnotatedGen d).toComposite)
      = q'.evaluateRew d.toComposite := by
  induction h with
  | classical q hq =>
    rw [QueryGen.rewritingGen_valid q hq d,
      QueryGen.evaluateRew_plain _ (QueryGen.rewritingGen_noGammaTok q hq)]
  | site is ts fs op l s qg hq =>
    exact QueryGen.havingSiteRew_valid is ts fs op l s qg hq d
  | sum h₁ h₂ ih₁ ih₂ =>
    show Multiset.map _ ((AnnotatedRelation.toComposite
      (QueryGen.evaluateAnnotatedGen _ d))) = _
    unfold QueryGen.evaluateAnnotatedGen
    simp only [QueryGen.evaluateGen, QueryGen.evaluateRew]
    rw [Multiset.map_add, AnnotatedRelation.toComposite_add,
      Multiset.map_add]
    exact congrArg₂ (· + ·) ih₁ ih₂
  | sel φ hφ hκ h ih =>
    show Multiset.map _ ((QueryGen.evaluateAnnotatedGen _ d).toComposite)
      = QueryGen.evaluateRew _ _
    simp only [QueryGen.evaluateRew]
    rw [← ih]
    unfold QueryGen.evaluateAnnotatedGen AnnotatedRelation.toComposite
    simp only [QueryGen.evaluateGen]
    rw [if_neg (by simp [hφ])]
    rw [Multiset.filter_map, Multiset.filter_map, Multiset.filter_map]
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map,
      Multiset.map_map]
    refine congrArg _ (Multiset.filter_congr (fun r _ => ?_)).symm
    refine Iff.trans (GenPred.holdsRew_inl _ _) ?_
    refine Iff.trans (GenPred.castComposite_holdsPlain hκ φ hφ _) ?_
    refine Iff.trans (iff_of_eq
      (Selection.castToAnnotatedTuple_eval φ.strip
        (GenRow.plainTuple r.fst) r.snd.finalize)) ?_
    exact Iff.trans (GenPred.strip_eval φ hφ _)
      (GenPred.holds_iff_holdsPlain φ r.fst).symm
  | @proj n m κ q q' ps hps hκ h ih =>
    show Multiset.map _ ((QueryGen.evaluateAnnotatedGen _ d).toComposite)
      = QueryGen.evaluateRew _ _
    unfold QueryGen.retagToRew
    show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) _
    simp only [QueryGen.evaluateRew]
    rw [← ih]
    unfold QueryGen.evaluateAnnotatedGen AnnotatedRelation.toComposite
    simp only [QueryGen.evaluateGen]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun r _ => ?_)
    simp only [Function.comp_apply]
    funext j
    by_cases hj : (j : ℕ) < m
    · rw [dif_pos hj]
      refine Eq.trans (congrArg Sum.inl
        ((AnnotatedTuple.toComposite_coord _ j).trans (dif_pos hj))) ?_
      refine Eq.trans (congrArg (fun v => (Sum.inl (Sum.inl v)
          : GenValue (T ⊕ K) K))
        (ProjCol.collapseSum_eval (ps ⟨(j : ℕ), hj⟩) r.fst)) ?_
      refine Eq.symm ?_
      refine Eq.trans (ProjCol.evalRew_inl _ _) ?_
      refine congrArg Sum.inl ?_
      refine Eq.trans (ProjCol.castComposite_evalPlain hκ _ (hps _) _) ?_
      refine Eq.trans (Term.castToAnnotatedTuple_eval _ _ _) ?_
      exact congrArg Sum.inl (ProjCol.strip_eval _ (hps _) _)
    · rw [dif_neg hj]
      refine Eq.trans (congrArg Sum.inl
        ((AnnotatedTuple.toComposite_coord _ j).trans (dif_neg hj))) ?_
      refine Eq.trans (congrArg (fun v => (Sum.inl (Sum.inr v)
          : GenValue (T ⊕ K) K))
        (GenAnn.finalize_cash _ _ _ Multiset.inter_le_left)) ?_
      refine Eq.symm ?_
      refine Eq.trans (ProjCol.evalRew_inl _ _) ?_
      refine congrArg Sum.inl ?_
      exact (AnnotatedTuple.toComposite_coord _ _).trans
        (dif_neg (by simp only [Fin.val_last]; omega))
  | @prod n₁ n₂ κ₁ κ₂ q₁ q₂ q₁' q₂' h₁ h₂ ih₁ ih₂ =>
    show Multiset.map _ ((QueryGen.evaluateAnnotatedGen _ d).toComposite)
      = QueryGen.evaluateRew _ _
    unfold QueryGen.retagToRew
    show _ = QueryGen.evaluateRew (QueryGen.Retag _ _) _
    simp only [QueryGen.evaluateRew]
    rw [← ih₁, ← ih₂]
    unfold QueryGen.evaluateAnnotatedGen AnnotatedRelation.toComposite
    simp only [QueryGen.evaluateGen]
    simp only [Multiset.map_map]
    rw [Multiset.map_product_map]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun xy _ => ?_)
    simp only [Function.comp_apply, Prod.map]
    funext j
    by_cases hj₁ : (j : ℕ) < n₁
    · rw [dif_pos hj₁]
      refine Eq.trans (congrArg Sum.inl
        ((AnnotatedTuple.toComposite_coord _ j).trans
          (dif_pos (show (j : ℕ) < n₁ + n₂ by omega)))) ?_
      refine Eq.trans (congrArg (fun v => (Sum.inl (Sum.inl
          (AggValue.collapseSum v)) : GenValue (T ⊕ K) K))
        ((congrArg (Fin.append xy.1.fst xy.2.fst)
          (Fin.ext rfl : (⟨(j : ℕ), by omega⟩ : Fin (n₁ + n₂))
            = Fin.castAdd n₂ (⟨(j : ℕ), hj₁⟩ : Fin n₁))).trans
          (Fin.append_left xy.1.fst xy.2.fst
            (⟨(j : ℕ), hj₁⟩ : Fin n₁)))) ?_
      refine Eq.symm ?_
      show Sum.inl (AggValue.collapseSum (Fin.append _ _
        (Fin.castAdd (n₂ + 1)
          (⟨(j : ℕ), Nat.lt_succ_of_lt hj₁⟩ : Fin (n₁ + 1))))) = _
      rw [Fin.append_left]
      exact congrArg Sum.inl
        ((AnnotatedTuple.toComposite_coord _ _).trans (dif_pos hj₁))
    · rw [dif_neg hj₁]
      by_cases hj₂ : (j : ℕ) < n₁ + n₂
      · rw [dif_pos hj₂]
        refine Eq.trans (congrArg Sum.inl
          ((AnnotatedTuple.toComposite_coord _ j).trans
            (dif_pos hj₂))) ?_
        refine Eq.trans (congrArg (fun v => (Sum.inl (Sum.inl
            (AggValue.collapseSum v)) : GenValue (T ⊕ K) K))
          ((congrArg (Fin.append xy.1.fst xy.2.fst)
            (Fin.ext (by
              simp only [Fin.val_natAdd]
              omega) : (⟨(j : ℕ), by omega⟩ : Fin (n₁ + n₂))
              = Fin.natAdd n₁ (⟨(j : ℕ) - n₁, by omega⟩ : Fin n₂))).trans
            (Fin.append_right xy.1.fst xy.2.fst
              (⟨(j : ℕ) - n₁, by omega⟩ : Fin n₂)))) ?_
        refine Eq.symm ?_
        show Sum.inl (AggValue.collapseSum (Fin.append _ _
          (Fin.natAdd (n₁ + 1)
            (⟨(j : ℕ) - n₁, by omega⟩ : Fin (n₂ + 1))))) = _
        rw [Fin.append_right]
        exact congrArg Sum.inl
          ((AnnotatedTuple.toComposite_coord _ _).trans
            (dif_pos (by show LT.lt ((j : ℕ) - n₁) n₂; omega)))
      · rw [dif_neg hj₂]
        refine Eq.trans (congrArg Sum.inl
          ((AnnotatedTuple.toComposite_coord _ j).trans
            (dif_neg hj₂))) ?_
        refine Eq.trans (congrArg (fun v => (Sum.inl (Sum.inr v)
            : GenValue (T ⊕ K) K))
          (GenAnn.finalize_prod _ _ _ _)) ?_
        refine Eq.symm ?_
        show Sum.inl (TermG.evalRew _ _ * TermG.evalRew _ _) = _
        rw [show TermG.evalRew (TermG.provIndex
              (Fin.castAdd (n₂ + 1) (Fin.last n₁))
              ((Fin.append_left _ _ _).trans
                (ColKind.rewKinds_of_not_lt (lt_irrefl n₁)))) _
            = (Sum.inr (GenRow.toAnnotated xy.1).snd : T ⊕ K) from by
          show AggValue.collapseSum (Fin.append _ _
            (Fin.castAdd (n₂ + 1) (Fin.last n₁))) = _
          rw [Fin.append_left]
          exact congrArg AggValue.collapseSum
            (congrArg Sum.inl ((AnnotatedTuple.toComposite_coord _ _).trans
              (dif_neg (by simp only [Fin.val_last]; omega)))) |>.trans rfl]
        rw [show TermG.evalRew (TermG.provIndex
              (Fin.natAdd (n₁ + 1) (Fin.last n₂))
              ((Fin.append_right _ _ _).trans
                (ColKind.rewKinds_of_not_lt (lt_irrefl n₂)))) _
            = (Sum.inr (GenRow.toAnnotated xy.2).snd : T ⊕ K) from by
          show AggValue.collapseSum (Fin.append _ _
            (Fin.natAdd (n₁ + 1) (Fin.last n₂))) = _
          rw [Fin.append_right]
          exact congrArg AggValue.collapseSum
            (congrArg Sum.inl ((AnnotatedTuple.toComposite_coord _ _).trans
              (dif_neg (by simp only [Fin.val_last]; omega)))) |>.trans rfl]
        rfl
