import Provenance.AggQueryRewritingValid
import Provenance.AggQueryBridges

/-! # The rewritten world's evaluator: tokens as ordinary column values

ProvSQL evaluates rewritten plans over a value universe that contains,
next to the regular values and the provenance identifiers, the aggregate
tokens produced by its `provsql_agg` gate; the `provsql_having` gate then
reads a token and produces the predicate provenance of an aggregate
comparison. The formal counterpart is the evaluator `AggQueryIn.evaluateRew`
defined here: it runs a rewritten query (a `AggQuery` over the composite
value type `T ⊕ K`) over rows `Tuple (GenValue (T ⊕ K) K) n` – the
lifted-column carrier of the general evaluator, instantiated at the
composite value type – with the kind vector saying which columns hold
tokens.

* On the value-kinded operators the evaluator is the plain semantics
  through the `inl` embedding (`Dedup`, `Diff` and `Gamma` collapse their
  statically all-regular rows to plain tuples, exactly as the general
  evaluator reads them through `GenRow.toAnnotated`).
* `AggQueryIn.GammaTok` builds tokens: one `AggValue.ofGroup` per
  `(term, aggregate)` pair over the group's occurrence sequence, whose
  annotations are the values of the explicit annotation term – in
  rewritten plans, the provenance column of the subquery – and writes the
  group-existence guard `δ(⊕ occs)` into its `prov` output column.
* `TermGIn.cmpAgg` is the cmp gate: `TermGIn.evalRew` interprets it by
  `AggValue.predProvOf`, the primitive the rewriting's correctness is
  stated against, faithfully to ProvSQL's own gate-relative correctness.
* `TermGIn.chiGate` is the indicator gate a `HAVING` predicate needs for
  its *regular* atoms: `TermGIn.evalRew` interprets it by `Having.chi`,
  the characteristic value `predsem` gives such an atom. Having no kind
  constraint to keep it off plain columns, it is what
  `AggQueryIn.chiFree` excludes below.

The rewriting rules built on this evaluator live downstream:
`Provenance.AggQueryGroupRewriting` (the bare grouping and the `HAVING`
site) and `Provenance.AggQueryClosure` (the compositional closure).
-/

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K]
  [DecidableEq K] [HasAltLinearOrder K]

/-! ## Terms and predicates in the rewritten world -/

/-- The annotation part of a composite value (`𝟘` on data values: a
malformed provenance read carries no worlds). -/
def Sum.annPart : T ⊕ K → K
  | Sum.inl _ => 0
  | Sum.inr k => k

/-- Term evaluation in the rewritten world: as `TermGIn.eval` on the
value-reading constructors, with the `cmpAgg` gate interpreted by the
predicate provenance of the token against the comparison term, and the
`chiGate` gate by the characteristic value of its comparison. -/
def TermGIn.evalRew {c n : ℕ} {κ : Fin n → ColKind} :
    TermGIn (T ⊕ K) c κ → Tuple (GenValue (T ⊕ K) K) n →
    (γ : Fin c → (T ⊕ K) := fun _ => 0) → T ⊕ K
  | .const a, _, _ => a
  | .outer k, _, γ => γ k
  | .index k _, u, _ => AggValue.collapseSum (u k)
  | .provIndex k _, u, _ => AggValue.collapseSum (u k)
  | .cmpAgg k _ op c, u, γ =>
    match u k with
    | Sum.inl _ => Sum.inr 0
    | Sum.inr a => Sum.inr (a.predProvOf op (c.evalRew u γ))
  | .chiGate op t₁ t₂, u, γ =>
    Sum.inr (Having.chi op (t₁.evalRew u γ) (t₂.evalRew u γ))
  | .add t₁ t₂, u, γ => t₁.evalRew u γ + t₂.evalRew u γ
  | .sub t₁ t₂, u, γ => t₁.evalRew u γ - t₂.evalRew u γ
  | .mul t₁ t₂, u, γ => t₁.evalRew u γ * t₂.evalRew u γ
  | .caseWhen op t₁ t₂ t₃ t₄, u, γ =>
    if op.eval3 (t₁.evalRew u γ) (t₂.evalRew u γ) = Kleene.true
    then t₃.evalRew u γ else t₄.evalRew u γ
  | .coalesce t₁ t₂, u, γ =>
    if ValueType.isNull (t₁.evalRew u γ) then t₂.evalRew u γ
    else t₁.evalRew u γ

/-- Projection-column evaluation in the rewritten world. -/
def ProjColIn.evalRew {c n : ℕ} {κ : Fin n → ColKind}
    (p : ProjColIn (T ⊕ K) c κ) (u : Tuple (GenValue (T ⊕ K) K) n)
    (γ : Fin c → (T ⊕ K) := fun _ => 0) : GenValue (T ⊕ K) K :=
  match p with
  | .term t => Sum.inl (t.evalRew u γ)
  | .token k _ => u k
  | .aggTerm k _ gf => Sum.map gf (AggTok.postcomp gf) (u k)
  | .provTerm t => Sum.inl (t.evalRew u γ)

/-- Three-valued evaluation of a predicate in the rewritten world (compared
tokens read through their deterministic collapse, as in
`GenPredIn.eval3`). -/
def GenPredIn.evalRew3 {c n : ℕ} {κ : Fin n → ColKind} :
    GenPredIn (T ⊕ K) c κ → Tuple (GenValue (T ⊕ K) K) n →
    (γ : Fin c → (T ⊕ K) := fun _ => 0) → Kleene
  | .cmp op t₁ t₂, u, γ => op.eval3 (t₁.evalRew u γ) (t₂.evalRew u γ)
  | .aggCmp k _ op t, u, γ =>
      op.eval3 (AggValue.collapseSum (u k)) (t.evalRew u γ)
  | .aggRange k _ op₁ t₁ op₂ t₂, u, γ =>
      (op₁.eval3 (AggValue.collapseSum (u k)) (t₁.evalRew u γ)).and
        (op₂.eval3 (AggValue.collapseSum (u k)) (t₂.evalRew u γ))
  | .and φ ψ, u, γ => (φ.evalRew3 u γ).and (ψ.evalRew3 u γ)
  | .or φ ψ, u, γ => (φ.evalRew3 u γ).or (ψ.evalRew3 u γ)
  | .not φ, u, γ => (φ.evalRew3 u γ).not

/-- The rows a selection keeps in the rewritten world: those on which the
predicate is *true*. -/
def GenPredIn.holdsRew {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn (T ⊕ K) c κ) (u : Tuple (GenValue (T ⊕ K) K) n)
    (γ : Fin c → (T ⊕ K) := fun _ => 0) : Prop :=
  φ.evalRew3 u γ = Kleene.true

/-- Structural decidability of `holdsRew`. -/
def GenPredIn.decHoldsRew {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn (T ⊕ K) c κ) (u : Tuple (GenValue (T ⊕ K) K) n)
    (γ : Fin c → (T ⊕ K) := fun _ => 0) : Decidable (φ.holdsRew u γ) :=
  inferInstanceAs (Decidable (_ = _))

instance GenPredIn.instDecidableHoldsRew {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn (T ⊕ K) c κ) (γ : Fin c → (T ⊕ K))
    (u : Tuple (GenValue (T ⊕ K) K) n) : Decidable (φ.holdsRew u γ) :=
  φ.decHoldsRew u γ

/-- **The reading a one-leaf expression of the rewritten world carries**:
the leaf's value, normalized through the data arm.

Every aggregate the rewriting emits is data-valued, being lifted from the
source's (`SeqAggFunc.liftComposite`), so the normalization is a no-op on
what actually arises. What it buys is that the column is the composite
transport of the source's *on the nose*: `AggExpr.toComposite` lifts an
expression's own function the same way, and a bare projection would read
alike but not be the same data. -/
def AggExprFun.projComposite : (Fin 1 → T ⊕ K) → T ⊕ K :=
  fun v => Sum.inl (Sum.elim id (fun _ => (0 : T)) (v 0))

/-- **A filtered aggregate of a group, in the rewritten world**: the
expression `AggQueryIn.GammaTok` builds for an aggregate carrying a
`FILTER` clause – one leaf over the whole group, the clause cutting only
what it reads – with the reading the composite transport carries. -/
def AggExpr.ofGroupWhenRew {c m : ℕ} (f : SeqAggFunc (T ⊕ K))
    (t : TermIn (T ⊕ K) c m) (keep : Tuple (T ⊕ K) m → Bool)
    (U : List (AnnotatedTuple (T ⊕ K) K m))
    (γ : Fin c → T ⊕ K := fun _ => 0) : AggExpr (T ⊕ K) K :=
  { AggExpr.ofGroupWhen f t keep U γ with
    g := AggExprFun.projComposite (T := T) (K := K) }

/-! ## The evaluator -/

/-- **The rewritten world's evaluator**: plain multiset semantics over
token-bearing rows. Value-kinded operators act through the `inl`
embedding; `GammaTok` builds tokens and the group guard; the gates
inside terms are interpreted by `predProvOf` and `Having.chi`. -/
def AggQueryIn.evaluateRew : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn (T ⊕ K) c n κ → Database (T ⊕ K) →
    (γ : Fin c → (T ⊕ K) := fun _ => 0) →
    Multiset (Tuple (GenValue (T ⊕ K) K) n)
  | _, n, _, .Rel _ s, D, _ =>
    match D.find n s with
    | none => 0
    | some rn => rn.map (fun t =>
        ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) n))
  | _, _, _, .Proj ps q, D, γ =>
    (q.evaluateRew D γ).map (fun u => (fun j => (ps j).evalRew u γ))
  | _, _, _, .Sel φ q, D, γ =>
    (q.evaluateRew D γ).filter (fun u => φ.holdsRew u γ)
  -- an aggregate column read as a key is not a rewritten-world
  -- operator: the rewritten plan cannot enumerate a token's values, and
  -- on plain rows there is one alternative, so it is the identity here
  | _, _, _, .Alt _ _ q, D, γ => q.evaluateRew D γ
  | _, _, _, .Mu b s q₀ q₁, D, γ =>
    -- the rounds are relations of the rewritten schema, so each round is
    -- read back through the collapse that `Rel` embeds
    (muSum (fun X : Relation (T ⊕ K) _ =>
        (q₁.evaluateRew (D.assign s X) γ).map
          (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))) b
      ((q₀.evaluateRew D γ).map
        (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _)))).map
      (fun t => ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) _))
  | _, _, _, .MuSet b s q₀ q₁, D, γ =>
    (muIter (fun X : Relation (T ⊕ K) _ =>
      (((q₀.evaluateRew (D.assign s X) γ).map
          (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))
        + (q₁.evaluateRew (D.assign s X) γ).map
            (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))).dedup)) b).map
      (fun t => ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) _))
  | _, _, _, .Prod q₁ q₂, D, γ =>
    ((q₁.evaluateRew D γ).product (q₂.evaluateRew D γ)).map
      (fun (x, y) => Fin.append x y)
  | _, _, _, @AggQueryIn.Apply _ _ n₁ _ _ q₁ q₂, D, γ =>
    (q₁.evaluateRew D γ).bind (fun u =>
      (q₂.evaluateRew D
          (Fin.append (fun k => AggValue.collapseSum (u k)) γ)).map
        (fun v => (Fin.append u v : Tuple (GenValue (T ⊕ K) K) (n₁ + _))))
  | _, _, _, .Sum q₁ q₂, D, γ => q₁.evaluateRew D γ + q₂.evaluateRew D γ
  | _, _, _, .Dedup q, D, γ =>
    (((q.evaluateRew D γ).map
        (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))).dedup).map
      (fun t => (fun k => Sum.inl (t k)))
  | _, _, _, .Diff q₁ q₂, D, γ =>
    let r₂ := (q₂.evaluateRew D γ).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))
    ((((q₁.evaluateRew D γ).map
        (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) _))).filter
      (fun t => t ∉ r₂)).map (fun t => (fun k => Sum.inl (t k))))
  | _, _, _, @AggQueryIn.Gamma _ _ m n₁ n₂ is ts fs q keep, D, γ =>
    let r : Relation (T ⊕ K) m := (q.evaluateRew D γ).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) m))
    let keys := (r.map
      (fun u => (fun k => u (is k) : Tuple (T ⊕ K) n₁))).dedup
    -- a `FILTER` clause cuts what the aggregate reads, here as in the
    -- plain semantics: the clause of a query of the rewritten world is
    -- already a selection over the composite domain
    keys.map (fun g => (fun k => Sum.inl (Fin.append g
      (fun j => (fs j)
        ((Relation.groupSeqOpt is r g (keep j)).map
          (fun v => (ts j).eval v γ))) k)))
  | _, _, _, @AggQueryIn.GammaScalar _ _ m n₂ ts fs q, D, γ =>
    let r : Relation (T ⊕ K) m := (q.evaluateRew D γ).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) m))
    (Multiset.ofList [(fun j => Sum.inl ((fs j)
      ((Relation.groupSeq (fun k : Fin 0 => k.elim0) r
        (fun k : Fin 0 => k.elim0)).map (fun v => (ts j).eval v γ)))
      : Tuple (GenValue (T ⊕ K) K) n₂)])
  | _, _, _, @AggQueryIn.GammaNest _ _ m n₁ _κ is _his p f q, D, γ =>
    -- second-level aggregation is not rewritten: as for a grouping, the
    -- rewritten world reads it through the plain semantics of the
    -- composite domain
    let r : Relation (T ⊕ K) m := (q.evaluateRew D γ).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) m))
    let key : Tuple (T ⊕ K) m → Tuple (T ⊕ K) n₁ := fun u => fun k => u (is k)
    ((r.map key).dedup).map (fun g =>
      (fun k => Sum.inl (Fin.append g (fun _ : Fin 1 =>
        f ((r.filter (fun u => key u = g)).map
          (fun u => p.evalPlain u γ))) k)))
  | _, _, _, @AggQueryIn.Win _ _ n' _m' _p' P O o w t f q dist keep, D, γ =>
    let r : Relation (T ⊕ K) n' := (q.evaluateRew D γ).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) n'))
    r.map (fun u : Tuple (T ⊕ K) n' =>
      ((fun k => Sum.inl ((Fin.snoc u (ValueFrame.windowValueOpt P O o w t
            (if dist then f.distinct else f) keep r u γ)
          : Tuple (T ⊕ K) (n' + 1)) k))
        : Tuple (GenValue (T ⊕ K) K) (n' + 1)))
  | _, _, _, @AggQueryIn.WinExpr _ _ n' _m' _p' _na P O o ws ts fs g q keeps, D, γ =>
    let r : Relation (T ⊕ K) n' := (q.evaluateRew D γ).map
      (fun u => (GenRow.plainTuple u : Tuple (T ⊕ K) n'))
    r.map (fun u : Tuple (T ⊕ K) n' =>
      ((fun k => Sum.inl ((Fin.snoc u
            (g (fun l => ValueFrame.windowValueOpt P O o (ws l) (ts l)
              (fs l) (keeps l) r u γ))
          : Tuple (T ⊕ K) (n' + 1)) k))
        : Tuple (GenValue (T ⊕ K) K) (n' + 1)))
  | _, _, _, .Retag _ q, D, γ => q.evaluateRew D γ
  | _, _, _, @AggQueryIn.ProvSum _ _ _m n₁ _κ is _his t q, D, γ =>
    let r := q.evaluateRew D γ
    let keys := (r.map
      (fun u => (fun k => GenRow.plainTuple u (is k)
        : Tuple (T ⊕ K) n₁))).dedup
    keys.map (fun g =>
      Fin.append (fun k => (Sum.inl (g k) : GenValue (T ⊕ K) K))
        (fun _ : Fin 1 => Sum.inl
          (((r.filter (fun u => ∀ k' : Fin n₁,
              GenRow.plainTuple u (is k') = g k')).map
            (fun u => t.evalRew u γ)).fold addFn 0)))
  | _, _, _, @AggQueryIn.GammaTok _ _ m n₁ n₂ _κ is _his ts fs a q keep, D, γ =>
    let r := q.evaluateRew D γ
    let ar : AnnotatedRelation (T ⊕ K) K m :=
      r.map (fun u => (GenRow.plainTuple u, (a.evalRew u γ).annPart))
    (Multiset.ofList (groupByKey (ar.map (fun p =>
        ((fun k => p.fst (is k), p.snd)
          : AnnotatedTuple (T ⊕ K) K n₁)))).val).map
      ((fun g : Tuple (T ⊕ K) n₁ =>
        Fin.append
          (Fin.append (fun k => (Sum.inl (g k) : GenValue (T ⊕ K) K))
            -- a `FILTER` on one of the aggregates makes its column an
            -- expression over the whole group, as under `Gamma`
            (fun j => Sum.inr (match keep j with
              | none => AggTok.tok (AggValue.ofGroup (fs j) (ts j)
                  (Having.havingGroup is ar g) γ)
              | some φ => AggTok.expr (AggExpr.ofGroupWhenRew (T := T) (fs j)
                  (ts j) φ.keeps (Having.havingGroup is ar g) γ))))
          (fun _ : Fin 1 => Sum.inl
            (Sum.inr (SemiringWithMonus.delta
              ((Having.havingGroup is ar g).map Prod.snd).sum))))
        ∘ Prod.fst)

/-! ## Agreement with the plain semantics off the gates -/

/-- No token-building grouping: together with gate-freeness, this cuts
out the fragment on which the rewritten world's evaluator is the plain
semantics through the `inl` embedding. -/
def AggQueryIn.noGammaTok {T' : Type} : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T' c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Proj _ q => q.noGammaTok
  | _, _, _, .Sel _ q => q.noGammaTok
  | _, _, _, .Prod q₁ q₂ => q₁.noGammaTok ∧ q₂.noGammaTok
  | _, _, _, .Apply q₁ q₂ => q₁.noGammaTok ∧ q₂.noGammaTok
  | _, _, _, .Sum q₁ q₂ => q₁.noGammaTok ∧ q₂.noGammaTok
  | _, _, _, .Dedup q => q.noGammaTok
  | _, _, _, .Diff q₁ q₂ => q₁.noGammaTok ∧ q₂.noGammaTok
  | _, _, _, .Alt _ _ q => q.noGammaTok
  | _, _, _, .Mu _ _ q₀ q₁ => q₀.noGammaTok ∧ q₁.noGammaTok
  | _, _, _, .MuSet _ _ q₀ q₁ => q₀.noGammaTok ∧ q₁.noGammaTok
  | _, _, _, .Gamma _ _ _ q _ => q.noGammaTok
  | _, _, _, .GammaScalar _ _ q => q.noGammaTok
  | _, _, _, .GammaNest _ _ _ _ q => q.noGammaTok
  | _, _, _, .ProvSum _ _ _ q => q.noGammaTok
  | _, _, _, .Retag _ q => q.noGammaTok
  | _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  | _, _, _, .Win _ _ _ _ _ _ q _ _ => q.noGammaTok
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.noGammaTok

/-- No indicator gate anywhere in a query's terms and predicates. -/
def AggQueryIn.chiFree {T' : Type} : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T' c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Proj ps q => (∀ j, (ps j).chiFree) ∧ q.chiFree
  | _, _, _, .Sel φ q => φ.chiFree ∧ q.chiFree
  | _, _, _, .Prod q₁ q₂ => q₁.chiFree ∧ q₂.chiFree
  | _, _, _, .Apply q₁ q₂ => q₁.chiFree ∧ q₂.chiFree
  | _, _, _, .Sum q₁ q₂ => q₁.chiFree ∧ q₂.chiFree
  | _, _, _, .Dedup q => q.chiFree
  | _, _, _, .Diff q₁ q₂ => q₁.chiFree ∧ q₂.chiFree
  | _, _, _, .Alt _ _ q => q.chiFree
  | _, _, _, .Mu _ _ q₀ q₁ => q₀.chiFree ∧ q₁.chiFree
  | _, _, _, .MuSet _ _ q₀ q₁ => q₀.chiFree ∧ q₁.chiFree
  | _, _, _, .Gamma _ _ _ q _ => q.chiFree
  | _, _, _, .GammaScalar _ _ q => q.chiFree
  | _, _, _, .GammaNest _ _ p _ q => p.chiFree ∧ q.chiFree
  | _, _, _, .ProvSum _ _ t q => t.chiFree ∧ q.chiFree
  | _, _, _, .Retag _ q => q.chiFree
  | _, _, _, .GammaTok _ _ _ _ a q _ => a.chiFree ∧ q.chiFree
  | _, _, _, .Win _ _ _ _ _ _ q _ _ => q.chiFree
  | _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.chiFree

/-- On `inl`-embedded rows a gate-free term evaluates in the rewritten
world as its plain evaluation – including the `cmpAgg` gate, whose junk
reading `𝟘` is definitionally the composite zero on a row with no
token. The indicator gate has no such escape: it returns a genuine
annotation, which is why it is excluded here. -/
theorem TermGIn.evalRew_inl {c n : ℕ} {κ : Fin n → ColKind}
    {γ : Fin c → (T ⊕ K)} :
    ∀ (t : TermGIn (T ⊕ K) c κ), t.chiFree → ∀ (u : Tuple (T ⊕ K) n),
      t.evalRew (fun k => Sum.inl (u k)) γ = t.evalPlain u γ
  | .const _, _, _ => rfl
  | .outer _, _, _ => rfl
  | .index _ _, _, _ => rfl
  | .provIndex _ _, _, _ => rfl
  | .cmpAgg _ _ _ _, _, _ => rfl
  | .chiGate _ _ _, ht, _ => ht.elim
  | .add t₁ t₂, ht, u => by
    show _ + _ = _ + _
    rw [evalRew_inl t₁ ht.1 u, evalRew_inl t₂ ht.2 u]
  | .sub t₁ t₂, ht, u => by
    show HSub.hSub _ _ = HSub.hSub _ _
    rw [evalRew_inl t₁ ht.1 u, evalRew_inl t₂ ht.2 u]
  | .mul t₁ t₂, ht, u => by
    show _ * _ = _ * _
    rw [evalRew_inl t₁ ht.1 u, evalRew_inl t₂ ht.2 u]
  | .caseWhen op t₁ t₂ t₃ t₄, ht, u => by
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [evalRew_inl t₁ ht.1 u, evalRew_inl t₂ ht.2.1 u,
      evalRew_inl t₃ ht.2.2.1 u, evalRew_inl t₄ ht.2.2.2 u]
    rfl
  | .coalesce t₁ t₂, ht, u => by
    show (if ValueType.isNull _ then _ else _) = _
    rw [evalRew_inl t₁ ht.1 u, evalRew_inl t₂ ht.2 u]
    rfl

/-- Gate-free projection columns on `inl`-embedded rows evaluate to the
embedded plain reading. -/
theorem ProjColIn.evalRew_inl {c n : ℕ} {κ : Fin n → ColKind}
    {γ : Fin c → (T ⊕ K)} (p : ProjColIn (T ⊕ K) c κ) (hp : p.chiFree)
    (u : Tuple (T ⊕ K) n) :
    p.evalRew (fun k => Sum.inl (u k)) γ = Sum.inl (p.evalPlain u γ) := by
  cases p with
  | term t => exact congrArg Sum.inl (t.evalRew_inl hp u)
  | token k h => rfl
  | aggTerm k h gf => rfl
  | provTerm t => exact congrArg Sum.inl (t.evalRew_inl hp u)

/-- Gate-free predicates on `inl`-embedded rows hold as their plain
reading. -/
theorem GenPredIn.evalRew3_inl {c n : ℕ} {κ : Fin n → ColKind}
    {γ : Fin c → (T ⊕ K)} :
    ∀ (φ : GenPredIn (T ⊕ K) c κ), φ.chiFree → ∀ (u : Tuple (T ⊕ K) n),
      φ.evalRew3 (fun k => Sum.inl (u k)) γ = φ.evalPlain3 u γ
  | .cmp op t₁ t₂, hφ, u => by
    simp only [GenPredIn.evalRew3, GenPredIn.evalPlain3,
      TermGIn.evalRew_inl t₁ hφ.1, TermGIn.evalRew_inl t₂ hφ.2]
  | .aggCmp k h op t, hφ, u => by
    simp only [GenPredIn.evalRew3, GenPredIn.evalPlain3,
      TermGIn.evalRew_inl t hφ]
    rfl
  | .aggRange k h op₁ t₁ op₂ t₂, hφ, u => by
    simp only [GenPredIn.evalRew3, GenPredIn.evalPlain3,
      TermGIn.evalRew_inl t₁ hφ.1, TermGIn.evalRew_inl t₂ hφ.2]
    rfl
  | .and φ ψ, hφ, u => by
    simp only [GenPredIn.evalRew3, GenPredIn.evalPlain3,
      evalRew3_inl φ hφ.1 u, evalRew3_inl ψ hφ.2 u]
  | .or φ ψ, hφ, u => by
    simp only [GenPredIn.evalRew3, GenPredIn.evalPlain3,
      evalRew3_inl φ hφ.1 u, evalRew3_inl ψ hφ.2 u]
  | .not φ, hφ, u => by
    simp only [GenPredIn.evalRew3, GenPredIn.evalPlain3, evalRew3_inl φ hφ u]

/-- Gate-free predicates on `inl`-embedded rows hold as their plain
reading. -/
theorem GenPredIn.holdsRew_inl {c n : ℕ} {κ : Fin n → ColKind}
    {γ : Fin c → (T ⊕ K)} (φ : GenPredIn (T ⊕ K) c κ) (hφ : φ.chiFree)
    (u : Tuple (T ⊕ K) n) :
    φ.holdsRew (fun k => Sum.inl (u k)) γ ↔ φ.holdsPlain u γ := by
  unfold GenPredIn.holdsRew GenPredIn.holdsPlain
  rw [GenPredIn.evalRew3_inl φ hφ u]

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
theorem AggQueryIn.evaluateRew_plain :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn (T ⊕ K) c n κ)
      (_hq : q.noGammaTok) (_hc : q.chiFree)
      (D : Database (T ⊕ K))
      (γ : Fin c → (T ⊕ K)),
      q.evaluateRew D γ
        = (q.evaluatePlain D γ).map (fun t =>
            ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) _)) := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    cases hf : D.find n s
    · rfl
    · rfl
  | Proj ps q ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih hq hc.2 D γ, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun t _ => ?_)
    simp only [Function.comp_apply]
    funext j
    exact (ps j).evalRew_inl (hc.1 j) t
  | Sel φ q ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih hq hc.2 D γ]
    simp only [Multiset.filter_map]
    exact congrArg _
      (Multiset.filter_congr (fun t _ => φ.holdsRew_inl hc.1 t))
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih₁ hq.1 hc.1 D γ, ih₂ hq.2 hc.2 D γ, Multiset.map_product_map,
      Multiset.map_map]
    rw [show (q₁.evaluatePlain D γ * q₂.evaluatePlain D γ)
        = Multiset.map (fun p : Tuple (T ⊕ K) _ × Tuple (T ⊕ K) _ =>
            Fin.append p.1 p.2)
          (Multiset.product (q₁.evaluatePlain D γ) (q₂.evaluatePlain D γ))
      from rfl]
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    simp only [Function.comp_apply, Prod.map]
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih₁ hq.1 hc.1 D γ, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun u _ => ?_)
    rw [show (fun k => AggValue.collapseSum
          ((fun k' => (Sum.inl (u k') : GenValue (T ⊕ K) K)) k)) = u from rfl,
      ih₂ hq.2 hc.2 D _, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    simp only [Function.comp_apply]
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih₁ hq.1 hc.1 D γ, ih₂ hq.2 hc.2 D γ, Multiset.map_add]
  | Dedup q ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih hq hc D γ, map_plainTuple_map_inl]
    congr 1
    exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) _) =>
      @Multiset.dedup _ i (q.evaluatePlain D γ)) (Subsingleton.elim _ _)
  | Alt k hk q ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    exact ih hq hc D γ
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    refine congrArg _ (muSum_congr (fun X => ?_) b ?_)
    · rw [ih₁ hq.2 hc.2 (D.assign s X) γ, map_plainTuple_map_inl]
    · rw [ih₀ hq.1 hc.1 D γ, map_plainTuple_map_inl]
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    refine congrArg _ (muIter_congr (fun X => ?_) b)
    rw [ih₀ hq.1 hc.1 (D.assign s X) γ, ih₁ hq.2 hc.2 (D.assign s X) γ,
      map_plainTuple_map_inl, map_plainTuple_map_inl]
    exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) _) =>
      @Multiset.dedup _ i (q₀.evaluatePlain (D.assign s X) γ
        + q₁.evaluatePlain (D.assign s X) γ)) (Subsingleton.elim _ _)
  | @Diff cI nD q₁ q₂ ih₁ ih₂ =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih₁ hq.1 hc.1 D γ, ih₂ hq.2 hc.2 D γ, map_plainTuple_map_inl,
      map_plainTuple_map_inl]
    exact congrArg (Multiset.map _)
      (congrArg (fun i : DecidablePred (fun t : Tuple (T ⊕ K) nD =>
          ¬ @Membership.mem _ (Multiset (Tuple (T ⊕ K) nD))
            Multiset.instMembership (q₂.evaluatePlain D γ) t) =>
        @Multiset.filter _ _ i (q₁.evaluatePlain D γ))
        (Subsingleton.elim _ _))
  | @Gamma cI m n₁ n₂ is ts fs q keep ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih hq hc D γ, map_plainTuple_map_inl, Multiset.map_map]
    refine Multiset.map_congr ?_ (fun g _ => rfl)
    exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) n₁) =>
      @Multiset.dedup _ i (Multiset.map
        (fun u (k : Fin n₁) => u (is k)) (q.evaluatePlain D γ)))
      (Subsingleton.elim _ _)
  | @GammaScalar cI m n₂ ts fs q ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih hq hc D γ, map_plainTuple_map_inl]
    rfl
  | @GammaNest cI m n₁ κ' is his p f q ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih hq hc.2 D γ, map_plainTuple_map_inl, Multiset.map_map]
    refine Multiset.map_congr ?_ (fun g _ => rfl)
    exact congrArg (fun i : DecidableEq (Tuple (T ⊕ K) n₁) =>
      @Multiset.dedup _ i (Multiset.map
        (fun u (k : Fin n₁) => u (is k)) (q.evaluatePlain D γ)))
      (Subsingleton.elim _ _)
  | Retag h q ih =>
    intro hq hc D γ
    exact ih hq hc D γ
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain]
    rw [ih hq hc.2 D γ, Multiset.map_map]
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
          (fun u (k : Fin n₁) => u (is k)) (q.evaluatePlain D γ)))
        (Subsingleton.elim _ _)
    · simp only [Function.comp_apply]
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        refine congrArg Sum.inl (congrArg (Multiset.fold addFn 0) ?_)
        rw [Multiset.filter_map, Multiset.map_map]
        refine Eq.trans
          (Multiset.map_congr rfl (fun u _ => t.evalRew_inl hc.1 u)) ?_
        refine congrArg₂ Multiset.map rfl ?_
        congr 1
  | GammaTok is his ts fs a q keep ih =>
    intro hq hc D γ
    exact hq.elim
  | @Win cI n' m' p' P O o w t f q dist keep ih =>
    -- a window reads the collapsed rows, which the embedding leaves
    -- alone, and its `FILTER` clause cuts the frame on both sides
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew, AggQueryIn.evaluatePlain_Win_eq_opt]
    rw [ih hq hc D γ, map_plainTuple_map_inl, Multiset.map_map]
    exact Multiset.map_congr rfl (fun _ _ => rfl)
  | @WinExpr cI n' m' p' na P O o ws ts fs g q keeps ih =>
    -- and so does a multi-frame one, leaf by leaf, clause and all
    intro hq hc D γ
    simp only [AggQueryIn.evaluateRew,
      AggQueryIn.evaluatePlain_WinExpr_eq_when]
    rw [ih hq hc D γ, map_plainTuple_map_inl, Multiset.map_map]
    exact Multiset.map_congr rfl (fun _ _ => rfl)

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

/-- The same lift for an aggregate of a *bag* – a nested value's outer
aggregate, which reads no sequence. -/
def NestedValue.liftComposite (f : Multiset T → T) :
    Multiset (T ⊕ K) → T ⊕ K :=
  fun s => Sum.inl (f (s.map (Sum.elim id (fun _ => 0))))

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The lifted bag aggregate on `inl`-embedded values. -/
theorem NestedValue.liftComposite_map_inl (f : Multiset T → T)
    (s : Multiset T) :
    (NestedValue.liftComposite (K := K) f) (s.map Sum.inl) = Sum.inl (f s) := by
  unfold NestedValue.liftComposite
  rw [Multiset.map_map,
    show (Sum.elim id (fun _ => (0 : T)) ∘ (Sum.inl : T → T ⊕ K)) = id
      from funext (fun _ => rfl),
    Multiset.map_id]

omit [DecidableEq K] in
/-- The comparison indicator restricts along the `inl` embedding. -/
theorem Having.chi_inl (op : CompOp) (x y : T) :
    (Having.chi op (Sum.inl x : T ⊕ K) (Sum.inl y) : K)
      = Having.chi op x y := by
  unfold Having.chi
  rw [CompOp.eval3_inl]

/-! ## The classical rewriting stays off the token operators -/

omit [DecidableEq K] in
/-- The classical rewriting emits no token-building grouping. -/
theorem AggQueryIn.rewriting_noGammaTok :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (hq : q.classical),
      ((q.rewriting hq
        : AggQuery (T ⊕ K) (n + 1) (ColKind.rewKinds n))).noGammaTok
  | _, _, _, .Rel _ _, _ => trivial
  | _, _, _, @AggQueryIn.Proj _ _ n m κ ps q, hq =>
    rewriting_noGammaTok q hq.2
  | _, _, _, .Sel _ q, hq => rewriting_noGammaTok q hq.2
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq =>
    ⟨rewriting_noGammaTok q₁ hq.1, rewriting_noGammaTok q₂ hq.2⟩
  | _, _, _, .Sum q₁ q₂, hq =>
    ⟨rewriting_noGammaTok q₁ hq.1, rewriting_noGammaTok q₂ hq.2⟩
  | _, _, _, @AggQueryIn.Dedup _ _ n q, hq => rewriting_noGammaTok q hq
  | _, _, _, @AggQueryIn.Diff _ _ n q₁ q₂, hq =>
    ⟨⟨rewriting_noGammaTok q₁ hq.1,
      ⟨rewriting_noGammaTok q₁ hq.1, rewriting_noGammaTok q₂ hq.2⟩⟩,
     ⟨rewriting_noGammaTok q₁ hq.1, rewriting_noGammaTok q₂ hq.2⟩⟩
  | _, _, _, .Gamma _ _ _ _ _, hq => False.elim hq
  | _, _, _, .GammaScalar _ _ _, hq => False.elim hq
  | _, _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, _, .Retag _ _, hq => False.elim hq
  | _, _, _, .GammaTok _ _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .Win _ _ _ _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _, hq => False.elim hq
termination_by structural _ _ _ q _ => q

omit [DecidableEq K] in
/-- The classical rewriting emits no `FILTER` clause: it emits no
grouping at all, a classical query having none. -/
theorem AggQueryIn.rewriting_noFilter :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (hq : q.classical),
      ((q.rewriting hq
        : AggQuery (T ⊕ K) (n + 1) (ColKind.rewKinds n))).noFilter
  | _, _, _, .Rel _ _, _ => trivial
  | _, _, _, @AggQueryIn.Proj _ _ n m κ ps q, hq =>
    rewriting_noFilter q hq.2
  | _, _, _, .Sel _ q, hq => rewriting_noFilter q hq.2
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq =>
    ⟨rewriting_noFilter q₁ hq.1, rewriting_noFilter q₂ hq.2⟩
  | _, _, _, .Sum q₁ q₂, hq =>
    ⟨rewriting_noFilter q₁ hq.1, rewriting_noFilter q₂ hq.2⟩
  | _, _, _, @AggQueryIn.Dedup _ _ n q, hq => rewriting_noFilter q hq
  | _, _, _, @AggQueryIn.Diff _ _ n q₁ q₂, hq =>
    ⟨⟨rewriting_noFilter q₁ hq.1,
      ⟨rewriting_noFilter q₁ hq.1, rewriting_noFilter q₂ hq.2⟩⟩,
     ⟨rewriting_noFilter q₁ hq.1, rewriting_noFilter q₂ hq.2⟩⟩
  | _, _, _, .Gamma _ _ _ _ _, hq => False.elim hq
  | _, _, _, .GammaScalar _ _ _, hq => False.elim hq
  | _, _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, _, .Retag _ _, hq => False.elim hq
  | _, _, _, .GammaTok _ _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .Win _ _ _ _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _, hq => False.elim hq
termination_by structural _ _ _ q _ => q

omit [DecidableEq K] in
/-- The classical rewriting emits no indicator gate: its terms are
column reads, their `⊗`/`⊖` combinations, and composite casts of the
source terms – the gate is introduced only by the `HAVING` site. -/
theorem AggQueryIn.rewriting_chiFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (hq : q.classical),
      ((q.rewriting hq
        : AggQuery (T ⊕ K) (n + 1) (ColKind.rewKinds n))).chiFree
  | _, _, _, .Rel _ _, _ => trivial
  | _, _, _, @AggQueryIn.Proj _ _ n m κ ps q, hq =>
    ⟨fun j => by
        dsimp only
        by_cases hj : ((j : ℕ) < m)
        · rw [dite_eq_left hj]
          exact ProjColIn.castComposite_chiFree _ _ _
        · rw [dite_eq_right hj]
          exact trivial,
     rewriting_chiFree q hq.2⟩
  | _, _, _, .Sel _ q, hq =>
    ⟨GenPredIn.castComposite_chiFree _ _ _, rewriting_chiFree q hq.2⟩
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq =>
    ⟨fun j => by
        dsimp only
        by_cases h₁ : ((j : ℕ) < n₁)
        · rw [dite_eq_left h₁]; exact trivial
        · rw [dite_eq_right h₁]
          by_cases h₂ : ((j : ℕ) < n₁ + n₂)
          · rw [dite_eq_left h₂]; exact trivial
          · rw [dite_eq_right h₂]; exact ⟨trivial, trivial⟩,
     ⟨rewriting_chiFree q₁ hq.1, rewriting_chiFree q₂ hq.2⟩⟩
  | _, _, _, .Sum q₁ q₂, hq =>
    ⟨rewriting_chiFree q₁ hq.1, rewriting_chiFree q₂ hq.2⟩
  | _, _, _, @AggQueryIn.Dedup _ _ n q, hq => ⟨trivial, rewriting_chiFree q hq⟩
  | _, _, _, @AggQueryIn.Diff _ _ n q₁ q₂, hq =>
    ⟨⟨fun j => by
        dsimp only
        by_cases hj : ((j : ℕ) < n)
        · rw [dite_eq_left hj]; exact trivial
        · rw [dite_eq_right hj]; exact trivial,
      ⟨keyJoinCond_chiFree _ _ _ _,
       ⟨rewriting_chiFree q₁ hq.1,
        ⟨⟨fun _ => trivial, rewriting_chiFree q₁ hq.1⟩,
         ⟨fun _ => trivial, rewriting_chiFree q₂ hq.2⟩⟩⟩⟩⟩,
     ⟨fun j => by
        dsimp only
        by_cases hj : ((j : ℕ) < n)
        · rw [dite_eq_left hj]; exact trivial
        · rw [dite_eq_right hj]; exact ⟨trivial, trivial⟩,
      ⟨keyJoinCond_chiFree _ _ _ _,
       ⟨rewriting_chiFree q₁ hq.1,
        ⟨trivial, rewriting_chiFree q₂ hq.2⟩⟩⟩⟩⟩
  | _, _, _, .Gamma _ _ _ _ _, hq => False.elim hq
  | _, _, _, .GammaScalar _ _ _, hq => False.elim hq
  | _, _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, _, .Retag _ _, hq => False.elim hq
  | _, _, _, .GammaTok _ _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .Win _ _ _ _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _, hq => False.elim hq
termination_by structural _ _ _ q _ => q

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
  · rw [Fin.append_left, dite_eq_left (by
      simp only [Fin.val_castAdd]
      exact i.isLt)]
    exact congrArg (fun k => Sum.inl (p.fst k)) (Fin.ext rfl)
  · rw [Fin.append_right, dite_eq_right (by
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
  let : LinearOrder K := HasAltLinearOrder.altOrder
  let ordm : LinearOrder (AnnotatedTuple T K m) :=
    inferInstanceAs (LinearOrder (Tuple T m ×ₗ K))
  let ordm1 : LinearOrder (AnnotatedTuple (T ⊕ K) K (m + 1)) :=
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
        rw [dite_eq_left hjm, dite_eq_left hjm]
        exact congrArg Sum.inl (hbelow ⟨j, hjm⟩
          (Fin.lt_def.mpr (Fin.lt_def.mp hj)))
      · have him : ((⟨(i : ℕ), by omega⟩ : Fin (m + 1)) : ℕ) < m :=
          i.isLt
        simp only [AnnotatedTuple.toComposite_coord]
        rw [dite_eq_left him, dite_eq_left him]
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
          rw [dite_eq_left hjm, dite_eq_left hjm]
        · have hlm : ¬ ((Fin.last m : Fin (m + 1)) : ℕ) < m := by
            simp only [Fin.val_last]; omega
          simp only [AnnotatedTuple.toComposite_coord]
          rw [dite_eq_right hlm, dite_eq_right hlm]
          exact (Sum.inr_lt_inr_composite _ _).mpr hlt
  have : Std.Antisymm (fun x y : AnnotatedTuple (T ⊕ K) K (m + 1) =>
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
      dite_eq_left (show (((is k').castLE (Nat.le_succ m) : Fin (m + 1)) : ℕ)
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
theorem AggQueryIn.rewriting_provRel {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ) (hq : q.classical) (d : AnnotatedDatabase T K) :
    Multiset.map (fun u => (GenRow.plainTuple u,
        ((TermGIn.provIndex (c := 0) (Fin.last n)
          (ColKind.rewKinds_of_not_lt (lt_irrefl n))).evalRew u).annPart))
      ((q.rewriting hq).evaluateRew d.toComposite)
      = ((q.strip hq).evaluateAnnotated (q.strip_source hq) d).map
          (fun p => ((p.toComposite, p.snd)
            : AnnotatedTuple (T ⊕ K) K (n + 1))) := by
  have hR : (q.rewriting hq).evaluateRew d.toComposite
      = Multiset.map (fun t : Tuple (T ⊕ K) (n + 1) =>
          ((fun k => Sum.inl (t k)) : Tuple (GenValue (T ⊕ K) K) (n + 1)))
        (((q.strip hq).evaluateAnnotated (q.strip_source hq)
          d).toComposite) := by
    rw [AggQueryIn.evaluateRew_plain _
        (AggQueryIn.rewriting_noGammaTok q hq)
        (AggQueryIn.rewriting_chiFree q hq) _,
      AggQueryIn.rewriting_plain q hq d.toComposite,
      ← Query.rewriting_valid (q.strip hq) (q.strip_source hq) d]
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
        dite_eq_right (by simp only [Fin.val_last]; omega)]]
    rfl
