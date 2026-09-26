/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.HavingJoinCompositional

/-!
# Monotone `HAVING` conditions: absorptivity suffices

The join-based rewriting of a `HAVING` condition is correct in every
absorptive commutative m-semiring – distributivity of `⊗` over `⊖` *not*
required – as soon as the condition is *monotone*: a Boolean combination,
by `∧` and `∨` only, of atoms whose validity is preserved when occurrences
are added to the group. The atoms covered are `COUNT(*) ≥ C`, `COUNT(*) > C`
(`Query.joinCount_monotone_correct`, `Provenance.HavingQueryCorrectness`),
and the *existential* comparisons `MIN(t) ≤ c`, `MIN(t) < c`,
`MAX(t) ≥ c`, `MAX(t) > c`, which hold in a world iff it contains a
qualifying occurrence (`Having.Existential`).

* **Existential atoms** are rewritten as `ε(Π_{#0}(σ_{t op c}(q)))`
  (`existentialQuery`): per group key, the `⊕`-sum of the annotations of
  the qualifying occurrences, which is the fused predicate provenance by
  `Having.havingProv_existential` (`existential_perKey`); padded, the
  rewriting is the key-projected fused site as a multiset
  (`existential_site_rewrite`, with the four instances
  `minLe_site_rewrite`, `minLt_site_rewrite`, `maxGe_site_rewrite`,
  `maxGt_site_rewrite`).

* **Boolean closure.** A conjunction is rewritten as the join of the two
  rewritings on the group key (`keyJoin`, which multiplies the per-key
  annotations, `keyJoin_perKeySum`) and a disjunction as their set union
  (`keyUnion`, which adds them, `keyUnion_perKeySum`): exactly how the
  fused semantics `HavingPred.prov` interprets `∧` and `∨`. The syntax
  `MonoCond` of monotone conditions over the token columns of a grouping
  comes with its compositional rewriting `MonoCond.rewrite`, its reading
  `MonoCond.toHavingPred` as a Boolean combination of fused comparisons,
  and its reading `MonoCond.toGenPred` as a generalized selection
  predicate. `MonoCond.site_evaluateAnnotated` is the closed form of the
  fused site `σ_ψ(γ_{#0}[ts : fs](q))` in the general evaluator, extending
  `AggQuery.havingSite_evaluateAnnotated` to positive combinations, and
  `MonoCond.site_rewrite` is the site substitution: the key-projected fused
  site and the padded rewriting are the same multiset of annotated tuples,
  in every absorptive commutative m-semiring.

The base query has the `(key, value, identifier)` schema of
`Provenance.HavingQueryCorrectness`, with the group key in column `#0`.
-/

variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

open Having

/-! ## Comparison atoms as selection predicates -/

/-- The Boolean term `t op s`. -/
def BoolTerm.ofCompOp {T : Type} {n : ℕ} (op : CompOp) (t s : Term T n) :
    BoolTerm T n :=
  match op with
  | .eq => BoolTerm.EQ t s
  | .ne => BoolTerm.NE t s
  | .lt => BoolTerm.LT t s
  | .le => BoolTerm.LE t s
  | .gt => BoolTerm.GT t s
  | .ge => BoolTerm.GE t s
  | .syneq => BoolTerm.SYNEQ t s
  | .synne => BoolTerm.SYNNE t s

/-- `t op s` holds on a tuple iff the comparison of the two values does.
Stated over a domain where nothing is null, the comparison being
three-valued. -/
theorem BoolTerm.ofCompOp_eval {T : Type} [ValueType T] [NoNulls T] {n : ℕ}
    (op : CompOp) (t s : Term T n) (u : Tuple T n) :
    (BoolTerm.ofCompOp op t s).eval u ↔ op.eval (t.eval u) (s.eval u) := by
  cases op <;>
    (rw [BoolTerm.eval_iff]; simp [BoolTerm.ofCompOp, BoolTerm.toCompOp,
      BoolTerm.args])

/-! ## Existential atoms: `ε(Π_{#0}(σ_{t op c}(q)))` -/

/-- The selection predicate `t op c` of an existential atom. -/
def atomSel (t : Term ℕ 3) (op : CompOp) (c : ℕ) : Selection ℕ 3 :=
  Selection.BT (BoolTerm.ofCompOp op t (Term.const c))

/-- The rewriting `ε(Π_{#0}(σ_{t op c}(q)))` of an existential comparison
`f(t) op c`: the group keys of the qualifying occurrences, duplicate-
eliminated. -/
def existentialQuery (t : Term ℕ 3) (op : CompOp) (c : ℕ) (q : Query ℕ 3) :
    Query ℕ 1 :=
  Query.Dedup (Query.Proj keyTerm (Query.Sel (atomSel t op c) q))

theorem existentialQuery_source (t : Term ℕ 3) (op : CompOp) (c : ℕ)
    (q : Query ℕ 3) (hq : q.source) : (existentialQuery t op c q).source :=
  hq

omit [HasAltLinearOrder K] in
/-- Every row of the existential rewriting carries a key of the base
query. -/
theorem existentialQuery_key_mem (t : Term ℕ 3) (op : CompOp) (c : ℕ)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (x : AnnotatedTuple ℕ K 1)
    (hx : x ∈ (existentialQuery t op c q).evaluateAnnotated
      (existentialQuery_source t op c q hq) d) :
    x.fst ∈ Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf) := by
  have hx' : x ∈ Multiset.ofList (groupByKey
      ((Query.Proj keyTerm (Query.Sel (atomSel t op c) q)).evaluateAnnotated hq d)).val :=
    hx
  rw [groupByKey_eq_dedup_map] at hx'
  obtain ⟨v, hv, hvx⟩ := Multiset.mem_map.mp hx'
  have hvfst : x.fst = v := by rw [← hvx]
  obtain ⟨y, hy, hyv⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hv)
  have hy' : y ∈ ((Query.Sel (atomSel t op c) q).evaluateAnnotated hq d).map
      (fun p => (⟨fun k => (keyTerm k).eval p.fst, p.snd⟩ : AnnotatedTuple ℕ K 1)) := hy
  obtain ⟨p, hp, hpy⟩ := Multiset.mem_map.mp hy'
  have hp' : p ∈ @Multiset.filter _ (fun ta => (atomSel t op c).eval ta.fst)
      (atomSel t op c).evalDecidableAnnotated (q.evaluateAnnotated hq d) := hp
  rw [Multiset.mem_dedup]
  refine Multiset.mem_map.mpr ⟨p, Multiset.mem_of_mem_filter hp', ?_⟩
  rw [hvfst, ← hyv, ← hpy]
  rfl

omit [HasAltLinearOrder K] in
/-- Per key, the existential rewriting sums the annotations of the base
rows of that key satisfying `t op c`. -/
theorem existentialQuery_perKeySum (t : Term ℕ 3) (op : CompOp) (c : ℕ)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((existentialQuery t op c q).evaluateAnnotated
          (existentialQuery_source t op c q hq) d))).sum
      = (Multiset.map Prod.snd (Multiset.filter
          (fun p : AnnotatedTuple ℕ K 3 => keyOf p = g ∧ op.eval (t.eval p.fst) c)
          (q.evaluateAnnotated hq d))).sum := by
  have h1 : (existentialQuery t op c q).evaluateAnnotated
        (existentialQuery_source t op c q hq) d
      = Multiset.ofList (groupByKey
          ((Query.Proj keyTerm (Query.Sel (atomSel t op c) q)).evaluateAnnotated hq d)).val :=
    rfl
  have h2 : (Query.Proj keyTerm (Query.Sel (atomSel t op c) q)).evaluateAnnotated hq d
      = ((Query.Sel (atomSel t op c) q).evaluateAnnotated hq d).map
          (fun p => (⟨fun k => (keyTerm k).eval p.fst, p.snd⟩ : AnnotatedTuple ℕ K 1)) :=
    rfl
  have h3 : (Query.Sel (atomSel t op c) q).evaluateAnnotated hq d
      = @Multiset.filter _ (fun ta => (atomSel t op c).eval ta.fst)
          (atomSel t op c).evalDecidableAnnotated (q.evaluateAnnotated hq d) :=
    rfl
  rw [h1, perKeySum_groupByKey, h2, Multiset.filter_map, Multiset.map_map, h3,
    Multiset.filter_filter]
  show (Multiset.map Prod.snd (@Multiset.filter _ _ _ (q.evaluateAnnotated hq d))).sum = _
  congr 2
  exact Multiset.filter_congr fun p _ =>
    and_congr Iff.rfl (BoolTerm.ofCompOp_eval op t (Term.const c) p.fst)

/-- **Existential atoms, per key.** In an absorptive commutative
m-semiring, the existential rewriting gives every group key the fused
`f(t) op c` predicate provenance of its group, for any existential
comparison (`MIN` with `≤`/`<`, `MAX` with `≥`/`>`). No distributivity of
`⊗` over `⊖` is assumed (`Having.havingProv_existential`). -/
theorem existential_perKey (h_abs : absorptive K) {f : SeqAggFunc ℕ} {op : CompOp}
    (hf : Existential f op) (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (ts : Tuple (Term ℕ 3) 1) (c : ℕ) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((existentialQuery (ts 0) op c q).evaluateAnnotated
          (existentialQuery_source (ts 0) op c q hq) d))).sum
      = havingProv (havingGroup keyIdx (q.evaluateAnnotated hq d) g) (ts 0) f op c := by
  rw [existentialQuery_perKeySum, havingProv_existential h_abs hf, havingGroup_coe,
    Multiset.filter_filter]
  congr 2
  exact Multiset.filter_congr fun p _ =>
    and_comm.trans (and_congr Iff.rfl ⟨fun h k' => congrFun h k', fun h => funext h⟩)

/-- **Site substitution for existential atoms.** In every absorptive
commutative m-semiring, the key-projected fused `HAVING f(t) op c` site
and the padded rewriting `ε(Π_{#0}(σ_{t op c}(q)))` evaluate to the same
multiset of annotated tuples, for any existential comparison. -/
theorem existential_site_rewrite (h_abs : absorptive K) {f : SeqAggFunc ℕ} {op : CompOp}
    (hf : Existential f op) (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (ts' : Tuple (Term ℕ 3) 1) (c : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => f) op 0
        (Term.const c) (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (keyPadded (existentialQuery (ts' 0) op c) q).evaluateAnnotated
          (keyPadded_source _ q (existentialQuery_source (ts' 0) op c q hq) hq) d :=
  (fused_key_proj_gen (q.toAgg hq) q hq d (Query.toAggHaving_input q hq d)
      ts' (fun _ => f) op (Term.const c)).trans
    (keyPadded_correct_of (existentialQuery (ts' 0) op c) q
      (existentialQuery_source (ts' 0) op c q hq) hq d _
      (fun x hx => existentialQuery_key_mem (ts' 0) op c q hq d x hx)
      (fun u => existential_perKey h_abs hf q hq d ts' c u)).symm

/-- `MIN(t) ≤ c`. -/
theorem minLe_site_rewrite (h_abs : absorptive K) (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) (ts' : Tuple (Term ℕ 3) 1) (c : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => SeqAggFunc.min) CompOp.le 0
        (Term.const c) (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (keyPadded (existentialQuery (ts' 0) CompOp.le c) q).evaluateAnnotated
          (keyPadded_source _ q (existentialQuery_source (ts' 0) CompOp.le c q hq) hq) d :=
  existential_site_rewrite h_abs existential_min_le q hq d ts' c

/-- `MIN(t) < c`. -/
theorem minLt_site_rewrite (h_abs : absorptive K) (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) (ts' : Tuple (Term ℕ 3) 1) (c : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => SeqAggFunc.min) CompOp.lt 0
        (Term.const c) (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (keyPadded (existentialQuery (ts' 0) CompOp.lt c) q).evaluateAnnotated
          (keyPadded_source _ q (existentialQuery_source (ts' 0) CompOp.lt c q hq) hq) d :=
  existential_site_rewrite h_abs existential_min_lt q hq d ts' c

/-- `MAX(t) ≥ c`. -/
theorem maxGe_site_rewrite (h_abs : absorptive K) (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) (ts' : Tuple (Term ℕ 3) 1) (c : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => SeqAggFunc.max) CompOp.ge 0
        (Term.const c) (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (keyPadded (existentialQuery (ts' 0) CompOp.ge c) q).evaluateAnnotated
          (keyPadded_source _ q (existentialQuery_source (ts' 0) CompOp.ge c q hq) hq) d :=
  existential_site_rewrite h_abs existential_max_ge q hq d ts' c

/-- `MAX(t) > c`. -/
theorem maxGt_site_rewrite (h_abs : absorptive K) (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) (ts' : Tuple (Term ℕ 3) 1) (c : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => SeqAggFunc.max) CompOp.gt 0
        (Term.const c) (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (keyPadded (existentialQuery (ts' 0) CompOp.gt c) q).evaluateAnnotated
          (keyPadded_source _ q (existentialQuery_source (ts' 0) CompOp.gt c q hq) hq) d :=
  existential_site_rewrite h_abs existential_max_gt q hq d ts' c

/-! ## Boolean closure: join on the group key and set union

A conjunction of conditions is rewritten as the join of the two rewritings
on the group key, `ε(Π_{#0}(σ_{#0 = #1}(Q₁ × Q₂)))`, and a disjunction as
their set union `ε(Q₁ ⊎ Q₂)`. Per key, the join multiplies and the union
adds the annotations, which is exactly how the fused semantics
(`HavingPred.prov`) interprets `∧` and `∨`. -/

/-- The key-equality predicate `#0 = #1` on a pair of one-column rows. -/
def joinSel : Selection ℕ 2 :=
  Selection.BT (BoolTerm.EQ (Term.index ⟨0, by omega⟩) (Term.index ⟨1, by omega⟩))

/-- The projection of a pair of one-column rows to its first column. -/
def pairKey : Tuple (Term ℕ 2) 1 := fun _ => Term.index ⟨0, by omega⟩

/-- The key-equality selection over the product, `σ_{#0 = #1}(Q₁ × Q₂)`. -/
def keyJoinInner (Q₁ Q₂ : Query ℕ 1) : Query ℕ 2 :=
  Query.Sel joinSel (@Query.Prod ℕ 1 1 2 rfl Q₁ Q₂)

/-- Join on the group key, `ε(Π_{#0}(σ_{#0 = #1}(Q₁ × Q₂)))`. -/
def keyJoin (Q₁ Q₂ : Query ℕ 1) : Query ℕ 1 :=
  Query.Dedup (Query.Proj pairKey (keyJoinInner Q₁ Q₂))

/-- Set union, `ε(Q₁ ⊎ Q₂)`. -/
def keyUnion (Q₁ Q₂ : Query ℕ 1) : Query ℕ 1 := Query.Dedup (Query.Sum Q₁ Q₂)

theorem keyJoin_source (Q₁ Q₂ : Query ℕ 1) (h₁ : Q₁.source) (h₂ : Q₂.source) :
    (keyJoin Q₁ Q₂).source := ⟨h₁, h₂⟩

theorem keyUnion_source (Q₁ Q₂ : Query ℕ 1) (h₁ : Q₁.source) (h₂ : Q₂.source) :
    (keyUnion Q₁ Q₂).source := ⟨h₁, h₂⟩

/-- The row of a product: appended data parts, multiplied annotations. -/
def pairRow (z : AnnotatedTuple ℕ K 1 × AnnotatedTuple ℕ K 1) : AnnotatedTuple ℕ K 2 :=
  ⟨Fin.append z.1.fst z.2.fst, z.1.snd * z.2.snd⟩

omit [HasAltLinearOrder K] in
/-- The annotated semantics of the key-equality selection over the
product, in closed form. -/
theorem keyJoinInner_eval (Q₁ Q₂ : Query ℕ 1) (h₁ : Q₁.source) (h₂ : Q₂.source)
    (d : AnnotatedDatabase ℕ K) :
    (keyJoinInner Q₁ Q₂).evaluateAnnotated ⟨h₁, h₂⟩ d
      = @Multiset.filter _ (fun ta => joinSel.eval ta.fst) joinSel.evalDecidableAnnotated
          (Multiset.map pairRow
            (Multiset.product (Q₁.evaluateAnnotated h₁ d) (Q₂.evaluateAnnotated h₂ d))) :=
  rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- A sum of products over a product multiset factorizes. -/
theorem sum_map_mul_product {α β : Type} (f : α → K) (h : β → K)
    (s : Multiset α) (t : Multiset β) :
    ((s ×ˢ t).map (fun z => f z.1 * h z.2)).sum = (s.map f).sum * (t.map h).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, Multiset.map_map, ih,
      Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [show ((fun z : α × β => f z.1 * h z.2) ∘ Prod.mk a) = fun b => f a * h b from rfl,
      Multiset.sum_map_mul_left]

omit [HasAltLinearOrder K] in
/-- **Join on the key multiplies the per-key annotations.** -/
theorem keyJoin_perKeySum (Q₁ Q₂ : Query ℕ 1) (h₁ : Q₁.source) (h₂ : Q₂.source)
    (d : AnnotatedDatabase ℕ K) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((keyJoin Q₁ Q₂).evaluateAnnotated (keyJoin_source Q₁ Q₂ h₁ h₂) d))).sum
      = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            (Q₁.evaluateAnnotated h₁ d))).sum
        * (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            (Q₂.evaluateAnnotated h₂ d))).sum := by
  set r₁ : Multiset (AnnotatedTuple ℕ K 1) := Q₁.evaluateAnnotated h₁ d with hr₁
  set r₂ : Multiset (AnnotatedTuple ℕ K 1) := Q₂.evaluateAnnotated h₂ d with hr₂
  have hd : (keyJoin Q₁ Q₂).evaluateAnnotated (keyJoin_source Q₁ Q₂ h₁ h₂) d
      = Multiset.ofList (groupByKey
          ((Query.Proj pairKey (keyJoinInner Q₁ Q₂)).evaluateAnnotated ⟨h₁, h₂⟩ d)).val := rfl
  have hp : (Query.Proj pairKey (keyJoinInner Q₁ Q₂)).evaluateAnnotated ⟨h₁, h₂⟩ d
      = ((keyJoinInner Q₁ Q₂).evaluateAnnotated ⟨h₁, h₂⟩ d).map
          (fun p => (⟨fun k => (pairKey k).eval p.fst, p.snd⟩ : AnnotatedTuple ℕ K 1)) := rfl
  rw [hd, perKeySum_groupByKey, hp, Multiset.filter_map, Multiset.map_map, keyJoinInner_eval,
    Multiset.filter_filter, Multiset.filter_map, Multiset.map_map]
  show (Multiset.map (fun z : AnnotatedTuple ℕ K 1 × AnnotatedTuple ℕ K 1 => z.1.snd * z.2.snd)
      (@Multiset.filter _ _ _ (r₁ ×ˢ r₂))).sum = _
  trans (Multiset.map (fun z : AnnotatedTuple ℕ K 1 × AnnotatedTuple ℕ K 1 => z.1.snd * z.2.snd)
      ((r₁ ×ˢ r₂).filter (fun z => z.1.fst = g ∧ z.2.fst = g))).sum
  · congr 2
    refine Multiset.filter_congr fun z _ => ?_
    have hjs : joinSel.eval3 (Fin.append z.1.fst z.2.fst) = Kleene.true
        ↔ Fin.append z.1.fst z.2.fst ⟨0, by omega⟩
            = Fin.append z.1.fst z.2.fst ⟨1, by omega⟩ := by
      show CompOp.eq.eval3 (Fin.append z.1.fst z.2.fst ⟨0, by omega⟩)
        (Fin.append z.1.fst z.2.fst ⟨1, by omega⟩) = Kleene.true ↔ _
      rw [CompOp.eval3_eq_true_iff_noNulls]
      rfl
    show ((fun _ : Fin 1 => Fin.append z.1.fst z.2.fst ⟨0, by omega⟩) = g
        ∧ joinSel.eval3 (Fin.append z.1.fst z.2.fst) = Kleene.true)
      ↔ z.1.fst = g ∧ z.2.fst = g
    rw [hjs]
    rw [append_coord_left z.1.fst z.2.fst 0 (by omega) (by omega),
      append_coord_right₀ z.1.fst z.2.fst (by omega) (by omega)]
    constructor
    · rintro ⟨hk, heq⟩
      have hx : z.1.fst ⟨0, by omega⟩ = g ⟨0, by omega⟩ := congrFun hk ⟨0, by omega⟩
      refine ⟨funext fun k => ?_, funext fun k => ?_⟩
      · rw [Subsingleton.elim k ⟨0, by omega⟩]; exact hx
      · rw [Subsingleton.elim k ⟨0, by omega⟩, ← heq]; exact hx
    · rintro ⟨hx, hy⟩
      refine ⟨funext fun k => ?_, ?_⟩
      · rw [hx]; exact congrArg g (Subsingleton.elim _ _)
      · rw [hx, hy]
  · exact (congrArg (fun m : Multiset (AnnotatedTuple ℕ K 1 × AnnotatedTuple ℕ K 1) =>
        (Multiset.map (fun z : AnnotatedTuple ℕ K 1 × AnnotatedTuple ℕ K 1 =>
          z.1.snd * z.2.snd) m).sum)
        (filter_product (fun p : AnnotatedTuple ℕ K 1 => p.fst = g)
          (fun p : AnnotatedTuple ℕ K 1 => p.fst = g) r₁ r₂).symm).trans
      (sum_map_mul_product Prod.snd Prod.snd _ _)

omit [HasAltLinearOrder K] in
/-- **Set union adds the per-key annotations.** -/
theorem keyUnion_perKeySum (Q₁ Q₂ : Query ℕ 1) (h₁ : Q₁.source) (h₂ : Q₂.source)
    (d : AnnotatedDatabase ℕ K) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((keyUnion Q₁ Q₂).evaluateAnnotated (keyUnion_source Q₁ Q₂ h₁ h₂) d))).sum
      = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            (Q₁.evaluateAnnotated h₁ d))).sum
        + (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            (Q₂.evaluateAnnotated h₂ d))).sum := by
  have hd : (keyUnion Q₁ Q₂).evaluateAnnotated (keyUnion_source Q₁ Q₂ h₁ h₂) d
      = Multiset.ofList (groupByKey ((Query.Sum Q₁ Q₂).evaluateAnnotated ⟨h₁, h₂⟩ d)).val := rfl
  rw [hd, perKeySum_groupByKey]
  exact sum_perKeySum Q₁ Q₂ h₁ h₂ ⟨h₁, h₂⟩ d g

omit [HasAltLinearOrder K] in
/-- Rows of a key join carry keys of the left argument. -/
theorem keyJoin_key_mem (Q₁ Q₂ : Query ℕ 1) (h₁ : Q₁.source) (h₂ : Q₂.source)
    (d : AnnotatedDatabase ℕ K) (x : AnnotatedTuple ℕ K 1)
    (hx : x ∈ (keyJoin Q₁ Q₂).evaluateAnnotated (keyJoin_source Q₁ Q₂ h₁ h₂) d) :
    ∃ y ∈ Q₁.evaluateAnnotated h₁ d, x.fst = y.fst := by
  have hx' : x ∈ Multiset.ofList (groupByKey
      ((Query.Proj pairKey (keyJoinInner Q₁ Q₂)).evaluateAnnotated ⟨h₁, h₂⟩ d)).val := hx
  rw [groupByKey_eq_dedup_map] at hx'
  obtain ⟨v, hv, hvx⟩ := Multiset.mem_map.mp hx'
  have hvfst : x.fst = v := by rw [← hvx]
  obtain ⟨y, hy, hyv⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hv)
  have hy' : y ∈ ((keyJoinInner Q₁ Q₂).evaluateAnnotated ⟨h₁, h₂⟩ d).map
      (fun p => (⟨fun k => (pairKey k).eval p.fst, p.snd⟩ : AnnotatedTuple ℕ K 1)) := hy
  obtain ⟨w, hw, hwy⟩ := Multiset.mem_map.mp hy'
  rw [keyJoinInner_eval Q₁ Q₂ h₁ h₂] at hw
  obtain ⟨z, hz, hzw⟩ := Multiset.mem_map.mp (Multiset.mem_of_mem_filter hw)
  obtain ⟨hz₁, -⟩ := Multiset.mem_product.mp hz
  refine ⟨z.1, hz₁, ?_⟩
  rw [hvfst, ← hyv, ← hwy, ← hzw]
  funext k
  show Fin.append z.1.fst z.2.fst ⟨0, by omega⟩ = z.1.fst k
  rw [append_coord_left z.1.fst z.2.fst 0 (by omega) (by omega)]
  exact congrArg z.1.fst (Subsingleton.elim _ _)

omit [HasAltLinearOrder K] in
/-- Rows of a set union carry keys of one of the arguments. -/
theorem keyUnion_key_mem (Q₁ Q₂ : Query ℕ 1) (h₁ : Q₁.source) (h₂ : Q₂.source)
    (d : AnnotatedDatabase ℕ K) (x : AnnotatedTuple ℕ K 1)
    (hx : x ∈ (keyUnion Q₁ Q₂).evaluateAnnotated (keyUnion_source Q₁ Q₂ h₁ h₂) d) :
    (∃ y ∈ Q₁.evaluateAnnotated h₁ d, x.fst = y.fst)
      ∨ (∃ y ∈ Q₂.evaluateAnnotated h₂ d, x.fst = y.fst) := by
  have hx' : x ∈ Multiset.ofList (groupByKey
      (Q₁.evaluateAnnotated h₁ d + Q₂.evaluateAnnotated h₂ d)).val := hx
  rw [groupByKey_eq_dedup_map] at hx'
  obtain ⟨v, hv, hvx⟩ := Multiset.mem_map.mp hx'
  have hvfst : x.fst = v := by rw [← hvx]
  obtain ⟨y, hy, hyv⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hv)
  rcases Multiset.mem_add.mp hy with hy | hy
  · exact Or.inl ⟨y, hy, hvfst.trans hyv.symm⟩
  · exact Or.inr ⟨y, hy, hvfst.trans hyv.symm⟩

/-! ## Monotone conditions and their compositional rewriting -/

/-- Monotone `HAVING` conditions over the aggregate columns of a grouping:
`COUNT(*) ≥ C + 1` and `COUNT(*) > C + 1` on the token column `l`, an
existential comparison `f(t) op c` on the token column `l`, and
conjunctions and disjunctions. Negation is excluded: it flips
monotonicity. -/
inductive MonoCond (n₂ : ℕ) where
  | countGe (l : Fin n₂) (C : ℕ)
  | countGt (l : Fin n₂) (C : ℕ)
  | exist (l : Fin n₂) (op : CompOp) (c : ℕ)
  | and (ψ₁ ψ₂ : MonoCond n₂)
  | or (ψ₁ ψ₂ : MonoCond n₂)

namespace MonoCond

variable {n₂ : ℕ}

/-- Well-formedness with respect to the aggregates `fs` of the grouping:
the `COUNT(*)` atoms sit on `COUNT(*)` columns and the existential atoms
on existential aggregate/operator pairs (`MIN` with `≤`/`<`, `MAX` with
`≥`/`>`, see `Having.Existential`). -/
def WF (fs : Tuple (SeqAggFunc ℕ) n₂) : MonoCond n₂ → Prop
  | countGe l _ => fs l = SeqAggFunc.count
  | countGt l _ => fs l = SeqAggFunc.count
  | exist l op _ => Existential (fs l) op
  | and ψ₁ ψ₂ => ψ₁.WF fs ∧ ψ₂.WF fs
  | or ψ₁ ψ₂ => ψ₁.WF fs ∧ ψ₂.WF fs

/-- The condition as a Boolean combination of fused aggregate comparisons,
whose provenance is `HavingPred.prov` (`∧ ↦ ⊗`, `∨ ↦ ⊕`). -/
def toHavingPred (ts : Tuple (Term ℕ 3) n₂) (fs : Tuple (SeqAggFunc ℕ) n₂) :
    MonoCond n₂ → HavingPred ℕ 3 1
  | countGe l C => HavingPred.cmp (ts l) (fs l) CompOp.ge (Term.const (C + 1))
  | countGt l C => HavingPred.cmp (ts l) (fs l) CompOp.gt (Term.const (C + 1))
  | exist l op c => HavingPred.cmp (ts l) (fs l) op (Term.const c)
  | and ψ₁ ψ₂ => HavingPred.and (ψ₁.toHavingPred ts fs) (ψ₂.toHavingPred ts fs)
  | or ψ₁ ψ₂ => HavingPred.or (ψ₁.toHavingPred ts fs) (ψ₂.toHavingPred ts fs)

/-- **The compositional positive rewriting `Q_ψ`**: `COUNT(*)` atoms become
the join chains `Q₂^{≥ C}`, existential atoms `ε(Π_{#0}(σ_{t op c}(q)))`,
a conjunction the join of the two rewritings on the group key, and a
disjunction their set union. -/
def rewrite (ts : Tuple (Term ℕ 3) n₂) : MonoCond n₂ → Query ℕ 3 → Query ℕ 1
  | countGe _ C, q => joinChainQuery q C
  | countGt _ C, q => joinChainQuery q (C + 1)
  | exist l op c, q => existentialQuery (ts l) op c q
  | and ψ₁ ψ₂, q => keyJoin (ψ₁.rewrite ts q) (ψ₂.rewrite ts q)
  | or ψ₁ ψ₂, q => keyUnion (ψ₁.rewrite ts q) (ψ₂.rewrite ts q)

theorem rewrite_source (ts : Tuple (Term ℕ 3) n₂) (q : Query ℕ 3) (hq : q.source) :
    ∀ ψ : MonoCond n₂, (ψ.rewrite ts q).source
  | countGe _ C => q2_source q hq C
  | countGt _ C => q2_source q hq (C + 1)
  | exist l op c => existentialQuery_source (ts l) op c q hq
  | and ψ₁ ψ₂ => keyJoin_source _ _ (rewrite_source ts q hq ψ₁) (rewrite_source ts q hq ψ₂)
  | or ψ₁ ψ₂ => keyUnion_source _ _ (rewrite_source ts q hq ψ₁) (rewrite_source ts q hq ψ₂)

/-- **Per-key correctness of the compositional rewriting.** In an
absorptive commutative m-semiring, for every well-formed monotone
condition `ψ`, the rewriting `Q_ψ` gives every group key the fused
provenance `HavingPred.prov` of `ψ` on its group. Induction on `ψ`: the
atoms are `Query.joinChain_count_correct` and `existential_perKey`, and
`∧`/`∨` are `keyJoin_perKeySum`/`keyUnion_perKeySum`. Distributivity of
`⊗` over `⊖` is not assumed. -/
theorem perKey_correct (h_abs : absorptive K) (ts : Tuple (Term ℕ 3) n₂)
    (fs : Tuple (SeqAggFunc ℕ) n₂) (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup) (g : Tuple ℕ 1) :
    ∀ ψ : MonoCond n₂, ψ.WF fs →
      (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
          ((ψ.rewrite ts q).evaluateAnnotated (rewrite_source ts q hq ψ) d))).sum
        = (ψ.toHavingPred ts fs).prov (havingGroup keyIdx (q.evaluateAnnotated hq d) g) g
  | countGe l C, hwf => by
    have hfs : fs l = SeqAggFunc.count := hwf
    show _ = havingProv (havingGroup keyIdx (q.evaluateAnnotated hq d) g) (ts l) (fs l) CompOp.ge (C + 1)
    rw [hfs]
    exact Query.joinChain_count_correct h_abs q hq d hnodup (fun _ => ts l) C g
  | countGt l C, hwf => by
    have hfs : fs l = SeqAggFunc.count := hwf
    show _ = havingProv (havingGroup keyIdx (q.evaluateAnnotated hq d) g) (ts l) (fs l) CompOp.gt (C + 1)
    rw [hfs, havingProv_count_gt]
    exact Query.joinChain_count_correct h_abs q hq d hnodup (fun _ => ts l) (C + 1) g
  | exist l op c, hwf => by
    have hf : Existential (fs l) op := hwf
    show _ = havingProv (havingGroup keyIdx (q.evaluateAnnotated hq d) g) (ts l) (fs l) op c
    exact existential_perKey h_abs hf q hq d (fun _ => ts l) c g
  | and ψ₁ ψ₂, hwf => by
    obtain ⟨h₁, h₂⟩ := hwf
    show (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((keyJoin (ψ₁.rewrite ts q) (ψ₂.rewrite ts q)).evaluateAnnotated
          (keyJoin_source _ _ (rewrite_source ts q hq ψ₁) (rewrite_source ts q hq ψ₂)) d))).sum
      = (ψ₁.toHavingPred ts fs).prov (havingGroup keyIdx (q.evaluateAnnotated hq d) g) g
        * (ψ₂.toHavingPred ts fs).prov (havingGroup keyIdx (q.evaluateAnnotated hq d) g) g
    rw [keyJoin_perKeySum _ _ (rewrite_source ts q hq ψ₁) (rewrite_source ts q hq ψ₂) d g,
      perKey_correct h_abs ts fs q hq d hnodup g ψ₁ h₁,
      perKey_correct h_abs ts fs q hq d hnodup g ψ₂ h₂]
  | or ψ₁ ψ₂, hwf => by
    obtain ⟨h₁, h₂⟩ := hwf
    show (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((keyUnion (ψ₁.rewrite ts q) (ψ₂.rewrite ts q)).evaluateAnnotated
          (keyUnion_source _ _ (rewrite_source ts q hq ψ₁) (rewrite_source ts q hq ψ₂)) d))).sum
      = (ψ₁.toHavingPred ts fs).prov (havingGroup keyIdx (q.evaluateAnnotated hq d) g) g
        + (ψ₂.toHavingPred ts fs).prov (havingGroup keyIdx (q.evaluateAnnotated hq d) g) g
    rw [keyUnion_perKeySum _ _ (rewrite_source ts q hq ψ₁) (rewrite_source ts q hq ψ₂) d g,
      perKey_correct h_abs ts fs q hq d hnodup g ψ₁ h₁,
      perKey_correct h_abs ts fs q hq d hnodup g ψ₂ h₂]

omit [HasAltLinearOrder K] in
/-- Every row of the rewriting carries a key of the base query. -/
theorem key_mem (ts : Tuple (Term ℕ 3) n₂) (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) :
    ∀ (ψ : MonoCond n₂) (x : AnnotatedTuple ℕ K 1),
      x ∈ (ψ.rewrite ts q).evaluateAnnotated (rewrite_source ts q hq ψ) d →
      x.fst ∈ Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)
  | countGe _ C, x, hx => joinChainQuery_key_mem q hq d C x hx
  | countGt _ C, x, hx => joinChainQuery_key_mem q hq d (C + 1) x hx
  | exist l op c, x, hx => existentialQuery_key_mem (ts l) op c q hq d x hx
  | and ψ₁ ψ₂, x, hx => by
    obtain ⟨y, hy, hxy⟩ := keyJoin_key_mem _ _ (rewrite_source ts q hq ψ₁)
      (rewrite_source ts q hq ψ₂) d x hx
    rw [hxy]
    exact key_mem ts q hq d ψ₁ y hy
  | or ψ₁ ψ₂, x, hx => by
    rcases keyUnion_key_mem _ _ (rewrite_source ts q hq ψ₁) (rewrite_source ts q hq ψ₂) d x hx
      with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
    · rw [hxy]; exact key_mem ts q hq d ψ₁ y hy
    · rw [hxy]; exact key_mem ts q hq d ψ₂ y hy

/-- **Multiset-level correctness of the compositional rewriting.** In an
absorptive commutative m-semiring, the padded rewriting `Q_ψ` of a
well-formed monotone condition evaluates to exactly one row per group key
of the base query, annotated with the fused provenance `HavingPred.prov`
of `ψ` on the group. -/
theorem padded_correct (h_abs : absorptive K) (ts : Tuple (Term ℕ 3) n₂)
    (fs : Tuple (SeqAggFunc ℕ) n₂) (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ψ : MonoCond n₂) (hwf : ψ.WF fs) :
    (keyPadded (ψ.rewrite ts) q).evaluateAnnotated
        (keyPadded_source _ q (rewrite_source ts q hq ψ) hq) d
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, (ψ.toHavingPred ts fs).prov
            (havingGroup keyIdx (q.evaluateAnnotated hq d) g) g) : Tuple ℕ 1 × K)) :=
  keyPadded_correct_of (ψ.rewrite ts) q (rewrite_source ts q hq ψ) hq d _
    (fun x hx => key_mem ts q hq d ψ x hx)
    (fun u => perKey_correct h_abs ts fs q hq d hnodup u ψ hwf)

end MonoCond

/-! ## The fused site of a compound condition, in the general evaluator -/

namespace MonoCond

variable {n₂ : ℕ}

/-- The condition as a generalized selection predicate over the output of
`Gamma`: each atom compares its token column against a constant
(`GenPredIn.fusedCmp`), and `∧`/`∨` are the Boolean connectives of
`GenPred`. -/
def toGenPred : MonoCond n₂ → GenPred ℕ (ColKind.gammaKinds 1 n₂)
  | countGe l C => GenPredIn.fusedCmp CompOp.ge l (Term.const (C + 1))
  | countGt l C => GenPredIn.fusedCmp CompOp.gt l (Term.const (C + 1))
  | exist l op c => GenPredIn.fusedCmp op l (Term.const c)
  | and ψ₁ ψ₂ => GenPredIn.and ψ₁.toGenPred ψ₂.toGenPred
  | or ψ₁ ψ₂ => GenPredIn.or ψ₁.toGenPred ψ₂.toGenPred

/-- The fused site `σ_ψ(γ_{#0}[ts : fs](qg))` of a monotone condition, as a
general query. -/
abbrev site (ts : Tuple (Term ℕ 3) n₂) (fs : Tuple (SeqAggFunc ℕ) n₂) (ψ : MonoCond n₂)
    (qg : AggQuery ℕ 3 (ColKind.allReg 3)) : AggQuery ℕ (1 + n₂) (ColKind.gammaKinds 1 n₂) :=
  AggQuery.Sel ψ.toGenPred (AggQuery.Gamma keyIdx ts fs qg)

theorem toGenPred_hasAggAtom : ∀ ψ : MonoCond n₂, ψ.toGenPred.hasAggAtom = true
  | countGe _ _ => rfl
  | countGt _ _ => rfl
  | exist _ _ _ => rfl
  | and ψ₁ ψ₂ => by
    show (ψ₁.toGenPred.hasAggAtom || ψ₂.toGenPred.hasAggAtom) = true
    rw [toGenPred_hasAggAtom ψ₁, toGenPred_hasAggAtom ψ₂]
    rfl
  | or ψ₁ ψ₂ => by
    show (ψ₁.toGenPred.hasAggAtom || ψ₂.toGenPred.hasAggAtom) = true
    rw [toGenPred_hasAggAtom ψ₁, toGenPred_hasAggAtom ψ₂]
    rfl

/-- A positive combination of aggregate atoms entails the existence of the
compared groups. -/
theorem toGenPred_entailsExistence :
    ∀ ψ : MonoCond n₂, ψ.toGenPred.entailsExistence false = true
  | countGe _ _ => rfl
  | countGt _ _ => rfl
  | exist _ _ _ => rfl
  | and ψ₁ ψ₂ => by
    show (if false = true then _ else
      (ψ₁.toGenPred.entailsExistence false || ψ₂.toGenPred.entailsExistence false)) = true
    rw [ite_eq_right Bool.false_ne_true, toGenPred_entailsExistence ψ₁, toGenPred_entailsExistence ψ₂]
    rfl
  | or ψ₁ ψ₂ => by
    show (if false = true then _ else
      (ψ₁.toGenPred.entailsExistence false && ψ₂.toGenPred.entailsExistence false)) = true
    rw [ite_eq_right Bool.false_ne_true, toGenPred_entailsExistence ψ₁, toGenPred_entailsExistence ψ₂]
    rfl

/-- Every compared column of the condition is a token column. -/
theorem toGenPred_comparedCols :
    ∀ ψ : MonoCond n₂, ∀ k ∈ ψ.toGenPred.comparedCols, ∃ l : Fin n₂, k = Fin.natAdd 1 l
  | countGe l _, k, hk => ⟨l, Finset.mem_singleton.mp hk⟩
  | countGt l _, k, hk => ⟨l, Finset.mem_singleton.mp hk⟩
  | exist l _ _, k, hk => ⟨l, Finset.mem_singleton.mp hk⟩
  | and ψ₁ ψ₂, k, hk => by
    rcases Finset.mem_union.mp hk with h | h
    · exact toGenPred_comparedCols ψ₁ k h
    · exact toGenPred_comparedCols ψ₂ k h
  | or ψ₁ ψ₂, k, hk => by
    rcases Finset.mem_union.mp hk with h | h
    · exact toGenPred_comparedCols ψ₁ k h
    · exact toGenPred_comparedCols ψ₂ k h

/-- The condition compares at least one token column. -/
theorem toGenPred_comparedCols_nonempty :
    ∀ ψ : MonoCond n₂, ψ.toGenPred.comparedCols.Nonempty
  | countGe l _ => ⟨Fin.natAdd 1 l, Finset.mem_singleton_self _⟩
  | countGt l _ => ⟨Fin.natAdd 1 l, Finset.mem_singleton_self _⟩
  | exist l _ _ => ⟨Fin.natAdd 1 l, Finset.mem_singleton_self _⟩
  | and ψ₁ _ => (toGenPred_comparedCols_nonempty ψ₁).mono Finset.subset_union_left
  | or ψ₁ _ => (toGenPred_comparedCols_nonempty ψ₁).mono Finset.subset_union_left

omit [HasAltLinearOrder K] in
/-- The predicate provenance of the condition on the `Gamma` output row of
the group `g` is `HavingPred.prov` of the condition on the group
sequence. -/
theorem toGenPred_predsem (ts : Tuple (Term ℕ 3) n₂) (fs : Tuple (SeqAggFunc ℕ) n₂)
    (U : List (AnnotatedTuple ℕ K 3)) (g : Tuple ℕ 1) :
    ∀ ψ : MonoCond n₂,
      ψ.toGenPred.predsem false
        (Fin.append (fun k => (Sum.inl (g k) : GenValue ℕ K))
          (fun j => Sum.inr (AggValue.ofGroup (fs j) (ts j) U)))
      = (ψ.toHavingPred ts fs).prov U g
  | countGe l C => by
    simp only [toGenPred, GenPredIn.fusedCmp, GenPredIn.predsem, Fin.append_right,
      Term.toGenKey_eval, Bool.false_eq_true, ite_false]
    exact AggValue.predProv_ofGroup (fs l) (ts l) U CompOp.ge _
  | countGt l C => by
    simp only [toGenPred, GenPredIn.fusedCmp, GenPredIn.predsem, Fin.append_right,
      Term.toGenKey_eval, Bool.false_eq_true, ite_false]
    exact AggValue.predProv_ofGroup (fs l) (ts l) U CompOp.gt _
  | exist l op c => by
    simp only [toGenPred, GenPredIn.fusedCmp, GenPredIn.predsem, Fin.append_right,
      Term.toGenKey_eval, Bool.false_eq_true, ite_false]
    exact AggValue.predProv_ofGroup (fs l) (ts l) U op _
  | and ψ₁ ψ₂ => by
    show (if false = true then _ else
        ψ₁.toGenPred.predsem false _ * ψ₂.toGenPred.predsem false _) = _
    rw [ite_eq_right Bool.false_ne_true, toGenPred_predsem ts fs U g ψ₁, toGenPred_predsem ts fs U g ψ₂]
    rfl
  | or ψ₁ ψ₂ => by
    show (if false = true then _ else
        ψ₁.toGenPred.predsem false _ + ψ₂.toGenPred.predsem false _) = _
    rw [ite_eq_right Bool.false_ne_true, toGenPred_predsem ts fs U g ψ₁, toGenPred_predsem ts fs U g ψ₂]
    rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The compared annotation lists of the condition on the `Gamma` output
row all equal the group's annotation list. -/
theorem compared_all_eq {f : Fin (1 + n₂) → Option (List K)} {L : List K}
    (hf : ∀ l : Fin n₂, f (Fin.natAdd 1 l) = some L) (ψ : MonoCond n₂) :
    ∀ l' ∈ ψ.toGenPred.comparedCols.val.filterMap f, l' = L := by
  intro l' hl'
  obtain ⟨k, hk, hfk⟩ := (Multiset.mem_filterMap _ _).mp hl'
  obtain ⟨l, rfl⟩ := toGenPred_comparedCols ψ k hk
  rw [hf l] at hfk
  exact (Option.some.inj hfk).symm

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The condition compares at least one token, so its compared lists are
not empty. -/
theorem compared_ne_zero {f : Fin (1 + n₂) → Option (List K)} {L : List K}
    (hf : ∀ l : Fin n₂, f (Fin.natAdd 1 l) = some L) (ψ : MonoCond n₂) :
    ψ.toGenPred.comparedCols.val.filterMap f ≠ 0 := by
  obtain ⟨k, hk⟩ := toGenPred_comparedCols_nonempty ψ
  obtain ⟨l, rfl⟩ := toGenPred_comparedCols ψ k hk
  intro h
  have hmem : L ∈ ψ.toGenPred.comparedCols.val.filterMap f :=
    (Multiset.mem_filterMap _ _).mpr ⟨_, hk, hf l⟩
  rw [h] at hmem
  exact Multiset.notMem_zero _ hmem

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- A row whose pending factors vanish finalizes to its concrete part. -/
theorem finalize_eq_of_pending_eq_zero (b : K) (p : Multiset (List K)) (hp : p = 0) :
    GenAnn.finalize ⟨b, p⟩ = b := by
  subst hp
  exact GenAnn.finalize_of_pending_zero b

/-- **Closed form of the fused site of a monotone condition.** The general
evaluator produces one row per group key of the subquery, carrying the
key followed by the whole-group aggregate values and annotated by the
fused provenance `HavingPred.prov` of the condition on the group's
occurrence sequence: the pending group factor introduced by `Gamma` is
superseded by the compared tokens (every atom compares a token of that
very group), and the atoms' predicate provenances combine by `⊗`/`⊕`.
Generalizes `AggQuery.havingSite_evaluateAnnotated` from one comparison to
a positive Boolean combination. -/
theorem site_evaluateAnnotated (ts : Tuple (Term ℕ 3) n₂) (fs : Tuple (SeqAggFunc ℕ) n₂)
    (ψ : MonoCond n₂) (qg : AggQuery ℕ 3 (ColKind.allReg 3)) (d : AnnotatedDatabase ℕ K) :
    (ψ.site ts fs qg).evaluateAnnotated d
      = (Multiset.dedup ((qg.evaluateAnnotated d).map
            (fun p => fun k : Fin 1 => p.fst (keyIdx k)))).map
          (fun g =>
            ((Fin.append g (fun k => (fs k)
                ((havingGroup keyIdx (qg.evaluateAnnotated d) g).map
                  (fun p => (ts k).eval p.fst))),
              (ψ.toHavingPred ts fs).prov (havingGroup keyIdx (qg.evaluateAnnotated d) g) g)
              : AnnotatedTuple ℕ K (1 + n₂))) := by
  unfold AggQuery.evaluateAnnotated
  simp only [AggQuery.evaluate]
  rw [ite_eq_left (toGenPred_hasAggAtom ψ)]
  generalize Multiset.map GenRow.toAnnotated (qg.evaluate d) = A
  conv_lhs => rw [Multiset.map_map]
  conv_lhs => rw [Multiset.map_map]
  have hkeys : Multiset.map Prod.fst (Multiset.ofList (groupByKey
        (A.map (fun p =>
          ((fun k => p.fst (keyIdx k), p.snd) : AnnotatedTuple ℕ K 1)))).val)
      = Multiset.dedup (A.map
          (fun p => fun k : Fin 1 => p.fst (keyIdx k))) := by
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
  · -- annotation: the fused provenance of the condition
    show GenAnn.finalize ⟨1 * _, _⟩ = _
    rw [ite_eq_left (toGenPred_entailsExistence ψ)]
    -- the pending group factor is superseded: every compared token carries
    -- the group's own annotation list
    refine (finalize_eq_of_pending_eq_zero _ _ ?_).trans ?_
    · refine Multiset.filter_eq_nil.mpr fun a ha hneg => hneg ?_
      rw [Multiset.mem_singleton] at ha
      subst ha
      refine ⟨?_, compared_ne_zero
          (L := (havingGroup keyIdx A kv.fst).map Prod.snd) ?_ ψ,
        compared_all_eq ?_ ψ⟩
      · -- every compared token is grouped, so nothing blocks the supersede
        refine Multiset.eq_zero_of_forall_notMem (fun l hl => ?_)
        obtain ⟨k, -, hk⟩ := (Multiset.mem_filterMap _ _).mp hl
        revert hk
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
          simp [Fin.append_left, Fin.append_right]
      all_goals
      · intro l
        simp only [Fin.append_right, AggValue.annList_ofGroup]
    · rw [one_mul]
      exact toGenPred_predsem ts fs _ kv.fst ψ

/-- **The key-projected fused site of a monotone condition** is one row per
group key of the base query, annotated with the fused provenance of the
condition on its group (the shape the padded rewriting evaluates to). -/
theorem site_key_proj (ts : Tuple (Term ℕ 3) n₂) (fs : Tuple (SeqAggFunc ℕ) n₂)
    (ψ : MonoCond n₂) (qg : AggQuery ℕ 3 (ColKind.allReg 3))
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hin : qg.evaluateAnnotated d = q.evaluateAnnotated hq d) :
    ((ψ.site ts fs qg).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd) : Tuple ℕ 1 × K))
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, (ψ.toHavingPred ts fs).prov
            (havingGroup keyIdx (q.evaluateAnnotated hq d) g) g) : Tuple ℕ 1 × K)) := by
  rw [site_evaluateAnnotated, hin]
  show ((Multiset.dedup ((q.evaluateAnnotated hq d).map
      (fun p => fun k : Fin 1 => p.fst (keyIdx k)))).map _).map _ = _
  rw [Multiset.map_map]
  show (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map _ = _
  refine Multiset.map_congr rfl (fun g _ => ?_)
  dsimp only [Function.comp]
  refine Prod.ext ?_ rfl
  funext k
  rw [append_coord_left g _ 0 (by omega) (by omega)]
  exact congrArg g (Subsingleton.elim _ _)

/-- **Site substitution for monotone conditions: absorptivity suffices.**
In every absorptive commutative m-semiring – distributivity of `⊗` over
`⊖` not required – the key-projected fused site `σ_ψ(γ_{#0}[ts : fs](q))`
of a well-formed monotone condition `ψ` and the padded compositional
rewriting `Q_ψ` evaluate to the *same multiset of annotated tuples*: the
rewriting can be substituted for the key-projected fused operator inside
any surrounding query. The sole hypothesis on the instance is the global
row-distinctness of the base query's output (the occurrence identifiers
of the `COUNT(*)` join chains). -/
theorem site_rewrite (h_abs : absorptive K) (ts : Tuple (Term ℕ 3) n₂)
    (fs : Tuple (SeqAggFunc ℕ) n₂) (ψ : MonoCond n₂) (hwf : ψ.WF fs)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup) :
    ((ψ.site ts fs (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd) : Tuple ℕ 1 × K))
      = (keyPadded (ψ.rewrite ts) q).evaluateAnnotated
          (keyPadded_source _ q (rewrite_source ts q hq ψ) hq) d :=
  (site_key_proj ts fs ψ (q.toAgg hq) q hq d (Query.toAggHaving_input q hq d)).trans
    (padded_correct h_abs ts fs q hq d hnodup ψ hwf).symm

end MonoCond
