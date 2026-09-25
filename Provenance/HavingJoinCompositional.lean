/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.HavingQueryCorrectness

/-!
# Compositional correctness of the JOIN rewriting for `HAVING COUNT(*)`

`Provenance.HavingQueryCorrectness` proves the join-based rewriting of a
`HAVING COUNT(*) op (C+1)` correct *extensionally*: per group key, the sum
of the annotations of the join query's rows is the fused predicate
provenance. This file upgrades that to an *intensional*, multiset-level
equality, the form needed to substitute the rewriting for the fused
operator inside an arbitrary surrounding query.

The one obstruction to multiset-level equality is the failing groups: the
fused operator emits a `𝟘`-annotated row for a group that fails the
comparison, while the join query emits no row at all. The rewriting is
therefore *padded*: `joinCountQueryPadded` adds to the join query the
self-difference `keysQuery q ∖ keysQuery q` – one `𝟘`-annotated row per
group key – and duplicate-eliminates the union, which merges everything
into exactly one row per group key carrying the summed annotation. The
result (`joinCountQueryPadded_correct`) is *equal as a multiset of
annotated tuples* to the key projection of the fused `HAVING` output
(`proj_fused_eq_keyed`), so the substitution is transparent to every
surrounding operator – including annotation-sensitive ones like `Diff`
and further `HAVING`s, which are *not* congruences for the naive
“equal up to `𝟘`-rows” relation (a `𝟘`-annotated row still changes the
deterministic aggregate values of an enclosing group).
-/

variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]

/-- `AnnotatedRelation` is an opaque `def` over `Multiset`, so instance
search does not see the multiset membership through it; register it. -/
instance {T K : Type} {n : ℕ} :
    Membership (AnnotatedTuple T K n) (AnnotatedRelation T K n) :=
  inferInstanceAs (Membership (AnnotatedTuple T K n)
    (Multiset (AnnotatedTuple T K n)))

/-! ## The padded join query -/

/-- The canonical key selector of the `(key, value, identifier)` base
schema. -/
def keyIdx : Tuple (Fin 3) 1 := fun _ => ⟨0, by omega⟩

/-- The key column, as a projection term. -/
def keyTerm : Tuple (Term ℕ 3) 1 := fun _ => Term.index ⟨0, by omega⟩

/-- The group key of an annotated base row. -/
def keyOf {K : Type} (p : AnnotatedTuple ℕ K 3) : Tuple ℕ 1 :=
  fun _ => p.fst ⟨0, by omega⟩

/-- One row per distinct group key, annotated by the `⊕`-sum of the
group's annotations. -/
def keysQuery (q : Query ℕ 3) : Query ℕ 1 := Query.Dedup (Query.Proj keyTerm q)

/-- One `𝟘`-annotated row per distinct group key: the self-difference of
the key query (`α ⊖ α = 𝟘`). -/
def zeroPadQuery (q : Query ℕ 3) : Query ℕ 1 :=
  Query.Diff (keysQuery q) (keysQuery q)

/-- Key padding of a one-column rewriting `Q` of a `HAVING` site over the
base query `q`: `Q`, padded with a `𝟘`-annotated row per group key of `q`
and duplicate-eliminated into one row per group key. -/
def keyPadded (Q : Query ℕ 3 → Query ℕ 1) (q : Query ℕ 3) : Query ℕ 1 :=
  Query.Dedup (Query.Sum (Q q) (zeroPadQuery q))

/-- The padded join-based rewriting of `HAVING COUNT(*) op (C + 1)`:
the join query, padded with a `𝟘`-annotated row per group key and
duplicate-eliminated into one row per group key. -/
def joinCountQueryPadded (q : Query ℕ 3) (op : CompOp) (C : ℕ) :
    Query ℕ 1 :=
  keyPadded (fun q => Query.joinCountQuery q op C) q

theorem keysQuery_source (q : Query ℕ 3) (hq : q.source) :
    (keysQuery q).source := hq

theorem zeroPadQuery_source (q : Query ℕ 3) (hq : q.source) :
    (zeroPadQuery q).source := ⟨hq, hq⟩

theorem keyPadded_source (Q : Query ℕ 3 → Query ℕ 1) (q : Query ℕ 3)
    (hQ : (Q q).source) (hq : q.source) : (keyPadded Q q).source :=
  ⟨hQ, hq, hq⟩

theorem joinCountQueryPadded_source (q : Query ℕ 3) (hq : q.source)
    (op : CompOp) (C : ℕ) : (joinCountQueryPadded q op C).source :=
  keyPadded_source _ q (Query.joinCountQuery_source q hq op C) hq

/-! ## Key bookkeeping -/

section Keys

variable [HasAltLinearOrder K]

omit [HasAltLinearOrder K] in
/-- Every row of the join chain carries the key of some base row in its
key coordinate. -/
theorem joinChain_key_mem (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) :
    ∀ (C : ℕ) (x : AnnotatedTuple ℕ K (3 * C + 3)),
      x ∈ (joinChain q C).evaluateAnnotated (joinChain_source q hq C) d →
      ∃ p ∈ q.evaluateAnnotated hq d,
        x.fst ⟨0, by omega⟩ = p.fst ⟨0, by omega⟩
  | 0, x, hx => ⟨x, hx, rfl⟩
  | C + 1, x, hx => by
    have hstep : (joinChain q (C + 1)).evaluateAnnotated
          (joinChain_source q hq (C + 1)) d
        = @Multiset.filter _
            (fun ta : AnnotatedTuple ℕ K (3 * (C + 1) + 3) =>
              (chainCond C).eval ta.fst)
            ((chainCond C).evalDecidableAnnotated)
            (Multiset.map (chainCombine C)
              (Multiset.product
                ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)
                (q.evaluateAnnotated hq d))) := rfl
    rw [hstep] at hx
    obtain ⟨z, hz, hzx⟩ := Multiset.mem_map.mp (Multiset.mem_of_mem_filter hx)
    obtain ⟨hz₁, -⟩ := Multiset.mem_product.mp hz
    obtain ⟨p, hp, hkey⟩ := joinChain_key_mem q hq d C z.1 hz₁
    refine ⟨p, hp, ?_⟩
    rw [← hzx]
    show Fin.append z.1.1 z.2.1 ⟨0, by omega⟩ = p.fst ⟨0, by omega⟩
    rw [Having.append_coord_left z.1.1 z.2.1 0 (by omega) (by omega)]
    exact hkey

omit [HasAltLinearOrder K] in
/-- The key multiset of the base query, through the key projection. -/
theorem keyed_fst (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K) :
    Multiset.map Prod.fst
        ((Query.Proj keyTerm q).evaluateAnnotated hq d)
      = (q.evaluateAnnotated hq d).map
          keyOf := by
  show Multiset.map Prod.fst ((q.evaluateAnnotated hq d).map _) = _
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl fun p _ => rfl

omit [HasAltLinearOrder K] in
/-- Every row of the chain-projected key query carries a key of the base
query. -/
theorem joinChainQuery_key_mem (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) (C : ℕ) (x : AnnotatedTuple ℕ K 1)
    (hx : x ∈ (joinChainQuery q C).evaluateAnnotated (q2_source q hq C) d) :
    x.fst ∈ Multiset.dedup ((q.evaluateAnnotated hq d).map
      keyOf) := by
  have hx' : x ∈ Multiset.ofList (groupByKey
      ((Query.Proj (fun _ : Fin 1 => Term.index (⟨0, by omega⟩ : Fin (3 * C + 3)))
        (joinChain q C)).evaluateAnnotated
        (Query.sourceDedup (q2_source q hq C) rfl) d)).val :=
    hx
  rw [groupByKey_eq_dedup_map] at hx'
  obtain ⟨v, hv, hvx⟩ := Multiset.mem_map.mp hx'
  have hvfst : x.fst = v := by rw [← hvx]
  obtain ⟨y, hy, hyv⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hv)
  obtain ⟨z, hz, hzy⟩ := Multiset.mem_map.mp hy
  obtain ⟨p, hp, hkey⟩ := joinChain_key_mem q hq d C z hz
  rw [Multiset.mem_dedup]
  refine Multiset.mem_map.mpr ⟨p, hp, ?_⟩
  rw [hvfst, ← hyv, ← hzy]
  funext k
  show p.fst ⟨0, by omega⟩ = z.fst ⟨0, by omega⟩
  exact hkey.symm

omit [HasAltLinearOrder K] in
/-- Rows of a difference keep the data parts of its left argument. -/
theorem diff_row_mem (q₁ q₂ : Query ℕ 1)
    (h₁ : q₁.source) (hd : (Query.Diff q₁ q₂).source)
    (d : AnnotatedDatabase ℕ K) (y : AnnotatedTuple ℕ K 1)
    (hy : y ∈ (Query.Diff q₁ q₂).evaluateAnnotated hd d) :
    ∃ z ∈ q₁.evaluateAnnotated h₁ d, y.fst = z.fst := by
  simp only [Query.evaluateAnnotated] at hy
  obtain ⟨z, hz, hzy⟩ := Multiset.mem_map.mp hy
  obtain ⟨u, α⟩ := z
  exact ⟨(u, α), hz, by rw [← hzy]⟩

omit [HasAltLinearOrder K] in
/-- Every row of the join-based query, for any comparison operator,
carries a key of the base query. -/
theorem joinCountQuery_key_mem (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) (op : CompOp) (C : ℕ)
    (x : AnnotatedTuple ℕ K 1)
    (hx : x ∈ (Query.joinCountQuery q op C).evaluateAnnotated
      (Query.joinCountQuery_source q hq op C) d) :
    x.fst ∈ Multiset.dedup ((q.evaluateAnnotated hq d).map
      keyOf) := by
  have hdiff : ∀ (C₁ C₂ : ℕ) (y : AnnotatedTuple ℕ K 1),
      y ∈ (Query.Diff (joinChainQuery q C₁) (joinChainQuery q C₂)
        ).evaluateAnnotated
        ⟨q2_source q hq C₁, q2_source q hq C₂⟩ d →
      y.fst ∈ Multiset.dedup ((q.evaluateAnnotated hq d).map
        keyOf) := by
    intro C₁ C₂ y hy
    obtain ⟨z, hz, hfst⟩ :=
      diff_row_mem (joinChainQuery q C₁) (joinChainQuery q C₂)
        (q2_source q hq C₁) ⟨q2_source q hq C₁, q2_source q hq C₂⟩ d y hy
    rw [hfst]
    exact joinChainQuery_key_mem q hq d C₁ z hz
  cases op with
  | lt => exact hdiff 0 C x hx
  | le => exact hdiff 0 (C + 1) x hx
  | eq => exact hdiff C (C + 1) x hx
  | ne =>
    rcases Multiset.mem_add.mp hx with hx' | hx'
    · exact hdiff 0 C x hx'
    · exact joinChainQuery_key_mem q hq d (C + 1) x hx'
  | ge => exact joinChainQuery_key_mem q hq d C x hx
  | gt => exact joinChainQuery_key_mem q hq d (C + 1) x hx
  | syneq => exact hdiff C (C + 1) x hx
  | synne =>
    rcases Multiset.mem_add.mp hx with hx' | hx'
    · exact hdiff 0 C x hx'
    · exact joinChainQuery_key_mem q hq d (C + 1) x hx'

end Keys

/-! ## Evaluation of the padding -/

section Padding

variable [HasAltLinearOrder K]

omit [HasAltLinearOrder K] in
/-- The key query evaluates to one row per distinct key with the summed
annotation. -/
theorem keysQuery_eval (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) :
    (keysQuery q).evaluateAnnotated (keysQuery_source q hq) d
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map
          keyOf)).map
          (fun u => ((u, (Multiset.map Prod.snd
            (Multiset.filter (fun p : AnnotatedTuple ℕ K 1 => p.1 = u)
              ((Query.Proj keyTerm q).evaluateAnnotated hq d))).sum)
            : Tuple ℕ 1 × K)) := by
  show Multiset.ofList (groupByKey
      ((Query.Proj keyTerm q).evaluateAnnotated hq d)).val = _
  rw [groupByKey_eq_dedup_map, keyed_fst]

omit [HasAltLinearOrder K] in
/-- The padding query evaluates to one `𝟘`-annotated row per distinct
key. -/
theorem zeroPadQuery_eval (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) :
    (zeroPadQuery q).evaluateAnnotated (zeroPadQuery_source q hq) d
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map
          keyOf)).map
          (fun u => ((u, (0 : K)) : Tuple ℕ 1 × K)) := by
  show ((keysQuery q).evaluateAnnotated (keysQuery_source q hq) d).map _ = _
  rw [keysQuery_eval q hq d, Multiset.map_map]
  refine Multiset.map_congr rfl fun u hu => ?_
  dsimp only [Function.comp]
  refine Prod.ext rfl ?_
  dsimp only
  rw [groupByKey_find_eq_filter_sum]
  have hB := perKeySum_dedup_map (α := Tuple ℕ 1) (β := K)
    ((q.evaluateAnnotated hq d).map keyOf)
    (fun u => (Multiset.map Prod.snd
      (Multiset.filter (fun p : AnnotatedTuple ℕ K 1 => p.1 = u)
        ((Query.Proj keyTerm q).evaluateAnnotated hq d))).sum) u
  rw [ite_eq_left (Multiset.mem_dedup.mp hu)] at hB
  refine Eq.trans ?_ (monus_self ((Multiset.map Prod.snd
    (Multiset.filter (fun p : AnnotatedTuple ℕ K 1 => p.1 = u)
      ((Query.Proj keyTerm q).evaluateAnnotated hq d))).sum))
  exact congrArg₂ (fun a b : K => a - b)
    (Eq.refl _)
    (Eq.trans (congrArg Multiset.sum (congrArg (Multiset.map Prod.snd)
      (Multiset.filter_congr (fun x _ => Iff.rfl)))) hB)

end Padding

/-! ## Site correctness: the padded rewriting, row for row -/

section SiteCorrectness

variable [HasAltLinearOrder K]

omit [HasAltLinearOrder K] in
/-- **The padding argument**, for any one-column rewriting `Q` whose rows
carry keys of the base query: whenever `Q q` gives every group key `u` the
annotation `F u` as a per-key annotation sum, the padded query evaluates to
exactly one row per group key `g` of `q`, annotated `F g`. Instances:
`joinCountQueryPadded_correct_of` for the `COUNT(*)` join rewritings, and
the existential and compositional rewritings of
`Provenance.HavingMonotone`. -/
theorem keyPadded_correct_of (Q : Query ℕ 3 → Query ℕ 1)
    (q : Query ℕ 3) (hQ : (Q q).source) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (F : Tuple ℕ 1 → K)
    (hkeys : ∀ x ∈ (Q q).evaluateAnnotated hQ d,
      x.fst ∈ Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf))
    (hkey : ∀ u : Tuple ℕ 1,
      (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
        ((Q q).evaluateAnnotated hQ d))).sum = F u) :
    (keyPadded Q q).evaluateAnnotated (keyPadded_source Q q hQ hq) d
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, F g) : Tuple ℕ 1 × K)) := by
  show Multiset.ofList (groupByKey
      ((Q q).evaluateAnnotated hQ d
      + (zeroPadQuery q).evaluateAnnotated (zeroPadQuery_source q hq) d)).val
    = _
  rw [groupByKey_eq_dedup_map, zeroPadQuery_eval q hq d, Multiset.map_add,
    Multiset.dedup_add]
  rw [show Multiset.dedup (Multiset.map Prod.fst
        ((Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun u => ((u, (0 : K)) : Tuple ℕ 1 × K))))
      = Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf) from by
    rw [Multiset.map_map,
      show Multiset.map
          (Prod.fst ∘ fun u : Tuple ℕ 1 => ((u, (0 : K)) : Tuple ℕ 1 × K))
          (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf))
        = Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf) from
        Multiset.map_id' _]
    exact Multiset.dedup_eq_self.mpr (Multiset.nodup_dedup _)]
  have hsub : Multiset.map Prod.fst ((Q q).evaluateAnnotated hQ d)
      ⊆ Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.mp hx
    rw [← hyx]
    exact hkeys y hy
  rw [Multiset.Subset.ndunion_eq_right hsub]
  refine Multiset.map_congr rfl (fun u hu => ?_)
  refine Prod.ext rfl ?_
  dsimp only
  rw [Multiset.filter_add, Multiset.map_add, Multiset.sum_add]
  have hzero : (Multiset.map Prod.snd (Multiset.filter
      (fun p : AnnotatedTuple ℕ K 1 => p.1 = u)
      ((Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
        (fun u => ((u, (0 : K)) : Tuple ℕ 1 × K))))).sum = (0 : K) :=
    Eq.trans (perKeySum_dedup_map (α := Tuple ℕ 1) (β := K)
      ((q.evaluateAnnotated hq d).map keyOf) (fun _ => (0 : K)) u)
      (ite_self _)
  exact Eq.trans (congrArg₂ (· + ·) (hkey u) hzero) (add_zero _)

/-- The padding argument for the `COUNT(*)` join rewritings: whenever
`Query.joinCountQuery q op C` gives every group key the fused predicate
provenance as a per-key annotation sum, the padded query evaluates to
exactly one row per group key carrying it. Both
`joinCountQueryPadded_correct` and `joinCountQueryPadded_monotone_correct`
are instances. -/
theorem joinCountQueryPadded_correct_of
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (ts : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ)
    (hkey : ∀ u : Tuple ℕ 1,
      (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
        ((Query.joinCountQuery q op C).evaluateAnnotated
          (Query.joinCountQuery_source q hq op C) d))).sum
      = Having.havingProv
          (Having.havingGroup keyIdx (q.evaluateAnnotated hq d) u)
          (ts 0) SeqAggFunc.count op (C + 1)) :
    (joinCountQueryPadded q op C).evaluateAnnotated
        (joinCountQueryPadded_source q hq op C) d
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, Having.havingProv
            (Having.havingGroup keyIdx (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count op (C + 1)) : Tuple ℕ 1 × K)) :=
  keyPadded_correct_of (fun q => Query.joinCountQuery q op C) q
    (Query.joinCountQuery_source q hq op C) hq d _
    (fun x hx => joinCountQuery_key_mem q hq d op C x hx) hkey

/-- **Multiset-level correctness of the padded JOIN rewriting.** In an
absorptive commutative m-semiring whose `⊗` distributes over `⊖`, the
padded join-based query evaluates to *exactly* – row for row, annotation
for annotation – one row per group key of the base query, annotated with
the fused `COUNT(*) op (C + 1)` predicate provenance. The sole hypothesis
is the injective per-group occurrence identifiers (global
row-distinctness of the base query's output). -/
theorem joinCountQueryPadded_correct
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ) :
    (joinCountQueryPadded q op C).evaluateAnnotated
        (joinCountQueryPadded_source q hq op C) d
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, Having.havingProv
            (Having.havingGroup keyIdx (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count op (C + 1)) : Tuple ℕ 1 × K)) :=
  joinCountQueryPadded_correct_of q hq d ts op C
    (Query.joinCount_correct h_abs h_distrib q hq d hnodup ts op C)

/-- **Padded rewriting of the monotone comparisons, without
distributivity.** For `op ∈ {≥, >}`, `joinCountQueryPadded_correct` holds
in every absorptive commutative m-semiring
(`Query.joinCount_monotone_correct`). -/
theorem joinCountQueryPadded_monotone_correct
    (h_abs : absorptive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts : Tuple (Term ℕ 3) 1) (op : CompOp) (hop : op = CompOp.ge ∨ op = CompOp.gt)
    (C : ℕ) :
    (joinCountQueryPadded q op C).evaluateAnnotated
        (joinCountQueryPadded_source q hq op C) d
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, Having.havingProv
            (Having.havingGroup keyIdx (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count op (C + 1)) : Tuple ℕ 1 × K)) :=
  joinCountQueryPadded_correct_of q hq d ts op C
    (Query.joinCount_monotone_correct h_abs q hq d hnodup ts op hop C)

/-- **The key-projected fused output.** Projecting the output of a fused
`HAVING f(t) op s` site to its group key yields one row per group key of
the base query, annotated with the predicate provenance of its group: the
shape the padded rewritings evaluate to (`keyPadded_correct_of`), so that a
padded rewriting can be substituted for the key-projected fused operator
inside any surrounding query. -/
theorem fused_key_proj_gen (qg : AggQuery ℕ 3 (ColKind.allReg 3))
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hin : qg.evaluateAnnotated d = q.evaluateAnnotated hq d)
    (ts' : Tuple (Term ℕ 3) 1) (fs : Tuple (SeqAggFunc ℕ) 1) (op : CompOp)
    (s : Term ℕ 1) :
    ((AggQuery.havingSite keyIdx ts' fs op 0 s qg).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, Having.havingProv
            (Having.havingGroup keyIdx (q.evaluateAnnotated hq d) g)
            (ts' 0) (fs 0) op (s.eval g)) : Tuple ℕ 1 × K)) := by
  rw [AggQuery.havingSite_evaluateAnnotated, hin]
  show ((Multiset.dedup ((q.evaluateAnnotated hq d).map
      (fun p => fun k : Fin 1 => p.fst (keyIdx k)))).map _).map _ = _
  rw [Multiset.map_map]
  show (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map _ = _
  refine Multiset.map_congr rfl (fun g hg => ?_)
  dsimp only [Function.comp]
  refine Prod.ext ?_ rfl
  funext k
  rw [Having.append_coord_left g _ 0 (by omega) (by omega)]
  exact congrArg g (Subsingleton.elim _ _)

/-- The `COUNT(*) op (C + 1)` instance of `fused_key_proj_gen`. -/
theorem fused_key_proj (qg : AggQuery ℕ 3 (ColKind.allReg 3))
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hin : qg.evaluateAnnotated d = q.evaluateAnnotated hq d)
    (ts' : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => SeqAggFunc.count) op 0
        (Term.const (C + 1)) qg).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (Multiset.dedup ((q.evaluateAnnotated hq d).map keyOf)).map
          (fun g => ((g, Having.havingProv
            (Having.havingGroup keyIdx (q.evaluateAnnotated hq d) g)
            (ts' 0) SeqAggFunc.count op (C + 1)) : Tuple ℕ 1 × K)) :=
  fused_key_proj_gen qg q hq d hin ts' (fun _ => SeqAggFunc.count) op (Term.const (C + 1))

/-- **Site substitution.** The key-projected fused
`HAVING COUNT(*) op (C + 1)` site over the embedded classical query and
the padded join-based rewriting
evaluate to the *same multiset of annotated tuples*: substituting one for
the other inside any surrounding query preserves the annotated semantics
verbatim. -/
theorem countHaving_site_rewrite
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts' : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => SeqAggFunc.count) op 0
        (Term.const (C + 1)) (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (joinCountQueryPadded q op C).evaluateAnnotated
          (joinCountQueryPadded_source q hq op C) d :=
  (fused_key_proj (q.toAgg hq) q hq d (Query.toAggHaving_input q hq d) ts' op C).trans
    (joinCountQueryPadded_correct h_abs h_distrib q hq d hnodup ts' op C).symm

/-- **Site substitution for the monotone comparisons**, in every absorptive
commutative m-semiring: `countHaving_site_rewrite` for `op ∈ {≥, >}` with
the distributivity hypothesis dropped. -/
theorem countHaving_site_rewrite_monotone
    (h_abs : absorptive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts' : Tuple (Term ℕ 3) 1) (op : CompOp) (hop : op = CompOp.ge ∨ op = CompOp.gt)
    (C : ℕ) :
    ((AggQuery.havingSite keyIdx ts' (fun _ => SeqAggFunc.count) op 0
        (Term.const (C + 1)) (q.toAgg hq)).evaluateAnnotated d).map
        (fun p => ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩, p.snd)
          : Tuple ℕ 1 × K))
      = (joinCountQueryPadded q op C).evaluateAnnotated
          (joinCountQueryPadded_source q hq op C) d :=
  (fused_key_proj (q.toAgg hq) q hq d (Query.toAggHaving_input q hq d) ts' op C).trans
    (joinCountQueryPadded_monotone_correct h_abs q hq d hnodup ts' op hop C).symm

end SiteCorrectness
