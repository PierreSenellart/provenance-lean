import Provenance.QueryAnnotatedDatabase
import Provenance.QueryRewriting

/-!
# Query evaluation commutes with m-semiring homomorphisms

Given an m-semiring homomorphism `h : K → K'`, evaluating a (non-aggregation)
query over an annotated database whose annotations have been pushed forward
along `h` is the same as evaluating over the original database and then pushing
the resulting relation forward along `h`:

```
  evaluateAnnotated q (h ⋆ d) = h ⋆ evaluateAnnotated q d
```

This is the formal counterpart to ProvSQL's “compile once, evaluate many”
architecture: each `sr_*` semiring evaluator is the application of a (different)
homomorphism to the same persistent provenance representation, and this theorem
says going through the homomorphism on the input side and on the output side
give the same answer.

The result is distinct from `How.universal`, which only proves *existence* of
a homomorphism out of `ℕ[X]` and does not connect it to query evaluation.

(The persistent provenance representation is *not* literally an element of
`ℕ[X]`. First, on the algebraic side, `ℕ[X]` is not the universal m-semiring
(see [Geerts & Poggi, Example 10][geerts2010database], or `How.not_universal_m`
in `Provenance/Semirings/How.lean`), so it could not factor every m-semiring
evaluation even if we restricted to the operators it supports. Second, on the
implementation side, ProvSQL's circuit has gate types that go beyond the
semiring framework altogether: `δ` (the δ operator for aggregation row
provenance from [Amsterdamer, Deutch & Tannen, *Provenance for aggregate
queries*][amsterdamer2011aggregate]), `cmp` (HAVING-style comparison gates),
`agg` / `semimod` / `value` (the K-semimodule construction for aggregate
values), `mulinput` (block-independent database alternatives), and the
continuous-distribution stack `rv` / `arith` / `mixture`. The commutation
theorem here applies to the `RA⁺(\)` fragment that *is* purely m-semiring-
valued; it neither covers nor speaks to those other gate types.)

For the positive fragment (`Rel`, `Proj`, `Sel`, `Prod`, `Sum`, `Dedup`), this
is the content of [Green, Karvounarakis & Tannen, *Provenance Semirings*,
Proposition 3.5][green2007provenance]: for any commutative-semiring map
`h : K → K'`, the transformation on `K`-relations commutes with every `RA⁺`
query of one argument *if and only if* `h` is a semiring homomorphism. Note
that Green et al. (and Geerts & Poggi below) work with set semantics, in which
a `K`-relation is a *function* `U-Tup → K` and union is defined pointwise by
`(R₁ ∪ R₂)(t) = R₁(t) + R₂(t)`; deduplication-with-annotation-sum is therefore
automatic. Our library works with `Multiset (AnnotatedTuple T K n)` instead,
so the deduplication step is exposed as a separate `Dedup` operator that
explicitly sums duplicate-tuple annotations. The `Dedup` case below is the
bookkeeping artifact of working in multiset semantics; it requires only that
`h` respect `+`, not monus, and so still belongs to Green et al.'s
proposition rather than to the difference extension below.

The genuine extension, covering `Diff` (the only case that requires monus),
is [Geerts & Poggi, *On database query languages for K-relations*,
Proposition 1][geerts2010database]: for any m-semiring map `h : K → K'`, the
transformation commutes with every `RA⁺(\)` query *if and only if* `h` is an
*m-semiring* homomorphism (i.e. it preserves monus in addition to addition
and multiplication). The `Diff` case of `Query.evaluateAnnotated_hom`
crucially uses `SemiringWithMonusHom`'s `map_sub` field; this is the only
case that goes beyond Green et al.'s setting.

Geerts & Poggi also observe ([*ibid.*, Example 10][geerts2010database]) that
`ℕ[X]` is *not* the universal m-semiring (the analog of Theorem 4.3 of
[Green et al.][green2007provenance] fails for `RA⁺(\)`); hence this commutation
theorem genuinely lives at the level of m-homomorphisms, and there is no
single universal factorization through `ℕ[X]`.

## Main definitions and results

* `SemiringWithMonusHom.mapAnnotatedTuple`, `mapAnnotatedRelation`,
  `mapAnnotatedDatabase`: pointwise pushforward along the homomorphism.
* `Query.evaluateAnnotated_hom`: the commutation theorem
  ([Green et al., Proposition 3.5][green2007provenance],
  [Geerts & Poggi, Proposition 1][geerts2010database]).
-/

set_option linter.unusedSectionVars false

-- `Filter.evalDecidableAnnotated` (in `QueryAnnotatedDatabase.lean`) is a
-- `@[reducible] def`, not an `instance`; we promote it here so that
-- typeclass synthesis can find it inside `Multiset.filter` goals.
attribute [instance] Filter.evalDecidableAnnotated

variable {T: Type} [ValueType T] [AddCommSemigroup T] [Sub T] [Mul T]
variable {K K': Type} [SemiringWithMonus K] [SemiringWithMonus K']
                     [DecidableEq K] [DecidableEq K']

namespace SemiringWithMonusHom

variable (h : SemiringWithMonusHom K K')

/-- Push an annotated tuple forward along a semiring homomorphism: the data
component is left untouched, the annotation is mapped through `h`. -/
def mapAnnotatedTuple (ta: AnnotatedTuple T K n) : AnnotatedTuple T K' n :=
  (ta.1, h ta.2)

/-- Push an annotated relation forward along a semiring homomorphism. -/
def mapAnnotatedRelation (r: AnnotatedRelation T K n) : AnnotatedRelation T K' n :=
  r.map (mapAnnotatedTuple h)

/-- Push an annotated database forward along a semiring homomorphism. -/
def mapAnnotatedDatabase (d: AnnotatedDatabase T K) : AnnotatedDatabase T K' :=
  d.map (fun e => (e.1, ⟨e.2.1, mapAnnotatedRelation h e.2.2⟩))

@[simp]
theorem mapAnnotatedRelation_zero :
    mapAnnotatedRelation (T := T) (n := n) h 0 = 0 := rfl

@[simp]
theorem mapAnnotatedRelation_add (r₁ r₂: AnnotatedRelation T K n) :
    mapAnnotatedRelation h (r₁ + r₂)
      = mapAnnotatedRelation h r₁ + mapAnnotatedRelation h r₂ := by
  unfold mapAnnotatedRelation
  exact Multiset.map_add _ r₁ r₂

/-- The data side of an annotated relation is unaffected by the pushforward. -/
@[simp]
theorem map_fst_mapAnnotatedRelation (r: AnnotatedRelation T K n) :
    (mapAnnotatedRelation h r).map Prod.fst = r.map Prod.fst := by
  show Multiset.map Prod.fst (Multiset.map (mapAnnotatedTuple h) r)
       = Multiset.map Prod.fst r
  simp only [Multiset.map_map]
  rfl

/-- Mapping the annotation side pushes the homomorphism through. -/
@[simp]
theorem map_snd_mapAnnotatedRelation (r: AnnotatedRelation T K n) :
    (mapAnnotatedRelation h r).map Prod.snd = (r.map Prod.snd).map h.toRingHom := by
  show Multiset.map Prod.snd (Multiset.map (mapAnnotatedTuple h) r)
       = Multiset.map h.toRingHom (Multiset.map Prod.snd r)
  simp only [Multiset.map_map]
  rfl

/-- Filtering by an `fst`-only predicate commutes with the pushforward. -/
theorem mapAnnotatedRelation_filter_fst (P: Tuple T n → Prop) [DecidablePred P]
    (r: AnnotatedRelation T K n) :
    @Multiset.filter _ (fun (ta: AnnotatedTuple T K' n) => P ta.fst) _
        (mapAnnotatedRelation h r)
      = mapAnnotatedRelation h
          (@Multiset.filter _ (fun (ta: AnnotatedTuple T K n) => P ta.fst) _ r) := by
  unfold mapAnnotatedRelation mapAnnotatedTuple
  induction r using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
    rw [Multiset.map_cons]
    by_cases hP : P p.fst
    · rw [Multiset.filter_cons_of_pos
            (p := fun ta : AnnotatedTuple T K' n => P ta.fst) _ hP,
          Multiset.filter_cons_of_pos
            (p := fun ta : AnnotatedTuple T K n => P ta.fst) _ hP,
          Multiset.map_cons, ih]
    · rw [Multiset.filter_cons_of_neg
            (p := fun ta : AnnotatedTuple T K' n => P ta.fst) _ hP,
          Multiset.filter_cons_of_neg
            (p := fun ta : AnnotatedTuple T K n => P ta.fst) _ hP, ih]

/-- Annotation-side sum over the entries with a given first component commutes
with the pushforward: it pulls out `h.toRingHom`. -/
theorem sum_filter_map_snd_mapAnnotatedRelation
    (v : Tuple T n) (r : AnnotatedRelation T K n) :
    (Multiset.map Prod.snd
        (@Multiset.filter _ (fun q : AnnotatedTuple T K' n => q.1 = v) _
          (mapAnnotatedRelation h r))).sum
      = h.toRingHom (Multiset.map Prod.snd
        (@Multiset.filter _ (fun q : AnnotatedTuple T K n => q.1 = v) _ r)).sum := by
  -- `mapAnnotatedRelation_filter_fst` pushes the pushforward through the filter,
  -- but the `DecidablePred` instances on `Multiset.filter` differ syntactically
  -- between the helper's output and the goal. Use `convert` to bypass that and
  -- close the residual instance subgoals with `Subsingleton.elim`.
  convert congrArg (Multiset.sum ∘ Multiset.map Prod.snd)
    (mapAnnotatedRelation_filter_fst (T := T) (K := K) (K' := K')
      h (P := fun x => x = v) r) using 1
  rw [Function.comp_apply, map_snd_mapAnnotatedRelation]
  exact (Multiset.sum_hom _ h.toRingHom).symm

/-- `Filter.eval` on the data side commutes with pushforward, in the form needed
to interchange `Multiset.filter` and `mapAnnotatedRelation` in the `Sel` case. -/
theorem mapAnnotatedRelation_filter (φ : Filter T n) (r: AnnotatedRelation T K n) :
    @Multiset.filter _ (fun (ta: AnnotatedTuple T K' n) => φ.eval ta.fst)
        φ.evalDecidableAnnotated (mapAnnotatedRelation h r)
      = mapAnnotatedRelation h
          (@Multiset.filter _ (fun (ta: AnnotatedTuple T K n) => φ.eval ta.fst)
            φ.evalDecidableAnnotated r) := by
  unfold mapAnnotatedRelation mapAnnotatedTuple
  induction r using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
    rw [Multiset.map_cons]
    by_cases hφ : φ.eval p.fst
    · rw [Multiset.filter_cons_of_pos
            (p := fun ta : AnnotatedTuple T K' n => φ.eval ta.fst) _ hφ,
          Multiset.filter_cons_of_pos
            (p := fun ta : AnnotatedTuple T K n => φ.eval ta.fst) _ hφ,
          Multiset.map_cons, ih]
    · rw [Multiset.filter_cons_of_neg
            (p := fun ta : AnnotatedTuple T K' n => φ.eval ta.fst) _ hφ,
          Multiset.filter_cons_of_neg
            (p := fun ta : AnnotatedTuple T K n => φ.eval ta.fst) _ hφ, ih]

/-- `find` commutes with the database-level pushforward. -/
theorem find_mapAnnotatedDatabase (n: ℕ) (s: String) (d: AnnotatedDatabase T K) :
    (mapAnnotatedDatabase h d).find n s
      = (d.find n s).map (mapAnnotatedRelation h) := by
  induction d with
  | nil =>
    unfold mapAnnotatedDatabase AnnotatedDatabase.find AnnotatedDatabase.find.f
    simp
  | cons hd tl ih =>
    unfold mapAnnotatedDatabase AnnotatedDatabase.find AnnotatedDatabase.find.f
    by_cases hcond: n = hd.snd.fst ∧ s = hd.fst
    · simp [hcond]
      have := hcond.left
      subst this
      rfl
    · simp [hcond]
      unfold mapAnnotatedDatabase AnnotatedDatabase.find at ih
      exact ih

end SemiringWithMonusHom

/-- `find?` on `groupByKey`, projected to the value side, equals the semiring
sum of the annotations at the chosen key. Bridges the `groupByKey`-based
aggregation used in `evaluateAnnotated`'s `Diff` clause with the `filter`-based
aggregation that `sum_filter_map_snd_mapAnnotatedRelation` reasons about. -/
theorem groupByKey_find_eq_filter_sum (r : AnnotatedRelation T K n) (u : Tuple T n) :
    (((groupByKey r).val.find? (·.1 = u)).map Prod.snd).getD 0
      = (Multiset.map Prod.snd
          (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u) r)).sum := by
  by_cases huk : u ∈ Multiset.map Prod.fst r
  · -- `u` appears as a key: extract the unique matching entry.
    obtain ⟨w, hw_mem⟩ := (groupByKey_key_iff r u).mpr huk
    have hw_eq := groupByKey_value r u w hw_mem
    have hfind : (groupByKey r).val.find? (·.1 = u) = some (u, w) := by
      have hnk := KeyValueList.nodupkey _ (groupByKey r).property
      rcases List.mem_iff_append.mp hw_mem with ⟨l₁, l₂, hsplit⟩
      rw [hsplit, List.find?_append]
      have hl₁_none : List.find? (fun x => decide (x.1 = u)) l₁ = none := by
        apply List.find?_eq_none.mpr
        intro a ha
        simp only [decide_eq_true_iff]
        rw [hsplit, List.pairwise_append] at hnk
        exact hnk.right.right a ha (u, w) List.mem_cons_self
      rw [hl₁_none]
      simp
    rw [hfind]; simp [hw_eq]
  · -- `u` is not a key: `find?` is `none` and the filter is empty.
    have hfind : (groupByKey r).val.find? (·.1 = u) = none := by
      apply List.find?_eq_none.mpr
      intro a ha
      simp only [decide_eq_true_iff]
      intro hau
      apply huk
      have hau_mem : (u, a.2) ∈ (groupByKey r).val := by
        have : a = (u, a.2) := Prod.ext hau rfl
        rw [← this]; exact ha
      exact (groupByKey_key_iff r u).mp ⟨a.2, hau_mem⟩
    rw [hfind]
    simp only [Option.map_none, Option.getD_none]
    symm
    -- The filter is empty (no element has key `u`); reduce via `Multiset.map_congr` style.
    have h_all_no : ∀ y ∈ Multiset.map Prod.snd
        (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u) r), False := by
      intro y hy
      rcases Multiset.mem_map.mp hy with ⟨x, hx_mem, _⟩
      rw [Multiset.mem_filter] at hx_mem
      exact huk (Multiset.mem_map.mpr ⟨x, hx_mem.1, hx_mem.2⟩)
    rw [show Multiset.map Prod.snd
            (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u) r) = 0 from
          Multiset.eq_zero_iff_forall_notMem.mpr (fun y hy => h_all_no y hy)]
    simp

/-! ## The commutation theorem -/

/-- **Commutation of query evaluation with m-semiring homomorphisms.** For an
m-semiring homomorphism `h : K → K'`, evaluating a (non-aggregation) query on
the pushed-forward annotated database equals pushing forward the result of
evaluating on the original database.

This is the “if” direction of [Green, Karvounarakis & Tannen, Proposition
3.5][green2007provenance] for the positive cases (`Rel`, `Proj`, `Sel`, `Prod`,
`Sum`, `Dedup`), and of [Geerts & Poggi, Proposition 1][geerts2010database]
for the only case that needs monus (`Diff`). The `Dedup` case is the explicit
form, in our multiset semantics, of the annotation-summing that is automatic
in Green et al.'s set semantics; it still requires only that `h` respect `+`.
The “only if” direction (that commutation forces `h` to be an m-hom) is not
formalised here.

Aggregation (`Agg`) is excluded via the `noAgg` precondition; see the comment
on `Query.evaluateAnnotated` for the underlying limitation. -/
theorem Query.evaluateAnnotated_hom
    (h : SemiringWithMonusHom K K') :
    ∀ {n} (q: Query T n) (hq: q.noAgg) (d: AnnotatedDatabase T K),
      evaluateAnnotated q hq (h.mapAnnotatedDatabase d)
        = h.mapAnnotatedRelation (evaluateAnnotated q hq d) := by
  intro n q
  induction q with
  | Rel n s =>
    intro _ d
    unfold evaluateAnnotated
    rw [SemiringWithMonusHom.find_mapAnnotatedDatabase]
    cases hf : d.find n s with
    | none => simp; rfl
    | some r => simp
  | Proj ts q' ih =>
    intro hq d
    simp only [evaluateAnnotated]
    rw [ih (Query.noAggProj hq rfl) d]
    unfold SemiringWithMonusHom.mapAnnotatedRelation
              SemiringWithMonusHom.mapAnnotatedTuple
    simp [Multiset.map_map]
  | Sel φ q' ih =>
    intro hq d
    simp only [evaluateAnnotated]
    rw [ih (Query.noAggSel hq rfl) d]
    exact h.mapAnnotatedRelation_filter φ _
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    intro hq d
    simp only [evaluateAnnotated]
    rw [ih₁ (Query.noAggProd hq rfl).left d,
        ih₂ (Query.noAggProd hq rfl).right d]
    generalize evaluateAnnotated q₁ (Query.noAggProd hq rfl).left d = r₁
    generalize evaluateAnnotated q₂ (Query.noAggProd hq rfl).right d = r₂
    unfold SemiringWithMonusHom.mapAnnotatedRelation
              SemiringWithMonusHom.mapAnnotatedTuple
    -- expose `Multiset.product` as a `bind` so `cons_bind` works in the recursion
    unfold Multiset.product
    induction r₁ using Multiset.induction_on with
    | empty => simp
    | @cons p s ih_p =>
      rw [Multiset.map_cons, Multiset.cons_bind, Multiset.cons_bind,
          Multiset.map_add, Multiset.map_add, ih_p, Multiset.map_add]
      -- the bind component matches after `ih_p`; only the head term needs work
      congr 1
      simp only [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro q _
      refine Prod.ext rfl ?_
      simp [Function.comp, h.toRingHom.map_mul]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq d
    simp only [evaluateAnnotated]
    rw [ih₁ (Query.noAggSum hq rfl).left d,
        ih₂ (Query.noAggSum hq rfl).right d]
    exact (SemiringWithMonusHom.mapAnnotatedRelation_add h _ _).symm
  | Dedup q' ih =>
    intro hq d
    simp only [evaluateAnnotated]
    rw [ih (Query.noAggDedup hq rfl) d]
    -- Rewrite both sides via `groupByKey_multiset_eq` (from `QueryRewriting`).
    rw [groupByKey_multiset_eq, groupByKey_multiset_eq,
        SemiringWithMonusHom.map_fst_mapAnnotatedRelation]
    -- Push `mapAnnotatedRelation h` through the outer `map` on the RHS so both
    -- sides become a single `Multiset.map` over `(map fst r).dedup`.
    conv_rhs =>
      change Multiset.map (SemiringWithMonusHom.mapAnnotatedTuple h)
        (Multiset.map _ _)
      rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro v _
    refine Prod.ext rfl ?_
    exact SemiringWithMonusHom.sum_filter_map_snd_mapAnnotatedRelation h v _
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq d
    simp only [evaluateAnnotated]
    rw [ih₁ (Query.noAggDiff hq rfl).left d,
        ih₂ (Query.noAggDiff hq rfl).right d]
    -- Push `mapAnnotatedRelation h` through the outer `r₁.map` on RHS.
    unfold SemiringWithMonusHom.mapAnnotatedRelation
              SemiringWithMonusHom.mapAnnotatedTuple
    simp only [Multiset.map_map]
    apply Multiset.map_congr rfl
    rintro ⟨u, α⟩ _
    refine Prod.ext rfl ?_
    -- After beta, the goal's RHS is `h(α − find?_orig u)`; apply `map_sub` to
    -- push `h` through.
    simp only [Function.comp_apply, SemiringWithMonusHom.map_sub]
    -- Now both sides are `h α − ?`; cancel the leading `h α` via `congr`.
    congr 1
    -- Remaining: `find?_h u = h.toRingHom (find?_orig u)`. Push through
    -- `groupByKey_find_eq_filter_sum` on both sides, then close by
    -- `sum_filter_map_snd_mapAnnotatedRelation`.
    rw [groupByKey_find_eq_filter_sum, groupByKey_find_eq_filter_sum]
    exact SemiringWithMonusHom.sum_filter_map_snd_mapAnnotatedRelation h u _
  | Agg _ _ _ _ =>
    intro hq _
    exact False.elim (by simp [Query.noAgg] at hq)
