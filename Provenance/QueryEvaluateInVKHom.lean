/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryAggregationHom
import Provenance.QueryEvaluateInVK

/-!
# Unified hom commutation for `Query.evaluateAnnotatedFull`

The single hom commutation theorem `Query.evaluateAnnotatedFull_hom`
asserts that for any well-formed query `q` and any `SemiringWithMonusHom
h : K → K'`,

```
evaluateAnnotatedFull q hq (h ⋆ d) =
  (evaluateAnnotatedFull q hq d).map (mapAnnotatedFullRow h)
```

where `mapAnnotatedFullRow h` is the pointwise pushforward on a
`LiftedTK`-tuple (`data` cells unchanged, `ann α` mapped through `h`,
`ktensor t` mapped through `KTensor.mapHom h.toRingHom`).

This is the aggregation analogue of `Query.evaluateAnnotated_hom`
([Green, Karvounarakis & Tannen, *Provenance Semirings*,
Prop. 3.5][green2007provenance]) extended to the (R5) aggregation case,
and continues the "compile once, evaluate many" theme of
[Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]: a single
K-annotated computation can be specialised to any concrete m-semiring
`K'` through an m-semiring homomorphism `h`, *including* for aggregate
queries with K-tensor row annotations.

The proof reduces:
- non-Agg cases to the existing `Query.evaluateAnnotated_hom` plus the
  bridge between `AnnotatedRelation.toLifted` and `mapAnnotatedRelation`
  (proven here);
- the Agg case is a direct argument mirroring `Query.evaluateAggSum_hom`
  but on the `LiftedTK`-valued output. The δ-applied row-annotation
  column is handled by the new `map_delta` field of
  `SemiringWithMonusHom`.

## References

* [Green, Karvounarakis & Tannen][green2007provenance]
* [Geerts & Poggi][geerts2010database]
* [Sen, Maniu & Senellart][sen2026provsql]
-/

namespace Query

variable {T : Type} [ValueType T] [AddCommSemigroup T] [Zero T]
variable {K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']
                       [DecidableEq K] [DecidableEq K']

/-! ## Bridge: `mapAnnotatedRelation` and `toLifted` commute -/

omit [ValueType T] [AddCommSemigroup T] [Zero T] [DecidableEq K] [DecidableEq K'] in
/-- The bridge between annotated-relation pushforward and `toLifted`:
pushing `h` through and then lifting agrees with lifting and then
applying `mapHomFn h.toRingHom` pointwise on each tuple cell. -/
theorem AnnotatedRelation.toLifted_mapAnnotatedRelation
    {n : ℕ} (h : SemiringWithMonusHom K K') (ar : AnnotatedRelation T K n) :
    (h.mapAnnotatedRelation ar).toLifted
      = ar.toLifted.map (fun t => fun k : Fin (n + 1) =>
          LiftedTK.mapHomFn h.toRingHom (t k)) := by
  unfold AnnotatedRelation.toLifted SemiringWithMonusHom.mapAnnotatedRelation
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  funext k
  show (SemiringWithMonusHom.mapAnnotatedTuple h p).toLifted k =
    LiftedTK.mapHomFn h.toRingHom (p.toLifted k)
  unfold AnnotatedTuple.toLifted SemiringWithMonusHom.mapAnnotatedTuple
  refine Fin.addCases ?_ ?_ k
  · intro i
    rw [Fin.append_left, Fin.append_left]
    rfl
  · intro j
    rw [Fin.append_right, Fin.append_right]
    have hj : j = 0 := by ext; exact Nat.lt_one_iff.mp j.isLt
    subst hj
    rfl

/-! ## Row-wise pushforward on `evaluateAnnotatedFull` output -/

/-- The row-wise pushforward applied to an `evaluateAnnotatedFull` output:
each `LiftedTK T K` cell is mapped through `LiftedTK.mapHomFn h.toRingHom`. -/
def mapAnnotatedFullRow (h : SemiringWithMonusHom K K') {n : ℕ}
    (row : Tuple (LiftedTK T K) n) : Tuple (LiftedTK T K') n :=
  fun k => LiftedTK.mapHomFn h.toRingHom (row k)

/-! ## Unified hom commutation theorem -/

/-- **Unified hom commutation** for `Query.evaluateAnnotatedFull`.

For any `SemiringWithMonusHom h : K → K'` and any well-formed query `q`
(non-aggregating, or top-level aggregation with non-aggregating inner
query), evaluating the unified annotated semantics on the pushforward
`h ⋆ d` is the same as evaluating on `d` and then mapping each output
row pointwise through `LiftedTK.mapHomFn h.toRingHom`.

This is the aggregation extension of the Green-Karvounarakis-Tannen
hom commutation property (Prop. 3.5), and the unified counterpart of
both `Query.evaluateAnnotated_hom` (non-Agg) and
`Query.evaluateAggSum_hom` (Agg, separate output format). -/
theorem evaluateAnnotatedFull_hom (h : SemiringWithMonusHom K K')
    {n : ℕ} (q : Query T n) (hq : q.wellFormed)
    (d : AnnotatedDatabase T K) :
    Query.evaluateAnnotatedFull q hq (h.mapAnnotatedDatabase d)
      = (Query.evaluateAnnotatedFull q hq d).map (Query.mapAnnotatedFullRow h) := by
  induction q with
  | Rel n s =>
      show ((Query.Rel n s).evaluateAnnotated hq (h.mapAnnotatedDatabase d)).toLifted = _
      rw [Query.evaluateAnnotated_hom h (Query.Rel n s) hq d,
          AnnotatedRelation.toLifted_mapAnnotatedRelation h]
      rfl
  | Proj ts q' _ =>
      show ((Query.Proj ts q').evaluateAnnotated hq (h.mapAnnotatedDatabase d)).toLifted = _
      rw [Query.evaluateAnnotated_hom h (Query.Proj ts q') hq d,
          AnnotatedRelation.toLifted_mapAnnotatedRelation h]
      rfl
  | Sel φ q' _ =>
      show ((Query.Sel φ q').evaluateAnnotated hq (h.mapAnnotatedDatabase d)).toLifted = _
      rw [Query.evaluateAnnotated_hom h (Query.Sel φ q') hq d,
          AnnotatedRelation.toLifted_mapAnnotatedRelation h]
      rfl
  | @Prod n₁ n₂ n hn q₁ q₂ _ _ =>
      show ((@Query.Prod _ n₁ n₂ n hn q₁ q₂).evaluateAnnotated hq
            (h.mapAnnotatedDatabase d)).toLifted = _
      rw [Query.evaluateAnnotated_hom h (@Query.Prod _ n₁ n₂ n hn q₁ q₂) hq d,
          AnnotatedRelation.toLifted_mapAnnotatedRelation h]
      rfl
  | Sum q₁ q₂ _ _ =>
      show ((Query.Sum q₁ q₂).evaluateAnnotated hq (h.mapAnnotatedDatabase d)).toLifted = _
      rw [Query.evaluateAnnotated_hom h (Query.Sum q₁ q₂) hq d,
          AnnotatedRelation.toLifted_mapAnnotatedRelation h]
      rfl
  | Dedup q' _ =>
      show ((Query.Dedup q').evaluateAnnotated hq (h.mapAnnotatedDatabase d)).toLifted = _
      rw [Query.evaluateAnnotated_hom h (Query.Dedup q') hq d,
          AnnotatedRelation.toLifted_mapAnnotatedRelation h]
      rfl
  | Diff q₁ q₂ _ _ =>
      show ((Query.Diff q₁ q₂).evaluateAnnotated hq (h.mapAnnotatedDatabase d)).toLifted = _
      rw [Query.evaluateAnnotated_hom h (Query.Diff q₁ q₂) hq d,
          AnnotatedRelation.toLifted_mapAnnotatedRelation h]
      rfl
  | @Agg m n₁ n₂ is ts as q_inner _ =>
      -- The Agg case mirrors `Query.evaluateAggSum_hom`'s structure but on
      -- the `LiftedTK`-valued output.
      show Query.evaluateAnnotatedFull
            (@Query.Agg T m n₁ n₂ is ts as q_inner) hq
            (h.mapAnnotatedDatabase d) = _
      unfold Query.evaluateAnnotatedFull
      dsimp only []
      rw [Query.evaluateAnnotated_hom h q_inner hq d]
      set r : AnnotatedRelation T K m := q_inner.evaluateAnnotated hq d
      rw [Multiset.map_map]
      -- Bind `r` and `h.mapAnnotatedRelation r` at the plain Prod type
      -- (rather than the `AnnotatedTuple`/Lex type) so the inner-map's
      -- lambda type matches the goal's syntactic form.
      let r_prod : Multiset (Tuple T m × K) := r
      let r_prod' : Multiset (Tuple T m × K') :=
        SemiringWithMonusHom.mapAnnotatedRelation h r
      -- Group keys agree on both sides: `mapAnnotatedRelation` only touches
      -- the K-side, but the group-key projection only reads `.fst`.
      have h_keys :
          r_prod'.map (fun p : Tuple T m × K' => fun k : Fin n₁ => p.1 (is k))
            = r_prod.map (fun p : Tuple T m × K => fun k : Fin n₁ => p.1 (is k)) := by
        show Multiset.map _
            (Multiset.map (SemiringWithMonusHom.mapAnnotatedTuple h) r_prod) = _
        rw [Multiset.map_map]
        rfl
      show
        Multiset.map _ (r_prod'.map (fun p : Tuple T m × K' => fun k : Fin n₁ =>
            p.1 (is k))).dedup
          = Multiset.map _ (r_prod.map (fun p : Tuple T m × K => fun k : Fin n₁ =>
              p.1 (is k))).dedup
      rw [h_keys]
      apply Multiset.map_congr rfl
      intro g _
      -- The matching multisets on either side differ only by the K-pushforward
      -- (the filter predicate only depends on `.fst`).
      have h_filter :
          Multiset.filter
              (fun p : Tuple T m × K' => ∀ k' : Fin n₁, p.1 (is k') = g k')
              (SemiringWithMonusHom.mapAnnotatedRelation h r)
            = SemiringWithMonusHom.mapAnnotatedRelation h
                (Multiset.filter
                  (fun p : Tuple T m × K => ∀ k' : Fin n₁, p.1 (is k') = g k') r) :=
        SemiringWithMonusHom.mapAnnotatedRelation_filter_fst
          (P := fun t : Tuple T m => ∀ k' : Fin n₁, t (is k') = g k') h r
      rw [h_filter]
      set matching : Multiset (AnnotatedTuple T K m) :=
        Multiset.filter
          (fun p : AnnotatedTuple T K m => ∀ k' : Fin n₁, p.fst (is k') = g k') r
      -- Show the per-group row matches: data side unchanged, K-tensor cells
      -- mapped through `KTensor.mapHom h.toRingHom`, δ-applied K cell
      -- mapped through `h.toRingHom` (and δ commutes via `h.map_delta`).
      unfold Query.mapAnnotatedFullRow Function.comp
      funext k
      refine Fin.addCases ?_ ?_ k
      · -- First `n₁ + n₂` columns (data + ktensor).
        intro i
        simp only [Fin.append_left]
        refine Fin.addCases ?_ ?_ i
        · -- First `n₁` columns: data side, unchanged by pushforward.
          intro j
          simp only [Fin.append_left]
          rfl
        · -- Next `n₂` columns: K-tensor cells, pushforward via mapHom.
          intro j
          simp only [Fin.append_right]
          show LiftedTK.ktensor
              ((SemiringWithMonusHom.mapAnnotatedRelation h matching).map
                (fun p => (p.snd, (ts j).eval p.fst)))
            = LiftedTK.mapHomFn h.toRingHom
                (LiftedTK.ktensor (matching.map (fun p => (p.snd, (ts j).eval p.fst))))
          unfold LiftedTK.mapHomFn
          congr 1
          unfold SemiringWithMonusHom.mapAnnotatedRelation
                  SemiringWithMonusHom.mapAnnotatedTuple KTensor.mapHom
          simp only [Multiset.map_map]
          rfl
      · -- Last column: δ(Σ α) — the K-side cell. Uses `map_delta`.
        intro j
        simp only [Fin.append_right]
        have hj : j = 0 := by ext; exact Nat.lt_one_iff.mp j.isLt
        subst hj
        show LiftedTK.ann
              (SemiringWithMonus.delta
                ((SemiringWithMonusHom.mapAnnotatedRelation h matching).map Prod.snd).sum)
          = LiftedTK.mapHomFn h.toRingHom
              (LiftedTK.ann (SemiringWithMonus.delta (matching.map Prod.snd).sum))
        unfold LiftedTK.mapHomFn
        congr 1
        -- The δ commutes via `h.map_delta`; the K-side sum commutes via `h.toRingHom`'s additivity.
        rw [SemiringWithMonusHom.map_snd_mapAnnotatedRelation h matching]
        rw [Multiset.sum_hom _ h.toRingHom]
        exact (h.map_delta _).symm

end Query
