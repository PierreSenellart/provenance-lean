/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryAggregation
import Provenance.QueryAnnotatedDatabaseHom

/-!
# Hom commutation for `Query.evaluateAggSum`

For a `SemiringWithMonusHom h : K → K'`, evaluating the aggregation operator
under the pushforward of the annotated database `h ⋆ d` equals pushing
the K-tensor coefficients of `evaluateAggSum`'s output forward along `h`:

```
evaluateAggSum is ts q hq (h ⋆ d) =
  (evaluateAggSum is ts q hq d).map (push K-tensor along h)
```

This is the aggregation analogue of `Query.evaluateAnnotated_hom`
([Green, Karvounarakis & Tannen, *Provenance Semirings*, Prop. 3.5][green2007provenance],
[Geerts & Poggi, *On database query languages for K-relations*,
Prop. 1][geerts2010database]) and continues the "compile once, evaluate
many" theme of [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]: a
single K-annotated computation can be specialised to any concrete
m-semiring K' through an m-semiring homomorphism, including for the
aggregation operator and its K-tensor row annotations.

The proof reduces to (i) the existing
`Query.evaluateAnnotated_hom` on the inner non-aggregating query and
(ii) the observation that the pushforward of an annotated relation
leaves the data side untouched and applies `h.toRingHom` to each
annotation — which means group keys, matching predicates and aggregated
data values are unaffected, while each K-tensor coefficient is mapped
through `h`.

## References

* [Green, Karvounarakis & Tannen][green2007provenance]
* [Geerts & Poggi][geerts2010database]
* [Sen, Maniu & Senellart][sen2026provsql]
-/

namespace Query

variable {T : Type} [ValueType T] [AddCommSemigroup T] [Zero T]
variable {K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']
                       [DecidableEq K] [DecidableEq K']

/-- The push-forward applied row-by-row to an `evaluateAggSum` output: the
group-key stays untouched; for each aggregated column, the data value
(`Prod.fst`) is preserved and the K-tensor (`Prod.snd`) is mapped through
`h.toRingHom` on each monomial's K-coefficient. -/
def mapAggSumRow (h : SemiringWithMonusHom K K') {n₁ n₂ : ℕ}
    (row : Tuple T n₁ × Tuple (T × KTensor K T) n₂) :
    Tuple T n₁ × Tuple (T × KTensor K' T) n₂ :=
  (row.fst, fun k => ((row.snd k).fst, KTensor.mapHom h.toRingHom (row.snd k).snd))

omit [Zero T] in
/-- **Aggregation hom commutation.** For any `SemiringWithMonusHom h : K → K'`
and any non-aggregating inner query `q`, evaluating the aggregation on
`h ⋆ d` is the same as evaluating on `d` and then mapping each K-tensor
coefficient through `h.toRingHom`. The aggregation operator therefore
inherits the "compile once, evaluate many" property already established
by `Query.evaluateAnnotated_hom` on the non-aggregating fragment. -/
theorem evaluateAggSum_hom (h : SemiringWithMonusHom K K')
    {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂)
    (q : Query T m) (hq : q.noAgg)
    (d : AnnotatedDatabase T K) :
    Query.evaluateAggSum is ts q hq (h.mapAnnotatedDatabase d)
      = (Query.evaluateAggSum is ts q hq d).map (Query.mapAggSumRow h) := by
  unfold Query.evaluateAggSum
  dsimp only []
  rw [Query.evaluateAnnotated_hom h q hq d]
  set r : AnnotatedRelation T K m := q.evaluateAnnotated hq d
  -- Push the outer `Multiset.map (Query.mapAggSumRow h)` on the RHS through.
  rw [Multiset.map_map]
  -- The dedup'd group keys agree on both sides: `mapAnnotatedRelation` only
  -- changes the K-side, but the group-key projection only reads `.fst`.
  have h_keys :
      Multiset.map (fun (p : Tuple T m × K') (k : Fin n₁) => p.1 (is k))
          (SemiringWithMonusHom.mapAnnotatedRelation h r)
        = Multiset.map (fun (p : Tuple T m × K) (k : Fin n₁) => p.1 (is k)) r := by
    show Multiset.map _
        (Multiset.map (SemiringWithMonusHom.mapAnnotatedTuple h) r) = _
    rw [Multiset.map_map]
    rfl
  rw [h_keys]
  -- The dedup'd group-key multisets are now equal; show the per-key bodies
  -- agree.
  apply Multiset.map_congr rfl
  intro g _
  -- Per-key: data side is `g`; for each aggregated column, the value and
  -- K-tensor are related by `h.toRingHom` on the K-coefficient only.
  unfold Query.aggSumRow Query.mapAggSumRow Function.comp
  -- The matching multisets on either side differ only by pushforward.
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
    Multiset.filter (fun p : AnnotatedTuple T K m => ∀ k' : Fin n₁, p.fst (is k') = g k') r
  refine Prod.ext rfl ?_
  funext k
  refine Prod.ext ?_ ?_
  · -- Aggregated value: data side unaffected by pushforward.
    show AggFunc.sum.eval
        ((SemiringWithMonusHom.mapAnnotatedRelation h matching).map
          (fun p => (ts k).eval p.fst))
        = AggFunc.sum.eval (matching.map (fun p => (ts k).eval p.fst))
    unfold SemiringWithMonusHom.mapAnnotatedRelation SemiringWithMonusHom.mapAnnotatedTuple
    rw [Multiset.map_map]
    rfl
  · -- Aggregated K-tensor: the K-coefficient is mapped through `h.toRingHom`.
    show (SemiringWithMonusHom.mapAnnotatedRelation h matching).map
            (fun p => (p.snd, (ts k).eval p.fst))
        = KTensor.mapHom h.toRingHom
            (matching.map (fun p => (p.snd, (ts k).eval p.fst)))
    unfold SemiringWithMonusHom.mapAnnotatedRelation SemiringWithMonusHom.mapAnnotatedTuple
            KTensor.mapHom
    simp only [Multiset.map_map]
    rfl

end Query
