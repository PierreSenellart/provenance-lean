/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.KSemiModule
import Provenance.QueryAnnotatedDatabase

/-!
# Annotated semantics of the aggregation operator

This file gives a first-cut formalisation of the aggregation operator
`Query.Agg` on `K`-annotated relations, following Section IV-B
(Definition 7) of [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]
and [Amsterdamer, Deutch & Tannen, *Provenance for aggregate queries*][amsterdamer2011aggregate].

Scope of this first cut:

* **Top-level aggregation only**. The inner query is `noAgg`; nested
  aggregations are not yet supported. This is the structure of the only
  aggregation example in the codebase (`Provenance.Example.qc`).
* **`AggFunc.sum` only**. The aggregation function is fixed to `sum`;
  other aggregation functions (currently none in `AggFunc`) are out of
  scope here.

For each group `g` (determined by the grouping indices `is`), the
evaluator produces one output row whose data part is `Fin.append g v`
(the grouping key plus the aggregated values `v`) and whose annotation
is, for each aggregated column `k`, a pair `(value, tensor)` where:

* `value : T` is `AggFunc.sum.eval` applied to the multiset of
  `(ts k).eval u` for `u` in the group;
* `tensor : KTensor K T` is the formal sum `∑_{(u, α) ∈ group} α ⊗ (ts k).eval u`,
  the K-tensor representation of Definition 7's annotation.

The bilinear quotient identifying `K ⊗ T` with Mathlib's `TensorProduct`
is not enforced in `KTensor`; the un-quotiented representation is what
the evaluator builds. Correctness theorems (commutation with random
worlds, with rewriting, etc.) will require either the quotient or
careful handling of bilinear equivalence; that work is deferred.

## References

* [Sen, Maniu & Senellart][sen2026provsql] (Section IV-B, Def. 7)
* [Amsterdamer, Deutch & Tannen][amsterdamer2011aggregate]
-/

namespace Query

variable {T : Type} [ValueType T] [AddCommSemigroup T] [Zero T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]

/-- The aggregator body for a fixed group key `g`: filter the inner relation
to tuples matching the grouping condition, then compute the per-aggregated-
column `(value, K-tensor)` pair. Factored out of `evaluateAggSum` to allow
proofs (notably hom commutation) to reason about the inner body separately
from the outer `dedup ∘ map` structure. -/
def aggSumRow {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂)
    (r : Multiset (Tuple T m × K))
    (g : Tuple T n₁) :
    Tuple T n₁ × Tuple (T × KTensor K T) n₂ :=
  (g, fun k =>
    (AggFunc.sum.eval ((r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
        (fun p => (ts k).eval p.fst)),
     (r.filter (fun p => ∀ k' : Fin n₁, p.fst (is k') = g k')).map
        (fun p => (p.snd, (ts k).eval p.fst))))

/-- Group-by + sum aggregation on a `K`-annotated relation.

Given a non-aggregating inner query `q` on an annotated database, an
indexing tuple `is` selecting the grouping columns, and a tuple of
aggregation terms `ts`, returns one row per distinct group key. Each
row carries:

* the group key (a `Tuple T n₁`);
* for each aggregated column `k`: the aggregated value
  `AggFunc.sum.eval (m.map (ts k).eval)` and the K-tensor annotation
  `∑_{(u, α) ∈ m} α ⊗ (ts k).eval u`, where `m` is the multiset of
  annotated tuples in the group.

This corresponds to `Query.Agg is ts ![AggFunc.sum, …, AggFunc.sum] q`
evaluated on the annotated database `d`, with the annotation in the
free formal-sum representation `KTensor K T`. -/
def evaluateAggSum
    {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂)
    (q : Query T m) (hq : q.noAgg)
    (d : AnnotatedDatabase T K) :
    Multiset (Tuple T n₁ × Tuple (T × KTensor K T) n₂) :=
  let r : Multiset (Tuple T m × K) := q.evaluateAnnotated hq d
  (Multiset.dedup (r.map (fun p => fun (k : Fin n₁) => p.fst (is k)))).map
    (Query.aggSumRow is ts r)

end Query
