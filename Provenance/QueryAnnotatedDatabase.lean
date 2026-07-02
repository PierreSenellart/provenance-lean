import Std.Data.HashMap.Lemmas

import Provenance.AnnotatedDatabase
import Provenance.Query
import Provenance.Util.KeyAccValueList

/-!
# Query semantics over annotated databases

This file defines the evaluation of relational algebra queries over annotated databases.
Query operators are lifted to annotated relations using the m-semiring operations of the
annotation domain `K`: addition corresponds to union, multiplication to join, and
monus to difference. This is the algebra of Section IV-B of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql], itself an adaptation of
[Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance] to
multiset semantics with explicit duplicate elimination and multiset difference.

## Main definitions

* `Query.evaluateAnnotated` – evaluates a query over an `AnnotatedDatabase T K`,
  propagating annotations through each relational operator according to the semiring
  structure of `K`

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section IV-B)
* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
-/

variable {T: Type} [ValueType T] [AddCommSemigroup T] [Sub T] [Mul T]
variable {K: Type} [SemiringWithMonus K] [DecidableEq K]

@[reducible] def Filter.evalDecidableAnnotated (φ : Filter T n) :
  DecidablePred (λ (ta: AnnotatedTuple T K n) ↦ φ.eval ta.fst) :=
    λ t => match φ.evalDecidable t.fst with
      | isTrue h  => isTrue (by simp [h])
      | isFalse h => isFalse  (by simp [h])

def groupByKey (m : Multiset (Tuple T n × K)) :=
  m.foldr KeyValueList.addKVFold ⟨[], by simp[KeyValueList]⟩

/-- Annotated (m-semiring) semantics of a non-aggregation query.

The `Diff` case follows ProvSQL: every tuple slot `(u, α)` of `r₁` is *kept*,
with its annotation rewritten to `α ⊖ Σ β` where `Σ β` is the semiring sum of
the annotations of all copies of `u` in `r₂`. Two consequences worth noting:

* difference never removes tuple slots (only annotations change, possibly to
  `0`), so the data part of the result is insensitive to `Diff` – this is
  made precise in `Provenance.QueryAdequacy`;
* each copy of `u` in `r₁` separately gets the full grouped sum subtracted,
  so the result is not invariant under regrouping extensionally equal
  annotated relations: over `ℕ`, `{(t,1),(t,1)} ∖ {(t,1)}` has total
  annotation `0` while `{(t,2)} ∖ {(t,1)}` has total annotation `1`. As a
  consequence, over `ℕ` the annotated semantics agrees with the
  all-or-nothing plain difference of `Query.evaluate` on `0`/`1`-annotated
  inputs, but not once `Dedup` has accumulated annotations
  (see `Nat.counterexample_diff_adequacy`). -/
def Query.evaluateAnnotated (q: Query T n) (hq: q.noAgg) (d: AnnotatedDatabase T K) : AnnotatedRelation T K n := match q with
| Rel   n  s  =>
  match h : d.find n s with
  | none => (∅: Multiset (AnnotatedTuple T K n))
  | some rn => rn
| @Proj _ n m ts q' =>
  let r := evaluateAnnotated q' (noAggProj hq rfl) d
  r.map (λ t ↦ ⟨λ k ↦ (ts k).eval t.fst, t.snd⟩)
| Sel   φ  q  =>
  let r := evaluateAnnotated q (noAggSel hq rfl) d
  @Multiset.filter _ (λ ta ↦ φ.eval ta.fst) φ.evalDecidableAnnotated r
| @Prod _ n₁ n₂ n hn q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (noAggProd hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (noAggProd hq rfl).right d
  Multiset.map (λ (x,y) ↦ ⟨
    Eq.mp (by simp[hn]; rfl)
    (Fin.append x.fst y.fst),
    x.snd*y.snd
  ⟩) (Multiset.product r₁ r₂)
| Sum   q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (noAggSum hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (noAggSum hq rfl).right d
  r₁+r₂
| Dedup q     =>
  let r := evaluateAnnotated q (noAggDedup hq rfl) d
  Multiset.ofList ((groupByKey r).val)
| Diff  q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (noAggDiff hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (noAggDiff hq rfl).right d
  let grouped₂ := groupByKey r₂
  r₁.map
    λ (u,α) ↦ ⟨u, α - (((grouped₂.val.find? (·.1=u)).map Prod.snd).getD 0)⟩
| Agg _ _ _ _ => False.elim (by
  simp[noAgg] at hq
)
