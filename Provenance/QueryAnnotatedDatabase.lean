import Std.Data.HashMap.Lemmas

import Provenance.AnnotatedDatabase
import Provenance.Query
import Provenance.Util.KeyAccValueList

variable {T: Type} [ValueType T] [AddCommSemigroup T] [Sub T] [Mul T]
variable {K: Type} [SemiringWithMonus K] [DecidableEq K]

def Filter.evalDecidableAnnotated (φ : Filter T n) :
  DecidablePred (λ (ta: AnnotatedTuple T K n) ↦ φ.eval ta.fst) :=
    λ t => match φ.evalDecidable t.fst with
      | isTrue h  => isTrue (by simp [Filter.eval, h])
      | isFalse h => isFalse  (by simp [Filter.eval, h])

def groupByKey (m : Multiset (Tuple T n × K)) :=
  m.foldr KeyValueList.addKVFold ⟨[], by simp[KeyValueList]⟩

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
