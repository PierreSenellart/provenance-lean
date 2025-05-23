import Std.Data.HashMap.Lemmas

import Provenance.AnnotatedDatabase
import Provenance.Query
import Provenance.Util.KeyAccValueList

variable {T: Type} [ValueType T]
variable {K: Type} [SemiringWithMonus K] [DecidableEq K]

def Filter.evalDecidableAnnotated (φ : Filter T n) :
  DecidablePred (λ (ta: AnnotatedTuple T K n) ↦ φ.eval ta.fst) :=
    λ t => match φ.evalDecidable t.fst with
      | isTrue h  => isTrue (by simp [Filter.eval, h])
      | isFalse h => isFalse  (by simp [Filter.eval, h])

def groupByKey (m : Multiset (Tuple T n × K)) :=
  m.foldr  []

def Query.evaluateAnnotated (q: Query T n) (d: AnnotatedDatabase T K) : AnnotatedRelation T K n := match q with
| Rel   n  s  => Eq.mp (congrArg (AnnotatedRelation T K) (d.wf n s)) (d (n,s)).snd
| Proj ts q =>
  let r := evaluateAnnotated q d
  r.map (λ t ↦ ⟨Vector.map (λ u ↦ u.eval t.fst) ts, t.snd⟩)
| Sel   φ  q  =>
  let r := evaluateAnnotated q d
  @Multiset.filter _ (λ ta ↦ φ.eval ta.fst) φ.evalDecidableAnnotated r
| Prod  q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ d
  let r₂ := evaluateAnnotated q₂ d
  Multiset.map (λ (x,y) ↦ ⟨Vector.append x.fst y.fst, x.snd*y.snd⟩) (Multiset.product r₁ r₂)
| Sum   q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ d
  let r₂ := evaluateAnnotated q₂ d
  r₁+r₂
| Dedup q     =>
  let r := evaluateAnnotated q d
  Multiset.ofList (groupByKey r)
| Diff  q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ d
  let r₂ := evaluateAnnotated q₂ d
  let grouped₂ := groupByKey r₂
  r₁.map
    λ (u,α) ↦ ⟨u, α - (grouped₂.find? u 0)⟩
