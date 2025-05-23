import Std.Data.HashMap.Lemmas

import Provenance.AnnotatedDatabase
import Provenance.Query

variable {T: Type} [ValueType T]
variable {K: Type} [SemiringWithMonus K] [DecidableEq K]

def Filter.evalDecidableAnnotated (φ : Filter T n) :
  DecidablePred (λ (ta: AnnotatedTuple T K n) ↦ φ.eval ta.fst) :=
    λ t => match φ.evalDecidable t.fst with
      | isTrue h  => isTrue (by simp [Filter.eval, h])
      | isFalse h => isFalse  (by simp [Filter.eval, h])

instance [LinearOrder α] : DecidableRel (@LEByKey α β _ _) :=
  λ a b => match inferInstanceAs (Decidable (a.fst <= b.fst)) with
  | isTrue h => isTrue (by unfold LEByKey; assumption)
  | isFalse h => isFalse (by unfold LEByKey; assumption)

theorem find_ordered_insert_tuple (t : Tuple T n × K) (l : List (Tuple T n × K)) :
  (List.orderedInsert LEByKey t l).find? (·.fst=t.fst) = some t := by
    sorry


instance :
  LeftCommutative (addToList: Tuple T n × K → List (Tuple T n × K) → List (Tuple T n × K)) where
  left_comm := by
    intro (t₁,α₁) (t₂,α₂) l
    by_cases h : t₁=t₂
    . rw[h]
      induction l with
      | nil =>
        simp[addToList,h]
        exact add_comm _ _
      | cons hd tl ih =>
        simp[addToList]
        by_cases ht : hd.fst = t₂ <;> simp[ht]
        .

          exact add_right_comm hd.snd α₂ α₁
        . by_cases hlt : hd.fst < t₂
          . simp[hlt]
            exact add_comm _ _
          . simp[hlt,ht]
            exact ih
    . have h' : ¬ t₂=t₁ := fun a ↦ h (id (Eq.symm a))
      induction l with
      | nil =>
        simp[addToList,h,h']
        by_cases h₁₂ : t₁<t₂ <;> simp[h₁₂]
        . simp[le_of_lt h₁₂]
        . intro hle
          have : t₁=t₂ := by
            apply eq_of_le_of_le <;> assumption
          contradiction
      | cons hd tl ih =>
        simp[addToList]
        by_cases ht : hd.fst = t₂ <;> simp[ht]
        . simp[h']
          by_cases h₁₂ : t₂<t₁ <;> simp[h₁₂]
          . have hh  : addToList (t₂, α₂) tl = (t₂, hd.snd+α₂)::tl := by
              unfold addToList
              sorry
            have hh' : addToList (t₁, α₁) tl = (t₁,α₁) :: hd :: tl := by
              sorry
            rw[hh,hh'] at ih
            exact ih
          . sorry
        . sorry

def groupByKey (m : Multiset (Tuple T n × K)) :=
  m.foldr addToList []

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
