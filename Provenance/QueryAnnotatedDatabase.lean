import Std.Data.HashMap.Lemmas

import Provenance.AnnotatedDatabase
import Provenance.Query

section QueryAnnotatedDatabase

variable {T: Type} [ValueType T] [DecidableEq T] [DecidableLE T]
variable {K: Type} [SemiringWithMonus K]

def Filter.evalDecidableAnnotated (φ : Filter T n) :
  DecidablePred (λ (ta: AnnotatedTuple T K n) ↦ φ.eval ta.fst) :=
    λ t => match φ.evalDecidable t.fst with
      | isTrue h  => isTrue (by simp [Filter.eval, h])
      | isFalse h => isFalse  (by simp [Filter.eval, h])

def addToList (ta: Tuple T n × K) (acc: List (Tuple T n × K)) := match acc with
| [] => [ta]
| ua::q =>
  if ua.fst=ta.fst then
    ⟨ua.fst,ua.snd+ta.snd⟩::q
  else if ua.fst<ta.fst then
    ta::acc
  else
    ua::(addToList ta q)

def findInList (t : Tuple T n) (l : List (Tuple T n × K)) (default: K) := match l with
| [] => default
| ua::q => if ua.fst=t then ua.snd else findInList t q default

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
        . unfold addToList
          simp
          exact add_right_comm hd.snd α₂ α₁
        . unfold addToList
          simp[ht]
          by_cases hlt : hd.fst < t₂
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
    λ (u,α) ↦ ⟨u, α - (findInList u grouped₂ 0)⟩

end QueryAnnotatedDatabase
