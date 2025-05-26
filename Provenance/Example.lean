import Provenance.Database
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Single

instance : Zero String := ⟨""⟩

def r : Relation String 4 := Multiset.ofList [
  !["1","John","Director","New York"],
  !["2", "Paul", "Janitor", "New York"],
  !["3", "Dave", "Analyst", "Paris"],
  !["4", "Ellen", "Field agent", "Berlin"],
  !["5", "Magdalen", "Double agent", "Paris"],
  !["6", "Nancy", "HR", "Paris"],
  !["7", "Susan", "Analyst", "Berlin"]
]

def d : Database String where
  db := ⟨
    ⟨Multiset.ofList [(4,"Personnel")], by decide⟩,
    λ (n,s) ↦ match (n,s) with
      | (4,"Personnel") => ⟨4,r⟩
      | _ => 0,
    by
      intro ⟨n,s⟩
      by_cases h: (n,s)=(4,"Personnel")
      . simp[h]
        by_contra hc
        have : (⟨4,r⟩:(n:ℕ)× Relation String n).fst = 0 := by
          rw[hc]
          rfl
        simp at this
      . simp[h]
  ⟩

  wf := λ n s ↦ by
    by_cases h: (n,s)=(4,"Personnel")
    . simp[h]; simp at h; simp[h.left]
    . simp[h]
