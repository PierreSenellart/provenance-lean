import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.String.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fintype

import Provenance.Database
import Provenance.AnnotatedDatabase
import Provenance.Query
import Provenance.SemiringWithMonus

import Provenance.Semirings.Nat

instance : ValueType String where
  zero := ""

def r : Relation String 4 := Multiset.ofList [
  !["1", "John", "Director", "New York"],
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

def r_count := r.annotate (λ t ↦ match (t 0).toNat? with | none => 0 | some val => val)

def qPersonnel := (@Query.Rel String 4 "Personnel")

/- This query looks for distinct cities -/
def q₀ := ε (Π ![Term.Index 3] qPersonnel)

/- This query looks for cities with ≥2 persons -/
def q₁ := ε (
  Π ![Term.Index 3]
  (
    σ (Filter.BT (Term.Index 0 < Term.Index 4)) (
      (qPersonnel ⋈ (Filter.BT (Term.Index 3 == Term.Index 7))) qPersonnel
    )
  )
)

/- This query looks for cities with ≤1 persons -/
def q₂ := q₀ - q₁

#eval q₀.evaluate d
#eval q₁.evaluate d
#eval q₂.evaluate d
