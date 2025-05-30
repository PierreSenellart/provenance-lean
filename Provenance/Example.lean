import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.String.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fintype

import Provenance.QueryAnnotatedDatabase
import Provenance.SemiringWithMonus

import Provenance.Semirings.Nat
import Provenance.Semirings.Tropical

instance : ValueType String where
  zero := ""

instance: Add String where
  add s t := s ++ t

instance: Sub String where
  sub _ _ := ""

instance: Mul String where
  mul _ _ := ""

def r : Relation String 4 := Multiset.ofList [
  !["1", "John", "Director", "New York"],
  !["2", "Paul", "Janitor", "New York"],
  !["3", "Dave", "Analyst", "Paris"],
  !["4", "Ellen", "Field agent", "Berlin"],
  !["5", "Magdalen", "Double agent", "Paris"],
  !["6", "Nancy", "HR", "Paris"],
  !["7", "Susan", "Analyst", "Berlin"]
]

def d : WFDatabase String where
  db := [(4,"Personnel",⟨4,r⟩)]

  wf := λ n s rn ↦ by
    simp[Database.find, Database.find.f]
    intro hn hs hrn
    rw[← hrn]
    simp[hn]

def qPersonnel := (@Query.Rel String 4 "Personnel")

/- This query looks for distinct cities -/
def q₀ := ε (Π ![#3] qPersonnel)

/- This query looks for cities with ≥2 persons -/
def q₁ := ε (
  Π ![#3]
  (
    σ (Filter.BT (#0 < #4)) (
      (qPersonnel ⋈ (Filter.BT (#3 == #7))) qPersonnel
    )
  )
)

/- This query looks for cities with ≤1 persons -/
def q₂ := q₀ - q₁

#eval q₀.evaluate d
#eval q₁.evaluate d
#eval q₂.evaluate d

def r_count := r.annotate (λ _ ↦ 1)
def d_count : WFAnnotatedDatabase String ℕ where
  db := [(4,"Personnel",⟨4,r_count⟩)]

  wf := λ n s rn ↦ by
    simp[AnnotatedDatabase.find, AnnotatedDatabase.find.f]
    intro hn hs hrn
    rw[← hrn]
    simp[hn]

def r_tropical := r.annotate (λ _ ↦ (Tropical.trop 1: Tropical (WithTop ℕ)))
def d_tropical : WFAnnotatedDatabase String (Tropical (WithTop ℕ)) where
  db := [(4,"Personnel",⟨4,r_tropical⟩)]

  wf := λ n s rn ↦ by
    simp[AnnotatedDatabase.find, AnnotatedDatabase.find.f]
    intro hn hs hrn
    rw[← hrn]
    simp[hn]

#eval r_count
#eval r_tropical
#eval q₀.evaluateAnnotated d_tropical
#eval q₁.evaluateAnnotated d_tropical
#eval q₂.evaluateAnnotated d_tropical
