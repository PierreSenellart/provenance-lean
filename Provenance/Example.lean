import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fintype

import Provenance.QueryAnnotatedDatabase
import Provenance.QueryRewriting
import Provenance.SemiringWithMonus

import Provenance.Semirings.Nat
import Provenance.Semirings.Tropical

import Provenance.Util.ValueTypeString

def r : Relation String 4 := Multiset.ofList [
  !["1", "John", "Director", "New York"],
  !["2", "Paul", "Janitor", "New York"],
  !["3", "Dave", "Analyst", "Paris"],
  !["4", "Ellen", "Field agent", "Berlin"],
  !["5", "Magdalen", "Double agent", "Paris"],
  !["6", "Nancy", "HR", "Paris"],
  !["7", "Susan", "Analyst", "Berlin"]
]

def d : Database String := [("Personnel", ⟨4,r⟩)]

def qPersonnel := (@Query.Rel String 4 "Personnel")

/- This query looks for distinct cities -/
def q₀ := ε (Π ![#3] qPersonnel)

/- This query looks for cities with ≥2 persons -/
def q₁ := ε ( Π ![#3]
  (
    σ (Filter.BT (#0 < #4)) (
      Query.Sel (Filter.BT (#3 == #7))
        (@Query.Prod _ 4 8 (by decide) qPersonnel qPersonnel)
    )
  )
)

/- This query looks for cities with ≤1 persons -/
def q₂ := q₀ - q₁

/- This aggregate query counts persons by cities -/
def qc := Query.Agg ![3] ![Term.const "1"] ![AggFunc.sum] qPersonnel

#eval! q₀.evaluate d
#eval! q₁.evaluate d
#eval! q₂.evaluate d
#eval! qc.evaluate d

def r_count := r.annotate (λ _ ↦ 1)
def d_count : AnnotatedDatabase String ℕ := [("Personnel", ⟨4, r_count⟩)]

def r_tropical := r.annotate (λ _ ↦ (Tropical.trop 1: Tropical (WithTop ℕ)))
def d_tropical : AnnotatedDatabase String (Tropical (WithTop ℕ)) := [("Personnel", ⟨4, r_tropical⟩)]

#eval! r_count
#eval! q₀.evaluateAnnotated (by decide) d_count
#eval! q₁.evaluateAnnotated (by decide) d_count
#eval! q₂.evaluateAnnotated (by decide) d_count

#eval! (qPersonnel.rewriting (by decide)).evaluate d_count.toComposite
#eval! (q₀.rewriting (by decide)).evaluate d_count.toComposite
#eval! (q₁.rewriting (by decide)).evaluate d_count.toComposite
#eval! (q₂.rewriting (by decide)).evaluate d_count.toComposite
