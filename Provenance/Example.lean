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
  zero := "0"

instance: Add String where
  add s t := match s.toNat? with
  | none => ""
  | some n => match t.toNat? with
              | none => ""
              | some m => toString (n+m)

lemma toNat_toString : ∀ n : ℕ, (toString (n)).toNat? = some n := by
  intro n
  induction n with
  | zero =>
    have : toString (0) = "0":= by decide
    rw[this]
    simp[String.toNat?]
    constructor
    . admit
    . admit
  | succ n ih =>
    admit

instance: AddCommSemigroup String where
  add_comm := by
    intro a b
    have hes: "".toNat? = none := rfl
    by_cases ha: a.toNat?=none <;>
    by_cases hb: b.toNat?=none <;>
    simp[HAdd.hAdd] <;> simp only[Add.add] <;> try simp[ha,hb,hes]
    . cases hb': b.toNat? with
      | none => contradiction
      | some val => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala =>
        cases hb': b.toNat? with
        | none => contradiction
        | some valb =>
          simp
          rw[add_comm]

  add_assoc := by
    intro a b c
    have hes: "".toNat? = none := rfl
    by_cases ha: a.toNat?=none <;>
    by_cases hb: b.toNat?=none <;>
    by_cases hc: c.toNat?=none <;>
    simp[HAdd.hAdd] <;> simp only[Add.add] <;> try simp[ha,hb,hc,hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some val => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala =>
        cases hb': b.toNat? with
        | none => contradiction
        | some valb =>
          simp[hes]
          cases hx: (toString (vala+valb)).toNat? <;> simp[hx]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala =>
        cases hb': b.toNat? with
        | none => contradiction
        | some valb =>
          cases hc': c.toNat? with
          | none => contradiction
          | some valc =>
            simp[toNat_toString]
            rw[add_assoc]

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

def qj: Query String (8-(4: Fin 8)) → Query String 8 := qPersonnel ⋈ (Filter.BT (#3 == #7))
/- This query looks for cities with ≥2 persons -/
def q₁ := ε ( Π ![#3]
  (
    σ (Filter.BT (#0 < #4)) (
      qj qPersonnel
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

#eval! r_count
#eval! r_tropical
#eval! q₀.evaluateAnnotated (by decide) d_tropical
#eval! q₁.evaluateAnnotated (by decide) d_tropical
#eval! q₂.evaluateAnnotated (by decide) d_tropical
