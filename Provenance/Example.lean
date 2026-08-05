import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fintype

import Provenance.QueryAnnotatedDatabase
import Provenance.AggQueryClosure
import Provenance.QueryRewriting
import Provenance.SemiringWithMonus

import Provenance.Semirings.Nat
import Provenance.Semirings.Tropical

import Provenance.Util.ValueTypeString


/-- A header line printed before an `#eval!`, so that the interleaved
output of this file stays readable. -/
private def hdr (s : String) : IO Unit := IO.println s!"\n── {s} ──"

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
    σ (Selection.BT (#0 < #4)) (
      Query.Sel (Selection.BT (#3 == #7))
        (@Query.Prod _ _ _ 8 (by decide) qPersonnel qPersonnel)
    )
  )
)

/- This query looks for cities with ≤1 persons -/
def q₂ := q₀ - q₁

#eval! hdr "plain: q₀ – distinct cities"
#eval! q₀.evaluate d
#eval! hdr "plain: q₁ – cities with ≥ 2 persons"
#eval! q₁.evaluate d
#eval! hdr "plain: q₂ = q₀ ∖ q₁ – cities with ≤ 1 person"
#eval! q₂.evaluate d

def r_count := r.annotate (λ _ ↦ 1)
def d_count : AnnotatedDatabase String ℕ := [("Personnel", ⟨4, r_count⟩)]

def r_tropical := r.annotate (λ _ ↦ (Tropical.trop 1: Tropical (WithTop ℕ)))
def d_tropical : AnnotatedDatabase String (Tropical (WithTop ℕ)) := [("Personnel", ⟨4, r_tropical⟩)]

#eval! hdr "input: Personnel annotated in ℕ (counting semiring)"
#eval! r_count
#eval! hdr "annotated ℕ: q₀"
#eval! q₀.evaluateAnnotated (by decide) d_count
#eval! hdr "annotated ℕ: q₁"
#eval! q₁.evaluateAnnotated (by decide) d_count
#eval! hdr "annotated ℕ: q₂"
#eval! q₂.evaluateAnnotated (by decide) d_count

#eval! hdr "rewritten (R1)–(R4), evaluated plainly: Personnel"
#eval! (qPersonnel.rewriting (by decide)).evaluate d_count.toComposite
#eval! hdr "rewritten (R1)–(R4), evaluated plainly: q₀"
#eval! (q₀.rewriting (by decide)).evaluate d_count.toComposite
#eval! hdr "rewritten (R1)–(R4), evaluated plainly: q₁"
#eval! (q₁.rewriting (by decide)).evaluate d_count.toComposite
#eval! hdr "rewritten (R1)–(R4), evaluated plainly: q₂"
#eval! (q₂.rewriting (by decide)).evaluate d_count.toComposite

/-! ### The general (kind-indexed) syntax and its rewriting

The same database, now through `AggQuery`: aggregation, `HAVING`, and the
rewriting of both into the composite domain `String ⊕ ℕ`. -/

def qgPersonnel : AggQuery String 4 (ColKind.allReg 4) :=
  AggQuery.Rel 4 "Personnel"

/- This query counts persons by city: `γ_{city}[1 : SUM]`. Its output has
one regular column (the group key) and one *aggregate-token* column. -/
def qgCount := AggQuery.Gamma ![3] ![Term.const "1"] ![SeqAggFunc.sum]
  qgPersonnel

/- `HAVING COUNT(*) = 2`, as a two-atom aggregate predicate. -/
def φexactlyTwo : GenPred String (ColKind.gammaKinds 1 1) :=
  GenPred.and (GenPred.fusedCmp CompOp.ge 0 (Term.const "2"))
    (GenPred.fusedCmp CompOp.le 0 (Term.const "2"))

/- `HAVING COUNT(*) ≥ 3`, a single-atom one. -/
def φatLeastThree : GenPred String (ColKind.gammaKinds 1 1) :=
  GenPred.fusedCmp CompOp.ge 0 (Term.const "3")

example : φexactlyTwo.aggOnly = true := rfl

/- Plain semantics: a `HAVING` selection filters, so Paris (3 persons) is
gone. -/
#eval! hdr "AggQuery plain: HAVING COUNT(*) = 2"
#eval! (AggQuery.Sel φexactlyTwo qgCount).evaluatePlain d

/- Annotated semantics: the aggregate token collapses to the actual-world
count, and the row *survives* with annotation `𝟘` – exactly as ProvSQL
emits it, since in other possible worlds Paris may well have two
persons. -/
#eval! hdr "AggQuery annotated ℕ: HAVING COUNT(*) = 2"
#eval! ((AggQuery.Sel φexactlyTwo qgCount).evaluateAnnotated d_count
  : AnnotatedRelation String ℕ 2)

/- Projecting the group key out of a grouping, of a `HAVING` site, and
their difference: the cities with fewer than three persons. -/
def cityCols : Tuple (ProjCol String (ColKind.gammaKinds 1 1)) 1 :=
  fun _ => ProjCol.term (TermG.index (Fin.castAdd 1 0)
    (Fin.append_left (fun _ : Fin 1 => ColKind.reg)
      (fun _ : Fin 1 => ColKind.agg) 0))

def qgAllCities : AggQuery String 1 (ColKind.allReg 1) :=
  AggQuery.Proj cityCols qgCount
def qgBigCities : AggQuery String 1 (ColKind.allReg 1) :=
  AggQuery.Proj cityCols (AggQuery.Sel φatLeastThree qgCount)
def qgSmallCities := AggQuery.Diff qgAllCities qgBigCities

#eval! hdr "AggQuery annotated ℕ: all cities"
#eval! (qgAllCities.evaluateAnnotated d_count : AnnotatedRelation String ℕ 1)
#eval! hdr "AggQuery annotated ℕ: cities with ≥ 3 persons"
#eval! (qgBigCities.evaluateAnnotated d_count : AnnotatedRelation String ℕ 1)
#eval! hdr "AggQuery annotated ℕ: cities with < 3 persons"
#eval! (qgSmallCities.evaluateAnnotated d_count
  : AnnotatedRelation String ℕ 1)

/- The rewritten world. `AggQuery.gammaRew` is the bare grouping – ProvSQL's
`provsql_agg` over the rewritten subquery – whose provenance column carries
the group-existence guard `δ(⊕ U)`; `AggQuery.havingPredRew` replaces that
guard by the `provsql_having` gate of the predicate. Rows are printed
through `AggValue.collapseSum`, which reads each aggregate token as its
actual-world value. -/
def qgCountRew : AggQuery (String ⊕ ℕ) 3 (ColKind.gammaRewKinds 1 1) :=
  AggQuery.gammaRew ![3] ![Term.const "1"] ![SeqAggFunc.sum] qgPersonnel
    trivial

def qgHavingRew : AggQuery (String ⊕ ℕ) 3 (ColKind.gammaRewKinds 1 1) :=
  AggQuery.havingPredRew ![3] ![Term.const "1"] ![SeqAggFunc.sum]
    φexactlyTwo qgPersonnel trivial

#eval! hdr "rewritten: bare GROUP BY (gammaRew), guard δ(⊕ U) in the last column"
#eval! (qgCountRew.evaluateRew d_count.toComposite).map
  (fun u => (fun k => AggValue.collapseSum (u k) : Tuple (String ⊕ ℕ) 3))
#eval! hdr "rewritten: HAVING COUNT(*) = 2 (havingPredRew), gate in the last column"
#eval! (qgHavingRew.evaluateRew d_count.toComposite).map
  (fun u => (fun k => AggValue.collapseSum (u k) : Tuple (String ⊕ ℕ) 3))

/- A `HAVING` predicate mixing a *regular* atom into the aggregate one:
`HAVING COUNT(*) ≥ 3 OR city = 'Berlin'`. The regular atom becomes an
indicator gate, `⊕`-ed with the `provsql_having` gate of the aggregate
one. Since a regular atom can fire in worlds where the group is empty,
the predicate no longer entails the group's existence, and the guard
`δ(⊕ U)` therefore survives as a factor of the provenance column instead
of being superseded. -/
def φbigOrBerlin : GenPred String (ColKind.gammaKinds 1 1) :=
  GenPred.or (GenPred.fusedCmp CompOp.ge 0 (Term.const "3"))
    (GenPred.cmp CompOp.eq
      (TermG.index (Fin.castAdd 1 0)
        (Fin.append_left (fun _ : Fin 1 => ColKind.reg)
          (fun _ : Fin 1 => ColKind.agg) 0))
      (TermG.const "Berlin"))

example : φbigOrBerlin.hasAggAtom = true := rfl
example : φbigOrBerlin.aggOnly = false := rfl
example : φbigOrBerlin.entailsExistence false = false := rfl

def qgMixedRew : AggQuery (String ⊕ ℕ) 3 (ColKind.gammaRewKinds 1 1) :=
  AggQuery.havingPredRew ![3] ![Term.const "1"] ![SeqAggFunc.sum]
    φbigOrBerlin qgPersonnel trivial

#eval! hdr "AggQuery annotated ℕ: HAVING COUNT(*) ≥ 3 OR city = 'Berlin'"
#eval! ((AggQuery.Sel φbigOrBerlin qgCount).evaluateAnnotated d_count
  : AnnotatedRelation String ℕ 2)
#eval! hdr "rewritten: the same mixed predicate, gate ⊗ guard in the last column"
#eval! (qgMixedRew.evaluateRew d_count.toComposite).map
  (fun u => (fun k => AggValue.collapseSum (u k) : Tuple (String ⊕ ℕ) 3))

/- The compositional closure applies to the whole difference query: its
derivation composes the bare-grouping rule, the `HAVING`-site rule, a
projection and a difference, and `AggQuery.rewritesTo_valid` transports
the correctness to it. -/
example : ∃ q' : AggQuery (String ⊕ ℕ) 2
      (ColKind.rewKindsOf (ColKind.allReg 1)),
    AggQuery.RewritesTo qgSmallCities q'
      ∧ (qgSmallCities.evaluate d_count).map GenRow.toCompositeRow
          = q'.evaluateRew d_count.toComposite :=
  let h := AggQuery.RewritesTo.diff
    (AggQuery.RewritesTo.proj cityCols
      (AggQuery.RewritesTo.gamma ![3] ![Term.const "1"] ![SeqAggFunc.sum]
        qgPersonnel trivial))
    (AggQuery.RewritesTo.proj cityCols
      (AggQuery.RewritesTo.havingPred ![3] ![Term.const "1"]
        ![SeqAggFunc.sum] φatLeastThree rfl qgPersonnel trivial))
  ⟨_, h, AggQuery.rewritesTo_valid h d_count⟩
