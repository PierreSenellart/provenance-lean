import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fintype

import Provenance.QueryAnnotatedDatabase
import Provenance.AggQueryClosure
import Provenance.QueryRewriting
import Provenance.Notation
import Provenance.OrderSpec
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
        (qPersonnel × qPersonnel)
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

def r_tropical := r.annotate (λ _ ↦ (MinTropical.trop 1: MinTropical (WithTop ℕ)))
def d_tropical : AnnotatedDatabase String (MinTropical (WithTop ℕ)) := [("Personnel", ⟨4, r_tropical⟩)]

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
  GenPredIn.and (GenPredIn.fusedCmp CompOp.ge 0 (Term.const "2"))
    (GenPredIn.fusedCmp CompOp.le 0 (Term.const "2"))

/- `HAVING COUNT(*) ≥ 3`, a single-atom one. -/
def φatLeastThree : GenPred String (ColKind.gammaKinds 1 1) :=
  GenPredIn.fusedCmp CompOp.ge 0 (Term.const "3")

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
  fun _ => ProjColIn.term (TermGIn.index (Fin.castAdd 1 0)
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
  GenPredIn.or (GenPredIn.fusedCmp CompOp.ge 0 (Term.const "3"))
    (GenPredIn.cmp CompOp.eq
      (TermGIn.index (Fin.castAdd 1 0)
        (Fin.append_left (fun _ : Fin 1 => ColKind.reg)
          (fun _ : Fin 1 => ColKind.agg) 0))
      (TermGIn.const "Berlin"))

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

/-! ### A window

`SUM(1) OVER (PARTITION BY city)` – the size of each city's group, given to
every row of that city. A window removes no row and merges none, so the
answer has as many rows as the input and every row keeps the annotation it
came with: no group is created, so no group-existence factor arises. -/

open Provenance.Notation in
def qwCity := RA[String |
  ⊞[#3 ; ; OrderSpec.unordered ; ValueFrame.whole ;
    `("1") : SeqAggFunc.sum] rel 4 "Personnel" ]

#eval! hdr "plain: SUM(1) OVER (PARTITION BY city)"
#eval! qwCity.evaluatePlain d
#eval! hdr "annotated ℕ: the same window, every row keeping its annotation"
#eval! (qwCity.evaluateAnnotated d_count : AnnotatedRelation String ℕ 5)

/-! The rows strictly before the current row's peers: a frame that contains
neither the row nor its equals, so it can be empty in a world where the row
is present. Its token is therefore read in the scalar convention, and the
first row of each city aggregates over nothing. -/

open Provenance.Notation in
def qwRunning := RA[String |
  ⊞[#3 ; #0 ; OrderSpec.asc 1 ; ValueFrame.rangeBefore (OrderSpec.asc 1) ;
    `("1") : SeqAggFunc.sum] rel 4 "Personnel" ]

#eval! hdr "plain: a running count over the rows strictly before, per city"
#eval! qwRunning.evaluatePlain d

/-! ### An aggregate over no row

With a null in the value domain, `SUM` over no row is `NULL`, as SQL has it,
and not the zero the domain happened to offer. A window is where that
becomes reachable on ordinary data: under the frame of the rows strictly
before, the first row of each city aggregates over nothing. -/

def rNull : Relation (WithNull String) 4 :=
  Multiset.map (fun (u : Tuple String 4) (k : Fin 4) => WithNull.val (u k)) r

def dNull : Database (WithNull String) := [("Personnel", ⟨4, rNull⟩)]

open Provenance.Notation in
def qwRunningNull := RA[WithNull String |
  ⊞[#3 ; #0 ; OrderSpec.asc 1 ; ValueFrame.rangeBefore (OrderSpec.asc 1) ;
    `(WithNull.val "1") : SeqAggFunc.sum.sqlOf] rel 4 "Personnel" ]

#eval! hdr "plain: SUM over the rows strictly before – NULL where there are none"
#eval! qwRunningNull.evaluatePlain dNull

/-! ### Where the nulls go is the clause's business

Three rows of one city, one of them with a null id. The frame is the same
in both queries below – the rows strictly before the current row's peers –
and so is the data; only the `ORDER BY` differs, in where it places the
null. The running counts come out different, which is the point: the
domain's own order has nothing to say about it, and a frame stated against
that order cannot express either reading. -/

def rOrdNull : Relation (WithNull String) 4 := Multiset.ofList [
  ![WithNull.val "1", WithNull.val "John", WithNull.val "Director",
    WithNull.val "New York"],
  ![WithNull.nil, WithNull.val "Paul", WithNull.val "Janitor",
    WithNull.val "New York"],
  ![WithNull.val "2", WithNull.val "Ann", WithNull.val "Analyst",
    WithNull.val "New York"]
]

def dOrdNull : Database (WithNull String) := [("Personnel", ⟨4, rOrdNull⟩)]

/-- `ORDER BY id ASC NULLS LAST`: the null row is counted last. -/
def ascNullsLast : OrderSpec 1 := fun _ => OrderCol.ASC

/-- `ORDER BY id ASC NULLS FIRST`: the null row is counted first. -/
def ascNullsFirst : OrderSpec 1 :=
  fun _ => { OrderCol.ASC with nullsFirst := true }

open Provenance.Notation in
def qwNullsLast := RA[WithNull String |
  ⊞[#3 ; #0 ; ascNullsLast ; ValueFrame.rangeBefore ascNullsLast ;
    `(WithNull.val "1") : SeqAggFunc.sum.sqlOf] rel 4 "Personnel" ]

open Provenance.Notation in
def qwNullsFirst := RA[WithNull String |
  ⊞[#3 ; #0 ; ascNullsFirst ; ValueFrame.rangeBefore ascNullsFirst ;
    `(WithNull.val "1") : SeqAggFunc.sum.sqlOf] rel 4 "Personnel" ]

#eval! hdr "plain: running count, ORDER BY id ASC NULLS LAST"
#eval! qwNullsLast.evaluatePlain dOrdNull
#eval! hdr "plain: running count, ORDER BY id ASC NULLS FIRST"
#eval! qwNullsFirst.evaluatePlain dOrdNull
