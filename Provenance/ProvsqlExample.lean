/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.DerivedAnn
import Provenance.Probability
import Provenance.Semirings.BoolFunc

/-!
# A worked query against ProvSQL's own answer

A left outer join of three departments with three employees, a rank and
an average over each department, and the three rows a total order and
`LIMIT 3` keep. ProvSQL computes the provenance of each candidate row on
this instance; everything below is that answer, checked in the kernel.
What it checks is the *system's* output and not the semantics alone, so a
disagreement is a finding about one of the two and not something to
fit.

**What is checked.** `q1_data` gives the six candidate rows; `q1_ann` and
`q2_ann` give their annotations as Boolean functions of the six tokens,
compared against ProvSQL's `sr_boolexpr` at all `64` valuations; and
`world_all`, `world_noA1`, `world_noB1` give the two window values on
each row in three worlds, by evaluating the windows plainly on that
world's instance.

**What had to be encoded differently, and why.**

* The two window columns are **two queries** here. `AggQueryIn.Win` takes
  an all-regular input, so a second window column cannot be added to a
  relation that already holds one: `rank() OVER …, avg(…) OVER …` in one
  `SELECT` is not in this syntax. Each window is read separately over the
  join.
* The `LIMIT` is taken **on the join**, before the windows, for the same
  reason: a truncation ranks its input, and the input of a rank is
  all-regular. It keeps the same rows here, the order reading only
  regular columns, and in the three worlds below the partitions it leaves
  are the ones SQL's windows read.
* The query is spelled in the core syntax rather than through
  `AggQueryIn.leftOuter` and `AggQueryIn.truncate`: those carry
  `AggQueryIn.castKind`, and a cast along a proof is what the kernel
  cannot reduce. Writing each projection's columns as a *function* of the
  column index keeps the kinds constant by reduction.
* `𝔹[X]` had to be made computable: the library's `DecidableEq (BoolFunc X)`
  is `Classical.decEq` and there is no linear order on `BoolFunc X` at
  all, so no annotated evaluation over it could be reduced. Both come
  from the truth table here, as local instances.
* Values are numbers: departments `1, 2, 3`, names `10, 20, 30`,
  identifiers `101, 102, 201`, salaries as they are. The domain is
  `WithNull ℕ`, the nulls being what the padded rows carry.

**Agreement.** Every row's annotation is ProvSQL's, as a Boolean
function. The one place the two readings are worded differently is the
average of a padded row: ProvSQL prints `NaN`, which it takes for a
display artefact, and the semantics says null – `world_noB1`.
-/

namespace ProvsqlExample

/-! The six tokens: dA, dB, dC, a1, a2, b1. -/
abbrev X := Fin 6
abbrev dA : X := 0
abbrev dB : X := 1
abbrev dC : X := 2
abbrev ta1 : X := 3
abbrev ta2 : X := 4
abbrev tb1 : X := 5

abbrev K := BoolFunc X

/-! ### Boolean functions of six variables, computably

The library's `DecidableEq (BoolFunc X)` is `Classical.decEq`, which the
kernel cannot reduce, and there is no linear order on `BoolFunc X` at all
– so an annotated evaluation over `𝔹[X]` cannot be computed. Both come
from the truth table here: a function of six variables is its 64 values,
and a list of booleans is ordered and has decidable equality. -/

/-- The valuation whose bits are those of `k`. -/
def valOf (k : ℕ) : X → Bool := fun i => Nat.testBit k (i : ℕ)

/-- The truth table of a Boolean function of the six tokens. -/
def table (f : K) : List Bool := (List.range 64).map (fun k => f (valOf k))

set_option maxRecDepth 100000 in
theorem valOf_surj : ∀ v : X → Bool, ∃ k : Fin 64, valOf (k : ℕ) = v := by
  decide

theorem table_inj : Function.Injective table := by
  intro f g h
  funext v
  obtain ⟨k, rfl⟩ := valOf_surj v
  have hget := congrArg (fun l : List Bool => l[(k : ℕ)]?) h
  simp only [table, List.getElem?_map, List.getElem?_range k.isLt] at hget
  exact Option.some.inj hget

/-- The order the group and frame sorts read annotations in. -/
local instance (priority := 3000) : HasAltLinearOrder K :=
  ⟨LinearOrder.lift' table table_inj⟩

local instance (priority := 3000) decEqK : DecidableEq K := fun f g =>
  decidable_of_iff (table f = table g)
    ⟨fun h => table_inj h, fun h => h ▸ rfl⟩
abbrev V := WithNull ℕ

/-- `A ↦ 1, B ↦ 2, C ↦ 3`; names `10, 20, 30`; ids `101, 102, 201`. -/
abbrev dept : AnnotatedRelation V K 2 :=
  (([(![WithNull.val 1, WithNull.val 10], BoolFunc.var dA),
     (![WithNull.val 2, WithNull.val 20], BoolFunc.var dB),
     (![WithNull.val 3, WithNull.val 30], BoolFunc.var dC)]
    : List (AnnotatedTuple V K 2)) : Multiset _)

abbrev emp : AnnotatedRelation V K 3 :=
  (([(![WithNull.val 101, WithNull.val 1, WithNull.val 100], BoolFunc.var ta1),
     (![WithNull.val 102, WithNull.val 1, WithNull.val 90], BoolFunc.var ta2),
     (![WithNull.val 201, WithNull.val 2, WithNull.val 120], BoolFunc.var tb1)]
    : List (AnnotatedTuple V K 3)) : Multiset _)

abbrev db : AnnotatedDatabase V K := [("Dept", ⟨2, dept⟩), ("Emp", ⟨3, emp⟩)]

/-! ### The query

`dept LEFT JOIN emp ON e.dept = d.dept`, spelled in the core syntax
rather than through `AggQueryIn.leftOuter`: the derived form carries
`AggQueryIn.castKind`, and a cast along a proof is what the kernel cannot
reduce, so a `decide` through it is impossible. Writing each projection's
column family as a *function* of the column index keeps the kinds
constant by reduction, which is what lets the two arms meet and the whole
query evaluate in the kernel.

The five columns are `d.dept, d.name, e.id, e.dept, e.salary`. -/

/-- `e.dept = d.dept`, over the product's kinds. -/
abbrev joinOn :
    GenPred V (Fin.append (ColKind.allReg 2) (ColKind.allReg 3)) :=
  GenPredIn.cmp CompOp.eq (TermGIn.index 3 rfl) (TermGIn.index 0 rfl)

/-- The identity projection on the five columns, which brings the kinds
to the constant form the other arm has. -/
abbrev idCols :
    Tuple (ProjColIn V 0
      (Fin.append (ColKind.allReg 2) (ColKind.allReg 3))) 5 :=
  fun j => ProjColIn.term (TermGIn.index j
    (congrFun (AggQueryIn.append_allReg 2 3) j))

/-- The matching pairs. -/
abbrev innerJ : AggQuery V 5 (ColKind.allReg 5) :=
  AggQueryIn.Proj idCols (AggQueryIn.Sel joinOn
    (AggQueryIn.Prod (AggQueryIn.Rel 2 "Dept") (AggQueryIn.Rel 3 "Emp")))

/-- The two department columns of a join row. -/
abbrev firstTwo : Tuple (ProjColIn V 0 (ColKind.allReg 5)) 2 :=
  fun i => ProjColIn.term (TermGIn.index (Fin.castAdd 3 i) rfl)

/-- The departments with no employee. -/
abbrev unmatchedQ : AggQuery V 2 (ColKind.allReg 2) :=
  AggQueryIn.Diff (AggQueryIn.Rel 2 "Dept")
    (AggQueryIn.Proj firstTwo innerJ)

/-- Padding such a department with three nulls. -/
abbrev padTo5 : Tuple (ProjColIn V 0 (ColKind.allReg 2)) 5 :=
  fun j => ProjColIn.term (Fin.addCases
    (fun i : Fin 2 => TermGIn.index i rfl)
    (fun _ : Fin 3 => TermGIn.const WithNull.nil) j)

/-- `dept LEFT JOIN emp ON e.dept = d.dept`. -/
abbrev q1 : AggQuery V 5 (ColKind.allReg 5) :=
  AggQueryIn.Sum innerJ (AggQueryIn.Proj padTo5 unmatchedQ)

open WithNull in
/-- The six candidate rows: the three matches and one padded row per
department. -/
theorem q1_data :
    (q1.evaluateAnnotated db).map
        (fun p => (p.1 0, p.1 1, p.1 2, p.1 3, p.1 4))
      = ((([(val 2, val 20, val 201, val 2, val 120),
            (val 1, val 10, val 101, val 1, val 100),
            (val 1, val 10, val 102, val 1, val 90),
            (val 1, val 10, nil, nil, nil),
            (val 2, val 20, nil, nil, nil),
            (val 3, val 30, nil, nil, nil)]
          : List (V × V × V × V × V))) : Multiset _) := by
  decide

set_option maxHeartbeats 2000000 in
open WithNull in
/-- **The annotations of the six candidates**, as Boolean functions of the
six tokens: a match by the product, a padded row by the department's own
token minus its matches. Each row is named by `(d.dept, e.id)`. -/
theorem q1_ann : ∀ v : X → Bool,
    (q1.evaluateAnnotated db).map (fun p => ((p.1 0, p.1 2), p.2 v))
      = ((([((val 2, val 201), v dB && v tb1),
            ((val 1, val 101), v dA && v ta1),
            ((val 1, val 102), v dA && v ta2),
            ((val 1, nil), v dA && !(v ta1) && !(v ta2)),
            ((val 2, nil), v dB && !(v tb1)),
            ((val 3, nil), v dC)]
          : List ((V × V) × Bool))) : Multiset _) := by
  decide

/-! ### The `ORDER BY … LIMIT 3`

`ORDER BY e.salary DESC NULLS LAST, e.id, d.dept`, keeping the first
three rows. The truncation is spelled by hand rather than through
`AggQueryIn.truncate`: that one goes through `rank`, whose column is
`1 + count` and whose kinds need `AggQueryIn.castKind`, and a cast along
a proof is what the kernel cannot reduce. Counting the rows that sort
*ahead* and keeping `≤ 2` is the same condition as `rank ≤ 3`, and needs
no cast. -/

local instance : One V := ⟨WithNull.val 1⟩

/-- The counting aggregate: how many rows the frame holds. -/
abbrev cnt : SeqAggFunc V := fun l => WithNull.val l.length

/-- `salary DESC NULLS LAST, id ASC, dept ASC`. -/
abbrev ord3 : OrderSpec 3 :=
  ![{ desc := true, nullsFirst := false }, OrderCol.ASC, OrderCol.ASC]

/-- The three order columns: `e.salary`, `e.id`, `d.dept`. -/
abbrev ocols : Tuple (Fin 5) 3 := ![4, 2, 0]

/-- How many rows sort strictly ahead of a row's peers: `rank - 1`. -/
abbrev aheadQ : AggQueryIn V 0 6 (Fin.snoc (ColKind.allReg 5) ColKind.agg) :=
  AggQueryIn.Win (fun k : Fin 0 => k.elim0) ocols ord3
    (ValueFrame.rangeBefore ord3) (TermIn.const 1) cnt q1
    (winReadsReg_allReg _ _ _)

/-- `LIMIT 3`: at most two rows ahead. -/
abbrev keep3 : GenPred V (Fin.snoc (ColKind.allReg 5) ColKind.agg) :=
  GenPredIn.aggCmp (Fin.last 5) (Fin.snoc_last _ _) CompOp.le
    (TermGIn.const (WithNull.val 2))

/-- Dropping the counting column again. -/
abbrev dropCount :
    Tuple (ProjColIn V 0 (Fin.snoc (ColKind.allReg 5) ColKind.agg)) 5 :=
  fun j => ProjColIn.term (TermGIn.index j.castSucc (by
    rw [Fin.snoc_castSucc]; rfl))

/-- The whole query but for its output columns. -/
abbrev q2 : AggQuery V 5 (ColKind.allReg 5) :=
  AggQueryIn.Proj dropCount (AggQueryIn.Sel keep3 aheadQ)

set_option maxHeartbeats 4000000 in
open WithNull in
/-- **The three rows SQL returns**, and the two padded ones it does not,
each with the annotation ProvSQL computes – equal as Boolean functions of
the six tokens over all 64 valuations. The `LIMIT` gate is vacuous on the
three matches and on the Accounting and Bakery padded rows, and cuts the
Catering row exactly in the worlds where three rows sort ahead of it. -/
theorem q2_ann : ∀ v : X → Bool,
    (q2.evaluateAnnotated db).map (fun p => ((p.1 0, p.1 2), p.2 v))
      = ((([((val 2, val 201), v dB && v tb1),
            ((val 1, val 101), v dA && v ta1),
            ((val 1, val 102), v dA && v ta2),
            ((val 1, nil), v dA && !(v ta1) && !(v ta2)),
            ((val 2, nil), v dB && !(v tb1)),
            ((val 3, nil), v dC && !(v dA && v ta1 && v ta2 && v dB))]
          : List ((V × V) × Bool))) : Multiset _) := by
  decide

/-! ### The two window columns, world by world

`rank() OVER (PARTITION BY d.dept ORDER BY e.salary DESC)` and
`avg(e.salary) OVER (PARTITION BY d.dept)`. They are **two separate
queries** here: a window takes an all-regular input, so a second window
column cannot be added to a relation that already has one, and the two
cannot be put side by side in this syntax. Each is read in a world by
evaluating it plainly on that world's instance
(`AnnotatedDatabase.randomWorld`), which is SQL on that sub-instance. -/

/-- SQL's `avg`: the mean of the non-null values, null over none. -/
abbrev avgAgg : SeqAggFunc V :=
  SeqAggFunc.sqlOf (fun l =>
    WithNull.val (((l.map (fun x => (x : Option ℕ).getD 0)).sum) / l.length))

/-- `rank() OVER (PARTITION BY d.dept ORDER BY e.salary DESC)`, as the
count of the rows ahead; the rank is one more. -/
abbrev rankWin : AggQueryIn V 0 6 (Fin.snoc (ColKind.allReg 5) ColKind.agg) :=
  AggQueryIn.Win ![0] ![4] ![OrderCol.DESC]
    (ValueFrame.rangeBefore ![OrderCol.DESC]) (TermIn.const 1) cnt q1
    (winReadsReg_allReg _ _ _)

/-- `avg(e.salary) OVER (PARTITION BY d.dept)`. -/
abbrev avgWin : AggQueryIn V 0 6 (Fin.snoc (ColKind.allReg 5) ColKind.agg) :=
  AggQueryIn.Win ![0] (fun k : Fin 0 => k.elim0) OrderSpec.unordered
    ValueFrame.whole (TermIn.index 4) avgAgg q1 (winReadsReg_allReg _ _ _)

/-- Every token true. -/
abbrev vAll : X → Bool := fun _ => true

/-- `a1` absent. -/
abbrev vNoA1 : X → Bool := fun i => i ≠ ta1

/-- `b1` absent. -/
abbrev vNoB1 : X → Bool := fun i => i ≠ tb1

open WithNull in
/-- **All six tokens true**: the three employees with SQL's rank and
average, and Catering's padded row – which the `LIMIT` cuts, as `q2_ann`
shows, and whose average is null. -/
theorem world_all :
    ((rankWin.evaluatePlain (AnnotatedDatabase.randomWorld vAll db)).map
        (fun u => (u 2, 1 + u 5)),
      (avgWin.evaluatePlain (AnnotatedDatabase.randomWorld vAll db)).map (fun u => (u 2, u 5)))
      = (((([(val 201, val 1), (val 101, val 1), (val 102, val 2),
              (nil, val 1)]
            : List (V × V))) : Multiset _),
         ((([(val 201, val 120), (val 101, val 95), (val 102, val 95),
              (nil, nil)]
            : List (V × V))) : Multiset _)) := by
  decide

open WithNull in
/-- **`a1` absent**: Accounting is down to `a2`, whose average is its own
salary, and Catering's padded row appears. -/
theorem world_noA1 :
    ((rankWin.evaluatePlain (AnnotatedDatabase.randomWorld vNoA1 db)).map
        (fun u => (u 2, 1 + u 5)),
      (avgWin.evaluatePlain (AnnotatedDatabase.randomWorld vNoA1 db)).map
        (fun u => (u 2, u 5)))
      = (((([(val 201, val 1), (val 102, val 1), (nil, val 1)]
            : List (V × V))) : Multiset _),
         ((([(val 201, val 120), (val 102, val 90), (nil, nil)]
            : List (V × V))) : Multiset _)) := by
  decide

open WithNull in
/-- **`b1` absent**: Bakery's padded row appears, and its average is null
– the partition holds one row and that row's salary is null. ProvSQL
prints `NaN` there, which it takes for a display artefact; the semantics
says null. Catering's padded row is present too and the `LIMIT` cuts it,
as `q2_ann` shows. -/
theorem world_noB1 :
    ((rankWin.evaluatePlain (AnnotatedDatabase.randomWorld vNoB1 db)).map
        (fun u => (u 2, 1 + u 5)),
      (avgWin.evaluatePlain (AnnotatedDatabase.randomWorld vNoB1 db)).map
        (fun u => (u 2, u 5)))
      = (((([(val 101, val 1), (val 102, val 2), (nil, val 1), (nil, val 1)]
            : List (V × V))) : Multiset _),
         ((([(val 101, val 95), (val 102, val 95), (nil, nil), (nil, nil)]
            : List (V × V))) : Multiset _)) := by
  decide

end ProvsqlExample
