/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Conformance.Expected
public import Provenance.Derived
public import Provenance.FragQuery
import all Provenance.Query

/-!
# Conformance of the plain semantics with PostgreSQL: shared notation

The conformance modules take the SQL queries of `conformance/queries.sql`
one by one, write each in the algebra, and state that the plain evaluator
returns on every instance of `Provenance.Conformance.Expected` exactly the
multiset PostgreSQL returned. There is one module per level of the chain of
fragments, a query sitting at the level of the construct it probes. The SQL
text of a query is in the docstring of its term or of its theorem, and
`scripts/conformance.py --check` checks that it is the text that was run.

This module holds what they share: the base relations, the terms and
predicates used over and over, and SQL's aggregates on the naturals with a
null.
-/

@[expose] public section

namespace Conformance

open WithNull

/-- A list of tuples read as a multiset. -/
abbrev rel {n : ℕ} (l : List (Tuple V n)) : Multiset (Tuple V n) := l

/-- What the plain evaluator returns for a query on an instance. -/
noncomputable abbrev run (i : Inst) {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery V n κ) :
    Multiset (Tuple V n) :=
  q.evaluatePlain (db i)

/-- A regular column of an all-regular relation. -/
abbrev col {c n : ℕ} (k : Fin n) : TermGIn V c (ColKind.allReg n) := TermGIn.index k rfl

/-- A constant. -/
abbrev lit {c n : ℕ} {κ : Fin n → ColKind} (v : ℕ) : TermGIn V c κ := TermGIn.const (val v)

/-- `t IS NULL`. -/
abbrev isNull {c n : ℕ} {κ : Fin n → ColKind} (t : TermGIn V c κ) : GenPredIn V c κ :=
  GenPredIn.cmp CompOp.syneq t (TermGIn.const nil)

abbrev T : AggQuery V 1 (ColKind.allReg 1) := AggQueryIn.Rel 1 "t"
abbrev S : AggQuery V 1 (ColKind.allReg 1) := AggQueryIn.Rel 1 "s"
abbrev U : AggQuery V 1 (ColKind.allReg 1) := AggQueryIn.Rel 1 "u"
abbrev Dept : AggQuery V 2 (ColKind.allReg 2) := AggQueryIn.Rel 2 "dept"
abbrev Emp : AggQuery V 3 (ColKind.allReg 3) := AggQueryIn.Rel 3 "emp"

/-- `count(*)`. -/
abbrev cnt : SeqAggFunc V := fun l => val l.length

/-- The natural a value holds, `0` for a null. -/
abbrev natOf (x : V) : ℕ := (x : Option ℕ).getD 0

/-- `count(x)`: the nulls do not count. -/
abbrev cntCol : SeqAggFunc V := SeqAggFunc.counting cnt

/-- `sum(x)`. -/
abbrev sumAgg : SeqAggFunc V := SeqAggFunc.sqlOf (fun l => val (l.map natOf).sum)

/-- `min(x)`. -/
abbrev minAgg : SeqAggFunc V := SeqAggFunc.sqlOf (fun l => val ((l.map natOf).min?.getD 0))

/-- `max(x)`. -/
abbrev maxAgg : SeqAggFunc V := SeqAggFunc.sqlOf (fun l => val ((l.map natOf).max?.getD 0))

/-- The correlation `emp.dept = dept.d`. -/
abbrev sameDept : GenPredIn V 2 (ColKind.allReg 3) :=
  GenPredIn.cmp CompOp.eq (TermGIn.index 1 rfl) (TermGIn.outer 0)

/-- `choose`: the first value of the sequence, a null read as a value, and
null over no row. It is what `lag`, `lead` and `first_value` read a frame
through. The library's `SeqAggFunc.pickFirst` gives the zero of the value
type over no row, which here is `0` and not the null. -/
abbrev chooseAgg : SeqAggFunc V := fun l => l.headD nil

/-! ### The same in the fragment syntax of the first levels -/

abbrev fT : FragQuery V 1 := .Rel 1 "t"
abbrev fS : FragQuery V 1 := .Rel 1 "s"
abbrev fU : FragQuery V 1 := .Rel 1 "u"
abbrev fDept : FragQuery V 2 := .Rel 2 "dept"

/-- `count(x)` counts matches: it is never null, and zero exactly over
nothing but nulls. -/
theorem cntCol_counts : SeqAggFunc.Counts cntCol :=
  SeqAggFunc.counts_counting (fun _ => rfl) (fun L => by
    cases L with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons a l =>
      constructor
      · intro h
        exact absurd (Option.some.inj h) (Nat.succ_ne_zero _)
      · intro h
        cases h)

/-- The unit a rank counts from. -/
instance : One V := ⟨val 1⟩

end Conformance
