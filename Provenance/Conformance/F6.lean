/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Conformance.Basic
import all Provenance.Database
import all Provenance.AggQuery
import all Provenance.Derived

/-!
# Conformance with PostgreSQL at `F6`: outer joins and the null-aware negation
-/

@[expose] public section

namespace Conformance

open WithNull

set_option maxRecDepth 100000 in
/-- A left outer join pads the department whose key is null, which matches
nothing, and no department that has a match.
```sql
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d LEFT JOIN emp e ON e.dept = d.d;
```
-/
theorem left_join_null_keys_ok : ∀ i,
    run i (AggQueryIn.leftOuter
        (GenPredIn.cmp CompOp.eq (TermGIn.index 3 rfl) (TermGIn.index 0 rfl)) Dept Emp)
      = rel (left_join_null_keys i) := by
  intro i
  simp only [run]
  rw [AggQueryIn.evaluatePlain_leftOuter]
  simp only [AggQueryIn.matchedLeft, AggQueryIn.innerJoin, AggQueryIn.evaluatePlain,
    AggQueryIn.evaluatePlain_castKind]
  revert i
  decide

/-- The null-aware condition of `d NOT IN (SELECT dept …)`: a row of the
subquery matches when the comparison is true or unknown. -/
abbrev notInDept : GenPredIn V 2 (ColKind.allReg 3) :=
  GenPredIn.or (GenPredIn.cmp CompOp.eq (TermGIn.index 1 rfl) (TermGIn.outer 0))
    (GenPredIn.or (isNull (TermGIn.index 1 rfl)) (isNull (TermGIn.outer 0)))

set_option maxRecDepth 100000 in
/-- `NOT IN` over a subquery that holds a null returns nothing.
```sql
SELECT d, name FROM dept WHERE d NOT IN (SELECT dept FROM emp);
```
-/
theorem not_in_null_ok : ∀ i,
    run i (AggQueryIn.antijoin cnt 0 notInDept Dept (AggQueryIn.Rel 3 "emp")) = rel (not_in_null i) := by decide

set_option maxRecDepth 100000 in
/-- Over a subquery with no null it keeps the department that is not there,
and not the one whose own key is null.
```sql
SELECT d, name FROM dept WHERE d NOT IN (SELECT dept FROM emp WHERE id < 103);
```
-/
theorem not_in_no_null_ok : ∀ i,
    run i (AggQueryIn.antijoin cnt 0 notInDept Dept
        (AggQueryIn.Sel (GenPredIn.cmp CompOp.lt (col 0) (lit 103)) (AggQueryIn.Rel 3 "emp")))
      = rel (not_in_no_null i) := by decide

/-- `e.dept = d.d` over the five columns of the join. -/
abbrev onDept : GenPred V (ColKind.allReg (2 + 3)) :=
  GenPredIn.cmp CompOp.eq (TermGIn.index 3 rfl) (TermGIn.index 0 rfl)

set_option maxRecDepth 100000 in
/-- A right outer join pads the employee with no department.
```sql
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d RIGHT JOIN emp e ON e.dept = d.d;
```
-/
theorem right_join_null_keys_ok : ∀ i,
    run i (AggQueryIn.rightOuter onDept Dept Emp) = rel (right_join_null_keys i) := by
  intro i
  simp only [run]
  rw [AggQueryIn.evaluatePlain_rightOuter]
  simp only [AggQueryIn.matchedRight, AggQueryIn.innerJoin, AggQueryIn.evaluatePlain,
    AggQueryIn.evaluatePlain_castKind]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- A full outer join pads on both sides.
```sql
SELECT d.d, d.name, e.id, e.dept, e.sal FROM dept d FULL JOIN emp e ON e.dept = d.d;
```
-/
theorem full_join_null_keys_ok : ∀ i,
    run i (AggQueryIn.fullOuter onDept Dept Emp) = rel (full_join_null_keys i) := by
  intro i
  simp only [run]
  rw [AggQueryIn.evaluatePlain_fullOuter, AggQueryIn.evaluatePlain_leftOuter]
  simp only [AggQueryIn.matchedLeft, AggQueryIn.matchedRight, AggQueryIn.innerJoin,
    AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- A correlated scalar subquery with an aggregate has its row for every outer row: null over no match.
```sql
SELECT d, name, (SELECT max(sal) FROM emp WHERE emp.dept = dept.d) FROM dept;
```
-/
theorem scalar_subquery_max_ok : ∀ i,
    run i (AggQueryIn.Apply Dept
        (AggQueryIn.GammaScalar (lab := 0)
          (rd := (AggQueryIn.Sel sameDept (AggQueryIn.Rel 3 "emp")).readsOuter)
          ![TermIn.index 2] ![maxAgg] (AggQueryIn.Sel sameDept (AggQueryIn.Rel 3 "emp"))))
      = rel (scalar_subquery_max i) := by
  decide

set_option maxRecDepth 100000 in
/-- The same with a count, which is `0` over no match.
```sql
SELECT d, name, (SELECT count(*) FROM emp WHERE emp.dept = dept.d) FROM dept;
```
-/
theorem scalar_subquery_count_ok : ∀ i,
    run i (AggQueryIn.Apply Dept
        (AggQueryIn.GammaScalar (lab := 0)
          (rd := (AggQueryIn.Sel sameDept (AggQueryIn.Rel 3 "emp")).readsOuter)
          ![TermIn.const (val 1)] ![cnt] (AggQueryIn.Sel sameDept (AggQueryIn.Rel 3 "emp"))))
      = rel (scalar_subquery_count i) := by
  decide

end Conformance
