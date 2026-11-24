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

set_option maxRecDepth 100000 in
/-- An expression over an aggregate value.
```sql
SELECT dept, count(*) + 1 FROM emp GROUP BY dept;
```
-/
theorem agg_expr_unary_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl),
          ProjColIn.aggTerm 1 rfl (fun v => v + val 1)]
        (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp))
      = rel (agg_expr_unary i) := by
  decide

set_option maxRecDepth 100000 in
/-- `>= ALL` is the antijoin on the null-aware negation: true over an empty subquery, never true once the subquery holds a null.
```sql
SELECT x FROM t WHERE x >= ALL (SELECT x FROM s);
```
-/
theorem all_sub_ok : ∀ i,
    run i (AggQueryIn.antijoin cnt 0
        (GenPredIn.or (GenPredIn.cmp CompOp.lt (TermGIn.outer 0) (TermGIn.index 0 rfl))
          (GenPredIn.or (isNull (TermGIn.index 0 rfl)) (isNull (TermGIn.outer 0))))
        T (AggQueryIn.Rel 1 "s"))
      = rel (all_sub i) := by
  decide

set_option maxRecDepth 100000 in
/-- An `EXISTS` under a disjunction is an atom on the count of matches, combined with the other condition.
```sql
SELECT d, name FROM dept WHERE name = 30 OR EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d);
```
-/
theorem or_exists_ok : ∀ i,
    run i (AggQueryIn.Proj (AggQueryIn.dropCount 2)
        (AggQueryIn.Sel
          (GenPredIn.or (GenPredIn.cmp CompOp.eq (TermGIn.index 1 rfl) (lit 30))
            (GenPredIn.aggCmp (AggQueryIn.countCol 2) (AggQueryIn.countKinds_countCol 2)
              CompOp.ne (lit 0)))
          (AggQueryIn.matchCount cnt 0 sameDept Dept (AggQueryIn.Rel 3 "emp"))))
      = rel (or_exists i) := by
  decide

set_option maxRecDepth 100000 in
/-- A scalar subquery with no aggregate: the one value where there is one row, the null where there is none.
```sql
SELECT d, name, (SELECT id FROM emp WHERE emp.id = dept.d + 100) FROM dept;
```
-/
theorem scalar_subquery_value_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl), ProjColIn.term (TermGIn.index 1 rfl),
          ProjColIn.token 3 rfl]
        (AggQueryIn.Sel (GenPredIn.aggCmp 2 rfl CompOp.le (lit 1))
          (AggQueryIn.Apply Dept
            (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => true)
              ![TermIn.const (val 1), TermIn.index 0] ![cnt, SeqAggFunc.sqlPickFirst]
              (AggQueryIn.Sel (GenPredIn.cmp CompOp.eq (TermGIn.index 0 rfl)
                  (TermGIn.add (TermGIn.outer 0) (lit 100)))
                (AggQueryIn.Rel 3 "emp"))))))
      = rel (scalar_subquery_value i) := by
  decide

/-- The kinds of a grouping-set row with two key columns and a count. -/
abbrev gs3 : Fin 3 → ColKind := ![ColKind.reg, ColKind.reg, ColKind.agg]

/-- The same with one key column. -/
abbrev gs2 : Fin 2 → ColKind := ![ColKind.reg, ColKind.agg]

set_option maxRecDepth 100000 in
/-- Grouping sets are the union of the aggregations on each set, each padded with nulls on the columns it does not group on.
```sql
SELECT dept, sal, count(*) FROM emp GROUP BY GROUPING SETS ((dept), (sal));
```
-/
theorem grouping_sets_ok : ∀ i,
    run i (AggQueryIn.Sum
        ((AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl), ProjColIn.term (TermGIn.const nil), ProjColIn.token 1 rfl]
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)).castKind (κ' := gs3) (funext fun j => by revert j; decide))
        ((AggQueryIn.Proj ![ProjColIn.term (TermGIn.const nil), ProjColIn.term (TermGIn.index 0 rfl), ProjColIn.token 1 rfl]
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![2] ![TermIn.const (val 1)] ![cnt] Emp)).castKind (κ' := gs3) (funext fun j => by revert j; decide)))
      = rel (grouping_sets i) := by
  intro i
  simp only [run, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- The empty grouping set is the grand total, which has its row over no input: it is the aggregation with no grouping.
```sql
SELECT dept, count(*) FROM emp GROUP BY GROUPING SETS ((dept), ());
```
-/
theorem grouping_sets_total_ok : ∀ i,
    run i (AggQueryIn.Sum
        ((AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl), ProjColIn.token 1 rfl]
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)).castKind (κ' := gs2) (funext fun j => by revert j; decide))
        ((AggQueryIn.Proj ![ProjColIn.term (TermGIn.const nil), ProjColIn.token 0 rfl]
          (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ![TermIn.const (val 1)] ![cnt] Emp)).castKind (κ' := gs2) (funext fun j => by revert j; decide)))
      = rel (grouping_sets_total i) := by
  intro i
  simp only [run, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- The grouping set `()` alone, through the derived operator: the grand total has its row over an empty table.
```sql
SELECT count(*), sum(sal) FROM emp GROUP BY GROUPING SETS (());
```
-/
theorem grand_total_set_ok : ∀ i,
    run i (AggQueryIn.gammaSet (fun k : Fin 0 => k.elim0)
        ![TermIn.const (val 1), TermIn.index 2] ![cnt, sumAgg] ∅ Emp)
      = rel (grand_total_set i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_gammaSet_empty (lab := 0) (rd := fun _ => false) (fun k : Fin 0 => k.elim0)
    ![TermIn.const (val 1), TermIn.index 2] ![cnt, sumAgg] Emp (db i) (γ := fun _ => 0)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

end Conformance
