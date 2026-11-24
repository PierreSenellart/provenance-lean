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
# Conformance with PostgreSQL at `F5`: selection on aggregate values
-/

@[expose] public section

namespace Conformance

open WithNull

set_option maxRecDepth 100000 in
/-- `HAVING` on a count keeps the groups, the null one included, with at least two rows.
```sql
SELECT dept FROM emp GROUP BY dept HAVING count(*) >= 2;
```
-/
theorem having_count_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.aggCmp 1 rfl CompOp.ge (lit 2)) (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)))
      = rel (having_count i) := by
  decide

set_option maxRecDepth 100000 in
/-- `HAVING` on a sum: a null sum compares as unknown and its group is dropped.
```sql
SELECT dept FROM emp GROUP BY dept HAVING sum(sal) > 100;
```
-/
theorem having_sum_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.aggCmp 1 rfl CompOp.gt (lit 100)) (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.index 2] ![sumAgg] Emp)))
      = rel (having_sum i) := by
  decide

set_option maxRecDepth 100000 in
/-- A `WHERE` on the aggregate column of a subquery is the same selection.
```sql
SELECT dept, c FROM (SELECT dept, count(*) AS c FROM emp GROUP BY dept) g WHERE c = 2;
```
-/
theorem where_on_agg_ok : ∀ i,
    run i (AggQueryIn.Sel (GenPredIn.aggCmp 1 rfl CompOp.eq (lit 2)) (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp))
      = rel (where_on_agg i) := by
  decide

set_option maxRecDepth 100000 in
/-- A conjunction of two conditions on two aggregates of one group.
```sql
SELECT dept FROM emp GROUP BY dept HAVING count(*) >= 2 AND sum(sal) > 100;
```
-/
theorem having_and_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.and (GenPredIn.aggCmp 1 rfl CompOp.ge (lit 2))
            (GenPredIn.aggCmp 2 rfl CompOp.gt (lit 100)))
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1]
          ![TermIn.const (val 1), TermIn.index 2] ![cnt, sumAgg] Emp)))
      = rel (having_and i) := by
  decide

set_option maxRecDepth 100000 in
/-- A disjunction of two such conditions: true when one is, the other being unknown on a null sum.
```sql
SELECT dept FROM emp GROUP BY dept HAVING count(*) >= 3 OR sum(sal) < 60;
```
-/
theorem having_or_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.or (GenPredIn.aggCmp 1 rfl CompOp.ge (lit 3))
            (GenPredIn.aggCmp 2 rfl CompOp.lt (lit 60)))
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1]
          ![TermIn.const (val 1), TermIn.index 2] ![cnt, sumAgg] Emp)))
      = rel (having_or i) := by
  decide

set_option maxRecDepth 100000 in
/-- `BETWEEN` on a count, as one range atom.
```sql
SELECT dept FROM emp GROUP BY dept HAVING count(*) BETWEEN 2 AND 3;
```
-/
theorem having_range_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.aggRange 1 rfl CompOp.ge (lit 2) CompOp.le (lit 3))
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)))
      = rel (having_range i) := by
  decide

set_option maxRecDepth 100000 in
/-- The negation of a condition on a count.
```sql
SELECT dept FROM emp GROUP BY dept HAVING NOT (count(*) = 1);
```
-/
theorem having_not_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.not (GenPredIn.aggCmp 1 rfl CompOp.eq (lit 1)))
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)))
      = rel (having_not i) := by
  decide

set_option maxRecDepth 100000 in
/-- `HAVING` on a maximum.
```sql
SELECT dept FROM emp GROUP BY dept HAVING max(sal) >= 100;
```
-/
theorem having_max_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.aggCmp 1 rfl CompOp.ge (lit 100))
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.index 2] ![maxAgg] Emp)))
      = rel (having_max i) := by
  decide

set_option maxRecDepth 100000 in
/-- `HAVING` on a minimum.
```sql
SELECT dept FROM emp GROUP BY dept HAVING min(sal) < 60;
```
-/
theorem having_min_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl)]
        (AggQueryIn.Sel (GenPredIn.aggCmp 1 rfl CompOp.lt (lit 60))
          (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.index 2] ![minAgg] Emp)))
      = rel (having_min i) := by
  decide

end Conformance
