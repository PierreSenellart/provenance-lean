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

end Conformance
