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
# Conformance with PostgreSQL at `F4`: aggregation
-/

@[expose] public section

namespace Conformance

open WithNull

set_option maxRecDepth 100000 in
/-- Grouping puts the null key in a group of its own; `count(*)` counts rows,
`count(sal)` the non-null salaries, and `sum`, `min` and `max` are null over
a group with no non-null salary.
```sql
SELECT dept, count(*), count(sal), sum(sal), min(sal), max(sal) FROM emp GROUP BY dept;
```
-/
theorem group_aggs_ok : ∀ i,
    run i (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1]
        ![TermIn.const (val 1), TermIn.index 2, TermIn.index 2, TermIn.index 2, TermIn.index 2]
        ![cnt, cntCol, sumAgg, minAgg, maxAgg] Emp)
      = rel (group_aggs i) := by decide

set_option maxRecDepth 100000 in
/-- An aggregation with no grouping has its row over no input: a count of `0`
and a null sum.
```sql
SELECT count(*), sum(sal) FROM emp WHERE id > 1000;
```
-/
theorem scalar_agg_empty_ok : ∀ i,
    run i (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false)
        ![TermIn.const (val 1), TermIn.index 2] ![cnt, sumAgg]
        (AggQueryIn.Sel (GenPredIn.cmp CompOp.gt (col 0) (lit 1000)) Emp))
      = rel (scalar_agg_empty i) := by decide

end Conformance
