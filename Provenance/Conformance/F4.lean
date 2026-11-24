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

set_option maxRecDepth 100000 in
/-- A `FILTER` clause cuts what the aggregate reads and not the groups: a group with no row passing it still has its row, with a count of `0`.
```sql
SELECT dept, count(*) FILTER (WHERE sal >= 90) FROM emp GROUP BY dept;
```
-/
theorem agg_filter_ok : ∀ i,
    run i (AggQueryIn.gammaWhere ![1] (Selection.BT (#2 >= TermIn.const (val 90))) (TermIn.const (val 1)) cnt Emp)
      = rel (agg_filter i) := by
  decide

set_option maxRecDepth 100000 in
/-- `count(DISTINCT sal)` counts the distinct non-null salaries of a group.
```sql
SELECT dept, count(DISTINCT sal) FROM emp GROUP BY dept;
```
-/
theorem agg_distinct_ok : ∀ i,
    run i (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.index 2] ![cntCol.distinct] Emp)
      = rel (agg_distinct i) := by
  decide

set_option maxRecDepth 100000 in
/-- `sum(DISTINCT sal)` over the whole table, null over no non-null salary.
```sql
SELECT sum(DISTINCT sal) FROM emp;
```
-/
theorem scalar_agg_distinct_ok : ∀ i,
    run i (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ![TermIn.index 2] ![sumAgg.distinct] Emp)
      = rel (scalar_agg_distinct i) := by
  decide

set_option maxRecDepth 100000 in
/-- Grouping on two columns, nulls in either.
```sql
SELECT dept, sal, count(*) FROM emp GROUP BY dept, sal;
```
-/
theorem group_two_keys_ok : ∀ i,
    run i (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1, 2] ![TermIn.const (val 1)] ![cnt] Emp)
      = rel (group_two_keys i) := by
  decide

set_option maxRecDepth 100000 in
/-- `min`, `max` and `count(sal)` over the whole table: null, null and `0` over no non-null salary.
```sql
SELECT min(sal), max(sal), count(sal) FROM emp;
```
-/
theorem scalar_min_max_ok : ∀ i,
    run i (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false)
        ![TermIn.index 2, TermIn.index 2, TermIn.index 2] ![minAgg, maxAgg, cntCol] Emp)
      = rel (scalar_min_max i) := by
  decide

set_option maxRecDepth 100000 in
/-- An aggregate over a term: the term is null on a null, and the sum skips it.
```sql
SELECT dept, sum(sal + 1) FROM emp GROUP BY dept;
```
-/
theorem group_sum_expr_ok : ∀ i,
    run i (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1]
        ![TermIn.add (TermIn.index 2) (TermIn.const (val 1))] ![sumAgg] Emp)
      = rel (group_sum_expr i) := by
  decide

set_option maxRecDepth 100000 in
/-- An order-dependent aggregate under its own `ORDER BY`: the first salary of each group in the order of `id`, a null read as a value.
```sql
SELECT dept, (array_agg(sal ORDER BY id))[1] FROM emp GROUP BY dept;
```
-/
theorem group_pickfirst_ordered_ok : ∀ i,
    run i (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.index 2]
        ![SeqAggFunc.sqlPickFirst] Emp (fun _ => none) (GroupOrder.byCols ![0] ![OrderCol.ASC]))
      = rel (group_pickfirst_ordered i) := by
  decide

set_option maxRecDepth 100000 in
/-- The same in descending order.
```sql
SELECT dept, (array_agg(sal ORDER BY id DESC))[1] FROM emp GROUP BY dept;
```
-/
theorem group_pickfirst_desc_ok : ∀ i,
    run i (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.index 2]
        ![SeqAggFunc.sqlPickFirst] Emp (fun _ => none) (GroupOrder.byCols ![0] ![OrderCol.DESC]))
      = rel (group_pickfirst_desc i) := by
  decide

end Conformance
