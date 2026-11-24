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
# Conformance with PostgreSQL at `F7`: windows, ranks and truncation
-/

@[expose] public section

namespace Conformance

open WithNull

set_option maxRecDepth 100000 in
/-- `rank()` gives tied rows the same rank and skips after them; in a
descending order the nulls come first.
```sql
SELECT id, dept, sal, rank() OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
```
-/
theorem rank_ties_nulls_ok : ∀ i,
    run i (AggQueryIn.rank cnt ![1] ![2] ![OrderCol.DESC] Emp (winReadsReg_allReg _ _ _))
      = rel (rank_ties_nulls i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_rank cnt ![1] ![2] ![OrderCol.DESC] Emp
    (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `dense_rank()` does not skip after tied rows.
```sql
SELECT id, dept, sal, dense_rank() OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
```
-/
theorem dense_rank_ties_nulls_ok : ∀ i,
    run i (AggQueryIn.denseRank cnt ![1] ![2] ![OrderCol.DESC] Emp (winReadsReg_allReg _ _ _))
      = rel (dense_rank_ties_nulls i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_denseRank cnt ![1] ![2] ![OrderCol.DESC] Emp
    (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- An aggregate over the whole partition: the sum skips the nulls, and is
null over a partition with none.
```sql
SELECT id, dept, sal, sum(sal) OVER (PARTITION BY dept) FROM emp;
```
-/
theorem win_sum_partition_ok : ∀ i,
    run i (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) ![1]
        (fun k : Fin 0 => k.elim0) OrderSpec.unordered ValueFrame.whole (TermIn.index 2)
        sumAgg Emp (winReadsReg_allReg _ _ _))
      = rel (win_sum_partition i) := by decide

set_option maxRecDepth 100000 in
/-- With an `ORDER BY` and no frame clause, the frame is the rows up to the
current row's peers: tied rows share the running count.
```sql
SELECT id, dept, sal, count(*) OVER (PARTITION BY dept ORDER BY sal DESC) FROM emp;
```
-/
theorem win_running_count_ok : ∀ i,
    run i (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) ![1] ![2]
        ![OrderCol.DESC] (ValueFrame.rangeUpTo ![OrderCol.DESC]) (TermIn.const (val 1))
        cnt Emp (winReadsReg_allReg _ _ _))
      = rel (win_running_count i) := by decide

set_option maxRecDepth 100000 in
/-- `ORDER BY id LIMIT 2`, the order being a key: the rows of rank at most 2.
```sql
SELECT id, dept, sal FROM emp ORDER BY id LIMIT 2;
```
-/
theorem limit_key_ok : ∀ i,
    run i (AggQueryIn.truncate cnt (fun k : Fin 0 => k.elim0) ![0] ![OrderCol.ASC]
        (val 0) (val 2) Emp (winReadsReg_allReg _ _ _))
      = rel (limit_key i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_truncate cnt (fun k : Fin 0 => k.elim0) ![0]
    ![OrderCol.ASC] (val 0) (val 2) Emp (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `FETCH FIRST 1 ROWS WITH TIES` keeps every row of rank 1.
```sql
SELECT id, dept, sal FROM emp ORDER BY sal DESC NULLS LAST FETCH FIRST 1 ROWS WITH TIES;
```
-/
theorem fetch_with_ties_ok : ∀ i,
    run i (AggQueryIn.truncate cnt (fun k : Fin 0 => k.elim0) ![2]
        ![{ desc := true, nullsFirst := false }] (val 0) (val 1) Emp
        (winReadsReg_allReg _ _ _))
      = rel (fetch_with_ties i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_truncate cnt (fun k : Fin 0 => k.elim0) ![2]
    ![{ desc := true, nullsFirst := false }] (val 0) (val 1) Emp (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `lag` over an order that is a key: the value on the previous row, null on the first.
```sql
SELECT id, dept, sal, lag(sal) OVER (ORDER BY id) FROM emp;
```
-/
theorem lag_key_ok : ∀ i,
    run i (AggQueryIn.lag (fun k : Fin 0 => k.elim0) ![0] ![OrderCol.ASC] (TermIn.index 2) Emp)
      = rel (lag_key i) := by
  decide

set_option maxRecDepth 100000 in
/-- `lead`: the value on the next row, null on the last.
```sql
SELECT id, dept, sal, lead(sal) OVER (ORDER BY id) FROM emp;
```
-/
theorem lead_key_ok : ∀ i,
    run i (AggQueryIn.lead (fun k : Fin 0 => k.elim0) ![0] ![OrderCol.ASC] (TermIn.index 2) Emp)
      = rel (lead_key i) := by
  decide

set_option maxRecDepth 100000 in
/-- `first_value` reads a null as a value.
```sql
SELECT id, dept, sal, first_value(sal) OVER (PARTITION BY dept ORDER BY id) FROM emp;
```
-/
theorem first_value_part_ok : ∀ i,
    run i (AggQueryIn.firstValue (hsql := sql_frame%) ![1] ![0] ![OrderCol.ASC]
        (ValueFrame.rangeUpTo ![OrderCol.ASC]) (TermIn.index 2) Emp)
      = rel (first_value_part i) := by
  decide

set_option maxRecDepth 100000 in
/-- `row_number()` over an order that is a key is the rank.
```sql
SELECT id, dept, sal, row_number() OVER (PARTITION BY dept ORDER BY id) FROM emp;
```
-/
theorem row_number_key_ok : ∀ i,
    run i (AggQueryIn.rank cnt ![1] ![0] ![OrderCol.ASC] Emp (winReadsReg_allReg _ _ _))
      = rel (row_number_key i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_rank cnt ![1] ![0] ![OrderCol.ASC] Emp
    (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `LIMIT 2 OFFSET 1` over a key: the rows of rank 2 and 3.
```sql
SELECT id, dept, sal FROM emp ORDER BY id LIMIT 2 OFFSET 1;
```
-/
theorem limit_offset_ok : ∀ i,
    run i (AggQueryIn.truncate cnt (fun k : Fin 0 => k.elim0) ![0] ![OrderCol.ASC]
        (val 1) (val 3) Emp (winReadsReg_allReg _ _ _))
      = rel (limit_offset i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_truncate cnt (fun k : Fin 0 => k.elim0) ![0]
    ![OrderCol.ASC] (val 1) (val 3) Emp (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `DISTINCT ON (dept) … ORDER BY dept, id`: the first row of each department, the null one included.
```sql
SELECT DISTINCT ON (dept) id, dept, sal FROM emp ORDER BY dept, id;
```
-/
theorem distinct_on_ok : ∀ i,
    run i (AggQueryIn.distinctOn cnt ![1] ![0] ![OrderCol.ASC] Emp (winReadsReg_allReg _ _ _))
      = rel (distinct_on i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_truncate cnt ![1] ![0]
    ![OrderCol.ASC] (0 : V) (1 : V) Emp (winReadsReg_allReg _ _ _) (db i)
  simp only [run, AggQueryIn.distinctOn]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `lag` within a partition: null on the first row of each, a null salary read as a value.
```sql
SELECT id, dept, sal, lag(sal) OVER (PARTITION BY dept ORDER BY id) FROM emp;
```
-/
theorem lag_part_ok : ∀ i,
    run i (AggQueryIn.lag ![1] ![0] ![OrderCol.ASC] (TermIn.index 2) Emp)
      = rel (lag_part i) := by
  decide

set_option maxRecDepth 100000 in
/-- `last_value` over the whole partition, in the order of the clause.
```sql
SELECT id, dept, sal, last_value(sal) OVER (PARTITION BY dept ORDER BY id RANGE BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING) FROM emp;
```
-/
theorem last_value_part_ok : ∀ i,
    run i (AggQueryIn.lastValue (hsql := sql_frame%) ![1] ![0] ![OrderCol.ASC]
        ValueFrame.whole (TermIn.index 2) Emp)
      = rel (last_value_part i) := by
  decide

set_option maxRecDepth 100000 in
/-- `lag(sal, 2)` over a key: null on the first two rows.
```sql
SELECT id, dept, sal, lag(sal, 2) OVER (ORDER BY id) FROM emp;
```
-/
theorem lag_two_ok : ∀ i,
    run i (AggQueryIn.lagAt (fun k : Fin 0 => k.elim0) ![0] ![OrderCol.ASC] 1 (TermIn.index 2) Emp)
      = rel (lag_two i) := by
  decide

set_option maxRecDepth 100000 in
/-- `rank()` in ascending order, where the nulls come last.
```sql
SELECT id, dept, sal, rank() OVER (ORDER BY sal) FROM emp;
```
-/
theorem rank_asc_nulls_ok : ∀ i,
    run i (AggQueryIn.rank cnt (fun k : Fin 0 => k.elim0) ![2] ![OrderCol.ASC] Emp (winReadsReg_allReg _ _ _))
      = rel (rank_asc_nulls i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_rank cnt (fun k : Fin 0 => k.elim0) ![2] ![OrderCol.ASC] Emp
    (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- A running sum within a partition, over an order that is a key.
```sql
SELECT id, dept, sal, sum(sal) OVER (PARTITION BY dept ORDER BY id) FROM emp;
```
-/
theorem win_running_sum_ok : ∀ i,
    run i (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) ![1] ![0]
        ![OrderCol.ASC] (ValueFrame.rangeUpTo ![OrderCol.ASC]) (TermIn.index 2)
        sumAgg Emp (winReadsReg_allReg _ _ _))
      = rel (win_running_sum i) := by
  decide

set_option maxRecDepth 100000 in
/-- `OVER ()`: one partition, the whole table.
```sql
SELECT id, dept, sal, count(*) OVER () FROM emp;
```
-/
theorem win_count_all_ok : ∀ i,
    run i (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) (fun k : Fin 0 => k.elim0)
        (fun k : Fin 0 => k.elim0) OrderSpec.unordered ValueFrame.whole (TermIn.const (val 1))
        cnt Emp (winReadsReg_allReg _ _ _))
      = rel (win_count_all i) := by
  decide

set_option maxRecDepth 100000 in
/-- `ntile(2)` over a key: the first half, rounded up, is bucket 1.
```sql
SELECT id, dept, sal, ntile(2) OVER (ORDER BY id) FROM emp;
```
-/
theorem ntile_two_ok : ∀ i,
    run i (AggQueryIn.ntile cnt (fun N r => val (if natOf r ≤ (natOf N + 1) / 2 then 1 else 2))
        (fun k : Fin 0 => k.elim0) ![0] ![OrderCol.ASC] Emp)
      = rel (ntile_two i) := by
  decide

set_option maxRecDepth 100000 in
/-- `ORDER BY … LIMIT` on a `UNION`: the truncation of the deduplicated result.
```sql
(SELECT x FROM t UNION SELECT x FROM s) ORDER BY x LIMIT 2;
```
-/
theorem setop_limit_ok : ∀ i,
    run i (AggQueryIn.truncate cnt (fun k : Fin 0 => k.elim0) ![0] ![OrderCol.ASC]
        (val 0) (val 2) (AggQueryIn.Dedup (AggQueryIn.Sum T S)) (winReadsReg_allReg _ _ _))
      = rel (setop_limit i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_truncate cnt (fun k : Fin 0 => k.elim0) ![0]
    ![OrderCol.ASC] (val 0) (val 2) (AggQueryIn.Dedup (AggQueryIn.Sum T S)) (winReadsReg_allReg _ _ _) (db i)
  simp only [run]
  rw [h]
  clear h
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `EXCLUDE CURRENT ROW`: the partition without the row itself, null where nothing is left.
```sql
SELECT id, dept, sal, sum(sal) OVER (PARTITION BY dept RANGE BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING EXCLUDE CURRENT ROW) FROM emp;
```
-/
theorem win_exclude_current_ok : ∀ i,
    run i (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) ![1] (fun k : Fin 0 => k.elim0)
        OrderSpec.unordered (ValueFrame.excludeCurrent ValueFrame.whole)
        (TermIn.index 2) sumAgg Emp (winReadsReg_allReg _ _ _))
      = rel (win_exclude_current i) := by
  decide

set_option maxRecDepth 100000 in
/-- `EXCLUDE GROUP`: the partition without the row and its peers.
```sql
SELECT id, dept, sal, count(*) OVER (PARTITION BY dept ORDER BY sal RANGE BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING EXCLUDE GROUP) FROM emp;
```
-/
theorem win_exclude_group_ok : ∀ i,
    run i (AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) ![1] ![2]
        ![OrderCol.ASC] (ValueFrame.excludeGroup ![OrderCol.ASC] ValueFrame.whole)
        (TermIn.const (val 1)) cnt Emp (winReadsReg_allReg _ _ _))
      = rel (win_exclude_group i) := by
  decide

set_option maxRecDepth 100000 in
/-- A `RANGE` frame with an offset: the rows whose salary is within 10 below the current one, and for a null salary its peers.
```sql
SELECT id, dept, sal, count(*) OVER (ORDER BY sal RANGE BETWEEN 10 PRECEDING AND CURRENT ROW) FROM emp;
```
-/
theorem win_range_offset_ok : ∀ i,
    run i (AggQueryIn.Win
        (hsql := Or.inl (ValueFrame.IsSQLUnder.noOthers
          (FrameCond.SqlBase.offToCur (fun j => Fin.fin_one_eq_zero j) (val 10))))
        (lab := 0) (rd := fun _ => false) (fun k : Fin 0 => k.elim0) ![2]
        ![OrderCol.ASC] (⟨.and (.geOff ![OrderCol.ASC] 0 true (val 10)) (.le ![OrderCol.ASC]), true⟩ : ValueFrame V 1)
        (TermIn.const (val 1)) cnt Emp (winReadsReg_allReg _ _ _))
      = rel (win_range_offset i) := by
  decide

set_option maxRecDepth 100000 in
/-- A window aggregate with a `FILTER` clause.
```sql
SELECT id, dept, sal, count(*) FILTER (WHERE sal >= 90) OVER (PARTITION BY dept) FROM emp;
```
-/
theorem win_filter_ok : ∀ i,
    run i (AggQueryIn.winFilter (hsql := sql_frame%) ![1] (fun k : Fin 0 => k.elim0) OrderSpec.unordered ValueFrame.whole
        CompOp.ge (TermIn.index 2) (TermIn.const (val 90)) (TermIn.const (val 1)) cntCol Emp)
      = rel (win_filter i) := by
  decide

end Conformance
