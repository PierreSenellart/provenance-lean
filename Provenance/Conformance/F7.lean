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

end Conformance
