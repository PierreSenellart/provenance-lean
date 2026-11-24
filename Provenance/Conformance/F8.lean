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
# Conformance with PostgreSQL at `F8`: aggregate values as data
-/

@[expose] public section

namespace Conformance

open WithNull

/-- The count of each department, read as a key: the aggregate column made
regular, and kept alone. -/
abbrev countAsKey : AggQuery V 1 (ColKind.allReg 1) :=
  (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 1 rfl)]
    (AggQueryIn.Explode 1 rfl (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp))).castKind
    (funext fun j => by revert j; decide)

set_option maxRecDepth 100000 in
/-- A `DISTINCT` over a count: the count is read as a key.
```sql
SELECT DISTINCT c FROM (SELECT dept, count(*) AS c FROM emp GROUP BY dept) g;
```
-/
theorem distinct_count_ok : ∀ i,
    run i (AggQueryIn.Dedup countAsKey)
      = rel (distinct_count i) := by
  intro i
  simp only [run, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- A grouping on a count.
```sql
SELECT c, count(*) FROM (SELECT dept, count(*) AS c FROM emp GROUP BY dept) g GROUP BY c;
```
-/
theorem group_on_count_ok : ∀ i,
    run i (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![0] ![TermIn.const (val 1)] ![cnt] countAsKey)
      = rel (group_on_count i) := by
  intro i
  simp only [run, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- A sum over the counts of an inner grouping: the count is read as a value.
```sql
SELECT dept, sum(c) FROM (SELECT dept, sal, count(*) AS c FROM emp GROUP BY dept, sal) g GROUP BY dept;
```
-/
theorem sum_of_counts_ok : ∀ i,
    run i (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) ![0]
        (fun k => by revert k; decide) (ProjColIn.token 2 rfl)
        (fun s => val (s.map natOf).sum)
        (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1, 2] ![TermIn.const (val 1)] ![cnt] Emp))
      = rel (sum_of_counts i) := by
  decide

set_option maxRecDepth 100000 in
/-- A rank over a count: the count is read as a key.
```sql
SELECT dept, c, rank() OVER (ORDER BY c DESC) FROM (SELECT dept, count(*) AS c FROM emp GROUP BY dept) g;
```
-/
theorem rank_over_count_ok : ∀ i,
    run i (AggQueryIn.rank cnt (fun k : Fin 0 => k.elim0) ![1] ![OrderCol.DESC]
        (AggQueryIn.Explode 1 rfl (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)) ⟨fun k => k.elim0, by decide, by decide⟩)
      = rel (rank_over_count i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_rank cnt (fun k : Fin 0 => k.elim0) ![1] ![OrderCol.DESC]
    (AggQueryIn.Explode 1 rfl (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)) ⟨fun k => k.elim0, by decide, by decide⟩ (db i)
  simp only [run]
  rw [h]
  clear h
  simp only [AggQueryIn.evaluatePlain]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- A `LIMIT` ordered by a count, then by the key of the group.
```sql
SELECT dept, c FROM (SELECT dept, count(*) AS c FROM emp GROUP BY dept) g ORDER BY c DESC, dept LIMIT 1;
```
-/
theorem limit_on_count_ok : ∀ i,
    run i (AggQueryIn.truncate cnt (fun k : Fin 0 => k.elim0) ![1, 0] ![OrderCol.DESC, OrderCol.ASC]
        (val 0) (val 1) (AggQueryIn.Explode 1 rfl (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)) ⟨fun k => k.elim0, by decide, by decide⟩)
      = rel (limit_on_count i) := by
  intro i
  have h := AggQueryIn.evaluatePlain_truncate cnt (fun k : Fin 0 => k.elim0) ![1, 0]
    ![OrderCol.DESC, OrderCol.ASC] (val 0) (val 1) (AggQueryIn.Explode 1 rfl (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1] ![TermIn.const (val 1)] ![cnt] Emp)) ⟨fun k => k.elim0, by decide, by decide⟩ (db i)
  simp only [run]
  rw [h]
  clear h
  simp only [AggQueryIn.evaluatePlain]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- A maximum over the maxima of an inner grouping.
```sql
SELECT dept, max(m) FROM (SELECT dept, sal, max(id) AS m FROM emp GROUP BY dept, sal) g GROUP BY dept;
```
-/
theorem max_of_max_ok : ∀ i,
    run i (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) ![0]
        (fun k => by revert k; decide) (ProjColIn.token 2 rfl)
        (fun s => val ((s.map natOf).sup))
        (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1, 2] ![TermIn.index 0] ![maxAgg] Emp))
      = rel (max_of_max i) := by
  decide

set_option maxRecDepth 100000 in
/-- A sum over the sums of an inner grouping, a null inner sum skipped.
```sql
SELECT dept, sum(v) FROM (SELECT dept, sal, sum(sal) AS v FROM emp GROUP BY dept, sal) g GROUP BY dept;
```
-/
theorem sum_of_sums_ok : ∀ i,
    run i (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) ![0]
        (fun k => by revert k; decide) (ProjColIn.token 2 rfl)
        (fun s => if s.filter (fun v => v ≠ nil) = 0 then nil
          else val ((s.filter (fun v => v ≠ nil)).map natOf).sum)
        (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1, 2] ![TermIn.index 2] ![sumAgg] Emp))
      = rel (sum_of_sums i) := by
  decide

set_option maxRecDepth 100000 in
/-- A count over the counts of an inner grouping: the number of inner groups.
```sql
SELECT dept, count(c) FROM (SELECT dept, sal, count(*) AS c FROM emp GROUP BY dept, sal) g GROUP BY dept;
```
-/
theorem count_of_counts_ok : ∀ i,
    run i (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) ![0]
        (fun k => by revert k; decide) (ProjColIn.token 2 rfl)
        (fun s => val (Multiset.card s))
        (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![1, 2] ![TermIn.const (val 1)] ![cnt] Emp))
      = rel (count_of_counts i) := by
  decide

end Conformance
