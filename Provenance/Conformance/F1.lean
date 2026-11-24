/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Conformance.Basic
public import Provenance.Extensionality
import all Provenance.Database
import all Provenance.Query
import all Provenance.AggQuery
import all Provenance.FragQuery

/-!
# Conformance with PostgreSQL at `F1`: duplicate elimination, existence and membership

Each query is a term of the fragment syntax `FragQueryIn`, read in the
general syntax by `FragQueryIn.toAgg`, so that its membership in the level
is the library's own (`AggQueryIn.InLevel1`). A second statement says that
the term, as written, is not of the level below.
-/

@[expose] public section

namespace Conformance

open WithNull

/-- `DISTINCT` keeps one copy, two nulls being one value.
```sql
SELECT DISTINCT x FROM t;
```
-/
abbrev distinct_q : FragQuery V 1 :=
  .Dedup fT

set_option maxRecDepth 100000 in
theorem distinct_ok : ∀ i,
    run i distinct_q.toAgg = rel (distinct i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem distinct_level : AggQueryIn.InLevel1 distinct_q.toAgg ∧ ¬ distinct_q.level0 :=
  ⟨⟨distinct_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `EXISTS` keeps a department once, however many employees it has.
```sql
SELECT d, name FROM dept WHERE EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d);
```
-/
abbrev exists_semi_q : FragQuery V 2 :=
  .Semijoin cntCol cntCol_counts sameDept fDept (.Rel 3 "emp")

set_option maxRecDepth 100000 in
theorem exists_semi_ok : ∀ i,
    run i exists_semi_q.toAgg = rel (exists_semi i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem exists_semi_level : AggQueryIn.InLevel1 exists_semi_q.toAgg ∧ ¬ exists_semi_q.level0 :=
  ⟨⟨exists_semi_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `IN` is the semijoin on equality: a null key is in nothing.
```sql
SELECT d, name FROM dept WHERE d IN (SELECT dept FROM emp);
```
-/
abbrev in_sub_q : FragQuery V 2 :=
  .Semijoin cntCol cntCol_counts sameDept fDept (.Rel 3 "emp")

set_option maxRecDepth 100000 in
theorem in_sub_ok : ∀ i,
    run i in_sub_q.toAgg = rel (in_sub i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem in_sub_level : AggQueryIn.InLevel1 in_sub_q.toAgg ∧ ¬ in_sub_q.level0 :=
  ⟨⟨in_sub_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `INTERSECT`, as the join of the two deduplicated sides on syntactic equality: the null is in both.
```sql
SELECT x FROM t INTERSECT SELECT x FROM s;
```
-/
abbrev intersect_set_q : FragQuery V 1 :=
  .Proj ![col 0] (.Sel (.cmp .syneq (col 0) (col 1)) (.Prod (.Dedup fT) (.Dedup fS)))

set_option maxRecDepth 100000 in
theorem intersect_set_ok : ∀ i,
    run i intersect_set_q.toAgg = rel (intersect_set i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem intersect_set_level : AggQueryIn.InLevel1 intersect_set_q.toAgg ∧ ¬ intersect_set_q.level0 :=
  ⟨⟨intersect_set_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

end Conformance
