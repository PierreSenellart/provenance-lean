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

/-- A `GROUP BY` with no aggregate is a `DISTINCT`: the null key is one group.
```sql
SELECT dept FROM emp GROUP BY dept;
```
-/
abbrev group_no_agg_q : FragQuery V 1 :=
  .Dedup (.Proj ![col 1] (.Rel 3 "emp"))

set_option maxRecDepth 100000 in
theorem group_no_agg_ok : ∀ i,
    run i group_no_agg_q.toAgg = rel (group_no_agg i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem group_no_agg_level : AggQueryIn.InLevel1 group_no_agg_q.toAgg ∧ ¬ group_no_agg_q.level0 :=
  ⟨⟨group_no_agg_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `UNION` is the sum, deduplicated.
```sql
SELECT x FROM t UNION SELECT x FROM s;
```
-/
abbrev union_set_q : FragQuery V 1 :=
  .Dedup (.Sum fT fS)

set_option maxRecDepth 100000 in
theorem union_set_ok : ∀ i,
    run i union_set_q.toAgg = rel (union_set i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem union_set_level : AggQueryIn.InLevel1 union_set_q.toAgg ∧ ¬ union_set_q.level0 :=
  ⟨⟨union_set_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `DISTINCT` on two columns: tuples are compared whole, nulls equal.
```sql
SELECT DISTINCT dept, sal FROM emp;
```
-/
abbrev distinct_pair_q : FragQuery V 2 :=
  .Dedup (.Proj ![col 1, col 2] (.Rel 3 "emp"))

set_option maxRecDepth 100000 in
theorem distinct_pair_ok : ∀ i,
    run i distinct_pair_q.toAgg = rel (distinct_pair i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem distinct_pair_level : AggQueryIn.InLevel1 distinct_pair_q.toAgg ∧ ¬ distinct_pair_q.level0 :=
  ⟨⟨distinct_pair_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `IN` over a subquery holding a null: the null is in nothing, the other values as usual.
```sql
SELECT x FROM t WHERE x IN (SELECT x FROM s);
```
-/
abbrev in_null_sub_q : FragQuery V 1 :=
  .Semijoin cntCol cntCol_counts (.cmp .eq (col 0) (TermGIn.outer 0)) fT (.Rel 1 "s")

set_option maxRecDepth 100000 in
theorem in_null_sub_ok : ∀ i,
    run i in_null_sub_q.toAgg = rel (in_null_sub i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem in_null_sub_level : AggQueryIn.InLevel1 in_null_sub_q.toAgg ∧ ¬ in_null_sub_q.level0 :=
  ⟨⟨in_null_sub_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- An uncorrelated `EXISTS` keeps every row or none.
```sql
SELECT x FROM t WHERE EXISTS (SELECT 1 FROM u);
```
-/
abbrev exists_uncorrelated_q : FragQuery V 1 :=
  .Semijoin cntCol cntCol_counts (.cmp .syneq (lit 0) (lit 0)) fT (.Rel 1 "u")

set_option maxRecDepth 100000 in
theorem exists_uncorrelated_ok : ∀ i,
    run i exists_uncorrelated_q.toAgg = rel (exists_uncorrelated i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem exists_uncorrelated_level : AggQueryIn.InLevel1 exists_uncorrelated_q.toAgg ∧ ¬ exists_uncorrelated_q.level0 :=
  ⟨⟨exists_uncorrelated_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `> ANY` is the semijoin on that comparison: unknown comparisons match nothing.
```sql
SELECT x FROM t WHERE x > ANY (SELECT x FROM s);
```
-/
abbrev any_sub_q : FragQuery V 1 :=
  .Semijoin cntCol cntCol_counts (.cmp .gt (TermGIn.outer 0) (col 0)) fT (.Rel 1 "s")

set_option maxRecDepth 100000 in
theorem any_sub_ok : ∀ i,
    run i any_sub_q.toAgg = rel (any_sub i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem any_sub_level : AggQueryIn.InLevel1 any_sub_q.toAgg ∧ ¬ any_sub_q.level0 :=
  ⟨⟨any_sub_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- `IN` on a row is the semijoin on the conjunction of the equalities.
```sql
SELECT d, name FROM dept WHERE (d, d) IN (SELECT dept, dept FROM emp);
```
-/
abbrev row_in_q : FragQuery V 2 :=
  .Semijoin cntCol cntCol_counts
    (.and (.cmp .eq (TermGIn.outer 0) (col 1)) (.cmp .eq (TermGIn.outer 0) (col 1)))
    fDept (.Rel 3 "emp")

set_option maxRecDepth 100000 in
theorem row_in_ok : ∀ i,
    run i row_in_q.toAgg = rel (row_in i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem row_in_level : AggQueryIn.InLevel1 row_in_q.toAgg ∧ ¬ row_in_q.level0 :=
  ⟨⟨row_in_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- A subquery whose body is a set operation.
```sql
SELECT x FROM t WHERE x IN (SELECT x FROM s UNION SELECT x FROM u);
```
-/
abbrev in_union_body_q : FragQuery V 1 :=
  .Semijoin cntCol cntCol_counts (.cmp .eq (col 0) (TermGIn.outer 0)) fT
    (.Dedup (.Sum (.Rel 1 "s") (.Rel 1 "u")))

set_option maxRecDepth 100000 in
theorem in_union_body_ok : ∀ i,
    run i in_union_body_q.toAgg = rel (in_union_body i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem in_union_body_level : AggQueryIn.InLevel1 in_union_body_q.toAgg ∧ ¬ in_union_body_q.level0 :=
  ⟨⟨in_union_body_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

/-- A block with no relation of its own: the semijoin of the unit row.
```sql
SELECT 1 WHERE EXISTS (SELECT 1 FROM u);
```
-/
abbrev exists_no_relation_q : FragQuery V 1 :=
  .Semijoin cntCol cntCol_counts (.cmp .syneq (lit 0) (lit 0)) (.Proj ![lit 1] .Unit) (.Rel 1 "u")

set_option maxRecDepth 100000 in
theorem exists_no_relation_ok : ∀ i,
    run i exists_no_relation_q.toAgg = rel (exists_no_relation i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem exists_no_relation_level : AggQueryIn.InLevel1 exists_no_relation_q.toAgg ∧ ¬ exists_no_relation_q.level0 :=
  ⟨⟨exists_no_relation_q, by simp [FragQueryIn.level1], rfl⟩, by simp [FragQueryIn.level0]⟩

end Conformance
