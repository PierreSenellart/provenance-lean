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
# Conformance with PostgreSQL at `F2`: difference and negation

Each query is a term of the fragment syntax `FragQueryIn`, read in the
general syntax by `FragQueryIn.toAgg`, so that its membership in the level
is the library's own (`AggQueryIn.InLevel2`). A second statement says that
the term, as written, is not of the level below.
-/

@[expose] public section

namespace Conformance

open WithNull

/-- `EXCEPT` is the difference, deduplicated: a null on the right removes the nulls.
```sql
SELECT x FROM t EXCEPT SELECT x FROM s;
```
-/
abbrev except_set_q : FragQuery V 1 :=
  .Dedup (.Diff fT fS)

set_option maxRecDepth 100000 in
theorem except_set_ok : ∀ i,
    run i except_set_q.toAgg = rel (except_set i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem except_set_level : AggQueryIn.InLevel2 except_set_q.toAgg ∧ ¬ except_set_q.level1 :=
  ⟨⟨except_set_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- The difference drops every copy of a tuple the right side holds, and keeps the duplicates of the others.
```sql
SELECT x FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.x IS NOT DISTINCT FROM t.x);
```
-/
abbrev diff_keeps_dups_q : FragQuery V 1 :=
  .Diff fT fU

set_option maxRecDepth 100000 in
theorem diff_keeps_dups_ok : ∀ i,
    run i diff_keeps_dups_q.toAgg = rel (diff_keeps_dups i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem diff_keeps_dups_level : AggQueryIn.InLevel2 diff_keeps_dups_q.toAgg ∧ ¬ diff_keeps_dups_q.level1 :=
  ⟨⟨diff_keeps_dups_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- `NOT EXISTS` keeps the department whose key is null: its comparison is unknown on every employee, so nothing matches.
```sql
SELECT d, name FROM dept WHERE NOT EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d);
```
-/
abbrev not_exists_anti_q : FragQuery V 2 :=
  .Antijoin cntCol cntCol_counts sameDept fDept (.Rel 3 "emp")

set_option maxRecDepth 100000 in
theorem not_exists_anti_ok : ∀ i,
    run i not_exists_anti_q.toAgg = rel (not_exists_anti i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem not_exists_anti_level : AggQueryIn.InLevel2 not_exists_anti_q.toAgg ∧ ¬ not_exists_anti_q.level1 :=
  ⟨⟨not_exists_anti_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- `EXCEPT` the other way round.
```sql
SELECT x FROM s EXCEPT SELECT x FROM t;
```
-/
abbrev except_rev_q : FragQuery V 1 :=
  .Dedup (.Diff fS fT)

set_option maxRecDepth 100000 in
theorem except_rev_ok : ∀ i,
    run i except_rev_q.toAgg = rel (except_rev i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem except_rev_level : AggQueryIn.InLevel2 except_rev_q.toAgg ∧ ¬ except_rev_q.level1 :=
  ⟨⟨except_rev_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- An uncorrelated `NOT EXISTS` keeps every row or none.
```sql
SELECT x FROM t WHERE NOT EXISTS (SELECT 1 FROM u);
```
-/
abbrev not_exists_uncorrelated_q : FragQuery V 1 :=
  .Antijoin cntCol cntCol_counts (.cmp .syneq (lit 0) (lit 0)) fT (.Rel 1 "u")

set_option maxRecDepth 100000 in
theorem not_exists_uncorrelated_ok : ∀ i,
    run i not_exists_uncorrelated_q.toAgg = rel (not_exists_uncorrelated i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem not_exists_uncorrelated_level : AggQueryIn.InLevel2 not_exists_uncorrelated_q.toAgg ∧ ¬ not_exists_uncorrelated_q.level1 :=
  ⟨⟨not_exists_uncorrelated_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- `NOT EXISTS` on an equality keeps the nulls, on which the comparison is unknown.
```sql
SELECT x FROM t WHERE NOT EXISTS (SELECT 1 FROM s WHERE s.x = t.x);
```
-/
abbrev not_exists_self_q : FragQuery V 1 :=
  .Antijoin cntCol cntCol_counts (.cmp .eq (col 0) (TermGIn.outer 0)) fT (.Rel 1 "s")

set_option maxRecDepth 100000 in
theorem not_exists_self_ok : ∀ i,
    run i not_exists_self_q.toAgg = rel (not_exists_self i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem not_exists_self_level : AggQueryIn.InLevel2 not_exists_self_q.toAgg ∧ ¬ not_exists_self_q.level1 :=
  ⟨⟨not_exists_self_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- A `NOT EXISTS` inside a `NOT EXISTS`: the departments all of whose employees have their salary in `s`.
```sql
SELECT d, name FROM dept WHERE NOT EXISTS (SELECT 1 FROM emp WHERE emp.dept = dept.d AND NOT EXISTS (SELECT 1 FROM s WHERE s.x = emp.sal));
```
-/
abbrev nested_not_exists_q : FragQuery V 2 :=
  .Antijoin cntCol cntCol_counts sameDept fDept
    (.Antijoin cntCol cntCol_counts (.cmp .eq (col 0) (TermGIn.outer 2)) (.Rel 3 "emp") (.Rel 1 "s"))

set_option maxRecDepth 100000 in
theorem nested_not_exists_ok : ∀ i,
    run i nested_not_exists_q.toAgg = rel (nested_not_exists i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem nested_not_exists_level : AggQueryIn.InLevel2 nested_not_exists_q.toAgg ∧ ¬ nested_not_exists_q.level1 :=
  ⟨⟨nested_not_exists_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- An `EXCEPT` over a `UNION ALL`.
```sql
(SELECT x FROM t UNION ALL SELECT x FROM s) EXCEPT SELECT x FROM u;
```
-/
abbrev setop_nested_q : FragQuery V 1 :=
  .Dedup (.Diff (.Sum fT fS) fU)

set_option maxRecDepth 100000 in
theorem setop_nested_ok : ∀ i,
    run i setop_nested_q.toAgg = rel (setop_nested i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem setop_nested_level : AggQueryIn.InLevel2 setop_nested_q.toAgg ∧ ¬ setop_nested_q.level1 :=
  ⟨⟨setop_nested_q, rfl⟩, by simp [FragQueryIn.level1]⟩

/-- `EXCEPT` against constant rows.
```sql
SELECT x FROM t EXCEPT VALUES (1), (5);
```
-/
abbrev except_values_q : FragQuery V 1 :=
  .Dedup (.Diff fT (.Sum (.Proj ![lit 1] .Unit) (.Proj ![lit 5] .Unit)))

set_option maxRecDepth 100000 in
theorem except_values_ok : ∀ i,
    run i except_values_q.toAgg = rel (except_values i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem except_values_level : AggQueryIn.InLevel2 except_values_q.toAgg ∧ ¬ except_values_q.level1 :=
  ⟨⟨except_values_q, rfl⟩, by simp [FragQueryIn.level1]⟩

end Conformance
