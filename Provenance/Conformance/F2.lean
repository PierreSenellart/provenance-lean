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

end Conformance
