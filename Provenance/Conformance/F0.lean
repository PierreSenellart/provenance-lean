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
import all Provenance.Derived

/-!
# Conformance with PostgreSQL at `F0`: joins and multiset union

Each query is a term of the fragment syntax `FragQueryIn`, read in the
general syntax by `FragQueryIn.toAgg`, so that its membership in the level
is the library's own (`AggQueryIn.InLevel0`).
-/

@[expose] public section

namespace Conformance

open WithNull

/-- A base relation keeps its duplicates.
```sql
SELECT x FROM t;
```
-/
abbrev rel_dups_q : FragQuery V 1 :=
  fT

set_option maxRecDepth 100000 in
theorem rel_dups_ok : ∀ i,
    run i rel_dups_q.toAgg = rel (rel_dups i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem rel_dups_level : AggQueryIn.InLevel0 rel_dups_q.toAgg :=
  ⟨rel_dups_q, by simp [FragQueryIn.level0], rfl⟩

/-- A selection keeps the rows on which the comparison is true.
```sql
SELECT x FROM t WHERE x = 1;
```
-/
abbrev sel_eq_q : FragQuery V 1 :=
  .Sel (.cmp .eq (col 0) (lit 1)) fT

set_option maxRecDepth 100000 in
theorem sel_eq_ok : ∀ i,
    run i sel_eq_q.toAgg = rel (sel_eq i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem sel_eq_level : AggQueryIn.InLevel0 sel_eq_q.toAgg :=
  ⟨sel_eq_q, by simp [FragQueryIn.level0], rfl⟩

/-- The negation of an unknown comparison is unknown: the nulls stay out.
```sql
SELECT x FROM t WHERE NOT (x = 1);
```
-/
abbrev sel_not_eq_q : FragQuery V 1 :=
  .Sel (.not (.cmp .eq (col 0) (lit 1))) fT

set_option maxRecDepth 100000 in
theorem sel_not_eq_ok : ∀ i,
    run i sel_not_eq_q.toAgg = rel (sel_not_eq i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem sel_not_eq_level : AggQueryIn.InLevel0 sel_not_eq_q.toAgg :=
  ⟨sel_not_eq_q, by simp [FragQueryIn.level0], rfl⟩

/-- `IS NULL` is true on a null.
```sql
SELECT x FROM t WHERE x IS NULL;
```
-/
abbrev sel_is_null_q : FragQuery V 1 :=
  .Sel (isNull (col 0)) fT

set_option maxRecDepth 100000 in
theorem sel_is_null_ok : ∀ i,
    run i sel_is_null_q.toAgg = rel (sel_is_null i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem sel_is_null_level : AggQueryIn.InLevel0 sel_is_null_q.toAgg :=
  ⟨sel_is_null_q, by simp [FragQueryIn.level0], rfl⟩

/-- `UNION ALL` adds multiplicities.
```sql
SELECT x FROM t UNION ALL SELECT x FROM s;
```
-/
abbrev union_all_q : FragQuery V 1 :=
  .Sum fT fS

set_option maxRecDepth 100000 in
theorem union_all_ok : ∀ i,
    run i union_all_q.toAgg = rel (union_all i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem union_all_level : AggQueryIn.InLevel0 union_all_q.toAgg :=
  ⟨union_all_q, by simp [FragQueryIn.level0], rfl⟩

/-- A join condition is unknown on a null: neither null of `t` matches the null of `s`.
```sql
SELECT t.x, s.x FROM t, s WHERE t.x = s.x;
```
-/
abbrev join_eq_q : FragQuery V 2 :=
  .Sel (.cmp .eq (col 0) (col 1)) (.Prod fT fS)

set_option maxRecDepth 100000 in
theorem join_eq_ok : ∀ i,
    run i join_eq_q.toAgg = rel (join_eq i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem join_eq_level : AggQueryIn.InLevel0 join_eq_q.toAgg :=
  ⟨join_eq_q, by simp [FragQueryIn.level0], rfl⟩

/-- A `LATERAL` subquery is read once per row of the left side, and a row with no match is dropped.
```sql
SELECT d.d, d.name, e.id FROM dept d, LATERAL (SELECT id FROM emp WHERE emp.dept = d.d) e;
```
-/
abbrev lateral_apply_q : FragQuery V 3 :=
  .Proj ![col 0, col 1, col 2] (.Apply fDept (.Proj ![col 0] (.Sel sameDept (.Rel 3 "emp"))))

set_option maxRecDepth 100000 in
theorem lateral_apply_ok : ∀ i,
    run i lateral_apply_q.toAgg = rel (lateral_apply i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem lateral_apply_level : AggQueryIn.InLevel0 lateral_apply_q.toAgg :=
  ⟨lateral_apply_q, by simp [FragQueryIn.level0], rfl⟩

set_option maxRecDepth 100000 in
/-- `VALUES` is a constant relation, duplicates kept.
```sql
SELECT * FROM (VALUES (1,2),(1,2),(3,NULL::int)) v;
```
-/
theorem values_rows_ok : ∀ i,
    run i (AggQueryIn.values [![val 1, val 2], ![val 1, val 2], ![val 3, nil]] (by simp))
      = rel (values_rows i) := by
  intro i
  simp only [run]
  rw [AggQueryIn.evaluatePlain_values]
  revert i
  decide

/-- A self-join multiplies the duplicates and matches no null.
```sql
SELECT a.x, b.x FROM t a, t b WHERE a.x = b.x;
```
-/
abbrev self_join_dups_q : FragQuery V 2 :=
  .Sel (.cmp .eq (col 0) (col 1)) (.Prod fT fT)

set_option maxRecDepth 100000 in
theorem self_join_dups_ok : ∀ i,
    run i self_join_dups_q.toAgg = rel (self_join_dups i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem self_join_dups_level : AggQueryIn.InLevel0 self_join_dups_q.toAgg :=
  ⟨self_join_dups_q, by simp [FragQueryIn.level0], rfl⟩

/-- A disjunction is true when one side is, the other being unknown.
```sql
SELECT x FROM t WHERE x = 1 OR x IS NULL;
```
-/
abbrev sel_or_null_q : FragQuery V 1 :=
  .Sel (.or (.cmp .eq (col 0) (lit 1)) (isNull (col 0))) fT

set_option maxRecDepth 100000 in
theorem sel_or_null_ok : ∀ i,
    run i sel_or_null_q.toAgg = rel (sel_or_null i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem sel_or_null_level : AggQueryIn.InLevel0 sel_or_null_q.toAgg :=
  ⟨sel_or_null_q, by simp [FragQueryIn.level0], rfl⟩

/-- A conjunction of two comparisons.
```sql
SELECT x FROM t WHERE x > 1 AND x < 3;
```
-/
abbrev sel_and_range_q : FragQuery V 1 :=
  .Sel (.and (.cmp .gt (col 0) (lit 1)) (.cmp .lt (col 0) (lit 3))) fT

set_option maxRecDepth 100000 in
theorem sel_and_range_ok : ∀ i,
    run i sel_and_range_q.toAgg = rel (sel_and_range i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem sel_and_range_level : AggQueryIn.InLevel0 sel_and_range_q.toAgg :=
  ⟨sel_and_range_q, by simp [FragQueryIn.level0], rfl⟩

/-- `<>` is unknown on a null, like `=`.
```sql
SELECT x FROM t WHERE x <> 1;
```
-/
abbrev sel_ne_q : FragQuery V 1 :=
  .Sel (.cmp .ne (col 0) (lit 1)) fT

set_option maxRecDepth 100000 in
theorem sel_ne_ok : ∀ i,
    run i sel_ne_q.toAgg = rel (sel_ne i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem sel_ne_level : AggQueryIn.InLevel0 sel_ne_q.toAgg :=
  ⟨sel_ne_q, by simp [FragQueryIn.level0], rfl⟩

/-- `IS NOT NULL` is the negation of a test that is never unknown.
```sql
SELECT x FROM t WHERE x IS NOT NULL;
```
-/
abbrev sel_is_not_null_q : FragQuery V 1 :=
  .Sel (.not (isNull (col 0))) fT

set_option maxRecDepth 100000 in
theorem sel_is_not_null_ok : ∀ i,
    run i sel_is_not_null_q.toAgg = rel (sel_is_not_null i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem sel_is_not_null_level : AggQueryIn.InLevel0 sel_is_not_null_q.toAgg :=
  ⟨sel_is_not_null_q, by simp [FragQueryIn.level0], rfl⟩

/-- A constant column beside a column.
```sql
SELECT 5, x FROM t;
```
-/
abbrev proj_const_q : FragQuery V 2 :=
  .Proj ![lit 5, col 0] fT

set_option maxRecDepth 100000 in
theorem proj_const_ok : ∀ i,
    run i proj_const_q.toAgg = rel (proj_const i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem proj_const_level : AggQueryIn.InLevel0 proj_const_q.toAgg :=
  ⟨proj_const_q, by simp [FragQueryIn.level0], rfl⟩

/-- A `SELECT` with no `FROM` is one row, on every instance.
```sql
SELECT 1, 2;
```
-/
abbrev select_no_from_q : FragQuery V 2 :=
  .Proj ![lit 1, lit 2] .Unit

set_option maxRecDepth 100000 in
theorem select_no_from_ok : ∀ i,
    run i select_no_from_q.toAgg = rel (select_no_from i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem select_no_from_level : AggQueryIn.InLevel0 select_no_from_q.toAgg :=
  ⟨select_no_from_q, by simp [FragQueryIn.level0], rfl⟩

/-- A product pairs every row with every row, nulls included.
```sql
SELECT s.x, u.x FROM s, u;
```
-/
abbrev cross_product_q : FragQuery V 2 :=
  .Prod fS fU

set_option maxRecDepth 100000 in
theorem cross_product_ok : ∀ i,
    run i cross_product_q.toAgg = rel (cross_product i) := by
  intro i
  simp only [run]
  rw [FragQueryIn.toAgg_evaluatePlain]
  revert i
  decide

theorem cross_product_level : AggQueryIn.InLevel0 cross_product_q.toAgg :=
  ⟨cross_product_q, by simp [FragQueryIn.level0], rfl⟩

end Conformance
