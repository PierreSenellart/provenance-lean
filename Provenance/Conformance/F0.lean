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

end Conformance
