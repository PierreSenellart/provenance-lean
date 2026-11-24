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
# Conformance with PostgreSQL at `F3`: functions over values
-/

@[expose] public section

namespace Conformance

open WithNull

/-- Arithmetic is null-strict.
```sql
SELECT x + 1 FROM t;
```
-/
theorem proj_add_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.add (col 0) (lit 1))] T)
      = rel (proj_add i) := by decide

set_option maxRecDepth 100000 in
/-- A `CASE` whose guard is unknown takes its `ELSE`.
```sql
SELECT CASE WHEN x = 1 THEN 10 ELSE 20 END FROM t;
```
-/
theorem proj_case_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.caseWhen CompOp.eq (col 0) (lit 1) (lit 10) (lit 20))] T)
      = rel (proj_case i) := by
  decide

set_option maxRecDepth 100000 in
/-- `COALESCE` is not null-strict.
```sql
SELECT COALESCE(x, 7) FROM t;
```
-/
theorem proj_coalesce_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.coalesce (col 0) (lit 7))] T)
      = rel (proj_coalesce i) := by
  decide

set_option maxRecDepth 100000 in
/-- A product and a sum, both null-strict.
```sql
SELECT x * 2 + x FROM t;
```
-/
theorem proj_mul_add_ok : ∀ i,
    run i (AggQueryIn.Proj ![ProjColIn.term (TermGIn.add (TermGIn.mul (col 0) (lit 2)) (col 0))] T)
      = rel (proj_mul_add i) := by
  decide

end Conformance
