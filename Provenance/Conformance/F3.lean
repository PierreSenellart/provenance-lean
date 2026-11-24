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

end Conformance
