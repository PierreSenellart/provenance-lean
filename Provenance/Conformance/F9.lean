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
# Conformance with PostgreSQL at `F9`: recursion
-/

@[expose] public section

namespace Conformance

open WithNull

/-- The recursive term over `edge`: one more edge after a path. -/
abbrev edgeStep : AggQueryIn V 0 2 (ColKind.allReg 2) [("r", 2)] :=
  (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl), ProjColIn.term (TermGIn.index 3 rfl)]
    (AggQueryIn.Sel (GenPredIn.cmp CompOp.eq (TermGIn.index 1 rfl) (TermGIn.index 2 rfl))
      (AggQueryIn.Prod (AggQueryIn.Hole 2 "r") (AggQueryIn.Rel 2 "edge")))).castKind
    (funext fun j => by revert j; decide)

/-- The same over `cyc`. -/
abbrev cycStep : AggQueryIn V 0 2 (ColKind.allReg 2) [("r", 2)] :=
  (AggQueryIn.Proj ![ProjColIn.term (TermGIn.index 0 rfl), ProjColIn.term (TermGIn.index 3 rfl)]
    (AggQueryIn.Sel (GenPredIn.cmp CompOp.eq (TermGIn.index 1 rfl) (TermGIn.index 2 rfl))
      (AggQueryIn.Prod (AggQueryIn.Hole 2 "r") (AggQueryIn.Rel 2 "cyc")))).castKind
    (funext fun j => by revert j; decide)

set_option maxRecDepth 100000 in
/-- `WITH RECURSIVE … UNION ALL` over acyclic data: one row per path, duplicates of the edges multiplying the paths, and no path through a null.
```sql
WITH RECURSIVE r(x, y) AS (SELECT src, dst FROM edge UNION ALL SELECT r.x, e.dst FROM r, edge e WHERE r.y = e.src) SELECT x, y FROM r;
```
-/
theorem rec_union_all_ok : ∀ i,
    run i (AggQueryIn.Mu "r" (AggQueryIn.Rel 2 "edge") edgeStep)
      = rel (rec_union_all i) := by
  intro i
  simp only [run, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  rw [muSumFix_eq_of_empty (k := 5) (by revert i; decide) (by revert i; decide)]
  revert i
  decide

set_option maxRecDepth 100000 in
/-- `WITH RECURSIVE … UNION` over cyclic data: the pairs joined by a path, each once.
```sql
WITH RECURSIVE r(x, y) AS (SELECT src, dst FROM cyc UNION SELECT r.x, e.dst FROM r, cyc e WHERE r.y = e.src) SELECT x, y FROM r;
```
-/
theorem rec_union_ok : ∀ i,
    run i (AggQueryIn.MuSet "r" (AggQueryIn.Rel 2 "cyc") cycStep)
      = rel (rec_union i) := by
  intro i
  simp only [run, AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  rw [muFix_eq_of_fix (j := 4) (by revert i; decide)]
  revert i
  decide

end Conformance
