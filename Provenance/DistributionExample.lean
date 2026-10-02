/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Derived
import Provenance.QueryAdequacy

/-!
# The distribution functions, and the two ranks, on a worked relation

`percent_rank`, `cume_dist` and `ntile` are aggregate expressions over
two frames of one partition (`AggQueryIn.WinExpr`), so what they compute
is not read off either frame alone. This file checks the values against
SQL's on a three-row relation, including the two cases where a reading
that treated the two frames separately would go wrong: a partition of
one row, where `percent_rank` is `0` by its own clause rather than by
dividing by zero, and a partition with peers, where the rank keeps a
class together.

The arithmetic is the parameter each of the three takes: here the
numerators are scaled by `100` so that `ℕ`'s truncating division shows
the fraction.

The file also contrasts `rank` with `dense_rank`, which differ exactly
where the order has peers: the one counts rows before a class, the other
counts distinct order values.

The checks are `#eval`s, as the worked example of `Provenance.Example`
is: the plain evaluator sorts each frame, and the kernel does not reduce
through that, so neither `decide` nor `rfl` closes an equation about a
computed relation. The expected values are stated with each one, and a
change in behaviour shows as changed output at build time.
-/

namespace DistributionExample

/-! Three rows in one partition, ordered by their only column. -/
abbrev R3 : Relation ℕ 1 := (([![10], ![20], ![30]] : List (Tuple ℕ 1)) : Multiset _)

/-- The database holding it. -/
abbrev D3 : Database ℕ := [("R", ⟨1, R3⟩)]

/-- One row, for the `N = 1` clause of `percent_rank`. -/
abbrev R1 : Relation ℕ 1 := (([![7]] : List (Tuple ℕ 1)) : Multiset _)

/-- Its database. -/
abbrev D1 : Database ℕ := [("R", ⟨1, R1⟩)]

/-- Two rows tied at `10` and one at `30`. -/
abbrev R4 : Relation ℕ 1 := (([![10], ![10], ![30]] : List (Tuple ℕ 1)) : Multiset _)

/-- Its database. -/
abbrev D4 : Database ℕ := [("R", ⟨1, R4⟩)]

/-- The base query. -/
abbrev base : AggQuery ℕ 1 (ColKind.allReg 1) := AggQueryIn.Rel 1 "R"

/-- Ascending on the only column. -/
abbrev ord : OrderSpec 1 := OrderSpec.asc 1

/-- No partitioning: the whole relation is one partition. -/
abbrev noP : Fin 0 → Fin 1 := fun _ => 0

/-- Division scaled by `100`, so a fraction is visible over `ℕ`. -/
abbrev pct : ℕ → ℕ → ℕ := fun a b => a * 100 / b

/-- SQL's `ntile` bucket of the rank `r` among `N` rows, for two
buckets. -/
abbrev two : ℕ → ℕ → ℕ := fun N r => (r - 1) * 2 / N + 1

/-! **`percent_rank` on three distinct rows**: `(r-1)/(N-1)`, so `0`,
`1/2`, `1` – printed as `0, 50, 100`. -/
#eval ((AggQueryIn.percentRank SeqAggFunc.count pct noP ![0] ord
  base).evaluatePlain D3).map (fun u => (u 0, u 1))

/-! **`cume_dist` on the same**: `c/N` with `c` over the rows up to the
current one and its peers, so `1/3`, `2/3`, `1` – `33, 66, 100`. -/
#eval ((AggQueryIn.cumeDist SeqAggFunc.count pct noP ![0] ord
  base).evaluatePlain D3).map (fun u => (u 0, u 1))

/-! **`ntile(2)` on three rows**: buckets `1, 1, 2`. -/
#eval ((AggQueryIn.ntile SeqAggFunc.count two noP ![0] ord
  base).evaluatePlain D3).map (fun u => (u 0, u 1))

/-! **`percent_rank` on one row is `0`**, by its own clause for `N = 1`
and not by a division. This is the case a reading of the two frames as
separate aggregates would have to invent a value for. -/
#eval ((AggQueryIn.percentRank SeqAggFunc.count pct noP ![0] ord
  base).evaluatePlain D1).map (fun u => (u 0, u 1))

/-! **`percent_rank` keeps a class of peers together**: the two rows
tied at `10` both have rank `1`, so both are `0` – `0, 0, 100`. -/
#eval ((AggQueryIn.percentRank SeqAggFunc.count pct noP ![0] ord
  base).evaluatePlain D4).map (fun u => (u 0, u 1))

/-! **`cume_dist` counts the peers in**: both tied rows are `2/3` –
`66, 66, 100`. -/
#eval ((AggQueryIn.cumeDist SeqAggFunc.count pct noP ![0] ord
  base).evaluatePlain D4).map (fun u => (u 0, u 1))

/-! **The two families the expression reads**, encoded as
`10 * before + whole`: `3, 13, 23`, so the frame of the rows strictly
before gives `0, 1, 2` and the whole partition gives `3` on every row.
That pair is what `percent_rank` divides, and reading the two
separately would allow `2` beside `1`. -/
#eval ((AggQueryIn.WinExpr noP ![0] ord
    ![ValueFrame.rangeBefore ord, ValueFrame.whole]
    ![TermIn.const 1, TermIn.const 1] ![SeqAggFunc.count, SeqAggFunc.count]
    (fun v => v 0 * 10 + v 1) base).evaluatePlain D3).map
  (fun u => (u 0, u 1))

/-! **`rank` against `dense_rank` with peers**: on `10, 10, 30` the ranks
are `1, 1, 3` – the two tied rows share rank `1` and the third counts the
two rows before it – while the dense ranks are `1, 1, 2`, counting the
one distinct order value before `30`. That is the whole difference
between the two, and it is why `drank` counts values and `rank` counts
rows. -/
#eval ((AggQueryIn.rank SeqAggFunc.count noP ![0] ord base).evaluatePlain
  D4).map (fun u => (u 0, u 1))

#eval ((AggQueryIn.denseRank SeqAggFunc.count noP ![0] ord base).evaluatePlain
  D4).map (fun u => (u 0, u 1))

/-! And on three distinct values the two agree, at `1, 2, 3`. -/
#eval ((AggQueryIn.rank SeqAggFunc.count noP ![0] ord base).evaluatePlain
  D3).map (fun u => (u 0, u 1))

#eval ((AggQueryIn.denseRank SeqAggFunc.count noP ![0] ord base).evaluatePlain
  D3).map (fun u => (u 0, u 1))

end DistributionExample
