/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Derived
public import Provenance.QueryAdequacy

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

The checks are theorems closed by `decide`: the clause's order is read by
an insertion sort (`OrderSpec.sortSeq`), which the kernel reduces, so each
computed relation is compared against its expected value by the kernel
rather than printed. The two ranks go through `AggQueryIn.castKind`, whose
cast the kernel cannot reduce, so their checks rewrite with
`evaluatePlain_rank` and `evaluatePlain_denseRank` first – which is the
same equation, stated on the cast-free right-hand side those lemmas
give.
-/

@[expose] public section

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
theorem percentRank_distinct :
    ((AggQueryIn.percentRank SeqAggFunc.count pct noP ![0] ord
        base).evaluatePlain D3).map (fun u => (u 0, u 1))
      = (([(10, 0), (20, 50), (30, 100)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **`cume_dist` on the same**: `c/N` with `c` over the rows up to the
current one and its peers, so `1/3`, `2/3`, `1` – `33, 66, 100`. -/
theorem cumeDist_distinct :
    ((AggQueryIn.cumeDist SeqAggFunc.count pct noP ![0] ord
        base).evaluatePlain D3).map (fun u => (u 0, u 1))
      = (([(10, 33), (20, 66), (30, 100)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **`ntile(2)` on three rows**: buckets `1, 1, 2`. -/
theorem ntile_distinct :
    ((AggQueryIn.ntile SeqAggFunc.count two noP ![0] ord
        base).evaluatePlain D3).map (fun u => (u 0, u 1))
      = (([(10, 1), (20, 1), (30, 2)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **`percent_rank` on one row is `0`**, by its own clause for `N = 1`
and not by a division. This is the case a reading of the two frames as
separate aggregates would have to invent a value for. -/
theorem percentRank_one :
    ((AggQueryIn.percentRank SeqAggFunc.count pct noP ![0] ord
        base).evaluatePlain D1).map (fun u => (u 0, u 1))
      = (([(7, 0)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **`percent_rank` keeps a class of peers together**: the two rows
tied at `10` both have rank `1`, so both are `0` – `0, 0, 100`. -/
theorem percentRank_peers :
    ((AggQueryIn.percentRank SeqAggFunc.count pct noP ![0] ord
        base).evaluatePlain D4).map (fun u => (u 0, u 1))
      = (([(10, 0), (10, 0), (30, 100)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **`cume_dist` counts the peers in**: both tied rows are `2/3` –
`66, 66, 100`. -/
theorem cumeDist_peers :
    ((AggQueryIn.cumeDist SeqAggFunc.count pct noP ![0] ord
        base).evaluatePlain D4).map (fun u => (u 0, u 1))
      = (([(10, 66), (10, 66), (30, 100)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **The two families the expression reads**, encoded as
`10 * before + whole`: `3, 13, 23`, so the frame of the rows strictly
before gives `0, 1, 2` and the whole partition gives `3` on every row.
That pair is what `percent_rank` divides, and reading the two
separately would allow `2` beside `1`. -/
theorem winExpr_both_frames :
    ((AggQueryIn.WinExpr (hsql := sql_frame%) (lab := 0) (rd := fun _ => false) noP ![0] ord
        ![ValueFrame.rangeBefore ord, ValueFrame.whole]
        ![TermIn.const 1, TermIn.const 1]
        ![SeqAggFunc.count, SeqAggFunc.count]
        (fun v => v 0 * 10 + v 1) base).evaluatePlain D3).map
      (fun u => (u 0, u 1))
      = (([(10, 3), (20, 13), (30, 23)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **`rank` against `dense_rank` with peers**: on `10, 10, 30` the ranks
are `1, 1, 3` – the two tied rows share rank `1` and the third counts the
two rows before it – while the dense ranks are `1, 1, 2`, counting the
one distinct order value before `30`. That is the whole difference
between the two, and it is why `drank` counts values and `rank` counts
rows. -/
theorem rank_peers :
    ((AggQueryIn.rank SeqAggFunc.count noP ![0] ord base
      (winReadsReg_allReg _ _ _)).evaluatePlain
        D4).map (fun u => (u 0, u 1))
      = (([(10, 1), (10, 1), (30, 3)] : List (ℕ × ℕ)) : Multiset _) := by
  rw [AggQueryIn.evaluatePlain_rank]
  decide

theorem denseRank_peers :
    ((AggQueryIn.denseRank SeqAggFunc.count noP ![0] ord
        base
      (winReadsReg_allReg _ _ _)).evaluatePlain D4).map (fun u => (u 0, u 1))
      = (([(10, 1), (10, 1), (30, 2)] : List (ℕ × ℕ)) : Multiset _) := by
  rw [AggQueryIn.evaluatePlain_denseRank]
  decide

/-! And on three distinct values the two agree, at `1, 2, 3`. -/
theorem rank_distinct :
    ((AggQueryIn.rank SeqAggFunc.count noP ![0] ord base
      (winReadsReg_allReg _ _ _)).evaluatePlain
        D3).map (fun u => (u 0, u 1))
      = (([(10, 1), (20, 2), (30, 3)] : List (ℕ × ℕ)) : Multiset _) := by
  rw [AggQueryIn.evaluatePlain_rank]
  decide

theorem denseRank_distinct :
    ((AggQueryIn.denseRank SeqAggFunc.count noP ![0] ord
        base
      (winReadsReg_allReg _ _ _)).evaluatePlain D3).map (fun u => (u 0, u 1))
      = (([(10, 1), (20, 2), (30, 3)] : List (ℕ × ℕ)) : Multiset _) := by
  rw [AggQueryIn.evaluatePlain_denseRank]
  decide

end DistributionExample
