/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Derived
import Provenance.QueryAdequacy
import Provenance.Semirings.Nat

/-!
# Second-level aggregation, through the alternatives

`sum(count(*))` over a `GROUP BY` aggregates an aggregate column. No
operator of the syntax aggregates a term that *reads* one – that is the
nested aggregate value of `Provenance.Nested`, whose outer aggregate has
to be symmetric because the order `≼` is an order on plain tuples and an
occurrence of a nested value carries a tuple with an aggregate column.

But the query is expressible all the same, and this file writes it. The
route is the one `AggQueryIn.Alt` documents: read the aggregate column as
a **key**, replacing each occurrence by its alternatives, one per value
the column takes and each carrying `[a ≐ v]`. The column becomes regular,
and every operator applies to a regular column – a grouping included. So
the outer aggregate is an *ordinary* one over an ordinary relation, and
nothing nested is involved.

The two readings are not the same object. The alternatives explode a row
into one per value its column takes, each annotated so that it is present
exactly in the worlds where the column has that value; the nested reading
keeps one row and reads it world by world. This file checks the first,
which the library has, on a relation where the two groups have different
counts.

The checks are `#eval`s, as `Provenance.Example`'s are: the evaluator
sorts, and the kernel does not reduce through that.
-/

namespace NestedExample

/-! Three rows in two groups: `1` twice and `2` once. -/
abbrev R : Relation ℕ 1 := (([![1], ![1], ![2]] : List (Tuple ℕ 1)) : Multiset _)

/-- The plain database. -/
abbrev D : Database ℕ := [("R", ⟨1, R⟩)]

/-- The annotated database, every row annotated `1`. -/
abbrev dN : AnnotatedDatabase ℕ ℕ :=
  [("R", ⟨1, (R.map (fun u => ((u, 1) : AnnotatedTuple ℕ ℕ 1)))⟩)]

/-! ## The inner grouping: one row per group, carrying its count -/

/-- `SELECT a, count(*) FROM R GROUP BY a`. -/
abbrev inner : AggQuery ℕ (1 + 1)
    (Fin.append (fun _ : Fin 1 => ColKind.reg) (fun _ : Fin 1 => ColKind.agg)) :=
  AggQueryIn.Gamma ![0] ![TermIn.const 1] ![SeqAggFunc.count]
    (AggQueryIn.Rel 1 "R")

/-- The count column is the second one, and it is an aggregate column. -/
theorem inner_kind :
    (Fin.append (fun _ : Fin 1 => ColKind.reg) (fun _ : Fin 1 => ColKind.agg)
      : Fin (1 + 1) → ColKind) 1 = ColKind.agg := by
  show (Fin.append (fun _ : Fin 1 => ColKind.reg) (fun _ : Fin 1 => ColKind.agg)
    : Fin (1 + 1) → ColKind) (Fin.natAdd 1 0) = _
  rw [Fin.append_right]

/-- Reading it as a key makes every column regular. -/
theorem alt_kind :
    Function.update
        (Fin.append (fun _ : Fin 1 => ColKind.reg) (fun _ : Fin 1 => ColKind.agg)
          : Fin (1 + 1) → ColKind) 1 ColKind.reg
      = ColKind.allReg (1 + 1) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Function.update_of_ne (by
      show Fin.castAdd 1 i ≠ (1 : Fin (1 + 1))
      intro hc
      exact absurd (congrArg Fin.val hc) (by simp [Fin.castAdd, Fin.castLE])),
      Fin.append_left]
    rfl
  · rw [show Fin.natAdd 1 j = (1 : Fin (1 + 1)) from
      Fin.ext (by simp [Fin.natAdd]), Function.update_self]
    rfl

/-! ## The outer aggregation over the alternatives -/

/-- `SELECT sum(c) FROM (SELECT a, count(*) AS c FROM R GROUP BY a) t`,
with the inner count read as a key so that the outer `sum` aggregates a
regular column. -/
abbrev outer : AggQuery ℕ 1 (fun _ => ColKind.agg) :=
  AggQueryIn.GammaScalar ![TermIn.index 1] ![SeqAggFunc.sum]
    ((AggQueryIn.Alt 1 inner_kind inner).castKind alt_kind)

/-! ## What the two sides compute

**The inner grouping, plainly**: one row per group with its count, `(1,2)`
and `(2,1)`. -/
#eval (inner.evaluatePlain D).map (fun u => (u 0, u 1))

/-! **The outer aggregation, plainly**: `2 + 1 = 3`, which is SQL's
`sum(count(*))`. Over a plain relation an aggregate value is a value and
`Alt` is the identity, so the alternatives cost nothing here. -/
#eval (outer.evaluatePlain D).map (fun u => u 0)

/-! **The alternatives, annotated**: one row per `(group, value)` pair the
count can take, each carrying the group's annotation times `[c ≐ v]`. With
every input row annotated `1` over `ℕ`, the group of `1`'s has a count of
`2` and the group of `2` a count of `1`. -/
#eval ((AggQueryIn.Alt 1 inner_kind inner).evaluateAnnotated dN).map
  (fun p => ((p.fst 0, p.fst 1), p.snd))

/-! **And the outer aggregation's token**: its occurrences are the three
alternatives, each carrying the alternative's annotation. Printed as
`(value, annotation)`:

the two possible ones contribute `2` and `1`, and the impossible one is
annotated `0`. The sum in a world is `2 + 1 = 3`, SQL's answer, and the
*deterministic* reading of the token is `1 + 2 + 1 = 4`, which is no
world's. That is what `def:zeq` means by equality after removal "of the
occurrences annotated `𝟘` inside their aggregate values", and it is why
`AggQueryIn.evaluateAnnotated_toPlain` excludes `Alt`: an aggregate
column read as a key gives one row per value the column takes in *some*
world, so the data part of the annotated evaluation is not the data part
of any one world. -/
#eval (outer.evaluate dN).map (fun r =>
  match r.fst 0 with
  | Sum.inr (AggTok.tok a) => a.occs
  | _ => [])

end NestedExample
