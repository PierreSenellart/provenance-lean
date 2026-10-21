/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.QueryAdequacy
public import Provenance.Semirings.Nat
public import Provenance.AggQuery
import Mathlib.Tactic.Bound.Init
import all Provenance.AggQuery

/-!
# Second-level aggregation, both ways

`sum(count(*))` over a `GROUP BY` aggregates an aggregate column, and the
syntax reads it in two ways. This file writes the query both ways, on a
relation whose two groups have different counts.

**Through the alternatives** (`AggQueryIn.Explode`): read the aggregate
column as a **key**, replacing each occurrence by its alternatives, one
per value the column takes and each carrying `[a ≐ v]`. The column
becomes regular, and every operator applies to a regular column – a
grouping included – so the outer aggregate is an *ordinary* one over an
ordinary relation and nothing nested is involved.

**Directly** (`AggQueryIn.GammaNest`): aggregate a term that *reads* the
aggregate column. The column this builds is a nested aggregate value
(`Provenance.Nested`), whose occurrences are the inner grouping's rows
and whose outer aggregate is a function of the bag of them – it has to
be, the order `≼` being an order on plain tuples while an occurrence
here carries a tuple with an aggregate column.

The two readings are not the same object. The alternatives explode a row
into one per value its column takes, each annotated so that it is present
exactly in the worlds where the column has that value; the nested reading
keeps one row and reads it world by world. The checks below show where
they part: the alternatives' token collapses to `4`, which is no world's
answer, where the nested token collapses to `3`, which is SQL's.

Each check is a theorem closed by `decide`: the evaluator reads a relation
as a sequence through an insertion sort, which the kernel reduces, so the
computed value is compared against the expected one by the kernel. The
queries built with `AggQueryIn.castKind` need `evaluate_castKind` or
`evaluatePlain_castKind` first – the kernel does not reduce a cast along a
proof.
-/

@[expose] public section

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
  AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![0] ![TermIn.const 1] ![SeqAggFunc.count]
    (AggQueryIn.Rel 1 "R")

/-- The count column is the second one, and it is an aggregate column. -/
theorem inner_kind :
    (Fin.append (fun _ : Fin 1 => ColKind.reg) (fun _ : Fin 1 => ColKind.agg)
      : Fin (1 + 1) → ColKind) 1 = ColKind.agg := by
  show (Fin.append (fun _ : Fin 1 => ColKind.reg) (fun _ : Fin 1 => ColKind.agg)
    : Fin (1 + 1) → ColKind) (Fin.natAdd 1 0) = _
  rw [Fin.append_right]

/-- Reading it as a key makes every column regular. -/
theorem explode_kind :
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
  AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ![TermIn.index 1] ![SeqAggFunc.sum]
    ((AggQueryIn.Explode 1 inner_kind inner).castKind explode_kind)

/-! ## What the two sides compute

**The inner grouping, plainly**: one row per group with its count, `(1,2)`
and `(2,1)`. -/
private theorem inner_plain :
    (inner.evaluatePlain D).map (fun u => (u 0, u 1))
      = (([(1, 2), (2, 1)] : List (ℕ × ℕ)) : Multiset _) := by
  decide

/-! **The outer aggregation, plainly**: `2 + 1 = 3`, which is SQL's
`sum(count(*))`. Over a plain relation an aggregate value is a value and
`Explode` is the identity, so the alternatives cost nothing here. -/
private theorem outer_plain :
    (outer.evaluatePlain D).map (fun u => u 0)
      = (([3] : List ℕ) : Multiset ℕ) := by
  simp only [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castKind]
  decide

/-! **The alternatives, annotated**: one row per `(group, value)` pair the
count can take, each carrying the group's annotation times `[c ≐ v]`. With
every input row annotated `1` over `ℕ`, the group of `1`'s has a count of
`2` and the group of `2` a count of `1`. -/
private theorem explode_annotated :
    ((AggQueryIn.Explode 1 inner_kind inner).evaluateAnnotated dN).map
        (fun p => ((p.fst 0, p.fst 1), p.snd))
      = ((([((1, 1), 0), ((1, 2), 1), ((2, 1), 1)] : List ((ℕ × ℕ) × ℕ)))
          : Multiset _) := by
  decide

/-! **And the outer aggregation's token**: its occurrences are the three
alternatives, each carrying the alternative's annotation. Printed as
`(value, annotation)`:

the two possible ones contribute `2` and `1`, and the impossible one is
annotated `0`. The sum in a world is `2 + 1 = 3`, SQL's answer, and the
*deterministic* reading of the token is `1 + 2 + 1 = 4`, which is no
world's. That is why equality up to `𝟘` removes the occurrences annotated
`𝟘` inside aggregate values as well as the rows annotated `𝟘`
(`GenRow.zeroNorm`), and it is why
`AggQueryIn.evaluateAnnotated_toPlain` excludes `Explode`: an aggregate
column read as a key gives one row per value the column takes in *some*
world, so the data part of the annotated evaluation is not the data part
of any one world. -/
private theorem outer_token_occs :
    (outer.evaluate dN).map (fun r =>
        match r.fst 0 with
        | Sum.inr (AggTok.tok a) => a.occs
        | _ => [])
      = (([[(1, 0), (2, 1), (1, 1)]] : List (List (ℕ × ℕ))) : Multiset _) := by
  simp only [AggQueryIn.evaluate, AggQueryIn.evaluate_castKind]
  decide

/-! ## The direct nested reading

`AggQueryIn.GammaNest` aggregates a term that *reads* the aggregate
column, so it keeps one row per group of its own and the column it builds
is a nested token: its occurrences are the inner grouping's rows, each
carrying the aggregate value read there. Here there is one group – no key
columns – so the token's occurrences are the two rows of `inner`, and its
outer aggregate is `sum` read off the bag of them (`SeqAggFunc.onBag`,
the aggregate being symmetric). -/
abbrev outerNest : AggQuery ℕ (0 + 1)
    (Fin.append (fun k : Fin 0 => k.elim0) (fun _ : Fin 1 => ColKind.agg)) :=
  AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) (fun k : Fin 0 => k.elim0) (fun k =>
      k.elim0)
    (ProjColIn.token 1 inner_kind)
    (SeqAggFunc.sum.onBag SeqAggFunc.sum_symmetric) inner

/-! **Plainly it is SQL's answer**: `2 + 1 = 3`, the same as through the
alternatives, an aggregate value being a value over a plain relation. -/
private theorem outerNest_plain :
    (outerNest.evaluatePlain D).map (fun u => u 0)
      = (([3] : List ℕ) : Multiset ℕ) := by
  decide

/-! **The occurrences of its token, annotated**: the inner grouping's two
rows, each as `(the collapse of the inner value, the row's
annotation)` – the counts `2` and `1`, each annotated `1`. -/
private theorem outerNest_occs :
    (outerNest.evaluate dN).map (fun r =>
        match r.fst 0 with
        | Sum.inr (AggTok.nest a) =>
          a.occs.map (fun o : NestInner ℕ ℕ a.lev × ℕ => (NestInner.collapse a.lev o.1, o.2))
        | _ => 0)
      = (([(([(2, 1), (1, 1)] : List (ℕ × ℕ)) : Multiset _)]
          : List (Multiset (ℕ × ℕ))) : Multiset _) := by
  decide

/-! **Its deterministic reading is `3`** – and not the `4` the
alternatives' token collapses to. Nothing is read twice here: the nested
token keeps one row and reads it world by world, where `Explode` explodes the
row into one per value its column takes. -/
private theorem outerNest_collapse :
    (outerNest.evaluate dN).map (fun r =>
        match r.fst 0 with
        | Sum.inr x => x.collapse
        | Sum.inl v => v)
      = (([3] : List ℕ) : Multiset ℕ) := by
  decide

/-! **And the values it takes over its worlds**: `{1, 2, 3}`. A world
keeps some of the two outer occurrences – at least one, the reading being
grouped – and, of each it keeps, some of that group's rows, at least one
(`World.IsWorld`): so the sums available are `1` (either group alone, one
row of it), `2` (both groups with one row each, or the first group's two
rows) and `3` (everything). `0` is not among them: that would be the
empty world, which a grouped reading does not have. -/
private theorem outerNest_vals :
    (outerNest.evaluate dN).map (fun r =>
        match r.fst 0 with
        | Sum.inr (AggTok.nest a) => a.vals
        | _ => ∅)
      = ((([({3, 2, 1} : Finset ℕ)] : List (Finset ℕ))) : Multiset _) := by
  decide

end NestedExample
