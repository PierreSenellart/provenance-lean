/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggValue

/-!
# Nested aggregate values

When the term of an aggregation or a window reads an aggregate column,
the aggregate value it builds is **nested**: what it aggregates, at
each of its occurrences, is not a value of the domain but another
aggregate value. Its occurrences are those of its own family `U`
*together with* those of the inner values, and its value in a world is
the outer aggregate applied to the inner values read in that world.

An `AggValue` cannot hold this: its reading consults its own occurrence
list alone. `NestedValue` carries, per outer occurrence, the inner
aggregate value the term reads there, and a `World` chooses which outer
occurrences are present *and* which occurrences of each inner value
are.

## Which worlds count

A world meets the family of each grouped inner value **that it reads**,
which is to say each inner value at an outer occurrence the world keeps
– `World.IsWorld`. The condition is on the inner values read and not on
all of them: an outer occurrence absent from the world contributes
nothing to the value there, and asking its inner family to be met would
ask a group to be non-empty while the row carrying it is absent.

This is not the condition a *predicate*'s worlds satisfy, which meet
every grouped family the predicate mentions with no such conditionality
– and the difference is structural rather than an oversight. A
predicate's families all belong to one tuple, which exists or does not,
so demanding all of them demands that the tuple exist. A nested value's
inner families each belong to a *different* outer occurrence, and the
world is choosing which of those occurrences are present, so a blanket
condition would quantify over occurrences the world has already
excluded.

Whether a world should also be *barred* from meeting the family of an
inner value it does not read is open, and the predicate is a parameter
of everything below (`World.IsWorldWith`) so that either answer is a
substitution. No instance realizes such a world – the outer occurrence
is annotated `δ(β)` for the very family at issue, and in an exclusive
semiring the complement factor annihilates them – so the choice is
between imposing the coherence and letting exclusivity dispose of it.
-/

variable {T K : Type} [ValueType T]

/-- **A nested aggregate value**: an outer aggregate over occurrences
that carry aggregate values rather than values. -/
structure NestedValue (T K : Type) where
  /-- The outer aggregate. -/
  agg : SeqAggFunc T
  /-- Per outer occurrence, the inner aggregate value the term reads
  there and the occurrence's own annotation. -/
  occs : List (AggValue T K × K)
  /-- Whether the outer reading is scalar – whether the empty world is
  one of its worlds. -/
  scalar : Bool

namespace NestedValue

/-- The inner aggregate value at an outer occurrence. -/
def innerAt (a : NestedValue T K) (i : Fin a.occs.length) : AggValue T K :=
  (a.occs.get i).1

/-- The annotation of an outer occurrence. -/
def outerAnn (a : NestedValue T K) (i : Fin a.occs.length) : K :=
  (a.occs.get i).2

/-- **A world of a nested value**: which outer occurrences are present,
and which occurrences of each inner value are. -/
structure World (a : NestedValue T K) where
  /-- The outer occurrences present. -/
  outer : Finset (Fin a.occs.length)
  /-- For each outer occurrence, the occurrences of its inner value
  that are present. -/
  inner : (i : Fin a.occs.length) → Finset (Fin (a.innerAt i).occs.length)

/-- **Admissibility, with the coherence condition as a parameter.**
`extra` is the clause `q:nestedcoherent` leaves open – whether a world
is barred from meeting the family of an inner value it does not read.
The document's reading is `IsWorld`, which takes `extra` to be
vacuous. -/
def World.IsWorldWith {a : NestedValue T K}
    (extra : a.World → Prop) (W : a.World) : Prop :=
  (a.scalar = true ∨ W.outer.Nonempty)
    ∧ (∀ i ∈ W.outer, (a.innerAt i).scalar = false → (W.inner i).Nonempty)
    ∧ extra W

/-- **The worlds the document commits to**: the outer family met unless
the reading is scalar, and the family of each grouped inner value *that
the world reads* met. -/
def World.IsWorld {a : NestedValue T K} (W : a.World) : Prop :=
  World.IsWorldWith (fun _ => True) W

/-- The reading that bars a world from meeting the family of an inner
value it does not read – the other answer to `q:nestedcoherent`. -/
def World.IsWorldCoherent {a : NestedValue T K} (W : a.World) : Prop :=
  World.IsWorldWith (fun W => ∀ i ∉ W.outer, W.inner i = ∅) W

/-- **The value of a nested aggregate in a world**: the outer aggregate
of the inner values read there, in the order of the outer
occurrences. -/
def valOn {a : NestedValue T K} (W : a.World) : T :=
  a.agg (((List.finRange a.occs.length).filter (fun i => i ∈ W.outer)).map
    (fun i => (a.innerAt i).valOn (W.inner i)))

/-- The world in which every occurrence, outer and inner, is present. -/
def World.full (a : NestedValue T K) : a.World :=
  ⟨Finset.univ, fun _ => Finset.univ⟩

/-- **The deterministic reading**: the outer aggregate of the inner
collapses. -/
def collapse (a : NestedValue T K) : T :=
  a.agg (a.occs.map (fun o => o.1.collapse))

omit [ValueType T] in
/-- **Everything present reads as the collapse.** -/
theorem valOn_full (a : NestedValue T K) :
    valOn (World.full a) = a.collapse := by
  unfold valOn collapse World.full
  refine congrArg a.agg ?_
  rw [List.filter_eq_self.mpr (fun i _ => by simp)]
  refine List.ext_get (by simp) (fun i h₁ h₂ => ?_)
  simp only [List.get_eq_getElem, List.getElem_map, NestedValue.innerAt,
    List.get_eq_getElem]
  rw [show ((List.finRange a.occs.length)[i]'(by simpa using h₁) : Fin a.occs.length)
      = ⟨i, by simpa using h₂⟩ from by simp]
  exact (AggValue.collapse_eq_valOn_univ _).symm

omit [ValueType T] in
/-- A world of the document's reading is one of the coherent reading's
as soon as it keeps no inner occurrence it does not read. -/
theorem World.isWorld_of_isWorldCoherent {a : NestedValue T K}
    {W : a.World} (h : W.IsWorldCoherent) : W.IsWorld :=
  ⟨h.1, h.2.1, trivial⟩

end NestedValue
