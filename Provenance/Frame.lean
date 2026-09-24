/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Occurrence

/-!
# Window frames determined by values

A window function computes, for each row, an aggregate over a *frame*: some
of the rows sharing its partition. Which rows, in general, depends on
positions in a sorted partition – the previous row, the previous three – and
a position is not something a row carries. In a world where some rows are
absent the previous row is the previous *present* row, so a frame read
positionally is not the restriction of the frame read on the whole relation,
and the value a row gets cannot be computed world by world.

A frame is *determined by values* when membership depends only on the order
values of the two rows and on whether they are the same occurrence: a
relation `ρ` between order values decides the other rows, and a predicate `s`
on its own order value decides whether the row is in its own frame. SQL's
`RANGE` and `GROUPS` frames without offsets, the frames with `EXCLUDE`, and
the frame of the rows strictly before the current one are all of this form;
`ROWS` frames other than the whole partition are not.

For such a frame the restriction property holds (`frame_inter`): the frame of
an occurrence among the present rows is its frame in the whole relation,
intersected with them. That is what lets a window be read in every world, and
it is the only property of frames the annotated semantics uses.
-/

variable {T K : Type} {n m p : ℕ}

/-- The values a tuple has at a list of columns: its partition key, or its
order value. -/
def Tuple.key (is : Tuple (Fin n) p) (u : Tuple T n) : Tuple T p :=
  fun k => u (is k)

/-- A frame determined by values: `ρ` decides which *other* occurrences of
the partition belong, from the two order values, and `s` decides whether the
occurrence belongs to its own frame.

Writing the two separately is what distinguishes `EXCLUDE CURRENT ROW` from
its peers: the current row and a peer have the same order value, so no
relation on order values alone could drop one and keep the other. -/
structure ValueFrame (T : Type) (p : ℕ) where
  /-- Whether an occurrence with order value `o'` is in the frame of one
  with order value `o`. -/
  ρ : Tuple T p → Tuple T p → Bool
  /-- Whether an occurrence with order value `o` is in its own frame. -/
  s : Tuple T p → Bool

namespace ValueFrame

variable [DecidableEq T]

/-- The frame *contains its current row exactly when it contains its peers*.
Under this condition the frame of an occurrence depends only on its tuple, so
a window over it does not need the occurrences told apart; `EXCLUDE CURRENT
ROW` and `EXCLUDE TIES` are the frames that fail it. -/
def ContainsSelf (w : ValueFrame T p) : Prop := ∀ o, w.s o = w.ρ o o

/-- Whether occurrence `j` is in the frame of occurrence `i`: same partition,
and then `s` on itself or `ρ` on the order values. -/
def mem (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam (AnnotatedTuple T K n)) (i j : Fin r.size) : Bool :=
  decide (Tuple.key P (r.row j).fst = Tuple.key P (r.row i).fst)
    && (if j = i then w.s (Tuple.key O (r.row i).fst)
        else w.ρ (Tuple.key O (r.row j).fst) (Tuple.key O (r.row i).fst))

/-- The frame of an occurrence, among a set of present occurrences. -/
def frameIn (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam (AnnotatedTuple T K n)) (W : Finset (Fin r.size)) (i : Fin r.size) :
    Finset (Fin r.size) :=
  W.filter (fun j => mem P O w r i j)

/-- The frame of an occurrence in the whole relation. -/
def frame (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) : Finset (Fin r.size) :=
  frameIn P O w r Finset.univ i

/-- Where the frame contains its current row exactly when it contains its
peers, membership stops mentioning the occurrence at all: the `if` collapses,
because an occurrence and itself have the same order value. -/
theorem mem_of_containsSelf {P : Tuple (Fin n) m} {O : Tuple (Fin n) p}
    {w : ValueFrame T p} (h : w.ContainsSelf) (r : OccFam (AnnotatedTuple T K n))
    (i j : Fin r.size) :
    mem P O w r i j
      = (decide (Tuple.key P (r.row j).fst = Tuple.key P (r.row i).fst)
          && w.ρ (Tuple.key O (r.row j).fst) (Tuple.key O (r.row i).fst)) := by
  unfold mem
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left rfl, h]
  · rw [ite_eq_right hji]

/-- **Such a frame depends only on the tuple.** Two occurrences carrying the
same tuple have the same frame, so a window over such a frame gives equal
rows equal values and needs no occurrences told apart.

The frames that fail `ContainsSelf` are exactly `EXCLUDE CURRENT ROW` and
`EXCLUDE TIES`, and they are exactly the ones that do need them: each of two
equal rows is then in the other's frame and not in its own, so the two get
different aggregates from the same relation. -/
theorem frame_eq_of_key_eq {P : Tuple (Fin n) m} {O : Tuple (Fin n) p}
    {w : ValueFrame T p} (h : w.ContainsSelf) (r : OccFam (AnnotatedTuple T K n))
    {i i' : Fin r.size} (hP : Tuple.key P (r.row i).fst
        = Tuple.key P (r.row i').fst)
    (hO : Tuple.key O (r.row i).fst = Tuple.key O (r.row i').fst) :
    frame P O w r i = frame P O w r i' := by
  unfold frame frameIn
  ext j
  simp only [Finset.mem_filter, mem_of_containsSelf h, hP, hO]

/-- **The restriction property.** The frame of an occurrence among the
present rows is its frame in the whole relation, intersected with them.

This is the only property of frames the annotated semantics uses, and it is
what a positional frame lacks: whether an occurrence belongs to another's
frame depends on the two order values and on whether they are the same
occurrence, on nothing else that the absent rows could change. -/
theorem frame_inter (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (r : OccFam (AnnotatedTuple T K n)) (W : Finset (Fin r.size))
    (i : Fin r.size) :
    frameIn P O w r W i = frame P O w r i ∩ W := by
  unfold frameIn frame
  ext j
  constructor
  · intro hj
    obtain ⟨hjW, hmem⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmem⟩, hjW⟩
  · intro hj
    obtain ⟨hall, hjW⟩ := Finset.mem_inter.mp hj
    exact Finset.mem_filter.mpr ⟨hjW, (Finset.mem_filter.mp hall).2⟩

end ValueFrame
