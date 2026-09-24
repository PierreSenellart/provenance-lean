/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Frame
import Provenance.AggQuery

/-!
# The window operator's token

A window gives every row of its input a further column: the aggregate over
that row's frame. It removes no row, merges none, and changes no annotation –
each row keeps the one it came with, and no group-existence factor arises,
because a window creates no group.

What the row gains is an aggregate *token*, built from its frame exactly as a
grouping builds one from its group. Which convention the token is read in is
decided per row, by whether the row is in its own frame: a row that is reads
its aggregate as a group's, never over nothing, while a row that is not may
have an empty frame in a world where it is itself present, and its aggregate
then ranges over no occurrence at all.

That is the second user of the scalar convention, and it arrives for the same
reason as the first: a row whose existence does not guarantee its aggregate
anything to range over.
-/

variable {T K : Type} {n m p : ℕ} [ValueType T] [HasAltLinearOrder K]

namespace ValueFrame

/-- The token a window gives an occurrence: the aggregate over its frame,
read in the convention that occurrence's frame warrants. -/
def token (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) : AggValue T K :=
  if w.s (Tuple.key O (r.row i).fst) then
    AggValue.ofGroup f t (frameSeq P O w r i)
  else
    AggValue.ofScalarGroup f t (frameSeq P O w r i)

/-- A row inside its own frame reads its aggregate as a group's. -/
@[simp] theorem token_scalar_of_mem (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size)
    (h : w.s (Tuple.key O (r.row i).fst) = true) :
    (token P O w t f r i).scalar = false := by
  simp [token, h]

/-- A row outside its own frame reads it in the scalar convention: the frame
may be empty in a world where the row is present. -/
@[simp] theorem token_scalar_of_not_mem (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (w : ValueFrame T p) (t : Term T n)
    (f : SeqAggFunc T) (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size)
    (h : w.s (Tuple.key O (r.row i).fst) = false) :
    (token P O w t f r i).scalar = true := by
  simp [token, h]

/-- Whichever convention it is read in, the token aggregates the frame. -/
theorem token_occs (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size) :
    (token P O w t f r i).occs
      = (frameSeq P O w r i).map (fun q => (t.eval q.fst, q.snd)) := by
  unfold token AggValue.ofScalarGroup AggValue.ofGroup
  split <;> rfl

/-! ## The operator

A window maps each occurrence of its input to one output occurrence: the same
row, one column longer, with the same annotation and nothing pending. Which
occurrence it is matters, because two occurrences carrying the same row may
have different frames – that is what the family reading is for. -/

/-- The window operator on a family: every occurrence keeps its row and its
annotation, and gains the token of its frame. -/
def window (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) : OccFam (GenRow T K (n + 1)) :=
  ⟨r.size, fun i =>
    (Fin.snoc (fun k => (Sum.inl ((r.row i).fst k) : GenValue T K))
        (Sum.inr (token P O w t f r i)),
     ⟨(r.row i).snd, 0⟩)⟩

omit [HasAltLinearOrder K] in
/-- Membership in a frame is carried along a re-indexing: it reads the rows
and whether two occurrences are the same, both of which a bijection
preserves. -/
theorem mem_congr (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) {r r' : OccFam (AnnotatedTuple T K n)}
    (e : Fin r.size ≃ Fin r'.size) (he : ∀ i, r'.row (e i) = r.row i)
    (i j : Fin r.size) :
    mem P O w r' (e i) (e j) = mem P O w r i j := by
  unfold mem
  rw [he i, he j]
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right hji, ite_eq_right (fun hc => hji (e.injective hc))]

omit [HasAltLinearOrder K] in
/-- A re-indexing carries a frame to the image of the frame. -/
theorem frame_congr (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) {r r' : OccFam (AnnotatedTuple T K n)}
    (e : Fin r.size ≃ Fin r'.size) (he : ∀ i, r'.row (e i) = r.row i)
    (i : Fin r.size) :
    frame P O w r' (e i) = (frame P O w r i).map e.toEmbedding := by
  ext j'
  obtain ⟨j, rfl⟩ := e.surjective j'
  simp only [frame, frameIn, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map_equiv, Equiv.symm_apply_apply]
  rw [mem_congr P O w e he i j]

/-- A re-indexing carries a frame's occurrence sequence unchanged: the frame
maps across, and the sequence is built by sorting the rows, which the
bijection does not move. -/
theorem frameSeq_congr (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) {r r' : OccFam (AnnotatedTuple T K n)}
    (e : Fin r.size ≃ Fin r'.size) (he : ∀ i, r'.row (e i) = r.row i)
    (i : Fin r.size) :
    frameSeq P O w r' (e i) = frameSeq P O w r i := by
  let _ : LinearOrder K := HasAltLinearOrder.altOrder
  let _ : LinearOrder (AnnotatedTuple T K n) :=
    inferInstanceAs (LinearOrder (Tuple T n ×ₗ K))
  unfold frameSeq
  rw [frame_congr P O w e he i, Finset.map_val, Multiset.map_map]
  exact congrArg (fun s => (Multiset.foldr sortedInsert ⟨[], by simp⟩ s).val)
    (Multiset.map_congr rfl (fun j _ => he j))

/-- **A window is well defined on occurrences, not on indices.** Congruent
inputs give congruent outputs, by the same bijection: an occurrence's row,
its annotation and its frame are all carried across, so nothing the operator
produces depends on which indexing was chosen. -/
theorem window_congr (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    {r r' : OccFam (AnnotatedTuple T K n)} (h : OccFam.Congr r r') :
    OccFam.Congr (window P O w t f r) (window P O w t f r') := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun i => ?_⟩
  show ((window P O w t f r').row (e i) : GenRow T K (n + 1))
    = (window P O w t f r).row i
  unfold window token
  simp only [he i, frameSeq_congr P O w e he i]

/-! ## The window on a relation

Applying the operator to a relation means reading it as a family, and any two
readings give the same answer, so the relation is what the answer is about. -/

/-- The window on a relation: read it as a family, apply the operator, forget
the index. -/
noncomputable def windowRel (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : AnnotatedRelation T K n) : Multiset (GenRow T K (n + 1)) :=
  (window P O w t f (OccFam.ofMultiset r)).toMultiset

/-- **The window's answer is about the relation, not the indexing.** Two
families with the same rows give the same rows out – the operator respects
re-indexing, and two indexings of one relation are the same family.

Two occurrences carrying equal rows may still receive different tokens, which
is what `EXCLUDE CURRENT ROW` requires; what this says is that *which* of
them receives which is not observable, because exchanging them exchanges
their answers. -/
theorem window_toMultiset_congr (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    {r r' : OccFam (AnnotatedTuple T K n)}
    (h : r.toMultiset = r'.toMultiset) :
    (window P O w t f r).toMultiset = (window P O w t f r').toMultiset :=
  OccFam.toMultiset_congr
    (window_congr P O w t f (OccFam.Congr_of_toMultiset_eq h))

/-- Reading a relation as a family and forgetting the index again is the
window of that relation, for any reading. -/
theorem windowRel_eq (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) (t : Term T n) (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T K n)) :
    windowRel P O w t f r.toMultiset = (window P O w t f r).toMultiset :=
  window_toMultiset_congr P O w t f (by simp)

end ValueFrame
