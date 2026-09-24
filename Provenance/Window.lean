/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Frame
import Provenance.AggValue

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

end ValueFrame
