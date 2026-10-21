/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Mathlib.Data.List.Sort

/-!
# Insertion sort with exposed bodies

Mathlib does not expose the bodies of `List.orderedInsert` and
`List.insertionSort` to other modules, so the kernel cannot reduce a
computation that sorts through them, and a `decide`-checked equation about a
computed relation gets stuck there. The two functions below are the same
ones, written out again with their bodies exposed. The evaluators sort
through these; each comes with a `simp` lemma rewriting it to Mathlib's, so
that proofs reason with Mathlib's lemmas.
-/

@[expose] public section

namespace List

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- `List.orderedInsert`, with an exposed body. -/
def orderedIns (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: orderedIns a l

/-- `List.insertionSort`, with an exposed body. -/
def insSort : List α → List α := foldr (orderedIns r) []

@[simp] theorem orderedIns_eq (a : α) (l : List α) :
    l.orderedIns r a = l.orderedInsert r a := by
  induction l with
  | nil => simp [orderedIns]
  | cons b l ih => simp [orderedIns, ih]

@[simp] private theorem insSort_eq (l : List α) : l.insSort r = l.insertionSort r := by
  induction l with
  | nil => simp [insSort, insertionSort_nil]
  | cons b l ih => simp only [insSort, foldr_cons, insertionSort_cons] at ih ⊢; rw [ih, orderedIns_eq]

end List
