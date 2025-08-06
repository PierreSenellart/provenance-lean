import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Nontrivial.Defs

inductive EndKind | open | closed
deriving DecidableEq

structure Endpoint (α: Type) where
  val  : α
  kind : EndKind

namespace Endpoint
instance [DecidableEq α] : DecidableEq (Endpoint α) := by
  intro a b
  cases a with
  | _ aval akind =>
    cases b with
    | _ bval bkind =>
      by_cases h₁: aval=bval
      . by_cases h₂: akind=bkind
        . exact isTrue (by simp[h₁,h₂])
        . exact isFalse (by intro h; cases h; exact h₂ rfl)
      . exact isFalse (by intro h; cases h; exact h₁ rfl)

def minLo [LinearOrder α] (a b : Endpoint α) : Endpoint α :=
  if a.val < b.val then a else
  if b.val < a.val then b else
  match a.kind, b.kind with
  | .closed, .open => a
  | .open, .closed => b
  | _, _           => a -- tie, equal kinds; either is fine

def maxHi [LinearOrder α] (a b : Endpoint α) : Endpoint α :=
  if a.val > b.val then a else
  if b.val > a.val then b else
  match a.kind, b.kind with
  | .closed, .open => a
  | .open, .closed => b
  | _, _           => a
end Endpoint

structure Interval (α: Type) [LinearOrder α] where
  lo : Endpoint α
  hi : Endpoint α
  wf :
    lo.val < hi.val ∨
    (lo.val = hi.val ∧ lo.kind = .closed ∧ hi.kind = .closed)

def below [LinearOrder α] (x: α) (hi : Endpoint α) : Prop :=
  match hi.kind with
  | .closed => x ≤ hi.val
  | .open   => x < hi.val

def above [LinearOrder α] (x: α) (lo : Endpoint α) : Prop :=
  match lo.kind with
  | .closed => lo.val ≤ x
  | .open   => lo.val < x

namespace Interval
def toSet [LinearOrder α] (I: Interval α) : Set α := {x | above x I.lo ∧ below x I.hi}

@[simp] lemma mem {α: Type} [LinearOrder α] (x : α) (I: Interval α) :
  x ∈ I.toSet ↔ above x I.lo ∧ below x I.hi := Iff.rfl

def disjoint [LinearOrder α] (I J : Interval α) : Prop :=
  Disjoint I.toSet J.toSet

def leAsLower [LinearOrder α] (a b : Endpoint α) : Prop :=
  a.val < b.val ∨ (a.val = b.val ∧ a.kind = .closed ∧ b.kind = .open)

/-- Before, may overlap in one point --/
def le [LinearOrder α] (I J : Interval α) : Prop :=
  I.hi.val ≤ J.lo.val

/-- Strictly before, no common point --/
def before [LinearOrder α] (I J : Interval α) : Prop :=
  I.hi.val < J.lo.val ∨
  (I.hi.val = J.lo.val ∧ (I.hi.kind = .open ∨ J.lo.kind = .open))

instance [LinearOrder α] [DecidableEq α] [DecidableLE α] {I J: Interval α} : Decidable (I.before J) := by
  by_cases hlt: I.hi.val < J.lo.val
  . exact isTrue (by left; exact hlt)
  . by_cases heq: I.hi.val=J.lo.val
    . by_cases hIo: I.hi.kind = .open
      . exact isTrue (by right; constructor; assumption; left; assumption)
      . by_cases hJo: J.lo.kind = .open
        . exact isTrue (by right; constructor; assumption; right; assumption)
        . exact isFalse (by simp[before,heq,hIo,hJo])
    . exact isFalse (by simp[before,hlt,heq])

@[simp]
lemma le_of_before [LinearOrder α] {I J : Interval α} (h: I.before J) : I.le J := by
  cases h with
  | inl h' => exact le_of_lt h'
  | inr h' => exact le_of_eq h'.1
end Interval

structure IntervalUnion (α: Type) [LinearOrder α] where
  intervals         : List (Interval α)
  pairwise_disjoint : intervals.Pairwise (fun I J => I ≠ J → I.disjoint J)
  sorted            : intervals.Sorted Interval.le

namespace IntervalUnion
def toSet [LinearOrder α] (U : IntervalUnion α) : Set α := ⋃ I ∈ U.intervals, I.toSet

@[simp]
lemma mem [LinearOrder α] (x: α) (U: IntervalUnion α) :
    x ∈ U.toSet ↔ ∃ I ∈ U.intervals, x ∈ I.toSet := by
      unfold toSet
      apply Iff.intro
      . intro hx
        have := Set.mem_iUnion.mp hx
        rcases this with ⟨I, hI, h⟩
        simp at h
        use I
        constructor
        . exact h.1.1
        . rw[← h.1.2] at h
          exact h.2
      . intro hx
        rcases hx with ⟨I, h⟩
        exact Set.mem_biUnion h.1 h.2

def merge2 [LinearOrder α] (I J : Interval α) : Interval α :=
  let lo := Endpoint.minLo I.lo J.lo
  let hi := Endpoint.maxHi I.hi J.hi
  {
    lo := lo
    hi := hi
    wf := by
      sorry
  }

def insertMerge [LinearOrder α] (I : Interval α) : List (Interval α) → List (Interval α)
| []    => [I]
| J::tl =>
  if I.before J then
    I::J::tl
  else if J.before I then
    J::(insertMerge I tl)
  else
    insertMerge (merge2 I J) tl

def mergeAll (U V : IntervalUnion α) : List (Interval α) :=
  V.intervals.foldl (fun acc I => insertMerge I acc) U.intervals
end IntervalUnion

variable {α: Type} [LinearOrder α] [BoundedOrder α] [Nontrivial α]

instance : Zero (IntervalUnion α) := ⟨[], by simp, by simp⟩
instance : One  (IntervalUnion α) := ⟨[⟨⟨⊥,.open⟩,⟨⊤,.open⟩,by simp⟩], by simp, by simp⟩

instance : Add  (IntervalUnion α) where
  add U V := {
    intervals := sorry,
    pairwise_disjoint := sorry,
    sorted := sorry
  }
