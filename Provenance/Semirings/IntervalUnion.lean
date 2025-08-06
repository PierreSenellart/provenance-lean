import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Nontrivial.Defs

inductive EndKind | open | closed

structure Endpoint (α: Type) where
  val  : α
  kind : EndKind

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

def le [LinearOrder α] (I J : Interval α) : Prop :=
  I.hi.val ≤ J.lo.val
end Interval

structure IntervalUnion (α: Type) [LinearOrder α] where
  intervals         : List (Interval α)
  pairwise_disjoint : intervals.Pairwise (fun I J => I ≠ J → I.disjoint J)
  sorted            : intervals.Sorted Interval.le

namespace IntervalUnion
def toSet [LinearOrder α] (U : IntervalUnion α) : Set α := ⋃ I ∈ U.intervals, (I.toSet)
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
