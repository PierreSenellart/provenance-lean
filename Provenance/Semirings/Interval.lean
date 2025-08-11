import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Set.Lattice

@[ext]
structure Endpoint (α: Type) where
  val    : α
  closed : Bool

namespace Endpoint
instance [DecidableEq α] : DecidableEq (Endpoint α) := by
  intro a b
  cases a with
  | _ aval aclosed =>
    cases b with
    | _ bval bclosed =>
      by_cases h₁: aval=bval
      . if h₂: aclosed=bclosed then
          exact isTrue (by simp[h₁,h₂])
        else
          exact isFalse (by intro h; cases h; exact h₂ rfl)
      . exact isFalse (by intro h; cases h; exact h₁ rfl)

def minLo [LinearOrder α] (a b : Endpoint α) : Endpoint α :=
  if a.val < b.val then a else
  if b.val < a.val then b else
  if ¬a.closed ∧ b.closed then b else a

def maxHi [LinearOrder α] (a b : Endpoint α) : Endpoint α :=
  if a.val > b.val then a else
  if b.val > a.val then b else
  if ¬a.closed ∧ b.closed then b else a

def below [LinearOrder α] (x: α) (hi : Endpoint α) : Prop :=
  if(hi.closed) then x ≤ hi.val else x < hi.val

def above [LinearOrder α] (x: α) (lo : Endpoint α) : Prop :=
  if(lo.closed) then lo.val ≤ x else lo.val < x

def le_of_below [LinearOrder α] (x: α) (lo: Endpoint α) :
    below x lo → x ≤ lo.val := by
      simp[below]
      by_cases h : lo.closed <;> simp[h]
      exact le_of_lt

def ge_of_not_below [LinearOrder α] (x: α) (lo: Endpoint α) :
    ¬below x lo → x ≥ lo.val := by
      simp[below]
      by_cases h : lo.closed <;> simp[h]
      exact le_of_lt

def ge_of_above [LinearOrder α] (x: α) (hi: Endpoint α) :
    above x hi → x ≥ hi.val := by
      simp[above]
      by_cases h : hi.closed <;> simp[h]
      exact le_of_lt

def le_of_not_above [LinearOrder α] (x: α) (hi: Endpoint α) :
    ¬above x hi → x ≤ hi.val := by
      simp[above]
      by_cases h : hi.closed <;> simp[h]
      exact le_of_lt

lemma below_of_below_of_lt [LinearOrder α] {hi hi': Endpoint α} (h: hi.val < hi'.val) {x: α} :
  below x hi → below x hi' := by
    unfold below
    by_cases hc: hi.closed <;> simp[hc] <;>
    by_cases hc': hi'.closed <;> simp[hc']
    . intro h'
      exact le_of_lt (lt_of_le_of_lt h' h)
    . intro h'
      exact lt_of_le_of_lt h' h
    . intro h'
      exact le_of_lt (lt_trans h' h)
    . intro h'
      exact lt_trans h' h

lemma above_of_above_of_lt [LinearOrder α] {lo lo': Endpoint α} (h: lo'.val < lo.val) {x: α} :
  above x lo → above x lo' := by
    unfold above
    by_cases hc: lo.closed <;> simp[hc] <;>
    by_cases hc': lo'.closed <;> simp[hc']
    . intro h'
      exact le_of_lt (lt_of_lt_of_le h h')
    . intro h'
      exact lt_of_lt_of_le h h'
    . intro h'
      exact le_of_lt (lt_trans h h')
    . intro h'
      exact lt_trans h h'
end Endpoint

@[ext]
structure Interval (α: Type) [LinearOrder α] where
  lo : Endpoint α
  hi : Endpoint α
  wf :
    lo.val < hi.val ∨
    (lo.val = hi.val ∧ lo.closed ∧ hi.closed)

namespace Interval
@[simp]
lemma le_lo_hi [LinearOrder α] (I: Interval α) : I.lo.val ≤ I.hi.val := by
  cases I.wf with
  | inl hI => exact le_of_lt hI
  | inr hI => exact le_of_eq hI.left

def toSet [LinearOrder α] (I: Interval α) : Set α := {x | Endpoint.above x I.lo ∧ Endpoint.below x I.hi}

@[simp]
lemma mem {α: Type} [LinearOrder α] (x : α) (I: Interval α) :
  x ∈ I.toSet ↔ Endpoint.above x I.lo ∧ Endpoint.below x I.hi := Iff.rfl

def disjoint [LinearOrder α] (I J : Interval α) : Prop :=
  Disjoint I.toSet J.toSet

instance [LinearOrder α] : PartialOrder (Interval α) where
  le I J : Prop := I.lo.val ≤ J.lo.val ∧ I.hi.val ≤ J.hi.val ∧
    (I.lo.val=J.lo.val → J.lo.closed → I.lo.closed) ∧
    (I.hi.val=J.hi.val → I.hi.closed → J.hi.closed)
  le_refl := by simp
  le_antisymm := by
    intro I J hIJ hJI
    have hlo : I.lo.val = J.lo.val := by
      exact le_antisymm hIJ.1 hJI.1
    have hhi : I.hi.val = J.hi.val := by
      exact le_antisymm hIJ.2.1 hJI.2.1
    ext <;> simp_all
    . have h₁ := hIJ.1
      have h₂ := hJI.1
      simp_all
      by_cases h: I.lo.closed
      . rw[h]
        exact Eq.symm (h₂ h)
      . simp at h
        simp[h] at *
        exact h₁
    . have h₁ := hIJ.2
      have h₂ := hJI.2
      simp_all
      by_cases h: I.hi.closed
      . rw[h]
        exact Eq.symm (h₁ h)
      . simp at h
        simp[h] at *
        exact h₂
  le_trans := by
    intro I J K hIJ hJK
    constructor
    . exact le_trans hIJ.1 hJK.1
    . constructor
      . exact le_trans hIJ.2.1 hJK.2.1
      . constructor
        . intro hIKlo hK
          have hIJlo : I.lo.val=J.lo.val := by
            exact eq_of_le_of_ge (hIJ.1) (by rw[← hIKlo] at hJK; exact hJK.1)
          have hJKlo : J.lo.val=K.lo.val := by
            rw[hIJlo] at hIKlo; exact hIKlo
          exact hIJ.2.2.1 hIJlo (hJK.2.2.1 hJKlo hK)
        . intro hIKhi hI
          have hIJhi : I.hi.val=J.hi.val := by
            exact eq_of_le_of_ge (hIJ.2.1) (by rw[← hIKhi] at hJK; exact hJK.2.1)
          have hJKhi : J.hi.val=K.hi.val := by
            rw[hIJhi] at hIKhi; exact hIKhi
          exact hJK.2.2.2 hJKhi (hIJ.2.2.2 hIJhi hI)

/-- Strictly before, no common point, cannot be merged --/
def before [LinearOrder α] (I J : Interval α) : Prop :=
  I.hi.val < J.lo.val ∨
  (I.hi.val = J.lo.val ∧ (I.hi.closed → ¬J.lo.closed))

instance [LinearOrder α] [DecidableEq α] [DecidableLE α] {I J: Interval α} : Decidable (I.before J) := by
  by_cases hlt: I.hi.val < J.lo.val
  . exact isTrue (by left; exact hlt)
  . by_cases heq: I.hi.val=J.lo.val
    . by_cases hIo: ¬I.hi.closed
      . exact isTrue (by right; constructor; assumption; tauto)
      . by_cases hJo: ¬J.lo.closed
        . exact isTrue (by right; constructor; assumption; tauto)
        . exact isFalse (by simp[before,heq,hIo,hJo])
    . exact isFalse (by simp[before,hlt,heq])

@[simp]
lemma le_of_before [LinearOrder α] {I J : Interval α} (h: I.before J) : I ≤ J := by
  simp[(· ≤ ·)]
  cases h with
  | inl h' =>
    have hlo : I.lo.val < J.lo.val := by
      cases I.wf with
      | inl hI => exact lt_trans hI h'
      | inr hI => rw[← hI.1] at h'; exact h'
    have hhi : I.hi.val < J.hi.val := by
      cases J.wf with
      | inl hJ => exact lt_trans h' hJ
      | inr hJ => rw[hJ.1] at h'; exact h'
    simp[le_of_lt hlo,le_of_lt hhi,ne_of_lt hlo,ne_of_lt hhi]
  | inr h' =>
    simp[h'.1]
    constructor
    . cases I.wf with
      | inl hI => rw[h'.1] at hI; exact le_of_lt hI
      | inr hI => rw[h'.1] at hI; exact le_of_eq hI.1
    . constructor
      . intro hlo hJlo
        simp[hJlo] at h'
        have hIwf := I.wf
        simp[h',hlo] at hIwf
      . intro hhi hIhi
        simp[hIhi] at h'
        have hJwf := J.wf
        simp[h',hhi] at hJwf
end Interval
