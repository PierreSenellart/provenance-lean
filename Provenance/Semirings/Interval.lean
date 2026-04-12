import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Set.Lattice

/-!
# Intervals over linear orders

This file defines closed/open intervals over a linear order and the operations
needed to build the interval-union semiring.

## Main definitions

* `Endpoint α` — an endpoint of an interval: a value in `α` together with a
  `closed` flag indicating whether the endpoint is included
* `Interval α` — an interval with possibly open endpoints whose endpoints satisfy
  `lo.val < hi.val`, or `lo.val = hi.val` with both endpoints closed
* `Interval.toSet` — the set of points belonging to an interval
* `Interval.disjoint` — two intervals are disjoint when their point sets are disjoint
* `Interval.before` — `I.before J` means `I` lies strictly to the left of `J`
  (no point is shared and they cannot be merged)
* `Interval.inter` — intersection of two intervals
* `Interval.diff` — difference of two intervals (a list of at most two intervals)

## Main results

* `Interval.toSet_not_empty` — every well-formed interval contains at least one point
* `Interval.ext_toSet` — two intervals with the same point set are equal
  (requires `DenselyOrdered`)
* `Interval.mem_inter` — membership in the intersection is conjunction of memberships
* `Interval.mem_diff` — membership in the difference is membership minus exclusion
* `Interval.disjoint_of_before` — `before` implies `disjoint`
-/

/-- An endpoint of an interval: a value together with a boolean flag indicating
whether the endpoint is included (`closed = true`) or excluded (`closed = false`). -/
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

lemma minLo_or [LinearOrder α] (a b: Endpoint α) :
    minLo a b = a ∨ minLo a b = b := by
      unfold minLo
      split_ifs <;> simp

lemma minLo_commutative [LinearOrder α] {a b: Endpoint α} :
  minLo a b = minLo b a := by
    simp[minLo]
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ <;> try simp
    . have := (lt_self_iff_false a.val).mp (lt_trans h₁ h₂)
      contradiction
    . have := Eq.trans (Eq.symm h₅.1) h₄.2
      contradiction
    . simp at h₁ h₃ h₄ h₆
      ext
      . exact le_antisymm h₃ h₁
      . cases h: a.closed
        . exact Eq.symm (h₄ h)
        . by_contra h'
          simp at h'
          have := Eq.trans (Eq.symm h) (h₆ h')
          contradiction

lemma minLo_le_left [LinearOrder α] {a b: Endpoint α} : (minLo a b).val ≤ a.val := by
  simp[minLo]
  split_ifs with hab hba hc
  . tauto
  . exact le_of_lt hba
  . exact le_of_not_gt hab
  . tauto

def maxHi [LinearOrder α] (a b : Endpoint α) : Endpoint α :=
  if a.val > b.val then a else
  if b.val > a.val then b else
  if ¬a.closed ∧ b.closed then b else a

lemma maxHi_or [LinearOrder α] (a b: Endpoint α) :
    maxHi a b = a ∨ maxHi a b = b := by
      unfold maxHi
      split_ifs <;> simp

lemma maxHi_commutative [LinearOrder α] {a b: Endpoint α} :
  maxHi a b = maxHi b a := by
    simp[maxHi]
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ <;> try simp
    . have := (lt_self_iff_false a.val).mp (lt_trans h₂ h₁)
      contradiction
    . have := Eq.trans (Eq.symm h₅.1) h₄.2
      contradiction
    . simp at h₁ h₃ h₄ h₆
      ext
      . exact le_antisymm h₁ h₃
      . cases h: a.closed
        . exact Eq.symm (h₄ h)
        . by_contra h'
          simp at h'
          have := Eq.trans (Eq.symm h) (h₆ h')
          contradiction

lemma le_maxHi_left [LinearOrder α] {a b: Endpoint α} : a.val ≤ (maxHi a b).val := by
  simp[maxHi]
  split_ifs with hab hba hc
  . tauto
  . exact le_of_lt hba
  . exact le_of_not_gt hab
  . tauto

/-- `below x hi` holds when `x` is on the correct side of the upper endpoint `hi`,
respecting its closedness: `x ≤ hi.val` if closed, `x < hi.val` if open. -/
def below [LinearOrder α] (x: α) (hi : Endpoint α) : Prop :=
  if(hi.closed) then x ≤ hi.val else x < hi.val

/-- `above x lo` holds when `x` is on the correct side of the lower endpoint `lo`,
respecting its closedness: `lo.val ≤ x` if closed, `lo.val < x` if open. -/
def above [LinearOrder α] (x: α) (lo : Endpoint α) : Prop :=
  if(lo.closed) then lo.val ≤ x else lo.val < x

lemma le_of_below [LinearOrder α] (x: α) (lo: Endpoint α) :
    below x lo → x ≤ lo.val := by
      simp[below]
      by_cases h : lo.closed <;> simp[h]
      exact le_of_lt

lemma ge_of_above [LinearOrder α] (x: α) (hi: Endpoint α) :
    above x hi → x ≥ hi.val := by
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

lemma below_of_below_of_le [LinearOrder α] {hi hi': Endpoint α}
    (h: hi.val ≤ hi'.val) (hep: ¬hi.closed ∨ hi'.closed) {x: α} :
  below x hi → below x hi' := by
    unfold below
    by_cases hc: hi.closed <;> simp[hc] <;>
    by_cases hc': hi'.closed <;> simp[hc']
    . intro h'
      exact le_trans h' h
    . simp[hc,hc'] at hep
    . intro h'
      exact le_of_lt (lt_of_lt_of_le h' h)
    . intro h'
      exact lt_of_lt_of_le h' h

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

lemma above_of_above_of_le [LinearOrder α] {lo lo': Endpoint α}
    (h: lo'.val ≤ lo.val) (hep: ¬lo.closed ∨ lo'.closed) {x: α} :
  above x lo → above x lo' := by
    unfold above
    by_cases hc: lo.closed <;> simp[hc] <;>
    by_cases hc': lo'.closed <;> simp[hc']
    . intro h'
      exact le_trans h h'
    . simp[hc,hc'] at hep
    . intro h'
      exact le_of_lt (lt_of_le_of_lt h h')
    . intro h'
      exact lt_of_le_of_lt h h'

/-! ### Endpoint operations for intersection and difference -/

/-- Most restrictive (largest) lower endpoint: `above x (maxLo a b) ↔ above x a ∧ above x b`. -/
def maxLo [LinearOrder α] (a b : Endpoint α) : Endpoint α :=
  if b.val < a.val then a else
  if a.val < b.val then b else
  if a.closed ∧ ¬b.closed then b else a

/-- Most restrictive (smallest) upper endpoint: `below x (minHi a b) ↔ below x a ∧ below x b`. -/
def minHi [LinearOrder α] (a b : Endpoint α) : Endpoint α :=
  if a.val < b.val then a else
  if b.val < a.val then b else
  if a.closed ∧ ¬b.closed then b else a

-- `h1 : ¬(b < a)` gives `not_lt.mp h1 : a ≤ b`; `h2 : ¬(a < b)` gives `not_lt.mp h2 : b ≤ a`
-- so `le_antisymm (not_lt.mp h1) (not_lt.mp h2) : a = b`
lemma above_maxLo [LinearOrder α] (x : α) (a b : Endpoint α) :
    above x (maxLo a b) ↔ above x a ∧ above x b := by
  constructor
  · intro h
    simp only [maxLo] at h
    split_ifs at h with h1 h2 h3
    · exact ⟨h, above_of_above_of_lt h1 h⟩
    · exact ⟨above_of_above_of_lt h2 h, h⟩
    · -- h1:¬(b<a), h2:¬(a<b), h3:(a.closed∧¬b.closed), maxLo=b
      have heq : a.val = b.val := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      -- above x b → above x a: use a.val=b.val, a.closed, and above_of_above_of_le
      exact ⟨above_of_above_of_le (le_of_eq heq) (Or.inr h3.1) h, h⟩
    · -- h1:¬(b<a), h2:¬(a<b), h3:¬(a.closed∧¬b.closed), maxLo=a
      have heq : a.val = b.val := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      -- above x a → above x b: a.val=b.val, ¬(a.closed∧¬b.closed) → ¬a.closed ∨ b.closed
      push_neg at h3
      refine ⟨h, above_of_above_of_le (le_of_eq heq.symm) ?_ h⟩
      cases hac : a.closed
      · exact Or.inl (by simp)
      · exact Or.inr (h3 (by simp [hac]))
  · rintro ⟨ha, hb⟩
    simp only [maxLo]
    split_ifs with h1 h2 h3 <;> assumption

-- `h1 : ¬(a < b)` gives `not_lt.mp h1 : b ≤ a`; `h2 : ¬(b < a)` gives `not_lt.mp h2 : a ≤ b`
-- so `le_antisymm (not_lt.mp h2) (not_lt.mp h1) : a = b`
lemma below_minHi [LinearOrder α] (x : α) (a b : Endpoint α) :
    below x (minHi a b) ↔ below x a ∧ below x b := by
  constructor
  · intro h
    simp only [minHi] at h
    split_ifs at h with h1 h2 h3
    · exact ⟨h, below_of_below_of_lt h1 h⟩
    · exact ⟨below_of_below_of_lt h2 h, h⟩
    · -- h1:¬(a<b), h2:¬(b<a), h3:(a.closed∧¬b.closed), minHi=b
      have heq : a.val = b.val := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      -- below x b → below x a: hi=b (open), hi'=a (closed), hi.val≤hi'.val = b.val≤a.val
      exact ⟨below_of_below_of_le (le_of_eq heq.symm) (Or.inr h3.1) h, h⟩
    · -- h1:¬(a<b), h2:¬(b<a), h3:¬(a.closed∧¬b.closed), minHi=a
      have heq : a.val = b.val := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      -- below x a → below x b: hi=a, hi'=b, hi.val≤hi'.val = a.val≤b.val
      push_neg at h3
      refine ⟨h, below_of_below_of_le (le_of_eq heq) ?_ h⟩
      cases hac : a.closed
      · exact Or.inl (by simp)
      · exact Or.inr (h3 (by simp [hac]))
  · rintro ⟨ha, hb⟩
    simp only [minHi]
    split_ifs with h1 h2 h3 <;> assumption

end Endpoint

/-- An interval over a linear order, given by a lower endpoint `lo` and an upper
endpoint `hi` satisfying `lo.val < hi.val` (strict) or `lo.val = hi.val` with both
endpoints closed (degenerate point interval). -/
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

@[simp]
lemma lo_below_hi [LinearOrder α] (I: Interval α) : Endpoint.below I.lo.val I.hi := by
  unfold Endpoint.below
  cases I.wf <;> simp_all

@[simp]
lemma hi_above_lo [LinearOrder α] (I: Interval α) : Endpoint.above I.hi.val I.lo := by
  unfold Endpoint.above
  cases I.wf <;> simp_all

/-- The set of points belonging to an interval: those `x` that are above `lo`
and below `hi` according to their respective closedness flags. -/
def toSet [LinearOrder α] (I: Interval α) : Set α := {x | Endpoint.above x I.lo ∧ Endpoint.below x I.hi}

lemma eq_closed_lo [LinearOrder α] [DenselyOrdered α] {I J : Interval α}
    (h: I.toSet = J.toSet) : I.lo.closed → J.lo.closed := by
  intro hIc
  have h' : I.lo.val ∈ J.toSet ∧ ∀ x ∈ J.toSet, I.lo.val ≤ x := by
    repeat rw[Eq.symm h]
    simp[toSet, Endpoint.above, Endpoint.below, hIc]
    constructor
    . have hIwf := I.wf
      intro hIhc
      simp[hIhc,hIc] at hIwf
      assumption
    . tauto
  by_cases hJc: J.lo.closed
  . simp_all
  . have h'₁ := h'.1
    simp[toSet,Endpoint.above,Endpoint.below,hJc] at h'₁
    have ⟨a, haJl, haIl⟩ := exists_between h'₁.1
    have haJ : a ∈ J.toSet := by
      simp[toSet,Endpoint.above,hJc,haJl,Endpoint.below]
      by_cases J.hi.closed <;> simp_all
      . exact le_of_lt (lt_of_lt_of_le haIl h'₁.2)
      . exact lt_trans haIl h'₁.2
    have := (lt_self_iff_false _).mp (lt_of_lt_of_le haIl (h'.2 a haJ))
    contradiction

lemma eq_closed_hi [LinearOrder α] [DenselyOrdered α] {I J : Interval α}
    (h: I.toSet = J.toSet) : I.hi.closed → J.hi.closed := by
  intro hIc
  have h' : I.hi.val ∈ J.toSet ∧ ∀ x ∈ J.toSet, x ≤ I.hi.val := by
    repeat rw[Eq.symm h]
    simp[toSet, Endpoint.above, Endpoint.below, hIc]
    have hIwf := I.wf
    intro hIhc
    simp[hIhc,hIc] at hIwf
    assumption
  by_cases hJc: J.hi.closed
  . simp_all
  . have h'₁ := h'.1
    simp[toSet,Endpoint.above,Endpoint.below,hJc] at h'₁
    have ⟨a, haIu, haJu⟩ := exists_between h'₁.2
    have haJ : a ∈ J.toSet := by
      simp[toSet,Endpoint.above,hJc,haJu,Endpoint.below]
      by_cases J.lo.closed <;> simp_all
      . exact le_of_lt (lt_of_le_of_lt h'₁.1 haIu)
      . exact lt_trans h'₁.1 haIu
    have := (lt_self_iff_false _).mp (lt_of_lt_of_le haIu (h'.2 a haJ))
    contradiction

theorem eq_closed [LinearOrder α] [DenselyOrdered α] {I J: Interval α}
    (h: I.toSet = J.toSet) : I.lo.closed=J.lo.closed ∧ I.hi.closed = J.hi.closed := by
      constructor
      . by_cases hIl: I.lo.closed <;> simp[hIl]
        . exact eq_closed_lo h hIl
        . by_contra hJl
          simp at hJl
          have := eq_closed_lo (Eq.symm h) hJl
          contradiction
      . by_cases hIu: I.hi.closed <;> simp[hIu]
        . exact eq_closed_hi h hIu
        . by_contra hJu
          simp at hJu
          have := eq_closed_hi (Eq.symm h) hJu
          contradiction

lemma toSet_not_empty [LinearOrder α] [DenselyOrdered α]
  (I: Interval α) : ∃ x, x∈I.toSet := by
  have hIwf := I.wf
  by_cases hIlc : I.lo.closed
  . use I.lo.val
    simp[Endpoint.above,Endpoint.below,hIlc,toSet]
    by_cases hIlh: I.lo.val < I.hi.val <;> simp[hIlh] at hIwf
    . simp[hIlh]
    . simp[hIwf]
  . by_cases hIhc : I.hi.closed
    . use I.hi.val
      simp[Endpoint.above,Endpoint.below,hIlc,hIhc,toSet]
      by_cases hIlh: I.lo.val < I.hi.val <;> simp[hIlh,hIlc] at hIwf
      simp[hIlh]
    . simp[hIlc,hIhc] at hIwf
      simp[toSet,Endpoint.above,Endpoint.below,hIlc,hIhc]
      apply exists_between
      exact hIwf

@[ext]
theorem ext_toSet [LinearOrder α] [DenselyOrdered α] {I J : Interval α}
  (h: I.toSet = J.toSet) : I = J := by
  have hc := eq_closed h
  simp at hc h
  unfold toSet at h
  ext <;> try simp[hc]
  . by_cases hlc: J.lo.closed
    <;> simp[hlc] at hc
    <;> simp[hc,hlc,Endpoint.above] at h
    . have hIlJ : I.lo.val ≤ J.lo.val := by
        have hJ : J.lo.val ∈ {x | J.lo.val ≤ x ∧ Endpoint.below x J.hi} := by
          simp
        rw[Eq.symm h] at hJ
        simp at hJ
        exact hJ.1
      have hJlI : J.lo.val ≤ I.lo.val := by
        have hI : I.lo.val ∈ {x | I.lo.val ≤ x ∧ Endpoint.below x I.hi} := by
          simp
        rw[h] at hI
        simp at hI
        exact hI.1
      exact le_antisymm hIlJ hJlI
    . by_contra hInJ
      by_cases hIleJ: I.lo.val ≤ J.lo.val
      . have hIlJ := lt_of_le_of_ne hIleJ hInJ
        have Iwf := I.wf
        simp[hc] at Iwf
        have : I.lo.val < min J.lo.val I.hi.val := by
          simp[hIlJ,Iwf]
        have ⟨x, hx⟩ := exists_between this
        simp at hx
        have hx' : x ∈ {x | I.lo.val < x ∧ Endpoint.below x I.hi} := by
          simp[Endpoint.below, hx]
          by_cases hIhc: I.hi.closed
          . simp[le_of_lt hx.2.2]
          . simp[hIhc]
        rw[h] at hx'
        simp at hx'
        have := (lt_self_iff_false _).mp (lt_trans hx'.1 hx.2.1)
        contradiction
      . simp at hIleJ
        have Jwf := J.wf
        simp[hlc] at Jwf
        have : J.lo.val < min I.lo.val J.hi.val := by
          simp[hIleJ,Jwf]
        have ⟨x, hx⟩ := exists_between this
        simp at hx
        have hx' : x ∈ {x | J.lo.val < x ∧ Endpoint.below x J.hi} := by
          simp[Endpoint.below, hx]
          by_cases hJhc: J.hi.closed
          . simp[le_of_lt hx.2.2]
          . simp[hJhc]
        rw[Eq.symm h] at hx'
        simp at hx'
        have := (lt_self_iff_false _).mp (lt_trans hx'.1 hx.2.1)
        contradiction
  . by_cases hlc: J.hi.closed
    <;> simp[hlc] at hc
    <;> simp[hc,hlc,Endpoint.below] at h
    . have hJlI : J.hi.val ≤ I.hi.val := by
        have hJ : J.hi.val ∈ {x | Endpoint.above x J.lo ∧ x ≤ J.hi.val} := by
          simp
        rw[Eq.symm h] at hJ
        simp at hJ
        exact hJ.2
      have hIlJ : I.hi.val ≤ J.hi.val := by
        have hI : I.hi.val ∈ {x | Endpoint.above x I.lo ∧ x ≤ I.hi.val} := by
          simp
        rw[h] at hI
        simp at hI
        exact hI.2
      exact le_antisymm hIlJ hJlI
    . by_contra hInJ
      by_cases hJleI: J.hi.val ≤ I.hi.val
      . have hJlI := lt_of_le_of_ne hJleI (λ a ↦ hInJ (id (Eq.symm a)))
        have Iwf := I.wf
        simp[hc] at Iwf
        have : max J.hi.val I.lo.val < I.hi.val := by
          simp[hJlI,Iwf]
        have ⟨x, hx⟩ := exists_between this
        simp at hx
        have hx' : x ∈ {x | Endpoint.above x I.lo ∧ x < I.hi.val} := by
          simp[Endpoint.above, hx]
          by_cases hIhc: I.lo.closed
          . simp[le_of_lt hx.1.2]
          . simp[hIhc]
        rw[h] at hx'
        simp at hx'
        have := (lt_self_iff_false _).mp (lt_trans hx'.2 hx.1.1)
        contradiction
      . simp at hJleI
        have Jwf := J.wf
        simp[hlc] at Jwf
        have : max I.hi.val J.lo.val < J.hi.val := by
          simp[hJleI,Jwf]
        have ⟨x, hx⟩ := exists_between this
        simp at hx
        have hx' : x ∈ {x | Endpoint.above x J.lo ∧ x < J.hi.val} := by
          simp[Endpoint.above, hx]
          by_cases hIhc: J.lo.closed
          . simp[le_of_lt hx.1.2]
          . simp[hIhc]
        rw[Eq.symm h] at hx'
        simp at hx'
        have := (lt_self_iff_false _).mp (lt_trans hx'.2 hx.1.1)
        contradiction

@[simp]
lemma mem {α: Type} [LinearOrder α] (x : α) (I: Interval α) :
  x ∈ I.toSet ↔ Endpoint.above x I.lo ∧ Endpoint.below x I.hi := Iff.rfl

/-- Two intervals are disjoint when their point sets have empty intersection. -/
def disjoint [LinearOrder α] (I J : Interval α) : Prop :=
  Disjoint I.toSet J.toSet

lemma not_mem_of_disjoint_right [LinearOrder α] {I J: Interval α} (h: I.disjoint J) :
  ∀ x ∈ J.toSet, ¬(x ∈ I.toSet) := by
    simp[disjoint] at h
    intro x hx
    exact Disjoint.notMem_of_mem_right h hx

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

/-- `I.before J` means the intervals are strictly separated and cannot be merged:
either `I.hi.val < J.lo.val`, or the endpoints meet at the same value but both are open. -/
def before [LinearOrder α] (I J : Interval α) : Prop :=
  I.hi.val < J.lo.val ∨
  (I.hi.val = J.lo.val ∧ ¬I.hi.closed ∧ ¬J.lo.closed)

lemma disjoint_of_before [LinearOrder α] {I J : Interval α} : I.before J → I.disjoint J := by
  intro h
  unfold disjoint
  intro A
  simp
  intro hAI hAJ
  by_contra hneq
  have hnemp := Set.nonempty_iff_ne_empty.mpr hneq
  rcases hnemp with ⟨x, hx⟩
  have hxI := hAI hx
  have hxJ := hAJ hx
  simp[Endpoint.below] at hxI
  simp[Endpoint.above] at hxJ
  unfold before at h
  cases h with
  | inl h' =>
    by_cases hIhc : I.hi.closed <;> simp[hIhc] at hxI <;>
    by_cases hJlc : J.lo.closed <;> simp[hJlc] at hxJ
    . have hle := le_trans hxJ.1 hxI.2
      have := (lt_self_iff_false _).mp (lt_of_le_of_lt hle h')
      contradiction
    . have hlt := lt_of_lt_of_le hxJ.1 hxI.2
      have := (lt_self_iff_false _).mp (lt_trans hlt h')
      contradiction
    . have hlt := lt_of_le_of_lt hxJ.1 hxI.2
      have := (lt_self_iff_false _).mp (lt_trans hlt h')
      contradiction
    . have hlt := lt_trans hxJ.1 hxI.2
      have := (lt_self_iff_false _).mp (lt_trans hlt h')
      contradiction
  | inr h' =>
    by_cases hIhc : I.hi.closed <;> simp[hIhc] at hxI <;>
    by_cases hJlc : J.lo.closed <;> simp[hJlc] at hxJ <;>
    simp[hIhc,hJlc] at h'; rw[h'] at hxI
    . have := (lt_self_iff_false _).mp (lt_trans hxI.2 hxJ.1)
      contradiction

instance [LinearOrder α] [DecidableEq α] [DecidableLE α] {I J: Interval α} : Decidable (I.before J) := by
  by_cases hlt: I.hi.val < J.lo.val
  . exact isTrue (by left; exact hlt)
  . by_cases heq: I.hi.val=J.lo.val
    . by_cases hIo: ¬I.hi.closed
      . by_cases hJo: ¬J.lo.closed
        . exact isTrue (by right; exact ⟨heq, hIo, hJo⟩)
        . exact isFalse (by simp[before,heq,hIo,hJo])
      . exact isFalse (by simp[before,heq,hIo])
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
      . intro hhi hIhi
        simp[hIhi] at h'

lemma before_of_before_of_le [LinearOrder α] {I J K : Interval α}
  (hIJ: I.before J) (hJK: J ≤ K) : I.before K := by
    simp[(· ≤ ·)] at hJK
    unfold before at hIJ
    unfold before
    have hJwf := J.wf
    by_cases hIJlt : I.hi.val < J.lo.val <;> simp[hIJlt] at hIJ
    . left
      exact lt_of_lt_of_le hIJlt hJK.1
    . rw[hIJ.1]
      by_cases hJKlt : J.lo.val < K.lo.val <;> simp[hJKlt]
      have hjeq := eq_of_le_of_ge hJK.1 (not_lt.mp hJKlt)
      refine ⟨hjeq, hIJ.2.1, ?_⟩
      by_contra hKlc
      simp at hKlc
      have hJlc := hJK.2.2.1 hjeq hKlc
      simp[hJlc] at hIJ

/-! ### Interval intersection -/

/-- Intersection of two intervals: empty or a single interval. -/
def inter [LinearOrder α] (I J : Interval α) : List (Interval α) :=
  let lo := Endpoint.maxLo I.lo J.lo
  let hi := Endpoint.minHi I.hi J.hi
  if h : lo.val < hi.val ∨ (lo.val = hi.val ∧ lo.closed ∧ hi.closed) then
    [⟨lo, hi, h⟩]
  else
    []

lemma mem_inter [LinearOrder α] (I J : Interval α) (x : α) :
    (∃ K ∈ I.inter J, x ∈ K.toSet) ↔ x ∈ I.toSet ∧ x ∈ J.toSet := by
  simp only [inter, toSet, Set.mem_setOf_eq]
  split_ifs with h
  · -- non-empty intersection
    simp only [List.mem_singleton, exists_eq_left]
    exact ⟨fun ⟨ha, hb⟩ => ⟨⟨(Endpoint.above_maxLo x I.lo J.lo).mp ha |>.1,
                                (Endpoint.below_minHi x I.hi J.hi).mp hb |>.1⟩,
                              ⟨(Endpoint.above_maxLo x I.lo J.lo).mp ha |>.2,
                               (Endpoint.below_minHi x I.hi J.hi).mp hb |>.2⟩⟩,
           fun ⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩ =>
             ⟨(Endpoint.above_maxLo x I.lo J.lo).mpr ⟨ha1, ha2⟩,
              (Endpoint.below_minHi x I.hi J.hi).mpr ⟨hb1, hb2⟩⟩⟩
  · -- empty intersection: any x in I.toSet ∩ J.toSet would satisfy the wf condition
    simp only [List.not_mem_nil, false_and, exists_false, false_iff]
    rintro ⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩
    apply h
    have hlo := (Endpoint.above_maxLo x I.lo J.lo).mpr ⟨ha1, ha2⟩
    have hhi := (Endpoint.below_minHi x I.hi J.hi).mpr ⟨hb1, hb2⟩
    -- x satisfies above x (maxLo lo lo') and below x (minHi hi hi'), so wf holds
    have hx_ge_lo : (Endpoint.maxLo I.lo J.lo).val ≤ x := Endpoint.ge_of_above x _ hlo
    have hx_le_hi : x ≤ (Endpoint.minHi I.hi J.hi).val := Endpoint.le_of_below x _ hhi
    rcases (hx_ge_lo.trans hx_le_hi).lt_or_eq with hlt | heq
    · left; exact hlt
    · right
      have hx_le_lo : x ≤ (Endpoint.maxLo I.lo J.lo).val := hx_le_hi.trans_eq heq.symm
      have hhi_le_x : (Endpoint.minHi I.hi J.hi).val ≤ x := heq ▸ hx_ge_lo
      refine ⟨heq, ?_, ?_⟩
      · simp only [Endpoint.above] at hlo
        cases hclo : (Endpoint.maxLo I.lo J.lo).closed
        · simp [hclo] at hlo
          exact absurd hlo (not_lt.mpr hx_le_lo)
        · rfl
      · simp only [Endpoint.below] at hhi
        cases hchi : (Endpoint.minHi I.hi J.hi).closed
        · simp [hchi] at hhi
          exact absurd hhi (not_lt.mpr hhi_le_x)
        · rfl

/-! ### Interval difference -/

/-- `above x e` is the negation of `below x` at the complemented endpoint. -/
lemma Endpoint.above_iff_not_below_complement [LinearOrder α] (x : α) (e : Endpoint α) :
    Endpoint.above x e ↔ ¬Endpoint.below x ⟨e.val, !e.closed⟩ := by
  simp only [Endpoint.above, Endpoint.below]
  cases e.closed <;> simp [not_le, not_lt]

/-- `below x e` is the negation of `above x` at the complemented endpoint. -/
lemma Endpoint.below_iff_not_above_complement [LinearOrder α] (x : α) (e : Endpoint α) :
    Endpoint.below x e ↔ ¬Endpoint.above x ⟨e.val, !e.closed⟩ := by
  simp only [Endpoint.above, Endpoint.below]
  cases e.closed <;> simp [not_le, not_lt]

/-- Membership in an optional singleton interval (where the interval may be empty due to
    wf failing) is equivalent to the endpoint conditions. -/
private lemma mem_opt_interval [LinearOrder α] (lo hi : Endpoint α) (x : α) :
    (∃ K ∈ (if h : lo.val < hi.val ∨ (lo.val = hi.val ∧ lo.closed ∧ hi.closed)
             then [⟨lo, hi, h⟩]
             else ([] : List (Interval α))), x ∈ K.toSet) ↔
    Endpoint.above x lo ∧ Endpoint.below x hi := by
  split_ifs with h
  · simp only [List.mem_singleton, exists_eq_left, toSet, Set.mem_setOf_eq]
  · simp only [List.not_mem_nil, false_and, exists_false, false_iff]
    rintro ⟨ha, hb⟩
    apply h
    have hx_ge : lo.val ≤ x := Endpoint.ge_of_above x lo ha
    have hx_le : x ≤ hi.val := Endpoint.le_of_below x hi hb
    rcases (hx_ge.trans hx_le).lt_or_eq with hlt | heq
    · left; exact hlt
    · right
      refine ⟨heq, ?_, ?_⟩
      · simp only [Endpoint.above] at ha
        cases hclo : lo.closed
        · simp [hclo] at ha
          exact absurd ha (not_lt.mpr (hx_le.trans_eq heq.symm))
        · rfl
      · simp only [Endpoint.below] at hb
        cases hchi : hi.closed
        · simp [hchi] at hb
          exact absurd hb (not_lt.mpr (heq ▸ hx_ge))
        · rfl

/-- Difference `I \ J`: the left piece (below J) and right piece (above J) of I. -/
def diff [LinearOrder α] (I J : Interval α) : List (Interval α) :=
  -- Left piece uses hi = complement of J.lo
  let leftHi  : Endpoint α := ⟨J.lo.val, !J.lo.closed⟩
  -- Right piece uses lo = complement of J.hi
  let rightLo : Endpoint α := ⟨J.hi.val, !J.hi.closed⟩
  let leftHi'  := Endpoint.minHi I.hi leftHi
  let rightLo' := Endpoint.maxLo I.lo rightLo
  (if h : I.lo.val < leftHi'.val ∨
          (I.lo.val = leftHi'.val ∧ I.lo.closed ∧ leftHi'.closed)
   then [⟨I.lo, leftHi', h⟩] else []) ++
  (if h : rightLo'.val < I.hi.val ∨
          (rightLo'.val = I.hi.val ∧ rightLo'.closed ∧ I.hi.closed)
   then [⟨rightLo', I.hi, h⟩] else [])

lemma mem_diff [LinearOrder α] (I J : Interval α) (x : α) :
    (∃ K ∈ I.diff J, x ∈ K.toSet) ↔ x ∈ I.toSet ∧ x ∉ J.toSet := by
  constructor
  · rintro ⟨K, hK, hxK⟩
    simp only [diff, List.mem_append] at hK
    rcases hK with hKL | hKR
    · -- K is in the left piece
      have hmem := (mem_opt_interval I.lo (Endpoint.minHi I.hi ⟨J.lo.val, !J.lo.closed⟩) x).mp
        ⟨K, hKL, hxK⟩
      obtain ⟨hIlo, hhi⟩ := hmem
      have hIhi := (Endpoint.below_minHi x I.hi ⟨J.lo.val, !J.lo.closed⟩).mp hhi |>.1
      have hc := (Endpoint.below_minHi x I.hi ⟨J.lo.val, !J.lo.closed⟩).mp hhi |>.2
      rw [Endpoint.below_iff_not_above_complement] at hc
      simp only [Bool.not_not] at hc
      exact ⟨⟨hIlo, hIhi⟩, fun ⟨haJ, _⟩ => hc haJ⟩
    · -- K is in the right piece
      have hmem := (mem_opt_interval (Endpoint.maxLo I.lo ⟨J.hi.val, !J.hi.closed⟩) I.hi x).mp
        ⟨K, hKR, hxK⟩
      obtain ⟨hlo, hIhi⟩ := hmem
      have hIlo := (Endpoint.above_maxLo x I.lo ⟨J.hi.val, !J.hi.closed⟩).mp hlo |>.1
      have hc := (Endpoint.above_maxLo x I.lo ⟨J.hi.val, !J.hi.closed⟩).mp hlo |>.2
      rw [Endpoint.above_iff_not_below_complement] at hc
      simp only [Bool.not_not] at hc
      exact ⟨⟨hIlo, hIhi⟩, fun ⟨_, hbJ⟩ => hc hbJ⟩
  · intro ⟨hxI, hxnotJ⟩
    simp only [toSet, Set.mem_setOf_eq] at hxI
    obtain ⟨hIlo, hIhi⟩ := hxI
    -- hxnotJ : ¬(above x J.lo ∧ below x J.hi)
    rcases Classical.em (Endpoint.above x J.lo) with haJ | hnaJ
    · -- above x J.lo, so ¬below x J.hi
      have hnbJ : ¬Endpoint.below x J.hi := by
        simp only [toSet, Set.mem_setOf_eq] at hxnotJ
        exact fun hbJ => hxnotJ ⟨haJ, hbJ⟩
      -- x is in the right piece
      have habove_rlo : Endpoint.above x (Endpoint.maxLo I.lo ⟨J.hi.val, !J.hi.closed⟩) := by
        rw [Endpoint.above_maxLo]
        exact ⟨hIlo, (Endpoint.above_iff_not_below_complement x ⟨J.hi.val, !J.hi.closed⟩).mpr
          (by simp only [Bool.not_not]; exact hnbJ)⟩
      obtain ⟨K, hK, hxK⟩ := (mem_opt_interval _ I.hi x).mpr ⟨habove_rlo, hIhi⟩
      exact ⟨K, by simp only [diff]; exact List.mem_append_right _ hK, hxK⟩
    · -- ¬above x J.lo: x is in the left piece
      have hnblo : Endpoint.below x ⟨J.lo.val, !J.lo.closed⟩ :=
        (Endpoint.below_iff_not_above_complement x ⟨J.lo.val, !J.lo.closed⟩).mpr
          (by simp only [Bool.not_not]; exact hnaJ)
      have hbelow_lhi : Endpoint.below x (Endpoint.minHi I.hi ⟨J.lo.val, !J.lo.closed⟩) :=
        (Endpoint.below_minHi x I.hi ⟨J.lo.val, !J.lo.closed⟩).mpr ⟨hIhi, hnblo⟩
      obtain ⟨K, hK, hxK⟩ := (mem_opt_interval I.lo _ x).mpr ⟨hIlo, hbelow_lhi⟩
      exact ⟨K, by simp only [diff]; exact List.mem_append_left _ hK, hxK⟩

end Interval
