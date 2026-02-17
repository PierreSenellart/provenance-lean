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

lemma minLo_le_right [LinearOrder α] {a b: Endpoint α} : (minLo a b).val ≤ b.val := by
  simp[minLo]
  split_ifs with hab hba hc
  . exact le_of_lt hab
  . tauto
  . tauto
  . exact le_of_not_gt hba

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

lemma le_maxHi_right [LinearOrder α] {a b: Endpoint α} : a.val ≤ (maxHi a b).val := by
  simp[maxHi]
  split_ifs with hab hba hc
  . tauto
  . exact le_of_lt hba
  . exact le_of_not_gt hab
  . tauto

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

end Endpoint

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

@[ext]
theorem ext_toSet [LinearOrder α] [DenselyOrdered α] {I J : Interval α}
  (h: I.toSet = J.toSet) : I = J := by
  have hc := eq_closed h
  let ⟨Ilo,Ihi,Iwf⟩ := I
  let ⟨Jlo,Jhi,Jwf⟩ := J
  simp at hc h
  unfold toSet at h
  rw[hc.1,hc.2] at Iwf
  simp
  constructor <;> ext <;> try simp[hc]
  . by_cases hlc: Jlo.closed <;> simp[hlc] at h
    . have hIlJ : Ilo.val ≤ Jlo.val := by
        sorry
      sorry
    . sorry
  . sorry


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

lemma ne_of_before [LinearOrder α] {I J : Interval α} : I.before J → I ≠ J := by
  unfold before
  intro h
  by_contra heq
  rw[Eq.symm heq] at h
  cases h with
  | inl h' =>
    have hIwf := I.wf
    cases hIwf with
    | inl h'' =>
      have := (lt_self_iff_false _).mp (lt_trans h' h'')
      contradiction
    | inr h'' =>
      rw[h''.1] at h'
      have := (lt_self_iff_false _).mp h'
      contradiction
  | inr h' =>
    have hIwf := I.wf
    simp[h'.1] at hIwf
    simp[hIwf] at h'

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
    simp[hIhc,hJlc] at h' <;> rw[h'] at hxI
    . have := (lt_self_iff_false _).mp (lt_of_le_of_lt hxI.2 hxJ.1)
      contradiction
    . have := (lt_self_iff_false _).mp (lt_of_lt_of_le hxI.2 hxJ.1)
      contradiction
    . have := (lt_self_iff_false _).mp (lt_trans hxI.2 hxJ.1)
      contradiction

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
      constructor
      . exact eq_of_le_of_ge hJK.1 (not_lt.mp hJKlt)
      . intro hIhc
        simp[hIhc] at hIJ
        have hIwf := I.wf
        simp[hIhc] at hIwf
        have hKwf := K.wf
        by_contra hKlc
        simp at hKlc
        simp[eq_of_le_of_ge hJK.1 (not_lt.mp hJKlt), hKlc, hIJ.2] at hJK

end Interval
