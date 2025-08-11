import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Nontrivial.Defs

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

structure IntervalUnion (α: Type) [LinearOrder α] where
  intervals         : List (Interval α)
  pairwise_disjoint : intervals.Pairwise (fun I J => I ≠ J → I.disjoint J)
  sorted            : intervals.Sorted LE.le

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


def merge [LinearOrder α] (I J : Interval α) (h: ¬ (I.before J ∨ J.before I)) :
  Interval α :=
  let lo := Endpoint.minLo I.lo J.lo
  let hi := Endpoint.maxHi I.hi J.hi
  {
    lo := lo
    hi := hi
    wf := by
      subst lo hi
      unfold Endpoint.minLo Endpoint.maxHi
      simp
      by_cases hIJlo: I.lo.val < J.lo.val <;> simp[hIJlo]
      . by_cases hJIhi: J.hi.val < I.hi.val <;> simp[hJIhi]
        . exact I.wf
        . by_cases hIJhi: I.hi.val < J.hi.val <;> simp[hIJhi]
          . left
            exact lt_of_lt_of_le hIJlo J.le_lo_hi
          . by_cases hkhi : ¬I.hi.closed ∧ J.hi.closed
            . simp[hkhi]
              left
              exact lt_of_lt_of_le hIJlo J.le_lo_hi
            . simp at hkhi
              have hIwf := I.wf
              by_cases hIc: I.hi.closed <;> simp[hIc]
              . simp[hIc] at hIwf
                exact hIwf
              . simp at hIc
                simp[hkhi hIc,hIc]
                simp[hIc] at hIwf
                exact hIwf
      . by_cases hJIlo: J.lo.val < I.lo.val <;> simp[hJIlo]
        . by_cases hJIhi: J.hi.val < I.hi.val <;> simp[hJIhi]
          . left
            exact lt_of_lt_of_le hJIlo I.le_lo_hi
          . by_cases hIJhi: I.hi.val < J.hi.val <;> simp[hIJhi]
            . exact J.wf
            . by_cases hkhi : ¬I.hi.closed ∧ J.hi.closed
              . simp[hkhi]
                have := J.wf
                tauto
              . simp at hkhi
                by_cases hIc: I.hi.closed <;> simp[hIc]
                . left
                  exact lt_of_lt_of_le hJIlo I.le_lo_hi
                . simp at hIc
                  simp[hkhi hIc]
                  left
                  exact lt_of_lt_of_le hJIlo I.le_lo_hi
        . have hIJloeq : I.lo.val=J.lo.val := by
            simp at hIJlo
            simp at hJIlo
            exact le_antisymm hJIlo hIJlo
          by_cases hJIhi: J.hi.val < I.hi.val <;> simp[hJIhi] <;>
          by_cases hklo : ¬I.lo.closed ∧ J.lo.closed
          . simp[hklo]
            left
            exact lt_of_le_of_lt J.le_lo_hi hJIhi
          . simp at hklo
            by_cases hIc: I.lo.closed <;> simp[hIc]
            . have Iwf := I.wf
              simp[hIc] at Iwf
              exact Iwf
            . simp at hIc
              simp[hklo hIc]
              exact I.wf
          . simp[hklo]
            have Jwf := J.wf
            by_cases hIJhi: I.hi.val < J.hi.val <;> simp[hIJhi]
            . tauto
            . by_cases hkhi : ¬I.hi.closed ∧ J.hi.closed
              . simp[hkhi]
                tauto
              . simp at hkhi
                rw[← hIJloeq]
                by_cases hIc: I.hi.closed <;> simp[hIc]
                . exact lt_or_eq_of_le I.le_lo_hi
                . simp at hIc
                  simp[hkhi hIc]
                  have hIwf := I.wf
                  simp[hIc] at hIwf
                  left
                  exact hIwf
          . simp at hklo
            by_cases hIclo : I.lo.closed <;> simp[hIclo] <;>
            by_cases hIJhi : I.hi.val < J.hi.val <;> simp[hIJhi]
            . rw[hIJloeq]
              have := J.wf
              tauto
            . by_cases hIchi : I.hi.closed <;> simp[hIchi]
              . exact lt_or_eq_of_le I.le_lo_hi
              . by_cases hJchi : J.hi.closed <;> simp[hJchi]
                . rw[hIJloeq]
                  exact lt_or_eq_of_le J.le_lo_hi
                . have := I.wf
                  tauto
            . have := J.wf
              by_cases hJclo : J.lo.closed <;> simp[hJclo]
              . tauto
              . rw[hIJloeq]
                tauto
            . have hIwf := I.wf
              simp at hIclo
              simp[hklo hIclo]
              by_cases hIchi : I.hi.closed <;> simp[hIchi]
              . tauto
              . have hJwf := J.wf
                by_cases hJchi : J.hi.closed <;> simp[hJchi]
                . rw[hIJloeq]
                  simp[hIclo]
                  simp[hklo hIclo] at hJwf
                  exact hJwf
                . exact hIwf
  }


set_option maxHeartbeats 500000
lemma mem_merge [LinearOrder α] {I J: Interval α} {h: ¬(I.before J ∨ J.before I)}:
  ∀ x, x ∈ (merge I J h).toSet ↔ x ∈ I.toSet ∨ x ∈ J.toSet := by
    intro x
    unfold merge
    unfold Interval.toSet Endpoint.minLo Endpoint.maxHi
    simp
    by_cases hIJlo : I.lo.val < J.lo.val <;> simp only[hIJlo]
    . by_cases hJIhi : J.hi.val < I.hi.val <;> simp[hJIhi]
      . intro hl hi
        exact ⟨Endpoint.above_of_above_of_lt hIJlo hl,
               Endpoint.below_of_below_of_lt hJIhi hi⟩
      . by_cases hIJhi : I.hi.val < J.hi.val <;> simp[hIJhi]
        . sorry
        . sorry
    . sorry



lemma merge_preserves_le [LinearOrder α] {I: Interval α} {J: Interval α} {K: Interval α}
  (hKI: K ≤ I) (hKJ: K ≤ J) (h: ¬ (I.before J ∨ J.before I)) :
    K ≤ merge I J h := by
      simp[merge,(· ≤ ·)] at *
      unfold Endpoint.maxHi Endpoint.minLo
      constructor
      . by_cases hIJlo : I.lo.val < J.lo.val <;> simp only[hIJlo]
        . tauto
        . by_cases hJIlo : J.lo.val < I.lo.val <;> simp only[hJIlo]
          . tauto
          . by_cases hloIc : I.lo.closed <;> simp only[hloIc] <;>
            by_cases hloJc : J.lo.closed <;> (try simp only[hloJc]) <;> tauto
      . constructor
        . by_cases hJIhi : J.hi.val < I.hi.val <;> simp only[hJIhi]
          . tauto
          . by_cases hIJhi : I.hi.val < J.hi.val <;> simp only[hIJhi]
            . tauto
            . by_cases hhiIc : I.hi.closed <;> simp only[hhiIc] <;>
              by_cases hhiJc : J.hi.closed <;> (try simp only[hhiJc]) <;> tauto
        . constructor
          . by_cases hIJlo : I.lo.val < J.lo.val <;> simp only[hIJlo]
            . tauto
            . by_cases hJIlo : J.lo.val < I.lo.val <;> simp only[hJIlo]
              . tauto
              . by_cases hloIc : I.lo.closed <;> simp only[hloIc] <;>
                by_cases hloJc : J.lo.closed <;> (try simp only[hloJc]) <;> tauto
          . by_cases hJIhi : J.hi.val < I.hi.val <;> simp only[hJIhi]
            . tauto
            . by_cases hIJhi : I.hi.val < J.hi.val <;> simp only[hIJhi]
              . tauto
              . by_cases hhiIc : I.hi.closed <;> simp only[hhiIc] <;>
                by_cases hhiJc : J.hi.closed <;> (try simp only[hhiJc]) <;> tauto


def insertMergeList [LinearOrder α] (I : Interval α) : List (Interval α) → List (Interval α)
| []    => [I]
| J::tl =>
  if hIJ: I.before J then
    I::J::tl
  else if hJI: J.before I then
    J::(insertMergeList I tl)
  else
    insertMergeList (merge I J (by simp[hIJ, hJI])) tl


lemma mem_insertMergeList [LinearOrder α] (I : Interval α) (L : List (Interval α)) :
  ∀ x, (∃ J ∈ insertMergeList I L, x ∈ J.toSet) ↔ (x ∈ I.toSet ∨ ∃ J ∈ L, x ∈ J.toSet) := by
    intro x
    induction L generalizing I with
    | nil => simp[insertMergeList]
    | cons J tl ih =>
      unfold insertMergeList
      by_cases hIJ: I.before J <;> simp[hIJ]
      by_cases hJI: J.before I <;> simp[hJI]
      . apply Iff.intro
        . intro h
          cases h with
          | inl h' => tauto
          | inr h' =>
            rcases h' with ⟨K, hK⟩
            have : (∃ K' ∈ insertMergeList I tl, x ∈ K'.toSet) := by
              use K
              exact hK
            have ih' := (ih I).mp this
            cases ih' with
            | inl ih'₁ => left; tauto
            | inr ih'₂ =>
              rcases ih'₂ with ⟨M, hM⟩
              right; right
              use M
              tauto
        . intro h
          cases h with
          | inl h' =>
            right
            apply (ih I).mpr
            tauto
          | inr h' =>
            cases h' with
            | inl h'' => tauto
            | inr h'' =>
              have := (ih I).mpr (Or.inr h'')
              tauto
      . apply Iff.intro
        . intro h
          have := (ih (merge I J (not_or_intro hIJ hJI))).mp h
          cases this with
          | inl h' =>
            rw[mem_merge] at h'
            cases h' with
            | inl h'' => left; tauto
            | inr h'' => right; left; tauto
          | inr h' => tauto
        . intro h'
          have hbefore := not_or_intro hIJ hJI
          cases h' with
          | inl h' =>
            apply (ih (merge I J hbefore)).mpr
            left
            exact (mem_merge x).mpr (Or.inl h')
          | inr h' =>
            apply (ih (merge I J hbefore)).mpr
            cases h' with
            | inl h'' =>
              left
              exact (mem_merge x).mpr (Or.inr h'')
            | inr h'' =>
              right
              tauto


lemma insertMergeList_preserves_le [LinearOrder α] {I: Interval α} {L: List (Interval α)} :
  ∀ J, J≤I → (∀ K ∈ L, J≤K) → ∀ K ∈ insertMergeList I L, J ≤ K := by
    intro J hJI
    intro hJL
    induction L generalizing I with
    | nil => simp[insertMergeList]; exact hJI
    | cons M tl ih =>
      intro K
      unfold insertMergeList
      have hK'tl : ∀ K' ∈ tl, J≤K' := by
        intro K' hK'
        exact hJL K' (List.mem_cons_of_mem M hK')
      by_cases hIM: I.before M <;> simp[hIM]
      . by_cases hKI: K=I <;> simp[hKI]
        . exact hJI
        . by_cases hKM: K=M <;> simp[hKM]
          . exact hJL M List.mem_cons_self
          . intro hK
            exact hJL K (List.mem_cons_of_mem _ hK)
      . by_cases hMI: M.before I <;> simp[hMI]
        . by_cases hKM: K=M <;> simp[hKM]
          . exact hJL M (List.mem_cons_self)
          . have hK'tl : ∀ K' ∈ tl, J≤K' := by
              intro K' hK'
              exact hJL K' (List.mem_cons_of_mem M hK')
            exact ih hJI hK'tl K
        . exact ih (merge_preserves_le hJI (hJL M List.mem_cons_self) (not_or_intro hIM hMI)) hK'tl K


lemma insertMergeList_preserves_sorted [LinearOrder α] (I : Interval α) :
  ∀ {l : List (Interval α)}, l.Sorted LE.le →
    (insertMergeList I l).Sorted LE.le := by
  intro l
  induction l generalizing I with
  | nil => simp[insertMergeList]
  | cons J tl ih =>
    intro hs
    rw[List.sorted_cons] at hs
    unfold insertMergeList
    by_cases hIJ: I.before J <;> simp[hIJ]
    . constructor
      . intro K hK
        exact le_trans (Interval.le_of_before hIJ) (hs.1 K hK)
      . constructor
        . exact hs.1
        . exact hs.2
    . by_cases hJI: J.before I <;> simp[hJI]
      . constructor
        . exact insertMergeList_preserves_le J (Interval.le_of_before hJI) hs.1
        . exact ih I hs.2
      . apply ih (merge I J (not_or_intro hIJ hJI))
        exact hs.2


def insertMerge [LinearOrder α]
  (I: Interval α) (U: IntervalUnion α) : IntervalUnion α :=
  ⟨
    insertMergeList I U.intervals,
    sorry,
    insertMergeList_preserves_sorted I U.sorted
  ⟩


def union [LinearOrder α] (U V : IntervalUnion α) : IntervalUnion α :=
  V.intervals.foldl (fun acc I => (IntervalUnion.insertMerge I acc)) U


lemma mem_union [LinearOrder α] (U V : IntervalUnion α) :
  ∀ x, (x ∈ (U.union V).toSet) ↔ (x ∈ U.toSet) ∨ (x ∈ V.toSet) := by
    sorry
end IntervalUnion


variable {α: Type} [LinearOrder α] [BoundedOrder α] [Nontrivial α]

instance : Zero (IntervalUnion α) := ⟨[], by simp, by simp⟩
instance : One  (IntervalUnion α) := ⟨[⟨⟨⊥,⊥⟩,⟨⊤,⊥⟩,by simp⟩], by simp, by simp⟩

instance : Add  (IntervalUnion α) where
  add U V := U.union V
