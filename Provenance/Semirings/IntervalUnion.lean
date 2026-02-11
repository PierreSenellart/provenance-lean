import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Nontrivial.Defs
import Provenance.Semirings.Interval
import Provenance.SemiringWithMonus

structure IntervalUnion (α: Type) [LinearOrder α] where
  intervals         : List (Interval α)
  pairwise_disjoint : intervals.Pairwise Interval.disjoint
  sorted            : intervals.Sorted LE.le

namespace IntervalUnion
def toSet [LinearOrder α] (U : IntervalUnion α) : Set α := ⋃ I ∈ U.intervals, I.toSet

theorem intervals_eq_of_toSet_eq [LinearOrder α] [DenselyOrdered α]
  (U V : IntervalUnion α) (h : U.toSet = V.toSet) :
  U.intervals = V.intervals := by
  rcases U with ⟨L₁, hdis₁, hsorted₁⟩
  rcases V with ⟨L₂, hdis₂, hsorted₂⟩
  simp[toSet] at h
  simp
  induction L₁ generalizing L₂ with
  | nil =>
    rw[eq_comm] at h
    simp at h
    cases L₂ with
    | nil => rfl
    | cons J tl =>
      have ⟨x,hx⟩ := Interval.toSet_not_empty J
      have hJ := h J
      simp at hJ
      rw[hJ] at hx
      contradiction
  | cons I tl ih =>
    cases L₂ with
    | nil =>
      simp at h
      have ⟨x, hx⟩ := Interval.toSet_not_empty I
      rw[h.1] at hx
      contradiction
    | cons J tl' =>
        have := ih (List.pairwise_cons.mp hdis₁).2
                   (List.sorted_cons.mp hsorted₁).2 tl'
                   (List.pairwise_cons.mp hdis₂).2
                   (List.sorted_cons.mp hsorted₂).2
        sorry

theorem ext [LinearOrder α] (U V : IntervalUnion α)
  (h : U.intervals = V.intervals) : U = V := by
  cases U
  cases V
  simp at h
  cases h
  simp

@[ext]
theorem ext_toSet [LinearOrder α] [DenselyOrdered α] (U V : IntervalUnion α)
  (h: U.toSet = V.toSet) : U = V := by
  apply IntervalUnion.ext U V
  exact intervals_eq_of_toSet_eq U V h

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

lemma merge_commutative [LinearOrder α] {I J: Interval α} {h: ¬(I.before J ∨ J.before I)}:
  merge I J h = merge J I (by exact fun a ↦ h (id (Or.symm a))) := by
    simp[merge,Endpoint.minLo_commutative,Endpoint.maxHi_commutative]

lemma mem_merge' [LinearOrder α] {I J: Interval α} (h: ¬(I.before J ∨ J.before I)):
  ∀ x, x ∈ I.toSet → x ∈ (merge I J h).toSet := by
    intro x hI
    constructor
    . by_cases hIJ: I.lo.val ≤ J.lo.val
      . by_cases hIc: I.lo.closed
        . apply Endpoint.above_of_above_of_le (Endpoint.minLo_le_left) _
          . exact hI.1
          . simp[hIc]
            unfold Endpoint.minLo
            by_cases hIJ': I.lo.val < J.lo.val <;> simp[hIJ',hIc]
            simp[not_lt_of_ge hIJ]
            exact hIc
        . unfold merge Endpoint.minLo
          by_cases hIJ': I.lo.val < J.lo.val <;> simp[hIJ',hIc]
          . exact hI.1
          . simp[Endpoint.above,hIc] at hI
            simp[not_lt_of_ge hIJ]
            split_ifs with hJc <;> simp[Endpoint.above,hJc]
            . exact le_trans (not_lt.mp hIJ') (le_of_lt hI.1)
            . simp[hIc]
              exact hI.1
      . simp at hIJ
        simp[merge,Endpoint.minLo,not_lt_of_gt hIJ,hIJ]
        exact Endpoint.above_of_above_of_lt hIJ hI.1
    . by_cases hIJ: J.hi.val ≤ I.hi.val
      . by_cases hIc: I.hi.closed
        . apply Endpoint.below_of_below_of_le (Endpoint.le_maxHi_left) _
          . exact hI.2
          . simp[hIc]
            unfold Endpoint.maxHi
            by_cases hIJ': J.hi.val < I.hi.val <;> simp[hIJ',hIc]
            simp[not_lt_of_ge hIJ]
            exact hIc
        . unfold merge Endpoint.maxHi
          by_cases hIJ': J.hi.val < I.hi.val <;> simp[hIJ',hIc]
          . exact hI.2
          . simp[Endpoint.below,hIc] at hI
            simp[not_lt_of_ge hIJ]
            split_ifs with hJc <;> simp[Endpoint.below,hJc]
            . exact le_trans (le_of_lt hI.2) (not_lt.mp hIJ')
            . simp[hIc]
              exact hI.2
      . simp at hIJ
        simp[merge,Endpoint.maxHi,not_lt_of_gt hIJ,hIJ]
        exact Endpoint.below_of_below_of_lt hIJ hI.2

lemma mem_merge [LinearOrder α] {I J: Interval α} {h: ¬(I.before J ∨ J.before I)}:
  ∀ x, x ∈ (merge I J h).toSet ↔ x ∈ I.toSet ∨ x ∈ J.toSet := by
    intro x
    apply Iff.intro
    . intro hmem
      simp at hmem
      by_cases hI : x ∈ I.toSet
      . tauto
      . simp[hI]
        simp[merge] at hmem
        simp at h
        constructor
        . have hmem₁ := hmem.1
          have h₁ := h.1
          by_cases hIJ : Endpoint.minLo I.lo J.lo = J.lo
          . rw[hIJ] at hmem₁
            exact hmem₁
          . have hIJ' : Endpoint.minLo I.lo J.lo = I.lo := by
              have := Endpoint.minLo_or I.lo J.lo
              simp[hIJ] at this
              exact this
            rw[hIJ'] at hmem₁
            simp[Endpoint.above] at hmem₁
            simp[Endpoint.above]
            simp[Endpoint.minLo] at hIJ'
            by_cases hle : J.lo.val ≤ I.lo.val
            . simp[hle] at hIJ'
              by_cases hlt: J.lo.val < I.lo.val
              . simp[hlt] at hIJ'
                rw[hIJ'] at hlt
                have := (lt_self_iff_false _).mp hlt
                contradiction
              . simp at hlt
                have heq : I.lo.val = J.lo.val := antisymm hlt hle
                rw[Eq.symm heq]
                by_cases hJc: J.lo.closed <;> by_cases hIc: I.lo.closed <;> simp[hJc] <;> simp[hIc] at hmem₁
                . assumption
                . exact le_of_lt hmem₁
                . simp[Endpoint.above,hmem₁,hIc,Endpoint.below] at hI
                  simp[Interval.before,Eq.symm heq,hJc] at h₁
                  by_cases hIhc: I.hi.closed <;> simp[hIhc] at hI
                  . exact lt_of_le_of_lt I.le_lo_hi hI
                  . have hIwf := I.wf
                    simp[hIc,hIhc] at hIwf
                    exact lt_of_lt_of_le hIwf hI
                . assumption
            . simp at hle
              simp[Endpoint.above,hmem₁,Endpoint.below] at hI
              simp[Interval.before] at h₁
              by_cases hJc : J.lo.closed <;> simp[hJc]
                                         <;> by_cases hIhc : I.hi.closed
                                         <;> simp[hIhc] at hI
              . exact le_trans h₁.1 (le_of_lt hI)
              . exact le_trans h₁.1 hI
              . exact lt_of_le_of_lt h₁.1 hI
              . simp[hIhc] at h₁
                exact lt_of_lt_of_le (lt_of_le_of_ne h₁.1 (λ a ↦ h₁.2 (id (Eq.symm a)))) hI

        . have hmem₂ := hmem.2
          have h₂ := h.2
          by_cases hIJ : Endpoint.maxHi I.hi J.hi = J.hi
          . rw[hIJ] at hmem₂
            exact hmem₂
          . have hIJ' : Endpoint.maxHi I.hi J.hi = I.hi := by
              have := Endpoint.maxHi_or I.hi J.hi
              simp[hIJ] at this
              exact this
            rw[hIJ'] at hmem₂
            simp[Endpoint.below] at hmem₂
            simp[Endpoint.below]
            simp[Endpoint.maxHi] at hIJ'
            by_cases hle : I.hi.val ≤ J.hi.val
            . simp[hle] at hIJ'
              by_cases hlt: I.hi.val < J.hi.val
              . simp[hlt] at hIJ'
                rw[hIJ'] at hlt
                have := (lt_self_iff_false _).mp hlt
                contradiction
              . simp at hlt
                have heq : I.hi.val = J.hi.val := antisymm hle hlt
                rw[Eq.symm heq]
                by_cases hJc: J.hi.closed <;> by_cases hIc: I.hi.closed <;> simp[hJc] <;> simp[hIc] at hmem₂
                . assumption
                . exact le_of_lt hmem₂
                . simp[Endpoint.below,hmem₂,hIc,Endpoint.above] at hI
                  simp[Interval.before,Eq.symm heq,hJc] at h₂
                  by_cases hIlc: I.lo.closed <;> simp[hIlc] at hI
                  . exact lt_of_lt_of_le hI I.le_lo_hi
                  . have hIwf := I.wf
                    simp[hIc,hIlc] at hIwf
                    exact lt_of_le_of_lt hI hIwf
                . assumption
            . simp at hle
              simp[Endpoint.below,hmem₂,Endpoint.above] at hI
              simp[Interval.before] at h₂
              by_cases hJc : J.hi.closed <;> simp[hJc]
                                         <;> by_cases hIlc : I.lo.closed
                                         <;> simp[hIlc] at hI
              . exact le_trans (le_of_lt hI) h₂.1
              . exact le_trans hI h₂.1
              . exact lt_of_lt_of_le hI h₂.1
              . simp[hIlc] at h₂
                exact lt_of_le_of_lt hI (lt_of_le_of_ne h₂.1 (λ a ↦ h₂.2 (id (Eq.symm a))))

    . intro hmem
      by_cases hI : x ∈ I.toSet
      . exact mem_merge' h x hI
      . cases hmem with
        | inl => contradiction
        | inr hJ =>
        . rw[merge_commutative]
          conv at h =>
            rhs
            rw[or_comm]
          exact mem_merge' h x hJ

set_option maxHeartbeats 500000
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
    intro J hJI hJL
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

lemma insertMergeList_preserves_disjoint [LinearOrder α] (I : Interval α) :
  ∀ {l : List (Interval α)}, (l.Sorted LE.le ∧ l.Pairwise Interval.disjoint) →
    (insertMergeList I l).Pairwise Interval.disjoint := by
  intro l
  induction l generalizing I with
  | nil => simp[insertMergeList]
  | cons J tl ih =>
    intro hs
    rw[List.pairwise_cons] at hs
    unfold insertMergeList
    by_cases hIJ: I.before J <;> simp[hIJ]
    . constructor
      . constructor
        . exact Interval.disjoint_of_before hIJ
        . intro K hK
          have hJtl := hs.1
          simp at hJtl
          exact Interval.disjoint_of_before
            (Interval.before_of_before_of_le hIJ (hJtl.1 K hK))
      . constructor
        . exact hs.2.1
        . exact hs.2.2
    . by_cases hJI: J.before I <;> simp[hJI]
      . constructor
        . intro K hK
          simp[Interval.disjoint]
          intro A
          simp
          intro hAJ hAK
          by_contra hc
          have hnemp := Set.nonempty_iff_ne_empty.mpr hc
          rcases hnemp with ⟨x, hx⟩
          have hxJ := hAJ hx
          have hxK := hAK hx
          have hmem := (mem_insertMergeList I tl x).mp ⟨K, ⟨hK, hxK⟩⟩
          cases hmem with
          | inl h =>
            have hh := Interval.disjoint_of_before hJI (Set.singleton_subset_iff.mpr hxJ)
            have := hh (Set.singleton_subset_iff.mpr h)
            simp at this
          | inr h =>
            rcases h with ⟨M, ⟨hM, hxM⟩⟩
            have := hs.2.1 M hM (Set.singleton_subset_iff.mpr hxJ) (Set.singleton_subset_iff.mpr hxM)
            simp at this
        . exact ih I ⟨(List.sorted_cons.mp hs.1).2, hs.2.2⟩
      . apply ih (merge I J (not_or_intro hIJ hJI))
        exact ⟨(List.sorted_cons.mp hs.1).2, hs.2.2⟩

def insertMerge [LinearOrder α]
  (I: Interval α) (U: IntervalUnion α) : IntervalUnion α :=
  ⟨
    insertMergeList I U.intervals,
    insertMergeList_preserves_disjoint I ⟨U.sorted, U.pairwise_disjoint⟩,
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

instance : AddMonoid (IntervalUnion α) where
  add_assoc := by
    intro a b c
    simp[(· + ·), Add.add]
    ext x
    repeat rw[IntervalUnion.mem_union]
    tauto
