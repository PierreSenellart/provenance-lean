import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Provenance.Semirings.BoolFunc
import Provenance.Semirings.Interval
import Provenance.SemiringWithMonus

/-!
# Interval-union semiring

This file defines the semiring of finite unions of pairwise-disjoint intervals over
a dense linear order, used for provenance in temporal and numeric-range databases.

An `IntervalUnion α` is a sorted, non-overlapping list of intervals. Addition is union,
multiplication is intersection, and monus is set difference. The natural order is
set inclusion.

## Main definitions

* `IntervalUnion α` — a finite union of pairwise-disjoint, sorted intervals
* `IntervalUnion.toSet` — the corresponding point set
* `IntervalUnion.union` — union of two interval unions (addition)
* `IntervalUnion.inter` — intersection of two interval unions (multiplication)
* `IntervalUnion.diff` — set difference of two interval unions (monus)

## Main results

* `IntervalUnion.ext_toSet` — two interval unions with the same point set are equal
  (requires `DenselyOrdered`)
* `IntervalUnion.mem_union` / `mem_inter` / `mem_diff` — membership characterizations
* `instance : SemiringWithMonus (IntervalUnion α)` — interval unions form an m-semiring
  for any `DenselyOrdered` and `BoundedOrder` linear order
* `IntervalUnion.absorptive` — the semiring is absorptive (`1 + a = 1`): the whole
  space absorbs any interval union under union
* `IntervalUnion.mul_sub_left_distributive` — `a * (b - c) = a * b - a * c`, i.e.,
  `A ∩ (B \ C) = (A ∩ B) \ (A ∩ C)`

## Concrete instances

* `SemiringWithMonus (IntervalUnion EReal)` — interval unions over the extended reals
* `SemiringWithMonus (IntervalUnion (WithBot (WithTop ℚ)))` — interval unions over the
  extended rationals

## References

* [Widiaatmaja, Djeffal, Dandekar & Senellart, *Demonstration of ProvSQL Update Provenance through Temporal Databases*][DBLP:conf/pw/WidiaatmajaDDS25]
-/

/-- A finite union of pairwise-disjoint intervals sorted from left to right.
The invariants `pairwise_disjoint` and `pairwise_before` ensure the canonical
representation. -/
structure IntervalUnion (α: Type) [LinearOrder α] where
  intervals         : List (Interval α)
  pairwise_disjoint : intervals.Pairwise Interval.disjoint
  pairwise_before   : intervals.Pairwise Interval.before

namespace IntervalUnion
/-- The point set of an interval union: the union of the point sets of its intervals. -/
def toSet [LinearOrder α] (U : IntervalUnion α) : Set α := ⋃ I ∈ U.intervals, I.toSet

-- Helper: convexity of interval toSet
private lemma interval_mem_between [LinearOrder α] {I : Interval α} {y z x : α}
    (hy : y ∈ I.toSet) (hx : x ∈ I.toSet) (hyz : y < z) (hzx : z < x) : z ∈ I.toSet := by
  constructor
  · have h : I.lo.val < z := lt_of_le_of_lt (Endpoint.ge_of_above y I.lo hy.1) hyz
    unfold Endpoint.above; cases I.lo.closed
    · exact h
    · exact le_of_lt h
  · have h : z < I.hi.val := lt_of_lt_of_le hzx (Endpoint.le_of_below x I.hi hx.2)
    unfold Endpoint.below; cases I.hi.closed
    · exact h
    · exact le_of_lt h

-- Helper: if z < K'.lo.val then z ∉ K'.toSet
private lemma not_mem_of_lt_lo [LinearOrder α] {K' : Interval α} {z : α}
    (hlt : z < K'.lo.val) : z ∉ K'.toSet := by
  intro hmem
  exact lt_irrefl z (lt_of_lt_of_le hlt (Endpoint.ge_of_above z K'.lo hmem.1))

-- Helper: if z = K'.lo.val and K'.lo.closed = false then z ∉ K'.toSet
private lemma not_mem_of_eq_lo_open [LinearOrder α] {K' : Interval α} {z : α}
    (heq : z = K'.lo.val) (hopen : ¬K'.lo.closed) : z ∉ K'.toSet := by
  intro hmem
  by_cases hc : K'.lo.closed
  · exact absurd hc hopen
  · have hlo := hmem.1
    simp [Endpoint.above, hc] at hlo
    rw [heq] at hlo
    exact absurd hlo (lt_irrefl K'.lo.val)

-- Helper: if z = K'.hi.val and K'.hi.closed = false then z ∉ K'.toSet
private lemma not_mem_of_eq_hi_open [LinearOrder α] {K' : Interval α} {z : α}
    (heq : z = K'.hi.val) (hopen : ¬K'.hi.closed) : z ∉ K'.toSet := by
  intro hmem
  by_cases hc : K'.hi.closed
  · exact absurd hc hopen
  · have hhi := hmem.2
    simp [Endpoint.below, hc] at hhi
    rw [heq] at hhi
    exact absurd hhi (lt_irrefl K'.hi.val)

@[ext]
theorem ext_toSet [LinearOrder α] [DenselyOrdered α]
  (U V : IntervalUnion α) (h : U.toSet = V.toSet) : U = V := by
  rcases U with ⟨L₁, hdis₁, hpb₁⟩
  rcases V with ⟨L₂, hdis₂, hpb₂⟩
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
        have ihtl := ih (List.pairwise_cons.mp hdis₁).2
                        (List.pairwise_cons.mp hpb₁).2 tl'
                        (List.pairwise_cons.mp hdis₂).2
                        (List.pairwise_cons.mp hpb₂).2
        -- gap_contra₁: x ∈ I.toSet ∧ K ∈ tl' ∧ x ∈ K.toSet → False
        have gap_contra : ∀ x : α, x ∈ I.toSet →
            ∀ K ∈ tl', x ∈ K.toSet → False := by
          intro x hxI K hKtl' hxK
          -- J.before K from pairwise_before of J :: tl'
          have hJbK := (List.pairwise_cons.mp hpb₂).1 K hKtl'
          -- get y ∈ J.toSet (non-empty)
          obtain ⟨y, hyJ⟩ := Interval.toSet_not_empty J
          -- y is in I :: tl via h
          have hyL₁ : y ∈ ⋃ L ∈ I :: tl, L.toSet := by
            have : y ∈ ⋃ L ∈ J :: tl', L.toSet :=
              Set.mem_iUnion₂.mpr ⟨J, List.mem_cons_self, hyJ⟩
            rwa [h]
          rw [Set.mem_iUnion₂] at hyL₁
          obtain ⟨L, hLconsI, hyL⟩ := hyL₁
          -- y in I.toSet or L ∈ tl
          cases List.mem_cons.mp hLconsI with
          | inr hLtl =>
            -- y ∈ L.toSet with I.before L → I.hi.val ≤ L.lo.val ≤ y ≤ J.hi.val and x ≤ I.hi.val but x ≥ K.lo.val > J.hi.val
            have hIbL := (List.pairwise_cons.mp hpb₁).1 L hLtl
            -- I.hi.val ≤ L.lo.val
            have hIhiLlo : I.hi.val ≤ L.lo.val := by
              cases hIbL with
              | inl h => exact h.le
              | inr h => exact le_of_eq h.1
            -- L.lo.val ≤ y (from y ∈ L.toSet)
            have hLloY : L.lo.val ≤ y := by
              simp only [Interval.mem, Endpoint.above] at hyL
              split_ifs at hyL with hc
              · exact hyL.1
              · exact hyL.1.le
            -- y ≤ J.hi.val (from y ∈ J.toSet)
            have hyJhi : y ≤ J.hi.val := by
              simp only [Interval.mem, Endpoint.below] at hyJ
              split_ifs at hyJ with hc
              · exact hyJ.2
              · exact hyJ.2.le
            -- x ≤ I.hi.val (from x ∈ I.toSet)
            have hxIhi : x ≤ I.hi.val := by
              simp only [Interval.mem, Endpoint.below] at hxI
              split_ifs at hxI with hc
              · exact hxI.2
              · exact hxI.2.le
            -- K.lo.val ≤ x (or strict) (from x ∈ K.toSet)
            -- J.hi.val < K.lo.val or = with K.lo.open
            cases hJbK with
            | inl hJhiKlo =>
              have hKloX : K.lo.val ≤ x := by
                simp only [Interval.mem, Endpoint.above] at hxK
                split_ifs at hxK with hc
                · exact hxK.1
                · exact hxK.1.le
              exact lt_irrefl x (lt_of_le_of_lt
                (le_trans hxIhi (le_trans hIhiLlo (le_trans hLloY hyJhi)))
                (lt_of_lt_of_le hJhiKlo hKloX))
            | inr hJbKopen =>
              have hKloX : K.lo.val < x := by
                simp only [Interval.mem, Endpoint.above, hJbKopen.2.2] at hxK
                exact hxK.1
              exact lt_irrefl x (lt_of_le_of_lt
                (le_trans hxIhi (le_trans hIhiLlo (le_trans hLloY (hJbKopen.1 ▸ hyJhi))))
                hKloX)
          | inl hLI =>
            -- y ∈ I.toSet (L = I). Use convexity + gap argument.
            subst hLI
            -- Gap between J.hi and K.lo (or at J.hi = K.lo with open endpoints)
            -- Get K₁ = head of tl' for gap
            cases tl' with
            | nil => exact absurd hKtl' List.not_mem_nil
            | cons K₁ tl'' =>
              -- K₁ is first in tl'
              have hJbK₁ := (List.pairwise_cons.mp hpb₂).1 K₁ List.mem_cons_self
              -- K₁.lo.val ≤ K.lo.val (K ∈ K₁ :: tl'')
              have hK₁loKlo : K₁.lo.val ≤ K.lo.val := by
                cases List.mem_cons.mp hKtl' with
                | inl h => rw [h]
                | inr h =>
                  have := Interval.le_of_before
                    ((List.pairwise_cons.mp (List.pairwise_cons.mp hpb₂).2).1 K h)
                  simp [(· ≤ ·)] at this
                  exact this.1
              -- x ≥ K.lo.val ≥ K₁.lo.val
              have hxKlo : K₁.lo.val ≤ x := by
                have : K.lo.val ≤ x := by
                  simp only [Interval.mem, Endpoint.above] at hxK
                  split_ifs at hxK with hc
                  · exact hxK.1
                  · exact hxK.1.le
                exact le_trans hK₁loKlo this
              -- y ≤ J.hi.val (from y ∈ J.toSet)
              have hyJhi : y ≤ J.hi.val := by
                simp only [Interval.mem, Endpoint.below] at hyJ
                split_ifs at hyJ with hc
                · exact hyJ.2
                · exact hyJ.2.le
              -- For all K' ∈ tl', K₁.lo.val ≤ K'.lo.val
              have hK₁loAll : ∀ K' ∈ (K₁ :: tl''), K₁.lo.val ≤ K'.lo.val := by
                intro K' hK'
                cases List.mem_cons.mp hK' with
                | inl h => rw [h]
                | inr h =>
                  have := Interval.le_of_before
                    ((List.pairwise_cons.mp (List.pairwise_cons.mp hpb₂).2).1 K' h)
                  simp [(· ≤ ·)] at this
                  exact this.1
              -- gap argument on J.before K₁
              cases hJbK₁ with
              | inl hJhiK₁lo =>
                -- Get z strictly between J.hi.val and K₁.lo.val
                obtain ⟨z, hz1, hz2⟩ := exists_between hJhiK₁lo
                -- y < z (y ≤ J.hi.val < z)
                have hyz : y < z := lt_of_le_of_lt hyJhi hz1
                -- z < x (z < K₁.lo.val ≤ x)
                have hzx : z < x := lt_of_lt_of_le hz2 hxKlo
                -- z ∈ I.toSet by convexity
                have hzI := interval_mem_between hyL hxI hyz hzx
                -- z ∉ J.toSet
                have hznotJ : z ∉ J.toSet := by
                  simp only [Interval.mem, Endpoint.below]
                  intro ⟨_, hzhi⟩
                  split_ifs at hzhi with hc
                  · exact absurd hz1 (not_lt.mpr hzhi)
                  · exact absurd hz1 (not_lt.mpr hzhi.le)
                -- z ∉ K' for K' ∈ K₁ :: tl''
                have hznotK' : ∀ K' ∈ (K₁ :: tl''), z ∉ K'.toSet := by
                  intro K' hK'
                  have hK₁loK' := hK₁loAll K' hK'
                  exact not_mem_of_lt_lo (lt_of_lt_of_le hz2 hK₁loK')
                -- z ∉ ⋃ K ∈ J :: tl'
                have hznotL₂ : z ∉ ⋃ K ∈ J :: K₁ :: tl'', K.toSet := by
                  simp only [Set.mem_iUnion]
                  rintro ⟨K', hK', hzK'⟩
                  cases List.mem_cons.mp hK' with
                  | inl h => exact hznotJ (h ▸ hzK')
                  | inr h => exact hznotK' K' h hzK'
                -- But z ∈ I.toSet ⊆ ⋃ K ∈ I :: tl = ⋃ K ∈ J :: tl'
                apply hznotL₂; rw [← h]
                exact Set.mem_iUnion₂.mpr ⟨_, List.mem_cons_self, hzI⟩
              | inr hJbK₁open =>
                -- z = J.hi.val = K₁.lo.val, both open
                set z := J.hi.val
                -- y < z (J.hi.closed = false → y ∈ J.toSet → y < J.hi.val = z)
                have hyz : y < z := by
                  simp only [Interval.mem, Endpoint.below, hJbK₁open.2.1] at hyJ
                  exact hyJ.2
                -- z < x
                have hzx : z < x := by
                  have hzK₁lo : z = K₁.lo.val := hJbK₁open.1
                  rcases lt_or_eq_of_le (hzK₁lo ▸ hxKlo) with hlt | heqx
                  · exact hlt
                  · exfalso
                    cases List.mem_cons.mp hKtl' with
                    | inl hKK₁ =>
                      rw [hKK₁] at hxK
                      simp only [Interval.mem, Endpoint.above, hJbK₁open.2.2] at hxK
                      exact absurd (hzK₁lo.symm.trans heqx ▸ hxK.1) (lt_irrefl x)
                    | inr hKtl'' =>
                      have hK₁K := (List.pairwise_cons.mp (List.pairwise_cons.mp hpb₂).2).1 K hKtl''
                      have hKloX : K.lo.val ≤ x := by
                        simp only [Interval.mem, Endpoint.above] at hxK
                        split_ifs at hxK with hc
                        · exact hxK.1
                        · exact hxK.1.le
                      have hKloZ : K.lo.val = z :=
                        le_antisymm (heqx ▸ hKloX)
                                    (hzK₁lo ▸ hK₁loAll K (List.mem_cons_of_mem K₁ hKtl''))
                      cases hK₁K with
                      | inl hlt =>
                        exact lt_irrefl K₁.lo.val
                          (lt_of_le_of_lt K₁.le_lo_hi (hlt.trans_eq (hKloZ.trans hzK₁lo)))
                      | inr heq =>
                        have : K₁.hi.val = z := heq.1.trans hKloZ
                        cases K₁.wf with
                        | inl h' =>
                          exact lt_irrefl K₁.lo.val (h'.trans_eq (this.trans hzK₁lo))
                        | inr h' => exact absurd h'.2.2 heq.2.1
                -- z ∈ I.toSet by convexity
                have hzI := interval_mem_between hyL hxI hyz hzx
                -- z ∉ J.toSet (J.hi.closed = false, z = J.hi.val)
                have hznotJ : z ∉ J.toSet := not_mem_of_eq_hi_open rfl hJbK₁open.2.1
                -- z ∉ K' for K' ∈ K₁ :: tl''
                have hznotK' : ∀ K' ∈ (K₁ :: tl''), z ∉ K'.toSet := by
                  intro K' hK'
                  cases List.mem_cons.mp hK' with
                  | inl h => exact h ▸ not_mem_of_eq_lo_open hJbK₁open.1 hJbK₁open.2.2
                  | inr hmem =>
                    have hK₁K'before :=
                      (List.pairwise_cons.mp (List.pairwise_cons.mp hpb₂).2).1 K' hmem
                    cases hK₁K'before with
                    | inl hlt =>
                      exact not_mem_of_lt_lo (calc z = K₁.lo.val := hJbK₁open.1
                        _ ≤ K₁.hi.val := K₁.le_lo_hi
                        _ < K'.lo.val := hlt)
                    | inr heq =>
                      rcases lt_or_eq_of_le
                          ((le_of_eq hJbK₁open.1).trans (K₁.le_lo_hi.trans_eq heq.1))
                          with hlt | heqz
                      · exact not_mem_of_lt_lo hlt
                      · exact not_mem_of_eq_lo_open heqz heq.2.2
                -- z ∉ ⋃ K ∈ J :: tl'
                have hznotL₂ : z ∉ ⋃ K ∈ J :: K₁ :: tl'', K.toSet := by
                  simp only [Set.mem_iUnion]
                  rintro ⟨K', hK', hzK'⟩
                  cases List.mem_cons.mp hK' with
                  | inl h => exact hznotJ (h ▸ hzK')
                  | inr h => exact hznotK' K' h hzK'
                -- But z ∈ I.toSet ⊆ ⋃ K ∈ I :: tl = ⋃ K ∈ J :: tl'
                apply hznotL₂; rw [← h]
                exact Set.mem_iUnion₂.mpr ⟨_, List.mem_cons_self, hzI⟩
        -- gap_contra₂: x ∈ J.toSet ∧ K ∈ tl ∧ x ∈ K.toSet → False
        have gap_contra₂ : ∀ x : α, x ∈ J.toSet → ∀ K ∈ tl, x ∈ K.toSet → False := by
          intro x hxJ K hKtl hxK
          have hIbK := (List.pairwise_cons.mp hpb₁).1 K hKtl
          obtain ⟨y, hyI⟩ := Interval.toSet_not_empty I
          have hyL₂ : y ∈ ⋃ L ∈ J :: tl', L.toSet := by
            have : y ∈ ⋃ L ∈ I :: tl, L.toSet :=
              Set.mem_iUnion₂.mpr ⟨I, List.mem_cons_self, hyI⟩
            rwa [← h]
          rw [Set.mem_iUnion₂] at hyL₂
          obtain ⟨L, hLconsJ, hyL⟩ := hyL₂
          cases List.mem_cons.mp hLconsJ with
          | inr hLtl' =>
            have hJbL := (List.pairwise_cons.mp hpb₂).1 L hLtl'
            have hJhiLlo : J.hi.val ≤ L.lo.val := by
              cases hJbL with
              | inl h => exact h.le
              | inr h => exact le_of_eq h.1
            have hLloY : L.lo.val ≤ y := by
              simp only [Interval.mem, Endpoint.above] at hyL
              split_ifs at hyL with hc
              · exact hyL.1
              · exact hyL.1.le
            have hxJhi : x ≤ J.hi.val := by
              simp only [Interval.mem, Endpoint.below] at hxJ
              split_ifs at hxJ with hc
              · exact hxJ.2
              · exact hxJ.2.le
            have hyIhi : y ≤ I.hi.val := by
              simp only [Interval.mem, Endpoint.below] at hyI
              split_ifs at hyI with hc
              · exact hyI.2
              · exact hyI.2.le
            cases hIbK with
            | inl hIhiKlo =>
              have hKloX : K.lo.val ≤ x := by
                simp only [Interval.mem, Endpoint.above] at hxK
                split_ifs at hxK with hc
                · exact hxK.1
                · exact hxK.1.le
              exact lt_irrefl x (lt_of_le_of_lt
                (le_trans hxJhi (le_trans hJhiLlo (le_trans hLloY hyIhi)))
                (lt_of_lt_of_le hIhiKlo hKloX))
            | inr hIbKopen =>
              have hKloX : K.lo.val < x := by
                simp only [Interval.mem, Endpoint.above, hIbKopen.2.2] at hxK
                exact hxK.1
              exact lt_irrefl x (lt_of_le_of_lt
                (le_trans hxJhi (le_trans hJhiLlo (le_trans hLloY (hIbKopen.1 ▸ hyIhi))))
                hKloX)
          | inl hLJ =>
            subst hLJ
            cases tl with
            | nil => exact absurd hKtl List.not_mem_nil
            | cons K₁ tl'' =>
              have hIbK₁ := (List.pairwise_cons.mp hpb₁).1 K₁ List.mem_cons_self
              have hK₁loKlo : K₁.lo.val ≤ K.lo.val := by
                cases List.mem_cons.mp hKtl with
                | inl h => rw [h]
                | inr h =>
                  have := Interval.le_of_before
                    ((List.pairwise_cons.mp (List.pairwise_cons.mp hpb₁).2).1 K h)
                  simp [(· ≤ ·)] at this; exact this.1
              have hxKlo : K₁.lo.val ≤ x := by
                have : K.lo.val ≤ x := by
                  simp only [Interval.mem, Endpoint.above] at hxK
                  split_ifs at hxK with hc
                  · exact hxK.1
                  · exact hxK.1.le
                exact le_trans hK₁loKlo this
              have hyIhi : y ≤ I.hi.val := by
                simp only [Interval.mem, Endpoint.below] at hyI
                split_ifs at hyI with hc
                · exact hyI.2
                · exact hyI.2.le
              have hK₁loAll : ∀ K' ∈ (K₁ :: tl''), K₁.lo.val ≤ K'.lo.val := by
                intro K' hK'
                cases List.mem_cons.mp hK' with
                | inl h => rw [h]
                | inr h =>
                  have := Interval.le_of_before
                    ((List.pairwise_cons.mp (List.pairwise_cons.mp hpb₁).2).1 K' h)
                  simp [(· ≤ ·)] at this; exact this.1
              cases hIbK₁ with
              | inl hIhiK₁lo =>
                obtain ⟨z, hz1, hz2⟩ := exists_between hIhiK₁lo
                have hyz : y < z := lt_of_le_of_lt hyIhi hz1
                have hzx : z < x := lt_of_lt_of_le hz2 hxKlo
                have hzJ := interval_mem_between hyL hxJ hyz hzx
                have hznotI : z ∉ I.toSet := by
                  simp only [Interval.mem, Endpoint.below]
                  intro ⟨_, hzhi⟩
                  split_ifs at hzhi with hc
                  · exact absurd hz1 (not_lt.mpr hzhi)
                  · exact absurd hz1 (not_lt.mpr hzhi.le)
                have hznotK' : ∀ K' ∈ (K₁ :: tl''), z ∉ K'.toSet := by
                  intro K' hK'
                  exact not_mem_of_lt_lo (lt_of_lt_of_le hz2 (hK₁loAll K' hK'))
                have hznotL₁ : z ∉ ⋃ K ∈ I :: K₁ :: tl'', K.toSet := by
                  simp only [Set.mem_iUnion]
                  rintro ⟨K', hK', hzK'⟩
                  cases List.mem_cons.mp hK' with
                  | inl h => exact hznotI (h ▸ hzK')
                  | inr h => exact hznotK' K' h hzK'
                -- But z ∈ J.toSet ⊆ ⋃ K ∈ J :: tl' = ⋃ K ∈ I :: tl
                apply hznotL₁; rw [h]
                exact Set.mem_iUnion₂.mpr ⟨_, List.mem_cons_self, hzJ⟩
              | inr hIbK₁open =>
                set z := I.hi.val
                have hyz : y < z := by
                  simp only [Interval.mem, Endpoint.below, hIbK₁open.2.1] at hyI
                  exact hyI.2
                have hzx : z < x := by
                  have hzK₁lo : z = K₁.lo.val := hIbK₁open.1
                  rcases lt_or_eq_of_le (hzK₁lo ▸ hxKlo) with hlt | heqx
                  · exact hlt
                  · exfalso
                    cases List.mem_cons.mp hKtl with
                    | inl hKK₁ =>
                      rw [hKK₁] at hxK
                      simp only [Interval.mem, Endpoint.above, hIbK₁open.2.2] at hxK
                      exact absurd (hzK₁lo.symm.trans heqx ▸ hxK.1) (lt_irrefl x)
                    | inr hKtl'' =>
                      have hK₁K := (List.pairwise_cons.mp (List.pairwise_cons.mp hpb₁).2).1 K hKtl''
                      have hKloX : K.lo.val ≤ x := by
                        simp only [Interval.mem, Endpoint.above] at hxK
                        split_ifs at hxK with hc
                        · exact hxK.1
                        · exact hxK.1.le
                      have hKloZ : K.lo.val = z :=
                        le_antisymm (heqx ▸ hKloX)
                                    (hzK₁lo ▸ hK₁loAll K (List.mem_cons_of_mem K₁ hKtl''))
                      cases hK₁K with
                      | inl hlt =>
                        exact lt_irrefl K₁.lo.val
                          (lt_of_le_of_lt K₁.le_lo_hi (hlt.trans_eq (hKloZ.trans hzK₁lo)))
                      | inr heq =>
                        have : K₁.hi.val = z := heq.1.trans hKloZ
                        cases K₁.wf with
                        | inl h' =>
                          exact lt_irrefl K₁.lo.val (h'.trans_eq (this.trans hzK₁lo))
                        | inr h' => exact absurd h'.2.2 heq.2.1
                have hzJ := interval_mem_between hyL hxJ hyz hzx
                have hznotI : z ∉ I.toSet := not_mem_of_eq_hi_open rfl hIbK₁open.2.1
                have hznotK' : ∀ K' ∈ (K₁ :: tl''), z ∉ K'.toSet := by
                  intro K' hK'
                  cases List.mem_cons.mp hK' with
                  | inl h => exact h ▸ not_mem_of_eq_lo_open hIbK₁open.1 hIbK₁open.2.2
                  | inr hmem =>
                    have hK₁K'before :=
                      (List.pairwise_cons.mp (List.pairwise_cons.mp hpb₁).2).1 K' hmem
                    cases hK₁K'before with
                    | inl hlt =>
                      exact not_mem_of_lt_lo (calc z = K₁.lo.val := hIbK₁open.1
                        _ ≤ K₁.hi.val := K₁.le_lo_hi
                        _ < K'.lo.val := hlt)
                    | inr heq =>
                      rcases lt_or_eq_of_le
                          ((le_of_eq hIbK₁open.1).trans (K₁.le_lo_hi.trans_eq heq.1))
                          with hlt | heqz
                      · exact not_mem_of_lt_lo hlt
                      · exact not_mem_of_eq_lo_open heqz heq.2.2
                have hznotL₁ : z ∉ ⋃ K ∈ I :: K₁ :: tl'', K.toSet := by
                  simp only [Set.mem_iUnion]
                  rintro ⟨K', hK', hzK'⟩
                  cases List.mem_cons.mp hK' with
                  | inl h => exact hznotI (h ▸ hzK')
                  | inr h => exact hznotK' K' h hzK'
                -- But z ∈ J.toSet ⊆ ⋃ K ∈ J :: tl' = ⋃ K ∈ I :: tl
                apply hznotL₁; rw [h]
                exact Set.mem_iUnion₂.mpr ⟨_, List.mem_cons_self, hzJ⟩
        -- I.toSet = J.toSet using both gap arguments
        have hIJeq : I.toSet = J.toSet := by
          ext x; constructor
          · intro hxI
            have hx : x ∈ ⋃ L ∈ J :: tl', L.toSet := by
              rw [← h]; exact Set.mem_iUnion₂.mpr ⟨I, List.mem_cons_self, hxI⟩
            rw [Set.mem_iUnion₂] at hx
            obtain ⟨L, hLcons, hxL⟩ := hx
            cases List.mem_cons.mp hLcons with
            | inl hLJ => exact hLJ ▸ hxL
            | inr hLtl' => exact False.elim (gap_contra x hxI L hLtl' hxL)
          · intro hxJ
            have hx : x ∈ ⋃ L ∈ I :: tl, L.toSet := by
              rw [h]; exact Set.mem_iUnion₂.mpr ⟨J, List.mem_cons_self, hxJ⟩
            rw [Set.mem_iUnion₂] at hx
            obtain ⟨L, hLcons, hxL⟩ := hx
            cases List.mem_cons.mp hLcons with
            | inl hLI => exact hLI ▸ hxL
            | inr hLtl => exact False.elim (gap_contra₂ x hxJ L hLtl hxL)
        have hIJeq': I = J := Interval.ext_toSet hIJeq
        rw[hIJeq']
        simp
        apply ihtl
        ext x
        apply Iff.intro
        . intro hxtl
          apply Set.mem_iUnion₂.mp at hxtl
          rcases hxtl with ⟨K, ⟨hK, hxK⟩⟩
          have hx : x ∈ ⋃ K' ∈ I :: tl, K'.toSet :=
            Set.mem_iUnion₂.mpr ⟨K, List.mem_cons.mpr (Or.inr hK), hxK⟩
          rw[List.pairwise_cons] at hdis₁
          have hdisjK : I.disjoint K := hdis₁.1 K hK
          rw[hIJeq'] at hdisjK
          rw[h] at hx
          rw[Set.mem_iUnion₂] at hx
          obtain ⟨K', hK'mem, hxK'⟩ := hx
          cases List.mem_cons.mp hK'mem with
          | inl hK'J =>
            exact absurd (hK'J ▸ hxK') (Interval.not_mem_of_disjoint_right hdisjK x hxK)
          | inr hK'tl' =>
            exact Set.mem_iUnion₂.mpr ⟨K', hK'tl', hxK'⟩
        . intro hxtl'
          apply Set.mem_iUnion₂.mp at hxtl'
          rcases hxtl' with ⟨K, ⟨hK, hxK⟩⟩
          have hx : x ∈ ⋃ K' ∈ J :: tl', K'.toSet :=
            Set.mem_iUnion₂.mpr ⟨K, List.mem_cons.mpr (Or.inr hK), hxK⟩
          rw[List.pairwise_cons] at hdis₂
          have hdisjK : J.disjoint K := hdis₂.1 K hK
          rw[Eq.symm hIJeq'] at hdisjK
          rw[Eq.symm h] at hx
          rw[Set.mem_iUnion₂] at hx
          obtain ⟨K', hK'mem, hxK'⟩ := hx
          cases List.mem_cons.mp hK'mem with
          | inl hK'I =>
            exact absurd (hK'I ▸ hxK') (Interval.not_mem_of_disjoint_right hdisjK x hxK)
          | inr hK'tl =>
            exact Set.mem_iUnion₂.mpr ⟨K', hK'tl, hxK'⟩

theorem ext [LinearOrder α] (U V : IntervalUnion α)
  (h : U.intervals = V.intervals) : U = V := by
  cases U
  cases V
  simp at h
  cases h
  simp

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
        exact Set.mem_iUnion₂.mpr ⟨I, h.1, h.2⟩

/-- Merge two overlapping or adjacent intervals into one. -/
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
                exact lt_of_lt_of_le (lt_of_le_of_ne h₁.1 (Ne.symm (by simpa [hJc] using h₁.2))) hI

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
                exact lt_of_le_of_lt hI (lt_of_le_of_ne h₂.1 (Ne.symm (by simpa [hJc] using h₂.2)))

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


/-- Insert an interval into a sorted disjoint list, merging with any overlapping
or adjacent intervals. -/
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

private lemma before_merge [LinearOrder α] {I J K : Interval α}
    (hnot : ¬ (I.before J ∨ J.before I))
    (hKI : K.before I) (hKJ : K.before J) : K.before (merge I J hnot) := by
  have hlo : (merge I J hnot).lo = Endpoint.minLo I.lo J.lo := rfl
  unfold Interval.before at *
  rcases Endpoint.minLo_or I.lo J.lo with hm | hm
  · rwa [hlo, hm]
  · rwa [hlo, hm]

private lemma insertMergeList_preserves_before [LinearOrder α] {I J : Interval α}
    {L : List (Interval α)} :
    J.before I → (∀ K ∈ L, J.before K) → ∀ K ∈ insertMergeList I L, J.before K := by
  intro hJI hJL
  induction L generalizing I with
  | nil => simp [insertMergeList]; exact hJI
  | cons M tl ih =>
    intro K
    unfold insertMergeList
    have hJtl : ∀ K' ∈ tl, J.before K' :=
      fun K' hK' => hJL K' (List.mem_cons_of_mem M hK')
    by_cases hIM : I.before M <;> simp [hIM]
    · by_cases hKI : K = I <;> simp [hKI]
      · exact hJI
      · by_cases hKM : K = M <;> simp [hKM]
        · exact hJL M List.mem_cons_self
        · intro hK
          exact hJL K (List.mem_cons_of_mem M hK)
    · by_cases hMI : M.before I <;> simp [hMI]
      · by_cases hKM : K = M <;> simp [hKM]
        · exact hJL M List.mem_cons_self
        · exact ih hJI hJtl K
      · exact ih (before_merge (not_or_intro hIM hMI) hJI (hJL M List.mem_cons_self)) hJtl K

lemma insertMergeList_preserves_pairwise_before [LinearOrder α] (I : Interval α) :
  ∀ {l : List (Interval α)}, l.Pairwise Interval.before →
    (insertMergeList I l).Pairwise Interval.before := by
  intro l
  induction l generalizing I with
  | nil => simp[insertMergeList]
  | cons J tl ih =>
    intro hs
    rw[List.pairwise_cons] at hs
    unfold insertMergeList
    by_cases hIJ: I.before J
    · simp only [hIJ, dif_pos]
      rw[List.pairwise_cons]
      constructor
      · intro K hK
        cases List.mem_cons.mp hK with
        | inl h => exact h ▸ hIJ
        | inr h => exact Interval.before_of_before_of_le hIJ (Interval.le_of_before (hs.1 K h))
      · exact List.pairwise_cons.mpr hs
    · simp only [hIJ, dif_neg, not_false_eq_true]
      by_cases hJI: J.before I
      · simp only [hJI, dif_pos]
        rw[List.pairwise_cons]
        constructor
        · intro K hK
          exact insertMergeList_preserves_before hJI (fun K' hK' => hs.1 K' hK') K hK
        · exact ih I hs.2
      · simp only [hJI, dif_neg, not_false_eq_true]
        apply ih (merge I J (not_or_intro hIJ hJI))
        exact hs.2

lemma insertMergeList_preserves_disjoint [LinearOrder α] (I : Interval α) :
  ∀ {l : List (Interval α)}, (l.Pairwise Interval.before ∧ l.Pairwise Interval.disjoint) →
    (insertMergeList I l).Pairwise Interval.disjoint := by
  intro l
  induction l generalizing I with
  | nil => simp[insertMergeList]
  | cons J tl ih =>
    intro hs
    obtain ⟨hsbefore, hsdisjoint⟩ := hs
    rw[List.pairwise_cons] at hsbefore
    rw[List.pairwise_cons] at hsdisjoint
    unfold insertMergeList
    by_cases hIJ: I.before J <;> simp[hIJ]
    · constructor
      · constructor
        · exact Interval.disjoint_of_before hIJ
        · intro K hK
          exact Interval.disjoint_of_before
            (Interval.before_of_before_of_le hIJ (Interval.le_of_before (hsbefore.1 K hK)))
      · constructor
        · exact hsdisjoint.1
        · exact hsdisjoint.2
    · by_cases hJI: J.before I <;> simp[hJI]
      · constructor
        · intro K hK
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
            have := hsdisjoint.1 M hM (Set.singleton_subset_iff.mpr hxJ) (Set.singleton_subset_iff.mpr hxM)
            simp at this
        · exact ih I ⟨hsbefore.2, hsdisjoint.2⟩
      · apply ih (merge I J (not_or_intro hIJ hJI))
        exact ⟨hsbefore.2, hsdisjoint.2⟩

def insertMerge [LinearOrder α]
  (I: Interval α) (U: IntervalUnion α) : IntervalUnion α :=
  ⟨
    insertMergeList I U.intervals,
    insertMergeList_preserves_disjoint I ⟨U.pairwise_before, U.pairwise_disjoint⟩,
    insertMergeList_preserves_pairwise_before I U.pairwise_before
  ⟩

lemma mem_insertMerge [LinearOrder α] (I : Interval α) (U : IntervalUnion α) (x : α) :
    x ∈ (insertMerge I U).toSet ↔ x ∈ I.toSet ∨ x ∈ U.toSet := by
  simp only [mem, insertMerge]
  exact mem_insertMergeList I U.intervals x

private lemma mem_foldl_insertMerge [LinearOrder α]
    (L : List (Interval α)) (U : IntervalUnion α) (x : α) :
    x ∈ (L.foldl (fun acc I => insertMerge I acc) U).toSet ↔
    x ∈ U.toSet ∨ ∃ I ∈ L, x ∈ I.toSet := by
  induction L generalizing U with
  | nil => simp
  | cons I tl ih =>
    simp only [List.foldl_cons]
    rw [ih (insertMerge I U), mem_insertMerge I U x]
    constructor
    · rintro ((hI | hU) | ⟨J, hJ, hxJ⟩)
      · exact Or.inr ⟨I, List.mem_cons_self, hI⟩
      · exact Or.inl hU
      · exact Or.inr ⟨J, List.mem_cons.mpr (Or.inr hJ), hxJ⟩
    · rintro (hU | ⟨J, hJ, hxJ⟩)
      · exact Or.inl (Or.inr hU)
      · cases List.mem_cons.mp hJ with
        | inl h => exact Or.inl (Or.inl (h ▸ hxJ))
        | inr h => exact Or.inr ⟨J, h, hxJ⟩

/-- Union of two interval unions (the semiring addition). -/
def union [LinearOrder α] (U V : IntervalUnion α) : IntervalUnion α :=
  V.intervals.foldl (fun acc I => (IntervalUnion.insertMerge I acc)) U

lemma mem_union [LinearOrder α] (U V : IntervalUnion α) :
    ∀ x, x ∈ (U.union V).toSet ↔ x ∈ U.toSet ∨ x ∈ V.toSet := by
  intro x
  unfold union
  rw [mem_foldl_insertMerge, mem x V]

/-- Intersection of two interval unions (the semiring multiplication). -/
def inter [LinearOrder α] (U V : IntervalUnion α) : IntervalUnion α :=
  let pieces := U.intervals.flatMap (fun I => V.intervals.flatMap (fun J => I.inter J))
  pieces.foldl (fun acc I => insertMerge I acc) ⟨[], by simp, by simp⟩

lemma mem_inter [LinearOrder α] (U V : IntervalUnion α) (x : α) :
    x ∈ (U.inter V).toSet ↔ x ∈ U.toSet ∧ x ∈ V.toSet := by
  simp only [inter, mem_foldl_insertMerge, mem x ⟨[], by simp, by simp⟩,
             List.not_mem_nil]
  simp only [mem x U, mem x V]
  constructor
  · rintro (⟨⟩ | ⟨K, hK, hxK⟩)
    · simp at *
    · simp only [List.mem_flatMap] at hK
      obtain ⟨I, hI, J, hJ, hIJ⟩ := hK
      have := (Interval.mem_inter I J x).mp ⟨K, hIJ, hxK⟩
      exact ⟨⟨I, hI, this.1⟩, ⟨J, hJ, this.2⟩⟩
  · rintro ⟨⟨I, hI, hxI⟩, ⟨J, hJ, hxJ⟩⟩
    right
    have := (Interval.mem_inter I J x).mpr ⟨hxI, hxJ⟩
    obtain ⟨K, hK, hxK⟩ := this
    exact ⟨K, by simp [List.mem_flatMap]; exact ⟨I, hI, J, hJ, hK⟩, hxK⟩

/-- Set difference of two interval unions (the semiring monus). -/
def diff [LinearOrder α] (U V : IntervalUnion α) : IntervalUnion α :=
  let pieces := U.intervals.flatMap (fun I =>
    V.intervals.foldl (fun L J => L.flatMap (fun I' => I'.diff J)) [I])
  pieces.foldl (fun acc I => insertMerge I acc) ⟨[], by simp, by simp⟩

-- Helper: iteratively subtracting a list of intervals from a list preserves membership
private lemma mem_foldl_diff [LinearOrder α]
    (L : List (Interval α)) (V : List (Interval α)) (x : α) :
    (∃ K ∈ V.foldl (fun acc J => acc.flatMap (fun I' => I'.diff J)) L, x ∈ K.toSet) ↔
    (∃ I ∈ L, x ∈ I.toSet) ∧ ∀ J ∈ V, x ∉ J.toSet := by
  induction V generalizing L with
  | nil => simp
  | cons J tl ih =>
    simp only [List.foldl_cons]
    rw [ih (L.flatMap (fun I' => I'.diff J))]
    constructor
    · rintro ⟨⟨I', hI', hxI'⟩, htl⟩
      simp only [List.mem_flatMap] at hI'
      obtain ⟨I, hI, hKI⟩ := hI'
      have := (Interval.mem_diff I J x).mp ⟨I', hKI, hxI'⟩
      exact ⟨⟨I, hI, this.1⟩, fun K hK => by
        simp only [List.mem_cons] at hK
        cases hK with
        | inl h => rw [h]; exact this.2
        | inr h => exact htl K h⟩
    · rintro ⟨⟨I, hI, hxI⟩, hnotin⟩
      refine ⟨?_, fun K hK => hnotin K (List.mem_cons_of_mem J hK)⟩
      simp only [List.mem_flatMap]
      have hnotJ := hnotin J List.mem_cons_self
      obtain ⟨K, hK, hxK⟩ := (Interval.mem_diff I J x).mpr ⟨hxI, hnotJ⟩
      exact ⟨K, ⟨I, hI, hK⟩, hxK⟩

lemma mem_diff [LinearOrder α] (U V : IntervalUnion α) (x : α) :
    x ∈ (U.diff V).toSet ↔ x ∈ U.toSet ∧ x ∉ V.toSet := by
  simp only [diff]
  rw [mem_foldl_insertMerge]
  simp only [mem x (⟨[], by simp, by simp⟩ : IntervalUnion α), List.not_mem_nil,
             false_and, exists_false, false_or]
  simp only [List.mem_flatMap]
  rw [mem x U, mem x V]
  constructor
  · rintro ⟨K, ⟨I, hI, hK⟩, hxK⟩
    obtain ⟨⟨_, hI', hxI'⟩, hnotV⟩ := (mem_foldl_diff [I] V.intervals x).mp ⟨K, hK, hxK⟩
    simp only [List.mem_singleton] at hI'
    rw [hI'] at hxI'
    exact ⟨⟨I, hI, hxI'⟩, fun ⟨J, hJ, hxJ⟩ => hnotV J hJ hxJ⟩
  · rintro ⟨⟨I, hI, hxI⟩, hnotV⟩
    have hnotV' : ∀ J ∈ V.intervals, x ∉ J.toSet :=
      fun J hJ hxJ => hnotV ⟨J, hJ, hxJ⟩
    obtain ⟨K, hK, hxK⟩ := (mem_foldl_diff [I] V.intervals x).mpr
      ⟨⟨I, List.mem_singleton.mpr rfl, hxI⟩, hnotV'⟩
    exact ⟨K, ⟨I, hI, hK⟩, hxK⟩

end IntervalUnion

open IntervalUnion

variable {α: Type} [LinearOrder α]

instance : Zero (IntervalUnion α) := ⟨[], by simp, by simp⟩
instance [BoundedOrder α] : One  (IntervalUnion α) := ⟨[⟨⟨⊥,⊤⟩,⟨⊤,⊤⟩,by simp[lt_or_eq_of_le] ⟩], by simp, by simp⟩

instance : Add  (IntervalUnion α) where
  add U V := U.union V

instance : Mul  (IntervalUnion α) where
  mul U V := U.inter V

instance : Sub  (IntervalUnion α) where
  sub U V := U.diff V

-- `+` unfolds to `union`, `*` to `inter`, `-` to `diff`
private lemma add_eq_union (U V : IntervalUnion α) : U + V = U.union V := rfl
private lemma mul_eq_inter (U V : IntervalUnion α) : U * V = U.inter V := rfl
private lemma sub_eq_diff  (U V : IntervalUnion α) : U - V = U.diff  V := rfl
@[simp]
private lemma zero_intervals : (0 : IntervalUnion α).intervals = [] := rfl

instance [DenselyOrdered α] : AddMonoid (IntervalUnion α) where
  add_assoc := by
    intro a b c; apply ext_toSet; ext x
    rw [add_eq_union, add_eq_union, add_eq_union, add_eq_union,
        mem_union, mem_union, mem_union, mem_union]
    tauto
  zero_add := by
    intro U; apply ext_toSet; ext x
    rw [add_eq_union, mem_union]
    simp [toSet]
  add_zero := fun _ => rfl
  nsmul := nsmulRec

-- Helper: `(1 : IntervalUnion α).toSet = Set.univ`
private lemma one_toSet [BoundedOrder α] : (1 : IntervalUnion α).toSet = Set.univ := by
  apply Set.eq_univ_of_forall; intro x
  rw [mem]
  -- By proof irrelevance any wf proof is definitionally equal to the one in the One instance
  refine ⟨⟨⟨⊥, ⊤⟩, ⟨⊤, ⊤⟩, by simp[lt_or_eq_of_le]⟩, List.mem_cons_self, ?_⟩
  simp [Interval.toSet, Endpoint.above, Endpoint.below]

-- Helper: `(0 : IntervalUnion α).toSet = ∅`
private lemma zero_toSet : (0 : IntervalUnion α).toSet = ∅ := by
  simp [IntervalUnion.toSet]

instance [DenselyOrdered α] [BoundedOrder α] : CommSemiring (IntervalUnion α) where
  add_comm := by
    intro a b; apply ext_toSet; ext x
    rw [add_eq_union, add_eq_union, mem_union, mem_union]; tauto
  mul_assoc := by
    intro a b c; apply ext_toSet; ext x
    rw [mul_eq_inter, mul_eq_inter, mul_eq_inter, mul_eq_inter,
        mem_inter, mem_inter, mem_inter, mem_inter]
    tauto
  mul_comm := by
    intro a b; apply ext_toSet; ext x
    rw [mul_eq_inter, mul_eq_inter, mem_inter, mem_inter]; tauto
  left_distrib := by
    intro a b c; apply ext_toSet; ext x
    rw [mul_eq_inter, add_eq_union, add_eq_union, mul_eq_inter, mul_eq_inter,
        mem_inter, mem_union, mem_union, mem_inter, mem_inter]
    tauto
  right_distrib := by
    intro a b c; apply ext_toSet; ext x
    rw [add_eq_union, mul_eq_inter, add_eq_union, mul_eq_inter, mul_eq_inter,
        mem_inter, mem_union, mem_union, mem_inter, mem_inter]
    tauto
  one_mul := by
    intro a; apply ext_toSet; ext x
    rw [mul_eq_inter, mem_inter]; simp [one_toSet]
  mul_one := by
    intro a; apply ext_toSet; ext x
    rw [mul_eq_inter, mem_inter]; simp [one_toSet]
  zero_mul := by
    intro a; apply ext_toSet; ext x
    rw [mul_eq_inter, mem_inter]; simp [zero_toSet]
  mul_zero := by
    intro a; apply ext_toSet; ext x
    rw [mul_eq_inter, mem_inter]; simp [zero_toSet]
  npow := npowRec

/-- Interval unions over a dense bounded linear order form a commutative m-semiring,
with union as addition, intersection as multiplication, set inclusion as natural order,
and set difference as monus. -/
instance [DenselyOrdered α] [BoundedOrder α]: SemiringWithMonus (IntervalUnion α) where
  -- Order: set inclusion
  le U V := U.toSet ⊆ V.toSet
  le_refl _ := Set.Subset.refl _
  le_antisymm U V hUV hVU := ext_toSet U V (Set.Subset.antisymm hUV hVU)
  le_trans _ _ _ hUV hVW := Set.Subset.trans hUV hVW
  -- Ordered add monoid: union is monotone
  add_le_add_left := by
    intro a b hab c x hx
    rw [add_eq_union, mem_union] at hx ⊢
    cases hx with
    | inl ha => left; exact hab ha
    | inr hc => right; exact hc
  -- Canonically ordered: a ≤ a + b always
  le_self_add := by
    intro a b x hx
    rw [add_eq_union, mem_union]; left; exact hx
  le_add_self := by
    intro a b x hx
    rw [add_eq_union, mem_union]; right; exact hx
  -- For exists_add_of_le: if a ≤ b, take c = b - a
  -- goal is `b = a + b.diff a`, so after ext_toSet the iff is b.toSet ↔ (a + b.diff a).toSet
  exists_add_of_le := by
    intro a b hab
    use b.diff a
    apply ext_toSet; ext x
    rw [add_eq_union, mem_union, mem_diff]
    constructor
    · intro hxb
      by_cases hxa : x ∈ a.toSet
      · left; exact hxa
      · right; exact ⟨hxb, hxa⟩
    · rintro (hxa | ⟨hxb, _⟩)
      · exact hab hxa
      · exact hxb
  -- Monus: A \ B ⊆ C ↔ A ⊆ B ∪ C
  monus_spec := by
    intro a b c
    constructor
    · intro h x hxa
      rw [add_eq_union, mem_union]
      by_cases hxb : x ∈ b.toSet
      · left; exact hxb
      · right; exact h ((IntervalUnion.mem_diff a b x).mpr ⟨hxa, hxb⟩)
    · intro h x hx
      have ⟨hxa, hxnb⟩ := (IntervalUnion.mem_diff a b x).mp hx
      have h' : a.toSet ⊆ (b.union c).toSet := h
      rcases (mem_union b c x).mp (h' hxa) with hxb | hxc
      · exact absurd hxb hxnb
      · exact hxc

  /- δ matches ProvSQL's `IntervalUnion::delta`: the identity. -/
  delta := id
  delta_zero := rfl
  delta_natCast_pos :=
    let habs : absorptive (IntervalUnion α) := fun a => by
      apply ext_toSet; ext x
      rw [add_eq_union, mem_union]
      simp [one_toSet]
    fun hn => delta_natCast_pos_id (idempotent_of_absorptive habs) hn
  delta_regrouping := delta_regrouping_id

instance [DenselyOrdered α] [BoundedOrder α] : CommSemiringWithMonus (IntervalUnion α) where
  mul_comm := mul_comm

/-- The interval-union semiring is absorptive: the multiplicative identity (the whole
space) absorbs any element under addition (union). -/
theorem IntervalUnion.absorptive [DenselyOrdered α] [BoundedOrder α] :
    absorptive (IntervalUnion α) := by
  intro a
  apply ext_toSet; ext x
  rw [add_eq_union, mem_union]
  simp [one_toSet]

/-- Left-distributivity of multiplication (intersection) over monus (set difference):
`A ∩ (B \ C) = (A ∩ B) \ (A ∩ C)`. -/
theorem IntervalUnion.mul_sub_left_distributive [DenselyOrdered α] [BoundedOrder α] :
    mul_sub_left_distributive (IntervalUnion α) := by
  intro a b c
  apply ext_toSet; ext x
  simp only [mul_eq_inter, sub_eq_diff, mem_inter, mem_diff]
  tauto

/-- The interval-union semiring is idempotent: `a + a = a` (derived from absorptivity). -/
theorem IntervalUnion.idempotent [DenselyOrdered α] [BoundedOrder α] :
    idempotent (IntervalUnion α) :=
  idempotent_of_absorptive IntervalUnion.absorptive

instance [BoundedOrder α] : Nontrivial (IntervalUnion α) := ⟨0, 1, fun h => by
  have : (0 : IntervalUnion α).intervals = (1 : IntervalUnion α).intervals := by rw [h]
  cases this⟩

/-- The interval-union semiring has characteristic 0 in the `CharP` sense: it is
idempotent and nontrivial (the empty list differs from the singleton `[⊥,⊤]`), so
every positive natural-number cast equals `1`. -/
instance IntervalUnion.instCharPZero [DenselyOrdered α] [BoundedOrder α] :
    CharP (IntervalUnion α) 0 :=
  CharP.zero_of_idempotent IntervalUnion.idempotent

/-- The interval-union semiring over the extended reals `[-∞, +∞]`. -/
noncomputable instance : SemiringWithMonus (IntervalUnion EReal) := inferInstance
noncomputable instance : CommSemiringWithMonus (IntervalUnion EReal) := inferInstance

/-- The interval-union semiring over the extended rationals. -/
instance : SemiringWithMonus (IntervalUnion (WithBot (WithTop ℚ))) := inferInstance
instance : CommSemiringWithMonus (IntervalUnion (WithBot (WithTop ℚ))) := inferInstance

/-! ## Homomorphism from `BoolFunc Y` to `IntervalUnion`

For any assignment `ν : Y → IntervalUnion β` with `Y` finite, there is an
m-semiring homomorphism `BoolFunc Y →+* IntervalUnion β` sending each
variable to its assigned interval union.

**Construction.** For `f ∈ BoolFunc Y`, write `f` in disjunctive normal form
over the finite variable set `Y`:
`f = ⋁_σ (⋀_i var_i^{σ(i)})`, where `σ : Y → Bool` ranges over assignments
with `f σ = true` and `var_i^true = var_i`, `var_i^false = 1 - var_i`. Define
`evalBF ν f := ∑_σ (if f σ then atomIU ν σ else 0)` where
`atomIU ν σ := ∏_i (if σ i then ν i else 1 - ν i)`. This is a finite Boolean
combination of the `ν(i)`'s, hence lies in `IntervalUnion β`.

The correctness rests on the set-theoretic characterisation
`mem_atomIU_iff_sig`: `x ∈ (atomIU ν σ).toSet` iff `σ` is the ν-signature of
`x`, where the ν-signature `sigOf ν x` sends each `i` to `decide (x ∈ ν i)`.
This yields `(evalBF ν f).toSet = {x : β | f (sigOf ν x) = true}`
(`evalBF_toSet`), from which preservation of `0`, `1`, `+`, `*`, monus,
and the variable mapping all follow.

For **infinite** `Y`, no such homomorphism exists in general: the set
`{x | f(τ_x) = true}` need not be a finite union of intervals when `f`
depends non-trivially on infinitely many variables. So `Fintype Y` is
essential. -/

namespace BoolFuncHom

set_option linter.unusedSectionVars false

open Classical

variable {β : Type} [LinearOrder β] [DenselyOrdered β] [BoundedOrder β]
variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- toSet of `+`: union of toSets. -/
private lemma add_toSet (U V : IntervalUnion β) : (U + V).toSet = U.toSet ∪ V.toSet := by
  apply Set.ext; intro x
  rw [add_eq_union, IntervalUnion.mem_union]; rfl

/-- toSet of `*`: intersection of toSets. -/
private lemma mul_toSet (U V : IntervalUnion β) : (U * V).toSet = U.toSet ∩ V.toSet := by
  apply Set.ext; intro x
  rw [mul_eq_inter, IntervalUnion.mem_inter]; rfl

/-- toSet of `-`: set difference. -/
private lemma sub_toSet (U V : IntervalUnion β) : (U - V).toSet = U.toSet \ V.toSet := by
  apply Set.ext; intro x
  rw [sub_eq_diff, IntervalUnion.mem_diff]; rfl

/-- toSet of a `Finset.sum` is the union of toSets. -/
private lemma sum_toSet {ι : Type _} (s : Finset ι) (f : ι → IntervalUnion β) :
    (∑ i ∈ s, f i).toSet = ⋃ i ∈ s, (f i).toSet := by
  induction s using Finset.induction_on with
  | empty => simp [IntervalUnion.toSet]
  | insert _ _ hi ih =>
    rw [Finset.sum_insert hi, add_toSet, ih, Finset.set_biUnion_insert]

/-- toSet of a `Finset.prod` is the intersection of toSets. -/
private lemma prod_toSet {ι : Type _} (s : Finset ι) (f : ι → IntervalUnion β) :
    (∏ i ∈ s, f i).toSet = ⋂ i ∈ s, (f i).toSet := by
  induction s using Finset.induction_on with
  | empty => simp [one_toSet]
  | insert _ _ hi ih =>
    rw [Finset.prod_insert hi, mul_toSet, ih, Finset.set_biInter_insert]

/-- The atom for a Boolean signature: the IntervalUnion of those `x : β`
whose membership in each `ν i` matches `σ i`. -/
private def atomIU (ν : Y → IntervalUnion β) (σ : Y → Bool) : IntervalUnion β :=
  ∏ i, if σ i then ν i else 1 - ν i

/-- toSet of `1 - ν i`: complement of `ν i.toSet`. -/
private lemma sub_one_toSet (a : IntervalUnion β) :
    (1 - a).toSet = (a.toSet)ᶜ := by
  rw [sub_eq_diff]
  ext x
  rw [IntervalUnion.mem_diff]
  simp [one_toSet]

/-- Membership in `atomIU ν σ`: the ν-signature of `x` equals `σ`. -/
private lemma mem_atomIU_toSet (ν : Y → IntervalUnion β) (σ : Y → Bool) (x : β) :
    x ∈ (atomIU ν σ).toSet ↔ ∀ i, (x ∈ (ν i).toSet ↔ σ i = true) := by
  rw [atomIU, prod_toSet]
  simp only [Set.mem_iInter, Finset.mem_univ, forall_const]
  refine forall_congr' fun i => ?_
  by_cases hσ : σ i = true
  · rw [if_pos hσ]
    simp [hσ]
  · rw [if_neg hσ, sub_one_toSet, Set.mem_compl_iff]
    simp [hσ]

/-- The canonical ν-signature of a point `x : β`: the Bool-valued function on `Y`
sending `i` to `true` iff `x` belongs to `ν i`. Noncomputable because membership
in `(ν i).toSet` is decided classically. -/
private noncomputable def sigOf (ν : Y → IntervalUnion β) (x : β) : Y → Bool :=
  fun i => decide (x ∈ (ν i).toSet)

/-- `x` belongs to `atomIU ν σ` iff `σ` is the ν-signature of `x`. -/
private lemma mem_atomIU_iff_sig (ν : Y → IntervalUnion β) (σ : Y → Bool) (x : β) :
    x ∈ (atomIU ν σ).toSet ↔ sigOf ν x = σ := by
  rw [mem_atomIU_toSet, funext_iff]
  refine forall_congr' fun i => ?_
  rw [sigOf]
  cases σ i <;> simp

/-- The DNF evaluation of a Boolean function: the IntervalUnion whose toSet is
the set of `x : β` such that `f` holds on `x`'s ν-signature. -/
private noncomputable def evalBF (ν : Y → IntervalUnion β) (f : BoolFunc Y) : IntervalUnion β :=
  ∑ σ : Y → Bool, if f σ then atomIU ν σ else 0

/-- toSet characterisation of `evalBF`. -/
private lemma evalBF_toSet (ν : Y → IntervalUnion β) (f : BoolFunc Y) :
    (evalBF ν f).toSet = {x : β | f (sigOf ν x) = true} := by
  rw [evalBF, sum_toSet]
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, _, hxσ⟩
    by_cases hfσ : f σ = true
    · rw [if_pos hfσ, mem_atomIU_iff_sig] at hxσ
      rw [hxσ]; exact hfσ
    · rw [if_neg hfσ, zero_toSet] at hxσ
      exact absurd hxσ (Set.notMem_empty _)
  · intro hf
    refine ⟨sigOf ν x, Finset.mem_univ _, ?_⟩
    rw [if_pos hf, mem_atomIU_iff_sig]

/-- `evalBF` sends `0` to `0`. -/
private lemma evalBF_zero (ν : Y → IntervalUnion β) : evalBF ν 0 = 0 := by
  apply ext_toSet
  rw [evalBF_toSet, zero_toSet]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  show ¬ (false = true)
  decide

/-- `evalBF` sends `1` to `1`. -/
private lemma evalBF_one (ν : Y → IntervalUnion β) : evalBF ν 1 = 1 := by
  apply ext_toSet
  rw [evalBF_toSet, one_toSet]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  rfl

/-- `evalBF` preserves addition. -/
private lemma evalBF_add (ν : Y → IntervalUnion β) (f g : BoolFunc Y) :
    evalBF ν (f + g) = evalBF ν f + evalBF ν g := by
  apply ext_toSet
  rw [add_toSet, evalBF_toSet, evalBF_toSet, evalBF_toSet]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union]
  show ((f (sigOf ν x)) || (g (sigOf ν x))) = true ↔ _
  simp [Bool.or_eq_true]

/-- `evalBF` preserves multiplication. -/
private lemma evalBF_mul (ν : Y → IntervalUnion β) (f g : BoolFunc Y) :
    evalBF ν (f * g) = evalBF ν f * evalBF ν g := by
  apply ext_toSet
  rw [mul_toSet, evalBF_toSet, evalBF_toSet, evalBF_toSet]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  show ((f (sigOf ν x)) && (g (sigOf ν x))) = true ↔ _
  simp [Bool.and_eq_true]

/-- `evalBF` preserves monus. -/
private lemma evalBF_sub (ν : Y → IntervalUnion β) (f g : BoolFunc Y) :
    evalBF ν (f - g) = evalBF ν f - evalBF ν g := by
  apply ext_toSet
  rw [sub_toSet, evalBF_toSet, evalBF_toSet, evalBF_toSet]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  show ((f (sigOf ν x)) && !(g (sigOf ν x))) = true ↔ _
  rw [Bool.and_eq_true]
  refine and_congr_right (fun _ => ?_)
  cases g (sigOf ν x) <;> simp

/-- `evalBF` sends the i-th variable to `ν i`. -/
private lemma evalBF_var (ν : Y → IntervalUnion β) (i : Y) :
    evalBF ν (BoolFunc.var i) = ν i := by
  apply ext_toSet
  rw [evalBF_toSet]
  ext x
  simp only [Set.mem_setOf_eq]
  show sigOf ν x i = true ↔ _
  rw [sigOf, Bool.decide_iff]

end BoolFuncHom

open BoolFuncHom

/-- For any assignment `ν : Y → IntervalUnion β` with `Y` finite, there is an
m-semiring homomorphism `BoolFunc Y →+* IntervalUnion β` sending each
variable `BoolFunc.var i` to `ν i`. The homomorphism is the DNF evaluation
`evalBF`: `f ↦ ∑_σ (if f σ then atomIU ν σ else 0)`. -/
theorem IntervalUnion.homomorphism_from_BoolFunc
    (β : Type) [LinearOrder β] [DenselyOrdered β] [BoundedOrder β]
    (Y : Type) [Fintype Y] [DecidableEq Y] :
    ∀ ν : Y → IntervalUnion β,
      ∃ h : SemiringWithMonusHom (BoolFunc Y) (IntervalUnion β),
        ∀ i : Y, h (BoolFunc.var i) = ν i := by
  intro ν
  refine ⟨{
    toFun := evalBF ν
    map_zero' := evalBF_zero ν
    map_one'  := evalBF_one ν
    map_add'  := evalBF_add ν
    map_mul'  := evalBF_mul ν
    map_sub   := evalBF_sub ν
  }, ?_⟩
  intro i
  exact evalBF_var ν i

/-- Specialisation of `IntervalUnion.homomorphism_from_BoolFunc` to the
extended rationals. -/
theorem IntervalUnion.homomorphism_from_BoolFunc_rat
    (Y : Type) [Fintype Y] [DecidableEq Y] :
    ∀ ν : Y → IntervalUnion (WithBot (WithTop ℚ)),
      ∃ h : SemiringWithMonusHom (BoolFunc Y) (IntervalUnion (WithBot (WithTop ℚ))),
        ∀ i : Y, h (BoolFunc.var i) = ν i :=
  IntervalUnion.homomorphism_from_BoolFunc _ Y
