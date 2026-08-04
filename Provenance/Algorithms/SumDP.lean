/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Provenance.Algorithms.CompOp

/-!
# Correctness of SUM enumeration via dynamic programming

This file formalises a subset-sum enumeration algorithm. The algorithm
enumerates the non-empty subsets `W` of a finite set of occurrences `U`
whose weighted sum `∑_{u ∈ W} t u` satisfies `(∑ t) op C` for a fixed
comparison operator `op` and constant `C : ℕ`. The main result
`sumDP_correct` shows that the output coincides with that set in the
sense of membership.

The standard imperative presentation uses an in-place `dp[j]` array
bounded by some `J` chosen per operator, with early returns for
impossible operator/constant combinations. We use the mathematically
equivalent functional formulation: `sumExact occs t j` is the list of
subsets of `occs.toFinset` with weighted sum exactly `j` (i.e., `dp[j]`
after iteration `N`), defined by direct recursion on `occs`. The six
`op`-cases and all four early-return cases collapse into a single
`flatMap` over satisfying sums in `{0, …, T}`, where
`T = occs.toFinset.sum t`. Impossible sums simply contribute empty
enumerations.

The aggregate term `t` enters as `α → ℕ`; an annotation `α_i` would be
part of the occurrence type and does not enter the sum.
-/

namespace SumDP

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Definitions -/

/-- `sumExact occs t j`: enumerate the subsets of `occs.toFinset` whose
weighted sum under `t` is exactly `j`. Mirrors the dynamic-programming
table `dp[j]` after the outer loop: every subset either omits the head
`u` (left recursion) or includes it (right recursion, requires
`t u ≤ j`). -/
def sumExact : List α → (α → ℕ) → ℕ → List (Finset α)
  | [],        _, 0     => [∅]
  | [],        _, _ + 1 => []
  | u :: rest, t, j =>
    sumExact rest t j ++
      (if t u ≤ j then (sumExact rest t (j - t u)).map (insert u) else [])

/-- `SumDP(U, t, C, op)`: top-level routine. The six operator-cases
(and the four early-return cases of a more imperative presentation)
collapse into a single `flatMap` over satisfying sums in `{0, …, T}`,
where `T` is the total weight `occs.toFinset.sum t`. -/
def sumDP (occs : List α) (t : α → ℕ) (C : ℕ) (op : CompOp) :
    List (Finset α) :=
  let T := occs.toFinset.sum t
  ((List.range (T + 1)).filter (fun j => decide (op.eval j C))).flatMap
    (fun j => (sumExact occs t j).filter (fun S => decide (S ≠ ∅)))

/-! ### Correctness lemmas -/

/-- Membership characterisation of `sumExact`. Under `occs.Nodup`,
the output enumerates exactly the subsets of `occs.toFinset` with
weighted sum equal to `j`. The Nodup hypothesis is used in the
inductive step to guarantee that the head `u` does not appear later in
`rest`, so that `insert u S'` with `S' ⊆ rest.toFinset` genuinely adds
`t u` to the sum (rather than collapsing to `S'`). -/
theorem sumExact_mem :
    ∀ (occs : List α), occs.Nodup →
    ∀ (t : α → ℕ) (j : ℕ) (S : Finset α),
      S ∈ sumExact occs t j ↔ S ⊆ occs.toFinset ∧ S.sum t = j := by
  intro occs hnodup t j
  induction occs generalizing j with
  | nil =>
    intro S
    cases j with
    | zero =>
      simp only [sumExact, List.mem_singleton, List.toFinset_nil,
        Finset.subset_empty]
      refine ⟨fun h => ⟨h, by rw [h]; simp⟩, fun ⟨h, _⟩ => h⟩
    | succ j =>
      simp only [sumExact, List.not_mem_nil, List.toFinset_nil,
        Finset.subset_empty, false_iff, not_and]
      intro h
      subst h
      simp
  | cons u rest ih =>
    intro S
    have hunodup : u ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrestnodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    -- sumExact (u :: rest) t j
    --   = sumExact rest t j ++ (if t u ≤ j then ... else [])
    simp only [sumExact, List.mem_append]
    rw [ih hrestnodup j]
    by_cases hle : t u ≤ j
    · simp only [hle, ↓reduceIte, List.mem_map]
      constructor
      · rintro (⟨hSU, hsum⟩ | ⟨S', hS'mem, hS'eq⟩)
        · refine ⟨?_, hsum⟩
          intro v hv
          have : v ∈ rest.toFinset := hSU hv
          simp at this ⊢
          exact Or.inr this
        · rw [ih hrestnodup (j - t u)] at hS'mem
          obtain ⟨hS'U, hS'sum⟩ := hS'mem
          refine ⟨?_, ?_⟩
          · rw [← hS'eq]
            intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hvS'
            · simp
            · have : v ∈ rest.toFinset := hS'U hvS'
              simp at this ⊢
              exact Or.inr this
          · rw [← hS'eq]
            have huS' : u ∉ S' := fun h => hunodup (List.mem_toFinset.mp (hS'U h))
            rw [Finset.sum_insert huS', hS'sum]
            omega
      · rintro ⟨hSU, hsum⟩
        by_cases huS : u ∈ S
        · right
          refine ⟨S.erase u, ?_, ?_⟩
          · rw [ih hrestnodup (j - t u)]
            refine ⟨?_, ?_⟩
            · intro v hv
              have hvS : v ∈ S := Finset.mem_of_mem_erase hv
              have hvne : v ≠ u := Finset.ne_of_mem_erase hv
              have : v ∈ (u :: rest).toFinset := hSU hvS
              simp at this
              rcases this with rfl | hvr
              · exact absurd rfl hvne
              · exact List.mem_toFinset.mpr hvr
            · have hadd : (S.erase u).sum t + t u = S.sum t :=
                Finset.sum_erase_add S t huS
              omega
          · exact Finset.insert_erase huS
        · left
          refine ⟨?_, hsum⟩
          intro v hv
          have : v ∈ (u :: rest).toFinset := hSU hv
          simp at this
          rcases this with rfl | hvr
          · exact absurd hv huS
          · exact List.mem_toFinset.mpr hvr
    · -- t u > j: the right branch is []
      simp only [hle, ↓reduceIte, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨hSU, hsum⟩
        refine ⟨?_, hsum⟩
        intro v hv
        have : v ∈ rest.toFinset := hSU hv
        simp at this ⊢
        exact Or.inr this
      · rintro ⟨hSU, hsum⟩
        refine ⟨?_, hsum⟩
        -- Show u ∉ S, since otherwise t u ≤ S.sum t = j, contradicting hle
        intro v hv
        have hvU : v ∈ (u :: rest).toFinset := hSU hv
        simp at hvU
        rcases hvU with rfl | hvr
        · -- v = u: but then t u ≤ S.sum t = j, contradicting ¬ (t u ≤ j)
          have : t v ≤ S.sum t := Finset.single_le_sum (f := t)
            (fun _ _ => Nat.zero_le _) hv
          rw [hsum] at this
          exact absurd this hle
        · exact List.mem_toFinset.mpr hvr

/-- The enumeration `sumExact` contains no duplicate subset. `Nodup` of
`occs` guarantees that the head `u` is absent from the subsets produced by
the recursive calls, so the `insert u` copies are pairwise distinct and
disjoint from the `u`-free part of the output. -/
theorem sumExact_nodup (occs : List α) (hnodup : occs.Nodup) (t : α → ℕ) (j : ℕ) :
    (sumExact occs t j).Nodup := by
  induction occs generalizing j with
  | nil => cases j <;> simp [sumExact]
  | cons u rest ih =>
    have hunodup : u ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrestnodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hnotmem : ∀ {j' : ℕ} {S : Finset α}, S ∈ sumExact rest t j' → u ∉ S := by
      intro j' S hS hu
      exact hunodup (List.mem_toFinset.mp
        (((sumExact_mem rest hrestnodup t j' S).mp hS).1 hu))
    simp only [sumExact]
    rw [List.nodup_append]
    refine ⟨ih hrestnodup j, ?_, ?_⟩
    · split_ifs with hle
      · refine List.Nodup.map_on ?_ (ih hrestnodup (j - t u))
        intro S₁ hS₁ S₂ hS₂ heq
        have h₁ : u ∉ S₁ := hnotmem hS₁
        have h₂ : u ∉ S₂ := hnotmem hS₂
        have : (insert u S₁).erase u = (insert u S₂).erase u := by rw [heq]
        rwa [Finset.erase_insert h₁, Finset.erase_insert h₂] at this
      · exact List.nodup_nil
    · intro S hS S' hS'
      have huS : u ∉ S := hnotmem hS
      split_ifs at hS' with hle
      · obtain ⟨S'', _, rfl⟩ := List.mem_map.mp hS'
        exact fun heq => huS (heq ▸ Finset.mem_insert_self u S'')
      · exact absurd hS' List.not_mem_nil

/-- The top-level enumeration `sumDP` contains no duplicate subset: within
one bucket `j` by `sumExact_nodup`, and across buckets because a subset in
bucket `j` has weighted sum exactly `j`. This is not cosmetic: the
provenance attached to the enumeration is the `⊕`-sum of the world
annotations over the returned list, and in a non-idempotent m-semiring a
duplicated world would change the value. -/
theorem sumDP_nodup (occs : List α) (hnodup : occs.Nodup) (t : α → ℕ)
    (C : ℕ) (op : CompOp) : (sumDP occs t C op).Nodup := by
  unfold sumDP
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => (sumExact_nodup occs hnodup t j).filter _, ?_⟩
  have hpw : (((List.range (occs.toFinset.sum t + 1)).filter
      (fun j => decide (op.eval j C)))).Pairwise (· ≠ ·) :=
    (List.nodup_range).filter _
  refine hpw.imp fun {j₁ j₂} hne S hS₁ hS₂ => hne ?_
  have h₁ := ((sumExact_mem occs hnodup t j₁ S).mp (List.mem_of_mem_filter hS₁)).2
  have h₂ := ((sumExact_mem occs hnodup t j₂ S).mp (List.mem_of_mem_filter hS₂)).2
  omega

/-- **Correctness of `sumDP`.**
For a list `occs` of distinct occurrences, a weight function `t`, a
constant `C : ℕ`, and a comparison operator `op`, the list
`sumDP occs t C op` enumerates exactly the non-empty subsets
`S ⊆ occs.toFinset` whose weighted sum satisfies `op.eval (S.sum t) C`. -/
theorem sumDP_correct (occs : List α) (hnodup : occs.Nodup) (t : α → ℕ)
    (C : ℕ) (op : CompOp) (S : Finset α) :
    S ∈ sumDP occs t C op ↔
      S ⊆ occs.toFinset ∧ S ≠ ∅ ∧ op.eval (S.sum t) C := by
  unfold sumDP
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range,
             decide_eq_true_iff]
  constructor
  · rintro ⟨j, ⟨_, hop⟩, hSj, hSne⟩
    rw [sumExact_mem occs hnodup t j S] at hSj
    obtain ⟨hSU, hsum⟩ := hSj
    refine ⟨hSU, hSne, ?_⟩
    rw [hsum]; exact hop
  · rintro ⟨hSU, hSne, hop⟩
    refine ⟨S.sum t, ⟨?_, ?_⟩, ?_, hSne⟩
    · -- S.sum t < occs.toFinset.sum t + 1
      have hle : S.sum t ≤ occs.toFinset.sum t :=
        Finset.sum_le_sum_of_subset hSU
      exact Nat.lt_succ_of_le hle
    · exact hop
    · rw [sumExact_mem occs hnodup t (S.sum t) S]
      exact ⟨hSU, rfl⟩

/-! ### Soundness of the implementation optimizations

The imperative implementation of the algorithm bounds its `dp` table by an
operator-specific `J = min(C, T)` for the operators `=`, `≤`, `<`, prunes
`dp[j]` cells beyond the running prefix sum, and short-circuits comparisons
that no achievable sum can satisfy. Each optimization is proved *as a list
equality* with the unoptimized enumeration: the optimized enumerations
return the same worlds, so the downstream `⊕`-sum of world annotations is
unchanged. -/

/-- Range trimming: `filter p` yields the same list on `range (T + 1)` and
on `range (J + 1)` when no `j ∈ (J, T]` satisfies `p`. -/
private theorem filter_range_eq (p : ℕ → Bool) {J T : ℕ} (hJT : J ≤ T)
    (h : ∀ j, J < j → j ≤ T → ¬ p j) :
    (List.range (T + 1)).filter p = (List.range (J + 1)).filter p := by
  induction T with
  | zero =>
    have : J = 0 := Nat.le_zero.mp hJT
    subst this; rfl
  | succ T' ih =>
    rcases Nat.lt_or_ge J (T' + 1) with hJ | hJ
    · rw [List.range_succ, List.filter_append,
        ih (by omega) (fun j h₁ h₂ => h j h₁ (by omega)),
        show List.filter p [T' + 1] = [] by
          simp [h (T' + 1) (by omega) le_rfl],
        List.append_nil]
    · have : J = T' + 1 := by omega
      subst this; rfl

/-- **Operator-specific bound on the `dp` table.** For `op ∈ {=, ≤, <}`, no
sum above `C` satisfies the comparison, so the enumeration may range over
`{0, …, min(C, T)}` instead of `{0, …, T}` and return the same list. -/
theorem sumDP_eq_bounded (occs : List α) (t : α → ℕ) (C : ℕ) {op : CompOp}
    (hop : op = .eq ∨ op = .le ∨ op = .lt) :
    sumDP occs t C op
      = ((List.range (min C (occs.toFinset.sum t) + 1)).filter
            (fun j => decide (op.eval j C))).flatMap
          (fun j => (sumExact occs t j).filter (fun S => decide (S ≠ ∅))) := by
  show ((List.range (occs.toFinset.sum t + 1)).filter
        (fun j => decide (op.eval j C))).flatMap
      (fun j => (sumExact occs t j).filter (fun S => decide (S ≠ ∅))) = _
  rcases Nat.le_total C (occs.toFinset.sum t) with hCT | hTC
  · rw [Nat.min_eq_left hCT]
    congr 1
    refine filter_range_eq _ hCT fun j h₁ _ => ?_
    rcases hop with rfl | rfl | rfl <;>
      simp only [CompOp.eval, decide_eq_true_eq] <;> omega
  · rw [Nat.min_eq_right hTC]

/-- **Reachability pruning.** Above the total weight of the occurrence list
(in the imperative formulation: above the running prefix sum at each step
of the recursion), the `dp` cells are empty: `sumExact occs t j = []` as
soon as `j` exceeds `(occs.map t).sum`. No `Nodup` hypothesis is needed. -/
theorem sumExact_eq_nil_of_lt_sum (occs : List α) (t : α → ℕ) :
    ∀ {j : ℕ}, (occs.map t).sum < j → sumExact occs t j = [] := by
  induction occs with
  | nil =>
    intro j h
    simp only [List.map_nil, List.sum_nil] at h
    cases j with
    | zero => omega
    | succ j => rfl
  | cons u rest ih =>
    intro j h
    simp only [List.map_cons, List.sum_cons] at h
    simp only [sumExact, ih (show (rest.map t).sum < j by omega), List.nil_append]
    split_ifs with hle
    · rw [ih (show (rest.map t).sum < j - t u by omega), List.map_nil]
    · rfl

/-- Under `Nodup`, the reachability bound can be read on the total weight
`T = ∑_{u ∈ occs} t u` of the distinct occurrences. -/
theorem sumExact_eq_nil_of_lt_sum' (occs : List α) (hnodup : occs.Nodup)
    (t : α → ℕ) {j : ℕ} (h : occs.toFinset.sum t < j) :
    sumExact occs t j = [] := by
  refine sumExact_eq_nil_of_lt_sum occs t ?_
  rwa [← List.sum_toFinset t hnodup]

/-- **Range check, unsatisfiable side.** If no achievable sum satisfies the
comparison, the enumeration is empty (and the associated provenance is
`𝟘`, an empty `⊕`-sum). -/
theorem sumDP_eq_nil_of_unsat (occs : List α) (t : α → ℕ) (C : ℕ) (op : CompOp)
    (h : ∀ j ≤ occs.toFinset.sum t, ¬ op.eval j C) :
    sumDP occs t C op = [] := by
  show ((List.range (occs.toFinset.sum t + 1)).filter
        (fun j => decide (op.eval j C))).flatMap
      (fun j => (sumExact occs t j).filter (fun S => decide (S ≠ ∅))) = []
  rw [List.filter_eq_nil_iff.mpr fun j hj => by
      simp only [decide_eq_true_eq]
      exact h j (Nat.lt_succ_iff.mp (List.mem_range.mp hj))]
  rfl

end SumDP
