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
# Correctness of Algorithm 1: SUM enumeration via dynamic programming

This file formalises Algorithm 1 of the HAVING / ProvSQL paper. The
algorithm enumerates the non-empty subsets `W` of a finite set of
occurrences `U` whose weighted sum `∑_{u ∈ W} t u` satisfies
`(∑ t) op C` for a fixed comparison operator `op` and constant `C : ℕ`.
The main result `sumDP_correct` shows that the output coincides with
that set in the sense of membership.

The paper presents the algorithm as an imperative subset-sum dynamic
program with an in-place `dp[j]` array, bounded by `J` chosen per
operator, with early returns for impossible operator/constant
combinations. We use the mathematically equivalent functional
formulation: `sumExact occs t j` is the list of subsets of
`occs.toFinset` with weighted sum exactly `j` (i.e., the paper's
`dp[j]` after iteration `N`), defined by direct recursion on `occs`.
The six `op`-cases of the algorithm and all four early-return cases
collapse into a single `flatMap` over satisfying sums in `{0, …, T}`,
where `T = occs.toFinset.sum t`. Impossible sums simply contribute
empty enumerations.

The aggregate term `t` enters as `α → ℕ`; the annotation `α_i` of the
paper is part of the occurrence type and does not enter the sum.
-/

namespace SumDP

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Definitions -/

/-- `sumExact occs t j`: enumerate the subsets of `occs.toFinset` whose
weighted sum under `t` is exactly `j`. Mirrors `dp[j]` after the outer
loop of Algorithm 1: every subset either omits the head `u` (left
recursion) or includes it (right recursion, requires `t u ≤ j`). -/
def sumExact : List α → (α → ℕ) → ℕ → List (Finset α)
  | [],        _, 0     => [∅]
  | [],        _, _ + 1 => []
  | u :: rest, t, j =>
    sumExact rest t j ++
      (if t u ≤ j then (sumExact rest t (j - t u)).map (insert u) else [])

/-- `SumDP(U, t, C, op)` of Algorithm 1. The six operator-cases of the
paper (and the four early-return cases) collapse into a single
`flatMap` over satisfying sums in `{0, …, T}`, where `T` is the total
weight `occs.toFinset.sum t`. -/
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

/-- **Correctness of Algorithm 1** (`thm:sumdp-correct` of the paper).
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

end SumDP
