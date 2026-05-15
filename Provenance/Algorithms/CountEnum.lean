/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Range

/-!
# Correctness of Algorithm 2: COUNT enumeration

This file formalises Algorithm 2 of the HAVING / ProvSQL paper (Sen,
Aryak & Senellart). The algorithm enumerates the non-empty subsets `W`
of a finite set of occurrences `U` whose cardinality satisfies
`|W| op C` for a fixed comparison operator `op ∈ {=, ≠, <, ≤, >, ≥}`
and a constant `C ∈ ℕ`. The main result `countEnum_correct` shows
that the list produced by `countEnum` coincides with that set, in the
sense of membership.

The aggregate term `t` of the paper is irrelevant to COUNT and is
dropped from the Lean signature; the paper notes this explicitly. The
"distinct occurrences" hypothesis of the paper is encoded as
`List.Nodup` and is needed in the spec only so that `Finset` cardinality
matches list length: without it, the algorithm still returns subsets of
`occs.toFinset`, but cardinality bookkeeping breaks.
-/

namespace CountEnum

variable {α : Type*} [DecidableEq α]

/-- Comparison operator for cardinalities. -/
inductive CompOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Semantics of a comparison operator on natural numbers. -/
def CompOp.eval : CompOp → ℕ → ℕ → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

instance (op : CompOp) (a b : ℕ) : Decidable (op.eval a b) := by
  cases op <;> simp [CompOp.eval] <;> infer_instance

/-- `Combinations(i, x, W)` of Algorithm 2, expressed with the suffix
list `occs` (representing the occurrences `(uᵢ, αᵢ), …, (u_N, α_N)`)
instead of an explicit index `i`. Returns the list of subsets obtained
by extending the accumulator `W` with exactly `x` further elements drawn
from `occs`. -/
def combinations : List α → ℕ → Finset α → List (Finset α)
  | _,         0,     W => [W]
  | [],        _ + 1, _ => []
  | u :: rest, x + 1, W => combinations rest (x + 1) W
                          ++ combinations rest x (insert u W)

/-- `AddExact(x)` of Algorithm 2: enumerate the non-empty subsets of
`occs` of cardinality exactly `x`. The `x = 0` case returns `[]` so
that the empty world is excluded from the output. -/
def addExact (occs : List α) (x : ℕ) : List (Finset α) :=
  if x = 0 then [] else combinations occs x ∅

/-- `CountEnum(U, C, op)` of Algorithm 2: the top-level routine. The
six cases of the algorithm collapse into a single `flatMap` over the
satisfying cardinalities `x ∈ {0, …, N}` because `addExact occs 0` is
already empty and `addExact occs x` is empty whenever `x > N`. -/
def countEnum (occs : List α) (C : ℕ) (op : CompOp) : List (Finset α) :=
  ((List.range (occs.length + 1)).filter (fun x => decide (op.eval x C))).flatMap
    (addExact occs)

/-! ### Correctness lemmas -/

/-- Membership characterisation of `combinations`. Under disjointness of
the accumulator and the suffix list, the output enumerates exactly the
sets of the form `W ∪ T` with `T` a subset of `occs.toFinset` of size
`x`. `Nodup occs` is needed so that the disjointness is preserved on
recursion (the head `u` must not appear later in the list). -/
theorem combinations_mem :
    ∀ (occs : List α), occs.Nodup →
    ∀ (x : ℕ) (W : Finset α), Disjoint W occs.toFinset →
    ∀ (S : Finset α),
      S ∈ combinations occs x W ↔
        ∃ T ⊆ occs.toFinset, T.card = x ∧ S = W ∪ T := by
  intro occs hnodup x
  induction occs generalizing x with
  | nil =>
    intro W _ S
    cases x with
    | zero =>
      simp [combinations]
    | succ x =>
      simp [combinations]
  | cons u rest ih =>
    intro W hdisj S
    have hunodup : u ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrestnodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    cases x with
    | zero =>
      simp [combinations]
    | succ x =>
      -- combinations (u :: rest) (x+1) W
      --   = combinations rest (x+1) W ++ combinations rest x (insert u W)
      simp only [combinations, List.mem_append]
      have huW : u ∉ W := by
        intro hu
        have : u ∈ (u :: rest).toFinset := by simp
        exact Finset.disjoint_left.mp hdisj hu this
      -- Disjointness for the two recursive calls
      have hdisj₁ : Disjoint W rest.toFinset := by
        rw [Finset.disjoint_left] at hdisj ⊢
        intro v hv hvr
        exact hdisj hv (by simp [hvr])
      have hdisj₂ : Disjoint (insert u W) rest.toFinset := by
        rw [Finset.disjoint_left]
        intro v hv hvr
        rcases Finset.mem_insert.mp hv with rfl | hvW
        · exact hunodup (List.mem_toFinset.mp hvr)
        · exact Finset.disjoint_left.mp hdisj₁ hvW hvr
      rw [ih hrestnodup (x + 1) W hdisj₁ S,
          ih hrestnodup x (insert u W) hdisj₂ S]
      constructor
      · rintro (⟨T, hT, hcard, hS⟩ | ⟨T, hT, hcard, hS⟩)
        · refine ⟨T, ?_, hcard, hS⟩
          intro v hv
          have : v ∈ rest.toFinset := hT hv
          simp at this ⊢
          exact Or.inr this
        · refine ⟨insert u T, ?_, ?_, ?_⟩
          · intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hvT
            · simp
            · have : v ∈ rest.toFinset := hT hvT
              simp at this ⊢
              exact Or.inr this
          · have huT : u ∉ T := fun h => hunodup (List.mem_toFinset.mp (hT h))
            rw [Finset.card_insert_of_notMem huT, hcard]
          · rw [hS, Finset.insert_union, Finset.union_insert]
      · rintro ⟨T, hT, hcard, hS⟩
        -- Split on whether u ∈ T
        by_cases huT : u ∈ T
        · right
          refine ⟨T.erase u, ?_, ?_, ?_⟩
          · intro v hv
            have hvT : v ∈ T := Finset.mem_of_mem_erase hv
            have hvne : v ≠ u := Finset.ne_of_mem_erase hv
            have : v ∈ (u :: rest).toFinset := hT hvT
            simp at this
            rcases this with rfl | hvr
            · exact absurd rfl hvne
            · exact List.mem_toFinset.mpr hvr
          · rw [Finset.card_erase_of_mem huT, hcard]
            simp
          · rw [hS]
            ext v
            simp [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
            by_cases hvu : v = u
            · subst hvu; simp [huW, huT]
            · simp [hvu]
        · left
          refine ⟨T, ?_, hcard, hS⟩
          intro v hv
          have : v ∈ (u :: rest).toFinset := hT hv
          simp at this
          rcases this with rfl | hvr
          · exact absurd hv huT
          · exact List.mem_toFinset.mpr hvr

/-- Membership characterisation of `addExact`: the output enumerates
the non-empty subsets of `occs` of cardinality exactly `x`. -/
theorem addExact_mem (occs : List α) (hnodup : occs.Nodup) (x : ℕ) (S : Finset α) :
    S ∈ addExact occs x ↔ S ⊆ occs.toFinset ∧ S.card = x ∧ S ≠ ∅ := by
  unfold addExact
  split_ifs with hx
  · subst hx
    simp only [List.not_mem_nil, false_iff, not_and]
    intro _ hcard hS
    exact hS (Finset.card_eq_zero.mp hcard)
  · rw [combinations_mem occs hnodup x ∅ (by simp) S]
    constructor
    · rintro ⟨T, hT, hcard, hS⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hS]; simpa
      · rw [hS]; simpa
      · rw [hS]
        simp only [Finset.empty_union]
        intro h
        subst h
        simp at hcard
        exact hx hcard.symm
    · rintro ⟨hSU, hcard, _⟩
      exact ⟨S, hSU, hcard, by simp⟩

/-- **Correctness of Algorithm 2** (`thm:count-enum-correct` of the
paper). For a list `occs` of distinct occurrences, a constant `C : ℕ`,
and a comparison operator `op`, the list `countEnum occs C op`
enumerates exactly the non-empty subsets `S ⊆ occs.toFinset` whose
cardinality satisfies `op.eval S.card C`. -/
theorem countEnum_correct (occs : List α) (hnodup : occs.Nodup) (C : ℕ)
    (op : CompOp) (S : Finset α) :
    S ∈ countEnum occs C op ↔ S ⊆ occs.toFinset ∧ S ≠ ∅ ∧ op.eval S.card C := by
  unfold countEnum
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨x, hxmem, hSmem⟩
    rw [List.mem_filter] at hxmem
    obtain ⟨_, hxop⟩ := hxmem
    rw [decide_eq_true_iff] at hxop
    rw [addExact_mem occs hnodup x S] at hSmem
    obtain ⟨hSU, hcard, hSne⟩ := hSmem
    refine ⟨hSU, hSne, ?_⟩
    rw [hcard]; exact hxop
  · rintro ⟨hSU, hSne, hop⟩
    refine ⟨S.card, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨?_, by rw [decide_eq_true_iff]; exact hop⟩
      rw [List.mem_range]
      have : S.card ≤ occs.toFinset.card := Finset.card_le_card hSU
      exact Nat.lt_succ_of_le (this.trans (List.toFinset_card_le occs))
    · rw [addExact_mem occs hnodup S.card S]
      exact ⟨hSU, rfl, hSne⟩

end CountEnum
