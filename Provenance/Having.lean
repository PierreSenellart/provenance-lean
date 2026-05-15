/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Provenance.SemiringWithMonus

/-!
# Algebraic identities behind HAVING (count) provenance

This file gathers query-free algebraic identities, in an arbitrary commutative
m-semiring, that underpin the correctness of the possible-world semantics for
`HAVING (count op C)` predicates.

For a finite ambient set `U : Finset ι` and a family `α : ι → K`, we define

* `A α W := ∏ x ∈ W, α x`,
* `T α U W := A α W ⊖ ⊕_{x ∈ U \ W} A α (W ∪ {x})`,
* `S α U C := ⊕_{W ⊆ U, |W| = C} A α W`,
* `F α U C := ⊕_{W ⊆ U, |W| ≥ C} T α U W`.

The main results are include/exclude-style recurrences for `S` and `F` and a
bounding lemma `A_V ≤ ⊕_{V ⊆ W ⊆ U} T_U(W)` in an idempotent m-semiring.
-/

namespace Having

open Finset

variable {ι : Type} [DecidableEq ι]
variable {K : Type} [CommSemiringWithMonus K]

/-- Monomial annotation of a subset: `A_W = ∏_{x ∈ W} α x`, with the
convention `A_∅ = 𝟙`. -/
def A (α : ι → K) (W : Finset ι) : K :=
  ∏ x ∈ W, α x

/-- `T_U(W) = A_W ⊖ ⊕_{x ∈ U \ W} A_{W ∪ {x}}`: the "exactly-`W`" contribution
that removes from `A_W` all one-step extensions of `W` inside `U`. -/
def T (α : ι → K) (U W : Finset ι) : K :=
  A α W - ∑ x ∈ U \ W, A α (insert x W)

/-- `S_C(U) = ⊕_{W ⊆ U, |W| = C} A_W`: the JOIN-based provenance for a
`HAVING count = C` aggregate (up to surface-level reindexing). -/
def S (α : ι → K) (U : Finset ι) (C : ℕ) : K :=
  ∑ W ∈ U.powersetCard C, A α W

/-- `F_C(U) = ⊕_{W ⊆ U, |W| ≥ C} T_U(W)`: the possible-world provenance for
a `HAVING count ≥ C` predicate. -/
def F (α : ι → K) (U : Finset ι) (C : ℕ) : K :=
  ∑ W ∈ U.powerset.filter (fun W => C ≤ W.card), T α U W

/-- Alternative form `T_U(W) = A_W ⊗ (𝟙 ⊖ ⊕_{x ∈ U \ W} α x)`. This is the
shape in which `T_U(W)` first arises from the possible-world semantics; the
definition of `T` is the rewritten form obtained via distributivity of `⊗`
over `⊖` and over `⊕`. Holds in any commutative m-semiring with
`mul_sub_left_distributive`. -/
theorem T_eq_mul_one_monus_sum (α : ι → K) (h_distrib : mul_sub_left_distributive K)
    (U W : Finset ι) :
    T α U W = A α W * (1 - ∑ x ∈ U \ W, α x) := by
  simp only [T, A]
  rw [h_distrib, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hxW : x ∉ W := (Finset.mem_sdiff.mp hx).2
  rw [Finset.prod_insert hxW, mul_comm]

/-- Include/exclude recurrence for the JOIN-based provenance `S`:
`S_{C+1}(U) = S_{C+1}(U \ {u}) ⊕ S_C(U \ {u}) ⊗ α u`. The proof partitions
`(insert u U').powersetCard (C+1)` into subsets that do not contain `u` and
images of `C`-sized subsets of `U'` under `insert u`. -/
theorem SC_recurrence (α : ι → K) {U : Finset ι} {u : ι} (hu : u ∈ U) (C : ℕ) :
    S α U (C + 1) = S α (U.erase u) (C + 1) + S α (U.erase u) C * α u := by
  have hu' : u ∉ U.erase u := Finset.notMem_erase u U
  have hU : U = insert u (U.erase u) := (Finset.insert_erase hu).symm
  simp only [S]
  conv_lhs => rw [hU, Finset.powersetCard_succ_insert hu']
  have hdisj : Disjoint ((U.erase u).powersetCard (C + 1))
                        (((U.erase u).powersetCard C).image (insert u)) := by
    rw [Finset.disjoint_left]
    intro W hW hW'
    simp only [Finset.mem_image, Finset.mem_powersetCard] at hW hW'
    obtain ⟨W', _, hWeq⟩ := hW'
    rw [← hWeq] at hW
    exact hu' (hW.1 (Finset.mem_insert_self u W'))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image
    (fun W₁ hW₁ W₂ hW₂ heq => by
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hW₁ hW₂
      have hu₁ : u ∉ W₁ := fun h => hu' (hW₁.1 h)
      have hu₂ : u ∉ W₂ := fun h => hu' (hW₂.1 h)
      have : (insert u W₁).erase u = (insert u W₂).erase u := by rw [heq]
      rwa [Finset.erase_insert hu₁, Finset.erase_insert hu₂] at this)]
  simp only [A]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun W' hW' => ?_)
  rw [Finset.mem_powersetCard] at hW'
  have hu_notin : u ∉ W' := fun h => hu' (hW'.1 h)
  rw [Finset.prod_insert hu_notin]
  exact mul_comm (α u) (∏ x ∈ W', α x)

/-- In an idempotent `CommSemiringWithMonus`, if every summand of a `Finset.sum`
is bounded above by `a`, then so is the sum. The empty sum is `0 ≤ a` by canonical
ordering; the inductive step uses `a + a = a`. -/
private theorem sum_le_of_forall_le (h_idem : idempotent K)
    {s : Finset ι} {f : ι → K} {a : K} (hle : ∀ x ∈ s, f x ≤ a) :
    ∑ x ∈ s, f x ≤ a := by
  induction s using Finset.induction with
  | empty => simp
  | insert x t hxt ih =>
    rw [Finset.sum_insert hxt]
    calc f x + ∑ y ∈ t, f y
        ≤ a + a := add_le_add (hle x (Finset.mem_insert_self _ _))
                              (ih (fun y hy => hle y (Finset.mem_insert_of_mem hy)))
      _ = a := h_idem a

/-- Upward expansion bound: in an idempotent m-semiring, the monomial of any
subset `V ⊆ U` is bounded above by the sum of `T_U(W)` over all supersets
`W ⊇ V` inside `U`. The proof is by strong induction on `(U \ V).card`,
using `le_plus_monus` for the inductive step and the auxiliary
`sum_le_of_forall_le` to collapse multiplicities by idempotence. -/
theorem upward_expansion (α : ι → K) (h_idem : idempotent K) (U : Finset ι) :
    ∀ V : Finset ι, V ⊆ U →
      A α V ≤ ∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W := by
  suffices h : ∀ n : ℕ, ∀ V : Finset ι, V ⊆ U → (U \ V).card = n →
      A α V ≤ ∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W from
    fun V hVU => h _ V hVU rfl
  intro n
  induction n with
  | zero =>
    intro V hVU hcard
    -- Base case: `U \ V = ∅`, so `V = U` and the filter contains only `U`.
    have hsub : U ⊆ V := by
      intro x hx
      by_contra hxV
      have : x ∈ U \ V := by simp [hx, hxV]
      rw [Finset.card_eq_zero.mp hcard] at this
      exact Finset.notMem_empty _ this
    have hVeq : V = U := Finset.Subset.antisymm hVU hsub
    rw [hVeq]
    have hfilter : U.powerset.filter (U ⊆ ·) = {U} := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      exact ⟨fun ⟨hWU, hUW⟩ => Finset.Subset.antisymm hWU hUW,
             fun h => h ▸ ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩⟩
    rw [hfilter, Finset.sum_singleton]
    -- `T α U U = A α U - 0 = A α U`.
    have hTUU : T α U U = A α U := by
      simp [T, monus_zero]
    rw [hTUU]
  | succ n ih =>
    intro V hVU hcard
    -- `Y = ⊕_{x ∈ U \ V} A α (insert x V)`.
    set Y : K := ∑ x ∈ U \ V, A α (insert x V) with hY
    -- `T α U V = A α V - Y` by definition.
    have hTV : T α U V = A α V - Y := rfl
    -- Step 1: `A α V ≤ Y + T α U V` from `le_plus_monus`.
    have hstep1 : A α V ≤ Y + T α U V := by rw [hTV]; exact le_plus_monus _ _
    -- Step 2: each `A α (insert x V) ≤ RHS` for `x ∈ U \ V`.
    have hAVx_bd : ∀ x ∈ U \ V,
        A α (insert x V) ≤ ∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxU, hxV⟩ := hx
      have hxinsV : insert x V ⊆ U := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyV
        · exact hxU
        · exact hVU hyV
      have hcard' : (U \ insert x V).card = n := by
        have : U \ insert x V = (U \ V).erase x := by
          ext y; simp; tauto
        rw [this, Finset.card_erase_of_mem (by simp [hxU, hxV]), hcard]; simp
      have hih := ih (insert x V) hxinsV hcard'
      apply le_trans hih
      apply Finset.sum_le_sum_of_subset
      intro W hW
      rw [Finset.mem_filter] at hW ⊢
      exact ⟨hW.1, fun y hy => hW.2 (Finset.mem_insert_of_mem hy)⟩
    -- Step 3: `Y ≤ RHS` by idempotent collapse.
    have hY_bd : Y ≤ ∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W :=
      sum_le_of_forall_le h_idem hAVx_bd
    -- Step 4: `T α U V ≤ RHS` since it is one of the summands.
    have hTV_bd : T α U V ≤ ∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W :=
      Finset.single_le_sum_of_canonicallyOrdered (f := T α U)
        (by rw [Finset.mem_filter];
            exact ⟨Finset.mem_powerset.mpr hVU, Finset.Subset.refl _⟩)
    -- Step 5: combine.
    calc A α V ≤ Y + T α U V := hstep1
      _ ≤ (∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W) +
          (∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W) := add_le_add hY_bd hTV_bd
      _ = ∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W :=
          h_idem _

/-- For `W ⊆ U.erase u`, `T α U W = T α (U.erase u) W - A α W * α u`. The
extra `A α W * α u` corresponds to the one-step extension by `u` that exists
inside `U` but not inside `U.erase u`. -/
private theorem T_eq_T_erase_sub (α : ι → K) {U : Finset ι} {u : ι} (hu : u ∈ U)
    {W : Finset ι} (hW : W ⊆ U.erase u) :
    T α U W = T α (U.erase u) W - A α W * α u := by
  have hu_notin : u ∉ W := fun h => Finset.notMem_erase u U (hW h)
  -- `U \ W = (U.erase u \ W) ∪ {u}` (disjoint).
  have hsplit : U \ W = insert u ((U.erase u) \ W) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    constructor
    · intro ⟨hxU, hxW⟩
      by_cases hxu : x = u
      · left; exact hxu
      · right; exact ⟨⟨hxu, hxU⟩, hxW⟩
    · rintro (rfl | ⟨⟨_, hxU⟩, hxW⟩)
      · exact ⟨hu, hu_notin⟩
      · exact ⟨hxU, hxW⟩
  have hu_notin_sdiff : u ∉ (U.erase u) \ W := by
    simp [Finset.mem_sdiff]
  have hA_insert : A α (insert u W) = A α W * α u := by
    simp only [A, Finset.prod_insert hu_notin]
    exact mul_comm (α u) _
  -- Compute T α U W using the split.
  show A α W - _ = (A α W - _) - A α W * α u
  rw [hsplit, Finset.sum_insert hu_notin_sdiff, hA_insert]
  rw [add_comm, ← monus_add]

/-- For `W ⊆ U.erase u`, `T α U W ≤ T α (U.erase u) W`. -/
private theorem T_le_T_erase (α : ι → K) {U : Finset ι} {u : ι} (hu : u ∈ U)
    {W : Finset ι} (hW : W ⊆ U.erase u) :
    T α U W ≤ T α (U.erase u) W := by
  rw [T_eq_T_erase_sub α hu hW]
  exact monus_le _ _

/-- `T α U (insert u W') = T α (U.erase u) W' * α u` for `W' ⊆ U.erase u`.
This is the simplification of the `u ∈ W` summands in the `F α U` split. -/
private theorem T_insert_eq (α : ι → K) (h_distrib : mul_sub_left_distributive K)
    {U : Finset ι} {u : ι}
    {W' : Finset ι} (hW' : W' ⊆ U.erase u) :
    T α U (insert u W') = T α (U.erase u) W' * α u := by
  have hu_notin : u ∉ W' := fun h => Finset.notMem_erase u U (hW' h)
  -- `U \ (insert u W') = (U.erase u) \ W'`.
  have hsdiff : U \ insert u W' = (U.erase u) \ W' := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
    tauto
  -- For `x ∈ (U.erase u) \ W'`, `insert x (insert u W') = insert u (insert x W')`
  -- and `A α (insert u (insert x W')) = α u * A α (insert x W')`.
  have hA_uW' : A α (insert u W') = α u * A α W' := by
    simp only [A]; rw [Finset.prod_insert hu_notin]
  have hA_uxW' : ∀ x ∈ (U.erase u) \ W',
      A α (insert x (insert u W')) = α u * A α (insert x W') := by
    intro x hx
    have hxu : x ≠ u := fun heq =>
      Finset.notMem_erase u U (heq ▸ (Finset.mem_sdiff.mp hx).1)
    have hu_notin_xW' : u ∉ insert x W' := by
      rw [Finset.mem_insert]; push Not
      exact ⟨Ne.symm hxu, hu_notin⟩
    simp only [A]
    rw [Finset.insert_comm x u W', Finset.prod_insert hu_notin_xW']
  show A α (insert u W') - _ = (A α W' - _) * α u
  rw [hsdiff, hA_uW', Finset.sum_congr rfl hA_uxW', ← Finset.mul_sum, ← h_distrib]
  exact mul_comm _ _

/-- Include/exclude recurrence for the possible-world provenance `F`:
`F_{C+1}(U) = F_{C+1}(U \ {u}) ⊕ F_C(U \ {u}) ⊗ α u`, in any idempotent
commutative m-semiring with left-distributivity of `⊗` over `⊖`. The proof
splits the powerset of `U` by whether `u ∈ W`, simplifies the `u ∈ W` part
to `F_C(U') ⊗ α u`, and combines two opposite inequalities using the upward
expansion bound `upward_expansion`. -/
theorem FC_recurrence (α : ι → K) (h_idem : idempotent K)
    (h_distrib : mul_sub_left_distributive K)
    {U : Finset ι} {u : ι} (hu : u ∈ U) (C : ℕ) :
    F α U (C + 1) = F α (U.erase u) (C + 1) + F α (U.erase u) C * α u := by
  set U' := U.erase u with hU'def
  have hu_notin' : u ∉ U' := Finset.notMem_erase u U
  have hU_eq : U = insert u U' := (Finset.insert_erase hu).symm
  -- Split the index set of `F α U (C+1)` into (I) (subsets not containing u)
  -- and (II) (subsets containing u, i.e., insert u W' for W' ⊆ U').
  have hpartition : U.powerset.filter (C + 1 ≤ ·.card) =
      U'.powerset.filter (C + 1 ≤ ·.card) ∪
        (U'.powerset.filter (C ≤ ·.card)).image (insert u) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
               Finset.mem_image]
    constructor
    · rintro ⟨hWU, hcard⟩
      by_cases huW : u ∈ W
      · right
        refine ⟨W.erase u, ⟨?_, ?_⟩, Finset.insert_erase huW⟩
        · intro x hx
          rcases Finset.mem_erase.mp hx with ⟨hxu, hxW⟩
          exact Finset.mem_erase.mpr ⟨hxu, hWU hxW⟩
        · rw [Finset.card_erase_of_mem huW]
          omega
      · left
        refine ⟨?_, hcard⟩
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun heq => huW (heq ▸ hx), hWU hx⟩
    · rintro (⟨hWU', hcard⟩ | ⟨W', ⟨hW'U', hW'card⟩, hWeq⟩)
      · refine ⟨?_, hcard⟩
        intro x hx
        exact (Finset.mem_erase.mp (hWU' hx)).2
      · have hu_notin_W' : u ∉ W' := fun h => hu_notin' (hW'U' h)
        refine ⟨?_, ?_⟩
        · rw [← hWeq, hU_eq]
          exact Finset.insert_subset_insert u hW'U'
        · rw [← hWeq, Finset.card_insert_of_notMem hu_notin_W']
          omega
  -- The two pieces are disjoint: (I) has subsets of U' (no u), (II) has subsets containing u.
  have hdisj : Disjoint (U'.powerset.filter (C + 1 ≤ ·.card))
                        ((U'.powerset.filter (C ≤ ·.card)).image (insert u)) := by
    rw [Finset.disjoint_left]
    intro W hW hW'
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image] at hW hW'
    obtain ⟨W', _, hWeq⟩ := hW'
    have : u ∈ W := hWeq ▸ Finset.mem_insert_self u W'
    exact hu_notin' (hW.1 this)
  -- `insert u` is injective on `U'.powerset.filter (C ≤ ·.card)`.
  have hinj : Set.InjOn (insert u)
      (↑(U'.powerset.filter (C ≤ ·.card)) : Set (Finset ι)) := by
    intro W₁ hW₁ W₂ hW₂ heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hW₁ hW₂
    have hu₁ : u ∉ W₁ := fun h => hu_notin' (hW₁.1 h)
    have hu₂ : u ∉ W₂ := fun h => hu_notin' (hW₂.1 h)
    have : (insert u W₁).erase u = (insert u W₂).erase u := by rw [heq]
    rwa [Finset.erase_insert hu₁, Finset.erase_insert hu₂] at this
  -- Names for the two parts.
  let part_I := ∑ W ∈ U'.powerset.filter (C + 1 ≤ ·.card), T α U W
  let part_II := ∑ W' ∈ U'.powerset.filter (C ≤ ·.card), T α U (insert u W')
  -- `F α U (C+1) = part_I + part_II` via the partition.
  have hsplit : F α U (C + 1) = part_I + part_II := by
    simp only [F]
    rw [hpartition, Finset.sum_union hdisj]
    show _ + ∑ W ∈ _, T α U W = part_I + part_II
    rw [Finset.sum_image hinj]
  -- Each `T α U (insert u W') = T α U' W' * α u` (for `W' ⊆ U'`).
  have hII_eq : part_II = F α U' C * α u := by
    show ∑ W' ∈ _, T α U (insert u W') = (∑ W' ∈ _, T α U' W') * α u
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun W' hW' => ?_)
    rw [Finset.mem_filter, Finset.mem_powerset] at hW'
    exact T_insert_eq α h_distrib hW'.1
  -- Step A: `part_I ≤ F α U' (C+1)` since `T α U W ≤ T α U' W` for `W ⊆ U'`.
  have hI_le_FU' : part_I ≤ F α U' (C + 1) := by
    refine Finset.sum_le_sum (fun W hW => ?_)
    rw [Finset.mem_filter, Finset.mem_powerset] at hW
    exact T_le_T_erase α hu hW.1
  -- So one direction: `F α U (C+1) ≤ F α U' (C+1) + F α U' C * α u`.
  have hle1 : F α U (C + 1) ≤ F α U' (C + 1) + F α U' C * α u := by
    rw [hsplit, hII_eq]
    exact add_le_add hI_le_FU' (le_refl _)
  -- Step B: For each `W ⊆ U'` with `C+1 ≤ W.card`, `T α U' W ≤ F α U (C+1)`.
  -- (i) `T α U W ≤ F α U (C+1)` since W is in F α U (C+1)'s sum.
  -- (ii) `A α W * α u = A α (insert u W) ≤ F α U (C+1)` by upward_expansion.
  -- Combined: T α U' W = T α U W + A α W * α u ≤ F α U (C+1) (using idempotence).
  have hFU'_le_FU : F α U' (C + 1) ≤ F α U (C + 1) := by
    refine sum_le_of_forall_le h_idem ?_
    intro W hW
    rw [Finset.mem_filter, Finset.mem_powerset] at hW
    obtain ⟨hWU', hWcard⟩ := hW
    have hWU : W ⊆ U := hWU'.trans (Finset.erase_subset _ _)
    -- (i)
    have hTUW_le : T α U W ≤ F α U (C + 1) := by
      simp only [F]
      refine Finset.single_le_sum_of_canonicallyOrdered (f := T α U) ?_
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hWU, hWcard⟩
    -- (ii) Use upward_expansion with V = insert u W.
    have huW : insert u W ⊆ U := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxW
      · exact hu
      · exact hWU hxW
    have hcard_uW : C + 1 ≤ (insert u W).card := by
      have hu_notin_W : u ∉ W := fun h => hu_notin' (hWU' h)
      rw [Finset.card_insert_of_notMem hu_notin_W]
      omega
    have hAuW_le : A α (insert u W) ≤ F α U (C + 1) := by
      apply (upward_expansion α h_idem U _ huW).trans
      simp only [F]
      refine Finset.sum_le_sum_of_subset ?_
      intro Y hY
      rw [Finset.mem_filter, Finset.mem_powerset] at hY ⊢
      refine ⟨hY.1, ?_⟩
      -- |Y| ≥ |insert u W| ≥ C+1
      have hcard_Y : (insert u W).card ≤ Y.card := Finset.card_le_card hY.2
      omega
    have hAWβ_eq : A α W * α u = A α (insert u W) := by
      have hu_notin_W : u ∉ W := fun h => hu_notin' (hWU' h)
      simp only [A]; rw [Finset.prod_insert hu_notin_W, mul_comm (α u) _]
    have hAWβ_le : A α W * α u ≤ F α U (C + 1) := hAWβ_eq ▸ hAuW_le
    -- Combine: T α U' W = T α U W + A α W * α u (by T_eq_T_erase_sub + le_plus_monus).
    -- More precisely, T α U W = T α U' W - A α W * α u, so by le_plus_monus:
    -- T α U' W ≤ (A α W * α u) + (T α U' W - A α W * α u) = (A α W * α u) + T α U W.
    have hTU'W_le : T α U' W ≤ A α W * α u + T α U W := by
      have h := le_plus_monus (T α U' W) (A α W * α u)
      rwa [← T_eq_T_erase_sub α hu hWU'] at h
    calc T α U' W ≤ A α W * α u + T α U W := hTU'W_le
      _ ≤ F α U (C + 1) + F α U (C + 1) := add_le_add hAWβ_le hTUW_le
      _ = F α U (C + 1) := h_idem _
  -- Step C: `F α U' C * α u = part_II ≤ F α U (C+1)` since `part_II` is a summand.
  have hII_le_FU : F α U' C * α u ≤ F α U (C + 1) := by
    rw [← hII_eq, hsplit]
    exact le_add_self
  -- Step D: combine using idempotence.
  have hle2 : F α U' (C + 1) + F α U' C * α u ≤ F α U (C + 1) := by
    calc F α U' (C + 1) + F α U' C * α u
        ≤ F α U (C + 1) + F α U (C + 1) := add_le_add hFU'_le_FU hII_le_FU
      _ = F α U (C + 1) := h_idem _
  exact le_antisymm hle1 hle2

/-! ### Upward-closed family collapse in absorptive m-semirings

The provenance of a finite family `F` of subsets, weighted by `A`, agrees
with the provenance of any subfamily `M ⊆ F` such that every element of
`F` contains some element of `M`. When `F` is upward-closed under
inclusion, the canonical such `M` is the set of minimal elements of `F`.
-/

/-- Multiplication on the left is monotone in any `SemiringWithMonus` (the
`CanonicallyOrderedAdd` structure makes the additive witness of `≤`
multiply through). -/
private theorem mul_le_mul_left_canonical (a : K) {b c : K} (h : b ≤ c) :
    a * b ≤ a * c := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [mul_add]
  exact le_self_add

/-- In an absorptive `CommSemiringWithMonus`, any finite product of
annotations is bounded above by `𝟙`. -/
private theorem prod_le_one_absorptive (h_abs : absorptive K) (α : ι → K) :
    ∀ S : Finset ι, ∏ x ∈ S, α x ≤ 1 := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  have hα_le_one : ∀ x, α x ≤ 1 := fun x => by
    rw [le_iff_add_eq h_idem, add_comm]; exact h_abs (α x)
  intro S
  induction S using Finset.induction with
  | empty => simp
  | insert x t hxt ih =>
    rw [Finset.prod_insert hxt]
    calc α x * ∏ y ∈ t, α y
        ≤ α x * 1 := mul_le_mul_left_canonical _ ih
      _ = α x := mul_one _
      _ ≤ 1 := hα_le_one x

/-- In an absorptive `CommSemiringWithMonus`, the monomial `A` is monotone
*decreasing* under inclusion: enlarging a subset can only decrease its
annotation, since each additional factor is bounded by `𝟙`. -/
private theorem A_le_of_subset_absorptive (h_abs : absorptive K) (α : ι → K)
    {W W' : Finset ι} (hW'W : W' ⊆ W) :
    A α W ≤ A α W' := by
  have hdisj : Disjoint W' (W \ W') := Finset.disjoint_sdiff
  have hunion : W = W' ∪ (W \ W') := (Finset.union_sdiff_of_subset hW'W).symm
  simp only [A]
  conv_lhs => rw [hunion, Finset.prod_union hdisj]
  calc (∏ x ∈ W', α x) * (∏ x ∈ W \ W', α x)
      ≤ (∏ x ∈ W', α x) * 1 :=
        mul_le_mul_left_canonical _ (prod_le_one_absorptive h_abs α _)
    _ = ∏ x ∈ W', α x := mul_one _

/-- Upward-closed family collapse: in an absorptive commutative m-semiring,
the `A`-weighted sum over a finite family `F` equals the `A`-weighted sum
over any subfamily `M ⊆ F` such that every element of `F` is a superset of
some element of `M`. Taking `M` = the minimal elements of `F` (when `F` is
upward-closed) is the canonical application: the provenance of an
upward-closed family of worlds collapses to the provenance of its minimal
worlds. -/
theorem absorbing_subfamily (α : ι → K) (h_abs : absorptive K)
    {F M : Finset (Finset ι)} (hM_sub : M ⊆ F)
    (hcover : ∀ W ∈ F, ∃ W' ∈ M, W' ⊆ W) :
    ∑ W ∈ F, A α W = ∑ W ∈ M, A α W := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  apply le_antisymm
  · apply sum_le_of_forall_le h_idem
    intro W hW
    obtain ⟨W', hW'M, hW'W⟩ := hcover W hW
    calc A α W ≤ A α W' := A_le_of_subset_absorptive h_abs α hW'W
      _ ≤ ∑ W'' ∈ M, A α W'' :=
        Finset.single_le_sum_of_canonicallyOrdered (f := A α) hW'M
  · exact Finset.sum_le_sum_of_subset hM_sub

/-! ### F equals S: algebraic skeleton of `HAVING count ≥ C`

The possible-world provenance `F_C(U)` agrees with the join-based provenance
`S_C(U)` for all `C ≥ 1`, in any absorptive commutative m-semiring with
left-distributivity of `⊗` over `⊖`. Proof by induction on `U.card` driven
by the `FC_recurrence` and `SC_recurrence` recurrences; the `C = 1` base of
the recurrence (where `F α U' 0` and `S α U' 0` appear on the right-hand
side) is closed by the auxiliary fact `F_zero_eq_one`.
-/

/-- In an absorptive idempotent m-semiring, `F α U 0 = 𝟙`: the
unconstrained possible-world provenance collapses to `𝟙`. Lower bound
from `upward_expansion` with `V = ∅`; upper bound from `T α U W ≤ A α W`
and `A α W ≤ 𝟙` (the latter via `prod_le_one_absorptive`). -/
theorem F_zero_eq_one (h_idem : idempotent K) (h_abs : absorptive K)
    (α : ι → K) (U : Finset ι) : F α U 0 = 1 := by
  apply le_antisymm
  · -- F α U 0 ≤ 𝟙: every summand T α U W ≤ A α W ≤ 𝟙.
    simp only [F]
    have hfilter : U.powerset.filter (fun W => 0 ≤ W.card) = U.powerset := by
      ext W; simp
    rw [hfilter]
    apply sum_le_of_forall_le h_idem
    intro W _
    calc T α U W ≤ A α W := by unfold T; exact monus_le _ _
      _ ≤ 1 := prod_le_one_absorptive h_abs α W
  · -- 𝟙 ≤ F α U 0 by `upward_expansion` with V = ∅.
    have hAempty : A α (∅ : Finset ι) = 1 := by simp [A]
    have h := upward_expansion α h_idem U ∅ (Finset.empty_subset U)
    rw [hAempty] at h
    have hfilter_eq : U.powerset.filter ((∅ : Finset ι) ⊆ ·) =
        U.powerset.filter (fun W => 0 ≤ W.card) := by
      ext W; simp
    rw [hfilter_eq] at h
    exact h

/-- **Algebraic skeleton of Theorem 1(i)** for `HAVING count ≥ C`: in an
absorptive commutative m-semiring with `mul_sub_left_distributive`, the
possible-world provenance `F_C(U)` equals the join-based provenance
`S_C(U)` for all `C ≥ 1`. Absorptive is a strictly stronger hypothesis
than the bare "idempotent + distributive" combination one might wish for,
but it is what makes the `C = 1` base of the recurrence-driven induction
go through, via `F_zero_eq_one`. The absorptive hypothesis is essential:
`Provenance.Semirings.Tropical.TropicalQ.F_ne_S` exhibits a non-absorptive
(but idempotent and distributive) instance — `Tropical (WithTop ℚ)` — for
which the conclusion fails. The idempotent m-semirings in the library
with `mul_sub_left_distributive` that *are* absorptive (Bool, BoolFunc,
IntervalUnion, `Tropical (WithTop ℕ)`, Viterbi, Łukasiewicz) all satisfy
the conclusion. -/
theorem F_eq_S (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) (U : Finset ι) (C : ℕ) :
    F α U (C + 1) = S α U (C + 1) := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  suffices h : ∀ n : ℕ, ∀ U' : Finset ι, U'.card = n →
      ∀ C : ℕ, F α U' (C + 1) = S α U' (C + 1) from
    h U.card U rfl C
  intro n
  induction n with
  | zero =>
    intro U' hU' C
    have hUempty : U' = ∅ := Finset.card_eq_zero.mp hU'
    subst hUempty
    have hF : F α (∅ : Finset ι) (C + 1) = 0 := by
      unfold F
      have : ((∅ : Finset ι).powerset.filter (fun W => C + 1 ≤ W.card)) = ∅ := by
        ext W
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty,
                   Finset.notMem_empty, iff_false, not_and]
        intro hW
        subst hW
        simp
      rw [this, Finset.sum_empty]
    have hS : S α (∅ : Finset ι) (C + 1) = 0 := by
      unfold S
      have : ((∅ : Finset ι).powersetCard (C + 1)) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      rw [this, Finset.sum_empty]
    rw [hF, hS]
  | succ n ih =>
    intro U' hU' C
    obtain ⟨u, hu⟩ : U'.Nonempty := Finset.card_pos.mp (hU' ▸ Nat.succ_pos _)
    have hcard' : (U'.erase u).card = n := by
      rw [Finset.card_erase_of_mem hu, hU']; omega
    rw [FC_recurrence α h_idem h_distrib hu C, SC_recurrence α hu C]
    congr 1
    · exact ih (U'.erase u) hcard' C
    · cases C with
      | zero =>
        rw [F_zero_eq_one h_idem h_abs α (U'.erase u)]
        have hS0 : S α (U'.erase u) 0 = 1 := by
          simp only [S, Finset.powersetCard_zero, Finset.sum_singleton,
                     A, Finset.prod_empty]
        rw [hS0]
      | succ C' =>
        rw [ih (U'.erase u) hcard' C']

end Having
