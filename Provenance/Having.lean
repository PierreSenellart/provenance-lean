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

The main results are the bounding lemma `A_V ≤ ⊕_{V ⊆ W ⊆ U} T_U(W)` in an
idempotent m-semiring (`upward_expansion`), the collapse of the `T`-weighted
sum over any upward-closed family of worlds to the `A`-weighted sum over its
minimal elements in an absorptive m-semiring (`upward_closed_collapse`, with
`F_eq_S` as the `HAVING count ≥ C` instance), include/exclude-style
recurrences for `S` and `F`, and the per-world bound `world_bound` behind the
`=` and `≤` cases.
-/

namespace Having

open Finset

variable {ι : Type} [DecidableEq ι]
variable {K : Type} [CommSemiringWithMonus K]

/-- Monomial annotation of a subset: `A_W = ∏_{x ∈ W} α x`, with the
convention `A_∅ = 𝟙`. -/
def A (α : ι → K) (W : Finset ι) : K :=
  ∏ x ∈ W, α x

/-- `T_U(W) = A_W ⊖ ⊕_{x ∈ U \ W} A_{W ∪ {x}}`: the “exactly-`W`” contribution
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
theorem sum_le_of_forall_le (h_idem : idempotent K)
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
theorem mul_le_mul_left_canonical (a : K) {b c : K} (h : b ≤ c) :
    a * b ≤ a * c := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [mul_add]
  exact le_self_add

/-- In an absorptive `CommSemiringWithMonus`, any finite product of
annotations is bounded above by `𝟙`. -/
theorem prod_le_one_absorptive (h_abs : absorptive K) (α : ι → K) :
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
theorem A_le_of_subset_absorptive (h_abs : absorptive K) (α : ι → K)
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

/-- **Upward-closed collapse of the possible-world provenance.** In an
absorptive commutative m-semiring, the `⊕`-sum of the world annotations
`T_U(W)` over an upward-closed family `F` of subsets of `U` equals the
`⊕`-sum of the *monomials* `A_V` over any subfamily `M ⊆ F` such that every
element of `F` contains some element of `M` (canonically, the minimal
elements of `F`).

Unlike `absorbing_subfamily`, which relates two `A`-weighted sums, this is
the statement needed to collapse a possible-world provenance (a `T`-weighted
sum): the `≤` half bounds each `T_U(W) ≤ A_W ≤ A_V` (by `monus_le` and
`A_le_of_subset_absorptive`), and the `≥` half recovers each `A_V` from
`upward_expansion`, whose index set is contained in `F` by upward closure.
Note that `mul_sub_left_distributive` is *not* needed. -/
theorem upward_closed_collapse (α : ι → K) (h_abs : absorptive K)
    {U : Finset ι} {F M : Finset (Finset ι)}
    (hFU : ∀ W ∈ F, W ⊆ U)
    (hF_up : ∀ W ∈ F, ∀ W' : Finset ι, W ⊆ W' → W' ⊆ U → W' ∈ F)
    (hM_sub : M ⊆ F)
    (hcover : ∀ W ∈ F, ∃ V ∈ M, V ⊆ W) :
    ∑ W ∈ F, T α U W = ∑ V ∈ M, A α V := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  apply le_antisymm
  · refine sum_le_of_forall_le h_idem fun W hW => ?_
    obtain ⟨V, hVM, hVW⟩ := hcover W hW
    calc T α U W ≤ A α W := monus_le _ _
      _ ≤ A α V := A_le_of_subset_absorptive h_abs α hVW
      _ ≤ ∑ V' ∈ M, A α V' :=
        Finset.single_le_sum_of_canonicallyOrdered (f := A α) hVM
  · refine sum_le_of_forall_le h_idem fun V hVM => ?_
    have hVF : V ∈ F := hM_sub hVM
    calc A α V ≤ ∑ W ∈ U.powerset.filter (V ⊆ ·), T α U W :=
        upward_expansion α h_idem U V (hFU V hVF)
      _ ≤ ∑ W ∈ F, T α U W := by
        refine Finset.sum_le_sum_of_subset fun W hW => ?_
        rw [Finset.mem_filter, Finset.mem_powerset] at hW
        exact hF_up V hVF W hW.2 hW.1

/-! ### F equals S: algebraic skeleton of `HAVING count ≥ C`

The possible-world provenance `F_C(U)` agrees with the join-based provenance
`S_C(U)` for all `C ≥ 1`, in any absorptive commutative m-semiring: the family
of worlds of cardinality `≥ C` is upward-closed with the worlds of cardinality
exactly `C` as minimal elements, so `upward_closed_collapse` applies. An
alternative, recurrence-driven proof goes through `FC_recurrence` and
`SC_recurrence` (with `F_zero_eq_one` closing the `C = 1` base), at the price
of the additional `mul_sub_left_distributive` hypothesis used by
`FC_recurrence`; the recurrences are kept as results of independent interest.
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

/-- **Algebraic skeleton** for `HAVING count ≥ C`: in an absorptive
commutative m-semiring, the possible-world provenance `F_C(U)` equals the
join-based provenance `S_C(U)` for all `C ≥ 1`. This is the instance of
`upward_closed_collapse` for the upward-closed family of worlds of
cardinality `≥ C`, whose minimal elements are the worlds of cardinality
exactly `C`; in particular `mul_sub_left_distributive` is *not* needed
(it re-enters only when relating `T` to the factored form of the world
annotation, see `T_eq_mul_one_monus_sum`). Absorptive is a strictly
stronger hypothesis than the bare “idempotent + distributive” combination
one might wish for, and it is essential:
`Provenance.Semirings.Tropical.TropicalR.F_ne_S` exhibits a non-absorptive
(but idempotent and distributive) instance – `Tropical (WithTop ℝ)` – for
which the conclusion fails. The idempotent m-semirings in the library
that *are* absorptive (Bool, BoolFunc, IntervalUnion,
`Tropical (WithTop ℕ)`, Viterbi, Łukasiewicz, MinMax) all satisfy
the conclusion. -/
theorem F_eq_S (h_abs : absorptive K)
    (α : ι → K) (U : Finset ι) (C : ℕ) :
    F α U (C + 1) = S α U (C + 1) := by
  show ∑ W ∈ U.powerset.filter (fun W => C + 1 ≤ W.card), T α U W
    = ∑ V ∈ U.powersetCard (C + 1), A α V
  refine upward_closed_collapse α h_abs ?_ ?_ ?_ ?_
  · exact fun W hW => Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
  · intro W hW W' hWW' hW'U
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hW'U,
      (Finset.mem_filter.mp hW).2.trans (Finset.card_le_card hWW')⟩
  · intro V hV
    obtain ⟨hVU, hVcard⟩ := Finset.mem_powersetCard.mp hV
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hVU, le_of_eq hVcard.symm⟩
  · intro W hW
    obtain ⟨hWU, hWcard⟩ := Finset.mem_filter.mp hW
    obtain ⟨V, hVW, hVcard⟩ := Finset.exists_subset_card_eq hWcard
    exact ⟨V, Finset.mem_powersetCard.mpr
      ⟨hVW.trans (Finset.mem_powerset.mp hWU), hVcard⟩, hVW⟩

/-! ### The `=` and `≤` cases

`F_eq_S` settles `HAVING count ≥ C`. The `=` and `≤` cases do not follow from
it formally; both rest on the per-world upper bound `world_bound` below.
-/

/-- **Per-world upper bound.** For `j ≤ |W| ≤ C`, the annotation of a
single world `W` is already below `S_j(U) ⊖ S_{C+1}(U)`.

The order of the steps matters: bounding `A_W` by `S_j(U)` inside the
subtrahend of `T_U(W) = A_W ⊖ (A_W ⊗ E_W)` would move the monus the wrong way.
The bound is applied instead to the factored form `T_U(W) = A_W ⊗ (𝟙 ⊖ E_W)`,
whose second factor does not mention `A_W`.

Unlike for `F_eq_S`, the `mul_sub_left_distributive` hypothesis here is
essential and not an artifact of the proof:
`Provenance.Semirings.ChainFive.ChainFive.not_world_bound` exhibits an
absorptive commutative m-semiring without it in which the conclusion fails
(and with it the conclusions of `G_eq_S_monus_S` and `atMost_eq_S_monus_S`,
which rest on this bound). -/
theorem world_bound (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) {U W : Finset ι} (hWU : W ⊆ U) {j C : ℕ}
    (hjW : j ≤ W.card) (hWC : W.card ≤ C) :
    T α U W ≤ S α U j - S α U (C + 1) := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  -- (1) `A_W ≤ S_j(U)`: shrink `W` to a `j`-subset, which is a summand of `S_j(U)`.
  obtain ⟨W', hW'W, hW'card⟩ := Finset.exists_subset_card_eq hjW
  have hAW : A α W ≤ S α U j :=
    le_trans (A_le_of_subset_absorptive h_abs α hW'W)
      (Finset.single_le_sum (f := fun V => A α V) (fun _ _ => zero_le)
        (Finset.mem_powersetCard.mpr ⟨hW'W.trans hWU, hW'card⟩))
  -- (2) `S_{C+1}(U) ≤ S_j(U) ⊗ E_W`.
  have hS : S α U (C + 1) ≤ S α U j * ∑ x ∈ U \ W, α x := by
    refine sum_le_of_forall_le h_idem ?_
    intro V hV
    obtain ⟨hVU, hVcard⟩ := Finset.mem_powersetCard.mp hV
    have hcard : W.card < V.card := by omega
    obtain ⟨v, hvV, hvW⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hverase : j ≤ (V.erase v).card := by
      rw [Finset.card_erase_of_mem hvV]; omega
    obtain ⟨V', hV'sub, hV'card⟩ := Finset.exists_subset_card_eq hverase
    have hvV' : v ∉ V' := fun h => Finset.notMem_erase v V (hV'sub h)
    have hsub : insert v V' ⊆ V :=
      Finset.insert_subset hvV (hV'sub.trans (Finset.erase_subset _ _))
    have hAV' : A α V' ≤ S α U j :=
      Finset.single_le_sum (f := fun X => A α X) (fun _ _ => zero_le)
        (Finset.mem_powersetCard.mpr
          ⟨(hV'sub.trans (Finset.erase_subset _ _)).trans hVU, hV'card⟩)
    have hαv : α v ≤ ∑ x ∈ U \ W, α x :=
      Finset.single_le_sum (f := fun x => α x) (fun _ _ => zero_le)
        (Finset.mem_sdiff.mpr ⟨hVU hvV, hvW⟩)
    calc A α V ≤ A α (insert v V') := A_le_of_subset_absorptive h_abs α hsub
      _ = α v * A α V' := by simp only [A, Finset.prod_insert hvV']
      _ ≤ α v * S α U j := mul_le_mul_left_canonical _ hAV'
      _ = S α U j * α v := mul_comm _ _
      _ ≤ S α U j * ∑ x ∈ U \ W, α x := mul_le_mul_left_canonical _ hαv
  calc T α U W = A α W * (1 - ∑ x ∈ U \ W, α x) := T_eq_mul_one_monus_sum α h_distrib U W
    _ = (1 - ∑ x ∈ U \ W, α x) * A α W := mul_comm _ _
    _ ≤ (1 - ∑ x ∈ U \ W, α x) * S α U j := mul_le_mul_left_canonical _ hAW
    _ = S α U j * (1 - ∑ x ∈ U \ W, α x) := mul_comm _ _
    _ = S α U j - S α U j * ∑ x ∈ U \ W, α x := by rw [h_distrib, mul_one]
    _ ≤ S α U j - S α U (C + 1) := monus_antitone hS _

/-- `G_C(U) = ⊕_{W ⊆ U, |W| = C} T_U(W)`: the possible-world provenance of a
`HAVING count = C` predicate. -/
def G (α : ι → K) (U : Finset ι) (C : ℕ) : K :=
  ∑ W ∈ U.powersetCard C, T α U W

/-- Monus distributes over a finite sum with a fixed subtrahend: the `Finset`
form of `add_monus_of_idempotent`. -/
theorem sum_monus {ι' : Type} [DecidableEq ι'] (h_idem : idempotent K)
    (s : Finset ι') (f : ι' → K) (c : K) :
    (∑ x ∈ s, f x) - c = ∑ x ∈ s, (f x - c) := by
  induction s using Finset.induction with
  | empty => simp [zero_monus]
  | insert x t hxt ih =>
      rw [Finset.sum_insert hxt, Finset.sum_insert hxt, add_monus_of_idempotent h_idem, ih]

/-- `a ≤ b` forces `a ⊖ b = 𝟘`. -/
private theorem monus_eq_zero_of_le {a b : K} (h : a ≤ b) : a - b = 0 :=
  le_antisymm ((SemiringWithMonus.monus_spec a b 0).mpr (by simpa using h)) zero_le

/-- A world of size at least `C + 1` is dominated by `S_{C+1}(U)`. -/
private theorem T_le_S_of_card_le (h_abs : absorptive K) (α : ι → K)
    {U W : Finset ι} (hWU : W ⊆ U) {C : ℕ} (hW : C + 1 ≤ W.card) :
    T α U W ≤ S α U (C + 1) := by
  obtain ⟨W', hW'W, hW'card⟩ := Finset.exists_subset_card_eq hW
  exact le_trans (monus_le _ _)
    (le_trans (A_le_of_subset_absorptive h_abs α hW'W)
      (Finset.single_le_sum (f := fun V => A α V) (fun _ _ => zero_le)
        (Finset.mem_powersetCard.mpr ⟨hW'W.trans hWU, hW'card⟩)))

/-- **The `=` case.** The possible-world provenance of `HAVING count = C`
is the join-side difference `S_C(U) ⊖ S_{C+1}(U)`. This does not follow from
`F_eq_S`; the `≤` half is `world_bound` and the `≥` half replaces the
subtrahend of each `T_U(W)` by the larger `S_{C+1}(U)`. -/
theorem G_eq_S_monus_S (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) (U : Finset ι) (C : ℕ) :
    G α U C = S α U C - S α U (C + 1) := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  refine le_antisymm ?_ ?_
  · refine sum_le_of_forall_le h_idem fun W hW => ?_
    obtain ⟨hWU, hWcard⟩ := Finset.mem_powersetCard.mp hW
    exact world_bound h_abs h_distrib α hWU (le_of_eq hWcard.symm) (le_of_eq hWcard)
  · rw [S, sum_monus h_idem]
    refine Finset.sum_le_sum fun W hW => ?_
    obtain ⟨hWU, hWcard⟩ := Finset.mem_powersetCard.mp hW
    have hP : ∑ x ∈ U \ W, A α (insert x W) ≤ S α U (C + 1) := by
      refine sum_le_of_forall_le h_idem fun x hx => ?_
      obtain ⟨hxU, hxW⟩ := Finset.mem_sdiff.mp hx
      exact Finset.single_le_sum (f := fun V => A α V) (fun _ _ => zero_le)
        (Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hxU hWU, by
          rw [Finset.card_insert_of_notMem hxW, hWcard]⟩)
    exact monus_antitone hP _

/-- **The `≤` case.** The possible-world provenance of `HAVING count ≤ C` on
non-empty worlds is `S_1(U) ⊖ S_{C+1}(U)`. -/
theorem atMost_eq_S_monus_S (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) (U : Finset ι) (C : ℕ) :
    ∑ W ∈ U.powerset.filter (fun W => 1 ≤ W.card ∧ W.card ≤ C), T α U W
      = S α U 1 - S α U (C + 1) := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  refine le_antisymm ?_ ?_
  · refine sum_le_of_forall_le h_idem fun W hW => ?_
    obtain ⟨hWU, h1, h2⟩ := Finset.mem_filter.mp hW
    exact world_bound h_abs h_distrib α (Finset.mem_powerset.mp hWU) h1 h2
  · have hF : F α U 1 = S α U 1 := F_eq_S h_abs α U 0
    rw [← hF, F, sum_monus h_idem]
    have hsub : ∑ W ∈ U.powerset.filter (fun W => 1 ≤ W.card ∧ W.card ≤ C),
          (T α U W - S α U (C + 1))
        = ∑ W ∈ U.powerset.filter (fun W => 1 ≤ W.card), (T α U W - S α U (C + 1)) := by
      refine Finset.sum_subset (fun W hW => ?_) (fun W hW hW' => ?_)
      · obtain ⟨hWU, h1, -⟩ := Finset.mem_filter.mp hW
        exact Finset.mem_filter.mpr ⟨hWU, h1⟩
      · obtain ⟨hWU, h1⟩ := Finset.mem_filter.mp hW
        have h2 : C + 1 ≤ W.card := by
          by_contra hc
          exact hW' (Finset.mem_filter.mpr ⟨hWU, h1, by omega⟩)
        exact monus_eq_zero_of_le
          (T_le_S_of_card_le h_abs α (Finset.mem_powerset.mp hWU) h2)
    rw [← hsub]
    exact Finset.sum_le_sum fun W _ => monus_le _ _

/-! ### Collapse to minimal worlds, and the size of the index sets

`upward_closed_collapse` specialises to any family of worlds cut out by a
superset-monotone predicate: the provenance collapses to the `⊕`-sum of the
monomials of the *minimal* valid worlds. For `SUM(t) op c` predicates over
`ℕ`-weights with `op ∈ {≥, >}`, a bounded-ratio hypothesis on the weights
(`c ≤ k ⊗ t i` for every occurrence) bounds the size of the minimal worlds
by `k` (resp. `k + 1`), so the collapsed sum ranges over an index set of at
most `∑_{i ≤ k} C(|U|, i)` terms. The cardinality facts are stated as
`Finset.card` statements about the index sets of the sums; they say nothing
about running time. -/

/-- Minimality of a world with respect to a predicate is decidable: only
the subsets of the world need inspecting. -/
instance decidableMinimal {P : Finset ι → Prop} [DecidablePred P] (V : Finset ι) :
    Decidable (∀ V' ⊂ V, ¬ P V') :=
  decidable_of_iff (∀ V' ∈ V.powerset, V' ≠ V → ¬ P V') <| by
    constructor
    · intro h V' hss
      exact h V' (Finset.mem_powerset.mpr hss.subset)
        (Finset.ssubset_iff_subset_ne.mp hss).2
    · intro h V' hV' hne
      exact h V' (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hV', hne⟩)

omit [DecidableEq ι] in
/-- Every world satisfying `P` contains a world satisfying `P` that is
minimal among **all** worlds (not merely among its own subsets). Strong
induction on the cardinality. -/
theorem exists_minimal_subset {P : Finset ι → Prop} :
    ∀ {W : Finset ι}, P W → ∃ V, V ⊆ W ∧ P V ∧ ∀ V' ⊂ V, ¬ P V' := by
  suffices h : ∀ n : ℕ, ∀ W : Finset ι, W.card ≤ n → P W →
      ∃ V, V ⊆ W ∧ P V ∧ ∀ V' ⊂ V, ¬ P V' from
    fun {W} hW => h W.card W le_rfl hW
  intro n
  induction n with
  | zero =>
    intro W hcard hW
    have hempty : W = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hempty
    exact ⟨∅, Finset.Subset.refl _, hW,
      fun V' hV' => absurd hV' (Finset.not_ssubset_empty V')⟩
  | succ n ih =>
    intro W hcard hW
    by_cases hex : ∃ V' ⊂ W, P V'
    · obtain ⟨V', hss, hPV'⟩ := hex
      have hcard' : V'.card ≤ n :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.card_lt_card hss) hcard)
      obtain ⟨V, hVV', hPV, hmin⟩ := ih V' hcard' hPV'
      exact ⟨V, hVV'.trans hss.subset, hPV, hmin⟩
    · push Not at hex
      exact ⟨W, Finset.Subset.refl _, hW, hex⟩

/-- **Collapse to minimal worlds.** In an absorptive commutative
m-semiring, for any predicate `P` on worlds that is monotone under
supersets, the `T`-weighted possible-world provenance of the valid worlds
inside `U` collapses to the `⊕`-sum of the monomials of the minimal valid
worlds. This is the workhorse behind the tractable `COUNT ≥` and bounded-
ratio `SUM ≥ / >` cases. -/
theorem collapse_to_minimal (α : ι → K) (h_abs : absorptive K)
    (U : Finset ι) {P : Finset ι → Prop} [DecidablePred P]
    (hmono : ∀ ⦃W W'⦄, W ⊆ W' → P W → P W') :
    ∑ W ∈ U.powerset.filter P, T α U W
      = ∑ V ∈ (U.powerset.filter P).filter (fun V => ∀ V' ⊂ V, ¬ P V'), A α V := by
  refine upward_closed_collapse α h_abs ?_ ?_ (Finset.filter_subset _ _) ?_
  · exact fun W hW => Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
  · intro W hW W' hWW' hW'U
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hW'U,
      hmono hWW' (Finset.mem_filter.mp hW).2⟩
  · intro W hW
    obtain ⟨hWU, hPW⟩ := Finset.mem_filter.mp hW
    obtain ⟨V, hVW, hPV, hmin⟩ := exists_minimal_subset hPW
    exact ⟨V, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (hVW.trans (Finset.mem_powerset.mp hWU)), hPV⟩,
       hmin⟩, hVW⟩

/-- **`HAVING SUM(t) ≥ c` collapse.** Instance of `collapse_to_minimal`
for the superset-monotone predicate `c ≤ ∑_{i ∈ W} t i` over `ℕ`-weights. -/
theorem sum_ge_collapse (α : ι → K) (h_abs : absorptive K)
    (U : Finset ι) (t : ι → ℕ) (c : ℕ) :
    ∑ W ∈ U.powerset.filter (fun W => c ≤ ∑ i ∈ W, t i), T α U W
      = ∑ V ∈ (U.powerset.filter (fun W => c ≤ ∑ i ∈ W, t i)).filter
          (fun V => ∀ V' ⊂ V, ¬ (c ≤ ∑ i ∈ V', t i)), A α V :=
  collapse_to_minimal α h_abs U fun _ _ hss h =>
    h.trans (Finset.sum_le_sum_of_subset hss)

/-- **`HAVING SUM(t) > c` collapse.** As `sum_ge_collapse`, for the strict
comparison. -/
theorem sum_gt_collapse (α : ι → K) (h_abs : absorptive K)
    (U : Finset ι) (t : ι → ℕ) (c : ℕ) :
    ∑ W ∈ U.powerset.filter (fun W => c < ∑ i ∈ W, t i), T α U W
      = ∑ V ∈ (U.powerset.filter (fun W => c < ∑ i ∈ W, t i)).filter
          (fun V => ∀ V' ⊂ V, ¬ (c < ∑ i ∈ V', t i)), A α V :=
  collapse_to_minimal α h_abs U fun _ _ hss h =>
    lt_of_lt_of_le h (Finset.sum_le_sum_of_subset hss)

omit [DecidableEq ι] in
/-- **Bounded ratio bounds the minimal worlds of `SUM(t) ≥ c`.** If every
occurrence of the group *with a nonzero value* satisfies `c ≤ k ⊗ t i`
(read: `c / t i ≤ k`), then any minimal world with `∑ t ≥ c` has at most
`k` occurrences: a zero-valued occurrence never belongs to a minimal
world (removing it leaves the sum unchanged), and any `k`-subset of
nonzero values already reaches the threshold. -/
theorem minimal_card_le_of_sum_ge {t : ι → ℕ} {c k : ℕ} {U W : Finset ι}
    (hratio : ∀ i ∈ U, t i ≠ 0 → c ≤ k * t i) (hWU : W ⊆ U)
    (_hW : c ≤ ∑ i ∈ W, t i) (hmin : ∀ W' ⊂ W, ¬ (c ≤ ∑ i ∈ W', t i)) :
    W.card ≤ k := by
  classical
  have hWnz : ∀ i ∈ W, t i ≠ 0 := by
    intro i hiW hti
    refine hmin (W.erase i) (Finset.erase_ssubset hiW) ?_
    calc c ≤ ∑ j ∈ W, t j := _hW
      _ = ∑ j ∈ W.erase i, t j := by
          rw [← Finset.add_sum_erase W t hiW, hti, Nat.zero_add]
  by_contra hcard
  push Not at hcard
  obtain ⟨W', hW'W, hW'card⟩ := Finset.exists_subset_card_eq (le_of_lt hcard)
  have hss : W' ⊂ W := Finset.ssubset_iff_subset_ne.mpr
    ⟨hW'W, fun h => by rw [h] at hW'card; omega⟩
  refine hmin W' hss ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨i, hiW⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
    have := hratio i (hWU hiW) (hWnz i hiW)
    omega
  · have hsum : k * c ≤ k * ∑ i ∈ W', t i := by
      calc k * c = ∑ _i ∈ W', c := by
            rw [Finset.sum_const_nat fun _ _ => rfl, hW'card]
        _ ≤ ∑ i ∈ W', k * t i := Finset.sum_le_sum fun i hi =>
            hratio i (hWU (hW'W hi)) (hWnz i (hW'W hi))
        _ = k * ∑ i ∈ W', t i := (Finset.mul_sum _ _ _).symm
    exact Nat.le_of_mul_le_mul_left hsum hk

omit [DecidableEq ι] in
/-- **Bounded ratio bounds the minimal worlds of `SUM(t) > c`.** If every
occurrence of the group *with a nonzero value* satisfies `c ≤ k ⊗ t i`,
then any minimal world with `∑ t > c` has at most `k + 1` occurrences: a
zero-valued occurrence never belongs to a minimal world, `k` nonzero
values reach `c`, and one further nonzero value makes the comparison
strict (which also covers the boundary case `c = 0`). -/
theorem minimal_card_le_of_sum_gt {t : ι → ℕ} {c k : ℕ} {U W : Finset ι}
    (hratio : ∀ i ∈ U, t i ≠ 0 → c ≤ k * t i) (hWU : W ⊆ U)
    (_hW : c < ∑ i ∈ W, t i) (hmin : ∀ W' ⊂ W, ¬ (c < ∑ i ∈ W', t i)) :
    W.card ≤ k + 1 := by
  classical
  have hWnz : ∀ i ∈ W, t i ≠ 0 := by
    intro i hiW hti
    refine hmin (W.erase i) (Finset.erase_ssubset hiW) ?_
    calc c < ∑ j ∈ W, t j := _hW
      _ = ∑ j ∈ W.erase i, t j := by
          rw [← Finset.add_sum_erase W t hiW, hti, Nat.zero_add]
  by_contra hcard
  push Not at hcard
  obtain ⟨W', hW'W, hW'card⟩ := Finset.exists_subset_card_eq (le_of_lt hcard)
  have hss : W' ⊂ W := Finset.ssubset_iff_subset_ne.mpr
    ⟨hW'W, fun h => by rw [h] at hW'card; omega⟩
  refine hmin W' hss ?_
  obtain ⟨i, hiW'⟩ := Finset.card_pos.mp (show 0 < W'.card by omega)
  have hipos : 0 < t i := Nat.pos_of_ne_zero (hWnz i (hW'W hiW'))
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact lt_of_lt_of_le hipos
      (Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _) hiW')
  · by_contra hnot
    push Not at hnot
    have h1 : (k + 1) * c ≤ k * ∑ i ∈ W', t i := by
      calc (k + 1) * c = ∑ _i ∈ W', c := by
            rw [Finset.sum_const_nat fun _ _ => rfl, hW'card]
        _ ≤ ∑ j ∈ W', k * t j :=
            Finset.sum_le_sum fun j hj =>
              hratio j (hWU (hW'W hj)) (hWnz j (hW'W hj))
        _ = k * ∑ i ∈ W', t i := (Finset.mul_sum _ _ _).symm
    have h2 : k * ∑ i ∈ W', t i ≤ k * c := Nat.mul_le_mul_left k hnot
    have h13 := h1.trans h2
    rw [Nat.add_mul, Nat.one_mul] at h13
    omega

/-- **Size of the `COUNT ≤ k` index set**: the worlds of cardinality at
most `k` inside `U` number `∑_{i ≤ k} C(|U|, i)`. This is a statement about
the number of terms of the possible-world `⊕`-sum, not about running
time. -/
theorem card_powerset_filter_card_le (U : Finset ι) (k : ℕ) :
    (U.powerset.filter (fun W => W.card ≤ k)).card
      = ∑ i ∈ Finset.range (k + 1), U.card.choose i := by
  have hpart : U.powerset.filter (fun W => W.card ≤ k)
      = (Finset.range (k + 1)).biUnion (fun i => U.powersetCard i) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hWU, hcard⟩
      exact ⟨W.card, by omega, hWU, rfl⟩
    · rintro ⟨i, hik, hWU, hcard⟩
      exact ⟨hWU, by omega⟩
  rw [hpart, Finset.card_biUnion (fun i _ j _ hij => ?_)]
  · exact Finset.sum_congr rfl fun i _ => Finset.card_powersetCard i U
  · show Disjoint (Finset.powersetCard i U) (Finset.powersetCard j U)
    rw [Finset.disjoint_left]
    intro W hW hW'
    rw [Finset.mem_powersetCard] at hW hW'
    exact hij (by rw [← hW.2, hW'.2])

/-- **Size of the collapsed `SUM(t) ≥ c` index set** under the bounded-
ratio hypothesis: the minimal valid worlds number at most
`∑_{i ≤ k} C(|U|, i)`. -/
theorem card_minimal_sum_ge_le (U : Finset ι) (t : ι → ℕ) {c k : ℕ}
    (hratio : ∀ i ∈ U, t i ≠ 0 → c ≤ k * t i) :
    ((U.powerset.filter (fun W => c ≤ ∑ i ∈ W, t i)).filter
        (fun V => ∀ V' ⊂ V, ¬ (c ≤ ∑ i ∈ V', t i))).card
      ≤ ∑ i ∈ Finset.range (k + 1), U.card.choose i := by
  rw [← card_powerset_filter_card_le U k]
  refine Finset.card_le_card fun W hW => ?_
  obtain ⟨hWF, hmin⟩ := Finset.mem_filter.mp hW
  obtain ⟨hWU, hsum⟩ := Finset.mem_filter.mp hWF
  exact Finset.mem_filter.mpr ⟨hWU,
    minimal_card_le_of_sum_ge hratio (Finset.mem_powerset.mp hWU) hsum hmin⟩

end Having
