/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Algorithms.CompOp
import Provenance.Having

set_option linter.unusedSectionVars false

/-!
# Scan-computable HAVING provenance for `MIN`, `MAX` and `PICKFIRST`

For a `HAVING` predicate comparing an aggregate to a constant, the
possible-world semantics sums the world annotations `T_U(W)` over the
non-empty valid worlds `W ⊆ U` of a group, of which there are in general
exponentially many. This file shows that for the aggregates `MIN`, `MAX` and
`PICKFIRST` – those whose validity is decided occurrence by occurrence – that
sum collapses, in an *absorptive* commutative m-semiring, to a closed form
using `O(|U|)` semiring operations: the provenance is obtained by a single
scan over the occurrences of the group, hence in polynomial time in data
complexity.

## The collapse

Everything rests on one identity, `meet_family_eq`: for `H ⊆ G ⊆ U`,

`⊕_{W ⊆ G, W ∩ H ≠ ∅} T_U(W) = (𝟙 ⊖ ⊕_{x ∈ U \ G} α x) ⊗ (⊕_{i ∈ H} α i)`,

i.e. the provenance of “the world stays inside `G` and meets `H`” is the
product of two running sums. Both hypotheses of the absorptive setting are
used: `≤` follows from `A_W ≤ α i ≤ ⊕_H α` (absorptivity makes `A` decreasing
under inclusion), and `≥` from `upward_expansion` in the universe `G`,
transported to `U` by `T_eq_T_of_subset` and `sum_monus`.

## Where the hypotheses are used

Absorptivity makes `A` decreasing under inclusion (`A_le_of_subset_absorptive`)
and is used in both halves. `mul_sub_left_distributive` is used exactly twice:
in the `≤` half, to pass from `T_U(W)` – defined in `Provenance.Having` as
`A_W ⊖ ⊕_x A_{W ∪ {x}}` – to the factored form `A_W ⊗ (𝟙 ⊖ ⊕_{U∖W} α)` in which
the possible-world semantics is stated; and in the `≥` half, to rewrite the
right-hand side as `⊕_H α ⊖ (⊕_H α ⊗ ⊕_{U∖G} α)`, the shape `sum_monus` needs.
The first use is not a proof convenience: in `MaxMin TVL` (absorptive but not
`mul_sub_left_distributive`) the identity is false for `T` as defined here –
`U = {1,2}`, `G = H = {1}` and `α₁ = α₂ = unknown` give `𝟘` on the left and
`unknown` on the right – because that is precisely where the two forms of the
world annotation part company.

The six comparison operators then instantiate this with the right pair
`(G, H)`; e.g. `MIN(t) ≥ c` keeps the worlds inside `G = {i | t i ≥ c}`, while
`MIN(t) ≤ c` keeps the worlds meeting `H = {i | t i ≤ c}`, and `MIN(t) = c`
uses both. `PICKFIRST` splits the worlds according to their first occurrence
and applies the identity to each fiber.

## Main results

* `meet_family_eq` – the collapse identity;
* `prov_eq_of_pointwise` – its reading as a selection predicate decided
  occurrence by occurrence;
* `minScan` / `minScan_correct`, `maxScan` / `maxScan_correct`,
  `firstScan` / `firstScan_correct` – the three scans and their correctness,
  for all six comparison operators.

Unlike the `COUNT`/`SUM` cases, no world enumeration is involved: the scans
are closed forms, and the absorptivity hypothesis is what makes them exist
(in `ℕ[X]`, for instance, the same provenance is a product rather than a
sum of annotations).
-/

/-- Comparisons are unchanged by the embedding of the value domain into
`WithTop` (used to give the empty world an aggregate value). -/
@[simp] theorem CompOp.eval_coe_withTop {V : Type} [LinearOrder V] (op : CompOp) (a b : V) :
    op.eval (a : WithTop V) (b : WithTop V) ↔ op.eval a b := by
  cases op <;> simp [CompOp.eval]

/-- Comparisons are unchanged by the embedding of the value domain into
`WithBot`. -/
@[simp] theorem CompOp.eval_coe_withBot {V : Type} [LinearOrder V] (op : CompOp) (a b : V) :
    op.eval (a : WithBot V) (b : WithBot V) ↔ op.eval a b := by
  cases op <;> simp [CompOp.eval]

namespace Having

open Finset

variable {ι : Type} [DecidableEq ι]
variable {K : Type} [CommSemiringWithMonus K]

/-- Monus is monotone in its first argument. -/
theorem monus_mono_left {a a' c : K} (h : a ≤ a') : a - c ≤ a' - c := by
  rw [SemiringWithMonus.monus_spec]
  exact h.trans (le_plus_monus a' c)

/-- The annotation of a world meeting `H` is bounded by `⊕_{i ∈ H} α i`. -/
theorem A_le_sum_of_meet (h_abs : absorptive K) (α : ι → K) {W H : Finset ι} {i : ι}
    (hiW : i ∈ W) (hiH : i ∈ H) : A α W ≤ ∑ j ∈ H, α j := by
  calc A α W ≤ A α {i} := A_le_of_subset_absorptive h_abs α (by simpa using hiW)
    _ = α i := by simp [A]
    _ ≤ ∑ j ∈ H, α j := Finset.single_le_sum_of_canonicallyOrdered (f := α) hiH

/-- Upper bound half of `meet_family_eq`. -/
theorem meet_family_le (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) {U G H : Finset ι} :
    ∑ W ∈ G.powerset.filter (fun W => (W ∩ H).Nonempty), T α U W
      ≤ (1 - ∑ x ∈ U \ G, α x) * ∑ i ∈ H, α i := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  refine sum_le_of_forall_le h_idem fun W hW => ?_
  obtain ⟨hWG, hmeet⟩ := Finset.mem_filter.mp hW
  obtain ⟨i, hi⟩ := hmeet
  have hWG' : W ⊆ G := Finset.mem_powerset.mp hWG
  have hAW : A α W ≤ ∑ j ∈ H, α j :=
    A_le_sum_of_meet h_abs α (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi).2
  have hSig : ∑ x ∈ U \ G, α x ≤ ∑ x ∈ U \ W, α x :=
    Finset.sum_le_sum_of_subset (Finset.sdiff_subset_sdiff (le_refl U) hWG')
  calc T α U W = A α W * (1 - ∑ x ∈ U \ W, α x) := T_eq_mul_one_monus_sum α h_distrib U W
    _ ≤ A α W * (1 - ∑ x ∈ U \ G, α x) := mul_le_mul_left_canonical _ (monus_antitone hSig 1)
    _ = (1 - ∑ x ∈ U \ G, α x) * A α W := mul_comm _ _
    _ ≤ (1 - ∑ x ∈ U \ G, α x) * ∑ i ∈ H, α i := mul_le_mul_left_canonical _ hAW

/-- Lower bound half in the special case `G = U`: every `α i`, `i ∈ H`, is
already reached by the worlds containing `i`. -/
theorem meet_family_self_ge (h_abs : absorptive K) (α : ι → K) {G H : Finset ι}
    (hHG : H ⊆ G) :
    ∑ i ∈ H, α i ≤ ∑ W ∈ G.powerset.filter (fun W => (W ∩ H).Nonempty), T α G W := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  refine sum_le_of_forall_le h_idem fun i hi => ?_
  have h1 : A α {i} ≤ ∑ W ∈ G.powerset.filter ({i} ⊆ ·), T α G W :=
    upward_expansion α h_idem G {i} (by simpa using hHG hi)
  have hsub : G.powerset.filter ({i} ⊆ ·) ⊆ G.powerset.filter (fun W => (W ∩ H).Nonempty) := by
    intro W hW
    rw [Finset.mem_filter] at hW ⊢
    refine ⟨hW.1, i, ?_⟩
    exact Finset.mem_inter.mpr ⟨by simpa using hW.2, hi⟩
  calc α i = A α {i} := by simp [A]
    _ ≤ ∑ W ∈ G.powerset.filter ({i} ⊆ ·), T α G W := h1
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- For a world `W ⊆ G ⊆ U`, passing from the universe `G` to the larger
universe `U` subtracts the annotations of the occurrences of `U \ G`. Only
`monus_add` and ordinary distributivity are used, not
`mul_sub_left_distributive`. -/
theorem T_eq_T_of_subset (α : ι → K)
    {U G W : Finset ι} (hGU : G ⊆ U) (hWG : W ⊆ G) :
    T α U W = T α G W - A α W * ∑ x ∈ U \ G, α x := by
  have hsplit : U \ W = (G \ W) ∪ (U \ G) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxU, hxW⟩
      by_cases hxG : x ∈ G
      · exact Or.inl ⟨hxG, hxW⟩
      · exact Or.inr ⟨hxU, hxG⟩
    · rintro (⟨hxG, hxW⟩ | ⟨hxU, hxG⟩)
      · exact ⟨hGU hxG, hxW⟩
      · exact ⟨hxU, fun h => hxG (hWG h)⟩
  have hdisj : Disjoint (G \ W) (U \ G) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_sdiff.mp hx).1
  -- The one-step extensions of `W` inside `U` split into those inside `G` and
  -- those by an occurrence of `U \ G`, the latter summing to `A_W ⊗ ⊕_{U∖G} α`.
  have hA : ∀ x ∈ U \ G, A α (insert x W) = A α W * α x := by
    intro x hx
    have hxW : x ∉ W := fun h => (Finset.mem_sdiff.mp hx).2 (hWG h)
    simp only [A, Finset.prod_insert hxW]
    exact mul_comm _ _
  have hsum : ∑ x ∈ U \ W, A α (insert x W)
      = (∑ x ∈ G \ W, A α (insert x W)) + A α W * ∑ x ∈ U \ G, α x := by
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_congr rfl hA, ← Finset.mul_sum]
  show A α W - _ = (A α W - _) - _
  rw [hsum, monus_add]

/-- **Core collapse.** In an absorptive m-semiring, the possible-world
provenance of the family of worlds that stay inside `G` and meet `H` is
`(𝟙 ⊖ ⊕_{x ∈ U \ G} α x) ⊗ (⊕_{i ∈ H} α i)`: two running sums, hence a single
scan over the occurrences of the group. -/
theorem meet_family_eq (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) {U G H : Finset ι} (hGU : G ⊆ U) (hHG : H ⊆ G) :
    ∑ W ∈ G.powerset.filter (fun W => (W ∩ H).Nonempty), T α U W
      = (1 - ∑ x ∈ U \ G, α x) * ∑ i ∈ H, α i := by
  have h_idem : idempotent K := idempotent_of_absorptive h_abs
  refine le_antisymm (meet_family_le h_abs h_distrib α) ?_
  have key : ∀ W ∈ G.powerset.filter (fun W => (W ∩ H).Nonempty),
      T α G W - (∑ i ∈ H, α i) * ∑ x ∈ U \ G, α x ≤ T α U W := by
    intro W hW
    obtain ⟨hWG, i, hi⟩ := Finset.mem_filter.mp hW
    have hAW : A α W ≤ ∑ j ∈ H, α j :=
      A_le_sum_of_meet h_abs α (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi).2
    rw [T_eq_T_of_subset α hGU (Finset.mem_powerset.mp hWG)]
    refine monus_antitone ?_ _
    calc A α W * ∑ x ∈ U \ G, α x
        = (∑ x ∈ U \ G, α x) * A α W := mul_comm _ _
      _ ≤ (∑ x ∈ U \ G, α x) * ∑ j ∈ H, α j := mul_le_mul_left_canonical _ hAW
      _ = (∑ j ∈ H, α j) * ∑ x ∈ U \ G, α x := mul_comm _ _
  calc (1 - ∑ x ∈ U \ G, α x) * ∑ i ∈ H, α i
      = (∑ i ∈ H, α i) * (1 - ∑ x ∈ U \ G, α x) := mul_comm _ _
    _ = (∑ i ∈ H, α i) - (∑ i ∈ H, α i) * ∑ x ∈ U \ G, α x := by rw [h_distrib, mul_one]
    _ ≤ (∑ W ∈ G.powerset.filter (fun W => (W ∩ H).Nonempty), T α G W)
          - (∑ i ∈ H, α i) * ∑ x ∈ U \ G, α x :=
        monus_mono_left (meet_family_self_ge h_abs α hHG)
    _ = ∑ W ∈ G.powerset.filter (fun W => (W ∩ H).Nonempty),
          (T α G W - (∑ i ∈ H, α i) * ∑ x ∈ U \ G, α x) := sum_monus h_idem _ _ _
    _ ≤ _ := Finset.sum_le_sum key

/-! ### Possible-world provenance of a selection predicate -/

/-- The possible-world provenance, at one group, of a selection predicate `P`
on worlds: the `⊕`-sum of the world annotations `T_U(W)` over the non-empty
worlds satisfying `P`, in the possible-world semantics of `HAVING`
predicates. -/
def prov (α : ι → K) (U : Finset ι) (P : Finset ι → Prop) [DecidablePred P] : K :=
  ∑ W ∈ U.powerset.filter (fun W => W.Nonempty ∧ P W), T α U W

/-- Two predicates that agree on the worlds of `U` have the same provenance. -/
theorem prov_congr (α : ι → K) (U : Finset ι) {P Q : Finset ι → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ W ⊆ U, (P W ↔ Q W)) :
    prov α U P = prov α U Q := by
  unfold prov
  refine Finset.sum_congr (Finset.filter_congr fun W hW => ?_) fun _ _ => rfl
  rw [h W (Finset.mem_powerset.mp hW)]

/-- The provenance of a disjunction of two mutually exclusive predicates is
the `⊕`-sum of the two provenances. -/
theorem prov_or (α : ι → K) (U : Finset ι) {P Q : Finset ι → Prop}
    [DecidablePred P] [DecidablePred Q] (hdisj : ∀ W, P W → Q W → False) :
    prov α U (fun W => P W ∨ Q W) = prov α U P + prov α U Q := by
  unfold prov
  have hsplit : U.powerset.filter (fun W => W.Nonempty ∧ (P W ∨ Q W))
      = U.powerset.filter (fun W => W.Nonempty ∧ P W)
        ∪ U.powerset.filter (fun W => W.Nonempty ∧ Q W) := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr fun W _ => ?_
    constructor
    · rintro ⟨hne, hPQ | hPQ⟩
      · exact Or.inl ⟨hne, hPQ⟩
      · exact Or.inr ⟨hne, hPQ⟩
    · rintro (⟨hne, hP⟩ | ⟨hne, hQ⟩)
      · exact ⟨hne, Or.inl hP⟩
      · exact ⟨hne, Or.inr hQ⟩
  rw [hsplit, Finset.sum_union]
  rw [Finset.disjoint_filter]
  exact fun W _ hP hQ => hdisj W hP.2 hQ.2

/-- Provenance of a predicate that splits into fibers indexed by a finite set:
if every non-empty world satisfying `R` satisfies `Q i` for exactly one `i ∈ P`,
the provenance of `R` is the `⊕`-sum of the provenances of the `Q i`. -/
theorem prov_fiber (α : ι → K) (U : Finset ι) (P : Finset ι) (Q : ι → Finset ι → Prop)
    [∀ i, DecidablePred (Q i)] {R : Finset ι → Prop} [DecidablePred R]
    (hR : ∀ W ⊆ U, (W.Nonempty ∧ R W ↔ ∃ i ∈ P, W.Nonempty ∧ Q i W))
    (hdisj : ∀ W : Finset ι, ∀ i ∈ P, ∀ j ∈ P, Q i W → Q j W → i = j) :
    prov α U R = ∑ i ∈ P, prov α U (Q i) := by
  have hfam : U.powerset.filter (fun W => W.Nonempty ∧ R W)
      = P.biUnion (fun i => U.powerset.filter (fun W => W.Nonempty ∧ Q i W)) := by
    ext W
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hWU, hne, hRW⟩
      obtain ⟨i, hiP, hne', hQ⟩ := (hR W hWU).mp ⟨hne, hRW⟩
      exact ⟨i, hiP, hWU, hne', hQ⟩
    · rintro ⟨i, hiP, hWU, hne, hQ⟩
      exact ⟨hWU, (hR W hWU).mpr ⟨i, hiP, hne, hQ⟩⟩
  have hpd : (↑P : Set ι).PairwiseDisjoint
      (fun i => U.powerset.filter (fun W => W.Nonempty ∧ Q i W)) := by
    intro i hi j hj hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro W hW hW'
    rw [Finset.mem_filter] at hW hW'
    exact hij (hdisj W i hi j hj hW.2.2 hW'.2.2)
  rw [prov, hfam, Finset.sum_biUnion hpd]
  rfl

/-- **Unsatisfiable predicates have provenance `𝟘`.** This is the
algebraic content of the range-check short-circuit of the enumeration
algorithms: when no world can satisfy the predicate, the possible-world
`⊕`-sum is empty. No hypothesis on the m-semiring is needed. -/
theorem prov_of_forall_not (α : ι → K) (U : Finset ι)
    {P : Finset ι → Prop} [DecidablePred P]
    (hP : ∀ W ⊆ U, W.Nonempty → ¬ P W) :
    prov α U P = 0 := by
  unfold prov
  rw [Finset.filter_false_of_mem
    (fun W hW h => hP W (Finset.mem_powerset.mp hW) h.1 h.2), Finset.sum_empty]

/-- **Necessarily-true predicates have provenance `⊕_{i ∈ U} α i`.** This
is the algebraic content of the complementary range-check short-circuit:
when every non-empty world satisfies the predicate, the possible-world
provenance is `F_1(U)`, which in an absorptive m-semiring collapses (by
`F_eq_S` at `C = 1`) to the `⊕`-sum of the annotations of the group. -/
theorem prov_of_forall (h_abs : absorptive K) (α : ι → K) (U : Finset ι)
    {P : Finset ι → Prop} [DecidablePred P]
    (hP : ∀ W ⊆ U, W.Nonempty → P W) :
    prov α U P = ∑ i ∈ U, α i := by
  have h1 : prov α U P = F α U 1 := by
    unfold prov F
    refine Finset.sum_congr (Finset.filter_congr fun W hW => ?_) fun _ _ => rfl
    rw [Finset.one_le_card]
    exact ⟨fun h => h.1, fun h => ⟨h, hP W (Finset.mem_powerset.mp hW) h⟩⟩
  have h2 : S α U 1 = ∑ i ∈ U, α i := by
    unfold S
    rw [Finset.powersetCard_one, Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by simp [A]
  rw [h1]
  exact (F_eq_S h_abs α U 0).trans h2

/-- **Occurrence-wise selection predicates are scan-computable.** If a
non-empty world satisfies `P` exactly when all its occurrences satisfy `p` and
at least one of them satisfies `q`, then the provenance of `P` is
`(𝟙 ⊖ ⊕_{¬p} α) ⊗ (⊕_{q} α)`.

This is the algebraic content of the tractability of the `MIN`, `MAX` and
`PICKFIRST` comparisons: all of them have this shape, so their provenance is
obtained from two running sums over the occurrences of the group. -/
theorem prov_eq_of_pointwise (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) (U : Finset ι) (p q r : ι → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (hqp : ∀ i ∈ U, q i → p i) (hr : ∀ i ∈ U, (r i ↔ ¬ p i))
    {P : Finset ι → Prop} [DecidablePred P]
    (hP : ∀ W ⊆ U, (W.Nonempty ∧ P W ↔ (∀ i ∈ W, p i) ∧ ∃ i ∈ W, q i)) :
    prov α U P = (1 - ∑ x ∈ U.filter r, α x) * ∑ i ∈ U.filter q, α i := by
  have hrfilter : U.filter r = U \ U.filter p := by
    rw [← Finset.filter_not]
    exact Finset.filter_congr fun i hi => by rw [hr i hi]
  rw [hrfilter]
  have hGU : U.filter p ⊆ U := Finset.filter_subset _ _
  have hHG : U.filter q ⊆ U.filter p := by
    intro i hi
    obtain ⟨hiU, hqi⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiU, hqp i hiU hqi⟩
  have hfam : U.powerset.filter (fun W => W.Nonempty ∧ P W)
      = (U.filter p).powerset.filter (fun W => (W ∩ U.filter q).Nonempty) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hWU, hPW⟩
      obtain ⟨hall, i, hiW, hqi⟩ := (hP W hWU).mp hPW
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hWU hx, hall x hx⟩,
        i, Finset.mem_inter.mpr ⟨hiW, Finset.mem_filter.mpr ⟨hWU hiW, hqi⟩⟩⟩
    · rintro ⟨hWG, i, hi⟩
      have hWU : W ⊆ U := hWG.trans hGU
      obtain ⟨hiW, hiH⟩ := Finset.mem_inter.mp hi
      exact ⟨hWU, (hP W hWU).mpr
        ⟨fun x hx => (Finset.mem_filter.mp (hWG hx)).2, i, hiW,
          (Finset.mem_filter.mp hiH).2⟩⟩
  rw [prov, hfam, meet_family_eq h_abs h_distrib α hGU hHG]

/-- Special case of `prov_eq_of_pointwise` with no constraint on the excluded
occurrences: the provenance of “some occurrence of the world satisfies `q`” is
`⊕_{q} α`. -/
theorem prov_eq_of_exists (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (α : ι → K) (U : Finset ι) (q : ι → Prop) [DecidablePred q]
    {P : Finset ι → Prop} [DecidablePred P]
    (hP : ∀ W ⊆ U, (W.Nonempty ∧ P W ↔ ∃ i ∈ W, q i)) :
    prov α U P = ∑ i ∈ U.filter q, α i := by
  have h := prov_eq_of_pointwise h_abs h_distrib α U (fun _ => True) q (fun _ => False)
    (fun _ _ _ => trivial) (fun _ _ => by simp)
    (P := P) (fun W hW => by rw [hP W hW]; simp)
  rw [h]
  simp [monus_zero]

/-! ### The `MIN` and `MAX` aggregates -/

section MinMax

variable {V : Type} [LinearOrder V]

/-- `MIN(t)` over a world, as an element of `WithTop V`: the empty world has
aggregate value `⊤` (it is excluded from the possible-world sum anyway). -/
def minAgg (t : ι → V) (W : Finset ι) : WithTop V := W.inf fun i => (t i : WithTop V)

/-- `MAX(t)` over a world, as an element of `WithBot V`. -/
def maxAgg (t : ι → V) (W : Finset ι) : WithBot V := W.sup fun i => (t i : WithBot V)

/-- **The `MIN` scan.** Closed form for the provenance of `MIN(t) op c`: for
each operator, at most two running `⊕`-sums over the occurrences of the group,
combined by one `⊖` and one `⊗`. Computing it takes `O(|U|)` semiring
operations, hence polynomial time in data complexity;
`minScan_correct` proves it correct. -/
def minScan (α : ι → K) (U : Finset ι) (t : ι → V) (op : CompOp) (c : V) : K :=
  match op with
  | .lt => ∑ i ∈ U.filter (fun i => t i < c), α i
  | .le => ∑ i ∈ U.filter (fun i => t i ≤ c), α i
  | .ge => (1 - ∑ x ∈ U.filter (fun i => t i < c), α x) * ∑ i ∈ U.filter (fun i => c ≤ t i), α i
  | .gt => (1 - ∑ x ∈ U.filter (fun i => t i ≤ c), α x) * ∑ i ∈ U.filter (fun i => c < t i), α i
  | .eq => (1 - ∑ x ∈ U.filter (fun i => t i < c), α x) * ∑ i ∈ U.filter (fun i => t i = c), α i
  | .ne => (∑ i ∈ U.filter (fun i => t i < c), α i)
      + (1 - ∑ x ∈ U.filter (fun i => t i ≤ c), α x) * ∑ i ∈ U.filter (fun i => c < t i), α i

/-- **The `MAX` scan**, the mirror image of `minScan`; see `maxScan_correct`. -/
def maxScan (α : ι → K) (U : Finset ι) (t : ι → V) (op : CompOp) (c : V) : K :=
  match op with
  | .gt => ∑ i ∈ U.filter (fun i => c < t i), α i
  | .ge => ∑ i ∈ U.filter (fun i => c ≤ t i), α i
  | .le => (1 - ∑ x ∈ U.filter (fun i => c < t i), α x) * ∑ i ∈ U.filter (fun i => t i ≤ c), α i
  | .lt => (1 - ∑ x ∈ U.filter (fun i => c ≤ t i), α x) * ∑ i ∈ U.filter (fun i => t i < c), α i
  | .eq => (1 - ∑ x ∈ U.filter (fun i => c < t i), α x) * ∑ i ∈ U.filter (fun i => t i = c), α i
  | .ne => (∑ i ∈ U.filter (fun i => c < t i), α i)
      + (1 - ∑ x ∈ U.filter (fun i => c ≤ t i), α x) * ∑ i ∈ U.filter (fun i => t i < c), α i

@[simp] theorem le_minAgg_iff (t : ι → V) (W : Finset ι) (c : V) :
    (c : WithTop V) ≤ minAgg t W ↔ ∀ i ∈ W, c ≤ t i := by
  simp [minAgg, Finset.le_inf_iff]

@[simp] theorem lt_minAgg_iff (t : ι → V) (W : Finset ι) (c : V) :
    (c : WithTop V) < minAgg t W ↔ ∀ i ∈ W, c < t i := by
  simp [minAgg, Finset.lt_inf_iff (WithTop.coe_lt_top c)]

@[simp] theorem minAgg_lt_iff (t : ι → V) (W : Finset ι) (c : V) :
    minAgg t W < (c : WithTop V) ↔ ∃ i ∈ W, t i < c := by
  simp [minAgg, Finset.inf_lt_iff]

@[simp] theorem minAgg_le_iff (t : ι → V) (W : Finset ι) (c : V) :
    minAgg t W ≤ (c : WithTop V) ↔ ∃ i ∈ W, t i ≤ c := by
  rw [← not_lt, lt_minAgg_iff]
  push Not
  rfl

theorem minAgg_eq_iff (t : ι → V) (W : Finset ι) (c : V) :
    minAgg t W = (c : WithTop V) ↔ (∀ i ∈ W, c ≤ t i) ∧ ∃ i ∈ W, t i = c := by
  rw [le_antisymm_iff, minAgg_le_iff, le_minAgg_iff]
  constructor
  · rintro ⟨⟨i, hiW, hic⟩, hall⟩
    exact ⟨hall, i, hiW, le_antisymm hic (hall i hiW)⟩
  · rintro ⟨hall, i, hiW, hic⟩
    exact ⟨⟨i, hiW, le_of_eq hic⟩, hall⟩

@[simp] theorem maxAgg_le_iff (t : ι → V) (W : Finset ι) (c : V) :
    maxAgg t W ≤ (c : WithBot V) ↔ ∀ i ∈ W, t i ≤ c := by
  simp [maxAgg, Finset.sup_le_iff]

@[simp] theorem maxAgg_lt_iff (t : ι → V) (W : Finset ι) (c : V) :
    maxAgg t W < (c : WithBot V) ↔ ∀ i ∈ W, t i < c := by
  simp [maxAgg, Finset.sup_lt_iff (WithBot.bot_lt_coe c)]

@[simp] theorem lt_maxAgg_iff (t : ι → V) (W : Finset ι) (c : V) :
    (c : WithBot V) < maxAgg t W ↔ ∃ i ∈ W, c < t i := by
  simp [maxAgg, Finset.lt_sup_iff]

@[simp] theorem le_maxAgg_iff (t : ι → V) (W : Finset ι) (c : V) :
    (c : WithBot V) ≤ maxAgg t W ↔ ∃ i ∈ W, c ≤ t i := by
  rw [← not_lt, maxAgg_lt_iff]
  push Not
  rfl

theorem maxAgg_eq_iff (t : ι → V) (W : Finset ι) (c : V) :
    maxAgg t W = (c : WithBot V) ↔ (∀ i ∈ W, t i ≤ c) ∧ ∃ i ∈ W, t i = c := by
  rw [le_antisymm_iff, maxAgg_le_iff, le_maxAgg_iff]
  constructor
  · rintro ⟨hall, i, hiW, hci⟩
    exact ⟨hall, i, hiW, le_antisymm (hall i hiW) hci⟩
  · rintro ⟨hall, i, hiW, hic⟩
    exact ⟨hall, i, hiW, le_of_eq hic.symm⟩

/-! #### Provenance of the six `MIN(t) op c` predicates -/

variable (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
variable (α : ι → K) (U : Finset ι) (t : ι → V) (c : V)

include h_abs h_distrib

/-- `MIN(t) < c`: some occurrence of the world has value `< c`. -/
theorem prov_min_lt :
    prov α U (fun W => minAgg t W < (c : WithTop V))
      = ∑ i ∈ U.filter (fun i => t i < c), α i := by
  refine prov_eq_of_exists h_abs h_distrib α U (fun i => t i < c) fun W _ => ?_
  rw [minAgg_lt_iff]
  exact ⟨fun h => h.2, fun ⟨i, hiW, hi⟩ => ⟨⟨i, hiW⟩, i, hiW, hi⟩⟩

/-- `MIN(t) ≤ c`: some occurrence of the world has value `≤ c`. -/
theorem prov_min_le :
    prov α U (fun W => minAgg t W ≤ (c : WithTop V))
      = ∑ i ∈ U.filter (fun i => t i ≤ c), α i := by
  refine prov_eq_of_exists h_abs h_distrib α U (fun i => t i ≤ c) fun W _ => ?_
  rw [minAgg_le_iff]
  exact ⟨fun h => h.2, fun ⟨i, hiW, hi⟩ => ⟨⟨i, hiW⟩, i, hiW, hi⟩⟩

/-- `MIN(t) ≥ c`: the world avoids every occurrence of value `< c` and is
non-empty. -/
theorem prov_min_ge :
    prov α U (fun W => (c : WithTop V) ≤ minAgg t W)
      = (1 - ∑ x ∈ U.filter (fun i => t i < c), α x) * ∑ i ∈ U.filter (fun i => c ≤ t i), α i := by
  refine prov_eq_of_pointwise h_abs h_distrib α U (fun i => c ≤ t i) (fun i => c ≤ t i)
    (fun i => t i < c) (fun _ _ h => h) (fun _ _ => by simp [not_le]) fun W _ => ?_
  rw [le_minAgg_iff]
  exact ⟨fun ⟨⟨i, hiW⟩, hall⟩ => ⟨hall, i, hiW, hall i hiW⟩,
    fun ⟨hall, i, hiW, _⟩ => ⟨⟨i, hiW⟩, hall⟩⟩

/-- `MIN(t) > c`: the world avoids every occurrence of value `≤ c` and is
non-empty. -/
theorem prov_min_gt :
    prov α U (fun W => (c : WithTop V) < minAgg t W)
      = (1 - ∑ x ∈ U.filter (fun i => t i ≤ c), α x) * ∑ i ∈ U.filter (fun i => c < t i), α i := by
  refine prov_eq_of_pointwise h_abs h_distrib α U (fun i => c < t i) (fun i => c < t i)
    (fun i => t i ≤ c) (fun _ _ h => h) (fun _ _ => by simp [not_lt]) fun W _ => ?_
  rw [lt_minAgg_iff]
  exact ⟨fun ⟨⟨i, hiW⟩, hall⟩ => ⟨hall, i, hiW, hall i hiW⟩,
    fun ⟨hall, i, hiW, _⟩ => ⟨⟨i, hiW⟩, hall⟩⟩

/-- `MIN(t) = c`: the world avoids every occurrence of value `< c` and
contains one of value `c`. -/
theorem prov_min_eq :
    prov α U (fun W => minAgg t W = (c : WithTop V))
      = (1 - ∑ x ∈ U.filter (fun i => t i < c), α x) * ∑ i ∈ U.filter (fun i => t i = c), α i := by
  refine prov_eq_of_pointwise h_abs h_distrib α U (fun i => c ≤ t i) (fun i => t i = c)
    (fun i => t i < c) (fun _ _ h => le_of_eq h.symm) (fun _ _ => by simp [not_le])
    fun W _ => ?_
  rw [minAgg_eq_iff]
  exact ⟨fun h => h.2, fun ⟨hall, i, hiW, hi⟩ => ⟨⟨i, hiW⟩, hall, i, hiW, hi⟩⟩

/-- `MIN(t) ≠ c`: the two disjoint cases `MIN(t) < c` and `MIN(t) > c`. -/
theorem prov_min_ne :
    prov α U (fun W => minAgg t W ≠ (c : WithTop V))
      = (∑ i ∈ U.filter (fun i => t i < c), α i)
        + (1 - ∑ x ∈ U.filter (fun i => t i ≤ c), α x)
            * ∑ i ∈ U.filter (fun i => c < t i), α i := by
  rw [prov_congr α U (Q := fun W => minAgg t W < (c : WithTop V) ∨
        (c : WithTop V) < minAgg t W) (fun W _ => ne_iff_lt_or_gt),
    prov_or α U (fun W h h' => absurd (h.trans h') (lt_irrefl _)),
    prov_min_lt h_abs h_distrib, prov_min_gt h_abs h_distrib]

/-! #### Provenance of the six `MAX(t) op c` predicates -/

/-- `MAX(t) > c`: some occurrence of the world has value `> c`. -/
theorem prov_max_gt :
    prov α U (fun W => (c : WithBot V) < maxAgg t W)
      = ∑ i ∈ U.filter (fun i => c < t i), α i := by
  refine prov_eq_of_exists h_abs h_distrib α U (fun i => c < t i) fun W _ => ?_
  rw [lt_maxAgg_iff]
  exact ⟨fun h => h.2, fun ⟨i, hiW, hi⟩ => ⟨⟨i, hiW⟩, i, hiW, hi⟩⟩

/-- `MAX(t) ≥ c`: some occurrence of the world has value `≥ c`. -/
theorem prov_max_ge :
    prov α U (fun W => (c : WithBot V) ≤ maxAgg t W)
      = ∑ i ∈ U.filter (fun i => c ≤ t i), α i := by
  refine prov_eq_of_exists h_abs h_distrib α U (fun i => c ≤ t i) fun W _ => ?_
  rw [le_maxAgg_iff]
  exact ⟨fun h => h.2, fun ⟨i, hiW, hi⟩ => ⟨⟨i, hiW⟩, i, hiW, hi⟩⟩

/-- `MAX(t) ≤ c`: the world avoids every occurrence of value `> c` and is
non-empty. -/
theorem prov_max_le :
    prov α U (fun W => maxAgg t W ≤ (c : WithBot V))
      = (1 - ∑ x ∈ U.filter (fun i => c < t i), α x) * ∑ i ∈ U.filter (fun i => t i ≤ c), α i := by
  refine prov_eq_of_pointwise h_abs h_distrib α U (fun i => t i ≤ c) (fun i => t i ≤ c)
    (fun i => c < t i) (fun _ _ h => h) (fun _ _ => by simp [not_le]) fun W _ => ?_
  rw [maxAgg_le_iff]
  exact ⟨fun ⟨⟨i, hiW⟩, hall⟩ => ⟨hall, i, hiW, hall i hiW⟩,
    fun ⟨hall, i, hiW, _⟩ => ⟨⟨i, hiW⟩, hall⟩⟩

/-- `MAX(t) < c`: the world avoids every occurrence of value `≥ c` and is
non-empty. -/
theorem prov_max_lt :
    prov α U (fun W => maxAgg t W < (c : WithBot V))
      = (1 - ∑ x ∈ U.filter (fun i => c ≤ t i), α x) * ∑ i ∈ U.filter (fun i => t i < c), α i := by
  refine prov_eq_of_pointwise h_abs h_distrib α U (fun i => t i < c) (fun i => t i < c)
    (fun i => c ≤ t i) (fun _ _ h => h) (fun _ _ => by simp [not_lt]) fun W _ => ?_
  rw [maxAgg_lt_iff]
  exact ⟨fun ⟨⟨i, hiW⟩, hall⟩ => ⟨hall, i, hiW, hall i hiW⟩,
    fun ⟨hall, i, hiW, _⟩ => ⟨⟨i, hiW⟩, hall⟩⟩

/-- `MAX(t) = c`: the world avoids every occurrence of value `> c` and
contains one of value `c`. -/
theorem prov_max_eq :
    prov α U (fun W => maxAgg t W = (c : WithBot V))
      = (1 - ∑ x ∈ U.filter (fun i => c < t i), α x) * ∑ i ∈ U.filter (fun i => t i = c), α i := by
  refine prov_eq_of_pointwise h_abs h_distrib α U (fun i => t i ≤ c) (fun i => t i = c)
    (fun i => c < t i) (fun _ _ h => le_of_eq h) (fun _ _ => by simp [not_le]) fun W _ => ?_
  rw [maxAgg_eq_iff]
  exact ⟨fun h => h.2, fun ⟨hall, i, hiW, hi⟩ => ⟨⟨i, hiW⟩, hall, i, hiW, hi⟩⟩

/-- `MAX(t) ≠ c`: the two disjoint cases `MAX(t) > c` and `MAX(t) < c`. -/
theorem prov_max_ne :
    prov α U (fun W => maxAgg t W ≠ (c : WithBot V))
      = (∑ i ∈ U.filter (fun i => c < t i), α i)
        + (1 - ∑ x ∈ U.filter (fun i => c ≤ t i), α x)
            * ∑ i ∈ U.filter (fun i => t i < c), α i := by
  rw [prov_congr α U (Q := fun W => (c : WithBot V) < maxAgg t W ∨
        maxAgg t W < (c : WithBot V)) (fun W _ => ne_comm.trans ne_iff_lt_or_gt),
    prov_or α U (fun W h h' => absurd (h.trans h') (lt_irrefl _)),
    prov_max_gt h_abs h_distrib, prov_max_lt h_abs h_distrib]

/-! #### The two scans are correct -/

/-- **Correctness of the `MIN` scan.** For every comparison operator, the
possible-world provenance of the `HAVING MIN(t) op c` predicate is computed by
the scan `minScan`. -/
theorem minScan_correct (op : CompOp) :
    prov α U (fun W => op.eval (minAgg t W) (c : WithTop V)) = minScan α U t op c := by
  cases op with
  | eq => exact prov_min_eq h_abs h_distrib α U t c
  | ne => exact prov_min_ne h_abs h_distrib α U t c
  | lt => exact prov_min_lt h_abs h_distrib α U t c
  | le => exact prov_min_le h_abs h_distrib α U t c
  | gt => exact prov_min_gt h_abs h_distrib α U t c
  | ge => exact prov_min_ge h_abs h_distrib α U t c

/-- **Correctness of the `MAX` scan.** -/
theorem maxScan_correct (op : CompOp) :
    prov α U (fun W => op.eval (maxAgg t W) (c : WithBot V)) = maxScan α U t op c := by
  cases op with
  | eq => exact prov_max_eq h_abs h_distrib α U t c
  | ne => exact prov_max_ne h_abs h_distrib α U t c
  | lt => exact prov_max_lt h_abs h_distrib α U t c
  | le => exact prov_max_le h_abs h_distrib α U t c
  | gt => exact prov_max_gt h_abs h_distrib α U t c
  | ge => exact prov_max_ge h_abs h_distrib α U t c

end MinMax

/-! ### The `PICKFIRST` aggregate

`PICKFIRST` is the non-commutative aggregate returning the value of the first
occurrence of its input sequence. Here the occurrences are ordered by a linear
order `≼` on `ι` (the order along which the group is enumerated), so the first
occurrence of a world is its `≼`-minimum. -/

section PickFirst

variable {V : Type} [LinearOrder V] [LinearOrder ι]

/-- `PICKFIRST(t)` over a world: the value of its `≼`-first occurrence, with
`⊤` for the empty world. -/
def firstAgg (t : ι → V) (W : Finset ι) : WithTop V := WithTop.map t W.min

/-- The value of `PICKFIRST` on a world whose `≼`-minimum is `i`. -/
theorem firstAgg_eq (t : ι → V) {W : Finset ι} {i : ι} (hiW : i ∈ W)
    (hmin : ∀ j ∈ W, i ≤ j) : firstAgg t W = (t i : WithTop V) := by
  have hne : W.Nonempty := ⟨i, hiW⟩
  have hmin' : W.min' hne = i :=
    le_antisymm (Finset.min'_le W i hiW) (hmin _ (Finset.min'_mem W hne))
  rw [firstAgg, ← Finset.coe_min' hne, WithTop.map_coe, hmin']

/-- **The `PICKFIRST` scan.** Closed form for the provenance of
`PICKFIRST(t) op c`: one term per satisfying occurrence, each combining the
annotation of that occurrence with the running sum of the annotations of the
occurrences that precede it. -/
def firstScan (α : ι → K) (U : Finset ι) (t : ι → V) (op : CompOp) (c : V) : K :=
  ∑ i ∈ U.filter (fun i => op.eval (t i) c),
    (1 - ∑ x ∈ U.filter (fun x => x < i), α x) * α i

variable (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
variable (α : ι → K) (U : Finset ι) (t : ι → V) (c : V)

include h_abs h_distrib

/-- Provenance of the worlds whose `≼`-first occurrence is a given `i`: the
world contains `i` and none of the occurrences preceding `i`. -/
theorem prov_first_fiber {i : ι} (hiU : i ∈ U) :
    prov α U (fun W => i ∈ W ∧ ∀ j ∈ W, i ≤ j)
      = (1 - ∑ x ∈ U.filter (fun x => x < i), α x) * α i := by
  have h := prov_eq_of_pointwise h_abs h_distrib α U (fun j => i ≤ j) (fun j => j = i)
    (fun j => j < i) (fun j _ hj => le_of_eq hj.symm) (fun _ _ => by simp [not_le])
    (P := fun W => i ∈ W ∧ ∀ j ∈ W, i ≤ j)
    (fun W _ => ⟨fun ⟨_, hiW, hall⟩ => ⟨hall, i, hiW, rfl⟩,
      fun ⟨hall, j, hjW, hji⟩ => ⟨⟨j, hjW⟩, hji ▸ hjW, hall⟩⟩)
  rw [h, Finset.filter_eq' U i, if_pos hiU, Finset.sum_singleton]

/-- **Correctness of the `PICKFIRST` scan.** The possible-world provenance of
the `HAVING PICKFIRST(t) op c` predicate is computed by the scan `firstScan`:
the worlds are partitioned according to their first occurrence. -/
theorem firstScan_correct (op : CompOp) :
    prov α U (fun W => op.eval (firstAgg t W) (c : WithTop V)) = firstScan α U t op c := by
  rw [prov_fiber α U (U.filter (fun i => op.eval (t i) c))
    (fun i W => i ∈ W ∧ ∀ j ∈ W, i ≤ j)
    (fun W hWU => by
      constructor
      · rintro ⟨hne, hop⟩
        refine ⟨W.min' hne, ?_, hne, Finset.min'_mem W hne, fun j hj => Finset.min'_le W j hj⟩
        refine Finset.mem_filter.mpr ⟨hWU (Finset.min'_mem W hne), ?_⟩
        rw [firstAgg_eq t (Finset.min'_mem W hne) (fun j hj => Finset.min'_le W j hj),
          CompOp.eval_coe_withTop] at hop
        exact hop
      · rintro ⟨i, hiP, hne, hiW, hall⟩
        refine ⟨hne, ?_⟩
        rw [firstAgg_eq t hiW hall, CompOp.eval_coe_withTop]
        exact (Finset.mem_filter.mp hiP).2)
    (fun W i _ j _ hi hj => le_antisymm (hi.2 j hj.1) (hj.2 i hi.1))]
  exact Finset.sum_congr rfl fun i hi =>
    prov_first_fiber h_abs h_distrib α U (Finset.mem_filter.mp hi).1

end PickFirst

end Having
