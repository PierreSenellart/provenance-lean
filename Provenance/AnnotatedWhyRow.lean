/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AnnotatedApproxRows
import Provenance.Semirings.Why

/-!
# `μ^∪` is necessary in the annotated algebra: the why-provenance semiring

Over the why-provenance semiring `Why[X]`, a set recursion cannot be
replaced by bag recursions, duplicate elimination and the other
operators. On one value `a`, with `S = {a}` annotated `𝟙` and
`E = {(a, a)}` annotated `{{x₁}, …, {x_m}}`, the set recursion
`μ^∪R.(S, Π₁(R ⋈ E))` settles after `m` rounds, and its row carries the
witness `{x₁, …, x_m}`. The data does not depend on `m`, so a query
without `μ^∪` runs the same rounds, groups and frames on every instance
of the family: its annotations are built from the input ones by a number
of products bounded by the query and the data alone, and their witnesses
are unions of boundedly many input witnesses.

The argument is a *graded* invariant (`Graded`): a family of properties
`G D` of annotations, closed under sums, under monus on the left and
under `δ`, with products adding the grades. `Why.grade D a` says that
every witness of `a` has at most `D` variables. No single instance can
separate the classes: the fixpoint of a linear recursion is a finite sum
of powers of its input annotations, which sums and products reach.

The basis theorem follows (`annMuOps_isBasis`): `{∅, Π, σ, apply, γ, win,
μ^⊎, −, μ^∪}` generates the annotated algebra over every commutative
m-semiring, and no proper subset of it does over all of them. It holds up
to `≈` too (`annMuOps_isBasis_approx`): the passes agree with their source
row by row up to finalization, and the witness's row is not `𝟘`.
-/

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## Graded properties of annotations -/

/-- **A grading of the annotations**: `G D a` says `a` has grade at most
`D`. It is monotone, holds of `𝟘` at every grade and of `𝟙` at grade `0`,
of sums at the larger grade, of products at the sum of the grades, of a
monus at its left argument's grade, and of `δ` at grade `0`. -/
structure Graded (G : ℕ → K → Prop) : Prop where
  mono : ∀ {D D' : ℕ} {a : K}, D ≤ D' → G D a → G D' a
  zero : ∀ D, G D 0
  one : G 0 1
  add : ∀ {D : ℕ} {a b : K}, G D a → G D b → G D (a + b)
  mul : ∀ {D D' : ℕ} {a b : K}, G D a → G D' b → G (D + D') (a * b)
  sub : ∀ {D : ℕ} {a : K} (b : K), G D a → G D (a - b)
  delta : ∀ a : K, G 0 (SemiringWithMonus.delta a)

namespace Graded

variable {G : ℕ → K → Prop} (hG : Graded G)
include hG

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem one' (D : ℕ) : G D 1 := hG.mono (Nat.zero_le D) hG.one

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem msum {D : ℕ} : ∀ s : Multiset K, (∀ a ∈ s, G D a) → G D s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; exact hG.zero D
  | cons a s ih =>
    intro h
    rw [Multiset.sum_cons]
    exact hG.add (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem lsum {D : ℕ} (l : List K) (h : ∀ a ∈ l, G D a) : G D l.sum := by
  rw [← Multiset.sum_coe]
  exact hG.msum _ fun a ha => h a (Multiset.mem_coe.1 ha)

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem fsum {D : ℕ} {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, G D (f i)) :
    G D (∑ i ∈ s, f i) := by
  unfold Finset.sum
  exact hG.msum _ fun a ha => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
    exact h i hi

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A product of `k` factors of grade `D` has grade `k D`. -/
theorem mprod {D : ℕ} : ∀ s : Multiset K, (∀ a ∈ s, G D a) → G (s.card * D) s.prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simpa using hG.one
  | cons a s ih =>
    intro h
    rw [Multiset.prod_cons, Multiset.card_cons, Nat.succ_mul, Nat.add_comm]
    exact hG.mul (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A product of factors of grades `D i` has grade their sum. -/
theorem mprod_sum : ∀ s : Multiset (K × ℕ), (∀ p ∈ s, G p.2 p.1) →
    G (s.map Prod.snd).sum (s.map Prod.fst).prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simpa using hG.one
  | cons a s ih =>
    intro h
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact hG.mul (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem fprod {D : ℕ} {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, G D (f i)) :
    G (s.card * D) (∏ i ∈ s, f i) := by
  unfold Finset.prod
  have := hG.mprod (s.val.map f) fun a ha => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
    exact h i hi
  rwa [Multiset.card_map] at this

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem chi (op : CompOp) (a b : T) : G 0 (Having.chi op a b : K) := by
  unfold Having.chi; split_ifs; exacts [hG.one, hG.zero 0]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem chiOf (P : T → Kleene) (a : T) : G 0 (Having.chiOf P a : K) := by
  unfold Having.chiOf; split_ifs; exacts [hG.one, hG.zero 0]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem one_sub (a : K) : G 0 (1 - a) := hG.sub a hG.one

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem worldAnn {D N : ℕ} (α : Fin N → K) (hα : ∀ i, G D (α i)) (W : Finset (Fin N)) :
    G (N * D) (Having.worldAnn α W) := by
  have h := hG.mul (hG.fprod W α fun i _ => hα i) (hG.one_sub (∑ i ∈ Wᶜ, α i))
  refine hG.mono ?_ h
  have := Finset.card_le_univ W
  rw [Fintype.card_fin] at this
  simpa using Nat.mul_le_mul_right D this

end Graded

/-! ## The annotations a token carries, counted -/

/-- Counting the factors of a nested world. -/
theorem card_add_sum_le {α : Type} (s : Multiset α) (g h : α → ℕ) (D : ℕ)
    (hgh : ∀ a ∈ s, g a ≤ h a) :
    s.card * D + (s.map (fun a => g a * D)).sum ≤ (s.map (fun a => 1 + h a)).sum * D := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have h1 := ih fun b hb => hgh b (Multiset.mem_cons_of_mem hb)
    have h2 : g a * D ≤ h a * D := Nat.mul_le_mul_right D (hgh a (Multiset.mem_cons_self a s))
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, one_mul]
    omega

section Tokens

/-- **How many annotations a world of an inner value multiplies at
most**: each occurrence of each storey, an expression family's with it. -/
def NestInner.annCount : (j : ℕ) → NestInner T K j → ℕ
  | 0, e => e.occs.length
  | j + 1, Sum.inl x => NestInner.annCount j x
  | j + 1, Sum.inr N => (N.occs.map (fun o => 1 + NestInner.annCount j o.1)).sum

/-- **How many annotations a world of a token multiplies at most**: its
occurrences, and for a nested value each of its own occurrences and every
inner one, at every storey. -/
def AggTok.annCount : AggTok T K → ℕ
  | .tok a => a.occs.length
  | .expr e => e.occs.length
  | .nest a => (a.occs.map (fun o => 1 + NestInner.annCount a.lev o.1)).sum

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem AggTok.annCount_setFam (φ : FamId T) (x : AggTok T K) :
    (x.setFam φ).annCount = x.annCount := by
  cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **What an inner value counts is what its families and nodes hold**,
with repetition. -/
theorem NestInner.count_eq : ∀ (j : ℕ) (x : NestInner T K j),
    ((NestInner.leaves j x).map (fun κ => κ.2.length)).sum
      + ((NestInner.nodes j x).map (fun κ => Multiset.card κ.2.2)).sum
      = NestInner.annCount j x
  | 0, e => by
    simp [NestInner.leaves, NestInner.nodes, NestInner.annCount, leafKey, AggExpr.annList]
  | j + 1, Sum.inl x => NestInner.count_eq j x
  | j + 1, Sum.inr N => by
    simp only [NestInner.leaves, NestInner.nodes, NestInner.annCount, Multiset.map_bind,
      Multiset.sum_bind, Multiset.map_cons, Multiset.sum_cons, NestNode.key]
    have h : ∀ o ∈ N.occs, 1 + NestInner.annCount j o.1
        = 1 + (((NestInner.leaves j o.1).map (fun κ => κ.2.length)).sum
          + ((NestInner.nodes j o.1).map (fun κ => Multiset.card κ.2.2)).sum) :=
      fun o _ => by rw [NestInner.count_eq j o.1]
    rw [Multiset.map_congr rfl h, Multiset.sum_map_add, Multiset.sum_map_add,
      Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem sum_map_le_of_le {α : Type} {s t : Multiset α} (h : s ≤ t) (f : α → ℕ) :
    (s.map f).sum ≤ (t.map f).sum := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [Multiset.map_add, Multiset.sum_add]
  exact Nat.le_add_right _ _

omit [ValueType T] [CommSemiringWithMonus K] [HasAltLinearOrder K] in
/-- **A nested value's families and nodes, each once, count no more than
its occurrences' inner values do.** -/
theorem NestedValue.count_le [DecidableEq T] (a : NestedValue T K) :
    (a.leaves.map (fun κ => κ.2.length)).sum
      + (a.nodes.map (fun κ => Multiset.card κ.2.2)).sum
      ≤ (a.occs.map (fun o => NestInner.annCount a.lev o.1)).sum := by
  classical
  have h1 := sum_map_le_of_le (Multiset.dedup_le (a.occs.bind
    (fun o => NestInner.leaves a.lev o.1))) (fun κ => κ.2.length)
  have h2 : (a.nodes.map (fun κ => Multiset.card κ.2.2)).sum
      ≤ ((a.occs.bind (fun o => NestInner.nodes a.lev o.1)).map
        (fun κ => Multiset.card κ.2.2)).sum := by
    unfold NestedValue.nodes
    exact sum_map_le_of_le (Multiset.dedup_le _) _
  have h3 : (a.occs.map (fun o => NestInner.annCount a.lev o.1)).sum
      = ((a.occs.bind (fun o => NestInner.leaves a.lev o.1)).map (fun κ => κ.2.length)).sum
        + ((a.occs.bind (fun o => NestInner.nodes a.lev o.1)).map
          (fun κ => Multiset.card κ.2.2)).sum := by
    rw [Multiset.map_bind, Multiset.sum_bind, Multiset.map_bind, Multiset.sum_bind,
      ← Multiset.sum_map_add]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun o _ =>
      (NestInner.count_eq _ o.1).symm)
  unfold NestedValue.leaves at h1 ⊢
  omega

/-- **A token within grade `D`, with at most `N` annotations to a world.** -/
def AggTok.Grade (G : ℕ → K → Prop) (N D : ℕ) (x : AggTok T K) : Prop :=
  x.AnnsIn (G D) ∧ x.annCount ≤ N

/-- **A row within grade `D`**: its concrete annotation, and every token
it holds. Pending factors are read only through `δ`, and need nothing. -/
def GenRow.Grade (G : ℕ → K → Prop) (N D : ℕ) {n : ℕ} (r : GenRow T K n) : Prop :=
  G D r.snd.base ∧ ∀ k a, r.fst k = Sum.inr a → a.Grade G N D

variable {G : ℕ → K → Prop}

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenRow.Grade.finalize (hG : Graded G) {N D n : ℕ} {r : GenRow T K n}
    (h : r.Grade G N D) : G D r.snd.finalize := by
  unfold GenAnn.finalize
  have := hG.mul h.1 (hG.mprod (D := 0)
    (r.snd.pending.map (fun l => SemiringWithMonus.delta l.sum)) fun a ha => by
      obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 ha
      exact hG.delta _)
  simpa using this

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggTok.Grade.mono {N N' D D' : ℕ} {x : AggTok T K}
    (h : x.Grade G N D) (hG : Graded G) (hN : N ≤ N') (hD : D ≤ D') : x.Grade G N' D' := by
  refine ⟨?_, le_trans h.2 hN⟩
  cases x with
  | tok a => exact fun p hp => hG.mono hD (h.1 p hp)
  | expr e => exact fun p hp => hG.mono hD (h.1 p hp)
  | nest a => exact NestedValue.AnnsIn.mono (Q := G D) (fun _ hk => hG.mono hD hk) h.1

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenRow.Grade.mono {N N' D D' n : ℕ} {r : GenRow T K n}
    (h : r.Grade G N D) (hG : Graded G) (hN : N ≤ N') (hD : D ≤ D') : r.Grade G N' D' :=
  ⟨hG.mono hD h.1, fun k a hk => (h.2 k a hk).mono hG hN hD⟩

omit [HasAltLinearOrder K] in
/-- **The worlds of one family multiply at most its count of annotations.** -/
theorem classWorlds_grade (hG : Graded G) {n N D : ℕ} (u : Tuple (GenValue T K) n)
    (M : List (Fin n)) {x₀ : AggTok T K} (h : x₀.Grade G N D) :
    ∀ w ∈ classWorlds u M x₀, G (N * D) w.1 ∧ G D w.2.1 := by
  intro w hw
  cases x₀ with
  | nest a =>
    simp only [classWorlds] at hw
    obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.1 hw
    have hWm := Multiset.mem_of_mem_filter hW
    obtain ⟨h1, h2, h3, h4, h5⟩ := NestedValue.isWorldOf_of_mem_worlds hWm
    obtain ⟨hr, hl, hn⟩ := NestedValue.AnnsIn.world h.1 hWm
    have hget : ∀ e ∈ W.leaf, ∀ i, G D (e.1.2.getD i 0) := fun e he i => by
      rw [List.getD_eq_getElem?_getD]
      cases hi : e.1.2[i]? with
      | none => exact hG.zero D
      | some k => exact hl e he k (List.mem_of_getElem? hi)
    -- the count of what a world can keep
    have hcR : Multiset.card W.root = Multiset.card a.occs := by
      rw [← h1, Multiset.card_map]
    have hcL : (W.leaf.map (fun e => e.2.card)).sum
        ≤ (a.leaves.map (fun κ => κ.2.length)).sum := by
      rw [← h2, Multiset.map_map]
      refine Multiset.sum_map_le_sum_map _ _ fun e he => ?_
      have := Finset.card_le_card (h3 e he)
      rwa [Finset.card_range] at this
    have hcN : (W.node.map (fun e => Multiset.card e.2.2)).sum
        = (a.nodes.map (fun κ => Multiset.card κ.2.2)).sum := by
      rw [← h4, Multiset.map_map]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun e he => by
        rw [Function.comp_apply, ← h5 e he, Multiset.card_map])
    have hcount : Multiset.card W.root + (W.leaf.map (fun e => e.2.card)).sum
        + (W.node.map (fun e => Multiset.card e.2.2)).sum ≤ N := by
      have hle := NestedValue.count_le a
      have h2' := h.2
      simp only [AggTok.annCount] at h2'
      rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
        mul_one] at h2'
      omega
    refine ⟨?_, ?_⟩
    · have hR := hG.mprod (D := D) (W.root.map (fun m => if m.2.2 = true then m.2.1 else 1))
        fun y hy => by
          obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hy
          split_ifs
          · exact hr m hm
          · exact hG.one' D
      rw [Multiset.card_map] at hR
      have hL := hG.mprod_sum (W.leaf.map (fun e => (NestedValue.leafProd e, e.2.card * D)))
        fun p hp => by
          obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hp
          exact hG.fprod _ _ fun i _ => hget e he i
      have hN := hG.mprod_sum (W.node.map (fun e => (NestedValue.decProd e.2.2,
          Multiset.card e.2.2 * D))) fun p hp => by
          obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hp
          have := hG.mprod (D := D) (e.2.2.map (fun m => if m.2.2 = true then m.2.1 else 1))
            fun y hy => by
              obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hy
              split_ifs
              · exact hn e he m hm
              · exact hG.one' D
          rwa [Multiset.card_map] at this
      simp only [Multiset.map_map, Function.comp_def] at hL hN
      have hP := hG.mul (hG.mul hR hL) hN
      refine hG.mono ?_ hP
      rw [Multiset.sum_map_mul_right, Multiset.sum_map_mul_right, ← Nat.add_mul, ← Nat.add_mul]
      exact Nat.mul_le_mul_right D hcount
    · refine hG.add (hG.add (hG.msum _ fun y hy => ?_) (hG.msum _ fun y hy => ?_))
        (hG.msum _ fun y hy => ?_)
      · obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hy
        split_ifs
        · exact hG.zero D
        · exact hr m hm
      · obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hy
        exact hG.fsum _ _ fun i _ => hget e he i
      · obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hy
        refine hG.msum _ fun z hz => ?_
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hz
        split_ifs
        · exact hG.zero D
        · exact hn e he m hm
  | tok a =>
    simp only [classWorlds] at hw
    obtain ⟨W, -, rfl⟩ := Multiset.mem_map.1 hw
    have ha : (AggTok.tok a).flatExpr.AnnsIn (G D) := AggExpr.annsIn_ofValue h.1
    have hlen : W.card ≤ N := by
      have := Finset.card_le_univ W
      rw [Fintype.card_fin] at this
      have h2 := h.2
      simp only [AggTok.annCount] at h2
      simp only [AggTok.flatExpr, AggExpr.ofValue, List.length_map] at this
      omega
    exact ⟨hG.mono (Nat.mul_le_mul_right D hlen) (hG.fprod _ _ fun i _ => ha.anns i),
      hG.fsum _ _ fun i _ => ha.anns i⟩
  | expr e =>
    simp only [classWorlds] at hw
    obtain ⟨W, -, rfl⟩ := Multiset.mem_map.1 hw
    have ha : (AggTok.expr e).flatExpr.AnnsIn (G D) := h.1
    have hlen : W.card ≤ N := by
      have := Finset.card_le_univ W
      rw [Fintype.card_fin] at this
      exact le_trans this h.2
    exact ⟨hG.mono (Nat.mul_le_mul_right D hlen) (hG.fprod _ _ fun i _ => ha.anns i),
      hG.fsum _ _ fun i _ => ha.anns i⟩

omit [HasAltLinearOrder K] in
open Classical in
/-- **The joint worlds of a row multiply at most a count per family.** -/
theorem jointWorlds_grade (hG : Graded G) {n N D : ℕ} (u : Tuple (GenValue T K) n)
    (cols : List (Fin n)) (hu : ∀ k a, u k = Sum.inr a → a.Grade G N D) :
    ∀ w ∈ jointWorlds u cols, G (cols.length * (N * D)) w.1 ∧ G D w.2.1 := by
  have hlen : ((tokCols u cols).map (fun p => p.2.classKey)).dedup.length ≤ cols.length :=
    le_trans (List.dedup_sublist _).length_le
      (by rw [List.length_map]; exact List.length_filterMap_le _ _)
  unfold jointWorlds
  revert hlen
  generalize ((tokCols u cols).map (fun p => p.2.classKey)).dedup = L
  intro hlen w hw
  obtain ⟨h1, h2⟩ : G (L.length * (N * D)) w.1 ∧ G D w.2.1 := by
    clear hlen
    induction L generalizing w with
    | nil =>
      rw [List.foldr_nil, Multiset.mem_singleton] at hw
      subst hw
      exact ⟨by simpa using hG.one, hG.zero D⟩
    | cons φ L ih =>
      simp only [List.foldr_cons] at hw
      split at hw
      · obtain ⟨h1, h2⟩ := ih w hw
        exact ⟨hG.mono (by simp [Nat.succ_mul]) h1, h2⟩
      · rename_i p₀ hf
        obtain ⟨⟨w₁, w₂⟩, hw12, rfl⟩ := Multiset.mem_map.mp hw
        obtain ⟨h1, h2⟩ := Multiset.mem_product.mp hw12
        have hp₀ := mem_tokCols (List.mem_of_find?_eq_some hf)
        obtain ⟨q1, q1'⟩ := classWorlds_grade hG u _ (hu _ _ hp₀.2) w₁ h1
        obtain ⟨q2, q2'⟩ := ih w₂ h2
        refine ⟨?_, hG.add q1' q2'⟩
        refine hG.mono ?_ (hG.mul q1 q2)
        simp only [List.length_cons]
        rw [Nat.succ_mul]; omega
  exact ⟨hG.mono (Nat.mul_le_mul_right _ hlen) h1, h2⟩

omit [HasAltLinearOrder K] in
/-- **A predicate's joint reading multiplies at most a count per compared
column.** -/
theorem GenPredIn.grade_predsemJ (hG : Graded G) {c n N D : ℕ} {κ : Fin n → ColKind}
    (u : Tuple (GenValue T K) n) (γ : Fin c → T)
    (hu : ∀ k a, u k = Sum.inr a → a.Grade G N D) (φ : GenPredIn T c κ) (neg : Bool) :
    G (n * (N * D)) (φ.predsemJ neg u γ) := by
  unfold GenPredIn.predsemJ
  refine hG.msum _ fun y hy => ?_
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨h1, -⟩ := jointWorlds_grade hG u _ hu w hw
  have hlen : ((List.finRange n).filter (· ∈ φ.comparedCols)).length ≤ n :=
    le_trans (List.length_filter_le _ _) (by simp)
  have h3 : G 0 (if φ.eval3W w.2.2 u γ = (if neg then Kleene.false else Kleene.true)
      then (1 : K) else 0) := by
    by_cases hc : φ.eval3W w.2.2 u γ = (if neg then Kleene.false else Kleene.true)
    · rw [ite_eq_left hc]; exact hG.one
    · rw [ite_eq_right hc]; exact hG.zero 0
  have := hG.mul (hG.mul (hG.mono (Nat.mul_le_mul_right _ hlen) h1) (hG.one_sub w.2.1)) h3
  simpa using this

end Tokens

/-! ## The tokens the operators build -/

section Build

variable {G : ℕ → K → Prop}

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **A frame is no larger than its relation and the current row**, over
any listing. -/
theorem length_frameListOf_le' {α : Type} [LinearOrder α] {n m p : ℕ} (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (X : Multiset α) (x : α) :
    (ValueFrame.frameListOf val P O o w X x).length ≤ Multiset.card X + 1 := by
  rw [ValueFrame.frameListOf]
  refine le_trans (le_of_eq (OrderSpec.sortSeq_perm _).length_eq) ?_
  rw [length_sortList]
  unfold ValueFrame.frameOf
  split_ifs
  · rw [Multiset.card_cons]
    exact Nat.add_le_add_right (le_trans (Multiset.card_le_card (Multiset.erase_le _ _))
      (Multiset.card_le_card (Multiset.filter_le _ X))) 1
  · exact le_trans (Multiset.card_le_card (Multiset.erase_le _ _))
      (le_trans (Multiset.card_le_card (Multiset.filter_le _ X)) (Nat.le_succ _))

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem length_mergeOccs_le (l : List (T × K)) : (AggValue.mergeOccs l).length ≤ l.length := by
  unfold AggValue.mergeOccs
  rw [List.length_map, length_sortList, Multiset.coe_card]
  exact le_trans (List.dedup_sublist _).length_le (by rw [List.length_map])

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem annsIn_mergeOccs_grade (hG : Graded G) {D : ℕ} (l : List (T × K))
    (hl : ∀ p ∈ l, G D p.2) : ∀ p ∈ AggValue.mergeOccs l, G D p.2 := by
  intro p hp
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hp
  refine hG.lsum _ fun a ha => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
  split_ifs
  · exact hl q hq
  · exact hG.zero D

omit [DecidableEq K] in
/-- **A window's token over a frame**: its occurrences are those of the
frame, merged by value under `DISTINCT`. -/
theorem grade_tokenOfDist (hG : Graded G) {c n m p D : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n)
    (γ : Fin c → T) (hX : ∀ q ∈ X, G D q.2) (hx : G D x.2) :
    (AggTok.tok (ValueFrame.tokenOfDist P O o w t f dist X x γ)).Grade G
      (Multiset.card X + 1) D := by
  have hU : ∀ q ∈ ValueFrame.frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X x,
      G D q.2 := fun q hq => by
    rcases mem_frameListOf _ P O o w X x q hq with rfl | hq
    · exact hx
    · exact hX q hq
  have hlen := length_frameListOf_le' (α := AnnotatedTuple T K n) Prod.fst P O o w X x
  have htok : (AggTok.tok (ValueFrame.tokenOf P O o w t f X x γ)).Grade G
      (Multiset.card X + 1) D := by
    unfold ValueFrame.tokenOf
    split_ifs
    · exact ⟨AggValue.annsIn_ofGroup f t _ γ hU, by
        simpa [AggTok.annCount, AggValue.ofGroup] using hlen⟩
    · exact ⟨AggValue.annsIn_ofScalarGroup f t _ γ hU, by
        simpa [AggTok.annCount, AggValue.ofScalarGroup, AggValue.ofGroup] using hlen⟩
  unfold ValueFrame.tokenOfDist
  split_ifs
  · exact ⟨annsIn_mergeOccs_grade hG _ htok.1,
      le_trans (length_mergeOccs_le _) htok.2⟩
  · exact htok

omit [DecidableEq K] in
/-- **A window's expression over a frame**: its occurrences are those of
the frame, the kept ones merged by value under `DISTINCT`. -/
theorem grade_exprWhenOf (hG : Graded G) {c n m p D : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (keep : Tuple T n → Bool) (X : AnnotatedRelation T K n)
    (x : AnnotatedTuple T K n) (γ : Fin c → T) (hX : ∀ q ∈ X, G D q.2) (hx : G D x.2) :
    (AggTok.expr (ValueFrame.exprWhenOf P O o w t f dist keep X x γ)).Grade G
      (Multiset.card X + 1) D := by
  have hU : ∀ q ∈ ValueFrame.frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X x,
      G D q.2 := fun q hq => by
    rcases mem_frameListOf _ P O o w X x q hq with rfl | hq
    · exact hx
    · exact hX q hq
  have hlen := length_frameListOf_le' (α := AnnotatedTuple T K n) Prod.fst P O o w X x
  unfold ValueFrame.exprWhenOf
  split_ifs
  · refine ⟨?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
        refine annsIn_mergeOccs_grade hG _ (fun q hq => ?_) z hz
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hq
        exact hU p' (List.mem_of_mem_filter hp')
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hq
        exact hU p' (List.mem_of_mem_filter hp')
    · simp only [AggTok.annCount, AggExpr.ofSeqDistWhen, List.length_append, List.length_map]
      have h1 := length_mergeOccs_le (((ValueFrame.frameListOf (α := AnnotatedTuple T K n)
        Prod.fst P O o w X x).filter (fun p => keep p.fst)).map (fun p => (t.eval p.fst γ, p.snd)))
      rw [List.length_map] at h1
      have h2 := List.length_eq_length_filter_add (l := ValueFrame.frameListOf
        (α := AnnotatedTuple T K n) Prod.fst P O o w X x) (fun p => keep p.fst)
      have h3 : (List.filter (fun p => !keep p.fst) (ValueFrame.frameListOf
          (α := AnnotatedTuple T K n) Prod.fst P O o w X x)).length
          = (List.filter (fun p => !(keep p.fst)) (ValueFrame.frameListOf
          (α := AnnotatedTuple T K n) Prod.fst P O o w X x)).length := rfl
      omega
  · exact ⟨AggExpr.annsIn_ofSeqWhen f t keep _ _ γ hU, by
      simpa [AggTok.annCount, AggExpr.ofSeqWhen] using hlen⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] theorem AggTok.annCount_postcomp (gf : T → T) (x : AggTok T K) :
    (x.postcomp gf).annCount = x.annCount := by
  cases x <;> rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggTok.Grade.postcomp {N D : ℕ} (gf : T → T) {x : AggTok T K} (h : x.Grade G N D) :
    (x.postcomp gf).Grade G N D :=
  ⟨AggTok.annsIn_postcomp gf h.1, by rw [AggTok.annCount_postcomp]; exact h.2⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A projection column reads a token of the row, perhaps through a term. -/
theorem ProjColIn.grade_eval {c n N D : ℕ} {κ : Fin n → ColKind} (p : ProjColIn T c κ)
    {u : Tuple (GenValue T K) n} (γ : Fin c → T) (hu : ∀ k a, u k = Sum.inr a → a.Grade G N D)
    {a : AggTok T K} (h : p.eval u γ = Sum.inr a) : a.Grade G N D := by
  cases p with
  | term t => exact absurd h (by simp [ProjColIn.eval])
  | provTerm t => exact absurd h (by simp [ProjColIn.eval])
  | token k hk => exact hu k a h
  | aggTerm k hk gf =>
    have h' : Sum.map gf (AggTok.postcomp gf) (u k) = Sum.inr a := h
    rcases hv : u k with v | a₀
    · rw [hv] at h'; simp at h'
    · rw [hv] at h'
      simp only [Sum.map_inr, Sum.inr.injEq] at h'
      rw [← h']
      exact (hu k a₀ hv).postcomp gf
  | aggTermOf k hk t =>
    have h' : Sum.map t.unary (AggTok.postcompTerm t) (u k) = Sum.inr a := h
    rcases hv : u k with v | a₀
    · rw [hv] at h'; simp at h'
    · rw [hv] at h'
      simp only [Sum.map_inr, Sum.inr.injEq] at h'
      rw [← h']
      have := (hu k a₀ hv).postcomp t.unary
      exact ⟨by rw [AggTok.postcompTerm, AggTok.AnnsIn_setFam]; exact this.1,
        by rw [AggTok.postcompTerm, AggTok.annCount_setFam]; exact this.2⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The inner reading of a column has at most its count of occurrences. -/
theorem length_innerValue_le {N : ℕ} (x : GenValue T K)
    (hx : ∀ a, x = Sum.inr a → a.annCount ≤ N) : (GenValue.innerValue x).occs.length ≤ N := by
  rcases x with v | a
  · simp [GenValue.innerValue, NestedValue.constInner, AggExpr.ofValue]
  · cases a with
    | tok a =>
      have := hx _ rfl
      simpa [GenValue.innerValue, AggExpr.ofValue, AggTok.annCount] using this
    | nest a => simp [GenValue.innerValue, NestedValue.constInner, AggExpr.ofValue]
    | expr e => exact hx _ rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The inner reading of a column at any storey has at most its count
of annotations.** -/
theorem annCount_innerAt_le {N : ℕ} (x : GenValue T K)
    (hx : ∀ a, x = Sum.inr a → a.annCount ≤ N) :
    ∀ D : ℕ, NestInner.annCount D (x.innerAt D) ≤ N
  | 0 => length_innerValue_le x hx
  | D + 1 => by
    rcases x with v | a
    · exact annCount_innerAt_le (Sum.inl v) hx D
    · cases a with
      | nest b =>
        by_cases hb : b.lev = D
        · subst hb
          simp only [GenValue.innerAt, dite_true]
          exact hx _ rfl
        · simp only [GenValue.innerAt, hb, dite_false]
          exact annCount_innerAt_le _ hx D
      | tok a => exact annCount_innerAt_le _ hx D
      | expr e => exact annCount_innerAt_le _ hx D

omit [CommSemiringWithMonus K] [DecidableEq K] in
theorem length_havingGroupOrd_le {m n₁ : ℕ} (is : Tuple (Fin m) n₁) (ord : GroupOrder T m)
    (r : AnnotatedRelation T K m) (g : Tuple T n₁) :
    (Having.havingGroupOrd is ord r g).length ≤ Multiset.card r := by
  rw [(Having.havingGroupOrd_perm is ord r g).length_eq, ← Multiset.coe_card,
    Having.havingGroup_coe]
  exact Multiset.card_le_card (Multiset.filter_le _ r)

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **A grouping's token over a group** has the group's occurrences. -/
theorem grade_ofGroupOrd {c m n₁ D : ℕ} (f : SeqAggFunc T) (t : TermIn T c m)
    (is : Tuple (Fin m) n₁) (ord : GroupOrder T m) (r : AnnotatedRelation T K m)
    (g : Tuple T n₁) (γ : Fin c → T) (keep : Option (Selection T m))
    (hr : ∀ p ∈ r, G D p.2) :
    (match keep with
      | none => AggTok.tok (AggValue.ofGroup f t (Having.havingGroupOrd is ord r g) γ)
      | some φ => AggTok.expr (AggExpr.ofGroupWhen f t φ.keeps
          (Having.havingGroupOrd is ord r g) γ)).Grade G (Multiset.card r) D := by
  have hU : ∀ p ∈ Having.havingGroupOrd is ord r g, G D p.2 := fun p hp => by
    rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe] at hp
    exact hr p (Multiset.mem_of_mem_filter hp)
  have hlen := length_havingGroupOrd_le is ord r g
  cases keep with
  | none => exact ⟨AggValue.annsIn_ofGroup f t _ γ hU, by
      simpa [AggTok.annCount, AggValue.ofGroup] using hlen⟩
  | some φ => exact ⟨AggExpr.annsIn_ofSeqWhen f t _ _ _ γ hU, by
      simpa [AggTok.annCount, AggExpr.ofGroupWhen, AggExpr.ofSeqWhen] using hlen⟩

end Build

/-! ## A family of evaluations sharing their data -/

section Family

variable {G : ℕ → K → Prop}

/-- **The plain instance a family's evaluations read**: the instance's data,
the one hole of a recursive term bound to its round's data. -/
def plainDB (P : Database T) (H : String → (m : ℕ) → Multiset (Tuple T m)) :
    List (String × ℕ) → Database T
  | [] => P
  | p :: _ => P.assign p.1 (H p.1 p.2)

/-- **A member of a family of evaluations**: an annotated instance and an
environment whose data is `P` and, at the holes, `H`, and whose
annotations are within grade `D`, with at most `N` annotations to a
token's world. -/
structure Member (G : ℕ → K → Prop) (N D : ℕ) (P : Database T) {c : ℕ} (γ : Fin c → T)
    (H : String → (m : ℕ) → Multiset (Tuple T m)) (ρc : Fin c → ColKind) (HK : HoleKinds)
    (l : List (String × ℕ)) (d : AnnotatedDatabase T K) (E : EvalEnv T K) : Prop where
  plain : d.toPlain = P
  holesPlain : ∀ p ∈ l, (E.holes p.1 p.2).map (fun r => GenRow.plainTuple r.fst) = H p.1 p.2
  inst : ∀ m s (r : AnnotatedRelation T K m), d.find m s = some r → ∀ x ∈ r, G D x.2
  holes : ∀ s m, ∀ r ∈ E.holes s m, r.Grade G N D
  ctx : ∀ k a, E.ctxAt c γ k = Sum.inr a → a.Grade G N D
  kinded : E.Kinded γ ρc HK

/-- **A member's data part is the plain evaluation of the family's data.** -/
theorem member_plain {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (hx : q.noExplode) (hh : q.hygienic) (hl : l.length ≤ 1)
    (hm : ∀ p ∈ l, q.noMention p.1) {ρc : Fin c → ColKind} {HK : HoleKinds}
    (hwk : q.wellKinded ρc HK) {N D : ℕ} {P : Database T} {γ : Fin c → T}
    {H : String → (m : ℕ) → Multiset (Tuple T m)} {d : AnnotatedDatabase T K}
    {E : EvalEnv T K} (hM : Member G N D P γ H ρc HK l d E) (hr : q.AnnSettlesAt d γ E) :
    (q.evaluate d γ E).map (fun r => GenRow.plainTuple r.fst)
      = q.stripAgg.evaluatePlain (plainDB P H l) γ := by
  refine AggQueryIn.evaluate_toPlain_env q hx hh hwk d E (plainDB P H l)
    {s | ∃ p ∈ l, p.1 = s} hM.kinded (fun n' s' hs' => ?_)
    (fun s' ⟨p, hp, he⟩ => he ▸ hm p hp) (fun p hp => ?_) hr
  · have hP : P.find n' s' = (d.find n' s').map AnnotatedRelation.toPlain := by
      rw [← hM.plain]; exact AnnotatedDatabase.find_toPlain n' s' d
    match l, hs' with
    | [], _ => exact hP
    | p :: _, hs' =>
      show (P.assign p.1 (H p.1 p.2)).find n' s' = _
      rw [Database.find_assign_of_ne _ _ _ _ (fun h => hs' ⟨p, List.mem_cons_self, h.2.symm⟩)]
      exact hP
  · match l, hl, hp with
    | [p'], _, hp =>
      rw [List.mem_singleton] at hp
      subst hp
      show (P.assign p.1 (H p.1 p.2)).find p.2 p.1 = _
      rw [Database.find_assign, hM.holesPlain p (List.mem_singleton_self _)]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem Member.sub {N D : ℕ} {P : Database T} {c : ℕ} {γ : Fin c → T}
    {H : String → (m : ℕ) → Multiset (Tuple T m)} {ρc : Fin c → ColKind} {HK : HoleKinds}
    {l l' : List (String × ℕ)} {d : AnnotatedDatabase T K} {E : EvalEnv T K}
    (hM : Member G N D P γ H ρc HK l d E) (h : ∀ p ∈ l', p ∈ l) :
    Member G N D P γ H ρc HK l' d E :=
  ⟨hM.plain, fun p hp => hM.holesPlain p (h p hp), hM.inst, hM.holes, hM.ctx, hM.kinded⟩

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem Member.closed {N D : ℕ} {P : Database T} {c : ℕ} {γ : Fin c → T}
    {H : String → (m : ℕ) → Multiset (Tuple T m)} {ρc : Fin c → ColKind} {HK : HoleKinds}
    {l : List (String × ℕ)} {d : AnnotatedDatabase T K} {E : EvalEnv T K}
    (hM : Member G N D P γ H ρc HK l d E) : Member G N D P γ H ρc HK [] d E :=
  hM.sub fun _ hp => absurd hp List.not_mem_nil

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenRow.grade_ofAnnotated {N D n : ℕ} {p : AnnotatedTuple T K n} (h : G D p.2) :
    (GenRow.ofAnnotated p).Grade G N D :=
  ⟨h, fun k a hk => by simp [GenRow.ofAnnotated] at hk⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem EvalEnv.grade_assignHole {N D m : ℕ} (E : EvalEnv T K) (s : String)
    {X : Multiset (GenRow T K m)} (hX : ∀ r ∈ X, r.Grade G N D)
    (hE : ∀ s' k, ∀ r ∈ E.holes s' k, r.Grade G N D) :
    ∀ s' k, ∀ r ∈ (E.assignHole s X).holes s' k, r.Grade G N D := by
  intro s' k r hr
  by_cases h : s' = s ∧ k = m
  · obtain ⟨rfl, rfl⟩ := h
    rw [EvalEnv.assignHole_holes_self] at hr
    exact hX r hr
  · have : (E.assignHole s X).holes s' k = E.holes s' k := by
      show (if h : s' = s ∧ k = m then _ else _) = _
      rw [dite_eq_right h]
    rw [this] at hr
    exact hE s' k r hr

/-- **The uniform bound**: a query without `μ^∪` has, over a family of
evaluations sharing their data, annotations within one grade – the data
fixes its rounds, its groups and its frames, and so how many products it
takes. -/
theorem AggQueryIn.exists_grade (hG : Graded G) {S : Set OpKind} (hS : OpKind.muSet ∉ S)
    {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.inSig Θ → q.noExplode → q.hygienic → l.length ≤ 1 →
      (∀ p ∈ l, q.noMention p.1) → ∀ {ρc : Fin c → ColKind} {HK : HoleKinds},
      q.wellKinded ρc HK →
      ∀ (P : Database T) (γ : Fin c → T) (H : String → (m : ℕ) → Multiset (Tuple T m))
        (N D : ℕ), ∃ N' D', N ≤ N' ∧ D ≤ D' ∧ ∀ (d : AnnotatedDatabase T K) (E : EvalEnv T K),
        Member G N D P γ H ρc HK l d E → q.AnnSettlesAt d γ E →
        ∀ r ∈ q.evaluate d γ E, r.Grade G N' D' := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ _ _ _ _ ρc HK _ P γ H N D
    refine ⟨N, D, le_rfl, le_rfl, fun d E hM _ r hr => ?_⟩
    revert hr
    simp only [AggQueryIn.evaluate]
    cases hf : d.find n s with
    | none => intro hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      intro hr
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hr
      exact GenRow.grade_ofAnnotated (hM.inst n s rn hf a ha)
  | Hole n s κ =>
    intro _ _ _ _ _ _ ρc HK _ P γ H N D
    exact ⟨N, D, le_rfl, le_rfl, fun d E hM _ r hr =>
      hM.holes s n r (Multiset.mem_of_mem_filter hr)⟩
  | Param pv ρ =>
    intro _ _ _ _ _ _ ρc HK _ P γ H N D
    refine ⟨N, D, le_rfl, le_rfl, fun d E hM _ r hr => ?_⟩
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows] at hr
    split at hr
    · rw [Multiset.mem_singleton] at hr
      subst hr
      refine ⟨hG.one' D, fun k a hk => ?_⟩
      revert hk
      show _root_.Sum.elim Sum.inl (E.ctxAt _ γ) (pv k) = Sum.inr a → a.Grade G N D
      cases pv k with
      | inl v => intro hk; simp at hk
      | inr j => intro hk; exact hM.ctx j a hk
    · exact absurd hr (Multiset.notMem_zero r)
  | Empty =>
    intro _ _ _ _ _ _ ρc HK _ P γ H N D
    exact ⟨N, D, le_rfl, le_rfl, fun _ _ _ _ r hr => absurd hr (Multiset.notMem_zero r)⟩
  | Proj ps q ih =>
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu.2 hi.2 hx hh hl hm hwk.2 P γ H N D
    refine ⟨N₁, D₁, hN, hD, fun d E hM hr r hrr => ?_⟩
    simp only [AggQueryIn.evaluate] at hrr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hrr
    obtain ⟨hb₀, ht₀⟩ := hb d E hM hr r₀ hr₀
    refine ⟨?_, fun j a hj => ProjColIn.grade_eval (ps j) γ ht₀ hj⟩
    have := hG.mul hb₀ (hG.mprod (D := 0) ((r₀.snd.pending - r₀.snd.pending ∩ tokenLists
      (fun j => (ps j).eval r₀.fst γ)).map (fun l => SemiringWithMonus.delta l.sum))
      fun a ha => by
        obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 ha
        exact hG.delta _)
    simpa using this
  | Sel φ q hφ ih =>
    rename_i n' κ' l'
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu.2 hi.2 hx hh hl hm hwk.2 P γ H N D
    refine ⟨N₁, D₁ + n' * (N₁ * D₁), hN, le_trans hD (Nat.le_add_right _ _),
      fun d E hM hr r hrr => ?_⟩
    dsimp only [AggQueryIn.evaluate] at hrr
    by_cases hagg : φ.hasAggAtom = true
    · rw [ite_eq_left hagg] at hrr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hrr
      obtain ⟨hb₀, ht₀⟩ := hb d E hM hr r₀ hr₀
      exact ⟨hG.mul hb₀ (GenPredIn.grade_predsemJ hG r₀.fst γ ht₀ φ false),
        fun k a hk => (ht₀ k a hk).mono hG le_rfl (Nat.le_add_right _ _)⟩
    · rw [ite_eq_right hagg] at hrr
      exact (hb d E hM hr r (Multiset.mem_of_mem_filter hrr)).mono hG le_rfl
        (Nat.le_add_right _ _)
  | Prod q₁ q₂ ih₁ ih₂ =>
    rename_i l₁ l₂
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    have hl₁ : l₁.length ≤ 1 := by rw [List.length_append] at hl; omega
    have hl₂ : l₂.length ≤ 1 := by rw [List.length_append] at hl; omega
    obtain ⟨N₁, D₁, hN₁, hD₁, hb₁⟩ := ih₁ hu.2.1 hi.1 hx.1 hh.1 hl₁
      (fun p hp => (hm p (List.mem_append_left _ hp)).1) hwk.1 P γ H N D
    obtain ⟨N₂, D₂, hN₂, hD₂, hb₂⟩ := ih₂ hu.2.2 hi.2 hx.2 hh.2 hl₂
      (fun p hp => (hm p (List.mem_append_right _ hp)).2) hwk.2 P γ H N D
    refine ⟨max N₁ N₂, D₁ + D₂, le_trans hN₁ (le_max_left _ _),
      le_trans hD₁ (Nat.le_add_right _ _), fun d E hM hr r hrr => ?_⟩
    simp only [AggQueryIn.evaluate] at hrr
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Multiset.mem_map.1 hrr
    obtain ⟨hxm, hym⟩ := Multiset.mem_product.1 hxy
    obtain ⟨bx, tx⟩ := hb₁ d E (hM.sub fun p hp => List.mem_append_left _ hp) hr.1 x hxm
    obtain ⟨b_y, ty⟩ := hb₂ d E (hM.sub fun p hp => List.mem_append_right _ hp) hr.2 y hym
    refine ⟨hG.mul bx b_y, fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk
      exact (tx i a hk).mono hG (le_max_left _ _) (Nat.le_add_right _ _)
    · simp only [Fin.append_right] at hk
      exact (ty i a hk).mono hG (le_max_right _ _) (Nat.le_add_left _ _)
  | Sum q₁ q₂ ih₁ ih₂ =>
    rename_i l₁ l₂
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    have hl₁ : l₁.length ≤ 1 := by rw [List.length_append] at hl; omega
    have hl₂ : l₂.length ≤ 1 := by rw [List.length_append] at hl; omega
    obtain ⟨N₁, D₁, hN₁, hD₁, hb₁⟩ := ih₁ hu.2.1 hi.1 hx.1 hh.1 hl₁
      (fun p hp => (hm p (List.mem_append_left _ hp)).1) hwk.1 P γ H N D
    obtain ⟨N₂, D₂, hN₂, hD₂, hb₂⟩ := ih₂ hu.2.2 hi.2 hx.2 hh.2 hl₂
      (fun p hp => (hm p (List.mem_append_right _ hp)).2) hwk.2 P γ H N D
    refine ⟨max N₁ N₂, max D₁ D₂, le_trans hN₁ (le_max_left _ _),
      le_trans hD₁ (le_max_left _ _), fun d E hM hr r hrr => ?_⟩
    simp only [AggQueryIn.evaluate] at hrr
    rcases Multiset.mem_add.1 hrr with hrr | hrr
    · exact (hb₁ d E (hM.sub fun p hp => List.mem_append_left _ hp) hr.1 r hrr).mono hG
        (le_max_left _ _) (le_max_left _ _)
    · exact (hb₂ d E (hM.sub fun p hp => List.mem_append_right _ hp) hr.2 r hrr).mono hG
        (le_max_right _ _) (le_max_right _ _)
  | Dedup q ih =>
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu.2 hi hx hh (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk P γ H N D
    refine ⟨N₁, D₁, hN, hD, fun d E hM hr r hrr => ?_⟩
    simp only [AggQueryIn.evaluate] at hrr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hrr
    rw [groupByKey_eq_dedup_map] at hp
    obtain ⟨u, -, rfl⟩ := Multiset.mem_map.1 hp
    refine GenRow.grade_ofAnnotated (hG.msum _ fun a ha => ?_)
    obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_filter hp')
    exact (hb d E hM.closed hr r₀ hr₀).finalize hG
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih₁ hu.2.1 hi.1 hx.1 hh.1 (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk.1 P γ H N D
    refine ⟨N₁, D₁, hN, hD, fun d E hM hr r hrr => ?_⟩
    simp only [AggQueryIn.evaluate] at hrr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hrr
    obtain ⟨⟨u, α⟩, hu', rfl⟩ := Multiset.mem_map.1 hp
    obtain ⟨r₀, hr₀, he⟩ := Multiset.mem_map.1 hu'
    refine GenRow.grade_ofAnnotated (hG.sub _ ?_)
    have he' := congrArg Prod.snd he
    simp only at he'
    rw [← he']
    exact (hb d E hM.closed hr.1 r₀ hr₀).finalize hG
  | Retag hk q ih =>
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu hi hx hh hl hm hwk P γ H N D
    exact ⟨N₁, D₁, hN, hD, fun d E hM hr r hrr => hb d E hM hr r hrr⟩
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂ _ _
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu.2 hi.2.2.2 hx hh (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk.2 P γ H N D
    obtain ⟨C, hC⟩ : ∃ C, C = Multiset.card (q.stripAgg.evaluatePlain (plainDB P H []) γ) :=
      ⟨_, rfl⟩
    refine ⟨max N₁ C, D₁, le_trans hN (le_max_left _ _), hD, fun d E hM hr r hrr => ?_⟩
    have hcard : Multiset.card (q.evaluate d γ E) = C := by
      rw [hC, ← member_plain q hx hh (by simp) (fun p hp => absurd hp List.not_mem_nil) hwk.2
        hM.closed hr, Multiset.card_map]
    simp only [AggQueryIn.evaluate] at hrr
    obtain ⟨kv, hkv, rfl⟩ := Multiset.mem_map.1 hrr
    have hRb : ∀ p ∈ (q.evaluate d γ E).map GenRow.toAnnotated, G D₁ p.2 := by
      intro p hp
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
      exact (hb d E hM.closed hr r₀ hr₀).finalize hG
    refine ⟨hG.one' D₁, fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk; simp at hk
    · simp only [Fin.append_right, Sum.inr.injEq] at hk
      subst hk
      have := grade_ofGroupOrd (G := G) (fs i) (ts i) is ord
        ((q.evaluate d γ E).map GenRow.toAnnotated) kv.1 γ (keep i) hRb
      rw [Multiset.card_map, hcard] at this
      refine ⟨?_, ?_⟩
      · rw [AggTok.AnnsIn_setFam]; exact this.1
      · rw [AggTok.annCount_setFam]; exact le_trans this.2 (le_max_right _ _)
  | GammaScalar ts fs q ord ih =>
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu.2 hi.2.2 hx hh (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk.2 P γ H N D
    obtain ⟨C, hC⟩ : ∃ C, C = Multiset.card (q.stripAgg.evaluatePlain (plainDB P H []) γ) :=
      ⟨_, rfl⟩
    refine ⟨max N₁ C, D₁, le_trans hN (le_max_left _ _), hD, fun d E hM hr r hrr => ?_⟩
    have hcard : Multiset.card (q.evaluate d γ E) = C := by
      rw [hC, ← member_plain q hx hh (by simp) (fun p hp => absurd hp List.not_mem_nil) hwk.2
        hM.closed hr, Multiset.card_map]
    simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hrr
    subst hrr
    have hRb : ∀ p ∈ (q.evaluate d γ E).map GenRow.toAnnotated, G D₁ p.2 := by
      intro p hp
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
      exact (hb d E hM.closed hr r₀ hr₀).finalize hG
    refine ⟨hG.one' D₁, fun k a hk => ?_⟩
    simp only [Sum.inr.injEq] at hk
    subst hk
    have := grade_ofGroupOrd (G := G) (fs k) (ts k) (fun k : Fin 0 => k.elim0) ord
      ((q.evaluate d γ E).map GenRow.toAnnotated) (fun k : Fin 0 => k.elim0) γ none hRb
    rw [Multiset.card_map, hcard] at this
    refine ⟨?_, ?_⟩
    · rw [AggTok.AnnsIn_setFam]; exact this.1
    · rw [AggTok.annCount_setFam]; exact le_trans this.2 (le_max_right _ _)
  | GammaNest is his p g q ih =>
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu.2 hi.2.2 hx hh (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk.2 P γ H N D
    obtain ⟨C, hC⟩ : ∃ C, C = Multiset.card (q.stripAgg.evaluatePlain (plainDB P H []) γ) :=
      ⟨_, rfl⟩
    refine ⟨max N₁ (C * (1 + N₁)), D₁, le_trans hN (le_max_left _ _), hD,
      fun d E hM hr r hrr => ?_⟩
    have hcard : Multiset.card (q.evaluate d γ E) = C := by
      rw [hC, ← member_plain q hx hh (by simp) (fun p hp => absurd hp List.not_mem_nil) hwk.2
        hM.closed hr, Multiset.card_map]
    simp only [AggQueryIn.evaluate] at hrr
    obtain ⟨gk, -, rfl⟩ := Multiset.mem_map.1 hrr
    have hb' := hb d E hM.closed hr
    refine ⟨hG.one' D₁, fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk; simp at hk
    · simp only [Fin.append_right, Sum.inr.injEq] at hk
      subst hk
      refine ⟨fun o ho => ?_, ?_⟩
      · simp only [nestOfGroup, nestOfVals, NestedValue.occs_ofOccs, Multiset.map_map] at ho
        obtain ⟨row, hrow, rfl⟩ := Multiset.mem_map.1 ho
        have hrow' := hb' row (Multiset.mem_of_mem_filter hrow)
        exact ⟨hrow'.finalize hG, GenValue.annsIn_innerAt _ (fun a ha =>
          (ProjColIn.grade_eval p γ hrow'.2 ha).1) _⟩
      · refine le_trans ?_ (le_max_right _ _)
        simp only [AggTok.annCount, nestOfGroup, nestOfVals, NestedValue.occs_ofOccs,
          Multiset.map_map, Function.comp_def]
        refine le_trans (Multiset.sum_le_card_nsmul _ (1 + N₁) fun x hx => ?_) ?_
        · obtain ⟨row, hrow, rfl⟩ := Multiset.mem_map.1 hx
          have hrow' := hb' row (Multiset.mem_of_mem_filter hrow)
          exact Nat.add_le_add_left (annCount_innerAt_le _ (fun a ha =>
            (ProjColIn.grade_eval p γ hrow'.2 ha).2) _) 1
        · rw [Multiset.card_map, smul_eq_mul]
          refine Nat.mul_le_mul_right _ ?_
          rw [← hcard]
          exact Multiset.card_le_card (Multiset.filter_le _ _)
  | Win P' O o w t g q hrr dist keep ih =>
    rename_i c' n' m' p' κ' _ _ _
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN, hD, hb⟩ := ih hu.2 hi.2.2.2 hx hh (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk.2 P γ H N D
    obtain ⟨C, hC⟩ : ∃ C, C = Multiset.card (q.stripAgg.evaluatePlain (plainDB P H []) γ) :=
      ⟨_, rfl⟩
    refine ⟨max N₁ (C + 1), D₁, le_trans hN (le_max_left _ _), hD,
      fun d E hM hr r hrr' => ?_⟩
    have hcard : Multiset.card (q.evaluate d γ E) = C := by
      rw [hC, ← member_plain q hx hh (by simp) (fun p hp => absurd hp List.not_mem_nil) hwk.2
        hM.closed hr, Multiset.card_map]
    simp only [AggQueryIn.evaluate] at hrr'
    obtain ⟨x, hxm, rfl⟩ := Multiset.mem_map.1 hrr'
    have hb' := hb d E hM.closed hr
    have hX : ∀ y ∈ (q.evaluate d γ E).map (GenRow.readAnnotated κ'), G D₁ y.2 := by
      intro y hy
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hy
      exact (hb' r₀ hr₀).finalize hG
    obtain ⟨bx, tx⟩ := hb' x hxm
    refine ⟨bx, fun k a hk => ?_⟩
    simp only [ValueFrame.windowGenRow] at hk
    refine Fin.lastCases (fun hk => ?_) (fun i hk => ?_) k hk
    · rw [Fin.snoc_last, Sum.inr.injEq] at hk
      subst hk
      have hcX : Multiset.card ((q.evaluate d γ E).map (GenRow.readAnnotated κ')) = C := by
        rw [Multiset.card_map, hcard]
      split
      · have := grade_tokenOfDist hG P' O o w t g dist _ (GenRow.readAnnotated κ' x) γ hX
          ((hb' x hxm).finalize hG)
        rw [hcX] at this
        exact ⟨by rw [AggTok.AnnsIn_setFam]; exact this.1,
          by rw [AggTok.annCount_setFam]; exact le_trans this.2 (le_max_right _ _)⟩
      · rename_i φ
        have := grade_exprWhenOf hG P' O o w t g dist φ.keeps _ (GenRow.readAnnotated κ' x) γ hX
          ((hb' x hxm).finalize hG)
        rw [hcX] at this
        exact ⟨by rw [AggTok.AnnsIn_setFam]; exact this.1,
          by rw [AggTok.annCount_setFam]; exact le_trans this.2 (le_max_right _ _)⟩
    · rw [Fin.snoc_castSucc] at hk
      exact (tx i a hk).mono hG (le_max_left _ _) le_rfl
  | ProvSum is his t q ih => exact fun hu => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun hu => hu.elim
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ hi => hi.elim
  | Explode k hk q ih => exact fun _ _ hx => hx.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hu => absurd hu.1 hS
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l'
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₁, D₁, hN₁, hD₁, hb₁⟩ := ih₁ hu.2.1 hi.1 hx.1 hh.1 hl (fun p hp => (hm p hp).1)
      hwk.1 P γ H N D
    have h2 := fun p : Tuple T n₁ => ih₂ hu.2.2 hi.2 hx.2 hh.2 (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk.2 P (Fin.append p γ) H (max N N₁) (max D D₁)
    choose N₂ D₂ hN₂ hD₂ hb₂ using h2
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset (Tuple T n₁),
        S₁ = (q₁.stripAgg.evaluatePlain (plainDB P H l') γ).toFinset := ⟨_, rfl⟩
    refine ⟨max N₁ (S₁.sup N₂), D₁ + S₁.sup D₂, le_trans hN₁ (le_max_left _ _),
      le_trans hD₁ (Nat.le_add_right _ _), fun d E hM hr r hrr => ?_⟩
    simp only [AggQueryIn.evaluate] at hrr
    obtain ⟨x, hxm, hrr⟩ := Multiset.mem_bind.1 hrr
    obtain ⟨y, hym, rfl⟩ := Multiset.mem_map.1 hrr
    obtain ⟨bx, tx⟩ := hb₁ d E hM hr.1 x hxm
    have hxS : GenRow.plainTuple x.fst ∈ S₁ := by
      rw [hS₁, Multiset.mem_toFinset, ← member_plain q₁ hx.1 hh.1 hl (fun p hp => (hm p hp).1)
        hwk.1 hM hr.1]
      exact Multiset.mem_map_of_mem _ hxm
    have hM₂ : Member G (max N N₁) (max D D₁) P (Fin.append (GenRow.plainTuple x.fst) γ) H
        (Fin.append κ₁ ρc) HK [] d (E.withCtx (Fin.append x.fst (E.ctxAt _ γ))) :=
      ⟨hM.plain, fun _ hp => absurd hp List.not_mem_nil,
        fun m s' r' hf a ha => hG.mono (le_max_left _ _) (hM.inst m s' r' hf a ha),
        fun s' m r' hr' => (hM.holes s' m r' hr').mono hG (le_max_left _ _) (le_max_left _ _),
        fun k a hk => by
          rw [EvalEnv.ctxAt_withCtx] at hk
          revert hk
          refine Fin.addCases (fun i => ?_) (fun i => ?_) k
          · rw [Fin.append_left]
            exact fun hk => (tx i a hk).mono hG (le_max_right _ _) (le_max_right _ _)
          · rw [Fin.append_right]
            exact fun hk => (hM.ctx i a hk).mono hG (le_max_left _ _) (le_max_left _ _),
        hM.kinded.enter (fun k => AggQueryIn.evaluate_conform q₁ d x hxm k)⟩
    obtain ⟨b_y, ty⟩ := hb₂ _ d _ hM₂ (hr.2 x hxm) y hym
    have hNle : N₂ (GenRow.plainTuple x.fst) ≤ S₁.sup N₂ := Finset.le_sup hxS
    have hDle : D₂ (GenRow.plainTuple x.fst) ≤ S₁.sup D₂ := Finset.le_sup hxS
    refine ⟨hG.mono (Nat.add_le_add_left hDle _) (hG.mul bx b_y), fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk
      exact (tx i a hk).mono hG (le_max_left _ _) (Nat.le_add_right _ _)
    · simp only [Fin.append_right] at hk
      exact (ty i a hk).mono hG (le_trans hNle (le_max_right _ _))
        (le_trans hDle (Nat.le_add_left _ _))
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m κ'
    intro hu hi hx hh hl hm ρc HK hwk P γ H N D
    obtain ⟨N₀, D₀, hN₀, hD₀, hb₀⟩ := ih₀ hu.2.1 hi.1 hx.1 hh.2.2.1 (by simp)
      (fun p hp => absurd hp List.not_mem_nil) hwk.1 P γ H N D
    -- the holes' data at a round
    let Hof : Multiset (Tuple T m) → String → (k : ℕ) → Multiset (Tuple T k) :=
      fun X s' k => if s' = s then (if h : m = k then h ▸ X else H s' k) else H s' k
    have hHof : ∀ X, Hof X s m = X := fun X => by simp [Hof]
    -- the plain rounds
    let Rp : ℕ → Multiset (Tuple T m) := fun j => Nat.rec (q₀.stripAgg.evaluatePlain P γ)
      (fun _ R => q₁.stripAgg.evaluatePlain (P.assign s R) γ) j
    have h1 := fun (H' : String → (k : ℕ) → Multiset (Tuple T k)) (N' D' : ℕ) =>
      ih₁ hu.2.2 hi.2 hx.2 hh.2.2.2 (by simp)
        (fun p hp => by obtain rfl := List.mem_singleton.1 hp; exact hh.2.1) hwk.2 P γ H' N' D'
    choose F₁N F₁D hF₁N hF₁D hF₁ using h1
    let b : ℕ → ℕ × ℕ := fun j => Nat.rec (N₀, D₀)
      (fun j bj => (F₁N (Hof (Rp j)) (max N bj.1) (max D bj.2),
        F₁D (Hof (Rp j)) (max N bj.1) (max D bj.2))) j
    classical
    let R : ℕ := if h : ∃ j, Rp (j + 1) = 0 then Nat.find h else 0
    refine ⟨(Finset.range (R + 1)).sup (fun j => (b j).1),
      (Finset.range (R + 1)).sup (fun j => (b j).2),
      le_trans hN₀ (Finset.le_sup (f := fun j => (b j).1) (Finset.mem_range.2 (Nat.succ_pos R))),
      le_trans hD₀ (Finset.le_sup (f := fun j => (b j).2) (Finset.mem_range.2 (Nat.succ_pos R))),
      fun d E hM hr r hrr => ?_⟩
    set step := AggQueryIn.muStep s q₁ d γ E with hstep
    have hconf : ∀ j, ∀ x ∈ step^[j] (q₀.evaluate d γ E), GenRow.Conforms κ' x.fst := by
      intro j
      cases j with
      | zero => exact fun x hx k => AggQueryIn.evaluate_conform q₀ d x hx k
      | succ j =>
        intro x hx k
        rw [Function.iterate_succ_apply'] at hx
        exact AggQueryIn.evaluate_conform q₁ d x hx k
    have key : ∀ j, (∀ x ∈ step^[j] (q₀.evaluate d γ E), x.Grade G (b j).1 (b j).2)
        ∧ (step^[j] (q₀.evaluate d γ E)).map (fun x => GenRow.plainTuple x.fst) = Rp j := by
      intro j
      induction j with
      | zero =>
        exact ⟨hb₀ d E hM.closed hr.1, member_plain q₀ hx.1 hh.2.2.1 (by simp)
          (fun p hp => absurd hp List.not_mem_nil) hwk.1 hM.closed hr.1⟩
      | succ j ihj =>
        obtain ⟨hgj, hpj⟩ := ihj
        have hMb : Member G (max N (b j).1) (max D (b j).2) P γ (Hof (Rp j)) ρc
            (HK.assign s κ') [(s, m)] d (E.assignHole s (step^[j] (q₀.evaluate d γ E))) :=
          ⟨hM.plain, fun p hp => by
              obtain rfl := List.mem_singleton.1 hp
              rw [EvalEnv.assignHole_holes_self, hpj, hHof],
            fun m' s' r' hf a ha => hG.mono (le_max_left _ _) (hM.inst m' s' r' hf a ha),
            EvalEnv.grade_assignHole E s
              (fun x hx => (hgj x hx).mono hG (le_max_right _ _) (le_max_right _ _))
              (fun s' k r' hr' => (hM.holes s' k r' hr').mono hG (le_max_left _ _)
                (le_max_left _ _)),
            fun k a hk => by
              rw [EvalEnv.ctxAt_assignHole] at hk
              exact (hM.ctx k a hk).mono hG (le_max_left _ _) (le_max_left _ _),
            hM.kinded.assignHole s (hconf j)⟩
        have hsj := hr.2.2.2.1 j
        rw [Function.iterate_succ_apply']
        refine ⟨fun x hx => hF₁ _ _ _ d _ hMb hsj x hx,
          (member_plain q₁ hx.2 hh.2.2.2 (by simp)
            (fun p hp => by obtain rfl := List.mem_singleton.1 hp; exact hh.2.1) hwk.2 hMb
            hsj).trans ?_⟩
        show q₁.stripAgg.evaluatePlain (P.assign s (Hof (Rp j) s m)) γ = _
        rw [hHof]
    -- the rounds end where the plain ones do
    obtain ⟨k, hk⟩ := hr.2.2.1
    have hex : ∃ j, Rp (j + 1) = 0 := ⟨k, by
      rw [← (key (k + 1)).2]
      show Multiset.map _ (step^[k + 1] (q₀.evaluate d γ E)) = 0
      rw [hk, Multiset.map_zero]⟩
    have hR : R = Nat.find hex := dite_eq_left hex
    have hend : step^[R + 1] (q₀.evaluate d γ E) = 0 := by
      have := (key (R + 1)).2
      rw [hR, Nat.find_spec hex] at this
      rw [hR]
      exact Multiset.map_eq_zero.1 this
    simp only [AggQueryIn.evaluate] at hrr
    rw [show (fun X => q₁.evaluate d γ (E.assignHole s X)) = step from rfl,
      muSumFix_eq_sum hr.2.1 hend] at hrr
    obtain ⟨j, hj, hrj⟩ := Multiset.mem_sum.1 hrr
    exact ((key j).1 r hrj).mono hG (Finset.le_sup (f := fun j => (b j).1) hj)
      (Finset.le_sup (f := fun j => (b j).2) hj)

end Family

/-! ## The grading of `Why[X]`: the size of a witness -/

section WhyGrade

variable {α : Type}

/-- **A why-provenance annotation of grade `D`**: every witness has at most
`D` variables. -/
def Why.grade (D : ℕ) (a : Why α) : Prop := ∀ w ∈ a.carrier, w.encard ≤ D

theorem Why.graded : Graded (Why.grade (α := α)) := by
  refine ⟨fun {D D' a} hD h w hw => le_trans (h w hw) (by exact_mod_cast hD),
    fun D w hw => absurd hw (Set.notMem_empty w), fun w hw => ?_,
    fun {D a b} ha hb w hw => ?_, fun {D D' a b} ha hb w hw => ?_,
    fun {D a} b ha w hw => ha w hw.1, fun a w hw => ?_⟩
  · have hw' : w = ∅ := hw
    simp [hw']
  · rcases (show w ∈ a.carrier ∪ b.carrier from hw) with h | h
    · exact ha w h
    · exact hb w h
  · obtain ⟨x, y, hx, hy, rfl⟩ := (show ∃ x y : Set α, x ∈ a.carrier ∧ y ∈ b.carrier ∧ w = x ∪ y
      from hw)
    calc (x ∪ y).encard ≤ x.encard + y.encard := Set.encard_union_le x y
      _ ≤ D + D' := add_le_add (ha x hx) (hb y hy)
      _ = ((D + D' : ℕ) : ℕ∞) := by push_cast; rfl
  · have hw' : w = ∅ ∧ a.carrier.Nonempty := hw
    simp [hw'.1]

end WhyGrade

/-! ## The edge annotation and its powers -/

section WhyEdge

/-- **The edge annotation**: `m` witnesses, one variable each. -/
def whyEdge (m : ℕ) : Why ℕ := ⟨{s | ∃ i < m, s = {i}}⟩

theorem mem_mul_carrier {a b : Why ℕ} {z : Set ℕ} :
    z ∈ (a * b).carrier ↔ ∃ x y, x ∈ a.carrier ∧ y ∈ b.carrier ∧ z = x ∪ y := Iff.rfl

/-- **The powers of the edge annotation**: the non-empty sets of at most `j`
of its variables. -/
theorem carrier_whyEdge_pow (m : ℕ) : ∀ j, 1 ≤ j →
    ((whyEdge m) ^ j).carrier = {s | s ⊆ {i | i < m} ∧ s.Nonempty ∧ s.ncard ≤ j} := by
  have hfin : ∀ s : Set ℕ, s ⊆ {i | i < m} → s.Finite := fun s hs =>
    (Set.finite_lt_nat m).subset hs
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · rw [zero_add, pow_one]
      ext s
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hi,
          Set.singleton_nonempty i, by rw [Set.ncard_singleton]⟩
      · rintro ⟨hs, hne, hc⟩
        have h1 : s.ncard = 1 := le_antisymm hc
          (Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (hfin s hs)).2 hne).ne')
        obtain ⟨i, rfl⟩ := Set.ncard_eq_one.1 h1
        exact ⟨i, hs (Set.mem_singleton i), rfl⟩
    · rw [pow_succ]
      ext s
      rw [mem_mul_carrier, ih hj']
      constructor
      · rintro ⟨x, y, ⟨hx, hxne, hxc⟩, ⟨i, hi, rfl⟩, rfl⟩
        refine ⟨Set.union_subset hx (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hi),
          hxne.mono Set.subset_union_left, ?_⟩
        calc (x ∪ {i}).ncard ≤ x.ncard + ({i} : Set ℕ).ncard := Set.ncard_union_le x {i}
          _ ≤ j + 1 := by rw [Set.ncard_singleton]; omega
      · rintro ⟨hs, ⟨i, his⟩, hc⟩
        have him : i < m := hs his
        by_cases hcj : s.ncard ≤ j
        · exact ⟨s, {i}, ⟨hs, ⟨i, his⟩, hcj⟩, ⟨i, him, rfl⟩,
            (Set.union_eq_left.2 (Set.singleton_subset_iff.2 his)).symm⟩
        · have hsc : s.ncard = j + 1 := by omega
          have hdc : (s \ {i}).ncard = j := by
            rw [Set.ncard_sdiff_singleton_of_mem his]; omega
          refine ⟨s \ {i}, {i}, ⟨fun z hz => hs hz.1, ?_, le_of_eq hdc⟩, ⟨i, him, rfl⟩, ?_⟩
          · exact Set.nonempty_of_ncard_ne_zero (by omega)
          · rw [Set.sdiff_union_self, Set.union_eq_left.2 (Set.singleton_subset_iff.2 his)]

/-- **All the variables are one witness of the `m`-th power.** -/
theorem range_mem_whyEdge_pow {m : ℕ} (hm : 1 ≤ m) :
    {i | i < m} ∈ ((whyEdge m) ^ m).carrier := by
  rw [carrier_whyEdge_pow m m hm]
  refine ⟨subset_rfl, ⟨0, hm⟩, ?_⟩
  have : ({i | i < m} : Set ℕ) = ↑(Finset.range m) := by ext; simp
  rw [this, Set.ncard_coe_finset, Finset.card_range]

/-- **The powers stop growing at `m`.** -/
theorem whyEdge_pow_succ_le {m : ℕ} (hm : 1 ≤ m) :
    ((whyEdge m) ^ (m + 1)).carrier ⊆ ((whyEdge m) ^ m).carrier := by
  rw [carrier_whyEdge_pow m m hm, carrier_whyEdge_pow m (m + 1) (by omega)]
  rintro s ⟨hs, hne, -⟩
  refine ⟨hs, hne, ?_⟩
  have : ({i | i < m} : Set ℕ) = ↑(Finset.range m) := by ext; simp
  calc s.ncard ≤ ({i | i < m} : Set ℕ).ncard :=
        Set.ncard_le_ncard hs (Set.finite_lt_nat m)
    _ = m := by rw [this, Set.ncard_coe_finset, Finset.card_range]

theorem carrier_le_sum (f : ℕ → Why ℕ) {k i : ℕ} (hi : i < k) :
    (f i).carrier ⊆ (∑ j ∈ Finset.range k, f j).carrier := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi)]
  exact Set.subset_union_left

/-- **The partial sums of the edge's powers stop growing at `m`.** -/
theorem sum_whyEdge_pow_succ {m : ℕ} (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range (m + 2), (whyEdge m) ^ j = ∑ j ∈ Finset.range (m + 1), (whyEdge m) ^ j := by
  rw [Finset.sum_range_succ]
  refine Why.ext (Set.union_eq_left.2 ?_)
  exact (whyEdge_pow_succ_le hm).trans (carrier_le_sum _ (Nat.lt_succ_self m))

end WhyEdge

/-! ### A self-loop on one tuple -/

section Loop

variable {α R : Type} [DecidableEq α] [CommSemiring R]

omit [DecidableEq α] in
theorem rounds_loop (z : α) (w : R) :
    ∀ j, PathSum.rounds {(z, 1)} (fun _ => {(z, w)}) j = {(z, w ^ j)}
  | 0 => by simp [PathSum.rounds]
  | j + 1 => by
    rw [PathSum.rounds, rounds_loop z w j]
    simp [PathSum.lin, pow_succ]

theorem wt_trunc_loop (z : α) (w : R) (k : ℕ) :
    PathSum.wt (PathSum.trunc {(z, 1)} (fun _ => {(z, w)}) k) z = ∑ j ∈ Finset.range k, w ^ j := by
  rw [PathSum.wt_trunc]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rounds_loop, PathSum.wt, Multiset.filter_singleton, ite_eq_left rfl]
  simp

theorem mem_iterate_loop (z : α) (w : R) {k : ℕ} (hk : 1 ≤ k) :
    (z, ∑ j ∈ Finset.range k, w ^ j)
      ∈ (PathSum.stepK {(z, 1)} (fun _ => {(z, w)}))^[k] 0 := by
  rw [PathSum.iterate_stepK_eq, ← wt_trunc_loop z w k]
  unfold PathSum.dedupK
  refine Multiset.mem_map_of_mem _ (Multiset.mem_dedup.2 (Multiset.mem_map.2
    ⟨(z, 1), ?_, rfl⟩))
  unfold PathSum.trunc
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Finset.sum_range_succ']
  exact Multiset.mem_add.2 (Or.inr (by simp [PathSum.rounds]))

theorem supp_trunc_loop (z : α) (w : R) {k : ℕ} (hk : 1 ≤ k) :
    PathSum.supp (PathSum.trunc {(z, 1)} (fun _ => {(z, w)}) k) = {z} := by
  ext v
  rw [PathSum.mem_supp, Finset.mem_singleton]
  constructor
  · rintro ⟨p, hp, rfl⟩
    unfold PathSum.trunc at hp
    obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 hp
    rw [rounds_loop, Multiset.mem_singleton] at hj
    rw [hj]
  · intro hv
    rw [hv]
    refine ⟨(z, 1), ?_, rfl⟩
    unfold PathSum.trunc
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [Finset.sum_range_succ']
    exact Multiset.mem_add.2 (Or.inr (by simp [PathSum.rounds]))

/-- **The loop settles where its partial sums do.** -/
theorem iterate_loop_succ (z : α) (w : R) {k : ℕ} (hk : 1 ≤ k)
    (h : ∑ j ∈ Finset.range (k + 1), w ^ j = ∑ j ∈ Finset.range k, w ^ j) :
    (PathSum.stepK {(z, 1)} (fun _ => {(z, w)}))^[k + 1] 0
      = (PathSum.stepK {(z, 1)} (fun _ => {(z, w)}))^[k] 0 := by
  rw [PathSum.iterate_stepK_eq, PathSum.iterate_stepK_eq]
  refine PathSum.dedupK_congr (by rw [supp_trunc_loop z w hk, supp_trunc_loop z w (by omega)])
    fun v => ?_
  by_cases hv : v = z
  · subst hv; rw [wt_trunc_loop, wt_trunc_loop, h]
  · rw [PathSum.wt_trunc, PathSum.wt_trunc]
    have : ∀ j, PathSum.wt (PathSum.rounds {(z, 1)} (fun _ => {(z, w)}) j) v = 0 := fun j => by
      rw [rounds_loop, PathSum.wt, Multiset.filter_singleton,
        ite_eq_right (fun h => hv h.symm)]
      simp
    simp [this]

end Loop

/-! ## The witness -/

section Witness

noncomputable instance : DecidableEq (Why ℕ) := Classical.decEq _

open Classical in
noncomputable instance : HasAltLinearOrder (Why ℕ) := ⟨linearOrderOfSTO WellOrderingRel⟩

/-- **The instances**: `R` holds `0` annotated `𝟙`, and `S` holds `0`
annotated by the `m` one-variable witnesses. -/
def dWhy (m : ℕ) : AnnotatedDatabase ℕ (Why ℕ) :=
  AnnotatedDatabase.assign "R"
    (({(((fun _ => 0) : Tuple ℕ 1), (1 : Why ℕ))}
      : Multiset (AnnotatedTuple ℕ (Why ℕ) 1)) : AnnotatedRelation ℕ (Why ℕ) 1)
    (AnnotatedDatabase.assign "S"
      (({(((fun _ => 0) : Tuple ℕ 1), whyEdge m)}
        : Multiset (AnnotatedTuple ℕ (Why ℕ) 1)) : AnnotatedRelation ℕ (Why ℕ) 1) [])

/-- **The body**: the recursive relation joined with `S`, kept on `S`'s
column. -/
def whyBody : AggQueryIn ℕ 0 1 (ColKind.allReg 1) [("X", 1)] :=
  AggQueryIn.Proj (fun _ : Fin 1 => ProjColIn.term (TermGIn.index 1 rfl))
    (AggQueryIn.Prod (AggQueryIn.Hole 1 "X") (AggQueryIn.Rel 1 "S"))

/-- **`μ^∪X.(R, Π₂(X × S))`.** -/
def whyWitness : AggQuery ℕ 1 (ColKind.allReg 1) :=
  AggQueryIn.MuSet "X" (AggQueryIn.Rel 1 "R") whyBody

theorem ann_whyBase (m : ℕ) (γ : Fin 0 → ℕ) (E : EvalEnv ℕ (Why ℕ)) :
    (AggQueryIn.Rel 1 "R" : AggQueryIn ℕ 0 1 (ColKind.allReg 1)).ann (dWhy m) γ E
      = (({(((fun _ => 0) : Tuple ℕ 1), (1 : Why ℕ))} : Multiset (AnnotatedTuple ℕ (Why ℕ) 1))
        : AnnotatedRelation ℕ (Why ℕ) 1) := by
  rw [AggQueryIn.ann_Rel, dWhy, AnnotatedDatabase.find_assign]

theorem ann_whyBody (m : ℕ) (γ : Fin 0 → ℕ) (E : EvalEnv ℕ (Why ℕ)) (u : Tuple ℕ 1) :
    whyBody.ann (dWhy m) γ (E.assignHole "X"
        ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow ℕ (Why ℕ) 1)))
      = (({(((fun _ => 0) : Tuple ℕ 1), whyEdge m)} : Multiset (AnnotatedTuple ℕ (Why ℕ) 1))
        : AnnotatedRelation ℕ (Why ℕ) 1) := by
  have hS : (dWhy m).find 1 "S" = some (({(((fun _ => 0) : Tuple ℕ 1), whyEdge m)}
      : Multiset (AnnotatedTuple ℕ (Why ℕ) 1)) : AnnotatedRelation ℕ (Why ℕ) 1) := by
    rw [dWhy, AnnotatedDatabase.find_assign_of_ne _ _ _ _ (by decide),
      AnnotatedDatabase.find_assign]
  have hc : GenRow.Conforms (ColKind.allReg 1) (GenRow.ofAnnotated (u, (1 : Why ℕ))).fst :=
    fun k => rfl
  simp only [whyBody, AggQueryIn.ann, AggQueryIn.evaluate, EvalEnv.assignHole_holes_self, hS,
    Multiset.filter_singleton, hc, ite_true, Multiset.map_singleton]
  rw [show ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow ℕ (Why ℕ) 1)).product
      {GenRow.ofAnnotated ((fun _ => 0), whyEdge m)}
      = {(GenRow.ofAnnotated (u, 1), GenRow.ofAnnotated ((fun _ => 0), whyEdge m))} from
    Multiset.product_singleton _ _, Multiset.map_singleton, Multiset.map_singleton,
    Multiset.map_singleton]
  refine congrArg (fun p => ({p} : Multiset (AnnotatedTuple ℕ (Why ℕ) 1))) (Prod.ext ?_ ?_)
  · funext j
    rfl
  · simp [GenRow.toAnnotated, GenAnn.finalize, GenRow.ofAnnotated]

theorem recLinear_whyBody : whyBody.recLinear "X" 1 :=
  Or.inl ⟨⟨rfl, rfl⟩, rfl, by simp [AggQueryIn.noMention]⟩

theorem noExplode_whyBody : whyBody.noExplode := ⟨trivial, trivial⟩

/-- **The witness's round function is the self-loop's.** -/
theorem muSetStep_whyWitness (m : ℕ) (γ : Fin 0 → ℕ) :
    AggQueryIn.muSetStep "X" (AggQueryIn.Rel 1 "R") whyBody (dWhy m) γ {}
      = PathSum.stepK {(((fun _ => 0) : Tuple ℕ 1), (1 : Why ℕ))}
          (fun _ => {(((fun _ => 0) : Tuple ℕ 1), whyEdge m)}) := funext fun X => by
  rw [AggQueryIn.muSetStep, AggQueryIn.dedupAnn_eq_dedupK, PathSum.stepK]
  congr 2
  · exact ann_whyBase m γ {}
  · change whyBody.ann (dWhy m) γ _ = _
    rw [AggQueryIn.ann_of_recLinear whyBody recLinear_whyBody noExplode_whyBody (dWhy m) γ {} X]
    congr 1
    funext u
    exact ann_whyBody m γ {} u

theorem evaluate_whyWitness (m : ℕ) (γ : Fin 0 → ℕ) :
    whyWitness.evaluate (dWhy m) γ {}
      = (muFix (PathSum.stepK {(((fun _ => 0) : Tuple ℕ 1), (1 : Why ℕ))}
          (fun _ => {(((fun _ => 0) : Tuple ℕ 1), whyEdge m)}))).map GenRow.ofAnnotated := by
  rw [whyWitness, AggQueryIn.evaluate_MuSet_of_recLinear "X" _ whyBody recLinear_whyBody
    noExplode_whyBody (dWhy m) γ {}]
  congr 3
  · exact ann_whyBase m γ {}
  · funext u
    exact ann_whyBody m γ {} u

theorem muSetSettles_why {m : ℕ} (hm : 1 ≤ m) :
    MuSetSettles (PathSum.stepK {(((fun _ => 0) : Tuple ℕ 1), (1 : Why ℕ))}
      (fun _ => {(((fun _ => 0) : Tuple ℕ 1), whyEdge m)})) :=
  ⟨m + 1, iterate_loop_succ _ _ (by omega) (sum_whyEdge_pow_succ hm)⟩

theorem annSettlesAt_whyWitness {m : ℕ} (hm : 1 ≤ m) (γ : Fin 0 → ℕ) :
    whyWitness.AnnSettlesAt (dWhy m) γ {} := by
  refine ⟨trivial, ?_, fun _ => ⟨trivial, trivial⟩⟩
  rw [muSetStep_whyWitness]
  exact muSetSettles_why hm

/-- **The witness's row carries all the variables as one witness.** -/
theorem exists_mem_evaluateAnnotated_whyWitness {m : ℕ} (hm : 1 ≤ m) (γ : Fin 0 → ℕ) :
    ∃ p ∈ whyWitness.evaluateAnnotated (dWhy m) γ, {i | i < m} ∈ p.2.carrier := by
  set step := PathSum.stepK {(((fun _ => 0) : Tuple ℕ 1), (1 : Why ℕ))}
    (fun _ => {(((fun _ => 0) : Tuple ℕ 1), whyEdge m)}) with hstep
  have hfix := AggQueryIn.muFix_eq_iterate_add (muSetSettles_why hm) (m + 1)
  have hmem := mem_iterate_loop ((fun _ => 0) : Tuple ℕ 1) (whyEdge m)
    (k := muFixIdx step + (m + 1)) (by omega)
  rw [← hfix] at hmem
  refine ⟨(((fun _ => 0) : Tuple ℕ 1),
      ∑ j ∈ Finset.range (muFixIdx step + (m + 1)), (whyEdge m) ^ j), ?_,
    carrier_le_sum (fun j => (whyEdge m) ^ j) (by omega : m < muFixIdx step + (m + 1))
      (range_mem_whyEdge_pow hm)⟩
  unfold AggQueryIn.evaluateAnnotated
  rw [evaluate_whyWitness, Multiset.map_map]
  refine Multiset.mem_map.2 ⟨_, hmem, Prod.ext ?_ ?_⟩
  · rfl
  · simp [GenRow.toAnnotated, GenRow.ofAnnotated, GenAnn.finalize]

theorem overSchema_whyWitness : whyWitness.overSchema schemaRS := by
  simp [whyWitness, whyBody, AggQueryIn.overSchema, AggQueryIn.noMention, schemaRS,
    Schema.ofFn_apply, Schema.update_apply]

theorem usesOnly_whyWitness : whyWitness.usesOnly plainRecOps := by
  simp [whyWitness, whyBody, AggQueryIn.usesOnly, plainRecOps, plainOps, basisDD, basisOps,
    ProjColIn.sourceCol]

theorem inMinimalSig_whyWitness : whyWitness.inMinimalSig SeqAggFunc.count := by
  simp [whyWitness, whyBody, AggQueryIn.inMinimalSig, AggQueryIn.inSig, ProjColIn.noFun,
    TermGIn.noFun]

theorem wellKinded_whyWitness :
    whyWitness.wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  simp [whyWitness, whyBody, AggQueryIn.wellKinded, ProjColIn.outerOk, TermGIn.outerOk]
  rfl

theorem dWhy_toPlain (m : ℕ) : (dWhy m).toPlain = (dWhy 0).toPlain := by
  simp [dWhy, AnnotatedDatabase.toPlain, AnnotatedDatabase.assign, AnnotatedRelation.toPlain]

theorem dWhy_grade (m : ℕ) : ∀ k t (r : AnnotatedRelation ℕ (Why ℕ) k),
    (dWhy m).find k t = some r → ∀ a ∈ r, Why.grade 1 a.2 := by
  intro k t r hr a ha
  unfold dWhy at hr
  by_cases h₁ : k = 1 ∧ t = "R"
  · obtain ⟨rfl, rfl⟩ := h₁
    rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
    subst hr
    rw [Multiset.mem_singleton] at ha
    subst ha
    exact Why.graded.mono (Nat.zero_le 1) Why.graded.one
  · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h₁] at hr
    by_cases h₂ : k = 1 ∧ t = "S"
    · obtain ⟨rfl, rfl⟩ := h₂
      rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
      subst hr
      rw [Multiset.mem_singleton] at ha
      subst ha
      rintro w ⟨i, -, rfl⟩
      simp
    · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h₂] at hr
      exact absurd hr (by
        rw [show AnnotatedDatabase.find k t ([] : AnnotatedDatabase ℕ (Why ℕ)) = none from rfl]
        simp)

end Witness

/-! ## The row -/

/-- **`μ^∪` is in every set generating the annotated algebra over `Why[X]`**,
with the counting aggregate. Over the instances `dWhy m`, which share their
data, a query without `μ^∪` keeps its annotations within one grade
(`AggQueryIn.exists_grade`), while `μ^∪X.(R, Π₂(X × S))` gives a row with
a witness of `m` variables. -/
theorem muSet_mem_of_generatesAnn {S : Set OpKind}
    (h : GeneratesAnn ℕ (Why ℕ) schemaRS SeqAggFunc.count S) : OpKind.muSet ∈ S := by
  by_contra hS
  obtain ⟨q', ho', hu', hi', ha', hwk', hm⟩ := h whyWitness overSchema_whyWitness
    usesOnly_whyWitness inMinimalSig_whyWitness ⟨trivial, noExplode_whyBody⟩ wellKinded_whyWitness
  obtain ⟨N', D', -, -, hb⟩ := AggQueryIn.exists_grade (Why.graded (α := ℕ)) hS q' hu' hi' ha'
    (q'.hygienic_of_overSchema _ ho') (by simp) (fun p hp => absurd hp List.not_mem_nil) hwk'
    (dWhy 0).toPlain (fun k => k.elim0) (fun _ _ => 0) 0 1
  have hM : Member Why.grade 0 1 (dWhy 0).toPlain (fun k : Fin 0 => k.elim0) (fun _ _ => 0)
      (ColKind.allReg 0) HoleKinds.empty [] (dWhy (D' + 1)) {} :=
    ⟨dWhy_toPlain _, fun _ hp => absurd hp List.not_mem_nil, dWhy_grade _,
      fun _ _ r hr => absurd hr (Multiset.notMem_zero r), fun k => k.elim0,
      EvalEnv.kinded_empty _⟩
  obtain ⟨hs', he⟩ := hm (dWhy (D' + 1)) (fun k => k.elim0)
    (annSettlesAt_whyWitness (by omega) _)
  obtain ⟨p, hp, hw⟩ := exists_mem_evaluateAnnotated_whyWitness (m := D' + 1) (by omega)
    (fun k => k.elim0)
  rw [← he] at hp
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hp
  have hg := (hb (dWhy (D' + 1)) {} hM hs' r hr).finalize Why.graded _ hw
  have hcard : ({i | i < D' + 1} : Set ℕ).encard = ((D' + 1 : ℕ) : ℕ∞) := by
    have : ({i | i < D' + 1} : Set ℕ) = ↑(Finset.range (D' + 1)) := by ext; simp
    rw [this, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
  rw [hcard] at hg
  exact absurd (by exact_mod_cast hg : D' + 1 ≤ D') (by omega)

/-! ## The annotated basis theorem -/

/-- **The basis of the annotated algebra**: `{∅, Π, σ, apply, γ, win, μ^⊎,
−, μ^∪}`, the classes of the whole algebra but `ε`, `×` and `⊎`. -/
def annMuOps : Set OpKind :=
  ((plainRecOps \ {OpKind.dedup}) \ {OpKind.prod}) \ {OpKind.union}

/-- **They generate the annotated algebra over every commutative
m-semiring**: `ε` is a set recursion, `×` an apply and `⊎` a pair of bag
recursions (`generatesAnn_dedupProdSumFree`). -/
theorem generatesAnn_annMuOps {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K]
    [DecidableEq K] [HasAltLinearOrder K] (sch : Schema) (cnt : SeqAggFunc T) :
    GeneratesAnn T K sch cnt annMuOps :=
  generatesAnn_dedupProdSumFree sch cnt

/-- **No proper subset of them generates over `ℕ`, `ℕ × ℕ` and `Why[X]`
together**, with the counting aggregate: `∅`, `Π`, `γ`, `μ^⊎`, `win` and
`σ` are inherited from the plain rows, the apply because `×` is not in the
set, `−` by the zero-pattern invariant over `ℕ × ℕ`, and `μ^∪` by the
witness-size invariant over `Why[X]`. -/
theorem annMuOps_minimal {S : Set OpKind} (hS : S ⊆ annMuOps)
    (hN : ∀ sch : Schema, GeneratesAnn ℕ ℕ sch SeqAggFunc.count S)
    (hP : ∀ sch : Schema, GeneratesAnn ℕ NatPair sch SeqAggFunc.count S)
    (hW : ∀ sch : Schema, GeneratesAnn ℕ (Why ℕ) sch SeqAggFunc.count S) :
    S = annMuOps := by
  refine Set.Subset.antisymm hS fun x hx => ?_
  have hout : ∀ y, y ∈ S → y ∉ annMuOps → False := fun y hy hn => hn (hS hy)
  obtain ⟨he, hp, hg, hmu, hw, hsel, hpa⟩ := required_mem_of_generatesAnn hN
  cases x with
  | empty => exact he
  | proj => exact hp
  | sel => exact hsel
  | prod => exact absurd hx (by simp [annMuOps])
  | apply =>
    rcases hpa with h | h
    · exact (hout _ h (by simp [annMuOps])).elim
    · exact h
  | union => exact absurd hx (by simp [annMuOps])
  | dedup => exact absurd hx (by simp [annMuOps])
  | diff => exact diff_mem_of_generatesAnn (hP schemaRS)
  | gamma => exact hg
  | win => exact hw
  | muBag => exact hmu
  | muSet => exact muSet_mem_of_generatesAnn (hW schemaRS)

/-- **The annotated basis theorem**: `{∅, Π, σ, apply, γ, win, μ^⊎, −, μ^∪}`
generates the annotated algebra in the minimal universe over every
commutative m-semiring, and no proper subset of it does over all of them.
In particular set recursion is required: over `Why[X]` no set of classes
without `μ^∪` generates (`muSet_mem_of_generatesAnn`). -/
theorem annMuOps_isBasis :
    (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
      (sch : Schema), GeneratesAnn ℕ K sch SeqAggFunc.count annMuOps)
    ∧ ∀ S ⊆ annMuOps,
      (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
        (sch : Schema), GeneratesAnn ℕ K sch SeqAggFunc.count S) →
      S = annMuOps :=
  ⟨fun _ _ _ _ sch => generatesAnn_annMuOps sch _,
    fun _ hS h => annMuOps_minimal hS (h ℕ) (h NatPair) (h (Why ℕ))⟩

/-- **With `ε` in place of `μ^∪` the classes do not generate over `Why[X]`**:
the set `{∅, Π, σ, apply, γ, win, μ^⊎, ε, −}`, which generates over the
semirings of `AnnBasisClass`, misses `μ^∪`. -/
theorem not_generatesAnn_annEpsOps_why :
    ¬ GeneratesAnn ℕ (Why ℕ) schemaRS SeqAggFunc.count annEpsOps :=
  fun h => absurd (muSet_mem_of_generatesAnn h) (by simp [annEpsOps])


/-! ## Up to `≈` -/

section Approx

/-- **The classes `{∅, Π, σ, apply, γ, win, μ^⊎, −, μ^∪}` generate the
annotated algebra up to `≈` over every commutative m-semiring**: each pass
agrees with its source row by row up to finalization, which is what `≈`
reads. -/
theorem generatesAnnZ_annMuOps {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K]
    [DecidableEq K] [HasAltLinearOrder K] (sch : Schema) (cnt : SeqAggFunc T) :
    GeneratesAnnZ T K sch cnt annMuOps := by
  intro n κ q ho hu hi ha hp
  -- `ε` as a set recursion
  obtain ⟨f, hf, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch q.names
  have ho₁ := overSchema_dedupFree q f hfr sch hfsch ho
  have hu₁ := usesOnly_dedupFree (by simp [plainRecOps, plainOps, basisDD, basisOps])
    (by simp [plainRecOps]) q f hu
  have hi₁ := inSig_dedupFree q f hi
  have ha₁ := noExplode_dedupFree q f ha
  have hp₁ := wellKinded_dedupFree q f hp
  set q₁ := dedupFree f q
  -- `×` as an apply
  have ho₂ := overSchema_prodFree q₁ sch ho₁
  have hu₂ := usesOnly_prodFree (mem_diff_dedup (by simp [plainRecOps, plainOps, basisDD,
      basisOps]) (by decide))
    (mem_diff_dedup (by simp [plainRecOps, plainOps, basisDD, basisOps]) (by decide))
    q₁ (by simp) hu₁
  set q₂ := prodFree q₁
  -- `⊎` as two bag recursions
  have hS : AggQueryIn.sumMuOps ⊆ annMuOps := by
    intro o ho
    simp only [AggQueryIn.sumMuOps, Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [annMuOps, plainRecOps, plainOps, basisDD, basisOps]
  have hu₂' : q₂.usesOnly (insert OpKind.union annMuOps) :=
    AggQueryIn.usesOnly_mono (fun o h => by
      by_cases hou : o = OpKind.union
      · exact Or.inl hou
      · exact Or.inr ⟨h, hou⟩) q₂ hu₂
  obtain ⟨g, hg, hgs, hgn⟩ := AggQueryIn.exists_freshSupply sch q₂.names
  obtain ⟨q₃, hs, hm⟩ := (AggQueryIn.exists_sumFreeAnn_aux hS
    (Set.mem_singleton cnt) q₂ hu₂' (AggQueryIn.hygienic_of_overSchema q₂ sch ho₂)
    (inSig_prodFree q₁ hi₁) g hg hgn).1 rfl
  refine ⟨q₃, hs.over sch hgs ho₂, hs.usesOnly, hs.inSig, hs.noExplode (noExplode_prodFree q₁ ha₁),
    hs.wellKinded _ _ (wellKinded_prodFree q₁ hp₁), fun d γ hset => ?_⟩
  have hs₁ := annSettlesAt_dedupFree q f d γ {} hset
  have hs₂ := annSettlesAt_prodFree q₁ d γ {} {} (EvalEnv.FinRel.refl _) hs₁
  have he₂ : (q₂.evaluate d γ {}).map GenRow.fin = (q₁.evaluate d γ {}).map GenRow.fin :=
    finEq_prodFree q₁ d γ {} {} (EvalEnv.FinRel.refl _)
  obtain ⟨hs₃, he₃⟩ := hm d γ {} {} (EvalEnv.FinRel.refl _) hs₂
  exact ⟨hs₃, GenRow.zeroNorm_eq_of_fin
    (he₃.symm.trans (he₂.trans (congrArg _ (evaluate_dedupFree q f d γ {}))))⟩

/-- **The witness's row, before finalization.** -/
theorem exists_mem_evaluate_whyWitness {m : ℕ} (hm : 1 ≤ m) (γ : Fin 0 → ℕ) :
    ∃ r ∈ whyWitness.evaluate (dWhy m) γ {}, {i | i < m} ∈ r.snd.finalize.carrier := by
  set step := PathSum.stepK {(((fun _ => 0) : Tuple ℕ 1), (1 : Why ℕ))}
    (fun _ => {(((fun _ => 0) : Tuple ℕ 1), whyEdge m)}) with hstep
  have hfix := AggQueryIn.muFix_eq_iterate_add (muSetSettles_why hm) (m + 1)
  have hmem := mem_iterate_loop ((fun _ => 0) : Tuple ℕ 1) (whyEdge m)
    (k := muFixIdx step + (m + 1)) (by omega)
  rw [← hfix] at hmem
  refine ⟨GenRow.ofAnnotated (((fun _ => 0) : Tuple ℕ 1),
      ∑ j ∈ Finset.range (muFixIdx step + (m + 1)), (whyEdge m) ^ j), ?_, ?_⟩
  · rw [evaluate_whyWitness]
    exact Multiset.mem_map_of_mem _ hmem
  · simp only [GenRow.ofAnnotated, GenAnn.finalize, Multiset.map_zero, Multiset.prod_zero,
      mul_one]
    exact carrier_le_sum (fun j => (whyEdge m) ^ j) (by omega : m < muFixIdx step + (m + 1))
      (range_mem_whyEdge_pow hm)

/-- **`μ^∪` is in every set generating the annotated algebra over `Why[X]`
up to `≈`**, with the counting aggregate: the witness's row is not `𝟘`, so
`≈` keeps it, and a match without `μ^∪` has no row annotated with a witness
of `m` variables. -/
theorem muSet_mem_of_generatesAnnZ {S : Set OpKind}
    (h : GeneratesAnnZ ℕ (Why ℕ) schemaRS SeqAggFunc.count S) : OpKind.muSet ∈ S := by
  by_contra hS
  obtain ⟨q', ho', hu', hi', ha', hwk', hm⟩ := h whyWitness overSchema_whyWitness
    usesOnly_whyWitness inMinimalSig_whyWitness ⟨trivial, noExplode_whyBody⟩
    wellKinded_whyWitness
  obtain ⟨N', D', -, -, hb⟩ := AggQueryIn.exists_grade (Why.graded (α := ℕ)) hS q' hu' hi' ha'
    (q'.hygienic_of_overSchema _ ho') (by simp) (fun p hp => absurd hp List.not_mem_nil) hwk'
    (dWhy 0).toPlain (fun k => k.elim0) (fun _ _ => 0) 0 1
  have hM : Member Why.grade 0 1 (dWhy 0).toPlain (fun k : Fin 0 => k.elim0) (fun _ _ => 0)
      (ColKind.allReg 0) HoleKinds.empty [] (dWhy (D' + 1)) {} :=
    ⟨dWhy_toPlain _, fun _ hp => absurd hp List.not_mem_nil, dWhy_grade _,
      fun _ _ r hr => absurd hr (Multiset.notMem_zero r), fun k => k.elim0,
      EvalEnv.kinded_empty _⟩
  obtain ⟨hs', he⟩ := hm (dWhy (D' + 1)) (fun k => k.elim0)
    (annSettlesAt_whyWitness (by omega) _)
  obtain ⟨r, hr, hw⟩ := exists_mem_evaluate_whyWitness (m := D' + 1) (by omega)
    (fun k => k.elim0)
  have hz : r.snd.finalize ≠ 0 := fun h0 => by
    rw [h0] at hw
    exact hw
  obtain ⟨r', hr', hfin⟩ := GenRow.exists_finalize_of_zeroNorm he hr hz
  have hg := (hb (dWhy (D' + 1)) {} hM hs' r' hr').finalize Why.graded _ (hfin ▸ hw)
  have hcard : ({i | i < D' + 1} : Set ℕ).encard = ((D' + 1 : ℕ) : ℕ∞) := by
    have : ({i | i < D' + 1} : Set ℕ) = ↑(Finset.range (D' + 1)) := by ext; simp
    rw [this, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
  rw [hcard] at hg
  exact absurd (by exact_mod_cast hg : D' + 1 ≤ D') (by omega)

/-- **No proper subset of `{∅, Π, σ, apply, γ, win, μ^⊎, −, μ^∪}` generates
up to `≈` over `𝔹`, `ℕ × ℕ` and `Why[X]` together**, with the counting
aggregate: the six plain rows through the Boolean support, `−` by the
zero-pattern invariant, `μ^∪` by the witness-size invariant. -/
theorem annMuOps_minimal_approx {S : Set OpKind} (hS : S ⊆ annMuOps)
    (hB : ∀ sch : Schema, GeneratesAnnZ ℕ BoolNone sch SeqAggFunc.count S)
    (hP : ∀ sch : Schema, GeneratesAnnZ ℕ NatPair sch SeqAggFunc.count S)
    (hW : ∀ sch : Schema, GeneratesAnnZ ℕ (Why ℕ) sch SeqAggFunc.count S) :
    S = annMuOps := by
  refine Set.Subset.antisymm hS fun x hx => ?_
  have hout : ∀ y, y ∈ S → y ∉ annMuOps → False := fun y hy hn => hn (hS hy)
  cases x with
  | empty => exact empty_mem_of_generatesAnnZ (hB _)
  | proj => exact proj_mem_of_generatesAnnZ (hB _)
  | sel => exact sel_mem_of_generatesAnnZ (hB _)
  | prod => exact absurd hx (by simp [annMuOps])
  | apply =>
    rcases prod_or_apply_mem_of_generatesAnnZ (hB _) with h | h
    · exact (hout _ h (by simp [annMuOps])).elim
    · exact h
  | union => exact absurd hx (by simp [annMuOps])
  | dedup => exact absurd hx (by simp [annMuOps])
  | diff => exact diff_mem_of_generatesAnnZ (hP schemaRS)
  | gamma => exact gamma_mem_of_generatesAnnZ (hB Schema.empty)
  | win => exact win_mem_of_generatesAnnZ (hB _)
  | muBag => exact muBag_mem_of_generatesAnnZ SeqAggFunc.isCount_count_nat.readsCount (hB _)
  | muSet => exact muSet_mem_of_generatesAnnZ (hW schemaRS)

/-- **The annotated basis theorem up to `≈`**: `{∅, Π, σ, apply, γ, win,
μ^⊎, −, μ^∪}` generates
the annotated algebra up to `≈` over every commutative m-semiring, and no
proper subset of it does over all of them – set recursion being required
over `Why[X]` (`muSet_mem_of_generatesAnnZ`). -/
theorem annMuOps_isBasis_approx :
    (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
      (sch : Schema), GeneratesAnnZ ℕ K sch SeqAggFunc.count annMuOps)
    ∧ ∀ S ⊆ annMuOps,
      (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
        (sch : Schema), GeneratesAnnZ ℕ K sch SeqAggFunc.count S) →
      S = annMuOps :=
  ⟨fun _ _ _ _ sch => generatesAnnZ_annMuOps sch _,
    fun _ hS h => annMuOps_minimal_approx hS (h BoolNone) (h NatPair) (h (Why ℕ))⟩

/-- **Nor up to `≈`**: with `ε` in place of `μ^∪` the classes do not
generate over `Why[X]` even when rows annotated `𝟘` are dropped. -/
theorem not_generatesAnnZ_annEpsOps_why :
    ¬ GeneratesAnnZ ℕ (Why ℕ) schemaRS SeqAggFunc.count annEpsOps :=
  fun h => absurd (muSet_mem_of_generatesAnnZ h) (by simp [annEpsOps])

end Approx