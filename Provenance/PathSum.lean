/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Ring

/-!
# Linear recursions over a semiring, read path by path

A set recursion whose body reads its recursive relation once is *linear*:
its round function is `X ↦ ε(B ⊎ X ⊳ G)`, where `X ⊳ G` sends a row
`(u, a)` to the rows of `G u`, each annotated by `a` times its own
annotation, and `ε` sums the annotations of the copies of a tuple. Its
`k`-th iterate is therefore `ε` of the sum of the first `k` rounds
`B, B ⊳ G, (B ⊳ G) ⊳ G, …` (`iterate_step_eq`), and the weight of a tuple
in round `j` is the sum, over the paths of `j` steps ending at it, of the
product of the annotations along the path (`y_eq_sum_pathsTo`).

The paths give the two facts a bounded simulation of the recursion needs.
Over a finite set `S` of tuples, a path of more than `|S|` steps repeats a
tuple, and the cycle between the two occurrences can be cut or pumped
(`pw_append_cons`):

* in an **absorptive** semiring (`𝟙 ⊕ a = 𝟙`), a path through a cycle is
  absorbed by the path with the cycle cut, so the rounds past `|S|` add
  nothing (`x_add_y_of_absorptive`);
* in a semiring with **no zero divisors**, a path of non-zero weight
  through a cycle pumps into paths of every larger length, so the rounds
  past `|S|` vanish wherever some round does (`y_eq_zero_of_eq_zero`).

Either way a recursion that settles does so within `|S|` rounds
(`iterate_succ_eq_of_settles`). The data part, which annotations do not
see, is the same argument over `ℕ` (`exists_lt_ne_zero`).
-/

open Finset

namespace PathSum

variable {α R : Type} [DecidableEq α]

section Paths

variable [CommSemiring R] (S : Finset α) (b : α → R) (g : α → α → R)

/-- The weights of the rounds of a linear recursion: `b` at round `0`,
then each tuple's weight pushed along `g`. -/
def y : ℕ → α → R
  | 0 => b
  | j + 1 => fun v => ∑ u ∈ S, y j u * g u v

/-- The weight of the first `M` rounds. -/
def x (M : ℕ) (v : α) : R := ∑ j ∈ range M, y S b g j v

/-- The weight of a path, listed from its end back to its start. -/
def pw : List α → R
  | [] => 0
  | [u] => b u
  | v :: u :: l => g u v * pw (u :: l)

/-- The product of the edge weights along a list, listed from its end. -/
def ep : List α → R
  | [] => 1
  | [_] => 1
  | v :: u :: l => g u v * ep (u :: l)

omit [DecidableEq α] in
/-- **A path factors at any of its tuples**: the edges up to it, times
the path from it back to the start. -/
theorem pw_append_cons (a : α) (m : List α) :
    ∀ l₁ : List α, pw b g (l₁ ++ a :: m) = ep g (l₁ ++ [a]) * pw b g (a :: m)
  | [] => by simp [ep]
  | [v] => by simp [pw, ep]
  | v :: w :: l => by
    have ih := pw_append_cons a m (w :: l)
    simp only [List.cons_append] at ih ⊢
    rw [pw, ep, ih, mul_assoc]

/-- The paths of `j` steps through `S` ending at `v`. -/
def pathsTo : ℕ → α → Finset (List α)
  | 0, v => if v ∈ S then {[v]} else ∅
  | j + 1, v => if v ∈ S then S.biUnion (fun u => (pathsTo j u).image (v :: ·)) else ∅

theorem mem_pathsTo : ∀ (j : ℕ) (v : α) (l : List α),
    l ∈ pathsTo S j v ↔ l.length = j + 1 ∧ l.head? = some v ∧ ∀ a ∈ l, a ∈ S
  | 0, v, l => by
    unfold pathsTo
    split_ifs with hv
    · simp only [mem_singleton]
      constructor
      · rintro rfl; simp [hv]
      · rintro ⟨hl, hh, -⟩
        match l, hl with
        | [w], _ => simp at hh; rw [hh]
    · simp only [notMem_empty, false_iff]
      rintro ⟨hl, hh, hS⟩
      match l, hl with
      | [w], _ => simp at hh; exact hv (hh ▸ hS w (by simp))
  | j + 1, v, l => by
    unfold pathsTo
    split_ifs with hv
    · simp only [mem_biUnion, mem_image]
      constructor
      · rintro ⟨u, hu, t, ht, rfl⟩
        obtain ⟨h₁, -, h₃⟩ := (mem_pathsTo j u t).1 ht
        refine ⟨by simp [h₁], rfl, ?_⟩
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hv
        · exact h₃ a ha
      · rintro ⟨hl, hh, hS⟩
        match l, hl with
        | w :: t, hl =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          match t, hl with
          | u :: t', hl =>
            refine ⟨u, hS u (by simp), u :: t', (mem_pathsTo j u _).2 ⟨?_, rfl, ?_⟩, rfl⟩
            · simpa using hl
            · intro a ha; exact hS a (List.mem_cons_of_mem _ ha)
    · simp only [notMem_empty, false_iff]
      rintro ⟨hl, hh, hS⟩
      match l, hl with
      | w :: t, _ =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        exact hv (hh ▸ hS w (by simp))

theorem eq_cons_of_mem_pathsTo {j : ℕ} {v : α} {l : List α} (h : l ∈ pathsTo S j v) :
    ∃ t, l = v :: t := by
  obtain ⟨-, hh, -⟩ := (mem_pathsTo S j v l).1 h
  match l, hh with
  | w :: t, hh => simp only [List.head?_cons, Option.some.injEq] at hh; exact ⟨t, hh ▸ rfl⟩

/-- **The rounds are path sums**: the weight of `v` at round `j` is the sum
of the weights of the paths of `j` steps through `S` ending at `v`. -/
theorem y_eq_sum_pathsTo (hb : ∀ u, u ∉ S → b u = 0)
    (hg : ∀ u ∈ S, ∀ v, v ∉ S → g u v = 0) :
    ∀ (j : ℕ) (v : α), y S b g j v = ∑ l ∈ pathsTo S j v, pw b g l
  | 0, v => by
    unfold pathsTo
    split_ifs with hv
    · simp [y, pw]
    · simp [y, hb v hv]
  | j + 1, v => by
    simp only [y]
    unfold pathsTo
    split_ifs with hv
    · rw [sum_biUnion]
      · refine sum_congr rfl fun u _ => ?_
        rw [y_eq_sum_pathsTo hb hg j u, sum_mul,
          sum_image (fun l₁ _ l₂ _ h => List.cons_injective h)]
        refine sum_congr rfl fun l hl => ?_
        obtain ⟨t, rfl⟩ := eq_cons_of_mem_pathsTo S hl
        rw [pw, mul_comm]
      · intro u _ u' _ hne
        simp only [Function.onFun]
        rw [disjoint_left]
        intro l hl hl'
        simp only [mem_image] at hl hl'
        obtain ⟨t, ht, rfl⟩ := hl
        obtain ⟨t', ht', he⟩ := hl'
        obtain ⟨r, rfl⟩ := eq_cons_of_mem_pathsTo S ht
        obtain ⟨r', rfl⟩ := eq_cons_of_mem_pathsTo S ht'
        simp only [List.cons.injEq] at he
        exact hne he.2.1.symm
    · simp only [sum_empty]
      exact sum_eq_zero fun u hu => by rw [hg u hu v hv, mul_zero]

omit [DecidableEq α] in
/-- A list longer than the set it lives in repeats an element. -/
theorem exists_repeat : ∀ l : List α, ¬ l.Nodup →
    ∃ l₁ a l₂ l₃, l = l₁ ++ a :: (l₂ ++ a :: l₃)
  | [], h => absurd List.nodup_nil h
  | x :: t, h => by
    rw [List.nodup_cons, not_and_or, not_not] at h
    rcases h with hx | ht
    · obtain ⟨l₂, l₃, rfl⟩ := List.append_of_mem hx
      exact ⟨[], x, l₂, l₃, rfl⟩
    · obtain ⟨l₁, a, l₂, l₃, rfl⟩ := exists_repeat t ht
      exact ⟨x :: l₁, a, l₂, l₃, rfl⟩

/-- **The cycle a long path goes through**: a path of `M ≥ |S|` steps is a
shorter path with a cycle spliced in, whose weight it multiplies. -/
theorem exists_cut {M : ℕ} {v : α} {l : List α} (hM : S.card ≤ M) (hl : l ∈ pathsTo S M v) :
    ∃ l₁ a l₂ l₃, l = l₁ ++ a :: (l₂ ++ a :: l₃)
      ∧ l₁ ++ a :: l₃ ∈ pathsTo S (M - (l₂.length + 1)) v
      ∧ l₂.length + 1 ≤ M := by
  obtain ⟨hlen, hh, hS⟩ := (mem_pathsTo S M v l).1 hl
  have hnd : ¬ l.Nodup := fun hnd => by
    have := List.toFinset_card_of_nodup hnd
    have hsub : l.toFinset ⊆ S := fun a ha => hS a (List.mem_toFinset.1 ha)
    have := card_le_card hsub
    omega
  obtain ⟨l₁, a, l₂, l₃, rfl⟩ := exists_repeat l hnd
  simp only [List.length_append, List.length_cons] at hlen
  refine ⟨l₁, a, l₂, l₃, rfl, (mem_pathsTo S _ v _).2 ⟨?_, ?_, ?_⟩, by omega⟩
  · simp only [List.length_append, List.length_cons]; omega
  · cases l₁ with
    | nil => simpa using hh
    | cons w t => simpa using hh
  · intro c hc
    apply hS
    simp only [List.mem_append, List.mem_cons] at hc ⊢
    tauto

omit [DecidableEq α] in
/-- The weight of a path is that of the path with its cycle cut, times
the cycle's. -/
theorem pw_cut (l₁ : List α) (a : α) (l₂ l₃ : List α) :
    pw b g (l₁ ++ a :: (l₂ ++ a :: l₃))
      = pw b g (l₁ ++ a :: l₃) * ep g (a :: (l₂ ++ [a])) := by
  rw [pw_append_cons, pw_append_cons]
  have := pw_append_cons b g a l₃ (a :: l₂)
  simp only [List.cons_append] at this
  rw [this]
  ring

/-- **Absorption**: in an absorptive semiring the round of `M ≥ |S|` steps
adds nothing to the rounds before it. -/
theorem x_add_y_of_absorptive (habs : ∀ a : R, 1 + a = 1) (hb : ∀ u, u ∉ S → b u = 0)
    (hg : ∀ u ∈ S, ∀ v, v ∉ S → g u v = 0) {M : ℕ} (hM : S.card ≤ M) (v : α) :
    x S b g M v + y S b g M v = x S b g M v := by
  rw [y_eq_sum_pathsTo S b g hb hg]
  suffices ∀ F ⊆ pathsTo S M v, x S b g M v + ∑ l ∈ F, pw b g l = x S b g M v from
    this _ subset_rfl
  intro F
  induction F using Finset.induction_on with
  | empty => simp
  | insert l F hlF ih =>
    intro hF
    rw [sum_insert hlF, add_comm (pw b g l), ← add_assoc, ih (subset_trans (subset_insert _ _) hF)]
    obtain ⟨l₁, a, l₂, l₃, rfl, hc, hlt⟩ := exists_cut S hM (hF (mem_insert_self _ _))
    rw [pw_cut]
    set j' := M - (l₂.length + 1)
    have hj' : j' ∈ range M := mem_range.2 (by omega)
    unfold x
    rw [← add_sum_erase _ _ hj', y_eq_sum_pathsTo S b g hb hg, ← add_sum_erase _ _ hc]
    have : pw b g (l₁ ++ a :: l₃) + pw b g (l₁ ++ a :: l₃) * ep g (a :: (l₂ ++ [a]))
        = pw b g (l₁ ++ a :: l₃) := by
      rw [← mul_one (pw b g (l₁ ++ a :: l₃)), mul_assoc, one_mul, ← mul_add, habs]
    calc _ = (pw b g (l₁ ++ a :: l₃) + pw b g (l₁ ++ a :: l₃) * ep g (a :: (l₂ ++ [a])))
          + ∑ l ∈ (pathsTo S j' v).erase (l₁ ++ a :: l₃), pw b g l
          + ∑ j ∈ (range M).erase j', y S b g j v := by ring
      _ = _ := by rw [this]

end Paths

section Ordered

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  (S : Finset α) (b : α → R) (g : α → α → R)

/-- **A long path can be shortened**: a tuple of non-zero weight at a round
of `M ≥ |S|` steps already has non-zero weight at an earlier one. -/
theorem exists_lt_ne_zero (hb : ∀ u, u ∉ S → b u = 0)
    (hg : ∀ u ∈ S, ∀ v, v ∉ S → g u v = 0) {M : ℕ} (hM : S.card ≤ M) {v : α}
    (h : y S b g M v ≠ 0) : ∃ j < M, y S b g j v ≠ 0 := by
  rw [y_eq_sum_pathsTo S b g hb hg] at h
  obtain ⟨l, hl, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨l₁, a, l₂, l₃, rfl, hc, hlt⟩ := exists_cut S hM hl
  refine ⟨M - (l₂.length + 1), by omega, ?_⟩
  rw [y_eq_sum_pathsTo S b g hb hg]
  intro h0
  rw [sum_eq_zero_iff] at h0
  apply hne
  rw [pw_cut, h0 _ hc, zero_mul]

/-- The path with its cycle gone round `k + 1` times. -/
def pumped (a : α) (l₂ l₃ : List α) : ℕ → List α
  | 0 => a :: l₃
  | k + 1 => a :: (l₂ ++ pumped a l₂ l₃ k)

omit [DecidableEq α] [PartialOrder R] [CanonicallyOrderedAdd R] in
theorem pw_pumped (a : α) (l₂ l₃ : List α) :
    ∀ k, pw b g (pumped a l₂ l₃ k) = ep g (a :: (l₂ ++ [a])) ^ k * pw b g (a :: l₃)
  | 0 => by simp [pumped]
  | k + 1 => by
    have hk : ∃ t, pumped a l₂ l₃ k = a :: t := by cases k <;> exact ⟨_, rfl⟩
    obtain ⟨t, ht⟩ := hk
    have := pw_append_cons b g a t (a :: l₂)
    simp only [List.cons_append] at this
    simp only [pumped, ← List.cons_append]
    rw [ht, List.cons_append, this, ← ht, pw_pumped a l₂ l₃ k, pow_succ]
    simp only [List.cons_append]
    ring

omit [DecidableEq α] in
theorem length_pumped (a : α) (l₂ l₃ : List α) :
    ∀ k, (pumped a l₂ l₃ k).length = l₃.length + 1 + k * (l₂.length + 1)
  | 0 => by simp [pumped]
  | k + 1 => by
    simp only [pumped, List.length_cons, List.length_append, length_pumped a l₂ l₃ k]
    ring

omit [DecidableEq α] in
theorem mem_pumped (a : α) (l₂ l₃ : List α) (c : α) :
    ∀ k, c ∈ pumped a l₂ l₃ k → c = a ∨ c ∈ l₂ ∨ c ∈ l₃
  | 0, h => by simp only [pumped, List.mem_cons] at h; tauto
  | k + 1, h => by
    simp only [pumped, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact mem_pumped a l₂ l₃ c k h

/-- **Pumping**: with no zero divisors, a tuple of non-zero weight at a
round of `M ≥ |S|` steps has non-zero weight at rounds as late as one
likes. -/
theorem exists_ge_ne_zero [NoZeroDivisors R] (hb : ∀ u, u ∉ S → b u = 0)
    (hg : ∀ u ∈ S, ∀ v, v ∉ S → g u v = 0) {M : ℕ} (hM : S.card ≤ M) {v : α}
    (h : y S b g M v ≠ 0) (L : ℕ) : ∃ L' ≥ L, y S b g L' v ≠ 0 := by
  rw [y_eq_sum_pathsTo S b g hb hg] at h
  obtain ⟨l, hl, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hlen, hh, hS⟩ := (mem_pathsTo S M v l).1 hl
  obtain ⟨l₁, a, l₂, l₃, rfl, -, -⟩ := exists_cut S hM hl
  have hfac : pw b g (l₁ ++ a :: (l₂ ++ a :: l₃))
      = ep g (l₁ ++ [a]) * (ep g (a :: (l₂ ++ [a])) * pw b g (a :: l₃)) := by
    rw [pw_cut, pw_append_cons]; ring
  rw [hfac] at hne
  have h₁ : ep g (l₁ ++ [a]) ≠ 0 := left_ne_zero_of_mul hne
  have h₂ : ep g (a :: (l₂ ++ [a])) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have h₃ : pw b g (a :: l₃) ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hne)
  set L' := l₁.length + l₃.length + L * (l₂.length + 1)
  refine ⟨L', ?_, ?_⟩
  · have : L ≤ L * (l₂.length + 1) := Nat.le_mul_of_pos_right L (by omega)
    omega
  have hp : l₁ ++ pumped a l₂ l₃ L ∈ pathsTo S L' v := by
    refine (mem_pathsTo S L' v _).2 ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, length_pumped, L']; ring
    · cases l₁ with
      | nil => cases L <;> simpa [pumped] using hh
      | cons w t => simpa using hh
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hS c (by simp [hc])
      · rcases mem_pumped a l₂ l₃ c L hc with rfl | hc | hc <;> exact hS _ (by simp [*])
  rw [y_eq_sum_pathsTo S b g hb hg]
  intro h0
  rw [sum_eq_zero_iff] at h0
  have := h0 _ hp
  have hpa : ∃ t, pumped a l₂ l₃ L = a :: t := by cases L <;> exact ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := hpa
  rw [ht, pw_append_cons, ← ht, pw_pumped] at this
  exact mul_ne_zero h₁ (mul_ne_zero (pow_ne_zero _ h₂) h₃) this

omit [DecidableEq α] [PartialOrder R] [CanonicallyOrderedAdd R] in
/-- A round of weight zero everywhere is followed only by such rounds. -/
theorem y_eq_zero_of_le {N : ℕ} (hN : ∀ v, y S b g N v = 0) :
    ∀ L, N ≤ L → ∀ v, y S b g L v = 0 := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => exact hN
  | succ L _ ih => intro v; simp [y, ih]

/-- **With no zero divisors, a recursion whose rounds vanish does so within
`|S|` rounds.** -/
theorem y_eq_zero_of_eq_zero [NoZeroDivisors R] (hb : ∀ u, u ∉ S → b u = 0)
    (hg : ∀ u ∈ S, ∀ v, v ∉ S → g u v = 0) {N : ℕ} (hN : ∀ v, y S b g N v = 0)
    {M : ℕ} (hM : S.card ≤ M) (v : α) : y S b g M v = 0 := by
  by_contra h
  obtain ⟨L', hL', hne⟩ := exists_ge_ne_zero S b g hb hg hM h N
  exact hne (y_eq_zero_of_le S b g hN L' hL' v)

end Ordered

section Multisets

variable [CommSemiring R]

/-- The weight of a tuple in a bag of annotated tuples: the sum of the
annotations of its copies. -/
def wt (r : Multiset (α × R)) (u : α) : R :=
  ((r.filter (fun p => p.1 = u)).map Prod.snd).sum

/-- The tuples a bag holds, whatever their annotations. -/
def supp (r : Multiset (α × R)) : Finset α := (r.map Prod.fst).toFinset

/-- **Duplicate elimination**: one copy of each tuple, annotated by its
weight – and no `δ`. -/
def dedupK (r : Multiset (α × R)) : Multiset (α × R) :=
  (r.map Prod.fst).dedup.map (fun u => (u, wt r u))

/-- **A linear round**: each row `(u, a)` of the previous round gives the
rows of `G u`, their annotations multiplied by `a`. -/
def lin {ω : Type} (G : α → Multiset (ω × R)) (X : Multiset (α × R)) : Multiset (ω × R) :=
  X.bind (fun p => (G p.1).map (fun q => (q.1, p.2 * q.2)))

/-- The rounds `B, B ⊳ G, (B ⊳ G) ⊳ G, …`. -/
def rounds (B : Multiset (α × R)) (G : α → Multiset (α × R)) : ℕ → Multiset (α × R)
  | 0 => B
  | j + 1 => lin G (rounds B G j)

/-- The sum of the first `k` rounds. -/
def trunc (B : Multiset (α × R)) (G : α → Multiset (α × R)) (k : ℕ) : Multiset (α × R) :=
  ∑ j ∈ range k, rounds B G j

/-- The round function of the set recursion: `ε(B ⊎ X ⊳ G)`. -/
def stepK (B : Multiset (α × R)) (G : α → Multiset (α × R)) (X : Multiset (α × R)) :
    Multiset (α × R) :=
  dedupK (B + lin G X)

@[simp] theorem wt_zero (u : α) : wt (0 : Multiset (α × R)) u = 0 := by simp [wt]

theorem wt_cons (p : α × R) (X : Multiset (α × R)) (u : α) :
    wt (p ::ₘ X) u = (if p.1 = u then p.2 else 0) + wt X u := by
  unfold wt
  by_cases h : p.1 = u <;> simp [h]

theorem wt_add (X Y : Multiset (α × R)) (u : α) : wt (X + Y) u = wt X u + wt Y u := by
  simp [wt, Multiset.filter_add]

omit [CommSemiring R] in
theorem mem_supp {r : Multiset (α × R)} {u : α} : u ∈ supp r ↔ ∃ p ∈ r, p.1 = u := by
  simp [supp]

omit [CommSemiring R] in
theorem supp_add (X Y : Multiset (α × R)) : supp (X + Y) = supp X ∪ supp Y := by
  ext u; simp [supp]

theorem wt_eq_zero_of_notMem {r : Multiset (α × R)} {u : α} (h : u ∉ supp r) : wt r u = 0 := by
  unfold wt
  rw [Multiset.filter_eq_nil.2, Multiset.map_zero, Multiset.sum_zero]
  intro p hp hpu
  exact h (mem_supp.2 ⟨p, hp, hpu⟩)

/-- **A weighted sum over a bag is a sum over its tuples**, by weight. -/
theorem sum_map_mul_eq (f : α → R) (S : Finset α) :
    ∀ X : Multiset (α × R), supp X ⊆ S →
      (X.map (fun p => p.2 * f p.1)).sum = ∑ u ∈ S, wt X u * f u := by
  intro X
  induction X using Multiset.induction_on with
  | empty => intro _; simp
  | cons p X ih =>
    intro hX
    have hp : p.1 ∈ S := hX (mem_supp.2 ⟨p, Multiset.mem_cons_self _ _, rfl⟩)
    have hX' : supp X ⊆ S := fun u hu => by
      obtain ⟨q, hq, rfl⟩ := mem_supp.1 hu
      exact hX (mem_supp.2 ⟨q, Multiset.mem_cons_of_mem hq, rfl⟩)
    simp only [Multiset.map_cons, Multiset.sum_cons, ih hX', wt_cons, add_mul,
      sum_add_distrib, ite_mul, zero_mul]
    rw [sum_ite_eq S p.1 (fun u => p.2 * f u)]
    simp [hp]

omit [DecidableEq α] in
theorem wt_lin {ω : Type} [DecidableEq ω] (G : α → Multiset (ω × R)) (X : Multiset (α × R))
    (v : ω) :
    wt (lin G X) v = (X.map (fun p => p.2 * wt (G p.1) v)).sum := by
  unfold wt lin
  rw [Multiset.filter_bind, Multiset.map_bind, Multiset.sum_bind]
  congr 1
  refine Multiset.map_congr rfl fun p _ => ?_
  rw [Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp_def]
  rw [← Multiset.sum_map_mul_left]

theorem mem_supp_lin {ω : Type} [DecidableEq ω] {G : α → Multiset (ω × R)}
    {X : Multiset (α × R)} {v : ω} :
    v ∈ supp (lin G X) ↔ ∃ u ∈ supp X, v ∈ supp (G u) := by
  simp only [mem_supp, lin, Multiset.mem_bind, Multiset.mem_map]
  constructor
  · rintro ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩
    exact ⟨p.1, ⟨p, hp, rfl⟩, q, hq, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, q, hq, rfl⟩
    exact ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩

theorem supp_dedupK (r : Multiset (α × R)) : supp (dedupK r) = supp r := by
  simp [supp, dedupK, Multiset.map_map]

theorem wt_dedupK (r : Multiset (α × R)) (u : α) : wt (dedupK r) u = wt r u := by
  unfold dedupK
  conv_lhs => unfold wt
  rw [Multiset.filter_map]
  simp only [Function.comp_def]
  rw [Multiset.filter_eq' _ u, Multiset.count_dedup]
  split_ifs with h
  · simp [wt]
  · simp only [Multiset.replicate_zero, Multiset.map_zero, Multiset.sum_zero]
    exact (wt_eq_zero_of_notMem (by simpa [supp] using h)).symm

/-- **Duplicate elimination reads only the tuples held and their
weights.** -/
theorem dedupK_congr {r r' : Multiset (α × R)} (hs : supp r = supp r')
    (hw : ∀ u, wt r u = wt r' u) : dedupK r = dedupK r' := by
  unfold dedupK
  have : (r.map Prod.fst).dedup = (r'.map Prod.fst).dedup := by
    have := congrArg Finset.val hs
    simpa [supp] using this
  rw [this]
  exact Multiset.map_congr rfl fun u _ => by rw [hw]

omit [DecidableEq α] in
theorem lin_add {ω : Type} (G : α → Multiset (ω × R)) (X Y : Multiset (α × R)) :
    lin G (X + Y) = lin G X + lin G Y := Multiset.add_bind _ _ _

omit [DecidableEq α] in
@[simp] theorem lin_zero {ω : Type} (G : α → Multiset (ω × R)) : lin G 0 = 0 :=
  Multiset.zero_bind _

/-- A linear round reads its input only through its tuples and their
weights. -/
theorem dedupK_add_lin_dedupK (B : Multiset (α × R)) (G : α → Multiset (α × R))
    (Y : Multiset (α × R)) : dedupK (B + lin G (dedupK Y)) = dedupK (B + lin G Y) := by
  refine dedupK_congr ?_ fun v => ?_
  · rw [supp_add, supp_add]
    congr 1
    ext v
    rw [mem_supp_lin, mem_supp_lin, supp_dedupK]
  · rw [wt_add, wt_add, wt_lin, wt_lin,
      sum_map_mul_eq (fun u => wt (G u) v) (supp Y) _ (by rw [supp_dedupK]),
      sum_map_mul_eq (fun u => wt (G u) v) (supp Y) _ subset_rfl]
    simp only [wt_dedupK]

omit [DecidableEq α] in
theorem trunc_succ (B : Multiset (α × R)) (G : α → Multiset (α × R)) (k : ℕ) :
    trunc B G (k + 1) = trunc B G k + rounds B G k := sum_range_succ _ _

/-- **The iterates of the set recursion are `ε` of the truncated sums of
its rounds.** -/
theorem iterate_stepK_eq (B : Multiset (α × R)) (G : α → Multiset (α × R)) :
    ∀ k, (stepK B G)^[k] 0 = dedupK (trunc B G k)
  | 0 => by simp [trunc, dedupK]
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_stepK_eq B G k, stepK, dedupK_add_lin_dedupK]
    refine dedupK_congr ?_ fun v => ?_
    · have h : ∀ j, lin G (trunc B G j) = ∑ i ∈ range j, rounds B G (i + 1) := by
        intro j
        induction j with
        | zero => simp [trunc]
        | succ j ih => rw [trunc_succ, lin_add, ih, sum_range_succ]; rfl
      rw [h, trunc, sum_range_succ', add_comm]
      rfl
    · have h : ∀ j, lin G (trunc B G j) = ∑ i ∈ range j, rounds B G (i + 1) := by
        intro j
        induction j with
        | zero => simp [trunc]
        | succ j ih => rw [trunc_succ, lin_add, ih, sum_range_succ]; rfl
      rw [h, trunc, sum_range_succ', add_comm]
      rfl

/-- A set of tuples closed under the rounds. -/
structure Closed (S : Finset α) (B : Multiset (α × R)) (G : α → Multiset (α × R)) : Prop where
  base : supp B ⊆ S
  step : ∀ u ∈ S, supp (G u) ⊆ S

theorem Closed.supp_rounds {S : Finset α} {B : Multiset (α × R)} {G : α → Multiset (α × R)}
    (h : Closed S B G) : ∀ j, supp (rounds B G j) ⊆ S
  | 0 => h.base
  | j + 1 => fun v hv => by
    obtain ⟨u, hu, hv⟩ := mem_supp_lin.1 hv
    exact h.step u (h.supp_rounds j hu) hv

/-- **The weights of the rounds are the path sums of `PathSum.y`.** -/
theorem wt_rounds {S : Finset α} {B : Multiset (α × R)} {G : α → Multiset (α × R)}
    (h : Closed S B G) : ∀ j v, wt (rounds B G j) v
      = y S (wt B) (fun u v => wt (G u) v) j v
  | 0, v => rfl
  | j + 1, v => by
    simp only [rounds, y]
    rw [wt_lin, sum_map_mul_eq (fun u => wt (G u) v) S _ (h.supp_rounds j)]
    exact sum_congr rfl fun u _ => by rw [wt_rounds h j u]

theorem wt_trunc (B : Multiset (α × R)) (G : α → Multiset (α × R)) (k : ℕ) (v : α) :
    wt (trunc B G k) v = ∑ j ∈ range k, wt (rounds B G j) v := by
  induction k with
  | zero => simp [trunc]
  | succ k ih => rw [trunc_succ, wt_add, ih, sum_range_succ]

theorem mem_supp_trunc {B : Multiset (α × R)} {G : α → Multiset (α × R)} {k : ℕ} {v : α} :
    v ∈ supp (trunc B G k) ↔ ∃ j < k, v ∈ supp (rounds B G j) := by
  induction k with
  | zero => simp [trunc, supp]
  | succ k ih =>
    rw [trunc_succ, supp_add, Finset.mem_union, ih]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h

/-- **The tuples of the rounds, over `ℕ`**: a tuple is held at round `j`
exactly where the count of the paths reaching it is non-zero. -/
theorem mem_supp_rounds_iff {S : Finset α} {B : Multiset (α × R)} {G : α → Multiset (α × R)}
    (h : Closed S B G) : ∀ j v, v ∈ supp (rounds B G j) ↔
      y S (fun u => if u ∈ supp B then 1 else 0)
        (fun u v => if v ∈ supp (G u) then 1 else 0) j v ≠ (0 : ℕ)
  | 0, v => by simp [y, rounds]
  | j + 1, v => by
    simp only [rounds, y, mem_supp_lin, ne_eq, sum_eq_zero_iff, not_forall, mul_eq_zero,
      not_or, exists_prop]
    constructor
    · rintro ⟨u, hu, hv⟩
      exact ⟨u, h.supp_rounds j hu, (mem_supp_rounds_iff h j u).1 hu, by simp [hv]⟩
    · rintro ⟨u, -, hu, hv⟩
      refine ⟨u, (mem_supp_rounds_iff h j u).2 hu, ?_⟩
      by_contra hn; simp [hn] at hv

end Multisets

section Settle

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

/-- **The semirings where a linear set recursion settles within the size
of its tuple set, if at all**: the absorptive ones, and those where `⊕`
cancels and `⊗` has no zero divisors. -/
def SettlesEarly (R : Type) [CommSemiring R] : Prop :=
  (∀ a : R, 1 + a = 1) ∨ ((∀ a b : R, a + b = a → b = 0) ∧ NoZeroDivisors R)

/-- **A linear set recursion that settles does so within `|S|` rounds**, for
a set `S` of tuples closed under its rounds, in the semirings of
`SettlesEarly`. -/
theorem iterate_succ_eq_of_settles {S : Finset α} {B : Multiset (α × R)}
    {G : α → Multiset (α × R)} (h : Closed S B G) (hR : SettlesEarly R)
    (hset : ∃ N, (stepK B G)^[N + 1] 0 = (stepK B G)^[N] 0) {M : ℕ} (hM : S.card ≤ M) :
    (stepK B G)^[M + 1] 0 = (stepK B G)^[M] 0 := by
  rw [iterate_stepK_eq, iterate_stepK_eq]
  have hbS : ∀ u, u ∉ S → wt B u = 0 := fun u hu =>
    wt_eq_zero_of_notMem fun h' => hu (h.base h')
  have hgS : ∀ u ∈ S, ∀ v, v ∉ S → wt (G u) v = 0 := fun u hu v hv =>
    wt_eq_zero_of_notMem fun h' => hv (h.step u hu h')
  refine dedupK_congr ?_ fun v => ?_
  · rw [trunc_succ, supp_add]
    refine Finset.union_eq_left.2 fun v hv => ?_
    have hN := (mem_supp_rounds_iff h M v).1 hv
    obtain ⟨j, hj, hj'⟩ := exists_lt_ne_zero S _ _
      (fun u hu => by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        exact fun h' => hu (h.base h'))
      (fun u hu v hv => by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        exact fun h' => hv (h.step u hu h')) hM hN
    exact mem_supp_trunc.2 ⟨j, hj, (mem_supp_rounds_iff h j v).2 hj'⟩
  · rw [wt_trunc, wt_trunc, sum_range_succ]
    have hx : ∀ k, ∑ j ∈ range k, wt (rounds B G j) v = x S (wt B) (fun u v => wt (G u) v) k v :=
      fun k => sum_congr rfl fun j _ => wt_rounds h j v
    rw [hx, wt_rounds h]
    rcases hR with habs | ⟨hcan, hnzd⟩
    · exact x_add_y_of_absorptive S _ _ habs hbS hgS hM v
    · obtain ⟨N, hN⟩ := hset
      rw [iterate_stepK_eq, iterate_stepK_eq] at hN
      have hyN : ∀ v, y S (wt B) (fun u v => wt (G u) v) N v = 0 := fun v => by
        have := congrArg (fun r => wt r v) hN
        simp only [wt_dedupK, wt_trunc, sum_range_succ] at this
        rw [← wt_rounds h]
        exact hcan _ _ this
      rw [y_eq_zero_of_eq_zero S _ _ hbS hgS hyN hM v, add_zero]

end Settle

section Counter

/-! ### The successor counter

The bounded simulation of the set recursion runs the same rounds on pairs
of a tuple and a *counter*: the base is paired with every counter, a round
pairs each derived tuple with every counter above the current one, and the
annotation is multiplied by `𝟙` where the counter is the least one, or the
successor of the current one, and by `𝟘` elsewhere. Round `j` then holds
the tuples of round `j` of the recursion, each paired with the counters of
rank `j` or more, annotated by their weight at the `j`-th counter and `𝟘`
at the others (`wt_simRounds`, `mem_supp_simRounds`); it is empty from
the number of counters on (`simRounds_eq_zero`); and `ε` of the sum of its
rounds, read on the tuples, is the `|cs|`-th iterate of the recursion
(`dedupK_simRounds`). -/

variable [CommSemiring R] {β : Type} [DecidableEq β]

/-- The indicator of a counter being the first one. -/
def firstInd (cs : List β) (c : β) : R := if cs[0]? = some c then 1 else 0

/-- The indicator of `c'` being the counter right after `c`. -/
def succInd (cs : List β) (c c' : β) : R :=
  if c ∈ cs ∧ cs[cs.idxOf c + 1]? = some c' then 1 else 0

/-- The hypotheses the simulation's rounds are read under: the counters
listed in a strictly increasing order, the base pairing each tuple of `B`
with every counter, and a round pairing each tuple of `G t` with every
counter above `c`, the annotations multiplied by the indicators. -/
structure SimSpec (lt : β → β → Prop) (cs : List β) (B : Multiset (α × R))
    (G : α → Multiset (α × R)) (B' : Multiset ((α × β) × R))
    (G' : α × β → Multiset ((α × β) × R)) : Prop where
  sorted : cs.Pairwise lt
  irrefl : ∀ c, ¬ lt c c
  trans : ∀ a b c, lt a b → lt b c → lt a c
  base_wt : ∀ t c, wt B' (t, c) = wt B t * firstInd cs c
  base_supp : ∀ t c, (t, c) ∈ supp B' ↔ t ∈ supp B ∧ c ∈ cs
  step_wt : ∀ t c, c ∈ cs → ∀ t' c', wt (G' (t, c)) (t', c') = wt (G t) t' * succInd cs c c'
  step_supp : ∀ t c, c ∈ cs → ∀ t' c',
    (t', c') ∈ supp (G' (t, c)) ↔ t' ∈ supp (G t) ∧ c' ∈ cs ∧ lt c c'

variable {lt : β → β → Prop} {cs : List β} {B : Multiset (α × R)}
  {G : α → Multiset (α × R)} {B' : Multiset ((α × β) × R)}
  {G' : α × β → Multiset ((α × β) × R)}

/-! #### A strictly sorted list -/

omit [CommSemiring R] [DecidableEq β] in
theorem sorted_lt_iff (hs : cs.Pairwise lt) (hirr : ∀ c, ¬ lt c c)
    (htr : ∀ a b c, lt a b → lt b c → lt a c) {i i' : ℕ} (hi : i < cs.length)
    (hi' : i' < cs.length) : lt cs[i] cs[i'] ↔ i < i' := by
  constructor
  · intro hl
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · exact hirr _ (htr _ _ _ hl (List.pairwise_iff_getElem.1 hs _ _ _ _ hlt))
    · subst heq; exact hirr _ hl
  · intro hlt; exact List.pairwise_iff_getElem.1 hs _ _ _ _ hlt

omit [CommSemiring R] [DecidableEq β] in
theorem nodup_of_sorted (hs : cs.Pairwise lt) (hirr : ∀ c, ¬ lt c c) : cs.Nodup :=
  hs.imp fun {a b} hab he => by subst he; exact hirr a hab

omit [CommSemiring R] [DecidableEq β] in
/-- **The first element is the one with nothing below it.** -/
theorem getElem_zero_eq_iff (hs : cs.Pairwise lt) (hirr : ∀ c, ¬ lt c c)
    (htr : ∀ a b c, lt a b → lt b c → lt a c) {c : β} (hc : c ∈ cs) :
    cs[0]? = some c ↔ ¬ ∃ a ∈ cs, lt a c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  have h0 : 0 < cs.length := by omega
  rw [List.getElem?_eq_getElem h0, Option.some.injEq,
    (List.Nodup.getElem_inj_iff (nodup_of_sorted hs hirr))]
  constructor
  · rintro rfl ⟨a, ha, hlt⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
    exact Nat.not_lt_zero _ ((sorted_lt_iff hs hirr htr hj hi).1 hlt)
  · intro h
    by_contra hne
    exact h ⟨cs[0], List.getElem_mem h0, (sorted_lt_iff hs hirr htr h0 hi).2 (by omega)⟩

omit [CommSemiring R] in
/-- **The next element is the one with nothing between.** -/
theorem getElem_idxOf_succ_eq_iff (hs : cs.Pairwise lt) (hirr : ∀ c, ¬ lt c c)
    (htr : ∀ a b c, lt a b → lt b c → lt a c) {c c' : β} (hc : c ∈ cs) (hc' : c' ∈ cs)
    (hlt : lt c c') :
    cs[cs.idxOf c + 1]? = some c' ↔ ¬ ∃ m ∈ cs, lt c m ∧ lt m c' := by
  have hnd := nodup_of_sorted hs hirr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc'
  rw [hnd.idxOf_getElem]
  have hij := (sorted_lt_iff hs hirr htr hi hj).1 hlt
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq, List.Nodup.getElem_inj_iff hnd]
  constructor
  · rintro he ⟨m, hm, h₁, h₂⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
    have := (sorted_lt_iff hs hirr htr hi hk).1 h₁
    have := (sorted_lt_iff hs hirr htr hk hj).1 h₂
    omega
  · intro h
    by_contra hne
    exact h ⟨cs[i + 1], List.getElem_mem (by omega),
      (sorted_lt_iff hs hirr htr hi (by omega)).2 (by omega),
      (sorted_lt_iff hs hirr htr (by omega) hj).2 (by omega)⟩

theorem SimSpec.nodup (h : SimSpec lt cs B G B' G') : cs.Nodup :=
  h.sorted.imp fun {a b} hab he => by subst he; exact h.irrefl a hab

theorem SimSpec.lt_iff (h : SimSpec lt cs B G B' G') {i i' : ℕ} (hi : i < cs.length)
    (hi' : i' < cs.length) : lt cs[i] cs[i'] ↔ i < i' := by
  constructor
  · intro hl
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
    · exact h.irrefl _ (h.trans _ _ _ hl (List.pairwise_iff_getElem.1 h.sorted _ _ _ _ hlt))
    · subst heq; exact h.irrefl _ hl
  · intro hlt; exact List.pairwise_iff_getElem.1 h.sorted _ _ _ _ hlt

theorem SimSpec.succInd_get (h : SimSpec lt cs B G B' G') {j : ℕ} (hj : j < cs.length)
    (c' : β) : succInd (R := R) cs cs[j] c' = if cs[j + 1]? = some c' then 1 else 0 := by
  unfold succInd
  rw [h.nodup.idxOf_getElem]
  simp [List.getElem_mem]

theorem SimSpec.supp_rounds (h : SimSpec lt cs B G B' G') :
    ∀ j t c, (t, c) ∈ supp (rounds B' G' j)
      ↔ t ∈ supp (rounds B G j) ∧ ∃ i, j ≤ i ∧ ∃ hi : i < cs.length, cs[i] = c
  | 0, t, c => by
    simp only [rounds, h.base_supp, zero_le, true_and, List.mem_iff_getElem]
  | j + 1, t', c' => by
    simp only [rounds]
    constructor
    · intro hm
      obtain ⟨⟨t, c⟩, hu, hv⟩ := mem_supp_lin.1 hm
      obtain ⟨ht, i, hji, hi, rfl⟩ := (h.supp_rounds j t c).1 hu
      obtain ⟨ht', hc', hlt⟩ := (h.step_supp t _ (List.getElem_mem hi) t' c').1 hv
      obtain ⟨i', hi', rfl⟩ := List.mem_iff_getElem.1 hc'
      refine ⟨mem_supp_lin.2 ⟨t, ht, ht'⟩, i', ?_, hi', rfl⟩
      have := (h.lt_iff hi hi').1 hlt
      omega
    · rintro ⟨ht', i', hji', hi', rfl⟩
      obtain ⟨t, ht, ht'⟩ := mem_supp_lin.1 ht'
      have hj : j < cs.length := by omega
      refine mem_supp_lin.2 ⟨(t, cs[j]), (h.supp_rounds j t _).2 ⟨ht, j, le_rfl, hj, rfl⟩, ?_⟩
      exact (h.step_supp t _ (List.getElem_mem hj) t' _).2
        ⟨ht', List.getElem_mem hi', (h.lt_iff hj hi').2 (by omega)⟩

theorem SimSpec.supp_rounds_subset (h : SimSpec lt cs B G B' G') {S : Finset α}
    (hS : Closed S B G) (j : ℕ) : supp (rounds B' G' j) ⊆ S ×ˢ cs.toFinset := by
  rintro ⟨t, c⟩ hm
  obtain ⟨ht, i, -, hi, rfl⟩ := (h.supp_rounds j t c).1 hm
  exact Finset.mem_product.2 ⟨hS.supp_rounds j ht, List.mem_toFinset.2 (List.getElem_mem hi)⟩

/-- **The simulation's round `j` carries round `j` of the recursion at the
`j`-th counter, and `𝟘` at the others.** -/
theorem SimSpec.wt_rounds (h : SimSpec lt cs B G B' G') {S : Finset α} (hS : Closed S B G) :
    ∀ j t c, wt (rounds B' G' j) (t, c)
      = wt (rounds B G j) t * (if cs[j]? = some c then 1 else 0)
  | 0, t, c => by simp only [rounds, h.base_wt, firstInd]
  | j + 1, t', c' => by
    simp only [rounds]
    rw [wt_lin, sum_map_mul_eq (fun p => wt (G' p) (t', c')) _ _ (h.supp_rounds_subset hS j),
      wt_lin, sum_map_mul_eq (fun u => wt (G u) t') S _ (hS.supp_rounds j), sum_product]
    by_cases hj : j < cs.length
    · have hsum : ∀ t, ∑ c ∈ cs.toFinset, wt (rounds B' G' j) (t, c) * wt (G' (t, c)) (t', c')
          = wt (rounds B G j) t * (wt (G t) t' * if cs[j + 1]? = some c' then 1 else 0) := by
        intro t
        rw [sum_eq_single cs[j]]
        · rw [h.wt_rounds hS j t, List.getElem?_eq_getElem hj, ite_eq_left rfl, mul_one,
            h.step_wt t _ (List.getElem_mem hj), h.succInd_get hj]
        · intro c _ hne
          rw [h.wt_rounds hS j t, List.getElem?_eq_getElem hj, ite_eq_right (fun he => hne
            (Option.some.inj he).symm), mul_zero, zero_mul]
        · intro hn; exact absurd (List.mem_toFinset.2 (List.getElem_mem hj)) hn
      simp only [hsum, ← mul_assoc, ← sum_mul]
    · have hj' : cs[j + 1]? = none := List.getElem?_eq_none (by omega)
      rw [hj', ite_eq_right (by simp), mul_zero]
      refine sum_eq_zero fun t _ => sum_eq_zero fun c _ => ?_
      rw [h.wt_rounds hS j t, List.getElem?_eq_none (by omega), ite_eq_right (by simp), mul_zero,
        zero_mul]

omit [CommSemiring R] in
theorem supp_eq_empty_iff {r : Multiset (α × R)} : supp r = ∅ ↔ r = 0 := by
  simp [supp, Multiset.toFinset_eq_empty, Multiset.map_eq_zero]

/-- **The simulation's rounds end at the number of counters.** -/
theorem SimSpec.rounds_eq_zero (h : SimSpec lt cs B G B' G') {j : ℕ} (hj : cs.length ≤ j) :
    rounds B' G' j = 0 := by
  have : supp (rounds B' G' j) = ∅ := by
    ext ⟨t, c⟩
    simp only [Finset.notMem_empty, iff_false]
    intro hm
    obtain ⟨-, i, hji, hi, -⟩ := (h.supp_rounds j t c).1 hm
    omega
  exact supp_eq_empty_iff.1 this

/-- Forgetting the counter. -/
def dropCtr (p : (α × β) × R) : α × R := (p.1.1, p.2)

theorem wt_map_dropCtr (C : Finset β) :
    ∀ X : Multiset ((α × β) × R), (∀ p ∈ X, p.1.2 ∈ C) →
      ∀ t, wt (X.map dropCtr) t = ∑ c ∈ C, wt X (t, c) := by
  intro X
  induction X using Multiset.induction_on with
  | empty => intro _ _; simp
  | cons p X ih =>
    intro hX t
    rw [Multiset.map_cons, wt_cons, ih (fun q hq => hX q (Multiset.mem_cons_of_mem hq))]
    simp only [wt_cons, sum_add_distrib, dropCtr]
    congr 1
    obtain ⟨⟨t₀, c₀⟩, a⟩ := p
    have hc : c₀ ∈ C := hX _ (Multiset.mem_cons_self _ _)
    by_cases ht : t₀ = t
    · subst ht
      simp [hc]
    · simp only [ht, ite_false]
      exact (sum_eq_zero fun c _ => by simp [ht]).symm

omit [CommSemiring R] in
theorem mem_supp_map_dropCtr {X : Multiset ((α × β) × R)} {t : α} :
    t ∈ supp (X.map dropCtr) ↔ ∃ c, (t, c) ∈ supp X := by
  simp only [mem_supp, Multiset.mem_map, dropCtr]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact ⟨p.1.2, p, hp, rfl⟩
  · rintro ⟨c, p, hp, he⟩; exact ⟨_, ⟨p, hp, rfl⟩, by rw [he]⟩

/-- **The simulation computes the `|cs|`-th iterate of the recursion**:
`ε` of the sum of any number `L ≥ |cs|` of its rounds, with the counters
forgotten, is `ε` of the sum of the first `|cs|` rounds of the recursion. -/
theorem SimSpec.dedupK_rounds (h : SimSpec lt cs B G B' G') {S : Finset α} (hS : Closed S B G)
    {L : ℕ} (hL : cs.length ≤ L) :
    dedupK ((∑ j ∈ range L, rounds B' G' j).map dropCtr) = dedupK (trunc B G cs.length) := by
  have hmemL : ∀ k, ∀ p ∈ ∑ j ∈ range k, rounds B' G' j, p.1.2 ∈ cs.toFinset := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro p hp
      rw [sum_range_succ, Multiset.mem_add] at hp
      rcases hp with hp | hp
      · exact ih p hp
      · exact (Finset.mem_product.1 (h.supp_rounds_subset hS k
          (mem_supp.2 ⟨p, hp, rfl⟩))).2
  refine dedupK_congr ?_ fun t => ?_
  · ext t
    rw [mem_supp_map_dropCtr, mem_supp_trunc]
    have hsum : ∀ (k : ℕ) (c : β), (t, c) ∈ supp (∑ j ∈ range k, rounds B' G' j)
        ↔ ∃ j < k, (t, c) ∈ supp (rounds B' G' j) := by
      intro k c
      exact mem_supp_trunc (B := B') (G := G')
    simp only [hsum, h.supp_rounds]
    constructor
    · rintro ⟨c, j, hj, ht, i, hji, hi, -⟩
      exact ⟨j, by omega, ht⟩
    · rintro ⟨j, hj, ht⟩
      exact ⟨cs[j], j, by omega, ht, j, le_rfl, hj, rfl⟩
  · rw [wt_map_dropCtr cs.toFinset _ (hmemL L), wt_trunc]
    have : ∀ c, wt (∑ j ∈ range L, rounds B' G' j) (t, c)
        = ∑ j ∈ range L, wt (rounds B' G' j) (t, c) := fun c => wt_trunc B' G' L (t, c)
    simp only [this, h.wt_rounds hS]
    rw [sum_comm]
    have hsplit : range L = range cs.length ∪ (range L \ range cs.length) := by
      rw [Finset.union_sdiff_of_subset (Finset.range_mono hL)]
    rw [hsplit, sum_union Finset.disjoint_sdiff]
    rw [sum_eq_zero (s := range L \ range cs.length)]
    · rw [add_zero]
      refine sum_congr rfl fun j hj => ?_
      have hj : j < cs.length := mem_range.1 hj
      rw [sum_eq_single cs[j]]
      · rw [List.getElem?_eq_getElem hj, ite_eq_left rfl, mul_one]
      · intro c _ hne
        rw [List.getElem?_eq_getElem hj, ite_eq_right (fun he => hne (Option.some.inj he).symm),
          mul_zero]
      · intro hn; exact absurd (List.mem_toFinset.2 (List.getElem_mem hj)) hn
    · intro j hj
      have : cs.length ≤ j := by simp at hj; omega
      exact sum_eq_zero fun c _ => by
        rw [List.getElem?_eq_none this, ite_eq_right (by simp), mul_zero]

end Counter

section Chains

/-! ### The all-chains counter

Where `⊕` and `⊗` do not add copies – in an absorptive semiring – a
simulation need not single out the successor of a counter: a round may
pair each derived tuple with *every* counter above the current one. The
base pairs each tuple with every counter, multiplying its weight by
`bw c`, and a round from counter `c` to `c'` multiplies by `sw c c'`. Round
`j` then sums, over the paths of `j` steps and the chains of `j + 1`
counters, the path's weight times the chain's (`wt_rounds_ge`), and never
weighs more than the recursion's round (`wt_rounds_le`). So `ε` of its
rounds is the recursion's value as soon as every path through distinct
tuples of non-zero weight is absorbed by the weight of some chain
(`ChainSpec.dedupK_rounds`): a path through a cycle is absorbed by the
path with the cycle cut. -/

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R]
  {β : Type} [DecidableEq β]

/-- The hypotheses the all-chains simulation's rounds are read under: the
counters listed in a strictly increasing order, the base pairing each
tuple of `B` with every counter, its weight multiplied by `bw`, and a
round pairing each tuple of `G t` with every counter above `c`, its weight
multiplied by `sw`. -/
structure ChainSpec (lt : β → β → Prop) (cs : List β) (bw : β → R) (sw : β → β → R)
    (B : Multiset (α × R)) (G : α → Multiset (α × R)) (B' : Multiset ((α × β) × R))
    (G' : α × β → Multiset ((α × β) × R)) : Prop where
  sorted : cs.Pairwise lt
  irrefl : ∀ c, ¬ lt c c
  trans : ∀ a b c, lt a b → lt b c → lt a c
  base_wt : ∀ t c, c ∈ cs → wt B' (t, c) = wt B t * bw c
  base_supp : ∀ t c, (t, c) ∈ supp B' ↔ t ∈ supp B ∧ c ∈ cs
  step_wt : ∀ t c, c ∈ cs → ∀ t' c', c' ∈ cs → lt c c' →
    wt (G' (t, c)) (t', c') = wt (G t) t' * sw c c'
  step_supp : ∀ t c, c ∈ cs → ∀ t' c',
    (t', c') ∈ supp (G' (t, c)) ↔ t' ∈ supp (G t) ∧ c' ∈ cs ∧ lt c c'

variable {lt : β → β → Prop} {cs : List β} {bw : β → R} {sw : β → β → R}
  {B : Multiset (α × R)} {G : α → Multiset (α × R)} {B' : Multiset ((α × β) × R)}
  {G' : α × β → Multiset ((α × β) × R)}

/-! #### The order of an absorptive semiring -/

omit [DecidableEq α] [IsOrderedAddMonoid R] in
theorem le_one_of_abs (habs : ∀ a : R, 1 + a = 1) (a : R) : a ≤ 1 :=
  le_iff_exists_add.2 ⟨1, by rw [add_comm a 1, habs a]⟩

omit [DecidableEq α] [IsOrderedAddMonoid R] in
theorem mul_le_mul_of_le_right' {a b : R} (h : a ≤ b) (c : R) : a * c ≤ b * c := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_mul]
  exact le_self_add

omit [DecidableEq α] [IsOrderedAddMonoid R] in
theorem mul_le_mul_of_le' {a b c d : R} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  le_trans (mul_le_mul_of_le_right' h₁ c) (by
    rw [mul_comm b c, mul_comm b d]; exact mul_le_mul_of_le_right' h₂ b)

omit [DecidableEq α] [IsOrderedAddMonoid R] in
theorem mul_le_left_of_abs (habs : ∀ a : R, 1 + a = 1) (a b : R) : a * b ≤ a := by
  have := mul_le_mul_of_le' (le_refl a) (le_one_of_abs habs b)
  rwa [mul_one] at this

omit [DecidableEq α] [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R] in
theorem add_self_of_abs (habs : ∀ a : R, 1 + a = 1) (a : R) : a + a = a := by
  calc a + a = a * (1 + 1) := by rw [mul_add, mul_one]
    _ = a := by rw [habs, mul_one]

omit [DecidableEq α] in
/-- **A sum of terms below `x` is below `x`**, `⊕` being idempotent. -/
theorem sum_le_of_abs (habs : ∀ a : R, 1 + a = 1) {ι : Type} (s : Finset ι) (f : ι → R) (x : R)
    (h : ∀ i ∈ s, f i ≤ x) : ∑ i ∈ s, f i ≤ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, ← add_self_of_abs habs x]
    exact add_le_add (h i (mem_insert_self i s))
      (ih fun j hj => h j (mem_insert_of_mem hj))

/-! #### The supports -/

omit [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R] in
theorem ChainSpec.supp_rounds (h : ChainSpec lt cs bw sw B G B' G') :
    ∀ j t c, (t, c) ∈ supp (rounds B' G' j)
      ↔ t ∈ supp (rounds B G j) ∧ ∃ i, j ≤ i ∧ ∃ hi : i < cs.length, cs[i] = c
  | 0, t, c => by
    simp only [rounds, h.base_supp, zero_le, true_and, List.mem_iff_getElem]
  | j + 1, t', c' => by
    simp only [rounds]
    constructor
    · intro hm
      obtain ⟨⟨t, c⟩, hu, hv⟩ := mem_supp_lin.1 hm
      obtain ⟨ht, i, hji, hi, rfl⟩ := (h.supp_rounds j t c).1 hu
      obtain ⟨ht', hc', hlt⟩ := (h.step_supp t _ (List.getElem_mem hi) t' c').1 hv
      obtain ⟨i', hi', rfl⟩ := List.mem_iff_getElem.1 hc'
      refine ⟨mem_supp_lin.2 ⟨t, ht, ht'⟩, i', ?_, hi', rfl⟩
      have := (sorted_lt_iff h.sorted h.irrefl h.trans hi hi').1 hlt
      omega
    · rintro ⟨ht', i', hji', hi', rfl⟩
      obtain ⟨t, ht, ht'⟩ := mem_supp_lin.1 ht'
      have hj : j < cs.length := by omega
      refine mem_supp_lin.2 ⟨(t, cs[j]), (h.supp_rounds j t _).2 ⟨ht, j, le_rfl, hj, rfl⟩, ?_⟩
      exact (h.step_supp t _ (List.getElem_mem hj) t' _).2
        ⟨ht', List.getElem_mem hi', (sorted_lt_iff h.sorted h.irrefl h.trans hj hi').2 (by omega)⟩

omit [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R] in
theorem ChainSpec.supp_rounds_subset (h : ChainSpec lt cs bw sw B G B' G') {S : Finset α}
    (hS : Closed S B G) (j : ℕ) : supp (rounds B' G' j) ⊆ S ×ˢ cs.toFinset := by
  rintro ⟨t, c⟩ hm
  obtain ⟨ht, i, -, hi, rfl⟩ := (h.supp_rounds j t c).1 hm
  exact Finset.mem_product.2 ⟨hS.supp_rounds j ht, List.mem_toFinset.2 (List.getElem_mem hi)⟩

omit [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R] in
/-- **The all-chains simulation's rounds end at the number of counters.** -/
theorem ChainSpec.rounds_eq_zero (h : ChainSpec lt cs bw sw B G B' G') {j : ℕ}
    (hj : cs.length ≤ j) : rounds B' G' j = 0 := by
  have : supp (rounds B' G' j) = ∅ := by
    ext ⟨t, c⟩
    simp only [Finset.notMem_empty, iff_false]
    intro hm
    obtain ⟨-, i, hji, hi, -⟩ := (h.supp_rounds j t c).1 hm
    omega
  exact supp_eq_empty_iff.1 this

/-! #### The weights -/

/-- **A round of the simulation weighs no more than the recursion's**, in
an absorptive semiring. -/
theorem ChainSpec.wt_rounds_le (h : ChainSpec lt cs bw sw B G B' G')
    (habs : ∀ a : R, 1 + a = 1) {S : Finset α} (hS : Closed S B G) :
    ∀ j t c, wt (rounds B' G' j) (t, c) ≤ wt (rounds B G j) t
  | 0, t, c => by
    simp only [rounds]
    by_cases hc : c ∈ cs
    · rw [h.base_wt t c hc]; exact mul_le_left_of_abs habs _ _
    · rw [wt_eq_zero_of_notMem fun hm => hc ((h.base_supp t c).1 hm).2]; exact zero_le
  | j + 1, t', c' => by
    simp only [rounds]
    rw [wt_lin, sum_map_mul_eq (fun p => wt (G' p) (t', c')) _ _ (h.supp_rounds_subset hS j),
      wt_lin, sum_map_mul_eq (fun u => wt (G u) t') S _ (hS.supp_rounds j), sum_product]
    refine Finset.sum_le_sum fun t _ => sum_le_of_abs habs _ _ _ fun c hc => ?_
    have hc : c ∈ cs := List.mem_toFinset.1 hc
    by_cases hm : (t', c') ∈ supp (G' (t, c))
    · obtain ⟨-, hc', hlt⟩ := (h.step_supp t c hc t' c').1 hm
      rw [h.step_wt t c hc t' c' hc' hlt]
      exact mul_le_mul_of_le' (h.wt_rounds_le habs hS j t c) (mul_le_left_of_abs habs _ _)
    · rw [wt_eq_zero_of_notMem hm, mul_zero]; exact zero_le

omit [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R] in
theorem ChainSpec.mem_cs_of_supp (h : ChainSpec lt cs bw sw B G B' G') {j : ℕ} {t : α} {c : β}
    (hm : (t, c) ∈ supp (rounds B' G' j)) : c ∈ cs := by
  obtain ⟨-, i, -, hi, rfl⟩ := (h.supp_rounds j t c).1 hm
  exact List.getElem_mem hi

/-- **A round of the simulation weighs at least each path times each chain
of counters of the same length**, the chain listed from its end, like the
path. -/
theorem ChainSpec.wt_rounds_ge (h : ChainSpec lt cs bw sw B G B' G') {S : Finset α}
    (hS : Closed S B G) :
    ∀ j t (l : List α) (ch : List β) (c : β), l ∈ pathsTo S j t → ch.length = l.length →
      ch.Pairwise (fun a b => lt b a) → (∀ e ∈ ch, e ∈ cs) → ch.head? = some c →
      pw (wt B) (fun u v => wt (G u) v) l * pw bw sw ch ≤ wt (rounds B' G' j) (t, c)
  | 0, t, l, ch, c, hl, hlen, _, hcs, hc => by
    obtain ⟨hl₁, hl₂, -⟩ := (mem_pathsTo S 0 t l).1 hl
    match l, hl₁, hl₂, ch, hlen, hc with
    | [u], _, hl₂, [e], _, hc =>
      simp only [List.head?_cons, Option.some.injEq] at hl₂ hc
      subst hl₂; subst hc
      rw [rounds, h.base_wt u e (hcs e List.mem_cons_self)]
      exact le_refl _
  | j + 1, t, l, ch, c, hl, hlen, hsort, hcs, hc => by
    obtain ⟨l', rfl⟩ := eq_cons_of_mem_pathsTo S hl
    obtain ⟨hl₁, -, hlS⟩ := (mem_pathsTo S (j + 1) t (t :: l')).1 hl
    match l', hl₁, ch, hlen, hc, hsort with
    | u :: l₀, hl₁, e' :: e :: ch₀, hlen, hc, hsort =>
      simp only [List.head?_cons, Option.some.injEq] at hc
      subst hc
      have hl₀ : u :: l₀ ∈ pathsTo S j u := (mem_pathsTo S j u _).2
        ⟨by simp only [List.length_cons] at hl₁ ⊢; omega, rfl,
          fun a ha => hlS a (List.mem_cons_of_mem _ ha)⟩
      have hlt : lt e e' := List.rel_of_pairwise_cons hsort List.mem_cons_self
      have hecs : e ∈ cs := hcs e (List.mem_cons_of_mem _ List.mem_cons_self)
      have he'cs : e' ∈ cs := hcs e' List.mem_cons_self
      have ih := h.wt_rounds_ge hS j u (u :: l₀) (e :: ch₀) e hl₀ (by simpa using hlen)
        (List.Pairwise.of_cons hsort) (fun a ha => hcs a (List.mem_cons_of_mem _ ha)) rfl
      simp only [rounds]
      rw [wt_lin, sum_map_mul_eq (fun p => wt (G' p) (t, e')) _ _ (h.supp_rounds_subset hS j)]
      have hmem : (u, e) ∈ S ×ˢ cs.toFinset :=
        Finset.mem_product.2 ⟨hlS u (by simp), List.mem_toFinset.2 hecs⟩
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hmem)
      rw [h.step_wt u e hecs t e' he'cs hlt, pw, pw]
      calc wt (G u) t * pw (wt B) (fun u v => wt (G u) v) (u :: l₀)
            * (sw e e' * pw bw sw (e :: ch₀))
          = pw (wt B) (fun u v => wt (G u) v) (u :: l₀) * pw bw sw (e :: ch₀)
            * (wt (G u) t * sw e e') := by ring
        _ ≤ _ := mul_le_mul_of_le_right' ih _

/-- A path with its cycle cut is a path of fewer steps to the same tuple. -/
theorem mem_pathsTo_cut {S : Finset α} {j : ℕ} {v : α} {l₁ : List α} {a : α} {l₂ l₃ : List α}
    (hl : l₁ ++ a :: (l₂ ++ a :: l₃) ∈ pathsTo S j v) :
    l₁ ++ a :: l₃ ∈ pathsTo S (j - (l₂.length + 1)) v ∧ l₂.length + 1 ≤ j := by
  classical
  obtain ⟨hlen, hh, hS⟩ := (mem_pathsTo S j v _).1 hl
  simp only [List.length_append, List.length_cons] at hlen
  refine ⟨(mem_pathsTo S _ v _).2 ⟨?_, ?_, ?_⟩, by omega⟩
  · simp only [List.length_append, List.length_cons]; omega
  · cases l₁ with
    | nil => simpa using hh
    | cons w t => simpa using hh
  · intro c hc
    apply hS
    simp only [List.mem_append, List.mem_cons] at hc ⊢
    tauto

omit [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R] in
/-- **A tuple of a round is in a round of fewer steps than the set it
lives in.** -/
theorem exists_short_round {S : Finset α} (hS : Closed S B G) :
    ∀ j t, t ∈ supp (rounds B G j) → ∃ j' < S.card, j' ≤ j ∧ t ∈ supp (rounds B G j') := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro t ht
    by_cases hj : j < S.card
    · exact ⟨j, hj, le_rfl, ht⟩
    · have hN := (mem_supp_rounds_iff hS j t).1 ht
      obtain ⟨j₁, hj₁, hj₁'⟩ := exists_lt_ne_zero S _ _
        (fun u hu => by
          simp only [ite_eq_right_iff, one_ne_zero, imp_false]
          exact fun h' => hu (hS.base h'))
        (fun u hu v hv => by
          simp only [ite_eq_right_iff, one_ne_zero, imp_false]
          exact fun h' => hv (hS.step u hu h')) (Nat.le_of_not_lt hj) hN
      obtain ⟨j', hj', hle, ht'⟩ := ih j₁ hj₁ t ((mem_supp_rounds_iff hS j₁ t).2 hj₁')
      exact ⟨j', hj', by omega, ht'⟩

omit [PartialOrder R] [CanonicallyOrderedAdd R] [IsOrderedAddMonoid R] in
/-- **The rounds past `|S|` add nothing**, in an absorptive semiring. -/
theorem x_stable (habs : ∀ a : R, 1 + a = 1) {S : Finset α} (hS : Closed S B G) {N : ℕ}
    (hN : S.card ≤ N) (v : α) :
    ∀ k, x S (wt B) (fun u v => wt (G u) v) (N + k) v = x S (wt B) (fun u v => wt (G u) v) N v
  | 0 => rfl
  | k + 1 => by
    have hbS : ∀ u, u ∉ S → wt B u = 0 := fun u hu =>
      wt_eq_zero_of_notMem fun h' => hu (hS.base h')
    have hgS : ∀ u ∈ S, ∀ v, v ∉ S → wt (G u) v = 0 := fun u hu v hv =>
      wt_eq_zero_of_notMem fun h' => hv (hS.step u hu h')
    rw [← Nat.add_assoc, x, sum_range_succ, ← x,
      x_add_y_of_absorptive S _ _ habs hbS hgS (by omega) v, x_stable habs hS hN v k]

/-- **The all-chains simulation computes the set recursion**, in an
absorptive semiring: `ε` of the sum of any number `L ≥ |cs|` of its rounds,
with the counters forgotten, is `ε` of the sum of the first `N ≥ |S|`
rounds of the recursion, when there are at least `|S|` counters and the
weight of every path through distinct tuples is `𝟘` or absorbed by that of
a chain of as many counters. -/
theorem ChainSpec.dedupK_rounds (h : ChainSpec lt cs bw sw B G B' G')
    (habs : ∀ a : R, 1 + a = 1) {S : Finset α} (hS : Closed S B G) {N L : ℕ}
    (hN : S.card ≤ N) (hcs : S.card ≤ cs.length) (hL : cs.length ≤ L)
    (hgen : ∀ j t l, l ∈ pathsTo S j t → l.Nodup →
      pw (wt B) (fun u v => wt (G u) v) l = 0 ∨ ∃ ch : List β, ch.length = l.length
        ∧ ch.Pairwise (fun a b => lt b a) ∧ (∀ e ∈ ch, e ∈ cs)
        ∧ pw (wt B) (fun u v => wt (G u) v) l * pw bw sw ch
          = pw (wt B) (fun u v => wt (G u) v) l) :
    dedupK ((∑ j ∈ range L, rounds B' G' j).map dropCtr) = dedupK (trunc B G N) := by
  have hcnd : cs.Nodup := nodup_of_sorted h.sorted h.irrefl
  have hmemL : ∀ k, ∀ p ∈ ∑ j ∈ range k, rounds B' G' j, p.1.2 ∈ cs.toFinset := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro p hp
      rw [sum_range_succ, Multiset.mem_add] at hp
      rcases hp with hp | hp
      · exact ih p hp
      · exact (Finset.mem_product.1 (h.supp_rounds_subset hS k
          (mem_supp.2 ⟨p, hp, rfl⟩))).2
  have hsumW : ∀ (k : ℕ) (u : α × β), wt (∑ j ∈ range k, rounds B' G' j) u
      = ∑ j ∈ range k, wt (rounds B' G' j) u := fun k u => wt_trunc B' G' k u
  refine dedupK_congr ?_ fun t => ?_
  · ext t
    rw [mem_supp_map_dropCtr, mem_supp_trunc]
    have hsum : ∀ (k : ℕ) (c : β), (t, c) ∈ supp (∑ j ∈ range k, rounds B' G' j)
        ↔ ∃ j < k, (t, c) ∈ supp (rounds B' G' j) := fun k c =>
      mem_supp_trunc (B := B') (G := G')
    simp only [hsum, h.supp_rounds]
    constructor
    · rintro ⟨c, j, hj, ht, i, hji, hi, -⟩
      obtain ⟨j', hj', -, ht'⟩ := exists_short_round hS j t ht
      exact ⟨j', by omega, ht'⟩
    · rintro ⟨j, hj, ht⟩
      obtain ⟨j', hj', -, ht'⟩ := exists_short_round hS j t ht
      exact ⟨cs[j'], j', by omega, ht', j', le_rfl, by omega, rfl⟩
  · set g := fun u v => wt (G u) v with hg
    rw [wt_map_dropCtr cs.toFinset _ (hmemL L), wt_trunc]
    simp only [hsumW]
    have hx : ∑ j ∈ range N, wt (rounds B G j) t = x S (wt B) g N t :=
      sum_congr rfl fun j _ => wt_rounds hS j t
    rw [hx]
    set X := ∑ c ∈ cs.toFinset, ∑ j ∈ range L, wt (rounds B' G' j) (t, c) with hX
    -- every round of the recursion is below its first `N` rounds
    have hyN : ∀ j, y S (wt B) g j t ≤ x S (wt B) g N t := by
      intro j
      by_cases hj : j < N
      · exact Finset.single_le_sum (f := fun j => y S (wt B) g j t) (fun _ _ => zero_le)
          (mem_range.2 hj)
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hj)
        rw [← x_stable habs hS hN t (k + 1), ← Nat.add_assoc, x, sum_range_succ]
        exact le_add_self
    -- every path is below the simulation's sum
    have hpw : ∀ m j l, l.length ≤ m → l ∈ pathsTo S j t → pw (wt B) g l ≤ X := by
      intro m
      induction m with
      | zero =>
        intro j l hl hm
        have := ((mem_pathsTo S j t l).1 hm).1
        omega
      | succ m ih =>
        intro j l hl hm
        by_cases hnd : l.Nodup
        · rcases hgen j t l hm hnd with h0 | ⟨ch, hlen, hsort, hcs', habs'⟩
          · rw [h0]; exact zero_le
          · obtain ⟨c, ch', rfl⟩ : ∃ c ch', ch = c :: ch' := by
              obtain ⟨hl₁, -, -⟩ := (mem_pathsTo S j t l).1 hm
              match ch, hlen with
              | [], hlen => simp at hlen; omega
              | c :: ch', _ => exact ⟨c, ch', rfl⟩
            have hlenj : (c :: ch').length = j + 1 := by
              rw [hlen]; exact ((mem_pathsTo S j t l).1 hm).1
            have hjL : j < L := by
              have hnd' : (c :: ch').Nodup := hsort.imp fun {a b} hab he => by
                subst he; exact h.irrefl a hab
              have := List.toFinset_card_of_nodup hnd'
              have hsub : (c :: ch').toFinset ⊆ cs.toFinset := fun a ha =>
                List.mem_toFinset.2 (hcs' a (List.mem_toFinset.1 ha))
              have := Finset.card_le_card hsub
              rw [List.toFinset_card_of_nodup hcnd] at this
              omega
            have hcc : c ∈ cs.toFinset := List.mem_toFinset.2 (hcs' c List.mem_cons_self)
            rw [← habs']
            refine le_trans (h.wt_rounds_ge hS j t l (c :: ch') c hm hlen hsort hcs' rfl) ?_
            refine le_trans (Finset.single_le_sum (f := fun j => wt (rounds B' G' j) (t, c))
              (fun _ _ => zero_le) (mem_range.2 hjL)) ?_
            exact Finset.single_le_sum (f := fun c => ∑ j ∈ range L, wt (rounds B' G' j) (t, c))
              (fun _ _ => zero_le) hcc
        · obtain ⟨l₁, a, l₂, l₃, rfl⟩ := exists_repeat l hnd
          obtain ⟨hc, -⟩ := mem_pathsTo_cut hm
          rw [pw_cut]
          refine le_trans (mul_le_left_of_abs habs _ _) (ih _ _ ?_ hc)
          simp only [List.length_append, List.length_cons] at hl ⊢
          omega
    refine le_antisymm ?_ ?_
    · refine sum_le_of_abs habs _ _ _ fun c _ => sum_le_of_abs habs _ _ _ fun j _ => ?_
      exact le_trans (h.wt_rounds_le habs hS j t c) (by rw [wt_rounds hS]; exact hyN j)
    · refine sum_le_of_abs habs _ _ _ fun j _ => ?_
      have hbS : ∀ u, u ∉ S → wt B u = 0 := fun u hu =>
        wt_eq_zero_of_notMem fun h' => hu (hS.base h')
      have hgS : ∀ u ∈ S, ∀ v, v ∉ S → wt (G u) v = 0 := fun u hu v hv =>
        wt_eq_zero_of_notMem fun h' => hv (hS.step u hu h')
      rw [y_eq_sum_pathsTo S _ _ hbS hgS]
      exact sum_le_of_abs habs _ _ _ fun l hl => hpw _ j l le_rfl hl

end Chains

section WeightAlgebra

/-! ### Weights of the usual constructions -/

variable [CommSemiring R] {β : Type} [DecidableEq β]

theorem wt_map_pair (x : α) (y : R) (B : Multiset (β × R)) (a : α) (b : β) :
    wt (B.map (fun q => ((x, q.1), y * q.2))) (a, b) = if x = a then y * wt B b else 0 := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons q B ih =>
    rw [Multiset.map_cons, wt_cons, ih, wt_cons]
    by_cases hx : x = a
    · subst hx
      by_cases hq : q.1 = b
      · simp [hq, mul_add]
      · simp [hq]
    · simp [hx]

/-- **The weight of a pair in a product** is the product of the weights. -/
theorem wt_product (A : Multiset (α × R)) (B : Multiset (β × R)) (a : α) (b : β) :
    wt ((A.product B).map (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2))) (a, b)
      = wt A a * wt B b := by
  induction A using Multiset.induction_on with
  | empty => simp [Multiset.product]
  | cons p A ih =>
    rw [show (p ::ₘ A).product B = B.map (Prod.mk p) + A.product B from Multiset.cons_product _ _ _,
      Multiset.map_add, wt_add, ih, Multiset.map_map, wt_cons, add_mul]
    congr 1
    rw [show ((fun q : (α × R) × (β × R) => ((q.1.1, q.2.1), q.1.2 * q.2.2)) ∘ Prod.mk p)
        = fun q => ((p.1, q.1), p.2 * q.2) from rfl, wt_map_pair]
    split_ifs <;> simp

theorem mem_supp_product (A : Multiset (α × R)) (B : Multiset (β × R)) (a : α) (b : β) :
    (a, b) ∈ supp ((A.product B).map (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2)))
      ↔ a ∈ supp A ∧ b ∈ supp B := by
  rw [mem_supp, mem_supp, mem_supp]
  constructor
  · rintro ⟨_, hx, hxe⟩
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨hp, hq⟩ := Multiset.mem_product.1 hpq
    simp only [Prod.mk.injEq] at hxe
    exact ⟨⟨p, hp, hxe.1⟩, ⟨q, hq, hxe.2⟩⟩
  · rintro ⟨⟨p, hp, h₁⟩, ⟨q, hq, h₂⟩⟩
    exact ⟨_, Multiset.mem_map.2 ⟨(p, q), Multiset.mem_product.2 ⟨hp, hq⟩, rfl⟩,
      by simp [h₁, h₂]⟩

/-- A filter on the tuple keeps a weight or zeroes it. -/
theorem wt_filter (X : Multiset (α × R)) (P : α → Prop) [DecidablePred P] (a : α) :
    wt (X.filter (fun p => P p.1)) a = if P a then wt X a else 0 := by
  unfold wt
  rw [Multiset.filter_filter]
  split_ifs with h
  · congr 2
    exact Multiset.filter_congr fun p _ => by constructor <;> intro h' <;> simp_all
  · rw [Multiset.filter_eq_nil.2 fun p _ (h' : p.1 = a ∧ P p.1) => h (h'.1 ▸ h'.2)]
    simp

/-- **A relation with one row per tuple** has the row's annotation as the
tuple's weight. -/
theorem wt_map_nodup {U : Multiset α} (hU : U.Nodup) (f : α → R) (a : α) :
    wt (U.map (fun u => (u, f u))) a = if a ∈ U then f a else 0 := by
  unfold wt
  rw [Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp]
  rw [show U.filter (fun u => u = a) = if a ∈ U then {a} else 0 from by
    rw [Multiset.filter_eq' U a, Multiset.count_eq_of_nodup hU]
    split_ifs <;> simp]
  split_ifs <;> simp

omit [DecidableEq β] in
/-- **Rows annotated `𝟙` mapped onto a tuple** weigh the number of rows
mapped there. -/
theorem wt_map_one (U : Multiset β) (g : β → α) (a : α) :
    wt (U.map (fun u => (g u, (1 : R)))) a = ((U.filter (fun u => g u = a)).card : R) := by
  unfold wt
  rw [Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]

omit [CommSemiring R] [DecidableEq β] in
theorem supp_map (U : Multiset β) (g : β → α) (f : β → R) :
    supp (U.map (fun u => (g u, f u))) = (U.map g).toFinset := by
  ext a; simp [supp, Multiset.map_map]

end WeightAlgebra


end PathSum
