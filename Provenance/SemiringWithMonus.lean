/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/-!
# Semirings with monus

This file defines semirings with monus and introduces their main
properties.

Many semirings relevant for provenance can be equipped with a monus -
operator, resulting in what is called a semiring with monus, or
m-semiring. This is standard in semiring theory [amer1984equationally] and was
introduced in the setting of provenance semirings by Geerts and Poggi
[geerts2010database]. The class is the algebraic structure underlying the
annotated query semantics of Section IV-A of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql] (Definition 5).

## References

* [Amer, *Equationally complete classes of commutative monoids with
monus*][amer1984equationally]
* [Geerts & Poggi, *On database query languages for
K-relations*][geerts2010database]
* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Definition 5)

-/

section SemiringWithMonus

/-! ## Definition of a `SemiringWithMonus` -/

/-- A `SemiringWithMonus` is a naturally ordered semiring
with a monus operation that is compatible with the natural order.
We do not require the semiring to be necessarily commutative.

In addition to monus, the class carries a `δ : α → α` operator subject
to three axioms (`delta_zero`, `delta_natCast_pos`, and
`delta_absorb`). This is the duplicate-eliminating support
operator used to interpret aggregation in the framework of
[Amsterdamer, Deutch & Tannen, *Provenance for aggregate queries*][amsterdamer2011aggregate],
mirroring ProvSQL's `Semiring::delta`. -/
class SemiringWithMonus (α : Type)
  extends Semiring α, PartialOrder α, IsOrderedAddMonoid α, CanonicallyOrderedAdd α, Sub α where
  monus_spec : ∀ a b c : α, a - b ≤ c ↔ a ≤ b + c
  /-- Duplicate-eliminating support operator. Sends `0` to `0` and any
  positive integer iterate of `1` to `1`. -/
  delta : α → α
  /-- `δ` sends `0` to `0`. -/
  delta_zero : delta 0 = 0
  /-- `δ` sends every positive integer iterate of `1` (i.e., every
  positive natural-number cast) to `1`. -/
  delta_natCast_pos : ∀ {n : ℕ}, 0 < n → delta ((n : α)) = 1
  /-- A δ-guard is absorbed by any multiple of one of its summands:
  `a ⊗ δ(a ⊕ b) = a`. This is what makes a group-existence factor
  redundant next to any provenance that already contains an occurrence
  of the group: `δ` really acts as “the group exists” and nothing more.
  Both usual choices of `δ` satisfy it in their natural habitat: the
  indicator (`δ x = 𝟙` for `x ≠ 𝟘`) in any canonically ordered semiring
  (`delta_absorb_indicator`), and the identity in lattice-like
  semirings, where it is absorption `a ⊓ (a ⊔ b) = a`. -/
  delta_absorb : ∀ (a b : α), a * delta (a + b) = a

/-! ## Main properties -/

/-- In a `SemiringWithMonus`, `a - b` is the smallest element `c`
satisfying `a ≤ b + c`. -/
theorem monus_smallest [K : SemiringWithMonus α] :
  ∀ a b : α, a ≤ b + (a - b) ∧ ∀ c: α, a ≤ b + c → a - b ≤ c := by {
    intro a b
    constructor
    . rw [← SemiringWithMonus.monus_spec]
    . intro c h
      rw [SemiringWithMonus.monus_spec]
      exact h
  }

/-- **Uniqueness of monus.** The monus operation is determined by its
adjunction property: any binary operation `s` satisfying
`s a b ≤ c ↔ a ≤ b + c` coincides with `⊖`. Consequently, a naturally
ordered semiring admits at most one monus operation. -/
theorem monus_unique [K : SemiringWithMonus α] (s : α → α → α)
    (hs : ∀ a b c : α, s a b ≤ c ↔ a ≤ b + c) :
    ∀ a b : α, s a b = a - b := by
  intro a b
  apply le_antisymm
  · rw [hs]
    exact (monus_smallest a b).1
  · rw [SemiringWithMonus.monus_spec]
    exact (hs a b (s a b)).mp le_rfl

/-- In a `SemiringWithMonus`, `δ 1 = 1`. -/
theorem delta_one [K : SemiringWithMonus α] : K.delta 1 = 1 := by
  have h := K.delta_natCast_pos (n := 1) Nat.zero_lt_one
  simpa using h

/-- In a `SemiringWithMonus`, `a - a = 0`. -/
theorem monus_self [K : SemiringWithMonus α] :
  ∀ a : α, a - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

/-- In a `SemiringWithMonus`, `0 - a = 0`. -/
theorem zero_monus [K : SemiringWithMonus α] :
  ∀ a : α, 0 - a = 0 := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]
      simp
    . simp
  }

/-- In a `SemiringWithMonus`, `a - 0 = a`. -/
theorem monus_zero [K : SemiringWithMonus α] :
  ∀ a : α, a - 0 = a := by {
    intro a
    apply le_antisymm
    . rw [SemiringWithMonus.monus_spec]; simp
    . have h := (monus_smallest a 0).1
      simpa using h
  }

/-- In a `SemiringWithMonus`, `a + (b -a) = b + (a - b)`. -/
theorem add_monus [K : SemiringWithMonus α] :
  ∀ a b : α, a + (b - a) = b + (a - b) := by
    intro a b

    have h : ∀ a b c : α, (a ≤ c ∧ b ≤ c) → a+(b-a) ≤ c := by
      intro a b c hc
      rcases hc with ⟨ha, hb⟩
      rcases (exists_add_of_le ha) with ⟨d, ha'⟩
      rw [ha'] at hb
      rw [← SemiringWithMonus.monus_spec] at hb
      apply add_le_add_left at hb
      specialize hb a
      rw[add_comm]
      simp [ha']
      nth_rewrite 2 [add_comm]
      assumption

    apply le_antisymm

    . apply h a b (b+(a-b))
      constructor
      . simp [← SemiringWithMonus.monus_spec]
      . simp

    . apply h b a (a+(b-a))
      constructor
      . simp [← SemiringWithMonus.monus_spec]
      . simp

/-- In a `SemiringWithMonus`, monus is left-distributive over plus. -/
theorem monus_add [K: SemiringWithMonus α] :
  ∀ a b c : α, a - (b + c) = a - b - c := by {
    intro a b c

    have h1 : ∀ x : α, (a ≤ b+c+x) → a - (b+c) ≤ x := by {
      intro x
      apply ((monus_smallest a (b+c)).right x)
    }

    have h2 : ∀ x : α, (a ≤ b+c+x) → a - b - c ≤ x := by {
      intro x hx
      rw [SemiringWithMonus.monus_spec]
      rw [SemiringWithMonus.monus_spec]
      rw [← add_assoc]
      exact hx
    }

    apply le_antisymm
    . apply h1
      calc
        a ≤ b + (a-b)       := by rw [← SemiringWithMonus.monus_spec a b (a-b)]
        _ ≤ b + c + (a-b-c) := by {
          rw [add_assoc]
          apply add_le_add_right
          rw [← SemiringWithMonus.monus_spec (a-b) c (a-b-c)]
        }

    . apply h2
      rw [← SemiringWithMonus.monus_spec]
  }

/-! ## Additional properties

The following properties do not always hold in an arbitrary m-semiring.
-/

/-- A `Semiring` is idempotent if `a + a = a`. -/
abbrev idempotent (α) [Semiring α] := ∀ a : α, a + a = a

/-- A `Semiring` is absorptive (also called 0-closed or 0-bounded) if `1 + a = a`. -/
abbrev absorptive (α) [Semiring α] := ∀ a : α, 1 + a = 1

/-- We define left-distributivity of times over monus in a `SemiringWithMonus`. -/
abbrev mul_sub_left_distributive (α) [SemiringWithMonus α] := ∀ a b c : α, a * (b - c) = a*b - a*c

/-- Absorptivity implies idempotence -/
theorem idempotent_of_absorptive [K: Semiring α] :
  absorptive α → idempotent α := by
    intro habs a
    nth_rewrite 1 2 [← mul_one a]
    rw[← mul_add]
    simp[habs 1]

/-- In an idempotent `SemiringWithMonus`, `a ≤ b` iff `a + b = b`. -/
theorem le_iff_add_eq [K: SemiringWithMonus α] (h: idempotent α) :
  ∀ a b: α, a ≤ b ↔ a+b = b := by
    intro a b
    apply Iff.intro
    . intro hab
      have := le_iff_exists_add.mp hab
      rcases this with ⟨c,hc⟩
      nth_rewrite 1 [hc]
      rw[← add_assoc]
      rw[h a]
      tauto
    . intro hab
      rw[← hab]
      exact le_self_add

/-- In an idempotent `SemiringWithMonus`, plus is the join of the
  semilattice -/
theorem plus_is_join [K: SemiringWithMonus α] (h: idempotent α) :
  ∀ a b: α, ((a ≤ a+b) ∧ (b ≤ a+b)) ∧ (∀ u: α, (a ≤ u) ∧ (b ≤ u) → a+b ≤ u) := by
    intro a b
    constructor
    . constructor
      . exact le_self_add
      . rw[add_comm]
        exact le_self_add
    . intro u hu
      have ha := (le_iff_add_eq h _ _).mp hu.1
      have hb := (le_iff_add_eq h _ _).mp hu.2
      apply (le_iff_add_eq h _ _).mpr
      rw[add_assoc]
      rw[hb]
      exact ha

/-- In a `SemiringWithMonus`, right-distributivity of monus
  over plus implies idempotence. -/
theorem idempotent_of_add_monus
  [K: SemiringWithMonus α]
  (h: ∀ a b c : α, (a + b) - c = (a - c) + (b - c)) : idempotent α := by
      intro a
      have ha := h a a a
      simp[monus_self] at ha
      have h₁ : a + a ≤ a := by
        have := (K.monus_spec _ _ _).mp (le_of_eq ha)
        simp at this
        assumption
      have h₂ : a ≤ a + a := by
        exact le_self_add
      exact eq_of_le_of_ge h₁ h₂

/-- In a `SemiringWithMonus`, idempotence implies right-distributivity of monus
  over plus. -/
theorem add_monus_of_idempotent [K: SemiringWithMonus α] (h: idempotent α) :
  ∀ a b c : α, (a + b) - c = (a - c) + (b - c) := by
    intro a b c
    have h₁ : (a + b) - c ≤ (a - c) + (b - c) := by
      apply (K.monus_spec _ _ _).mpr
      have ha : a ≤ c + (a - c) := (monus_smallest _ _).1
      have hb : b ≤ c + (b - c) := (monus_smallest _ _).1
      have := add_le_add ha hb
      apply le_trans this
      simp[← add_assoc]
      rw[add_assoc c _ c]
      rw[add_comm (a-c) c]
      simp[← add_assoc]
      rw[h c]

    have h₂ : (a - c) + (b - c) ≤ (a + b) - c := by
      suffices h₂' : (a-c) ≤ (a + b) - c ∧ (b-c) ≤ (a + b) - c from
        (plus_is_join h (a-c) (b-c)).2 _ h₂'
      constructor
      . have hab := @le_self_add _ _ _ _ a b
        have habc := le_trans hab (monus_smallest (a+b) c).1
        exact (K.monus_spec _ _ _).mpr habc
      . have hab := @le_self_add _ _ _ _ b a
        rw[add_comm] at hab
        have habc := le_trans hab (monus_smallest (a+b) c).1
        exact (K.monus_spec _ _ _).mpr habc

    exact eq_of_le_of_ge h₁ h₂

/-- A `SemiringWithMonus` is idempotent iff monus is right-distributive
  over plus. -/
theorem idempotent_iff_add_monus [SemiringWithMonus α] :
  idempotent α ↔ ∀ a b c : α, (a + b) - c = (a - c) + (b - c)
    := ⟨add_monus_of_idempotent, idempotent_of_add_monus⟩

/-- Finite-family version of `add_monus_of_idempotent`: in an idempotent
  `SemiringWithMonus`, monus distributes over the sum of any multiset of
  annotations, `(⨁ᵢ aᵢ) ⊖ c = ⨁ᵢ (aᵢ ⊖ c)`. -/
theorem add_monus_of_idempotent_multiset [SemiringWithMonus α] (h: idempotent α) :
  ∀ (s : Multiset α) (c : α), s.sum - c = (s.map (· - c)).sum := by
    intro s c
    induction s using Multiset.induction_on with
    | empty => simp [zero_monus]
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons,
          add_monus_of_idempotent h, ih]

theorem monus_le [SemiringWithMonus α] :
  ∀ a b : α, a - b ≤ a := by
    simp[SemiringWithMonus.monus_spec]

theorem le_plus_monus [SemiringWithMonus α] :
  ∀ a b : α, a ≤ b + (a - b) := by
    simp[← SemiringWithMonus.monus_spec]

/-- Monus is antitone in its second argument: subtracting more leaves less.
Together with `monus_le` this is what lets a subtrahend be replaced by a
larger one inside an upper bound. -/
theorem monus_antitone [SemiringWithMonus α] {b b' : α} (h : b ≤ b') (a : α) :
    a - b' ≤ a - b := by
  rw [SemiringWithMonus.monus_spec]
  exact le_trans (le_plus_monus a b) (add_le_add h le_rfl)

/-! ## Characteristic of idempotent semirings

In an idempotent semiring (`a + a = a`), every positive natural-number cast
collapses to `1`. With `1 ≠ 0` this yields `CharP K 0`. Note that this is
strictly weaker than `CharZero K`, which fails for idempotent semirings since
the cast `ℕ → K` is not injective. -/

/-- In a semiring with idempotent addition, the cast of any positive natural
number equals `1`. -/
theorem natCast_pos_eq_one_of_idempotent {K : Type} [Semiring K] (h : idempotent K) :
  ∀ {n : ℕ}, 0 < n → (n : K) = 1 := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      match Nat.eq_zero_or_pos m with
      | .inl hm => subst hm; simp
      | .inr hm => rw [Nat.cast_succ, ih hm, h 1]

/-- A nontrivial idempotent semiring has characteristic 0 in the `CharP` sense.
Unlike `CharZero`, this does not require the natural-number cast to be injective:
in an idempotent semiring every positive natural maps to `1`, but `1 ≠ 0` still
suffices to give `CharP K 0`. -/
theorem CharP.zero_of_idempotent {K : Type} [Semiring K] [Nontrivial K]
  (h : idempotent K) : CharP K 0 := by
    refine ⟨fun x => ?_⟩
    rw [zero_dvd_iff]
    refine ⟨fun hx => ?_, fun hx => by rw [hx]; exact Nat.cast_zero⟩
    by_contra hne
    rw [natCast_pos_eq_one_of_idempotent h (Nat.pos_of_ne_zero hne)] at hx
    exact one_ne_zero hx

/-! ## Generic constructions of `δ`

In the m-semirings used for provenance the `δ` operator is invariably
realized in one of two ways: as the identity (when the semiring is
idempotent, so every positive natural cast already equals `1`) or as the
indicator-of-nonzero (`a ↦ if a = 0 then 0 else 1`). The lemmas below
package the proofs of the `δ` axioms for both candidates so each
concrete instance can plug them in directly. -/

/-- `δ := id` satisfies `delta_natCast_pos` in any idempotent semiring:
every positive natural-number cast collapses to `1`. -/
theorem delta_natCast_pos_id {K : Type} [Semiring K] (h : idempotent K)
    {n : ℕ} (hn : 0 < n) : (id ((n : K)) : K) = 1 :=
  natCast_pos_eq_one_of_idempotent h hn

/-- The “indicator-of-nonzero” recipe: `δ a = 0` when `a = 0` and
`δ a = 1` otherwise. Captured abstractly so a single set of axioms can
serve all the concrete instances that use it (`ℕ`, `ℕ[X]`, Tropical,
Viterbi, Lukasiewicz). -/
structure IsDeltaIndicator {K : Type} [Zero K] [One K] (δ : K → K) : Prop where
  zero : δ 0 = 0
  nonzero : ∀ a, a ≠ 0 → δ a = 1

/-- Any `δ` matching the indicator recipe satisfies `delta_natCast_pos`
in a nontrivial semiring of characteristic 0 (in the `CharP` sense):
positive natural-number casts are nonzero, so `δ` sends them to `1`. -/
theorem delta_natCast_pos_indicator {K : Type} [Semiring K] [Nontrivial K] [CharP K 0]
    {δ : K → K} (h : IsDeltaIndicator δ) {n : ℕ} (hn : 0 < n) : δ ((n : K)) = 1 := by
  refine h.nonzero _ ?_
  intro hzero
  rw [CharP.cast_eq_zero_iff K 0 n, zero_dvd_iff] at hzero
  omega

/-- Any `δ` matching the indicator recipe satisfies `delta_absorb` in a
canonically ordered semiring: if `a ⊕ b = 𝟘` then `a = 𝟘` by zero-sum
freeness, and otherwise `δ(a ⊕ b) = 𝟙`. -/
theorem delta_absorb_indicator
    {K : Type} [Semiring K] [PartialOrder K] [IsOrderedAddMonoid K]
    [CanonicallyOrderedAdd K]
    {δ : K → K} (h : IsDeltaIndicator δ) (a b : K) :
    a * δ (a + b) = a := by
  by_cases hab : a + b = 0
  · have ha : a = 0 := le_antisymm (hab ▸ le_self_add) zero_le
    rw [ha, zero_mul]
  · rw [h.nonzero _ hab, mul_one]

/-! ## Admissibility of a candidate `δ`

`δ` is not determined by the axioms, and the two operators used in practice
are the identity and the support indicator. `IsDelta` states the axioms as a
predicate on a *candidate* operator, so that a semiring can record which of
the two it must use: the identity is preferred where it is admissible, and
the indicator is forced exactly where `¬ IsDelta id` holds. The three
`not_isDelta_id_of_*` lemmas below cover the three ways the identity fails,
in increasing order of subtlety. -/

/-- A candidate operator `δ : K → K` satisfies the δ-axioms of
`SemiringWithMonus`. -/
structure IsDelta {K : Type} [Semiring K] (δ : K → K) : Prop where
  /-- `δ` sends `𝟘` to `𝟘`. -/
  zero : δ 0 = 0
  /-- `δ` sends every positive natural-number cast to `𝟙`. -/
  natCast_pos : ∀ {n : ℕ}, 0 < n → δ ((n : K)) = 1
  /-- A δ-guard is absorbed by any multiple of one of its summands. -/
  absorb : ∀ a b : K, a * δ (a + b) = a

/-- The `δ` carried by a `SemiringWithMonus` is admissible, by definition of
the class. In particular, in a semiring whose instance takes `δ := id` this
gives `IsDelta id` for free. -/
theorem isDelta_delta [K : SemiringWithMonus α] : IsDelta K.delta :=
  ⟨K.delta_zero, K.delta_natCast_pos, K.delta_absorb⟩

/-- To refute `δ := id`, exhibit a pair violating the lattice absorption law
`a ⊗ (a ⊕ b) = a`, which is what `delta_absorb` demands of the identity. -/
theorem not_isDelta_id_of_absorb_ne {K : Type} [Semiring K] {a b : K}
    (h : a * (a + b) ≠ a) : ¬ IsDelta (id : K → K) :=
  fun hd => h (by simpa using hd.absorb a b)

/-- `δ := id` requires the semiring to be idempotent: `delta_natCast_pos` at
`n = 2` reads `𝟙 ⊕ 𝟙 = 𝟙`, whence `a ⊕ a = a ⊗ (𝟙 ⊕ 𝟙) = a`. This is the
crudest of the three obstructions, and the one that rules the identity out
of the counting semirings (`ℕ`, `ℕ[X]`). -/
theorem not_isDelta_id_of_not_idempotent {K : Type} [Semiring K]
    (h : ¬ idempotent K) : ¬ IsDelta (id : K → K) := by
  intro hd
  have h2 : (1 : K) + 1 = 1 := by
    have hcast := hd.natCast_pos (n := 2) (by omega)
    simp only [id_eq] at hcast
    push_cast at hcast
    rwa [one_add_one_eq_two]
  refine h (fun a => ?_)
  calc a + a = a * 1 + a * 1 := by rw [mul_one]
    _ = a * (1 + 1) := (mul_add a 1 1).symm
    _ = a * 1 := by rw [h2]
    _ = a := mul_one a

/-- `δ := id` requires multiplicative idempotence as soon as addition is
idempotent: `delta_absorb` at `b = a` reads `a ⊗ (a ⊕ a) = a ⊗ a = a`. This is
the obstruction in the absorptive semirings whose `⊗` is a genuine product
(Viterbi, Łukasiewicz), where the two coarser tests below say nothing. -/
theorem not_isDelta_id_of_not_mul_idempotent {K : Type} [Semiring K]
    (hadd : idempotent K) (h : ¬ ∀ a : K, a * a = a) : ¬ IsDelta (id : K → K) :=
  fun hd => h (fun a => by simpa [hadd a] using hd.absorb a a)

/-- `δ := id` requires absorptivity: `delta_absorb` at `a = 𝟙` reads
`𝟙 ⊗ (𝟙 ⊕ b) = 𝟙`, i.e., `𝟙 ⊕ b = 𝟙`. -/
theorem not_isDelta_id_of_not_absorptive {K : Type} [Semiring K]
    (h : ¬ absorptive K) : ¬ IsDelta (id : K → K) := by
  intro hd
  exact h (fun a => by simpa using hd.absorb 1 a)

/-! ## Existence of a `δ`-like operator

This is the abstract counterpart of the `SemiringWithMonus` δ-axioms: we
characterize, in an arbitrary nontrivial semiring (no order assumed), when
a function `δ : K → K` satisfying `δ 0 = 0` and `δ ((n : K)) = 1` for
`0 < n` can exist. The class also demands `delta_absorb`, which the iff
below ignores, so it should be read as a statement about how much of the
ProvSQL δ interface is consistent with a given characteristic, not as a
full existence proof for the class. (Constructing a witness for
`delta_absorb` requires more structure: in a canonically ordered semiring
the indicator works, see `delta_absorb_indicator`.) -/

/-- In any nontrivial semiring, a function `δ : K → K` satisfying `δ 0 = 0`
and `δ ((n : K)) = 1` for every positive natural cast `n` exists if and only
if `K` has characteristic `0` in the `CharP` sense. The forward direction
follows because `δ 0 = 0` and `δ ((n : K)) = 1` are inconsistent when
`(n : K) = 0` for some `0 < n` (it would force `0 = 1`). The backward
direction defines `δ` as the indicator of being nonzero.

Note that the `δ` operator is not uniquely determined by these axioms: they
only pin its values on the image of `ℕ`. Two typical choices are δ as the
indicator of being nonzero (`δ x = if x = 0 then 0 else 1`, used in the
backward direction below) and, in an idempotent semiring, δ as the identity
(since every positive natural cast then equals `1`, see
`natCast_pos_eq_one_of_idempotent`). Both are idempotent (`δ (δ a) = δ a`);
adding idempotence as a third requirement would leave the statement
unchanged, since the forward direction never uses it and the indicator
witness satisfies it. -/
theorem delta_exists_iff_charP_zero {K : Type} [Semiring K] [Nontrivial K] :
  (∃ δ : K → K,
    δ 0 = 0 ∧
    (∀ {n : ℕ}, 0 < n → δ ((n : K)) = 1)) ↔ CharP K 0 := by
    constructor
    . rintro ⟨δ, h0, hpos⟩
      refine ⟨fun n => ?_⟩
      rw [zero_dvd_iff]
      refine ⟨fun hn => ?_, fun hn => by rw [hn]; exact Nat.cast_zero⟩
      by_contra hne
      have h1 := hpos (Nat.pos_of_ne_zero hne)
      rw [hn, h0] at h1
      exact one_ne_zero h1.symm
    . intro hchar
      classical
      have : CharP K 0 := hchar
      refine ⟨fun x => if x = 0 then 0 else 1, by simp, ?_⟩
      intro n hn
      have hne : (n : K) ≠ 0 := by
        intro h
        rw [CharP.cast_eq_zero_iff K 0 n, zero_dvd_iff] at h
        omega
      simp [hne]

/-- **The third axiom is free.** In a canonically ordered semiring, a full
`IsDelta` operator exists as soon as *some* function satisfies the first two
axioms: the indicator witnessing `delta_exists_iff_charP_zero` satisfies
`delta_absorb` as well (`delta_absorb_indicator`). So the admissibility
question for a candidate δ is never one of existence – it is only about
whether the *preferred* candidate, the identity, is among the admissible
ones (`not_isDelta_id_of_*`). -/
theorem isDelta_exists_of_natCast_axioms
    {K : Type} [Semiring K] [PartialOrder K] [IsOrderedAddMonoid K]
    [CanonicallyOrderedAdd K] [Nontrivial K] {δ : K → K}
    (h0 : δ 0 = 0) (hpos : ∀ {n : ℕ}, 0 < n → δ ((n : K)) = 1) :
    ∃ δ' : K → K, IsDelta δ' := by
  classical
  have : CharP K 0 := delta_exists_iff_charP_zero.mp ⟨δ, h0, hpos⟩
  have hind : IsDeltaIndicator (fun x : K => if x = 0 then 0 else 1) :=
    ⟨by simp, fun a ha => by simp [ha]⟩
  exact ⟨_, hind.zero, delta_natCast_pos_indicator hind,
    delta_absorb_indicator hind⟩

/-- The companion of `delta_exists_iff_charP_zero` for the full axiom set: in a
nontrivial canonically ordered semiring, an admissible `δ` exists if and only if
the characteristic is `0`. -/
theorem isDelta_exists_iff_charP_zero
    {K : Type} [Semiring K] [PartialOrder K] [IsOrderedAddMonoid K]
    [CanonicallyOrderedAdd K] [Nontrivial K] :
    (∃ δ : K → K, IsDelta δ) ↔ CharP K 0 := by
  constructor
  · rintro ⟨δ, hd⟩
    exact delta_exists_iff_charP_zero.mp ⟨δ, hd.zero, hd.natCast_pos⟩
  · intro hchar
    have : CharP K 0 := hchar
    obtain ⟨δ, h0, hpos⟩ := delta_exists_iff_charP_zero.mpr hchar
    exact isDelta_exists_of_natCast_axioms h0 hpos

/-! ## Commutative `SemiringWithMonus`s

`SemiringWithMonus` is intentionally not assumed to be commutative; however, every
provenance semiring used in this library is in fact commutative, and the algebraic
identities that drive HAVING-style aggregate provenance (see `Provenance.Having`)
require it. `CommSemiringWithMonus` packages a `SemiringWithMonus` together with
the commutativity axiom, producing a `CommMonoid` instance whose `Mul` matches
the one already supplied by `SemiringWithMonus`, so no `Mul` diamond appears when
`Finset.prod` is used.
-/

/-- A `SemiringWithMonus` whose multiplication is commutative. -/
class CommSemiringWithMonus (K : Type) extends SemiringWithMonus K where
  /-- Multiplication on `K` is commutative. -/
  mul_comm : ∀ a b : K, a * b = b * a

/-- A `CommSemiringWithMonus` is automatically a `CommMonoid`, sharing its
multiplicative structure with the underlying `SemiringWithMonus`. This makes
`Finset.prod` usable without introducing a separate `CommSemiring` hypothesis
that would cause a `Mul` diamond. -/
instance (priority := 100) {K : Type} [h : CommSemiringWithMonus K] : CommMonoid K where
  mul_comm := h.mul_comm

/-! ## Homomorphisms of `SemiringWithMonus`s
-/

/-- Definition of a homomorphism of `SemiringWithMonus`s. Preserves the
semiring structure (via `RingHom`), the monus (`map_sub`), and the δ
operator (`map_delta`). The latter is required for hom commutation of the
aggregation operator, where δ appears on the row-annotation column
(Definition 7 / R5 of [Sen, Maniu & Senellart][sen2026provsql]). -/
class SemiringWithMonusHom (α β : Type) [SemiringWithMonus α] [SemiringWithMonus β]
  extends RingHom α β where
  map_sub : ∀ (x y: α), toRingHom (x - y) = toRingHom x - toRingHom y
  /-- The hom preserves `δ`: `h (δ a) = δ (h a)`. -/
  map_delta : ∀ (a : α), toRingHom (SemiringWithMonus.delta a) =
    SemiringWithMonus.delta (toRingHom a)

instance (α β) [SemiringWithMonus α] [SemiringWithMonus β] :
CoeFun (SemiringWithMonusHom α β) (fun _ ↦ α → β) where
  coe f := fun x => f.toRingHom x

/-- If ν is an injective m-semiring homomorphism from α to β,
  and β is idempotent, so is α. -/
theorem idempotent_of_injective_homomorphism_idempotent
  [SemiringWithMonus α]
  [SemiringWithMonus β]
  (ν: SemiringWithMonusHom α β)
  (hνi : Function.Injective ν) :
  idempotent β → idempotent α := by
    intro hβ x
    apply hνi
    simp
    exact hβ _

/-- If ν is an m-semiring homomorphism from α onto β,
  and α is idempotent, so is β. -/
theorem idempotent_of_surjective_homomorphism_idempotent
  [SemiringWithMonus α]
  [SemiringWithMonus β]
  (ν: SemiringWithMonusHom α β)
  (hνs : Function.Surjective ν) :
  idempotent α → idempotent β := by
    intro hα x
    have ⟨a,ha⟩ := hνs x
    rw[← ha]
    rw[← RingHom.map_add]
    simp[hα]

/-- If ν is an injective m-semiring homomorphism from α to β,
  and β has left-distributivity of times over monus, so has α. -/
theorem mul_sub_left_of_injective_homomorphism_mul_sub_left
   [SemiringWithMonus α]
   [SemiringWithMonus β]
   (ν: SemiringWithMonusHom α β)
  (hνi : Function.Injective ν) :
  mul_sub_left_distributive β → mul_sub_left_distributive α := by
    intro hβ a b c
    apply hνi
    simp[SemiringWithMonusHom.map_sub]
    exact hβ _ _ _

/-- If ν is an m-semiring homomorphism from α onto β,
  and α has left-distributivity of times over monus, so has β. -/
theorem mul_sub_left_of_surjective_homomorphism_mul_sub_left
  [SemiringWithMonus α]
  [SemiringWithMonus β]
  (ν: SemiringWithMonusHom α β)
  (hνs : Function.Surjective ν) :
  mul_sub_left_distributive α → mul_sub_left_distributive β := by
    intro hα x y z
    have ⟨a,ha⟩ := hνs x
    have ⟨b,hb⟩ := hνs y
    have ⟨c,hc⟩ := hνs z
    rw[← ha, ← hb, ← hc]
    simp only[← SemiringWithMonusHom.map_sub, ← RingHom.map_mul]
    simp[hα]

/-! ## Miscellaneous
-/

/-- On an arbitrary semiring the natural relation `a ≼ b ↔ ∃ c, b = a + c`
is always a preorder (reflexive by `c = 0`, transitive by adding witnesses)
but not always antisymmetric: on `ℤ`, any two elements are related in both
directions, e.g., `0 ≼ 1 ≼ 0` with `0 ≠ 1`. This is why `SemiringWithMonus`
*assumes* the canonically ordered structure instead of deriving an order
from `+`. -/
theorem natural_preorder_not_antisymm :
    ∃ a b : ℤ, (∃ c, b = a + c) ∧ (∃ c, a = b + c) ∧ a ≠ b :=
  ⟨0, 1, ⟨1, by omega⟩, ⟨-1, by omega⟩, by decide⟩

class HasAltLinearOrder (α : Type u) where
  altOrder : LinearOrder α


end SemiringWithMonus
