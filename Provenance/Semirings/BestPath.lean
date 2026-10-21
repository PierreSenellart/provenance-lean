import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.List.Lex
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Monoid.Defs

import Provenance.SemiringWithMonus

/-!
# The one-best-derivation m-semiring (ProvSQL's `sr_best_path`)

A value is `𝟘`, or a cost `c` with a word `w` of labels – one derivation
of a tuple, with its cost – and a value is *better* than another when
its cost is lower or, at equal costs, when its word comes first in
shortlex order (shorter first, then lexicographic). `sr_best_path`
(`src/semiring/BestPath.h`, since 1.13.0) computes in it:
- `a ⊕ b` is the better of the two, so that the values form a chain with
  `𝟘` at the bottom and `⊕` its maximum (`selective_of`);
- `(c, w) ⊗ (c', w') = (c + c', w · w')`, the concatenation in the order
  of the query, which does **not** commute (`not_commutative`);
- `𝟙 = (0, ε)`;
- `a ⊖ b` is `a` where `a` is strictly better than `b`, `𝟘` otherwise.

The chain is the natural order of the semiring, better being greater:
the `LinearOrder` of `BestPathVal` is the dual of the shortlex-with-cost
key, with `𝟘` adjoined at the bottom. What makes the semiring laws hold
is that this key is compatible with concatenation on both sides
(`key_mul_le_mul_right`, `key_mul_le_mul_left`), strictly, which is also
what gives the distributivity of `⊗` over the monus on both sides
(`mul_sub_left_distributive_of`, `mul_sub_right_distributive_of`) that
`BestPath.h` claims. ProvSQL's two further claims: with nonnegative
costs `𝟙` is the best value, so the semiring is **absorptive on both
sides** (`absorptive_of`, which asks `0 ≤ c` of every cost – ProvSQL
refuses a negative cost at the leaves, `semiring-negative-cost`), and
every star is then `𝟙`. Without the cost hypothesis the semiring laws
still hold; only absorptivity does not.

The costs are any linearly ordered cancellative additive monoid
(`ℝ`, `ℝ≥0`, `ℕ`), the labels any linearly ordered type (ProvSQL
compares them bytewise).
-/

/-- A cost and a word of labels: a value of `sr_best_path` other than
`𝟘`. -/
structure BestPathVal (C Λ : Type) where
  cost : C
  word : List Λ

namespace BestPathVal

variable {C Λ : Type} [LinearOrder C] [LinearOrder Λ]

/-- The key a value is compared by: its cost, then the length of its
word, then the word itself in lexicographic order. Smaller is better. -/
def key (p : BestPathVal C Λ) : C ×ₗ (ℕ ×ₗ List Λ) :=
  toLex (p.cost, toLex (p.word.length, p.word))

omit [LinearOrder C] [LinearOrder Λ] in
theorem key_injective : Function.Injective (key : BestPathVal C Λ → _) := by
  intro p q h
  have h' := congrArg ofLex h
  simp only [key, ofLex_toLex] at h'
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  have h2' := congrArg ofLex h2
  simp only [ofLex_toLex] at h2'
  cases p; cases q
  simp only at h1 h2'
  cases h1
  cases (Prod.mk.inj h2').2
  rfl

/-- **The chain**: better is greater. -/
instance : LinearOrder (BestPathVal C Λ) :=
  LinearOrder.lift' (fun p => OrderDual.toDual (key p))
    (fun _ _ h => key_injective (OrderDual.toDual.injective h))

theorem le_iff_key (p q : BestPathVal C Λ) : p ≤ q ↔ key q ≤ key p := Iff.rfl
theorem lt_iff_key (p q : BestPathVal C Λ) : p < q ↔ key q < key p := Iff.rfl

omit [LinearOrder C] [LinearOrder Λ] in
/-- A lexicographic comparison of two words of equal length survives
appending the same word to both. -/
theorem lex_append_right_of_length_eq {r : Λ → Λ → Prop} :
    ∀ {s₁ s₂ : List Λ}, List.Lex r s₁ s₂ → s₁.length = s₂.length →
      ∀ t, List.Lex r (s₁ ++ t) (s₂ ++ t)
  | _, _, .nil, h, _ => absurd h (by simp)
  | _, _, .cons h, hl, t => .cons (lex_append_right_of_length_eq h (by simpa using hl) t)
  | _, _, .rel h, _, _ => .rel h

omit [LinearOrder C] in
theorem append_lt_append_right {s₁ s₂ : List Λ} (h : s₁ < s₂)
    (hl : s₁.length = s₂.length) (t : List Λ) : s₁ ++ t < s₂ ++ t :=
  lex_append_right_of_length_eq h hl t

omit [LinearOrder C] in
theorem append_lt_append_left {s₁ s₂ : List Λ} (h : s₁ < s₂) (t : List Λ) :
    t ++ s₁ < t ++ s₂ :=
  List.Lex.append_left _ h t

section Cost
variable [AddCommMonoid C] [IsOrderedCancelAddMonoid C]

/-- Concatenation, with the costs added. -/
def mul (p q : BestPathVal C Λ) : BestPathVal C Λ :=
  ⟨p.cost + q.cost, p.word ++ q.word⟩

/-- The empty derivation at cost `0`. -/
def one : BestPathVal C Λ := ⟨0, []⟩

/-- The key is strictly monotone under concatenation on the right. -/
theorem key_mul_lt_mul_right {p q : BestPathVal C Λ} (h : key p < key q)
    (r : BestPathVal C Λ) : key (mul p r) < key (mul q r) := by
  simp only [key, mul, Prod.Lex.toLex_lt_toLex] at h ⊢
  rcases h with h | ⟨h1, h⟩
  · exact Or.inl (add_lt_add_left h _)
  · refine Or.inr ⟨by rw [h1], ?_⟩
    rcases h with h | ⟨h2, h⟩
    · exact Or.inl (by simp only [List.length_append]; omega)
    · exact Or.inr ⟨by simp only [List.length_append, h2],
        append_lt_append_right h h2 _⟩

/-- And on the left. -/
theorem key_mul_lt_mul_left {p q : BestPathVal C Λ} (h : key p < key q)
    (r : BestPathVal C Λ) : key (mul r p) < key (mul r q) := by
  simp only [key, mul, Prod.Lex.toLex_lt_toLex] at h ⊢
  rcases h with h | ⟨h1, h⟩
  · exact Or.inl (add_lt_add_right h _)
  · refine Or.inr ⟨by rw [h1], ?_⟩
    rcases h with h | ⟨h2, h⟩
    · exact Or.inl (by simp only [List.length_append]; omega)
    · exact Or.inr ⟨by simp only [List.length_append, h2],
        append_lt_append_left h _⟩

theorem key_mul_le_mul_right {p q : BestPathVal C Λ} (h : key p ≤ key q)
    (r : BestPathVal C Λ) : key (mul p r) ≤ key (mul q r) := by
  rcases lt_or_eq_of_le h with h | h
  · exact le_of_lt (key_mul_lt_mul_right h r)
  · rw [key_injective h]

theorem key_mul_le_mul_left {p q : BestPathVal C Λ} (h : key p ≤ key q)
    (r : BestPathVal C Λ) : key (mul r p) ≤ key (mul r q) := by
  rcases lt_or_eq_of_le h with h | h
  · exact le_of_lt (key_mul_lt_mul_left h r)
  · rw [key_injective h]

/-- In the chain's order (better is greater), `⊗ r` is monotone. -/
theorem mul_le_mul_right' {p q : BestPathVal C Λ} (h : p ≤ q) (r : BestPathVal C Λ) :
    mul p r ≤ mul q r :=
  key_mul_le_mul_right h r

theorem mul_le_mul_left' {p q : BestPathVal C Λ} (h : p ≤ q) (r : BestPathVal C Λ) :
    mul r p ≤ mul r q :=
  key_mul_le_mul_left h r

theorem mul_lt_mul_right' {p q : BestPathVal C Λ} (h : p < q) (r : BestPathVal C Λ) :
    mul p r < mul q r :=
  key_mul_lt_mul_right h r

theorem mul_lt_mul_left' {p q : BestPathVal C Λ} (h : p < q) (r : BestPathVal C Λ) :
    mul r p < mul r q :=
  key_mul_lt_mul_left h r

theorem mul_le_mul_right_iff (p q r : BestPathVal C Λ) :
    mul p r ≤ mul q r ↔ p ≤ q :=
  ⟨fun h => le_of_not_gt fun h' => not_lt_of_ge h (mul_lt_mul_right' h' r),
    fun h => mul_le_mul_right' h r⟩

theorem mul_le_mul_left_iff (p q r : BestPathVal C Λ) :
    mul r p ≤ mul r q ↔ p ≤ q :=
  ⟨fun h => le_of_not_gt fun h' => not_lt_of_ge h (mul_lt_mul_left' h' r),
    fun h => mul_le_mul_left' h r⟩

end Cost

end BestPathVal

/-- **The one-best-derivation semiring**: a value of `sr_best_path`, with
`𝟘` at the bottom of the chain. A structure of its own, so that the
chain's order and the operations below are found on it and not on
`Option`. -/
structure BestPath (C Λ : Type) where
  val : Option (BestPathVal C Λ)

namespace BestPath

variable {C Λ : Type} [LinearOrder C] [LinearOrder Λ]

/-- The chain's key: `⊥` for `𝟘`, the dual of the value's key otherwise. -/
def keyW (a : BestPath C Λ) : WithBot (OrderDual (C ×ₗ (ℕ ×ₗ List Λ))) :=
  match a.val with
  | none => ⊥
  | some p => WithBot.some (OrderDual.toDual (BestPathVal.key p))

omit [LinearOrder C] [LinearOrder Λ] in
theorem keyW_injective : Function.Injective (keyW : BestPath C Λ → _) := by
  intro a b h
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some q => exact absurd h (WithBot.bot_ne_coe)
      | some p =>
        cases b with
        | none => exact absurd h (WithBot.coe_ne_bot)
        | some q =>
          have h' := WithBot.coe_inj.mp h
          rw [BestPathVal.key_injective (OrderDual.toDual.injective h')]

instance : LinearOrder (BestPath C Λ) := LinearOrder.lift' keyW keyW_injective

theorem le_iff_keyW (a b : BestPath C Λ) : a ≤ b ↔ keyW a ≤ keyW b := Iff.rfl

theorem some_le_some (p q : BestPathVal C Λ) :
    (⟨some p⟩ : BestPath C Λ) ≤ ⟨some q⟩ ↔ p ≤ q := by
  rw [le_iff_keyW]
  show WithBot.some (OrderDual.toDual (BestPathVal.key p))
    ≤ WithBot.some (OrderDual.toDual (BestPathVal.key q)) ↔ _
  rw [WithBot.coe_le_coe]
  exact Iff.rfl

theorem none_le (a : BestPath C Λ) : (⟨none⟩ : BestPath C Λ) ≤ a := by
  rw [le_iff_keyW]
  exact bot_le

theorem not_some_le_none (p : BestPathVal C Λ) :
    ¬ (⟨some p⟩ : BestPath C Λ) ≤ ⟨none⟩ := by
  rw [le_iff_keyW]
  exact not_le.mpr (WithBot.bot_lt_coe _)

/-- `⊕` is the better of two values: the maximum of the chain. -/
instance : Add (BestPath C Λ) := ⟨fun a b => max a b⟩

theorem add_def (a b : BestPath C Λ) : a + b = max a b := rfl

instance : Zero (BestPath C Λ) := ⟨⟨none⟩⟩

omit [LinearOrder C] [LinearOrder Λ] in
theorem zero_def : (0 : BestPath C Λ) = ⟨none⟩ := rfl

theorem zero_le' (a : BestPath C Λ) : (0 : BestPath C Λ) ≤ a := none_le a

section Cost
variable [AddCommMonoid C] [IsOrderedCancelAddMonoid C]

/-- `⊗` concatenates, adding the costs; `𝟘` absorbs. -/
instance : Mul (BestPath C Λ) :=
  ⟨fun a b => match a.val, b.val with
    | some p, some q => ⟨some (BestPathVal.mul p q)⟩
    | _, _ => ⟨none⟩⟩

instance : One (BestPath C Λ) := ⟨⟨some BestPathVal.one⟩⟩

omit [LinearOrder C] [LinearOrder Λ] [IsOrderedCancelAddMonoid C] in
theorem one_def : (1 : BestPath C Λ) = ⟨some BestPathVal.one⟩ := rfl

omit [LinearOrder C] [LinearOrder Λ] [IsOrderedCancelAddMonoid C] in
theorem some_mul_some (p q : BestPathVal C Λ) :
    (⟨some p⟩ : BestPath C Λ) * ⟨some q⟩ = ⟨some (BestPathVal.mul p q)⟩ := rfl

omit [LinearOrder C] [LinearOrder Λ] [IsOrderedCancelAddMonoid C] in
theorem none_mul (a : BestPath C Λ) : (⟨none⟩ : BestPath C Λ) * a = ⟨none⟩ := by
  obtain ⟨a⟩ := a
  cases a <;> rfl

omit [LinearOrder C] [LinearOrder Λ] [IsOrderedCancelAddMonoid C] in
theorem mul_none (a : BestPath C Λ) : a * (⟨none⟩ : BestPath C Λ) = ⟨none⟩ := by
  obtain ⟨a⟩ := a
  cases a <;> rfl

/-- `⊗ r` is monotone in the chain. -/
theorem mul_right_mono (r : BestPath C Λ) : Monotone (fun a : BestPath C Λ => a * r) := by
  intro a b h
  dsimp only
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  obtain ⟨r⟩ := r
  cases a with
  | none => rw [none_mul]; exact none_le _
  | some p =>
    cases b with
    | none => exact absurd h (not_some_le_none p)
    | some q =>
      cases r with
      | none => rw [mul_none, mul_none]
      | some r =>
        rw [some_mul_some, some_mul_some, some_le_some]
        exact BestPathVal.mul_le_mul_right' ((some_le_some p q).mp h) r

theorem mul_left_mono (r : BestPath C Λ) : Monotone (fun a : BestPath C Λ => r * a) := by
  intro a b h
  dsimp only
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  obtain ⟨r⟩ := r
  cases a with
  | none => rw [mul_none]; exact none_le _
  | some p =>
    cases b with
    | none => exact absurd h (not_some_le_none p)
    | some q =>
      cases r with
      | none => rw [none_mul, none_mul]
      | some r =>
        rw [some_mul_some, some_mul_some, some_le_some]
        exact BestPathVal.mul_le_mul_left' ((some_le_some p q).mp h) r

instance : Semiring (BestPath C Λ) where
  add_assoc := max_assoc
  zero_add := fun a => max_eq_right (zero_le' a)
  add_zero := fun a => max_eq_left (zero_le' a)
  add_comm := max_comm
  nsmul := nsmulRec
  mul_assoc := fun a b c => by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    cases a <;> cases b <;> cases c <;>
      simp only [some_mul_some, none_mul, mul_none, BestPathVal.mul, add_assoc,
        List.append_assoc]
  zero_mul := fun a => none_mul a
  mul_zero := fun a => mul_none a
  one_mul := fun a => by
    obtain ⟨a⟩ := a
    cases a with
    | none => rfl
    | some p =>
      rw [one_def, some_mul_some]
      simp [BestPathVal.mul, BestPathVal.one]
  mul_one := fun a => by
    obtain ⟨a⟩ := a
    cases a with
    | none => rfl
    | some p =>
      rw [one_def, some_mul_some]
      simp [BestPathVal.mul, BestPathVal.one]
  left_distrib := fun a b c => (mul_left_mono a).map_max
  right_distrib := fun a b c => (mul_right_mono c).map_max
  natCast := fun n => if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ := fun n => by
    cases n with
    | zero => show (1 : BestPath C Λ) = max 0 1; exact (max_eq_right (zero_le' _)).symm
    | succ n => show (1 : BestPath C Λ) = max 1 1; exact (max_self _).symm

instance : IsOrderedAddMonoid (BestPath C Λ) where
  add_le_add_left := fun _ _ h c => max_le_max h (le_refl c)

instance : CanonicallyOrderedAdd (BestPath C Λ) where
  exists_add_of_le := fun {_ b} h => ⟨b, (max_eq_right h).symm⟩
  le_self_add := fun _ _ => le_max_left _ _
  le_add_self := fun _ _ => le_max_right _ _

/-- ProvSQL's `BestPath::delta`: the indicator of being non-`𝟘`. -/
noncomputable def deltaInd (a : BestPath C Λ) : BestPath C Λ :=
  if a = 0 then 0 else 1

omit [IsOrderedCancelAddMonoid C] in
theorem deltaInd_isIndicator : IsDeltaIndicator (deltaInd : BestPath C Λ → BestPath C Λ) where
  zero := by simp [deltaInd]
  nonzero := fun a ha => by simp [deltaInd, ha]

omit [LinearOrder C] [LinearOrder Λ] [IsOrderedCancelAddMonoid C] in
theorem one_ne_zero' : (1 : BestPath C Λ) ≠ 0 := fun h => by
  cases BestPath.mk.inj h

theorem natCast_pos {n : ℕ} (hn : 0 < n) : ((n : BestPath C Λ)) = 1 := by
  show (if n = 0 then (0 : BestPath C Λ) else 1) = 1
  rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hn)]

/-- **The one-best-derivation semiring is an m-semiring**: `a ⊖ b` is
`a` where `a` is strictly better than `b` and `𝟘` otherwise, the least
`c` with `a ≤ b ⊕ c` in a chain. -/
noncomputable instance : SemiringWithMonus (BestPath C Λ) where
  sub := fun a b => if a ≤ b then 0 else a
  monus_spec := fun a b c => by
    show (if a ≤ b then (0 : BestPath C Λ) else a) ≤ c ↔ a ≤ max b c
    split_ifs with h
    · exact ⟨fun _ => le_trans h (le_max_left b c), fun _ => zero_le' c⟩
    · constructor
      · exact fun hac => le_trans hac (le_max_right b c)
      · intro hbc
        rcases le_max_iff.mp hbc with h' | h'
        · exact absurd h' h
        · exact h'
  delta := deltaInd
  delta_zero := deltaInd_isIndicator.zero
  delta_natCast_pos := fun hn => by
    rw [natCast_pos hn]
    exact deltaInd_isIndicator.nonzero 1 one_ne_zero'
  delta_absorb := delta_absorb_indicator deltaInd_isIndicator

theorem sub_def (a b : BestPath C Λ) : a - b = if a ≤ b then 0 else a := rfl

omit [AddCommMonoid C] [IsOrderedCancelAddMonoid C] in
/-- `⊕` keeps one of its arguments. -/
theorem selective_of (a b : BestPath C Λ) : a + b = a ∨ a + b = b := by
  rw [add_def]
  rcases le_total a b with h | h
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left h)

theorem idempotent_add : idempotent (BestPath C Λ) := fun a => max_self a

omit [LinearOrder C] [LinearOrder Λ] [IsOrderedCancelAddMonoid C] in
/-- **Concatenation does not commute**: two distinct labels in either
order are two distinct words. -/
theorem not_commutative {a b : Λ} (hab : a ≠ b) (c : C) :
    (⟨some ⟨c, [a]⟩⟩ : BestPath C Λ) * ⟨some ⟨c, [b]⟩⟩
      ≠ (⟨some ⟨c, [b]⟩⟩ : BestPath C Λ) * ⟨some ⟨c, [a]⟩⟩ := by
  rw [some_mul_some, some_mul_some]
  intro h
  have h' := BestPathVal.mk.inj (Option.some.inj (BestPath.mk.inj h))
  simp only [List.singleton_append, List.cons.injEq] at h'
  exact hab h'.2.1

/-- **Absorptive on both sides, for nonnegative costs**: `𝟙 = (0, ε)` is
then the best value, so `𝟙 ⊕ a = 𝟙` – and absorptivity on the other side
of a product is the same statement in a semiring where `⊕` is a
maximum. -/
theorem absorptive_of (h0 : ∀ c : C, 0 ≤ c) : absorptive (BestPath C Λ) := by
  intro a
  rw [add_def]
  refine max_eq_left ?_
  obtain ⟨a⟩ := a
  cases a with
  | none => exact none_le _
  | some p =>
    rw [one_def, some_le_some, BestPathVal.le_iff_key]
    simp only [BestPathVal.key, BestPathVal.one, Prod.Lex.toLex_le_toLex,
      List.length_nil]
    rcases lt_or_eq_of_le (h0 p.cost) with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rcases Nat.eq_zero_or_pos p.word.length with hl | hl
      · refine Or.inr ⟨hl.symm, ?_⟩
        rw [List.length_eq_zero_iff.mp hl]
      · exact Or.inl hl

/-- **`⊗` distributes over the monus on the left**: `⊗` by a value is an
order embedding of the chain, so it carries “strictly better” along. -/
theorem mul_sub_left_distributive_of : mul_sub_left_distributive (BestPath C Λ) := by
  intro a b c
  rw [sub_def, sub_def]
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  obtain ⟨c⟩ := c
  cases a with
  | none => simp only [none_mul]; rw [ite_eq_left (le_refl _)]; rfl
  | some a =>
    cases b with
    | none =>
      rw [ite_eq_left (none_le _), zero_def, mul_none, ite_eq_left (none_le _)]
    | some b =>
      cases c with
      | none =>
        rw [ite_eq_right (not_some_le_none b), mul_none, some_mul_some,
          ite_eq_right (not_some_le_none _)]
      | some c =>
        rw [some_mul_some, some_mul_some]
        by_cases hbc : b ≤ c
        · rw [ite_eq_left ((some_le_some b c).mpr hbc),
            ite_eq_left ((some_le_some _ _).mpr (BestPathVal.mul_le_mul_left' hbc a)),
            zero_def, mul_none]
        · rw [ite_eq_right (fun h => hbc ((some_le_some b c).mp h)),
            ite_eq_right (fun h => hbc ((BestPathVal.mul_le_mul_left_iff b c a).mp
              ((some_le_some _ _).mp h))), some_mul_some]

/-- And on the right. -/
theorem mul_sub_right_distributive_of (a b c : BestPath C Λ) :
    (b - c) * a = b * a - c * a := by
  rw [sub_def, sub_def]
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  obtain ⟨c⟩ := c
  cases a with
  | none => simp only [mul_none]; rw [ite_eq_left (le_refl _)]; rfl
  | some a =>
    cases b with
    | none =>
      rw [ite_eq_left (none_le _), zero_def, none_mul, ite_eq_left (none_le _)]
    | some b =>
      cases c with
      | none =>
        rw [ite_eq_right (not_some_le_none b), none_mul, some_mul_some,
          ite_eq_right (not_some_le_none _)]
      | some c =>
        rw [some_mul_some, some_mul_some]
        by_cases hbc : b ≤ c
        · rw [ite_eq_left ((some_le_some b c).mpr hbc),
            ite_eq_left ((some_le_some _ _).mpr (BestPathVal.mul_le_mul_right' hbc a)),
            zero_def, none_mul]
        · rw [ite_eq_right (fun h => hbc ((some_le_some b c).mp h)),
            ite_eq_right (fun h => hbc ((BestPathVal.mul_le_mul_right_iff b c a).mp
              ((some_le_some _ _).mp h))), some_mul_some]

/-- **Complemented**: `𝟙 ⊖ (a ⊕ b) = (𝟙 ⊖ a) ⊗ (𝟙 ⊖ b)`, both sides `𝟘`
exactly when one of `a`, `b` is at least `𝟙`. -/
theorem complemented_of : complemented (BestPath C Λ) := by
  intro a b
  rw [sub_def, sub_def, sub_def, add_def]
  by_cases ha : (1 : BestPath C Λ) ≤ a
  · rw [ite_eq_left ha, ite_eq_left (le_trans ha (le_max_left a b)), zero_def, none_mul]
  · rw [ite_eq_right ha]
    by_cases hb : (1 : BestPath C Λ) ≤ b
    · rw [ite_eq_left hb, ite_eq_left (le_trans hb (le_max_right a b)), zero_def, mul_none]
    · rw [ite_eq_right hb, ite_eq_right (fun h => ?_), mul_one]
      rcases le_max_iff.mp h with h | h
      · exact ha h
      · exact hb h

end Cost

end BestPath
