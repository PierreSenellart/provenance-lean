import Mathlib.Computability.Language
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Monoid.Defs

import Provenance.SemiringWithMonus
import Provenance.Semirings.Regex

/-!
# The min-cost-paths m-semiring (ProvSQL's `sr_tropical_paths`)

A value is `𝟘`, or a cost `c` with a language `L` over the labels of the
input tuples – the least cost of a derivation of a tuple, with every
derivation of that cost. `sr_tropical_paths` (`src/semiring/TropicalPaths.h`,
since 1.13.0) computes in it:
- `(c, L) ⊕ (c', L')` keeps the lower cost with its derivations, and the
  union of the two languages on a tie;
- `(c, L) ⊗ (c', L') = (c + c', L · L')`, the concatenation in the order
  of the query, which does **not** commute (`not_commutative`);
- `𝟘` is the absent value, `𝟙 = (0, {ε})`.

`⊕` is the join of a partial order: the lexicographic order of the
costs reversed and the languages by inclusion (`TropicalPathsVal.le_iff`:
`(c, L) ≤ (c', L')` when `c' < c`, or `c = c'` and `L ⊆ L'`), with `𝟘`
adjoined at the bottom. That order is the natural order of the semiring,
and the monus it determines – `a` where `a` has the lower cost, `𝟘`
where `b` has, and the difference of the languages on a tie – makes the
semiring an m-semiring (`instSemiringWithMonus`). ProvSQL refuses to
compute that monus (`semiring-no-monus`: on a tie it is a difference of
languages, which needs automata), so the refusal is a gap of the
implementation and not of the algebra, exactly as for `sr_regex`.

The star ProvSQL implements is verified against the fixpoint equation
`s = 𝟙 ⊕ a ⊗ s` it solves: for a positive cost the solution is `𝟙`
(`one_add_mul_one_of_pos`: a cycle of positive cost never lies on a
shortest path), for a cost `0` it is `(0, L∗)` (`one_add_mul_kstar`:
the cycle can be followed any number of times at no cost), and for a
negative cost there is none (`no_fixpoint_of_neg`: the least cost is
unbounded), which is what `recursion-cycle-no-value` refuses.

The costs are any linearly ordered cancellative additive monoid (`ℝ`
for ProvSQL), the labels any type.
-/

noncomputable section

/-- A cost and the derivations of that cost: a value of
`sr_tropical_paths` other than `𝟘`. -/
structure TropicalPathsVal (C Λ : Type) where
  cost : C
  paths : Language Λ

namespace TropicalPathsVal

variable {C Λ : Type} [LinearOrder C]

/-- The key the values are ordered by: the cost reversed, then the
language by inclusion. -/
def key (p : TropicalPathsVal C Λ) : OrderDual C ×ₗ Language Λ :=
  toLex (OrderDual.toDual p.cost, p.paths)

omit [LinearOrder C] in
theorem key_injective : Function.Injective (key : TropicalPathsVal C Λ → _) := by
  intro p q h
  have h' := Prod.mk.inj (congrArg ofLex h)
  cases p; cases q
  simp only at h'
  rw [OrderDual.toDual.injective h'.1, h'.2]

instance : PartialOrder (TropicalPathsVal C Λ) := PartialOrder.lift key key_injective

theorem le_iff (p q : TropicalPathsVal C Λ) :
    p ≤ q ↔ q.cost < p.cost ∨ (p.cost = q.cost ∧ p.paths ≤ q.paths) := by
  show key p ≤ key q ↔ _
  rw [key, key, Prod.Lex.toLex_le_toLex]
  simp only [OrderDual.toDual_lt_toDual, OrderDual.toDual_inj]

/-- `⊕` on two values: the lower cost wins, a tie merges the languages. -/
def sup (p q : TropicalPathsVal C Λ) : TropicalPathsVal C Λ :=
  if p.cost < q.cost then p
  else if q.cost < p.cost then q
  else ⟨p.cost, p.paths + q.paths⟩

theorem sup_of_lt {p q : TropicalPathsVal C Λ} (h : p.cost < q.cost) : sup p q = p := by
  rw [sup, ite_eq_left h]

theorem sup_of_gt {p q : TropicalPathsVal C Λ} (h : q.cost < p.cost) : sup p q = q := by
  rw [sup, ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_left h]

theorem sup_of_eq {p q : TropicalPathsVal C Λ} (h : p.cost = q.cost) :
    sup p q = ⟨p.cost, p.paths + q.paths⟩ := by
  rw [sup, ite_eq_right (not_lt.mpr (le_of_eq h.symm)), ite_eq_right (not_lt.mpr (le_of_eq h))]

/-- **`⊕` is the join** of the order. -/
instance : SemilatticeSup (TropicalPathsVal C Λ) where
  sup := sup
  le_sup_left := fun p q => by
    show p ≤ sup p q
    rcases lt_trichotomy p.cost q.cost with h | h | h
    · rw [sup_of_lt h]
    · rw [sup_of_eq h, le_iff]
      exact Or.inr ⟨rfl, le_sup_left⟩
    · rw [sup_of_gt h, le_iff]
      exact Or.inl h
  le_sup_right := fun p q => by
    show q ≤ sup p q
    rcases lt_trichotomy p.cost q.cost with h | h | h
    · rw [sup_of_lt h, le_iff]
      exact Or.inl h
    · rw [sup_of_eq h, le_iff]
      exact Or.inr ⟨h.symm, le_sup_right⟩
    · rw [sup_of_gt h]
  sup_le := fun p q r hp hq => by
    show sup p q ≤ r
    rcases lt_trichotomy p.cost q.cost with h | h | h
    · rw [sup_of_lt h]; exact hp
    · rw [sup_of_eq h, le_iff]
      rw [le_iff] at hp hq
      rcases hp with hp | ⟨hp1, hp2⟩
      · exact Or.inl hp
      · rcases hq with hq | ⟨hq1, hq2⟩
        · exact Or.inl (h ▸ hq)
        · exact Or.inr ⟨hp1, sup_le hp2 hq2⟩
    · rw [sup_of_gt h]; exact hq

theorem sup_def (p q : TropicalPathsVal C Λ) : p ⊔ q = sup p q := rfl

end TropicalPathsVal

/-- **The min-cost-paths semiring**: a value of `sr_tropical_paths`, with
`𝟘` at the bottom. -/
structure TropicalPaths (C Λ : Type) where
  val : Option (TropicalPathsVal C Λ)

namespace TropicalPaths

variable {C Λ : Type} [LinearOrder C]

/-- The order's key: `⊥` for `𝟘`, the value's key otherwise. -/
def keyW (a : TropicalPaths C Λ) : WithBot (OrderDual C ×ₗ Language Λ) :=
  match a.val with
  | none => ⊥
  | some p => WithBot.some (TropicalPathsVal.key p)

omit [LinearOrder C] in
theorem keyW_injective : Function.Injective (keyW : TropicalPaths C Λ → _) := by
  intro a b h
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some q => exact absurd h WithBot.bot_ne_coe
  | some p =>
    cases b with
    | none => exact absurd h WithBot.coe_ne_bot
    | some q => rw [TropicalPathsVal.key_injective (WithBot.coe_inj.mp h)]

instance : PartialOrder (TropicalPaths C Λ) := PartialOrder.lift keyW keyW_injective

theorem some_le_some (p q : TropicalPathsVal C Λ) :
    (⟨some p⟩ : TropicalPaths C Λ) ≤ ⟨some q⟩ ↔ p ≤ q := by
  show WithBot.some (TropicalPathsVal.key p) ≤ WithBot.some (TropicalPathsVal.key q) ↔ _
  rw [WithBot.coe_le_coe]
  exact Iff.rfl

theorem none_le (a : TropicalPaths C Λ) : (⟨none⟩ : TropicalPaths C Λ) ≤ a :=
  (bot_le : (⊥ : WithBot (OrderDual C ×ₗ Language Λ)) ≤ keyW a)

theorem not_some_le_none (p : TropicalPathsVal C Λ) :
    ¬ (⟨some p⟩ : TropicalPaths C Λ) ≤ ⟨none⟩ :=
  fun h => lt_irrefl _ (lt_of_lt_of_le (WithBot.bot_lt_coe (TropicalPathsVal.key p)) h)

theorem le_none_iff (a : TropicalPaths C Λ) : a ≤ ⟨none⟩ ↔ a = ⟨none⟩ := by
  obtain ⟨a⟩ := a
  cases a with
  | none => exact ⟨fun _ => rfl, fun _ => le_refl _⟩
  | some p => exact ⟨fun h => absurd h (not_some_le_none p), fun h => by cases h⟩

/-- `⊕`: `𝟘` is neutral, two values join. -/
def add (a b : TropicalPaths C Λ) : TropicalPaths C Λ :=
  match a.val, b.val with
  | none, _ => b
  | _, none => a
  | some p, some q => ⟨some (p ⊔ q)⟩

instance : Add (TropicalPaths C Λ) := ⟨add⟩

theorem none_add (a : TropicalPaths C Λ) : (⟨none⟩ : TropicalPaths C Λ) + a = a := by
  obtain ⟨a⟩ := a; cases a <;> rfl

theorem add_none (a : TropicalPaths C Λ) : a + (⟨none⟩ : TropicalPaths C Λ) = a := by
  obtain ⟨a⟩ := a; cases a <;> rfl

theorem some_add_some (p q : TropicalPathsVal C Λ) :
    (⟨some p⟩ : TropicalPaths C Λ) + ⟨some q⟩ = ⟨some (p ⊔ q)⟩ := rfl

/-- **`⊕` is the join** of the order with `𝟘` at the bottom. -/
instance : SemilatticeSup (TropicalPaths C Λ) where
  sup := add
  le_sup_left := fun a b => by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    cases a with
    | none => exact none_le _
    | some p =>
      cases b with
      | none => exact le_refl _
      | some q =>
        show (⟨some p⟩ : TropicalPaths C Λ) ≤ ⟨some (p ⊔ q)⟩
        exact (some_le_some _ _).mpr le_sup_left
  le_sup_right := fun a b => by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    cases a with
    | none => exact le_refl _
    | some p =>
      cases b with
      | none => exact none_le _
      | some q =>
        show (⟨some q⟩ : TropicalPaths C Λ) ≤ ⟨some (p ⊔ q)⟩
        exact (some_le_some _ _).mpr le_sup_right
  sup_le := fun a b c ha hb => by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    cases a with
    | none => exact hb
    | some p =>
      cases b with
      | none => exact ha
      | some q =>
        obtain ⟨c⟩ := c
        cases c with
        | none => exact absurd ha (not_some_le_none p)
        | some r =>
          show (⟨some (p ⊔ q)⟩ : TropicalPaths C Λ) ≤ ⟨some r⟩
          exact (some_le_some _ _).mpr
            (sup_le ((some_le_some _ _).mp ha) ((some_le_some _ _).mp hb))

theorem add_eq_sup (a b : TropicalPaths C Λ) : a + b = a ⊔ b := rfl

instance : Zero (TropicalPaths C Λ) := ⟨⟨none⟩⟩

omit [LinearOrder C] in
theorem zero_def : (0 : TropicalPaths C Λ) = ⟨none⟩ := rfl

theorem zero_le' (a : TropicalPaths C Λ) : (0 : TropicalPaths C Λ) ≤ a := none_le a

section Cost
variable [AddCommMonoid C] [IsOrderedCancelAddMonoid C]

/-- `⊗` concatenates the languages, adding the costs; `𝟘` absorbs. -/
instance : Mul (TropicalPaths C Λ) :=
  ⟨fun a b => match a.val, b.val with
    | some p, some q => ⟨some ⟨p.cost + q.cost, p.paths * q.paths⟩⟩
    | _, _ => ⟨none⟩⟩

instance : One (TropicalPaths C Λ) := ⟨⟨some ⟨0, 1⟩⟩⟩

omit [LinearOrder C] [IsOrderedCancelAddMonoid C] in
theorem one_def : (1 : TropicalPaths C Λ) = ⟨some ⟨0, 1⟩⟩ := rfl

omit [LinearOrder C] [IsOrderedCancelAddMonoid C] in
theorem some_mul_some (p q : TropicalPathsVal C Λ) :
    (⟨some p⟩ : TropicalPaths C Λ) * ⟨some q⟩
      = ⟨some ⟨p.cost + q.cost, p.paths * q.paths⟩⟩ := rfl

omit [LinearOrder C] [IsOrderedCancelAddMonoid C] in
theorem none_mul (a : TropicalPaths C Λ) : (⟨none⟩ : TropicalPaths C Λ) * a = ⟨none⟩ := by
  obtain ⟨a⟩ := a; cases a <;> rfl

omit [LinearOrder C] [IsOrderedCancelAddMonoid C] in
theorem mul_none (a : TropicalPaths C Λ) : a * (⟨none⟩ : TropicalPaths C Λ) = ⟨none⟩ := by
  obtain ⟨a⟩ := a; cases a <;> rfl

/-- **Distributivity on the right**, value by value: the lower cost
stays the lower after adding the same cost, and a tie's merged language
concatenates as the union of the concatenations. -/
theorem some_sup_mul (p q r : TropicalPathsVal C Λ) :
    (⟨some (p ⊔ q)⟩ : TropicalPaths C Λ) * ⟨some r⟩
      = ⟨some p⟩ * ⟨some r⟩ + ⟨some q⟩ * ⟨some r⟩ := by
  simp only [some_mul_some]
  rw [some_add_some, TropicalPathsVal.sup_def, TropicalPathsVal.sup_def]
  rcases lt_trichotomy p.cost q.cost with h | h | h
  · rw [TropicalPathsVal.sup_of_lt h,
      TropicalPathsVal.sup_of_lt (show p.cost + r.cost < q.cost + r.cost from
        add_lt_add_left h _)]
  · rw [TropicalPathsVal.sup_of_eq h,
      TropicalPathsVal.sup_of_eq (show p.cost + r.cost = q.cost + r.cost from by rw [h])]
    simp only [add_mul]
  · rw [TropicalPathsVal.sup_of_gt h,
      TropicalPathsVal.sup_of_gt (show q.cost + r.cost < p.cost + r.cost from
        add_lt_add_left h _)]

/-- And on the left. -/
theorem mul_some_sup (p q r : TropicalPathsVal C Λ) :
    (⟨some r⟩ : TropicalPaths C Λ) * ⟨some (p ⊔ q)⟩
      = ⟨some r⟩ * ⟨some p⟩ + ⟨some r⟩ * ⟨some q⟩ := by
  simp only [some_mul_some]
  rw [some_add_some, TropicalPathsVal.sup_def, TropicalPathsVal.sup_def]
  rcases lt_trichotomy p.cost q.cost with h | h | h
  · rw [TropicalPathsVal.sup_of_lt h,
      TropicalPathsVal.sup_of_lt (show r.cost + p.cost < r.cost + q.cost from
        add_lt_add_right h _)]
  · rw [TropicalPathsVal.sup_of_eq h,
      TropicalPathsVal.sup_of_eq (show r.cost + p.cost = r.cost + q.cost from by rw [h])]
    simp only [mul_add]
  · rw [TropicalPathsVal.sup_of_gt h,
      TropicalPathsVal.sup_of_gt (show r.cost + q.cost < r.cost + p.cost from
        add_lt_add_right h _)]

instance : Semiring (TropicalPaths C Λ) where
  add_assoc := fun a b c => by rw [add_eq_sup, add_eq_sup, add_eq_sup, add_eq_sup, sup_assoc]
  zero_add := fun a => none_add a
  add_zero := fun a => add_none a
  add_comm := fun a b => by rw [add_eq_sup, add_eq_sup, sup_comm]
  nsmul := nsmulRec
  mul_assoc := fun a b c => by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    cases a <;> cases b <;> cases c <;>
      simp only [some_mul_some, none_mul, mul_none, add_assoc, mul_assoc]
  zero_mul := fun a => none_mul a
  mul_zero := fun a => mul_none a
  one_mul := fun a => by
    obtain ⟨a⟩ := a
    cases a with
    | none => rfl
    | some p => rw [one_def, some_mul_some]; simp
  mul_one := fun a => by
    obtain ⟨a⟩ := a
    cases a with
    | none => rfl
    | some p => rw [one_def, some_mul_some]; simp
  left_distrib := fun a b c => by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    cases a with
    | none => rw [none_mul, none_mul, none_mul, none_add]
    | some r =>
      cases b with
      | none => rw [none_add, mul_none, none_add]
      | some p =>
        cases c with
        | none => rw [add_none, mul_none, add_none]
        | some q => rw [some_add_some, mul_some_sup]
  right_distrib := fun a b c => by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    cases c with
    | none => rw [mul_none, mul_none, mul_none, none_add]
    | some r =>
      cases a with
      | none => rw [none_add, none_mul, none_add]
      | some p =>
        cases b with
        | none => rw [add_none, none_mul, add_none]
        | some q => rw [some_add_some, some_sup_mul]
  natCast := fun n => if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ := fun n => by
    cases n with
    | zero => show (1 : TropicalPaths C Λ) = 0 + 1; exact (none_add _).symm
    | succ n => show (1 : TropicalPaths C Λ) = 1 + 1; rw [add_eq_sup, sup_idem]

instance : IsOrderedAddMonoid (TropicalPaths C Λ) where
  add_le_add_left := fun _ _ h c => sup_le_sup_right h c

instance : CanonicallyOrderedAdd (TropicalPaths C Λ) where
  exists_add_of_le := fun {_ b} h => ⟨b, (sup_eq_right.mpr h).symm⟩
  le_self_add := fun _ _ => le_sup_left
  le_add_self := fun _ _ => le_sup_right

open Classical in
/-- ProvSQL's `TropicalPaths::delta`: the indicator of being non-`𝟘`. -/
def deltaInd (a : TropicalPaths C Λ) : TropicalPaths C Λ :=
  if a = 0 then 0 else 1

omit [LinearOrder C] [IsOrderedCancelAddMonoid C] in
theorem deltaInd_isIndicator :
    IsDeltaIndicator (deltaInd : TropicalPaths C Λ → TropicalPaths C Λ) where
  zero := by simp [deltaInd]
  nonzero := fun a ha => by simp [deltaInd, ha]

omit [LinearOrder C] [IsOrderedCancelAddMonoid C] in
theorem one_ne_zero' : (1 : TropicalPaths C Λ) ≠ 0 := fun h => by
  cases TropicalPaths.mk.inj h

theorem natCast_pos {n : ℕ} (hn : 0 < n) : ((n : TropicalPaths C Λ)) = 1 := by
  show (if n = 0 then (0 : TropicalPaths C Λ) else 1) = 1
  rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hn)]

open Classical in
/-- **The monus**: `a` where `a` has the lower cost, `𝟘` where `b` has,
and on a tie the difference of the languages, `𝟘` if that is empty. -/
def monus (a b : TropicalPaths C Λ) : TropicalPaths C Λ :=
  match a.val, b.val with
  | none, _ => ⟨none⟩
  | some _, none => a
  | some p, some q =>
    if p.cost < q.cost then a
    else if q.cost < p.cost then ⟨none⟩
    else if p.paths - q.paths = 0 then ⟨none⟩
    else ⟨some ⟨p.cost, p.paths - q.paths⟩⟩

omit [AddCommMonoid C] [IsOrderedCancelAddMonoid C] in
open Classical in
theorem monus_spec' (a b c : TropicalPaths C Λ) : monus a b ≤ c ↔ a ≤ b + c := by
  rw [add_eq_sup]
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  cases a with
  | none =>
    show (⟨none⟩ : TropicalPaths C Λ) ≤ c ↔ _
    exact ⟨fun _ => none_le _, fun _ => none_le _⟩
  | some p =>
    cases b with
    | none =>
      show (⟨some p⟩ : TropicalPaths C Λ) ≤ c ↔ _
      rw [show (⟨none⟩ : TropicalPaths C Λ) ⊔ c = c from sup_eq_right.mpr (none_le c)]
    | some q =>
      obtain ⟨c⟩ := c
      rcases lt_trichotomy p.cost q.cost with h | h | h
      · -- `a` has the lower cost: the monus is `a`.
        show (if p.cost < q.cost then (⟨some p⟩ : TropicalPaths C Λ) else _) ≤ _ ↔ _
        rw [ite_eq_left h]
        constructor
        · exact fun hac => le_trans hac le_sup_right
        · intro hbc
          cases c with
          | none =>
            rw [show (⟨some q⟩ : TropicalPaths C Λ) ⊔ ⟨none⟩ = ⟨some q⟩ from
              sup_eq_left.mpr (none_le _), some_le_some, TropicalPathsVal.le_iff] at hbc
            rcases hbc with hbc | ⟨hbc, -⟩
            · exact absurd (lt_trans h hbc) (lt_irrefl _)
            · exact absurd hbc (ne_of_lt h)
          | some r =>
            rw [show (⟨some q⟩ : TropicalPaths C Λ) ⊔ ⟨some r⟩ = ⟨some (q ⊔ r)⟩ from rfl,
              some_le_some, TropicalPathsVal.sup_def] at hbc
            rw [some_le_some]
            rcases lt_trichotomy q.cost r.cost with h' | h' | h'
            · rw [TropicalPathsVal.sup_of_lt h', TropicalPathsVal.le_iff] at hbc
              rcases hbc with hbc | ⟨hbc, -⟩
              · exact absurd (lt_trans h hbc) (lt_irrefl _)
              · exact absurd hbc (ne_of_lt h)
            · rw [TropicalPathsVal.sup_of_eq h', TropicalPathsVal.le_iff] at hbc
              rcases hbc with hbc | ⟨hbc, -⟩
              · exact absurd (lt_trans h hbc) (lt_irrefl _)
              · exact absurd hbc (ne_of_lt h)
            · rw [TropicalPathsVal.sup_of_gt h'] at hbc
              exact hbc
      · -- a tie: the difference of the languages.
        show (if p.cost < q.cost then (⟨some p⟩ : TropicalPaths C Λ)
          else if q.cost < p.cost then ⟨none⟩
          else if p.paths - q.paths = 0 then ⟨none⟩
          else ⟨some ⟨p.cost, p.paths - q.paths⟩⟩) ≤ _ ↔ _
        rw [ite_eq_right (not_lt.mpr (le_of_eq h.symm)),
          ite_eq_right (not_lt.mpr (le_of_eq h))]
        by_cases hd : p.paths - q.paths = 0
        · rw [ite_eq_left hd]
          refine ⟨fun _ => le_trans ?_ le_sup_left, fun _ => none_le _⟩
          rw [some_le_some, TropicalPathsVal.le_iff]
          exact Or.inr ⟨h, tsub_eq_zero_iff_le.mp hd⟩
        · rw [ite_eq_right hd]
          cases c with
          | none =>
            rw [show (⟨some q⟩ : TropicalPaths C Λ) ⊔ ⟨none⟩ = ⟨some q⟩ from
              sup_eq_left.mpr (none_le _), some_le_some, TropicalPathsVal.le_iff]
            constructor
            · exact fun hc => absurd hc (not_some_le_none _)
            · rintro (hc | ⟨-, hc⟩)
              · exact absurd (h ▸ hc) (lt_irrefl _)
              · exact absurd (tsub_eq_zero_iff_le.mpr hc) hd
          | some r =>
            rw [show (⟨some q⟩ : TropicalPaths C Λ) ⊔ ⟨some r⟩ = ⟨some (q ⊔ r)⟩ from rfl,
              some_le_some, some_le_some, TropicalPathsVal.sup_def,
              TropicalPathsVal.le_iff]
            rcases lt_trichotomy q.cost r.cost with h' | h' | h'
            · rw [TropicalPathsVal.sup_of_lt h', TropicalPathsVal.le_iff]
              constructor
              · rintro (hc | ⟨hc, -⟩)
                · exact absurd (h ▸ hc) (not_lt.mpr (le_of_lt h'))
                · exact absurd (h.symm.trans hc) (ne_of_lt h')
              · rintro (hc | ⟨-, hc⟩)
                · exact absurd (h ▸ hc) (lt_irrefl _)
                · exact absurd (tsub_eq_zero_iff_le.mpr hc) hd
            · rw [TropicalPathsVal.sup_of_eq h', TropicalPathsVal.le_iff]
              constructor
              · rintro (hc | ⟨hc, hc'⟩)
                · exact absurd (h.trans h' ▸ hc) (lt_irrefl _)
                · refine Or.inr ⟨h, ?_⟩
                  rw [tsub_le_iff_right] at hc'
                  rw [add_comm]; exact hc'
              · rintro (hc | ⟨-, hc⟩)
                · exact absurd (h ▸ hc) (lt_irrefl _)
                · refine Or.inr ⟨h.trans h', ?_⟩
                  rw [tsub_le_iff_right, add_comm]; exact hc
            · rw [TropicalPathsVal.sup_of_gt h', TropicalPathsVal.le_iff]
              constructor
              · rintro (hc | ⟨hc, -⟩)
                · exact Or.inl hc
                · exact absurd (h.symm.trans hc) (ne_of_gt h')
              · rintro (hc | ⟨hc, -⟩)
                · exact Or.inl hc
                · exact absurd (h.symm.trans hc) (ne_of_gt h')
      · -- `b` has the lower cost: the monus is `𝟘`, and `a ≤ b`.
        show (if p.cost < q.cost then (⟨some p⟩ : TropicalPaths C Λ)
          else if q.cost < p.cost then ⟨none⟩ else _) ≤ _ ↔ _
        rw [ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_left h]
        refine ⟨fun _ => le_trans ?_ le_sup_left, fun _ => none_le _⟩
        rw [some_le_some, TropicalPathsVal.le_iff]
        exact Or.inl h

/-- **The min-cost-paths semiring is an m-semiring.** -/
instance : SemiringWithMonus (TropicalPaths C Λ) where
  sub := monus
  monus_spec := monus_spec'
  delta := deltaInd
  delta_zero := deltaInd_isIndicator.zero
  delta_natCast_pos := fun hn => by
    rw [natCast_pos hn]
    exact deltaInd_isIndicator.nonzero 1 one_ne_zero'
  delta_absorb := delta_absorb_indicator deltaInd_isIndicator

theorem idempotent_add : idempotent (TropicalPaths C Λ) := fun a => by
  rw [add_eq_sup, sup_idem]

omit [LinearOrder C] [IsOrderedCancelAddMonoid C] in
/-- **Concatenation does not commute**: two distinct labels in either
order are two distinct words. -/
theorem not_commutative {a b : Λ} (hab : a ≠ b) (c : C) :
    (⟨some ⟨c, {[a]}⟩⟩ : TropicalPaths C Λ) * ⟨some ⟨c, {[b]}⟩⟩
      ≠ (⟨some ⟨c, {[b]}⟩⟩ : TropicalPaths C Λ) * ⟨some ⟨c, {[a]}⟩⟩ := by
  rw [some_mul_some, some_mul_some]
  intro h
  have h' := (TropicalPathsVal.mk.inj (Option.some.inj (TropicalPaths.mk.inj h))).2
  exact Language.not_commutative hab h'

/-- **Not exclusive**: a value of positive cost is beaten by `𝟙`, whose
monus against it is `𝟙` again, and `a ⊗ 𝟙 = a ≠ 𝟘`. -/
theorem not_exclusive {c : C} (hc : 0 < c) (L : Language Λ) :
    (⟨some ⟨c, L⟩⟩ : TropicalPaths C Λ) * (1 - ⟨some ⟨c, L⟩⟩) ≠ 0 := by
  have h1 : (1 : TropicalPaths C Λ) - ⟨some ⟨c, L⟩⟩ = 1 := by
    show monus 1 _ = 1
    rw [one_def]
    show (if (0 : C) < c then (⟨some ⟨0, 1⟩⟩ : TropicalPaths C Λ) else _) = _
    rw [ite_eq_left hc]
  rw [h1, mul_one]
  exact fun h => by cases TropicalPaths.mk.inj h

/-! ## The star, against the fixpoint equation it solves -/

/-- A cycle of positive cost is never followed on a shortest path: `𝟙`
solves `s = 𝟙 ⊕ a ⊗ s`. -/
theorem one_add_mul_one_of_pos {c : C} (hc : 0 < c) (L : Language Λ) :
    (1 : TropicalPaths C Λ) + ⟨some ⟨c, L⟩⟩ * 1 = 1 := by
  rw [mul_one, one_def, some_add_some, TropicalPathsVal.sup_def,
    TropicalPathsVal.sup_of_lt hc]

omit [IsOrderedCancelAddMonoid C] in
/-- A cycle of cost `0` is followed any number of times at no cost:
`(0, L∗)` solves `s = 𝟙 ⊕ a ⊗ s` for `a = (0, L)`. -/
theorem one_add_mul_kstar (L : Language Λ) :
    (1 : TropicalPaths C Λ) + ⟨some ⟨0, L⟩⟩ * ⟨some ⟨0, KStar.kstar L⟩⟩
      = ⟨some ⟨0, KStar.kstar L⟩⟩ := by
  rw [some_mul_some, one_def, some_add_some, TropicalPathsVal.sup_def,
    TropicalPathsVal.sup_of_eq (by simp), add_zero,
    Language.one_add_self_mul_kstar_eq_kstar]

/-- A cycle of negative cost has no least cost: no value solves
`s = 𝟙 ⊕ a ⊗ s`, which is what `recursion-cycle-no-value` refuses. -/
theorem no_fixpoint_of_neg {c : C} (hc : c < 0) (L : Language Λ) (s : TropicalPaths C Λ) :
    (1 : TropicalPaths C Λ) + ⟨some ⟨c, L⟩⟩ * s ≠ s := by
  obtain ⟨s⟩ := s
  cases s with
  | none => rw [mul_none, add_none]; exact one_ne_zero'
  | some r =>
    rw [some_mul_some, one_def, some_add_some, TropicalPathsVal.sup_def]
    intro h
    have hs := Option.some.inj (TropicalPaths.mk.inj h)
    rcases lt_trichotomy (0 : C) (c + r.cost) with h0 | h0 | h0
    · rw [TropicalPathsVal.sup_of_lt (p := ⟨0, 1⟩) (q := ⟨c + r.cost, L * r.paths⟩) h0] at hs
      have hr : r.cost = 0 := (congrArg TropicalPathsVal.cost hs).symm
      rw [hr, add_zero] at h0
      exact absurd h0 (not_lt.mpr (le_of_lt hc))
    · rw [TropicalPathsVal.sup_of_eq (p := ⟨0, 1⟩) (q := ⟨c + r.cost, L * r.paths⟩) h0] at hs
      have hr : r.cost = 0 := (congrArg TropicalPathsVal.cost hs).symm
      rw [hr, add_zero] at h0
      exact absurd h0.symm (ne_of_lt hc)
    · rw [TropicalPathsVal.sup_of_gt (p := ⟨0, 1⟩) (q := ⟨c + r.cost, L * r.paths⟩) h0] at hs
      have hr : r.cost = c + r.cost := (congrArg TropicalPathsVal.cost hs).symm
      have hlt := add_lt_add_left hc r.cost
      rw [zero_add, ← hr] at hlt
      exact lt_irrefl _ hlt

end Cost

end TropicalPaths

end
