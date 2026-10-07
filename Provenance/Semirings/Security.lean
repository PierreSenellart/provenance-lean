/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.SemiringWithMonus
import Mathlib.Order.BooleanAlgebra.Defs

/-!
# The security semiring, and every Boolean algebra as an m-semiring

The *alternative security semiring* `S′` of Amsterdamer, Deutch and
Tannen annotates a tuple with the set of clearance levels at which it may
be seen: `⊕` is union, `⊗` is intersection, `𝟘` is the empty set, `𝟙` is
the whole set `L` of levels, the monus is set difference and `δ` is the
identity. It is `𝔹^L`, and nothing about it is special to sets: the
construction below reads **any** Boolean algebra as an m-semiring, with
`⊕ = ⊔`, `⊗ = ⊓`, `a ⊖ b = a \ b` and `δ = id`, and `S′` is that
construction at `Set L`.

`BooleanAlgebra.toSemiringWithMonus` is a `def` and deliberately **not**
an instance: `Bool`, `Prop`, `Set α` and `α → Bool` are all Boolean
algebras in Mathlib, so a global instance would collide with the
catalog's own `𝔹` and `𝔹[X]` instances and would put a second `Add`,
`Mul` and `Sub` on anything else Mathlib happens to make a Boolean
algebra. Types that want it ask for it, as `Security` does below.

What the construction satisfies is everything the properties tables ask
of a semiring at once: both idempotences, absorptivity, exclusivity,
complementedness, left-distributivity of `⊗` over `⊖`, and `δ = id`.
That is the content of the characterization in the semantics paper: among
m-semirings that are lattices, exclusivity *is* being a Boolean algebra
(`monus_one_isCompl`, `monus_one_unique_compl`).
-/

namespace BooleanAlgebra

variable {α : Type} [BooleanAlgebra α]

/-- The commutative semiring of a Boolean algebra: join for `⊕`, meet
for `⊗`. Separated from the m-semiring below so that the numerals and
the natural-number cast are available while the monus part is built. -/
@[instance_reducible]
def toCommSemiring : CommSemiring α where
  add := (· ⊔ ·)
  zero := ⊥
  mul := (· ⊓ ·)
  one := ⊤
  nsmul := fun n a => if n = 0 then ⊥ else a
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun n a => by
    cases n with
    | zero => show (if 1 = 0 then ⊥ else a) = (if 0 = 0 then ⊥ else a) ⊔ a
              simp
    | succ k => show (if k + 2 = 0 then ⊥ else a)
                  = (if k + 1 = 0 then ⊥ else a) ⊔ a
                simp
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  mul_assoc := inf_assoc
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  left_distrib := inf_sup_left
  right_distrib := inf_sup_right
  zero_mul := bot_inf_eq
  mul_zero := inf_bot_eq
  mul_comm := inf_comm

section Cast

attribute [local instance] BooleanAlgebra.toCommSemiring

/-- Every positive natural-number cast is `𝟙`, join being idempotent. -/
theorem natCast_pos {n : ℕ} (hn : 0 < n) : ((n : α)) = (1 : α) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ k ih =>
    rw [Nat.cast_succ]
    cases Nat.eq_zero_or_pos k with
    | inl hk => rw [hk]; show (0 : α) + 1 = 1; rw [zero_add]
    | inr hk => rw [ih hk]; show (1 : α) + 1 = 1; exact sup_idem _

end Cast

/-- **Every Boolean algebra is an m-semiring****: join for `⊕`, meet for
`⊗`, the difference for the monus, and the identity for `δ`. A `def` and
not an instance, for the reason in this file's header. -/
@[instance_reducible]
def toSemiringWithMonus : SemiringWithMonus α :=
  letI := BooleanAlgebra.toCommSemiring (α := α)
  { sub := (· \ ·)
    add_le_add_left := fun _ _ h c => sup_le_sup_right h c
    exists_add_of_le := fun {_ b} h => ⟨b, (sup_eq_right.mpr h).symm⟩
    le_self_add := fun _ _ => le_sup_left
    le_add_self := fun _ _ => le_sup_right
    monus_spec := fun _ _ _ => sdiff_le_iff
    delta := id
    delta_zero := rfl
    delta_natCast_pos := fun hn => BooleanAlgebra.natCast_pos hn
    delta_absorb := fun _ _ => inf_sup_self }


section Properties

attribute [local instance] BooleanAlgebra.toCommSemiring
attribute [local instance] BooleanAlgebra.toSemiringWithMonus

/-- `⊕` is idempotent: it is a join. -/
theorem idempotent_add : idempotent α := fun _ => sup_idem _

/-- `⊗` is idempotent too: it is a meet. -/
theorem mul_idempotent : ∀ a : α, a * a = a := fun _ => inf_idem _

/-- **Absorptive**: `𝟙` is the top. -/
theorem absorptive_of : absorptive α := fun _ => top_sup_eq _

/-- **Exclusive**: `𝟙 ⊖ a` is the complement, which meets `a` at `𝟘`. -/
theorem exclusive_of : exclusive α := fun a => by
  show a ⊓ (⊤ \ a) = ⊥
  simp

/-- **Complemented**: De Morgan. -/
theorem complemented_of : complemented α := fun a b => by
  show ⊤ \ (a ⊔ b) = (⊤ \ a) ⊓ (⊤ \ b)
  simp

/-- **`⊗` distributes over `⊖`**, which is `a ⊓ (b ⊓ cᶜ) = (a ⊓ b) ⊓ (a ⊓ c)ᶜ`
read through the lattice: the condition the decompositions of the
semantics paper ask for. -/
theorem mul_sub_left_distributive_of : mul_sub_left_distributive α := by
  intro a b c
  show a ⊓ (b \ c) = (a ⊓ b) \ (a ⊓ c)
  rw [sdiff_eq, sdiff_eq, compl_inf, inf_sup_left,
    show (a ⊓ b) ⊓ aᶜ = ⊥ from by
      rw [inf_right_comm]
      simp,
    bot_sup_eq, inf_assoc]

/-- **`δ` is the identity**, and legally so: the lattice absorption law
is what `IsLegalDelta` asks of it, and every positive cast is `𝟙`. -/
theorem isLegalDelta_id_of : IsLegalDelta (id : α → α) :=
  { zero := rfl
    natCast_pos := fun hn => BooleanAlgebra.natCast_pos hn
    absorb := fun _ _ => inf_sup_self }

theorem isDelta_id_of : IsDelta (id : α → α) := isDelta_delta

/-- The nested-coherence condition: a value meets the complement of its
own `δ` at `𝟘`, which for `δ = id` is exclusivity again. -/
theorem nested_coherent_of (a : α) :
    a * (1 - SemiringWithMonus.delta a) = 0 := exclusive_of a

end Properties

end BooleanAlgebra

/-! ## The security semiring

`S′ L` is the construction at `Set L`: a tuple is annotated with the set
of clearance levels at which it may be seen, `⊕` collects levels, `⊗`
requires them, and the monus removes them. Its own type keeps the
construction's `Add`, `Mul` and `Sub` off `Set L` itself, where Mathlib's
would clash. -/

/-- **The alternative security semiring** `S′ = 𝔹^L`: the subsets of a
set `L` of clearance levels. -/
def Security (L : Type) := Set L

namespace Security

instance {L : Type} : BooleanAlgebra (Security L) :=
  inferInstanceAs (BooleanAlgebra (Set L))

instance {L : Type} : Membership L (Security L) :=
  inferInstanceAs (Membership L (Set L))

noncomputable instance {L : Type} : CommSemiring (Security L) :=
  BooleanAlgebra.toCommSemiring

noncomputable instance {L : Type} : SemiringWithMonus (Security L) :=
  BooleanAlgebra.toSemiringWithMonus

noncomputable instance {L : Type} : CommSemiringWithMonus (Security L) where
  mul_comm := inf_comm

/-- The levels at which a tuple annotated `a` may be seen. -/
theorem mem_add {L : Type} (a b : Security L) (x : L) :
    x ∈ (a + b : Security L) ↔ x ∈ a ∨ x ∈ b := Iff.rfl

/-- A tuple of a join is visible at a level iff both its sides are. -/
theorem mem_mul {L : Type} (a b : Security L) (x : L) :
    x ∈ (a * b : Security L) ↔ x ∈ a ∧ x ∈ b := Iff.rfl

/-- And a difference removes the levels of the subtrahend. -/
theorem mem_sub {L : Type} (a b : Security L) (x : L) :
    x ∈ (a - b : Security L) ↔ x ∈ a ∧ x ∉ b := Iff.rfl

theorem absorptive {L : Type} : _root_.absorptive (Security L) :=
  BooleanAlgebra.absorptive_of

theorem exclusive {L : Type} : _root_.exclusive (Security L) :=
  BooleanAlgebra.exclusive_of

theorem complemented {L : Type} : _root_.complemented (Security L) :=
  BooleanAlgebra.complemented_of

theorem idempotent {L : Type} : _root_.idempotent (Security L) :=
  BooleanAlgebra.idempotent_add

theorem mul_idempotent {L : Type} : ∀ a : Security L, a * a = a :=
  BooleanAlgebra.mul_idempotent

theorem mul_sub_left_distributive {L : Type} :
    _root_.mul_sub_left_distributive (Security L) :=
  BooleanAlgebra.mul_sub_left_distributive_of

end Security
