/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.SemiringWithMonus
public import Provenance.Semirings.Bool
public import Mathlib.Order.PrimeSeparator
import Mathlib.Order.Hom.Lattice
import all Provenance.SemiringWithMonus

/-!
# Lattice and Boolean m-semirings, and their points

The m-semirings in which `⊕` and `⊗` are a bounded distributive lattice,
those in which `𝟙 ⊖ ·` is moreover a complement, and the homomorphisms
onto `𝔹` that separate the elements of either.

`IsLatticeSemiring K` says that `K` is absorptive (`𝟙 ⊕ a = 𝟙`, which
gives `a ⊕ a = a` and `a ⊕ a ⊗ b = a`) and that `⊗` is idempotent. That
is what makes `(K, ⊕, ⊗)` a bounded distributive lattice *for the natural
order of `K`*: `IsLatticeSemiring.distribLattice` and
`IsLatticeSemiring.boundedOrder` build the structures on the order `K`
already carries, with `⊔ = ⊕`, `⊓ = ⊗`, `⊥ = 𝟘` and `⊤ = 𝟙`.
`IsBooleanSemiring K` adds exclusivity, `a ⊗ (𝟙 ⊖ a) = 𝟘`, under which
`𝟙 ⊖ ·` is the complement (`monus_one_isCompl`) and the monus is
`a ⊖ b = a ⊗ (𝟙 ⊖ b)` (`IsBooleanSemiring.monus_eq_mul_one_monus`).

A *point* of `K` is a semiring homomorphism `K →+* 𝔹`. Over a lattice
m-semiring the points separate the elements
(`IsLatticeSemiring.exists_point_ne`, off Mathlib's prime separation
theorem for distributive lattices): two elements agreeing at every point
are equal (`IsLatticeSemiring.eq_of_forall_point`). Over a Boolean
m-semiring a point preserves the monus as well
(`IsBooleanSemiring.map_monus`), and when `δ` is the identity it is an
m-semiring homomorphism (`IsBooleanSemiring.pointHom`). These are what
the extensionality theorem of `Provenance.Extensionality` uses: the
annotation of a tuple is determined by its images at the points, and each
image is a plain evaluation.
-/

@[expose] public section

variable {K : Type} [CommSemiringWithMonus K]

/-! ## Lattice m-semirings -/

/-- **A lattice m-semiring**: absorptive, with an idempotent `⊗`. These
are the m-semirings in which `(K, ⊕, ⊗)` is a bounded distributive
lattice, `𝟘` its bottom and `𝟙` its top. -/
structure IsLatticeSemiring (K : Type) [CommSemiringWithMonus K] : Prop where
  /-- `𝟙 ⊕ a = 𝟙`. -/
  absorptive : absorptive K
  /-- `a ⊗ a = a`. -/
  mulIdempotent : mulIdempotent K

/-- **A Boolean m-semiring**: a lattice m-semiring that is exclusive, so
that `𝟙 ⊖ a` is the complement of `a`. -/
structure IsBooleanSemiring (K : Type) [CommSemiringWithMonus K] : Prop
    extends IsLatticeSemiring K where
  /-- `a ⊗ (𝟙 ⊖ a) = 𝟘`. -/
  exclusive : exclusive K

namespace IsLatticeSemiring

/-- `⊕` is idempotent. -/
theorem idempotent (h : IsLatticeSemiring K) : idempotent K :=
  idempotent_of_absorptive h.absorptive

/-- The order of `K` is `a ≤ b ↔ a ⊕ b = b`. -/
theorem le_iff (h : IsLatticeSemiring K) (a b : K) : a ≤ b ↔ a + b = b :=
  le_iff_add_eq h.idempotent a b

/-- Multiplication is monotone in both arguments. -/
theorem mul_le_mul (_h : IsLatticeSemiring K) {a b c d : K} (hab : a ≤ b)
    (hcd : c ≤ d) : a * c ≤ b * d :=
  calc a * c ≤ a * d := mul_le_mul_left_of_le hcd a
    _ = d * a := mul_comm a d
    _ ≤ d * b := mul_le_mul_left_of_le hab d
    _ = b * d := mul_comm d b

/-- **The lattice on the natural order**: `⊔` is `⊕` and `⊓` is `⊗`. -/
@[instance_reducible] private noncomputable def lattice (h : IsLatticeSemiring K) : Lattice K :=
  { (inferInstance : PartialOrder K) with
    sup := (· + ·)
    inf := (· * ·)
    le_sup_left := fun _ _ => le_self_add
    le_sup_right := fun _ _ => le_add_self
    sup_le := fun a b c hac hbc => by
      show a + b ≤ c
      calc a + b ≤ c + c := add_le_add hac hbc
        _ = c := h.idempotent c
    inf_le_left := fun a b => by
      show a * b ≤ a
      rw [mul_comm]
      exact mul_le_right h.absorptive b a
    inf_le_right := fun a b => mul_le_right h.absorptive a b
    le_inf := fun a b c hab hac => by
      show a ≤ b * c
      calc a = a * a := (h.mulIdempotent a).symm
        _ ≤ b * c := h.mul_le_mul hab hac }

/-- **And it is distributive**, `⊗` distributing over `⊕` by the semiring
law. -/
@[instance_reducible] private noncomputable def distribLattice (h : IsLatticeSemiring K) : DistribLattice K :=
  letI := h.lattice
  DistribLattice.ofInfSupLe (fun a b c => by
    show a * (b + c) ≤ a * b + a * c
    rw [mul_add])

/-- **Bounded by `𝟘` and `𝟙`.** -/
@[instance_reducible] private noncomputable def boundedOrder (h : IsLatticeSemiring K) : BoundedOrder K :=
  { bot := 0
    bot_le := fun _ => zero_le
    top := 1
    le_top := le_one_of_absorptive h.absorptive }

/-! ### Points

A point is a semiring homomorphism `K →+* 𝔹`. Each proper prime ideal
`J` of the lattice gives one, `a ↦ [a ∉ J]`: the complement of a prime
ideal is closed under `⊓`, and the complement of an ideal is upward
closed and closed under the two sides of a `⊔`. -/

open Classical in
/-- **The point of a prime ideal**: `a ↦ [a ∉ J]`. The ideal is one of
the natural order of `K`, which is the order of the lattice. -/
private noncomputable def pointOfPrime (h : IsLatticeSemiring K)
    (J : Order.Ideal K) (hJ : J.IsPrime) : K →+* Bool :=
  letI := h.lattice
  letI := h.boundedOrder
  haveI : Order.Ideal.IsProper J := hJ.toIsProper
  { toFun := fun a => decide (a ∉ J)
    map_one' := by
      show decide ((1 : K) ∉ J) = true
      exact decide_eq_true (Order.Ideal.IsProper.top_notMem (I := J) inferInstance)
    map_mul' := fun x y => by
      show decide (x * y ∉ J) = (decide (x ∉ J) && decide (y ∉ J))
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_iff, Bool.and_eq_true]
      refine ⟨fun hxy => ⟨fun hx => hxy (J.lower ?_ hx),
        fun hy => hxy (J.lower ?_ hy)⟩, fun hxy hm => ?_⟩
      · exact (mul_le_right h.absorptive y x).trans_eq' (mul_comm y x)
      · exact mul_le_right h.absorptive x y
      · rcases hJ.mem_or_mem (x := x) (y := y) hm with hx | hx
        · exact hxy.1 hx
        · exact hxy.2 hx
    map_zero' := by
      show decide ((0 : K) ∉ J) = false
      exact decide_eq_false (not_not.mpr (Order.Ideal.bot_mem J))
    map_add' := fun x y => by
      show decide (x + y ∉ J) = (decide (x ∉ J) || decide (y ∉ J))
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_iff, Bool.or_eq_true]
      rw [show x + y = x ⊔ y from rfl, Order.Ideal.sup_mem_iff]
      tauto }

/-- **The points separate the elements**: two distinct elements of a
lattice m-semiring differ at some point. One of the two is not below the
other, so the principal filter of the first and the principal ideal of
the second are disjoint, and a prime ideal extending the ideal and
avoiding the filter gives a point true on the first and false on the
second. -/
theorem exists_point_ne (h : IsLatticeSemiring K) {a b : K} (hab : a ≠ b) :
    ∃ f : K →+* Bool, f a ≠ f b := by
  classical
  let _ := h.distribLattice
  let _ := h.boundedOrder
  -- a point false on `y` and true on `x`, whenever `¬ x ≤ y`
  have sep : ∀ {x y : K}, ¬ x ≤ y → ∃ f : K →+* Bool, f x = true ∧ f y = false := by
    intro x y hxy
    have hdisj : Disjoint ((Order.PFilter.principal x : Order.PFilter K) : Set K)
        ((Order.Ideal.principal y : Order.Ideal K) : Set K) := by
      rw [Set.disjoint_left]
      intro z hzF hzI
      exact hxy (le_trans (Order.PFilter.mem_principal.mp hzF)
        (Order.Ideal.mem_principal.mp hzI))
    obtain ⟨J, hJ, hIJ, hFJ⟩ :=
      DistribLattice.prime_ideal_of_disjoint_filter_ideal hdisj
    refine ⟨h.pointOfPrime J hJ, ?_, ?_⟩
    · show decide (x ∉ J) = true
      rw [decide_eq_true_iff]
      exact fun hx => Set.disjoint_left.mp hFJ (Order.PFilter.mem_principal.mpr le_rfl) hx
    · show decide (y ∉ J) = false
      rw [decide_eq_false_iff_not, not_not]
      exact hIJ (Order.Ideal.mem_principal.mpr le_rfl)
  by_cases hle : a ≤ b
  · have hlt : ¬ b ≤ a := fun hba => hab (le_antisymm hle hba)
    obtain ⟨f, hfb, hfa⟩ := sep hlt
    exact ⟨f, by rw [hfa, hfb]; decide⟩
  · obtain ⟨f, hfa, hfb⟩ := sep hle
    exact ⟨f, by rw [hfa, hfb]; decide⟩

/-- **Two elements agreeing at every point are equal.** -/
theorem eq_of_forall_point (h : IsLatticeSemiring K) {a b : K}
    (hf : ∀ f : K →+* Bool, f a = f b) : a = b := by
  by_contra hab
  obtain ⟨f, hne⟩ := h.exists_point_ne hab
  exact hne (hf f)

end IsLatticeSemiring

/-! ## Boolean m-semirings -/

namespace IsBooleanSemiring

/-- **The monus of a Boolean m-semiring is `a ⊗ (𝟙 ⊖ b)`**: the meet with
the complement, which residuation determines. -/
theorem monus_eq_mul_one_monus (h : IsBooleanSemiring K) (a b : K) :
    a - b = a * (1 - b) := by
  refine le_antisymm ?_ ?_
  · rw [SemiringWithMonus.monus_spec]
    let _ := h.toIsLatticeSemiring.distribLattice
    have hdist : b + a * (1 - b) = (b + a) * (b + (1 - b)) :=
      sup_inf_left b a (1 - b)
    rw [hdist, add_one_monus_eq_one_of_absorptive h.absorptive, mul_one]
    exact le_add_self
  · calc a * (1 - b) ≤ (b + (a - b)) * (1 - b) := by
          rw [mul_comm, mul_comm (b + (a - b))]
          exact mul_le_mul_left_of_le (le_plus_monus a b) _
      _ = b * (1 - b) + (a - b) * (1 - b) := add_mul _ _ _
      _ = (a - b) * (1 - b) := by rw [h.exclusive b, zero_add]
      _ = (1 - b) * (a - b) := mul_comm _ _
      _ ≤ a - b := mul_le_right h.absorptive _ _

omit [CommSemiringWithMonus K] in
/-- In `𝔹`, a complement is a negation. -/
private theorem Bool.eq_not_of_sup_inf {x y : Bool} (hsup : (x || y) = true)
    (hinf : (x && y) = false) : y = !x := by
  revert x y
  decide

/-- **A point sends `𝟙 ⊖ b` to the negation of its value at `b`**: the two
join to `𝟙` and meet at `𝟘`, and so do their images. -/
theorem map_one_monus (h : IsBooleanSemiring K) (f : K →+* Bool) (b : K) :
    f (1 - b) = !(f b) := by
  refine Bool.eq_not_of_sup_inf ?_ ?_
  · show f b + f (1 - b) = true
    rw [← map_add, add_one_monus_eq_one_of_absorptive h.absorptive, map_one]
    rfl
  · show f b * f (1 - b) = false
    rw [← map_mul, h.exclusive, map_zero]
    rfl

/-- **A point of a Boolean m-semiring preserves the monus**, the monus of
`𝔹` being `a ∧ ¬ b`. -/
theorem map_monus (h : IsBooleanSemiring K) (f : K →+* Bool) (a b : K) :
    f (a - b) = f a - f b := by
  rw [h.monus_eq_mul_one_monus, map_mul, h.map_one_monus]
  rfl

/-- **A point is an m-semiring homomorphism when `δ` is the identity**,
the `δ` of `𝔹` being the identity too. -/
@[instance_reducible] def pointHom (h : IsBooleanSemiring K) (hδ : ∀ a : K, SemiringWithMonus.delta a = a)
    (f : K →+* Bool) : SemiringWithMonusHom K Bool where
  toRingHom := f
  map_sub := h.map_monus f
  map_delta := fun a => by rw [hδ a]; rfl

/-- The underlying function of `pointHom` is the point. -/
@[simp] theorem pointHom_apply (h : IsBooleanSemiring K)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) (f : K →+* Bool) (a : K) :
    h.pointHom hδ f a = f a := rfl

end IsBooleanSemiring

/-! ## From the two identities to the lattice, and back

The paper states the lattice condition as three identities,
`a ⊕ a = a`, `a ⊗ a = a` and `a ⊕ a ⊗ b = a`; the library's `absorptive`
is `𝟙 ⊕ a = 𝟙`. The absorption law and `absorptive` are equivalent in
every semiring, with no idempotence needed – one is the other at `a = 𝟙`,
and `𝟙 ⊕ b = 𝟙` gives `a ⊕ a ⊗ b = a ⊗ (𝟙 ⊕ b) = a` – and `a ⊕ a = a`
follows from either (`idempotent_of_absorptive`). So the paper's class and
`IsLatticeSemiring` are the same class, which is recorded here so that
either form can be read off the other. -/

/-- **`𝟙 ⊕ a = 𝟙` from the absorption law `a ⊕ a ⊗ b = a`**, at `a = 𝟙`. -/
theorem absorptive_of_add_mul_self (h : ∀ a b : K, a + a * b = a) : absorptive K :=
  fun a => by simpa using h 1 a

/-- **The absorption law from `𝟙 ⊕ a = 𝟙`.** -/
theorem add_mul_self_of_absorptive (h : absorptive K) (a b : K) : a + a * b = a :=
  add_mul_self h a b

/-- **The other absorption law, `a ⊗ (a ⊕ b) = a`**, from distributivity
and the first. -/
theorem IsLatticeSemiring.mul_add_self (h : IsLatticeSemiring K) (a b : K) :
    a * (a + b) = a :=
  _root_.mul_add_self h.absorptive h.mulIdempotent a b

/-- `𝟙` is the top of the natural order. -/
theorem IsLatticeSemiring.le_one (h : IsLatticeSemiring K) (a : K) : a ≤ 1 :=
  le_one_of_absorptive h.absorptive a

end
