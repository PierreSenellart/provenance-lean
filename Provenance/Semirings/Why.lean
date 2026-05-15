import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc

/-!
# Why-provenance m-semiring `Why[X]`

This file defines the *Why* provenance semiring `Why α = Set (Set α)`.
Elements are sets of subsets of `α` (representing sets of witnesses). Addition
is union of families, and multiplication is pairwise union of witnesses.

`Why α` is idempotent but **not** absorptive when `α` is nonempty. It also
does **not** satisfy left-distributivity of multiplication over monus, contradicting
a claim in [Amsterdamer, Deutch & Tannen, *On the limitations of provenance for
queries with differences*, Table on p. 4][amsterdamer2011limitations].

## References

* [Amsterdamer, Deutch & Tannen, *On the limitations of provenance for queries with differences*][amsterdamer2011limitations]
-/

@[ext]
structure Why (α: Type) where
  carrier : Set (Set α)

instance : Coe (Why α) (Set (Set α)) := ⟨Why.carrier⟩

instance : Zero (Why α) where
  zero := ⟨∅⟩

instance : Add (Why α) where
  add a b := ⟨a ∪ b⟩

def why_mul (a b: Why α) : Why α := ⟨{ z : Set α | ∃ x y : Set α, x ∈ a.carrier ∧ y ∈ b.carrier ∧ z = x ∪ y}⟩

instance : CommSemiring (Why α) where
  one := ⟨{∅}⟩
  mul := why_mul

  add_assoc := by
    intro a b c
    simp [HAdd.hAdd, Add.add]
    exact Set.union_assoc _ _ _

  zero_add := by
    intro a
    show ⟨(⟨∅⟩ : Why α).carrier ∪ a.carrier⟩ = a
    simp

  add_zero := by
    intro a
    show ⟨a.carrier ∪ (⟨∅⟩ : Why α).carrier⟩ = a
    simp

  add_comm := by
    intro a b
    simp [HAdd.hAdd, Add.add]
    exact Set.union_comm _ _

  mul_assoc := by
    intro a b c
    unfold why_mul
    ext w
    simp [HMul.hMul]
    apply Iff.intro
    . intro h
      obtain ⟨xa, xb, h₁, h₂⟩ := h
      obtain ⟨hxa, hxb⟩ := h₁
      obtain ⟨xc, hxc, hw⟩ := h₂
      use xa, hxa, xb, xc
      constructor
      . use hxb, hxc
      . simp[hw, Set.union_assoc]

    . intro h
      obtain ⟨xa, hxa, xb, xc, hxbc, hw⟩ := h
      use xa, xb
      constructor
      . use hxa, hxbc.1
      . use xc, hxbc.2
        simp[hw, Set.union_assoc]

  one_mul := by
    intro a
    show why_mul (⟨{∅}⟩: Why α) a = a
    unfold why_mul
    simp

  mul_one := by
    intro a
    show why_mul a (⟨{∅}⟩: Why α) = a
    unfold why_mul
    simp

  zero_mul := by
    intro a
    show why_mul (⟨∅⟩: Why α) a = (⟨∅⟩: Why α)
    unfold why_mul
    simp

  mul_zero := by
    intro a
    show why_mul a (⟨∅⟩: Why α) = (⟨∅⟩: Why α)
    unfold why_mul
    simp

  mul_comm := by
    intro a b
    show why_mul a b = why_mul b a
    unfold why_mul
    ext z
    simp
    apply Iff.intro
    . intro h
      obtain ⟨x, hx, y, hy, hz⟩ := h
      use y, hy, x, hx
      simp[hz, Set.union_comm]
    . intro h
      obtain ⟨y, hy, x, hx, hz⟩ := h
      use x, hx, y, hy
      simp[hz, Set.union_comm]

  left_distrib := by
    intro a b c
    show why_mul a ⟨b ∪ c⟩ = ⟨(why_mul a b) ∪ (why_mul a c)⟩
    unfold why_mul
    ext z
    simp
    apply Iff.intro
    . intro h
      obtain ⟨x, hx, y, hy, hz⟩ := h
      cases hy with
      | inl hy' =>
        left
        use x, hx, y, hy'
      | inr hy' =>
        right
        use x, hx, y, hy'
    . intro h
      cases h with
      | inl h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x, hx, y
        simp[hy, hz]
      | inr h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x, hx, y
        simp[hy, hz]

  right_distrib := by
    intro a b c
    show why_mul ⟨a ∪ b⟩ c = ⟨(why_mul a c) ∪ (why_mul b c)⟩
    unfold why_mul
    simp
    ext z
    simp
    apply Iff.intro
    . intro h
      obtain ⟨x, hx, y, hy, hz⟩ := h
      cases hx with
      | inl hx' =>
        left
        use x, hx', y, hy
      | inr hx' =>
        right
        use x, hx', y, hy
    . intro h
      cases h with
      | inl h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x
        simp[hx]
        use y
      | inr h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x
        simp[hx]
        use y

  nsmul := nsmulRec

instance : SemiringWithMonus (Why α) where
  le a b := a.carrier ⊆ b.carrier
  le_refl := by simp
  le_trans := by
    intro a b c ha hb x hx
    exact hb (ha hx)

  le_antisymm := by
    intro a b ha hb
    ext x
    apply Iff.intro
    . exact fun a ↦ ha (hb (ha a))
    . exact fun a ↦ hb (ha (hb a))

  add_le_add_left := by
    simp[HAdd.hAdd,Add.add]
    intro a b hab c x hx
    simp
    left
    exact hab hx

  add_le_add_right := by
    simp[HAdd.hAdd,Add.add]
    intro a b hab c x hx
    simp
    right
    exact hab hx

  exists_add_of_le := by
    intro a b hab
    simp[HAdd.hAdd,Add.add]
    use ⟨b.carrier \ a.carrier⟩
    ext x
    simp
    intro hx
    exact hab hx

  le_self_add := by
    intro a b x hx
    simp[HAdd.hAdd,Add.add]
    left
    exact hx

  le_add_self := by
    intro a b x hx
    simp[HAdd.hAdd,Add.add]
    right
    exact hx

  sub a b := ⟨a.carrier \ b.carrier⟩
  monus_spec := by
    intro a b c
    simp[HAdd.hAdd,Add.add]
    change (⟨a.carrier \ b.carrier⟩: Why α).carrier ⊆ c.carrier ↔ a.carrier ⊆ b.carrier ∪ c.carrier
    apply Iff.intro
    . intro h x hx
      by_cases hx' : x ∈ b.carrier
      . left
        exact hx'
      . right
        have h' : x ∈ a.carrier \ b.carrier := by simp[hx, hx']
        exact h h'
    . intro h x hx
      simp at hx
      obtain ⟨ha, hb⟩ := hx
      have h' : x ∈ b.carrier ∪ c.carrier := h ha
      simp at h'
      tauto

  /- δ matches ProvSQL's `Why::delta`: identity on `Why α` (the C++ form
  `x.empty() ? zero() : x` collapses to the identity since `zero = ⟨∅⟩`). -/
  delta := id
  delta_zero := rfl
  delta_natCast_pos := by
    have hidem : idempotent (Why α) := fun a => by simp [(· + ·), Add.add]
    intro n hn
    exact natCast_pos_eq_one_of_idempotent hidem hn

theorem Why.idempotent : idempotent (Why α) := by
  intro a
  simp[(· + ·), Add.add]

instance : Nontrivial (Why α) := ⟨0, 1, fun h => by
  have h' : (⟨∅⟩ : Why α) = ⟨{∅}⟩ := h
  injection h' with h''
  exact Set.singleton_ne_empty _ h''.symm⟩

/-- `Why α` has characteristic 0 in the `CharP` sense: it is idempotent and
nontrivial (`⟨∅⟩ ≠ ⟨{∅}⟩`), so every positive natural-number cast equals `1`. -/
instance Why.instCharPZero : CharP (Why α) 0 :=
  CharP.zero_of_idempotent Why.idempotent

theorem Why.not_absorptive (hNotEmpty: ∃ (_: α), ⊤) : ¬(absorptive (Why α)) := by
  rcases hNotEmpty with ⟨x, _⟩
  simp
  use ⟨{{x}}⟩
  simp[(· + ·), Add.add, insert, Set.insert]
  intro h
  have h' := congrArg Why.carrier h
  have hone: (1: Why α).1=({∅}: Set (Set α)) := by
    rfl
  rw[hone] at h'
  simp at h'
  have := congrArg (fun S => {x} ∈ S) h'
  simp at this

/-- In Why[X], as long as X is non-empty, times is not distributive over
  monus. Note that this contradicts [Amsterdamer, Deutch & Tannen, *On
  the limitations of provenance for queries with differences*, table page
  4][amsterdamer2011limitations], which claims this semiring satisfies
  axiom A13. -/
theorem Why.not_mul_sub_left_distributive [Inhabited α] :
  ¬(mul_sub_left_distributive (Why α)) := by
  simp
  have x := (default: α)
  use ⟨{{x}}⟩, ⟨{∅}⟩, ⟨{{x}}⟩
  simp[(· * ·),Mul.mul,why_mul,(· - ·),Sub.sub]

/-- There is no semiring homomorphism from `BoolFunc Y` to `Why α` (with `α`
inhabited) sending the variables to arbitrary values: `Why α` is not
absorptive (`Why.not_absorptive`), which contradicts `var i + 1 = 1` in
`BoolFunc Y`. -/
theorem Why.no_hom_from_BoolFunc {Y : Type} [Inhabited Y] [Inhabited α] :
    ∃ ν : Y → Why α,
      ¬ ∃ φ : BoolFunc Y →+* Why α, ∀ i : Y, φ (BoolFunc.var i) = ν i :=
  BoolFunc.no_hom_of_not_absorptive (Why.not_absorptive ⟨default, trivial⟩)
