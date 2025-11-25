import Provenance.SemiringWithMonus
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic

section Which

variable {α: Type} [DecidableEq α]

inductive Which (α: Type) where
  | wset : Finset α → Which α
  | wbot : Which α
open Which

instance : Zero (Which α) := ⟨wbot⟩

instance : Add  (Which α) := ⟨λ a b =>
  match a with
  | wbot   => b
  | wset sa => match b with
    | wbot => wset sa
    | wset sb => wset (sa ∪ sb)⟩

instance : Mul  (Which α) := ⟨λ a b =>
  match a with
  | wbot => wbot
  | wset sa => match b with
    | wbot => wbot
    | wset sb => wset (sa ∪ sb)⟩

instance : One  (Which α) := ⟨wset ∅⟩

instance : Sub  (Which α) := ⟨λ a b =>
  match a with
    | wbot => wbot
    | wset sa => match b with
      | wbot => wset sa
      | wset sb => if sa ⊆ sb then wbot else wset (sa \ sb)⟩

instance : LE   (Which α) := ⟨λ a b =>
  match a with
    | wbot => True
    | wset sa => match b with
      | wbot => False
      | wset sb => sa ⊆ sb⟩


instance : CommSemiring (Which α) where
  add_assoc := by
    intro a b c
    simp [(· + ·), Add.add]
    match a with
    | wbot => simp
    | wset sa => match b with
      | wbot => simp
      | wset sb => match c with
        | wbot => simp
        | wset sc =>
          simp[Finset.union_assoc]

  zero_add := by
    intro a
    simp [(· + ·), Add.add]

  add_zero := by
    intro a
    simp [(· + ·), Add.add]
    match a with
    | wbot => rfl
    | wset sa => simp

  add_comm := by
    intro a b
    simp [(· + ·), Add.add]
    cases a <;> cases b <;>
      simp; exact Finset.union_comm _ _

  mul_assoc := by
    intro a b c
    simp [(· * ·),Mul.mul]
    cases a <;> cases b <;> cases c <;> simp

  one_mul := by
    intro a
    simp [(· * ·),Mul.mul]
    cases a <;> simp

  mul_one := by
    intro a
    simp [(· * ·),Mul.mul]
    cases a <;> simp

  zero_mul := by
    intro a
    simp [(· * ·),Mul.mul]
    cases a <;> rfl

  mul_zero := by
    intro a
    simp [(· * ·),Mul.mul]
    cases a <;> simp <;> rfl

  mul_comm := by
    intro a b
    simp [(· * ·),Mul.mul]
    cases a <;> cases b <;> simp
    exact Finset.union_comm _ _

  left_distrib := by
    intro a b c
    simp [(· + ·),(· * ·),Add.add,Mul.mul]
    cases a <;> cases b <;> cases c <;> simp
    rename_i x y z
    ext u
    simp
    tauto

  right_distrib := by
    intro a b c
    simp [(· + ·),(· * ·),Add.add,Mul.mul]
    cases a <;> cases b <;> cases c <;> simp
    rename_i x y z
    ext u
    simp
    tauto

  nsmul := nsmulRec

instance : PartialOrder (Which α) where
  le_refl := by
    intro a
    simp[(· ≤ ·)]
    cases a <;> simp

  le_trans := by
    intro a b c
    simp[(· ≤ ·)]
    cases a <;> cases b <;> cases c <;> simp
    rename_i x y z
    intro hxy hyz u hu
    exact hyz (hxy hu)

  le_antisymm := by
    intro a b
    simp[(· ≤ ·)]
    cases a <;> cases b <;> simp
    exact Finset.Subset.antisymm

instance : CanonicallyOrderedAdd (Which α) where
  exists_add_of_le := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]
    cases a <;> cases b <;> simp
    . rename_i sa sb
      intro hab
      use wset (sb \ sa)
      simp
      assumption

  le_self_add := by
    intro a b
    cases a <;> cases b <;> simp [(· ≤ ·)]

  le_add_self := by
    intro a b
    cases a <;> cases b <;> simp [(· ≤ ·)]

instance : IsOrderedAddMonoid (Which α) where
  add_le_add_left := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]
    cases a <;> cases b <;> intro h c <;> cases c <;> simp <;> simp at h
    . rename_i x y z
      exact Finset.union_subset_union_left h
    . assumption

  add_le_add_right := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]
    cases a <;> cases b <;> intro h c <;> cases c <;> simp <;> simp at h
    . rename_i x y z
      exact Finset.union_subset_union_right h
    . assumption

instance : SemiringWithMonus (Which α) where
  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· - ·),Sub.sub,(· ≤ ·)]
    cases ha : a <;> rename_i sa <;> cases hb : b <;> cases hc : c <;> simp
    . rename_i sb sc
      by_cases h' : sa ⊆ sb <;> simp[h']
      . intro x hx
        exact Finset.mem_union_left sc (h' hx)
      . apply Iff.intro
        . intro h₁ x hx
          by_cases hxb : x ∈ sb
          . exact Finset.mem_union_left sc hxb
          . simp[hxb]
            have hx₁ : x ∈ sa \ sb := by
              simp[hx,hxb]
            exact h₁ hx₁
        . intro h₁ x hx
          simp at hx
          have hx₁ : x ∈ sa := by
            simp[hx]
          have : x ∈ sb ∪ sc := h₁ hx₁
          simp[hx] at this
          assumption
    . rename_i sb
      by_cases h' : sa ⊆ sb <;> simp[h']


/-- Which[X] is not absorptive as long as there is at least one variable -/
theorem Which.not_absorptive (h: ∃ (x: α), ⊤) : ¬(absorptive (Which α)) := by
  rcases h with ⟨x, hx⟩
  simp
  use wset {x}
  simp[(· + ·), Add.add]
  have : wset ∅ = (1: Which α) := by
    rfl
  rw[← this]
  simp

/-- Which[∅] is absorptive -/
theorem Which.absorptive (h: IsEmpty α): absorptive (Which α) := by
  intro x
  simp[(· + ·), Add.add]
  cases hx: x
  . rename_i a
    have : a = ∅ := by
      exact Finset.eq_empty_of_isEmpty a
    simp[this]
    rfl
  . rfl

theorem Which.idempotent : idempotent (Which α) := by
  intro a
  simp[(· + ·), Add.add]
  cases ha: a <;> simp
