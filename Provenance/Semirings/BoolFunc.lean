import Provenance.SemiringWithMonus

/-!
# Boolean-function m-semiring `Bool[X]`

This file defines the semiring `BoolFunc X` of Boolean functions over a set `X` of
Boolean variables. Concretely, `BoolFunc X = (X → Bool) → Bool`: elements are functions
from Boolean assignments to Booleans, with pointwise operations.

Addition is pointwise `||`, multiplication is pointwise `&&`, and the natural order
is `f ≤ g ↔ ∀ a, f a → g a` (pointwise implication).

`BoolFunc X` is absorptive, idempotent, and left-distributive.

This semiring is used in
[Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance] and
surveyed in [Senellart, *Provenance and Probabilities in Relational Databases*][senellart2017provenance].

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Senellart, *Provenance and Probabilities in Relational Databases*][senellart2017provenance]
-/

/-- The type of Boolean functions over Boolean assignments to `X`:
`(X → Bool) → Bool` with pointwise operations. -/
def BoolFunc (X : Type) := (X → Bool) → Bool


instance : Zero (BoolFunc X) := ⟨λ _ ↦ False⟩
instance : Add  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) || (f₂ ν)⟩
instance : One  (BoolFunc X) := ⟨λ _ ↦ True⟩
instance : Mul  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && (f₂ ν)⟩
instance : LE   (BoolFunc X) := ⟨λ f₁ f₂ ↦ ∀ ν : X → Bool, (f₁ ν) ≤ (f₂ ν)⟩
instance : Sub  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && !(f₂ ν)⟩


instance : CommSemiring (BoolFunc X) where
  add_assoc := by
    intro a b c
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_assoc _ _ _

  add_comm := by
    intro a b
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_comm _ _

  zero_add := by tauto

  add_zero := by
    simp[(· + ·),Add.add]
    intro a
    apply funext
    simp
    tauto

  nsmul := nsmulRec

  left_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_left _ _ _

  right_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_right _ _ _

  zero_mul := by tauto

  mul_zero := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto

  mul_assoc := by
    intro a b c
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_assoc _ _ _

  mul_comm := by
    intro a b
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_comm _ _

  one_mul := by tauto

  mul_one := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto


/-- `BoolFunc X` is a commutative m-semiring with pointwise `||` as addition,
pointwise `&&` as multiplication, and pointwise implication as natural order. -/
instance : SemiringWithMonus (BoolFunc X) where
  -- natural order
  le_refl := by tauto

  le_trans := by tauto

  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    apply funext
    intro ν
    exact Bool.le_antisymm (hab ν) (hba ν)

  le_self_add := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  le_add_self := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  add_le_add_left := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  exists_add_of_le := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    intro a b h
    use b
    apply funext
    intro x
    cases ha : a x
    . tauto
    . apply (h x) ha

  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· ≤ ·),(· - ·),Sub.sub]
    apply Iff.intro
    . intro h ν ha
      cases hb : b ν <;> simp
      . exact h ν ha hb
    . intro h ν ha hb
      have h' : b ν = true ∨ c ν = true := h ν ha
      simp[hb] at h'
      exact h'

  /- δ matches ProvSQL's `BoolExpr::delta`: the identity. -/
  delta := id
  delta_zero := rfl
  delta_natCast_pos := by
    have hidem : idempotent (BoolFunc X) :=
      idempotent_of_absorptive (fun a => by simp [(· + ·), Add.add]; congr)
    intro n hn
    exact natCast_pos_eq_one_of_idempotent hidem hn

theorem BoolFunc.absorptive : absorptive (BoolFunc X) := by
  intro a
  simp[(· + ·),Add.add]
  congr

theorem BoolFunc.idempotent : idempotent (BoolFunc X) :=
  idempotent_of_absorptive (BoolFunc.absorptive)

theorem BoolFunc.mul_sub_left_distributive : mul_sub_left_distributive (BoolFunc X) := by
  intro x y z
  simp[(· * ·),Mul.mul,(· - ·),Sub.sub]
  apply funext
  intro ν
  by_cases hx: x ν <;> by_cases hy: y ν <;> by_cases hz: z ν <;> simp[hx,hy,hz]

instance : Nontrivial (BoolFunc X) := ⟨0, 1, by
  intro h
  have : (0 : BoolFunc X) (fun _ => false) = (1 : BoolFunc X) (fun _ => false) := by rw [h]
  exact Bool.false_ne_true this⟩

/-- `BoolFunc X` has characteristic 0 in the `CharP` sense: it is idempotent and
nontrivial, so every positive natural-number cast equals `1`. -/
instance BoolFunc.instCharPZero : CharP (BoolFunc X) 0 :=
  CharP.zero_of_idempotent BoolFunc.idempotent
