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

/-- The `i`-th variable of `BoolFunc X`: the Boolean function that returns the
value of an assignment at `i`. -/
def BoolFunc.var {X : Type} (i : X) : BoolFunc X := fun ν => ν i


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
  delta_natCast_pos :=
    let hidem : idempotent (BoolFunc X) :=
      idempotent_of_absorptive (fun a => by simp [(· + ·), Add.add]; congr)
    fun hn => delta_natCast_pos_id hidem hn
  delta_regrouping := delta_regrouping_id

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

/-! ## Universal property obstructions

The variable functions `BoolFunc.var i` satisfy two algebraic identities in
`BoolFunc X` that constrain the target of any semiring homomorphism:

* `1 + var i = 1` (`BoolFunc.absorptive`)
* `var i * var i = var i` (multiplicative idempotence)

If the target `K` is **not** absorptive (there exists `a : K` with
`1 + a ≠ 1`), assigning that `a` to any variable makes a semiring
homomorphism `BoolFunc X →+* K` impossible. Similarly if `K`'s multiplication
is not idempotent. -/

/-- `BoolFunc.var i * BoolFunc.var i = BoolFunc.var i`. -/
lemma BoolFunc.var_mul_self {X : Type} (i : X) :
    BoolFunc.var i * BoolFunc.var i = BoolFunc.var i := by
  funext τ
  simp [(· * ·), Mul.mul, BoolFunc.var]

/-- `f + (1 - f) = 1` in `BoolFunc X` (Boolean complement on the join side). -/
lemma BoolFunc.add_sub_self {X : Type} (f : BoolFunc X) : f + (1 - f) = 1 := by
  funext τ
  simp [(· + ·), Add.add, (· - ·), Sub.sub]
  have h1 : (1 : BoolFunc X) τ = true := rfl
  rw [h1]
  cases f τ <;> simp

/-- `f * (1 - f) = 0` in `BoolFunc X` (Boolean complement on the meet side). -/
lemma BoolFunc.mul_sub_self {X : Type} (f : BoolFunc X) : f * (1 - f) = 0 := by
  funext τ
  simp [(· * ·), Mul.mul, (· - ·), Sub.sub]
  have h1 : (1 : BoolFunc X) τ = true := rfl
  have h0 : (0 : BoolFunc X) τ = false := rfl
  rw [h1, h0]
  cases f τ <;> simp

/-- If the target `K` is not absorptive, there is no semiring homomorphism
from `BoolFunc X` (with `X` inhabited) sending the variables to arbitrary
values. Picking `ν` constant equal to a witness `a` of `1 + a ≠ 1` blocks
any homomorphism: `var i + 1 = 1` in `BoolFunc X`, so `1 + a = 1` is forced
in `K`. -/
theorem BoolFunc.no_hom_of_not_absorptive {K : Type} [Semiring K]
    {X : Type} [Inhabited X] (hna : ¬ _root_.absorptive K) :
    ∃ ν : X → K, ¬ ∃ φ : BoolFunc X →+* K, ∀ i : X, φ (BoolFunc.var i) = ν i := by
  simp only [_root_.absorptive] at hna
  push Not at hna
  obtain ⟨a, ha⟩ := hna
  refine ⟨fun _ => a, ?_⟩
  rintro ⟨φ, hφ⟩
  have habs : (1 : BoolFunc X) + BoolFunc.var (default : X) = (1 : BoolFunc X) :=
    BoolFunc.absorptive _
  have h1 : φ ((1 : BoolFunc X) + BoolFunc.var (default : X)) = φ 1 := by rw [habs]
  rw [φ.map_add, φ.map_one, hφ default] at h1
  exact ha h1

/-- If the target `K` does not have idempotent multiplication, there is no
semiring homomorphism from `BoolFunc X` (with `X` inhabited) sending the
variables to arbitrary values. Picking `ν` constant equal to a witness `a`
of `a * a ≠ a` blocks any homomorphism, since `var i * var i = var i` in
`BoolFunc X`. -/
theorem BoolFunc.no_hom_of_not_mul_idem {K : Type} [Semiring K]
    {X : Type} [Inhabited X] (hna : ¬ ∀ a : K, a * a = a) :
    ∃ ν : X → K, ¬ ∃ φ : BoolFunc X →+* K, ∀ i : X, φ (BoolFunc.var i) = ν i := by
  push Not at hna
  obtain ⟨a, ha⟩ := hna
  refine ⟨fun _ => a, ?_⟩
  rintro ⟨φ, hφ⟩
  have h1 : φ (BoolFunc.var (default : X) * BoolFunc.var (default : X))
      = φ (BoolFunc.var (default : X)) := by rw [BoolFunc.var_mul_self]
  rw [φ.map_mul, hφ default] at h1
  exact ha h1

/-- For any assignment `ν : X → BoolFunc Y`, the substitution map
`f ↦ (τ ↦ f (fun i => ν i τ))` is an m-semiring homomorphism
`BoolFunc X → BoolFunc Y` sending each variable `BoolFunc.var i` to `ν i`.
This realizes `BoolFunc X` as a “free” object: variables can be sent to
arbitrary Boolean functions. -/
theorem BoolFunc.homomorphism_from_BoolFunc {X Y : Type} :
    ∀ ν : X → BoolFunc Y,
      ∃ h : SemiringWithMonusHom (BoolFunc X) (BoolFunc Y),
        ∀ i : X, h (BoolFunc.var i) = ν i := by
  intro ν
  refine ⟨{
    toFun     := fun f => fun τ => f (fun i => ν i τ)
    map_zero' := rfl
    map_one'  := rfl
    map_add'  := by intro a b; rfl
    map_mul'  := by intro a b; rfl
    map_sub   := by intro a b; rfl
  }, ?_⟩
  intro i
  funext τ
  rfl
