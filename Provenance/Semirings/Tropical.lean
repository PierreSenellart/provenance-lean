import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

import Provenance.Having
import Provenance.HavingMinMax
import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc

/-!
# Tropical m-semiring

This file shows that the tropicalization of any linearly ordered additive commutative
monoid with an absorbing top element (e.g., `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, `ℝ ∪ {∞}`) is a
commutative m-semiring. Addition is `min` (inherited from the tropical structure in
Mathlib), multiplication is the original addition of the monoid, zero is `⊤`, and one
is `0`.

The tropical semiring is absorptive and idempotent, and satisfies left-distributivity
of multiplication over monus.

The tropical semiring is used as a provenance semiring in
[Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance].

Note: [Geerts & Poggi, *On database query languages for K-relations*, Example 4][geerts2010database]
claims that the tropical semiring cannot be extended to an m-semiring. That claim is
incorrect: the paper gives a wrong definition of the monus operator.

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Geerts & Poggi, *On database query languages for K-relations*][geerts2010database]
-/

instance [ToString α] : ToString (WithTop α) where
  toString x := match x with | none => "⊤" | some x => toString x

instance [ToString α] : ToString (MinTropical α) where
  toString x := toString ((x.untrop: α))

/-- In the tropicalization of a linear order, `a ≥ b` if and only if
`a+b = b`. -/
theorem tropical_order_ge [LinearOrder α] :
  ∀ a b: MinTropical α, a.untrop ≥ b.untrop ↔ a+b = b := by
    intro a b
    exact MinTropical.add_eq_right_iff.symm

/-- ProvSQL's `Tropical::delta`: the indicator of being nonzero. -/
private noncomputable def MinTropical.deltaInd
    [LinearOrderedAddCommMonoidWithTop α] (a : MinTropical α) : MinTropical α :=
  if a = 0 then 0 else 1

/-- The tropical semiring is an m-semiring. The natural order of the
semiring is the reverse of the usual order. The monus `a-b` is defined as
`⊤` if `a≥b` (for the usual order, not the natural semiring order), and
as `a` otherwise. -/
noncomputable instance [LinearOrderedAddCommMonoidWithTop α] : SemiringWithMonus (MinTropical α) where
  sub a b := if (MinTropical.untrop a ≥ MinTropical.untrop b) then ⊤ else a
  le a b := MinTropical.untrop a ≥ MinTropical.untrop b
  lt a b := a+b = b ∧ a ≠ b
  lt_iff_le_not_ge := by
    intro a b
    rw[tropical_order_ge,tropical_order_ge]
    apply Iff.intro
    . intro h
      constructor
      . tauto
      . obtain ⟨h₁, h₂⟩ := h
        rw[add_comm, h₁]
        tauto
    . intro h
      obtain ⟨h₁, h₂⟩ := h
      constructor
      . tauto
      . rw[add_comm, h₁] at h₂
        tauto

  le_refl := by simp
  le_trans := by
    intro a b c hab hbc
    rw[tropical_order_ge]
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hbc
    calc
      a + c = a + b + c := by simp[hbc,add_assoc]
          _ = b + c     := by simp[hab]
              _ = c     := by simp[hbc]

  le_antisymm := by
    intro a b hab hba
    rw[tropical_order_ge] at hab
    rw[tropical_order_ge] at hba
    calc
      a = b + a := by simp[hba]
      _ = a + b := by simp[add_comm]
      _ = b     := by simp[hab]

  add_le_add_left := by
    intro a b h c

    rw[tropical_order_ge]
    rw[tropical_order_ge] at h

    calc
      a + c + (b + c) = c + a + (c + b)   := by simp[add_comm]
                    _ = c + (a + (c + b)) := by rw[add_assoc]
                    _ = c + (a + c + b)   := by rw[add_assoc]
                    _ = c + (c + a + b)   := by rw[add_comm a c]
                    _ = c + (c + (a + b)) := by rw[add_assoc]
                    _ = c + (c + b)       := by rw[h]
                    _ = c + c + b         := by rw[add_assoc]
                    _ = c + b             := by simp

    simp[add_comm]

  exists_add_of_le := by
    intro a b h
    rw[tropical_order_ge] at h
    use b
    simp[h]

  le_self_add := by
    intro a b
    rw[tropical_order_ge]
    calc
      a + (a + b) = a + a + b := by rw[add_assoc]
                _ = a + b     := by simp

  le_add_self := by
    simp[add_comm]

  monus_spec := by
    intro a b c
    simp[(· - ·)]
    split_ifs with h
    . simp
      left
      exact h
    . simp at h
      apply Iff.intro
      . tauto
      . intro h'
        cases h' with
        | inl h'' =>
          apply lt_of_lt_of_le h at h''
          apply lt_irrefl at h''
          contradiction
        | inr h'' =>
          exact h''

  /- δ matches ProvSQL's `Tropical::delta`: the support indicator
  (`0 = trop ⊤ ↦ 0`, any other element ↦ `1 = trop 0`).
  The tropical semiring is additively idempotent, so `δ := id` does satisfy
  `delta_zero` and `delta_natCast_pos`, but it fails `delta_absorb`, whose
  content here is `a + min(a, b) = a` in the underlying monoid – see
  `MinTropicalN.not_isDelta_id`. The indicator is therefore forced, as in ProvSQL.

  The proofs below are local rather than going through the generic helpers
  `delta_natCast_pos_indicator` / `delta_absorb_indicator`: the tropical order
  that makes the semiring canonically ordered is the *reverse* of the Mathlib order on
  `MinTropical α`, so we cannot expose a separate `CanonicallyOrderedAdd (MinTropical α)`
  instance without clashing with `Mathlib.Algebra.Tropical.Basic`. -/
  delta := MinTropical.deltaInd
  delta_zero := by simp [MinTropical.deltaInd]
  delta_natCast_pos := by
    have hidem : idempotent (MinTropical α) := fun a => by simp [(· + ·), Add.add]
    intro n hn
    have hcast : ((n : MinTropical α)) = 1 :=
      natCast_pos_eq_one_of_idempotent hidem hn
    show MinTropical.deltaInd ((n : MinTropical α)) = 1
    rw [MinTropical.deltaInd, hcast]
    split_ifs with hh
    · exact hh.symm
    · rfl
  delta_absorb := fun a b => by
    by_cases h : a + b = 0
    · have hmin : min (MinTropical.untrop a) (MinTropical.untrop b) = ⊤ := by
        rw [← MinTropical.untrop_add, h, MinTropical.untrop_zero]
      have ha : a = 0 := MinTropical.untrop_injective (by
        rw [MinTropical.untrop_zero]
        exact le_antisymm le_top (by rw [← hmin]; exact min_le_left _ _))
      rw [ha, zero_mul]
    · show a * MinTropical.deltaInd (a + b) = a
      rw [MinTropical.deltaInd, ite_eq_right h, mul_one]

noncomputable instance [LinearOrderedAddCommMonoidWithTop α] :
    CommSemiringWithMonus (MinTropical α) where
  mul_comm := mul_comm

/-- The tropical semiring over `ℕ ∪ {∞}` is a semiring with monus. -/
noncomputable instance : SemiringWithMonus (MinTropical (WithTop ℕ)) := inferInstance
noncomputable instance : CommSemiringWithMonus (MinTropical (WithTop ℕ)) := inferInstance
/-- The tropical semiring over `ℚ ∪ {∞}` is a semiring with monus. -/
noncomputable instance : SemiringWithMonus (MinTropical (WithTop ℚ)) := inferInstance
noncomputable instance : CommSemiringWithMonus (MinTropical (WithTop ℚ)) := inferInstance

/-- The tropical semiring over `ℤ ∪ {∞}` is a semiring with monus. Like
the `ℚ` and `ℝ` variants it is idempotent and `⊗`-over-`⊖` distributive
but not absorptive; unlike them its carrier is kernel-computable, which
makes it the tropical semiring of choice for `decide`-checked
counterexamples. -/
noncomputable instance : SemiringWithMonus (MinTropical (WithTop ℤ)) := inferInstance
noncomputable instance : CommSemiringWithMonus (MinTropical (WithTop ℤ)) := inferInstance
instance : HasAltLinearOrder (MinTropical (WithTop ℤ)) := ⟨inferInstance⟩

/-- The tropical semiring over `ℝ ∪ {∞}` is a semiring with monus. Note
that this contradicts [Geerts & Poggi, *On database query languages for
K-relations*, Example 4][geerts2010database] which claims this semiring
cannot be extended to a semiring with monus: indeed, that paper gives
a wrong definition of the monus operator in the tropical semiring. -/
noncomputable instance : SemiringWithMonus (MinTropical (WithTop ℝ)) := inferInstance
noncomputable instance : CommSemiringWithMonus (MinTropical (WithTop ℝ)) := inferInstance

/-- The tropical semiring is absorptive, as long as the order in the
  addition monoid corresponds to a canonical order (e.g., as in ℕ) --/
theorem MinTropical.absorptive [LinearOrderedAddCommMonoidWithTop α] [CanonicallyOrderedAdd α] : absorptive (MinTropical α) := by
  intro a
  simp only[(· + ·), Add.add]
  congr
  simp[untrop_one]

theorem MinTropicalN.absorptive : absorptive (MinTropical (WithTop ℕ)) := by
  exact MinTropical.absorptive

/-- The tropical semiring over `WithTop ℕ` is not exclusive: absorptive and
totally ordered, with `trop 1` neither `𝟘 = trop ⊤` nor `𝟙 = trop 0`, so
`𝟙 ⊖ trop 1 = 𝟙` and `trop 1 ⊗ 𝟙 = trop 1`. -/
theorem MinTropicalN.not_exclusive : ¬ exclusive (MinTropical (WithTop ℕ)) :=
  not_exclusive_of_absorptive_of_total MinTropicalN.absorptive
    (fun a b => le_total (MinTropical.untrop b) (MinTropical.untrop a))
    (a := MinTropical.trop ((1 : ℕ) : WithTop ℕ))
    (by decide) (by decide)

/-- On the tropical semiring over `ℕ ∪ {∞}` the identity is not an admissible `δ`,
even though this semiring *is* absorptive (`MinTropicalN.absorptive`): what
`delta_absorb` asks of `δ := id` is the lattice law `a ⊗ (a ⊕ b) = a`, i.e.,
`a + min(a, b) = a` in `ℕ`, and at `a = b = trop 1` it reads `trop 2 ≠ trop 1`.
This is why the instance takes the support indicator (ProvSQL's
`Tropical::delta`). -/
theorem MinTropicalN.not_isDelta_id :
    ¬ IsDelta (id : MinTropical (WithTop ℕ) → MinTropical (WithTop ℕ)) := by
  refine not_isDelta_id_of_absorb_ne
    (a := MinTropical.trop ((1 : ℕ) : WithTop ℕ))
    (b := MinTropical.trop ((1 : ℕ) : WithTop ℕ)) ?_
  intro h
  have h' := congrArg MinTropical.untrop h
  simp [MinTropical.untrop_mul] at h'

/-- Times distributes over monus on tropical semirings made of an order
  strictly compatible with addition, with an additional top element. -/
theorem MinTropical.mul_sub_left_distributive
  [LinearOrder α] [AddCancelCommMonoid α] [IsOrderedAddMonoid α] [AddLeftStrictMono α]:
  mul_sub_left_distributive (MinTropical (WithTop α)) := by
    intro a b c
    simp[(· - ·), Sub.sub]
    split_ifs with h₁ h₂ h₃
    . exact mul_zero _
    . simp at *
      simp only[(· ≤ ·)] at h₁
      have h' := add_le_add_right h₁ (untrop a)
      have contradiction := lt_of_lt_of_le h₂ h'
      simp at contradiction
    . simp only[(· ≤ ·)] at h₁
      have h : untrop b < untrop c := by
        exact lt_of_not_ge h₁
      by_cases ha: untrop a = ⊤
      . simp only[ha,(· * ·),Mul.mul]
        rfl
      . have h_lt : untrop a + untrop b < untrop a + untrop c :=
          WithTop.add_lt_add_left ha h
        have contradiction := lt_of_lt_of_le h_lt h₃
        simp at contradiction
    . rfl

theorem MinTropicalN.mul_sub_left_distributive : mul_sub_left_distributive (MinTropical (WithTop ℕ)) := by
  exact MinTropical.mul_sub_left_distributive
theorem MinTropicalQ.mul_sub_left_distributive : mul_sub_left_distributive (MinTropical (WithTop ℚ)) := by
  exact MinTropical.mul_sub_left_distributive
theorem MinTropicalR.mul_sub_left_distributive : mul_sub_left_distributive (MinTropical (WithTop ℝ)) := by
  exact MinTropical.mul_sub_left_distributive

/-- The tropical semiring is idempotent --/
theorem MinTropical.idempotent [LinearOrderedAddCommMonoidWithTop α] : idempotent (MinTropical α) := by
  intro a
  simp[(· + ·), Add.add]

/-- The tropical semiring over `WithTop R` (for any `R` with `Zero R`) has characteristic 0
in the `CharP` sense: it is idempotent, and `(0 : MinTropical (WithTop R)) = trop ⊤` differs from
`(1 : MinTropical (WithTop R)) = trop 0` since `⊤ ≠ 0` in `WithTop R`. -/
instance MinTropicalN.instCharPZero : CharP (MinTropical (WithTop ℕ)) 0 :=
  CharP.zero_of_idempotent MinTropical.idempotent
instance MinTropicalQ.instCharPZero : CharP (MinTropical (WithTop ℚ)) 0 :=
  CharP.zero_of_idempotent MinTropical.idempotent
noncomputable instance MinTropicalR.instCharPZero : CharP (MinTropical (WithTop ℝ)) 0 :=
  CharP.zero_of_idempotent MinTropical.idempotent

/-- The tropical semiring over `ℕ ∪ {∞}` does not have idempotent multiplication:
`MinTropical.trop 1 * MinTropical.trop 1 = MinTropical.trop 2 ≠ MinTropical.trop 1`. (MinTropical
multiplication is the original additive monoid operation, which is not idempotent
on `ℕ`.) -/
theorem MinTropicalN.not_mul_idempotent :
    ¬ ∀ a : MinTropical (WithTop ℕ), a * a = a := by
  push Not
  refine ⟨MinTropical.trop (1 : WithTop ℕ), ?_⟩
  intro h
  have : MinTropical.trop (1 + 1 : WithTop ℕ) = MinTropical.trop (1 : WithTop ℕ) := h
  have h' : (1 + 1 : WithTop ℕ) = (1 : WithTop ℕ) := MinTropical.trop_injective this
  exact absurd h' (by decide)

/-- There is no semiring homomorphism from `BoolFunc Y` to the tropical semiring
over `ℕ ∪ {∞}` sending the variables to arbitrary values: tropical multiplication
is not idempotent, contradicting `var i * var i = var i` in `BoolFunc Y`. -/
theorem MinTropicalN.no_hom_from_BoolFunc {Y : Type} [Inhabited Y] :
    ∃ ν : Y → MinTropical (WithTop ℕ),
      ¬ ∃ φ : BoolFunc Y →+* MinTropical (WithTop ℕ),
        ∀ i : Y, φ (BoolFunc.var i) = ν i :=
  BoolFunc.no_hom_of_not_mul_idem MinTropicalN.not_mul_idempotent

/-! ### Counterexample to `Having.F_eq_S` without absorptivity

Unlike `MinTropical (WithTop ℕ)` (canonically ordered, hence absorptive via
`MinTropical.absorptive`), `MinTropical (WithTop ℝ)` is **not** absorptive: with
`a = trop (-1)` we have `1 + a = trop (min 0 (-1)) = trop (-1) ≠ trop 0 = 1`.

The tropical m-semiring over `ℝ` is still idempotent and satisfies
`mul_sub_left_distributive`, so it satisfies the “idempotent + ⊗-over-⊖
distributive” hypotheses one might hope to suffice for `Having.F_eq_S`.
The witness below shows that the strengthened hypothesis (absorptivity) is
genuinely required: on `U = {true, false} ⊆ Bool` and `α ≡ trop (-1)` we
have `S_1(U) = trop (-1)` but `F_1(U) = trop (-2)`. -/

/-- `MinTropical (WithTop ℝ)` is **not** absorptive: `1 + trop (-1) = trop (-1) ≠ 1`.
The proof goes through `tropical_order_ge`: `a + 1 = 1` would force
`untrop a ≥ untrop 1 = 0`, but with `a = trop (-1)` we have `untrop a = -1`. -/
theorem MinTropicalR.not_absorptive : ¬ absorptive (MinTropical (WithTop ℝ)) := by
  intro h
  have h1 := h (MinTropical.trop ((-1 : ℝ) : WithTop ℝ))
  rw [add_comm] at h1
  have hge := (tropical_order_ge _ _).mpr h1
  rw [MinTropical.untrop_one] at hge
  have hlt : ((-1 : ℝ) : WithTop ℝ) < (0 : WithTop ℝ) := by
    show ((-1 : ℝ) : WithTop ℝ) < ((0 : ℝ) : WithTop ℝ)
    exact_mod_cast (by norm_num : (-1 : ℝ) < 0)
  exact absurd hge (not_le.mpr hlt)

namespace MinTropicalR

/-- Counterexample family: the constant `α ≡ trop (-1)` on `Bool`. -/
private noncomputable def α_ce : Bool → MinTropical (WithTop ℝ) :=
  fun _ => MinTropical.trop ((-1 : ℝ) : WithTop ℝ)

private theorem A_ce_singleton (b : Bool) :
    Having.A α_ce ({b} : Finset Bool) = MinTropical.trop ((-1 : ℝ) : WithTop ℝ) := by
  simp [Having.A, α_ce]

private theorem A_ce_true_false :
    Having.A α_ce ({true, false} : Finset Bool) =
      MinTropical.trop ((-2 : ℝ) : WithTop ℝ) := by
  show ∏ x ∈ ({true, false} : Finset Bool), α_ce x = _
  rw [Finset.prod_pair (by decide : true ≠ false)]
  show MinTropical.trop ((-1 : ℝ) : WithTop ℝ) * MinTropical.trop ((-1 : ℝ) : WithTop ℝ) = _
  apply MinTropical.untrop_injective
  rw [MinTropical.untrop_mul]
  show ((-1 : ℝ) : WithTop ℝ) + ((-1 : ℝ) : WithTop ℝ) = ((-2 : ℝ) : WithTop ℝ)
  have h : (-1 : ℝ) + (-1 : ℝ) = -2 := by linarith
  rw [← WithTop.coe_add, h]

private theorem A_ce_false_true :
    Having.A α_ce ({false, true} : Finset Bool) =
      MinTropical.trop ((-2 : ℝ) : WithTop ℝ) := by
  rw [show ({false, true} : Finset Bool) = ({true, false} : Finset Bool) from by decide]
  exact A_ce_true_false

/-- `S_1` on `U = {true, false}` collapses by idempotence: both singleton
monomials equal `trop (-1)`, and `trop (-1) + trop (-1) = trop (-1)`. -/
private theorem S_ce_univ_one :
    Having.S α_ce (Finset.univ : Finset Bool) 1 =
      MinTropical.trop ((-1 : ℝ) : WithTop ℝ) := by
  show ∑ W ∈ (Finset.univ : Finset Bool).powersetCard 1, Having.A α_ce W = _
  rw [show ((Finset.univ : Finset Bool).powersetCard 1)
        = ({({true} : Finset Bool), {false}} : Finset (Finset Bool)) from by decide]
  rw [Finset.sum_pair (by decide : ({true} : Finset Bool) ≠ {false})]
  rw [A_ce_singleton true, A_ce_singleton false]
  exact MinTropical.idempotent _

private theorem neg1_ge_neg2 :
    ((-1 : ℝ) : WithTop ℝ) ≥ ((-2 : ℝ) : WithTop ℝ) := by
  exact_mod_cast (by norm_num : (-1 : ℝ) ≥ -2)

/-- The “exactly-`{b}`” contribution vanishes for both singletons: the
monus `trop (-1) ⊖ trop (-2)` collapses to `0` because `-1 ≥ -2` puts
`trop (-2)` above `trop (-1)` in the natural (reverse) order. -/
private theorem T_ce_singleton_eq_zero (b : Bool) :
    Having.T α_ce (Finset.univ : Finset Bool) ({b} : Finset Bool) = 0 := by
  show Having.A α_ce {b} -
       ∑ x ∈ ((Finset.univ : Finset Bool) \ {b}),
         Having.A α_ce (insert x {b}) = 0
  have huniv : (Finset.univ : Finset Bool) \ ({b} : Finset Bool) = {!b} := by
    cases b <;> decide
  rw [huniv, Finset.sum_singleton]
  have hAinsert : Having.A α_ce (insert (!b) ({b} : Finset Bool)) =
      MinTropical.trop ((-2 : ℝ) : WithTop ℝ) := by
    cases b
    · exact A_ce_true_false
    · exact A_ce_false_true
  rw [A_ce_singleton, hAinsert]
  show (if MinTropical.untrop (MinTropical.trop ((-1 : ℝ) : WithTop ℝ)) ≥
           MinTropical.untrop (MinTropical.trop ((-2 : ℝ) : WithTop ℝ)) then
        (⊤ : MinTropical (WithTop ℝ)) else _) = 0
  have hge : MinTropical.untrop (MinTropical.trop ((-1 : ℝ) : WithTop ℝ)) ≥
      MinTropical.untrop (MinTropical.trop ((-2 : ℝ) : WithTop ℝ)) := by
    simpa using neg1_ge_neg2
  rw [ite_eq_left hge]
  rfl

/-- The maximal subset contributes `trop (-2)`: with `U \ {true, false} = ∅`,
the residual sum is `0 = trop ⊤`, and `trop (-2) ⊖ 0 = trop (-2)` since
`¬ (-2 ≥ ⊤)`. -/
private theorem T_ce_univ_eq_neg2 :
    Having.T α_ce (Finset.univ : Finset Bool) ({true, false} : Finset Bool) =
      MinTropical.trop ((-2 : ℝ) : WithTop ℝ) := by
  show Having.A α_ce {true, false} -
       ∑ x ∈ ((Finset.univ : Finset Bool) \ {true, false}),
         Having.A α_ce (insert x {true, false}) = _
  rw [show ((Finset.univ : Finset Bool) \ ({true, false} : Finset Bool))
        = (∅ : Finset Bool) from by decide]
  rw [Finset.sum_empty, A_ce_true_false]
  show (if MinTropical.untrop (MinTropical.trop ((-2 : ℝ) : WithTop ℝ)) ≥
           MinTropical.untrop (0 : MinTropical (WithTop ℝ)) then
        (⊤ : MinTropical (WithTop ℝ)) else _) = _
  rw [ite_eq_right]
  rw [MinTropical.untrop_zero]
  intro h
  have h' : (⊤ : WithTop ℝ) ≤ ((-2 : ℝ) : WithTop ℝ) := h
  rw [top_le_iff] at h'
  exact WithTop.coe_ne_top h'

/-- `F_1` aggregates `T_U(W)` over `W ∈ {{true}, {false}, {true, false}}`;
the singletons contribute `0` (by `T_ce_singleton_eq_zero`) and the maximal
subset contributes `trop (-2)`. -/
private theorem F_ce_univ_one :
    Having.F α_ce (Finset.univ : Finset Bool) 1 =
      MinTropical.trop ((-2 : ℝ) : WithTop ℝ) := by
  show ∑ W ∈ (Finset.univ : Finset Bool).powerset.filter (fun W => 1 ≤ W.card),
         Having.T α_ce (Finset.univ : Finset Bool) W = _
  rw [show ((Finset.univ : Finset Bool).powerset.filter (fun W => 1 ≤ W.card))
        = ({({true} : Finset Bool), {false}, {true, false}}
            : Finset (Finset Bool)) from by decide]
  rw [show ({({true} : Finset Bool), {false}, {true, false}}
            : Finset (Finset Bool))
        = insert ({true} : Finset Bool)
            ({({false} : Finset Bool), {true, false}}
              : Finset (Finset Bool)) from rfl]
  rw [Finset.sum_insert (by decide :
      ({true} : Finset Bool) ∉
        ({({false} : Finset Bool), {true, false}} : Finset (Finset Bool)))]
  rw [Finset.sum_pair (by decide :
      ({false} : Finset Bool) ≠ ({true, false} : Finset Bool))]
  rw [T_ce_singleton_eq_zero true, T_ce_singleton_eq_zero false, T_ce_univ_eq_neg2]
  rw [zero_add, zero_add]

end MinTropicalR

/-- The HAVING-count identity `F_C(U) = S_C(U)` from `Having.F_eq_S`
fails in `MinTropical (WithTop ℝ)`: with `U = Finset.univ : Finset Bool`,
`α ≡ trop (-1)`, and `C = 1`, we have `F_1(U) = trop (-2)` while
`S_1(U) = trop (-1)`. This shows that `Having.F_eq_S` genuinely needs the
absorptivity hypothesis (cf. `MinTropicalR.not_absorptive`): the weaker
“idempotent + `mul_sub_left_distributive`” combination satisfied by
`MinTropical (WithTop ℝ)` (and likewise by `MinTropical (WithTop ℚ)`) is insufficient. -/
theorem MinTropicalR.F_ne_S :
    Having.F MinTropicalR.α_ce (Finset.univ : Finset Bool) 1 ≠
      Having.S MinTropicalR.α_ce (Finset.univ : Finset Bool) 1 := by
  rw [MinTropicalR.F_ce_univ_one, MinTropicalR.S_ce_univ_one]
  intro h
  exact absurd (WithTop.coe_injective (MinTropical.trop_injective h)) (by norm_num)

namespace MinTropicalR

/-- Counterexample aggregate term: the constant `t ≡ 0` on `Bool`. -/
private noncomputable def t_ce : Bool → ℝ := fun _ => 0

/-- On the counterexample instance, the possible-world provenance of
`MIN(t) ≥ 0` sums over all non-empty worlds (the predicate holds
everywhere since `t ≡ 0`), so it coincides with `F_1(U) = trop (-2)`. -/
private theorem prov_min_ge_ce :
    Having.prov α_ce (Finset.univ : Finset Bool)
        (fun W => CompOp.ge.eval (Having.minAgg t_ce W) (((0 : ℝ) : WithTop ℝ)))
      = MinTropical.trop ((-2 : ℝ) : WithTop ℝ) := by
  rw [← F_ce_univ_one]
  show ∑ W ∈ _, _ = ∑ W ∈ _, _
  refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) fun _ _ => rfl
  have hP : CompOp.ge.eval (Having.minAgg t_ce W) (((0 : ℝ) : WithTop ℝ)) := by
    show ((0 : ℝ) : WithTop ℝ) ≤ Having.minAgg t_ce W
    rw [Having.le_minAgg_iff]
    intro i _
    simp [t_ce]
  rw [Finset.one_le_card]
  exact ⟨fun h => h.1, fun h => ⟨h, hP⟩⟩

/-- On the counterexample instance, the `MIN` scan for `≥` returns
`trop (-1)`: no occurrence has value `< 0`, so the scan degenerates to
`𝟙 ⊗ (α true ⊕ α false) = trop (-1) ⊕ trop (-1) = trop (-1)`. -/
private theorem minScan_ge_ce :
    Having.minScan α_ce (Finset.univ : Finset Bool) t_ce CompOp.ge (0 : ℝ)
      = MinTropical.trop ((-1 : ℝ) : WithTop ℝ) := by
  show (1 - ∑ x ∈ Finset.univ.filter (fun i => t_ce i < 0), α_ce x)
      * ∑ i ∈ Finset.univ.filter (fun i => (0 : ℝ) ≤ t_ce i), α_ce i = _
  have h₁ : (Finset.univ : Finset Bool).filter (fun i => t_ce i < 0) = ∅ :=
    Finset.filter_false_of_mem (fun i _ => by simp [t_ce])
  have h₂ : (Finset.univ : Finset Bool).filter (fun i => (0 : ℝ) ≤ t_ce i)
      = Finset.univ :=
    Finset.filter_true_of_mem (fun i _ => by simp [t_ce])
  rw [h₁, h₂, Finset.sum_empty, monus_zero, one_mul,
    show (Finset.univ : Finset Bool) = ({true, false} : Finset Bool) from by decide,
    Finset.sum_pair (by decide : true ≠ false)]
  exact MinTropical.idempotent _

/-- The `MIN`-scan collapse (`Having.minScan_correct`) fails in
`MinTropical (WithTop ℝ)`: on `U = {true, false}` with `α ≡ trop (-1)`,
`t ≡ 0` and the predicate `MIN(t) ≥ 0`, the possible-world provenance is
`trop (-2)` while the scan returns `trop (-1)`. This is the same instance
as `MinTropicalR.F_ne_S`, and shows that the absorptivity hypothesis of
`Having.minScan_correct` (and, by symmetry, of `Having.maxScan_correct`
and `Having.firstScan_correct`) is genuinely required: the weaker
“idempotent + `mul_sub_left_distributive`” combination satisfied by
`MinTropical (WithTop ℝ)` is insufficient. -/
theorem minScan_ne_prov :
    Having.prov α_ce (Finset.univ : Finset Bool)
        (fun W => CompOp.ge.eval (Having.minAgg t_ce W) (((0 : ℝ) : WithTop ℝ)))
      ≠ Having.minScan α_ce (Finset.univ : Finset Bool) t_ce CompOp.ge (0 : ℝ) := by
  rw [prov_min_ge_ce, minScan_ge_ce]
  intro h
  exact absurd (WithTop.coe_injective (MinTropical.trop_injective h)) (by norm_num)

end MinTropicalR
