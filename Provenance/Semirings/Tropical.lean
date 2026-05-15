import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Real.Basic

import Provenance.Having
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

instance [ToString α] : ToString (Tropical α) where
  toString x := toString ((x.untrop: α))

/-- In the tropicalization of a linear order, `a ≥ b` if and only if
`a+b = b`. -/
theorem tropical_order_ge [LinearOrder α] :
  ∀ a b: Tropical α, a.untrop ≥ b.untrop ↔ a+b = b := by
    intro a b
    exact Tropical.add_eq_right_iff.symm

/-- ProvSQL's `Tropical::delta`: the indicator of being nonzero. -/
private noncomputable def Tropical.deltaInd
    [LinearOrderedAddCommMonoidWithTop α] (a : Tropical α) : Tropical α :=
  if a = 0 then 0 else 1

/-- The tropical semiring is an m-semiring. The natural order of the
semiring is the reverse of the usual order. The monus `a-b` is defined as
`⊤` if `a≥b` (for the usual order, not the natural semiring order), and
as `a` otherwise. -/
noncomputable instance [LinearOrderedAddCommMonoidWithTop α] : SemiringWithMonus (Tropical α) where
  sub a b := if (Tropical.untrop a ≥ Tropical.untrop b) then ⊤ else a
  le a b := Tropical.untrop a ≥ Tropical.untrop b
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
      simp at h
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
  The tropical semiring is idempotent, so a tropical `δ` could equally well be the
  identity; we follow ProvSQL and use the indicator here.

  The proofs below are local rather than going through the generic helpers
  `delta_natCast_pos_indicator` / `delta_regrouping_indicator`: the tropical order
  that makes the semiring canonically ordered is the *reverse* of the Mathlib order on
  `Tropical α`, so we cannot expose a separate `CanonicallyOrderedAdd (Tropical α)`
  instance without clashing with `Mathlib.Algebra.Tropical.Basic`. -/
  delta := Tropical.deltaInd
  delta_zero := by simp [Tropical.deltaInd]
  delta_natCast_pos := by
    have hidem : idempotent (Tropical α) := fun a => by simp [(· + ·), Add.add]
    intro n hn
    have hcast : ((n : Tropical α)) = 1 :=
      natCast_pos_eq_one_of_idempotent hidem hn
    show Tropical.deltaInd ((n : Tropical α)) = 1
    rw [Tropical.deltaInd, hcast]
    split_ifs with hh
    · exact hh.symm
    · rfl
  delta_regrouping := by
    -- `Tropical α` analogue of `Multiset.sum_eq_zero_iff` (Mathlib only provides the
    -- canonically-ordered version, but the tropical order here is reversed). Proved
    -- by induction: zero in the tropical semiring is `trop ⊤`, addition is `min`,
    -- and `min x y = ⊤ ↔ x = ⊤ ∧ y = ⊤`.
    have hsum_zero : ∀ (t : Multiset (Tropical α)),
        t.sum = 0 ↔ ∀ a ∈ t, a = 0 := by
      intro t
      induction t using Multiset.induction_on with
      | empty => simp
      | cons a r ih =>
        rw [Multiset.sum_cons]
        simp only [Multiset.mem_cons, forall_eq_or_imp]
        constructor
        · intro hadd
          have h : min (Tropical.untrop a) (Tropical.untrop r.sum) = ⊤ := by
            rw [← Tropical.untrop_add, hadd, Tropical.untrop_zero]
          refine ⟨Tropical.untrop_injective ?_, ih.mp (Tropical.untrop_injective ?_)⟩
          · rw [Tropical.untrop_zero]
            exact le_antisymm le_top (by rw [← h]; exact min_le_left _ _)
          · rw [Tropical.untrop_zero]
            exact le_antisymm le_top (by rw [← h]; exact min_le_right _ _)
        · rintro ⟨ha, hr⟩
          rw [ha, ih.mpr hr, add_zero]
    intro s
    show Tropical.deltaInd (s.map Tropical.deltaInd).sum = Tropical.deltaInd s.sum
    -- Both sides reduce to a single `if`; show the conditions coincide.
    have hzero_iff : (s.map Tropical.deltaInd).sum = 0 ↔ s.sum = 0 := by
      constructor
      · intro h
        refine (hsum_zero s).mpr (fun a ha => ?_)
        by_contra hane
        have h1eq : (1 : Tropical α) = 0 := by
          have hmem : (1 : Tropical α) ∈ s.map Tropical.deltaInd :=
            Multiset.mem_map.mpr ⟨a, ha, by simp [Tropical.deltaInd, hane]⟩
          exact (hsum_zero _).mp h _ hmem
        -- `1 = 0` in a semiring collapses everything to `0`.
        apply hane
        calc a = a * 1 := (mul_one a).symm
          _ = a * 0 := by rw [h1eq]
          _ = 0 := mul_zero a
      · intro h
        refine (hsum_zero _).mpr ?_
        intro b hb
        obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
        simp [Tropical.deltaInd, (hsum_zero s).mp h a ha]
    show (if (s.map Tropical.deltaInd).sum = 0 then (0 : Tropical α) else 1) =
         if s.sum = 0 then (0 : Tropical α) else 1
    by_cases hs : s.sum = 0
    · rw [if_pos hs, if_pos (hzero_iff.mpr hs)]
    · rw [if_neg hs, if_neg (fun h => hs (hzero_iff.mp h))]

noncomputable instance [LinearOrderedAddCommMonoidWithTop α] :
    CommSemiringWithMonus (Tropical α) where
  mul_comm := mul_comm

/-- The tropical semiring over `ℕ ∪ {∞}` is a semiring with monus. -/
noncomputable instance : SemiringWithMonus (Tropical (WithTop ℕ)) := inferInstance
noncomputable instance : CommSemiringWithMonus (Tropical (WithTop ℕ)) := inferInstance
/-- The tropical semiring over `ℚ ∪ {∞}` is a semiring with monus. -/
noncomputable instance : SemiringWithMonus (Tropical (WithTop ℚ)) := inferInstance
noncomputable instance : CommSemiringWithMonus (Tropical (WithTop ℚ)) := inferInstance

/-- The tropical semiring over `ℝ ∪ {∞}` is a semiring with monus. Note
that this contradicts [Geerts & Poggi, *On database query languages for
K-relations*, Example 4][geerts2010database] which claims this semiring
cannot be extended to a semiring with monus: indeed, that paper gives
a wrong definition of the monus operator in the tropical semiring. -/
noncomputable instance : SemiringWithMonus (Tropical (WithTop ℝ)) := inferInstance
noncomputable instance : CommSemiringWithMonus (Tropical (WithTop ℝ)) := inferInstance

/-- The tropical semiring is absorptive, as long as the order in the
  addition monoid corresponds to a canonical order (e.g., as in ℕ) --/
theorem Tropical.absorptive [LinearOrderedAddCommMonoidWithTop α] [CanonicallyOrderedAdd α] : absorptive (Tropical α) := by
  intro a
  simp only[(· + ·), Add.add]
  congr
  simp[untrop_one]

theorem TropicalN.absorptive : absorptive (Tropical (WithTop ℕ)) := by
  exact Tropical.absorptive

/-- Times distributes over monus on tropical semirings made of an order
  strictly compatible with addition, with an additional top element. -/
theorem Tropical.mul_sub_left_distributive
  [LinearOrder α] [AddCancelCommMonoid α] [IsOrderedAddMonoid α] [AddLeftStrictMono α]:
  mul_sub_left_distributive (Tropical (WithTop α)) := by
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

theorem TropicalN.mul_sub_left_distributive : mul_sub_left_distributive (Tropical (WithTop ℕ)) := by
  exact Tropical.mul_sub_left_distributive
theorem TropicalQ.mul_sub_left_distributive : mul_sub_left_distributive (Tropical (WithTop ℚ)) := by
  exact Tropical.mul_sub_left_distributive
theorem TropicalR.mul_sub_left_distributive : mul_sub_left_distributive (Tropical (WithTop ℝ)) := by
  exact Tropical.mul_sub_left_distributive

/-- The tropical semiring is idempotent --/
theorem Tropical.idempotent [LinearOrderedAddCommMonoidWithTop α] : idempotent (Tropical α) := by
  intro a
  simp[(· + ·), Add.add]

/-- The tropical semiring over `WithTop R` (for any `R` with `Zero R`) has characteristic 0
in the `CharP` sense: it is idempotent, and `(0 : Tropical (WithTop R)) = trop ⊤` differs from
`(1 : Tropical (WithTop R)) = trop 0` since `⊤ ≠ 0` in `WithTop R`. -/
instance TropicalN.instCharPZero : CharP (Tropical (WithTop ℕ)) 0 :=
  CharP.zero_of_idempotent Tropical.idempotent
instance TropicalQ.instCharPZero : CharP (Tropical (WithTop ℚ)) 0 :=
  CharP.zero_of_idempotent Tropical.idempotent
noncomputable instance TropicalR.instCharPZero : CharP (Tropical (WithTop ℝ)) 0 :=
  CharP.zero_of_idempotent Tropical.idempotent

/-- The tropical semiring over `ℕ ∪ {∞}` does not have idempotent multiplication:
`Tropical.trop 1 * Tropical.trop 1 = Tropical.trop 2 ≠ Tropical.trop 1`. (Tropical
multiplication is the original additive monoid operation, which is not idempotent
on `ℕ`.) -/
theorem TropicalN.not_mul_idempotent :
    ¬ ∀ a : Tropical (WithTop ℕ), a * a = a := by
  push Not
  refine ⟨Tropical.trop (1 : WithTop ℕ), ?_⟩
  intro h
  have : Tropical.trop (1 + 1 : WithTop ℕ) = Tropical.trop (1 : WithTop ℕ) := h
  have h' : (1 + 1 : WithTop ℕ) = (1 : WithTop ℕ) := Tropical.trop_injective this
  exact absurd h' (by decide)

/-- There is no semiring homomorphism from `BoolFunc Y` to the tropical semiring
over `ℕ ∪ {∞}` sending the variables to arbitrary values: tropical multiplication
is not idempotent, contradicting `var i * var i = var i` in `BoolFunc Y`. -/
theorem TropicalN.no_hom_from_BoolFunc {Y : Type} [Inhabited Y] :
    ∃ ν : Y → Tropical (WithTop ℕ),
      ¬ ∃ φ : BoolFunc Y →+* Tropical (WithTop ℕ),
        ∀ i : Y, φ (BoolFunc.var i) = ν i :=
  BoolFunc.no_hom_of_not_mul_idem TropicalN.not_mul_idempotent

/-! ### Counterexample to `Having.F_eq_S` without absorptivity

Unlike `Tropical (WithTop ℕ)` (canonically ordered, hence absorptive via
`Tropical.absorptive`), `Tropical (WithTop ℚ)` is **not** absorptive: with
`a = trop (-1)` we have `1 + a = trop (min 0 (-1)) = trop (-1) ≠ trop 0 = 1`.

The tropical m-semiring over `ℚ` is still idempotent and satisfies
`mul_sub_left_distributive`, so it satisfies the "idempotent + ⊗-over-⊖
distributive" hypotheses one might hope to suffice for `Having.F_eq_S`.
The witness below shows that the strengthened hypothesis (absorptivity) is
genuinely required: on `U = {true, false} ⊆ Bool` and `α ≡ trop (-1)` we
have `S_1(U) = trop (-1)` but `F_1(U) = trop (-2)`. -/

/-- `Tropical (WithTop ℚ)` is **not** absorptive: `1 + trop (-1) = trop (-1) ≠ 1`.
The proof goes through `tropical_order_ge`: `a + 1 = 1` would force
`untrop a ≥ untrop 1 = 0`, but with `a = trop (-1)` we have `untrop a = -1`. -/
theorem TropicalQ.not_absorptive : ¬ absorptive (Tropical (WithTop ℚ)) := by
  intro h
  have h1 := h (Tropical.trop ((-1 : ℚ) : WithTop ℚ))
  rw [add_comm] at h1
  have hge := (tropical_order_ge _ _).mpr h1
  rw [Tropical.untrop_one] at hge
  have hlt : ((-1 : ℚ) : WithTop ℚ) < (0 : WithTop ℚ) := by
    show ((-1 : ℚ) : WithTop ℚ) < ((0 : ℚ) : WithTop ℚ)
    exact_mod_cast (by norm_num : (-1 : ℚ) < 0)
  exact absurd hge (not_le.mpr hlt)

namespace TropicalQ

/-- Counterexample family: the constant `α ≡ trop (-1)` on `Bool`. -/
private def α_ce : Bool → Tropical (WithTop ℚ) :=
  fun _ => Tropical.trop ((-1 : ℚ) : WithTop ℚ)

private theorem A_ce_singleton (b : Bool) :
    Having.A α_ce ({b} : Finset Bool) = Tropical.trop ((-1 : ℚ) : WithTop ℚ) := by
  simp [Having.A, α_ce]

private theorem A_ce_true_false :
    Having.A α_ce ({true, false} : Finset Bool) =
      Tropical.trop ((-2 : ℚ) : WithTop ℚ) := by
  show ∏ x ∈ ({true, false} : Finset Bool), α_ce x = _
  rw [Finset.prod_pair (by decide : true ≠ false)]
  show Tropical.trop ((-1 : ℚ) : WithTop ℚ) * Tropical.trop ((-1 : ℚ) : WithTop ℚ) = _
  apply Tropical.untrop_injective
  rw [Tropical.untrop_mul]
  show ((-1 : ℚ) : WithTop ℚ) + ((-1 : ℚ) : WithTop ℚ) = ((-2 : ℚ) : WithTop ℚ)
  norm_cast

private theorem A_ce_false_true :
    Having.A α_ce ({false, true} : Finset Bool) =
      Tropical.trop ((-2 : ℚ) : WithTop ℚ) := by
  rw [show ({false, true} : Finset Bool) = ({true, false} : Finset Bool) from by decide]
  exact A_ce_true_false

/-- `S_1` on `U = {true, false}` collapses by idempotence: both singleton
monomials equal `trop (-1)`, and `trop (-1) + trop (-1) = trop (-1)`. -/
private theorem S_ce_univ_one :
    Having.S α_ce (Finset.univ : Finset Bool) 1 =
      Tropical.trop ((-1 : ℚ) : WithTop ℚ) := by
  show ∑ W ∈ (Finset.univ : Finset Bool).powersetCard 1, Having.A α_ce W = _
  rw [show ((Finset.univ : Finset Bool).powersetCard 1)
        = ({({true} : Finset Bool), {false}} : Finset (Finset Bool)) from by decide]
  rw [Finset.sum_pair (by decide : ({true} : Finset Bool) ≠ {false})]
  rw [A_ce_singleton true, A_ce_singleton false]
  exact Tropical.idempotent _

private theorem neg1_ge_neg2 :
    ((-1 : ℚ) : WithTop ℚ) ≥ ((-2 : ℚ) : WithTop ℚ) := by
  exact_mod_cast (by norm_num : (-1 : ℚ) ≥ -2)

/-- The "exactly-`{b}`" contribution vanishes for both singletons: the
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
      Tropical.trop ((-2 : ℚ) : WithTop ℚ) := by
    cases b
    · exact A_ce_true_false
    · exact A_ce_false_true
  rw [A_ce_singleton, hAinsert]
  show (if Tropical.untrop (Tropical.trop ((-1 : ℚ) : WithTop ℚ)) ≥
           Tropical.untrop (Tropical.trop ((-2 : ℚ) : WithTop ℚ)) then
        (⊤ : Tropical (WithTop ℚ)) else _) = 0
  simp only [Tropical.untrop_trop]
  rw [if_pos neg1_ge_neg2]
  rfl

/-- The maximal subset contributes `trop (-2)`: with `U \ {true, false} = ∅`,
the residual sum is `0 = trop ⊤`, and `trop (-2) ⊖ 0 = trop (-2)` since
`¬ (-2 ≥ ⊤)`. -/
private theorem T_ce_univ_eq_neg2 :
    Having.T α_ce (Finset.univ : Finset Bool) ({true, false} : Finset Bool) =
      Tropical.trop ((-2 : ℚ) : WithTop ℚ) := by
  show Having.A α_ce {true, false} -
       ∑ x ∈ ((Finset.univ : Finset Bool) \ {true, false}),
         Having.A α_ce (insert x {true, false}) = _
  rw [show ((Finset.univ : Finset Bool) \ ({true, false} : Finset Bool))
        = (∅ : Finset Bool) from by decide]
  rw [Finset.sum_empty, A_ce_true_false]
  show (if Tropical.untrop (Tropical.trop ((-2 : ℚ) : WithTop ℚ)) ≥
           Tropical.untrop (0 : Tropical (WithTop ℚ)) then
        (⊤ : Tropical (WithTop ℚ)) else _) = _
  rw [if_neg]
  rw [Tropical.untrop_zero]
  intro h
  have h' : (⊤ : WithTop ℚ) ≤ ((-2 : ℚ) : WithTop ℚ) := h
  rw [top_le_iff] at h'
  exact WithTop.coe_ne_top h'

/-- `F_1` aggregates `T_U(W)` over `W ∈ {{true}, {false}, {true, false}}`;
the singletons contribute `0` (by `T_ce_singleton_eq_zero`) and the maximal
subset contributes `trop (-2)`. -/
private theorem F_ce_univ_one :
    Having.F α_ce (Finset.univ : Finset Bool) 1 =
      Tropical.trop ((-2 : ℚ) : WithTop ℚ) := by
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

end TropicalQ

/-- The HAVING-count identity `F_C(U) = S_C(U)` from `Having.F_eq_S`
fails in `Tropical (WithTop ℚ)`: with `U = Finset.univ : Finset Bool`,
`α ≡ trop (-1)`, and `C = 1`, we have `F_1(U) = trop (-2)` while
`S_1(U) = trop (-1)`. This shows that `Having.F_eq_S` genuinely needs the
absorptivity hypothesis (cf. `TropicalQ.not_absorptive`): the weaker
"idempotent + `mul_sub_left_distributive`" combination satisfied by
`Tropical (WithTop ℚ)` (and by `Tropical (WithTop ℝ)`) is insufficient. -/
theorem TropicalQ.F_ne_S :
    Having.F TropicalQ.α_ce (Finset.univ : Finset Bool) 1 ≠
      Having.S TropicalQ.α_ce (Finset.univ : Finset Bool) 1 := by
  rw [TropicalQ.F_ce_univ_one, TropicalQ.S_ce_univ_one]
  intro h
  exact absurd (WithTop.coe_injective (Tropical.trop_injective h)) (by norm_num)
