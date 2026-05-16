import Provenance.SemiringWithMonus
import Provenance.Semirings.BoolFunc

import Mathlib.Order.BoundedOrder.Basic

/-!
# Min-max semiring

This file defines the *min-max* semiring `MinMax α` over a bounded linear order `α`,
where addition is `min` and multiplication is `max`. The natural order is the
**reverse** of the order on `α` (so `⊤` is the additive identity and `⊥` the
multiplicative identity). This semiring models security levels or (dually) the fuzzy
semiring.

Also defined:
* `MaxMin α = MinMax (OrderDual α)` – the dual semiring with `max` for addition and
  `min` for multiplication
* `TVL` – three-valued logic `{⊥, unknown, ⊤}`, an instance of `MaxMin`

`MinMax α` is absorptive and idempotent. The dual `MaxMin TVL` does **not** satisfy
left-distributivity of multiplication over monus.

The security/access control semiring is discussed in
[Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance].

## References

* [Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance]
-/

section MinMax

variable {α: Type} [LinearOrder α] [OrderBot α] [OrderTop α]

/-- The min-max semiring over a bounded linear order: addition is `min`, multiplication
is `max`, zero is `⊤` and one is `⊥`. The natural order is the reverse of `α`'s order. -/
@[ext]
structure MinMax (α: Type) where
  val: α

instance : Coe (MinMax α) α := ⟨MinMax.val⟩

instance : Top  (MinMax α) := ⟨⟨⊤⟩⟩
instance : Bot  (MinMax α) := ⟨⟨⊥⟩⟩
instance : LE   (MinMax α) := ⟨λ a b ↦ b.val ≤ a.val⟩

instance : LinearOrder (MinMax α) where
  le_refl := by simp[(· ≤ ·)]
  le_trans := by
    simp[(· ≤ ·)]
    intro a b c hba hcb
    exact Preorder.le_trans c.val b.val a.val hcb hba
  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    ext
    apply le_antisymm <;> assumption
  le_total := by simp[(· ≤ ·)]; intro a b; apply le_total
  toDecidableLE := inferInstance

instance : Zero (MinMax α) := ⟨⊤⟩
instance : Add  (MinMax α) := ⟨λ a b ↦ ⟨min a.val b.val⟩⟩
instance : One  (MinMax α) := ⟨⊥⟩
instance : Mul  (MinMax α) := ⟨λ a b ↦ ⟨max a.val b.val⟩⟩
instance : Sub  (MinMax α) := ⟨λ a b ↦ if a.val ≥ b.val then ⟨⊤⟩ else ⟨a.val⟩⟩

instance : CommSemiring (MinMax α) where
  add_assoc := by
    intro a b c
    simp[(· + ·),Add.add]
    exact min_assoc _ _ _

  add_comm := by
    intro a b
    simp[(· + ·),Add.add]
    exact min_comm _ _

  zero_add  := by
    intro a
    ext
    simp[(· + ·),Add.add]
    exact OrderTop.le_top _
  add_zero := by
    intro a
    ext
    simp[(· + ·),Add.add]
    exact OrderTop.le_top _

  nsmul := nsmulRec
  mul_assoc := by
    intro a b c
    simp[(· * ·),Mul.mul]
    exact max_assoc _ _ _
  mul_comm := by
    intro a b
    simp[(· * ·),Mul.mul]
    exact max_comm _ _

  left_distrib := by
    intro a b c
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    exact sup_inf_left _ _ _

  right_distrib := by
    intro a b c
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    exact sup_inf_right _ _ _

  one_mul := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderBot.bot_le _
  mul_one := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderBot.bot_le _

  zero_mul := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderTop.le_top _
  mul_zero := by
    intro a
    ext
    simp[(· * ·),Mul.mul]
    exact OrderTop.le_top _

/-- `MinMax α` is a commutative m-semiring for any bounded linear order `α`. -/
instance : SemiringWithMonus (MinMax α) where
  add_le_add_left := by
    intro a b hab c
    simp[(· + ·),Add.add,(· ≤ ·)]
    exact Or.inl hab

  exists_add_of_le := by
    intro a b hab
    use b
    ext
    simp[(· + ·),Add.add]
    exact hab

  le_self_add := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]

  le_add_self := by
    intro a b
    simp[(· + ·),Add.add,(· ≤ ·)]

  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· ≤ ·),(· - ·),Sub.sub]
    split_ifs with h <;> simp <;> tauto

  /- δ matches ProvSQL's `MinMax::delta`: the identity. -/
  delta := id
  delta_zero := rfl
  delta_natCast_pos :=
    let hidem : idempotent (MinMax α) :=
      idempotent_of_absorptive (fun a => by
        simp [(· + ·), Add.add]
        congr
        simp
        left
        rfl)
    fun hn => delta_natCast_pos_id hidem hn
  delta_regrouping := delta_regrouping_id

instance : CommSemiringWithMonus (MinMax α) where
  mul_comm := mul_comm

theorem MinMax.absorptive : absorptive (MinMax α) := by
  intro a
  simp[(· + ·), Add.add]
  congr
  simp
  left
  rfl

theorem MinMax.idempotent : idempotent (MinMax α) :=
  idempotent_of_absorptive MinMax.absorptive

instance [Nontrivial α] : Nontrivial (MinMax α) := ⟨0, 1, fun h => by
  have h' : (⟨⊤⟩ : MinMax α) = ⟨⊥⟩ := h
  injection h' with h''
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  apply hxy
  have hx : x = ⊥ := le_antisymm (h'' ▸ le_top) bot_le
  have hy : y = ⊥ := le_antisymm (h'' ▸ le_top) bot_le
  exact hx.trans hy.symm⟩

/-- `MinMax α` has characteristic 0 in the `CharP` sense whenever `α` is nontrivial:
it is idempotent, and `(0 : MinMax α) = ⟨⊤⟩` differs from `(1 : MinMax α) = ⟨⊥⟩`
since `⊥ ≠ ⊤` in a nontrivial bounded order. -/
instance MinMax.instCharPZero [Nontrivial α] : CharP (MinMax α) 0 :=
  CharP.zero_of_idempotent MinMax.idempotent

abbrev MaxMin (α : Type) := MinMax (OrderDual α)

instance : CommSemiring (MaxMin α) :=
  inferInstanceAs (CommSemiring (MinMax (OrderDual α)))

instance : SemiringWithMonus (MaxMin α) :=
  inferInstanceAs (SemiringWithMonus (MinMax (OrderDual α)))

instance : CommSemiringWithMonus (MaxMin α) :=
  inferInstanceAs (CommSemiringWithMonus (MinMax (OrderDual α)))

instance {α : Type} [h : Nontrivial α] : Nontrivial (OrderDual α) := h

/-- Three-valued logic `{⊥, unknown, ⊤}`, used as an instance of `MaxMin`. -/
inductive TVL
| bot
| unknown
| top
deriving DecidableEq, Repr, Ord

instance : LE TVL where
  le := λ a b => (compare a b).isLE

instance : LinearOrder TVL where
  le_refl := by intro a; cases a <;> decide
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_antisymm := by intro a b; cases a <;> cases b <;> decide
  le_total := by intro a b; cases a <;> cases b <;> decide
  toDecidableLE := inferInstance

instance : OrderBot TVL where
  bot := TVL.bot
  bot_le := by intro a; cases a <;> decide

instance : OrderTop TVL where
  top := TVL.top
  le_top := by intro a; cases a <;> decide

instance : CommSemiring (MaxMin TVL) :=
  inferInstance

instance : SemiringWithMonus (MaxMin TVL) :=
  inferInstance

instance : CommSemiringWithMonus (MaxMin TVL) :=
  inferInstance

instance : Nontrivial TVL := ⟨TVL.bot, TVL.top, by decide⟩

/-- `MaxMin α` has characteristic 0 in the `CharP` sense whenever `α` is nontrivial:
this lifts the general `MinMax` instance to the dual order through
`MaxMin α = MinMax (OrderDual α)`. In particular it applies to `MaxMin TVL` since
`TVL` is nontrivial. -/
instance MaxMin.instCharPZero {α : Type} [LinearOrder α] [OrderBot α] [OrderTop α]
    [Nontrivial α] : CharP (MaxMin α) 0 :=
  inferInstance

theorem TVL.not_mul_sub_left_distributive : ¬(mul_sub_left_distributive (MaxMin TVL)) := by
  simp
  use ⟨TVL.unknown⟩, ⟨TVL.top⟩, ⟨TVL.unknown⟩
  decide

/-- There is no semiring homomorphism from `BoolFunc Y` to `MaxMin TVL` sending the
variables to arbitrary values. The semiring `MaxMin TVL` is absorptive and has
both idempotent addition and idempotent multiplication, so the simple
obstructions don't apply: the failure is more subtle.

The argument uses only that a semiring homomorphism preserves `+` and `*`
(monus is irrelevant here, even though one of the elements we exhibit
happens to be written using BoolFunc's monus). In `BoolFunc Y`, the element
`c := 1 - var i` satisfies two purely additive/multiplicative identities:
`var i + c = 1` and `var i * c = 0`. Applying any semiring homomorphism `φ`
and writing `y := φ c` (an arbitrary element of the target), this forces
`φ (var i) + y = 1` and `φ (var i) * y = 0`. Setting `φ (var i) = ⟨unknown⟩`
in `MaxMin TVL`: the first equation reduces to `max(unknown, y.val) = top`,
forcing `y.val = top`; the second reduces to `min(unknown, y.val) = bot`,
forcing `y.val = bot`. The two are incompatible.

The same obstruction extends to `MinMax α` whenever `α` has at least three
distinct order values. -/
theorem TVL.no_hom_from_BoolFunc {Y : Type} [Inhabited Y] :
    ∃ ν : Y → MaxMin TVL,
      ¬ ∃ φ : BoolFunc Y →+* MaxMin TVL,
        ∀ i : Y, φ (BoolFunc.var i) = ν i := by
  refine ⟨fun _ => ⟨TVL.unknown⟩, ?_⟩
  rintro ⟨φ, hφ⟩
  set v := BoolFunc.var (default : Y)
  have hadd_bf : v + (1 - v) = (1 : BoolFunc Y) := BoolFunc.add_sub_self v
  have hmul_bf : v * (1 - v) = (0 : BoolFunc Y) := BoolFunc.mul_sub_self v
  have hφv : φ v = (⟨TVL.unknown⟩ : MaxMin TVL) := hφ (default : Y)
  have hadd : φ v + φ (1 - v) = 1 := by rw [← φ.map_add, hadd_bf, φ.map_one]
  have hmul : φ v * φ (1 - v) = 0 := by rw [← φ.map_mul, hmul_bf, φ.map_zero]
  rw [hφv] at hadd hmul
  have key : ∀ y : MaxMin TVL,
      ¬ ((⟨TVL.unknown⟩ : MaxMin TVL) + y = 1 ∧
         (⟨TVL.unknown⟩ : MaxMin TVL) * y = 0) := by
    intro y
    obtain ⟨w⟩ := y
    cases w <;> decide
  exact key (φ (1 - v)) ⟨hadd, hmul⟩
