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

/-- The support-indicator `δ` of why-provenance: `𝟘` on the empty
witness family, `𝟙` otherwise. The witness-preserving identity choice
(ProvSQL's historical `Why::delta`) violates `delta_absorb` – `Why` is
not absorptive – so `δ` collapses group existence to a bare "exists". -/
private def Why.deltaInd (a : Why α) : Why α :=
  ⟨{s | s = ∅ ∧ a.carrier.Nonempty}⟩

private lemma Why.deltaInd_zero : Why.deltaInd (0 : Why α) = 0 := by
  ext z
  show z ∈ {s | s = ∅ ∧ (∅ : Set (Set α)).Nonempty} ↔ z ∈ (∅ : Set (Set α))
  simp

private lemma Why.carrier_nonempty_of_ne {a : Why α} (h : a ≠ 0) :
    a.carrier.Nonempty := by
  rcases Set.eq_empty_or_nonempty a.carrier with he | hne
  · exact absurd (by ext z; rw [he]; exact Iff.rfl) h
  · exact hne

private lemma Why.deltaInd_of_ne {a : Why α} (h : a ≠ 0) :
    Why.deltaInd a = 1 := by
  ext z
  show z ∈ {s | s = ∅ ∧ a.carrier.Nonempty} ↔ z ∈ ({∅} : Set (Set α))
  simp [Why.carrier_nonempty_of_ne h]

private lemma Why.zsf {a b : Why α} (h : a + b = 0) : a = 0 := by
  have hc : a.carrier ∪ b.carrier = (∅ : Set (Set α)) :=
    congrArg Why.carrier h
  have hx : a.carrier = ∅ := by
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    have hmem : w ∈ a.carrier ∪ b.carrier := Set.mem_union_left _ hw
    rw [hc] at hmem
    exact hmem
  ext z
  rw [hx]
  exact Iff.rfl

private lemma Why.sum_eq_zero_iff (t : Multiset (Why α)) :
    t.sum = 0 ↔ ∀ a ∈ t, a = 0 := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.sum_cons]
    constructor
    · intro h x hx
      have ha : a = 0 := Why.zsf h
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact ha
      · rw [ha, zero_add] at h
        exact ih.mp h x hx
    · intro h
      rw [h a (Multiset.mem_cons_self a t), zero_add,
        ih.mpr fun x hx => h x (Multiset.mem_cons_of_mem hx)]

private lemma Why.one_ne_zero' : (1 : Why α) ≠ 0 := by
  intro h
  have := congrArg Why.carrier h
  exact Set.singleton_ne_empty (∅ : Set α) this

/-- Why-provenance is a semiring with monus: `∖` is set difference on the outer
level, `2^(2^X)` ordered by inclusion.

Named explicitly, and not to be renamed: this name is published as a link target
in [Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*, ICDE 2026][sen2026provsql]. -/
instance instSemiringWithMonusWhy : SemiringWithMonus (Why α) where
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

  /- δ is the support indicator (see `Why.deltaInd`). -/
  delta := Why.deltaInd
  delta_zero := Why.deltaInd_zero
  delta_natCast_pos :=
    let hidem : idempotent (Why α) := fun a => by simp [(· + ·), Add.add]
    fun hn => by
      rw [natCast_pos_eq_one_of_idempotent hidem hn,
        Why.deltaInd_of_ne Why.one_ne_zero']
  delta_regrouping := fun s => by
    by_cases hz : s.sum = 0
    · have hmap : (s.map Why.deltaInd).sum = 0 :=
        (Why.sum_eq_zero_iff _).mpr fun x hx => by
          obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
          rw [(Why.sum_eq_zero_iff s).mp hz a ha, Why.deltaInd_zero]
      rw [hz, hmap, Why.deltaInd_zero]
    · have hmapne : (s.map Why.deltaInd).sum ≠ 0 := by
        intro h
        apply hz
        refine (Why.sum_eq_zero_iff s).mpr fun a ha => ?_
        have hda := (Why.sum_eq_zero_iff _).mp h _
          (Multiset.mem_map_of_mem _ ha)
        by_contra hane
        rw [Why.deltaInd_of_ne hane] at hda
        exact Why.one_ne_zero' hda
      rw [Why.deltaInd_of_ne hmapne, Why.deltaInd_of_ne hz]
  delta_absorb := fun a b => by
    by_cases ha : a = 0
    · rw [ha, zero_mul]
    · have habne : a + b ≠ 0 := fun h => ha (Why.zsf h)
      rw [Why.deltaInd_of_ne habne, mul_one]

instance : CommSemiringWithMonus (Why α) where
  mul_comm := mul_comm

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

/-- **The `=`-comparison correspondence fails in `Why[X]`.** For a
three-tuple group with occurrence annotations `t₁`, `t₂`, `t₃`, the fused
`HAVING (COUNT(*) = 2)` predicate provenance is
`(t₁ ⊗ t₂) ⊗ (𝟙 ⊖ t₃) ⊕ (t₁ ⊗ t₃) ⊗ (𝟙 ⊖ t₂) ⊕ (t₂ ⊗ t₃) ⊗ (𝟙 ⊖ t₁)`,
while the join-based rewriting `Q₂^{≥2} − Q₂^{≥3}` annotates the key with
`((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)) ⊖ (t₁ ⊗ t₂ ⊗ t₃)`. In `Why[X]` –
idempotent, but without distributivity of `⊗` over `⊖`
(`Why.not_mul_sub_left_distributive`) – the two disagree: with
`t₁ = t₂ = t₃ = ⟨{{a}}⟩` for any witness `a`, every product equals
`⟨{{a}}⟩` and every factor `𝟙 ⊖ tᵢ` equals `𝟙` (as `∅ ∉ {{a}}`), so the
fused side keeps the witness, `⟨{{a}}⟩`, while on the join side the
difference of the two `≥`-chains cancels it:
`⟨{{a}}⟩ ⊖ ⟨{{a}}⟩ = 𝟘`. -/
theorem Why.counterexample_having [Inhabited α] :
    ∃ t₁ t₂ t₃ : Why α,
      (t₁ * t₂) * (1 - t₃) + (t₁ * t₃) * (1 - t₂) + (t₂ * t₃) * (1 - t₁)
        ≠ (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) - t₁ * t₂ * t₃ := by
  refine ⟨⟨{{default}}⟩, ⟨{{default}}⟩, ⟨{{default}}⟩, ?_⟩
  have hmul : (⟨{{default}}⟩ : Why α) * ⟨{{default}}⟩ = ⟨{{default}}⟩ := by
    ext z
    show (∃ x y : Set α, x ∈ ({{default}} : Set (Set α))
        ∧ y ∈ ({{default}} : Set (Set α)) ∧ z = x ∪ y)
      ↔ z ∈ ({{default}} : Set (Set α))
    constructor
    · rintro ⟨x, y, hx, hy, rfl⟩
      simp only [Set.mem_singleton_iff] at hx hy ⊢
      rw [hx, hy, Set.union_self]
    · intro hz
      simp only [Set.mem_singleton_iff] at hz
      exact ⟨{default}, {default}, rfl, rfl, by rw [hz, Set.union_self]⟩
  have hone : (1 : Why α) - ⟨{{default}}⟩ = 1 := by
    ext z
    show z ∈ (({∅} : Set (Set α)) \ {{default}}) ↔ z ∈ ({∅} : Set (Set α))
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun hz => ?_⟩
      simp only [Set.mem_singleton_iff] at h hz
      rw [h] at hz
      exact (Set.singleton_ne_empty (default : α)) hz.symm
  have haa : ∀ a : Why α, a + a = a := by
    intro a
    ext z
    show z ∈ a.carrier ∪ a.carrier ↔ z ∈ a.carrier
    rw [Set.union_self]
  have hsub : (⟨{{default}}⟩ : Why α) - ⟨{{default}}⟩ = 0 := by
    ext z
    show z ∈ (({{default}} : Set (Set α)) \ {{default}}) ↔ z ∈ (∅ : Set (Set α))
    rw [Set.sdiff_self]
  simp only [hmul, hone, mul_one, haa, hsub]
  intro h
  have hcarr := congrArg Why.carrier h
  exact (Set.singleton_ne_empty ({default} : Set α)) hcarr
