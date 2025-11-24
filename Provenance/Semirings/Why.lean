import Provenance.SemiringWithMonus

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
    apply Iff.intro
    . intro hx
      by_cases h: x ∈ a.carrier
      . left
        assumption
      . right
        constructor <;> assumption
    . intro hx
      by_cases h: x ∈ a.carrier
      . exact hab h
      . simp[h] at hx
        assumption

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

theorem Why.idempotent : idempotent (Why α) := by
  intro a
  simp[(· + ·), Add.add]

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
