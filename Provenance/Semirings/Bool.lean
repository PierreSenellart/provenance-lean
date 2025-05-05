import Provenance.SemiringWithMonus

instance : CommSemiring Bool where
  add := Bool.or
  mul := Bool.and
  zero := Bool.false
  one := Bool.true
  add_assoc := Bool.or_assoc
  add_comm := Bool.or_comm
  zero_add := Bool.false_or
  add_zero := Bool.or_false
  mul_assoc := Bool.and_assoc
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := Bool.and_or_distrib_left
  right_distrib := Bool.and_or_distrib_right
  zero_mul := Bool.false_and
  mul_zero := Bool.and_false
  mul_comm := Bool.and_comm
  nsmul (n: Nat) (b: Bool) :=
    if n = 0 then Bool.false else b
  nsmul_succ := by {
    intro n b
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇
    . tauto
    . tauto
    . tauto
    . tauto
    . tauto
    . tauto
    . tauto
    . change (b = (b || b))
      simp
  }

instance : SemiringWithMonus Bool where
  -- natural order
  le_self_add := by {
    intro a b
    induction a with
    | true =>
      tauto
    | false =>
      tauto
  }

  add_le_add_left := by {
    intro a b h c
    induction a with
    | true =>
      induction b with
      | true => tauto
      | false => tauto
    | false =>
      induction c with
      | true => tauto
      | false => tauto
  }

  exists_add_of_le := by {
    intro a b h
    rw[le_iff_exists_sup] at h
    exact h
  }

  -- monus
  sub (a b : Bool) := a && !b

  monus_spec := by {
    intro a b c
    apply Iff.intro

    . intro h
      induction a with
      | true =>
        induction b with
        | true => tauto
        | false => tauto
      | false => tauto

    . intro h
      induction a with
      | true =>
        induction b with
        | true => tauto
        | false => tauto
      | false => tauto
  }
