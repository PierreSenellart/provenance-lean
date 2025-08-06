import Provenance.SemiringWithMonus

instance : SemiringWithMonus Nat where
  monus_spec := by
    intro a b c
    apply Iff.intro
    . intro h
      simp at h
      rw[add_comm]
      exact h

    . intro h
      induction b with
      | zero =>
        simp at h
        simp[h]
      | succ n ih =>
        apply eq_or_lt_of_le at h
        cases h with
        | inl hl =>
          simp[hl]
        | inr hr =>
          rw[add_comm, ← add_assoc] at hr
          apply Nat.le_of_lt_succ at hr
          rw[add_comm] at hr
          have h : a - n ≤ c := by {
            apply ih
            exact hr
          }
          simp at h
          simp
          apply Nat.le_succ_of_le
          exact h

instance : HasAltLinearOrder Nat where
  altOrder := inferInstance
