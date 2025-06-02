import Mathlib.Algebra.Group.Defs
import Mathlib.Data.String.Basic

import Provenance.Util.ValueType

instance : Zero String where
  zero := "0"

instance: Add String where
  add s t := match s.toNat? with
  | none => ""
  | some n => match t.toNat? with
              | none => ""
              | some m => toString (n+m)

instance: Sub String where
  sub _ _ := ""

instance: Mul String where
  mul _ _ := ""

lemma toNat_toString : ∀ n : ℕ, (toString (n)).toNat? = some n := by
  intro n
  induction n with
  | zero =>
    have : toString (0) = "0":= by decide
    rw[this]
    simp[String.toNat?]
    constructor
    . admit
    . admit
  | succ n ih =>
    admit

instance: ValueType String where
  add_comm := by
    intro a b
    have hes: "".toNat? = none := rfl
    by_cases ha: a.toNat?=none <;>
    by_cases hb: b.toNat?=none <;>
    simp[HAdd.hAdd] <;> simp only[Add.add] <;> try simp[ha,hb,hes]
    . cases hb': b.toNat? with
      | none => contradiction
      | some val => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala =>
        cases hb': b.toNat? with
        | none => contradiction
        | some valb =>
          simp
          rw[Nat.add_comm]

  add_assoc := by
    intro a b c
    have hes: "".toNat? = none := rfl
    by_cases ha: a.toNat?=none <;>
    by_cases hb: b.toNat?=none <;>
    by_cases hc: c.toNat?=none <;>
    simp[HAdd.hAdd] <;> simp only[Add.add] <;> try simp[ha,hb,hc,hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some val => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala => simp[hes]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala =>
        cases hb': b.toNat? with
        | none => contradiction
        | some valb =>
          simp[hes]
          cases hx: (toString (vala+valb)).toNat? <;> simp[hx]
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala =>
        cases hb': b.toNat? with
        | none => contradiction
        | some valb =>
          cases hc': c.toNat? with
          | none => contradiction
          | some valc =>
            simp[toNat_toString]
            rw[Nat.add_assoc]
