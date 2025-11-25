import Mathlib.Algebra.Group.Defs
import Mathlib.Data.String.Basic

import Provenance.Util.ValueType

instance : Zero String where
  zero := Nat.repr 0

instance: Add String where
  add s t := match s.toNat? with
  | none => ""
  | some n => match t.toNat? with
              | none => ""
              | some m => Nat.repr (n+m)

instance: Sub String where
  sub _ _ := ""

instance: Mul String where
  mul _ _ := ""

#find (Nat.repr _).toNat?

lemma toNat_reprStr : ∀ n : ℕ, (Nat.repr n).toNat? = some n := by
  intro n
  induction n with
  | zero =>
    simp[String.toNat?]
    constructor
    . simp[String.isNat]
      constructor
      . decide
      . apply String.all_eq
    . apply String.foldl_eq
  | succ n ih =>
    sorry

instance: ValueType String where
  add_comm := by
    intro a b
    have hes: "".toNat? = none := rfl
    by_cases ha: a.toNat?=none <;>
    by_cases hb: b.toNat?=none <;>
    simp[HAdd.hAdd] <;> simp only[Add.add] <;> try simp[ha,hb]
    . cases hb': b.toNat? with
      | none => contradiction
      | some val => simp
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala => simp
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
          cases hx: (Nat.repr (vala+valb)).toNat? <;> simp
    . cases ha': a.toNat? with
      | none => contradiction
      | some vala =>
        cases hb': b.toNat? with
        | none => contradiction
        | some valb =>
          cases hc': c.toNat? with
          | none => contradiction
          | some valc =>
            simp[toNat_reprStr]
            rw[Nat.add_assoc]
