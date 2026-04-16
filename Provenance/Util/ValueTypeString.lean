import Mathlib.Algebra.Group.Defs
import Mathlib.Data.String.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.IntervalCases

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

private theorem Nat.toDigitsCore_append_aux (fuel n : Nat) (ds : List Char) :
    Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds := by
  induction fuel generalizing n ds with
  | zero => simp [Nat.toDigitsCore]
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    by_cases h : n / 10 = 0
    · simp [h]
    · simp [h]
      rw [ih (n/10) (Nat.digitChar (n%10) :: ds)]
      rw [ih (n/10) [Nat.digitChar (n%10)]]
      simp [List.append_assoc]

private theorem Nat.toDigitsCore_fuel_eq (n : Nat) :
    ∀ fuel₁ fuel₂, n + 1 ≤ fuel₁ → n + 1 ≤ fuel₂ →
      Nat.toDigitsCore 10 fuel₁ n [] = Nat.toDigitsCore 10 fuel₂ n [] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fuel₁ fuel₂ h₁ h₂
    obtain ⟨f₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel₁ ≠ 0)
    obtain ⟨f₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel₂ ≠ 0)
    by_cases hn : n / 10 = 0
    · simp [Nat.toDigitsCore, hn]
    · have h_n_ge_10 : 10 ≤ n := by
        by_contra hc
        push_neg at hc
        have : n / 10 = 0 := Nat.div_eq_of_lt hc
        contradiction
      have h_div_lt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      simp only [Nat.toDigitsCore, hn, ↓reduceIte]
      rw [Nat.toDigitsCore_append_aux f₁ (n/10) _]
      rw [Nat.toDigitsCore_append_aux f₂ (n/10) _]
      congr 1
      apply ih (n/10) h_div_lt <;> omega

private theorem Nat.toDigits_recursion (n : Nat) (h : 10 ≤ n) :
    Nat.toDigits 10 n = Nat.toDigits 10 (n/10) ++ [Nat.digitChar (n%10)] := by
  have hn : n / 10 ≠ 0 := by
    intro hd
    have := Nat.div_eq_of_lt (a := n) (b := 10)
    omega
  unfold Nat.toDigits
  conv_lhs => unfold Nat.toDigitsCore
  simp only [hn, ↓reduceIte]
  rw [Nat.toDigitsCore_append_aux n (n/10) _]
  rw [Nat.toDigitsCore_fuel_eq (n/10) n (n/10+1) (by omega) (by omega)]

private theorem Nat.toDigits_lt_10 (n : Nat) (h : n < 10) :
    Nat.toDigits 10 n = [Nat.digitChar n] := by
  unfold Nat.toDigits
  unfold Nat.toDigitsCore
  simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]

private lemma Nat.digitChar_isDigit (d : Nat) (h : d < 10) :
    (Nat.digitChar d).isDigit = true := by
  unfold Nat.digitChar
  interval_cases d <;> decide

private lemma Nat.digitChar_toNat_sub (d : Nat) (h : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  unfold Nat.digitChar
  show _ - 48 = _
  interval_cases d <;> decide

private theorem Nat.toDigits_all_isDigit (n : Nat) :
    ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc
    by_cases h10 : n < 10
    · rw [Nat.toDigits_lt_10 n h10] at hc
      simp at hc
      rw [hc]
      exact Nat.digitChar_isDigit n h10
    · push_neg at h10
      rw [Nat.toDigits_recursion n h10] at hc
      rw [List.mem_append] at hc
      cases hc with
      | inl hin => exact ih (n/10) (Nat.div_lt_self (by omega) (by omega)) c hin
      | inr hin =>
        simp at hin
        rw [hin]
        exact Nat.digitChar_isDigit (n%10) (Nat.mod_lt _ (by omega))

private theorem Nat.toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  by_cases h10 : n < 10
  · rw [Nat.toDigits_lt_10 n h10]; simp
  · push_neg at h10
    rw [Nat.toDigits_recursion n h10]; simp

private theorem Nat.toDigits_foldl (n : Nat) :
    (Nat.toDigits 10 n).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h10 : n < 10
    · rw [Nat.toDigits_lt_10 n h10]
      simp only [List.foldl_cons, List.foldl_nil, zero_mul, zero_add]
      exact Nat.digitChar_toNat_sub n h10
    · push_neg at h10
      rw [Nat.toDigits_recursion n h10]
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (n/10) (Nat.div_lt_self (by omega) (by omega))]
      rw [Nat.digitChar_toNat_sub (n%10) (Nat.mod_lt _ (by omega))]
      omega

lemma toNat_reprStr : ∀ n : ℕ, (Nat.repr n).toNat? = some n := by
  intro n
  unfold String.toNat?
  have hisNat : (Nat.repr n).isNat = true := by
    unfold String.isNat
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have hne : Nat.repr n ≠ "" := by
        unfold Nat.repr
        rw [Ne, String.ofList_eq_empty_iff]
        exact Nat.toDigits_ne_nil n
      have : (Nat.repr n).isEmpty = false := by
        rw [Bool.eq_false_iff, Ne, String.isEmpty_iff]
        exact hne
      simp [this]
    · rw [String.all_eq]
      unfold Nat.repr
      rw [String.toList_ofList, List.all_eq_true]
      intro c hc
      exact Nat.toDigits_all_isDigit n c hc
  rw [if_pos hisNat]
  congr 1
  rw [String.foldl_eq]
  unfold Nat.repr
  rw [String.toList_ofList]
  exact Nat.toDigits_foldl n

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
