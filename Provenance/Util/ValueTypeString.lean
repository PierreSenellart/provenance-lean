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

/-! ### Bridging `String.foldl` / `String.Slice.foldl` to `List.foldl`

In Lean 4.29 `String.foldl` is defined through `String.Slice.foldl`, which itself
is `Std.Iter.fold` over the iterator of characters. We restate it as a `List.foldl`
on `toList` to reuse standard list-induction arguments. -/

private theorem Slice.foldl_eq_copy_toList_foldl
    {α : Type u} (f : α → Char → α) (init : α) (s : String.Slice) :
    s.foldl f init = s.copy.toList.foldl f init := by
  show Std.Iter.fold f init s.chars = _
  rw [← Std.Iter.foldl_toList, String.Slice.toList_chars]

private theorem String.foldl_eq_toList_foldl
    {α : Type u} (f : α → Char → α) (init : α) (s : String) :
    s.foldl f init = s.toList.foldl f init := by
  show s.toSlice.foldl f init = _
  rw [Slice.foldl_eq_copy_toList_foldl, String.copy_toSlice]

/-! ### `Nat.repr n` has no underscores: parsing reduces to digit folds -/

/-- A digit character is not the underscore. -/
private lemma digitChar_ne_underscore (d : Nat) (h : d < 10) :
    Nat.digitChar d ≠ '_' := by
  unfold Nat.digitChar
  interval_cases d <;> decide

/-- Every character in `Nat.toDigits 10 n` is different from `'_'`. -/
private theorem Nat.toDigits_no_underscore (n : Nat) :
    ∀ c ∈ Nat.toDigits 10 n, c ≠ '_' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc
    by_cases h10 : n < 10
    · rw [Nat.toDigits_lt_10 n h10] at hc
      simp at hc; subst hc
      exact digitChar_ne_underscore n h10
    · push_neg at h10
      rw [Nat.toDigits_recursion n h10] at hc
      rw [List.mem_append] at hc
      cases hc with
      | inl hin => exact ih (n/10) (Nat.div_lt_self (by omega) (by omega)) c hin
      | inr hin =>
        simp at hin; subst hin
        exact digitChar_ne_underscore (n%10) (Nat.mod_lt _ (by omega))

/-- For a list of characters none of which is `'_'`, folding with the underscore-
skipping step is the same as folding with the unconditional digit step. -/
private lemma List.foldl_digit_no_underscore (l : List Char)
    (h : ∀ c ∈ l, c ≠ '_') (init : Nat) :
    l.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) init
      = l.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd : hd ≠ '_' := h hd List.mem_cons_self
    have h_tl : ∀ c ∈ tl, c ≠ '_' := fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [List.foldl_cons, if_neg h_hd]
    exact ih h_tl _

/-! ### Tracking the four-tuple state of `String.Slice.isNat` -/

/-- Step function inlined from `String.Slice.isNat` (kept abstract here so we
can talk about the iteration state explicitly). -/
private def isNatStep
    (st : Bool × Bool × Bool × Bool) (c : Char) : Bool × Bool × Bool × Bool :=
  let (isFirst, lastWasUnderscore, _lastCharWasDigit, valid) := st
  let isDigit := c.isDigit
  let isUnderscore := c = '_'
  let newValid := valid && (isDigit || isUnderscore) &&
                  !(isFirst && isUnderscore) &&
                  !(lastWasUnderscore && isUnderscore)
  (false, isUnderscore, isDigit, newValid)

/-- A digit character is not the underscore (consequence of being a decimal digit). -/
private lemma not_underscore_of_isDigit {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  intro hc
  rw [hc] at h
  simp at h

/-- On a list of digits (no underscores), the state stays `(false, false, true, true)`
once we have processed at least one character. -/
private lemma foldl_isNatStep_digits_steady (l : List Char)
    (h_dig : ∀ c ∈ l, c.isDigit = true) :
    l.foldl isNatStep (false, false, true, true) = (false, false, true, true) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hd_digit : hd.isDigit = true := h_dig hd List.mem_cons_self
    have tl_dig : ∀ c ∈ tl, c.isDigit = true :=
      fun c hc => h_dig c (List.mem_cons_of_mem _ hc)
    have hd_not_us : hd ≠ '_' := not_underscore_of_isDigit hd_digit
    have hus : (decide (hd = '_')) = false := decide_eq_false hd_not_us
    simp only [List.foldl_cons, isNatStep, hd_digit, hus]
    simp
    exact ih tl_dig

/-- For a non-empty list of digits, the full fold starting from the initial
state ends in `(false, false, true, true)`. -/
private lemma foldl_isNatStep_digits (l : List Char) (h_ne : l ≠ [])
    (h_dig : ∀ c ∈ l, c.isDigit = true) :
    l.foldl isNatStep (true, false, false, true) = (false, false, true, true) := by
  cases l with
  | nil => exact absurd rfl h_ne
  | cons hd tl =>
    have hd_digit : hd.isDigit = true := h_dig hd List.mem_cons_self
    have tl_dig : ∀ c ∈ tl, c.isDigit = true :=
      fun c hc => h_dig c (List.mem_cons_of_mem _ hc)
    have hd_not_us : hd ≠ '_' := not_underscore_of_isDigit hd_digit
    simp only [List.foldl_cons, isNatStep]
    have hus : (decide (hd = '_')) = false := decide_eq_false hd_not_us
    simp [hd_digit, hus]
    exact foldl_isNatStep_digits_steady tl tl_dig

lemma toNat_reprStr : ∀ n : ℕ, (Nat.repr n).toNat? = some n := by
  intro n
  -- Reduce to the slice-level definition.
  show (Nat.repr n).toSlice.toNat? = some n
  unfold String.Slice.toNat?
  -- The `isNat` check succeeds because `Nat.repr n` consists of digit characters.
  have hisNat : (Nat.repr n).toSlice.isNat = true := by
    unfold String.Slice.isNat
    -- The string is non-empty.
    have hne : (Nat.repr n) ≠ "" := by
      unfold Nat.repr
      rw [Ne, String.ofList_eq_empty_iff]
      exact Nat.toDigits_ne_nil n
    have hempty : (Nat.repr n).toSlice.isEmpty = false := by
      rw [String.isEmpty_toSlice]
      rw [Bool.eq_false_iff]
      simpa [String.isEmpty_iff] using hne
    rw [hempty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Reduce the slice foldl to a List foldl on `(Nat.repr n).toList`.
    have hfold :
        (Nat.repr n).toSlice.foldl
            (fun (isFirst, lastWasUnderscore, _lastCharWasDigit, valid) c =>
              let isDigit := c.isDigit
              let isUnderscore := c = '_'
              let newValid := valid && (isDigit || isUnderscore) &&
                              !(isFirst && isUnderscore) &&
                              !(lastWasUnderscore && isUnderscore)
              (false, isUnderscore, isDigit, newValid))
            (true, false, false, true)
          = (Nat.repr n).toList.foldl isNatStep (true, false, false, true) := by
      rw [Slice.foldl_eq_copy_toList_foldl, String.copy_toSlice]
      rfl
    rw [hfold]
    -- The foldl over digit characters yields the "valid, non-empty digit" state.
    have hne_list : (Nat.repr n).toList ≠ [] := by
      unfold Nat.repr; rw [String.toList_ofList]; exact Nat.toDigits_ne_nil n
    have hdig : ∀ c ∈ (Nat.repr n).toList, c.isDigit = true := by
      unfold Nat.repr; rw [String.toList_ofList]; exact Nat.toDigits_all_isDigit n
    rw [foldl_isNatStep_digits _ hne_list hdig]
    rfl
  rw [if_pos hisNat]
  -- Now reduce the parsing fold to the standard digit fold.
  congr 1
  rw [Slice.foldl_eq_copy_toList_foldl, String.copy_toSlice]
  have hnous : ∀ c ∈ (Nat.repr n).toList, c ≠ '_' := by
    unfold Nat.repr; rw [String.toList_ofList]; exact Nat.toDigits_no_underscore n
  rw [List.foldl_digit_no_underscore _ hnous]
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
