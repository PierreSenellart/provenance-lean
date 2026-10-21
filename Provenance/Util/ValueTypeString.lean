module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.String.Basic

public import Provenance.Util.ValueType
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Strings as a value domain

The worked examples read a relation of strings, and a sum of two of them
is their decimal reading added. The reading is `strToNat?`, which walks
the characters of the string structurally rather than calling
`String.toNat?`: the latter goes through the slice API, which is defined
by well-founded recursion and does not reduce in the kernel, so an
equation about a computed relation over this domain could not be closed
by `decide`. Everything here reduces, which is what makes
`Provenance.Example`'s checks theorems.
-/

@[expose] public section

namespace ValueTypeString

/-- Whether every character of a list is a decimal digit. -/
def allDigits : List Char → Bool
  | [] => true
  | c :: t => c.isDigit && allDigits t

/-- The value of a decimal numeral, read most significant digit first
into an accumulator. -/
def digitsVal : List Char → ℕ → ℕ
  | [], acc => acc
  | c :: t, acc => digitsVal t (acc * 10 + (c.toNat - 48))

/-- **The decimal reading of a string**: its value where it is a
non-empty run of digits, and nothing otherwise. This is `String.toNat?`
read off the characters, so that the kernel reduces it. -/
def strToNat? (s : String) : Option ℕ :=
  match s.toList with
  | [] => none
  | l => if allDigits l then some (digitsVal l 0) else none

@[simp] theorem strToNat?_empty : strToNat? "" = none := rfl

private theorem allDigits_append (l₁ l₂ : List Char) :
    allDigits (l₁ ++ l₂) = (allDigits l₁ && allDigits l₂) := by
  induction l₁ with
  | nil => rfl
  | cons c t ih => rw [List.cons_append, allDigits, allDigits, ih, Bool.and_assoc]

private theorem digitsVal_append (l₁ l₂ : List Char) (acc : ℕ) :
    digitsVal (l₁ ++ l₂) acc = digitsVal l₂ (digitsVal l₁ acc) := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons c t ih => rw [List.cons_append, digitsVal, digitsVal, ih]

/-! ## Printing a number

The domain prints numbers with its own copy of `Nat.repr`. The core
printer is not exposed to other modules, so a computation through it
does not reduce there; this one is, which keeps the worked examples
decidable. -/

/-- The decimal digit `d`, for `d < 10`. -/
def digitChar (d : ℕ) : Char := Char.ofNat (48 + d)

/-- `Nat.toDigitsCore` in base ten: prepend to `ds` the decimal digits of
`n`, most significant first, within `fuel` steps. -/
def toDigitsCore : ℕ → ℕ → List Char → List Char
  | 0, _, ds => ds
  | fuel + 1, n, ds =>
    if n / 10 = 0 then digitChar (n % 10) :: ds
    else toDigitsCore fuel (n / 10) (digitChar (n % 10) :: ds)

/-- The decimal numeral of `n`, as `Nat.repr` prints it. -/
def numeral (n : ℕ) : String := String.ofList (toDigitsCore (n + 1) n [])

private theorem isDigit_digitChar {d : ℕ} (h : d < 10) :
    (digitChar d).isDigit = true :=
  have hall : ∀ e : Fin 10, (digitChar e.val).isDigit = true := by decide
  hall ⟨d, h⟩

private theorem toNat_digitChar {d : ℕ} (h : d < 10) :
    (digitChar d).toNat - 48 = d :=
  have hall : ∀ e : Fin 10, (digitChar e.val).toNat - 48 = e.val := by decide
  hall ⟨d, h⟩

/-- **What the digits of a number read back as.** The characters
`toDigitsCore` prepends are digits, and reading them most significant
first multiplies the accumulator by a power of ten and adds the number
back. -/
private theorem toDigitsCore_spec : ∀ (fuel : ℕ), 0 < fuel → ∀ n : ℕ, n < 10 ^ fuel →
    ∃ k, 0 < k ∧ ∀ ds : List Char,
      allDigits (toDigitsCore fuel n ds) = allDigits ds
        ∧ (∀ acc, digitsVal (toDigitsCore fuel n ds) acc
            = digitsVal ds (acc * 10 ^ k + n))
        ∧ (toDigitsCore fuel n ds).length = k + ds.length := by
  intro fuel
  induction fuel with
  | zero => intro hf; exact absurd hf (Nat.lt_irrefl 0)
  | succ fuel ih =>
    intro _ n hn
    have hmod : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
    by_cases hx : n / 10 = 0
    · refine ⟨1, Nat.one_pos, fun ds => ?_⟩
      have hn10 : n < 10 := Nat.lt_of_div_eq_zero (by norm_num) hx
      have hself : n % 10 = n := Nat.mod_eq_of_lt hn10
      refine ⟨?_, ?_, ?_⟩
      · rw [show toDigitsCore (fuel + 1) n ds
              = digitChar (n % 10) :: ds from by
            simp only [toDigitsCore, hx, ite_true], allDigits,
          isDigit_digitChar hmod, Bool.true_and]
      · intro acc
        rw [show toDigitsCore (fuel + 1) n ds
              = digitChar (n % 10) :: ds from by
            simp only [toDigitsCore, hx, ite_true], digitsVal,
          toNat_digitChar hmod, hself, pow_one]
      · rw [show toDigitsCore (fuel + 1) n ds
              = digitChar (n % 10) :: ds from by
            simp only [toDigitsCore, hx, ite_true], List.length_cons,
          Nat.add_comm]
    · have hlt : n / 10 < 10 ^ fuel := by
        rw [pow_succ, Nat.mul_comm] at hn
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hn ⊢; exact hn)
      have hfuel : 0 < fuel := by
        rcases Nat.eq_zero_or_pos fuel with rfl | hp
        · exact absurd (Nat.lt_one_iff.mp (by simpa using hlt)) hx
        · exact hp
      obtain ⟨k, hk, hspec⟩ := ih hfuel (n / 10) hlt
      refine ⟨k + 1, Nat.succ_pos k, fun ds => ?_⟩
      have hunf : toDigitsCore (fuel + 1) n ds
          = toDigitsCore fuel (n / 10) (digitChar (n % 10) :: ds) := by
        simp only [toDigitsCore, hx, ite_false]
      obtain ⟨hall, hval, hlen⟩ := hspec (digitChar (n % 10) :: ds)
      refine ⟨?_, ?_, ?_⟩
      · rw [hunf, hall, allDigits, isDigit_digitChar hmod, Bool.true_and]
      · intro acc
        rw [hunf, hval acc, digitsVal, toNat_digitChar hmod]
        congr 1
        rw [pow_succ, ← Nat.mul_assoc, Nat.add_mul, Nat.mul_comm (n / 10) 10,
          Nat.add_assoc, show 10 * (n / 10) + n % 10 = n from by omega]
      · rw [hunf, hlen, List.length_cons, Nat.add_assoc, Nat.add_comm 1 ds.length,
          ← Nat.add_assoc]

/-- **The reading of a string that is a non-empty run of digits.** -/
private theorem strToNat?_of_digits {s : String} {c : Char} {t : List Char}
    (hs : s.toList = c :: t) (hall : allDigits (c :: t) = true) :
    strToNat? s = some (digitsVal (c :: t) 0) := by
  unfold strToNat?
  rw [hs]
  exact ite_eq_left hall

/-- **A number reads back as itself.** This is `Nat.toNat?_repr` for the
structural reading and the printer above. -/
theorem strToNat?_numeral (n : ℕ) : strToNat? (numeral n) = some n := by
  have hbound : n < 10 ^ (n + 1) :=
    lt_of_lt_of_le (Nat.lt_pow_self (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
  obtain ⟨k, hk, hspec⟩ := toDigitsCore_spec (n + 1) (Nat.succ_pos n) n hbound
  obtain ⟨hall, hval, hlen⟩ := hspec []
  have hd : (numeral n).toList = toDigitsCore (n + 1) n [] := by
    rw [numeral, String.toList_ofList]
  cases hl : toDigitsCore (n + 1) n [] with
  | nil =>
    rw [hl] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons c t =>
    have hallT : allDigits (c :: t) = true := by rw [← hl, hall]; rfl
    have hvalT : digitsVal (c :: t) 0 = n := by
      rw [← hl, hval 0]
      show 0 * 10 ^ k + n = n
      omega
    rw [strToNat?_of_digits (by rw [hd, hl]) hallT, hvalT]

/-! ## The value domain

Zero is the numeral `0`, a sum is the sum of the two readings printed
back, and a string that is not a numeral reads as nothing – which makes
the sum the empty string, as the domain's own arithmetic has it. -/

instance : Zero String where
  zero := numeral 0

instance : Add String where
  add s t := match strToNat? s with
    | none => ""
    | some n => match strToNat? t with
                | none => ""
                | some m => numeral (n + m)

private theorem add_def (s t : String) :
    s + t = (match strToNat? s with
      | none => ""
      | some n => match strToNat? t with
                  | none => ""
                  | some m => numeral (n + m)) := rfl

theorem add_of_left_none {a b : String} (h : strToNat? a = none) :
    a + b = "" := by rw [add_def, h]

theorem add_of_right_none {a b : String} {n : ℕ} (ha : strToNat? a = some n)
    (hb : strToNat? b = none) : a + b = "" := by rw [add_def, ha, hb]

theorem add_eq_repr {a b : String} {n m : ℕ} (ha : strToNat? a = some n)
    (hb : strToNat? b = some m) : a + b = numeral (n + m) := by
  rw [add_def, ha, hb]

instance : Sub String where
  sub _ _ := ""

instance : Mul String where
  mul _ _ := ""

instance : ValueType String where
  nonzero := numeral 1
  nonzero_ne_zero := by decide
  add_comm := by
    intro a b
    rcases ha : strToNat? a with _ | n
    · rw [add_of_left_none ha]
      rcases hb : strToNat? b with _ | m
      · rw [add_of_left_none hb]
      · rw [add_of_right_none hb ha]
    · rcases hb : strToNat? b with _ | m
      · rw [add_of_right_none ha hb, add_of_left_none hb]
      · rw [add_eq_repr ha hb, add_eq_repr hb ha, Nat.add_comm]
  add_assoc := by
    intro a b c
    rcases ha : strToNat? a with _ | n
    · rw [add_of_left_none ha, add_of_left_none strToNat?_empty,
        add_of_left_none ha]
    · rcases hb : strToNat? b with _ | m
      · rw [add_of_right_none ha hb, add_of_left_none strToNat?_empty,
          add_of_left_none hb, add_of_right_none ha strToNat?_empty]
      · rcases hc : strToNat? c with _ | k
        · rw [add_eq_repr ha hb, add_of_right_none (strToNat?_numeral (n + m)) hc,
            add_of_right_none hb hc, add_of_right_none ha strToNat?_empty]
        · rw [add_eq_repr ha hb, add_eq_repr hb hc,
            add_eq_repr (strToNat?_numeral (n + m)) hc,
            add_eq_repr ha (strToNat?_numeral (m + k)), Nat.add_assoc]

/-- The string domain has no null: `WithNull String` is how a nullable
column of strings is modeled. -/
instance : NoNulls String := ⟨fun _ => rfl⟩

end ValueTypeString
