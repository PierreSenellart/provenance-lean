import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind

class ValueType (T : Type) extends Zero T, LinearOrder T

variable {T: Type} [ValueType T]

instance : DecidableRel ((· : T) ≠ ·) :=
  λ a b =>
    match inferInstanceAs (Decidable (a = b)) with
    | isTrue h  => isFalse (by simp[h])
    | isFalse h => isTrue  (by simp[h])

instance : DecidableRel ((· : T) < ·) :=
  λ a b =>
    match inferInstanceAs (Decidable (a ≤ b)), inferInstanceAs (Decidable (a = b)) with
    | isTrue h₁, isTrue h₂  => isFalse (by simp[h₂])
    | isTrue h₁, isFalse h₂ => isTrue  (lt_of_le_of_ne h₁ h₂)
    | isFalse h₁, _         => isFalse (by contrapose h₁; simp at *; exact le_of_lt h₁)

abbrev Tuple (T : Type) (n: ℕ) := Vector T n

instance : Std.Irrefl (λ (a b: T) ↦ a < b) where
  irrefl := by simp

instance : Std.Antisymm (fun (a b: T) ↦ ¬a < b) where
  antisymm := by
    intro a b hab hba
    have hab' := le_of_not_lt hab
    have hbc' := le_of_not_lt hba
    apply le_antisymm <;> assumption

instance : Std.Asymm (fun (a b : T) ↦ a < b) where
  asymm := by
    intro a b
    exact not_lt_of_gt

instance : Trans (fun (a b : T) ↦ ¬a < b) (fun a b ↦ ¬a < b) (fun a b ↦ ¬a < b) where
  trans := by
    intro a b c
    intro hab hbc
    apply not_lt_of_ge
    have hab' := le_of_not_lt hab
    have hbc' := le_of_not_lt hbc
    exact Preorder.le_trans c b a hbc' hab'

instance : Zero (Tuple T n) := ⟨Vector.replicate n 0⟩

instance : LinearOrder (List T) := inferInstance

instance : LinearOrder (Array T) where
  le_refl := by apply Array.lt_irrefl

  le_trans := by
    intro a b c
    apply Array.le_trans

  le_antisymm := by
    have h : ∀ (a b : List T), a ≤ b → b ≤ a → a=b := by apply le_antisymm
    intro a b
    specialize h a.toList b.toList
    simp only[(· ≤ ·)]
    simp[h]
    intro hab hba
    exact Array.toList_inj.mp (h hab hba)

  le_total := by
    have h : ∀ (a b : List T), a.le b ∨ b.le a := by simp[le_total]
    intro a b
    specialize h a.toList b.toList
    assumption

  lt_iff_le_not_le := by
    intro a b
    simp[(· ≤ ·)]
    apply Iff.intro
    . intro h
      constructor
      . tauto
      . constructor
        . cases a with
          | mk la => induction la generalizing b with
            | nil => cases b with
              | mk lb => cases lb with
                | nil        => contradiction
                | cons tb qb =>  simp
            | cons ta qa ih => cases b with
              | mk lb => cases lb with
                | nil        => contradiction
                | cons tb qb =>
                  simp at *
                  intro ht
                  simp[ht] at h
                  let ab := (⟨qb⟩: Array T)
                  specialize ih ab
                  exact fun a ↦ ih h (congrArg Array.mk a)
        . tauto
    . tauto

  toDecidableLE := inferInstance

  compare_eq_compareOfLessAndEq := by
    intro a b
    unfold compare
    unfold compareOfLessAndEq
    cases a with
    | mk la => induction la generalizing b with
      | nil => cases b with
        | mk lb  =>
          simp only[Array.instOrd]
          unfold compare
          unfold Array.compareLex
          unfold Array.compareLex.go
          cases lb <;> simp
      | cons ta qa ih => cases b with
        | mk lb =>
          simp only[Array.instOrd]
          cases lb with
          | nil => simp[compare,Array.compareLex,Array.compareLex.go]
          | cons tb qb =>
            let aa := (⟨qa⟩: Array T)
            let ab := (⟨qb⟩: Array T)
            specialize ih ab
            simp
            by_cases h : ta=tb
            . simp[h]
              by_cases hq : qa=qb
              . simp[compare,Array.compareLex,hq]
                unfold Array.compareLex.go
                have heq : compare tb tb = Ordering.eq := compare_eq_iff_eq.mpr rfl
                simp[heq]
                have heq' : compare qa qb = Ordering.eq := by
                  simp[compare_eq_iff_eq,List.instOrd,hq]
                  simp[hq,aa,ab] at ih
                  simp[Array.instOrd,Array.compareLex] at ih
                  unfold Array.compareLex.go at ih
                  sorry
                sorry
              . sorry
            . by_cases hab : ta<tb
              . simp[hab]
                sorry
              . simp[hab]
                sorry

instance : LinearOrder (Tuple T n) where
  le_refl := by apply Vector.lt_irrefl

  le_trans := by
    intro a b c
    apply Vector.le_trans

  le_antisymm := by
    have h : ∀ (a b : Array T), a ≤ b → b ≤ a → a=b := by apply le_antisymm
    intro a b
    specialize h a.toArray b.toArray
    intro hab hba
    exact Vector.toArray_inj.mp (h hab hba)

  le_total := by
    have h : ∀ (a b : List T), a.le b ∨ b.le a := by simp[le_total]
    intro a b
    specialize h a.toList b.toList
    assumption

  lt_iff_le_not_le := by
    intro a b
    simp[(· ≤ ·)]
    apply Iff.intro
    . intro h
      constructor
      . tauto
      . constructor
        . cases a with
          | mk arra sa =>
            cases b with
            | mk arrb sb =>
              have h' : arra < arrb := by
                simp only [(· < ·)] at h
                exact h
              have h'' : ¬arra=arrb := ne_of_lt h'
              simp[h'']
              tauto
        . tauto
    . tauto

  toDecidableLE := inferInstance

  compare_eq_compareOfLessAndEq := by
    intro a b
    unfold compare
    unfold compareOfLessAndEq
    cases a with
    | mk arr sa => cases arr with
      | mk la => induction la generalizing n b with
        | nil => cases b with
          | mk arrb sb => cases arrb with
            | mk lb  =>
              simp only[Vector.instOrd,Vector.compareLex]
              unfold compare
              unfold Array.compareLex
              unfold Array.compareLex.go
              cases lb <;> simp
        | cons ta qa ih => cases b with
          | mk arrb sb => cases arrb with
            | mk lb =>
              simp only[Vector.instOrd,Vector.compareLex]
              cases lb with
              | nil => simp[compare,Array.compareLex,Array.compareLex.go]
              | cons tb qb =>
                specialize @ih (n-1)
                let aa := (⟨qa⟩: Array T)
                let ab := (⟨qb⟩: Array T)
                have hab : qb.length = n-1 := Nat.eq_sub_of_add_eq sb
                have haa : qa.length = n-1 := Nat.eq_sub_of_add_eq sa
                specialize ih ⟨ab, hab⟩
                specialize ih haa
                simp
                by_cases h : ta=tb
                . simp[h]
                  have heq : compare tb tb = Ordering.eq := by
                    exact compare_eq_iff_eq.mpr rfl
                  by_cases hq : qa=qb
                  . simp[compare,Array.compareLex,hq]
                    unfold Array.compareLex.go
                    simp[heq]
                    have heq' : compare aa ab = Ordering.eq := by
                      simp[aa,ab,hq]
                      rw[← compare_eq_iff_eq]

                    sorry
                  . sorry
                . by_cases hab : ta<tb
                  . simp[hab]
                    sorry
                  . simp[hab]
                    sorry

def Relation (T) (arity: ℕ) := Multiset (Tuple T arity)

instance : Add (Relation T arity) := inferInstanceAs (Add (Multiset (Tuple T arity)))
instance : Sub (Relation T arity) := inferInstanceAs (Sub (Multiset (Tuple T arity)))
instance : HMul (Relation T a₁) (Relation T a₂) (Relation T (a₁+a₂)) where
  hMul r s :=
    Multiset.map (λ (x,y) ↦ Vector.append x y) (Multiset.product r s)

instance : Zero (Relation T n) where zero := (∅: Multiset (Tuple T n))
instance : Zero ((n : ℕ) × Relation T n) where zero := ⟨0,(∅: Multiset (Tuple T 0))⟩

structure Database (T) where
  db : (ℕ × String) →₀ (Σ n, Relation T n)
  wf : ∀ (n: ℕ) (s: String), (db (n,s)).fst = n

instance : FunLike (Database T) (ℕ × String) (Σ n, Relation T n) where
  coe := λ d ↦ (λ (n, s) ↦ d.db (n, s))
  coe_injective' := by
    intro d₁ d₂ h
    simp at h
    cases d₁; cases d₂
    congr
