import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind

class ValueType (T : Type) extends Zero T, BEq T, LE T, LinearOrder T

variable {T: Type} [ValueType T] [DecidableEq T] [DecidableLE T]

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
    exact ValueType.le_trans c b a hbc' hab'

instance : Zero (Tuple T n) := ⟨Vector.replicate n 0⟩
instance : PartialOrder (Tuple T n) where
  le_refl := by apply Vector.lt_irrefl

  le_trans := by
    intro a b c
    apply Vector.le_trans

  le_antisymm := by
    intro a b
    simp only [(· ≤ ·)]
    simp
    intro hab hba
    refine Vector.toList_inj.mp ?_
    cases a with
    | mk arr s  =>
      cases arr with
      | mk la => cases la with
        | nil        =>
          simp[(· ≤ ·)] at hba
          simp[hba]
        | cons ta qa => cases b with
          | mk arrb sb => cases arrb with
            | mk lb => cases lb with
              | nil        =>
                simp[(· ≤ ·)] at hab
              | cons tb qb =>
                simp[(· ≤ ·)] at *
                cases hab with
                | inl hab' => assumption
                | inr hab' => cases hba with
                  | inl hba' => simp[hba']
                  | inr hba' =>
                    apply List.lex_asymm at hab'
                    contradiction
                    intro x y
                    exact not_lt_of_gt

  lt_iff_le_not_le := by
    intro a b
    simp[(· ≤ ·)]
    apply Iff.intro
    . intro h
      constructor
      . tauto
      . constructor
        . cases a with
          | mk arr sa =>
            cases arr with
            | mk la => induction la generalizing n b with
              | nil => cases b with
                | mk arrb sb => cases arrb with
                  | mk lb => cases lb with
                    | nil        => contradiction
                    | cons tb qb =>  simp
              | cons ta qa ih => cases b with
                | mk arrb sb => cases arrb with
                  | mk lb => cases lb with
                    | nil        => contradiction
                    | cons tb qb =>
                      simp at *
                      intro ht
                      simp[ht] at h
                      specialize @ih (n-1)
                      let ab := (⟨qb⟩: Array T)
                      have hab : qb.length = n-1 := Nat.eq_sub_of_add_eq sb
                      specialize ih ⟨ab, hab⟩
                      simp[Nat.eq_sub_of_add_eq sa] at ih
                      exact fun a ↦ ih h (congrArg Array.mk a)
        . tauto
    . tauto

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
