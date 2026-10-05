import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic

/-!
---
title: Relations and databases with multiset semantics
type: definition
---
Values are drawn from a value type: a linearly ordered type with a zero,
an addition, a subtraction and a multiplication, over which the arithmetic
of query terms is read. A tuple of arity $k$ is a map $\{0, \dots, k-1\}
\to \mathcal{V}$, tuples being ordered lexicographically; a relation of
arity $k$ is a finite multiset of $k$-tuples, with multiset union and the
cross product of multisets; a database is a finite list of named
relations, each with its arity, looked up by name and arity.
-/

namespace Lax392996.Databases

/-- The values of a database: a linearly ordered type with a zero, an
addition, a subtraction and a multiplication, the arithmetic of terms. -/
class ValueType (T : Type) extends Zero T, AddCommSemigroup T, Sub T, Mul T, LinearOrder T

variable {T : Type} [ValueType T] {n m : ℕ}

/-- A tuple of arity `n` over `T`. -/
def Tuple (T : Type) (n: ℕ) := Fin n → T

instance instDecidableEqTuple [DecidableEq T] : DecidableEq (Tuple T n) := by
  show DecidableEq (Fin n → T)
  infer_instance

/-- The lexicographic strict order on tuples. -/
instance instLTTuple : LT (Tuple T n) :=
  ⟨λ a b ↦ ∃ i : Fin n, (∀ j, j < i → a j = b j) ∧ a i < b i⟩

instance instLETuple : LE (Tuple T n) := ⟨λ a b ↦ a < b ∨ a = b⟩

instance instDecidableRelTupleLt : DecidableRel (λ (t₁ t₂: Tuple T n) => t₁ < t₂) :=
  λ f g ↦
    let _ : DecidablePred (fun i : Fin n => (∀ j, j < i → f j = g j) ∧ f i < g i) :=
      fun i => @instDecidableAnd _ _
        (@Fintype.decidableForallFintype (Fin n) (fun j => j < i → f j = g j)
          (fun _j => inferInstance) _)
        inferInstance
    if h : ∃ i : Fin n, (∀ j, j < i → f j = g j) ∧ f i < g i then
      isTrue (h)
    else
      isFalse (h)

/-- Tuples are linearly ordered, lexicographically. -/
instance instLinearOrderTuple : LinearOrder (Tuple T n) where
  le_refl := by simp[(· ≤ ·)]

  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    cases hab with
    | inl hab' =>
      cases hba with
      | inl hba' =>
        simp only[(· < ·)] at *
        rcases hab' with ⟨iab,hiab⟩
        rcases hba' with ⟨iba,hiba⟩
        by_cases h : iab=iba
        . rw[h] at hiab
          have := lt_trans hiab.right hiba.right
          have := lt_asymm (lt_trans hiab.right hiba.right)
          contradiction
        . by_cases h' : iab<iba
          . have heq := hiba.left iab h'
            have := hiab.right
            rw[heq] at this
            have := lt_asymm this
            contradiction
          . have h'' : iba<iab := by
              refine lt_iff_le_and_ne.mpr ?_
              constructor
              . exact le_of_not_gt h'
              . exact fun a ↦ h (id (Eq.symm a))
            have heq := hiab.left iba h''
            have := hiba.right
            rw[heq] at this
            have := lt_asymm this
            contradiction
      | inr hba' => exact Eq.symm hba'
    | inr hab' => exact hab'

  le_trans := by
    intro a b c
    simp only[(· ≤ ·),(· < ·)]
    intro hab hbc
    cases hab with
    | inl habl =>
      cases hbc with
      | inl hbcl =>
        apply Or.inl
        rcases habl with ⟨iab,hiab⟩
        rcases hbcl with ⟨ibc,hibc⟩
        let i := min iab ibc
        use i
        have h : ∀ (j : Fin n), j < i → a j = c j := by
          intro j hj
          have hx := hiab.left j (lt_min_iff.mp hj).left
          have hy := hibc.left j (lt_min_iff.mp hj).right
          rw[hy] at hx; exact hx
        use h
        by_cases heq : iab = i
        . by_cases heq' : ibc = i
          . rw[heq] at hiab
            rw[heq'] at hibc
            exact lt_trans hiab.right hibc.right
          . have h' : i < ibc := lt_of_le_of_ne (min_le_right iab ibc) (ne_comm.mpr heq')
            have hab := hiab.right
            rw[heq] at hab
            have hbc := hibc.left i h'
            rw[hbc] at hab
            exact hab
        . have heq'' : ibc = i := by
            have choice : iab = i ∨ ibc = i := by
              rcases min_choice iab ibc with hc | hc
              . exact Or.inl hc.symm
              . exact Or.inr hc.symm
            tauto
          have h' : i < iab := lt_of_le_of_ne (min_le_left iab ibc) (ne_comm.mpr heq)
          have hbc := hibc.right
          rw[heq''] at hbc
          have hab := hiab.left i h'
          rw[hab]
          exact hbc
      | inr hbcr =>
        rw[← hbcr]
        exact Or.inl habl
    | inr habr =>
      rw[habr]
      exact hbc

  le_total := by
    intro a b
    simp only[(· ≤ ·)]
    by_cases heq: a=b
    . tauto
    . by_cases h: ∃ i, (∀ j < i, a j = b j) ∧ a i < b i
      . apply Or.inl; apply Or.inl
        simp only[(· < ·)]
        tauto
      . apply Or.inr; apply Or.inl
        simp only[(· < ·)]
        have hexists : ∃ k, ¬ a k = b k := by
          refine Classical.byContradiction fun hne => ?_
          simp at hne
          exact heq (funext hne)
        have hdec : DecidablePred (fun j : Fin n => ¬ a j = b j) := fun j => instDecidableNot
        obtain ⟨k, hk⟩ : ∃ k, k = Fin.find (λ j ↦ ¬ a j = b j) hexists := ⟨_, rfl⟩
        use k
        have hspec : ¬ a k = b k := by rw [hk]; exact Fin.find_spec hexists
        have hmin_ab : ∀ j < k, a j = b j := by
          intro j hj
          rw [hk] at hj
          have := Fin.find_min hexists hj
          simp at this
          exact this
        have hmin_ba : ∀ j < k, b j = a j := fun j hj => (hmin_ab j hj).symm
        refine ⟨hmin_ba, ?_⟩
        simp at h
        have hle : b k ≤ a k := h k hmin_ab
        exact lt_iff_le_and_ne.mpr ⟨hle, fun h => hspec h.symm⟩

  lt_iff_le_not_ge := by
    intro a b
    simp only[(· ≤ ·)]
    apply Iff.intro
    . intro hab
      constructor
      . tauto
      . simp only[(· < ·)] at *
        rcases hab with ⟨i, hi⟩
        simp
        constructor
        . intro k h
          cases hki : compare k i with
          | eq =>
            simp at hki
            rw[hki]
            exact le_of_lt hi.right
          | lt =>
            simp[compare] at hki
            have := hi.left k hki
            simp[this]
          | gt =>
            simp only[compare,compareOfLessAndEq] at hki
            by_cases hki' : k < i
            . simp[hki'] at hki
            . by_cases hki'' : k = i
              . rw[hki''] at hki
                simp at hki
              . simp[hki'] at hki
                have hgt : k>i := by
                  have hle := le_of_not_gt hki'
                  apply lt_of_le_of_ne
                  . exact hle
                  . exact fun a ↦ hki'' (id (Eq.symm a))
                have h' := h i hgt
                rw[h'] at hi
                have hc : a i < a i := hi.right
                simp at hc
        . intro heq
          rw[heq] at hi
          simp at hi
    . intro ⟨h₁,h₂⟩
      simp at h₂
      have hne : a ≠ b := by
        rw[ne_comm]; exact h₂.right
      simp[hne] at h₁
      exact h₁

  toDecidableLE :=
    λ a b ↦
      match (inferInstance : Decidable (a<b)), (inferInstance : Decidable (a=b)) with
      | isTrue h₁, _           => isTrue (Or.inl h₁)
      | _, isTrue h₂           => isTrue (Or.inr h₂)
      | isFalse h₁, isFalse h₂ => isFalse (
        fun h ↦
          match h with
            | Or.inl h' => h₁ h'
            | Or.inr h' => h₂ h'
        )

/-- A relation of arity `arity` over `T`: a finite multiset of tuples. -/
def Relation (T) (arity: ℕ) := Multiset (Tuple T arity)

/-- Transport of a relation along an equality of arities. -/
def Relation.cast (heq: n=m) (r: Relation T n): Relation T m :=
  Eq.ndrec (motive := fun m => Relation T m) r heq

instance instAddRelation {arity : ℕ} : Add (Relation T arity) := by
  show Add (Multiset (Tuple T arity))
  infer_instance

/-- The cross product of two relations, concatenating the tuples. -/
instance instHMulRelationHAddNat {a₁ a₂ : ℕ} :
    HMul (Relation T a₁) (Relation T a₂) (Relation T (a₁+a₂)) where
  hMul r s :=
    Multiset.map (λ ((x,y) : (Tuple T a₁)×(Tuple T a₂)) ↦
      Fin.append x y
    ) (Multiset.product r s)

/-- A database: a list of named relations, each with its arity. -/
def Database (T) := List (String × Σ n, Relation T n)

/-- The relation named `s` of arity `n` in a database, if any. -/
def Database.find (n: ℕ) (s: String) (d: Database T) : Option (Relation T n) :=
  let rec f
  | [] => none
  | (s',rn)::tl => if h: n = rn.fst ∧ s=s' then some (Eq.mp (by rw[h.left]) rn.snd) else f tl
  f d

end Lax392996.Databases
