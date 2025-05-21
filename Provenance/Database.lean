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

def Tuple (T : Type) (n: ℕ) := Fin n → T

instance : Zero (Tuple T n) := ⟨λ _ ↦ 0⟩

instance : LT (Tuple T n) := ⟨λ a b ↦ ∃ i : Fin n, (∀ j, j < i → a j = b j) ∧ a i < b i⟩
instance : LE (Tuple T n) := ⟨λ a b ↦ a < b ∨ a = b⟩

instance : DecidableRel ((·: Tuple T n) = ·) :=
  λ f g ↦
    if h : ∀ i, f i = g i then
      isTrue (funext h)
    else
      isFalse (fun H => h (congrFun H))

instance : DecidableRel ((·: Tuple T n) < ·) :=
  λ f g ↦
    if h : ∃ i : Fin n, (∀ j, j < i → f j = g j) ∧ f i < g i then
      isTrue (h)
    else
      isFalse (h)

instance : LinearOrder (Tuple T n) where
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
              . exact le_of_not_lt h'
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
        left
        rcases habl with ⟨iab,hiab⟩
        rcases hbcl with ⟨ibc,hibc⟩
        let i := min iab ibc
        use i
        have h : ∀ (j : Fin n), j < i → a j = c j := by
          intro j hj
          have hx := hiab.left
          have hy := hibc.left
          specialize hx j (lt_min_iff.mp hj).left
          specialize hy j (lt_min_iff.mp hj).right
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
              have := min_choice iab ibc
              nth_rw 1 [eq_comm] at this
              nth_rw 2 [eq_comm] at this
              assumption
            tauto
          have h' : i < iab := lt_of_le_of_ne (min_le_left iab ibc) (ne_comm.mpr heq)
          have hbc := hibc.right
          rw[heq''] at hbc
          have hab := hiab.left i h'
          rw[hab]
          exact hbc
      | inr hbcr =>
        subst hbcr
        left; exact habl
    | inr habr =>
      subst habr
      exact hbc

  le_total := by
    intro a b
    simp only[(· ≤ ·)]
    by_cases heq: a=b
    . tauto
    . by_cases h: ∃ i, (∀ j < i, a j = b j) ∧ a i < b i
      . left;left
        simp only[(· < ·)]
        tauto
      . right;left
        simp only[(· < ·)]
        cases h' : Fin.find (λ j ↦ ¬ a j = b j) with
        | none   =>
          apply Fin.find_eq_none_iff.mp at h'
          simp at h'
          simp[funext h'] at heq
        | some k =>
          use k
          have h'' := h'
          apply Fin.find_min at h'
          constructor
          . intro j hj; specialize h' hj
            simp at h'; simp[h']
          . simp at h
            specialize h k
            have : ∀ j < k, a j = b j := by
              intro j hj; specialize h' hj
              simp at h'
              simp[h']
            specialize h this
            apply lt_iff_le_and_ne.mpr
            constructor
            . assumption
            . apply Fin.find_eq_some_iff.mp at h''
              rw[ne_comm]
              simp[h''.left]

  lt_iff_le_not_le := by
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
        . intro k
          intro h
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
              . simp[hki',hki''] at hki
                have hgt : k>i := by
                  apply le_of_not_lt at hki'
                  apply lt_of_le_of_ne
                  . assumption
                  . exact fun a ↦ hki'' (id (Eq.symm a))
                specialize h i hgt
                rw[h] at hi
                have hc : a i < a i := hi.right
                simp at hc
        . by_contra heq
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
      match inferInstanceAs (Decidable (a<b)), inferInstanceAs (Decidable (a=b)) with
      | isTrue h₁, _           => isTrue (Or.inl h₁)
      | _, isTrue h₂           => isTrue (Or.inr h₂)
      | isFalse h₁, isFalse h₂ => isFalse (
        fun h ↦
          match h with
            | Or.inl h' => h₁ h'
            | Or.inr h' => h₂ h'
        )

def Relation (T) (arity: ℕ) := Multiset (Tuple T arity)

instance : Add (Relation T arity) := inferInstanceAs (Add (Multiset (Tuple T arity)))
instance : Sub (Relation T arity) := inferInstanceAs (Sub (Multiset (Tuple T arity)))
instance : HMul (Relation T a₁) (Relation T a₂) (Relation T (a₁+a₂)) where
  hMul r s :=
    Multiset.map (λ ((x,y) : (Tuple T a₁)×(Tuple T a₂)) ↦
      Fin.append x y
    ) (Multiset.product r s)

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
