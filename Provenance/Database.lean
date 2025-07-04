import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind

import Provenance.Util.ValueType

variable {T: Type} [ValueType T]

def Tuple (T : Type) (n: ℕ) := Fin n → T

def Tuple.repr [Repr T] (t: Tuple T n) (_: ℕ) : Std.Format :=
  let elems := (List.finRange n).map (fun (i: Fin n) => reprArg (t i))
  Std.Format.bracket "[" (Std.Format.joinSep elems ", ") "]"

def Tuple.cast (heq : n=m) (t: Tuple T n): Tuple T m := by
  subst heq
  exact t

theorem Tuple.apply_cast {T: Type} (heq: n=m) (f: Tuple T m → α) (t: Tuple T n) :
  f (t.cast heq) = (@_root_.cast (Tuple T m → α) (Tuple T n → α) (by simp[heq]) f) t := by
  subst heq
  rfl

theorem Tuple.cast_get {T: Type} (heq: n=m) (t: Tuple T n) (k: Fin m) :
  t.cast heq k = t (k.cast (Eq.symm heq)) := by
    subst heq
    rfl

instance [DecidableEq T] : DecidableEq (Tuple T n) :=
  λ t₁ t₂ =>
    if h : ∀ k, t₁ k = t₂ k then isTrue (funext h)
    else isFalse (by
      intro h'
      apply h
      exact fun k => congrFun h' k)

instance [Repr α] : Repr (Tuple α n) := ⟨Tuple.repr⟩

instance : Zero (Tuple T n) := ⟨λ _ ↦ 0⟩

instance : LT (Tuple T n) := ⟨λ a b ↦ ∃ i : Fin n, (∀ j, j < i → a j = b j) ∧ a i < b i⟩
instance : LE (Tuple T n) := ⟨λ a b ↦ a < b ∨ a = b⟩

instance [ToString T] : ToString (Tuple T n) where
  toString t :=
    "(" ++ String.intercalate ", " (List.ofFn (fun i => toString (t i))) ++ ")"

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

def Relation.cast (heq: n=m) (r: Relation T n): Relation T m := by
  subst heq
  exact r

def Relation.cast_eq (r: Relation T n) (s: Relation T m) (heq: n=m) :
  s = r.cast heq ↔ s = r.map (λ t ↦ t.cast heq)
  := by
    simp[Relation.cast, Tuple.cast]
    subst heq
    simp

instance : Add (Relation T arity) := inferInstanceAs (Add (Multiset (Tuple T arity)))
instance : Sub (Relation T arity) := inferInstanceAs (Sub (Multiset (Tuple T arity)))
instance : HMul (Relation T a₁) (Relation T a₂) (Relation T (a₁+a₂)) where
  hMul r s :=
    Multiset.map (λ ((x,y) : (Tuple T a₁)×(Tuple T a₂)) ↦
      Fin.append x y
    ) (Multiset.product r s)

instance : Zero (Relation T n) where zero := (∅: Multiset (Tuple T n))
instance : Zero ((n : ℕ) × Relation T n) where zero := ⟨0,(∅: Multiset (Tuple T 0))⟩

def Database (T) := List (String × Σ n, Relation T n)

def Database.find (n: ℕ) (s: String) (d: Database T) : Option (Relation T n) :=
  let rec f
  | [] => none
  | (s',rn)::tl => if h: n = rn.fst ∧ s=s' then some (Eq.mp (by rw[h.left]) rn.snd) else f tl
  f d

def sortedInsert [LinearOrder α] (x : α) (l : {l : List α // List.Sorted (· ≤ ·) l}) :
    {l : List α // List.Sorted (· ≤ ·) l} :=
  ⟨l.val.orderedInsert (· ≤ ·) x, List.Sorted.orderedInsert x l.val l.property⟩

instance [LinearOrder α] :
  @LeftCommutative α _ sortedInsert where
  left_comm := by
    intros a b l
    simp only [sortedInsert]
    simp
    apply @List.eq_of_perm_of_sorted α (· ≤ ·)
    . rw[List.perm_iff_count]
      intro c
      repeat rw[List.orderedInsert_count]
      by_cases hab : a=b <;>
        by_cases hca : c=a <;>
        by_cases hcb : c=b <;> simp[hab,hca,hcb,eq_comm]
      have : a≠c := by exact fun z ↦ hca (id (Eq.symm z))
      simp[this]
    . exact List.Sorted.orderedInsert _ _ (List.Sorted.orderedInsert _ _ l.property)
    . exact List.Sorted.orderedInsert _ _ (List.Sorted.orderedInsert _ _ l.property)

instance [ToString T] : ToString (Relation T n) where
  toString r :=
    String.intercalate "\n" ((r.foldr sortedInsert ⟨[],by simp⟩).val.map toString) ++ "\n"
