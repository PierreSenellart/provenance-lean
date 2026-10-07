import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Bind

import Provenance.Util.ValueType

/-!
# Tuples, relations, and databases

This file defines the basic relational model used throughout the library.

## Main definitions

* `Tuple T n` – a tuple of arity `n` over value type `T`, represented as a function
  `Fin n → T`
* `Relation T n` – a multiset of tuples of arity `n`
* `Database T` – a mapping from relation names (strings) to relations of the
  corresponding arities
-/

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
  inferInstanceAs (DecidableEq (Fin n → T))

instance [Repr α] : Repr (Tuple α n) := ⟨Tuple.repr⟩

instance : Zero (Tuple T n) := ⟨λ _ ↦ 0⟩

instance : LT (Tuple T n) := ⟨λ a b ↦ ∃ i : Fin n, (∀ j, j < i → a j = b j) ∧ a i < b i⟩
instance : LE (Tuple T n) := ⟨λ a b ↦ a < b ∨ a = b⟩

instance [ToString T] : ToString (Tuple T n) where
  toString t :=
    "(" ++ String.intercalate ", " (List.ofFn (fun i => toString (t i))) ++ ")"

instance : DecidableRel (λ (t₁ t₂: Tuple T n) => t₁ < t₂) :=
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
        have hexists : ∃ k, ¬ a k = b k := by
          by_contra hne
          simp at hne
          exact heq (funext hne)
        set k := Fin.find (λ j ↦ ¬ a j = b j) hexists with hk_def
        use k
        have hspec : ¬ a k = b k := Fin.find_spec hexists
        have hmin_ab : ∀ j < k, a j = b j := by
          intro j hj
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
                  apply le_of_not_gt at hki'
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

theorem Relation.cast_eq {S: Type} (r: Relation S n) (s: Relation S m) (heq: n=m) :
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

/-- **Binding a relation name**, the `I[R ↦ M]` of a recursion's rounds.
A database is searched front to back, so a binding is a cons: it shadows
whatever the name had, and nothing else moves. -/
def Database.assign (s : String) {k : ℕ} (X : Relation T k)
    (d : Database T) : Database T := (s, ⟨k, X⟩) :: d

omit [ValueType T] in
@[simp] theorem Database.find_assign (s : String) {k : ℕ} (X : Relation T k)
    (d : Database T) : (d.assign s X).find k s = some X := by
  show (if h : k = k ∧ s = s then _ else _) = _
  rw [dite_eq_left ⟨rfl, rfl⟩]
  rfl

omit [ValueType T] in
theorem Database.find_assign_of_ne (s s' : String) {k k' : ℕ}
    (X : Relation T k) (d : Database T) (h : ¬(k' = k ∧ s' = s)) :
    (d.assign s X).find k' s' = d.find k' s' := by
  show (if h : k' = k ∧ s' = s then _ else _) = _
  rw [dite_eq_right h]
  rfl

def sortedInsert [LinearOrder α] (x : α) (l : {l : List α // List.Pairwise (· ≤ ·) l}) :
    {l : List α // List.Pairwise (· ≤ ·) l} :=
  ⟨l.val.orderedInsert (· ≤ ·) x, List.Pairwise.orderedInsert x l.val l.property⟩

instance [LinearOrder α] :
  @LeftCommutative α _ sortedInsert where
  left_comm := by
    intros a b l
    simp only [sortedInsert]
    simp
    apply @List.Perm.eq_of_pairwise' α (· ≤ ·) _
    . exact List.Pairwise.orderedInsert _ _ (List.Pairwise.orderedInsert _ _ l.property)
    . exact List.Pairwise.orderedInsert _ _ (List.Pairwise.orderedInsert _ _ l.property)
    rw[List.perm_iff_count]
    intro c
    repeat rw[List.orderedInsert_count]
    by_cases hab : a=b <;>
      by_cases hca : c=a <;>
      by_cases hcb : c=b <;> simp[hab,hca,hcb,eq_comm]
    have : a≠c := by exact fun z ↦ hca (id (Eq.symm z))
    simp[this]

/-- A multiset as a sorted list: the canonical reading of a relation as a
sequence. It is computable, where a choice through `Multiset.toList` is
not, and it is determined by the multiset, which is what lets two
sequences built from the same rows be recognised as the same sequence.

It is an insertion sort rather than `Multiset.sort`, which is defined by
well-founded recursion and does not reduce in the kernel: the evaluators
read a relation as a sequence through this, and a `decide`-checked
equation about a computed relation needs every step of it to reduce. -/
def sortList {α : Type} [LinearOrder α] (M : Multiset α) : List α :=
  (M.foldr sortedInsert ⟨[], by simp⟩).val

/-- Sorting changes no element: the list's multiset is the original. -/
@[simp] theorem sortList_coe {α : Type} [LinearOrder α] (M : Multiset α) :
    (↑(sortList M) : Multiset α) = M := by
  induction M using Multiset.induction_on with
  | empty => rfl
  | cons a M ih =>
    rw [sortList, Multiset.foldr_cons]
    calc (↑((sortedInsert a (M.foldr sortedInsert ⟨[], by simp⟩)).val) : Multiset α)
        = ↑(a :: (M.foldr sortedInsert ⟨[], by simp⟩).val) :=
          Multiset.coe_eq_coe.mpr (List.perm_orderedInsert _ a _)
      _ = a ::ₘ ↑((M.foldr sortedInsert ⟨[], by simp⟩).val) := rfl
      _ = a ::ₘ M := by rw [← sortList, ih]

/-- And it sorts: the list is pairwise `≤`. -/
theorem sortList_pairwise {α : Type} [LinearOrder α] (M : Multiset α) :
    (sortList M).Pairwise (· ≤ ·) :=
  (Multiset.foldr sortedInsert ⟨[], by simp⟩ M).property

/-- Sorting changes no count: the list is as long as the multiset. -/
@[simp] theorem length_sortList {α : Type} [LinearOrder α] (M : Multiset α) :
    (sortList M).length = Multiset.card M := by
  rw [← Multiset.coe_card, sortList_coe]

/-- An element of the sorted list is an element of the multiset. -/
@[simp] theorem mem_sortList {α : Type} [LinearOrder α] {M : Multiset α}
    {x : α} : x ∈ sortList M ↔ x ∈ M := by
  rw [← Multiset.mem_coe, sortList_coe]

/-- **A sorted list is its multiset's sorted list.** Two sequences built
by sorting the same rows are the same sequence, whatever route built
them. -/
theorem sortList_eq {α : Type} [LinearOrder α] {l : List α} {M : Multiset α}
    (hs : l.Pairwise (· ≤ ·)) (hm : (↑l : Multiset α) = M) : l = sortList M :=
  List.Perm.eq_of_pairwise' (r := (· ≤ ·)) hs (sortList_pairwise M)
    (Multiset.coe_eq_coe.mp (by rw [hm, sortList_coe]))

instance [ToString T] : ToString (Relation T n) where
  toString r :=
    String.intercalate "\n" ((r.foldr sortedInsert ⟨[],by simp⟩).val.map toString) ++ "\n"
