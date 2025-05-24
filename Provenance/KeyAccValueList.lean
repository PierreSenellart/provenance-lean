import Mathlib.Data.List.Sort
import Mathlib.Order.Defs.LinearOrder

variable {α: Type} [LinearOrder α]

def LEByKey (a b: Prod α β) : Prop :=
  a.fst <= b.fst

instance : DecidableRel (λ (a b: α×β) ↦ LEByKey a b) :=
  λ a b ↦ if h : a.fst <= b.fst then isTrue (h) else isFalse (h)

instance : IsTotal (α × β) LEByKey where
  total := by
    intro a b
    unfold LEByKey
    exact le_total _ _

instance : IsTrans (α × β) LEByKey where
  trans := by
    intro a b c
    unfold LEByKey
    exact Preorder.le_trans _ _ _

def KeyValueList (l : List (α×β)) := match l with
| []     => True
| hd::tl => KeyValueList tl ∧ match tl with
  | []     => True
  | hd'::_ => hd.1<hd'.1

def List.addKV [DecidableEq β] [Add β] (l: List (α×β)) (a: α) (b: β) :=
  match l.find? (·.1=a) with
  | none        => l.orderedInsert LEByKey (a,b)
  | some (a,b') => (l.eraseP (Prod.fst · = a)).orderedInsert LEByKey (a,b+b')

theorem KeyValueList.sorted (l: List (α×β)) (h: KeyValueList l) :
  List.Sorted LEByKey l := by
    induction l with
    | nil           => simp
    | cons hd tl ih =>
      apply List.sorted_cons.mpr
      simp[KeyValueList] at h
      constructor
      . cases tl with
        | nil          => simp
        | cons hd' tl' =>
          simp at h
          intro b hb
          rcases hb
          . exact le_of_lt h.right
          . rename_i hb
            have sorted_tail := ih h.left
            rw[List.sorted_cons] at sorted_tail
            exact le_of_lt (lt_of_lt_of_le h.right (sorted_tail.left b hb))
      . exact ih h.left

theorem KeyValueList.erase (l : List (α×β)) (h: KeyValueList l) (a: α):
  KeyValueList (l.eraseP (·.1=a)) := by
  induction l with
  | nil           =>
    unfold KeyValueList
    simp
  | cons hd tl ih =>
    rw[List.eraseP_cons]
    by_cases h' : hd.1=a
    . simp[h']
      exact h.left
    . simp[h']
      constructor
      . exact ih h.left
      . cases tl with
        | nil          => simp
        | cons hd' tl' =>
          rw[List.eraseP_cons]
          unfold KeyValueList at h
          simp at h
          by_cases h'': hd'.1=a
          . simp[h'']
            unfold KeyValueList at h
            cases tl' with
            | nil        => simp
            | cons hd' _ =>
              simp
              simp at h
              exact lt_trans h.right h.left.right
          . simp[h'']
            exact h.right

theorem KeyValueList.noKeyDup (l : List (α×β)) (h: KeyValueList l):
  List.Pairwise (·.1≠·.1) l := by
    induction l with
    | nil => tauto
    | cons hd tl ih =>
      rw[List.pairwise_cons]
      constructor
      . unfold KeyValueList at h
        induction tl with
        | nil => tauto
        | cons hd' tl' ih' =>
          intro a' ha'
          rcases ha'
          . simp at h
            exact ne_of_lt h.right
          . rename_i ha'
            have hb : KeyValueList tl' → List.Pairwise (·.1≠·.1) tl' := by
              intro hb'
              have := ih h.left
              exact List.Pairwise.of_cons this
            have hc: (KeyValueList tl' ∧ match tl' with | [] => True | hd' :: tail => hd.1 < hd'.1) := by
              constructor
              . exact h.left.left
              . cases tl' with
                | nil         => tauto
                | cons hd'' _ =>
                  simp
                  simp at h
                  have h'' := h.left.right
                  simp at h''
                  exact lt_trans h.right h''
            exact ih' hb hc a' ha'
      . exact ih h.left

theorem KeyValueList.erase_find (l : List (α×β)) (h: KeyValueList l) (a: α):
  (l.eraseP (·.1=a)).find? (·.1=a) = none := by
    induction l with
    | nil => tauto
    | cons hd tl ih =>
      by_cases h' : hd.1 = a
      . simp[h']
        have hnoKeyDup := noKeyDup (hd::tl) h
        rw[← h']
        intro a' b ha'b
        rw[List.pairwise_cons] at hnoKeyDup
        have := hnoKeyDup.left (a',b) ha'b
        simp[ne_comm] at this
        assumption
      . simp[h']
        intro a' b ha'b
        have hi := ih h.left
        simp at hi
        exact hi a' b ha'b

theorem KeyValueList.orderedInsert [DecidableEq β] [Add β]
  (l : List (α×β)) (h: KeyValueList l) (a: α) (b: β) (hp: l.find? (·.1=a) = none):
  KeyValueList (l.orderedInsert LEByKey (a,b)) := by
    induction l with
    | nil           => simp[KeyValueList]
    | cons hd tl ih =>
      simp[hp]
      by_cases hab : a < hd.1 <;> simp[le_of_lt,hab,LEByKey]
      . constructor
        . exact h
        . exact hab
      . have hnle : ¬ a≤hd.1 := by
          simp
          simp at hab
          simp at hp
          exact lt_of_le_of_ne hab hp.left
        simp[hnle]
        unfold KeyValueList
        constructor
        . unfold List.addKV at ih
          rw[List.find?_cons] at hp
          have hne := ne_comm.mp (ne_of_not_le hnle)
          simp[hne] at hp
          have hfindtl : List.find? (·.1=a) tl = none := by
            rw[List.find?_eq_none]
            intro ab hab
            simp
            exact hp ab.1 ab.2 hab
          simp[hfindtl] at ih
          exact ih h.left
        . cases tl with
          | nil          => exact lt_of_not_le hnle
          | cons hd' _   =>
            simp
            by_cases h'': a<=hd'.1 <;> simp[h'',LEByKey]
            . exact lt_of_not_le hnle
            . exact h.right

theorem KeyValueList.addKV [DecidableEq β] [Add β] (l : List (α×β)) (h: KeyValueList l) (a: α) (b: β):
  KeyValueList (l.addKV a b) := by
    induction l with
    | nil           =>
      unfold List.addKV
      simp[KeyValueList]
    | cons hd tl ih =>
      unfold List.addKV
      match h' : (hd::tl).find? (·.1=a) with
      | none =>
        simp[h']
        exact KeyValueList.orderedInsert (hd::tl) h a b h'
      | some (a,b') =>
        simp[h']
        have herasekvl : KeyValueList ((hd::tl).eraseP (·.1=a)) := by
          exact erase (hd :: tl) h a
        have herasefind : ((hd::tl).eraseP (·.1 = a)).find? (·.1=a) = none := by
          exact erase_find (hd :: tl) h a
        exact KeyValueList.orderedInsert
          ((hd::tl).eraseP (·.1 = a))
          herasekvl
          a
          (b+b')
          herasefind
