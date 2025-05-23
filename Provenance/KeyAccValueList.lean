import Mathlib.Data.List.Sort
import Mathlib.Order.Defs.LinearOrder

def LEByKey {α β: Type} [LinearOrder α] (a b: Prod α β) : Prop :=
  a.fst <= b.fst

instance [LinearOrder α] : DecidableRel (λ (a b: α×β) ↦ LEByKey a b) :=
  λ a b ↦ if h : a.fst <= b.fst then isTrue (h) else isFalse (h)

instance [LinearOrder α] : IsTotal (α × β) LEByKey where
  total := by
    intro a b
    unfold LEByKey
    exact le_total _ _

instance [LinearOrder α] : IsTrans (α × β) LEByKey where
  trans := by
    intro a b c
    unfold LEByKey
    exact Preorder.le_trans _ _ _

class KeyAccValueList (α β: Type) [LinearOrder α] [DecidableEq β] [Add β] where
  list : List (α × β)
  sorted : list.Sorted LEByKey
  noDupKey : list.Pairwise (·.fst≠·.fst)

def KeyAccValueList.find? [LinearOrder α] [DecidableEq β] [Add β]
  (l: KeyAccValueList α β) (a : α) : Option (α×β) :=
  l.list.find? (·.fst=a)

def KeyAccValueList.erase [LinearOrder α] [DecidableEq β] [Add β]
  (l: KeyAccValueList α β) (ab : α×β) : KeyAccValueList α β :=
  {
    list := l.list.erase ab

    sorted := by
      suffices
        h : list.Sorted LEByKey → (list.erase ab).Sorted LEByKey
        from h l.sorted
      induction l.list with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.erase]
        by_cases h₁ : hd == ab <;> simp only[h₁] <;> intro h
        · exact List.Sorted.tail h
        · simp at h₁
          rw[List.sorted_cons]
          constructor
          . intro b hb
            have : b ∈ tl := List.mem_of_mem_erase hb
            exact (List.sorted_cons.mp h).left b this
          . exact ih (List.Sorted.tail h)

    noDupKey := by
      suffices
        h : list.Pairwise (·.fst≠·.fst) → (list.erase ab).Pairwise (·.fst≠·.fst)
        from h l.noDupKey
      induction l.list with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.erase]
        by_cases h₁ : hd == ab <;> simp only[h₁] <;> intro h
        . exact (List.pairwise_cons.mp h).right
        . simp at h₁
          apply List.pairwise_cons.mpr
          rw[List.pairwise_cons] at h
          constructor
          . intro a ha
            have : a ∈ tl := List.mem_of_mem_erase ha
            exact h.left a this
          . exact ih h.right
  }

def KeyAccValueList.add [LinearOrder α] [DecidableEq β] [Add β]
  (l: KeyAccValueList α β) (ab : α×β) : KeyAccValueList α β :=
  {
    list := match l.find? ab.fst with
            | none       => l.list.orderedInsert LEByKey ab
            | some (a,b) => (l.erase (a,b)).list.orderedInsert LEByKey ⟨ab.fst,ab.snd+b⟩

    sorted :=
      match l.find? ab.1 with
      | none       => List.Sorted.orderedInsert _ _ l.sorted
      | some (a,b) => List.Sorted.orderedInsert _ _ (l.erase (a,b)).sorted

    noDupKey := by
      match h: l.find? ab.1 with
      | none       =>
        simp
        unfold find? at h
        simp[List.find?_eq_none] at h
        sorry
      | some (a,b) => sorry
  }
