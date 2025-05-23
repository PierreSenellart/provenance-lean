import Mathlib.Data.List.Sort
import Mathlib.Order.Defs.LinearOrder

def LEByKey {α β: Type} [LinearOrder α] [DecidableLE α] (a b: Prod α β) : Prop :=
  a.fst <= b.fst

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
        h : List.Sorted LEByKey list → List.Sorted LEByKey (list.erase ab)
        from h l.sorted
      induction l.list with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.erase]
        by_cases h₁ : hd == ab
        · simp only[h₁]
          intro h
          exact List.Sorted.tail h
        · simp only[h₁]
          simp at h₁
          intro h
          rw[List.sorted_cons]
          constructor
          . intro b hb
            have : b ∈ tl := List.mem_of_mem_erase hb
            exact (List.sorted_cons.mp h).left b this
          . exact ih (List.Sorted.tail h)

    noDupKey := by
      suffices
        h : list.Pairwise (·.fst≠·.fst)
      induction l.list with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.erase]
        by_cases h₁ : hd == ab
        . simp only[h₁]

          sorry
        . sorry
  }

def KeyAccValueList.add [LinearOrder α] [DecidableEq β] [Add β]
  (l: KeyAccValueList α β) (ab : α×β) : KeyAccValueList α β :=
  match find? ab.fst with
    | none       => list.orderedInsert LEByKey a
    | some (a,b) => (erase ⟨a,b⟩).orderedInsert LEByKey ⟨ab.fst,ab.snd+b⟩


def KeyAccValueList.erase := fun ab => list.erase ab
def KeyAccValueList.add := fun (ab: α×β) =>
match find? ab.fst with
  | none       => insert ab
  | some (a,b) => (erase ⟨a,b⟩).insert ⟨ab.fst,ab.snd+b⟩
