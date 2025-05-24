import Mathlib.Algebra.Group.Defs
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

theorem KeyValueList.noDupKey (l : List (α×β)) (h: KeyValueList l):
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

theorem KeyValueList.eq_iff_forall_mem [DecidableEq β]
  (l₁ l₂ : List (α×β)) (h₁: KeyValueList l₁) (h₂: KeyValueList l₂):
  l₁=l₂ ↔ ∀ x, x∈l₁ ↔ x∈l₂ := by
    apply Iff.intro
    . intro heq
      subst heq
      tauto
    . intro hmem
      induction l₁ generalizing l₂ with
      | nil =>
        cases l₂ with
        | nil => tauto
        | cons hd₂ tl₂ =>
          simp at hmem
          have := (hmem hd₂.1 hd₂.2).left
          simp at this
      | cons hd₁ tl₁ ih =>
        cases l₂ with
        | nil =>
          simp at hmem
          have := (hmem hd₁.1 hd₁.2).left
          simp at this
        | cons hd₂ tl₂ =>
          rw[List.cons_eq_cons]
          have hd₁eqhd₂ : hd₁=hd₂ := by
            by_cases hlt : hd₁.1 < hd₂.1
            . have h1b2 := (hmem hd₁).mp
              simp at h1b2
              rcases h1b2 with h'₁|h'₂
              . exact h'₁
              . have hs := KeyValueList.sorted (hd₂::tl₂) h₂
                rw[List.sorted_cons] at hs
                have hc := hs.left hd₁ h'₂
                simp[LEByKey,hlt] at hc
                have := lt_of_lt_of_le hlt hc
                simp at this
            . apply le_of_not_lt at hlt
              apply lt_or_eq_of_le at hlt
              rcases hlt with hlt'|heq'
              . have h2b1 := (hmem hd₂).mpr
                simp at h2b1
                rcases h2b1 with h'₁|h'₂
                . exact Eq.symm h'₁
                . have hs := KeyValueList.sorted (hd₁::tl₁) h₁
                  rw[List.sorted_cons] at hs
                  have hc := hs.left hd₂ h'₂
                  simp[LEByKey,hlt'] at hc
                  have := lt_of_lt_of_le hlt' hc
                  simp at this
              . have hnodup := noDupKey (hd₂::tl₂) h₂
                rw[List.pairwise_cons] at hnodup
                have hmem12 := (hmem hd₁).mp
                simp at hmem12
                rcases hmem12 with heq|hc
                . exact heq
                . have := hnodup.left hd₁ hc
                  simp[heq'] at this
          simp[hd₁eqhd₂]
          have hcondtl₂ : ∀ (x : α × β), x ∈ tl₁ ↔ x ∈ tl₂ := by
            intro x
            apply Iff.intro
            . intro hx
              have hmem12 := (hmem x).mp
              simp[hx] at hmem12
              rcases hmem12 with hhd|htl
              . rw[← hd₁eqhd₂] at hhd
                have hnodup := noDupKey (hd₁::tl₁) h₁
                rw[List.pairwise_cons] at hnodup
                rw[hhd] at hx
                have := hnodup.left hd₁ hx
                simp at this
              . exact htl
            . intro hx
              have hmem21 := (hmem x).mpr
              simp[hx] at hmem21
              rcases hmem21 with hhd|htl
              . rw[hd₁eqhd₂] at hhd
                have hnodup := noDupKey (hd₂::tl₂) h₂
                rw[List.pairwise_cons] at hnodup
                rw[hhd] at hx
                have := hnodup.left hd₂ hx
                simp at this
              . exact htl
          exact ih tl₂ h₁.left h₂.left hcondtl₂

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

theorem KeyValueList.erase_find (l : List (α×β)) (h: KeyValueList l) (a: α):
  (l.eraseP (·.1=a)).find? (·.1=a) = none := by
    induction l with
    | nil => tauto
    | cons hd tl ih =>
      by_cases h' : hd.1 = a
      . simp[h']
        have hnoDupKey := noDupKey (hd::tl) h
        rw[← h']
        intro a' b ha'b
        rw[List.pairwise_cons] at hnoDupKey
        have := hnoDupKey.left (a',b) ha'b
        simp[ne_comm] at this
        assumption
      . simp[h']
        intro a' b ha'b
        have hi := ih h.left
        simp at hi
        exact hi a' b ha'b

theorem KeyValueList.orderedInsert [DecidableEq β]
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
        exact orderedInsert (hd::tl) h a b h'
      | some (a,b') =>
        simp[h']
        exact orderedInsert
          ((hd::tl).eraseP (·.1 = a))
          (erase (hd :: tl) h a)
          a
          (b+b')
          (erase_find (hd :: tl) h a)

theorem KeyValueList.addKV_spec [DecidableEq β] [Add β] (l: List (α×β)) (h: KeyValueList l) (a: α) (b: β):
  ∀ x, x ∈ l.addKV a b ↔
    (x.1 ≠ a ∧ x ∈ l) ∨
    (x.1 = a ∧ (¬ (∃ y ∈ l, y.1=a) ∧ x=(a,b) ∨
                  (∃ y ∈ l, y.1=a ∧ x=(a,b+y.2)))) := by
  simp
  intro xa xb
  induction l with
  | nil =>
    unfold List.addKV
    simp
  | cons hd tl ih =>
    simp
    by_cases hxa : xa = a
    . simp[hxa]
      by_cases hhda : hd.1 = a
      . unfold List.addKV
        simp[LEByKey,hhda]
        have nodup := noDupKey (hd::tl) h
        rw[List.pairwise_cons] at nodup
        apply Iff.intro
        . intro hmp
          have := nodup.left (a,xb)
          simp[hhda] at this
          simp[this] at hmp
          simp[hmp]
          right
          use a, hd.2
          simp[← hhda]
        . intro hmpr
          left
          rcases hmpr with h₁|h₂
          . simp[h₁]
            rw[← hhda] at h₁
            have := h₁.left hd.2
            simp at this
          . let ⟨a₁,b₁,h₂'⟩:=h₂
            let ⟨h₂'₁,h₂'₂,h₂'₃⟩:=h₂'
            rw[h₂'₃]
            rw[h₂'₂] at h₂'₁
            rcases h₂'₁ with hi|hj
            . simp[Prod.eq_iff_fst_eq_snd_eq] at hi
              simp[hi]
            . have := nodup.left (a,b₁) hj
              simp[hhda] at this
      . unfold List.addKV
        simp[LEByKey,hhda]
        sorry
    . simp[hxa]
      simp[hxa] at ih
      by_cases hxhd : hd=(xa,xb)
      . simp[hxhd]
        unfold List.addKV

        simp[hxa]
        sorry
      . sorry


def KeyValueList.addKVFold [DecidableEq β] [Add β]
  (ab: α×β) (l : {l: List (α×β) // KeyValueList l}) :
  {l: List (α×β) // KeyValueList l} := ⟨l.val.addKV ab.1 ab.2, KeyValueList.addKV _ l.property _ _⟩

instance [DecidableEq β] [AddCommMagma β]:
  @LeftCommutative (α×β) _ (KeyValueList.addKVFold) where
  left_comm ab₁ ab₂ l := by
    unfold KeyValueList.addKVFold
    simp
    induction l.val with
    | nil =>
      simp[List.addKV]
      by_cases h : ab₁.1 = ab₂.1
      . simp[h]
        exact add_comm _ _
      . have h' : ¬ ab₂.1 = ab₁.1 := fun a ↦ h (id (Eq.symm a))
        simp[h,h']
        by_cases h12 : ab₁.1 ≤ ab₂.1
        . have h12': ¬ ab₂.1 ≤ ab₁.1 := not_le_of_gt (lt_of_le_of_ne h12 h)
          simp [h12,h12',LEByKey]
        . simp[h12,le_of_lt (lt_of_not_le h12),LEByKey]
    | cons hd tl ih =>
      sorry
