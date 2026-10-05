import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Sort
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.List.Nodup
import Lax392996.AnnotatedDatabases
import Lax392996.AnnotatedSemantics
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.MultisetSemantics
import Lax392996.ProbabilisticDatabases
import Lax392996.RelationalAlgebra
import Lax392996.RewritingRules
import Lax392996.SemiringsWithMonus
import Lax392996.WhyProvenance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace Lax392996Proofs.Foreign
end Lax392996Proofs.Foreign

namespace Lax392996Proofs.Foreign.KeyValueList
end Lax392996Proofs.Foreign.KeyValueList

namespace Lax392996Proofs.Foreign.List
end Lax392996Proofs.Foreign.List

variable {α: Type} [LinearOrder α]

def _root_.Lax392996Proofs.Foreign.LEByKey (a b: Prod α β) : Prop :=
  a.fst <= b.fst

export Lax392996Proofs.Foreign (LEByKey)

instance _root_.Lax392996Proofs.Foreign.instDecidableRelProdLEByKey : DecidableRel (λ (a b: α×β) ↦ Lax392996Proofs.Foreign.LEByKey a b) :=
  λ a b ↦ if h : a.fst <= b.fst then isTrue (h) else isFalse (h)

instance _root_.Lax392996Proofs.Foreign.instTotalProdLEByKey : Std.Total (α := α × β) Lax392996Proofs.Foreign.LEByKey where
  total := by
    intro a b
    unfold Lax392996Proofs.Foreign.LEByKey
    exact le_total _ _

instance _root_.Lax392996Proofs.Foreign.instIsTransProdLEByKey : IsTrans (α × β) Lax392996Proofs.Foreign.LEByKey where
  trans := by
    intro a b c
    unfold Lax392996Proofs.Foreign.LEByKey
    exact Preorder.le_trans _ _ _

def _root_.Lax392996Proofs.Foreign.KeyValueList (l : List (α×β)) := match l with
| []     => True
| hd::tl => Lax392996Proofs.Foreign.KeyValueList tl ∧ match tl with
  | []     => True
  | hd'::_ => hd.1<hd'.1

export Lax392996Proofs.Foreign (KeyValueList)

open Lax392996Proofs.Foreign.List in
def _root_.Lax392996Proofs.Foreign.List.addKV [DecidableEq β] [Add β] (l: List (α×β)) (a: α) (b: β) :=
  match l.find? (·.1=a) with
  | none        => l.orderedInsert Lax392996Proofs.Foreign.LEByKey (a,b)
  | some (a,b') => (l.eraseP (Prod.fst · = a)).orderedInsert Lax392996Proofs.Foreign.LEByKey (a,b+b')

namespace List
export Lax392996Proofs.Foreign.List (addKV)
end List

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.sorted (l: List (α×β)) (h: Lax392996Proofs.Foreign.KeyValueList l) :
  l.Pairwise Lax392996Proofs.Foreign.LEByKey := by
    induction l with
    | nil           => simp
    | cons hd tl ih =>
      apply List.pairwise_cons.mpr
      simp[Lax392996Proofs.Foreign.KeyValueList] at h
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
            rw[List.pairwise_cons] at sorted_tail
            exact le_of_lt (lt_of_lt_of_le h.right (sorted_tail.left b hb))
      . exact ih h.left

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (sorted)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.nodup (l: List (α×β)) (hl: Lax392996Proofs.Foreign.KeyValueList l) :
  l.Nodup := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      rw[List.nodup_cons]
      constructor
      . induction tl with
        | nil => simp
        | cons hd' tl' ih' =>
          simp[Lax392996Proofs.Foreign.KeyValueList] at hl
          simp
          constructor
          . exact fun a ↦ (ne_of_lt hl.right) (congrArg Prod.fst a)
          . have hih' : Lax392996Proofs.Foreign.KeyValueList tl' → tl'.Nodup := by
              intro htl'
              have := ih hl.left
              rw[List.nodup_cons] at this
              exact this.right
            have h' := ih' hih'
            have hkvl : Lax392996Proofs.Foreign.KeyValueList (hd::tl') := by
              simp[Lax392996Proofs.Foreign.KeyValueList]
              cases tl' with
              | nil =>
                simp[Lax392996Proofs.Foreign.KeyValueList]
              | cons hd'' tl'' =>
                simp
                constructor
                . exact hl.left.left
                . exact lt_trans hl.right hl.left.right
            exact h' hkvl
      . exact ih hl.left

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (nodup)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.nodupkey (l : List (α×β)) (h: Lax392996Proofs.Foreign.KeyValueList l):
  List.Pairwise (·.1≠·.1) l := by
    induction l with
    | nil => tauto
    | cons hd tl ih =>
      rw[List.pairwise_cons]
      constructor
      . unfold Lax392996Proofs.Foreign.KeyValueList at h
        induction tl with
        | nil => tauto
        | cons hd' tl' ih' =>
          intro a' ha'
          rcases ha'
          . simp at h
            exact ne_of_lt h.right
          . rename_i ha'
            have hb : Lax392996Proofs.Foreign.KeyValueList tl' → List.Pairwise (·.1≠·.1) tl' := by
              intro hb'
              have := ih h.left
              exact List.Pairwise.of_cons this
            have hc: (Lax392996Proofs.Foreign.KeyValueList tl' ∧ match tl' with | [] => True | hd' :: tail => hd.1 < hd'.1) := by
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

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (nodupkey)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.functional (l : List (α×β)) (hl: Lax392996Proofs.Foreign.KeyValueList l):
  ∀ x ∈ l, ∀ y ∈ l, x.1=y.1 → x.2=y.2 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hnodup := Lax392996Proofs.Foreign.KeyValueList.nodupkey (hd::tl) hl
    rw[List.pairwise_cons] at hnodup
    intro x hx y hy
    cases hx with
    | head =>
      cases hy with
      | head => tauto
      | tail =>
        rename_i ytl
        simp[hnodup.left y ytl]
    | tail xtl =>
      rename_i xtl
      cases hy with
      | head =>
        simp[hnodup.left x xtl,ne_comm]
      | tail ytl =>
        rename_i ytl
        exact ih hl.left x xtl y ytl

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (functional)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.eq_iff_forall_mem [DecidableEq β]
  (l₁ l₂ : List (α×β)) (h₁: Lax392996Proofs.Foreign.KeyValueList l₁) (h₂: Lax392996Proofs.Foreign.KeyValueList l₂):
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
              . have hs := Lax392996Proofs.Foreign.KeyValueList.sorted (hd₂::tl₂) h₂
                rw[List.pairwise_cons] at hs
                have hc := hs.left hd₁ h'₂
                simp[Lax392996Proofs.Foreign.LEByKey] at hc
                have := lt_of_lt_of_le hlt hc
                simp at this
            . apply le_of_not_gt at hlt
              apply lt_or_eq_of_le at hlt
              rcases hlt with hlt'|heq'
              . have h2b1 := (hmem hd₂).mpr
                simp at h2b1
                rcases h2b1 with h'₁|h'₂
                . exact Eq.symm h'₁
                . have hs := Lax392996Proofs.Foreign.KeyValueList.sorted (hd₁::tl₁) h₁
                  rw[List.pairwise_cons] at hs
                  have hc := hs.left hd₂ h'₂
                  simp[Lax392996Proofs.Foreign.LEByKey] at hc
                  have := lt_of_lt_of_le hlt' hc
                  simp at this
              . have hnodup := Lax392996Proofs.Foreign.KeyValueList.nodupkey (hd₂::tl₂) h₂
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
                have hnodup := Lax392996Proofs.Foreign.KeyValueList.nodupkey (hd₁::tl₁) h₁
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
                have hnodup := Lax392996Proofs.Foreign.KeyValueList.nodupkey (hd₂::tl₂) h₂
                rw[List.pairwise_cons] at hnodup
                rw[hhd] at hx
                have := hnodup.left hd₂ hx
                simp at this
              . exact htl
          exact ih tl₂ h₁.left h₂.left hcondtl₂

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (eq_iff_forall_mem)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.erase (l : List (α×β)) (h: Lax392996Proofs.Foreign.KeyValueList l) (a: α):
  Lax392996Proofs.Foreign.KeyValueList (l.eraseP (·.1=a)) := by
  induction l with
  | nil           =>
    unfold Lax392996Proofs.Foreign.KeyValueList
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
          unfold Lax392996Proofs.Foreign.KeyValueList at h
          simp at h
          by_cases h'': hd'.1=a
          . simp[h'']
            unfold Lax392996Proofs.Foreign.KeyValueList at h
            cases tl' with
            | nil        => simp
            | cons hd' _ =>
              simp
              simp at h
              exact lt_trans h.right h.left.right
          . simp[h'']
            exact h.right

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (erase)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.erase_find (l : List (α×β)) (h: Lax392996Proofs.Foreign.KeyValueList l) (a: α):
  (l.eraseP (·.1=a)).find? (·.1=a) = none := by
    induction l with
    | nil => tauto
    | cons hd tl ih =>
      by_cases h' : hd.1 = a
      . simp[h']
        have hnodupkey := Lax392996Proofs.Foreign.KeyValueList.nodupkey (hd::tl) h
        rw[← h']
        intro a' b ha'b
        rw[List.pairwise_cons] at hnodupkey
        have := hnodupkey.left (a',b) ha'b
        simp[ne_comm] at this
        assumption
      . simp[h']
        intro a' b ha'b
        have hi := ih h.left
        simp at hi
        exact hi a' b ha'b

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (erase_find)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.orderedInsert [DecidableEq β]
  (l : List (α×β)) (h: Lax392996Proofs.Foreign.KeyValueList l) (a: α) (b: β) (hp: l.find? (·.1=a) = none):
  Lax392996Proofs.Foreign.KeyValueList (l.orderedInsert Lax392996Proofs.Foreign.LEByKey (a,b)) := by
    induction l with
    | nil           => simp[Lax392996Proofs.Foreign.KeyValueList]
    | cons hd tl ih =>
      simp
      by_cases hab : a < hd.1 <;> simp[le_of_lt,hab,Lax392996Proofs.Foreign.LEByKey]
      . constructor
        . exact h
        . exact hab
      . have hnle : ¬ a≤hd.1 := by
          simp
          simp at hab
          simp at hp
          exact lt_of_le_of_ne hab hp.left
        simp[hnle]
        unfold Lax392996Proofs.Foreign.KeyValueList
        constructor
        . rw[List.find?_cons] at hp
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
          | nil          => exact lt_of_not_ge hnle
          | cons hd' _   =>
            simp
            by_cases h'': a<=hd'.1 <;> simp[h'',Lax392996Proofs.Foreign.LEByKey]
            . exact lt_of_not_ge hnle
            . exact h.right

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (orderedInsert)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.addKV [DecidableEq β] [Add β] (l : List (α×β)) (h: Lax392996Proofs.Foreign.KeyValueList l) (a: α) (b: β):
  Lax392996Proofs.Foreign.KeyValueList (l.addKV a b) := by
    induction l with
    | nil           =>
      unfold Lax392996Proofs.Foreign.List.addKV
      simp[Lax392996Proofs.Foreign.KeyValueList]
    | cons hd tl ih =>
      unfold Lax392996Proofs.Foreign.List.addKV
      match h' : (hd::tl).find? (·.1=a) with
      | none =>
        simp[h']
        exact Lax392996Proofs.Foreign.KeyValueList.orderedInsert (hd::tl) h a b h'
      | some (a,b') =>
        simp[h']
        exact Lax392996Proofs.Foreign.KeyValueList.orderedInsert
          ((hd::tl).eraseP (·.1 = a))
          (Lax392996Proofs.Foreign.KeyValueList.erase (hd :: tl) h a)
          a
          (b+b')
          (Lax392996Proofs.Foreign.KeyValueList.erase_find (hd :: tl) h a)

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (addKV)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
lemma _root_.Lax392996Proofs.Foreign.KeyValueList.eraseP_eq_filter {l : List (α×β)} (hl: Lax392996Proofs.Foreign.KeyValueList l) (a: α):
    l.eraseP (·.1=a) = l.filter (·.1≠a) := by
  induction l with
  | nil => simp [List.eraseP, List.filter]
  | cons hd tl ih =>
    simp only [List.eraseP, List.filter]
    by_cases h : hd.1=a
    . simp[h]
      have : tl = List.filter (fun x ↦ true) tl := by simp
      nth_rewrite 1 [this]
      apply List.filter_congr
      intro y hy
      by_contra hc
      simp at hc
      have nodup := (List.nodup_cons.mp (Lax392996Proofs.Foreign.KeyValueList.nodup (hd::tl) hl)).left
      have functional := Lax392996Proofs.Foreign.KeyValueList.functional (hd::tl) hl hd (by simp) y (by simp[hy])
      simp[h,hc] at functional
      have : (y.1,y.2) ∉ tl := by
        rw[hc,← h,← functional]
        exact nodup
      contradiction
    · simp[h]
      have := ih hl.left
      simp at this
      exact this

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (eraseP_eq_filter)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
lemma _root_.Lax392996Proofs.Foreign.KeyValueList.addKV_spec_not_key [DecidableEq β] [Add β] (l: List (α×β)) (hl: Lax392996Proofs.Foreign.KeyValueList l) (a: α) (b: β):
  ∀ x, (x.1 ≠ a) → (x ∈ l.addKV a b ↔ x ∈ l) := by
    intro x hxa
    cases l with
    | nil =>
      simp[Lax392996Proofs.Foreign.List.addKV]
      exact ne_of_apply_ne Prod.fst hxa
    | cons hd tl =>
      apply Iff.intro
      . intro hyp
        simp[Lax392996Proofs.Foreign.List.addKV] at hyp
        simp
        by_cases hxhd: x=hd
        . left; exact hxhd
        . right
          cases hf: List.find? (·.1 = a) (hd :: tl) with
          | none =>
            simp[hf] at hyp
            by_cases le: a≤hd.1 <;> simp[Lax392996Proofs.Foreign.LEByKey,le] at hyp <;>
            rcases hyp with hyp₁|hyp₂|hyp₃
            . rw[hyp₁] at hxa
              contradiction
            . contradiction
            . exact hyp₃
            . contradiction
            . rw[hyp₂] at hxa
              contradiction
            . exact hyp₃
          | some val =>
            simp[hf] at hyp
            have hp := List.find?_some hf
            simp at hp
            rcases hyp with hyp₁|hyp₂
            . rw[hyp₁] at hxa
              rw[hp] at hxa
              contradiction
            . rw[List.mem_eraseP_of_neg] at hyp₂
              . simp[hxhd] at hyp₂
                exact hyp₂
              . simp
                rw[hp]
                exact hxa
      . intro hyp
        simp at hyp
        simp[Lax392996Proofs.Foreign.List.addKV]
        rcases hyp with hyp₁|hyp₂
        . cases hf: List.find? (·.1 = a) (hd :: tl) with
          | none =>
            by_cases le: a≤hd.1 <;> simp[Lax392996Proofs.Foreign.LEByKey,le] <;> simp[hyp₁]
          | some val =>
            simp
            right
            rw[List.eraseP_cons]
            have hp := List.find?_some hf
            simp at hp
            rw[hp]
            rw[← hyp₁]
            simp[hxa]
        . cases hf: List.find? (·.1 = a) (hd :: tl) with
        | none =>
          by_cases le: a≤hd.1 <;> simp[Lax392996Proofs.Foreign.LEByKey,le] <;> simp[hyp₂]
        | some val =>
          simp
          right
          rw[List.eraseP_cons]
          have hp := List.find?_some hf
          simp at hp
          rw[hp]
          by_cases hhda: hd.1=a
          . simp[hhda]
            exact hyp₂
          . simp[hhda]
            right
            rw[List.mem_eraseP_of_neg]
            . exact hyp₂
            . simp[hxa]

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (addKV_spec_not_key)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
lemma _root_.Lax392996Proofs.Foreign.KeyValueList.addKV_spec_key_not_before [DecidableEq β] [Add β] (l: List (α×β)) (hl: Lax392996Proofs.Foreign.KeyValueList l) (a: α) (b: β):
  ∀ x, (x.1 = a) → ¬ (∃ z, (a,z) ∈ l) → (x ∈ l.addKV a b ↔ x=(a,b)) := by
    intro x hxa hz
    cases l with
    | nil =>
      simp[Lax392996Proofs.Foreign.List.addKV]
    | cons hd tl =>
      simp[Lax392996Proofs.Foreign.List.addKV]
      have hnone : List.find? (·.1=a) (hd::tl) = none := by
        rw[List.find?_eq_none]
        simp at hz
        intro y hy
        simp
        specialize hz y.2
        by_contra hc
        rw[← hc] at hz
        simp[hz] at hy
      simp[hnone]
      simp at hz
      specialize hz x.2
      rw[← hxa] at hz
      simp at hz
      by_cases hle: a≤hd.1 <;> simp[hle,Lax392996Proofs.Foreign.LEByKey,hz]

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (addKV_spec_key_not_before)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
lemma _root_.Lax392996Proofs.Foreign.KeyValueList.addKV_spec_key_before [DecidableEq β] [Add β] (l: List (α×β)) (hl: Lax392996Proofs.Foreign.KeyValueList l) (a: α) (b: β):
  ∀ x, (x.1 = a) → ∀ z, (a,z) ∈ l → (x ∈ l.addKV a b ↔ x=(a,b+z)) := by
    intro x hxa z hz
    cases l with
    | nil =>
      simp at hz
    | cons hd tl =>
      simp[Lax392996Proofs.Foreign.List.addKV]
      have hsome : List.find? (·.1=a) (hd::tl) = some (a, z) := by
        rw[List.find?_eq_some_iff_append]
        simp
        have hz₂ := hz
        rw[List.mem_iff_append] at hz₂
        rcases hz₂ with ⟨s,t,hzst⟩
        use s
        constructor
        . use t
        . intro a' b' hs
          have h': (a',b') ∈ s ++ (a,z) :: t := List.mem_append_left ((a, z) :: t) hs
          rw[← hzst] at h'
          have := Lax392996Proofs.Foreign.KeyValueList.functional _ hl _ h' _ hz
          simp at this
          by_contra hc
          have := this hc
          rw[this,hc] at hs
          rw[hzst] at hl
          have := List.nodup_append.mp (Lax392996Proofs.Foreign.KeyValueList.nodup (s ++ (a, z) :: t) hl)
          have problem := this.right.right
          simp at problem
          have := problem a z hs
          simp at this
      simp[hsome]
      intro hx
      rw[Lax392996Proofs.Foreign.KeyValueList.eraseP_eq_filter hl] at hx
      rw[List.mem_filter] at hx
      have := hx.right
      simp[hxa] at this

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (addKV_spec_key_before)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.addKV_spec [DecidableEq β] [Add β]
  (l: List (α×β)) (hl: Lax392996Proofs.Foreign.KeyValueList l) (a: α) (b: β):
  ∀ x, x ∈ l.addKV a b ↔
    (x.1 ≠ a ∧ x ∈ l) ∨
    (x.1 = a ∧ (¬ (∃ z, (a,z) ∈ l) ∧ x=(a,b) ∨
                  (∃ z, (a,z) ∈ l ∧ x=(a,b+z)))) := by
  intro x
  by_cases hxa : x.1 = a
  . by_cases hz: ∃ z, (a,z)∈ l
    . simp[hxa,hz]
      rcases hz with ⟨z, hz'⟩
      have := Lax392996Proofs.Foreign.KeyValueList.addKV_spec_key_before l hl a b x hxa
      specialize this z
      simp[hz'] at this
      apply Iff.intro
      . intro hx
        use z
        constructor
        . exact hz'
        . exact this.mp hx
      . intro hz
        rcases hz with ⟨z' ,hz''⟩
        rcases hz'' with ⟨h₁,h₂⟩
        have func := Lax392996Proofs.Foreign.KeyValueList.functional l hl _ h₁ _ hz'
        simp at func
        rw[func] at h₂
        exact this.mpr h₂
    . simp[hxa,hz]
      have := Lax392996Proofs.Foreign.KeyValueList.addKV_spec_key_not_before l hl a b x hxa hz
      apply Iff.intro
      . intro hx
        left
        exact this.mp hx
      . intro hz
        rcases hz with hz₁|⟨z,hz₂,hz₃⟩
        . exact this.mpr hz₁
        . simp at hz
          specialize hz z
          contradiction
  . simp[hxa]
    exact Lax392996Proofs.Foreign.KeyValueList.addKV_spec_not_key l hl a b x hxa

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (addKV_spec)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
theorem _root_.Lax392996Proofs.Foreign.KeyValueList.addKV_mem [DecidableEq β] [Add β] (l: List (α×β)) (h: Lax392996Proofs.Foreign.KeyValueList l) (a: α) (b: β):
  ∃ b', (a,b') ∈ l.addKV a b := by
    simp[Lax392996Proofs.Foreign.List.addKV]
    induction l with
    | nil           => simp
    | cons hd tl ih =>
      by_cases hhd: hd.1 = a
      . simp[hhd]
      . simp[hhd]
        rcases ih h.left with ⟨b', ih'⟩
        use b'
        cases htl : List.find? (·.1=a) tl with
        | none =>
          simp[htl] at ih'
          simp
          by_cases hb': b'=b
          . simp[hb',Lax392996Proofs.Foreign.LEByKey]
            by_cases hle : a≤hd.1 <;> simp[hle]
          . simp[hb'] at ih'
            have hgt : a > hd.1 := by
              have := (List.pairwise_cons.mp (Lax392996Proofs.Foreign.KeyValueList.sorted (hd::tl) h)).left (a,b') ih'
              simp[Lax392996Proofs.Foreign.LEByKey] at this
              exact lt_of_le_of_ne this hhd
            simp[Lax392996Proofs.Foreign.LEByKey]
            simp[not_le_of_gt hgt]
            tauto
        | some val =>
          simp[htl] at ih'
          simp
          rcases ih' with ih'₁|ih'₂
          . tauto
          . right
            rw[List.eraseP_cons]
            have hvala : val.1=a := by
              have := List.find?_some htl
              exact decide_eq_true_eq.mp this
            rw[hvala]
            rw[hvala] at ih'₂
            simp[hhd]
            right
            exact ih'₂

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (addKV_mem)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
def _root_.Lax392996Proofs.Foreign.KeyValueList.addKVFold [DecidableEq β] [Add β]
  (ab: α×β) (l : {l: List (α×β) // Lax392996Proofs.Foreign.KeyValueList l}) :
  {l: List (α×β) // Lax392996Proofs.Foreign.KeyValueList l} := ⟨l.val.addKV ab.1 ab.2, Lax392996Proofs.Foreign.KeyValueList.addKV _ l.property _ _⟩

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (addKVFold)
end KeyValueList

open Lax392996Proofs.Foreign.KeyValueList in
lemma _root_.Lax392996Proofs.Foreign.KeyValueList.add_comm_internal [DecidableEq β] [AddCommSemigroup β]
  (l: List (α×β)) (hl: Lax392996Proofs.Foreign.KeyValueList l) (a₁ a₂ a: α) (b₁ b₂ b: β):
  (a,b) ∈ (l.addKV a₂ b₂).addKV a₁ b₁ → (a,b) ∈ (l.addKV a₁ b₁).addKV a₂ b₂ := by
  repeat rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec _ (Lax392996Proofs.Foreign.KeyValueList.addKV l hl _ _)]
  repeat rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl]

  . by_cases hy : a₁=a₂ <;>
    by_cases hx₁: a=a₁ <;>
    by_cases hx₂: a=a₂ <;> simp[hy,hx₁,hx₂,eq_comm]
    any_goals repeat rw[← hy]
    any_goals repeat rw[← hx₁]
    any_goals repeat rw[← hx₂]
    any_goals simp[hy,hx₁,hx₂]
    any_goals repeat rw[← hy]
    any_goals repeat rw[← hx₁]
    any_goals repeat rw[← hx₂]
    . intro h
      right
      rcases h with hwrong|hright
      . have := Lax392996Proofs.Foreign.KeyValueList.addKV_mem l hl a b₂
        rcases this with ⟨b',hb'⟩
        rcases hwrong with ⟨hwrongl,hwrongr⟩
        specialize hwrongl b'
        contradiction
      . rcases hright with ⟨b',hab⟩
        rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl] at hab
        simp at hab
        rcases hab with ⟨habl|habr,hr⟩
        . by_cases hb : ∀ z, (a,z) ∉ l
          . simp[hb] at habl
            use b₁
            rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl]
            simp[hy,hx₁]
            rw[← hx₂]
            constructor
            . left
              assumption
            . rw[habl,add_comm] at hr
              exact hr
          . simp at hb
            rcases hb with ⟨z,hz⟩
            have := habl.left z
            contradiction
        . rcases habr with ⟨z,hz⟩
          use b₁+z
          simp[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl]
          constructor
          . right
            use z
            simp[*]
            rw[← hx₂]
            exact hz.left
          . rw[hz.right] at hr
            rw[← add_assoc]
            nth_rewrite 2 [add_comm]
            rw[add_assoc]
            exact hr
    . rw[hx₁,hy] at hx₂
      contradiction
    . rw[hx₂,← hy] at hx₁
      contradiction
    . rw[← hx₁,← hx₂] at hy
      contradiction
    . intro h
      by_cases hz: ∀ z: β, (a, z) ∉ l
      . left
        rcases h with h₁|h₂
        . constructor
          . exact hz
          . exact h₁.right
        . rcases h₂ with ⟨z',hz',h₂⟩
          specialize hz z'
          rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl] at hz'
          simp[hx₂] at hz'
          contradiction
      . right
        simp at hz
        rcases hz with ⟨z,hz⟩
        use z
        simp[hz]
        rcases h with h₁|h₂
        . have := h₁.left z
          rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl] at this
          simp[hx₂] at this
          contradiction
        . rcases h₂ with ⟨z',hz',h₂⟩
          rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl] at hz'
          simp[hx₂] at hz'
          have hzz': z=z' := by
            have := Lax392996Proofs.Foreign.KeyValueList.functional l hl _ hz _ hz'
            simp at this
            assumption
          simp[h₂,hzz']
    . intro h
      by_cases hz: ∀ z: β, (a,z) ∉ l
      . left
        rcases h with h₁|h₂
        . constructor
          . intro z
            rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl]
            simp[hx₁]
            exact hz z
          . exact h₁.right
        . rcases h₂ with ⟨z',hz',h₂⟩
          specialize hz z'
          contradiction
      . right
        simp at hz
        rcases hz with ⟨z,hz⟩
        use z
        constructor
        . rw[Lax392996Proofs.Foreign.KeyValueList.addKV_spec l hl]
          simp[hx₁]
          exact hz
        . rcases h with h₁|h₂
          . rcases h₁ with ⟨h₁₁,h₁₂⟩
            specialize h₁₁ z
            contradiction
          . rcases h₂ with ⟨z',hz',h₂⟩
            have hzz': z=z' := by
              have := Lax392996Proofs.Foreign.KeyValueList.functional l hl _ hz _ hz'
              simp at this
              assumption
            rw[hzz']
            assumption

namespace KeyValueList
export Lax392996Proofs.Foreign.KeyValueList (add_comm_internal)
end KeyValueList

instance _root_.Lax392996Proofs.Foreign.instLeftCommutativeProdSubtypeListKeyValueListAddKVFold [DecidableEq β] [AddCommSemigroup β] :
  @LeftCommutative (α×β) _ (Lax392996Proofs.Foreign.KeyValueList.addKVFold) where
  left_comm ab₁ ab₂ l := by
    unfold Lax392996Proofs.Foreign.KeyValueList.addKVFold
    simp
    rw[Lax392996Proofs.Foreign.KeyValueList.eq_iff_forall_mem]
    intro x

    apply Iff.intro
    . exact Lax392996Proofs.Foreign.KeyValueList.add_comm_internal _ l.property _ _ _ _ _ _
    . exact Lax392996Proofs.Foreign.KeyValueList.add_comm_internal _ l.property _ _ _ _ _ _
    . exact Lax392996Proofs.Foreign.KeyValueList.addKV _ (Lax392996Proofs.Foreign.KeyValueList.addKV l.val l.property _ _) _ _
    . exact Lax392996Proofs.Foreign.KeyValueList.addKV _ (Lax392996Proofs.Foreign.KeyValueList.addKV l.val l.property _ _) _ _


