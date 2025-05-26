import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Sort
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.List.Nodup

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

theorem KeyValueList.nodup (l: List (α×β)) (hl: KeyValueList l) :
  l.Nodup := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      rw[List.nodup_cons]
      constructor
      . induction tl with
        | nil => simp
        | cons hd' tl' ih' =>
          simp[KeyValueList] at hl
          simp
          constructor
          . exact fun a ↦ (ne_of_lt hl.right) (congrArg Prod.fst a)
          . have hih' : KeyValueList tl' → tl'.Nodup := by
              intro htl'
              have := ih hl.left
              rw[List.nodup_cons] at this
              exact this.right
            have h' := ih' hih'
            have hkvl : KeyValueList (hd::tl') := by
              simp[KeyValueList]
              cases tl' with
              | nil =>
                simp[KeyValueList]
              | cons hd'' tl'' =>
                simp
                constructor
                . exact hl.left.left
                . exact lt_trans hl.right hl.left.right
            exact h' hkvl
      . exact ih hl.left

theorem KeyValueList.nodupkey (l : List (α×β)) (h: KeyValueList l):
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

theorem KeyValueList.functional (l : List (α×β)) (hl: KeyValueList l):
  ∀ x ∈ l, ∀ y ∈ l, x.1=y.1 → x.2=y.2 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hnodup := nodupkey (hd::tl) hl
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
              . have hnodup := nodupkey (hd₂::tl₂) h₂
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
                have hnodup := nodupkey (hd₁::tl₁) h₁
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
                have hnodup := nodupkey (hd₂::tl₂) h₂
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
        have hnodupkey := nodupkey (hd::tl) h
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

lemma KeyValueList.eraseP_eq_filter {l : List (α×β)} (hl: KeyValueList l) (a: α):
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
      have nodup := (List.nodup_cons.mp (nodup (hd::tl) hl)).left
      have functional := functional (hd::tl) hl hd (by simp) y (by simp[hy])
      simp[h,hc] at functional
      have : (y.1,y.2) ∉ tl := by
        rw[hc,← h,← functional]
        exact nodup
      contradiction
    · simp[h]
      have := ih hl.left
      simp at this
      exact this

lemma KeyValueList.addKV_spec_not_key [DecidableEq β] [Add β] (l: List (α×β)) (hl: KeyValueList l) (a: α) (b: β):
  ∀ x, (x.1 ≠ a) → (x ∈ l.addKV a b ↔ x ∈ l) := by
    intro x hxa
    cases l with
    | nil =>
      simp[List.addKV]
      exact ne_of_apply_ne Prod.fst hxa
    | cons hd tl =>
      apply Iff.intro
      . intro hyp
        simp[List.addKV,hxa] at hyp
        simp
        by_cases hxhd: x=hd
        . left; exact hxhd
        . right
          cases hf: List.find? (·.1 = a) (hd :: tl) with
          | none =>
            simp[hf] at hyp
            by_cases le: a≤hd.1 <;> simp[LEByKey,le] at hyp <;>
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
        simp[List.addKV,hxa]
        rcases hyp with hyp₁|hyp₂
        . cases hf: List.find? (·.1 = a) (hd :: tl) with
          | none =>
            by_cases le: a≤hd.1 <;> simp[LEByKey,le] <;> simp[hyp₁]
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
          by_cases le: a≤hd.1 <;> simp[LEByKey,le] <;> simp[hyp₂]
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

lemma KeyValueList.addKV_spec_key_not_before [DecidableEq β] [Add β] (l: List (α×β)) (hl: KeyValueList l) (a: α) (b: β):
  ∀ x, (x.1 = a) → ¬ (∃ z, (a,z) ∈ l) → (x ∈ l.addKV a b ↔ x=(a,b)) := by
    intro x hxa hz
    cases l with
    | nil =>
      simp[List.addKV]
    | cons hd tl =>
      simp[List.addKV]
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
      by_cases hle: a≤hd.1 <;> simp[hle,LEByKey,hz]

lemma KeyValueList.addKV_spec_key_before [DecidableEq β] [Add β] (l: List (α×β)) (hl: KeyValueList l) (a: α) (b: β):
  ∀ x, (x.1 = a) → ∀ z, (a,z) ∈ l → (x ∈ l.addKV a b ↔ x=(a,b+z)) := by
    intro x hxa z hz
    cases l with
    | nil =>
      simp at hz
    | cons hd tl =>
      simp[List.addKV]
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
          have := functional _ hl _ h' _ hz
          simp at this
          by_contra hc
          have := this hc
          rw[this,hc] at hs
          rw[hzst] at hl
          have := List.nodup_append.mp (KeyValueList.nodup (s ++ (a, z) :: t) hl)
          unfold List.Disjoint at this
          have problem := this.right.right
          simp at problem
          have := problem a z hs
          simp at this
      simp[hsome]
      intro hx
      rw[eraseP_eq_filter hl] at hx
      rw[List.mem_filter] at hx
      have := hx.right
      simp[hxa] at this

theorem KeyValueList.addKV_spec [DecidableEq β] [Add β]
  (l: List (α×β)) (hl: KeyValueList l) (a: α) (b: β):
  ∀ x, x ∈ l.addKV a b ↔
    (x.1 ≠ a ∧ x ∈ l) ∨
    (x.1 = a ∧ (¬ (∃ z, (a,z) ∈ l) ∧ x=(a,b) ∨
                  (∃ z, (a,z) ∈ l ∧ x=(a,b+z)))) := by
  intro x
  by_cases hxa : x.1 = a
  . by_cases hz: ∃ z, (a,z)∈ l
    . simp[hxa,hz]
      rcases hz with ⟨z, hz'⟩
      have := addKV_spec_key_before l hl a b x hxa
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
        have func := functional l hl _ h₁ _ hz'
        simp at func
        rw[func] at h₂
        exact this.mpr h₂
    . simp[hxa,hz]
      have := addKV_spec_key_not_before l hl a b x hxa hz
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
    exact addKV_spec_not_key l hl a b x hxa


theorem KeyValueList.addKV_mem [DecidableEq β] [Add β] (l: List (α×β)) (h: KeyValueList l) (a: α) (b: β):
  ∃ b', (a,b') ∈ l.addKV a b := by
    simp[List.addKV]
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
          simp[htl]
          by_cases hb': b'=b
          . simp[hb',LEByKey]
            by_cases hle : a≤hd.1 <;> simp[hle]
          . simp[hb'] at ih'
            have hgt : a > hd.1 := by
              have := (List.sorted_cons.mp (KeyValueList.sorted (hd::tl) h)).left (a,b') ih'
              simp[LEByKey] at this
              exact lt_of_le_of_ne this hhd
            simp[LEByKey]
            simp[not_le_of_gt hgt]
            tauto
        | some val =>
          simp[htl] at ih'
          simp[htl]
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

def KeyValueList.addKVFold [DecidableEq β] [Add β]
  (ab: α×β) (l : {l: List (α×β) // KeyValueList l}) :
  {l: List (α×β) // KeyValueList l} := ⟨l.val.addKV ab.1 ab.2, KeyValueList.addKV _ l.property _ _⟩

lemma KeyValueList.add_comm_internal [DecidableEq β] [AddCommSemigroup β]
  (l: List (α×β)) (hl: KeyValueList l) (a₁ a₂ a: α) (b₁ b₂ b: β):
  (a,b) ∈ (l.addKV a₂ b₂).addKV a₁ b₁ → (a,b) ∈ (l.addKV a₁ b₁).addKV a₂ b₂ := by
  repeat rw[KeyValueList.addKV_spec _ (KeyValueList.addKV l hl _ _)]
  repeat rw[KeyValueList.addKV_spec l hl]

  . by_cases hy : a₁=a₂ <;>
    by_cases hx₁: a=a₁ <;>
    by_cases hx₂: a=a₂ <;> simp[hy,hx₁,hx₂,eq_comm,ne_comm]
    any_goals repeat rw[← hy]
    any_goals repeat rw[← hx₁]
    any_goals repeat rw[← hx₂]
    any_goals simp[hy,hx₁,hx₂,eq_comm,ne_comm]
    any_goals repeat rw[← hy]
    any_goals repeat rw[← hx₁]
    any_goals repeat rw[← hx₂]
    . intro h
      right
      rcases h with hwrong|hright
      . have := addKV_mem l hl a b₂
        rcases this with ⟨b',hb'⟩
        rcases hwrong with ⟨hwrongl,hwrongr⟩
        specialize hwrongl b'
        contradiction
      . rcases hright with ⟨b',hab⟩
        rw[addKV_spec l hl] at hab
        simp at hab
        rcases hab with ⟨habl|habr,hr⟩
        . by_cases hb : ∀ z, (a,z) ∉ l
          . simp[hb] at habl
            use b₁
            rw[addKV_spec l hl]
            simp[hy,hx₁,hx₂,eq_comm,ne_comm]
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
          simp[addKV_spec l hl]
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
          rw[addKV_spec l hl] at hz'
          simp[hx₂] at hz'
          contradiction
      . right
        simp at hz
        rcases hz with ⟨z,hz⟩
        use z
        simp[hz]
        rcases h with h₁|h₂
        . have := h₁.left z
          rw[addKV_spec l hl] at this
          simp[hx₂,hy] at this
          contradiction
        . rcases h₂ with ⟨z',hz',h₂⟩
          rw[addKV_spec l hl] at hz'
          simp[hx₂,hy] at hz'
          have hzz': z=z' := by
            have := functional l hl _ hz _ hz'
            simp at this
            assumption
          simp[h₂,hzz']
    . intro h
      by_cases hz: ∀ z: β, (a,z) ∉ l
      . left
        rcases h with h₁|h₂
        . constructor
          . intro z
            rw[addKV_spec l hl]
            simp[hy,hx₁]
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
        . rw[addKV_spec l hl]
          simp[hx₁,hy]
          exact hz
        . rcases h with h₁|h₂
          . rcases h₁ with ⟨h₁₁,h₁₂⟩
            specialize h₁₁ z
            contradiction
          . rcases h₂ with ⟨z',hz',h₂⟩
            have hzz': z=z' := by
              have := functional l hl _ hz _ hz'
              simp at this
              assumption
            rw[hzz']
            assumption

instance [DecidableEq β] [AddCommSemigroup β]:
  @LeftCommutative (α×β) _ (KeyValueList.addKVFold) where
  left_comm ab₁ ab₂ l := by
    unfold KeyValueList.addKVFold
    simp
    rw[KeyValueList.eq_iff_forall_mem]
    intro x

    apply Iff.intro
    . exact KeyValueList.add_comm_internal _ l.property _ _ _ _ _ _
    . exact KeyValueList.add_comm_internal _ l.property _ _ _ _ _ _
    . exact KeyValueList.addKV _ (KeyValueList.addKV l.val l.property _ _) _ _
    . exact KeyValueList.addKV _ (KeyValueList.addKV l.val l.property _ _) _ _
