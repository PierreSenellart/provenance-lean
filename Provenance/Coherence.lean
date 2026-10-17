/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.ReadsCongr
import Provenance.JointHom

/-!
# One family identifier, one value

An operator building aggregate values stamps each with a family
identifier: its label, the group key, the parameters it records, the
column, and the terms applied since. This file proves that across all the
evaluations a query performs – one per row of an apply's left side, one
per round of a recursion – two values carrying the same identifier are
the same value (`AggQueryIn.builds_coherent`). This is what lets a
recursion's body build values: what it builds in one round, it builds
again in the next.

Three things are asked of the query, each because an identifier would
otherwise not determine the value:

* `AggQueryIn.readsRecorded` – every operator records the parameters its
  subtree reads, so that equal parameters mean equal inputs;
* `AggQueryIn.labelsDistinct` – no two operators share a label;
* `AggQueryIn.sourceCols` – no projection column applies an arbitrary
  function to an aggregate value (`ProjColIn.aggTerm`, a column of the
  rewritten world), which the identifier would not record;
* `AggQueryIn.allFramesContainSelf` – every window frame contains the
  current row, so that a window's value is a function of the row's tuple;
  an `EXCLUDE CURRENT ROW` frame removes one occurrence of the row, which
  two rows with the same tuple but different annotations remove
  differently.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-! ## The fences -/

section Fences

/-- **Every window frame contains its current row**, single-frame windows
included. -/
def AggQueryIn.allFramesContainSelf : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.allFramesContainSelf
  | _, _, _, _, .Sel _ q _ => q.allFramesContainSelf
  | _, _, _, _, .Prod q₁ q₂ => q₁.allFramesContainSelf ∧ q₂.allFramesContainSelf
  | _, _, _, _, .Apply q₁ q₂ => q₁.allFramesContainSelf ∧ q₂.allFramesContainSelf
  | _, _, _, _, .Sum q₁ q₂ => q₁.allFramesContainSelf ∧ q₂.allFramesContainSelf
  | _, _, _, _, .Dedup q => q.allFramesContainSelf
  | _, _, _, _, .Diff q₁ q₂ => q₁.allFramesContainSelf ∧ q₂.allFramesContainSelf
  | _, _, _, _, .Explode _ _ q => q.allFramesContainSelf
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.allFramesContainSelf ∧ q₁.allFramesContainSelf
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.allFramesContainSelf ∧ q₁.allFramesContainSelf
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.allFramesContainSelf
  | _, _, _, _, .GammaScalar _ _ q _ => q.allFramesContainSelf
  | _, _, _, _, .GammaNest _ _ _ _ q => q.allFramesContainSelf
  | _, _, _, _, .ProvSum _ _ _ q => q.allFramesContainSelf
  | _, _, _, _, .Retag _ q => q.allFramesContainSelf
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.allFramesContainSelf
  | _, _, _, _, .Win _ _ _ w _ _ q _ _ _ => w.ContainsSelf ∧ q.allFramesContainSelf
  | _, _, _, _, .WinExpr _ _ _ ws _ _ _ q _ =>
      (∀ l, (ws l).ContainsSelf) ∧ q.allFramesContainSelf

/-- **Every projection column is one of the source language's**: none
applies an arbitrary function to an aggregate value. -/
def AggQueryIn.sourceCols : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj ps q => (∀ j, (ps j).sourceCol = true) ∧ q.sourceCols
  | _, _, _, _, .Sel _ q _ => q.sourceCols
  | _, _, _, _, .Prod q₁ q₂ => q₁.sourceCols ∧ q₂.sourceCols
  | _, _, _, _, .Apply q₁ q₂ => q₁.sourceCols ∧ q₂.sourceCols
  | _, _, _, _, .Sum q₁ q₂ => q₁.sourceCols ∧ q₂.sourceCols
  | _, _, _, _, .Dedup q => q.sourceCols
  | _, _, _, _, .Diff q₁ q₂ => q₁.sourceCols ∧ q₂.sourceCols
  | _, _, _, _, .Explode _ _ q => q.sourceCols
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.sourceCols ∧ q₁.sourceCols
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.sourceCols ∧ q₁.sourceCols
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.sourceCols
  | _, _, _, _, .GammaScalar _ _ q _ => q.sourceCols
  | _, _, _, _, .GammaNest _ _ p _ q => p.sourceCol = true ∧ q.sourceCols
  | _, _, _, _, .ProvSum _ _ _ q => q.sourceCols
  | _, _, _, _, .Retag _ q => q.sourceCols
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.sourceCols
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.sourceCols
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.sourceCols

end Fences

/-! ## The values an evaluation builds -/

section Builds

/-- **The values the operators of a query build while it is evaluated**:
the columns an operator adds to its output rows, and what its
subqueries build – once per row of an apply's left side, once per round
of a recursion. -/
noncomputable def AggQueryIn.Builds : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c n κ l → AnnotatedDatabase T K → (Fin c → T) →
    EvalEnv T K → AggTok T K → Prop
  | _, _, _, _, .Rel _ _, _, _, _, _ => False
  | _, _, _, _, .Hole _ _ _, _, _, _, _ => False
  | _, _, _, _, .Param _ _, _, _, _, _ => False
  | _, _, _, _, .Empty, _, _, _, _ => False
  | _, _, _, _, .Proj _ q, d, γ, E, x => q.Builds d γ E x
  | _, _, _, _, .Sel _ q _, d, γ, E, x => q.Builds d γ E x
  | _, _, _, _, .Prod q₁ q₂, d, γ, E, x => q₁.Builds d γ E x ∨ q₂.Builds d γ E x
  | _, _, _, _, .Apply q₁ q₂, d, γ, E, x => q₁.Builds d γ E x ∨
      ∃ r ∈ q₁.evaluate d γ E, q₂.Builds d (Fin.append (GenRow.plainTuple r.fst) γ)
        (E.withCtx (Fin.append r.fst (E.ctxAt _ γ))) x
  | _, _, _, _, .Sum q₁ q₂, d, γ, E, x => q₁.Builds d γ E x ∨ q₂.Builds d γ E x
  | _, _, _, _, .Dedup q, d, γ, E, x => q.Builds d γ E x
  | _, _, _, _, .Diff q₁ q₂, d, γ, E, x => q₁.Builds d γ E x ∨ q₂.Builds d γ E x
  | _, _, _, _, .Explode _ _ q, d, γ, E, x => q.Builds d γ E x
  | _, _, _, _, .Mu s q₀ q₁, d, γ, E, x => q₀.Builds d γ E x ∨
      ∃ k, q₁.Builds d γ (E.assignHole s ((AggQueryIn.muStep s q₁ d γ E)^[k]
        (q₀.evaluate d γ E))) x
  | _, _, _, _, .MuSet s q₀ q₁, d, γ, E, x => q₀.Builds d γ E x ∨
      ∃ k, q₁.Builds d γ (E.assignHole s
        ((muIter (AggQueryIn.muSetStep s q₀ q₁ d γ E) k).map GenRow.ofAnnotated)) x
  | _, _, _, _, @AggQueryIn.Gamma _ _ _ _ n₂ lab rd is ts fs q keep ord, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E,
        ∃ j : Fin n₂, r.fst (Fin.natAdd _ j) = Sum.inr x) ∨ q.Builds d γ E x
  | _, _, _, _, @AggQueryIn.GammaScalar _ _ _ n₂ lab rd ts fs q ord, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E,
        ∃ j : Fin n₂, r.fst j = Sum.inr x) ∨ q.Builds d γ E x
  | _, _, _, _, @AggQueryIn.GammaNest _ _ _ _ _ lab rd is his p f q, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).evaluate d γ E,
        r.fst (Fin.natAdd _ 0) = Sum.inr x) ∨ q.Builds d γ E x
  | _, _, _, _, .ProvSum _ _ _ q, d, γ, E, x => q.Builds d γ E x
  | _, _, _, _, .Retag _ q, d, γ, E, x => q.Builds d γ E x
  | _, _, _, _, @AggQueryIn.GammaTok _ _ _ _ n₂ _ lab rd is his ts fs a q keep, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E,
        ∃ j : Fin n₂, r.fst (Fin.castAdd 1 (Fin.natAdd _ j)) = Sum.inr x) ∨ q.Builds d γ E x
  | _, _, _, _, @AggQueryIn.Win _ _ _ _ _ _ lab rd P O o w t f q hrr dist keep, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q hrr dist keep).evaluate d γ E,
        r.fst (Fin.last _) = Sum.inr x) ∨ q.Builds d γ E x
  | _, _, _, _, @AggQueryIn.WinExpr _ _ _ _ _ _ lab rd P O o ws ts fs g q keeps, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q keeps).evaluate d γ E,
        r.fst (Fin.last _) = Sum.inr x) ∨ q.Builds d γ E x

end Builds

/-! ## Values derived by terms -/

/-- **The values derived from `S` by terms**: `S` and every term over
one of them. -/
inductive TermCl {K₀ : Type} [ValueType T] (S : AggTok T K₀ → Prop) : AggTok T K₀ → Prop
  | base {x} : S x → TermCl S x
  | step {x} (t : TermIn T 1 0) : TermCl S x → TermCl S (x.postcompTerm t)

/-- **One family identifier, one value.** -/
def FamFun {K₀ : Type} (S : AggTok T K₀ → Prop) : Prop :=
  ∀ x y, S x → S y → x.fam = y.fam → x = y

/-! ## Terms over coherent values -/

section TermCl

/-- The terms a family identifier records. -/
def FamId.terms' : FamId T → List (TermIn T 1 0)
  | .mk _ _ _ _ ts => ts

/-- A family identifier with its terms forgotten. -/
def FamId.root : FamId T → FamId T
  | .mk l k p c _ => .mk l k p c []

omit [ValueType T] in
@[simp] theorem FamId.root_addTerm (t : TermIn T 1 0) (φ : FamId T) :
    (φ.addTerm t).root = φ.root := by cases φ; rfl

omit [ValueType T] in
@[simp] theorem FamId.terms'_addTerm (t : TermIn T 1 0) (φ : FamId T) :
    (φ.addTerm t).terms' = φ.terms' ++ [t] := by cases φ; rfl

omit [ValueType T] in
theorem FamId.eq_of_root_terms' {φ ψ : FamId T} (h₁ : φ.root = ψ.root)
    (h₂ : φ.terms' = ψ.terms') : φ = ψ := by
  cases φ; cases ψ
  simp only [FamId.root, FamId.mk.injEq, and_true] at h₁
  simp only [FamId.terms'] at h₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h₁
  rw [h₂]

/-- Terms applied in order. -/
def AggTok.postcompTerms {K₀ : Type} (x : AggTok T K₀) : List (TermIn T 1 0) → AggTok T K₀
  | [] => x
  | t :: ts => (x.postcompTerm t).postcompTerms ts

theorem AggTok.postcompTerms_append {K₀ : Type} (x : AggTok T K₀) (ts : List (TermIn T 1 0))
    (t : TermIn T 1 0) : x.postcompTerms (ts ++ [t]) = (x.postcompTerms ts).postcompTerm t := by
  induction ts generalizing x with
  | nil => rfl
  | cons s ts ih => exact ih _

omit [DecidableEq K] [HasAltLinearOrder K] [CommSemiringWithMonus K] in
/-- **A value derived by terms is its root's, the terms applied.** -/
theorem TermCl.root {S : AggTok T K → Prop} (hS : ∀ x, S x → x.fam.terms' = []) {x : AggTok T K}
    (hx : TermCl S x) : ∃ x₀, S x₀ ∧ x₀.fam = x.fam.root ∧ x = x₀.postcompTerms x.fam.terms' := by
  induction hx with
  | @base x h =>
    refine ⟨x, h, ?_, ?_⟩
    · have := hS x h
      cases hf : x.fam with
      | mk l k p c ts =>
        rw [hf] at this
        simp only [FamId.terms'] at this
        subst this
        rfl
    · rw [hS x h]; rfl
  | @step x t _ ih =>
    obtain ⟨x₀, h₀, hr, he⟩ := ih
    refine ⟨x₀, h₀, ?_, ?_⟩
    · rw [hr, AggTok.postcompTerm, AggTok.fam_setFam, FamId.root_addTerm]
    · rw [AggTok.postcompTerm, AggTok.fam_setFam, FamId.terms'_addTerm,
        AggTok.postcompTerms_append, ← he]
      rfl
omit [DecidableEq K] [HasAltLinearOrder K] [CommSemiringWithMonus K] in
omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **Terms keep one identifier to one value**, over values recording
no term. -/
theorem FamFun.termCl {S : AggTok T K → Prop} (hS : ∀ x, S x → x.fam.terms' = [])
    (hF : FamFun S) : FamFun (TermCl S) := by
  intro x y hx hy hxy
  obtain ⟨x₀, hx₀, hrx, hex⟩ := hx.root hS
  obtain ⟨y₀, hy₀, hry, hey⟩ := hy.root hS
  have h₀ : x₀ = y₀ := hF x₀ y₀ hx₀ hy₀ (by rw [hrx, hry, hxy])
  rw [hex, hey, h₀, hxy]

end TermCl

/-! ## What is built: the operator's label, no term -/

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem AggTok.stamp_spec {x y : AggTok T K} {lab : ℕ} {key : List T}
    {ps : List (T ⊕ FamId T)} {j : ℕ} (h : x = y.setFam (.mk lab key ps j [])) :
    x.fam.terms' = [] ∧ x.lab = lab := by
  subst h
  simp [AggTok.lab, AggTok.fam_setFam, FamId.lab, FamId.terms']

/-- **A built value records no term and carries a label of the query.** -/
theorem AggQueryIn.builds_spec :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (x : AggTok T K),
      q.Builds d γ E x → x.fam.terms' = [] ∧ x.lab ∈ q.labels := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intro d γ E x h; exact h.elim
  | Hole _ _ _ => intro d γ E x h; exact h.elim
  | Param _ _ => intro d γ E x h; exact h.elim
  | Empty => intro d γ E x h; exact h.elim
  | Proj ps q ih => intro d γ E x h; exact ih d γ E x h
  | Sel φ q hφ ih => intro d γ E x h; exact ih d γ E x h
  | Dedup q ih => intro d γ E x h; exact ih d γ E x h
  | Explode k hk q ih => intro d γ E x h; exact ih d γ E x h
  | Retag hκ q ih => intro d γ E x h; exact ih d γ E x h
  | ProvSum is his t q ih => intro d γ E x h; exact ih d γ E x h
  | Prod q₁ q₂ ih₁ ih₂ | Sum q₁ q₂ ih₁ ih₂ | Diff q₁ q₂ ih₁ ih₂ =>
    intro d γ E x h
    rcases h with h | h
    · exact (ih₁ d γ E x h).imp_right (List.mem_append_left _)
    · exact (ih₂ d γ E x h).imp_right (List.mem_append_right _)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d γ E x h
    rcases h with h | ⟨r, -, h⟩
    · exact (ih₁ d γ E x h).imp_right (List.mem_append_left _)
    · exact (ih₂ _ _ _ x h).imp_right (List.mem_append_right _)
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d γ E x h
    rcases h with h | ⟨k, h⟩
    · exact (ih₀ d γ E x h).imp_right (List.mem_append_left _)
    · exact (ih₁ _ _ _ x h).imp_right (List.mem_append_right _)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d γ E x h
    rcases h with h | ⟨k, h⟩
    · exact (ih₀ d γ E x h).imp_right (List.mem_append_left _)
    · exact (ih₁ _ _ _ x h).imp_right (List.mem_append_right _)
  | @Gamma cI mI nI₁ nI₂ lab rd is ts fs q keep ord ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, j, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
      dsimp only at hj
      rw [Fin.append_right] at hj
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      exact ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, j, hj⟩ | h
    · simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr
      subst hr
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      exact ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)
  | @GammaNest cI mI nI₁ κ' lab rd is his p f q ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
      dsimp only at hj
      rw [Fin.append_right] at hj
      have hx := (Sum.inr_injective hj).symm
      subst hx
      exact ⟨rfl, List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)
  | @GammaTok cI mI nI₁ nI₂ κ' lab rd is his ts fs a q keep ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, j, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
      dsimp only at hj
      rw [Fin.append_left, Fin.append_right] at hj
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      exact ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)
  | @Win cI nI mI pI κw lab rd P O o w t f q hrr dist keep ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hr
      simp only [ValueFrame.windowGenRow, Fin.snoc_last] at hj
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      exact ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)
  | @WinExpr cI nI mI pI qI lab rd P O o ws ts fs g q keeps ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
      simp only [Fin.snoc_last] at hj
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      exact ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)

/-! ## Where a row's values come from -/

section RowToks

omit [DecidableEq K] [HasAltLinearOrder K] [CommSemiringWithMonus K] in
theorem TermCl.mono {S S' : AggTok T K → Prop} (h : ∀ x, S x → S' x) {x : AggTok T K}
    (hx : TermCl S x) : TermCl S' x := by
  induction hx with
  | base hs => exact TermCl.base (h _ hs)
  | step t _ ih => exact TermCl.step t ih

omit [DecidableEq K] [HasAltLinearOrder K] [CommSemiringWithMonus K] in
theorem TermCl.idem {S : AggTok T K → Prop} {x : AggTok T K} (hx : TermCl (TermCl S) x) :
    TermCl S x := by
  induction hx with
  | base hs => exact hs
  | step t _ ih => exact TermCl.step t ih

/-- **The values an environment provides** to a query reading the
rounds `l`: its context's, and those of the rounds bound to the names in
`l`. -/
def EvalEnv.Toks {c : ℕ} (E : EvalEnv T K) (γ : Fin c → T) (l : List (String × ℕ))
    (x : AggTok T K) : Prop :=
  (∃ k, E.ctxAt c γ k = Sum.inr x)
    ∨ ∃ p ∈ l, ∃ r ∈ E.holes p.1 p.2, ∃ k, r.fst k = Sum.inr x

theorem mem_iterate_of_mem_muSum {α : Type} (step : Multiset α → Multiset α) :
    ∀ (b : ℕ) (M : Multiset α) {a : α}, a ∈ muSum step b M → ∃ k, a ∈ step^[k] M
  | 0, M, a, h => ⟨0, h⟩
  | b + 1, M, a, h => by
    rcases Multiset.mem_add.mp h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := mem_iterate_of_mem_muSum step b (step M) h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
omit [DecidableEq K] [HasAltLinearOrder K] in
omit [DecidableEq K] in
/-- An alternative of a row holds an aggregate value only where the row
does. -/
theorem GenRow.inr_of_mem_alternativesAt' [DecidableEq K] {n : ℕ}
    {r a : GenRow T K n} {k : Fin n} (ha : a ∈ r.alternativesAt k) {j : Fin n} {x : AggTok T K}
    (hj : a.fst j = Sum.inr x) : r.fst j = Sum.inr x := by
  unfold GenRow.alternativesAt at ha
  split at ha
  · rw [Multiset.mem_singleton.mp ha] at hj
    exact hj
  · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    by_cases hjk : j = k
    · subst hjk
      simp at hj
    · dsimp only at hj
      erw [Function.update_of_ne hjk] at hj
      exact hj

end RowToks

/-- **Every value a row holds is built by the query or provided by the
environment, up to terms.** -/
theorem AggQueryIn.rowToks :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.sourceCols → ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K),
      ∀ r ∈ q.evaluate d γ E, ∀ k x, r.fst k = Sum.inr x →
        TermCl (fun y => q.Builds d γ E y ∨ E.Toks γ l y) x := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    split at hr
    · exact absurd hr (Multiset.notMem_zero _)
    · obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      exact absurd hk (by simp [GenRow.ofAnnotated])
  | Hole n s κ =>
    intro _ d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    exact TermCl.base (Or.inr (Or.inr ⟨(s, n), List.mem_singleton_self _, r,
      (Multiset.mem_filter.mp hr).1, k, hk⟩))
  | Param pv ρ =>
    intro _ d γ E r hr k x hk
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows] at hr
    split_ifs at hr
    · rw [Multiset.mem_singleton] at hr
      subst hr
      dsimp only at hk
      cases hp : pv k with
      | inl a => rw [hp] at hk; exact absurd hk (by simp)
      | inr j => rw [hp] at hk; exact TermCl.base (Or.inr (Or.inl ⟨j, hk⟩))
    · exact absurd hr (Multiset.notMem_zero _)
  | Empty => intro _ d γ E r hr; exact absurd hr (Multiset.notMem_zero _)
  | Proj ps q ih =>
    intro hsc d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
    dsimp only at hk
    have hih := ih hsc.2 d γ E r₀ hr₀
    have hcol := hsc.1 k
    revert hk hcol
    cases ps k with
    | term t => intro hk; exact absurd hk (by simp [ProjColIn.eval])
    | provTerm t => intro hk; exact absurd hk (by simp [ProjColIn.eval])
    | token k' hk' => intro hk _; exact (hih k' x hk).mono (fun z hz => hz)
    | aggTerm k' hk' gf => intro _ hcol; exact absurd hcol (by simp [ProjColIn.sourceCol])
    | aggTermOf k' hk' t =>
      intro hk _
      simp only [ProjColIn.eval] at hk
      cases hr₀k : r₀.fst k' with
      | inl v => rw [hr₀k] at hk; exact absurd hk (by simp)
      | inr y =>
        rw [hr₀k] at hk
        simp only [Sum.map_inr, Sum.inr.injEq] at hk
        subst hk
        exact (TermCl.step t (hih k' y hr₀k)).mono (fun z hz => hz)
  | Sel φ q hφ ih =>
    intro hsc d γ E r hr k x hk
    dsimp only [AggQueryIn.evaluate] at hr
    by_cases hagg : φ.hasAggAtom
    · rw [ite_eq_left hagg] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      exact ih hsc d γ E r₀ hr₀ k x hk
    · rw [ite_eq_right hagg] at hr
      exact ih hsc d γ E r (Multiset.mem_filter.mp hr).1 k x hk
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hsc d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨⟨y₁, y₂⟩, hy, rfl⟩ := Multiset.mem_map.mp hr
    obtain ⟨hy₁, hy₂⟩ := Multiset.mem_product.mp hy
    dsimp only at hk
    revert hk
    refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
    · rw [Fin.append_left] at hk
      exact (ih₁ hsc.1 d γ E y₁ hy₁ i x hk).mono (fun z hz => hz.imp Or.inl (fun h => h.imp id
        (fun ⟨p, hp, h⟩ => ⟨p, List.mem_append_left _ hp, h⟩)))
    · rw [Fin.append_right] at hk
      exact (ih₂ hsc.2 d γ E y₂ hy₂ j x hk).mono (fun z hz => hz.imp Or.inr (fun h => h.imp id
        (fun ⟨p, hp, h⟩ => ⟨p, List.mem_append_right _ hp, h⟩)))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hsc d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · exact (ih₁ hsc.1 d γ E r hr k x hk).mono (fun z hz => hz.imp Or.inl (fun h => h.imp id
        (fun ⟨p, hp, h⟩ => ⟨p, List.mem_append_left _ hp, h⟩)))
    · exact (ih₂ hsc.2 d γ E r hr k x hk).mono (fun z hz => hz.imp Or.inr (fun h => h.imp id
        (fun ⟨p, hp, h⟩ => ⟨p, List.mem_append_right _ hp, h⟩)))
  | Dedup q ih =>
    intro _ d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd hk (by simp [GenRow.ofAnnotated])
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro _ d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd hk (by simp [GenRow.ofAnnotated])
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro _ d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd hk (by simp [GenRow.ofAnnotated])
  | Explode k' hk' q ih =>
    intro hsc d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, ha⟩ := Multiset.mem_bind.mp hr
    exact ih hsc d γ E r₀ hr₀ k x (GenRow.inr_of_mem_alternativesAt' ha hk)
  | Retag hκ q ih =>
    intro hsc d γ E r hr k x hk
    exact ih hsc d γ E r hr k x hk
  | ProvSum is his t q ih =>
    intro _ d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
    dsimp only at hk
    revert hk
    refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
    · rw [Fin.append_left] at hk; exact absurd hk (by simp)
    · rw [Fin.append_right] at hk; exact absurd hk (by simp)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hsc d γ E r hr k x hk
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨y₁, hy₁, hr'⟩ := Multiset.mem_bind.mp hr
    obtain ⟨y₂, hy₂, rfl⟩ := Multiset.mem_map.mp hr'
    dsimp only at hk
    have h₁ := ih₁ hsc.1 d γ E y₁ hy₁
    revert hk
    refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
    · rw [Fin.append_left] at hk
      exact (h₁ i x hk).mono (fun z hz => hz.imp Or.inl id)
    · rw [Fin.append_right] at hk
      refine TermCl.idem ((ih₂ hsc.2 d _ _ y₂ hy₂ j x hk).mono (fun z hz => ?_))
      rcases hz with hz | hz | ⟨p, hp, -⟩
      · exact TermCl.base (Or.inl (Or.inr ⟨y₁, hy₁, hz⟩))
      · obtain ⟨k', hk'⟩ := hz
        rw [EvalEnv.ctxAt_withCtx] at hk'
        revert hk'
        refine Fin.addCases (fun i hk' => ?_) (fun i hk' => ?_) k'
        · rw [Fin.append_left] at hk'
          exact (h₁ i z hk').mono (fun w hw => hw.imp Or.inl id)
        · rw [Fin.append_right] at hk'
          exact TermCl.base (Or.inr (Or.inl ⟨i, hk'⟩))
      · exact absurd hp List.not_mem_nil
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hsc d γ E r hr k x hk
    have key : ∀ j, ∀ r ∈ (AggQueryIn.muStep s q₁ d γ E)^[j] (q₀.evaluate d γ E), ∀ k x,
        r.fst k = Sum.inr x →
          TermCl (fun y => (AggQueryIn.Mu s q₀ q₁).Builds d γ E y ∨ E.Toks γ [] y) x := by
      intro j
      induction j with
      | zero =>
        intro r hj k x hk
        exact (ih₀ hsc.1 d γ E r hj k x hk).mono (fun z hz => hz.imp Or.inl id)
      | succ j ihj =>
        intro r hj k x hk
        rw [Function.iterate_succ_apply'] at hj
        refine TermCl.idem ((ih₁ hsc.2 d γ _ r hj k x hk).mono (fun z hz => ?_))
        rcases hz with hz | hz | ⟨p, hp, r', hr', k', hk'⟩
        · exact TermCl.base (Or.inl (Or.inr ⟨j, hz⟩))
        · obtain ⟨k', hk'⟩ := hz
          rw [EvalEnv.ctxAt_assignHole] at hk'
          exact TermCl.base (Or.inr (Or.inl ⟨k', hk'⟩))
        · obtain rfl := List.mem_singleton.mp hp
          simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr'
          exact ihj r' hr' k' z hk'
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨j, hj⟩ := mem_iterate_of_mem_muSum _ _ _ hr
    exact key j r hj k x hk
  | @Gamma cI mI nI₁ nI₂ lab rd is ts fs q keep ord ih =>
    intro _ d γ E r hr k x hk
    have hr₀ := hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    dsimp only at hk
    revert hk
    refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
    · rw [Fin.append_left] at hk; exact absurd hk (by simp)
    · exact TermCl.base (Or.inl (Or.inl ⟨_, hr₀, j, hk⟩))
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro _ d γ E r hr k x hk
    exact TermCl.base (Or.inl (Or.inl ⟨r, hr, k, hk⟩))
  | @GammaNest cI mI nI₁ κ' lab rd is his p f q ih =>
    intro _ d γ E r hr k x hk
    have hr₀ := hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
    dsimp only at hk
    revert hk
    refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
    · rw [Fin.append_left] at hk; exact absurd hk (by simp)
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      exact TermCl.base (Or.inl (Or.inl ⟨_, hr₀, hk⟩))
  | @GammaTok cI mI nI₁ nI₂ κ' lab rd is his ts fs a q keep ih =>
    intro _ d γ E r hr k x hk
    have hr₀ := hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    dsimp only at hk
    revert hk
    refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
    · revert hk
      refine Fin.addCases (fun i' hk => ?_) (fun j' hk => ?_) i
      · rw [Fin.append_left, Fin.append_left] at hk; exact absurd hk (by simp)
      · exact TermCl.base (Or.inl (Or.inl ⟨_, hr₀, j', hk⟩))
    · rw [Fin.append_right] at hk; exact absurd hk (by simp)
  | @Win cI nI mI pI κw lab rd P O o w t f q hrr dist keep ih =>
    intro hsc d γ E r hr k x hk
    have hr₀ := hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hr
    revert hk
    refine Fin.lastCases (fun hk => ?_) (fun i hk => ?_) k
    · exact TermCl.base (Or.inl (Or.inl ⟨_, hr₀, hk⟩))
    · simp only [ValueFrame.windowGenRow, Fin.snoc_castSucc] at hk
      exact (ih hsc d γ E y hy i x hk).mono (fun z hz => hz.imp Or.inr id)
  | @WinExpr cI nI mI pI qI lab rd P O o ws ts fs g q keeps ih =>
    intro _ d γ E r hr k x hk
    have hr₀ := hr
    simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
    revert hk
    refine Fin.lastCases (fun hk => ?_) (fun i' hk => ?_) k
    · exact TermCl.base (Or.inl (Or.inl ⟨_, hr₀, hk⟩))
    · simp only [Fin.snoc_castSucc] at hk; exact absurd hk (by simp)

/-! ## Equal parameters, equal inputs -/

section Params

omit [ValueType T] in
theorem filterMap_mask_agree {ι α : Type} (r : ι → Bool) (f g : ι → α) :
    ∀ l : List ι, l.filterMap (fun k => if r k then some (f k) else none)
        = l.filterMap (fun k => if r k then some (g k) else none) →
      ∀ k ∈ l, r k = true → f k = g k
  | [], _, k, hk, _ => absurd hk List.not_mem_nil
  | a :: l, h, k, hk, hr => by
    simp only [List.filterMap_cons] at h
    by_cases ha : r a = true
    · simp only [ha, ite_true, List.cons.injEq] at h
      rcases List.mem_cons.mp hk with rfl | hk
      · exact h.1
      · exact filterMap_mask_agree r f g l h.2 k hk hr
    · simp only [ha, Bool.false_eq_true, ite_false] at h
      rcases List.mem_cons.mp hk with rfl | hk
      · exact absurd hr ha
      · exact filterMap_mask_agree r f g l h k hk hr

omit [ValueType T] in
/-- **Equal recorded parameters agree at every recorded position.** -/
theorem ctxKey_agree {c : ℕ} {α : Type} (r : Fin c → Bool) {f g : Fin c → α}
    (h : ctxKey r f = ctxKey r g) : AgreeOn r f g :=
  fun k hk => filterMap_mask_agree r f g _ h k (List.mem_finRange k) hk

omit [ValueType T] in
theorem mem_ctxKey {c : ℕ} {α : Type} (r : Fin c → Bool) (f : Fin c → α) {k : Fin c}
    (hk : r k = true) : f k ∈ ctxKey r f := by
  unfold ctxKey
  exact List.mem_filterMap.mpr ⟨k, List.mem_finRange k, by simp [hk]⟩

omit [ValueType T] in
/-- **A parameter's identifier is smaller than the identifier recording
it.** -/
theorem FamId.sizeOf_param_lt {lab : ℕ} {key : List T} {ps : List (T ⊕ FamId T)} {col : ℕ}
    {ts : List (TermIn T 1 0)} {φ : FamId T} (h : Sum.inr φ ∈ ps) :
    sizeOf φ < sizeOf (FamId.mk lab key ps col ts) := by
  have h₁ : sizeOf (Sum.inr φ : T ⊕ FamId T) < sizeOf ps := List.sizeOf_lt_of_mem h
  have h₂ : sizeOf φ < sizeOf (Sum.inr φ : T ⊕ FamId T) := by simp
  simp only [FamId.mk.sizeOf_spec]
  omega

end Params
