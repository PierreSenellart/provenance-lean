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

/-- Frames containing the current row everywhere contain it in the
multi-frame windows. -/
theorem AggQueryIn.framesContainSelf_of_all :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.allFramesContainSelf → q.framesContainSelf := by
  intro c n κ l q
  induction q with
  | Rel _ _ | Hole _ _ _ | Param _ _ | Empty => intro _; trivial
  | Proj _ _ ih | Sel _ _ _ ih | Dedup _ ih | Explode _ _ _ ih | Retag _ _ ih
    | ProvSum _ _ _ _ ih | Gamma _ _ _ _ _ _ ih | GammaScalar _ _ _ _ ih
    | GammaNest _ _ _ _ _ ih | GammaTok _ _ _ _ _ _ _ ih => exact ih
  | Prod _ _ ih₁ ih₂ | Apply _ _ ih₁ ih₂ | Sum _ _ ih₁ ih₂ | Diff _ _ ih₁ ih₂
    | Mu _ _ _ ih₁ ih₂ | MuSet _ _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Win _ _ _ _ _ _ _ _ _ _ ih => exact fun h => ih h.2
  | WinExpr _ _ _ _ _ _ _ _ _ ih => exact fun h => ⟨h.1, ih h.2⟩

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
  | _, _, _, _, @AggQueryIn.Win _ _ _ _ _ _ lab rd P O o w hs t f q hrr dist keep, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.Win (hsql := hs) (lab := lab) (rd := rd) P O o w t f q hrr dist
        keep).evaluate d γ E,
        r.fst (Fin.last _) = Sum.inr x) ∨ q.Builds d γ E x
  | _, _, _, _, @AggQueryIn.WinExpr _ _ _ _ _ _ lab rd P O o ws hs ts fs g q keeps, d, γ, E, x =>
      (∃ r ∈ (AggQueryIn.WinExpr (hsql := hs) (lab := lab) (rd := rd) P O o ws ts fs g q
        keeps).evaluate d γ E,
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
    {ps : List (T ⊕ FamId T)} {j : ℕ} {ids : Option (List (OccId T))}
    (h : x = y.setFam (.mk lab key ps j []) ids) :
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
      refine ⟨h1, ?_⟩
      rw [AggQueryIn.labels, labCons_of_ne (Fin.pos j).ne', h2]
      exact List.mem_cons_self
    · exact (ih d γ E x h).imp_right
        (fun h => by rw [AggQueryIn.labels]; exact mem_labCons_of_mem h)
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, j, hj⟩ | h
    · simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr
      subst hr
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      refine ⟨h1, ?_⟩
      rw [AggQueryIn.labels, labCons_of_ne (Fin.pos j).ne', h2]
      exact List.mem_cons_self
    · exact (ih d γ E x h).imp_right
        (fun h => by rw [AggQueryIn.labels]; exact mem_labCons_of_mem h)
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
      refine ⟨h1, ?_⟩
      rw [AggQueryIn.labels, labCons_of_ne (Fin.pos j).ne', h2]
      exact List.mem_cons_self
    · exact (ih d γ E x h).imp_right
        (fun h => by rw [AggQueryIn.labels]; exact mem_labCons_of_mem h)
  | @Win cI nI mI pI κw lab rd P O o w _ t f q hrr dist keep ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hr
      simp only [ValueFrame.windowGenRow, Fin.snoc_last] at hj
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      exact ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)
  | @WinExpr cI nI mI pI qI lab rd P O o ws _ ts fs g q keeps ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
      simp only [Fin.snoc_last] at hj
      obtain ⟨h1, h2⟩ := AggTok.stamp_spec (Sum.inr_injective hj).symm
      exact ⟨h1, by rw [h2]; exact List.mem_cons_self⟩
    · exact (ih d γ E x h).imp_right (List.mem_cons_of_mem _)

/-! ## The width of each operator -/

section Widths

/-- The column a family identifier records. -/
def FamId.col : FamId T → ℕ
  | .mk _ _ _ c _ => c

/-- **Each operator's label with the number of columns it builds.** -/
def AggQueryIn.labWidths : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → List (ℕ × ℕ)
  | _, _, _, _, .Rel _ _ => []
  | _, _, _, _, .Hole _ _ _ => []
  | _, _, _, _, .Param _ _ => []
  | _, _, _, _, .Empty => []
  | _, _, _, _, .Proj _ q => q.labWidths
  | _, _, _, _, .Sel _ q _ => q.labWidths
  | _, _, _, _, .Prod q₁ q₂ => q₁.labWidths ++ q₂.labWidths
  | _, _, _, _, .Apply q₁ q₂ => q₁.labWidths ++ q₂.labWidths
  | _, _, _, _, .Sum q₁ q₂ => q₁.labWidths ++ q₂.labWidths
  | _, _, _, _, .Dedup q => q.labWidths
  | _, _, _, _, .Diff q₁ q₂ => q₁.labWidths ++ q₂.labWidths
  | _, _, _, _, .Explode _ _ q => q.labWidths
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.labWidths ++ q₁.labWidths
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.labWidths ++ q₁.labWidths
  | _, _, _, _, @AggQueryIn.Gamma _ _ _ _ n₂ lab _ _ _ _ q _ _ => labCons n₂ (lab, n₂) q.labWidths
  | _, _, _, _, @AggQueryIn.GammaScalar _ _ _ n₂ lab _ _ _ q _ => labCons n₂ (lab, n₂) q.labWidths
  | _, _, _, _, @AggQueryIn.GammaNest _ _ _ _ _ lab _ _ _ _ _ q => (lab, 1) :: q.labWidths
  | _, _, _, _, .ProvSum _ _ _ q => q.labWidths
  | _, _, _, _, .Retag _ q => q.labWidths
  | _, _, _, _, @AggQueryIn.GammaTok _ _ _ _ n₂ _ lab _ _ _ _ _ _ q _ => labCons n₂ (lab,
      n₂) q.labWidths
  | _, _, _, _, @AggQueryIn.Win _ _ _ _ _ _ lab _ _ _ _ _ _ _ _ q _ _ _ => (lab, 1) :: q.labWidths
  | _, _, _, _, @AggQueryIn.WinExpr _ _ _ _ _ _ lab _ _ _ _ _ _ _ _ _ q _ =>
      (lab, 1) :: q.labWidths

omit [ValueType T] in
theorem AggQueryIn.labels_eq_map_labWidths :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.labels = q.labWidths.map Prod.fst := by
  intro c n κ l q
  induction q with
  | Rel _ _ | Hole _ _ _ | Param _ _ | Empty => rfl
  | Proj _ _ ih | Sel _ _ _ ih | Dedup _ ih | Explode _ _ _ ih | Retag _ _ ih
    | ProvSum _ _ _ _ ih => exact ih
  | Prod _ _ ih₁ ih₂ | Apply _ _ ih₁ ih₂ | Sum _ _ ih₁ ih₂ | Diff _ _ ih₁ ih₂
    | Mu _ _ _ ih₁ ih₂ | MuSet _ _ _ ih₁ ih₂ =>
    simp only [AggQueryIn.labels, AggQueryIn.labWidths, List.map_append, ih₁, ih₂]
  | Gamma _ _ _ _ _ _ ih | GammaScalar _ _ _ _ ih | GammaTok _ _ _ _ _ _ _ ih =>
    simp only [AggQueryIn.labels, AggQueryIn.labWidths, labCons, ih]
    split <;> simp
  | GammaNest _ _ _ _ _ ih | Win _ _ _ _ _ _ _ _ _ _ ih | WinExpr _ _ _ _ _ _ _ _ _ ih =>
    simp only [AggQueryIn.labels, AggQueryIn.labWidths, List.map_cons, ih]

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem AggTok.stamp_col {x y : AggTok T K} {lab : ℕ} {key : List T}
    {ps : List (T ⊕ FamId T)} {j : ℕ} {ids : Option (List (OccId T))}
    (h : x = y.setFam (.mk lab key ps j []) ids) :
    x.fam.col = j := by
  subst h
  simp [AggTok.fam_setFam, FamId.col]

/-- **A built value's column is one its operator builds.** -/
theorem AggQueryIn.builds_col :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (x : AggTok T K),
      q.Builds d γ E x → ∃ w, (x.lab, w) ∈ q.labWidths ∧ x.fam.col < w := by
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
    · obtain ⟨w, hw, hc⟩ := ih₁ d γ E x h; exact ⟨w, List.mem_append_left _ hw, hc⟩
    · obtain ⟨w, hw, hc⟩ := ih₂ d γ E x h; exact ⟨w, List.mem_append_right _ hw, hc⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d γ E x h
    rcases h with h | ⟨r, -, h⟩
    · obtain ⟨w, hw, hc⟩ := ih₁ d γ E x h; exact ⟨w, List.mem_append_left _ hw, hc⟩
    · obtain ⟨w, hw, hc⟩ := ih₂ _ _ _ x h; exact ⟨w, List.mem_append_right _ hw, hc⟩
  | Mu s q₀ q₁ ih₀ ih₁ | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d γ E x h
    rcases h with h | ⟨k, h⟩
    · obtain ⟨w, hw, hc⟩ := ih₀ d γ E x h; exact ⟨w, List.mem_append_left _ hw, hc⟩
    · obtain ⟨w, hw, hc⟩ := ih₁ _ _ _ x h; exact ⟨w, List.mem_append_right _ hw, hc⟩
  | @Gamma cI mI nI₁ nI₂ lab rd is ts fs q keep ord ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, j, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
      dsimp only at hj
      rw [Fin.append_right] at hj
      have he := (Sum.inr_injective hj).symm
      refine ⟨nI₂, ?_, by rw [AggTok.stamp_col he]; exact j.isLt⟩
      rw [AggQueryIn.labWidths, labCons_of_ne (Fin.pos j).ne', (AggTok.stamp_spec he).2]
      exact List.mem_cons_self
    · obtain ⟨w, hw, hc⟩ := ih d γ E x h; exact ⟨w,
        by rw [AggQueryIn.labWidths]; exact mem_labCons_of_mem hw, hc⟩
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, j, hj⟩ | h
    · simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr
      subst hr
      have he := (Sum.inr_injective hj).symm
      refine ⟨nI₂, ?_, by rw [AggTok.stamp_col he]; exact j.isLt⟩
      rw [AggQueryIn.labWidths, labCons_of_ne (Fin.pos j).ne', (AggTok.stamp_spec he).2]
      exact List.mem_cons_self
    · obtain ⟨w, hw, hc⟩ := ih d γ E x h; exact ⟨w,
        by rw [AggQueryIn.labWidths]; exact mem_labCons_of_mem hw, hc⟩
  | @GammaNest cI mI nI₁ κ' lab rd is his p f q ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
      dsimp only at hj
      rw [Fin.append_right] at hj
      have hx := (Sum.inr_injective hj).symm
      subst hx
      exact ⟨1, List.mem_cons_self, by simp [AggTok.fam, FamId.col]⟩
    · obtain ⟨w, hw, hc⟩ := ih d γ E x h; exact ⟨w, List.mem_cons_of_mem _ hw, hc⟩
  | @GammaTok cI mI nI₁ nI₂ κ' lab rd is his ts fs a q keep ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, j, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
      dsimp only at hj
      rw [Fin.append_left, Fin.append_right] at hj
      have he := (Sum.inr_injective hj).symm
      refine ⟨nI₂, ?_, by rw [AggTok.stamp_col he]; exact j.isLt⟩
      rw [AggQueryIn.labWidths, labCons_of_ne (Fin.pos j).ne', (AggTok.stamp_spec he).2]
      exact List.mem_cons_self
    · obtain ⟨w, hw, hc⟩ := ih d γ E x h; exact ⟨w,
        by rw [AggQueryIn.labWidths]; exact mem_labCons_of_mem hw, hc⟩
  | @Win cI nI mI pI κw lab rd P O o w _ t f q hrr dist keep ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate] at hr
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hr
      simp only [ValueFrame.windowGenRow, Fin.snoc_last] at hj
      have he := (Sum.inr_injective hj).symm
      refine ⟨1, ?_, by rw [AggTok.stamp_col he]; exact Nat.zero_lt_one⟩
      rw [(AggTok.stamp_spec he).2]; exact List.mem_cons_self
    · obtain ⟨w, hw, hc⟩ := ih d γ E x h; exact ⟨w, List.mem_cons_of_mem _ hw, hc⟩
  | @WinExpr cI nI mI pI qI lab rd P O o ws _ ts fs g q keeps ih =>
    intro d γ E x h
    rcases h with ⟨r, hr, hj⟩ | h
    · simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
      simp only [Fin.snoc_last] at hj
      have he := (Sum.inr_injective hj).symm
      refine ⟨1, ?_, by rw [AggTok.stamp_col he]; exact Nat.zero_lt_one⟩
      rw [(AggTok.stamp_spec he).2]; exact List.mem_cons_self
    · obtain ⟨w, hw, hc⟩ := ih d γ E x h; exact ⟨w, List.mem_cons_of_mem _ hw, hc⟩

end Widths

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
  | @Win cI nI mI pI κw lab rd P O o w _ t f q hrr dist keep ih =>
    intro hsc d γ E r hr k x hk
    have hr₀ := hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hr
    revert hk
    refine Fin.lastCases (fun hk => ?_) (fun i hk => ?_) k
    · exact TermCl.base (Or.inl (Or.inl ⟨_, hr₀, hk⟩))
    · simp only [ValueFrame.windowGenRow, Fin.snoc_castSucc] at hk
      exact (ih hsc d γ E y hy i x hk).mono (fun z hz => hz.imp Or.inr id)
  | @WinExpr cI nI mI pI qI lab rd P O o ws _ ts fs g q keeps ih =>
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

/-! ## One evaluation of a window: the value is the tuple's -/

section WindowValue

namespace ValueFrame

omit [DecidableEq K] in
/-- **A window's value over a frame containing its current row is the
tuple's**: two rows of the relation carrying the same tuple read the same
value. -/
theorem tokenOfDist_congr_fst {c n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) {w : ValueFrame T p} (hc : w.ContainsSelf) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (X : AnnotatedRelation T K n)
    {x y : AnnotatedTuple T K n} (hx : Multiset.Mem X x) (hy : Multiset.Mem X y)
    (hxy : x.fst = y.fst)
    (γ : Fin c → T) :
    tokenOfDist P O o w t f dist X x γ = tokenOfDist P O o w t f dist X y γ := by
  have hf : frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X x
      = frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X y := by
    unfold frameListOf
    rw [frameOf_congr_val (α := AnnotatedTuple T K n) Prod.fst P O hc X hx hy hxy]
  unfold tokenOfDist tokenOf
  rw [hf, hxy]

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The identities a window gives the occurrences of a frame depend on the
row only through its tuple, where the frame contains its current row. -/
theorem frameOids_congr_fst {n m p : ℕ} (lab : ℕ) (ck : List (T ⊕ FamId T))
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) {w : ValueFrame T p} (hc : w.ContainsSelf) (X : AnnotatedRelation T K n)
    {x y : AnnotatedTuple T K n} (hx : Multiset.Mem X x) (hy : Multiset.Mem X y)
    (hxy : x.fst = y.fst) :
    frameOids lab ck P O o w X x = frameOids lab ck P O o w X y := by
  have hf : frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X x
      = frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X y := by
    unfold frameListOf
    rw [frameOf_congr_val (α := AnnotatedTuple T K n) Prod.fst P O hc X hx hy hxy]
  unfold frameOids
  rw [hf, hxy]

omit [DecidableEq K] in
theorem exprWhenOf_congr_fst {c n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) {w : ValueFrame T p} (hc : w.ContainsSelf) (t : TermIn T c n)
    (f : SeqAggFunc T) (dist : Bool) (keep : Tuple T n → Bool) (X : AnnotatedRelation T K n)
    {x y : AnnotatedTuple T K n} (hx : Multiset.Mem X x) (hy : Multiset.Mem X y)
    (hxy : x.fst = y.fst)
    (γ : Fin c → T) :
    exprWhenOf P O o w t f dist keep X x γ = exprWhenOf P O o w t f dist keep X y γ := by
  have hf : frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X x
      = frameListOf (α := AnnotatedTuple T K n) Prod.fst P O o w X y := by
    unfold frameListOf
    rw [frameOf_congr_val (α := AnnotatedTuple T K n) Prod.fst P O hc X hx hy hxy]
  unfold exprWhenOf
  rw [hf, hxy]

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **A multi-frame window's expression over frames containing their
current row is the tuple's**: two occurrences carrying the same tuple get
the same expression. -/
theorem exprOfWhen_congr_row {c n m p q : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) {ws : Fin q → ValueFrame T p} (hc : ∀ l, (ws l).ContainsSelf)
    (ts : Fin q → TermIn T c n) (fs : Fin q → SeqAggFunc T) (g : (Fin q → T) → T)
    (keeps : Fin q → Option (Selection T n)) (r : OccFam (AnnotatedTuple T K n))
    {i i' : Fin r.size} (h : (r.row i).fst = (r.row i').fst) (γ : Fin c → T) :
    exprOfWhen P O o ws ts fs g keeps r i γ = exprOfWhen P O o ws ts fs g keeps r i' γ := by
  have hidx : exprIdx (α := AnnotatedTuple T K n) Prod.fst P O o ws r i
      = exprIdx (α := AnnotatedTuple T K n) Prod.fst P O o ws r i' := by
    unfold exprIdx frameSeqOn frameSeq
    rw [frame_eq_of_key_eq (val := fun j : Fin r.size => (r.row j).fst)
      (containsSelf_unionFrame hc) (OccFam.mk r.size id)
      (i := Fin.cast (by simp) i) (i' := Fin.cast (by simp) i')
      (congrArg (Tuple.key P) h) (congrArg (Tuple.key O) h)]
  have hmem : ∀ l j, mem (α := AnnotatedTuple T K n) Prod.fst P O (ws l) r i j
      = mem (α := AnnotatedTuple T K n) Prod.fst P O (ws l) r i' j := by
    intro l j
    rw [mem_of_containsSelf (hc l), mem_of_containsSelf (hc l), h]
  unfold exprOfWhen exprOfValsWhen
  simp only [hidx, hmem, h]

end ValueFrame

end WindowValue

/-! ## One evaluation of an operator: one value per identifier -/

section NodeFun

/-- **A grouping builds one value per identifier**: the identifier records
the group key and the column. -/
theorem AggQueryIn.newFun_Gamma {c m n₁ n₂ lab : ℕ} {rd : Fin c → Bool}
    (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (keep : Fin n₂ → Option (Selection T m))
    (ord : GroupOrder T m) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r r' : GenRow T K (n₁ + n₂)}
    (hr : r ∈ (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E)
    (hr' : r' ∈ (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E)
    {j j' : Fin n₂} {x y : AggTok T K} (hx : r.fst (Fin.natAdd n₁ j) = Sum.inr x)
    (hy : r'.fst (Fin.natAdd n₁ j') = Sum.inr y) (hxy : x.fam = y.fam) : x = y := by
  simp only [AggQueryIn.evaluate] at hr hr'
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨kv', -, rfl⟩ := Multiset.mem_map.mp hr'
  dsimp only at hx hy
  rw [Fin.append_right, Sum.inr.injEq] at hx hy
  subst hx hy
  simp only [AggTok.fam_setFam, FamId.mk.injEq] at hxy
  obtain ⟨-, hg, -, hj, -⟩ := hxy
  have hg' : kv.fst = kv'.fst := List.ofFn_injective hg
  rw [hg']
  simp only [Fin.val_inj] at hj
  rw [hj]

theorem AggQueryIn.newFun_GammaScalar {c m n₂ lab : ℕ} {rd : Fin c → Bool}
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (ord : GroupOrder T m)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r r' : GenRow T K n₂}
    (hr : r ∈ (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E)
    (hr' : r' ∈ (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E)
    {j j' : Fin n₂} {x y : AggTok T K} (hx : r.fst j = Sum.inr x)
    (hy : r'.fst j' = Sum.inr y) (hxy : x.fam = y.fam) : x = y := by
  simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr hr'
  subst hr hr'
  dsimp only at hx hy
  rw [Sum.inr.injEq] at hx hy
  subst hx hy
  simp only [AggTok.fam_setFam, FamId.mk.injEq] at hxy
  obtain ⟨-, -, -, hj, -⟩ := hxy
  simp only [Fin.val_inj] at hj
  rw [hj]

theorem AggQueryIn.newFun_GammaNest {c m n₁ lab : ℕ} {κ : Fin m → ColKind}
    {rd : Fin c → Bool} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (p : ProjColIn T c κ) (f : Multiset T → T) (q : AggQueryIn T c m κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r r' : GenRow T K (n₁ + 1)}
    (hr : r ∈ (AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).evaluate d γ E)
    (hr' : r' ∈ (AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).evaluate d γ E)
    {x y : AggTok T K} (hx : r.fst (Fin.natAdd n₁ 0) = Sum.inr x)
    (hy : r'.fst (Fin.natAdd n₁ 0) = Sum.inr y) (hxy : x.fam.family = y.fam.family) : x = y := by
  simp only [AggQueryIn.evaluate] at hr hr'
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨g', -, rfl⟩ := Multiset.mem_map.mp hr'
  dsimp only at hx hy
  rw [Fin.append_right, Sum.inr.injEq] at hx hy
  subst hx hy
  simp only [AggTok.fam, fam_nestOfGroup, FamId.family, Prod.mk.injEq] at hxy
  obtain ⟨-, hg, -⟩ := hxy
  rw [List.ofFn_injective hg]

theorem AggQueryIn.newFun_GammaTok {c m n₁ n₂ lab : ℕ} {κ : Fin m → ColKind}
    {rd : Fin c → Bool} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂) (a : TermGIn T c κ)
    (q : AggQueryIn T c m κ) (keep : Fin n₂ → Option (Selection T m))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r r' : GenRow T K (n₁ + n₂ + 1)}
    (hr : r ∈ (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E)
    (hr' : r' ∈
      (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E)
    {j j' : Fin n₂} {x y : AggTok T K}
    (hx : r.fst (Fin.castAdd 1 (Fin.natAdd n₁ j)) = Sum.inr x)
    (hy : r'.fst (Fin.castAdd 1 (Fin.natAdd n₁ j')) = Sum.inr y) (hxy : x.fam = y.fam) :
    x = y := by
  simp only [AggQueryIn.evaluate] at hr hr'
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨kv', -, rfl⟩ := Multiset.mem_map.mp hr'
  dsimp only at hx hy
  rw [Fin.append_left, Fin.append_right, Sum.inr.injEq] at hx hy
  subst hx hy
  simp only [AggTok.fam_setFam, FamId.mk.injEq] at hxy
  obtain ⟨-, hg, -, hj, -⟩ := hxy
  have hg' : kv.fst = kv'.fst := List.ofFn_injective hg
  rw [hg']
  simp only [Fin.val_inj] at hj
  rw [hj]

/-- **A window over a frame containing its current row builds one value
per identifier**: the identifier records the tuple the window reads, and
the value is that tuple's. -/
theorem AggQueryIn.newFun_Win {c n m p lab : ℕ} {κ : Fin n → ColKind} {rd : Fin c → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) {w : ValueFrame T p} {hsql :
      w.IsSQL o}
    (hc : w.ContainsSelf) (t : TermIn T c n) (f : SeqAggFunc T) (q : AggQueryIn T c n κ)
    (hrr : WinReadsReg κ P O t) (dist : Bool) (keep : Option (Selection T n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r r' : GenRow T K (n + 1)}
    (hr : r ∈ (AggQueryIn.Win (hsql := sql_frame%) (lab := lab) (rd := rd) P O o w t f q hrr dist
      keep).evaluate d γ E)
    (hr' : r' ∈
      (AggQueryIn.Win (hsql := sql_frame%) (lab := lab) (rd := rd) P O o w t f q hrr dist
        keep).evaluate d γ E)
    {x y : AggTok T K} (hx : r.fst (Fin.last _) = Sum.inr x)
    (hy : r'.fst (Fin.last _) = Sum.inr y) (hxy : x.fam.family = y.fam.family) : x = y := by
  simp only [AggQueryIn.evaluate] at hr hr'
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.mp hr'
  simp only [ValueFrame.windowGenRow, Fin.snoc_last, Sum.inr.injEq] at hx hy
  subst hx hy
  simp only [AggTok.fam_setFam, FamId.family, Prod.mk.injEq] at hxy
  obtain ⟨-, hg, -⟩ := hxy
  have hg' : (GenRow.readAnnotated κ u).fst = (GenRow.readAnnotated κ u').fst :=
    List.ofFn_injective hg
  have hm : ∀ v ∈ q.evaluate d γ E, Multiset.Mem
      ((q.evaluate d γ E).map (GenRow.readAnnotated κ) : AnnotatedRelation T K n)
      (GenRow.readAnnotated κ v) := fun v hv => Multiset.mem_map_of_mem _ hv
  cases keep with
  | none =>
    simp only
    rw [ValueFrame.tokenOfDist_congr_fst P O o hc t f dist _ (hm u hu) (hm u' hu') hg' γ, hg',
      ValueFrame.frameOids_congr_fst lab _ P O o hc _ (hm u hu) (hm u' hu') hg']
  | some φ =>
    simp only
    rw [ValueFrame.exprWhenOf_congr_fst P O o hc t f dist φ.keeps _ (hm u hu) (hm u' hu')
      hg' γ, hg', ValueFrame.frameOids_congr_fst lab _ P O o hc _ (hm u hu) (hm u' hu') hg']

/-- **A multi-frame window over frames containing the current row builds
one value per identifier.** -/
theorem AggQueryIn.newFun_WinExpr {c n m p q lab : ℕ} {rd : Fin c → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    {ws : Fin q → ValueFrame T p} {hsql : ∀ l, (ws l).IsSQL o} (hc : ∀ l, (ws l).ContainsSelf)
    (ts : Fin q → TermIn T c n) (fs : Fin q → SeqAggFunc T) (g : (Fin q → T) → T)
    (q₀ : AggQueryIn T c n (ColKind.allReg n)) (keeps : Fin q → Option (Selection T n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r r' : GenRow T K (n + 1)}
    (hr : r ∈ (AggQueryIn.WinExpr (hsql := sql_frame%) (lab := lab) (rd := rd) P O o ws ts fs g q₀
      keeps).evaluate
      d γ E)
    (hr' : r' ∈ (AggQueryIn.WinExpr (hsql := sql_frame%) (lab := lab) (rd := rd) P O o ws ts fs g
      q₀ keeps).evaluate
      d γ E)
    {x y : AggTok T K} (hx : r.fst (Fin.last _) = Sum.inr x)
    (hy : r'.fst (Fin.last _) = Sum.inr y) (hxy : x.fam.family = y.fam.family) : x = y := by
  simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr hr'
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨i', -, rfl⟩ := Multiset.mem_map.mp hr'
  simp only [Fin.snoc_last, Sum.inr.injEq] at hx hy
  subst hx hy
  simp only [AggTok.fam_setFam, FamId.family, Prod.mk.injEq] at hxy
  obtain ⟨-, hg, -⟩ := hxy
  rw [ValueFrame.exprOfWhen_congr_row P O o hc ts fs g keeps _ (List.ofFn_injective hg) γ, hg]

/-- **The columns a grouping builds for one group share a class.** -/
theorem AggQueryIn.newKey_Gamma {c m n₁ n₂ lab : ℕ} {rd : Fin c → Bool}
    (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (keep : Fin n₂ → Option (Selection T m))
    (ord : GroupOrder T m) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r r' : GenRow T K (n₁ + n₂)}
    (hr : r ∈ (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E)
    (hr' : r' ∈ (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E)
    {j j' : Fin n₂} {x y : AggTok T K} (hx : r.fst (Fin.natAdd n₁ j) = Sum.inr x)
    (hy : r'.fst (Fin.natAdd n₁ j') = Sum.inr y) (hxy : x.fam.family = y.fam.family) :
    x.classKey = y.classKey := by
  simp only [AggQueryIn.evaluate] at hr hr'
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨kv', -, rfl⟩ := Multiset.mem_map.mp hr'
  dsimp only at hx hy
  rw [Fin.append_right, Sum.inr.injEq] at hx hy
  subst hx hy
  have hxy' := hxy
  simp only [AggTok.fam_setFam, FamId.family, Prod.mk.injEq] at hxy'
  obtain ⟨-, hg, -⟩ := hxy'
  have hg' : kv.fst = kv'.fst := List.ofFn_injective hg
  rw [hg']
  cases keep j <;> cases keep j' <;>
    simp [AggTok.setFam, AggTok.classKey, AggTok.annList, AggTok.fam, FamId.family,
      AggValue.ofGroup, AggExpr.annList, AggExpr.ofGroupWhen, AggExpr.ofSeqWhen, List.map_map]

theorem AggQueryIn.newKey_GammaScalar {c m n₂ lab : ℕ} {rd : Fin c → Bool}
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (ord : GroupOrder T m)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r r' : GenRow T K n₂}
    (hr : r ∈ (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E)
    (hr' : r' ∈ (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E)
    {j j' : Fin n₂} {x y : AggTok T K} (hx : r.fst j = Sum.inr x)
    (hy : r'.fst j' = Sum.inr y) (hxy : x.fam.family = y.fam.family) :
    x.classKey = y.classKey := by
  simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr hr'
  subst hr hr'
  dsimp only at hx hy
  rw [Sum.inr.injEq] at hx hy
  subst hx hy
  simp only [AggTok.fam_setFam] at hxy
  simp [AggTok.setFam, AggTok.classKey, AggTok.annList, AggTok.fam, AggValue.ofScalarGroup,
    AggValue.ofGroup, hxy]

theorem AggQueryIn.newKey_GammaTok {c m n₁ n₂ lab : ℕ} {κ : Fin m → ColKind}
    {rd : Fin c → Bool} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂) (a : TermGIn T c κ)
    (q : AggQueryIn T c m κ) (keep : Fin n₂ → Option (Selection T m))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r r' : GenRow T K (n₁ + n₂ + 1)}
    (hr : r ∈ (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E)
    (hr' : r' ∈
      (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E)
    {j j' : Fin n₂} {x y : AggTok T K}
    (hx : r.fst (Fin.castAdd 1 (Fin.natAdd n₁ j)) = Sum.inr x)
    (hy : r'.fst (Fin.castAdd 1 (Fin.natAdd n₁ j')) = Sum.inr y)
    (hxy : x.fam.family = y.fam.family) : x.classKey = y.classKey := by
  simp only [AggQueryIn.evaluate] at hr hr'
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  obtain ⟨kv', -, rfl⟩ := Multiset.mem_map.mp hr'
  dsimp only at hx hy
  rw [Fin.append_left, Fin.append_right, Sum.inr.injEq] at hx hy
  subst hx hy
  have hxy' := hxy
  simp only [AggTok.fam_setFam, FamId.family, Prod.mk.injEq] at hxy'
  obtain ⟨-, hg, -⟩ := hxy'
  have hg' : kv.fst = kv'.fst := List.ofFn_injective hg
  rw [hg']
  cases keep j <;> cases keep j' <;>
    simp [AggTok.setFam, AggTok.classKey, AggTok.annList, AggTok.fam, FamId.family,
      AggValue.ofGroup, AggExpr.annList, AggExpr.ofGroupWhen, AggExpr.ofSeqWhen, List.map_map]

end NodeFun

/-! ## Coherent situations -/

section Situation

/-- **A coherent situation**: the plain context is the collapse of the
environment's context, as the evaluator keeps it. -/
def EvalEnv.SitOK {c : ℕ} (E : EvalEnv T K) (γ : Fin c → T) : Prop :=
  ∀ k, γ k = AggValue.collapseSum (E.ctxAt c γ k)

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem EvalEnv.sitOK_empty {c : ℕ} (γ : Fin c → T) : ({} : EvalEnv T K).SitOK γ := by
  intro k
  simp

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem EvalEnv.SitOK.assignHole {c : ℕ} {E : EvalEnv T K} {γ : Fin c → T} (h : E.SitOK γ)
    (s : String) {n : ℕ} (X : Multiset (GenRow T K n)) : (E.assignHole s X).SitOK γ := by
  intro k
  rw [EvalEnv.ctxAt_assignHole]
  exact h k

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem EvalEnv.SitOK.apply {c n₁ : ℕ} {E : EvalEnv T K} {γ : Fin c → T} (h : E.SitOK γ)
    (u : Tuple (GenValue T K) n₁) :
    (E.withCtx (Fin.append u (E.ctxAt _ γ))).SitOK (Fin.append (GenRow.plainTuple u) γ) := by
  intro k
  rw [EvalEnv.ctxAt_withCtx]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left, Fin.append_left]; rfl
  · rw [Fin.append_right, Fin.append_right]; exact h i

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
/-- **Equal recorded parameters, coherent situations: equal readings.**
Where the parameters a family records are equal, the two contexts agree
at every recorded position – an aggregate parameter is recorded by its
identifier, which `hU` turns back into the value – and so do the plain
contexts. -/
theorem EvalEnv.agree_of_paramKey {c : ℕ} (rd : Fin c → Bool) {γ₁ γ₂ : Fin c → T}
    {E₁ E₂ : EvalEnv T K} (U : AggTok T K → Prop) (M : ℕ)
    (hU : ∀ x y, U x → U y → x.fam = y.fam → sizeOf x.fam < M → x = y)
    (hU₁ : ∀ k x, E₁.ctxAt c γ₁ k = Sum.inr x → U x)
    (hU₂ : ∀ k x, E₂.ctxAt c γ₂ k = Sum.inr x → U x)
    (hM : ∀ φ, Sum.inr φ ∈ E₁.paramKey rd γ₁ → sizeOf φ < M)
    (h : E₁.paramKey rd γ₁ = E₂.paramKey rd γ₂) :
    AgreeOn rd (E₁.ctxAt c γ₁) (E₂.ctxAt c γ₂) := by
  have ha := ctxKey_agree rd h
  intro k hk
  have hk' := ha k hk
  dsimp only at hk'
  cases h₁ : E₁.ctxAt c γ₁ k with
  | inl v =>
    cases h₂ : E₂.ctxAt c γ₂ k with
    | inl v' => rw [h₁, h₂] at hk'; simp only [GenValue.paramId, Sum.inl.injEq] at hk'; rw [hk']
    | inr y => rw [h₁, h₂] at hk'; simp [GenValue.paramId] at hk'
  | inr x =>
    cases h₂ : E₂.ctxAt c γ₂ k with
    | inl v' => rw [h₁, h₂] at hk'; simp [GenValue.paramId] at hk'
    | inr y =>
      rw [h₁, h₂] at hk'
      simp only [GenValue.paramId, Sum.inr.injEq] at hk'
      have hm : Sum.inr x.fam ∈ E₁.paramKey rd γ₁ := by
        have := mem_ctxKey rd (fun k => GenValue.paramId (E₁.ctxAt c γ₁ k)) hk
        simp only [h₁, GenValue.paramId] at this
        exact this
      rw [hU x y (hU₁ k x h₁) (hU₂ k y h₂) hk' (hM _ hm)]

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem EvalEnv.SitOK.agree {c : ℕ} {rd : Fin c → Bool} {γ₁ γ₂ : Fin c → T}
    {E₁ E₂ : EvalEnv T K} (h₁ : E₁.SitOK γ₁) (h₂ : E₂.SitOK γ₂)
    (h : AgreeOn rd (E₁.ctxAt c γ₁) (E₂.ctxAt c γ₂)) : AgreeOn rd γ₁ γ₂ := by
  intro k hk
  rw [h₁ k, h₂ k, h k hk]

end Situation

/-! ## The values a situation provides -/

section Provided

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem EvalEnv.Toks.mono {c : ℕ} {E : EvalEnv T K} {γ : Fin c → T}
    {l l' : List (String × ℕ)} (h : l ⊆ l') {x : AggTok T K} (hx : E.Toks γ l x) :
    E.Toks γ l' x :=
  hx.imp id (fun ⟨p, hp, hr⟩ => ⟨p, h hp, hr⟩)

/-- **Every value a round of a bag recursion holds is built by the
recursion or provided by the environment, up to terms.** -/
theorem AggQueryIn.muRoundToks {c n : ℕ} {κ : Fin n → ColKind} (s : String)
    (q₀ : AggQueryIn T c n κ) (q₁ : AggQueryIn T c n κ [(s, n)])
    (hsc : (AggQueryIn.Mu s q₀ q₁).sourceCols) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    ∀ j, ∀ r ∈ (AggQueryIn.muStep s q₁ d γ E)^[j] (q₀.evaluate d γ E), ∀ k x,
      r.fst k = Sum.inr x →
        TermCl (fun y => (AggQueryIn.Mu s q₀ q₁).Builds d γ E y ∨ E.Toks γ [] y) x := by
  intro j
  induction j with
  | zero =>
    intro r hj k x hk
    exact (q₀.rowToks hsc.1 d γ E r hj k x hk).mono (fun z hz => hz.imp Or.inl id)
  | succ j ihj =>
    intro r hj k x hk
    rw [Function.iterate_succ_apply'] at hj
    refine TermCl.idem ((q₁.rowToks hsc.2 d γ _ r hj k x hk).mono (fun z hz => ?_))
    rcases hz with hz | hz | ⟨p, hp, r', hr', k', hk'⟩
    · exact TermCl.base (Or.inl (Or.inr ⟨j, hz⟩))
    · obtain ⟨k', hk'⟩ := hz
      rw [EvalEnv.ctxAt_assignHole] at hk'
      exact TermCl.base (Or.inr (Or.inl ⟨k', hk'⟩))
    · obtain rfl := List.mem_singleton.mp hp
      simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr'
      exact ihj r' hr' k' z hk'

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem AggTok.lab_of_fam {x : AggTok T K} {lab : ℕ} {key : List T}
    {ps : List (T ⊕ FamId T)} {j : ℕ} {ts : List (TermIn T 1 0)}
    (h : x.fam = FamId.mk lab key ps j ts) : x.lab = lab := by
  unfold AggTok.lab
  rw [h]
  rfl

end Provided

/-! ## What an operator stamps -/

section NodeFam

theorem AggQueryIn.newFam_Gamma {c m n₁ n₂ lab : ℕ} {rd : Fin c → Bool}
    (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (keep : Fin n₂ → Option (Selection T m))
    (ord : GroupOrder T m) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r : GenRow T K (n₁ + n₂)}
    (hr : r ∈ (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E)
    {x : AggTok T K} (hx : ∃ j, r.fst (Fin.natAdd n₁ j) = Sum.inr x) :
    ∃ key j, x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  obtain ⟨j, hx⟩ := hx
  simp only [AggQueryIn.evaluate] at hr
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  dsimp only at hx
  rw [Fin.append_right, Sum.inr.injEq] at hx
  subst hx
  exact ⟨_, _, AggTok.fam_setFam _ _⟩

theorem AggQueryIn.newFam_GammaScalar {c m n₂ lab : ℕ} {rd : Fin c → Bool}
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (ord : GroupOrder T m)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r : GenRow T K n₂}
    (hr : r ∈ (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E)
    {x : AggTok T K} (hx : ∃ j, r.fst j = Sum.inr x) :
    ∃ key j, x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  obtain ⟨j, hx⟩ := hx
  simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr
  subst hr
  dsimp only at hx
  rw [Sum.inr.injEq] at hx
  subst hx
  exact ⟨_, _, AggTok.fam_setFam _ _⟩

theorem AggQueryIn.newFam_GammaNest {c m n₁ lab : ℕ} {κ : Fin m → ColKind}
    {rd : Fin c → Bool} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (p : ProjColIn T c κ) (f : Multiset T → T) (q : AggQueryIn T c m κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r : GenRow T K (n₁ + 1)}
    (hr : r ∈ (AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).evaluate d γ E)
    {x : AggTok T K} (hx : r.fst (Fin.natAdd n₁ 0) = Sum.inr x) :
    ∃ key j, x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate] at hr
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
  dsimp only at hx
  rw [Fin.append_right, Sum.inr.injEq] at hx
  subst hx
  exact ⟨_, _, rfl⟩

theorem AggQueryIn.newFam_GammaTok {c m n₁ n₂ lab : ℕ} {κ : Fin m → ColKind}
    {rd : Fin c → Bool} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂) (a : TermGIn T c κ)
    (q : AggQueryIn T c m κ) (keep : Fin n₂ → Option (Selection T m))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r : GenRow T K (n₁ + n₂ + 1)}
    (hr : r ∈ (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E)
    {x : AggTok T K} (hx : ∃ j, r.fst (Fin.castAdd 1 (Fin.natAdd n₁ j)) = Sum.inr x) :
    ∃ key j, x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  obtain ⟨j, hx⟩ := hx
  simp only [AggQueryIn.evaluate] at hr
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  dsimp only at hx
  rw [Fin.append_left, Fin.append_right, Sum.inr.injEq] at hx
  subst hx
  exact ⟨_, _, AggTok.fam_setFam _ _⟩

theorem AggQueryIn.newFam_Win {c n m p lab : ℕ} {κ : Fin n → ColKind} {rd : Fin c → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) {hsql :
      w.IsSQL o}
    (t : TermIn T c n) (f : SeqAggFunc T) (q : AggQueryIn T c n κ)
    (hrr : WinReadsReg κ P O t) (dist : Bool) (keep : Option (Selection T n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r : GenRow T K (n + 1)}
    (hr : r ∈ (AggQueryIn.Win (hsql := sql_frame%) (lab := lab) (rd := rd) P O o w t f q hrr dist
      keep).evaluate d γ E)
    {x : AggTok T K} (hx : r.fst (Fin.last _) = Sum.inr x) :
    ∃ key j, x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate] at hr
  obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hr
  simp only [ValueFrame.windowGenRow, Fin.snoc_last, Sum.inr.injEq] at hx
  subst hx
  exact ⟨_, _, AggTok.fam_setFam _ _⟩

theorem AggQueryIn.newFam_WinExpr {c n m p q lab : ℕ} {rd : Fin c → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin q → ValueFrame T p) {hsql : ∀ l, (ws l).IsSQL o}
    (ts : Fin q → TermIn T c n) (fs : Fin q → SeqAggFunc T) (g : (Fin q → T) → T)
    (q₀ : AggQueryIn T c n (ColKind.allReg n)) (keeps : Fin q → Option (Selection T n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r : GenRow T K (n + 1)}
    (hr : r ∈ (AggQueryIn.WinExpr (hsql := sql_frame%) (lab := lab) (rd := rd) P O o ws ts fs g q₀
      keeps).evaluate
      d γ E)
    {x : AggTok T K} (hx : r.fst (Fin.last _) = Sum.inr x) :
    ∃ key j, x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
  simp only [Fin.snoc_last, Sum.inr.injEq] at hx
  subst hx
  exact ⟨_, _, AggTok.fam_setFam _ _⟩

end NodeFam

/-! ## The rows an operator builds -/

section NodeRow

/-- **A grouping's row**: its key columns hold values, and its aggregate
columns the values of one family, the `j`-th recording column `j`. -/
theorem AggQueryIn.newRow_Gamma {c m n₁ n₂ lab : ℕ} {rd : Fin c → Bool}
    (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (keep : Fin n₂ → Option (Selection T m))
    (ord : GroupOrder T m) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r : GenRow T K (n₁ + n₂)}
    (hr : r ∈ (AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q keep ord).evaluate d γ E) :
    ∃ key, (∀ i, ∃ v, r.fst (Fin.castAdd n₂ i) = Sum.inl v)
      ∧ ∀ j : Fin n₂, ∃ x, r.fst (Fin.natAdd n₁ j) = Sum.inr x
        ∧ x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate] at hr
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  refine ⟨List.ofFn kv.fst, fun i => ⟨kv.fst i, ?_⟩, fun j => ?_⟩
  · dsimp only; rw [Fin.append_left]
  · dsimp only; rw [Fin.append_right]; exact ⟨_, rfl, AggTok.fam_setFam _ _⟩

theorem AggQueryIn.newRow_GammaScalar {c m n₂ lab : ℕ} {rd : Fin c → Bool}
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (q : AggQueryIn T c m (ColKind.allReg m)) (ord : GroupOrder T m)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r : GenRow T K n₂}
    (hr : r ∈ (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q ord).evaluate d γ E) :
    ∃ key, ∀ j : Fin n₂, ∃ x, r.fst j = Sum.inr x
        ∧ x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr
  subst hr
  exact ⟨[], fun j => ⟨_, rfl, AggTok.fam_setFam _ _⟩⟩

theorem AggQueryIn.newRow_GammaNest {c m n₁ lab : ℕ} {κ : Fin m → ColKind}
    {rd : Fin c → Bool} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (p : ProjColIn T c κ) (f : Multiset T → T) (q : AggQueryIn T c m κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r : GenRow T K (n₁ + 1)}
    (hr : r ∈ (AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q).evaluate d γ E) :
    ∃ key, (∀ i, ∃ v, r.fst (Fin.castAdd 1 i) = Sum.inl v)
      ∧ ∀ j : Fin 1, ∃ x, r.fst (Fin.natAdd n₁ j) = Sum.inr x
        ∧ x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate] at hr
  obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
  refine ⟨List.ofFn g, fun i => ⟨g i, ?_⟩, fun j => ?_⟩
  · dsimp only; rw [Fin.append_left]
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    dsimp only; rw [Fin.append_right]; exact ⟨_, rfl, rfl⟩

theorem AggQueryIn.newRow_GammaTok {c m n₁ n₂ lab : ℕ} {κ : Fin m → ColKind}
    {rd : Fin c → Bool} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂) (a : TermGIn T c κ)
    (q : AggQueryIn T c m κ) (keep : Fin n₂ → Option (Selection T m))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    {r : GenRow T K (n₁ + n₂ + 1)}
    (hr : r ∈ (AggQueryIn.GammaTok (lab := lab) (rd := rd) is his ts fs a q keep).evaluate d γ E) :
    ∃ key, (∀ i, ∃ v, r.fst (Fin.castAdd 1 (Fin.castAdd n₂ i)) = Sum.inl v)
      ∧ (∀ i : Fin 1, ∃ v, r.fst (Fin.natAdd (n₁ + n₂) i) = Sum.inl v)
      ∧ ∀ j : Fin n₂, ∃ x, r.fst (Fin.castAdd 1 (Fin.natAdd n₁ j)) = Sum.inr x
        ∧ x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate] at hr
  obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
  refine ⟨List.ofFn kv.fst, fun i => ⟨kv.fst i, ?_⟩, fun i => ?_, fun j => ?_⟩
  · dsimp only; rw [Fin.append_left, Fin.append_left]
  · dsimp only; rw [Fin.append_right]; exact ⟨_, rfl⟩
  · dsimp only; rw [Fin.append_left, Fin.append_right]; exact ⟨_, rfl, AggTok.fam_setFam _ _⟩

theorem AggQueryIn.newRow_WinExpr {c n m p q lab : ℕ} {rd : Fin c → Bool}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin q → ValueFrame T p) {hsql : ∀ l, (ws l).IsSQL o}
    (ts : Fin q → TermIn T c n) (fs : Fin q → SeqAggFunc T) (g : (Fin q → T) → T)
    (q₀ : AggQueryIn T c n (ColKind.allReg n)) (keeps : Fin q → Option (Selection T n))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {r : GenRow T K (n + 1)}
    (hr : r ∈ (AggQueryIn.WinExpr (hsql := sql_frame%) (lab := lab) (rd := rd) P O o ws ts fs g q₀
      keeps).evaluate
      d γ E) :
    ∃ key, (∀ i, ∃ v, r.fst (Fin.castSucc i) = Sum.inl v)
      ∧ ∀ j : Fin 1, ∃ x, r.fst (Fin.last n) = Sum.inr x
        ∧ x.fam = FamId.mk lab key (E.paramKey rd γ) j [] := by
  simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
  refine ⟨List.ofFn ((OccFam.ofSorted (Multiset.map GenRow.toAnnotated
    (q₀.evaluate d γ E))).row i).fst, fun i' => ?_, fun j => ?_⟩
  · simp only [Fin.snoc_castSucc]; exact ⟨_, rfl⟩
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Fin.snoc_last]
    exact ⟨_, rfl, AggTok.fam_setFam _ _⟩

end NodeRow

/-! ## Two evaluations of one operator -/

section CohNode

/-- **One operator in two coherent situations builds one value per
identifier**, given that its parameters' identifiers – which are smaller –
already determine their values (`hU`). Equal identifiers record equal
parameters, so the two situations agree where the operator reads
(`EvalEnv.agree_of_paramKey`), so the operator's two evaluations are one
(`AggQueryIn.evaluate_congr_reads`), in which the identifier determines the
value (`hfun`). -/
theorem AggQueryIn.coh_node {c n : ℕ} {κ : Fin n → ColKind} (node : AggQueryIn T c n κ)
    (hrr : node.readsRecorded) {rd : Fin c → Bool} (hrd : rd = node.readsOuter) (lab : ℕ)
    (P : GenRow T K n → AggTok T K → Prop) (d : AnnotatedDatabase T K)
    (Q : AggTok T K → AggTok T K → Prop)
    (hfam : ∀ γ E r x, r ∈ node.evaluate d γ E → P r x →
      ∃ key j, x.fam = FamId.mk lab key (E.paramKey rd γ) j [])
    (hfun : ∀ γ E r r' x y, r ∈ node.evaluate d γ E → r' ∈ node.evaluate d γ E →
      P r x → P r' y → x.fam.family = y.fam.family → Q x y)
    (U : AggTok T K → Prop) (M : ℕ)
    (hU : ∀ x y, U x → U y → x.fam = y.fam → sizeOf x.fam < M → x = y)
    {γ₁ γ₂ : Fin c → T} {E₁ E₂ : EvalEnv T K} (hs₁ : E₁.SitOK γ₁) (hs₂ : E₂.SitOK γ₂)
    (hc₁ : ∀ k x, E₁.ctxAt c γ₁ k = Sum.inr x → U x)
    (hc₂ : ∀ k x, E₂.ctxAt c γ₂ k = Sum.inr x → U x)
    {x y : AggTok T K} (hx : ∃ r ∈ node.evaluate d γ₁ E₁, P r x)
    (hy : ∃ r ∈ node.evaluate d γ₂ E₂, P r y) (hxy : x.fam.family = y.fam.family)
    (hM : ∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) : Q x y := by
  obtain ⟨r, hr, hPx⟩ := hx
  obtain ⟨r', hr', hPy⟩ := hy
  obtain ⟨key, j, hfx⟩ := hfam γ₁ E₁ r x hr hPx
  obtain ⟨key', j', hfy⟩ := hfam γ₂ E₂ r' y hr' hPy
  have hpk : E₁.paramKey rd γ₁ = E₂.paramKey rd γ₂ := by
    have := hxy
    rw [hfx, hfy] at this
    simp only [FamId.family, Prod.mk.injEq] at this
    exact this.2.2
  have hsz : ∀ φ, Sum.inr φ ∈ E₁.paramKey rd γ₁ → sizeOf φ < M := fun φ hφ =>
    hM φ (by rw [hfx]; exact hφ)
  have hctx := EvalEnv.agree_of_paramKey rd U M hU hc₁ hc₂ hsz hpk
  have hγ := hs₁.agree hs₂ hctx
  have heq : node.evaluate d γ₁ E₁ = node.evaluate d γ₂ E₂ :=
    node.evaluate_congr_reads hrr d (fun _ hp => absurd hp List.not_mem_nil)
      (hrd ▸ hγ) (hrd ▸ hctx)
  rw [← heq] at hr'
  exact hfun γ₁ E₁ r r' x y hr hr' hPx hPy hxy

end CohNode

/-! ## Combining the cases -/

section Combine

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem AggTok.lab_eq_of_fam {x y : AggTok T K} (h : x.fam = y.fam) : x.lab = y.lab := by
  unfold AggTok.lab
  rw [h]

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
theorem AggTok.lab_eq_of_family {x y : AggTok T K} (h : x.fam.family = y.fam.family) :
    x.lab = y.lab := by
  unfold AggTok.lab
  cases hx : x.fam
  cases hy : y.fam
  rw [hx, hy] at h
  simp only [FamId.family, Prod.mk.injEq] at h
  simp only [FamId.lab, h.1]

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
/-- **Values built by an operator and by its subquery**: their labels
differ, so equal identifiers mean both come from the same place. -/
theorem coh_cons {lab : ℕ} {L : List ℕ} (hnd : (lab :: L).Nodup)
    {N₁ N₂ C₁ C₂ : AggTok T K → Prop} (R : AggTok T K → AggTok T K → Prop)
    (hN₁ : ∀ x, N₁ x → x.lab = lab) (hN₂ : ∀ x, N₂ x → x.lab = lab)
    (hC₁ : ∀ x, C₁ x → x.lab ∈ L) (hC₂ : ∀ x, C₂ x → x.lab ∈ L)
    (hNN : ∀ x y, N₁ x → N₂ y → x.fam.family = y.fam.family → R x y)
    (hCC : ∀ x y, C₁ x → C₂ y → x.fam.family = y.fam.family → R x y) :
    ∀ x y, (N₁ x ∨ C₁ x) → (N₂ y ∨ C₂ y) → x.fam.family = y.fam.family → R x y := by
  have hn := (List.nodup_cons.mp hnd).1
  intro x y hx hy hxy
  have hl := AggTok.lab_eq_of_family hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hNN x y hx hy hxy
  · exact absurd (hN₁ x hx ▸ hl ▸ hC₂ y hy) hn
  · exact absurd (hN₂ y hy ▸ hl.symm ▸ hC₁ x hx) hn
  · exact hCC x y hx hy hxy

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
/-- **Values built by two subqueries**: their labels differ. -/
theorem coh_append {L₁ L₂ : List ℕ} (hnd : (L₁ ++ L₂).Nodup)
    {A₁ A₂ B₁ B₂ : AggTok T K → Prop} (R : AggTok T K → AggTok T K → Prop)
    (hA₁ : ∀ x, A₁ x → x.lab ∈ L₁) (hA₂ : ∀ x, A₂ x → x.lab ∈ L₁)
    (hB₁ : ∀ x, B₁ x → x.lab ∈ L₂) (hB₂ : ∀ x, B₂ x → x.lab ∈ L₂)
    (hAA : ∀ x y, A₁ x → A₂ y → x.fam.family = y.fam.family → R x y)
    (hBB : ∀ x y, B₁ x → B₂ y → x.fam.family = y.fam.family → R x y) :
    ∀ x y, (A₁ x ∨ B₁ x) → (A₂ y ∨ B₂ y) → x.fam.family = y.fam.family → R x y := by
  have hd := List.disjoint_of_nodup_append hnd
  intro x y hx hy hxy
  have hl := AggTok.lab_eq_of_family hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hAA x y hx hy hxy
  · exact (hd (hA₁ x hx) (hl ▸ hB₂ y hy)).elim
  · exact (hd (hA₂ y hy) (hl ▸ hB₁ x hx)).elim
  · exact hBB x y hx hy hxy
omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
/-- `coh_cons` for an operator that may build no column. -/
theorem coh_labCons {w lab : ℕ} {L : List ℕ} (hnd : (labCons w lab L).Nodup)
    {N₁ N₂ C₁ C₂ : AggTok T K → Prop} (R : AggTok T K → AggTok T K → Prop)
    (hN₁ : ∀ x, N₁ x → x.lab = lab ∧ w ≠ 0) (hN₂ : ∀ x, N₂ x → x.lab = lab ∧ w ≠ 0)
    (hC₁ : ∀ x, C₁ x → x.lab ∈ L) (hC₂ : ∀ x, C₂ x → x.lab ∈ L)
    (hNN : ∀ x y, N₁ x → N₂ y → x.fam.family = y.fam.family → R x y)
    (hCC : ∀ x y, C₁ x → C₂ y → x.fam.family = y.fam.family → R x y) :
    ∀ x y, (N₁ x ∨ C₁ x) → (N₂ y ∨ C₂ y) → x.fam.family = y.fam.family → R x y := by
  by_cases hw : w = 0
  · intro x y hx hy hxy
    rcases hx with hx | hx
    · exact absurd hw (hN₁ x hx).2
    rcases hy with hy | hy
    · exact absurd hw (hN₂ y hy).2
    exact hCC x y hx hy hxy
  · rw [labCons_of_ne hw] at hnd
    exact coh_cons hnd R (fun x h => (hN₁ x h).1) (fun x h => (hN₂ x h).1) hC₁ hC₂ hNN hCC

end Combine

/-! ## Across the evaluations of a query -/

section CohAll

/-- **What coherence says of two values of one family**: one identifier,
one value, and one family, one class. -/
def CohRel (x y : AggTok T K) : Prop := (x.fam = y.fam → x = y) ∧ x.classKey = y.classKey

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
theorem CohRel.of_eq {x y : AggTok T K} (h : x = y) : CohRel x y := ⟨fun _ => h, by rw [h]⟩

/-- **What the induction carries**: in two coherent situations whose
provided and built values lie in `U`, two values the query builds with the
same identifier, of size at most `M`, are equal. -/
def AggQueryIn.CohAt (U : AggTok T K → Prop) (M : ℕ) {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) (d : AnnotatedDatabase T K) : Prop :=
  ∀ (γ₁ : Fin c → T) (E₁ : EvalEnv T K) (γ₂ : Fin c → T) (E₂ : EvalEnv T K),
    E₁.SitOK γ₁ → E₂.SitOK γ₂ → (∀ x, E₁.Toks γ₁ l x → U x) → (∀ x, E₂.Toks γ₂ l x → U x) →
    (∀ x, q.Builds d γ₁ E₁ x → U x) → (∀ x, q.Builds d γ₂ E₂ x → U x) →
    ∀ x y, q.Builds d γ₁ E₁ x → q.Builds d γ₂ E₂ y → x.fam.family = y.fam.family →
      (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y

/-- **Coherence at one size**: given that identifiers of size below `M`
determine their values in `U`, identifiers of size `M` do among the values
a query builds. -/
theorem AggQueryIn.cohAt (U : AggTok T K → Prop) (hcl : ∀ x, TermCl U x → U x) (M : ℕ)
    (hU : ∀ x y, U x → U y → x.fam = y.fam → sizeOf x.fam < M → x = y) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.labelsDistinct → q.readsRecorded → q.sourceCols → q.allFramesContainSelf →
      ∀ d, q.CohAt U M d := by
  intro c n κ l q
  induction q with
  | Rel _ _ => intro _ _ _ _ d γ₁ E₁ γ₂ E₂ _ _ _ _ _ _ x y hx; exact hx.elim
  | Hole _ _ _ => intro _ _ _ _ d γ₁ E₁ γ₂ E₂ _ _ _ _ _ _ x y hx; exact hx.elim
  | Param _ _ => intro _ _ _ _ d γ₁ E₁ γ₂ E₂ _ _ _ _ _ _ x y hx; exact hx.elim
  | Empty => intro _ _ _ _ d γ₁ E₁ γ₂ E₂ _ _ _ _ _ _ x y hx; exact hx.elim
  | Proj ps q ih =>
    intro hld hrr hsc hfc d
    exact ih hld hrr hsc.2 hfc d
  | Sel φ q hφ ih =>
    intro hld hrr hsc hfc d
    exact ih hld hrr hsc hfc d
  | Dedup q ih =>
    intro hld hrr hsc hfc d
    exact ih hld hrr hsc hfc d
  | Explode k hk q ih =>
    intro hld hrr hsc hfc d
    exact ih hld hrr hsc hfc d
  | Retag hκ q ih =>
    intro hld hrr hsc hfc d
    exact ih hld hrr hsc hfc d
  | ProvSum is his t q ih =>
    intro hld hrr hsc hfc d
    exact ih hld hrr hsc hfc d
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (q₁.labels ++ q₂.labels).Nodup := hld
    refine coh_append hnd
      (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z hz => (q₁.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₁.builds_spec d γ₂ E₂ z hz).2)
      (fun z hz => (q₂.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₂.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy => ih₁ hnd.of_append_left hrr.1 hsc.1 hfc.1 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        (fun z hz => ht₁ z (hz.mono (List.subset_append_left _ _)))
        (fun z hz => ht₂ z (hz.mono (List.subset_append_left _ _)))
        (fun z hz => hb₁ z (Or.inl hz)) (fun z hz => hb₂ z (Or.inl hz)) x y hx hy hxy)
      (fun x y hx hy hxy => ih₂ hnd.of_append_right hrr.2 hsc.2 hfc.2 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        (fun z hz => ht₁ z (hz.mono (List.subset_append_right _ _)))
        (fun z hz => ht₂ z (hz.mono (List.subset_append_right _ _)))
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (q₁.labels ++ q₂.labels).Nodup := hld
    refine coh_append hnd
      (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z hz => (q₁.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₁.builds_spec d γ₂ E₂ z hz).2)
      (fun z hz => (q₂.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₂.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy => ih₁ hnd.of_append_left hrr.1 hsc.1 hfc.1 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        (fun z hz => ht₁ z (hz.mono (List.subset_append_left _ _)))
        (fun z hz => ht₂ z (hz.mono (List.subset_append_left _ _)))
        (fun z hz => hb₁ z (Or.inl hz)) (fun z hz => hb₂ z (Or.inl hz)) x y hx hy hxy)
      (fun x y hx hy hxy => ih₂ hnd.of_append_right hrr.2 hsc.2 hfc.2 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        (fun z hz => ht₁ z (hz.mono (List.subset_append_right _ _)))
        (fun z hz => ht₂ z (hz.mono (List.subset_append_right _ _)))
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (q₁.labels ++ q₂.labels).Nodup := hld
    refine coh_append hnd
      (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z hz => (q₁.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₁.builds_spec d γ₂ E₂ z hz).2)
      (fun z hz => (q₂.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₂.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy => ih₁ hnd.of_append_left hrr.1 hsc.1 hfc.1 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        ht₁ ht₂ (fun z hz => hb₁ z (Or.inl hz)) (fun z hz => hb₂ z (Or.inl hz)) x y hx hy hxy)
      (fun x y hx hy hxy => ih₂ hnd.of_append_right hrr.2 hsc.2 hfc.2 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        ht₁ ht₂ (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | @Apply cA nA₁ nA₂ κA₁ κA₂ lA q₁ q₂ ih₁ ih₂ =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (q₁.labels ++ q₂.labels).Nodup := hld
    -- the context a row of the left side gives the right side
    have hsub : ∀ {γ : Fin cA → T} {E : EvalEnv T K}, (∀ z, E.Toks γ lA z → U z) →
        (∀ z, (AggQueryIn.Apply q₁ q₂).Builds d γ E z → U z) →
        ∀ r ∈ q₁.evaluate d γ E, ∀ z,
          (E.withCtx (Fin.append r.fst (E.ctxAt _ γ))).Toks
            (Fin.append (GenRow.plainTuple r.fst) γ) [] z → U z := by
      intro γ E ht hb r hr z hz
      rcases hz with ⟨k, hk⟩ | ⟨p, hp, -⟩
      · rw [EvalEnv.ctxAt_withCtx] at hk
        revert hk
        refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k
        · rw [Fin.append_left] at hk
          exact hcl z ((q₁.rowToks hsc.1 d γ E r hr i z hk).mono (fun w hw =>
            hw.elim (fun h => hb w (Or.inl h)) (fun h => ht w h)))
        · rw [Fin.append_right] at hk
          exact ht z (Or.inl ⟨i, hk⟩)
      · exact absurd hp List.not_mem_nil
    refine coh_append hnd (A₁ := q₁.Builds d γ₁ E₁) (A₂ := q₁.Builds d γ₂ E₂)
      (B₁ := fun z => ∃ r ∈ q₁.evaluate d γ₁ E₁, q₂.Builds d
        (Fin.append (GenRow.plainTuple r.fst) γ₁) (E₁.withCtx (Fin.append r.fst (E₁.ctxAt _ γ₁))) z)
      (B₂ := fun z => ∃ r ∈ q₁.evaluate d γ₂ E₂, q₂.Builds d
        (Fin.append (GenRow.plainTuple r.fst) γ₂) (E₂.withCtx (Fin.append r.fst (E₂.ctxAt _ γ₂))) z)
      (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z hz => (q₁.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₁.builds_spec d γ₂ E₂ z hz).2)
      (fun z ⟨r, _, hz⟩ => (q₂.builds_spec _ _ _ z hz).2)
      (fun z ⟨r, _, hz⟩ => (q₂.builds_spec _ _ _ z hz).2)
      (fun x y hx hy hxy => ih₁ hnd.of_append_left hrr.1 hsc.1 hfc.1 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        ht₁ ht₂ (fun z hz => hb₁ z (Or.inl hz)) (fun z hz => hb₂ z (Or.inl hz)) x y hx hy hxy)
      (fun x y ⟨r, hr, hx⟩ ⟨r', hr', hy⟩ hxy => ih₂ hnd.of_append_right hrr.2 hsc.2 hfc.2 d
        _ _ _ _ (hs₁.apply r.fst) (hs₂.apply r'.fst)
        (hsub ht₁ hb₁ r hr) (hsub ht₂ hb₂ r' hr')
        (fun z hz => hb₁ z (Or.inr ⟨r, hr, hz⟩)) (fun z hz => hb₂ z (Or.inr ⟨r', hr', hz⟩))
        x y hx hy hxy)
      x y hx hy hxy hM
  | @Mu cM nM κM s q₀ q₁ ih₀ ih₁ =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (q₀.labels ++ q₁.labels).Nodup := hld
    have hsub : ∀ {γ : Fin cM → T} {E : EvalEnv T K}, (∀ z, E.Toks γ [] z → U z) →
        (∀ z, (AggQueryIn.Mu s q₀ q₁).Builds d γ E z → U z) → ∀ j z,
          (E.assignHole s ((AggQueryIn.muStep s q₁ d γ E)^[j] (q₀.evaluate d γ E))).Toks
            γ [(s, nM)] z → U z := by
      intro γ E ht hb j z hz
      rcases hz with ⟨k, hk⟩ | ⟨p, hp, r, hr, k, hk⟩
      · rw [EvalEnv.ctxAt_assignHole] at hk
        exact ht z (Or.inl ⟨k, hk⟩)
      · obtain rfl := List.mem_singleton.mp hp
        simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr
        exact hcl z ((q₀.muRoundToks s q₁ hsc d γ E j r hr k z hk).mono (fun w hw =>
          hw.elim (fun h => hb w h) (fun h => ht w h)))
    refine coh_append hnd (A₁ := q₀.Builds d γ₁ E₁) (A₂ := q₀.Builds d γ₂ E₂)
      (B₁ := fun z => ∃ j, q₁.Builds d γ₁ (E₁.assignHole s
        ((AggQueryIn.muStep s q₁ d γ₁ E₁)^[j] (q₀.evaluate d γ₁ E₁))) z)
      (B₂ := fun z => ∃ j, q₁.Builds d γ₂ (E₂.assignHole s
        ((AggQueryIn.muStep s q₁ d γ₂ E₂)^[j] (q₀.evaluate d γ₂ E₂))) z)
      (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z hz => (q₀.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₀.builds_spec d γ₂ E₂ z hz).2)
      (fun z ⟨j, hz⟩ => (q₁.builds_spec _ _ _ z hz).2)
      (fun z ⟨j, hz⟩ => (q₁.builds_spec _ _ _ z hz).2)
      (fun x y hx hy hxy => ih₀ hnd.of_append_left hrr.1 hsc.1 hfc.1 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        ht₁ ht₂ (fun z hz => hb₁ z (Or.inl hz)) (fun z hz => hb₂ z (Or.inl hz)) x y hx hy hxy)
      (fun x y ⟨j, hx⟩ ⟨j', hy⟩ hxy => ih₁ hnd.of_append_right hrr.2 hsc.2 hfc.2 d
        _ _ _ _ (hs₁.assignHole _ _) (hs₂.assignHole _ _)
        (hsub ht₁ hb₁ j) (hsub ht₂ hb₂ j')
        (fun z hz => hb₁ z (Or.inr ⟨j, hz⟩)) (fun z hz => hb₂ z (Or.inr ⟨j', hz⟩))
        x y hx hy hxy)
      x y hx hy hxy hM
  | @MuSet cM nM s q₀ q₁ ih₀ ih₁ =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (q₀.labels ++ q₁.labels).Nodup := hld
    have hsub : ∀ {γ : Fin cM → T} {E : EvalEnv T K}, (∀ z, E.Toks γ [] z → U z) →
        ∀ (X : Multiset (AnnotatedTuple T K nM)) z,
          (E.assignHole s (X.map GenRow.ofAnnotated)).Toks γ [(s, nM)] z → U z := by
      intro γ E ht X z hz
      rcases hz with ⟨k, hk⟩ | ⟨p, hp, r, hr, k, hk⟩
      · rw [EvalEnv.ctxAt_assignHole] at hk
        exact ht z (Or.inl ⟨k, hk⟩)
      · obtain rfl := List.mem_singleton.mp hp
        simp only [EvalEnv.assignHole, and_self, ↓reduceDIte] at hr
        obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hr
        exact absurd hk (by simp [GenRow.ofAnnotated])
    refine coh_append hnd (A₁ := q₀.Builds d γ₁ E₁) (A₂ := q₀.Builds d γ₂ E₂)
      (B₁ := fun z => ∃ j, q₁.Builds d γ₁ (E₁.assignHole s
        ((muIter (AggQueryIn.muSetStep s q₀ q₁ d γ₁ E₁) j).map GenRow.ofAnnotated)) z)
      (B₂ := fun z => ∃ j, q₁.Builds d γ₂ (E₂.assignHole s
        ((muIter (AggQueryIn.muSetStep s q₀ q₁ d γ₂ E₂) j).map GenRow.ofAnnotated)) z)
      (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z hz => (q₀.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q₀.builds_spec d γ₂ E₂ z hz).2)
      (fun z ⟨j, hz⟩ => (q₁.builds_spec _ _ _ z hz).2)
      (fun z ⟨j, hz⟩ => (q₁.builds_spec _ _ _ z hz).2)
      (fun x y hx hy hxy => ih₀ hnd.of_append_left hrr.1 hsc.1 hfc.1 d γ₁ E₁ γ₂ E₂ hs₁ hs₂
        ht₁ ht₂ (fun z hz => hb₁ z (Or.inl hz)) (fun z hz => hb₂ z (Or.inl hz)) x y hx hy hxy)
      (fun x y ⟨j, hx⟩ ⟨j', hy⟩ hxy => ih₁ hnd.of_append_right hrr.2 hsc.2 hfc.2 d
        _ _ _ _ (hs₁.assignHole _ _) (hs₂.assignHole _ _)
        (hsub ht₁ _) (hsub ht₂ _)
        (fun z hz => hb₁ z (Or.inr ⟨j, hz⟩)) (fun z hz => hb₂ z (Or.inr ⟨j', hz⟩))
        x y hx hy hxy)
      x y hx hy hxy hM
  | @Gamma cI mI nI₁ nI₂ lab rd is ts fs q keep ord ih =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (labCons nI₂ lab q.labels).Nodup := hld
    refine coh_labCons hnd (fun x y => (∀ φ,
        Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z ⟨r, hr, ⟨j, hz⟩⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_Gamma is ts fs q keep ord d _ _ hr ⟨j, hz⟩
        exact ⟨AggTok.lab_of_fam h, (Fin.pos j).ne'⟩)
      (fun z ⟨r, hr, ⟨j, hz⟩⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_Gamma is ts fs q keep ord d _ _ hr ⟨j, hz⟩
        exact ⟨AggTok.lab_of_fam h, (Fin.pos j).ne'⟩)
      (fun z hz => (q.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy hM => AggQueryIn.coh_node _ hrr hrr.1 lab
        (Q := CohRel)
        (fun r x => ∃ j, r.fst (Fin.natAdd _ j) = Sum.inr x) d
        (fun γ E r x hr hx => AggQueryIn.newFam_Gamma is ts fs q keep ord d γ E hr hx)
        (fun γ E r r' x y hr hr' ⟨j, hx⟩ ⟨j', hy⟩ hxy =>
          ⟨fun hf => AggQueryIn.newFun_Gamma is ts fs q keep ord d γ E hr hr' hx hy hf,
            AggQueryIn.newKey_Gamma is ts fs q keep ord d γ E hr hr' hx hy hxy⟩)
        U M hU hs₁ hs₂ (fun k z hk => ht₁ z (Or.inl ⟨k, hk⟩))
        (fun k z hk => ht₂ z (Or.inl ⟨k, hk⟩)) hx hy hxy hM)
      (fun x y hx hy hxy => ih (labCons_nodup hnd) hrr.2 hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (labCons nI₂ lab q.labels).Nodup := hld
    refine coh_labCons hnd (fun x y => (∀ φ,
        Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z ⟨r, hr, ⟨j, hz⟩⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_GammaScalar ts fs q ord d _ _ hr ⟨j, hz⟩
        exact ⟨AggTok.lab_of_fam h, (Fin.pos j).ne'⟩)
      (fun z ⟨r, hr, ⟨j, hz⟩⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_GammaScalar ts fs q ord d _ _ hr ⟨j, hz⟩
        exact ⟨AggTok.lab_of_fam h, (Fin.pos j).ne'⟩)
      (fun z hz => (q.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy hM => AggQueryIn.coh_node _ hrr hrr.1 lab
        (Q := CohRel)
        (fun r x => ∃ j, r.fst j = Sum.inr x) d
        (fun γ E r x hr hx => AggQueryIn.newFam_GammaScalar ts fs q ord d γ E hr hx)
        (fun γ E r r' x y hr hr' ⟨j, hx⟩ ⟨j', hy⟩ hxy =>
          ⟨fun hf => AggQueryIn.newFun_GammaScalar ts fs q ord d γ E hr hr' hx hy hf,
            AggQueryIn.newKey_GammaScalar ts fs q ord d γ E hr hr' hx hy hxy⟩)
        U M hU hs₁ hs₂ (fun k z hk => ht₁ z (Or.inl ⟨k, hk⟩))
        (fun k z hk => ht₂ z (Or.inl ⟨k, hk⟩)) hx hy hxy hM)
      (fun x y hx hy hxy => ih (labCons_nodup hnd) hrr.2 hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | @GammaNest cI mI nI₁ κ' lab rd is his p f q ih =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (lab :: q.labels).Nodup := hld
    refine coh_cons hnd (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z ⟨r, hr, hz⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_GammaNest is his p f q d _ _ hr hz
        exact AggTok.lab_of_fam h)
      (fun z ⟨r, hr, hz⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_GammaNest is his p f q d _ _ hr hz
        exact AggTok.lab_of_fam h)
      (fun z hz => (q.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy hM => AggQueryIn.coh_node _ hrr hrr.1 lab
        (Q := CohRel)
        (fun r x => r.fst (Fin.natAdd _ 0) = Sum.inr x) d
        (fun γ E r x hr hx => AggQueryIn.newFam_GammaNest is his p f q d γ E hr hx)
        (fun γ E r r' x y hr hr' hx hy hxy =>
          CohRel.of_eq (AggQueryIn.newFun_GammaNest is his p f q d γ E hr hr' hx hy hxy))
        U M hU hs₁ hs₂ (fun k z hk => ht₁ z (Or.inl ⟨k, hk⟩))
        (fun k z hk => ht₂ z (Or.inl ⟨k, hk⟩)) hx hy hxy hM)
      (fun x y hx hy hxy => ih hnd.of_cons hrr.2 hsc.2 hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | @GammaTok cI mI nI₁ nI₂ κ' lab rd is his ts fs a q keep ih =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (labCons nI₂ lab q.labels).Nodup := hld
    refine coh_labCons hnd (fun x y => (∀ φ,
        Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z ⟨r, hr, ⟨j, hz⟩⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_GammaTok is his ts fs a q keep d _ _ hr ⟨j, hz⟩
        exact ⟨AggTok.lab_of_fam h, (Fin.pos j).ne'⟩)
      (fun z ⟨r, hr, ⟨j, hz⟩⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_GammaTok is his ts fs a q keep d _ _ hr ⟨j, hz⟩
        exact ⟨AggTok.lab_of_fam h, (Fin.pos j).ne'⟩)
      (fun z hz => (q.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy hM => AggQueryIn.coh_node _ hrr hrr.1 lab
        (Q := CohRel)
        (fun r x => ∃ j, r.fst (Fin.castAdd 1 (Fin.natAdd _ j)) = Sum.inr x) d
        (fun γ E r x hr hx => AggQueryIn.newFam_GammaTok is his ts fs a q keep d γ E hr hx)
        (fun γ E r r' x y hr hr' ⟨j, hx⟩ ⟨j', hy⟩ hxy =>
          ⟨fun hf => AggQueryIn.newFun_GammaTok is his ts fs a q keep d γ E hr hr' hx hy hf,
            AggQueryIn.newKey_GammaTok is his ts fs a q keep d γ E hr hr' hx hy hxy⟩)
        U M hU hs₁ hs₂ (fun k z hk => ht₁ z (Or.inl ⟨k, hk⟩))
        (fun k z hk => ht₂ z (Or.inl ⟨k, hk⟩)) hx hy hxy hM)
      (fun x y hx hy hxy => ih (labCons_nodup hnd) hrr.2 hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | @Win cI nI mI pI κw lab rd P O o w _ t f q hwr dist keep ih =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (lab :: q.labels).Nodup := hld
    refine coh_cons hnd (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z ⟨r, hr, hz⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_Win P O o w t f q hwr dist keep d _ _ hr hz
        exact AggTok.lab_of_fam h)
      (fun z ⟨r, hr, hz⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_Win P O o w t f q hwr dist keep d _ _ hr hz
        exact AggTok.lab_of_fam h)
      (fun z hz => (q.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy hM => AggQueryIn.coh_node _ hrr hrr.1 lab
        (Q := CohRel)
        (fun r x => r.fst (Fin.last _) = Sum.inr x) d
        (fun γ E r x hr hx => AggQueryIn.newFam_Win P O o w t f q hwr dist keep d γ E hr hx)
        (fun γ E r r' x y hr hr' hx hy hxy =>
          CohRel.of_eq (AggQueryIn.newFun_Win P O o hfc.1 t f q hwr dist keep d γ E hr hr' hx hy
            hxy))
        U M hU hs₁ hs₂ (fun k z hk => ht₁ z (Or.inl ⟨k, hk⟩))
        (fun k z hk => ht₂ z (Or.inl ⟨k, hk⟩)) hx hy hxy hM)
      (fun x y hx hy hxy => ih hnd.of_cons hrr.2 hsc hfc.2 d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM
  | @WinExpr cI nI mI pI qI lab rd P O o ws _ ts fs g q keeps ih =>
    intro hld hrr hsc hfc d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂ hb₁ hb₂ x y hx hy hxy hM
    have hnd : (lab :: q.labels).Nodup := hld
    refine coh_cons hnd (fun x y => (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y)
      (fun z ⟨r, hr, hz⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_WinExpr P O o ws ts fs g q keeps d _ _ hr hz
        exact AggTok.lab_of_fam h)
      (fun z ⟨r, hr, hz⟩ => by
        obtain ⟨_, _, h⟩ := AggQueryIn.newFam_WinExpr P O o ws ts fs g q keeps d _ _ hr hz
        exact AggTok.lab_of_fam h)
      (fun z hz => (q.builds_spec d γ₁ E₁ z hz).2) (fun z hz => (q.builds_spec d γ₂ E₂ z hz).2)
      (fun x y hx hy hxy hM => AggQueryIn.coh_node _ hrr hrr.1 lab
        (Q := CohRel)
        (fun r x => r.fst (Fin.last _) = Sum.inr x) d
        (fun γ E r x hr hx => AggQueryIn.newFam_WinExpr P O o ws ts fs g q keeps d γ E hr hx)
        (fun γ E r r' x y hr hr' hx hy hxy =>
          CohRel.of_eq (AggQueryIn.newFun_WinExpr P O o hfc.1 ts fs g q keeps d γ E hr hr' hx hy
            hxy))
        U M hU hs₁ hs₂ (fun k z hk => ht₁ z (Or.inl ⟨k, hk⟩))
        (fun k z hk => ht₂ z (Or.inl ⟨k, hk⟩)) hx hy hxy hM)
      (fun x y hx hy hxy => ih hnd.of_cons hrr.2 hsc hfc.2 d γ₁ E₁ γ₂ E₂ hs₁ hs₂ ht₁ ht₂
        (fun z hz => hb₁ z (Or.inr hz)) (fun z hz => hb₂ z (Or.inr hz)) x y hx hy hxy)
      x y hx hy hxy hM

end CohAll

/-! ## The theorem -/

section Coherent

omit [ValueType T] in
theorem FamId.root_of_terms' {φ : FamId T} (h : φ.terms' = []) : φ.root = φ := by
  cases φ with
  | mk l k p c ts =>
    simp only [FamId.terms'] at h
    subst h
    rfl

omit [ValueType T] in
theorem FamId.sizeOf_root_lt {φ : FamId T} (h : φ.terms' ≠ []) : sizeOf φ.root < sizeOf φ := by
  cases φ with
  | mk l k p c ts =>
    cases ts with
    | nil => exact absurd rfl h
    | cons t ts =>
      have h1 : 1 ≤ sizeOf ts := by cases ts <;> simp; omega
      simp only [FamId.root, FamId.mk.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
      omega

omit [ValueType T] in
theorem FamId.sizeOf_param_lt' {ψ φ : FamId T} (h : Sum.inr φ ∈ ψ.family.2.2) :
    sizeOf φ < sizeOf ψ := by
  cases ψ with
  | mk l k p c ts => exact FamId.sizeOf_param_lt h

omit [ValueType T] in
@[simp] theorem FamId.family_root (φ : FamId T) : φ.root.family = φ.family := by
  cases φ; rfl

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem AggTok.classKey_postcompTerms (x : AggTok T K) :
    ∀ ts, (x.postcompTerms ts).classKey = x.classKey
  | [] => rfl
  | t :: ts => by
    rw [AggTok.postcompTerms, AggTok.classKey_postcompTerms _ ts, AggTok.classKey_postcompTerm]

/-- **One family, one class**: values of one family are read in one
listing, so they carry the same annotations. -/
def FamKeyed {K₀ : Type} [CommSemiringWithMonus K₀] (S : AggTok T K₀ → Prop) : Prop :=
  ∀ x y, S x → S y → x.fam.family = y.fam.family → x.classKey = y.classKey

/-- **One family identifier, one value, across every evaluation a query
performs; one family, one class.** In two coherent situations whose
provided values are terms over a set `R₀` of values that record no term,
carry no label of the query and are themselves coherent, the values the
query builds in either situation, those of `R₀`, and every term over them
have one value per identifier and one class per family. The induction is
on the size of the identifier: an operator's identifier records its
parameters' identifiers, which are smaller, and equal parameters make
equal inputs (`AggQueryIn.coh_node`). -/
theorem AggQueryIn.builds_coherent {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (hld : q.labelsDistinct) (hrr : q.readsRecorded)
    (hsc : q.sourceCols) (hfc : q.allFramesContainSelf) (d : AnnotatedDatabase T K)
    (R₀ : AggTok T K → Prop) (hR₀t : ∀ y, R₀ y → y.fam.terms' = []) (hR₀ : FamFun R₀)
    (hR₀k : FamKeyed R₀) (hR₀l : ∀ y, R₀ y → y.lab ∉ q.labels)
    {γ₁ γ₂ : Fin c → T} {E₁ E₂ : EvalEnv T K} (hs₁ : E₁.SitOK γ₁) (hs₂ : E₂.SitOK γ₂)
    (ht₁ : ∀ x, E₁.Toks γ₁ l x → TermCl R₀ x) (ht₂ : ∀ x, E₂.Toks γ₂ l x → TermCl R₀ x) :
    FamFun (TermCl (fun x => q.Builds d γ₁ E₁ x ∨ q.Builds d γ₂ E₂ x ∨ R₀ x))
      ∧ FamKeyed (TermCl (fun x => q.Builds d γ₁ E₁ x ∨ q.Builds d γ₂ E₂ x ∨ R₀ x)) := by
  set S : AggTok T K → Prop := fun x => q.Builds d γ₁ E₁ x ∨ q.Builds d γ₂ E₂ x ∨ R₀ x
    with hSdef
  have hSt : ∀ x, S x → x.fam.terms' = [] := by
    rintro x (h | h | h)
    · exact (q.builds_spec d γ₁ E₁ x h).1
    · exact (q.builds_spec d γ₂ E₂ x h).1
    · exact hR₀t x h
  have hcl : ∀ x, TermCl (TermCl S) x → TermCl S x := fun x h => h.idem
  have hR : ∀ x, TermCl R₀ x → TermCl S x := fun x h => h.mono (fun z hz => Or.inr (Or.inr hz))
  have hb₁ : ∀ x, q.Builds d γ₁ E₁ x → TermCl S x := fun x h => TermCl.base (Or.inl h)
  have hb₂ : ∀ x, q.Builds d γ₂ E₂ x → TermCl S x :=
    fun x h => TermCl.base (Or.inr (Or.inl h))
  -- what the induction gives, from either situation to either
  have hsit : ∀ M, (∀ x y, TermCl S x → TermCl S y → x.fam = y.fam → sizeOf x.fam < M →
        x = y) →
      ∀ {γ : Fin c → T} {E : EvalEnv T K}, E.SitOK γ →
        (∀ x, E.Toks γ l x → TermCl R₀ x) → (∀ x, q.Builds d γ E x → TermCl S x) →
      ∀ {γ' : Fin c → T} {E' : EvalEnv T K}, E'.SitOK γ' →
        (∀ x, E'.Toks γ' l x → TermCl R₀ x) → (∀ x, q.Builds d γ' E' x → TermCl S x) →
      ∀ x y, q.Builds d γ E x → q.Builds d γ' E' y → x.fam.family = y.fam.family →
        (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) → CohRel x y :=
    fun M ihM _ _ hs ht hb _ _ hs' ht' hb' x y hx hy hxy hM =>
      q.cohAt (TermCl S) hcl M ihM hld hrr hsc hfc d _ _ _ _ hs hs'
        (fun z hz => hR z (ht z hz)) (fun z hz => hR z (ht' z hz)) hb hb' x y hx hy hxy hM
  -- two values of the base with one family: both built, or both from `R₀`
  have hbase : ∀ M, (∀ x y, TermCl S x → TermCl S y → x.fam = y.fam → sizeOf x.fam < M →
        x = y) →
      ∀ x y, S x → S y → x.fam.family = y.fam.family →
        (∀ φ, Sum.inr φ ∈ x.fam.family.2.2 → sizeOf φ < M) →
        (CohRel x y ∨ (R₀ x ∧ R₀ y)) := by
    intro M ihM x y hx hy hxy hM
    have hl := AggTok.lab_eq_of_family hxy
    rcases hx with h₁ | h₁ | h₁ <;> rcases hy with h₂ | h₂ | h₂
    · exact Or.inl (hsit M ihM hs₁ ht₁ hb₁ hs₁ ht₁ hb₁ _ _ h₁ h₂ hxy hM)
    · exact Or.inl (hsit M ihM hs₁ ht₁ hb₁ hs₂ ht₂ hb₂ _ _ h₁ h₂ hxy hM)
    · exact absurd (hl ▸ (q.builds_spec d γ₁ E₁ _ h₁).2) (hR₀l _ h₂)
    · exact Or.inl (hsit M ihM hs₂ ht₂ hb₂ hs₁ ht₁ hb₁ _ _ h₁ h₂ hxy hM)
    · exact Or.inl (hsit M ihM hs₂ ht₂ hb₂ hs₂ ht₂ hb₂ _ _ h₁ h₂ hxy hM)
    · exact absurd (hl ▸ (q.builds_spec d γ₂ E₂ _ h₁).2) (hR₀l _ h₂)
    · exact absurd (hl.symm ▸ (q.builds_spec d γ₁ E₁ _ h₂).2) (hR₀l _ h₁)
    · exact absurd (hl.symm ▸ (q.builds_spec d γ₂ E₂ _ h₂).2) (hR₀l _ h₁)
    · exact Or.inr ⟨h₁, h₂⟩
  have key : ∀ M, ∀ x y, TermCl S x → TermCl S y → x.fam = y.fam → sizeOf x.fam < M →
      x = y := by
    intro M
    induction M with
    | zero => intro x y _ _ _ h; exact absurd h (Nat.not_lt_zero _)
    | succ M ihM =>
      intro x y hx hy hxy hM
      obtain ⟨x₀, hx₀, hrx, hex⟩ := hx.root hSt
      obtain ⟨y₀, hy₀, hry, hey⟩ := hy.root hSt
      by_cases ht : x.fam.terms' = []
      · have hx₀' : x₀ = x := by rw [hex, ht]; rfl
        have hy₀' : y₀ = y := by rw [hey, ← hxy, ht]; rfl
        subst hx₀' hy₀'
        have hM' : sizeOf x₀.fam ≤ M := Nat.lt_succ_iff.mp hM
        rcases hbase M ihM x₀ y₀ hx₀ hy₀ (congrArg FamId.family hxy)
            (fun φ hφ => lt_of_lt_of_le (FamId.sizeOf_param_lt' hφ) hM') with h | ⟨h₁, h₂⟩
        · exact h.1 hxy
        · exact hR₀ _ _ h₁ h₂ hxy
      · have h₀ : x₀ = y₀ := ihM x₀ y₀ (TermCl.base hx₀) (TermCl.base hy₀)
          (by rw [hrx, hry, hxy])
          (by rw [hrx]; exact lt_of_lt_of_le (FamId.sizeOf_root_lt ht) (Nat.lt_succ_iff.mp hM))
        rw [hex, hey, h₀, hxy]
  have hF : FamFun (TermCl S) := fun x y hx hy hxy => key _ x y hx hy hxy (Nat.lt_succ_self _)
  refine ⟨hF, ?_⟩
  intro x y hx hy hxy
  obtain ⟨x₀, hx₀, hrx, hex⟩ := hx.root hSt
  obtain ⟨y₀, hy₀, hry, hey⟩ := hy.root hSt
  have hf₀ : x₀.fam.family = y₀.fam.family := by
    rw [hrx, hry, FamId.family_root, FamId.family_root, hxy]
  rw [hex, hey, AggTok.classKey_postcompTerms, AggTok.classKey_postcompTerms]
  rcases hbase (sizeOf x₀.fam) (fun x y hx hy hxy _ => hF x y hx hy hxy) x₀ y₀ hx₀ hy₀ hf₀
      (fun φ hφ => FamId.sizeOf_param_lt' hφ) with h | ⟨h₁, h₂⟩
  · exact h.2
  · exact hR₀k _ _ h₁ h₂ hf₀

/-- **A query evaluated from scratch**: what it builds has one value per
identifier and one class per family, terms included. -/
theorem AggQueryIn.builds_coherent_closed {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) (hld : q.labelsDistinct) (hrr : q.readsRecorded)
    (hsc : q.sourceCols) (hfc : q.allFramesContainSelf) (d : AnnotatedDatabase T K)
    (γ : Fin c → T) :
    FamFun (TermCl (q.Builds d γ {})) ∧ FamKeyed (TermCl (q.Builds d γ {})) := by
  have hnone : ∀ x, ({} : EvalEnv T K).Toks γ [] x → TermCl (fun _ : AggTok T K => False) x := by
    intro x hx
    rcases hx with ⟨k, hk⟩ | ⟨p, hp, -⟩
    · rw [EvalEnv.empty_ctxAt] at hk
      exact absurd hk (by simp)
    · exact absurd hp List.not_mem_nil
  have h := q.builds_coherent (γ₁ := γ) (γ₂ := γ) hld hrr hsc hfc d (fun _ => False)
    (fun _ h => h.elim) (fun _ _ h => h.elim) (by intro _ _ h; exact h.elim)
    (fun _ h => h.elim) (EvalEnv.sitOK_empty _) (EvalEnv.sitOK_empty _) hnone hnone
  have hsub : ∀ x, TermCl (q.Builds d γ {}) x →
      TermCl (fun x => q.Builds d γ {} x ∨ q.Builds d γ {} x ∨ False) x :=
    fun x hx => hx.mono (fun z hz => Or.inl hz)
  exact ⟨fun x y hx hy => h.1 x y (hsub x hx) (hsub y hy),
    by intro x y hx hy; exact h.2 x y (hsub x hx) (hsub y hy)⟩

end Coherent
