import Provenance.BasisRec

/-!
# Genericity of the minimal universe: a query reads its parameters only up to order

The order-type lemma `sec:basis` of `sql-semantics.tex` argues and does not
check: a recursion-free query of the minimal signature, with parameters,
answers up to the substitution of its parameters the same on any two
parameter tuples that fall the same way among a finite set of values the
query and the instance fix. This module builds the pieces: a **faithful
value map** – a function of values that keeps the null apart and the order
among the values it is read on – and the fact that every comparison the
evaluator makes commutes with one.
-/

variable {T : Type} [ValueType T]

/-! ## Faithful value maps -/

/-- **A value map faithful on a set**: it keeps the null and the order among
the values of the set. Every comparison the minimal signature makes between
values of the set is preserved by it. -/
structure FaithfulOn (τ : T → T) (W : Set T) : Prop where
  isNull : ∀ a ∈ W, ValueType.isNull (τ a) = ValueType.isNull a
  le_iff : ∀ a ∈ W, ∀ b ∈ W, (τ a ≤ τ b ↔ a ≤ b)

namespace FaithfulOn

variable {τ : T → T} {W : Set T}

theorem mono {W' : Set T} (h : FaithfulOn τ W) (hW : W' ⊆ W) : FaithfulOn τ W' :=
  ⟨fun a ha => h.isNull a (hW ha), fun a ha b hb => h.le_iff a (hW ha) b (hW hb)⟩

theorem eq_iff (h : FaithfulOn τ W) {a b : T} (ha : a ∈ W) (hb : b ∈ W) :
    τ a = τ b ↔ a = b := by
  constructor
  · intro he
    exact le_antisymm ((h.le_iff a ha b hb).mp he.le) ((h.le_iff b hb a ha).mp he.ge)
  · intro he; rw [he]

theorem lt_iff (h : FaithfulOn τ W) {a b : T} (ha : a ∈ W) (hb : b ∈ W) :
    (τ a < τ b) ↔ (a < b) := by
  rw [lt_iff_not_ge, lt_iff_not_ge, h.le_iff b hb a ha]

theorem injOn (h : FaithfulOn τ W) : Set.InjOn τ W :=
  fun _ ha _ hb he => (h.eq_iff ha hb).mp he

/-- A comparison of the signature is preserved. -/
theorem compOp_eval (h : FaithfulOn τ W) (op : CompOp) {a b : T} (ha : a ∈ W) (hb : b ∈ W) :
    op.eval (τ a) (τ b) ↔ op.eval a b := by
  cases op
  all_goals simp only [CompOp.eval]
  · exact h.eq_iff ha hb
  · exact not_congr (h.eq_iff ha hb)
  · exact h.lt_iff ha hb
  · exact h.le_iff a ha b hb
  · exact h.lt_iff hb ha
  · exact h.le_iff b hb a ha
  · exact h.eq_iff ha hb
  · exact not_congr (h.eq_iff ha hb)

/-- And its three-valued reading, the null kept apart. -/
theorem compOp_eval3 (h : FaithfulOn τ W) (op : CompOp) {a b : T} (ha : a ∈ W) (hb : b ∈ W) :
    op.eval3 (τ a) (τ b) = op.eval3 a b := by
  unfold CompOp.eval3
  rw [h.isNull a ha, h.isNull b hb]
  split
  · rfl
  · rw [show decide (op.eval (τ a) (τ b)) = decide (op.eval a b) from
      decide_eq_decide.mpr (h.compOp_eval op ha hb)]

/-- A column of an `ORDER BY` reads alike. -/
theorem orderCol_le (h : FaithfulOn τ W) (c : OrderCol) {a b : T} (ha : a ∈ W) (hb : b ∈ W) :
    c.le (τ a) (τ b) = c.le a b := by
  unfold OrderCol.le
  rw [h.isNull a ha, h.isNull b hb]
  cases hn : ValueType.isNull a <;> cases hm : ValueType.isNull b <;> simp only [Bool.false_eq_true,
    ↓reduceIte]
  cases c.desc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact decide_eq_decide.mpr (h.le_iff a ha b hb)
  · simp only [↓reduceIte]
    exact decide_eq_decide.mpr (h.le_iff b hb a ha)

theorem orderCol_peer (h : FaithfulOn τ W) (c : OrderCol) {a b : T} (ha : a ∈ W) (hb : b ∈ W) :
    c.peer (τ a) (τ b) = c.peer a b := by
  unfold OrderCol.peer
  rw [h.orderCol_le c ha hb, h.orderCol_le c hb ha]

theorem orderSpec_leOn (h : FaithfulOn τ W) {p : ℕ} (o : OrderSpec p) (ks : List (Fin p))
    {x y : Tuple T p} (hx : ∀ k, x k ∈ W) (hy : ∀ k, y k ∈ W) :
    o.leOn ks (τ ∘ x) (τ ∘ y) = o.leOn ks x y := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [OrderSpec.leOn, Function.comp]
    rw [h.orderCol_peer (o k) (hx k) (hy k), h.orderCol_le (o k) (hx k) (hy k), ih]

theorem orderSpec_le (h : FaithfulOn τ W) {p : ℕ} (o : OrderSpec p)
    {x y : Tuple T p} (hx : ∀ k, x k ∈ W) (hy : ∀ k, y k ∈ W) :
    o.le (τ ∘ x) (τ ∘ y) = o.le x y :=
  h.orderSpec_leOn o _ hx hy

theorem orderSpec_lt (h : FaithfulOn τ W) {p : ℕ} (o : OrderSpec p)
    {x y : Tuple T p} (hx : ∀ k, x k ∈ W) (hy : ∀ k, y k ∈ W) :
    o.lt (τ ∘ x) (τ ∘ y) = o.lt x y := by
  unfold OrderSpec.lt
  rw [h.orderSpec_le o hy hx]

theorem orderSpec_peer (h : FaithfulOn τ W) {p : ℕ} (o : OrderSpec p)
    {x y : Tuple T p} (hx : ∀ k, x k ∈ W) (hy : ∀ k, y k ∈ W) :
    o.peer (τ ∘ x) (τ ∘ y) = o.peer x y := by
  unfold OrderSpec.peer
  rw [h.orderSpec_le o hx hy, h.orderSpec_le o hy hx]

/-- A frame condition reads alike. -/
theorem frameCond_holds (h : FaithfulOn τ W) {p : ℕ} (c : FrameCond p)
    {x y : Tuple T p} (hx : ∀ k, x k ∈ W) (hy : ∀ k, y k ∈ W) :
    c.holds (τ ∘ x) (τ ∘ y) = c.holds x y := by
  induction c with
  | whole => rfl
  | le o => exact h.orderSpec_le o hx hy
  | lt o => exact h.orderSpec_lt o hx hy
  | ge o => exact h.orderSpec_le o hy hx
  | gt o => exact h.orderSpec_lt o hy hx
  | and a b iha ihb => simp only [FrameCond.holds, iha, ihb]
  | or a b iha ihb => simp only [FrameCond.holds, iha, ihb]
  | orAll cs ih =>
    simp only [FrameCond.holds]
    exact congrArg _ (funext fun j => ih j)

end FaithfulOn

/-! ## The constants a query names, all of them

`AggQueryIn.consts` lists a projection's constants only, which is what the
value analysis needs; a value map that is to commute with the evaluator has
to fix the constants of every comparison too. -/

/-- The constants of a Boolean term. -/
def BoolTerm.consts {k : ℕ} (b : BoolTerm T k) : Finset T :=
  Union.union (b.args).1.consts (b.args).2.consts

/-- The constants of a classical selection. -/
def Selection.consts {k : ℕ} : Selection T k → Finset T
  | .BT b => b.consts
  | .Not φ => φ.consts
  | .And φ ψ => Union.union φ.consts ψ.consts
  | .Or φ ψ => Union.union φ.consts ψ.consts
  | .True => ∅

/-- The constants of a clause, or none. -/
def Selection.constsOpt {k : ℕ} : Option (Selection T k) → Finset T
  | none => ∅
  | some φ => φ.consts

/-- The constants of a predicate of the general syntax. -/
def GenPredIn.consts {c k : ℕ} {κ : Fin k → ColKind} : GenPredIn T c κ → Finset T
  | .cmp _ t₁ t₂ => Union.union t₁.consts t₂.consts
  | .aggCmp _ _ _ t => t.consts
  | .aggRange _ _ _ t₁ _ t₂ => Union.union t₁.consts t₂.consts
  | .and φ ψ => Union.union φ.consts ψ.consts
  | .or φ ψ => Union.union φ.consts ψ.consts
  | .not φ => φ.consts

/-- The constants of a family of terms. -/
def TermIn.constsFam {c k m : ℕ} (ts : Fin m → TermIn T c k) : Finset T :=
  Finset.univ.biUnion (fun j => (ts j).consts)

/-- **Every constant a query names**, in its columns, its predicates, its
clauses and the terms its aggregates read. -/
def AggQueryIn.allConsts : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Finset T
  | _, _, _, _, .Rel _ _ => ∅
  | _, _, _, _, .Hole _ _ => ∅
  | _, _, _, _, .Empty => ∅
  | _, _, _, _, .Proj ps q => Union.union (Finset.univ.biUnion (fun j => (ps j).consts)) q.allConsts
  | _, _, _, _, .Sel φ q _ => Union.union φ.consts q.allConsts
  | _, _, _, _, .Prod q₁ q₂ => Union.union q₁.allConsts q₂.allConsts
  | _, _, _, _, .Apply q₁ q₂ => Union.union q₁.allConsts q₂.allConsts
  | _, _, _, _, .Sum q₁ q₂ => Union.union q₁.allConsts q₂.allConsts
  | _, _, _, _, .Dedup q => q.allConsts
  | _, _, _, _, .Diff q₁ q₂ => Union.union q₁.allConsts q₂.allConsts
  | _, _, _, _, .Alt _ _ q => q.allConsts
  | _, _, _, _, .Retag _ q => q.allConsts
  | _, _, _, _, .Mu _ q₀ q₁ => Union.union q₀.allConsts q₁.allConsts
  | _, _, _, _, .MuSet _ q₀ q₁ => Union.union q₀.allConsts q₁.allConsts
  | _, _, _, _, .Gamma _ ts _ q keep _ =>
      Union.union (Union.union (TermIn.constsFam ts)
        (Finset.univ.biUnion (fun j => Selection.constsOpt (keep j)))) q.allConsts
  | _, _, _, _, .GammaScalar ts _ q _ => Union.union (TermIn.constsFam ts) q.allConsts
  | _, _, _, _, .GammaNest _ _ p _ q => Union.union p.consts q.allConsts
  | _, _, _, _, .ProvSum _ _ t q => Union.union t.consts q.allConsts
  | _, _, _, _, .GammaTok _ _ ts _ a q keep =>
      Union.union (Union.union (Union.union (TermIn.constsFam ts) a.consts)
        (Finset.univ.biUnion (fun j => Selection.constsOpt (keep j)))) q.allConsts
  | _, _, _, _, .Win _ _ _ _ t _ q _ _ keep =>
      Union.union (Union.union t.consts (Selection.constsOpt keep)) q.allConsts
  | _, _, _, _, .WinExpr _ _ _ _ ts _ _ q keeps =>
      Union.union (Union.union (TermIn.constsFam ts)
        (Finset.univ.biUnion (fun j => Selection.constsOpt (keeps j)))) q.allConsts

/-! ## Terms, predicates and selections under a faithful map

A function-free term is a column, an outer column or a constant, so a map
fixing the constants commutes with it; a comparison between values of the
set the map is faithful on reads alike. -/

namespace FaithfulOn

variable {τ : T → T} {W : Set T}

/-- A function-free term read on mapped values is the mapped value. -/
theorem termIn_eval {c k : ℕ} (t : TermIn T c k) (ht : t.noFun = true)
    (hc : ∀ a ∈ t.consts, τ a = a) (u : Tuple T k) (γ : Fin c → T) :
    t.eval (τ ∘ u) (τ ∘ γ) = τ (t.eval u γ) := by
  cases t with
  | const a => exact (hc a (Finset.mem_singleton_self a)).symm
  | outer j => rfl
  | index j => rfl
  | add _ _ => exact absurd ht (by simp [TermIn.noFun])
  | sub _ _ => exact absurd ht (by simp [TermIn.noFun])
  | mul _ _ => exact absurd ht (by simp [TermIn.noFun])
  | caseWhen _ _ _ _ _ => exact absurd ht (by simp [TermIn.noFun])
  | coalesce _ _ => exact absurd ht (by simp [TermIn.noFun])

theorem termGIn_evalPlain {c k : ℕ} {κ : Fin k → ColKind} (t : TermGIn T c κ)
    (ht : t.noFun = true) (hc : ∀ a ∈ t.consts, τ a = a) (u : Tuple T k) (γ : Fin c → T) :
    t.evalPlain (τ ∘ u) (τ ∘ γ) = τ (t.evalPlain u γ) := by
  cases t with
  | const a => exact (hc a (Finset.mem_singleton_self a)).symm
  | outer j => rfl
  | index j _ => rfl
  | provIndex j _ => rfl
  | cmpAgg _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | chiGate _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | add _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | sub _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | mul _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | caseWhen _ _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | coalesce _ _ => exact absurd ht (by simp [TermGIn.noFun])

theorem projColIn_evalPlain {c k : ℕ} {κ : Fin k → ColKind} (p : ProjColIn T c κ)
    (hp : p.noFun = true) (hc : ∀ a ∈ p.consts, τ a = a) (u : Tuple T k) (γ : Fin c → T) :
    p.evalPlain (τ ∘ u) (τ ∘ γ) = τ (p.evalPlain u γ) := by
  cases p with
  | term t => exact termGIn_evalPlain t hp hc u γ
  | token j _ => rfl
  | aggTerm _ _ _ => exact absurd hp (by simp [ProjColIn.noFun])
  | aggTermOf j _ t =>
    show t.unary (τ (u j)) = τ (t.unary (u j))
    unfold TermIn.unary
    have := termIn_eval (τ := τ) t hp hc (fun i => i.elim0) (fun _ => u j)
    rw [← this]
    congr 1
    funext i
    exact i.elim0
  | provTerm t => exact termGIn_evalPlain t hp hc u γ

/-- A function-free term's value is a value of the row, the context or a
constant: it lies in any set holding those. -/
theorem termIn_eval_mem {c k : ℕ} (t : TermIn T c k) (ht : t.noFun = true)
    (hc : ∀ a ∈ t.consts, a ∈ W) {u : Tuple T k} (hu : ∀ j, u j ∈ W) {γ : Fin c → T}
    (hγ : ∀ j, γ j ∈ W) : t.eval u γ ∈ W := by
  cases t with
  | const a => exact hc a (Finset.mem_singleton_self a)
  | outer j => exact hγ j
  | index j => exact hu j
  | add _ _ => exact absurd ht (by simp [TermIn.noFun])
  | sub _ _ => exact absurd ht (by simp [TermIn.noFun])
  | mul _ _ => exact absurd ht (by simp [TermIn.noFun])
  | caseWhen _ _ _ _ _ => exact absurd ht (by simp [TermIn.noFun])
  | coalesce _ _ => exact absurd ht (by simp [TermIn.noFun])

theorem termGIn_evalPlain_mem {c k : ℕ} {κ : Fin k → ColKind} (t : TermGIn T c κ)
    (ht : t.noFun = true) (hc : ∀ a ∈ t.consts, a ∈ W) {u : Tuple T k} (hu : ∀ j, u j ∈ W)
    {γ : Fin c → T} (hγ : ∀ j, γ j ∈ W) : t.evalPlain u γ ∈ W := by
  cases t with
  | const a => exact hc a (Finset.mem_singleton_self a)
  | outer j => exact hγ j
  | index j _ => exact hu j
  | provIndex j _ => exact hu j
  | cmpAgg _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | chiGate _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | add _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | sub _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | mul _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | caseWhen _ _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
  | coalesce _ _ => exact absurd ht (by simp [TermGIn.noFun])

/-- A Boolean term reads alike on mapped rows. -/
theorem boolTerm_eval3 (h : FaithfulOn τ W) {k : ℕ} (b : BoolTerm T k) (hb : b.noFun = true)
    (hc : ∀ a ∈ b.consts, τ a = a ∧ a ∈ W) {u : Tuple T k} (hu : ∀ j, u j ∈ W) :
    b.eval3 (τ ∘ u) = b.eval3 u := by
  unfold BoolTerm.eval3
  have h₁ := Bool.and_eq_true_iff.mp hb
  have hc₁ : ∀ a ∈ (b.args).1.consts, τ a = a :=
    fun a ha => (hc a (Finset.mem_union_left _ ha)).1
  have hc₂ : ∀ a ∈ (b.args).2.consts, τ a = a :=
    fun a ha => (hc a (Finset.mem_union_right _ ha)).1
  rw [show (b.args).1.eval (τ ∘ u) = (b.args).1.eval (τ ∘ u) (τ ∘ fun _ : Fin 0 => 0) from
      congrArg _ (funext fun j => j.elim0),
    show (b.args).2.eval (τ ∘ u) = (b.args).2.eval (τ ∘ u) (τ ∘ fun _ : Fin 0 => 0) from
      congrArg _ (funext fun j => j.elim0),
    termIn_eval _ h₁.1 hc₁ u (fun _ => 0), termIn_eval _ h₁.2 hc₂ u (fun _ => 0)]
  exact h.compOp_eval3 _
    (termIn_eval_mem _ h₁.1 (fun a ha => (hc a (Finset.mem_union_left _ ha)).2) hu
      (γ := fun _ => 0) (fun j => j.elim0))
    (termIn_eval_mem _ h₁.2 (fun a ha => (hc a (Finset.mem_union_right _ ha)).2) hu
      (γ := fun _ => 0) (fun j => j.elim0))

/-- A classical selection reads alike on mapped rows. -/
theorem selection_eval3 (h : FaithfulOn τ W) {k : ℕ} (φ : Selection T k) (hφ : φ.noFun = true)
    (hc : ∀ a ∈ φ.consts, τ a = a ∧ a ∈ W) {u : Tuple T k} (hu : ∀ j, u j ∈ W) :
    φ.eval3 (τ ∘ u) = φ.eval3 u := by
  induction φ with
  | BT b => exact h.boolTerm_eval3 b hφ hc hu
  | Not φ ih => exact congrArg Kleene.not (ih hφ hc)
  | And φ ψ ihφ ihψ =>
    have h₁ := Bool.and_eq_true_iff.mp hφ
    simp only [Selection.eval3]
    rw [ihφ h₁.1 (fun a ha => hc a (Finset.mem_union_left _ ha)),
      ihψ h₁.2 (fun a ha => hc a (Finset.mem_union_right _ ha))]
  | Or φ ψ ihφ ihψ =>
    have h₁ := Bool.and_eq_true_iff.mp hφ
    simp only [Selection.eval3]
    rw [ihφ h₁.1 (fun a ha => hc a (Finset.mem_union_left _ ha)),
      ihψ h₁.2 (fun a ha => hc a (Finset.mem_union_right _ ha))]
  | True => rfl

theorem selection_keeps (h : FaithfulOn τ W) {k : ℕ} (φ : Selection T k) (hφ : φ.noFun = true)
    (hc : ∀ a ∈ φ.consts, τ a = a ∧ a ∈ W) {u : Tuple T k} (hu : ∀ j, u j ∈ W) :
    φ.keeps (τ ∘ u) = φ.keeps u := by
  unfold Selection.keeps
  rw [h.selection_eval3 φ hφ hc hu]

theorem selection_keepsOpt (h : FaithfulOn τ W) {k : ℕ} (keep : Option (Selection T k))
    (hφ : Selection.noFunOpt keep = true)
    (hc : ∀ a ∈ Selection.constsOpt keep, τ a = a ∧ a ∈ W) {u : Tuple T k}
    (hu : ∀ j, u j ∈ W) : Selection.keepsOpt keep (τ ∘ u) = Selection.keepsOpt keep u := by
  cases keep with
  | none => rfl
  | some φ => exact h.selection_keeps φ hφ hc hu

/-- A predicate of the general syntax reads alike on mapped rows. -/
theorem genPredIn_evalPlain3 (h : FaithfulOn τ W) {c k : ℕ} {κ : Fin k → ColKind}
    (φ : GenPredIn T c κ) (hφ : φ.noFun = true) (hc : ∀ a ∈ φ.consts, τ a = a ∧ a ∈ W)
    {u : Tuple T k} (hu : ∀ j, u j ∈ W) {γ : Fin c → T} (hγ : ∀ j, γ j ∈ W) :
    φ.evalPlain3 (τ ∘ u) (τ ∘ γ) = φ.evalPlain3 u γ := by
  induction φ with
  | cmp op t₁ t₂ =>
    have h₁ := Bool.and_eq_true_iff.mp hφ
    simp only [GenPredIn.evalPlain3]
    rw [termGIn_evalPlain t₁ h₁.1 (fun a ha => (hc a (Finset.mem_union_left _ ha)).1),
      termGIn_evalPlain t₂ h₁.2 (fun a ha => (hc a (Finset.mem_union_right _ ha)).1)]
    exact h.compOp_eval3 op
      (termGIn_evalPlain_mem t₁ h₁.1 (fun a ha => (hc a (Finset.mem_union_left _ ha)).2) hu hγ)
      (termGIn_evalPlain_mem t₂ h₁.2 (fun a ha => (hc a (Finset.mem_union_right _ ha)).2) hu hγ)
  | aggCmp j _ op t =>
    simp only [GenPredIn.evalPlain3, Function.comp_apply]
    rw [termGIn_evalPlain t hφ (fun a ha => (hc a ha).1)]
    exact h.compOp_eval3 op (hu j)
      (termGIn_evalPlain_mem t hφ (fun a ha => (hc a ha).2) hu hγ)
  | aggRange j _ op₁ t₁ op₂ t₂ =>
    have h₁ := Bool.and_eq_true_iff.mp hφ
    simp only [GenPredIn.evalPlain3, Function.comp_apply]
    rw [termGIn_evalPlain t₁ h₁.1 (fun a ha => (hc a (Finset.mem_union_left _ ha)).1),
      termGIn_evalPlain t₂ h₁.2 (fun a ha => (hc a (Finset.mem_union_right _ ha)).1)]
    rw [h.compOp_eval3 op₁ (hu j)
      (termGIn_evalPlain_mem t₁ h₁.1 (fun a ha => (hc a (Finset.mem_union_left _ ha)).2) hu hγ),
      h.compOp_eval3 op₂ (hu j)
      (termGIn_evalPlain_mem t₂ h₁.2 (fun a ha => (hc a (Finset.mem_union_right _ ha)).2) hu hγ)]
  | and φ ψ ihφ ihψ =>
    have h₁ := Bool.and_eq_true_iff.mp hφ
    simp only [GenPredIn.evalPlain3]
    rw [ihφ h₁.1 (fun a ha => hc a (Finset.mem_union_left _ ha)),
      ihψ h₁.2 (fun a ha => hc a (Finset.mem_union_right _ ha))]
  | or φ ψ ihφ ihψ =>
    have h₁ := Bool.and_eq_true_iff.mp hφ
    simp only [GenPredIn.evalPlain3]
    rw [ihφ h₁.1 (fun a ha => hc a (Finset.mem_union_left _ ha)),
      ihψ h₁.2 (fun a ha => hc a (Finset.mem_union_right _ ha))]
  | not φ ih =>
    simp only [GenPredIn.evalPlain3]
    rw [ih hφ hc]

theorem genPredIn_holdsPlain (h : FaithfulOn τ W) {c k : ℕ} {κ : Fin k → ColKind}
    (φ : GenPredIn T c κ) (hφ : φ.noFun = true) (hc : ∀ a ∈ φ.consts, τ a = a ∧ a ∈ W)
    {u : Tuple T k} (hu : ∀ j, u j ∈ W) {γ : Fin c → T} (hγ : ∀ j, γ j ∈ W) :
    φ.holdsPlain (τ ∘ u) (τ ∘ γ) ↔ φ.holdsPlain u γ := by
  unfold GenPredIn.holdsPlain
  rw [h.genPredIn_evalPlain3 φ hφ hc hu hγ]

end FaithfulOn

/-! ## What a count reads

A count is a function of how many non-null values its sequence holds
(`SeqAggFunc.IsCount`), so it reads a listing of a bag through the bag's
non-null count alone, and a faithful map of the bag's rows keeps that
count. -/

/-- The non-null count of a term over a bag of rows. -/
def Multiset.nonNullCount {c m : ℕ} (t : TermIn T c m) (γ : Fin c → T)
    (S : Multiset (Tuple T m)) : ℕ :=
  S.countP (fun u => ValueType.isNull (t.eval u γ) = false)

/-- A count over a listing of a bag is a function of the bag's non-null count. -/
theorem SeqAggFunc.IsCount.eq_of_nonNullCount {cnt : SeqAggFunc T} (hc : cnt.IsCount)
    {c m : ℕ} (t : TermIn T c m) (γ γ' : Fin c → T) {L L' : List (Tuple T m)}
    (h : Multiset.nonNullCount t γ (L : Multiset (Tuple T m))
      = Multiset.nonNullCount t γ' (L' : Multiset (Tuple T m))) :
    cnt (L.map (fun v => t.eval v γ)) = cnt (L'.map (fun v => t.eval v γ')) := by
  obtain ⟨g, hg⟩ := hc
  rw [hg, hg]
  congr 1
  unfold Multiset.nonNullCount at h
  rw [Multiset.coe_countP, Multiset.coe_countP] at h
  rw [List.countP_map, List.countP_map]
  refine Eq.trans ?_ (Eq.trans h ?_)
  · exact List.countP_congr (fun v _ => by simp [Function.comp])
  · exact List.countP_congr (fun v _ => by simp [Function.comp])

/-- The non-null count over a listing of a bag is the bag's. -/
theorem Multiset.nonNullCount_coe_perm {c m : ℕ} (t : TermIn T c m) (γ : Fin c → T)
    {L : List (Tuple T m)} {S : Multiset (Tuple T m)} (h : (L : Multiset (Tuple T m)) = S) :
    Multiset.nonNullCount t γ (L : Multiset (Tuple T m)) = Multiset.nonNullCount t γ S := by
  rw [h]

namespace FaithfulOn

variable {τ : T → T} {W : Set T}

/-- A faithful map keeps the non-null count of a bag whose rows it reads. -/
theorem nonNullCount_map (h : FaithfulOn τ W) {c m : ℕ} (t : TermIn T c m) (ht : t.noFun = true)
    (hc : ∀ a ∈ t.consts, τ a = a ∧ a ∈ W) {γ : Fin c → T} (hγ : ∀ j, γ j ∈ W)
    {S : Multiset (Tuple T m)} (hS : ∀ u ∈ S, ∀ j, u j ∈ W) :
    Multiset.nonNullCount t (τ ∘ γ) (S.map (fun u => (τ ∘ u : Tuple T m)))
      = Multiset.nonNullCount t γ S := by
  unfold Multiset.nonNullCount
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, Multiset.filter_map,
    Multiset.card_map]
  congr 1
  refine Multiset.filter_congr (fun u hu => ?_)
  show ValueType.isNull (t.eval (τ ∘ u) (τ ∘ γ)) = false ↔ ValueType.isNull (t.eval u γ) = false
  rw [termIn_eval t ht (fun a ha => (hc a ha).1),
    h.isNull _ (termIn_eval_mem t ht (fun a ha => (hc a ha).2) (hS u hu) hγ)]

/-- A group of the mapped relation is the mapped group. -/
theorem filter_key_map (h : FaithfulOn τ W) {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    {r : Multiset (Tuple T m)} (hr : ∀ u ∈ r, ∀ j, u j ∈ W) {g : Tuple T n₁}
    (hg : ∀ k, g k ∈ W) :
    (r.map (fun u => (τ ∘ u : Tuple T m))).filter
        (fun u => ∀ k' : Fin n₁, u (is k') = (τ ∘ g : Tuple T n₁) k')
      = (r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map
          (fun u => (τ ∘ u : Tuple T m)) := by
  rw [Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr (fun u hu => ?_)
  show (∀ k', τ (u (is k')) = τ (g k')) ↔ ∀ k', u (is k') = g k'
  exact forall_congr' (fun k' => h.eq_iff (hr u hu _) (hg k'))

/-- A clause keeps the mapped rows it keeps. -/
theorem filter_keeps_map (h : FaithfulOn τ W) {m : ℕ} (keep : Option (Selection T m))
    (hk : Selection.noFunOpt keep = true)
    (hc : ∀ a ∈ Selection.constsOpt keep, τ a = a ∧ a ∈ W)
    {S : Multiset (Tuple T m)} (hS : ∀ u ∈ S, ∀ j, u j ∈ W) :
    (S.map (fun u => (τ ∘ u : Tuple T m))).filter (fun u => Selection.keepsOpt keep u = true)
      = (S.filter (fun u => Selection.keepsOpt keep u = true)).map
          (fun u => (τ ∘ u : Tuple T m)) := by
  rw [Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr (fun u hu => ?_)
  show Selection.keepsOpt keep (τ ∘ u) = true ↔ Selection.keepsOpt keep u = true
  rw [h.selection_keepsOpt keep hk hc (hS u hu)]

end FaithfulOn

/-- The occurrence sequence of a group, as a bag: the group's rows, cut by
the clause. -/
theorem Relation.groupSeqOptOrd_coe {m n₁ : ℕ} (is : Tuple (Fin m) n₁) (ord : GroupOrder T m)
    (r : Relation T m) (g : Tuple T n₁) (keep : Option (Selection T m)) :
    ((Relation.groupSeqOptOrd is ord r g keep : List (Tuple T m)) : Multiset (Tuple T m))
      = ((r : Multiset (Tuple T m)).filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).filter
          (fun u => Selection.keepsOpt keep u = true) := by
  have hbase : ((Relation.groupSeqOrd is ord r g : List (Tuple T m)) : Multiset (Tuple T m))
      = (r : Multiset (Tuple T m)).filter (fun u => ∀ k' : Fin n₁, u (is k') = g k') := by
    rw [Multiset.coe_eq_coe.mpr (Relation.groupSeqOrd_perm is ord r g)]
    unfold Relation.groupSeq
    rw [sortList_coe]
  cases keep with
  | none =>
    rw [Relation.groupSeqOptOrd_none, hbase]
    symm
    exact Multiset.filter_eq_self.mpr (fun _ _ => rfl)
  | some φ =>
    show (((Relation.groupSeqOrd is ord r g).filter φ.keeps : List (Tuple T m))
      : Multiset (Tuple T m)) = _
    rw [← hbase, Multiset.filter_coe]
    congr 1
    exact List.filter_congr (fun u _ => Bool.decide_eq_true.symm)

/-! ## Frames and window values under a faithful map -/

/-- Duplicate elimination commutes with a map injective on the bag. -/
theorem Multiset.dedup_map_of_injOn {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s : Multiset α} (hf : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
    (s.map f).dedup = s.dedup.map f := by
  refine (Multiset.Nodup.ext (Multiset.nodup_dedup _)
    (Multiset.Nodup.map_on (fun x hx y hy => hf x (Multiset.mem_dedup.mp hx) y
      (Multiset.mem_dedup.mp hy)) (Multiset.nodup_dedup s))).mpr (fun b => ?_)
  rw [Multiset.mem_dedup, Multiset.mem_map, Multiset.mem_map]
  exact exists_congr (fun a => and_congr_left (fun _ => Multiset.mem_dedup.symm))

namespace FaithfulOn

variable {τ : T → T} {W : Set T}

/-- Two rows over the set are mapped alike only if equal. -/
theorem row_eq_iff (h : FaithfulOn τ W) {m : ℕ} {x y : Tuple T m}
    (hx : ∀ j, x j ∈ W) (hy : ∀ j, y j ∈ W) :
    (τ ∘ x : Tuple T m) = (τ ∘ y) ↔ x = y := by
  constructor
  · intro he
    funext j
    exact (h.eq_iff (hx j) (hy j)).mp (congrFun he j)
  · intro he; rw [he]

/-- A row of a frame is the current row or a row of the relation. -/
theorem _root_.ValueFrame.mem_frameOf_elim {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) {X : Multiset (Tuple T n)} {x u : Tuple T n}
    (hu : u ∈ ValueFrame.frameOf (α := Tuple T n) id P O w X x) : u = x ∨ u ∈ X := by
  unfold ValueFrame.frameOf at hu
  rw [Multiset.erase_instEq (α := Tuple T n) (fun a b => LinearOrder.toDecidableEq a b)
    (fun a b => instDecidableEqTuple a b)] at hu
  split at hu
  · rcases Multiset.mem_cons.mp hu with h | h
    · exact Or.inl h
    · exact Or.inr (Multiset.mem_of_mem_filter (Multiset.mem_of_mem_erase h))
  · exact Or.inr (Multiset.mem_of_mem_filter (Multiset.mem_of_mem_erase hu))

/-- Erasing commutes with a map injective at the erased element. -/
theorem _root_.Multiset.erase_map_of_injAt {α : Type} [LinearOrder α] (f : α → α)
    (S : Multiset α) (x : α) (hf : ∀ y ∈ S, f y = f x → y = x) :
    (S.map f).erase (f x) = (S.erase x).map f := by
  by_cases hmem : x ∈ S
  · exact (Multiset.map_erase_of_mem _ S hmem).symm
  · rw [Multiset.erase_of_notMem hmem, Multiset.erase_of_notMem]
    intro hc
    obtain ⟨y, hy, hyx⟩ := Multiset.mem_map.mp hc
    exact hmem (hf y hy hyx ▸ hy)

/-- The frame of a mapped row in the mapped relation is the mapped frame. -/
theorem frameOf_map (h : FaithfulOn τ W) {n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (w : ValueFrame T p) {X : Multiset (Tuple T n)} (hX : ∀ u ∈ X, ∀ j, u j ∈ W)
    {x : Tuple T n} (hx : ∀ j, x j ∈ W) :
    ValueFrame.frameOf (α := Tuple T n) id P O w (X.map (fun u => (τ ∘ u : Tuple T n)))
        (τ ∘ x)
      = (ValueFrame.frameOf (α := Tuple T n) id P O w X x).map (fun u => (τ ∘ u : Tuple T n)) := by
  have hkey : ∀ {q : ℕ} (is : Tuple (Fin n) q) (u : Tuple T n),
      Tuple.key is (τ ∘ u) = (τ ∘ Tuple.key is u : Tuple T q) := fun _ _ => rfl
  have hpred : ∀ y ∈ X,
      ((Tuple.key P (id (τ ∘ y : Tuple T n)) = Tuple.key P (id (τ ∘ x : Tuple T n))
          ∧ w.ρ (Tuple.key O (id (τ ∘ y : Tuple T n))) (Tuple.key O (id (τ ∘ x : Tuple T n)))
            = true)
        ↔ (Tuple.key P (id y) = Tuple.key P (id x)
          ∧ w.ρ (Tuple.key O (id y)) (Tuple.key O (id x)) = true)) := by
    intro y hy
    simp only [id]
    rw [hkey P y, hkey P x, hkey O y, hkey O x, ValueFrame.ρ_apply, ValueFrame.ρ_apply,
      h.frameCond_holds w.cond (x := Tuple.key O y) (y := Tuple.key O x)
        (fun k => hX y hy _) (fun k => hx _)]
    exact and_congr (h.row_eq_iff (x := Tuple.key P y) (y := Tuple.key P x)
      (fun k => hX y hy _) (fun k => hx _)) Iff.rfl
  have hfilt : (X.map (fun u => (τ ∘ u : Tuple T n))).filter (fun y =>
        Tuple.key P (id y) = Tuple.key P (id (τ ∘ x : Tuple T n))
          ∧ w.ρ (Tuple.key O (id y)) (Tuple.key O (id (τ ∘ x : Tuple T n))) = true)
      = (X.filter (fun y => Tuple.key P (id y) = Tuple.key P (id x)
          ∧ w.ρ (Tuple.key O (id y)) (Tuple.key O (id x)) = true)).map
          (fun u => (τ ∘ u : Tuple T n)) := by
    rw [Multiset.filter_map]
    congr 1
    exact Multiset.filter_congr (fun y hy => hpred y hy)
  have herase : ∀ (S : Multiset (Tuple T n)), (∀ u ∈ S, ∀ j, u j ∈ W) →
      @Multiset.erase (Tuple T n) (fun a b => LinearOrder.toDecidableEq a b)
          (S.map (fun u => (τ ∘ u : Tuple T n))) (τ ∘ x)
        = (@Multiset.erase (Tuple T n) (fun a b => LinearOrder.toDecidableEq a b) S x).map
            (fun u => (τ ∘ u : Tuple T n)) :=
    fun S hS => Multiset.erase_map_of_injAt _ S x
      (fun y hy hyx => (h.row_eq_iff (hS y hy) hx).mp hyx)
  unfold ValueFrame.frameOf
  rw [ValueFrame.s_apply, ValueFrame.s_apply, hfilt]
  split
  · rw [Multiset.map_cons]
    congr 1
    exact herase _ (fun u hu => hX u (Multiset.mem_of_mem_filter hu))
  · exact herase _ (fun u hu => hX u (Multiset.mem_of_mem_filter hu))

/-- The non-null count of a window's frame, under a clause or not. -/
theorem frame_nonNullCount (h : FaithfulOn τ W) {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (ht : t.noFun = true) (hc : ∀ a ∈ t.consts, τ a = a ∧ a ∈ W)
    (keep : Option (Selection T n)) (hk : Selection.noFunOpt keep = true)
    (hkc : ∀ a ∈ Selection.constsOpt keep, τ a = a ∧ a ∈ W)
    {X : Multiset (Tuple T n)} (hX : ∀ u ∈ X, ∀ j, u j ∈ W) {x : Tuple T n} (hx : ∀ j, x j ∈ W)
    {γ : Fin c → T} (hγ : ∀ j, γ j ∈ W) :
    Multiset.nonNullCount t (τ ∘ γ)
        (((ValueFrame.frameListOf (α := Tuple T n) id P O o w
          (X.map (fun u => (τ ∘ u : Tuple T n))) (τ ∘ x)).filter
            (fun u => Selection.keepsOpt keep u = true) : List (Tuple T n)))
      = Multiset.nonNullCount t γ
        (((ValueFrame.frameListOf (α := Tuple T n) id P O o w X x).filter
            (fun u => Selection.keepsOpt keep u = true) : List (Tuple T n))) := by
  have hmem : ∀ u ∈ ValueFrame.frameOf (α := Tuple T n) id P O w X x, ∀ j, u j ∈ W := by
    intro u hu
    rcases ValueFrame.mem_frameOf_elim P O w hu with rfl | hu'
    · exact hx
    · exact hX u hu'
  rw [← Multiset.filter_coe, ← Multiset.filter_coe, ValueFrame.frameListOf_coe,
    ValueFrame.frameListOf_coe, h.frameOf_map P O w hX hx, h.filter_keeps_map keep hk hkc hmem,
    h.nonNullCount_map t ht hc hγ (fun u hu => hmem u (Multiset.mem_of_mem_filter hu))]

end FaithfulOn

/-! ## The values a query computes

In the minimal signature a query builds a value only by counting: every
other value of its result is read off the instance, off the context or off
its own constants. `AggQueryIn.countValsAll` collects the counts – the
values of the aggregate columns of every aggregating node, at every
context and, under a recursion, at every round – so that the value lemma
`AggQueryIn.valsIn_evaluatePlain` can say where every value of a result
comes from. -/

/-- A relation with every value mapped. -/
def Relation.mapVals (τ : T → T) {n : ℕ} (r : Relation T n) : Relation T n :=
  (r : Multiset (Tuple T n)).map (fun u => (τ ∘ u : Tuple T n))

/-- **The counts a query computes**: the values of the aggregate columns
of each of its aggregating nodes, over every context, and, under a
recursion, over every relation the recursive name may be bound to. It is
the set a faithful map must fix for the query to commute with it. -/
noncomputable def AggQueryIn.countValsAll : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c n κ l → Database T → Set T
  | _, _, _, _, .Rel _ _, _ => ∅
  | _, _, _, _, .Hole _ _, _ => ∅
  | _, _, _, _, .Empty, _ => ∅
  | _, _, _, _, .Proj _ q, D => q.countValsAll D
  | _, _, _, _, .Sel _ q _, D => q.countValsAll D
  | _, _, _, _, .Prod q₁ q₂, D => Union.union (q₁.countValsAll D) (q₂.countValsAll D)
  | _, _, _, _, .Apply q₁ q₂, D => Union.union (q₁.countValsAll D) (q₂.countValsAll D)
  | _, _, _, _, .Sum q₁ q₂, D => Union.union (q₁.countValsAll D) (q₂.countValsAll D)
  | _, _, _, _, .Dedup q, D => q.countValsAll D
  | _, _, _, _, .Diff q₁ q₂, D => Union.union (q₁.countValsAll D) (q₂.countValsAll D)
  | _, _, _, _, .Alt _ _ q, D => q.countValsAll D
  | _, _, _, _, .Retag _ q, D => q.countValsAll D
  | _, n, _, _, .Mu s q₀ q₁, D =>
      Union.union (q₀.countValsAll D)
        (Set.iUnion (fun X : Relation T n => q₁.countValsAll (D.assign s X)))
  | _, n, _, _, .MuSet s q₀ q₁, D =>
      Union.union (q₀.countValsAll D)
        (Set.iUnion (fun X : Relation T n => q₁.countValsAll (D.assign s X)))
  | _, _, _, _, @AggQueryIn.Gamma _ _ _ n₁ n₂ is ts fs q keep ord, D =>
      Union.union (q.countValsAll D)
        {v | ∃ (γ : Fin _ → T) (u : Tuple T (n₁ + n₂)),
          Multiset.Mem ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain D γ) u
            ∧ ∃ j : Fin n₂, v = u (Fin.natAdd n₁ j)}
  | _, _, _, _, @AggQueryIn.GammaScalar _ _ _ n₂ ts fs q ord, D =>
      Union.union (q.countValsAll D)
        {v | ∃ (γ : Fin _ → T) (u : Tuple T n₂),
          Multiset.Mem ((AggQueryIn.GammaScalar ts fs q ord).evaluatePlain D γ) u
            ∧ ∃ j : Fin n₂, v = u j}
  | _, _, _, _, @AggQueryIn.GammaNest _ _ _ n₁ _ is his p f q, D =>
      Union.union (q.countValsAll D)
        {v | ∃ (γ : Fin _ → T) (u : Tuple T (n₁ + 1)),
          Multiset.Mem ((AggQueryIn.GammaNest is his p f q).evaluatePlain D γ) u
            ∧ v = u (Fin.natAdd n₁ 0)}
  | _, _, _, _, .ProvSum _ _ _ q, D => q.countValsAll D
  | _, _, _, _, .GammaTok _ _ _ _ _ q _, D => q.countValsAll D
  | _, _, _, _, @AggQueryIn.Win _ _ n _ _ _ P O o w t f q hrr dist keep, D =>
      Union.union (q.countValsAll D)
        {v | ∃ (γ : Fin _ → T) (u : Tuple T (n + 1)),
          Multiset.Mem ((AggQueryIn.Win P O o w t f q hrr dist keep).evaluatePlain D γ) u
            ∧ v = u (Fin.last n)}
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _, D => q.countValsAll D

omit [ValueType T] in
theorem Tuple.append_mem {V : Set T} {n₁ n₂ : ℕ} {u : Tuple T n₁} {v : Tuple T n₂}
    (hu : ∀ i, u i ∈ V) (hv : ∀ j, v j ∈ V) : ∀ i, (Fin.append u v : Tuple T (n₁ + n₂)) i ∈ V :=
  Fin.addCases (fun i => by rw [Fin.append_left]; exact hu i)
    (fun j => by rw [Fin.append_right]; exact hv j)

omit [ValueType T] in
theorem Tuple.snoc_mem {V : Set T} {n : ℕ} {u : Tuple T n} {x : T} (hu : ∀ i, u i ∈ V)
    (hx : x ∈ V) : ∀ i, (Fin.snoc u x : Tuple T (n + 1)) i ∈ V :=
  Fin.lastCases (by rw [Fin.snoc_last]; exact hx) (fun i => by rw [Fin.snoc_castSucc]; exact hu i)

/-- A function-free projection column reads a value it was given. -/
theorem ProjColIn.evalPlain_mem {W : Set T} {c k : ℕ} {κ : Fin k → ColKind} (p : ProjColIn T c κ)
    (hp : p.noFun = true) (hc : ∀ a ∈ p.consts, a ∈ W) {u : Tuple T k} (hu : ∀ j, u j ∈ W)
    {γ : Fin c → T} (hγ : ∀ j, γ j ∈ W) : p.evalPlain u γ ∈ W := by
  cases p with
  | term t => exact FaithfulOn.termGIn_evalPlain_mem t hp hc hu hγ
  | token j hj => exact hu j
  | aggTerm j hj gf => exact absurd hp (by simp [ProjColIn.noFun])
  | aggTermOf j hj t =>
    show t.unary (u j) ∈ W
    rw [TermIn.unary]
    exact FaithfulOn.termIn_eval_mem t hp hc (fun i => i.elim0) (fun _ => hu j)
  | provTerm t => exact FaithfulOn.termGIn_evalPlain_mem t hp hc hu hγ

/-- **Where every value of a result comes from**: the instance at the
relations the query reads (its holes included), the context, the query's
constants, or a count the query computes. No settling is asked: a
recursion's junk value is a sum of its rounds, which read like the
rest. -/
theorem AggQueryIn.valsIn_evaluatePlain {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig Θ → ∀ (D : Database T) (γ : Fin c → T) (V : Set T),
        (∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
          ∀ u, Multiset.Mem r u → ∀ j, u j ∈ V) →
        (∀ j, γ j ∈ V) → (∀ a ∈ q.allConsts, a ∈ V) → q.countValsAll D ⊆ V →
        ∀ u, Multiset.Mem (q.evaluatePlain D γ) u → ∀ j, u j ∈ V := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ D γ V hD _ _ _ u hu
    rw [AggQueryIn.evaluatePlain] at hu
    cases hf : D.find n s with
    | none => rw [hf] at hu; exact absurd (show u ∈ (∅ : Multiset (Tuple T n)) from hu) (by simp)
    | some rn => rw [hf] at hu; exact hD (n, s) (List.mem_singleton_self _) rn hf u hu
  | Hole n s =>
    intro _ D γ V hD _ _ _ u hu
    rw [AggQueryIn.evaluatePlain] at hu
    cases hf : D.find n s with
    | none => rw [hf] at hu; exact absurd (show u ∈ (∅ : Multiset (Tuple T n)) from hu) (by simp)
    | some rn => rw [hf] at hu; exact hD (n, s) (List.mem_singleton_self _) rn hf u hu
  | Empty =>
    intro _ _ _ _ _ _ _ _ u hu
    exact absurd (show u ∈ (0 : Multiset (Tuple T 0)) from hu) (by simp)
  | Proj ps q ih =>
    intro hs D γ V hD hγ hc hV u hu j
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
    exact (ps j).evalPlain_mem (hs.1 j)
      (fun a ha => hc a (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)))
      (ih hs.2 D γ V hD hγ (fun a ha => hc a (Finset.mem_union_right _ ha)) hV v hv) hγ
  | Sel φ q _ ih =>
    intro hs D γ V hD hγ hc hV u hu
    exact ih hs.2 D γ V hD hγ (fun a ha => hc a (Finset.mem_union_right _ ha)) hV u
      (Multiset.mem_of_mem_filter hu)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hs D γ V hD hγ hc hV u hu
    rw [AggQueryIn.evaluatePlain, Relation.hMul_eq_bind] at hu
    obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
    refine Tuple.append_mem
      (ih₁ hs.1 D γ V (fun p hp => hD p (List.mem_append_left _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_left _ ha))
        (subset_trans Set.subset_union_left hV) v hv)
      (ih₂ hs.2 D γ V (fun p hp => hD p (List.mem_append_right _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_right _ ha))
        (subset_trans Set.subset_union_right hV) w hw)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hs D γ V hD hγ hc hV u hu
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨v, hv, hu⟩ := Multiset.mem_bind.mp hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
    have hv' : ∀ j, v j ∈ V := ih₁ hs.1 D γ V (fun p hp => hD p (List.mem_append_left _ hp)) hγ
      (fun a ha => hc a (Finset.mem_union_left _ ha)) (subset_trans Set.subset_union_left hV) v hv
    exact Tuple.append_mem hv' (ih₂ hs.2 D (Fin.append v γ) V
      (fun p hp => hD p (List.mem_append_right _ hp)) (Tuple.append_mem hv' hγ)
      (fun a ha => hc a (Finset.mem_union_right _ ha)) (subset_trans Set.subset_union_right hV)
      w hw)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hs D γ V hD hγ hc hV u hu
    rw [AggQueryIn.evaluatePlain] at hu
    rcases Multiset.mem_add.mp hu with h | h
    · exact ih₁ hs.1 D γ V (fun p hp => hD p (List.mem_append_left _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_left _ ha)) (subset_trans Set.subset_union_left hV) u h
    · exact ih₂ hs.2 D γ V (fun p hp => hD p (List.mem_append_right _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_right _ ha)) (subset_trans Set.subset_union_right hV) u h
  | Dedup q ih =>
    intro hs D γ V hD hγ hc hV u hu
    exact ih hs D γ V hD hγ hc hV u (Multiset.mem_dedup.mp hu)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hs D γ V hD hγ hc hV u hu
    exact ih₁ hs.1 D γ V (fun p hp => hD p (List.mem_append_left _ hp)) hγ
      (fun a ha => hc a (Finset.mem_union_left _ ha)) (subset_trans Set.subset_union_left hV) u
      (Multiset.mem_of_mem_filter hu)
  | Alt k hk q ih => exact fun hs D γ V hD hγ hc hV u hu => ih hs D γ V hD hγ hc hV u hu
  | Retag hk q ih => exact fun hs D γ V hD hγ hc hV u hu => ih hs D γ V hD hγ hc hV u hu
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs D γ V hD hγ hc hV
    have hc₀ : ∀ a ∈ q₀.allConsts, a ∈ V := fun a ha => hc a (Finset.mem_union_left _ ha)
    have hc₁ : ∀ a ∈ q₁.allConsts, a ∈ V := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hV₀ : q₀.countValsAll D ⊆ V := subset_trans Set.subset_union_left hV
    -- the body, read with the name bound to a relation whose values are in `V`
    have hbody : ∀ X : Relation T m, (∀ u, Multiset.Mem X u → ∀ j, u j ∈ V) →
        ∀ u, Multiset.Mem (q₁.evaluatePlain (D.assign s X) γ) u → ∀ j, u j ∈ V := by
      intro X hX
      refine ih₁ hs.2 (D.assign s X) γ V ?_ hγ hc₁
        (subset_trans (Set.subset_iUnion (fun X => q₁.countValsAll (D.assign s X)) X)
          (subset_trans Set.subset_union_right hV))
      rintro ⟨k, t⟩ hp r hr
      by_cases hkt : k = m ∧ t = s
      · obtain ⟨rfl, rfl⟩ := hkt
        rw [Database.find_assign, Option.some.injEq] at hr
        rw [← hr]; exact hX
      · rw [Database.find_assign_of_ne s t _ D hkt] at hr
        refine hD (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, ?_⟩)) r hr
        exact decide_eq_true (fun h => hkt (Prod.mk.inj h))
    have hbase : ∀ u, Multiset.Mem (q₀.evaluatePlain D γ) u → ∀ j, u j ∈ V :=
      ih₀ hs.1 D γ V (fun p hp => hD p (List.mem_append_left _ hp)) hγ hc₀ hV₀
    have hiter : ∀ k (u : Tuple T m), Multiset.Mem ((fun X => q₁.evaluatePlain (D.assign s X) γ)^[k]
        (q₀.evaluatePlain D γ)) u → ∀ j, u j ∈ V := by
      intro k
      induction k with
      | zero => exact hbase
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hbody _ ih
    have hsum : ∀ (b : ℕ) (M : Multiset (Tuple T m)),
        (∀ k (u : Tuple T m), Multiset.Mem ((fun X => q₁.evaluatePlain (D.assign s X) γ)^[k] M) u →
          ∀ j, u j ∈ V) →
        ∀ u, u ∈ muSum (fun X => q₁.evaluatePlain (D.assign s X) γ) b M → ∀ j, u j ∈ V := by
      intro b
      induction b with
      | zero => exact fun M hM u hu => hM 0 u hu
      | succ b ih =>
        intro M hM u hu
        rw [muSum] at hu
        rcases Multiset.mem_add.mp hu with h | h
        · exact hM 0 u h
        · exact ih _ (fun k u hu => hM (k + 1) u (by rw [Function.iterate_succ_apply]; exact hu)) u h
    exact hsum _ _ hiter
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs D γ V hD hγ hc hV
    have hc₀ : ∀ a ∈ q₀.allConsts, a ∈ V := fun a ha => hc a (Finset.mem_union_left _ ha)
    have hc₁ : ∀ a ∈ q₁.allConsts, a ∈ V := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hV₀ : q₀.countValsAll D ⊆ V := subset_trans Set.subset_union_left hV
    have hbody : ∀ X : Relation T m, (∀ u, Multiset.Mem X u → ∀ j, u j ∈ V) →
        ∀ u, Multiset.Mem (q₁.evaluatePlain (D.assign s X) γ) u → ∀ j, u j ∈ V := by
      intro X hX
      refine ih₁ hs.2 (D.assign s X) γ V ?_ hγ hc₁
        (subset_trans (Set.subset_iUnion (fun X => q₁.countValsAll (D.assign s X)) X)
          (subset_trans Set.subset_union_right hV))
      rintro ⟨k, t⟩ hp r hr
      by_cases hkt : k = m ∧ t = s
      · obtain ⟨rfl, rfl⟩ := hkt
        rw [Database.find_assign, Option.some.injEq] at hr
        rw [← hr]; exact hX
      · rw [Database.find_assign_of_ne s t _ D hkt] at hr
        refine hD (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, ?_⟩)) r hr
        exact decide_eq_true (fun h => hkt (Prod.mk.inj h))
    have hbase : ∀ u, Multiset.Mem (q₀.evaluatePlain D γ) u → ∀ j, u j ∈ V :=
      ih₀ hs.1 D γ V (fun p hp => hD p (List.mem_append_left _ hp)) hγ hc₀ hV₀
    have hiter : ∀ k (u : Tuple T m), u ∈ muIter (fun X : Multiset (Tuple T m) =>
        (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup) k → ∀ j, u j ∈ V := by
      intro k
      induction k with
      | zero => exact fun u hu => absurd hu (Multiset.notMem_zero u)
      | succ k ih =>
        intro u hu
        rw [muIter] at hu
        rcases Multiset.mem_add.mp (Multiset.mem_dedup.mp hu) with h | h
        · exact hbase u h
        · exact hbody _ ih u h
    exact hiter _
  | Gamma is ts fs q keep ord ih =>
    intro hs D γ V hD hγ hc hV u hu
    have hu0 := hu
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
    rw [Multiset.mem_dedup] at hgg
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
    have hvV : ∀ i, v i ∈ V := ih hs.2.2.2 D γ V hD hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha)) (subset_trans Set.subset_union_left hV) v hv
    exact Tuple.append_mem (fun i => hvV (is i))
      (fun j => hV (Set.mem_union_right _ ⟨γ, _, hu0, j, by rw [Fin.append_right]⟩))
  | GammaScalar ts fs q ord ih =>
    intro hs D γ V hD hγ hc hV u hu j
    exact hV (Set.mem_union_right _ ⟨γ, u, hu, j, rfl⟩)
  | GammaNest is his p f q ih =>
    intro hs D γ V hD hγ hc hV u hu
    have hu0 := hu
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨gg, hgg, rfl⟩ := Multiset.mem_map.mp hu
    rw [Multiset.mem_dedup] at hgg
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hgg
    have hvV : ∀ i, v i ∈ V := ih hs.2.2 D γ V hD hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha)) (subset_trans Set.subset_union_left hV) v hv
    refine Tuple.append_mem (fun i => hvV (is i)) (fun j => ?_)
    have h0 : j = 0 := Subsingleton.elim j 0
    subst h0
    exact hV (Set.mem_union_right _ ⟨γ, _, hu0, by rw [Fin.append_right]⟩)
  | ProvSum is his t q ih => exact fun hs => hs.elim
  | GammaTok is his ts fs a q keep ih => exact fun hs => hs.elim
  | Win P O o w t f q hrr dist keep ih =>
    intro hs D γ V hD hγ hc hV u hu
    have hu0 := hu
    rw [AggQueryIn.evaluatePlain] at hu
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hu
    have hvV : ∀ i, v i ∈ V := ih hs.2.2.2 D γ V hD hγ
      (fun a ha => hc a (Finset.mem_union_right _ ha)) (subset_trans Set.subset_union_left hV) v hv
    exact Tuple.snoc_mem hvV (hV (Set.mem_union_right _ ⟨γ, _, hu0, by rw [Fin.snoc_last]⟩))
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hs => hs.elim

/-! ## A query commutes with a faithful map

A map that is faithful on the values a query reads, fixes its constants
and fixes the counts it computes commutes with its evaluation: the
result on the mapped instance in the mapped context is the mapped
result. The counts have to be fixed because the query recomputes them –
a count is the number of non-null values read, which the map preserves,
so the mapped result holds the count and not its image. Nothing is asked
of the recursions: their rounds correspond one by one, settling or
not. -/

omit [ValueType T] in
theorem Tuple.comp_append (τ : T → T) {n₁ n₂ : ℕ} (u : Tuple T n₁) (v : Tuple T n₂) :
    (τ ∘ Fin.append u v : Tuple T (n₁ + n₂)) = Fin.append (τ ∘ u) (τ ∘ v) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · show τ (Fin.append u v (Fin.castAdd n₂ i)) = Fin.append (τ ∘ u) (τ ∘ v) (Fin.castAdd n₂ i)
    rw [Fin.append_left, Fin.append_left]; rfl
  · show τ (Fin.append u v (Fin.natAdd n₁ j)) = Fin.append (τ ∘ u) (τ ∘ v) (Fin.natAdd n₁ j)
    rw [Fin.append_right, Fin.append_right]; rfl

/-- Reading a mapped row's regular columns is mapping the read row, the
map fixing the zero the aggregate columns are read as. -/
theorem ColKind.readTuple_comp {n : ℕ} (κ : Fin n → ColKind) {τ : T → T} (h0 : τ 0 = 0)
    (u : Tuple T n) : ColKind.readTuple κ (τ ∘ u) = τ ∘ ColKind.readTuple κ u := by
  funext k
  show (match (κ k).base with | ColKind.agg => 0 | _ => τ (u k))
    = τ (match (κ k).base with | ColKind.agg => 0 | _ => u k)
  cases (κ k).base <;> simp [h0]

/-- A count over a bag of values the map preserves nulls on reads alike. -/
theorem SeqAggFunc.IsCount.onBag_map {cnt : SeqAggFunc T} (hc : cnt.IsCount)
    (hsym : cnt.Symmetric) {τ : T → T} {W : Set T} (h : FaithfulOn τ W) {M : Multiset T}
    (hM : ∀ a ∈ M, a ∈ W) : cnt.onBag hsym (M.map τ) = cnt.onBag hsym M := by
  induction M using Quot.inductionOn with
  | h L =>
    show cnt.onBag hsym ((L : Multiset T).map τ) = cnt.onBag hsym (L : Multiset T)
    rw [Multiset.map_coe, SeqAggFunc.onBag_coe, SeqAggFunc.onBag_coe]
    obtain ⟨g, hg⟩ := hc
    rw [hg, hg]
    congr 1
    rw [List.countP_map]
    exact List.countP_congr (fun a ha => by
      simp [Function.comp, h.isNull a (hM a (Multiset.mem_coe.mpr ha))])

namespace FaithfulOn

variable {τ : T → T} {W : Set T}

/-- Mapping the rows of two relations over `W` is injective. -/
theorem map_tuple_inj (h : FaithfulOn τ W) {n : ℕ} {X Y : Multiset (Tuple T n)}
    (hX : ∀ u ∈ X, ∀ j, u j ∈ W) (hY : ∀ u ∈ Y, ∀ j, u j ∈ W) :
    X.map (fun u => (τ ∘ u : Tuple T n)) = Y.map (fun u => (τ ∘ u : Tuple T n)) ↔ X = Y := by
  refine ⟨fun he => ?_, fun he => by rw [he]⟩
  classical
  have : Nonempty T := ⟨0⟩
  have hinv : ∀ a ∈ W, Function.invFunOn τ W (τ a) = a :=
    fun a ha => h.injOn.leftInvOn_invFunOn ha
  have hback : ∀ (Z : Multiset (Tuple T n)), (∀ u ∈ Z, ∀ j, u j ∈ W) →
      (Z.map (fun u => (τ ∘ u : Tuple T n))).map (fun v => (Function.invFunOn τ W ∘ v : Tuple T n))
        = Z := by
    intro Z hZ
    rw [Multiset.map_map]
    refine Eq.trans (Multiset.map_congr rfl (fun u hu => ?_)) (Multiset.map_id Z)
    funext j
    exact hinv (u j) (hZ u hu j)
  rw [← hback X hX, ← hback Y hY, he]

/-- The key columns of a mapped row are the mapped key columns. -/
theorem filter_key_map' (h : FaithfulOn τ W) {m n₁ : ℕ} (is : Tuple (Fin m) n₁)
    {r : Multiset (Tuple T m)} (hr : ∀ u ∈ r, ∀ j, u j ∈ W) {g : Tuple T n₁}
    (hg : ∀ k, g k ∈ W) :
    (r.map (fun u => (τ ∘ u : Tuple T m))).filter
        (fun u => (fun k => u (is k) : Tuple T n₁) = (τ ∘ g : Tuple T n₁))
      = (r.filter (fun u => (fun k => u (is k) : Tuple T n₁) = g)).map
          (fun u => (τ ∘ u : Tuple T m)) := by
  have e₁ : (r.map (fun u => (τ ∘ u : Tuple T m))).filter
        (fun u => (fun k => u (is k) : Tuple T n₁) = (τ ∘ g : Tuple T n₁))
      = (r.map (fun u => (τ ∘ u : Tuple T m))).filter
        (fun u => ∀ k' : Fin n₁, u (is k') = (τ ∘ g : Tuple T n₁) k') :=
    Multiset.filter_congr (fun u _ => funext_iff)
  have e₂ : r.filter (fun u => (fun k => u (is k) : Tuple T n₁) = g)
      = r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k') :=
    Multiset.filter_congr (fun u _ => funext_iff)
  rw [e₁, e₂, h.filter_key_map is hr hg]

/-- The keys of a mapped relation are the mapped keys. -/
theorem keys_map (h : FaithfulOn τ W) {m n₁ : ℕ} [DecidableEq (Tuple T n₁)]
    (is : Tuple (Fin m) n₁) {r : Multiset (Tuple T m)} (hr : ∀ u ∈ r, ∀ j, u j ∈ W) :
    ((r.map (fun u => (τ ∘ u : Tuple T m))).map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup
      = ((r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup).map
          (fun g => (τ ∘ g : Tuple T n₁)) := by
  have hinj := Multiset.dedup_map_of_injOn (s := r.map (fun u => (fun k => u (is k) : Tuple T n₁)))
    (f := fun g => (τ ∘ g : Tuple T n₁)) (fun x hx y hy hxy => by
      obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.mp hy
      exact (h.row_eq_iff (fun k => hr x' hx' (is k)) (fun k => hr y' hy' (is k))).mp hxy)
  rw [← hinj, Multiset.map_map, Multiset.map_map]
  rfl

omit [ValueType T] in
/-- A key of a relation over `W` is over `W`. -/
theorem keys_mem_of_mem_dedup {m n₁ : ℕ} [DecidableEq (Tuple T n₁)] (is : Tuple (Fin m) n₁)
    {r : Multiset (Tuple T m)}
    (hr : ∀ u ∈ r, ∀ j, u j ∈ W) {g : Tuple T n₁}
    (hg : g ∈ (r.map (fun u => (fun k => u (is k) : Tuple T n₁))).dedup) : ∀ k, g k ∈ W := by
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hg)
  exact fun k => hr x hx (is k)

end FaithfulOn

/-- **The values of a recursion's body, read with its name bound**: those
of the instance at its other leaves, of the bound relation, of the
context, of its constants, or counts. -/
theorem AggQueryIn.valsIn_evaluatePlain_assign {Θ : Set (SeqAggFunc T)} {c m : ℕ} (s : String)
    {l : List (String × ℕ)} (q₁ : AggQueryIn T c m (ColKind.allReg m) l) (hs : q₁.inSig Θ)
    (D : Database T) (γ : Fin c → T) (V : Set T)
    (hD : ∀ p ∈ q₁.leaves, p ≠ (m, s) → ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
      ∀ u, Multiset.Mem r u → ∀ j, u j ∈ V)
    (hγ : ∀ j, γ j ∈ V) (hc : ∀ a ∈ q₁.allConsts, a ∈ V) (X : Relation T m)
    (hV : q₁.countValsAll (D.assign s X) ⊆ V) (hX : ∀ u, Multiset.Mem X u → ∀ j, u j ∈ V) :
    ∀ u, Multiset.Mem (q₁.evaluatePlain (D.assign s X) γ) u → ∀ j, u j ∈ V := by
  refine AggQueryIn.valsIn_evaluatePlain q₁ hs (D.assign s X) γ V ?_ hγ hc hV
  rintro ⟨k, t⟩ hp r hr
  by_cases hkt : k = m ∧ t = s
  · obtain ⟨rfl, rfl⟩ := hkt
    rw [Database.find_assign, Option.some.injEq] at hr
    rw [← hr]; exact hX
  · rw [Database.find_assign_of_ne s t _ D hkt] at hr
    exact hD (k, t) hp (fun h => hkt (Prod.mk.inj h)) r hr

namespace FaithfulOn

variable {τ : T → T} {W : Set T}

/-- **A grouping of a mapped relation**: the mapped keys, each with the
counts of its group, which the map preserves. -/
theorem gamma_map (h : FaithfulOn τ W) {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {c m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (hfs : ∀ j, fs j = cnt) (hts : ∀ j, (ts j).noFun = true)
    (hcts : ∀ j, ∀ a ∈ (ts j).consts, τ a = a ∧ a ∈ W)
    (keep : Fin n₂ → Option (Selection T m)) (hk : ∀ j, Selection.noFunOpt (keep j) = true)
    (hck : ∀ j, ∀ a ∈ Selection.constsOpt (keep j), τ a = a ∧ a ∈ W) (ord : GroupOrder T m)
    (q : AggQueryIn T c m (ColKind.allReg m)) (D D' : Database T) {γ : Fin c → T}
    (hγ : ∀ j, γ j ∈ W) (hvals : ∀ u, Multiset.Mem (q.evaluatePlain D γ) u → ∀ j, u j ∈ W)
    (hr : (q.evaluatePlain D' (τ ∘ γ) : Multiset (Tuple T m))
      = (q.evaluatePlain D γ : Multiset (Tuple T m)).map (fun u => (τ ∘ u : Tuple T m))) :
    ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain D' (τ ∘ γ)
        : Multiset (Tuple T (n₁ + n₂)))
      = ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain D γ
          : Multiset (Tuple T (n₁ + n₂))).map
          (fun u => Fin.append (τ ∘ (fun i => u (Fin.castAdd n₂ i)) : Tuple T n₁)
            (fun j => u (Fin.natAdd n₁ j))) := by
  simp only [AggQueryIn.evaluatePlain]
  rw [hr]
  erw [h.keys_map is hvals]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun g hg => ?_)
  have hgW : ∀ k, g k ∈ W := FaithfulOn.keys_mem_of_mem_dedup is hvals hg
  show Fin.append (τ ∘ g) _ = Fin.append (τ ∘ (fun i => Fin.append g _ (Fin.castAdd n₂ i)))
    (fun j => Fin.append g _ (Fin.natAdd n₁ j))
  refine congrArg₂ Fin.append ?_ ?_
  · funext i
    show τ (g i) = τ (Fin.append g _ (Fin.castAdd n₂ i))
    rw [Fin.append_left]
  · funext j
    rw [Fin.append_right]
    show fs j _ = fs j _
    rw [hfs j]
    beta_reduce
    refine hcnt.eq_of_nonNullCount (ts j) (τ ∘ γ) γ ?_
    erw [Relation.groupSeqOptOrd_coe, Relation.groupSeqOptOrd_coe, h.filter_key_map is hvals hgW,
      h.filter_keeps_map (keep j) (hk j) (hck j)
        (fun u hu => hvals u (Multiset.mem_of_mem_filter hu)),
      h.nonNullCount_map (ts j) (hts j) (hcts j) hγ
        (fun u hu => hvals u (Multiset.mem_of_mem_filter (Multiset.mem_of_mem_filter hu)))]

/-- **A scalar aggregation of a mapped relation** is the same row: it holds
counts only. -/
theorem gammaScalar_map (h : FaithfulOn τ W) {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {c m n₂ : ℕ} (ts : Tuple (TermIn T c m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (hfs : ∀ j, fs j = cnt) (hts : ∀ j, (ts j).noFun = true)
    (hcts : ∀ j, ∀ a ∈ (ts j).consts, τ a = a ∧ a ∈ W) (ord : GroupOrder T m)
    (q : AggQueryIn T c m (ColKind.allReg m)) (D D' : Database T) {γ : Fin c → T}
    (hγ : ∀ j, γ j ∈ W) (hvals : ∀ u, Multiset.Mem (q.evaluatePlain D γ) u → ∀ j, u j ∈ W)
    (hr : (q.evaluatePlain D' (τ ∘ γ) : Multiset (Tuple T m))
      = (q.evaluatePlain D γ : Multiset (Tuple T m)).map (fun u => (τ ∘ u : Tuple T m))) :
    (AggQueryIn.GammaScalar ts fs q ord).evaluatePlain D' (τ ∘ γ)
      = (AggQueryIn.GammaScalar ts fs q ord).evaluatePlain D γ := by
  have hvac : ∀ (S : Multiset (Tuple T m)) (P : Tuple T m → Fin 0 → Prop)
      [DecidablePred fun u => ∀ k', P u k'], S.filter (fun u => ∀ k', P u k') = S :=
    fun S P _ => Multiset.filter_eq_self.mpr (fun u _ k' => k'.elim0)
  simp only [AggQueryIn.evaluatePlain]
  rw [hr]
  refine congrArg (fun x : Tuple T n₂ => (↑[x] : Multiset (Tuple T n₂))) ?_
  funext j
  show fs j _ = fs j _
  rw [hfs j]
  refine hcnt.eq_of_nonNullCount (ts j) (τ ∘ γ) γ ?_
  erw [← Relation.groupSeqOptOrd_none, ← Relation.groupSeqOptOrd_none,
    Relation.groupSeqOptOrd_coe, Relation.groupSeqOptOrd_coe, hvac, hvac,
    h.filter_keeps_map none rfl (fun a ha => absurd ha (by simp [Selection.constsOpt])) hvals,
    h.nonNullCount_map (ts j) (hts j) (hcts j) hγ
      (fun u hu => hvals u (Multiset.mem_of_mem_filter hu))]

/-- **A second-level aggregation of a mapped relation**, its aggregate a
count: the mapped keys with the same counts. -/
theorem gammaNest_map (h : FaithfulOn τ W) {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {c m n₁ : ℕ} {κ : Fin m → ColKind} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (p : ProjColIn T c κ) (hp : p.noFun = true) (hcp : ∀ a ∈ p.consts, τ a = a ∧ a ∈ W)
    (hsym : cnt.Symmetric) (q : AggQueryIn T c m κ) (D D' : Database T) {γ : Fin c → T}
    (hγ : ∀ j, γ j ∈ W) (hvals : ∀ u, Multiset.Mem (q.evaluatePlain D γ) u → ∀ j, u j ∈ W)
    (hr : (q.evaluatePlain D' (τ ∘ γ) : Multiset (Tuple T m))
      = (q.evaluatePlain D γ : Multiset (Tuple T m)).map (fun u => (τ ∘ u : Tuple T m))) :
    ((AggQueryIn.GammaNest is his p (cnt.onBag hsym) q).evaluatePlain D' (τ ∘ γ)
        : Multiset (Tuple T (n₁ + 1)))
      = ((AggQueryIn.GammaNest is his p (cnt.onBag hsym) q).evaluatePlain D γ
          : Multiset (Tuple T (n₁ + 1))).map
          (fun u => Fin.append (τ ∘ (fun i => u (Fin.castAdd 1 i)) : Tuple T n₁)
            (fun j => u (Fin.natAdd n₁ j))) := by
  simp only [AggQueryIn.evaluatePlain]
  rw [hr]
  erw [h.keys_map is hvals]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun g hg => ?_)
  have hgW : ∀ k, g k ∈ W := FaithfulOn.keys_mem_of_mem_dedup is hvals hg
  show Fin.append (τ ∘ g) _ = Fin.append (τ ∘ (fun i => Fin.append g _ (Fin.castAdd 1 i)))
    (fun j => Fin.append g _ (Fin.natAdd n₁ j))
  refine congrArg₂ Fin.append ?_ ?_
  · funext i
    show τ (g i) = τ (Fin.append g _ (Fin.castAdd 1 i))
    rw [Fin.append_left]
  · funext j
    rw [Fin.append_right]
    show cnt.onBag hsym _ = cnt.onBag hsym _
    beta_reduce
    erw [h.filter_key_map' is hvals hgW, Multiset.map_map]
    have hbag : ((q.evaluatePlain D γ : Multiset (Tuple T m)).filter
          (fun u => (fun k => u (is k) : Tuple T n₁) = g)).map
            ((fun u => p.evalPlain u (τ ∘ γ)) ∘ (fun u => (τ ∘ u : Tuple T m)))
        = (((q.evaluatePlain D γ : Multiset (Tuple T m)).filter
          (fun u => (fun k => u (is k) : Tuple T n₁) = g)).map (fun u => p.evalPlain u γ)).map τ := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl (fun u _ =>
        FaithfulOn.projColIn_evalPlain p hp (fun a ha => (hcp a ha).1) u γ)
    rw [hbag]
    refine hcnt.onBag_map hsym h (fun a ha => ?_)
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp ha
    exact ProjColIn.evalPlain_mem p hp (fun a ha => (hcp a ha).2)
      (hvals u (Multiset.mem_of_mem_filter hu)) hγ

/-- **A window over a mapped relation**, its aggregate a count: the mapped
rows, each with the count of its frame. -/
theorem win_map (h : FaithfulOn τ W) {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) (h0 : τ 0 = 0)
    (h0W : (0 : T) ∈ W) {c n m p : ℕ} {κ : Fin n → ColKind} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    (ht : t.noFun = true) (hct : ∀ a ∈ t.consts, τ a = a ∧ a ∈ W) (f : SeqAggFunc T)
    {dist : Bool} (hfc : (if dist then f.distinct else f) = cnt) (keep : Option (Selection T n))
    (hk : Selection.noFunOpt keep = true) (hck : ∀ a ∈ Selection.constsOpt keep, τ a = a ∧ a ∈ W)
    (q : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t)
    (D D' : Database T) {γ : Fin c → T} (hγ : ∀ j, γ j ∈ W)
    (hvals : ∀ u, Multiset.Mem (q.evaluatePlain D γ) u → ∀ j, u j ∈ W)
    (hr : (q.evaluatePlain D' (τ ∘ γ) : Multiset (Tuple T n))
      = (q.evaluatePlain D γ : Multiset (Tuple T n)).map (fun u => (τ ∘ u : Tuple T n))) :
    ((AggQueryIn.Win P O o w t f q hrr dist keep).evaluatePlain D' (τ ∘ γ)
        : Multiset (Tuple T (n + 1)))
      = ((AggQueryIn.Win P O o w t f q hrr dist keep).evaluatePlain D γ
          : Multiset (Tuple T (n + 1))).map
          (fun u => Fin.snoc (τ ∘ Fin.init u : Tuple T n) (u (Fin.last n))) := by
  have hXW : ∀ v ∈ (q.evaluatePlain D γ : Multiset (Tuple T n)).map (ColKind.readTuple κ),
      ∀ j, v j ∈ W := by
    intro v hv j
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hv
    show (match (κ j).base with | ColKind.agg => 0 | _ => x j) ∈ W
    cases (κ j).base <;> simp [h0W, hvals x hx j]
  have hread' : (q.evaluatePlain D γ : Multiset (Tuple T n)).map
        (fun x => ColKind.readTuple κ (τ ∘ x : Tuple T n))
      = ((q.evaluatePlain D γ : Multiset (Tuple T n)).map (ColKind.readTuple κ)).map
          (fun u => (τ ∘ u : Tuple T n)) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ => ColKind.readTuple_comp κ h0 u)
  simp only [AggQueryIn.evaluatePlain]
  rw [hr]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl (fun u hu => ?_)
  simp only [Function.comp_apply, Fin.init_snoc, Fin.snoc_last]
  congr 1
  rw [hfc, ColKind.readTuple_comp κ h0 u]
  erw [hread']
  have hxW : ∀ j, ColKind.readTuple κ u j ∈ W := hXW _ (Multiset.mem_map.mpr ⟨u, hu, rfl⟩)
  have key := h.frame_nonNullCount P O o w t ht hct keep hk hck hXW hxW hγ
  cases keep with
  | none =>
    rw [ValueFrame.windowValueOpt_none, ValueFrame.windowValueOpt_none, ValueFrame.windowValue,
      ValueFrame.windowValue]
    refine hcnt.eq_of_nonNullCount t (τ ∘ γ) γ ?_
    have e : ∀ L : List (Tuple T n), L.filter (fun u => Selection.keepsOpt none u = true) = L :=
      fun L => List.filter_eq_self.mpr (fun a _ => by simp [Selection.keepsOpt])
    rw [e, e] at key
    exact key
  | some φ =>
    rw [ValueFrame.windowValueOpt_some, ValueFrame.windowValueOpt_some,
      ValueFrame.windowValueWhen, ValueFrame.windowValueWhen]
    refine hcnt.eq_of_nonNullCount t (τ ∘ γ) γ ?_
    have e : ∀ L : List (Tuple T n), L.filter (fun u => Selection.keepsOpt (some φ) u = true)
        = L.filter φ.keeps :=
      fun L => List.filter_congr (fun a _ => by simp [Selection.keepsOpt])
    rw [e, e] at key
    exact key

end FaithfulOn

/-- **A query of the minimal signature commutes with a faithful map**
that fixes its constants and its counts: on an instance whose relations
at the query's leaves are the mapped ones, in the mapped context, it
returns the mapped result. -/
theorem AggQueryIn.evaluatePlain_faithful {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig {cnt} → ∀ {τ : T → T} {W : Set T}, FaithfulOn τ W → τ 0 = 0 → (0 : T) ∈ W →
      ∀ (D D' : Database T) (γ : Fin c → T),
        (∀ p ∈ q.leaves, D'.find p.1 p.2 = (D.find p.1 p.2).map (Relation.mapVals τ)) →
        (∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
          ∀ u, Multiset.Mem r u → ∀ j, u j ∈ W) →
        (∀ j, γ j ∈ W) → (∀ a ∈ q.allConsts, τ a = a ∧ a ∈ W) →
        (∀ v ∈ q.countValsAll D, τ v = v ∧ v ∈ W) →
        (q.evaluatePlain D' (τ ∘ γ) : Multiset (Tuple T n))
          = (q.evaluatePlain D γ : Multiset (Tuple T n)).map (fun u => (τ ∘ u : Tuple T n)) := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hf := hD' (n, s) (List.mem_singleton_self _)
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    cases hf0 : D.find n s with
    | none =>
      rw [hf0, Option.map_none] at hf
      rw [hf]
      exact (Multiset.map_zero _).symm
    | some rn =>
      rw [hf0, Option.map_some] at hf
      rw [hf]
      rfl
  | Hole n s =>
    intro _ τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hf := hD' (n, s) (List.mem_singleton_self _)
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    cases hf0 : D.find n s with
    | none =>
      rw [hf0, Option.map_none] at hf
      rw [hf]
      exact (Multiset.map_zero _).symm
    | some rn =>
      rw [hf0, Option.map_some] at hf
      rw [hf]
      rfl
  | Empty =>
    intro _ τ W h h0 h0W D D' γ hD' hD hγ hc hV
    exact (Multiset.map_zero _).symm
  | Proj ps q ih =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    simp only [AggQueryIn.evaluatePlain]
    rw [ih hs.2 h h0 h0W D D' γ hD' hD hγ (fun a ha => hc a (Finset.mem_union_right _ ha)) hV,
      Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    funext j
    exact FaithfulOn.projColIn_evalPlain (ps j) (hs.1 j)
      (fun a ha => (hc a (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩))).1) v γ
  | Sel φ q _ ih =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hvals := AggQueryIn.valsIn_evaluatePlain q hs.2 D γ W hD hγ
      (fun a ha => (hc a (Finset.mem_union_right _ ha)).2) (fun v hv => (hV v hv).2)
    simp only [AggQueryIn.evaluatePlain]
    rw [ih hs.2 h h0 h0W D D' γ hD' hD hγ (fun a ha => hc a (Finset.mem_union_right _ ha)) hV,
      Multiset.filter_map]
    congr 1
    exact Multiset.filter_congr (fun u hu => h.genPredIn_holdsPlain φ hs.1
      (fun a ha => hc a (Finset.mem_union_left _ ha)) (hvals u hu) hγ)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain, Relation.hMul_eq_bind,
      Relation.hMul_eq_bind,
      ih₁ hs.1 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_left _ hp))
        (fun p hp => hD p (List.mem_append_left _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_left _ ha)) (fun v hv => hV v (Set.mem_union_left _ hv)),
      ih₂ hs.2 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_right _ hp))
        (fun p hp => hD p (List.mem_append_right _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_right _ ha))
        (fun v hv => hV v (Set.mem_union_right _ hv)),
      Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun a _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    exact (Tuple.comp_append τ a v).symm
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hvals := AggQueryIn.valsIn_evaluatePlain q₁ hs.1 D γ W
      (fun p hp => hD p (List.mem_append_left _ hp)) hγ
      (fun a ha => (hc a (Finset.mem_union_left _ ha)).2)
      (fun v hv => (hV v (Set.mem_union_left _ hv)).2)
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain,
      ih₁ hs.1 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_left _ hp))
        (fun p hp => hD p (List.mem_append_left _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_left _ ha)) (fun v hv => hV v (Set.mem_union_left _ hv)),
      Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun u hu => ?_)
    rw [← Tuple.comp_append τ u γ,
      ih₂ hs.2 h h0 h0W D D' (Fin.append u γ) (fun p hp => hD' p (List.mem_append_right _ hp))
        (fun p hp => hD p (List.mem_append_right _ hp)) (Tuple.append_mem (hvals u hu) hγ)
        (fun a ha => hc a (Finset.mem_union_right _ ha))
        (fun v hv => hV v (Set.mem_union_right _ hv)),
      Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    exact (Tuple.comp_append τ u v).symm
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain]
    show _ + _ = Multiset.map _ (_ + _)
    rw [Multiset.map_add,
      ih₁ hs.1 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_left _ hp))
        (fun p hp => hD p (List.mem_append_left _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_left _ ha)) (fun v hv => hV v (Set.mem_union_left _ hv)),
      ih₂ hs.2 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_right _ hp))
        (fun p hp => hD p (List.mem_append_right _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_right _ ha))
        (fun v hv => hV v (Set.mem_union_right _ hv))]
  | Dedup q ih =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hvals := AggQueryIn.valsIn_evaluatePlain q hs D γ W hD hγ
      (fun a ha => (hc a ha).2) (fun v hv => (hV v hv).2)
    rw [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain, ih hs h h0 h0W D D' γ hD' hD hγ hc hV]
    exact Multiset.dedup_map_of_injOn (fun x hx y hy hxy =>
      (h.row_eq_iff (hvals x hx) (hvals y hy)).mp hxy)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hvals₁ := AggQueryIn.valsIn_evaluatePlain q₁ hs.1 D γ W
      (fun p hp => hD p (List.mem_append_left _ hp)) hγ
      (fun a ha => (hc a (Finset.mem_union_left _ ha)).2)
      (fun v hv => (hV v (Set.mem_union_left _ hv)).2)
    have hvals₂ := AggQueryIn.valsIn_evaluatePlain q₂ hs.2 D γ W
      (fun p hp => hD p (List.mem_append_right _ hp)) hγ
      (fun a ha => (hc a (Finset.mem_union_right _ ha)).2)
      (fun v hv => (hV v (Set.mem_union_right _ hv)).2)
    simp only [AggQueryIn.evaluatePlain]
    rw [ih₁ hs.1 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_left _ hp))
        (fun p hp => hD p (List.mem_append_left _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_left _ ha)) (fun v hv => hV v (Set.mem_union_left _ hv)),
      ih₂ hs.2 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_right _ hp))
        (fun p hp => hD p (List.mem_append_right _ hp)) hγ
        (fun a ha => hc a (Finset.mem_union_right _ ha))
        (fun v hv => hV v (Set.mem_union_right _ hv)),
      Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr (fun u hu => ?_)
    show (τ ∘ u : Tuple T _) ∉ Multiset.map _ _ ↔ u ∉ _
    rw [not_iff_not, Multiset.mem_map]
    constructor
    · rintro ⟨v, hv, hvu⟩
      rw [(h.row_eq_iff (hvals₂ v hv) (hvals₁ u hu)).mp hvu] at hv
      exact hv
    · exact fun hu' => ⟨u, hu', rfl⟩
  | Alt k hk q ih =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    exact ih hs h h0 h0W D D' γ hD' hD hγ hc hV
  | Retag hk q ih =>
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    exact ih hs h h0 h0W D D' γ hD' hD hγ hc hV
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hc₀ : ∀ a ∈ q₀.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_left _ ha)
    have hc₁ : ∀ a ∈ q₁.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hV₀ : ∀ v ∈ q₀.countValsAll D, τ v = v ∧ v ∈ W :=
      fun v hv => hV v (Set.mem_union_left _ hv)
    have hV₁ : ∀ X : Relation T m, ∀ v ∈ q₁.countValsAll (D.assign s X), τ v = v ∧ v ∈ W :=
      fun X v hv => hV v (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨X, hv⟩))
    have hDm : ∀ p ∈ q₁.leaves, p ≠ (m, s) → ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ W := fun p hp hne => hD p
      (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
    -- the body on a round whose values are in `W`, and its values
    have hbody : ∀ X : Relation T m, (∀ u, Multiset.Mem X u → ∀ j, u j ∈ W) →
        (q₁.evaluatePlain (D'.assign s (Relation.mapVals τ X)) (τ ∘ γ) : Multiset (Tuple T m))
          = (q₁.evaluatePlain (D.assign s X) γ : Multiset (Tuple T m)).map
              (fun u => (τ ∘ u : Tuple T m)) := by
      intro X hX
      refine ih₁ hs.2 h h0 h0W (D.assign s X) (D'.assign s (Relation.mapVals τ X)) γ ?_ ?_ hγ hc₁
        (hV₁ X)
      · rintro ⟨k, t⟩ hp
        by_cases hkt : k = m ∧ t = s
        · obtain ⟨rfl, rfl⟩ := hkt
          rw [Database.find_assign, Database.find_assign, Option.map_some]
        · rw [Database.find_assign_of_ne s t _ D hkt, Database.find_assign_of_ne s t _ D' hkt]
          exact hD' (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp,
            decide_eq_true (fun h => hkt (Prod.mk.inj h))⟩))
      · rintro ⟨k, t⟩ hp r hr
        by_cases hkt : k = m ∧ t = s
        · obtain ⟨rfl, rfl⟩ := hkt
          rw [Database.find_assign, Option.some.injEq] at hr
          rw [← hr]; exact hX
        · rw [Database.find_assign_of_ne s t _ D hkt] at hr
          exact hDm (k, t) hp (fun h => hkt (Prod.mk.inj h)) r hr
    have hbodyV : ∀ X : Relation T m, (∀ u, Multiset.Mem X u → ∀ j, u j ∈ W) →
        ∀ u, Multiset.Mem (q₁.evaluatePlain (D.assign s X) γ) u → ∀ j, u j ∈ W :=
      fun X hX => AggQueryIn.valsIn_evaluatePlain_assign s q₁ hs.2 D γ W hDm hγ
        (fun a ha => (hc₁ a ha).2) X (fun v hv => (hV₁ X v hv).2) hX
    have hM := ih₀ hs.1 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_left _ hp))
      (fun p hp => hD p (List.mem_append_left _ hp)) hγ hc₀ hV₀
    have hMV := AggQueryIn.valsIn_evaluatePlain q₀ hs.1 D γ W
      (fun p hp => hD p (List.mem_append_left _ hp)) hγ (fun a ha => (hc₀ a ha).2)
      (fun v hv => (hV₀ v hv).2)
    -- the rounds correspond
    set step : Multiset (Tuple T m) → Multiset (Tuple T m) :=
      fun X => q₁.evaluatePlain (D.assign s X) γ with hstep
    set step' : Multiset (Tuple T m) → Multiset (Tuple T m) :=
      fun X => q₁.evaluatePlain (D'.assign s X) (τ ∘ γ) with hstep'
    set M : Multiset (Tuple T m) := q₀.evaluatePlain D γ with hMdef
    have hiterV : ∀ k, ∀ u ∈ step^[k] M, ∀ j, u j ∈ W := by
      intro k
      induction k with
      | zero => exact hMV
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hbodyV _ ih
    have hiter : ∀ k, step'^[k] (M.map (fun u => (τ ∘ u : Tuple T m)))
        = (step^[k] M).map (fun u => (τ ∘ u : Tuple T m)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        exact hbody _ (hiterV k)
    have hrounds : muRounds step' (M.map (fun u => (τ ∘ u : Tuple T m))) = muRounds step M := by
      unfold muRounds
      congr 1
      ext k
      show step'^[k + 1] _ = 0 ↔ step^[k + 1] M = 0
      rw [hiter, Multiset.map_eq_zero]
    have hsum : ∀ (b j : ℕ), muSum step' b (step'^[j] (M.map (fun u => (τ ∘ u : Tuple T m))))
        = (muSum step b (step^[j] M)).map (fun u => (τ ∘ u : Tuple T m)) := by
      intro b
      induction b with
      | zero => exact fun j => hiter j
      | succ b ih =>
        intro j
        rw [muSum, muSum, Multiset.map_add, ← Function.iterate_succ_apply' step',
          ← Function.iterate_succ_apply' step, ih, hiter]
    show muSumFix step' (q₀.evaluatePlain D' (τ ∘ γ)) = Multiset.map _ (muSumFix step M)
    rw [hM]
    unfold muSumFix
    rw [hrounds]
    exact hsum _ 0
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hc₀ : ∀ a ∈ q₀.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_left _ ha)
    have hc₁ : ∀ a ∈ q₁.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hV₀ : ∀ v ∈ q₀.countValsAll D, τ v = v ∧ v ∈ W :=
      fun v hv => hV v (Set.mem_union_left _ hv)
    have hV₁ : ∀ X : Relation T m, ∀ v ∈ q₁.countValsAll (D.assign s X), τ v = v ∧ v ∈ W :=
      fun X v hv => hV v (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨X, hv⟩))
    have hDm : ∀ p ∈ q₁.leaves, p ≠ (m, s) → ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ W := fun p hp hne => hD p
      (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
    have hbody : ∀ X : Relation T m, (∀ u, Multiset.Mem X u → ∀ j, u j ∈ W) →
        (q₁.evaluatePlain (D'.assign s (Relation.mapVals τ X)) (τ ∘ γ) : Multiset (Tuple T m))
          = (q₁.evaluatePlain (D.assign s X) γ : Multiset (Tuple T m)).map
              (fun u => (τ ∘ u : Tuple T m)) := by
      intro X hX
      refine ih₁ hs.2 h h0 h0W (D.assign s X) (D'.assign s (Relation.mapVals τ X)) γ ?_ ?_ hγ hc₁
        (hV₁ X)
      · rintro ⟨k, t⟩ hp
        by_cases hkt : k = m ∧ t = s
        · obtain ⟨rfl, rfl⟩ := hkt
          rw [Database.find_assign, Database.find_assign, Option.map_some]
        · rw [Database.find_assign_of_ne s t _ D hkt, Database.find_assign_of_ne s t _ D' hkt]
          exact hD' (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp,
            decide_eq_true (fun h => hkt (Prod.mk.inj h))⟩))
      · rintro ⟨k, t⟩ hp r hr
        by_cases hkt : k = m ∧ t = s
        · obtain ⟨rfl, rfl⟩ := hkt
          rw [Database.find_assign, Option.some.injEq] at hr
          rw [← hr]; exact hX
        · rw [Database.find_assign_of_ne s t _ D hkt] at hr
          exact hDm (k, t) hp (fun h => hkt (Prod.mk.inj h)) r hr
    have hbodyV : ∀ X : Relation T m, (∀ u, Multiset.Mem X u → ∀ j, u j ∈ W) →
        ∀ u, Multiset.Mem (q₁.evaluatePlain (D.assign s X) γ) u → ∀ j, u j ∈ W :=
      fun X hX => AggQueryIn.valsIn_evaluatePlain_assign s q₁ hs.2 D γ W hDm hγ
        (fun a ha => (hc₁ a ha).2) X (fun v hv => (hV₁ X v hv).2) hX
    have hM := ih₀ hs.1 h h0 h0W D D' γ (fun p hp => hD' p (List.mem_append_left _ hp))
      (fun p hp => hD p (List.mem_append_left _ hp)) hγ hc₀ hV₀
    have hMV := AggQueryIn.valsIn_evaluatePlain q₀ hs.1 D γ W
      (fun p hp => hD p (List.mem_append_left _ hp)) hγ (fun a ha => (hc₀ a ha).2)
      (fun v hv => (hV₀ v hv).2)
    set step : Multiset (Tuple T m) → Multiset (Tuple T m) :=
      fun X => (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup with hstep
    set step' : Multiset (Tuple T m) → Multiset (Tuple T m) :=
      fun X => (q₀.evaluatePlain D' (τ ∘ γ) + q₁.evaluatePlain (D'.assign s X) (τ ∘ γ)).dedup
      with hstep'
    have hiterV : ∀ k, ∀ u ∈ muIter step k, ∀ j, u j ∈ W := by
      intro k
      induction k with
      | zero => exact fun u hu => absurd hu (Multiset.notMem_zero u)
      | succ k ih =>
        intro u hu
        rw [muIter] at hu
        rcases Multiset.mem_add.mp (Multiset.mem_dedup.mp hu) with h' | h'
        · exact hMV u h'
        · exact hbodyV _ ih u h'
    have hiter : ∀ k, muIter step' k = (muIter step k).map (fun u => (τ ∘ u : Tuple T m)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [muIter, muIter, ih]
        show ((q₀.evaluatePlain D' (τ ∘ γ) : Multiset (Tuple T m))
          + q₁.evaluatePlain (D'.assign s (Relation.mapVals τ (muIter step k))) (τ ∘ γ)).dedup
          = _
        rw [hM, hbody _ (hiterV k), ← Multiset.map_add]
        refine Multiset.dedup_map_of_injOn (fun x hx y hy hxy => (h.row_eq_iff ?_ ?_).mp hxy)
        · exact (Multiset.mem_add.mp hx).elim (hMV x) (hbodyV _ (hiterV k) x)
        · exact (Multiset.mem_add.mp hy).elim (hMV y) (hbodyV _ (hiterV k) y)
    have hidx : muFixIdx step' = muFixIdx step := by
      unfold muFixIdx
      congr 1
      ext j
      show step'^[j + 1] 0 = step'^[j] 0 ↔ step^[j + 1] 0 = step^[j] 0
      rw [← muIter_eq_iterate, ← muIter_eq_iterate, ← muIter_eq_iterate, ← muIter_eq_iterate,
        hiter, hiter]
      exact h.map_tuple_inj (hiterV _) (hiterV _)
    show muFix step' = Multiset.map _ (muFix step)
    unfold muFix
    rw [hidx]
    exact hiter _
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hcq : ∀ a ∈ q.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hcts : ∀ j, ∀ a ∈ (ts j).consts, τ a = a ∧ a ∈ W := fun j a ha =>
      hc a (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)))
    have hck : ∀ j, ∀ a ∈ Selection.constsOpt (keep j), τ a = a ∧ a ∈ W := fun j a ha =>
      hc a (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)))
    have hVq : ∀ v ∈ q.countValsAll D, τ v = v ∧ v ∈ W :=
      fun v hv => hV v (Set.mem_union_left _ hv)
    have hvals := AggQueryIn.valsIn_evaluatePlain q hs.2.2.2 D γ W hD hγ
      (fun a ha => (hcq a ha).2) (fun v hv => (hVq v hv).2)
    have hr := ih hs.2.2.2 h h0 h0W D D' γ hD' hD hγ hcq hVq
    rw [h.gamma_map hcnt is ts fs (fun j => Set.mem_singleton_iff.mp (hs.2.1 j)) hs.1 hcts keep
      hs.2.2.1 hck ord q D D' hγ hvals hr]
    refine Multiset.map_congr rfl (fun u hu => ?_)
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · show Fin.append _ _ (Fin.castAdd n₂ i) = τ (u (Fin.castAdd n₂ i))
      rw [Fin.append_left]; rfl
    · show Fin.append _ _ (Fin.natAdd n₁ j) = τ (u (Fin.natAdd n₁ j))
      rw [Fin.append_right]
      exact (hV _ (Set.mem_union_right _ ⟨γ, u, hu, j, rfl⟩)).1.symm
  | GammaScalar ts fs q ord ih =>
    rename_i c' m n₂
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    have hcq : ∀ a ∈ q.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hcts : ∀ j, ∀ a ∈ (ts j).consts, τ a = a ∧ a ∈ W := fun j a ha =>
      hc a (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩))
    have hVq : ∀ v ∈ q.countValsAll D, τ v = v ∧ v ∈ W :=
      fun v hv => hV v (Set.mem_union_left _ hv)
    have hvals := AggQueryIn.valsIn_evaluatePlain q hs.2.2 D γ W hD hγ
      (fun a ha => (hcq a ha).2) (fun v hv => (hVq v hv).2)
    have hr := ih hs.2.2 h h0 h0W D D' γ hD' hD hγ hcq hVq
    rw [h.gammaScalar_map hcnt ts fs (fun j => Set.mem_singleton_iff.mp (hs.2.1 j)) hs.1 hcts ord
      q D D' hγ hvals hr]
    symm
    refine Eq.trans (Multiset.map_congr rfl (fun u hu => ?_)) (Multiset.map_id _)
    funext j
    exact (hV _ (Set.mem_union_right _ ⟨γ, u, hu, j, rfl⟩)).1
  | GammaNest is his p f q ih =>
    rename_i c' m n₁ κ'
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    obtain ⟨hp, ⟨g', hsym, hmem, rfl⟩, hsq⟩ := hs
    obtain rfl := Set.mem_singleton_iff.mp hmem
    have hcq : ∀ a ∈ q.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hcp : ∀ a ∈ p.consts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_left _ ha)
    have hVq : ∀ v ∈ q.countValsAll D, τ v = v ∧ v ∈ W :=
      fun v hv => hV v (Set.mem_union_left _ hv)
    have hvals := AggQueryIn.valsIn_evaluatePlain q hsq D γ W hD hγ
      (fun a ha => (hcq a ha).2) (fun v hv => (hVq v hv).2)
    have hr := ih hsq h h0 h0W D D' γ hD' hD hγ hcq hVq
    rw [h.gammaNest_map hcnt is his p hp hcp hsym q D D' hγ hvals hr]
    refine Multiset.map_congr rfl (fun u hu => ?_)
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · show Fin.append _ _ (Fin.castAdd 1 i) = τ (u (Fin.castAdd 1 i))
      rw [Fin.append_left]; rfl
    · show Fin.append _ _ (Fin.natAdd n₁ j) = τ (u (Fin.natAdd n₁ j))
      rw [Fin.append_right, Fin.fin_one_eq_zero j]
      exact (hV _ (Set.mem_union_right _ ⟨γ, u, hu, rfl⟩)).1.symm
  | ProvSum is his t q ih => exact fun hs => hs.elim
  | GammaTok is his ts fs a q keep ih => exact fun hs => hs.elim
  | Win P O o w t f q hrr dist keep ih =>
    rename_i c' n' m' p' κ'
    intro hs τ W h h0 h0W D D' γ hD' hD hγ hc hV
    obtain ⟨ht, hf, hk, hsq⟩ := hs
    have hcq : ∀ a ∈ q.allConsts, τ a = a ∧ a ∈ W := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hct : ∀ a ∈ t.consts, τ a = a ∧ a ∈ W := fun a ha =>
      hc a (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
    have hck : ∀ a ∈ Selection.constsOpt keep, τ a = a ∧ a ∈ W := fun a ha =>
      hc a (Finset.mem_union_left _ (Finset.mem_union_right _ ha))
    have hVq : ∀ v ∈ q.countValsAll D, τ v = v ∧ v ∈ W :=
      fun v hv => hV v (Set.mem_union_left _ hv)
    have hvals := AggQueryIn.valsIn_evaluatePlain q hsq D γ W hD hγ
      (fun a ha => (hcq a ha).2) (fun v hv => (hVq v hv).2)
    have hr := ih hsq h h0 h0W D D' γ hD' hD hγ hcq hVq
    have hfc : (if dist then f.distinct else f) = cnt := by
      cases dist with
      | false => exact Set.mem_singleton_iff.mp hf
      | true => exact Set.mem_singleton_iff.mp hf
    rw [h.win_map hcnt h0 h0W P O o w t ht hct f hfc keep hk hck q hrr D D' hγ hvals hr]
    refine Multiset.map_congr rfl (fun u hu => ?_)
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · show (Fin.snoc _ _ : Tuple T (n' + 1)) (Fin.last n') = τ (u (Fin.last n'))
      rw [Fin.snoc_last]
      exact (hV _ (Set.mem_union_right _ ⟨γ, u, hu, rfl⟩)).1.symm
    · show (Fin.snoc _ _ : Tuple T (n' + 1)) (Fin.castSucc i) = τ (u (Fin.castSucc i))
      rw [Fin.snoc_castSucc]; rfl
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hs => hs.elim

/-! ## Order types

Two parameter tuples have the same *order type* over a finite set of
values when each parameter falls at the same place among the set's values
and the parameters compare alike pairwise. A map sending one to the other
and fixing the set is then faithful on the set and on the first tuple,
which is what the commutation theorem asks; over a set holding the null,
the order type decides nullness too. There are finitely many order types
over a set, polynomially many in its size, which is what bounds the counts
a query can compute as its parameters vary. -/

/-- How many values of `S` are at most `x`. -/
def Finset.cardLe (S : Finset T) (x : T) : ℕ := (S.filter (· ≤ x)).card

theorem Finset.cardLe_le_card (S : Finset T) (x : T) : S.cardLe x ≤ S.card :=
  Finset.card_filter_le _ _

theorem Finset.cardLe_mono (S : Finset T) {x y : T} (h : x ≤ y) : S.cardLe x ≤ S.cardLe y :=
  Finset.card_le_card (fun _ ha => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp ha).1, le_trans (Finset.mem_filter.mp ha).2 h⟩)

/-- For `b ∈ S`, `x < b` exactly when fewer values of `S` are at most `x`
than at most `b`. -/
theorem Finset.lt_iff_cardLe_lt (S : Finset T) {b : T} (hb : b ∈ S) (x : T) :
    (x < b) ↔ (S.cardLe x < S.cardLe b) := by
  constructor
  · intro hxb
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset
      (fun a ha => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp ha).1, le_trans (Finset.mem_filter.mp ha).2 (le_of_lt hxb)⟩)).mpr
      ⟨b, Finset.mem_filter.mpr ⟨hb, le_refl b⟩, fun hmem => ?_⟩)
    exact absurd (Finset.mem_filter.mp hmem).2 (not_le.mpr hxb)
  · intro hlt
    by_contra hnot
    exact absurd (S.cardLe_mono (not_lt.mp hnot)) (not_le.mpr hlt)

/-- For `a ∈ S`, `a ≤ x` exactly when no more values of `S` are at most
`a` than at most `x`. -/
theorem Finset.le_iff_cardLe_le (S : Finset T) {a : T} (ha : a ∈ S) (x : T) :
    (a ≤ x) ↔ (S.cardLe a ≤ S.cardLe x) := by
  constructor
  · exact fun h => S.cardLe_mono h
  · intro hle
    by_contra hnot
    exact absurd ((S.lt_iff_cardLe_lt ha x).mp (not_le.mp hnot)) (not_lt.mpr hle)

theorem Finset.eq_of_cardLe_eq (S : Finset T) {a b : T} (ha : a ∈ S) (hb : b ∈ S)
    (h : S.cardLe a = S.cardLe b) : a = b :=
  le_antisymm ((S.le_iff_cardLe_le ha b).mpr (le_of_eq h))
    ((S.le_iff_cardLe_le hb a).mpr (le_of_eq h.symm))

/-- The order types over `S` of tuples of `c` parameters. -/
abbrev OrdType (S : Finset T) (c : ℕ) : Type :=
  (Fin c → Fin (S.card + 1) × Bool) × (Fin c → Fin c → Bool)

/-- **The order type of a parameter tuple over `S`**: for each parameter,
how many values of `S` are at most it and whether it is one of them, and
how the parameters compare pairwise. -/
def ordType (S : Finset T) {c : ℕ} (u : Fin c → T) : OrdType S c :=
  (fun i => (⟨S.cardLe (u i), Nat.lt_succ_of_le (S.cardLe_le_card _)⟩, decide (u i ∈ S)),
    fun i j => decide (u i ≤ u j))

/-- **Two tuples of one order type are related by a faithful map** fixing
the set, where the set holds the null. -/
theorem exists_faithful_of_ordType_eq (S : Finset T)
    (hν : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ S) {c : ℕ} {u u' : Fin c → T}
    (h : ordType S u = ordType S u') :
    ∃ τ : T → T, FaithfulOn τ (↑S ∪ Set.range u) ∧ (∀ a ∈ S, τ a = a) ∧ ∀ i, τ (u i) = u' i := by
  classical
  have hpos : ∀ i, S.cardLe (u i) = S.cardLe (u' i) :=
    fun i => congrArg (fun o : OrdType S c => (o.1 i).1.val) h
  have hmem : ∀ i, u i ∈ S ↔ u' i ∈ S := fun i =>
    decide_eq_decide.mp (congrArg (fun o : OrdType S c => (o.1 i).2) h)
  have hle : ∀ i j, (u i ≤ u j ↔ u' i ≤ u' j) := fun i j =>
    decide_eq_decide.mp (congrArg (fun o : OrdType S c => o.2 i j) h)
  let τ : T → T := fun a =>
    if a ∈ S then a else if h : ∃ i, u i = a then u' (Classical.choose h) else a
  have hτS : ∀ a ∈ S, τ a = a := fun a ha => ite_eq_left ha
  have hτu : ∀ i, τ (u i) = u' i := by
    intro i
    by_cases hi : u i ∈ S
    · rw [hτS _ hi]
      exact S.eq_of_cardLe_eq hi ((hmem i).mp hi) (hpos i)
    · have hex : ∃ j, u j = u i := ⟨i, rfl⟩
      show (if u i ∈ S then u i else if h : ∃ j, u j = u i then u' (Classical.choose h) else u i)
        = u' i
      rw [ite_eq_right hi, dite_eq_left hex]
      have hj := Classical.choose_spec hex
      exact le_antisymm ((hle _ _).mp (le_of_eq hj)) ((hle _ _).mp (le_of_eq hj.symm))
  have hW : ∀ a ∈ (↑S ∪ Set.range u : Set T), a ∈ S ∨ ∃ i, u i ∉ S ∧ a = u i := by
    rintro a (ha | ⟨i, rfl⟩)
    · exact Or.inl ha
    · by_cases hi : u i ∈ S
      · exact Or.inl hi
      · exact Or.inr ⟨i, hi, rfl⟩
  have hnull : ∀ x, x ∉ S → ValueType.isNull x = false := by
    intro x hx
    by_contra hn
    exact hx (hν x ((ValueType.isNull_iff_nullVal x).mp (by simpa using hn)))
  -- a value outside `S` is at most a value of `S` exactly when it is below it
  have hle_of_notMem : ∀ x, x ∉ S → ∀ b ∈ S, (x ≤ b ↔ ¬ (b ≤ x)) := by
    intro x hx b hb
    rw [← not_lt]
    exact not_congr (lt_iff_le_and_ne.trans (and_iff_left (fun hbx => hx (hbx ▸ hb))))
  refine ⟨τ, ⟨?_, ?_⟩, hτS, hτu⟩
  · intro a ha
    rcases hW a ha with haS | ⟨i, hi, rfl⟩
    · rw [hτS a haS]
    · rw [hτu i, hnull _ hi, hnull _ (fun h' => hi ((hmem i).mpr h'))]
  · intro a ha b hb
    rcases hW a ha with haS | ⟨i, hi, rfl⟩ <;> rcases hW b hb with hbS | ⟨j, hj, rfl⟩
    · rw [hτS a haS, hτS b hbS]
    · rw [hτS a haS, hτu j, S.le_iff_cardLe_le haS, S.le_iff_cardLe_le haS, hpos j]
    · rw [hτu i, hτS b hbS, hle_of_notMem _ (fun h' => hi ((hmem i).mpr h')) b hbS,
        hle_of_notMem _ hi b hbS, S.le_iff_cardLe_le hbS, S.le_iff_cardLe_le hbS, hpos i]
    · rw [hτu i, hτu j]
      exact (hle i j).symm

/-- A representative parameter tuple of an order type, where one exists. -/
noncomputable def ordRep (S : Finset T) (c : ℕ) (ω : OrdType S c) : Fin c → T :=
  open Classical in
  if h : ∃ u : Fin c → T, ordType S u = ω then Classical.choose h else fun _ => 0

theorem ordType_ordRep (S : Finset T) {c : ℕ} (u : Fin c → T) :
    ordType S (ordRep S c (ordType S u)) = ordType S u := by
  unfold ordRep
  rw [dite_eq_left (⟨u, rfl⟩ : ∃ v : Fin c → T, ordType S v = ordType S u)]
  exact Classical.choose_spec (⟨u, rfl⟩ : ∃ v : Fin c → T, ordType S v = ordType S u)

/-- The values a relation holds at some of its columns. -/
def Relation.valsAtCols {n : ℕ} (r : Multiset (Tuple T n)) (J : Finset (Fin n)) : Finset T :=
  J.biUnion (fun j => (r.map (fun u => u j)).toFinset)

theorem Relation.mem_valsAtCols {n : ℕ} {r : Multiset (Tuple T n)} {J : Finset (Fin n)}
    {u : Tuple T n} (hu : u ∈ r) {j : Fin n} (hj : j ∈ J) : u j ∈ Relation.valsAtCols r J :=
  Finset.mem_biUnion.mpr ⟨j, hj, Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨u, hu, rfl⟩)⟩

/-- The values at some columns of a query's result at a representative of
each order type over `S`. -/
noncomputable def AggQueryIn.repVals (S : Finset T) {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (Q : AggQueryIn T c n κ l) (J : Finset (Fin n)) (D : Database T) :
    Finset T :=
  Finset.univ.biUnion (fun ω : OrdType S c => Relation.valsAtCols (Q.evaluatePlain D (ordRep S c ω)) J)

/-- **The count types of a query over a base set `B`**: at each
aggregating node, the values of its aggregate columns at a representative
of each order type of its context over `B` and the count types of its
input. Every count the query computes is one of these, and there are
polynomially many in `|B|`. -/
noncomputable def AggQueryIn.countTypes (B : Finset T) : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c n κ l → Database T → Finset T
  | _, _, _, _, .Rel _ _, _ => ∅
  | _, _, _, _, .Hole _ _, _ => ∅
  | _, _, _, _, .Empty, _ => ∅
  | _, _, _, _, .Proj _ q, D => q.countTypes B D
  | _, _, _, _, .Sel _ q _, D => q.countTypes B D
  | _, _, _, _, .Prod q₁ q₂, D => Union.union (q₁.countTypes B D) (q₂.countTypes B D)
  | _, _, _, _, .Apply q₁ q₂, D => Union.union (q₁.countTypes B D) (q₂.countTypes B D)
  | _, _, _, _, .Sum q₁ q₂, D => Union.union (q₁.countTypes B D) (q₂.countTypes B D)
  | _, _, _, _, .Dedup q, D => q.countTypes B D
  | _, _, _, _, .Diff q₁ q₂, D => Union.union (q₁.countTypes B D) (q₂.countTypes B D)
  | _, _, _, _, .Alt _ _ q, D => q.countTypes B D
  | _, _, _, _, .Retag _ q, D => q.countTypes B D
  | _, _, _, _, .Mu _ q₀ q₁, D => Union.union (q₀.countTypes B D) (q₁.countTypes B D)
  | _, _, _, _, .MuSet _ q₀ q₁, D => Union.union (q₀.countTypes B D) (q₁.countTypes B D)
  | _, _, _, _, @AggQueryIn.Gamma _ _ _ n₁ n₂ is ts fs q keep ord, D =>
      Union.union (q.countTypes B D)
        ((AggQueryIn.Gamma is ts fs q keep ord).repVals (Union.union B (q.countTypes B D))
          (Finset.univ.image (Fin.natAdd n₁ : Fin n₂ → Fin (n₁ + n₂))) D)
  | _, _, _, _, @AggQueryIn.GammaScalar _ _ _ _ ts fs q ord, D =>
      Union.union (q.countTypes B D)
        ((AggQueryIn.GammaScalar ts fs q ord).repVals (Union.union B (q.countTypes B D))
          Finset.univ D)
  | _, _, _, _, @AggQueryIn.GammaNest _ _ _ n₁ _ is his p f q, D =>
      Union.union (q.countTypes B D)
        ((AggQueryIn.GammaNest is his p f q).repVals (Union.union B (q.countTypes B D))
          {Fin.natAdd n₁ 0} D)
  | _, _, _, _, .ProvSum _ _ _ q, D => q.countTypes B D
  | _, _, _, _, .GammaTok _ _ _ _ _ q _, D => q.countTypes B D
  | _, _, _, _, @AggQueryIn.Win _ _ n _ _ _ P O o w t f q hrr dist keep, D =>
      Union.union (q.countTypes B D)
        ((AggQueryIn.Win P O o w t f q hrr dist keep).repVals (Union.union B (q.countTypes B D))
          {Fin.last n} D)
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _, D => q.countTypes B D

/-! ## Every count is a count type

At an aggregating node, the counts at a context are the counts at the
representative of its order type: the two contexts are related by a
faithful map fixing the base set and the input's count types, with which
the input commutes. -/

/-- **The faithful map to the representative**, at an aggregating node:
the node's input, read at the representative of the context's order type
over `S`, is the mapped input. `S` holds the base set and the counts the
input computes. -/
theorem AggQueryIn.exists_faithful_rep {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) {B : Finset T}
    (hν : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) (h0 : (0 : T) ∈ B)
    {c m : ℕ} {κ : Fin m → ColKind} (q : AggQueryIn T c m κ) (hs : q.inSig {cnt})
    {S : Finset T} (hBS : B ⊆ S) (D D' : Database T)
    (hD' : ∀ p ∈ q.leaves, D'.find p.1 p.2 = D.find p.1 p.2)
    (hD : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
      ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B)
    (hc : ∀ a ∈ q.allConsts, a ∈ B) (hcv : q.countValsAll D' ⊆ ↑S) (γ : Fin c → T) :
    ∃ τ : T → T, FaithfulOn τ (↑S ∪ Set.range γ) ∧ (∀ a ∈ S, τ a = a) ∧ τ 0 = 0
      ∧ (0 : T) ∈ (↑S ∪ Set.range γ : Set T) ∧ τ ∘ γ = ordRep S c (ordType S γ)
      ∧ (∀ u, Multiset.Mem (q.evaluatePlain D' γ) u → ∀ j, u j ∈ (↑S ∪ Set.range γ : Set T))
      ∧ (q.evaluatePlain D (τ ∘ γ) : Multiset (Tuple T m))
          = (q.evaluatePlain D' γ : Multiset (Tuple T m)).map (fun u => (τ ∘ u : Tuple T m)) := by
  obtain ⟨τ, h, hτS, hτγ⟩ := exists_faithful_of_ordType_eq S (fun ν hn => hBS (hν ν hn))
    (ordType_ordRep S γ).symm
  have hSW : ∀ a ∈ S, a ∈ (↑S ∪ Set.range γ : Set T) :=
    fun a ha => Set.mem_union_left _ (Finset.mem_coe.mpr ha)
  have hBW : ∀ a ∈ B, a ∈ (↑S ∪ Set.range γ : Set T) := fun a ha => hSW a (hBS ha)
  have hγW : ∀ j, γ j ∈ (↑S ∪ Set.range γ : Set T) := fun j => Set.mem_union_right _ ⟨j, rfl⟩
  have hDW : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D'.find p.1 p.2 = some r →
      ∀ u, Multiset.Mem r u → ∀ j, u j ∈ (↑S ∪ Set.range γ : Set T) :=
    fun p hp r hr u hu j => hBW _ (hD p hp r (by rw [← hD' p hp]; exact hr) u hu j)
  refine ⟨τ, h, hτS, hτS 0 (hBS h0), hBW 0 h0, funext hτγ, ?_, ?_⟩
  · exact AggQueryIn.valsIn_evaluatePlain q hs D' γ _ hDW hγW (fun a ha => hBW a (hc a ha))
      (fun v hv => hSW v (hcv hv))
  · refine AggQueryIn.evaluatePlain_faithful hcnt q hs h (hτS 0 (hBS h0)) (hBW 0 h0) D' D γ ?_
      hDW hγW (fun a ha => ⟨hτS a (hBS (hc a ha)), hBW a (hc a ha)⟩)
      (fun v hv => ⟨hτS v (hcv hv), hSW v (hcv hv)⟩)
    intro p hp
    rw [hD' p hp]
    cases hf : D.find p.1 p.2 with
    | none => rfl
    | some r =>
      rw [Option.map_some]
      congr 1
      show r = (r : Multiset (Tuple T p.1)).map (fun u => (τ ∘ u : Tuple T p.1))
      symm
      refine Eq.trans (Multiset.map_congr rfl (fun u hu => ?_)) (Multiset.map_id _)
      funext j
      exact hτS _ (hBS (hD p hp r hf u hu j))

/-- **Every count a query computes is a count type**: over a base set
holding the instance's values at the query's leaves, its constants, the
zero and the null, the counts of a hygienic query of the minimal signature
lie in the base set and its count types. The instance it is read at may
differ from the one the count types are taken over at the holes, which is
what a recursion's rounds need. -/
theorem AggQueryIn.countValsAll_subset {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) {B : Finset T}
    (hν : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) (h0 : (0 : T) ∈ B) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig {cnt} → q.hygienic → (∀ p ∈ l, q.noMention p.1) →
      ∀ (D D' : Database T),
        (∀ p ∈ q.leaves, (p.2, p.1) ∉ l → D'.find p.1 p.2 = D.find p.1 p.2) →
        (∀ p ∈ q.leaves, (p.2, p.1) ∉ l → ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
          ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B) →
        (∀ a ∈ q.allConsts, a ∈ B) →
        q.countValsAll D' ⊆ ↑(Union.union B (q.countTypes B D)) := by
  have hmono : ∀ {A : Set T} {C C' : Finset T}, A ⊆ ↑(Union.union B C) → C ⊆ C' →
      A ⊆ ↑(Union.union B C') :=
    fun hA hC => subset_trans hA (Finset.coe_subset.mpr (Finset.union_subset_union_right hC))
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ _ _ _ _ _ _ _ => Set.empty_subset _
  | Hole n s => exact fun _ _ _ _ _ _ _ _ => Set.empty_subset _
  | Empty => exact fun _ _ _ _ _ _ _ _ => Set.empty_subset _
  | Proj ps q ih =>
    exact fun hs hh hn D D' hD' hD hc => ih hs.2 hh hn D D' hD' hD
      (fun a ha => hc a (Finset.mem_union_right _ ha))
  | Sel φ q _ ih =>
    exact fun hs hh hn D D' hD' hD hc => ih hs.2 hh hn D D' hD' hD
      (fun a ha => hc a (Finset.mem_union_right _ ha))
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn D D' hD' hD hc
    have h₁ := ih₁ hs.1 hh.1 (fun p hp => (hn p (List.mem_append_left _ hp)).1) D D'
      (fun p hp hpl => hD' p (List.mem_append_left _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim hpl (fun h₂ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₁ (hn _ (List.mem_append_right _ h₂)).1 p hp rfl))))
      (fun p hp hpl => hD p (List.mem_append_left _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim hpl (fun h₂ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₁ (hn _ (List.mem_append_right _ h₂)).1 p hp rfl))))
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₂ := ih₂ hs.2 hh.2 (fun p hp => (hn p (List.mem_append_right _ hp)).2) D D'
      (fun p hp hpl => hD' p (List.mem_append_right _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim (fun h₁ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₂ (hn _ (List.mem_append_left _ h₁)).2 p hp rfl))
          hpl))
      (fun p hp hpl => hD p (List.mem_append_right _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim (fun h₁ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₂ (hn _ (List.mem_append_left _ h₁)).2 p hp rfl))
          hpl))
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    exact Set.union_subset (hmono h₁ Finset.subset_union_left) (hmono h₂ Finset.subset_union_right)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn D D' hD' hD hc
    have h₁ := ih₁ hs.1 hh.1 (fun p hp => (hn p hp).1) D D'
      (fun p hp hpl => hD' p (List.mem_append_left _ hp) hpl)
      (fun p hp hpl => hD p (List.mem_append_left _ hp) hpl)
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₂ := ih₂ hs.2 hh.2 (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD' p (List.mem_append_right _ hp) (fun hmem =>
        absurd rfl (AggQueryIn.ne_of_noMention_of_mem_leaves q₂ (hn _ hmem).2 p hp)))
      (fun p hp _ => hD p (List.mem_append_right _ hp) (fun hmem =>
        absurd rfl (AggQueryIn.ne_of_noMention_of_mem_leaves q₂ (hn _ hmem).2 p hp)))
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    exact Set.union_subset (hmono h₁ Finset.subset_union_left) (hmono h₂ Finset.subset_union_right)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn D D' hD' hD hc
    have h₁ := ih₁ hs.1 hh.1 (fun p hp => (hn p (List.mem_append_left _ hp)).1) D D'
      (fun p hp hpl => hD' p (List.mem_append_left _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim hpl (fun h₂ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₁ (hn _ (List.mem_append_right _ h₂)).1 p hp rfl))))
      (fun p hp hpl => hD p (List.mem_append_left _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim hpl (fun h₂ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₁ (hn _ (List.mem_append_right _ h₂)).1 p hp rfl))))
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₂ := ih₂ hs.2 hh.2 (fun p hp => (hn p (List.mem_append_right _ hp)).2) D D'
      (fun p hp hpl => hD' p (List.mem_append_right _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim (fun h₁ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₂ (hn _ (List.mem_append_left _ h₁)).2 p hp rfl))
          hpl))
      (fun p hp hpl => hD p (List.mem_append_right _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim (fun h₁ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₂ (hn _ (List.mem_append_left _ h₁)).2 p hp rfl))
          hpl))
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    exact Set.union_subset (hmono h₁ Finset.subset_union_left) (hmono h₂ Finset.subset_union_right)
  | Dedup q ih => exact fun hs hh hn D D' hD' hD hc => ih hs hh hn D D' hD' hD hc
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn D D' hD' hD hc
    have h₁ := ih₁ hs.1 hh.1 (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD' p (List.mem_append_left _ hp) List.not_mem_nil)
      (fun p hp _ => hD p (List.mem_append_left _ hp) List.not_mem_nil)
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₂ := ih₂ hs.2 hh.2 (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD' p (List.mem_append_right _ hp) List.not_mem_nil)
      (fun p hp _ => hD p (List.mem_append_right _ hp) List.not_mem_nil)
      (fun a ha => hc a (Finset.mem_union_right _ ha))
    exact Set.union_subset (hmono h₁ Finset.subset_union_left) (hmono h₂ Finset.subset_union_right)
  | Alt k hk q ih => exact fun hs hh hn D D' hD' hD hc => ih hs hh hn D D' hD' hD hc
  | Retag hk q ih => exact fun hs hh hn D D' hD' hD hc => ih hs hh hn D D' hD' hD hc
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs hh hn D D' hD' hD hc
    have h₀ := ih₀ hs.1 hh.2.2.1 (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD' p (List.mem_append_left _ hp) List.not_mem_nil)
      (fun p hp _ => hD p (List.mem_append_left _ hp) List.not_mem_nil)
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₁ : ∀ X : Relation T m, q₁.countValsAll (D'.assign s X)
        ⊆ ↑(Union.union B (q₁.countTypes B D)) := by
      intro X
      refine ih₁ hs.2 hh.2.2.2 (fun p hp => ?_) D (D'.assign s X) ?_ ?_
        (fun a ha => hc a (Finset.mem_union_right _ ha))
      · rw [List.mem_singleton.mp hp]; exact hh.2.1
      · rintro ⟨k, t⟩ hp hpl
        have hne : (k, t) ≠ (m, s) := fun h => hpl (by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact List.mem_singleton_self _)
        rw [Database.find_assign_of_ne s t X D' (fun h => hne (Prod.ext h.1 h.2))]
        exact hD' (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
          List.not_mem_nil
      · rintro ⟨k, t⟩ hp hpl
        have hne : (k, t) ≠ (m, s) := fun h => hpl (by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact List.mem_singleton_self _)
        exact hD (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
          List.not_mem_nil
    exact Set.union_subset (hmono h₀ Finset.subset_union_left)
      (Set.iUnion_subset (fun X => hmono (h₁ X) Finset.subset_union_right))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs hh hn D D' hD' hD hc
    have h₀ := ih₀ hs.1 hh.2.2.1 (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD' p (List.mem_append_left _ hp) List.not_mem_nil)
      (fun p hp _ => hD p (List.mem_append_left _ hp) List.not_mem_nil)
      (fun a ha => hc a (Finset.mem_union_left _ ha))
    have h₁ : ∀ X : Relation T m, q₁.countValsAll (D'.assign s X)
        ⊆ ↑(Union.union B (q₁.countTypes B D)) := by
      intro X
      refine ih₁ hs.2 hh.2.2.2 (fun p hp => ?_) D (D'.assign s X) ?_ ?_
        (fun a ha => hc a (Finset.mem_union_right _ ha))
      · rw [List.mem_singleton.mp hp]; exact hh.2.1
      · rintro ⟨k, t⟩ hp hpl
        have hne : (k, t) ≠ (m, s) := fun h => hpl (by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact List.mem_singleton_self _)
        rw [Database.find_assign_of_ne s t X D' (fun h => hne (Prod.ext h.1 h.2))]
        exact hD' (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
          List.not_mem_nil
      · rintro ⟨k, t⟩ hp hpl
        have hne : (k, t) ≠ (m, s) := fun h => hpl (by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact List.mem_singleton_self _)
        exact hD (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
          List.not_mem_nil
    exact Set.union_subset (hmono h₀ Finset.subset_union_left)
      (Set.iUnion_subset (fun X => hmono (h₁ X) Finset.subset_union_right))
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂
    intro hs hh hn D D' hD' hD hc
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hD'q : ∀ p ∈ q.leaves, D'.find p.1 p.2 = D.find p.1 p.2 :=
      fun p hp => hD' p hp List.not_mem_nil
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hq := ih hs.2.2.2 hh (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD'q p hp) (fun p hp _ => hDq p hp) hcq
    have hBS : B ⊆ Union.union B (q.countTypes B D) := Finset.subset_union_left
    refine Set.union_subset (hmono hq Finset.subset_union_left) ?_
    rintro v ⟨γ, u, hu, j, rfl⟩
    obtain ⟨τ, h, hτS, h0τ, h0W, hcomp, hvals, hr⟩ :=
      AggQueryIn.exists_faithful_rep hcnt hν h0 q hs.2.2.2 hBS D D' hD'q hDq hcq hq γ
    have hfix : ∀ a ∈ B, τ a = a ∧ a ∈ (↑(Union.union B (q.countTypes B D)) ∪ Set.range γ : Set T) :=
      fun a ha => ⟨hτS a (hBS ha), Set.mem_union_left _ (hBS ha)⟩
    have hG := h.gamma_map hcnt is ts fs (fun j => Set.mem_singleton_iff.mp (hs.2.1 j)) hs.1
      (fun j a ha => hfix a (hc a (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩))))) keep hs.2.2.1
      (fun j a ha => hfix a (hc a (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩))))) ord q D' D
      (fun j => Set.mem_union_right _ ⟨j, rfl⟩) hvals hr
    rw [hcomp] at hG
    have hFu := Multiset.mem_map_of_mem (f := fun u : Tuple T (n₁ + n₂) =>
      Fin.append (τ ∘ (fun i => u (Fin.castAdd n₂ i)) : Tuple T n₁) (fun j => u (Fin.natAdd n₁ j))) hu
    rw [← hG] at hFu
    have hmem := Relation.mem_valsAtCols
      (J := Finset.univ.image (Fin.natAdd n₁ : Fin n₂ → Fin (n₁ + n₂))) hFu
      (j := Fin.natAdd n₁ j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    rw [Fin.append_right] at hmem
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨ordType _ γ, Finset.mem_univ _, hmem⟩)))
  | GammaScalar ts fs q ord ih =>
    rename_i c' m n₂
    intro hs hh hn D D' hD' hD hc
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hD'q : ∀ p ∈ q.leaves, D'.find p.1 p.2 = D.find p.1 p.2 :=
      fun p hp => hD' p hp List.not_mem_nil
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hq := ih hs.2.2 hh (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD'q p hp) (fun p hp _ => hDq p hp) hcq
    have hBS : B ⊆ Union.union B (q.countTypes B D) := Finset.subset_union_left
    refine Set.union_subset (hmono hq Finset.subset_union_left) ?_
    rintro v ⟨γ, u, hu, j, rfl⟩
    obtain ⟨τ, h, hτS, h0τ, h0W, hcomp, hvals, hr⟩ :=
      AggQueryIn.exists_faithful_rep hcnt hν h0 q hs.2.2 hBS D D' hD'q hDq hcq hq γ
    have hfix : ∀ a ∈ B, τ a = a ∧ a ∈ (↑(Union.union B (q.countTypes B D)) ∪ Set.range γ : Set T) :=
      fun a ha => ⟨hτS a (hBS ha), Set.mem_union_left _ (hBS ha)⟩
    have hG := h.gammaScalar_map hcnt ts fs (fun j => Set.mem_singleton_iff.mp (hs.2.1 j)) hs.1
      (fun j a ha => hfix a (hc a (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)))) ord q D' D
      (fun j => Set.mem_union_right _ ⟨j, rfl⟩) hvals hr
    rw [hcomp] at hG
    have hu' : Multiset.Mem ((AggQueryIn.GammaScalar ts fs q ord).evaluatePlain D
        (ordRep (Union.union B (q.countTypes B D)) c'
          (ordType (Union.union B (q.countTypes B D)) γ))) u := by
      rw [hG]; exact hu
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨ordType _ γ, Finset.mem_univ _,
        Relation.mem_valsAtCols hu' (Finset.mem_univ j)⟩)))
  | GammaNest is his p f q ih =>
    rename_i c' m n₁ κ'
    intro hs hh hn D D' hD' hD hc
    obtain ⟨hp, ⟨g', hsym, hmem, rfl⟩, hsq⟩ := hs
    obtain rfl := Set.mem_singleton_iff.mp hmem
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hD'q : ∀ p ∈ q.leaves, D'.find p.1 p.2 = D.find p.1 p.2 :=
      fun p hp => hD' p hp List.not_mem_nil
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hq := ih hsq hh (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD'q p hp) (fun p hp _ => hDq p hp) hcq
    have hBS : B ⊆ Union.union B (q.countTypes B D) := Finset.subset_union_left
    refine Set.union_subset (hmono hq Finset.subset_union_left) ?_
    rintro v ⟨γ, u, hu, rfl⟩
    obtain ⟨τ, h, hτS, h0τ, h0W, hcomp, hvals, hr⟩ :=
      AggQueryIn.exists_faithful_rep hcnt hν h0 q hsq hBS D D' hD'q hDq hcq hq γ
    have hfix : ∀ a ∈ B, τ a = a ∧ a ∈ (↑(Union.union B (q.countTypes B D)) ∪ Set.range γ : Set T) :=
      fun a ha => ⟨hτS a (hBS ha), Set.mem_union_left _ (hBS ha)⟩
    have hG := h.gammaNest_map hcnt is his p hp
      (fun a ha => hfix a (hc a (Finset.mem_union_left _ ha))) hsym q D' D
      (fun j => Set.mem_union_right _ ⟨j, rfl⟩) hvals hr
    rw [hcomp] at hG
    have hFu := Multiset.mem_map_of_mem (f := fun u : Tuple T (n₁ + 1) =>
      Fin.append (τ ∘ (fun i => u (Fin.castAdd 1 i)) : Tuple T n₁) (fun j => u (Fin.natAdd n₁ j))) hu
    rw [← hG] at hFu
    have hmem := Relation.mem_valsAtCols hFu (Finset.mem_singleton_self (Fin.natAdd n₁ 0))
    rw [Fin.append_right] at hmem
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨ordType _ γ, Finset.mem_univ _, hmem⟩)))
  | ProvSum is his t q ih => exact fun hs => hs.elim
  | GammaTok is his ts fs a q keep ih => exact fun hs => hs.elim
  | Win P O o w t f q hrr dist keep ih =>
    rename_i c' n' m' p' κ'
    intro hs hh hn D D' hD' hD hc
    obtain ⟨ht, hf, hk, hsq⟩ := hs
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hD'q : ∀ p ∈ q.leaves, D'.find p.1 p.2 = D.find p.1 p.2 :=
      fun p hp => hD' p hp List.not_mem_nil
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hq := ih hsq hh (fun p hp => absurd hp List.not_mem_nil) D D'
      (fun p hp _ => hD'q p hp) (fun p hp _ => hDq p hp) hcq
    have hBS : B ⊆ Union.union B (q.countTypes B D) := Finset.subset_union_left
    have hfc : (if dist then f.distinct else f) = cnt := by
      cases dist with
      | false => exact Set.mem_singleton_iff.mp hf
      | true => exact Set.mem_singleton_iff.mp hf
    refine Set.union_subset (hmono hq Finset.subset_union_left) ?_
    rintro v ⟨γ, u, hu, rfl⟩
    obtain ⟨τ, h, hτS, h0τ, h0W, hcomp, hvals, hr⟩ :=
      AggQueryIn.exists_faithful_rep hcnt hν h0 q hsq hBS D D' hD'q hDq hcq hq γ
    have hfix : ∀ a ∈ B, τ a = a ∧ a ∈ (↑(Union.union B (q.countTypes B D)) ∪ Set.range γ : Set T) :=
      fun a ha => ⟨hτS a (hBS ha), Set.mem_union_left _ (hBS ha)⟩
    have hG := h.win_map hcnt h0τ h0W P O o w t ht
      (fun a ha => hfix a (hc a (Finset.mem_union_left _ (Finset.mem_union_left _ ha)))) f hfc keep hk
      (fun a ha => hfix a (hc a (Finset.mem_union_left _ (Finset.mem_union_right _ ha)))) q hrr D' D
      (fun j => Set.mem_union_right _ ⟨j, rfl⟩) hvals hr
    rw [hcomp] at hG
    have hFu := Multiset.mem_map_of_mem (f := fun u : Tuple T (n' + 1) =>
      (Fin.snoc (τ ∘ Fin.init u : Tuple T n') (u (Fin.last n')) : Tuple T (n' + 1))) hu
    erw [← hG] at hFu
    have hmem := Relation.mem_valsAtCols hFu (Finset.mem_singleton_self (Fin.last n'))
    rw [Fin.snoc_last] at hmem
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨ordType _ γ, Finset.mem_univ _, hmem⟩)))
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hs => hs.elim

/-! ## There are polynomially many count types

An aggregating node's count types at one order type are the values of its
aggregate columns at one context, no more than its groups, which are
tuples over the base set, the count types of its input and the context;
and there are polynomially many order types. -/

/-- A function of a natural number bounded by a polynomial. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ a b : ℕ, ∀ m, f m ≤ a * (m + 1) ^ b

namespace PolyBounded

theorem const (k : ℕ) : PolyBounded (fun _ => k) := ⟨k, 0, fun m => by simp⟩

theorem id : PolyBounded (fun m => m) := ⟨1, 1, fun m => by simp⟩

theorem mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ m, f m ≤ g m) : PolyBounded f := by
  obtain ⟨a, b, hb⟩ := hg
  exact ⟨a, b, fun m => le_trans (h m) (hb m)⟩

theorem add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun m => f m + g m) := by
  obtain ⟨a, b, hb⟩ := hf
  obtain ⟨a', b', hb'⟩ := hg
  refine ⟨a + a', max b b', fun m => ?_⟩
  have h1 : (m + 1) ^ b ≤ (m + 1) ^ max b b' := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : (m + 1) ^ b' ≤ (m + 1) ^ max b b' := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc f m + g m ≤ a * (m + 1) ^ b + a' * (m + 1) ^ b' := Nat.add_le_add (hb m) (hb' m)
    _ ≤ a * (m + 1) ^ max b b' + a' * (m + 1) ^ max b b' :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (a + a') * (m + 1) ^ max b b' := by ring

theorem mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun m => f m * g m) := by
  obtain ⟨a, b, hb⟩ := hf
  obtain ⟨a', b', hb'⟩ := hg
  refine ⟨a * a', b + b', fun m => ?_⟩
  calc f m * g m ≤ (a * (m + 1) ^ b) * (a' * (m + 1) ^ b') := Nat.mul_le_mul (hb m) (hb' m)
    _ = a * a' * (m + 1) ^ (b + b') := by ring

theorem pow {f : ℕ → ℕ} (hf : PolyBounded f) (p : ℕ) : PolyBounded (fun m => f m ^ p) := by
  obtain ⟨a, b, hb⟩ := hf
  refine ⟨a ^ p, b * p, fun m => ?_⟩
  calc f m ^ p ≤ (a * (m + 1) ^ b) ^ p := Nat.pow_le_pow_left (hb m) p
    _ = a ^ p * (m + 1) ^ (b * p) := by rw [mul_pow, ← pow_mul]

end PolyBounded

/-- The values at `J` columns of a relation are at most `|J|` times its rows. -/
theorem Relation.card_valsAtCols_le {n : ℕ} (r : Multiset (Tuple T n)) (J : Finset (Fin n)) :
    (Relation.valsAtCols r J).card ≤ J.card * Multiset.card r :=
  Finset.card_biUnion_le_card_mul _ _ _ (fun _ _ =>
    le_trans (Multiset.toFinset_card_le _) (le_of_eq (Multiset.card_map _ _)))

omit [ValueType T] in
/-- There are `(2(|S|+1))^c · 2^(c·c)` order types over `S` of `c` parameters. -/
theorem card_ordType (S : Finset T) (c : ℕ) :
    Fintype.card (OrdType S c) = (2 * (S.card + 1)) ^ c * 2 ^ (c * c) := by
  show Fintype.card ((Fin c → Fin (S.card + 1) × Bool) × (Fin c → Fin c → Bool)) = _
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]
  ring

/-- The representative values of a query are at most the order types times
a bound on each. -/
theorem AggQueryIn.card_repVals_le (S : Finset T) {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (Q : AggQueryIn T c n κ l) (J : Finset (Fin n)) (D : Database T)
    (N : ℕ) (hN : ∀ ω : OrdType S c,
      (Relation.valsAtCols (Q.evaluatePlain D (ordRep S c ω)) J).card ≤ N) :
    (Q.repVals S J D).card ≤ (2 * (S.card + 1)) ^ c * 2 ^ (c * c) * N := by
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ _ (fun ω _ => hN ω)) ?_
  rw [Finset.card_univ, card_ordType]

/-- The values of a query's input at an aggregating node lie in the base
set, the input's count types and the context: a finite set. -/
theorem AggQueryIn.valsIn_of_countTypes {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) {B : Finset T}
    (hν : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) (h0 : (0 : T) ∈ B)
    {c m : ℕ} {κ : Fin m → ColKind} (q : AggQueryIn T c m κ) (hs : q.inSig {cnt})
    (hh : q.hygienic) (D : Database T)
    (hD : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
      ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B)
    (hc : ∀ a ∈ q.allConsts, a ∈ B) (γ : Fin c → T) :
    ∀ u, Multiset.Mem (q.evaluatePlain D γ) u → ∀ j,
      u j ∈ Union.union (Union.union B (q.countTypes B D)) (Finset.univ.image γ) := by
  have hcv := AggQueryIn.countValsAll_subset hcnt hν h0 q hs hh
    (fun p hp => absurd hp List.not_mem_nil) D D (fun _ _ _ => rfl) (fun p hp _ => hD p hp) hc
  refine AggQueryIn.valsIn_evaluatePlain q hs D γ
    (↑(Union.union (Union.union B (q.countTypes B D)) (Finset.univ.image γ)) : Set T)
    (fun p hp r hr u hu j => Finset.mem_coe.mpr (Finset.mem_union_left _
      (Finset.mem_union_left _ (hD p hp r hr u hu j))))
    (fun j => Finset.mem_coe.mpr (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)))
    (fun a ha => Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (hc a ha))))
    (fun v hv => Finset.mem_coe.mpr (Finset.mem_union_left _ (hcv hv)))

/-- A grouping has at most `|V|^n₁` groups, `V` the values of its input. -/
theorem AggQueryIn.card_gamma_le {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) {B : Finset T}
    (hν : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) (h0 : (0 : T) ∈ B)
    {c m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (q : AggQueryIn T c m (ColKind.allReg m))
    (keep : Fin n₂ → Option (Selection T m)) (ord : GroupOrder T m) (hs : q.inSig {cnt})
    (hh : q.hygienic) (D : Database T)
    (hD : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
      ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B)
    (hc : ∀ a ∈ q.allConsts, a ∈ B) (γ : Fin c → T) :
    Multiset.card ((AggQueryIn.Gamma is ts fs q keep ord).evaluatePlain D γ
      : Multiset (Tuple T (n₁ + n₂))) ≤ ((Union.union B (q.countTypes B D)).card + c) ^ n₁ := by
  have hvals := AggQueryIn.valsIn_of_countTypes hcnt hν h0 q hs hh D hD hc γ
  simp only [AggQueryIn.evaluatePlain]
  rw [Multiset.card_map]
  refine le_trans (card_le_pow_of_nodup_valsIn
    (V := Union.union (Union.union B (q.countTypes B D)) (Finset.univ.image γ))
    (Multiset.nodup_dedup _) ?_) (Nat.pow_le_pow_left ?_ _)
  · intro g hg k
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hg)
    exact hvals x hx (is k)
  · exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left
      (le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin])) _)

/-- A second-level aggregation has at most `|V|^n₁` groups. -/
theorem AggQueryIn.card_gammaNest_le {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) {B : Finset T}
    (hν : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) (h0 : (0 : T) ∈ B)
    {c m n₁ : ℕ} {κ : Fin m → ColKind} (is : Tuple (Fin m) n₁) (his : ∀ k, κ (is k) ≠ ColKind.agg)
    (p : ProjColIn T c κ) (f : Multiset T → T) (q : AggQueryIn T c m κ) (hs : q.inSig {cnt})
    (hh : q.hygienic) (D : Database T)
    (hD : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
      ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B)
    (hc : ∀ a ∈ q.allConsts, a ∈ B) (γ : Fin c → T) :
    Multiset.card ((AggQueryIn.GammaNest is his p f q).evaluatePlain D γ
      : Multiset (Tuple T (n₁ + 1))) ≤ ((Union.union B (q.countTypes B D)).card + c) ^ n₁ := by
  have hvals := AggQueryIn.valsIn_of_countTypes hcnt hν h0 q hs hh D hD hc γ
  simp only [AggQueryIn.evaluatePlain]
  rw [Multiset.card_map]
  refine le_trans (card_le_pow_of_nodup_valsIn
    (V := Union.union (Union.union B (q.countTypes B D)) (Finset.univ.image γ))
    (Multiset.nodup_dedup _) ?_) (Nat.pow_le_pow_left ?_ _)
  · intro g hg k
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hg)
    exact hvals x hx (is k)
  · exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left
      (le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin])) _)

/-- A window's column takes at most `(|V|+1)^n` values, `V` the values of
its input: it is a function of the row's regular columns. -/
theorem AggQueryIn.card_win_vals_le {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) {B : Finset T}
    (hν : ∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) (h0 : (0 : T) ∈ B)
    {c n m p : ℕ} {κ : Fin n → ColKind} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (q : AggQueryIn T c n κ) (hrr : WinReadsReg κ P O t) (dist : Bool)
    (keep : Option (Selection T n)) (hs : q.inSig {cnt}) (hh : q.hygienic) (D : Database T)
    (hD : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
      ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B)
    (hc : ∀ a ∈ q.allConsts, a ∈ B) (γ : Fin c → T) :
    (Relation.valsAtCols ((AggQueryIn.Win P O o w t f q hrr dist keep).evaluatePlain D γ
        : Multiset (Tuple T (n + 1))) {Fin.last n}).card
      ≤ ((Union.union B (q.countTypes B D)).card + c + 1) ^ n := by
  have hvals := AggQueryIn.valsIn_of_countTypes hcnt hν h0 q hs hh D hD hc γ
  set V : Finset T := Union.union (Union.union B (q.countTypes B D)) (Finset.univ.image γ) with hV
  have hcardV : V.card ≤ (Union.union B (q.countTypes B D)).card + c :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left
      (le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin])) _)
  -- the column is a function of the read row
  simp only [AggQueryIn.evaluatePlain]
  unfold Relation.valsAtCols
  rw [Finset.singleton_biUnion, Multiset.map_map]
  have hmapeq : (q.evaluatePlain D γ : Multiset (Tuple T n)).map
        ((fun u : Tuple T (n + 1) => u (Fin.last n)) ∘ (fun u : Tuple T n =>
          (Fin.snoc u (ValueFrame.windowValueOpt P O o w t (if dist then f.distinct else f) keep
            ((q.evaluatePlain D γ : Multiset (Tuple T n)).map (ColKind.readTuple κ))
            (ColKind.readTuple κ u) γ) : Tuple T (n + 1))))
      = ((q.evaluatePlain D γ : Multiset (Tuple T n)).map (ColKind.readTuple κ)).map
          (fun v => ValueFrame.windowValueOpt P O o w t (if dist then f.distinct else f) keep
            ((q.evaluatePlain D γ : Multiset (Tuple T n)).map (ColKind.readTuple κ)) v γ) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    show (Fin.snoc u _ : Tuple T (n + 1)) (Fin.last n) = _
    rw [Fin.snoc_last]
    rfl
  erw [hmapeq]
  rw [Multiset.toFinset_map]
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_def, Multiset.toFinset_val]
  refine le_trans (card_le_pow_of_nodup_valsIn (V := insert 0 V) (Multiset.nodup_dedup _) ?_)
    (Nat.pow_le_pow_left ?_ _)
  · intro v hv j
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hv)
    show (match (κ j).base with | ColKind.agg => 0 | _ => x j) ∈ insert 0 V
    cases (κ j).base
    · exact Finset.mem_insert_of_mem (hvals x hx j)
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hvals x hx j)
  · exact le_trans (Finset.card_insert_le _ _) (by omega)

/-- **There are polynomially many count types**: the count types of a
hygienic query of the minimal signature over a base set holding its
instance values, its constants, the zero and the null number at most a
polynomial, fixed by the query, in the size of the base set. -/
theorem AggQueryIn.exists_polyBound_countTypes {cnt : SeqAggFunc T} (hcnt : cnt.IsCount) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig {cnt} → q.hygienic → (∀ p ∈ l, q.noMention p.1) →
      ∃ f : ℕ → ℕ, PolyBounded f ∧ ∀ (B : Finset T) (D : Database T),
        (∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) → (0 : T) ∈ B →
        (∀ p ∈ q.leaves, (p.2, p.1) ∉ l → ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
          ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B) →
        (∀ a ∈ q.allConsts, a ∈ B) → (q.countTypes B D).card ≤ f B.card := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ _ _ => ⟨fun _ => 0, PolyBounded.const 0, fun _ _ _ _ _ _ => le_refl _⟩
  | Hole n s => exact fun _ _ _ => ⟨fun _ => 0, PolyBounded.const 0, fun _ _ _ _ _ _ => le_refl _⟩
  | Empty => exact fun _ _ _ => ⟨fun _ => 0, PolyBounded.const 0, fun _ _ _ _ _ _ => le_refl _⟩
  | Proj ps q ih =>
    intro hs hh hn
    obtain ⟨f, hf, hb⟩ := ih hs.2 hh hn
    exact ⟨f, hf, fun B D hν h0 hD hc => hb B D hν h0 hD
      (fun a ha => hc a (Finset.mem_union_right _ ha))⟩
  | Sel φ q _ ih =>
    intro hs hh hn
    obtain ⟨f, hf, hb⟩ := ih hs.2 hh hn
    exact ⟨f, hf, fun B D hν h0 hD hc => hb B D hν h0 hD
      (fun a ha => hc a (Finset.mem_union_right _ ha))⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn
    obtain ⟨f₁, hf₁, hb₁⟩ := ih₁ hs.1 hh.1 (fun p hp => (hn p (List.mem_append_left _ hp)).1)
    obtain ⟨f₂, hf₂, hb₂⟩ := ih₂ hs.2 hh.2 (fun p hp => (hn p (List.mem_append_right _ hp)).2)
    refine ⟨fun m => f₁ m + f₂ m, hf₁.add hf₂, fun B D hν h0 hD hc => ?_⟩
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · refine hb₁ B D hν h0 (fun p hp hpl => hD p (List.mem_append_left _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim hpl (fun h₂ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₁ (hn _ (List.mem_append_right _ h₂)).1 p hp rfl))))
        (fun a ha => hc a (Finset.mem_union_left _ ha))
    · refine hb₂ B D hν h0 (fun p hp hpl => hD p (List.mem_append_right _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim (fun h₁ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₂ (hn _ (List.mem_append_left _ h₁)).2 p hp rfl))
          hpl))
        (fun a ha => hc a (Finset.mem_union_right _ ha))
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn
    obtain ⟨f₁, hf₁, hb₁⟩ := ih₁ hs.1 hh.1 (fun p hp => (hn p hp).1)
    obtain ⟨f₂, hf₂, hb₂⟩ := ih₂ hs.2 hh.2 (fun p hp => absurd hp List.not_mem_nil)
    refine ⟨fun m => f₁ m + f₂ m, hf₁.add hf₂, fun B D hν h0 hD hc => ?_⟩
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · exact hb₁ B D hν h0 (fun p hp hpl => hD p (List.mem_append_left _ hp) hpl)
        (fun a ha => hc a (Finset.mem_union_left _ ha))
    · exact hb₂ B D hν h0 (fun p hp _ => hD p (List.mem_append_right _ hp) (fun hmem =>
        absurd rfl (AggQueryIn.ne_of_noMention_of_mem_leaves q₂ (hn _ hmem).2 p hp)))
        (fun a ha => hc a (Finset.mem_union_right _ ha))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn
    obtain ⟨f₁, hf₁, hb₁⟩ := ih₁ hs.1 hh.1 (fun p hp => (hn p (List.mem_append_left _ hp)).1)
    obtain ⟨f₂, hf₂, hb₂⟩ := ih₂ hs.2 hh.2 (fun p hp => (hn p (List.mem_append_right _ hp)).2)
    refine ⟨fun m => f₁ m + f₂ m, hf₁.add hf₂, fun B D hν h0 hD hc => ?_⟩
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · refine hb₁ B D hν h0 (fun p hp hpl => hD p (List.mem_append_left _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim hpl (fun h₂ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₁ (hn _ (List.mem_append_right _ h₂)).1 p hp rfl))))
        (fun a ha => hc a (Finset.mem_union_left _ ha))
    · refine hb₂ B D hν h0 (fun p hp hpl => hD p (List.mem_append_right _ hp) (fun hmem =>
        (List.mem_append.mp hmem).elim (fun h₁ => hpl
          (AggQueryIn.mem_index_of_mem_leaves q₂ (hn _ (List.mem_append_left _ h₁)).2 p hp rfl))
          hpl))
        (fun a ha => hc a (Finset.mem_union_right _ ha))
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hs hh hn
    obtain ⟨f₁, hf₁, hb₁⟩ := ih₁ hs.1 hh.1 (fun p hp => absurd hp List.not_mem_nil)
    obtain ⟨f₂, hf₂, hb₂⟩ := ih₂ hs.2 hh.2 (fun p hp => absurd hp List.not_mem_nil)
    refine ⟨fun m => f₁ m + f₂ m, hf₁.add hf₂, fun B D hν h0 hD hc => ?_⟩
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · exact hb₁ B D hν h0 (fun p hp _ => hD p (List.mem_append_left _ hp) List.not_mem_nil)
        (fun a ha => hc a (Finset.mem_union_left _ ha))
    · exact hb₂ B D hν h0 (fun p hp _ => hD p (List.mem_append_right _ hp) List.not_mem_nil)
        (fun a ha => hc a (Finset.mem_union_right _ ha))
  | Alt k hk q ih => exact ih
  | Retag hk q ih => exact ih
  | Mu s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs hh hn
    obtain ⟨f₀, hf₀, hb₀⟩ := ih₀ hs.1 hh.2.2.1 (fun p hp => absurd hp List.not_mem_nil)
    obtain ⟨f₁, hf₁, hb₁⟩ := ih₁ hs.2 hh.2.2.2 (fun p hp => by
      rw [List.mem_singleton.mp hp]; exact hh.2.1)
    refine ⟨fun m => f₀ m + f₁ m, hf₀.add hf₁, fun B D hν h0 hD hc => ?_⟩
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · exact hb₀ B D hν h0 (fun p hp _ => hD p (List.mem_append_left _ hp) List.not_mem_nil)
        (fun a ha => hc a (Finset.mem_union_left _ ha))
    · refine hb₁ B D hν h0 (fun p hp hpl => ?_) (fun a ha => hc a (Finset.mem_union_right _ ha))
      obtain ⟨k, t⟩ := p
      have hne : (k, t) ≠ (m, s) := fun h => hpl (by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact List.mem_singleton_self _)
      exact hD (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
        List.not_mem_nil
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' m
    intro hs hh hn
    obtain ⟨f₀, hf₀, hb₀⟩ := ih₀ hs.1 hh.2.2.1 (fun p hp => absurd hp List.not_mem_nil)
    obtain ⟨f₁, hf₁, hb₁⟩ := ih₁ hs.2 hh.2.2.2 (fun p hp => by
      rw [List.mem_singleton.mp hp]; exact hh.2.1)
    refine ⟨fun m => f₀ m + f₁ m, hf₀.add hf₁, fun B D hν h0 hD hc => ?_⟩
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · exact hb₀ B D hν h0 (fun p hp _ => hD p (List.mem_append_left _ hp) List.not_mem_nil)
        (fun a ha => hc a (Finset.mem_union_left _ ha))
    · refine hb₁ B D hν h0 (fun p hp hpl => ?_) (fun a ha => hc a (Finset.mem_union_right _ ha))
      obtain ⟨k, t⟩ := p
      have hne : (k, t) ≠ (m, s) := fun h => hpl (by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact List.mem_singleton_self _)
      exact hD (k, t) (List.mem_append_right _ (List.mem_filter.mpr ⟨hp, decide_eq_true hne⟩))
        List.not_mem_nil
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂
    intro hs hh hn
    obtain ⟨fq, hfq, hb⟩ := ih hs.2.2.2 hh (fun p hp => absurd hp List.not_mem_nil)
    refine ⟨fun m => fq m + ((2 * (m + fq m + 1)) ^ c' * 2 ^ (c' * c'))
        * (n₂ * (m + fq m + c') ^ n₁),
      hfq.add ((((PolyBounded.const 2).mul ((PolyBounded.id.add hfq).add
        (PolyBounded.const 1))).pow c' |>.mul (PolyBounded.const (2 ^ (c' * c')))).mul
        ((PolyBounded.const n₂).mul (((PolyBounded.id.add hfq).add (PolyBounded.const c')).pow n₁))),
      fun B D hν h0 hD hc => ?_⟩
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hBq := hb B D hν h0 (fun p hp _ => hDq p hp) hcq
    have hS : (Union.union B (q.countTypes B D)).card ≤ B.card + fq B.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left hBq _)
    show (Union.union (q.countTypes B D) _).card ≤ _
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add hBq ?_)
    refine le_trans (AggQueryIn.card_repVals_le _ _ _ D
      (n₂ * ((Union.union B (q.countTypes B D)).card + c') ^ n₁) (fun ω => ?_)) ?_
    · refine le_trans (Relation.card_valsAtCols_le _ _) (Nat.mul_le_mul ?_
        (AggQueryIn.card_gamma_le hcnt hν h0 is ts fs q keep ord hs.2.2.2 hh D hDq hcq
          (ordRep (Union.union B (q.countTypes B D)) c' ω)))
      exact le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin])
    · refine Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  | GammaScalar ts fs q ord ih =>
    rename_i c' m n₂
    intro hs hh hn
    obtain ⟨fq, hfq, hb⟩ := ih hs.2.2 hh (fun p hp => absurd hp List.not_mem_nil)
    refine ⟨fun m => fq m + ((2 * (m + fq m + 1)) ^ c' * 2 ^ (c' * c')) * n₂,
      hfq.add ((((PolyBounded.const 2).mul ((PolyBounded.id.add hfq).add
        (PolyBounded.const 1))).pow c' |>.mul (PolyBounded.const (2 ^ (c' * c')))).mul
        (PolyBounded.const n₂)),
      fun B D hν h0 hD hc => ?_⟩
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hBq := hb B D hν h0 (fun p hp _ => hDq p hp) hcq
    have hS : (Union.union B (q.countTypes B D)).card ≤ B.card + fq B.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left hBq _)
    show (Union.union (q.countTypes B D) _).card ≤ _
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add hBq ?_)
    refine le_trans (AggQueryIn.card_repVals_le _ _ _ D n₂ (fun ω => ?_)) ?_
    · refine le_trans (Relation.card_valsAtCols_le _ _) ?_
      rw [Finset.card_univ, Fintype.card_fin]
      simp only [AggQueryIn.evaluatePlain]
      rw [Multiset.coe_card, List.length_singleton, Nat.mul_one]
    · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
  | GammaNest is his p f q ih =>
    rename_i c' m n₁ κ'
    intro hs hh hn
    obtain ⟨fq, hfq, hb⟩ := ih hs.2.2 hh (fun p hp => absurd hp List.not_mem_nil)
    refine ⟨fun m => fq m + ((2 * (m + fq m + 1)) ^ c' * 2 ^ (c' * c'))
        * (1 * (m + fq m + c') ^ n₁),
      hfq.add ((((PolyBounded.const 2).mul ((PolyBounded.id.add hfq).add
        (PolyBounded.const 1))).pow c' |>.mul (PolyBounded.const (2 ^ (c' * c')))).mul
        ((PolyBounded.const 1).mul (((PolyBounded.id.add hfq).add (PolyBounded.const c')).pow n₁))),
      fun B D hν h0 hD hc => ?_⟩
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hBq := hb B D hν h0 (fun p hp _ => hDq p hp) hcq
    have hS : (Union.union B (q.countTypes B D)).card ≤ B.card + fq B.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left hBq _)
    show (Union.union (q.countTypes B D) _).card ≤ _
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add hBq ?_)
    refine le_trans (AggQueryIn.card_repVals_le _ _ _ D
      (1 * ((Union.union B (q.countTypes B D)).card + c') ^ n₁) (fun ω => ?_)) ?_
    · refine le_trans (Relation.card_valsAtCols_le _ _) (Nat.mul_le_mul (le_of_eq ?_)
        (AggQueryIn.card_gammaNest_le hcnt hν h0 is his p f q hs.2.2 hh D hDq hcq
          (ordRep (Union.union B (q.countTypes B D)) c' ω)))
      exact Finset.card_singleton _
    · refine Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  | ProvSum is his t q ih => exact fun hs => hs.elim
  | GammaTok is his ts fs a q keep ih => exact fun hs => hs.elim
  | Win P O o w t f q hrr dist keep ih =>
    rename_i c' n' m' p' κ'
    intro hs hh hn
    obtain ⟨fq, hfq, hb⟩ := ih hs.2.2.2 hh (fun p hp => absurd hp List.not_mem_nil)
    refine ⟨fun m => fq m + ((2 * (m + fq m + 1)) ^ c' * 2 ^ (c' * c'))
        * (m + fq m + c' + 1) ^ n',
      hfq.add ((((PolyBounded.const 2).mul ((PolyBounded.id.add hfq).add
        (PolyBounded.const 1))).pow c' |>.mul (PolyBounded.const (2 ^ (c' * c')))).mul
        ((((PolyBounded.id.add hfq).add (PolyBounded.const c')).add (PolyBounded.const 1)).pow n')),
      fun B D hν h0 hD hc => ?_⟩
    have hDq : ∀ p ∈ q.leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B := fun p hp => hD p hp List.not_mem_nil
    have hcq : ∀ a ∈ q.allConsts, a ∈ B := fun a ha => hc a (Finset.mem_union_right _ ha)
    have hBq := hb B D hν h0 (fun p hp _ => hDq p hp) hcq
    have hS : (Union.union B (q.countTypes B D)).card ≤ B.card + fq B.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left hBq _)
    show (Union.union (q.countTypes B D) _).card ≤ _
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add hBq ?_)
    refine le_trans (AggQueryIn.card_repVals_le _ _ _ D
      (((Union.union B (q.countTypes B D)).card + c' + 1) ^ n') (fun ω => ?_)) ?_
    · exact AggQueryIn.card_win_vals_le hcnt hν h0 P O o w t f q hrr dist keep hs.2.2.2 hh D hDq
        hcq _
    · refine Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
        (Nat.pow_le_pow_left (by omega) _)
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hs => hs.elim

/-- **A set recursion's fixpoint is polynomially bounded in the number of
values it may read**: its rows are duplicate-free tuples over the base set
and the count types, of which there are polynomially many. -/
theorem AggQueryIn.exists_card_bound_muSet {cnt : SeqAggFunc T} (hcnt : cnt.IsCount)
    {c n : ℕ} (s : String) (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hs : (AggQueryIn.MuSet s q₀ q₁).inSig {cnt}) (hh : (AggQueryIn.MuSet s q₀ q₁).hygienic) :
    ∃ f : ℕ → ℕ, PolyBounded f ∧ ∀ (B : Finset T) (D : Database T) (γ : Fin c → T),
      (∀ ν : T, ValueType.nullVal = some ν → ν ∈ B) → (0 : T) ∈ B → (∀ j, γ j ∈ B) →
      (∀ p ∈ (AggQueryIn.MuSet s q₀ q₁).leaves, ∀ r : Relation T p.1, D.find p.1 p.2 = some r →
        ∀ u, Multiset.Mem r u → ∀ j, u j ∈ B) →
      (∀ a ∈ (AggQueryIn.MuSet s q₀ q₁).allConsts, a ∈ B) →
      Multiset.card ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ : Multiset (Tuple T n))
        ≤ f B.card := by
  obtain ⟨fM, hfM, hb⟩ := AggQueryIn.exists_polyBound_countTypes hcnt (AggQueryIn.MuSet s q₀ q₁)
    hs hh (fun p hp => absurd hp List.not_mem_nil)
  refine ⟨fun m => (m + fM m) ^ n, (PolyBounded.id.add hfM).pow n, fun B D γ hν h0 hγ hD hc => ?_⟩
  have hcv := AggQueryIn.countValsAll_subset hcnt hν h0 (AggQueryIn.MuSet s q₀ q₁) hs hh
    (fun p hp => absurd hp List.not_mem_nil) D D (fun _ _ _ => rfl) (fun p hp _ => hD p hp) hc
  have hvals := AggQueryIn.valsIn_evaluatePlain (AggQueryIn.MuSet s q₀ q₁) hs D γ
    (↑(Union.union B ((AggQueryIn.MuSet s q₀ q₁).countTypes B D)) : Set T)
    (fun p hp r hr u hu j => Finset.mem_coe.mpr (Finset.mem_union_left _ (hD p hp r hr u hu j)))
    (fun j => Finset.mem_coe.mpr (Finset.mem_union_left _ (hγ j)))
    (fun a ha => Finset.mem_coe.mpr (Finset.mem_union_left _ (hc a ha))) hcv
  have hnd : ((AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ : Multiset (Tuple T n)).Nodup := by
    show (muIter _ (muFixIdx _)).Nodup
    rw [muIter_eq_iterate]
    exact nodup_iterate_dedup _ _
  refine le_trans (card_le_pow_of_nodup_valsIn hnd hvals) (Nat.pow_le_pow_left ?_ _)
  exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (hb B D hν h0
    (fun p hp _ => hD p hp) hc) _)
