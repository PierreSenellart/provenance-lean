/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.AnnotatedMuUnion
public import Provenance.AnnotatedBasis
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Provenance.AnnotatedProd
import Provenance.HavingQueryCorrectness
import all Provenance.AggQuery
import all Provenance.AggQueryAdequacy
import all Provenance.AnnotatedMuUnion
import all Provenance.AnnotatedProd
import all Provenance.MuUnion
import all Provenance.PathSum
import all Provenance.SemiringWithMonus

/-!
# The set recursion from the bag recursion and `ε`: the two counters

Both counters rest on one invariant (`AggQueryIn.rowBd_evaluate`): a value
enters a row from a row holding it, so the row's annotation is built from
the annotations of rows holding it by operations that keep any bound
`BdClosed` describes. Two bounds serve: below the value's weight where `δ`
is the identity (`leBd`), and `𝟘` where every row holding the value is
annotated `𝟘`, which holds in every m-semiring (`zeroBd`).

**Where `δ` is the support map** (`muSetSim_correct_succ`), a counter
holding a value carried only by rows annotated `𝟘` is annotated `𝟘`, and
so is every derivation through a tuple holding one: the derivations of
non-zero weight live on the tuples holding no such value, and the
successor counter runs over the counters annotated `𝟙`. Rows annotated `𝟘`
therefore need no fence, and the simulation is exact.

**Where `δ` is the identity** – the Boolean algebras and the min-max
semirings – a grouping annotates a counter value by the sum of the
annotations of the rows holding it, not by `𝟙`, so the successor counter
of `AnnotatedMuUnion` multiplies the derivations it is paired with by
annotations it should not. The *all-chains* counter does not: a round
pairs each derived tuple with every counter above the current one, and a
derivation is paired with every chain of counters as long as itself
(`PathSum.ChainSpec`). Such a semiring is absorptive with an idempotent
`⊗`, so what a derivation must meet is one chain whose annotations are
all above its own weight; then the chain absorbs nothing of it.

A chain over the values the derivation's tuples hold is one: every row
holding a value of the instance is annotated below that value's weight
(`AggQueryIn.rowBd_evaluate`), a tuple being free to repeat what its
predecessor holds, the query's constants and its context. There are as
many such chains as the tuples a derivation through distinct tuples can
visit, at width `(2c + 2) n`, which needs no bound of the plain semantics:
counting the tuples over those values is enough, for either counter.
-/

@[expose] public section

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

namespace AggQueryIn

/-! ## The relations a query reads off the instance -/

/-- **The relations a query reads off the instance**, each with its arity:
its `Rel` leaves, the holes left out. -/
def relLeaves : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → List (ℕ × String)
  | _, _, _, _, .Rel k s => [(k, s)]
  | _, _, _, _, .Hole _ _ _ => []
  | _, _, _, _, .Param _ _ => []
  | _, _, _, _, .Empty => []
  | _, _, _, _, .Proj _ q => q.relLeaves
  | _, _, _, _, .Sel _ q _ => q.relLeaves
  | _, _, _, _, .Prod q₁ q₂ => q₁.relLeaves ++ q₂.relLeaves
  | _, _, _, _, .Apply q₁ q₂ => q₁.relLeaves ++ q₂.relLeaves
  | _, _, _, _, .Sum q₁ q₂ => q₁.relLeaves ++ q₂.relLeaves
  | _, _, _, _, .Dedup q => q.relLeaves
  | _, _, _, _, .Diff q₁ q₂ => q₁.relLeaves ++ q₂.relLeaves
  | _, _, _, _, .Explode _ _ q => q.relLeaves
  | _, _, _, _, .Retag _ q => q.relLeaves
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.relLeaves ++ q₁.relLeaves
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.relLeaves ++ q₁.relLeaves
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.relLeaves
  | _, _, _, _, .GammaScalar _ _ q _ => q.relLeaves
  | _, _, _, _, .GammaNest _ _ _ _ q => q.relLeaves
  | _, _, _, _, .ProvSum _ _ _ q => q.relLeaves
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.relLeaves
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.relLeaves
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.relLeaves

omit [ValueType T] in
/-- A relation a query reads off the instance does not carry a name it does
not mention. -/
private theorem ne_of_mem_relLeaves {t : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention t → ∀ p ∈ q.relLeaves, p.2 ≠ t := by
  intro c n κ l q
  induction q with
  | Rel k s =>
    intro h p hp
    rw [List.mem_singleton.1 hp]
    exact h
  | Hole _ _ _ => exact fun _ p hp => absurd hp List.not_mem_nil
  | Param _ _ => exact fun _ p hp => absurd hp List.not_mem_nil
  | Empty => exact fun _ p hp => absurd hp List.not_mem_nil
  | Proj _ q ih => exact fun h => ih h
  | Sel _ q _ ih => exact fun h => ih h
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact (List.mem_append.1 hp).elim (ih₁ h.1 p) (ih₂ h.2 p)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact (List.mem_append.1 hp).elim (ih₁ h.1 p) (ih₂ h.2 p)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact (List.mem_append.1 hp).elim (ih₁ h.1 p) (ih₂ h.2 p)
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact (List.mem_append.1 hp).elim (ih₁ h.1 p) (ih₂ h.2 p)
  | Explode _ _ q ih => exact fun h => ih h
  | Retag _ q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro h p hp
    exact (List.mem_append.1 hp).elim (ih₀ h.1 p) (ih₁ h.2 p)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro h p hp
    exact (List.mem_append.1 hp).elim (ih₀ h.1 p) (ih₁ h.2 p)
  | Gamma _ _ _ q _ _ ih => exact fun h => ih h
  | GammaScalar _ _ q _ ih => exact fun h => ih h
  | GammaNest _ _ _ _ q ih => exact fun h => ih h
  | ProvSum _ _ _ q ih => exact fun h => ih h
  | GammaTok _ _ _ _ _ q _ ih => exact fun h => ih h
  | Win _ _ _ _ _ _ q _ _ _ ih => exact fun h => ih h
  | WinExpr _ _ _ _ _ _ _ q _ ih => exact fun h => ih h

omit [ValueType T] in
/-- **A hygienic query's relations off the instance are among its
leaves**: a body's `Rel` leaves do not carry its recursion's name. -/
private theorem mem_leaves_of_mem_relLeaves :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.hygienic → ∀ p ∈ q.relLeaves, p ∈ q.leaves := by
  intro c n κ l q
  induction q with
  | Rel k s => exact fun _ p hp => hp
  | Hole _ _ _ => exact fun _ p hp => absurd hp List.not_mem_nil
  | Param _ _ => exact fun _ p hp => absurd hp List.not_mem_nil
  | Empty => exact fun _ p hp => absurd hp List.not_mem_nil
  | Proj _ q ih => exact fun h => ih h
  | Sel _ q _ ih => exact fun h => ih h
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact List.mem_append.2 ((List.mem_append.1 hp).imp (ih₁ h.1 p) (ih₂ h.2 p))
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact List.mem_append.2 ((List.mem_append.1 hp).imp (ih₁ h.1 p) (ih₂ h.2 p))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact List.mem_append.2 ((List.mem_append.1 hp).imp (ih₁ h.1 p) (ih₂ h.2 p))
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro h p hp
    exact List.mem_append.2 ((List.mem_append.1 hp).imp (ih₁ h.1 p) (ih₂ h.2 p))
  | Explode _ _ q ih => exact fun h => ih h
  | Retag _ q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro h p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact List.mem_append_left _ (ih₀ h.2.2.1 p hp)
    · refine List.mem_append_right _ (List.mem_filter.2 ⟨ih₁ h.2.2.2 p hp, ?_⟩)
      have := ne_of_mem_relLeaves q₁ h.2.1 p hp
      simp only [ne_eq, decide_eq_true_eq]
      exact fun he => this (by rw [he])
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro h p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact List.mem_append_left _ (ih₀ h.2.2.1 p hp)
    · refine List.mem_append_right _ (List.mem_filter.2 ⟨ih₁ h.2.2.2 p hp, ?_⟩)
      have := ne_of_mem_relLeaves q₁ h.2.1 p hp
      simp only [ne_eq, decide_eq_true_eq]
      exact fun he => this (by rw [he])
  | Gamma _ _ _ q _ _ ih => exact fun h => ih h
  | GammaScalar _ _ q _ ih => exact fun h => ih h
  | GammaNest _ _ _ _ q ih => exact fun h => ih h
  | ProvSum _ _ _ q ih => exact fun h => ih h
  | GammaTok _ _ _ _ _ q _ ih => exact fun h => ih h
  | Win _ _ _ _ _ _ q _ _ _ ih => exact fun h => ih h
  | WinExpr _ _ _ _ _ _ _ q _ ih => exact fun h => ih h

/-! ## A row is below the weights of the values it holds -/

/-- **A bound on the rows holding a value**: a property `Bd v a` of a value
and an annotation that every operator keeps – a product keeps it from
either factor, a sum from both summands, a difference from its left side,
and `δ` from its argument. -/
structure BdClosed (Bd : T → K → Prop) : Prop where
  mul_right : ∀ v a b, Bd v a → Bd v (a * b)
  mul_left : ∀ v a b, Bd v b → Bd v (a * b)
  add : ∀ v a b, Bd v a → Bd v b → Bd v (a + b)
  monus : ∀ v a b, Bd v a → Bd v (a - b)
  delta : ∀ v a, Bd v a → Bd v (SemiringWithMonus.delta a)

/-- **A row is within the bound on its values**: each value it holds is
free (`F`), or its annotation is within the bound `Bd` on that value. -/
def RowBd (F : T → Prop) (Bd : T → K → Prop) {n : ℕ} (r : GenRow T K n) : Prop :=
  ∀ k v, r.fst k = Sum.inl v → F v ∨ Bd v r.snd.finalize

/-- The same for a tuple and its annotation. -/
def TupBd (F : T → Prop) (Bd : T → K → Prop) {n : ℕ} (p : Tuple T n × K) : Prop :=
  ∀ k, F (p.1 k) ∨ Bd (p.1 k) p.2

/-- **The bound of a weight**: a value of `Vl` whose weight `e` is above the
annotation. -/
abbrev leBd (Vl : T → Prop) (e : T → K) (v : T) (a : K) : Prop := Vl v ∧ a ≤ e v

/-- **The bound of a value held by no row of non-zero annotation**: the
annotation is `𝟘` where the value is one of `Z`. -/
abbrev zeroBd (Z : T → Prop) (v : T) (a : K) : Prop := Z v → a = 0

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem ne_zero_of_mem' {α : Type} {s : Multiset α} {a : α} (h : a ∈ s) : s ≠ 0 :=
  fun h0 => by rw [h0] at h; exact Multiset.notMem_zero a h

section Bounds

variable {F : T → Prop} {Bd : T → K → Prop}

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem rowBd_of_tupBd {n : ℕ} {r : GenRow T K n}
    (h : TupBd F Bd (GenRow.plainTuple r.fst, r.snd.finalize)) : RowBd F Bd r := by
  intro k v hk
  have := h k
  simp only [GenRow.plainTuple, hk] at this
  exact this

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tupBd_of_rowBd {n : ℕ} {r : GenRow T K n} (h : RowBd F Bd r)
    (hr : ∀ k, GenValue.kindOf (r.fst k) = ColKind.reg) :
    TupBd F Bd (GenRow.plainTuple r.fst, r.snd.finalize) := by
  intro k
  have hk := hr k
  revert hk
  cases hv : r.fst k with
  | inl v =>
    intro _
    have := h k v hv
    simp only [GenRow.plainTuple, hv]
    exact this
  | inr a => intro hk; exact absurd hk (by simp [GenValue.kindOf])

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem rowBd_ofAnnotated {n : ℕ} {p : AnnotatedTuple T K n} (h : TupBd F Bd (p.1, p.2)) :
    RowBd F Bd (GenRow.ofAnnotated p) := by
  intro k v hk
  simp only [GenRow.ofAnnotated, Sum.inl.injEq] at hk
  subst hk
  have := h k
  simp only [GenRow.ofAnnotated, GenAnn.finalize_of_pending_zero]
  exact this

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A sum of elements below `x` is below `x`, in an absorptive semiring. -/
private theorem msum_le (habs : ∀ a : K, 1 + a = 1) (x : K) :
    ∀ s : Multiset K, (∀ a ∈ s, a ≤ x) → s.sum ≤ x := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; exact zero_le
  | cons a s ih =>
    intro h
    rw [Multiset.sum_cons, ← PathSum.add_self_of_abs habs x]
    exact add_le_add (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- **A sum of a non-empty bag within the bound is.** -/
private theorem BdClosed.sum (hB : BdClosed Bd) (v : T) :
    ∀ s : Multiset K, s ≠ 0 → (∀ a ∈ s, Bd v a) → Bd v s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro h; exact absurd rfl h
  | cons a s ih =>
    intro _ h
    rw [Multiset.sum_cons]
    by_cases hs : s = 0
    · subst hs
      rw [Multiset.sum_zero, add_zero]
      exact h a (Multiset.mem_cons_self a 0)
    · exact hB.add v _ _ (h a (Multiset.mem_cons_self a s))
        (ih hs fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **Duplicate elimination keeps the bound**: a tuple's weight sums
annotations each within it. -/
private theorem tupBd_dedupK (hB : BdClosed Bd) {n : ℕ} {Y : Multiset (Tuple T n × K)}
    (h : ∀ p ∈ Y, TupBd F Bd p) : ∀ p ∈ PathSum.dedupK Y, TupBd F Bd p := by
  intro p hp
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_dedup.1 hu)
  intro k
  by_cases hF : F (q.1 k)
  · exact Or.inl hF
  refine Or.inr (hB.sum _ _ ?_ fun a ha => ?_)
  · exact ne_zero_of_mem' (Multiset.mem_map.2 ⟨q, Multiset.mem_filter.2 ⟨hq, rfl⟩, rfl⟩)
  obtain ⟨q', hq', rfl⟩ := Multiset.mem_map.1 ha
  obtain ⟨hq'Y, hq'e⟩ := Multiset.mem_filter.1 hq'
  have := (h q' hq'Y k).resolve_left (by rw [hq'e]; exact hF)
  rw [hq'e] at this
  exact this

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Where `δ` is the identity, an annotation below a weight is a bound.** -/
private theorem leBd_closed (hδ : ∀ a : K, SemiringWithMonus.delta a = a) (Vl : T → Prop)
    (e : T → K) : BdClosed (leBd Vl e) := by
  have hid : IsDelta (id : K → K) := by
    have h := isDelta_delta (α := K)
    rwa [show SemiringWithMonus.delta = (id : K → K) from funext hδ] at h
  have habs : ∀ a : K, 1 + a = 1 := fun a => by simpa using hid.absorb 1 a
  refine ⟨fun v a b h => ⟨h.1, ?_⟩, fun v a b h => ⟨h.1, ?_⟩, fun v a b ha hb => ⟨ha.1, ?_⟩,
    fun v a b h => ⟨h.1, le_trans (monus_le a b) h.2⟩, fun v a h => by rw [hδ]; exact h⟩
  · rw [mul_comm]; exact le_trans (mul_le_right habs b a) h.2
  · exact le_trans (mul_le_right habs a b) h.2
  · rw [← PathSum.add_self_of_abs habs (e v)]
    exact add_le_add ha.2 hb.2

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- **In every m-semiring, `𝟘` is a bound**: a product with `𝟘`, a sum of
`𝟘`s, `𝟘` minus anything and `δ 𝟘` are `𝟘`. -/
private theorem zeroBd_closed (Z : T → Prop) : BdClosed (K := K) (zeroBd Z) := by
  refine ⟨fun v a b h hz => ?_, fun v a b h hz => ?_, fun v a b ha hb hz => ?_,
    fun v a b h hz => ?_, fun v a h hz => ?_⟩
  · rw [h hz, zero_mul]
  · rw [h hz, mul_zero]
  · rw [ha hz, hb hz, add_zero]
  · rw [h hz, zero_monus]
  · rw [h hz]; exact SemiringWithMonus.delta_zero

end Bounds

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **A column of the minimal signature reads a value it was given**: a
value of the row, a constant, or an outer column the kinds let it read. -/
private theorem projCol_eval_inl_cases {c n : ℕ} {κ : Fin n → ColKind} (p : ProjColIn T c κ)
    (hp : p.noFun = true) {ok : Fin c → Prop} (hok : p.outerOk ok)
    {u : Tuple (GenValue T K) n} (hu : ∀ k, GenValue.kindOf (u k) = (κ k).base)
    (γ : Fin c → T) {v : T} (h : p.eval u γ = Sum.inl v) :
    (∃ k, u k = Sum.inl v) ∨ v ∈ p.consts ∨ ∃ j, ok j ∧ γ j = v := by
  have hterm : ∀ t : TermGIn T c κ, t.noFun = true → t.outerOk ok → t.eval u γ = v →
      (∃ k, u k = Sum.inl v) ∨ v ∈ t.consts ∨ ∃ j, ok j ∧ γ j = v := by
    intro t ht hok' he
    cases t with
    | const a => exact Or.inr (Or.inl (by rw [← he]; exact Finset.mem_singleton_self a))
    | outer j => exact Or.inr (Or.inr ⟨j, hok', he⟩)
    | index k hk =>
      left
      refine ⟨k, ?_⟩
      have hk' := hu k
      rw [hk] at hk'
      simp only [TermGIn.eval] at he
      rcases hv : u k with a | a
      · rw [hv] at he
        exact congrArg Sum.inl he
      · rw [hv] at hk'
        simp [GenValue.kindOf, ColKind.base] at hk'
    | provIndex k hk =>
      left
      refine ⟨k, ?_⟩
      have hk' := hu k
      rw [hk] at hk'
      simp only [TermGIn.eval] at he
      rcases hv : u k with a | a
      · rw [hv] at he
        exact congrArg Sum.inl he
      · rw [hv] at hk'
        simp [GenValue.kindOf, ColKind.base] at hk'
    | cmpAgg _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
    | chiGate _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
    | add _ _ => exact absurd ht (by simp [TermGIn.noFun])
    | sub _ _ => exact absurd ht (by simp [TermGIn.noFun])
    | mul _ _ => exact absurd ht (by simp [TermGIn.noFun])
    | caseWhen _ _ _ _ _ => exact absurd ht (by simp [TermGIn.noFun])
    | coalesce _ _ => exact absurd ht (by simp [TermGIn.noFun])
  cases p with
  | term t => exact hterm t hp hok (Sum.inl.inj h)
  | token k hk => exact Or.inl ⟨k, h⟩
  | aggTerm k hk gf => exact absurd hp (by simp [ProjColIn.noFun])
  | aggTermOf k hk t =>
    exfalso
    have hk' := hu k
    rw [hk] at hk'
    have h' : Sum.map t.unary (AggTok.postcompTerm t) (u k) = Sum.inl v := h
    rcases hv : u k with a | a
    · rw [hv] at hk'
      simp [GenValue.kindOf, ColKind.base] at hk'
    · rw [hv] at h'
      simp at h'
  | provTerm t => exact hterm t hp hok (Sum.inl.inj h)

/-- The holes of an environment bound to rows within the bound. -/
def HolesBd (F : T → Prop) (Bd : T → K → Prop) (l : List (String × ℕ)) (E : EvalEnv T K) :
    Prop :=
  ∀ p ∈ l, ∀ r ∈ E.holes p.1 p.2, RowBd F Bd r

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem holesBd_assignHole {F : T → Prop} {Bd : T → K → Prop} {E : EvalEnv T K} (s : String)
    {n : ℕ} {X : Multiset (GenRow T K n)} (hX : ∀ r ∈ X, RowBd F Bd r) :
    HolesBd F Bd [(s, n)] (E.assignHole s X) := by
  intro p hp r hr
  obtain rfl := List.mem_singleton.1 hp
  dsimp only at hr
  rw [EvalEnv.assignHole_holes_self] at hr
  exact hX r hr

/-- **Every row a query computes is within the bound on the values it
holds**, for a bound every operator keeps (`BdClosed`): each value is free
– a constant of the query, a value of the context, or one the instance's
rows are given as free – or the row's annotation is within the bound on
it, as soon as the instance's rows and the rounds the holes are bound to
are. A value enters a row from a row holding it, so its annotation is
built from annotations within the bound by the operations that keep it; a
grouping's is `δ` of the sum over its group. -/
theorem rowBd_evaluate {Bd : T → K → Prop} (hB : BdClosed Bd)
    {d : AnnotatedDatabase T K} {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig Θ → q.noExplode → ∀ {ρc : Fin c → ColKind} {HK : HoleKinds},
      q.wellKinded ρc HK → ∀ (F : T → Prop), (∀ x ∈ q.allConsts, F x) →
      (∀ p ∈ q.relLeaves, ∀ r : AnnotatedRelation T K p.1, d.find p.1 p.2 = some r →
        ∀ a ∈ r, TupBd F Bd (a.1, a.2)) →
      ∀ (γ : Fin c → T) (E : EvalEnv T K), (∀ k, (ρc k).base ≠ ColKind.agg → F (γ k)) →
      (∀ k v, E.ctxAt c γ k = Sum.inl v → F v) → HolesBd F Bd l E →
      ∀ r ∈ q.evaluate d γ E, RowBd F Bd r := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ ρc HK _ F _ hD γ E _ _ _ r hr
    revert hr
    simp only [evaluate]
    cases hf : d.find n s with
    | none => intro hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      intro hr
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hr
      exact rowBd_ofAnnotated (hD (n, s) (List.mem_singleton_self _) rn hf a ha)
  | Hole n s κ =>
    intro _ _ ρc HK _ F _ _ γ E _ _ hH r hr
    exact hH (s, n) (List.mem_singleton_self _) r (Multiset.mem_of_mem_filter hr)
  | Param pv ρ =>
    intro _ _ ρc HK _ F hc _ γ E _ hctx _ r hr
    simp only [evaluate, EvalEnv.paramRows] at hr
    split at hr
    · rw [Multiset.mem_singleton] at hr
      subst hr
      intro k v hk
      left
      revert hk
      show _root_.Sum.elim Sum.inl (E.ctxAt _ γ) (pv k) = Sum.inl v → F v
      cases hpv : pv k with
      | inl a =>
        intro hk
        cases Sum.inl.inj hk
        refine hc _ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, ?_⟩)
        rw [hpv]
        exact Finset.mem_singleton_self _
      | inr j => intro hk; exact hctx j v hk
    · exact absurd hr (Multiset.notMem_zero r)
  | Empty => intro _ _ _ _ _ _ _ _ _ _ _ _ _ r hr; exact absurd hr (Multiset.notMem_zero r)
  | Proj ps q ih =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
    have hb := ih hi.2 hx hw.2 F (fun x hx' => hc x (Finset.mem_union_right _ hx')) hD γ E hγ
      hctx hH r₀ hr₀
    intro j v hj
    have hfin := GenAnn.finalize_cash' r₀.snd (r₀.snd.pending ∩
      tokenLists (fun j => (ps j).eval r₀.fst γ)) Multiset.inter_le_left
    simp only at hj ⊢
    rw [hfin]
    rcases projCol_eval_inl_cases (ps j) (hi.1 j) (hw.1 j)
      (fun k => evaluate_conform q d r₀ hr₀ k) γ hj with ⟨k, hk⟩ | hcon | ⟨j', hj', he⟩
    · exact hb k v hk
    · exact Or.inl (hc v (Finset.mem_union_left _ (Finset.mem_biUnion.2
        ⟨j, Finset.mem_univ j, hcon⟩)))
    · exact Or.inl (he ▸ hγ j' hj')
  | Sel φ q hφ ih =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    have ih' := ih hi.2 hx hw.2 F (fun x hx' => hc x (Finset.mem_union_right _ hx')) hD γ E hγ
      hctx hH
    dsimp only [evaluate] at hr
    by_cases hagg : φ.hasAggAtom = true
    · rw [ite_eq_left hagg] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
      intro k v hk
      have hb := ih' r₀ hr₀ k v hk
      refine hb.imp id fun h => ?_
      show Bd v (GenAnn.finalize ⟨r₀.snd.base * φ.predsemJ false r₀.fst γ, _⟩)
      rw [GenAnn.finalize_sel φ r₀.fst r₀.snd.base r₀.snd.pending _ _
        (fun k hk a hka => (Multiset.mem_filterMap _ _).mpr
          ⟨k, Finset.mem_val.mpr hk, by rw [hka]⟩)
        (fun k hk a hka hsc => (Multiset.mem_filterMap _ _).mpr
          ⟨k, Finset.mem_val.mpr hk, by rw [hka]; simp [hsc]⟩) ?_]
      · exact hB.mul_left _ _ _ h
      intro l hl
      obtain ⟨k, hk, hkl⟩ := (Multiset.mem_filterMap _ _).mp hl
      refine ⟨k, Finset.mem_val.mp hk, ?_⟩
      split at hkl
      · exact absurd hkl (by simp)
      · exact ⟨_, by assumption⟩
    · rw [ite_eq_right hagg] at hr
      exact ih' r (Multiset.mem_of_mem_filter hr)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨hxm, hym⟩ := Multiset.mem_product.1 hxy
    have bx := ih₁ hi.1 hx.1 hw.1 F (fun x hx' => hc x (Finset.mem_union_left _ hx'))
      (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγ hctx
      (fun p hp => hH p (List.mem_append_left _ hp)) x hxm
    have bY := ih₂ hi.2 hx.2 hw.2 F (fun x hx' => hc x (Finset.mem_union_right _ hx'))
      (fun p hp => hD p (List.mem_append_right _ hp)) γ E hγ hctx
      (fun p hp => hH p (List.mem_append_right _ hp)) y hym
    intro k v hk
    simp only [GenAnn.finalize_mul'] at hk ⊢
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk
      exact (bx i v hk).imp id (hB.mul_right _ _ _)
    · simp only [Fin.append_right] at hk
      exact (bY i v hk).imp id (hB.mul_left _ _ _)
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l'
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨x, hxm, hr⟩ := Multiset.mem_bind.1 hr
    obtain ⟨y, hym, rfl⟩ := Multiset.mem_map.1 hr
    have bx := ih₁ hi.1 hx.1 hw.1 F (fun x hx' => hc x (Finset.mem_union_left _ hx'))
      (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγ hctx hH x hxm
    have hconf := evaluate_conform q₁ d x hxm
    set F' : T → Prop := fun v => F v ∨ ∃ k, x.fst k = Sum.inl v with hF'
    have bY := ih₂ hi.2 hx.2 hw.2 F' (fun x hx' => Or.inl (hc x (Finset.mem_union_right _ hx')))
      (fun p hp r hr a ha k => (hD p (List.mem_append_right _ hp) r hr a ha k).imp Or.inl id)
      _ _ (fun k hk => ?_) (fun k v hk => ?_) (fun p hp => absurd hp List.not_mem_nil) y hym
    · intro k v hk
      rw [GenAnn.finalize_mul']
      refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
      · simp only [Fin.append_left] at hk
        exact (bx i v hk).imp id (hB.mul_right _ _ _)
      · simp only [Fin.append_right] at hk
        rcases bY i v hk with (hF | ⟨k', hk'⟩) | h
        · exact Or.inl hF
        · exact (bx k' v hk').imp id (hB.mul_right _ _ _)
        · exact Or.inr (hB.mul_left _ _ _ h)
    · refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
      · rw [Fin.append_left] at hk ⊢
        have h1 := hconf i
        rcases hv : x.fst i with a | a
        · exact Or.inr ⟨i, by rw [hv]; simp [GenRow.plainTuple, hv]⟩
        · rw [hv] at h1
          exact absurd h1.symm (by simpa [GenValue.kindOf] using hk)
      · rw [Fin.append_right] at hk ⊢
        exact Or.inl (hγ i hk)
    · rw [EvalEnv.ctxAt_withCtx] at hk
      revert hk
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]; exact fun hk => Or.inr ⟨i, hk⟩
      · rw [Fin.append_right]; exact fun hk => Or.inl (hctx i v hk)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    rcases Multiset.mem_add.1 hr with hr | hr
    · exact ih₁ hi.1 hx.1 hw.1 F (fun x hx' => hc x (Finset.mem_union_left _ hx'))
        (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγ hctx
        (fun p hp => hH p (List.mem_append_left _ hp)) r hr
    · exact ih₂ hi.2 hx.2 hw.2 F (fun x hx' => hc x (Finset.mem_union_right _ hx'))
        (fun p hp => hD p (List.mem_append_right _ hp)) γ E hγ hctx
        (fun p hp => hH p (List.mem_append_right _ hp)) r hr
  | Dedup q ih =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hr
    have hY : ∀ p ∈ (q.evaluate d γ E).map GenRow.toAnnotated, TupBd F Bd (p.1, p.2) := by
      intro p hp
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
      exact tupBd_of_rowBd (ih hi hx hw F hc hD γ E hγ hctx hH r₀ hr₀)
        (fun k => evaluate_conform q d r₀ hr₀ k)
    have hg : (Multiset.ofList (groupByKey ((q.evaluate d γ E).map GenRow.toAnnotated)).val
        : Multiset (AnnotatedTuple T K _))
        = PathSum.dedupK ((q.evaluate d γ E).map GenRow.toAnnotated) := by
      rw [groupByKey_eq_dedup_map]; rfl
    rw [hg] at hp
    exact rowBd_ofAnnotated (tupBd_dedupK hB hY p hp)
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨⟨u, α⟩, hp', rfl⟩ := Multiset.mem_map.1 hp
    obtain ⟨r₀, hr₀, he⟩ := Multiset.mem_map.1 hp'
    have hb := tupBd_of_rowBd (ih₁ hi.1 hx.1 hw.1 F
      (fun x hx' => hc x (Finset.mem_union_left _ hx'))
      (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγ hctx hH r₀ hr₀)
      (fun k => evaluate_conform q₁ d r₀ hr₀ k)
    refine rowBd_ofAnnotated fun k => ?_
    have he' : (GenRow.toAnnotated r₀) = (u, α) := he
    simp only [GenRow.toAnnotated] at he'
    have := hb k
    rw [(Prod.mk.inj he').1, (Prod.mk.inj he').2] at this
    exact this.imp id (hB.monus _ _ _)
  | Explode k hk q ih => exact fun _ hx => hx.elim
  | Retag hk q ih =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    exact ih hi hx hw F hc hD γ E hγ hctx hH r hr
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    refine forall_mem_muSumFix (P := RowBd F Bd) (fun X hX y hy => ?_)
      (ih₀ hi.1 hx.1 hw.1 F (fun x hx' => hc x (Finset.mem_union_left _ hx'))
        (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγ hctx
        (fun p hp => absurd hp List.not_mem_nil)) r hr
    exact ih₁ hi.2 hx.2 hw.2 F (fun x hx' => hc x (Finset.mem_union_right _ hx'))
      (fun p hp => hD p (List.mem_append_right _ hp)) γ _ hγ
      (by simpa only [EvalEnv.ctxAt_assignHole] using hctx) (holesBd_assignHole s hX) y hy
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    rename_i c' n'
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    set step := fun X : Multiset (AnnotatedTuple T K n') =>
      AnnotatedRelation.dedupAnn (((q₀.evaluate d γ E).map GenRow.toAnnotated)
        + ((q₁.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))).map
            GenRow.toAnnotated)) with hstep
    have hit : ∀ k, ∀ p ∈ muIter step k, TupBd F Bd (p.1, p.2) := by
      intro k
      induction k with
      | zero => intro p hp; exact absurd hp (Multiset.notMem_zero p)
      | succ k ihk =>
        intro p hp
        simp only [muIter, hstep] at hp
        rw [dedupAnn_eq_dedupK] at hp
        refine tupBd_dedupK hB (fun p hp => ?_) p hp
        rcases Multiset.mem_add.1 hp with hp | hp
        · obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
          exact tupBd_of_rowBd (ih₀ hi.1 hx.1 hw.1 F
            (fun x hx' => hc x (Finset.mem_union_left _ hx'))
            (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγ hctx
            (fun p hp => absurd hp List.not_mem_nil) r₀ hr₀)
            (fun k => evaluate_conform q₀ d r₀ hr₀ k)
        · obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
          refine tupBd_of_rowBd (ih₁ hi.2 hx.2 hw.2 F
            (fun x hx' => hc x (Finset.mem_union_right _ hx'))
            (fun p hp => hD p (List.mem_append_right _ hp)) γ _ hγ
            (by simpa only [EvalEnv.ctxAt_assignHole] using hctx)
            (holesBd_assignHole s fun r hr => ?_) r₀ hr₀)
            (fun k => evaluate_conform q₁ d r₀ hr₀ k)
          obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hr
          exact rowBd_ofAnnotated (ihk a ha)
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hr
    exact rowBd_ofAnnotated (hit _ p hp)
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂ _ _
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨kv, hkv, rfl⟩ := Multiset.mem_map.1 hr
    set R := (q.evaluate d γ E).map GenRow.toAnnotated with hR
    have hRb : ∀ p ∈ R, TupBd F Bd (p.1, p.2) := by
      intro p hp
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
      exact tupBd_of_rowBd (ih hi.2.2.2 hx hw.2 F
        (fun x hx' => hc x (Finset.mem_union_right _ hx')) hD γ E hγ hctx hH r₀ hr₀)
        (fun k => evaluate_conform q d r₀ hr₀ k)
    -- the key is held by some row of the group
    rw [groupByKey_eq_dedup_map] at hkv
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.1 hkv
    obtain ⟨p₀, hp₀, hp₀g⟩ := Multiset.mem_map.1 (Multiset.mem_dedup.1 hg)
    obtain ⟨p₁, hp₁, rfl⟩ := Multiset.mem_map.1 hp₀
    have hU : ∀ x ∈ Having.havingGroupOrd is ord R g, x ∈ R ∧ ∀ k, x.1 (is k) = g k := by
      intro x hx'
      rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe] at hx'
      exact Multiset.mem_filter.1 hx'
    have hp₁U : p₁ ∈ Having.havingGroupOrd is ord R g := by
      rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe]
      exact Multiset.mem_filter.2 ⟨hp₁, fun k => by rw [← hp₀g]⟩
    intro k v hk
    simp only [GenAnn.finalize, Multiset.map_singleton, Multiset.prod_singleton, one_mul]
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left, Sum.inl.injEq] at hk
      subst hk
      by_cases hF : F (g i)
      · exact Or.inl hF
      have hb : ∀ x ∈ Having.havingGroupOrd is ord R g, Bd (g i) x.2 := by
        intro x hx'
        have := (hRb x (hU x hx').1 (is i)).resolve_left (by rw [(hU x hx').2 i]; exact hF)
        rwa [(hU x hx').2 i] at this
      refine Or.inr (hB.delta _ _ ?_)
      rw [← Multiset.sum_coe, ← Multiset.map_coe]
      refine hB.sum _ _ (ne_zero_of_mem' (Multiset.mem_map.2
        ⟨p₁, Multiset.mem_coe.2 hp₁U, rfl⟩)) fun a ha => ?_
      obtain ⟨x, hx', rfl⟩ := Multiset.mem_map.1 ha
      exact hb x (Multiset.mem_coe.1 hx')
    · simp only [Fin.append_right] at hk
      exact absurd hk (by simp)
  | GammaScalar ts fs q ord ih =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate, Multiset.mem_singleton] at hr
    subst hr
    intro k v hk
    exact absurd hk (by simp)
  | GammaNest is his p g q ih =>
    rename_i c' m n₁ κ' _ _
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨gk, hgk, rfl⟩ := Multiset.mem_map.1 hr
    have hb := ih hi.2.2 hx hw.2 F (fun x hx' => hc x (Finset.mem_union_right _ hx')) hD γ E
      hγ hctx hH
    obtain ⟨r₁, hr₁, hr₁g⟩ := Multiset.mem_map.1 (Multiset.mem_dedup.1 hgk)
    have hkey : ∀ row ∈ q.evaluate d γ E, ∀ i,
        row.fst (is i) = Sum.inl (AggValue.collapseSum (row.fst (is i))) := by
      intro row hrow i
      have h1 := evaluate_conform q d row hrow (is i)
      rw [ColKind.base_eq_reg_of_ne_agg (his i)] at h1
      rcases hv : row.fst (is i) with a | a
      · rfl
      · rw [hv] at h1; exact absurd h1 (by simp [GenValue.kindOf])
    intro k v hk
    simp only [GenAnn.finalize, Multiset.map_singleton, Multiset.prod_singleton, one_mul,
      List.sum_cons, List.sum_nil, add_zero]
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left, Sum.inl.injEq] at hk
      subst hk
      by_cases hF : F (gk i)
      · exact Or.inl hF
      have hrow : ∀ row ∈ (q.evaluate d γ E).filter (fun row =>
          (fun k => AggValue.collapseSum (row.fst (is k))) = gk),
          Bd (gk i) row.snd.finalize := by
        intro row hrow
        obtain ⟨hrow, hrg⟩ := Multiset.mem_filter.1 hrow
        have h1 := hkey row hrow i
        rw [show AggValue.collapseSum (row.fst (is i)) = gk i from congrFun hrg i] at h1
        exact (hb row hrow (is i) (gk i) h1).resolve_left hF
      refine Or.inr (hB.delta _ _ ?_)
      refine hB.sum _ _ (ne_zero_of_mem' (Multiset.mem_map.2
        ⟨r₁, Multiset.mem_filter.2 ⟨hr₁, hr₁g⟩, rfl⟩)) fun a ha => ?_
      obtain ⟨row, hrow', rfl⟩ := Multiset.mem_map.1 ha
      exact hrow row hrow'
    · simp only [Fin.append_right] at hk
      exact absurd hk (by simp)
  | ProvSum is his t q ih => exact fun hi => hi.elim
  | GammaTok is his ts fs a q keep ih => exact fun hi => hi.elim
  | Win P O o w t g q hrr dist keep ih =>
    intro hi hx ρc HK hw F hc hD γ E hγ hctx hH r hr
    simp only [evaluate] at hr
    obtain ⟨x, hxm, rfl⟩ := Multiset.mem_map.1 hr
    have hb := ih hi.2.2.2.2 hx hw.2 F (fun x hx' => hc x (Finset.mem_union_right _ hx')) hD γ E
      hγ hctx hH x hxm
    intro k v hk
    simp only [ValueFrame.windowGenRow] at hk ⊢
    refine Fin.lastCases (fun hk => ?_) (fun i hk => ?_) k hk
    · rw [Fin.snoc_last] at hk; exact absurd hk (by simp)
    · rw [Fin.snoc_castSucc] at hk; exact hb i v hk
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hi => hi.elim

/-! ## The counters, annotated by the weights of their values -/

section ChainCounter

variable {c : ℕ}

/-- **The power of a relation with one row per value**: the tuples over its
values, each annotated by the product of its values' annotations. -/
private theorem ann_pow (C : AggQueryIn T c 1 (ColKind.allReg 1)) (V : Multiset (Tuple T 1))
    (f : Tuple T 1 → K) (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (hC : C.ann d γ E = V.map (fun v => ((v, f v) : AnnotatedTuple T K 1))) :
    ∀ K', (pow C K').ann d γ E
      = (powT V K').map (fun v => ((v, ∏ k, f (fun _ => v k)) : AnnotatedTuple T K K'))
  | 0 => by rw [pow, ann_unitC]; simp [powT]
  | K' + 1 => by
    rw [pow, ann_prodA, ann_pow C V f d γ E hC K', hC, product_map_map', Multiset.map_map,
      powT, Multiset.map_map]
    refine Multiset.map_congr rfl fun p _ => ?_
    simp only [Function.comp]
    refine Prod.ext rfl ?_
    show (∏ k, f (fun _ => p.1 k)) * f p.2
      = ∏ k : Fin (K' + 1), f (fun _ => Fin.append p.1 p.2 k)
    rw [Fin.prod_univ_castSucc]
    congr 1
    · exact Finset.prod_congr rfl fun k _ => congrArg f (funext fun _ =>
        (Fin.append_left p.1 p.2 k).symm)
    · refine congrArg f (funext fun i => ?_)
      rw [Fin.fin_one_eq_zero i]
      exact (Fin.append_right p.1 p.2 0).symm

private theorem wt_ctrLt_wt (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (hWn : W.Nodup) (w : Tuple T K' → K)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, w v) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (a b : Tuple T K')
    (ha : a ∈ W) (hb : b ∈ W) (hlt : ascLt K' a b) :
    PathSum.wt ((ctrLt EQ K').ann d γ E) (Fin.append a b) = w a * w b := by
  rw [ann_ctrLt EQ K' d γ E W w hW hnn]
  erw [PathSum.wt_map_nodup (nodup_ltPairs hWn)]
  rw [ite_eq_left ((mem_ltPairs a b).2 ⟨ha, hb, hlt⟩)]
  simp only [Fin.append_left, Fin.append_right]

private theorem mem_supp_ctrLt_wt (EQ : AggQueryIn T c 1 (ColKind.allReg 1)) (K' : ℕ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) (W : Multiset (Tuple T K'))
    (w : Tuple T K' → K)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, w v) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (a b : Tuple T K') :
    Fin.append a b ∈ PathSum.supp ((ctrLt EQ K').ann d γ E) ↔ a ∈ W ∧ b ∈ W ∧ ascLt K' a b := by
  rw [ann_ctrLt EQ K' d γ E W w hW hnn]
  erw [PathSum.supp_map]
  rw [Multiset.map_id', Multiset.mem_toFinset]
  exact mem_ltPairs a b

/-- **The all-chains simulation's rounds are those of `PathSum.ChainSpec`**,
for a sorted listing `l` of the counters, annotated by `w`. -/
private theorem chainSpec_of (s : String) (n K' : ℕ) (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hL : L.recLinear s n) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (W : Multiset (Tuple T K')) (hWn : W.Nodup) (w : Tuple T K' → K)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, w v) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) :
    ∃ l : List (Tuple T K'), l.Pairwise (ascLt K') ∧ l.length = W.card ∧ (∀ x, x ∈ l ↔ x ∈ W) ∧
      PathSum.ChainSpec (ascLt K') l w (fun a b => w a * w b) (BQ.ann d γ E)
        (fun u => L.ann d γ (E.assignHole s
          ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))))
        (((prodA BQ (ctrStart true EQ K')).ann d γ E).map splitRow)
        (fun q : Tuple T n × Tuple T K' =>
          (simRow s n K' true EQ L d γ E (Fin.append q.1 q.2)).map splitRow) := by
  set B := BQ.ann d γ E with hBdef
  set G := fun u => L.ann d γ (E.assignHole s
    ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) with hGdef
  obtain ⟨l, hlsort, hlen, hlmem⟩ := exists_sorted_counters K' W.toFinset
  have hcardW : W.toFinset.card = W.card := Multiset.toFinset_card_of_nodup hWn
  have hlnd : l.Nodup := PathSum.nodup_of_sorted hlsort ascLt_irrefl'
  have hmem : ∀ x, x ∈ l ↔ x ∈ W := by
    have hsub : l.toFinset ⊆ W.toFinset := fun x hx => hlmem x (List.mem_toFinset.1 hx)
    have heq : l.toFinset = W.toFinset := Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hlnd, hlen])
    intro x
    rw [← List.mem_toFinset, heq, Multiset.mem_toFinset]
  refine ⟨l, hlsort, hlen.trans hcardW, hmem, ?_⟩
  set base := (prodA BQ (ctrStart true EQ K')).ann d γ E with hbase
  set F := simRow s n K' true EQ L d γ E with hF
  have hpair : ∀ {a b : ℕ} (X : AnnotatedRelation T K a) (Y : AnnotatedRelation T K b),
      ((X.product Y).map (fun p => ((Fin.append p.1.1 p.2.1, p.1.2 * p.2.2)
        : AnnotatedTuple T K (a + b)))).map splitRow
      = (X.product Y).map (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2)) := by
    intro a b X Y
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun p _ => ?_
    simp only [Function.comp, splitRow, leftPart_append, rightPart_append]
  have hB'e : base.map splitRow = (B.product ((ctr EQ K').ann d γ E)).map
      (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2)) := by
    rw [hbase, ann_prodA, ctrStart_true, hpair]
  have hG'e : ∀ t c₀, (F (Fin.append t c₀)).map splitRow
      = ((G t).product ((((ctrLt EQ K').ann d γ E).filter
      (fun p => (fun k => p.1 (Fin.castAdd K' k)) = c₀)).map
        (fun p => (((fun j => p.1 (Fin.natAdd K' j)), p.2) : AnnotatedTuple T K K')))).map
      (fun p => ((p.1.1, p.2.1), p.1.2 * p.2.2)) := by
    intro t c₀
    rw [hF]
    simp only [simRow]
    rw [ann_prodA, ann_substRow s n K' L hL, ann_ctrNext, ctrStep_true, hpair, leftPart_append,
      rightPart_append]
    rfl
  have hsuppW : ∀ b, b ∈ PathSum.supp ((ctr EQ K').ann d γ E) ↔ b ∈ W := fun b => by
    rw [hW]
    erw [PathSum.supp_map]
    rw [Multiset.map_id', Multiset.mem_toFinset]
  refine ⟨hlsort, ascLt_irrefl', ascLt_trans', fun t c₀ hc => ?_, fun t c₀ => ?_,
    fun t c₀ hc t' c' hc' hlt => ?_, fun t c₀ hc t' c' => ?_⟩
  · rw [hB'e]
    erw [PathSum.wt_product]
    rw [hW]
    erw [PathSum.wt_map_nodup hWn]
    rw [ite_eq_left ((hmem c₀).1 hc)]
  · rw [hB'e]
    erw [PathSum.mem_supp_product]
    rw [hsuppW, hmem]
  · show PathSum.wt ((F (Fin.append t c₀)).map splitRow) (t', c') = _
    rw [hG'e]
    erw [PathSum.wt_product]
    erw [wt_halves]
    rw [wt_ctrLt_wt EQ K' d γ E W hWn w hW hnn c₀ c' ((hmem c₀).1 hc) ((hmem c').1 hc') hlt]
  · show (t', c') ∈ PathSum.supp ((F (Fin.append t c₀)).map splitRow) ↔ _
    rw [hG'e]
    erw [PathSum.mem_supp_product]
    erw [mem_supp_halves]
    rw [mem_supp_ctrLt_wt EQ K' d γ E W w hW hnn, hmem]
    exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, (hmem c₀).1 hc, h.2.1, h.2.2⟩⟩

/-- **The all-chains simulation computes the set recursion**, in an
absorptive semiring: where the counters are the `K'`-tuples `W` over values
none of which is the null, annotated by `w`, there are at least as many
counters as tuples in a set `S` closed under the recursion's rounds, and
every derivation through distinct tuples of `S` weighs `𝟘` or is absorbed
by the weight of a chain of as many counters, the simulation's value is the
set recursion's wherever the latter settles. -/
private theorem evaluate_simResultA_chain (s s' : String) (n K' : ℕ)
    (EQ : AggQueryIn T c 1 (ColKind.allReg 1))
    (BQ : AggQueryIn T c n (ColKind.allReg n)) (L : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hL : L.recLinear s n) (hLx : L.noExplode) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (W : Multiset (Tuple T K')) (hWn : W.Nodup) (w : Tuple T K' → K)
    (hW : (ctr EQ K').ann d γ E = W.map (fun v => ((v, w v) : AnnotatedTuple T K K')))
    (hnn : ∀ u ∈ W, ∀ k, ValueType.isNull (u k) = false) (S : Finset (Tuple T n))
    (hS : PathSum.Closed S (BQ.ann d γ E) (fun u => L.ann d γ (E.assignHole s
      ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))))
    (hcard : S.card ≤ W.card) (habs : ∀ a : K, 1 + a = 1)
    (hgen : ∀ j t p, p ∈ PathSum.pathsTo S j t → p.Nodup →
      PathSum.pw (PathSum.wt (BQ.ann d γ E))
          (fun u v => PathSum.wt (L.ann d γ (E.assignHole s
            ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))) v) p = 0
        ∨ ∃ ch : List (Tuple T K'), ch.length = p.length
          ∧ ch.Pairwise (fun a b => ascLt K' b a) ∧ (∀ x ∈ ch, x ∈ W)
          ∧ PathSum.pw (PathSum.wt (BQ.ann d γ E))
              (fun u v => PathSum.wt (L.ann d γ (E.assignHole s
                ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))) v) p
              * PathSum.pw w (fun a b => w a * w b) ch
            = PathSum.pw (PathSum.wt (BQ.ann d γ E))
              (fun u v => PathSum.wt (L.ann d γ (E.assignHole s
                ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n)))) v) p)
    (hset : MuSetSettles (muSetStep s BQ L d γ E)) :
    (simResultA s s' n K' true EQ BQ L).evaluate d γ E = (MuSet s BQ L).evaluate d γ E := by
  set B := BQ.ann d γ E with hBdef
  set G := fun u => L.ann d γ (E.assignHole s
    ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) with hGdef
  have hstep : muSetStep s BQ L d γ E = PathSum.stepK B G := funext fun X => by
    rw [muSetStep, dedupAnn_eq_dedupK, PathSum.stepK]
    congr 2
    exact ann_of_recLinear L hL hLx d γ E X
  rw [hstep] at hset
  obtain ⟨l, -, hlen, hmem, hspec⟩ := chainSpec_of s n K' EQ BQ L hL d γ E W hWn w hW hnn
  rw [evaluate_MuSet_of_recLinear s BQ L hL hLx d γ E]
  have hfix : muFix (PathSum.stepK B G) = (PathSum.stepK B G)^[l.length] 0 := by
    rw [← muIter_eq_iterate]
    apply muFix_eq_of_fix
    have h := PathSum.iterate_succ_eq_of_settles hS (Or.inl habs) hset (M := l.length)
      (by rw [hlen]; exact hcard)
    rw [Function.iterate_succ_apply'] at h
    rw [muIter_eq_iterate]
    exact h
  rw [hfix, PathSum.iterate_stepK_eq]
  set base := (prodA BQ (ctrStart true EQ K')).ann d γ E with hbase
  set F := simRow s n K' true EQ L d γ E with hF
  have hzero : (PathSum.lin F)^[l.length] base = 0 := by
    have h := hspec.rounds_eq_zero (le_refl l.length)
    rw [rounds_map_splitRow] at h
    exact Multiset.map_eq_zero.1 h
  have hk : ∃ k, (PathSum.lin F)^[k + 1] base = 0 :=
    ⟨l.length, by rw [Function.iterate_succ_apply', hzero, PathSum.lin_zero]⟩
  rw [simResultA, evaluate_dedup_eq, ann_keepCols, ann_simA s s' n K' true EQ BQ L d γ E hk,
    muSumFix_eq_sum (PathSum.lin_zero F) (L := l.length)
      (by rw [Function.iterate_succ_apply', hzero, PathSum.lin_zero])]
  congr 1
  have hproj : ∀ X : Multiset (Tuple T (n + K') × K),
      X.map (fun p => ((fun i => p.1 (Fin.castAdd K' i), p.2) : AnnotatedTuple T K n))
        = (X.map splitRow).map PathSum.dropCtr := fun X => by
    rw [Multiset.map_map]; rfl
  have hsum : ∀ (S' : Finset ℕ) (X : ℕ → Multiset (Tuple T (n + K') × K)),
      (∑ j ∈ S', X j).map splitRow = ∑ j ∈ S', (X j).map splitRow := by
    intro S' X
    induction S' using Finset.induction_on with
    | empty => simp
    | insert j S' hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Multiset.map_add, ih]
  erw [hproj, hsum]
  simp only [← rounds_map_splitRow]
  refine hspec.dedupK_rounds habs hS (le_of_le_of_eq hcard hlen.symm)
    (le_of_le_of_eq hcard hlen.symm) (Nat.le_succ _) fun j t p hp hnd => ?_
  rcases hgen j t p hp hnd with h0 | ⟨ch, h₁, h₂, h₃, h₄⟩
  · exact Or.inl h0
  · exact Or.inr ⟨ch, h₁, h₂, fun x hx => (hmem x).2 (h₃ x hx), h₄⟩

end ChainCounter

/-! ## The node: a set recursion replaced by its all-chains simulation -/

section ChainNode

variable {c : ℕ}

/-- A leaf row's value is a row of the counter values, with its annotation. -/
private theorem mem_ann_valRel_of_leaf {ls : List (ℕ × String)} {cs : List T}
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {q : ℕ × String} (hq : q ∈ ls)
    {r : AnnotatedRelation T K q.1} (hr : d.find q.1 q.2 = some r) {p : AnnotatedTuple T K q.1}
    (hp : p ∈ r) (i : Fin q.1) (hnn : ValueType.isNull (p.1 i) = false) :
    (((fun _ => p.1 i), p.2) : AnnotatedTuple T K 1) ∈ (valRel ls cs).ann d γ E := by
  rw [valRel, ann_sel _ _ _ rfl, ann_listSum]
  refine Multiset.mem_filter.2 ⟨?_, (holdsPlain_nonNullPred' _ γ).2 hnn⟩
  refine (mem_list_sum' _).2 ⟨_, List.mem_map.2 ⟨colRel (Rel q.1 q.2) i,
    List.mem_append_left _ (List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨i, List.mem_finRange i,
      rfl⟩⟩), rfl⟩, ?_⟩
  rw [ann_colRel, ann_Rel, hr]
  exact Multiset.mem_map.2 ⟨p, hp, rfl⟩

/-- A non-null constant is a row of the counter values, annotated `𝟙`. -/
private theorem mem_ann_valRel_of_const {ls : List (ℕ × String)} {cs : List T}
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) {a : T} (ha : a ∈ cs)
    (hnn : ValueType.isNull a = false) :
    (((fun _ => a), 1) : AnnotatedTuple T K 1) ∈ (valRel ls cs).ann d γ E := by
  rw [valRel, ann_sel _ _ _ rfl, ann_listSum]
  refine Multiset.mem_filter.2 ⟨?_, (holdsPlain_nonNullPred' _ γ).2 hnn⟩
  refine (mem_list_sum' _).2 ⟨_, List.mem_map.2 ⟨constRel a,
    List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩), rfl⟩, ?_⟩
  rw [ann_constRel]
  exact Multiset.mem_singleton_self _

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- An annotation is below the weight of its tuple. -/
private theorem le_wt_of_mem {n : ℕ} {X : Multiset (Tuple T n × K)} {p : Tuple T n × K} (hp : p ∈ X) :
    p.2 ≤ PathSum.wt X p.1 := by
  unfold PathSum.wt
  refine Multiset.le_sum_of_mem (Multiset.mem_map.2 ⟨p, ?_, rfl⟩)
  exact Multiset.mem_filter.2 ⟨hp, rfl⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **Tuples over a set of values**: at most its size to the arity. -/
private theorem card_le_of_vals {n : ℕ} (S : Finset (Tuple T n)) (A : Finset T)
    (h : ∀ t ∈ S, ∀ k, t k ∈ A) : S.card ≤ A.card ^ n := by
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin n => A) := fun t ht =>
    Fintype.mem_piFinset.2 (h t ht)
  have := Finset.card_le_card hsub
  rwa [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this


/-- **A tuple's weight is below each of its values' weights**, where every row
is. -/
private theorem wt_ann_le_of_rowBd (habs : ∀ a : K, 1 + a = 1) {F Vl : T → Prop} {e : T → K}
    {n : ℕ} {l : List (String × ℕ)} (q : AggQueryIn T c n (ColKind.allReg n) l)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (h : ∀ r ∈ q.evaluate d γ E, RowBd F (leBd Vl e) r) (u : Tuple T n) (k : Fin n)
    (hF : ¬ F (u k)) : PathSum.wt (q.ann d γ E) u ≤ e (u k) := by
  unfold PathSum.wt ann
  refine msum_le habs _ _ fun a ha => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 ha
  obtain ⟨hp, hpu⟩ := Multiset.mem_filter.1 hp
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hp
  have hk : r.fst k = Sum.inl (u k) := by
    have h1 := evaluate_conform q d r hr k
    rw [← hpu]
    rcases hv : r.fst k with x | x
    · simp [GenRow.toAnnotated, GenRow.plainTuple, hv]
    · rw [hv] at h1; simp [GenValue.kindOf, ColKind.allReg, ColKind.base] at h1
  exact ((h r hr k (u k) hk).resolve_left hF).2

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The width of the counter**: `(m + 2c + 1)^n` tuples are outrun by
`m^((2c + 2) n)` counters. -/
private theorem card_arith_chain0 {m A n : ℕ} (hm : 2 ≤ m) (hA : A ≤ m + 2 * c + 1) :
    A ^ n ≤ m ^ ((2 * c + 2) * n) := by
  have h1 := add_le_pow_of_two_le hm (2 * c)
  calc A ^ n ≤ (m ^ (2 * c + 2)) ^ n := Nat.pow_le_pow_left (by omega) n
    _ = m ^ ((2 * c + 2) * n) := (pow_mul m _ n).symm

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The width of the all-chains counter**: `(m + 2c + 1)^n` tuples are
outrun by `m^((2c + 2) n + 2)` counters. -/
private theorem card_arith_chain {m A n : ℕ} (hm : 2 ≤ m) (hA : A ≤ m + 2 * c + 1) :
    A ^ n ≤ m ^ ((2 * c + 2) * n + 2) :=
  le_trans (card_arith_chain0 hm hA) (Nat.pow_le_pow_right (by omega) (by omega))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The width of the successor counter**: twice `(m + 2c + 1)^n` tuples,
and one more, are outrun by `m^((2c + 2) n + 2)` counters. -/
private theorem card_arith_succ {m A n : ℕ} (hm : 2 ≤ m) (hA : A ≤ m + 2 * c + 1) :
    2 * A ^ n + 1 ≤ m ^ ((2 * c + 2) * n + 2) := by
  have h1 := card_arith_chain0 (c := c) (n := n) hm hA
  have h2 : 1 ≤ m ^ ((2 * c + 2) * n) := Nat.one_le_pow _ _ (by omega)
  have h3 : 4 ≤ m ^ 2 := by nlinarith
  rw [pow_add]
  nlinarith

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A weight absorbing each counter of a chain absorbs the chain's. -/
private theorem pw_absorb {K' : ℕ} (w : Tuple T K' → K) (X : K) :
    ∀ ch : List (Tuple T K'), ch ≠ [] → (∀ x ∈ ch, X * w x = X) →
      X * PathSum.pw w (fun a b => w a * w b) ch = X
  | [], h, _ => absurd rfl h
  | [a], _, h => by simp only [PathSum.pw]; exact h a List.mem_cons_self
  | a' :: a :: rest, _, h => by
    rw [PathSum.pw, ← mul_assoc, ← mul_assoc, h a (by simp), h a' List.mem_cons_self]
    exact pw_absorb w X (a :: rest) (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))

set_option maxHeartbeats 1000000 in
/-- **A set recursion is its all-chains simulation**, where `δ` is the
identity, at an instance where it settles, given matches `q₀'`, `q₁'` of
its base and body that agree with them wherever these settle. -/
theorem muSetSim_correct_chain (cnt : SeqAggFunc T)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) {n : ℕ} (s s' : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hq₁ : q₁.recLinear s n) (hq₁x : q₁.noExplode) (hq₁' : q₁'.recLinear s n)
    (hq₁'x : q₁'.noExplode) (hsig : (MuSet s q₀ q₁).inSig {cnt})
    (hhyg : (MuSet s q₀ q₁).hygienic) (hx : (MuSet s q₀ q₁).noExplode)
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hwk : (MuSet s q₀ q₁).wellKinded ρc HK)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (hset : (MuSet s q₀ q₁).AnnSettlesAt d γ E)
    (h₀ : q₀'.AnnSettlesAt d γ E ∧ q₀'.evaluate d γ E = q₀.evaluate d γ E)
    (h₁ : ∀ X : AnnotatedRelation T K n,
      q₁.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated)) →
        q₁'.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated))
          ∧ q₁'.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))
            = q₁.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))) :
    (muSetSim true s s' q₀ q₁ q₀' q₁').AnnSettlesAt d γ E
      ∧ (muSetSim true s s' q₀ q₁ q₀' q₁').evaluate d γ E
        = (MuSet s q₀ q₁).evaluate d γ E := by
  have hid : IsDelta (id : K → K) := by
    have h := isDelta_delta (α := K)
    rwa [show SemiringWithMonus.delta = (id : K → K) from funext hδ] at h
  have habs : ∀ a : K, 1 + a = 1 := fun a => by simpa using hid.absorb 1 a
  have hidem : ∀ a : K, a * a = a := fun a => by
    have := hid.absorb a a
    rwa [id, PathSum.add_self_of_abs habs a] at this
  have hmulL : ∀ a b : K, a * b ≤ a := fun a b => by
    rw [mul_comm]; exact mul_le_right habs b a
  -- a derivation's weight is absorbed by an annotation above it
  have habsorb : ∀ x f : K, x ≤ f → x * f = x := fun x f h =>
    le_antisymm (hmulL x f) (by
      calc x = x * x := (hidem x).symm
        _ ≤ x * f := mul_le_mul_left_of_le h x)
  obtain ⟨hs₀, hsS, hsk⟩ := hset
  -- the two set recursions have the same iterates
  have hiter : ∀ k, muSetStep s q₀' q₁' d γ E (muIter (muSetStep s q₀ q₁ d γ E) k)
      = muSetStep s q₀ q₁ d γ E (muIter (muSetStep s q₀ q₁ d γ E) k) := fun k => by
    have h1 := (h₁ _ (hsk k)).2
    generalize muIter (muSetStep s q₀ q₁ d γ E) k = X at h1 ⊢
    unfold muSetStep evaluateAnnotated
    rw [h₀.2, h1]
  have hfix := muFix_congr_iter hiter
  have hsS' := muSetSettles_congr_iter hiter hsS
  have hMuSet : (MuSet s q₀' q₁').evaluate d γ E = (MuSet s q₀ q₁).evaluate d γ E := by
    rw [evaluate_MuSet, evaluate_MuSet, hfix]
  -- the recursion of `PathSum` the matches give
  set B := q₀'.ann d γ E with hB
  set G := fun u => q₁'.ann d γ (E.assignHole s
    ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) with hG
  have hstep : muSetStep s q₀' q₁' d γ E = PathSum.stepK B G := funext fun X => by
    rw [muSetStep, dedupAnn_eq_dedupK, PathSum.stepK]
    congr 2
    exact ann_of_recLinear q₁' hq₁' hq₁'x d γ E X
  have hsK : MuSetSettles (PathSum.stepK B G) := hstep ▸ hsS'
  -- the counters
  set ls := ctrLeaves s q₀ q₁ with hls
  set cs := ctrConsts s q₀ q₁ with hcs
  set EQ : AggQueryIn T c 1 (ColKind.allReg 1) := valRel ls cs with hEQ
  set K' := ctrWidth c n with hK'
  have hK'e : K' = (2 * c + 2) * n + 2 := rfl
  set V := ((EQ.ann d γ E).map Prod.fst).dedup with hV
  set W := powT V K' with hW
  set ev : T → K := fun x => PathSum.wt (EQ.ann d γ E) (fun _ => x) with hev
  set w : Tuple T K' → K := fun v => ∏ k, ev (v k) with hw
  have hWn : W.Nodup := nodup_powT (Multiset.nodup_dedup _) K'
  have hWa : (ctr EQ K').ann d γ E = W.map (fun v => ((v, w v) : AnnotatedTuple T K K')) := by
    refine ann_pow (dedupG EQ) V (fun x => PathSum.wt (EQ.ann d γ E) x) d γ E ?_ K'
    rw [ann_dedupG]
    refine Multiset.map_congr rfl fun g _ => ?_
    rw [hδ]
  have hVnn : ∀ v ∈ V, ValueType.isNull (v 0) = false := fun v hv => by
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_dedup.1 hv)
    exact (mem_ann_valRel hp).1
  have hnn := nonNull_powT hVnn K'
  -- the tuples of the settled value
  set S := PathSum.supp (muFix (PathSum.stepK B G)) with hS
  have hSc : PathSum.Closed S B G := closed_supp_muFix B G hsK
  classical
  -- the free values: the null, the constants, and the context's
  set F : T → Prop := fun x => ValueType.isNull x = true ∨ x ∈ (MuSet s q₀ q₁).allConsts
    ∨ (∃ k, (ρc k).base ≠ ColKind.agg ∧ γ k = x) ∨ ∃ k, E.ctxAt c γ k = Sum.inl x with hFdef
  set Vl : T → Prop := fun x => (fun _ => x) ∈ (EQ.ann d γ E).map Prod.fst with hVl
  have hD : ∀ p ∈ (MuSet s q₀ q₁).relLeaves, ∀ r : AnnotatedRelation T K p.1,
      d.find p.1 p.2 = some r → ∀ a ∈ r, TupBd F (leBd Vl ev) (a.1, a.2) := by
    intro p hp r hr a ha k
    by_cases hn : ValueType.isNull (a.1 k) = true
    · exact Or.inl (Or.inl hn)
    · have hn' : ValueType.isNull (a.1 k) = false := by simpa using hn
      have hrow := mem_ann_valRel_of_leaf (cs := cs) d γ E
        (mem_leaves_of_mem_relLeaves _ hhyg p hp) hr ha k hn'
      exact Or.inr ⟨Multiset.mem_map.2 ⟨_, hrow, rfl⟩, le_wt_of_mem hrow⟩
  have hc : ∀ x ∈ (MuSet s q₀ q₁).allConsts, F x := fun x hx => Or.inr (Or.inl hx)
  have hγF : ∀ k, (ρc k).base ≠ ColKind.agg → F (γ k) := fun k hk =>
    Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))
  have hctxF : ∀ k v, E.ctxAt c γ k = Sum.inl v → F v := fun k v hk =>
    Or.inr (Or.inr (Or.inr ⟨k, hk⟩))
  have hrowsM : ∀ r ∈ (MuSet s q₀ q₁).evaluate d γ E, RowBd F (leBd Vl ev) r :=
    rowBd_evaluate (leBd_closed hδ Vl ev) (MuSet s q₀ q₁) hsig hx hwk F hc hD γ E hγF hctxF
      (fun p hp => absurd hp List.not_mem_nil)
  have hrows₀ : ∀ r ∈ q₀.evaluate d γ E, RowBd F (leBd Vl ev) r :=
    rowBd_evaluate (leBd_closed hδ Vl ev) q₀ hsig.1 hx.1 hwk.1 F
      (fun x hx => hc x (Finset.mem_union_left _ hx))
      (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγF hctxF
      (fun p hp => absurd hp List.not_mem_nil)
  have hrows₁ : ∀ u : Tuple T n, ∀ r ∈ q₁.evaluate d γ (E.assignHole s
      ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))),
      RowBd (fun x => F x ∨ ∃ k, u k = x) (leBd Vl ev) r := fun u =>
    rowBd_evaluate (leBd_closed hδ Vl ev) q₁ hsig.2 hx.2 hwk.2 _
      (fun x hx => Or.inl (hc x (Finset.mem_union_right _ hx)))
      (fun p hp r hr a ha k => (hD p (List.mem_append_right _ hp) r hr a ha k).imp Or.inl id) γ _
      (fun k hk => Or.inl (hγF k hk))
      (fun k v hk => Or.inl (hctxF k v (by simpa only [EvalEnv.ctxAt_assignHole] using hk)))
      (holesBd_assignHole s fun r hr => by
        rw [Multiset.mem_singleton] at hr
        subst hr
        exact rowBd_ofAnnotated fun k => Or.inl (Or.inr ⟨k, rfl⟩))
  -- the tuples of `S` hold free values and counter values
  have hSvals : ∀ t ∈ S, ∀ k, F (t k) ∨ Vl (t k) := by
    intro t ht k
    obtain ⟨⟨t', a⟩, hp, rfl⟩ := PathSum.mem_supp.1 ht
    have hm : GenRow.ofAnnotated ((t', a) : AnnotatedTuple T K n)
        ∈ (MuSet s q₀ q₁).evaluate d γ E := by
      rw [← hMuSet, evaluate_MuSet_of_recLinear s q₀' q₁' hq₁' hq₁'x d γ E]
      exact Multiset.mem_map_of_mem _ hp
    exact (hrowsM _ hm k (t' k) rfl).imp id (fun h => h.1)
  -- the free values, as a finite set
  set FreeFin : Finset T := Union.union (Union.union (ValueType.nullVal : Option T).toFinset
    (Finset.univ.image γ)) (Finset.univ.biUnion (fun k => match E.ctxAt c γ k with
      | Sum.inl x => {x}
      | Sum.inr _ => ∅)) with hFreeFin
  have hFreeCard : FreeFin.card ≤ 1 + c + c := by
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
      · cases (ValueType.nullVal : Option T) <;> simp
      · exact le_trans Finset.card_image_le (by simp)
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => 1) fun k _ => ?_) (by simp)
      split <;> simp
  set CV : Finset T := (cs.toFinset).filter (fun x => ValueType.isNull x = false) with hCV
  have hFcases : ∀ x, F x → x ∈ FreeFin ∨ x ∈ CV := by
    intro x hx
    rcases hx with hn | hcx | ⟨k, -, rfl⟩ | ⟨k, hk⟩
    · left
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      rw [(ValueType.isNull_iff_nullVal x).1 hn]
      exact Finset.mem_singleton_self x
    · cases hn : ValueType.isNull x
      · right
        refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 (List.mem_append_left _
          (Finset.mem_toList.2 hcx)), hn⟩
      · left
        refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        rw [(ValueType.isNull_iff_nullVal x).1 hn]
        exact Finset.mem_singleton_self x
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem γ (Finset.mem_univ k))))
    · refine Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, ?_⟩))
      rw [hk]
      exact Finset.mem_singleton_self x
  have hCVrow : ∀ x ∈ CV, (((fun _ => x), 1) : AnnotatedTuple T K 1) ∈ EQ.ann d γ E := by
    intro x hx
    obtain ⟨hx, hn⟩ := Finset.mem_filter.1 hx
    exact mem_ann_valRel_of_const d γ E (List.mem_toFinset.1 hx) hn
  have hCVV : ∀ x ∈ CV, (fun _ => x) ∈ V := fun x hx =>
    Multiset.mem_dedup.2 (Multiset.mem_map.2 ⟨_, hCVrow x hx, rfl⟩)
  have hCVone : ∀ x ∈ CV, ∀ y : K, y ≤ ev x := fun x hx y =>
    le_trans (PathSum.le_one_of_abs habs y) (le_wt_of_mem (hCVrow x hx))
  have h0CV : (0 : T) ∈ CV := Finset.mem_filter.2 ⟨List.mem_toFinset.2
    (List.mem_append_right _ (by simp)), ValueType.isNull_zero⟩
  have hnzCV : (ValueType.nonzero : T) ∈ CV := Finset.mem_filter.2 ⟨List.mem_toFinset.2
    (List.mem_append_right _ (by simp)), ValueType.isNull_nonzero⟩
  have hVlV : ∀ x, Vl x → (fun _ => x) ∈ V := fun x hx => Multiset.mem_dedup.2 hx
  have hcard : S.card ≤ W.card := by
    obtain ⟨AV, hAV⟩ : ∃ AV : Finset T, AV = Union.union (V.map (fun v => v 0)).toFinset FreeFin :=
      ⟨_, rfl⟩
    have hSAV : ∀ t ∈ S, ∀ k, t k ∈ AV := by
      intro t ht k
      rw [hAV]
      rcases hSvals t ht k with hF | hv
      · rcases hFcases _ hF with h | h
        · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_left _ (Multiset.mem_toFinset.2
            (Multiset.mem_map.2 ⟨_, hCVV _ h, rfl⟩))
      · exact Finset.mem_union_left _ (Multiset.mem_toFinset.2
          (Multiset.mem_map.2 ⟨_, hVlV _ hv, rfl⟩))
    have hm2 : 2 ≤ V.card := by
      rw [← Multiset.toFinset_card_of_nodup (Multiset.nodup_dedup _)]
      refine Finset.one_lt_card.2 ⟨fun _ => 0, Multiset.mem_toFinset.2 (hCVV 0 h0CV),
        fun _ => ValueType.nonzero, Multiset.mem_toFinset.2 (hCVV _ hnzCV), ?_⟩
      intro h
      exact ValueType.nonzero_ne_zero (congrFun h 0).symm
    have hAVc : AV.card ≤ V.card + 2 * c + 1 := by
      rw [hAV]
      have := Finset.card_union_le (V.map (fun v => v 0)).toFinset FreeFin
      have h2 : (V.map (fun v => v 0)).toFinset.card ≤ V.card :=
        le_trans (Multiset.toFinset_card_le _) (by rw [Multiset.card_map])
      omega
    rw [hW, card_powT, hK'e]
    exact le_trans (card_le_of_vals S AV hSAV) (card_arith_chain hm2 hAVc)
  have hB_eq : B = q₀.ann d γ E := by rw [hB, ann, ann, h₀.2]
  have hG_eq : ∀ u ∈ S, G u = q₁.ann d γ (E.assignHole s
      ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) := by
    intro u hu
    have hfS : muFix (PathSum.stepK B G)
        = muIter (muSetStep s q₀ q₁ d γ E) (muFixIdx (muSetStep s q₀ q₁ d γ E)) := by
      rw [← hstep, hfix]; rfl
    have hsub : PathSum.supp ({((u, 1) : AnnotatedTuple T K n)} : Multiset (AnnotatedTuple T K n))
        ⊆ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E)
          (muFixIdx (muSetStep s q₀ q₁ d γ E))) := fun v hv => by
      have : v = u := by simpa [PathSum.supp] using hv
      rw [this, ← hfS]; exact hu
    have h1 := annSettlesAt_of_recLinear_subset q₁ hq₁ hq₁x d γ E _ _ hsub (hsk _)
    have h2 := (h₁ _ h1).2
    rw [Multiset.map_singleton] at h2
    rw [hG]
    simp only [ann]
    rw [h2]
  have hgen : ∀ j t p, p ∈ PathSum.pathsTo S j t → p.Nodup →
      PathSum.pw (PathSum.wt B) (fun u v => PathSum.wt (G u) v) p = 0
        ∨ ∃ ch : List (Tuple T K'), ch.length = p.length
          ∧ ch.Pairwise (fun a b => ascLt K' b a) ∧ (∀ x ∈ ch, x ∈ W)
          ∧ PathSum.pw (PathSum.wt B) (fun u v => PathSum.wt (G u) v) p
              * PathSum.pw w (fun a b => w a * w b) ch
            = PathSum.pw (PathSum.wt B) (fun u v => PathSum.wt (G u) v) p := by
    intro j t p hp hnd
    obtain ⟨hplen, -, hpS⟩ := (PathSum.mem_pathsTo S j t p).1 hp
    right
    obtain ⟨X, hX⟩ : ∃ X, X = PathSum.pw (PathSum.wt B) (fun u v => PathSum.wt (G u) v) p :=
      ⟨_, rfl⟩
    rw [← hX]
    -- a derivation weighs no more than the weight of a value it holds
    have claimA : ∀ l : List (Tuple T n), (∀ a ∈ l, a ∈ S) → ∀ u ∈ l, ∀ k, ¬ F (u k) →
        PathSum.pw (PathSum.wt B) (fun u v => PathSum.wt (G u) v) l ≤ ev (u k) := by
      intro l
      induction l with
      | nil => intro _ u hu; exact absurd hu List.not_mem_nil
      | cons v rest ih =>
        intro hl u hu k hF
        cases rest with
        | nil =>
          obtain rfl : u = v := List.mem_singleton.1 hu
          show PathSum.wt B u ≤ _
          rw [hB_eq]
          exact wt_ann_le_of_rowBd habs q₀ d γ E hrows₀ u k hF
        | cons u' l' =>
          show PathSum.wt (G u') v * PathSum.pw _ _ (u' :: l') ≤ _
          have hrest : ∀ a ∈ u' :: l', a ∈ S := fun a ha => hl a (List.mem_cons_of_mem _ ha)
          rcases List.mem_cons.1 hu with rfl | hu
          · by_cases hxu : ∃ k', u' k' = u k
            · obtain ⟨k', hk'⟩ := hxu
              have := ih hrest u' List.mem_cons_self k' (by rw [hk']; exact hF)
              rw [hk'] at this
              exact le_trans (mul_le_right habs _ _) this
            · refine le_trans (hmulL _ _) ?_
              rw [hG_eq u' (hrest u' List.mem_cons_self)]
              exact wt_ann_le_of_rowBd habs q₁ d γ _ (hrows₁ u') u k
                (fun h => h.elim hF hxu)
          · exact le_trans (mul_le_right habs _ _) (ih hrest u hu k hF)
    -- the values of the derivation, and the constants
    obtain ⟨Vp, hVp⟩ : ∃ Vp : Finset T, Vp = (p.toFinset.biUnion
        (fun u => Finset.univ.image u)).filter (fun x => ¬ F x) := ⟨_, rfl⟩
    obtain ⟨Cp, hCp⟩ : ∃ Cp : Finset T, Cp = Union.union Vp CV := ⟨_, rfl⟩
    have hXC : ∀ x ∈ Cp, X ≤ ev x := by
      intro x hx
      rw [hCp] at hx
      rcases Finset.mem_union.1 hx with hx | hx
      · rw [hVp] at hx
        obtain ⟨hx, hF⟩ := Finset.mem_filter.1 hx
        obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.1 hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
        rw [hX]
        exact claimA p hpS u (List.mem_toFinset.1 hu) k hF
      · exact hCVone x hx X
    have hCpV : ∀ x ∈ Cp, (fun _ => x) ∈ V := by
      intro x hx
      rw [hCp] at hx
      rcases Finset.mem_union.1 hx with hx | hx
      · rw [hVp] at hx
        obtain ⟨hx, hF⟩ := Finset.mem_filter.1 hx
        obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.1 hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
        exact hVlV _ ((hSvals u (hpS u (List.mem_toFinset.1 hu)) k).resolve_left hF)
      · exact hCVV x hx
    have hCp2 : 2 ≤ Cp.card := by
      rw [hCp]
      exact Finset.one_lt_card.2 ⟨0, Finset.mem_union_right _ h0CV,
        ValueType.nonzero, Finset.mem_union_right _ hnzCV, ValueType.nonzero_ne_zero.symm⟩
    -- as many counters over them as tuples in the derivation
    obtain ⟨Wp, hWp⟩ : ∃ Wp : Finset (Tuple T K'), Wp = Fintype.piFinset (fun _ : Fin K' => Cp) :=
      ⟨_, rfl⟩
    have hWpc : Wp.card = Cp.card ^ K' := by
      rw [hWp, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hlenWp : j + 1 ≤ Wp.card := by
      obtain ⟨A, hA⟩ : ∃ A : Finset T, A = Union.union Cp FreeFin := ⟨_, rfl⟩
      have hpA : ∀ u ∈ p.toFinset, ∀ k, u k ∈ A := by
        intro u hu k
        rw [hA, hCp]
        by_cases hF : F (u k)
        · rcases hFcases _ hF with h | h
          · exact Finset.mem_union_right _ h
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          rw [hVp]
          exact Finset.mem_filter.2
            ⟨Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_image_of_mem u (Finset.mem_univ k)⟩, hF⟩
      have hAc : A.card ≤ Cp.card + 2 * c + 1 := by
        rw [hA]
        have := Finset.card_union_le Cp FreeFin
        omega
      have h1 := card_le_of_vals p.toFinset A hpA
      rw [List.toFinset_card_of_nodup hnd, hplen] at h1
      rw [hWpc, hK'e]
      exact le_trans h1 (card_arith_chain hCp2 hAc)
    have hWpW : ∀ x ∈ Wp, x ∈ W := by
      intro x hx
      rw [hWp] at hx
      rw [hW]
      exact (mem_powT K' x).2 fun k => hCpV _ (Fintype.mem_piFinset.1 hx k)
    have hWpabs : ∀ x ∈ Wp, X * w x = X := by
      intro x hx
      rw [hWp] at hx
      rw [hw]
      show X * ∏ k, ev (x k) = X
      refine Finset.prod_induction (fun k => ev (x k)) (fun y => X * y = X)
        (fun a b ha hb => by rw [← mul_assoc, ha, hb]) (mul_one X) fun k _ => ?_
      exact habsorb X _ (hXC _ (Fintype.mem_piFinset.1 hx k))
    -- a chain of them, listed from its end
    obtain ⟨lw, hlw, hlwlen, hlwmem⟩ := exists_sorted_counters K' Wp
    have hmemW : ∀ x ∈ (lw.take (j + 1)).reverse, x ∈ Wp := fun x hx =>
      hlwmem x (List.mem_of_mem_take (List.mem_reverse.1 hx))
    have hchlen : ((lw.take (j + 1)).reverse).length = p.length := by
      rw [List.length_reverse, List.length_take, hplen]
      omega
    refine ⟨(lw.take (j + 1)).reverse, hchlen,
      List.pairwise_reverse.2 (hlw.sublist (List.take_sublist _ _)),
      fun x hx => hWpW x (hmemW x hx), ?_⟩
    refine pw_absorb w X _ (fun h => ?_) (fun x hx => hWpabs x (hmemW x hx))
    rw [h] at hchlen
    simp at hchlen
    omega
  -- the rounds' tuples, where the body settles
  have hLrow : ∀ j t, t ∈ PathSum.supp (PathSum.rounds B G j) →
      q₁'.AnnSettlesAt d γ (E.assignHole s
        ({GenRow.ofAnnotated (t, 1)} : Multiset (GenRow T K n))) := by
    intro j t ht
    have htm : t ∈ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E) (j + 1)) := by
      rw [← muIter_congr_iter hiter, hstep, muIter_eq_iterate, PathSum.iterate_stepK_eq,
        PathSum.supp_dedupK]
      exact PathSum.mem_supp_trunc.2 ⟨j, Nat.lt_succ_self j, ht⟩
    have hsub : PathSum.supp ({((t, 1) : AnnotatedTuple T K n)} : Multiset (AnnotatedTuple T K n))
        ⊆ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E) (j + 1)) := fun v hv => by
      have : v = t := by simpa [PathSum.supp] using hv
      rw [this]; exact htm
    have h1 := annSettlesAt_of_recLinear_subset q₁ hq₁ hq₁x d γ E _ _ hsub (hsk (j + 1))
    exact (h₁ _ h1).1
  obtain ⟨l, -, -, -, hspec⟩ := chainSpec_of s n K' EQ q₀' q₁' hq₁' d γ E W hWn w hWa hnn
  refine ⟨annSettlesAt_simResultA_of s s' n K' true EQ (annSettlesAt_valRel ls cs) q₀' q₁' hq₁'
      d γ E h₀.1 ⟨l.length, hspec.rounds_eq_zero (le_refl l.length)⟩
      (fun k t c' hm => ((hspec.supp_rounds k t c').1 hm).1) hLrow, ?_⟩
  rw [← hMuSet]
  exact evaluate_simResultA_chain s s' n K' EQ q₀' q₁' hq₁' hq₁'x d γ E W hWn w hWa hnn S hSc
    hcard habs hgen hsS'

/-- **The all-chains counter is correct** at every instance, where `δ` is
the identity. -/
private theorem nodeCorrect_chain (cnt : SeqAggFunc T) (hδ : ∀ a : K, SemiringWithMonus.delta a = a) :
    NodeCorrect cnt true (fun _ : AnnotatedDatabase T K => True) :=
  fun s s' q₀ q₁ q₀' q₁' h₁ h₂ h₃ h₄ h₅ h₆ h₇ _ _ h₈ d _ γ E _ hs h₀ h₁' =>
    muSetSim_correct_chain cnt hδ s s' q₀ q₁ q₀' q₁' h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ d γ E hs h₀ h₁'

end ChainNode

/-! ## The node: a set recursion replaced by its successor simulation -/

section SuccNode

variable {c : ℕ}

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A property of the value alone is a bound. -/
private theorem valBd_closed (Vl : T → Prop) : BdClosed (K := K) (fun v _ => Vl v) :=
  ⟨fun _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h _ => h, fun _ _ _ h => h, fun _ _ h => h⟩

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- Two bounds together are one. -/
private theorem andBd_closed {B₁ B₂ : T → K → Prop} (h₁ : BdClosed B₁) (h₂ : BdClosed B₂) :
    BdClosed (fun v a => B₁ v a ∧ B₂ v a) :=
  ⟨fun v a b h => ⟨h₁.mul_right v a b h.1, h₂.mul_right v a b h.2⟩,
    fun v a b h => ⟨h₁.mul_left v a b h.1, h₂.mul_left v a b h.2⟩,
    fun v a b ha hb => ⟨h₁.add v a b ha.1 hb.1, h₂.add v a b ha.2 hb.2⟩,
    fun v a b h => ⟨h₁.monus v a b h.1, h₂.monus v a b h.2⟩,
    fun v a h => ⟨h₁.delta v a h.1, h₂.delta v a h.2⟩⟩

/-- **A tuple holding a value of `Z` weighs `𝟘`**, where every row is `𝟘`
on the values of `Z` it holds. -/
private theorem wt_ann_eq_zero_of_rowBd {F Z : T → Prop} {Bd : T → K → Prop}
    (hBd : ∀ v a, Bd v a → Z v → a = 0) {n : ℕ} {l : List (String × ℕ)}
    (q : AggQueryIn T c n (ColKind.allReg n) l) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) (h : ∀ r ∈ q.evaluate d γ E, RowBd F Bd r) (u : Tuple T n) (k : Fin n)
    (hF : ¬ F (u k)) (hZ : Z (u k)) : PathSum.wt (q.ann d γ E) u = 0 := by
  unfold PathSum.wt ann
  refine Multiset.sum_eq_zero fun a ha => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 ha
  obtain ⟨hp, hpu⟩ := Multiset.mem_filter.1 hp
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hp
  have hk : r.fst k = Sum.inl (u k) := by
    have h1 := evaluate_conform q d r hr k
    rw [← hpu]
    rcases hv : r.fst k with x | x
    · simp [GenRow.toAnnotated, GenRow.plainTuple, hv]
    · rw [hv] at h1; simp [GenValue.kindOf, ColKind.allReg, ColKind.base] at h1
  exact hBd _ _ ((h r hr k (u k) hk).resolve_left hF) hZ

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
private theorem prod_ind {m : ℕ} (Q : Fin m → Prop) [DecidablePred Q] [Decidable (∀ k, Q k)] :
    (∏ k, (if Q k then (1 : K) else 0)) = if ∀ k, Q k then 1 else 0 := by
  by_cases h : ∀ k, Q k
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun k _ => by rw [ite_eq_left (h k)]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [ite_eq_right hk])

set_option maxHeartbeats 1000000 in
/-- **A set recursion is its successor simulation**, where `δ` is the
support map and the semiring settles its linear recursions within twice the
size of their tuple set (`PathSum.SettlesLinear`), at every instance where the recursion settles –
rows annotated `𝟘` included – given matches `q₀'`, `q₁'` of its base and
body that agree with them wherever these settle. A counter value held only
by rows annotated `𝟘` is annotated `𝟘`, and so is every row holding it, so
the derivations of non-zero weight live on the counters annotated `𝟙`. -/
theorem muSetSim_correct_succ (cnt : SeqAggFunc T)
    (hδ : ∀ a : K, a ≠ 0 → SemiringWithMonus.delta a = 1) (hK : PathSum.SettlesLinear K)
    {n : ℕ} (s s' : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (hq₁ : q₁.recLinear s n) (hq₁x : q₁.noExplode) (hq₁' : q₁'.recLinear s n)
    (hq₁'x : q₁'.noExplode) (hsig : (MuSet s q₀ q₁).inSig {cnt})
    (hhyg : (MuSet s q₀ q₁).hygienic) (hx : (MuSet s q₀ q₁).noExplode)
    {ρc : Fin c → ColKind} {HK : HoleKinds} (hwk : (MuSet s q₀ q₁).wellKinded ρc HK)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (hset : (MuSet s q₀ q₁).AnnSettlesAt d γ E)
    (h₀ : q₀'.AnnSettlesAt d γ E ∧ q₀'.evaluate d γ E = q₀.evaluate d γ E)
    (h₁ : ∀ X : AnnotatedRelation T K n,
      q₁.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated)) →
        q₁'.AnnSettlesAt d γ (E.assignHole s (X.map GenRow.ofAnnotated))
          ∧ q₁'.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))
            = q₁.evaluate d γ (E.assignHole s (X.map GenRow.ofAnnotated))) :
    (muSetSim false s s' q₀ q₁ q₀' q₁').AnnSettlesAt d γ E
      ∧ (muSetSim false s s' q₀ q₁ q₀' q₁').evaluate d γ E
        = (MuSet s q₀ q₁).evaluate d γ E := by
  classical
  obtain ⟨hs₀, hsS, hsk⟩ := hset
  -- the two set recursions have the same iterates
  have hiter : ∀ k, muSetStep s q₀' q₁' d γ E (muIter (muSetStep s q₀ q₁ d γ E) k)
      = muSetStep s q₀ q₁ d γ E (muIter (muSetStep s q₀ q₁ d γ E) k) := fun k => by
    have h1 := (h₁ _ (hsk k)).2
    generalize muIter (muSetStep s q₀ q₁ d γ E) k = X at h1 ⊢
    unfold muSetStep evaluateAnnotated
    rw [h₀.2, h1]
  have hfix := muFix_congr_iter hiter
  have hsS' := muSetSettles_congr_iter hiter hsS
  have hMuSet : (MuSet s q₀' q₁').evaluate d γ E = (MuSet s q₀ q₁).evaluate d γ E := by
    rw [evaluate_MuSet, evaluate_MuSet, hfix]
  -- the recursion of `PathSum` the matches give
  set B := q₀'.ann d γ E with hB
  set G := fun u => q₁'.ann d γ (E.assignHole s
    ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) with hG
  have hstep : muSetStep s q₀' q₁' d γ E = PathSum.stepK B G := funext fun X => by
    rw [muSetStep, dedupAnn_eq_dedupK, PathSum.stepK]
    congr 2
    exact ann_of_recLinear q₁' hq₁' hq₁'x d γ E X
  have hsK : MuSetSettles (PathSum.stepK B G) := hstep ▸ hsS'
  -- the counters, annotated `𝟙` where none of their values weighs `𝟘`
  set ls := ctrLeaves s q₀ q₁ with hls
  set cs := ctrConsts s q₀ q₁ with hcs
  set EQ : AggQueryIn T c 1 (ColKind.allReg 1) := valRel ls cs with hEQ
  set K' := ctrWidth c n with hK'
  have hK'e : K' = (2 * c + 2) * n + 2 := rfl
  set V := ((EQ.ann d γ E).map Prod.fst).dedup with hV
  set W := powT V K' with hW
  set Z : T → Prop := fun x => PathSum.wt (EQ.ann d γ E) (fun _ => x) = 0 with hZ
  set P : Tuple T K' → Prop := fun v => ∀ k, ¬ Z (v k) with hP
  have hWn : W.Nodup := nodup_powT (Multiset.nodup_dedup _) K'
  have hWa : (ctr EQ K').ann d γ E
      = W.map (fun v => ((v, @ite K (P v) (Classical.propDecidable _) 1 0)
        : AnnotatedTuple T K K')) := by
    rw [show (ctr EQ K').ann d γ E = (powT V K').map (fun v =>
        ((v, ∏ k, SemiringWithMonus.delta (PathSum.wt (EQ.ann d γ E) (fun _ => v k)))
          : AnnotatedTuple T K K')) from
      ann_pow (dedupG EQ) V (fun x => SemiringWithMonus.delta (PathSum.wt (EQ.ann d γ E) x))
        d γ E (by rw [ann_dedupG]) K']
    refine Multiset.map_congr rfl fun v _ => Prod.ext rfl ?_
    show (∏ k, SemiringWithMonus.delta (PathSum.wt (EQ.ann d γ E) (fun _ => v k))) = _
    rw [Finset.prod_congr rfl (g := fun k => if ¬ Z (v k) then (1 : K) else 0) fun k _ => by
      by_cases hz : Z (v k)
      · rw [ite_eq_right (fun h => h hz)]
        show SemiringWithMonus.delta _ = _
        rw [show PathSum.wt (EQ.ann d γ E) (fun _ => v k) = 0 from hz]
        exact SemiringWithMonus.delta_zero
      · rw [ite_eq_left hz]
        exact hδ _ hz, prod_ind]
    show _ = @ite K (P v) (Classical.propDecidable _) 1 0
    congr
  have hVnn : ∀ v ∈ V, ValueType.isNull (v 0) = false := fun v hv => by
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_dedup.1 hv)
    exact (mem_ann_valRel hp).1
  have hnn := nonNull_powT hVnn K'
  -- the tuples of the settled value
  set S := PathSum.supp (muFix (PathSum.stepK B G)) with hS
  have hSc : PathSum.Closed S B G := closed_supp_muFix B G hsK
  -- the free values: the null, the constants, and the context's
  set F : T → Prop := fun x => ValueType.isNull x = true ∨ x ∈ (MuSet s q₀ q₁).allConsts
    ∨ (∃ k, (ρc k).base ≠ ColKind.agg ∧ γ k = x) ∨ ∃ k, E.ctxAt c γ k = Sum.inl x with hFdef
  set Vl : T → Prop := fun x => (fun _ => x) ∈ (EQ.ann d γ E).map Prod.fst with hVl
  set Bd : T → K → Prop := fun v a => Vl v ∧ zeroBd Z v a with hBd
  have hBc : BdClosed Bd := andBd_closed (valBd_closed Vl) (zeroBd_closed Z)
  have hD : ∀ p ∈ (MuSet s q₀ q₁).relLeaves, ∀ r : AnnotatedRelation T K p.1,
      d.find p.1 p.2 = some r → ∀ a ∈ r, TupBd F Bd (a.1, a.2) := by
    intro p hp r hr a ha k
    by_cases hn : ValueType.isNull (a.1 k) = true
    · exact Or.inl (Or.inl hn)
    · have hn' : ValueType.isNull (a.1 k) = false := by simpa using hn
      have hrow := mem_ann_valRel_of_leaf (cs := cs) d γ E
        (mem_leaves_of_mem_relLeaves _ hhyg p hp) hr ha k hn'
      refine Or.inr ⟨Multiset.mem_map.2 ⟨_, hrow, rfl⟩, fun hz => ?_⟩
      have hz' : PathSum.wt (EQ.ann d γ E) (fun _ => a.1 k) = 0 := hz
      have h1 := le_wt_of_mem hrow
      exact le_antisymm (le_trans h1 (le_of_eq hz')) zero_le
  have hc : ∀ x ∈ (MuSet s q₀ q₁).allConsts, F x := fun x hx => Or.inr (Or.inl hx)
  have hγF : ∀ k, (ρc k).base ≠ ColKind.agg → F (γ k) := fun k hk =>
    Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))
  have hctxF : ∀ k v, E.ctxAt c γ k = Sum.inl v → F v := fun k v hk =>
    Or.inr (Or.inr (Or.inr ⟨k, hk⟩))
  have hrowsM : ∀ r ∈ (MuSet s q₀ q₁).evaluate d γ E, RowBd F Bd r :=
    rowBd_evaluate hBc (MuSet s q₀ q₁) hsig hx hwk F hc hD γ E hγF hctxF
      (fun p hp => absurd hp List.not_mem_nil)
  have hrows₀ : ∀ r ∈ q₀.evaluate d γ E, RowBd F Bd r :=
    rowBd_evaluate hBc q₀ hsig.1 hx.1 hwk.1 F (fun x hx => hc x (Finset.mem_union_left _ hx))
      (fun p hp => hD p (List.mem_append_left _ hp)) γ E hγF hctxF
      (fun p hp => absurd hp List.not_mem_nil)
  have hrows₁ : ∀ u : Tuple T n, ∀ r ∈ q₁.evaluate d γ (E.assignHole s
      ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))),
      RowBd (fun x => F x ∨ ∃ k, u k = x) Bd r := fun u =>
    rowBd_evaluate hBc q₁ hsig.2 hx.2 hwk.2 _
      (fun x hx => Or.inl (hc x (Finset.mem_union_right _ hx)))
      (fun p hp r hr a ha k => (hD p (List.mem_append_right _ hp) r hr a ha k).imp Or.inl id) γ _
      (fun k hk => Or.inl (hγF k hk))
      (fun k v hk => Or.inl (hctxF k v (by simpa only [EvalEnv.ctxAt_assignHole] using hk)))
      (holesBd_assignHole s fun r hr => by
        rw [Multiset.mem_singleton] at hr
        subst hr
        exact rowBd_ofAnnotated fun k => Or.inl (Or.inr ⟨k, rfl⟩))
  -- the tuples of `S` hold free values and counter values
  have hSvals : ∀ t ∈ S, ∀ k, F (t k) ∨ Vl (t k) := by
    intro t ht k
    obtain ⟨⟨t', a⟩, hp, rfl⟩ := PathSum.mem_supp.1 ht
    have hm : GenRow.ofAnnotated ((t', a) : AnnotatedTuple T K n)
        ∈ (MuSet s q₀ q₁).evaluate d γ E := by
      rw [← hMuSet, evaluate_MuSet_of_recLinear s q₀' q₁' hq₁' hq₁'x d γ E]
      exact Multiset.mem_map_of_mem _ hp
    exact (hrowsM _ hm k (t' k) rfl).imp id (fun h => h.1)
  -- the free values, as a finite set
  set FreeFin : Finset T := Union.union (Union.union (ValueType.nullVal : Option T).toFinset
    (Finset.univ.image γ)) (Finset.univ.biUnion (fun k => match E.ctxAt c γ k with
      | Sum.inl x => {x}
      | Sum.inr _ => ∅)) with hFreeFin
  have hFreeCard : FreeFin.card ≤ 1 + c + c := by
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
      · cases (ValueType.nullVal : Option T) <;> simp
      · exact le_trans Finset.card_image_le (by simp)
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => 1) fun k _ => ?_) (by simp)
      split <;> simp
  set CV : Finset T := (cs.toFinset).filter (fun x => ValueType.isNull x = false) with hCV
  have hFcases : ∀ x, F x → x ∈ FreeFin ∨ x ∈ CV := by
    intro x hx
    rcases hx with hn | hcx | ⟨k, -, rfl⟩ | ⟨k, hk⟩
    · left
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      rw [(ValueType.isNull_iff_nullVal x).1 hn]
      exact Finset.mem_singleton_self x
    · cases hn : ValueType.isNull x
      · right
        refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 (List.mem_append_left _
          (Finset.mem_toList.2 hcx)), hn⟩
      · left
        refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        rw [(ValueType.isNull_iff_nullVal x).1 hn]
        exact Finset.mem_singleton_self x
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem γ (Finset.mem_univ k))))
    · refine Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, ?_⟩))
      rw [hk]
      exact Finset.mem_singleton_self x
  have hCVrow : ∀ x ∈ CV, (((fun _ => x), 1) : AnnotatedTuple T K 1) ∈ EQ.ann d γ E := by
    intro x hx
    obtain ⟨hx, hn⟩ := Finset.mem_filter.1 hx
    exact mem_ann_valRel_of_const d γ E (List.mem_toFinset.1 hx) hn
  have hCVV : ∀ x ∈ CV, (fun _ => x) ∈ V := fun x hx =>
    Multiset.mem_dedup.2 (Multiset.mem_map.2 ⟨_, hCVrow x hx, rfl⟩)
  have h0CV : (0 : T) ∈ CV := Finset.mem_filter.2 ⟨List.mem_toFinset.2
    (List.mem_append_right _ (by simp)), ValueType.isNull_zero⟩
  have hnzCV : (ValueType.nonzero : T) ∈ CV := Finset.mem_filter.2 ⟨List.mem_toFinset.2
    (List.mem_append_right _ (by simp)), ValueType.isNull_nonzero⟩
  have hVlV : ∀ x, Vl x → (fun _ => x) ∈ V := fun x hx => Multiset.mem_dedup.2 hx
  have hcard : S.card ≤ W.card := by
    obtain ⟨AV, hAV⟩ : ∃ AV : Finset T, AV = Union.union (V.map (fun v => v 0)).toFinset FreeFin :=
      ⟨_, rfl⟩
    have hSAV : ∀ t ∈ S, ∀ k, t k ∈ AV := by
      intro t ht k
      rw [hAV]
      rcases hSvals t ht k with hF | hv
      · rcases hFcases _ hF with h | h
        · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_left _ (Multiset.mem_toFinset.2
            (Multiset.mem_map.2 ⟨_, hCVV _ h, rfl⟩))
      · exact Finset.mem_union_left _ (Multiset.mem_toFinset.2
          (Multiset.mem_map.2 ⟨_, hVlV _ hv, rfl⟩))
    have hm2 : 2 ≤ V.card := by
      rw [← Multiset.toFinset_card_of_nodup (Multiset.nodup_dedup _)]
      refine Finset.one_lt_card.2 ⟨fun _ => 0, Multiset.mem_toFinset.2 (hCVV 0 h0CV),
        fun _ => ValueType.nonzero, Multiset.mem_toFinset.2 (hCVV _ hnzCV), ?_⟩
      intro h
      exact ValueType.nonzero_ne_zero (congrFun h 0).symm
    have hAVc : AV.card ≤ V.card + 2 * c + 1 := by
      rw [hAV]
      have := Finset.card_union_le (V.map (fun v => v 0)).toFinset FreeFin
      have h2 : (V.map (fun v => v 0)).toFinset.card ≤ V.card :=
        le_trans (Multiset.toFinset_card_le _) (by rw [Multiset.card_map])
      omega
    rw [hW, card_powT, hK'e]
    exact le_trans (card_le_of_vals S AV hSAV) (card_arith_chain hm2 hAVc)
  have hB_eq : B = q₀.ann d γ E := by rw [hB, ann, ann, h₀.2]
  have hG_eq : ∀ u ∈ S, G u = q₁.ann d γ (E.assignHole s
      ({GenRow.ofAnnotated (u, 1)} : Multiset (GenRow T K n))) := by
    intro u hu
    have hfS : muFix (PathSum.stepK B G)
        = muIter (muSetStep s q₀ q₁ d γ E) (muFixIdx (muSetStep s q₀ q₁ d γ E)) := by
      rw [← hstep, hfix]; rfl
    have hsub : PathSum.supp ({((u, 1) : AnnotatedTuple T K n)} : Multiset (AnnotatedTuple T K n))
        ⊆ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E)
          (muFixIdx (muSetStep s q₀ q₁ d γ E))) := fun v hv => by
      have : v = u := by simpa [PathSum.supp] using hv
      rw [this, ← hfS]; exact hu
    have h1 := annSettlesAt_of_recLinear_subset q₁ hq₁ hq₁x d γ E _ _ hsub (hsk _)
    have h2 := (h₁ _ h1).2
    rw [Multiset.map_singleton] at h2
    rw [hG]
    simp only [ann]
    rw [h2]
  have hzBd : ∀ v a, Bd v a → Z v → a = 0 := fun v a h hz => h.2 hz
  -- the tuples of non-zero weight: those holding no value of `Z` but free ones
  have hS' : ∃ S' : Finset (Tuple T n), S' ⊆ S ∧ (∀ u, u ∉ S' → PathSum.wt B u = 0)
      ∧ (∀ u ∈ S', ∀ v, v ∉ S' → PathSum.wt (G u) v = 0)
      ∧ (S' = ∅ ∨ 2 * S'.card + 1
        ≤ (W.filter (fun x => @decide (P x) (Classical.propDecidable _) = true)).card) := by
    by_cases h10 : (1 : K) = 0
    · have h0 : ∀ x : K, x = 0 := fun x => by rw [← mul_one x, h10, mul_zero]
      exact ⟨∅, Finset.empty_subset _, fun u _ => h0 _, fun u _ v _ => h0 _, Or.inl rfl⟩
    refine ⟨S.filter (fun t => ∀ k, F (t k) ∨ ¬ Z (t k)), Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · intro u hu
      by_cases huS : u ∈ S
      · have : ∃ k, ¬ F (u k) ∧ Z (u k) := by
          by_contra hne
          push Not at hne
          exact hu (Finset.mem_filter.2 ⟨huS, fun k => by
            by_cases hF : F (u k)
            · exact Or.inl hF
            · exact Or.inr (hne k hF)⟩)
        obtain ⟨k, hF, hz⟩ := this
        rw [hB_eq]
        exact wt_ann_eq_zero_of_rowBd hzBd q₀ d γ E hrows₀ u k hF hz
      · exact PathSum.wt_eq_zero_of_notMem fun h => huS (hSc.base h)
    · intro u hu v hv
      have huS := (Finset.mem_filter.1 hu).1
      by_cases hvS : v ∈ S
      · have : ∃ k, ¬ F (v k) ∧ Z (v k) := by
          by_contra hne
          push Not at hne
          exact hv (Finset.mem_filter.2 ⟨hvS, fun k => by
            by_cases hF : F (v k)
            · exact Or.inl hF
            · exact Or.inr (hne k hF)⟩)
        obtain ⟨k, hF, hz⟩ := this
        rw [hG_eq u huS]
        refine wt_ann_eq_zero_of_rowBd hzBd q₁ d γ _ (hrows₁ u) v k (fun h => ?_) hz
        rcases h with h | ⟨k', hk'⟩
        · exact hF h
        · rcases (Finset.mem_filter.1 hu).2 k' with h' | h'
          · exact hF (hk' ▸ h')
          · exact h' (hk' ▸ hz)
      · exact PathSum.wt_eq_zero_of_notMem fun h => hvS (hSc.step u huS h)
    · -- the values of these tuples, and the counters over them
      obtain ⟨V1, hV1⟩ : ∃ V1 : Finset T,
          V1 = ((V.map (fun v => v 0)).toFinset).filter (fun x => ¬ Z x) := ⟨_, rfl⟩
      have hCVnz : ∀ x ∈ CV, ¬ Z x := fun x hx hz => by
        have hz' : PathSum.wt (EQ.ann d γ E) (fun _ => x) = 0 := hz
        have h1 := le_wt_of_mem (hCVrow x hx)
        exact h10 (le_antisymm (le_trans h1 (le_of_eq hz')) zero_le)
      have hCV1 : ∀ x ∈ CV, x ∈ V1 := fun x hx => by
        rw [hV1]
        exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (Multiset.mem_map.2
          ⟨_, hCVV x hx, rfl⟩), hCVnz x hx⟩
      have hV1V : ∀ x ∈ V1, (fun _ => x) ∈ V ∧ ¬ Z x := fun x hx => by
        rw [hV1] at hx
        obtain ⟨hx, hz⟩ := Finset.mem_filter.1 hx
        obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hx)
        refine ⟨?_, hz⟩
        have : (fun _ : Fin 1 => v 0) = v := funext fun i => by rw [Fin.fin_one_eq_zero i]
        rw [this]; exact hv
      have hV12 : 2 ≤ V1.card := Finset.one_lt_card.2 ⟨0, hCV1 0 h0CV, ValueType.nonzero,
        hCV1 _ hnzCV, ValueType.nonzero_ne_zero.symm⟩
      obtain ⟨A, hA⟩ : ∃ A : Finset T, A = Union.union V1 FreeFin := ⟨_, rfl⟩
      have hS'A : ∀ t ∈ S.filter (fun t => ∀ k, F (t k) ∨ ¬ Z (t k)), ∀ k, t k ∈ A := by
        intro t ht k
        obtain ⟨htS, ht'⟩ := Finset.mem_filter.1 ht
        rw [hA]
        rcases ht' k with hF | hz
        · rcases hFcases _ hF with h | h
          · exact Finset.mem_union_right _ h
          · exact Finset.mem_union_left _ (hCV1 _ h)
        · rcases hSvals t htS k with hF | hv
          · rcases hFcases _ hF with h | h
            · exact Finset.mem_union_right _ h
            · exact Finset.mem_union_left _ (hCV1 _ h)
          · refine Finset.mem_union_left _ ?_
            rw [hV1]
            exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (Multiset.mem_map.2
              ⟨_, hVlV _ hv, rfl⟩), hz⟩
      have hAc : A.card ≤ V1.card + 2 * c + 1 := by
        rw [hA]
        have := Finset.card_union_le V1 FreeFin
        omega
      obtain ⟨Wp, hWp⟩ : ∃ Wp : Finset (Tuple T K'), Wp = Fintype.piFinset (fun _ : Fin K' => V1) :=
        ⟨_, rfl⟩
      have hWpc : Wp.card = V1.card ^ K' := by
        rw [hWp, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hWpsub : Wp ⊆ (W.filter (fun x => @decide (P x) (Classical.propDecidable _)
          = true)).toFinset := by
        intro x hx
        rw [hWp] at hx
        refine Multiset.mem_toFinset.2 (Multiset.mem_filter.2 ⟨?_, ?_⟩)
        · rw [hW]
          exact (mem_powT K' x).2 fun k => (hV1V _ (Fintype.mem_piFinset.1 hx k)).1
        · exact @decide_eq_true _ (Classical.propDecidable _)
            fun k => (hV1V _ (Fintype.mem_piFinset.1 hx k)).2
      have h1 := Finset.card_le_card hWpsub
      rw [Multiset.toFinset_card_of_nodup (Multiset.Nodup.filter _ hWn), hWpc] at h1
      have h2 := card_le_of_vals _ A hS'A
      have h3 : 2 * A.card ^ n + 1 ≤ V1.card ^ K' := by
        rw [hK'e]; exact card_arith_succ hV12 hAc
      exact Or.inr (by omega)
  obtain ⟨S', hsub, hb', hg', hcard'⟩ := hS'
  -- the rounds' tuples, where the body settles
  have hLrow : ∀ j t, t ∈ PathSum.supp (PathSum.rounds B G j) →
      q₁'.AnnSettlesAt d γ (E.assignHole s
        ({GenRow.ofAnnotated (t, 1)} : Multiset (GenRow T K n))) := by
    intro j t ht
    have htm : t ∈ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E) (j + 1)) := by
      rw [← muIter_congr_iter hiter, hstep, muIter_eq_iterate, PathSum.iterate_stepK_eq,
        PathSum.supp_dedupK]
      exact PathSum.mem_supp_trunc.2 ⟨j, Nat.lt_succ_self j, ht⟩
    have hsub : PathSum.supp ({((t, 1) : AnnotatedTuple T K n)} : Multiset (AnnotatedTuple T K n))
        ⊆ PathSum.supp (muIter (muSetStep s q₀ q₁ d γ E) (j + 1)) := fun v hv => by
      have : v = t := by simpa [PathSum.supp] using hv
      rw [this]; exact htm
    have h1 := annSettlesAt_of_recLinear_subset q₁ hq₁ hq₁x d γ E _ _ hsub (hsk (j + 1))
    exact (h₁ _ h1).1
  obtain ⟨l, -, -, -, hspec⟩ := simSpec_of s n K' EQ q₀' q₁' hq₁' d γ E W hWn P hWa hnn
  refine ⟨annSettlesAt_simResultA_of s s' n K' false EQ (annSettlesAt_valRel ls cs) q₀' q₁' hq₁'
      d γ E h₀.1 ⟨l.length, hspec.rounds_eq_zero (le_refl l.length)⟩
      (fun k t c' hm => ((hspec.supp_rounds k t c').1 hm).1) hLrow, ?_⟩
  rw [← hMuSet]
  exact evaluate_simResultA s s' n K' EQ q₀' q₁' hq₁' hq₁'x d γ E W hWn P hWa hnn S S' hSc hsub
    hb' hg' hcard hcard' hK hsS'

/-- **The successor counter is correct** at every instance, where `δ` is the
support map and the semiring settles its linear recursions within twice
the size of their tuple set. -/
private theorem nodeCorrect_succ (cnt : SeqAggFunc T)
    (hδ : ∀ a : K, a ≠ 0 → SemiringWithMonus.delta a = 1) (hK : PathSum.SettlesLinear K) :
    NodeCorrect cnt false (fun _ : AnnotatedDatabase T K => True) :=
  fun s s' q₀ q₁ q₀' q₁' h₁ h₂ h₃ h₄ h₅ h₆ h₇ _ _ h₈ d _ γ E _ hs h₀ h₁' =>
    muSetSim_correct_succ cnt hδ hK s s' q₀ q₁ q₀' q₁' h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ d γ E hs h₀ h₁'

end SuccNode

end AggQueryIn

/-! ## The annotated basis with `ε` and without `μ^∪`, where `δ` is the identity -/

/-- **`μ^∪` is dispensable beside `μ^⊎` and `ε` in the annotated algebra
where `δ` is the identity** – the Boolean algebras and the min-max
semirings, over every instance: the classes
`{∅, Π, σ, apply, γ, win, μ^⊎, ε, −}` match every query of the annotated
algebra in the minimal universe, every set recursion written as its
all-chains simulation. -/
theorem generatesAnn_annEpsOps_of_delta_id (sch : Schema) (cnt : SeqAggFunc T)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) :
    GeneratesAnn T K sch cnt annEpsOps := by
  intro n κ q ho hu hi ha hp
  obtain ⟨q', ho', hu', hi', ha', hp', hm⟩ := generatesAnnOn_annEpsOps_of sch cnt true
    (AggQueryIn.nodeCorrect_chain cnt hδ) q ho hu hi ha hp
  exact ⟨q', ho', hu', hi', ha', hp', fun d γ hs => hm d γ trivial hs⟩

/-- **`μ^∪` is dispensable beside `μ^⊎` and `ε` in the annotated algebra
where `δ` is the support map**, over every instance – rows annotated `𝟘`
included – in the semirings that settle their linear recursions within
twice the size of their tuple set (`PathSum.SettlesLinear`: absorptive, `⊕`
cancellative with no zero divisors, or `⊗` equal to `⊕` on non-zero values –
`ℕ`, `ℕ[X]`, the tropical, Viterbi and Łukasiewicz semirings, `Lin[X]`):
the classes `{∅, Π, σ, apply, γ, win, μ^⊎, ε, −}` match every query of the
annotated algebra in the minimal universe, every set recursion written as
its successor simulation. -/
theorem generatesAnn_annEpsOps_of_support (sch : Schema) (cnt : SeqAggFunc T)
    (hδ : ∀ a : K, a ≠ 0 → SemiringWithMonus.delta a = 1) (hK : PathSum.SettlesLinear K) :
    GeneratesAnn T K sch cnt annEpsOps := by
  intro n κ q ho hu hi ha hp
  obtain ⟨q', ho', hu', hi', ha', hp', hm⟩ := generatesAnnOn_annEpsOps_of sch cnt false
    (AggQueryIn.nodeCorrect_succ cnt hδ hK) q ho hu hi ha hp
  exact ⟨q', ho', hu', hi', ha', hp', fun d γ hs => hm d γ trivial hs⟩
