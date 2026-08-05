/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryGenBridges
import Provenance.HavingProbability

/-!
# Possible-world foundations for the general evaluator

The token-level ingredients of the random-world commutation for
`QueryGen.evaluateGen` over `𝔹[X]` (the general-evaluator counterpart of
`randomWorld_evaluateAnnotated`, whose target statement is

`genRandomWorld v (q.evaluateGen d) = q.evaluatePlain (d.randomWorld v)`

– under a valuation `v`, specializing the general evaluation's surviving
rows is the plain evaluation of the realized world):

* `AggValue.realized` – the positions of a token's occurrences realized
  by a valuation, and `AggValue.specialize_eval` connecting the
  world-faithful reading `specialize` to the per-world reading `valOn`
  at the realized world;
* `AggValue.predProv_eval_iff` – **the token-level PQE bridge**: under a
  valuation, the predicate provenance of a comparison against a token is
  true iff the realized group is non-empty and its aggregate value
  satisfies the comparison. This is `havingProv_eval_iff` transported to
  tokens; the σ-aggregate case of the commutation reduces to it;
* `GenRow.specializeTuple` and `genRandomWorld` – the specialized reading
  of a row and the realized world of a general evaluation: the rows whose
  finalized annotation is true, with tokens specialized.
-/

variable {T : Type} [ValueType T]
variable {X : Type} [Fintype X] [DecidableEq X]

open HavingProbability

namespace AggValue

/-- The positions of a token's occurrences realized by a valuation. -/
def realized (a : AggValue T (BoolFunc X)) (v : X → Bool) :
    Finset (Fin a.occs.length) :=
  Finset.univ.filter (fun i => a.anns i v = true)

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- The world-faithful reading under a valuation is the per-world reading
at the realized world. -/
theorem specialize_eval (a : AggValue T (BoolFunc X)) (v : X → Bool) :
    a.specialize (fun α => α v) = a.valOn (a.realized v) := by
  rw [AggValue.specialize_eq_valOn]
  congr 1

/-- **The token-level PQE bridge.** Under a valuation `v`, the predicate
provenance of `⟨token⟩ op c` is true iff the token's realized group is
non-empty and its specialized aggregate value satisfies the comparison.
The σ-aggregate case of the random-world commutation reduces to this. -/
theorem predProv_eval_iff (a : AggValue T (BoolFunc X)) (op : CompOp)
    (c : T) (v : X → Bool) :
    (a.predProv op c) v = true
      ↔ (a.realized v).Nonempty
        ∧ op.eval (a.specialize (fun α => α v)) c := by
  rw [AggValue.specialize_eval]
  unfold AggValue.predProv
  rw [sum_eval_eq_true_iff]
  constructor
  · rintro ⟨W, hW, hWv⟩
    obtain ⟨-, hne⟩ := Finset.mem_filter.mp hW
    have hsplit : ((Having.worldAnn a.anns W) v
        && (Having.chi (K := BoolFunc X) op (a.valOn W) c) v) = true := hWv
    rw [Bool.and_eq_true] at hsplit
    have hWeq : W = a.realized v :=
      (worldAnn_eval_iff a.anns W v).mp hsplit.1
    subst hWeq
    exact ⟨hne, (chi_eval_iff op _ c v).mp hsplit.2⟩
  · rintro ⟨hne, hP⟩
    refine ⟨a.realized v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, ?_⟩
    have hgoal : ((Having.worldAnn a.anns (a.realized v)) v
        && (Having.chi (K := BoolFunc X) op
              (a.valOn (a.realized v)) c) v) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(worldAnn_eval_iff a.anns _ v).mpr rfl,
        (chi_eval_iff op _ c v).mpr hP⟩
    exact hgoal

end AggValue

/-- The specialized reading of a lifted value: regular values are
themselves, a token aggregates its realized occurrences. -/
def GenValue.specializeAt (v : X → Bool) :
    GenValue T (BoolFunc X) → T :=
  Sum.elim id (fun a => a.specialize (fun α => α v))

/-- The specialized reading of a row's tuple. -/
def GenRow.specializeTuple (v : X → Bool)
    (u : Tuple (GenValue T (BoolFunc X)) n) : Tuple T n :=
  fun k => GenValue.specializeAt v (u k)

/-- The realized world of a general evaluation: the rows whose finalized
annotation is true under the valuation, with tokens specialized. -/
def genRandomWorld (v : X → Bool)
    (R : Multiset (GenRow T (BoolFunc X) n)) : Multiset (Tuple T n) :=
  (R.filter (fun r => r.snd.finalize v = true)).map
    (fun r => GenRow.specializeTuple v r.fst)

/-! ## Evaluation of factored annotations -/

omit [Fintype X] [DecidableEq X] in
private lemma multiset_sum_eval (s : Multiset (BoolFunc X)) (v : X → Bool) :
    s.sum v = true ↔ ∃ f ∈ s, f v = true := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.sum_zero, Multiset.notMem_zero, false_and,
      exists_false, iff_false]
    exact Bool.false_ne_true
  | cons a s ih =>
    rw [Multiset.sum_cons]
    show (a v || s.sum v) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨f, hf, hfv⟩)
      exacts [⟨a, Multiset.mem_cons_self a s, h⟩,
        ⟨f, Multiset.mem_cons_of_mem hf, hfv⟩]
    · rintro ⟨f, hf, hfv⟩
      rcases Multiset.mem_cons.mp hf with rfl | hf
      exacts [Or.inl hfv, Or.inr ⟨f, hf, hfv⟩]

omit [Fintype X] [DecidableEq X] in
private lemma multiset_prod_eval (s : Multiset (BoolFunc X)) (v : X → Bool) :
    s.prod v = true ↔ ∀ f ∈ s, f v = true := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero, Multiset.notMem_zero, false_implies,
      implies_true, iff_true]
    rfl
  | cons a s ih =>
    rw [Multiset.prod_cons]
    show (a v && s.prod v) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨ha, hs⟩ f hf
      rcases Multiset.mem_cons.mp hf with rfl | hf
      exacts [ha, hs f hf]
    · intro h
      exact ⟨h a (Multiset.mem_cons_self a s),
        fun f hf => h f (Multiset.mem_cons_of_mem hf)⟩

/-- Truth of a group's existence guard under a valuation: some occurrence
annotation is realized. -/
def annGuard (l : List (BoolFunc X)) (v : X → Bool) : Prop :=
  ∃ κ ∈ l, κ v = true

instance (l : List (BoolFunc X)) (v : X → Bool) :
    Decidable (annGuard l v) :=
  inferInstanceAs (Decidable (∃ κ ∈ l, κ v = true))

omit [Fintype X] [DecidableEq X] in
private lemma list_sum_eval (l : List (BoolFunc X)) (v : X → Bool) :
    l.sum v = true ↔ annGuard l v := by
  rw [← Multiset.sum_coe, multiset_sum_eval]
  rfl

omit [Fintype X] [DecidableEq X] in
/-- Pointwise truth of a finalized factored annotation: the concrete part
holds and every pending group is realized non-empty (`δ` is the identity
on `𝔹[X]`). -/
theorem GenAnn.finalize_eval_iff (a : GenAnn (BoolFunc X)) (v : X → Bool) :
    a.finalize v = true
      ↔ a.base v = true ∧ ∀ l ∈ a.pending, annGuard l v := by
  show (a.base v
      && (a.pending.map (fun l => SemiringWithMonus.delta l.sum)).prod v)
    = true ↔ _
  rw [Bool.and_eq_true, multiset_prod_eval]
  refine and_congr_right fun _ => ⟨fun h l hl => ?_, fun h f hf => ?_⟩
  · exact (list_sum_eval l v).mp
      (h _ (Multiset.mem_map_of_mem _ hl))
  · obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp hf
    exact (list_sum_eval l v).mpr (h l hl)

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- A token's existence guard is the non-emptiness of its realized world. -/
theorem AggValue.annGuard_iff_realized (a : AggValue T (BoolFunc X))
    (v : X → Bool) :
    annGuard (a.occs.map Prod.snd) v ↔ (a.realized v).Nonempty := by
  unfold annGuard AggValue.realized
  constructor
  · rintro ⟨κ, hκ, hv⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hκ
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ho
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by unfold AggValue.anns; rw [hi]; exact hv⟩⟩
  · rintro ⟨i, hi⟩
    exact ⟨(a.occs.get i).snd,
      List.mem_map.mpr ⟨a.occs.get i, List.get_mem a.occs i, rfl⟩,
      (Finset.mem_filter.mp hi).2⟩

/-! ## Specialized readings under kind conformance -/

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- A regular-kinded value is a left injection. -/
theorem GenValue.eq_inl_of_kindOf_reg {K' : Type} {x : GenValue T K'}
    (h : GenValue.kindOf x = ColKind.reg) : ∃ w, x = Sum.inl w := by
  cases x with
  | inl w => exact ⟨w, rfl⟩
  | inr a => exact absurd h (by simp [GenValue.kindOf])

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- A token-kinded value is a right injection. -/
theorem GenValue.eq_inr_of_kindOf_agg {K' : Type} {x : GenValue T K'}
    (h : GenValue.kindOf x = ColKind.agg) : ∃ a, x = Sum.inr a := by
  cases x with
  | inl w => exact absurd h (by simp [GenValue.kindOf])
  | inr a => exact ⟨a, rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- On a kind-conformant tuple, a term's lifted evaluation is its plain
evaluation on the specialized tuple (regular columns hold regular values,
on which both readings are the identity). -/
theorem TermG.eval_specialize {n : ℕ} {κ : Fin n → ColKind}
    (t : TermG T κ) (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool) :
    t.eval u = t.evalPlain (GenRow.specializeTuple v u) := by
  induction t with
  | const a => rfl
  | cmpAgg k h op c ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | index k h =>
    obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg
      ((hconf k).trans (by rw [h]; rfl))
    show AggValue.collapseSum (u k) = GenRow.specializeTuple v u k
    unfold GenRow.specializeTuple
    rw [hw]
    rfl
  | provIndex k h =>
    obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg
      ((hconf k).trans (by rw [h]; rfl))
    show AggValue.collapseSum (u k) = GenRow.specializeTuple v u k
    unfold GenRow.specializeTuple
    rw [hw]
    rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermG.eval, TermG.evalPlain, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => rw [TermG.eval, TermG.evalPlain, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => rw [TermG.eval, TermG.evalPlain, ih₁, ih₂]

omit [Fintype X] [DecidableEq X] in
/-- On a kind-conformant tuple, an aggregate-atom-free predicate holds
iff its plain reading holds on the specialized tuple. -/
theorem GenPred.holds_iff_specialize {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (hφ : φ.hasAggAtom = false)
    (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool) :
    φ.holds u ↔ φ.holdsPlain (GenRow.specializeTuple v u) := by
  induction φ with
  | cmp op t₁ t₂ =>
    rw [GenPred.holds, GenPred.holdsPlain,
      TermG.eval_specialize t₁ u hconf v, TermG.eval_specialize t₂ u hconf v]
  | aggCmp k h op t => exact absurd hφ (by simp [GenPred.hasAggAtom])
  | and φ ψ ihφ ihψ =>
    rw [GenPred.hasAggAtom, Bool.or_eq_false_iff] at hφ
    rw [GenPred.holds, GenPred.holdsPlain, ihφ hφ.1, ihψ hφ.2]
  | or φ ψ ihφ ihψ =>
    rw [GenPred.hasAggAtom, Bool.or_eq_false_iff] at hφ
    rw [GenPred.holds, GenPred.holdsPlain, ihφ hφ.1, ihψ hφ.2]
  | not φ ih =>
    rw [GenPred.hasAggAtom] at hφ
    rw [GenPred.holds, GenPred.holdsPlain, ih hφ]

/-! ## The σ-aggregate row lemma -/

/-- The annotation lists of the tokens compared by a predicate on a row
(the evaluator's `compared`). -/
def GenPred.selCompared {K' : Type} {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (u : Tuple (GenValue T K') n) :
    Multiset (List K') :=
  φ.comparedCols.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => some (a.occs.map Prod.snd))

/-- The pending factors after a σ with aggregate atoms (the evaluator's
update, definitionally). -/
def GenPred.selPending {K' : Type} [DecidableEq K'] {n : ℕ}
    {κ : Fin n → ColKind} (φ : GenPred T κ)
    (u : Tuple (GenValue T K') n) (p : Multiset (List K')) :
    Multiset (List K') :=
  if φ.entailsExistence false then
    p.filter (fun l => ¬(φ.selCompared u ≠ 0 ∧ ∀ l' ∈ φ.selCompared u, l' = l))
  else p

/-- **Predicate provenance evaluation, under existence guards.** On a
kind-conformant row all of whose compared groups are realized non-empty,
the predicate provenance is true iff the (polarity-adjusted) plain
predicate holds on the specialized tuple. -/
theorem GenPred.predsem_eval_iff {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (neg : Bool)
    (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool)
    (hg : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
      u k = Sum.inr a → (a.realized v).Nonempty) :
    ((φ.predsem neg u) v = true)
      ↔ (if neg = true then ¬ φ.holdsPlain (GenRow.specializeTuple v u)
          else φ.holdsPlain (GenRow.specializeTuple v u)) := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ =>
    simp only [GenPred.predsem]
    rw [chi_eval_iff, GenPred.holdsPlain,
      ← TermG.eval_specialize t₁ u hconf v,
      ← TermG.eval_specialize t₂ u hconf v]
    cases neg with
    | false => simp
    | true => simp [CompOp.negate_eval]
  | aggCmp k h op t =>
    obtain ⟨a, ha⟩ := GenValue.eq_inr_of_kindOf_agg
      ((hconf k).trans (by rw [h]; rfl))
    simp only [GenPred.predsem, ha]
    rw [AggValue.predProv_eval_iff, GenPred.holdsPlain]
    have hne := hg k (Finset.mem_singleton_self k) a ha
    have hspec : GenRow.specializeTuple v u k
        = a.specialize (fun α => α v) := by
      unfold GenRow.specializeTuple
      rw [ha]
      rfl
    rw [hspec, ← TermG.eval_specialize t u hconf v]
    cases neg with
    | false => simp [hne]
    | true => simp [hne, CompOp.negate_eval]
  | and φ ψ ihφ ihψ =>
    have hgφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_left _ hk)
    have hgψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPred.and φ ψ).predsem false u
          = φ.predsem false u * ψ.predsem false u := rfl
      rw [he]
      show (_ && _) = true ↔ _
      rw [Bool.and_eq_true, ihφ false hgφ, ihψ false hgψ,
        GenPred.holdsPlain]
      simp
    | true =>
      have he : (GenPred.and φ ψ).predsem true u
          = φ.predsem true u + ψ.predsem true u := rfl
      rw [he]
      show (_ || _) = true ↔ _
      rw [Bool.or_eq_true, ihφ true hgφ, ihψ true hgψ,
        GenPred.holdsPlain]
      simp
      tauto
  | or φ ψ ihφ ihψ =>
    have hgφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_left _ hk)
    have hgψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPred.or φ ψ).predsem false u
          = φ.predsem false u + ψ.predsem false u := rfl
      rw [he]
      show (_ || _) = true ↔ _
      rw [Bool.or_eq_true, ihφ false hgφ, ihψ false hgψ,
        GenPred.holdsPlain]
      simp
    | true =>
      have he : (GenPred.or φ ψ).predsem true u
          = φ.predsem true u * ψ.predsem true u := rfl
      rw [he]
      show (_ && _) = true ↔ _
      rw [Bool.and_eq_true, ihφ true hgφ, ihψ true hgψ,
        GenPred.holdsPlain]
      simp [not_or]
  | not φ ih =>
    have he : (GenPred.not φ).predsem neg u = φ.predsem (!neg) u := rfl
    rw [he, ih (!neg) hg, GenPred.holdsPlain]
    cases neg <;> simp

/-- **Existence entailment extracts the guard.** When a predicate entails
existence and all its compared tokens carry the annotation list `ℓ₀`, a
true predicate provenance realizes `ℓ₀`. -/
theorem GenPred.entails_guard {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (neg : Bool)
    (u : Tuple (GenValue T (BoolFunc X)) n) (v : X → Bool)
    (ℓ₀ : List (BoolFunc X))
    (huni : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
      u k = Sum.inr a → a.occs.map Prod.snd = ℓ₀)
    (hent : φ.entailsExistence neg = true)
    (hp : (φ.predsem neg u) v = true) : annGuard ℓ₀ v := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ => exact absurd hent (by simp [GenPred.entailsExistence])
  | aggCmp k h op t =>
    cases hu : u k with
    | inl w =>
      simp only [GenPred.predsem, hu] at hp
      exact absurd hp Bool.false_ne_true
    | inr a =>
      simp only [GenPred.predsem, hu] at hp
      have hne := (AggValue.predProv_eval_iff a _ _ v).mp hp |>.1
      rw [← huni k (Finset.mem_singleton_self k) a hu]
      exact (AggValue.annGuard_iff_realized a v).mpr hne
  | and φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPred.and φ ψ).predsem false u
          = φ.predsem false u * ψ.predsem false u := rfl
      rw [he] at hp
      have hp' : (φ.predsem false u v && ψ.predsem false u v) = true := hp
      rw [Bool.and_eq_true] at hp'
      have hent' : (φ.entailsExistence false || ψ.entailsExistence false)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rcases hent' with h | h
      exacts [ihφ false huφ h hp'.1, ihψ false huψ h hp'.2]
    | true =>
      have he : (GenPred.and φ ψ).predsem true u
          = φ.predsem true u + ψ.predsem true u := rfl
      rw [he] at hp
      have hp' : (φ.predsem true u v || ψ.predsem true u v) = true := hp
      have hent' : (φ.entailsExistence true && ψ.entailsExistence true)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [Bool.or_eq_true] at hp'
      rcases hp' with h | h
      exacts [ihφ true huφ hent'.1 h, ihψ true huψ hent'.2 h]
  | or φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPred.or φ ψ).predsem false u
          = φ.predsem false u + ψ.predsem false u := rfl
      rw [he] at hp
      have hp' : (φ.predsem false u v || ψ.predsem false u v) = true := hp
      have hent' : (φ.entailsExistence false && ψ.entailsExistence false)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [Bool.or_eq_true] at hp'
      rcases hp' with h | h
      exacts [ihφ false huφ hent'.1 h, ihψ false huψ hent'.2 h]
    | true =>
      have he : (GenPred.or φ ψ).predsem true u
          = φ.predsem true u * ψ.predsem true u := rfl
      rw [he] at hp
      have hp' : (φ.predsem true u v && ψ.predsem true u v) = true := hp
      rw [Bool.and_eq_true] at hp'
      have hent' : (φ.entailsExistence true || ψ.entailsExistence true)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rcases hent' with h | h
      exacts [ihφ true huφ h hp'.1, ihψ true huψ h hp'.2]
  | not φ ih =>
    have he : (GenPred.not φ).predsem neg u = φ.predsem (!neg) u := rfl
    rw [he] at hp
    exact ih (!neg) huni hent hp

/-! ## Finalize algebra (any m-semiring) -/

/-- Cashing pending factors into the concrete part preserves the
finalized annotation (the projection case of the evaluator). -/
theorem GenAnn.finalize_cash {K' : Type} [CommSemiringWithMonus K']
    [DecidableEq K'] (b : K') (p kept : Multiset (List K'))
    (hle : kept ≤ p) :
    (GenAnn.mk
        (b * ((p - kept).map (fun l => SemiringWithMonus.delta l.sum)).prod)
        kept).finalize
      = (GenAnn.mk b p).finalize := by
  unfold GenAnn.finalize
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [Multiset.map_add, Multiset.prod_add, mul_assoc]

/-- The finalized annotation of a product row is the product of the
finalized annotations. -/
theorem GenAnn.finalize_mul {K' : Type} [CommSemiringWithMonus K']
    (a₁ a₂ : GenAnn K') :
    (GenAnn.mk (a₁.base * a₂.base) (a₁.pending + a₂.pending)).finalize
      = a₁.finalize * a₂.finalize := by
  unfold GenAnn.finalize
  rw [Multiset.map_add, Multiset.prod_add]
  exact mul_mul_mul_comm _ _ _ _

/-! ## The row-level σ lemmas -/

/-- A σ with aggregate atoms only strengthens the annotation: the
finalized updated annotation implies the finalized original one (the
superseded factors are recovered from the predicate provenance through
existence entailment). -/
theorem GenPred.sel_finalize_old {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (u : Tuple (GenValue T (BoolFunc X)) n)
    (b : BoolFunc X) (p : Multiset (List (BoolFunc X))) (v : X → Bool)
    (h : (GenAnn.mk (b * φ.predsem false u) (φ.selPending u p)).finalize v
      = true) :
    (GenAnn.mk b p).finalize v = true := by
  rw [GenAnn.finalize_eval_iff] at h ⊢
  obtain ⟨hbp, hupd⟩ := h
  have hbp' : (b v && (φ.predsem false u) v) = true := hbp
  rw [Bool.and_eq_true] at hbp'
  refine ⟨hbp'.1, fun l hl => ?_⟩
  unfold GenPred.selPending at hupd
  by_cases hE : φ.entailsExistence false = true
  · rw [if_pos hE] at hupd
    by_cases hcond : (φ.selCompared u ≠ 0 ∧ ∀ l' ∈ φ.selCompared u, l' = l)
    · refine GenPred.entails_guard φ false u v l ?_ hE hbp'.2
      intro k hk a ha
      refine hcond.2 _ ((Multiset.mem_filterMap _ _).mpr ⟨k, Finset.mem_val.mpr hk, ?_⟩)
      rw [ha]
    · exact hupd l (Multiset.mem_filter.mpr ⟨hl, hcond⟩)
  · rw [if_neg hE] at hupd
    exact hupd l hl

/-- **The σ-aggregate row lemma.** On a kind-conformant, guarded row, the
updated annotation is realized iff the original annotation is realized
and the plain predicate holds on the specialized tuple. -/
theorem GenPred.sel_finalize_eval_iff {n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPred T κ) (u : Tuple (GenValue T (BoolFunc X)) n)
    (b : BoolFunc X) (p : Multiset (List (BoolFunc X))) (v : X → Bool)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base)
    (hguard : (GenAnn.mk b p).finalize v = true →
      ∀ (k : Fin n) (a : AggValue T (BoolFunc X)), u k = Sum.inr a →
        (a.realized v).Nonempty) :
    ((GenAnn.mk (b * φ.predsem false u) (φ.selPending u p)).finalize v
        = true)
      ↔ (GenAnn.mk b p).finalize v = true
        ∧ φ.holdsPlain (GenRow.specializeTuple v u) := by
  constructor
  · intro h
    have hold := GenPred.sel_finalize_old φ u b p v h
    have hbp : (b v && (φ.predsem false u) v) = true :=
      ((GenAnn.finalize_eval_iff _ v).mp h).1
    rw [Bool.and_eq_true] at hbp
    refine ⟨hold, ?_⟩
    have hps := (GenPred.predsem_eval_iff φ false u hconf v
      (fun k _ a ha => hguard hold k a ha)).mp hbp.2
    simpa using hps
  · rintro ⟨hold, hh⟩
    have hgs := hguard hold
    rw [GenAnn.finalize_eval_iff] at hold ⊢
    obtain ⟨hb, hG⟩ := hold
    have hps : (φ.predsem false u) v = true :=
      (GenPred.predsem_eval_iff φ false u hconf v
        (fun k _ a ha => hgs k a ha)).mpr (by simpa using hh)
    refine ⟨?_, fun l hl => ?_⟩
    · show (b v && _) = true
      rw [Bool.and_eq_true]
      exact ⟨hb, hps⟩
    · unfold GenPred.selPending at hl
      by_cases hE : φ.entailsExistence false = true
      · rw [if_pos hE] at hl
        exact hG l (Multiset.mem_of_mem_filter hl)
      · rw [if_neg hE] at hl
        exact hG l hl

/-! ## The guardedness invariant -/

variable [HasAltLinearOrder (BoolFunc X)]

/-- **Guardedness of the general evaluator**: on any row it produces,
whenever the finalized annotation is realized, every token's group is
realized non-empty – the group-existence guard of each token is carried
either by a pending factor or by a predicate provenance in the concrete
part. -/
theorem QueryGen.evaluateGen_guarded :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (d : AnnotatedDatabase T (BoolFunc X)) (r : GenRow T (BoolFunc X) n),
      r ∈ q.evaluateGen d → ∀ v : X → Bool, r.snd.finalize v = true →
      ∀ (k : Fin n) (a : AggValue T (BoolFunc X)), r.fst k = Sum.inr a →
        (a.realized v).Nonempty := by
  intro n κ q
  induction q with
  | Rel n s =>
    intro d r hr v _ k a ha
    simp only [QueryGen.evaluateGen] at hr
    cases hf : d.find n s with
    | none => rw [hf] at hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      rw [hf] at hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      exact absurd ha (by simp [GenRow.ofAnnotated])
  | Proj ps q ih =>
    intro d r hr v hfin j a ha
    simp only [QueryGen.evaluateGen] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
    have hfin₀ : r₀.snd.finalize v = true := by
      rw [← GenAnn.finalize_cash r₀.snd.base r₀.snd.pending
        (r₀.snd.pending ∩ tokenLists (fun j => (ps j).eval r₀.fst))
        Multiset.inter_le_left]
      exact hfin
    have ha' : (ps j).eval r₀.fst = Sum.inr a := ha
    cases hp : ps j with
    | term t =>
      rw [hp] at ha'
      exact absurd ha' (by simp [ProjCol.eval])
    | provTerm t =>
      rw [hp] at ha'
      exact absurd ha' (by simp [ProjCol.eval])
    | token k hk =>
      rw [hp] at ha'
      exact ih d r₀ hr₀ v hfin₀ k a ha'
  | Sel φ q ih =>
    intro d r hr v hfin k a ha
    simp only [QueryGen.evaluateGen] at hr
    by_cases hφ : φ.hasAggAtom
    · rw [if_pos hφ] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      have hold := GenPred.sel_finalize_old φ r₀.fst r₀.snd.base
        r₀.snd.pending v hfin
      exact ih d r₀ hr₀ v hold k a ha
    · rw [if_neg hφ] at hr
      exact ih d r (Multiset.mem_of_mem_filter hr) v hfin k a ha
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d r hr v hfin k a ha
    simp only [QueryGen.evaluateGen] at hr
    obtain ⟨xy, hxy, rfl⟩ := Multiset.mem_map.mp hr
    have hx := Multiset.mem_product.mp hxy
    have hfin' : (xy.fst.snd.finalize v && xy.snd.snd.finalize v) = true := by
      have := GenAnn.finalize_mul xy.fst.snd xy.snd.snd
      rw [show (GenAnn.mk (xy.fst.snd.base * xy.snd.snd.base)
          (xy.fst.snd.pending + xy.snd.snd.pending)).finalize
          = xy.fst.snd.finalize * xy.snd.snd.finalize from this] at hfin
      exact hfin
    rw [Bool.and_eq_true] at hfin'
    revert ha
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro ha
    · exact ih₁ d xy.fst hx.left v hfin'.1 i a
        ((Fin.append_left xy.fst.fst xy.snd.fst i).symm.trans ha)
    · exact ih₂ d xy.snd hx.right v hfin'.2 j a
        ((Fin.append_right xy.fst.fst xy.snd.fst j).symm.trans ha)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d r hr v hfin k a ha
    simp only [QueryGen.evaluateGen] at hr
    rcases Multiset.mem_add.mp hr with h | h
    exacts [ih₁ d r h v hfin k a ha, ih₂ d r h v hfin k a ha]
  | Dedup q ih =>
    intro d r hr v _ k a ha
    simp only [QueryGen.evaluateGen] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d r hr v _ k a ha
    simp only [QueryGen.evaluateGen] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Gamma is ts fs q ih =>
    intro d r hr v hfin k a ha
    simp only [QueryGen.evaluateGen] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    have hG : annGuard ((Having.havingGroup is
        ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst).map Prod.snd) v :=
      ((GenAnn.finalize_eval_iff _ v).mp hfin).2 _ (Multiset.mem_singleton_self _)
    revert ha
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro ha
    · have ha' : (Sum.inl (kv.fst i) : GenValue T (BoolFunc X)) = Sum.inr a :=
        (Fin.append_left
          (fun k => (Sum.inl (kv.fst k) : GenValue T (BoolFunc X)))
          (fun j' => Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst))) i).symm.trans
          ha
      exact absurd ha' (by simp)
    · have haj : (Sum.inr (AggValue.ofGroup (fs j) (ts j)
          (Having.havingGroup is
            ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst))
          : GenValue T (BoolFunc X)) = Sum.inr a :=
        (Fin.append_right
          (fun k => (Sum.inl (kv.fst k) : GenValue T (BoolFunc X)))
          (fun j' => Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst))) j).symm.trans
          ha
      rw [← Sum.inr.inj haj]
      refine (AggValue.annGuard_iff_realized _ v).mp ?_
      rw [AggValue.annList_ofGroup]
      exact hG
  | @ProvSum m n₁ κ' is his t q ih =>
    intro d r hr v _ k a ha
    have hconf := QueryGen.evaluateGen_conform _ d r hr k
    rw [ha] at hconf
    revert hconf
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro hconf
    · rw [Fin.append_left, ColKind.base_eq_reg_of_ne_agg (his i)] at hconf
      exact ColKind.noConfusion hconf
    · rw [Fin.append_right] at hconf
      exact ColKind.noConfusion hconf
  | @GammaTok m n₁ n₂ κ' is his ts fs a' q ih =>
    intro d r hr v hfin k a ha
    have hconf := QueryGen.evaluateGen_conform _ d r hr k
    rw [ha] at hconf
    simp only [QueryGen.evaluateGen] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    have hG : annGuard ((Having.havingGroup is
        ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst).map Prod.snd) v :=
      ((GenAnn.finalize_eval_iff _ v).mp hfin).2 _
        (Multiset.mem_singleton_self _)
    revert hconf ha
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro hconf ha
    · revert hconf ha
      refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i <;> intro hconf ha
      · rw [Fin.append_left, Fin.append_left,
          ColKind.base_eq_reg_of_ne_agg (his i')] at hconf
        exact ColKind.noConfusion hconf
      · simp only [Fin.append_left, Fin.append_right] at ha
        rw [← Sum.inr.inj ha]
        refine (AggValue.annGuard_iff_realized _ v).mp ?_
        rw [AggValue.annList_ofGroup]
        exact hG
    · rw [Fin.append_right] at hconf
      exact ColKind.noConfusion hconf
  | Retag h q ih =>
    intro d r hr v hfin k a ha
    exact ih d r hr v hfin k a ha

/-! ## Realized-world plumbing -/

private lemma filter_map_comm {α β : Type} (f : α → β) (p : β → Prop)
    [DecidablePred p] (s : Multiset α) :
    (s.map f).filter p = (s.filter (fun a => p (f a))).map f := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    by_cases hp : p (f a)
    · rw [Multiset.map_cons, Multiset.filter_cons_of_pos _ hp,
        Multiset.filter_cons_of_pos (p := fun a => p (f a)) _ hp,
        Multiset.map_cons, ih]
    · rw [Multiset.map_cons, Multiset.filter_cons_of_neg _ hp,
        Multiset.filter_cons_of_neg (p := fun a => p (f a)) _ hp, ih]

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
private lemma genRandomWorld_add {n : ℕ}
    (R₁ R₂ : Multiset (GenRow T (BoolFunc X) n)) (v : X → Bool) :
    genRandomWorld v (R₁ + R₂)
      = genRandomWorld v R₁ + genRandomWorld v R₂ := by
  unfold genRandomWorld
  rw [Multiset.filter_add, Multiset.map_add]

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- On embedded annotated tuples, the general realized world is the
plain one. -/
private lemma genRandomWorld_ofAnnotated {n : ℕ}
    (R : AnnotatedRelation T (BoolFunc X) n) (v : X → Bool) :
    genRandomWorld v (R.map GenRow.ofAnnotated) = randomWorld v R := by
  unfold genRandomWorld randomWorld
  rw [filter_map_comm, Multiset.map_map]
  have hpred : (R.filter
        (fun p : AnnotatedTuple T (BoolFunc X) n =>
          (GenRow.ofAnnotated p).snd.finalize v = true))
      = R.filter
        (fun p : AnnotatedTuple T (BoolFunc X) n => p.snd v = true) := by
    apply Multiset.filter_congr
    intro p _
    show (⟨p.snd, 0⟩ : GenAnn (BoolFunc X)).finalize v = true ↔ p.snd v = true
    rw [GenAnn.finalize_of_pending_zero]
  rw [hpred]
  apply Multiset.map_congr rfl
  intro p _
  rfl

omit [Fintype X] [DecidableEq X] in
/-- On an all-regular subquery, the plain and general realized worlds
coincide (every column is a regular value, on which the specialized and
plain readings agree). -/
private lemma genRandomWorld_allReg {n : ℕ}
    (q : QueryGen T n (ColKind.allReg n))
    (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool) :
    randomWorld v ((q.evaluateGen d).map GenRow.toAnnotated)
      = genRandomWorld v (q.evaluateGen d) := by
  unfold randomWorld genRandomWorld
  rw [filter_map_comm, Multiset.map_map]
  refine Multiset.map_congr
    (Multiset.filter_congr fun r _ => Iff.rfl) fun r hr => ?_
  have hconf := QueryGen.evaluateGen_conform q d r
    (Multiset.mem_of_mem_filter hr)
  show GenRow.plainTuple r.fst = GenRow.specializeTuple v r.fst
  funext k
  obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg (hconf k)
  unfold GenRow.plainTuple GenRow.specializeTuple
  rw [hw]
  rfl

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
/-- A projection column specializes to its plain reading on the
specialized tuple. -/
private lemma ProjCol.specializeAt_eval {n : ℕ} {κ : Fin n → ColKind}
    (pc : ProjCol T κ) (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool) :
    GenValue.specializeAt v (pc.eval u)
      = pc.evalPlain (GenRow.specializeTuple v u) := by
  cases pc with
  | term t =>
    show GenValue.specializeAt v (Sum.inl (t.eval u)) = _
    exact TermG.eval_specialize t u hconf v
  | token k hk => rfl
  | provTerm t =>
    show GenValue.specializeAt v (Sum.inl (t.eval u)) = _
    exact TermG.eval_specialize t u hconf v

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- Specialization distributes over appending regular and token parts. -/
private lemma specializeTuple_append {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggValue T (BoolFunc X)) (v : X → Bool) :
    GenRow.specializeTuple v
        (Fin.append (fun k => (Sum.inl (g k) : GenValue T (BoolFunc X)))
          (fun j => Sum.inr (h j)))
      = Fin.append g (fun j => (h j).specialize (fun α => α v)) := by
  funext k
  unfold GenRow.specializeTuple
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left, Fin.append_left]; rfl
  · rw [Fin.append_right, Fin.append_right]; rfl

private lemma product_filter {α β : Type} (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] (s : Multiset α) (t : Multiset β) :
    (Multiset.product s t).filter (fun x => p x.fst ∧ q x.snd)
      = Multiset.product (s.filter p) (t.filter q) := by
  show (s ×ˢ t).filter _ = (s.filter p) ×ˢ (t.filter q)
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.zero_product, Multiset.filter_zero,
      Multiset.filter_zero, Multiset.zero_product]
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.filter_add, ih, filter_map_comm]
    by_cases hp : p a
    · rw [Multiset.filter_cons_of_pos _ hp, Multiset.cons_product]
      congr 1
      exact congrArg _ (Multiset.filter_congr fun b _ => by simp [hp])
    · rw [Multiset.filter_cons_of_neg _ hp,
        show t.filter (fun b => p a ∧ q b) = 0 from
          Multiset.filter_eq_nil.mpr (fun b _ hb => hp hb.1),
        Multiset.map_zero, zero_add]

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
/-- The realized world of a `groupByKey`-deduplicated relation is the
deduplicated realized world (a grouped annotation is realized iff some
contributing annotation is). -/
private lemma randomWorld_groupByKey {n : ℕ}
    (r : AnnotatedRelation T (BoolFunc X) n) (v : X → Bool) :
    randomWorld v (Multiset.ofList (groupByKey r).val)
      = (randomWorld v r).dedup := by
  have hgbk_nodup : (Multiset.ofList (groupByKey r).val :
      Multiset (Tuple T n × BoolFunc X)).Nodup := by
    rw [Multiset.coe_nodup]
    exact KeyValueList.nodup _ (groupByKey r).property
  have hLNodup : (randomWorld v (Multiset.ofList (groupByKey r).val)).Nodup := by
    show (Multiset.map Prod.fst _).Nodup
    apply Multiset.Nodup.map_on
    · intro p hp q hq hpq
      rw [Multiset.mem_filter] at hp hq
      exact Prod.ext hpq
        (KeyValueList.functional _ (groupByKey r).property p
          (Multiset.mem_coe.mp hp.1) q (Multiset.mem_coe.mp hq.1) hpq)
    · exact Multiset.Nodup.filter _ hgbk_nodup
  rw [Multiset.Nodup.ext hLNodup (Multiset.nodup_dedup _)]
  intro t
  constructor
  · intro ht
    rw [Multiset.mem_dedup]
    unfold randomWorld at ht ⊢
    rw [Multiset.mem_map] at ht
    obtain ⟨p, hp, hpfst⟩ := ht
    rw [Multiset.mem_filter] at hp
    obtain ⟨hp_in, hp_snd⟩ := hp
    have hp_val : p.snd = (Multiset.map Prod.snd
          (Multiset.filter (fun q : AnnotatedTuple T (BoolFunc X) n =>
            q.fst = p.fst) r)).sum :=
      groupByKey_value r p.fst p.snd (Multiset.mem_coe.mp hp_in)
    rw [hp_val, multiset_sum_eval] at hp_snd
    obtain ⟨α, hα_in, hα_true⟩ := hp_snd
    obtain ⟨α_pair, hα_pair_in, rfl⟩ := Multiset.mem_map.mp hα_in
    rw [Multiset.mem_filter] at hα_pair_in
    rw [Multiset.mem_map]
    exact ⟨α_pair, Multiset.mem_filter.mpr ⟨hα_pair_in.1, hα_true⟩,
      hα_pair_in.2.trans hpfst⟩
  · intro ht
    rw [Multiset.mem_dedup] at ht
    unfold randomWorld at ht ⊢
    rw [Multiset.mem_map] at ht
    obtain ⟨α_pair, hα_in, hα_fst⟩ := ht
    rw [Multiset.mem_filter] at hα_in
    obtain ⟨hα_r, hα_v⟩ := hα_in
    have hmem_map : t ∈ Multiset.map Prod.fst r :=
      Multiset.mem_map.mpr ⟨α_pair, hα_r, hα_fst⟩
    obtain ⟨w, hw_in⟩ := (groupByKey_key_iff r t).mpr hmem_map
    have hw_v_true : w v = true := by
      rw [groupByKey_value r t w hw_in, multiset_sum_eval]
      exact ⟨α_pair.snd,
        Multiset.mem_map.mpr ⟨α_pair,
          Multiset.mem_filter.mpr ⟨hα_r, hα_fst⟩, rfl⟩, hα_v⟩
    exact Multiset.mem_map.mpr ⟨(t, w),
      Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr hw_in, hw_v_true⟩, rfl⟩

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
/-- The realized world of the monus-based difference is the all-or-nothing
difference of the realized worlds (ported from the `Diff` case of
`randomWorld_evaluateAnnotated`). -/
private lemma randomWorld_monus {n : ℕ}
    (r₁ r₂ : AnnotatedRelation T (BoolFunc X) n) (v : X → Bool) :
    randomWorld v (r₁.map (fun (u, α) =>
        (⟨u, α - ((((groupByKey r₂).val.find? (·.1 = u)).map
          Prod.snd).getD 0)⟩ : AnnotatedTuple T (BoolFunc X) n)))
      = (randomWorld v r₁).filter (fun t => t ∉ randomWorld v r₂) := by
  have hrw_cons : ∀ (a : Tuple T n × BoolFunc X)
      (t : Multiset (Tuple T n × BoolFunc X)),
      Multiset.map Prod.fst
          (Multiset.filter
            (fun p : Tuple T n × BoolFunc X => p.snd v = true) (a ::ₘ t))
        = if a.snd v = true then
            a.fst ::ₘ Multiset.map Prod.fst
                (Multiset.filter
                  (fun p : Tuple T n × BoolFunc X => p.snd v = true) t)
          else Multiset.map Prod.fst
                (Multiset.filter
                  (fun p : Tuple T n × BoolFunc X => p.snd v = true) t) := by
    intro a t
    by_cases ha : a.snd v = true
    · rw [Multiset.filter_cons_of_pos
          (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) _ ha,
        Multiset.map_cons]
      simp [ha]
    · rw [Multiset.filter_cons_of_neg
          (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) _ ha]
      simp [ha]
  let r₁' : Multiset (Tuple T n × BoolFunc X) := r₁
  show Multiset.map Prod.fst
        (Multiset.filter
          (fun p : Tuple T n × BoolFunc X => p.snd v = true)
          (r₁'.map (fun p : Tuple T n × BoolFunc X =>
            (p.fst, p.snd -
              (((groupByKey r₂).val.find? (fun q => q.1 = p.fst)).map
                Prod.snd).getD 0))))
      = Multiset.filter (fun t => t ∉ randomWorld v r₂)
          (Multiset.map Prod.fst
            (Multiset.filter
              (fun p : Tuple T n × BoolFunc X => p.snd v = true) r₁'))
  induction r₁' using Multiset.induction_on with
  | empty => rfl
  | cons p s ih =>
    rw [Multiset.map_cons]
    set β : BoolFunc X :=
        ((List.find? (fun q : Tuple T n × BoolFunc X => decide (q.1 = p.fst))
          (groupByKey r₂).val).map Prod.snd).getD 0 with hβ_def
    have hβ_iff : β v = false ↔ p.fst ∉ randomWorld v r₂ :=
      diff_annotation_eq_false_iff v r₂ p.fst
    rw [hrw_cons (p.fst, p.snd - β)]
    conv_rhs => rw [hrw_cons p s]
    by_cases hpv : p.snd v = true
    · by_cases hbv : β v = false
      · have hp_notin : p.fst ∉ randomWorld v r₂ := hβ_iff.mp hbv
        have hcond_lhs : (p.snd - β) v = true := by
          rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv, hbv]
          rfl
        rw [if_pos hcond_lhs, if_pos hpv, ih]
        rw [Multiset.filter_cons_of_pos
            (p := fun t : Tuple T n => t ∉ randomWorld v r₂) _ hp_notin]
      · have hbv_true : β v = true := by
          cases h : β v
          · exact absurd h hbv
          · rfl
        have hp_in : ¬ p.fst ∉ randomWorld v r₂ := by
          intro h
          exact absurd (hβ_iff.mpr h) hbv
        have hcond_lhs : ¬ (p.snd - β) v = true := by
          rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv, hbv_true]
          simp
        rw [if_neg hcond_lhs, if_pos hpv, ih]
        rw [Multiset.filter_cons_of_neg
            (p := fun t : Tuple T n => t ∉ randomWorld v r₂) _ hp_in]
    · have hpv_false : p.snd v = false := by
        cases h : p.snd v
        · rfl
        · exact absurd h hpv
      have hcond_lhs : ¬ (p.snd - β) v = true := by
        rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv_false]
        simp
      rw [if_neg hcond_lhs, if_neg hpv]
      exact ih

/-! ## The `Gamma` case helpers -/

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
private lemma annGuard_map_snd {m : ℕ}
    (U : List (AnnotatedTuple T (BoolFunc X) m)) (v : X → Bool) :
    annGuard (U.map Prod.snd) v ↔ ∃ p ∈ U, p.snd v = true := by
  unfold annGuard
  constructor
  · rintro ⟨κ, hκ, h⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hκ
    exact ⟨p, hp, h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p.snd, List.mem_map.mpr ⟨p, hp, rfl⟩, h⟩

/-- The specialized group token is the plain aggregate of the group in
the realized world. -/
private lemma specialize_ofGroup {m n₁ : ℕ}
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T (BoolFunc X) m)
    (g : Tuple T n₁) (f : SeqAggFunc T) (t : Term T m) (v : X → Bool) :
    (AggValue.ofGroup f t (Having.havingGroup is r g)).specialize
        (fun α => α v)
      = f ((Relation.groupSeq is (randomWorld v r) g).map t.eval) := by
  unfold AggValue.specialize AggValue.ofGroup
  rw [groupSeq_randomWorld, seqOf_realizedWorld, List.filter_map,
    List.map_map, List.map_map]
  rfl

/-! ## The random-world commutation -/

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- Generic specialization distributes over `Fin.append`. -/
private lemma specializeTuple_append' {n₁ n₂ : ℕ}
    (u₁ : Tuple (GenValue T (BoolFunc X)) n₁)
    (u₂ : Tuple (GenValue T (BoolFunc X)) n₂) (v : X → Bool) :
    GenRow.specializeTuple v (Fin.append u₁ u₂)
      = Fin.append (GenRow.specializeTuple v u₁)
          (GenRow.specializeTuple v u₂) := by
  funext k
  unfold GenRow.specializeTuple
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- **Random-world commutation for the general evaluator** (over `𝔹[X]`):
specializing the realized rows of the general annotated evaluation is the
plain evaluation of the realized world. The σ-aggregate case is the row
lemma `GenPred.sel_finalize_eval_iff` under the conformance and
guardedness invariants; the `Gamma` case rests on
`groupSeq_randomWorld`. -/
theorem QueryGen.genRandomWorld_evaluateGen :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (_hq : q.noProvSum)
      (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool),
    genRandomWorld v (q.evaluateGen d)
      = q.evaluatePlain (d.randomWorld v) := by
  intro n κ q
  induction q with
  | Rel n s =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    rw [AnnotatedDatabase.find_randomWorld]
    cases hf : d.find n s with
    | none => rfl
    | some rn => exact genRandomWorld_ofAnnotated rn v
  | Proj ps q ih =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map]
    rw [Multiset.filter_congr (fun r (_ : r ∈ q.evaluateGen d) =>
      Iff.of_eq (congrArg (fun α : BoolFunc X => α v = true)
        (GenAnn.finalize_cash r.snd.base r.snd.pending
          (r.snd.pending ∩ tokenLists (fun j => (ps j).eval r.fst))
          Multiset.inter_le_left)))]
    rw [Multiset.map_congr rfl (fun r hr => ?_), ← Multiset.map_map, ← ih hq d v]
    · rfl
    · -- pointwise: the specialized projected tuple is the plain projection
      -- of the specialized tuple
      have hconf := QueryGen.evaluateGen_conform q d r
        (Multiset.mem_of_mem_filter hr)
      show GenRow.specializeTuple v (fun j => (ps j).eval r.fst)
        = fun j => (ps j).evalPlain (GenRow.specializeTuple v r.fst)
      funext j
      exact ProjCol.specializeAt_eval (ps j) r.fst hconf v
  | Sel φ q ih =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    by_cases hφ : φ.hasAggAtom
    · rw [if_pos hφ]
      unfold genRandomWorld
      rw [filter_map_comm, Multiset.map_map]
      refine Eq.trans (congrArg (Multiset.map _)
        (Multiset.filter_congr
          (q := fun r : GenRow T (BoolFunc X) _ =>
            r.snd.finalize v = true
              ∧ φ.holdsPlain (GenRow.specializeTuple v r.fst))
          fun r hr => ?_)) ?_
      · exact GenPred.sel_finalize_eval_iff φ r.fst r.snd.base
          r.snd.pending v (QueryGen.evaluateGen_conform q d r hr)
          (fun hfin => QueryGen.evaluateGen_guarded q d r hr v hfin)
      · rw [← ih hq d v]
        unfold genRandomWorld
        rw [filter_map_comm, Multiset.filter_filter]
        exact Multiset.map_congr
          (Multiset.filter_congr fun r _ => and_comm) (fun r _ => rfl)
    · rw [if_neg hφ]
      unfold genRandomWorld
      rw [Multiset.filter_filter]
      refine Eq.trans (congrArg (Multiset.map _)
        (Multiset.filter_congr
          (q := fun r : GenRow T (BoolFunc X) _ =>
            r.snd.finalize v = true
              ∧ φ.holdsPlain (GenRow.specializeTuple v r.fst))
          fun r hr => ?_)) ?_
      · exact and_congr_right fun _ => GenPred.holds_iff_specialize φ
          (by simpa using hφ) r.fst
          (QueryGen.evaluateGen_conform q d r hr) v
      · rw [← ih hq d v]
        unfold genRandomWorld
        rw [filter_map_comm, Multiset.filter_filter]
        exact Multiset.map_congr
          (Multiset.filter_congr fun r _ => and_comm) (fun r _ => rfl)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map]
    refine Eq.trans (congrArg (Multiset.map _)
      (Multiset.filter_congr
        (q := fun xy : GenRow T (BoolFunc X) _ × GenRow T (BoolFunc X) _ =>
          xy.fst.snd.finalize v = true ∧ xy.snd.snd.finalize v = true)
        fun xy _ => ?_)) ?_
    · exact Iff.trans
        (Iff.of_eq (congrArg (fun α : BoolFunc X => α v = true)
          (GenAnn.finalize_mul xy.fst.snd xy.snd.snd)))
        (Iff.of_eq (Bool.and_eq_true _ _))
    · rw [product_filter
        (fun r : GenRow T (BoolFunc X) _ => r.snd.finalize v = true)
        (fun r : GenRow T (BoolFunc X) _ => r.snd.finalize v = true)
        (q₁.evaluateGen d) (q₂.evaluateGen d), ← ih₁ hq.1 d v, ← ih₂ hq.2 d v]
      show _ = Multiset.map
        (fun uv : Tuple T _ × Tuple T _ => Fin.append uv.fst uv.snd)
        (Multiset.product (genRandomWorld v (q₁.evaluateGen d))
          (genRandomWorld v (q₂.evaluateGen d)))
      unfold genRandomWorld
      rw [product_map_map, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro xy _
      exact specializeTuple_append' xy.fst.fst xy.snd.fst v
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    rw [genRandomWorld_add, ih₁ hq.1 d v, ih₂ hq.2 d v]
  | Dedup q ih =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    rw [genRandomWorld_ofAnnotated, randomWorld_groupByKey,
      genRandomWorld_allReg, ih hq d v]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    refine Eq.trans (genRandomWorld_ofAnnotated _ v)
      (Eq.trans (randomWorld_monus
        ((q₁.evaluateGen d).map GenRow.toAnnotated)
        ((q₂.evaluateGen d).map GenRow.toAnnotated) v) ?_)
    rw [genRandomWorld_allReg, genRandomWorld_allReg, ih₁ hq.1 d v, ih₂ hq.2 d v]
  | @Gamma m n₁ n₂ is ts fs q ih =>
    intro hq d v
    simp only [QueryGen.evaluateGen, QueryGen.evaluatePlain]
    rw [← ih hq d v, ← genRandomWorld_allReg q d v]
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map]
    rw [Multiset.filter_congr (fun kv (_ : kv ∈ Multiset.ofList
        (groupByKey (((q.evaluateGen d).map GenRow.toAnnotated).map (fun p =>
          ((fun k => p.fst (is k), p.snd)
            : AnnotatedTuple T (BoolFunc X) n₁)))).val) =>
      show (⟨1, {(Having.havingGroup is
            ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst).map Prod.snd}⟩
          : GenAnn (BoolFunc X)).finalize v = true
        ↔ annGuard ((Having.havingGroup is
            ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst).map
              Prod.snd) v
        from Iff.trans (GenAnn.finalize_eval_iff
            ⟨1, {(Having.havingGroup is
              ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst).map
                Prod.snd}⟩ v)
          ⟨fun h => h.2 _ (Multiset.mem_singleton_self _),
           fun h => ⟨rfl, fun l hl => (Multiset.mem_singleton.mp hl) ▸ h⟩⟩)]
    -- key multisets: the realized keys are the realized world's keys
    have hkeys : (((randomWorld v
          ((q.evaluateGen d).map GenRow.toAnnotated)).map
            (fun u => (fun k => u (is k) : Tuple T n₁))).dedup : Multiset _)
        = Multiset.map Prod.fst
          (Multiset.filter (fun kv : AnnotatedTuple T (BoolFunc X) n₁ =>
            annGuard ((Having.havingGroup is
              ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst).map
                Prod.snd) v)
            (Multiset.ofList (groupByKey
              (((q.evaluateGen d).map GenRow.toAnnotated).map (fun p =>
                ((fun k => p.fst (is k), p.snd)
                  : AnnotatedTuple T (BoolFunc X) n₁)))).val)) := by
      have hRnodup : (Multiset.map Prod.fst
          (Multiset.filter (fun kv : AnnotatedTuple T (BoolFunc X) n₁ =>
            annGuard ((Having.havingGroup is
              ((q.evaluateGen d).map GenRow.toAnnotated) kv.fst).map
                Prod.snd) v)
            (Multiset.ofList (groupByKey
              (((q.evaluateGen d).map GenRow.toAnnotated).map (fun p =>
                ((fun k => p.fst (is k), p.snd)
                  : AnnotatedTuple T (BoolFunc X) n₁)))).val))).Nodup := by
        refine Multiset.nodup_of_le
          (Multiset.map_le_map (Multiset.filter_le _ _)) ?_
        rw [map_fst_groupByKey]
        exact Multiset.nodup_dedup _
      rw [Multiset.Nodup.ext (Multiset.nodup_dedup _) hRnodup]
      intro g
      rw [Multiset.mem_dedup, randomWorld_key_mem_iff,
        realizedWorld_nonempty_iff, ← annGuard_map_snd]
      constructor
      · intro hg
        have hkey : g ∈ Multiset.map Prod.fst
            (((q.evaluateGen d).map GenRow.toAnnotated).map (fun p =>
              ((fun k => p.fst (is k), p.snd)
                : AnnotatedTuple T (BoolFunc X) n₁))) := by
          obtain ⟨κ₀, hκ₀, hκv⟩ := hg
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hκ₀
          have hpU := hp
          rw [← Multiset.mem_coe, Having.havingGroup_coe] at hpU
          obtain ⟨hpR, hpk⟩ := Multiset.mem_filter.mp hpU
          exact Multiset.mem_map.mpr
            ⟨((fun k => p.fst (is k), p.snd)
                : AnnotatedTuple T (BoolFunc X) n₁),
             Multiset.mem_map.mpr ⟨p, hpR, rfl⟩, funext hpk⟩
        obtain ⟨w, hw⟩ := (groupByKey_key_iff _ g).mpr hkey
        exact Multiset.mem_map.mpr ⟨(g, w),
          Multiset.mem_filter.mpr ⟨Multiset.mem_coe.mpr hw, hg⟩, rfl⟩
      · intro hg
        obtain ⟨kv, hkv, rfl⟩ := Multiset.mem_map.mp hg
        exact (Multiset.mem_filter.mp hkv).2
    rw [hkeys]
    conv_rhs => rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun kv _ => ?_
    simp only [Function.comp_apply]
    show GenRow.specializeTuple v (Fin.append _ _) = _
    rw [specializeTuple_append]
    congr 1
    funext j
    exact specialize_ofGroup is ((q.evaluateGen d).map GenRow.toAnnotated)
      kv.fst (fs j) (ts j) v
  | ProvSum is his t q ih =>
    intro hq
    exact hq.elim
  | GammaTok is his ts fs a q ih =>
    intro hq
    exact hq.elim
  | Retag h q ih =>
    intro hq d v
    exact ih hq d v

/-! ## Unrestricted probabilistic query evaluation (PQE) -/

/-- The Boolean provenance of a general query: the `⊕`-sum of the
finalized annotations of its rows – true in a world iff some row is
realized. -/
noncomputable def QueryGen.booleanProv {n : ℕ} {κ : Fin n → ColKind}
    (q : QueryGen T n κ)
    (d : AnnotatedDatabase T (BoolFunc X)) : BoolFunc X :=
  ((q.evaluateGen d).map (fun r => r.snd.finalize)).sum

/-- **Pointwise PQE bridge, general form**: the Boolean provenance of a
general query is true in a world iff the plain evaluation of that world
is non-empty. Immediate from the random-world commutation. -/
theorem QueryGen.booleanProv_eval_iff {n : ℕ} {κ : Fin n → ColKind}
    (q : QueryGen T n κ) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool) :
    (q.booleanProv d) v = true
      ↔ q.evaluatePlain (d.randomWorld v) ≠ 0 := by
  unfold QueryGen.booleanProv
  rw [multiset_sum_eval, ← QueryGen.genRandomWorld_evaluateGen q hq d v]
  unfold genRandomWorld
  rw [Ne, Multiset.map_eq_zero]
  constructor
  · rintro ⟨f, hf, hfv⟩ h0
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hf
    exact absurd (Multiset.mem_filter.mpr ⟨hr, hfv⟩)
      (by rw [h0]; exact Multiset.notMem_zero r)
  · intro hne
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨hrR, hrf⟩ := Multiset.mem_filter.mp hr
    exact ⟨r.snd.finalize, Multiset.mem_map.mpr ⟨r, hrR, rfl⟩, hrf⟩

/-- Probability that a random world of `d` satisfies the Boolean query
`q` (non-empty answer), over a tuple-independent probabilistic
database. -/
noncomputable def QueryGen.booleanProb {n : ℕ} {κ : Fin n → ColKind}
    (P : ProbAssignment X) (q : QueryGen T n κ)
    (d : AnnotatedDatabase T (BoolFunc X)) : ℚ :=
  ∑ v : X → Bool,
    if Multiset.card (q.evaluatePlain (d.randomWorld v)) = 0 then 0
    else P.valProb v

/-- **Unrestricted probabilistic query evaluation.** For *any* general
query – aggregate comparisons anywhere, through joins, projections,
unions and further selections – over a tuple-independent probabilistic
database, the probability that a random world satisfies the Boolean
query equals the probability of its Boolean provenance. This removes the
top-level restriction of the fused `booleanHaving_pqe`. -/
theorem QueryGen.boolean_pqe {n : ℕ} {κ : Fin n → ColKind}
    (P : ProbAssignment X) (q : QueryGen T n κ) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) :
    QueryGen.booleanProb P q d = P.funcProb (q.booleanProv d) := by
  unfold QueryGen.booleanProb ProbAssignment.funcProb
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : q.evaluatePlain (d.randomWorld v) = 0
  · rw [if_pos (Multiset.card_eq_zero.mpr h),
      if_neg (fun hf => (QueryGen.booleanProv_eval_iff q hq d v).mp hf h)]
  · rw [if_neg (fun hc => h (Multiset.card_eq_zero.mp hc)),
      if_pos ((QueryGen.booleanProv_eval_iff q hq d v).mpr h)]

/-- The provenance of a tuple `t` in a general query with all-regular
output: the `⊕`-sum of the finalized annotations of the rows whose data
part is `t`. -/
noncomputable def QueryGen.tupleProv {n : ℕ}
    (q : QueryGen T n (ColKind.allReg n))
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) : BoolFunc X :=
  (((q.evaluateGen d).filter
    (fun r => GenRow.plainTuple r.fst = t)).map
      (fun r => r.snd.finalize)).sum

/-- **Pointwise tuple-marginal bridge**: the provenance of `t` is true in
a world iff `t` belongs to the plain evaluation of that world. -/
theorem QueryGen.tupleProv_eval_iff {n : ℕ}
    (q : QueryGen T n (ColKind.allReg n)) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) (v : X → Bool) :
    (q.tupleProv d t) v = true
      ↔ t ∈ q.evaluatePlain (d.randomWorld v) := by
  unfold QueryGen.tupleProv
  rw [multiset_sum_eval, ← QueryGen.genRandomWorld_evaluateGen q hq d v]
  unfold genRandomWorld
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨f, hf, hfv⟩
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hf
    obtain ⟨hrR, hrt⟩ := Multiset.mem_filter.mp hr
    refine ⟨r, Multiset.mem_filter.mpr ⟨hrR, hfv⟩, ?_⟩
    rw [← hrt]
    funext k
    obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg
      (QueryGen.evaluateGen_conform q d r hrR k)
    unfold GenRow.specializeTuple GenRow.plainTuple
    rw [hw]
    rfl
  · rintro ⟨r, hr, hrt⟩
    obtain ⟨hrR, hrf⟩ := Multiset.mem_filter.mp hr
    refine ⟨r.snd.finalize, Multiset.mem_map.mpr
      ⟨r, Multiset.mem_filter.mpr ⟨hrR, ?_⟩, rfl⟩, hrf⟩
    rw [← hrt]
    funext k
    obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg
      (QueryGen.evaluateGen_conform q d r hrR k)
    unfold GenRow.specializeTuple GenRow.plainTuple
    rw [hw]
    rfl

/-- The marginal probability that `t` belongs to a random world's
answer. -/
noncomputable def QueryGen.tupleProb {n : ℕ} (P : ProbAssignment X)
    (q : QueryGen T n (ColKind.allReg n))
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) : ℚ :=
  ∑ v : X → Bool,
    if t ∈ q.evaluatePlain (d.randomWorld v) then P.valProb v else 0

/-- **Unrestricted tuple-marginal PQE**: for a general query with
all-regular output over a tuple-independent probabilistic database, the
marginal probability of an answer tuple is the probability of its
provenance. This is the general-evaluator counterpart of the paper's
intensional-PQE theorem, with aggregate comparisons allowed anywhere in
the query. -/
theorem QueryGen.tuple_pqe {n : ℕ} (P : ProbAssignment X)
    (q : QueryGen T n (ColKind.allReg n)) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) :
    QueryGen.tupleProb P q d t = P.funcProb (q.tupleProv d t) := by
  unfold QueryGen.tupleProb ProbAssignment.funcProb
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : t ∈ q.evaluatePlain (d.randomWorld v)
  · rw [if_pos h, if_pos ((QueryGen.tupleProv_eval_iff q hq d t v).mpr h)]
  · rw [if_neg h,
      if_neg (fun hf => h ((QueryGen.tupleProv_eval_iff q hq d t v).mp hf))]
