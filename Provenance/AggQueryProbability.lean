/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryBridges
import Provenance.HavingProbability

/-!
# Possible-world foundations for the general evaluator

The token-level ingredients of the random-world commutation for
`AggQueryIn.evaluate` over `𝔹[X]` (the general-evaluator counterpart of
`randomWorld_evaluateAnnotated`, whose target statement is

`genRandomWorld v (q.evaluate d) = q.evaluatePlain (d.randomWorld v)`

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
/-- A token has a realized occurrence as soon as one of its occurrences is
realized. -/
theorem realized_nonempty_of_mem (a : AggValue T (BoolFunc X)) (v : X → Bool)
    {x : T × BoolFunc X} (hx : x ∈ a.occs) (hv : x.snd v = true) :
    (a.realized v).Nonempty := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩⟩
  unfold AggValue.anns
  rw [hj]
  exact hv

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- The world-faithful reading under a valuation is the per-world reading
at the realized world. -/
theorem specialize_eval (a : AggValue T (BoolFunc X)) (v : X → Bool) :
    a.specialize (fun α => α v) = a.valOn (a.realized v) := by
  rw [AggValue.specialize_eq_valOn]
  congr 1

/-! ### A token read over its distinct values

The merged token reads one occurrence per class, annotated by the `⊕`
of the class's members and ordered by the domain. Under a valuation it
therefore reads the classes the world holds, in that world's own order,
and its reading is the distinct aggregate of the realized occurrences –
with no condition on the aggregate, which is what the order being a
function of the values buys. -/

omit [ValueType T] [Fintype X] [DecidableEq X] in
theorem zero_boolFunc_eval (v : X → Bool) : (0 : BoolFunc X) v = false := rfl


omit [Fintype X] [DecidableEq X] in
/-- A class sum is realized by a valuation exactly when one of the
class's occurrences is. -/
theorem classSum_eval_iff (v : X → Bool) (u : T) :
    ∀ l : List (T × BoolFunc X),
      (classSum l u) v = true ↔ ∃ p ∈ l, p.1 = u ∧ p.2 v = true
  | [] => by
    constructor
    · intro h
      exact absurd h (by simp [classSum, zero_boolFunc_eval])
    · rintro ⟨p, hp, -⟩; exact absurd hp List.not_mem_nil
  | (w, α) :: t => by
    rw [classSum, List.map_cons, List.sum_cons]
    show ((if w = u then α else 0) v || (classSum t u) v) = true ↔ _
    rw [Bool.or_eq_true, classSum_eval_iff v u t]
    constructor
    · rintro (h | ⟨p, hp, hpu, hpv⟩)
      · by_cases hw : w = u
        · exact ⟨(w, α), List.mem_cons_self, hw, by simpa [hw] using h⟩
        · rw [ite_eq_right hw, zero_boolFunc_eval] at h
          exact absurd h Bool.false_ne_true
      · exact ⟨p, List.mem_cons_of_mem _ hp, hpu, hpv⟩
    · rintro ⟨p, hp, hpu, hpv⟩
      rcases List.mem_cons.mp hp with rfl | hpt
      · refine Or.inl ?_
        rw [ite_eq_left hpu]
        exact hpv
      · exact Or.inr ⟨p, hpt, hpu, hpv⟩



omit [ValueType T] [Fintype X] [DecidableEq X] in
private theorem map_fst_filter_map_pair (p : BoolFunc X → Bool)
    (g : T → BoolFunc X) :
    ∀ l : List T,
      (((l.map (fun u => (u, g u))).filter (fun o => p o.snd)).map Prod.fst)
        = l.filter (fun u => p (g u))
  | [] => rfl
  | u :: t => by
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    by_cases hu : p (g u) <;>
      simp [hu, map_fst_filter_map_pair p g t]

theorem nodup_sort_dedup (l : List T) :
    (Multiset.sort (Multiset.ofList (List.dedup l)) (· ≤ ·)).Nodup :=
  (Quotient.exact
    (Multiset.sort_eq (Multiset.ofList (List.dedup l)) (· ≤ ·))).symm.nodup
      (List.nodup_dedup l)

omit [Fintype X] [DecidableEq X] in
/-- **A merged token specializes to the distinct aggregate of the
realized occurrences.** Restricting to a world keeps the classes the
world holds, in the order the domain gives their values, which is that
world's own order. -/
theorem specialize_mergeByValue (a : AggValue T (BoolFunc X)) (v : X → Bool) :
    (mergeByValue a).specialize (fun α => α v)
      = a.agg.distinct ((a.occs.filter (fun o => o.snd v)).map Prod.fst) := by
  show a.agg _ = a.agg _
  refine congrArg a.agg ?_
  rw [show (mergeByValue a).occs
      = (Multiset.sort ((a.occs.map Prod.fst).dedup : Multiset T) (· ≤ ·)).map
        (fun u => (u, classSum a.occs u)) from rfl,
    map_fst_filter_map_pair (fun α => α v) (fun u => classSum a.occs u)]
  refine List.Perm.eq_of_pairwise' ((Multiset.pairwise_sort _ _).filter _)
    (Multiset.pairwise_sort _ _) ?_
  refine (List.perm_ext_iff_of_nodup ((nodup_sort_dedup _).filter _)
    (nodup_sort_dedup _)).mpr (fun u => ?_)
  rw [List.mem_filter, Multiset.mem_sort, Multiset.mem_sort,
        Multiset.mem_coe, Multiset.mem_coe, List.mem_dedup, List.mem_dedup,
        List.mem_map, List.mem_map]
  constructor
  · rintro ⟨-, hq⟩
    obtain ⟨p, hp, hpu, hpv⟩ := (classSum_eval_iff v u a.occs).mp hq
    exact ⟨p, List.mem_filter.mpr ⟨hp, hpv⟩, hpu⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hpo, hpv⟩ := List.mem_filter.mp hp
    exact ⟨⟨p, hpo, rfl⟩,
      (classSum_eval_iff v p.fst a.occs).mpr ⟨p, hpo, rfl, hpv⟩⟩

/-- **The token-level PQE bridge.** Under a valuation `v`, the predicate
provenance of `⟨token⟩ op c` is true iff the token's realized group is
non-empty and its specialized aggregate value satisfies the comparison.
The σ-aggregate case of the random-world commutation reduces to this. -/
theorem predProv_eval_iff (a : AggValue T (BoolFunc X)) (op : CompOp)
    (c : T) (v : X → Bool) :
    (a.predProv op c) v = true
      ↔ (a.realized v).Nonempty
        ∧ op.eval3 (a.specialize (fun α => α v)) c = Kleene.true := by
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

/-- The scalar counterpart: with the empty world among a token's worlds,
the comparison holds under a valuation exactly when it holds of the
aggregate over the realized occurrences – whether or not any is realized.
The hypothesis of `predProv_eval_iff` is what the scalar convention drops. -/
theorem predProvScalar_eval_iff (a : AggValue T (BoolFunc X)) (op : CompOp)
    (c : T) (v : X → Bool) :
    (a.predProvScalar op c) v = true
      ↔ op.eval3 (a.specialize (fun α => α v)) c = Kleene.true := by
  rw [AggValue.specialize_eval]
  unfold AggValue.predProvScalar
  rw [sum_eval_eq_true_iff]
  constructor
  · rintro ⟨W, -, hWv⟩
    have hsplit : ((Having.worldAnn a.anns W) v
        && (Having.chi (K := BoolFunc X) op (a.valOn W) c) v) = true := hWv
    rw [Bool.and_eq_true] at hsplit
    have hWeq : W = a.realized v :=
      (worldAnn_eval_iff a.anns W v).mp hsplit.1
    subst hWeq
    exact (chi_eval_iff op _ c v).mp hsplit.2
  · intro hP
    refine ⟨a.realized v, Finset.mem_univ _, ?_⟩
    have hgoal : ((Having.worldAnn a.anns (a.realized v)) v
        && (Having.chi (K := BoolFunc X) op
              (a.valOn (a.realized v)) c) v) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(worldAnn_eval_iff a.anns _ v).mpr rfl,
        (chi_eval_iff op _ c v).mpr hP⟩
    exact hgoal

/-- **The token-level PQE bridge for a test**, as `predProv_eval_iff`
with an arbitrary three-valued test in place of the comparison. -/
theorem predProvWith_eval_iff (a : AggValue T (BoolFunc X)) (P : T → Kleene)
    (v : X → Bool) :
    (a.predProvWith P) v = true
      ↔ (a.realized v).Nonempty
        ∧ P (a.specialize (fun α => α v)) = Kleene.true := by
  rw [AggValue.specialize_eval]
  unfold AggValue.predProvWith
  rw [sum_eval_eq_true_iff]
  constructor
  · rintro ⟨W, hW, hWv⟩
    obtain ⟨-, hne⟩ := Finset.mem_filter.mp hW
    have hsplit : ((Having.worldAnn a.anns W) v
        && (Having.chiOf (K := BoolFunc X) P (a.valOn W)) v) = true := hWv
    rw [Bool.and_eq_true] at hsplit
    have hWeq : W = a.realized v :=
      (worldAnn_eval_iff a.anns W v).mp hsplit.1
    subst hWeq
    exact ⟨hne, (chiOf_eval_iff P _ v).mp hsplit.2⟩
  · rintro ⟨hne, hP⟩
    refine ⟨a.realized v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, ?_⟩
    have hgoal : ((Having.worldAnn a.anns (a.realized v)) v
        && (Having.chiOf (K := BoolFunc X) P (a.valOn (a.realized v))) v)
          = true := by
      rw [Bool.and_eq_true]
      exact ⟨(worldAnn_eval_iff a.anns _ v).mpr rfl,
        (chiOf_eval_iff P _ v).mpr hP⟩
    exact hgoal

/-- The scalar counterpart for a test. -/
theorem predProvScalarWith_eval_iff (a : AggValue T (BoolFunc X))
    (P : T → Kleene) (v : X → Bool) :
    (a.predProvScalarWith P) v = true
      ↔ P (a.specialize (fun α => α v)) = Kleene.true := by
  rw [AggValue.specialize_eval]
  unfold AggValue.predProvScalarWith
  rw [sum_eval_eq_true_iff]
  constructor
  · rintro ⟨W, -, hWv⟩
    have hsplit : ((Having.worldAnn a.anns W) v
        && (Having.chiOf (K := BoolFunc X) P (a.valOn W)) v) = true := hWv
    rw [Bool.and_eq_true] at hsplit
    have hWeq : W = a.realized v :=
      (worldAnn_eval_iff a.anns W v).mp hsplit.1
    subst hWeq
    exact (chiOf_eval_iff P _ v).mp hsplit.2
  · intro hP
    refine ⟨a.realized v, Finset.mem_univ _, ?_⟩
    have hgoal : ((Having.worldAnn a.anns (a.realized v)) v
        && (Having.chiOf (K := BoolFunc X) P (a.valOn (a.realized v))) v)
          = true := by
      rw [Bool.and_eq_true]
      exact ⟨(worldAnn_eval_iff a.anns _ v).mpr rfl,
        (chiOf_eval_iff P _ v).mpr hP⟩
    exact hgoal

/-- The token PQE bridge for a test, in the token's own convention. -/
theorem predProvOfWith_eval_iff (a : AggValue T (BoolFunc X))
    (P : T → Kleene) (v : X → Bool) :
    (a.predProvOfWith P) v = true
      ↔ (a.scalar = true ∨ (a.realized v).Nonempty)
        ∧ P (a.specialize (fun α => α v)) = Kleene.true := by
  unfold AggValue.predProvOfWith
  cases hs : a.scalar
  · simpa [hs] using predProvWith_eval_iff a P v
  · simp only [ite_true]
    rw [predProvScalarWith_eval_iff]
    simp

/-- **The token PQE bridge, in the token's own convention.** A grouped
token needs a realized occurrence; a scalar one does not, the empty world
being one of its worlds. -/
theorem predProvOf_eval_iff (a : AggValue T (BoolFunc X)) (op : CompOp)
    (c : T) (v : X → Bool) :
    (a.predProvOf op c) v = true
      ↔ (a.scalar = true ∨ (a.realized v).Nonempty)
        ∧ op.eval3 (a.specialize (fun α => α v)) c = Kleene.true := by
  unfold AggValue.predProvOf
  cases hs : a.scalar
  · simpa [hs] using predProv_eval_iff a op c v
  · simp only [ite_true]
    rw [predProvScalar_eval_iff]
    simp

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
theorem TermGIn.eval_specialize {c n : ℕ} {κ : Fin n → ColKind}
    (t : TermGIn T c κ) {γ : Fin c → T} (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool) :
    t.eval u γ = t.evalPlain (GenRow.specializeTuple v u) γ := by
  induction t with
  | const a => rfl
  | outer k => rfl
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
  | add t₁ t₂ ih₁ ih₂ => rw [TermGIn.eval, TermGIn.evalPlain, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => rw [TermGIn.eval, TermGIn.evalPlain, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => rw [TermGIn.eval, TermGIn.evalPlain, ih₁, ih₂]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    rw [TermGIn.eval, TermGIn.evalPlain, ih₁, ih₂, ih₃, ih₄]
  | coalesce t₁ t₂ ih₁ ih₂ =>
    rw [TermGIn.eval, TermGIn.evalPlain, ih₁, ih₂]

omit [Fintype X] [DecidableEq X] in
/-- On a kind-conformant tuple, an aggregate-atom-free predicate evaluates
as its plain reading does on the specialized tuple – three-valuedly, so the
statement covers the unknown case too. -/
theorem GenPredIn.eval3_eq_specialize {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (hφ : φ.hasAggAtom = false)
    (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool) :
    φ.eval3 u γ = φ.evalPlain3 (GenRow.specializeTuple v u) γ := by
  induction φ with
  | cmp op t₁ t₂ =>
    rw [GenPredIn.eval3, GenPredIn.evalPlain3,
      TermGIn.eval_specialize t₁ u hconf v, TermGIn.eval_specialize t₂ u hconf v]
  | aggCmp k h op t => exact absurd hφ (by simp [GenPredIn.hasAggAtom])
  | aggRange k h op₁ t₁ op₂ t₂ =>
    exact absurd hφ (by simp [GenPredIn.hasAggAtom])
  | and φ ψ ihφ ihψ =>
    rw [GenPredIn.hasAggAtom, Bool.or_eq_false_iff] at hφ
    rw [GenPredIn.eval3, GenPredIn.evalPlain3, ihφ hφ.1, ihψ hφ.2]
  | or φ ψ ihφ ihψ =>
    rw [GenPredIn.hasAggAtom, Bool.or_eq_false_iff] at hφ
    rw [GenPredIn.eval3, GenPredIn.evalPlain3, ihφ hφ.1, ihψ hφ.2]
  | not φ ih =>
    rw [GenPredIn.hasAggAtom] at hφ
    rw [GenPredIn.eval3, GenPredIn.evalPlain3, ih hφ]

omit [Fintype X] [DecidableEq X] in
/-- On a kind-conformant tuple, an aggregate-atom-free predicate holds
iff its plain reading holds on the specialized tuple. -/
theorem GenPredIn.holds_iff_specialize {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (hφ : φ.hasAggAtom = false)
    (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool) :
    φ.holds u γ ↔ φ.holdsPlain (GenRow.specializeTuple v u) γ := by
  unfold GenPredIn.holds GenPredIn.holdsPlain
  rw [GenPredIn.eval3_eq_specialize φ hφ u hconf v]

/-! ## The σ-aggregate row lemma -/

/-- The annotation lists of the tokens compared by a predicate on a row
(the evaluator's `compared`). -/
def GenPredIn.selCompared {K' : Type} {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (u : Tuple (GenValue T K') n) :
    Multiset (List K') :=
  φ.comparedCols.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => some (a.occs.map Prod.snd))

/-- The compared tokens read in the scalar convention. A comparison against
one of these entails no group's existence – it holds in the empty world – so
its presence blocks the supersede whatever occurrences it carries. -/
def GenPredIn.selComparedScalar {K' : Type} {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (u : Tuple (GenValue T K') n) :
    Multiset (List K') :=
  φ.comparedCols.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => if a.scalar then some (a.occs.map Prod.snd) else none)

/-- The pending factors after a σ with aggregate atoms (the evaluator's
update, definitionally). -/
def GenPredIn.selPending {K' : Type} [DecidableEq K'] {c n : ℕ}
    {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    (u : Tuple (GenValue T K') n) (p : Multiset (List K')) :
    Multiset (List K') :=
  if φ.entailsExistence false then
    p.filter (fun l => ¬(φ.selComparedScalar u = 0 ∧ φ.selCompared u ≠ 0
      ∧ ∀ l' ∈ φ.selCompared u, l' = l))
  else p

/-- **Predicate provenance evaluation, under existence guards.** On a
kind-conformant row all of whose compared groups are realized non-empty,
the predicate provenance is true iff the (polarity-adjusted) plain
predicate holds on the specialized tuple. -/
theorem GenPredIn.predsem_eval_iff {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (neg : Bool)
    (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool)
    (hg : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
      u k = Sum.inr a → a.scalar = true ∨ (a.realized v).Nonempty) :
    ((φ.predsem neg u γ) v = true)
      ↔ (if neg = true
          then φ.evalPlain3 (GenRow.specializeTuple v u) γ = Kleene.false
          else φ.evalPlain3 (GenRow.specializeTuple v u) γ = Kleene.true) := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.predsem]
    rw [chi_eval_iff, GenPredIn.evalPlain3,
      ← TermGIn.eval_specialize t₁ u hconf v,
      ← TermGIn.eval_specialize t₂ u hconf v]
    cases neg with
    | false => simp
    | true => simp [CompOp.negate_eval3]
  | aggCmp k h op t =>
    obtain ⟨a, ha⟩ := GenValue.eq_inr_of_kindOf_agg
      ((hconf k).trans (by rw [h]; rfl))
    simp only [GenPredIn.predsem, ha]
    rw [AggValue.predProvOf_eval_iff, GenPredIn.evalPlain3]
    have hne := hg k (Finset.mem_singleton_self k) a ha
    have hspec : GenRow.specializeTuple v u k
        = a.specialize (fun α => α v) := by
      unfold GenRow.specializeTuple
      rw [ha]
      rfl
    rw [hspec, ← TermGIn.eval_specialize t u hconf v]
    cases neg with
    | false => simp [hne]
    | true => simp [hne, CompOp.negate_eval3]
  | aggRange k h op₁ t₁ op₂ t₂ =>
    obtain ⟨a, ha⟩ := GenValue.eq_inr_of_kindOf_agg
      ((hconf k).trans (by rw [h]; rfl))
    simp only [GenPredIn.predsem, ha]
    rw [AggValue.predProvOfWith_eval_iff, GenPredIn.evalPlain3]
    have hne := hg k (Finset.mem_singleton_self k) a ha
    have hspec : GenRow.specializeTuple v u k
        = a.specialize (fun α => α v) := by
      unfold GenRow.specializeTuple
      rw [ha]
      rfl
    rw [hspec, ← TermGIn.eval_specialize t₁ u hconf v,
      ← TermGIn.eval_specialize t₂ u hconf v]
    cases neg with
    | false => simp [hne]
    | true => simp [hne]
  | and φ ψ ihφ ihψ =>
    have hgφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = true ∨ (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_left _ hk)
    have hgψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = true ∨ (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.and φ ψ).predsem false u γ
          = φ.predsem false u γ * ψ.predsem false u γ := rfl
      rw [he]
      show (_ && _) = true ↔ _
      rw [Bool.and_eq_true, ihφ false hgφ, ihψ false hgψ,
        GenPredIn.evalPlain3]
      simp
    | true =>
      have he : (GenPredIn.and φ ψ).predsem true u γ
          = φ.predsem true u γ + ψ.predsem true u γ := rfl
      rw [he]
      show (_ || _) = true ↔ _
      rw [Bool.or_eq_true, ihφ true hgφ, ihψ true hgψ,
        GenPredIn.evalPlain3]
      simp
  | or φ ψ ihφ ihψ =>
    have hgφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = true ∨ (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_left _ hk)
    have hgψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = true ∨ (a.realized v).Nonempty :=
      fun k hk => hg k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.or φ ψ).predsem false u γ
          = φ.predsem false u γ + ψ.predsem false u γ := rfl
      rw [he]
      show (_ || _) = true ↔ _
      rw [Bool.or_eq_true, ihφ false hgφ, ihψ false hgψ,
        GenPredIn.evalPlain3]
      simp
    | true =>
      have he : (GenPredIn.or φ ψ).predsem true u γ
          = φ.predsem true u γ * ψ.predsem true u γ := rfl
      rw [he]
      show (_ && _) = true ↔ _
      rw [Bool.and_eq_true, ihφ true hgφ, ihψ true hgψ,
        GenPredIn.evalPlain3]
      simp
  | not φ ih =>
    have he : (GenPredIn.not φ).predsem neg u γ = φ.predsem (!neg) u γ := rfl
    rw [he, ih (!neg) hg, GenPredIn.evalPlain3]
    cases neg <;> simp

/-- **Existence entailment extracts the guard.** When a predicate entails
existence and all its compared tokens carry the annotation list `ℓ₀`, a
true predicate provenance realizes `ℓ₀`. -/
theorem GenPredIn.entails_guard {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (neg : Bool)
    (u : Tuple (GenValue T (BoolFunc X)) n) (v : X → Bool)
    (ℓ₀ : List (BoolFunc X))
    (huni : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
      u k = Sum.inr a → a.scalar = false ∧ a.occs.map Prod.snd = ℓ₀)
    (hent : φ.entailsExistence neg = true)
    (hp : (φ.predsem neg u γ) v = true) : annGuard ℓ₀ v := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ => exact absurd hent (by simp [GenPredIn.entailsExistence])
  | aggCmp k h op t =>
    cases hu : u k with
    | inl w =>
      simp only [GenPredIn.predsem, hu] at hp
      exact absurd hp Bool.false_ne_true
    | inr a =>
      simp only [GenPredIn.predsem, hu] at hp
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) a hu
      rw [AggValue.predProvOf_of_grouped hsc] at hp
      have hne := (AggValue.predProv_eval_iff a _ _ v).mp hp |>.1
      rw [← heq]
      exact (AggValue.annGuard_iff_realized a v).mpr hne
  | aggRange k h op₁ t₁ op₂ t₂ =>
    cases hu : u k with
    | inl w =>
      simp only [GenPredIn.predsem, hu] at hp
      exact absurd hp Bool.false_ne_true
    | inr a =>
      simp only [GenPredIn.predsem, hu] at hp
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) a hu
      have hne := (AggValue.predProvOfWith_eval_iff a _ v).mp hp |>.1
      rw [← heq]
      exact (AggValue.annGuard_iff_realized a v).mpr
        (hne.resolve_left (by rw [hsc]; exact Bool.false_ne_true))
  | and φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.and φ ψ).predsem false u γ
          = φ.predsem false u γ * ψ.predsem false u γ := rfl
      rw [he] at hp
      have hp' : ((φ.predsem false u γ) v && (ψ.predsem false u γ) v) = true := hp
      rw [Bool.and_eq_true] at hp'
      have hent' : (φ.entailsExistence false || ψ.entailsExistence false)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rcases hent' with h | h
      exacts [ihφ false huφ h hp'.1, ihψ false huψ h hp'.2]
    | true =>
      have he : (GenPredIn.and φ ψ).predsem true u γ
          = φ.predsem true u γ + ψ.predsem true u γ := rfl
      rw [he] at hp
      have hp' : ((φ.predsem true u γ) v || (ψ.predsem true u γ) v) = true := hp
      have hent' : (φ.entailsExistence true && ψ.entailsExistence true)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [Bool.or_eq_true] at hp'
      rcases hp' with h | h
      exacts [ihφ true huφ hent'.1 h, ihψ true huψ hent'.2 h]
  | or φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggValue T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.occs.map Prod.snd = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.or φ ψ).predsem false u γ
          = φ.predsem false u γ + ψ.predsem false u γ := rfl
      rw [he] at hp
      have hp' : ((φ.predsem false u γ) v || (ψ.predsem false u γ) v) = true := hp
      have hent' : (φ.entailsExistence false && ψ.entailsExistence false)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [Bool.or_eq_true] at hp'
      rcases hp' with h | h
      exacts [ihφ false huφ hent'.1 h, ihψ false huψ hent'.2 h]
    | true =>
      have he : (GenPredIn.or φ ψ).predsem true u γ
          = φ.predsem true u γ * ψ.predsem true u γ := rfl
      rw [he] at hp
      have hp' : ((φ.predsem true u γ) v && (ψ.predsem true u γ) v) = true := hp
      rw [Bool.and_eq_true] at hp'
      have hent' : (φ.entailsExistence true || ψ.entailsExistence true)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rcases hent' with h | h
      exacts [ihφ true huφ h hp'.1, ihψ true huψ h hp'.2]
  | not φ ih =>
    have he : (GenPredIn.not φ).predsem neg u γ = φ.predsem (!neg) u γ := rfl
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
theorem GenPredIn.sel_finalize_old {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (u : Tuple (GenValue T (BoolFunc X)) n)
    (b : BoolFunc X) (p : Multiset (List (BoolFunc X))) (v : X → Bool)
    (h : (GenAnn.mk (b * φ.predsem false u γ) (φ.selPending u p)).finalize v
      = true) :
    (GenAnn.mk b p).finalize v = true := by
  rw [GenAnn.finalize_eval_iff] at h ⊢
  obtain ⟨hbp, hupd⟩ := h
  have hbp' : (b v && (φ.predsem false u γ) v) = true := hbp
  rw [Bool.and_eq_true] at hbp'
  refine ⟨hbp'.1, fun l hl => ?_⟩
  unfold GenPredIn.selPending at hupd
  by_cases hE : φ.entailsExistence false = true
  · rw [ite_eq_left hE] at hupd
    by_cases hcond : (φ.selComparedScalar u = 0 ∧ φ.selCompared u ≠ 0
        ∧ ∀ l' ∈ φ.selCompared u, l' = l)
    · refine GenPredIn.entails_guard φ false u v l ?_ hE hbp'.2
      intro k hk a ha
      refine ⟨?_, ?_⟩
      · -- no compared token is scalar, so this one is grouped
        by_contra hsc
        rw [Bool.not_eq_false] at hsc
        have hmem : (a.occs.map Prod.snd) ∈ φ.selComparedScalar u :=
          (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [ha, hsc]⟩
        rw [hcond.1] at hmem
        exact absurd hmem (Multiset.notMem_zero _)
      · refine hcond.2.2 _ ?_
        have hmem : (a.occs.map Prod.snd) ∈ φ.selCompared u :=
          (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [ha]⟩
        exact hmem
    · exact hupd l (Multiset.mem_filter.mpr ⟨hl, hcond⟩)
  · rw [ite_eq_right hE] at hupd
    exact hupd l hl

/-- **The σ-aggregate row lemma.** On a kind-conformant, guarded row, the
updated annotation is realized iff the original annotation is realized
and the plain predicate holds on the specialized tuple. -/
theorem GenPredIn.sel_finalize_eval_iff {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (u : Tuple (GenValue T (BoolFunc X)) n)
    (b : BoolFunc X) (p : Multiset (List (BoolFunc X))) (v : X → Bool)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base)
    (hguard : (GenAnn.mk b p).finalize v = true →
      ∀ (k : Fin n) (a : AggValue T (BoolFunc X)), u k = Sum.inr a →
        a.scalar = true ∨ (a.realized v).Nonempty) :
    ((GenAnn.mk (b * φ.predsem false u γ) (φ.selPending u p)).finalize v
        = true)
      ↔ (GenAnn.mk b p).finalize v = true
        ∧ φ.holdsPlain (GenRow.specializeTuple v u) γ := by
  constructor
  · intro h
    have hold := GenPredIn.sel_finalize_old φ u b p v h
    have hbp : (b v && (φ.predsem false u γ) v) = true :=
      ((GenAnn.finalize_eval_iff _ v).mp h).1
    rw [Bool.and_eq_true] at hbp
    refine ⟨hold, ?_⟩
    have hps := (GenPredIn.predsem_eval_iff φ false u hconf v
      (fun k _ a ha => hguard hold k a ha)).mp hbp.2
    rw [ite_eq_right Bool.false_ne_true] at hps
    exact hps
  · rintro ⟨hold, hh⟩
    have hgs := hguard hold
    rw [GenAnn.finalize_eval_iff] at hold ⊢
    obtain ⟨hb, hG⟩ := hold
    have hps : (φ.predsem false u γ) v = true :=
      (GenPredIn.predsem_eval_iff φ false u hconf v
        (fun k _ a ha => hgs k a ha)).mpr
        (by rw [ite_eq_right Bool.false_ne_true]; exact hh)
    refine ⟨?_, fun l hl => ?_⟩
    · show (b v && _) = true
      rw [Bool.and_eq_true]
      exact ⟨hb, hps⟩
    · unfold GenPredIn.selPending at hl
      by_cases hE : φ.entailsExistence false = true
      · rw [ite_eq_left hE] at hl
        exact hG l (Multiset.mem_of_mem_filter hl)
      · rw [ite_eq_right hE] at hl
        exact hG l hl

/-! ## The guardedness invariant -/

variable [HasAltLinearOrder (BoolFunc X)]

/-- **Guardedness of the general evaluator**: on any row it produces,
whenever the finalized annotation is realized, every *grouped* token's group
is realized non-empty – the group-existence guard of each such token is
carried either by a pending factor or by a predicate provenance in the
concrete part.

A scalar token is exempt, and has to be: its row exists on its own, and the
empty world is one of its worlds, so there is no occurrence to realize. This
is the case split the possible-world reading of an aggregate comparison
makes anyway. -/
theorem AggQueryIn.evaluate_guarded :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (d : AnnotatedDatabase T (BoolFunc X)) {γ : Fin c → T}
      (r : GenRow T (BoolFunc X) n),
      r ∈ q.evaluate d γ → ∀ v : X → Bool, r.snd.finalize v = true →
      ∀ (k : Fin n) (a : AggValue T (BoolFunc X)), r.fst k = Sum.inr a →
        a.scalar = true ∨ (a.realized v).Nonempty := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro d γ r hr v _ k a ha
    simp only [AggQueryIn.evaluate] at hr
    cases hf : d.find n s with
    | none => rw [hf] at hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      rw [hf] at hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      exact absurd ha (by simp [GenRow.ofAnnotated])
  | Proj ps q ih =>
    intro d γ r hr v hfin j a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
    have hfin₀ : r₀.snd.finalize v = true := by
      rw [← GenAnn.finalize_cash r₀.snd.base r₀.snd.pending
        (r₀.snd.pending ∩ tokenLists (fun j => (ps j).eval r₀.fst γ))
        Multiset.inter_le_left]
      exact hfin
    have ha' : (ps j).eval r₀.fst γ = Sum.inr a := ha
    cases hp : ps j with
    | term t =>
      rw [hp] at ha'
      exact absurd ha' (by simp [ProjColIn.eval])
    | provTerm t =>
      rw [hp] at ha'
      exact absurd ha' (by simp [ProjColIn.eval])
    | token k hk =>
      rw [hp] at ha'
      exact ih d r₀ hr₀ v hfin₀ k a ha'
    | aggTerm k hk gf =>
      -- reading a token through a function changes neither its
      -- occurrences nor its convention, so the guard is the token's
      rw [hp] at ha'
      replace ha' : Sum.map gf (AggValue.postcomp gf) (r₀.fst k)
          = Sum.inr a := ha'
      cases hu : r₀.fst k with
      | inl w =>
        rw [hu] at ha'
        exact absurd ha' (by simp)
      | inr a₀ =>
        have hha : a = a₀.postcomp gf := by
          rw [hu] at ha'
          exact (Sum.inr.inj ha').symm
        subst hha
        exact ih d r₀ hr₀ v hfin₀ k a₀ hu
  | Sel φ q ih =>
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.mp hr
      have hold := GenPredIn.sel_finalize_old φ r₀.fst r₀.snd.base
        r₀.snd.pending v hfin
      exact ih d r₀ hr₀ v hold k a ha
    · rw [ite_eq_right hφ] at hr
      exact ih d r (Multiset.mem_of_mem_filter hr) v hfin k a ha
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
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
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hx, hr⟩ := Multiset.mem_bind.mp hr
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hr
    have hfin' : (x.snd.finalize v && y.snd.finalize v) = true := by
      have := GenAnn.finalize_mul x.snd y.snd
      rw [show (GenAnn.mk (x.snd.base * y.snd.base)
          (x.snd.pending + y.snd.pending)).finalize
          = x.snd.finalize * y.snd.finalize from this] at hfin
      exact hfin
    rw [Bool.and_eq_true] at hfin'
    revert ha
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro ha
    · exact ih₁ d x hx v hfin'.1 i a
        ((Fin.append_left x.fst y.fst i).symm.trans ha)
    · exact ih₂ d y hy v hfin'.2 j a
        ((Fin.append_right x.fst y.fst j).symm.trans ha)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.mp hr with h | h
    exacts [ih₁ d r h v hfin k a ha, ih₂ d r h v hfin k a ha]
  | Dedup q ih =>
    intro d γ r hr v _ k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro d γ r hr v _ k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro d γ r hr v _ k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro d γ r hr v _ k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    exact absurd ha (by simp [GenRow.ofAnnotated])
  | @GammaScalar cI m n₂ ts fs q ih =>
    -- every token of a scalar aggregation is scalar, so the guard is vacuous
    intro d γ r hr v _ k a ha
    refine Or.inl ?_
    simp only [AggQueryIn.evaluate] at hr
    rw [Multiset.mem_singleton] at hr
    subst hr
    rw [← Sum.inr.inj ha]
    rfl
  | Gamma is ts fs q ih =>
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    have hG : annGuard ((Having.havingGroup is
        ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map Prod.snd) v :=
      ((GenAnn.finalize_eval_iff _ v).mp hfin).2 _ (Multiset.mem_singleton_self _)
    revert ha
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro ha
    · have ha' : (Sum.inl (kv.fst i) : GenValue T (BoolFunc X)) = Sum.inr a :=
        (Fin.append_left
          (fun k => (Sum.inl (kv.fst k) : GenValue T (BoolFunc X)))
          (fun j' => Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst) γ)) i).symm.trans
          ha
      exact absurd ha' (by simp)
    · have haj : (Sum.inr (AggValue.ofGroup (fs j) (ts j)
          (Having.havingGroup is
            ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst) γ)
          : GenValue T (BoolFunc X)) = Sum.inr a :=
        (Fin.append_right
          (fun k => (Sum.inl (kv.fst k) : GenValue T (BoolFunc X)))
          (fun j' => Sum.inr (AggValue.ofGroup (fs j') (ts j')
            (Having.havingGroup is
              ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst) γ)) j).symm.trans
          ha
      rw [← Sum.inr.inj haj]
      refine Or.inr ((AggValue.annGuard_iff_realized _ v).mp ?_)
      rw [AggValue.annList_ofGroup]
      exact hG
  | @Win cI n' m' p' P O o w t f q dist ih =>
    -- a window creates no group, and its one token is guarded by the row it
    -- is computed for whenever that row is in its own frame; when it is not,
    -- the token is scalar and the guard is vacuous
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
    revert ha
    refine Fin.lastCases (fun ha => ?_) (fun k' ha => ?_) k
    · dsimp only at ha
      rw [Fin.snoc_last] at ha
      rw [← Sum.inr.inj ha]
      by_cases hs : w.s (Tuple.key O ((OccFam.ofSorted
          ((q.evaluate d γ).map GenRow.toAnnotated)).row i).fst) = true
      · refine Or.inr ?_
        cases dist
        · exact AggValue.realized_nonempty_of_mem _ v
            (ValueFrame.mem_token_occs P O o w t f _ i hs) (by simpa using hfin)
        · refine AggValue.realized_nonempty_of_mem _ v
            (AggValue.mem_occs_mergeByValue _
              (ValueFrame.mem_token_occs P O o w t f _ i hs)) ?_
          exact (AggValue.classSum_eval_iff v _ _).mpr
            ⟨_, ValueFrame.mem_token_occs P O o w t f _ i hs, rfl,
              by simpa using hfin⟩
      · refine Or.inl ?_
        rw [ValueFrame.scalar_tokenDist]
        exact ValueFrame.token_scalar_of_not_mem P O o w t f _ i
          (by simpa using hs)
    · dsimp only at ha
      rw [Fin.snoc_castSucc] at ha
      exact absurd ha (by simp)
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro d γ r hr v _ k a ha
    have hconf := AggQueryIn.evaluate_conform _ d r hr k
    rw [ha] at hconf
    revert hconf
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro hconf
    · rw [Fin.append_left, ColKind.base_eq_reg_of_ne_agg (his i)] at hconf
      exact ColKind.noConfusion hconf
    · rw [Fin.append_right] at hconf
      exact ColKind.noConfusion hconf
  | @GammaTok cI m n₁ n₂ κ' is his ts fs a' q ih =>
    intro d γ r hr v hfin k a ha
    have hconf := AggQueryIn.evaluate_conform _ d r hr k
    rw [ha] at hconf
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    have hG : annGuard ((Having.havingGroup is
        ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map Prod.snd) v :=
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
        refine Or.inr ((AggValue.annGuard_iff_realized _ v).mp ?_)
        rw [AggValue.annList_ofGroup]
        exact hG
    · rw [Fin.append_right] at hconf
      exact ColKind.noConfusion hconf
  | Retag h q ih =>
    intro d γ r hr v hfin k a ha
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
private lemma genRandomWorld_allReg {c n : ℕ}
    (q : AggQueryIn T c n (ColKind.allReg n))
    (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool)
    {γ : Fin c → T} :
    randomWorld v ((q.evaluate d γ).map GenRow.toAnnotated)
      = genRandomWorld v (q.evaluate d γ) := by
  unfold randomWorld genRandomWorld
  rw [filter_map_comm, Multiset.map_map]
  refine Multiset.map_congr
    (Multiset.filter_congr fun r _ => Iff.rfl) fun r hr => ?_
  have hconf := AggQueryIn.evaluate_conform q d r
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
private lemma ProjColIn.specializeAt_eval {c n : ℕ} {κ : Fin n → ColKind}
    (pc : ProjColIn T c κ) (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base) (v : X → Bool)
    {γ : Fin c → T} :
    GenValue.specializeAt v (pc.eval u γ)
      = pc.evalPlain (GenRow.specializeTuple v u) γ := by
  cases pc with
  | term t =>
    show GenValue.specializeAt v (Sum.inl (t.eval u γ)) = _
    exact TermGIn.eval_specialize t u hconf v
  | token k hk => rfl
  | aggTerm k hk gf =>
    show GenValue.specializeAt v (Sum.map gf (AggValue.postcomp gf) (u k))
      = gf (GenValue.specializeAt v (u k))
    cases u k <;> rfl
  | provTerm t =>
    show GenValue.specializeAt v (Sum.inl (t.eval u γ)) = _
    exact TermGIn.eval_specialize t u hconf v

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
        rw [ite_eq_left hcond_lhs, ite_eq_left hpv, ih]
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
        rw [ite_eq_right hcond_lhs, ite_eq_left hpv, ih]
        rw [Multiset.filter_cons_of_neg
            (p := fun t : Tuple T n => t ∉ randomWorld v r₂) _ hp_in]
    · have hpv_false : p.snd v = false := by
        cases h : p.snd v
        · rfl
        · exact absurd h hpv
      have hcond_lhs : ¬ (p.snd - β) v = true := by
        rw [show (p.snd - β) v = (p.snd v && !(β v)) from rfl, hpv_false]
        simp
      rw [ite_eq_right hcond_lhs, ite_eq_right hpv]
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
private lemma specialize_ofGroup {c m n₁ : ℕ}
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T (BoolFunc X) m)
    (g : Tuple T n₁) (f : SeqAggFunc T) (t : TermIn T c m) (v : X → Bool)
    {γ : Fin c → T} :
    (AggValue.ofGroup f t (Having.havingGroup is r g) γ).specialize
        (fun α => α v)
      = f ((Relation.groupSeq is (randomWorld v r) g).map
          (fun x => t.eval x γ)) := by
  unfold AggValue.specialize AggValue.ofGroup
  rw [groupSeq_randomWorld, seqOf_realizedWorld, List.filter_map,
    List.map_map, List.map_map]
  rfl

omit [ValueType T] [Fintype X] [DecidableEq X] in
private lemma list_filter_map_comm {α β : Type} (g : α → β) (p : β → Bool)
    (l : List α) :
    (l.map g).filter p = (l.filter (fun a => p (g a))).map g := by
  induction l with
  | nil => rfl
  | cons a t ih => by_cases hp : p (g a) <;> simp [hp, ih]

omit [Fintype X] [DecidableEq X] in
/-- **A window's token is world-faithful.** Under a valuation the token
reads as the plain aggregate the realized world gives its row: restricting
the relation to a world restricts every frame to that world, which is the
only property of frames the annotated semantics uses. -/
theorem tokenOf_filter_agg {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n')
    (f g : SeqAggFunc T) (R : AnnotatedRelation T (BoolFunc X) n')
    {x : AnnotatedTuple T (BoolFunc X) n'} (hx : x ∈ R) (v : X → Bool)
    {γ : Fin c → T} (hc : x.snd v = true) :
    g ((((ValueFrame.tokenOf P O o w t f R x γ).occs.filter
        (fun o => o.snd v)).map Prod.fst))
      = ValueFrame.windowValue P O o w t g (randomWorld v R) x.fst γ := by
  have hframe : ValueFrame.frameOf (α := Tuple T n') id P O w
      (randomWorld v R) x.fst
      = Multiset.map (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
        ((ValueFrame.frameOf (α := AnnotatedTuple T (BoolFunc X) n')
          Prod.fst P O w R x).filter
          (fun y : AnnotatedTuple T (BoolFunc X) n' => y.snd v = true)) := by
    unfold randomWorld
    rw [ValueFrame.frameOf_map (α := AnnotatedTuple T (BoolFunc X) n')
        (valα := Prod.fst) (valβ := id) Prod.fst (fun _ => rfl) P O w _
        (Multiset.mem_filter.mpr ⟨hx, hc⟩),
      ValueFrame.frameOf_filter (α := AnnotatedTuple T (BoolFunc X) n')
        Prod.fst _ P O w R hc]
  have hproj : ∀ L : List (AnnotatedTuple T (BoolFunc X) n'),
      List.map (fun q : AnnotatedTuple T (BoolFunc X) n' => t.eval q.fst γ)
          (OrderSpec.sortSeq (Tuple.key O) Prod.fst o L)
        = List.map (fun x => t.eval x γ) (OrderSpec.sortSeq (Tuple.key O)
            (id : Tuple T n' → Tuple T n') o
            (List.map (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst L)) := by
    intro L
    rw [← ValueFrame.sortSeq_map_fst, List.map_map]
    rfl
  unfold ValueFrame.windowValue ValueFrame.frameListOf
  rw [ValueFrame.tokenOf_occs]
  refine congrArg g ?_
  unfold ValueFrame.frameListOf
  rw [list_filter_map_comm, List.map_map]
  have hpred : (fun q : AnnotatedTuple T (BoolFunc X) n' => q.snd v)
      = (fun q : AnnotatedTuple T (BoolFunc X) n' => decide (q.snd v = true)) := by
    funext q; simp
  show List.map (fun q : AnnotatedTuple T (BoolFunc X) n' => t.eval q.fst γ)
      (List.filter (fun q : AnnotatedTuple T (BoolFunc X) n' => q.snd v)
        (OrderSpec.sortSeq (Tuple.key O) Prod.fst o
          (sortList (ValueFrame.frameOf
            (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst P O w R x))))
    = _
  rw [hpred, OrderSpec.filter_sortSeq_map_eq (o := o) (fun x => t.eval x γ)
      (fun q : AnnotatedTuple T (BoolFunc X) n' => decide (q.snd v = true)),
    hproj, sortList_filter, ValueFrame.sortList_map_fst, hframe]


omit [Fintype X] [DecidableEq X] in
/-- **A token specializes to the aggregate of the realized frame**: the
case of `tokenOf_filter_agg` where the aggregate applied is the token's
own. -/
theorem tokenOf_specialize {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n')
    (f : SeqAggFunc T) (R : AnnotatedRelation T (BoolFunc X) n')
    {x : AnnotatedTuple T (BoolFunc X) n'} (hx : x ∈ R) (v : X → Bool)
    {γ : Fin c → T} (hc : x.snd v = true) :
    (ValueFrame.tokenOf P O o w t f R x γ).specialize (fun α => α v)
      = ValueFrame.windowValue P O o w t f (randomWorld v R) x.fst γ := by
  unfold AggValue.specialize
  rw [ValueFrame.tokenOf_agg]
  exact tokenOf_filter_agg P O o w t f f R hx v hc

omit [Fintype X] [DecidableEq X] in
/-- **The same for a token read over the frame's distinct values**: it
specializes to the distinct aggregate of the realized frame, with no
condition on the aggregate. -/
theorem tokenOfDist_specialize {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n') (f : SeqAggFunc T) (dist : Bool)
    (R : AnnotatedRelation T (BoolFunc X) n')
    {x : AnnotatedTuple T (BoolFunc X) n'} (hx : x ∈ R) (v : X → Bool)
    {γ : Fin c → T} (hc : x.snd v = true) :
    (ValueFrame.tokenOfDist P O o w t f dist R x γ).specialize (fun α => α v)
      = ValueFrame.windowValue P O o w t (if dist then f.distinct else f)
        (randomWorld v R) x.fst γ := by
  unfold ValueFrame.tokenOfDist
  cases dist
  · simpa using tokenOf_specialize P O o w t f R hx v hc
  · simp only [ite_true]
    rw [AggValue.specialize_mergeByValue, ValueFrame.tokenOf_agg]
    exact tokenOf_filter_agg P O o w t f f.distinct R hx v hc

/-! ## The random-world commutation -/

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- Generic specialization distributes over `Fin.append`. -/
private lemma filter_bind {α β : Type} (s : Multiset α) (F : α → Multiset β)
    (p : β → Prop) [DecidablePred p] :
    (s.bind F).filter p = s.bind (fun a => (F a).filter p) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.filter_add, ih]

private lemma bind_filter {α β : Type} (s : Multiset α) (p : α → Prop)
    [DecidablePred p] (F : α → Multiset β) :
    (s.filter p).bind F = s.bind (fun a => if p a then F a else 0) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases h : p a <;> simp [h, ih]

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- On a row all of whose columns are regular the specialized reading is
the collapsed one: there is no token to specialize. -/
private lemma specializeTuple_eq_plainTuple {n : ℕ}
    (u : Tuple (GenValue T (BoolFunc X)) n)
    (hconf : ∀ k, GenValue.kindOf (u k) = ColKind.reg) (v : X → Bool) :
    GenRow.specializeTuple v u = GenRow.plainTuple u := by
  funext k
  obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg (hconf k)
  unfold GenRow.plainTuple GenRow.specializeTuple
  rw [hw]
  rfl

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
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
lemma `GenPredIn.sel_finalize_eval_iff` under the conformance and
guardedness invariants; the `Gamma` case rests on
`groupSeq_randomWorld`. -/
theorem AggQueryIn.genRandomWorld_evaluate :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (_hq : q.noProvSum)
      (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool)
      {γ : Fin c → T},
    genRandomWorld v (q.evaluate d γ)
      = q.evaluatePlain (d.randomWorld v) γ := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [AnnotatedDatabase.find_randomWorld]
    cases hf : d.find n s with
    | none => rfl
    | some rn => exact genRandomWorld_ofAnnotated rn v
  | Proj ps q ih =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map]
    rw [Multiset.filter_congr (fun r (_ : r ∈ q.evaluate d γ) =>
      Iff.of_eq (congrArg (fun α : BoolFunc X => α v = true)
        (GenAnn.finalize_cash r.snd.base r.snd.pending
          (r.snd.pending ∩ tokenLists (fun j => (ps j).eval r.fst γ))
          Multiset.inter_le_left)))]
    rw [Multiset.map_congr rfl (fun r hr => ?_), ← Multiset.map_map, ← ih hq d v]
    · rfl
    · -- pointwise: the specialized projected tuple is the plain projection
      -- of the specialized tuple
      have hconf := AggQueryIn.evaluate_conform q d r
        (Multiset.mem_of_mem_filter hr)
      show GenRow.specializeTuple v (fun j => (ps j).eval r.fst γ)
        = fun j => (ps j).evalPlain (GenRow.specializeTuple v r.fst) γ
      funext j
      exact ProjColIn.specializeAt_eval (ps j) r.fst hconf v
  | Sel φ q ih =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    by_cases hφ : φ.hasAggAtom
    · rw [ite_eq_left hφ]
      unfold genRandomWorld
      rw [filter_map_comm, Multiset.map_map]
      refine Eq.trans (congrArg (Multiset.map _)
        (Multiset.filter_congr
          (q := fun r : GenRow T (BoolFunc X) _ =>
            r.snd.finalize v = true
              ∧ φ.holdsPlain (GenRow.specializeTuple v r.fst) γ)
          fun r hr => ?_)) ?_
      · exact GenPredIn.sel_finalize_eval_iff φ r.fst r.snd.base
          r.snd.pending v (AggQueryIn.evaluate_conform q d r hr)
          (fun hfin => AggQueryIn.evaluate_guarded q d r hr v hfin)
      · rw [← ih hq d v]
        unfold genRandomWorld
        rw [filter_map_comm, Multiset.filter_filter]
        exact Multiset.map_congr
          (Multiset.filter_congr fun r _ => and_comm) (fun r _ => rfl)
    · rw [ite_eq_right hφ]
      unfold genRandomWorld
      rw [Multiset.filter_filter]
      refine Eq.trans (congrArg (Multiset.map _)
        (Multiset.filter_congr
          (q := fun r : GenRow T (BoolFunc X) _ =>
            r.snd.finalize v = true
              ∧ φ.holdsPlain (GenRow.specializeTuple v r.fst) γ)
          fun r hr => ?_)) ?_
      · exact and_congr_right fun _ => GenPredIn.holds_iff_specialize φ
          (by simpa using hφ) r.fst
          (AggQueryIn.evaluate_conform q d r hr) v
      · rw [← ih hq d v]
        unfold genRandomWorld
        rw [filter_map_comm, Multiset.filter_filter]
        exact Multiset.map_congr
          (Multiset.filter_congr fun r _ => and_comm) (fun r _ => rfl)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
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
        (q₁.evaluate d γ) (q₂.evaluate d γ), ← ih₁ hq.1 d v, ← ih₂ hq.2 d v]
      show _ = Multiset.map
        (fun uv : Tuple T _ × Tuple T _ => Fin.append uv.fst uv.snd)
        (Multiset.product (genRandomWorld v (q₁.evaluate d γ))
          (genRandomWorld v (q₂.evaluate d γ)))
      unfold genRandomWorld
      rw [product_map_map, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro xy _
      exact specializeTuple_append' xy.fst.fst xy.snd.fst v
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    -- the left side is all-regular, so its rows specialize as they collapse
    have hspec : ∀ x ∈ q₁.evaluate d γ,
        GenRow.specializeTuple v x.fst = GenRow.plainTuple x.fst :=
      fun x hx => specializeTuple_eq_plainTuple x.fst
        (fun k => AggQueryIn.evaluate_conform q₁ d x hx k) v
    conv_rhs => rw [← ih₁ hq.1 d v]
    unfold genRandomWorld
    rw [filter_bind, Multiset.map_bind, Multiset.bind_map, bind_filter]
    refine Multiset.bind_congr (fun x hx => ?_)
    by_cases hfx : x.snd.finalize v = true
    · rw [ite_eq_left hfx, hspec x hx]
      rw [show ∀ M : Multiset (GenRow T (BoolFunc X) _),
          Multiset.filter (fun r : GenRow T (BoolFunc X) _ =>
              r.snd.finalize v = true)
            (M.map (fun y => ((Fin.append x.fst y.fst,
              ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩)
                : GenRow T (BoolFunc X) _)))
            = (M.filter (fun y => y.snd.finalize v = true)).map
                (fun y => ((Fin.append x.fst y.fst,
                  ⟨x.snd.base * y.snd.base,
                    x.snd.pending + y.snd.pending⟩)
                    : GenRow T (BoolFunc X) _)) from fun M => ?_]
      · rw [Multiset.map_map, ← ih₂ hq.2 d v]
        unfold genRandomWorld
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl (fun y _ => ?_)
        show GenRow.specializeTuple v (Fin.append x.fst y.fst) = _
        rw [specializeTuple_append', hspec x hx]
        rfl
      · rw [filter_map_comm]
        refine congrArg (Multiset.map _) (Multiset.filter_congr (fun y _ => ?_))
        show ((GenAnn.mk (x.snd.base * y.snd.base)
            (x.snd.pending + y.snd.pending)).finalize v = true) ↔ _
        rw [GenAnn.finalize_mul x.snd y.snd]
        show ((x.snd.finalize v && y.snd.finalize v) = true) ↔ _
        rw [Bool.and_eq_true]
        exact ⟨fun h => h.2, fun h => ⟨hfx, h⟩⟩
    · rw [ite_eq_right hfx]
      refine Multiset.eq_zero_of_forall_notMem (fun z hz => ?_)
      obtain ⟨w, hw, -⟩ := Multiset.mem_map.mp hz
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_mem_filter hw)
      have hfin := (Multiset.of_mem_filter hw)
      refine hfx ?_
      have := (Bool.and_eq_true _ _).mp
        ((congrArg (fun α : BoolFunc X => α v = true)
          (GenAnn.finalize_mul x.snd y.snd)) ▸ hfin)
      exact this.1
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_add, ih₁ hq.1 d v, ih₂ hq.2 d v]
  | Dedup q ih =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_ofAnnotated, randomWorld_groupByKey,
      genRandomWorld_allReg, ih hq d v]
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_ofAnnotated]
    refine Eq.trans (muSum_map (h := _root_.randomWorld v)
      (randomWorld_add v)
      (stepP := fun Y => q₁.evaluatePlain ((d.randomWorld v).assign s Y) γ)
      (fun Y => by
        rw [genRandomWorld_allReg]
        exact ih₁ hq.2 (d.assign s Y) v) b _) ?_
    rw [genRandomWorld_allReg, ih₀ hq.1 d v]
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_ofAnnotated]
    refine muIter_map (h := _root_.randomWorld v) rfl
      (stepP := fun Y => (q₀.evaluatePlain ((d.randomWorld v).assign s Y) γ
        + q₁.evaluatePlain ((d.randomWorld v).assign s Y) γ).dedup)
      (fun Y => ?_) b
    show _root_.randomWorld v (AnnotatedRelation.dedupAnn (_ + _)) = _
    rw [AnnotatedRelation.dedupAnn, randomWorld_groupByKey, randomWorld_add,
      genRandomWorld_allReg, genRandomWorld_allReg, ih₀ hq.1 (d.assign s Y) v,
      ih₁ hq.2 (d.assign s Y) v]
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    refine Eq.trans (genRandomWorld_ofAnnotated _ v)
      (Eq.trans (randomWorld_monus
        ((q₁.evaluate d γ).map GenRow.toAnnotated)
        ((q₂.evaluate d γ).map GenRow.toAnnotated) v) ?_)
    rw [genRandomWorld_allReg, genRandomWorld_allReg, ih₁ hq.1 d v, ih₂ hq.2 d v]
  | @GammaScalar cI m n₂ ts fs q ih =>
    -- one row on each side, kept in every world, its tokens specializing to
    -- the aggregates over the realized rows
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [← ih hq d v, ← genRandomWorld_allReg q d v]
    unfold genRandomWorld
    rw [show Multiset.filter
          (fun r : GenRow T (BoolFunc X) n₂ => r.snd.finalize v = true)
          {(⟨fun j => Sum.inr (AggValue.ofScalarGroup (fs j) (ts j)
              (Having.havingGroup (fun i : Fin 0 => i.elim0)
                ((q.evaluate d γ).map GenRow.toAnnotated)
                (fun i : Fin 0 => i.elim0)) γ), ⟨1, 0⟩⟩
            : GenRow T (BoolFunc X) n₂)}
        = {(⟨fun j => Sum.inr (AggValue.ofScalarGroup (fs j) (ts j)
              (Having.havingGroup (fun i : Fin 0 => i.elim0)
                ((q.evaluate d γ).map GenRow.toAnnotated)
                (fun i : Fin 0 => i.elim0)) γ), ⟨1, 0⟩⟩
            : GenRow T (BoolFunc X) n₂)}
        from Multiset.filter_eq_self.mpr (fun r hr => by
          rw [Multiset.mem_singleton] at hr; subst hr; rfl)]
    rw [Multiset.map_singleton]
    exact congrArg (fun u => (Multiset.ofList [u] : Multiset (Tuple T n₂)))
      (funext fun j => specialize_ofGroup _
        ((q.evaluate d γ).map GenRow.toAnnotated) _ (fs j) (ts j) v)
  | @Gamma cI m n₁ n₂ is ts fs q ih =>
    intro hq d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [← ih hq d v, ← genRandomWorld_allReg q d v]
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map]
    rw [Multiset.filter_congr (fun kv (_ : kv ∈ Multiset.ofList
        (groupByKey (((q.evaluate d γ).map GenRow.toAnnotated).map (fun p =>
          ((fun k => p.fst (is k), p.snd)
            : AnnotatedTuple T (BoolFunc X) n₁)))).val) =>
      show (⟨1, {(Having.havingGroup is
            ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map Prod.snd}⟩
          : GenAnn (BoolFunc X)).finalize v = true
        ↔ annGuard ((Having.havingGroup is
            ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map
              Prod.snd) v
        from Iff.trans (GenAnn.finalize_eval_iff
            ⟨1, {(Having.havingGroup is
              ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map
                Prod.snd}⟩ v)
          ⟨fun h => h.2 _ (Multiset.mem_singleton_self _),
           fun h => ⟨rfl, fun l hl => (Multiset.mem_singleton.mp hl) ▸ h⟩⟩)]
    -- key multisets: the realized keys are the realized world's keys
    have hkeys : (((randomWorld v
          ((q.evaluate d γ).map GenRow.toAnnotated)).map
            (fun u => (fun k => u (is k) : Tuple T n₁))).dedup : Multiset _)
        = Multiset.map Prod.fst
          (Multiset.filter (fun kv : AnnotatedTuple T (BoolFunc X) n₁ =>
            annGuard ((Having.havingGroup is
              ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map
                Prod.snd) v)
            (Multiset.ofList (groupByKey
              (((q.evaluate d γ).map GenRow.toAnnotated).map (fun p =>
                ((fun k => p.fst (is k), p.snd)
                  : AnnotatedTuple T (BoolFunc X) n₁)))).val)) := by
      have hRnodup : (Multiset.map Prod.fst
          (Multiset.filter (fun kv : AnnotatedTuple T (BoolFunc X) n₁ =>
            annGuard ((Having.havingGroup is
              ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map
                Prod.snd) v)
            (Multiset.ofList (groupByKey
              (((q.evaluate d γ).map GenRow.toAnnotated).map (fun p =>
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
            (((q.evaluate d γ).map GenRow.toAnnotated).map (fun p =>
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
    exact specialize_ofGroup is ((q.evaluate d γ).map GenRow.toAnnotated)
      kv.fst (fs j) (ts j) v
  | ProvSum is his t q ih =>
    intro hq
    exact hq.elim
  | GammaTok is his ts fs a q ih =>
    intro hq
    exact hq.elim
  | @Win cI nI mI pI P O o w t f q dist ih =>
    -- one output row per realized input row; the token specializes to the
    -- aggregate the realized world gives the row, because restricting the
    -- relation restricts every frame
    intro hq d v γ
    rw [AggQueryIn.evaluate_Win_eq, AggQueryIn.evaluatePlain_Win_eq, ← ih hq d v,
      ← genRandomWorld_allReg q d v]
    unfold genRandomWorld randomWorld
    rw [filter_map_comm, Multiset.map_map, Multiset.map_map,
      Multiset.filter_congr (fun x (_ : x ∈ q.evaluateAnnotated d γ) =>
        show (ValueFrame.windowRow P O o w t f
              (q.evaluateAnnotated d γ) x γ dist).snd.finalize v = true
          ↔ x.snd v = true from by
          simp [ValueFrame.windowRow])]
    refine Multiset.map_congr rfl (fun x hx => ?_)
    obtain ⟨hxR, hxc⟩ := Multiset.mem_filter.mp hx
    simp only [Function.comp_apply, ValueFrame.windowRow]
    funext k
    unfold GenRow.specializeTuple
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact tokenOfDist_specialize P O o w t f dist
        (q.evaluateAnnotated d γ) hxR v hxc
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl
  | Retag h q ih =>
    intro hq d v γ
    exact ih hq d v

/-! ## Unrestricted probabilistic query evaluation (PQE) -/

/-- The Boolean provenance of a general query: the `⊕`-sum of the
finalized annotations of its rows – true in a world iff some row is
realized. -/
noncomputable def AggQueryIn.booleanProv {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ)
    (d : AnnotatedDatabase T (BoolFunc X)) : BoolFunc X :=
  ((q.evaluate d).map (fun r => r.snd.finalize)).sum

/-- **Pointwise PQE bridge, general form**: the Boolean provenance of a
general query is true in a world iff the plain evaluation of that world
is non-empty. Immediate from the random-world commutation. -/
theorem AggQueryIn.booleanProv_eval_iff {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool) :
    (q.booleanProv d) v = true
      ↔ q.evaluatePlain (d.randomWorld v) ≠ 0 := by
  unfold AggQueryIn.booleanProv
  rw [multiset_sum_eval, ← AggQueryIn.genRandomWorld_evaluate q hq d v]
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
noncomputable def AggQueryIn.booleanProb {n : ℕ} {κ : Fin n → ColKind}
    (P : ProbAssignment X) (q : AggQuery T n κ)
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
theorem AggQueryIn.boolean_pqe {n : ℕ} {κ : Fin n → ColKind}
    (P : ProbAssignment X) (q : AggQuery T n κ) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) :
    AggQueryIn.booleanProb P q d = P.funcProb (q.booleanProv d) := by
  unfold AggQueryIn.booleanProb ProbAssignment.funcProb
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : q.evaluatePlain (d.randomWorld v) = 0
  · rw [ite_eq_left (Multiset.card_eq_zero.mpr h),
      ite_eq_right (fun hf => (AggQueryIn.booleanProv_eval_iff q hq d v).mp hf h)]
  · rw [ite_eq_right (fun hc => h (Multiset.card_eq_zero.mp hc)),
      ite_eq_left ((AggQueryIn.booleanProv_eval_iff q hq d v).mpr h)]

/-- The provenance of a tuple `t` in a general query with all-regular
output: the `⊕`-sum of the finalized annotations of the rows whose data
part is `t`. -/
noncomputable def AggQueryIn.tupleProv {n : ℕ}
    (q : AggQuery T n (ColKind.allReg n))
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) : BoolFunc X :=
  (((q.evaluate d).filter
    (fun r => GenRow.plainTuple r.fst = t)).map
      (fun r => r.snd.finalize)).sum

/-- **Pointwise tuple-marginal bridge**: the provenance of `t` is true in
a world iff `t` belongs to the plain evaluation of that world. -/
theorem AggQueryIn.tupleProv_eval_iff {n : ℕ}
    (q : AggQuery T n (ColKind.allReg n)) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) (v : X → Bool) :
    (q.tupleProv d t) v = true
      ↔ t ∈ q.evaluatePlain (d.randomWorld v) := by
  unfold AggQueryIn.tupleProv
  rw [multiset_sum_eval, ← AggQueryIn.genRandomWorld_evaluate q hq d v]
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
      (AggQueryIn.evaluate_conform q d r hrR k)
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
      (AggQueryIn.evaluate_conform q d r hrR k)
    unfold GenRow.specializeTuple GenRow.plainTuple
    rw [hw]
    rfl

/-- The marginal probability that `t` belongs to a random world's
answer. -/
noncomputable def AggQueryIn.tupleProb {n : ℕ} (P : ProbAssignment X)
    (q : AggQuery T n (ColKind.allReg n))
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) : ℚ :=
  ∑ v : X → Bool,
    if t ∈ q.evaluatePlain (d.randomWorld v) then P.valProb v else 0

/-- **Unrestricted tuple-marginal PQE**: for a general query with
all-regular output over a tuple-independent probabilistic database, the
marginal probability of an answer tuple is the probability of its
provenance. This is the general-evaluator counterpart of the classical
intensional-PQE theorem `ProbAssignment.theorem_12`, with aggregate
comparisons allowed anywhere in the query. -/
theorem AggQueryIn.tuple_pqe {n : ℕ} (P : ProbAssignment X)
    (q : AggQuery T n (ColKind.allReg n)) (hq : q.noProvSum)
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) :
    AggQueryIn.tupleProb P q d t = P.funcProb (q.tupleProv d t) := by
  unfold AggQueryIn.tupleProb ProbAssignment.funcProb
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : t ∈ q.evaluatePlain (d.randomWorld v)
  · rw [ite_eq_left h, ite_eq_left ((AggQueryIn.tupleProv_eval_iff q hq d t v).mpr h)]
  · rw [ite_eq_right h,
      ite_eq_right (fun hf => h ((AggQueryIn.tupleProv_eval_iff q hq d t v).mp hf))]
