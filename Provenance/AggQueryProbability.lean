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

/-- **Whether an aggregate column's group is realized** under a
valuation – what guardedness asserts of every grouped column of a row.
On an ordinary token that is a realized occurrence, unless the token is
scalar; on a nested value and on an expression it is that the
occurrences the valuation keeps are a world of it, which exempts a
scalar reading in the same way. -/
def _root_.AggTok.Realized (v : X → Bool) : AggTok T (BoolFunc X) → Prop
  | .tok a => a.scalar = true ∨ (a.realized v).Nonempty
  | .nest a => (a.realizedWorld (fun α => α v)).IsWorld a
  | .expr e => e.IsWorld (e.realizedWorld (fun α => α v))

omit [ValueType T] [Fintype X] [DecidableEq X] in
@[simp] theorem _root_.AggTok.Realized_tok (a : AggValue T (BoolFunc X))
    (v : X → Bool) :
    (AggTok.tok a).Realized v ↔ (a.scalar = true ∨ (a.realized v).Nonempty) :=
  Iff.rfl

omit [ValueType T] [Fintype X] [DecidableEq X] in
@[simp] theorem _root_.AggTok.Realized_nest (a : NestedValue T (BoolFunc X))
    (v : X → Bool) :
    (AggTok.nest a).Realized v
      ↔ (a.realizedWorld (fun α => α v)).IsWorld a :=
  Iff.rfl

omit [ValueType T] [Fintype X] [DecidableEq X] in
@[simp] theorem _root_.AggTok.Realized_expr (e : AggExpr T (BoolFunc X))
    (v : X → Bool) :
    (AggTok.expr e).Realized v
      ↔ e.IsWorld (e.realizedWorld (fun α => α v)) :=
  Iff.rfl

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- **Reading a column through a function leaves its guard alone**: the
occurrences, the conventions and so the worlds are the ones it had. -/
@[simp] theorem _root_.AggTok.Realized_postcomp (gf : T → T)
    (x : AggTok T (BoolFunc X)) (v : X → Bool) :
    (x.postcomp gf).Realized v ↔ x.Realized v := by
  cases x <;> exact Iff.rfl

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

namespace AggExpr

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- The world-faithful reading of an expression under a valuation is its
reading in the world the valuation cuts out. -/
theorem specialize_eval (e : AggExpr T (BoolFunc X)) (v : X → Bool) :
    e.specialize (fun α => α v)
      = e.valOn (e.realizedWorld (fun α => α v)) := rfl

/-- **The PQE bridge for an aggregate expression.** Only one subfamily
has a realized annotation under a valuation – the occurrences the
valuation keeps – so the world sum is true exactly when that subfamily
is a world of the expression and the test holds of its value there. This
is `AggValue.predProvWith_eval_iff` with `IsWorld` in place of “the
group is non-empty if grouped”. -/
theorem predProvWith_eval_iff (e : AggExpr T (BoolFunc X)) (P : T → Kleene)
    (v : X → Bool) :
    (e.predProvWith P) v = true
      ↔ e.IsWorld (e.realizedWorld (fun α => α v))
        ∧ P (e.specialize (fun α => α v)) = Kleene.true := by
  unfold AggExpr.predProvWith
  rw [sum_eval_eq_true_iff]
  constructor
  · rintro ⟨W, hW, hWv⟩
    obtain ⟨-, hiw⟩ := Finset.mem_filter.mp hW
    have hsplit : ((Having.worldAnn e.anns W) v
        && (Having.chiOf (K := BoolFunc X) P (e.valOn W)) v) = true := hWv
    rw [Bool.and_eq_true] at hsplit
    have hWeq : W = e.realizedWorld (fun α => α v) :=
      (worldAnn_eval_iff e.anns W v).mp hsplit.1
    subst hWeq
    exact ⟨hiw, (chiOf_eval_iff P _ v).mp hsplit.2⟩
  · rintro ⟨hiw, hP⟩
    refine ⟨e.realizedWorld (fun α => α v),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiw⟩, ?_⟩
    have hgoal : ((Having.worldAnn e.anns
          (e.realizedWorld (fun α => α v))) v
        && (Having.chiOf (K := BoolFunc X) P
          (e.valOn (e.realizedWorld (fun α => α v)))) v) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(worldAnn_eval_iff e.anns _ v).mpr rfl,
        (chiOf_eval_iff P _ v).mpr hP⟩
    exact hgoal

end AggExpr

namespace NestedValue

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- The world-faithful reading of a nested value under a valuation is its
reading in the world the valuation cuts out. -/
theorem specialize_eval (a : NestedValue T (BoolFunc X)) (v : X → Bool) :
    a.specialize (fun α => α v)
      = a.valOn (a.realizedWorld (fun α => α v)) := rfl

omit [ValueType T] in
/-- **What it takes for a world of a nested value to hold under a
valuation**: every occurrence it keeps, outer or inner, has a true
annotation, and every one it drops has a false one. -/
theorem World.ann_eval_eq_true_iff (W : World T (BoolFunc X)) (v : X → Bool) :
    W.ann v = true
      ↔ ((∀ d ∈ W.occs, d.present = true → (d.occ.2) v = true)
          ∧ ∀ d ∈ W.occs, ∀ j ∈ d.sub, (d.occ.1.anns j) v = true)
        ∧ ((∀ d ∈ W.occs, d.present = false → (d.occ.2) v = false)
          ∧ ∀ d ∈ W.occs, ∀ j, j ∉ d.sub → (d.occ.1.anns j) v = false) := by
  have hkept : (W.occs.map
      (fun d => if d.present = true then d.occ.2 else 1)).prod v = true
      ↔ ∀ d ∈ W.occs, d.present = true → (d.occ.2) v = true := by
    rw [multiset_prod_eval_eq_true_iff]
    constructor
    · intro hall d hd hp
      have := hall _ (Multiset.mem_map_of_mem _ hd)
      rwa [ite_eq_left hp] at this
    · intro hall f hf
      rw [Multiset.mem_map] at hf
      obtain ⟨d, hd, rfl⟩ := hf
      by_cases hp : d.present = true
      · rw [ite_eq_left hp]
        exact hall d hd hp
      · rw [ite_eq_right hp]
        rfl
  have hinner : (W.occs.map
      (fun d => ∏ j ∈ d.sub, d.occ.1.anns j)).prod v = true
      ↔ ∀ d ∈ W.occs, ∀ j ∈ d.sub, (d.occ.1.anns j) v = true := by
    rw [multiset_prod_eval_eq_true_iff]
    constructor
    · intro hall d hd j hj
      exact (prod_eval_eq_true_iff _ _ v).mp
        (hall _ (Multiset.mem_map_of_mem _ hd)) j hj
    · intro hall f hf
      rw [Multiset.mem_map] at hf
      obtain ⟨d, hd, rfl⟩ := hf
      exact (prod_eval_eq_true_iff _ _ v).mpr (hall d hd)
  have hdrop : (W.occs.map
      (fun d => if d.present = true then 0 else d.occ.2)).sum v = false
      ↔ ∀ d ∈ W.occs, d.present = false → (d.occ.2) v = false := by
    rw [← Bool.not_eq_true, multiset_sum_eval_eq_true_iff]
    constructor
    · intro hnone d hd hp
      by_contra hcon
      refine hnone ⟨_, Multiset.mem_map_of_mem _ hd, ?_⟩
      rw [ite_eq_right (by rw [hp]; exact Bool.false_ne_true)]
      exact Bool.eq_true_of_ne_false hcon
    · rintro hall ⟨f, hf, hfv⟩
      rw [Multiset.mem_map] at hf
      obtain ⟨d, hd, rfl⟩ := hf
      by_cases hp : d.present = true
      · rw [ite_eq_left hp] at hfv
        exact Bool.noConfusion hfv
      · rw [ite_eq_right hp] at hfv
        rw [hall d hd (Bool.not_eq_true _ |>.mp hp)] at hfv
        exact Bool.noConfusion hfv
  have hdropinner : (W.occs.map
      (fun d => ∑ j ∈ (d.sub)ᶜ, d.occ.1.anns j)).sum v = false
      ↔ ∀ d ∈ W.occs, ∀ j, j ∉ d.sub → (d.occ.1.anns j) v = false := by
    rw [← Bool.not_eq_true, multiset_sum_eval_eq_true_iff]
    constructor
    · intro hnone d hd j hj
      by_contra hcon
      refine hnone ⟨_, Multiset.mem_map_of_mem _ hd, ?_⟩
      exact (sum_eval_eq_true_iff _ _ v).mpr
        ⟨j, Finset.mem_compl.mpr hj, Bool.eq_true_of_ne_false hcon⟩
    · rintro hall ⟨f, hf, hfv⟩
      rw [Multiset.mem_map] at hf
      obtain ⟨d, hd, rfl⟩ := hf
      obtain ⟨j, hj, hjv⟩ := (sum_eval_eq_true_iff _ _ v).mp hfv
      rw [hall d hd j (Finset.mem_compl.mp hj)] at hjv
      exact Bool.noConfusion hjv
  have hv : ∀ x y z w : BoolFunc X, ((x * y) * (1 - (z + w))) v = true
      ↔ (x v = true ∧ y v = true) ∧ (z v = false ∧ w v = false) := by
    intro x y z w
    show ((x v && y v) && !(z v || w v)) = true ↔ _
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_false_iff]
  rw [World.ann, World.presentProd, World.absentSum, hv, hkept, hinner,
    hdrop, hdropinner]

omit [ValueType T] in
/-- **Only the realized world holds**: over `𝔹[X]` a world of a nested
value is annotated true under a valuation exactly when it is the world
the valuation cuts out – which is what makes the world sum a reading of
one world. -/
theorem World.ann_eval_iff {a : NestedValue T (BoolFunc X)}
    {W : World T (BoolFunc X)} (hW : W.IsWorldOf a) (v : X → Bool) :
    W.ann v = true ↔ W = a.realizedWorld (fun α => α v) := by
  rw [World.ann_eval_eq_true_iff]
  constructor
  · rintro ⟨⟨hkp, hki⟩, hdp, hdi⟩
    have hreal : ∀ d ∈ W.occs, d = realizedOcc (fun α => α v) d.occ := by
      intro d hd
      obtain ⟨o, p, S⟩ := d
      have hp : p = (o.2) v := by
        by_cases hpt : p = true
        · rw [hpt, hkp _ hd hpt]
        · rw [Bool.not_eq_true] at hpt
          rw [hpt, hdp _ hd hpt]
      have hS : S = Finset.univ.filter (fun j => (o.1.anns j) v = true) := by
        ext j
        rw [Finset.mem_filter, and_iff_right (Finset.mem_univ j)]
        constructor
        · exact fun hj => hki _ hd j hj
        · intro hj
          by_contra hjn
          rw [hdi _ hd j hjn] at hj
          exact Bool.noConfusion hj
      show (⟨o, p, S⟩ : WorldOcc T (BoolFunc X)) = ⟨o, _, _⟩
      rw [hp, hS]
    show W = ⟨a.occs.map (realizedOcc (fun α => α v))⟩
    refine congrArg World.mk ?_
    calc W.occs = W.occs.map (fun d => d) := (Multiset.map_id' W.occs).symm
      _ = W.occs.map (fun d => realizedOcc (fun α => α v) d.occ) :=
          Multiset.map_congr rfl hreal
      _ = a.occs.map (realizedOcc (fun α => α v)) := by
          rw [show (fun d : WorldOcc T (BoolFunc X) =>
                realizedOcc (fun α => α v) d.occ)
              = (realizedOcc (fun α => α v)) ∘ WorldOcc.occ from rfl,
            ← Multiset.map_map]
          exact congrArg _ hW
  · rintro rfl
    have hmem : ∀ d ∈ (a.realizedWorld (fun α => α v)).occs,
        ∃ o ∈ a.occs, realizedOcc (fun α => α v) o = d := by
      intro d hd
      have hd' : d ∈ a.occs.map (realizedOcc (fun α => α v)) := hd
      rw [Multiset.mem_map] at hd'
      exact hd'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro d hd hp
      obtain ⟨o, -, rfl⟩ := hmem d hd
      exact hp
    · intro d hd j hj
      obtain ⟨o, -, rfl⟩ := hmem d hd
      exact (Finset.mem_filter.mp hj).2
    · intro d hd hp
      obtain ⟨o, -, rfl⟩ := hmem d hd
      exact hp
    · intro d hd j hj
      obtain ⟨o, -, rfl⟩ := hmem d hd
      have hno : ¬ (o.1.anns j) v = true := fun hcon =>
        hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcon⟩)
      exact Bool.not_eq_true _ |>.mp hno

/-- **The PQE bridge for a nested value**: only the realized world is
annotated true, so the world sum holds under a valuation exactly when
that world is a world of the value and the test holds of its reading
there. This is `AggExpr.predProvWith_eval_iff` over the bag of
occurrences. -/
theorem predProvWith_eval_iff (a : NestedValue T (BoolFunc X))
    (P : T → Kleene) (v : X → Bool) :
    (a.predProvWith P) v = true
      ↔ (a.realizedWorld (fun α => α v)).IsWorld a
        ∧ P (a.specialize (fun α => α v)) = Kleene.true := by
  unfold NestedValue.predProvWith
  rw [multiset_sum_eval_eq_true_iff]
  constructor
  · rintro ⟨f, hf, hfv⟩
    rw [Multiset.mem_map] at hf
    obtain ⟨W, hW, rfl⟩ := hf
    obtain ⟨hmem, hiw⟩ := Multiset.mem_filter.mp hW
    have hsplit : (W.ann v
        && (Having.chiOf (K := BoolFunc X) P (a.valOn W)) v) = true := hfv
    rw [Bool.and_eq_true] at hsplit
    have hWeq : W = a.realizedWorld (fun α => α v) :=
      (World.ann_eval_iff (isWorldOf_of_mem_worlds hmem) v).mp hsplit.1
    subst hWeq
    exact ⟨hiw, (chiOf_eval_iff P _ v).mp hsplit.2⟩
  · rintro ⟨hiw, hP⟩
    refine ⟨_, Multiset.mem_map_of_mem _ (Multiset.mem_filter.mpr
      ⟨mem_worlds_iff.mpr (isWorldOf_realizedWorld a _), hiw⟩), ?_⟩
    have hgoal : ((a.realizedWorld (fun α => α v)).ann v
        && (Having.chiOf (K := BoolFunc X) P
          (a.valOn (a.realizedWorld (fun α => α v)))) v) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(World.ann_eval_iff (isWorldOf_realizedWorld a _) v).mpr rfl,
        (chiOf_eval_iff P _ v).mpr hP⟩
    exact hgoal

omit [Fintype X] [DecidableEq X] in
/-- **The reading a valuation gives a nested value is one of its
values**, as soon as the world it cuts out is a world of it. -/
theorem specialize_mem_vals (a : NestedValue T (BoolFunc X)) (v : X → Bool)
    (hr : (a.realizedWorld (fun α => α v)).IsWorld a) :
    a.specialize (fun α => α v) ∈ a.vals := by
  rw [vals, Multiset.mem_toFinset, Multiset.mem_map]
  exact ⟨a.realizedWorld (fun α => α v),
    Multiset.mem_filter.mpr
      ⟨mem_worlds_iff.mpr (isWorldOf_realizedWorld a _), hr⟩, rfl⟩

end NestedValue

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

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- **A realized occurrence of the family is a non-empty realized
world.** This is what makes a filtered aggregate of a group guarded: its
family is the whole group, so the group's existence guard gives it an
occurrence the valuation keeps. -/
theorem AggExpr.realizedWorld_nonempty_of_annGuard
    (e : AggExpr T (BoolFunc X)) (v : X → Bool)
    (hG : annGuard e.annList v) :
    (e.realizedWorld (fun α => α v)).Nonempty := by
  obtain ⟨α, hmem, hα⟩ := hG
  have hlen : e.annList.length = e.occs.length := List.length_map _
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  refine ⟨Fin.cast hlen i, ?_⟩
  rw [AggExpr.realizedWorld, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hann : e.anns (Fin.cast hlen i) = α := by
    rw [← hi]
    show (e.occs.get (Fin.cast hlen i)).snd.fst = e.annList.get i
    simp only [AggExpr.annList, List.get_eq_getElem, List.getElem_map,
      Fin.val_cast]
  rw [hann]
  exact hα

/-- **An expression whose test is realized has a realized occurrence.**
Not read in the scalar convention, some leaf of it is grouped, and a
world of the expression meets that leaf's occurrences – so the family
carries a realized annotation, which is the group's existence guard.
This is `AggValue.annGuard_iff_realized`'s forward use for an
expression column. -/
theorem AggExpr.annGuard_of_predProvWith (e : AggExpr T (BoolFunc X))
    (hsc : e.isScalar = false) (P : T → Kleene) (v : X → Bool)
    (hp : (e.predProvWith P) v = true) : annGuard e.annList v := by
  obtain ⟨hiw, -⟩ := (AggExpr.predProvWith_eval_iff e P v).mp hp
  obtain ⟨l, hl⟩ := AggExpr.exists_grouped_of_not_isScalar hsc
  obtain ⟨i, hi⟩ := hiw l hl
  obtain ⟨hiR, -⟩ := Finset.mem_inter.mp hi
  refine ⟨e.anns i, ?_, ?_⟩
  · show e.anns i ∈ e.occs.map (fun o => o.snd.fst)
    exact List.mem_map.mpr ⟨e.occs.get i, List.get_mem _ _, rfl⟩
  · exact (Finset.mem_filter.mp hiR).2

/-- **A nested value whose test is realized has a realized
occurrence.** Not read in the scalar convention, the world the valuation
cuts out keeps an occurrence, whose annotation is therefore realized –
and that is the family's existence guard, which for a nested value is the
one annotation its bag sums to. -/
theorem NestedValue.annGuard_of_predProvWith (a : NestedValue T (BoolFunc X))
    (hsc : a.scalar = false) (P : T → Kleene) (v : X → Bool)
    (hp : (a.predProvWith P) v = true) :
    annGuard [(a.occs.map Prod.snd).sum] v := by
  obtain ⟨hiw, -⟩ := (NestedValue.predProvWith_eval_iff a P v).mp hp
  refine ⟨(a.occs.map Prod.snd).sum, List.mem_singleton_self _, ?_⟩
  rcases hiw.1 with hs | hs
  · exact absurd (hsc.symm.trans hs) Bool.false_ne_true
  · obtain ⟨d, hd⟩ := Multiset.card_pos_iff_exists_mem.mp hs
    have hpres : d.present = true := (Multiset.mem_filter.mp hd).2
    have hdocc : d ∈ (a.realizedWorld (fun α => α v)).occs :=
      Multiset.mem_of_mem_filter hd
    have hdocc' : d ∈ a.occs.map (NestedValue.realizedOcc (fun α => α v)) :=
      hdocc
    rw [Multiset.mem_map] at hdocc'
    obtain ⟨o, ho, rfl⟩ := hdocc'
    exact multiset_sum_eval_eq_true_iff _ v |>.mpr
      ⟨o.2, Multiset.mem_map_of_mem _ ho, hpres⟩

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
def GenPredIn.selCompared {K' : Type} [AddCommMonoid K'] {c n : ℕ}
    {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (u : Tuple (GenValue T K') n) :
    Multiset (List K') :=
  φ.comparedCols.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => some a.annList)

/-- The compared tokens read in the scalar convention. A comparison against
one of these entails no group's existence – it holds in the empty world – so
its presence blocks the supersede whatever occurrences it carries. -/
def GenPredIn.selComparedScalar {K' : Type} [AddCommMonoid K'] {c n : ℕ}
    {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (u : Tuple (GenValue T K') n) :
    Multiset (List K') :=
  φ.comparedCols.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => if a.scalar then some a.annList else none)

/-- The pending factors after a σ with aggregate atoms (the evaluator's
update, definitionally). -/
def GenPredIn.selPending {K' : Type} [AddCommMonoid K'] [DecidableEq K']
    {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
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
    (hg : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T (BoolFunc X),
      u k = Sum.inr a → a.Realized v) :
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
    obtain ⟨x, hx⟩ := GenValue.eq_inr_of_kindOf_agg
      ((hconf k).trans (by rw [h]; rfl))
    have hne' := hg k (Finset.mem_singleton_self k) x hx
    cases x with
    | tok a =>
      have ha := hx
      have hne : a.scalar = true ∨ (a.realized v).Nonempty := hne'
      simp only [GenPredIn.predsem, ha, AggTok.predProvOf,
        AggTok.predProvOfWith_tok]
      rw [AggValue.predProvOfWith_eval_iff, GenPredIn.evalPlain3]
      have hspec : GenRow.specializeTuple v u k
          = a.specialize (fun α => α v) := by
        unfold GenRow.specializeTuple
        rw [ha]
        rfl
      rw [hspec, ← TermGIn.eval_specialize t u hconf v]
      cases neg with
      | false => simp [hne]
      | true => simp [hne, CompOp.negate_eval3]
    | nest a =>
      have ha := hx
      have hne : (a.realizedWorld (fun α => α v)).IsWorld a := hne'
      simp only [GenPredIn.predsem, ha, AggTok.predProvOf,
        AggTok.predProvOfWith]
      rw [NestedValue.predProvWith_eval_iff, GenPredIn.evalPlain3]
      have hspec : GenRow.specializeTuple v u k
          = a.specialize (fun α => α v) := by
        unfold GenRow.specializeTuple
        rw [ha]
        rfl
      rw [hspec, ← TermGIn.eval_specialize t u hconf v]
      cases neg with
      | false => simp [hne]
      | true => simp [hne, CompOp.negate_eval3]
    | expr e =>
      have ha := hx
      have hne : e.IsWorld (e.realizedWorld (fun α => α v)) := hne'
      simp only [GenPredIn.predsem, ha, AggTok.predProvOf,
        AggTok.predProvOfWith_expr]
      rw [AggExpr.predProvWith_eval_iff, GenPredIn.evalPlain3]
      have hspec : GenRow.specializeTuple v u k
          = e.specialize (fun α => α v) := by
        unfold GenRow.specializeTuple
        rw [ha]
        rfl
      rw [hspec, ← TermGIn.eval_specialize t u hconf v]
      cases neg with
      | false => simp [hne]
      | true => simp [hne, CompOp.negate_eval3]
  | aggRange k h op₁ t₁ op₂ t₂ =>
    obtain ⟨x, hx⟩ := GenValue.eq_inr_of_kindOf_agg
      ((hconf k).trans (by rw [h]; rfl))
    have hne' := hg k (Finset.mem_singleton_self k) x hx
    cases x with
    | tok a =>
      have ha := hx
      have hne : a.scalar = true ∨ (a.realized v).Nonempty := hne'
      simp only [GenPredIn.predsem, ha, AggTok.predProvOfWith_tok]
      rw [AggValue.predProvOfWith_eval_iff, GenPredIn.evalPlain3]
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
    | nest a =>
      have ha := hx
      have hne : (a.realizedWorld (fun α => α v)).IsWorld a := hne'
      simp only [GenPredIn.predsem, ha, AggTok.predProvOfWith]
      rw [NestedValue.predProvWith_eval_iff, GenPredIn.evalPlain3]
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
    | expr e =>
      have ha := hx
      have hne : e.IsWorld (e.realizedWorld (fun α => α v)) := hne'
      simp only [GenPredIn.predsem, ha, AggTok.predProvOfWith_expr]
      rw [AggExpr.predProvWith_eval_iff, GenPredIn.evalPlain3]
      have hspec : GenRow.specializeTuple v u k
          = e.specialize (fun α => α v) := by
        unfold GenRow.specializeTuple
        rw [ha]
        rfl
      rw [hspec, ← TermGIn.eval_specialize t₁ u hconf v,
        ← TermGIn.eval_specialize t₂ u hconf v]
      cases neg with
      | false => simp [hne]
      | true => simp [hne]
  | and φ ψ ihφ ihψ =>
    have hgφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.Realized v :=
      fun k hk => hg k (Finset.mem_union_left _ hk)
    have hgψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.Realized v :=
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
    have hgφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.Realized v :=
      fun k hk => hg k (Finset.mem_union_left _ hk)
    have hgψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.Realized v :=
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
    (huni : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T (BoolFunc X),
      u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀)
    (hent : φ.entailsExistence neg = true)
    (hp : (φ.predsem neg u γ) v = true) : annGuard ℓ₀ v := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ => exact absurd hent (by simp [GenPredIn.entailsExistence])
  | aggCmp k h op t =>
    cases hu : u k with
    | inl w =>
      simp only [GenPredIn.predsem, hu] at hp
      exact absurd hp Bool.false_ne_true
    | inr x =>
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) x hu
      cases x with
      | tok a =>
        simp only [AggTok.scalar_tok] at hsc
        simp only [AggTok.annList_tok] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOf_tok] at hp
        rw [AggValue.predProvOf_of_grouped hsc] at hp
        have hne := (AggValue.predProv_eval_iff a _ _ v).mp hp |>.1
        rw [← heq]
        exact (AggValue.annGuard_iff_realized a v).mpr hne
      | nest a =>
        simp only [AggTok.scalar_nest] at hsc
        simp only [AggTok.annList_nest] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOf,
          AggTok.predProvOfWith] at hp
        rw [← heq]
        exact NestedValue.annGuard_of_predProvWith a hsc _ v hp
      | expr e =>
        simp only [AggTok.scalar_expr] at hsc
        simp only [AggTok.annList_expr] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOf,
          AggTok.predProvOfWith_expr] at hp
        rw [← heq]
        exact AggExpr.annGuard_of_predProvWith e hsc _ v hp
  | aggRange k h op₁ t₁ op₂ t₂ =>
    cases hu : u k with
    | inl w =>
      simp only [GenPredIn.predsem, hu] at hp
      exact absurd hp Bool.false_ne_true
    | inr x =>
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) x hu
      cases x with
      | tok a =>
        simp only [AggTok.scalar_tok] at hsc
        simp only [AggTok.annList_tok] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith_tok] at hp
        have hne := (AggValue.predProvOfWith_eval_iff a _ v).mp hp |>.1
        rw [← heq]
        exact (AggValue.annGuard_iff_realized a v).mpr
          (hne.resolve_left (by rw [hsc]; exact Bool.false_ne_true))
      | nest a =>
        simp only [AggTok.scalar_nest] at hsc
        simp only [AggTok.annList_nest] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith] at hp
        rw [← heq]
        exact NestedValue.annGuard_of_predProvWith a hsc _ v hp
      | expr e =>
        simp only [AggTok.scalar_expr] at hsc
        simp only [AggTok.annList_expr] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith_expr] at hp
        rw [← heq]
        exact AggExpr.annGuard_of_predProvWith e hsc _ v hp
  | and φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
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
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T (BoolFunc X),
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
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
        have hmem : a.annList ∈ φ.selComparedScalar u :=
          (Multiset.mem_filterMap _ _).mpr
            ⟨k, Finset.mem_val.mpr hk, by simp [ha, hsc]⟩
        rw [hcond.1] at hmem
        exact absurd hmem (Multiset.notMem_zero _)
      · refine hcond.2.2 _ ?_
        have hmem : a.annList ∈ φ.selCompared u :=
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
      ∀ (k : Fin n) (a : AggTok T (BoolFunc X)), u k = Sum.inr a →
        a.Realized v) :
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

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- Dropping a middle factor of a `𝔹[X]` product keeps it realized. -/
private lemma mul_mul_eval_iff (x y z : BoolFunc X) (v : X → Bool)
    (h : (x * z) v = true) : ((x * y) * z) v = true ↔ y v = true := by
  have h' : (x v && z v) = true := h
  simp only [Bool.and_eq_true] at h'
  show ((x v && y v) && z v) = true ↔ _
  simp [h'.1, h'.2]

omit [ValueType T] [Fintype X] [DecidableEq X] in
private lemma mul_mul_eval_drop (x y z : BoolFunc X) (v : X → Bool)
    (h : ((x * y) * z) v = true) : (x * z) v = true := by
  have h' : ((x v && y v) && z v) = true := h
  show (x v && z v) = true
  simp only [Bool.and_eq_true] at h' ⊢
  exact ⟨h'.1.1, h'.2⟩

omit [Fintype X] [DecidableEq X] in
/-- **The column a projection reads is realized where the row is**: a
term reads no token at all, and the two token cases read a column of the
row itself – through a function in the second, which
`AggTok.Realized_postcomp` carries. -/
theorem ProjColIn.realized_eval {c n : ℕ} {κ : Fin n → ColKind}
    (p : ProjColIn T c κ) (u : Tuple (GenValue T (BoolFunc X)) n)
    {γ : Fin c → T} (v : X → Bool)
    (hrow : ∀ (k : Fin n) (a : AggTok T (BoolFunc X)),
      u k = Sum.inr a → a.Realized v)
    {a : AggTok T (BoolFunc X)} (ha : p.eval u γ = Sum.inr a) :
    a.Realized v := by
  cases p with
  | term t => exact absurd ha (by simp [ProjColIn.eval])
  | provTerm t => exact absurd ha (by simp [ProjColIn.eval])
  | token k hk =>
    refine hrow k a ?_
    rw [← ha]
    rfl
  | aggTerm k hk gf =>
    cases hu : u k with
    | inl w => exact absurd ha (by simp [ProjColIn.eval, hu])
    | inr x =>
      have hax : a = x.postcomp gf := by
        have := ha
        simp only [ProjColIn.eval, hu, Sum.map_inr] at this
        exact (Sum.inr.inj this).symm
      rw [hax, AggTok.Realized_postcomp]
      exact hrow k x hu

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- **The world a valuation cuts out of an embedded token is the one it
cuts out of the token.** -/
theorem AggExpr.realizedWorld_ofValue (a : AggValue T (BoolFunc X))
    (v : X → Bool) :
    (AggExpr.ofValue a).realizedWorld (fun α => α v)
      = (a.realized v).map
        (finCongr (AggExpr.length_ofValue_occs a)).toEmbedding := by
  ext j
  rw [Finset.mem_map_equiv, AggExpr.realizedWorld, Finset.mem_filter,
    and_iff_right (Finset.mem_univ j), AggValue.realized, Finset.mem_filter,
    and_iff_right (Finset.mem_univ _)]
  show (AggExpr.ofValue a).anns j v = true
    ↔ a.anns (finCongr (AggExpr.length_ofValue_occs a).symm j) v = true
  rw [show (AggExpr.ofValue a).anns j
      = a.anns (finCongr (AggExpr.length_ofValue_occs a).symm j) from by
    rw [← AggExpr.anns_ofValue a (finCongr
      (AggExpr.length_ofValue_occs a).symm j)]
    rfl]

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- **An embedded token specializes as the token does.** -/
theorem AggExpr.specialize_ofValue (a : AggValue T (BoolFunc X))
    (v : X → Bool) :
    (AggExpr.ofValue a).specialize (fun α => α v)
      = a.specialize (fun α => α v) := by
  rw [AggExpr.specialize, AggExpr.realizedWorld_ofValue,
    AggExpr.valOn_ofValue, AggValue.specialize_eval]

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- **A reading that reads nothing returns its value**, whatever the
valuation. -/
theorem NestedValue.specialize_constInner (w : T) (v : X → Bool) :
    (NestedValue.constInner w : AggExpr T (BoolFunc X)).specialize
      (fun α => α v) = w := rfl

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- **A realized column's inner reading has the world the valuation cuts
out among its own.** On an expression that is what `AggTok.Realized`
says of it; on an ordinary token it is the token's realized occurrence,
through the embedding (`AggExpr.isWorld_ofValue`); and a reading that
reads nothing is scalar, so the empty world is one of its worlds. This
is the condition a world of the nested value owes each inner reading it
keeps. -/
theorem GenValue.realized_innerValue (x : GenValue T (BoolFunc X))
    (v : X → Bool)
    (hx : ∀ a : AggTok T (BoolFunc X), x = Sum.inr a → a.Realized v) :
    (GenValue.innerValue x).IsWorld
      ((GenValue.innerValue x).realizedWorld (fun α => α v)) := by
  have hconst : ∀ w : T,
      (NestedValue.constInner w : AggExpr T (BoolFunc X)).IsWorld
        ((NestedValue.constInner w : AggExpr T (BoolFunc X)).realizedWorld
          (fun α => α v)) := by
    intro w
    rw [show (NestedValue.constInner w
          : AggExpr T (BoolFunc X)).realizedWorld (fun α => α v) = ∅ from
      Finset.eq_empty_of_forall_notMem (fun j _ => absurd j.isLt (by
        simp [NestedValue.constInner, AggExpr.ofValue]))]
    exact (AggExpr.isWorld_empty_iff _).mpr (by
      rw [NestedValue.constInner, AggExpr.isScalar_ofValue])
  cases x with
  | inl w => exact hconst w
  | inr y =>
    cases y with
    | tok a =>
      show (AggExpr.ofValue a).IsWorld
        ((AggExpr.ofValue a).realizedWorld (fun α => α v))
      rw [AggExpr.realizedWorld_ofValue, AggExpr.isWorld_ofValue]
      exact hx (AggTok.tok a) rfl
    | nest b => exact hconst b.collapse
    | expr e => exact hx (AggTok.expr e) rfl

omit [Fintype X] [DecidableEq X] in
/-- **What a nested occurrence reads in the world a valuation cuts
out**: the inner reading of a projection column, read over the
occurrences the valuation keeps, is what the valuation makes of that
column. So an occurrence of a nested token reads what the realized row
reads there. A *nested* column is the one case this excludes – the
second storey is read through its collapse, which is the deterministic
reading and not the world one – and `GenRow.NoNested` rules it out. -/
theorem ProjColIn.specialize_innerValue {c n : ℕ} {κ : Fin n → ColKind}
    (p : ProjColIn T c κ) (u : Tuple (GenValue T (BoolFunc X)) n)
    {γ : Fin c → T} (hconf : ∀ k, GenValue.kindOf (u k) = (κ k).base)
    (hnn : GenRow.NoNested u) (v : X → Bool) :
    (GenValue.innerValue (p.eval u γ)).specialize (fun α => α v)
      = p.evalPlain (GenRow.specializeTuple v u) γ := by
  cases p with
  | term t =>
    show (NestedValue.constInner (t.eval u γ)).specialize _ = _
    rw [NestedValue.specialize_constInner]
    exact TermGIn.eval_specialize t u hconf v
  | provTerm t =>
    show (NestedValue.constInner (t.eval u γ)).specialize _ = _
    rw [NestedValue.specialize_constInner]
    exact TermGIn.eval_specialize t u hconf v
  | token k hk =>
    show (GenValue.innerValue (u k)).specialize _
      = GenValue.specializeAt v (u k)
    cases hu : u k with
    | inl w => exact NestedValue.specialize_constInner w v
    | inr x =>
      cases x with
      | tok a => exact AggExpr.specialize_ofValue a v
      | nest b => exact absurd (hnn k (AggTok.nest b) hu) (by simp)
      | expr e => rfl
  | aggTerm k hk gf =>
    show (GenValue.innerValue (Sum.map gf (AggTok.postcomp gf) (u k))).specialize
        (fun α => α v)
      = gf (GenValue.specializeAt v (u k))
    cases hu : u k with
    | inl w => exact NestedValue.specialize_constInner (gf w) v
    | inr x =>
      cases x with
      | tok a =>
        show (AggExpr.ofValue (AggValue.postcomp gf a)).specialize
            (fun α => α v) = _
        rw [AggExpr.specialize_ofValue]
        rfl
      | nest b => exact absurd (hnn k (AggTok.nest b) hu) (by simp)
      | expr e =>
        show (e.postcomp gf).specialize (fun α => α v) = _
        rw [AggExpr.specialize, AggExpr.valOn_postcomp]
        rfl

omit [ValueType T] [Fintype X] [DecidableEq X] in
/-- **A value column specializes to its collapse**: a valuation moves
only what a token reads, and a column that holds no token holds its
value. -/
theorem GenValue.specializeAt_of_ne_agg {x : GenValue T (BoolFunc X)}
    (h : GenValue.kindOf x ≠ ColKind.agg) (v : X → Bool) :
    GenValue.specializeAt v x = AggValue.collapseSum x := by
  cases x with
  | inl w => rfl
  | inr a => exact absurd rfl h

/-! ## The guardedness invariant -/

variable [HasAltLinearOrder (BoolFunc X)]

omit [Fintype X] [DecidableEq X] in
/-- **A filtered window's column is guarded by the row it is computed
for.** Where that row is in its own frame it contributes an occurrence to
the family – its own where the clause rejects it, its value's class where
the clause keeps it – and a valuation that realizes the row realizes that
occurrence's annotation. -/
theorem annGuard_annList_exprWhen {n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    {c : ℕ} (t : TermIn T c n') (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n' → Bool)
    (r : OccFam (AnnotatedTuple T (BoolFunc X) n')) (i : Fin r.size)
    (v : X → Bool) {γ : Fin c → T}
    (hs : w.s (Tuple.key O (r.row i).fst) = true)
    (hc : (r.row i).snd v = true) :
    annGuard (ValueFrame.exprWhen P O o w t f dist keep r i γ).annList v := by
  have hmem := ValueFrame.self_mem_frameSeqOn P O o w r i hs
  unfold ValueFrame.exprWhen
  cases dist
  · simp only [Bool.false_eq_true, ite_false, AggExpr.annList_ofSeqWhen]
    exact ⟨(r.row i).snd, List.mem_map.mpr ⟨r.row i, hmem, rfl⟩, hc⟩
  · simp only [ite_true, AggExpr.annList_ofSeqDistWhen]
    by_cases hk : keep (r.row i).fst = true
    · -- the clause keeps the row, so its value's class is in the merged part
      set pay : List (T × BoolFunc X) :=
        (((ValueFrame.frameSeqOn (α := AnnotatedTuple T (BoolFunc X) n')
            Prod.fst P O o w r i).filter (fun p => keep p.fst)).map
          (fun p => (t.eval p.fst γ, p.snd))) with hpay
      have hin : (t.eval (r.row i).fst γ, (r.row i).snd) ∈ pay :=
        List.mem_map.mpr
          ⟨r.row i, List.mem_filter.mpr ⟨hmem, by simpa using hk⟩, rfl⟩
      refine ⟨AggValue.classSum pay (t.eval (r.row i).fst γ),
        List.mem_append_left _ (List.mem_map.mpr
          ⟨(t.eval (r.row i).fst γ, AggValue.classSum pay
              (t.eval (r.row i).fst γ)),
            AggValue.mem_mergeOccs hin, rfl⟩), ?_⟩
      exact (AggValue.classSum_eval_iff v _ pay).mpr
        ⟨(t.eval (r.row i).fst γ, (r.row i).snd), hin, rfl, hc⟩
    · -- the clause rejects it, so it is its own occurrence of the family
      refine ⟨(r.row i).snd, List.mem_append_right _ ?_, hc⟩
      exact List.mem_map.mpr ⟨r.row i,
        List.mem_filter.mpr ⟨hmem, by simpa using hk⟩, rfl⟩
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
      r ∈ q.evaluate d γ → ∀ v : X → Bool,
      r.snd.finalize v = true →
      ∀ (k : Fin n) (a : AggTok T (BoolFunc X)), r.fst k = Sum.inr a →
        a.Realized v := by
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
      replace ha' : Sum.map gf (AggTok.postcomp gf) (r₀.fst k)
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
        cases a₀ with
        | tok a₀ => exact ih d r₀ hr₀ v hfin₀ k (AggTok.tok a₀) hu
        | nest a₀ =>
          exact (AggTok.Realized_postcomp gf (AggTok.nest a₀) v).mpr
            (ih d r₀ hr₀ v hfin₀ k (AggTok.nest a₀) hu)
        | expr a₀ =>
          -- reading through a function moves neither the family nor the
          -- conventions, so the worlds are the expression's own
          exact ih d r₀ hr₀ v hfin₀ k (AggTok.expr a₀) hu
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
  | Alt k hk q ih =>
    intro d γ r hr v hfin j a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, hs⟩ := Multiset.mem_bind.mp hr
    cases hfk : r₀.fst k with
    | inl w =>
      rw [GenRow.alternativesAt, hfk, Multiset.mem_singleton] at hs
      subst hs
      exact ih d _ hr₀ v hfin j a ha
    | inr b =>
      rw [GenRow.alternativesAt, hfk] at hs
      obtain ⟨v', -, rfl⟩ := Multiset.mem_map.mp hs
      by_cases hj : j = k
      · subst hj
        exact absurd ha (by simp)
      · refine ih d r₀ hr₀ v ?_ j a
          ((Function.update_of_ne hj (Sum.inl v') r₀.fst).symm.trans ha)
        exact mul_mul_eval_drop _ _ _ v hfin
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
    simp only [AggQueryIn.evaluate] at hr
    rw [Multiset.mem_singleton] at hr
    subst hr
    rw [← Sum.inr.inj ha]
    exact Or.inl rfl
  | Gamma is ts fs q keep ih =>
    -- the group's existence guard is the occurrence-annotation list the
    -- operator puts pending, over every occurrence of the group. An
    -- unfiltered token is grouped and takes its realized occurrence from
    -- that guard; a filtered one is scalar, and asks nothing
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.mp hr
    have hG : annGuard ((Having.havingGroup is
        ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map Prod.snd) v :=
      ((GenAnn.finalize_eval_iff _ v).mp hfin).2 _ (Multiset.mem_singleton_self _)
    revert ha
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro ha
    · dsimp only at ha
      rw [Fin.append_left] at ha
      exact absurd ha (by simp)
    · dsimp only at ha
      rw [Fin.append_right] at ha
      rw [← Sum.inr.inj ha]
      cases hkj : keep j with
      | none =>
        refine Or.inr ((AggValue.annGuard_iff_realized _ v).mp ?_)
        rw [AggValue.annList_ofGroup]
        exact hG
      | some φ =>
        -- the expression's family is the whole group, so the group's own
        -- guard gives it a realized occurrence – and that is a world of it
        rw [AggTok.Realized_expr, AggExpr.isWorld_ofGroupWhen]
        refine AggExpr.realizedWorld_nonempty_of_annGuard _ v ?_
        rw [AggExpr.annList_ofGroupWhen]
        exact hG
  | @GammaNest cI m n₁ κ' is his p f q ih =>
    -- the group's existence guard is the one annotation its bag of
    -- occurrences sums to, which gives the outer family a realized
    -- occurrence; each occurrence it keeps carries an inner value whose
    -- own guard is the guard of the row it came from
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hr
    have hG := ((GenAnn.finalize_eval_iff _ v).mp hfin).2 _
      (Multiset.mem_singleton_self _)
    revert ha
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> intro ha
    · dsimp only at ha
      rw [Fin.append_left] at ha
      exact absurd ha (by simp)
    · dsimp only at ha
      rw [Fin.append_right] at ha
      rw [← Sum.inr.inj ha]
      -- the occurrences of the group, with their rows
      set rows := (q.evaluate d γ).filter
        (fun row => (fun k => AggValue.collapseSum (row.fst (is k))) = g)
        with hrows
      have hocc : ∀ o ∈ rows.map (fun row =>
            (GenValue.innerValue (p.eval row.fst γ), row.snd.finalize)),
          ∃ row ∈ rows, (GenValue.innerValue (p.eval row.fst γ),
            row.snd.finalize) = o := by
        intro o ho
        exact Multiset.mem_map.mp ho
      refine ⟨Or.inr ?_, fun dd hdd hpres hsc => ?_, trivial⟩
      · -- the family's guard gives a realized occurrence
        obtain ⟨β, hβmem, hβv⟩ := hG
        rw [List.mem_singleton] at hβmem
        subst hβmem
        obtain ⟨β', hβ', hβ'v⟩ :=
          multiset_sum_eval_eq_true_iff _ v |>.mp hβv
        rw [Multiset.mem_map] at hβ'
        obtain ⟨o, ho, rfl⟩ := hβ'
        refine Multiset.card_pos_iff_exists_mem.mpr
          ⟨NestedValue.realizedOcc (fun α => α v) o, ?_⟩
        show NestedValue.realizedOcc (fun α => α v) o
          ∈ Multiset.filter
              (fun dd : NestedValue.WorldOcc T (BoolFunc X) =>
                dd.present = true) _
        rw [Multiset.mem_filter]
        exact ⟨Multiset.mem_map_of_mem _ ho, hβ'v⟩
      · -- and each kept occurrence's inner value is guarded by its row
        have hdd' : dd ∈ (rows.map (fun row =>
            (GenValue.innerValue (p.eval row.fst γ), row.snd.finalize))).map
            (NestedValue.realizedOcc (fun α => α v)) := hdd
        rw [Multiset.mem_map] at hdd'
        obtain ⟨o, ho, rfl⟩ := hdd'
        obtain ⟨row, hrow, rfl⟩ := hocc o ho
        have hfinrow : row.snd.finalize v = true := hpres
        refine GenValue.realized_innerValue (p.eval row.fst γ) v
          (fun a' ha' => ProjColIn.realized_eval p row.fst v
            (fun k' a'' ha'' => ih d row
              (Multiset.mem_of_mem_filter (by rw [hrows] at hrow; exact hrow))
              v hfinrow k' a'' ha'') ha') hsc
  | @Win cI n' m' p' P O o w t f q dist keep ih =>
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
      cases hk : keep with
      | some φ =>
        -- the column is an expression over the whole frame: where the row is
        -- in its own frame the leaf is grouped, and the row's own occurrence
        -- is in the family, realized with it
        rw [AggTok.Realized_expr]
        intro l hl
        have hs : w.s (Tuple.key O ((OccFam.ofSorted
            ((q.evaluate d γ).map GenRow.toAnnotated)).row i).fst) = true := by
          have hx : (!w.s (Tuple.key O ((OccFam.ofSorted
              ((q.evaluate d γ).map GenRow.toAnnotated)).row i).fst)) = false := by
            rw [← ValueFrame.scalar_exprWhen P O o w t f dist φ.keeps _ i l]
            exact hl
          simpa using hx
        have hrow : (((OccFam.ofSorted
            ((q.evaluate d γ).map GenRow.toAnnotated)).row i).snd) v = true := by
          have := hfin
          dsimp only at this
          rwa [GenAnn.finalize_of_pending_zero] at this
        obtain ⟨j, hj⟩ := AggExpr.realizedWorld_nonempty_of_annGuard _ v
          (annGuard_annList_exprWhen P O o w t f dist φ.keeps _ i v hs hrow)
        exact ⟨j, Finset.mem_inter.mpr ⟨hj, by
          rw [ValueFrame.inFrame_exprWhen]; exact Finset.mem_univ _⟩⟩
      | none =>
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
  | @GammaTok cI m n₁ n₂ κ' is his ts fs a' q keep ih =>
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
        cases hkj : keep j' with
        | none =>
          refine Or.inr ((AggValue.annGuard_iff_realized _ v).mp ?_)
          rw [AggValue.annList_ofGroup]
          exact hG
        | some φ =>
          -- as under `Gamma`: the expression's family is the whole group,
          -- so the group's own guard gives it a realized occurrence
          rw [AggTok.Realized_expr, AggExpr.isWorld_ofGroupWhen]
          refine AggExpr.realizedWorld_nonempty_of_annGuard _ v ?_
          rw [AggExpr.annList_ofGroupWhen]
          exact hG
    · rw [Fin.append_right] at hconf
      exact ColKind.noConfusion hconf
  | Retag h q ih =>
    intro d γ r hr v hfin k a ha
    exact ih d r hr v hfin k a ha
  | @WinExpr cI nI mI pI qI P O o ws ts fs g q keeps ih =>
    -- the window creates no group, so the row's own annotation is the
    -- whole guard: a valuation that realizes it keeps the current
    -- occurrence, which every leaf whose frame contains the current row
    -- reads. That is exactly a world of the expression.
    intro d γ r hr v hfin k a ha
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hr
    revert ha
    refine Fin.lastCases (fun ha => ?_) (fun k' ha => ?_) k
    · dsimp only at ha
      rw [Fin.snoc_last] at ha
      rw [← Sum.inr.inj ha]
      -- the row's annotation is realized, nothing being pending
      have hrow : ((OccFam.ofSorted (Multiset.map GenRow.toAnnotated
          (q.evaluate d γ))).row i).snd v = true := by
        have := hfin
        dsimp only at this
        rwa [GenAnn.finalize_of_pending_zero] at this
      show (ValueFrame.exprOfWhen P O o ws ts fs g keeps _ i γ).IsWorld _
      intro l hl
      -- a leaf read in the grouped convention has the current row in its
      -- frame, so the current occurrence is in its group – whatever its
      -- clause does with it
      have hs : (ws l).s (Tuple.key O ((OccFam.ofSorted
          (Multiset.map GenRow.toAnnotated (q.evaluate d γ))).row i).fst)
        = true := by
        have hx : (!(ws l).s (Tuple.key O ((OccFam.ofSorted
            (Multiset.map GenRow.toAnnotated (q.evaluate d γ))).row i).fst))
          = false := hl
        simpa using hx
      obtain ⟨j, hann, hframe⟩ :=
        ValueFrame.self_mem_inFrame_exprOfWhen P O o ts fs g keeps _ i γ
          (l := l) hs
      refine ⟨j, Finset.mem_inter.mpr ⟨?_, hframe l hs⟩⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show ((ValueFrame.exprOfWhen P O o ws ts fs g keeps _ i γ).anns j) v = true
      rw [hann]
      exact hrow
    · dsimp only at ha
      rw [Fin.snoc_castSucc] at ha
      exact absurd ha (by simp)

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

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- The realized world of an indexed family of rows, read occurrence by
occurrence. -/
private lemma genRandomWorld_occFam {n N : ℕ}
    (f : Fin N → GenRow T (BoolFunc X) n) (v : X → Bool) :
    genRandomWorld v (OccFam.mk N f).toMultiset
      = Multiset.map (fun i => GenRow.specializeTuple v (f i).fst)
          (Multiset.filter (fun i => (f i).snd.finalize v = true)
            (Finset.univ : Finset (Fin N)).val) := by
  unfold genRandomWorld OccFam.toMultiset
  rw [filter_map_comm, Multiset.map_map]
  rfl

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- And the realized world of a family of annotated occurrences. -/
private lemma randomWorld_occFam {n : ℕ}
    (r : OccFam (AnnotatedTuple T (BoolFunc X) n)) (v : X → Bool) :
    randomWorld v r.toMultiset
      = Multiset.map (fun i => (r.row i).fst)
          (Multiset.filter (fun i => (r.row i).snd v = true)
            (Finset.univ : Finset (Fin r.size)).val) := by
  unfold randomWorld OccFam.toMultiset
  rw [filter_map_comm, Multiset.map_map]
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
    show GenValue.specializeAt v (Sum.map gf (AggTok.postcomp gf) (u k))
      = gf (GenValue.specializeAt v (u k))
    cases u k with
    | inl w => rfl
    | inr x => cases x <;> rfl
  | provTerm t =>
    show GenValue.specializeAt v (Sum.inl (t.eval u γ)) = _
    exact TermGIn.eval_specialize t u hconf v

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- Specialization distributes over appending regular and token parts. -/
private lemma specializeTuple_append {n₁ n₂ : ℕ} (g : Tuple T n₁)
    (h : Fin n₂ → AggTok T (BoolFunc X)) (v : X → Bool) :
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

omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- The occurrences an expression's realized world selects are those its
valuation annotates true. -/
private lemma seqOf_realizedWorld_expr (e : AggExpr T (BoolFunc X))
    (v : X → Bool) :
    Having.seqOf e.occs (e.realizedWorld (fun α => α v))
      = e.occs.filter (fun z => z.snd.fst v) := by
  unfold AggExpr.realizedWorld
  exact Having.seqOf_filter_positions (fun z => z.snd.fst v) e.occs

/-- **And so is the expression it now builds**: its leaf reads the
occurrences the clause keeps among those the valuation realizes, which is
the plain filtered aggregate of the group in the realized world. -/
private lemma specialize_exprOfGroupWhen {c m n₁ : ℕ}
    (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T (BoolFunc X) m)
    (g : Tuple T n₁) (f : SeqAggFunc T) (t : TermIn T c m)
    (keep : Tuple T m → Bool) (v : X → Bool) {γ : Fin c → T} :
    (AggExpr.ofGroupWhen f t keep (Having.havingGroup is r g) γ).specialize
        (fun α => α v)
      = f (((Relation.groupSeq is (randomWorld v r) g).filter keep).map
          (fun x => t.eval x γ)) := by
  show f ((AggExpr.ofGroupWhen f t keep (Having.havingGroup is r g) γ).leafSeq
    ⟨0, by simp⟩ _) = _
  rw [AggExpr.leafSeq_eq_filter, seqOf_realizedWorld_expr,
    AggExpr.occs_ofGroupWhen, groupSeq_randomWorld]
  simp only [seqOf_realizedWorld, List.filter_map, List.map_map,
    List.filter_filter, Function.comp_def, Bool.true_and]
  refine congrArg f (congrArg₂ List.map rfl
    (List.filter_congr (fun p _ => ?_)))
  simp

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


omit [ValueType T] [Fintype X] [DecidableEq X]
  [HasAltLinearOrder (BoolFunc X)] in
/-- A `Bool`-valued `List.filter`, read as a `Multiset.filter`. -/
private lemma filter_coe_bool {α : Type} (pB : α → Bool) (l : List α) :
    (↑(l.filter pB) : Multiset α) = Multiset.filter (fun a => pB a = true) ↑l := by
  rw [Multiset.filter_coe]
  simp

omit [Fintype X] [DecidableEq X] in
/-- **A filtered window token is world-faithful.** Under a valuation it
reads as the plain filtered aggregate the realized world gives its row:
the clause cuts the frame by the rows and the valuation cuts it by the
annotations, the two cuts commute, and both readings are sorted by the
clause so only the values matter (`OrderSpec.map_eq_of_sorted`). -/
theorem tokenOfWhen_filter_agg {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n') (f g : SeqAggFunc T) (keep : Tuple T n' → Bool)
    (R : AnnotatedRelation T (BoolFunc X) n')
    {x : AnnotatedTuple T (BoolFunc X) n'} (hx : x ∈ R) (v : X → Bool)
    {γ : Fin c → T} (hc : x.snd v = true) :
    g ((((ValueFrame.tokenOfWhen P O o w t f keep R x γ).occs.filter
        (fun q => q.snd v)).map Prod.fst))
      = ValueFrame.windowValueWhen P O o w t g keep (randomWorld v R) x.fst γ := by
  refine congrArg g ?_
  -- the occurrences the two cuts leave, read off the annotated frame
  have hL : (((ValueFrame.tokenOfWhen P O o w t f keep R x γ).occs.filter
        (fun q => q.snd v)).map Prod.fst)
      = (((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n')
          Prod.fst P O o w R x).filter
          (fun q => q.snd v && keep q.fst)).map Prod.fst).map
        (fun u => t.eval u γ) := by
    show ((((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n')
        Prod.fst P O o w R x).filter (fun q => keep q.fst)).map
        (fun q => (t.eval q.fst γ, q.snd))).filter
        (fun z => z.snd v)).map Prod.fst = _
    rw [list_filter_map_comm, List.map_map, List.filter_filter, List.map_map]
    rfl
  rw [hL]
  refine OrderSpec.map_eq_of_sorted (α := Tuple T n') (key := Tuple.key O)
    (val := id) (o := o) (fun u => t.eval u γ) ?_ ?_ ?_
  · -- the same rows, by the restriction property of frames
    refine Multiset.coe_eq_coe.mp ?_
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
    rw [← Multiset.map_coe, filter_coe_bool, filter_coe_bool,
      ValueFrame.frameListOf_coe (α := AnnotatedTuple T (BoolFunc X) n')
        Prod.fst P O o w R x,
      ValueFrame.frameListOf_coe (α := Tuple T n') id P O o w
        (randomWorld v R) x.fst,
      hframe, Multiset.filter_map, Multiset.filter_filter]
    refine congrArg (Multiset.map Prod.fst) (Multiset.filter_congr ?_)
    intro y _
    show (y.snd v && keep y.fst) = true ↔ _
    rw [Bool.and_eq_true]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · -- the annotated reading, sorted by the clause and projected
    rw [List.pairwise_map]
    exact List.Pairwise.filter _ (OrderSpec.sortSeq_sorted
      (α := AnnotatedTuple T (BoolFunc X) n') (key := Tuple.key O)
      (val := Prod.fst) (o := o) _)
  · exact List.Pairwise.filter _ (OrderSpec.sortSeq_sorted
      (α := Tuple T n') (key := Tuple.key O)
      (val := (id : Tuple T n' → Tuple T n')) (o := o) _)

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

omit [Fintype X] [DecidableEq X] in
/-- **One leaf's reading of its frame in a world**: the rows of its frame
the world keeps give the plain window value the realized world gives the
row. This is the single-frame statement in the form a leaf of an
expression needs it, the family being listed by occurrence. -/
theorem frameSeq_filter_agg {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n') (f : SeqAggFunc T)
    (r : OccFam (AnnotatedTuple T (BoolFunc X) n')) (i : Fin r.size)
    (v : X → Bool) {γ : Fin c → T} (hc : (r.row i).snd v = true) :
    f ((((ValueFrame.frameSeqOn (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
          P O o w r i).filter (fun y => y.snd v)).map
        (fun y : AnnotatedTuple T (BoolFunc X) n' => t.eval y.fst γ)))
      = ValueFrame.windowValue P O o w t f (randomWorld v r.toMultiset)
          (r.row i).fst γ := by
  have hform : (((ValueFrame.tokenOf P O o w t f r.toMultiset (r.row i) γ).occs.filter
        (fun z => z.snd v)).map Prod.fst)
      = (((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
          P O o w r.toMultiset (r.row i)).filter (fun y => y.snd v)).map
        (fun y : AnnotatedTuple T (BoolFunc X) n' => t.eval y.fst γ)) := by
    rw [ValueFrame.tokenOf_occs, list_filter_map_comm, List.map_map]
    rfl
  rw [ValueFrame.frameSeqOn_eq_frameListOf, ← hform]
  exact tokenOf_filter_agg P O o w t f f r.toMultiset
    (OccFam.row_mem_toMultiset r i) v hc

omit [Fintype X] [DecidableEq X] in
/-- **The same under a `FILTER` clause**: the clause cuts the frame by the
rows, which the restriction to a world does not move. -/
theorem frameSeq_filter_agg_when {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n') (f : SeqAggFunc T) (keep : Tuple T n' → Bool)
    (r : OccFam (AnnotatedTuple T (BoolFunc X) n')) (i : Fin r.size)
    (v : X → Bool) {γ : Fin c → T} (hc : (r.row i).snd v = true) :
    f ((((ValueFrame.frameSeqOn (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
          P O o w r i).filter (fun y => keep y.fst && y.snd v)).map
        (fun y : AnnotatedTuple T (BoolFunc X) n' => t.eval y.fst γ)))
      = ValueFrame.windowValueWhen P O o w t f keep (randomWorld v r.toMultiset)
          (r.row i).fst γ := by
  have hform : (((ValueFrame.tokenOfWhen P O o w t f keep r.toMultiset
        (r.row i) γ).occs.filter (fun z => z.snd v)).map Prod.fst)
      = (((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
          P O o w r.toMultiset (r.row i)).filter
          (fun y => keep y.fst && y.snd v)).map
        (fun y : AnnotatedTuple T (BoolFunc X) n' => t.eval y.fst γ)) := by
    show ((((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n')
        Prod.fst P O o w r.toMultiset (r.row i)).filter
        (fun z => keep z.fst)).map
        (fun z => (t.eval z.fst γ, z.snd))).filter
        (fun z => z.snd v)).map Prod.fst = _
    rw [list_filter_map_comm, List.map_map, List.filter_filter]
    exact congrArg₂ List.map rfl
      (List.filter_congr (fun y _ => Bool.and_comm _ _))
  rw [ValueFrame.frameSeqOn_eq_frameListOf, ← hform]
  exact tokenOfWhen_filter_agg P O o w t f f keep r.toMultiset
    (OccFam.row_mem_toMultiset r i) v hc

omit [Fintype X] [DecidableEq X] in
/-- **The column a multi-frame window builds is world-faithful.** Under a
valuation each leaf reads its own frame cut down to the realized rows, in
the clause's order, and that is the plain window value the realized world
gives the row. The leaf aggregates need not be symmetric: both readings
are sorted by the clause, so they differ only inside blocks of equal rows
(`OrderSpec.map_eq_of_sorted`). -/
theorem exprOf_specialize {c n' m' p' q' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (ws : Fin q' → ValueFrame T p')
    (ts : Fin q' → TermIn T c n') (fs : Fin q' → SeqAggFunc T)
    (g : (Fin q' → T) → T)
    (r : OccFam (AnnotatedTuple T (BoolFunc X) n')) (i : Fin r.size)
    (v : X → Bool) {γ : Fin c → T} (hc : (r.row i).snd v = true) :
    (ValueFrame.exprOf P O o ws ts fs g r i γ).specialize (fun α => α v)
      = g (fun l => ValueFrame.windowValue P O o (ws l) (ts l) (fs l)
          (randomWorld v r.toMultiset) (r.row i).fst γ) := by
  show g (fun l => (fs l) ((ValueFrame.exprOf P O o ws ts fs g r i γ).leafSeq l
      (Finset.univ.filter (fun x =>
        ((ValueFrame.exprOf P O o ws ts fs g r i γ).anns x) v = true)))) = _
  refine congrArg g (funext (fun l => ?_))
  rw [ValueFrame.leafSeq_exprOf_keep P O o ws ts fs g r i γ l (fun α => α v),
    show (fun j : Fin r.size => (ts l).eval (r.row j).fst γ)
      = (fun y : AnnotatedTuple T (BoolFunc X) n' => (ts l).eval y.fst γ)
        ∘ r.row from rfl,
    ← List.map_map]
  -- the leaf's rows and the frame list hold the same occurrences
  have hpred : (fun y : AnnotatedTuple T (BoolFunc X) n' => y.snd v)
      = (fun y : AnnotatedTuple T (BoolFunc X) n' => decide (y.snd v = true)) := by
    funext y; simp
  have h1 : (↑((((ValueFrame.exprIdx (α := AnnotatedTuple T (BoolFunc X) n')
        Prod.fst P O o ws r i).filter
        (fun j => ValueFrame.mem (α := AnnotatedTuple T (BoolFunc X) n')
          Prod.fst P O (ws l) r i j && (r.row j).snd v)).map r.row))
      : Multiset (AnnotatedTuple T (BoolFunc X) n'))
      = (ValueFrame.frameOf (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
          P O (ws l) r.toMultiset (r.row i)).filter
        (fun y => y.snd v = true) :=
    ValueFrame.exprIdx_filter_keep_rows_coe P O o ws r i l (fun α => α v)
  have h2 : (↑((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n')
        Prod.fst P O o (ws l) r.toMultiset (r.row i)).filter
        (fun y => y.snd v)) : Multiset (AnnotatedTuple T (BoolFunc X) n'))
      = (ValueFrame.frameOf (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
          P O (ws l) r.toMultiset (r.row i)).filter
        (fun y => y.snd v = true) := by
    rw [hpred, ← Multiset.filter_coe, ValueFrame.frameListOf_coe]
  have hmapeq : (List.map r.row
        ((ValueFrame.exprIdx (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst
            P O o ws r i).filter
          (fun j => ValueFrame.mem (α := AnnotatedTuple T (BoolFunc X) n')
            Prod.fst P O (ws l) r i j && (r.row j).snd v))).map
        (fun y : AnnotatedTuple T (BoolFunc X) n' => (ts l).eval y.fst γ)
      = ((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n')
          Prod.fst P O o (ws l) r.toMultiset (r.row i)).filter
          (fun y => y.snd v)).map
        (fun y : AnnotatedTuple T (BoolFunc X) n' => (ts l).eval y.fst γ) :=
    OrderSpec.map_eq_of_sorted (key := Tuple.key O)
      (val := (Prod.fst : AnnotatedTuple T (BoolFunc X) n' → Tuple T n'))
      (o := o) (fun u => (ts l).eval u γ)
      (Multiset.coe_eq_coe.mp (h1.trans h2.symm))
      (ValueFrame.exprIdx_filter_rows_pairwise
        (α := AnnotatedTuple T (BoolFunc X) n') Prod.fst P O o ws r i _)
      (List.Pairwise.filter _ (OrderSpec.sortSeq_sorted
        (key := Tuple.key O)
        (val := (Prod.fst : AnnotatedTuple T (BoolFunc X) n' → Tuple T n'))
        (o := o) _))
  rw [hmapeq]
  -- and the frame list is what the single-frame case already settles
  have hform : (((ValueFrame.tokenOf P O o (ws l) (ts l) (fs l) r.toMultiset
        (r.row i) γ).occs.filter (fun z => z.snd v)).map Prod.fst)
      = ((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n')
          Prod.fst P O o (ws l) r.toMultiset (r.row i)).filter
          (fun y => y.snd v)).map
        (fun y : AnnotatedTuple T (BoolFunc X) n' => (ts l).eval y.fst γ) := by
    rw [ValueFrame.tokenOf_occs, list_filter_map_comm, List.map_map]
    rfl
  rw [← hform]
  exact tokenOf_filter_agg P O o (ws l) (ts l) (fs l) (fs l) r.toMultiset
    (OccFam.row_mem_toMultiset r i) v hc

omit [Fintype X] [DecidableEq X] in
/-- **A filtered multi-frame window's column is world-faithful too.**
Each leaf reads its own frame cut down by its own clause and to the
realized rows, which is the plain window value the realized world gives
the row: a clause tests the row, and restricting the relation to a world
does not move a row. -/
theorem exprOfWhen_specialize {c n' m' p' q' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (ws : Fin q' → ValueFrame T p')
    (ts : Fin q' → TermIn T c n') (fs : Fin q' → SeqAggFunc T)
    (g : (Fin q' → T) → T) (keeps : Fin q' → Option (Selection T n'))
    (r : OccFam (AnnotatedTuple T (BoolFunc X) n')) (i : Fin r.size)
    (v : X → Bool) {γ : Fin c → T} (hc : (r.row i).snd v = true) :
    (ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).specialize (fun α => α v)
      = g (fun l => ValueFrame.windowValueOpt P O o (ws l) (ts l) (fs l)
          (keeps l) (randomWorld v r.toMultiset) (r.row i).fst γ) := by
  show g (fun l => (fs l)
      ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).leafSeq l
        (Finset.univ.filter (fun x =>
          ((ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ).anns x) v
            = true)))) = _
  refine congrArg g (funext (fun l => ?_))
  rw [ValueFrame.leafSeq_exprOfWhen_keep P O o ws ts fs g keeps r i γ l
    (fun α => α v)]
  cases keeps l with
  | none =>
    simp only [Bool.and_true, ValueFrame.windowValueOpt_none]
    rw [ValueFrame.map_exprIdx_filter_occs P O o ws ts r i γ l
      (fun y => y.snd v)]
    exact frameSeq_filter_agg P O o (ws l) (ts l) (fs l) r i v hc
  | some φ =>
    simp only [Bool.and_assoc, ValueFrame.windowValueOpt_some]
    rw [ValueFrame.map_exprIdx_filter_occs P O o ws ts r i γ l
      (fun y => φ.keeps y.fst && y.snd v)]
    exact frameSeq_filter_agg_when P O o (ws l) (ts l) (fs l) φ.keeps r i v hc


omit [Fintype X] [DecidableEq X] in
/-- **A filtered token specializes to the filtered aggregate of the
realized frame**: the case of `tokenOfWhen_filter_agg` where the
aggregate applied is the token's own. -/
theorem tokenOfWhen_specialize {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n') (f : SeqAggFunc T) (keep : Tuple T n' → Bool)
    (R : AnnotatedRelation T (BoolFunc X) n')
    {x : AnnotatedTuple T (BoolFunc X) n'} (hx : x ∈ R) (v : X → Bool)
    {γ : Fin c → T} (hc : x.snd v = true) :
    (ValueFrame.tokenOfWhen P O o w t f keep R x γ).specialize (fun α => α v)
      = ValueFrame.windowValueWhen P O o w t f keep (randomWorld v R) x.fst γ := by
  unfold AggValue.specialize
  exact tokenOfWhen_filter_agg P O o w t f f keep R hx v hc

omit [Fintype X] [DecidableEq X] in
/-- The same for the `DISTINCT` reading. -/
theorem tokenOfDistWhen_specialize {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n') (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n' → Bool) (R : AnnotatedRelation T (BoolFunc X) n')
    {x : AnnotatedTuple T (BoolFunc X) n'} (hx : x ∈ R) (v : X → Bool)
    {γ : Fin c → T} (hc : x.snd v = true) :
    (ValueFrame.tokenOfDistWhen P O o w t f dist keep R x γ).specialize
        (fun α => α v)
      = ValueFrame.windowValueWhen P O o w t (if dist then f.distinct else f)
        keep (randomWorld v R) x.fst γ := by
  unfold ValueFrame.tokenOfDistWhen
  cases dist
  · simpa using tokenOfWhen_specialize P O o w t f keep R hx v hc
  · simp only [ite_true]
    rw [AggValue.specialize_mergeByValue]
    exact tokenOfWhen_filter_agg P O o w t f f.distinct keep R hx v hc

omit [Fintype X] [DecidableEq X] in
/-- **A filtered window's column is world-faithful.** Its leaf reads the
occurrences the clause keeps among those the valuation realizes – merged
by value under `DISTINCT` – which is the plain filtered window value the
realized world gives the row: a clause tests the row and the valuation
reads the annotation, so the two cuts commute. -/
theorem exprWhenOf_specialize {c n' m' p' : ℕ} (P : Tuple (Fin n') m')
    (O : Tuple (Fin n') p') (o : OrderSpec p') (w : ValueFrame T p')
    (t : TermIn T c n') (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n' → Bool) (R : AnnotatedRelation T (BoolFunc X) n')
    {x : AnnotatedTuple T (BoolFunc X) n'} (hx : x ∈ R) (v : X → Bool)
    {γ : Fin c → T} (hc : x.snd v = true) :
    (ValueFrame.exprWhenOf P O o w t f dist keep R x γ).specialize
        (fun α => α v)
      = ValueFrame.windowValueWhen P O o w t
          (if dist then f.distinct else f) keep (randomWorld v R) x.fst γ := by
  unfold ValueFrame.exprWhenOf
  cases dist
  · simp only [Bool.false_eq_true, ite_false]
    show f ((AggExpr.ofSeqWhen f t keep _ (!w.s (Tuple.key O x.fst)) γ).leafSeq
      ⟨0, Nat.zero_lt_one⟩ _) = _
    rw [AggExpr.leafSeq_realizedWorld_ofSeqWhen]
    refine Eq.trans ?_ (tokenOfWhen_filter_agg P O o w t f f keep R hx v hc)
    refine congrArg f ?_
    show _ = List.map Prod.fst (List.filter
      (fun q : T × BoolFunc X => q.snd v)
      (((ValueFrame.frameListOf (α := AnnotatedTuple T (BoolFunc X) n')
          Prod.fst P O o w R x).filter (fun q => keep q.fst)).map
        (fun q => (t.eval q.fst γ, q.snd))))
    rw [List.filter_map, List.map_map, List.filter_filter]
    exact congrArg₂ List.map rfl
      (List.filter_congr (fun p _ => (Bool.and_comm _ _)))
  · simp only [ite_true]
    show f ((AggExpr.ofSeqDistWhen f t keep _ (!w.s (Tuple.key O x.fst))
      γ).leafSeq ⟨0, Nat.zero_lt_one⟩ _) = _
    rw [AggExpr.leafSeq_realizedWorld_ofSeqDistWhen]
    exact tokenOfDistWhen_specialize P O o w t f true keep R hx v hc

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

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
/-- The value a token specializes to under a valuation is one of the
values it takes, its group being realized. -/
private lemma specialize_mem_vals (a : AggValue T (BoolFunc X)) (v : X → Bool)
    (hr : a.scalar = true ∨ (a.realized v).Nonempty) :
    a.specialize (fun α => α v) ∈ a.vals := by
  rw [AggValue.specialize_eval]
  exact Finset.mem_image.mpr ⟨a.realized v,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
/-- The value an expression takes in the world a valuation cuts out is
one of its values, as soon as that world is a world of it. -/
theorem AggExpr.specialize_mem_vals (e : AggExpr T (BoolFunc X)) (v : X → Bool)
    (hr : e.IsWorld (e.realizedWorld (fun α => α v))) :
    e.specialize (fun α => α v) ∈ e.vals :=
  Finset.mem_image.mpr ⟨e.realizedWorld (fun α => α v),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩

omit [Fintype X] [DecidableEq X] [HasAltLinearOrder (BoolFunc X)] in
/-- **The reading a column takes under a valuation is one of its
values**, whichever kind of token it holds. -/
theorem AggTok.specialize_mem_vals {x : AggTok T (BoolFunc X)}
    (v : X → Bool) (hr : x.Realized v) :
    x.specialize (fun α => α v) ∈ x.vals := by
  cases x with
  | tok a => exact _root_.specialize_mem_vals a v hr
  | nest a => exact NestedValue.specialize_mem_vals a v hr
  | expr e => exact AggExpr.specialize_mem_vals e v hr

omit [HasAltLinearOrder (BoolFunc X)] in
/-- **Exactly one value of a column is realized**: the alternative test
`[a ≐ v']` holds under a valuation precisely of the reading the valuation
gives the column. -/
theorem AggTok.altProv_eval_iff {x : AggTok T (BoolFunc X)}
    (v : X → Bool) (hr : x.Realized v) (v' : T) :
    (x.altProv v') v = true ↔ v' = x.specialize (fun α => α v) := by
  cases x with
  | tok a =>
    rw [AggTok.altProv_tok, AggValue.altProv,
      AggValue.predProvOfWith_eval_iff]
    constructor
    · rintro ⟨-, h2⟩
      exact ((CompOp.syneq_eval3_eq_true_iff _ _).mp h2).symm
    · intro h
      exact ⟨hr, (CompOp.syneq_eval3_eq_true_iff _ _).mpr h.symm⟩
  | nest a =>
    show (a.predProvWith (fun y => CompOp.syneq.eval3 y v')) v = true ↔ _
    rw [NestedValue.predProvWith_eval_iff]
    constructor
    · rintro ⟨-, h2⟩
      exact ((CompOp.syneq_eval3_eq_true_iff _ _).mp h2).symm
    · intro h
      exact ⟨hr, (CompOp.syneq_eval3_eq_true_iff _ _).mpr h.symm⟩
  | expr e =>
    show (e.predProvWith (fun y => CompOp.syneq.eval3 y v')) v = true ↔ _
    rw [AggExpr.predProvWith_eval_iff]
    constructor
    · rintro ⟨-, h2⟩
      exact ((CompOp.syneq_eval3_eq_true_iff _ _).mp h2).symm
    · intro h
      exact ⟨hr, (CompOp.syneq_eval3_eq_true_iff _ _).mpr h.symm⟩

omit [HasAltLinearOrder (BoolFunc X)] in
/-- **Exactly one alternative of an occurrence survives a valuation**:
the one whose value is the column's value in that world – and it
specializes to what the occurrence specializes to, so reading an
aggregate column as a key changes no realized world. -/
private lemma genRandomWorld_alternativesAt {n : ℕ}
    (r : GenRow T (BoolFunc X) n) (k : Fin n) (v : X → Bool)
    (hg : ∀ a : AggTok T (BoolFunc X), r.fst k = Sum.inr a →
      r.snd.finalize v = true → a.Realized v) :
    genRandomWorld v (r.alternativesAt k) = genRandomWorld v {r} := by
  cases hfk : r.fst k with
  | inl w => rw [GenRow.alternativesAt, hfk]
  | inr x =>
    rw [GenRow.alternativesAt, hfk]
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map, Multiset.filter_singleton]
    by_cases hfin : r.snd.finalize v = true
    · have hr : x.Realized v := hg x hfk hfin
      have hp : ∀ v' : T,
          ((⟨r.snd.base * x.altProv v', r.snd.pending⟩ : GenAnn (BoolFunc X)).finalize) v
            = true ↔ v' = x.specialize (fun α => α v) := by
        intro v'
        rw [show ((⟨r.snd.base * x.altProv v', r.snd.pending⟩
              : GenAnn (BoolFunc X)).finalize)
            = (r.snd.base * x.altProv v')
              * (r.snd.pending.map (fun l => SemiringWithMonus.delta l.sum)).prod
            from rfl,
          mul_mul_eval_iff _ _ _ v hfin]
        exact AggTok.altProv_eval_iff v hr v'
      have hfil : Multiset.filter
            (fun v' => ((⟨r.snd.base * x.altProv v', r.snd.pending⟩
              : GenAnn (BoolFunc X)).finalize) v = true) x.vals.val
          = {x.specialize (fun α => α v)} := by
        rw [← Finset.filter_val,
          Finset.filter_congr (fun v' _ => hp v'), Finset.filter_eq',
          ite_eq_left (AggTok.specialize_mem_vals v hr)]
        rfl
      rw [ite_eq_left hfin, hfil, Multiset.map_singleton, Multiset.map_singleton]
      refine congrArg _ (funext (fun j => ?_))
      by_cases hj : j = k
      · subst hj
        show GenValue.specializeAt v (Function.update r.fst j (Sum.inl _) j)
          = GenValue.specializeAt v (r.fst j)
        rw [Function.update_self, hfk]
        rfl
      · exact congrArg (GenValue.specializeAt v)
          (Function.update_of_ne hj (Sum.inl (x.specialize fun α => α v)) r.fst)
    · rw [ite_eq_right hfin]
      refine Multiset.eq_zero_of_forall_notMem (fun t ht => ?_)
      obtain ⟨v', hv', -⟩ := Multiset.mem_map.mp ht
      obtain ⟨-, hp⟩ := Multiset.mem_filter.mp hv'
      have hmem : ((r.snd.base * x.altProv v')
          * ((r.snd.pending.map (fun l => SemiringWithMonus.delta l.sum)).prod)) v
            = true := hp
      exact hfin (mul_mul_eval_drop _ _ _ v hmem)

omit [HasAltLinearOrder (BoolFunc X)] in
/-- Reading an aggregate column as a key changes no realized world. -/
private lemma genRandomWorld_bind_alternativesAt {n : ℕ} (k : Fin n)
    (v : X → Bool) :
    ∀ R : Multiset (GenRow T (BoolFunc X) n),
      (∀ r ∈ R, ∀ a : AggTok T (BoolFunc X), r.fst k = Sum.inr a →
        r.snd.finalize v = true → a.Realized v) →
      genRandomWorld v (R.bind (fun r => r.alternativesAt k))
        = genRandomWorld v R := by
  intro R
  induction R using Multiset.induction_on with
  | empty => intro _; rfl
  | cons r R ih =>
    intro hg
    rw [← Multiset.singleton_add, Multiset.add_bind, genRandomWorld_add,
      genRandomWorld_add, Multiset.singleton_bind,
      genRandomWorld_alternativesAt r k v
        (fun a ha => hg r (Multiset.mem_cons_self r R) a ha),
      ih (fun r' hr' => hg r' (Multiset.mem_cons_of_mem hr'))]

/-- **Random-world commutation for the general evaluator** (over `𝔹[X]`):
specializing the realized rows of the general annotated evaluation is the
plain evaluation of the realized world. The σ-aggregate case is the row
lemma `GenPredIn.sel_finalize_eval_iff` under the conformance and
guardedness invariants; the `Gamma` case rests on
`groupSeq_randomWorld`; the multi-frame window on `exprOf_specialize`,
which says its column reads in a world what the plain window reads of
that world – so the operator asks nothing of its frames or of its
aggregates here.

Second-level aggregation is covered too, for one storey: the group's
pending factor is realized exactly when one of its rows is, so the keys
that survive are the realized world's keys, and the token's realized
world keeps those rows and reads each in the world the valuation cuts out
of the row's own column (`ProjColIn.specialize_innerValue`). What
`nestOnce` excludes is a second storey, whose inner reading is taken
through its collapse – the deterministic reading, not the world one. -/
theorem AggQueryIn.genRandomWorld_evaluate :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (_hq : q.noProvSum) (_hn : q.nestOnce)
      (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool)
      {γ : Fin c → T},
    genRandomWorld v (q.evaluate d γ)
      = q.evaluatePlain (d.randomWorld v) γ := by
  intro c n κ q
  induction q with
  | Rel n s =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [AnnotatedDatabase.find_randomWorld]
    cases hf : d.find n s with
    | none => rfl
    | some rn => exact genRandomWorld_ofAnnotated rn v
  | Proj ps q ih =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map]
    rw [Multiset.filter_congr (fun r (_ : r ∈ q.evaluate d γ) =>
      Iff.of_eq (congrArg (fun α : BoolFunc X => α v = true)
        (GenAnn.finalize_cash r.snd.base r.snd.pending
          (r.snd.pending ∩ tokenLists (fun j => (ps j).eval r.fst γ))
          Multiset.inter_le_left)))]
    rw [Multiset.map_congr rfl (fun r hr => ?_), ← Multiset.map_map, ← ih hq hn d v]
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
    intro hq hn d v γ
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
      · rw [← ih hq hn d v]
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
      · rw [← ih hq hn d v]
        unfold genRandomWorld
        rw [filter_map_comm, Multiset.filter_filter]
        exact Multiset.map_congr
          (Multiset.filter_congr fun r _ => and_comm) (fun r _ => rfl)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hn d v γ
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
        (q₁.evaluate d γ) (q₂.evaluate d γ), ← ih₁ hq.1 hn.1 d v, ← ih₂ hq.2 hn.2 d v]
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
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    -- the left side is all-regular, so its rows specialize as they collapse
    have hspec : ∀ x ∈ q₁.evaluate d γ,
        GenRow.specializeTuple v x.fst = GenRow.plainTuple x.fst :=
      fun x hx => specializeTuple_eq_plainTuple x.fst
        (fun k => AggQueryIn.evaluate_conform q₁ d x hx k) v
    conv_rhs => rw [← ih₁ hq.1 hn.1 d v]
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
      · rw [Multiset.map_map, ← ih₂ hq.2 hn.2 d v]
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
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_add, ih₁ hq.1 hn.1 d v, ih₂ hq.2 hn.2 d v]
  | Dedup q ih =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_ofAnnotated, randomWorld_groupByKey,
      genRandomWorld_allReg, ih hq hn d v]
  | Alt k hk q ih =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_bind_alternativesAt k v (q.evaluate d γ)
      (fun r hr a ha hfin =>
        AggQueryIn.evaluate_guarded q d r hr v hfin k a ha)]
    exact ih hq hn d v
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_ofAnnotated]
    refine Eq.trans (muSum_map (h := _root_.randomWorld v)
      (randomWorld_add v)
      (stepP := fun Y => q₁.evaluatePlain ((d.randomWorld v).assign s Y) γ)
      (fun Y => by
        rw [genRandomWorld_allReg]
        exact ih₁ hq.2 hn.2 (d.assign s Y) v) b _) ?_
    rw [genRandomWorld_allReg, ih₀ hq.1 hn.1 d v]
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [genRandomWorld_ofAnnotated]
    refine muIter_map (h := _root_.randomWorld v) rfl
      (stepP := fun Y => (q₀.evaluatePlain ((d.randomWorld v).assign s Y) γ
        + q₁.evaluatePlain ((d.randomWorld v).assign s Y) γ).dedup)
      (fun Y => ?_) b
    show _root_.randomWorld v (AnnotatedRelation.dedupAnn (_ + _)) = _
    rw [AnnotatedRelation.dedupAnn, randomWorld_groupByKey, randomWorld_add,
      genRandomWorld_allReg, genRandomWorld_allReg,
      ih₀ hq.1 hn.1 (d.assign s Y) v, ih₁ hq.2 hn.2 (d.assign s Y) v]
    rfl
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    refine Eq.trans (genRandomWorld_ofAnnotated _ v)
      (Eq.trans (randomWorld_monus
        ((q₁.evaluate d γ).map GenRow.toAnnotated)
        ((q₂.evaluate d γ).map GenRow.toAnnotated) v) ?_)
    rw [genRandomWorld_allReg, genRandomWorld_allReg, ih₁ hq.1 hn.1 d v, ih₂ hq.2 hn.2 d v]
  | @GammaScalar cI m n₂ ts fs q ih =>
    -- one row on each side, kept in every world, its tokens specializing to
    -- the aggregates over the realized rows
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [← ih hq hn d v, ← genRandomWorld_allReg q d v]
    unfold genRandomWorld
    rw [show Multiset.filter
          (fun r : GenRow T (BoolFunc X) n₂ => r.snd.finalize v = true)
          {(⟨fun j => Sum.inr (AggTok.tok (AggValue.ofScalarGroup (fs j) (ts j)
              (Having.havingGroup (fun i : Fin 0 => i.elim0)
                ((q.evaluate d γ).map GenRow.toAnnotated)
                (fun i : Fin 0 => i.elim0)) γ)), ⟨1, 0⟩⟩
            : GenRow T (BoolFunc X) n₂)}
        = {(⟨fun j => Sum.inr (AggTok.tok (AggValue.ofScalarGroup (fs j) (ts j)
              (Having.havingGroup (fun i : Fin 0 => i.elim0)
                ((q.evaluate d γ).map GenRow.toAnnotated)
                (fun i : Fin 0 => i.elim0)) γ)), ⟨1, 0⟩⟩
            : GenRow T (BoolFunc X) n₂)}
        from Multiset.filter_eq_self.mpr (fun r hr => by
          rw [Multiset.mem_singleton] at hr; subst hr; rfl)]
    rw [Multiset.map_singleton]
    exact congrArg (fun u => (Multiset.ofList [u] : Multiset (Tuple T n₂)))
      (funext fun j => specialize_ofGroup _
        ((q.evaluate d γ).map GenRow.toAnnotated) _ (fs j) (ts j) v)
  | @GammaNest cI m n₁ κ' is his p f q ih =>
    -- one output row per group that the realized world keeps, and its
    -- token specializes to the outer aggregate over the realized rows of
    -- the group: the pending factor is realized exactly when one of the
    -- group's rows is, and the realized world of the token keeps that
    -- occurrence and reads it in the world it cuts out of the row's own
    -- column (`ProjColIn.specialize_innerValue`)
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [← ih hq (AggQueryIn.nestOnce_of_noGammaNest q hn) d v]
    -- the rows, the key read off their values, and what a row contributes
    set rows := q.evaluate d γ with hrows
    set key : GenRow T (BoolFunc X) m → Tuple T n₁ :=
      fun row => fun k => AggValue.collapseSum (row.fst (is k)) with hkey
    -- every row has no nested column, so each occurrence of the token
    -- reads what its row reads
    have hnest : ∀ row ∈ rows, GenRow.NoNested row.fst :=
      fun row hrow => AggQueryIn.evaluate_noNested q hn d row hrow
    have hconf : ∀ row ∈ rows, ∀ k, GenValue.kindOf (row.fst k) = (κ' k).base :=
      fun row hrow => AggQueryIn.evaluate_conform q d row hrow
    -- the key a realized row carries in the realized world is its own
    have hkeyspec : ∀ row ∈ rows,
        (fun k => GenRow.specializeTuple v row.fst (is k) : Tuple T n₁)
          = key row := by
      intro row hrow
      funext k
      show GenValue.specializeAt v (row.fst (is k)) = _
      refine GenValue.specializeAt_of_ne_agg ?_ v
      rw [hconf row hrow (is k), ColKind.base_eq_reg_of_ne_agg (his k)]
      exact fun hc => ColKind.noConfusion hc
    -- a group's row survives exactly where its own annotation does
    have hsurv : ∀ g : Tuple T n₁,
        (⟨1, {[(((rows.filter (fun row => key row = g)).map
            (fun row => (GenValue.innerValue (p.eval row.fst γ),
              row.snd.finalize))).map Prod.snd).sum]}⟩
          : GenAnn (BoolFunc X)).finalize v = true
        ↔ 0 < Multiset.card ((rows.filter (fun row => key row = g)).filter
            (fun row => row.snd.finalize v = true)) := by
      intro g
      rw [GenAnn.finalize_eval_iff, Multiset.card_pos_iff_exists_mem]
      constructor
      · rintro ⟨-, hpend⟩
        obtain ⟨β, hβmem, hβv⟩ := hpend _ (Multiset.mem_singleton_self _)
        rw [List.mem_singleton] at hβmem
        subst hβmem
        obtain ⟨β', hβ', hβ'v⟩ := multiset_sum_eval_eq_true_iff _ v |>.mp hβv
        rw [Multiset.map_map, Multiset.mem_map] at hβ'
        obtain ⟨row, hrow, rfl⟩ := hβ'
        exact ⟨row, Multiset.mem_filter.mpr ⟨hrow, hβ'v⟩⟩
      · rintro ⟨row, hrowm⟩
        obtain ⟨hrow, hrowv⟩ := Multiset.mem_filter.mp hrowm
        refine ⟨rfl, fun l hl => ?_⟩
        rw [Multiset.mem_singleton] at hl
        subst hl
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        refine multiset_sum_eval_eq_true_iff _ v |>.mpr ⟨row.snd.finalize, ?_, hrowv⟩
        rw [Multiset.map_map]
        exact Multiset.mem_map_of_mem _ hrow
    unfold genRandomWorld
    rw [filter_map_comm, Multiset.map_map,
      Multiset.filter_congr (fun g (_ : g ∈ (rows.map key).dedup) => hsurv g)]
    -- the keys the realized world has are the keys with a realized row
    have hkeys : ((rows.map key).dedup).filter
          (fun g => 0 < Multiset.card
            ((rows.filter (fun row => key row = g)).filter
              (fun row => row.snd.finalize v = true)))
        = ((((rows.filter (fun r => r.snd.finalize v = true)).map
            (fun r => GenRow.specializeTuple v r.fst)).map
              (fun u => (fun k => u (is k) : Tuple T n₁))).dedup) := by
      refine (Multiset.Nodup.ext ?_ (Multiset.nodup_dedup _)).mpr (fun g => ?_)
      · exact Multiset.Nodup.filter _ (Multiset.nodup_dedup _)
      · constructor
        · intro hg
          obtain ⟨-, hgc⟩ := Multiset.mem_filter.mp hg
          obtain ⟨row, hrowm⟩ := Multiset.card_pos_iff_exists_mem.mp hgc
          obtain ⟨hrowf, hrowv⟩ := Multiset.mem_filter.mp hrowm
          obtain ⟨hrow, hrowk⟩ := Multiset.mem_filter.mp hrowf
          refine Multiset.mem_dedup.mpr (Multiset.mem_map.mpr
            ⟨GenRow.specializeTuple v row.fst, Multiset.mem_map.mpr
              ⟨row, Multiset.mem_filter.mpr ⟨hrow, hrowv⟩, rfl⟩, ?_⟩)
          exact (hkeyspec row hrow).trans hrowk
        · intro hg
          obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_dedup.mp hg)
          obtain ⟨row, hrowf, rfl⟩ := Multiset.mem_map.mp hu
          obtain ⟨hrow, hrowv⟩ := Multiset.mem_filter.mp hrowf
          refine Multiset.mem_filter.mpr ⟨Multiset.mem_dedup.mpr
            (Multiset.mem_map.mpr ⟨row, hrow, (hkeyspec row hrow).symm⟩), ?_⟩
          exact Multiset.card_pos_iff_exists_mem.mpr ⟨row,
            Multiset.mem_filter.mpr ⟨Multiset.mem_filter.mpr
              ⟨hrow, (hkeyspec row hrow).symm⟩, hrowv⟩⟩
    rw [hkeys]
    refine Multiset.map_congr rfl (fun g hg => ?_)
    -- and per key the two tuples agree, the token specializing to the
    -- outer aggregate over the group's realized rows
    simp only [Function.comp_apply]
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · show GenValue.specializeAt v (Fin.append _ _ (Fin.castAdd 1 i)) = _
      rw [Fin.append_left, Fin.append_left]
      rfl
    · show GenValue.specializeAt v (Fin.append _ _ (Fin.natAdd n₁ j)) = _
      rw [Fin.append_right, Fin.append_right]
      show (NestedValue.mk f _ false).specialize
        (fun α : BoolFunc X => α v) = f _
      rw [NestedValue.specialize_eq]
      refine congrArg f ?_
      show (((rows.filter (fun row => key row = g)).map
            (fun row => (GenValue.innerValue (p.eval row.fst γ),
              row.snd.finalize))).filter (fun o => o.2 v = true)).map
          (fun o => o.1.specialize (fun α : BoolFunc X => α v)) = _
      rw [Multiset.filter_map, Multiset.map_map, Multiset.filter_filter]
      conv_rhs => rw [Multiset.filter_map, Multiset.map_map,
        Multiset.filter_filter]
      refine Multiset.map_congr (Multiset.filter_congr (fun row hrow => ?_))
        (fun row hrow => ?_)
      · -- the key a realized row carries in the realized world is its own
        constructor
        · rintro ⟨hv, hk⟩
          exact ⟨(hkeyspec row hrow).trans hk, hv⟩
        · rintro ⟨hk, hv⟩
          exact ⟨hv, (hkeyspec row hrow).symm.trans hk⟩
      · -- and the occurrence reads what the realized row reads
        have hrow' : row ∈ rows := (Multiset.mem_filter.mp hrow).1
        exact ProjColIn.specialize_innerValue p row.fst (hconf row hrow')
          (hnest row hrow') v
  | @Gamma cI m n₁ n₂ is ts fs q keep ih =>
    intro hq hn d v γ
    simp only [AggQueryIn.evaluate, AggQueryIn.evaluatePlain]
    rw [← ih hq hn d v, ← genRandomWorld_allReg q d v]
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
    cases hkj : keep j with
    | none =>
      exact specialize_ofGroup is ((q.evaluate d γ).map GenRow.toAnnotated)
        kv.fst (fs j) (ts j) v
    | some φ =>
      exact specialize_exprOfGroupWhen is ((q.evaluate d γ).map GenRow.toAnnotated)
        kv.fst (fs j) (ts j) φ.keeps v
  | ProvSum is his t q ih =>
    intro hq
    exact hq.elim
  | GammaTok is his ts fs a q keep ih =>
    intro hq
    exact hq.elim
  | @Win cI nI mI pI P O o w t f q dist keep ih =>
    -- one output row per realized input row; the token specializes to the
    -- aggregate the realized world gives the row, because restricting the
    -- relation restricts every frame – and a clause cuts the frame by the
    -- rows, which the restriction does not move
    intro hq hn d v γ
    cases hk : keep with
    | none =>
      rw [AggQueryIn.evaluate_Win_eq, AggQueryIn.evaluatePlain_Win_eq,
        ← ih hq hn d v, ← genRandomWorld_allReg q d v]
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
    | some φ =>
      rw [AggQueryIn.evaluate_Win_eq_when, AggQueryIn.evaluatePlain_Win_eq_when,
        ← ih hq hn d v, ← genRandomWorld_allReg q d v]
      unfold genRandomWorld randomWorld
      rw [filter_map_comm, Multiset.map_map, Multiset.map_map,
        Multiset.filter_congr (fun x (_ : x ∈ q.evaluateAnnotated d γ) =>
          show (ValueFrame.windowRowWhen P O o w t f φ.keeps
                (q.evaluateAnnotated d γ) x γ dist).snd.finalize v = true
            ↔ x.snd v = true from by
            simp [ValueFrame.windowRowWhen])]
      refine Multiset.map_congr rfl (fun x hx => ?_)
      obtain ⟨hxR, hxc⟩ := Multiset.mem_filter.mp hx
      simp only [Function.comp_apply, ValueFrame.windowRowWhen]
      funext k
      unfold GenRow.specializeTuple
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · rw [Fin.snoc_last, Fin.snoc_last]
        exact exprWhenOf_specialize P O o w t f dist φ.keeps
          (q.evaluateAnnotated d γ) hxR v hxc
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        rfl
  | Retag h q ih =>
    intro hq hn d v γ
    exact ih hq hn d v
  | @WinExpr cI nI mI pI qI P O o ws ts fs g q keeps ih =>
    -- one output row per realized occurrence. The column specializes to
    -- the plain window value the realized world gives the row
    -- (`exprOf_specialize`), so nothing depends on the indexing – which
    -- is what lets the family be compared with a relation at all.
    intro hq hn d v γ
    rw [AggQueryIn.evaluatePlain_WinExpr_eq_when, ← ih hq hn d v,
      ← genRandomWorld_allReg q d v]
    simp only [AggQueryIn.evaluate]
    set R : Multiset (AnnotatedTuple T (BoolFunc X) nI) :=
      Multiset.map GenRow.toAnnotated (q.evaluate d γ) with hRdef
    clear_value R
    have hRW : randomWorld v R
        = Multiset.map (fun i : Fin (OccFam.ofSorted R).size =>
            ((OccFam.ofSorted R).row i).fst)
          (Multiset.filter (fun i : Fin (OccFam.ofSorted R).size =>
            ((OccFam.ofSorted R).row i).snd v = true)
            (Finset.univ : Finset (Fin (OccFam.ofSorted R).size)).val) := by
      have hw := randomWorld_occFam (OccFam.ofSorted R) v
      rwa [OccFam.toMultiset_ofSorted] at hw
    rw [genRandomWorld_occFam]
    refine Eq.trans ?_ (congrArg (Multiset.map (fun u : Tuple T nI =>
        (Fin.snoc u (g (fun l => ValueFrame.windowValueOpt P O o (ws l) (ts l)
          (fs l) (keeps l) (randomWorld v R) u γ)) : Tuple T (nI + 1)))) hRW).symm
    rw [Multiset.map_map]
    refine Multiset.map_congr (Multiset.filter_congr (fun i _ => ?_))
      (fun i hi => ?_)
    · dsimp only
      rw [GenAnn.finalize_of_pending_zero]
    have hc : ((OccFam.ofSorted R).row i).snd v = true :=
      (Multiset.mem_filter.mp hi).2
    dsimp only [Function.comp]
    unfold GenRow.specializeTuple
    funext k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact (exprOfWhen_specialize P O o ws ts fs g keeps (OccFam.ofSorted R) i v
        hc).trans (by rw [OccFam.toMultiset_ofSorted])
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl

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
    (q : AggQuery T n κ) (hq : q.noProvSum) (hn : q.nestOnce)
    (d : AnnotatedDatabase T (BoolFunc X)) (v : X → Bool) :
    (q.booleanProv d) v = true
      ↔ q.evaluatePlain (d.randomWorld v) ≠ 0 := by
  unfold AggQueryIn.booleanProv
  rw [multiset_sum_eval, ← AggQueryIn.genRandomWorld_evaluate q hq hn d v]
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
    (hn : q.nestOnce)
    (d : AnnotatedDatabase T (BoolFunc X)) :
    AggQueryIn.booleanProb P q d = P.funcProb (q.booleanProv d) := by
  unfold AggQueryIn.booleanProb ProbAssignment.funcProb
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : q.evaluatePlain (d.randomWorld v) = 0
  · rw [ite_eq_left (Multiset.card_eq_zero.mpr h),
      ite_eq_right (fun hf =>
        (AggQueryIn.booleanProv_eval_iff q hq hn d v).mp hf h)]
  · rw [ite_eq_right (fun hc => h (Multiset.card_eq_zero.mp hc)),
      ite_eq_left ((AggQueryIn.booleanProv_eval_iff q hq hn d v).mpr h)]

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
    (hn : q.nestOnce)
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) (v : X → Bool) :
    (q.tupleProv d t) v = true
      ↔ t ∈ q.evaluatePlain (d.randomWorld v) := by
  unfold AggQueryIn.tupleProv
  rw [multiset_sum_eval, ← AggQueryIn.genRandomWorld_evaluate q hq hn d v]
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
    (hn : q.nestOnce)
    (d : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) :
    AggQueryIn.tupleProb P q d t = P.funcProb (q.tupleProv d t) := by
  unfold AggQueryIn.tupleProb ProbAssignment.funcProb
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : t ∈ q.evaluatePlain (d.randomWorld v)
  · rw [ite_eq_left h,
      ite_eq_left ((AggQueryIn.tupleProv_eval_iff q hq hn d t v).mpr h)]
  · rw [ite_eq_right h,
      ite_eq_right (fun hf =>
        h ((AggQueryIn.tupleProv_eval_iff q hq hn d t v).mp hf))]
