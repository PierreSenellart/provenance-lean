import Mathlib.Data.Fin.VecNotation

import Provenance.AnnotatedDatabase
import Provenance.Query
import Provenance.QueryAnnotatedDatabase
import Provenance.Util.ValueType

/-!
# Query evaluation by rewriting

This file provides an alternative approach to evaluating queries on annotated databases:
instead of directly interpreting operators over annotated tuples, a query on `T` is
rewritten into a query on `T ⊕ K` that operates on plain tuples whose values encode
both data and provenance.

The rewriting implemented here realises rules (R1)–(R5) from
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the Provenance
and Probability of Data*][sen2026provsql].

A correctness proof that `Query.rewriting` agrees with `Query.evaluateAnnotated` is
partially formalised: rules (R1), (R2), (R3) are machine-checked end-to-end; rule
(R4) is proved modulo two `sorry`s in the `Diff` case, one each in the
"unmatched" and "matched" halves of the rewriting. Both reduce to a semijoin
identity over `Multiset.product`/`Multiset.filter`/`Multiset.map` (matching the
join condition against the deduped key set produced by the inner rewriting).
The instance-synthesis blocker on the inner dedup is now lifted via
`Query.rewriting_valid_diff_inner_dd_inst` (an instance-polymorphic restatement
of `Query.rewriting_valid_diff_inner_dd` that bridges the `LinearOrder.toDecidableEq`
vs `instDecidableEqSum` mismatch through `Subsingleton.elim`-style conversion).
The (R5) aggregation correctness lives in `Provenance.QueryEvaluateInVK` as
`Query.rewriting_valid_full`, with its V_K interpretation; the syntactic (R5)
rewriting itself is in this file as `Query.rewritingAgg`.

## References

* [Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the Provenance and Probability of Data*][sen2026provsql]
-/

def Query.rewriting [ValueType T] (q: Query T n) (hq: q.noAgg) : Query (T⊕K) (n+1) := match q with
| Rel   n  s  => Rel (n+1) s
| Proj  ts q  =>
  let ts :=
    (λ (k: Fin (n+1)) => if h : ↑k<n then (ts ⟨k,h⟩).castToAnnotatedTuple
                         else Term.index (Fin.last q.arity))
  Proj ts (q.rewriting (noAggProj hq rfl))
| Sel   φ  q  => Sel φ.castToAnnotatedTuple (q.rewriting (noAggSel hq rfl))
| @Prod T n₁ n₂ n hn q₁ q₂ =>
  let tmp :=
    @Query.Prod (T⊕K) (n₁+1) (n₂+1) (n+2) (by omega) (q₁.rewriting (noAggProd hq rfl).left)
  let product := tmp (q₂.rewriting (noAggProd hq rfl).right)
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if ↑k<n₁ then #(k.castLE (by simp))
    else if (↑k<n: Prop) then #(Fin.ofNat _ (↑k+1))
    else Term.mul #(Fin.ofNat _ n₁) #(Fin.ofNat _ (n+1)))
  Proj ts product
| Sum   q₁ q₂ => Sum (q₁.rewriting (noAggSum hq rfl).left) (rewriting q₂ (noAggSum hq rfl).right)
| Dedup q     =>
  let q' := q.rewriting (noAggDedup hq rfl)
  Agg (λ (k: Fin n) ↦ k.castLE (by simp)) ![#(Fin.last n)] ![AggFunc.sum] q'
| Diff  q₁ q₂ =>
  let q'₁ := q₁.rewriting (noAggDiff hq rfl).left
  let q'₂ := q₂.rewriting (noAggDiff hq rfl).right
  let joinCond₁ :=
    ((List.range n).map
      (λ k ↦ @Filter.BT (T⊕K) (2*n+1) (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
      (λ t t' ↦ Filter.And t t') Filter.True
  let prod₁t := λ r ↦ Sel joinCond₁ (@Query.Prod _ (n+1) n (2*n+1) (by omega) q'₁ r)
  let prod₁r := Dedup (Diff (Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (Nat.le_succ _)))) q'₁)
                            (Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (Nat.le_succ _)))) q'₂))
  let prod₁ := prod₁t (prod₁r)
  let joinCond₂ :=
    ((List.range n).map
      (λ k ↦ @Filter.BT (T⊕K) (2*n+2) (#(Fin.ofNat _ k)==#(Fin.ofNat _ (k+n+1))))).foldr
      (λ t t' ↦ Filter.And t t') Filter.True
  have h₂ : (2*n+2 - (n+1): ℕ) = n+1  := by omega
  let prod₂t := λ r ↦ Sel joinCond₂ (@Query.Prod _ (n+1) (n+1) (2*n+2) (by omega) q'₁ r)
  let prod₂r := Agg (λ (k: Fin n) ↦ (k.castLE (by simp))) ![#(Fin.last n)] ![AggFunc.sum] q'₂
  let prod₂ := prod₂t (prod₂r)
  let ts₁ := (λ (k: Fin (n+1)) ↦ #(k.castLE (by omega)))
  let ts₂ := (λ (k: Fin (n+1)) ↦ if ↑k<n then #(k.castLE (by omega))
                                 else Term.sub #(Fin.ofNat _ n) #(Fin.last (2*n+1)))
  Sum (Proj ts₁ prod₁) (Proj ts₂ prod₂)
| Agg _ _ _ _ => by simp[noAgg] at hq

lemma Query.rewriting_valid_prod_heqn (hn: n₁+n₂=n): n₁+1 + (n₂+1) = n+2 := by omega

lemma Query.rewriting_valid_prod0 [Mul K] {n₁ n₂ n: ℕ}
  (hn: n₁+n₂=n)
  (heq : (Fin (n₁ + n₂) → T) = (Fin n → T)):
  ∀ (ar₁: AnnotatedRelation T K n₁) (ar₂: AnnotatedRelation T K n₂), AnnotatedRelation.toComposite
  (Multiset.map (fun x ↦ (cast heq (Fin.append x.1.1 x.2.1), x.1.2 * x.2.2))
    (Multiset.product (ar₁) (ar₂))) = (
      AnnotatedRelation.toComposite
      (Multiset.map (fun x ↦ (Fin.append x.1.1 x.2.1, x.1.2 * x.2.2))
        (Multiset.product (ar₁) (ar₂)))).cast (by simp[hn]) := by
        intro ar₁ ar₂
        subst n
        rw[AnnotatedRelation.cast_toComposite]
        congr
        rfl

lemma cast_apply
  (f: Tuple T n → α)
  (t: Tuple T m)
  (hn: n=m) :
    @cast (Tuple T n → α) (Tuple T m → α) (by simp[hn]) f t
  = f (t.cast (Eq.symm hn)) := by
    subst hn
    simp[Tuple.cast]

lemma Query.rewriting_valid_prod1 {n₁ n:ℕ} [ValueType (T⊕K)]
  (hn: n₁+1+(n₂+1)=n+2)
  (f: (Tuple (T ⊕ K) (n + 2)) → (Tuple (T ⊕ K) (n + 1))):
  ∀ (r: Relation (T⊕K) (n₁+1+(n₂+1))),
  (r.cast hn).map f = r.map (λ t ↦ f (t.cast hn))
    := by
  intro r
  congr 1
  . simp[hn]
  . refine Function.hfunext ?_ ?_
    . simp[hn]
    . intro t t' heq
      rw[Tuple.apply_cast hn f t']
      simp
      rw[cast_apply]
      simp[Tuple.cast]
      apply congrArg
      rw[eq_comm]
      rw[eqRec_eq_cast]
      rw[cast_eq_iff_heq]
      exact (HEq.symm heq)
      simp[hn]
  . exact eqRec_heq _ _

lemma Query.rewriting_append_left
  (t₁: Tuple T n₁)
  (t₂: Tuple T n₂)
  (hn: n₁+n₂=n)
  (k: Fin n)
  (hk: k<n₁):
  (hn ▸ Fin.append t₁ t₂) k = t₁ (k.castLT hk) := by
  subst hn
  simp[Fin.append,Fin.addCases,hk]

lemma Query.rewriting_append_right
  (t₁: Tuple T n₁)
  (t₂: Tuple T n₂)
  (hn: n₁+n₂=n)
  (k: Fin n)
  (hk: ¬k<n₁):
  (hn ▸ Fin.append t₁ t₂) k = t₂ (⟨↑k-n₁, by omega⟩) := by
  subst hn
  simp[Fin.append,Fin.addCases,hk]
  apply congrArg
  refine Fin.eq_of_val_eq ?_
  simp

/-- `Tuple.cast`-flavoured variant of `rewriting_append_left`. Both `Tuple.cast`'s and `▸`'s
`Eq.rec` motives must syntactically agree for `rw` to fire on Lean v4.29; this version
matches the motive produced by `Tuple.cast`. -/
lemma Query.tupleCast_append_left
  (t₁: Tuple T n₁)
  (t₂: Tuple T n₂)
  (hn: n₁+n₂=n)
  (k: Fin n)
  (hk: ↑k<n₁):
  Tuple.cast hn (Fin.append t₁ t₂) k = t₁ (k.castLT hk) := by
  subst hn
  unfold Tuple.cast
  simp[Fin.append,Fin.addCases,hk]

/-- `Tuple.cast`-flavoured variant of `rewriting_append_right`. -/
lemma Query.tupleCast_append_right
  (t₁: Tuple T n₁)
  (t₂: Tuple T n₂)
  (hn: n₁+n₂=n)
  (k: Fin n)
  (hk: ¬↑k<n₁):
  Tuple.cast hn (Fin.append t₁ t₂) k = t₂ ⟨↑k-n₁, by omega⟩ := by
  subst hn
  unfold Tuple.cast
  simp[Fin.append,Fin.addCases,hk]
  apply congrArg
  refine Fin.eq_of_val_eq ?_
  simp

/-!
### Helper lemmas for the `Dedup` case of `rewriting_valid`
-/

/-- Folding `addFn` over a multiset of `Sum.inr k` values in `T⊕K` reduces to the
`Multiset.sum` in `K`, wrapped in `Sum.inr`. -/
lemma Multiset.fold_addFn_map_inr
    {T K: Type} [ValueType T] [SemiringWithMonus K] [HasAltLinearOrder K]
    (m: Multiset K):
  Multiset.fold (@addFn (T⊕K) _) (0: T⊕K) (m.map (fun k ↦ (Sum.inr k: T⊕K)))
  = (Sum.inr m.sum: T⊕K) := by
  induction m using Multiset.induction with
  | empty =>
    simp
    rfl
  | cons hd tl ih =>
    rw[Multiset.map_cons, Multiset.fold_cons_left, ih, Multiset.sum_cons]
    show addFn (Sum.inr hd : T⊕K) (Sum.inr tl.sum) = Sum.inr (hd + tl.sum)
    rfl

/-- Filtering `ar.toComposite` by "first-n columns match `Sum.inl ∘ v`" and projecting to the
last column yields the `Sum.inr`-wrapped annotations of the matching entries of `ar`. -/
lemma AnnotatedRelation.toComposite_filter_map_last
  {T K: Type} [ValueType T] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n) (v: Tuple T n):
  Multiset.map (fun u: Tuple (T⊕K) (n+1) ↦ u (Fin.last n))
    (Multiset.filter
      (fun u: Tuple (T⊕K) (n+1) ↦
        ∀ k': Fin n, u (k'.castLE (Nat.le_succ n)) = (Sum.inl (v k'): T⊕K))
      ar.toComposite)
  = Multiset.map (fun p: AnnotatedTuple T K n ↦ (Sum.inr p.2: T⊕K))
      (Multiset.filter (fun p: AnnotatedTuple T K n ↦ p.1 = v) ar) := by
  unfold AnnotatedRelation.toComposite
  rw[Multiset.filter_map, Multiset.map_map]
  -- Show filters and maps are equal by pointwise agreement
  have hfilter : Multiset.filter
      ((fun u: Tuple (T⊕K) (n+1) ↦
         ∀ k': Fin n, u (k'.castLE (Nat.le_succ n)) = (Sum.inl (v k'): T⊕K))
        ∘ AnnotatedTuple.toComposite) ar
    = Multiset.filter (fun p: AnnotatedTuple T K n ↦ p.1 = v) ar := by
    apply Multiset.filter_congr
    intro p _
    unfold Function.comp AnnotatedTuple.toComposite
    constructor
    · intro h
      funext k
      have hk := h k
      have hcast : k.castLE (Nat.le_succ n) = Fin.castAdd 1 k := rfl
      rw[hcast] at hk
      rw[Fin.append_left] at hk
      simp at hk
      exact hk
    · intro h k
      subst h
      have hcast : k.castLE (Nat.le_succ n) = Fin.castAdd 1 k := rfl
      rw[hcast, Fin.append_left]
  rw[hfilter]
  -- Now show the map functions agree on filtered entries
  apply Multiset.map_congr rfl
  intro p _
  simp only [Function.comp]
  unfold AnnotatedTuple.toComposite
  have : Fin.last n = Fin.natAdd n (0: Fin 1) := by
    apply Fin.eq_of_val_eq; simp
  rw[this, Fin.append_right]
  rfl

/-- The dedup of the first-n projection of `ar.toComposite` is the `Sum.inl`-image of the dedup
of the first-projection of `ar`. -/
lemma AnnotatedRelation.dedup_toComposite_proj_first_n
  {T K: Type} [ValueType T] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n) (h: n ≤ n+1):
  Multiset.dedup
    ((Multiset.map (fun u k ↦ u (Fin.castLE h k)) ar.toComposite: Multiset (Tuple (T⊕K) n)))
  = Multiset.map (fun v ↦ (fun k: Fin n ↦ (Sum.inl (v k): T⊕K) : Tuple (T⊕K) n))
      (Multiset.dedup (Multiset.map Prod.fst ar)) := by
  -- Work around higher-order unification by doing a single change-of-representation.
  -- We show both sides equal `Multiset.map (Sum.inl-lift) (Multiset.map Prod.fst ar).dedup`.
  have h_inj : Function.Injective
      (fun (v : Tuple T n) (k : Fin n) => (Sum.inl (v k) : T⊕K)) := by
    intro v₁ v₂ heq
    funext k
    exact Sum.inl.inj (congrFun heq k)
  have hmap_inner : ∀ p : AnnotatedTuple T K n,
      (fun k : Fin n ↦ p.toComposite (Fin.castLE h k))
    = (fun k : Fin n ↦ (Sum.inl (p.1 k) : T⊕K)) := by
    intro p
    funext k
    unfold AnnotatedTuple.toComposite
    have hcast : k.castLE h = Fin.castAdd 1 k := rfl
    rw [hcast, Fin.append_left]
  calc Multiset.dedup
        ((Multiset.map (fun u k ↦ u (Fin.castLE h k)) ar.toComposite
          : Multiset (Tuple (T⊕K) n)))
      = Multiset.dedup (Multiset.map
          (fun v ↦ (fun k : Fin n ↦ (Sum.inl (v k) : T⊕K) : Tuple (T⊕K) n))
          (Multiset.map Prod.fst ar)) := by
          congr 1
          unfold AnnotatedRelation.toComposite
          rw [Multiset.map_map, Multiset.map_map]
          exact Multiset.map_congr rfl (fun p _ => hmap_inner p)
    _ = Multiset.map (fun v ↦ (fun k : Fin n ↦ (Sum.inl (v k) : T⊕K) : Tuple (T⊕K) n))
          (Multiset.map Prod.fst ar).dedup :=
        Multiset.dedup_map_of_injective h_inj _

/-- Auxiliary: key set of `groupByKey ar` equals first-projection keys of `ar`. -/
lemma groupByKey_key_iff
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n) (v: Tuple T n):
  (∃ w, (v, w) ∈ (groupByKey ar).val) ↔ v ∈ Multiset.map Prod.fst ar := by
  induction ar using Multiset.induction_on with
  | empty =>
    -- Empty case: both sides are empty.
    have hval : (groupByKey (0 : AnnotatedRelation T K n)).val = [] := by
      unfold groupByKey; rfl
    refine ⟨?_, ?_⟩
    · rintro ⟨w, hmem⟩
      have : ¬ (v, w) ∈ (groupByKey (0 : AnnotatedRelation T K n)).val := by
        rw [hval]; exact List.not_mem_nil
      exact absurd hmem this
    · rintro ⟨x, hx⟩
  | @cons p tl ih =>
    have hkv : (groupByKey (p ::ₘ tl)).val = (groupByKey tl).val.addKV p.1 p.2 := by
      unfold groupByKey; rw[Multiset.foldr_cons]; rfl
    show (∃ w, (v, w) ∈ (groupByKey (p ::ₘ tl)).val) ↔
         v ∈ (Multiset.map Prod.fst (p ::ₘ tl) : Multiset (Tuple T n))
    rw[hkv]
    simp only [Multiset.map_cons, Multiset.mem_cons]
    constructor
    · rintro ⟨w, hw⟩
      rw[KeyValueList.addKV_spec _ (groupByKey tl).property] at hw
      rcases hw with ⟨_, hmem⟩ | ⟨heq, _⟩
      · right; exact ih.mp ⟨w, hmem⟩
      · left; exact heq
    · rintro (hpeq | hv)
      · obtain ⟨w, hw⟩ := KeyValueList.addKV_mem _ (groupByKey tl).property p.1 p.2
        refine ⟨w, ?_⟩
        rw[hpeq]
        exact hw
      · obtain ⟨w, hw⟩ := ih.mpr hv
        by_cases hpv : p.1 = v
        · obtain ⟨w', hw'⟩ := KeyValueList.addKV_mem _ (groupByKey tl).property p.1 p.2
          refine ⟨w', ?_⟩
          rw[← hpv]; exact hw'
        · refine ⟨w, ?_⟩
          rw[KeyValueList.addKV_spec _ (groupByKey tl).property]
          left
          refine ⟨fun h ↦ hpv h.symm, hw⟩

/-- Auxiliary: if `(v, w) ∈ (groupByKey ar).val`, then `w` is the semiring-sum of annotations
of entries in `ar` with key `v`. -/
lemma groupByKey_value
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n) (v: Tuple T n) (w: K):
  (v, w) ∈ (groupByKey ar).val →
    w = (Multiset.map Prod.snd
          (Multiset.filter (fun p: AnnotatedTuple T K n ↦ p.1 = v) ar)).sum := by
  induction ar using Multiset.induction_on generalizing w with
  | empty =>
    have hval : (groupByKey (0 : AnnotatedRelation T K n)).val = [] := by
      unfold groupByKey; rfl
    intro hmem
    exfalso
    have hnm : ¬ (v, w) ∈ (groupByKey (0 : AnnotatedRelation T K n)).val := by
      rw [hval]; exact List.not_mem_nil
    exact hnm hmem
  | @cons p tl ih =>
    intro hmem
    have hkv : (groupByKey (p ::ₘ tl)).val = (groupByKey tl).val.addKV p.1 p.2 := by
      unfold groupByKey; rw[Multiset.foldr_cons]; rfl
    change (v, w) ∈ (groupByKey (p ::ₘ tl)).val at hmem
    rw[hkv] at hmem
    rw[KeyValueList.addKV_spec _ (groupByKey tl).property] at hmem
    by_cases hpv : p.1 = v
    · -- p.1 = v
      show w = (Multiset.map Prod.snd (Multiset.filter (fun p : AnnotatedTuple T K n ↦ p.1 = v)
        ((p : AnnotatedTuple T K n) ::ₘ (tl : Multiset (AnnotatedTuple T K n))))).sum
      rw [Multiset.filter_cons, if_pos hpv, Multiset.map_add, Multiset.sum_add,
          Multiset.map_singleton, Multiset.sum_singleton]
      rcases hmem with ⟨hne, _⟩ | ⟨_, hdisj⟩
      · exact absurd hpv.symm hne
      · rcases hdisj with ⟨hnone, hw⟩ | ⟨z, hz, hw⟩
        · -- (v, w) = (p.1, p.2) and no entry with key p.1 in groupByKey tl
          have hw_eq : w = p.2 := ((Prod.mk.injEq _ _ _ _).mp hw).2
          -- The remaining filter over `tl` is empty.
          have hnokey : ¬ v ∈ Multiset.map Prod.fst tl := by
            intro h
            apply hnone
            rw [hpv]
            exact (groupByKey_key_iff tl v).mpr h
          have hfilter_eq : Multiset.filter (fun p : AnnotatedTuple T K n ↦ p.1 = v) tl = 0 :=
            Multiset.filter_eq_nil.mpr (fun q hq hq1 =>
              hnokey (Multiset.mem_map.mpr ⟨q, hq, hq1⟩))
          have hmap_filter_empty : (Multiset.map Prod.snd
              (Multiset.filter (fun p : AnnotatedTuple T K n ↦ p.1 = v) tl)).sum = 0 := by
            convert Multiset.sum_zero
            convert Multiset.map_zero (Prod.snd : AnnotatedTuple T K n → K)
          rw [hmap_filter_empty, add_zero]
          exact hw_eq
        · -- (v, w) = (p.1, p.2 + z) with (p.1, z) ∈ groupByKey tl
          have hv_eq : v = p.1 := ((Prod.mk.injEq _ _ _ _).mp hw).1
          have hw_eq : w = p.2 + z := ((Prod.mk.injEq _ _ _ _).mp hw).2
          have hz' : (v, z) ∈ (groupByKey tl).val := hv_eq ▸ hz
          rw[hw_eq, ih z hz']
    · -- p.1 ≠ v
      show w = (Multiset.map Prod.snd (Multiset.filter (fun p : AnnotatedTuple T K n ↦ p.1 = v)
        ((p : AnnotatedTuple T K n) ::ₘ (tl : Multiset (AnnotatedTuple T K n))))).sum
      rw [Multiset.filter_cons, if_neg hpv, zero_add]
      rcases hmem with ⟨_, hmem⟩ | ⟨heq, _⟩
      · exact ih w hmem
      · exact absurd heq.symm hpv

/-- `groupByKey ar`, as a multiset, equals the dedup of the first-projection of `ar`, with each
key paired with the semiring-sum of annotations sharing that key. -/
lemma groupByKey_multiset_eq
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n):
  (Multiset.ofList (groupByKey ar).val: Multiset (AnnotatedTuple T K n))
  = Multiset.map
      (fun v: Tuple T n ↦
        (v, (Multiset.map Prod.snd
              (Multiset.filter (fun p: AnnotatedTuple T K n ↦ p.1 = v) ar)).sum))
      (Multiset.dedup (Multiset.map Prod.fst ar)) := by
  have hLNodup : (Multiset.ofList (groupByKey ar).val :
      Multiset (AnnotatedTuple T K n)).Nodup := by
    rw[Multiset.coe_nodup]
    exact KeyValueList.nodup _ (groupByKey ar).property
  have hRNodup : (Multiset.map
      (fun v: Tuple T n ↦ (v, (Multiset.map Prod.snd (Multiset.filter (fun p ↦ p.1 = v) ar)).sum))
      (Multiset.dedup (Multiset.map Prod.fst ar))).Nodup := by
    apply Multiset.Nodup.map
    · intro v₁ v₂ heq
      exact (Prod.mk.injEq _ _ _ _).mp heq |>.1
    · exact Multiset.nodup_dedup _
  refine (Multiset.Nodup.ext hLNodup hRNodup).mpr ?_
  rintro ⟨v, w⟩
  show (v, w) ∈ (Multiset.ofList (groupByKey ar).val : Multiset (AnnotatedTuple T K n)) ↔
       (v, w) ∈ Multiset.map (fun v: Tuple T n ↦
         (v, (Multiset.map Prod.snd (Multiset.filter (fun p : AnnotatedTuple T K n ↦ p.1 = v) ar)).sum))
         (Multiset.dedup (Multiset.map Prod.fst ar))
  simp only [Multiset.mem_map]
  constructor
  · intro hmem
    refine ⟨v, ?_, ?_⟩
    · rw[Multiset.mem_dedup]
      exact (groupByKey_key_iff ar v).mp ⟨w, hmem⟩
    · have hw := groupByKey_value ar v w hmem
      congr 1
      exact hw.symm
  · rintro ⟨v', hv', heq⟩
    rw[Multiset.mem_dedup] at hv'
    obtain ⟨w', hw'⟩ := (groupByKey_key_iff ar v').mpr hv'
    have hval := groupByKey_value ar v' w' hw'
    injection heq with heq1 heq2
    subst heq1
    have : w = w' := heq2.symm.trans hval.symm
    rw[this]
    exact hw'

/-!
### Helper lemmas for the `Diff` case of `rewriting_valid`
-/

/-- `Multiset.dedup` only depends on the `DecidableEq` instance up to subsingleton equality. -/
lemma Multiset.dedup_eq_of_instances {α : Type*} (inst₁ inst₂ : DecidableEq α) (m : Multiset α) :
  @Multiset.dedup α inst₁ m = @Multiset.dedup α inst₂ m := by
  congr
  apply Subsingleton.elim

/-- `Multiset.filter` only depends on the `DecidablePred` instance up to subsingleton equality. -/
lemma Multiset.filter_eq_of_instances {α : Type*} (p : α → Prop)
  (inst₁ inst₂ : DecidablePred p) (m : Multiset α) :
  @Multiset.filter α p inst₁ m = @Multiset.filter α p inst₂ m := by
  congr

/-- Folded `Filter.And` over a mapped list is equivalent to the universal conjunction. -/
lemma Filter.eval_foldr_and_map {T: Type} [ValueType T] {N: ℕ} {α : Type*}
  (list: List α) (f: α → Filter T N) (t: Tuple T N):
  Filter.eval
    ((list.map f).foldr (λ t t' ↦ Filter.And t t') Filter.True) t
  ↔ ∀ x ∈ list, Filter.eval (f x) t := by
  induction list with
  | nil => simp [Filter.eval]
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldr_cons, Filter.eval, List.mem_cons]
    rw[ih]
    constructor
    · rintro ⟨hhd, htl⟩ x (rfl | hx)
      · exact hhd
      · exact htl x hx
    · intro h
      exact ⟨h hd (Or.inl rfl), fun x hx ↦ h x (Or.inr hx)⟩

/-- The folded join condition `(#k == #(k+n+1))` for `k ∈ List.range n` evaluates true iff the
tuple's values at indices `ofNat k` and `ofNat (k+n+1)` agree for every `k < n`. -/
lemma Query.rewriting_valid_joinCond_eval
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
  {N n: ℕ} [NeZero N] (t: Tuple (T⊕K) N):
  Filter.eval
    (((List.range n).map
      (λ k ↦ @Filter.BT (T⊕K) N
        (#(Fin.ofNat N k) == #(Fin.ofNat N (k+n+1))))).foldr
      (λ t t' ↦ Filter.And t t') Filter.True) t
  ↔ ∀ k: Fin n, t (@Fin.ofNat N _ k)
              = t (@Fin.ofNat N _ (k+n+1)) := by
  rw[Filter.eval_foldr_and_map]
  simp only [List.mem_range]
  constructor
  · intro h k
    have := h k.val k.isLt
    simpa [Filter.eval, BoolTerm.eval, Term.eval] using this
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa [Filter.eval, BoolTerm.eval, Term.eval] using this

/-- Semiring-sum over the filter, via `groupByKey.find?`-based lookup. -/
lemma Query.rewriting_valid_find_getD_eq_sum
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n) (u: Tuple T n):
  (((groupByKey ar).val.find? (·.1 = u)).map Prod.snd).getD 0
  = (Multiset.map Prod.snd
      (Multiset.filter (fun p: AnnotatedTuple T K n ↦ p.1 = u) ar)).sum := by
  cases hfind : (groupByKey ar).val.find? (·.1 = u) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    -- u is not a key of ar, so filter is empty, sum is 0
    have hnone : ¬ ∃ w, (u, w) ∈ (groupByKey ar).val := by
      intro ⟨w, hmem⟩
      rw[List.find?_eq_none] at hfind
      have := hfind (u, w) hmem
      simp at this
    have hnotinkeys : u ∉ Multiset.map Prod.fst ar :=
      fun h ↦ hnone ((groupByKey_key_iff ar u).mpr h)
    -- Avoid `rw` on `filter` (DecidablePred instance divergence with `Tuple` def).
    -- Instead work at the `sum`/`map` level via `convert`.
    have hfilter_eq : Multiset.filter (fun p : AnnotatedTuple T K n ↦ p.1 = u) ar = 0 :=
      Multiset.filter_eq_nil.mpr (fun q hq hq1 =>
        hnotinkeys (Multiset.mem_map.mpr ⟨q, hq, hq1⟩))
    have hmap_filter_empty : (Multiset.map Prod.snd
        (Multiset.filter (fun p : AnnotatedTuple T K n ↦ p.1 = u) ar)).sum = 0 := by
      convert Multiset.sum_zero
      convert Multiset.map_zero (Prod.snd : AnnotatedTuple T K n → K)
    exact hmap_filter_empty.symm
  | some vw =>
    simp only [Option.map_some, Option.getD_some]
    -- vw ∈ groupByKey and vw.1 = u
    have hmem : vw ∈ (groupByKey ar).val := List.mem_of_find?_eq_some hfind
    have hcond : vw.1 = u := by
      have := List.find?_some hfind
      simpa using this
    obtain ⟨v, w⟩ := vw
    simp at hcond
    subst hcond
    exact groupByKey_value ar v w hmem

/-- Subtraction distributes over `Sum.inr` in `T⊕K`. -/
lemma Query.rewriting_valid_sub_inr
  {T K: Type} [ValueType T] [HasAltLinearOrder K] [SemiringWithMonus K] (a b: K):
  ((Sum.inr a: T⊕K) - Sum.inr b) = Sum.inr (a - b) := by
  rfl

/-- Non-dedup form of `dedup_toComposite_proj_first_n`: the first-`n` projection of
`ar.toComposite` is the `Sum.inl`-lift of the first-projection of `ar`. -/
lemma AnnotatedRelation.toComposite_proj_first_n
  {T K: Type} [ValueType T] {n: ℕ}
  (ar: AnnotatedRelation T K n) (h: n ≤ n+1):
  Multiset.map (fun (u: Tuple (T⊕K) (n+1)) ↦
      ((fun (k: Fin n) ↦ u (Fin.castLE h k)) : Tuple (T⊕K) n))
    ar.toComposite
  = Multiset.map (fun (v: Tuple T n) ↦
      ((fun (k: Fin n) ↦ (Sum.inl (v k): T⊕K)) : Tuple (T⊕K) n))
      (Multiset.map Prod.fst ar) := by
  unfold AnnotatedRelation.toComposite
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  simp only [Function.comp]
  funext k
  unfold AnnotatedTuple.toComposite
  have hcast : Fin.castLE h k = Fin.castAdd 1 k := rfl
  rw[hcast, Fin.append_left]

/-- `Sum.inl`-lift of tuples is injective. -/
lemma Sum.inl_lift_injective {T K: Type} {n: ℕ}:
  Function.Injective (fun (v: Tuple T n) (k: Fin n) ↦ (Sum.inl (v k): T⊕K)) := by
  intro v₁ v₂ heq
  funext k
  exact Sum.inl.inj (congrFun heq k)

/-- Filtering by "not a member of an injective image" pulls through the map. -/
lemma Multiset.filter_notMem_map_of_injective
  {α β: Type*} [DecidableEq α] [DecidableEq β] {f: α → β} (hf: Function.Injective f)
  (m: Multiset α) (s: Multiset α):
  Multiset.filter (fun b ↦ b ∉ Multiset.map f s) (Multiset.map f m)
  = Multiset.map f (Multiset.filter (fun a ↦ a ∉ s) m) := by
  rw[Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro a _
  simp [Function.comp, Multiset.mem_map, hf.eq_iff]

/-- Helper: the data part `Tuple.fromComposite` and `AnnotatedTuple.toComposite` agree on data. -/
lemma AnnotatedTuple.toComposite_castLE
  {T K: Type} [Zero K] {n: ℕ} (p: AnnotatedTuple T K n) (k: Fin n):
  p.toComposite (k.castLE (Nat.le_succ n)) = Sum.inl (p.1 k) := by
  unfold AnnotatedTuple.toComposite
  have hcast : k.castLE (Nat.le_succ n) = Fin.castAdd 1 k := rfl
  rw[hcast, Fin.append_left]

/-- The annotation part of `p.toComposite` is `Sum.inr p.2`. -/
lemma AnnotatedTuple.toComposite_last
  {T K: Type} [Zero K] {n: ℕ} (p: AnnotatedTuple T K n):
  p.toComposite (Fin.last n) = (Sum.inr p.2: T⊕K) := by
  unfold AnnotatedTuple.toComposite
  have : Fin.last n = Fin.natAdd n (0: Fin 1) := by
    apply Fin.eq_of_val_eq; simp
  rw[this, Fin.append_right]
  rfl

/-- Roundtrip: `Tuple.fromComposite ∘ AnnotatedTuple.toComposite = id`. The
composite encoding loses no information: peeling the data columns and the
annotation column back out reconstructs the original annotated tuple. -/
lemma Tuple.fromComposite_toComposite
  {T K: Type} [ValueType T] [Zero K] {n: ℕ} (p: AnnotatedTuple T K n):
  Tuple.fromComposite p.toComposite = p := by
  apply Prod.ext
  · funext k
    show (match p.toComposite (k.castLE (Nat.le_succ n)) with
            | Sum.inl x => x | Sum.inr _ => 0) = p.1 k
    rw [AnnotatedTuple.toComposite_castLE]
  · show (match p.toComposite (Fin.last n) with
            | Sum.inl _ => 0 | Sum.inr x => x) = p.2
    rw [AnnotatedTuple.toComposite_last]

/-- Pushforward version of `Tuple.fromComposite_toComposite`: mapping
`Tuple.fromComposite` over a composite-encoded annotated relation recovers
the original annotated relation. -/
lemma AnnotatedRelation.map_fromComposite_toComposite
  {T K: Type} [ValueType T] [Zero K] {n: ℕ} (r: AnnotatedRelation T K n):
  Multiset.map Tuple.fromComposite r.toComposite = r := by
  unfold AnnotatedRelation.toComposite
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id r]
  apply Multiset.map_congr rfl
  intro p _
  exact Tuple.fromComposite_toComposite p

/-- Reduction of the inner `Dedup ∘ Diff ∘ Proj` block of the `Diff` rewriting:
    deduping the difference of first-`n` projections of `AR₁.toComposite` and `AR₂.toComposite`
    yields the `Sum.inl`-lift of the deduped "unmatched-keys" filter over the data part.
    Stated using `Fin.castLE` (function form) and dot notation (`.dedup`) so the LHS
    pattern matches what `simp only [evaluate]` produces in the `Diff` case of
    `rewriting_valid`. -/
lemma Query.rewriting_valid_diff_inner_dd
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] {n: ℕ}
  (AR₁ AR₂: AnnotatedRelation T K n):
  (Multiset.filter
    (fun u: Tuple (T⊕K) n ↦
      u ∉ Multiset.map
            (fun (u': Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
            AR₂.toComposite)
    (Multiset.map
      (fun (u': Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
      AR₁.toComposite)).dedup
  = Multiset.map (fun (v: Tuple T n) (k: Fin n) ↦ (Sum.inl (v k): T⊕K))
      (Multiset.filter (fun v ↦ v ∉ Multiset.map Prod.fst AR₂)
        (Multiset.map Prod.fst AR₁)).dedup := by
  -- Unfold toComposite, fuse Multiset.map, simplify pointwise via `hcomp`.
  unfold AnnotatedRelation.toComposite
  simp only [Multiset.map_map, Function.comp_def]
  have hcomp : ∀ (p : AnnotatedTuple T K n) (k : Fin n),
      p.toComposite (k.castLE (Nat.le_succ n)) = (Sum.inl (p.1 k) : T⊕K) :=
    fun p k => AnnotatedTuple.toComposite_castLE p k
  simp only [hcomp]
  -- Now both inner `map`s have the curried form `λp k. Sum.inl (p.1 k)`.
  -- We need to convert this into `(Sum.inl-lift) ∘ Prod.fst` form so that injectivity applies.
  -- `rw` is fragile here (HOU on Lean v4.29); fall back to `Multiset.Nodup.ext`.
  refine (Multiset.Nodup.ext (Multiset.nodup_dedup _) ?_).mpr ?_
  · exact (Multiset.nodup_dedup _).map (fun _ _ heq => Sum.inl_lift_injective heq)
  intro u
  constructor
  · intro hLHS
    have hmem₁ := Multiset.mem_dedup.mp hLHS
    rw [Multiset.mem_filter] at hmem₁
    obtain ⟨hmem_map, hnot⟩ := hmem₁
    obtain ⟨p, hp, hp_eq⟩ := Multiset.mem_map.mp hmem_map
    refine Multiset.mem_map.mpr ⟨p.1, ?_, hp_eq⟩
    refine Multiset.mem_dedup.mpr ?_
    rw [Multiset.mem_filter]
    refine ⟨?_, ?_⟩
    · refine Multiset.mem_map.mpr ⟨p, hp, rfl⟩
    · intro hmem₂
      apply hnot
      obtain ⟨q, hq, hq_eq⟩ := Multiset.mem_map.mp hmem₂
      refine Multiset.mem_map.mpr ⟨q, hq, ?_⟩
      funext k
      rw [← hp_eq]
      exact congrArg (fun (v: Tuple T n) ↦ (Sum.inl (v k) : T⊕K)) hq_eq
  · intro hRHS
    obtain ⟨v, hv, hv_eq⟩ := Multiset.mem_map.mp hRHS
    have hv₁ := Multiset.mem_dedup.mp hv
    rw [Multiset.mem_filter] at hv₁
    obtain ⟨hv_in_keys, hnot⟩ := hv₁
    obtain ⟨p, hp, hpv⟩ := Multiset.mem_map.mp hv_in_keys
    refine Multiset.mem_dedup.mpr ?_
    rw [Multiset.mem_filter]
    refine ⟨?_, ?_⟩
    · refine Multiset.mem_map.mpr ⟨p, hp, ?_⟩
      funext k
      rw [← hv_eq, ← hpv]
    · intro hmem₂
      apply hnot
      obtain ⟨q, hq, hq_eq⟩ := Multiset.mem_map.mp hmem₂
      refine Multiset.mem_map.mpr ⟨q, hq, ?_⟩
      funext k
      apply Sum.inl.inj
      have : (fun k ↦ (Sum.inl (q.1 k) : T⊕K)) = u := hq_eq
      rw [← hv_eq] at this
      exact congrFun this k

/-- `Relation.cast` rewrites to a `Multiset.map` of `Tuple.cast`. -/
lemma Relation.cast_eq_map {T : Type} {n m : ℕ} (h : n = m) (r : Relation T n) :
    r.cast h = r.map (Tuple.cast h) := (Relation.cast_eq r _ h).mp rfl

/-- Filter pushes through `AnnotatedRelation.toComposite` via the
`Tuple.fromComposite ∘ AnnotatedTuple.toComposite = id` roundtrip:
filtering before taking the composite encoding equals filtering the composite
encoding by the same predicate composed with `Tuple.fromComposite`. -/
lemma AnnotatedRelation.toComposite_filter
    {T K : Type} [ValueType T] [Zero K] {n : ℕ}
    (ar : AnnotatedRelation T K n) (pred : AnnotatedTuple T K n → Prop)
    [DecidablePred pred] :
    AnnotatedRelation.toComposite (Multiset.filter pred ar)
    = ar.toComposite.filter (fun t : Tuple (T⊕K) (n+1) ↦ pred (Tuple.fromComposite t)) := by
  unfold AnnotatedRelation.toComposite
  rw [Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro p _
  rw [Function.comp_apply, Tuple.fromComposite_toComposite]

/-- **Semijoin reduction.** Given multisets `r : Multiset α` and `s : Multiset β` and
a key function `g : α → β`, with `s` `Nodup`, the projection-after-filter of the
cartesian product (keeping pairs whose `g`-image matches) coincides with filtering
`r` to those `a` whose `g a` belongs to `s`. This is the multiset version of the
relational semijoin and is the structural identity behind the `unmatched_eq`
half of the `Diff`-case rewriting correctness. -/
lemma Multiset.semijoin_proj_eq_filter {α β : Type*} [DecidableEq β]
    (r : Multiset α) (s : Multiset β) (g : α → β) (hs : s.Nodup) :
    ((r ×ˢ s).filter (fun pair : α × β ↦ g pair.1 = pair.2)).map Prod.fst
    = r.filter (fun a ↦ g a ∈ s) := by
  induction r using Multiset.induction with
  | empty => simp
  | cons hd tl ih =>
    rw [Multiset.cons_product, Multiset.filter_add, Multiset.map_add, ih,
        Multiset.filter_cons]
    congr 1
    -- Show ((s.map (Prod.mk hd)).filter (fun pair => g pair.1 = pair.2)).map Prod.fst
    --    = if g hd ∈ s then {hd} else 0
    rw [Multiset.filter_map, Multiset.map_map]
    -- Goal: (s.filter (fun b => g hd = b)).map (Prod.fst ∘ Prod.mk hd) = ...
    show (s.filter (fun b ↦ g hd = b)).map (fun _ ↦ hd) = _
    by_cases hgmem : g hd ∈ s
    · -- s.filter (g hd = ·) = {g hd} since s is Nodup; map by constant gives {hd}.
      rw [if_pos hgmem]
      have hcount : s.count (g hd) = 1 := Multiset.count_eq_one_of_mem hs hgmem
      -- Convert filter to count.
      have hfilter_eq : s.filter (fun b ↦ g hd = b) = {g hd} := by
        ext b
        rw [Multiset.count_filter, Multiset.count_singleton]
        by_cases hb : g hd = b
        · subst hb
          rw [if_pos rfl]
          exact hcount.trans (if_pos rfl).symm
        · simp [hb, Ne.symm hb]
      rw [hfilter_eq, Multiset.map_singleton]
    · -- s.filter (g hd = ·) = 0 since g hd ∉ s; map gives 0.
      rw [if_neg hgmem]
      have hfilter_eq : s.filter (fun b ↦ g hd = b) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro b hb heq
        exact hgmem (heq ▸ hb)
      rw [hfilter_eq, Multiset.map_zero]

/-- Instance-polymorphic restatement of `Query.rewriting_valid_diff_inner_dd`.
Inside the `Diff` case of `rewriting_valid`, Lean's instance synthesis picks
inconsistent `DecidableEq (T⊕K)` instances at different positions in the goal:
the inner `Multiset.dedup` is elaborated with `LinearOrder.toDecidableEq` (via
`ValueType (T⊕K)`), while the surrounding `Multiset.filter`'s `decidableMem`
uses `instDecidableEqSum`. This wrapper accepts both as explicit parameters and
bridges to the canonical helper via `Subsingleton.elim`. -/
lemma Query.rewriting_valid_diff_inner_dd_inst
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] {n: ℕ}
  (AR₁ AR₂ : AnnotatedRelation T K n)
  (instA : DecidableEq (Tuple (T⊕K) n))
  (instDP : DecidablePred (fun u : Tuple (T⊕K) n ↦
      u ∉ @Multiset.map (Tuple (T⊕K) (n+1)) (Tuple (T⊕K) n)
            (fun (u': Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
            AR₂.toComposite)) :
  @Multiset.dedup _ instA
    (@Multiset.filter _ _ instDP
      (@Multiset.map (Tuple (T⊕K) (n+1)) (Tuple (T⊕K) n)
        (fun (u': Tuple (T⊕K) (n+1)) (k: Fin n) ↦ u' (Fin.castLE (Nat.le_succ n) k))
        AR₁.toComposite))
  = Multiset.map (fun (v: Tuple T n) (k: Fin n) ↦ (Sum.inl (v k): T⊕K))
      (Multiset.filter (fun v ↦ v ∉ Multiset.map Prod.fst AR₂)
        (Multiset.map Prod.fst AR₁)).dedup := by
  convert Query.rewriting_valid_diff_inner_dd AR₁ AR₂ using 4

theorem Query.rewriting_valid
  [ValueType T] [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
  (q: Query T n) (hq: q.noAgg) :
  ∀ (d: AnnotatedDatabase T K), (q.evaluateAnnotated hq d).toComposite = (q.rewriting hq).evaluate d.toComposite := by
  intro d
  induction q with
  | Rel n s =>
    unfold evaluateAnnotated evaluate rewriting
    simp
    match ha: AnnotatedDatabase.find n s d with
    | none =>
      rw[AnnotatedDatabase.find_toComposite_none] at ha
      rw[ha]
      simp[AnnotatedRelation.toComposite]
    | some rn =>
      rw[AnnotatedDatabase.find_toComposite_some] at ha
      rw[ha]
  | @Proj m n' ts q ih =>
    unfold evaluateAnnotated evaluate rewriting
    simp
    rw[← ih (noAggProj hq rfl)]
    unfold AnnotatedRelation.toComposite
    simp
    apply congrFun
    apply congrArg
    funext t k
    by_cases hkn' : k=Fin.last n'
    . simp[hkn']
      simp[Term.eval]
      unfold Query.arity
      have : ∀ x, Fin.last x = Fin.natAdd (Fin.last x) 0 := by
        simp
        intro x
        rfl
      rw[this n',this m]
      unfold AnnotatedTuple.toComposite
      simp [Fin.append_right]
    . simp at hkn'
      have hlt := Fin.val_lt_last hkn'
      simp[hlt]
      have : k = (Fin.castAdd 1 (k.castLT hlt): Fin (n'+1)) := by simp
      rewrite (occs := [1]) [this]
      unfold AnnotatedTuple.toComposite
      rw [Fin.append_left]
      rw[Term.castToAnnotatedTuple_eval]
      rfl
  | Sel φ q' ih =>
    unfold evaluateAnnotated evaluate rewriting
    simp
    rw[← ih (noAggSel hq rfl)]
    unfold AnnotatedRelation.toComposite
    rw[Multiset.filter_map]
    apply congrArg
    apply congrFun
    simp[Function.comp_def]
    unfold AnnotatedTuple.toComposite
    conv =>
      rhs
      congr
      . ext x
        rw[Filter.castToAnnotatedTuple_eval φ]
        skip
      . apply φ.evalDecidableAnnotated
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    unfold evaluateAnnotated evaluate rewriting
    simp
    have heq : (Fin (n₁ + n₂) → T) = (Fin n → T) := by simp[hn]
    rw[Query.rewriting_valid_prod0 hn heq]
    rw[AnnotatedRelation.toComposite_map_product]
    rw[ih₁ (noAggProd hq rfl).left]
    rw[ih₂ (noAggProd hq rfl).right]
    simp
    rw[eq_comm]
    rw[Relation.cast_eq]
    conv_lhs =>
      unfold evaluate
      simp[(·*·)]
      skip
    rw[rewriting_valid_prod1 (rewriting_valid_prod_heqn hn)]
    -- Lean v4.29's pattern unifier cannot find `Multiset.map (Multiset.map ...)` in either
    -- side because `Tuple.cast`/`Fin.append` hide the codomain through their motives.
    -- Reduce both sides to a single `Multiset.map` by exposing the head structure via
    -- `Eq.trans` with the desired `Multiset.map_map` instance – letting Lean infer the
    -- specific function arguments avoids the failing higher-order match.
    refine Eq.trans (Multiset.map_map _ _ _) (Eq.trans ?_ (Multiset.map_map _ _ _).symm)
    apply Multiset.map_congr rfl
    intro p _
    simp only [Function.comp]
    funext k
    rw[Tuple.cast_get]
    subst hn
    by_cases hlt₁: ↑k < n₁
    . simp[hlt₁]
      simp only[Term.eval]
      have hksucc : ↑(Fin.castLE (by omega : n₁+n₂+1 ≤ n₁+n₂+2) k) < n₁+1 := by simp; omega
      rw[tupleCast_append_left (n:=n₁+n₂+2) p.1 p.2 (by omega) _ hksucc]
      apply congrArg
      refine Fin.eq_of_val_eq ?_
      simp[Fin.castLT]
    . by_cases hlt: ↑k < n₁+n₂
      . simp[hlt₁,hlt]
        simp only[Term.eval]
        simp only [← Fin.ofNat_eq_cast]
        have hk₁₂: ((k:ℕ)+1)<n₁+n₂+2 := by omega
        rw[tupleCast_append_right (n:=n₁+n₂+2) p.1 p.2 (by omega)
              (Fin.ofNat (n₁+n₂+2) ((k:ℕ)+1))
              (by simp [Fin.ofNat, Nat.mod_eq_of_lt hk₁₂]; omega)]
        apply congrArg
        refine Fin.eq_of_val_eq ?_
        have hkn1 : ((k:ℕ)-n₁)<n₂+1 := by omega
        simp [Fin.ofNat, Nat.mod_eq_of_lt hk₁₂, Nat.mod_eq_of_lt hkn1]
      . simp[hlt₁,hlt]
        simp only[Term.eval]
        simp only [← Fin.ofNat_eq_cast]
        have hn1 : n₁<n₁+n₂+2 := by omega
        rw[tupleCast_append_left (n:=n₁+n₂+2) p.1 p.2 (by omega)
              (Fin.ofNat (n₁+n₂+2) n₁) (by simp [Fin.ofNat, Nat.mod_eq_of_lt hn1])]
        rw[tupleCast_append_right (n:=n₁+n₂+2) p.1 p.2 (by omega)
              (Fin.last (n₁+n₂+1)) (by simp)]
        congr
        . apply congrArg
          apply Fin.eq_of_val_eq
          simp [Fin.castLT, Fin.ofNat, Nat.mod_eq_of_lt hn1]
        . apply congrArg
          apply Fin.eq_of_val_eq
          simp
  | Sum q₁ q₂ ih₁ ih₂ =>
    unfold evaluateAnnotated evaluate rewriting
    simp
    rw[ih₁ (noAggSum hq rfl).left]
    rw[ih₂ (noAggSum hq rfl).right]
  | Dedup q ih =>
    have hq' := noAggDedup hq rfl
    have ih' := ih hq'
    -- LHS = common form
    have lhs_eq :
      AnnotatedRelation.toComposite
        (Multiset.ofList (groupByKey (q.evaluateAnnotated hq' d)).val :
          AnnotatedRelation T K _)
      = Multiset.map
          (fun v: Tuple T _ ↦
            AnnotatedTuple.toComposite
              (v, (Multiset.map Prod.snd
                    (Multiset.filter (fun p: AnnotatedTuple T K _ ↦ p.1 = v)
                      (q.evaluateAnnotated hq' d))).sum))
          (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq' d))) := by
      unfold AnnotatedRelation.toComposite
      rw[groupByKey_multiset_eq]
      exact Multiset.map_map _ _ _
    -- RHS = common form
    have rhs_eq :
      evaluate ((Dedup q).rewriting hq) d.toComposite
      = Multiset.map
          (fun v: Tuple T _ ↦
            AnnotatedTuple.toComposite
              (v, (Multiset.map Prod.snd
                    (Multiset.filter (fun p: AnnotatedTuple T K _ ↦ p.1 = v)
                      (q.evaluateAnnotated hq' d))).sum))
          (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq' d))) := by
      unfold rewriting evaluate
      simp only [evaluate, Term.eval]
      rw[← ih']
      apply Eq.trans (b := Multiset.map _
        (Multiset.map (fun v ↦ (fun k: Fin _ ↦ (Sum.inl (v k): T⊕K)))
          (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq' d)))))
      · apply congrArg
        convert AnnotatedRelation.dedup_toComposite_proj_first_n
          (q.evaluateAnnotated hq' d) (Nat.le_succ _) using 2
      · rw[Multiset.map_map]
        apply Multiset.map_congr rfl
        intro v _hv
        simp only [Function.comp, Matrix.cons_val_fin_one, Term.eval]
        rw[AnnotatedRelation.toComposite_filter_map_last]
        simp only [AggFunc.eval]
        rw[show (fun p: AnnotatedTuple T K _ ↦ (Sum.inr p.2: T⊕K))
              = (fun k ↦ (Sum.inr k: T⊕K)) ∘ Prod.snd from rfl]
        -- Prove both sides equal via pointwise funext into the Fin.append/toComposite structure.
        unfold AnnotatedTuple.toComposite
        funext k
        rename_i n
        by_cases hk: k = Fin.last n
        · subst hk
          simp [Fin.append, Fin.addCases]
          -- Under the last component, we need fold-addFn-map-inr applied.
          show Multiset.fold addFn (0 : T⊕K)
              (Multiset.map (fun x : AnnotatedTuple T K _ ↦ (Sum.inr x.2 : T⊕K))
                (Multiset.filter (fun p : AnnotatedTuple T K _ ↦ p.1 = v)
                  (q.evaluateAnnotated hq' d)))
            = (Sum.inr (Multiset.map Prod.snd (Multiset.filter
                (fun p : AnnotatedTuple T K _ ↦ p.1 = v)
                (q.evaluateAnnotated hq' d))).sum : T⊕K)
          rw [show Multiset.map (fun x : AnnotatedTuple T K _ ↦ (Sum.inr x.2 : T⊕K))
                (Multiset.filter (fun p : AnnotatedTuple T K _ ↦ p.1 = v)
                  (q.evaluateAnnotated hq' d))
              = Multiset.map (fun k : K ↦ (Sum.inr k : T⊕K))
                  (Multiset.map Prod.snd
                    (Multiset.filter (fun p : AnnotatedTuple T K _ ↦ p.1 = v)
                      (q.evaluateAnnotated hq' d))) from
            (Multiset.map_map _ _ _).symm]
          exact Multiset.fold_addFn_map_inr _
        · have hlt : (k: ℕ) < n := Fin.val_lt_last hk
          simp [Fin.append, Fin.addCases, hlt]
    rw[← lhs_eq] at rhs_eq
    unfold evaluateAnnotated
    exact rhs_eq.symm
  | Diff q₁ q₂ ih₁ ih₂ =>
    have hq'₁ := (noAggDiff hq rfl).left
    have hq'₂ := (noAggDiff hq rfl).right
    have ih'₁ := ih₁ hq'₁
    have ih'₂ := ih₂ hq'₂
    -- LHS: (ar₁.map (fun (u,α) ↦ (u, α - β_u))).toComposite
    -- where β_u = sum of annotations of u in ar₂.
    -- Rewrite β_u via find?/getD using our helper.
    -- Common form: each tuple from ar₁ with its annotation minus ar₂'s matching sum.
    have lhs_eq :
      AnnotatedRelation.toComposite
        ((q₁.evaluateAnnotated hq'₁ d).map (fun p: AnnotatedTuple T K _ ↦
          (p.1, p.2 - (Multiset.map Prod.snd
            (Multiset.filter (fun q: AnnotatedTuple T K _ ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d))).sum)))
      = ((Diff q₁ q₂).evaluateAnnotated hq d).toComposite := by
      show _ = AnnotatedRelation.toComposite _
      congr 1
      apply Multiset.map_congr rfl
      intro p _
      congr 1
      rw[← Query.rewriting_valid_find_getD_eq_sum (q₂.evaluateAnnotated hq'₂ d) p.1]
    -- RHS = evaluate (Sum (Proj ts₁ prod₁) (Proj ts₂ prod₂)) d.toComposite
    rename_i n -- bring the arity variable into scope as `n`
    -- The unmatched part of the rewriting (coming from `Proj ts₁ prod₁`).
    have unmatched_eq :
      evaluate
        (Query.Proj (fun (k: Fin (n+1)) ↦ #(k.castLE (by omega)))
          (Query.Sel (((List.range n).map
              (λ k ↦ @Filter.BT (T⊕K) (2*n+1)
                (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
              (λ t t' ↦ Filter.And t t') Filter.True)
            (@Query.Prod _ (n+1) n (2*n+1) (by omega) (q₁.rewriting hq'₁)
              (Query.Dedup (Query.Diff
                (Query.Proj (λ (k: Fin n) ↦ Term.index (k.castLE (Nat.le_succ _)))
                  (q₁.rewriting hq'₁))
                (Query.Proj (λ (k: Fin n) ↦ Term.index (k.castLE (Nat.le_succ _)))
                  (q₂.rewriting hq'₂)))))))
        d.toComposite
      = AnnotatedRelation.toComposite
          (Multiset.filter (fun p: AnnotatedTuple T K n ↦
            p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
            (q₁.evaluateAnnotated hq'₁ d)) := by
      -- Abbreviations for the two evaluated annotated relations.
      set AR₁ := q₁.evaluateAnnotated hq'₁ d with hAR₁
      set AR₂ := q₂.evaluateAnnotated hq'₂ d with hAR₂
      -- Unfold `evaluate` and reduce the inner subqueries via the induction hypotheses.
      simp only [evaluate, Term.eval]
      rw[← ih'₁, ← ih'₂]
      -- The goal contains the inner-Diff form
      --   (Multiset.filter (· ∉ Multiset.map proj_n AR₂.toComposite)
      --     (Multiset.map proj_n AR₁.toComposite)).dedup
      -- which is `Query.rewriting_valid_diff_inner_dd`'s LHS. A direct `rw`/`simp only`
      -- with that helper fails because the goal's `.dedup` is elaborated with
      -- `LinearOrder.toDecidableEq` (via ValueType (T⊕K)) while the helper's `.dedup`
      -- uses `instDecidableEqSum`; the instances are propositionally equal but not
      -- syntactically. The bridge `Query.rewriting_valid_diff_inner_dd_inst` accepts both
      -- `DecidableEq` and `DecidablePred` instances explicitly and discharges the gap
      -- via `Subsingleton.elim` (its proof is `convert ... using 4`), letting `simp_rw`
      -- finally fire here.
      simp_rw [Query.rewriting_valid_diff_inner_dd_inst AR₁ AR₂]
      -- The remaining goal is a semijoin reduction:
      --   map proj_outer (filter selFilter (Relation.cast _ (AR₁.toComposite * Big)))
      --   = AnnotatedRelation.toComposite (filter (· ∉ map fst AR₂) AR₁)
      -- where Big = map (Sum.inl-lift) (filter (· ∉ map fst AR₂) (map fst AR₁)).dedup.
      -- Move the RHS filter inside `toComposite` via `AnnotatedRelation.toComposite_filter`
      -- so both sides become filters on `AR₁.toComposite`.
      rw [AnnotatedRelation.toComposite_filter, Relation.cast_eq_map]
      -- Unfold `r * s` (relation product = append-after-cartesian-product) and
      -- collapse the two `Multiset.map`s into one.
      simp only [(·*·), Mul.mul, Multiset.map_map]
      -- Push `Multiset.filter` through the map, then collapse with the outer map.
      rw [Multiset.filter_map, Multiset.map_map]
      -- The LHS is now `Multiset.map F (Multiset.filter G (AR₁.toComposite ×ˢ Big))`
      -- where `F = proj_outer ∘ Tuple.cast h ∘ uncurry Fin.append` collapses to `Prod.fst`
      -- and `G = selFilter.eval ∘ Tuple.cast h ∘ uncurry Fin.append` collapses to
      -- `fun (p, q) => p.first_n = q`. Both are pointwise Fin-arithmetic facts;
      -- once established, `Multiset.semijoin_proj_eq_filter` (with `Big.Nodup` from
      -- `Sum.inl_lift_injective.nodup_dedup`) reduces the LHS to
      -- `AR₁.toComposite.filter (fun t => t.first_n ∈ Big)`, and the final
      -- `Multiset.filter_congr` step uses `Tuple.fromComposite_toComposite` +
      -- `Sum.inl_lift_injective` to match the RHS.
      sorry
    -- The matched part of the rewriting (coming from `Proj ts₂ prod₂`).
    have matched_eq :
      evaluate
        (Query.Proj (fun (k: Fin (n+1)) ↦
            if ↑k < n then #(k.castLE (by omega))
            else Term.sub #(Fin.ofNat _ n) #(Fin.last (2*n+1)))
          (Query.Sel (((List.range n).map
              (λ k ↦ @Filter.BT (T⊕K) (2*n+2)
                (#(Fin.ofNat _ k) == #(Fin.ofNat _ (k+n+1))))).foldr
              (λ t t' ↦ Filter.And t t') Filter.True)
            (@Query.Prod _ (n+1) (n+1) (2*n+2) (by omega) (q₁.rewriting hq'₁)
              (Query.Agg (fun k: Fin n ↦ k.castLE (by simp)) ![#(Fin.last n)]
                ![AggFunc.sum] (q₂.rewriting hq'₂)))))
        d.toComposite
      = (Multiset.filter (fun p: AnnotatedTuple T K n ↦
            p.1 ∈ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
          (q₁.evaluateAnnotated hq'₁ d)).map
          (fun p: AnnotatedTuple T K n ↦ AnnotatedTuple.toComposite
            (p.1, p.2 - (Multiset.map Prod.snd
              (Multiset.filter (fun q: AnnotatedTuple T K n ↦ q.1 = p.1)
                (q₂.evaluateAnnotated hq'₂ d))).sum)) := by
      sorry
    have rhs_eq :
      evaluate ((Diff q₁ q₂).rewriting hq) d.toComposite
      = AnnotatedRelation.toComposite
        ((q₁.evaluateAnnotated hq'₁ d).map (fun p: AnnotatedTuple T K _ ↦
          (p.1, p.2 - (Multiset.map Prod.snd
            (Multiset.filter (fun q: AnnotatedTuple T K _ ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d))).sum))) := by
      unfold rewriting evaluate
      simp only []
      rw[unmatched_eq, matched_eq]
      -- Split ar₁ via filter
      have hsplit :
          q₁.evaluateAnnotated hq'₁ d
          = Multiset.filter (fun p: AnnotatedTuple T K n ↦
              p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d)
            + Multiset.filter (fun p: AnnotatedTuple T K n ↦
              p.1 ∈ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d) := by
        rw[add_comm]
        exact (Multiset.filter_add_not _ _).symm
      -- Show unmatched.toComposite equals the map form (since β = 0 on unmatched, α - 0 = α)
      have h_unmatched_toComp :
          AnnotatedRelation.toComposite
            (Multiset.filter (fun p: AnnotatedTuple T K n ↦
              p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d))
        = Multiset.map
            (fun p: AnnotatedTuple T K n ↦ AnnotatedTuple.toComposite
              (p.1, p.2 - (Multiset.map Prod.snd
                (Multiset.filter (fun q: AnnotatedTuple T K n ↦ q.1 = p.1)
                  (q₂.evaluateAnnotated hq'₂ d))).sum))
            (Multiset.filter (fun p: AnnotatedTuple T K n ↦
              p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d))
              (q₁.evaluateAnnotated hq'₁ d)) := by
        unfold AnnotatedRelation.toComposite
        apply Multiset.map_congr rfl
        intro p hp
        have hunmatched : p.1 ∉ Multiset.map Prod.fst (q₂.evaluateAnnotated hq'₂ d) :=
          (Multiset.mem_filter.mp hp).2
        have hfilter_empty :
            Multiset.filter (fun q: AnnotatedTuple T K n ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d) = 0 :=
          Multiset.filter_eq_nil.mpr (fun q hq hqeq =>
            hunmatched (Multiset.mem_map.mpr ⟨q, hq, hqeq⟩))
        -- Avoid direct `rw` on filter (DecidablePred instance divergence). Convert sum to 0 instead.
        have hsum_zero : (Multiset.map Prod.snd
            (Multiset.filter (fun q: AnnotatedTuple T K n ↦ q.1 = p.1)
              (q₂.evaluateAnnotated hq'₂ d))).sum = 0 := by
          convert Multiset.sum_zero
          convert Multiset.map_zero (Prod.snd : AnnotatedTuple T K n → K)
        rw[hsum_zero]
        have hp2 : HSub.hSub p.2 (0: K) = p.2 := by
          apply le_antisymm
          · rw[SemiringWithMonus.monus_spec]; simp
          · simpa using (monus_smallest p.2 0).left
        rw[hp2]
        rfl
      rw[h_unmatched_toComp]
      conv_rhs => rw[AnnotatedRelation.toComposite, Multiset.map_map, hsplit, Multiset.map_add]
      rfl
    exact lhs_eq.symm.trans rhs_eq.symm
  | Agg _ _ _ _ => simp[noAgg] at hq

/-! ## (R5) Rewriting of top-level aggregation

The aggregation rewriting rule (R5) of
[Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]:

> `γ_{i₁,…,iₘ}[t₁ : f₁, …, tₙ : fₙ](q)` is rewritten to
> `γ_{i₁,…,iₘ}[t₁ * #(k+1) : f̂₁, …, tₙ * #(k+1) : f̂ₙ, #(k+1) : δ(⊕)](q)`.

Unlike (R1)–(R4), which keep the rewriting target in `Query (T ⊕ K)` and
the standard `evaluate` semantics, (R5)'s rewritten query is interpreted
in the K-semimodule `V_K` – the per-column term `t_j * #(k+1)` evaluates
to a K-tensor monomial `α ⊗ v_j`, not to a plain `T ⊕ K` value. The
companion evaluator `Query.evaluateInVK` (in
`Provenance.QueryEvaluateInVK`) carries that interpretation.

`Query.rewritingAgg` here implements the rewriting **syntactically** as a
`Query (T ⊕ K)`. Its semantic correctness – the analogue of `rewriting_valid`
stating that `⟪Agg ...⟫_Î` matches `evaluateInVK (rewritingAgg ...) Î.toComposite`
– is proved as the (R5) case of `Query.rewriting_valid_full` (in
`Provenance.QueryEvaluateInVK`), packaged together with the (R1)–(R4)
correctness. The R4 sorries in `Query.rewriting_valid` for the diff
case are carried over there as the only remaining gap.
-/

/-- (R5) Top-level aggregation rewriting. Produces a plain `Query (T ⊕ K)`
representing `γ_{is}[t_j * #(k+1) : f̂_j, #(k+1) : δ(⊕)](q.rewriting)`.

The inner query `q` is required to be `noAgg` (the ICDE paper imposes
aggregation-at-root); `q.rewriting` handles its (R1)–(R4) rewriting and
the resulting query operates on tuples of arity `m+1` (the original `m`
data columns plus one annotation column). The output Agg has `n₁`
grouping columns, `n₂+1` aggregated columns (the original `n₂` plus the
`δ(⊕)` annotation column at the end), and arity `n₁ + n₂ + 1`. -/
def Query.rewritingAgg [ValueType T] {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂)
    (as : Tuple AggFunc n₂)
    (q_inner : Query T m) (hq_inner : q_inner.noAgg) :
    Query (T ⊕ K) (n₁ + n₂ + 1) :=
  let q_inner' : Query (T ⊕ K) (m + 1) := q_inner.rewriting hq_inner
  -- Index of the annotation column on the rewritten inner query (= the last Fin).
  let annIdx : Term (T ⊕ K) (m + 1) := Term.index (Fin.last m)
  -- New aggregated-column terms.
  let ts' : Tuple (Term (T ⊕ K) (m + 1)) (n₂ + 1) := fun k =>
    if h : ↑k < n₂ then
      Term.mul (ts ⟨k, h⟩).castToAnnotatedTuple annIdx
    else
      annIdx
  -- New aggregators: f̂_j (= as j for the original aggregated columns; here
  -- the lift is the identity on the AggFunc constructors), plus `sumDelta`
  -- for the new annotation column.
  let as' : Tuple AggFunc (n₂ + 1) := fun k =>
    if h : ↑k < n₂ then as ⟨k, h⟩ else AggFunc.sumDelta
  -- New grouping indices: lift `is k : Fin m` to `Fin (m + 1)` (one extra
  -- annotation column at the end).
  let is' : Tuple (Fin (m + 1)) n₁ := fun k => (is k).castLE (Nat.le_succ _)
  @Query.Agg (T ⊕ K) (m + 1) n₁ (n₂ + 1) is' ts' as' q_inner'

/-! ## Unified rewriting for queries with at-most-top-level aggregation -/

/-- A query is *well-formed for rewriting* if it has no aggregation at all
(corresponding to the (R1)–(R4) cases) or if it is a top-level
aggregation whose inner query has no aggregation (the (R5) case). This is
the structural precondition imposed by the ICDE paper, which restricts
the aggregation operator to the root of a query plan. -/
def Query.wellFormed : ∀ {n}, Query T n → Prop
  | _, @Query.Agg _ _ _ _ _ _ _ q_inner => q_inner.noAgg
  | _, q => q.noAgg

/-- Unified rewriting: dispatches between the (R1)–(R4) rewriting for
non-aggregating queries and the (R5) rewriting for top-level
aggregations. The single function realises the rewriting rules (R1)–(R5)
of [Sen, Maniu & Senellart][sen2026provsql] together. -/
def Query.rewritingFull [ValueType T] :
    ∀ {n}, (q : Query T n) → q.wellFormed → Query (T ⊕ K) (n + 1)
  | _, @Query.Agg _ _ _ _ is ts as q_inner, h =>
      Query.rewritingAgg (K := K) is ts as q_inner h
  | _, Query.Rel n s, h => (Query.Rel n s).rewriting h
  | _, Query.Proj ts q', h => (Query.Proj ts q').rewriting h
  | _, Query.Sel φ q', h => (Query.Sel φ q').rewriting h
  | _, @Query.Prod _ _ _ _ hn q₁ q₂, h => (@Query.Prod _ _ _ _ hn q₁ q₂).rewriting h
  | _, Query.Sum q₁ q₂, h => (Query.Sum q₁ q₂).rewriting h
  | _, Query.Dedup q', h => (Query.Dedup q').rewriting h
  | _, Query.Diff q₁ q₂, h => (Query.Diff q₁ q₂).rewriting h
