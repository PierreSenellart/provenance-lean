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
partially formalised (rules (R1), (R2), and (R3) are machine-checked).

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
  let prod₁r := Dedup (Diff (Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (by simp)))) q'₁)
                            (Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (by simp)))) q'₂))
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
  . simp[Relation.cast]

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
  unfold AnnotatedRelation.toComposite
  rw[Multiset.map_map]
  -- Rewrite the composed map to `(Sum.inl ∘ ·) ∘ Prod.fst` via funext
  have heq :
    ((fun u: Tuple (T⊕K) (n+1) ↦ fun k: Fin n ↦ u (Fin.castLE h k))
       ∘ (fun p: AnnotatedTuple T K n ↦ p.toComposite))
    = (fun v: Tuple T n ↦ (fun k: Fin n ↦ (Sum.inl (v k): T⊕K))) ∘ Prod.fst := by
    funext p k
    simp only [Function.comp]
    unfold AnnotatedTuple.toComposite
    have hcast : k.castLE h = Fin.castAdd 1 k := rfl
    rw[hcast, Fin.append_left]
  rw[heq]
  rw[← Multiset.map_map]
  -- Apply dedup_map_of_injective
  apply Multiset.dedup_map_of_injective
  intro v₁ v₂ h
  funext k
  have := congrFun h k
  exact Sum.inl.inj this

/-- Auxiliary: key set of `groupByKey ar` equals first-projection keys of `ar`. -/
private lemma groupByKey_key_iff
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n) (v: Tuple T n):
  (∃ w, (v, w) ∈ (groupByKey ar).val) ↔ v ∈ Multiset.map Prod.fst ar := by
  induction ar using Multiset.induction_on with
  | empty => simp[groupByKey]
  | @cons p tl ih =>
    have hkv : (groupByKey (p ::ₘ tl)).val = (groupByKey tl).val.addKV p.1 p.2 := by
      unfold groupByKey; rw[Multiset.foldr_cons]; rfl
    rw[hkv, Multiset.map_cons, Multiset.mem_cons]
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
private lemma groupByKey_value
  {T K: Type} [ValueType T] [SemiringWithMonus K] [DecidableEq K] {n: ℕ}
  (ar: AnnotatedRelation T K n) (v: Tuple T n) (w: K):
  (v, w) ∈ (groupByKey ar).val →
    w = (Multiset.map Prod.snd
          (Multiset.filter (fun p: AnnotatedTuple T K n ↦ p.1 = v) ar)).sum := by
  induction ar using Multiset.induction_on generalizing w with
  | empty => simp[groupByKey]
  | @cons p tl ih =>
    intro hmem
    have hkv : (groupByKey (p ::ₘ tl)).val = (groupByKey tl).val.addKV p.1 p.2 := by
      unfold groupByKey; rw[Multiset.foldr_cons]; rfl
    rw[hkv] at hmem
    rw[KeyValueList.addKV_spec _ (groupByKey tl).property] at hmem
    by_cases hpv : p.1 = v
    · -- p.1 = v
      rw[show Multiset.filter (fun p₁ : AnnotatedTuple T K n ↦ p₁.1 = v) (p ::ₘ tl)
          = p ::ₘ Multiset.filter (fun p₁ : AnnotatedTuple T K n ↦ p₁.1 = v) tl
        from Multiset.filter_cons_of_pos tl hpv]
      rw[Multiset.map_cons, Multiset.sum_cons]
      rcases hmem with ⟨hne, _⟩ | ⟨_, hdisj⟩
      · exact absurd hpv.symm hne
      · rcases hdisj with ⟨hnone, hw⟩ | ⟨z, hz, hw⟩
        · -- (v, w) = (p.1, p.2) and no entry with key p.1 in groupByKey tl
          have hw_eq : w = p.2 := ((Prod.mk.injEq _ _ _ _).mp hw).2
          have hfilter_empty :
            Multiset.filter (fun p_1 : AnnotatedTuple T K n ↦ p_1.1 = v) tl = 0 := by
            rw[Multiset.filter_eq_nil]
            intro q hq hq1
            apply hnone
            rw[hpv]
            exact (groupByKey_key_iff tl v).mpr (Multiset.mem_map.mpr ⟨q, hq, hq1⟩)
          rw[hfilter_empty, Multiset.map_zero, Multiset.sum_zero, add_zero]
          exact hw_eq
        · -- (v, w) = (p.1, p.2 + z) with (p.1, z) ∈ groupByKey tl
          have hv_eq : v = p.1 := ((Prod.mk.injEq _ _ _ _).mp hw).1
          have hw_eq : w = p.2 + z := ((Prod.mk.injEq _ _ _ _).mp hw).2
          have hz' : (v, z) ∈ (groupByKey tl).val := hv_eq ▸ hz
          rw[hw_eq, ih z hz']
    · -- p.1 ≠ v
      rw[show Multiset.filter (fun p₁ : AnnotatedTuple T K n ↦ p₁.1 = v) (p ::ₘ tl)
          = Multiset.filter (fun p₁ : AnnotatedTuple T K n ↦ p₁.1 = v) tl
        from Multiset.filter_cons_of_neg tl hpv]
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
  rw[Multiset.mem_coe, Multiset.mem_map]
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
      rw[@Fin.append_right (Fin.last n')]
      rw[@Fin.append_right (Fin.last m)]
    . simp at hkn'
      have hlt := Fin.val_lt_last hkn'
      simp[hlt]
      have : k = (Fin.castAdd (Fin.last 1) (k.castLT hlt): Fin (n'+1)) := by simp
      rewrite (occs := [1]) [this]
      unfold AnnotatedTuple.toComposite
      rw[@Fin.append_left (Fin.last n') (Fin.last 1)]
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
    rw[Multiset.map_map]
    conv_lhs =>
      unfold evaluate
      simp[(·*·)]
      skip
    rw[rewriting_valid_prod1 (rewriting_valid_prod_heqn hn)]
    simp
    congr
    ext p k
    rw[Tuple.cast_get]
    subst hn
    by_cases hlt₁: ↑k < n₁
    . simp[hlt₁]
      simp only[Term.eval]
      unfold Tuple.cast
      simp
      have hksucc : ↑k < n₁+1 := by omega
      rw[rewriting_append_left]
      . apply congrArg
        refine Fin.eq_of_val_eq ?_
        simp
        have : ↑k < n₁+1 := by omega
        simp[hksucc]
      . simp[hksucc]
    . by_cases hlt: ↑k < n₁+n₂
      . simp[hlt₁,hlt]
        simp only[Term.eval]
        unfold Tuple.cast
        simp
        have hk₁₂: (k+1:ℕ)<n₁+n₂+2 := by omega
        rw[rewriting_append_right]
        . apply congrArg
          simp[Nat.mod_eq_of_lt hk₁₂]
          refine Fin.eq_of_val_eq ?_
          have : (k-n₁:ℕ)<n₂+1 := by omega
          simp[Nat.mod_eq_of_lt this]
        . simp[Nat.mod_eq_of_lt hk₁₂,hlt₁]
      . simp[hlt₁,hlt]
        simp only[Term.eval]
        unfold Tuple.cast
        simp
        rw[rewriting_append_left]
        . rw[rewriting_append_right]
          . congr
            . apply congrArg
              apply Fin.eq_of_val_eq
              simp[Fin.castLT]
              omega
            . apply congrArg
              apply Fin.eq_of_val_eq
              simp
          . simp
        . have : n₁ < n₁+n₂+2 := by omega
          simp[Nat.mod_eq_of_lt this]
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
      rw[Multiset.map_map]
      rfl
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
      -- Apply dedup helper via congrArg on the outer Multiset.map
      apply Eq.trans (b := Multiset.map _
        (Multiset.map (fun v ↦ (fun k: Fin _ ↦ (Sum.inl (v k): T⊕K)))
          (Multiset.dedup (Multiset.map Prod.fst (q.evaluateAnnotated hq' d)))))
      · apply congrArg
        convert AnnotatedRelation.dedup_toComposite_proj_first_n
          (q.evaluateAnnotated hq' d) (Nat.le_succ _) using 2
      · -- Now map composition and element-wise equality
        rw[Multiset.map_map]
        apply Multiset.map_congr rfl
        intro v _hv
        -- Show outer_f (Sum.inl∘v) = toComposite (v, sum_v)
        simp only [Function.comp, Matrix.cons_val_fin_one, Term.eval]
        rw[AnnotatedRelation.toComposite_filter_map_last]
        simp only [AggFunc.eval]
        rw[show (fun p: AnnotatedTuple T K _ ↦ (Sum.inr p.2: T⊕K))
              = (fun k ↦ (Sum.inr k: T⊕K)) ∘ Prod.snd from rfl]
        rw[← Multiset.map_map]
        rw[Multiset.fold_addFn_map_inr]
        -- Both sides are Fin.append; show equal via funext
        unfold AnnotatedTuple.toComposite
        funext k
        by_cases hk: k = Fin.last _
        · subst hk
          simp [Fin.append, Fin.addCases]
        · rename_i n
          have hlt : (k: ℕ) < n := Fin.val_lt_last hk
          simp [Fin.append, Fin.addCases, hlt]
    rw[← lhs_eq] at rhs_eq
    unfold evaluateAnnotated
    exact rhs_eq.symm
  | Diff q₁ q₂ ih₁ ih₂ =>
    unfold evaluateAnnotated evaluate rewriting
    simp
    sorry
  | Agg _ _ _ _ => simp[noAgg] at hq
