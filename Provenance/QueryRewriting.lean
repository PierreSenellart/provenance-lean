import Mathlib.Data.Fin.VecNotation

import Provenance.AnnotatedDatabase
import Provenance.Query
import Provenance.QueryAnnotatedDatabase
import Provenance.Util.ValueType

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
      rw[Eq.rec_eq_cast]
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
    unfold evaluateAnnotated evaluate rewriting
    simp
    rw[← ih (noAggDedup hq rfl)]
    unfold evaluate
    unfold evaluate
    simp
    rw[← ih (noAggDedup hq rfl)]
    unfold AnnotatedRelation.toComposite

    sorry
  | Diff q₁ q₂ ih₁ ih₂ =>
    unfold evaluateAnnotated evaluate rewriting
    simp
    sorry
  | Agg _ _ _ _ => simp[noAgg] at hq
