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
                         else Term.index q.arity)
  Proj ts (q.rewriting (noAggProj hq rfl))
| Sel   φ  q  => Sel φ.castToAnnotatedTuple (q.rewriting (noAggSel hq rfl))
| @Prod T n₁ n₂ n hn q₁ q₂ =>
  let tmp :=
    @Query.Prod (T⊕K) (n₁+1) (n₂+1) (n+2) (by omega) (q₁.rewriting (noAggProd hq rfl).left)
  let product := tmp (q₂.rewriting (noAggProd hq rfl).right)
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if k<n₁ then #k
    else if (↑k<n: Prop) then #(k+1)
      else Term.mul #n₁ #(n+1))
  Proj ts product
| Sum   q₁ q₂ => Sum (q₁.rewriting (noAggSum hq rfl).left) (rewriting q₂ (noAggSum hq rfl).right)
| Dedup q     =>
  let q' := q.rewriting (noAggDedup hq rfl)
  Agg (λ (k: Fin n) ↦ (k: Fin (n+1))) ![#n] ![AggFunc.sum] q'
| Diff  q₁ q₂ =>
  let q'₁ := q₁.rewriting (noAggDiff hq rfl).left
  let q'₂ := q₂.rewriting (noAggDiff hq rfl).right
  let joinCond₁ :=
    ((List.range n).map
      (λ k ↦ @Filter.BT (T⊕K) (2*n+1) (#k==#(k+n+1)))).foldr
      (λ t t' ↦ Filter.And t t') Filter.True
  let prod₁t := λ r ↦ Sel joinCond₁ (@Query.Prod _ (n+1) n (2*n+1) (by omega) q'₁ r)
  let prod₁r := Dedup (Diff (Proj (λ (k: Fin n) ↦ (Term.index (k: Fin (n+1)))) q'₁)
                            (Proj (λ (k: Fin n) ↦ (Term.index (k: Fin (n+1)))) q'₂))
  let prod₁ := prod₁t (prod₁r)
  let joinCond₂ :=
    ((List.range n).map
      (λ k ↦ @Filter.BT (T⊕K) (2*n+2) (#k==#(k+n+1)))).foldr
      (λ t t' ↦ Filter.And t t') Filter.True
  have h₂ : (2*n+2 - (n+1): ℕ) = n+1  := by omega
  let prod₂t := λ r ↦ Sel joinCond₂ (@Query.Prod _ (n+1) (n+1) (2*n+2) (by omega) q'₁ r)
  let prod₂r := Agg (λ (k: Fin n) ↦ (k: Fin (n+1))) ![#n] ![AggFunc.sum] q'₂
  let prod₂ := prod₂t (prod₂r)
  let ts₁ := (λ (k: Fin (n+1)) ↦ #(k: Fin (2*n+1)))
  let ts₂ := (λ (k: Fin (n+1)) ↦ if ↑k<n then #(k: Fin (2*n+2))
                                 else Term.sub #n #(2*n+1))
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
      sorry
  . sorry

theorem Query.rewriting_valid
  [ValueType T] [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
  (q: Query T n) (hq: q.noAgg) :
  ∀ (d: AnnotatedDatabase T K), (q.evaluateAnnotated hq d).toComposite = (q.rewriting hq).evaluate d.toComposite := by
  intro d
  induction q with
  | Rel n s =>
    unfold Query.evaluateAnnotated Query.evaluate Query.rewriting
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
    unfold Query.evaluateAnnotated Query.evaluate Query.rewriting
    simp
    rw[← ih (noAggProj hq rfl)]
    unfold AnnotatedRelation.toComposite
    simp
    apply congrFun
    apply congrArg
    funext t k
    by_cases hkn' : k=n'
    . simp[hkn']
      simp[Term.eval]
      unfold Query.arity
      have : ∀ x, Fin.last x = Fin.natAdd (Fin.last x) 0 := by
        simp
        intro x
        rfl
      rw[this n',this m]
      rw[@Fin.append_right (Fin.last n')]
      rw[@Fin.append_right (Fin.last m)]
    . simp at hkn'
      have hlt := Fin.val_lt_last hkn'
      simp[hlt]
      have : k = (Fin.castAdd (Fin.last 1) (k.castLT hlt): Fin (n'+1)) := by simp
      rewrite (occs := [1]) [this]
      rw[@Fin.append_left (Fin.last n') (Fin.last 1)]
      rw[Term.castToAnnotatedTuple_eval]
      rfl
  | Sel φ q' ih =>
    unfold Query.evaluateAnnotated Query.evaluate Query.rewriting
    simp
    rw[← ih (noAggSel hq rfl)]
    unfold AnnotatedRelation.toComposite
    rw[Multiset.filter_map]
    apply congrArg
    apply congrFun
    simp[Function.comp_def]
    conv =>
      rhs
      congr
      . ext x
        rw[Filter.castToAnnotatedTuple_eval φ]
        skip
      . apply φ.evalDecidableAnnotated
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    unfold Query.evaluateAnnotated Query.evaluate Query.rewriting
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
      unfold Query.evaluate
      simp[(·*·)]
      skip
    rw[Query.rewriting_valid_prod1 hn]
    simp
    congr
    . exact (Eq.symm hn)
    . refine Function.hfunext ?_ ?_
      . rfl
      . intro p₁ p₂ hteq
        congr! with k k' heqk
        . exact (Eq.symm hn)
        . sorry


  | Sum q₁ q₂ ih₁ ih₂ =>
    unfold Query.evaluateAnnotated Query.evaluate Query.rewriting
    simp
    rw[ih₁ (noAggSum hq rfl).left]
    rw[ih₂ (noAggSum hq rfl).right]
  | Dedup q ih =>
    unfold Query.evaluateAnnotated Query.evaluate Query.rewriting
    simp
    sorry
  | Diff q₁ q₂ ih₁ ih₂ =>
    unfold Query.evaluateAnnotated Query.evaluate Query.rewriting
    simp
    sorry
  | Agg _ _ _ _ => simp[noAgg] at hq
