/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryStrip

/-!
# Correctness of the native rewriting

The last stage: the query the general syntax rewrites to and the
classical rewriting of its strip evaluate identically under the plain
semantics (`AggQueryIn.rewriting_plain`), whence the correctness theorem
`AggQueryIn.rewriting_valid` – evaluating the annotated semantics and
folding the rows into composite `T ⊕ K` tuples is evaluating the
rewritten query over the composite database.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## Plain-semantics agreement of the two rewritten queries -/

section PlainAgreement

omit [DecidableEq K] in
/-- The composite cast of a term agrees with the classical cast of its
strip. -/
theorem TermGIn.castComposite_evalPlain {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) (t : TermGIn T c κ)
    (u : Tuple (T ⊕ K) (n + 1)) :
    (t.castComposite hκ (K := K)).evalPlain u
      = (t.strip.castToAnnotatedTuple).eval u := by
  induction t with
  | const a => rfl
  | outer k => rfl
  | index k h => rfl
  | provIndex k h =>
    exact absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | cmpAgg k h op c ih =>
    exact absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ =>
    show (t₁.castComposite hκ).evalPlain u + (t₂.castComposite hκ).evalPlain u
      = _
    rw [ih₁, ih₂]
    rfl
  | sub t₁ t₂ ih₁ ih₂ =>
    show HSub.hSub ((t₁.castComposite hκ).evalPlain u)
        ((t₂.castComposite hκ).evalPlain u)
      = _
    rw [ih₁, ih₂]
    rfl
  | mul t₁ t₂ ih₁ ih₂ =>
    show (t₁.castComposite hκ).evalPlain u * (t₂.castComposite hκ).evalPlain u
      = _
    rw [ih₁, ih₂]
    rfl

omit [DecidableEq K] in
/-- The composite cast of a predicate agrees with the classical cast of its
strip – three-valuedly, both readings being Kleene's. -/
theorem GenPredIn.castComposite_evalPlain3 {c n : ℕ}
    {κ : Fin n → ColKind} (hκ : ∀ k, κ k = ColKind.reg) :
    ∀ (φ : GenPredIn T c κ) (hφ : φ.hasAggAtom = false)
      (u : Tuple (T ⊕ K) (n + 1)),
      (φ.castComposite hκ hφ (K := K)).evalPlain3 u
        = (φ.strip.castToAnnotatedTuple).eval3 u
  | .cmp op t₁ t₂, _, u => by
    cases op <;>
      (simp only [GenPredIn.castComposite, GenPredIn.evalPlain3, GenPredIn.strip,
         Selection.castToAnnotatedTuple, BoolTerm.castToAnnotatedTuple,
         Selection.eval3, BoolTerm.eval3, BoolTerm.toCompOp, BoolTerm.args,
         TermGIn.castComposite_evalPlain])
  | .aggCmp _ _ _ _, hφ, _ => Bool.noConfusion hφ
  | .and φ ψ, hφ, u => by
    show (GenPredIn.evalPlain3 _ _).and _ = _
    rw [castComposite_evalPlain3 hκ φ (Bool.or_eq_false_iff.mp hφ).1 u,
      castComposite_evalPlain3 hκ ψ (Bool.or_eq_false_iff.mp hφ).2 u]
    rfl
  | .or φ ψ, hφ, u => by
    show (GenPredIn.evalPlain3 _ _).or _ = _
    rw [castComposite_evalPlain3 hκ φ (Bool.or_eq_false_iff.mp hφ).1 u,
      castComposite_evalPlain3 hκ ψ (Bool.or_eq_false_iff.mp hφ).2 u]
    rfl
  | .not φ, hφ, u => by
    show (GenPredIn.evalPlain3 _ _).not = _
    rw [castComposite_evalPlain3 hκ φ hφ u]
    rfl

omit [DecidableEq K] in
/-- The composite cast of a predicate agrees with the classical cast of
its strip. -/
theorem GenPredIn.castComposite_holdsPlain {c n : ℕ}
    {κ : Fin n → ColKind} (hκ : ∀ k, κ k = ColKind.reg)
    (φ : GenPredIn T c κ) (hφ : φ.hasAggAtom = false)
    (u : Tuple (T ⊕ K) (n + 1)) :
    (φ.castComposite hκ hφ (K := K)).holdsPlain u
      ↔ (φ.strip.castToAnnotatedTuple).eval u := by
  unfold GenPredIn.holdsPlain Selection.eval
  rw [GenPredIn.castComposite_evalPlain3 hκ φ hφ u]

omit [DecidableEq K] in
/-- The composite cast of a projection column agrees with the classical
cast of its strip. -/
theorem ProjColIn.castComposite_evalPlain {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    ∀ (p : ProjColIn T c κ) (hp : p.kind = ColKind.reg)
      (u : Tuple (T ⊕ K) (n + 1)),
      (p.castComposite hκ hp (K := K)).evalPlain u
        = (p.strip.castToAnnotatedTuple).eval u
  | .term t, _, u => TermGIn.castComposite_evalPlain hκ t u
  | .token _ _, hp, _ => ColKind.noConfusion hp
  | .provTerm _, hp, _ => ColKind.noConfusion hp

theorem Relation.cast_filter {T' : Type} {n m : ℕ} (hn : n = m)
    (p : Tuple T' m → Prop) [DecidablePred p] (r : Relation T' n) :
    (r.cast hn).filter p
      = Relation.cast hn (r.filter (fun t => p (Tuple.cast hn t))) := by
  subst hn
  rfl

theorem Tuple.cast_coord {T' : Type} {n m : ℕ} (heq : n = m)
    (t : Tuple T' n) (k : Fin m) :
    Tuple.cast heq t k = t ⟨(k : ℕ), by omega⟩ := by
  subst heq
  rfl

/-- **Plain-semantics agreement**: the native rewriting and the classical
rewriting of the stripped query evaluate identically on any composite
database. -/
theorem AggQueryIn.rewriting_plain :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (hq : q.classical) (D : Database (T ⊕ K)),
      (q.rewriting hq).evaluatePlain D
        = ((q.strip hq).rewriting (q.strip_source hq)).evaluate D
  | _, n, _, .Rel _ s, _, D => by
    show (AggQueryIn.Rel (T := T ⊕ K) (n + 1) s).evaluatePlain D
      = (Query.Rel (T := T ⊕ K) (n + 1) s).evaluate D
    simp only [AggQueryIn.evaluatePlain, Query.evaluate]
    cases D.find (n + 1) s <;> rfl
  | _, _, _, @AggQueryIn.Proj _ _ n m κ ps q, hq, D => by
    unfold AggQueryIn.rewriting AggQueryIn.retagToRew AggQueryIn.strip
    simp only [AggQueryIn.evaluatePlain]
    unfold Query.rewriting Query.evaluate
    rw [rewriting_plain q hq.2 D]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    funext j
    dsimp only
    by_cases hj : (j : ℕ) < m
    · rw [dite_eq_left hj, dite_eq_left hj]
      exact ProjColIn.castComposite_evalPlain _ _ _ u
    · rw [dite_eq_right hj, dite_eq_right hj]
      rfl
  | _, _, _, .Sel φ q, hq, D => by
    unfold AggQueryIn.rewriting AggQueryIn.strip
    simp only [AggQueryIn.evaluatePlain]
    unfold Query.rewriting Query.evaluate
    rw [rewriting_plain q hq.2 D]
    let : DecidablePred (Selection.eval (φ.strip.castToAnnotatedTuple
        (K := K))) := (φ.strip.castToAnnotatedTuple).evalDecidable
    exact Multiset.filter_congr
      (fun u _ => GenPredIn.castComposite_holdsPlain
        (AggQueryIn.classical_kinds q hq.2) φ hq.1 u)
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq, D => by
    unfold AggQueryIn.rewriting AggQueryIn.retagToRew AggQueryIn.strip
    simp only [AggQueryIn.evaluatePlain]
    unfold Query.rewriting
    simp only [Query.evaluate]
    rw [rewriting_plain q₁ hq.1 D, rewriting_plain q₂ hq.2 D,
      Query.rewriting_valid_prod1]
    refine Multiset.map_congr rfl (fun t _ => ?_)
    funext j
    by_cases h₁ : (j : ℕ) < n₁
    · rw [dite_eq_left h₁, ite_eq_left h₁]
      simp only [ProjColIn.evalPlain, TermGIn.evalPlain, TermIn.eval]
      rw [Tuple.cast_coord]
      rfl
    · rw [dite_eq_right h₁, ite_eq_right h₁]
      by_cases h₂ : (j : ℕ) < n₁ + n₂
      · rw [dite_eq_left h₂, ite_eq_left h₂]
        simp only [ProjColIn.evalPlain, TermGIn.evalPlain, TermIn.eval]
        rw [Tuple.cast_coord]
        refine congrArg t (Fin.ext ?_)
        show n₁ + 1 + ((j : ℕ) - n₁) = _
        simp only [Fin.ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [dite_eq_right h₂, ite_eq_right h₂]
        simp only [ProjColIn.evalPlain, TermGIn.evalPlain, TermIn.eval]
        rw [Tuple.cast_coord, Tuple.cast_coord]
        refine congrArg₂ (· * ·) (congrArg t (Fin.ext ?_))
          (congrArg t (Fin.ext ?_))
        · show (n₁ : ℕ) = _
          simp only [Fin.ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
        · show n₁ + 1 + n₂ = _
          simp only [Fin.ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
  | _, _, _, .Sum q₁ q₂, hq, D => by
    unfold AggQueryIn.rewriting AggQueryIn.strip
    simp only [AggQueryIn.evaluatePlain]
    unfold Query.rewriting Query.evaluate
    rw [rewriting_plain q₁ hq.1 D, rewriting_plain q₂ hq.2 D]
  | _, _, _, @AggQueryIn.Dedup _ _ n q, hq, D => by
    unfold AggQueryIn.rewriting AggQueryIn.retagToRew AggQueryIn.strip
    simp only [AggQueryIn.evaluatePlain]
    unfold Query.rewriting
    simp only [Query.evaluate]
    rw [rewriting_plain q hq D]
    refine Multiset.map_congr ?_ (fun g _ => ?_)
    · congr 1
    · funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        show Multiset.fold addFn 0 _ = Multiset.fold addFn 0 _
        refine congrArg _ (Multiset.map_congr ?_ (fun u _ => rfl))
        congr 1
  | _, _, _, @AggQueryIn.Diff _ _ n q₁ q₂, hq, D => by
    unfold AggQueryIn.rewriting AggQueryIn.retagToRew AggQueryIn.strip
    simp only [AggQueryIn.evaluatePlain]
    unfold Query.rewriting
    simp only [Query.evaluate]
    rw [rewriting_plain q₁ hq.1 D, rewriting_plain q₂ hq.2 D]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [show (fun x (j : Fin n) => (ProjColIn.term (TermGIn.index
          (Fin.castLE (Nat.le_succ n) j)
          (ColKind.rewKinds_lt j.isLt))).evalPlain x)
        = (fun x (k : Fin n) =>
            (#(Fin.castLE (Nat.le_succ n) k)).eval (T := T ⊕ K) x) from
        funext fun x => funext fun j => rfl]
      rw [Relation.cast_filter, Relation.cast_eq_map, Multiset.map_map]
      have : NeZero (2 * n + 1) := ⟨by omega⟩
      have : ∀ {m : ℕ} (φ : Selection (T ⊕ K) m) (h : n + 1 + n = m),
          DecidablePred fun t : Tuple (T ⊕ K) (n + 1 + n) =>
            φ.eval (Tuple.cast h t) :=
        fun φ h t => φ.evalDecidable (Tuple.cast h t)
      refine Multiset.map_congr (Eq.trans (Multiset.filter_congr (fun t _ =>
        Iff.trans (keyJoinCond_holdsPlain _ _ _ _ t)
          (Iff.trans (forall_congr' (fun k =>
            iff_of_eq (congrArg₂ (· = ·)
              ((Tuple.cast_coord (by omega : n + 1 + n = 2 * n + 1) t
                  (Fin.ofNat (2 * n + 1) (k : ℕ))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_castAdd, Fin.val_castLE]
                  rw [Nat.mod_eq_of_lt (by omega)])))).symm
              ((Tuple.cast_coord (by omega : n + 1 + n = 2 * n + 1) t
                  (Fin.ofNat (2 * n + 1) ((k : ℕ) + n + 1))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_natAdd]
                  rw [Nat.mod_eq_of_lt (by omega)]
                  omega)))).symm)))
            (Query.rewriting_valid_joinCond_eval
              (Tuple.cast (by omega : n + 1 + n = 2 * n + 1) t)).symm)))
        ?_) (fun t _ => ?_)
      · congr 1
      · funext j
        by_cases hj : (j : ℕ) < n
        · rw [dite_eq_left hj]
          simp only [ProjColIn.evalPlain, TermGIn.evalPlain, TermIn.eval,
            Function.comp_apply]
          rw [Tuple.cast_coord]
          rfl
        · rw [dite_eq_right hj]
          simp only [ProjColIn.evalPlain, TermGIn.evalPlain, TermIn.eval,
            Function.comp_apply]
          rw [Tuple.cast_coord]
          exact congrArg t (Fin.ext (by
            simp only [Fin.val_castAdd, Fin.val_castLE, Fin.val_last]
            omega))
    · rw [show (fun (x : Tuple (T ⊕ K) (n + 1)) (k : Fin n) =>
            x (Fin.castLE (Nat.le_succ n) k))
          = (fun t (k : Fin n) =>
              (#(Fin.castLE (Nat.le_succ n) k)).eval (T := T ⊕ K) t) from
        funext fun x => funext fun k => rfl]
      rw [Relation.cast_filter, Relation.cast_eq_map, Multiset.map_map]
      have : NeZero (2 * n + 2) := ⟨by omega⟩
      have : ∀ {m : ℕ} (φ : Selection (T ⊕ K) m) (h : n + 1 + (n + 1) = m),
          DecidablePred fun t : Tuple (T ⊕ K) (n + 1 + (n + 1)) =>
            φ.eval (Tuple.cast h t) :=
        fun φ h t => φ.evalDecidable (Tuple.cast h t)
      refine Multiset.map_congr (Eq.trans (Multiset.filter_congr (fun t _ =>
        Iff.trans (keyJoinCond_holdsPlain _ _ _ _ t)
          (Iff.trans (forall_congr' (fun k =>
            iff_of_eq (congrArg₂ (· = ·)
              ((Tuple.cast_coord
                  (by omega : n + 1 + (n + 1) = 2 * n + 2) t
                  (Fin.ofNat (2 * n + 2) (k : ℕ))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_castAdd, Fin.val_castLE]
                  rw [Nat.mod_eq_of_lt (by omega)])))).symm
              ((Tuple.cast_coord
                  (by omega : n + 1 + (n + 1) = 2 * n + 2) t
                  (Fin.ofNat (2 * n + 2) ((k : ℕ) + n + 1))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_natAdd, Fin.val_castAdd]
                  rw [Nat.mod_eq_of_lt (by omega)]
                  omega)))).symm)))
            (Query.rewriting_valid_joinCond_eval
              (Tuple.cast
                (by omega : n + 1 + (n + 1) = 2 * n + 2) t)).symm)))
        ?_) (fun t _ => ?_)
      · -- at default transparency `congr` unfolds the two rewritten
        -- subqueries, which costs a minute and buys nothing
        with_reducible congr 1
        refine congrArg (HMul.hMul _) ?_
        refine Multiset.map_congr ?_ (fun g _ => ?_)
        · congr 1
        · funext k
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k
          · rw [Fin.append_left, Fin.append_left]
          · rw [Fin.append_right, Fin.append_right]
            show Multiset.fold addFn 0 _ = Multiset.fold addFn 0 _
            refine congrArg _ (Multiset.map_congr ?_ (fun u _ => rfl))
            congr 1
      · funext j
        by_cases hj : (j : ℕ) < n
        · rw [dite_eq_left hj]
          simp only [Function.comp_apply]
          rw [ite_eq_left hj]
          simp only [ProjColIn.evalPlain, TermGIn.evalPlain, TermIn.eval]
          rw [Tuple.cast_coord]
          rfl
        · rw [dite_eq_right hj]
          simp only [Function.comp_apply]
          rw [ite_eq_right hj]
          simp only [ProjColIn.evalPlain, TermGIn.evalPlain, TermIn.eval]
          rw [Tuple.cast_coord, Tuple.cast_coord]
          refine congrArg₂ _
            (congrArg t (Fin.ext (by
              simp only [Fin.ofNat, Fin.val_castAdd, Fin.val_last]
              rw [Nat.mod_eq_of_lt (by omega)])))
            (congrArg t (Fin.ext (by
              simp only [Fin.val_natAdd, Fin.val_last, Fin.val_zero]
              omega)))
  | _, _, _, .Gamma _ _ _ _, hq, _ => False.elim hq
  | _, _, _, .GammaScalar _ _ _, hq, _ => False.elim hq
  | _, _, _, .ProvSum _ _ _ _, hq, _ => False.elim hq
  | _, _, _, .Retag _ _, hq, _ => False.elim hq
  | _, _, _, .GammaTok _ _ _ _ _ _, hq, _ => False.elim hq
  | _, _, _, .Win _ _ _ _ _ _ _, hq, _ => False.elim hq

end PlainAgreement

/-! ## Rewriting correctness -/

section Correctness

/-- **Correctness of the native rewriting.** For a classical query in the
general syntax, evaluating the annotated semantics and folding the result
into composite `T ⊕ K` tuples agrees with evaluating the rewritten query
under the plain semantics over the composite database. This is the
general-syntax form of the classical rewriting correctness. -/
theorem AggQueryIn.rewriting_valid {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ) (hq : q.classical) (d : AnnotatedDatabase T K) :
    (q.evaluateAnnotated d).toComposite
      = (q.rewriting hq).evaluatePlain d.toComposite := by
  rw [AggQueryIn.strip_bridge q hq d,
    Query.rewriting_valid (q.strip hq) (q.strip_source hq) d,
    AggQueryIn.rewriting_plain q hq d.toComposite]

end Correctness
