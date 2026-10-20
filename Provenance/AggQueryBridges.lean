/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryAdequacy

/-!
# Regression bridges for the general evaluator

The fused `HAVING` operator is recovered from the decomposed general
syntax: on its fragment – one aggregate comparison directly above the
grouping – the general evaluator `σ_ψ ∘ Gamma` computes exactly the fused
semantics in closed form (`AggQueryIn.havingSite_evaluateAnnotated`).
Row by row, the pending group factor introduced by `Gamma` is superseded
by the predicate provenance of the comparison (the token's `predProv`,
which is the fused `Having.havingProv` by `AggValue.predProv_ofGroup`),
and the data part collapses to the whole-group aggregate values.

Every theorem about the fused semantics – the possible-world collapses of
`Provenance.HavingSemantics`, the query-level correctness results – is
therefore stated directly against the general evaluator, with this closed
form as the working lemma; no separate fused evaluator is needed. The
kind transport `AggQueryIn.castKind` is transparent to evaluation
(`AggQueryIn.evaluate_castKind`).
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-- A term over the group key, embedded as a term over the key columns of
a `Gamma` output. -/
def TermIn.toGenKey {n₁ : ℕ} (n₂ : ℕ) :
    Term T n₁ → TermG T (ColKind.gammaKinds n₁ n₂)
  | .const a => .const a
  | .index k => .index (Fin.castAdd n₂ k) (by simp [ColKind.gammaKinds])
  | .add t₁ t₂ => .add (t₁.toGenKey n₂) (t₂.toGenKey n₂)
  | .sub t₁ t₂ => .sub (t₁.toGenKey n₂) (t₂.toGenKey n₂)
  | .mul t₁ t₂ => .mul (t₁.toGenKey n₂) (t₂.toGenKey n₂)
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    .caseWhen op (t₁.toGenKey n₂) (t₂.toGenKey n₂) (t₃.toGenKey n₂)
      (t₄.toGenKey n₂)
  | .coalesce t₁ t₂ => .coalesce (t₁.toGenKey n₂) (t₂.toGenKey n₂)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The embedded key term evaluates on a `Gamma` output row as the
original term on the group key. -/
theorem TermIn.toGenKey_eval {n₁ n₂ : ℕ} (s : Term T n₁) (g : Tuple T n₁)
    (h : Fin n₂ → AggTok T K) :
    (s.toGenKey n₂).eval
        (Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
          (fun j => Sum.inr (h j)))
      = s.eval g := by
  induction s with
  | const a => rfl
  | outer k => exact k.elim0
  | index k =>
    show AggValue.collapseSum
        (Fin.append _ _ (Fin.castAdd n₂ k)) = g k
    rw [Fin.append_left]
    rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermIn.toGenKey, TermGIn.eval, ih₁, ih₂]; rfl
  | sub t₁ t₂ ih₁ ih₂ => rw [TermIn.toGenKey, TermGIn.eval, ih₁, ih₂]; rfl
  | mul t₁ t₂ ih₁ ih₂ => rw [TermIn.toGenKey, TermGIn.eval, ih₁, ih₂]; rfl
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    rw [TermIn.toGenKey, TermGIn.eval, ih₁, ih₂, ih₃, ih₄]; rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    rw [TermIn.toGenKey, TermGIn.eval, ih₁, ih₂]; rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The annotation list of a group token is the group's annotation list. -/
theorem AggValue.annList_ofGroup {c m : ℕ} (f : SeqAggFunc T)
    (t : TermIn T c m) (U : List (AnnotatedTuple T K m)) {γ : Fin c → T} :
    (AggValue.ofGroup f t U γ).occs.map Prod.snd = U.map Prod.snd := by
  show (U.map (fun p => (t.eval p.fst γ, p.snd))).map Prod.snd = _
  rw [List.map_map]
  rfl

/-- The fused aggregate comparison, as a generalized selection atom on a
`Gamma` output: the `l`-th token column compared against a term over the
group key. -/
def GenPredIn.fusedCmp {n₁ n₂ : ℕ} (op : CompOp) (l : Fin n₂)
    (s : Term T n₁) : GenPred T (ColKind.gammaKinds n₁ n₂) :=
  GenPredIn.aggCmp (Fin.natAdd n₁ l) (by simp [ColKind.gammaKinds]) op
    (s.toGenKey n₂)

/-- The fused `HAVING` site as a general query: one aggregate comparison
directly above the grouping. -/
abbrev AggQueryIn.havingSite {m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁)
    (ts : Tuple (Term T m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (op : CompOp) (l : Fin n₂) (s : Term T n₁)
    (qg : AggQuery T m (ColKind.allReg m)) :
    AggQuery T (n₁ + n₂) (ColKind.gammaKinds n₁ n₂) :=
  AggQueryIn.Sel (GenPredIn.fusedCmp op l s) (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) is
      ts fs qg)

omit [HasAltLinearOrder K] in
/-- **A regular test conjoined to a predicate** multiplies its joint
reading by the test's characteristic value: the test reads no aggregate
value, so it holds or fails in every world alike. -/
theorem GenPredIn.predsemJ_and_cmp {c n : ℕ} {κ : Fin n → ColKind} (op : CompOp)
    (t₁ t₂ : TermGIn T c κ) (ψ : GenPredIn T c κ) (u : Tuple (GenValue T K) n)
    (γ : Fin c → T) :
    (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsemJ false u γ
      = Having.chi op (t₁.eval u γ) (t₂.eval u γ) * ψ.predsemJ false u γ := by
  unfold GenPredIn.predsemJ
  rw [show ((GenPredIn.cmp op t₁ t₂).and ψ).comparedCols = ψ.comparedCols from by
    simp [GenPredIn.comparedCols], ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun w _ => ?_))
  simp only [GenPredIn.eval3W, Bool.false_eq_true, ite_false, Having.chi]
  by_cases h₁ : op.eval3 (t₁.eval u γ) (t₂.eval u γ) = Kleene.true
  · rw [h₁, ite_eq_left rfl, one_mul]
    generalize ψ.eval3W w.2.2 u γ = b
    cases b <;> simp [Kleene.and]
  · rw [ite_eq_right h₁, zero_mul, ite_eq_right, mul_zero]
    intro h
    exact h₁ ((Kleene.and_eq_true_iff _ _).mp h).1

omit [HasAltLinearOrder K] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The predicate at given values reads them only at its compared
columns. -/
theorem GenPredIn.eval3W_congr {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    {v v' : Fin n → Option T} (u : Tuple (GenValue T K) n) (γ : Fin c → T)
    (h : ∀ k ∈ φ.comparedCols, v k = v' k) : φ.eval3W v u γ = φ.eval3W v' u γ := by
  induction φ with
  | cmp op t₁ t₂ => rfl
  | aggCmp k hk op t => simp only [GenPredIn.eval3W, h k (Finset.mem_singleton_self k)]
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.eval3W, h k (Finset.mem_singleton_self k)]
  | and φ ψ ihφ ihψ =>
    simp only [GenPredIn.eval3W, ihφ (fun k hk => h k (Finset.mem_union_left _ hk)),
      ihψ (fun k hk => h k (Finset.mem_union_right _ hk))]
  | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.eval3W, ihφ (fun k hk => h k (Finset.mem_union_left _ hk)),
      ihψ (fun k hk => h k (Finset.mem_union_right _ hk))]
  | not φ ih => simp only [GenPredIn.eval3W, ih h]

omit [HasAltLinearOrder K] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The predicate at given values reads the row only through its terms. -/
theorem GenPredIn.eval3W_congr_terms {K' : Type} [CommSemiringWithMonus K'] {c n : ℕ}
    {κ : Fin n → ColKind} (φ : GenPredIn T c κ) (v : Fin n → Option T)
    {u' : Tuple (GenValue T K') n} {u : Tuple (GenValue T K) n} {γ : Fin c → T}
    (h : ∀ t : TermGIn T c κ, t.eval u' γ = t.eval u γ) :
    φ.eval3W v u' γ = φ.eval3W v u γ := by
  induction φ with
  | cmp op t₁ t₂ => simp only [GenPredIn.eval3W, h t₁, h t₂]
  | aggCmp k hk op t => simp only [GenPredIn.eval3W, h t]
  | aggRange k hk op₁ t₁ op₂ t₂ => simp only [GenPredIn.eval3W, h t₁, h t₂]
  | and φ ψ ihφ ihψ => simp only [GenPredIn.eval3W, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [GenPredIn.eval3W, ihφ, ihψ]
  | not φ ih => simp only [GenPredIn.eval3W, ih]

omit [HasAltLinearOrder K] in
/-- **A predicate comparing no aggregate column** is read in the one
empty world: its joint reading is its truth there. -/
theorem GenPredIn.predsemJ_of_no_token {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (neg : Bool) (u : Tuple (GenValue T K) n) (γ : Fin c → T)
    (h : ∀ k ∈ φ.comparedCols, ∀ x, u k ≠ Sum.inr x) :
    φ.predsemJ neg u γ
      = if φ.eval3W (fun _ => none) u γ = (if neg then Kleene.false else Kleene.true)
        then 1 else 0 := by
  have ht : tokCols u ((List.finRange n).filter (· ∈ φ.comparedCols)) = [] := by
    unfold tokCols
    refine List.filterMap_eq_nil_iff.mpr (fun k hk => ?_)
    have hk' : k ∈ φ.comparedCols := by simpa using (List.mem_filter.mp hk).2
    cases hu : u k with
    | inl w => rfl
    | inr x => exact absurd hu (h k hk' x)
  unfold GenPredIn.predsemJ jointWorlds
  rw [ht]
  simp [monus_zero]

omit [HasAltLinearOrder K] in
open Classical in
/-- **A predicate comparing one aggregate column** is that column's
reading of the test the predicate makes of its value. -/
theorem GenPredIn.predsemJ_of_single {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (neg : Bool) (u : Tuple (GenValue T K) n) (γ : Fin c → T)
    (k : Fin n) (hk : φ.comparedCols = {k}) (x : AggTok T K) (hu : u k = Sum.inr x) :
    φ.predsemJ neg u γ
      = x.predProvOfWith (fun a =>
          if φ.eval3W (fun j => if j = k then some a else none) u γ
              = (if neg then Kleene.false else Kleene.true)
          then Kleene.true else Kleene.false) := by
  unfold GenPredIn.predsemJ
  rw [hk, filter_finRange_singleton, jointWorlds_single u k x hu, Multiset.map_map,
    ← classWorlds_sum_single u k x hu]
  congr 1
  refine Multiset.map_congr rfl (fun w hw => ?_)
  obtain ⟨a, ha⟩ : ∃ a, w.2.2 k = some a := by
    cases x <;> simp only [classWorlds] at hw <;> obtain ⟨W, -, rfl⟩ := Multiset.mem_map.mp hw <;>
      simp [hu]
  have hv : (combineW w (1, 0, fun _ => none)).2.2 = w.2.2 := by
    funext j; simp [combineW]
  simp only [Function.comp_apply]
  rw [show (combineW w (1, 0, fun _ => none)).1 = w.1 from mul_one _,
    show (combineW w (1, 0, fun _ => none)).2.1 = w.2.1 from add_zero _, hv, ha]
  rw [GenPredIn.eval3W_congr φ u γ (v' := fun j => if j = k then some a else none)
    (fun j hj => by
      rw [hk, Finset.mem_singleton] at hj
      subst hj; simp [ha])]
  simp only [Option.elim, Having.chiOf]
  split_ifs <;> simp_all

/-- **Closed form of the fused `HAVING` site.** On its fragment – one
aggregate comparison directly above the grouping – the general evaluator
produces one row per group key of the subquery, carrying the key followed
by the whole-group aggregate values and annotated by the predicate
provenance `Having.havingProv` of the group's occurrence sequence. This
is what makes the fused site a theorem rather than a semantics of its
own: the pending group factor introduced by `Gamma` is superseded by the
comparison's predicate provenance, and the data part collapses to the
whole-group aggregate values. -/
theorem AggQueryIn.havingSite_evaluateAnnotated {m n₁ n₂ : ℕ}
    (is : Tuple (Fin m) n₁) (ts : Tuple (Term T m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (op : CompOp) (l : Fin n₂)
    (s : Term T n₁) (qg : AggQuery T m (ColKind.allReg m))
    (d : AnnotatedDatabase T K) :
    (AggQueryIn.havingSite is ts fs op l s qg).evaluateAnnotated d
      = (Multiset.dedup ((qg.evaluateAnnotated d).map
            (fun p => fun k : Fin n₁ => p.fst (is k)))).map
          (fun g =>
            ((Fin.append g (fun k => (fs k)
                ((Having.havingGroup is (qg.evaluateAnnotated d) g).map
                  (fun p => (ts k).eval p.fst))),
              Having.havingProv
                (Having.havingGroup is (qg.evaluateAnnotated d) g)
                (ts l) (fs l) op (s.eval g))
              : AnnotatedTuple T K (n₁ + n₂))) := by
  unfold AggQueryIn.evaluateAnnotated
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_left (show (GenPredIn.fusedCmp (T := T) op l s).hasAggAtom = true
    from rfl)]
  generalize Multiset.map GenRow.toAnnotated (qg.evaluate d) = A
  conv_lhs => rw [Multiset.map_map]
  conv_lhs => rw [Multiset.map_map]
  have hkeys : Multiset.map Prod.fst (Multiset.ofList (groupByKey
        (A.map (fun p =>
          ((fun k => p.fst (is k), p.snd) : AnnotatedTuple T K n₁)))).val)
      = Multiset.dedup (A.map
          (fun p => fun k : Fin n₁ => p.fst (is k))) := by
    rw [map_fst_groupByKey, Multiset.map_map]
    rfl
  rw [← hkeys, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro kv _
  simp only [Function.comp_apply]
  unfold GenRow.toAnnotated
  refine Prod.ext ?_ ?_
  · -- data part: whole-group aggregate values
    exact (GenRow.plainTuple_append kv.fst
        (fun j => (AggTok.tok (AggValue.ofGroup (fs j) (ts j)
          (Having.havingGroup is A kv.fst))).setFam (FamId.mk 0 (List.ofFn kv.fst) [] j []))).trans
      (congrArg (Fin.append kv.fst)
        (funext fun j => (AggTok.collapse_setFam (FamId.mk 0 (List.ofFn kv.fst) [] j [])
          (AggTok.tok (AggValue.ofGroup (fs j) (ts j) (Having.havingGroup is A kv.fst)))).trans
          (AggValue.collapse_ofGroup (fs j) (ts j) _)))
  · -- annotation: the predicate provenance of the comparison
    show GenAnn.finalize ⟨1 * _, _⟩ = _
    simp only [GenPredIn.fusedCmp]
    rw [GenPredIn.predsemJ_aggCmp _ _ _ _ _ _ _ (Fin.append_right _ _ l)]
    simp only [GenPredIn.comparedCols,
      Finset.singleton_val, ← Multiset.cons_zero, Multiset.filterMap_cons,
      Multiset.filterMap_zero, Fin.append_right, AggValue.annList_ofGroup,
      Option.map_some, Option.getD_some, add_zero,
      Multiset.filter_cons, Multiset.filter_zero, Multiset.cons_ne_zero,
      ne_eq, not_false_eq_true, Multiset.forall_mem_cons,
      Multiset.notMem_zero, IsEmpty.forall_iff, implies_true, and_true,
      true_and, not_true, ite_false,
      GenPredIn.entailsExistence, ite_true,
      GenAnn.finalize_of_pending_zero, one_mul, TermIn.toGenKey_eval,
      Bool.false_eq_true,
      AggTok.setFam_tok, AggTok.predProvOf, AggTok.predProvOfWith, AggTok.scalar,
      AggTok.annList, AggValue.scalar_ofGroup,
      Option.map_none, Option.getD_none]
    exact AggValue.predProv_ofGroup (fs l) (ts l)
      (Having.havingGroup is A kv.fst) op (s.eval kv.fst)

/-! ## A predicate over two groups keeps both groups' factors

The general evaluator drops a pending group factor only where *every*
compared token carries that group's annotation list. A predicate reading
two groups therefore removes nothing: both factors stay pending, and
`GenAnn.finalize` cashes them into the row's annotation.

This is what keeps the `⊕` of a disjunction from ever being read on its
own. The predicate provenance of `φ₁ ∨ φ₂` over two groups can be
non-`𝟘` in worlds where neither group is read at all – `𝔹` with both
disjuncts on `⊤` is the instance – and it is the factors the row keeps
that make the row's annotation `𝟘` there. -/
theorem AggQueryIn.evaluate_Sel_of_two_groups {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (q : AggQueryIn T c n κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (hagg : φ.hasAggAtom = true)
    (htwo : ∀ r ∈ q.evaluate d γ, ∃ k₁ ∈ φ.comparedCols, ∃ k₂ ∈ φ.comparedCols,
      ∃ a₁ a₂ : AggTok T K, r.fst k₁ = Sum.inr a₁ ∧ r.fst k₂ = Sum.inr a₂ ∧
        a₁.annList ≠ a₂.annList) :
    (AggQueryIn.Sel φ q).evaluate d γ
      = (q.evaluate d γ).map (fun r =>
          (⟨r.fst, ⟨r.snd.base * φ.predsemJ false r.fst γ, r.snd.pending⟩⟩
            : GenRow T K n)) := by
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_left hagg]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  obtain ⟨k₁, hk₁, k₂, hk₂, a₁, a₂, he₁, he₂, hne⟩ := htwo r hr
  refine congrArg
    (fun p => (⟨r.fst, ⟨r.snd.base * φ.predsemJ false r.fst γ, p⟩⟩
      : GenRow T K n)) ?_
  split
  · refine Multiset.filter_eq_self.mpr (fun l _ => ?_)
    rintro ⟨-, -, hall⟩
    exact hne (((hall _ ((Multiset.mem_filterMap _ _).mpr
        ⟨k₁, Finset.mem_val.mpr hk₁, by rw [he₁]⟩)).trans
      (hall _ ((Multiset.mem_filterMap _ _).mpr
        ⟨k₂, Finset.mem_val.mpr hk₂, by rw [he₂]⟩)).symm))
  · rfl

/-- **The disjunction of two aggregate atoms over two groups keeps both
group factors.** The instance of `AggQueryIn.evaluate_Sel_of_two_groups`
the `∨` rule is about: the row's annotation is the disjunction's `⊕`
times every group's pending factor, never the `⊕` alone. -/
theorem AggQueryIn.evaluate_Sel_or_of_two_groups {c n : ℕ}
    {κ : Fin n → ColKind} {k₁ k₂ : Fin n} (h₁ : κ k₁ = ColKind.agg)
    (h₂ : κ k₂ = ColKind.agg) (op₁ op₂ : CompOp) (t₁ t₂ : TermGIn T c κ)
    (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (hdis : ∀ r ∈ q.evaluate d γ, ∃ a₁ a₂ : AggTok T K,
      r.fst k₁ = Sum.inr a₁ ∧ r.fst k₂ = Sum.inr a₂ ∧
        a₁.annList ≠ a₂.annList) :
    (AggQueryIn.Sel (GenPredIn.or (GenPredIn.aggCmp k₁ h₁ op₁ t₁)
        (GenPredIn.aggCmp k₂ h₂ op₂ t₂)) q).evaluate d γ
      = (q.evaluate d γ).map (fun r =>
          (⟨r.fst, ⟨r.snd.base * (GenPredIn.or (GenPredIn.aggCmp k₁ h₁ op₁ t₁)
              (GenPredIn.aggCmp k₂ h₂ op₂ t₂)).predsemJ false r.fst γ,
            r.snd.pending⟩⟩ : GenRow T K n)) :=
  AggQueryIn.evaluate_Sel_of_two_groups _ q d γ rfl
    (fun r hr => by
      obtain ⟨a₁, a₂, he₁, he₂, hne⟩ := hdis r hr
      exact ⟨k₁, by simp [GenPredIn.comparedCols], k₂,
        by simp [GenPredIn.comparedCols], a₁, a₂, he₁, he₂, hne⟩)

/-! ## A projection that keeps every group's tokens changes nothing

The projection clause cashes the pending factors of the groups whose
token columns it drops. Where it drops none – a reordering, a renaming,
anything keeping every token column a pending factor belongs to – the
concrete part and the pending part come through untouched, so such a
projection standing inside a chain of aggregate selections changes
neither the families the chain reads nor the annotation it builds. -/
theorem AggQueryIn.evaluate_Proj_of_pending_le {c n m : ℕ}
    {κ : Fin n → ColKind} (ps : Fin m → ProjColIn T c κ)
    (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (h : ∀ r ∈ q.evaluate d γ,
      r.snd.pending ≤ tokenLists (fun j => (ps j).eval r.fst γ)) :
    (AggQueryIn.Proj ps q).evaluate d γ
      = (q.evaluate d γ).map (fun r =>
          ((fun j => (ps j).eval r.fst γ, r.snd) : GenRow T K m)) := by
  simp only [AggQueryIn.evaluate]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  have hk : r.snd.pending ∩ tokenLists (fun j => (ps j).eval r.fst γ)
      = r.snd.pending :=
    le_antisymm Multiset.inter_le_left
      (Multiset.le_inter (le_refl _) (h r hr))
  refine Prod.ext rfl ?_
  show (⟨r.snd.base * _, _⟩ : GenAnn K) = r.snd
  rw [hk, tsub_self, Multiset.map_zero, Multiset.prod_zero, mul_one]

/-! ## Equality up to impossible rows

A tuple annotated `𝟘` holds in no world, so an implementation is free
to drop it. Two annotated relations that agree after that removal say
the same thing about every world, and some equalities between query
spellings hold only in that sense. -/

omit [CommSemiringWithMonus K] [HasAltLinearOrder K] in
/-- Filtering the image of a map is mapping the filtered source. -/
theorem Multiset.filter_map_comm {α β : Type} (f : α → β) (p : β → Prop)
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

/-- **Dropping the impossible rows**: what is left of an annotated
relation when the tuples annotated `𝟘` – those in no world – are
removed. (Not `AnnotatedRelation.support`, which is the `𝔹`-specific
data-part reading of `Provenance.SupportAdequacy`.) -/
def AnnotatedRelation.dropZero {n : ℕ} (r : AnnotatedRelation T K n) :
    AnnotatedRelation T K n :=
  Multiset.filter (fun p => p.snd ≠ 0) r

/-- **Equality up to impossible rows.**

This drops `𝟘`-annotated *tuples* only. It is stated on annotated
relations, where that is all there is to drop: `GenRow.toAnnotated`
collapses every aggregate column through `GenRow.plainTuple`, so a
finalized relation carries no aggregate value and hence no occurrence
annotation. A coarser equivalence that also dropped the `𝟘`-annotated
occurrences *inside* aggregate values would differ from this one on
`GenRow`s, which still carry their tokens, and coincide with it on
everything `evaluateAnnotated` returns. -/
def AnnotatedRelation.ZEq {n : ℕ} (r s : AnnotatedRelation T K n) : Prop :=
  r.dropZero = s.dropZero

omit [ValueType T] [HasAltLinearOrder K] in
/-- Two readings of a source agree up to impossible rows when they agree
wherever a test holds and the second annotates `𝟘` wherever it fails. -/
theorem dropZero_map_filter {α : Type} {n : ℕ} (s : Multiset α)
    (F G : α → AnnotatedTuple T K n) (P : α → Prop) [DecidablePred P]
    (hP : ∀ a ∈ s, ¬ P a → (G a).snd = 0)
    (hFG : ∀ a ∈ s, P a → F a = G a) :
    AnnotatedRelation.dropZero ((s.filter P).map F)
      = AnnotatedRelation.dropZero (s.map G) := by
  unfold AnnotatedRelation.dropZero
  rw [Multiset.filter_map_comm, Multiset.filter_map_comm,
    Multiset.filter_filter]
  refine Multiset.map_congr (Multiset.filter_congr (fun a ha => ?_))
    (fun a ha => ?_)
  · by_cases hp : P a
    · rw [hFG a ha hp]
      exact ⟨fun h => h.1, fun h => ⟨h, hp⟩⟩
    · exact ⟨fun h => absurd h.2 hp, fun h => absurd (hP a ha hp) h⟩
  · have hmem := Multiset.mem_of_mem_filter ha
    refine hFG a hmem ?_
    by_contra hc
    exact Multiset.of_mem_filter ha (hP a hmem hc)

/-- **A regular selection may be absorbed into the aggregate predicate
below it – up to impossible rows, and not up to equality of relations.**

A selection whose predicate has an aggregate atom keeps every row,
annotating the failing ones `𝟘`; a selection on regular columns removes
them. So the chain and the single selection on the conjunction give the
same annotation to every row the regular test keeps, and part on the
rows it rejects: gone on one side, present annotated `𝟘` on the other.
They therefore have the same support and are not the same relation,
which is the equality a normalization rewriting a chain into one
predicate can claim and the one it cannot. -/
theorem AggQueryIn.evaluate_Sel_reg_absorb {c n : ℕ} {κ : Fin n → ColKind}
    (op : CompOp) (t₁ t₂ : TermGIn T c κ) (ψ : GenPredIn T c κ)
    (hψ : ψ.hasAggAtom = true) (q : AggQueryIn T c n κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    AnnotatedRelation.ZEq
      ((AggQueryIn.Sel (GenPredIn.cmp op t₁ t₂)
        (AggQueryIn.Sel ψ q)).evaluateAnnotated d γ)
      ((AggQueryIn.Sel (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ)
        q).evaluateAnnotated d γ) := by
  unfold AnnotatedRelation.ZEq AggQueryIn.evaluateAnnotated
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_right (show ¬ (GenPredIn.cmp (T := T) (κ := κ) op t₁ t₂).hasAggAtom
      = true from by simp [GenPredIn.hasAggAtom]),
    ite_eq_left hψ,
    ite_eq_left (show (GenPredIn.and (GenPredIn.cmp (T := T) (κ := κ) op t₁ t₂)
        ψ).hasAggAtom = true from by simp [GenPredIn.hasAggAtom, hψ])]
  rw [Multiset.filter_map_comm]
  simp only [Multiset.map_map]
  apply dropZero_map_filter
  · intro r hr hnot
    have hchi : Having.chi (K := K) op (t₁.eval r.fst γ) (t₂.eval r.fst γ)
        = 0 := ite_eq_right hnot
    show GenAnn.finalize ⟨r.snd.base
      * (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsemJ false r.fst γ, _⟩ = 0
    rw [show (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsemJ false r.fst γ
        = Having.chi op (t₁.eval r.fst γ) (t₂.eval r.fst γ)
          * ψ.predsemJ false r.fst γ from GenPredIn.predsemJ_and_cmp _ _ _ _ _ _, hchi, zero_mul,
        mul_zero]
    unfold GenAnn.finalize
    exact zero_mul _
  · intro r hr hp
    have hchi : Having.chi (K := K) op (t₁.eval r.fst γ) (t₂.eval r.fst γ)
        = 1 := ite_eq_left hp
    refine Prod.ext rfl ?_
    show GenAnn.finalize ⟨r.snd.base * ψ.predsemJ false r.fst γ, _⟩
      = GenAnn.finalize ⟨r.snd.base
        * (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsemJ false r.fst γ, _⟩
    rw [show (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsemJ false r.fst γ
        = Having.chi op (t₁.eval r.fst γ) (t₂.eval r.fst γ)
          * ψ.predsemJ false r.fst γ from GenPredIn.predsemJ_and_cmp _ _ _ _ _ _, hchi, one_mul]
    simp only [GenPredIn.entailsExistence, Bool.false_eq_true, ite_false,
      Bool.false_or]
    rw [show ((GenPredIn.cmp (T := T) (κ := κ) op t₁ t₂).and ψ).comparedCols
        = ψ.comparedCols from by
      simp [GenPredIn.comparedCols]]


/-! ## Guard absorption and the finalize identities

These belong to the *evaluator*, not to any particular metatheorem: an
existence-entailing predicate provenance absorbs the `δ`-guard of the
group it compares, which is what licenses the evaluator's supersede of a
pending factor, and the finalize identities say what the three row
transformations do to the factored annotation. The homomorphism layer and
the rewriting closure both read them. -/

section GuardAbsorption

variable {c n : ℕ} {κ : Fin n → ColKind}

/-! ## Guard absorption

The first substantive use of the `delta_absorb` axiom: an
existence-entailing predicate provenance algebraically absorbs its
group's `δ`-guard. Every monomial of the possible-world sum contains
some occurrence annotation of the group (the worlds are non-empty), and
`delta_absorb` lets that occurrence swallow `δ` of the whole group
sum. -/

omit [HasAltLinearOrder K] in
/-- A token's predicate provenance absorbs the `δ`-guard of its own
group, for an arbitrary test on its value. -/
theorem AggValue.predProvWith_delta_absorb (a : AggValue T K)
    (P : T → Kleene) :
    a.predProvWith P
        * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = a.predProvWith P := by
  unfold AggValue.predProvWith
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun W hW => ?_
  obtain ⟨-, hne⟩ := Finset.mem_filter.mp hW
  obtain ⟨i₀, hi₀⟩ := hne
  have hmem : a.anns i₀ ∈ (↑(a.occs.map Prod.snd) : Multiset K) :=
    Multiset.mem_coe.mpr
      (List.mem_map.mpr ⟨a.occs.get i₀, List.get_mem _ _, rfl⟩)
  have hr : (a.occs.map Prod.snd).sum
      = a.anns i₀ + ((↑(a.occs.map Prod.snd) : Multiset K).erase
          (a.anns i₀)).sum := by
    rw [← Multiset.sum_coe, ← Multiset.sum_cons, Multiset.cons_erase hmem]
  have key : a.anns i₀
      * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = a.anns i₀ := by
    rw [hr]
    exact SemiringWithMonus.delta_absorb _ _
  have hw : Having.worldAnn a.anns W
      = a.anns i₀ * ((∏ i ∈ W.erase i₀, a.anns i)
          * (1 - ∑ i ∈ Wᶜ, a.anns i)) := by
    unfold Having.worldAnn
    rw [← Finset.mul_prod_erase W a.anns hi₀, mul_assoc]
  rw [hw]
  calc a.anns i₀ * ((∏ i ∈ W.erase i₀, a.anns i)
          * (1 - ∑ i ∈ Wᶜ, a.anns i)) * Having.chiOf P (a.valOn W)
        * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = ((∏ i ∈ W.erase i₀, a.anns i) * (1 - ∑ i ∈ Wᶜ, a.anns i)
          * Having.chiOf P (a.valOn W))
        * (a.anns i₀
          * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)) := by
        rw [mul_rotate (a.anns i₀), mul_assoc]
    _ = ((∏ i ∈ W.erase i₀, a.anns i) * (1 - ∑ i ∈ Wᶜ, a.anns i)
          * Having.chiOf P (a.valOn W)) * a.anns i₀ := by
        rw [key]
    _ = a.anns i₀ * ((∏ i ∈ W.erase i₀, a.anns i)
          * (1 - ∑ i ∈ Wᶜ, a.anns i)) * Having.chiOf P (a.valOn W) :=
        (mul_rotate _ _ _).symm

omit [HasAltLinearOrder K] in
/-- The comparison case. -/
theorem AggValue.predProv_delta_absorb (a : AggValue T K) (op : CompOp)
    (c : T) :
    a.predProv op c
        * SemiringWithMonus.delta ((a.occs.map Prod.snd).sum)
      = a.predProv op c :=
  AggValue.predProvWith_delta_absorb a (fun v => op.eval3 v c)

omit [HasAltLinearOrder K] in
/-- **Guard absorption for entailing predicates**: when a predicate
entails existence and all its compared tokens carry the annotation list
`ℓ₀`, its predicate provenance absorbs `δ(⊕ℓ₀)`. -/
theorem GenPredIn.predsem_delta_absorb {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) {γ : Fin c → T} (neg : Bool) (u : Tuple (GenValue T K) n)
    (ℓ₀ : List K)
    (huni : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀)
    (hent : φ.entailsExistence neg = true) :
    φ.predsem neg u γ * SemiringWithMonus.delta ℓ₀.sum
      = φ.predsem neg u γ := by
  induction φ generalizing neg with
  | cmp op t₁ t₂ => exact absurd hent (by simp [GenPredIn.entailsExistence])
  | aggCmp k h op t =>
    cases hu : u k with
    | inl w => simp only [GenPredIn.predsem, hu, zero_mul]
    | inr x =>
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) x hu
      cases x with
      | tok a =>
        simp only [AggTok.scalar_tok] at hsc
        simp only [AggTok.annList_tok] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOf_tok]
        rw [AggValue.predProvOf_of_grouped hsc, ← heq]
        exact AggValue.predProv_delta_absorb a _ _
      | nest b =>
        simp only [AggTok.scalar_nest] at hsc
        simp only [AggTok.annList_nest] at heq
        simp only [GenPredIn.predsem, AggTok.predProvOf, hu,
          AggTok.predProvOfWith]
        rw [← heq, List.sum_singleton]
        exact NestedValue.predProvWith_delta_absorb b hsc _
      | expr e =>
        simp only [AggTok.scalar_expr] at hsc
        simp only [AggTok.annList_expr] at heq
        simp only [GenPredIn.predsem, AggTok.predProvOf, hu,
          AggTok.predProvOfWith_expr]
        rw [← heq]
        exact AggExpr.predProvWith_delta_absorb e
          (AggExpr.exists_grouped_of_not_isScalar hsc) _
  | aggRange k h op₁ t₁ op₂ t₂ =>
    cases hu : u k with
    | inl w => simp only [GenPredIn.predsem, hu, zero_mul]
    | inr x =>
      obtain ⟨hsc, heq⟩ := huni k (Finset.mem_singleton_self k) x hu
      cases x with
      | tok a =>
        simp only [AggTok.scalar_tok] at hsc
        simp only [AggTok.annList_tok] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith_tok]
        rw [AggValue.predProvOfWith, hsc, ite_eq_right Bool.false_ne_true,
          ← heq]
        exact AggValue.predProvWith_delta_absorb a _
      | nest b =>
        simp only [AggTok.scalar_nest] at hsc
        simp only [AggTok.annList_nest] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith]
        rw [← heq, List.sum_singleton]
        exact NestedValue.predProvWith_delta_absorb b hsc _
      | expr e =>
        simp only [AggTok.scalar_expr] at hsc
        simp only [AggTok.annList_expr] at heq
        simp only [GenPredIn.predsem, hu, AggTok.predProvOfWith_expr]
        rw [← heq]
        exact AggExpr.predProvWith_delta_absorb e
          (AggExpr.exists_grouped_of_not_isScalar hsc) _
  | and φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.and φ ψ).predsem false u γ
          = φ.predsem false u γ * ψ.predsem false u γ := rfl
      have hent' : (φ.entailsExistence false || ψ.entailsExistence false)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rw [he]
      rcases hent' with h | h
      · calc φ.predsem false u γ * ψ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = ψ.predsem false u γ * (φ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum) := by
              rw [mul_comm (φ.predsem false u γ) (ψ.predsem false u γ), mul_assoc]
          _ = ψ.predsem false u γ * φ.predsem false u γ := by
              rw [ihφ false huφ h]
          _ = φ.predsem false u γ * ψ.predsem false u γ := mul_comm _ _
      · calc φ.predsem false u γ * ψ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = φ.predsem false u γ * (ψ.predsem false u γ
              * SemiringWithMonus.delta ℓ₀.sum) := mul_assoc _ _ _
          _ = φ.predsem false u γ * ψ.predsem false u γ := by
              rw [ihψ false huψ h]
    | true =>
      have he : (GenPredIn.and φ ψ).predsem true u γ
          = φ.predsem true u γ + ψ.predsem true u γ := rfl
      have hent' : (φ.entailsExistence true && ψ.entailsExistence true)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [he, add_mul, ihφ true huφ hent'.1, ihψ true huψ hent'.2]
  | or φ ψ ihφ ihψ =>
    have huφ : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_left _ hk)
    have huψ : ∀ k ∈ ψ.comparedCols, ∀ a : AggTok T K,
        u k = Sum.inr a → a.scalar = false ∧ a.annList = ℓ₀ :=
      fun k hk => huni k (Finset.mem_union_right _ hk)
    cases neg with
    | false =>
      have he : (GenPredIn.or φ ψ).predsem false u γ
          = φ.predsem false u γ + ψ.predsem false u γ := rfl
      have hent' : (φ.entailsExistence false && ψ.entailsExistence false)
          = true := hent
      rw [Bool.and_eq_true] at hent'
      rw [he, add_mul, ihφ false huφ hent'.1, ihψ false huψ hent'.2]
    | true =>
      have he : (GenPredIn.or φ ψ).predsem true u γ
          = φ.predsem true u γ * ψ.predsem true u γ := rfl
      have hent' : (φ.entailsExistence true || ψ.entailsExistence true)
          = true := hent
      rw [Bool.or_eq_true] at hent'
      rw [he]
      rcases hent' with h | h
      · calc φ.predsem true u γ * ψ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = ψ.predsem true u γ * (φ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum) := by
              rw [mul_comm (φ.predsem true u γ) (ψ.predsem true u γ), mul_assoc]
          _ = ψ.predsem true u γ * φ.predsem true u γ := by
              rw [ihφ true huφ h]
          _ = φ.predsem true u γ * ψ.predsem true u γ := mul_comm _ _
      · calc φ.predsem true u γ * ψ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum
            = φ.predsem true u γ * (ψ.predsem true u γ
              * SemiringWithMonus.delta ℓ₀.sum) := mul_assoc _ _ _
          _ = φ.predsem true u γ * ψ.predsem true u γ := by
              rw [ihψ true huψ h]
  | not φ ih =>
    have he : (GenPredIn.not φ).predsem neg u γ = φ.predsem (!neg) u γ := rfl
    rw [he]
    exact ih (!neg) huni hent

omit [HasAltLinearOrder K] in
/-- An existence-entailing predicate provenance absorbs the `δ`-guards of
any collection of pending factors, each of which is the occurrence list of
*every* compared token. -/
theorem GenPredIn.predsem_absorb_prod (φ : GenPredIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) (hent : φ.entailsExistence false = true)
    (D : Multiset (List K))
    (hD : ∀ l ∈ D, ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.scalar = false ∧ a.annList = l) :
    φ.predsem false u γ
        * (D.map (fun l => SemiringWithMonus.delta l.sum)).prod
      = φ.predsem false u γ := by
  induction D using Multiset.induction_on with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, mul_one]
  | cons l D ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc,
      GenPredIn.predsem_delta_absorb φ false u l
        (fun k hk a hka => hD l (Multiset.mem_cons_self l D) k hk a hka) hent]
    exact ih (fun l' hl' => hD l' (Multiset.mem_cons_of_mem hl'))

omit [HasAltLinearOrder K] in
/-- An annotation of a list absorbs `δ` of its sum. -/
theorem delta_absorb_of_mem {l : List K} {a : K} (h : a ∈ l) :
    a * SemiringWithMonus.delta l.sum = a := by
  rw [(List.perm_cons_erase h).sum_eq, List.sum_cons]
  exact SemiringWithMonus.delta_absorb _ _

omit [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
theorem AggTok.flatExpr_isScalar_of_not_nest (x : AggTok T K) (hx : x.isNested = false) :
    x.flatExpr.isScalar = x.scalar := by
  cases x with
  | tok a => exact AggExpr.isScalar_ofValue a
  | expr e => rfl
  | nest a => exact absurd hx (by simp [AggTok.isNested])

omit [HasAltLinearOrder K] [ValueType T] [DecidableEq K] in
theorem AggTok.flatExpr_annList_of_not_nest (x : AggTok T K) (hx : x.isNested = false) :
    x.flatExpr.annList = x.annList := by
  cases x with
  | tok a => exact AggExpr.annList_ofValue a
  | expr e => rfl
  | nest a => exact absurd hx (by simp [AggTok.isNested])

omit [HasAltLinearOrder K] [ValueType T] in
/-- A world of a grouped expression keeps one of its occurrences, whose
annotation absorbs `δ` of the family's sum. -/
theorem AggExpr.prod_world_absorb (e : AggExpr T K) (hsc : e.isScalar = false)
    (W : Finset (Fin e.occs.length)) (hW : e.IsWorld W) :
    (∏ i ∈ W, e.anns i) * SemiringWithMonus.delta e.annList.sum = ∏ i ∈ W, e.anns i := by
  obtain ⟨l, hl⟩ := AggExpr.exists_grouped_of_not_isScalar hsc
  obtain ⟨i₀, hi₀⟩ := hW l hl
  have hi : i₀ ∈ W := (Finset.mem_inter.mp hi₀).1
  have hm : e.anns i₀ ∈ e.annList := List.mem_map.mpr ⟨e.occs.get i₀, List.get_mem _ _, rfl⟩
  rw [← Finset.mul_prod_erase W _ hi, mul_right_comm, delta_absorb_of_mem hm]

omit [HasAltLinearOrder K] in
open Classical in
/-- The worlds of a family whose value is not nested, unfolded. -/
theorem classWorlds_of_not_nest {n : ℕ} (u : Tuple (GenValue T K) n) (M : List (Fin n))
    (x : AggTok T K) (hx : x.isNested = false) :
    classWorlds u M x
      = ((Finset.univ : Finset (Finset (Fin x.flatExpr.occs.length))).filter
          (fun W => flatOk u M W = true)).val.map
        (fun W => (∏ i ∈ W, x.flatExpr.anns i, ∑ i ∈ Wᶜ, x.flatExpr.anns i,
          fun k => if k ∈ M then
            (match u k with
              | Sum.inr y => some (y.flatExpr.valOn (trW W))
              | _ => none) else none)) := by
  cases x with
  | nest a => simp [AggTok.isNested] at hx
  | tok a => rfl
  | expr a => rfl

omit [HasAltLinearOrder K] in
open Classical in
/-- **A world of a grouped family absorbs its guard**: its present
product carries one of the family's annotations. -/
theorem classWorlds_absorb {n : ℕ} (u : Tuple (GenValue T K) n) (M : List (Fin n))
    (x₀ : AggTok T K) {k₀ : Fin n} (hk₀ : k₀ ∈ M) (hu₀ : u k₀ = Sum.inr x₀)
    (hsc : x₀.scalar = false) :
    ∀ w ∈ classWorlds u M x₀, w.1 * SemiringWithMonus.delta x₀.annList.sum = w.1 := by
  intro w hw
  cases x₀ with
  | nest b =>
    simp only [classWorlds] at hw
    obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.mp hw
    have hWb : W.IsWorld b :=
      (nestOk_iff u M W).mp (Multiset.mem_filter.mp hW).2 k₀ hk₀ b hu₀
    have hkept : 0 < Multiset.card W.kept := by
      rcases hWb.1 with hs | hs
      · exact absurd (hsc.symm.trans hs) Bool.false_ne_true
      · exact hs
    show W.presentProd * SemiringWithMonus.delta (AggTok.nest b).annList.sum = W.presentProd
    simp only [AggTok.annList, List.sum_singleton]
    exact NestedValue.World.presentProd_delta_absorb
      (NestedValue.isWorldOf_of_mem_worlds (Multiset.mem_of_mem_filter hW)) hkept
  | tok a =>
    simp only [classWorlds] at hw
    obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.mp hw
    have hWa : (AggTok.tok a).flatExpr.IsWorld W := by
      have := (flatOk_iff u M W).mp (Finset.mem_filter.mp (Finset.mem_val.mp hW)).2 k₀ hk₀ _ hu₀
      simpa only [trW_self] using this
    rw [← AggTok.flatExpr_annList_of_not_nest _ rfl]
    exact AggExpr.prod_world_absorb _
      ((AggTok.flatExpr_isScalar_of_not_nest _ rfl).trans hsc) W hWa
  | expr e =>
    simp only [classWorlds] at hw
    obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.mp hw
    have hWa : (AggTok.expr e).flatExpr.IsWorld W := by
      have := (flatOk_iff u M W).mp (Finset.mem_filter.mp (Finset.mem_val.mp hW)).2 k₀ hk₀ _ hu₀
      simpa only [trW_self] using this
    rw [← AggTok.flatExpr_annList_of_not_nest _ rfl]
    exact AggExpr.prod_world_absorb _
      ((AggTok.flatExpr_isScalar_of_not_nest _ rfl).trans hsc) W hWa

omit [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
theorem mem_tokCols {n : ℕ} {u : Tuple (GenValue T K) n} {cols : List (Fin n)}
    {p : Fin n × AggTok T K} (h : p ∈ tokCols u cols) : p.1 ∈ cols ∧ u p.1 = Sum.inr p.2 := by
  unfold tokCols at h
  obtain ⟨k, hk, hp⟩ := List.mem_filterMap.mp h
  cases hu : u k with
  | inl v => rw [hu] at hp; exact absurd hp (by simp)
  | inr x =>
    rw [hu] at hp
    obtain rfl := Option.some.inj hp
    exact ⟨hk, hu⟩

omit [HasAltLinearOrder K] in
open Classical in
/-- **Every joint world absorbs a grouped guard** its compared values all
carry. -/
theorem jointWorlds_absorb {n : ℕ} (u : Tuple (GenValue T K) n) (cols : List (Fin n))
    (ℓ₀ : List K) (hex : ∃ k ∈ cols, ∃ x, u k = Sum.inr x)
    (huni : ∀ k ∈ cols, ∀ x, u k = Sum.inr x → x.scalar = false ∧ x.annList = ℓ₀) :
    ∀ w ∈ jointWorlds u cols, w.1 * SemiringWithMonus.delta ℓ₀.sum = w.1 := by
  intro w hw
  unfold jointWorlds at hw
  obtain ⟨k, hk, x, hx⟩ := hex
  have hL : (k, x) ∈ tokCols u cols := by
    unfold tokCols
    exact List.mem_filterMap.mpr ⟨k, hk, by simp [hx]⟩
  cases hF : ((tokCols u cols).map (fun p => p.2.classKey)).dedup with
  | nil =>
    have : x.classKey ∈ ((tokCols u cols).map (fun p => p.2.classKey)).dedup :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨_, hL, rfl⟩)
    rw [hF] at this; exact absurd this List.not_mem_nil
  | cons φ G =>
    rw [hF, List.foldr_cons] at hw
    have hφ : φ ∈ (tokCols u cols).map (fun p => p.2.classKey) :=
      List.mem_dedup.mp (hF ▸ List.mem_cons_self)
    cases hf : (tokCols u cols).find? (fun p => p.2.classKey = φ) with
    | none =>
      obtain ⟨p, hp, hpφ⟩ := List.mem_map.mp hφ
      exact absurd (List.find?_eq_none.mp hf p hp) (by simp [hpφ])
    | some p₀ =>
      rw [hf] at hw
      obtain ⟨⟨w₁, w₂⟩, hw₁₂, rfl⟩ := Multiset.mem_map.mp hw
      obtain ⟨hw₁, -⟩ := Multiset.mem_product.mp hw₁₂
      have hp₀ := List.mem_of_find?_eq_some hf
      have hp₀φ : p₀.2.classKey = φ := by simpa using List.find?_some hf
      obtain ⟨hc₀, hu₀⟩ := mem_tokCols hp₀
      obtain ⟨hsc, hann⟩ := huni _ hc₀ _ hu₀
      have hM : p₀.1 ∈ ((tokCols u cols).filter (fun p => p.2.classKey = φ)).map Prod.fst :=
        List.mem_map.mpr ⟨p₀, List.mem_filter.mpr ⟨hp₀, by simp [hp₀φ]⟩, rfl⟩
      have habs := classWorlds_absorb u _ p₀.2 hM hu₀ hsc w₁ hw₁
      rw [hann] at habs
      show w₁.1 * w₂.1 * _ = w₁.1 * w₂.1
      rw [mul_right_comm, habs]

omit [HasAltLinearOrder K] in
open Classical in
/-- A world of one family assigns nothing to the columns outside it. -/
theorem classWorlds_none {n : ℕ} (u : Tuple (GenValue T K) n) (M : List (Fin n))
    (x₀ : AggTok T K) :
    ∀ w ∈ classWorlds u M x₀, ∀ k ∉ M, w.2.2 k = none := by
  intro w hw k hk
  cases x₀ <;> simp only [classWorlds] at hw <;> obtain ⟨W, -, rfl⟩ := Multiset.mem_map.mp hw <;>
    simp [hk]

omit [HasAltLinearOrder K] in
open Classical in
/-- **Reading the joint worlds family by family.** Let `G` be a property
of worlds that holds of the empty one and holds of two worlds read
together exactly when it holds of each. If, in each family of the row,
the worlds satisfying `G` give the family's columns the values `val`,
and some world satisfies `G`, then so do the joint worlds. -/
theorem jointWorlds_of_classes {n : ℕ} (u : Tuple (GenValue T K) n) (cols : List (Fin n))
    (G : K × K × (Fin n → Option T) → Prop) (val : Fin n → T)
    (hinit : G (1, 0, fun _ => none))
    (hcomb : ∀ w₁ w₂, G (combineW w₁ w₂) ↔ G w₁ ∧ G w₂)
    (hclass : ∀ (M : List (Fin n)) (x₀ : AggTok T K),
      (∀ k ∈ M, ∃ y, (k, y) ∈ tokCols u cols ∧ y.classKey = x₀.classKey) →
      (∀ w ∈ classWorlds u M x₀, G w → ∀ k ∈ M, w.2.2 k = some (val k))
        ∧ ∃ w ∈ classWorlds u M x₀, G w) :
    (∀ w ∈ jointWorlds u cols, G w → ∀ p ∈ tokCols u cols, w.2.2 p.1 = some (val p.1))
      ∧ ∃ w ∈ jointWorlds u cols, G w := by
  unfold jointWorlds
  have hkeys : ∀ p ∈ tokCols u cols,
      p.2.classKey ∈ ((tokCols u cols).map (fun p => p.2.classKey)).dedup :=
    fun p hp => List.mem_dedup.mpr (List.mem_map_of_mem hp)
  generalize ((tokCols u cols).map (fun p => p.2.classKey)).dedup = L at hkeys ⊢
  suffices H : (∀ w ∈ L.foldr
          (fun φ acc =>
            match (tokCols u cols).find? (fun p => p.2.classKey = φ) with
            | none => acc
            | some p₀ =>
              ((classWorlds u (((tokCols u cols).filter
                (fun p => p.2.classKey = φ)).map Prod.fst) p₀.2)
                ×ˢ acc).map (fun w => combineW w.1 w.2))
          ({(1, 0, fun _ => none)} : Multiset (K × K × (Fin n → Option T))),
        G w → ∀ p ∈ tokCols u cols, p.2.classKey ∈ L → w.2.2 p.1 = some (val p.1))
      ∧ ∃ w ∈ L.foldr
          (fun φ acc =>
            match (tokCols u cols).find? (fun p => p.2.classKey = φ) with
            | none => acc
            | some p₀ =>
              ((classWorlds u (((tokCols u cols).filter
                (fun p => p.2.classKey = φ)).map Prod.fst) p₀.2)
                ×ˢ acc).map (fun w => combineW w.1 w.2))
          ({(1, 0, fun _ => none)} : Multiset (K × K × (Fin n → Option T))), G w by
    exact ⟨fun w hw hg p hp => H.1 w hw hg p hp (hkeys p hp), H.2⟩
  clear hkeys
  induction L with
  | nil =>
    exact ⟨fun _ _ _ _ _ hp => absurd hp List.not_mem_nil,
      ⟨_, Multiset.mem_singleton_self _, hinit⟩⟩
  | cons φ L ih =>
    obtain ⟨ihA, ihE⟩ := ih
    simp only [List.foldr_cons]
    cases hf : (tokCols u cols).find? (fun p => p.2.classKey = φ) with
    | none =>
      have hno : ∀ p ∈ tokCols u cols, p.2.classKey ≠ φ := by
        intro p hp h
        have := List.find?_eq_none.mp hf p hp
        simp [h] at this
      refine ⟨fun w hw hg p hp hpL => ihA w hw hg p hp ?_, ihE⟩
      rcases List.mem_cons.mp hpL with h | h
      · exact absurd h (hno p hp)
      · exact h
    | some p₀ =>
      have hk₀ : p₀.2.classKey = φ := by simpa using List.find?_some hf
      have hM : ∀ k ∈ ((tokCols u cols).filter (fun p => p.2.classKey = φ)).map Prod.fst,
          ∃ y, (k, y) ∈ tokCols u cols ∧ y.classKey = p₀.2.classKey := by
        intro k hk
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
        obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
        exact ⟨p.2, hp1, by rw [hk₀]; simpa using hp2⟩
      obtain ⟨hcA, hcE⟩ := hclass _ p₀.2 hM
      have hcN := classWorlds_none u
        (((tokCols u cols).filter (fun p => p.2.classKey = φ)).map Prod.fst) p₀.2
      refine ⟨fun w hw hg p hp hpL => ?_, ?_⟩
      · obtain ⟨⟨w₁, w₂⟩, hw12, rfl⟩ := Multiset.mem_map.mp hw
        obtain ⟨h1, h2⟩ := Multiset.mem_product.mp hw12
        obtain ⟨g1, g2⟩ := (hcomb w₁ w₂).mp hg
        show (w₁.2.2 p.1).or (w₂.2.2 p.1) = _
        by_cases hpM : p.1 ∈ ((tokCols u cols).filter (fun p => p.2.classKey = φ)).map Prod.fst
        · rw [hcA w₁ h1 g1 p.1 hpM]
          rfl
        · rw [hcN w₁ h1 p.1 hpM, Option.none_or]
          refine ihA w₂ h2 g2 p hp ?_
          rcases List.mem_cons.mp hpL with h | h
          · exact absurd (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simpa using h⟩,
              rfl⟩) hpM
          · exact h
      · obtain ⟨w₁, h1, g1⟩ := hcE
        obtain ⟨w₂, h2, g2⟩ := ihE
        exact ⟨combineW w₁ w₂, Multiset.mem_map.mpr
          ⟨(w₁, w₂), Multiset.mem_product.mpr ⟨h1, h2⟩, rfl⟩, (hcomb w₁ w₂).mpr ⟨g1, g2⟩⟩

omit [HasAltLinearOrder K] in
/-- **The joint reading absorbs a grouped guard** its compared values all
carry, as soon as one of its compared columns holds a value: every world
it is read in meets that value's group. -/
theorem GenPredIn.predsemJ_delta_absorb (φ : GenPredIn T c κ) (neg : Bool) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) (ℓ₀ : List K)
    (hex : ∃ k ∈ φ.comparedCols, ∃ x, u k = Sum.inr x)
    (huni : ∀ k ∈ φ.comparedCols, ∀ x : AggTok T K,
      u k = Sum.inr x → x.scalar = false ∧ x.annList = ℓ₀) :
    φ.predsemJ neg u γ * SemiringWithMonus.delta ℓ₀.sum = φ.predsemJ neg u γ := by
  unfold GenPredIn.predsemJ
  rw [← Multiset.sum_map_mul_right]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun w hw => ?_))
  have hw' := jointWorlds_absorb u _ ℓ₀
    (by
      obtain ⟨k, hk, x, hx⟩ := hex
      exact ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, by simpa using hk⟩, x, hx⟩)
    (fun k hk x hx => huni k (by simpa using (List.mem_filter.mp hk).2) x hx) w hw
  rw [mul_right_comm, mul_right_comm w.1, hw']

omit [HasAltLinearOrder K] in
/-- **Selection finalize identity.** On each side separately, the
annotation produced by an aggregate-atom selection finalizes to the
predicate provenance times the input's finalized annotation: kept pending
factors commute out, and each superseded factor is absorbed by the
predicate provenance, every world it is read in meeting the superseded
group. The compared-lists multiset `C` is abstract; what is used is that
every compared token's occurrence list belongs to it and that each of its
lists comes from a compared token. -/
theorem GenAnn.finalize_sel (φ : GenPredIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) (b : K) (P : Multiset (List K))
    (C Cs : Multiset (List K))
    (hC : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.annList ∈ C)
    (hCs : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.scalar = true → a.annList ∈ Cs)
    (hCex : ∀ l ∈ C, ∃ k ∈ φ.comparedCols, ∃ a : AggTok T K, u k = Sum.inr a) :
    GenAnn.finalize ⟨b * φ.predsemJ false u γ,
      if φ.entailsExistence false then
        P.filter (fun l => ¬(Cs = 0 ∧ C ≠ 0 ∧ ∀ l' ∈ C, l' = l))
      else P⟩
      = φ.predsemJ false u γ * GenAnn.finalize ⟨b, P⟩ := by
  by_cases hent : φ.entailsExistence false = true
  · rw [ite_eq_left hent]
    show b * φ.predsemJ false u γ * _ = φ.predsemJ false u γ * (b * _)
    set dropCond := fun l : List K => (Cs = 0 ∧ C ≠ 0 ∧ ∀ l' ∈ C, l' = l)
      with hdrop
    have habs : φ.predsemJ false u γ
        * ((P.filter dropCond).map
            (fun l => SemiringWithMonus.delta l.sum)).prod
        = φ.predsemJ false u γ := by
      induction P using Multiset.induction_on with
      | empty => rw [Multiset.filter_zero, Multiset.map_zero, Multiset.prod_zero, mul_one]
      | cons l P ih =>
        by_cases hl : dropCond l
        · rw [Multiset.filter_cons_of_pos _ hl, Multiset.map_cons, Multiset.prod_cons,
            ← mul_assoc]
          obtain ⟨hCs0, hC0, hall⟩ := hl
          obtain ⟨l₁, hl₁⟩ := Multiset.exists_mem_of_ne_zero hC0
          rw [GenPredIn.predsemJ_delta_absorb φ false u l (hCex l₁ hl₁)
            (fun k hk a hka => ⟨?_, hall _ (hC k hk a hka)⟩), ih]
          by_contra hsc
          rw [Bool.not_eq_false] at hsc
          have := hCs k hk a hka hsc
          rw [hCs0] at this
          exact absurd this (Multiset.notMem_zero _)
        · rw [Multiset.filter_cons_of_neg _ hl, ih]
    calc b * φ.predsemJ false u γ
          * ((P.filter (fun l => ¬ dropCond l)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod
        = b * (φ.predsemJ false u γ
            * (((P.filter (fun l => ¬ dropCond l)).map
                (fun l => SemiringWithMonus.delta l.sum)).prod
              * ((P.filter dropCond).map
                (fun l => SemiringWithMonus.delta l.sum)).prod)) := by
          rw [mul_comm (((P.filter (fun l => ¬ dropCond l)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod),
            ← mul_assoc (φ.predsemJ false u γ), habs, mul_assoc]
      _ = b * (φ.predsemJ false u γ
            * ((P.filter (fun l => ¬ dropCond l) + P.filter dropCond).map
                (fun l => SemiringWithMonus.delta l.sum)).prod) := by
          rw [Multiset.map_add, Multiset.prod_add]
      _ = φ.predsemJ false u γ
            * (b * (P.map (fun l => SemiringWithMonus.delta l.sum)).prod) := by
          have hsplit : P.filter (fun l => ¬ dropCond l) + P.filter dropCond
              = P := by
            rw [add_comm]
            exact Multiset.filter_add_not _ P
          rw [hsplit, mul_left_comm]
  · rw [ite_eq_right hent]
    show b * φ.predsemJ false u γ * _ = φ.predsemJ false u γ * (b * _)
    rw [mul_right_comm]
    exact mul_comm _ _

end GuardAbsorption
