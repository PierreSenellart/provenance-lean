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
  AggQueryIn.Sel (GenPredIn.fusedCmp op l s) (AggQueryIn.Gamma is ts fs qg)

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
        (fun j => AggTok.tok (AggValue.ofGroup (fs j) (ts j)
          (Having.havingGroup is A kv.fst)))).trans
      (congrArg (Fin.append kv.fst)
        (funext fun j => AggValue.collapse_ofGroup (fs j) (ts j) _))
  · -- annotation: the predicate provenance of the comparison
    show GenAnn.finalize ⟨1 * _, _⟩ = _
    simp only [GenPredIn.fusedCmp, GenPredIn.predsem, GenPredIn.comparedCols,
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
      AggTok.predProvOf, AggTok.predProvOfWith, AggTok.scalar,
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
          (⟨r.fst, ⟨r.snd.base * φ.predsem false r.fst γ, r.snd.pending⟩⟩
            : GenRow T K n)) := by
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_left hagg]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  obtain ⟨k₁, hk₁, k₂, hk₂, a₁, a₂, he₁, he₂, hne⟩ := htwo r hr
  refine congrArg
    (fun p => (⟨r.fst, ⟨r.snd.base * φ.predsem false r.fst γ, p⟩⟩
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
              (GenPredIn.aggCmp k₂ h₂ op₂ t₂)).predsem false r.fst γ,
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
      * (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsem false r.fst γ, _⟩ = 0
    rw [show (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsem false r.fst γ
        = Having.chi op (t₁.eval r.fst γ) (t₂.eval r.fst γ)
          * ψ.predsem false r.fst γ from rfl, hchi, zero_mul, mul_zero]
    unfold GenAnn.finalize
    exact zero_mul _
  · intro r hr hp
    have hchi : Having.chi (K := K) op (t₁.eval r.fst γ) (t₂.eval r.fst γ)
        = 1 := ite_eq_left hp
    refine Prod.ext rfl ?_
    show GenAnn.finalize ⟨r.snd.base * ψ.predsem false r.fst γ, _⟩
      = GenAnn.finalize ⟨r.snd.base
        * (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsem false r.fst γ, _⟩
    rw [show (GenPredIn.and (GenPredIn.cmp op t₁ t₂) ψ).predsem false r.fst γ
        = Having.chi op (t₁.eval r.fst γ) (t₂.eval r.fst γ)
          * ψ.predsem false r.fst γ from rfl, hchi, one_mul]
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
/-- **Selection finalize identity.** On each side separately, the
annotation produced by an aggregate-atom selection finalizes to the
predicate provenance times the input's finalized annotation: kept pending
factors commute out, and each superseded factor is absorbed by the
predicate provenance, its drop condition being exactly the absorption
license. The compared-lists multiset `C` is abstract; the only fact used
is that every compared token's occurrence list belongs to it. -/
theorem GenAnn.finalize_sel (φ : GenPredIn T c κ) {γ : Fin c → T}
    (u : Tuple (GenValue T K) n) (b : K) (P : Multiset (List K))
    (C Cs : Multiset (List K))
    (hC : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.annList ∈ C)
    (hCs : ∀ k ∈ φ.comparedCols, ∀ a : AggTok T K,
      u k = Sum.inr a → a.scalar = true → a.annList ∈ Cs) :
    GenAnn.finalize ⟨b * φ.predsem false u γ,
      if φ.entailsExistence false then
        P.filter (fun l => ¬(Cs = 0 ∧ C ≠ 0 ∧ ∀ l' ∈ C, l' = l))
      else P⟩
      = φ.predsem false u γ * GenAnn.finalize ⟨b, P⟩ := by
  by_cases hent : φ.entailsExistence false = true
  · rw [ite_eq_left hent]
    show b * φ.predsem false u γ * _ = φ.predsem false u γ * (b * _)
    set dropCond := fun l : List K => (Cs = 0 ∧ C ≠ 0 ∧ ∀ l' ∈ C, l' = l)
      with hdrop
    have habs : φ.predsem false u γ
        * ((P.filter dropCond).map
            (fun l => SemiringWithMonus.delta l.sum)).prod
        = φ.predsem false u γ := by
      refine GenPredIn.predsem_absorb_prod φ u hent _
        (fun l hl k hk a hka => ?_)
      have hcond := (Multiset.mem_filter.mp hl).2
      refine ⟨?_, hcond.2.2 a.annList (hC k hk a hka)⟩
      by_contra hsc
      rw [Bool.not_eq_false] at hsc
      have := hCs k hk a hka hsc
      rw [hcond.1] at this
      exact absurd this (Multiset.notMem_zero _)
    calc b * φ.predsem false u γ
          * ((P.filter (fun l => ¬ dropCond l)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod
        = b * (φ.predsem false u γ
            * (((P.filter (fun l => ¬ dropCond l)).map
                (fun l => SemiringWithMonus.delta l.sum)).prod
              * ((P.filter dropCond).map
                (fun l => SemiringWithMonus.delta l.sum)).prod)) := by
          rw [mul_comm (((P.filter (fun l => ¬ dropCond l)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod),
            ← mul_assoc (φ.predsem false u γ), habs, mul_assoc]
      _ = b * (φ.predsem false u γ
            * ((P.filter (fun l => ¬ dropCond l) + P.filter dropCond).map
                (fun l => SemiringWithMonus.delta l.sum)).prod) := by
          rw [Multiset.map_add, Multiset.prod_add]
      _ = φ.predsem false u γ
            * (b * (P.map (fun l => SemiringWithMonus.delta l.sum)).prod) := by
          have hsplit : P.filter (fun l => ¬ dropCond l) + P.filter dropCond
              = P := by
            rw [add_comm]
            exact Multiset.filter_add_not _ P
          rw [hsplit, mul_left_comm]
  · rw [ite_eq_right hent]
    show b * φ.predsem false u γ * _ = φ.predsem false u γ * (b * _)
    rw [mul_right_comm]
    exact mul_comm _ _


end GuardAbsorption
