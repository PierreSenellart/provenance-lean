/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryRewriting

/-!
# Stripping the classical fragment to the classical syntax

The classical fragment `AggQueryIn.classical` of the general syntax maps
back, operator for operator, to the classical `Query` syntax of
`Provenance.Query`. `AggQueryIn.strip` is that map, and
`AggQueryIn.strip_bridge` says it is faithful: the general annotated
evaluator and the classical one agree on it. The rewriting correctness
of `Provenance.AggQueryRewritingValid` goes through this bridge and the
classical theorem `Query.rewriting_valid`.

The strips of terms, predicates and projection columns send an *outer*
column to the constant `𝟘`, which is what the valuation a closed query
reads gives it, so the agreement statements below hold as they stand.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## Stripping to the classical syntax

The classical fragment of the general syntax maps back to the classical
`Query` syntax; the correctness of the native rewriting is assembled
through this strip, the classical correctness theorem, and the
plain-semantics agreement of the two rewritten queries. -/

section Strip

/-- Strip a term over regular columns to a classical term (the
`provIndex` arm is unreachable on the classical fragment and mapped
harmlessly). -/
def TermGIn.strip {c n : ℕ} {κ : Fin n → ColKind} : TermGIn T c κ → Term T n
  | .const a => .const a
  | .index k _ => .index k
  | .provIndex k _ => .index k
  | .cmpAgg _ _ _ _ => .const 0
  | .chiGate _ _ _ => .const 0
  -- an outer column reads the valuation, which is the constant `𝟘` on a
  -- closed query – the only valuation the strip is stated against
  | .outer _ => .const 0
  | .add t₁ t₂ => .add t₁.strip t₂.strip
  | .sub t₁ t₂ => .sub t₁.strip t₂.strip
  | .mul t₁ t₂ => .mul t₁.strip t₂.strip
  | .caseWhen op t₁ t₂ t₃ t₄ =>
    .caseWhen op t₁.strip t₂.strip t₃.strip t₄.strip
  | .coalesce t₁ t₂ => .coalesce t₁.strip t₂.strip

/-- Plain evaluation factors through the strip. -/
theorem TermGIn.strip_eval {c n : ℕ} {κ : Fin n → ColKind} (t : TermGIn T c κ)
    (u : Tuple T n) : t.strip.eval u = t.evalPlain u := by
  induction t with
  | const a => rfl
  | outer k => rfl
  | index k h => rfl
  | provIndex k h => rfl
  | cmpAgg k h op c ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermGIn.strip, TermIn.eval, TermGIn.evalPlain, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => rw [TermGIn.strip, TermIn.eval, TermGIn.evalPlain, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => rw [TermGIn.strip, TermIn.eval, TermGIn.evalPlain, ih₁, ih₂]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    rw [TermGIn.strip, TermIn.eval, TermGIn.evalPlain, ih₁, ih₂, ih₃, ih₄]
  | coalesce t₁ t₂ ih₁ ih₂ =>
    rw [TermGIn.strip, TermIn.eval, TermGIn.evalPlain, ih₁, ih₂]

/-- Strip an aggregate-atom-free predicate to a classical selection. -/
def GenPredIn.strip {c n : ℕ} {κ : Fin n → ColKind} :
    GenPredIn T c κ → Selection T n
  | .cmp .eq t₁ t₂ => .BT (.EQ t₁.strip t₂.strip)
  | .cmp .ne t₁ t₂ => .BT (.NE t₁.strip t₂.strip)
  | .cmp .le t₁ t₂ => .BT (.LE t₁.strip t₂.strip)
  | .cmp .lt t₁ t₂ => .BT (.LT t₁.strip t₂.strip)
  | .cmp .ge t₁ t₂ => .BT (.GE t₁.strip t₂.strip)
  | .cmp .gt t₁ t₂ => .BT (.GT t₁.strip t₂.strip)
  | .cmp .syneq t₁ t₂ => .BT (.SYNEQ t₁.strip t₂.strip)
  | .cmp .synne t₁ t₂ => .BT (.SYNNE t₁.strip t₂.strip)
  | .aggCmp _ _ _ _ => .True
  | .aggRange _ _ _ _ _ _ => .True
  | .and φ ψ => .And φ.strip ψ.strip
  | .or φ ψ => .Or φ.strip ψ.strip
  | .not φ => .Not φ.strip

/-- Truth factors through the strip, on aggregate-atom-free predicates –
three-valuedly, both readings being Kleene's. -/
theorem GenPredIn.strip_eval3 {c n : ℕ} {κ : Fin n → ColKind} :
    ∀ (φ : GenPredIn T c κ), φ.hasAggAtom = false → ∀ (u : Tuple T n),
      φ.strip.eval3 u = φ.evalPlain3 u
  | .cmp op t₁ t₂, _, u => by
    cases op <;>
      (simp only [GenPredIn.strip, Selection.eval3, BoolTerm.eval3,
         BoolTerm.toCompOp, BoolTerm.args, TermGIn.strip_eval];
       rfl)
  | .aggCmp _ _ _ _, hφ, _ => Bool.noConfusion hφ
  | .and φ ψ, hφ, u => by
    show (Selection.eval3 _ _).and _ = _
    rw [strip_eval3 φ (Bool.or_eq_false_iff.mp hφ).1 u,
      strip_eval3 ψ (Bool.or_eq_false_iff.mp hφ).2 u]
    rfl
  | .or φ ψ, hφ, u => by
    show (Selection.eval3 _ _).or _ = _
    rw [strip_eval3 φ (Bool.or_eq_false_iff.mp hφ).1 u,
      strip_eval3 ψ (Bool.or_eq_false_iff.mp hφ).2 u]
    rfl
  | .not φ, hφ, u => by
    show (Selection.eval3 _ _).not = _
    rw [strip_eval3 φ hφ u]
    rfl

/-- Truth factors through the strip, on aggregate-atom-free predicates. -/
theorem GenPredIn.strip_eval {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (hφ : φ.hasAggAtom = false) (u : Tuple T n) :
    φ.strip.eval u ↔ φ.holdsPlain u := by
  unfold Selection.eval GenPredIn.holdsPlain
  rw [GenPredIn.strip_eval3 φ hφ u]

/-- Strip a regular projection column to a classical term. -/
def ProjColIn.strip {c n : ℕ} {κ : Fin n → ColKind} :
    ProjColIn T c κ → Term T n
  | .term t => t.strip
  | .token _ _ => .const 0
  | .aggTerm _ _ _ => .const 0
  | .provTerm t => t.strip

/-- Strip a classical-fragment query to the classical syntax. -/
def AggQueryIn.strip :
    {c n : ℕ} → {κ : Fin n → ColKind} → (q : AggQueryIn T c n κ) →
    q.classical → Query T n
  | _, n, _, .Rel _ s, _ => .Rel n s
  | _, _, _, .Proj ps q, hq =>
    .Proj (fun j => (ps j).strip) (q.strip hq.2)
  | _, _, _, .Sel φ q, hq => .Sel φ.strip (q.strip hq.2)
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ _ _ q₁ q₂, hq =>
    @Query.Prod T n₁ n₂ (n₁ + n₂) rfl (q₁.strip hq.1) (q₂.strip hq.2)
  | _, _, _, .Sum q₁ q₂, hq => .Sum (q₁.strip hq.1) (q₂.strip hq.2)
  | _, _, _, .Dedup q, hq => .Dedup (q.strip hq)
  | _, _, _, .Diff q₁ q₂, hq => .Diff (q₁.strip hq.1) (q₂.strip hq.2)
  | _, _, _, .Gamma _ _ _ _, hq => False.elim hq
  | _, _, _, .GammaScalar _ _ _, hq => False.elim hq
  | _, _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, _, .Retag _ _, hq => False.elim hq
  | _, _, _, .GammaTok _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .Win _ _ _ _ _ _ _, hq => False.elim hq
termination_by structural _ _ _ q _ => q

/-- The strip is aggregation-free. -/
theorem AggQueryIn.strip_source :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (hq : q.classical), (q.strip hq).source
  | _, _, _, .Rel _ _, _ => trivial
  | _, _, _, .Proj _ q, hq => strip_source q hq.2
  | _, _, _, .Sel _ q, hq => strip_source q hq.2
  | _, _, _, .Prod q₁ q₂, hq => ⟨strip_source q₁ hq.1, strip_source q₂ hq.2⟩
  | _, _, _, .Sum q₁ q₂, hq => ⟨strip_source q₁ hq.1, strip_source q₂ hq.2⟩
  | _, _, _, .Dedup q, hq => strip_source q hq
  | _, _, _, .Diff q₁ q₂, hq => ⟨strip_source q₁ hq.1, strip_source q₂ hq.2⟩
  | _, _, _, .Gamma _ _ _ _, hq => False.elim hq
  | _, _, _, .GammaScalar _ _ _, hq => False.elim hq
  | _, _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, _, .Retag _ _, hq => False.elim hq
  | _, _, _, .GammaTok _ _ _ _ _ _, hq => False.elim hq
  | _, _, _, .Win _ _ _ _ _ _ _, hq => False.elim hq

end Strip

/-! ## Faithfulness of the strip -/

section StripFaithful

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- The collapsed data part of an invariant row is its classical
counterpart's data part. -/
theorem GenRow.Inv.plainTuple_eq {n : ℕ} {r : GenRow T K n}
    {p : AnnotatedTuple T K n} (h : GenRow.Inv r p) :
    GenRow.plainTuple r.fst = p.fst :=
  congrArg Prod.fst h.toAnnotated_eq

/-- **Row-wise faithfulness of the strip**: on the classical fragment,
the general evaluator produces rows satisfying the embedding invariant
against the classical annotated evaluation of the stripped query. -/
theorem AggQueryIn.strip_rel :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ)
      (hq : q.classical) (d : AnnotatedDatabase T K),
      Multiset.Rel GenRow.Inv (q.evaluate d)
        ((q.strip hq).evaluateAnnotated (q.strip_source hq) d)
  | _, n, _, .Rel _ s, _, d => by
    show Multiset.Rel GenRow.Inv (match d.find n s with
      | none => (∅ : Multiset (GenRow T K n))
      | some rn => rn.map GenRow.ofAnnotated)
      ((Query.Rel n s).evaluateAnnotated trivial d)
    unfold Query.evaluateAnnotated
    cases d.find n s with
    | none => exact Multiset.Rel.zero
    | some rn => exact rel_inv_ofAnnotated rn
  | _, _, _, .Proj ps q, hq, d => by
    refine rel_map_of_rel (strip_rel q hq.2 d) (fun r p hr => ⟨?_, ?_, ?_⟩)
    · funext j
      show (ps j).eval r.fst = Sum.inl ((ps j).strip.eval p.fst)
      have hkind := hq.1 j
      cases hp : ps j with
      | term t =>
        show Sum.inl (t.eval r.fst) = Sum.inl (t.strip.eval p.fst)
        rw [TermGIn.strip_eval, TermGIn.eval_eq_evalPlain t r.fst,
          hr.plainTuple_eq]
      | token k hk => rw [hp] at hkind; exact ColKind.noConfusion hkind
      | aggTerm k hk gf => rw [hp] at hkind; exact ColKind.noConfusion hkind
      | provTerm t => rw [hp] at hkind; exact ColKind.noConfusion hkind
    · exact (GenAnn.finalize_cash _ _ _ Multiset.inter_le_left).trans hr.2.1
    · show r.snd.pending ∩ _ = 0
      rw [hr.2.2]
      exact Multiset.zero_inter _
  | _, _, _, .Sel φ q, hq, d => by
    show Multiset.Rel _
      (if φ.hasAggAtom then _ else
        Multiset.filter _ (q.evaluate d)) _
    rw [ite_eq_right (by rw [hq.1]; exact Bool.false_ne_true)]
    refine rel_filter_of_iff (strip_rel q hq.2 d) (fun r p hr => ?_)
    rw [GenPredIn.holds_iff_holdsPlain, hr.plainTuple_eq]
    exact (GenPredIn.strip_eval φ hq.1 p.fst).symm
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ _ _ q₁ q₂, hq, d => by
    refine rel_map_of_rel
      (rel_product (strip_rel q₁ hq.1 d) (strip_rel q₂ hq.2 d)) ?_
    rintro ⟨x, y⟩ ⟨p, p'⟩ ⟨hx, hy⟩
    refine ⟨?_, ?_, ?_⟩
    · funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · show Fin.append x.fst y.fst (Fin.castAdd n₂ i) = _
        rw [Fin.append_left, hx.1]
        show Sum.inl (p.fst i)
          = Sum.inl (Fin.append p.fst p'.fst (Fin.castAdd n₂ i))
        rw [Fin.append_left]
      · show Fin.append x.fst y.fst (Fin.natAdd n₁ j) = _
        rw [Fin.append_right, hy.1]
        show Sum.inl (p'.fst j)
          = Sum.inl (Fin.append p.fst p'.fst (Fin.natAdd n₁ j))
        rw [Fin.append_right]
    · show GenAnn.finalize ⟨x.snd.base * y.snd.base,
        x.snd.pending + y.snd.pending⟩ = p.snd * p'.snd
      rw [GenAnn.finalize_prod, hx.2.1, hy.2.1]
    · show x.snd.pending + y.snd.pending = 0
      rw [hx.2.2, hy.2.2]
      rfl
  | _, _, _, .Sum q₁ q₂, hq, d =>
    Multiset.Rel.add (strip_rel q₁ hq.1 d) (strip_rel q₂ hq.2 d)
  | _, _, _, .Dedup q, hq, d => by
    show Multiset.Rel _ ((Multiset.ofList (groupByKey
      ((q.evaluate d).map GenRow.toAnnotated)).val).map
        GenRow.ofAnnotated) _
    rw [show (q.evaluate d).map GenRow.toAnnotated
        = (q.strip hq).evaluateAnnotated (q.strip_source hq) d from
      (map_eq_of_rel (strip_rel q hq d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    exact rel_inv_ofAnnotated _
  | _, _, _, .Diff q₁ q₂, hq, d => by
    show Multiset.Rel _
      (((((q₁.evaluate d).map GenRow.toAnnotated)).map _).map
        GenRow.ofAnnotated) _
    rw [show (q₁.evaluate d).map GenRow.toAnnotated
        = (q₁.strip hq.1).evaluateAnnotated (q₁.strip_source hq.1) d from
      (map_eq_of_rel (strip_rel q₁ hq.1 d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [show (q₂.evaluate d).map GenRow.toAnnotated
        = (q₂.strip hq.2).evaluateAnnotated (q₂.strip_source hq.2) d from
      (map_eq_of_rel (strip_rel q₂ hq.2 d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [Multiset.map_map]
    refine rel_map_of_forall (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    exact ⟨rfl, GenAnn.finalize_of_pending_zero _, rfl⟩
  | _, _, _, .Gamma _ _ _ _, hq, _ => False.elim hq
  | _, _, _, .GammaScalar _ _ _, hq, _ => False.elim hq
  | _, _, _, .ProvSum _ _ _ _, hq, _ => False.elim hq
  | _, _, _, .Retag _ _, hq, _ => False.elim hq
  | _, _, _, .GammaTok _ _ _ _ _ _, hq, _ => False.elim hq
  | _, _, _, .Win _ _ _ _ _ _ _, hq, _ => False.elim hq

/-- **Faithfulness of the strip**: on the classical fragment the general
annotated evaluator computes the classical annotated semantics of the
stripped query. -/
theorem AggQueryIn.strip_bridge {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ) (hq : q.classical) (d : AnnotatedDatabase T K) :
    q.evaluateAnnotated d
      = (q.strip hq).evaluateAnnotated (q.strip_source hq) d := by
  unfold AggQueryIn.evaluateAnnotated
  exact (map_eq_of_rel (AggQueryIn.strip_rel q hq d)
    (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)

end StripFaithful
