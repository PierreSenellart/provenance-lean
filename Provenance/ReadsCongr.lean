/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQuerySubst

/-!
# An evaluation reads its context only where it says it does

`AggQueryIn.readsOuter` lists the context positions a query reads. This
file proves that the annotated evaluation depends on the context – the
valuation `γ` of the parameters and the environment's context of general
values – only at those positions, provided every operator building
aggregate values records the positions its subtree reads
(`AggQueryIn.readsRecorded`), which is what it stamps its values with
(`AggQueryIn.evaluate_congr_reads`).

This is what makes an operator's values a function of their family
identifier: two evaluations of one operator under contexts that agree on
the parameters it records build the same values.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-- Two valuations agree on the positions a read set holds. -/
def AgreeOn {c : ℕ} {α : Type} (r : Fin c → Bool) (γ γ' : Fin c → α) : Prop :=
  ∀ k, r k = true → γ k = γ' k

omit [ValueType T] in
theorem TermIn.eval_congr_reads {c n : ℕ} [ValueType T] (t : TermIn T c n) (u : Tuple T n)
    {γ γ' : Fin c → T} (h : ∀ k, t.readsOuter k = true → γ k = γ' k) :
    t.eval u γ = t.eval u γ' := by
  induction t with
  | const a => rfl
  | outer j => exact h j (by simp [TermIn.readsOuter])
  | index j => rfl
  | add t₁ t₂ ih₁ ih₂ | sub t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ | coalesce t₁ t₂ ih₁ ih₂ =>
    simp only [TermIn.eval]
    rw [ih₁ (fun k hk => h k (by simp [TermIn.readsOuter, hk])),
      ih₂ (fun k hk => h k (by simp [TermIn.readsOuter, hk]))]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    simp only [TermIn.eval]
    rw [ih₁ (fun k hk => h k (by simp [TermIn.readsOuter, hk])),
      ih₂ (fun k hk => h k (by simp [TermIn.readsOuter, hk])),
      ih₃ (fun k hk => h k (by simp [TermIn.readsOuter, hk])),
      ih₄ (fun k hk => h k (by simp [TermIn.readsOuter, hk]))]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem TermGIn.eval_congr_reads {c n : ℕ} {κ : Fin n → ColKind} (t : TermGIn T c κ)
    (u : Tuple (GenValue T K) n) {γ γ' : Fin c → T}
    (h : ∀ k, t.readsOuter k = true → γ k = γ' k) :
    t.eval u γ = t.eval u γ' := by
  induction t with
  | const a => rfl
  | outer j => exact h j (by simp [TermGIn.readsOuter])
  | index j _ => rfl
  | provIndex j _ => rfl
  | cmpAgg _ _ _ _ _ => rfl
  | chiGate _ _ _ _ _ => rfl
  | add t₁ t₂ ih₁ ih₂ | sub t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ | coalesce t₁ t₂ ih₁ ih₂ =>
    simp only [TermGIn.eval]
    rw [ih₁ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₂ (fun k hk => h k (by simp [TermGIn.readsOuter, hk]))]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    simp only [TermGIn.eval]
    rw [ih₁ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₂ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₃ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₄ (fun k hk => h k (by simp [TermGIn.readsOuter, hk]))]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem TermGIn.evalPlain_congr_reads {c n : ℕ} {κ : Fin n → ColKind} (t : TermGIn T c κ)
    (u : Tuple T n) {γ γ' : Fin c → T}
    (h : ∀ k, t.readsOuter k = true → γ k = γ' k) :
    t.evalPlain u γ = t.evalPlain u γ' := by
  induction t with
  | const a => rfl
  | outer j => exact h j (by simp [TermGIn.readsOuter])
  | index j _ => rfl
  | provIndex j _ => rfl
  | cmpAgg _ _ _ _ _ => rfl
  | chiGate _ _ _ _ _ => rfl
  | add t₁ t₂ ih₁ ih₂ | sub t₁ t₂ ih₁ ih₂ | mul t₁ t₂ ih₁ ih₂ | coalesce t₁ t₂ ih₁ ih₂ =>
    simp only [TermGIn.evalPlain]
    rw [ih₁ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₂ (fun k hk => h k (by simp [TermGIn.readsOuter, hk]))]
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    simp only [TermGIn.evalPlain]
    rw [ih₁ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₂ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₃ (fun k hk => h k (by simp [TermGIn.readsOuter, hk])),
      ih₄ (fun k hk => h k (by simp [TermGIn.readsOuter, hk]))]

omit [DecidableEq K] [HasAltLinearOrder K] [CommSemiringWithMonus K] in
theorem GenPredIn.eval3_congr_reads {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    (u : Tuple (GenValue T K) n) {γ γ' : Fin c → T}
    (h : ∀ k, φ.readsOuter k = true → γ k = γ' k) :
    φ.eval3 u γ = φ.eval3 u γ' := by
  induction φ with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.eval3]
    rw [t₁.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk])),
      t₂.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | aggCmp j hj op t =>
    simp only [GenPredIn.eval3]
    rw [t.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | aggRange j hj op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.eval3]
    rw [t₁.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk])),
      t₂.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.eval3]
    rw [ihφ (fun k hk => h k (by simp [GenPredIn.readsOuter, hk])),
      ihψ (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | not φ ih =>
    simp only [GenPredIn.eval3]
    rw [ih (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]

omit [DecidableEq K] [HasAltLinearOrder K] [CommSemiringWithMonus K] in
theorem GenPredIn.eval3W_congr_reads {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    (v : Fin n → Option T) (u : Tuple (GenValue T K) n) {γ γ' : Fin c → T}
    (h : ∀ k, φ.readsOuter k = true → γ k = γ' k) :
    φ.eval3W v u γ = φ.eval3W v u γ' := by
  induction φ with
  | cmp op t₁ t₂ =>
    simp only [GenPredIn.eval3W]
    rw [t₁.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk])),
      t₂.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | aggCmp j hj op t =>
    simp only [GenPredIn.eval3W]
    rw [t.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | aggRange j hj op₁ t₁ op₂ t₂ =>
    simp only [GenPredIn.eval3W]
    rw [t₁.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk])),
      t₂.eval_congr_reads u (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [GenPredIn.eval3W]
    rw [ihφ (fun k hk => h k (by simp [GenPredIn.readsOuter, hk])),
      ihψ (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]
  | not φ ih =>
    simp only [GenPredIn.eval3W]
    rw [ih (fun k hk => h k (by simp [GenPredIn.readsOuter, hk]))]

omit [HasAltLinearOrder K] in
theorem GenPredIn.predsemJ_congr_reads {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    (neg : Bool) (u : Tuple (GenValue T K) n) {γ γ' : Fin c → T}
    (h : ∀ k, φ.readsOuter k = true → γ k = γ' k) :
    φ.predsemJ neg u γ = φ.predsemJ neg u γ' := by
  unfold GenPredIn.predsemJ
  simp only [φ.eval3W_congr_reads _ u h]

omit [DecidableEq K] [HasAltLinearOrder K] [CommSemiringWithMonus K] in
theorem ProjColIn.eval_congr_reads {c n : ℕ} {κ : Fin n → ColKind} (p : ProjColIn T c κ)
    (u : Tuple (GenValue T K) n) {γ γ' : Fin c → T}
    (h : ∀ k, p.readsOuter k = true → γ k = γ' k) :
    p.eval u γ = p.eval u γ' := by
  cases p with
  | term t => simp only [ProjColIn.eval]; rw [t.eval_congr_reads u h]
  | provTerm t => simp only [ProjColIn.eval]; rw [t.eval_congr_reads u h]
  | token _ _ => rfl
  | aggTerm _ _ _ => rfl
  | aggTermOf _ _ _ => rfl

/-! ## The values an operator builds read the parameters only through its terms -/

section Builders

variable {c m : ℕ} {γ γ' : Fin c → T}

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggValue.ofGroup_congr_γ (f : SeqAggFunc T) (t : TermIn T c m)
    (U : List (AnnotatedTuple T K m)) (h : ∀ r, t.eval r γ = t.eval r γ') :
    AggValue.ofGroup f t U γ = AggValue.ofGroup f t U γ' := by
  simp only [AggValue.ofGroup, h]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggValue.ofScalarGroup_congr_γ (f : SeqAggFunc T) (t : TermIn T c m)
    (U : List (AnnotatedTuple T K m)) (h : ∀ r, t.eval r γ = t.eval r γ') :
    AggValue.ofScalarGroup f t U γ = AggValue.ofScalarGroup f t U γ' := by
  simp only [AggValue.ofScalarGroup, AggValue.ofGroup, h]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem AggExpr.ofSeqWhen_congr_γ (f : SeqAggFunc T) (t : TermIn T c m)
    (keep : Tuple T m → Bool) (U : List (AnnotatedTuple T K m)) (sc : Bool)
    (h : ∀ r, t.eval r γ = t.eval r γ') :
    AggExpr.ofSeqWhen f t keep U sc γ = AggExpr.ofSeqWhen f t keep U sc γ' := by
  simp only [AggExpr.ofSeqWhen, h]

omit [DecidableEq K] [HasAltLinearOrder K] in
theorem AggExpr.ofSeqDistWhen_congr_γ (f : SeqAggFunc T) (t : TermIn T c m)
    (keep : Tuple T m → Bool) (U : List (AnnotatedTuple T K m)) (sc : Bool)
    (h : ∀ r, t.eval r γ = t.eval r γ') :
    AggExpr.ofSeqDistWhen f t keep U sc γ = AggExpr.ofSeqDistWhen f t keep U sc γ' := by
  simp only [AggExpr.ofSeqDistWhen, h]

omit [DecidableEq K] in
theorem ValueFrame.tokenOfDist_congr_γ {n p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n)
    (h : ∀ r, t.eval r γ = t.eval r γ') :
    ValueFrame.tokenOfDist P O o w t f dist X x γ
      = ValueFrame.tokenOfDist P O o w t f dist X x γ' := by
  unfold ValueFrame.tokenOfDist ValueFrame.tokenOf
  rw [AggValue.ofGroup_congr_γ f t _ h, AggValue.ofScalarGroup_congr_γ f t _ h]

omit [DecidableEq K] in
theorem ValueFrame.exprWhenOf_congr_γ {n p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (dist : Bool)
    (keep : Tuple T n → Bool) (X : AnnotatedRelation T K n) (x : AnnotatedTuple T K n)
    (h : ∀ r, t.eval r γ = t.eval r γ') :
    ValueFrame.exprWhenOf P O o w t f dist keep X x γ
      = ValueFrame.exprWhenOf P O o w t f dist keep X x γ' := by
  unfold ValueFrame.exprWhenOf
  rw [AggExpr.ofSeqWhen_congr_γ f t keep _ _ h, AggExpr.ofSeqDistWhen_congr_γ f t keep _ _ h]

omit [CommSemiringWithMonus K] [DecidableEq K] in
theorem ValueFrame.exprOfWhen_congr_γ {n p q : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (ws : Fin q → ValueFrame T p) (ts : Fin q → TermIn T c n)
    (fs : Fin q → SeqAggFunc T) (g : (Fin q → T) → T) (keeps : Fin q → Option (Selection T n))
    (r : OccFam (AnnotatedTuple T K n)) (i : Fin r.size)
    (h : ∀ l r, (ts l).eval r γ = (ts l).eval r γ') :
    ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ
      = ValueFrame.exprOfWhen P O o ws ts fs g keeps r i γ' := by
  simp only [ValueFrame.exprOfWhen, h]

omit [DecidableEq K] in
theorem ValueFrame.windowGenRow_congr_γ {n p : ℕ} (lab : ℕ) (ck : List (T ⊕ FamId T))
    (κ : Fin n → ColKind) (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T) (keep : Option (Selection T n))
    (X : AnnotatedRelation T K n) (x : GenRow T K n) (dist : Bool)
    (h : ∀ r, t.eval r γ = t.eval r γ') :
    ValueFrame.windowGenRow lab ck κ P O o w t f keep X x γ dist
      = ValueFrame.windowGenRow lab ck κ P O o w t f keep X x γ' dist := by
  unfold ValueFrame.windowGenRow
  cases keep with
  | none => rw [ValueFrame.tokenOfDist_congr_γ P O o w t f dist X _ h]
  | some φ => simp only [ValueFrame.exprWhenOf_congr_γ P O o w t f dist _ X _ h]

end Builders

/-! ## The congruence -/

omit [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [CommSemiringWithMonus K] in
/-- The parameters a read set records, read off two contexts agreeing
there. -/
theorem EvalEnv.paramKey_congr_reads {c : ℕ} (rd : Fin c → Bool) {γ γ' : Fin c → T}
    {E E' : EvalEnv T K} (h : AgreeOn rd (E.ctxAt c γ) (E'.ctxAt c γ')) :
    E.paramKey rd γ = E'.paramKey rd γ' := by
  unfold EvalEnv.paramKey ctxKey
  refine List.filterMap_congr (fun k _ => ?_)
  by_cases hk : rd k = true
  · simp only [hk, ite_true, h k hk]
  · simp only [hk, Bool.false_eq_true, ite_false]

/-- **An evaluation reads its context only where it says it does.** Two
valuations of the parameters and two environment contexts that agree on
the positions the query reads, with the same rounds bound to the names it
reads, give the same
evaluation – provided the operators building aggregate values record the
positions their subtrees read, which is what they stamp. -/
theorem AggQueryIn.evaluate_congr_reads :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.readsRecorded → ∀ (d : AnnotatedDatabase T K) {γ γ' : Fin c → T} {E E' : EvalEnv T K},
      (∀ p ∈ l, E.holes p.1 p.2 = E'.holes p.1 p.2) → AgreeOn q.readsOuter γ γ' →
      AgreeOn q.readsOuter (E.ctxAt c γ) (E'.ctxAt c γ') →
      q.evaluate d γ E = q.evaluate d γ' E' := by
  intro c n κ l q
  induction q with
  | Rel n s => intro _ d γ γ' E E' _ _ _; rfl
  | Hole n s κ =>
    intro _ d γ γ' E E' hh _ _
    simp only [AggQueryIn.evaluate, hh (s, n) (List.mem_singleton_self _)]
  | Param pv ρ =>
    intro _ d γ γ' E E' _ _ hc
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows]
    have hu : (fun k => _root_.Sum.elim Sum.inl (E.ctxAt _ γ) (pv k))
        = (fun k => _root_.Sum.elim Sum.inl (E'.ctxAt _ γ') (pv k)) := by
      funext k
      cases hp : pv k with
      | inl a => rfl
      | inr j =>
        exact hc j (by
          simp only [AggQueryIn.readsOuter, List.any_eq_true, List.mem_finRange, true_and]
          exact ⟨k, by rw [hp]; simp⟩)
    rw [hu]
  | Empty => intro _ d γ γ' E E' _ _ _; rfl
  | Proj ps q ih =>
    intro hrr d γ γ' E E' hh hg hc
    have hp : ∀ j (r : Tuple (GenValue T K) _), (ps j).eval r γ = (ps j).eval r γ' := fun j r =>
      (ps j).eval_congr_reads r (fun k hk => hg k (by
        simp only [AggQueryIn.readsOuter, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
          true_and]
        exact Or.inl ⟨j, hk⟩))
    simp only [AggQueryIn.evaluate, ih hrr d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
        hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk])), hp]
  | Sel φ q hφ ih =>
    intro hrr d γ γ' E E' hh hg hc
    have hφg : ∀ k, φ.readsOuter k = true → γ k = γ' k :=
      fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk])
    have hholds : ∀ u : Tuple (GenValue T K) _, φ.holds u γ = φ.holds u γ' := fun u => by
      unfold GenPredIn.holds; rw [φ.eval3_congr_reads u hφg]
    simp only [AggQueryIn.evaluate, ih hrr d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
        hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk])), hholds,
      φ.predsemJ_congr_reads _ _ hφg]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih₁ hrr.1 d (fun p hp => hh p (List.mem_append_left _ hp))
        (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k
            (by simp [AggQueryIn.readsOuter, hk])), ih₂ hrr.2 d (fun p hp => hh p
                (List.mem_append_right _ hp)) (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
                    hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk]))]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih₁ hrr.1 d (fun p hp => hh p (List.mem_append_left _ hp))
        (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k
            (by simp [AggQueryIn.readsOuter, hk])), ih₂ hrr.2 d (fun p hp => hh p
                (List.mem_append_right _ hp)) (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
                    hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk]))]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih₁ hrr.1 d hh (fun k hk => hg k
        (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter,
            hk])), ih₂ hrr.2 d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk]))
                (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk]))]
  | Dedup q ih =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih hrr d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
        hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk]))]
  | Explode k h q ih =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih hrr d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
        hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk]))]
  | Retag h q ih =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih hrr d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
        hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk]))]
  | @Apply cI n₁ n₂ κ₁ κ₂ l₁ q₁ q₂ ih₁ ih₂ =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih₁ hrr.1 d hh (fun k hk => hg k
        (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter,
            hk]))]
    refine Multiset.bind_congr (fun x _ => ?_)
    rw [ih₂ hrr.2 d (E := E.withCtx (Fin.append x.fst (E.ctxAt _ γ)))
      (E' := E'.withCtx (Fin.append x.fst (E'.ctxAt _ γ'))) (fun _ hp => absurd hp List.not_mem_nil)
      (fun k hk => ?_) (fun k hk => ?_)]
    · revert hk
      refine Fin.addCases (fun i _ => ?_) (fun j hj => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        exact hg j (by simp [AggQueryIn.readsOuter, hj])
    · rw [EvalEnv.ctxAt_withCtx, EvalEnv.ctxAt_withCtx]
      revert hk
      refine Fin.addCases (fun i _ => ?_) (fun j hj => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        exact hc j (by simp [AggQueryIn.readsOuter, hj])
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih₀ hrr.1 d (fun _ hp => absurd hp List.not_mem_nil)
        (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k
            (by simp [AggQueryIn.readsOuter, hk]))]
    exact muSumFix_congr (fun X => ih₁ hrr.2 d (E := E.assignHole s X) (E' := E'.assignHole s X)
      (fun p hp => by
        obtain rfl := List.mem_singleton.mp hp
        simp [EvalEnv.assignHole]) (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk]))
      (fun k hk => by
        rw [EvalEnv.ctxAt_assignHole, EvalEnv.ctxAt_assignHole]
        exact hc k (by simp [AggQueryIn.readsOuter, hk]))) rfl
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hrr d γ γ' E E' hh hg hc
    simp only [AggQueryIn.evaluate, ih₀ hrr.1 d (fun _ hp => absurd hp List.not_mem_nil)
        (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k
            (by simp [AggQueryIn.readsOuter, hk]))]
    refine congrArg _ (muFix_congr (fun X => ?_))
    rw [ih₁ hrr.2 d (E := E.assignHole s (X.map GenRow.ofAnnotated))
      (E' := E'.assignHole s (X.map GenRow.ofAnnotated))
      (fun p hp => by
        obtain rfl := List.mem_singleton.mp hp
        simp [EvalEnv.assignHole]) (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk]))
      (fun k hk => by
        rw [EvalEnv.ctxAt_assignHole, EvalEnv.ctxAt_assignHole]
        exact hc k (by simp [AggQueryIn.readsOuter, hk]))]
  | @Gamma cI mI nI₁ nI₂ lab rd is ts fs q keep ord ih =>
    intro hrr d γ γ' E E' hh hg hc
    have hts : ∀ j (r : Tuple T _), (ts j).eval r γ = (ts j).eval r γ' := fun j r =>
      (ts j).eval_congr_reads r (fun k hk => hg k (by
        simp only [AggQueryIn.readsOuter, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
          true_and]
        exact Or.inl (Or.inl ⟨j, hk⟩)))
    have hpk : E.paramKey rd γ = E'.paramKey rd γ' :=
      EvalEnv.paramKey_congr_reads rd (by rw [hrr.1]; exact hc)
    simp only [AggQueryIn.evaluate, ih hrr.2 d hh (fun k hk => hg k
        (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter,
            hk])), hpk, AggValue.ofGroup,
      AggExpr.ofGroupWhen, AggExpr.ofSeqWhen, hts]
  | @GammaScalar cI mI nI₂ lab rd ts fs q ord ih =>
    intro hrr d γ γ' E E' hh hg hc
    have hts : ∀ j (r : Tuple T _), (ts j).eval r γ = (ts j).eval r γ' := fun j r =>
      (ts j).eval_congr_reads r (fun k hk => hg k (by
        simp only [AggQueryIn.readsOuter, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
          true_and]
        exact Or.inl (Or.inl ⟨j, hk⟩)))
    have hpk : E.paramKey rd γ = E'.paramKey rd γ' :=
      EvalEnv.paramKey_congr_reads rd (by rw [hrr.1]; exact hc)
    simp only [AggQueryIn.evaluate, ih hrr.2 d hh (fun k hk => hg k
        (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter,
            hk])), hpk, AggValue.ofScalarGroup,
      AggValue.ofGroup, hts]
  | @GammaTok cI mI nI₁ nI₂ κ' lab rd is his ts fs a q keep ih =>
    intro hrr d γ γ' E E' hh hg hc
    have hts : ∀ j (r : Tuple T _), (ts j).eval r γ = (ts j).eval r γ' := fun j r =>
      (ts j).eval_congr_reads r (fun k hk => hg k (by
        simp only [AggQueryIn.readsOuter, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
          true_and]
        exact Or.inl (Or.inl (Or.inl ⟨j, hk⟩))))
    have hpk : E.paramKey rd γ = E'.paramKey rd γ' :=
      EvalEnv.paramKey_congr_reads rd (by rw [hrr.1]; exact hc)
    have ha : ∀ r : Tuple T _, a.evalPlain r γ = a.evalPlain r γ' := fun r =>
      a.evalPlain_congr_reads r (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk]))
    simp only [AggQueryIn.evaluate, ih hrr.2 d hh (fun k hk => hg k
        (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter,
            hk])), hpk, AggValue.ofGroup,
      AggExpr.ofGroupWhen, AggExpr.ofSeqWhen, hts, ha]
  | @ProvSum cI m n₁ κ' is his t q ih =>
    intro hrr d γ γ' E E' hh hg hc
    have ht : ∀ r : Tuple T _, t.evalPlain r γ = t.evalPlain r γ' := fun r =>
      t.evalPlain_congr_reads r (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk]))
    simp only [AggQueryIn.evaluate, ih hrr d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter,
        hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter, hk])), ht]
  | @GammaNest cI mI nI₁ κ' lab rd is his p f q ih =>
    intro hrr d γ γ' E E' hh hg hc
    have hp : ∀ r : Tuple (GenValue T K) _, p.eval r γ = p.eval r γ' := fun r =>
      p.eval_congr_reads r (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk]))
    have hpk : E.paramKey rd γ = E'.paramKey rd γ' :=
      EvalEnv.paramKey_congr_reads rd (by rw [hrr.1]; exact hc)
    simp only [AggQueryIn.evaluate, ih hrr.2 d hh (fun k hk => hg k
        (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter,
            hk])), hpk, nestOfGroup, hp]
  | @Win cI nI mI pI κw lab rd P O o w _ t f q hrr' dist keep ih =>
    intro hrr d γ γ' E E' hh hg hc
    have ht : ∀ r : Tuple T _, t.eval r γ = t.eval r γ' := fun r =>
      t.eval_congr_reads r (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk]))
    have hpk : E.paramKey rd γ = E'.paramKey rd γ' :=
      EvalEnv.paramKey_congr_reads rd (by rw [hrr.1]; exact hc)
    simp only [AggQueryIn.evaluate, ih hrr.2 d hh (fun k hk => hg k
        (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k (by simp [AggQueryIn.readsOuter,
            hk])), hpk,
      ValueFrame.windowGenRow_congr_γ _ _ _ P O o w t f _ _ _ dist ht]
  | @WinExpr cI nI mI pI qI lab rd P O o ws _ ts fs g q keeps ih =>
    intro hrr d γ γ' E E' hh hg hc
    have hts : ∀ j (r : Tuple T _), (ts j).eval r γ = (ts j).eval r γ' := fun j r =>
      (ts j).eval_congr_reads r (fun k hk => hg k (by
        simp only [AggQueryIn.readsOuter, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
          true_and]
        exact Or.inl (Or.inl ⟨j, hk⟩)))
    have hpk : E.paramKey rd γ = E'.paramKey rd γ' :=
      EvalEnv.paramKey_congr_reads rd (by rw [hrr.1]; exact hc)
    simp only [AggQueryIn.evaluate]
    rw [ih hrr.2 d hh (fun k hk => hg k (by simp [AggQueryIn.readsOuter, hk])) (fun k hk => hc k
        (by simp [AggQueryIn.readsOuter, hk])), hpk]
    simp only [ValueFrame.exprOfWhen_congr_γ P O o ws ts fs g keeps _ _ hts]
