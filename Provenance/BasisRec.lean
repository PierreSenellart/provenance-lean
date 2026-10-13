import Provenance.WinKept

/-!
# A generating set of the whole algebra

`thm:plainbasis` classifies the bases of the recursion-free fragment and
says of the whole algebra only which classes every basis contains. This
module supplies the other half: **a set of classes that generates the
whole algebra in the minimal universe**, `basisRecWinOps` =
`{∅, Π, σ, apply, γ, win, μ^⊎, μ^∪}` (`generatesOnRec_basisRecWinOps`),
and without `win` for the windows `prop:winderived` reaches
(`generatesOnRec_basisRecOps_of_winsDerivable`). The
apply is kept in place of `×` because the restriction on recursive terms
admits an apply whose left side reads the recursive relation, and the
decorrelation of such an apply puts `ε` of that left side inside the
right side's decorrelation – the recursive relation read twice, under a
duplicate elimination.

The pass is one structural induction (`exists_basisRec_aux`), every node
re-typed to regular columns and rewritten by the local identities of
`Provenance.PlainBasis` – a window kept over the doubled input
(`Provenance.WinKept`) or, without the window class, written as an apply
of a scalar aggregation (`winByApply`), duplicate elimination as a
grouping, the difference as a
`NOT IN`, a product as an apply, a union as two bag recursions
(`Provenance.SumByMu`) – with a second half for recursive bodies, as the
union's pass has. What the induction needs first is that the predicates
the generation statement asks of its output pass through the two
wrappers every case uses: the substitution an apply's right side is read
through (`AggQueryIn.substMap`) and the re-typing of an operator's
output (`AggQueryIn.allRegOf`).
-/

variable {T : Type} [ValueType T]

/-! ## The same through the re-typing of a query's columns -/

omit [ValueType T] in
theorem AggQueryIn.names_altBelow {c n : ℕ} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (q.altBelow m).names = q.names := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show ((q.castKind _).names) = _
    rw [AggQueryIn.names_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.altBelow
    split
    · split
      · rw [AggQueryIn.names_castKind]
        show (AggQueryIn.Alt _ _ (q.altBelow m)).names = _
        exact ih q
      · rw [AggQueryIn.names_castKind]
        exact ih q
      · show (AggQueryIn.Retag _ (q.altBelow m)).names = _
        exact ih q
    · rw [AggQueryIn.names_castKind]
      exact ih q

omit [ValueType T] in
theorem AggQueryIn.noMention_altBelow {c n : ℕ} {s : String} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (q.altBelow m).noMention s ↔ q.noMention s := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show ((q.castKind _).noMention s) ↔ _
    rw [AggQueryIn.noMention_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.altBelow
    split
    · split
      · rw [AggQueryIn.noMention_castKind]
        show (AggQueryIn.Alt _ _ (q.altBelow m)).noMention s ↔ _
        exact ih q
      · rw [AggQueryIn.noMention_castKind]
        exact ih q
      · show (AggQueryIn.Retag _ (q.altBelow m)).noMention s ↔ _
        exact ih q
    · rw [AggQueryIn.noMention_castKind]
      exact ih q

omit [ValueType T] in
theorem AggQueryIn.hygienic_altBelow {c n : ℕ} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (q.altBelow m).hygienic ↔ q.hygienic := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show ((q.castKind _).hygienic) ↔ _
    rw [AggQueryIn.hygienic_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.altBelow
    split
    · split
      · rw [AggQueryIn.hygienic_castKind]
        show (AggQueryIn.Alt _ _ (q.altBelow m)).hygienic ↔ _
        exact ih q
      · rw [AggQueryIn.hygienic_castKind]
        exact ih q
      · show (AggQueryIn.Retag _ (q.altBelow m)).hygienic ↔ _
        exact ih q
    · rw [AggQueryIn.hygienic_castKind]
      exact ih q

theorem AggQueryIn.inSig_altBelow {c n : ℕ} {Θ : Set (SeqAggFunc T)} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (q.altBelow m).inSig Θ ↔ q.inSig Θ := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show ((q.castKind _).inSig Θ) ↔ _
    rw [AggQueryIn.inSig_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.altBelow
    split
    · split
      · rw [AggQueryIn.inSig_castKind]
        show (AggQueryIn.Alt _ _ (q.altBelow m)).inSig Θ ↔ _
        exact ih q
      · rw [AggQueryIn.inSig_castKind]
        exact ih q
      · show (AggQueryIn.Retag _ (q.altBelow m)).inSig Θ ↔ _
        exact ih q
    · rw [AggQueryIn.inSig_castKind]
      exact ih q

theorem AggQueryIn.settlesAt_altBelow {c n : ℕ} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) (D : Database T)
      (γ : Fin c → T), (q.altBelow m).SettlesAt D γ ↔ q.SettlesAt D γ := by
  intro m
  induction m with
  | zero =>
    intro κ l q D γ
    show ((q.castKind _).SettlesAt D γ) ↔ _
    rw [AggQueryIn.settlesAt_castKind]
  | succ m ih =>
    intro κ l q D γ
    unfold AggQueryIn.altBelow
    split
    · split
      · rw [AggQueryIn.settlesAt_castKind]
        show (AggQueryIn.Alt _ _ (q.altBelow m)).SettlesAt D γ ↔ _
        exact ih q D γ
      · rw [AggQueryIn.settlesAt_castKind]
        exact ih q D γ
      · show (AggQueryIn.Retag _ (q.altBelow m)).SettlesAt D γ ↔ _
        exact ih q D γ
    · rw [AggQueryIn.settlesAt_castKind]
      exact ih q D γ

omit [ValueType T] in
@[simp] theorem AggQueryIn.names_allRegOf {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) : (q.allRegOf).names = q.names := by
  rw [AggQueryIn.allRegOf, AggQueryIn.names_castKind, AggQueryIn.names_altBelow]

omit [ValueType T] in
@[simp] theorem AggQueryIn.noMention_allRegOf {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (s : String) : (q.allRegOf).noMention s ↔ q.noMention s := by
  rw [AggQueryIn.allRegOf, AggQueryIn.noMention_castKind, AggQueryIn.noMention_altBelow]

omit [ValueType T] in
@[simp] theorem AggQueryIn.hygienic_allRegOf {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) : (q.allRegOf).hygienic ↔ q.hygienic := by
  rw [AggQueryIn.allRegOf, AggQueryIn.hygienic_castKind,
    AggQueryIn.hygienic_altBelow]

@[simp] theorem AggQueryIn.inSig_allRegOf {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (Θ : Set (SeqAggFunc T)) : (q.allRegOf).inSig Θ ↔ q.inSig Θ := by
  rw [AggQueryIn.allRegOf, AggQueryIn.inSig_castKind, AggQueryIn.inSig_altBelow]

@[simp] theorem AggQueryIn.settlesAt_allRegOf {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (D : Database T) (γ : Fin c → T) :
    (q.allRegOf).SettlesAt D γ ↔ q.SettlesAt D γ := by
  rw [AggQueryIn.allRegOf, AggQueryIn.settlesAt_castKind, AggQueryIn.settlesAt_altBelow]

/-! ## What re-typing a column keeps of the signature -/

theorem TermGIn.noFun_toReg {c n : ℕ} {κ : Fin n → ColKind} {t : TermGIn T c κ}
    (h : t.noFun = true) : (t.toReg).noFun = true := by
  cases t <;> first | rfl | exact Bool.noConfusion h

omit [ValueType T] in
theorem TermIn.noFun_atCol {c k : ℕ} {κ : Fin k → ColKind} (i : Fin k) (h : κ i = ColKind.reg)
    {t : TermIn T 1 0} (ht : t.noFun = true) : (t.atCol (c := c) i h).noFun = true := by
  cases t <;> first | rfl | exact Bool.noConfusion ht | exact Fin.elim0 ‹Fin 0›

theorem ProjColIn.noFun_toReg {c n : ℕ} {κ : Fin n → ColKind} {p : ProjColIn T c κ}
    (hs : p.sourceCol = true) (hn : p.noFun = true) : (p.toReg).noFun = true := by
  cases p with
  | term t => exact TermGIn.noFun_toReg hn
  | token k h => rfl
  | aggTerm k h gf => exact Bool.noConfusion hs
  | aggTermOf k h t => exact TermIn.noFun_atCol k rfl hn
  | provTerm t => exact TermGIn.noFun_toReg hn

omit [ValueType T] in
@[simp] theorem TermGIn.noFun_index {c n : ℕ} {κ : Fin n → ColKind} (k : Fin n)
    (h : κ k = ColKind.reg) : (TermGIn.index (T := T) (c := c) k h).noFun = true := rfl

theorem GenPredIn.noFun_toReg {c n : ℕ} {κ : Fin n → ColKind} {φ : GenPredIn T c κ}
    (h : φ.noFun = true) : (φ.toReg).noFun = true := by
  induction φ with
  | cmp op t₁ t₂ =>
    have h' := Bool.and_eq_true_iff.mp h
    show (_ && _) = true
    simp only [TermGIn.noFun_toReg h'.1, TermGIn.noFun_toReg h'.2, Bool.and_self]
  | aggCmp k hk op t =>
    show (_ && _) = true
    simp only [TermGIn.noFun_toReg h, TermGIn.noFun_index, Bool.and_self]
  | aggRange k hk op₁ t₁ op₂ t₂ =>
    have h' := Bool.and_eq_true_iff.mp h
    show ((_ && _) && (_ && _)) = true
    simp only [TermGIn.noFun_toReg h'.1, TermGIn.noFun_toReg h'.2, TermGIn.noFun_index,
      Bool.and_self]
  | and φ ψ ihφ ihψ =>
    have h' := Bool.and_eq_true_iff.mp h
    show (_ && _) = true
    simp only [ihφ h'.1, ihψ h'.2, Bool.and_self]
  | or φ ψ ihφ ihψ =>
    have h' := Bool.and_eq_true_iff.mp h
    show (_ && _) = true
    simp only [ihφ h'.1, ihψ h'.2, Bool.and_self]
  | not φ ih => exact ih h

/-! ## A product in the other order

A recursive term may read the recursive relation on either side of a
product, but only on the *left* of an apply, so a product whose right
side reads it is written as the apply the other way round, its columns
put back in place by a projection. -/

/-- The column `j` of a product, in the product the other way round. -/
def swapIdx (n₁ n₂ : ℕ) : Fin (n₁ + n₂) → Fin (n₂ + n₁) :=
  Fin.addCases (fun i => Fin.natAdd n₂ i) (fun i => Fin.castAdd n₁ i)

omit [ValueType T] in
theorem swap_append {n₁ n₂ : ℕ} (u : Tuple T n₁) (v : Tuple T n₂) :
    (fun j => (Fin.append v u : Tuple T (n₂ + n₁)) (swapIdx n₁ n₂ j))
      = (Fin.append u v : Tuple T (n₁ + n₂)) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · show (Fin.append v u : Tuple T (n₂ + n₁)) (swapIdx n₁ n₂ (Fin.castAdd n₂ i)) = _
    rw [swapIdx, Fin.addCases_left, Fin.append_right, Fin.append_left]
  · show (Fin.append v u : Tuple T (n₂ + n₁)) (swapIdx n₁ n₂ (Fin.natAdd n₁ i)) = _
    rw [swapIdx, Fin.addCases_right, Fin.append_left, Fin.append_right]

omit [ValueType T] in
/-- **A product read through the swap is the product the other way
round.** -/
theorem Relation.hMul_swap {n₁ n₂ : ℕ} (r₁ : Relation T n₁) (r₂ : Relation T n₂) :
    Multiset.map (fun u : Tuple T (n₂ + n₁) =>
        (fun j => u (swapIdx n₁ n₂ j) : Tuple T (n₁ + n₂))) (r₂ * r₁)
      = r₁ * r₂ := by
  rw [Relation.hMul_eq_bind, Relation.hMul_eq_bind, Multiset.map_bind]
  have h1 : ∀ v : Tuple T n₂,
      Multiset.map (fun u : Tuple T (n₂ + n₁) =>
          (fun j => u (swapIdx n₁ n₂ j) : Tuple T (n₁ + n₂)))
        (Multiset.map (fun u => (Fin.append v u : Tuple T (n₂ + n₁))) r₁)
      = r₁.bind (fun u => ({(Fin.append u v : Tuple T (n₁ + n₂))} : Multiset _)) := by
    intro v
    rw [Multiset.map_map, ← Multiset.bind_singleton]
    refine Multiset.bind_congr fun u _ => ?_
    show ({(fun j => (Fin.append v u : Tuple T (n₂ + n₁)) (swapIdx n₁ n₂ j)
      : Tuple T (n₁ + n₂))} : Multiset _) = _
    rw [swap_append]
  simp only [h1]
  rw [Multiset.bind_bind]
  exact Multiset.bind_congr fun u _ =>
    Multiset.bind_singleton r₂ (fun v => (Fin.append u v : Tuple T (n₁ + n₂)))

/-- The columns of the swap, over the product the other way round. -/
def swapCols (c n₁ n₂ : ℕ) :
    Fin (n₁ + n₂) → ProjColIn T c (Fin.append (ColKind.allReg n₂) (ColKind.allReg n₁)) :=
  fun j => ProjColIn.term (TermGIn.index (swapIdx n₁ n₂ j)
    (congrFun (AggQueryIn.append_allReg n₂ n₁) _))

omit [ValueType T] in
theorem swapCols_kind (c n₁ n₂ : ℕ) :
    (fun j => (swapCols (T := T) c n₁ n₂ j).kind) = ColKind.allReg (n₁ + n₂) :=
  funext fun _ => rfl

/-- **`q₁ × q₂` as the apply of `q₂` with `q₁` lifted to its context**,
the columns put back in the product's order. -/
def AggQueryIn.prodSwap {c n₁ n₂ : ℕ} {l : List (String × ℕ)}
    (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂) l)
    (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁)) :
    AggQueryIn T c (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) l :=
  (AggQueryIn.Proj (swapCols c n₁ n₂)
    (AggQueryIn.Apply q₂ (q₁.substMap (fun j : Fin c => Sum.inr (Fin.natAdd n₂ j))))).castKind
    (swapCols_kind c n₁ n₂)

theorem AggQueryIn.evaluatePlain_prodSwap {c n₁ n₂ : ℕ} {l : List (String × ℕ)}
    (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂) l) (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁))
    (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.prodSwap q₂ q₁).evaluatePlain D γ
      = q₁.evaluatePlain D γ * q₂.evaluatePlain D γ := by
  rw [AggQueryIn.prodSwap, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u : Tuple T (n₂ + n₁) =>
      (fun j => u (swapIdx n₁ n₂ j) : Tuple T (n₁ + n₂)))
    ((AggQueryIn.Apply q₂ (q₁.substMap (fun j : Fin c => Sum.inr (Fin.natAdd n₂ j)))).evaluatePlain
      D γ) = _
  rw [AggQueryIn.apply_plainEquiv_prod q₂ q₁ D γ]
  exact Relation.hMul_swap (q₁.evaluatePlain D γ) (q₂.evaluatePlain D γ)

/-! ## The window's derived form, through the predicates of the pass -/

theorem noFun_outerKeyCond {c n' m' : ℕ} {κ : Fin n' → ColKind} (cols : Tuple (Fin n') m')
    (h : ∀ k, κ (cols k) = ColKind.reg) (outs : Tuple (Fin c) m') :
    (outerKeyCond (T := T) cols h outs).noFun = true := by
  unfold outerKeyCond
  induction List.finRange m' with
  | nil => rfl
  | cons k l ih =>
    show (_ && _) = true
    rw [ih]
    rfl

section WinDerivedFacts

variable {n m p : ℕ} {c : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
  (ψ : GenPredIn T (n + c) (ColKind.allReg n)) (t : TermIn T c n) (f : SeqAggFunc T)
  (q : AggQueryIn T c n (ColKind.allReg n))

theorem AggQueryIn.names_winByApply : (winByApply P O o ψ t f q).names = q.names := by
  rw [winByApply, winByApplyOn, AggQueryIn.names_castKind]
  show Union.union q.names (q.substMap _).names = q.names
  rw [AggQueryIn.names_substMap, Finset.union_self]

theorem AggQueryIn.noMention_winByApply (s : String) :
    (winByApply P O o ψ t f q).noMention s ↔ q.noMention s := by
  rw [winByApply, winByApplyOn, AggQueryIn.noMention_castKind]
  show q.noMention s ∧ (q.substMap _).noMention s ↔ _
  rw [AggQueryIn.noMention_substMap]
  exact and_self_iff

theorem AggQueryIn.hygienic_winByApply :
    (winByApply P O o ψ t f q).hygienic ↔ q.hygienic := by
  rw [winByApply, winByApplyOn, AggQueryIn.hygienic_castKind]
  show q.hygienic ∧ (q.substMap _).hygienic ↔ _
  rw [AggQueryIn.hygienic_substMap]
  exact and_self_iff

theorem AggQueryIn.inSig_winByApply {Θ : Set (SeqAggFunc T)} (hf : f ∈ Θ) (ht : t.noFun = true)
    (hψ : ψ.noFun = true) (hq : q.inSig Θ) : (winByApply P O o ψ t f q).inSig Θ := by
  rw [winByApply, winByApplyOn, AggQueryIn.inSig_castKind]
  refine ⟨hq, fun j => ?_, fun j => ?_, ?_, (AggQueryIn.inSig_substMap q _).mpr hq⟩
  · rw [Subsingleton.elim j 0]
    show (t.substMap _).noFun = true
    rw [TermIn.noFun_substMap]
    exact ht
  · rw [Subsingleton.elim j 0]
    exact hf
  · show (_ && _) = true
    rw [noFun_outerKeyCond, hψ]
    rfl

theorem AggQueryIn.settlesAt_winByApply (D : Database T) (γ : Fin c → T) :
    (winByApply P O o ψ t f q).SettlesAt D γ ↔ q.SettlesAt D γ := by
  rw [winByApply, winByApplyOn, AggQueryIn.settlesAt_castKind]
  show q.SettlesAt D γ ∧ (∀ u, Multiset.Mem (q.evaluatePlain D γ) u →
    (q.substMap (applyOuter T c n)).SettlesAt D (Fin.append u γ)) ↔ _
  refine ⟨fun h => h.1, fun h => ⟨h, fun u _ => ?_⟩⟩
  rw [AggQueryIn.settlesAt_substMap, substVal_applyOuter]
  exact h

end WinDerivedFacts

/-! ## The difference's derived form, its product written as an apply -/

section DiffDerivedFacts

variable {c k : ℕ} (cnt : SeqAggFunc T) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))

/-- **The `NOT IN` form with its product written as an apply**, which is
what a basis holding the apply and not `×` reads it as. -/
def AggQueryIn.notInDiffA : AggQueryIn T c k (ColKind.allReg k) :=
  .Proj (fun i : Fin k =>
      .term (TermGIn.index (Fin.castAdd (k + 1) i) (notInKinds_left k i)))
    (.Sel AggQueryIn.notInCond (.Apply q₁
      ((AggQueryIn.tagAgg cnt q₁ q₂).substMap (applyOuter T c k))))

theorem AggQueryIn.evaluatePlain_notInDiffA (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.notInDiffA cnt q₁ q₂).evaluatePlain D γ
      = (AggQueryIn.notInDiff cnt q₁ q₂).evaluatePlain D γ := by
  show Multiset.map _ (Multiset.filter _ ((AggQueryIn.Apply q₁
      ((AggQueryIn.tagAgg cnt q₁ q₂).substMap
        (fun j : Fin c => Sum.inr (Fin.natAdd k j)))).evaluatePlain D γ))
    = Multiset.map _ (Multiset.filter _
      ((AggQueryIn.Prod q₁ (AggQueryIn.tagAgg cnt q₁ q₂)).evaluatePlain D γ))
  rw [AggQueryIn.apply_plainEquiv_prod q₁ (AggQueryIn.tagAgg cnt q₁ q₂) D γ]

theorem noFun_keyJoinCond {n m : ℕ} {κ : Fin m → ColKind} (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ (posL k) = ColKind.reg) (hR : ∀ k, κ (posR k) = ColKind.reg) :
    (keyJoinCond (T' := T) posL posR hL hR).noFun = true := by
  unfold keyJoinCond
  induction List.finRange n with
  | nil => rfl
  | cons k l ih =>
    show (_ && _) = true
    rw [ih]
    rfl

theorem AggQueryIn.noFun_notInCond :
    (AggQueryIn.notInCond (T := T) (c := c) (k := k)).noFun = true := by
  show ((_ : GenPredIn T c (notInKinds k)).noFun && _) = true
  rw [GenPredIn.noFun_substMap, noFun_keyJoinCond]
  rfl

omit [ValueType T] in
theorem AggQueryIn.noFun_tagCols (a : T) (j : Fin (k + 1)) :
    (AggQueryIn.tagCols (T := T) (c := c) (k := k) a j).noFun = true := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · show (ProjColIn.term (Fin.lastCases (TermGIn.const a)
      (fun i : Fin k => TermGIn.index i rfl) (Fin.last k))).noFun = true
    rw [Fin.lastCases_last]
    rfl
  · show (ProjColIn.term (Fin.lastCases (TermGIn.const a)
      (fun i : Fin k => TermGIn.index i rfl) (Fin.castSucc i))).noFun = true
    rw [Fin.lastCases_castSucc]
    rfl

theorem AggQueryIn.usesOnly_notInDiffA {S : Set OpKind} (hp : OpKind.proj ∈ S)
    (hs : OpKind.sel ∈ S) (ha : OpKind.apply ∈ S) (hu : OpKind.union ∈ S) (hg : OpKind.gamma ∈ S)
    (h₁ : q₁.usesOnly S) (h₂ : q₂.usesOnly S) : (AggQueryIn.notInDiffA cnt q₁ q₂).usesOnly S :=
  ⟨⟨hp, fun _ => rfl⟩, hs, ha, h₁, (AggQueryIn.usesOnly_substMap _ _).mpr
    ⟨hg, hu, ⟨⟨hp, fun _ => rfl⟩, h₁⟩, ⟨⟨hp, fun _ => rfl⟩, h₂⟩⟩⟩

theorem AggQueryIn.hygienic_notInDiffA (h₁ : q₁.hygienic) (h₂ : q₂.hygienic) :
    (AggQueryIn.notInDiffA cnt q₁ q₂).hygienic :=
  ⟨h₁, (AggQueryIn.hygienic_substMap _ _).mpr ⟨h₁, h₂⟩⟩

theorem AggQueryIn.inSig_notInDiffA {Θ : Set (SeqAggFunc T)} (hc : cnt ∈ Θ) (h₁ : q₁.inSig Θ)
    (h₂ : q₂.inSig Θ) : (AggQueryIn.notInDiffA cnt q₁ q₂).inSig Θ := by
  refine ⟨fun _ => rfl, AggQueryIn.noFun_notInCond, h₁,
    (AggQueryIn.inSig_substMap _ _).mpr ⟨fun j => ?_, fun j => ?_, fun j => ?_,
      ⟨fun j => AggQueryIn.noFun_tagCols 0 j, h₁⟩, ⟨fun j => AggQueryIn.noFun_tagCols _ j, h₂⟩⟩⟩
  · rw [Subsingleton.elim j 0]; rfl
  · rw [Subsingleton.elim j 0]; exact hc
  · rw [Subsingleton.elim j 0]; rfl

theorem AggQueryIn.overSchema_notInDiffA {sch : Schema} (h₁ : q₁.overSchema sch)
    (h₂ : q₂.overSchema sch) : (AggQueryIn.notInDiffA cnt q₁ q₂).overSchema sch :=
  ⟨h₁, (AggQueryIn.overSchema_substMap _ _ sch).mpr ⟨h₁, h₂⟩⟩

theorem AggQueryIn.names_notInDiffA :
    (AggQueryIn.notInDiffA cnt q₁ q₂).names ⊆ Union.union q₁.names q₂.names := by
  show Union.union q₁.names ((AggQueryIn.tagAgg cnt q₁ q₂).substMap _).names ⊆ _
  rw [AggQueryIn.names_substMap]
  show Union.union q₁.names (Union.union q₁.names q₂.names) ⊆ _
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

theorem AggQueryIn.noMention_notInDiffA {s : String} (h₁ : q₁.noMention s) (h₂ : q₂.noMention s) :
    (AggQueryIn.notInDiffA cnt q₁ q₂).noMention s :=
  ⟨h₁, (AggQueryIn.noMention_substMap _ _).mpr ⟨h₁, h₂⟩⟩

theorem AggQueryIn.settlesAt_notInDiffA (D : Database T) (γ : Fin c → T) (h₁ : q₁.SettlesAt D γ)
    (h₂ : q₂.SettlesAt D γ) : (AggQueryIn.notInDiffA cnt q₁ q₂).SettlesAt D γ := by
  refine ⟨h₁, fun u _ => ?_⟩
  rw [AggQueryIn.settlesAt_substMap, substVal_applyOuter]
  exact ⟨h₁, h₂⟩

theorem AggQueryIn.sumsAllReg_notInDiffA (h₁ : q₁.sumsAllReg) (h₂ : q₂.sumsAllReg) :
    (AggQueryIn.notInDiffA cnt q₁ q₂).sumsAllReg := by
  refine ⟨h₁, ?_⟩
  show ((AggQueryIn.tagAgg cnt q₁ q₂).substMap _).sumsAllReg
  rw [AggQueryIn.sumsAllReg_substMap]
  exact ⟨funext fun _ => rfl, h₁, h₂⟩

end DiffDerivedFacts

/-! ## A product as an apply, in the order given and the other way round -/

section ProdApplyFacts

variable {c n₁ n₂ : ℕ} {l : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁) l)
  (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂))

/-- **`q₁ × q₂` as the apply of `q₁` with `q₂` lifted to its context.** -/
def AggQueryIn.prodA : AggQueryIn T c (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) l :=
  (AggQueryIn.Apply q₁ (q₂.substMap (applyOuter T c n₁))).castKind
    (AggQueryIn.append_allReg n₁ n₂)

theorem AggQueryIn.evaluatePlain_prodA (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.prodA q₁ q₂).evaluatePlain D γ = q₁.evaluatePlain D γ * q₂.evaluatePlain D γ := by
  rw [AggQueryIn.prodA, AggQueryIn.evaluatePlain_castKind]
  show (AggQueryIn.Apply q₁
    (q₂.substMap (fun j : Fin c => Sum.inr (Fin.natAdd n₁ j)))).evaluatePlain D γ = _
  exact AggQueryIn.apply_plainEquiv_prod q₁ q₂ D γ

/-- The apply form is defined where the two factors are. -/
theorem AggQueryIn.settlesAt_prodA (D : Database T) (γ : Fin c → T) (h₁ : q₁.SettlesAt D γ)
    (h₂ : q₂.SettlesAt D γ) : (AggQueryIn.prodA q₁ q₂).SettlesAt D γ := by
  rw [AggQueryIn.prodA, AggQueryIn.settlesAt_castKind]
  refine ⟨h₁, fun u _ => ?_⟩
  rw [AggQueryIn.settlesAt_substMap, substVal_applyOuter]
  exact h₂

omit [ValueType T] in
theorem AggQueryIn.usesOnly_prodA {S : Set OpKind} (ha : OpKind.apply ∈ S) (h₁ : q₁.usesOnly S)
    (h₂ : q₂.usesOnly S) : (AggQueryIn.prodA q₁ q₂).usesOnly S := by
  rw [AggQueryIn.prodA, AggQueryIn.usesOnly_castKind]
  exact ⟨ha, h₁, (AggQueryIn.usesOnly_substMap _ _).mpr h₂⟩

omit [ValueType T] in
theorem AggQueryIn.hygienic_prodA (h₁ : q₁.hygienic) (h₂ : q₂.hygienic) :
    (AggQueryIn.prodA q₁ q₂).hygienic := by
  rw [AggQueryIn.prodA, AggQueryIn.hygienic_castKind]
  exact ⟨h₁, (AggQueryIn.hygienic_substMap _ _).mpr h₂⟩

theorem AggQueryIn.inSig_prodA {Θ : Set (SeqAggFunc T)} (h₁ : q₁.inSig Θ) (h₂ : q₂.inSig Θ) :
    (AggQueryIn.prodA q₁ q₂).inSig Θ := by
  rw [AggQueryIn.prodA, AggQueryIn.inSig_castKind]
  exact ⟨h₁, (AggQueryIn.inSig_substMap _ _).mpr h₂⟩

omit [ValueType T] in
theorem AggQueryIn.overSchema_prodA {sch : Schema} (h₁ : q₁.overSchema sch)
    (h₂ : q₂.overSchema sch) :
    (AggQueryIn.prodA q₁ q₂).overSchema sch := by
  rw [AggQueryIn.prodA, AggQueryIn.overSchema_castKind]
  exact ⟨h₁, (AggQueryIn.overSchema_substMap _ _ sch).mpr h₂⟩

omit [ValueType T] in
theorem AggQueryIn.names_prodA :
    (AggQueryIn.prodA q₁ q₂).names = Union.union q₁.names q₂.names := by
  rw [AggQueryIn.prodA, AggQueryIn.names_castKind]
  show Union.union q₁.names (q₂.substMap _).names = _
  rw [AggQueryIn.names_substMap]

omit [ValueType T] in
theorem AggQueryIn.noMention_prodA {s : String} (h₁ : q₁.noMention s) (h₂ : q₂.noMention s) :
    (AggQueryIn.prodA q₁ q₂).noMention s := by
  rw [AggQueryIn.prodA, AggQueryIn.noMention_castKind]
  exact ⟨h₁, (AggQueryIn.noMention_substMap _ _).mpr h₂⟩

end ProdApplyFacts

section ProdSwapFacts

variable {c n₁ n₂ : ℕ} {l : List (String × ℕ)} (q₂ : AggQueryIn T c n₂ (ColKind.allReg n₂) l)
  (q₁ : AggQueryIn T c n₁ (ColKind.allReg n₁))

/-- The swapped form is defined where the two factors are. -/
theorem AggQueryIn.settlesAt_prodSwap (D : Database T) (γ : Fin c → T) (h₂ : q₂.SettlesAt D γ)
    (h₁ : q₁.SettlesAt D γ) : (AggQueryIn.prodSwap q₂ q₁).SettlesAt D γ := by
  rw [AggQueryIn.prodSwap, AggQueryIn.settlesAt_castKind]
  refine ⟨h₂, fun u _ => ?_⟩
  show (q₁.substMap (applyOuter T c n₂)).SettlesAt D (Fin.append u γ)
  rw [AggQueryIn.settlesAt_substMap, substVal_applyOuter]
  exact h₁

omit [ValueType T] in
theorem AggQueryIn.usesOnly_prodSwap {S : Set OpKind} (hp : OpKind.proj ∈ S)
    (ha : OpKind.apply ∈ S) (h₂ : q₂.usesOnly S) (h₁ : q₁.usesOnly S) :
    (AggQueryIn.prodSwap q₂ q₁).usesOnly S := by
  rw [AggQueryIn.prodSwap, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hp, fun _ => rfl⟩, ha, h₂, (AggQueryIn.usesOnly_substMap _ _).mpr h₁⟩

omit [ValueType T] in
theorem AggQueryIn.hygienic_prodSwap (h₂ : q₂.hygienic) (h₁ : q₁.hygienic) :
    (AggQueryIn.prodSwap q₂ q₁).hygienic := by
  rw [AggQueryIn.prodSwap, AggQueryIn.hygienic_castKind]
  exact ⟨h₂, (AggQueryIn.hygienic_substMap _ _).mpr h₁⟩

theorem AggQueryIn.inSig_prodSwap {Θ : Set (SeqAggFunc T)} (h₂ : q₂.inSig Θ) (h₁ : q₁.inSig Θ) :
    (AggQueryIn.prodSwap q₂ q₁).inSig Θ := by
  rw [AggQueryIn.prodSwap, AggQueryIn.inSig_castKind]
  exact ⟨fun _ => rfl, h₂, (AggQueryIn.inSig_substMap _ _).mpr h₁⟩

omit [ValueType T] in
theorem AggQueryIn.overSchema_prodSwap {sch : Schema} (h₂ : q₂.overSchema sch)
    (h₁ : q₁.overSchema sch) : (AggQueryIn.prodSwap q₂ q₁).overSchema sch := by
  rw [AggQueryIn.prodSwap, AggQueryIn.overSchema_castKind]
  exact ⟨h₂, (AggQueryIn.overSchema_substMap _ _ sch).mpr h₁⟩

omit [ValueType T] in
theorem AggQueryIn.names_prodSwap :
    (AggQueryIn.prodSwap q₂ q₁).names = Union.union q₂.names q₁.names := by
  rw [AggQueryIn.prodSwap, AggQueryIn.names_castKind]
  show Union.union q₂.names (q₁.substMap _).names = _
  rw [AggQueryIn.names_substMap]

omit [ValueType T] in
theorem AggQueryIn.noMention_prodSwap {s : String} (h₂ : q₂.noMention s) (h₁ : q₁.noMention s) :
    (AggQueryIn.prodSwap q₂ q₁).noMention s := by
  rw [AggQueryIn.prodSwap, AggQueryIn.noMention_castKind]
  exact ⟨h₂, (AggQueryIn.noMention_substMap _ _).mpr h₁⟩

end ProdSwapFacts

/-! ## The classes, and what the pass carries -/

/-- **The generating set**: the construction's classes and the set
recursion. -/
def basisRecOps : Set OpKind := insert OpKind.muSet AggQueryIn.sumMuOps

theorem sumMuOps_subset_basisRecOps : AggQueryIn.sumMuOps ⊆ basisRecOps :=
  fun _ hx => Set.mem_insert_of_mem _ hx

theorem union_notMem_basisRecOps : OpKind.union ∉ basisRecOps := by
  simp [basisRecOps, AggQueryIn.sumMuOps]

omit [ValueType T] in
/-- With no `⊎` at all, every `⊎` is all-regular. -/
theorem AggQueryIn.sumsAllReg_of_usesOnly {S : Set OpKind} (hu : OpKind.union ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l), q.usesOnly S → q.sumsAllReg := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun hq => ih hq.2
  | Sel φ q _ ih => exact fun hq => ih hq.2
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => absurd hq.1 hu
  | Dedup q ih => exact fun hq => ih hq.2
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Alt k hk q ih => exact fun hq => ih hq
  | Retag hk q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.2.1, ih₁ hq.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.2.1, ih₁ hq.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun hq => ih hq.2
  | GammaScalar ts fs q ord ih => exact fun hq => ih hq.2
  | GammaNest is his p fn q ih => exact fun hq => ih hq.2
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | Win P O o w t fw q hrr dist keep ih => exact fun hq => ih hq.2
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq => ih hq.2

/-- **No aggregating operator**: no grouping, no window, no second-level
aggregation. In the minimal signature such a query creates no value: what
it returns it read off the instance, its context or its own constants. -/
def AggQueryIn.noAgg : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.noAgg
  | _, _, _, _, .Sel _ q _ => q.noAgg
  | _, _, _, _, .Prod q₁ q₂ => q₁.noAgg ∧ q₂.noAgg
  | _, _, _, _, .Apply q₁ q₂ => q₁.noAgg ∧ q₂.noAgg
  | _, _, _, _, .Sum q₁ q₂ => q₁.noAgg ∧ q₂.noAgg
  | _, _, _, _, .Dedup q => q.noAgg
  | _, _, _, _, .Diff q₁ q₂ => q₁.noAgg ∧ q₂.noAgg
  | _, _, _, _, .Alt _ _ q => q.noAgg
  | _, _, _, _, .Retag _ q => q.noAgg
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.noAgg ∧ q₁.noAgg
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.noAgg ∧ q₁.noAgg
  | _, _, _, _, .Gamma _ _ _ _ _ _ => False
  | _, _, _, _, .GammaScalar _ _ _ _ => False
  | _, _, _, _, .GammaNest _ _ _ _ _ => False
  | _, _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  | _, _, _, _, .Win _ _ _ _ _ _ _ _ _ _ => False
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

/-- **Every set recursion's term computes no aggregate**: the fragment
`prop:muunion` replaces `μ^∪` in. -/
def AggQueryIn.setRecNoAgg : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.setRecNoAgg
  | _, _, _, _, .Sel _ q _ => q.setRecNoAgg
  | _, _, _, _, .Prod q₁ q₂ => q₁.setRecNoAgg ∧ q₂.setRecNoAgg
  | _, _, _, _, .Apply q₁ q₂ => q₁.setRecNoAgg ∧ q₂.setRecNoAgg
  | _, _, _, _, .Sum q₁ q₂ => q₁.setRecNoAgg ∧ q₂.setRecNoAgg
  | _, _, _, _, .Dedup q => q.setRecNoAgg
  | _, _, _, _, .Diff q₁ q₂ => q₁.setRecNoAgg ∧ q₂.setRecNoAgg
  | _, _, _, _, .Alt _ _ q => q.setRecNoAgg
  | _, _, _, _, .Retag _ q => q.setRecNoAgg
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.setRecNoAgg ∧ q₁.setRecNoAgg
  | _, _, _, _, .MuSet _ q₀ q₁ => q₁.noAgg ∧ q₀.setRecNoAgg ∧ q₁.setRecNoAgg
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.setRecNoAgg
  | _, _, _, _, .GammaScalar _ _ q _ => q.setRecNoAgg
  | _, _, _, _, .GammaNest _ _ _ _ q => q.setRecNoAgg
  | _, _, _, _, .ProvSum _ _ _ q => q.setRecNoAgg
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.setRecNoAgg
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.setRecNoAgg
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.setRecNoAgg

/-- **What the pass keeps of a query, besides its value**: the
generating classes, the restriction on recursive terms, the signature,
well-formedness over a schema declaring none of the fresh names, the
names (its own, or fresh ones), and the names it does not mention (fresh
ones aside). Windows are gone from the output, so nothing is said of
them. -/
structure AggQueryIn.BasisRecOf (S : Set OpKind) (Θ : Set (SeqAggFunc T)) (f : ℕ → String)
    {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)} (q : AggQueryIn T c n κ l)
    (q' : AggQueryIn T c n (ColKind.allReg n) l') : Prop where
  usesOnly : q'.usesOnly S
  hygienic : q'.hygienic
  inSig : q'.inSig Θ
  over : ∀ sch : Schema, (∀ i, sch (f i) = none) → q.overSchema sch → q'.overSchema sch
  names : ∀ x, x ∈ q'.names → x ∈ q.names ∨ ∃ i, x = f i
  nom : ∀ s, (∀ i, s ≠ f i) → q.noMention s → q'.noMention s

namespace AggQueryIn

/-- A third of the supply: the names `f (3 i + j)`. -/
def tri (f : ℕ → String) (j : ℕ) : ℕ → String := fun i => f (3 * i + j)

theorem tri_injective {f : ℕ → String} (hf : Function.Injective f) (j : ℕ) :
    Function.Injective (tri f j) :=
  fun _ _ h => by have := hf h; omega

omit [ValueType T] in
theorem tri_fresh {f : ℕ → String} {A B : Finset String} (hfr : ∀ i, f i ∉ B)
    (hAB : A ⊆ B) (j : ℕ) : ∀ i, tri f j i ∉ A :=
  fun _ h => hfr _ (hAB h)

omit [ValueType T] in
theorem names_tri {f : ℕ → String} {j : ℕ} {x : String} {A B : Finset String}
    (h : x ∈ A ∨ ∃ i, x = tri f j i) (hAB : A ⊆ B) : x ∈ B ∨ ∃ i, x = f i :=
  h.imp (fun h => hAB h) (fun ⟨i, hi⟩ => ⟨3 * i + j, hi⟩)

omit [ValueType T] in
theorem ne_tri {f : ℕ → String} {s : String} (hs : ∀ i, s ≠ f i) (j : ℕ) :
    ∀ i, s ≠ tri f j i :=
  fun _ => hs _

omit [ValueType T] in
theorem sch_tri {f : ℕ → String} {sch : Schema} (hsch : ∀ i, sch (f i) = none) (j : ℕ) :
    ∀ i, sch (tri f j i) = none :=
  fun _ => hsch _

omit [ValueType T] in
/-- A name of one third of the supply is not among the names a child
built with another third, nor among the query's. -/
theorem tri_notMem {f : ℕ → String} (hf : Function.Injective f) {j j' : ℕ} (hj : j < 3)
    (hj' : j' < 3) (hne : j ≠ j') {A B : Finset String}
    (hn : ∀ x, x ∈ A → x ∈ B ∨ ∃ i, x = tri f j' i) (hfr : ∀ i, f i ∉ B) :
    ∀ i, tri f j i ∉ A := fun i h => by
  rcases hn _ h with h' | ⟨i', hi'⟩
  · exact hfr _ h'
  · have := hf hi'
    omega

omit [ValueType T] in
theorem ne_of_mem_names {f : ℕ → String} {s : String} {B : Finset String}
    (hfr : ∀ i, f i ∉ B) (hs : s ∈ B) : ∀ i, s ≠ f i :=
  fun i h => hfr i (h ▸ hs)

omit [ValueType T] in
theorem update_fresh {f : ℕ → String} {sch : Schema} {s : String} {m : ℕ}
    (hsch : ∀ i, sch (f i) = none) (hs : ∀ i, s ≠ f i) : ∀ i, (sch.update s m) (f i) = none :=
  fun i => by
    show (if f i = s then _ else _) = none
    rw [ite_eq_right (hs i).symm]
    exact hsch i

/-- **What stands in for a set recursion** where the target classes hold
none: from the pass's rewriting of the base, the body and its closed
part of `μ^∪R.(q₀, q₁)`, with `q₁` computing no aggregate, a query over
the target classes defined and equal to the recursion wherever the
recursion is. The supply `f` is the recursion's own, its children having
been rewritten with its first and second thirds; the bodies are over the
schema the recursion is written over, with its name declared. -/
def MuSetHandler (S : Set OpKind) (Θ : Set (SeqAggFunc T)) : Prop :=
  ∀ {c n : ℕ} (s : String) (q₀ q₀' qC : AggQueryIn T c n (ColKind.allReg n))
    (q₁ q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)])
    (f : ℕ → String), Function.Injective f → (∀ i, s ≠ f i) →
    (∀ i, f i ∉ q₀.names) → (∀ i, f i ∉ q₁.names) → q₀.noMention s → q₁.noMention s →
    ∀ sch : Schema, (∀ i, sch (f i) = none) → sch s = none → q₀.overSchema sch →
      q₁.overSchema (sch.update s n) → q₁.noAgg → q₁.inSig Θ →
      qC.noMention s → q₀'.noMention s →
      BasisRecOf S Θ (tri f 1) q₀ q₀' → BasisRecOf S Θ (tri f 2) q₁ q₁' →
      BasisRecOf S Θ (tri f 2) q₁ qC →
      (∀ (D : Database T) (γ : Fin c → T), q₀.SettlesAt D γ →
        q₀'.SettlesAt D γ ∧ q₀.evaluatePlain D γ = q₀'.evaluatePlain D γ) →
      (∀ (D : Database T) (γ : Fin c → T), q₁.SettlesAt D γ →
        q₁'.SettlesAt D γ ∧ qC.SettlesAt D γ
          ∧ (q₁.evaluatePlain D γ : Multiset (Tuple T n))
              = q₁'.evaluatePlain D γ + qC.evaluatePlain D γ) →
      ∃ q' : AggQueryIn T c n (ColKind.allReg n),
        BasisRecOf S Θ f (AggQueryIn.MuSet s q₀ q₁) q' ∧
        ∀ (D : Database T) (γ : Fin c → T), (AggQueryIn.MuSet s q₀ q₁).SettlesAt D γ →
          q'.SettlesAt D γ
            ∧ (AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ = q'.evaluatePlain D γ


omit [ValueType T] in
private theorem orL {p a b : Prop} (h : p ∨ a ∧ b) : p ∨ a := h.imp_right And.left

omit [ValueType T] in
private theorem orR {p a b : Prop} (h : p ∨ a ∧ b) : p ∨ b := h.imp_right And.right

/-- **The pass**, both halves at once: every query of the whole algebra in
a signature `Θ` holding the counting aggregate `cnt`, with restricted
recursions and derivable windows, is matched by a query over
`basisRecOps` with all-regular columns, keeping what `BasisRecOf` lists
and defined and equal wherever the query is; and a body reading the name
`s` once is matched by such a body and a closed query it is the sum of
(`exists_sumFree_aux`'s shape). -/
theorem exists_basisRec_aux {S : Set OpKind} (hS : sumMuOps ⊆ S) (hnu : OpKind.union ∉ S)
    {Θ : Set (SeqAggFunc T)} (hms : OpKind.muSet ∈ S ∨ MuSetHandler S Θ)
    (cnt : SeqAggFunc T) (hcnt : cnt ∈ Θ) (hcc : SeqAggFunc.Counts cnt) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly plainRecOps → q.hygienic → q.inSig Θ →
      (OpKind.win ∈ S ∨ q.WinsDerivable) →
      ∀ (f : ℕ → String), Function.Injective f → (∀ i, f i ∉ q.names) →
      ∀ (sch : Schema), (∀ i, sch (f i) = none) → q.overSchema sch →
        OpKind.muSet ∈ S ∨ q.setRecNoAgg →
        (l = [] → ∃ q' : AggQueryIn T c n (ColKind.allReg n), BasisRecOf S Θ f q q' ∧
            ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
              q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ)
        ∧ (∀ (s : String) (m : ℕ), l = [(s, m)] → q.noMention s →
            ∃ (q' : AggQueryIn T c n (ColKind.allReg n) l)
              (qC : AggQueryIn T c n (ColKind.allReg n)), qC.noMention s
              ∧ BasisRecOf S Θ f q q' ∧ BasisRecOf S Θ f q qC
              ∧ ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
                q'.SettlesAt D γ ∧ qC.SettlesAt D γ
                  ∧ (q.evaluatePlain D γ : Multiset (Tuple T n))
                      = q'.evaluatePlain D γ + qC.evaluatePlain D γ) := by
  have hSu : sumMuOps ⊆ S := hS
  have hproj : OpKind.proj ∈ S := hS (by simp [sumMuOps])
  have hsel : OpKind.sel ∈ S := hS (by simp [sumMuOps])
  have happly : OpKind.apply ∈ S := hS (by simp [sumMuOps])
  have hgamma : OpKind.gamma ∈ S := hS (by simp [sumMuOps])
  have hempty : OpKind.empty ∈ S := hS (by simp [sumMuOps])
  have hmub : OpKind.muBag ∈ S := hS (by simp [sumMuOps])
  have hsar : ∀ {c n : ℕ} (p : AggQueryIn T c n (ColKind.allReg n)), p.usesOnly S →
      p.sumsAllReg := fun p hp => AggQueryIn.sumsAllReg_of_usesOnly hnu p hp
  have hmono : ∀ {c n : ℕ} (p : AggQueryIn T c n (ColKind.allReg n)), p.usesOnly S →
      p.usesOnly (insert OpKind.union S) :=
    fun p hp => AggQueryIn.usesOnly_mono (Set.subset_insert _ _) p hp
  -- the union of two outputs, through the union's own pass
  have hsum : ∀ {c n : ℕ} (p₁ p₂ : AggQueryIn T c n (ColKind.allReg n)) (g : ℕ → String),
      Function.Injective g → (∀ i, g i ∉ p₁.names) → (∀ i, g i ∉ p₂.names) →
      p₁.usesOnly S → p₂.usesOnly S → p₁.hygienic → p₂.hygienic →
      p₁.inSig Θ → p₂.inSig Θ →
      ∃ p : AggQueryIn T c n (ColKind.allReg n),
        SumFreeOf S Θ g (AggQueryIn.Sum p₁ p₂) p ∧
        ∀ (D : Database T) (γ : Fin c → T), p₁.SettlesAt D γ → p₂.SettlesAt D γ →
          p.SettlesAt D γ ∧ (p.evaluatePlain D γ : Multiset (Tuple T n))
            = p₁.evaluatePlain D γ + p₂.evaluatePlain D γ := by
    intro c n p₁ p₂ g hg hg₁ hg₂ hu₁ hu₂ hr₁ hr₂ hi₁ hi₂
    obtain ⟨p, hsf, he⟩ := (exists_sumFree_aux hSu (AggQueryIn.Sum p₁ p₂)
      ⟨Set.mem_insert _ _, hmono p₁ hu₁, hmono p₂ hu₂⟩ ⟨hr₁, hr₂⟩ ⟨hi₁, hi₂⟩
      ⟨rfl, hsar p₁ hu₁, hsar p₂ hu₂⟩ g hg
      (fun i h => (Finset.mem_union.mp h).elim (hg₁ i) (hg₂ i))).1 rfl
    exact ⟨p, hsf, fun D γ h₁ h₂ => ⟨(he D γ ⟨h₁, h₂⟩).1, (he D γ ⟨h₁, h₂⟩).2.symm⟩⟩
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    exact ⟨fun _ => ⟨AggQueryIn.Rel n s', ⟨trivial, trivial, trivial, fun _ _ h => h,
      fun x hx => Or.inl hx, fun _ _ h => h⟩, fun D γ _ => ⟨trivial, rfl⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Hole n s' =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    refine ⟨fun hl => absurd hl (by simp), fun s m hl _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
    refine ⟨AggQueryIn.Hole n _, emptyRel n, noMention_emptyRel n _,
      ⟨trivial, trivial, trivial, fun _ _ h => h, fun x hx => Or.inl hx, fun _ _ h => h⟩,
      ⟨usesOnly_emptyRel hSu n, hygienic_emptyRel n, inSig_emptyRel Θ n,
        fun sch _ _ => overSchema_emptyRel sch n,
        fun x hx => by rw [names_emptyRel] at hx; exact absurd hx (Finset.notMem_empty x),
        fun s' _ _ => noMention_emptyRel n s'⟩,
      fun D γ _ => ⟨trivial, settlesAt_emptyRel n D γ, ?_⟩⟩
    rw [evaluatePlain_emptyRel]
    exact (add_zero (M := Multiset (Tuple T n)) _).symm
  | Empty =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    exact ⟨fun _ => ⟨AggQueryIn.Empty, ⟨hempty, trivial, trivial, fun _ _ h => h,
      fun x hx => Or.inl hx, fun _ _ h => h⟩, fun D γ _ => ⟨trivial, rfl⟩⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
  | Proj ps q ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, hbody⟩ := ih hq.2 hr hi.2 hw f hf hfr sch hsch ho hfrag
    have hcols : ∀ j, ((ps j).toReg).sourceCol = true := fun j => by cases ps j <;> rfl
    -- the bundle for a re-typed projection over an output
    have hbundle : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ (ColKind.allReg _) l'},
        BasisRecOf S Θ f q p →
        BasisRecOf S Θ f (AggQueryIn.Proj ps q)
          ((AggQueryIn.Proj (fun j => (ps j).toReg) p).castKind
            (funext fun j => ProjColIn.kind_toReg (ps j))) := fun hp =>
      { usesOnly := by
          rw [AggQueryIn.usesOnly_castKind]
          exact ⟨⟨hproj, hcols⟩, hp.usesOnly⟩
        hygienic := by
          rw [AggQueryIn.hygienic_castKind]
          exact hp.hygienic
        inSig := by
          rw [AggQueryIn.inSig_castKind]
          exact ⟨fun j => ProjColIn.noFun_toReg (hq.1.2 j) (hi.1 j), hp.inSig⟩
        over := fun sch hsch ho => by
          rw [AggQueryIn.overSchema_castKind]
          exact hp.over sch hsch ho
        names := fun x hx => by
          rw [AggQueryIn.names_castKind] at hx
          exact hp.names x hx
        nom := fun s hs hn => by
          rw [AggQueryIn.noMention_castKind]
          exact hp.nom s hs hn }
    have heval : ∀ {l' : List (String × ℕ)} (p : AggQueryIn T _ _ (ColKind.allReg _) l')
        (D : Database T) (γ : Fin _ → T),
        ((AggQueryIn.Proj (fun j => (ps j).toReg) p).castKind
            (funext fun j => ProjColIn.kind_toReg (ps j))).evaluatePlain D γ
          = Multiset.map (fun u => (fun j => (ps j).evalPlain u γ : Tuple T _))
              (p.evaluatePlain D γ) := fun p D γ => by
      rw [AggQueryIn.evaluatePlain_castKind]
      simp only [AggQueryIn.evaluatePlain]
      refine Multiset.map_congr rfl (fun u _ => funext (fun j => ?_))
      exact ProjColIn.evalPlain_toReg (ps j) (hq.1.2 j) u γ
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hb, he⟩ := hc hl
      refine ⟨_, hbundle hb, fun D γ hset => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_castKind]; exact hs', ?_⟩
      rw [heval]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
    · obtain ⟨q', qC, hCn, hb, hbC, he⟩ := hbody s m hl hnm
      refine ⟨(AggQueryIn.Proj (fun j => (ps j).toReg) q').castKind
          (funext fun j => ProjColIn.kind_toReg (ps j)),
        (AggQueryIn.Proj (fun j => (ps j).toReg) qC).castKind
          (funext fun j => ProjColIn.kind_toReg (ps j)),
        by rw [AggQueryIn.noMention_castKind]; exact hCn, hbundle hb, hbundle hbC,
        fun D γ hset => ?_⟩
      obtain ⟨hs', hsC', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_castKind]; exact hs',
        by rw [AggQueryIn.settlesAt_castKind]; exact hsC', ?_⟩
      rw [heval, heval]
      simp only [AggQueryIn.evaluatePlain]
      rw [he', Multiset.map_add]
  | Sel φ q hφ ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, hbody⟩ := ih hq.2 hr hi.2 hw f hf hfr sch hsch ho hfrag
    have hok : ∀ l' : List (String × ℕ), SelOK l' φ.toReg :=
      fun _ => SelOK.of_noAggAtom (GenPredIn.hasAggAtom_toReg φ)
    have hbundle : ∀ {l' : List (String × ℕ)} {p : AggQueryIn T _ _ (ColKind.allReg _) l'},
        BasisRecOf S Θ f q p →
        BasisRecOf S Θ f (AggQueryIn.Sel φ q) (AggQueryIn.Sel φ.toReg p (hok l')) := fun hp =>
      ⟨⟨hsel, hp.usesOnly⟩, hp.hygienic, ⟨GenPredIn.noFun_toReg hi.1, hp.inSig⟩,
        hp.over, hp.names, hp.nom⟩
    have heval : ∀ {l' : List (String × ℕ)} (p : AggQueryIn T _ _ (ColKind.allReg _) l')
        (D : Database T) (γ : Fin _ → T),
        (AggQueryIn.Sel φ.toReg p (hok l')).evaluatePlain D γ
          = Multiset.filter (fun u => φ.holdsPlain u γ) (p.evaluatePlain D γ) := fun p D γ => by
      simp only [AggQueryIn.evaluatePlain]
      exact Multiset.filter_congr (fun u _ => GenPredIn.holdsPlain_toReg φ u γ)
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hb, he⟩ := hc hl
      refine ⟨_, hbundle hb, fun D γ hset => ?_⟩
      obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨hs', ?_⟩
      rw [heval]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
    · obtain ⟨q', qC, hCn, hb, hbC, he⟩ := hbody s m hl hnm
      refine ⟨AggQueryIn.Sel φ.toReg q' (hok _), AggQueryIn.Sel φ.toReg qC (hok _),
        hCn, hbundle hb, hbundle hbC,
        fun D γ hset => ?_⟩
      obtain ⟨hs', hsC', he'⟩ := he D γ hset
      refine ⟨hs', hsC', ?_⟩
      rw [heval, heval]
      simp only [AggQueryIn.evaluatePlain]
      rw [he', Multiset.filter_add]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc₁, hbody₁⟩ := ih₁ hq.2.1 hr.1 hi.1 (orL hw) (tri f 1) (tri_injective hf 1)
      (tri_fresh hfr Finset.subset_union_left 1) sch (sch_tri hsch 1) ho.1
      (hfrag.imp_right And.left)
    obtain ⟨hc₂, hbody₂⟩ := ih₂ hq.2.2 hr.2 hi.2 (orR hw) (tri f 2) (tri_injective hf 2)
      (tri_fresh hfr Finset.subset_union_right 2) sch (sch_tri hsch 2) ho.2
      (hfrag.imp_right And.right)
    have hbundleA : ∀ {l' : List (String × ℕ)} {p₁ : AggQueryIn T _ _ (ColKind.allReg _) l'}
        {p₂ : AggQueryIn T _ _ (ColKind.allReg _)},
        BasisRecOf S Θ (tri f 1) q₁ p₁ → BasisRecOf S Θ (tri f 2) q₂ p₂ →
        BasisRecOf S Θ f (AggQueryIn.Prod q₁ q₂) (AggQueryIn.prodA p₁ p₂) := fun hp₁ hp₂ =>
      ⟨usesOnly_prodA _ _ happly hp₁.usesOnly hp₂.usesOnly,
        hygienic_prodA _ _ hp₁.hygienic hp₂.hygienic,
        inSig_prodA _ _ hp₁.inSig hp₂.inSig,
        fun sch hsch ho => overSchema_prodA _ _ (hp₁.over sch (sch_tri hsch 1) ho.1)
          (hp₂.over sch (sch_tri hsch 2) ho.2),
        fun x hx => by
          rw [names_prodA] at hx
          exact (Finset.mem_union.mp hx).elim
            (fun h => names_tri (hp₁.names x h) Finset.subset_union_left)
            (fun h => names_tri (hp₂.names x h) Finset.subset_union_right),
        fun s hs hn => noMention_prodA _ _ (hp₁.nom s (ne_tri hs 1) hn.1)
          (hp₂.nom s (ne_tri hs 2) hn.2)⟩
    have hbundleS : ∀ {p₁ : AggQueryIn T _ _ (ColKind.allReg _)}
        {l' : List (String × ℕ)} {p₂ : AggQueryIn T _ _ (ColKind.allReg _) l'},
        BasisRecOf S Θ (tri f 1) q₁ p₁ → BasisRecOf S Θ (tri f 2) q₂ p₂ →
        BasisRecOf S Θ f (AggQueryIn.Prod q₁ q₂) (AggQueryIn.prodSwap p₂ p₁) := fun hp₁ hp₂ =>
      ⟨usesOnly_prodSwap _ _ hproj happly hp₂.usesOnly hp₁.usesOnly,
        hygienic_prodSwap _ _ hp₂.hygienic hp₁.hygienic,
        inSig_prodSwap _ _ hp₂.inSig hp₁.inSig,
        fun sch hsch ho => overSchema_prodSwap _ _ (hp₂.over sch (sch_tri hsch 2) ho.2)
          (hp₁.over sch (sch_tri hsch 1) ho.1),
        fun x hx => by
          rw [names_prodSwap] at hx
          exact (Finset.mem_union.mp hx).elim
            (fun h => names_tri (hp₂.names x h) Finset.subset_union_right)
            (fun h => names_tri (hp₁.names x h) Finset.subset_union_left),
        fun s hs hn => noMention_prodSwap _ _ (hp₂.nom s (ne_tri hs 2) hn.2)
          (hp₁.nom s (ne_tri hs 1) hn.1)⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      obtain ⟨q₁', hb₁, he₁⟩ := hc₁ rfl
      obtain ⟨q₂', hb₂, he₂⟩ := hc₂ rfl
      refine ⟨AggQueryIn.prodA q₁' q₂', hbundleA hb₁ hb₂, fun D γ hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
      obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
      refine ⟨settlesAt_prodA _ _ D γ hs₁' hs₂', ?_⟩
      rw [evaluatePlain_prodA]
      simp only [AggQueryIn.evaluatePlain]
      rw [he₁', he₂']
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₂', hb₂, he₂⟩ := hc₂ rfl
        obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hbody₁ s m rfl h₁
        refine ⟨AggQueryIn.prodA p₁ q₂', AggQueryIn.prodA pC q₂',
          noMention_prodA _ _ hCn (hb₂.nom s (ne_tri (ne_of_mem_names hfr
            (Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁
              (List.mem_singleton_self _)))) 2) h₂),
          hbundleA hp hb₂, hbundleA hpC hb₂, fun D γ hset => ?_⟩
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.1
        obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
        refine ⟨settlesAt_prodA _ _ D γ hp' hs₂', settlesAt_prodA _ _ D γ hpC' hs₂', ?_⟩
        rw [evaluatePlain_prodA, evaluatePlain_prodA]
        simp only [AggQueryIn.evaluatePlain]
        rw [he', he₂', Relation.hMul_eq_bind, Relation.hMul_eq_bind, Relation.hMul_eq_bind,
          Multiset.add_bind]
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₁', hb₁, he₁⟩ := hc₁ rfl
        obtain ⟨p₂, pC, hCn, hp, hpC, he⟩ := hbody₂ s m rfl h₂
        refine ⟨AggQueryIn.prodSwap p₂ q₁', AggQueryIn.prodSwap pC q₁',
          noMention_prodSwap _ _ hCn (hb₁.nom s (ne_tri (ne_of_mem_names hfr
            (Finset.mem_union_right _ (AggQueryIn.mem_names_of_index q₂
              (List.mem_singleton_self _)))) 1) h₁),
          hbundleS hb₁ hp, hbundleS hb₁ hpC, fun D γ hset => ?_⟩
        obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.2
        refine ⟨settlesAt_prodSwap _ _ D γ hp' hs₁', settlesAt_prodSwap _ _ D γ hpC' hs₁', ?_⟩
        rw [evaluatePlain_prodSwap, evaluatePlain_prodSwap]
        simp only [AggQueryIn.evaluatePlain]
        rw [he₁', he', Relation.hMul_eq_bind, Relation.hMul_eq_bind, Relation.hMul_eq_bind,
          ← Multiset.bind_add]
        exact Multiset.bind_congr fun a _ => Multiset.map_add _ _ _
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc₁, hbody₁⟩ := ih₁ hq.2.1 hr.1 hi.1 (orL hw) (tri f 1) (tri_injective hf 1)
      (tri_fresh hfr Finset.subset_union_left 1) sch (sch_tri hsch 1) ho.1
      (hfrag.imp_right And.left)
    obtain ⟨hc₂, -⟩ := ih₂ hq.2.2 hr.2 hi.2 (orR hw) (tri f 2) (tri_injective hf 2)
      (tri_fresh hfr Finset.subset_union_right 2) sch (sch_tri hsch 2) ho.2
      (hfrag.imp_right And.right)
    obtain ⟨q₂', hb₂, he₂⟩ := hc₂ rfl
    have hbundle : ∀ {l' : List (String × ℕ)} {p₁ : AggQueryIn T _ _ (ColKind.allReg _) l'},
        BasisRecOf S Θ (tri f 1) q₁ p₁ →
        BasisRecOf S Θ f (AggQueryIn.Apply q₁ q₂)
          ((AggQueryIn.Apply p₁ q₂').castKind (AggQueryIn.append_allReg _ _)) := fun hp₁ =>
      { usesOnly := by
          rw [AggQueryIn.usesOnly_castKind]
          exact ⟨happly, hp₁.usesOnly, hb₂.usesOnly⟩
        hygienic := by
          rw [AggQueryIn.hygienic_castKind]
          exact ⟨hp₁.hygienic, hb₂.hygienic⟩
        inSig := by
          rw [AggQueryIn.inSig_castKind]
          exact ⟨hp₁.inSig, hb₂.inSig⟩
        over := fun sch hsch ho => by
          rw [AggQueryIn.overSchema_castKind]
          exact ⟨hp₁.over sch (sch_tri hsch 1) ho.1, hb₂.over sch (sch_tri hsch 2) ho.2⟩
        names := fun x hx => by
          rw [AggQueryIn.names_castKind] at hx
          exact (Finset.mem_union.mp hx).elim
            (fun h => names_tri (hp₁.names x h) Finset.subset_union_left)
            (fun h => names_tri (hb₂.names x h) Finset.subset_union_right)
        nom := fun s hs hn => by
          rw [AggQueryIn.noMention_castKind]
          exact ⟨hp₁.nom s (ne_tri hs 1) hn.1, hb₂.nom s (ne_tri hs 2) hn.2⟩ }
    have hmem : ∀ (D : Database T) (γ : Fin _ → T) (l' : List (String × ℕ))
        (p : AggQueryIn T _ _ (ColKind.allReg _) l'),
        q₁.evaluatePlain D γ = p.evaluatePlain D γ →
        ∀ u, Multiset.Mem (p.evaluatePlain D γ) u → Multiset.Mem (q₁.evaluatePlain D γ) u :=
      fun D γ _ p he u hu => by rw [he]; exact hu
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q₁', hb₁, he₁⟩ := hc₁ hl
      refine ⟨_, hbundle hb₁, fun D γ hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
      refine ⟨by
        rw [AggQueryIn.settlesAt_castKind]
        exact ⟨hs₁', fun u hu => (he₂ D _ (hset.2 u (hmem D γ _ q₁' he₁' u hu))).1⟩, ?_⟩
      rw [AggQueryIn.evaluatePlain_castKind]
      simp only [AggQueryIn.evaluatePlain]
      rw [he₁']
      exact Multiset.bind_congr fun u hu =>
        congrArg _ (he₂ D _ (hset.2 u (hmem D γ _ q₁' he₁' u hu))).2
    · obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hbody₁ s m hl hnm.1
      have hs2 : ∀ i, s ≠ tri f 2 i :=
        ne_tri (ne_of_mem_names hfr (Finset.mem_union_left _
          (AggQueryIn.mem_names_of_index q₁ (hl ▸ List.mem_singleton_self _)))) 2
      refine ⟨(AggQueryIn.Apply p₁ q₂').castKind (AggQueryIn.append_allReg _ _),
        (AggQueryIn.Apply pC q₂').castKind (AggQueryIn.append_allReg _ _),
        by rw [AggQueryIn.noMention_castKind]; exact ⟨hCn, hb₂.nom s hs2 hnm.2⟩,
        hbundle hp, hbundle hpC, fun D γ hset => ?_⟩
      obtain ⟨hp', hpC', he'⟩ := he D γ hset.1
      have hmem' : ∀ u, Multiset.Mem (p₁.evaluatePlain D γ) u
          ∨ Multiset.Mem (pC.evaluatePlain D γ) u →
          Multiset.Mem (q₁.evaluatePlain D γ) u :=
        fun u hu => by rw [he']; exact Multiset.mem_add.mpr hu
      refine ⟨by
        rw [AggQueryIn.settlesAt_castKind]
        exact ⟨hp', fun u hu => (he₂ D _ (hset.2 u (hmem' u (Or.inl hu)))).1⟩, by
        rw [AggQueryIn.settlesAt_castKind]
        exact ⟨hpC', fun u hu => (he₂ D _ (hset.2 u (hmem' u (Or.inr hu)))).1⟩, ?_⟩
      rw [AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain_castKind]
      simp only [AggQueryIn.evaluatePlain]
      rw [he', Multiset.add_bind]
      refine congrArg₂ (· + ·) ?_ ?_
      · exact Multiset.bind_congr fun u hu =>
          congrArg _ (he₂ D _ (hset.2 u (hmem' u (Or.inl hu)))).2
      · exact Multiset.bind_congr fun u hu =>
          congrArg _ (he₂ D _ (hset.2 u (hmem' u (Or.inr hu)))).2
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc₁, hbody₁⟩ := ih₁ hq.2.1 hr.1 hi.1 (orL hw) (tri f 1) (tri_injective hf 1)
      (tri_fresh hfr Finset.subset_union_left 1) sch (sch_tri hsch 1) ho.1
      (hfrag.imp_right And.left)
    obtain ⟨hc₂, hbody₂⟩ := ih₂ hq.2.2 hr.2 hi.2 (orR hw) (tri f 2) (tri_injective hf 2)
      (tri_fresh hfr Finset.subset_union_right 2) sch (sch_tri hsch 2) ho.2
      (hfrag.imp_right And.right)
    have hf0₁ : ∀ i, f i ∉ q₁.names := fun i h => hfr i (Finset.mem_union_left _ h)
    have hf0₂ : ∀ i, f i ∉ q₂.names := fun i h => hfr i (Finset.mem_union_right _ h)
    -- the bundle of the union's pass, as a bundle of this one
    have hbundle : ∀ {p₁ p₂ p : AggQueryIn T _ _ (ColKind.allReg _)},
        BasisRecOf S Θ (tri f 1) q₁ p₁ → BasisRecOf S Θ (tri f 2) q₂ p₂ →
        SumFreeOf S Θ (tri f 0) (AggQueryIn.Sum p₁ p₂) p →
        BasisRecOf S Θ f (AggQueryIn.Sum q₁ q₂) p := fun hp₁ hp₂ hsf =>
      ⟨hsf.usesOnly, hsf.hygienic, hsf.inSig,
        fun sch hsch ho => hsf.over sch (sch_tri hsch 0)
          ⟨hp₁.over sch (sch_tri hsch 1) ho.1, hp₂.over sch (sch_tri hsch 2) ho.2⟩,
        fun x hx => (hsf.names x hx).elim
          (fun h => (Finset.mem_union.mp h).elim
            (fun h => names_tri (hp₁.names x h) Finset.subset_union_left)
            (fun h => names_tri (hp₂.names x h) Finset.subset_union_right))
          (fun ⟨i, hi⟩ => Or.inr ⟨3 * i + 0, hi⟩),
        fun s hs hn => hsf.nom s (ne_tri hs 0)
          ⟨hp₁.nom s (ne_tri hs 1) hn.1, hp₂.nom s (ne_tri hs 2) hn.2⟩⟩
    have hfresh : ∀ {p₁ p₂ : AggQueryIn T _ _ (ColKind.allReg _)},
        BasisRecOf S Θ (tri f 1) q₁ p₁ → BasisRecOf S Θ (tri f 2) q₂ p₂ →
        (∀ i, tri f 0 i ∉ p₁.names) ∧ (∀ i, tri f 0 i ∉ p₂.names) := fun hp₁ hp₂ =>
      ⟨tri_notMem hf (by omega) (by omega) (by omega) hp₁.names hf0₁,
        tri_notMem hf (by omega) (by omega) (by omega) hp₂.names hf0₂⟩
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
      subst hl₁ hl₂
      obtain ⟨q₁', hb₁, he₁⟩ := hc₁ rfl
      obtain ⟨q₂', hb₂, he₂⟩ := hc₂ rfl
      obtain ⟨p, hsf, he⟩ := hsum q₁' q₂' (tri f 0) (tri_injective hf 0) (hfresh hb₁ hb₂).1
        (hfresh hb₁ hb₂).2 hb₁.usesOnly hb₂.usesOnly hb₁.hygienic hb₂.hygienic
        hb₁.inSig hb₂.inSig
      refine ⟨p, hbundle hb₁ hb₂ hsf, fun D γ hset => ?_⟩
      obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
      obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
      obtain ⟨hp, hpe⟩ := he D γ hs₁' hs₂'
      refine ⟨hp, ?_⟩
      show (q₁.evaluatePlain D γ : Multiset (Tuple T _)) + q₂.evaluatePlain D γ = _
      rw [hpe, he₁', he₂']
    · rcases List.append_eq_singleton' hl with ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₂', hb₂, he₂⟩ := hc₂ rfl
        obtain ⟨p₁, pC, hCn, hp, hpC, he⟩ := hbody₁ s m rfl h₁
        have hss : s ∈ (AggQueryIn.Sum q₁ q₂).names :=
          Finset.mem_union_left _ (AggQueryIn.mem_names_of_index q₁ (List.mem_singleton_self _))
        obtain ⟨p, hsf, hpe⟩ := hsum pC q₂' (tri f 0) (tri_injective hf 0) (hfresh hpC hb₂).1
          (hfresh hpC hb₂).2 hpC.usesOnly hb₂.usesOnly hpC.hygienic hb₂.hygienic
          hpC.inSig hb₂.inSig
        refine ⟨p₁, p,
          hsf.nom s (ne_tri (ne_of_mem_names hfr hss) 0)
            ⟨hCn, hb₂.nom s (ne_tri (ne_of_mem_names hfr hss) 2) h₂⟩,
          ⟨hp.usesOnly, hp.hygienic, hp.inSig,
            fun sch hsch ho => hp.over sch (sch_tri hsch 1) ho.1,
            fun x hx => names_tri (hp.names x hx) Finset.subset_union_left,
            fun s' hs' hn => hp.nom s' (ne_tri hs' 1) hn.1⟩,
          hbundle hpC hb₂ hsf, fun D γ hset => ?_⟩
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.1
        obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
        obtain ⟨hps, hpv⟩ := hpe D γ hpC' hs₂'
        refine ⟨hp', hps, ?_⟩
        show (q₁.evaluatePlain D γ : Multiset (Tuple T _)) + q₂.evaluatePlain D γ = _
        rw [hpv, he', he₂']
        show (_ : Multiset (Tuple T _)) + _ + _ = _ + (_ + _)
        exact add_assoc _ _ _
      · subst hl₁ hl₂
        obtain ⟨h₁, h₂⟩ := hnm
        obtain ⟨q₁', hb₁, he₁⟩ := hc₁ rfl
        obtain ⟨p₂, pC, hCn, hp, hpC, he⟩ := hbody₂ s m rfl h₂
        have hss : s ∈ (AggQueryIn.Sum q₁ q₂).names :=
          Finset.mem_union_right _ (AggQueryIn.mem_names_of_index q₂ (List.mem_singleton_self _))
        obtain ⟨p, hsf, hpe⟩ := hsum q₁' pC (tri f 0) (tri_injective hf 0) (hfresh hb₁ hpC).1
          (hfresh hb₁ hpC).2 hb₁.usesOnly hpC.usesOnly hb₁.hygienic hpC.hygienic
          hb₁.inSig hpC.inSig
        refine ⟨p₂, p,
          hsf.nom s (ne_tri (ne_of_mem_names hfr hss) 0)
            ⟨hb₁.nom s (ne_tri (ne_of_mem_names hfr hss) 1) h₁, hCn⟩,
          ⟨hp.usesOnly, hp.hygienic, hp.inSig,
            fun sch hsch ho => hp.over sch (sch_tri hsch 2) ho.2,
            fun x hx => names_tri (hp.names x hx) Finset.subset_union_right,
            fun s' hs' hn => hp.nom s' (ne_tri hs' 2) hn.2⟩,
          hbundle hb₁ hpC hsf, fun D γ hset => ?_⟩
        obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
        obtain ⟨hp', hpC', he'⟩ := he D γ hset.2
        obtain ⟨hps, hpv⟩ := hpe D γ hs₁' hpC'
        refine ⟨hp', hps, ?_⟩
        show (q₁.evaluatePlain D γ : Multiset (Tuple T _)) + q₂.evaluatePlain D γ = _
        rw [hpv, he₁', he']
        show (_ : Multiset (Tuple T _)) + (_ + _) = _ + (_ + _)
        exact add_left_comm _ _ _
  | @Dedup cd nd q ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, -⟩ := ih hq.2 hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨q', hb, he⟩ := hc rfl
    have hκ : (fun j => ((Fin.append (ColKind.allReg nd) (fun _ : Fin 0 => ColKind.agg)) j))
        = ColKind.allReg (nd + 0) := by
      funext j
      refine Fin.addCases (fun k => ?_) (fun z => z.elim0) j
      rw [Fin.append_left]
      rfl
    refine ⟨fun _ => ⟨(AggQueryIn.Gamma (fun k => k) (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0) q').castKind hκ, ?_, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · exact { usesOnly := by
                rw [AggQueryIn.usesOnly_castKind]
                exact ⟨hgamma, hb.usesOnly⟩
              hygienic := by
                rw [AggQueryIn.hygienic_castKind]
                exact hb.hygienic
              inSig := by
                rw [AggQueryIn.inSig_castKind]
                exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, hb.inSig⟩
              over := fun sch hsch ho => by
                rw [AggQueryIn.overSchema_castKind]
                exact hb.over sch hsch ho
              names := fun x hx => by
                rw [AggQueryIn.names_castKind] at hx
                exact hb.names x hx
              nom := fun s hs hn => by
                rw [AggQueryIn.noMention_castKind]
                exact hb.nom s hs hn }
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_castKind]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_castKind]
      refine Eq.trans ?_ (AggQueryIn.dedup_plainEquiv_gamma q' D γ)
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc₁, -⟩ := ih₁ hq.2.1 hr.1 hi.1 (orL hw) (tri f 1) (tri_injective hf 1)
      (tri_fresh hfr Finset.subset_union_left 1) sch (sch_tri hsch 1) ho.1
      (hfrag.imp_right And.left)
    obtain ⟨hc₂, -⟩ := ih₂ hq.2.2 hr.2 hi.2 (orR hw) (tri f 2) (tri_injective hf 2)
      (tri_fresh hfr Finset.subset_union_right 2) sch (sch_tri hsch 2) ho.2
      (hfrag.imp_right And.right)
    obtain ⟨q₁', hb₁, he₁⟩ := hc₁ rfl
    obtain ⟨q₂', hb₂, he₂⟩ := hc₂ rfl
    have hf0₁ : ∀ i, f i ∉ q₁.names := fun i h => hfr i (Finset.mem_union_left _ h)
    have hf0₂ : ∀ i, f i ∉ q₂.names := fun i h => hfr i (Finset.mem_union_right _ h)
    have hn₁ : ∀ i, tri f 0 i ∉ q₁'.names :=
      tri_notMem hf (by omega) (by omega) (by omega) hb₁.names hf0₁
    have hn₂ : ∀ i, tri f 0 i ∉ q₂'.names :=
      tri_notMem hf (by omega) (by omega) (by omega) hb₂.names hf0₂
    obtain ⟨p, hsf, he⟩ := (exists_sumFree_aux hSu (AggQueryIn.notInDiffA cnt q₁' q₂')
      (usesOnly_notInDiffA cnt q₁' q₂' (Set.mem_insert_of_mem _ hproj)
        (Set.mem_insert_of_mem _ hsel) (Set.mem_insert_of_mem _ happly) (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ hgamma) (hmono q₁' hb₁.usesOnly) (hmono q₂' hb₂.usesOnly))
      (hygienic_notInDiffA cnt q₁' q₂' hb₁.hygienic hb₂.hygienic)
      (inSig_notInDiffA cnt q₁' q₂' hcnt hb₁.inSig hb₂.inSig)
      (sumsAllReg_notInDiffA cnt q₁' q₂' (hsar q₁' hb₁.usesOnly) (hsar q₂' hb₂.usesOnly))
      (tri f 0) (tri_injective hf 0)
      (fun i h => (Finset.mem_union.mp (names_notInDiffA cnt q₁' q₂' h)).elim (hn₁ i) (hn₂ i))).1
      rfl
    refine ⟨fun _ => ⟨p, ⟨hsf.usesOnly, hsf.hygienic, hsf.inSig,
      fun sch hsch ho => hsf.over sch (sch_tri hsch 0)
        (overSchema_notInDiffA cnt q₁' q₂' (hb₁.over sch (sch_tri hsch 1) ho.1)
          (hb₂.over sch (sch_tri hsch 2) ho.2)),
      fun x hx => (hsf.names x hx).elim
        (fun h => (Finset.mem_union.mp (names_notInDiffA cnt q₁' q₂' h)).elim
          (fun h => names_tri (hb₁.names x h) Finset.subset_union_left)
          (fun h => names_tri (hb₂.names x h) Finset.subset_union_right))
        (fun ⟨i, hi⟩ => Or.inr ⟨3 * i + 0, hi⟩),
      fun s hs hn => hsf.nom s (ne_tri hs 0)
        (noMention_notInDiffA cnt q₁' q₂' (hb₁.nom s (ne_tri hs 1) hn.1)
          (hb₂.nom s (ne_tri hs 2) hn.2))⟩, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨hs₁', he₁'⟩ := he₁ D γ hset.1
    obtain ⟨hs₂', he₂'⟩ := he₂ D γ hset.2
    obtain ⟨hps, hpe⟩ := he D γ (settlesAt_notInDiffA cnt q₁' q₂' D γ hs₁' hs₂')
    refine ⟨hps, ?_⟩
    have hD : (AggQueryIn.Diff q₁ q₂).evaluatePlain D γ
        = (AggQueryIn.Diff q₁' q₂').evaluatePlain D γ := by
      simp only [AggQueryIn.evaluatePlain]
      rw [he₁', he₂']
    rw [hD, AggQueryIn.diff_plainEquiv_notIn cnt hcc q₁' q₂' D γ, ← evaluatePlain_notInDiffA, hpe]
  | Alt k hk q ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, hbody⟩ := ih hq hr hi hw f hf hfr sch hsch ho hfrag
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hb, he⟩ := hc hl
      exact ⟨q', ⟨hb.usesOnly, hb.hygienic, hb.inSig, hb.over, hb.names, hb.nom⟩,
        fun D γ hset => he D γ hset⟩
    obtain ⟨q', qC, hCn, hb, hbC, he⟩ := hbody s m hl hnm
    exact ⟨q', qC, hCn, ⟨hb.usesOnly, hb.hygienic, hb.inSig, hb.over, hb.names, hb.nom⟩,
      ⟨hbC.usesOnly, hbC.hygienic, hbC.inSig, hbC.over, hbC.names, hbC.nom⟩,
      fun D γ hset => he D γ hset⟩
  | Retag hk q ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, hbody⟩ := ih hq hr hi hw f hf hfr sch hsch ho hfrag
    refine ⟨fun hl => ?_, fun s m hl hnm => ?_⟩
    · obtain ⟨q', hb, he⟩ := hc hl
      exact ⟨q', ⟨hb.usesOnly, hb.hygienic, hb.inSig, hb.over, hb.names, hb.nom⟩,
        fun D γ hset => he D γ hset⟩
    obtain ⟨q', qC, hCn, hb, hbC, he⟩ := hbody s m hl hnm
    exact ⟨q', qC, hCn, ⟨hb.usesOnly, hb.hygienic, hb.inSig, hb.over, hb.names, hb.nom⟩,
      ⟨hbC.usesOnly, hbC.hygienic, hbC.inSig, hbC.over, hbC.names, hbC.nom⟩,
      fun D γ hset => he D γ hset⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    have hfs : ∀ i, s ≠ f i := ne_of_mem_names hfr (Finset.mem_insert_self s _)
    obtain ⟨hc₀, -⟩ := ih₀ hq.2.1 hr.2.2.1 hi.1 (orL hw) (tri f 1) (tri_injective hf 1)
      (tri_fresh hfr (fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)) 1)
      sch (sch_tri hsch 1) ho.2.1 (hfrag.imp_right And.left)
    obtain ⟨q₀', hb₀, he₀⟩ := hc₀ rfl
    obtain ⟨-, hbody₁⟩ := ih₁ hq.2.2 hr.2.2.2 hi.2 (orR hw) (tri f 2) (tri_injective hf 2)
      (tri_fresh hfr (fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_right _ h)) 2)
      (sch.update s _) (update_fresh (sch_tri hsch 2) (ne_tri hfs 2)) ho.2.2.2
      (hfrag.imp_right And.right)
    obtain ⟨q₁', qC, hCn, hb₁, hbC, he₁⟩ := hbody₁ s _ rfl hr.2.1
    refine ⟨fun _ => ⟨AggQueryIn.Mu s q₀' q₁', ?_, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · exact {
        usesOnly := ⟨hmub, hb₀.usesOnly, hb₁.usesOnly⟩
        hygienic := ⟨hb₀.nom s (ne_tri hfs 1) hr.1, hb₁.nom s (ne_tri hfs 2) hr.2.1,
          hb₀.hygienic, hb₁.hygienic⟩
        inSig := ⟨hb₀.inSig, hb₁.inSig⟩
        over := fun sch hsch ho => ⟨ho.1, hb₀.over sch (sch_tri hsch 1) ho.2.1,
          hb₁.nom s (ne_tri hfs 2) hr.2.1,
          hb₁.over (sch.update s _) (sch_tri (update_fresh hsch hfs) 2) ho.2.2.2⟩
        names := fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact Or.inl (Finset.mem_insert_self _ _)
          exact (Finset.mem_union.mp hx').elim
            (fun h => names_tri (hb₀.names x h)
              (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)))
            (fun h => names_tri (hb₁.names x h)
              (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_right _ hy)))
        nom := fun s' hs' hn => ⟨hb₀.nom s' (ne_tri hs' 1) hn.1, hb₁.nom s' (ne_tri hs' 2) hn.2⟩ }
    · exact AggQueryIn.mu_of_split s q₀ q₀' q₁ q₁' qC hCn D γ hset (he₀ D γ hset.1)
        (fun D' h => he₁ D' γ h)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    have hfs : ∀ i, s ≠ f i := ne_of_mem_names hfr (Finset.mem_insert_self s _)
    have hf0₀ : ∀ i, f i ∉ q₀.names :=
      fun i h => hfr i (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hf0₁ : ∀ i, f i ∉ q₁.names :=
      fun i h => hfr i (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    obtain ⟨hc₀, -⟩ := ih₀ hq.2.1 hr.2.2.1 hi.1 (orL hw) (tri f 1) (tri_injective hf 1)
      (tri_fresh hfr (fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)) 1)
      sch (sch_tri hsch 1) ho.2.1 (hfrag.imp_right fun h => h.2.1)
    obtain ⟨q₀', hb₀, he₀⟩ := hc₀ rfl
    obtain ⟨-, hbody₁⟩ := ih₁ hq.2.2 hr.2.2.2 hi.2 (orR hw) (tri f 2) (tri_injective hf 2)
      (tri_fresh hfr (fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_right _ h)) 2)
      (sch.update s _) (update_fresh (sch_tri hsch 2) (ne_tri hfs 2)) ho.2.2.2
      (hfrag.imp_right fun h => h.2.2)
    obtain ⟨q₁', qC, hCn, hb₁, hbC, he₁⟩ := hbody₁ s _ rfl hr.2.1
    have h₀n : q₀'.noMention s := hb₀.nom s (ne_tri hfs 1) hr.1
    by_cases hmus : OpKind.muSet ∈ S
    swap
    · -- the target has no set recursion: the simulation stands in
      have hfr' : q₁.noAgg := (hfrag.resolve_left hmus).1
      obtain ⟨q', hb', he'⟩ := (hms.resolve_left hmus) s q₀ q₀' qC q₁ q₁' f hf hfs hf0₀ hf0₁
        hr.1 hr.2.1 sch hsch ho.1 ho.2.1 ho.2.2.2 hfr' hi.2 hCn h₀n hb₀ hb₁ hbC
        (fun D γ h => he₀ D γ h) (fun D γ h => he₁ D γ h)
      exact ⟨fun _ => ⟨q', hb', he'⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    obtain ⟨base, hsf, hbase⟩ := hsum q₀' qC (tri f 0) (tri_injective hf 0)
      (tri_notMem hf (by omega) (by omega) (by omega) hb₀.names hf0₀)
      (tri_notMem hf (by omega) (by omega) (by omega) hbC.names hf0₁)
      hb₀.usesOnly hbC.usesOnly hb₀.hygienic hbC.hygienic hb₀.inSig hbC.inSig
    have hbn : base.noMention s := hsf.nom s (ne_tri hfs 0) ⟨h₀n, hCn⟩
    refine ⟨fun _ => ⟨AggQueryIn.MuSet s base q₁', ?_, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · exact {
        usesOnly := ⟨hmus, hsf.usesOnly, hb₁.usesOnly⟩
        hygienic := ⟨hbn, hb₁.nom s (ne_tri hfs 2) hr.2.1, hsf.hygienic, hb₁.hygienic⟩
        inSig := ⟨hsf.inSig, hb₁.inSig⟩
        over := fun sch hsch ho => ⟨ho.1,
          hsf.over sch (sch_tri hsch 0) ⟨hb₀.over sch (sch_tri hsch 1) ho.2.1,
            AggQueryIn.overSchema_of_update_of_noMention qC (fun _ h => by simp at h) hCn
              (hbC.over (sch.update s _) (sch_tri (update_fresh hsch hfs) 2) ho.2.2.2)⟩,
          hb₁.nom s (ne_tri hfs 2) hr.2.1,
          hb₁.over (sch.update s _) (sch_tri (update_fresh hsch hfs) 2) ho.2.2.2⟩
        names := fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact Or.inl (Finset.mem_insert_self _ _)
          rcases Finset.mem_union.mp hx' with h | h
          · rcases hsf.names x h with h' | ⟨i, hi⟩
            · exact (Finset.mem_union.mp h').elim
                (fun h => names_tri (hb₀.names x h)
                  (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)))
                (fun h => names_tri (hbC.names x h)
                  (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_right _ hy)))
            · exact Or.inr ⟨3 * i + 0, hi⟩
          · exact names_tri (hb₁.names x h)
              (fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_right _ hy))
        nom := fun s' hs' hn => ⟨hsf.nom s' (ne_tri hs' 0)
          ⟨hb₀.nom s' (ne_tri hs' 1) hn.1, hbC.nom s' (ne_tri hs' 2) hn.2⟩,
          hb₁.nom s' (ne_tri hs' 2) hn.2⟩ }
    · exact AggQueryIn.muSet_of_split s q₀ q₀' q₁ q₁' qC base hCn D γ hset
        (fun D' h => he₀ D' γ h) (fun D' h => he₁ D' γ h)
        (fun D' h₀ hC => hbase D' γ h₀ hC)
  | Gamma is ts fs q keep ord ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2.2 hw f hf hfr sch hsch ho hfrag
    obtain ⟨q', hb, he⟩ := hc rfl
    refine ⟨fun _ => ⟨(AggQueryIn.Gamma is ts fs q' keep ord).allRegOf, ?_, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · exact { usesOnly := by
                rw [AggQueryIn.usesOnly_allRegOf]
                exact ⟨hgamma, hb.usesOnly⟩
              hygienic := by
                rw [AggQueryIn.hygienic_allRegOf]
                exact hb.hygienic
              inSig := by
                rw [AggQueryIn.inSig_allRegOf]
                exact ⟨hi.1, hi.2.1, hi.2.2.1, hb.inSig⟩
              over := fun sch hsch ho => by
                rw [AggQueryIn.overSchema_allRegOf]
                exact hb.over sch hsch ho
              names := fun x hx => by
                rw [AggQueryIn.names_allRegOf] at hx
                exact hb.names x hx
              nom := fun s hs hn => by
                rw [AggQueryIn.noMention_allRegOf]
                exact hb.nom s hs hn }
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
  | GammaScalar ts fs q ord ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2 hw f hf hfr sch hsch ho hfrag
    obtain ⟨q', hb, he⟩ := hc rfl
    refine ⟨fun _ => ⟨(AggQueryIn.GammaScalar ts fs q' ord).allRegOf, ?_, fun D γ hset => ?_⟩,
      fun _ _ hl _ => absurd hl (by simp)⟩
    · exact { usesOnly := by
                rw [AggQueryIn.usesOnly_allRegOf]
                exact ⟨hgamma, hb.usesOnly⟩
              hygienic := by
                rw [AggQueryIn.hygienic_allRegOf]
                exact hb.hygienic
              inSig := by
                rw [AggQueryIn.inSig_allRegOf]
                exact ⟨hi.1, hi.2.1, hb.inSig⟩
              over := fun sch hsch ho => by
                rw [AggQueryIn.overSchema_allRegOf]
                exact hb.over sch hsch ho
              names := fun x hx => by
                rw [AggQueryIn.names_allRegOf] at hx
                exact hb.names x hx
              nom := fun s hs hn => by
                rw [AggQueryIn.noMention_allRegOf]
                exact hb.nom s hs hn }
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
  | GammaNest is his pc fn q ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2 hw f hf hfr sch hsch ho hfrag
    obtain ⟨q', hb, he⟩ := hc rfl
    refine ⟨fun _ => ⟨(AggQueryIn.GammaNest is (fun k hc => ColKind.noConfusion hc)
        pc.toReg fn q').allRegOf, ?_, fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    · exact { usesOnly := by
                rw [AggQueryIn.usesOnly_allRegOf]
                exact ⟨⟨hgamma, by rw [show (pc.toReg).sourceCol = true from by
                  cases pc <;> rfl]⟩, hb.usesOnly⟩
              hygienic := by
                rw [AggQueryIn.hygienic_allRegOf]
                exact hb.hygienic
              inSig := by
                rw [AggQueryIn.inSig_allRegOf]
                exact ⟨ProjColIn.noFun_toReg hq.1.2 hi.1, hi.2.1, hb.inSig⟩
              over := fun sch hsch ho => by
                rw [AggQueryIn.overSchema_allRegOf]
                exact hb.over sch hsch ho
              names := fun x hx => by
                rw [AggQueryIn.names_allRegOf] at hx
                exact hb.names x hx
              nom := fun s hs hn => by
                rw [AggQueryIn.noMention_allRegOf]
                exact hb.nom s hs hn }
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
      refine Multiset.map_congr rfl (fun g _ => ?_)
      funext j
      refine Fin.addCases (fun k => ?_) (fun z => ?_) j
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        refine congrArg fn (Multiset.map_congr rfl (fun u _ => ?_))
        exact (ProjColIn.evalPlain_toReg pc hq.1.2 u γ).symm
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | @Win cw nw _mw _pw _κw P' O o w t fw q hrr dist keep ih =>
    intro hq hr hi hw f hf hfr sch hsch ho hfrag
    by_cases hwin : OpKind.win ∈ S
    · -- the target keeps windows: the window over the re-typed child, through the doubling
      obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2.2 (Or.inl hwin) f hf hfr sch hsch ho hfrag
      obtain ⟨q', hb, he⟩ := hc rfl
      refine ⟨fun _ => ⟨(winKept P' O o w t fw _κw q' dist keep).allRegOf, ?_,
          fun D γ hset => ?_⟩,
        fun _ _ hl _ => absurd hl (by simp)⟩
      · exact { usesOnly := by
                  rw [AggQueryIn.usesOnly_allRegOf]
                  exact usesOnly_winKept P' O o w t fw _κw q' dist keep hwin hproj hb.usesOnly
                hygienic := by
                  rw [AggQueryIn.hygienic_allRegOf]
                  exact hygienic_winKept P' O o w t fw _κw q' dist keep hb.hygienic
                inSig := by
                  rw [AggQueryIn.inSig_allRegOf]
                  exact inSig_winKept P' O o w t fw _κw q' dist keep hi.1 hi.2.1 hi.2.2.1 hb.inSig
                over := fun sch hsch ho => by
                  rw [AggQueryIn.overSchema_allRegOf]
                  exact overSchema_winKept P' O o w t fw _κw q' dist keep (hb.over sch hsch ho)
                names := fun x hx => by
                  rw [AggQueryIn.names_allRegOf, names_winKept] at hx
                  exact hb.names x hx
                nom := fun s hs hn => by
                  rw [AggQueryIn.noMention_allRegOf]
                  exact noMention_winKept P' O o w t fw _κw q' dist keep s (hb.nom s hs hn) }
      · obtain ⟨hs', he'⟩ := he D γ hset
        refine ⟨by rw [AggQueryIn.settlesAt_allRegOf]
                   exact settlesAt_winKept P' O o w t fw _κw q' dist keep D γ hs', ?_⟩
        rw [AggQueryIn.evaluatePlain_allRegOf,
          evaluatePlain_winKept P' O o w t fw q hrr q' dist keep D γ he']
    obtain ⟨hreg, hcs, hd'⟩ := hw.resolve_left hwin
    obtain ⟨hc, -⟩ := ih hq.2 hr hi.2.2.2 (Or.inr hd') f hf hfr sch hsch ho hfrag
    obtain ⟨q', hb, he⟩ := hc rfl
    have hκ := funext hreg
    subst hκ
    obtain ⟨ψ, hψn, hψ⟩ := ValueFrame.exists_framePred (T := T) (n := nw) (c := cw) O w keep
    have hfΘ : (if dist then fw.distinct else fw) ∈ Θ := by
      cases dist
      · exact hi.2.1
      · exact hi.2.1
    refine ⟨fun _ => ⟨(winByApply P' O o ψ t (if dist then fw.distinct else fw) q').allRegOf, ?_,
      fun D γ hset => ?_⟩, fun _ _ hl _ => absurd hl (by simp)⟩
    · exact { usesOnly := by
                rw [AggQueryIn.usesOnly_allRegOf]
                exact usesOnly_winByApply P' O o ψ t _ happly hgamma hsel hb.usesOnly
              hygienic := by
                rw [AggQueryIn.hygienic_allRegOf, hygienic_winByApply]
                exact hb.hygienic
              inSig := by
                rw [AggQueryIn.inSig_allRegOf]
                exact inSig_winByApply P' O o ψ t _ q' hfΘ hi.1 (hψn hi.2.2.1) hb.inSig
              over := fun sch hsch ho => by
                rw [AggQueryIn.overSchema_allRegOf]
                exact overSchema_winByApply P' O o ψ t _ (hb.over sch hsch ho)
              names := fun x hx => by
                rw [AggQueryIn.names_allRegOf, names_winByApply] at hx
                exact hb.names x hx
              nom := fun s hs hn => by
                rw [AggQueryIn.noMention_allRegOf, noMention_winByApply]
                exact hb.nom s hs hn }
    · obtain ⟨hs', he'⟩ := he D γ hset
      refine ⟨by rw [AggQueryIn.settlesAt_allRegOf, settlesAt_winByApply]; exact hs', ?_⟩
      rw [AggQueryIn.evaluatePlain_allRegOf]
      refine Eq.trans ?_
        (evaluatePlain_winByApplyOf P' O o hcs ψ t fw dist keep hψ q' D γ).symm
      simp only [AggQueryIn.evaluatePlain]
      rw [he']
      rfl
  | WinExpr P' O o ws ts fs g q keeps ih => exact fun _ _ hi _ => hi.elim

end AggQueryIn

/-- The seven classes with the windows. -/
def basisRecWinOps : Set OpKind := insert OpKind.win basisRecOps

theorem sumMuOps_subset_basisRecWinOps : AggQueryIn.sumMuOps ⊆ basisRecWinOps :=
  fun _ hx => Set.mem_insert_of_mem _ (sumMuOps_subset_basisRecOps hx)

theorem union_notMem_basisRecWinOps : OpKind.union ∉ basisRecWinOps := by
  simp [basisRecWinOps, basisRecOps, AggQueryIn.sumMuOps]

/-- **A generating set of the whole algebra in the minimal universe**
(the positive half the recursion rows of `tab:basisclasses` were
missing): over a schema declaring finitely many names, the classes
`basisRecWinOps` – `∅`, `Π`, `σ`, the apply, `γ`, `win`, `μ^⊎` and
`μ^∪` – generate the whole algebra in the signature `𝒜(∅, {count})`, for
a counting aggregate. Duplicate elimination and the difference go by
`prop:collapse`, products by the apply, unions by the bag recursion
(`Provenance.SumByMu`), every column is read as a value, and a window
stays a window, over the doubled input (`Provenance.WinKept`). With the
necessity rows, a basis of the whole algebra in that universe is `∅`,
`Π`, `γ`, `μ^⊎`, one of `σ` and `−`, one of `×` and the apply, `win` (the
`win` row, not formalized) and possibly `μ^∪`. -/
theorem generatesOnRec_basisRecWinOps (sch : Schema) (hfin : {s | sch s ≠ none}.Finite)
    (cnt : SeqAggFunc T) (hcc : SeqAggFunc.Counts cnt) :
    GeneratesOnRec T sch cnt basisRecWinOps := by
  intro n κ q ho hq hi
  have hr : q.hygienic := q.hygienic_of_overSchema _ ho
  obtain ⟨f, hf, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch hfin q.names
  have hmus : OpKind.muSet ∈ basisRecWinOps := by
    simp [basisRecWinOps, basisRecOps, AggQueryIn.sumMuOps]
  have hwin : OpKind.win ∈ basisRecWinOps := Set.mem_insert _ _
  obtain ⟨q', hb, he⟩ := (AggQueryIn.exists_basisRec_aux sumMuOps_subset_basisRecWinOps
    union_notMem_basisRecWinOps (Or.inl hmus) cnt (Set.mem_singleton cnt) hcc q
    hq hr hi (Or.inl hwin) f hf hfr sch hfsch ho (Or.inl hmus)).1 rfl
  exact ⟨q', hb.over sch hfsch ho, hb.usesOnly, hb.inSig, fun D γ hs => he D γ hs⟩

/-- **Without the window class, for the windows `prop:winderived`
reaches**: every query whose windows contain their current row and read
all-regular inputs (`AggQueryIn.WinsDerivable`) is matched over the
seven classes `basisRecOps`, defined and equal wherever it is. The
hypothesis is the fragment's and not the predicate's: the `win` row of
`tab:basisclasses` says the other windows are not derivable in the
minimal signature. -/
theorem generatesOnRec_basisRecOps_of_winsDerivable (sch : Schema)
    (hfin : {s | sch s ≠ none}.Finite) (cnt : SeqAggFunc T) (hcc : SeqAggFunc.Counts cnt)
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ) (ho : q.overSchema sch)
    (hq : q.usesOnly plainRecOps) (hr : q.hygienic) (hi : q.inMinimalSig cnt)
    (hw : q.WinsDerivable) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.overSchema sch ∧ q'.usesOnly basisRecOps ∧ q'.hygienic
        ∧ q'.inMinimalSig cnt
        ∧ ∀ (D : Database T) (γ : Fin 0 → T), q.SettlesAt D γ →
          q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  obtain ⟨f, hf, hfsch, hfr⟩ := AggQueryIn.exists_freshSupply sch hfin q.names
  have hmus : OpKind.muSet ∈ basisRecOps := by simp [basisRecOps, AggQueryIn.sumMuOps]
  obtain ⟨q', hb, he⟩ := (AggQueryIn.exists_basisRec_aux sumMuOps_subset_basisRecOps
    union_notMem_basisRecOps (Or.inl hmus) cnt (Set.mem_singleton cnt) hcc q
    hq hr hi (Or.inr hw) f hf hfr sch hfsch ho (Or.inl hmus)).1 rfl
  exact ⟨q', hb.over sch hfsch ho, hb.usesOnly, hb.hygienic, hb.inSig,
    fun D γ hs => he D γ hs⟩
