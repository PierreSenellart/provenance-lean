import Provenance.AnnotatedDedup
import Provenance.MuUnion
import Provenance.AggQueryProbability

/-!
# The product from the apply, annotated

`q₁ × q₂` is the apply of `q₁` with `q₂` read under the ambient context
only, in every semiring: both build the row `(u, v)` annotated
`α_u ⊗ β_v` (`evaluate_prodApply`). Since an apply's left side may carry
aggregate columns, so may the factors, and nothing re-types a token.

In a recursive term whose hole is in the *right* factor the apply cannot
take that factor as its right side, which must be closed, so the two
factors are swapped and the columns put back by a projection
(`prodSwapAnn`). A projection cashes the pending group factors of the
groups whose tokens it does not keep, so the rows it builds differ from
the product's in how their annotation is split between the concrete part
and the pending factors – never in what the annotation finalizes to. What
is preserved is therefore agreement up to finalization (`AggQueryIn.FinEq`):
the same columns, tokens included, and the same finalized annotations,
which every operator respects (the selection on an aggregate value through
`GenAnn.finalize_sel`, its superseded factors being absorbed by the
comparison) and which is all the annotated evaluation reads.

`prodFree` replaces each product, and `generatesAnn_dedupProdFree` says
the classes other than `ε` and `×` generate the annotated algebra.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-! ## Agreement up to finalization -/

/-- **Two queries agree up to finalization**: on every instance and in
every context, the same rows with the same columns and the same finalized
annotations. -/
def AggQueryIn.FinEq {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) (q' : AggQueryIn T c n κ l') : Prop :=
  ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T),
    (q.evaluate d γ).map GenRow.fin = (q'.evaluate d γ).map GenRow.fin

namespace AggQueryIn.FinEq

variable {c n : ℕ} {κ : Fin n → ColKind} {l l' l'' : List (String × ℕ)}

theorem refl (q : AggQueryIn T c n κ l) : AggQueryIn.FinEq (K := K) q q := fun _ _ => rfl

theorem symm {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (h : AggQueryIn.FinEq (K := K) q q') : AggQueryIn.FinEq (K := K) q' q :=
  fun d γ => (h d γ).symm

theorem trans {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    {q'' : AggQueryIn T c n κ l''} (h : AggQueryIn.FinEq (K := K) q q')
    (h' : AggQueryIn.FinEq (K := K) q' q'') : AggQueryIn.FinEq (K := K) q q'' :=
  fun d γ => (h d γ).trans (h' d γ)

theorem of_eq {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (h : ∀ d γ, q.evaluate (K := K) d γ = q'.evaluate d γ) : AggQueryIn.FinEq (K := K) q q' :=
  fun d γ => by rw [h d γ]

/-- What the annotated reading reads of a row is determined by its
finalization. -/
theorem toAnnotated {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (h : AggQueryIn.FinEq (K := K) q q') (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    (q.evaluate d γ).map GenRow.toAnnotated = (q'.evaluate d γ).map GenRow.toAnnotated :=
  Multiset.map_eq_of_factor (f := GenRow.fin) (fun a b hab => by
    obtain ⟨h₁, h₂⟩ := GenRow.fin_eq_iff.mp hab
    unfold GenRow.toAnnotated
    rw [h₁, h₂]) (h d γ)

theorem evaluateAnnotated {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (h : AggQueryIn.FinEq (K := K) q q') (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    q.evaluateAnnotated d γ = q'.evaluateAnnotated d γ :=
  h.toAnnotated d γ

theorem readAnnotated (κ' : Fin n → ColKind) {q : AggQueryIn T c n κ l}
    {q' : AggQueryIn T c n κ l'}
    (h : AggQueryIn.FinEq (K := K) q q') (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    (q.evaluate d γ).map (GenRow.readAnnotated κ') =
      (q'.evaluate d γ).map (GenRow.readAnnotated κ') :=
  Multiset.map_eq_of_factor (f := GenRow.fin) (fun a b hab => by
    obtain ⟨h₁, h₂⟩ := GenRow.fin_eq_iff.mp hab
    unfold GenRow.readAnnotated
    rw [h₁, h₂]) (h d γ)

end AggQueryIn.FinEq

/-! ## Every operator respects it -/

omit [ValueType T] [HasAltLinearOrder K] in
/-- A projection cashes the pending factors it does not keep, which leaves
the finalized annotation alone. -/
theorem GenAnn.finalize_cash' (g : GenAnn K) (N : Multiset (List K)) (hN : N ≤ g.pending) :
    (⟨g.base * ((g.pending - N).map (fun l => SemiringWithMonus.delta l.sum)).prod, N⟩
      : GenAnn K).finalize = g.finalize := by
  unfold GenAnn.finalize
  conv_rhs => rw [← Multiset.sub_add_cancel hN]
  rw [Multiset.map_add, Multiset.prod_add, mul_assoc]

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenAnn.finalize_mul_base (g : GenAnn K) (x : K) :
    (⟨g.base * x, g.pending⟩ : GenAnn K).finalize = g.finalize * x := by
  unfold GenAnn.finalize
  exact mul_right_comm _ _ _

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
theorem GenAnn.finalize_mul' (a₁ a₂ : GenAnn K) :
    (GenAnn.mk (a₁.base * a₂.base) (a₁.pending + a₂.pending)).finalize
      = a₁.finalize * a₂.finalize := by
  unfold GenAnn.finalize
  rw [Multiset.map_add, Multiset.prod_add]
  exact mul_mul_mul_comm _ _ _ _

private theorem product_map_fin {α β γ δ : Type*} (f : α → γ) (g : β → δ)
    (A : Multiset α) (B : Multiset β) :
    (A.map f).product (B.map g) = (A.product B).map (fun p => (f p.1, g p.2)) := by
  unfold Multiset.product
  rw [Multiset.bind_map, Multiset.map_bind]
  refine Multiset.bind_congr (fun a _ => ?_)
  rw [Multiset.map_map, Multiset.map_map]
  rfl

namespace AggQueryIn.FinEq

theorem proj {c n m : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (ps : Tuple (ProjColIn T c κ) m) {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Proj ps q) (AggQueryIn.Proj ps q') := by
  intro d γ
  simp only [AggQueryIn.evaluate, Multiset.map_map]
  refine Multiset.map_eq_of_factor (f := GenRow.fin) (fun a b hab => ?_) (h d γ)
  obtain ⟨h₁, h₂⟩ := GenRow.fin_eq_iff.mp hab
  simp only [Function.comp, GenRow.fin]
  rw [GenAnn.finalize_cash' _ _ Multiset.inter_le_left,
    GenAnn.finalize_cash' _ _ Multiset.inter_le_left, h₁, h₂]

theorem sel {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (φ : GenPredIn T c κ) {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (hφ : SelOK l φ) (hφ' : SelOK l' φ) (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Sel φ q hφ) (AggQueryIn.Sel φ q' hφ') := by
  intro d γ
  simp only [AggQueryIn.evaluate]
  by_cases hagg : φ.hasAggAtom
  · rw [ite_eq_left hagg, ite_eq_left hagg, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_eq_of_factor (f := GenRow.fin) (fun a b hab => ?_) (h d γ)
    obtain ⟨h₁, h₂⟩ := GenRow.fin_eq_iff.mp hab
    simp only [Function.comp, GenRow.fin]
    refine Prod.ext h₁ ?_
    -- the comparison multiplies the finalized annotation, the superseded
    -- factors being absorbed
    rw [GenAnn.finalize_sel φ a.1 a.2.base a.2.pending _ _ (fun k hk x hx => ?_)
        (fun k hk x hx hs => ?_),
      GenAnn.finalize_sel φ b.1 b.2.base b.2.pending _ _ (fun k hk x hx => ?_)
        (fun k hk x hx hs => ?_), h₁]
    · exact congrArg (φ.predsem false b.1 γ * ·) h₂
    all_goals exact (Multiset.mem_filterMap _ _).mpr ⟨_, hk, by simp_all⟩
  · rw [ite_eq_right hagg, ite_eq_right hagg]
    have hF : ∀ R : Multiset (GenRow T K n),
        (R.filter (fun r => φ.holds r.fst γ)).map GenRow.fin
          = (R.map GenRow.fin).filter (fun x => φ.holds x.1 γ) := fun R => by
      rw [Multiset.filter_map]
      rfl
    rw [hF, hF, h d γ]

theorem prod {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₂ l₁' l₂' : List (String × ℕ)}
    {q₁ : AggQueryIn T c n₁ κ₁ l₁} {q₁' : AggQueryIn T c n₁ κ₁ l₁'}
    {q₂ : AggQueryIn T c n₂ κ₂ l₂} {q₂' : AggQueryIn T c n₂ κ₂ l₂'}
    (h₁ : AggQueryIn.FinEq (K := K) q₁ q₁') (h₂ : AggQueryIn.FinEq (K := K) q₂ q₂') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Prod q₁ q₂) (AggQueryIn.Prod q₁' q₂') := by
  intro d γ
  simp only [AggQueryIn.evaluate, Multiset.map_map]
  have hP : ((q₁.evaluate d γ).product (q₂.evaluate d γ)).map (fun p => (p.1.fin, p.2.fin))
      = ((q₁'.evaluate d γ).product (q₂'.evaluate d γ)).map (fun p => (p.1.fin, p.2.fin)) := by
    rw [← product_map_fin, ← product_map_fin, h₁ d γ, h₂ d γ]
  refine Multiset.map_eq_of_factor (fun a b hab => ?_) hP
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  obtain ⟨ha₁, ha₂⟩ := Prod.ext_iff.mp hab
  obtain ⟨h11, h12⟩ := GenRow.fin_eq_iff.mp ha₁
  obtain ⟨h21, h22⟩ := GenRow.fin_eq_iff.mp ha₂
  simp only [Function.comp, GenRow.fin]
  rw [GenAnn.finalize_mul', GenAnn.finalize_mul']
  simp only at h11 h12 h21 h22
  rw [h11, h12, h21, h22]

theorem apply {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₁' : List (String × ℕ)}
    {q₁ : AggQueryIn T c n₁ κ₁ l₁} {q₁' : AggQueryIn T c n₁ κ₁ l₁'}
    {q₂ q₂' : AggQueryIn T (n₁ + c) n₂ κ₂}
    (h₁ : AggQueryIn.FinEq (K := K) q₁ q₁') (h₂ : AggQueryIn.FinEq (K := K) q₂ q₂') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Apply q₁ q₂) (AggQueryIn.Apply q₁' q₂') := by
  intro d γ
  simp only [AggQueryIn.evaluate, Multiset.map_bind]
  refine (Multiset.bind_congr (fun x _ => ?_)).trans
    (Multiset.bind_eq_of_factor (f := GenRow.fin) (fun a b hab => ?_) (h₁ d γ))
  · rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_eq_of_factor (f := GenRow.fin) (fun y y' hy => ?_) (h₂ d _)
    obtain ⟨h1, h2⟩ := GenRow.fin_eq_iff.mp hy
    simp only [Function.comp, GenRow.fin]
    rw [GenAnn.finalize_mul', GenAnn.finalize_mul', h1, h2]
  · obtain ⟨h1, h2⟩ := GenRow.fin_eq_iff.mp hab
    simp only [Multiset.map_map]
    rw [h1]
    refine Multiset.map_congr rfl (fun y _ => ?_)
    simp only [Function.comp, GenRow.fin]
    rw [GenAnn.finalize_mul', GenAnn.finalize_mul', h2]

theorem sum {c n : ℕ} {κ : Fin n → ColKind} {l₁ l₂ l₁' l₂' : List (String × ℕ)}
    {q₁ : AggQueryIn T c n κ l₁} {q₁' : AggQueryIn T c n κ l₁'}
    {q₂ : AggQueryIn T c n κ l₂} {q₂' : AggQueryIn T c n κ l₂'}
    (h₁ : AggQueryIn.FinEq (K := K) q₁ q₁') (h₂ : AggQueryIn.FinEq (K := K) q₂ q₂') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Sum q₁ q₂) (AggQueryIn.Sum q₁' q₂') := by
  intro d γ
  simp only [AggQueryIn.evaluate]
  rw [Multiset.map_add, Multiset.map_add, h₁ d γ, h₂ d γ]

theorem dedup {c n : ℕ} {q q' : AggQueryIn T c n (ColKind.allReg n)}
    (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Dedup q) (AggQueryIn.Dedup q') :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h.toAnnotated d γ]

theorem diff {c n : ℕ} {q₁ q₁' q₂ q₂' : AggQueryIn T c n (ColKind.allReg n)}
    (h₁ : AggQueryIn.FinEq (K := K) q₁ q₁') (h₂ : AggQueryIn.FinEq (K := K) q₂ q₂') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Diff q₁ q₂) (AggQueryIn.Diff q₁' q₂') :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h₁.toAnnotated d γ, h₂.toAnnotated d γ]

theorem explode {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)} (k : Fin n)
    (hk : κ k = ColKind.agg) {q : AggQueryIn T c n κ l} {q' : AggQueryIn T c n κ l'}
    (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Explode k hk q) (AggQueryIn.Explode k hk q') := by
  intro d γ
  simp only [AggQueryIn.evaluate, Multiset.map_bind]
  refine Multiset.bind_eq_of_factor (f := GenRow.fin) (fun a b hab => ?_) (h d γ)
  obtain ⟨h1, h2⟩ := GenRow.fin_eq_iff.mp hab
  unfold GenRow.alternativesAt
  rw [h1]
  split
  · rw [Multiset.map_singleton, Multiset.map_singleton, hab]
  · rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun v _ => ?_)
    simp only [Function.comp, GenRow.fin]
    rw [GenAnn.finalize_mul_base, GenAnn.finalize_mul_base, h2]

theorem retag {c n : ℕ} {κ κ' : Fin n → ColKind} {l l' : List (String × ℕ)}
    (hk : ∀ k, (κ k).base = (κ' k).base) {q : AggQueryIn T c n κ l}
    {q' : AggQueryIn T c n κ l'} (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Retag hk q) (AggQueryIn.Retag hk q') := by
  intro d γ
  simp only [AggQueryIn.evaluate]
  exact h d γ

theorem mu {c n : ℕ} (s : String) {q₀ q₀' : AggQueryIn T c n (ColKind.allReg n)}
    {q₁ q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)]}
    (h₀ : AggQueryIn.FinEq (K := K) q₀ q₀') (h₁ : AggQueryIn.FinEq (K := K) q₁ q₁') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Mu s q₀ q₁) (AggQueryIn.Mu s q₀' q₁') :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h₀.toAnnotated, h₁.toAnnotated]

theorem muSet {c n : ℕ} (s : String) {q₀ q₀' : AggQueryIn T c n (ColKind.allReg n)}
    {q₁ q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)]}
    (h₀ : AggQueryIn.FinEq (K := K) q₀ q₀') (h₁ : AggQueryIn.FinEq (K := K) q₁ q₁') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.MuSet s q₀ q₁) (AggQueryIn.MuSet s q₀' q₁') :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h₀.toAnnotated, h₁.toAnnotated]

theorem gamma {c m n₁ n₂ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (TermIn T c m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (keep : Fin n₂ → Option (Selection T m))
    (ord : GroupOrder T m) {q q' : AggQueryIn T c m (ColKind.allReg m)}
    (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Gamma is ts fs q keep ord)
      (AggQueryIn.Gamma is ts fs q' keep ord) :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h.toAnnotated d γ]

theorem gammaScalar {c m n₂ : ℕ} (ts : Tuple (TermIn T c m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (ord : GroupOrder T m)
    {q q' : AggQueryIn T c m (ColKind.allReg m)} (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.GammaScalar ts fs q ord)
      (AggQueryIn.GammaScalar ts fs q' ord) :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h.toAnnotated d γ]

theorem provSum {c m n₁ : ℕ} {κ : Fin m → ColKind} (is : Tuple (Fin m) n₁)
    (his : ∀ k, κ (is k) ≠ ColKind.agg) (t : TermGIn T c κ) {q q' : AggQueryIn T c m κ}
    (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.ProvSum is his t q) (AggQueryIn.ProvSum is his t q') :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h.toAnnotated d γ]

theorem gammaTok {c m n₁ n₂ : ℕ} {κ : Fin m → ColKind} (is : Tuple (Fin m) n₁)
    (his : ∀ k, κ (is k) ≠ ColKind.agg) (ts : Tuple (TermIn T c m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (a : TermGIn T c κ)
    (keep : Fin n₂ → Option (Selection T m)) {q q' : AggQueryIn T c m κ}
    (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.GammaTok is his ts fs a q keep)
      (AggQueryIn.GammaTok is his ts fs a q' keep) :=
  of_eq fun d γ => by simp only [AggQueryIn.evaluate, h.toAnnotated d γ]

theorem win {c n m p : ℕ} {κ : Fin n → ColKind} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    {q q' : AggQueryIn T c n κ} (hrr : WinReadsReg κ P O t) (dist : Bool)
    (keep : Option (Selection T n)) (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.Win P O o w t f q hrr dist keep)
      (AggQueryIn.Win P O o w t f q' hrr dist keep) := by
  intro d γ
  simp only [AggQueryIn.evaluate]
  rw [h.readAnnotated κ d γ, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_eq_of_factor (f := GenRow.fin) (fun a b hab => ?_) (h d γ)
  obtain ⟨h1, h2⟩ := GenRow.fin_eq_iff.mp hab
  simp only [Function.comp, GenRow.fin, ValueFrame.windowGenRow, GenRow.readAnnotated]
  rw [h1, h2]

theorem winExpr {c n m p qn : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (ws : Fin qn → ValueFrame T p) (ts : Fin qn → TermIn T c n) (fs : Fin qn → SeqAggFunc T)
    (g : (Fin qn → T) → T) (keeps : Fin qn → Option (Selection T n))
    {q q' : AggQueryIn T c n (ColKind.allReg n)} (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.WinExpr P O o ws ts fs g q keeps)
      (AggQueryIn.WinExpr P O o ws ts fs g q' keeps) :=
  of_eq fun d γ => by
    simp only [AggQueryIn.evaluate]
    rw [h.toAnnotated d γ]

theorem gammaNest {c m n₁ : ℕ} {κ : Fin m → ColKind} (is : Tuple (Fin m) n₁)
    (his : ∀ k, κ (is k) ≠ ColKind.agg) (p : ProjColIn T c κ) (f : Multiset T → T)
    {q q' : AggQueryIn T c m κ} (h : AggQueryIn.FinEq (K := K) q q') :
    AggQueryIn.FinEq (K := K) (AggQueryIn.GammaNest is his p f q)
      (AggQueryIn.GammaNest is his p f q') :=
  of_eq fun d γ => by
    simp only [AggQueryIn.evaluate]
    have hk : (q.evaluate d γ).map (fun row k => AggValue.collapseSum (row.1 (is k)))
        = (q'.evaluate d γ).map (fun row k => AggValue.collapseSum (row.1 (is k))) :=
      Multiset.map_eq_of_factor (fun a b hab => by rw [(GenRow.fin_eq_iff.mp hab).1]) (h d γ)
    have hU : ∀ g : Tuple T n₁,
        ((q.evaluate d γ).filter (fun x => (fun k => AggValue.collapseSum (x.1 (is k))) = g)).map
            (fun x => ((p.eval x.1 γ).innerValue, x.2.finalize))
          = ((q'.evaluate d γ).filter
              (fun x => (fun k => AggValue.collapseSum (x.1 (is k))) = g)).map
            (fun x => ((p.eval x.1 γ).innerValue, x.2.finalize)) := fun g =>
      Multiset.map_filter_eq_of_factor (f := GenRow.fin)
        (fun a b hab => by rw [(GenRow.fin_eq_iff.mp hab).1])
        (fun a b hab => by rw [(GenRow.fin_eq_iff.mp hab).1, (GenRow.fin_eq_iff.mp hab).2])
        (h d γ)
    rw [hk]
    simp only [hU]

end AggQueryIn.FinEq

/-! ## Substitution keeps the fences and the settling -/

theorem AggQueryIn.evaluateAnnotated_substMap {c n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ} (θ : Fin c → T ⊕ Fin d)
    (dB : AnnotatedDatabase T K) (γ : Fin d → T) :
    (q.substMap θ).evaluateAnnotated dB γ = q.evaluateAnnotated dB (substVal θ γ) := by
  unfold AggQueryIn.evaluateAnnotated
  rw [AggQueryIn.evaluate_substMap]

theorem AggQueryIn.muStep_substMap {c n : ℕ} (s : String)
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) {d : ℕ} (θ : Fin c → T ⊕ Fin d)
    (dB : AnnotatedDatabase T K) (γ : Fin d → T) :
    AggQueryIn.muStep s (q₁.substMap θ) dB γ = AggQueryIn.muStep s q₁ dB (substVal θ γ) := by
  funext X
  exact AggQueryIn.evaluateAnnotated_substMap q₁ θ _ γ

theorem AggQueryIn.muSetStep_substMap {c n : ℕ} (s : String)
    (q₀ : AggQueryIn T c n (ColKind.allReg n))
    (q₁ : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) {d : ℕ} (θ : Fin c → T ⊕ Fin d)
    (dB : AnnotatedDatabase T K) (γ : Fin d → T) :
    AggQueryIn.muSetStep s (q₀.substMap θ) (q₁.substMap θ) dB γ
      = AggQueryIn.muSetStep s q₀ q₁ dB (substVal θ γ) := by
  funext X
  unfold AggQueryIn.muSetStep
  rw [AggQueryIn.evaluateAnnotated_substMap, AggQueryIn.evaluateAnnotated_substMap]

theorem AggQueryIn.annSettlesAt_castKind {c n : ℕ} {κ κ' : Fin n → ColKind}
    {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l)
    (dB : AnnotatedDatabase T K) (γ : Fin c → T) :
    (q.castKind h).AnnSettlesAt dB γ ↔ q.AnnSettlesAt dB γ := by
  subst h; exact Iff.rfl

theorem AggQueryIn.annSettlesAt_castIdx {c n : ℕ} {κ : Fin n → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c n κ l)
    (dB : AnnotatedDatabase T K) (γ : Fin c → T) :
    (q.castIdx h).AnnSettlesAt dB γ ↔ q.AnnSettlesAt dB γ := by
  subst h; exact Iff.rfl

theorem AggQueryIn.evaluate_castIdx {c n : ℕ} {κ : Fin n → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c n κ l)
    (dB : AnnotatedDatabase T K) (γ : Fin c → T) :
    (q.castIdx h).evaluate dB γ = q.evaluate dB γ := by
  subst h; rfl

omit [ValueType T] in
theorem AggQueryIn.stripAgg_castIdx {c n : ℕ} {κ : Fin n → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c n κ l) :
    (q.castIdx h).stripAgg = q.stripAgg.castIdx h := by
  subst h; rfl

omit [ValueType T] in
theorem AggQueryIn.noExplode_castIdx {c n : ℕ} {κ : Fin n → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c n κ l) :
    (q.castIdx h).noExplode ↔ q.noExplode := by
  subst h; exact Iff.rfl

theorem AggQueryIn.noAggParam_castIdx {c n : ℕ} {κ : Fin n → ColKind}
    {l l' : List (String × ℕ)} (h : l = l') (q : AggQueryIn T c n κ l) :
    (q.castIdx h).noAggParam ↔ q.noAggParam := by
  subst h; exact Iff.rfl

/-- **A substituted query settles where the query does**, under the
valuation the substitution induces. -/
theorem AggQueryIn.annSettlesAt_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d) (dB : AnnotatedDatabase T K) (γ : Fin d → T),
      (q.substMap θ).AnnSettlesAt dB γ ↔ q.AnnSettlesAt dB (substVal θ γ) := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ dB γ => Iff.rfl
  | Hole n s => exact fun θ dB γ => Iff.rfl
  | Empty => exact fun θ dB γ => Iff.rfl
  | Proj ps q ih =>
    intro d θ dB γ
    rw [AggQueryIn.substMap, AggQueryIn.annSettlesAt_castKind]
    exact ih θ dB γ
  | Sel φ q _ ih => exact fun θ dB γ => ih θ dB γ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ dB γ => and_congr (ih₁ θ dB γ) (ih₂ θ dB γ)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d θ dB γ
    refine and_congr (ih₁ θ dB γ) (forall_congr' fun u => ?_)
    rw [AggQueryIn.evaluateAnnotated_substMap]
    exact imp_congr Iff.rfl (by rw [ih₂ _ dB (Fin.append u γ), substVal_append])
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ dB γ => and_congr (ih₁ θ dB γ) (ih₂ θ dB γ)
  | Dedup q ih => exact fun θ dB γ => ih θ dB γ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ dB γ => and_congr (ih₁ θ dB γ) (ih₂ θ dB γ)
  | Explode k hk q ih => exact fun θ dB γ => ih θ dB γ
  | Retag hk q ih => exact fun θ dB γ => ih θ dB γ
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.AnnSettlesAt, AggQueryIn.muStep_substMap,
      AggQueryIn.evaluateAnnotated_substMap, ih₀ θ, ih₁ θ]
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d θ dB γ
    rw [AggQueryIn.substMap]
    simp only [AggQueryIn.AnnSettlesAt, AggQueryIn.muSetStep_substMap, ih₀ θ, ih₁ θ]
  | Gamma is ts fs q keep ord ih => exact fun θ dB γ => ih θ dB γ
  | GammaScalar ts fs q ord ih => exact fun θ dB γ => ih θ dB γ
  | GammaNest is his p fn q ih => exact fun θ dB γ => ih θ dB γ
  | ProvSum is his t q ih => exact fun θ dB γ => ih θ dB γ
  | GammaTok is his ts fs a q keep ih => exact fun θ dB γ => ih θ dB γ
  | Win P O o w t fw q hrr dist keep ih => exact fun θ dB γ => ih θ dB γ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ dB γ => ih θ dB γ

omit [ValueType T] in
theorem AggQueryIn.noExplode_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), (q.substMap θ).noExplode ↔ q.noExplode := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ => Iff.rfl
  | Hole n s => exact fun θ => Iff.rfl
  | Empty => exact fun θ => Iff.rfl
  | Proj ps q ih =>
    intro d θ
    rw [AggQueryIn.substMap, AggQueryIn.noExplode_castKind]
    exact ih θ
  | Sel φ q _ ih => exact fun θ => ih θ
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ _)
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Dedup q ih => exact fun θ => ih θ
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ => and_congr (ih₁ θ) (ih₂ θ)
  | Explode k hk q ih => exact fun θ => Iff.rfl
  | Retag hk q ih => exact fun θ => ih θ
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun θ => and_congr (ih₀ θ) (ih₁ θ)
  | Gamma is ts fs q keep ord ih => exact fun θ => ih θ
  | GammaScalar ts fs q ord ih => exact fun θ => ih θ
  | GammaNest is his p fn q ih => exact fun θ => ih θ
  | ProvSum is his t q ih => exact fun θ => ih θ
  | GammaTok is his ts fs a q keep ih => exact fun θ => ih θ
  | Win P O o w t fw q hrr dist keep ih => exact fun θ => ih θ
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ => ih θ

omit [ValueType T] in
/-- Agreement away from the aggregate columns of an apply's left side
survives the shifted substitution an apply passes to its right side. -/
theorem AgreeReg.substVal_lift {c d n₁ : ℕ} {κ₁ : Fin n₁ → ColKind} (θ : Fin c → T ⊕ Fin d)
    {γ γ' : Fin (n₁ + d) → T} (h : AgreeReg κ₁ γ γ') :
    AgreeReg κ₁
      (substVal (Fin.append (fun k => Sum.inr (Fin.castAdd d k))
        (fun j => Sum.map id (Fin.natAdd n₁) (θ j))) γ)
      (substVal (Fin.append (fun k => Sum.inr (Fin.castAdd d k))
        (fun j => Sum.map id (Fin.natAdd n₁) (θ j))) γ') := by
  refine ⟨fun i hi => ?_, fun j => ?_⟩
  · show Sum.elim id γ (Fin.append _ _ (Fin.castAdd c i))
      = Sum.elim id γ' (Fin.append _ _ (Fin.castAdd c i))
    rw [Fin.append_left]
    exact h.1 i hi
  · show Sum.elim id γ (Fin.append _ _ (Fin.natAdd n₁ j))
      = Sum.elim id γ' (Fin.append _ _ (Fin.natAdd n₁ j))
    rw [Fin.append_right]
    cases θ j with
    | inl a => rfl
    | inr m => exact h.2 m

theorem AggQueryIn.ReadsRegParams.substMap_lift {c d n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {q₂ : AggQueryIn T (n₁ + c) n₂ κ₂} (θ : Fin c → T ⊕ Fin d)
    (h : AggQueryIn.ReadsRegParams κ₁ q₂) :
    AggQueryIn.ReadsRegParams κ₁ (q₂.substMap (Fin.append (fun k => Sum.inr (Fin.castAdd d k))
        (fun j => Sum.map id (Fin.natAdd n₁) (θ j)))) := by
  refine ⟨fun D γ γ' hγ => ?_, fun D γ γ' hγ => ?_, fun K' _ _ _ dB γ γ' hγ => ?_⟩
  · rw [AggQueryIn.evaluatePlain_substMap, AggQueryIn.evaluatePlain_substMap]
    exact h.1 D _ _ (hγ.substVal_lift θ)
  · rw [AggQueryIn.stripAgg_substMap, AggQueryIn.evaluatePlain_substMap,
      AggQueryIn.evaluatePlain_substMap]
    exact h.2.1 D _ _ (hγ.substVal_lift θ)
  · rw [AggQueryIn.evaluate_substMap, AggQueryIn.evaluate_substMap]
    exact h.2.2 K' dB _ _ (hγ.substVal_lift θ)

theorem AggQueryIn.noAggParam_substMap :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) {d : ℕ}
      (θ : Fin c → T ⊕ Fin d), q.noAggParam → (q.substMap θ).noAggParam := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun θ _ => trivial
  | Hole n s => exact fun θ _ => trivial
  | Empty => exact fun θ _ => trivial
  | Proj ps q ih =>
    intro d θ h
    rw [AggQueryIn.substMap, AggQueryIn.noAggParam_castKind]
    exact ih θ h
  | Sel φ q _ ih => exact fun θ h => ih θ h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun θ h => ⟨ih₁ θ h.1, ih₂ θ h.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun θ h => ⟨ih₁ θ h.1, ih₂ _ h.2.1, h.2.2.substMap_lift θ⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun θ h => ⟨ih₁ θ h.1, ih₂ θ h.2⟩
  | Dedup q ih => exact fun θ h => ih θ h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun θ h => ⟨ih₁ θ h.1, ih₂ θ h.2⟩
  | Explode k hk q ih => exact fun θ h => ih θ h
  | Retag hk q ih => exact fun θ h => ih θ h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun θ h => ⟨ih₀ θ h.1, ih₁ θ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun θ h => ⟨ih₀ θ h.1, ih₁ θ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun θ h => ih θ h
  | GammaScalar ts fs q ord ih => exact fun θ h => ih θ h
  | GammaNest is his p fn q ih => exact fun θ h => ih θ h
  | ProvSum is his t q ih => exact fun θ h => ih θ h
  | GammaTok is his ts fs a q keep ih => exact fun θ h => ih θ h
  | Win P O o w t fw q hrr dist keep ih => exact fun θ h => ih θ h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun θ h => ih θ h

/-! ## A column carried through, in any context -/

/-- A column carried through a projection whatever its kind – `carryCol`
in a context of any arity. -/
def carryColIn {c n : ℕ} (κ : Fin n → ColKind) (k : Fin n) : ProjColIn T c κ :=
  match h : κ k with
  | ColKind.reg => .term (TermGIn.index k h)
  | ColKind.agg => .token k h
  | ColKind.prov => .provTerm (TermGIn.provIndex k h)

omit [ValueType T] in
@[simp] theorem carryColIn_kind {c n : ℕ} (κ : Fin n → ColKind) (k : Fin n) :
    (carryColIn (T := T) (c := c) κ k).kind = κ k := by
  unfold carryColIn
  split
  · next h => exact h.symm
  · next h => exact h.symm
  · next h => exact h.symm

omit [ValueType T] in
@[simp] theorem carryColIn_sourceCol {c n : ℕ} (κ : Fin n → ColKind) (k : Fin n) :
    (carryColIn (T := T) (c := c) κ k).sourceCol = true := by
  unfold carryColIn
  split <;> rfl

omit [ValueType T] in
@[simp] theorem carryColIn_noFun {c n : ℕ} (κ : Fin n → ColKind) (k : Fin n) :
    (carryColIn (T := T) (c := c) κ k).noFun = true := by
  unfold carryColIn
  split <;> rfl

theorem evalPlain_carryColIn {c n : ℕ} (κ : Fin n → ColKind) (k : Fin n) (u : Tuple T n)
    (γ : Fin c → T) : (carryColIn κ k).evalPlain u γ = u k := by
  unfold carryColIn
  split <;> rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A column carried through reads the row's own value, on a row whose
values have the kinds the column says. -/
theorem eval_carryColIn {c n : ℕ} (κ : Fin n → ColKind) (k : Fin n)
    (u : Tuple (GenValue T K) n) (γ : Fin c → T) (hu : GenValue.kindOf (u k) = (κ k).base) :
    (carryColIn κ k).eval u γ = u k := by
  unfold carryColIn
  split
  · next h =>
    rw [h] at hu
    obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg hu
    show Sum.inl (AggValue.collapseSum (u k)) = u k
    rw [hw]
    rfl
  · rfl
  · next h =>
    rw [h] at hu
    obtain ⟨w, hw⟩ := GenValue.eq_inl_of_kindOf_reg hu
    show Sum.inl (AggValue.collapseSum (u k)) = u k
    rw [hw]
    rfl

/-! ## The product as an apply -/

omit [ValueType T] in
theorem swapCarry_kind {c n₁ n₂ : ℕ} (κ₁ : Fin n₁ → ColKind) (κ₂ : Fin n₂ → ColKind) :
    (fun j => (carryColIn (T := T) (c := c) (Fin.append κ₂ κ₁) (swapIdx n₁ n₂ j)).kind)
      = Fin.append κ₁ κ₂ :=
  funext fun j => by
    rw [carryColIn_kind]
    exact congrFun (swap_append (T := ColKind) κ₁ κ₂) j

/-- **The product written with an apply**: `q₁ ⊳ q₂` with `q₂` read under
the ambient context only. When the hole of a recursive term is in `q₂`,
which an apply's right side cannot hold, the factors are swapped and the
columns put back by a projection; a product with a hole on each side,
which no recursive term has, is left alone. -/
def prodAnn {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁)
    (q₂ : AggQueryIn T c n₂ κ₂ l₂) :
    AggQueryIn T c (n₁ + n₂) (Fin.append κ₁ κ₂) (l₁ ++ l₂) :=
  if h₂ : l₂ = [] then
    (AggQueryIn.Apply q₁ ((q₂.castIdx h₂).substMap (applyOuter T c n₁))).castIdx
      (by rw [h₂, List.append_nil])
  else if h₁ : l₁ = [] then
    ((AggQueryIn.Proj (fun j => carryColIn (Fin.append κ₂ κ₁) (swapIdx n₁ n₂ j))
        (AggQueryIn.Apply q₂ ((q₁.castIdx h₁).substMap (applyOuter T c n₂)))).castKind
      (swapCarry_kind κ₁ κ₂)).castIdx (by rw [h₁, List.nil_append])
  else AggQueryIn.Prod q₁ q₂

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem kindOf_append {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {u : Tuple (GenValue T K) n₁} {v : Tuple (GenValue T K) n₂}
    (hu : ∀ k, GenValue.kindOf (u k) = (κ₁ k).base)
    (hv : ∀ k, GenValue.kindOf (v k) = (κ₂ k).base) (k : Fin (n₁ + n₂)) :
    GenValue.kindOf ((Fin.append u v : Tuple (GenValue T K) (n₁ + n₂)) k)
      = (Fin.append κ₁ κ₂ k).base := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left, Fin.append_left]; exact hu i
  · rw [Fin.append_right, Fin.append_right]; exact hv i

/-- **The product is the apply of its left factor with its right factor
read under the ambient context**, exactly. -/
theorem evaluate_prodApply {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (q₂ : AggQueryIn T c n₂ κ₂)
    (dB : AnnotatedDatabase T K) (γ : Fin c → T) :
    (AggQueryIn.Apply q₁ (q₂.substMap (applyOuter T c n₁))).evaluate dB γ
      = (AggQueryIn.Prod q₁ q₂).evaluate dB γ := by
  simp only [AggQueryIn.evaluate]
  unfold Multiset.product
  rw [Multiset.map_bind]
  refine Multiset.bind_congr (fun x _ => ?_)
  rw [AggQueryIn.evaluate_substMap, substVal_applyOuter, Multiset.map_map]
  rfl

/-- **The product the other way round**, its columns put back: the same
rows with the same finalized annotations. -/
theorem finEq_prodSwap {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁) (q₂ : AggQueryIn T c n₂ κ₂ l₂) :
    AggQueryIn.FinEq (K := K)
      ((AggQueryIn.Proj (fun j => carryColIn (Fin.append κ₂ κ₁) (swapIdx n₁ n₂ j))
        (AggQueryIn.Apply q₂ (q₁.substMap (applyOuter T c n₂)))).castKind
          (swapCarry_kind κ₁ κ₂))
      (AggQueryIn.Prod q₁ q₂) := by
  intro dB γ
  rw [AggQueryIn.evaluate_castKind]
  simp only [AggQueryIn.evaluate, Multiset.map_map, Multiset.map_bind]
  unfold Multiset.product
  rw [Multiset.map_bind]
  simp only [AggQueryIn.evaluate_substMap, substVal_applyOuter, Multiset.map_map]
  rw [Multiset.bind_map_comm]
  refine Multiset.bind_congr (fun x hx => Multiset.map_congr rfl (fun y hy => ?_))
  simp only [Function.comp, GenRow.fin]
  refine Prod.ext (funext fun j => ?_) ?_
  · show (carryColIn (Fin.append κ₂ κ₁) (swapIdx n₁ n₂ j)).eval
        (Fin.append y.fst x.fst) γ = (Fin.append x.fst y.fst : Tuple (GenValue T K) _) j
    rw [eval_carryColIn _ _ _ _ (kindOf_append
        (fun k => AggQueryIn.evaluate_conform q₂ dB y hy k)
        (fun k => AggQueryIn.evaluate_conform q₁ dB x hx k) _)]
    exact congrFun (swap_append (T := GenValue T K) x.fst y.fst) j
  · show GenAnn.finalize _ = GenAnn.finalize _
    rw [GenAnn.finalize_cash _ _ _ Multiset.inter_le_left]
    show (GenAnn.mk (y.snd.base * x.snd.base) (y.snd.pending + x.snd.pending)).finalize
      = (GenAnn.mk (x.snd.base * y.snd.base) (x.snd.pending + y.snd.pending)).finalize
    rw [GenAnn.finalize_mul', GenAnn.finalize_mul', mul_comm]

theorem AggQueryIn.FinEq.castIdx {c n : ℕ} {κ : Fin n → ColKind} {l l' : List (String × ℕ)}
    (h : l = l') (q : AggQueryIn T c n κ l) :
    AggQueryIn.FinEq (K := K) (q.castIdx h) q :=
  AggQueryIn.FinEq.of_eq fun dB γ => AggQueryIn.evaluate_castIdx h q dB γ

/-- **The product as an apply agrees with the product** up to finalization,
exactly when no swap is needed. -/
theorem finEq_prodAnn {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (q₂ : AggQueryIn T c n₂ κ₂ l₂) :
    AggQueryIn.FinEq (K := K) (prodAnn q₁ q₂) (AggQueryIn.Prod q₁ q₂) := by
  unfold prodAnn
  split_ifs with h₂ h₁
  · refine ((AggQueryIn.FinEq.castIdx _ _).trans (AggQueryIn.FinEq.of_eq fun dB γ => ?_)).trans
      (AggQueryIn.FinEq.prod (AggQueryIn.FinEq.refl q₁) (AggQueryIn.FinEq.castIdx h₂ q₂))
    exact evaluate_prodApply q₁ (q₂.castIdx h₂) dB γ
  · exact ((AggQueryIn.FinEq.castIdx _ _).trans (finEq_prodSwap (q₁.castIdx h₁) q₂)).trans
      (AggQueryIn.FinEq.prod (AggQueryIn.FinEq.castIdx h₁ q₁) (AggQueryIn.FinEq.refl q₂))
  · exact AggQueryIn.FinEq.refl _

theorem evaluatePlain_prodApply {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (q₂ : AggQueryIn T c n₂ κ₂)
    (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.Apply q₁ (q₂.substMap (applyOuter T c n₁))).evaluatePlain D γ
      = (AggQueryIn.Prod q₁ q₂).evaluatePlain D γ := by
  show Multiset.bind (q₁.evaluatePlain D γ) (fun u =>
      Multiset.map _ ((q₂.substMap _).evaluatePlain D (Fin.append u γ)))
    = q₁.evaluatePlain D γ * q₂.evaluatePlain D γ
  rw [Relation.hMul_eq_bind]
  refine Multiset.bind_congr (fun u _ => ?_)
  rw [AggQueryIn.evaluatePlain_substMap, substVal_applyOuter]

/-- And so does it in the plain semantics, exactly. -/
theorem evaluatePlain_prodAnn {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (q₂ : AggQueryIn T c n₂ κ₂ l₂)
    (D : Database T) (γ : Fin c → T) :
    (prodAnn q₁ q₂).evaluatePlain D γ = (AggQueryIn.Prod q₁ q₂).evaluatePlain D γ := by
  unfold prodAnn
  split_ifs with h₂ h₁
  · rw [AggQueryIn.evaluatePlain_castIdx, evaluatePlain_prodApply]
    simp only [AggQueryIn.evaluatePlain, AggQueryIn.evaluatePlain_castIdx]
  · rw [AggQueryIn.evaluatePlain_castIdx, AggQueryIn.evaluatePlain_castKind]
    show Multiset.map (fun u => (fun j =>
        (carryColIn (Fin.append κ₂ κ₁) (swapIdx n₁ n₂ j)).evalPlain u γ))
      (Multiset.bind (q₂.evaluatePlain D γ) (fun v => Multiset.map
        (fun u => (Fin.append v u : Tuple T (n₂ + n₁)))
        (((q₁.castIdx h₁).substMap (applyOuter T c n₂)).evaluatePlain D (Fin.append v γ))))
      = q₁.evaluatePlain D γ * q₂.evaluatePlain D γ
    simp only [AggQueryIn.evaluatePlain_substMap, substVal_applyOuter,
      AggQueryIn.evaluatePlain_castIdx, Multiset.map_bind, Multiset.map_map,
      Relation.hMul_eq_bind]
    rw [Multiset.bind_map_comm]
    refine Multiset.bind_congr (fun u _ => Multiset.map_congr rfl (fun v _ => ?_))
    simp only [Function.comp, evalPlain_carryColIn]
    exact swap_append u v
  · rfl

omit [ValueType T] in
theorem stripAgg_prodAnn {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (q₂ : AggQueryIn T c n₂ κ₂ l₂) :
    (prodAnn q₁ q₂).stripAgg = prodAnn q₁.stripAgg q₂.stripAgg := by
  unfold prodAnn
  split_ifs with h₂ h₁
  · rw [AggQueryIn.stripAgg_castIdx, AggQueryIn.stripAgg, AggQueryIn.stripAgg_substMap,
      AggQueryIn.stripAgg_castIdx]
  · rw [AggQueryIn.stripAgg_castIdx, AggQueryIn.stripAgg_castKind, AggQueryIn.stripAgg,
      AggQueryIn.stripAgg, AggQueryIn.stripAgg_substMap, AggQueryIn.stripAgg_castIdx]
  · rfl

theorem annSettlesAt_prodAnn {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (q₂ : AggQueryIn T c n₂ κ₂ l₂)
    (dB : AnnotatedDatabase T K) (γ : Fin c → T) (h₁ : q₁.AnnSettlesAt dB γ)
    (h₂ : q₂.AnnSettlesAt dB γ) : (prodAnn q₁ q₂).AnnSettlesAt dB γ := by
  unfold prodAnn
  split_ifs with hl₂ hl₁
  · rw [AggQueryIn.annSettlesAt_castIdx]
    refine ⟨h₁, fun u _ => ?_⟩
    rw [AggQueryIn.annSettlesAt_substMap, substVal_applyOuter, AggQueryIn.annSettlesAt_castIdx]
    exact h₂
  · rw [AggQueryIn.annSettlesAt_castIdx, AggQueryIn.annSettlesAt_castKind]
    refine ⟨h₂, fun u _ => ?_⟩
    rw [AggQueryIn.annSettlesAt_substMap, substVal_applyOuter, AggQueryIn.annSettlesAt_castIdx]
    exact h₁
  · exact ⟨h₁, h₂⟩

omit [ValueType T] in
theorem usesOnly_prodAnn {S : Set OpKind} (hap : OpKind.apply ∈ S) (hpr : OpKind.proj ∈ S)
    {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁) (q₂ : AggQueryIn T c n₂ κ₂ l₂)
    (hlen : (l₁ ++ l₂).length ≤ 1) (h₁ : q₁.usesOnly S) (h₂ : q₂.usesOnly S) :
    (prodAnn q₁ q₂).usesOnly S := by
  unfold prodAnn
  split_ifs with hl₂ hl₁
  · rw [AggQueryIn.usesOnly_castIdx]
    exact ⟨hap, h₁, (AggQueryIn.usesOnly_substMap _ _).mpr
      ((AggQueryIn.usesOnly_castIdx _ _).mpr h₂)⟩
  · rw [AggQueryIn.usesOnly_castIdx, AggQueryIn.usesOnly_castKind]
    exact ⟨⟨hpr, fun j => carryColIn_sourceCol _ _⟩, hap, h₂,
      (AggQueryIn.usesOnly_substMap _ _).mpr ((AggQueryIn.usesOnly_castIdx _ _).mpr h₁)⟩
  · exfalso
    have h₁' := List.length_pos_of_ne_nil hl₁
    have h₂' := List.length_pos_of_ne_nil hl₂
    rw [List.length_append] at hlen
    omega

theorem inSig_prodAnn {Θ : Set (SeqAggFunc T)} {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁)
    (q₂ : AggQueryIn T c n₂ κ₂ l₂) (h₁ : q₁.inSig Θ) (h₂ : q₂.inSig Θ) :
    (prodAnn q₁ q₂).inSig Θ := by
  unfold prodAnn
  split_ifs with hl₂ hl₁
  · rw [AggQueryIn.inSig_castIdx]
    exact ⟨h₁, (AggQueryIn.inSig_substMap _ _).mpr ((AggQueryIn.inSig_castIdx _ _).mpr h₂)⟩
  · rw [AggQueryIn.inSig_castIdx, AggQueryIn.inSig_castKind]
    exact ⟨fun j => carryColIn_noFun _ _, h₂,
      (AggQueryIn.inSig_substMap _ _).mpr ((AggQueryIn.inSig_castIdx _ _).mpr h₁)⟩
  · exact ⟨h₁, h₂⟩

omit [ValueType T] in
theorem overSchema_prodAnn {sch : Schema} {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁)
    (q₂ : AggQueryIn T c n₂ κ₂ l₂) (h₁ : q₁.overSchema sch) (h₂ : q₂.overSchema sch) :
    (prodAnn q₁ q₂).overSchema sch := by
  unfold prodAnn
  split_ifs with hl₂ hl₁
  · rw [AggQueryIn.overSchema_castIdx]
    exact ⟨h₁, (AggQueryIn.overSchema_substMap _ _ _).mpr
      ((AggQueryIn.overSchema_castIdx _ _).mpr h₂)⟩
  · rw [AggQueryIn.overSchema_castIdx, AggQueryIn.overSchema_castKind]
    exact ⟨h₂, (AggQueryIn.overSchema_substMap _ _ _).mpr
      ((AggQueryIn.overSchema_castIdx _ _).mpr h₁)⟩
  · exact ⟨h₁, h₂⟩

omit [ValueType T] in
theorem noExplode_prodAnn {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁)
    (q₂ : AggQueryIn T c n₂ κ₂ l₂) (h₁ : q₁.noExplode) (h₂ : q₂.noExplode) :
    (prodAnn q₁ q₂).noExplode := by
  unfold prodAnn
  split_ifs with hl₂ hl₁
  · rw [AggQueryIn.noExplode_castIdx]
    exact ⟨h₁, (AggQueryIn.noExplode_substMap _ _).mpr
      ((AggQueryIn.noExplode_castIdx _ _).mpr h₂)⟩
  · rw [AggQueryIn.noExplode_castIdx, AggQueryIn.noExplode_castKind]
    exact ⟨h₂, (AggQueryIn.noExplode_substMap _ _).mpr
      ((AggQueryIn.noExplode_castIdx _ _).mpr h₁)⟩
  · exact ⟨h₁, h₂⟩

theorem noAggParam_prodAnn {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁)
    (q₂ : AggQueryIn T c n₂ κ₂ l₂) (h₁ : q₁.noAggParam) (h₂ : q₂.noAggParam) :
    (prodAnn q₁ q₂).noAggParam := by
  unfold prodAnn
  split_ifs with hl₂ hl₁
  · rw [AggQueryIn.noAggParam_castIdx]
    exact ⟨h₁, AggQueryIn.noAggParam_substMap _ _ ((AggQueryIn.noAggParam_castIdx _ _).mpr h₂),
      AggQueryIn.readsRegParams_applyOuter _⟩
  · rw [AggQueryIn.noAggParam_castIdx, AggQueryIn.noAggParam_castKind]
    exact ⟨h₂, AggQueryIn.noAggParam_substMap _ _ ((AggQueryIn.noAggParam_castIdx _ _).mpr h₁),
      AggQueryIn.readsRegParams_applyOuter _⟩
  · exact ⟨h₁, h₂⟩

/-! ## The pass -/

/-- Every product replaced by its apply form. -/
def prodFree : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → AggQueryIn T c n κ l
  | _, _, _, _, .Rel n s => .Rel n s
  | _, _, _, _, .Hole n s => .Hole n s
  | _, _, _, _, .Empty => .Empty
  | _, _, _, _, .Proj ps q => .Proj ps (prodFree q)
  | _, _, _, _, .Sel φ q hφ => .Sel φ (prodFree q) hφ
  | _, _, _, _, .Prod q₁ q₂ => prodAnn (prodFree q₁) (prodFree q₂)
  | _, _, _, _, .Apply q₁ q₂ => .Apply (prodFree q₁) (prodFree q₂)
  | _, _, _, _, .Sum q₁ q₂ => .Sum (prodFree q₁) (prodFree q₂)
  | _, _, _, _, .Dedup q => .Dedup (prodFree q)
  | _, _, _, _, .Diff q₁ q₂ => .Diff (prodFree q₁) (prodFree q₂)
  | _, _, _, _, .Explode k h q => .Explode k h (prodFree q)
  | _, _, _, _, .Retag h q => .Retag h (prodFree q)
  | _, _, _, _, .Mu s q₀ q₁ => .Mu s (prodFree q₀) (prodFree q₁)
  | _, _, _, _, .MuSet s q₀ q₁ => .MuSet s (prodFree q₀) (prodFree q₁)
  | _, _, _, _, .Gamma is ts fs q keep ord => .Gamma is ts fs (prodFree q) keep ord
  | _, _, _, _, .GammaScalar ts fs q ord => .GammaScalar ts fs (prodFree q) ord
  | _, _, _, _, .GammaNest is his p g q => .GammaNest is his p g (prodFree q)
  | _, _, _, _, .ProvSum is his t q => .ProvSum is his t (prodFree q)
  | _, _, _, _, .GammaTok is his ts fs a q keep => .GammaTok is his ts fs a (prodFree q) keep
  | _, _, _, _, .Win P O o w t g q hrr dist keep => .Win P O o w t g (prodFree q) hrr dist keep
  | _, _, _, _, .WinExpr P O o ws ts fs g q keeps => .WinExpr P O o ws ts fs g (prodFree q) keeps

/-- **The pass agrees with the query up to finalization.** -/
theorem finEq_prodFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      AggQueryIn.FinEq (K := K) (prodFree q) q := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact AggQueryIn.FinEq.refl _
  | Hole _ _ => exact AggQueryIn.FinEq.refl _
  | Empty => exact AggQueryIn.FinEq.refl _
  | Proj ps q ih => exact AggQueryIn.FinEq.proj ps ih
  | Sel φ q hφ ih => exact AggQueryIn.FinEq.sel φ hφ hφ ih
  | Prod q₁ q₂ ih₁ ih₂ => exact (finEq_prodAnn _ _).trans (AggQueryIn.FinEq.prod ih₁ ih₂)
  | Apply q₁ q₂ ih₁ ih₂ => exact AggQueryIn.FinEq.apply ih₁ ih₂
  | Sum q₁ q₂ ih₁ ih₂ => exact AggQueryIn.FinEq.sum ih₁ ih₂
  | Dedup q ih => exact AggQueryIn.FinEq.dedup ih
  | Diff q₁ q₂ ih₁ ih₂ => exact AggQueryIn.FinEq.diff ih₁ ih₂
  | Explode k hk q ih => exact AggQueryIn.FinEq.explode k hk ih
  | Retag hk q ih => exact AggQueryIn.FinEq.retag hk ih
  | Mu s q₀ q₁ ih₀ ih₁ => exact AggQueryIn.FinEq.mu s ih₀ ih₁
  | MuSet s q₀ q₁ ih₀ ih₁ => exact AggQueryIn.FinEq.muSet s ih₀ ih₁
  | Gamma is ts fs q keep ord ih => exact AggQueryIn.FinEq.gamma is ts fs keep ord ih
  | GammaScalar ts fs q ord ih => exact AggQueryIn.FinEq.gammaScalar ts fs ord ih
  | GammaNest is his p g q ih => exact AggQueryIn.FinEq.gammaNest is his p g ih
  | ProvSum is his t q ih => exact AggQueryIn.FinEq.provSum is his t ih
  | GammaTok is his ts fs a q keep ih => exact AggQueryIn.FinEq.gammaTok is his ts fs a keep ih
  | Win P O o w t g q hrr dist keep ih => exact AggQueryIn.FinEq.win P O o w t g hrr dist keep ih
  | WinExpr P O o ws ts fs g q keeps ih =>
    exact AggQueryIn.FinEq.winExpr P O o ws ts fs g keeps ih

/-- **And reads exactly as the query in the plain semantics.** -/
theorem evaluatePlain_prodFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (D : Database T) (γ : Fin c → T),
      (prodFree q).evaluatePlain D γ = q.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ => rfl
  | Hole _ _ => exact fun _ _ => rfl
  | Empty => exact fun _ _ => rfl
  | Proj ps q ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | Sel φ q hφ ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro D γ
    rw [prodFree, evaluatePlain_prodAnn]
    simp only [AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Apply q₁ q₂ ih₁ ih₂ => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Sum q₁ q₂ ih₁ ih₂ => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Dedup q ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | Diff q₁ q₂ ih₁ ih₂ => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih₁, ih₂]
  | Explode k hk q ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | Retag hk q ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | Mu s q₀ q₁ ih₀ ih₁ => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih₀, ih₁]
  | Gamma is ts fs q keep ord ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | GammaScalar ts fs q ord ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | GammaNest is his p g q ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | ProvSum is his t q ih => intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | GammaTok is his ts fs a q keep ih =>
    intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | Win P O o w t g q hrr dist keep ih =>
    intro D γ; simp only [prodFree, AggQueryIn.evaluatePlain, ih]
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro D γ
    simp only [prodFree, AggQueryIn.evaluatePlain]
    rw [ih]

omit [ValueType T] in
/-- Stripping and the pass commute. -/
theorem stripAgg_prodFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (prodFree q).stripAgg = prodFree q.stripAgg := by
  intro c n κ l q
  induction q with
  | Rel _ _ => rfl
  | Hole _ _ => rfl
  | Empty => rfl
  | Proj ps q ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | Sel φ q hφ ih =>
    simp only [prodFree, AggQueryIn.stripAgg]
    by_cases h : φ.hasAggAtom
    · rw [ite_eq_left h, ite_eq_left h, ih]
    · rw [ite_eq_right h, ite_eq_right h, ih, prodFree]
  | Prod q₁ q₂ ih₁ ih₂ => simp only [prodFree, AggQueryIn.stripAgg, stripAgg_prodAnn, ih₁, ih₂]
  | Apply q₁ q₂ ih₁ ih₂ => simp only [prodFree, AggQueryIn.stripAgg, ih₁, ih₂]
  | Sum q₁ q₂ ih₁ ih₂ => simp only [prodFree, AggQueryIn.stripAgg, ih₁, ih₂]
  | Dedup q ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | Diff q₁ q₂ ih₁ ih₂ => simp only [prodFree, AggQueryIn.stripAgg, ih₁]
  | Explode k hk q ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | Retag hk q ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | Mu s q₀ q₁ ih₀ ih₁ => simp only [prodFree, AggQueryIn.stripAgg, ih₀, ih₁]
  | MuSet s q₀ q₁ ih₀ ih₁ => simp only [prodFree, AggQueryIn.stripAgg, ih₀, ih₁]
  | Gamma is ts fs q keep ord ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | GammaScalar ts fs q ord ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | GammaNest is his p g q ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | ProvSum is his t q ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | GammaTok is his ts fs a q keep ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | Win P O o w t g q hrr dist keep ih => simp only [prodFree, AggQueryIn.stripAgg, ih]
  | WinExpr P O o ws ts fs g q keeps ih => simp only [prodFree, AggQueryIn.stripAgg, ih]

/-- **The pass settles wherever the query does.** -/
theorem annSettlesAt_prodFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (d : AnnotatedDatabase T K) (γ : Fin c → T),
      q.AnnSettlesAt d γ → (prodFree q).AnnSettlesAt d γ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ _ _ => trivial
  | Hole _ _ => exact fun _ _ _ => trivial
  | Empty => exact fun _ _ _ => trivial
  | Proj ps q ih => exact fun d γ h => ih d γ h
  | Sel φ q hφ ih => exact fun d γ h => ih d γ h
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun d γ h => annSettlesAt_prodAnn _ _ d γ (ih₁ d γ h.1) (ih₂ d γ h.2)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro d γ h
    refine ⟨ih₁ d γ h.1, fun u hu => ih₂ d _ (h.2 u ?_)⟩
    rw [(finEq_prodFree q₁).evaluateAnnotated] at hu
    exact hu
  | Sum q₁ q₂ ih₁ ih₂ => exact fun d γ h => ⟨ih₁ d γ h.1, ih₂ d γ h.2⟩
  | Dedup q ih => exact fun d γ h => ih d γ h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun d γ h => ⟨ih₁ d γ h.1, ih₂ d γ h.2⟩
  | Explode k hk q ih => exact fun d γ h => ih d γ h
  | Retag hk q ih => exact fun d γ h => ih d γ h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro d γ h
    obtain ⟨h₀, hz, hs, hk, hk0⟩ := h
    have hst : AggQueryIn.muStep s (prodFree q₁) d γ = AggQueryIn.muStep s q₁ d γ :=
      funext (fun X => (finEq_prodFree q₁).evaluateAnnotated _ γ)
    have hb : (prodFree q₀).evaluateAnnotated d γ = q₀.evaluateAnnotated d γ :=
      (finEq_prodFree q₀).evaluateAnnotated d γ
    show (AggQueryIn.Mu s (prodFree q₀) (prodFree q₁)).AnnSettlesAt d γ
    refine ⟨ih₀ d γ h₀, ?_, ?_, fun k => ?_, ?_⟩
    · rw [hst]; exact hz
    · rw [hst, hb]; exact hs
    · rw [hst, hb]; exact ih₁ _ γ (hk k)
    · exact ih₁ _ γ hk0
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro d γ h
    obtain ⟨h₀, hs, hk⟩ := h
    have hst : AggQueryIn.muSetStep s (prodFree q₀) (prodFree q₁) d γ
        = AggQueryIn.muSetStep s q₀ q₁ d γ :=
      funext (fun X => by
        simp only [AggQueryIn.muSetStep, (finEq_prodFree q₀).evaluateAnnotated,
          (finEq_prodFree q₁).evaluateAnnotated])
    show (AggQueryIn.MuSet s (prodFree q₀) (prodFree q₁)).AnnSettlesAt d γ
    refine ⟨ih₀ d γ h₀, ?_, fun k => ?_⟩
    · rw [hst]; exact hs
    · rw [hst]; exact ih₁ _ γ (hk k)
  | Gamma is ts fs q keep ord ih => exact fun d γ h => ih d γ h
  | GammaScalar ts fs q ord ih => exact fun d γ h => ih d γ h
  | GammaNest is his p g q ih => exact fun d γ h => ih d γ h
  | ProvSum is his t q ih => exact fun d γ h => ih d γ h
  | GammaTok is his ts fs a q keep ih => exact fun d γ h => ih d γ h
  | Win P O o w t g q hrr dist keep ih => exact fun d γ h => ih d γ h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun d γ h => ih d γ h

/-! ## What the pass keeps -/

omit [ValueType T] in
/-- A class of the source other than `×` is a class of the target. -/
theorem mem_diff_prod {S : Set OpKind} {op : OpKind} (h : op ∈ S) (hne : op ≠ OpKind.prod) :
    op ∈ S \ {OpKind.prod} :=
  ⟨h, fun h' => hne (Set.mem_singleton_iff.mp h')⟩

omit [ValueType T] in
private theorem length_le_one_of_append {l₁ l₂ : List (String × ℕ)}
    (h : (l₁ ++ l₂).length ≤ 1) : l₁.length ≤ 1 ∧ l₂.length ≤ 1 := by
  rw [List.length_append] at h
  omega

omit [ValueType T] in
theorem usesOnly_prodFree {S : Set OpKind} (hap : OpKind.apply ∈ S) (hpr : OpKind.proj ∈ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      l.length ≤ 1 → q.usesOnly S → (prodFree q).usesOnly (S \ {OpKind.prod}) := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ h => h
  | Hole _ _ => exact fun _ h => h
  | Empty => exact fun _ h => mem_diff_prod h (by decide)
  | Proj ps q ih => exact fun hl h => ⟨⟨mem_diff_prod h.1.1 (by decide), h.1.2⟩, ih hl h.2⟩
  | Sel φ q hφ ih => exact fun hl h => ⟨mem_diff_prod h.1 (by decide), ih hl h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hl h
    obtain ⟨hl₁, hl₂⟩ := length_le_one_of_append hl
    exact usesOnly_prodAnn (mem_diff_prod hap (by decide)) (mem_diff_prod hpr (by decide)) _ _
      hl (ih₁ hl₁ h.2.1) (ih₂ hl₂ h.2.2)
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun hl h => ⟨mem_diff_prod h.1 (by decide), ih₁ hl h.2.1, ih₂ (by simp) h.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hl h
    obtain ⟨hl₁, hl₂⟩ := length_le_one_of_append hl
    exact ⟨mem_diff_prod h.1 (by decide), ih₁ hl₁ h.2.1, ih₂ hl₂ h.2.2⟩
  | Dedup q ih => exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih (by simp) h.2⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih₁ (by simp) h.2.1, ih₂ (by simp) h.2.2⟩
  | Explode k hk q ih => exact fun hl h => ih hl h
  | Retag hk q ih => exact fun hl h => ih hl h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih₀ (by simp) h.2.1, ih₁ (by simp) h.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih₀ (by simp) h.2.1, ih₁ (by simp) h.2.2⟩
  | Gamma is ts fs q keep ord ih =>
    exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih (by simp) h.2⟩
  | GammaScalar ts fs q ord ih =>
    exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih (by simp) h.2⟩
  | GammaNest is his p g q ih =>
    exact fun _ h => ⟨⟨mem_diff_prod h.1.1 (by decide), h.1.2⟩, ih (by simp) h.2⟩
  | ProvSum is his t q ih => exact fun _ h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun _ h => h.elim
  | Win P O o w t g q hrr dist keep ih =>
    exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih (by simp) h.2⟩
  | WinExpr P O o ws ts fs g q keeps ih =>
    exact fun _ h => ⟨mem_diff_prod h.1 (by decide), ih (by simp) h.2⟩

theorem inSig_prodFree {Θ : Set (SeqAggFunc T)} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.inSig Θ → (prodFree q).inSig Θ := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ⟨h.1, ih h.2⟩
  | Sel φ q hφ ih => exact fun h => ⟨h.1, ih h.2⟩
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => inSig_prodAnn _ _ (ih₁ h.1) (ih₂ h.2)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ⟨h.1, h.2.1, h.2.2.1, ih h.2.2.2⟩
  | GammaScalar ts fs q ord ih => exact fun h => ⟨h.1, h.2.1, ih h.2.2⟩
  | GammaNest is his p g q ih => exact fun h => ⟨h.1, h.2.1, ih h.2.2⟩
  | ProvSum is his t q ih => exact fun h => h.elim
  | GammaTok is his ts fs a q keep ih => exact fun h => h.elim
  | Win P O o w t g q hrr dist keep ih => exact fun h => ⟨h.1, h.2.1, h.2.2.1, ih h.2.2.2⟩
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => h.elim

omit [ValueType T] in
theorem noExplode_prodFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noExplode → (prodFree q).noExplode := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q hφ ih => exact fun h => ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => noExplode_prodAnn _ _ (ih₁ h.1) (ih₂ h.2)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode k hk q ih => exact fun h => h.elim
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p g q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t g q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

omit [ValueType T] in
theorem noMention_prodAnn {s : String} {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind}
    {κ₂ : Fin n₂ → ColKind} {l₁ l₂ : List (String × ℕ)} (q₁ : AggQueryIn T c n₁ κ₁ l₁)
    (q₂ : AggQueryIn T c n₂ κ₂ l₂) (h₁ : q₁.noMention s) (h₂ : q₂.noMention s) :
    (prodAnn q₁ q₂).noMention s := by
  unfold prodAnn
  split_ifs with hl₂ hl₁
  · rw [AggQueryIn.noMention_castIdx]
    exact ⟨h₁, (AggQueryIn.noMention_substMap _ _).mpr
      ((AggQueryIn.noMention_castIdx _ _).mpr h₂)⟩
  · rw [AggQueryIn.noMention_castIdx, AggQueryIn.noMention_castKind]
    exact ⟨h₂, (AggQueryIn.noMention_substMap _ _).mpr
      ((AggQueryIn.noMention_castIdx _ _).mpr h₁)⟩
  · exact ⟨h₁, h₂⟩

omit [ValueType T] in
theorem noMention_prodFree {s : String} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention s → (prodFree q).noMention s := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q hφ ih => exact fun h => ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => noMention_prodAnn _ _ (ih₁ h.1) (ih₂ h.2)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s' q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s' q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p g q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t g q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

omit [ValueType T] in
theorem overSchema_prodFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (sch : Schema), q.overSchema sch → (prodFree q).overSchema sch := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun _ h => h
  | Hole _ _ => exact fun _ h => h
  | Empty => exact fun _ h => h
  | Proj ps q ih => exact fun sch h => ih sch h
  | Sel φ q hφ ih => exact fun sch h => ih sch h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun sch h => overSchema_prodAnn _ _ (ih₁ sch h.1) (ih₂ sch h.2)
  | Apply q₁ q₂ ih₁ ih₂ => exact fun sch h => ⟨ih₁ sch h.1, ih₂ sch h.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun sch h => ⟨ih₁ sch h.1, ih₂ sch h.2⟩
  | Dedup q ih => exact fun sch h => ih sch h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun sch h => ⟨ih₁ sch h.1, ih₂ sch h.2⟩
  | Explode k hk q ih => exact fun sch h => ih sch h
  | Retag hk q ih => exact fun sch h => ih sch h
  | Mu s q₀ q₁ ih₀ ih₁ =>
    exact fun sch h => ⟨h.1, ih₀ sch h.2.1, noMention_prodFree q₁ h.2.2.1, ih₁ _ h.2.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    exact fun sch h => ⟨h.1, ih₀ sch h.2.1, noMention_prodFree q₁ h.2.2.1, ih₁ _ h.2.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun sch h => ih sch h
  | GammaScalar ts fs q ord ih => exact fun sch h => ih sch h
  | GammaNest is his p g q ih => exact fun sch h => ih sch h
  | ProvSum is his t q ih => exact fun sch h => ih sch h
  | GammaTok is his ts fs a q keep ih => exact fun sch h => ih sch h
  | Win P O o w t g q hrr dist keep ih => exact fun sch h => ih sch h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun sch h => ih sch h

/-- **The pass reads no aggregate parameter where the query reads none.** -/
theorem noAggParam_prodFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noAggParam → (prodFree q).noAggParam := by
  intro c n κ l q
  induction q with
  | Rel _ _ => exact fun h => h
  | Hole _ _ => exact fun h => h
  | Empty => exact fun h => h
  | Proj ps q ih => exact fun h => ih h
  | Sel φ q hφ ih => exact fun h => ih h
  | Prod q₁ q₂ ih₁ ih₂ => exact fun h => noAggParam_prodAnn _ _ (ih₁ h.1) (ih₂ h.2)
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun h => ⟨ih₁ h.1, ih₂ h.2.1,
      AggQueryIn.ReadsRegParams.of_eval (evaluatePlain_prodFree q₂)
        (fun D γ => by rw [stripAgg_prodFree, evaluatePlain_prodFree])
        (fun K' _ _ _ d γ => finEq_prodFree q₂ d γ) h.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup q ih => exact fun h => ih h
  | Diff q₁ q₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode k hk q ih => exact fun h => ih h
  | Retag hk q ih => exact fun h => ih h
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma is ts fs q keep ord ih => exact fun h => ih h
  | GammaScalar ts fs q ord ih => exact fun h => ih h
  | GammaNest is his p g q ih => exact fun h => ih h
  | ProvSum is his t q ih => exact fun h => ih h
  | GammaTok is his ts fs a q keep ih => exact fun h => ih h
  | Win P O o w t g q hrr dist keep ih => exact fun h => ih h
  | WinExpr P O o ws ts fs g q keeps ih => exact fun h => ih h

/-! ## The sufficient half: `ε` and `×` are dispensable -/

/-- **The classes other than `ε` and `×` generate the annotated algebra**,
over every schema and every commutative m-semiring: each `ε` is a set
recursion (`dedupFree`), then each product the apply of its left factor
with its right factor read under the ambient context, swapped when the
right factor holds a recursive term's hole (`prodFree`). The second pass
keeps every row, its columns and its finalized annotation, which is all
the annotated evaluation reads. -/
theorem generatesAnn_dedupProdFree (sch : Schema) (cnt : SeqAggFunc T) :
    GeneratesAnn T K sch cnt ((plainRecOps \ {OpKind.dedup}) \ {OpKind.prod}) := by
  intro n κ q ho hu hi ha hp
  obtain ⟨q', ho', hu', hi', ha', hp', he⟩ :=
    generatesAnn_dedupFree (K := K) sch cnt q ho hu hi ha hp
  refine ⟨prodFree q', overSchema_prodFree q' sch ho',
    usesOnly_prodFree (mem_diff_dedup (by simp [plainRecOps, plainOps, basisDD, basisOps])
        (by decide))
      (mem_diff_dedup (by simp [plainRecOps, plainOps, basisDD, basisOps]) (by decide))
      q' (by simp) hu',
    inSig_prodFree q' hi', noExplode_prodFree q' ha', noAggParam_prodFree q' hp',
    fun d γ hs => ?_⟩
  obtain ⟨hs', he'⟩ := he d γ hs
  exact ⟨annSettlesAt_prodFree q' d γ hs', ((finEq_prodFree q').evaluateAnnotated d γ).trans he'⟩
