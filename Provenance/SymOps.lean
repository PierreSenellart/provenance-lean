module

public import Provenance.SymTerms

/-!
# The symbolic operators: projection, selection, join

A symbolic relation holds, for every descriptor of a parameter row, the
encodings of the rows a query computes at the parameter rows of that
type – and junk under the descriptors of no parameter row. What each
operator below is asked is to map the **slice** of its input under the
descriptor of a parameter row (`Sym.slice`) to the slice of its output:
the encodings of the input's rows to the encodings of the output's. The
rows may carry further columns after their cells (`P` of them), which a
recursive term carries through its rounds untouched.
-/

@[expose] public section

variable {T : Type} [ValueType T]

namespace Sym

variable {k c n : ℕ}

/-- **The descriptor of a symbolic row**: its first `k` cells. -/
def descP {P : ℕ} (r : Tuple T ((k + n) * (7 + k) + P)) : Tuple T (k * (7 + k)) :=
  ofCells (fun i j => r (cc P (Fin.castAdd n i) j))

theorem descP_rowEncP (C : Finset T) (par : Fin k → T) (v : Tuple T n) {P : ℕ}
    (e : Tuple T P) : descP (rowEncP C par v e) = descEnc C par := by
  unfold descP descEnc
  congr 1
  funext i j
  rw [rowEncP_cc, Fin.append_left]

open Classical in
/-- **The slice of a symbolic relation** under a descriptor. -/
noncomputable def slice {P : ℕ} (Q : Multiset (Tuple T ((k + n) * (7 + k) + P)))
    (d : Tuple T (k * (7 + k))) : Multiset (Tuple T ((k + n) * (7 + k) + P)) :=
  Q.filter (fun r => descP r = d)

/-- The encodings of rows carrying further columns. -/
noncomputable def encAll (C : Finset T) (par : Fin k → T) {P : ℕ}
    (R : Multiset (Tuple T n × Tuple T P)) : Multiset (Tuple T ((k + n) * (7 + k) + P)) :=
  R.map (fun x => rowEncP C par x.1 x.2)

/-- **What a symbolic relation is asked**: under the descriptor of the
parameter row `par`, it holds the encodings of `R`. -/
def SliceIs (C : Finset T) (par : Fin k → T) {P : ℕ}
    (Q : Multiset (Tuple T ((k + n) * (7 + k) + P))) (R : Multiset (Tuple T n × Tuple T P)) :
    Prop :=
  slice Q (descEnc C par) = encAll C par R

/-! ## Maps keeping the descriptor -/

/-- **A map keeping the descriptor maps the slices.** -/
theorem slice_map {m P P' : ℕ}
    (g : Tuple T ((k + n) * (7 + k) + P) → Tuple T ((k + m) * (7 + k) + P'))
    (hg : ∀ r, descP (g r) = descP r) (Q : Multiset (Tuple T ((k + n) * (7 + k) + P)))
    (d : Tuple T (k * (7 + k))) : slice (Q.map g) d = (slice Q d).map g := by
  unfold slice
  rw [Multiset.filter_map]
  congr 1
  exact Multiset.filter_congr (fun r _ => by simp only [Function.comp, hg])

/-- **A filter commutes with the slices.** -/
theorem slice_filter {P : ℕ} (p : Tuple T ((k + n) * (7 + k) + P) → Prop) [DecidablePred p]
    (Q : Multiset (Tuple T ((k + n) * (7 + k) + P))) (d : Tuple T (k * (7 + k))) :
    slice (Q.filter p) d = (slice Q d).filter p := by
  unfold slice
  rw [Multiset.filter_filter, Multiset.filter_filter]
  exact Multiset.filter_congr (fun r _ => and_comm)

/-! ## Projection -/

/-- The symbolic projection keeps the descriptor. -/
theorem descP_symProj (P : ℕ) {m : ℕ} (srcs : Fin m → CS T k c n) (γ : Fin c → T)
    (r : Tuple T ((k + n) * (7 + k) + P)) :
    descP (fun x => (symProjSA P srcs x).eval r γ) = descP r := by
  unfold descP
  congr 1
  funext i j
  show (symProjSA P srcs (Fin.castAdd P (finProdFinEquiv (Fin.castAdd m i, j)))).eval r γ = _
  rw [symProjSA, Fin.addCases_left, Equiv.symm_apply_apply, Fin.addCases_left]
  rfl

/-- **The symbolic projection's slice**: the encodings of the projected
rows. -/
theorem sliceIs_symProj {C : Finset T} (par : Fin k → T) (P : ℕ) {m : ℕ}
    (srcs : Fin m → CS T k c n) (γ : Fin c → T) (hamb : ∀ j, CG C (γ j))
    (hc : ∀ j a, srcs j = .const a → CG C a)
    {Q : Multiset (Tuple T ((k + n) * (7 + k) + P))} {R : Multiset (Tuple T n × Tuple T P)}
    (hQ : SliceIs C par Q R) :
    SliceIs C par (Q.map (fun r x => (symProjSA P srcs x).eval r γ))
      (R.map (fun x => ((fun j => (srcs j).val par γ x.1 : Tuple T m), x.2))) := by
  unfold SliceIs at hQ ⊢
  rw [slice_map _ (descP_symProj P srcs γ), hQ, encAll, encAll, Multiset.map_map,
    Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  exact eval_symProjSA P srcs par γ x.1 x.2 hamb hc

/-! ## Selection -/

/-- **The symbolic selection's slice**: the encodings of the rows kept. -/
theorem sliceIs_symSel {C : Finset T} (par : Fin k → T) (P : ℕ) {κ : Fin n → ColKind}
    (φ : GenPredIn T (k + c) κ) (hφ : φ.noFun = true) (hφc : ∀ a ∈ φ.consts, CG C a)
    (γ : Fin c → T) (hamb : ∀ j, CG C (γ j))
    {Q : Multiset (Tuple T ((k + n) * (7 + k) + P))} {R : Multiset (Tuple T n × Tuple T P)}
    (hR : ∀ x ∈ R, ∀ i, GoodVal (C := C) par (x.1 i)) (hQ : SliceIs C par Q R) :
    SliceIs C par (Q.filter (fun r => (transPred P φ).eval3 r γ = Kleene.true))
      (R.filter (fun x => φ.evalPlain3 x.1 (Fin.append par γ) = Kleene.true)) := by
  unfold SliceIs at hQ ⊢
  rw [slice_filter, hQ, encAll, encAll, Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr (fun x hx => ?_)
  show (transPred P φ).eval3 (rowEncP C par x.1 x.2) γ = Kleene.true ↔ _
  rw [eval3_transPred P φ hφ hφc par γ x.1 x.2 (hR x hx) hamb]

/-! ## Join -/

section Join

variable {n₁ n₂ : ℕ}

/-- **The two descriptors of a pair of symbolic rows agree**, the left one
carrying `P₁` further columns and the right one `P₂`. -/
def descEqSP (P₁ P₂ : ℕ) :
    SP T c (((k + n₁) * (7 + k) + P₁) + ((k + n₂) * (7 + k) + P₂)) :=
  andAll ((List.finRange k).flatMap (fun i => (List.finRange (7 + k)).map (fun j =>
    .atom .syneq (.col (Fin.castAdd _ (cc P₁ (Fin.castAdd n₁ i) j)))
      (.col (Fin.natAdd _ (cc P₂ (Fin.castAdd n₂ i) j))))))

theorem eval3_descEqSP (P₁ P₂ : ℕ) (r₁ : Tuple T ((k + n₁) * (7 + k) + P₁))
    (r₂ : Tuple T ((k + n₂) * (7 + k) + P₂)) (γ : Fin c → T) :
    (descEqSP (n₁ := n₁) (n₂ := n₂) P₁ P₂).eval3 (Fin.append r₁ r₂) γ
      = Kleene.ofBool (decide (descP r₁ = descP r₂)) := by
  unfold descEqSP
  rw [eval3_andAll _ _ _ (fun p hp => by
    obtain ⟨i, -, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    rw [eval3_atom_syneq]; exact ofBool_definite _)]
  refine ofBool_congr ?_
  simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
    forall_exists_index]
  constructor
  · intro h
    unfold descP
    congr 1
    funext i j
    have := h _ i j rfl
    rw [eval3_atom_syneq, Kleene.ofBool_eq_true_iff, decide_eq_true_eq] at this
    simpa [SA.eval, Fin.append_left, Fin.append_right] using this
  · intro h p i j hp
    subst hp
    rw [eval3_atom_syneq, Kleene.ofBool_eq_true_iff, decide_eq_true_eq]
    have := congrArg (fun r => cellOf r i j) h
    simp only [descP, cellOf_ofCells] at this
    simpa [SA.eval, Fin.append_left, Fin.append_right] using this

/-- **The cells of a joined row**: the descriptor and the cells of the
left row, then the cells of the right row, then the further columns of
the left row (`L`) or of the right row (`R`). -/
def joinCellSA (P₁ P₂ : ℕ) (y : Fin ((k + (n₁ + n₂)) * (7 + k))) :
    SA T c (((k + n₁) * (7 + k) + P₁) + ((k + n₂) * (7 + k) + P₂)) :=
  Fin.addCases (motive := fun _ => SA T c _)
    (fun i₀ => .col (Fin.castAdd _ (cc P₁ (Fin.castAdd n₁ i₀) (finProdFinEquiv.symm y).2)))
    (fun t => Fin.addCases (motive := fun _ => SA T c _)
      (fun t₁ => .col (Fin.castAdd _ (cc P₁ (Fin.natAdd k t₁) (finProdFinEquiv.symm y).2)))
      (fun t₂ => .col (Fin.natAdd _ (cc P₂ (Fin.natAdd k t₂) (finProdFinEquiv.symm y).2))) t)
    (finProdFinEquiv.symm y).1

/-- The join keeping the left row's further columns. -/
def joinLSA (P₁ P₂ : ℕ) :
    Fin ((k + (n₁ + n₂)) * (7 + k) + P₁)
      → SA T c (((k + n₁) * (7 + k) + P₁) + ((k + n₂) * (7 + k) + P₂)) :=
  Fin.addCases (joinCellSA P₁ P₂) (fun z => .col (Fin.castAdd _ (Fin.natAdd _ z)))

/-- The join keeping the right row's further columns. -/
def joinRSA (P₁ P₂ : ℕ) :
    Fin ((k + (n₁ + n₂)) * (7 + k) + P₂)
      → SA T c (((k + n₁) * (7 + k) + P₁) + ((k + n₂) * (7 + k) + P₂)) :=
  Fin.addCases (joinCellSA P₁ P₂) (fun z => .col (Fin.natAdd _ (Fin.natAdd _ z)))

theorem joinCellSA_eval (C : Finset T) (par : Fin k → T) {P₁ P₂ : ℕ} (v₁ : Tuple T n₁)
    (e₁ : Tuple T P₁) (v₂ : Tuple T n₂) (e₂ : Tuple T P₂) (γ : Fin c → T)
    (i : Fin (k + (n₁ + n₂))) (j : Fin (7 + k)) :
    (joinCellSA P₁ P₂ (finProdFinEquiv (i, j))).eval
        (Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂)) γ
      = (Fin.append (fun i => enc C k (code C par i))
          (fun j => enc C k (vcode C par (Fin.append v₁ v₂ j))) i) j := by
  unfold joinCellSA
  rw [Equiv.symm_apply_apply]
  refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
  · rw [Fin.addCases_left, Fin.append_left]
    show Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂) (Fin.castAdd _ _) = _
    rw [Fin.append_left, rowEncP_cc, Fin.append_left]
  · rw [Fin.addCases_right, Fin.append_right]
    refine Fin.addCases (fun t₁ => ?_) (fun t₂ => ?_) t
    · rw [Fin.addCases_left, Fin.append_left]
      show Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂) (Fin.castAdd _ _) = _
      rw [Fin.append_left, rowEncP_cc, Fin.append_right]
    · rw [Fin.addCases_right, Fin.append_right]
      show Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂) (Fin.natAdd _ _) = _
      rw [Fin.append_right, rowEncP_cc, Fin.append_right]

theorem rowEncP_ext (C : Finset T) (par : Fin k → T) {m P : ℕ} (v : Tuple T m) (e : Tuple T P)
    (f : Tuple T ((k + m) * (7 + k) + P))
    (hc : ∀ i j, f (cc P i j) = (Fin.append (fun i => enc C k (code C par i))
      (fun j => enc C k (vcode C par (v j))) i) j)
    (hs : ∀ z, f (Fin.natAdd _ z) = e z) : f = rowEncP C par v e := by
  funext x
  refine Fin.addCases (fun y => ?_) (fun z => ?_) x
  · obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
    show f (cc P i j) = rowEncP C par v e (cc P i j)
    rw [hc, rowEncP_cc]
  · rw [hs]
    show e z = Fin.append (rowEnc C par v) e (Fin.natAdd _ z)
    rw [Fin.append_right]

/-- **A joined pair of encoded rows is the encoding of the joined row**,
the left one's further columns kept. -/
theorem joinLSA_eval (C : Finset T) (par : Fin k → T) {P₁ P₂ : ℕ} (v₁ : Tuple T n₁)
    (e₁ : Tuple T P₁) (v₂ : Tuple T n₂) (e₂ : Tuple T P₂) (γ : Fin c → T) :
    (fun x => (joinLSA P₁ P₂ x).eval (Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂)) γ)
      = rowEncP C par (Fin.append v₁ v₂) e₁ := by
  refine rowEncP_ext C par _ e₁ _ (fun i j => ?_) (fun z => ?_)
  · show (joinLSA P₁ P₂ (Fin.castAdd P₁ (finProdFinEquiv (i, j)))).eval _ γ = _
    rw [joinLSA, Fin.addCases_left, joinCellSA_eval]
  · show (joinLSA P₁ P₂ (Fin.natAdd _ z)).eval _ γ = _
    rw [joinLSA, Fin.addCases_right]
    show Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂) (Fin.castAdd _ (Fin.natAdd _ z)) = _
    rw [Fin.append_left]
    show Fin.append (rowEnc C par v₁) e₁ (Fin.natAdd _ z) = _
    rw [Fin.append_right]

/-- **The same, the right one's further columns kept.** -/
theorem joinRSA_eval (C : Finset T) (par : Fin k → T) {P₁ P₂ : ℕ} (v₁ : Tuple T n₁)
    (e₁ : Tuple T P₁) (v₂ : Tuple T n₂) (e₂ : Tuple T P₂) (γ : Fin c → T) :
    (fun x => (joinRSA P₁ P₂ x).eval (Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂)) γ)
      = rowEncP C par (Fin.append v₁ v₂) e₂ := by
  refine rowEncP_ext C par _ e₂ _ (fun i j => ?_) (fun z => ?_)
  · show (joinRSA P₁ P₂ (Fin.castAdd P₂ (finProdFinEquiv (i, j)))).eval _ γ = _
    rw [joinRSA, Fin.addCases_left, joinCellSA_eval]
  · show (joinRSA P₁ P₂ (Fin.natAdd _ z)).eval _ γ = _
    rw [joinRSA, Fin.addCases_right]
    show Fin.append (rowEncP C par v₁ e₁) (rowEncP C par v₂ e₂) (Fin.natAdd _ (Fin.natAdd _ z)) = _
    rw [Fin.append_right]
    show Fin.append (rowEnc C par v₂) e₂ (Fin.natAdd _ z) = _
    rw [Fin.append_right]

omit [ValueType T] in
theorem descP_joinCell {P₁ P₂ M : ℕ}
    (f : Fin ((k + (n₁ + n₂)) * (7 + k) + M)
      → SA T c (((k + n₁) * (7 + k) + P₁) + ((k + n₂) * (7 + k) + P₂)))
    (hf : ∀ y, f (Fin.castAdd M y) = joinCellSA P₁ P₂ y)
    (r₁ : Tuple T ((k + n₁) * (7 + k) + P₁)) (r₂ : Tuple T ((k + n₂) * (7 + k) + P₂))
    (γ : Fin c → T) :
    descP (n := n₁ + n₂) (fun x => (f x).eval (Fin.append r₁ r₂) γ) = descP r₁ := by
  unfold descP
  congr 1
  funext i j
  show (f (Fin.castAdd M (finProdFinEquiv (Fin.castAdd (n₁ + n₂) i, j)))).eval _ γ = _
  rw [hf, joinCellSA, Equiv.symm_apply_apply, Fin.addCases_left]
  show Fin.append r₁ r₂ (Fin.castAdd _ _) = _
  rw [Fin.append_left]

/-- **The slices of a join** are the joins of the slices. -/
theorem slice_join {P₁ P₂ M : ℕ}
    (proj : Tuple T (((k + n₁) * (7 + k) + P₁) + ((k + n₂) * (7 + k) + P₂))
      → Tuple T ((k + (n₁ + n₂)) * (7 + k) + M))
    (hproj : ∀ r₁ r₂, descP (proj (Fin.append r₁ r₂)) = descP r₁) (γ : Fin c → T)
    (Q₁ : Multiset (Tuple T ((k + n₁) * (7 + k) + P₁)))
    (Q₂ : Multiset (Tuple T ((k + n₂) * (7 + k) + P₂))) (d : Tuple T (k * (7 + k))) :
    slice (((Q₁.bind fun r₁ => Q₂.map (fun r₂ => Fin.append r₁ r₂)).filter
        (fun x => (descEqSP (n₁ := n₁) (n₂ := n₂) P₁ P₂).eval3 x γ = Kleene.true)).map proj) d
      = ((slice Q₁ d).bind fun r₁ => (slice Q₂ d).map (fun r₂ => Fin.append r₁ r₂)).map proj := by
  classical
  unfold slice
  rw [Multiset.filter_map, Multiset.filter_filter, Multiset.filter_bind]
  congr 1
  rw [← AggQueryIn.Multiset.bind_ite (fun r₁ => descP r₁ = d)]
  refine Multiset.bind_congr (fun r₁ _ => ?_)
  rw [Multiset.filter_map]
  by_cases h₁ : descP r₁ = d
  · rw [ite_eq_left h₁]
    congr 1
    refine Multiset.filter_congr (fun r₂ _ => ?_)
    simp only [Function.comp, hproj, eval3_descEqSP, Kleene.ofBool_eq_true_iff, decide_eq_true_eq,
      h₁]
    exact ⟨fun h => h.2.symm, fun h => ⟨trivial, h.symm⟩⟩
  · rw [ite_eq_right h₁, Multiset.filter_eq_nil.mpr]
    · rfl
    · intro r₂ _ h
      simp only [Function.comp, hproj] at h
      exact h₁ h.1

/-- **The symbolic join's slice, the left row's further columns kept.** -/
theorem sliceIs_joinL {C : Finset T} (par : Fin k → T) {P₁ P₂ : ℕ} (γ : Fin c → T)
    {Q₁ : Multiset (Tuple T ((k + n₁) * (7 + k) + P₁))}
    {Q₂ : Multiset (Tuple T ((k + n₂) * (7 + k) + P₂))}
    {R₁ : Multiset (Tuple T n₁ × Tuple T P₁)} {R₂ : Multiset (Tuple T n₂ × Tuple T P₂)}
    (h₁ : SliceIs C par Q₁ R₁) (h₂ : SliceIs C par Q₂ R₂) :
    SliceIs C par (((Q₁.bind fun r₁ => Q₂.map (fun r₂ => Fin.append r₁ r₂)).filter
        (fun x => (descEqSP (n₁ := n₁) (n₂ := n₂) P₁ P₂).eval3 x γ = Kleene.true)).map
          (fun x i => (joinLSA P₁ P₂ i).eval x γ))
      (R₁.bind fun x₁ => R₂.map fun x₂ => (Fin.append x₁.1 x₂.1, x₁.2)) := by
  unfold SliceIs at h₁ h₂ ⊢
  rw [slice_join _ (fun r₁ r₂ => descP_joinCell _ (fun y => by rw [joinLSA, Fin.addCases_left])
    r₁ r₂ γ), h₁, h₂, encAll, encAll, encAll, Multiset.bind_map, Multiset.map_bind,
    Multiset.map_bind]
  refine Multiset.bind_congr (fun x₁ _ => ?_)
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun x₂ _ => joinLSA_eval C par _ _ _ _ γ)

/-- **The symbolic join's slice, the right row's further columns kept.** -/
theorem sliceIs_joinR {C : Finset T} (par : Fin k → T) {P₁ P₂ : ℕ} (γ : Fin c → T)
    {Q₁ : Multiset (Tuple T ((k + n₁) * (7 + k) + P₁))}
    {Q₂ : Multiset (Tuple T ((k + n₂) * (7 + k) + P₂))}
    {R₁ : Multiset (Tuple T n₁ × Tuple T P₁)} {R₂ : Multiset (Tuple T n₂ × Tuple T P₂)}
    (h₁ : SliceIs C par Q₁ R₁) (h₂ : SliceIs C par Q₂ R₂) :
    SliceIs C par (((Q₁.bind fun r₁ => Q₂.map (fun r₂ => Fin.append r₁ r₂)).filter
        (fun x => (descEqSP (n₁ := n₁) (n₂ := n₂) P₁ P₂).eval3 x γ = Kleene.true)).map
          (fun x i => (joinRSA P₁ P₂ i).eval x γ))
      (R₁.bind fun x₁ => R₂.map fun x₂ => (Fin.append x₁.1 x₂.1, x₂.2)) := by
  unfold SliceIs at h₁ h₂ ⊢
  rw [slice_join _ (fun r₁ r₂ => descP_joinCell _ (fun y => by rw [joinRSA, Fin.addCases_left])
    r₁ r₂ γ), h₁, h₂, encAll, encAll, encAll, Multiset.bind_map, Multiset.map_bind,
    Multiset.map_bind]
  refine Multiset.bind_congr (fun x₁ _ => ?_)
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun x₂ _ => joinRSA_eval C par _ _ _ _ γ)

end Join

/-! ## The descriptors, and the leaves -/

omit [ValueType T] in
/-- A row of descriptors is its own descriptor. -/
theorem descP_desc (r : Tuple T ((k + 0) * (7 + k) + 0)) : descP (n := 0) (P := 0) r = r := by
  funext x
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  show r (cc 0 (Fin.castAdd 0 (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = r (finProdFinEquiv (i, j))
  rw [Equiv.symm_apply_apply]
  rfl

/-- The encoding of a parameter row with no output is its descriptor. -/
theorem rowEncP_zero (C : Finset T) (par : Fin k → T) :
    rowEncP (n := 0) C par Fin.elim0 (Fin.elim0 : Tuple T 0) = descEnc C par := by
  funext x
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  show rowEncP C par Fin.elim0 Fin.elim0 (cc 0 (Fin.castAdd 0 i) j) = _
  rw [rowEncP_cc, Fin.append_left]
  show _ = cellOf (descEnc C par) i j
  rw [descEnc, cellOf_ofCells]

/-- **The relation of descriptors, as a symbolic relation with no
output**: its slice under a descriptor it holds once is that row. -/
theorem sliceIs_desc {C : Finset T} (par : Fin k → T) {Dq : Multiset (Tuple T (k * (7 + k)))}
    (hnd : Dq.Nodup) (hm : descEnc C par ∈ Dq) :
    SliceIs (n := 0) (P := 0) C par Dq {((Fin.elim0 : Tuple T 0), (Fin.elim0 : Tuple T 0))} := by
  classical
  unfold SliceIs slice encAll
  rw [Multiset.map_singleton, rowEncP_zero]
  simp only [descP_desc]
  exact (Multiset.Nodup.ext (hnd.filter _) (Multiset.nodup_singleton _)).mpr (fun x => by
    rw [Multiset.mem_filter, Multiset.mem_singleton]
    exact ⟨And.right, fun h => ⟨h ▸ hm, h⟩⟩)

/-- **The cells of a leaf's row**, paired with a descriptor: the
descriptor's cells, then the row's values as concrete cells. -/
def leafSA (n : ℕ) : Fin ((k + n) * (7 + k) + 0) → SA T c (k * (7 + k) + n) :=
  fun x => Fin.addCases (motive := fun _ => SA T c (k * (7 + k) + n))
    (fun i₀ => .col (Fin.castAdd n (ci i₀ (finProdFinEquiv.symm x).2)))
    (fun t => concCols (.col (Fin.natAdd _ t)) (finProdFinEquiv.symm x).2)
    (finProdFinEquiv.symm x).1

theorem leafSA_eval (C : Finset T) (par : Fin k → T) (v : Tuple T n) (γ : Fin c → T)
    (hv : ∀ t, CG C (v t)) :
    (fun x => (leafSA (k := k) n x).eval (Fin.append (descEnc C par) v) γ)
      = rowEncP C par v (Fin.elim0 : Tuple T 0) := by
  refine rowEncP_ext C par v _ _ (fun i j => ?_) (fun z => z.elim0)
  show (leafSA n (Fin.castAdd 0 (finProdFinEquiv (i, j)))).eval _ γ = _
  unfold leafSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (i, j)) = finProdFinEquiv (i, j) from rfl,
    Equiv.symm_apply_apply]
  refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
  · rw [Fin.addCases_left, Fin.append_left]
    show Fin.append (descEnc C par) v (Fin.castAdd n _) = _
    rw [Fin.append_left]
    show cellOf (descEnc C par) i₀ j = _
    rw [descEnc, cellOf_ofCells]
  · rw [Fin.addCases_right, Fin.append_right, concCols_eval]
    show enc C k (.conc (Fin.append (descEnc C par) v (Fin.natAdd _ t))) j = _
    rw [Fin.append_right, vcode_of_mem par (hv t)]

theorem descP_leafSA (d : Tuple T (k * (7 + k))) (v : Tuple T n) (γ : Fin c → T) :
    descP (P := 0) (fun x => (leafSA (k := k) n x).eval (Fin.append d v) γ) = d := by
  funext x
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  simp only [descP, ofCells, Equiv.symm_apply_apply]
  show (leafSA n (Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd n i, j)))).eval _ γ
    = d (finProdFinEquiv (i, j))
  unfold leafSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd n i, j))
      = finProdFinEquiv (Fin.castAdd n i, j) from rfl,
    Equiv.symm_apply_apply, Fin.addCases_left]
  show Fin.append d v (Fin.castAdd n _) = _
  rw [Fin.append_left]
  rfl

/-- **A leaf paired with the descriptors**: its slice under a descriptor
is the encoding of its rows. -/
theorem sliceIs_leaf {C : Finset T} (par : Fin k → T) (γ : Fin c → T)
    {Dq : Multiset (Tuple T (k * (7 + k)))} (hnd : Dq.Nodup) (hm : descEnc C par ∈ Dq)
    (R : Multiset (Tuple T n)) (hR : ∀ v ∈ R, ∀ t, CG C (v t)) :
    SliceIs C par ((Dq.bind fun d => R.map fun v => (Fin.append d v : Tuple T _)).map
        (fun x i => (leafSA (k := k) n i).eval x γ))
      (R.map fun v => (v, (Fin.elim0 : Tuple T 0))) := by
  classical
  unfold SliceIs slice encAll
  rw [Multiset.filter_map, Multiset.filter_bind]
  have hfil : ∀ d, Multiset.filter ((fun r => descP (P := 0) r = descEnc C par) ∘
      (fun x i => (leafSA (k := k) n i).eval x γ))
        (R.map fun v => (Fin.append d v : Tuple T _))
      = if d = descEnc C par then R.map (fun v => Fin.append d v) else 0 := by
    intro d
    rw [Multiset.filter_map]
    by_cases hd : d = descEnc C par
    · rw [ite_eq_left hd, Multiset.filter_eq_self.mpr (fun v _ => by
        simp only [Function.comp, descP_leafSA]; exact hd)]
    · rw [ite_eq_right hd, Multiset.filter_eq_nil.mpr (fun v _ h => by
        simp only [Function.comp, descP_leafSA] at h; exact hd h)]
      rfl
  simp only [hfil]
  have hsl : Dq.filter (fun d => d = descEnc C par) = {descEnc C par} :=
    (Multiset.Nodup.ext (hnd.filter _) (Multiset.nodup_singleton _)).mpr (fun x => by
      rw [Multiset.mem_filter, Multiset.mem_singleton]
      exact ⟨And.right, fun h => ⟨h ▸ hm, h⟩⟩)
  rw [AggQueryIn.Multiset.bind_ite (fun d => d = descEnc C par), hsl, Multiset.singleton_bind,
    Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun v hv => leafSA_eval C par v γ (hR v hv))

end Sym
