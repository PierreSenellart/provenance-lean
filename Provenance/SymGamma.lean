import Provenance.SymOps

/-!
# The symbolic grouping

A grouping over a symbolic relation groups by the descriptor and by the
key cells, and counts through the value column of each cell: a cell's
value column is null exactly when the value it stands for is
(`Sym.isNull_termV`), and the counting aggregates of the minimal
signature read nothing but how many values are not null
(`SeqAggFunc.ReadsCount`). Under the descriptor of a parameter row the
groups are the encodings of the groups the query forms at that row, one
for one, the encoding being injective on good values; so the grouping of
the symbolic relation computes, under each such descriptor, the encodings
of the keys and the very counts of the grouping
(`Sym.gammaRows_slice`).
-/

variable {T : Type} [ValueType T]

namespace Sym

variable {k c m n₁ n₂ : ℕ}

/-! ## The plain grouping, as a function of its input -/

/-- **The rows a grouping emits** from its input. -/
noncomputable def gammaRows {c' m' : ℕ} (is : Tuple (Fin m') n₁) (ts : Tuple (TermIn T c' m') n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (keep : Fin n₂ → Option (Selection T m'))
    (ord : GroupOrder T m') (r : Multiset (Tuple T m')) (γ : Fin c' → T) :
    Multiset (Tuple T (n₁ + n₂)) :=
  ((r.map (fun u => (fun k' => u (is k') : Tuple T n₁))).dedup).map (fun g => Fin.append g
    (fun j => (fs j) ((Relation.groupSeqOptOrd is ord r g (keep j)).map
      (fun v => (ts j).eval v γ))))

/-- A counting aggregate reads the bag of a group. -/
theorem readsCount_groupSeq {c' m' : ℕ} {f : SeqAggFunc T} (hf : f.ReadsCount)
    (is : Tuple (Fin m') n₁) (t : TermIn T c' m') (ord : GroupOrder T m')
    (r : Multiset (Tuple T m')) (g : Tuple T n₁) (keep : Option (Selection T m'))
    (γ : Fin c' → T) :
    f ((Relation.groupSeqOptOrd is ord r g keep).map (fun v => t.eval v γ))
      = hf.choose ((((r.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).filter
          (fun u => Selection.keepsOpt keep u = true)).map (fun v => t.eval v γ)).countP
            (fun x => ValueType.isNull x = false)) := by
  rw [hf.choose_spec, ← Relation.groupSeqOptOrd_coe is ord r g keep, Multiset.map_coe,
    Multiset.coe_countP]
  exact congrArg hf.choose (List.countP_congr (fun x _ => by simp))

/-! ## The symbolic grouping's keys and terms -/

/-- **The key columns of the symbolic grouping**: the descriptor's, then
the key cells'. -/
def gKeyIdx (is : Tuple (Fin m) n₁) :
    Tuple (Fin ((k + m) * (7 + k))) (k * (7 + k) + n₁ * (7 + k)) :=
  Fin.append (fun y => ci (Fin.castAdd m (finProdFinEquiv.symm y).1) (finProdFinEquiv.symm y).2)
    (fun y => ci (Fin.natAdd k (is (finProdFinEquiv.symm y).1)) (finProdFinEquiv.symm y).2)

/-- **A term of a grouping, read on a symbolic row**: the value column of
the cell it reads. -/
def termV : TermIn T (k + c) m → TermIn T c ((k + m) * (7 + k))
  | .const a => .const a
  | .outer o => Fin.addCases (motive := fun _ => TermIn T c ((k + m) * (7 + k)))
      (fun i => .index (ci (Fin.castAdd m i) (iV k))) (fun j => .outer j) o
  | .index i => .index (ci (Fin.natAdd k i) (iV k))
  | _ => .const 0

/-- The value column of a code is null exactly when the value it stands
for is. -/
theorem isNull_enc_V (C : Finset T) (par : Fin k → T) (b : T) :
    ValueType.isNull (enc C k (vcode C par b) (iV k)) = ValueType.isNull b := by
  by_cases h : ∃ i, IsFresh C (par i) ∧ par i = b
  · obtain ⟨i, hi, rfl⟩ := h
    rw [vcode_par, code_of_fresh hi, enc_fresh_V, isNull_lval_lo, hi.2]
  · rw [vcode_of_not par (fun i hi he => h ⟨i, hi, he⟩)]; rfl

/-- **A term read on an encoded row is null exactly when the term is.** -/
theorem isNull_termV (C : Finset T) (t : TermIn T (k + c) m) (ht : t.noFun = true)
    (par : Fin k → T) (v : Tuple T m) (γ : Fin c → T) :
    ValueType.isNull ((termV t).eval (rowEnc C par v) γ)
      = ValueType.isNull (t.eval v (Fin.append par γ)) := by
  cases t with
  | const a => rfl
  | outer o =>
    refine Fin.addCases (fun i => ?_) (fun j => ?_) o
    · simp only [termV, Fin.addCases_left]
      show ValueType.isNull (rowEnc C par v (ci (Fin.castAdd m i) (iV k)))
        = ValueType.isNull (Fin.append par γ (Fin.castAdd c i))
      rw [Fin.append_left]
      show ValueType.isNull (cellOf (rowEnc C par v) (Fin.castAdd m i) (iV k)) = _
      rw [rowEnc, cellOf_ofCells, Fin.append_left, ← vcode_par, isNull_enc_V]
    · simp only [termV, Fin.addCases_right]
      show ValueType.isNull (γ j) = ValueType.isNull (Fin.append par γ (Fin.natAdd k j))
      rw [Fin.append_right]
  | index i =>
    show ValueType.isNull (cellOf (rowEnc C par v) (Fin.natAdd k i) (iV k)) = _
    rw [rowEnc, cellOf_ofCells, Fin.append_right, isNull_enc_V]
    rfl
  | _ => simp [TermIn.noFun] at ht

/-- The key of an encoded row: the descriptor and the encodings of the
key values. -/
theorem key_rowEnc (C : Finset T) (is : Tuple (Fin m) n₁) (par : Fin k → T) (v : Tuple T m) :
    (fun x => rowEnc C par v (gKeyIdx is x))
      = Fin.append (descEnc C par)
          (ofCells (fun t => enc C k (vcode C par (v (is t))))) := by
  funext x
  refine Fin.addCases (fun y => ?_) (fun y => ?_) x
  · rw [Fin.append_left]
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
    simp only [gKeyIdx, Fin.append_left, Equiv.symm_apply_apply]
    show cellOf (rowEnc C par v) (Fin.castAdd m i) j = cellOf (descEnc C par) i j
    rw [rowEnc, descEnc, cellOf_ofCells, cellOf_ofCells, Fin.append_left]
  · rw [Fin.append_right]
    obtain ⟨⟨t, j⟩, rfl⟩ := finProdFinEquiv.surjective y
    simp only [gKeyIdx, Fin.append_right, Equiv.symm_apply_apply]
    show cellOf (rowEnc C par v) (Fin.natAdd k (is t)) j
      = cellOf (ofCells (fun t => enc C k (vcode C par (v (is t))))) t j
    rw [rowEnc, cellOf_ofCells, cellOf_ofCells, Fin.append_right]

/-- An encoded row with no further columns is the encoded row. -/
theorem rowEncP_elim0 (C : Finset T) (par : Fin k → T) (v : Tuple T m) :
    (rowEncP C par v (Fin.elim0 : Tuple T 0) : Tuple T ((k + m) * (7 + k))) = rowEnc C par v := by
  funext i
  exact Fin.append_left (rowEnc C par v) (Fin.elim0 : Tuple T 0) i

/-- **The encoding of a key.** -/
noncomputable def encK (C : Finset T) (par : Fin k → T) (g : Tuple T n₁) :
    Tuple T (k * (7 + k) + n₁ * (7 + k)) :=
  Fin.append (descEnc C par) (ofCells (fun t => enc C k (vcode C par (g t))))

/-- The key of an encoded row is the encoding of its key. -/
theorem key_rowEnc_encK (C : Finset T) (is : Tuple (Fin m) n₁) (par : Fin k → T)
    (v : Tuple T m) :
    Tuple.key (gKeyIdx is) (rowEnc C par v) = encK C par (fun t => v (is t)) :=
  key_rowEnc C is par v

theorem encK_injective (C : Finset T) (par : Fin k → T) :
    Function.Injective (encK (n₁ := n₁) C par) := fun g g' h => by
  funext t
  have h' : ofCells (fun t => enc C k (vcode C par (g t)))
      = ofCells (fun t => enc C k (vcode C par (g' t))) := by
    funext x
    have := congrFun h (Fin.natAdd _ x)
    simpa [encK, Fin.append_right] using this
  have := (ofCells_eq_iff _ _).mp h' t
  exact vcode_injective par (enc_inj (rankOK_vcode par _) (rankOK_vcode par _) this)

/-- The descriptor of a key. -/
def keyDesc {M : ℕ} (x : Tuple T (k * (7 + k) + M)) : Tuple T (k * (7 + k)) :=
  fun i => x (Fin.castAdd M i)

omit [ValueType T] in
theorem keyDesc_key (is : Tuple (Fin m) n₁) (r : Tuple T ((k + m) * (7 + k))) :
    keyDesc (fun x => r (gKeyIdx is x)) = descP (P := 0) r := by
  funext y
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [keyDesc, gKeyIdx, Fin.append_left, descP, ofCells, Equiv.symm_apply_apply]
  rfl

theorem keyDesc_encK (C : Finset T) (par : Fin k → T) (g : Tuple T n₁) :
    keyDesc (encK C par g) = descEnc C par := by
  funext y
  simp [keyDesc, encK, Fin.append_left]

omit [ValueType T] in
theorem Multiset.dedup_filter_comm {α : Type} [DecidableEq α] (q : α → Prop) [DecidablePred q]
    (M : Multiset α) : (M.dedup).filter q = (M.filter q).dedup :=
  (Multiset.Nodup.ext ((Multiset.nodup_dedup M).filter _) (Multiset.nodup_dedup _)).mpr
    (fun x => by simp [Multiset.mem_filter, Multiset.mem_dedup])

/-- **A selection read on an encoded row keeps it as on the row.** -/
theorem keepsOpt_transSel {C : Finset T} (par : Fin k → T) (keep : Option (Selection T m))
    (hkeep : ∀ φ, keep = some φ → φ.noFun = true ∧ ∀ a ∈ φ.consts, CG C a) (v : Tuple T m)
    (hv : ∀ i, GoodVal (C := C) par (v i)) :
    Selection.keepsOpt (keep.map (fun φ => (transSel (k := k) 0 φ).toSel)) (rowEnc C par v)
      = Selection.keepsOpt keep v := by
  cases keep with
  | none => rfl
  | some φ =>
    obtain ⟨hn, hc⟩ := hkeep φ rfl
    show Selection.keeps _ (rowEnc C par v) = Selection.keeps φ v
    unfold Selection.keeps
    rw [show rowEnc C par v = (rowEncP C par v (Fin.elim0 : Tuple T 0)
        : Tuple T ((k + m) * (7 + k))) from (rowEncP_elim0 C par v).symm,
      SP.eval3_toSel _ _ (fun j => j.elim0), eval3_transSel 0 φ hn hc par v _ hv]

/-- The slice of a symbolic relation with no further columns, as encoded
rows. -/
theorem slice_eq_map_rowEnc {C : Finset T} {par : Fin k → T}
    {Q : Multiset (Tuple T ((k + m) * (7 + k)))} {R : Multiset (Tuple T m)}
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0)))) :
    Q.filter (fun r => descP (P := 0) r = descEnc C par) = R.map (rowEnc C par) := by
  have := hQ
  unfold SliceIs encAll slice at this
  rw [this, Multiset.map_map]
  exact Multiset.map_congr rfl (fun v _ => rowEncP_elim0 C par v)

/-- **The keys a symbolic grouping forms under a descriptor** are the
encodings of the keys the grouping forms at the parameter row. -/
theorem keys_slice {C : Finset T} {par : Fin k → T} (is : Tuple (Fin m) n₁)
    {Q : Multiset (Tuple T ((k + m) * (7 + k)))} {R : Multiset (Tuple T m)}
    (hsl : Q.filter (fun r => descP (P := 0) r = descEnc C par) = R.map (rowEnc C par)) :
    ((Q.map (fun u => (fun x => u (gKeyIdx is x)
      : Tuple T (k * (7 + k) + n₁ * (7 + k))))).dedup).filter
        (fun ks => keyDesc ks = descEnc C par)
      = ((R.map (fun u => (fun k' => u (is k') : Tuple T n₁))).dedup).map (encK C par) := by
  classical
  rw [Multiset.dedup_filter_comm, Multiset.filter_map]
  have hf : Q.filter ((fun ks : Tuple T (k * (7 + k) + n₁ * (7 + k)) =>
      keyDesc ks = descEnc C par) ∘ (fun u => (fun x => u (gKeyIdx is x))))
      = Q.filter (fun r => descP (P := 0) r = descEnc C par) :=
    Multiset.filter_congr (fun r _ => by simp only [Function.comp, keyDesc_key])
  rw [hf, hsl, Multiset.map_map, ← Multiset.dedup_map_of_injective (encK_injective C par),
    Multiset.map_map]
  congr 2
  funext v
  exact key_rowEnc C is par v

/-- **The group of an encoded key** is the encoding of the group. -/
theorem group_slice {C : Finset T} {par : Fin k → T} (is : Tuple (Fin m) n₁)
    {Q : Multiset (Tuple T ((k + m) * (7 + k)))} {R : Multiset (Tuple T m)}
    (hsl : Q.filter (fun r => descP (P := 0) r = descEnc C par) = R.map (rowEnc C par))
    (g : Tuple T n₁) :
    Q.filter (fun u => ∀ x, u (gKeyIdx is x) = encK C par g x)
      = (R.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map (rowEnc C par) := by
  classical
  have h1 : Q.filter (fun u => ∀ x, u (gKeyIdx is x) = encK C par g x)
      = (Q.filter (fun r => descP (P := 0) r = descEnc C par)).filter
          (fun u => ∀ x, u (gKeyIdx is x) = encK C par g x) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr (fun u _ => ⟨fun h => ⟨h, ?_⟩, And.left⟩)
    rw [← keyDesc_key is u, ← keyDesc_encK C par g]
    exact congrArg keyDesc (funext h)
  rw [h1, hsl, Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr (fun v _ => ?_)
  show (∀ x, rowEnc C par v (gKeyIdx is x) = encK C par g x) ↔ _
  rw [← funext_iff, key_rowEnc]
  show encK C par (fun k' => v (is k')) = encK C par g ↔ _
  rw [(encK_injective C par).eq_iff, funext_iff]

/-- **The symbolic grouping, under the descriptor of a parameter row**,
emits the encodings of the keys the grouping forms at that row, each with
the counts the grouping computes there. -/
theorem gammaRows_slice {C : Finset T} (par : Fin k → T) (is : Tuple (Fin m) n₁)
    (ts : Tuple (TermIn T (k + c) m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (keep : Fin n₂ → Option (Selection T m)) (ord : GroupOrder T m)
    (hts : ∀ j, (ts j).noFun = true) (hfs : ∀ j, (fs j).ReadsCount)
    (hkeep : ∀ j φ, keep j = some φ → φ.noFun = true ∧ ∀ a ∈ φ.consts, CG C a)
    (Q : Multiset (Tuple T ((k + m) * (7 + k)))) (R : Multiset (Tuple T m))
    (hR : ∀ v ∈ R, ∀ i, GoodVal (C := C) par (v i))
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0))))
    (γ : Fin c → T) :
    (gammaRows (gKeyIdx is) (fun j => termV (ts j)) fs
        (fun j => (keep j).map (fun φ => (transSel 0 φ).toSel)) .unord Q γ).filter
          (fun x => keyDesc (M := n₁ * (7 + k)) (fun i => x (Fin.castAdd n₂ i)) = descEnc C par)
      = (gammaRows is ts fs keep ord R (Fin.append par γ)).map (fun y =>
          Fin.append (encK C par (fun t => y (Fin.castAdd n₂ t)))
            (fun j => y (Fin.natAdd n₁ j))) := by
  classical
  have hsl := slice_eq_map_rowEnc hQ
  have hkeys := keys_slice is hsl
  have hgroup := group_slice is hsl
  unfold gammaRows
  rw [Multiset.filter_map]
  have hcomp : Multiset.filter ((fun x : Tuple T ((k * (7 + k) + n₁ * (7 + k)) + n₂) =>
      keyDesc (M := n₁ * (7 + k)) (fun i => x (Fin.castAdd n₂ i)) = descEnc C par) ∘
        (fun g => Fin.append g (fun j => (fs j) ((Relation.groupSeqOptOrd (gKeyIdx is) .unord Q g
          ((keep j).map (fun φ => (transSel 0 φ).toSel))).map
            (fun v => (termV (ts j)).eval v γ)))))
        ((Q.map (fun u => (fun x => u (gKeyIdx is x)
          : Tuple T (k * (7 + k) + n₁ * (7 + k))))).dedup)
      = ((Q.map (fun u => (fun x => u (gKeyIdx is x)
          : Tuple T (k * (7 + k) + n₁ * (7 + k))))).dedup).filter
        (fun ks => keyDesc ks = descEnc C par) :=
    Multiset.filter_congr (fun ks _ => by
      simp only [Function.comp]
      rw [show (fun i => (Fin.append ks _ : Tuple T _) (Fin.castAdd n₂ i)) = ks from
        funext fun i => Fin.append_left _ _ i])
  rw [hcomp, hkeys, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  simp only [Function.comp, Fin.append_left, Fin.append_right]
  congr 1
  funext j
  rw [readsCount_groupSeq (hfs j), readsCount_groupSeq (hfs j)]
  refine congrArg (hfs j).choose ?_
  have hg := hgroup g
  rw [show (Q.filter (fun u => ∀ x, u (gKeyIdx is x) = encK C par g x)) = _ from hg,
    Multiset.filter_map, Multiset.map_map, Multiset.countP_map, Multiset.countP_map]
  simp only [Multiset.filter_filter]
  congr 1
  apply Multiset.filter_congr
  intro v hv
  simp only [Function.comp]
  rw [keepsOpt_transSel par (keep j) (hkeep j) v (hR v hv), isNull_termV C (ts j) (hts j) par v γ]

/-! ## From the grouping's rows to symbolic rows -/

/-- **The cells of a grouping's row**: the descriptor and key cells as
they are, each aggregate column as a concrete cell. -/
def gOutSA (n₁ n₂ : ℕ) :
    Fin ((k + (n₁ + n₂)) * (7 + k) + 0) → SA T c ((k * (7 + k) + n₁ * (7 + k)) + n₂) :=
  fun x => Fin.addCases (motive := fun _ => SA T c _)
    (fun i₀ => .col (Fin.castAdd n₂ (Fin.castAdd _ (ci i₀ (finProdFinEquiv.symm x).2))))
    (fun t => Fin.addCases (motive := fun _ => SA T c _)
      (fun t₁ => .col (Fin.castAdd n₂ (Fin.natAdd _ (ci t₁ (finProdFinEquiv.symm x).2))))
      (fun t₂ => concCols (.col (Fin.natAdd _ t₂)) (finProdFinEquiv.symm x).2) t)
    (finProdFinEquiv.symm x).1

/-- **A grouping's encoded row is a symbolic row**, its aggregate values
being values of the cut. -/
theorem gOutSA_eval (C : Finset T) (par : Fin k → T) (g : Tuple T n₁) (a : Tuple T n₂)
    (γ : Fin c → T) (ha : ∀ j, CG C (a j)) :
    (fun x => (gOutSA (k := k) n₁ n₂ x).eval (Fin.append (encK C par g) a) γ)
      = rowEncP C par (Fin.append g a) (Fin.elim0 : Tuple T 0) := by
  refine rowEncP_ext C par _ _ _ (fun i j => ?_) (fun z => z.elim0)
  show (gOutSA n₁ n₂ (Fin.castAdd 0 (finProdFinEquiv (i, j)))).eval _ γ = _
  unfold gOutSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (i, j)) = finProdFinEquiv (i, j) from rfl,
    Equiv.symm_apply_apply]
  refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
  · rw [Fin.addCases_left, Fin.append_left]
    show Fin.append (encK C par g) a (Fin.castAdd n₂ _) = _
    rw [Fin.append_left, encK, Fin.append_left]
    show cellOf (descEnc C par) i₀ j = _
    rw [descEnc, cellOf_ofCells]
  · rw [Fin.addCases_right, Fin.append_right]
    refine Fin.addCases (fun t₁ => ?_) (fun t₂ => ?_) t
    · rw [Fin.addCases_left, Fin.append_left]
      show Fin.append (encK C par g) a (Fin.castAdd n₂ _) = _
      rw [Fin.append_left, encK, Fin.append_right]
      show cellOf (ofCells _) t₁ j = _
      rw [cellOf_ofCells]
    · rw [Fin.addCases_right, Fin.append_right, concCols_eval]
      show enc C k (.conc (Fin.append (encK C par g) a (Fin.natAdd _ t₂))) j = _
      rw [Fin.append_right, vcode_of_mem par (ha t₂)]

theorem descP_gOutSA (x : Tuple T ((k * (7 + k) + n₁ * (7 + k)) + n₂)) (γ : Fin c → T) :
    descP (P := 0) (fun y => (gOutSA (k := k) n₁ n₂ y).eval x γ)
      = keyDesc (M := n₁ * (7 + k)) (fun i => x (Fin.castAdd n₂ i)) := by
  funext y
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [descP, ofCells, Equiv.symm_apply_apply]
  show (gOutSA n₁ n₂ (Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd (n₁ + n₂) i, j)))).eval x γ = _
  unfold gOutSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd (n₁ + n₂) i, j))
      = finProdFinEquiv (Fin.castAdd (n₁ + n₂) i, j) from rfl,
    Equiv.symm_apply_apply, Fin.addCases_left]
  rfl

/-- **The symbolic grouping's slice**: the encodings of the grouping's
rows, where its aggregate values are values of the cut. -/
theorem sliceIs_symGamma {C : Finset T} (par : Fin k → T) (is : Tuple (Fin m) n₁)
    (ts : Tuple (TermIn T (k + c) m) n₂) (fs : Tuple (SeqAggFunc T) n₂)
    (keep : Fin n₂ → Option (Selection T m)) (ord : GroupOrder T m)
    (hts : ∀ j, (ts j).noFun = true) (hfs : ∀ j, (fs j).ReadsCount)
    (hkeep : ∀ j φ, keep j = some φ → φ.noFun = true ∧ ∀ a ∈ φ.consts, CG C a)
    (Q : Multiset (Tuple T ((k + m) * (7 + k)))) (R : Multiset (Tuple T m))
    (hR : ∀ v ∈ R, ∀ i, GoodVal (C := C) par (v i))
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0))))
    (γ : Fin c → T)
    (hcnt : ∀ y ∈ gammaRows is ts fs keep ord R (Fin.append par γ),
      ∀ j, CG C (y (Fin.natAdd n₁ j))) :
    SliceIs (P := 0) C par ((gammaRows (gKeyIdx is) (fun j => termV (ts j)) fs
        (fun j => (keep j).map (fun φ => (transSel 0 φ).toSel)) .unord Q γ).map
          (fun x y => (gOutSA (k := k) n₁ n₂ y).eval x γ))
      ((gammaRows is ts fs keep ord R (Fin.append par γ)).map
        fun v => (v, (Fin.elim0 : Tuple T 0))) := by
  unfold SliceIs slice encAll
  rw [Multiset.filter_map]
  simp only [Function.comp, descP_gOutSA]
  rw [gammaRows_slice par is ts fs keep ord hts hfs hkeep Q R hR hQ γ, Multiset.map_map,
    Multiset.map_map]
  refine Multiset.map_congr rfl (fun y hy => ?_)
  simp only [Function.comp]
  rw [gOutSA_eval C par _ _ γ (hcnt y hy)]
  congr 1
  funext x
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · rw [Fin.append_left]
  · rw [Fin.append_right]

/-! ## Second-level aggregation -/

/-- **The rows a second-level aggregation emits** from its input. -/
noncomputable def nestRows {c' m' : ℕ} {κ' : Fin m' → ColKind} (is : Tuple (Fin m') n₁)
    (p : ProjColIn T c' κ') (f : Multiset T → T) (r : Multiset (Tuple T m')) (γ : Fin c' → T) :
    Multiset (Tuple T (n₁ + 1)) :=
  ((r.map (fun u => (fun k' => u (is k') : Tuple T n₁))).dedup).map (fun g => Fin.append g
    (fun _ : Fin 1 => f ((r.filter (fun u => (fun k' => u (is k') : Tuple T n₁) = g)).map
      (fun u => p.evalPlain u γ))))

/-- A counting aggregate read on a bag reads how many of its values are
not null. -/
theorem onBag_readsCount {g : SeqAggFunc T} (hg : g.Symmetric) (hr : g.ReadsCount)
    (M : Multiset T) :
    SeqAggFunc.onBag g hg M = hr.choose (M.countP (fun x => ValueType.isNull x = false)) := by
  induction M using Quot.inductionOn with
  | h L =>
    show SeqAggFunc.onBag g hg (↑L : Multiset T)
      = hr.choose ((↑L : Multiset T).countP (fun x => ValueType.isNull x = false))
    rw [SeqAggFunc.onBag_coe, hr.choose_spec, Multiset.coe_countP]
    exact congrArg hr.choose (List.countP_congr (fun x _ => by simp))

/-- **The value column of a projection column's cell.** -/
def projV {κ : Fin m → ColKind} (p : ProjColIn T (k + c) κ) :
    ProjColIn T c (ColKind.allReg ((k + m) * (7 + k) + 0)) :=
  .term ((projCS p).sa 0 (iV k)).toG

/-- **A projection column read on an encoded row is null exactly when the
column is.** -/
theorem isNull_projV {C : Finset T} {κ : Fin m → ColKind} (p : ProjColIn T (k + c) κ)
    (hp : p.noFun = true) (hpc : ∀ a ∈ p.consts, CG C a) (par : Fin k → T) (v : Tuple T m)
    (γ : Fin c → T) (hamb : ∀ j, CG C (γ j)) :
    ValueType.isNull ((projV p).evalPlain (rowEnc C par v) γ)
      = ValueType.isNull (p.evalPlain v (Fin.append par γ)) := by
  show ValueType.isNull ((((projCS p).sa 0 (iV k)).toG).evalPlain (rowEnc C par v) γ) = _
  rw [SA.evalPlain_toG, ← rowEncP_elim0 C par v,
    CS.eval_sa 0 (projCS p) par γ v _ (fun a h => by rw [h] at *; exact hamb a)
      (fun a h => hpc a (projCS_const p hp h)),
    isNull_enc_V, projCS_val p hp]

/-- **The symbolic second-level aggregation, under the descriptor of a
parameter row**, emits the encodings of the keys with the values the
aggregation computes there. -/
theorem nestRows_slice {C : Finset T} (par : Fin k → T) (is : Tuple (Fin m) n₁)
    {κ : Fin m → ColKind} (p : ProjColIn T (k + c) κ) (hp : p.noFun = true)
    (hpc : ∀ a ∈ p.consts, CG C a) (g' : SeqAggFunc T) (hg : g'.Symmetric) (hr : g'.ReadsCount)
    (Q : Multiset (Tuple T ((k + m) * (7 + k)))) (R : Multiset (Tuple T m))
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0))))
    (γ : Fin c → T) (hamb : ∀ j, CG C (γ j)) :
    (nestRows (κ' := ColKind.allReg ((k + m) * (7 + k))) (gKeyIdx is) (projV p)
        (SeqAggFunc.onBag g' hg) Q γ).filter
          (fun x => keyDesc (M := n₁ * (7 + k)) (fun i => x (Fin.castAdd 1 i)) = descEnc C par)
      = (nestRows is p (SeqAggFunc.onBag g' hg) R (Fin.append par γ)).map (fun y =>
          Fin.append (encK C par (fun t => y (Fin.castAdd 1 t)))
            (fun j => y (Fin.natAdd n₁ j))) := by
  classical
  have hsl := slice_eq_map_rowEnc hQ
  have hkeys := keys_slice is hsl
  unfold nestRows
  rw [Multiset.filter_map]
  have hcomp : ∀ (F : Tuple T (k * (7 + k) + n₁ * (7 + k)) → Fin 1 → T),
      Multiset.filter ((fun x : Tuple T ((k * (7 + k) + n₁ * (7 + k)) + 1) =>
        keyDesc (M := n₁ * (7 + k)) (fun i => x (Fin.castAdd 1 i)) = descEnc C par) ∘
          (fun g => Fin.append g (F g)))
        ((Q.map (fun u => (fun x => u (gKeyIdx is x)
          : Tuple T (k * (7 + k) + n₁ * (7 + k))))).dedup)
      = ((Q.map (fun u => (fun x => u (gKeyIdx is x)
          : Tuple T (k * (7 + k) + n₁ * (7 + k))))).dedup).filter
        (fun ks => keyDesc ks = descEnc C par) := fun F =>
    Multiset.filter_congr (fun ks _ => by
      simp only [Function.comp]
      rw [show (fun i => (Fin.append ks _ : Tuple T _) (Fin.castAdd 1 i)) = ks from
        funext fun i => Fin.append_left _ _ i])
  rw [hcomp, hkeys, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  simp only [Function.comp, Fin.append_left, Fin.append_right]
  congr 1
  funext j
  rw [onBag_readsCount hg hr, onBag_readsCount hg hr]
  refine congrArg hr.choose ?_
  have hg' : Q.filter (fun u => (fun x => u (gKeyIdx is x) : Tuple T _) = encK C par g)
      = (R.filter (fun u => (fun k' => u (is k') : Tuple T n₁) = g)).map (rowEnc C par) := by
    have := group_slice is hsl g
    simp only [← funext_iff] at this
    exact this
  rw [hg', Multiset.map_map, Multiset.countP_map, Multiset.countP_map]
  congr 1
  apply Multiset.filter_congr
  intro v hv
  simp only [Function.comp]
  rw [isNull_projV p hp hpc par v γ hamb]

/-! ## Aggregation without grouping

The scalar aggregation emits one row on every input, the empty one
included, so its symbolic counterpart emits one row under every
descriptor: it groups by the descriptor the union of the input's rows,
tagged `ValueType.nonzero`, and of one padding row per descriptor, tagged
`0`, and its aggregates read only the rows tagged `ValueType.nonzero`
through a `FILTER` clause. -/

/-- The descriptor columns of a tagged symbolic row. -/
def sKeyIdx : Tuple (Fin ((k + m) * (7 + k) + 1)) (k * (7 + k)) :=
  fun y => Fin.castAdd 1 (ci (Fin.castAdd m (finProdFinEquiv.symm y).1) (finProdFinEquiv.symm y).2)

/-- **The clause keeping the input's rows**: the tag is `ValueType.nonzero`. -/
def tagSel {N : ℕ} : Selection T (N + 1) :=
  .BT (.SYNEQ (.index (Fin.natAdd N 0)) (.const ValueType.nonzero))

theorem keeps_tagSel {N : ℕ} (r : Tuple T N) (a : T) :
    (tagSel (N := N)).keeps (Fin.append r (fun _ : Fin 1 => a))
      = decide (a = ValueType.nonzero) := by
  unfold tagSel Selection.keeps
  refine decide_eq_decide.mpr ?_
  show CompOp.syneq.eval3 (Fin.append r (fun _ : Fin 1 => a) (Fin.natAdd N 0))
    ValueType.nonzero = Kleene.true ↔ _
  rw [CompOp.syneq_eval3_eq_true_iff, Fin.append_right]

omit [ValueType T] in
theorem key_tagged (r : Tuple T ((k + m) * (7 + k))) (a : T) :
    (fun y => (Fin.append r (fun _ : Fin 1 => a) : Tuple T _) (sKeyIdx (m := m) y))
      = descP (P := 0) r := by
  funext y
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [sKeyIdx, descP, ofCells, Equiv.symm_apply_apply]
  exact Fin.append_left _ _ _

/-- **The symbolic scalar aggregation's rows under a descriptor**: one row,
the descriptor with the aggregation's values at the parameter row. -/
theorem gammaScalar_slice {C : Finset T} (par : Fin k → T) (ts : Tuple (TermIn T (k + c) m) n₂)
    (fs : Tuple (SeqAggFunc T) n₂) (ord : GroupOrder T m)
    (hts : ∀ j, (ts j).noFun = true) (hfs : ∀ j, (fs j).ReadsCount)
    (Q : Multiset (Tuple T ((k + m) * (7 + k)))) (R : Multiset (Tuple T m))
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0))))
    (Pad : Multiset (Tuple T ((k + m) * (7 + k))))
    (hpad : (Pad.map (fun r => descP (P := 0) r)).Nodup
      ∧ descEnc C par ∈ Pad.map (fun r => descP (P := 0) r))
    (γ : Fin c → T) :
    (gammaRows sKeyIdx (fun j => (termV (ts j)).widen 1) fs (fun _ => some tagSel) .unord
        (Pad.map (fun r => Fin.append r (fun _ : Fin 1 => (0 : T)))
          + Q.map (fun r => Fin.append r (fun _ : Fin 1 => ValueType.nonzero))) γ).filter
          (fun x => (fun i => x (Fin.castAdd n₂ i) : Tuple T (k * (7 + k))) = descEnc C par)
      = {Fin.append (descEnc C par) (fun j => (fs j) ((Relation.groupSeqOrd
          (fun k' : Fin 0 => k'.elim0) ord R (fun k' : Fin 0 => k'.elim0)).map
            (fun v => (ts j).eval v (Fin.append par γ))))} := by
  classical
  have hsl := slice_eq_map_rowEnc hQ
  set U := Pad.map (fun r => (Fin.append r (fun _ : Fin 1 => (0 : T)) : Tuple T _))
    + Q.map (fun r => (Fin.append r (fun _ : Fin 1 => ValueType.nonzero) : Tuple T _)) with hU
  have hkey : ∀ r : Tuple T ((k + m) * (7 + k)), ∀ a : T,
      (fun k' => (Fin.append r (fun _ : Fin 1 => a) : Tuple T _) (sKeyIdx (m := m) k'))
        = descP (P := 0) r := fun r a => key_tagged r a
  -- the keys under the descriptor: the descriptor alone
  have hkeys : ((U.map (fun u => (fun k' => u (sKeyIdx (m := m) k')
      : Tuple T (k * (7 + k))))).dedup).filter
      (fun g => g = descEnc C par) = {descEnc C par} := by
    refine (Multiset.Nodup.ext ((Multiset.nodup_dedup _).filter _)
      (Multiset.nodup_singleton _)).mpr (fun x => ?_)
    rw [Multiset.mem_filter, Multiset.mem_dedup, Multiset.mem_singleton]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    subst h
    rw [hU, Multiset.map_add, Multiset.mem_add]
    left
    rw [Multiset.map_map]
    have : (fun u => (fun k' => u (sKeyIdx (m := m) k') : Tuple T _)) ∘
        (fun r => (Fin.append r (fun _ : Fin 1 => (0 : T)) : Tuple T _))
        = fun r => descP (P := 0) r := funext fun r => hkey r 0
    rw [this]
    exact hpad.2
  unfold gammaRows
  rw [Multiset.filter_map]
  simp only [Function.comp, Fin.append_left]
  erw [hkeys, Multiset.map_singleton]
  congr 2
  funext j
  rw [readsCount_groupSeq (hfs j), ← Relation.groupSeqOptOrd_none, readsCount_groupSeq (hfs j)]
  refine congrArg (hfs j).choose ?_
  -- the group: the input's rows under the descriptor, tagged
  have hgrp : (U.filter (fun u => ∀ k' : Fin (k * (7 + k)),
        u (sKeyIdx (m := m) k') = descEnc C par k')).filter
          (fun u => Selection.keepsOpt (some tagSel) u = true)
      = (R.map (rowEnc C par)).map
          (fun r => (Fin.append r (fun _ : Fin 1 => ValueType.nonzero) : Tuple T _)) := by
    rw [hU, Multiset.filter_add, Multiset.filter_add, ← hsl, Multiset.filter_map,
      Multiset.filter_map, Multiset.filter_map, Multiset.filter_map]
    have h0 : Multiset.filter ((fun u => Selection.keepsOpt (some tagSel) u = true) ∘
        (fun r => (Fin.append r (fun _ : Fin 1 => (0 : T)) : Tuple T _)))
          (Multiset.filter ((fun u => ∀ k' : Fin (k * (7 + k)),
            u (sKeyIdx (m := m) k') = descEnc C par k') ∘
              (fun r => (Fin.append r (fun _ : Fin 1 => (0 : T)) : Tuple T _))) Pad) = 0 :=
      Multiset.filter_eq_nil.mpr (fun r _ h => by
        simp only [Function.comp, Selection.keepsOpt, keeps_tagSel] at h
        exact ValueType.nonzero_ne_zero (T := T) (of_decide_eq_true h).symm)
    rw [h0, Multiset.map_zero, zero_add, Multiset.filter_filter]
    congr 1
    refine Multiset.filter_congr (fun r _ => ?_)
    simp only [Function.comp, Selection.keepsOpt, keeps_tagSel, decide_true, true_and]
    rw [← funext_iff, hkey]
  erw [hgrp, Multiset.map_map, Multiset.map_map, Multiset.countP_map, Multiset.countP_map]
  have hall : (R : Multiset (Tuple T m)).filter (fun u => ∀ k' : Fin 0,
      u ((fun k' : Fin 0 => k'.elim0) k') = (fun k' : Fin 0 => k'.elim0) k') = R :=
    Multiset.filter_eq_self.mpr (fun _ _ k' => k'.elim0)
  have hn : R.filter (fun u => Selection.keepsOpt (none : Option (Selection T m)) u = true) = R :=
    Multiset.filter_eq_self.mpr (fun _ _ => rfl)
  rw [hall]
  erw [hn]
  congr 1
  refine Multiset.filter_congr (fun v _ => ?_)
  simp only [Function.comp]
  rw [TermIn.eval_widen, isNull_termV C (ts j) (hts j) par v γ]

/-- **The cells of a scalar aggregation's row**: the descriptor's cells,
then each aggregate column as a concrete cell. -/
def sOutSA (n₂ : ℕ) : Fin ((k + n₂) * (7 + k) + 0) → SA T c (k * (7 + k) + n₂) :=
  fun x => Fin.addCases (motive := fun _ => SA T c _)
    (fun i₀ => .col (Fin.castAdd n₂ (ci i₀ (finProdFinEquiv.symm x).2)))
    (fun t => concCols (.col (Fin.natAdd _ t)) (finProdFinEquiv.symm x).2)
    (finProdFinEquiv.symm x).1

theorem sOutSA_eval (C : Finset T) (par : Fin k → T) (a : Tuple T n₂) (γ : Fin c → T)
    (ha : ∀ j, CG C (a j)) :
    (fun x => (sOutSA (k := k) n₂ x).eval (Fin.append (descEnc C par) a) γ)
      = rowEncP C par a (Fin.elim0 : Tuple T 0) := by
  refine rowEncP_ext C par _ _ _ (fun i j => ?_) (fun z => z.elim0)
  show (sOutSA n₂ (Fin.castAdd 0 (finProdFinEquiv (i, j)))).eval _ γ = _
  unfold sOutSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (i, j)) = finProdFinEquiv (i, j) from rfl,
    Equiv.symm_apply_apply]
  refine Fin.addCases (fun i₀ => ?_) (fun t => ?_) i
  · rw [Fin.addCases_left, Fin.append_left]
    show Fin.append (descEnc C par) a (Fin.castAdd n₂ _) = _
    rw [Fin.append_left]
    show cellOf (descEnc C par) i₀ j = _
    rw [descEnc, cellOf_ofCells]
  · rw [Fin.addCases_right, Fin.append_right, concCols_eval]
    show enc C k (.conc (Fin.append (descEnc C par) a (Fin.natAdd _ t))) j = _
    rw [Fin.append_right, vcode_of_mem par (ha t)]

theorem descP_sOutSA (x : Tuple T (k * (7 + k) + n₂)) (γ : Fin c → T) :
    descP (P := 0) (fun y => (sOutSA (k := k) n₂ y).eval x γ)
      = (fun i => x (Fin.castAdd n₂ i) : Tuple T (k * (7 + k))) := by
  funext y
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [descP, ofCells, Equiv.symm_apply_apply]
  show (sOutSA n₂ (Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd n₂ i, j)))).eval x γ = _
  unfold sOutSA
  rw [show Fin.castAdd 0 (finProdFinEquiv (Fin.castAdd n₂ i, j))
      = finProdFinEquiv (Fin.castAdd n₂ i, j) from rfl,
    Equiv.symm_apply_apply, Fin.addCases_left]
  rfl

/-- **The symbolic scalar aggregation's slice**: the encoding of the one
row the aggregation emits, its values being values of the cut. -/
theorem sliceIs_symGammaScalar {C : Finset T} (par : Fin k → T)
    (ts : Tuple (TermIn T (k + c) m) n₂) (fs : Tuple (SeqAggFunc T) n₂) (ord : GroupOrder T m)
    (hts : ∀ j, (ts j).noFun = true) (hfs : ∀ j, (fs j).ReadsCount)
    (Q : Multiset (Tuple T ((k + m) * (7 + k)))) (R : Multiset (Tuple T m))
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0))))
    (Pad : Multiset (Tuple T ((k + m) * (7 + k))))
    (hpad : (Pad.map (fun r => descP (P := 0) r)).Nodup
      ∧ descEnc C par ∈ Pad.map (fun r => descP (P := 0) r))
    (γ : Fin c → T)
    (hcnt : ∀ j, CG C ((fs j) ((Relation.groupSeqOrd (fun k' : Fin 0 => k'.elim0) ord R
      (fun k' : Fin 0 => k'.elim0)).map (fun v => (ts j).eval v (Fin.append par γ))))) :
    SliceIs (P := 0) C par ((gammaRows sKeyIdx (fun j => (termV (ts j)).widen 1) fs
        (fun _ => some tagSel) .unord
        (Pad.map (fun r => Fin.append r (fun _ : Fin 1 => (0 : T)))
          + Q.map (fun r => Fin.append r (fun _ : Fin 1 => ValueType.nonzero))) γ).map
          (fun x y => (sOutSA (k := k) n₂ y).eval x γ))
      {((fun j => (fs j) ((Relation.groupSeqOrd (fun k' : Fin 0 => k'.elim0) ord R
          (fun k' : Fin 0 => k'.elim0)).map (fun v => (ts j).eval v (Fin.append par γ))) :
            Tuple T n₂), (Fin.elim0 : Tuple T 0))} := by
  unfold SliceIs slice encAll
  rw [Multiset.filter_map]
  simp only [Function.comp, descP_sOutSA]
  rw [gammaScalar_slice par ts fs ord hts hfs Q R hQ Pad hpad γ, Multiset.map_singleton,
    Multiset.map_singleton, sOutSA_eval C par _ γ hcnt]

/-- **The symbolic second-level aggregation's slice**, its values being
values of the cut. -/
theorem sliceIs_symGammaNest {C : Finset T} (par : Fin k → T) (is : Tuple (Fin m) n₁)
    {κ : Fin m → ColKind} (p : ProjColIn T (k + c) κ) (hp : p.noFun = true)
    (hpc : ∀ a ∈ p.consts, CG C a) (g' : SeqAggFunc T) (hg : g'.Symmetric) (hr : g'.ReadsCount)
    (Q : Multiset (Tuple T ((k + m) * (7 + k)))) (R : Multiset (Tuple T m))
    (hQ : SliceIs (P := 0) C par Q (R.map fun v => (v, (Fin.elim0 : Tuple T 0))))
    (γ : Fin c → T) (hamb : ∀ j, CG C (γ j))
    (hcnt : ∀ y ∈ nestRows is p (SeqAggFunc.onBag g' hg) R (Fin.append par γ),
      CG C (y (Fin.natAdd n₁ 0))) :
    SliceIs (P := 0) C par ((nestRows (κ' := ColKind.allReg ((k + m) * (7 + k))) (gKeyIdx is)
        (projV p) (SeqAggFunc.onBag g' hg) Q γ).map
          (fun x y => (gOutSA (k := k) n₁ 1 y).eval x γ))
      ((nestRows is p (SeqAggFunc.onBag g' hg) R (Fin.append par γ)).map
        fun v => (v, (Fin.elim0 : Tuple T 0))) := by
  unfold SliceIs slice encAll
  rw [Multiset.filter_map]
  simp only [Function.comp, descP_gOutSA]
  rw [nestRows_slice par is p hp hpc g' hg hr Q R hQ γ hamb, Multiset.map_map,
    Multiset.map_map]
  refine Multiset.map_congr rfl (fun y hy => ?_)
  simp only [Function.comp]
  rw [gOutSA_eval C par _ _ γ (fun j => by rw [Subsingleton.elim j 0]; exact hcnt y hy)]
  congr 1
  funext x
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · rw [Fin.append_left]
  · rw [Fin.append_right]

end Sym
