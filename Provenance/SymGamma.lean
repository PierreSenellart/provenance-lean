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
  have hsl : Q.filter (fun r => descP (P := 0) r = descEnc C par) = R.map (rowEnc C par) := by
    have := hQ
    unfold SliceIs encAll slice at this
    rw [this, Multiset.map_map]
    exact Multiset.map_congr rfl (fun v _ => rowEncP_elim0 C par v)
  -- the keys of the symbolic grouping under the descriptor
  have hkeys : ((Q.map (fun u => (fun x => u (gKeyIdx is x)
      : Tuple T (k * (7 + k) + n₁ * (7 + k))))).dedup).filter
        (fun ks => keyDesc ks = descEnc C par)
      = ((R.map (fun u => (fun k' => u (is k') : Tuple T n₁))).dedup).map (encK C par) := by
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
  -- the group of an encoded key
  have hgroup : ∀ g : Tuple T n₁,
      Q.filter (fun u => ∀ x, u (gKeyIdx is x) = encK C par g x)
        = (R.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k')).map (rowEnc C par) := by
    intro g
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

end Sym
