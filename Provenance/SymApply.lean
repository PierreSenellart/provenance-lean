import Provenance.SymMatch

/-!
# An apply written with products

An apply `L ⊳ R` reads its right side at each row of its left side. Its
right side's table (`Sym.tabQ`) holds the encodings of the right side's
rows under every descriptor; so the apply is the product of its left side
with the descriptors, the table and enough copies of a pool of values,
where a row's descriptor is its own (`Sym.matchSP`), the table's row is
filed under that descriptor, and the copied values are the ones the
table's cells code (`Sym.decCell`) – projected on the left row and the
decoded values (`Sym.applyX`, `Sym.evaluatePlain_applyX`). No row of the
left side is read twice: the left side appears once, as the last factor,
so the construction applies as well inside a recursive term.
-/

variable {T : Type} [ValueType T]

namespace Sym

section Construction

variable {c k n₂ : ℕ}

/-- The columns of a row of the product: its left row. -/
def uIdx (k n₂ : ℕ) (i : Fin k) : Fin (((k * (7 + k) + (k + n₂) * (7 + k)) + n₂) + k) :=
  Fin.natAdd _ i

/-- The cell `i` of the row's descriptor. -/
def dIdx (k n₂ : ℕ) (i : Fin k) (j : Fin (7 + k)) :
    Fin (((k * (7 + k) + (k + n₂) * (7 + k)) + n₂) + k) :=
  Fin.castAdd k (Fin.castAdd n₂ (Fin.castAdd ((k + n₂) * (7 + k)) (ci i j)))

/-- A column of the row's table row. -/
def tIdx (k n₂ : ℕ) (z : Fin ((k + n₂) * (7 + k))) :
    Fin (((k * (7 + k) + (k + n₂) * (7 + k)) + n₂) + k) :=
  Fin.castAdd k (Fin.castAdd n₂ (Fin.natAdd (k * (7 + k)) z))

/-- The `j`-th decoded value. -/
def wIdx (k n₂ : ℕ) (j : Fin n₂) : Fin (((k * (7 + k) + (k + n₂) * (7 + k)) + n₂) + k) :=
  Fin.castAdd k (Fin.natAdd (k * (7 + k) + (k + n₂) * (7 + k)) j)

/-- **The row's descriptor, the table row filed under it, and the values
its cells code.** -/
def applyPred (k n₂ : ℕ) : SP T c (((k * (7 + k) + (k + n₂) * (7 + k)) + n₂) + k) :=
  .and (matchSP (fun i => .col (uIdx k n₂ i)) (fun i j => .col (dIdx k n₂ i j)))
    (.and (andAll ((List.finRange k).flatMap (fun i => (List.finRange (7 + k)).map (fun j =>
        .atom .syneq (.col (dIdx k n₂ i j)) (.col (tIdx k n₂ (ci (Fin.castAdd n₂ i) j)))))))
      (andAll ((List.finRange n₂).map (fun j => decCell (.col (wIdx k n₂ j))
        (fun z => .col (tIdx k n₂ (ci (Fin.natAdd k j) z))) (fun i => .col (uIdx k n₂ i))
        (fun i j' => .col (dIdx k n₂ i j'))))))

/-- The values a decoded value is taken from: a pool, and the cut. -/
noncomputable def valsQ (f : ℕ → String) (env : SymEnv T k c)
    (VQ : AggQueryIn T c 1 (ColKind.allReg 1)) : AggQueryIn T c 1 (ColKind.allReg 1) :=
  AggQueryIn.dedupG (u2 f VQ env.CQ)

/-- **An apply, with products**: the left side `L` (read once), the right
side `R`'s table, and a pool `VQ` holding the left side's values. -/
noncomputable def applyX (cnt : SeqAggFunc T) (f : ℕ → String) {l : List (String × ℕ)}
    {κ₂ : Fin n₂ → ColKind} (L : AggQueryIn T c k (ColKind.allReg k) l)
    (R : AggQueryIn T (k + c) n₂ κ₂) (VQ : AggQueryIn T c 1 (ColKind.allReg 1)) :
    AggQueryIn T c (k + n₂) (ColKind.allReg (k + n₂)) l :=
  projQ (Fin.append (fun i => SA.col (uIdx k n₂ i)) (fun j => SA.col (wIdx k n₂ j)))
    (AggQueryIn.Sel (applyPred k n₂).toGen
      (prodR (prodR (prodR (tabEnv cnt (part f 0) R).Desc (tabQ cnt (part f 0) R))
        (powU (valsQ (part f 1) (tabEnv cnt (part f 0) R) VQ) n₂)) L)
      (SelOK.of_noAggAtom (SP.hasAggAtom_toGen _)))

end Construction

/-! ## The predicate on a row of the product -/

section PredEval

variable {c k n₂ : ℕ} (d : Tuple T (k * (7 + k))) (t : Tuple T ((k + n₂) * (7 + k)))
  (w : Tuple T n₂) (u : Tuple T k) (γ : Fin c → T)

/-- The row of the product. -/
abbrev prow : Tuple T (((k * (7 + k) + (k + n₂) * (7 + k)) + n₂) + k) :=
  Fin.append (Fin.append (Fin.append d t) w) u

omit [ValueType T] in
@[simp] theorem eval_uIdx (i : Fin k) :
    (SA.col (c := c) (uIdx k n₂ i)).eval (prow d t w u) γ = u i := by
  simp [uIdx, SA.eval, prow]

omit [ValueType T] in
@[simp] theorem eval_dIdx (i : Fin k) (j : Fin (7 + k)) :
    (SA.col (c := c) (dIdx k n₂ i j)).eval (prow d t w u) γ = d (ci i j) := by
  simp [dIdx, SA.eval, prow]

omit [ValueType T] in
@[simp] theorem eval_tIdx (z : Fin ((k + n₂) * (7 + k))) :
    (SA.col (c := c) (tIdx k n₂ z)).eval (prow d t w u) γ = t z := by
  simp [tIdx, SA.eval, prow]

omit [ValueType T] in
@[simp] theorem eval_wIdx (j : Fin n₂) :
    (SA.col (c := c) (wIdx k n₂ j)).eval (prow d t w u) γ = w j := by
  simp [wIdx, SA.eval, prow]

/-- **The predicate on a row of the product**: its three conjuncts. -/
theorem eval3_applyPred_true :
    (applyPred (c := c) k n₂).eval3 (prow d t w u) γ = Kleene.true ↔
      (matchSP (fun i => SA.col (c := c) (uIdx k n₂ i)) (fun i j => .col (dIdx k n₂ i j))).eval3
          (prow d t w u) γ = Kleene.true
        ∧ descP (n := n₂) (P := 0) t = d
        ∧ ∀ j, (decCell (SA.col (c := c) (wIdx k n₂ j))
            (fun z => .col (tIdx k n₂ (ci (Fin.natAdd k j) z)))
            (fun i => .col (uIdx k n₂ i)) (fun i j' => .col (dIdx k n₂ i j'))).eval3
              (prow d t w u) γ = Kleene.true := by
  unfold applyPred
  rw [SP.eval3_and', SP.eval3_and', Kleene.and_eq_true_iff, Kleene.and_eq_true_iff, andAll_true,
    andAll_true]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h
      funext x
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
      have := h _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange _,
        List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩⟩)
      rw [eval3_atom_syneq, eval_dIdx, eval_tIdx, Kleene.ofBool_eq_true_iff,
        decide_eq_true_eq] at this
      show t (cc 0 (Fin.castAdd n₂ (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = d (finProdFinEquiv (i, j))
      rw [Equiv.symm_apply_apply]
      exact this.symm
    · intro h p hp
      obtain ⟨i, -, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      rw [eval3_atom_syneq, eval_dIdx, eval_tIdx, Kleene.ofBool_eq_true_iff, decide_eq_true_eq,
        ← h]
      show t (cc 0 (Fin.castAdd n₂ (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = t (ci (Fin.castAdd n₂ i) j)
      rw [Equiv.symm_apply_apply]
      rfl
  · constructor
    · intro h j
      exact h _ (List.mem_map.mpr ⟨j, List.mem_finRange _, rfl⟩)
    · intro h p hp
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      exact h j

end PredEval

/-! ## Rearranging a product -/

theorem map_filter_eq_bind' {α ρ : Type} (s : Multiset α) (p : α → Prop) [DecidablePred p]
    (g : α → ρ) : (s.filter p).map g = s.bind (fun x => if p x then {g x} else 0) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.filter_cons, Multiset.cons_bind, ← ih]
    split <;> simp

/-- **A selection over a product of four relations, projected**, read
row of the last relation by row. -/
theorem filter_prod4 {α β γ δ E Z H ρ : Type} (Dq : Multiset α) (Tq : Multiset β) (Wq : Multiset γ)
    (Lv : Multiset δ) (f1 : α → β → E) (f2 : E → γ → Z) (f3 : Z → δ → H) (p : H → Prop)
    [DecidablePred p] (g : H → ρ) :
    ((((Dq.bind fun d => Tq.map (f1 d)).bind fun x => Wq.map (f2 x)).bind
      fun z => Lv.map (f3 z)).filter p).map g
      = Lv.bind (fun u => Dq.bind (fun d => Tq.bind (fun t =>
          (Wq.filter (fun w => p (f3 (f2 (f1 d t) w) u))).map
            (fun w => g (f3 (f2 (f1 d t) w) u))))) := by
  simp only [Multiset.bind_assoc, Multiset.bind_map, Multiset.filter_bind, Multiset.map_bind,
    Multiset.filter_map, map_filter_eq_bind', Function.comp]
  calc _ = Dq.bind (fun d => Tq.bind (fun t => Wq.bind (fun w => Lv.bind (fun u =>
        if p (f3 (f2 (f1 d t) w) u) then {g (f3 (f2 (f1 d t) w) u)} else 0)))) := by
        refine Multiset.bind_congr fun d _ => Multiset.bind_congr fun t _ =>
          Multiset.bind_congr fun w _ => Multiset.bind_congr fun u _ => ?_
        split <;> simp
    _ = Dq.bind (fun d => Tq.bind (fun t => Lv.bind (fun u => Wq.bind (fun w =>
        if p (f3 (f2 (f1 d t) w) u) then {g (f3 (f2 (f1 d t) w) u)} else 0)))) := by
        refine Multiset.bind_congr fun d _ => Multiset.bind_congr fun t _ => Multiset.bind_bind _ _
    _ = Dq.bind (fun d => Lv.bind (fun u => Tq.bind (fun t => Wq.bind (fun w =>
        if p (f3 (f2 (f1 d t) w) u) then {g (f3 (f2 (f1 d t) w) u)} else 0)))) := by
        refine Multiset.bind_congr fun d _ => Multiset.bind_bind _ _
    _ = _ := Multiset.bind_bind _ _

/-- A cell the cut produces holds a code. -/
theorem cellShape_code {C : Finset T} {k : ℕ} {x : Tuple T (7 + k)} (h : CellShape C k x) :
    ∃ cd : Code T, ShapeOK C k cd ∧ x = enc C k cd := by
  rcases h with ⟨a, ha, rfl⟩ | ⟨l, r, hl, hr, rfl⟩
  · exact ⟨.conc a, ha, rfl⟩
  · exact ⟨.fresh l r, ⟨hl, hr⟩, rfl⟩

/-- **Two codes of the shapes a cut produces have the same columns only if
they are equal.** -/
theorem enc_inj' {C : Finset T} {k : ℕ} {x y : Code T} (hx : ShapeOK C k x) (hy : ShapeOK C k y)
    (h : enc C k x = enc C k y) : x = y := by
  have hF := congrFun h (iF k)
  have hV := congrFun h (iV k)
  cases x with
  | conc a =>
    cases y with
    | conc b => rw [enc_conc_V, enc_conc_V] at hV; rw [hV]
    | fresh l r => rw [enc_conc_F, enc_fresh_F] at hF; exact absurd hF.symm nonzero_ne_zero'
  | fresh l r =>
    cases y with
    | conc b => rw [enc_conc_F, enc_fresh_F] at hF; exact absurd hF nonzero_ne_zero'
    | fresh l' r' =>
      have hB := congrFun h (iB k)
      rw [enc_fresh_V, enc_fresh_V] at hV
      rw [enc_fresh_B, enc_fresh_B] at hB
      have hl : l = l' := (withBot_eq_iff (C := C) l l').mpr ⟨hB, hV⟩
      have hr : r = r' := (therm_eq_iff' (T := T) hx.2 hy.2).mp (fun j => by
        have := congrFun h (iR j)
        rwa [enc_fresh_R, enc_fresh_R] at this)
      rw [hl, hr]

/-- A row's own code holds a cut's shape, the null being in the cut. -/
theorem shapeOK_code {C : Finset T} {k : ℕ} (hnull : ∀ a : T, ValueType.isNull a = true → a ∈ C)
    (par : Fin k → T) (i : Fin k) : ShapeOK C k (code C par i) := by
  by_cases h : IsFresh C (par i)
  · rw [code_of_fresh h]
    refine ⟨?_, (rank_code_lt i).le⟩
    cases hl : lo C (par i) with
    | bot => trivial
    | coe t => exact ⟨(lo_eq_coe hl).1, (lo_eq_coe hl).2.1⟩
  · rw [code_of_not_fresh h]
    show par i ∈ C
    by_contra hm
    cases hn : ValueType.isNull (par i)
    · exact h ⟨hm, hn⟩
    · exact hm (hnull _ hn)

/-! ## The apply, with products, computes the apply -/

section Correct

variable {c k n₂ : ℕ}

theorem rowEnc_out (C : Finset T) (par : Fin k → T) (v : Tuple T n₂) (j : Fin n₂)
    (z : Fin (7 + k)) : rowEnc C par v (ci (Fin.natAdd k j) z) = enc C k (vcode C par (v j)) z := by
  unfold rowEnc
  show ofCells _ (finProdFinEquiv (Fin.natAdd k j, z)) = _
  simp only [ofCells, Equiv.symm_apply_apply, Fin.append_right]

theorem descEnc_cell (C : Finset T) (par : Fin k → T) (i : Fin k) (j : Fin (7 + k)) :
    descEnc C par (ci i j) = enc C k (code C par i) j := by
  unfold descEnc
  show ofCells _ (finProdFinEquiv (i, j)) = _
  simp only [ofCells, Equiv.symm_apply_apply]

/-- **The apply, with products, computes the apply**, wherever the right
side settles at the left side's rows and the pool holds their values. -/
theorem evaluatePlain_applyX (Θ : Set (SeqAggFunc T)) {cnt : SeqAggFunc T}
    (hc : SeqAggFunc.Counts cnt) (f : ℕ → String) {l : List (String × ℕ)} {κ₂ : Fin n₂ → ColKind}
    (L : AggQueryIn T c k (ColKind.allReg k) l) (R : AggQueryIn T (k + c) n₂ κ₂)
    (VQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hU : R.usesOnly basisProdOps) (hsrc : SymSrc Θ R)
    (hfR : ∀ i, R.noMention (f i))
    (hfV : VQ.noMention (part f 1 0)) (D' : Database T) (γ : Fin c → T)
    (hset : ∀ u, Multiset.Mem (L.evaluatePlain D' γ) u → R.SettlesAt D' (Fin.append u γ))
    (hval : ∀ u, Multiset.Mem (L.evaluatePlain D' γ) u → ∀ i,
      u i ∈ valsU (VQ.evaluatePlain D' γ)) :
    ((applyX cnt f L R VQ).evaluatePlain D' γ : Multiset (Tuple T (k + n₂)))
      = (L.evaluatePlain D' γ : Multiset (Tuple T k)).bind (fun u =>
          (R.evaluatePlain D' (Fin.append u γ) : Multiset (Tuple T n₂)).map
            (fun v => (Fin.append u v : Tuple T (k + n₂)))) := by
  -- the environment and its cut
  have hcore : ∀ i, (cutCore cnt (part (part (part f 0) 1) 1) R).noMention
      (part (part (part f 0) 1) 0 i) := fun i => noMention_cutCore cnt _ _ R le_rfl (hfR _)
  have facts := mem_cutOf (part (part (part f 0) 1) 0) R.allConsts
    (cutCore cnt (part (part (part f 0) 1) 1) R) hcore D' γ
  have hCQ : ∀ i, (cutQ cnt (part (part f 0) 1) R).noMention (part (part f 0) 0 i) :=
    fun i => noMention_cutQ cnt _ R (hfR _)
  have henv := envOK_envOf (part (part f 0) 0) hc k (cutQ cnt (part (part f 0) 1) R) hCQ D' γ
    facts.1
  set C := cutAt (tabEnv cnt (part f 0) R) D' γ with hCdef
  have hnull : ∀ a : T, ValueType.isNull a = true → a ∈ C := facts.1
  -- the descriptors
  have hmemD := mem_descQ (fun i => part (part f 0) 0 (2 * i)) hc k (cutQ cnt (part (part f 0) 1) R)
    (fun i => hCQ _) D' γ
  -- the pool
  set Vq := valsQ (part f 1) (tabEnv cnt (part f 0) R) VQ with hVq
  have hVmem : ∀ a : T, (a ∈ valsU (VQ.evaluatePlain D' γ) ∨ a ∈ C) →
      Multiset.Mem (Vq.evaluatePlain D' γ) (fun _ => a) := by
    intro a ha
    rw [hVq, valsQ, AggQueryIn.evaluatePlain_dedupG]
    show (fun _ => a) ∈ Multiset.dedup _
    rw [Multiset.mem_dedup, u2]
    erw [AggQueryIn.evaluatePlain_sumByMuX (part f 1 0) (part f 1 1) VQ
      (tabEnv cnt (part f 0) R).CQ hfV (noMention_cutQ cnt _ R (hfR _))]
    show (fun _ => a) ∈ (_ + _ : Multiset _)
    rw [Multiset.mem_add]
    rcases ha with ha | ha
    · left
      obtain ⟨y, hy, rfl⟩ := mem_valsU.mp ha
      rw [← unary_eq y]; exact hy
    · right
      obtain ⟨y, hy, rfl⟩ := mem_valsU.mp ha
      rw [← unary_eq y]; exact hy
  have hVnd : (Vq.evaluatePlain D' γ : Multiset (Tuple T 1)).Nodup := by
    rw [hVq, valsQ, AggQueryIn.evaluatePlain_dedupG]; exact Multiset.nodup_dedup _
  have hWnd := nodup_powU Vq D' γ hVnd n₂
  -- the product, row of the left side by row
  rw [applyX, evaluatePlain_projQ]
  show Multiset.map _ (Multiset.filter _ _) = _
  rw [evaluatePlain_prodR, evaluatePlain_prodR, evaluatePlain_prodR]
  rw [filter_prod4]
  refine Multiset.bind_congr fun u hu => ?_
  obtain ⟨hS, hG⟩ := tabQ_correct Θ hc (part f 0) R hU hsrc (fun i => hfR _) D' γ u
    (hset u hu)
  have hsl := slice_eq_map_rowEnc hS
  -- the projection
  have hproj : ∀ d t w, (fun x => (Fin.append (fun i => SA.col (c := c) (uIdx k n₂ i))
      (fun j => SA.col (wIdx k n₂ j)) x).eval (prow d t w u) γ) = Fin.append u w := by
    intro d t w
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · rw [Fin.append_left, Fin.append_left, eval_uIdx]
    · rw [Fin.append_right, Fin.append_right, eval_wIdx]
  -- the predicate
  have hP : ∀ d, Multiset.Mem ((tabEnv cnt (part f 0) R).Desc.evaluatePlain D' γ) d → ∀ t w,
      (applyPred (c := c) k n₂).toGen.holdsPlain (prow d t w u) γ ↔
        (d = descEnc C u ∧ descP (n := n₂) (P := 0) t = d
          ∧ ∀ j, (decCell (SA.col (c := c) (wIdx k n₂ j))
            (fun z => .col (tIdx k n₂ (ci (Fin.natAdd k j) z))) (fun i => .col (uIdx k n₂ i))
            (fun i j' => .col (dIdx k n₂ i j'))).eval3 (prow d t w u) γ = Kleene.true) := by
    intro d hd t w
    rw [GenPredIn.holdsPlain, SP.evalPlain3_toGen, eval3_applyPred_true]
    refine and_congr ?_ Iff.rfl
    have hshape := (hmemD d).mp hd
    choose cd hcd using fun i => cellShape_code (hshape i)
    rw [eval3_matchSP_true _ _ _ γ u cd (fun i => eval_uIdx d t w u γ i)
      (fun i j => by rw [eval_dIdx]; exact congrFun (hcd i).2 j) (fun i => (hcd i).1)]
    constructor
    · intro h
      rw [← ofCells_cellOf d]
      exact congrArg ofCells (funext fun i => (hcd i).2.trans (by rw [h i]; rfl))
    · intro h
      subst h
      refine fun i => enc_inj' (hcd i).1 (shapeOK_code hnull u i) ?_
      rw [← (hcd i).2]
      funext j
      exact descEnc_cell C u i j
  -- the decoded values of a table row
  have hW : ∀ v, Multiset.Mem (R.evaluatePlain D' (Fin.append u γ)) v →
      ((powU Vq n₂).evaluatePlain D' γ : Multiset (Tuple T n₂)).filter (fun w =>
        ∀ j, (decCell (SA.col (c := c) (wIdx k n₂ j))
          (fun z => .col (tIdx k n₂ (ci (Fin.natAdd k j) z))) (fun i => .col (uIdx k n₂ i))
          (fun i j' => .col (dIdx k n₂ i j'))).eval3 (prow (descEnc C u) (rowEnc C u v) w u) γ
            = Kleene.true) = {v} := by
    intro v hv
    have hvW : Multiset.Mem ((powU Vq n₂).evaluatePlain D' γ) v :=
      (mem_powU Vq D' γ n₂ v).mpr fun j => hVmem _ (by
        rcases hG v hv j with ⟨i, hi⟩ | hj | hj
        · exact Or.inl (hi ▸ hval u hu i)
        · exact Or.inr hj
        · exact Or.inr (hnull _ hj))
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ hWnd) (Multiset.nodup_singleton v)).mpr
      fun w => ?_
    rw [Multiset.mem_filter, Multiset.mem_singleton]
    have hdec : ∀ j, (decCell (SA.col (c := c) (wIdx k n₂ j))
        (fun z => .col (tIdx k n₂ (ci (Fin.natAdd k j) z))) (fun i => .col (uIdx k n₂ i))
        (fun i j' => .col (dIdx k n₂ i j'))).eval3 (prow (descEnc C u) (rowEnc C u v) w u) γ
          = Kleene.true ↔ w j = v j := fun j => by
      rw [eval3_decCell_true _ _ _ _ _ γ u (v j) (fun i => eval_uIdx _ _ _ u γ i)
        (fun i j' => by rw [eval_dIdx]; exact descEnc_cell C u i j')
        (fun z => by rw [eval_tIdx]; exact rowEnc_out C u v j z), eval_wIdx]
    simp only [hdec]
    exact ⟨fun h => funext h.2, fun h => by subst h; exact ⟨hvW, fun _ => rfl⟩⟩
  -- the descriptors other than the row's give nothing
  have hDesc : ((tabEnv cnt (part f 0) R).Desc.evaluatePlain D' γ
      : Multiset (Tuple T (k * (7 + k)))).filter (fun d => d = descEnc C u) = {descEnc C u} := by
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ henv.1) (Multiset.nodup_singleton _)).mpr
      fun d => ?_
    rw [Multiset.mem_filter, Multiset.mem_singleton]
    exact ⟨fun h => h.2, fun h => by subst h; exact ⟨henv.2.1 u, rfl⟩⟩
  calc _ = ((tabEnv cnt (part f 0) R).Desc.evaluatePlain D' γ
        : Multiset (Tuple T (k * (7 + k)))).bind (fun d => if d = descEnc C u then
          ((tabQ cnt (part f 0) R).evaluatePlain D' γ
              : Multiset (Tuple T ((k + n₂) * (7 + k)))).bind
            (fun t => if descP (n := n₂) (P := 0) t = descEnc C u then
              (((powU Vq n₂).evaluatePlain D' γ : Multiset (Tuple T n₂)).filter (fun w =>
                ∀ j, (decCell (SA.col (c := c) (wIdx k n₂ j))
                  (fun z => .col (tIdx k n₂ (ci (Fin.natAdd k j) z))) (fun i => .col (uIdx k n₂ i))
                  (fun i j' => .col (dIdx k n₂ i j'))).eval3 (prow (descEnc C u) t w u) γ
                    = Kleene.true)).map (fun w => Fin.append u w) else 0) else 0) := by
        refine Multiset.bind_congr fun d hd => ?_
        split
        · rename_i hdu
          subst hdu
          refine Multiset.bind_congr fun t _ => ?_
          split
          · rename_i ht
            refine (Multiset.map_congr rfl fun w _ => hproj _ t w).trans
              (congrArg _ (Multiset.filter_congr fun w _ => (hP _ hd t w).trans ?_))
            simp only [true_and, ht]
          · rename_i ht
            refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
            obtain ⟨w, hw, -⟩ := Multiset.mem_map.mp hx
            exact ht ((hP _ hd t w).mp (Multiset.mem_filter.mp hw).2).2.1
        · rename_i hdu
          refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
          obtain ⟨t, -, hx⟩ := Multiset.mem_bind.mp hx
          obtain ⟨w, hw, -⟩ := Multiset.mem_map.mp hx
          exact hdu ((hP d hd t w).mp (Multiset.mem_filter.mp hw).2).1
    _ = ((R.evaluatePlain D' (Fin.append u γ) : Multiset (Tuple T n₂))).bind
        (fun v => {(Fin.append u v : Tuple T (k + n₂))}) := by
        rw [AggQueryIn.Multiset.bind_ite (fun d => d = descEnc C u), hDesc,
          Multiset.singleton_bind, AggQueryIn.Multiset.bind_ite]
        show (Multiset.filter (fun t => descP (P := 0) t = descEnc C u)
          ((tabQ cnt (part f 0) R).evaluatePlain D' γ)).bind _ = _
        rw [hsl, Multiset.bind_map]
        refine Multiset.bind_congr fun v hv => ?_
        rw [hW v hv, Multiset.map_singleton]
    _ = _ := by rw [Multiset.bind_singleton]

end Correct

/-- **The apply written with products settles where its left side and its
pool do.** -/
theorem settlesAt_applyX {c k n₂ : ℕ} {cnt : SeqAggFunc T} (hc : SeqAggFunc.Counts cnt)
    (f : ℕ → String) {l : List (String × ℕ)} {κ₂ : Fin n₂ → ColKind}
    (L : AggQueryIn T c k (ColKind.allReg k) l) (R : AggQueryIn T (k + c) n₂ κ₂)
    (VQ : AggQueryIn T c 1 (ColKind.allReg 1)) (hR : ∀ i, R.noMention (f i))
    (hV : VQ.noMention (part f 1 0)) (D : Database T) (γ : Fin c → T)
    (hL : L.SettlesAt D γ) (hVs : VQ.SettlesAt D γ) : (applyX cnt f L R VQ).SettlesAt D γ := by
  have henv := envSettles_tabEnv hc (part f 0) R (fun _ => hR _)
  have hnm := envNoMention_tabEnv cnt (part f 0) R (s := part f 1 1) (hR _)
  unfold applyX
  refine settlesAt_projQ _ _ D γ ?_
  show (prodR _ _).SettlesAt D γ
  refine settlesAt_prodR _ _ D γ (settlesAt_prodR _ _ D γ (settlesAt_prodR _ _ D γ (henv.desc D γ)
    (settlesAt_tabQ hc (part f 0) R (fun _ => hR _) D γ))
      (settlesAt_powU (D := D) (γ := γ) _ ?_ n₂)) hL
  unfold valsQ
  refine (AggQueryIn.settlesAt_dedupG _ D γ).mpr ?_
  exact AggQueryIn.settlesAt_sumByMuX _ _ _ _ hV hnm.1 D γ hVs (henv.cq D γ)

end Sym
