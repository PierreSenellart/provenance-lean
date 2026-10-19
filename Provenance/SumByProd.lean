import Provenance.MuUnion

/-!
# `⊎` from `μ^⊎` with products

`Provenance.SumByMu` derives the union from two bag recursions whose
rounds join the recursive relation with a closed relation, the join
written as an apply so that the construction lives in a basis holding the
apply. Here the same construction is written with the product, for the
bases holding `×` and not the apply: `AggQueryIn.sumByMuX`. Its rounds
read exactly what `sumByMu`'s do (`AggQueryIn.apply_plainEquiv_prod`), so
its value and its definedness are those of `sumByMu`.

The difference read as a `NOT IN` (`AggQueryIn.notInDiff`) is a product
already; `AggQueryIn.notInDiffX` is it with its tagged union written by
`sumByMuX`.
-/

variable {T : Type} [ValueType T]

namespace AggQueryIn

variable {c k : ℕ}

/-! ## Bag recursions with equal bodies -/

/-- **Two bodies reading alike give the same bag recursion.** -/
theorem evaluatePlain_Mu_congr_body {n : ℕ} {κ : Fin n → ColKind} (s : String)
    (q₀ : AggQueryIn T c n κ) (q₁ q₁' : AggQueryIn T c n κ [(s, n)])
    (h : ∀ (D : Database T) (γ : Fin c → T), q₁.evaluatePlain D γ = q₁'.evaluatePlain D γ)
    (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.Mu s q₀ q₁).evaluatePlain D γ = (AggQueryIn.Mu s q₀ q₁').evaluatePlain D γ := by
  simp only [AggQueryIn.evaluatePlain]
  exact congrArg₂ muSumFix (funext fun X => h _ γ) rfl

/-- **A bag recursion settles with a body reading alike**, provided that
body settles at every round. -/
theorem settlesAt_Mu_congr_body {n : ℕ} {κ : Fin n → ColKind} (s : String)
    (q₀ : AggQueryIn T c n κ) (q₁ q₁' : AggQueryIn T c n κ [(s, n)])
    (h : ∀ (D : Database T) (γ : Fin c → T), q₁.evaluatePlain D γ = q₁'.evaluatePlain D γ)
    (D : Database T) (γ : Fin c → T)
    (h' : ∀ X : Relation T n, q₁'.SettlesAt (D.assign s X) γ)
    (hs : (AggQueryIn.Mu s q₀ q₁).SettlesAt D γ) :
    (AggQueryIn.Mu s q₀ q₁').SettlesAt D γ := by
  obtain ⟨h₀, hz, hm, -⟩ := hs
  refine ⟨h₀, ?_, ?_, fun j => h' _⟩
  · rw [← h]; exact hz
  · exact (congrArg (fun f => MuSettles f _) (funext fun X => h (D.assign s X) γ)).mp hm

/-! ## The construction -/

/-- **A round of the construction, with a product**: `phaseBody` with the
apply replaced by the product it stands for. -/
def phaseBodyX (s : String) (p₁ : T) (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) :
    AggQueryIn T c (k + 1) (ColKind.allReg (k + 1)) [(s, k + 1)] :=
  (AggQueryIn.Proj (roundCols p₁)
    (AggQueryIn.Sel sameTag (AggQueryIn.Prod (AggQueryIn.Hole (k + 1) s) Z))).castKind
    (roundCols_kind p₁)

theorem evaluatePlain_phaseBodyX (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (D : Database T) (γ : Fin c → T) :
    (phaseBodyX s p₁ Z).evaluatePlain D γ = (phaseBody s p₁ Z).evaluatePlain D γ := by
  rw [phaseBodyX, phaseBody, AggQueryIn.evaluatePlain_castKind,
    AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u j => (roundCols p₁ j).evalPlain u γ)
      (Multiset.filter (fun u => sameTag.holdsPlain u γ)
        ((AggQueryIn.Prod (AggQueryIn.Hole (k + 1) s) Z).evaluatePlain D γ))
    = Multiset.map (fun u j => (roundCols p₁ j).evalPlain u γ)
      (Multiset.filter (fun u => sameTag.holdsPlain u γ)
        ((AggQueryIn.Apply (AggQueryIn.Hole (k + 1) s)
          (Z.substMap (fun j : Fin c => _root_.Sum.inr (Fin.natAdd (k + 1) j)))).evaluatePlain
            D γ))
  rw [AggQueryIn.apply_plainEquiv_prod (AggQueryIn.Hole (k + 1) s) Z D γ]

theorem settlesAt_phaseBodyX (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (D : Database T) (γ : Fin c → T)
    (hZ : Z.SettlesAt D γ) : (phaseBodyX s p₁ Z).SettlesAt D γ := by
  rw [phaseBodyX, AggQueryIn.settlesAt_castKind]
  exact (⟨trivial, hZ⟩ : True ∧ _)

/-- **`⊎` from two bag recursions with products**: `sumByMu` with each
round's apply written as the product it is. -/
def sumByMuX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c k (ColKind.allReg k) :=
  (AggQueryIn.Proj unwithTagCols
    (AggQueryIn.Sel (notTag 0)
      (AggQueryIn.Mu s₂
        (AggQueryIn.Mu s₁ (driver 0) (phaseBodyX s₁ ValueType.nonzero (withTag 0 q₁)))
        (phaseBodyX s₂ ValueType.nonzero (withTag 0 q₂))))).castKind (funext fun _ => rfl)

/-- The inner recursion reads as `sumByMu`'s. -/
theorem evaluatePlain_sumByMuX_inner (s₁ : String) (q₁ : AggQueryIn T c k (ColKind.allReg k))
    (D : Database T) (γ : Fin c → T) :
    (AggQueryIn.Mu s₁ (driver 0) (phaseBodyX s₁ ValueType.nonzero (withTag 0 q₁))).evaluatePlain
        D γ
      = (AggQueryIn.Mu s₁ (driver 0) (phaseBody s₁ ValueType.nonzero (withTag 0 q₁))).evaluatePlain
        D γ :=
  evaluatePlain_Mu_congr_body s₁ _ _ _ (fun D γ => evaluatePlain_phaseBodyX _ _ _ D γ) D γ

/-- **The construction reads as `sumByMu`.** -/
theorem evaluatePlain_sumByMuX_eq (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (D : Database T) (γ : Fin c → T) :
    (sumByMuX s₁ s₂ q₁ q₂).evaluatePlain D γ = (sumByMu s₁ s₂ q₁ q₂).evaluatePlain D γ := by
  rw [sumByMuX, sumByMu, AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain_castKind]
  show Multiset.map (fun u j => (unwithTagCols j).evalPlain u γ)
      (Multiset.filter (fun u => (notTag 0).holdsPlain u γ)
        ((AggQueryIn.Mu s₂
          (AggQueryIn.Mu s₁ (driver 0) (phaseBodyX s₁ ValueType.nonzero (withTag 0 q₁)))
          (phaseBodyX s₂ ValueType.nonzero (withTag 0 q₂))).evaluatePlain D γ))
    = Multiset.map (fun u j => (unwithTagCols j).evalPlain u γ)
      (Multiset.filter (fun u => (notTag 0).holdsPlain u γ)
        ((AggQueryIn.Mu s₂
          (AggQueryIn.Mu s₁ (driver 0) (phaseBody s₁ ValueType.nonzero (withTag 0 q₁)))
          (phaseBody s₂ ValueType.nonzero (withTag 0 q₂))).evaluatePlain D γ))
  rw [evaluatePlain_Mu_congr_body s₂ _ _ _ (fun D γ => evaluatePlain_phaseBodyX _ _ _ D γ) D γ]
  have hin := evaluatePlain_sumByMuX_inner s₁ q₁ D γ
  simp only [AggQueryIn.evaluatePlain] at hin ⊢
  rw [hin]

/-- **The construction is the union.** -/
theorem evaluatePlain_sumByMuX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂₂ : q₂.noMention s₂) (D : Database T) (γ : Fin c → T) :
    (sumByMuX s₁ s₂ q₁ q₂).evaluatePlain D γ
      = q₁.evaluatePlain D γ + q₂.evaluatePlain D γ := by
  rw [evaluatePlain_sumByMuX_eq, evaluatePlain_sumByMu s₁ s₂ q₁ q₂ h₁ h₂₂]

/-- **A phase recursion with products settles**, on every instance where
its operands do. -/
theorem settlesAt_phaseMuX (s : String) {p₀ p₁ : T} (hp : p₁ ≠ p₀)
    (base Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.noMention s)
    (D : Database T) (γ : Fin c → T) (R : Multiset (Tuple T k))
    (hZv : Z.evaluatePlain D γ = R.map (tagRow p₀))
    (hb : base.SettlesAt D γ) (hZs : Z.SettlesAt D γ) :
    (AggQueryIn.Mu s base (phaseBodyX s p₁ Z)).SettlesAt D γ := by
  have hstep : ∀ X : Multiset (Tuple T (k + 1)),
      (phaseBodyX s p₁ Z).evaluatePlain (D.assign s X) γ
        = (X.filter (fun x => x 0 = p₀)).bind
            (fun _ => R.map (tagRow p₁)) :=
    fun X => (evaluatePlain_phaseBodyX s p₁ Z _ γ).trans
      (evaluatePlain_phaseBody s p₀ p₁ Z hZ D γ R hZv X)
  refine ⟨hb, ?_, ⟨1, ?_⟩, fun j => ?_⟩
  · rw [hstep, Multiset.filter_zero, Multiset.zero_bind]
  · rw [Function.iterate_succ_apply', Function.iterate_one]
    show (phaseBodyX s p₁ Z).evaluatePlain (D.assign s
      ((phaseBodyX s p₁ Z).evaluatePlain (D.assign s (base.evaluatePlain D γ)) γ)) γ = 0
    rw [hstep, hstep]
    rw [Multiset.filter_eq_nil.mpr (fun x hx h => hp (Eq.trans (mem_round_phase hx).symm h)),
      Multiset.zero_bind]
  · exact settlesAt_phaseBodyX s p₁ Z _ γ (AggQueryIn.settlesAt_of_noMention Z hZ
      (fun _k s' hs' => (Database.find_assign_of_ne s s' _ D
        (fun hc => hs'.elim (fun h => h hc.2) (fun h => by simp at h))).symm) γ hZs)

/-- **The construction settles wherever its operands do.** -/
theorem settlesAt_sumByMuX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂₂ : q₂.noMention s₂)
    (D : Database T) (γ : Fin c → T) (hs₁ : q₁.SettlesAt D γ) (hs₂ : q₂.SettlesAt D γ) :
    (sumByMuX s₁ s₂ q₁ q₂).SettlesAt D γ := by
  rw [sumByMuX, AggQueryIn.settlesAt_castKind]
  show (AggQueryIn.Mu s₂ _ _).SettlesAt D γ
  refine settlesAt_phaseMuX s₂ ValueType.nonzero_ne_zero _ _
    ((noMention_withTag 0 q₂ s₂).mpr h₂₂) D γ _ (evaluatePlain_withTag 0 q₂ D γ) ?_ ?_
  · refine settlesAt_phaseMuX s₁ ValueType.nonzero_ne_zero _ _
      ((noMention_withTag 0 q₁ s₁).mpr h₁) D γ _ (evaluatePlain_withTag 0 q₁ D γ) ?_ ?_
    · rw [driver, AggQueryIn.settlesAt_castKind]
      show (unitC : AggQueryIn T c 0 _).SettlesAt D γ
      rw [unitC, AggQueryIn.settlesAt_castKind]
      trivial
    · rw [withTag, AggQueryIn.settlesAt_castKind]; exact hs₁
  · rw [withTag, AggQueryIn.settlesAt_castKind]; exact hs₂

/-! ## What the construction is made of -/

/-- **The classes the construction uses**: `sumMuOps` with the product in
place of the apply. -/
def sumProdOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.sel, OpKind.prod, OpKind.gamma, OpKind.muBag}

omit [ValueType T] in
theorem usesOnly_unitCX {S : Set OpKind} (hS : sumProdOps ⊆ S) :
    (unitC : AggQueryIn T c 0 _).usesOnly S := by
  rw [unitC, AggQueryIn.usesOnly_castKind]
  exact ⟨hS (by simp [sumProdOps]), hS (by simp [sumProdOps])⟩

omit [ValueType T] in
theorem usesOnly_withTagX {S : Set OpKind} (hS : sumProdOps ⊆ S) (t : T)
    (q : AggQueryIn T c k (ColKind.allReg k)) (hq : q.usesOnly S) :
    (withTag t q).usesOnly S := by
  rw [withTag, AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hS (by simp [sumProdOps]), fun j => ?_⟩, hq⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem usesOnly_driverX {S : Set OpKind} (hS : sumProdOps ⊆ S) (p₀ : T) :
    (driver (c := c) (k := k) p₀).usesOnly S := by
  rw [driver, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumProdOps]), fun _ => rfl⟩, usesOnly_unitCX hS⟩

omit [ValueType T] in
theorem usesOnly_phaseBodyX {S : Set OpKind} (hS : sumProdOps ⊆ S) (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.usesOnly S) :
    (phaseBodyX s p₁ Z).usesOnly S := by
  rw [phaseBodyX, AggQueryIn.usesOnly_castKind]
  refine ⟨⟨hS (by simp [sumProdOps]), fun j => ?_⟩, hS (by simp [sumProdOps]),
    hS (by simp [sumProdOps]), trivial, hZ⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- **The construction uses the classes of `sumProdOps`** and its operands'. -/
theorem usesOnly_sumByMuX {S : Set OpKind} (hS : sumProdOps ⊆ S) (s₁ s₂ : String)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) (h₁ : q₁.usesOnly S) (h₂ : q₂.usesOnly S) :
    (sumByMuX s₁ s₂ q₁ q₂).usesOnly S := by
  rw [sumByMuX, AggQueryIn.usesOnly_castKind]
  exact ⟨⟨hS (by simp [sumProdOps]), fun _ => rfl⟩, hS (by simp [sumProdOps]),
    hS (by simp [sumProdOps]),
    ⟨hS (by simp [sumProdOps]), usesOnly_driverX hS 0,
      usesOnly_phaseBodyX hS _ _ _ (usesOnly_withTagX hS 0 q₁ h₁)⟩,
    usesOnly_phaseBodyX hS _ _ _ (usesOnly_withTagX hS 0 q₂ h₂)⟩

omit [ValueType T] in
theorem hygienic_phaseBodyX (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) :
    (phaseBodyX s p₁ Z).hygienic ↔ Z.hygienic := by
  rw [phaseBodyX, AggQueryIn.hygienic_castKind]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

omit [ValueType T] in
theorem noMention_phaseBodyX (s' : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) {s : String}
    (hZ : Z.noMention s) : (phaseBodyX s' p₁ Z).noMention s := by
  rw [phaseBodyX, AggQueryIn.noMention_castKind]
  exact ⟨trivial, hZ⟩

/-- **The construction's recursions are hygienic**, given fresh names. -/
theorem hygienic_sumByMuX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂₁ : q₁.noMention s₂) (h₂₂ : q₂.noMention s₂)
    (hr₁ : q₁.hygienic) (hr₂ : q₂.hygienic) :
    (sumByMuX s₁ s₂ q₁ q₂).hygienic := by
  rw [sumByMuX, AggQueryIn.hygienic_castKind]
  exact ⟨⟨noMention_driver 0 s₂,
      noMention_phaseBodyX s₁ _ _ ((noMention_withTag 0 q₁ s₂).mpr h₂₁)⟩,
    noMention_phaseBodyX s₂ _ _ ((noMention_withTag 0 q₂ s₂).mpr h₂₂),
    ⟨noMention_driver 0 s₁, noMention_phaseBodyX s₁ _ _ ((noMention_withTag 0 q₁ s₁).mpr h₁),
      hygienic_driver 0, (hygienic_phaseBodyX _ _ _).mpr
        ((hygienic_withTag 0 q₁).mpr hr₁)⟩,
    (hygienic_phaseBodyX _ _ _).mpr ((hygienic_withTag 0 q₂).mpr hr₂)⟩

theorem inSig_phaseBodyX (Θ : Set (SeqAggFunc T)) (s : String) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.inSig Θ) :
    (phaseBodyX s p₁ Z).inSig Θ := by
  rw [phaseBodyX, AggQueryIn.inSig_castKind]
  refine ⟨fun j => ?_, rfl, trivial, hZ⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- **The construction is in every signature its operands are in.** -/
theorem inSig_sumByMuX (Θ : Set (SeqAggFunc T)) (s₁ s₂ : String)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) (h₁ : q₁.inSig Θ) (h₂ : q₂.inSig Θ) :
    (sumByMuX s₁ s₂ q₁ q₂).inSig Θ := by
  rw [sumByMuX, AggQueryIn.inSig_castKind]
  exact ⟨fun _ => rfl, rfl, ⟨inSig_driver Θ 0,
      inSig_phaseBodyX Θ _ _ _ (inSig_withTag Θ 0 q₁ h₁)⟩,
    inSig_phaseBodyX Θ _ _ _ (inSig_withTag Θ 0 q₂ h₂)⟩

omit [ValueType T] in
theorem overSchema_phaseBodyX {sch : Schema} {s : String} (hs : sch s = some (k + 1)) (p₁ : T)
    (Z : AggQueryIn T c (k + 1) (ColKind.allReg (k + 1))) (hZ : Z.overSchema sch) :
    (phaseBodyX s p₁ Z).overSchema sch := by
  rw [phaseBodyX, AggQueryIn.overSchema_castKind]
  exact ⟨hs, hZ⟩

/-- **The construction is well-formed over a schema declaring neither
bound name**, its operands being so and naming neither. -/
theorem overSchema_sumByMuX (sch : Schema) (s₁ s₂ : String)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (hs₁ : sch s₁ = none) (hs₂ : sch s₂ = none) (hn₁ : s₁ ∉ q₁.names) (hn₂ : s₂ ∉ q₂.names)
    (h₁ : q₁.overSchema sch) (h₂ : q₂.overSchema sch) :
    (sumByMuX s₁ s₂ q₁ q₂).overSchema sch := by
  rw [sumByMuX, AggQueryIn.overSchema_castKind]
  exact ⟨hs₂, ⟨hs₁, overSchema_driver sch 0,
      noMention_phaseBodyX s₁ _ _ ((noMention_withTag 0 q₁ s₁).mpr
        (AggQueryIn.noMention_of_not_mem_names q₁ hn₁)),
      overSchema_phaseBodyX (Schema.update_self sch s₁ (k + 1)) _ _
        ((overSchema_withTag _ 0 q₁).mpr
          (AggQueryIn.overSchema_update_of_not_mem_names q₁ h₁ hn₁))⟩,
    noMention_phaseBodyX s₂ _ _ ((noMention_withTag 0 q₂ s₂).mpr
      (AggQueryIn.noMention_of_not_mem_names q₂ hn₂)),
    overSchema_phaseBodyX (Schema.update_self sch s₂ (k + 1)) _ _
      ((overSchema_withTag _ 0 q₂).mpr
        (AggQueryIn.overSchema_update_of_not_mem_names q₂ h₂ hn₂))⟩

/-- **The construction names its two bound names and its operands'.** -/
theorem names_sumByMuX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    (sumByMuX s₁ s₂ q₁ q₂).names ⊆ insert s₁ (insert s₂ (Union.union q₁.names q₂.names)) := by
  intro x hx
  rw [sumByMuX, AggQueryIn.names_castKind] at hx
  simp only [AggQueryIn.names, phaseBodyX, withTag, driver, unitC, AggQueryIn.names_castKind,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    false_or] at hx
  simp only [Finset.mem_insert, Finset.mem_union]
  tauto

/-- The construction names nothing its operands do not, its two bound
names aside. -/
theorem noMention_sumByMuX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    {s : String} (h₁ : q₁.noMention s) (h₂ : q₂.noMention s) :
    (sumByMuX s₁ s₂ q₁ q₂).noMention s := by
  rw [sumByMuX, AggQueryIn.noMention_castKind]
  exact ⟨⟨noMention_driver 0 s, noMention_phaseBodyX s₁ _ _
      ((noMention_withTag 0 q₁ s).mpr h₁)⟩,
    noMention_phaseBodyX s₂ _ _ ((noMention_withTag 0 q₂ s).mpr h₂)⟩

/-! ## The difference, with products and the union from recursions -/

/-- **The tagged union of the `NOT IN` form**, its union written by
`sumByMuX`. -/
def tagUnionX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c (k + 1) (ColKind.allReg (k + 1)) :=
  sumByMuX s₁ s₂ (.Proj (AggQueryIn.tagCols 0) q₁)
    (.Proj (AggQueryIn.tagCols ValueType.nonzero) q₂)

/-- The grouping of the `NOT IN` form over `tagUnionX`. -/
def tagAggX (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c (k + 1)
      (Fin.append (fun _ : Fin k => ColKind.reg)
        (fun _ : Fin 1 => ColKind.agg)) :=
  .Gamma (lab := 0) (rd := fun _ => false) (fun i : Fin k => i.castSucc)
    ![TermIn.index (Fin.last k)] ![cnt]
    (tagUnionX s₁ s₂ q₁ q₂) ![some AggQueryIn.rightTag]

/-- **The difference read as a `NOT IN`, over the classes of a basis
holding `×` and not `⊎`.** -/
def notInDiffX (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    AggQueryIn T c k (ColKind.allReg k) :=
  .Proj (fun i : Fin k =>
      .term (TermGIn.index (Fin.castAdd (k + 1) i) (notInKinds_left k i)))
    (.Sel AggQueryIn.notInCond (.Prod q₁ (tagAggX s₁ s₂ cnt q₁ q₂)))

theorem evaluatePlain_tagUnionX (s₁ s₂ : String) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂ : q₂.noMention s₂) (D : Database T) (γ : Fin c → T) :
    (tagUnionX s₁ s₂ q₁ q₂).evaluatePlain D γ
      = (AggQueryIn.tagUnion q₁ q₂).evaluatePlain D γ := by
  rw [tagUnionX]
  exact (evaluatePlain_sumByMuX s₁ s₂ (.Proj (AggQueryIn.tagCols 0) q₁)
    (.Proj (AggQueryIn.tagCols ValueType.nonzero) q₂) (by simpa [AggQueryIn.noMention] using h₁)
    (by simpa [AggQueryIn.noMention] using h₂) D γ).trans rfl

/-- **The construction is the difference**, the two bound names being
fresh for the operands they bind over and the aggregate counting. -/
theorem evaluatePlain_notInDiffX (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (hc : SeqAggFunc.Counts cnt) (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂ : q₂.noMention s₂) (D : Database T) (γ : Fin c → T) :
    (notInDiffX s₁ s₂ cnt q₁ q₂).evaluatePlain D γ
      = (AggQueryIn.Diff q₁ q₂).evaluatePlain D γ := by
  rw [AggQueryIn.diff_plainEquiv_notIn cnt hc q₁ q₂ D γ]
  have htu := evaluatePlain_tagUnionX s₁ s₂ q₁ q₂ h₁ h₂ D γ
  simp only [notInDiffX, AggQueryIn.notInDiff, tagAggX, AggQueryIn.tagAgg,
    AggQueryIn.evaluatePlain]
  rw [htu]

theorem settlesAt_notInDiffX (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k))
    (h₁ : q₁.noMention s₁) (h₂ : q₂.noMention s₂) (D : Database T) (γ : Fin c → T)
    (hs₁ : q₁.SettlesAt D γ) (hs₂ : q₂.SettlesAt D γ) :
    (notInDiffX s₁ s₂ cnt q₁ q₂).SettlesAt D γ :=
  ⟨hs₁, settlesAt_sumByMuX s₁ s₂ (.Proj (AggQueryIn.tagCols 0) q₁)
    (.Proj (AggQueryIn.tagCols ValueType.nonzero) q₂) (by simpa [AggQueryIn.noMention] using h₁)
    (by simpa [AggQueryIn.noMention] using h₂) D γ hs₁ hs₂⟩

theorem usesOnly_notInDiffX {S : Set OpKind} (hS : sumProdOps ⊆ S) (s₁ s₂ : String)
    (cnt : SeqAggFunc T) {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (h₁ : q₁.usesOnly S) (h₂ : q₂.usesOnly S) :
    (notInDiffX s₁ s₂ cnt q₁ q₂).usesOnly S :=
  ⟨⟨hS (by simp [sumProdOps]), fun _ => rfl⟩, hS (by simp [sumProdOps]),
    hS (by simp [sumProdOps]), h₁, hS (by simp [sumProdOps]),
    usesOnly_sumByMuX hS s₁ s₂ _ _ ⟨⟨hS (by simp [sumProdOps]), fun _ => rfl⟩, h₁⟩
      ⟨⟨hS (by simp [sumProdOps]), fun _ => rfl⟩, h₂⟩⟩

theorem hygienic_notInDiffX (s₁ s₂ : String) (cnt : SeqAggFunc T)
    {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (h₁ : q₁.noMention s₁) (h₂₁ : q₁.noMention s₂) (h₂₂ : q₂.noMention s₂)
    (hr₁ : q₁.hygienic) (hr₂ : q₂.hygienic) :
    (notInDiffX s₁ s₂ cnt q₁ q₂).hygienic :=
  ⟨hr₁, hygienic_sumByMuX s₁ s₂ _ _ h₁ h₂₁ h₂₂ hr₁ hr₂⟩

theorem inSig_notInDiffX {Θ : Set (SeqAggFunc T)} (s₁ s₂ : String) {cnt : SeqAggFunc T}
    (hc : cnt ∈ Θ) {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (h₁ : q₁.inSig Θ) (h₂ : q₂.inSig Θ) : (notInDiffX s₁ s₂ cnt q₁ q₂).inSig Θ := by
  refine ⟨fun _ => rfl, AggQueryIn.noFun_notInCond, h₁, fun j => ?_, fun j => ?_, fun j => ?_,
    inSig_sumByMuX Θ s₁ s₂ _ _ ⟨fun j => AggQueryIn.noFun_tagCols 0 j, h₁⟩
      ⟨fun j => AggQueryIn.noFun_tagCols _ j, h₂⟩⟩
  · rw [Subsingleton.elim j 0]; rfl
  · rw [Subsingleton.elim j 0]; exact hc
  · rw [Subsingleton.elim j 0]; rfl

theorem overSchema_notInDiffX (sch : Schema) (s₁ s₂ : String) (cnt : SeqAggFunc T)
    {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (hs₁ : sch s₁ = none) (hs₂ : sch s₂ = none) (hn₁ : s₁ ∉ q₁.names) (hn₂ : s₂ ∉ q₂.names)
    (h₁ : q₁.overSchema sch) (h₂ : q₂.overSchema sch) :
    (notInDiffX s₁ s₂ cnt q₁ q₂).overSchema sch :=
  ⟨h₁, overSchema_sumByMuX sch s₁ s₂ _ _ hs₁ hs₂ hn₁ hn₂ h₁ h₂⟩

theorem names_notInDiffX (s₁ s₂ : String) (cnt : SeqAggFunc T)
    (q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)) :
    (notInDiffX s₁ s₂ cnt q₁ q₂).names
      ⊆ insert s₁ (insert s₂ (Union.union q₁.names q₂.names)) := by
  intro x hx
  have h := names_sumByMuX s₁ s₂ (.Proj (AggQueryIn.tagCols (c := c) 0) q₁)
    (.Proj (AggQueryIn.tagCols (c := c) ValueType.nonzero) q₂)
  change x ∈ Union.union q₁.names (sumByMuX s₁ s₂ _ _).names at hx
  simp only [Finset.mem_union] at hx
  rcases hx with hx | hx
  · simp [hx]
  · have := h hx
    simp only [AggQueryIn.names, Finset.mem_insert, Finset.mem_union] at this ⊢
    tauto

theorem noMention_notInDiffX (s₁ s₂ : String) (cnt : SeqAggFunc T)
    {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)} {s : String}
    (h₁ : q₁.noMention s) (h₂ : q₂.noMention s) :
    (notInDiffX s₁ s₂ cnt q₁ q₂).noMention s :=
  ⟨h₁, noMention_sumByMuX s₁ s₂ _ _ h₁ h₂⟩

end AggQueryIn
