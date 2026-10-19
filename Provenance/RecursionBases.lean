import Provenance.DiffBasis

/-!
# The bases of the whole algebra, all of them

A recursive term reads its recursive relation under a projection, a
selection, either side of a product, the left side of an apply, either side
of a union, `Explode` and `Retag`, and nowhere else. Of these only a
selection and an apply can drop a row: without them a round has `k · |X|`
rows for a `k` that does not depend on the round `X`, so a bag recursion
that settles is its base (`AggQueryIn.evaluatePlain_mu_degenerate`), and the
algebra is left with polynomial answers, which the chain of diamonds
refutes. So `σ` or the apply is in every basis
(`sel_or_apply_mem_of_generatesOnRec`), and `{∅, Π, −, ×, γ, win, μ^⊎}` is
not one. With the other rows this classifies the generating sets
completely (`generatesOnRec_iff`): they are the supersets of the three
bases `basisRecOps`, `Sym.basisProdOps` and `basisRecDiffOps`.
-/

variable {T : Type} [ValueType T]

namespace AggQueryIn

/-! ## A recursive term that drops no row -/

/-- **Without a selection and an apply, a recursive term multiplies its
round**: it reads `X` as `k · |X| + C` rows, `k` and `C` fixed by the
instance and the context. -/
theorem card_body_of_noFilter {S : Set OpKind} (hsel : OpKind.sel ∉ S)
    (hap : OpKind.apply ∉ S) {s : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      l = [(s, m)] → q.usesOnly S → q.noMention s →
      ∀ (D : Database T) (γ : Fin c → T), ∃ k C : ℕ, ∀ X : Relation T m,
        Multiset.card (q.evaluatePlain (D.assign s X) γ) = k * Multiset.card X + C := by
  intro c n κ l q
  induction q with
  | Hole n s' κh =>
    intro hl _ _ D γ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.mp hl)
    refine ⟨1, 0, fun X => ?_⟩
    simp only [AggQueryIn.evaluatePlain, Database.find_assign]
    omega
  | Proj ps q ih =>
    intro hl hu hm D γ
    obtain ⟨k, C, h⟩ := ih hl hu.2 hm D γ
    exact ⟨k, C, fun X => by simp only [AggQueryIn.evaluatePlain, Multiset.card_map]; exact h X⟩
  | Sel φ q hφ ih => exact fun _ hu => absurd hu.1 hsel
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hl hu hm D γ
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      obtain ⟨k, C, h⟩ := ih₁ h₁ hu.2.1 hm.1 D γ
      refine ⟨k * Multiset.card (q₂.evaluatePlain D γ),
        C * Multiset.card (q₂.evaluatePlain D γ), fun X => ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [Relation.card_hMul, h X, AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hm.2]
      ring
    · subst h₁
      obtain ⟨k, C, h⟩ := ih₂ h₂ hu.2.2 hm.2 D γ
      refine ⟨Multiset.card (q₁.evaluatePlain D γ) * k,
        Multiset.card (q₁.evaluatePlain D γ) * C, fun X => ?_⟩
      simp only [AggQueryIn.evaluatePlain]
      rw [Relation.card_hMul, h X, AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hm.1]
      ring
  | Apply q₁ q₂ ih₁ ih₂ => exact fun _ hu => absurd hu.1 hap
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hl hu hm D γ
    rcases List.append_eq_singleton' hl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst h₂
      obtain ⟨k, C, h⟩ := ih₁ h₁ hu.2.1 hm.1 D γ
      refine ⟨k, C + Multiset.card (q₂.evaluatePlain D γ), fun X => ?_⟩
      show Multiset.card (q₁.evaluatePlain (D.assign s X) γ + q₂.evaluatePlain (D.assign s X) γ)
        = _
      rw [Multiset.card_add, h X, AggQueryIn.evaluatePlain_assign_of_noMention X q₂ hm.2]
      ring
    · subst h₁
      obtain ⟨k, C, h⟩ := ih₂ h₂ hu.2.2 hm.2 D γ
      refine ⟨k, Multiset.card (q₁.evaluatePlain D γ) + C, fun X => ?_⟩
      show Multiset.card (q₁.evaluatePlain (D.assign s X) γ + q₂.evaluatePlain (D.assign s X) γ)
        = _
      rw [Multiset.card_add, h X, AggQueryIn.evaluatePlain_assign_of_noMention X q₁ hm.1]
      ring
  | Explode k hk q ih => exact fun hl hu hm D γ => ih hl hu hm D γ
  | Retag h q ih => exact fun hl hu hm D γ => ih hl hu hm D γ
  | _ => exact fun hl => absurd hl (by simp)

/-- **A bag recursion whose term drops no row is its base**, wherever it
settles: its rounds have `k^j · |M|` rows, so one of them is empty only if
`k` or the base is. -/
theorem evaluatePlain_mu_degenerate {S : Set OpKind} (hsel : OpKind.sel ∉ S)
    (hap : OpKind.apply ∉ S) {c n : ℕ} {κ : Fin n → ColKind} (s : String)
    (q₀ : AggQueryIn T c n κ) (q₁ : AggQueryIn T c n κ [(s, n)]) (hu : q₁.usesOnly S)
    (hm : q₁.noMention s) (D : Database T) (γ : Fin c → T)
    (h : (AggQueryIn.Mu s q₀ q₁).SettlesAt D γ) :
    (AggQueryIn.Mu s q₀ q₁).evaluatePlain D γ = q₀.evaluatePlain D γ := by
  obtain ⟨-, h0, ⟨j, hj⟩, -⟩ := h
  obtain ⟨k, C, hkc⟩ := card_body_of_noFilter hsel hap q₁ rfl hu hm D γ
  set step : Multiset (Tuple T n) → Multiset (Tuple T n) :=
    fun X => q₁.evaluatePlain (D.assign s X) γ with hstep
  have hC : C = 0 := by
    have := hkc 0
    rw [show q₁.evaluatePlain (D.assign s (0 : Relation T n)) γ = 0 from h0] at this
    simpa using this.symm
  have hcard : ∀ i (M : Multiset (Tuple T n)), Multiset.card (step^[i] M)
      = k ^ i * Multiset.card M := by
    intro i
    induction i with
    | zero => intro M; simp
    | succ i ih =>
      intro M
      rw [Function.iterate_succ_apply', pow_succ, show Multiset.card (step (step^[i] M))
        = k * Multiset.card (step^[i] M) + C from hkc _, ih, hC]
      ring
  have h1 : step (q₀.evaluatePlain D γ) = 0 := by
    have hz := congrArg Multiset.card hj
    rw [hcard, Multiset.card_zero, mul_eq_zero, pow_eq_zero_iff (Nat.succ_ne_zero j)] at hz
    rcases hz with hk | hM
    · apply Multiset.card_eq_zero.mp
      rw [hkc, hk, hC]
      simp
    · rw [Multiset.card_eq_zero.mp hM]
      exact h0
  simp only [AggQueryIn.evaluatePlain]
  rw [muSumFix_eq_of_empty h0 (k := 0) (by rw [Function.iterate_one]; exact h1)]
  rfl

/-- **A set recursion matched base for base and term for term**, the term
at the source's rounds, is defined and equal wherever the source is. -/
theorem muSet_congr {c n : ℕ} (s : String) (q₀ q₀' : AggQueryIn T c n (ColKind.allReg n))
    (q₁ q₁' : AggQueryIn T c n (ColKind.allReg n) [(s, n)]) (D : Database T) (γ : Fin c → T)
    (h : (AggQueryIn.MuSet s q₀ q₁).SettlesAt D γ)
    (h₀ : q₀'.SettlesAt D γ ∧ q₀.evaluatePlain D γ = q₀'.evaluatePlain D γ)
    (h₁ : ∀ X : Relation T n, q₁.SettlesAt (D.assign s X) γ →
      q₁'.SettlesAt (D.assign s X) γ
        ∧ q₁.evaluatePlain (D.assign s X) γ = q₁'.evaluatePlain (D.assign s X) γ) :
    (AggQueryIn.MuSet s q₀' q₁').SettlesAt D γ
      ∧ (AggQueryIn.MuSet s q₀ q₁).evaluatePlain D γ
          = (AggQueryIn.MuSet s q₀' q₁').evaluatePlain D γ := by
  obtain ⟨-, hS, hk⟩ := h
  set step : Multiset (Tuple T n) → Multiset (Tuple T n) :=
    fun X => (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s X) γ).dedup with hstep
  set step' : Multiset (Tuple T n) → Multiset (Tuple T n) :=
    fun X => (q₀'.evaluatePlain D γ + q₁'.evaluatePlain (D.assign s X) γ).dedup with hstep'
  have hround : ∀ i, step (muIter step i) = step' (muIter step i) := by
    intro i
    show (q₀.evaluatePlain D γ + q₁.evaluatePlain (D.assign s (muIter step i)) γ).dedup
      = (q₀'.evaluatePlain D γ + q₁'.evaluatePlain (D.assign s (muIter step i)) γ).dedup
    rw [h₀.2, (h₁ _ (hk i)).2]
  have hiter : ∀ i, muIter step i = muIter step' i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      show step (muIter step i) = step' (muIter step' i)
      rw [hround, ih]
  have hS' : MuSetSettles step' := by
    obtain ⟨j, hj⟩ := hS
    refine ⟨j, ?_⟩
    rw [← muIter_eq_iterate, ← muIter_eq_iterate] at hj ⊢
    rw [← hiter, ← hiter]
    exact hj
  refine ⟨⟨h₀.1, hS', fun i => ?_⟩, ?_⟩
  · have := (h₁ _ (hk i)).1
    rw [hiter i] at this
    exact this
  · have hidx : muFixIdx step = muFixIdx step' := by
      unfold muFixIdx
      congr 1
      ext j
      simp only [Set.mem_ofPred_eq]
      rw [← muIter_eq_iterate, ← muIter_eq_iterate, ← muIter_eq_iterate, ← muIter_eq_iterate,
        hiter, hiter]
    show muFix step = muFix step'
    unfold muFix
    rw [hidx, hiter]

/-! ## Dropping such recursions -/

/-- **Over classes with no selection and no apply, every bag recursion can
be replaced by its base**: the result has no bag recursion, keeps the
hygiene, the signature and the names not mentioned, and is defined and
equal wherever the source is. -/
theorem exists_dropMu {S : Set OpKind} (hsel : OpKind.sel ∉ S) (hap : OpKind.apply ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.hygienic →
      ∃ q' : AggQueryIn T c n κ l, q'.usesOnly (S \ {OpKind.muBag}) ∧ q'.hygienic
        ∧ (∀ Θ, q.inSig Θ → q'.inSig Θ) ∧ (∀ x, q.noMention x → q'.noMention x)
        ∧ ∀ (D : Database T) (γ : Fin c → T), q.SettlesAt D γ →
            q'.SettlesAt D γ ∧ q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  have hmem : ∀ {k : OpKind}, k ∈ S → k ≠ OpKind.muBag → k ∈ S \ {OpKind.muBag} :=
    fun hk hne => ⟨hk, hne⟩
  intro c n κ l q
  induction q with
  | Rel n s =>
    exact fun _ _ => ⟨AggQueryIn.Rel n s, trivial, trivial, fun _ h => h, fun _ h => h,
      fun _ _ h => ⟨h, rfl⟩⟩
  | Hole n s κh =>
    exact fun _ _ => ⟨AggQueryIn.Hole n s κh, trivial, trivial, fun _ h => h, fun _ h => h,
      fun _ _ h => ⟨h, rfl⟩⟩
  | Param pv ρ =>
    exact fun hu _ => ⟨AggQueryIn.Param pv ρ, ⟨hmem hu.1 (by decide), hmem hu.2.1 (by decide),
      hmem hu.2.2 (by decide)⟩, trivial, fun _ h => h, fun _ h => h, fun _ _ h => ⟨h, rfl⟩⟩
  | Empty =>
    exact fun hu _ => ⟨AggQueryIn.Empty, hmem hu (by decide), trivial, fun _ h => h,
      fun _ h => h, fun _ _ h => ⟨h, rfl⟩⟩
  | Proj ps q ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu.2 hr
    refine ⟨AggQueryIn.Proj ps q', ⟨⟨hmem hu.1.1 (by decide), hu.1.2⟩, hu'⟩, hr',
      fun Θ hi => ⟨hi.1, hi' Θ hi.2⟩, hm', fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | Sel φ q hφ ih => exact fun hu => absurd hu.1 hsel
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hu hr
    obtain ⟨q₁', hu₁, hr₁, hi₁, hm₁, he₁⟩ := ih₁ hu.2.1 hr.1
    obtain ⟨q₂', hu₂, hr₂, hi₂, hm₂, he₂⟩ := ih₂ hu.2.2 hr.2
    refine ⟨AggQueryIn.Prod q₁' q₂', ⟨hmem hu.1 (by decide), hu₁, hu₂⟩, ⟨hr₁, hr₂⟩,
      fun Θ hi => ⟨hi₁ Θ hi.1, hi₂ Θ hi.2⟩, fun x hx => ⟨hm₁ x hx.1, hm₂ x hx.2⟩,
      fun D γ h => ⟨⟨(he₁ D γ h.1).1, (he₂ D γ h.2).1⟩, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he₁ D γ h.1).2, (he₂ D γ h.2).2]
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hu => absurd hu.1 hap
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hu hr
    obtain ⟨q₁', hu₁, hr₁, hi₁, hm₁, he₁⟩ := ih₁ hu.2.1 hr.1
    obtain ⟨q₂', hu₂, hr₂, hi₂, hm₂, he₂⟩ := ih₂ hu.2.2 hr.2
    refine ⟨AggQueryIn.Sum q₁' q₂', ⟨hmem hu.1 (by decide), hu₁, hu₂⟩, ⟨hr₁, hr₂⟩,
      fun Θ hi => ⟨hi₁ Θ hi.1, hi₂ Θ hi.2⟩, fun x hx => ⟨hm₁ x hx.1, hm₂ x hx.2⟩,
      fun D γ h => ⟨⟨(he₁ D γ h.1).1, (he₂ D γ h.2).1⟩, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he₁ D γ h.1).2, (he₂ D γ h.2).2]
  | Dedup q ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu.2 hr
    refine ⟨AggQueryIn.Dedup q', ⟨hmem hu.1 (by decide), hu'⟩, hr', hi', hm',
      fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hu hr
    obtain ⟨q₁', hu₁, hr₁, hi₁, hm₁, he₁⟩ := ih₁ hu.2.1 hr.1
    obtain ⟨q₂', hu₂, hr₂, hi₂, hm₂, he₂⟩ := ih₂ hu.2.2 hr.2
    refine ⟨AggQueryIn.Diff q₁' q₂', ⟨hmem hu.1 (by decide), hu₁, hu₂⟩, ⟨hr₁, hr₂⟩,
      fun Θ hi => ⟨hi₁ Θ hi.1, hi₂ Θ hi.2⟩, fun x hx => ⟨hm₁ x hx.1, hm₂ x hx.2⟩,
      fun D γ h => ⟨⟨(he₁ D γ h.1).1, (he₂ D γ h.2).1⟩, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he₁ D γ h.1).2, (he₂ D γ h.2).2]
  | Explode k hk q ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu hr
    exact ⟨AggQueryIn.Explode k hk q', hu', hr', hi', hm', he'⟩
  | Retag h q ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu hr
    exact ⟨AggQueryIn.Retag h q', hu', hr', hi', hm', he'⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hu hr
    obtain ⟨q₀', hu₀, hr₀, hi₀, hm₀, he₀⟩ := ih₀ hu.2.1 hr.2.2.1
    refine ⟨q₀', hu₀, hr₀, fun Θ hi => hi₀ Θ hi.1, fun x hx => hm₀ x hx.1, fun D γ h => ?_⟩
    rw [evaluatePlain_mu_degenerate hsel hap s q₀ q₁ hu.2.2 hr.2.1 D γ h]
    exact he₀ D γ h.1
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro hu hr
    obtain ⟨q₀', hu₀, hr₀, hi₀, hm₀, he₀⟩ := ih₀ hu.2.1 hr.2.2.1
    obtain ⟨q₁', hu₁, hr₁, hi₁, hm₁, he₁⟩ := ih₁ hu.2.2 hr.2.2.2
    exact ⟨AggQueryIn.MuSet s q₀' q₁', ⟨hmem hu.1 (by decide), hu₀, hu₁⟩,
      ⟨hm₀ s hr.1, hm₁ s hr.2.1, hr₀, hr₁⟩, fun Θ hi => ⟨hi₀ Θ hi.1, hi₁ Θ hi.2⟩,
      fun x hx => ⟨hm₀ x hx.1, hm₁ x hx.2⟩,
      fun D γ h => muSet_congr s q₀ q₀' q₁ q₁' D γ h (he₀ D γ h.1) fun X hX => he₁ _ γ hX⟩
  | @Gamma c' m n₁ n₂ lab rd is ts fs q keep ord ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu.2 hr
    refine ⟨AggQueryIn.Gamma (lab := lab) (rd := rd) is ts fs q' keep ord,
      ⟨hmem hu.1 (by decide), hu'⟩, hr', fun Θ hi => ⟨hi.1, hi.2.1, hi.2.2.1, hi' Θ hi.2.2.2⟩,
      hm', fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | @GammaScalar c' m n₂ lab rd ts fs q ord ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu.2 hr
    refine ⟨AggQueryIn.GammaScalar (lab := lab) (rd := rd) ts fs q' ord,
      ⟨hmem hu.1 (by decide), hu'⟩, hr', fun Θ hi => ⟨hi.1, hi.2.1, hi' Θ hi.2.2⟩,
      hm', fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | @GammaNest c' m n₁ κ' lab rd is his p f q ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu.2 hr
    refine ⟨AggQueryIn.GammaNest (lab := lab) (rd := rd) is his p f q',
      ⟨⟨hmem hu.1.1 (by decide), hu.1.2⟩, hu'⟩, hr', fun Θ hi => ⟨hi.1, hi.2.1, hi' Θ hi.2.2⟩,
      hm', fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | ProvSum is his t q ih => exact fun hu => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun hu => hu.elim
  | @Win c' n' m' p' κ' lab rd P O o w t f q hrr dist keep ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu.2 hr
    refine ⟨AggQueryIn.Win (lab := lab) (rd := rd) P O o w t f q' hrr dist keep,
      ⟨hmem hu.1 (by decide), hu'⟩, hr', fun Θ hi => ⟨hi.1, hi.2.1, hi.2.2.1, hi' Θ hi.2.2.2⟩,
      hm', fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain, (he' D γ h).2]
  | @WinExpr c' n' m' p' na lab rd P O o ws ts fs g q keeps ih =>
    intro hu hr
    obtain ⟨q', hu', hr', hi', hm', he'⟩ := ih hu.2 hr
    refine ⟨AggQueryIn.WinExpr (lab := lab) (rd := rd) P O o ws ts fs g q' keeps,
      ⟨hmem hu.1 (by decide), hu'⟩, hr', fun Θ hi => hi.elim, hm',
      fun D γ h => ⟨(he' D γ h).1, ?_⟩⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [(he' D γ h).2]

end AggQueryIn

/-! ## The row, and the classification -/

/-- **`σ` or the apply is in every basis of the whole algebra**: the chain
of diamonds again. Over classes with neither, every bag recursion of the
match is its base, so the match is a query with no bag recursion, whose
answers are polynomial in the instance. -/
theorem sel_or_apply_mem_of_generatesAt {cnt : SeqAggFunc ℕ} (hcnt : cnt.ReadsCount)
    {S : Set OpKind} (hS : GeneratesAt ℕ schemaSE cnt S chainWitness) :
    OpKind.sel ∈ S ∨ OpKind.apply ∈ S := by
  by_contra h
  obtain ⟨hsel, hap⟩ := not_or.mp h
  obtain ⟨κ', q', hsch, hu', hsig', he⟩ := hS overSchema_chainWitness
    usesOnly_chainWitness inSig_chainWitness
  obtain ⟨q'', hu'', hr'', hi'', -, hse⟩ :=
    AggQueryIn.exists_dropMu hsel hap q' hu' (q'.hygienic_of_overSchema _ hsch)
  obtain ⟨b, k, hb⟩ := AggQueryIn.exists_polyBound_rec (S := S \ {OpKind.muBag}) (by simp)
    hcnt q'' hu'' hr'' (hi'' _ hsig')
  refine chainWitness_no_polynomial_bound ⟨b, k, fun n => ?_⟩
  have hs := he.settles (dChain n) (fun j => j.elim0) (settlesAt_chainWitness n)
  rw [hs.2, (hse _ _ hs.1).2]
  exact hb _ _ (hse _ _ hs.1).1

/-- `σ` or the apply is in every basis of the whole algebra. -/
theorem sel_or_apply_mem_of_generatesOnRec {cnt : SeqAggFunc ℕ} (hcnt : cnt.ReadsCount)
    {S : Set OpKind} (hS : GeneratesOnRec ℕ schemaSE cnt S) :
    OpKind.sel ∈ S ∨ OpKind.apply ∈ S :=
  sel_or_apply_mem_of_generatesAt hcnt (hS _)

/-- **The difference and the product together are not a basis**:
`{∅, Π, −, ×, γ, win, μ^⊎}` does not generate the whole algebra in the
minimal universe. -/
theorem not_generatesOnRec_prodDiff :
    ¬ GeneratesOnRec ℕ schemaSE SeqAggFunc.count
      {OpKind.empty, OpKind.proj, OpKind.diff, OpKind.prod, OpKind.gamma, OpKind.win,
        OpKind.muBag} := by
  intro h
  rcases sel_or_apply_mem_of_generatesOnRec SeqAggFunc.isCount_count_nat.readsCount h with h | h
  · simp at h
  · simp at h

/-- **The generating sets of the whole algebra in the minimal universe**,
over `ℕ` with the counting aggregate: exactly the supersets of one of the
three bases, `{∅, Π, σ, apply, γ, win, μ^⊎}`, `{∅, Π, σ, ×, γ, win, μ^⊎}`
and `{∅, Π, −, apply, γ, win, μ^⊎}`. -/
theorem generatesOnRec_iff {S : Set OpKind} :
    (∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S)
      ↔ basisRecOps ⊆ S ∨ Sym.basisProdOps ⊆ S ∨ basisRecDiffOps ⊆ S := by
  constructor
  · intro hgen
    obtain ⟨he, hp, hg, hm, hwin, hs, ha⟩ := required_mem_of_generatesOnRec hgen
    have hsa := sel_or_apply_mem_of_generatesOnRec
      SeqAggFunc.isCount_count_nat.readsCount (hgen schemaSE)
    by_cases hsel : OpKind.sel ∈ S
    · rcases ha with hprod | happ
      · refine Or.inr (Or.inl ?_)
        intro x hx
        simp only [Sym.basisProdOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      · refine Or.inl ?_
        intro x hx
        simp only [basisRecOps, AggQueryIn.sumMuOps, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · have hdiff := hs.resolve_left hsel
      have happ := hsa.resolve_left hsel
      refine Or.inr (Or.inr ?_)
      intro x hx
      simp only [basisRecDiffOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rintro (h | h | h) sch
    · exact generatesOnRec_of_basisRecOps_subset sch _ SeqAggFunc.isCount_count_nat h
    · exact GeneratesOnRec.mono h
        (Sym.basisProdOps_generatesOnRec sch _ SeqAggFunc.isCount_count_nat)
    · exact GeneratesOnRec.mono h
        (basisRecDiffOps_generatesOnRec sch _ SeqAggFunc.isCount_count_nat)
