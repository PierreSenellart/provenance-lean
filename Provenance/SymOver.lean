import Provenance.SymStruct

/-!
# The apply written with products is well formed over the schema

A query is well formed over a schema when every relation it reads is
declared, and every name it binds is fresh in its scope. The constructions
of `Provenance.SymApply` bind names from a supply, sliced so that a
construction never binds, inside a recursion, the name that recursion
binds. `Sym.Over sch A q` says that `q` is well formed over `sch` and names
nothing outside `A`; each construction is shown to keep it, with `A` the
names of its input and its supply's.
-/

variable {T : Type} [ValueType T]

namespace Sym

/-- **Well formed over a schema, naming only names in `A`.** -/
def Over {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (sch : Schema)
    (A : String → Prop) (q : AggQueryIn T c n κ l) : Prop :=
  q.overSchema sch ∧ ∀ x ∈ q.names, A x

section Prim

variable {c : ℕ} {sch : Schema} {A A' : String → Prop}

omit [ValueType T] in
theorem Over.mono {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    {q : AggQueryIn T c n κ l} (h : Over sch A q) (hA : ∀ x, A x → A' x) : Over sch A' q :=
  ⟨h.1, fun x hx => hA x (h.2 x hx)⟩

omit [ValueType T] in
theorem over_projQ {N M : ℕ} {l : List (String × ℕ)} (F : Fin M → SA T c N)
    {q : AggQueryIn T c N (ColKind.allReg N) l} (h : Over sch A q) : Over sch A (projQ F q) := by
  unfold Over projQ
  rw [AggQueryIn.overSchema_castKind, AggQueryIn.names_castKind]
  exact h

omit [ValueType T] in
theorem over_prodR {a b : ℕ} {l₁ l₂ : List (String × ℕ)}
    {q₁ : AggQueryIn T c a (ColKind.allReg a) l₁} {q₂ : AggQueryIn T c b (ColKind.allReg b) l₂}
    (h₁ : Over sch A q₁) (h₂ : Over sch A q₂) : Over sch A (prodR q₁ q₂) := by
  unfold Over prodR
  rw [AggQueryIn.overSchema_castKind, AggQueryIn.names_castKind]
  refine ⟨⟨h₁.1, h₂.1⟩, fun x hx => ?_⟩
  rcases Finset.mem_union.mp hx with hx | hx
  · exact h₁.2 x hx
  · exact h₂.2 x hx

omit [ValueType T] in
theorem over_sel {N : ℕ} {κ : Fin N → ColKind} {l : List (String × ℕ)} (φ : GenPredIn T c κ)
    {q : AggQueryIn T c N κ l} (hφ : SelOK l φ) (h : Over sch A q) :
    Over sch A (AggQueryIn.Sel φ q hφ) := h

omit [ValueType T] in
theorem over_rel (n : ℕ) (s : String) (hs : sch s = some n) (hA : A s) :
    Over sch A (AggQueryIn.Rel (T := T) (c := c) n s) :=
  ⟨hs, fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hA⟩

omit [ValueType T] in
theorem over_hole (n : ℕ) (s : String) (hs : sch s = some n) (hA : A s) :
    Over sch A (AggQueryIn.Hole (T := T) (c := c) n s (ColKind.allReg n)) :=
  ⟨hs, fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hA⟩

omit [ValueType T] in
theorem over_param {m : ℕ} (pv : Fin m → T ⊕ Fin c) :
    Over sch A (AggQueryIn.Param pv (ColKind.allReg m)) :=
  ⟨trivial, fun x hx => absurd hx (Finset.notMem_empty x)⟩

omit [ValueType T] in
theorem over_constQ (a : T) : Over sch A (constQ (c := c) a) := over_param _

theorem over_emptyRel (n : ℕ) : Over sch A (AggQueryIn.emptyRel (T := T) (c := c) n) :=
  ⟨AggQueryIn.overSchema_emptyRel sch n, fun x hx => by
    rw [AggQueryIn.names_emptyRel] at hx; exact absurd hx (Finset.notMem_empty x)⟩

omit [ValueType T] in
theorem over_unitC : Over sch A (AggQueryIn.unitC (T := T) (c := c)) :=
  ⟨AggQueryIn.overSchema_unitC sch, fun x hx => by
    rw [AggQueryIn.names_unitC] at hx; exact absurd hx (Finset.notMem_empty x)⟩

omit [ValueType T] in
theorem over_dedupG {n : ℕ} {q : AggQueryIn T c n (ColKind.allReg n)} (h : Over sch A q) :
    Over sch A (AggQueryIn.dedupG q) :=
  ⟨AggQueryIn.overSchema_dedupG (q := q) h.1, fun x hx => by
    rw [AggQueryIn.names_dedupG] at hx; exact h.2 x hx⟩

omit [ValueType T] in
theorem over_allRegOf {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    {q : AggQueryIn T c n κ l} (h : Over sch A q) : Over sch A q.allRegOf := by
  unfold Over
  rw [AggQueryIn.overSchema_allRegOf, AggQueryIn.names_allRegOf]
  exact h

/-- **A union binds its two names**, fresh for its operands. -/
theorem over_sumByMuX {n : ℕ} (s₁ s₂ : String) {q₁ q₂ : AggQueryIn T c n (ColKind.allReg n)}
    (h₁ : Over sch A q₁) (h₂ : Over sch A q₂) (hs₁ : sch s₁ = none) (hs₂ : sch s₂ = none)
    (hA₁ : ¬ A s₁) (hA₂ : ¬ A s₂) :
    Over sch (fun x => A x ∨ x = s₁ ∨ x = s₂) (AggQueryIn.sumByMuX s₁ s₂ q₁ q₂) := by
  refine ⟨AggQueryIn.overSchema_sumByMuX sch s₁ s₂ q₁ q₂ hs₁ hs₂ (fun h => hA₁ (h₁.2 _ h))
    (fun h => hA₂ (h₂.2 _ h)) h₁.1 h₂.1, fun x hx => ?_⟩
  have := AggQueryIn.names_sumByMuX s₁ s₂ q₁ q₂ hx
  simp only [Finset.mem_insert, Finset.mem_union] at this
  rcases this with rfl | rfl | h | h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (h₁.2 x h)
  · exact Or.inl (h₂.2 x h)

theorem over_notInDiffX {k : ℕ} (s₁ s₂ : String) (cnt : SeqAggFunc T)
    {q₁ q₂ : AggQueryIn T c k (ColKind.allReg k)}
    (h₁ : Over sch A q₁) (h₂ : Over sch A q₂) (hs₁ : sch s₁ = none) (hs₂ : sch s₂ = none)
    (hA₁ : ¬ A s₁) (hA₂ : ¬ A s₂) :
    Over sch (fun x => A x ∨ x = s₁ ∨ x = s₂) (AggQueryIn.notInDiffX s₁ s₂ cnt q₁ q₂) := by
  refine ⟨AggQueryIn.overSchema_notInDiffX sch s₁ s₂ cnt hs₁ hs₂ (fun h => hA₁ (h₁.2 _ h))
    (fun h => hA₂ (h₂.2 _ h)) h₁.1 h₂.1, fun x hx => ?_⟩
  have := AggQueryIn.names_notInDiffX s₁ s₂ cnt q₁ q₂ hx
  simp only [Finset.mem_insert, Finset.mem_union] at this
  rcases this with rfl | rfl | h | h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (h₁.2 x h)
  · exact Or.inl (h₂.2 x h)

end Prim

/-! ## Supplies of names -/

section Supply

variable {c : ℕ} {sch : Schema} {A : String → Prop}

/-- **A union binding the next two names of a supply**, its operands
naming only later ones. -/
theorem over_sumByMuX_from {n : ℕ} (f : ℕ → String) (hf : Function.Injective f) (m : ℕ)
    {q₁ q₂ : AggQueryIn T c n (ColKind.allReg n)}
    (h₁ : Over sch (fun x => A x ∨ ∃ i, m + 2 ≤ i ∧ x = f i) q₁)
    (h₂ : Over sch (fun x => A x ∨ ∃ i, m + 2 ≤ i ∧ x = f i) q₂)
    (hsch : ∀ i, sch (f i) = none) (hA : ∀ i, ¬ A (f i)) :
    Over sch (fun x => A x ∨ ∃ i, m ≤ i ∧ x = f i)
        (AggQueryIn.sumByMuX (f m) (f (m + 1)) q₁ q₂) := by
  have hn : ∀ j, LT.lt j (m + 2) → ¬ (A (f j) ∨ ∃ i, m + 2 ≤ i ∧ f j = f i) := by
    rintro j hj (h | ⟨i, hi, he⟩)
    · exact hA j h
    · have := hf he; omega
  refine (over_sumByMuX _ _ h₁ h₂ (hsch _) (hsch _) (hn m (by omega)) (hn (m + 1) (by omega))).mono
    fun x hx => ?_
  rcases hx with (h | ⟨i, hi, rfl⟩) | rfl | rfl
  · exact Or.inl h
  · exact Or.inr ⟨i, by omega, rfl⟩
  · exact Or.inr ⟨m, le_rfl, rfl⟩
  · exact Or.inr ⟨m + 1, by omega, rfl⟩

end Supply

/-! ## The order queries and the environment -/

section EnvOver

variable {c : ℕ} {sch : Schema} {A : String → Prop}

theorem over_ltQ {p : ℕ} {R : AggQueryIn T c p (ColKind.allReg p)} (h : Over sch A R) :
    Over sch A (ltQ R) := over_sel _ _ (over_prodR h h)

theorem over_midQ {p : ℕ} {R : AggQueryIn T c p (ColKind.allReg p)} (h : Over sch A R) :
    Over sch A (midQ R) := over_projQ _ (over_sel _ _ (over_prodR (over_prodR h h) h))

theorem over_belowQ {p : ℕ} {R : AggQueryIn T c p (ColKind.allReg p)} (h : Over sch A R) :
    Over sch A (belowQ R) := over_projQ _ (over_ltQ h)

theorem over_aboveQ {p : ℕ} {R : AggQueryIn T c p (ColKind.allReg p)} (h : Over sch A R) :
    Over sch A (aboveQ R) := over_projQ _ (over_ltQ h)

omit [ValueType T] in
theorem over_nnQ {CQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Over sch A CQ) :
    Over sch A (nnQ CQ) := over_sel _ _ h

/-- The order queries name what their relation does and two names more. -/
theorem over_succQ (s₁ s₂ : String) (cnt : SeqAggFunc T) {p : ℕ}
    {R : AggQueryIn T c p (ColKind.allReg p)} (h : Over sch A R) (hs₁ : sch s₁ = none)
    (hs₂ : sch s₂ = none) (hA₁ : ¬ A s₁) (hA₂ : ¬ A s₂) :
    Over sch (fun x => A x ∨ x = s₁ ∨ x = s₂) (succQ s₁ s₂ cnt R) :=
  over_notInDiffX s₁ s₂ cnt (over_ltQ h) (over_midQ h) hs₁ hs₂ hA₁ hA₂

theorem over_leastQ (s₁ s₂ : String) (cnt : SeqAggFunc T) {p : ℕ}
    {R : AggQueryIn T c p (ColKind.allReg p)} (h : Over sch A R) (hs₁ : sch s₁ = none)
    (hs₂ : sch s₂ = none) (hA₁ : ¬ A s₁) (hA₂ : ¬ A s₂) :
    Over sch (fun x => A x ∨ x = s₁ ∨ x = s₂) (leastQ s₁ s₂ cnt R) :=
  over_notInDiffX s₁ s₂ cnt h (over_aboveQ h) hs₁ hs₂ hA₁ hA₂

theorem over_greatestQ (s₁ s₂ : String) (cnt : SeqAggFunc T) {p : ℕ}
    {R : AggQueryIn T c p (ColKind.allReg p)} (h : Over sch A R) (hs₁ : sch s₁ = none)
    (hs₂ : sch s₂ = none) (hA₁ : ¬ A s₁) (hA₂ : ¬ A s₂) :
    Over sch (fun x => A x ∨ x = s₁ ∨ x = s₂) (greatestQ s₁ s₂ cnt R) :=
  over_notInDiffX s₁ s₂ cnt h (over_belowQ h) hs₁ hs₂ hA₁ hA₂

omit [ValueType T] in
theorem over_powU {EQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Over sch A EQ) :
    ∀ K, Over sch A (powU EQ K)
  | 0 => by rw [powU]; exact over_unitC
  | K + 1 => by rw [powU]; exact over_prodR (over_powU h K) h

omit [ValueType T] in
theorem over_powX {m : ℕ} {R : AggQueryIn T c m (ColKind.allReg m)} (h : Over sch A R) :
    ∀ K, Over sch A (powX R K)
  | 0 => by rw [powX]; exact over_unitC
  | K + 1 => by rw [powX]; exact over_prodR (over_powX h K) h

variable (f : ℕ → String) (hf : Function.Injective f) (hsch : ∀ i, sch (f i) = none)
  (hA : ∀ i, ¬ A (f i))
include hf hsch hA

theorem over_alphaQ {CQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Over sch A CQ) :
    Over sch (fun x => A x ∨ ∃ i, LT.lt i 4 ∧ x = f i) (alphaQ f CQ) := by
  have hf' : Function.Injective (fun i => f (i + 0)) := fun a b hab => by
    have := hf hab; omega
  have hin : Over sch (fun x => A x ∨ ∃ i, 2 ≤ i ∧ x = f i)
      (AggQueryIn.sumByMuX (f 2) (f 3) (constQ (c := c) (0 : T)) (constQ ValueType.nonzero)) :=
    (over_sumByMuX_from f hf 2 (over_constQ _) (over_constQ _) hsch hA).mono fun x hx => by
      rcases hx with h | ⟨i, hi, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, rfl⟩
  have hin' : Over sch (fun x => A x ∨ ∃ i, 2 ≤ i ∧ LT.lt i 4 ∧ x = f i)
      (AggQueryIn.sumByMuX (f 2) (f 3) (constQ (c := c) (0 : T)) (constQ ValueType.nonzero)) := by
    refine ⟨hin.1, fun x hx => ?_⟩
    have := AggQueryIn.names_sumByMuX (f 2) (f 3) (constQ (c := c) (0 : T))
        (constQ ValueType.nonzero) hx
    simp only [Finset.mem_insert, Finset.mem_union] at this
    rcases this with rfl | rfl | h' | h'
    · exact Or.inr ⟨2, le_rfl, by omega, rfl⟩
    · exact Or.inr ⟨3, by omega, by omega, rfl⟩
    · exact absurd h' (Finset.notMem_empty _)
    · exact absurd h' (Finset.notMem_empty _)
  have hout := over_sumByMuX_from (A := A) f hf 0 (q₁ := nnQ CQ)
    (q₂ := AggQueryIn.sumByMuX (f 2) (f 3) (constQ (c := c) (0 : T)) (constQ ValueType.nonzero))
    ((over_nnQ h).mono fun x hx => Or.inl hx)
    (hin'.mono (A' := fun x => A x ∨ ∃ i, 0 + 2 ≤ i ∧ x = f i) fun x hx => by
      rcases hx with h | ⟨i, hi, -, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, rfl⟩) hsch hA
  refine ⟨(over_dedupG hout).1, fun x hx => ?_⟩
  rw [alphaQ, AggQueryIn.names_dedupG] at hx
  have := AggQueryIn.names_sumByMuX (f 0) (f 1) _ _ hx
  simp only [Finset.mem_insert, Finset.mem_union] at this
  rcases this with rfl | rfl | h' | h'
  · exact Or.inr ⟨0, by omega, rfl⟩
  · exact Or.inr ⟨1, by omega, rfl⟩
  · exact Or.inl (h.2 x h')
  · rcases hin'.2 x h' with h'' | ⟨i, -, hi, rfl⟩
    · exact Or.inl h''
    · exact Or.inr ⟨i, hi, rfl⟩

theorem over_ctrQ {CQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Over sch A CQ) (K : ℕ) :
    Over sch (fun x => A x ∨ ∃ i, LT.lt i 4 ∧ x = f i) (ctrQ f CQ K) :=
  over_powU (over_alphaQ f hf hsch hA h) K

theorem over_lqQ (cnt : SeqAggFunc T) {CQ : AggQueryIn T c 1 (ColKind.allReg 1)}
    (h : Over sch A CQ) (K : ℕ) : Over sch (fun x => A x ∨ ∃ i, x = f i) (lqQ f cnt CQ K) := by
  refine (over_leastQ (f 4) (f 5) cnt (over_ctrQ f hf hsch hA h K) (hsch _) (hsch _) ?_ ?_).mono
    fun x hx => ?_
  · rintro (h' | ⟨i, hi, he⟩)
    · exact hA _ h'
    · have := hf he; omega
  · rintro (h' | ⟨i, hi, he⟩)
    · exact hA _ h'
    · have := hf he; omega
  · rcases hx with (h' | ⟨i, -, rfl⟩) | rfl | rfl
    · exact Or.inl h'
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inr ⟨4, rfl⟩
    · exact Or.inr ⟨5, rfl⟩

theorem over_sqQ (cnt : SeqAggFunc T) {CQ : AggQueryIn T c 1 (ColKind.allReg 1)}
    (h : Over sch A CQ) (K : ℕ) : Over sch (fun x => A x ∨ ∃ i, x = f i) (sqQ f cnt CQ K) := by
  refine (over_succQ (f 6) (f 7) cnt (over_ctrQ f hf hsch hA h K) (hsch _) (hsch _) ?_ ?_).mono
    fun x hx => ?_
  · rintro (h' | ⟨i, hi, he⟩)
    · exact hA _ h'
    · have := hf he; omega
  · rintro (h' | ⟨i, hi, he⟩)
    · exact hA _ h'
    · have := hf he; omega
  · rcases hx with (h' | ⟨i, -, rfl⟩) | rfl | rfl
    · exact Or.inl h'
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inr ⟨6, rfl⟩
    · exact Or.inr ⟨7, rfl⟩

theorem over_thQ (k : ℕ) : ∀ r, Over sch (fun x => A x ∨ ∃ i, LT.lt i (2 * r) ∧ x = f i)
    (thQ (T := T) (c := c) f k r)
  | 0 => over_param _
  | r + 1 => by
    have h : Over sch (fun x => A x ∨ ∃ i, LT.lt i (2 * r) ∧ x = f i)
        (thQ (T := T) (c := c) f k r) :=
      over_thQ k r
    refine (over_sumByMuX (f (2 * r)) (f (2 * r + 1)) h (over_param _) (hsch _) (hsch _) ?_ ?_).mono
      fun x hx => ?_
    · rintro (h' | ⟨i, hi, he⟩)
      · exact hA _ h'
      · have := hf he; omega
    · rintro (h' | ⟨i, hi, he⟩)
      · exact hA _ h'
      · have := hf he; omega
    · rcases hx with (h' | ⟨i, hi, rfl⟩) | rfl | rfl
      · exact Or.inl h'
      · exact Or.inr ⟨i, by omega, rfl⟩
      · exact Or.inr ⟨2 * r, by omega, rfl⟩
      · exact Or.inr ⟨2 * r + 1, by omega, rfl⟩

omit hsch hA in
theorem ne_of_lt_inj {i j : ℕ} (h : i ≠ j) : f i ≠ f j := fun he => h (hf he)

theorem over_cellsQ (cnt : SeqAggFunc T) (k : ℕ) {CQ : AggQueryIn T c 1 (ColKind.allReg 1)}
    (h : Over sch A CQ) : Over sch (fun x => A x ∨ ∃ i, x = f i) (cellsQ f cnt k CQ) := by
  -- the pieces name only the supply's names from `8` on
  have hth : Over sch (fun x => A x ∨ ∃ i, 8 ≤ i ∧ x = f i) (thP (T := T) (c := c) f k) := by
    have hg : Function.Injective (fun i => f (i + 16)) := fun a b hab => by
      have := hf hab; omega
    exact (over_thQ (T := T) (c := c) (fun i => f (i + 16)) hg (fun _ => hsch _) (fun _ => hA _) k
      k).mono
      fun x hx => by
        rcases hx with h' | ⟨i, -, rfl⟩
        · exact Or.inl h'
        · exact Or.inr ⟨i + 16, by omega, rfl⟩
  have hnn := over_nnQ h
  have hpair : ∀ (j : ℕ), 8 ≤ j → ∀ {q : AggQueryIn T c (1 + 1) (ColKind.allReg (1 + 1))},
      Over sch (fun x => A x ∨ x = f j ∨ x = f (j + 1)) q →
      Over sch (fun x => A x ∨ ∃ i, 8 ≤ i ∧ x = f i) q :=
    fun j hj q hq => hq.mono fun x hx => by
      rcases hx with h' | rfl | rfl
      · exact Or.inl h'
      · exact Or.inr ⟨j, hj, rfl⟩
      · exact Or.inr ⟨j + 1, by omega, rfl⟩
  have hfr : ∀ j, ¬ A (f j) := hA
  have h1 : Over sch (fun x => A x ∨ ∃ i, 8 ≤ i ∧ x = f i) (concP k CQ) :=
    over_projQ _ (h.mono fun x hx => Or.inl hx)
  have h2 : Over sch (fun x => A x ∨ ∃ i, 8 ≤ i ∧ x = f i) (succP f cnt k CQ) :=
    over_projQ _ (over_prodR (hpair 8 le_rfl (over_succQ (f 8) (f 9) cnt hnn (hsch _) (hsch _)
      (hfr _) (hfr _))) hth)
  have h3 : Over sch (fun x => A x ∨ ∃ i, 8 ≤ i ∧ x = f i) (topP f cnt k CQ) :=
    over_projQ _ (over_prodR ((over_greatestQ (f 10) (f 11) cnt hnn (hsch _) (hsch _) (hfr _)
      (hfr _)).mono fun x hx => by
        rcases hx with h' | rfl | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨10, by omega, rfl⟩
        · exact Or.inr ⟨11, by omega, rfl⟩) hth)
  have h4 : Over sch (fun x => A x ∨ ∃ i, 8 ≤ i ∧ x = f i) (botP f cnt k CQ) :=
    over_projQ _ (over_prodR ((over_leastQ (f 12) (f 13) cnt hnn (hsch _) (hsch _) (hfr _)
      (hfr _)).mono fun x hx => by
        rcases hx with h' | rfl | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨12, by omega, rfl⟩
        · exact Or.inr ⟨13, by omega, rfl⟩) hth)
  have h5 : Over sch (fun x => A x ∨ ∃ i, 8 ≤ i ∧ x = f i) (botEP f cnt k CQ) :=
    over_projQ _ (over_prodR ((over_notInDiffX (f 14) (f 15) cnt (over_unitC (A := A))
      (over_projQ _ hnn) (hsch _) (hsch _) (hfr _) (hfr _)).mono fun x hx => by
        rcases hx with h' | rfl | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨14, by omega, rfl⟩
        · exact Or.inr ⟨15, by omega, rfl⟩) hth)
  have hlift : ∀ m m', m' ≤ m → ∀ {q : AggQueryIn T c (7 + k) (ColKind.allReg (7 + k))},
      Over sch (fun x => A x ∨ ∃ i, m ≤ i ∧ x = f i) q →
      Over sch (fun x => A x ∨ ∃ i, m' ≤ i ∧ x = f i) q :=
    fun m m' hm q hq => hq.mono fun x hx => by
      rcases hx with h' | ⟨i, hi, rfl⟩
      · exact Or.inl h'
      · exact Or.inr ⟨i, by omega, rfl⟩
  have u3 := over_sumByMuX_from f hf 6 h4 h5 hsch hA
  have u2' := over_sumByMuX_from f hf 4 (hlift 8 6 (by omega) h3) u3 hsch hA
  have u1 := over_sumByMuX_from f hf 2 (hlift 8 4 (by omega) h2) u2' hsch hA
  have u0 := over_sumByMuX_from f hf 0 (hlift 8 2 (by omega) h1) u1 hsch hA
  exact (over_dedupG u0).mono fun x hx => by
    rcases hx with h' | ⟨i, -, rfl⟩
    · exact Or.inl h'
    · exact Or.inr ⟨i, rfl⟩

theorem over_descQ (cnt : SeqAggFunc T) (k : ℕ) {CQ : AggQueryIn T c 1 (ColKind.allReg 1)}
    (h : Over sch A CQ) : Over sch (fun x => A x ∨ ∃ i, x = f i) (descQ f cnt k CQ) :=
  over_projQ _ (over_powX (over_cellsQ f hf hsch hA cnt k h) k)

end EnvOver

/-- **The environment's queries are well formed, naming only `A`.** -/
structure EnvOver {k c : ℕ} (sch : Schema) (A : String → Prop) (env : SymEnv T k c) : Prop where
  cq : Over sch A env.CQ
  desc : Over sch A env.Desc
  lq : ∀ n, Over sch A (env.Lq n)
  sq : ∀ n, Over sch A (env.Sq n)

theorem envOver_envOf {c : ℕ} {sch : Schema} {A : String → Prop} (f : ℕ → String)
    (hf : Function.Injective f) (hsch : ∀ i, sch (f i) = none) (hA : ∀ i, ¬ A (f i))
    (cnt : SeqAggFunc T) (k : ℕ) {CQ : AggQueryIn T c 1 (ColKind.allReg 1)} (h : Over sch A CQ) :
    EnvOver sch (fun x => A x ∨ ∃ i, x = f i) (envOf f cnt k CQ) := by
  have h0 : Function.Injective (fun i => f (2 * i)) := fun a b hab => by have := hf hab; omega
  have h1 : Function.Injective (fun i => f (2 * i + 1)) := fun a b hab => by
    have := hf hab; omega
  have hm : ∀ (g : ℕ → String), (∀ i, ∃ j, g i = f j) → ∀ x, (A x ∨ ∃ i, x = g i) →
      (A x ∨ ∃ i, x = f i) := fun g hg x hx => by
    rcases hx with h' | ⟨i, rfl⟩
    · exact Or.inl h'
    · obtain ⟨j, hj⟩ := hg i; exact Or.inr ⟨j, hj⟩
  refine ⟨h.mono fun x hx => Or.inl hx, ?_, fun n => ?_, fun n => ?_⟩
  · exact (over_descQ _ h0 (fun _ => hsch _) (fun _ => hA _) cnt k h).mono
      (hm _ fun i => ⟨2 * i, rfl⟩)
  · exact (over_lqQ _ h1 (fun _ => hsch _) (fun _ => hA _) cnt h _).mono
      (hm _ fun i => ⟨2 * i + 1, rfl⟩)
  · exact (over_sqQ _ h1 (fun _ => hsch _) (fun _ => hA _) cnt h _).mono
      (hm _ fun i => ⟨2 * i + 1, rfl⟩)

/-! ## The relations a query reads -/

/-- **Every relation the query reads is declared, its name in `A`.** -/
def RelsIn (sch : Schema) (A : String → Prop) : {c n : ℕ} → {κ : Fin n → ColKind} →
    {l : List (String × ℕ)} → AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel n s => sch s = some n ∧ A s
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => RelsIn sch A q
  | _, _, _, _, .Sel _ q _ => RelsIn sch A q
  | _, _, _, _, .Prod q₁ q₂ => RelsIn sch A q₁ ∧ RelsIn sch A q₂
  | _, _, _, _, .Apply q₁ q₂ => RelsIn sch A q₁ ∧ RelsIn sch A q₂
  | _, _, _, _, .Sum q₁ q₂ => RelsIn sch A q₁ ∧ RelsIn sch A q₂
  | _, _, _, _, .Dedup q => RelsIn sch A q
  | _, _, _, _, .Diff q₁ q₂ => RelsIn sch A q₁ ∧ RelsIn sch A q₂
  | _, _, _, _, .Explode _ _ q => RelsIn sch A q
  | _, _, _, _, .Retag _ q => RelsIn sch A q
  | _, _, _, _, .Mu _ q₀ q₁ => RelsIn sch A q₀ ∧ RelsIn sch A q₁
  | _, _, _, _, .MuSet _ q₀ q₁ => RelsIn sch A q₀ ∧ RelsIn sch A q₁
  | _, _, _, _, .Gamma _ _ _ q _ _ => RelsIn sch A q
  | _, _, _, _, .GammaScalar _ _ q _ => RelsIn sch A q
  | _, _, _, _, .GammaNest _ _ _ _ q => RelsIn sch A q
  | _, _, _, _, .ProvSum _ _ _ q => RelsIn sch A q
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => RelsIn sch A q
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => RelsIn sch A q
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => RelsIn sch A q

omit [ValueType T] in
theorem relsIn_update {sch : Schema} {A : String → Prop} {t : String} {m : ℕ} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.noMention t → (RelsIn (sch.update t m) A q ↔ RelsIn sch A q) := by
  intro c n κ l q
  induction q with
  | Rel n s' =>
    intro hq
    show ((sch.update t m) s' = some n ∧ A s') ↔ (sch s' = some n ∧ A s')
    rw [Schema.update_apply, ite_eq_right hq]
  | Hole => exact fun _ => Iff.rfl
  | Param => exact fun _ => Iff.rfl
  | Empty => exact fun _ => Iff.rfl
  | Proj _ _ ih => exact fun hq => ih hq
  | Sel _ _ _ ih => exact fun hq => ih hq
  | Prod _ _ ih₁ ih₂ => exact fun hq => and_congr (ih₁ hq.1) (ih₂ hq.2)
  | Apply _ _ ih₁ ih₂ => exact fun hq => and_congr (ih₁ hq.1) (ih₂ hq.2)
  | Sum _ _ ih₁ ih₂ => exact fun hq => and_congr (ih₁ hq.1) (ih₂ hq.2)
  | Dedup _ ih => exact fun hq => ih hq
  | Diff _ _ ih₁ ih₂ => exact fun hq => and_congr (ih₁ hq.1) (ih₂ hq.2)
  | Explode _ _ _ ih => exact fun hq => ih hq
  | Retag _ _ ih => exact fun hq => ih hq
  | Mu _ _ _ ih₀ ih₁ => exact fun hq => and_congr (ih₀ hq.1) (ih₁ hq.2)
  | MuSet _ _ _ ih₀ ih₁ => exact fun hq => and_congr (ih₀ hq.1) (ih₁ hq.2)
  | Gamma _ _ _ _ _ _ ih => exact fun hq => ih hq
  | GammaScalar _ _ _ _ ih => exact fun hq => ih hq
  | GammaNest _ _ _ _ _ ih => exact fun hq => ih hq
  | ProvSum _ _ _ _ ih => exact fun hq => ih hq
  | GammaTok _ _ _ _ _ _ _ ih => exact fun hq => ih hq
  | Win _ _ _ _ _ _ _ _ _ _ ih => exact fun hq => ih hq
  | WinExpr _ _ _ _ _ _ _ _ _ ih => exact fun hq => ih hq

omit [ValueType T] in
/-- **A well-formed hygienic query reads only declared relations.** -/
theorem relsIn_of_overSchema {A : String → Prop} :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      {sch : Schema}, q.overSchema sch → q.hygienic → (∀ x ∈ q.names, A x) → RelsIn sch A q := by
  intro c n κ l q
  induction q with
  | Rel n s' => exact fun ho _ hA => ⟨ho, hA s' (Finset.mem_singleton_self _)⟩
  | Hole => exact fun _ _ _ => trivial
  | Param => exact fun _ _ _ => trivial
  | Empty => exact fun _ _ _ => trivial
  | Proj _ _ ih => exact fun ho hr hA => ih ho hr hA
  | Sel _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | Prod _ _ ih₁ ih₂ =>
    exact fun ho hr hA => ⟨ih₁ ho.1 hr.1 fun x hx => hA x (Finset.mem_union_left _ hx),
      ih₂ ho.2 hr.2 fun x hx => hA x (Finset.mem_union_right _ hx)⟩
  | Apply _ _ ih₁ ih₂ =>
    exact fun ho hr hA => ⟨ih₁ ho.1 hr.1 fun x hx => hA x (Finset.mem_union_left _ hx),
      ih₂ ho.2 hr.2 fun x hx => hA x (Finset.mem_union_right _ hx)⟩
  | Sum _ _ ih₁ ih₂ =>
    exact fun ho hr hA => ⟨ih₁ ho.1 hr.1 fun x hx => hA x (Finset.mem_union_left _ hx),
      ih₂ ho.2 hr.2 fun x hx => hA x (Finset.mem_union_right _ hx)⟩
  | Dedup _ ih => exact fun ho hr hA => ih ho hr hA
  | Diff _ _ ih₁ ih₂ =>
    exact fun ho hr hA => ⟨ih₁ ho.1 hr.1 fun x hx => hA x (Finset.mem_union_left _ hx),
      ih₂ ho.2 hr.2 fun x hx => hA x (Finset.mem_union_right _ hx)⟩
  | Explode _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | Retag _ _ ih => exact fun ho hr hA => ih ho hr hA
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro sch ho hr hA
    refine ⟨ih₀ ho.2.1 hr.2.2.1 fun x hx => hA x (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ hx)), ?_⟩
    exact (relsIn_update q₁ hr.2.1).mp (ih₁ ho.2.2.2 hr.2.2.2 fun x hx =>
      hA x (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro sch ho hr hA
    refine ⟨ih₀ ho.2.1 hr.2.2.1 fun x hx => hA x (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ hx)), ?_⟩
    exact (relsIn_update q₁ hr.2.1).mp (ih₁ ho.2.2.2 hr.2.2.2 fun x hx =>
      hA x (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)))
  | Gamma _ _ _ _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | GammaScalar _ _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | GammaNest _ _ _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | ProvSum _ _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | GammaTok _ _ _ _ _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | Win _ _ _ _ _ _ _ _ _ _ ih => exact fun ho hr hA => ih ho hr hA
  | WinExpr _ _ _ _ _ _ _ _ _ ih => exact fun ho hr hA => ih ho hr hA

omit [ValueType T] in
theorem Over.update {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} {sch : Schema}
    {A : String → Prop} {q : AggQueryIn T c n κ l} (h : Over sch A q) {t : String} (ht : ¬ A t)
    (m : ℕ) : Over (sch.update t m) A q :=
  ⟨AggQueryIn.overSchema_update_of_not_mem_names q h.1 (fun hm => ht (h.2 t hm)), h.2⟩

theorem EnvOver.update {k c : ℕ} {sch : Schema} {A : String → Prop} {env : SymEnv T k c}
    (h : EnvOver sch A env) {t : String} (ht : ¬ A t) (m : ℕ) : EnvOver (sch.update t m) A env :=
  ⟨h.cq.update ht m, h.desc.update ht m, fun n => (h.lq n).update ht m,
    fun n => (h.sq n).update ht m⟩

theorem EnvOver.mono {k c : ℕ} {sch : Schema} {A A' : String → Prop} {env : SymEnv T k c}
    (h : EnvOver sch A env) (hA : ∀ x, A x → A' x) : EnvOver sch A' env :=
  ⟨h.cq.mono hA, h.desc.mono hA, fun n => (h.lq n).mono hA, fun n => (h.sq n).mono hA⟩

omit [ValueType T] in
theorem noMention_of_relsIn {sch : Schema} {A : String → Prop} {t : String} (ht : ¬ A t) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      RelsIn sch A q → q.noMention t := by
  intro c n κ l q
  induction q with
  | Rel n s' => exact fun h he => ht (he ▸ h.2)
  | Hole => exact fun _ => trivial
  | Param => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj _ _ ih => exact fun h => ih h
  | Sel _ _ _ ih => exact fun h => ih h
  | Prod _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup _ ih => exact fun h => ih h
  | Diff _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode _ _ _ ih => exact fun h => ih h
  | Retag _ _ ih => exact fun h => ih h
  | Mu _ _ _ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet _ _ _ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma _ _ _ _ _ _ ih => exact fun h => ih h
  | GammaScalar _ _ _ _ ih => exact fun h => ih h
  | GammaNest _ _ _ _ _ ih => exact fun h => ih h
  | ProvSum _ _ _ _ ih => exact fun h => ih h
  | GammaTok _ _ _ _ _ _ _ ih => exact fun h => ih h
  | Win _ _ _ _ _ _ _ _ _ _ ih => exact fun h => ih h
  | WinExpr _ _ _ _ _ _ _ _ _ ih => exact fun h => ih h

theorem envNoMention_of_over {k c : ℕ} {sch : Schema} {A : String → Prop} {env : SymEnv T k c}
    (h : EnvOver sch A env) {t : String} (ht : ¬ A t) : EnvNoMention env t :=
  ⟨AggQueryIn.noMention_of_not_mem_names _ (fun hm => ht (h.cq.2 t hm)),
    AggQueryIn.noMention_of_not_mem_names _ (fun hm => ht (h.desc.2 t hm)),
    fun n => ⟨AggQueryIn.noMention_of_not_mem_names _ (fun hm => ht ((h.lq n).2 t hm)),
      AggQueryIn.noMention_of_not_mem_names _ (fun hm => ht ((h.sq n).2 t hm))⟩⟩

theorem over_junkB {c N M : ℕ} {sch : Schema} {A : String → Prop} (s : String)
    (hs : sch s = some M) (hA : A s) : Over sch A (junkB (T := T) (c := c) N M s) := by
  unfold Over junkB
  rw [AggQueryIn.overSchema_castKind, AggQueryIn.names_castKind]
  exact ⟨hs, fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hA⟩

/-- **The symbolic evaluation is well formed**, its recursions binding
names of its supply. -/
theorem over_sym_aux {k c : ℕ} (env : SymEnv T k c) (A : String → Prop) :
    ∀ (N : ℕ) (g : ℕ → String) {n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
      (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N → Function.Injective g →
      (∀ i, ¬ A (g i)) → ∀ (sch : Schema), (∀ i, sch (g i) = none) → EnvOver sch A env →
      RelsIn sch A q →
      Over sch (fun x => A x ∨ ∃ i, x = g i) (sym env g q)
        ∧ ∀ P s m, sch s = some ((k + m) * (7 + k) + P) →
          Over sch (fun x => A x ∨ (∃ i, x = g i) ∨ x = s) (symB env g P s m q) := by
  intro N
  induction N with
  | zero =>
    intro g n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro g n κ l q hq hg hgA sch hsch henv hrels
    have hjunk : ∀ P s m, sch s = some ((k + m) * (7 + k) + P) → ∀ {N'},
        Over sch (fun x => A x ∨ (∃ i, x = g i) ∨ x = s)
          (junkB (T := T) (c := c) N' ((k + m) * (7 + k) + P) s) :=
      fun P s m hs => over_junkB s hs (Or.inr (Or.inr rfl))
    have hemp : ∀ n', Over sch (fun x => A x ∨ ∃ i, x = g i)
        (AggQueryIn.emptyRel (T := T) (c := c) n') := fun n' => over_emptyRel n'
    have hD : Over sch (fun x => A x ∨ ∃ i, x = g i) env.Desc := henv.desc.mono fun x h => Or.inl h
    have hmonoB : ∀ s, ∀ {N' : ℕ} {l' : List (String × ℕ)}
        {q' : AggQueryIn T c N' (ColKind.allReg N') l'},
        Over sch (fun x => A x ∨ ∃ i, x = g i) q' →
        Over sch (fun x => A x ∨ (∃ i, x = g i) ∨ x = s) q' :=
      fun s _ _ _ h => h.mono fun x hx => by
        rcases hx with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    -- a sub-supply's names are the supply's
    have htri : ∀ j, Function.Injective (AggQueryIn.tri g j) ∧ (∀ i, ¬ A (AggQueryIn.tri g j i))
        ∧ (∀ i, sch (AggQueryIn.tri g j i) = none) :=
      fun j => ⟨AggQueryIn.tri_injective hg j, fun _ => hgA _, fun _ => hsch _⟩
    have hsub : ∀ j x, (A x ∨ ∃ i, x = AggQueryIn.tri g j i) → (A x ∨ ∃ i, x = g i) :=
      fun j x hx => by
        rcases hx with h' | ⟨i, rfl⟩
        · exact Or.inl h'
        · exact Or.inr ⟨3 * i + j, rfl⟩
    have hsubB : ∀ j s x, (A x ∨ (∃ i, x = AggQueryIn.tri g j i) ∨ x = s) →
        (A x ∨ (∃ i, x = g i) ∨ x = s) :=
      fun j s x hx => by
        rcases hx with h' | ⟨i, rfl⟩ | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl ⟨3 * i + j, rfl⟩)
        · exact Or.inr (Or.inr h')
    cases q with
    | Rel n s' =>
      refine ⟨?_, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
      rw [sym]
      exact over_projQ _ (over_prodR hD (over_rel n s' hrels.1 (Or.inl hrels.2)))
    | Hole n s' κ' =>
      refine ⟨by rw [sym]; exact hemp _, fun P s m hs => ?_⟩
      rw [symB]
      split
      · rename_i h; subst h
        exact over_hole _ s hs (Or.inr (Or.inr rfl))
      · exact hjunk P s m hs
    | Param pv ρ =>
      refine ⟨?_, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
      rw [sym]; exact over_projQ _ hD
    | Empty =>
      exact ⟨by rw [sym]; exact hemp _, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | Proj ps q =>
      obtain ⟨h₁, h₂⟩ := ih g q (by simp at hq; omega) hg hgA sch hsch henv hrels
      exact ⟨by rw [sym]; exact over_projQ _ h₁,
        fun P s m hs => by rw [symB]; exact over_projQ _ (h₂ P s m hs)⟩
    | Sel φ q hφ =>
      obtain ⟨h₁, h₂⟩ := ih g q (by simp at hq; omega) hg hgA sch hsch henv hrels
      exact ⟨by rw [sym]; exact over_sel _ _ h₁,
        fun P s m hs => by rw [symB]; exact over_sel _ _ (h₂ P s m hs)⟩
    | Prod q₁ q₂ =>
      obtain ⟨h₁, h₁'⟩ := ih (AggQueryIn.tri g 1) q₁ (by simp at hq; omega) (htri 1).1 (htri 1).2.1
        sch (htri 1).2.2 henv hrels.1
      obtain ⟨h₂, h₂'⟩ := ih (AggQueryIn.tri g 2) q₂ (by simp at hq; omega) (htri 2).1 (htri 2).2.1
        sch (htri 2).2.2 henv hrels.2
      refine ⟨?_, fun P s m hs => ?_⟩
      · rw [sym]
        exact over_projQ _ (over_sel _ _ (over_prodR (h₁.mono (hsub 1)) (h₂.mono (hsub 2))))
      · rw [symB]
        split
        · exact over_projQ _ (over_sel _ _ (over_prodR (hmonoB s (h₁.mono (hsub 1)))
            ((h₂' P s m hs).mono (hsubB 2 s))))
        · exact over_projQ _ (over_sel _ _ (over_prodR ((h₁' P s m hs).mono (hsubB 1 s))
            (hmonoB s (h₂.mono (hsub 2)))))
    | Explode i hi' q =>
      obtain ⟨h₁, h₂⟩ := ih g q (by simp at hq; omega) hg hgA sch hsch henv hrels
      exact ⟨by rw [sym]; exact h₁, fun P s m hs => by rw [symB]; exact h₂ P s m hs⟩
    | Retag h q =>
      obtain ⟨h₁, h₂⟩ := ih g q (by simp at hq; omega) hg hgA sch hsch henv hrels
      exact ⟨by rw [sym]; exact h₁, fun P s m hs => by rw [symB]; exact h₂ P s m hs⟩
    | Mu s' q₀ q₁ =>
      refine ⟨?_, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
      set t := AggQueryIn.tri g 0 0 with ht
      have hgA0 : ¬ A t := hgA _
      have hsch0 : sch t = none := hsch _
      have hne : ∀ i, t ≠ AggQueryIn.tri g 2 i := fun i he => by
        have := hg he; omega
      set sch' := sch.update t ((k + n) * (7 + k) + env.ctrK n) with hsch'
      obtain ⟨h₀, -⟩ := ih (AggQueryIn.tri g 1) q₀ (by simp at hq; omega) (htri 1).1 (htri 1).2.1
        sch (htri 1).2.2 henv hrels.1
      have henv' := henv.update hgA0 ((k + n) * (7 + k) + env.ctrK n)
      have hrels' : RelsIn sch' A q₁ := (relsIn_update q₁ (noMention_of_relsIn hgA0 q₁ hrels.2)).mpr
        hrels.2
      obtain ⟨-, h₁⟩ := ih (AggQueryIn.tri g 2) q₁ (by simp at hq; omega) (htri 2).1 (htri 2).2.1
        sch' (fun i => by
          rw [hsch', Schema.update_apply, ite_eq_right (hne i).symm]; exact hsch _) henv' hrels'
      have hb := h₁ (env.ctrK n) t n (AggQueryIn.Schema.update_self sch t _)
      have hbase : Over sch (fun x => A x ∨ ∃ i, x = g i)
          (prodR (sym env (AggQueryIn.tri g 1) q₀) (env.Lq n)) :=
        over_prodR (h₀.mono (hsub 1)) ((henv.lq n).mono fun x h => Or.inl h)
      have hstep : Over sch' (fun x => A x ∨ ∃ i, x = g i)
          (stepQ t (symB env (AggQueryIn.tri g 2) (env.ctrK n) t n q₁) (env.Sq n)) := by
        unfold stepQ
        refine over_projQ _ (over_sel _ _ (over_prodR (hb.mono fun x hx => ?_)
          ((henv'.sq n).mono fun x h => Or.inl h)))
        rcases hx with h' | ⟨i, rfl⟩ | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨3 * i + 2, rfl⟩
        · exact Or.inr ⟨0, rfl⟩
      have hnmB : (stepQ t (symB env (AggQueryIn.tri g 2) (env.ctrK n) t n q₁) (env.Sq n)).noMention
          t := by
        unfold stepQ
        rw [AggQueryIn.noMention_castKind]
        exact (noMention_prodR _ _).mpr ⟨(noMention_sym_aux env (envNoMention_of_over henv hgA0) _ _
          q₁ le_rfl (noMention_of_relsIn hgA0 q₁ hrels.2)).2 _ _ _,
          ((envNoMention_of_over henv hgA0).2.2 n).2⟩
      rw [sym, symMuQ]
      unfold Over
      rw [AggQueryIn.overSchema_castKind, AggQueryIn.names_castKind]
      refine ⟨⟨hsch0, hbase.1, hnmB, hstep.1⟩, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr ⟨0, rfl⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hbase.2 x hx
      · exact hstep.2 x hx
    | Gamma is ts fs q keep ord =>
      obtain ⟨h₁, -⟩ := ih g q (by simp at hq; omega) hg hgA sch hsch henv hrels
      refine ⟨?_, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
      rw [sym]
      exact over_projQ _ (over_allRegOf h₁)
    | GammaScalar ts fs q ord =>
      obtain ⟨h₁, -⟩ := ih (AggQueryIn.tri g 1) q (by simp at hq; omega) (htri 1).1 (htri 1).2.1
        sch (htri 1).2.2 henv hrels
      refine ⟨?_, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
      rw [sym]
      refine over_projQ _ (over_allRegOf ?_)
      have hu := over_sumByMuX (AggQueryIn.tri g 0 0) (AggQueryIn.tri g 0 1)
        (A := fun x => A x ∨ ∃ i, x = AggQueryIn.tri g 1 i)
        (over_projQ (padSA _) (henv.desc.mono fun x h => Or.inl h))
        (over_projQ (tagSA ValueType.nonzero) h₁) (hsch _) (hsch _)
        (by rintro (h' | ⟨i, he⟩); exact hgA _ h'; have := hg he; simp at this)
        (by rintro (h' | ⟨i, he⟩); exact hgA _ h'; have := hg he; simp at this; omega)
      exact hu.mono fun x hx => by
        rcases hx with (h' | ⟨i, rfl⟩) | rfl | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨3 * i + 1, rfl⟩
        · exact Or.inr ⟨0, rfl⟩
        · exact Or.inr ⟨3, rfl⟩
    | GammaNest is his p g' q =>
      obtain ⟨h₁, -⟩ := ih g q (by simp at hq; omega) hg hgA sch hsch henv hrels
      refine ⟨?_, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
      rw [sym]
      exact over_projQ _ (over_allRegOf h₁)
    | Win P O o w t g' q hrr dist keep =>
      obtain ⟨h₁, -⟩ := ih g q (by simp at hq; omega) hg hgA sch hsch henv hrels
      refine ⟨?_, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
      rw [sym]
      exact over_projQ _ (over_allRegOf h₁)
    | Apply => exact ⟨by rw [sym]; exact hemp _, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | Sum => exact ⟨by rw [sym]; exact hemp _, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | Dedup => exact ⟨by rw [sym]; exact hemp _, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | Diff => exact ⟨by rw [sym]; exact hemp _, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | MuSet => exact ⟨by rw [sym]; exact hemp _, fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | GammaTok => exact ⟨by rw [sym]; exact hemp _,
        fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | ProvSum => exact ⟨by rw [sym]; exact hemp _,
        fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩
    | WinExpr => exact ⟨by rw [sym]; exact hemp _,
        fun P s m hs => by rw [symB]; exact hjunk P s m hs⟩

/-! ## Supplies, sliced -/

/-- The names of `A` and of a supply. -/
def Sup (A : String → Prop) (f : ℕ → String) : String → Prop := fun x => A x ∨ ∃ i, x = f i

/-- **A supply of fresh names**: injective, undeclared, and outside `A`. -/
structure SupOK (sch : Schema) (A : String → Prop) (f : ℕ → String) : Prop where
  inj : Function.Injective f
  fresh : ∀ i, sch (f i) = none
  out : ∀ i, ¬ A (f i)

section Slices

variable {sch : Schema} {A B : String → Prop} {f : ℕ → String}

theorem SupOK.slice (h : SupOK sch A f) (ρ : ℕ → ℕ) (hrho : Function.Injective ρ) :
    SupOK sch A (fun i => f (ρ i)) :=
  ⟨fun _ _ he => hrho (h.inj he), fun _ => h.fresh _, fun _ => h.out _⟩

/-- A slice's names are outside another, disjoint slice and outside `A`. -/
theorem SupOK.slice_out (h : SupOK sch A f) (ρ τ : ℕ → ℕ) (hrt : ∀ i j, ρ i ≠ τ j)
    (hτ : Function.Injective τ) : SupOK sch (Sup A (fun i => f (ρ i))) (fun i => f (τ i)) :=
  ⟨fun _ _ he => hτ (h.inj he), fun _ => h.fresh _, fun j hj => by
    rcases hj with hj | ⟨i, hi⟩
    · exact h.out _ hj
    · exact hrt i j (h.inj hi).symm⟩

theorem SupOK.mono (h : SupOK sch B f) (hAB : ∀ x, A x → B x) : SupOK sch A f :=
  ⟨h.inj, h.fresh, fun i hi => h.out i (hAB _ hi)⟩

theorem sup_mono_slice (ρ : ℕ → ℕ) {x : String} (hx : Sup A (fun i => f (ρ i)) x) : Sup A f x := by
  rcases hx with hx | ⟨i, rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨ρ i, rfl⟩

theorem sup_mono_left (hAB : ∀ x, A x → B x) {x : String} (hx : Sup A f x) : Sup B f x := by
  rcases hx with hx | hx
  · exact Or.inl (hAB _ hx)
  · exact Or.inr hx

theorem sup_left {x : String} (hx : A x) : Sup A f x := Or.inl hx

end Slices

omit [ValueType T] in
theorem relsIn_mono {sch : Schema} {A B : String → Prop} (hAB : ∀ x, A x → B x) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      RelsIn sch A q → RelsIn sch B q := by
  intro c n κ l q
  induction q with
  | Rel n s' => exact fun h => ⟨h.1, hAB _ h.2⟩
  | Hole => exact fun _ => trivial
  | Param => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj _ _ ih => exact fun h => ih h
  | Sel _ _ _ ih => exact fun h => ih h
  | Prod _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Apply _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Sum _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Dedup _ ih => exact fun h => ih h
  | Diff _ _ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩
  | Explode _ _ _ ih => exact fun h => ih h
  | Retag _ _ ih => exact fun h => ih h
  | Mu _ _ _ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | MuSet _ _ _ ih₀ ih₁ => exact fun h => ⟨ih₀ h.1, ih₁ h.2⟩
  | Gamma _ _ _ _ _ _ ih => exact fun h => ih h
  | GammaScalar _ _ _ _ ih => exact fun h => ih h
  | GammaNest _ _ _ _ _ ih => exact fun h => ih h
  | ProvSum _ _ _ _ ih => exact fun h => ih h
  | GammaTok _ _ _ _ _ _ _ ih => exact fun h => ih h
  | Win _ _ _ _ _ _ _ _ _ _ ih => exact fun h => ih h
  | WinExpr _ _ _ _ _ _ _ _ _ ih => exact fun h => ih h

omit [ValueType T] in
theorem over_of_projQ {c N M : ℕ} {sch : Schema} {A : String → Prop} {l : List (String × ℕ)}
    (F : Fin M → SA T c N) {q : AggQueryIn T c N (ColKind.allReg N) l}
    (h : Over sch A (projQ F q)) : Over sch A q := by
  unfold Over projQ at h
  rw [AggQueryIn.overSchema_castKind, AggQueryIn.names_castKind] at h
  exact h

/-! ## The cut is well formed -/

section CutOver

variable {c : ℕ} {sch : Schema} {A : String → Prop}

theorem over_u2 {B : String → Prop} (f : ℕ → String) {a b : AggQueryIn T c 1 (ColKind.allReg 1)}
    (ha : Over sch B a) (hb : Over sch B b) (hf : SupOK sch B f) :
    Over sch (Sup B f) (u2 f a b) :=
  (over_sumByMuX _ _ ha hb (hf.fresh 0) (hf.fresh 1) (hf.out 0) (hf.out 1)).mono fun x hx => by
    rcases hx with hx | rfl | rfl
    · exact Or.inl hx
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩

theorem over_unionFin : ∀ (f : ℕ → String) (n : ℕ)
    (F : Fin n → AggQueryIn T c 1 (ColKind.allReg 1)),
    SupOK sch A f → (∀ i, Over sch A (F i)) → Over sch (Sup A f) (unionFin f n F)
  | _, 0, _, _, _ => by rw [unionFin]; exact over_emptyRel 1
  | f, n + 1, F, hf, hF => by
    rw [unionFin]
    have ih := over_unionFin (fun i => f (i + 2)) n (fun i => F i.succ)
      (hf.slice _ fun _ _ h => by omega) (fun i => hF i.succ)
    have hout : ∀ j, LT.lt j 2 → ¬ Sup A (fun i => f (i + 2)) (f j) := fun j hj hx => by
      rcases hx with hx | ⟨i, hi⟩
      · exact hf.out _ hx
      · have := hf.inj hi; omega
    refine (over_sumByMuX _ _ ((hF 0).mono fun x hx => Or.inl hx) ih (hf.fresh 0) (hf.fresh 1)
      (hout 0 (by omega)) (hout 1 (by omega))).mono fun x hx => ?_
    rcases hx with hx | rfl | rfl
    · exact sup_mono_slice _ hx
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩

theorem over_valsOf (f : ℕ → String) {n : ℕ} {q : AggQueryIn T c n (ColKind.allReg n)}
    (hf : SupOK sch A f) (h : Over sch A q) : Over sch (Sup A f) (valsOf f q) :=
  over_unionFin f n _ hf fun _ => over_projQ _ h

theorem over_colsQ {N p : ℕ} (f : ℕ → String) {q : AggQueryIn T c N (ColKind.allReg N)}
    (idx : Fin p → Fin N) (hf : SupOK sch A f) (h : Over sch A q) :
    Over sch (Sup A f) (colsQ f q idx) :=
  over_unionFin f p _ hf fun _ => over_projQ _ h

theorem over_ambQ (f : ℕ → String) (hf : SupOK sch A f) : Over sch (Sup A f) (ambQ (T := T) f c) :=
  over_unionFin f c _ hf fun _ => over_projQ _ over_unitC

theorem over_nullQ : Over sch A (nullQ (T := T) (c := c)) := by
  unfold nullQ
  split
  · exact over_constQ _
  · exact over_emptyRel 1

theorem over_constsQ (f : ℕ → String) (S : Finset T) (hf : SupOK sch A f) :
    Over sch (Sup A f) (constsQ (c := c) f S) :=
  over_unionFin f _ _ hf fun _ => over_constQ _

/-- The names of `A` and of a supply at the indices `P` holds of. -/
def SupP (A : String → Prop) (f : ℕ → String) (P : ℕ → Prop) : String → Prop :=
  fun x => A x ∨ ∃ i, P i ∧ x = f i

theorem supOK_part {f : ℕ → String} {P : ℕ → Prop} (hf : SupOK sch A f) (j : ℕ)
    (hP : ∀ i, ¬ P (8 * i + j)) : SupOK sch (SupP A f P) (part f j) :=
  ⟨fun a b he => by have := hf.inj he; omega, fun _ => hf.fresh _, fun i hx => by
    rcases hx with hx | ⟨i', hi', he⟩
    · exact hf.out _ hx
    · have := hf.inj he; subst this; exact hP i hi'⟩

theorem supP_part {B : String → Prop} {f : ℕ → String} {P : ℕ → Prop} (j : ℕ)
    (hP : ∀ i, P (8 * i + j)) (hB : ∀ x, B x → SupP A f P x) :
    ∀ x, Sup B (part f j) x → SupP A f P x := fun x hx => by
  rcases hx with hx | ⟨i, rfl⟩
  · exact hB x hx
  · exact Or.inr ⟨_, hP i, rfl⟩

theorem sup_of_supP {f : ℕ → String} {P : ℕ → Prop} {x : String} (hx : SupP A f P x) :
    Sup A f x := by
  rcases hx with hx | ⟨i, -, rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨i, rfl⟩

theorem supOK_of_part {f : ℕ → String} (hf : SupOK sch A f) (j : ℕ) :
    SupOK sch A (part f j) :=
  hf.slice (fun i => 8 * i + j) fun _ _ h => by simp only at h; omega

theorem over_cutOf (f : ℕ → String) (S : Finset T) {core : AggQueryIn T c 1 (ColKind.allReg 1)}
    (hf : SupOK sch A f) (h : Over sch A core) : Over sch (Sup A f) (cutOf f S core) := by
  have hP : ∀ j, j % 8 ≠ 0 → ∀ i, (fun j => j % 8 ≠ 0) (8 * i + j) := fun j hj i => by
    simp only; omega
  have hb : ∀ x, A x → SupP A f (fun j => j % 8 ≠ 0) x := fun x hx => Or.inl hx
  have h1 := over_u2 (part f 1) (B := Sup A (part f 2))
      ((over_nullQ (T := T) (c := c)).mono fun x hx => Or.inl hx)
    (over_ambQ _ (supOK_of_part hf 2)) (hf.slice_out (fun i => 8 * i + 2) (fun i => 8 * i + 1)
      (fun _ _ => by omega) (fun _ _ h => by simp only at h; omega))
  have h2 := over_u2 (part f 3) (B := Sup A (part f 4)) (over_constsQ _ S (supOK_of_part hf 4))
    (h.mono fun x hx => Or.inl hx) (hf.slice_out (fun i => 8 * i + 4) (fun i => 8 * i + 3)
      (fun _ _ => by omega) (fun _ _ h => by simp only at h; omega))
  refine (over_u2 (part f 0) (B := SupP A f (fun j => j % 8 ≠ 0))
    (h1.mono (supP_part 1 (hP 1 (by omega)) (supP_part 2 (hP 2 (by omega)) hb)))
    (h2.mono (supP_part 3 (hP 3 (by omega)) (supP_part 4 (hP 4 (by omega)) hb)))
    (supOK_part hf 0 fun i h => h (by omega))).mono fun x hx => ?_
  rcases hx with hx | ⟨i, rfl⟩
  · exact sup_of_supP hx
  · exact Or.inr ⟨_, rfl⟩

end CutOver

section CutCoreOver

variable {k c : ℕ} {sch : Schema} {A : String → Prop}

/-- **An aggregation's contribution to a cut is well formed**, given that
its raw symbolic counterpart is, in any environment and with any supply. -/
theorem over_aggCut (cnt : SeqAggFunc T) (f : ℕ → String) (hf : SupOK sch A f)
    {X : AggQueryIn T c 1 (ColKind.allReg 1)} (hX : Over sch (Sup A (part f 1)) X) (S : Finset T)
    {p p' : ℕ} (raw : SymEnv T k c → (ℕ → String) → AggQueryIn T c p (ColKind.allReg p))
    (idx : Fin p' → Fin p)
    (hraw : ∀ (B : String → Prop) (env : SymEnv T k c) (g : ℕ → String), (∀ x, A x → B x) →
      EnvOver sch B env → SupOK sch B g → Over sch (Sup B g) (raw env g)) :
    Over sch (Sup A f) (u2 (part f 0) X (colsQ (part f 2)
      (raw (envOf (part f 3) cnt k (cutOf (part f 4) S X)) (part f 5)) idx)) := by
  -- the names below slice `j`, other than slice `e`
  have hok : ∀ e, LT.lt e 8 → SupOK sch (SupP A f (fun i => i % 8 ≠ 0 ∧ i % 8 ≠ e)) (part f e) :=
    fun e he => supOK_part hf e fun i hi => hi.2 (by omega)
  have hin : ∀ {B : String → Prop} (j e : ℕ), LT.lt j 8 → j ≠ 0 → j ≠ e →
      (∀ x, B x → SupP A f (fun i => i % 8 ≠ 0 ∧ i % 8 ≠ e) x) →
      ∀ x, Sup B (part f j) x → SupP A f (fun i => i % 8 ≠ 0 ∧ i % 8 ≠ e) x :=
    fun j e hj h0 hje hB => supP_part j (fun i => ⟨by omega, by omega⟩) hB
  have hA' : ∀ e, ∀ x, A x → SupP A f (fun i => i % 8 ≠ 0 ∧ i % 8 ≠ e) x := fun _ x h => Or.inl h
  have hc := over_cutOf (part f 4) S ((hok 4 (by omega)).mono
    (hin 1 4 (by omega) (by omega) (by omega) (hA' 4))) hX
  have he := envOver_envOf (part f 3) (hok 3 (by omega)).inj (hok 3 (by omega)).fresh
    (fun i h => (hok 3 (by omega)).out i
      (hin 4 3 (by omega) (by omega) (by omega) (hin 1 3 (by omega) (by omega) (by omega)
        (hA' 3)) _ h)) cnt k hc
  have hr := hraw _ _ (part f 5) (fun x h => Or.inl (Or.inl (Or.inl h))) he
    ((hok 5 (by omega)).mono (hin 3 5 (by omega) (by omega) (by omega)
      (hin 4 5 (by omega) (by omega) (by omega) (hin 1 5 (by omega) (by omega) (by omega)
        (hA' 5)))))
  have hcols := over_colsQ (part f 2) idx ((hok 2 (by omega)).mono
    (hin 5 2 (by omega) (by omega) (by omega) (hin 3 2 (by omega) (by omega) (by omega)
      (hin 4 2 (by omega) (by omega) (by omega) (hin 1 2 (by omega) (by omega) (by omega)
        (hA' 2)))))) hr
  have hfin : ∀ x, SupP A f (fun i => i % 8 ≠ 0 ∧ i % 8 ≠ 0) x →
      SupP A f (fun i => i % 8 ≠ 0) x := fun x hx => by
    rcases hx with hx | ⟨i, hi, rfl⟩
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi.1, rfl⟩
  refine (over_u2 (part f 0) (B := SupP A f (fun i => i % 8 ≠ 0))
    (hX.mono fun x hx => hfin x (hin 1 0 (by omega) (by omega) (by omega) (hA' 0) x hx))
    (hcols.mono fun x hx => hfin x (hin 2 0 (by omega) (by omega) (by omega)
      (hin 5 0 (by omega) (by omega) (by omega) (hin 3 0 (by omega) (by omega) (by omega)
        (hin 4 0 (by omega) (by omega) (by omega) (hin 1 0 (by omega) (by omega) (by omega)
          (hA' 0))))) x hx))
    (supOK_part hf 0 fun i h => h (by omega))).mono fun x hx => ?_
  rcases hx with hx | ⟨i, rfl⟩
  · exact sup_of_supP hx
  · exact Or.inr ⟨_, rfl⟩

/-- **Two operands of a cut's union**, named by slices 1 and 2. -/
theorem over_u2Parts (f : ℕ → String) (hf : SupOK sch A f)
    {a b : AggQueryIn T c 1 (ColKind.allReg 1)}
    (ha : Over sch (Sup A (part f 1)) a) (hb : Over sch (Sup A (part f 2)) b) :
    Over sch (Sup A f) (u2 (part f 0) a b) := by
  have hA' : ∀ x, A x → SupP A f (fun i => i % 8 ≠ 0) x := fun x h => Or.inl h
  refine (over_u2 (part f 0) (B := SupP A f (fun i => i % 8 ≠ 0))
    (ha.mono (supP_part 1 (fun i => by omega) hA'))
    (hb.mono (supP_part 2 (fun i => by omega) hA'))
    (supOK_part hf 0 fun i h => h (by omega))).mono fun x hx => ?_
  rcases hx with hx | ⟨i, rfl⟩
  · exact sup_of_supP hx
  · exact Or.inr ⟨_, rfl⟩

/-- **The core of a cut is well formed.** -/
theorem over_cutCore (cnt : SeqAggFunc T) :
    ∀ (N : ℕ) (f : ℕ → String) {A : String → Prop} {n : ℕ} {κ : Fin n → ColKind}
      {l : List (String × ℕ)} (q : AggQueryIn T (k + c) n κ l), sizeOf q ≤ N →
      SupOK sch A f → RelsIn sch A q → Over sch (Sup A f) (cutCore cnt f q) := by
  intro N
  induction N with
  | zero =>
    intro f A n κ l q hq
    cases q <;> simp at hq
  | succ N ih =>
    intro f A n κ l q hq hf hr
    have hraw : ∀ {p : ℕ} {κn : Fin p → ColKind} (node : AggQueryIn T (k + c) p κn) {P : ℕ}
        (raw : SymEnv T k c → (ℕ → String) → AggQueryIn T c P (ColKind.allReg P))
        (F : Fin _ → SA T c P),
        (∀ env g, sym env g node = projQ F (raw env g)) → RelsIn sch A node →
        ∀ (B : String → Prop) (env : SymEnv T k c) (g : ℕ → String), (∀ x, A x → B x) →
          EnvOver sch B env → SupOK sch B g → Over sch (Sup B g) (raw env g) := by
      intro p κn node P raw F hsym hnode B env g hAB henv hg
      have := (over_sym_aux env B _ g node le_rfl hg.inj hg.out sch hg.fresh henv
        (relsIn_mono hAB node hnode)).1
      rw [hsym] at this
      exact over_of_projQ F this
    cases q with
    | Rel n s' => rw [cutCore]; exact over_valsOf f hf (over_rel n s' hr.1 hr.2)
    | Hole => rw [cutCore]; exact over_emptyRel 1
    | Param => rw [cutCore]; exact over_emptyRel 1
    | Empty => rw [cutCore]; exact over_emptyRel 1
    | Proj ps q => rw [cutCore]; exact ih f q (by simp at hq; omega) hf hr
    | Sel φ q _ => rw [cutCore]; exact ih f q (by simp at hq; omega) hf hr
    | Prod q₁ q₂ =>
      rw [cutCore]
      exact over_u2Parts f hf (ih _ q₁ (by simp at hq; omega) (supOK_of_part hf 1) hr.1)
        (ih _ q₂ (by simp at hq; omega) (supOK_of_part hf 2) hr.2)
    | Explode _ _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hf hr
    | Retag _ q => rw [cutCore]; exact ih f q (by simp at hq; omega) hf hr
    | Mu _ q₀ q₁ =>
      rw [cutCore]
      exact over_u2Parts f hf (ih _ q₀ (by simp at hq; omega) (supOK_of_part hf 1) hr.1)
        (ih _ q₁ (by simp at hq; omega) (supOK_of_part hf 2) hr.2)
    | Gamma is ts fs q keep ord =>
      rw [cutCore]
      exact over_aggCut cnt f hf (ih _ q (by simp at hq; omega) (supOK_of_part hf 1) hr) _ _ _
        (hraw (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) is ts fs q keep ord) _ _
          (fun env g => sym_Gamma env g is ts fs q keep ord) (by exact hr))
    | GammaScalar ts fs q ord =>
      rw [cutCore]
      exact over_aggCut cnt f hf (ih _ q (by simp at hq; omega) (supOK_of_part hf 1) hr) _ _ _
        (hraw (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false) ts fs q ord) _ _
          (fun env g => sym_GammaScalar env g ts fs q ord) (by exact hr))
    | GammaNest is his p g q =>
      rw [cutCore]
      exact over_aggCut cnt f hf (ih _ q (by simp at hq; omega) (supOK_of_part hf 1) hr) _ _ _
        (hraw (AggQueryIn.GammaNest (lab := 0) (rd := fun _ => false) is his p g q) _ _
          (fun env g' => sym_GammaNest env g' is his p g q) (by exact hr))
    | Win P O o w t g q hrr dist keep =>
      rw [cutCore]
      exact over_aggCut cnt f hf (ih _ q (by simp at hq; omega) (supOK_of_part hf 1) hr) _ _ _
        (hraw (AggQueryIn.Win (lab := 0) (rd := fun _ => false) P O o w t g q hrr dist keep) _ _
          (fun env g' => sym_Win env g' P O o w t g q hrr dist keep) (by exact hr))
    | Apply => rw [cutCore]; exact over_emptyRel 1
    | Sum => rw [cutCore]; exact over_emptyRel 1
    | Dedup => rw [cutCore]; exact over_emptyRel 1
    | Diff => rw [cutCore]; exact over_emptyRel 1
    | MuSet => rw [cutCore]; exact over_emptyRel 1
    | GammaTok => rw [cutCore]; exact over_emptyRel 1
    | ProvSum => rw [cutCore]; exact over_emptyRel 1
    | WinExpr => rw [cutCore]; exact over_emptyRel 1

end CutCoreOver

/-! ## The table and the apply are well formed -/

section TabOver

variable {k c : ℕ} {sch : Schema} {A : String → Prop}

theorem over_cutQ (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    {l : List (String × ℕ)} (q : AggQueryIn T (k + c) n κ l) (hf : SupOK sch A f)
    (hr : RelsIn sch A q) : Over sch (Sup A f) (cutQ cnt f q) := by
  have hA' : ∀ x, A x → SupP A f (fun i => i % 8 = 1) x := fun x h => Or.inl h
  have hc := over_cutOf (part f 0) q.allConsts (A := SupP A f (fun i => i % 8 = 1))
    (supOK_part hf 0 fun i h => by omega)
    ((over_cutCore cnt _ (part f 1) q le_rfl (supOK_of_part hf 1) hr).mono
      (supP_part 1 (fun i => by omega) hA'))
  refine hc.mono fun x hx => ?_
  rcases hx with hx | ⟨i, rfl⟩
  · exact sup_of_supP hx
  · exact Or.inr ⟨_, rfl⟩

theorem envOver_tabEnv' (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) (hf : SupOK sch A f) (hr : RelsIn sch A q) :
    EnvOver sch (SupP A f (fun i => i % 8 = 0 ∨ i % 8 = 1)) (tabEnv cnt f q) := by
  have hA' : ∀ x, A x → SupP A f (fun i => i % 8 = 1) x := fun x h => Or.inl h
  have hok := supOK_part hf 0 (P := fun i => i % 8 = 1) fun i h => by omega
  refine (envOver_envOf (part f 0) hok.inj hok.fresh hok.out cnt k
    ((over_cutQ cnt (part f 1) q (supOK_of_part hf 1) hr).mono
      (supP_part 1 (fun i => by omega) hA'))).mono fun x hx => ?_
  rcases hx with (hx | ⟨i, hi, rfl⟩) | ⟨i, rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨i, Or.inr hi, rfl⟩
  · exact Or.inr ⟨_, Or.inl (by omega), rfl⟩

theorem envOver_tabEnv (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) (hf : SupOK sch A f) (hr : RelsIn sch A q) :
    EnvOver sch (Sup A f) (tabEnv cnt f q) :=
  (envOver_tabEnv' cnt f q hf hr).mono fun _ hx => sup_of_supP hx

theorem over_tabQ (cnt : SeqAggFunc T) (f : ℕ → String) {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T (k + c) n κ) (hf : SupOK sch A f) (hr : RelsIn sch A q) :
    Over sch (Sup A f) (tabQ cnt f q) := by
  have hok := supOK_part hf 2 (P := fun i => i % 8 = 0 ∨ i % 8 = 1) fun i h => by omega
  refine ((over_sym_aux _ _ _ (part f 2) q le_rfl hok.inj hok.out sch hok.fresh
    (envOver_tabEnv' cnt f q hf hr) (relsIn_mono (fun x h => Or.inl h) q hr)).1).mono
    fun x hx => ?_
  rcases hx with hx | ⟨i, rfl⟩
  · exact sup_of_supP hx
  · exact Or.inr ⟨_, rfl⟩

theorem over_valsQ (f : ℕ → String) {env : SymEnv T k c} {VQ : AggQueryIn T c 1 (ColKind.allReg 1)}
    (henv : EnvOver sch A env) (hV : Over sch A VQ) (hf : SupOK sch A f) :
    Over sch (Sup A f) (valsQ f env VQ) :=
  over_dedupG (over_u2 f hV henv.cq hf)

/-- **The apply written with products is well formed**, naming the
names of its operands, of its pool and of its supply. The pool may name
anything but the names of the union the apply builds over it. -/
theorem over_applyX (cnt : SeqAggFunc T) (f : ℕ → String) {n₂ : ℕ} {l : List (String × ℕ)}
    {κ₂ : Fin n₂ → ColKind} {L : AggQueryIn T c k (ColKind.allReg k) l}
    {R : AggQueryIn T (k + c) n₂ κ₂} {VQ : AggQueryIn T c 1 (ColKind.allReg 1)}
    {AL AV : String → Prop} (hf : SupOK sch A f) (hL : Over sch AL L) (hR : RelsIn sch A R)
    (hV : Over sch AV VQ) (hAV : ∀ i, ¬ AV (part f 1 i)) :
    Over sch (fun x => Sup A f x ∨ AL x ∨ AV x) (applyX cnt f L R VQ) := by
  have h0 : ∀ x, Sup A (part f 0) x → Sup A f x := fun x hx => sup_mono_slice _ hx
  have henv := envOver_tabEnv cnt (part f 0) R (supOK_of_part hf 0) hR
  have hok : SupOK sch (fun x => AV x ∨ Sup A (part f 0) x) (part f 1) :=
    ⟨(supOK_of_part hf 1).inj, (supOK_of_part hf 1).fresh, fun i hx => by
      rcases hx with hx | hx
      · exact hAV i hx
      · rcases hx with hx | ⟨j, hj⟩
        · exact hf.out _ hx
        · have := hf.inj hj; omega⟩
  have hvals := over_valsQ (A := fun x => AV x ∨ Sup A (part f 0) x) (part f 1)
    (henv.mono fun x hx => Or.inr hx) (hV.mono fun x hx => Or.inl hx) hok
  unfold applyX
  refine over_projQ _ (over_sel _ _ (over_prodR (over_prodR (over_prodR
    ((henv.desc.mono h0).mono fun x hx => Or.inl hx)
    (((over_tabQ cnt (part f 0) R (supOK_of_part hf 0) hR).mono h0).mono fun x hx => Or.inl hx))
    (over_powU (hvals.mono fun x hx => ?_) n₂)) (hL.mono fun x hx => Or.inr (Or.inl hx))))
  rcases hx with (hx | hx) | ⟨i, rfl⟩
  · exact Or.inr (Or.inr hx)
  · exact Or.inl (h0 x hx)
  · exact Or.inl (Or.inr ⟨_, rfl⟩)

theorem noMention_applyX (cnt : SeqAggFunc T) (f : ℕ → String) {n₂ : ℕ} {l : List (String × ℕ)}
    {κ₂ : Fin n₂ → ColKind} {L : AggQueryIn T c k (ColKind.allReg k) l}
    {R : AggQueryIn T (k + c) n₂ κ₂} {VQ : AggQueryIn T c 1 (ColKind.allReg 1)} {s : String}
    (hL : L.noMention s) (hR : R.noMention s) (hV : VQ.noMention s) :
    (applyX cnt f L R VQ).noMention s := by
  have he := envNoMention_tabEnv cnt (part f 0) R hR
  unfold applyX projQ
  rw [AggQueryIn.noMention_castKind]
  exact (noMention_prodR _ _).mpr ⟨(noMention_prodR _ _).mpr ⟨(noMention_prodR _ _).mpr
    ⟨he.2.1, noMention_tabQ cnt _ R hR⟩, noMention_powU _ (AggQueryIn.noMention_dedupG _ _
      (noMention_u2 _ hV he.1)) n₂⟩, hL⟩

end TabOver

end Sym
