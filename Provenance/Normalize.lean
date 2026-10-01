/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryBridges

/-!
# Normalizing a chain of selections

Under the joint reading a predicate's provenance is one `⊕` over the
worlds of the union of the families it reads, so `σ_{ψ₁ ∧ ψ₂}` is one
sum where `σ_{ψ₁} ∘ σ_{ψ₂}` is a product of two. The two agree exactly
where the conjunction decomposes, and over `ℕ` on one family they do
not – `4` against `2` (`natRangeToken_mul_ne_and`). So `HAVING p AND q`
and a `WHERE p` around a `HAVING q` of the same grouping, which a SQL
user would call one query, would denote different things.

They are made to agree by reading a chain as one predicate:
`AggQueryIn.normalize` merges adjacent selections, and a query is read
as `evaluate (normalize q)`. `AggQueryIn.normalize_chainFree` says the
result has no selection directly above a selection, and
`AggQueryIn.normalize_id_of_chainFree` that normalizing changes nothing
where there was no chain.

The equality this buys is up to impossible rows and not of relations,
for the reason `AggQueryIn.evaluate_Sel_reg_absorb` gives: a selection
with an aggregate atom keeps its failing rows annotated `𝟘` where a
regular one removes them, so merging a regular selection into the
predicate below it keeps rows the chain had dropped.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-- **Merge adjacent selections**: `σ_φ(σ_ψ(q))` becomes `σ_{φ ∧ ψ}(q)`,
recursively, so that a maximal chain becomes one selection on the
conjunction of its predicates, in the order they were written. -/
def AggQueryIn.normalize : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → AggQueryIn T c n κ
  | _, _, _, .Rel n s => .Rel n s
  | _, _, _, .Proj ps q => .Proj ps q.normalize
  | _, _, _, .Sel φ q =>
    match q.normalize with
    | .Sel ψ q' => .Sel (.and φ ψ) q'
    | q' => .Sel φ q'
  | _, _, _, .Prod q₁ q₂ => .Prod q₁.normalize q₂.normalize
  | _, _, _, .Apply q₁ q₂ => .Apply q₁.normalize q₂.normalize
  | _, _, _, .Sum q₁ q₂ => .Sum q₁.normalize q₂.normalize
  | _, _, _, .Dedup q => .Dedup q.normalize
  | _, _, _, .Diff q₁ q₂ => .Diff q₁.normalize q₂.normalize
  | _, _, _, .Alt k h q => .Alt k h q.normalize
  | _, _, _, .Mu b s q₀ q₁ => .Mu b s q₀.normalize q₁.normalize
  | _, _, _, .MuSet b s q₀ q₁ => .MuSet b s q₀.normalize q₁.normalize
  | _, _, _, .Gamma is ts fs q => .Gamma is ts fs q.normalize
  | _, _, _, .GammaScalar ts fs q => .GammaScalar ts fs q.normalize
  | _, _, _, .ProvSum is his t q => .ProvSum is his t q.normalize
  | _, _, _, .Retag h q => .Retag h q.normalize
  | _, _, _, .GammaTok is his ts fs a q => .GammaTok is his ts fs a q.normalize
  | _, _, _, .Win P O o w t f q dist => .Win P O o w t f q.normalize dist

/-- **No selection directly above a selection**: the shape a normalized
query has, and the shape on which a chain and its merge cannot differ
because there is no chain. -/
def AggQueryIn.chainFree : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Proj _ q => q.chainFree
  | _, _, _, .Sel _ (.Sel _ _) => False
  | _, _, _, .Sel _ q => q.chainFree
  | _, _, _, .Prod q₁ q₂ => q₁.chainFree ∧ q₂.chainFree
  | _, _, _, .Apply q₁ q₂ => q₁.chainFree ∧ q₂.chainFree
  | _, _, _, .Sum q₁ q₂ => q₁.chainFree ∧ q₂.chainFree
  | _, _, _, .Dedup q => q.chainFree
  | _, _, _, .Diff q₁ q₂ => q₁.chainFree ∧ q₂.chainFree
  | _, _, _, .Alt _ _ q => q.chainFree
  | _, _, _, .Mu _ _ q₀ q₁ => q₀.chainFree ∧ q₁.chainFree
  | _, _, _, .MuSet _ _ q₀ q₁ => q₀.chainFree ∧ q₁.chainFree
  | _, _, _, .Gamma _ _ _ q => q.chainFree
  | _, _, _, .GammaScalar _ _ q => q.chainFree
  | _, _, _, .ProvSum _ _ _ q => q.chainFree
  | _, _, _, .Retag _ q => q.chainFree
  | _, _, _, .GammaTok _ _ _ _ _ q => q.chainFree
  | _, _, _, .Win _ _ _ _ _ _ q _ => q.chainFree

omit [ValueType T] in
/-- **Normalizing leaves no chain.** -/
theorem AggQueryIn.normalize_chainFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.normalize.chainFree := by
  intro c n κ q
  induction q with
  | Rel n s => trivial
  | Proj ps q ih => exact ih
  | Sel φ q ih =>
    show (match q.normalize with
      | .Sel ψ q' => AggQueryIn.Sel (.and φ ψ) q'
      | q' => AggQueryIn.Sel φ q').chainFree
    split
    · next ψ q' heq =>
        rw [heq] at ih
        cases q' <;> exact ih
    · next hne => cases hq : q.normalize <;> simp_all [AggQueryIn.chainFree]
  | Prod q₁ q₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | Dedup q ih => exact ih
  | Diff q₁ q₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | Alt k h q ih => exact ih
  | Mu b s q₀ q₁ ih₀ ih₁ => exact ⟨ih₀, ih₁⟩
  | MuSet b s q₀ q₁ ih₀ ih₁ => exact ⟨ih₀, ih₁⟩
  | Gamma is ts fs q ih => exact ih
  | GammaScalar ts fs q ih => exact ih
  | ProvSum is his t q ih => exact ih
  | Retag h q ih => exact ih
  | GammaTok is his ts fs a q ih => exact ih
  | Win P O o w t f q dist ih => exact ih

omit [ValueType T] in
/-- **Normalizing changes nothing where there was no chain**, so it is
idempotent and imposes nothing on a query already in normal form. -/
theorem AggQueryIn.normalize_id_of_chainFree :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.chainFree → q.normalize = q := by
  intro c n κ q
  induction q with
  | Rel n s => intro _; rfl
  | Proj ps q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | Sel φ q ih =>
    intro h
    have hq : q.chainFree := by cases q <;> first | exact h.elim | exact h
    show (match q.normalize with
      | .Sel ψ q' => AggQueryIn.Sel (.and φ ψ) q'
      | q' => AggQueryIn.Sel φ q') = _
    rw [ih hq]
    cases q <;> first | exact h.elim | rfl
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro h; rw [AggQueryIn.normalize, ih₁ h.1, ih₂ h.2]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro h; rw [AggQueryIn.normalize, ih₁ h.1, ih₂ h.2]
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro h; rw [AggQueryIn.normalize, ih₁ h.1, ih₂ h.2]
  | Dedup q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro h; rw [AggQueryIn.normalize, ih₁ h.1, ih₂ h.2]
  | Alt k hk q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | Mu b s q₀ q₁ ih₀ ih₁ =>
    intro h; rw [AggQueryIn.normalize, ih₀ h.1, ih₁ h.2]
  | MuSet b s q₀ q₁ ih₀ ih₁ =>
    intro h; rw [AggQueryIn.normalize, ih₀ h.1, ih₁ h.2]
  | Gamma is ts fs q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | GammaScalar ts fs q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | ProvSum is his t q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | Retag hk q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | GammaTok is his ts fs a q ih => intro h; rw [AggQueryIn.normalize, ih h]
  | Win P O o w t f q dist ih => intro h; rw [AggQueryIn.normalize, ih h]

omit [ValueType T] in
/-- **Normalization is idempotent.** -/
theorem AggQueryIn.normalize_idem {c n : ℕ} {κ : Fin n → ColKind}
    (q : AggQueryIn T c n κ) : q.normalize.normalize = q.normalize :=
  AggQueryIn.normalize_id_of_chainFree _ (AggQueryIn.normalize_chainFree q)

/-! ## What the merge does to the pending factors

The concrete parts of a chain and of its merge always agree: both
multiply the two predicates' provenances in, and `K` is commutative.
The pending parts are the question, since the supersede test runs once
per selection in a chain and once on the union of the compared columns
in the merge. Over **one family** they agree exactly, with nothing asked
of `K`: each test reduces to "drop that family's factor", and dropping
it twice is dropping it once. -/

/-- The annotation lists the compared tokens of a predicate carry on a
row – what the evaluator's supersede test compares. -/
abbrev GenPredIn.comparedLists {c n : ℕ} {κ : Fin n → ColKind}
    (χ : GenPredIn T c κ) (u : Tuple (GenValue T K) n) : Multiset (List K) :=
  χ.comparedCols.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => some a.annList)

/-- Those of the *scalar* compared tokens, which block the supersede. -/
abbrev GenPredIn.comparedScalarLists {c n : ℕ} {κ : Fin n → ColKind}
    (χ : GenPredIn T c κ) (u : Tuple (GenValue T K) n) : Multiset (List K) :=
  χ.comparedCols.val.filterMap (fun k =>
    match u k with
    | Sum.inl _ => none
    | Sum.inr a => if a.scalar then some a.annList else none)

/-- **A predicate reads one family on a row**: every column it compares
holds a grouped token, and they all carry the same annotation list. -/
def GenPredIn.ReadsOne {c n : ℕ} {κ : Fin n → ColKind}
    (χ : GenPredIn T c κ) (u : Tuple (GenValue T K) n) (ℓ : List K) : Prop :=
  χ.comparedCols.Nonempty ∧
    ∀ k ∈ χ.comparedCols, ∃ a : AggTok T K, u k = Sum.inr a ∧
      a.scalar = false ∧ a.annList = ℓ

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Reading one family, every compared list is that family's. -/
theorem GenPredIn.mem_comparedLists {c n : ℕ} {κ : Fin n → ColKind}
    {χ : GenPredIn T c κ} {u : Tuple (GenValue T K) n} {ℓ : List K}
    (h : χ.ReadsOne u ℓ) {x : List K} (hx : x ∈ χ.comparedLists u) : x = ℓ := by
  obtain ⟨k, hk, hfk⟩ := (Multiset.mem_filterMap _ _).mp hx
  obtain ⟨a, hu, -, hocc⟩ := h.2 k (Finset.mem_val.mp hk)
  rw [hu] at hfk
  exact (Option.some.inj hfk).symm.trans hocc

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Reading one family, some column does hold a token. -/
theorem GenPredIn.comparedLists_ne_zero {c n : ℕ} {κ : Fin n → ColKind}
    {χ : GenPredIn T c κ} {u : Tuple (GenValue T K) n} {ℓ : List K}
    (h : χ.ReadsOne u ℓ) : χ.comparedLists u ≠ 0 := by
  obtain ⟨k, hk⟩ := h.1
  obtain ⟨a, hu, -, hocc⟩ := h.2 k hk
  intro hcon
  exact Multiset.notMem_zero ℓ (hcon ▸ (Multiset.mem_filterMap _ _).mpr
    ⟨k, Finset.mem_val.mpr hk, by rw [hu]; exact congrArg some hocc⟩)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Reading one family, no compared token is scalar. -/
theorem GenPredIn.comparedScalarLists_eq_zero {c n : ℕ} {κ : Fin n → ColKind}
    {χ : GenPredIn T c κ} {u : Tuple (GenValue T K) n} {ℓ : List K}
    (h : χ.ReadsOne u ℓ) : χ.comparedScalarLists u = 0 := by
  refine Multiset.eq_zero_of_forall_notMem (fun x hx => ?_)
  obtain ⟨k, hk, hfk⟩ := (Multiset.mem_filterMap _ _).mp hx
  obtain ⟨a, hu, hsc, -⟩ := h.2 k (Finset.mem_val.mp hk)
  simp [hu, hsc] at hfk

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- **The supersede test says "drop that family's factor"** when the
compared lists are all one list and none of them is scalar. Stated on
bare multisets so that it unifies with whatever the evaluator's clause
has built. -/
theorem Having.supersede_test_iff {S L : Multiset (List K)} {ℓ : List K}
    (hsc : S = 0) (hnz : L ≠ 0) (hall : ∀ x ∈ L, x = ℓ) (l : List K) :
    (¬(S = 0 ∧ L ≠ 0 ∧ ∀ l' ∈ L, l' = l)) ↔ l ≠ ℓ := by
  constructor
  · intro hn hl
    exact hn ⟨hsc, hnz, fun l' hl' => (hall l' hl').trans hl.symm⟩
  · rintro hne ⟨-, -, hforall⟩
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hnz
    exact hne ((hforall x hx).symm.trans (hall x hx))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- A conjunction of two predicates reading one family reads it too. -/
theorem GenPredIn.ReadsOne.and {c n : ℕ} {κ : Fin n → ColKind}
    {φ ψ : GenPredIn T c κ} {u : Tuple (GenValue T K) n} {ℓ : List K}
    (hφ : φ.ReadsOne u ℓ) (hψ : ψ.ReadsOne u ℓ) :
    (GenPredIn.and φ ψ).ReadsOne u ℓ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := hφ.1
    exact ⟨k, by
      show k ∈ φ.comparedCols ∪ ψ.comparedCols
      exact Finset.mem_union_left _ hk⟩
  · intro k hk
    rcases Finset.mem_union.mp (show k ∈ φ.comparedCols ∪ ψ.comparedCols from hk)
      with h | h
    · exact hφ.2 k h
    · exact hψ.2 k h

/-- **Merging a chain over one family is sound.** Where both predicates
read the same family on every row and both entail its existence, a
selection on the conjunction computes what the chain computes – the
concrete parts by commutativity, and the pending parts because each
supersede test says "drop that family's factor" and dropping it twice
is dropping it once. Nothing is asked of `K`. -/
theorem AggQueryIn.evaluate_Sel_merge_of_readsOne {c n : ℕ}
    {κ : Fin n → ColKind} (φ ψ : GenPredIn T c κ)
    (hφa : φ.hasAggAtom = true) (hψa : ψ.hasAggAtom = true)
    (hφe : φ.entailsExistence false = true)
    (hψe : ψ.entailsExistence false = true)
    (q : AggQueryIn T c n κ) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (ℓ : GenRow T K n → List K)
    (hone : ∀ r ∈ q.evaluate d γ,
      φ.ReadsOne r.fst (ℓ r) ∧ ψ.ReadsOne r.fst (ℓ r)) :
    (AggQueryIn.Sel (GenPredIn.and φ ψ) q).evaluate d γ
      = (AggQueryIn.Sel φ (AggQueryIn.Sel ψ q)).evaluate d γ := by
  simp only [AggQueryIn.evaluate]
  rw [ite_eq_left (show (GenPredIn.and φ ψ).hasAggAtom = true from by
      simp [GenPredIn.hasAggAtom, hφa]),
    ite_eq_left hψa, ite_eq_left hφa, Multiset.map_map]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  obtain ⟨hφ1, hψ1⟩ := hone r hr
  refine Prod.ext rfl ?_
  show (⟨_, _⟩ : GenAnn K) = ⟨_, _⟩
  have hiff : ∀ {χ : GenPredIn T c κ}, χ.ReadsOne r.fst (ℓ r) → ∀ l : List K,
      (¬(χ.comparedScalarLists r.fst = 0 ∧ χ.comparedLists r.fst ≠ 0
        ∧ ∀ l' ∈ χ.comparedLists r.fst, l' = l)) ↔ l ≠ ℓ r :=
    fun {χ} h l => Having.supersede_test_iff
      (GenPredIn.comparedScalarLists_eq_zero h)
      (GenPredIn.comparedLists_ne_zero h)
      (fun x hx => GenPredIn.mem_comparedLists h hx) l
  congr 1
  · simp only [GenPredIn.predsem_and, mul_comm, mul_left_comm]
  · simp only [GenPredIn.entailsExistence, hφe, hψe, Bool.false_eq_true,
      ite_false, Bool.or_self, ite_true]
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr (fun l _ =>
      (hiff (hφ1.and hψ1) l).trans
        ((and_congr (hiff hφ1 l) (hiff hψ1 l)).trans and_self_iff).symm)
