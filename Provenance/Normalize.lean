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
