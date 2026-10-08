/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Decorrelate

/-!
# The basis, assembled

`thm:plainbasis` has two halves. The lower bounds are the six invariants
of `Provenance.PlainBasis`, each with a query that breaks it. The upper
bound is this file: **every query of the fragment is equivalent to one
using only the six classes `∅`, `Π`, `σ`, `×`, `⊎`, `γ`.**

It is three passes, in this order, each of which is a structural
recursion carrying the identities already proved:

1. **the windows go** (`AggQueryIn.exists_winFree`), each becoming an
   apply of a scalar aggregation (`prop:winderived`,
   `PlainBasis.winByApply`);
2. **the applies go** (`AggQueryIn.exists_applyFree_plainEquiv`), by the
   decorrelation of `Provenance.Decorrelate`, which leaves duplicate
   elimination and the difference behind;
3. **those two go** (`AggQueryIn.exists_basisOps_of_dedupDiff`), by the
   two identities of `sec:basis` – `ε` from a grouping, `−` from counts.

The order is forced: a window becomes an apply, so the windows must go
before the applies; and the decorrelation *builds* an `ε` (the distinct
rows of an apply's left side) and a `−` (the parameter rows a scalar
aggregation's slices do not reach), so those must go after. Each pass is
stated with the class set as a parameter, which is what lets them be
composed: it is only because the decorrelation of a window-free query is
window-free that the first pass is not undone by the second.

`AggQueryIn.exists_basisOps_plainEquiv` is the three passes composed,
and `Generates` reads it as a property of a set of classes
(`basisOps_generates`). The converse half – that a generating set has to
contain each class – is `generates_necessary`, from four of the six
invariants; its docstring says which two rows are not there and why.

Two bases of `thm:plainbasis` are *not* proved to generate: the ones
taking `−` for `σ` and the apply for `×`. Both identities are available
(`AggQueryIn.sel_plainEquiv_selByDiff_polTerm`,
`AggQueryIn.apply_plainEquiv_prod`); what is missing is the pass that
applies them, which is the same recursion again in the other direction.
-/

variable {T : Type} [ValueType T]

/-! ## What a window has to be for `prop:winderived` to reach it -/

/-- **Every window of the query is derivable.** At each window: its
input's columns are all regular (an apply reads its left side as a
relation of values), its frame contains its current row, it carries
neither `DISTINCT` nor a `FILTER` clause, and its frame condition is a
predicate – which in SQL it is, being a frame clause, while in the
library `ValueFrame.ρ` is an arbitrary relation on order values.

A *multi-frame* window is not derivable at all: its column combines the
leaves' values by a function no term expresses, so the predicate reads
`False` there. -/
def AggQueryIn.WinsDerivable : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Empty => True
  | _, _, _, .Proj _ q => q.WinsDerivable
  | _, _, _, .Sel _ q => q.WinsDerivable
  | _, _, _, .Prod q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, .Apply q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, .Sum q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, .Dedup q => q.WinsDerivable
  | _, _, _, .Diff q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, .Alt _ _ q => q.WinsDerivable
  | _, _, _, .Mu _ q₀ q₁ => q₀.WinsDerivable ∧ q₁.WinsDerivable
  | _, _, _, .MuSet _ q₀ q₁ => q₀.WinsDerivable ∧ q₁.WinsDerivable
  | _, _, _, .Gamma _ _ _ q _ _ => q.WinsDerivable
  | _, _, _, .GammaScalar _ _ q _ => q.WinsDerivable
  | _, _, _, .GammaNest _ _ _ _ q => q.WinsDerivable
  | _, _, _, .ProvSum _ _ _ q => q.WinsDerivable
  | _, _, _, .Retag _ q => q.WinsDerivable
  | _, _, _, .GammaTok _ _ _ _ _ q _ => q.WinsDerivable
  | c, _, _, @AggQueryIn.Win _ _ n _ _ κ' _ O _ w _ _ q _ dist keep =>
      (∀ i, κ' i = ColKind.reg) ∧ w.ContainsSelf ∧ dist = false
        ∧ keep = none
        ∧ (∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
            ∀ (y u : Tuple T n) (γ : Fin c → T),
              ψ.holdsPlain y (Fin.append u γ)
                ↔ w.ρ (Tuple.key O y) (Tuple.key O u) = true)
        ∧ q.WinsDerivable
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

omit [ValueType T] in
/-- A class other than `j` that `insert j S` holds is in `S`. -/
private theorem mem_of_mem_insert {S : Set OpKind} {k j : OpKind}
    (hk : k ≠ j) (h : k ∈ insert j S) : k ∈ S :=
  (Set.mem_insert_iff.mp h).resolve_left hk

/-! ## The first pass: the windows go -/

/-- **Every window is eliminable** (`prop:winderived`, recursively): a
query whose windows are derivable is equivalent to one with no window,
using the apply, the aggregation and the selection in their place. -/
theorem AggQueryIn.exists_winFree {S : Set OpKind} (ha : OpKind.apply ∈ S)
    (hg : OpKind.gamma ∈ S) (hs : OpKind.sel ∈ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly (insert OpKind.win S) → q.WinsDerivable →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ q
  induction q with
  | Rel n s => exact fun _ _ => ⟨AggQueryIn.Rel n s, trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun hq _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) hq, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq.2 hd
    refine ⟨AggQueryIn.Proj ps q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq.2 hd
    refine ⟨AggQueryIn.Sel φ q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hd
    obtain ⟨q₁', hu₁, he₁⟩ := ih₁ hq.2.1 hd.1
    obtain ⟨q₂', hu₂, he₂⟩ := ih₂ hq.2.2 hd.2
    refine ⟨AggQueryIn.Prod q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hd
    obtain ⟨q₁', hu₁, he₁⟩ := ih₁ hq.2.1 hd.1
    obtain ⟨q₂', hu₂, he₂⟩ := ih₂ hq.2.2 hd.2
    refine ⟨AggQueryIn.Apply q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.bind_congr (fun u _ =>
      congrArg (Multiset.map _) (he₂ D (Fin.append u γ)))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hd
    obtain ⟨q₁', hu₁, he₁⟩ := ih₁ hq.2.1 hd.1
    obtain ⟨q₂', hu₂, he₂⟩ := ih₂ hq.2.2 hd.2
    refine ⟨AggQueryIn.Sum q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq.2 hd
    refine ⟨AggQueryIn.Dedup q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hd
    obtain ⟨q₁', hu₁, he₁⟩ := ih₁ hq.2.1 hd.1
    obtain ⟨q₂', hu₂, he₂⟩ := ih₂ hq.2.2 hd.2
    refine ⟨AggQueryIn.Diff q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Alt i hi q ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq hd
    exact ⟨AggQueryIn.Alt i hi q', hu', fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq hd
    exact ⟨AggQueryIn.Retag hbase q', hu', fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq.2 hd
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq.2 hd
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc f q ih =>
    intro hq hd
    obtain ⟨q', hu', he'⟩ := ih hq.2 hd
    refine ⟨AggQueryIn.GammaNest is his pc f q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P' O o w t f q hrr dist keep ih =>
    intro hq hd
    obtain ⟨hreg, hcs, hdist, hkeep, ⟨ψ, hψ⟩, hd'⟩ := hd
    obtain ⟨q', hu', he'⟩ := ih hq.2 hd'
    subst hdist
    subst hkeep
    have hκ := funext hreg
    subst hκ
    refine ⟨winByApply P' O o ψ t f q',
      usesOnly_winByApply P' O o ψ t f ha hg hs hu', fun D γ => ?_⟩
    refine Eq.trans ?_
      (evaluatePlain_winByApply P' O o hcs ψ hψ t f q' D γ).symm
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
    rfl
  | WinExpr P' O o ws ts fs g q keeps ih => exact fun _ hd => hd.elim

/-! ## The third pass: duplicate elimination and the difference go -/

/-- **Duplicate elimination and the difference are eliminable**
(recursively): over a closed query using the basis classes and those
two, duplicate elimination becomes a grouping (`sec:basis`'s (a)) and
the difference becomes a count over the tagged union (its (b)), so the
query is equivalent to one over the basis alone.

The query is asked to be closed, which is where the two identities are
proved, and to use no apply – both of which the decorrelation's output
is. -/
theorem AggQueryIn.exists_basisOps_of_dedupDiff {S : Set OpKind}
    (hp : OpKind.proj ∈ S) (hs : OpKind.sel ∈ S) (hx : OpKind.prod ∈ S)
    (hu : OpKind.union ∈ S) (hg : OpKind.gamma ∈ S)
    (hap : OpKind.apply ∉ S) (a : T) (ha : a ≠ 0) (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ), c = 0 →
      q.usesOnly (insert OpKind.dedup (insert OpKind.diff S)) →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ q
  induction q with
  | Rel n s => exact fun _ _ => ⟨AggQueryIn.Rel n s, trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun _ hq => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) (mem_of_mem_insert (by decide) hq),
      fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    refine ⟨AggQueryIn.Proj ps q', ⟨hp, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    refine ⟨AggQueryIn.Sel φ q', ⟨hs, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hc hq
    obtain ⟨q₁', hu₁, he₁⟩ := ih₁ hc hq.2.1
    obtain ⟨q₂', hu₂, he₂⟩ := ih₂ hc hq.2.2
    refine ⟨AggQueryIn.Prod q₁' q₂', ⟨hx, hu₁, hu₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro _ hq
    exact absurd (mem_of_mem_insert (by decide)
      (mem_of_mem_insert (by decide) hq.1)) hap
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hc hq
    obtain ⟨q₁', hu₁, he₁⟩ := ih₁ hc hq.2.1
    obtain ⟨q₂', hu₂, he₂⟩ := ih₂ hc hq.2.2
    refine ⟨AggQueryIn.Sum q₁' q₂', ⟨hu, hu₁, hu₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    -- duplicate elimination is the grouping on every column
    refine ⟨(AggQueryIn.Gamma (fun k => k) (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0) q').castKind ?_, ?_, fun D γ => ?_⟩
    · funext j
      refine Fin.addCases (fun k => ?_) (fun z => z.elim0) j
      rw [Fin.append_left]
      rfl
    · rw [AggQueryIn.usesOnly_castKind]
      exact ⟨hg, hu'⟩
    · rw [AggQueryIn.evaluatePlain_castKind]
      refine Eq.trans ?_ (AggQueryIn.dedup_plainEquiv_gamma q' D γ)
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hc hq
    obtain ⟨q₁', hu₁, he₁⟩ := ih₁ hc hq.2.1
    obtain ⟨q₂', hu₂, he₂⟩ := ih₂ hc hq.2.2
    subst hc
    -- the difference is a count over the tagged union
    refine ⟨AggQueryIn.notInDiff a f q₁' q₂',
      AggQueryIn.usesOnly_notInDiff a f hp hs hx hu hg hu₁ hu₂,
      fun D γ => ?_⟩
    refine Eq.trans ?_ (AggQueryIn.diff_plainEquiv_notIn a ha f hzero q₁' q₂'
      D γ)
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Alt i hi q ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq
    exact ⟨AggQueryIn.Alt i hi q', hu', fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq
    exact ⟨AggQueryIn.Retag hbase q', hu', fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun _ hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun _ hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord, ⟨hg, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord, ⟨hg, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    refine ⟨AggQueryIn.GammaNest is his pc fn q', ⟨hg, hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs b q keep ih => exact fun _ hq => hq.elim
  | ProvSum is his t q ih => exact fun _ hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    refine ⟨AggQueryIn.Win P' O o w t fn q' hrr dist keep,
      ⟨mem_of_mem_insert (by decide)
        (mem_of_mem_insert (by decide) hq.1), hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hc hq
    obtain ⟨q', hu', he'⟩ := ih hc hq.2
    refine ⟨AggQueryIn.WinExpr P' O o ws ts fs g q' keeps,
      ⟨mem_of_mem_insert (by decide)
        (mem_of_mem_insert (by decide) hq.1), hu'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]

/-! ## The three passes composed -/

/-- The classes the middle of the construction works in: the basis, with
duplicate elimination and the difference, which the decorrelation leaves
behind and the third pass removes. -/
def basisDD : Set OpKind := insert OpKind.dedup (insert OpKind.diff basisOps)

/-- **The scope of the classification**: the basis, duplicate
elimination, the difference, the apply and the window. The four
operators `usesOnly` reads as `False` – the two recursions, the
token-building grouping and the provenance sum – are outside it, as is
the multi-frame window, which `AggQueryIn.WinsDerivable` excludes. -/
def plainOps : Set OpKind := insert OpKind.win (insert OpKind.apply basisDD)

/-- **The generation half of `thm:plainbasis`**: every query of the
plain fragment is equivalent to one using only the six basis classes
`∅`, `Π`, `σ`, `×`, `⊎`, `γ`.

The three hypotheses are what the identities ask for: a value `a ≠ 0` to
tag the two sides of a difference with, an aggregate `f` reading `𝟘`
exactly on a sequence of zeros (`count` of the non-null tags, or their
sum where the domain has no zero divisors), and that every window be
derivable – its frame containing its current row, its input all-regular,
its frame condition a predicate. -/
theorem AggQueryIn.exists_basisOps_plainEquiv {n : ℕ} {κ : Fin n → ColKind}
    (a : T) (ha : a ≠ 0) (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps) (hd : q.WinsDerivable) :
    ∃ q' : AggQuery T n κ, q'.usesOnly basisOps ∧ q.PlainEquiv q' := by
  -- the windows go
  obtain ⟨q₁, hu₁, he₁⟩ :=
    AggQueryIn.exists_winFree (S := insert OpKind.apply basisDD)
      (by simp [basisDD, basisOps]) (by simp [basisDD, basisOps])
      (by simp [basisDD, basisOps]) q hq hd
  -- the applies go, by the decorrelation
  obtain ⟨q₂, hu₂, he₂⟩ :=
    AggQueryIn.exists_applyFree_plainEquiv (S := basisDD)
      (by intro k hk; simp [decorrOps] at hk; rcases hk with h|h|h|h|h|h|h <;>
        simp [basisDD, basisOps, h])
      (by simp [basisDD, basisOps]) q₁ hu₁
  -- and duplicate elimination and the difference go with them
  obtain ⟨q₃, hu₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_of_dedupDiff (S := basisOps)
      (by simp [basisOps]) (by simp [basisOps]) (by simp [basisOps])
      (by simp [basisOps]) (by simp [basisOps]) (by simp [basisOps])
      a ha f hzero q₂ rfl hu₂
  exact ⟨q₃, hu₃, fun D γ => (he₁ D γ).trans ((he₂ D γ).trans (he₃ D γ))⟩

/-! ## What every generating set must contain

The other half of `thm:plainbasis`. Each of the six invariants of
`Provenance.PlainBasis` holds of every query that avoids one class, and
each has a witness query that breaks it; a generating set that omitted
the class would have to express the witness by a query that cannot. -/

/-- **A query with no window has every window derivable**, there being
none: the condition is on the windows, so it is vacuous. -/
theorem AggQueryIn.winsDerivable_of_usesOnly {S : Set OpKind}
    (hw : OpKind.win ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly S → q.WinsDerivable := by
  intro c n κ q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun hq => ih hq.2
  | Sel φ q ih => exact fun hq => ih hq.2
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Dedup q ih => exact fun hq => ih hq.2
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Alt i hi q ih => exact fun hq => ih hq
  | Retag hbase q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | Gamma is ts fs q keep ord ih => exact fun hq => ih hq.2
  | GammaScalar ts fs q ord ih => exact fun hq => ih hq.2
  | GammaNest is his pc fn q ih => exact fun hq => ih hq.2
  | GammaTok is his ts fs b q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih => exact fun hq => absurd hq.1 hw
  | WinExpr P' O o ws ts fs g q keeps ih => exact fun hq => absurd hq.1 hw

/-- **A generating set**: every query of the plain fragment whose
windows are derivable is equivalent to one using only its classes. -/
def Generates (T : Type) [ValueType T] (S : Set OpKind) : Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ),
    q.usesOnly plainOps → q.WinsDerivable →
      ∃ q' : AggQuery T n κ, q'.usesOnly S ∧ q.PlainEquiv q'

/-- **The six classes generate**, over a domain with a non-zero value
and an aggregate that reads `𝟘` exactly on the zeros – over `ℕ` the
value `1` and the sum. -/
theorem basisOps_generates (a : T) (ha : a ≠ 0) (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) :
    Generates T basisOps :=
  fun q hq hd => AggQueryIn.exists_basisOps_plainEquiv a ha f hzero q hq hd

/-- Over `ℕ`: the tag is `1` and the aggregate is the sum. -/
theorem basisOps_generates_nat : Generates ℕ basisOps :=
  basisOps_generates 1 one_ne_zero List.sum (fun _ => List.sum_eq_zero_iff)

/-- Transporting along an equality of kind vectors changes no window. -/
@[simp] theorem AggQueryIn.winsDerivable_castKind {c n : ℕ}
    {κ κ' : Fin n → ColKind} (h : κ = κ') (q : AggQueryIn T c n κ) :
    (q.castKind h).WinsDerivable ↔ q.WinsDerivable := by
  cases h
  exact Iff.rfl

omit [ValueType T] in
/-- The empty instance is thin: it binds no name at all. -/
theorem Database.thin_nil : Database.Thin ([] : Database T) := by
  intro k s r h
  have hnone : (none : Option (Relation T k)) = some r := h
  exact (Option.some_ne_none r hnone.symm).elim

omit [ValueType T] in
/-- The unit uses the aggregation and the empty relation. -/
private theorem usesOnly_unit {S : Set OpKind} (hg : OpKind.gamma ∈ S)
    (he : OpKind.empty ∈ S) :
    (AggQueryIn.unit : AggQuery T 0 (ColKind.allReg 0)).usesOnly S := by
  unfold AggQueryIn.unit
  rw [AggQueryIn.usesOnly_castKind]
  exact ⟨hg, he⟩

omit [ValueType T] in
/-- And a constant row projects it. -/
private theorem usesOnly_rowOf {S : Set OpKind} {k : ℕ}
    (hp : OpKind.proj ∈ S) (hg : OpKind.gamma ∈ S) (he : OpKind.empty ∈ S)
    (u : Tuple T k) : (AggQueryIn.rowOf u).usesOnly S := by
  unfold AggQueryIn.rowOf
  rw [AggQueryIn.usesOnly_castKind]
  exact ⟨hp, usesOnly_unit hg he⟩

/-- The unit has no window. -/
private theorem winsDerivable_unit :
    (AggQueryIn.unit : AggQuery T 0 (ColKind.allReg 0)).WinsDerivable := by
  rw [AggQueryIn.unit, AggQueryIn.winsDerivable_castKind]
  exact trivial

/-- Nor does a constant row. -/
private theorem winsDerivable_rowOf {k : ℕ} (u : Tuple T k) :
    (AggQueryIn.rowOf u).WinsDerivable := by
  rw [AggQueryIn.rowOf, AggQueryIn.winsDerivable_castKind]
  exact winsDerivable_unit

/-- **`⊎` is necessary**: without it a thin instance has an answer of at
most one row, and two copies of one row are two. -/
theorem union_mem_of_generates {S : Set OpKind} (hS : Generates T S) :
    OpKind.union ∈ S := by
  by_contra hu
  set u : Tuple T 0 := fun j => j.elim0 with hu0
  obtain ⟨q', hu', he⟩ := hS (AggQueryIn.values [u, u] (by simp))
    (show (AggQueryIn.Sum (AggQueryIn.rowOf u) (AggQueryIn.rowOf u)).usesOnly
        plainOps from
      ⟨by simp [plainOps, basisDD, basisOps],
        usesOnly_rowOf (by simp [plainOps, basisDD, basisOps])
          (by simp [plainOps, basisDD, basisOps])
          (by simp [plainOps, basisDD, basisOps]) u,
        usesOnly_rowOf (by simp [plainOps, basisDD, basisOps])
          (by simp [plainOps, basisDD, basisOps])
          (by simp [plainOps, basisDD, basisOps]) u⟩)
    (show (AggQueryIn.Sum (AggQueryIn.rowOf u)
        (AggQueryIn.rowOf u)).WinsDerivable from
      ⟨winsDerivable_rowOf u, winsDerivable_rowOf u⟩)
  have h2 := AggQueryIn.card_values_two u ([] : Database T) (fun j => j.elim0)
  rw [he ([] : Database T) (fun j => j.elim0)] at h2
  have h1 := AggQueryIn.card_le_one_of_thin hu q' hu' ([] : Database T)
    Database.thin_nil (fun j => j.elim0)
  omega

/-- **`γ` is necessary**: without it the all-empty instance has an empty
answer, and the unit has a row there. -/
theorem gamma_mem_of_generates {S : Set OpKind} (hS : Generates T S) :
    OpKind.gamma ∈ S := by
  by_contra hg
  obtain ⟨q', hu', he⟩ := hS (AggQueryIn.unit : AggQuery T 0 _)
    (usesOnly_unit (by simp [plainOps, basisDD, basisOps])
      (by simp [plainOps, basisDD, basisOps]))
    winsDerivable_unit
  refine AggQueryIn.evaluatePlain_unit_ne_zero ([] : Database T)
    (fun j => j.elim0) (Eq.trans (he ([] : Database T) (fun j => j.elim0)) ?_)
  exact AggQueryIn.evaluatePlain_eq_zero_of_allEmpty hg q' hu'
    ([] : Database T) Database.allEmpty_nil (fun j => j.elim0)

/-- **`Π` is necessary**: without it a query's multiplicities are
bounded by the query, and a projection of a relation with a repeated
column has unbounded ones. -/
theorem proj_mem_of_generates {S : Set OpKind} (hS : Generates ℕ S) :
    OpKind.proj ∈ S := by
  by_contra hp
  obtain ⟨q', hu', he⟩ := hS projWitness ⟨by simp [plainOps, basisDD, basisOps],
    trivial⟩ trivial
  refine projWitness_unbounded_multiplicity ⟨q'.multBound, fun D hnd u => ?_⟩
  rw [he D (fun j => j.elim0)]
  exact AggQueryIn.count_le_multBound hp q' hu' D hnd (fun j => j.elim0) u

/-- **One of `×` and the apply is necessary**: without both, an answer
is linear in the instance, and a relation joined with itself is
quadratic. -/
theorem prod_or_apply_mem_of_generates {S : Set OpKind} (hS : Generates ℕ S) :
    OpKind.prod ∈ S ∨ OpKind.apply ∈ S := by
  by_contra h
  obtain ⟨hp, ha⟩ := not_or.mp h
  obtain ⟨q', hu', he⟩ := hS prodWitness
    ⟨by simp [plainOps, basisDD, basisOps], trivial, trivial⟩ ⟨trivial, trivial⟩
  refine prodWitness_no_linear_bound ⟨q'.sizeBound, fun D => ?_⟩
  rw [he D (fun j => j.elim0)]
  exact AggQueryIn.card_le_sizeBound hp ha q' hu' D (fun j => j.elim0)

/-- **What a generating set must contain**, from the four invariants
whose statement is about the semantics alone: the projection, the union,
the aggregation, and one of the product and the apply.

The `∅` and `σ`/`−` rows of `tab:basisclasses` are not here, and the
reason is not that their invariants are missing – they are
`AggQueryIn.usesEmpty_of_overSchema_empty` and
`AggQueryIn.zero_or_ne_zero_of_noSelDiff`, with their witnesses – but
that both are *schema-relative*: they ask the query to be over the
schema (`AggQueryIn.overSchema`), since a query naming a relation the
instance does not hold is empty on every instance. Using them asks the
generation theorem to produce a query over the same schema, which is
`AggQueryIn.PlainEquivOn`, and that means carrying `overSchema` through
the three passes and the decorrelation. -/
theorem generates_necessary {S : Set OpKind} (hS : Generates ℕ S) :
    OpKind.proj ∈ S ∧ OpKind.union ∈ S ∧ OpKind.gamma ∈ S
      ∧ (OpKind.prod ∈ S ∨ OpKind.apply ∈ S) :=
  ⟨proj_mem_of_generates hS, union_mem_of_generates hS,
    gamma_mem_of_generates hS, prod_or_apply_mem_of_generates hS⟩
