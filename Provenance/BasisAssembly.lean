/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AllRegular
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
and `GeneratesOn` reads it as a property of a set of classes
(`basisOps_generatesOn`). Each pass also carries `overSchema`: the query
it produces names the relations the query it is given names, which is
what the other half needs.

That other half is six lemmas, one per row of `tab:basisclasses`:
`proj_mem_of_generatesOn`, `union_mem_of_generatesOn`,
`gamma_mem_of_generatesOn`, `prod_or_apply_mem_of_generatesOn`,
`empty_mem_of_generatesOn` and `sel_or_diff_mem_of_generatesOn`. They
are separate statements rather than one conjunction because each names
the schema its witness lives over, and the `∅` row lives over the
*empty* schema – no single schema serves them all.

The two **swaps** of `thm:plainbasis` – `−` for `σ`, the apply for `×` –
are the last two theorems here, `AggQueryIn.exists_selFree` and
`AggQueryIn.exists_prodFree`. Each is a pass applying the identity
everywhere, and what they ask of a query is `AggQueryIn.SwapReady`: a
selection's input and a product's left factor must have regular
columns, since the difference and an apply's left side take those.
`AggQueryIn.exists_allReg` of `Provenance.AllRegular` is what puts a
query in that shape, reading every column as a value – which over a
plain relation changes nothing.

**The three alternative bases are stated and proved**:
`AggQueryIn.exists_basisDiffOps_plainEquiv` over `{∅, Π, ×, ⊎, γ, −}`,
`AggQueryIn.exists_basisApplyOps_plainEquiv` over
`{∅, Π, σ, apply, ⊎, γ}` and `exists_basisApplyDiffOps_plainEquiv` over
`{∅, Π, apply, ⊎, γ, −}`, with `basisDiffOps_generatesOn`,
`basisApplyOps_generatesOn` and `basisApplyDiffOps_generatesOn` their
`GeneratesOn` forms. Each is the three passes, then the re-typing, then
the swap or swaps.

They ask nothing of their input beyond what the six-class statement
asks. That the columns re-type is part of `AggQueryIn.usesOnly`: a
projection column reading an aggregate column through an arbitrary
function belongs to the rewritten world, not to the source language,
which reads it through a *term* (`ProjColIn.aggTermOf`), and `usesOnly`
refuses the former as it refuses `GammaTok` and `ProvSum`. What is left
of `AggQueryIn.Retypable` is the window's own condition, and that is
vacuous here: the first pass replaces every window by an apply of a
scalar aggregation (`AggQueryIn.retypable_of_usesOnly`).
-/

variable {T : Type} [ValueType T]

/-! ## What a window has to be for `prop:winderived` to reach it -/

/-- **Every window of the query is derivable.** Two things at each
window: its input's columns are all regular (an apply reads its left side
as a relation of values), and its frame contains its current row –
`EXCLUDE CURRENT ROW` and `EXCLUDE TIES` have no reading as an
aggregation, a group being determined by its rows and not by the
occurrence, which is the restriction `prop:winderived` itself carries.

Nothing is asked about the frame *condition* any more: a frame names a
`FrameCond`, so the selection that spells it out is read off it
(`ValueFrame.exists_framePred`), for every frame of the syntax, every
`FILTER` clause and every domain. `DISTINCT` and a clause are covered
too: the derived form aggregates `f^distinct` where the window does, and
the clause enters that selection (`evaluatePlain_winByApplyOf`).

What stays out is a *multi-frame* window, and not for want of proving:
its column combines the leaves' values by a function no term expresses,
so the predicate reads `False` there, as it does for
`ProjColIn.aggTerm` elsewhere. -/
def AggQueryIn.WinsDerivable : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.WinsDerivable
  | _, _, _, _, .Sel _ q _ => q.WinsDerivable
  | _, _, _, _, .Prod q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, _, .Apply q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, _, .Sum q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, _, .Dedup q => q.WinsDerivable
  | _, _, _, _, .Diff q₁ q₂ => q₁.WinsDerivable ∧ q₂.WinsDerivable
  | _, _, _, _, .Explode _ _ q => q.WinsDerivable
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.WinsDerivable ∧ q₁.WinsDerivable
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.WinsDerivable ∧ q₁.WinsDerivable
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.WinsDerivable
  | _, _, _, _, .GammaScalar _ _ q _ => q.WinsDerivable
  | _, _, _, _, .GammaNest _ _ _ _ q => q.WinsDerivable
  | _, _, _, _, .ProvSum _ _ _ q => q.WinsDerivable
  | _, _, _, _, .Retag _ q => q.WinsDerivable
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.WinsDerivable
  | _, _, _, _, @AggQueryIn.Win _ _ _ _ _ κ' _ _ _ w _ _ q _ _ _ =>
      (∀ i, κ' i = ColKind.reg) ∧ w.ContainsSelf ∧ q.WinsDerivable
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

omit [ValueType T] in
/-- A class other than `j` that `insert j S` holds is in `S`. -/
private theorem mem_of_mem_insert {S : Set OpKind} {k j : OpKind}
    (hk : k ≠ j) (h : k ∈ insert j S) : k ∈ S :=
  (Set.mem_insert_iff.mp h).resolve_left hk

omit [ValueType T] in
/-- And a class outside `S` and other than `j` is outside `insert j S`. -/
private theorem not_mem_insert_of_ne {S : Set OpKind} {k j : OpKind}
    (hkj : k ≠ j) (hk : k ∉ S) : k ∉ insert j S :=
  fun hc => hk (mem_of_mem_insert hkj hc)

/-! ## The first pass: the windows go -/

/-- **Every window is eliminable** (`prop:winderived`, recursively): a
query whose windows are derivable is equivalent to one with no window,
using the apply, the aggregation and the selection in their place. -/
theorem AggQueryIn.exists_winFree {S : Set OpKind} {sch : Schema}
    (ha : OpKind.apply ∈ S) (hg : OpKind.gamma ∈ S) (hs : OpKind.sel ∈ S)
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly (insert OpKind.win S) → q.WinsDerivable →
      q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ l, q'.usesOnly S ∧ q'.overSchema sch
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    exact fun _ _ hqs =>
      ⟨AggQueryIn.Rel n s, trivial, hqs, fun _ _ => rfl⟩
  | Hole n s =>
    exact fun _ _ hqs =>
      ⟨AggQueryIn.Hole n s _, trivial, hqs, fun _ _ => rfl⟩
  | Param pv ρ =>
    exact fun hq _ _ => ⟨AggQueryIn.Param pv ρ,
      ⟨mem_of_mem_insert (by decide) hq.1, mem_of_mem_insert (by decide) hq.2.1, mem_of_mem_insert
          (by decide) hq.2.2⟩, trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun hq _ _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) hq, trivial, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Proj ps q',
      ⟨⟨mem_of_mem_insert (by decide) hq.1.1, hq.1.2⟩, hu'⟩, hs',
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q hφ ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Sel φ q' hφ,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Prod q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,       fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Apply q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,       fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.bind_congr (fun u _ =>
      congrArg (Multiset.map _) (he₂ D (Fin.append u γ)))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,       fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Dedup q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Diff q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,       fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Explode i hi q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq hd hqs
    exact ⟨AggQueryIn.Explode i hi q', hu', hs',       fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq hd hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs',       fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
      exact fun hq => absurd hq.1 (not_mem_insert_of_ne (by decide) hmb)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
      exact fun hq => absurd hq.1 (not_mem_insert_of_ne (by decide) hms)
  | Gamma is ts fs q keep ord ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc f q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.GammaNest is his pc f q',
      ⟨⟨mem_of_mem_insert (by decide) hq.1.1, hq.1.2⟩, hu'⟩, hs',
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | @Win cw nw _mw _pw _κw P' O o w t f q hrr dist keep ih =>
    intro hq hd hqs
    obtain ⟨hreg, hcs, hd'⟩ := hd
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hd' hqs
    have hκ := funext hreg
    subst hκ
    -- the frame is a condition on the order values, so the selection that
    -- spells it out is read off it
    obtain ⟨ψ, -, hψ⟩ :=
      ValueFrame.exists_framePred (T := T) (n := nw) (c := cw) O w keep
    refine ⟨winByApply P' O o ψ t (if dist then f.distinct else f) q',
      usesOnly_winByApply P' O o ψ t _ ha hg hs hu',
      overSchema_winByApply P' O o ψ t _ hs',
            fun D γ => ?_⟩
    refine Eq.trans ?_
      (evaluatePlain_winByApplyOf P' O o hcs ψ t f dist keep hψ q' D γ).symm
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
    {sch : Schema} (hp : OpKind.proj ∈ S) (hs : OpKind.sel ∈ S)
    (hx : OpKind.prod ∈ S) (hu : OpKind.union ∈ S) (hg : OpKind.gamma ∈ S)
    (hap : OpKind.apply ∉ S) (hmb : OpKind.muBag ∉ S)
    (hms : OpKind.muSet ∉ S) (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l), c = 0 →
      q.usesOnly (insert OpKind.dedup (insert OpKind.diff S)) →
      q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ l, q'.usesOnly S ∧ q'.overSchema sch
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    exact fun _ _ hqs =>
      ⟨AggQueryIn.Rel n s, trivial, hqs, fun _ _ => rfl⟩
  | Hole n s =>
    exact fun _ _ hqs =>
      ⟨AggQueryIn.Hole n s _, trivial, hqs, fun _ _ => rfl⟩
  | Param pv ρ =>
    exact fun _ hq _ => ⟨AggQueryIn.Param pv ρ,
      ⟨mem_of_mem_insert (by decide) (mem_of_mem_insert (by decide) hq.1), mem_of_mem_insert
          (by decide) (mem_of_mem_insert (by decide) hq.2.1),
        mem_of_mem_insert (by decide) (mem_of_mem_insert (by decide) hq.2.2)⟩, trivial,
            fun _ _ => rfl⟩
  | Empty =>
    exact fun _ hq _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) (mem_of_mem_insert (by decide) hq),
      trivial, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Proj ps q', ⟨⟨hp, hq.1.2⟩, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q hφ ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Sel φ q' hφ, ⟨hs, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hc hq hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hc hq.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hc hq.2.2 hqs.2
    refine ⟨AggQueryIn.Prod q₁' q₂', ⟨hx, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro _ hq
    exact absurd (mem_of_mem_insert (by decide)
      (mem_of_mem_insert (by decide) hq.1)) hap
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hc hq hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hc hq.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hc hq.2.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂', ⟨hu, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    -- duplicate elimination is the grouping on every column
    refine ⟨(AggQueryIn.Gamma (fun k => k) (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0) q').castKind ?_, ?_, ?_,
      fun D γ => ?_⟩
    · funext j
      refine Fin.addCases (fun k => ?_) (fun z => z.elim0) j
      rw [Fin.append_left]
      rfl
    · rw [AggQueryIn.usesOnly_castKind]
      exact ⟨hg, hu'⟩
    · rw [AggQueryIn.overSchema_castKind]
      exact hs'
    · rw [AggQueryIn.evaluatePlain_castKind]
      refine Eq.trans ?_ (AggQueryIn.dedup_plainEquiv_gamma q' D γ)
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hc hq hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hc hq.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hc hq.2.2 hqs.2
    subst hc
    -- the difference is a count over the tagged union
    refine ⟨AggQueryIn.notInDiff cnt q₁' q₂',
      AggQueryIn.usesOnly_notInDiff cnt hp hs hx hu hg hu₁ hu₂,
      AggQueryIn.overSchema_notInDiff cnt hs₁ hs₂,
      fun D γ => ?_⟩
    refine Eq.trans ?_
      (AggQueryIn.diff_plainEquiv_notIn cnt hcnt q₁' q₂' D γ)
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Explode i hi q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq hqs
    exact ⟨AggQueryIn.Explode i hi q', hu', hs',       fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs',       fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
      exact fun _ hq => absurd hq.1 (not_mem_insert_of_ne (by decide)
        (not_mem_insert_of_ne (by decide) hmb))
  | MuSet s q₀ q₁ ih₀ ih₁ =>
      exact fun _ hq => absurd hq.1 (not_mem_insert_of_ne (by decide)
        (not_mem_insert_of_ne (by decide) hms))
  | Gamma is ts fs q keep ord ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord, ⟨hg, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord, ⟨hg, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.GammaNest is his pc fn q', ⟨⟨hg, hq.1.2⟩, hu'⟩, hs',
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs b q keep ih => exact fun _ hq => hq.elim
  | ProvSum is his t q ih => exact fun _ hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Win P' O o w t fn q' hrr dist keep,
      ⟨mem_of_mem_insert (by decide)
        (mem_of_mem_insert (by decide) hq.1), hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.WinExpr P' O o ws ts fs g q' keeps,
      ⟨mem_of_mem_insert (by decide)
        (mem_of_mem_insert (by decide) hq.1), hu'⟩, hs', fun D γ => ?_⟩
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

/-- **The generation half of `thm:plainbasis`**: every query of the plain
fragment is equivalent to one using only the six basis classes `∅`, `Π`,
`σ`, `×`, `⊎`, `γ`, over the same schema.

The three hypotheses are what the identities ask for: an aggregate that
counts (SQL's `count(e)`, which `sec:basis` assumes among the
aggregates), that the query use only the classes in scope, and that
every window be derivable. -/
theorem AggQueryIn.exists_basisOps_plainEquiv {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps) (hd : q.WinsDerivable)
    (hqs : q.overSchema sch) :
    ∃ q' : AggQuery T n κ,
      q'.usesOnly basisOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  -- the windows go
  obtain ⟨q₁, hu₁, hs₁, he₁⟩ :=
    AggQueryIn.exists_winFree (S := insert OpKind.apply basisDD)
      (by simp [basisDD, basisOps]) (by simp [basisDD, basisOps])
      (by simp [basisDD, basisOps]) (by simp [basisDD, basisOps])
      (by simp [basisDD, basisOps]) q hq hd hqs
  -- the applies go, by the decorrelation
  obtain ⟨q₂, hu₂, hs₂, he₂⟩ :=
    AggQueryIn.exists_applyFree_plainEquiv (S := basisDD)
      (by intro k hk; simp [decorrOps] at hk; rcases hk with h|h|h|h|h|h|h <;>
        simp [basisDD, basisOps, h])
      (by simp [basisDD, basisOps]) (by simp [basisDD, basisOps])
      (by simp [basisDD, basisOps]) q₁ hu₁ hs₁
  -- and duplicate elimination and the difference go with them
  obtain ⟨q₃, hu₃, hs₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_of_dedupDiff (S := basisOps)
      (by simp [basisOps]) (by simp [basisOps]) (by simp [basisOps])
      (by simp [basisOps]) (by simp [basisOps]) (by simp [basisOps])
      (by simp [basisOps]) (by simp [basisOps])
      cnt hcnt q₂ rfl hu₂ hs₂
  exact ⟨q₃, hu₃, hs₃,
    fun D γ => (he₁ D γ).trans ((he₂ D γ).trans (he₃ D γ))⟩

/-- **`COUNT(*)` over `ℕ` is a count.** Nothing there is null, so the
length of a sequence is `0` exactly when the sequence has no value to
count. -/
theorem counts_count_nat : SeqAggFunc.Counts (SeqAggFunc.count) :=
  SeqAggFunc.counts_of_noNulls (fun _ => rfl)
    (fun _ => List.length_eq_zero_iff)

/-! ## The basis with the window kept

`win` is a class of the basis (the classification's own `win` row), so the
statement a *source* query is read by keeps its windows and runs only two
passes: the applies go by the decorrelation, and the duplicate
elimination and the difference it builds go with them. Nothing is asked
of a window here – not that its frame contain its current row, not that
it be single-frame, not that its input's columns be regular – because
nothing has to rewrite one: the decorrelation carries a window of *every*
frame (`ValueFrame.frameOf_slices`: the row a frame takes out is the same
row on both sides), and the third pass keeps it.

`AggQueryIn.exists_basisOps_plainEquiv` is the strictly stronger claim –
the window class is not needed *for the windows `prop:winderived`
reaches* – and that is where `AggQueryIn.WinsDerivable` is asked. -/

/-- The basis with the window: the six classes and `win`. -/
def basisWinOps : Set OpKind := insert OpKind.win basisOps

/-- **Every query of the plain fragment is equivalent to one over the
basis and the window**, over the same schema and with the same columns.
This is `thm:plainbasis` for the basis that holds `win`, and it carries
no hypothesis about windows at all. -/
theorem AggQueryIn.exists_basisWinOps_plainEquiv {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt) (q : AggQuery T n κ)
    (hq : q.usesOnly plainOps) (hqs : q.overSchema sch) :
    ∃ q' : AggQuery T n κ,
      q'.usesOnly basisWinOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  -- the applies go, by the decorrelation, the windows riding along
  obtain ⟨q₂, hu₂, hs₂, he₂⟩ :=
    AggQueryIn.exists_applyFree_plainEquiv (S := insert OpKind.win basisDD)
      (by intro k hk; simp [decorrOps] at hk; rcases hk with h|h|h|h|h|h|h <;>
        simp [basisDD, basisOps, h])
      (by simp [basisDD, basisOps]) (by simp [basisDD, basisOps])
      (by simp [basisDD, basisOps]) q
      (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [plainOps, basisDD, basisOps, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hk ⊢
        tauto) q hq)
      hqs
  -- and duplicate elimination and the difference go with them
  obtain ⟨q₃, hu₃, hs₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_of_dedupDiff (S := basisWinOps)
      (by simp [basisWinOps, basisOps]) (by simp [basisWinOps, basisOps])
      (by simp [basisWinOps, basisOps]) (by simp [basisWinOps, basisOps])
      (by simp [basisWinOps, basisOps]) (by simp [basisWinOps, basisOps])
      (by simp [basisWinOps, basisOps]) (by simp [basisWinOps, basisOps])
      cnt hcnt q₂ rfl
      (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisWinOps, basisDD, basisOps, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hk ⊢
        tauto) q₂ hu₂) hs₂
  exact ⟨q₃, hu₃, hs₃, fun D γ => (he₂ D γ).trans (he₃ D γ)⟩

/-- Over `ℕ`, with `COUNT(*)` as the aggregate. -/
theorem AggQueryIn.exists_basisWinOps_plainEquiv_nat {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (q : AggQuery ℕ n κ) (hq : q.usesOnly plainOps)
    (hqs : q.overSchema sch) :
    ∃ q' : AggQuery ℕ n κ,
      q'.usesOnly basisWinOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' :=
  AggQueryIn.exists_basisWinOps_plainEquiv SeqAggFunc.count counts_count_nat
    q hq hqs

/-- **A generating set over a schema**: every query over `sch` whose
windows are derivable, and which applies no function to an aggregate
column, is equivalent to one over `sch` using only the classes of `S`.
This is the form the classification needs for the `∅` and `σ`/`−` rows;
the three passes give the equivalence on *every* instance, which is
stronger than `AggQueryIn.PlainEquivOn` asks. The query produced has
regular columns throughout, which is what the swaps need and what the
plain semantics has anyway. It is also asked to be **defined everywhere**
(`AggQueryIn.SettlesAt`), as the query it stands for is: a set of
classes holding a recursion could otherwise stand in for a total query
with one whose rounds never settle, and whose value is then nothing the
semantics says. -/
def GeneratesOn (T : Type) [ValueType T] (sch : Schema) (S : Set OpKind) :
    Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ),
    q.overSchema sch → q.usesOnly plainOps → q.WinsDerivable →
      ∃ q' : AggQuery T n (ColKind.allReg n),
        q'.overSchema sch ∧ q'.usesOnly S
          ∧ (∀ (D : Database T) (γ : Fin 0 → T), q'.SettlesAt D γ)
          ∧ q.PlainEquiv q'

/-- The schema of the binary relation the projection witness reads. -/
def schemaS : Schema := Schema.ofFn (fun s => if s = "S" then some 2 else none) {"S"}
  (fun s hs => Finset.mem_singleton.mpr (by by_contra hne; exact hs (ite_eq_right hne)))

/-- **The six classes generate, over a schema**: `GeneratesOn`'s form of
the theorem above, which is what the classification's other half is
stated against. -/
theorem basisOps_generatesOn (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt) (sch : Schema) :
    GeneratesOn T sch basisOps :=
  fun q hqs hq hd => by
    obtain ⟨q₃, hu₃, hs₃, he₃⟩ :=
      AggQueryIn.exists_basisOps_plainEquiv cnt hcnt q hq hd hqs
    obtain ⟨q', hu', hs', -, he'⟩ :=
      AggQueryIn.exists_allReg (S := basisOps) (sch := sch)
        (by simp [basisOps]) (by simp [basisOps]) q₃ hu₃
        (AggQueryIn.retypable_of_usesOnly (by simp [basisOps]) q₃ hu₃) hs₃
    exact ⟨q', hs', hu',
      AggQueryIn.settlesAt_of_usesOnly (by simp [basisOps])
        (by simp [basisOps]) q' hu',
      fun D γ => (he₃ D γ).trans (he' D γ)⟩

/-- Over `ℕ`, with `COUNT(*)` as the aggregate. -/
theorem basisOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisOps :=
  basisOps_generatesOn SeqAggFunc.count counts_count_nat sch

/-! ## What every generating set must contain

The other half of `thm:plainbasis`. Each of the six invariants of
`Provenance.PlainBasis` holds of every query that avoids one class, and
each has a witness query that breaks it; a generating set that omitted
the class would have to express the witness by a query that cannot. -/

/-- **A query with no window has every window derivable**, there being
none: the condition is on the windows, so it is vacuous. -/
theorem AggQueryIn.winsDerivable_of_usesOnly {S : Set OpKind}
    (hw : OpKind.win ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.WinsDerivable := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Param pv ρ => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun hq => ih hq.2
  | Sel φ q _ ih => exact fun hq => ih hq.2
  | Prod q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Dedup q ih => exact fun hq => ih hq.2
  | Diff q₁ q₂ ih₁ ih₂ => exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Explode i hi q ih => exact fun hq => ih hq
  | Retag hbase q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.2.1, ih₁ hq.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.2.1, ih₁ hq.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun hq => ih hq.2
  | GammaScalar ts fs q ord ih => exact fun hq => ih hq.2
  | GammaNest is his pc fn q ih => exact fun hq => ih hq.2
  | GammaTok is his ts fs b q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih => exact fun hq => absurd hq.1 hw
  | WinExpr P' O o ws ts fs g q keeps ih => exact fun hq => absurd hq.1 hw

/-- Transporting along an equality of kind vectors changes no window. -/
@[simp] theorem AggQueryIn.winsDerivable_castKind {c n : ℕ}
    {κ κ' : Fin n → ColKind} {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
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
  exact ⟨⟨hp, fun _ => rfl⟩, usesOnly_unit hg he⟩

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
theorem union_mem_of_generatesOn {S : Set OpKind} {sch : Schema}
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S)
    (hS : GeneratesOn T sch S) : OpKind.union ∈ S := by
  by_contra hu
  set u : Tuple T 0 := fun j => j.elim0 with hu0
  obtain ⟨q', -, hu', -, he⟩ := hS (AggQueryIn.values [u, u] (by simp))
    (show (AggQueryIn.Sum (AggQueryIn.rowOf u)
        (AggQueryIn.rowOf u)).overSchema sch from
      ⟨by rw [AggQueryIn.rowOf, AggQueryIn.overSchema_castKind]
          exact AggQueryIn.overSchema_unit,
        by rw [AggQueryIn.rowOf, AggQueryIn.overSchema_castKind]
           exact AggQueryIn.overSchema_unit⟩)
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
  have h1 := AggQueryIn.card_le_one_of_thin hu hmb hms q' hu'
    ([] : Database T)
    Database.thin_nil (fun j => j.elim0)
  omega

/-- **`γ` is necessary**: without it the all-empty instance has an empty
answer, and the unit has a row there. -/
theorem gamma_mem_of_generatesOn {S : Set OpKind} {sch : Schema}
    (hS : GeneratesOn T sch S) : OpKind.gamma ∈ S := by
  by_contra hg
  obtain ⟨q', -, hu', -, he⟩ := hS (AggQueryIn.unit : AggQuery T 0 _)
    AggQueryIn.overSchema_unit
    (usesOnly_unit (by simp [plainOps, basisDD, basisOps])
      (by simp [plainOps, basisDD, basisOps]))
    winsDerivable_unit
  refine AggQueryIn.evaluatePlain_unit_ne_zero ([] : Database T)
    (fun j => j.elim0) (Eq.trans (he ([] : Database T) (fun j => j.elim0)) ?_)
  exact AggQueryIn.evaluatePlain_eq_zero_of_allEmpty hg q' hu'
    ([] : Database T) Database.allEmpty_nil (fun j => j.elim0)

/-- **`Π` is necessary**, the recursions included: without it a query's
multiplicities are bounded by the query wherever it is defined – a
recursive term then reads the previous round tuple by tuple, so a bag
recursion that settles is its base – and a projection of a relation
with a repeated column has unbounded ones. -/
theorem proj_mem_of_generatesOn {S : Set OpKind}
    (hS : GeneratesOn ℕ schemaS S) : OpKind.proj ∈ S := by
  by_contra hp
  obtain ⟨q', hsch, hu', hset, he⟩ := hS projWitness (by rfl)
    ⟨⟨by simp [plainOps, basisDD, basisOps], fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl⟩, trivial⟩ trivial
  refine projWitness_unbounded_multiplicity ⟨q'.multBound, fun D hnd u => ?_⟩
  rw [he D (fun j => j.elim0)]
  exact AggQueryIn.count_le_multBound hp q' hu' (q'.hygienic_of_overSchema _ hsch) D hnd
    (fun j => j.elim0) (hset D _) u

/-- **One of `×` and the apply is necessary**: without both, an answer
is linear in the instance, and a relation joined with itself is
quadratic. This is the recursion-free form; with the recursions the row
is stated in the minimal universe, `prod_or_apply_mem_of_generatesOnRec`
of `Provenance.RecursionBasis`. -/
theorem prod_or_apply_mem_of_generatesOn {S : Set OpKind}
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S)
    (hS : GeneratesOn ℕ schemaR S) :
    OpKind.prod ∈ S ∨ OpKind.apply ∈ S := by
  by_contra h
  obtain ⟨hp, ha⟩ := not_or.mp h
  obtain ⟨q', hsch, hu', hset, he⟩ := hS prodWitness ⟨by rfl, by rfl⟩
    ⟨by simp [plainOps, basisDD, basisOps], trivial, trivial⟩
    ⟨trivial, trivial⟩
  refine prodWitness_no_linear_bound ⟨q'.sizeBound, fun D => ?_⟩
  rw [he D (fun j => j.elim0)]
  exact AggQueryIn.card_le_sizeBound hp ha q' hu' (q'.hygienic_of_overSchema _ hsch)
    (AggQueryIn.recNoFun_of_usesOnly hmb hms q' hu') D (fun j => j.elim0)
    (hset D _)

/-! ## The two rows that are about the schema

`∅` and `σ`/`−` are necessary for a reason the semantics alone does not
see: a query may name a relation the schema does not declare, and such a
reference reads the empty relation. So without `∅` one can still write a
query with no rows – by naming nothing – and without `σ` and `−` one can
still write a query that is empty on every instance. What makes them
necessary is that the query be *over the schema*
(`AggQueryIn.overSchema`), which is how `tab:basisclasses` reads its
rows, and the generation then has to produce a query over the same
schema. -/

/-- **`∅` is necessary**, the recursions included: over the empty schema
a query can name no relation, so there is nothing to write it with. No
witness is needed – the unit is already a query over that schema, and
whatever it is equivalent to must be written without a relation name.
A recursion is no way round it: the name it binds is declared to its
*body* only, its base being a query of the ambient schema
(`sec:plain`: in `μR.(q₀,q₁)` the base does not read `R`), so the base
of a recursion over the empty schema has `∅` for its only leaf. -/
theorem empty_mem_of_generatesOn {S : Set OpKind}
    (hS : GeneratesOn T Schema.empty S) : OpKind.empty ∈ S := by
  obtain ⟨q', hsch, hu', -, -⟩ := hS (AggQueryIn.unit : AggQuery T 0 _)
    AggQueryIn.overSchema_unit
    (usesOnly_unit (by simp [plainOps, basisDD, basisOps])
      (by simp [plainOps, basisDD, basisOps]))
    winsDerivable_unit
  exact AggQueryIn.usesEmpty_of_overSchema_empty q' hsch hu'

/-- **One of `σ` and `−` is necessary**, the recursions included: without
both, a query over the schema is empty on every instance or non-empty on
every full one wherever it is defined, and a selection on a value is
neither – it keeps the row of one full instance and drops the row of
another. -/
theorem sel_or_diff_mem_of_generatesOn {S : Set OpKind}
    (hS : GeneratesOn ℕ schemaR S) :
    OpKind.sel ∈ S ∨ OpKind.diff ∈ S := by
  by_contra h
  obtain ⟨hsel, hdiff⟩ := not_or.mp h
  obtain ⟨q', hsch, hu', hset, he⟩ := hS selWitness (by rfl)
    ⟨by simp [plainOps, basisDD, basisOps], trivial⟩ trivial
  refine selWitness_breaks ?_
  rcases AggQueryIn.zero_or_ne_zero_of_noSelDiff hsel hdiff q' hu' hsch with
    h0 | h1
  · exact Or.inl (fun D γ => (he D γ).trans (h0 D γ (hset D γ)))
  · exact Or.inr (fun D γ hfull hc =>
      h1 D γ hfull (hset D γ) ((he D γ).symm.trans hc))

/-! ## The swaps: a selection as a difference, a product as an apply

`sec:basis` says that `−` may stand in for `σ`, and the apply for `×`.
Both identities are in `Provenance.PlainBasis`; what they ask of a query
is that the input of a selection and the left factor of a product have
regular columns – the difference and an apply's left side take those –
and `AggQueryIn.exists_allReg` is what puts a query in that shape
(`AggQueryIn.SwapReady`). These two passes then apply them everywhere. -/

/-- **Every product is an apply** (recursively): one whose right side
reads no outer column, which is what `apply_plainEquiv_prod` says. -/
theorem AggQueryIn.exists_prodFree {S : Set OpKind} {sch : Schema}
    (ha : OpKind.apply ∈ S) (hmb : OpKind.muBag ∉ S)
    (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l), l = [] →
      q.usesOnly (insert OpKind.prod S) → q.SwapReady → q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S ∧ q'.overSchema sch
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ _ _ hqs => ⟨AggQueryIn.Rel n s, trivial, hqs, fun _ _ => rfl⟩
  | Hole n s => exact fun hl => absurd hl (by simp)
  | Param pv ρ =>
    exact fun _ hq _ _ => ⟨AggQueryIn.Param pv ρ,
      ⟨mem_of_mem_insert (by decide) hq.1, mem_of_mem_insert (by decide) hq.2.1, mem_of_mem_insert
          (by decide) hq.2.2⟩, trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun _ hq _ _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) hq, trivial, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hl hq.2 hw hqs
    refine ⟨AggQueryIn.Proj ps q',
      ⟨⟨mem_of_mem_insert (by decide) hq.1.1, hq.1.2⟩, hu'⟩, hs',
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q _ ih =>
    intro hl hq hw hqs
    subst hl
    obtain ⟨q', hu', hs', he'⟩ := ih rfl hq.2 hw.2.2 hqs
    refine ⟨AggQueryIn.Sel φ q' trivial,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hl hq hw hqs
    obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
    obtain ⟨hreg, hw₁, hw₂⟩ := hw
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hl₁ hq.2.1 hw₁ hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hl₂ hq.2.2 hw₂ hqs.2
    have hκ := funext hreg
    subst hκ
    -- a product is the apply whose right side reads no outer column
    refine ⟨AggQueryIn.Apply q₁'
        (q₂'.substMap (fun k : Fin _ => Sum.inr (Fin.natAdd _ k))),
      ⟨ha, hu₁, (AggQueryIn.usesOnly_substMap q₂' _).mpr hu₂⟩,
      ⟨hs₁, (AggQueryIn.overSchema_substMap q₂' _ sch).mpr hs₂⟩,
      fun D γ => ?_⟩
    refine Eq.trans ?_ (AggQueryIn.apply_plainEquiv_prod q₁' q₂' D γ).symm
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hl hq hw hqs
    subst hl
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ rfl hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ rfl hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Apply q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.bind_congr (fun u _ =>
      congrArg (Multiset.map _) (he₂ D (Fin.append u γ)))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hl hq hw hqs
    obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hl₁ hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hl₂ hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih rfl hq.2 hw hqs
    refine ⟨AggQueryIn.Dedup q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hl hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ rfl hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ rfl hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Diff q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Explode i hi q ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hl hq hw hqs
    exact ⟨AggQueryIn.Explode i hi q', hu', hs', fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hl hq hw hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs', fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
      exact fun _ hq => absurd hq.1 (not_mem_insert_of_ne (by decide) hmb)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
      exact fun _ hq => absurd hq.1 (not_mem_insert_of_ne (by decide) hms)
  | Gamma is ts fs q keep ord ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih rfl hq.2 hw hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih rfl hq.2 hw hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih rfl hq.2 hw hqs
    refine ⟨AggQueryIn.GammaNest is his pc fn q',
      ⟨⟨mem_of_mem_insert (by decide) hq.1.1, hq.1.2⟩, hu'⟩, hs',
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs b q keep ih => exact fun _ hq => hq.elim
  | ProvSum is his t q ih => exact fun _ hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih rfl hq.2 hw hqs
    refine ⟨AggQueryIn.Win P' O o w t fn q' hrr dist keep,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hl hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih rfl hq.2 hw hqs
    refine ⟨AggQueryIn.WinExpr P' O o ws ts fs g q' keeps,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]

/-- **Every selection is a difference** (recursively): the rows tagged
with the predicate's value, minus those the constant tagging leaves out,
which is what `sel_plainEquiv_selByDiff_polTerm` says. The query is
asked to be closed, which is where that identity is proved, and to use
no apply – both of which the three passes' output is. -/
theorem AggQueryIn.exists_selFree {S : Set OpKind} {sch : Schema}
    (hp : OpKind.proj ∈ S) (hd : OpKind.diff ∈ S)
    (hap : OpKind.apply ∉ S) (hmb : OpKind.muBag ∉ S)
    (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
        l = [] → c = 0 →
      q.usesOnly (insert OpKind.sel S) → q.SwapReady → q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S ∧ q'.overSchema sch
        ∧ q'.SwapReady ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ _ _ _ hqs => ⟨AggQueryIn.Rel n s, trivial, hqs, trivial, fun _ _ => rfl⟩
  | Hole n s => exact fun hl => absurd hl (by simp)
  | Param pv ρ =>
    exact fun _ _ hq _ _ => ⟨AggQueryIn.Param pv ρ,
      ⟨mem_of_mem_insert (by decide) hq.1, mem_of_mem_insert (by decide) hq.2.1, mem_of_mem_insert
          (by decide) hq.2.2⟩, trivial, trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun _ _ hq _ _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) hq, trivial, trivial, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hl hc hq.2 hw hqs
    refine ⟨AggQueryIn.Proj ps q', ⟨⟨hp, hq.1.2⟩, hu'⟩, hs', hw',
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q _ ih =>
    intro hl hc hq hw hqs
    subst hl
    obtain ⟨hreg, hagg, hw'⟩ := hw
    obtain ⟨q', hu', hs', hw'', he'⟩ := ih rfl hc hq.2 hw' hqs
    subst hc
    have hκ := funext hreg
    subst hκ
    refine ⟨AggQueryIn.selByDiff ValueType.nonzero
        (φ.polTerm ValueType.nonzero true) q',
      AggQueryIn.usesOnly_selByDiff ValueType.nonzero _ hp hd hu',
      AggQueryIn.overSchema_selByDiff ValueType.nonzero _ hs',
      AggQueryIn.swapReady_selByDiff ValueType.nonzero _ hw'',
      fun D γ => ?_⟩
    refine Eq.trans ?_ (AggQueryIn.sel_plainEquiv_selByDiff_polTerm
      ValueType.nonzero ValueType.nonzero_ne_zero φ hagg q' D γ)
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hl hc hq hw hqs
    obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hl₁ hc hq.2.1 hw.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hl₂ hc hq.2.2 hw.2.2 hqs.2
    refine ⟨AggQueryIn.Prod q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      ⟨hw.1, hw₁, hw₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro _ _ hq
    exact absurd (mem_of_mem_insert (by decide) hq.1) hap
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hl hc hq hw hqs
    obtain ⟨hl₁, hl₂⟩ := List.append_eq_nil_iff.mp hl
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hl₁ hc hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hl₂ hc hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      ⟨hw₁, hw₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih rfl hc hq.2 hw hqs
    refine ⟨AggQueryIn.Dedup q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hl hc hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ rfl hc hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ rfl hc hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Diff q₁' q₂', ⟨hd, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      ⟨hw₁, hw₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Explode i hi q ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hl hc hq hw hqs
    exact ⟨AggQueryIn.Explode i hi q', hu', hs', hw', fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hl hc hq hw hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs', hw', fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ =>
      exact fun _ _ hq => absurd hq.1 (not_mem_insert_of_ne (by decide) hmb)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
      exact fun _ _ hq => absurd hq.1 (not_mem_insert_of_ne (by decide) hms)
  | Gamma is ts fs q keep ord ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih rfl hc hq.2 hw hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih rfl hc hq.2 hw hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih rfl hc hq.2 hw hqs
    refine ⟨AggQueryIn.GammaNest is his pc fn q',
      ⟨⟨mem_of_mem_insert (by decide) hq.1.1, hq.1.2⟩, hu'⟩, hs', hw',
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs b q keep ih => exact fun _ _ hq => hq.elim
  | ProvSum is his t q ih => exact fun _ _ hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih rfl hc hq.2 hw hqs
    refine ⟨AggQueryIn.Win P' O o w t fn q' hrr dist keep,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hl hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih rfl hc hq.2 hw hqs
    refine ⟨AggQueryIn.WinExpr P' O o ws ts fs g q' keeps,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]

/-! ## The two alternative bases

With the swaps proved as passes, the generation half holds of the two
sets `sec:basis` offers in place of the six: `−` may stand in for `σ`,
and the apply for `×`. Each is the three passes, then the re-typing,
then the pass that applies the identity everywhere – the re-typing in
the middle because a selection's input and a product's left factor have
to hold values, which is what the difference and an apply's left side
take. -/

/-- The basis with the difference in place of the selection. -/
def basisDiffOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.prod, OpKind.union, OpKind.gamma,
    OpKind.diff}

/-- The basis with the apply in place of the product. -/
def basisApplyOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.sel, OpKind.apply, OpKind.union,
    OpKind.gamma}

/-- **The basis with `−` for `σ`**: every query of the plain fragment
whose projections post-compose no aggregate column is equivalent to one
over `∅`, `Π`, `×`, `⊎`, `γ`, `−`. The value domain's own non-zero
value is what the selection's difference marks the rows it keeps
with. -/
theorem AggQueryIn.exists_basisDiffOps_plainEquiv {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps)
    (hd : q.WinsDerivable) (hqs : q.overSchema sch) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.usesOnly basisDiffOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  obtain ⟨q₃, hu₃, hs₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_plainEquiv cnt hcnt q hq hd hqs
  obtain ⟨q₄, hu₄, hs₄, hw₄, he₄⟩ :=
    AggQueryIn.exists_allReg (S := basisOps) (sch := sch)
        (by simp [basisOps]) (by simp [basisOps]) q₃ hu₃
      (AggQueryIn.retypable_of_usesOnly (by simp [basisOps]) q₃ hu₃) hs₃
  obtain ⟨q₅, hu₅, hs₅, -, he₅⟩ :=
    AggQueryIn.exists_selFree (S := basisDiffOps) (by simp [basisDiffOps])
      (by simp [basisDiffOps]) (by simp [basisDiffOps])
      (by simp [basisDiffOps]) (by simp [basisDiffOps]) q₄ rfl rfl
      (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with h | h | h | h | h | h <;>
          simp [basisDiffOps, h]) q₄ hu₄) hw₄ hs₄
  exact ⟨q₅, hu₅, hs₅,
    fun D γ => ((he₃ D γ).trans (he₄ D γ)).trans (he₅ D γ)⟩

/-- **The basis with the apply for `×`**: the same, over `∅`, `Π`, `σ`,
the apply, `⊎`, `γ`. -/
theorem AggQueryIn.exists_basisApplyOps_plainEquiv {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt) (q : AggQuery T n κ)
    (hq : q.usesOnly plainOps) (hd : q.WinsDerivable)
    (hqs : q.overSchema sch) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.usesOnly basisApplyOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  obtain ⟨q₃, hu₃, hs₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_plainEquiv cnt hcnt q hq hd hqs
  obtain ⟨q₄, hu₄, hs₄, hw₄, he₄⟩ :=
    AggQueryIn.exists_allReg (S := basisOps) (sch := sch)
        (by simp [basisOps]) (by simp [basisOps]) q₃ hu₃
      (AggQueryIn.retypable_of_usesOnly (by simp [basisOps]) q₃ hu₃) hs₃
  obtain ⟨q₅, hu₅, hs₅, he₅⟩ :=
    AggQueryIn.exists_prodFree (S := basisApplyOps) (by simp [basisApplyOps])
      (by simp [basisApplyOps]) (by simp [basisApplyOps])
      q₄ rfl (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with h | h | h | h | h | h <;>
          simp [basisApplyOps, h]) q₄ hu₄) hw₄ hs₄
  exact ⟨q₅, hu₅, hs₅,
    fun D γ => ((he₃ D γ).trans (he₄ D γ)).trans (he₅ D γ)⟩

/-- **`{∅, Π, ×, ⊎, γ, −}` generates, over a schema.** -/
theorem basisDiffOps_generatesOn (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt) (sch : Schema) :
    GeneratesOn T sch basisDiffOps :=
  fun q hqs hq hd => by
    obtain ⟨q', hu', hs', he'⟩ :=
      AggQueryIn.exists_basisDiffOps_plainEquiv cnt hcnt q hq hd hqs
    exact ⟨q', hs', hu',
      AggQueryIn.settlesAt_of_usesOnly (by simp [basisDiffOps])
        (by simp [basisDiffOps]) q' hu', he'⟩

/-- **`{∅, Π, σ, apply, ⊎, γ}` generates, over a schema.** -/
theorem basisApplyOps_generatesOn (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt) (sch : Schema) :
    GeneratesOn T sch basisApplyOps :=
  fun q hqs hq hd => by
    obtain ⟨q', hu', hs', he'⟩ :=
      AggQueryIn.exists_basisApplyOps_plainEquiv cnt hcnt q hq hd hqs
    exact ⟨q', hs', hu',
      AggQueryIn.settlesAt_of_usesOnly (by simp [basisApplyOps])
        (by simp [basisApplyOps]) q' hu', he'⟩

/-- Over `ℕ`, with `COUNT(*)` as the aggregate. -/
theorem basisDiffOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisDiffOps :=
  basisDiffOps_generatesOn SeqAggFunc.count counts_count_nat sch

/-- Over `ℕ`, with `COUNT(*)` as the aggregate. -/
theorem basisApplyOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisApplyOps :=
  basisApplyOps_generatesOn SeqAggFunc.count counts_count_nat sch

/-! ## Three windows that are derivable

`AggQueryIn.WinsDerivable` asks of a window that its frame contain its
current row and that its input be all regular. These are the three
frames of `sec:basis`'s `prop:winderived` that satisfy the first, each
over any `DISTINCT` and any `FILTER` clause: the whole partition and the
two `RANGE` frames. Nothing is asked of the frame condition, which
`ValueFrame.exists_framePred` reads as a predicate of the language, nor
of the domain. -/

/-- **A window over the whole partition is derivable.** -/
theorem AggQueryIn.winsDerivable_win_whole {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (t : TermIn T c n)
    (f : SeqAggFunc T) {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o ValueFrame.whole t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.containsSelf_whole, hq⟩

/-- **And one over `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT
ROW`.** -/
theorem AggQueryIn.winsDerivable_win_rangeUpTo {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : TermIn T c n) (f : SeqAggFunc T)
    {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o (ValueFrame.rangeUpTo o) t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.rangeUpTo_containsSelf o, hq⟩

/-- **And one over the same frame excluding the current row's peers**
(`EXCLUDE GROUP`), which is what a running total that must not read its
own row needs. -/
theorem AggQueryIn.winsDerivable_win_rangeBefore {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : TermIn T c n) (f : SeqAggFunc T)
    {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o (ValueFrame.rangeBefore o) t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.rangeBefore_containsSelf o, hq⟩

/-! ## The fourth basis: both swaps at once

`sec:basis` offers the two swaps independently, so a fourth basis is the
two together: `−` for `σ` and the apply for `×`. What makes the
composition work is that the selection pass leaves its output ready for
the product pass (`AggQueryIn.swapReady_selByDiff`), the difference it
builds introducing neither a product nor a selection of its own. -/

/-- The basis with the difference for the selection *and* the apply for
the product. -/
def basisApplyDiffOps : Set OpKind :=
  {OpKind.empty, OpKind.proj, OpKind.apply, OpKind.union, OpKind.gamma,
    OpKind.diff}

/-- **The basis with `−` for `σ` and the apply for `×`**: every query of
the plain fragment whose projections post-compose no aggregate column is
equivalent to one over `∅`, `Π`, the apply, `⊎`, `γ`, `−`. -/
theorem AggQueryIn.exists_basisApplyDiffOps_plainEquiv {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps)
    (hd : q.WinsDerivable) (hqs : q.overSchema sch) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.usesOnly basisApplyDiffOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  obtain ⟨q₃, hu₃, hs₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_plainEquiv cnt hcnt q hq hd hqs
  obtain ⟨q₄, hu₄, hs₄, hw₄, he₄⟩ :=
    AggQueryIn.exists_allReg (S := basisOps) (sch := sch)
        (by simp [basisOps]) (by simp [basisOps]) q₃ hu₃
      (AggQueryIn.retypable_of_usesOnly (by simp [basisOps]) q₃ hu₃) hs₃
  -- the selections become differences, and what is left is still ready
  -- for the product swap
  obtain ⟨q₅, hu₅, hs₅, hw₅, he₅⟩ :=
    AggQueryIn.exists_selFree (S := basisDiffOps) (by simp [basisDiffOps])
      (by simp [basisDiffOps]) (by simp [basisDiffOps])
      (by simp [basisDiffOps]) (by simp [basisDiffOps]) q₄ rfl rfl
      (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with h | h | h | h | h | h <;>
          simp [basisDiffOps, h]) q₄ hu₄) hw₄ hs₄
  -- and then the products become applies
  obtain ⟨q₆, hu₆, hs₆, he₆⟩ :=
    AggQueryIn.exists_prodFree (S := basisApplyDiffOps)
      (by simp [basisApplyDiffOps]) (by simp [basisApplyDiffOps])
      (by simp [basisApplyDiffOps]) q₅ rfl (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisDiffOps, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hk
        rcases hk with h | h | h | h | h | h <;>
          simp [basisApplyDiffOps, h]) q₅ hu₅) hw₅ hs₅
  exact ⟨q₆, hu₆, hs₆, fun D γ =>
    (((he₃ D γ).trans (he₄ D γ)).trans (he₅ D γ)).trans (he₆ D γ)⟩

/-- **`{∅, Π, apply, ⊎, γ, −}` generates, over a schema.** -/
theorem basisApplyDiffOps_generatesOn (cnt : SeqAggFunc T)
    (hcnt : SeqAggFunc.Counts cnt) (sch : Schema) :
    GeneratesOn T sch basisApplyDiffOps :=
  fun q hqs hq hd => by
    obtain ⟨q', hu', hs', he'⟩ :=
      AggQueryIn.exists_basisApplyDiffOps_plainEquiv cnt hcnt q hq hd hqs
    exact ⟨q', hs', hu',
      AggQueryIn.settlesAt_of_usesOnly (by simp [basisApplyDiffOps])
        (by simp [basisApplyDiffOps]) q' hu', he'⟩

/-- Over `ℕ`, with `COUNT(*)` as the aggregate. -/
theorem basisApplyDiffOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisApplyDiffOps :=
  basisApplyDiffOps_generatesOn SeqAggFunc.count counts_count_nat sch

