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

**The two alternative bases are stated and proved**:
`AggQueryIn.exists_basisDiffOps_plainEquiv` over `{∅, Π, ×, ⊎, γ, −}`
and `AggQueryIn.exists_basisApplyOps_plainEquiv` over
`{∅, Π, σ, apply, ⊎, γ}`, with `basisDiffOps_generatesOn` and
`basisApplyOps_generatesOn` their `GeneratesOn` forms. Each is the three
passes, then the re-typing, then the swap. What makes the composition
work is that `AggQueryIn.NoAggTerm` – no projection column
post-composing an aggregate column – is *preserved* by all three passes
and by the decorrelation, and that the window case of
`AggQueryIn.Retypable` is vacuous after the first pass, which replaces
every window by an apply of a scalar aggregation
(`AggQueryIn.retypable_of_noAggTerm`). Each pass carries the
preservation as an **implication** in its conclusion
(`q.NoAggTerm → q'.NoAggTerm`, and `P.NoAggTerm → q.NoAggTerm →
q'.NoAggTerm` for the decorrelation, whose construction reads the
parameter relation too), so the six-class theorems ask nothing extra and
only the two alternative bases need the property of their input.
`GeneratesOn` asks it of every query it quantifies over, which makes the
six necessity rows statements about a smaller class of generating
sets.
-/

variable {T : Type} [ValueType T]

/-! ## What a window has to be for `prop:winderived` to reach it -/

/-- **Every window of the query is derivable.** At each window: its
input's columns are all regular (an apply reads its left side as a
relation of values), its frame contains its current row, and there is a
predicate of the language that holds exactly where the frame condition
holds and the window's `FILTER` clause keeps the row. The last is a
statement about the *encoding* rather than a restriction on queries: in
SQL a frame clause and a `FILTER` clause are both conditions one can
write, while in the library `ValueFrame.ρ` is an arbitrary relation on
order values.

`DISTINCT` and a `FILTER` clause are covered (since 2026-10-08): the
derived form aggregates `f^distinct` where the window does, and the
clause enters the selection that spells the frame out
(`evaluatePlain_winByApplyOf`). The predicate is *built* for three
frames, not merely asked for: the whole partition
(`AggQueryIn.winsDerivable_win_whole`), and the two `RANGE` frames read
against the clause, either over a domain with no null (`_rangeUpTo`,
`_rangeBefore`) or over one that names its null (`_rangeUpTo_of_null`,
`_rangeBefore_of_null`, where the clause's null placement is read by
`IS NOT DISTINCT FROM ν` tests).
What stays out is a *multi-frame* window, and not for want of proving:
its column combines the leaves' values by a function no term expresses,
so the predicate reads `False` there, as it does for
`ProjColIn.aggTerm` elsewhere. -/
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
  | c, _, _, @AggQueryIn.Win _ _ n _ _ κ' _ O _ w _ _ q _ _ keep =>
      (∀ i, κ' i = ColKind.reg) ∧ w.ContainsSelf
        ∧ (∃ ψ : GenPredIn T (n + c) (ColKind.allReg n),
            ∀ (y u : Tuple T n) (γ : Fin c → T),
              ψ.holdsPlain y (Fin.append u γ)
                ↔ (w.ρ (Tuple.key O y) (Tuple.key O u) = true
                    ∧ Selection.keepsOpt keep y = true))
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
theorem AggQueryIn.exists_winFree {S : Set OpKind} {sch : Schema}
    (ha : OpKind.apply ∈ S) (hg : OpKind.gamma ∈ S) (hs : OpKind.sel ∈ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly (insert OpKind.win S) → q.WinsDerivable →
      q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S ∧ q'.overSchema sch
        ∧ (q.NoAggTerm → q'.NoAggTerm)
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ q
  induction q with
  | Rel n s =>
    exact fun _ _ hqs =>
      ⟨AggQueryIn.Rel n s, trivial, hqs, fun _ => trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun hq _ _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) hq, trivial, fun _ => trivial,
      fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Proj ps q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', (fun hn => ⟨hn.1, hn' hn.2⟩),
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Sel φ q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', (fun hn => hn' hn), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, hn₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hn₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Prod q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, (fun hn => ⟨hn₁ hn.1, hn₂ hn.2⟩),
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, hn₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hn₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Apply q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, (fun hn => ⟨hn₁ hn.1, hn₂ hn.2⟩),
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.bind_congr (fun u _ =>
      congrArg (Multiset.map _) (he₂ D (Fin.append u γ)))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, hn₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hn₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, (fun hn => ⟨hn₁ hn.1, hn₂ hn.2⟩),
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Dedup q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', (fun hn => hn' hn), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hd hqs
    obtain ⟨q₁', hu₁, hs₁, hn₁, he₁⟩ := ih₁ hq.2.1 hd.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hn₂, he₂⟩ := ih₂ hq.2.2 hd.2 hqs.2
    refine ⟨AggQueryIn.Diff q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, (fun hn => ⟨hn₁ hn.1, hn₂ hn.2⟩),
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Alt i hi q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq hd hqs
    exact ⟨AggQueryIn.Alt i hi q', hu', hs', (fun hn => hn' hn),
      fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq hd hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs', (fun hn => hn' hn),
      fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', (fun hn => hn' hn), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', (fun hn => hn' hn), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc f q ih =>
    intro hq hd hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq.2 hd hqs
    refine ⟨AggQueryIn.GammaNest is his pc f q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', (fun hn => ⟨hn.1, hn' hn.2⟩),
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P' O o w t f q hrr dist keep ih =>
    intro hq hd hqs
    obtain ⟨hreg, hcs, ⟨ψ, hψ⟩, hd'⟩ := hd
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hq.2 hd' hqs
    have hκ := funext hreg
    subst hκ
    refine ⟨winByApply P' O o ψ t (if dist then f.distinct else f) q',
      usesOnly_winByApply P' O o ψ t _ ha hg hs hu',
      overSchema_winByApply P' O o ψ t _ hs',
      (fun hn => noAggTerm_winByApply P' O o ψ t _ (hn' hn)),
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
    (hap : OpKind.apply ∉ S) (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ), c = 0 →
      q.usesOnly (insert OpKind.dedup (insert OpKind.diff S)) →
      q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S ∧ q'.overSchema sch
        ∧ (q.NoAggTerm → q'.NoAggTerm)
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ q
  induction q with
  | Rel n s =>
    exact fun _ _ hqs =>
      ⟨AggQueryIn.Rel n s, trivial, hqs, fun _ => trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun _ hq _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) (mem_of_mem_insert (by decide) hq),
      trivial, fun _ => trivial, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Proj ps q', ⟨hp, hu'⟩, hs',
      (fun hn => ⟨hn.1, hn' hn.2⟩), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Sel φ q', ⟨hs, hu'⟩, hs', (fun hn => hn' hn),
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hc hq hqs
    obtain ⟨q₁', hu₁, hs₁, hn₁, he₁⟩ := ih₁ hc hq.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hn₂, he₂⟩ := ih₂ hc hq.2.2 hqs.2
    refine ⟨AggQueryIn.Prod q₁' q₂', ⟨hx, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      (fun hn => ⟨hn₁ hn.1, hn₂ hn.2⟩), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro _ hq
    exact absurd (mem_of_mem_insert (by decide)
      (mem_of_mem_insert (by decide) hq.1)) hap
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hc hq hqs
    obtain ⟨q₁', hu₁, hs₁, hn₁, he₁⟩ := ih₁ hc hq.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hn₂, he₂⟩ := ih₂ hc hq.2.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂', ⟨hu, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      (fun hn => ⟨hn₁ hn.1, hn₂ hn.2⟩), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    -- duplicate elimination is the grouping on every column
    refine ⟨(AggQueryIn.Gamma (fun k => k) (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0) q').castKind ?_, ?_, ?_, ?_,
      fun D γ => ?_⟩
    · funext j
      refine Fin.addCases (fun k => ?_) (fun z => z.elim0) j
      rw [Fin.append_left]
      rfl
    · rw [AggQueryIn.usesOnly_castKind]
      exact ⟨hg, hu'⟩
    · rw [AggQueryIn.overSchema_castKind]
      exact hs'
    · intro hn
      rw [AggQueryIn.noAggTerm_castKind]
      exact hn' hn
    · rw [AggQueryIn.evaluatePlain_castKind]
      refine Eq.trans ?_ (AggQueryIn.dedup_plainEquiv_gamma q' D γ)
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hc hq hqs
    obtain ⟨q₁', hu₁, hs₁, hn₁, he₁⟩ := ih₁ hc hq.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hn₂, he₂⟩ := ih₂ hc hq.2.2 hqs.2
    subst hc
    -- the difference is a count over the tagged union
    refine ⟨AggQueryIn.notInDiff ValueType.nonzero f q₁' q₂',
      AggQueryIn.usesOnly_notInDiff ValueType.nonzero f hp hs hx hu hg hu₁ hu₂,
      AggQueryIn.overSchema_notInDiff ValueType.nonzero f hs₁ hs₂,
      (fun hn => AggQueryIn.noAggTerm_notInDiff ValueType.nonzero f
        (hn₁ hn.1) (hn₂ hn.2)),
      fun D γ => ?_⟩
    refine Eq.trans ?_ (AggQueryIn.diff_plainEquiv_notIn ValueType.nonzero
      ValueType.nonzero_ne_zero f hzero q₁' q₂' D γ)
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Alt i hi q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq hqs
    exact ⟨AggQueryIn.Alt i hi q', hu', hs', (fun hn => hn' hn),
      fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs', (fun hn => hn' hn),
      fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun _ hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun _ hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord, ⟨hg, hu'⟩, hs',
      (fun hn => hn' hn), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord, ⟨hg, hu'⟩, hs',
      (fun hn => hn' hn), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.GammaNest is his pc fn q', ⟨hg, hu'⟩, hs',
      (fun hn => ⟨hn.1, hn' hn.2⟩), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs b q keep ih => exact fun _ hq => hq.elim
  | ProvSum is his t q ih => exact fun _ hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.Win P' O o w t fn q' hrr dist keep,
      ⟨mem_of_mem_insert (by decide)
        (mem_of_mem_insert (by decide) hq.1), hu'⟩, hs',
      (fun hn => hn' hn), fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hc hq hqs
    obtain ⟨q', hu', hs', hn', he'⟩ := ih hc hq.2 hqs
    refine ⟨AggQueryIn.WinExpr P' O o ws ts fs g q' keeps,
      ⟨mem_of_mem_insert (by decide)
        (mem_of_mem_insert (by decide) hq.1), hu'⟩, hs',
      (fun hn => hn' hn), fun D γ => ?_⟩
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
and a predicate of the language holding where its frame condition holds
and its `FILTER` clause keeps the row. `DISTINCT` and the clause are
covered; a multi-frame window is not. -/
theorem AggQueryIn.exists_basisOps_plainEquiv_noAggTerm {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps) (hd : q.WinsDerivable)
    (hqs : q.overSchema sch) :
    ∃ q' : AggQuery T n κ,
      q'.usesOnly basisOps ∧ q'.overSchema sch
        ∧ (q.NoAggTerm → q'.NoAggTerm) ∧ q.PlainEquiv q' := by
  -- the windows go
  obtain ⟨q₁, hu₁, hs₁, hn₁, he₁⟩ :=
    AggQueryIn.exists_winFree (S := insert OpKind.apply basisDD)
      (by simp [basisDD, basisOps]) (by simp [basisDD, basisOps])
      (by simp [basisDD, basisOps]) q hq hd hqs
  -- the applies go, by the decorrelation
  obtain ⟨q₂, hu₂, hs₂, hn₂, he₂⟩ :=
    AggQueryIn.exists_applyFree_plainEquiv (S := basisDD)
      (by intro k hk; simp [decorrOps] at hk; rcases hk with h|h|h|h|h|h|h <;>
        simp [basisDD, basisOps, h])
      (by simp [basisDD, basisOps]) q₁ hu₁ hs₁
  -- and duplicate elimination and the difference go with them
  obtain ⟨q₃, hu₃, hs₃, hn₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_of_dedupDiff (S := basisOps)
      (by simp [basisOps]) (by simp [basisOps]) (by simp [basisOps])
      (by simp [basisOps]) (by simp [basisOps]) (by simp [basisOps])
      f hzero q₂ rfl hu₂ hs₂
  exact ⟨q₃, hu₃, hs₃, fun hqn => hn₃ (hn₂ (hn₁ hqn)),
    fun D γ => (he₁ D γ).trans ((he₂ D γ).trans (he₃ D γ))⟩

/-- **The generation half of `thm:plainbasis`**: every query of the plain
fragment is equivalent to one using only the six basis classes `∅`, `Π`,
`σ`, `×`, `⊎`, `γ`, over the same schema.

`exists_basisOps_plainEquiv_noAggTerm` is the same statement with the
no-aggTerm invariant carried through, which is what the bases that
re-type their columns need; it is no part of what the theorem says. -/
theorem AggQueryIn.exists_basisOps_plainEquiv {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps) (hd : q.WinsDerivable)
    (hqs : q.overSchema sch) :
    ∃ q' : AggQuery T n κ,
      q'.usesOnly basisOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  obtain ⟨q', hu', hs', -, he'⟩ :=
    AggQueryIn.exists_basisOps_plainEquiv_noAggTerm f hzero q hq hd hqs
  exact ⟨q', hu', hs', he'⟩

/-- **A generating set over a schema**: every query over `sch` whose
windows are derivable, and which applies no function to an aggregate
column, is equivalent to one over `sch` using only the classes of `S`.
This is the form the classification needs for the `∅` and `σ`/`−` rows;
the three passes give the equivalence on *every* instance, which is
stronger than `AggQueryIn.PlainEquivOn` asks. The query produced has
regular columns throughout, which is what the swaps need and what the
plain semantics has anyway. -/
def GeneratesOn (T : Type) [ValueType T] (sch : Schema) (S : Set OpKind) :
    Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ),
    q.overSchema sch → q.usesOnly plainOps → q.WinsDerivable →
      q.NoAggTerm →
      ∃ q' : AggQuery T n (ColKind.allReg n),
        q'.overSchema sch ∧ q'.usesOnly S ∧ q.PlainEquiv q'

/-- The schema of the binary relation the projection witness reads. -/
def schemaS : Schema := fun s => if s = "S" then some 2 else none

/-- **The six classes generate, over a schema**: `GeneratesOn`'s form of
the theorem above, which is what the classification's other half is
stated against. -/
theorem basisOps_generatesOn (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) (sch : Schema) :
    GeneratesOn T sch basisOps :=
  fun q hqs hq hd hqn => by
    obtain ⟨q₃, hu₃, hs₃, hn₃, he₃⟩ :=
      AggQueryIn.exists_basisOps_plainEquiv_noAggTerm f hzero q hq hd hqs
    obtain ⟨q', hu', hs', -, he'⟩ :=
      AggQueryIn.exists_allReg (S := basisOps) (sch := sch) q₃ hu₃
        (AggQueryIn.retypable_of_noAggTerm (by simp [basisOps]) q₃ hu₃
          (hn₃ hqn)) hs₃
    exact ⟨q', hs', hu', fun D γ => (he₃ D γ).trans (he' D γ)⟩

/-- Over `ℕ`, with the tag `1` and the sum. -/
theorem basisOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisOps :=
  basisOps_generatesOn List.sum (fun _ => List.sum_eq_zero_iff) sch

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

omit [ValueType T] in
/-- The unit applies no function to an aggregate column. -/
private theorem noAggTerm_unit :
    (AggQueryIn.unit : AggQuery T 0 (ColKind.allReg 0)).NoAggTerm := by
  unfold AggQueryIn.unit
  rw [AggQueryIn.noAggTerm_castKind]
  exact trivial

omit [ValueType T] in
/-- Nor does a constant row: its columns are constants. -/
private theorem noAggTerm_rowOf {k : ℕ} (u : Tuple T k) :
    (AggQueryIn.rowOf u).NoAggTerm := by
  unfold AggQueryIn.rowOf
  rw [AggQueryIn.noAggTerm_castKind]
  exact ⟨fun _ => rfl, noAggTerm_unit⟩

/-- **`⊎` is necessary**: without it a thin instance has an answer of at
most one row, and two copies of one row are two. -/
theorem union_mem_of_generatesOn {S : Set OpKind} {sch : Schema}
    (hS : GeneratesOn T sch S) : OpKind.union ∈ S := by
  by_contra hu
  set u : Tuple T 0 := fun j => j.elim0 with hu0
  obtain ⟨q', -, hu', he⟩ := hS (AggQueryIn.values [u, u] (by simp))
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
    (show (AggQueryIn.Sum (AggQueryIn.rowOf u)
        (AggQueryIn.rowOf u)).NoAggTerm from
      ⟨noAggTerm_rowOf u, noAggTerm_rowOf u⟩)
  have h2 := AggQueryIn.card_values_two u ([] : Database T) (fun j => j.elim0)
  rw [he ([] : Database T) (fun j => j.elim0)] at h2
  have h1 := AggQueryIn.card_le_one_of_thin hu q' hu' ([] : Database T)
    Database.thin_nil (fun j => j.elim0)
  omega

/-- **`γ` is necessary**: without it the all-empty instance has an empty
answer, and the unit has a row there. -/
theorem gamma_mem_of_generatesOn {S : Set OpKind} {sch : Schema}
    (hS : GeneratesOn T sch S) : OpKind.gamma ∈ S := by
  by_contra hg
  obtain ⟨q', -, hu', he⟩ := hS (AggQueryIn.unit : AggQuery T 0 _)
    AggQueryIn.overSchema_unit
    (usesOnly_unit (by simp [plainOps, basisDD, basisOps])
      (by simp [plainOps, basisDD, basisOps]))
    winsDerivable_unit noAggTerm_unit
  refine AggQueryIn.evaluatePlain_unit_ne_zero ([] : Database T)
    (fun j => j.elim0) (Eq.trans (he ([] : Database T) (fun j => j.elim0)) ?_)
  exact AggQueryIn.evaluatePlain_eq_zero_of_allEmpty hg q' hu'
    ([] : Database T) Database.allEmpty_nil (fun j => j.elim0)

/-- **`Π` is necessary**: without it a query's multiplicities are
bounded by the query, and a projection of a relation with a repeated
column has unbounded ones. -/
theorem proj_mem_of_generatesOn {S : Set OpKind}
    (hS : GeneratesOn ℕ schemaS S) : OpKind.proj ∈ S := by
  by_contra hp
  obtain ⟨q', -, hu', he⟩ := hS projWitness (by rfl)
    ⟨by simp [plainOps, basisDD, basisOps], trivial⟩ trivial
    ⟨fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl, trivial⟩
  refine projWitness_unbounded_multiplicity ⟨q'.multBound, fun D hnd u => ?_⟩
  rw [he D (fun j => j.elim0)]
  exact AggQueryIn.count_le_multBound hp q' hu' D hnd (fun j => j.elim0) u

/-- **One of `×` and the apply is necessary**: without both, an answer
is linear in the instance, and a relation joined with itself is
quadratic. -/
theorem prod_or_apply_mem_of_generatesOn {S : Set OpKind}
    (hS : GeneratesOn ℕ schemaR S) :
    OpKind.prod ∈ S ∨ OpKind.apply ∈ S := by
  by_contra h
  obtain ⟨hp, ha⟩ := not_or.mp h
  obtain ⟨q', -, hu', he⟩ := hS prodWitness ⟨by rfl, by rfl⟩
    ⟨by simp [plainOps, basisDD, basisOps], trivial, trivial⟩ ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩
  refine prodWitness_no_linear_bound ⟨q'.sizeBound, fun D => ?_⟩
  rw [he D (fun j => j.elim0)]
  exact AggQueryIn.card_le_sizeBound hp ha q' hu' D (fun j => j.elim0)

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

/-- **`∅` is necessary**: over the empty schema a query can name no
relation, so there is nothing to write it with. No witness is needed –
the unit is already a query over that schema, and whatever it is
equivalent to must be written without a relation name. -/
theorem empty_mem_of_generatesOn {S : Set OpKind}
    (hS : GeneratesOn T Schema.empty S) : OpKind.empty ∈ S := by
  obtain ⟨q', hsch, hu', -⟩ := hS (AggQueryIn.unit : AggQuery T 0 _)
    AggQueryIn.overSchema_unit
    (usesOnly_unit (by simp [plainOps, basisDD, basisOps])
      (by simp [plainOps, basisDD, basisOps]))
    winsDerivable_unit noAggTerm_unit
  exact AggQueryIn.usesEmpty_of_overSchema_empty q' hsch hu'

/-- **One of `σ` and `−` is necessary**: without both, a query over the
schema is empty on every instance or non-empty on every full one, and a
selection on a value is neither – it keeps the row of one full instance
and drops the row of another. -/
theorem sel_or_diff_mem_of_generatesOn {S : Set OpKind}
    (hS : GeneratesOn ℕ schemaR S) :
    OpKind.sel ∈ S ∨ OpKind.diff ∈ S := by
  by_contra h
  obtain ⟨hsel, hdiff⟩ := not_or.mp h
  obtain ⟨q', hsch, hu', he⟩ := hS selWitness (by rfl)
    ⟨by simp [plainOps, basisDD, basisOps], trivial⟩ trivial trivial
  refine selWitness_breaks ?_
  rcases AggQueryIn.zero_or_ne_zero_of_noSelDiff hsel hdiff q' hu' hsch with
    h0 | h1
  · exact Or.inl (fun D γ => (he D γ).trans (h0 D γ))
  · exact Or.inr (fun D γ hfull hc => h1 D γ hfull ((he D γ).symm.trans hc))

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
    (ha : OpKind.apply ∈ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.usesOnly (insert OpKind.prod S) → q.SwapReady → q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S ∧ q'.overSchema sch
        ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ q
  induction q with
  | Rel n s => exact fun _ _ hqs => ⟨AggQueryIn.Rel n s, trivial, hqs,
      fun _ _ => rfl⟩
  | Empty =>
    exact fun hq _ _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) hq, trivial, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw hqs
    refine ⟨AggQueryIn.Proj ps q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw.2.2 hqs
    refine ⟨AggQueryIn.Sel φ q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hw hqs
    obtain ⟨hreg, hw₁, hw₂⟩ := hw
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hw₁ hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hw₂ hqs.2
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
    intro hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Apply q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.bind_congr (fun u _ =>
      congrArg (Multiset.map _) (he₂ D (Fin.append u γ)))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw hqs
    refine ⟨AggQueryIn.Dedup q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, he₁⟩ := ih₁ hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, he₂⟩ := ih₂ hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Diff q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Alt i hi q ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq hw hqs
    exact ⟨AggQueryIn.Alt i hi q', hu', hs', fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq hw hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs', fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw hqs
    refine ⟨AggQueryIn.GammaNest is his pc fn q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs b q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw hqs
    refine ⟨AggQueryIn.Win P' O o w t fn q' hrr dist keep,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hq hw hqs
    obtain ⟨q', hu', hs', he'⟩ := ih hq.2 hw hqs
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
    (hap : OpKind.apply ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ), c = 0 →
      q.usesOnly (insert OpKind.sel S) → q.SwapReady → q.overSchema sch →
      ∃ q' : AggQueryIn T c n κ, q'.usesOnly S ∧ q'.overSchema sch
        ∧ q'.SwapReady ∧ ∀ (D : Database T) (γ : Fin c → T),
          q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ q
  induction q with
  | Rel n s => exact fun _ _ _ hqs => ⟨AggQueryIn.Rel n s, trivial, hqs,
      trivial, fun _ _ => rfl⟩
  | Empty =>
    exact fun _ hq _ _ => ⟨AggQueryIn.Empty,
      mem_of_mem_insert (by decide) hq, trivial, trivial, fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq.2 hw hqs
    refine ⟨AggQueryIn.Proj ps q', ⟨hp, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Sel φ q ih =>
    intro hc hq hw hqs
    obtain ⟨hreg, hagg, hw'⟩ := hw
    obtain ⟨q', hu', hs', hw'', he'⟩ := ih hc hq.2 hw' hqs
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
    intro hc hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hc hq.2.1 hw.2.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hc hq.2.2 hw.2.2 hqs.2
    refine ⟨AggQueryIn.Prod q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      ⟨hw.1, hw₁, hw₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro _ hq
    exact absurd (mem_of_mem_insert (by decide) hq.1) hap
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hc hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hc hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hc hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂',
      ⟨mem_of_mem_insert (by decide) hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      ⟨hw₁, hw₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq.2 hw hqs
    refine ⟨AggQueryIn.Dedup q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hc hq hw hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hc hq.2.1 hw.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hc hq.2.2 hw.2 hqs.2
    refine ⟨AggQueryIn.Diff q₁' q₂', ⟨hd, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩,
      ⟨hw₁, hw₂⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Alt i hi q ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq hw hqs
    exact ⟨AggQueryIn.Alt i hi q', hu', hs', hw', fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq hw hqs
    exact ⟨AggQueryIn.Retag hbase q', hu', hs', hw', fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun _ hq => hq.elim
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun _ hq => hq.elim
  | Gamma is ts fs q keep ord ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq.2 hw hqs
    refine ⟨AggQueryIn.Gamma is ts fs q' keep ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq.2 hw hqs
    refine ⟨AggQueryIn.GammaScalar ts fs q' ord,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq.2 hw hqs
    refine ⟨AggQueryIn.GammaNest is his pc fn q',
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | GammaTok is his ts fs b q keep ih => exact fun _ hq => hq.elim
  | ProvSum is his t q ih => exact fun _ hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq.2 hw hqs
    refine ⟨AggQueryIn.Win P' O o w t fn q' hrr dist keep,
      ⟨mem_of_mem_insert (by decide) hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hc hq hw hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hc hq.2 hw hqs
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
over `∅`, `Π`, `×`, `⊎`, `γ`, `−`. The tag `yes ≠ 0` is what the
selection's difference marks the rows it keeps with. -/
theorem AggQueryIn.exists_basisDiffOps_plainEquiv {sch : Schema} {n : ℕ}
    {κ : Fin n → ColKind} (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps)
    (hd : q.WinsDerivable) (hqs : q.overSchema sch) (hqn : q.NoAggTerm) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.usesOnly basisDiffOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  obtain ⟨q₃, hu₃, hs₃, hn₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_plainEquiv_noAggTerm f hzero q hq hd hqs
  obtain ⟨q₄, hu₄, hs₄, hw₄, he₄⟩ :=
    AggQueryIn.exists_allReg (S := basisOps) (sch := sch) q₃ hu₃
      (AggQueryIn.retypable_of_noAggTerm (by simp [basisOps]) q₃ hu₃
        (hn₃ hqn)) hs₃
  obtain ⟨q₅, hu₅, hs₅, -, he₅⟩ :=
    AggQueryIn.exists_selFree (S := basisDiffOps) (by simp [basisDiffOps])
      (by simp [basisDiffOps]) (by simp [basisDiffOps]) q₄ rfl
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
    {κ : Fin n → ColKind} (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) (q : AggQuery T n κ)
    (hq : q.usesOnly plainOps) (hd : q.WinsDerivable)
    (hqs : q.overSchema sch) (hqn : q.NoAggTerm) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.usesOnly basisApplyOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  obtain ⟨q₃, hu₃, hs₃, hn₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_plainEquiv_noAggTerm f hzero q hq hd hqs
  obtain ⟨q₄, hu₄, hs₄, hw₄, he₄⟩ :=
    AggQueryIn.exists_allReg (S := basisOps) (sch := sch) q₃ hu₃
      (AggQueryIn.retypable_of_noAggTerm (by simp [basisOps]) q₃ hu₃
        (hn₃ hqn)) hs₃
  obtain ⟨q₅, hu₅, hs₅, he₅⟩ :=
    AggQueryIn.exists_prodFree (S := basisApplyOps) (by simp [basisApplyOps])
      q₄ (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with h | h | h | h | h | h <;>
          simp [basisApplyOps, h]) q₄ hu₄) hw₄ hs₄
  exact ⟨q₅, hu₅, hs₅,
    fun D γ => ((he₃ D γ).trans (he₄ D γ)).trans (he₅ D γ)⟩

/-- **`{∅, Π, ×, ⊎, γ, −}` generates, over a schema.** -/
theorem basisDiffOps_generatesOn (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) (sch : Schema) :
    GeneratesOn T sch basisDiffOps :=
  fun q hqs hq hd hqn => by
    obtain ⟨q', hu', hs', he'⟩ :=
      AggQueryIn.exists_basisDiffOps_plainEquiv f hzero q hq hd hqs hqn
    exact ⟨q', hs', hu', he'⟩

/-- **`{∅, Π, σ, apply, ⊎, γ}` generates, over a schema.** -/
theorem basisApplyOps_generatesOn (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) (sch : Schema) :
    GeneratesOn T sch basisApplyOps :=
  fun q hqs hq hd hqn => by
    obtain ⟨q', hu', hs', he'⟩ :=
      AggQueryIn.exists_basisApplyOps_plainEquiv f hzero q hq hd hqs hqn
    exact ⟨q', hs', hu', he'⟩

/-- Over `ℕ`, with the tag `1`, the sum, and `1` as the selection's
marker. -/
theorem basisDiffOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisDiffOps :=
  basisDiffOps_generatesOn List.sum (fun _ => List.sum_eq_zero_iff) sch

/-- Over `ℕ`, with the tag `1` and the sum. -/
theorem basisApplyOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisApplyOps :=
  basisApplyOps_generatesOn List.sum (fun _ => List.sum_eq_zero_iff) sch

/-! ## Three windows that are derivable

`AggQueryIn.WinsDerivable` asks of a window a predicate of the language
holding where its frame condition holds and its `FILTER` clause keeps the
row. These are the three frames of `sec:basis`'s `prop:winderived` for
which `Provenance.PlainBasis` builds that predicate: the whole
partition, which asks nothing of the domain, and the two `RANGE` frames
read against the clause, which ask that nothing be null – the predicate
language has comparisons and `IS NOT DISTINCT FROM` but no `IS NULL`
atom, so the null branches of `OrderCol.le` have no reading there. Each
takes any `DISTINCT` and any clause. -/

/-- **A window over the whole partition is derivable.** -/
theorem AggQueryIn.winsDerivable_win_whole {c n m p : ℕ} (P : Tuple (Fin n) m)
    (O : Tuple (Fin n) p) (o : OrderSpec p) (t : TermIn T c n)
    (f : SeqAggFunc T) {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o ValueFrame.whole t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.containsSelf_whole,
    exists_framePred_whole O keep, hq⟩

/-- **And one over `RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW`**,
where nothing is null. -/
theorem AggQueryIn.winsDerivable_win_rangeUpTo [NoNulls T] {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : TermIn T c n) (f : SeqAggFunc T)
    {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o (ValueFrame.rangeUpTo o) t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.rangeUpTo_containsSelf o,
    exists_framePred_rangeUpTo O o keep, hq⟩

/-- **And one over the same frame excluding the current row's peers**
(`EXCLUDE GROUP`), which is what a running total that must not read its
own row needs. -/
theorem AggQueryIn.winsDerivable_win_rangeBefore [NoNulls T] {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : TermIn T c n) (f : SeqAggFunc T)
    {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o (ValueFrame.rangeBefore o) t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.rangeBefore_containsSelf o,
    exists_framePred_rangeBefore O o keep, hq⟩

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
    {κ : Fin n → ColKind} (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0)
    (q : AggQuery T n κ) (hq : q.usesOnly plainOps)
    (hd : q.WinsDerivable) (hqs : q.overSchema sch) (hqn : q.NoAggTerm) :
    ∃ q' : AggQuery T n (ColKind.allReg n),
      q'.usesOnly basisApplyDiffOps ∧ q'.overSchema sch ∧ q.PlainEquiv q' := by
  obtain ⟨q₃, hu₃, hs₃, hn₃, he₃⟩ :=
    AggQueryIn.exists_basisOps_plainEquiv_noAggTerm f hzero q hq hd hqs
  obtain ⟨q₄, hu₄, hs₄, hw₄, he₄⟩ :=
    AggQueryIn.exists_allReg (S := basisOps) (sch := sch) q₃ hu₃
      (AggQueryIn.retypable_of_noAggTerm (by simp [basisOps]) q₃ hu₃
        (hn₃ hqn)) hs₃
  -- the selections become differences, and what is left is still ready
  -- for the product swap
  obtain ⟨q₅, hu₅, hs₅, hw₅, he₅⟩ :=
    AggQueryIn.exists_selFree (S := basisDiffOps) (by simp [basisDiffOps])
      (by simp [basisDiffOps]) (by simp [basisDiffOps]) q₄ rfl
      (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with h | h | h | h | h | h <;>
          simp [basisDiffOps, h]) q₄ hu₄) hw₄ hs₄
  -- and then the products become applies
  obtain ⟨q₆, hu₆, hs₆, he₆⟩ :=
    AggQueryIn.exists_prodFree (S := basisApplyDiffOps)
      (by simp [basisApplyDiffOps]) q₅ (AggQueryIn.usesOnly_mono (by
        intro k hk
        simp only [basisDiffOps, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hk
        rcases hk with h | h | h | h | h | h <;>
          simp [basisApplyDiffOps, h]) q₅ hu₅) hw₅ hs₅
  exact ⟨q₆, hu₆, hs₆, fun D γ =>
    (((he₃ D γ).trans (he₄ D γ)).trans (he₅ D γ)).trans (he₆ D γ)⟩

/-- **`{∅, Π, apply, ⊎, γ, −}` generates, over a schema.** -/
theorem basisApplyDiffOps_generatesOn (f : SeqAggFunc T)
    (hzero : ∀ l : List T, f l = 0 ↔ ∀ x ∈ l, x = 0) (sch : Schema) :
    GeneratesOn T sch basisApplyDiffOps :=
  fun q hqs hq hd hqn => by
    obtain ⟨q', hu', hs', he'⟩ :=
      AggQueryIn.exists_basisApplyDiffOps_plainEquiv f hzero q hq hd hqs hqn
    exact ⟨q', hs', hu', he'⟩

/-- Over `ℕ`, with the tag `1`, the sum and the marker `1`. -/
theorem basisApplyDiffOps_generatesOn_nat (sch : Schema) :
    GeneratesOn ℕ sch basisApplyDiffOps :=
  basisApplyDiffOps_generatesOn List.sum (fun _ => List.sum_eq_zero_iff) sch

/-- **The two `RANGE` frames over a domain that names its null**: the
same windows as `AggQueryIn.winsDerivable_win_rangeUpTo` and
`_rangeBefore`, with the clause's null placement read by `IS NOT
DISTINCT FROM ν` tests instead of a domain without nulls. `ν` is asked
to be a null and the only one, which is SQL's `NULL`. -/
theorem AggQueryIn.winsDerivable_win_rangeUpTo_of_null {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : TermIn T c n) (f : SeqAggFunc T)
    {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) {ν : T}
    (hν : ValueType.isNull ν = true)
    (hνu : ∀ a : T, ValueType.isNull a = true → a = ν) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o (ValueFrame.rangeUpTo o) t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.rangeUpTo_containsSelf o,
    exists_framePred_rangeUpTo_of_null O o keep hν hνu, hq⟩

/-- And the same without the current row's peers. -/
theorem AggQueryIn.winsDerivable_win_rangeBefore_of_null {c n m p : ℕ}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (t : TermIn T c n) (f : SeqAggFunc T)
    {q : AggQueryIn T c n (ColKind.allReg n)} (dist : Bool)
    (keep : Option (Selection T n)) {ν : T}
    (hν : ValueType.isNull ν = true)
    (hνu : ∀ a : T, ValueType.isNull a = true → a = ν) (hq : q.WinsDerivable) :
    (AggQueryIn.Win P O o (ValueFrame.rangeBefore o) t f q
      (winReadsReg_allReg P O t) dist keep).WinsDerivable :=
  ⟨fun _ => rfl, ValueFrame.rangeBefore_containsSelf o,
    exists_framePred_rangeBefore_of_null O o keep hν hνu, hq⟩
