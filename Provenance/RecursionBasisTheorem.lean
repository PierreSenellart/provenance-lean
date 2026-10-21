module

public import Provenance.MuUnion
public import Mathlib.Order.BourbakiWitt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Provenance.WinRow

/-!
# The bases of the whole algebra in the minimal universe

The classification of the whole algebra (recursions and windows
included) in the minimal universe `𝒜(∅, {count})`, in one place: the
classes every generating set contains, read off the necessity rows
(`Provenance.RecursionBasis`, `Provenance.WinRow`), and the set that
generates (`Provenance.MuUnion`). `basisRecOps` = `{∅, Π, σ, apply, γ,
win, μ^⊎}` is a basis: it generates over every schema, and no proper
subset does. The bases are not all of its shape: `−` for `σ` and `×`
for the apply are the two alternatives the rows leave open, and each gives
a basis too (`basisRecDiffOps_isBasis`, in `Provenance.DiffBasis`, and
`Sym.basisProdOps_isBasis`, in `Provenance.SymPass`). The two together,
`{∅, Π, −, ×, γ, win, μ^⊎}`, do not generate it: `σ` or the apply is in
every basis, and the generating sets are exactly the supersets of the three
bases (`generatesOnRec_iff`, in `Provenance.RecursionBases`).
-/

@[expose] public section

variable {T : Type} [ValueType T]

/-- **Every set of classes holding the basis generates the whole
algebra**, over every schema and for every counting aggregate. -/
theorem generatesOnRec_of_basisRecOps_subset (sch : Schema) (cnt : SeqAggFunc T)
    (hcnt : cnt.IsCount) {S : Set OpKind} (hS : basisRecOps ⊆ S) :
    GeneratesOnRec T sch cnt S :=
  GeneratesOnRec.mono hS (basisRecOps_generatesOnRec sch cnt hcnt)

/-- **What every generating set contains**: a set of classes generating
the whole algebra over `ℕ` with the counting aggregate, over every
schema, holds `∅`, `Π`, `γ`, `μ^⊎` and `win`, one of `σ` and `−`, and one
of `×` and the apply. Each conjunct is witnessed over its own schema. -/
theorem required_mem_of_generatesOnRec {S : Set OpKind}
    (hS : ∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S) :
    OpKind.empty ∈ S ∧ OpKind.proj ∈ S ∧ OpKind.gamma ∈ S ∧ OpKind.muBag ∈ S
      ∧ OpKind.win ∈ S ∧ (OpKind.sel ∈ S ∨ OpKind.diff ∈ S)
      ∧ (OpKind.prod ∈ S ∨ OpKind.apply ∈ S) :=
  ⟨empty_mem_of_generatesOnRec (hS _), proj_mem_of_generatesOnRec (hS _),
    gamma_mem_of_generatesOnRec (hS Schema.empty),
    muBag_mem_of_generatesOnRec SeqAggFunc.isCount_count_nat.readsCount (hS _),
    win_mem_of_generatesOnRec (hS _), sel_or_diff_mem_of_generatesOnRec (hS _),
    prod_or_apply_mem_of_generatesOnRec (hS _)⟩

/-- **No proper subset of the basis generates**: dropping any of its
seven classes loses one of the required ones – `σ` with no `−` in the
set, the apply with no `×`. -/
theorem basisRecOps_minimal {S : Set OpKind} (hS : S ⊂ basisRecOps) :
    ¬ ∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S := by
  intro hgen
  obtain ⟨he, hp, hg, hm, hwin, hs, ha⟩ := required_mem_of_generatesOnRec hgen
  obtain ⟨x, hx, hxS⟩ := Set.exists_of_ssubset hS
  have hsub := hS.subset
  have hdiff : OpKind.diff ∉ S := fun h => by
    have := hsub h
    simp [basisRecOps, AggQueryIn.sumMuOps] at this
  have hprod : OpKind.prod ∉ S := fun h => by
    have := hsub h
    simp [basisRecOps, AggQueryIn.sumMuOps] at this
  simp only [basisRecOps, AggQueryIn.sumMuOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hxS hwin
  · exact hxS he
  · exact hxS hp
  · exact hxS (hs.resolve_right hdiff)
  · exact hxS (ha.resolve_left hprod)
  · exact hxS hg
  · exact hxS hm

/-- **`basisRecOps` is a basis of the whole algebra in the minimal
universe over `ℕ`**: it generates over every schema, and no proper
subset does. -/
theorem basisRecOps_isBasis :
    (∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count basisRecOps)
      ∧ ∀ S : Set OpKind, S ⊂ basisRecOps →
          ¬ ∀ sch : Schema, GeneratesOnRec ℕ sch SeqAggFunc.count S :=
  ⟨fun sch => basisRecOps_generatesOnRec sch _ SeqAggFunc.isCount_count_nat, fun _ hS => basisRecOps_minimal hS⟩
