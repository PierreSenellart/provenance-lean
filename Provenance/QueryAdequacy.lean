import Provenance.QueryAnnotatedDatabase
import Provenance.QueryRewriting
import Provenance.Semirings.Nat

/-!
# Data-part adequacy of the annotated semantics

This file relates the annotated semantics `Query.evaluateAnnotated` to the
plain semantics `Query.evaluate`, on the *data parts*: what happens when all
annotations are forgotten.

For the positive (`Diff`-free) fragment the two semantics agree exactly, for
*any* m-semiring `K` (`Query.evaluateAnnotated_toPlain_of_noDiff`). This is
the counterpart, in the copies-as-elements encoding of annotated relations
used here, of the `ℕ`-adequacy theorem of [Benzaken, Cohen-Boulakia,
Contejean, Keller & Zucchini, *A Coq formalization of data
provenance*][benzaken2021coq]: in their function-with-support encoding of
K-relations, tuple multiplicities must be carried by the annotations, so
adequacy is a statement about `K = ℕ`; here multiplicities are carried by the
multiset structure itself and the data-part statement is annotation-generic.

In the presence of difference the exact correspondence breaks down –
necessarily so: over `ℕ`, monus-based difference and the all-or-nothing
plain difference genuinely disagree once duplicate elimination has
accumulated annotations (`Nat.counterexample_diff_adequacy`, at the end of
this file). What survives is:

* an *equality with the stripped query* (`Query.evaluateAnnotated_toPlain`):
  the data part of the annotated result is the plain evaluation of the query
  obtained by replacing every `Diff q₁ q₂` with `q₁` (`Query.stripDiff`).
  This makes precise that the annotated `Diff` never removes tuple slots; it
  only rewrites annotations (possibly to `0`), faithfully to ProvSQL, where
  rows are never deleted by difference at the provenance level;
* an *inclusion* (`Query.evaluate_toPlain_le_evaluateAnnotated`): the plain
  evaluation is a sub-multiset of the data part of the annotated evaluation,
  since plain evaluation is monotone under stripping differences
  (`Query.evaluate_le_stripDiff`).

The inclusion cannot be strengthened to an equality on the tuples with
*non-zero* annotation: nesting differences makes the support of the
annotated result both under- and over-approximate the plain result.

## Main definitions

* `Query.stripDiff` – replace every `Diff q₁ q₂` node with `q₁`
* `Query.noDiff` – the `Diff`-free predicate on queries (mirroring
  `Query.noAgg`)
* `AnnotatedRelation.toPlain`, `AnnotatedDatabase.toPlain` – forget the
  annotations

## Main results

* `Query.evaluateAnnotated_toPlain` – data-part equality with the stripped
  query, for any m-semiring `K`
* `Query.evaluate_le_stripDiff` – plain evaluation is monotone under
  stripping differences
* `Query.evaluate_toPlain_le_evaluateAnnotated` – the data-part inclusion
* `Query.evaluateAnnotated_toPlain_of_noDiff` – data-part adequacy for the
  positive fragment

## References

* [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini, *A Coq
  formalization of data provenance*][benzaken2021coq]
* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]
-/

variable {T : Type} {K : Type}

/-- Replace every difference node `Diff q₁ q₂` of a query with its left
argument `q₁`, recursively. Since the annotated semantics of `Diff` keeps
every tuple slot of its left argument (only annotations change), the data
part of the annotated evaluation of `q` is the plain evaluation of
`q.stripDiff` (see `Query.evaluateAnnotated_toPlain`). -/
def Query.stripDiff : Query T n → Query T n
| Rel n s => Rel n s
| Proj ts q => Proj ts q.stripDiff
| Sel φ q => Sel φ q.stripDiff
| @Prod _ n₁ n₂ n hn q₁ q₂ => @Prod T n₁ n₂ n hn q₁.stripDiff q₂.stripDiff
| Sum q₁ q₂ => Sum q₁.stripDiff q₂.stripDiff
| Dedup q => Dedup q.stripDiff
| Diff q₁ _ => q₁.stripDiff
| Agg is ts as q => Agg is ts as q.stripDiff

/-- The `Diff`-free (positive) fragment of the relational algebra, mirroring
`Query.noAgg`. -/
def Query.noDiff (q: Query T n): Prop := match q with
| Rel _ _ => True
| Proj _ q => q.noDiff
| Sel _ q => q.noDiff
| Prod q₁ q₂ => q₁.noDiff ∧ q₂.noDiff
| Sum q₁ q₂ => q₁.noDiff ∧ q₂.noDiff
| Dedup q => q.noDiff
| Diff _ _ => False
| Agg _ _ _ q => q.noDiff

/-- On `Diff`-free queries, `Query.stripDiff` is the identity. -/
theorem Query.stripDiff_of_noDiff (q: Query T n) (hd: q.noDiff) :
    q.stripDiff = q := by
  induction q with
  | Rel n s => rfl
  | Proj ts q ih =>
    simp only [noDiff] at hd
    simp only [stripDiff, ih hd]
  | Sel φ q ih =>
    simp only [noDiff] at hd
    simp only [stripDiff, ih hd]
  | Prod q₁ q₂ ih₁ ih₂ =>
    simp only [noDiff] at hd
    simp only [stripDiff, ih₁ hd.left, ih₂ hd.right]
  | Sum q₁ q₂ ih₁ ih₂ =>
    simp only [noDiff] at hd
    simp only [stripDiff, ih₁ hd.left, ih₂ hd.right]
  | Dedup q ih =>
    simp only [noDiff] at hd
    simp only [stripDiff, ih hd]
  | Diff q₁ q₂ ih₁ ih₂ =>
    simp only [noDiff] at hd
  | Agg is ts as q ih =>
    simp only [noDiff] at hd
    simp only [stripDiff, ih hd]

/-- Forget the annotations of an annotated relation, keeping one tuple slot
per annotated tuple (including slots whose annotation is `0`). The return
type is a bare `Multiset (Tuple T n)` so that `Multiset` lemmas apply without
an extra unfolding step. -/
def AnnotatedRelation.toPlain [Zero K] (r: AnnotatedRelation T K n) :
    Multiset (Tuple T n) :=
  Multiset.map Prod.fst r

/-- Forget the annotations of an annotated database, relation by relation. -/
def AnnotatedDatabase.toPlain [Zero K] (d: AnnotatedDatabase T K) : Database T :=
  d.map (fun e => (e.fst, ⟨e.snd.fst, e.snd.snd.toPlain⟩))

lemma AnnotatedDatabase.find_toPlain [Zero K]
    (n : ℕ) (s : String) (d : AnnotatedDatabase T K) :
    (d.toPlain).find n s = (d.find n s).map AnnotatedRelation.toPlain := by
  induction d with
  | nil => rfl
  | cons hd tl ih =>
    unfold AnnotatedDatabase.toPlain AnnotatedDatabase.find AnnotatedDatabase.find.f
            Database.find Database.find.f
    by_cases hcond : n = hd.snd.fst ∧ s = hd.fst
    · simp [hcond]
      have := hcond.left; subst this
      rfl
    · simp [hcond]
      unfold AnnotatedDatabase.toPlain AnnotatedDatabase.find at ih
      exact ih

/-! ### Helper lemmas: `Multiset.map Prod.fst` commutes with the operators

All helpers are stated on bare `Multiset (α × β)` carriers, so that applying
them by `exact` (full-transparency unification) sees through the
`AnnotatedRelation` / `×ₗ` type synonyms in the goals. -/

private lemma map_fst_map_data {α β γ : Type} (f : α → γ) (r : Multiset (α × β)) :
    Multiset.map Prod.fst (Multiset.map (fun p : α × β => (f p.1, p.2)) r)
      = Multiset.map f (Multiset.map Prod.fst r) := by
  induction r using Multiset.induction_on with
  | empty => rfl
  | cons p s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, ih]

private lemma map_fst_filter_data {α β : Type} (φ : α → Prop)
    (instφ : DecidablePred φ)
    (inst : DecidablePred fun p : α × β => φ p.1) (r : Multiset (α × β)) :
    Multiset.map Prod.fst (@Multiset.filter _ _ inst r)
      = @Multiset.filter _ φ instφ (Multiset.map Prod.fst r) := by
  induction r using Multiset.induction_on with
  | empty => rfl
  | cons p s ih =>
    by_cases hp : φ p.1
    · rw [Multiset.filter_cons_of_pos (p := fun p : α × β => φ p.1) _ hp,
          Multiset.map_cons, Multiset.map_cons,
          Multiset.filter_cons_of_pos (p := φ) _ hp, ih]
    · rw [Multiset.filter_cons_of_neg (p := fun p : α × β => φ p.1) _ hp,
          Multiset.map_cons,
          Multiset.filter_cons_of_neg (p := φ) _ hp, ih]

private lemma map_fst_map_sub {α β : Type} [Sub β] (g : α → β) (r : Multiset (α × β)) :
    Multiset.map Prod.fst (Multiset.map (fun p : α × β => (p.1, p.2 - g p.1)) r)
      = Multiset.map Prod.fst r := by
  induction r using Multiset.induction_on with
  | empty => rfl
  | cons p s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, ih]

private lemma product_map_fst {α₁ α₂ β : Type} [Mul β] {γ : Type}
    (h : α₁ → α₂ → γ)
    (r₁ : Multiset (α₁ × β)) (r₂ : Multiset (α₂ × β)) :
    Multiset.map Prod.fst
      (Multiset.map (fun x : (α₁ × β) × (α₂ × β) => (h x.1.1 x.2.1, x.1.2 * x.2.2))
        (Multiset.product r₁ r₂))
    = Multiset.map (fun x : α₁ × α₂ => h x.1 x.2)
        (Multiset.product (Multiset.map Prod.fst r₁) (Multiset.map Prod.fst r₂)) := by
  unfold Multiset.product
  rw [Multiset.map_map, Multiset.bind_map, Multiset.map_bind, Multiset.map_bind]
  apply Multiset.bind_congr
  intro p _
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  rfl

/-- `Multiset.product` is monotone in both arguments. -/
private lemma product_le_product {α β : Type} {a a' : Multiset α} {b b' : Multiset β}
    (h₁ : a ≤ a') (h₂ : b ≤ b') :
    Multiset.product a b ≤ Multiset.product a' b' := by
  obtain ⟨u₁, rfl⟩ := Multiset.le_iff_exists_add.mp h₁
  obtain ⟨u₂, rfl⟩ := Multiset.le_iff_exists_add.mp h₂
  show a ×ˢ b ≤ (a + u₁) ×ˢ (b + u₂)
  rw [Multiset.add_product, Multiset.product_add]
  exact le_trans (Multiset.le_iff_exists_add.mpr ⟨a ×ˢ u₂, rfl⟩)
    (Multiset.le_iff_exists_add.mpr ⟨u₁ ×ˢ (b + u₂), rfl⟩)

variable [ValueType T] [SemiringWithMonus K] [DecidableEq K]

/-- **Data-part equality.** For any non-aggregation query `q` over any
m-semiring `K`, forgetting the annotations of the annotated evaluation of
`q` yields the plain evaluation of the *stripped* query `q.stripDiff` on the
plain database: annotated `Diff` never removes tuple slots, so all the
differences disappear from the data part. -/
theorem Query.evaluateAnnotated_toPlain :
    ∀ {n} (q: Query T n) (hq: q.noAgg) (d: AnnotatedDatabase T K),
    (q.evaluateAnnotated hq d).toPlain = (q.stripDiff).evaluate d.toPlain := by
  intro n q
  induction q with
  | Rel n s =>
    intro hq d
    simp only [Query.evaluateAnnotated, Query.evaluate, Query.stripDiff]
    rw [AnnotatedDatabase.find_toPlain]
    cases hf : d.find n s
    · rfl
    · simp
  | Proj ts q' ih =>
    intro hq d
    simp only [Query.evaluateAnnotated, Query.evaluate, Query.stripDiff]
    rw [← ih (Query.noAggProj hq rfl) d]
    exact map_fst_map_data (fun u => (fun k => (ts k).eval u)) _
  | Sel φ q' ih =>
    intro hq d
    simp only [Query.evaluateAnnotated, Query.evaluate, Query.stripDiff]
    rw [← ih (Query.noAggSel hq rfl) d]
    have hinst : φ.evalDecidableAnnotated
        = (fun ta : AnnotatedTuple T K _ => φ.evalDecidable ta.fst) :=
      Subsingleton.elim _ _
    rw [hinst]
    exact map_fst_filter_data φ.eval φ.evalDecidable
      (fun ta => φ.evalDecidable ta.1)
      (q'.evaluateAnnotated (Query.noAggSel hq rfl) d)
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    intro hq d
    subst hn
    simp only [Query.evaluateAnnotated, Query.evaluate, Query.stripDiff]
    rw [← ih₁ (Query.noAggProd hq rfl).left d, ← ih₂ (Query.noAggProd hq rfl).right d]
    exact product_map_fst (fun x y => Fin.append x y) _ _
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq d
    simp only [Query.evaluateAnnotated, Query.evaluate, Query.stripDiff]
    rw [← ih₁ (Query.noAggSum hq rfl).left d, ← ih₂ (Query.noAggSum hq rfl).right d]
    exact Multiset.map_add _ _ _
  | Dedup q' ih =>
    intro hq d
    simp only [Query.evaluateAnnotated, Query.evaluate, Query.stripDiff]
    rw [← ih (Query.noAggDedup hq rfl) d]
    set r := q'.evaluateAnnotated (Query.noAggDedup hq rfl) d with hr
    -- Both sides are `Nodup`; equality follows from membership equivalence,
    -- which is `groupByKey_key_iff`.
    have hL : (AnnotatedRelation.toPlain (Multiset.ofList (groupByKey r).val)).Nodup := by
      show (Multiset.map Prod.fst (Multiset.ofList (groupByKey r).val)).Nodup
      apply Multiset.Nodup.map_on
      · intro p hp q hq hpq
        have hp' : p ∈ (groupByKey r).val := Multiset.mem_coe.mp hp
        have hq' : q ∈ (groupByKey r).val := Multiset.mem_coe.mp hq
        exact Prod.ext hpq
          (KeyValueList.functional _ (groupByKey r).property p hp' q hq' hpq)
      · rw [Multiset.coe_nodup]
        exact KeyValueList.nodup _ (groupByKey r).property
    have hR : (Multiset.dedup (AnnotatedRelation.toPlain r)).Nodup :=
      Multiset.nodup_dedup _
    rw [Multiset.Nodup.ext hL hR]
    intro t
    constructor
    · intro ht
      have ht' : t ∈ Multiset.map Prod.fst (Multiset.ofList (groupByKey r).val) := ht
      rw [Multiset.mem_map] at ht'
      obtain ⟨p, hp, hfst⟩ := ht'
      show t ∈ Multiset.dedup (AnnotatedRelation.toPlain r)
      rw [Multiset.mem_dedup]
      show t ∈ Multiset.map Prod.fst r
      rw [← hfst]
      exact (groupByKey_key_iff r p.fst).mp ⟨p.snd, Multiset.mem_coe.mp hp⟩
    · intro ht
      have ht' : t ∈ Multiset.map Prod.fst r := Multiset.mem_dedup.mp ht
      obtain ⟨w, hw⟩ := (groupByKey_key_iff r t).mpr ht'
      show t ∈ Multiset.map Prod.fst (Multiset.ofList (groupByKey r).val)
      rw [Multiset.mem_map]
      exact ⟨(t, w), Multiset.mem_coe.mpr hw, rfl⟩
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq d
    simp only [Query.evaluateAnnotated, Query.stripDiff]
    rw [← ih₁ (Query.noAggDiff hq rfl).left d]
    exact map_fst_map_sub
      (fun u => ((((groupByKey
          (q₂.evaluateAnnotated (Query.noAggDiff hq rfl).right d)).val.find?
        (·.1 = u)).map Prod.snd).getD 0)) _
  | Agg is ts as q' ih =>
    intro hq d
    simp [Query.noAgg] at hq

/-- Plain evaluation is monotone (in the sub-multiset order) under stripping
differences: the plain `Diff` is a `filter` of its left argument, and every
other operator is monotone. -/
theorem Query.evaluate_le_stripDiff :
    ∀ {n} (q: Query T n), q.noAgg → ∀ (d: Database T),
    @LE.le (Multiset (Tuple T n)) _ (q.evaluate d) ((q.stripDiff).evaluate d) := by
  intro n q
  induction q with
  | Rel n s =>
    intro hq d
    exact le_refl _
  | Proj ts q' ih =>
    intro hq d
    simp only [Query.evaluate, Query.stripDiff]
    exact Multiset.map_le_map (ih (Query.noAggProj hq rfl) d)
  | Sel φ q' ih =>
    intro hq d
    simp only [Query.evaluate, Query.stripDiff]
    exact @Multiset.filter_le_filter _ φ.eval φ.evalDecidable _ _
      (ih (Query.noAggSel hq rfl) d)
  | @Prod n₁ n₂ n hn q₁ q₂ ih₁ ih₂ =>
    intro hq d
    subst hn
    simp only [Query.evaluate, Query.stripDiff]
    have h₁ := ih₁ (Query.noAggProd hq rfl).left d
    have h₂ := ih₂ (Query.noAggProd hq rfl).right d
    show Multiset.map (fun x : Tuple T n₁ × Tuple T n₂ => Fin.append x.1 x.2)
        (Multiset.product (q₁.evaluate d) (q₂.evaluate d))
      ≤ Multiset.map (fun x : Tuple T n₁ × Tuple T n₂ => Fin.append x.1 x.2)
        (Multiset.product (q₁.stripDiff.evaluate d) (q₂.stripDiff.evaluate d))
    exact Multiset.map_le_map (product_le_product h₁ h₂)
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq d
    simp only [Query.evaluate, Query.stripDiff]
    exact le_trans
      (Multiset.add_le_add_left (ih₂ (Query.noAggSum hq rfl).right d))
      (Multiset.add_le_add_right (ih₁ (Query.noAggSum hq rfl).left d))
  | Dedup q' ih =>
    intro hq d
    simp only [Query.evaluate, Query.stripDiff]
    have h := ih (Query.noAggDedup hq rfl) d
    exact (Multiset.le_iff_subset (Multiset.nodup_dedup _)).mpr
      (fun t ht => Multiset.mem_dedup.mpr
        (Multiset.mem_of_le h (Multiset.mem_dedup.mp ht)))
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq d
    simp only [Query.evaluate, Query.stripDiff]
    exact le_trans (Multiset.filter_le _ _) (ih₁ (Query.noAggDiff hq rfl).left d)
  | Agg is ts as q' ih =>
    intro hq d
    simp [Query.noAgg] at hq

/-- **Data-part inclusion.** The plain evaluation of `q` on the underlying
plain database is a sub-multiset of the data part of the annotated
evaluation: annotated evaluation never loses tuple slots, it only zeroes
annotations. The inclusion is strict in general (`Diff` slots whose
annotation was zeroed remain on the right), and it cannot be strengthened to
an equality on non-zero-annotated slots (see
`Nat.counterexample_diff_adequacy`). -/
theorem Query.evaluate_toPlain_le_evaluateAnnotated
    (q: Query T n) (hq: q.noAgg) (d: AnnotatedDatabase T K) :
    @LE.le (Multiset (Tuple T n)) _ (q.evaluate d.toPlain)
      ((q.evaluateAnnotated hq d).toPlain) := by
  rw [Query.evaluateAnnotated_toPlain q hq d]
  exact Query.evaluate_le_stripDiff q hq d.toPlain

/-- **Data-part adequacy for the positive fragment.** On `Diff`-free (and
aggregation-free) queries, the annotated semantics computes exactly the
plain semantics on the data parts, for *any* m-semiring `K`. In the
copies-as-elements encoding this is the analogue of the `K = ℕ` adequacy
theorem of [Benzaken, Cohen-Boulakia, Contejean, Keller &
Zucchini][benzaken2021coq] (there, multiplicities live in the annotations,
so the statement is `ℕ`-specific; here they live in the multiset). -/
theorem Query.evaluateAnnotated_toPlain_of_noDiff
    (q: Query T n) (hq: q.noAgg) (hd: q.noDiff) (d: AnnotatedDatabase T K) :
    (q.evaluateAnnotated hq d).toPlain = q.evaluate d.toPlain := by
  rw [Query.evaluateAnnotated_toPlain q hq d, Query.stripDiff_of_noDiff q hd]

/-! ### `ℕ`-adequacy genuinely fails beyond the positive fragment

The following counterexample shows that
`Query.evaluateAnnotated_toPlain_of_noDiff` cannot be extended to queries
with difference, not even on the tuples with non-zero annotation: over
`K = ℕ` with all base annotations `1`, the query `(δ R₁) ∖ R₂` on
`R₁ = {t, t}`, `R₂ = {t}` keeps `t` with annotation `2 ∸ 1 = 1` in the
annotated semantics, while the plain semantics removes it. The `Dedup` is
essential: it accumulates the annotation `2`, which the monus difference
then decrements instead of zeroing. This is why the `ℕ`-adequacy theorem
of [Benzaken, Cohen-Boulakia, Contejean, Keller &
Zucchini][benzaken2021coq] is necessarily restricted to the positive
fragment. -/

/-- Natural numbers as a value type (used for kernel-computable
counterexamples: unlike `String`, the order on `ℕ` reduces by `decide`). -/
instance : ValueType ℕ where

/-- Over `ℕ`, the non-zero-annotated support of the annotated evaluation
differs from the plain evaluation on a query combining `Dedup` and `Diff`:
`ℕ`-adequacy stops at the positive fragment. -/
theorem Nat.counterexample_diff_adequacy :
    let t : Tuple ℕ 1 := ![0]
    let r₁ : AnnotatedRelation ℕ ℕ 1 := Multiset.ofList [(t, 1), (t, 1)]
    let r₂ : AnnotatedRelation ℕ ℕ 1 := Multiset.ofList [(t, 1)]
    let d : AnnotatedDatabase ℕ ℕ := [("R1", ⟨1, r₁⟩), ("R2", ⟨1, r₂⟩)]
    let q : Query ℕ 1 :=
      Query.Diff (Query.Dedup (Query.Rel 1 "R1")) (Query.Rel 1 "R2")
    ∃ hq : q.noAgg,
      Multiset.map Prod.fst
          (Multiset.filter (fun p : AnnotatedTuple ℕ ℕ 1 => p.snd ≠ 0)
            (q.evaluateAnnotated hq d))
        ≠ q.evaluate d.toPlain := by
  intro t r₁ r₂ d q
  refine ⟨by decide, ?_⟩
  simp only [q, d, r₁, r₂, t, Query.evaluateAnnotated, Query.evaluate]
  decide
