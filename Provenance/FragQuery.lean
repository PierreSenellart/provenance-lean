/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Derived
public import Provenance.AggQueryAdequacy
public import Provenance.QueryToAgg
public import Provenance.DerivedAnn
import Mathlib.Tactic.Bound.Init
import all Provenance.AggQuery
import all Provenance.AggQueryAdequacy
import all Provenance.AggValue
import all Provenance.Database
import all Provenance.DerivedAnn
import all Provenance.HavingQueryCorrectness
import all Provenance.Nested
import all Provenance.QueryAnnotatedDatabaseHom

/-!
# The first levels of the chain of fragments, as a syntax of their own

The extensionality theorem of `Provenance.Extensionality` grades the
m-semirings along the first levels of the chain of SQL fragments of the
sql-semantics paper: `F₀` (projection, selection, product, apply, union,
the constant relations), `F₁` (`F₀` with duplicate elimination, `EXISTS`
and `IN`) and `F₂` (`F₁` with `EXCEPT`, `NOT EXISTS` and `NOT IN`); the
projections and selections carry the library's terms, so the level `F₃`
of the paper, which adds expressions, is `F₂` here as well. Each
construct of these levels is an operator of the kind-indexed syntax, or
a query it abbreviates (`Provenance.Derived`); but the levels are not
sets of operator classes – `EXISTS` is an apply, a scalar count and a
selection on an aggregate atom, which `AggQueryIn.usesOnly` charges to
three classes – so they are given here as a syntax of their own,
`FragQueryIn T c n`, with a translation `FragQueryIn.toAgg` into the
general syntax and the levels as predicates on it (`FragQueryIn.level0`,
`FragQueryIn.level1`; `F₂` is the whole syntax).

Every output column is regular, so the translation's annotated
evaluation produces plain annotated tuples, and the file gives it in
closed form: `FragQueryIn.sem` is the annotated semantics operator by
operator – multiset operations and the m-semiring's `⊕`, `⊗` and `⊖` – and
`FragQueryIn.toAgg_evaluateAnnotated` says the general evaluator computes
it. The same for the plain semantics, `FragQueryIn.semPlain` and
`FragQueryIn.toAgg_evaluatePlain`. The one closed form that costs a
hypothesis is the semijoin's, `α ⊗ ⊕β` in an absorptive m-semiring
(`AggValue.predProvScalar_count_ne_zero`), which is why the bridge asks
absorptivity of a query with a semijoin and nothing of the others.

An `EXISTS` or `IN` counts, in SQL's scalar convention, the rows of its
subquery that match the current row; the count is over a constant that is
not null (`ValueType.nonzero`), so that it is `𝟘` exactly where nothing
matches, and any aggregate that counts (`SeqAggFunc.Counts`) may do the
counting.
-/

@[expose] public section

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-- **The syntax of the first levels of the chain.** The context `c` is
the arity of the row an apply's right side reads, as in `AggQueryIn`;
every output column is regular. -/
inductive FragQueryIn (T : Type) [ValueType T] : ℕ → ℕ → Type where
  /-- A base relation. -/
  | Rel : {c : ℕ} → (n : ℕ) → String → FragQueryIn T c n
  /-- The empty relation of arity `0`. -/
  | Empty : {c : ℕ} → FragQueryIn T c 0
  /-- The unit: one empty tuple, annotated `𝟙`. A row of constants is a
  projection of it, and `VALUES` a union of such rows. -/
  | Unit : {c : ℕ} → FragQueryIn T c 0
  /-- Generalized projection, every column a term. -/
  | Proj : {c n m : ℕ} → (ts : Tuple (TermGIn T c (ColKind.allReg n)) m) →
      FragQueryIn T c n → FragQueryIn T c m
  /-- Selection by a predicate on regular columns. -/
  | Sel : {c n : ℕ} → (φ : GenPredIn T c (ColKind.allReg n)) →
      FragQueryIn T c n → FragQueryIn T c n
  /-- Cartesian product. -/
  | Prod : {c n₁ n₂ : ℕ} → FragQueryIn T c n₁ → FragQueryIn T c n₂ →
      FragQueryIn T c (n₁ + n₂)
  /-- Apply, SQL's `LATERAL`: the right side is read once per row of the
  left, in a context extended by that row. -/
  | Apply : {c n₁ n₂ : ℕ} → FragQueryIn T c n₁ → FragQueryIn T (n₁ + c) n₂ →
      FragQueryIn T c (n₁ + n₂)
  /-- Union (all). -/
  | Sum : {c n : ℕ} → FragQueryIn T c n → FragQueryIn T c n → FragQueryIn T c n
  /-- Duplicate elimination. -/
  | Dedup : {c n : ℕ} → FragQueryIn T c n → FragQueryIn T c n
  /-- Difference, `EXCEPT ALL`. -/
  | Diff : {c n : ℕ} → FragQueryIn T c n → FragQueryIn T c n → FragQueryIn T c n
  /-- Semijoin, `WHERE EXISTS` and `IN`: the rows of the left side that the
  predicate matches with some row of the right side, read in the context
  of the left row. The aggregate counts the matches. -/
  | Semijoin : {c k l : ℕ} → (cnt : SeqAggFunc T) → cnt.Counts →
      (φ : GenPredIn T (k + c) (ColKind.allReg l)) →
      FragQueryIn T c k → FragQueryIn T (k + c) l → FragQueryIn T c k
  /-- Antijoin, `WHERE NOT EXISTS` and `NOT IN`: the rows of the left side
  that the predicate matches with no row of the right side. -/
  | Antijoin : {c k l : ℕ} → (cnt : SeqAggFunc T) → cnt.Counts →
      (φ : GenPredIn T (k + c) (ColKind.allReg l)) →
      FragQueryIn T c k → FragQueryIn T (k + c) l → FragQueryIn T c k

/-- A closed query of the fragment syntax. -/
abbrev FragQuery (T : Type) [ValueType T] (n : ℕ) := FragQueryIn T 0 n

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
/-- **A predicate over regular columns has no aggregate atom**: an
aggregate atom names a column of aggregate kind, and there is none. -/
theorem GenPredIn.hasAggAtom_allReg {c n : ℕ} :
    ∀ φ : GenPredIn T c (ColKind.allReg n), φ.hasAggAtom = false
  | .cmp _ _ _ => rfl
  | .aggCmp _ h _ _ => ColKind.noConfusion h
  | .aggRange _ h _ _ _ _ => ColKind.noConfusion h
  | .and φ ψ => by
    show (φ.hasAggAtom || ψ.hasAggAtom) = false
    rw [GenPredIn.hasAggAtom_allReg φ, GenPredIn.hasAggAtom_allReg ψ]
    rfl
  | .or φ ψ => by
    show (φ.hasAggAtom || ψ.hasAggAtom) = false
    rw [GenPredIn.hasAggAtom_allReg φ, GenPredIn.hasAggAtom_allReg ψ]
    rfl
  | .not φ => GenPredIn.hasAggAtom_allReg φ

namespace FragQueryIn

/-! ## The levels -/

/-- **Level `F₀`**: no duplicate elimination, no difference, no semijoin
and no antijoin. -/
def level0 : {c n : ℕ} → FragQueryIn T c n → Prop
  | _, _, Rel _ _ => True
  | _, _, Empty => True
  | _, _, Unit => True
  | _, _, Proj _ q => q.level0
  | _, _, Sel _ q => q.level0
  | _, _, Prod q₁ q₂ => q₁.level0 ∧ q₂.level0
  | _, _, Apply q₁ q₂ => q₁.level0 ∧ q₂.level0
  | _, _, Sum q₁ q₂ => q₁.level0 ∧ q₂.level0
  | _, _, Dedup _ => False
  | _, _, Diff _ _ => False
  | _, _, Semijoin _ _ _ _ _ => False
  | _, _, Antijoin _ _ _ _ _ => False

/-- **Level `F₁`**: `F₀` with duplicate elimination and the semijoin, and
without the negated forms. -/
def level1 : {c n : ℕ} → FragQueryIn T c n → Prop
  | _, _, Rel _ _ => True
  | _, _, Empty => True
  | _, _, Unit => True
  | _, _, Proj _ q => q.level1
  | _, _, Sel _ q => q.level1
  | _, _, Prod q₁ q₂ => q₁.level1 ∧ q₂.level1
  | _, _, Apply q₁ q₂ => q₁.level1 ∧ q₂.level1
  | _, _, Sum q₁ q₂ => q₁.level1 ∧ q₂.level1
  | _, _, Dedup q => q.level1
  | _, _, Diff _ _ => False
  | _, _, Semijoin _ _ _ q₁ q₂ => q₁.level1 ∧ q₂.level1
  | _, _, Antijoin _ _ _ _ _ => False

/-- Whether a query has a semijoin somewhere: the one construct whose
closed form asks absorptivity of the m-semiring. -/
def hasSemijoin : {c n : ℕ} → FragQueryIn T c n → Prop
  | _, _, Rel _ _ => False
  | _, _, Empty => False
  | _, _, Unit => False
  | _, _, Proj _ q => q.hasSemijoin
  | _, _, Sel _ q => q.hasSemijoin
  | _, _, Prod q₁ q₂ => q₁.hasSemijoin ∨ q₂.hasSemijoin
  | _, _, Apply q₁ q₂ => q₁.hasSemijoin ∨ q₂.hasSemijoin
  | _, _, Sum q₁ q₂ => q₁.hasSemijoin ∨ q₂.hasSemijoin
  | _, _, Dedup q => q.hasSemijoin
  | _, _, Diff q₁ q₂ => q₁.hasSemijoin ∨ q₂.hasSemijoin
  | _, _, Semijoin _ _ _ _ _ => True
  | _, _, Antijoin _ _ _ q₁ q₂ => q₁.hasSemijoin ∨ q₂.hasSemijoin

/-- A query of `F₀` has no semijoin. -/
theorem not_hasSemijoin_of_level0 : ∀ {c n : ℕ} (q : FragQueryIn T c n),
    q.level0 → ¬ q.hasSemijoin
  | _, _, Rel _ _, _, h => h
  | _, _, Empty, _, h => h
  | _, _, Unit, _, h => h
  | _, _, Proj _ q, hq, h => not_hasSemijoin_of_level0 q hq h
  | _, _, Sel _ q, hq, h => not_hasSemijoin_of_level0 q hq h
  | _, _, Prod q₁ q₂, hq, h =>
    h.elim (not_hasSemijoin_of_level0 q₁ hq.1) (not_hasSemijoin_of_level0 q₂ hq.2)
  | _, _, Apply q₁ q₂, hq, h =>
    h.elim (not_hasSemijoin_of_level0 q₁ hq.1) (not_hasSemijoin_of_level0 q₂ hq.2)
  | _, _, Sum q₁ q₂, hq, h =>
    h.elim (not_hasSemijoin_of_level0 q₁ hq.1) (not_hasSemijoin_of_level0 q₂ hq.2)
  | _, _, Dedup _, hq, _ => hq.elim
  | _, _, Diff _ _, hq, _ => hq.elim
  | _, _, Semijoin _ _ _ _ _, hq, _ => hq.elim
  | _, _, Antijoin _ _ _ _ _, hq, _ => hq.elim

/-- `F₀ ⊆ F₁`. -/
theorem level1_of_level0 : ∀ {c n : ℕ} (q : FragQueryIn T c n), q.level0 → q.level1
  | _, _, Rel _ _, _ => trivial
  | _, _, Empty, _ => trivial
  | _, _, Unit, _ => trivial
  | _, _, Proj _ q, hq => level1_of_level0 q hq
  | _, _, Sel _ q, hq => level1_of_level0 q hq
  | _, _, Prod q₁ q₂, hq => ⟨level1_of_level0 q₁ hq.1, level1_of_level0 q₂ hq.2⟩
  | _, _, Apply q₁ q₂, hq => ⟨level1_of_level0 q₁ hq.1, level1_of_level0 q₂ hq.2⟩
  | _, _, Sum q₁ q₂, hq => ⟨level1_of_level0 q₁ hq.1, level1_of_level0 q₂ hq.2⟩
  | _, _, Dedup _, hq => hq.elim
  | _, _, Diff _ _, hq => hq.elim
  | _, _, Semijoin _ _ _ _ _, hq => hq.elim
  | _, _, Antijoin _ _ _ _ _, hq => hq.elim

/-! ## The two semantics, in closed form -/

/-- The rows of the right side of a semijoin that match a left row `u`:
the right side read in the context `u` extended by the outer one, cut by
the predicate. -/
noncomputable def matchesAnn {c k l : ℕ} (φ : GenPredIn T (k + c) (ColKind.allReg l))
    (S : AnnotatedDatabase T K → (Fin (k + c) → T) → AnnotatedRelation T K l)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (u : Tuple T k) :
    AnnotatedRelation T K l :=
  (S d (Fin.append u γ)).filter (fun p => φ.holdsPlain p.1 (Fin.append u γ))

/-- **The annotated semantics**, operator by operator. A duplicate
elimination sums the annotations of the copies of a tuple, a difference
subtracts from each copy on the left the sum of the copies on the right,
a semijoin multiplies each left row by the sum of the annotations of its
matches and an antijoin by `𝟙 ⊖` that sum. -/
noncomputable def sem : {c n : ℕ} → FragQueryIn T c n → AnnotatedDatabase T K →
    (Fin c → T) → AnnotatedRelation T K n
  | _, n, Rel _ s, d, _ => (d.find n s).getD (0 : Multiset (AnnotatedTuple T K n))
  | _, _, Empty, _, _ => (0 : Multiset (AnnotatedTuple T K 0))
  | _, _, Unit, _, _ => ({((fun j => j.elim0 : Tuple T 0), 1)} : Multiset (AnnotatedTuple T K 0))
  | _, _, Proj ts q, d, γ =>
    (q.sem d γ).map (fun p => ((fun j => (ts j).evalPlain p.1 γ, p.2) : AnnotatedTuple T K _))
  | _, _, Sel φ q, d, γ =>
    (q.sem d γ).filter (fun p : AnnotatedTuple T K _ => φ.holdsPlain p.1 γ)
  | _, _, Prod q₁ q₂, d, γ =>
    ((q₁.sem d γ).product (q₂.sem d γ)).map (fun xy =>
      ((Fin.append xy.1.1 xy.2.1, xy.1.2 * xy.2.2) : AnnotatedTuple T K _))
  | _, _, Apply q₁ q₂, d, γ =>
    (q₁.sem d γ).bind (fun x => (q₂.sem d (Fin.append x.1 γ)).map (fun y =>
      ((Fin.append x.1 y.1, x.2 * y.2) : AnnotatedTuple T K _)))
  | _, _, Sum q₁ q₂, d, γ => q₁.sem d γ + q₂.sem d γ
  | _, _, Dedup q, d, γ =>
    ((q.sem d γ).map Prod.fst).dedup.map (fun u =>
      ((u, AnnotatedRelation.annSum (q.sem d γ) u) : AnnotatedTuple T K _))
  | _, _, Diff q₁ q₂, d, γ =>
    (q₁.sem d γ).map (fun p =>
      ((p.1, p.2 - AnnotatedRelation.annSum (q₂.sem d γ) p.1) : AnnotatedTuple T K _))
  | _, _, Semijoin _ _ φ q₁ q₂, d, γ =>
    (q₁.sem d γ).map (fun p =>
      ((p.1, p.2 * AnnotatedRelation.annTotal (matchesAnn φ q₂.sem d γ p.1))
        : AnnotatedTuple T K _))
  | _, _, Antijoin _ _ φ q₁ q₂, d, γ =>
    (q₁.sem d γ).map (fun p =>
      ((p.1, p.2 * HSub.hSub (1 : K) (AnnotatedRelation.annTotal (matchesAnn φ q₂.sem d γ p.1)))
        : AnnotatedTuple T K _))

/-- The rows of the right side of a semijoin that match a left row, in
the plain semantics. -/
noncomputable def matchesPlain {c k l : ℕ} (φ : GenPredIn T (k + c) (ColKind.allReg l))
    (S : Database T → (Fin (k + c) → T) → Relation T l)
    (D : Database T) (γ : Fin c → T) (u : Tuple T k) : Relation T l :=
  @Multiset.filter _ (fun v => φ.holdsPlain v (Fin.append u γ))
    (fun v => φ.decHoldsPlain v (Fin.append u γ)) (S D (Fin.append u γ))

/-- **The plain semantics**, operator by operator. -/
noncomputable def semPlain : {c n : ℕ} → FragQueryIn T c n → Database T →
    (Fin c → T) → Relation T n
  | _, n, Rel _ s, D, _ => (D.find n s).getD (0 : Multiset (Tuple T n))
  | _, _, Empty, _, _ => (0 : Multiset (Tuple T 0))
  | _, _, Unit, _, _ => ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0))
  | _, _, Proj ts q, D, γ =>
    (q.semPlain D γ).map (fun u => (fun j => (ts j).evalPlain u γ : Tuple T _))
  | _, _, Sel φ q, D, γ =>
    @Multiset.filter _ (fun u => φ.holdsPlain u γ) (fun u => φ.decHoldsPlain u γ)
      (q.semPlain D γ)
  | _, _, Prod q₁ q₂, D, γ =>
    ((q₁.semPlain D γ).product (q₂.semPlain D γ)).map (fun xy =>
      (Fin.append xy.1 xy.2 : Tuple T _))
  | _, _, Apply q₁ q₂, D, γ =>
    (q₁.semPlain D γ).bind (fun u => (q₂.semPlain D (Fin.append u γ)).map (fun v =>
      (Fin.append u v : Tuple T _)))
  | _, _, Sum q₁ q₂, D, γ => q₁.semPlain D γ + q₂.semPlain D γ
  | _, _, Dedup q, D, γ => (q.semPlain D γ).dedup
  | _, _, Diff q₁ q₂, D, γ =>
    (q₁.semPlain D γ).filter (fun u => u ∉ (show Multiset (Tuple T _) from q₂.semPlain D γ))
  | _, _, Semijoin _ _ φ q₁ q₂, D, γ =>
    (q₁.semPlain D γ).filter (fun u =>
      (show Multiset (Tuple T _) from matchesPlain φ q₂.semPlain D γ u) ≠ 0)
  | _, _, Antijoin _ _ φ q₁ q₂, D, γ =>
    (q₁.semPlain D γ).filter (fun u =>
      (show Multiset (Tuple T _) from matchesPlain φ q₂.semPlain D γ u) = 0)

/-! ## The translation into the general syntax -/

/-- The projection that keeps the left arm's columns of a match-count
row and drops the count, in a context. -/
def dropCountIn (c k : ℕ) : Tuple (ProjColIn T c (AggQueryIn.countKinds k)) k :=
  fun i => .term (TermGIn.index (Fin.castAdd 1 i) (Fin.append_left _ _ i))

/-- **The match count of a semijoin in a context**: the left side, each
row extended by the token counting, over a non-null constant, the rows of
the right side the predicate matches it with. -/
def matchCountIn {c k l : ℕ} (cnt : SeqAggFunc T)
    (φ : GenPredIn T (k + c) (ColKind.allReg l))
    (R : AggQueryIn T c k (ColKind.allReg k))
    (Q : AggQueryIn T (k + c) l (ColKind.allReg l)) :
    AggQueryIn T c (k + 1) (AggQueryIn.countKinds k) :=
  AggQueryIn.Apply R
    (AggQueryIn.GammaScalar (lab := 0) (rd := (AggQueryIn.Sel φ Q).readsOuter)
      ![TermIn.const ValueType.nonzero] ![cnt] (AggQueryIn.Sel φ Q))

/-- **The count site of a semijoin or an antijoin in a context**: the
match count compared against `𝟘`, projected back onto the left side. -/
def countSiteIn {c k l : ℕ} (op : CompOp) (cnt : SeqAggFunc T)
    (φ : GenPredIn T (k + c) (ColKind.allReg l))
    (R : AggQueryIn T c k (ColKind.allReg k))
    (Q : AggQueryIn T (k + c) l (ColKind.allReg l)) :
    AggQueryIn T c k (ColKind.allReg k) :=
  AggQueryIn.Proj (dropCountIn c k)
    (AggQueryIn.Sel (GenPredIn.aggCmp (AggQueryIn.countCol k) (AggQueryIn.countKinds_countCol k) op
        (TermGIn.const 0))
      (matchCountIn cnt φ R Q))

/-- **The translation into the general syntax.** Each construct is the
operator of the same name, a semijoin or an antijoin the count site that
`Provenance.Derived` gives it, and the unit a scalar aggregation of
nothing over the empty relation. -/
def toAgg : {c n : ℕ} → FragQueryIn T c n → AggQueryIn T c n (ColKind.allReg n)
  | _, n, Rel _ s => AggQueryIn.Rel n s
  | _, _, Empty => AggQueryIn.Empty
  | _, _, Unit =>
    (AggQueryIn.GammaScalar (lab := 0) (rd := fun _ => false)
      (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
      AggQueryIn.Empty).castKind (funext fun j => j.elim0)
  | _, _, Proj ts q => AggQueryIn.Proj (fun j => ProjColIn.term (ts j)) q.toAgg
  | _, _, Sel φ q => AggQueryIn.Sel φ q.toAgg
  | _, _, @Prod _ _ _ n₁ n₂ q₁ q₂ =>
    (AggQueryIn.Prod q₁.toAgg q₂.toAgg).castKind (ColKind.allReg_append n₁ n₂)
  | _, _, @Apply _ _ _ n₁ n₂ q₁ q₂ =>
    (AggQueryIn.Apply q₁.toAgg q₂.toAgg).castKind (ColKind.allReg_append n₁ n₂)
  | _, _, Sum q₁ q₂ => AggQueryIn.Sum q₁.toAgg q₂.toAgg
  | _, _, Dedup q => AggQueryIn.Dedup q.toAgg
  | _, _, Diff q₁ q₂ => AggQueryIn.Diff q₁.toAgg q₂.toAgg
  | _, _, Semijoin cnt _ φ q₁ q₂ => countSiteIn CompOp.ne cnt φ q₁.toAgg q₂.toAgg
  | _, _, Antijoin cnt _ φ q₁ q₂ => countSiteIn CompOp.eq cnt φ q₁.toAgg q₂.toAgg

/-! ## The plain semantics of the translation -/

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- A constant term reads as the constant. -/
private theorem TermIn.eval_const {c m : ℕ} (x : T) (v : Tuple T m) (γ : Fin c → T) :
    (TermIn.const x : TermIn T c m).eval v γ = x := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **What a count over a non-null constant says of a sequence**: it is
`𝟘` exactly on the empty one. -/
private theorem counts_const_eq_zero_iff {α : Type} {cnt : SeqAggFunc T} (hc : cnt.Counts)
    (L : List α) : cnt (L.map (fun _ => ValueType.nonzero)) = 0 ↔ L = [] := by
  rw [hc.eq_zero]
  constructor
  · intro h
    cases L with
    | nil => rfl
    | cons a L =>
      have := h ValueType.nonzero (List.mem_map.mpr ⟨a, List.mem_cons_self, rfl⟩)
      rw [ValueType.isNull_nonzero] at this
      exact absurd this Bool.false_ne_true
  · rintro rfl
    simp

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The plain reading of a count site**: the match count's comparison
against `𝟘` holds on a left row exactly when its matches are, or are
not, there. -/
private theorem holdsPlain_countSite {α : Type} {c k : ℕ} (op : CompOp) {cnt : SeqAggFunc T}
    (hc : cnt.Counts) (u : Tuple T k) (L : List α) (γ : Fin c → T) :
    (GenPredIn.aggCmp (c := c) (AggQueryIn.countCol k) (AggQueryIn.countKinds_countCol k) op
        (TermGIn.const 0)).holdsPlain
      (Fin.append u (fun _ : Fin 1 => cnt (L.map (fun _ => ValueType.nonzero)))) γ
      ↔ op.eval (cnt (L.map (fun _ => ValueType.nonzero))) (0 : T) := by
  unfold GenPredIn.holdsPlain GenPredIn.evalPlain3
  rw [show Fin.append u (fun _ : Fin 1 => cnt (L.map (fun _ => ValueType.nonzero)))
      (AggQueryIn.countCol k) = cnt (L.map (fun _ => ValueType.nonzero)) from
    Fin.append_right _ _ 0]
  exact CompOp.eval3_eq_true_iff op (hc.not_null _) ValueType.isNull_zero

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The sequence a scalar count reads of a relation, with no key columns:
the relation's rows in the canonical order. -/
private theorem groupSeqOrd_nil {m : ℕ} (r : Relation T m) :
    Relation.groupSeqOrd (fun i : Fin 0 => i.elim0) GroupOrder.unord r
        (fun i : Fin 0 => i.elim0) = sortList r := by
  simp only [Relation.groupSeqOrd, Relation.groupSeq]
  rw [Multiset.filter_eq_self.mpr (fun _ _ k' => k'.elim0)]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The plain evaluation of a count site**: the left rows whose matches
compare as the operator says against nothing. -/
private theorem evaluatePlain_countSiteIn {c k l : ℕ} (op : CompOp) {cnt : SeqAggFunc T}
    (hc : cnt.Counts) (φ : GenPredIn T (k + c) (ColKind.allReg l))
    (R : AggQueryIn T c k (ColKind.allReg k))
    (Q : AggQueryIn T (k + c) l (ColKind.allReg l))
    (D : Database T) (γ : Fin c → T) :
    (countSiteIn op cnt φ R Q).evaluatePlain D γ
      = (R.evaluatePlain D γ).filter (fun u =>
          op.eval (cnt ((sortList (@Multiset.filter _
              (fun v => φ.holdsPlain v (Fin.append u γ))
              (fun v => φ.decHoldsPlain v (Fin.append u γ)) (Q.evaluatePlain D (Fin.append u γ)))).map
            (fun _ => ValueType.nonzero))) (0 : T)) := by
  unfold countSiteIn matchCountIn
  simp only [AggQueryIn.evaluatePlain]
  -- the scalar count gives one row per left row
  have hrow : ∀ u : Tuple T k,
      (Multiset.ofList [(fun j : Fin 1 => (![cnt] j)
          ((Relation.groupSeqOrd (fun i : Fin 0 => i.elim0) GroupOrder.unord
            (@Multiset.filter _ (fun v => φ.holdsPlain v (Fin.append u γ))
              (fun v => φ.decHoldsPlain v (Fin.append u γ))
              (Q.evaluatePlain D (Fin.append u γ))) (fun i : Fin 0 => i.elim0)).map
            (fun v => (![TermIn.const ValueType.nonzero] j).eval v (Fin.append u γ)))
          : Tuple T 1)] : Relation T 1)
        = {(fun _ : Fin 1 => cnt ((sortList (@Multiset.filter _
              (fun v => φ.holdsPlain v (Fin.append u γ))
              (fun v => φ.decHoldsPlain v (Fin.append u γ))
              (Q.evaluatePlain D (Fin.append u γ)))).map (fun _ => ValueType.nonzero)))} := by
    intro u
    refine congrArg (fun w : Tuple T 1 => ({w} : Multiset (Tuple T 1))) ?_
    funext j
    rw [Fin.fin_one_eq_zero j, groupSeqOrd_nil]
    simp only [Matrix.cons_val_zero]
    rfl
  simp only [hrow, Multiset.map_singleton, Multiset.bind_singleton]
  rw [Multiset.filter_map, Multiset.map_map]
  refine (Multiset.map_congr ?_ (fun u _ => ?_)).trans (Multiset.map_id _)
  · refine Multiset.filter_congr (fun u _ => ?_)
    simp only [Function.comp_apply]
    exact holdsPlain_countSite op hc u _ γ
  · simp only [Function.comp_apply, id_eq]
    funext j
    simp only [dropCountIn, ProjColIn.evalPlain, TermGIn.evalPlain]
    exact Fin.append_left _ _ j

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The rows of a relation, in canonical order, are nothing exactly when
the relation is empty. -/
private theorem sortList_eq_nil_iff {m : ℕ} (r : Multiset (Tuple T m)) :
    sortList r = [] ↔ r = 0 := by
  constructor
  · intro h
    have := sortList_coe r
    rw [h] at this
    exact this.symm
  · rintro rfl
    rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The general evaluator computes the plain semantics of the
fragment.** -/
theorem toAgg_evaluatePlain : ∀ {c n : ℕ} (q : FragQueryIn T c n) (D : Database T)
    (γ : Fin c → T), q.toAgg.evaluatePlain D γ = q.semPlain D γ
  | _, n, Rel _ s, D, γ => by
    simp only [toAgg, AggQueryIn.evaluatePlain, semPlain]
    cases D.find n s <;> rfl
  | _, _, Empty, D, γ => rfl
  | _, _, Unit, D, γ => by
    simp only [toAgg, semPlain]
    rw [AggQueryIn.evaluatePlain_castKind]
    simp only [AggQueryIn.evaluatePlain]
    exact congrArg (fun v : Tuple T 0 => ({v} : Multiset (Tuple T 0)))
      (funext fun j => j.elim0)
  | _, _, Proj ts q, D, γ => by
    simp only [toAgg, AggQueryIn.evaluatePlain, semPlain]
    rw [toAgg_evaluatePlain q D γ]
    rfl
  | _, _, Sel φ q, D, γ => by
    simp only [toAgg, AggQueryIn.evaluatePlain, semPlain]
    rw [toAgg_evaluatePlain q D γ]
  | _, _, Prod q₁ q₂, D, γ => by
    simp only [toAgg, semPlain]
    rw [AggQueryIn.evaluatePlain_castKind]
    simp only [AggQueryIn.evaluatePlain]
    rw [toAgg_evaluatePlain q₁ D γ, toAgg_evaluatePlain q₂ D γ]
    rfl
  | _, _, Apply q₁ q₂, D, γ => by
    simp only [toAgg, semPlain]
    rw [AggQueryIn.evaluatePlain_castKind]
    simp only [AggQueryIn.evaluatePlain]
    rw [toAgg_evaluatePlain q₁ D γ]
    refine Multiset.bind_congr (fun u _ => ?_)
    rw [toAgg_evaluatePlain q₂ D _]
  | _, _, Sum q₁ q₂, D, γ => by
    simp only [toAgg, AggQueryIn.evaluatePlain, semPlain]
    rw [toAgg_evaluatePlain q₁ D γ, toAgg_evaluatePlain q₂ D γ]
  | _, _, Dedup q, D, γ => by
    simp only [toAgg, AggQueryIn.evaluatePlain, semPlain]
    rw [toAgg_evaluatePlain q D γ]
  | _, _, Diff q₁ q₂, D, γ => by
    simp only [toAgg, AggQueryIn.evaluatePlain, semPlain]
    rw [toAgg_evaluatePlain q₁ D γ, toAgg_evaluatePlain q₂ D γ]
  | _, _, Semijoin cnt hc φ q₁ q₂, D, γ => by
    simp only [toAgg, semPlain]
    rw [evaluatePlain_countSiteIn CompOp.ne hc, toAgg_evaluatePlain q₁ D γ]
    refine Multiset.filter_congr (fun u _ => ?_)
    rw [toAgg_evaluatePlain q₂ D _]
    show cnt _ ≠ 0 ↔ _
    rw [Ne, counts_const_eq_zero_iff hc, sortList_eq_nil_iff]
    rfl
  | _, _, Antijoin cnt hc φ q₁ q₂, D, γ => by
    simp only [toAgg, semPlain]
    rw [evaluatePlain_countSiteIn CompOp.eq hc, toAgg_evaluatePlain q₁ D γ]
    refine Multiset.filter_congr (fun u _ => ?_)
    rw [toAgg_evaluatePlain q₂ D _]
    show cnt _ = 0 ↔ _
    rw [counts_const_eq_zero_iff hc, sortList_eq_nil_iff]
    rfl

/-! ## The annotated semantics of the translation

The rows the general evaluator produces on a translated query are
embedded annotated tuples: regular values, and nothing pending. The
lemmas below read each operator on such rows. -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The data of an embedded row. -/
private theorem GenRow.ofAnnotated_fst {n : ℕ} (p : AnnotatedTuple T K n) :
    (GenRow.ofAnnotated p).fst = fun k => Sum.inl (p.fst k) := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The annotation of an embedded row: its concrete part, nothing
pending. -/
private theorem GenRow.ofAnnotated_snd {n : ℕ} (p : AnnotatedTuple T K n) :
    (GenRow.ofAnnotated p).snd = ⟨p.snd, 0⟩ := rfl

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- Finalizing embedded rows gives the tuples back. -/
private theorem map_toAnnotated_map_ofAnnotated {n : ℕ} (X : AnnotatedRelation T K n) :
    (X.map GenRow.ofAnnotated).map GenRow.toAnnotated = X := by
  rw [Multiset.map_map]
  refine (Multiset.map_congr rfl (fun p _ => ?_)).trans (Multiset.map_id _)
  exact GenRow.toAnnotated_ofAnnotated p

/-- **An apply, in a context and an environment**: the evaluator's
clause, with nothing simplified. -/
private theorem evaluate_Apply_env {c n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQueryIn T c n₁ κ₁) (q₂ : AggQueryIn T (n₁ + c) n₂ κ₂)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.Apply q₁ q₂).evaluate d γ E
      = (q₁.evaluate d γ E).bind (fun x =>
          (q₂.evaluate d (Fin.append (GenRow.plainTuple x.fst) γ)
              (E.withCtx (Fin.append x.fst (E.ctxAt _ γ)))).map (fun y =>
            (⟨Fin.append x.fst y.fst,
              ⟨x.snd.base * y.snd.base, x.snd.pending + y.snd.pending⟩⟩
              : GenRow T K (n₁ + n₂)))) := by
  simp only [AggQueryIn.evaluate]

/-- **A selection without an aggregate atom filters**, in any context
and environment. -/
private theorem evaluate_Sel_noAgg_env {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    (hφ : φ.hasAggAtom = false) (q : AggQueryIn T c n κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.Sel φ q).evaluate d γ E
      = (q.evaluate d γ E).filter (fun r => φ.holds r.fst γ) := by
  show (if φ.hasAggAtom = true then _ else _) = _
  rw [hφ]
  rfl

/-- **A selection on an aggregate atom, over rows with nothing
pending**: each row's concrete annotation is multiplied by the
predicate's provenance, and nothing is pending afterwards either. -/
private theorem evaluate_Sel_agg_env {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    (hφ : φ.hasAggAtom = true) (q : AggQueryIn T c n κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (hz : ∀ r ∈ q.evaluate d γ E, r.snd.pending = 0) :
    (AggQueryIn.Sel φ q).evaluate d γ E
      = (q.evaluate d γ E).map (fun r =>
          (⟨r.fst, ⟨r.snd.base * φ.predsemJ false r.fst γ, 0⟩⟩ : GenRow T K n)) := by
  show (if φ.hasAggAtom = true then _ else _) = _
  rw [hφ]
  simp only [ite_true]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  rw [hz r hr]
  simp only [Multiset.filter_zero, ite_self]

/-- **A projection over rows with nothing pending** evaluates its
columns and keeps the concrete annotations. -/
private theorem evaluate_Proj_env {c n m : ℕ} {κ : Fin n → ColKind}
    (ps : Tuple (ProjColIn T c κ) m) (q : AggQueryIn T c n κ)
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (hz : ∀ r ∈ q.evaluate d γ E, r.snd.pending = 0) :
    (AggQueryIn.Proj ps q).evaluate d γ E
      = (q.evaluate d γ E).map (fun r =>
          (⟨fun j => (ps j).eval r.fst γ, ⟨r.snd.base, 0⟩⟩ : GenRow T K m)) := by
  simp only [AggQueryIn.evaluate]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  rw [hz r hr]
  simp only [Multiset.zero_inter, Multiset.sub_zero, Multiset.map_zero, Multiset.prod_zero,
    mul_one]

/-- **A scalar aggregation on one pair, in a context and an
environment**: the one row carrying its token. -/
private theorem evaluate_GammaScalar_one_env {lab c m : ℕ} {rd : Fin c → Bool} (t : TermIn T c m)
    (cnt : SeqAggFunc T) (q : AggQueryIn T c m (ColKind.allReg m))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K) :
    (AggQueryIn.GammaScalar (lab := lab) (rd := rd) ![t] ![cnt] q).evaluate d γ E
      = {(⟨fun j : Fin 1 => Sum.inr ((AggTok.tok (AggValue.ofScalarGroup cnt t
            (Having.havingGroup (fun i : Fin 0 => i.elim0)
              (q.evaluateAnnotated d γ E) (fun i : Fin 0 => i.elim0)) γ)).setFam
                (.mk lab [] (E.paramKey rd γ) j [])
                (some (OccId.listing lab (E.paramKey rd γ) []
                  (Having.havingGroup (fun i : Fin 0 => i.elim0)
                    (q.evaluateAnnotated d γ E) (fun i : Fin 0 => i.elim0)).length))),
          ⟨1, 0⟩⟩ : GenRow T K 1)} := by
  simp only [AggQueryIn.evaluate, AggQueryIn.evaluateAnnotated,
    Having.havingGroupOrd_unord, Matrix.cons_val_fin_one]

/-- The token a count site builds on a left row `u`: the scalar count,
over the non-null constant, of the rows of the right side that match
`u`. -/
noncomputable def countToken {c k l : ℕ} (cnt : SeqAggFunc T)
    (M : AnnotatedRelation T K l) (u : Tuple T k) (γ : Fin c → T) : AggValue T K :=
  AggValue.ofScalarGroup cnt (TermIn.const ValueType.nonzero)
    (Having.havingGroup (fun i : Fin 0 => i.elim0) M (fun i : Fin 0 => i.elim0))
    (Fin.append u γ)

omit [HasAltLinearOrder K] in
/-- The scalar predicate provenance of a scalar token reads its
occurrences and its aggregate, and nothing else: setting its family
changes it not. -/
private theorem predProvOf_setFam_tok (a : AggValue T K) (ha : a.scalar = true) (φ : FamId T)
    (ids : Option (List (OccId T))) (op : CompOp) (x : T) :
    ((AggTok.tok a).setFam φ ids).predProvOf op x = a.predProvScalar op x := by
  show ({ a with fam := φ, oids := ids.getD a.oids } : AggValue T K).predProvOf op x = _
  rw [AggValue.predProvOf, ite_eq_left ha]
  rfl

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The count token's occurrences all carry the non-null constant. -/
private theorem countToken_occs_not_null {c k l : ℕ} (cnt : SeqAggFunc T)
    (M : AnnotatedRelation T K l) (u : Tuple T k) (γ : Fin c → T) :
    ∀ o ∈ (countToken cnt M u γ).occs, ValueType.isNull o.fst = false := by
  intro o ho
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
  exact ValueType.isNull_nonzero

omit [DecidableEq K] in
/-- The `⊕`-sum of the count token's occurrence annotations is the
`⊕`-sum of the annotations of the matches. -/
private theorem sum_anns_countToken {c k l : ℕ} (cnt : SeqAggFunc T)
    (M : AnnotatedRelation T K l) (u : Tuple T k) (γ : Fin c → T) :
    ∑ i, (countToken cnt M u γ).anns i = M.annTotal := by
  rw [show (fun i => (countToken cnt M u γ).anns i)
      = fun i => ((countToken cnt M u γ).occs.get i).snd from rfl,
    AggQueryIn.sum_fin_get Prod.snd]
  show (List.map Prod.snd (List.map
      (fun p : AnnotatedTuple T K l =>
        ((TermIn.const ValueType.nonzero).eval p.fst (Fin.append u γ), p.snd))
      (Having.havingGroup (fun i : Fin 0 => i.elim0) M (fun i : Fin 0 => i.elim0)))).sum = _
  rw [List.map_map]
  exact AggQueryIn.annTotal_havingGroup M

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The rows a selection keeps, read on embedded rows: those whose tuple
satisfies the predicate classically. -/
private theorem filter_holds_map_ofAnnotated {c n : ℕ} (φ : GenPredIn T c (ColKind.allReg n))
    (X : AnnotatedRelation T K n) (γ : Fin c → T) :
    (X.map GenRow.ofAnnotated).filter (fun r => φ.holds r.fst γ)
      = (X.filter (fun p => φ.holdsPlain p.fst γ)).map GenRow.ofAnnotated := by
  rw [Multiset.filter_map]
  refine congrArg _ (Multiset.filter_congr (fun p _ => ?_))
  show φ.holds (GenRow.ofAnnotated p).fst γ ↔ _
  rw [GenPredIn.holds_iff_holdsPlain, GenRow.plainTuple_ofAnnotated]

/-- **The rows a count site produces, in a context**: each row of the left
side, its annotation multiplied by the predicate provenance of comparing
its match count against `𝟘`. Stated for a left side and a right side whose
rows are embedded annotated tuples, which is what the translation
produces. -/
private theorem evaluate_countSiteIn {c k l : ℕ} (op : CompOp) (cnt : SeqAggFunc T)
    (φ : GenPredIn T (k + c) (ColKind.allReg l))
    (R : AggQueryIn T c k (ColKind.allReg k))
    (Q : AggQueryIn T (k + c) l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K)
    (X : AnnotatedRelation T K k)
    (S : (Fin (k + c) → T) → AnnotatedRelation T K l)
    (hR : R.evaluate d γ E = X.map GenRow.ofAnnotated)
    (hQ : ∀ (γ' : Fin (k + c) → T) (E' : EvalEnv T K),
      Q.evaluate d γ' E' = (S γ').map GenRow.ofAnnotated) :
    (countSiteIn op cnt φ R Q).evaluate d γ E
      = (X.map (fun p =>
          ((p.fst, p.snd * (countToken cnt
            ((S (Fin.append p.fst γ)).filter (fun r => φ.holdsPlain r.fst (Fin.append p.fst γ)))
            p.fst γ).predProvScalar op 0) : AnnotatedTuple T K k))).map GenRow.ofAnnotated := by
  -- the matches of a left row, as the scalar aggregation sees them
  have hsel : ∀ (p : AnnotatedTuple T K k) (E' : EvalEnv T K),
      (AggQueryIn.Sel φ Q).evaluateAnnotated d (Fin.append p.fst γ) E'
        = (S (Fin.append p.fst γ)).filter
            (fun r => φ.holdsPlain r.fst (Fin.append p.fst γ)) := by
    intro p E'
    unfold AggQueryIn.evaluateAnnotated
    rw [evaluate_Sel_noAgg_env φ (GenPredIn.hasAggAtom_allReg φ) Q, hQ, filter_holds_map_ofAnnotated,
      map_toAnnotated_map_ofAnnotated]
  -- the match count: each left row, extended by its token
  have hM : (matchCountIn cnt φ R Q).evaluate d γ E
      = X.map (fun p =>
          (⟨Fin.append (fun j => Sum.inl (p.fst j))
              (fun _ : Fin 1 => Sum.inr ((AggTok.tok (countToken cnt
                ((S (Fin.append p.fst γ)).filter
                  (fun r => φ.holdsPlain r.fst (Fin.append p.fst γ))) p.fst γ)).setFam
                (.mk 0 [] ((E.withCtx (Fin.append (GenRow.ofAnnotated p).fst
                  (E.ctxAt c γ))).paramKey (AggQueryIn.Sel φ Q).readsOuter (Fin.append p.fst γ)) 0 [])
                (some (OccId.listing 0 ((E.withCtx (Fin.append (GenRow.ofAnnotated p).fst
                  (E.ctxAt c γ))).paramKey (AggQueryIn.Sel φ Q).readsOuter (Fin.append p.fst γ)) []
                  (Having.havingGroup (fun i : Fin 0 => i.elim0)
                    ((S (Fin.append p.fst γ)).filter
                      (fun r => φ.holdsPlain r.fst (Fin.append p.fst γ)))
                    (fun i : Fin 0 => i.elim0)).length)))),
            ⟨p.snd, 0⟩⟩ : GenRow T K (k + 1))) := by
    unfold matchCountIn
    rw [evaluate_Apply_env, hR, Multiset.bind_map]
    refine (Multiset.bind_congr (fun p _ => ?_)).trans (Multiset.bind_singleton _ _)
    rw [evaluate_GammaScalar_one_env, Multiset.map_singleton, GenRow.plainTuple_ofAnnotated,
      hsel]
    refine congrArg (fun r : GenRow T K (k + 1) => ({r} : Multiset _)) ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      congr 1
      funext j
      rw [Fin.fin_one_eq_zero j]
      rfl
    · show (⟨p.snd * 1, 0 + 0⟩ : GenAnn K) = ⟨p.snd, 0⟩
      rw [mul_one, add_zero]
  have hz : ∀ r ∈ (matchCountIn cnt φ R Q).evaluate d γ E, r.snd.pending = 0 := by
    rw [hM]
    intro r hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
    rfl
  unfold countSiteIn
  rw [evaluate_Proj_env _ _ d γ E (by
      rw [evaluate_Sel_agg_env _ rfl _ d γ E hz]
      intro r hr
      obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
      rfl),
    evaluate_Sel_agg_env _ rfl _ d γ E hz, hM, Multiset.map_map, Multiset.map_map,
    Multiset.map_map]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  simp only [Function.comp_apply]
  refine Prod.ext ?_ ?_
  · funext j
    show Sum.inl (AggValue.collapseSum (Fin.append (fun j => Sum.inl (p.fst j)) _
      (Fin.castAdd 1 j))) = (Sum.inl (p.fst j) : GenValue T K)
    rw [Fin.append_left]
    rfl
  · show (⟨p.snd * GenPredIn.predsemJ _ false _ γ, 0⟩ : GenAnn K) = ⟨_, 0⟩
    rw [GenPredIn.predsemJ_aggCmp _ _ op _ _ γ _ (Fin.append_right _ _ 0) false,
      predProvOf_setFam_tok _ rfl]
    rfl

/-- A count compared as “not `𝟘`” annotates the `⊕`-sum of its matches,
in an absorptive m-semiring. -/
private theorem countToken_predProvScalar_ne {c k l : ℕ} (habs : absorptive K)
    {cnt : SeqAggFunc T} (hc : cnt.Counts) (M : AnnotatedRelation T K l) (u : Tuple T k)
    (γ : Fin c → T) :
    (countToken cnt M u γ).predProvScalar CompOp.ne 0 = M.annTotal := by
  rw [AggValue.predProvScalar_count_ne_zero habs _ hc (countToken_occs_not_null cnt M u γ),
    sum_anns_countToken]

/-- A count compared as “`𝟘`” annotates `𝟙 ⊖` the `⊕`-sum of its matches,
in every m-semiring. -/
private theorem countToken_predProvScalar_eq {c k l : ℕ}
    {cnt : SeqAggFunc T} (hc : cnt.Counts) (M : AnnotatedRelation T K l) (u : Tuple T k)
    (γ : Fin c → T) :
    (countToken cnt M u γ).predProvScalar CompOp.eq 0 = 1 - M.annTotal := by
  rw [AggValue.predProvScalar_count_eq_zero _ hc (countToken_occs_not_null cnt M u γ),
    sum_anns_countToken]

/-- **The general evaluator computes the annotated semantics of the
fragment, row for row**: on a translated query it produces the embedded
rows of `FragQueryIn.sem`, in every context and every environment.
Absorptivity is asked only of a query with a semijoin, whose closed form
needs it. -/
theorem toAgg_evaluate : ∀ {c n : ℕ} (q : FragQueryIn T c n), (q.hasSemijoin → absorptive K) →
    ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T) (E : EvalEnv T K),
    q.toAgg.evaluate d γ E = (q.sem d γ).map GenRow.ofAnnotated
  | _, n, Rel _ s, habs, d, γ, E => by
    simp only [toAgg, AggQueryIn.evaluate, sem]
    cases d.find n s <;> rfl
  | _, _, Empty, habs, d, γ, E => rfl
  | _, _, Unit, habs, d, γ, E => by
    simp only [toAgg, sem]
    rw [AggQueryIn.evaluate_castKind]
    simp only [AggQueryIn.evaluate, Multiset.map_singleton]
    refine congrArg (fun r : GenRow T K 0 => ({r} : Multiset _)) (Prod.ext ?_ rfl)
    funext j
    exact j.elim0
  | _, _, Proj ts q, habs, d, γ, E => by
    simp only [toAgg, sem]
    rw [evaluate_Proj_env _ _ d γ E (by
        rw [toAgg_evaluate q habs d γ E]
        intro r hr
        obtain ⟨p, -, rfl⟩ := Multiset.mem_map.mp hr
        rfl),
      toAgg_evaluate q habs d γ E, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    refine Prod.ext ?_ rfl
    funext j
    show Sum.inl ((ts j).eval (GenRow.ofAnnotated p).fst γ) = (Sum.inl ((ts j).evalPlain p.fst γ) : GenValue T K)
    rw [TermGIn.eval_eq_evalPlain, GenRow.plainTuple_ofAnnotated]
  | _, _, Sel φ q, habs, d, γ, E => by
    simp only [toAgg, sem]
    rw [evaluate_Sel_noAgg_env φ (GenPredIn.hasAggAtom_allReg φ), toAgg_evaluate q habs d γ E, filter_holds_map_ofAnnotated]
  | _, _, Prod q₁ q₂, habs, d, γ, E => by
    simp only [toAgg, sem]
    rw [AggQueryIn.evaluate_castKind]
    simp only [AggQueryIn.evaluate]
    rw [toAgg_evaluate q₁ (fun h => habs (Or.inl h)) d γ E,
      toAgg_evaluate q₂ (fun h => habs (Or.inr h)) d γ E, AggQueryIn.product_map_map,
      Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun xy _ => ?_)
    refine Prod.ext ?_ ?_
    · funext k
      show Fin.append (fun j => Sum.inl (xy.1.fst j)) (fun j => Sum.inl (xy.2.fst j)) k
        = (Sum.inl (Fin.append xy.1.fst xy.2.fst k) : GenValue T K)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
    · show (⟨xy.1.snd * xy.2.snd, 0 + 0⟩ : GenAnn K) = ⟨xy.1.snd * xy.2.snd, 0⟩
      rw [add_zero]
  | _, _, Apply q₁ q₂, habs, d, γ, E => by
    simp only [toAgg, sem]
    rw [AggQueryIn.evaluate_castKind, evaluate_Apply_env,
      toAgg_evaluate q₁ (fun h => habs (Or.inl h)) d γ E, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun p _ => ?_)
    rw [GenRow.plainTuple_ofAnnotated, toAgg_evaluate q₂ (fun h => habs (Or.inr h)) d _ _,
      Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun y _ => ?_)
    refine Prod.ext ?_ ?_
    · funext k
      show Fin.append (fun j => Sum.inl (p.fst j)) (fun j => Sum.inl (y.fst j)) k
        = (Sum.inl (Fin.append p.fst y.fst k) : GenValue T K)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
    · show (⟨p.snd * y.snd, 0 + 0⟩ : GenAnn K) = ⟨p.snd * y.snd, 0⟩
      rw [add_zero]
  | _, _, Sum q₁ q₂, habs, d, γ, E => by
    simp only [toAgg, AggQueryIn.evaluate, sem]
    rw [toAgg_evaluate q₁ (fun h => habs (Or.inl h)) d γ E,
      toAgg_evaluate q₂ (fun h => habs (Or.inr h)) d γ E, Multiset.map_add]
  | _, _, Dedup q, habs, d, γ, E => by
    simp only [toAgg, AggQueryIn.evaluate, sem]
    rw [toAgg_evaluate q habs d γ E, map_toAnnotated_map_ofAnnotated, groupByKey_eq_dedup_map]
    simp only [Multiset.map_map]
    rfl
  | _, _, Diff q₁ q₂, habs, d, γ, E => by
    simp only [toAgg, AggQueryIn.evaluate, sem]
    rw [toAgg_evaluate q₁ (fun h => habs (Or.inl h)) d γ E,
      toAgg_evaluate q₂ (fun h => habs (Or.inr h)) d γ E, map_toAnnotated_map_ofAnnotated,
      map_toAnnotated_map_ofAnnotated]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    show GenRow.ofAnnotated (u, α - _) = GenRow.ofAnnotated (u, α - _)
    rw [groupByKey_find_eq_filter_sum]
    rfl
  | _, _, Semijoin cnt hc φ q₁ q₂, habs, d, γ, E => by
    simp only [toAgg, sem]
    rw [evaluate_countSiteIn CompOp.ne cnt φ _ _ d γ E (q₁.sem d γ) (q₂.sem d)
      (toAgg_evaluate q₁ (fun _ => habs trivial) d γ E)
      (fun γ' E' => toAgg_evaluate q₂ (fun _ => habs trivial) d γ' E')]
    refine congrArg _ (Multiset.map_congr rfl (fun p _ => ?_))
    rw [countToken_predProvScalar_ne (habs trivial) hc]
    rfl
  | _, _, Antijoin cnt hc φ q₁ q₂, habs, d, γ, E => by
    simp only [toAgg, sem]
    rw [evaluate_countSiteIn CompOp.eq cnt φ _ _ d γ E (q₁.sem d γ) (q₂.sem d)
      (toAgg_evaluate q₁ (fun h => habs (Or.inl h)) d γ E)
      (fun γ' E' => toAgg_evaluate q₂ (fun h => habs (Or.inr h)) d γ' E')]
    refine congrArg _ (Multiset.map_congr rfl (fun p _ => ?_))
    rw [countToken_predProvScalar_eq hc]
    rfl

/-- **The general evaluator computes the annotated semantics of the
fragment.** -/
theorem toAgg_evaluateAnnotated {c n : ℕ} (q : FragQueryIn T c n)
    (habs : q.hasSemijoin → absorptive K) (d : AnnotatedDatabase T K) (γ : Fin c → T)
    (E : EvalEnv T K) :
    q.toAgg.evaluateAnnotated d γ E = q.sem d γ := by
  unfold AggQueryIn.evaluateAnnotated
  rw [toAgg_evaluate q habs d γ E, map_toAnnotated_map_ofAnnotated]

end FragQueryIn

end
