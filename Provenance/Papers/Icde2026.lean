/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryRewriting
import Provenance.Semirings.Why

/-!
# Frozen restatement of the claims of a published paper

[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*, ICDE 2026][sen2026provsql] links to this
library: eight of its definitions and results carry a hyperlink to a declaration
page under <https://provsql.org/lean-docs/>, and the paper as a whole links to
the landing page. Those links are in a PDF and cannot be fixed after the fact.

There is one published documentation tree, and it tracks `main`, so the paper's
links deliberately reach material that has grown *beyond* the paper. What has to
be guaranteed is therefore narrower, and sharper, than "the docs still match the
paper":

1. the anchors still exist — checked by `scripts/check-anchors.sh`, which reads
   the `Anchor:` lines below;
2. the declarations they land on still **subsume** the paper's claims — checked
   by this file.

This module is what makes the second half mechanical. Each claim the paper makes
is restated here *in the paper's own form* and proved by applying the library
declaration the paper cites. If the library generalizes — a wider fragment, an
extra hypothesis discharged, a fused operator — the proof still goes through,
which is the right answer: the paper's claim is still there, subsumed. If a
statement is ever *weakened*, this file stops compiling and `lake build` fails.
No textual or anchor-level check distinguishes those two cases.

The statements below are therefore **frozen**: they were fixed when the paper
was published and are never edited to follow the library. Only the proof terms
may be re-plumbed. `scripts/release.sh check` compares this file against the
hash in `scripts/icde2026.sha256`, so an edit is a deliberate act that shows up
in a diff rather than a silent drift.

## Scope

Two places where the library and the paper are not literally coextensive, both
recorded here rather than papered over:

* The paper's relational algebra has an aggregation former
  `γ_{i₁,…,i_m}[t₁:f₁,…,t_n:f_n]`, and its rewriting has a rule (R5) for it.
  `Query`, the declaration the paper's grammar links to, is the *classical*
  syntax: it carries the operators of RA⁺(∖) plus `ProvSum`, the ⊕-aggregation
  that rules (R1)–(R4) emit. General aggregation, and the rewriting rule for it,
  live on the kind-indexed syntax (`AggQuery.Gamma`, and the bare-grouping
  rewriting of `Provenance.AggQueryGroupRewriting`), which did not exist when
  the paper was written. This module deliberately does not import those: a
  frozen file should depend on as little as possible, and what it must pin is
  what the paper's anchors name.
* Accordingly, the rewriting correctness theorem restated below carries the
  hypothesis `q.source`, the fragment (R1)–(R4) covers.

Anchor: Provenance.html
-/

namespace Icde2026

set_option linter.unusedSectionVars false

variable {T : Type} [ValueType T] {K : Type} {α : Type} {n n₁ n₂ k k₁ k₂ : ℕ}

/-! ## Semirings with monus

The paper defines an m-semiring by three equations. In the library the monus is
axiomatized instead by its Galois connection `a ⊖ b ≤ c ↔ a ≤ b ⊕ c`, which is
strictly stronger: the three equations are theorems. That is exactly the shape
of drift this file is meant to allow — a *generalization* of the cited
declaration keeps these proofs one-liners.
-/

/-- The paper's m-semiring axiom (i): `a ⊕ (b ⊖ a) = b ⊕ (a ⊖ b)`.

Anchor: Provenance/SemiringWithMonus.html#SemiringWithMonus -/
theorem msemiring_axiom_i [SemiringWithMonus K] (a b : K) :
    a + (b - a) = b + (a - b) :=
  add_monus a b

/-- The paper's m-semiring axiom (ii): `(a ⊖ b) ⊖ c = a ⊖ (b ⊕ c)`. -/
theorem msemiring_axiom_ii [SemiringWithMonus K] (a b c : K) :
    ((a - b) - c) = (a - (b + c)) :=
  (monus_add a b c).symm

/-- The paper's m-semiring axiom (iii): `a ⊖ a = 𝟘 ⊖ a = 𝟘`. -/
theorem msemiring_axiom_iii [SemiringWithMonus K] (a : K) :
    ((a - a) = 0) ∧ (((0 : K) - a) = 0) :=
  ⟨monus_self a, zero_monus a⟩

/-- The paper's δ-semiring axiom (i): `δ(𝟘) = 𝟘`. -/
theorem delta_axiom_i [SemiringWithMonus K] :
    SemiringWithMonus.delta (0 : K) = 0 :=
  SemiringWithMonus.delta_zero

/-- The paper's δ-semiring axiom (ii): `δ(𝟙 ⊕ ⋯ ⊕ 𝟙) = 𝟙`, whatever the number
of `𝟙`s. -/
theorem delta_axiom_ii [SemiringWithMonus K] {j : ℕ} (hj : 0 < j) :
    SemiringWithMonus.delta ((j : K)) = 1 :=
  SemiringWithMonus.delta_natCast_pos hj

/-! ## Why-provenance

The paper's proposition: for a set `X`, the structure
`(2^(2^X), ∅, {∅}, ∪, ⋓, ∖)` is an m-semiring. Exhibiting the instance is only
half of that — the operations have to be the stated ones — so each of the six is
pinned separately.
-/

/-- Why-provenance: `𝟘` is `∅`.

Anchor: Provenance/Semirings/Why.html#instSemiringWithMonusWhy -/
theorem why_zero : (0 : Why α).carrier = ∅ := rfl

/-- Why-provenance: `𝟙` is `{∅}`. -/
theorem why_one : (1 : Why α).carrier = {∅} := rfl

/-- Why-provenance: `⊕` is union of families. -/
theorem why_add (a b : Why α) : (a + b).carrier = a.carrier ∪ b.carrier := rfl

/-- Why-provenance: `⊗` is `⋓`, the pairwise union of witnesses. -/
theorem why_mul (a b : Why α) :
    (a * b).carrier
      = {z : Set α | ∃ x y : Set α, x ∈ a.carrier ∧ y ∈ b.carrier ∧ z = x ∪ y} :=
  rfl

/-- Why-provenance: `⊖` is set difference of families. -/
theorem why_monus (a b : Why α) : (a - b).carrier = a.carrier \ b.carrier := rfl

/-- Why-provenance is an m-semiring under exactly those operations. -/
theorem why_isMSemiring : Nonempty (SemiringWithMonus (Why α)) :=
  ⟨instSemiringWithMonusWhy⟩

/-! ## Annotated databases

The paper: a `K`-relation of arity `k` is a finite multiset of `k`-tuples each
carrying an annotation from `K`, and a `K`-instance over a schema `D` maps each
relation name `R` to a `K`-relation of arity `D(R)`.
-/

/-- A `K`-relation of arity `n` is a multiset of `n`-tuples paired with an
annotation.

Anchor: Provenance/AnnotatedDatabase.html#AnnotatedDatabase -/
theorem annotated_relation_eq : AnnotatedRelation T K n = Multiset (Tuple T n ×ₗ K) := rfl

/-- A `K`-instance answers a relation name, at an arity, with a `K`-relation. -/
theorem annotated_database_lookup :
    ∀ (R : String) (d : AnnotatedDatabase T K),
      (AnnotatedDatabase.find n R d : Option (AnnotatedRelation T K n)) = d.find n R :=
  fun _ _ => rfl

/-! ## The relational algebra `RA_k`

Each clause of the paper's grammar, as the typing rule it is. Each is proved by
exhibiting the corresponding constructor of `Query`.

Anchor: Provenance/Query.html#Query
-/

/-- **relation**: `R ∈ RA_{D(R)}`. -/
def raRelation (n : ℕ) (R : String) : Query T n := Query.Rel n R

/-- **projection**: for `q ∈ RA_k` and terms `t₁, …, t_n` of max-index `≤ k`,
`Π_{t₁,…,t_n}(q) ∈ RA_n`. -/
def raProjection (ts : Tuple (Term T k) n) (q : Query T k) : Query T n := Query.Proj ts q

/-- **selection**: for `q ∈ RA_k` and `φ` a Boolean combination of comparisons
between terms of max-index `≤ k`, `σ_φ(q) ∈ RA_k`. -/
def raSelection (φ : Selection T k) (q : Query T k) : Query T k := Query.Sel φ q

/-- **cross product**: for `q₁ ∈ RA_{k₁}` and `q₂ ∈ RA_{k₂}`,
`q₁ × q₂ ∈ RA_{k₁+k₂}`. -/
def raProduct (q₁ : Query T k₁) (q₂ : Query T k₂) : Query T (k₁ + k₂) :=
  Query.Prod (hn := rfl) q₁ q₂

/-- **multiset sum**: for `q₁, q₂ ∈ RA_k`, `q₁ ⊎ q₂ ∈ RA_k`. -/
def raMultisetSum (q₁ q₂ : Query T k) : Query T k := Query.Sum q₁ q₂

/-- **duplicate elimination**: for `q ∈ RA_k`, `ε(q) ∈ RA_k`. -/
def raDupElim (q : Query T k) : Query T k := Query.Dedup q

/-- **multiset difference**: for `q₁, q₂ ∈ RA_k`, `q₁ - q₂ ∈ RA_k`. -/
def raDifference (q₁ q₂ : Query T k) : Query T k := Query.Diff q₁ q₂

/-- **join**, the paper's syntactic sugar `q₁ ⋈_φ q₂ ≝ σ_φ(q₁ × q₂)`. -/
def raJoin (φ : Selection T (k₁ + k₂)) (q₁ : Query T k₁) (q₂ : Query T k₂) :
    Query T (k₁ + k₂) :=
  Query.Sel φ (Query.Prod (hn := rfl) q₁ q₂)

/-- **set union**, the paper's syntactic sugar `q₁ ∪ q₂ ≝ ε(q₁ ⊎ q₂)`. -/
def raSetUnion (q₁ q₂ : Query T k) : Query T k := Query.Dedup (Query.Sum q₁ q₂)

/-! ## Plain multiset semantics

The paper's `⟦·⟧_I`, clause by clause.

Anchor: Provenance/Query.html#Query.evaluate
-/

/-- **relation**: `⟦R⟧_I ≝ I(R)`. -/
theorem eval_rel (R : String) (d : Database T) :
    (Query.Rel n R).evaluate d = (d.find n R).getD (∅ : Multiset (Tuple T n)) := by
  rw [Query.evaluate]; cases d.find n R <;> rfl

/-- **projection**: `⟦Π_{t₁,…,t_n}(q)⟧_I ≝ {|(t₁(u),…,t_n(u)) | u ∈ ⟦q⟧_I|}`. -/
theorem eval_proj (ts : Tuple (Term T k) n) (q : Query T k) (d : Database T) :
    (Query.Proj ts q).evaluate d = (q.evaluate d).map (fun u l => (ts l).eval u) := by
  rw [Query.evaluate]

/-- **selection**: `⟦σ_φ(q)⟧_I ≝ {|u | u ∈ ⟦q⟧_I, φ(u)|}`. -/
theorem eval_sel (φ : Selection T n) (q : Query T n) (d : Database T) :
    (Query.Sel φ q).evaluate d
      = @Multiset.filter _ φ.eval φ.evalDecidable (q.evaluate d) := by
  rw [Query.evaluate]

/-- **cross product**: `⟦q₁ × q₂⟧_I ≝ ⟦q₁⟧_I × ⟦q₂⟧_I`. -/
theorem eval_prod {hn : k₁ + k₂ = n} (q₁ : Query T k₁) (q₂ : Query T k₂) (d : Database T) :
    (Query.Prod (hn := hn) q₁ q₂).evaluate d
      = ((q₁.evaluate d) * (q₂.evaluate d)).cast hn := by
  rw [Query.evaluate]

/-- **multiset sum**: `⟦q₁ ⊎ q₂⟧_I ≝ ⟦q₁⟧_I ⊎ ⟦q₂⟧_I`. -/
theorem eval_sum (q₁ q₂ : Query T n) (d : Database T) :
    (Query.Sum q₁ q₂).evaluate d = q₁.evaluate d + q₂.evaluate d := by
  rw [Query.evaluate]

/-- **duplicate elimination**: `⟦ε(q)⟧_I` maps `t` to `1` when `⟦q⟧_I(t) > 0`
and to `0` otherwise. -/
theorem eval_dedup (q : Query T n) (d : Database T) :
    (Query.Dedup q).evaluate d = (q.evaluate d).dedup := by
  rw [Query.evaluate]

/-- **multiset difference**: every copy of a tuple occurring at all in `⟦q₂⟧_I`
is removed from `⟦q₁⟧_I`. -/
theorem eval_diff (q₁ q₂ : Query T n) (d : Database T) (r₂ : Multiset (Tuple T n))
    (hr : r₂ = q₂.evaluate d) :
    (Query.Diff q₁ q₂).evaluate d = (q₁.evaluate d).filter (fun u => u ∉ r₂) := by
  subst hr; rw [Query.evaluate]

/-! ## Semantics over annotated databases

The paper's `⟪·⟫_Î`: the same operators, with `⊕` on multiset sum and duplicate
elimination, `⊗` on cross product, and `⊖` on difference.

Anchor: Provenance/QueryAnnotatedDatabase.html#Query.evaluateAnnotated
-/

section Annotated

variable [SemiringWithMonus K] [DecidableEq K]

/-- **relation**: `⟪R⟫_Î ≝ Î(R)`. -/
theorem aeval_rel (R : String) (hq : (Query.Rel n R).source) (d : AnnotatedDatabase T K) :
    (Query.Rel n R).evaluateAnnotated hq d
      = (d.find n R).getD (∅ : Multiset (AnnotatedTuple T K n)) := by
  rw [Query.evaluateAnnotated]; cases d.find n R <;> rfl

/-- **projection**: the annotation rides along unchanged. -/
theorem aeval_proj (ts : Tuple (Term T k) n) (q : Query T k)
    (hq : (Query.Proj ts q).source) (d : AnnotatedDatabase T K) :
    (Query.Proj ts q).evaluateAnnotated hq d
      = (q.evaluateAnnotated (Query.sourceProj hq rfl) d).map
          (fun p => ⟨fun l => (ts l).eval p.fst, p.snd⟩) := by
  rw [Query.evaluateAnnotated]

/-- **selection**: the predicate reads the data part only. -/
theorem aeval_sel (φ : Selection T n) (q : Query T n) (hq : (Query.Sel φ q).source)
    (d : AnnotatedDatabase T K) :
    (Query.Sel φ q).evaluateAnnotated hq d
      = @Multiset.filter _ (fun p => φ.eval p.fst) φ.evalDecidableAnnotated
          (q.evaluateAnnotated (Query.sourceSel hq rfl) d) := by
  rw [Query.evaluateAnnotated]

/-- **cross product**: annotations multiply, `α ⊗ β`. -/
theorem aeval_prod {hn : k₁ + k₂ = n} (q₁ : Query T k₁) (q₂ : Query T k₂)
    (hq : (Query.Prod (hn := hn) q₁ q₂).source) (d : AnnotatedDatabase T K) :
    (Query.Prod (hn := hn) q₁ q₂).evaluateAnnotated hq d
      = Multiset.map
          (fun (xy : AnnotatedTuple T K k₁ × AnnotatedTuple T K k₂) =>
            (⟨Eq.mp (by simp [hn]; rfl) (Fin.append xy.1.fst xy.2.fst), xy.1.snd * xy.2.snd⟩ :
              AnnotatedTuple T K n))
          (Multiset.product (q₁.evaluateAnnotated (Query.sourceProd hq rfl).left d)
            (q₂.evaluateAnnotated (Query.sourceProd hq rfl).right d)) := by
  rw [Query.evaluateAnnotated]

/-- **multiset sum**: the two annotated relations are added. -/
theorem aeval_sum (q₁ q₂ : Query T n) (hq : (Query.Sum q₁ q₂).source)
    (d : AnnotatedDatabase T K) :
    (Query.Sum q₁ q₂).evaluateAnnotated hq d
      = q₁.evaluateAnnotated (Query.sourceSum hq rfl).left d
        + q₂.evaluateAnnotated (Query.sourceSum hq rfl).right d := by
  rw [Query.evaluateAnnotated]

/-- **duplicate elimination**: the copies of a tuple are collapsed into one,
annotated by the `⊕`-sum of their annotations. -/
theorem aeval_dedup (q : Query T n) (hq : (Query.Dedup q).source)
    (d : AnnotatedDatabase T K) :
    (Query.Dedup q).evaluateAnnotated hq d
      = Multiset.ofList (groupByKey (q.evaluateAnnotated (Query.sourceDedup hq rfl) d)).val := by
  rw [Query.evaluateAnnotated]

/-- **multiset difference**: a tuple of the left argument keeps its slot, with
annotation `α ⊖ Σβ` where `Σβ` is the `⊕`-sum of the annotations of its copies
in the right argument. -/
theorem aeval_diff (q₁ q₂ : Query T n) (hq : (Query.Diff q₁ q₂).source)
    (d : AnnotatedDatabase T K) :
    (Query.Diff q₁ q₂).evaluateAnnotated hq d
      = (q₁.evaluateAnnotated (Query.sourceDiff hq rfl).left d).map
          (fun (u, a) => (u, a - ((((groupByKey
              (q₂.evaluateAnnotated (Query.sourceDiff hq rfl).right d)).val.find?
                (·.1 = u)).map Prod.snd).getD 0))) := by
  rw [Query.evaluateAnnotated]; rfl

end Annotated

/-! ## The rewriting rules (R1)–(R4)

The paper gives five rules; (R5), aggregation, is not part of this classical
rewriting (see *Scope* above). Each rule below is stated as the equation it is:
applying the rewriting to an operator produces exactly the paper's right-hand
side. The annotation lives in the last column, so a query of arity `n` rewrites
to one of arity `n+1`.

Anchor: Provenance/QueryRewriting.html#query.Rewriting
-/

open Query in
/-- **(R1) projection.** `Π_{t₁,…,t_n}(q)` is rewritten to
`Π_{t₁,…,t_n,#(k+1)}(q̂)`: the terms are carried over unchanged and the
annotation column of the rewritten argument is appended. -/
theorem rule_projection (ts : Tuple (Term T k) n) (q : Query T k)
    (hq : (Query.Proj ts q).source) :
    (Query.Proj ts q).rewriting (K := K) hq
      = Proj
          (fun l : Fin (n + 1) =>
            if h : (l : ℕ) < n then (ts ⟨l, h⟩).castToAnnotatedTuple
            else Term.index (Fin.last q.arity))
          (q.rewriting (Query.sourceProj hq rfl)) :=
  rfl

open Query in
/-- **(R2) cross product.** `q₁ × q₂` is rewritten to
`Π_{#1,…,#k₁,#(k₁+2),…,#(k₁+k₂+1),#(k₁+1) ⊗ #(k₁+k₂+2)}(q̂₁ × q̂₂)`: the two
data blocks are kept, the two annotation columns are multiplied. -/
theorem rule_product {hn : n₁ + n₂ = n} (q₁ : Query T n₁) (q₂ : Query T n₂)
    (hq : (Query.Prod (hn := hn) q₁ q₂).source) :
    (Query.Prod (hn := hn) q₁ q₂).rewriting (K := K) hq
      = Proj
          (fun l : Fin (n + 1) =>
            if (l : ℕ) < n₁ then #(l.castLE (by simp))
            else if ((l : ℕ) < n : Prop) then #(Fin.ofNat _ ((l : ℕ) + 1))
            else Term.mul #(Fin.ofNat _ n₁) #(Fin.ofNat _ (n + 1)))
          (@Query.Prod (T ⊕ K) (n₁ + 1) (n₂ + 1) (n + 2) (by omega)
            (q₁.rewriting (Query.sourceProd hq rfl).left)
            (q₂.rewriting (Query.sourceProd hq rfl).right)) :=
  rfl

open Query in
/-- **(R3) duplicate elimination.** `ε(q)` is rewritten to
`γ_{1,…,k}[#(k+1) : ⊕](q̂)`: group by the data columns and `⊕`-sum the
annotation column. This is the rule that makes duplicate elimination the
`⊕`-gate creator, and `ProvSum` is its target operator. -/
theorem rule_dupelim (q : Query T n) (hq : (Query.Dedup q).source) :
    (Query.Dedup q).rewriting (K := K) hq
      = ProvSum (fun l : Fin n => l.castLE (by simp)) #(Fin.last n)
          (q.rewriting (Query.sourceDedup hq rfl)) :=
  rfl

open Query in
/-- **(R4) multiset difference.** `q₁ - q₂` is rewritten to the multiset sum of
two branches: the tuples of `q̂₁` whose data part survives the set difference of
the two data projections, carrying their annotation unchanged; and the tuples of
`q̂₁` matched against the `⊕`-aggregated `q̂₂`, carrying `α ⊖ Σβ`. Both branches
are joins on the `k` data columns. -/
theorem rule_difference (q₁ q₂ : Query T n) (hq : (Query.Diff q₁ q₂).source) :
    (Query.Diff q₁ q₂).rewriting (K := K) hq
      = (let q'₁ := q₁.rewriting (K := K) (Query.sourceDiff hq rfl).left
         let q'₂ := q₂.rewriting (K := K) (Query.sourceDiff hq rfl).right
         let joinCond₁ :=
           ((List.range n).map
             (fun j => @Selection.BT (T ⊕ K) (2 * n + 1)
               (#(Fin.ofNat _ j) == #(Fin.ofNat _ (j + n + 1))))).foldr
             (fun t t' => Selection.And t t') Selection.True
         let prod₁t := fun r => Sel joinCond₁ (@Query.Prod _ (n + 1) n (2 * n + 1) (by omega) q'₁ r)
         let prod₁r :=
           Dedup (Diff (Proj (fun j : Fin n => Term.index (j.castLE (Nat.le_succ _))) q'₁)
                       (Proj (fun j : Fin n => Term.index (j.castLE (Nat.le_succ _))) q'₂))
         let prod₁ := prod₁t prod₁r
         let joinCond₂ :=
           ((List.range n).map
             (fun j => @Selection.BT (T ⊕ K) (2 * n + 2)
               (#(Fin.ofNat _ j) == #(Fin.ofNat _ (j + n + 1))))).foldr
             (fun t t' => Selection.And t t') Selection.True
         let prod₂t := fun r => Sel joinCond₂ (@Query.Prod _ (n + 1) (n + 1) (2 * n + 2) (by omega) q'₁ r)
         let prod₂r := ProvSum (fun j : Fin n => j.castLE (by simp)) #(Fin.last n) q'₂
         let prod₂ := prod₂t prod₂r
         let ts₁ := fun j : Fin (n + 1) => #(j.castLE (by omega))
         let ts₂ := fun j : Fin (n + 1) =>
           if (j : ℕ) < n then #(j.castLE (by omega))
           else Term.sub #(Fin.ofNat _ n) #(Fin.last (2 * n + 1))
         Sum (Proj ts₁ prod₁) (Proj ts₂ prod₂)) :=
  rfl

/-! ## Correctness of the rewriting

The paper's theorem: let `D` be a schema, `q` a query over `D`, `K` an
appropriate algebraic structure, `Î` a `K`-instance over `D`, and `q̂` the query
obtained by applying the rewriting rules recursively bottom up. Then
`⟪q⟫_Î = ⟦q̂⟧_Î`.

The equality is between an annotated relation and a plain one, so it is stated
through the encoding that puts the annotation in the last column
(`toComposite`), which is what "the same relation" means once the rewriting has
moved the annotation into the data.

Anchor: Provenance/QueryRewriting.html#Query.rewriting_valid
-/

/-- `⟪q⟫_Î = ⟦q̂⟧_Î`, for `q` in the fragment the rules (R1)–(R4) cover. -/
theorem rewriting_valid [SemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
    (q : Query T n) (hq : q.source) (d : AnnotatedDatabase T K) :
    (q.evaluateAnnotated hq d).toComposite = (q.rewriting hq).evaluate d.toComposite :=
  Query.rewriting_valid q hq d

end Icde2026
