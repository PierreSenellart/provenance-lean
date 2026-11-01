/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.BooleanSemiring
public import Provenance.FragQueryMeta
public import Provenance.Semirings.How
public import Provenance.AggQueryHom
public import Provenance.AggQueryProbability
public import Provenance.RecursionBasis
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.Bound.Init
import all Provenance.AggQuery
import all Provenance.AggQueryProbability
import all Provenance.AnnotatedMuUnion
import all Provenance.DerivedAnn
import all Provenance.FragQuery
import all Provenance.FragQueryMeta
import all Provenance.QueryAnnotatedDatabase
import all Provenance.SupportAdequacy

/-!
# Graded extensionality

In which m-semirings does the annotation of a tuple depend on the query
alone and not on its spelling? Call `K` *extensional for a class of
queries* when any two queries of the class with regular output columns
and the same plain semantics on every instance give, on every
`K`-instance, the same `K`-relation after collapsing the copies of each
tuple by `⊕` – the K-relation of Green, Karvounarakis and Tannen
(`AnnotatedRelation.annSum`). The answer is graded along the first levels
of the chain of fragments of the sql-semantics paper, and the grading says
which construct asks for which axiom:

* **(a)** every commutative m-semiring is extensional for `F₀` – projection,
  selection, product, apply, union and the constant relations
  (`extensional_level0`); and on the classical layer, where the evaluator
  is defined over every m-semiring, the commutativity of `⊗` is what a
  swapped product forces (`mul_comm_of_extensional_swap`);
* **(b)** `K` is extensional for `F₁` – `F₀` with duplicate elimination
  and the semijoin, SQL's `EXISTS` and `IN` – iff it is a lattice
  m-semiring: `⊗` idempotent and `K` absorptive, so that `(K, ⊕, ⊗)` is
  a bounded distributive lattice (`extensional_level1_iff`);
* **(c)** `K` is extensional for `F₂` – with the difference and the
  antijoin, `EXCEPT`, `NOT EXISTS` and `NOT IN` – iff it is a Boolean
  m-semiring, whatever its `δ` (`extensional_level2_iff`);
* **(d)** `K` is extensional for the whole recursion-free algebra –
  grouping, windows, nested aggregation included – iff it is a Boolean
  m-semiring whose `δ` is the identity (`extensional_tame_iff`).

Each axiom is forced by one pair of equivalent queries over a one-tuple
instance, written with the constructs of the level that forces it: the
two sides annotate the one output tuple by `a` and `a ⊕ a`, `a` and
`a ⊗ a`, `a` and `a ⊕ a ⊗ b`, `𝟘` and `a ⊗ (𝟙 ⊖ a)`, `a` and `δ(a)`. Conversely,
on `F₀` a copy of an output tuple is annotated by a product of the
annotations it is derived from; over `ℕ[K]`, the universal commutative
semiring, two queries with the same multiplicities on every instance
give each tuple the same polynomial, by a polynomial identity over `ℕ`
(`FragQueryIn.semPlain_unfold`, `MvPolynomial.funext_set`), and the
universal homomorphism carries that to `K`. Above `F₀`, a lattice
m-semiring has enough homomorphisms onto `𝔹` to separate its elements
(`IsLatticeSemiring.eq_of_forall_point`); those of a Boolean m-semiring
preserve the monus and, when `δ` is the identity, `δ`; and at each such
point the annotated semantics is the plain semantics of the support
(`FragQueryIn.mem_support_sem`, `AggQueryIn.genRandomWorld_evaluate`).

The levels `F₀`, `F₁` and `F₂` are the syntax `FragQueryIn` of
`Provenance.FragQuery`, read in the general syntax through
`FragQueryIn.toAgg`; the whole algebra is the general syntax under the
hygiene the metatheory asks of a query (`AggQueryIn.Tame`), without
recursion, so that nothing has to settle.
-/

@[expose] public section

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-! ## Extensionality -/

/-- **`K` is extensional for the queries satisfying `F`**: two such queries
with the same plain semantics on every instance collapse, on every
`K`-instance, to the same `K`-relation. -/
def Extensional (T : Type) [ValueType T] (K : Type) [CommSemiringWithMonus K] [DecidableEq K]
    [HasAltLinearOrder K] (F : ∀ {n : ℕ}, AggQuery T n (ColKind.allReg n) → Prop) : Prop :=
  ∀ {n : ℕ} (q₁ q₂ : AggQuery T n (ColKind.allReg n)), F q₁ → F q₂ → q₁.PlainEquiv q₂ →
    ∀ (d : AnnotatedDatabase T K) (u : Tuple T n),
      (q₁.evaluateAnnotated d).annSum u = (q₂.evaluateAnnotated d).annSum u

/-- **The queries of `F₀`**, in the general syntax: the translations of
the level-`0` queries of the fragment syntax. -/
def AggQueryIn.InLevel0 {n : ℕ} (q : AggQuery T n (ColKind.allReg n)) : Prop :=
  ∃ e : FragQuery T n, e.level0 ∧ e.toAgg = q

/-- **The queries of `F₁`.** -/
def AggQueryIn.InLevel1 {n : ℕ} (q : AggQuery T n (ColKind.allReg n)) : Prop :=
  ∃ e : FragQuery T n, e.level1 ∧ e.toAgg = q

/-- **The queries of `F₂`**: every translation of the fragment syntax. -/
def AggQueryIn.InLevel2 {n : ℕ} (q : AggQuery T n (ColKind.allReg n)) : Prop :=
  ∃ e : FragQuery T n, e.toAgg = q

/-- **A tame query of the whole algebra**: recursion-free, and with the
hygiene the metatheory asks – no provenance sum, hygienic, well-kinded,
with distinct labels, recorded reads, source columns and frames
containing their row. These are the hypotheses of the homomorphism
commutation (`AggQueryIn.evaluateAnnotated_hom`) and of the random-world
commutation (`AggQueryIn.genRandomWorld_evaluate`) of the general
evaluator. -/
def AggQueryIn.Tame {n : ℕ} (q : AggQuery T n (ColKind.allReg n)) : Prop :=
  q.noRec ∧ q.noProvSum ∧ q.hygienic ∧ q.wellKinded (ColKind.allReg 0) HoleKinds.empty
    ∧ q.labelsDistinct ∧ q.readsRecorded ∧ q.sourceCols ∧ q.allFramesContainSelf

/-- The levels are nested. -/
theorem AggQueryIn.inLevel1_of_inLevel0 {n : ℕ} {q : AggQuery T n (ColKind.allReg n)}
    (h : q.InLevel0) : q.InLevel1 :=
  let ⟨e, he, hq⟩ := h
  ⟨e, FragQueryIn.level1_of_level0 e he, hq⟩

theorem AggQueryIn.inLevel2_of_inLevel1 {n : ℕ} {q : AggQuery T n (ColKind.allReg n)}
    (h : q.InLevel1) : q.InLevel2 :=
  let ⟨e, _, hq⟩ := h
  ⟨e, hq⟩

/-- Extensionality is antitone in the class of queries. -/
theorem Extensional.mono {F G : ∀ {n : ℕ}, AggQuery T n (ColKind.allReg n) → Prop}
    (hFG : ∀ {n : ℕ} (q : AggQuery T n (ColKind.allReg n)), F q → G q)
    (hG : Extensional T K G) : Extensional T K F :=
  fun q₁ q₂ h₁ h₂ hpe d u => hG q₁ q₂ (hFG q₁ h₁) (hFG q₂ h₂) hpe d u

/-! ## The plain equivalence of translated queries -/

namespace FragQueryIn

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Two translated queries are plainly equivalent exactly when their
closed-form plain semantics agree on every instance. -/
theorem toAgg_plainEquiv_iff {n : ℕ} (e₁ e₂ : FragQuery T n) :
    e₁.toAgg.PlainEquiv e₂.toAgg ↔ ∀ (D : Database T) (γ : Fin 0 → T),
      e₁.semPlain D γ = e₂.semPlain D γ := by
  unfold AggQueryIn.PlainEquiv
  constructor
  · intro h D γ
    rw [← toAgg_evaluatePlain e₁ D γ, ← toAgg_evaluatePlain e₂ D γ]
    exact h D γ
  · intro h D γ
    rw [toAgg_evaluatePlain e₁ D γ, toAgg_evaluatePlain e₂ D γ]
    exact h D γ

/-- The collapsed annotations of a translated query, in closed form. -/
theorem annSum_toAgg_evaluateAnnotated {n : ℕ} (e : FragQuery T n)
    (habs : e.hasSemijoin → absorptive K) (d : AnnotatedDatabase T K) (u : Tuple T n) :
    (e.toAgg.evaluateAnnotated d).annSum u = (e.sem d (fun _ => 0)).annSum u := by
  rw [toAgg_evaluateAnnotated e habs d (fun _ => 0) {}]

end FragQueryIn

/-! ## (a) Every commutative m-semiring is extensional for `F₀`

The argument is in `ℕ[K]`, the polynomial semiring over the
annotations themselves, read as indeterminates: the instance `d` is the
image of the instance `d₀` carrying `X a` where `d` carries `a`, under the
universal homomorphism sending `X a` to `a`. Over `d₀` the collapsed
annotation of a tuple is a polynomial, and evaluating it at a valuation
`n : K → ℕ` is the multiplicity of the tuple on the plain instance in
which each copy carrying `a` is repeated `n a` times. Two queries with
the same plain semantics everywhere have the same multiplicities, so the
two polynomials agree on all of `ℕ^K`, and a polynomial identity
settles it. -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Reading annotations through two functions in turn. -/
private theorem AnnotatedRelation.mapAnn_mapAnn {K₁ K₂ K₃ : Type} (f : K₁ → K₂) (g : K₂ → K₃)
    {n : ℕ} (r : AnnotatedRelation T K₁ n) : (r.mapAnn f).mapAnn g = r.mapAnn (g ∘ f) := by
  unfold AnnotatedRelation.mapAnn
  rw [Multiset.map_map]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem AnnotatedDatabase.mapAnn_mapAnn {K₁ K₂ K₃ : Type} (f : K₁ → K₂) (g : K₂ → K₃)
    (d : AnnotatedDatabase T K₁) : (d.mapAnn f).mapAnn g = d.mapAnn (g ∘ f) := by
  unfold AnnotatedDatabase.mapAnn
  rw [List.map_map]
  refine List.map_congr_left (fun e _ => ?_)
  exact congrArg (fun r : AnnotatedRelation T K₃ e.snd.fst =>
    ((e.fst, ⟨e.snd.fst, r⟩) : String × Σ n, AnnotatedRelation T K₃ n))
    (AnnotatedRelation.mapAnn_mapAnn f g e.snd.snd)

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Reading annotations through the identity. -/
private theorem AnnotatedDatabase.mapAnn_id' (d : AnnotatedDatabase T K) (f : K → K)
    (hf : ∀ a, f a = a) : d.mapAnn f = d := by
  unfold AnnotatedDatabase.mapAnn
  refine (List.map_congr_left (fun e _ => ?_)).trans (List.map_id _)
  show (e.fst, ⟨e.snd.fst, e.snd.snd.mapAnn f⟩) = e
  unfold AnnotatedRelation.mapAnn
  rw [show e.snd.snd.map (fun p => ((p.1, f p.2) : AnnotatedTuple T K _)) = e.snd.snd from
    (Multiset.map_congr rfl (fun p _ => by rw [hf]; rfl)).trans (Multiset.map_id _)]

/-- **A polynomial over `ℕ` is determined by its values on `ℕ^ι`.** The
polynomial is mapped to `ℤ`, an infinite domain, where Mathlib's
identity theorem applies to the box `ℕ^ι`. -/
private theorem MvPolynomial.ext_of_forall_eval_nat {ι : Type} {p q : MvPolynomial ι ℕ}
    (h : ∀ x : ι → ℕ, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q := by
  refine MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective ?_
  refine MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℤ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective) (fun x hx => ?_)
  choose n hn using fun i => hx i (Set.mem_univ i)
  have hxn : x = fun i => ((n i : ℕ) : ℤ) := by
    funext i
    exact (hn i).symm
  subst hxn
  have key : ∀ r : MvPolynomial ι ℕ,
      MvPolynomial.eval (fun i => ((n i : ℕ) : ℤ)) (MvPolynomial.map (Nat.castRingHom ℤ) r)
        = ((MvPolynomial.eval n r : ℕ) : ℤ) := by
    intro r
    rw [MvPolynomial.eval_map]
    have := MvPolynomial.eval₂_comp_left (Nat.castRingHom ℤ) (RingHom.id ℕ) n r
    rw [RingHom.comp_id] at this
    exact this.symm
  rw [key, key, h n]

/-- **Every commutative m-semiring is extensional for `F₀`.** -/
theorem extensional_level0 : Extensional T K AggQueryIn.InLevel0 := by
  rintro n q₁ q₂ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩ hpe d u
  rw [FragQueryIn.annSum_toAgg_evaluateAnnotated e₁
      (fun h => (FragQueryIn.not_hasSemijoin_of_level0 e₁ he₁ h).elim),
    FragQueryIn.annSum_toAgg_evaluateAnnotated e₂
      (fun h => (FragQueryIn.not_hasSemijoin_of_level0 e₂ he₂ h).elim)]
  rw [FragQueryIn.toAgg_plainEquiv_iff] at hpe
  -- the instance over `ℕ[K]`, and the homomorphism back
  obtain ⟨h, hX⟩ := How.universal (X := K) K (fun a => a)
  set d₀ : AnnotatedDatabase T (MvPolynomial K ℕ) := d.mapAnn MvPolynomial.X with hd₀
  have hd : d₀.mapAnn h = d := by
    rw [hd₀, AnnotatedDatabase.mapAnn_mapAnn]
    exact AnnotatedDatabase.mapAnn_id' d _ (fun a => hX a)
  -- the two polynomials agree at every valuation
  have hpoly : (e₁.sem d₀ (fun _ => 0)).annSum u = (e₂.sem d₀ (fun _ => 0)).annSum u := by
    refine MvPolynomial.ext_of_forall_eval_nat (fun v => ?_)
    have hv : ∀ e : FragQuery T n, e.level0 →
        MvPolynomial.eval v ((e.sem d₀ (fun _ => 0)).annSum u)
          = Multiset.count u (e.semPlain (d₀.mapAnn (MvPolynomial.eval v)).unfold (fun _ => 0)) := by
      intro e he
      rw [FragQueryIn.semPlain_unfold e he, AnnotatedRelation.count_unfold,
        FragQueryIn.sem_mapAnn (MvPolynomial.eval v) e
          (fun hm => (FragQueryIn.not_hasMonus_of_level1 e
            (FragQueryIn.level1_of_level0 e he) hm).elim),
        AnnotatedRelation.annSum_mapAnn]
    rw [hv e₁ he₁, hv e₂ he₂, hpe]
  -- and so do their images in `K`
  rw [← hd, FragQueryIn.sem_mapAnn h e₁
      (fun hm => (FragQueryIn.not_hasMonus_of_level1 e₁
        (FragQueryIn.level1_of_level0 e₁ he₁) hm).elim),
    FragQueryIn.sem_mapAnn h e₂
      (fun hm => (FragQueryIn.not_hasMonus_of_level1 e₂
        (FragQueryIn.level1_of_level0 e₂ he₂) hm).elim),
    AnnotatedRelation.annSum_mapAnn, AnnotatedRelation.annSum_mapAnn, hpoly]


/-! ## The forcing pairs

Each axiom is forced by one pair of queries with the same plain
semantics on every instance, read on a one-tuple instance: `R` holding
`![x]` annotated `a`. -/

/-- The instance with one relation `R` holding one tuple, annotated `a`. -/
def oneTupleDb (x : T) (a : K) : AnnotatedDatabase T K :=
  [("R", ⟨1, ({(![x], a)} : Multiset (AnnotatedTuple T K 1))⟩)]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem oneTupleDb_find (x : T) (a : K) :
    (oneTupleDb x a).find 1 "R" = some ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) := rfl

/-- The instance with two relations `R` and `S`, each holding the one
tuple `![x]`, annotated `a` and `b`. -/
def twoRelDb (x : T) (a b : K) : AnnotatedDatabase T K :=
  [("R", ⟨1, ({(![x], a)} : Multiset (AnnotatedTuple T K 1))⟩),
   ("S", ⟨1, ({(![x], b)} : Multiset (AnnotatedTuple T K 1))⟩)]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem twoRelDb_find_R (x : T) (a b : K) :
    ((twoRelDb x a b).find 1 "R").getD (0 : Multiset (AnnotatedTuple T K 1))
      = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) := rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem twoRelDb_find_S (x : T) (a b : K) :
    ((twoRelDb x a b).find 1 "S").getD (0 : Multiset (AnnotatedTuple T K 1))
      = ({(![x], b)} : Multiset (AnnotatedTuple T K 1)) := rfl

omit [HasAltLinearOrder K] [DecidableEq K] in
/-- The collapsed annotation of a one-tuple relation. -/
private theorem annSum_singleton (p : AnnotatedTuple T K n) (u : Tuple T n) :
    AnnotatedRelation.annSum ({p} : Multiset (AnnotatedTuple T K n)) u
      = if p.1 = u then p.2 else 0 := by
  unfold AnnotatedRelation.annSum
  rw [Multiset.filter_singleton]
  split_ifs <;> simp

omit [HasAltLinearOrder K] [DecidableEq K] in
private theorem annSum_add (r s : AnnotatedRelation T K n) (u : Tuple T n) :
    AnnotatedRelation.annSum (r + s) u = r.annSum u + s.annSum u := by
  unfold AnnotatedRelation.annSum
  rw [Multiset.filter_add, Multiset.map_add, Multiset.sum_add]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
/-- A tuple of arity one is the vector of its one value. -/
private theorem Tuple.eq_vecCons (u : Tuple T 1) : ![u 0] = u := by
  funext j
  rw [Fin.fin_one_eq_zero j]
  rfl

/-! ### (a) on the classical layer: the commutativity of `⊗`

The general evaluator is defined over commutative m-semirings, so the
commutativity of `⊗` is not an axiom it can force. The classical evaluator
`Query.evaluateAnnotated` is defined over every m-semiring, and there the
swapped product does force it: `Π₂,₁(R × S)` and `S × R` have the same
plain semantics on every instance, and annotate the one tuple of a
two-relation instance by `a ⊗ b` and `b ⊗ a`. -/

section Classical

variable {K₀ : Type} [SemiringWithMonus K₀] [DecidableEq K₀]

/-- `Π₂,₁(R × S)`, in the classical syntax. -/
def swapProd₁ : Query T 2 :=
  Query.Proj ![TermIn.index 1, TermIn.index 0]
    (@Query.Prod T 1 1 2 rfl (Query.Rel 1 "R") (Query.Rel 1 "S"))

/-- `S × R`. -/
def swapProd₂ : Query T 2 := @Query.Prod T 1 1 2 rfl (Query.Rel 1 "S") (Query.Rel 1 "R")

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
theorem swapProd₁_source : (swapProd₁ (T := T)).source := ⟨trivial, trivial⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
theorem swapProd₂_source : (swapProd₂ (T := T)).source := ⟨trivial, trivial⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The K-relation an annotated relation collapses to**, over any
m-semiring: the `⊕`-sum of the annotations of the copies of a tuple. On a
commutative m-semiring it is `AnnotatedRelation.annSum`. -/
def _root_.AnnotatedRelation.collapse {n : ℕ} (r : AnnotatedRelation T K₀ n) (u : Tuple T n) : K₀ :=
  (Multiset.map Prod.snd
    (Multiset.filter (fun p : AnnotatedTuple T K₀ n => p.1 = u) r)).sum

omit [HasAltLinearOrder K] [DecidableEq K] in
/-- On a commutative m-semiring the collapse is `annSum`. -/
theorem _root_.AnnotatedRelation.collapse_eq_annSum {n : ℕ} (r : AnnotatedRelation T K n)
    (u : Tuple T n) : r.collapse u = r.annSum u := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [DecidableEq K₀] in
private theorem collapse_singleton {n : ℕ} (p : AnnotatedTuple T K₀ n) (u : Tuple T n) :
    AnnotatedRelation.collapse ({p} : Multiset (AnnotatedTuple T K₀ n)) u
      = if p.1 = u then p.2 else 0 := by
  unfold AnnotatedRelation.collapse
  rw [Multiset.filter_singleton]
  split_ifs <;> simp

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Reading the two columns of an appended pair back in the other order
appends the pair the other way. -/
private theorem swap_append (u v : Tuple T 1) :
    (fun k : Fin 2 => (![TermIn.index 1, TermIn.index 0] k : Term T 2).eval (Fin.append u v))
      = Fin.append v u := by
  funext k
  refine Fin.addCases (m := 1) (n := 1) (fun j => ?_) (fun j => ?_) k
  · rw [Fin.fin_one_eq_zero j, Fin.append_left]
    show Fin.append u v (Fin.natAdd 1 0) = v 0
    rw [Fin.append_right]
  · rw [Fin.fin_one_eq_zero j, Fin.append_right]
    show Fin.append u v (Fin.castAdd 1 0) = u 0
    rw [Fin.append_left]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Swapping the columns of a product of two relations of arity one
is the product the other way. -/
private theorem map_swap_mul (R S : Relation T 1) :
    Multiset.map (fun t : Tuple T 2 => fun k : Fin 2 =>
        (![TermIn.index 1, TermIn.index 0] k : Term T 2).eval t) (R * S)
      = S * R := by
  show Multiset.map _ (Multiset.map _ (Multiset.product R S))
    = Multiset.map _ (Multiset.product S R)
  rw [Multiset.map_map, show Multiset.product S R = (Multiset.product R S).map Prod.swap from
    (Multiset.map_swap_product R S).symm, Multiset.map_map]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  obtain ⟨u, v⟩ := p
  exact swap_append u v

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The two sides of the pair have the same plain semantics** on every
instance. -/
theorem swapProd_evaluate (D : Database T) :
    (swapProd₁ (T := T)).evaluate D = swapProd₂.evaluate D := by
  unfold swapProd₁ swapProd₂
  simp only [Query.evaluate]
  exact map_swap_mul _ _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [SemiringWithMonus K₀] [DecidableEq K₀] in
private theorem twoRelDb_find_R' (x : T) (a b : K₀) :
    (twoRelDb x a b).find 1 "R" = some ({(![x], a)} : Multiset (AnnotatedTuple T K₀ 1)) := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] [SemiringWithMonus K₀] [DecidableEq K₀] in
private theorem twoRelDb_find_S' (x : T) (a b : K₀) :
    (twoRelDb x a b).find 1 "S" = some ({(![x], b)} : Multiset (AnnotatedTuple T K₀ 1)) := rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- `Π₂,₁(R × S)` annotates its one tuple by `a ⊗ b`. -/
private theorem swapProd₁_evaluateAnnotated (x : T) (a b : K₀) :
    (swapProd₁ (T := T)).evaluateAnnotated swapProd₁_source (twoRelDb x a b)
      = ({(Fin.append ![x] ![x], a * b)} : Multiset (AnnotatedTuple T K₀ 2)) := by
  simp only [swapProd₁, Query.evaluateAnnotated, twoRelDb_find_R', twoRelDb_find_S']
  rw [show Multiset.product ({(![x], a)} : Multiset (AnnotatedTuple T K₀ 1))
      ({(![x], b)} : Multiset (AnnotatedTuple T K₀ 1)) = {((![x], a), (![x], b))} from
    Multiset.product_singleton (![x], a) (![x], b), Multiset.map_singleton, Multiset.map_singleton]
  refine congrArg (fun p : AnnotatedTuple T K₀ 2 => ({p} : Multiset _)) (Prod.ext ?_ rfl)
  exact swap_append ![x] ![x]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- `S × R` annotates it by `b ⊗ a`. -/
private theorem swapProd₂_evaluateAnnotated (x : T) (a b : K₀) :
    (swapProd₂ (T := T)).evaluateAnnotated swapProd₂_source (twoRelDb x a b)
      = ({(Fin.append ![x] ![x], b * a)} : Multiset (AnnotatedTuple T K₀ 2)) := by
  simp only [swapProd₂, Query.evaluateAnnotated, twoRelDb_find_R', twoRelDb_find_S']
  rw [show Multiset.product ({(![x], b)} : Multiset (AnnotatedTuple T K₀ 1))
      ({(![x], a)} : Multiset (AnnotatedTuple T K₀ 1)) = {((![x], b), (![x], a))} from
    Multiset.product_singleton (![x], b) (![x], a), Multiset.map_singleton]
  rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **`⊗` is commutative where the swapped product is extensional**: an
m-semiring over which `Π₂,₁(R × S)` and `S × R` collapse to the same
annotations on every instance has a commutative multiplication. -/
theorem mul_comm_of_extensional_swap
    (hext : ∀ (d : AnnotatedDatabase T K₀) (u : Tuple T 2),
      (swapProd₁.evaluateAnnotated swapProd₁_source d).collapse u
        = (swapProd₂.evaluateAnnotated swapProd₂_source d).collapse u) :
    ∀ a b : K₀, a * b = b * a := by
  intro a b
  have := hext (twoRelDb (0 : T) a b) (Fin.append ![0] ![0])
  rw [swapProd₁_evaluateAnnotated, swapProd₂_evaluateAnnotated, collapse_singleton,
    collapse_singleton] at this
  simpa using this

end Classical

namespace FragQueryIn

/-- The base relation `R` of arity `1`, in any context. -/
abbrev relRIn (c : ℕ) : FragQueryIn T c 1 := Rel 1 "R"

/-- The base relation `R` of arity `1`. -/
abbrev relR : FragQuery T 1 := Rel 1 "R"

/-- The base relation `S` of arity `1`. -/
abbrev relS : FragQuery T 1 := Rel 1 "S"

/-- The projection onto the first column of a relation of arity `2`. -/
abbrev projFst : Tuple (TermGIn T 0 (ColKind.allReg (1 + 1))) 1 :=
  ![TermGIn.index 0 rfl]


/-- **The pair forcing `a ⊕ a = a`**: `ε(R)` against `ε(R ⊎ R)`. -/
abbrev pairAddIdem₁ : FragQuery T 1 := Dedup relR
abbrev pairAddIdem₂ : FragQuery T 1 := Dedup (Sum relR relR)

/-- **The pair forcing `a ⊗ a = a`**: `ε(R)` against `ε(Π₁(R × R))`. -/
abbrev pairMulIdem₁ : FragQuery T 1 := Dedup relR
abbrev pairMulIdem₂ : FragQuery T 1 := Dedup (Proj projFst (Prod relR relR))

/-- **The pair forcing `a ⊕ a ⊗ b = a`**, and with it `𝟙 ⊕ b = 𝟙`: `ε(R)`
against `ε(R ⊎ Π₁(R × S))`. -/
abbrev pairAbs₁ : FragQuery T 1 := Dedup relR
abbrev pairAbs₂ : FragQuery T 1 := Dedup (Sum relR (Proj projFst (Prod relR relS)))

/-- The predicate matching the current row with a row of the subquery on
their one column: `R.x IS NOT DISTINCT FROM S.x`. -/
abbrev keyMatch : GenPredIn T (1 + 0) (ColKind.allReg 1) :=
  GenPredIn.cmp CompOp.syneq (TermGIn.outer 0) (TermGIn.index 0 rfl)

/-- **The pair forcing `a ⊗ (𝟙 ⊖ a) = 𝟘`**: the antijoin of `R` with itself
on its column, `WHERE NOT EXISTS`, against the empty query. -/
abbrev pairExcl₁ (cnt : SeqAggFunc T) (hc : cnt.Counts) : FragQuery T 1 :=
  Antijoin cnt hc keyMatch relR (relRIn (1 + 0))
abbrev pairExcl₂ (x : T) : FragQuery T 1 := Proj ![TermGIn.const x] Empty

/-! ### What the pairs annotate on the one-tuple instance -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem oneTupleDb_find_getD (x : T) (a : K) :
    ((oneTupleDb x a).find 1 "R").getD (0 : Multiset (AnnotatedTuple T K 1))
      = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) := rfl

omit [HasAltLinearOrder K] [DecidableEq K] in
private theorem sem_relR {c : ℕ} (x : T) (a : K) (γ : Fin c → T) :
    (relRIn c).sem (oneTupleDb x a) γ = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) := by
  simp only [sem, oneTupleDb_find_getD]

omit [HasAltLinearOrder K] [DecidableEq K] in
private theorem sem_relR_two (x : T) (a b : K) :
    relR.sem (twoRelDb x a b) (fun _ => 0) = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) := by
  simp only [sem, twoRelDb_find_R]

omit [HasAltLinearOrder K] [DecidableEq K] in
private theorem sem_relS_two (x : T) (a b : K) :
    relS.sem (twoRelDb x a b) (fun _ => 0) = ({(![x], b)} : Multiset (AnnotatedTuple T K 1)) := by
  simp only [sem, twoRelDb_find_S]

omit [HasAltLinearOrder K] [DecidableEq K] in
/-- The first column of the product of two one-tuple relations. -/
private theorem sem_proj_prod (x : T) (a b : K) (e₁ e₂ : FragQuery T 1) (d : AnnotatedDatabase T K)
    (h₁ : e₁.sem d (fun _ => 0) = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)))
    (h₂ : e₂.sem d (fun _ => 0) = ({(![x], b)} : Multiset (AnnotatedTuple T K 1))) :
    (Proj projFst (Prod e₁ e₂)).sem d (fun _ => 0)
      = ({(![x], a * b)} : Multiset (AnnotatedTuple T K 1)) := by
  simp only [sem, h₁, h₂]
  rw [show Multiset.product ({(![x], a)} : Multiset (AnnotatedTuple T K 1))
      ({(![x], b)} : Multiset (AnnotatedTuple T K 1)) = {((![x], a), (![x], b))} from
    Multiset.product_singleton (![x], a) (![x], b), Multiset.map_singleton, Multiset.map_singleton]
  refine congrArg (fun p : AnnotatedTuple T K 1 => ({p} : Multiset _)) (Prod.ext ?_ rfl)
  funext j
  rw [Fin.fin_one_eq_zero j]
  show Fin.append (![x]) (![x]) (Fin.castAdd 1 0) = x
  rw [Fin.append_left]
  rfl

omit [HasAltLinearOrder K] [DecidableEq K] in
private theorem annSum_cons {n : ℕ} (p : AnnotatedTuple T K n) (r : AnnotatedRelation T K n)
    (v : Tuple T n) :
    AnnotatedRelation.annSum (p ::ₘ (r : Multiset (AnnotatedTuple T K n))) v
      = (if p.1 = v then p.2 else 0) + r.annSum v := by
  unfold AnnotatedRelation.annSum
  rw [Multiset.filter_cons, Multiset.map_add, Multiset.sum_add]
  split_ifs <;> simp

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- The collapsed annotations of a relation built on a duplicate-free
multiset of tuples, each with the annotation a function gives it. -/
private theorem annSum_map_nodup {n : ℕ} (s : Multiset (Tuple T n)) (hs : s.Nodup)
    (f : Tuple T n → K) (v : Tuple T n) :
    AnnotatedRelation.annSum (s.map (fun u => ((u, f u) : AnnotatedTuple T K n))) v
      = if v ∈ s then f v else 0 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.notMem_zero, ite_false]
    rfl
  | cons u s ih =>
    rw [Multiset.map_cons, annSum_cons, ih (Multiset.nodup_cons.mp hs).2]
    by_cases huv : u = v
    · subst huv
      simp [(Multiset.nodup_cons.mp hs).1]
    · simp [huv, Ne.symm huv]

omit [DecidableEq K] [HasAltLinearOrder K] in
private theorem annSum_dedup (r : AnnotatedRelation T K 1) (x : T) (hx : ![x] ∈ r.map Prod.fst) :
    AnnotatedRelation.annSum (((r.map Prod.fst).dedup).map
      (fun u => ((u, r.annSum u) : AnnotatedTuple T K 1))) ![x] = r.annSum ![x] := by
  rw [annSum_map_nodup _ (Multiset.nodup_dedup _), ite_eq_left (Multiset.mem_dedup.mpr hx)]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- On the one-tuple instance, `ε(R)` annotates `![x]` by `a`. -/
private theorem annSum_pairAddIdem₁ (x : T) (a : K) :
    (pairAddIdem₁.sem (oneTupleDb x a) (fun _ => 0)).annSum ![x] = a := by
  simp only [sem, oneTupleDb_find_getD]
  rw [annSum_dedup _ x (Multiset.mem_map.mpr ⟨(![x], a), by simp, rfl⟩), annSum_singleton]
  simp

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- And `ε(R ⊎ R)` by `a ⊕ a`. -/
private theorem annSum_pairAddIdem₂ (x : T) (a : K) :
    (pairAddIdem₂.sem (oneTupleDb x a) (fun _ => 0)).annSum ![x] = a + a := by
  simp only [sem, oneTupleDb_find_getD]
  rw [annSum_dedup _ x (Multiset.mem_map.mpr ⟨(![x], a),
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _)), rfl⟩), annSum_add,
    annSum_singleton]
  simp

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- `ε(Π₁(R × R))` annotates `![x]` by `a ⊗ a`. -/
private theorem annSum_pairMulIdem₂ (x : T) (a : K) :
    (pairMulIdem₂.sem (oneTupleDb x a) (fun _ => 0)).annSum ![x] = a * a := by
  rw [show pairMulIdem₂.sem (oneTupleDb x a) (fun _ => 0)
      = (((Proj projFst (Prod relR relR)).sem (oneTupleDb x a) (fun _ => 0)).map Prod.fst).dedup.map
          (fun u => ((u, ((Proj projFst (Prod relR relR)).sem (oneTupleDb x a) (fun _ => 0)).annSum u)
            : AnnotatedTuple T K 1)) from rfl,
    sem_proj_prod x a a relR relR _ (sem_relR x a _) (sem_relR x a _),
    annSum_dedup _ x (Multiset.mem_map.mpr ⟨(![x], a * a), by simp, rfl⟩), annSum_singleton]
  simp

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- `ε(R)` annotates `![x]` by `a` on the two-relation instance. -/
private theorem annSum_pairAbs₁ (x : T) (a b : K) :
    (pairAbs₁.sem (twoRelDb x a b) (fun _ => 0)).annSum ![x] = a := by
  rw [show pairAbs₁.sem (twoRelDb x a b) (fun _ => 0)
      = ((relR.sem (twoRelDb x a b) (fun _ => 0)).map Prod.fst).dedup.map
          (fun u => ((u, (relR.sem (twoRelDb x a b) (fun _ => 0)).annSum u)
            : AnnotatedTuple T K 1)) from rfl,
    sem_relR_two, annSum_dedup _ x (Multiset.mem_map.mpr ⟨(![x], a), by simp, rfl⟩),
    annSum_singleton]
  simp

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- And `ε(R ⊎ Π₁(R × S))` by `a ⊕ a ⊗ b`. -/
private theorem annSum_pairAbs₂ (x : T) (a b : K) :
    (pairAbs₂.sem (twoRelDb x a b) (fun _ => 0)).annSum ![x] = a + a * b := by
  rw [show pairAbs₂.sem (twoRelDb x a b) (fun _ => 0)
      = (((Sum relR (Proj projFst (Prod relR relS))).sem (twoRelDb x a b) (fun _ => 0)).map
          Prod.fst).dedup.map
          (fun u => ((u, ((Sum relR (Proj projFst (Prod relR relS))).sem (twoRelDb x a b)
            (fun _ => 0)).annSum u) : AnnotatedTuple T K 1)) from rfl,
    show (Sum relR (Proj projFst (Prod relR relS))).sem (twoRelDb x a b) (fun _ => 0)
      = relR.sem (twoRelDb x a b) (fun _ => 0)
        + (Proj projFst (Prod relR relS)).sem (twoRelDb x a b) (fun _ => 0) from rfl,
    sem_proj_prod x a b relR relS _ (sem_relR_two x a b) (sem_relS_two x a b), sem_relR_two,
    annSum_dedup _ x (Multiset.mem_map.mpr ⟨(![x], a),
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _)), rfl⟩), annSum_add,
    annSum_singleton, annSum_singleton]
  simp

omit [HasAltLinearOrder K] in
/-- The key predicate holds of a row against itself. -/
private theorem keyMatch_holdsPlain (u : Tuple T 1) (γ : Fin 0 → T) :
    (keyMatch (T := T)).holdsPlain u (Fin.append u γ) := by
  unfold GenPredIn.holdsPlain GenPredIn.evalPlain3
  show CompOp.syneq.eval3 (Fin.append u γ (Fin.castAdd 0 0)) (u 0) = Kleene.true
  rw [Fin.append_left]
  simp [CompOp.eval3, CompOp.strict, CompOp.eval]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- The antijoin of `R` with itself annotates `![x]` by `a ⊗ (𝟙 ⊖ a)`. -/
private theorem annSum_pairExcl₁ (cnt : SeqAggFunc T) (hc : cnt.Counts) (x : T) (a : K) :
    ((pairExcl₁ cnt hc).sem (oneTupleDb x a) (fun _ => 0)).annSum ![x] = a * (1 - a) := by
  rw [show (pairExcl₁ cnt hc).sem (oneTupleDb x a) (fun _ => 0)
      = (relR.sem (oneTupleDb x a) (fun _ => 0)).map (fun p =>
          ((p.1, p.2 * (1 - (matchesAnn keyMatch (relRIn (1 + 0)).sem (oneTupleDb x a)
            (fun _ => 0) p.1).annTotal)) : AnnotatedTuple T K 1)) from rfl,
    sem_relR, Multiset.map_singleton, annSum_singleton]
  simp only [ite_true]
  unfold matchesAnn
  rw [sem_relR, Multiset.filter_singleton, ite_eq_left (keyMatch_holdsPlain ![x] _)]
  show a * (1 - AnnotatedRelation.annTotal ({(![x], a)} : Multiset (AnnotatedTuple T K 1))) = _
  unfold AnnotatedRelation.annTotal
  rw [Multiset.map_singleton, Multiset.sum_singleton]

omit [HasAltLinearOrder K] [DecidableEq K] in
/-- The empty query annotates nothing. -/
private theorem annSum_pairExcl₂ (x : T) (d : AnnotatedDatabase T K) (u : Tuple T 1) :
    ((pairExcl₂ x).sem d (fun _ => 0)).annSum u = 0 := by
  show AnnotatedRelation.annSum (Multiset.map _ (0 : Multiset (AnnotatedTuple T K 0))) u = 0
  rw [Multiset.map_zero]
  rfl

/-! ### The pairs are plainly equivalent -/

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The first column of a product: the rows of the left side, each as
often as the right side has rows. -/
private theorem mem_semPlain_proj_prod (e₁ e₂ : FragQuery T 1) (D : Database T) (γ : Fin 0 → T)
    (v : Tuple T 1) :
    v ∈ (show Multiset (Tuple T 1) from (Proj projFst (Prod e₁ e₂)).semPlain D γ)
      ↔ v ∈ (show Multiset (Tuple T 1) from e₁.semPlain D γ)
        ∧ (show Multiset (Tuple T 1) from e₂.semPlain D γ) ≠ 0 := by
  simp only [semPlain]
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨⟨u, u'⟩, huu', rfl⟩ := Multiset.mem_map.mp hw
    obtain ⟨hu, hu'⟩ := Multiset.mem_product.mp huu'
    refine ⟨?_, fun h0 => Multiset.eq_zero_iff_forall_notMem.mp h0 u' hu'⟩
    convert hu using 1
    funext j
    rw [Fin.fin_one_eq_zero j]
    show Fin.append u u' (Fin.castAdd 1 0) = u 0
    rw [Fin.append_left]
  · rintro ⟨hv, hne⟩
    obtain ⟨u', hu'⟩ := Multiset.exists_mem_of_ne_zero hne
    refine ⟨Fin.append v u', Multiset.mem_map.mpr ⟨(v, u'), Multiset.mem_product.mpr ⟨hv, hu'⟩, rfl⟩, ?_⟩
    funext j
    rw [Fin.fin_one_eq_zero j]
    show Fin.append v u' (Fin.castAdd 1 0) = v 0
    rw [Fin.append_left]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem pairAddIdem_plainEquiv :
    (pairAddIdem₁ (T := T)).toAgg.PlainEquiv pairAddIdem₂.toAgg := by
  rw [toAgg_plainEquiv_iff]
  intro D γ
  show (relR.semPlain D γ).dedup = (relR.semPlain D γ + relR.semPlain D γ).dedup
  exact Multiset.dedup_ext.mpr (fun v => by rw [Multiset.mem_add, or_self])

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem pairMulIdem_plainEquiv :
    (pairMulIdem₁ (T := T)).toAgg.PlainEquiv pairMulIdem₂.toAgg := by
  rw [toAgg_plainEquiv_iff]
  intro D γ
  show (relR.semPlain D γ).dedup = ((Proj projFst (Prod relR relR)).semPlain D γ).dedup
  refine Multiset.dedup_ext.mpr (fun v => ?_)
  rw [mem_semPlain_proj_prod]
  exact ⟨fun h => ⟨h, fun h0 => Multiset.eq_zero_iff_forall_notMem.mp h0 v h⟩, fun h => h.1⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem pairAbs_plainEquiv :
    (pairAbs₁ (T := T)).toAgg.PlainEquiv pairAbs₂.toAgg := by
  rw [toAgg_plainEquiv_iff]
  intro D γ
  show (relR.semPlain D γ).dedup
    = (relR.semPlain D γ + (Proj projFst (Prod relR relS)).semPlain D γ).dedup
  refine Multiset.dedup_ext.mpr (fun v => ?_)
  rw [Multiset.mem_add, mem_semPlain_proj_prod]
  exact ⟨fun h => Or.inl h, fun h => h.elim id (fun h => h.1)⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem pairExcl_plainEquiv (cnt : SeqAggFunc T) (hc : cnt.Counts) (x : T) :
    (pairExcl₁ cnt hc).toAgg.PlainEquiv (pairExcl₂ x).toAgg := by
  rw [toAgg_plainEquiv_iff]
  intro D γ
  show Multiset.filter _ (relR.semPlain D γ) = Multiset.map _ (0 : Multiset (Tuple T 0))
  rw [Multiset.map_zero, Multiset.filter_eq_nil]
  intro u hu h0
  have hmem : u ∈ (show Multiset (Tuple T 1) from
      matchesPlain keyMatch (relRIn (1 + 0)).semPlain D γ u) :=
    Multiset.mem_filter.mpr ⟨hu, keyMatch_holdsPlain u γ⟩
  rw [h0] at hmem
  exact Multiset.notMem_zero u hmem

end FragQueryIn

/-! ## What extensionality forces -/

open FragQueryIn in
/-- **`⊕` is idempotent** where `K` is extensional for a class holding
`ε(R)` and `ε(R ⊎ R)`. -/
theorem idempotent_of_extensional {F : ∀ {n : ℕ}, AggQuery T n (ColKind.allReg n) → Prop}
    (h₁ : F pairAddIdem₁.toAgg) (h₂ : F pairAddIdem₂.toAgg) (hext : Extensional T K F) :
    idempotent K := by
  intro a
  have := hext _ _ h₁ h₂ pairAddIdem_plainEquiv (oneTupleDb (0 : T) a) ![0]
  rw [annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_pairAddIdem₁, annSum_pairAddIdem₂] at this
  exact this.symm

open FragQueryIn in
/-- **`⊗` is idempotent** where `K` is extensional for a class holding
`ε(R)` and `ε(Π₁(R × R))`. -/
theorem mulIdempotent_of_extensional {F : ∀ {n : ℕ}, AggQuery T n (ColKind.allReg n) → Prop}
    (h₁ : F pairMulIdem₁.toAgg) (h₂ : F pairMulIdem₂.toAgg) (hext : Extensional T K F) :
    mulIdempotent K := by
  intro a
  have := hext _ _ h₁ h₂ pairMulIdem_plainEquiv (oneTupleDb (0 : T) a) ![0]
  rw [annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_pairAddIdem₁, annSum_pairMulIdem₂] at this
  exact this.symm

open FragQueryIn in
/-- **`K` is absorptive** where it is extensional for a class holding
`ε(R)` and `ε(R ⊎ Π₁(R × S))`: the pair gives `a ⊕ a ⊗ b = a`, and
`𝟙 ⊕ b = 𝟙` is its instance at `a = 𝟙`. -/
theorem absorptive_of_extensional {F : ∀ {n : ℕ}, AggQuery T n (ColKind.allReg n) → Prop}
    (h₁ : F pairAbs₁.toAgg) (h₂ : F pairAbs₂.toAgg)
    (hext : Extensional T K F) : absorptive K := by
  intro b
  have := hext _ _ h₁ h₂ pairAbs_plainEquiv (twoRelDb (0 : T) 1 b) ![0]
  rw [annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_pairAbs₁, annSum_pairAbs₂, one_mul] at this
  exact this.symm

open FragQueryIn in
/-- **`K` is exclusive** where it is extensional for a class holding the
antijoin of `R` with itself and the empty query. -/
theorem exclusive_of_extensional {F : ∀ {n : ℕ}, AggQuery T n (ColKind.allReg n) → Prop}
    (cnt : SeqAggFunc T) (hc : cnt.Counts)
    (h₁ : F (pairExcl₁ cnt hc).toAgg) (h₂ : F (pairExcl₂ (0 : T)).toAgg)
    (hext : Extensional T K F) : exclusive K := by
  intro a
  have := hext _ _ h₁ h₂ (pairExcl_plainEquiv cnt hc 0) (oneTupleDb (0 : T) a) ![0]
  rw [annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h),
    annSum_pairExcl₁, annSum_pairExcl₂] at this
  exact this

/-- **A counting aggregate**, for the antijoin pair: `nonzero` where the
sequence holds a non-null value, `𝟘` otherwise. -/
def SeqAggFunc.existsNonNull : SeqAggFunc T :=
  fun L => if L.any (fun v => !ValueType.isNull v) then ValueType.nonzero else 0

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem SeqAggFunc.existsNonNull_counts : (SeqAggFunc.existsNonNull (T := T)).Counts where
  not_null L := by
    unfold SeqAggFunc.existsNonNull
    split_ifs
    · exact ValueType.isNull_nonzero
    · exact ValueType.isNull_zero
  eq_zero L := by
    unfold SeqAggFunc.existsNonNull
    constructor
    · intro h v hv
      by_contra hnull
      have : L.any (fun v => !ValueType.isNull v) = true :=
        List.any_eq_true.mpr ⟨v, hv, by simpa using hnull⟩
      rw [ite_eq_left this] at h
      exact ValueType.nonzero_ne_zero h
    · intro h
      rw [ite_eq_right]
      intro hany
      obtain ⟨v, hv, hnn⟩ := List.any_eq_true.mp hany
      have := h v hv
      simp [this] at hnn

/-! ## (b) and (c): the converses, through the points -/

/-- **Over a lattice m-semiring, two translated queries with the same
plain semantics collapse to the same annotations**, provided the
translation reaches their semantics and the points pass through them.
The annotation of a tuple is determined by its images at the points of
`K`, and each image is a plain evaluation of the support. -/
theorem annSum_eq_of_points (hL : IsLatticeSemiring K) {n : ℕ} (e₁ e₂ : FragQuery T n)
    (hpe : e₁.toAgg.PlainEquiv e₂.toAgg)
    (hs₁ : ∀ f : K →+* Bool, e₁.hasMonus → ∀ x y : K, f (x - y) = f x - f y)
    (hs₂ : ∀ f : K →+* Bool, e₂.hasMonus → ∀ x y : K, f (x - y) = f x - f y)
    (d : AnnotatedDatabase T K) (u : Tuple T n) :
    (e₁.toAgg.evaluateAnnotated d).annSum u = (e₂.toAgg.evaluateAnnotated d).annSum u := by
  rw [FragQueryIn.annSum_toAgg_evaluateAnnotated e₁ (fun _ => hL.absorptive),
    FragQueryIn.annSum_toAgg_evaluateAnnotated e₂ (fun _ => hL.absorptive)]
  rw [FragQueryIn.toAgg_plainEquiv_iff] at hpe
  refine hL.eq_of_forall_point (fun f => ?_)
  have key : ∀ e : FragQuery T n, (e.hasMonus → ∀ x y : K, f (x - y) = f x - f y) →
      (f ((e.sem d (fun _ => 0)).annSum u) = true
        ↔ u ∈ (show Multiset (Tuple T n) from
            e.semPlain (d.mapAnn f).support (fun _ => 0))) := by
    intro e hs
    rw [← AnnotatedRelation.annSum_mapAnn, ← FragQueryIn.sem_mapAnn f e hs,
      AnnotatedRelation.annSum_eq_true_iff, FragQueryIn.mem_support_sem]
  rw [Bool.eq_iff_iff, key e₁ (hs₁ f), key e₂ (hs₂ f), hpe]

/-- **(b) `K` is extensional for `F₁` iff it is a lattice m-semiring.** -/
theorem extensional_level1_iff :
    Extensional T K AggQueryIn.InLevel1 ↔ IsLatticeSemiring K := by
  constructor
  · intro hext
    exact ⟨absorptive_of_extensional ⟨_, by simp [FragQueryIn.level1], rfl⟩
        ⟨_, by simp [FragQueryIn.level1], rfl⟩ hext,
      mulIdempotent_of_extensional ⟨_, by simp [FragQueryIn.level1], rfl⟩
        ⟨_, by simp [FragQueryIn.level1], rfl⟩ hext⟩
  · rintro hL n q₁ q₂ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩ hpe d u
    exact annSum_eq_of_points hL e₁ e₂ hpe
      (fun _ hm => (FragQueryIn.not_hasMonus_of_level1 e₁ he₁ hm).elim)
      (fun _ hm => (FragQueryIn.not_hasMonus_of_level1 e₂ he₂ hm).elim) d u

/-- **(c) `K` is extensional for `F₂` iff it is a Boolean m-semiring**,
whatever its `δ`. -/
theorem extensional_level2_iff :
    Extensional T K AggQueryIn.InLevel2 ↔ IsBooleanSemiring K := by
  constructor
  · intro hext
    have hL : IsLatticeSemiring K :=
      (extensional_level1_iff).mp
        (hext.mono (fun _ h => AggQueryIn.inLevel2_of_inLevel1 h))
    exact ⟨hL, exclusive_of_extensional SeqAggFunc.existsNonNull
      SeqAggFunc.existsNonNull_counts ⟨_, rfl⟩ ⟨_, rfl⟩ hext⟩
  · rintro hB n q₁ q₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩ hpe d u
    exact annSum_eq_of_points hB.toIsLatticeSemiring e₁ e₂ hpe
      (fun f _ => hB.map_monus f) (fun f _ => hB.map_monus f) d u

/-! ## (d) The whole recursion-free algebra

The pair forcing `δ(a) = a` is `ε(R)` against `Π₁(γ₁[count](R))`, a
grouping that aggregates with its aggregate column projected away: the
first annotates the one tuple by `a`, the second by the group's
existence factor `δ(a)`. Conversely, when `K` is Boolean with `δ` the
identity, every point of `K` is an m-semiring homomorphism onto `𝔹`,
the general evaluator commutes with it, and over `𝔹` the annotated
evaluation is the plain evaluation of the support
(`AggQueryIn.genRandomWorld_evaluate`, read through the constant
embedding of `𝔹` into `𝔹[∅]`). -/

/-- The kinds of a grouping of arity-one key with one aggregate. -/
abbrev gammaKinds : Fin (1 + 1) → ColKind :=
  Fin.append (fun _ : Fin 1 => ColKind.reg) (fun _ : Fin 1 => ColKind.agg)

/-- The projection reading the key column of such a grouping. -/
abbrev projKey : Tuple (ProjCol T gammaKinds) 1 :=
  fun _ => ProjColIn.term (TermGIn.index (κ := gammaKinds) 0 rfl)

/-- **The grouping of the forcing pair**: `γ₁[count](R)`, with any
sequence aggregate for the count, its aggregate column projected away. -/
def pairDelta₂Raw (cnt : SeqAggFunc T) : AggQuery T 1 (fun j => (projKey (T := T) j).kind) :=
  AggQueryIn.Proj projKey
    (AggQueryIn.Gamma (lab := 0) (rd := fun _ => false) ![0] ![TermIn.const ValueType.nonzero]
      ![cnt] (AggQueryIn.Rel 1 "R"))

/-- The same, with its kinds read as all regular. -/
def pairDelta₂ (cnt : SeqAggFunc T) : AggQuery T 1 (ColKind.allReg 1) :=
  AggQueryIn.castKind (κ := fun j => (projKey (T := T) j).kind) (κ' := ColKind.allReg 1)
    (funext fun _ => rfl) (pairDelta₂Raw cnt)

/-- **Duplicate elimination of `R`**, the other side of the pair. -/
def pairDelta₁ : AggQuery T 1 (ColKind.allReg 1) := AggQueryIn.Dedup (AggQueryIn.Rel 1 "R")

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
/-- The one-column key of a tuple of arity one is the tuple. -/
private theorem key_one (u : Tuple T 1) : (fun k : Fin 1 => u (![0] k)) = u := by
  funext k
  rw [Fin.fin_one_eq_zero k]
  rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The two sides of the pair have the same plain semantics: the
distinct tuples of `R`. -/
private theorem pairDelta_plainEquiv (cnt : SeqAggFunc T) :
    (pairDelta₁ (T := T)).PlainEquiv (pairDelta₂ cnt) := by
  intro D γ
  unfold pairDelta₁ pairDelta₂ pairDelta₂Raw
  rw [AggQueryIn.evaluatePlain_castKind]
  simp only [AggQueryIn.evaluatePlain, Multiset.map_map]
  rw [show (fun u : Tuple T 1 => (fun k : Fin 1 => u (![0] k))) = id from
    funext (fun u => key_one u), Multiset.map_id]
  refine (Multiset.map_id _).symm.trans (Multiset.map_congr rfl (fun g _ => ?_))
  simp only [Function.comp_apply, id_eq]
  funext j
  rw [Fin.fin_one_eq_zero j]
  simp only [ProjColIn.evalPlain, TermGIn.evalPlain]
  show g 0 = Fin.append g _ (Fin.castAdd 1 0)
  rw [Fin.append_left]

omit [DecidableEq K] [CommSemiringWithMonus K] in
/-- The one-tuple relation, grouped by its column, is one group. -/
private theorem havingGroup_oneTuple (x : T) (a : K) :
    Having.havingGroup ![0] ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) ![x]
      = [(![x], a)] := by
  refine Multiset.coe_eq_singleton.mp ?_
  rw [Having.havingGroup_coe, Multiset.filter_singleton]
  split_ifs with h
  · rfl
  · exact absurd (fun k' => by rw [Fin.fin_one_eq_zero k']; rfl) h

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The projection of the pair reads the key back from the grouping's
row. -/
private theorem proj_key_row (x : T) (G : Fin 1 → GenValue T K) :
    (fun j : Fin 1 => (projKey (T := T) j).eval
      (Fin.append (fun k => Sum.inl (![x] k)) G) (fun _ : Fin 0 => 0))
      = fun j : Fin 1 => (Sum.inl (![x] j) : GenValue T K) := by
  funext j
  rw [Fin.fin_one_eq_zero j]
  show Sum.inl (AggValue.collapseSum (Fin.append (fun k => Sum.inl (![x] k)) G (Fin.castAdd 1 0)))
    = (Sum.inl (![x] 0) : GenValue T K)
  rw [Fin.append_left]
  rfl

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- A tuple of regular values carries no token. -/
private theorem tokenLists_inl (x : T) :
    tokenLists (K := K) (fun j : Fin 1 => (Sum.inl (![x] j) : GenValue T K)) = 0 := by
  unfold tokenLists
  refine Multiset.eq_zero_of_forall_notMem (fun b hb => ?_)
  obtain ⟨i, -, hi⟩ := (Multiset.mem_filterMap _ _).mp hb
  exact absurd hi (by simp)

/-- `Π₁(γ₁[count](R))` annotates `![x]` by `δ(a)` on the one-tuple
instance. -/
private theorem annSum_pairDelta₂ (cnt : SeqAggFunc T) (x : T) (a : K) :
    ((pairDelta₂ cnt).evaluateAnnotated (oneTupleDb x a)).annSum ![x]
      = SemiringWithMonus.delta a := by
  unfold pairDelta₂ pairDelta₂Raw AggQueryIn.evaluateAnnotated
  rw [AggQueryIn.evaluate_castKind]
  simp only [AggQueryIn.evaluate, oneTupleDb_find, Multiset.map_singleton,
    GenRow.toAnnotated_ofAnnotated, Having.havingGroupOrd_unord]
  rw [key_one, groupByKey_eq_dedup_map]
  simp only [Multiset.map_singleton, Multiset.dedup_singleton]
  simp only [annSum_singleton,
    proj_key_row, tokenLists_inl, Multiset.inter_zero, Multiset.sub_zero, Multiset.map_singleton,
    Multiset.prod_singleton, one_mul]
  simp only [GenRow.toAnnotated, GenAnn.finalize, Multiset.map_zero,
    Multiset.prod_zero, mul_one]
  rw [ite_eq_left (show GenRow.plainTuple (fun k => (Sum.inl (![x] k) : GenValue T K)) = ![x] from
    funext fun j => rfl), havingGroup_oneTuple]
  simp

/-- `ε(R)` annotates `![x]` by `a`. -/
private theorem annSum_pairDelta₁ (x : T) (a : K) :
    ((pairDelta₁ (T := T)).evaluateAnnotated (oneTupleDb x a)).annSum ![x] = a := by
  rw [show pairDelta₁ (T := T) = (FragQueryIn.Dedup FragQueryIn.relR).toAgg from rfl,
    FragQueryIn.annSum_toAgg_evaluateAnnotated _ (fun h => by simp [FragQueryIn.hasSemijoin] at h)]
  exact FragQueryIn.annSum_pairAddIdem₁ x a

/-- **`δ` is the identity** where `K` is extensional for a class holding
`ε(R)` and `Π₁(γ₁[count](R))`. -/
theorem delta_id_of_extensional {F : ∀ {n : ℕ}, AggQuery T n (ColKind.allReg n) → Prop}
    (cnt : SeqAggFunc T) (h₁ : F pairDelta₁) (h₂ : F (pairDelta₂ cnt))
    (hext : Extensional T K F) : ∀ a : K, SemiringWithMonus.delta a = a := by
  intro a
  have := hext _ _ h₁ h₂ (pairDelta_plainEquiv cnt) (oneTupleDb (0 : T) a) ![0]
  rw [annSum_pairDelta₁, annSum_pairDelta₂] at this
  exact this.symm

/-! ### Tameness of the forcing pairs -/

section CastKind

variable {c n : ℕ} {κ κ' : Fin n → ColKind} (h : κ = κ') (q : AggQueryIn T c n κ)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
@[simp] private theorem noRec_castKind : (q.castKind h).noRec ↔ q.noRec := by
  subst h; exact Iff.rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
@[simp] private theorem noProvSum_castKind : (q.castKind h).noProvSum ↔ q.noProvSum := by
  subst h; exact Iff.rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
@[simp] private theorem hygienic_castKind : (q.castKind h).hygienic ↔ q.hygienic := by
  subst h; exact Iff.rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
@[simp] private theorem wellKinded_castKind (ρc : Fin c → ColKind) (HK : HoleKinds) :
    (q.castKind h).wellKinded ρc HK ↔ q.wellKinded ρc HK := by
  subst h; exact Iff.rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
@[simp] private theorem labels_castKind : (q.castKind h).labels = q.labels := by
  subst h; rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
@[simp] private theorem readsRecorded_castKind : (q.castKind h).readsRecorded ↔ q.readsRecorded := by
  subst h; exact Iff.rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] [ValueType T] in
@[simp] private theorem sourceCols_castKind : (q.castKind h).sourceCols ↔ q.sourceCols := by
  subst h; exact Iff.rfl

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
@[simp] private theorem allFramesContainSelf_castKind :
    (q.castKind h).allFramesContainSelf ↔ q.allFramesContainSelf := by
  subst h; exact Iff.rfl

end CastKind

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- Two functions out of `Fin 0` are equal. -/
private theorem fin0_fun_eq {α : Type} (f g : Fin 0 → α) : f = g :=
  funext (fun k => k.elim0)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tame_pairDelta₁ : (pairDelta₁ (T := T)).Tame := by
  simp [pairDelta₁, AggQueryIn.Tame, AggQueryIn.noRec, AggQueryIn.noProvSum, AggQueryIn.hygienic,
    AggQueryIn.wellKinded, AggQueryIn.labelsDistinct, AggQueryIn.labels, AggQueryIn.readsRecorded,
    AggQueryIn.sourceCols, AggQueryIn.allFramesContainSelf]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tame_pairDelta₂ (cnt : SeqAggFunc T) : (pairDelta₂ cnt).Tame := by
  simp [pairDelta₂, pairDelta₂Raw, AggQueryIn.Tame, AggQueryIn.noRec, AggQueryIn.noProvSum,
    AggQueryIn.hygienic, AggQueryIn.wellKinded, AggQueryIn.labelsDistinct, AggQueryIn.labels,
    AggQueryIn.readsRecorded, AggQueryIn.sourceCols, AggQueryIn.allFramesContainSelf,
    ProjColIn.outerOk, TermGIn.outerOk, TermIn.outerOk, labCons, ProjColIn.sourceCol]
  exact fin0_fun_eq _ _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tame_pairMulIdem₁ : (FragQueryIn.pairMulIdem₁ (T := T)).toAgg.Tame := by
  simp [FragQueryIn.toAgg, AggQueryIn.Tame, AggQueryIn.noRec, AggQueryIn.noProvSum,
    AggQueryIn.hygienic, AggQueryIn.wellKinded, AggQueryIn.labelsDistinct, AggQueryIn.labels,
    AggQueryIn.readsRecorded, AggQueryIn.sourceCols, AggQueryIn.allFramesContainSelf]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tame_pairMulIdem₂ : (FragQueryIn.pairMulIdem₂ (T := T)).toAgg.Tame := by
  simp [FragQueryIn.toAgg, AggQueryIn.Tame, AggQueryIn.noRec, AggQueryIn.noProvSum,
    AggQueryIn.hygienic, AggQueryIn.wellKinded, AggQueryIn.labelsDistinct, AggQueryIn.labels,
    AggQueryIn.readsRecorded, AggQueryIn.sourceCols, AggQueryIn.allFramesContainSelf,
    ProjColIn.outerOk, TermGIn.outerOk, ProjColIn.sourceCol]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tame_pairAbs₂ : (FragQueryIn.pairAbs₂ (T := T)).toAgg.Tame := by
  simp [FragQueryIn.toAgg, AggQueryIn.Tame, AggQueryIn.noRec, AggQueryIn.noProvSum,
    AggQueryIn.hygienic, AggQueryIn.wellKinded, AggQueryIn.labelsDistinct, AggQueryIn.labels,
    AggQueryIn.readsRecorded, AggQueryIn.sourceCols, AggQueryIn.allFramesContainSelf,
    ProjColIn.outerOk, TermGIn.outerOk, ProjColIn.sourceCol]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tame_pairExcl₁ (cnt : SeqAggFunc T) (hc : cnt.Counts) :
    (FragQueryIn.pairExcl₁ cnt hc).toAgg.Tame := by
  simp [FragQueryIn.toAgg, FragQueryIn.countSiteIn, FragQueryIn.matchCountIn,
    FragQueryIn.dropCountIn, AggQueryIn.Tame, AggQueryIn.noRec, AggQueryIn.noProvSum,
    AggQueryIn.hygienic, AggQueryIn.wellKinded, AggQueryIn.labelsDistinct, AggQueryIn.labels,
    AggQueryIn.readsRecorded, AggQueryIn.sourceCols, AggQueryIn.allFramesContainSelf,
    ProjColIn.outerOk, TermGIn.outerOk, TermIn.outerOk, GenPredIn.outerOk, ProjColIn.sourceCol,
    labCons, AggQueryIn.readsOuter, TermIn.readsOuter, GenPredIn.readsOuter, TermGIn.readsOuter]
  refine ⟨?_, ?_⟩
  · show ¬ (ColKind.allReg 1 0).base = ColKind.agg
    decide
  · funext x
    simp only [show ((List.finRange 1).any fun _ => false) = false from rfl, Bool.false_or]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem tame_pairExcl₂ : (FragQueryIn.pairExcl₂ (0 : T)).toAgg.Tame := by
  simp [FragQueryIn.toAgg, AggQueryIn.Tame, AggQueryIn.noRec, AggQueryIn.noProvSum,
    AggQueryIn.hygienic, AggQueryIn.wellKinded, AggQueryIn.labelsDistinct, AggQueryIn.labels,
    AggQueryIn.readsRecorded, AggQueryIn.sourceCols, AggQueryIn.allFramesContainSelf,
    ProjColIn.outerOk, TermGIn.outerOk, ProjColIn.sourceCol]

/-! ### The converse: points are m-semiring homomorphisms -/

/-- **A point of a Boolean m-semiring with `δ` the identity, into
`𝔹[X]`**: the point followed by the constant embedding. -/
@[reducible] def IsBooleanSemiring.pointHomX (hB : IsBooleanSemiring K)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) (f : K →+* Bool) (X : Type) :
    SemiringWithMonusHom K (BoolFunc X) where
  toRingHom := ((Bool.constHom X).toRingHom).comp f
  map_sub := fun a b => by
    show (Bool.constHom X) (f (a - b)) = (Bool.constHom X) (f a) - (Bool.constHom X) (f b)
    rw [hB.map_monus f, ← (Bool.constHom X).map_sub]
  map_delta := fun a => by
    show (Bool.constHom X) (f (SemiringWithMonus.delta a)) = SemiringWithMonus.delta ((Bool.constHom X) (f a))
    rw [hδ a]
    rfl

omit [ValueType T] [HasAltLinearOrder K] [DecidableEq K] in
/-- The image of a database under the composite is the image under the
constant embedding of the image under the point. -/
private theorem mapAnnotatedDatabase_pointHomX (hB : IsBooleanSemiring K)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) (f : K →+* Bool) (X : Type)
    (d : AnnotatedDatabase T K) :
    (hB.pointHomX hδ f X).mapAnnotatedDatabase d
      = (Bool.constHom X).mapAnnotatedDatabase ((hB.pointHom hδ f).mapAnnotatedDatabase d) := by
  unfold SemiringWithMonusHom.mapAnnotatedDatabase SemiringWithMonusHom.mapAnnotatedRelation
  simp only [List.map_map, Multiset.map_map, Function.comp_def]
  rfl

omit [ValueType T] [HasAltLinearOrder K] [DecidableEq K] in
private theorem mapAnnotatedRelation_pointHomX (hB : IsBooleanSemiring K)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) (f : K →+* Bool) (X : Type) {n : ℕ}
    (r : AnnotatedRelation T K n) :
    (hB.pointHomX hδ f X).mapAnnotatedRelation r
      = (Bool.constHom X).mapAnnotatedRelation ((hB.pointHom hδ f).mapAnnotatedRelation r) := by
  unfold SemiringWithMonusHom.mapAnnotatedRelation
  rw [Multiset.map_map]
  rfl

omit [ValueType T] [HasAltLinearOrder K] [DecidableEq K] in
/-- The image of a relation under a point, read as a pushforward. -/
private theorem mapAnnotatedRelation_pointHom (hB : IsBooleanSemiring K)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) (f : K →+* Bool) {n : ℕ}
    (r : AnnotatedRelation T K n) :
    (hB.pointHom hδ f).mapAnnotatedRelation r = r.mapAnn f := rfl

/-- **The realized world of a regular-valued evaluation is the random
world of its finalized rows.** -/
private theorem genRandomWorld_eq_randomWorld {X : Type} [Fintype X] [DecidableEq X]
    (v : X → Bool) {n : ℕ} (R : Multiset (GenRow T (BoolFunc X) n))
    (hreg : ∀ r ∈ R, ∀ k, GenValue.kindOf (r.fst k) = ColKind.reg) :
    genRandomWorld v R = randomWorld v (R.map GenRow.toAnnotated) := by
  unfold genRandomWorld randomWorld
  rw [Multiset.filter_map, Multiset.map_map]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  obtain ⟨hr, -⟩ := Multiset.mem_filter.mp hr
  show GenRow.specializeTuple v r.fst = GenRow.plainTuple r.fst
  funext k
  have hk := hreg r hr k
  show GenValue.specializeAt v (r.fst k) = AggValue.collapseSum (r.fst k)
  cases hx : r.fst k with
  | inl x => rfl
  | inr a =>
    rw [hx] at hk
    exact absurd hk (by simp [GenValue.kindOf])

open Classical in
/-- Any linear order serves to list the occurrences of a family. -/
private noncomputable instance : HasAltLinearOrder (BoolFunc Empty) :=
  ⟨linearOrderOfSTO WellOrderingRel⟩

/-- **Over a Boolean m-semiring with `δ` the identity, a point reads a
tame query's collapsed annotation as a plain evaluation of the
support.** -/
private theorem point_annSum_eq_true_iff (hB : IsBooleanSemiring K)
    (hδ : ∀ a : K, SemiringWithMonus.delta a = a) (f : K →+* Bool) {n : ℕ}
    (q : AggQuery T n (ColKind.allReg n)) (hq : q.Tame) (d : AnnotatedDatabase T K)
    (u : Tuple T n) :
    f ((q.evaluateAnnotated d).annSum u) = true
      ↔ u ∈ (show Multiset (Tuple T n) from
          q.evaluatePlain ((hB.pointHom hδ f).mapAnnotatedDatabase d).support) := by
  obtain ⟨hnr, hnp, hh, hwk, hld, hrr, hsc, hfc⟩ := hq
  let v : Empty → Bool := fun e => e.elim
  have hrec : ∀ (K' : Type) [CommSemiringWithMonus K'] [DecidableEq K'] [HasAltLinearOrder K']
      (d' : AnnotatedDatabase T K'), q.AnnSettlesAt d' (fun _ => 0) {} :=
    fun K' _ _ _ d' => AggQueryIn.annSettlesAt_of_noRec q hnr d' _ {}
  rw [← AnnotatedRelation.annSum_mapAnn, ← mapAnnotatedRelation_pointHom hB hδ f,
    AnnotatedRelation.annSum_eq_true_iff, ← randomWorld_constHom (X := Empty) v,
    ← mapAnnotatedRelation_pointHomX, ← AggQueryIn.evaluateAnnotated_hom _ q hld hrr hsc hfc d
      (hrec K d),
    show q.evaluateAnnotated ((hB.pointHomX hδ f Empty).mapAnnotatedDatabase d)
      = (q.evaluate ((hB.pointHomX hδ f Empty).mapAnnotatedDatabase d)).map GenRow.toAnnotated
      from rfl,
    ← genRandomWorld_eq_randomWorld v _ (fun r hr k => by
      rw [AggQueryIn.evaluate_conform q _ r hr k]; rfl),
    AggQueryIn.genRandomWorld_evaluate q hnp hh hwk _ v (hrec _ _),
    mapAnnotatedDatabase_pointHomX, AnnotatedDatabase.randomWorld_constHom]

/-- **(d) `K` is extensional for the whole recursion-free algebra iff it
is a Boolean m-semiring whose `δ` is the identity.** -/
theorem extensional_tame_iff :
    Extensional T K AggQueryIn.Tame
      ↔ IsBooleanSemiring K ∧ ∀ a : K, SemiringWithMonus.delta a = a := by
  constructor
  · intro hext
    have hB : IsBooleanSemiring K :=
      ⟨⟨absorptive_of_extensional tame_pairMulIdem₁ tame_pairAbs₂ hext,
        mulIdempotent_of_extensional tame_pairMulIdem₁ tame_pairMulIdem₂ hext⟩,
       exclusive_of_extensional _ SeqAggFunc.existsNonNull_counts
         (tame_pairExcl₁ _ SeqAggFunc.existsNonNull_counts) tame_pairExcl₂ hext⟩
    exact ⟨hB, delta_id_of_extensional (fun _ => 0) tame_pairDelta₁ (tame_pairDelta₂ _) hext⟩
  · rintro ⟨hB, hδ⟩ n q₁ q₂ h₁ h₂ hpe d u
    refine hB.toIsLatticeSemiring.eq_of_forall_point (fun f => ?_)
    rw [Bool.eq_iff_iff, point_annSum_eq_true_iff hB hδ f q₁ h₁ d u,
      point_annSum_eq_true_iff hB hδ f q₂ h₂ d u, hpe]

end
