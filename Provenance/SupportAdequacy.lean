import Provenance.Probability
import Provenance.QueryAdequacy

/-!
# Support adequacy over `𝔹` and transfer along monus homomorphisms

`Provenance.QueryAdequacy` shows that on the data parts, adequacy of the
annotated semantics with the plain semantics stops at the positive fragment.
This file gives the equality that *does* extend to the full non-aggregation
fragment (difference and duplicate elimination included): over the Boolean
m-semiring `𝔹`, the *support* of the annotated evaluation – the multiset of
true-annotated tuple slots – is exactly the plain evaluation of the support
of the database (`Query.evaluateAnnotated_support`).

The result is derived, rather than re-proved, from the possible-worlds
commutation theorem `randomWorld_evaluateAnnotated` of
`Provenance.Probability`, instantiated at the variable-free Boolean-function
semiring `BoolFunc Empty ≃ 𝔹` via the constant embedding `Bool.constHom`.

It then transfers along *any* m-semiring homomorphism `h : K → 𝔹`
(`Query.evaluateAnnotated_support_hom`), by the hom-commutation theorem
`Query.evaluateAnnotated_hom`: every annotation domain that admits a
monus-preserving support map into `𝔹` inherits the adequacy equality.
`BoolFunc X` admits one per valuation (`Bool.homomorphism_to_BoolFunc`),
which recovers the possible-worlds reading; `ℕ` admits none
(`Nat.no_monusHom_to_Bool` in `Provenance.Semirings.Nat`) – its support map
`n ↦ (n ≠ 0)` is a ring homomorphism but does not preserve monus, which is
the algebraic reason why `ℕ`-adequacy is restricted to the positive fragment
(the theorem of [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini,
*A Coq formalization of data provenance*][benzaken2021coq]).

## Main definitions

* `AnnotatedRelation.support`, `AnnotatedDatabase.support` – the
  true-annotated tuple slots of a `𝔹`-annotated relation / database
* `Bool.constHom` – the constant embedding `𝔹 → 𝔹[X]` as an m-semiring
  homomorphism

## Main results

* `Query.evaluateAnnotated_support` – support adequacy over `𝔹`, for the
  full non-aggregation fragment
* `Query.evaluateAnnotated_support_hom` – transfer along any m-semiring
  homomorphism `K → 𝔹`

## References

* [Benzaken, Cohen-Boulakia, Contejean, Keller & Zucchini, *A Coq
  formalization of data provenance*][benzaken2021coq]
* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]
-/

variable {T : Type}

/-- Boolean support of a `𝔹`-annotated relation: the multiset of data parts
of the true-annotated tuple slots. The return type is a bare
`Multiset (Tuple T n)` so that `Multiset` lemmas apply without an extra
unfolding step. -/
def AnnotatedRelation.support (r : AnnotatedRelation T Bool n) :
    Multiset (Tuple T n) :=
  Multiset.map Prod.fst
    (Multiset.filter (fun p : AnnotatedTuple T Bool n => p.snd = true) r)

/-- Boolean support of a `𝔹`-annotated database, relation by relation. -/
def AnnotatedDatabase.support (d : AnnotatedDatabase T Bool) : Database T :=
  d.map (fun e => (e.fst, ⟨e.snd.fst, e.snd.snd.support⟩))

/-- The constant embedding `𝔹 → 𝔹[X]` as an m-semiring homomorphism (the
same homomorphism exhibited by `Bool.homomorphism_from_BoolFunc`, as a
usable definition). -/
@[reducible] def Bool.constHom (X : Type) : SemiringWithMonusHom Bool (BoolFunc X) where
  toFun     := fun b => fun _ => b
  map_zero' := rfl
  map_one'  := rfl
  map_add'  := by intro a b; rfl
  map_mul'  := by intro a b; rfl
  map_sub   := by intro a b; rfl
  map_delta := by intro a; rfl

/-- The random world of the constant embedding of a `𝔹`-annotated relation
is its support, under any valuation. -/
lemma randomWorld_constHom {X : Type} (v : X → Bool)
    (r : AnnotatedRelation T Bool n) :
    randomWorld v ((Bool.constHom X).mapAnnotatedRelation r) = r.support := by
  let r' : Multiset (Tuple T n × Bool) := r
  show Multiset.map Prod.fst
      (Multiset.filter (fun p : Tuple T n × BoolFunc X => p.snd v = true)
        (Multiset.map (fun p : Tuple T n × Bool =>
          ((p.1, fun _ => p.2) : Tuple T n × BoolFunc X)) r'))
    = Multiset.map Prod.fst
        (Multiset.filter (fun p : Tuple T n × Bool => p.snd = true) r')
  induction r' using Multiset.induction_on with
  | empty => rfl
  | cons p s ih =>
    rw [Multiset.map_cons]
    by_cases hp : p.2 = true
    · rw [Multiset.filter_cons_of_pos
            (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) _ hp,
          Multiset.filter_cons_of_pos
            (p := fun p : Tuple T n × Bool => p.snd = true) _ hp,
          Multiset.map_cons, Multiset.map_cons, ih]
    · rw [Multiset.filter_cons_of_neg
            (p := fun p : Tuple T n × BoolFunc X => p.snd v = true) _ hp,
          Multiset.filter_cons_of_neg
            (p := fun p : Tuple T n × Bool => p.snd = true) _ hp, ih]

/-- Database-level version of `randomWorld_constHom`. -/
lemma AnnotatedDatabase.randomWorld_constHom {X : Type} (v : X → Bool)
    (d : AnnotatedDatabase T Bool) :
    ((Bool.constHom X).mapAnnotatedDatabase d).randomWorld v = d.support := by
  induction d with
  | nil => rfl
  | cons e tl ih =>
    show (e.fst, ⟨e.snd.fst, _root_.randomWorld v
          ((Bool.constHom X).mapAnnotatedRelation e.snd.snd)⟩)
        :: ((Bool.constHom X).mapAnnotatedDatabase tl).randomWorld v
      = (e.fst, ⟨e.snd.fst, e.snd.snd.support⟩) :: AnnotatedDatabase.support tl
    rw [_root_.randomWorld_constHom, ih]

variable [ValueType T]

/-- **Support adequacy over `𝔹`.** For any non-aggregation query `q` – the
full fragment, difference and duplicate elimination included – the support
of the `𝔹`-annotated evaluation equals the plain evaluation of the support
of the database. This is the equality that replaces the (positive-fragment
only) `ℕ`-adequacy of [Benzaken, Cohen-Boulakia, Contejean, Keller &
Zucchini][benzaken2021coq] once difference enters the language. -/
theorem Query.evaluateAnnotated_support {n : ℕ}
    (q : Query T n) (hq : q.noAgg) (d : AnnotatedDatabase T Bool) :
    (q.evaluateAnnotated hq d).support = q.evaluate d.support := by
  rw [← randomWorld_constHom (X := Empty) (fun e => e.elim)
        (q.evaluateAnnotated hq d),
      ← Query.evaluateAnnotated_hom (Bool.constHom Empty) q hq d,
      randomWorld_evaluateAnnotated q hq _ _,
      AnnotatedDatabase.randomWorld_constHom]

variable {K : Type} [SemiringWithMonus K] [DecidableEq K]

/-- **Transfer of support adequacy along monus homomorphisms.** Any
m-semiring homomorphism `h : K → 𝔹` turns the annotated evaluation over `K`
into a plain evaluation on the `h`-support of the database. `BoolFunc X`
admits one such homomorphism per valuation
(`Bool.homomorphism_to_BoolFunc`), recovering the possible-worlds semantics;
`ℕ` admits none (`Nat.no_monusHom_to_Bool`), which is why `ℕ`-adequacy stops
at the positive fragment. -/
theorem Query.evaluateAnnotated_support_hom {n : ℕ}
    (h : SemiringWithMonusHom K Bool)
    (q : Query T n) (hq : q.noAgg) (d : AnnotatedDatabase T K) :
    (h.mapAnnotatedRelation (q.evaluateAnnotated hq d)).support
      = q.evaluate (h.mapAnnotatedDatabase d).support := by
  rw [← Query.evaluateAnnotated_hom h q hq d,
      Query.evaluateAnnotated_support q hq (h.mapAnnotatedDatabase d)]
