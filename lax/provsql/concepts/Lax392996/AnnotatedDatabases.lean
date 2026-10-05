import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Multiset.Basic
import Lax392996.Databases
import Lax392996.SemiringsWithMonus

/-!
---
title: Annotated relations and databases
type: definition
---
For an m-semiring $\mathbb{K}$, a $\mathbb{K}$-relation of arity $k$ is a
finite multiset of $k$-tuples each carrying an annotation in $\mathbb{K}$,
and a $\mathbb{K}$-instance maps each relation name, at its arity, to a
$\mathbb{K}$-relation: the two claims record that the definitions are these
ones. An annotated tuple of arity $k$ also reads as a plain tuple of arity
$k+1$ over $\mathcal{V} \uplus \mathbb{K}$, its annotation in the last
column, which extends to relations and instances, and a composite tuple
reads back as an annotated one; this composite reading is what the
rewriting of the paper targets. For it, $\mathcal{V} \uplus
\mathbb{K}$ is made a value type, with data values below annotations and
the annotations compared through the alternative linear order of
$\mathbb{K}$.
-/

namespace Lax392996.AnnotatedDatabases

open Lax392996.Databases Lax392996.SemiringsWithMonus

universe u

variable {T : Type} [ValueType T] {K : Type} [Zero K] {n : ℕ}

/-- An annotated tuple: a tuple paired with an annotation, ordered
lexicographically. -/
abbrev AnnotatedTuple (T : Type) (K : Type u) (n: ℕ) := Tuple T n ×ₗ K

/-- A `K`-relation of arity `arity`: a finite multiset of annotated tuples. -/
def AnnotatedRelation (T : Type) (K : Type u) (arity: ℕ) := Multiset (AnnotatedTuple T K arity)

instance instAddAnnotatedRelation {arity : ℕ} : Add (AnnotatedRelation T K arity) := by
  show Add (Multiset (AnnotatedTuple T K arity))
  infer_instance

/-- A `K`-instance: a list of named annotated relations, each with its arity. -/
def AnnotatedDatabase (T : Type) (K : Type u) := List (String × Σ n, AnnotatedRelation T K n)

/-- The annotated relation named `s` of arity `n` in a `K`-instance, if any. -/
def AnnotatedDatabase.find (n: ℕ) (s: String) (d: AnnotatedDatabase T K) :
    Option (AnnotatedRelation T K n) :=
  let rec f
  | [] => none
  | (s',rn)::tl => if h: n = rn.fst ∧ s =s' then some (Eq.mp (by rw[h.left]) rn.snd) else f tl
  f d

/-- The composite reading of an annotated tuple: the annotation becomes a
last column over `T ⊕ K`. -/
def AnnotatedTuple.toComposite (p: AnnotatedTuple T K n) :=
  Fin.append (λ k: Fin n ↦ Sum.inl (p.fst k)) ![Sum.inr p.snd]

/-- The annotated tuple a composite tuple reads as: the data values from
its first `n` columns, the annotation from its last one. -/
def Tuple.fromComposite (t: Tuple (T⊕K) (n+1)) : AnnotatedTuple T K n :=
  (
    λ (k: Fin n) ↦ match t (k.castLE (by simp)) with | Sum.inl x => x | Sum.inr _ => 0,
                   match t (Fin.last n)         with | Sum.inl _ => 0 | Sum.inr x => x
  )

/-- The composite reading of an annotated relation. -/
def AnnotatedRelation.toComposite (ar: AnnotatedRelation T K n):
  Relation (T⊕K) (n+1) :=
  ar.map λ p ↦ p.toComposite

/-- The composite reading of a `K`-instance: a plain database over `T ⊕ K`. -/
def AnnotatedDatabase.toComposite (d: AnnotatedDatabase T K): Database (T⊕K) :=
  d.map λ (s, ⟨n',r⟩) ↦ (s, ⟨n'+1,r.toComposite⟩)

/-- `V ⊕ K` is a value type: data values are below annotations, and
annotations are compared through the alternative linear order of `K`. -/
instance instValueTypeSumOfHasAltLinearOrderOfSemiringWithMonus {V K : Type}
    [ValueType V] [HasAltLinearOrder K] [SemiringWithMonus K] : ValueType (V⊕K) where
  zero := Sum.inr 0

  add a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'+b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'+b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  sub a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'-b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'-b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  mul a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'*b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'*b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp[(· + ·)] <;> exact add_assoc _ _ _

  add_comm a b := by
    cases a <;> cases b <;> simp[(· + ·)] <;> exact add_comm _ _

  le a b := match a,b with
  | Sum.inl a', Sum.inl b' => a'≤b'
  | Sum.inr a', Sum.inr b' => HasAltLinearOrder.altOrder.le a' b'
  | Sum.inl a', Sum.inr b' => True
  | Sum.inr a', Sum.inl b' => False

  le_refl a := by
    cases a <;> simp

  le_antisymm a b := by
    cases a <;> cases b <;> simp
    . exact le_antisymm
    . exact HasAltLinearOrder.altOrder.le_antisymm _ _

  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp
    . exact le_trans
    . exact HasAltLinearOrder.altOrder.le_trans _ _ _

  le_total a b := by
    cases a <;> cases b <;> simp
    . exact le_total _ _
    . next x y =>
      exact HasAltLinearOrder.altOrder.le_total x y

  toDecidableLE :=
    λ a b ↦ match a, b with
    | Sum.inl a', Sum.inl b' => inferInstance
    | Sum.inr a', Sum.inr b' => inferInstance
    | Sum.inl a', Sum.inr b' => isTrue (trivial)
    | Sum.inr a', Sum.inl b' => isFalse (id)

/-- A `K`-relation of arity `n` is a multiset of `n`-tuples paired with an
annotation. -/
axiom annotated_relation_eq : AnnotatedRelation T K n = Multiset (Tuple T n ×ₗ K)

/-- A `K`-instance answers a relation name, at an arity, with a `K`-relation. -/
axiom annotated_database_lookup :
  ∀ (R : String) (d : AnnotatedDatabase T K),
    (AnnotatedDatabase.find n R d : Option (AnnotatedRelation T K n)) = d.find n R

end Lax392996.AnnotatedDatabases
