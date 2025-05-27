import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter

import Provenance.Database

variable {T: Type} [ValueType T]

inductive Term T n where
| Const : T → Term T n
| Index : Fin n → Term T n

def Term.eval (term: Term T n) (tuple: Tuple T n) := match term with
  | Term.Const a => a
  | Term.Index k => tuple k

instance : Coe T (Term T n) where
  coe a:= Term.Const a

instance : OfNat (Term ℕ n) (a: ℕ) where
  ofNat := Term.Const a

prefix:max "#" => @Term.Index

inductive BoolTerm (T) (n: ℕ) where
| EQ : Term T n → Term T n → BoolTerm T n
| NE : Term T n → Term T n → BoolTerm T n
| LE : Term T n → Term T n → BoolTerm T n
| LT : Term T n → Term T n → BoolTerm T n
| GE : Term T n → Term T n → BoolTerm T n
| GT : Term T n → Term T n → BoolTerm T n

infix:20 " == " => λ x y ↦ BoolTerm.EQ x y
infix:20 " != " => λ x y ↦ BoolTerm.NE x y
infix:20 " <= " => λ x y ↦ BoolTerm.LE x y
infix:20 " < " => λ x y ↦ BoolTerm.LT x y
infix:20 " >= " => λ x y ↦ BoolTerm.GE x y
infix:20 " > " => λ x y ↦ BoolTerm.GT x y

def BoolTerm.eval (φ: BoolTerm T n) (tuple: Tuple T n) := match φ with
| EQ t₁ t₂ => (t₁.eval tuple) = (t₂.eval tuple)
| NE t₁ t₂ => (t₁.eval tuple) ≠ (t₂.eval tuple)
| LE t₁ t₂ => (t₁.eval tuple) ≤ (t₂.eval tuple)
| LT t₁ t₂ => (t₁.eval tuple) < (t₂.eval tuple)
| GE t₁ t₂ => (t₁.eval tuple) ≥ (t₂.eval tuple)
| GT t₁ t₂ => (t₁.eval tuple) > (t₂.eval tuple)

def BoolTerm.evalDecidable (φ: BoolTerm T n) : DecidablePred φ.eval :=
  λ t => by
    cases φ <;> rename_i x y <;> simp [BoolTerm.eval]
    . exact inferInstanceAs (Decidable (x.eval t = y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t ≠ y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t ≤ y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t < y.eval t))
    . exact inferInstanceAs (Decidable (y.eval t ≤ x.eval t))
    . exact inferInstanceAs (Decidable (y.eval t < x.eval t))

inductive Filter (T) (n: ℕ) where
| BT   : BoolTerm T n   → Filter T n
| Not  : Filter T n → Filter T n
| And  : Filter T n → Filter T n → Filter T n
| Or   : Filter T n → Filter T n → Filter T n

def Filter.eval (φ: Filter T n) (tuple: Tuple T n) := match φ with
| BT  φ     => φ.eval tuple
| Not φ     => ¬ (φ.eval tuple)
| And φ₁ φ₂ => (φ₁.eval tuple) ∧ (φ₂.eval tuple)
| Or  φ₁ φ₂ => (φ₁.eval tuple) ∨ (φ₂.eval tuple)

def Filter.evalDecidable (φ : Filter T n) : DecidablePred φ.eval :=
  λ t => match φ with
    | Filter.BT φ      => φ.evalDecidable t
    | Filter.Not φ     => match φ.evalDecidable t with
      | isTrue h  => isFalse (by simp [Filter.eval, h])
      | isFalse h => isTrue  (by simp [Filter.eval, h])
    | Filter.And φ₁ φ₂  => match φ₁.evalDecidable t, φ₂.evalDecidable t with
      | isTrue h₁, isTrue h₂   => isTrue  (by simp [Filter.eval, h₁, h₂])
      | isFalse h, _ | _, isFalse h => isFalse (by simp [Filter.eval, h])
    | Filter.Or φ₁ φ₂   => match φ₁.evalDecidable t, φ₂.evalDecidable t with
      | isTrue h, _ | _, isTrue h => isTrue (by simp [Filter.eval, h])
      | isFalse h₁, isFalse h₂    => isFalse (by simp [Filter.eval, h₁, h₂])

instance : Coe (BoolTerm T n) (Filter T n) where
  coe bt := Filter.BT bt

inductive Query (T: Type) : ℕ → Type
| Rel   : (n: ℕ) → String → Query T n
| Proj  : Tuple (Term T n) m → Query T n → Query T m
| Sel   : Filter T n → Query T n → Query T n
| Prod  : Query T n₁ → Query T n₂ → Query T (n₁+n₂)
| Sum   : Query T n → Query T n → Query T n
| Dedup : Query T n → Query T n
| Diff  : Query T n → Query T n → Query T n

prefix:50 "Π " => Query.Proj
prefix:50 "σ " => Query.Sel
infix:80 " × " => Query.Prod
infix:50 " ⊎ " => Query.Sum
prefix:50 "ε " => Query.Dedup
infix:50 " - " => Query.Diff
infix:80 " ⋈ " => λ q₁ φ ↦ λ q₂ ↦ (σ φ) (q₁ × q₂)
infix:50 " ∪ " => λ q₁ q₂ ↦ ε (q₁ ⊎ q₂)

def Query.arity (_: Query T n) := n

def Query.evaluate (q: Query T n) (d: Database T) : Relation T n := match q with
| Rel   n  s  =>
    if hsupport: (n,s) ∈ d.db.support then
      Eq.mp (congrArg (Relation T) (d.wf n s hsupport)) (d (n,s)).snd
    else
      (∅: Multiset (Tuple T n))
| Proj ts q => let r := evaluate q d; Multiset.map (λ t ↦ λ k ↦ (ts k).eval t) r
| Sel   φ  q  => let r := evaluate q d; @Multiset.filter _ φ.eval φ.evalDecidable r
| Prod  q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ * r₂
| Sum   q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ + r₂
| Dedup q     => let r := evaluate q d; Multiset.dedup r
| Diff  q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ - r₂
