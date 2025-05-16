import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter

import Provenance.Database

section Query

variable {α: Type} [Zero α] [decEq: DecidableEq α] [PartialOrder α] [decLE: DecidableLE α]
variable (hα : ∃ x : α, x ≠ (0: α))

instance : DecidableRel ((· : α) ≠ ·) :=
  λ a b =>
    match inferInstanceAs (Decidable (a = b)) with
    | isTrue h  => isFalse (by simp[h])
    | isFalse h => isTrue  (by simp[h])

instance : DecidableRel ((· : α) < ·) :=
  λ a b =>
    match inferInstanceAs (Decidable (a ≤ b)), inferInstanceAs (Decidable (a = b)) with
    | isTrue h₁, isTrue h₂  => isFalse (by simp[h₂])
    | isTrue h₁, isFalse h₂ => isTrue  (lt_of_le_of_ne h₁ h₂)
    | isFalse h₁, _         => isFalse (by contrapose h₁; simp at *; exact le_of_lt h₁)

inductive Term α n where
| Const : α → Term α n
| Index : Fin n → Term α n

def Term.eval (term: Term α n) (tuple: Tuple α n) := match term with
  | Term.Const a => a
  | Term.Index k => tuple[k]

instance : Coe α (Term α n) where
  coe a:= Term.Const a

instance : OfNat (Term ℕ n) (a: ℕ) where
  ofNat := Term.Const a

prefix:max "#" => @Term.Index

inductive BoolTerm (α) (n: ℕ) where
| EQ : Term α n → Term α n → BoolTerm α n
| NE : Term α n → Term α n → BoolTerm α n
| LE : Term α n → Term α n → BoolTerm α n
| LT : Term α n → Term α n → BoolTerm α n
| GE : Term α n → Term α n → BoolTerm α n
| GT : Term α n → Term α n → BoolTerm α n

infix:20 " == " => λ x y ↦ BoolTerm.EQ x y
infix:20 " != " => λ x y ↦ BoolTerm.NE x y
infix:20 " <= " => λ x y ↦ BoolTerm.LE x y
infix:20 " < " => λ x y ↦ BoolTerm.LT x y
infix:20 " >= " => λ x y ↦ BoolTerm.GE x y
infix:20 " > " => λ x y ↦ BoolTerm.GT x y

def BoolTerm.eval (φ: BoolTerm α n) (tuple: Tuple α n) := match φ with
| EQ t₁ t₂ => (t₁.eval tuple) = (t₂.eval tuple)
| NE t₁ t₂ => (t₁.eval tuple) ≠ (t₂.eval tuple)
| LE t₁ t₂ => (t₁.eval tuple) ≤ (t₂.eval tuple)
| LT t₁ t₂ => (t₁.eval tuple) < (t₂.eval tuple)
| GE t₁ t₂ => (t₁.eval tuple) ≥ (t₂.eval tuple)
| GT t₁ t₂ => (t₁.eval tuple) > (t₂.eval tuple)

def BoolTerm.evalDecidable (φ: BoolTerm α n) : DecidablePred φ.eval :=
  λ t => by
    cases φ <;> rename_i x y <;> simp [BoolTerm.eval]
    . exact inferInstanceAs (Decidable (x.eval t = y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t ≠ y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t ≤ y.eval t))
    . exact inferInstanceAs (Decidable (x.eval t < y.eval t))
    . exact inferInstanceAs (Decidable (y.eval t ≤ x.eval t))
    . exact inferInstanceAs (Decidable (y.eval t < x.eval t))

inductive Filter (α) (n: ℕ) where
| BT   : BoolTerm α n   → Filter α n
| Not  : Filter α n → Filter α n
| And  : Filter α n → Filter α n → Filter α n
| Or   : Filter α n → Filter α n → Filter α n

def Filter.eval (φ: Filter α n) (tuple: Tuple α n) := match φ with
| BT  φ     => φ.eval tuple
| Not φ     => ¬ (φ.eval tuple)
| And φ₁ φ₂ => (φ₁.eval tuple) ∧ (φ₂.eval tuple)
| Or  φ₁ φ₂ => (φ₁.eval tuple) ∨ (φ₂.eval tuple)

def Filter.evalDecidable (φ : Filter α n) : DecidablePred φ.eval :=
  λ t => match φ with
    | Filter.BT φ      => φ.evalDecidable t
    | Filter.Not φ     => match evalDecidable φ t with
      | isTrue h  => isFalse (by simp [Filter.eval, h])
      | isFalse h => isTrue  (by simp [Filter.eval, h])
    | Filter.And φ₁ φ₂  => match evalDecidable φ₁ t, evalDecidable φ₂ t with
      | isTrue h₁, isTrue h₂   => isTrue  (by simp [Filter.eval, h₁, h₂])
      | isFalse h, _ | _, isFalse h => isFalse (by simp [Filter.eval, h])
    | Filter.Or φ₁ φ₂   => match evalDecidable φ₁ t, evalDecidable φ₂ t with
      | isTrue h, _ | _, isTrue h => isTrue (by simp [Filter.eval, h])
      | isFalse h₁, isFalse h₂    => isFalse (by simp [Filter.eval, h₁, h₂])

instance : Coe (BoolTerm α n) (Filter α n) where
  coe bt := Filter.BT bt

inductive Query (α: Type) : ℕ → Type
| Rel   : (n: ℕ) → String → Query α n
| Proj  : Tuple (Term α n) m → Query α n → Query α m
| Sel   : Filter α n → Query α n → Query α n
| Prod  : Query α n₁ → Query α n₂ → Query α (n₁+n₂)
| Sum   : Query α n → Query α n → Query α n
| Dedup : Query α n → Query α n
| Diff  : Query α n → Query α n → Query α n

prefix:50 "Π " => Query.Proj
prefix:50 "σ " => Query.Sel
infix:80 " × " => Query.Prod
infix:50 " ⊎ " => Query.Sum
prefix:50 "ε " => Query.Dedup
infix:50 " - " => Query.Diff
infix:80 " ⋈ " => λ q₁ φ ↦ λ q₂ ↦ (σ φ) (q₁ × q₂)
infix:50 " ∪ " => λ q₁ q₂ ↦ ε (q₁ ⊎ q₂)

def Query.arity (_: Query α n) := n

def Query.evaluate (q: Query α n) (d: Database α) : Relation α n := match q with
| Rel   n  s  => Eq.mp (congrArg (Relation α) (d.wf n s)) (d (n,s)).snd
| Proj ts q => let r := evaluate q d
  Multiset.map (λ t ↦ Vector.map (λ u ↦ u.eval t) ts) r
| Sel   φ  q  => let r := evaluate q d; @Multiset.filter _ (Filter.eval φ) (Filter.evalDecidable φ) r
| Prod  q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ * r₂
| Sum   q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ + r₂
| Dedup q     => let r := evaluate q d; Multiset.dedup r
| Diff  q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ - r₂

def ms : Multiset (Vector ℕ 3) :=
  {
    Vector.ofFn (λ i => match i.val with
      | 0 => 1
      | 1 => 2
      | _ => 3),
    Vector.ofFn (λ i => match i.val with
      | 0 => 4
      | 1 => 5
      | _ => 6)
  }

end Query
