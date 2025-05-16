import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Multiset.Dedup

import Provenance.Database

section Query

variable {α: Type} [Zero α] [DecidableEq α]
variable (hα : ∃ x : α, x ≠ (0: α))

inductive Term α n where
| Const : α → Term α n
| Index : Fin n → Term α n

def Term.index {α} (k: ℕ) := @Index α k

def Term.eval (term: Term α n) (tuple: Tuple α n) := match term with
  | Term.Const a => a
  | Term.Index k => tuple[k]

instance : Coe α (Term α n) where
  coe a:= Term.Const a

instance : OfNat (Term ℕ n) (a: ℕ) where
  ofNat := Term.Const a

prefix:max "#" => Term.index

inductive BoolTerm (α) (n: ℕ) where
| EQ : Term α n → Term α n → BoolTerm α n
| NE : Term α n → Term α n → BoolTerm α n
| LE : Term α n → Term α n → BoolTerm α n
| LT : Term α n → Term α n → BoolTerm α n
| GE : Term α n → Term α n → BoolTerm α n
| GT : Term α n → Term α n → BoolTerm α n

infix:20 " == " => λ x y ↦ BoolTerm.EQ x y

inductive Filter (α) (n: ℕ) where
| BT   : BoolTerm α n   → Filter α n
| Not  : Filter α n → Filter α n
| And  : Filter α n → Filter α n → Filter α n
| Or   : Filter α n → Filter α n → Filter α n

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

set_option diagnostics true

def Query.evaluate (q: Query α n) (d: Database α) : Relation α n := match q with
| Rel   n  s  => Eq.mp (congrArg (Relation α) (d.wf n s)) (d (n,s)).snd
| Proj ts q => let r := evaluate q d
  Multiset.map (λ t ↦ Vector.map (λ u ↦ Term.eval u t) ts) r
| Sel   φ  q  => sorry
| Prod  q₁ q₂ => sorry
| Sum   q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ + r₂
| Dedup q     => let r := evaluate q d; Multiset.dedup r
| Diff  q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ - r₂

end Query
