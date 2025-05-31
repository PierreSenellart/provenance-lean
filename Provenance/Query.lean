import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Prod.Lex

import Provenance.Database

variable {T: Type} [ValueType T] [AddCommSemigroup T] [Sub T] [Mul T]
variable {K: Type} [Zero K]

inductive Term T n where
| const : T → Term T n
| index : Fin n → Term T n
| add : Term T n → Term T n → Term T n
| sub : Term T n → Term T n → Term T n
| mul : Term T n → Term T n → Term T n

def Term.castToAnnotatedTuple (t: Term T n) : Term (T⊕K) (n+1) := match t with
| const c => const (Sum.inl c)
| index k => index (k.castLT (k.val_lt_of_le (Nat.le_add_right n 1)))
| add t₁ t₂ => add t₁.castToAnnotatedTuple t₂.castToAnnotatedTuple
| sub t₁ t₂ => sub t₁.castToAnnotatedTuple t₂.castToAnnotatedTuple
| mul t₁ t₂ => mul t₁.castToAnnotatedTuple t₂.castToAnnotatedTuple

def Term.eval (term: Term T n) (tuple: Tuple T n) := match term with
  | const a => a
  | index k => tuple k
  | add t₁ t₂ => (t₁.eval tuple) + (t₂.eval tuple)
  | sub t₁ t₂ => (t₁.eval tuple) - (t₂.eval tuple)
  | mul t₁ t₂ => (t₁.eval tuple) * (t₂.eval tuple)

instance : Coe T (Term T n) where
  coe a:= Term.const a

instance : OfNat (Term ℕ n) (a: ℕ) where
  ofNat := Term.const a

prefix:max "#" => Term.index

inductive BoolTerm (T) (n: ℕ) where
| EQ : Term T n → Term T n → BoolTerm T n
| NE : Term T n → Term T n → BoolTerm T n
| LE : Term T n → Term T n → BoolTerm T n
| LT : Term T n → Term T n → BoolTerm T n
| GE : Term T n → Term T n → BoolTerm T n
| GT : Term T n → Term T n → BoolTerm T n

def BoolTerm.castToAnnotatedTuple (bt: BoolTerm T n): BoolTerm (T⊕K) (n+1) :=
  match bt with
  | EQ a b => EQ a.castToAnnotatedTuple b.castToAnnotatedTuple
  | NE a b => NE a.castToAnnotatedTuple b.castToAnnotatedTuple
  | LE a b => LE a.castToAnnotatedTuple b.castToAnnotatedTuple
  | LT a b => LT a.castToAnnotatedTuple b.castToAnnotatedTuple
  | GE a b => GE a.castToAnnotatedTuple b.castToAnnotatedTuple
  | GT a b => GT a.castToAnnotatedTuple b.castToAnnotatedTuple

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

def Filter.castToAnnotatedTuple (f: Filter T n): Filter (T⊕K) (n+1) := match f with
| BT  φ     => BT φ.castToAnnotatedTuple
| Not φ     => Not φ.castToAnnotatedTuple
| And φ₁ φ₂ => And φ₁.castToAnnotatedTuple φ₂.castToAnnotatedTuple
| Or  φ₁ φ₂ => Or φ₁.castToAnnotatedTuple φ₂.castToAnnotatedTuple

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

inductive AggFunc
| sum


def addFn (a b : T) := a + b
instance : @Std.Commutative T addFn where
  comm := add_comm
instance : @Std.Associative T addFn where
  assoc := add_assoc

def AggFunc.eval (a: AggFunc) (m: Multiset T) := match a with
| sum => m.fold (addFn: T→T→T) 0

inductive Query (T: Type) : ℕ → Type
| Rel   : (n: ℕ) → String → Query T n
| Proj  : Tuple (Term T n) m → Query T n → Query T m
| Sel   : Filter T n → Query T n → Query T n
| Prod {n₁: Fin n} : Query T n₁ → Query T (n-n₁) → Query T n
| Sum   : Query T n → Query T n → Query T n
| Dedup : Query T n → Query T n
| Diff  : Query T n → Query T n → Query T n
| Agg       : Tuple (Fin m) n₁ → Tuple (Term T m) n₂ → Tuple AggFunc n₂ → Query T m → Query T (n₁+n₂)

def Query.noAgg (q: Query T n): Prop := match q with
| Rel   n  s  => True
| Proj  _ q   => q.noAgg
| Sel   _  q  => q.noAgg
| Prod  q₁ q₂ => q₁.noAgg ∧ q₂.noAgg
| Sum   q₁ q₂ => q₁.noAgg ∧ q₂.noAgg
| Dedup q     => q.noAgg
| Diff  q₁ q₂ => q₁.noAgg ∧ q₂.noAgg
| Agg _ _ _ q => False

def Query.noAggDecidable {T: Type} {n: ℕ}: DecidablePred (@Query.noAgg T n):=
  fun (q: Query T n) => match q with
  | Rel n s => isTrue (by simp[noAgg])
  | Proj  _ q'   => match q'.noAggDecidable with
    | isTrue h => isTrue (by simp[noAgg]; exact h)
    | isFalse h => isFalse (by simp[noAgg]; exact h)
  | Sel   _  q'  => match q'.noAggDecidable with
    | isTrue h => isTrue (by simp[noAgg]; exact h)
    | isFalse h => isFalse (by simp[noAgg]; exact h)
  | Prod  q₁ q₂ => match q₁.noAggDecidable, q₂.noAggDecidable with
    | isTrue h₁,  isTrue h₂  => isTrue (by simp[noAgg]; exact ⟨h₁,h₂⟩)
    | isFalse h₁, _          => isFalse (by simp[noAgg]; simp[h₁])
    | _,          isFalse h₂ => isFalse (by simp[noAgg]; simp[h₂])
  | Sum   q₁ q₂ => match q₁.noAggDecidable, q₂.noAggDecidable with
    | isTrue h₁,  isTrue h₂  => isTrue (by simp[noAgg]; exact ⟨h₁,h₂⟩)
    | isFalse h₁, _          => isFalse (by simp[noAgg]; simp[h₁])
    | _,          isFalse h₂ => isFalse (by simp[noAgg]; simp[h₂])
  | Dedup q'     => match q'.noAggDecidable with
    | isTrue h => isTrue (by simp[noAgg]; exact h)
    | isFalse h => isFalse (by simp[noAgg]; exact h)
  | Diff  q₁ q₂ => match q₁.noAggDecidable, q₂.noAggDecidable with
    | isTrue h₁,  isTrue h₂  => isTrue (by simp[noAgg]; exact ⟨h₁,h₂⟩)
    | isFalse h₁, _          => isFalse (by simp[noAgg]; simp[h₁])
    | _,          isFalse h₂ => isFalse (by simp[noAgg]; simp[h₂])
  | Agg _ _ _ q' => isFalse (by simp[noAgg])

instance {T: Type} {n: ℕ} : DecidablePred (@Query.noAgg T n) := Query.noAggDecidable

set_option linter.unusedSectionVars false
@[simp]
theorem Query.noAggProd {q: Query T n} :
  q.noAgg → ∀ {n₁: Fin n} {q₁: Query T n₁} {q₂: Query T (n-n₁)} (_: q = Prod q₁ q₂), q₁.noAgg ∧ q₂.noAgg  := by
    intro hna n₁ q₁ q₂ hq
    unfold noAgg at hna
    simp[hq] at hna
    assumption

@[simp]
theorem Query.noAggSum {q: Query T n} :
  q.noAgg → ∀ {q₁: Query T n} {q₂: Query T n} (_: q = Sum q₁ q₂), q₁.noAgg ∧ q₂.noAgg  := by
    intro hna q₁ q₂ hq
    unfold noAgg at hna
    simp[hq] at hna
    assumption

@[simp]
theorem Query.noAggDiff {q: Query T n} :
  q.noAgg → ∀ {q₁: Query T n} {q₂: Query T n} (_: q = Diff q₁ q₂), q₁.noAgg ∧ q₂.noAgg  := by
    intro hna q₁ q₂ hq
    unfold noAgg at hna
    simp[hq] at hna
    assumption

@[simp]
theorem Query.noAggProj {q: Query T n} :
  q.noAgg → ∀ {m} {t} {q': Query T m} (_: q = Proj t q'), q'.noAgg := by
    intro hna m t q' hq
    unfold noAgg at hna
    rw[hq] at hna
    assumption

@[simp]
theorem Query.noAggSel {q: Query T n} :
  q.noAgg → ∀ {φ} {q': Query T n} (_: q = Sel φ q'), q'.noAgg := by
    intro hna φ q' hq
    unfold noAgg at hna
    rw[hq] at hna
    assumption

@[simp]
theorem Query.noAggDedup {q: Query T n} :
  q.noAgg → ∀ {q': Query T n} (_: q = Dedup q'), q'.noAgg := by
    intro hna q' hq
    unfold noAgg at hna
    rw[hq] at hna
    assumption

prefix:max "Π " => Query.Proj
prefix:max "σ " => Query.Sel
infix:80 " × " => Query.Prod
infix:50 " ⊎ " => Query.Sum
prefix:max "ε " => Query.Dedup
infix:50 " - " => Query.Diff
infix:1020 " ⋈ " => λ q₁ φ ↦ λ q₂ ↦ (σ φ) (q₁ × q₂)
infix:50 " ∪ " => λ q₁ q₂ ↦ ε (q₁ ⊎ q₂)

def Query.arity (_: Query T n) := n

def Query.aggdepth2_plus_depth (q: Query T n) : ℕ := match q with
| Rel   n  s  => 0
| Proj  _ q   => let d := q.aggdepth2_plus_depth; d+1
| Sel   _  q  => let d := q.aggdepth2_plus_depth; d+1
| Prod  q₁ q₂ =>
  let d₁ := q₁.aggdepth2_plus_depth
  let d₂ := q₂.aggdepth2_plus_depth
  (max d₁ d₂)+1
| Sum   q₁ q₂ =>
  let d₁ := q₁.aggdepth2_plus_depth
  let d₂ := q₂.aggdepth2_plus_depth
  (max d₁ d₂)+1
| Dedup q     => let d := q.aggdepth2_plus_depth; d+1
| Diff  q₁ q₂ =>
  let d₁ := q₁.aggdepth2_plus_depth
  let d₂ := q₂.aggdepth2_plus_depth
  (max d₁ d₂)+1
| Agg _ _ _ q => let d := q.aggdepth2_plus_depth; (d+3)

def Query.evaluate (q: Query T n) (d: WFDatabase T): Relation T n := match q with
| Rel   n  s  =>
  match h : d.db (n, s) with
  | none => (∅: Multiset (Tuple T n))
  | some rn => Eq.mp (congrArg (Relation T) (d.wf n s rn h)) rn.snd
| Proj ts q => let r := evaluate q d; Multiset.map (λ t ↦ λ k ↦ (ts k).eval t) r
| Sel   φ  q  => let r := evaluate q d; @Multiset.filter _ φ.eval φ.evalDecidable r
| @Prod _ n n₁ q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ := evaluate q₂ d
  Eq.mp (by
    have : n₁ + (n-n₁) = n := by omega
    rw[this]
  ) (r₁ * r₂)
| Sum   q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ + r₂
| Dedup q     => let r := evaluate q d; Multiset.dedup r
| Diff  q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ - r₂
| @Agg _ m n₁ n₂ is ts as q =>
    let r := evaluate ε (Π (λ (k: Fin n₁) ↦ #(is k)) q) d
    let s := evaluate q d
    r.map (λ t ↦ Fin.append t (
      λ (k: Fin n₂) ↦ ((as k).eval (
        (s.filter (λ u ↦ ∀ k': Fin n₁, u (is k') = t k')).map (λ u ↦ (ts k).eval u)
      ))
    ))
termination_by q.aggdepth2_plus_depth
decreasing_by
  all_goals simp[aggdepth2_plus_depth]
  any_goals refine Nat.lt_add_one_of_le ?_
  any_goals exact Nat.le_max_left _ _
  any_goals exact Nat.le_max_right _ _
