import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Prod.Lex

import Provenance.Algorithms.CompOp
import Provenance.Database
import Provenance.Util.ValueTypeNull

/-!
# Relational algebra

This file defines the abstract syntax and semantics of relational algebra queries over
plain (unannotated) databases. The language is the *extended relational algebra*
described in Section III of
[Sen, Maniu & Senellart, *ProvSQL: A General System for Keeping Track of the
Provenance and Probability of Data*][sen2026provsql], with multiset semantics,
explicit duplicate elimination, multiset difference, and aggregation.

## Main definitions

* `Term T n` – an expression that evaluates to a value of type `T` in the context of
  a tuple of arity `n` (constants, tuple projections, and arithmetic operations)
* `Query T` – a relational algebra query: selection, projection, union, join,
  difference, and renaming
* `Query.evaluate` – the standard set semantics of queries over `Database T`

## References

* [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql] (Section III)
-/

variable {T: Type} [ValueType T]

inductive Term T n where
| const : T → Term T n
| index : Fin n → Term T n
| add : Term T n → Term T n → Term T n
| sub : Term T n → Term T n → Term T n
| mul : Term T n → Term T n → Term T n

def Term.repr [Repr T] : Term T n → ℕ → Std.Format
| const a, _ => reprArg a
| index k, _ => "#" ++ (reprArg k)
| add t₁ t₂, p => Repr.addAppParen (repr t₁ p ++ "+" ++ repr t₂ p) p
| sub t₁ t₂, p => Repr.addAppParen (repr t₁ p ++ "-" ++ repr t₂ p) p
| mul t₁ t₂, p => Repr.addAppParen (repr t₁ p ++ "*" ++ repr t₂ p) p

instance [Repr α] : Repr (Term α n) := ⟨Term.repr⟩

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

theorem Term.castToAnnotatedTuple_eval [HasAltLinearOrder K] [SemiringWithMonus K] (t: Term T n) (tuple: Tuple T n) :
∀ α: K,
  t.castToAnnotatedTuple.eval (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α]) = Sum.inl (t.eval tuple) := by
  intro α
  induction t with
  | const c =>
    unfold castToAnnotatedTuple eval
    simp
  | index k =>
    unfold castToAnnotatedTuple eval
    have hk : k.castLT (lt_trans k.isLt (lt_add_one n)) = Fin.castAdd 1 k := rfl
    rw[hk]
    rw[Fin.append_left]
  | add t₁ t₂ ih₁ ih₂ =>
    unfold castToAnnotatedTuple eval
    rw[ih₁, ih₂]
    simp[(·+·),Add.add]
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold castToAnnotatedTuple eval
    rw[ih₁, ih₂]
    simp[(·-·),Sub.sub]
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold castToAnnotatedTuple eval
    rw[ih₁, ih₂]
    simp[(·*·),Mul.mul]

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

def BoolTerm.repr [Repr T] : BoolTerm T n → ℕ → Std.Format
| EQ t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ "==" ++ t₂.repr p) p
| NE t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ "!=" ++ t₂.repr p) p
| LE t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ "<=" ++ t₂.repr p) p
| LT t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ "<" ++ t₂.repr p) p
| GE t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ ">=" ++ t₂.repr p) p
| GT t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ ">" ++ t₂.repr p) p

instance [Repr α] : Repr (BoolTerm α n) := ⟨BoolTerm.repr⟩

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

/-- The comparison a Boolean term makes. -/
def BoolTerm.toCompOp : BoolTerm T n → CompOp
| EQ _ _ => CompOp.eq
| NE _ _ => CompOp.ne
| LE _ _ => CompOp.le
| LT _ _ => CompOp.lt
| GE _ _ => CompOp.ge
| GT _ _ => CompOp.gt

/-- The two terms a Boolean term compares. -/
def BoolTerm.args : BoolTerm T n → Term T n × Term T n
| EQ t₁ t₂ | NE t₁ t₂ | LE t₁ t₂ | LT t₁ t₂ | GE t₁ t₂ | GT t₁ t₂ => (t₁, t₂)

/-- **Three-valued evaluation of a comparison**: a comparison with a `NULL`
operand is neither true nor false. -/
def BoolTerm.eval3 (φ: BoolTerm T n) (tuple: Tuple T n) : Kleene :=
  φ.toCompOp.eval3 ((φ.args).1.eval tuple) ((φ.args).2.eval tuple)

/-- The rows a comparison keeps: those on which it is *true*. -/
def BoolTerm.eval (φ: BoolTerm T n) (tuple: Tuple T n) : Prop :=
  φ.eval3 tuple = Kleene.true

theorem BoolTerm.castToAnnotatedTuple_eval3 [HasAltLinearOrder K]
    [SemiringWithMonus K] (t: BoolTerm T n) (tuple: Tuple T n) (α : K) :
    t.castToAnnotatedTuple.eval3
        (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α])
      = t.eval3 tuple := by
  have hop : ∀ (x y : T),
      CompOp.eval3 (T := T ⊕ K) t.toCompOp (Sum.inl x) (Sum.inl y)
        = t.toCompOp.eval3 x y := by
    intro x y
    have hn : ∀ z : T, ValueType.isNull (Sum.inl z : T ⊕ K)
        = ValueType.isNull z := fun _ => rfl
    unfold CompOp.eval3
    rw [hn x, hn y]
    by_cases h : ValueType.isNull x ∨ ValueType.isNull y
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      have hle : ∀ a b : T, ((Sum.inl a : T ⊕ K) ≤ Sum.inl b) ↔ a ≤ b :=
        fun _ _ => Iff.rfl
      have hlt : ∀ a b : T, ((Sum.inl a : T ⊕ K) < Sum.inl b) ↔ a < b := by
        intro a b
        rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
        exact and_congr (hle a b) (not_congr (hle b a))
      have heq : ∀ a b : T, ((Sum.inl a : T ⊕ K) = Sum.inl b) ↔ a = b :=
        fun _ _ => ⟨Sum.inl.inj, congrArg Sum.inl⟩
      refine congrArg Kleene.ofBool ?_
      cases t.toCompOp <;>
        simp only [CompOp.eval, ge_iff_le, gt_iff_lt,
          ne_eq, heq, hle, hlt]
  cases t <;>
    (simp only [BoolTerm.castToAnnotatedTuple, BoolTerm.eval3, BoolTerm.toCompOp,
       BoolTerm.args, Term.castToAnnotatedTuple_eval];
     exact hop _ _)

theorem BoolTerm.castToAnnotatedTuple_eval [HasAltLinearOrder K]
    [SemiringWithMonus K] (t: BoolTerm T n) (tuple: Tuple T n) :
    ∀ α: K, t.castToAnnotatedTuple.eval
        (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α]) = t.eval tuple := by
  intro α
  unfold BoolTerm.eval
  rw [BoolTerm.castToAnnotatedTuple_eval3]

@[reducible] def BoolTerm.evalDecidable (φ: BoolTerm T n) : DecidablePred φ.eval :=
  fun _ => inferInstanceAs (Decidable (_ = _))

inductive Selection (T) (n: ℕ) where
| BT   : BoolTerm T n   → Selection T n
| Not  : Selection T n → Selection T n
| And  : Selection T n → Selection T n → Selection T n
| Or   : Selection T n → Selection T n → Selection T n
| True : Selection T n

def Selection.repr [Repr T] : Selection T n → ℕ → Std.Format
| BT t, p => t.repr p
| Not f, p => "¬" ++ (Repr.addAppParen (f.repr p) p)
| And t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ "∧" ++ t₂.repr p) p
| Or t₁ t₂, p => Repr.addAppParen (t₁.repr p ++ "∨" ++ t₂.repr p) p
| True, _ => "True"

instance [Repr α] : Repr (Selection α n) := ⟨Selection.repr⟩

def Selection.castToAnnotatedTuple (f: Selection T n): Selection (T⊕K) (n+1) := match f with
| BT  t     => BT t.castToAnnotatedTuple
| Not φ     => Not φ.castToAnnotatedTuple
| And φ₁ φ₂ => And φ₁.castToAnnotatedTuple φ₂.castToAnnotatedTuple
| Or  φ₁ φ₂ => Or φ₁.castToAnnotatedTuple φ₂.castToAnnotatedTuple
| True      => True

/-- **Three-valued evaluation of a selection**, in Kleene's logic: a row on
which the predicate is unknown is selected by neither it nor its negation. -/
def Selection.eval3 (φ: Selection T n) (tuple: Tuple T n) : Kleene := match φ with
| BT  φ     => φ.eval3 tuple
| Not φ     => (φ.eval3 tuple).not
| And φ₁ φ₂ => (φ₁.eval3 tuple).and (φ₂.eval3 tuple)
| Or  φ₁ φ₂ => (φ₁.eval3 tuple).or (φ₂.eval3 tuple)
| True      => Kleene.true

/-- The rows a selection keeps: those on which it is *true*. -/
def Selection.eval (φ: Selection T n) (tuple: Tuple T n) : Prop :=
  φ.eval3 tuple = Kleene.true

theorem Selection.castToAnnotatedTuple_eval3 [HasAltLinearOrder K]
    [SemiringWithMonus K] (φ: Selection T n) (tuple: Tuple T n) (α : K) :
    φ.castToAnnotatedTuple.eval3
        (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α])
      = φ.eval3 tuple := by
  induction φ with
  | BT t => exact BoolTerm.castToAnnotatedTuple_eval3 t tuple α
  | Not φ ih => show (_ : Kleene).not = _; rw [ih]; rfl
  | And φ₁ φ₂ ih₁ ih₂ => show (_ : Kleene).and _ = _; rw [ih₁, ih₂]; rfl
  | Or φ₁ φ₂ ih₁ ih₂ => show (_ : Kleene).or _ = _; rw [ih₁, ih₂]; rfl
  | True => rfl

theorem Selection.castToAnnotatedTuple_eval [HasAltLinearOrder K]
    [SemiringWithMonus K] (φ: Selection T n) (tuple: Tuple T n) :
    ∀ α: K, φ.castToAnnotatedTuple.eval
        (Fin.append (λ k ↦ Sum.inl (tuple k)) ![Sum.inr α]) = φ.eval tuple := by
  intro α
  unfold Selection.eval
  rw [Selection.castToAnnotatedTuple_eval3]

@[reducible] def Selection.evalDecidable (φ : Selection T n) : DecidablePred φ.eval :=
  fun _ => inferInstanceAs (Decidable (_ = _))

@[simp] theorem Selection.eval_bt (b : BoolTerm T n) (t : Tuple T n) :
    (Selection.BT b).eval t ↔ b.eval t := Iff.rfl

/-- Where nothing is null a comparison reads two-valuedly. -/
@[simp] theorem BoolTerm.eval_iff [NoNulls T] (b : BoolTerm T n)
    (t : Tuple T n) :
    b.eval t ↔ b.toCompOp.eval ((b.args).1.eval t) ((b.args).2.eval t) := by
  unfold BoolTerm.eval BoolTerm.eval3
  rw [CompOp.eval3_eq_true_iff _ (isNull_eq_false _) (isNull_eq_false _)]

@[simp] theorem Selection.eval_and (φ ψ : Selection T n) (t : Tuple T n) :
    (Selection.And φ ψ).eval t ↔ φ.eval t ∧ ψ.eval t :=
  Kleene.and_eq_true_iff _ _

@[simp] theorem Selection.eval_or (φ ψ : Selection T n) (t : Tuple T n) :
    (Selection.Or φ ψ).eval t ↔ φ.eval t ∨ ψ.eval t :=
  Kleene.or_eq_true_iff _ _

/-- **A row is kept by `NOT φ` when `φ` is false**, which is not the same as
`φ` failing to be true: a row on which `φ` is unknown is kept by neither. -/
@[simp] theorem Selection.eval_not (φ : Selection T n) (t : Tuple T n) :
    (Selection.Not φ).eval t ↔ φ.eval3 t = Kleene.false :=
  Kleene.not_eq_true_iff _

@[simp] theorem Selection.eval_true (t : Tuple T n) :
    (Selection.True : Selection T n).eval t := rfl

/-- Where nothing is null no selection is ever unknown. -/
theorem Selection.eval3_ne_unknown [NoNulls T] (t : Tuple T n) :
    ∀ φ : Selection T n, φ.eval3 t ≠ Kleene.unknown
  | BT b => by
    show b.toCompOp.eval3 _ _ ≠ _
    rw [CompOp.eval3_eq_ofBool]
    cases decide (b.toCompOp.eval ((b.args).1.eval t) ((b.args).2.eval t)) <;>
      simp [Kleene.ofBool]
  | Not φ => by
    have h := eval3_ne_unknown t φ
    cases e : φ.eval3 t <;> simp_all [Selection.eval3, Kleene.not]
  | And φ ψ => by
    have h₁ := eval3_ne_unknown t φ
    have h₂ := eval3_ne_unknown t ψ
    cases e₁ : φ.eval3 t <;> cases e₂ : ψ.eval3 t <;>
      simp_all [Selection.eval3, Kleene.and]
  | Or φ ψ => by
    have h₁ := eval3_ne_unknown t φ
    have h₂ := eval3_ne_unknown t ψ
    cases e₁ : φ.eval3 t <;> cases e₂ : ψ.eval3 t <;>
      simp_all [Selection.eval3, Kleene.or]
  | True => by simp [Selection.eval3]

/-- Negation is classical where nothing is null. -/
theorem Selection.eval_not_iff [NoNulls T] (φ : Selection T n) (t : Tuple T n) :
    (Selection.Not φ).eval t ↔ ¬ φ.eval t := by
  have h := Selection.eval3_ne_unknown t φ
  show (φ.eval3 t).not = Kleene.true ↔ ¬ (φ.eval3 t = Kleene.true)
  cases e : φ.eval3 t <;> simp_all [Kleene.not]

instance : Coe (BoolTerm T n) (Selection T n) where
  coe bt := Selection.BT bt

/-- Addition as a binary function, the fold of the `⊕`-sum performed by
the rewriting-target operator `Query.ProvSum` (and by its general-syntax
counterpart `AggQuery.ProvSum`). -/
def addFn (a b : T) := a + b
instance : @Std.Commutative T addFn where
  comm := add_comm
instance : @Std.Associative T addFn where
  assoc := add_assoc

/-- An aggregate function on *sequences* of values: an arbitrary function
from finite sequences over `T` to `T`. Beyond the monoid-shaped `⊕`-sum
of `Query.ProvSum`, this interface covers non-commutative aggregates –
such as `PICKFIRST`, whose result depends on the order of its input – and
non-associative ones. It is the aggregate interface of the fused `Having`
operator, whose possible-world semantics does not need any algebraic
structure on the aggregate. -/
def SeqAggFunc (T : Type) := List T → T

namespace SeqAggFunc

/-! An aggregate is a total function on sequences, so each one has to say
what it does with the empty sequence. Where a row exists only because its
group does, that value is never read and the choice is immaterial. Where the
row exists on its own – an aggregation over no grouping, a frame that may
exclude the row it is computed for – it is read, by the scalar convention of
`AggValue.predProvScalar`.

The aggregates below are those of a domain with no null, and they give the
zero of the value type over no row. `COUNT` is right that way: SQL counts no
row as `0`. `SUM`, `MIN` and `MAX` are not, since SQL gives `NULL` there, and
`sqlOf` is what makes them so on a domain that has a null – it skips the
nulls, as SQL does, and gives `NULL` when nothing is left. `COUNT(*)` stays
unwrapped, being the one aggregate SQL does *not* read that way. -/

/-- `SUM` as a sequence aggregate; `0` on the empty sequence, where SQL has
`null`. -/
def sum : SeqAggFunc T := fun L => L.foldr (· + ·) 0

/-- `COUNT(*)` as a sequence aggregate (over an `ℕ`-valued domain); `0` on
the empty sequence, as SQL has. -/
def count : SeqAggFunc ℕ := List.length

/-- `MIN`, with the zero of the value type as its default on the empty
sequence, where SQL has `null`. -/
def min : SeqAggFunc T := fun L => match L with
  | [] => 0
  | x :: xs => xs.foldr Min.min x

/-- `MAX`, with the zero of the value type as its default on the empty
sequence, where SQL has `null`. -/
def max : SeqAggFunc T := fun L => match L with
  | [] => 0
  | x :: xs => xs.foldr Max.max x

/-- `PICKFIRST`: the first value of the sequence, with the zero of the value
type as its default on the empty one, where SQL has `null`. -/
def pickFirst : SeqAggFunc T := fun L => L.headD 0

/-- **SQL's reading of an aggregate on a domain with a null**: skip the
nulls, and give `NULL` when nothing is left. `SUM`, `MIN` and `MAX` are read
this way. `COUNT` is not: it gives `0` over no row, which is what the
unwrapped aggregate already does. -/
def sqlOf {V : Type} [ValueTypeNull V] (f : SeqAggFunc V) : SeqAggFunc V := fun L =>
  if (L.filter (fun a => decide (a ≠ ValueTypeNull.null))).isEmpty
  then ValueTypeNull.null
  else f (L.filter (fun a => decide (a ≠ ValueTypeNull.null)))

/-- **An aggregate over no row is null.** This is what the scalar
convention needed and could not have: an aggregation without grouping over
an empty input, and a frame that excludes the row it is computed for, both
read their value here. -/
@[simp] theorem sqlOf_nil {V : Type} [ValueTypeNull V] (f : SeqAggFunc V) :
    f.sqlOf [] = ValueTypeNull.null := rfl

/-- **Away from the null the SQL reading is the aggregate itself.** The
results proved of an aggregate over a domain with no null are recovered:
they are this case. -/
theorem sqlOf_eq_of_no_null {V : Type} [ValueTypeNull V] (f : SeqAggFunc V)
    {L : List V} (hne : L ≠ [])
    (h : ∀ a ∈ L, a ≠ ValueTypeNull.null) : f.sqlOf L = f L := by
  have hfil : L.filter (fun a => decide (a ≠ ValueTypeNull.null)) = L :=
    List.filter_eq_self.mpr (fun a ha => by simp [h a ha])
  unfold sqlOf
  rw [hfil, ite_eq_right (by simpa using hne)]

/-- An aggregate over nothing but nulls is null, as it is over no row. -/
theorem sqlOf_eq_null_of_all_null {V : Type} [ValueTypeNull V]
    (f : SeqAggFunc V) {L : List V} (h : ∀ a ∈ L, a = ValueTypeNull.null) :
    f.sqlOf L = ValueTypeNull.null := by
  have hfil : L.filter (fun a => decide (a ≠ ValueTypeNull.null)) = [] :=
    List.filter_eq_nil_iff.mpr (fun a ha => by simp [h a ha])
  unfold sqlOf
  rw [hfil]
  rfl

end SeqAggFunc

inductive Query (T: Type) : ℕ → Type
| Rel   : (n: ℕ) → String → Query T n
| Proj  : Tuple (Term T n) m → Query T n → Query T m
| Sel   : Selection T n → Query T n → Query T n
| Prod {hn: n₁+n₂=n} : Query T n₁ → Query T n₂ → Query T n
| Sum   : Query T n → Query T n → Query T n
| Dedup : Query T n → Query T n
| Diff  : Query T n → Query T n → Query T n
/-- Provenance aggregation: group by the key columns of the first
argument and `⊕`-sum the term of the second over each group into a single
trailing output column. It is not a *source* operator – aggregation as
such lives on the general syntax (`AggQuery.Gamma`) – but the *target* of
the (R1)–(R4) rewriting: the ⊕-gate creation of the `ε` and `∖` rules of
`Query.rewriting`. Its general-syntax counterpart is
`AggQuery.ProvSum`. -/
| ProvSum   : Tuple (Fin m) n₁ → Term T m → Query T m → Query T (n₁+1)
/-- The fused `HAVING` operator: grouping by the indices of the first
argument, computing the sequence aggregates of the third argument applied
to the terms of the second (each group read in the canonical tuple order,
which plays the role of the ordering `≼` of non-commutative aggregates),
and keeping only the groups whose aggregate value in column `l` (the
`Fin n₂` argument) compares, via the comparison operator, with the value of
the regular term (the `Term T n₁` argument, evaluated on the group key –
this covers both query constants and group-key attributes). The output has
the group key followed by the aggregate values. -/
| Having    : Tuple (Fin m) n₁ → Tuple (Term T m) n₂ → Tuple (SeqAggFunc T) n₂ →
    CompOp → Fin n₂ → Term T n₁ → Query T m → Query T (n₁+n₂)

def Query.repr [Repr T] : Query T n → ℕ → Std.Format
| Rel _ s, p => s
| Proj ts q, p => "Π_" ++ (Repr.addAppParen (ts.repr p) p) ++ (Repr.addAppParen (q.repr p) p)
| Sel φ q, p => "σ_" ++ (Repr.addAppParen (φ.repr p) p) ++ (Repr.addAppParen (q.repr p) p)
| Prod q₁ q₂, p => Repr.addAppParen (q₁.repr p ++ "×" ++ q₂.repr p) p
| Sum q₁ q₂, p => Repr.addAppParen (q₁.repr p ++ "⊎" ++ q₂.repr p) p
| Dedup q, p => "ε" ++ Repr.addAppParen (q.repr p) p
| Diff q₁ q₂, p => Repr.addAppParen (q₁.repr p ++ "-" ++ q₂.repr p) p
| ProvSum is t q, p =>
  "γ⊕_" ++ (Repr.addAppParen (is.repr p) p)
    ++ (Repr.addAppParen (t.repr p) p)
    ++ (Repr.addAppParen (q.repr p) p)
| Having is ts _ op l s q, p =>
  "γHaving_" ++ (Repr.addAppParen (is.repr p) p)
    ++ (Repr.addAppParen (ts.repr p) p)
    ++ "[#" ++ (reprArg l) ++ (reprArg op) ++ (Repr.addAppParen (s.repr p) p) ++ "]"
    ++ (Repr.addAppParen (q.repr p) p)

instance [Repr α] : Repr (Query α n) := ⟨Query.repr⟩

/-- The **source fragment** of the classical syntax: the operators a
query is *written* with, RA⁺(∖). It excludes the two operators that are
not source operators – `ProvSum`, which the (R1)–(R4) rewriting *emits*,
and the fused `Having`, whose semantics lives on the general syntax – and
is exactly the fragment carrying an annotated semantics
(`Query.evaluateAnnotated`) and accepted by `Query.rewriting`. Its
general-syntax counterpart is `AggQuery.classical`. -/
def Query.source (q: Query T n): Prop := match q with
| Rel   n  s  => True
| Proj  _ q   => q.source
| Sel   _  q  => q.source
| Prod  q₁ q₂ => q₁.source ∧ q₂.source
| Sum   q₁ q₂ => q₁.source ∧ q₂.source
| Dedup q     => q.source
| Diff  q₁ q₂ => q₁.source ∧ q₂.source
| ProvSum _ _ q => False
| Having _ _ _ _ _ _ _ => False

@[reducible] def Query.sourceDecidable {T: Type} {n: ℕ}: DecidablePred (@Query.source T n):=
  fun (q: Query T n) => match q with
  | Rel n s => isTrue (by simp[source])
  | Proj  _ q'   => match q'.sourceDecidable with
    | isTrue h => isTrue (by simp[source]; exact h)
    | isFalse h => isFalse (by simp[source]; exact h)
  | Sel   _  q'  => match q'.sourceDecidable with
    | isTrue h => isTrue (by simp[source]; exact h)
    | isFalse h => isFalse (by simp[source]; exact h)
  | Prod  q₁ q₂ => match q₁.sourceDecidable, q₂.sourceDecidable with
    | isTrue h₁,  isTrue h₂  => isTrue (by simp[source]; exact ⟨h₁,h₂⟩)
    | isFalse h₁, _          => isFalse (by simp[source]; simp[h₁])
    | _,          isFalse h₂ => isFalse (by simp[source]; simp[h₂])
  | Sum   q₁ q₂ => match q₁.sourceDecidable, q₂.sourceDecidable with
    | isTrue h₁,  isTrue h₂  => isTrue (by simp[source]; exact ⟨h₁,h₂⟩)
    | isFalse h₁, _          => isFalse (by simp[source]; simp[h₁])
    | _,          isFalse h₂ => isFalse (by simp[source]; simp[h₂])
  | Dedup q'     => match q'.sourceDecidable with
    | isTrue h => isTrue (by simp[source]; exact h)
    | isFalse h => isFalse (by simp[source]; exact h)
  | Diff  q₁ q₂ => match q₁.sourceDecidable, q₂.sourceDecidable with
    | isTrue h₁,  isTrue h₂  => isTrue (by simp[source]; exact ⟨h₁,h₂⟩)
    | isFalse h₁, _          => isFalse (by simp[source]; simp[h₁])
    | _,          isFalse h₂ => isFalse (by simp[source]; simp[h₂])
  | ProvSum _ _ q' => isFalse (by simp[source])
  | Having _ _ _ _ _ _ _ => isFalse (by simp[source])

instance {T: Type} {n: ℕ} : DecidablePred (@Query.source T n) := Query.sourceDecidable

set_option linter.unusedSectionVars false
@[simp]
theorem Query.sourceProd {q: Query T n} :
  q.source → ∀ {n₁} {q₁: Query T n₁} {q₂: Query T n₂} {hn: n₁+n₂=n}
    (_: q = @Prod T n₁ n₂ n hn q₁ q₂), q₁.source ∧ q₂.source  := by
    intro hna n₁ q₁ q₂ hn₁ hq
    unfold source at hna
    simp[hq] at hna
    assumption

@[simp]
theorem Query.sourceSum {q: Query T n} :
  q.source → ∀ {q₁: Query T n} {q₂: Query T n} (_: q = Sum q₁ q₂), q₁.source ∧ q₂.source  := by
    intro hna q₁ q₂ hq
    unfold source at hna
    simp[hq] at hna
    assumption

@[simp]
theorem Query.sourceDiff {q: Query T n} :
  q.source → ∀ {q₁: Query T n} {q₂: Query T n} (_: q = Diff q₁ q₂), q₁.source ∧ q₂.source  := by
    intro hna q₁ q₂ hq
    unfold source at hna
    simp[hq] at hna
    assumption

@[simp]
theorem Query.sourceProj {q: Query T n} :
  q.source → ∀ {m} {t} {q': Query T m} (_: q = Proj t q'), q'.source := by
    intro hna m t q' hq
    unfold source at hna
    rwa [hq] at hna

@[simp]
theorem Query.sourceSel {q: Query T n} :
  q.source → ∀ {φ} {q': Query T n} (_: q = Sel φ q'), q'.source := by
    intro hna φ q' hq
    unfold source at hna
    rwa [hq] at hna

@[simp]
theorem Query.sourceDedup {q: Query T n} :
  q.source → ∀ {q': Query T n} (_: q = Dedup q'), q'.source := by
    intro hna q' hq
    unfold source at hna
    rwa [hq] at hna

prefix:max "Π " => Query.Proj
prefix:max "σ " => Query.Sel
infix:80 " × " => fun q₁ q₂ => Query.Prod (hn := by first | rfl | omega) q₁ q₂
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
| ProvSum _ _ q => let d := q.aggdepth2_plus_depth; (d+3)
| Having _ _ _ _ _ _ q => let d := q.aggdepth2_plus_depth; (d+3)

/-- The occurrences of the group of key `g` in relation `r`: the multiset of
matching tuples, as a list sorted by the canonical linear order on tuples.
The sort order plays the role of the ordering `≼` along which
non-commutative sequence aggregates read the occurrences of a group; for
commutative aggregates it is irrelevant. -/
def Relation.groupSeq (is : Tuple (Fin m) n₁) (r : Relation T m) (g : Tuple T n₁) :
    List (Tuple T m) :=
  Multiset.sort (Multiset.filter (fun u => ∀ k' : Fin n₁, u (is k') = g k') r) (· ≤ ·)

/-- Standard multiset semantics of a query over a plain database.

The `Diff` case is *all-or-nothing* difference: every copy of a tuple that
occurs at all in `r₂` is removed from `r₁` (deliberately not `Multiset.sub`,
which would subtract multiplicities as in SQL's `EXCEPT ALL`). This matches
the monus-based annotated semantics of difference
(`Query.evaluateAnnotated`) exactly on `0`/`1`-annotated inputs; on general
annotations the two disagree over `ℕ` (see `Nat.counterexample_diff_adequacy`
and `Provenance.QueryAdequacy`). -/
def Query.evaluate (q: Query T n) (d: Database T): Relation T n := match q with
| Rel   n  s  =>
  match d.find n s with
  | none => (∅: Multiset (Tuple T n))
  | some rn => rn
| Proj ts q => let r := evaluate q d; Multiset.map (λ t ↦ λ k ↦ (ts k).eval t) r
| Sel   φ  q  => let r := evaluate q d; @Multiset.filter _ φ.eval φ.evalDecidable r
| @Prod _ n₁ n₂ n hn q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ := evaluate q₂ d
  (r₁ * r₂).cast hn
| Sum   q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ + r₂
| Dedup q     => let r := evaluate q d; Multiset.dedup r
| Diff  q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ : Multiset (Tuple T _) := evaluate q₂ d
  r₁.filter (fun t ↦ t ∉ r₂)
| @ProvSum _ m n₁ is t q =>
    let r := evaluate ε (Π (λ (k: Fin n₁) ↦ #(is k)) q) d
    let s := evaluate q d
    r.map (λ g ↦ Fin.append g (
      λ _: Fin 1 ↦ (
        (s.filter (λ u ↦ ∀ k': Fin n₁, u (is k') = g k')).map (λ u ↦ t.eval u)
      ).fold addFn 0
    ))
| @Having _ m n₁ n₂ is ts fs op l s q =>
    let keys := evaluate ε (Π (λ (k: Fin n₁) ↦ #(is k)) q) d
    let r := evaluate q d
    Multiset.map
      (λ g ↦ Fin.append g
        (λ (k: Fin n₂) ↦ (fs k) ((Relation.groupSeq is r g).map (ts k).eval)))
      (Multiset.filter
        (λ g ↦ op.eval ((fs l) ((Relation.groupSeq is r g).map (ts l).eval)) (s.eval g))
        keys)
termination_by q.aggdepth2_plus_depth
decreasing_by
  all_goals simp[aggdepth2_plus_depth]
  any_goals refine Nat.lt_add_one_of_le ?_
  any_goals exact Nat.le_max_left _ _
  any_goals exact Nat.le_max_right _ _
