/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQuery

/-!
# Derived operators

The operators of this file add nothing to the algebra: each is an
abbreviation, a query built from the basis, and its semantics – plain and
annotated – is the semantics of the query it abbreviates. What they buy is
that the theorems proved of the basis apply to them as they stand, and that
the translation of SQL has something to name.

Padding replaces columns by the null, which is what an outer join does to
the arm with no match. Intersection is a self-join of the two deduplicated
arms on all their columns, matching syntactically as SQL's `INTERSECT`
does – and not `ε(q₁ - (q₁ - q₂))`, which has the same rows but annotates
them by a difference of differences rather than by a conjunction of the two
memberships.
-/

variable {T : Type} {n m : ℕ}

namespace AggQuery

/-! ## Padding -/

section Padding

variable [ValueTypeNull T]

/-- The projection column that reads column `k`, or the null when there is
no column to read. -/
def padCol (c : Option (Fin n)) :
    ProjCol T (ColKind.allReg n) :=
  match c with
  | some k => .term (TermG.index k rfl)
  | none => .term (TermG.const ValueTypeNull.null)

@[simp] theorem padCol_kind (c : Option (Fin n)) :
    (padCol (T := T) c).kind = ColKind.reg := by
  cases c <;> rfl

/-- **Padding**: a projection that reads the columns `π` names and puts the
null where `π` names none. It is what an outer join does to the arm with no
match, and it adds no operator. -/
def pad (π : Fin m → Option (Fin n))
    (q : AggQuery T n (ColKind.allReg n)) : AggQuery T m (ColKind.allReg m) :=
  (Proj (fun j => padCol (π j)) q).castKind (funext fun j => padCol_kind (π j))

/-- The padding that keeps every column of `q` and appends `l` null
columns, as a left outer join does to an unmatched row. -/
def padRight (l : ℕ)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + l) (ColKind.allReg (n + l)) :=
  pad (Fin.addCases (fun i => some i) (fun _ => none)) q

/-- The padding that prepends `l` null columns, as a right outer join
does. -/
def padLeft (l : ℕ)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (l + n) (ColKind.allReg (l + n)) :=
  pad (Fin.addCases (fun _ => none) (fun i => some i)) q

end Padding

/-! ## Intersection -/

section Inter

variable [ValueType T]

/-- The conjunction `⋀_{i<k} #i ≐ #(k+i)`: the two blocks of a doubled
schema agree, column by column, *syntactically* – two nulls being the same
value, as every key comparison in SQL's set operators is. -/
def interCond (k : ℕ) :
    GenPred T (ColKind.allReg (k + k)) :=
  keyJoinCond (fun i : Fin k => Fin.castAdd k i) (fun i : Fin k => Fin.natAdd k i)
    (fun _ => rfl) (fun _ => rfl)

/-- The projection onto the first `a` columns of a schema of `a + b`. -/
def firstCols (a b : ℕ) : Tuple (ProjCol T (ColKind.allReg (a + b))) a :=
  fun i => .term (TermG.index (Fin.castAdd b i) rfl)

/-- The projection onto the last `b` columns of a schema of `a + b`. -/
def lastCols (a b : ℕ) : Tuple (ProjCol T (ColKind.allReg (a + b))) b :=
  fun j => .term (TermG.index (Fin.natAdd a j) rfl)

/-- The projection onto the first block of a doubled schema. -/
def fstBlock (k : ℕ) : Tuple (ProjCol T (ColKind.allReg (k + k))) k :=
  firstCols k k

omit [ValueType T] in
@[simp] theorem firstCols_kind (a b : ℕ) (i : Fin a) :
    ((firstCols (T := T) a b) i).kind = ColKind.reg := rfl

omit [ValueType T] in
@[simp] theorem lastCols_kind (a b : ℕ) (j : Fin b) :
    ((lastCols (T := T) a b) j).kind = ColKind.reg := rfl

omit [ValueType T] in
@[simp] theorem fstBlock_kind (k : ℕ) (i : Fin k) :
    ((fstBlock (T := T) k) i).kind = ColKind.reg := rfl

/-- Doubling an all-regular schema leaves it all-regular. -/
theorem append_allReg (a b : ℕ) :
    Fin.append (ColKind.allReg a) (ColKind.allReg b) = ColKind.allReg (a + b) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- **Intersection**, SQL's `INTERSECT`: one copy of each tuple the two
arms share, matched syntactically. Its annotation is the product of the
two `⊕`-sums, one per arm – the provenance of a conjunction of the two
memberships, which is what `ε(q₁ - (q₁ - q₂))` would not give. -/
def inter (q₁ q₂ : AggQuery T n (ColKind.allReg n)) :
    AggQuery T n (ColKind.allReg n) :=
  (Proj (fstBlock n)
    (Sel (interCond n)
      ((Prod (Dedup q₁) (Dedup q₂)).castKind (append_allReg n n))))
  |>.castKind (funext fun i => fstBlock_kind n i)

end Inter

/-! ## Outer joins -/

section Outer

variable [ValueTypeNull T] {n₁ n₂ : ℕ}

/-- The inner join of the two arms: the rows that match. -/
def innerJoin (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sel φ ((Prod q₁ q₂).castKind (append_allReg n₁ n₂))

/-- The rows of the left arm with no match, padded on the right with
nulls. -/
def leftUnmatched (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  padRight n₂ (Diff q₁
    ((Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
      (funext fun i => firstCols_kind n₁ n₂ i)))

/-- The rows of the right arm with no match, padded on the left with
nulls. -/
def rightUnmatched (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  padLeft n₁ (Diff q₂
    ((Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
      (funext fun j => lastCols_kind n₁ n₂ j)))

/-- **Left outer join**: the matching rows, and the rows of the left arm
with no match padded with nulls. -/
def leftOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sum (innerJoin φ q₁ q₂) (leftUnmatched φ q₁ q₂)

/-- **Right outer join**. -/
def rightOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sum (innerJoin φ q₁ q₂) (rightUnmatched φ q₁ q₂)

/-- **Full outer join**: both arms padded. -/
def fullOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) :
    AggQuery T (n₁ + n₂) (ColKind.allReg (n₁ + n₂)) :=
  Sum (leftOuter φ q₁ q₂) (rightUnmatched φ q₁ q₂)

end Outer

end AggQuery
