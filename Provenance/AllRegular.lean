/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Determinacy
import Provenance.PlainBasis

/-!
# Reading every column as a value

In the plain semantics every column holds a value of the domain: the
kind vector is a *syntactic* index, saying which operators may be
written where, and `AggQueryIn.evaluatePlain` returns plain tuples. The
operators that compare keys – duplicate elimination, the difference, a
grouping's and a partition's indices – are the ones that insist on
regular columns, and `AggQueryIn.Explode` is what bridges them: it reads an
aggregate column as a key, and over a plain relation it is the identity
(its own docstring says so). `AggQueryIn.Retag` does the same between
the two value-armed kinds.

This module makes that into a theorem: **every query is
plain-equivalent to one whose columns are all regular**
(`AggQueryIn.exists_allReg`), so the kind discipline costs nothing in
the plain semantics. Three readings of an aggregate column have exact
regular counterparts – an aggregate atom is the same comparison on the
column, a range atom is its two comparisons, and a column read as a
token is the column – and the one that has none is
`ProjColIn.aggTerm`, which post-composes the column with an arbitrary
function of the domain: no term expresses that.

A window is the other exception, and for a different reason: it is the
one operator whose plain semantics reads the kind vector, reading its
input through `ColKind.readTuple`. That nulling is how the library lists
a frame, and it is one admissible listing: what the document asks of an
aggregation is *determinacy* – the aggregate is symmetric, or any two
peers of the clause carry equal values of the aggregated term – and
under determinacy every listing the clause allows gives one value.
Re-typing changes the listing, since an aggregate column read as a value
enters the tie-break, but only *inside* a block of peers, so a
determinate window reads the same value either way
(`ValueFrame.windowValueOpt_readTuple_of_det`). That is what
`AggQueryIn.Retypable` asks of a window – determinacy on every
instance, quantified as `AggQueryIn.recSettles` is, or an all-regular
input where no column moves – and it is the document's condition rather
than an approximation of it. A `FILTER` clause is asked to read the
occurrence's regular columns, as `sec:agg` says a clause does, and is
then carried through with nothing further to prove.

What this is for: the swaps of `sec:basis` – a selection written with a
difference, a product written with an apply – are stated over queries
whose columns are regular, because that is what `Diff` and an apply's
left side take. Regularizing first is what lets them apply to a query
that has aggregate columns in its *type* and ordinary values in its
rows.
-/

variable {T : Type} [ValueType T]

/-! ## The three readings that have regular counterparts -/

/-- **A term reading every column as a regular one.** A provenance
column is read as the value it holds; the aggregate-comparison gate has
no plain value of its own (the generic evaluators give it `0`), so it
becomes that constant. -/
def TermGIn.toReg {c n : ℕ} {κ : Fin n → ColKind} :
    TermGIn T c κ → TermGIn T c (ColKind.allReg n)
  | .const a => .const a
  | .outer j => .outer j
  | .index k _ => .index k rfl
  | .provIndex k _ => .index k rfl
  | .cmpAgg _ _ _ _ => .const 0
  | .chiGate op t₁ t₂ => .chiGate op t₁.toReg t₂.toReg
  | .add t₁ t₂ => .add t₁.toReg t₂.toReg
  | .sub t₁ t₂ => .sub t₁.toReg t₂.toReg
  | .mul t₁ t₂ => .mul t₁.toReg t₂.toReg
  | .caseWhen op t₁ t₂ t₃ t₄ =>
      .caseWhen op t₁.toReg t₂.toReg t₃.toReg t₄.toReg
  | .coalesce t₁ t₂ => .coalesce t₁.toReg t₂.toReg

/-- It reads what the term reads. -/
theorem TermGIn.evalPlain_toReg {c n : ℕ} {κ : Fin n → ColKind}
    (t : TermGIn T c κ) (u : Tuple T n) (γ : Fin c → T) :
    (t.toReg).evalPlain u γ = t.evalPlain u γ := by
  induction t with
  | const a => rfl
  | outer j => rfl
  | index k h => rfl
  | provIndex k h => rfl
  | cmpAgg k h op t ih => rfl
  | chiGate op t₁ t₂ ih₁ ih₂ => rfl
  | add t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact congrArg₂ _ ih₁ ih₂
  | caseWhen op t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    show (if op.eval3 _ _ = Kleene.true then _ else _) = _
    rw [ih₁, ih₂, ih₃, ih₄]
    rfl
  | coalesce t₁ t₂ ih₁ ih₂ =>
    show (if ValueType.isNull _ then _ else _) = _
    rw [ih₁, ih₂]
    rfl

/-- **A predicate reading every column as a regular one.** An aggregate
atom becomes the same comparison on the column, and a range atom the
conjunction of its two – which is what it says on a row, the difference
between them being what they annotate. -/
def GenPredIn.toReg {c n : ℕ} {κ : Fin n → ColKind} :
    GenPredIn T c κ → GenPredIn T c (ColKind.allReg n)
  | .cmp op t₁ t₂ => .cmp op t₁.toReg t₂.toReg
  | .aggCmp k _ op t => .cmp op (.index k rfl) t.toReg
  | .aggRange k _ op₁ t₁ op₂ t₂ =>
      .and (.cmp op₁ (.index k rfl) t₁.toReg)
        (.cmp op₂ (.index k rfl) t₂.toReg)
  | .and φ ψ => .and φ.toReg ψ.toReg
  | .or φ ψ => .or φ.toReg ψ.toReg
  | .not φ => .not φ.toReg

/-- It reads what the predicate reads. -/
theorem GenPredIn.evalPlain3_toReg {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (u : Tuple T n) (γ : Fin c → T) :
    (φ.toReg).evalPlain3 u γ = φ.evalPlain3 u γ := by
  induction φ with
  | cmp op t₁ t₂ =>
    show CompOp.eval3 op _ _ = CompOp.eval3 op _ _
    rw [TermGIn.evalPlain_toReg, TermGIn.evalPlain_toReg]
  | aggCmp k h op t =>
    show CompOp.eval3 op _ _ = CompOp.eval3 op _ _
    rw [TermGIn.evalPlain_toReg]
    rfl
  | aggRange k h op₁ t₁ op₂ t₂ =>
    show Kleene.and (CompOp.eval3 op₁ _ _) (CompOp.eval3 op₂ _ _)
      = Kleene.and (CompOp.eval3 op₁ _ _) (CompOp.eval3 op₂ _ _)
    rw [TermGIn.evalPlain_toReg, TermGIn.evalPlain_toReg]
    rfl
  | and φ ψ ihφ ihψ => exact congrArg₂ Kleene.and ihφ ihψ
  | or φ ψ ihφ ihψ => exact congrArg₂ Kleene.or ihφ ihψ
  | not φ ih => exact congrArg Kleene.not ih

/-- It keeps the same rows. -/
theorem GenPredIn.holdsPlain_toReg {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) (u : Tuple T n) (γ : Fin c → T) :
    (φ.toReg).holdsPlain u γ ↔ φ.holdsPlain u γ := by
  unfold GenPredIn.holdsPlain
  rw [GenPredIn.evalPlain3_toReg]

/-- And it has no aggregate atom left. -/
@[simp] theorem GenPredIn.hasAggAtom_toReg {c n : ℕ} {κ : Fin n → ColKind}
    (φ : GenPredIn T c κ) : (φ.toReg).hasAggAtom = false := by
  induction φ with
  | cmp op t₁ t₂ => rfl
  | aggCmp k h op t => rfl
  | aggRange k h op₁ t₁ op₂ t₂ => rfl
  | and φ ψ ihφ ihψ => rw [GenPredIn.toReg, GenPredIn.hasAggAtom, ihφ, ihψ]; rfl
  | or φ ψ ihφ ihψ => rw [GenPredIn.toReg, GenPredIn.hasAggAtom, ihφ, ihψ]; rfl
  | not φ ih => rw [GenPredIn.toReg, GenPredIn.hasAggAtom, ih]

/-- **A projection column read as a regular one.** A column read as a
token is the column; a provenance column is the value it holds; a term
over an aggregate column is the same term over that column read as a
regular one (`TermIn.atCol`). Only the rewritten world's column, which
carries an arbitrary function, has no counterpart, and is sent to a
constant – which is why the lemma below asks `sourceCol`. -/
def ProjColIn.toReg {c n : ℕ} {κ : Fin n → ColKind} :
    ProjColIn T c κ → ProjColIn T c (ColKind.allReg n)
  | .term t => .term t.toReg
  | .token k _ => .term (.index k rfl)
  | .aggTerm _ _ _ => .term (.const 0)
  | .aggTermOf k _ t => .term (t.atCol k rfl)
  | .provTerm t => .term t.toReg

/-- Every column it builds is regular. -/
@[simp] theorem ProjColIn.kind_toReg {c n : ℕ} {κ : Fin n → ColKind}
    (p : ProjColIn T c κ) : (p.toReg).kind = ColKind.reg := by
  cases p <;> rfl

/-- It reads what the column reads, where that has a regular
counterpart. -/
theorem ProjColIn.evalPlain_toReg {c n : ℕ} {κ : Fin n → ColKind}
    (p : ProjColIn T c κ) (hp : p.sourceCol = true) (u : Tuple T n)
    (γ : Fin c → T) : (p.toReg).evalPlain u γ = p.evalPlain u γ := by
  cases p with
  | term t => exact TermGIn.evalPlain_toReg t u γ
  | token k h => rfl
  | aggTerm k h gf => exact absurd hp (by simp [ProjColIn.sourceCol])
  | aggTermOf k h t => exact TermIn.evalPlain_atCol k rfl u γ t
  | provTerm t => exact TermGIn.evalPlain_toReg t u γ

/-! ## Reading a query's own columns as values

`Explode` reads one aggregate column as a key and `Retag` reads the
provenance columns as values, so regularizing a query's columns is a
recursion over them. Both are the identity over a plain relation, which
is what makes the whole thing invisible to `evaluatePlain`. -/

/-- The kind vector with the columns below `m` read as regular. -/
def regBelow {n : ℕ} (κ : Fin n → ColKind) (m : ℕ) : Fin n → ColKind :=
  fun k => if k.val < m then ColKind.reg else κ k

theorem regBelow_zero {n : ℕ} (κ : Fin n → ColKind) : regBelow κ 0 = κ := by
  funext k
  exact ite_eq_right (Nat.not_lt_zero k.val)

theorem regBelow_ge {n m : ℕ} (κ : Fin n → ColKind) (h : n ≤ m) :
    regBelow κ m = ColKind.allReg n := by
  funext k
  exact ite_eq_left (Nat.lt_of_lt_of_le k.isLt h)

theorem regBelow_succ_of_le {n : ℕ} (κ : Fin n → ColKind) {m : ℕ}
    (h : n ≤ m) : regBelow κ (m + 1) = regBelow κ m := by
  rw [regBelow_ge κ h, regBelow_ge κ (Nat.le_succ_of_le h)]

theorem regBelow_succ {n : ℕ} (κ : Fin n → ColKind) {m : ℕ} (h : m < n) :
    regBelow κ (m + 1)
      = Function.update (regBelow κ m) (⟨m, h⟩ : Fin n) ColKind.reg := by
  funext k
  by_cases hk : k = (⟨m, h⟩ : Fin n)
  · subst hk
    rw [Function.update_self]
    exact ite_eq_left (Nat.lt_succ_self m)
  · rw [Function.update_of_ne hk]
    show (if k.val < m + 1 then ColKind.reg else κ k)
      = if k.val < m then ColKind.reg else κ k
    by_cases hlt : k.val < m
    · rw [ite_eq_left (Nat.lt_succ_of_lt hlt), ite_eq_left hlt]
    · have hne : k.val ≠ m := fun hc => hk (Fin.ext hc)
      rw [ite_eq_right (fun hc => hlt (Nat.lt_of_le_of_ne
          (Nat.le_of_lt_succ hc) hne)), ite_eq_right hlt]

/-- **Every column below `m` read as a value.** -/
def AggQueryIn.explodeBelow {c n : ℕ} :
    (m : ℕ) → {κ : Fin n → ColKind} → {l : List (String × ℕ)} → AggQueryIn T c n κ l →
      AggQueryIn T c n (regBelow κ m) l
  | 0, κ, _, q => q.castKind (regBelow_zero κ).symm
  | m + 1, κ, _, q =>
    if h : m < n then
      match hk : regBelow κ m (⟨m, h⟩ : Fin n) with
      | ColKind.agg =>
          (AggQueryIn.Explode (⟨m, h⟩ : Fin n) hk
            (AggQueryIn.explodeBelow m q)).castKind (regBelow_succ κ h).symm
      | ColKind.reg =>
          (AggQueryIn.explodeBelow m q).castKind (by
            rw [regBelow_succ κ h]
            exact (Function.update_eq_self_iff.mpr hk.symm).symm)
      | ColKind.prov =>
          (AggQueryIn.Retag (κ' := regBelow κ (m + 1)) (fun i => by
            rw [regBelow_succ κ h]
            by_cases hi : i = (⟨m, h⟩ : Fin n)
            · subst hi
              rw [Function.update_self, hk]
              rfl
            · rw [Function.update_of_ne hi])
            (AggQueryIn.explodeBelow m q))
    else
      (AggQueryIn.explodeBelow m q).castKind
        (regBelow_succ_of_le κ (Nat.le_of_not_lt h)).symm

/-- **A query with every column read as a value.** -/
def AggQueryIn.allRegOf {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)}
    (q : AggQueryIn T c n κ l) : AggQueryIn T c n (ColKind.allReg n) l :=
  (q.explodeBelow n).castKind (regBelow_ge κ le_rfl)

omit [ValueType T] in
/-- Reading the columns as values changes no operator. -/
@[simp] theorem AggQueryIn.usesOnly_explodeBelow {c n : ℕ} {S : Set OpKind} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (q.explodeBelow m).usesOnly S ↔ q.usesOnly S := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show ((q.castKind _).usesOnly S) ↔ _
    rw [AggQueryIn.usesOnly_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.explodeBelow
    split
    · split
      · rw [AggQueryIn.usesOnly_castKind]
        show (AggQueryIn.Explode _ _ (q.explodeBelow m)).usesOnly S ↔ _
        rw [AggQueryIn.usesOnly]
        exact ih q
      · rw [AggQueryIn.usesOnly_castKind]
        exact ih q
      · show (AggQueryIn.Retag _ (q.explodeBelow m)).usesOnly S ↔ _
        rw [AggQueryIn.usesOnly]
        exact ih q
    · rw [AggQueryIn.usesOnly_castKind]
      exact ih q

omit [ValueType T] in
/-- Nor which relations it names. -/
@[simp] theorem AggQueryIn.overSchema_explodeBelow {c n : ℕ} {sch : Schema} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (q.explodeBelow m).overSchema sch ↔ q.overSchema sch := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show ((q.castKind _).overSchema sch) ↔ _
    rw [AggQueryIn.overSchema_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.explodeBelow
    split
    · split
      · rw [AggQueryIn.overSchema_castKind]
        show (AggQueryIn.Explode _ _ (q.explodeBelow m)).overSchema sch ↔ _
        rw [AggQueryIn.overSchema]
        exact ih q
      · rw [AggQueryIn.overSchema_castKind]
        exact ih q
      · show (AggQueryIn.Retag _ (q.explodeBelow m)).overSchema sch ↔ _
        rw [AggQueryIn.overSchema]
        exact ih q
    · rw [AggQueryIn.overSchema_castKind]
      exact ih q

/-- **And it is invisible to the plain semantics**: both readings are the
identity there. -/
@[simp] theorem AggQueryIn.evaluatePlain_explodeBelow {c n : ℕ} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l)
      (D : Database T) (γ : Fin c → T),
      (q.explodeBelow m).evaluatePlain D γ = q.evaluatePlain D γ := by
  intro m
  induction m with
  | zero =>
    intro κ l q D γ
    show (q.castKind _).evaluatePlain D γ = _
    rw [AggQueryIn.evaluatePlain_castKind]
  | succ m ih =>
    intro κ l q D γ
    unfold AggQueryIn.explodeBelow
    split
    · split
      · rw [AggQueryIn.evaluatePlain_castKind]
        show (AggQueryIn.Explode _ _ (q.explodeBelow m)).evaluatePlain D γ = _
        rw [AggQueryIn.evaluatePlain]
        exact ih q D γ
      · rw [AggQueryIn.evaluatePlain_castKind]
        exact ih q D γ
      · show (AggQueryIn.Retag _ (q.explodeBelow m)).evaluatePlain D γ = _
        rw [AggQueryIn.evaluatePlain]
        exact ih q D γ
    · rw [AggQueryIn.evaluatePlain_castKind]
      exact ih q D γ

omit [ValueType T] in
@[simp] theorem AggQueryIn.usesOnly_allRegOf {c n : ℕ} {S : Set OpKind}
    {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) :
    (q.allRegOf).usesOnly S ↔ q.usesOnly S := by
  rw [AggQueryIn.allRegOf, AggQueryIn.usesOnly_castKind,
    AggQueryIn.usesOnly_explodeBelow]

omit [ValueType T] in
@[simp] theorem AggQueryIn.overSchema_allRegOf {c n : ℕ} {sch : Schema}
    {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) :
    (q.allRegOf).overSchema sch ↔ q.overSchema sch := by
  rw [AggQueryIn.allRegOf, AggQueryIn.overSchema_castKind,
    AggQueryIn.overSchema_explodeBelow]

@[simp] theorem AggQueryIn.evaluatePlain_allRegOf {c n : ℕ}
    {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) (D : Database T)
    (γ : Fin c → T) : (q.allRegOf).evaluatePlain D γ = q.evaluatePlain D γ := by
  rw [AggQueryIn.allRegOf, AggQueryIn.evaluatePlain_castKind,
    AggQueryIn.evaluatePlain_explodeBelow]

/-! ## The one reading with no regular counterpart -/

/-- **What a query has to be for its columns to be readable as values.**
Two things, and both are real.

No projection column may post-compose an aggregate column
(`ProjColIn.aggTerm`): its value is `gf` of the column, and the term
language applies no arbitrary `gf`.

And every window either reads an all-regular input or is
**determinate** on every instance, with no `FILTER` clause. A window is
the one operator whose *plain* semantics reads the kind vector: it reads
its input through `ColKind.readTuple`, which nulls the aggregate
columns, so a window over a re-typed input reads values where the
original read `0`. Both are listings the clause allows, and they differ
only inside a block of peers – an aggregate column read as a value
enters the tie-break and nothing else. Determinacy is exactly the
condition under which that cannot be seen, and it is the document's own
condition on an aggregation: the aggregate reads its frame as a bag, or
the term it aggregates is constant on the rows the clause leaves tied
(`Relation.rowsAgree` of `Provenance.Determinacy`, read on the rows the
window reads, `AggQueryIn.readRows`). Since it is a condition on the
rows, it is quantified over the instance here, in the manner of
`AggQueryIn.recSettles`;
`ValueFrame.windowValue_readTuple_of_det` is what it buys, and
`ValueFrame.windowValue_readTuple` the symmetric case of the same thing.
A query the condition refuses does tell the two readings apart: over the
rows `(2,5)`, `(2,6)`, `(1,7)` whose first column is an aggregate one,
with no `ORDER BY`, so that all three are peers, `first_value` of the
second column reads `5` before the re-typing and `7` after. A `FILTER`
clause is no longer excluded but asked to read the occurrence's regular
columns, which is what `sec:agg` says a clause does: its truth is then
unchanged by the nulling, so it keeps the same rows on both sides. -/
def AggQueryIn.Retypable : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.Retypable
  | _, _, _, _, .Sel _ q _ => q.Retypable
  | _, _, _, _, .Prod q₁ q₂ => q₁.Retypable ∧ q₂.Retypable
  | _, _, _, _, .Apply q₁ q₂ => q₁.Retypable ∧ q₂.Retypable
  | _, _, _, _, .Sum q₁ q₂ => q₁.Retypable ∧ q₂.Retypable
  | _, _, _, _, .Dedup q => q.Retypable
  | _, _, _, _, .Diff q₁ q₂ => q₁.Retypable ∧ q₂.Retypable
  | _, _, _, _, .Explode _ _ q => q.Retypable
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.Retypable ∧ q₁.Retypable
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.Retypable ∧ q₁.Retypable
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.Retypable
  | _, _, _, _, .GammaScalar _ _ q _ => q.Retypable
  | _, _, _, _, .GammaNest _ _ _ _ q => q.Retypable
  | _, _, _, _, .ProvSum _ _ _ q => q.Retypable
  | _, _, _, _, .Retag _ q => q.Retypable
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.Retypable
  | c, _, _, _, @AggQueryIn.Win _ _ n _ _ κ' _lab _rd _ O o _ _ t fn q _ dist keep =>
      ((∀ i, κ' i = ColKind.reg)
          ∨ ((∀ (D : Database T) (γ : Fin c → T),
                (if dist then fn.distinct else fn).Symmetric
                  ∨ Relation.rowsAgree (q.readRows D γ)
                      (fun y z => o.peer (Tuple.key O y) (Tuple.key O z))
                      (fun y => t.eval y γ))
              ∧ ∀ y : Tuple T n,
                  Selection.keepsOpt keep (ColKind.readTuple κ' y)
                    = Selection.keepsOpt keep y))
        ∧ q.Retypable
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.Retypable

/-- **A window-free query is re-typable.** The window is the only thing
`AggQueryIn.Retypable` asks about, every column of the source language
re-typing on its own (a column reading an aggregate column reads it
through a term, `ProjColIn.aggTermOf`, and `AggQueryIn.usesOnly` refuses
the rewritten world's arbitrary function). So a query whose classes
exclude the window is re-typable outright – which is the case the three
passes of `Provenance.BasisAssembly` are in, the first of them replacing
every window by an apply of a scalar aggregation. -/
theorem AggQueryIn.retypable_of_usesOnly {S : Set OpKind}
    (hw : OpKind.win ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.Retypable := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ => trivial
  | Hole n s => exact fun _ => trivial
  | Param pv ρ => exact fun _ => trivial
  | Empty => exact fun _ => trivial
  | Proj ps q ih => exact fun hq => ih hq.2
  | Sel φ q _ ih => exact fun hq => ih hq.2
  | Prod q₁ q₂ ih₁ ih₂ =>
    exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Apply q₁ q₂ ih₁ ih₂ =>
    exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Sum q₁ q₂ ih₁ ih₂ =>
    exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Dedup q ih => exact fun hq => ih hq.2
  | Diff q₁ q₂ ih₁ ih₂ =>
    exact fun hq => ⟨ih₁ hq.2.1, ih₂ hq.2.2⟩
  | Explode k h q ih => exact fun hq => ih hq
  | Retag h q ih => exact fun hq => ih hq
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.2.1, ih₁ hq.2.2⟩
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => ⟨ih₀ hq.2.1, ih₁ hq.2.2⟩
  | Gamma is ts fs q keep ord ih => exact fun hq => ih hq.2
  | GammaScalar ts fs q ord ih => exact fun hq => ih hq.2
  | GammaNest is his pc f q ih => exact fun hq => ih hq.2
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P O o w t f q hrr dist keep ih => exact fun hq => absurd hq.1 hw
  | WinExpr P O o ws ts fs g q keeps ih => exact fun hq => absurd hq.1 hw

/-- **What the swaps of `sec:basis` ask of a query**: the input of every
selection has regular columns and its predicate has no aggregate atom
(so that the selection can become a difference, which takes regular
columns), and the left factor of every product has regular columns (so
that the product can become an apply, whose left side takes them). It is
what `AggQueryIn.exists_allReg` leaves behind. -/
def AggQueryIn.SwapReady : {c n : ℕ} → {κ : Fin n → ColKind} → {l : List (String × ℕ)} →
    AggQueryIn T c n κ l → Prop
  | _, _, _, _, .Rel _ _ => True
  | _, _, _, _, .Hole _ _ _ => True
  | _, _, _, _, .Param _ _ => True
  | _, _, _, _, .Empty => True
  | _, _, _, _, .Proj _ q => q.SwapReady
  | _, _, κ, _, .Sel φ q _ =>
      (∀ i, κ i = ColKind.reg) ∧ φ.hasAggAtom = false ∧ q.SwapReady
  | _, _, _, _, @AggQueryIn.Prod _ _ _ _ κ₁ _ _ _ q₁ q₂ =>
      (∀ i, κ₁ i = ColKind.reg) ∧ q₁.SwapReady ∧ q₂.SwapReady
  | _, _, _, _, .Apply q₁ q₂ => q₁.SwapReady ∧ q₂.SwapReady
  | _, _, _, _, .Sum q₁ q₂ => q₁.SwapReady ∧ q₂.SwapReady
  | _, _, _, _, .Dedup q => q.SwapReady
  | _, _, _, _, .Diff q₁ q₂ => q₁.SwapReady ∧ q₂.SwapReady
  | _, _, _, _, .Explode _ _ q => q.SwapReady
  | _, _, _, _, .Mu _ q₀ q₁ => q₀.SwapReady ∧ q₁.SwapReady
  | _, _, _, _, .MuSet _ q₀ q₁ => q₀.SwapReady ∧ q₁.SwapReady
  | _, _, _, _, .Gamma _ _ _ q _ _ => q.SwapReady
  | _, _, _, _, .GammaScalar _ _ q _ => q.SwapReady
  | _, _, _, _, .GammaNest _ _ _ _ q => q.SwapReady
  | _, _, _, _, .ProvSum _ _ _ q => q.SwapReady
  | _, _, _, _, .Retag _ q => q.SwapReady
  | _, _, _, _, .GammaTok _ _ _ _ _ q _ => q.SwapReady
  | _, _, _, _, .Win _ _ _ _ _ _ q _ _ _ => q.SwapReady
  | _, _, _, _, .WinExpr _ _ _ _ _ _ _ q _ => q.SwapReady

omit [ValueType T] in
/-- **The difference a selection becomes is ready for the product swap**
wherever its input is: it projects, tags and takes differences, and
introduces no product and no selection of its own. This is what lets the
two swaps be composed, so that the basis with `−` for `σ` *and* the
apply for `×` is reached. -/
theorem AggQueryIn.swapReady_selByDiff {k : ℕ} (yes : T)
    (t : TermGIn T 0 (ColKind.allReg k)) {q : AggQuery T k (ColKind.allReg k)}
    (hq : q.SwapReady) : (AggQueryIn.selByDiff yes t q).SwapReady :=
  ⟨hq, hq, hq⟩

omit [ValueType T] in
@[simp] theorem AggQueryIn.swapReady_castKind {c n : ℕ}
    {κ κ' : Fin n → ColKind} {l : List (String × ℕ)} (h : κ = κ') (q : AggQueryIn T c n κ l) :
    (q.castKind h).SwapReady ↔ q.SwapReady := by
  cases h
  exact Iff.rfl

omit [ValueType T] in
@[simp] theorem AggQueryIn.swapReady_explodeBelow {c n : ℕ} :
    ∀ (m : ℕ) {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      (q.explodeBelow m).SwapReady ↔ q.SwapReady := by
  intro m
  induction m with
  | zero =>
    intro κ l q
    show ((q.castKind _).SwapReady) ↔ _
    rw [AggQueryIn.swapReady_castKind]
  | succ m ih =>
    intro κ l q
    unfold AggQueryIn.explodeBelow
    split
    · split
      · rw [AggQueryIn.swapReady_castKind]
        show (AggQueryIn.Explode _ _ (q.explodeBelow m)).SwapReady ↔ _
        rw [AggQueryIn.SwapReady]
        exact ih q
      · rw [AggQueryIn.swapReady_castKind]
        exact ih q
      · show (AggQueryIn.Retag _ (q.explodeBelow m)).SwapReady ↔ _
        rw [AggQueryIn.SwapReady]
        exact ih q
    · rw [AggQueryIn.swapReady_castKind]
      exact ih q

omit [ValueType T] in
@[simp] theorem AggQueryIn.swapReady_allRegOf {c n : ℕ}
    {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l) :
    (q.allRegOf).SwapReady ↔ q.SwapReady := by
  rw [AggQueryIn.allRegOf, AggQueryIn.swapReady_castKind,
    AggQueryIn.swapReady_explodeBelow]

/-! ## A window over columns it does not read

A window reads the regular columns of its input and carries the
aggregate ones through: `ColKind.readTuple` nulls an aggregate column
before the partition, the frame, the order and the term see the row. It
is one listing of the frame among those the clause allows, which is all
the semantics asks for, an aggregation being admitted only where its
value does not depend on the listing.

That is why re-typing is not free here: reading an aggregate column as a
value puts it into the tie-break, which can reorder rows the clause
leaves tied, and an order-dependent aggregate reads the reordered
sequence. Where the aggregate reads its frame as a bag the reordering is
immaterial, and this section proves that much. -/

omit [ValueType T] in
/-- Which decision procedure an erasure uses does not matter. -/
private theorem erase_instEq {α : Type} (i j : DecidableEq α) (s : Multiset α)
    (a : α) : @Multiset.erase α i s a = @Multiset.erase α j s a := by
  rw [Subsingleton.elim i j]

/-- **The frame of the nulled relation is the nulled frame.** The frame
condition reads the partition and order keys, which the nulling leaves
alone, so the rows it holds are the same ones; and a row agreeing with
the current row on every regular column has its order key, hence is in
the frame exactly when the current row is, so the occurrence a frame
excluding its current row takes out is taken out on both sides. -/
theorem ValueFrame.frameOf_readTuple {n m p : ℕ} {κ : Fin n → ColKind}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (w : ValueFrame T p)
    (hP : ∀ k, (κ (P k)).base = ColKind.reg)
    (hO : ∀ k, (κ (O k)).base = ColKind.reg)
    (R : Multiset (Tuple T n)) {u : Tuple T n} (hu : u ∈ R) :
    ValueFrame.frameOf (α := Tuple T n) id P O w
        (R.map (ColKind.readTuple κ)) (ColKind.readTuple κ u)
      = (ValueFrame.frameOf (α := Tuple T n) id P O w R u).map
          (ColKind.readTuple κ) := by
  have hkP : ∀ y : Tuple T n,
      Tuple.key P (ColKind.readTuple κ y) = Tuple.key P y :=
    fun y => Tuple.key_readTuple P hP y
  have hkO : ∀ y : Tuple T n,
      Tuple.key O (ColKind.readTuple κ y) = Tuple.key O y :=
    fun y => Tuple.key_readTuple O hO y
  set m' : Tuple T n → Tuple T n := ColKind.readTuple κ with hm'
  set cond : Tuple T n → Prop := fun y =>
    Tuple.key P y = Tuple.key P u
      ∧ w.ρ (Tuple.key O y) (Tuple.key O u) = true with hcond
  -- the rows the condition keeps are the nulled images of those it keeps
  have hfil : Multiset.filter (fun y : Tuple T n =>
        Tuple.key P y = Tuple.key P (m' u)
          ∧ w.ρ (Tuple.key O y) (Tuple.key O (m' u)) = true) (R.map m')
      = (Multiset.filter cond R).map m' := by
    rw [hm', hkP u, hkO u, Multiset.filter_map]
    refine congrArg _ (Multiset.filter_congr (fun y _ => ?_))
    simp only [Function.comp_apply, hcond, Tuple.key_readTuple P hP,
      Tuple.key_readTuple O hO]
  -- and the occurrence a frame excluding its current row takes out is the
  -- same one on both sides
  have herase : @Multiset.erase (Tuple T n)
        (fun a b => LinearOrder.toDecidableEq a b)
        ((Multiset.filter cond R).map m') (m' u)
      = (@Multiset.erase (Tuple T n)
          (fun a b => LinearOrder.toDecidableEq a b)
          (Multiset.filter cond R) u).map m' := by
    rw [erase_instEq (α := Tuple T n) (fun a b => LinearOrder.toDecidableEq a b)
        (fun a b => instDecidableEqTuple a b),
      erase_instEq (α := Tuple T n) (fun a b => LinearOrder.toDecidableEq a b)
        (fun a b => instDecidableEqTuple a b)]
    by_cases hmem : u ∈ Multiset.filter cond R
    · exact (Multiset.map_erase_of_mem m' _ hmem).symm
    · have hnot : m' u ∉ (Multiset.filter cond R).map m' := by
        intro hc
        obtain ⟨v, hv, hveq⟩ := Multiset.mem_map.mp hc
        obtain ⟨-, hvρ⟩ := (Multiset.mem_filter.mp hv).2
        have hkey : Tuple.key O v = Tuple.key O u := by
          rw [← hkO v, ← hkO u, hm']
          exact congrArg (Tuple.key O) hveq
        exact hmem (Multiset.mem_filter.mpr ⟨hu, rfl, hkey ▸ hvρ⟩)
      rw [Multiset.erase_of_notMem hnot, Multiset.erase_of_notMem hmem]
  unfold ValueFrame.frameOf
  simp only [id_eq]
  rw [hfil, herase, hm', hkO u]
  by_cases hs : w.s (Tuple.key O u) = true
  · rw [ite_eq_left hs, ite_eq_left hs, Multiset.map_cons]
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- **A symmetric window reads the same value before and after the
nulling.** The frame holds the same rows either way
(`ValueFrame.frameOf_readTuple`), and the term reads the same value at
each of them (`TermIn.eval_readTuple`), so the two sequences the
aggregate is applied to are permutations of one another – and a
symmetric aggregate does not tell them apart. -/
theorem ValueFrame.windowValue_readTuple {c n m p : ℕ} {κ : Fin n → ColKind}
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p)
    (w : ValueFrame T p) (t : TermIn T c n) {f : SeqAggFunc T}
    (hf : f.Symmetric) (hrr : WinReadsReg κ P O t)
    (R : Multiset (Tuple T n)) {u : Tuple T n} (hu : u ∈ R) (γ : Fin c → T) :
    ValueFrame.windowValue P O o w t f (R.map (ColKind.readTuple κ))
        (ColKind.readTuple κ u) γ
      = ValueFrame.windowValue P O o w t f R u γ := by
  obtain ⟨hP, hO, hreg⟩ := hrr
  refine hf (Multiset.coe_eq_coe.mp ?_)
  rw [← Multiset.map_coe, ← Multiset.map_coe, ValueFrame.frameListOf_coe,
    ValueFrame.frameListOf_coe, ValueFrame.frameOf_readTuple P O w hP hO R hu,
    Multiset.map_map]
  refine Multiset.map_congr rfl (fun v _ => ?_)
  exact TermIn.eval_readTuple t hreg v γ

/-- **A determinate window reads the same value before and after the
nulling**, symmetric or not, and with a `FILTER` clause or without: the
two listings of the frame are sorted by the clause's keys and differ
only inside a block of peers, where the term does not look
(`OrderSpec.map_eq_of_keySorted`), and a clause that reads the
occurrence's regular columns keeps the same rows on both sides. The
hypothesis is the document's own condition on an aggregation – the
aggregate reads its frame as a bag, or the term it aggregates is
constant on the rows the clause leaves tied. -/
theorem ValueFrame.windowValueOpt_readTuple_of_det {c : ℕ}
    {κ : Fin n → ColKind} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n)
    {f : SeqAggFunc T} (keep : Option (Selection T n))
    (hrr : WinReadsReg κ P O t)
    (hkeep : ∀ y : Tuple T n,
      Selection.keepsOpt keep (ColKind.readTuple κ y)
        = Selection.keepsOpt keep y)
    (R : Multiset (Tuple T n)) {u : Tuple T n} (hu : u ∈ R) (γ : Fin c → T)
    (hsym : f.Symmetric
      ∨ Relation.rowsAgree (R.map (ColKind.readTuple κ))
          (fun y z => o.peer (Tuple.key O y) (Tuple.key O z))
          (fun y => t.eval y γ)) :
    ValueFrame.windowValueOpt P O o w t f keep (R.map (ColKind.readTuple κ))
        (ColKind.readTuple κ u) γ
      = ValueFrame.windowValueOpt P O o w t f keep R u γ := by
  obtain ⟨hP, hO, hreg⟩ := hrr
  set A : List (Tuple T n) :=
    ValueFrame.frameListOf (α := Tuple T n) id P O o w R u with hA
  set B : List (Tuple T n) :=
    ValueFrame.frameListOf (α := Tuple T n) id P O o w
      (R.map (ColKind.readTuple κ)) (ColKind.readTuple κ u) with hB
  -- the term reads the same value before and after the nulling
  have hAmap : A.map (fun v => t.eval v γ)
      = (A.map (ColKind.readTuple κ)).map (fun v => t.eval v γ) := by
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => (TermIn.eval_readTuple t hreg v γ).symm)
  -- and the two listings are listings of one bag, sorted by the clause's keys
  have hperm : B.Perm (A.map (ColKind.readTuple κ)) := by
    refine Multiset.coe_eq_coe.mp ?_
    rw [hB, ValueFrame.frameListOf_coe, ← Multiset.map_coe, hA,
      ValueFrame.frameListOf_coe,
      ValueFrame.frameOf_readTuple P O w hP hO R hu]
  have hkeyB : B.Pairwise (fun y z : Tuple T n =>
      o.le (Tuple.key O y) (Tuple.key O z) = true) := by
    rw [hB]
    exact (OrderSpec.sortSeq_sorted _).imp (fun {x y} h =>
      OrderSpec.le_of_readLe (val := (id : Tuple T n → Tuple T n)) h)
  have hkeyA : (A.map (ColKind.readTuple κ)).Pairwise (fun y z : Tuple T n =>
      o.le (Tuple.key O y) (Tuple.key O z) = true) := by
    rw [List.pairwise_map, hA]
    refine (OrderSpec.sortSeq_sorted _).imp (fun {x y} h => ?_)
    rw [Tuple.key_readTuple O hO, Tuple.key_readTuple O hO]
    exact OrderSpec.le_of_readLe (val := (id : Tuple T n → Tuple T n)) h
  have hmemB : ∀ y ∈ B, y ∈ R.map (ColKind.readTuple κ) := by
    intro y hy
    rw [hB] at hy
    exact ValueFrame.mem_of_mem_frameOf (α := Tuple T n) id P O w
      (R.map (ColKind.readTuple κ)) (Multiset.mem_map_of_mem _ hu)
      (show y ∈ ValueFrame.frameOf (α := Tuple T n) id P O w
          (R.map (ColKind.readTuple κ)) (ColKind.readTuple κ u) from by
        rw [← ValueFrame.frameListOf_coe (α := Tuple T n) id P O o w]
        exact Multiset.mem_coe.mpr hy)
  cases keep with
  | none =>
    rw [ValueFrame.windowValueOpt_none, ValueFrame.windowValueOpt_none]
    unfold ValueFrame.windowValue
    rw [← hB, ← hA, hAmap]
    rcases hsym with hs | hdet
    · exact hs (hperm.map _)
    · exact congrArg f (OrderSpec.map_eq_of_keySorted (Tuple.key O) o
        (fun v => t.eval v γ)
        (S := fun y => y ∈ R.map (ColKind.readTuple κ)) hdet B
        (A.map (ColKind.readTuple κ)) hmemB hperm hkeyB hkeyA)
  | some φ =>
    rw [ValueFrame.windowValueOpt_some, ValueFrame.windowValueOpt_some]
    unfold ValueFrame.windowValueWhen
    rw [← hB, ← hA]
    have hAfil : (A.filter φ.keeps).map (fun v => t.eval v γ)
        = ((A.map (ColKind.readTuple κ)).filter φ.keeps).map
            (fun v => t.eval v γ) := by
      rw [List.filter_map, show (φ.keeps ∘ ColKind.readTuple κ) = φ.keeps from
        funext (fun y => hkeep y), List.map_map]
      exact List.map_congr_left (fun v _ =>
        (TermIn.eval_readTuple t hreg v γ).symm)
    rw [hAfil]
    rcases hsym with hs | hdet
    · exact hs ((hperm.filter φ.keeps).map _)
    · exact congrArg f (OrderSpec.map_eq_of_keySorted (Tuple.key O) o
        (fun v => t.eval v γ)
        (S := fun y => y ∈ R.map (ColKind.readTuple κ)) hdet
        (B.filter φ.keeps) ((A.map (ColKind.readTuple κ)).filter φ.keeps)
        (fun y hy => hmemB y (List.mem_of_mem_filter hy))
        (hperm.filter φ.keeps) (hkeyB.sublist List.filter_sublist)
        (hkeyA.sublist List.filter_sublist))

/-! ## Every query is one whose columns are all values -/

/-- **The kind discipline costs nothing in the plain semantics**: every
query whose projections post-compose no aggregate column is
plain-equivalent to one all of whose columns are regular, using the same
operator classes and naming the same relations.

Each case rebuilds the operator over re-typed children and then reads
the columns it produces as values (`AggQueryIn.allRegOf`), which is the
identity there. `Explode` and `Retag` disappear: their children come back
already regular. -/
theorem AggQueryIn.exists_allReg {S : Set OpKind} {sch : Schema}
    (hmb : OpKind.muBag ∉ S) (hms : OpKind.muSet ∉ S) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.Retypable → q.overSchema sch →
      ∃ q' : AggQueryIn T c n (ColKind.allReg n) l,
        q'.usesOnly S ∧ q'.overSchema sch ∧ q'.SwapReady
          ∧ ∀ (D : Database T) (γ : Fin c → T),
            q.evaluatePlain D γ = q'.evaluatePlain D γ := by
  intro c n κ l q
  induction q with
  | Rel n s => exact fun _ _ hqs => ⟨AggQueryIn.Rel n s, trivial, hqs, trivial, fun _ _ => rfl⟩
  | Hole n s =>
    exact fun _ _ hqs => ⟨AggQueryIn.Hole n s _, trivial, hqs, trivial, fun _ _ => rfl⟩
  | Param pv ρ =>
    exact fun hq _ _ => ⟨AggQueryIn.Param pv (ColKind.allReg _), hq, trivial, trivial,
      fun _ _ => rfl⟩
  | Empty =>
    exact fun hq _ _ => ⟨AggQueryIn.Empty, hq, trivial, trivial,
      fun _ _ => rfl⟩
  | Proj ps q ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt hqs
    refine ⟨(AggQueryIn.Proj (fun j => (ps j).toReg) q').castKind
        (funext (fun j => ProjColIn.kind_toReg (ps j))), ?_, ?_, ?_,
      fun D γ => ?_⟩
    · rw [AggQueryIn.usesOnly_castKind]
      exact ⟨⟨hq.1.1, fun j => by
        rw [show ((ps j).toReg).sourceCol = true from by
          cases (ps j) <;> rfl]⟩, hu'⟩
    · rw [AggQueryIn.overSchema_castKind]
      exact hs'
    · rw [AggQueryIn.swapReady_castKind]
      exact hw'
    · rw [AggQueryIn.evaluatePlain_castKind]
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]
      refine Multiset.map_congr rfl (fun u _ => funext (fun j => ?_))
      exact (ProjColIn.evalPlain_toReg (ps j) (hq.1.2 j) u γ).symm
  | Sel φ q _ ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt hqs
    refine ⟨AggQueryIn.Sel φ.toReg q' (SelOK.of_noAggAtom (GenPredIn.hasAggAtom_toReg φ)),
      ⟨hq.1, hu'⟩, hs',
      ⟨fun i => rfl, GenPredIn.hasAggAtom_toReg φ, hw'⟩, fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
    exact Multiset.filter_congr (fun u _ =>
      (GenPredIn.holdsPlain_toReg φ u γ).symm)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hq hnt hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hq.2.1 hnt.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hq.2.2 hnt.2 hqs.2
    refine ⟨(AggQueryIn.Prod q₁' q₂').castKind (AggQueryIn.append_allReg _ _),
      ?_, ?_, ?_, fun D γ => ?_⟩
    · rw [AggQueryIn.usesOnly_castKind]
      exact ⟨hq.1, hu₁, hu₂⟩
    · rw [AggQueryIn.overSchema_castKind]
      exact ⟨hs₁, hs₂⟩
    · rw [AggQueryIn.swapReady_castKind]
      exact ⟨fun i => rfl, hw₁, hw₂⟩
    · rw [AggQueryIn.evaluatePlain_castKind]
      simp only [AggQueryIn.evaluatePlain]
      rw [he₁ D γ, he₂ D γ]
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hq hnt hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hq.2.1 hnt.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hq.2.2 hnt.2 hqs.2
    refine ⟨(AggQueryIn.Apply q₁' q₂').castKind (AggQueryIn.append_allReg _ _),
      ?_, ?_, ?_, fun D γ => ?_⟩
    · rw [AggQueryIn.usesOnly_castKind]
      exact ⟨hq.1, hu₁, hu₂⟩
    · rw [AggQueryIn.overSchema_castKind]
      exact ⟨hs₁, hs₂⟩
    · rw [AggQueryIn.swapReady_castKind]
      exact ⟨hw₁, hw₂⟩
    · rw [AggQueryIn.evaluatePlain_castKind]
      simp only [AggQueryIn.evaluatePlain]
      rw [he₁ D γ]
      exact Multiset.bind_congr (fun u _ =>
        congrArg (Multiset.map _) (he₂ D (Fin.append u γ)))
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hq hnt hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hq.2.1 hnt.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hq.2.2 hnt.2 hqs.2
    refine ⟨AggQueryIn.Sum q₁' q₂', ⟨hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, ⟨hw₁, hw₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ, he₂ D γ]
  | Dedup q ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt hqs
    refine ⟨AggQueryIn.Dedup q', ⟨hq.1, hu'⟩, hs', hw', fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he' D γ]
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hq hnt hqs
    obtain ⟨q₁', hu₁, hs₁, hw₁, he₁⟩ := ih₁ hq.2.1 hnt.1 hqs.1
    obtain ⟨q₂', hu₂, hs₂, hw₂, he₂⟩ := ih₂ hq.2.2 hnt.2 hqs.2
    refine ⟨AggQueryIn.Diff q₁' q₂', ⟨hq.1, hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, ⟨hw₁, hw₂⟩,
      fun D γ => ?_⟩
    simp only [AggQueryIn.evaluatePlain]
    rw [he₁ D γ]
    exact Multiset.filter_congr (fun t _ => by rw [he₂ D γ])
  | Explode i hi q ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq hnt hqs
    exact ⟨q', hu', hs', hw', fun D γ => he' D γ⟩
  | Retag hbase q ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq hnt hqs
    exact ⟨q', hu', hs', hw', fun D γ => he' D γ⟩
  | Mu s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hmb
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hq => absurd hq.1 hms
  | Gamma is ts fs q keep ord ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt hqs
    refine ⟨(AggQueryIn.Gamma (lab := 0) (rd := (fun _ => false)) is ts fs q' keep ord).allRegOf,
        ?_, ?_, ?_,
      fun D γ => ?_⟩
    · rw [AggQueryIn.usesOnly_allRegOf]
      exact ⟨hq.1, hu'⟩
    · rw [AggQueryIn.overSchema_allRegOf]
      exact hs'
    · rw [AggQueryIn.swapReady_allRegOf]
      exact hw'
    · rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]
  | GammaScalar ts fs q ord ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt hqs
    refine ⟨(AggQueryIn.GammaScalar (lab := 0) (rd := (fun _ => false)) ts fs q' ord).allRegOf, ?_,
        ?_, ?_,
      fun D γ => ?_⟩
    · rw [AggQueryIn.usesOnly_allRegOf]
      exact ⟨hq.1, hu'⟩
    · rw [AggQueryIn.overSchema_allRegOf]
      exact hs'
    · rw [AggQueryIn.swapReady_allRegOf]
      exact hw'
    · rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]
  | GammaNest is his pc fn q ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt hqs
    refine ⟨(AggQueryIn.GammaNest (lab := 0) (rd := (fun _ => false)) is (fun k hc =>
        ColKind.noConfusion hc)
      pc.toReg fn q').allRegOf, ?_, ?_, ?_, fun D γ => ?_⟩
    · rw [AggQueryIn.usesOnly_allRegOf]
      exact ⟨⟨hq.1.1, by rw [show (pc.toReg).sourceCol = true from by
        cases pc <;> rfl]⟩, hu'⟩
    · rw [AggQueryIn.overSchema_allRegOf]
      exact hs'
    · rw [AggQueryIn.swapReady_allRegOf]
      exact hw'
    · rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]
      refine Multiset.map_congr rfl (fun g _ => ?_)
      funext j
      refine Fin.addCases (fun k => ?_) (fun z => ?_) j
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        refine congrArg fn (Multiset.map_congr rfl (fun u _ => ?_))
        exact (ProjColIn.evalPlain_toReg pc hq.1.2 u γ).symm
  | GammaTok is his ts fs a q keep ih => exact fun hq => hq.elim
  | ProvSum is his t q ih => exact fun hq => hq.elim
  | Win P' O o w t fn q hrr dist keep ih =>
    intro hq hnt hqs
    obtain ⟨hwin, hnt'⟩ := hnt
    rcases hwin with hreg | ⟨hsym, hkeep⟩
    · obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt' hqs
      have hκ := funext hreg
      subst hκ
      refine ⟨(AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := (fun _ => false)) P' O o w t
          fn q'
          (winReadsReg_allReg P' O t) dist
        keep).allRegOf, ?_, ?_, ?_, fun D γ => ?_⟩
      · rw [AggQueryIn.usesOnly_allRegOf]
        exact ⟨hq.1, hu'⟩
      · rw [AggQueryIn.overSchema_allRegOf]
        exact hs'
      · rw [AggQueryIn.swapReady_allRegOf]
        exact hw'
      · rw [AggQueryIn.evaluatePlain_allRegOf]
        simp only [AggQueryIn.evaluatePlain]
        rw [he' D γ]
        rfl
    · obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt' hqs
      refine ⟨(AggQueryIn.Win (hsql := sql_frame%) (lab := 0) (rd := (fun _ => false)) P' O o w t
          fn q'
          (winReadsReg_allReg P' O t) dist
        keep).allRegOf, ?_, ?_, ?_, fun D γ => ?_⟩
      · rw [AggQueryIn.usesOnly_allRegOf]
        exact ⟨hq.1, hu'⟩
      · rw [AggQueryIn.overSchema_allRegOf]
        exact hs'
      · rw [AggQueryIn.swapReady_allRegOf]
        exact hw'
      · rw [AggQueryIn.evaluatePlain_allRegOf]
        simp only [AggQueryIn.evaluatePlain]
        rw [he' D γ]
        simp only [ColKind.readTuple_allReg, Multiset.map_id']
        refine Multiset.map_congr rfl (fun y hy => ?_)
        refine congrArg (Fin.snoc (α := fun _ => T) y) ?_
        refine ValueFrame.windowValueOpt_readTuple_of_det P' O o w t keep hrr
          hkeep _ hy γ ?_
        rcases hsym D γ with hs | hdet
        · exact Or.inl hs
        · refine Or.inr ?_
          rw [← he' D γ]
          exact hdet
  | WinExpr P' O o ws ts fs g q keeps ih =>
    intro hq hnt hqs
    obtain ⟨q', hu', hs', hw', he'⟩ := ih hq.2 hnt hqs
    refine ⟨(AggQueryIn.WinExpr (hsql := sql_frame%) (lab := 0) (rd := (fun _ => false)) P' O o ws
        ts fs g q'
        keeps).allRegOf, ?_, ?_,
      ?_, fun D γ => ?_⟩
    · rw [AggQueryIn.usesOnly_allRegOf]
      exact ⟨hq.1, hu'⟩
    · rw [AggQueryIn.overSchema_allRegOf]
      exact hs'
    · rw [AggQueryIn.swapReady_allRegOf]
      exact hw'
    · rw [AggQueryIn.evaluatePlain_allRegOf]
      simp only [AggQueryIn.evaluatePlain]
      rw [he' D γ]

