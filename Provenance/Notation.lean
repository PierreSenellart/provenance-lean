/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Mathlib.Tactic.FinCases
import Provenance.AggQuery

/-!
# Surface syntax for kind-indexed queries

Writing an `AggQuery` by hand is dominated by bookkeeping rather than by the
query: a column reference carries a proof that its column is regular, a
projection's kind vector is computed from its columns, and duplicate
elimination and difference demand a kind vector that is syntactically
all-regular. None of that is the query, and all of it has to be written out.

This module gives a bracketed surface syntax in which it is not. Inside
`RA[ … ]` the parser knows whether it is reading a term, a predicate or a
query, so the elaboration inserts the wrappers and discharges the kind
obligations:

```
RA[ ε (π[#3] (σ[#0 < #4 ∧ #3 = #7] (rel 4 "Personnel" × rel 4 "Personnel"))) ]
```

Three things follow from the syntax living in categories of its own rather
than in notation over terms.

* The connectives are unambiguous. `∧`, `∨`, `¬`, `<` and `=` are parsed in
  the predicate category, so they neither clash with their meanings on `Prop`
  nor have to be overloaded globally.
* The wrappers disappear. A comparison in a selection elaborates straight to
  a `GenPred` atom; nothing has to coerce a bare comparison into a predicate,
  which plain notation cannot do anyway, the column types being undetermined
  until the query around them is known.
* The kind obligations are discharged where they arise, by `rfl` on a
  concrete kind vector.

Column references are positional: `#i` is column `i`, counting from zero, of
the query the surrounding operator reads.
-/

namespace Provenance.Notation

/-- Terms over the columns of a query. -/
declare_syntax_cat raTerm
/-- Predicates over the columns of a query. -/
declare_syntax_cat raPred
/-- Queries. -/
declare_syntax_cat raQuery

/-! ### Terms -/

syntax:max "#" num : raTerm
syntax:max "(" raTerm ")" : raTerm
/-- A Lean term, as a constant of the query language. -/
syntax:max "`(" term ")" : raTerm
syntax:65 raTerm " + " raTerm : raTerm
syntax:65 raTerm " - " raTerm : raTerm
syntax:70 raTerm " * " raTerm : raTerm

/-! ### Predicates -/

syntax:50 raTerm " = " raTerm : raPred
syntax:50 raTerm " ≠ " raTerm : raPred
syntax:50 raTerm " < " raTerm : raPred
syntax:50 raTerm " ≤ " raTerm : raPred
syntax:50 raTerm " > " raTerm : raPred
syntax:50 raTerm " ≥ " raTerm : raPred
syntax:max "(" raPred ")" : raPred
syntax:max "¬" raPred : raPred
syntax:35 raPred " ∧ " raPred : raPred
syntax:30 raPred " ∨ " raPred : raPred

/-! ### Columns and aggregated columns

Grouping reads two lists that are not terms: the key *columns*, which are
indices, and the aggregated columns, each a term paired with the aggregate
applied to it. -/

/-- A column of the query being read. -/
declare_syntax_cat raCol
syntax:max "#" num : raCol

/-- One output column of a projection: a term, or a bare column reference
carried through whatever its kind. -/
declare_syntax_cat raProj
syntax raTerm : raProj

/-- One aggregated column: a term and the aggregate applied to it. The
aggregate is an ordinary Lean term of type `SeqAggFunc`, so the catalog is
open – `SeqAggFunc.sum`, `SeqAggFunc.sum`, and anything else of that type. -/
declare_syntax_cat raAgg
syntax raTerm " : " term : raAgg

/-! ### Queries -/

syntax:max "(" raQuery ")" : raQuery
syntax:max "rel " num str : raQuery
/-- A query already written in Lean. -/
syntax:max "`(" term ")" : raQuery
syntax:80 "π[" raProj,* "] " raQuery : raQuery
syntax:80 "σ[" raPred "] " raQuery : raQuery
syntax:80 "ε " raQuery : raQuery
/-- Grouping. With no keys before the `;` this is aggregation *without*
grouping, whose single row exists even over an empty input – the absence of
a `GROUP BY` is what makes an aggregation scalar, here as in SQL. -/
syntax:80 "γ[" raCol,* " ; " raAgg,* "] " raQuery : raQuery
/-- A window. Before the aggregated column come the partition columns, the
order columns, the `ORDER BY` clause and the frame: `⊞[#0 ; #1 ; o ; w ; #2 : f] q`
gives every row of `q` a further column holding `f` of `#2` over that row's
frame, which is `w` read on the order column `#1` within the partition given
by `#0`, and read in the order `o` gives that column. The clause is a term
of type `OrderSpec` (`OrderSpec.asc`, `OrderSpec.desc`, or a column-by-column
`OrderCol`), and the frame a term of type `ValueFrame`, so both catalogs are
open – `ValueFrame.whole`, `upTo`, `before`, `rangeUpTo o`, `peerGroup o`
and the `EXCLUDE` modifiers of any of them. -/
syntax:80 "⊞[" raCol,* " ; " raCol,* " ; " term " ; " term " ; " raAgg "] " raQuery : raQuery
syntax:70 raQuery " × " raQuery : raQuery
syntax:60 raQuery " ⊎ " raQuery : raQuery
syntax:60 raQuery " ∖ " raQuery : raQuery

/-- Bracket around a query of the surface syntax. -/
syntax "RA[" raQuery "]" : term

/-- The same, naming the value type. Only a base relation leaves the value
type undetermined – every other operator takes it from its argument – so this
is what a query written from the ground up needs, in place of an ascription. -/
syntax "RA[" term " | " raQuery "]" : term

/-! ### Elaboration

Each category expands through an internal marker in the term category, which
is what lets a rule recurse into its own sub-syntax. Column references become
`TermGIn.index` with the regularity proof discharged by `rfl`, which is what a
concrete kind vector makes available. -/

/-- A query all of whose columns are regular. This is the shape of a source
query before any grouping, and the one an ascription on a base relation
needs: the arity determines the kind vector, so naming it again is noise. -/
abbrev RegQuery (T : Type) (n : ℕ) := AggQuery T n (ColKind.allReg n)

/-- Retag a query whose kind vector is all-regular by computation into the
`ColKind.allReg` form that `Dedup` and `Diff` ask for. The obligation is
discharged by the tactic on a concrete kind vector, which is what the surface
syntax always produces. -/
def allReg {T : Type} {n : ℕ} {κ : Fin n → ColKind}
    (q : AggQuery T n κ)
    (h : κ = ColKind.allReg n := by first | rfl | (funext j; fin_cases j <;> rfl)) :
    AggQuery T n (ColKind.allReg n) :=
  q.castKind h

scoped syntax:max "ra_term% " raTerm : term
scoped syntax:max "ra_cterm% " raTerm : term
scoped syntax:max "ra_proj% " raProj : term
scoped syntax:max "ra_pred% " raPred : term
scoped syntax:max "ra_query% " raQuery : term

macro_rules
  | `(ra_term% #$i:num)     => `(TermGIn.index $i (by rfl))
  | `(ra_term% ($t:raTerm)) => `(ra_term% $t)
  | `(ra_term% `($t:term))  => `(TermGIn.const $t)
  | `(ra_term% $a:raTerm + $b:raTerm)     => `(TermGIn.add (ra_term% $a) (ra_term% $b))
  | `(ra_term% $a:raTerm - $b:raTerm)     => `(TermGIn.sub (ra_term% $a) (ra_term% $b))
  | `(ra_term% $a:raTerm * $b:raTerm)     => `(TermGIn.mul (ra_term% $a) (ra_term% $b))

/-- The same term syntax, read into the classical `Term`: what a grouping
aggregates is a term over the columns of its all-regular input, which carries
no kinds and so needs no regularity proof. One surface category, two
readings. -/
macro_rules
  | `(ra_cterm% #$i:num)     => `(TermIn.index $i)
  | `(ra_cterm% ($t:raTerm)) => `(ra_cterm% $t)
  | `(ra_cterm% `($t:term))  => `(TermIn.const $t)
  | `(ra_cterm% $a:raTerm + $b:raTerm) => `(TermIn.add (ra_cterm% $a) (ra_cterm% $b))
  | `(ra_cterm% $a:raTerm - $b:raTerm) => `(TermIn.sub (ra_cterm% $a) (ra_cterm% $b))
  | `(ra_cterm% $a:raTerm * $b:raTerm) => `(TermIn.mul (ra_cterm% $a) (ra_cterm% $b))

/-! ### Reading a column

A column reference says which column, not what is in it. Which atom, or which
projection column, that becomes is settled by the kind vector, and the kind
vector is concrete on any query one can write – so the two functions below
decide it by computation. The surface syntax therefore does not change with
the kinds: a comparison against a grouped aggregate is written like any other
comparison, as it is in SQL. -/

/-- The atom comparing column `k` against a term, whichever kind the column
has: a regular comparison on a value column, an aggregate atom on a token
column. -/
def atomAt {T : Type} {n : ℕ} {κ : Fin n → ColKind} (k : Fin n) (op : CompOp)
    (t : TermG T κ) : GenPred T κ :=
  match h : κ k with
  | ColKind.reg  => GenPredIn.cmp op (TermGIn.index k h) t
  | ColKind.agg  => GenPredIn.aggCmp k h op t
  | ColKind.prov => GenPredIn.cmp op (TermGIn.provIndex k h) t

/-- The projection column carrying column `k` through, whichever kind it
has. -/
def projAt {T : Type} {n : ℕ} {κ : Fin n → ColKind} (k : Fin n) : ProjCol T κ :=
  match h : κ k with
  | ColKind.reg  => ProjColIn.term (TermGIn.index k h)
  | ColKind.agg  => ProjColIn.token k h
  | ColKind.prov => ProjColIn.provTerm (TermGIn.provIndex k h)

/-- A bare column reference, if that is what the term is. -/
private def asCol : Lean.TSyntax `raTerm → Option (Lean.TSyntax `num)
  | `(raTerm| #$i:num) => some i
  | _ => none

/-- Build a comparison, reading a bare column reference on either side
through `atomAt`. The converse operator is used for the flipped case, so that
`t ≤ #i` is the atom `#i ≥ t`. -/
private def mkCmp (op conv : Lean.TSyntax `term) (a b : Lean.TSyntax `raTerm) :
    Lean.MacroM (Lean.TSyntax `term) := do
  if let some i := asCol a then `($(Lean.mkIdent ``atomAt) $i $op (ra_term% $b))
  else if let some j := asCol b then `($(Lean.mkIdent ``atomAt) $j $conv (ra_term% $a))
  else `(GenPredIn.cmp $op (ra_term% $a) (ra_term% $b))

/-- A projection column: a bare column reference is carried through by
`projAt`, anything else is a term. -/
private def mkProj (t : Lean.TSyntax `raTerm) : Lean.MacroM (Lean.TSyntax `term) := do
  if let some i := asCol t then `($(Lean.mkIdent ``projAt) $i)
  else `(ProjColIn.term (ra_term% $t))

macro_rules
  | `(ra_proj% $t:raTerm) => mkProj t

macro_rules
  | `(ra_pred% ($p:raPred)) => `(ra_pred% $p)
  | `(ra_pred% $a:raTerm = $b:raTerm)  => do mkCmp (← `(CompOp.eq)) (← `(CompOp.eq)) a b
  | `(ra_pred% $a:raTerm ≠ $b:raTerm)  => do mkCmp (← `(CompOp.ne)) (← `(CompOp.ne)) a b
  | `(ra_pred% $a:raTerm < $b:raTerm)  => do mkCmp (← `(CompOp.lt)) (← `(CompOp.gt)) a b
  | `(ra_pred% $a:raTerm ≤ $b:raTerm)  => do mkCmp (← `(CompOp.le)) (← `(CompOp.ge)) a b
  | `(ra_pred% $a:raTerm > $b:raTerm)  => do mkCmp (← `(CompOp.gt)) (← `(CompOp.lt)) a b
  | `(ra_pred% $a:raTerm ≥ $b:raTerm)  => do mkCmp (← `(CompOp.ge)) (← `(CompOp.le)) a b
  | `(ra_pred% ¬$p:raPred)      => `(GenPredIn.not (ra_pred% $p))
  | `(ra_pred% $a:raPred ∧ $b:raPred)  => `(GenPredIn.and (ra_pred% $a) (ra_pred% $b))
  | `(ra_pred% $a:raPred ∨ $b:raPred)  => `(GenPredIn.or (ra_pred% $a) (ra_pred% $b))

macro_rules
  | `(ra_query% ($q:raQuery)) => `(ra_query% $q)
  | `(ra_query% rel $n:num $s:str) => `(AggQuery.Rel $n $s)
  | `(ra_query% `($q:term)) => `($q)
  | `(ra_query% π[$ts,*] $q:raQuery) =>
      `(AggQuery.Proj ![$[ra_proj% $ts],*] (ra_query% $q))
  | `(ra_query% σ[$p:raPred] $q:raQuery) => `(AggQuery.Sel (ra_pred% $p) (ra_query% $q))
  | `(ra_query% $a:raQuery × $b:raQuery) => `(AggQuery.Prod (ra_query% $a) (ra_query% $b))
  | `(ra_query% $a:raQuery ⊎ $b:raQuery) => `(AggQuery.Sum (ra_query% $a) (ra_query% $b))
  | `(ra_query% ε $q:raQuery)    => `(AggQuery.Dedup (allReg (ra_query% $q)))
  | `(ra_query% γ[$ks,* ; $as,*] $q:raQuery) => do
      let keys ← ks.getElems.mapM fun k => match k with
        | `(raCol| #$i:num) => `(($i : Fin _))
        | _ => Lean.Macro.throwUnsupported
      let ts ← as.getElems.mapM fun a => match a with
        | `(raAgg| $t:raTerm : $_:term) => `(ra_cterm% $t)
        | _ => Lean.Macro.throwUnsupported
      let fs ← as.getElems.mapM fun a => match a with
        | `(raAgg| $_:raTerm : $f:term) => pure f
        | _ => Lean.Macro.throwUnsupported
      -- no keys is not a grouping with none: it is SQL's scalar
      -- aggregation, whose single row survives an empty input
      if ks.getElems.isEmpty then
        `(AggQuery.GammaScalar ![$ts,*] ![$fs,*] (allReg (ra_query% $q)))
      else
        `(AggQuery.Gamma ![$keys,*] ![$ts,*] ![$fs,*] (allReg (ra_query% $q)))
  | `(ra_query% ⊞[$ps,* ; $os,* ; $o:term ; $w:term ; $a:raAgg] $q:raQuery) => do
      let keys ← ps.getElems.mapM fun k => match k with
        | `(raCol| #$i:num) => `(($i : Fin _))
        | _ => Lean.Macro.throwUnsupported
      let ords ← os.getElems.mapM fun k => match k with
        | `(raCol| #$i:num) => `(($i : Fin _))
        | _ => Lean.Macro.throwUnsupported
      match a with
      | `(raAgg| $t:raTerm : $f:term) =>
          `(AggQuery.Win ![$keys,*] ![$ords,*] $o $w (ra_cterm% $t) $f
              (allReg (ra_query% $q)))
      | _ => Lean.Macro.throwUnsupported
  | `(ra_query% $a:raQuery ∖ $b:raQuery) =>
      `(AggQuery.Diff (allReg (ra_query% $a)) (allReg (ra_query% $b)))

macro_rules
  | `(RA[ $q:raQuery ]) => `(ra_query% $q)
  | `(RA[ $t:term | $q:raQuery ]) => `((ra_query% $q : AggQuery $t _ _))

end Provenance.Notation

/-! ### Worked productions

Every production is exercised below. A surface syntax that elaborates is the
only evidence that it parses and that the obligations it hides – the
regularity proofs, the kind vectors, the retaggings – really do discharge. -/

section Examples

variable {T : Type} [ValueType T]

/-- Selection, join, projection and duplicate elimination. -/
example : AggQuery T 1 (ColKind.allReg 1) :=
  RA[T | ε (π[#3] (σ[#0 < #4 ∧ #3 = #7] (rel 4 "R" × rel 4 "R"))) ]

/-- Union and difference, both retagging their arguments. -/
example : AggQuery T 2 (ColKind.allReg 2) :=
  RA[T | (π[#0, #3] (rel 4 "R")) ∖ (π[#0, #3] (rel 4 "S")) ]

example : AggQuery T 4 (ColKind.allReg 4) :=
  RA[T | rel 4 "R" ⊎ rel 4 "S" ]

/-- Grouping: the key columns before the `;`, the aggregated columns
after. -/
example := RA[T | γ[#3 ; #0 : SeqAggFunc.sum] rel 4 "R" ]

/-- Aggregation without grouping: no keys, so the single row survives an
empty input. -/
example := RA[T | γ[ ; #0 : SeqAggFunc.sum] rel 4 "R" ]

/-- A comparison against a token column is written like any other
comparison; which atom it becomes is decided by the kind vector. -/
example (c : T) :=
  RA[T | σ[#1 ≥ `(c)] γ[#3 ; #0 : SeqAggFunc.sum] rel 4 "R" ]

/-- A window: partition columns, order columns, clause, frame, aggregated
column. -/
example := RA[T |
  ⊞[#3 ; #0 ; OrderSpec.asc 1 ; ValueFrame.whole ; #0 : SeqAggFunc.sum]
    rel 4 "R" ]

/-- A window over the whole relation, with the frame of the rows the clause
sorts strictly before the current row's peers. -/
example := RA[T |
  ⊞[ ; #0 ; OrderSpec.asc 1 ; ValueFrame.rangeBefore (OrderSpec.asc 1) ;
    #0 : SeqAggFunc.sum] rel 4 "R" ]

end Examples
