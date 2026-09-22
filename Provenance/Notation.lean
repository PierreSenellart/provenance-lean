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

/-! ### Queries -/

syntax:max "(" raQuery ")" : raQuery
syntax:max "rel " num str : raQuery
/-- A query already written in Lean. -/
syntax:max "`(" term ")" : raQuery
syntax:80 "π[" raTerm,* "] " raQuery : raQuery
syntax:80 "σ[" raPred "] " raQuery : raQuery
syntax:80 "ε " raQuery : raQuery
syntax:70 raQuery " × " raQuery : raQuery
syntax:60 raQuery " ⊎ " raQuery : raQuery
syntax:60 raQuery " ∖ " raQuery : raQuery

/-- Bracket around a query of the surface syntax. -/
syntax "RA[" raQuery "]" : term

/-! ### Elaboration

Each category expands through an internal marker in the term category, which
is what lets a rule recurse into its own sub-syntax. Column references become
`TermG.index` with the regularity proof discharged by `rfl`, which is what a
concrete kind vector makes available. -/

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
scoped syntax:max "ra_pred% " raPred : term
scoped syntax:max "ra_query% " raQuery : term

macro_rules
  | `(ra_term% #$i:num)     => `(TermG.index $i (by rfl))
  | `(ra_term% ($t:raTerm)) => `(ra_term% $t)
  | `(ra_term% `($t:term))  => `(TermG.const $t)
  | `(ra_term% $a:raTerm + $b:raTerm)     => `(TermG.add (ra_term% $a) (ra_term% $b))
  | `(ra_term% $a:raTerm - $b:raTerm)     => `(TermG.sub (ra_term% $a) (ra_term% $b))
  | `(ra_term% $a:raTerm * $b:raTerm)     => `(TermG.mul (ra_term% $a) (ra_term% $b))

macro_rules
  | `(ra_pred% ($p:raPred)) => `(ra_pred% $p)
  | `(ra_pred% $a:raTerm = $b:raTerm)  => `(GenPred.cmp CompOp.eq (ra_term% $a) (ra_term% $b))
  | `(ra_pred% $a:raTerm ≠ $b:raTerm)  => `(GenPred.cmp CompOp.ne (ra_term% $a) (ra_term% $b))
  | `(ra_pred% $a:raTerm < $b:raTerm)  => `(GenPred.cmp CompOp.lt (ra_term% $a) (ra_term% $b))
  | `(ra_pred% $a:raTerm ≤ $b:raTerm)  => `(GenPred.cmp CompOp.le (ra_term% $a) (ra_term% $b))
  | `(ra_pred% $a:raTerm > $b:raTerm)  => `(GenPred.cmp CompOp.gt (ra_term% $a) (ra_term% $b))
  | `(ra_pred% $a:raTerm ≥ $b:raTerm)  => `(GenPred.cmp CompOp.ge (ra_term% $a) (ra_term% $b))
  | `(ra_pred% ¬$p:raPred)      => `(GenPred.not (ra_pred% $p))
  | `(ra_pred% $a:raPred ∧ $b:raPred)  => `(GenPred.and (ra_pred% $a) (ra_pred% $b))
  | `(ra_pred% $a:raPred ∨ $b:raPred)  => `(GenPred.or (ra_pred% $a) (ra_pred% $b))

macro_rules
  | `(ra_query% ($q:raQuery)) => `(ra_query% $q)
  | `(ra_query% rel $n:num $s:str) => `(AggQuery.Rel $n $s)
  | `(ra_query% `($q:term)) => `($q)
  | `(ra_query% π[$ts,*] $q:raQuery) =>
      `(AggQuery.Proj ![$[ProjCol.term (ra_term% $ts)],*] (ra_query% $q))
  | `(ra_query% σ[$p:raPred] $q:raQuery) => `(AggQuery.Sel (ra_pred% $p) (ra_query% $q))
  | `(ra_query% $a:raQuery × $b:raQuery) => `(AggQuery.Prod (ra_query% $a) (ra_query% $b))
  | `(ra_query% $a:raQuery ⊎ $b:raQuery) => `(AggQuery.Sum (ra_query% $a) (ra_query% $b))
  | `(ra_query% ε $q:raQuery)    => `(AggQuery.Dedup (allReg (ra_query% $q)))
  | `(ra_query% $a:raQuery ∖ $b:raQuery) =>
      `(AggQuery.Diff (allReg (ra_query% $a)) (allReg (ra_query% $b)))

macro_rules
  | `(RA[ $q:raQuery ]) => `(ra_query% $q)

end Provenance.Notation
