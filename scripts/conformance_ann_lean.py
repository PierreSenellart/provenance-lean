#!/usr/bin/env python3
"""Write the Lean modules that check the annotated semantics against ProvSQL.

For each level F0 to F9 of the plain conformance suite, writes
Provenance/Conformance/Ann/F<k>.lean: for every query of that level that
Provenance/Conformance/ExpectedAnn.lean has answers for, with the term the
plain module gives it,

* one theorem per instance (counting semiring) and per valuation and instance
  (Boolean semiring), that the annotated semantics gives ProvSQL's rows;
* one theorem gathering them, over every instance.

A query's term is read off its plain theorem, `run i <term> = rel (<name> i)`,
so the two suites state the same query. Its proof unfolds the derived
operators, rewrites their casts away and ends with `decide +kernel`; the
grouping sets are first rewritten to plain groupings (`gammaSet_enum`), the
recursions read off their fixpoint with the bound the plain proof gives.

Each module imports the one of the level before, so that Lake builds them one
at a time, and elaborates its theorems one at a time (Elab.async false): a
module takes up to 4 GB to check.

Usage: scripts/conformance_ann_lean.py
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONF = ROOT / "Provenance" / "Conformance"
LEVELS = [f"F{k}" for k in range(10)]
NINST = 4  # Inst
NVAL = 2   # Val

# The definitions of `Provenance.Derived` a term is built with, unfolded before
# evaluation, and the ones its columns and predicates are built with, unfolded
# once the casts are gone (unfolding those first leaves casts `rw` cannot reach).
STRUCT = ("pad padRight padLeft inter innerJoin leftUnmatched rightUnmatched leftOuter "
          "rightOuter fullOuter matchCount semijoin antijoin firstValue lastValue lag lead "
          "nthValue lagAt leadAt rank denseRank percentRank cumeDist ntile truncate distinctOn "
          "truncateFrom gammaSet gammaSets gammaDistinct gammaScalarDistinct gammaFilter "
          "winFilter gammaWhere winWhere unit rowOf values").split()
HELPER = ("padCol interCond firstCols lastCols fstBlock matchedLeft matchedRight dropCount "
          "carryCol overWindow dropRank rankRange rankFrom gsCol gsTotalCol gsRow gsRowSingle "
          "gsRowPos gsPos distinctCols distinctRow filterTerm filterHolds countKinds "
          "countCol").split()
FRAG = ["FragQueryIn.toAgg", "FragQueryIn.countSiteIn", "FragQueryIn.matchCountIn",
        "FragQueryIn.dropCountIn"]

# The aggregate column ProvSQL explodes into one row per value it takes, where
# the plain term reads it as a value: the annotated statement reads it as a key.
EXPLODE = {"exists_value": 2}


def names(xs):
    return ", ".join("AggQueryIn." + x for x in xs)


def grouping_sets(term):
    """The grouping sets of a term, as (width of the key, sorted index lists),
    or None if it has none."""
    m = re.search(r"AggQueryIn\.gammaSets? (!\[[^\]]*\]|\(fun k : Fin 0 => k\.elim0\))", term)
    if not m:
        return None
    key = m.group(1)
    width = 0 if key.startswith("(") else len(key[2:-1].split(","))
    sets = [[] if s == "∅" else [int(x) for x in s[1:-1].split(",")]
            for s in re.findall(r"\{[\d, ]+\}|∅", term[m.end():])]
    return width, sets


def gs_steps(width, sets):
    """Each grouping set rewritten to a grouping over its enumeration."""
    out = ["try simp only [AggQueryIn.gammaSets, List.foldr]"]
    for s in sets:
        if not s:
            continue
        S = "({" + ", ".join(map(str, s)) + "} : Finset (Fin %d))" % width
        e = "(![" + ", ".join(map(str, s)) + "] : Fin %s.card → Fin %d)" % (S, width)
        pos = ("(fun b : Fin %d => " % width
               + "".join(f"if b = {a} then some ⟨{k}, by decide⟩ else " for k, a in enumerate(s))
               + "none)")
        out.append(
            f"erw [gammaSet_enum _ _ _ {S} (by decide) {e}"
            " (by intro a b h; fin_cases a <;> fin_cases b <;> first | decide | exact absurd h (by decide))"
            " (by intro x; fin_cases x <;> decide)"
            f" {pos}"
            " (by intro x; fin_cases x <;> first | rfl | decide)"
            " (by intro a ha; fin_cases a <;> simp_all)]")
    if [] in sets:
        out.append(f"erw [AggQueryIn.gammaSet.eq_1 _ _ _ (∅ : Finset (Fin {width}))]")
        out.append("simp only [eq_self, ↓reduceIte]")
    return out


def rec_steps(proof):
    """The fixpoint of a recursion, with the bound its plain proof gives."""
    m = re.search(r"muSumFix_eq_of_empty \(k := \d+\)", proof)
    if m:
        return [f"rw [{m.group(0)} (by rw [← Multiset.card_eq_zero]; decide)"
                " (by rw [← Multiset.card_eq_zero]; decide)]"]
    m = re.search(r"muFix_eq_of_fix \(j := \d+\)", proof)
    if m:
        return [f"erw [{m.group(0)} ?hj]",
                "case hj => exact @of_decide_eq_true _ (relDecEq _ _) (by decide)"]
    return None


def proof(run, term, plain_proof):
    unfold = f"{names(STRUCT)}, List.foldl, {', '.join(FRAG)}"
    gs = grouping_sets(term)
    rec = rec_steps(plain_proof)
    if gs:
        unfold = unfold.replace(", AggQueryIn.gammaSets", "").replace(", AggQueryIn.gammaSet", "")
        lines = [f"simp only [{run}]"] + gs_steps(*gs) + [f"try simp only [{unfold}]"]
    elif rec:
        lines = [f"simp only [{run}, {unfold}, AggQueryIn.evaluate, AggQueryIn.evaluate_castKind]"] + rec
    else:
        lines = [f"simp only [{run}, {unfold}]"]
    lines += ["repeat (first",
              "  | rw [AggQueryIn.evaluate_castKind]",
              "  | erw [AggQueryIn.evaluate_castKind]",
              "  | simp only [AggQueryIn.evaluate])",
              f"try simp only [{names(HELPER)}, gsColPos, addCases_const, snoc_const, append_const]",
              "try simp only [eval_vecCons, ProjColIn.eval, pairCol_k]",
              "decide +kernel"]
    return "\n  ".join(lines)


def queries(level):
    """(name, term, plain proof) of the queries of a level, in its order."""
    src = (CONF / f"{level}.lean").read_text()
    out = []
    for blk in re.split(r"\n(?=theorem )", src):
        m = re.match(r"theorem (\w+)_ok : ∀ i,\s*run i (.*?)\s*=\s*rel \((\w+) i\) := by(.*)",
                     blk, re.S)
        if m and m.group(1) == m.group(3):
            out.append((m.group(1), " ".join(m.group(2).split()), m.group(4)))
    return out


def module(k, answered):
    level = LEVELS[k]
    prev = "Provenance.Conformance.Ann.Basic" if k == 0 else f"Provenance.Conformance.Ann.{LEVELS[k - 1]}"
    L = ["/-\n  Released under the MIT license as described in the file LICENSE.\n"
         "  Authors: Pierre Senellart\n-/\nmodule\n",
         f"public import {prev}\npublic import Provenance.Conformance.{level}\n"
         "import all Provenance.AggQuery\nimport all Provenance.Derived\n"
         "import all Provenance.FragQuery\n",
         f"/-!\n# Conformance of the annotated semantics with ProvSQL at `{level}`\n\n"
         f"The queries of `Provenance.Conformance.{level}`, with the terms written there.\n"
         "Generated by `scripts/conformance_ann_lean.py`; not edited by hand.\n-/\n",
         "public section\n\n-- one theorem at a time, so that the memory is that of one proof\n"
         "set_option Elab.async false\n"
         "-- one proof serves every query: some of its steps do nothing on some of them\n"
         "set_option linter.unusedSimpArgs false\nset_option linter.unusedTactic false\n"
         "set_option linter.unreachableTactic false\nset_option linter.unnecessarySeqFocus false\n"
         "\nnamespace Conformance\n\nopen WithNull\n"]
    count = 0
    for name, term, plain in queries(level):
        if name in EXPLODE:
            term = f"(AggQueryIn.Explode {EXPLODE[name]} rfl ({term}))"
        for kind, run, sr, args in (
                ("N", "runNR", "counting", [(i,) for i in range(NINST)]),
                ("B", "runBR", "Boolean", [(j, i) for j in range(NVAL) for i in range(NINST)])):
            ann = f"{name}_ann{kind}"
            if ann not in answered:
                continue
            count += 1
            parts = []
            for a in args:
                sfx, sp = "_".join(map(str, a)), " ".join(map(str, a))
                parts.append(f"{ann}_ok_{sfx}")
                L.append(f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 8000000 in\n"
                         f"theorem {ann}_ok_{sfx} :\n    {run} {sp} {term}\n"
                         f"      = ({ann} {sp} : Multiset _) := by\n  {proof(run, term, plain)}\n")
            binders = "i" if kind == "N" else "j i"
            cases = "fin_cases i" if kind == "N" else "fin_cases j <;> fin_cases i"
            L.append(f"/-- The annotated semantics of `{name}` over the {sr} semiring is ProvSQL's,\n"
                     f"on every instance{'' if kind == 'N' else ' and under every valuation'}. -/\n"
                     f"theorem {ann}_ok : ∀ {binders},\n    {run} {binders} {term}\n"
                     f"      = ({ann} {binders} : Multiset _) := by\n"
                     f"  intro {binders}\n  {cases}\n  exacts [{', '.join(parts)}]\n")
    L.append("end Conformance\n")
    return "\n".join(L), count


def main():
    answered = set(re.findall(r"abbrev (\w+_ann[NB]) ", (CONF / "ExpectedAnn.lean").read_text()))
    total = 0
    for k, level in enumerate(LEVELS):
        text, count = module(k, answered)
        (CONF / "Ann" / f"{level}.lean").write_text(text)
        total += count
        print(f"{level}: {count} statements")
    print(f"{total} statements, of {len(answered)} answers in ExpectedAnn")


if __name__ == "__main__":
    main()
