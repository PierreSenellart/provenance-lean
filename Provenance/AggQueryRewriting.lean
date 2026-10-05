/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryEmbedding

/-!
# The rewriting rules (R1)–(R4), natively on the general syntax

The rewriting of [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]
turns a query over annotated relations into an ordinary query over the
*composite* encoding: one extra column carries the annotation, of the
lifted value type `T ⊕ K`. With the three-kind discipline the rewriting
is expressible natively: the annotation column is *marked* `prov`
(`ColKind.rewKinds`), read back by `TermGIn.provIndex` terms, aggregated by
`AggQueryIn.ProvSum` (the `⊕`-gate creation of `ε` and `∖`), and the
value-kind bookkeeping is `AggQueryIn.Retag` – semantically the identity.

`AggQueryIn.rewriting` below mirrors the classical `Query.rewriting`
rule for rule on the classical fragment (`AggQueryIn.classical`) of the
general syntax. Its correctness against `evaluateAnnotated` is assembled
in stages, over the next two modules: the strip to the classical syntax
and its faithfulness (`Provenance.AggQueryStrip`), then the
plain-semantics agreement of the two rewritten queries and the
correctness theorem itself (`Provenance.AggQueryRewritingValid`).

This module holds the syntax of the rewriting: the target kind vector,
the classical fragment, the casts into the composite domain, and
`AggQueryIn.rewriting`.
-/

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

/-! ## The target kind vector -/

/-- The kind vector of a rewritten query: `n` data columns followed by
the provenance column. -/
def ColKind.rewKinds (n : ℕ) : Fin (n + 1) → ColKind :=
  fun k => if (k : ℕ) < n then ColKind.reg else ColKind.prov

theorem ColKind.rewKinds_lt {n : ℕ} {k : Fin (n + 1)} (h : (k : ℕ) < n) :
    ColKind.rewKinds n k = ColKind.reg := ite_eq_left h

theorem ColKind.rewKinds_of_not_lt {n : ℕ} {k : Fin (n + 1)}
    (h : ¬ (k : ℕ) < n) : ColKind.rewKinds n k = ColKind.prov := ite_eq_right h

theorem ColKind.rewKinds_base {n : ℕ} (k : Fin (n + 1)) :
    (ColKind.rewKinds n k).base = ColKind.reg := by
  unfold ColKind.rewKinds
  split <;> rfl

/-- Retag any pointwise value-kinded query to the rewriting kinds. -/
def AggQueryIn.retagToRew {T' : Type} {n : ℕ} {κ : Fin (n + 1) → ColKind}
    (h : ∀ k, (κ k).base = ColKind.reg)
    (q : AggQuery T' (n + 1) κ) : AggQuery T' (n + 1) (ColKind.rewKinds n) :=
  AggQueryIn.Retag (fun k => (h k).trans (ColKind.rewKinds_base k).symm) q

/-! ## The classical fragment -/

/-- The classical (R1)–(R4) source fragment of the general syntax: no
grouping, no provenance aggregation, no retagging, projections through
regular terms only, selections without aggregate atoms. -/
def AggQueryIn.classical : {c n : ℕ} → {κ : Fin n → ColKind} →
    AggQueryIn T c n κ → Prop
  | _, _, _, .Rel _ _ => True
  | _, _, _, .Proj ps q =>
      (∀ j, (ps j).kind = ColKind.reg) ∧ q.classical
  | _, _, _, .Sel φ q => φ.hasAggAtom = false ∧ q.classical
  | _, _, _, .Prod q₁ q₂ => q₁.classical ∧ q₂.classical
  | _, _, _, .Sum q₁ q₂ => q₁.classical ∧ q₂.classical
  | _, _, _, .Dedup q => q.classical
  | _, _, _, .Diff q₁ q₂ => q₁.classical ∧ q₂.classical
  -- the apply is not part of (R1)-(R5): its right side is read once per
  -- row of its left, which the rewritten plan has no way to express
  | _, _, _, .Apply _ _ => False
  -- an aggregate column read as a key is not part of (R1)-(R5): the
  -- rewritten plan has no way to enumerate the values a token takes
  | _, _, _, .Alt _ _ _ => False
  -- recursion is not part of (R1)-(R5): a rewritten body carries the
  -- provenance column, so the name bound by the rounds would have to be
  -- bound to the rewritten relation, and the fixpoint is then over a
  -- different schema than the one the source query iterates
  | _, _, _, .Mu _ _ _ _ => False
  | _, _, _, .MuSet _ _ _ _ => False
  | _, _, _, .Gamma _ _ _ _ _ => False
  | _, _, _, .GammaScalar _ _ _ => False
  | _, _, _, .GammaNest _ _ _ _ _ => False
  | _, _, _, .ProvSum _ _ _ _ => False
  | _, _, _, .Retag _ _ => False
  | _, _, _, .GammaTok _ _ _ _ _ _ _ => False
  -- rewriting a window into the provenance-carrying form is not part of
  -- (R1)-(R5); a window is excluded from the fragment, as a grouping is
  | _, _, _, .Win _ _ _ _ _ _ _ _ _ => False
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _ => False

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- A classical query builds no nested token, every aggregating operator
being outside the fragment. -/
theorem AggQueryIn.noGammaNest_of_classical :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.classical → q.noGammaNest
  | _, _, _, .Rel _ _, _ => trivial
  | _, _, _, .Proj _ q, hq => AggQueryIn.noGammaNest_of_classical q hq.2
  | _, _, _, .Sel _ q, hq => AggQueryIn.noGammaNest_of_classical q hq.2
  | _, _, _, .Prod q₁ q₂, hq =>
    ⟨AggQueryIn.noGammaNest_of_classical q₁ hq.1,
      AggQueryIn.noGammaNest_of_classical q₂ hq.2⟩
  | _, _, _, .Sum q₁ q₂, hq =>
    ⟨AggQueryIn.noGammaNest_of_classical q₁ hq.1,
      AggQueryIn.noGammaNest_of_classical q₂ hq.2⟩
  | _, _, _, .Dedup q, hq => AggQueryIn.noGammaNest_of_classical q hq
  | _, _, _, .Diff q₁ q₂, hq =>
    ⟨AggQueryIn.noGammaNest_of_classical q₁ hq.1,
      AggQueryIn.noGammaNest_of_classical q₂ hq.2⟩
  | _, _, _, .Apply _ _, hq => hq.elim
  | _, _, _, .Alt _ _ _, hq => hq.elim
  | _, _, _, .Mu _ _ _ _, hq => hq.elim
  | _, _, _, .MuSet _ _ _ _, hq => hq.elim
  | _, _, _, .Gamma _ _ _ _ _, hq => hq.elim
  | _, _, _, .GammaScalar _ _ _, hq => hq.elim
  | _, _, _, .GammaNest _ _ _ _ _, hq => hq.elim
  | _, _, _, .ProvSum _ _ _ _, hq => hq.elim
  | _, _, _, .Retag _ _, hq => hq.elim
  | _, _, _, .GammaTok _ _ _ _ _ _ _, hq => hq.elim
  | _, _, _, .Win _ _ _ _ _ _ _ _ _, hq => hq.elim
  | _, _, _, .WinExpr _ _ _ _ _ _ _ _ _, hq => hq.elim

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Classical queries have all-regular kinds (pointwise). -/
theorem AggQueryIn.classical_kinds :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} (q : AggQueryIn T c n κ),
      q.classical → ∀ k, κ k = ColKind.reg
  | _, _, _, .Rel _ _, _, _ => rfl
  | _, _, _, .Proj ps _, hq, k => hq.1 k
  | _, _, _, .Sel _ q, hq, k => classical_kinds q hq.2 k
  | _, _, _, .Prod q₁ q₂, hq, k => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]
      exact classical_kinds q₁ hq.1 i
    · rw [Fin.append_right]
      exact classical_kinds q₂ hq.2 j
  | _, _, _, .Sum q₁ q₂, hq, k => classical_kinds q₁ hq.1 k
  | _, _, _, .Dedup _, _, _ => rfl
  | _, _, _, .Diff _ _, _, _ => rfl

/-! ## Casting terms, predicates and columns to the composite domain -/

/-- A term over all-regular columns, over the composite domain with its
columns shifted into the data block of the rewritten schema. -/
def TermGIn.castComposite {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    TermGIn T c κ → TermG (T ⊕ K) (ColKind.rewKinds n)
  | .const a => .const (Sum.inl a)
  -- as in `TermGIn.strip`: the valuation a closed query reads is `𝟘`
  | .outer _ => .const (Sum.inl 0)
  | .index k _ => .index (k.castLE (Nat.le_succ n))
      (ColKind.rewKinds_lt k.isLt)
  | .provIndex k h =>
      absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | .cmpAgg k h _ _ =>
      absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | .chiGate _ _ _ => .const (Sum.inl 0)
  | .add t₁ t₂ => .add (t₁.castComposite hκ) (t₂.castComposite hκ)
  | .sub t₁ t₂ => .sub (t₁.castComposite hκ) (t₂.castComposite hκ)
  | .mul t₁ t₂ => .mul (t₁.castComposite hκ) (t₂.castComposite hκ)
  | .caseWhen op t₁ t₂ t₃ t₄ =>
      .caseWhen op (t₁.castComposite hκ) (t₂.castComposite hκ)
        (t₃.castComposite hκ) (t₄.castComposite hκ)
  | .coalesce t₁ t₂ => .coalesce (t₁.castComposite hκ) (t₂.castComposite hκ)

/-- An aggregate-atom-free predicate, over the composite domain. -/
def GenPredIn.castComposite {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    (φ : GenPredIn T c κ) → φ.hasAggAtom = false →
    GenPred (T ⊕ K) (ColKind.rewKinds n)
  | .cmp op t₁ t₂, _ =>
      .cmp op (t₁.castComposite hκ) (t₂.castComposite hκ)
  | .aggCmp _ _ _ _, hφ => Bool.noConfusion hφ
  | .and φ ψ, hφ =>
      .and (φ.castComposite hκ (Bool.or_eq_false_iff.mp hφ).1)
        (ψ.castComposite hκ (Bool.or_eq_false_iff.mp hφ).2)
  | .or φ ψ, hφ =>
      .or (φ.castComposite hκ (Bool.or_eq_false_iff.mp hφ).1)
        (ψ.castComposite hκ (Bool.or_eq_false_iff.mp hφ).2)
  | .not φ, hφ => .not (φ.castComposite hκ hφ)

/-- A regular projection column, over the composite domain. -/
def ProjColIn.castComposite {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    (p : ProjColIn T c κ) → p.kind = ColKind.reg →
    ProjCol (T ⊕ K) (ColKind.rewKinds n)
  | .term t, _ => .term (t.castComposite hκ)
  | .token _ _, hp => ColKind.noConfusion hp
  | .aggTerm _ _ _, hp => ColKind.noConfusion hp
  | .provTerm _, hp => ColKind.noConfusion hp

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The composite cast emits no indicator gate: a source gate, whose
generic semantics is the junk constant, casts to that constant. -/
theorem TermGIn.castComposite_chiFree {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    ∀ (t : TermGIn T c κ), (t.castComposite hκ (K := K)).chiFree
  | .const _ => trivial
  | .outer _ => trivial
  | .index _ _ => trivial
  | .provIndex k h =>
      absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | .cmpAgg k h _ _ =>
      absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | .chiGate _ _ _ => trivial
  | .add t₁ t₂ => ⟨castComposite_chiFree hκ t₁, castComposite_chiFree hκ t₂⟩
  | .sub t₁ t₂ => ⟨castComposite_chiFree hκ t₁, castComposite_chiFree hκ t₂⟩
  | .mul t₁ t₂ => ⟨castComposite_chiFree hκ t₁, castComposite_chiFree hκ t₂⟩
  | .caseWhen _ t₁ t₂ t₃ t₄ =>
      ⟨castComposite_chiFree hκ t₁, castComposite_chiFree hκ t₂,
        castComposite_chiFree hκ t₃, castComposite_chiFree hκ t₄⟩
  | .coalesce t₁ t₂ =>
      ⟨castComposite_chiFree hκ t₁, castComposite_chiFree hκ t₂⟩

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The composite cast of a predicate emits no indicator gate. -/
theorem GenPredIn.castComposite_chiFree {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    ∀ (φ : GenPredIn T c κ) (hφ : φ.hasAggAtom = false),
      (φ.castComposite hκ hφ (K := K)).chiFree
  | .cmp _ t₁ t₂, _ =>
      ⟨TermGIn.castComposite_chiFree hκ t₁, TermGIn.castComposite_chiFree hκ t₂⟩
  | .aggCmp _ _ _ _, hφ => Bool.noConfusion hφ
  | .and φ ψ, hφ =>
      ⟨castComposite_chiFree hκ φ (Bool.or_eq_false_iff.mp hφ).1,
       castComposite_chiFree hκ ψ (Bool.or_eq_false_iff.mp hφ).2⟩
  | .or φ ψ, hφ =>
      ⟨castComposite_chiFree hκ φ (Bool.or_eq_false_iff.mp hφ).1,
       castComposite_chiFree hκ ψ (Bool.or_eq_false_iff.mp hφ).2⟩
  | .not φ, hφ => castComposite_chiFree hκ φ hφ

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The composite cast of a projection column emits no indicator gate. -/
theorem ProjColIn.castComposite_chiFree {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    ∀ (p : ProjColIn T c κ) (hp : p.kind = ColKind.reg),
      (p.castComposite hκ hp (K := K)).chiFree
  | .term t, _ => TermGIn.castComposite_chiFree hκ t
  | .token _ _, hp => ColKind.noConfusion hp
  | .aggTerm _ _ _, hp => ColKind.noConfusion hp
  | .provTerm _, hp => ColKind.noConfusion hp

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
theorem ProjColIn.castComposite_kind {c n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) (p : ProjColIn T c κ)
    (hp : p.kind = ColKind.reg) :
    ((p.castComposite hκ hp : ProjCol (T ⊕ K) (ColKind.rewKinds n))).kind
      = ColKind.reg := by
  cases p with
  | term t => rfl
  | token k hk => exact ColKind.noConfusion hp
  | aggTerm k hk gf => exact ColKind.noConfusion hp
  | provTerm t => exact ColKind.noConfusion hp

/-! ## The rewriting -/

/-- **The (R1)–(R4) rewriting, natively on the general syntax.** Each
rule mirrors the classical `Query.rewriting`: the base relation exposes
its provenance column (R1), projections keep it verbatim (R2, key case),
selections filter the data columns (R2), joins multiply the two
provenance columns (R3), unions concatenate (R4, first case),
deduplication `⊕`-sums the provenance per surviving tuple (R4, `ε`), and
difference combines the unmatched branch with the matched branch's
`α ⊖ Σβ` (R4, `∖`). -/
def AggQueryIn.rewriting :
    {c n : ℕ} → {κ : Fin n → ColKind} → (q : AggQueryIn T c n κ) →
    q.classical → AggQuery (T ⊕ K) (n + 1) (ColKind.rewKinds n)
  | _, n, _, .Rel _ s, _ =>
    AggQueryIn.retagToRew (fun _ => rfl) (AggQueryIn.Rel (n + 1) s)
  | _, _, _, @AggQueryIn.Proj _ _ n m κ ps q, hq =>
    AggQueryIn.retagToRew
      (fun j => by
        by_cases hj : (j : ℕ) < m
        · rw [dite_eq_left hj, ProjColIn.castComposite_kind]
          rfl
        · rw [dite_eq_right hj]
          rfl)
      (AggQueryIn.Proj
        (fun j : Fin (m + 1) =>
          if hj : (j : ℕ) < m then
            (ps ⟨j, hj⟩).castComposite
              (AggQueryIn.classical_kinds q hq.2) (hq.1 ⟨j, hj⟩)
          else
            ProjColIn.provTerm (TermGIn.provIndex (Fin.last n)
              (ColKind.rewKinds_of_not_lt (lt_irrefl n))))
        (q.rewriting hq.2))
  | _, _, _, .Sel φ q, hq =>
    AggQueryIn.Sel (φ.castComposite (AggQueryIn.classical_kinds q hq.2) hq.1)
      (q.rewriting hq.2)
  | _, _, _, @AggQueryIn.Prod _ _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq =>
    AggQueryIn.retagToRew
      (fun j => by
        by_cases h₁ : (j : ℕ) < n₁
        · rw [dite_eq_left h₁]; rfl
        · rw [dite_eq_right h₁]
          by_cases h₂ : (j : ℕ) < n₁ + n₂
          · rw [dite_eq_left h₂]; rfl
          · rw [dite_eq_right h₂]; rfl)
      (AggQueryIn.Proj
        (fun j : Fin (n₁ + n₂ + 1) =>
          if h₁ : (j : ℕ) < n₁ then
            ProjColIn.term (TermGIn.index
              (Fin.castAdd (n₂ + 1) (⟨j, Nat.lt_succ_of_lt h₁⟩ : Fin (n₁ + 1)))
              ((Fin.append_left _ _ _).trans (ColKind.rewKinds_lt h₁)))
          else if h₂ : (j : ℕ) < n₁ + n₂ then
            ProjColIn.term (TermGIn.index
              (Fin.natAdd (n₁ + 1)
                (⟨(j : ℕ) - n₁, by omega⟩ : Fin (n₂ + 1)))
              ((Fin.append_right _ _ _).trans
                (ColKind.rewKinds_lt (by simp; omega))))
          else
            ProjColIn.provTerm (TermGIn.mul
              (TermGIn.provIndex (Fin.castAdd (n₂ + 1) (Fin.last n₁))
                ((Fin.append_left _ _ _).trans
                  (ColKind.rewKinds_of_not_lt (lt_irrefl n₁))))
              (TermGIn.provIndex (Fin.natAdd (n₁ + 1) (Fin.last n₂))
                ((Fin.append_right _ _ _).trans
                  (ColKind.rewKinds_of_not_lt (lt_irrefl n₂))))))
        (AggQueryIn.Prod (q₁.rewriting hq.1) (q₂.rewriting hq.2)))
  | _, _, _, .Sum q₁ q₂, hq =>
    AggQueryIn.Sum (q₁.rewriting hq.1) (q₂.rewriting hq.2)
  | _, _, _, @AggQueryIn.Dedup _ _ n q, hq =>
    AggQueryIn.retagToRew
      (fun j => by
        refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
        · rw [Fin.append_left, ColKind.rewKinds_lt i.isLt]
          rfl
        · rw [Fin.append_right]
          rfl)
      (AggQueryIn.ProvSum (fun k : Fin n => k.castLE (Nat.le_succ n))
        (fun k => by
          rw [ColKind.rewKinds_lt k.isLt]
          exact fun hc => ColKind.noConfusion hc)
        (TermGIn.provIndex (Fin.last n)
          (ColKind.rewKinds_of_not_lt (lt_irrefl n)))
        (q.rewriting hq))
  | _, _, _, @AggQueryIn.Diff _ _ n q₁ q₂, hq =>
    -- unmatched branch: rows of `q₁` whose data part is absent from `q₂`
    let keyProj : (q : AggQuery (T ⊕ K) (n + 1) (ColKind.rewKinds n)) →
        AggQuery (T ⊕ K) n (ColKind.allReg n) := fun q =>
      AggQueryIn.Retag (fun _ => rfl)
        (AggQueryIn.Proj
          (fun j : Fin n =>
            ProjColIn.term (TermGIn.index (j.castLE (Nat.le_succ n))
              (ColKind.rewKinds_lt j.isLt)))
          q)
    let q₁r := q₁.rewriting hq.1
    let q₂r := q₂.rewriting hq.2
    let survivors :=
      AggQueryIn.Dedup (AggQueryIn.Diff (keyProj q₁r) (keyProj q₂r))
    let joined₁ :=
      AggQueryIn.Sel
        (keyJoinCond
          (posL := fun k : Fin n => Fin.castAdd n (k.castLE (Nat.le_succ n)))
          (posR := fun k : Fin n => Fin.natAdd (n + 1) k)
          (fun k => (Fin.append_left _ _ _).trans
            (ColKind.rewKinds_lt k.isLt))
          (fun k => (Fin.append_right _ _ _).trans rfl))
        (AggQueryIn.Prod q₁r survivors)
    let branch₁ :=
      AggQueryIn.retagToRew
        (fun j => by
          by_cases hj : (j : ℕ) < n
          · rw [dite_eq_left hj]; rfl
          · rw [dite_eq_right hj]; rfl)
        (AggQueryIn.Proj
          (fun j : Fin (n + 1) =>
            if hj : (j : ℕ) < n then
              ProjColIn.term (TermGIn.index
                (Fin.castAdd n (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (n + 1)))
                ((Fin.append_left _ _ _).trans (ColKind.rewKinds_lt hj)))
            else
              ProjColIn.provTerm (TermGIn.provIndex
                (Fin.castAdd n (Fin.last n))
                ((Fin.append_left _ _ _).trans
                  (ColKind.rewKinds_of_not_lt (lt_irrefl n)))))
          joined₁)
    -- matched branch: `α ⊖ Σβ` against the per-key sum of `q₂`
    let sums₂ :=
      AggQueryIn.ProvSum (fun k : Fin n => k.castLE (Nat.le_succ n))
        (fun k => by
          rw [ColKind.rewKinds_lt k.isLt]
          exact fun hc => ColKind.noConfusion hc)
        (TermGIn.provIndex (Fin.last n)
          (ColKind.rewKinds_of_not_lt (lt_irrefl n)))
        q₂r
    let joined₂ :=
      AggQueryIn.Sel
        (keyJoinCond
          (posL := fun k : Fin n =>
            Fin.castAdd (n + 1) (k.castLE (Nat.le_succ n)))
          (posR := fun k : Fin n =>
            Fin.natAdd (n + 1) (Fin.castAdd 1 k))
          (fun k => (Fin.append_left _ _ _).trans
            (ColKind.rewKinds_lt k.isLt))
          (fun k => (Fin.append_right _ _ _).trans
            ((Fin.append_left _ _ _).trans
              (ColKind.rewKinds_lt k.isLt))))
        (AggQueryIn.Prod q₁r sums₂)
    let branch₂ :=
      AggQueryIn.retagToRew
        (fun j => by
          by_cases hj : (j : ℕ) < n
          · rw [dite_eq_left hj]; rfl
          · rw [dite_eq_right hj]; rfl)
        (AggQueryIn.Proj
          (fun j : Fin (n + 1) =>
            if hj : (j : ℕ) < n then
              ProjColIn.term (TermGIn.index
                (Fin.castAdd (n + 1)
                  (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (n + 1)))
                ((Fin.append_left _ _ _).trans (ColKind.rewKinds_lt hj)))
            else
              ProjColIn.provTerm (TermGIn.sub
                (TermGIn.provIndex (Fin.castAdd (n + 1) (Fin.last n))
                  ((Fin.append_left _ _ _).trans
                    (ColKind.rewKinds_of_not_lt (lt_irrefl n))))
                (TermGIn.provIndex
                  (Fin.natAdd (n + 1) (Fin.natAdd n (0 : Fin 1)))
                  ((Fin.append_right _ _ _).trans
                    (Fin.append_right _ _ _)))))
          joined₂)
    AggQueryIn.Sum branch₁ branch₂
termination_by structural _ _ _ q _ => q
