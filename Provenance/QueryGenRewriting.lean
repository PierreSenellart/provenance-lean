/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryGenEmbedding

/-!
# The rewriting rules (R1)–(R4), natively on the general syntax

The rewriting of [Sen, Maniu & Senellart, *ProvSQL*][sen2026provsql]
turns a query over annotated relations into an ordinary query over the
*composite* encoding: one extra column carries the annotation, of the
lifted value type `T ⊕ K`. With the three-kind discipline the rewriting
is expressible natively: the annotation column is *marked* `prov`
(`ColKind.rewKinds`), read back by `TermG.provIndex` terms, aggregated by
`QueryGen.ProvSum` (the `⊕`-gate creation of `ε` and `∖`), and the
value-kind bookkeeping is `QueryGen.Retag` – semantically the identity.

`QueryGen.rewritingGen` below mirrors the classical `Query.rewriting`
rule for rule on the classical fragment (`QueryGen.classical`) of the
general syntax. Its correctness against `evaluateAnnotatedGen` is
assembled in stages: faithfulness of the classical strip, the classical
correctness theorem `Query.rewriting_valid`, and the plain-semantics
agreement of the two rewritten queries.
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
    ColKind.rewKinds n k = ColKind.reg := if_pos h

theorem ColKind.rewKinds_of_not_lt {n : ℕ} {k : Fin (n + 1)}
    (h : ¬ (k : ℕ) < n) : ColKind.rewKinds n k = ColKind.prov := if_neg h

theorem ColKind.rewKinds_base {n : ℕ} (k : Fin (n + 1)) :
    (ColKind.rewKinds n k).base = ColKind.reg := by
  unfold ColKind.rewKinds
  split <;> rfl

/-- Retag any pointwise value-kinded query to the rewriting kinds. -/
def QueryGen.retagToRew {T' : Type} {n : ℕ} {κ : Fin (n + 1) → ColKind}
    (h : ∀ k, (κ k).base = ColKind.reg)
    (q : QueryGen T' (n + 1) κ) : QueryGen T' (n + 1) (ColKind.rewKinds n) :=
  QueryGen.Retag (fun k => (h k).trans (ColKind.rewKinds_base k).symm) q

/-! ## The classical fragment -/

/-- The classical (R1)–(R4) source fragment of the general syntax: no
grouping, no provenance aggregation, no retagging, projections through
regular terms only, selections without aggregate atoms. -/
def QueryGen.classical : {n : ℕ} → {κ : Fin n → ColKind} →
    QueryGen T n κ → Prop
  | _, _, .Rel _ _ => True
  | _, _, .Proj ps q =>
      (∀ j, (ps j).kind = ColKind.reg) ∧ q.classical
  | _, _, .Sel φ q => φ.hasAggAtom = false ∧ q.classical
  | _, _, .Prod q₁ q₂ => q₁.classical ∧ q₂.classical
  | _, _, .Sum q₁ q₂ => q₁.classical ∧ q₂.classical
  | _, _, .Dedup q => q.classical
  | _, _, .Diff q₁ q₂ => q₁.classical ∧ q₂.classical
  | _, _, .Gamma _ _ _ _ => False
  | _, _, .ProvSum _ _ _ _ => False
  | _, _, .Retag _ _ => False
  | _, _, .GammaTok _ _ _ _ _ _ => False

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- Classical queries have all-regular kinds (pointwise). -/
theorem QueryGen.classical_kinds :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ),
      q.classical → ∀ k, κ k = ColKind.reg
  | _, _, .Rel _ _, _, _ => rfl
  | _, _, .Proj ps _, hq, k => hq.1 k
  | _, _, .Sel _ q, hq, k => classical_kinds q hq.2 k
  | _, _, .Prod q₁ q₂, hq, k => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]
      exact classical_kinds q₁ hq.1 i
    · rw [Fin.append_right]
      exact classical_kinds q₂ hq.2 j
  | _, _, .Sum q₁ q₂, hq, k => classical_kinds q₁ hq.1 k
  | _, _, .Dedup _, _, _ => rfl
  | _, _, .Diff _ _, _, _ => rfl

/-! ## Casting terms, predicates and columns to the composite domain -/

/-- A term over all-regular columns, over the composite domain with its
columns shifted into the data block of the rewritten schema. -/
def TermG.castComposite {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    TermG T κ → TermG (T ⊕ K) (ColKind.rewKinds n)
  | .const a => .const (Sum.inl a)
  | .index k _ => .index (k.castLE (Nat.le_succ n))
      (ColKind.rewKinds_lt k.isLt)
  | .provIndex k h =>
      absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | .cmpAgg k h _ _ =>
      absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | .add t₁ t₂ => .add (t₁.castComposite hκ) (t₂.castComposite hκ)
  | .sub t₁ t₂ => .sub (t₁.castComposite hκ) (t₂.castComposite hκ)
  | .mul t₁ t₂ => .mul (t₁.castComposite hκ) (t₂.castComposite hκ)

/-- An aggregate-atom-free predicate, over the composite domain. -/
def GenPred.castComposite {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    (φ : GenPred T κ) → φ.hasAggAtom = false →
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
def ProjCol.castComposite {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    (p : ProjCol T κ) → p.kind = ColKind.reg →
    ProjCol (T ⊕ K) (ColKind.rewKinds n)
  | .term t, _ => .term (t.castComposite hκ)
  | .token _ _, hp => ColKind.noConfusion hp
  | .provTerm _, hp => ColKind.noConfusion hp

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
theorem ProjCol.castComposite_kind {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) (p : ProjCol T κ)
    (hp : p.kind = ColKind.reg) :
    ((p.castComposite hκ hp : ProjCol (T ⊕ K) (ColKind.rewKinds n))).kind
      = ColKind.reg := by
  cases p with
  | term t => rfl
  | token k hk => exact ColKind.noConfusion hp
  | provTerm t => exact ColKind.noConfusion hp

/-! ## Join conditions on key columns -/

/-- The conjunction of equalities between two blocks of regular columns
(the join condition of the `Diff` rewriting). -/
def keyJoinCond {T' : Type} [Zero T'] {n m : ℕ} {κ : Fin m → ColKind}
    (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ (posL k) = ColKind.reg)
    (hR : ∀ k, κ (posR k) = ColKind.reg) :
    GenPred T' κ :=
  ((List.finRange n).map (fun k =>
    GenPred.cmp CompOp.eq (TermG.index (posL k) (hL k))
      (TermG.index (posR k) (hR k)))).foldr GenPred.and
    (GenPred.cmp CompOp.eq (.const 0) (.const 0))

/-! ## The rewriting -/

/-- **The (R1)–(R4) rewriting, natively on the general syntax.** Each
rule mirrors the classical `Query.rewriting`: the base relation exposes
its provenance column (R1), projections keep it verbatim (R2, key case),
selections filter the data columns (R2), joins multiply the two
provenance columns (R3), unions concatenate (R4, first case),
deduplication `⊕`-sums the provenance per surviving tuple (R4, `ε`), and
difference combines the unmatched branch with the matched branch's
`α ⊖ Σβ` (R4, `∖`). -/
def QueryGen.rewritingGen :
    {n : ℕ} → {κ : Fin n → ColKind} → (q : QueryGen T n κ) →
    q.classical → QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n)
  | n, _, .Rel _ s, _ =>
    QueryGen.retagToRew (fun _ => rfl) (QueryGen.Rel (n + 1) s)
  | _, _, @QueryGen.Proj _ n m κ ps q, hq =>
    QueryGen.retagToRew
      (fun j => by
        by_cases hj : (j : ℕ) < m
        · rw [dif_pos hj, ProjCol.castComposite_kind]
          rfl
        · rw [dif_neg hj]
          rfl)
      (QueryGen.Proj
        (fun j : Fin (m + 1) =>
          if hj : (j : ℕ) < m then
            (ps ⟨j, hj⟩).castComposite
              (QueryGen.classical_kinds q hq.2) (hq.1 ⟨j, hj⟩)
          else
            ProjCol.provTerm (TermG.provIndex (Fin.last n)
              (ColKind.rewKinds_of_not_lt (lt_irrefl n))))
        (q.rewritingGen hq.2))
  | _, _, .Sel φ q, hq =>
    QueryGen.Sel (φ.castComposite (QueryGen.classical_kinds q hq.2) hq.1)
      (q.rewritingGen hq.2)
  | _, _, @QueryGen.Prod _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq =>
    QueryGen.retagToRew
      (fun j => by
        by_cases h₁ : (j : ℕ) < n₁
        · rw [dif_pos h₁]; rfl
        · rw [dif_neg h₁]
          by_cases h₂ : (j : ℕ) < n₁ + n₂
          · rw [dif_pos h₂]; rfl
          · rw [dif_neg h₂]; rfl)
      (QueryGen.Proj
        (fun j : Fin (n₁ + n₂ + 1) =>
          if h₁ : (j : ℕ) < n₁ then
            ProjCol.term (TermG.index
              (Fin.castAdd (n₂ + 1) (⟨j, Nat.lt_succ_of_lt h₁⟩ : Fin (n₁ + 1)))
              ((Fin.append_left _ _ _).trans (ColKind.rewKinds_lt h₁)))
          else if h₂ : (j : ℕ) < n₁ + n₂ then
            ProjCol.term (TermG.index
              (Fin.natAdd (n₁ + 1)
                (⟨(j : ℕ) - n₁, by omega⟩ : Fin (n₂ + 1)))
              ((Fin.append_right _ _ _).trans
                (ColKind.rewKinds_lt (by simp; omega))))
          else
            ProjCol.provTerm (TermG.mul
              (TermG.provIndex (Fin.castAdd (n₂ + 1) (Fin.last n₁))
                ((Fin.append_left _ _ _).trans
                  (ColKind.rewKinds_of_not_lt (lt_irrefl n₁))))
              (TermG.provIndex (Fin.natAdd (n₁ + 1) (Fin.last n₂))
                ((Fin.append_right _ _ _).trans
                  (ColKind.rewKinds_of_not_lt (lt_irrefl n₂))))))
        (QueryGen.Prod (q₁.rewritingGen hq.1) (q₂.rewritingGen hq.2)))
  | _, _, .Sum q₁ q₂, hq =>
    QueryGen.Sum (q₁.rewritingGen hq.1) (q₂.rewritingGen hq.2)
  | _, _, @QueryGen.Dedup _ n q, hq =>
    QueryGen.retagToRew
      (fun j => by
        refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
        · rw [Fin.append_left, ColKind.rewKinds_lt i.isLt]
          rfl
        · rw [Fin.append_right]
          rfl)
      (QueryGen.ProvSum (fun k : Fin n => k.castLE (Nat.le_succ n))
        (fun k => by
          rw [ColKind.rewKinds_lt k.isLt]
          exact fun hc => ColKind.noConfusion hc)
        (TermG.provIndex (Fin.last n)
          (ColKind.rewKinds_of_not_lt (lt_irrefl n)))
        (q.rewritingGen hq))
  | _, _, @QueryGen.Diff _ n q₁ q₂, hq =>
    -- unmatched branch: rows of `q₁` whose data part is absent from `q₂`
    let keyProj : (q : QueryGen (T ⊕ K) (n + 1) (ColKind.rewKinds n)) →
        QueryGen (T ⊕ K) n (ColKind.allReg n) := fun q =>
      QueryGen.Retag (fun _ => rfl)
        (QueryGen.Proj
          (fun j : Fin n =>
            ProjCol.term (TermG.index (j.castLE (Nat.le_succ n))
              (ColKind.rewKinds_lt j.isLt)))
          q)
    let q₁r := q₁.rewritingGen hq.1
    let q₂r := q₂.rewritingGen hq.2
    let survivors :=
      QueryGen.Dedup (QueryGen.Diff (keyProj q₁r) (keyProj q₂r))
    let joined₁ :=
      QueryGen.Sel
        (keyJoinCond
          (posL := fun k : Fin n => Fin.castAdd n (k.castLE (Nat.le_succ n)))
          (posR := fun k : Fin n => Fin.natAdd (n + 1) k)
          (fun k => (Fin.append_left _ _ _).trans
            (ColKind.rewKinds_lt k.isLt))
          (fun k => (Fin.append_right _ _ _).trans rfl))
        (QueryGen.Prod q₁r survivors)
    let branch₁ :=
      QueryGen.retagToRew
        (fun j => by
          by_cases hj : (j : ℕ) < n
          · rw [dif_pos hj]; rfl
          · rw [dif_neg hj]; rfl)
        (QueryGen.Proj
          (fun j : Fin (n + 1) =>
            if hj : (j : ℕ) < n then
              ProjCol.term (TermG.index
                (Fin.castAdd n (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (n + 1)))
                ((Fin.append_left _ _ _).trans (ColKind.rewKinds_lt hj)))
            else
              ProjCol.provTerm (TermG.provIndex
                (Fin.castAdd n (Fin.last n))
                ((Fin.append_left _ _ _).trans
                  (ColKind.rewKinds_of_not_lt (lt_irrefl n)))))
          joined₁)
    -- matched branch: `α ⊖ Σβ` against the per-key sum of `q₂`
    let sums₂ :=
      QueryGen.ProvSum (fun k : Fin n => k.castLE (Nat.le_succ n))
        (fun k => by
          rw [ColKind.rewKinds_lt k.isLt]
          exact fun hc => ColKind.noConfusion hc)
        (TermG.provIndex (Fin.last n)
          (ColKind.rewKinds_of_not_lt (lt_irrefl n)))
        q₂r
    let joined₂ :=
      QueryGen.Sel
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
        (QueryGen.Prod q₁r sums₂)
    let branch₂ :=
      QueryGen.retagToRew
        (fun j => by
          by_cases hj : (j : ℕ) < n
          · rw [dif_pos hj]; rfl
          · rw [dif_neg hj]; rfl)
        (QueryGen.Proj
          (fun j : Fin (n + 1) =>
            if hj : (j : ℕ) < n then
              ProjCol.term (TermG.index
                (Fin.castAdd (n + 1)
                  (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (n + 1)))
                ((Fin.append_left _ _ _).trans (ColKind.rewKinds_lt hj)))
            else
              ProjCol.provTerm (TermG.sub
                (TermG.provIndex (Fin.castAdd (n + 1) (Fin.last n))
                  ((Fin.append_left _ _ _).trans
                    (ColKind.rewKinds_of_not_lt (lt_irrefl n))))
                (TermG.provIndex
                  (Fin.natAdd (n + 1) (Fin.natAdd n (0 : Fin 1)))
                  ((Fin.append_right _ _ _).trans
                    (Fin.append_right _ _ _)))))
          joined₂)
    QueryGen.Sum branch₁ branch₂
termination_by structural _ _ q _ => q

/-! ## Stripping to the classical syntax

The classical fragment of the general syntax maps back to the classical
`Query` syntax; the correctness of the native rewriting is assembled
through this strip, the classical correctness theorem, and the
plain-semantics agreement of the two rewritten queries. -/

section Strip

/-- Strip a term over regular columns to a classical term (the
`provIndex` arm is unreachable on the classical fragment and mapped
harmlessly). -/
def TermG.strip {n : ℕ} {κ : Fin n → ColKind} : TermG T κ → Term T n
  | .const a => .const a
  | .index k _ => .index k
  | .provIndex k _ => .index k
  | .cmpAgg _ _ _ _ => .const 0
  | .add t₁ t₂ => .add t₁.strip t₂.strip
  | .sub t₁ t₂ => .sub t₁.strip t₂.strip
  | .mul t₁ t₂ => .mul t₁.strip t₂.strip

/-- Plain evaluation factors through the strip. -/
theorem TermG.strip_eval {n : ℕ} {κ : Fin n → ColKind} (t : TermG T κ)
    (u : Tuple T n) : t.strip.eval u = t.evalPlain u := by
  induction t with
  | const a => rfl
  | index k h => rfl
  | provIndex k h => rfl
  | cmpAgg k h op c ih => rfl
  | add t₁ t₂ ih₁ ih₂ => rw [TermG.strip, Term.eval, TermG.evalPlain, ih₁, ih₂]
  | sub t₁ t₂ ih₁ ih₂ => rw [TermG.strip, Term.eval, TermG.evalPlain, ih₁, ih₂]
  | mul t₁ t₂ ih₁ ih₂ => rw [TermG.strip, Term.eval, TermG.evalPlain, ih₁, ih₂]

/-- Strip an aggregate-atom-free predicate to a classical selection. -/
def GenPred.strip {n : ℕ} {κ : Fin n → ColKind} : GenPred T κ → Selection T n
  | .cmp .eq t₁ t₂ => .BT (.EQ t₁.strip t₂.strip)
  | .cmp .ne t₁ t₂ => .BT (.NE t₁.strip t₂.strip)
  | .cmp .le t₁ t₂ => .BT (.LE t₁.strip t₂.strip)
  | .cmp .lt t₁ t₂ => .BT (.LT t₁.strip t₂.strip)
  | .cmp .ge t₁ t₂ => .BT (.GE t₁.strip t₂.strip)
  | .cmp .gt t₁ t₂ => .BT (.GT t₁.strip t₂.strip)
  | .aggCmp _ _ _ _ => .True
  | .and φ ψ => .And φ.strip ψ.strip
  | .or φ ψ => .Or φ.strip ψ.strip
  | .not φ => .Not φ.strip

/-- Classical truth factors through the strip, on aggregate-atom-free
predicates. -/
theorem GenPred.strip_eval {n : ℕ} {κ : Fin n → ColKind} :
    ∀ (φ : GenPred T κ), φ.hasAggAtom = false → ∀ (u : Tuple T n),
      φ.strip.eval u ↔ φ.holdsPlain u
  | .cmp .eq t₁ t₂, _, u => by
    show t₁.strip.eval u = t₂.strip.eval u ↔ _
    rw [TermG.strip_eval, TermG.strip_eval]
    exact Iff.rfl
  | .cmp .ne t₁ t₂, _, u => by
    show t₁.strip.eval u ≠ t₂.strip.eval u ↔ _
    rw [TermG.strip_eval, TermG.strip_eval]
    exact Iff.rfl
  | .cmp .le t₁ t₂, _, u => by
    show t₁.strip.eval u ≤ t₂.strip.eval u ↔ _
    rw [TermG.strip_eval, TermG.strip_eval]
    exact Iff.rfl
  | .cmp .lt t₁ t₂, _, u => by
    show LT.lt (t₁.strip.eval u) (t₂.strip.eval u) ↔ _
    rw [TermG.strip_eval, TermG.strip_eval]
    exact Iff.rfl
  | .cmp .ge t₁ t₂, _, u => by
    show t₁.strip.eval u ≥ t₂.strip.eval u ↔ _
    rw [TermG.strip_eval, TermG.strip_eval]
    exact Iff.rfl
  | .cmp .gt t₁ t₂, _, u => by
    show GT.gt (t₁.strip.eval u) (t₂.strip.eval u) ↔ _
    rw [TermG.strip_eval, TermG.strip_eval]
    exact Iff.rfl
  | .aggCmp _ _ _ _, hφ, _ => Bool.noConfusion hφ
  | .and φ ψ, hφ, u =>
    and_congr
      (strip_eval φ (Bool.or_eq_false_iff.mp hφ).1 u)
      (strip_eval ψ (Bool.or_eq_false_iff.mp hφ).2 u)
  | .or φ ψ, hφ, u =>
    or_congr
      (strip_eval φ (Bool.or_eq_false_iff.mp hφ).1 u)
      (strip_eval ψ (Bool.or_eq_false_iff.mp hφ).2 u)
  | .not φ, hφ, u => not_congr (strip_eval φ hφ u)

/-- Strip a regular projection column to a classical term. -/
def ProjCol.strip {n : ℕ} {κ : Fin n → ColKind} : ProjCol T κ → Term T n
  | .term t => t.strip
  | .token _ _ => .const 0
  | .provTerm t => t.strip

/-- Strip a classical-fragment query to the classical syntax. -/
def QueryGen.strip :
    {n : ℕ} → {κ : Fin n → ColKind} → (q : QueryGen T n κ) →
    q.classical → Query T n
  | n, _, .Rel _ s, _ => .Rel n s
  | _, _, .Proj ps q, hq =>
    .Proj (fun j => (ps j).strip) (q.strip hq.2)
  | _, _, .Sel φ q, hq => .Sel φ.strip (q.strip hq.2)
  | _, _, @QueryGen.Prod _ n₁ n₂ _ _ q₁ q₂, hq =>
    @Query.Prod T n₁ n₂ (n₁ + n₂) rfl (q₁.strip hq.1) (q₂.strip hq.2)
  | _, _, .Sum q₁ q₂, hq => .Sum (q₁.strip hq.1) (q₂.strip hq.2)
  | _, _, .Dedup q, hq => .Dedup (q.strip hq)
  | _, _, .Diff q₁ q₂, hq => .Diff (q₁.strip hq.1) (q₂.strip hq.2)
  | _, _, .Gamma _ _ _ _, hq => False.elim hq
  | _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, .Retag _ _, hq => False.elim hq
  | _, _, .GammaTok _ _ _ _ _ _, hq => False.elim hq
termination_by structural _ _ q _ => q

/-- The strip is aggregation-free. -/
theorem QueryGen.strip_noAgg :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (hq : q.classical), (q.strip hq).noAgg
  | _, _, .Rel _ _, _ => trivial
  | _, _, .Proj _ q, hq => strip_noAgg q hq.2
  | _, _, .Sel _ q, hq => strip_noAgg q hq.2
  | _, _, .Prod q₁ q₂, hq => ⟨strip_noAgg q₁ hq.1, strip_noAgg q₂ hq.2⟩
  | _, _, .Sum q₁ q₂, hq => ⟨strip_noAgg q₁ hq.1, strip_noAgg q₂ hq.2⟩
  | _, _, .Dedup q, hq => strip_noAgg q hq
  | _, _, .Diff q₁ q₂, hq => ⟨strip_noAgg q₁ hq.1, strip_noAgg q₂ hq.2⟩
  | _, _, .Gamma _ _ _ _, hq => False.elim hq
  | _, _, .ProvSum _ _ _ _, hq => False.elim hq
  | _, _, .Retag _ _, hq => False.elim hq
  | _, _, .GammaTok _ _ _ _ _ _, hq => False.elim hq

end Strip

/-! ## Faithfulness of the strip -/

section StripFaithful

omit [ValueType T] [DecidableEq K] [HasAltLinearOrder K] in
/-- The collapsed data part of an invariant row is its classical
counterpart's data part. -/
theorem GenRow.Inv.plainTuple_eq {n : ℕ} {r : GenRow T K n}
    {p : AnnotatedTuple T K n} (h : GenRow.Inv r p) :
    GenRow.plainTuple r.fst = p.fst :=
  congrArg Prod.fst h.toAnnotated_eq

/-- **Row-wise faithfulness of the strip**: on the classical fragment,
the general evaluator produces rows satisfying the embedding invariant
against the classical annotated evaluation of the stripped query. -/
theorem QueryGen.strip_rel :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (hq : q.classical) (d : AnnotatedDatabase T K),
      Multiset.Rel GenRow.Inv (q.evaluateGen d)
        ((q.strip hq).evaluateAnnotated (q.strip_noAgg hq) d)
  | n, _, .Rel _ s, _, d => by
    show Multiset.Rel GenRow.Inv (match d.find n s with
      | none => (∅ : Multiset (GenRow T K n))
      | some rn => rn.map GenRow.ofAnnotated)
      ((Query.Rel n s).evaluateAnnotated trivial d)
    unfold Query.evaluateAnnotated
    cases d.find n s with
    | none => exact Multiset.Rel.zero
    | some rn => exact rel_inv_ofAnnotated rn
  | _, _, .Proj ps q, hq, d => by
    refine rel_map_of_rel (strip_rel q hq.2 d) (fun r p hr => ⟨?_, ?_, ?_⟩)
    · funext j
      show (ps j).eval r.fst = Sum.inl ((ps j).strip.eval p.fst)
      have hkind := hq.1 j
      cases hp : ps j with
      | term t =>
        show Sum.inl (t.eval r.fst) = Sum.inl (t.strip.eval p.fst)
        rw [TermG.strip_eval, TermG.eval_eq_evalPlain t r.fst,
          hr.plainTuple_eq]
      | token k hk => rw [hp] at hkind; exact ColKind.noConfusion hkind
      | provTerm t => rw [hp] at hkind; exact ColKind.noConfusion hkind
    · exact (GenAnn.finalize_cash _ _ _ Multiset.inter_le_left).trans hr.2.1
    · show r.snd.pending ∩ _ = 0
      rw [hr.2.2]
      exact Multiset.zero_inter _
  | _, _, .Sel φ q, hq, d => by
    show Multiset.Rel _
      (if φ.hasAggAtom then _ else
        Multiset.filter _ (q.evaluateGen d)) _
    rw [if_neg (by rw [hq.1]; exact Bool.false_ne_true)]
    refine rel_filter_of_iff (strip_rel q hq.2 d) (fun r p hr => ?_)
    rw [GenPred.holds_iff_holdsPlain, hr.plainTuple_eq]
    exact (GenPred.strip_eval φ hq.1 p.fst).symm
  | _, _, @QueryGen.Prod _ n₁ n₂ _ _ q₁ q₂, hq, d => by
    refine rel_map_of_rel
      (rel_product (strip_rel q₁ hq.1 d) (strip_rel q₂ hq.2 d)) ?_
    rintro ⟨x, y⟩ ⟨p, p'⟩ ⟨hx, hy⟩
    refine ⟨?_, ?_, ?_⟩
    · funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · show Fin.append x.fst y.fst (Fin.castAdd n₂ i) = _
        rw [Fin.append_left, hx.1]
        show Sum.inl (p.fst i)
          = Sum.inl (Fin.append p.fst p'.fst (Fin.castAdd n₂ i))
        rw [Fin.append_left]
      · show Fin.append x.fst y.fst (Fin.natAdd n₁ j) = _
        rw [Fin.append_right, hy.1]
        show Sum.inl (p'.fst j)
          = Sum.inl (Fin.append p.fst p'.fst (Fin.natAdd n₁ j))
        rw [Fin.append_right]
    · show GenAnn.finalize ⟨x.snd.base * y.snd.base,
        x.snd.pending + y.snd.pending⟩ = p.snd * p'.snd
      rw [GenAnn.finalize_prod, hx.2.1, hy.2.1]
    · show x.snd.pending + y.snd.pending = 0
      rw [hx.2.2, hy.2.2]
      rfl
  | _, _, .Sum q₁ q₂, hq, d =>
    Multiset.Rel.add (strip_rel q₁ hq.1 d) (strip_rel q₂ hq.2 d)
  | _, _, .Dedup q, hq, d => by
    show Multiset.Rel _ ((Multiset.ofList (groupByKey
      ((q.evaluateGen d).map GenRow.toAnnotated)).val).map
        GenRow.ofAnnotated) _
    rw [show (q.evaluateGen d).map GenRow.toAnnotated
        = (q.strip hq).evaluateAnnotated (q.strip_noAgg hq) d from
      (map_eq_of_rel (strip_rel q hq d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    exact rel_inv_ofAnnotated _
  | _, _, .Diff q₁ q₂, hq, d => by
    show Multiset.Rel _
      (((((q₁.evaluateGen d).map GenRow.toAnnotated)).map _).map
        GenRow.ofAnnotated) _
    rw [show (q₁.evaluateGen d).map GenRow.toAnnotated
        = (q₁.strip hq.1).evaluateAnnotated (q₁.strip_noAgg hq.1) d from
      (map_eq_of_rel (strip_rel q₁ hq.1 d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [show (q₂.evaluateGen d).map GenRow.toAnnotated
        = (q₂.strip hq.2).evaluateAnnotated (q₂.strip_noAgg hq.2) d from
      (map_eq_of_rel (strip_rel q₂ hq.2 d)
        (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)]
    rw [Multiset.map_map]
    refine rel_map_of_forall (fun p _ => ?_)
    obtain ⟨u, α⟩ := p
    exact ⟨rfl, GenAnn.finalize_of_pending_zero _, rfl⟩
  | _, _, .Gamma _ _ _ _, hq, _ => False.elim hq
  | _, _, .ProvSum _ _ _ _, hq, _ => False.elim hq
  | _, _, .Retag _ _, hq, _ => False.elim hq
  | _, _, .GammaTok _ _ _ _ _ _, hq, _ => False.elim hq

/-- **Faithfulness of the strip**: on the classical fragment the general
annotated evaluator computes the classical annotated semantics of the
stripped query. -/
theorem QueryGen.strip_bridge {n : ℕ} {κ : Fin n → ColKind}
    (q : QueryGen T n κ) (hq : q.classical) (d : AnnotatedDatabase T K) :
    q.evaluateAnnotatedGen d
      = (q.strip hq).evaluateAnnotated (q.strip_noAgg hq) d := by
  unfold QueryGen.evaluateAnnotatedGen
  exact (map_eq_of_rel (QueryGen.strip_rel q hq d)
    (fun r p hr => hr.toAnnotated_eq)).trans (Multiset.map_id _)

end StripFaithful

/-! ## Plain-semantics agreement of the two rewritten queries -/

section PlainAgreement

omit [DecidableEq K] in
/-- The composite cast of a term agrees with the classical cast of its
strip. -/
theorem TermG.castComposite_evalPlain {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) (t : TermG T κ)
    (u : Tuple (T ⊕ K) (n + 1)) :
    (t.castComposite hκ (K := K)).evalPlain u
      = (t.strip.castToAnnotatedTuple).eval u := by
  induction t with
  | const a => rfl
  | index k h => rfl
  | provIndex k h =>
    exact absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | cmpAgg k h op c ih =>
    exact absurd ((hκ k).symm.trans h) (fun hc => ColKind.noConfusion hc)
  | add t₁ t₂ ih₁ ih₂ =>
    show (t₁.castComposite hκ).evalPlain u + (t₂.castComposite hκ).evalPlain u
      = _
    rw [ih₁, ih₂]
    rfl
  | sub t₁ t₂ ih₁ ih₂ =>
    show HSub.hSub ((t₁.castComposite hκ).evalPlain u)
        ((t₂.castComposite hκ).evalPlain u)
      = _
    rw [ih₁, ih₂]
    rfl
  | mul t₁ t₂ ih₁ ih₂ =>
    show (t₁.castComposite hκ).evalPlain u * (t₂.castComposite hκ).evalPlain u
      = _
    rw [ih₁, ih₂]
    rfl

omit [DecidableEq K] in
/-- The composite cast of a predicate agrees with the classical cast of
its strip. -/
theorem GenPred.castComposite_holdsPlain {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    ∀ (φ : GenPred T κ) (hφ : φ.hasAggAtom = false)
      (u : Tuple (T ⊕ K) (n + 1)),
      (φ.castComposite hκ hφ (K := K)).holdsPlain u
        ↔ (φ.strip.castToAnnotatedTuple).eval u
  | .cmp .eq t₁ t₂, _, u => by
    show (t₁.castComposite hκ).evalPlain u = (t₂.castComposite hκ).evalPlain u
      ↔ _
    rw [TermG.castComposite_evalPlain, TermG.castComposite_evalPlain]
    exact Iff.rfl
  | .cmp .ne t₁ t₂, _, u => by
    show (t₁.castComposite hκ).evalPlain u ≠ (t₂.castComposite hκ).evalPlain u
      ↔ _
    rw [TermG.castComposite_evalPlain, TermG.castComposite_evalPlain]
    exact Iff.rfl
  | .cmp .le t₁ t₂, _, u => by
    show (t₁.castComposite hκ).evalPlain u ≤ (t₂.castComposite hκ).evalPlain u
      ↔ _
    rw [TermG.castComposite_evalPlain, TermG.castComposite_evalPlain]
    exact Iff.rfl
  | .cmp .lt t₁ t₂, _, u => by
    show LT.lt ((t₁.castComposite hκ).evalPlain u)
        ((t₂.castComposite hκ).evalPlain u)
      ↔ _
    rw [TermG.castComposite_evalPlain, TermG.castComposite_evalPlain]
    exact Iff.rfl
  | .cmp .ge t₁ t₂, _, u => by
    show (t₁.castComposite hκ).evalPlain u ≥ (t₂.castComposite hκ).evalPlain u
      ↔ _
    rw [TermG.castComposite_evalPlain, TermG.castComposite_evalPlain]
    exact Iff.rfl
  | .cmp .gt t₁ t₂, _, u => by
    show GT.gt ((t₁.castComposite hκ).evalPlain u)
        ((t₂.castComposite hκ).evalPlain u)
      ↔ _
    rw [TermG.castComposite_evalPlain, TermG.castComposite_evalPlain]
    exact Iff.rfl
  | .aggCmp _ _ _ _, hφ, _ => Bool.noConfusion hφ
  | .and φ ψ, hφ, u =>
    and_congr
      (castComposite_holdsPlain hκ φ (Bool.or_eq_false_iff.mp hφ).1 u)
      (castComposite_holdsPlain hκ ψ (Bool.or_eq_false_iff.mp hφ).2 u)
  | .or φ ψ, hφ, u =>
    or_congr
      (castComposite_holdsPlain hκ φ (Bool.or_eq_false_iff.mp hφ).1 u)
      (castComposite_holdsPlain hκ ψ (Bool.or_eq_false_iff.mp hφ).2 u)
  | .not φ, hφ, u => not_congr (castComposite_holdsPlain hκ φ hφ u)

omit [DecidableEq K] in
/-- The composite cast of a projection column agrees with the classical
cast of its strip. -/
theorem ProjCol.castComposite_evalPlain {n : ℕ} {κ : Fin n → ColKind}
    (hκ : ∀ k, κ k = ColKind.reg) :
    ∀ (p : ProjCol T κ) (hp : p.kind = ColKind.reg)
      (u : Tuple (T ⊕ K) (n + 1)),
      (p.castComposite hκ hp (K := K)).evalPlain u
        = (p.strip.castToAnnotatedTuple).eval u
  | .term t, _, u => TermG.castComposite_evalPlain hκ t u
  | .token _ _, hp, _ => ColKind.noConfusion hp
  | .provTerm _, hp, _ => ColKind.noConfusion hp

theorem Relation.cast_filter {T' : Type} {n m : ℕ} (hn : n = m)
    (p : Tuple T' m → Prop) [DecidablePred p] (r : Relation T' n) :
    (r.cast hn).filter p
      = Relation.cast hn (r.filter (fun t => p (Tuple.cast hn t))) := by
  subst hn
  rfl

theorem GenPred.holdsPlain_foldr_and {T' : Type} [ValueType T'] {N : ℕ}
    {κ' : Fin N → ColKind} {α : Type} (l : List α)
    (f : α → GenPred T' κ') (base : GenPred T' κ') (u : Tuple T' N) :
    (((l.map f).foldr GenPred.and base).holdsPlain u)
      ↔ (∀ x ∈ l, (f x).holdsPlain u) ∧ base.holdsPlain u := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    show (f hd).holdsPlain u ∧ _ ↔ _
    rw [ih]
    constructor
    · rintro ⟨hhd, htl, hb⟩
      exact ⟨fun x hx => (List.mem_cons.mp hx).elim (fun he => he ▸ hhd)
        (htl x), hb⟩
    · rintro ⟨hall, hb⟩
      exact ⟨hall hd (List.mem_cons_self), fun x hx => hall x (List.mem_cons_of_mem hd hx), hb⟩

theorem keyJoinCond_holdsPlain {T' : Type} [ValueType T'] {n m : ℕ}
    {κ' : Fin m → ColKind} (posL posR : Fin n → Fin m)
    (hL : ∀ k, κ' (posL k) = ColKind.reg)
    (hR : ∀ k, κ' (posR k) = ColKind.reg) (u : Tuple T' m) :
    (keyJoinCond posL posR hL hR).holdsPlain u
      ↔ ∀ k, u (posL k) = u (posR k) := by
  unfold keyJoinCond
  rw [GenPred.holdsPlain_foldr_and]
  constructor
  · rintro ⟨hall, -⟩ k
    exact hall k (List.mem_finRange k)
  · intro h
    exact ⟨fun k _ => h k, rfl⟩

theorem Tuple.cast_coord {T' : Type} {n m : ℕ} (heq : n = m)
    (t : Tuple T' n) (k : Fin m) :
    Tuple.cast heq t k = t ⟨(k : ℕ), by omega⟩ := by
  subst heq
  rfl

/-- **Plain-semantics agreement**: the native rewriting and the classical
rewriting of the stripped query evaluate identically on any composite
database. -/
theorem QueryGen.rewritingGen_plain :
    ∀ {n : ℕ} {κ : Fin n → ColKind} (q : QueryGen T n κ)
      (hq : q.classical) (D : Database (T ⊕ K)),
      (q.rewritingGen hq).evaluatePlain D
        = ((q.strip hq).rewriting (q.strip_noAgg hq)).evaluate D
  | n, _, .Rel _ s, _, D => by
    show (QueryGen.Rel (T := T ⊕ K) (n + 1) s).evaluatePlain D
      = (Query.Rel (T := T ⊕ K) (n + 1) s).evaluate D
    unfold QueryGen.evaluatePlain Query.evaluate
    cases D.find (n + 1) s <;> rfl
  | _, _, @QueryGen.Proj _ n m κ ps q, hq, D => by
    unfold QueryGen.rewritingGen QueryGen.retagToRew QueryGen.strip
    simp only [QueryGen.evaluatePlain]
    unfold Query.rewriting Query.evaluate
    rw [rewritingGen_plain q hq.2 D]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    funext j
    dsimp only
    by_cases hj : (j : ℕ) < m
    · rw [dif_pos hj, dif_pos hj]
      exact ProjCol.castComposite_evalPlain _ _ _ u
    · rw [dif_neg hj, dif_neg hj]
      rfl
  | _, _, .Sel φ q, hq, D => by
    unfold QueryGen.rewritingGen QueryGen.strip
    simp only [QueryGen.evaluatePlain]
    unfold Query.rewriting Query.evaluate
    rw [rewritingGen_plain q hq.2 D]
    letI : DecidablePred (Selection.eval (φ.strip.castToAnnotatedTuple
        (K := K))) := (φ.strip.castToAnnotatedTuple).evalDecidable
    exact Multiset.filter_congr
      (fun u _ => GenPred.castComposite_holdsPlain
        (QueryGen.classical_kinds q hq.2) φ hq.1 u)
  | _, _, @QueryGen.Prod _ n₁ n₂ κ₁ κ₂ q₁ q₂, hq, D => by
    unfold QueryGen.rewritingGen QueryGen.retagToRew QueryGen.strip
    simp only [QueryGen.evaluatePlain]
    unfold Query.rewriting
    simp only [Query.evaluate]
    rw [rewritingGen_plain q₁ hq.1 D, rewritingGen_plain q₂ hq.2 D,
      Query.rewriting_valid_prod1]
    refine Multiset.map_congr rfl (fun t _ => ?_)
    funext j
    by_cases h₁ : (j : ℕ) < n₁
    · rw [dif_pos h₁, if_pos h₁]
      simp only [ProjCol.evalPlain, TermG.evalPlain, Term.eval]
      rw [Tuple.cast_coord]
      rfl
    · rw [dif_neg h₁, if_neg h₁]
      by_cases h₂ : (j : ℕ) < n₁ + n₂
      · rw [dif_pos h₂, if_pos h₂]
        simp only [ProjCol.evalPlain, TermG.evalPlain, Term.eval]
        rw [Tuple.cast_coord]
        refine congrArg t (Fin.ext ?_)
        show n₁ + 1 + ((j : ℕ) - n₁) = _
        simp only [Fin.ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [dif_neg h₂, if_neg h₂]
        simp only [ProjCol.evalPlain, TermG.evalPlain, Term.eval]
        rw [Tuple.cast_coord, Tuple.cast_coord]
        refine congrArg₂ (· * ·) (congrArg t (Fin.ext ?_))
          (congrArg t (Fin.ext ?_))
        · show (n₁ : ℕ) = _
          simp only [Fin.ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
        · show n₁ + 1 + n₂ = _
          simp only [Fin.ofNat]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
  | _, _, .Sum q₁ q₂, hq, D => by
    unfold QueryGen.rewritingGen QueryGen.strip
    simp only [QueryGen.evaluatePlain]
    unfold Query.rewriting Query.evaluate
    rw [rewritingGen_plain q₁ hq.1 D, rewritingGen_plain q₂ hq.2 D]
  | _, _, @QueryGen.Dedup _ n q, hq, D => by
    unfold QueryGen.rewritingGen QueryGen.retagToRew QueryGen.strip
    simp only [QueryGen.evaluatePlain]
    unfold Query.rewriting
    simp only [Query.evaluate]
    rw [rewritingGen_plain q hq D]
    refine Multiset.map_congr ?_ (fun g _ => ?_)
    · congr 1
    · funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right,
          Subsingleton.elim j (0 : Fin 1)]
        show Multiset.fold addFn 0 _ = Multiset.fold addFn 0 _
        refine congrArg _ (Multiset.map_congr ?_ (fun u _ => rfl))
        congr 1
  | _, _, @QueryGen.Diff _ n q₁ q₂, hq, D => by
    unfold QueryGen.rewritingGen QueryGen.retagToRew QueryGen.strip
    simp only [QueryGen.evaluatePlain]
    unfold Query.rewriting
    simp only [Query.evaluate]
    rw [rewritingGen_plain q₁ hq.1 D, rewritingGen_plain q₂ hq.2 D]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [show (fun x (j : Fin n) => (ProjCol.term (TermG.index
          (Fin.castLE (Nat.le_succ n) j)
          (ColKind.rewKinds_lt j.isLt))).evalPlain x)
        = (fun x (k : Fin n) =>
            (#(Fin.castLE (Nat.le_succ n) k)).eval (T := T ⊕ K) x) from
        funext fun x => funext fun j => rfl]
      rw [Relation.cast_filter, Relation.cast_eq_map, Multiset.map_map]
      haveI : NeZero (2 * n + 1) := ⟨by omega⟩
      haveI : ∀ {m : ℕ} (φ : Selection (T ⊕ K) m) (h : n + 1 + n = m),
          DecidablePred fun t : Tuple (T ⊕ K) (n + 1 + n) =>
            φ.eval (Tuple.cast h t) :=
        fun φ h t => φ.evalDecidable (Tuple.cast h t)
      refine Multiset.map_congr (Eq.trans (Multiset.filter_congr (fun t _ =>
        Iff.trans (keyJoinCond_holdsPlain _ _ _ _ t)
          (Iff.trans (forall_congr' (fun k =>
            iff_of_eq (congrArg₂ (· = ·)
              ((Tuple.cast_coord (by omega : n + 1 + n = 2 * n + 1) t
                  (Fin.ofNat (2 * n + 1) (k : ℕ))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_castAdd, Fin.val_castLE]
                  rw [Nat.mod_eq_of_lt (by omega)])))).symm
              ((Tuple.cast_coord (by omega : n + 1 + n = 2 * n + 1) t
                  (Fin.ofNat (2 * n + 1) ((k : ℕ) + n + 1))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_natAdd]
                  rw [Nat.mod_eq_of_lt (by omega)]
                  omega)))).symm)))
            (Query.rewriting_valid_joinCond_eval
              (Tuple.cast (by omega : n + 1 + n = 2 * n + 1) t)).symm)))
        ?_) (fun t _ => ?_)
      · congr 1
      · funext j
        by_cases hj : (j : ℕ) < n
        · rw [dif_pos hj]
          simp only [ProjCol.evalPlain, TermG.evalPlain, Term.eval,
            Function.comp_apply]
          rw [Tuple.cast_coord]
          rfl
        · rw [dif_neg hj]
          simp only [ProjCol.evalPlain, TermG.evalPlain, Term.eval,
            Function.comp_apply]
          rw [Tuple.cast_coord]
          exact congrArg t (Fin.ext (by
            simp only [Fin.val_castAdd, Fin.val_castLE, Fin.val_last]
            omega))
    · rw [show (fun (x : Tuple (T ⊕ K) (n + 1)) (k : Fin n) =>
            x (Fin.castLE (Nat.le_succ n) k))
          = (fun t (k : Fin n) =>
              (#(Fin.castLE (Nat.le_succ n) k)).eval (T := T ⊕ K) t) from
        funext fun x => funext fun k => rfl]
      rw [Relation.cast_filter, Relation.cast_eq_map, Multiset.map_map]
      haveI : NeZero (2 * n + 2) := ⟨by omega⟩
      haveI : ∀ {m : ℕ} (φ : Selection (T ⊕ K) m) (h : n + 1 + (n + 1) = m),
          DecidablePred fun t : Tuple (T ⊕ K) (n + 1 + (n + 1)) =>
            φ.eval (Tuple.cast h t) :=
        fun φ h t => φ.evalDecidable (Tuple.cast h t)
      refine Multiset.map_congr (Eq.trans (Multiset.filter_congr (fun t _ =>
        Iff.trans (keyJoinCond_holdsPlain _ _ _ _ t)
          (Iff.trans (forall_congr' (fun k =>
            iff_of_eq (congrArg₂ (· = ·)
              ((Tuple.cast_coord
                  (by omega : n + 1 + (n + 1) = 2 * n + 2) t
                  (Fin.ofNat (2 * n + 2) (k : ℕ))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_castAdd, Fin.val_castLE]
                  rw [Nat.mod_eq_of_lt (by omega)])))).symm
              ((Tuple.cast_coord
                  (by omega : n + 1 + (n + 1) = 2 * n + 2) t
                  (Fin.ofNat (2 * n + 2) ((k : ℕ) + n + 1))).trans
                (congrArg t (Fin.ext (by
                  simp only [Fin.ofNat, Fin.val_natAdd, Fin.val_castAdd]
                  rw [Nat.mod_eq_of_lt (by omega)]
                  omega)))).symm)))
            (Query.rewriting_valid_joinCond_eval
              (Tuple.cast
                (by omega : n + 1 + (n + 1) = 2 * n + 2) t)).symm)))
        ?_) (fun t _ => ?_)
      · congr 1
        refine congrArg (HMul.hMul _) ?_
        refine Multiset.map_congr ?_ (fun g _ => ?_)
        · congr 1
        · funext k
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k
          · rw [Fin.append_left, Fin.append_left]
          · rw [Fin.append_right, Fin.append_right,
              Subsingleton.elim j (0 : Fin 1)]
            show Multiset.fold addFn 0 _ = Multiset.fold addFn 0 _
            refine congrArg _ (Multiset.map_congr ?_ (fun u _ => rfl))
            congr 1
      · funext j
        by_cases hj : (j : ℕ) < n
        · rw [dif_pos hj]
          simp only [Function.comp_apply]
          rw [if_pos hj]
          simp only [ProjCol.evalPlain, TermG.evalPlain, Term.eval]
          rw [Tuple.cast_coord]
          rfl
        · rw [dif_neg hj]
          simp only [Function.comp_apply]
          rw [if_neg hj]
          simp only [ProjCol.evalPlain, TermG.evalPlain, Term.eval]
          rw [Tuple.cast_coord, Tuple.cast_coord]
          refine congrArg₂ _
            (congrArg t (Fin.ext (by
              simp only [Fin.ofNat, Fin.val_castAdd, Fin.val_last]
              rw [Nat.mod_eq_of_lt (by omega)])))
            (congrArg t (Fin.ext (by
              simp only [Fin.val_natAdd, Fin.val_last, Fin.val_zero]
              omega)))
  | _, _, .Gamma _ _ _ _, hq, _ => False.elim hq
  | _, _, .ProvSum _ _ _ _, hq, _ => False.elim hq
  | _, _, .Retag _ _, hq, _ => False.elim hq
  | _, _, .GammaTok _ _ _ _ _ _, hq, _ => False.elim hq

end PlainAgreement

/-! ## Rewriting correctness -/

section Correctness

/-- **Correctness of the native rewriting.** For a classical query in the
general syntax, evaluating the annotated semantics and folding the result
into composite `T ⊕ K` tuples agrees with evaluating the rewritten query
under the plain semantics over the composite database. This is the
general-syntax form of the classical rewriting correctness. -/
theorem QueryGen.rewritingGen_valid {n : ℕ} {κ : Fin n → ColKind}
    (q : QueryGen T n κ) (hq : q.classical) (d : AnnotatedDatabase T K) :
    (q.evaluateAnnotatedGen d).toComposite
      = (q.rewritingGen hq).evaluatePlain d.toComposite := by
  rw [QueryGen.strip_bridge q hq d,
    Query.rewriting_valid (q.strip hq) (q.strip_noAgg hq) d,
    QueryGen.rewritingGen_plain q hq d.toComposite]

end Correctness
