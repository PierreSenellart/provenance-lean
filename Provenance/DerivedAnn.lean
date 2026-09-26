/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.Derived
import Provenance.HavingQueryCorrectness

/-!
# Annotations of the derived operators

The annotations of the operators of `Provenance.Derived` follow from their
definitions, being the annotations the basis gives the query each one
abbreviates. Some are worth computing, because they are what the choice of
definition is answerable for.

Intersection is the first. `q₁ ∩ q₂` annotates a shared tuple by
`(⊕ α) ⊗ (⊕ β)`, the sums ranging over its copies on each side: the
provenance of a conjunction of the two memberships. The other definition
that comes to mind, `ε(q₁ - (q₁ - q₂))`, has the same rows and the same
support over `𝔹`, and annotates them by a difference of differences
instead.
-/

variable {T : Type}
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] {n : ℕ}

namespace AggQuery

section Core

variable [ValueType T]

/-- The `⊕`-sum of the annotations a query gives one tuple: what
duplicate elimination accumulates on it. -/
def annSum (q : AggQuery T n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (u : Tuple T n) : K :=
  (Multiset.map Prod.snd (Multiset.filter
    (fun p : AnnotatedTuple T K n => p.1 = u) (q.evaluateAnnotated d))).sum

/-- The `⊕`-sum of the annotations one tuple carries in an annotated
relation. -/
def _root_.AnnotatedRelation.annSum (r : AnnotatedRelation T K n)
    (u : Tuple T n) : K :=
  (Multiset.map Prod.snd
    (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u) r)).sum

theorem annSum_eq (q : AggQuery T n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) (u : Tuple T n) :
    annSum q d u = (q.evaluateAnnotated d).annSum u := rfl

/-- **Difference subtracts, from each row of the left arm, the `⊕`-sum of
the annotations its tuple carries on the right.** No row is removed: a row
whose tuple is matched is kept with a monus, which is what ProvSQL
emits. -/
theorem evaluate_Diff (q₁ q₂ : AggQuery T n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) :
    (AggQuery.Diff q₁ q₂).evaluate d
      = (q₁.evaluateAnnotated d).map (fun p =>
          GenRow.ofAnnotated
            (p.1, p.2 - (q₂.evaluateAnnotated d).annSum p.1)) := by
  show (Multiset.map _ ((q₁.evaluate d).map GenRow.toAnnotated)).map
      GenRow.ofAnnotated = _
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  show GenRow.ofAnnotated (p.1, p.2 - _) = _
  rw [groupByKey_find_eq_filter_sum]
  rfl

/-- **Duplicate elimination keeps one copy of each tuple, carrying the
`⊕`-sum of its copies' annotations.** -/
theorem evaluate_Dedup (q : AggQuery T n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) :
    (AggQuery.Dedup q).evaluate d
      = ((q.evaluateAnnotated d).map Prod.fst).dedup.map
          (fun u => GenRow.ofAnnotated (u, annSum q d u)) := by
  show (Multiset.ofList (groupByKey ((q.evaluate d).map GenRow.toAnnotated)).val).map
      GenRow.ofAnnotated = _
  rw [groupByKey_eq_dedup_map, Multiset.map_map]
  rfl

private theorem product_map_map {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (A : Multiset α) (B : Multiset β) :
    (A.map f).product (B.map g) = (A.product B).map (fun p => (f p.1, g p.2)) := by
  induction A using Multiset.induction_on with
  | empty => rfl
  | cons a A ih =>
    rw [Multiset.map_cons,
      show ((f a) ::ₘ A.map f).product (B.map g)
        = ((f a) ::ₘ A.map f) ×ˢ (B.map g) from rfl, Multiset.cons_product,
      show A.map f ×ˢ B.map g = (A.map f).product (B.map g) from rfl, ih,
      show (a ::ₘ A).product B = (a ::ₘ A) ×ˢ B from rfl, Multiset.cons_product,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl

/-- **A projection carries the finalized annotation across.** What it
cashes of the pending factors, for the groups whose token columns it
drops, it takes out of the pending part and multiplies into the concrete
one, so the two together are unchanged. -/
theorem evaluateAnnotated_Proj {m : ℕ} {κ : Fin n → ColKind}
    (ps : Tuple (ProjCol T κ) m) (q : AggQuery T n κ)
    (d : AnnotatedDatabase T K) :
    (AggQuery.Proj ps q).evaluateAnnotated d
      = (q.evaluate d).map (fun r =>
          ((fun j => AggValue.collapseSum ((ps j).eval r.fst), r.snd.finalize)
            : AnnotatedTuple T K m)) := by
  show ((AggQuery.Proj ps q).evaluate d).map GenRow.toAnnotated = _
  show (Multiset.map _ (q.evaluate d)).map GenRow.toAnnotated = _
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun r _ => ?_)
  refine Prod.ext rfl ?_
  show r.snd.base * _ * _ = r.snd.finalize
  unfold GenAnn.finalize
  rw [mul_assoc, ← Multiset.prod_add, ← Multiset.map_add,
    tsub_add_cancel_of_le (Multiset.inter_le_left)]

/-- A selection without an aggregate atom filters. -/
theorem evaluate_Sel_of_noAgg {κ : Fin n → ColKind} (φ : GenPred T κ)
    (hφ : φ.hasAggAtom = false) (q : AggQuery T n κ)
    (d : AnnotatedDatabase T K) :
    (AggQuery.Sel φ q).evaluate d
      = (q.evaluate d).filter (fun r => φ.holds r.fst) := by
  show (if φ.hasAggAtom = true then _ else _) = _
  rw [hφ]
  rfl

/-- A product pairs the rows, multiplying the concrete annotations and
putting the pending factors side by side. -/
theorem evaluate_Prod {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQuery T n₁ κ₁) (q₂ : AggQuery T n₂ κ₂)
    (d : AnnotatedDatabase T K) :
    (AggQuery.Prod q₁ q₂).evaluate d
      = ((q₁.evaluate d).product (q₂.evaluate d)).map (fun xy =>
          (⟨Fin.append xy.1.fst xy.2.fst,
            ⟨xy.1.snd.base * xy.2.snd.base,
              xy.1.snd.pending + xy.2.snd.pending⟩⟩ :
            GenRow T K (n₁ + n₂))) := rfl

/-- **What intersection annotates**: a shared tuple by the product of the
two `⊕`-sums, one per arm – the provenance of a conjunction of the two
memberships. -/
theorem evaluateAnnotated_inter (q₁ q₂ : AggQuery T n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) :
    (inter q₁ q₂).evaluateAnnotated d
      = (Multiset.filter
          (fun u => u ∈ ((q₂.evaluateAnnotated d).map Prod.fst).dedup)
          ((q₁.evaluateAnnotated d).map Prod.fst).dedup).map
          (fun u => ((u, annSum q₁ d u * annSum q₂ d u) : AnnotatedTuple T K n)) := by
  set A₁ := ((q₁.evaluateAnnotated d).map Prod.fst).dedup with hA₁
  set A₂ := ((q₂.evaluateAnnotated d).map Prod.fst).dedup with hA₂
  show ((inter q₁ q₂).evaluate d).map GenRow.toAnnotated = _
  unfold inter
  rw [AggQuery.evaluate_castKind]
  rw [show (AggQuery.Proj (fstBlock n) (AggQuery.Sel (interCond n)
        ((AggQuery.Prod (AggQuery.Dedup q₁) (AggQuery.Dedup q₂)).castKind
          (append_allReg n n)))).evaluate d
      = ((AggQuery.Sel (interCond n)
          ((AggQuery.Prod (AggQuery.Dedup q₁) (AggQuery.Dedup q₂)).castKind
            (append_allReg n n))).evaluate d).map (fun r =>
        (⟨fun j => (fstBlock n j).eval r.fst,
          ⟨r.snd.base * ((r.snd.pending -
              r.snd.pending ∩ tokenLists (fun j => (fstBlock n j).eval r.fst)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod,
            r.snd.pending ∩ tokenLists (fun j => (fstBlock n j).eval r.fst)⟩⟩ :
          GenRow T K n)) from rfl,
    evaluate_Sel_of_noAgg _ (interCond_hasAggAtom n), AggQuery.evaluate_castKind,
    evaluate_Prod, evaluate_Dedup, evaluate_Dedup, product_map_map,
    Multiset.map_map, Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp_def]
  rw [Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp_def]
  rw [Multiset.filter_congr (fun p (_ : p ∈ A₁.product A₂) =>
    show (interCond n).holds
        (Fin.append (GenRow.ofAnnotated (p.1, annSum q₁ d p.1)).1
          (GenRow.ofAnnotated (p.2, annSum q₂ d p.2)).1) ↔ p.1 = p.2 from by
      rw [interCond, keyJoinCond_holds]
      constructor
      · intro h
        funext k
        have hk := h k
        unfold GenRow.plainTuple at hk
        rwa [Fin.append_left, Fin.append_right] at hk
      · intro hp k
        show GenRow.plainTuple _ _ = GenRow.plainTuple _ _
        unfold GenRow.plainTuple
        rw [Fin.append_left, Fin.append_right]
        exact congrFun hp k)]
  rw [filter_product_diag _ _ (Multiset.nodup_dedup _) _ _ (fun _ _ => Iff.rfl),
    Multiset.map_map]
  refine Multiset.map_congr rfl (fun u _ => ?_)
  show GenRow.toAnnotated (⟨fun j => (fstBlock n j).eval _, _⟩ : GenRow T K n) = _
  refine Prod.ext ?_ ?_
  · funext j
    show AggValue.collapseSum
        ((Fin.append (GenRow.ofAnnotated (u, annSum q₁ d u)).1
          (GenRow.ofAnnotated (u, annSum q₂ d u)).1 :
            Tuple (GenValue T K) (n + n)) (Fin.castAdd n j)) = u j
    rw [Fin.append_left]
    rfl
  · show GenAnn.finalize _ = _
    simp [GenAnn.finalize, GenRow.ofAnnotated]

end Core

/-! ## Outer joins -/

section Outer

variable [ValueTypeNull T] {n₁ n₂ : ℕ}

/-- **The `⊕`-sum of the annotations of a row's matches**, over the matches
of *every copy* of its tuple – the difference the padded copy goes through
is per tuple and syntactic. -/
def matchAnn (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂))
    (d : AnnotatedDatabase T K) (u : Tuple T n₁) : K :=
  (Multiset.map Prod.snd (Multiset.filter
    (fun p : AnnotatedTuple T K (n₁ + n₂) =>
      (fun j => p.1 (Fin.castAdd n₂ j) : Tuple T n₁) = u)
    ((innerJoin φ q₁ q₂).evaluateAnnotated d))).sum

/-- The right arm of the difference in a left outer join carries, on a
tuple, the `⊕`-sum of the annotations of its matches. -/
theorem annSum_firstCols (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂))
    (d : AnnotatedDatabase T K) (u : Tuple T n₁) :
    (((AggQuery.Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun i => firstCols_kind n₁ n₂ i)).evaluateAnnotated d).annSum u
      = matchAnn φ q₁ q₂ d u := by
  show AnnotatedRelation.annSum
      ((((AggQuery.Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun i => firstCols_kind n₁ n₂ i)).evaluate d).map
          GenRow.toAnnotated) u = _
  rw [AggQuery.evaluate_castKind]
  show AnnotatedRelation.annSum
      ((AggQuery.Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).evaluateAnnotated d) u = _
  rw [evaluateAnnotated_Proj]
  unfold AnnotatedRelation.annSum matchAnn
  show (Multiset.map Prod.snd (Multiset.filter _ (Multiset.map _
    ((innerJoin φ q₁ q₂).evaluate d)))).sum
    = (Multiset.map Prod.snd (Multiset.filter _ (Multiset.map GenRow.toAnnotated
        ((innerJoin φ q₁ q₂).evaluate d)))).sum
  rw [Multiset.filter_map, Multiset.filter_map, Multiset.map_map, Multiset.map_map]
  rfl

/-- **What a left outer join annotates**: a matching pair by the product of
the two annotations, and a padded row of the left arm by `α ⊖ ⊕(α' ⊗ β)`,
the sum over the matches of *every copy* of its tuple – the tuple is
unmatched in the worlds where none of its matches is present.

The subtracted form is the definition. `α ⊗ (𝟙 ⊖ ⊕β)`, the form one would
expect, is equal to it when `⊗` distributes over `⊖` and `K` is absorptive,
and not in general. -/
theorem evaluateAnnotated_leftOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : AnnotatedDatabase T K) :
    (leftOuter φ q₁ q₂).evaluateAnnotated d
      = (show Multiset (AnnotatedTuple T K (n₁ + n₂)) from
          (innerJoin φ q₁ q₂).evaluateAnnotated d)
        + (Multiset.map (fun p : AnnotatedTuple T K n₁ =>
            ((Fin.append p.1 (fun _ : Fin n₂ => ValueTypeNull.null),
              p.2 - matchAnn φ q₁ q₂ d p.1) :
              AnnotatedTuple T K (n₁ + n₂)))
            (show Multiset (AnnotatedTuple T K n₁) from q₁.evaluateAnnotated d)
           : Multiset (AnnotatedTuple T K (n₁ + n₂))) := by
  show (show Multiset (AnnotatedTuple T K (n₁ + n₂)) from
      (((innerJoin φ q₁ q₂).evaluate d
        + (leftUnmatched φ q₁ q₂).evaluate d)).map GenRow.toAnnotated) = _
  rw [Multiset.map_add]
  refine congrArg (_ + ·) ?_
  show ((leftUnmatched φ q₁ q₂).evaluateAnnotated d) = _
  unfold leftUnmatched padRight pad
  show (((AggQuery.Proj _ _).castKind _).evaluate d).map GenRow.toAnnotated = _
  rw [AggQuery.evaluate_castKind]
  show ((AggQuery.Proj _ _).evaluateAnnotated d) = _
  rw [evaluateAnnotated_Proj, evaluate_Diff, Multiset.map_map]
  simp only [Function.comp_def]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  rw [annSum_firstCols]
  refine Prod.ext ?_ (by simp [GenRow.ofAnnotated])
  funext j
  show AggValue.collapseSum
      ((padCol (Fin.addCases (fun i => some i) (fun _ => none) j)).eval
        (GenRow.ofAnnotated (p.1, p.2 - matchAnn φ q₁ q₂ d p.1)).fst)
    = Fin.append p.1 (fun _ : Fin n₂ => ValueTypeNull.null) j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, Fin.addCases_left]
    rfl
  · rw [Fin.append_right, Fin.addCases_right]
    rfl

/-- The `⊕`-sum of the annotations of the matches of a row of the right
arm. -/
def matchAnnRight (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂))
    (d : AnnotatedDatabase T K) (v : Tuple T n₂) : K :=
  (Multiset.map Prod.snd (Multiset.filter
    (fun p : AnnotatedTuple T K (n₁ + n₂) =>
      (fun j => p.1 (Fin.natAdd n₁ j) : Tuple T n₂) = v)
    ((innerJoin φ q₁ q₂).evaluateAnnotated d))).sum

/-- The right arm of the difference in a right outer join carries, on a
tuple, the `⊕`-sum of the annotations of its matches. -/
theorem annSum_lastCols (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂))
    (d : AnnotatedDatabase T K) (v : Tuple T n₂) :
    AnnotatedRelation.annSum
      (((AggQuery.Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun j => lastCols_kind n₁ n₂ j)).evaluateAnnotated d) v
      = matchAnnRight φ q₁ q₂ d v := by
  show AnnotatedRelation.annSum
      ((((AggQuery.Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun j => lastCols_kind n₁ n₂ j)).evaluate d).map
          GenRow.toAnnotated) v = _
  rw [AggQuery.evaluate_castKind]
  show AnnotatedRelation.annSum
      ((AggQuery.Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).evaluateAnnotated d) v = _
  rw [evaluateAnnotated_Proj]
  unfold AnnotatedRelation.annSum matchAnnRight
  show (Multiset.map Prod.snd (Multiset.filter _ (Multiset.map _
    ((innerJoin φ q₁ q₂).evaluate d)))).sum
    = (Multiset.map Prod.snd (Multiset.filter _ (Multiset.map GenRow.toAnnotated
        ((innerJoin φ q₁ q₂).evaluate d)))).sum
  rw [Multiset.filter_map, Multiset.filter_map, Multiset.map_map, Multiset.map_map]
  rfl

/-- The padded part of a right outer join: the rows of the right arm,
padded on the left, each subtracted the annotations of its matches. -/
theorem evaluateAnnotated_rightUnmatched
    (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : AnnotatedDatabase T K) :
    (rightUnmatched φ q₁ q₂).evaluateAnnotated d
      = (Multiset.map (fun p : AnnotatedTuple T K n₂ =>
          ((Fin.append (fun _ : Fin n₁ => ValueTypeNull.null) p.1,
            p.2 - matchAnnRight φ q₁ q₂ d p.1) :
            AnnotatedTuple T K (n₁ + n₂)))
          (show Multiset (AnnotatedTuple T K n₂) from q₂.evaluateAnnotated d)
         : Multiset (AnnotatedTuple T K (n₁ + n₂))) := by
  unfold rightUnmatched padLeft pad
  show (((AggQuery.Proj _ _).castKind _).evaluate d).map GenRow.toAnnotated = _
  rw [AggQuery.evaluate_castKind]
  show ((AggQuery.Proj _ _).evaluateAnnotated d) = _
  rw [evaluateAnnotated_Proj, evaluate_Diff, Multiset.map_map]
  simp only [Function.comp_def]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  rw [annSum_lastCols]
  refine Prod.ext ?_ (by simp [GenRow.ofAnnotated])
  funext j
  show AggValue.collapseSum
      ((padCol (Fin.addCases (fun _ => none) (fun i => some i) j)).eval
        (GenRow.ofAnnotated (p.1, p.2 - matchAnnRight φ q₁ q₂ d p.1)).fst)
    = Fin.append (fun _ : Fin n₁ => ValueTypeNull.null) p.1 j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left, Fin.addCases_left]
    rfl
  · rw [Fin.append_right, Fin.addCases_right]
    rfl

/-- **What a right outer join annotates**, symmetrically. -/
theorem evaluateAnnotated_rightOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : AnnotatedDatabase T K) :
    (rightOuter φ q₁ q₂).evaluateAnnotated d
      = (show Multiset (AnnotatedTuple T K (n₁ + n₂)) from
          (innerJoin φ q₁ q₂).evaluateAnnotated d)
        + (Multiset.map (fun p : AnnotatedTuple T K n₂ =>
            ((Fin.append (fun _ : Fin n₁ => ValueTypeNull.null) p.1,
              p.2 - matchAnnRight φ q₁ q₂ d p.1) :
              AnnotatedTuple T K (n₁ + n₂)))
            (show Multiset (AnnotatedTuple T K n₂) from q₂.evaluateAnnotated d)
           : Multiset (AnnotatedTuple T K (n₁ + n₂))) := by
  show (show Multiset (AnnotatedTuple T K (n₁ + n₂)) from
      (((innerJoin φ q₁ q₂).evaluate d
        + (rightUnmatched φ q₁ q₂).evaluate d)).map GenRow.toAnnotated) = _
  rw [Multiset.map_add]
  exact congrArg (_ + ·) (evaluateAnnotated_rightUnmatched φ q₁ q₂ d)

/-- **What a full outer join annotates**: the left outer join, and the rows
of the right arm padded on the left, each subtracted the annotations of its
matches. -/
theorem evaluateAnnotated_fullOuter (φ : GenPred T (ColKind.allReg (n₁ + n₂)))
    (q₁ : AggQuery T n₁ (ColKind.allReg n₁))
    (q₂ : AggQuery T n₂ (ColKind.allReg n₂)) (d : AnnotatedDatabase T K) :
    (fullOuter φ q₁ q₂).evaluateAnnotated d
      = (show Multiset (AnnotatedTuple T K (n₁ + n₂)) from
          (leftOuter φ q₁ q₂).evaluateAnnotated d)
        + (Multiset.map (fun p : AnnotatedTuple T K n₂ =>
            ((Fin.append (fun _ : Fin n₁ => ValueTypeNull.null) p.1,
              p.2 - matchAnnRight φ q₁ q₂ d p.1) :
              AnnotatedTuple T K (n₁ + n₂)))
            (show Multiset (AnnotatedTuple T K n₂) from q₂.evaluateAnnotated d)
           : Multiset (AnnotatedTuple T K (n₁ + n₂))) := by
  show (show Multiset (AnnotatedTuple T K (n₁ + n₂)) from
      (((leftOuter φ q₁ q₂).evaluate d
        + (rightUnmatched φ q₁ q₂).evaluate d)).map GenRow.toAnnotated) = _
  rw [Multiset.map_add]
  exact congrArg (_ + ·) (evaluateAnnotated_rightUnmatched φ q₁ q₂ d)

/-! ## Semijoin and antijoin -/

/-- Projecting a `Gamma` output back onto its key columns carries the
annotation across and keeps the key. -/
theorem evaluateAnnotated_Proj_keyCols {k : ℕ}
    (X : AggQuery T (k + 1)
      (Fin.append (fun _ => ColKind.reg) (fun _ => ColKind.agg)))
    (d : AnnotatedDatabase T K) :
    (AggQuery.Proj (keyCols k) X).evaluateAnnotated d
      = Multiset.map (fun p : AnnotatedTuple T K (k + 1) =>
          ((fun j => p.1 (Fin.castAdd 1 j), p.2) : AnnotatedTuple T K k))
          (show Multiset (AnnotatedTuple T K (k + 1)) from X.evaluateAnnotated d) := by
  rw [evaluateAnnotated_Proj]
  show _ = Multiset.map _ ((X.evaluate d).map GenRow.toAnnotated)
  rw [Multiset.map_map]
  rfl

/-- **The closed form of a semijoin's annotation.** Its selection on an
aggregate value sits directly above the grouping, so it is a fused
`HAVING` site: one row per row of the left arm, annotated by the predicate
provenance of the comparison on that row's group. -/
theorem evaluateAnnotated_semijoin (cnt : SeqAggFunc T) (κ : Fin l)
    (φ : GenPred T (ColKind.allReg (k + l)))
    (R : AggQuery T k (ColKind.allReg k)) (Q : AggQuery T l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) :
    (semijoin cnt κ φ R Q).evaluateAnnotated d
      = Multiset.map (fun g : Tuple T k =>
          ((g, Having.havingProv
              (Having.havingGroup (fun i : Fin k => Fin.castAdd l i)
                ((leftOuter φ R Q).evaluateAnnotated d) g)
              (Term.index (Fin.natAdd k κ)) cnt CompOp.ne 0)
            : AnnotatedTuple T K k))
          (Multiset.dedup (Multiset.map
            (fun p : AnnotatedTuple T K (k + l) =>
              (fun i : Fin k => p.fst (Fin.castAdd l i) : Tuple T k))
            (show Multiset (AnnotatedTuple T K (k + l)) from
              (leftOuter φ R Q).evaluateAnnotated d))) := by
  show (((AggQuery.Proj (keyCols k) (AggQuery.Sel (countCmp CompOp.ne 0)
      (matchCount cnt κ φ R Q))).castKind
        (funext fun i => keyCols_kind i)).evaluate d).map GenRow.toAnnotated = _
  rw [AggQuery.evaluate_castKind]
  show ((AggQuery.Proj (keyCols k) _).evaluateAnnotated d) = _
  rw [evaluateAnnotated_Proj_keyCols,
    show AggQuery.Sel (countCmp (k := k) CompOp.ne 0) (matchCount cnt κ φ R Q)
      = AggQuery.havingSite (fun i : Fin k => Fin.castAdd l i)
          ![Term.index (Fin.natAdd k κ)] ![cnt] CompOp.ne 0 (Term.const 0)
          (leftOuter φ R Q) from rfl,
    AggQuery.havingSite_evaluateAnnotated, Multiset.map_map]
  simp only [Function.comp_def]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  refine Prod.ext ?_ rfl
  funext j
  dsimp only
  exact Fin.append_left _ _ j

/-- **The closed form of an antijoin's annotation**, likewise: the
predicate provenance of the comparison `= 0` on each row's group. -/
theorem evaluateAnnotated_antijoin (cnt : SeqAggFunc T) (κ : Fin l)
    (φ : GenPred T (ColKind.allReg (k + l)))
    (R : AggQuery T k (ColKind.allReg k)) (Q : AggQuery T l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) :
    (antijoin cnt κ φ R Q).evaluateAnnotated d
      = Multiset.map (fun g : Tuple T k =>
          ((g, Having.havingProv
              (Having.havingGroup (fun i : Fin k => Fin.castAdd l i)
                ((leftOuter φ R Q).evaluateAnnotated d) g)
              (Term.index (Fin.natAdd k κ)) cnt CompOp.eq 0)
            : AnnotatedTuple T K k))
          (Multiset.dedup (Multiset.map
            (fun p : AnnotatedTuple T K (k + l) =>
              (fun i : Fin k => p.fst (Fin.castAdd l i) : Tuple T k))
            (show Multiset (AnnotatedTuple T K (k + l)) from
              (leftOuter φ R Q).evaluateAnnotated d))) := by
  show (((AggQuery.Proj (keyCols k) (AggQuery.Sel (countCmp CompOp.eq 0)
      (matchCount cnt κ φ R Q))).castKind
        (funext fun i => keyCols_kind i)).evaluate d).map GenRow.toAnnotated = _
  rw [AggQuery.evaluate_castKind]
  show ((AggQuery.Proj (keyCols k) _).evaluateAnnotated d) = _
  rw [evaluateAnnotated_Proj_keyCols,
    show AggQuery.Sel (countCmp (k := k) CompOp.eq 0) (matchCount cnt κ φ R Q)
      = AggQuery.havingSite (fun i : Fin k => Fin.castAdd l i)
          ![Term.index (Fin.natAdd k κ)] ![cnt] CompOp.eq 0 (Term.const 0)
          (leftOuter φ R Q) from rfl,
    AggQuery.havingSite_evaluateAnnotated, Multiset.map_map]
  simp only [Function.comp_def]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  refine Prod.ext ?_ rfl
  funext j
  dsimp only
  exact Fin.append_left _ _ j

/-- **A semijoin annotates a row of the left arm by the `⊕`-sum of the
annotations of its matches.** In an absorptive m-semiring the predicate
provenance of `COUNT(κ) ≠ 0` on the row's group collapses to the
occurrences that qualify, and those are exactly the matches: the padded
copy carries a null in column `κ` and a count skips it. -/
theorem evaluateAnnotated_semijoin_sum (h_abs : absorptive K)
    {cnt : SeqAggFunc T} (hc : Counts cnt) (κ : Fin l)
    (φ : GenPred T (ColKind.allReg (k + l)))
    (R : AggQuery T k (ColKind.allReg k)) (Q : AggQuery T l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) :
    (semijoin cnt κ φ R Q).evaluateAnnotated d
      = Multiset.map (fun g : Tuple T k =>
          ((g, ((Multiset.filter
              (fun p : AnnotatedTuple T K (k + l) =>
                ValueType.isNull (p.fst (Fin.natAdd k κ)) = false)
              (↑(Having.havingGroup (fun i : Fin k => Fin.castAdd l i)
                  ((leftOuter φ R Q).evaluateAnnotated d) g) :
                Multiset (AnnotatedTuple T K (k + l)))).map Prod.snd).sum)
            : AnnotatedTuple T K k))
          (Multiset.dedup (Multiset.map
            (fun p : AnnotatedTuple T K (k + l) =>
              (fun i : Fin k => p.fst (Fin.castAdd l i) : Tuple T k))
            (show Multiset (AnnotatedTuple T K (k + l)) from
              (leftOuter φ R Q).evaluateAnnotated d))) := by
  rw [evaluateAnnotated_semijoin]
  refine Multiset.map_congr rfl (fun g _ => ?_)
  refine Prod.ext rfl ?_
  dsimp only
  exact Having.havingProv_existentialOn h_abs (existentialOn_counting hc) _ _

end Outer

end AggQuery
