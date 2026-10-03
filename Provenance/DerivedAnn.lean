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

namespace AggQueryIn

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
    (AggQueryIn.Diff q₁ q₂).evaluate d
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
    (AggQueryIn.Dedup q).evaluate d
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
    (AggQueryIn.Proj ps q).evaluateAnnotated d
      = (q.evaluate d).map (fun r =>
          ((fun j => AggValue.collapseSum ((ps j).eval r.fst), r.snd.finalize)
            : AnnotatedTuple T K m)) := by
  show ((AggQueryIn.Proj ps q).evaluate d).map GenRow.toAnnotated = _
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
    (AggQueryIn.Sel φ q).evaluate d
      = (q.evaluate d).filter (fun r => φ.holds r.fst) := by
  show (if φ.hasAggAtom = true then _ else _) = _
  rw [hφ]
  rfl

/-- A product pairs the rows, multiplying the concrete annotations and
putting the pending factors side by side. -/
theorem evaluate_Prod {n₁ n₂ : ℕ} {κ₁ : Fin n₁ → ColKind} {κ₂ : Fin n₂ → ColKind}
    (q₁ : AggQuery T n₁ κ₁) (q₂ : AggQuery T n₂ κ₂)
    (d : AnnotatedDatabase T K) :
    (AggQueryIn.Prod q₁ q₂).evaluate d
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
  rw [AggQueryIn.evaluate_castKind]
  rw [show (AggQueryIn.Proj (fstBlock n) (AggQueryIn.Sel (interCond n)
        ((AggQueryIn.Prod (AggQueryIn.Dedup q₁) (AggQueryIn.Dedup q₂)).castKind
          (append_allReg n n)))).evaluate d
      = ((AggQueryIn.Sel (interCond n)
          ((AggQueryIn.Prod (AggQueryIn.Dedup q₁) (AggQueryIn.Dedup q₂)).castKind
            (append_allReg n n))).evaluate d).map (fun r =>
        (⟨fun j => (fstBlock n j).eval r.fst,
          ⟨r.snd.base * ((r.snd.pending -
              r.snd.pending ∩ tokenLists (fun j => (fstBlock n j).eval r.fst)).map
              (fun l => SemiringWithMonus.delta l.sum)).prod,
            r.snd.pending ∩ tokenLists (fun j => (fstBlock n j).eval r.fst)⟩⟩ :
          GenRow T K n)) from rfl,
    evaluate_Sel_of_noAgg _ (interCond_hasAggAtom n), AggQueryIn.evaluate_castKind,
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
    (((AggQueryIn.Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun i => firstCols_kind n₁ n₂ i)).evaluateAnnotated d).annSum u
      = matchAnn φ q₁ q₂ d u := by
  show AnnotatedRelation.annSum
      ((((AggQueryIn.Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun i => firstCols_kind n₁ n₂ i)).evaluate d).map
          GenRow.toAnnotated) u = _
  rw [AggQueryIn.evaluate_castKind]
  show AnnotatedRelation.annSum
      ((AggQueryIn.Proj (firstCols n₁ n₂) (innerJoin φ q₁ q₂)).evaluateAnnotated d) u = _
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
  show (((AggQueryIn.Proj _ _).castKind _).evaluate d).map GenRow.toAnnotated = _
  rw [AggQueryIn.evaluate_castKind]
  show ((AggQueryIn.Proj _ _).evaluateAnnotated d) = _
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
      (((AggQueryIn.Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun j => lastCols_kind n₁ n₂ j)).evaluateAnnotated d) v
      = matchAnnRight φ q₁ q₂ d v := by
  show AnnotatedRelation.annSum
      ((((AggQueryIn.Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).castKind
        (funext fun j => lastCols_kind n₁ n₂ j)).evaluate d).map
          GenRow.toAnnotated) v = _
  rw [AggQueryIn.evaluate_castKind]
  show AnnotatedRelation.annSum
      ((AggQueryIn.Proj (lastCols n₁ n₂) (innerJoin φ q₁ q₂)).evaluateAnnotated d) v = _
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
  show (((AggQueryIn.Proj _ _).castKind _).evaluate d).map GenRow.toAnnotated = _
  rw [AggQueryIn.evaluate_castKind]
  show ((AggQueryIn.Proj _ _).evaluateAnnotated d) = _
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

end Outer

/-! ## Semijoin and antijoin -/

section Semijoin

variable [ValueType T] {k l : ℕ}

/-- The `⊕`-sum of every annotation of an annotated relation: the
provenance of "there is a row here", which is what an existential
subquery asks for. -/
def _root_.AnnotatedRelation.annTotal (r : AnnotatedRelation T K n) : K :=
  (Multiset.map Prod.snd r).sum

/-- The token a match count builds on a row `u` of the left arm: the
scalar count, over the column `kap`, of the rows of `Q` that `φ` matches
`u` with. -/
def matchToken (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) (u : Tuple T k) : AggValue T K :=
  AggValue.ofScalarGroup cnt (TermIn.index (c := 0) kap)
    (Having.havingGroup (fun i : Fin 0 => i.elim0)
      ((Sel φ Q).evaluateAnnotated d u) (fun i : Fin 0 => i.elim0))

/-- A scalar aggregation on one `(term, aggregate)` pair produces the one
row that carries its token. -/
theorem evaluate_GammaScalar_one {c m : ℕ} (t : TermIn T c m)
    (cnt : SeqAggFunc T) (q : AggQueryIn T c m (ColKind.allReg m))
    (d : AnnotatedDatabase T K) (γ : Fin c → T) :
    (GammaScalar ![t] ![cnt] q).evaluate d γ
      = {(⟨fun _ : Fin 1 => Sum.inr (AggTok.tok (AggValue.ofScalarGroup cnt t
            (Having.havingGroup (fun i : Fin 0 => i.elim0)
              (q.evaluateAnnotated d γ) (fun i : Fin 0 => i.elim0)) γ)),
          ⟨1, 0⟩⟩ : GenRow T K 1)} := by
  simp only [AggQueryIn.evaluate, AggQueryIn.evaluateAnnotated,
    Matrix.cons_val_fin_one]

/-- **What a match count evaluates to**: each occurrence of the left arm,
its annotation untouched, extended by its match token. -/
theorem evaluate_matchCount (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (R : AggQuery T k (ColKind.allReg k))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) :
    (matchCount cnt kap φ R Q).evaluate d
      = (R.evaluate d).map (fun x =>
          (⟨Fin.append x.fst (fun _ : Fin 1 => Sum.inr (AggTok.tok
              (matchToken cnt kap φ Q d (GenRow.plainTuple x.fst)))),
            x.snd⟩ : GenRow T K (k + 1))) := by
  rw [matchCount, AggQueryIn.evaluate_Apply]
  refine (Multiset.bind_congr (fun x _ => ?_)).trans
    (Multiset.bind_singleton _ _)
  rw [evaluate_GammaScalar_one, Multiset.map_singleton]
  refine congrArg (fun r : GenRow T K (k + 1) => ({r} : Multiset _)) ?_
  refine Prod.ext rfl ?_
  show (⟨x.snd.base * 1, x.snd.pending + 0⟩ : GenAnn K) = x.snd
  rw [mul_one, add_zero]

/-- **The rows a count site produces**: each occurrence of the left arm,
its annotation multiplied by the predicate provenance of comparing its
match count against `𝟘`. -/
theorem evaluateAnnotated_countSite (op : CompOp) (cnt : SeqAggFunc T)
    (kap : Fin l) (φ : GenPredIn T k (ColKind.allReg l))
    (R : AggQuery T k (ColKind.allReg k))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) :
    (Proj (dropCount k)
      (Sel (GenPredIn.aggCmp (countCol k) (countKinds_countCol k) op
          (TermGIn.const 0))
        (matchCount cnt kap φ R Q))).evaluateAnnotated d
      = (R.evaluateAnnotated d).map (fun p =>
          ((p.fst,
            p.snd * (matchToken cnt kap φ Q d p.fst).predProvScalar op 0)
            : AnnotatedTuple T K k)) := by
  simp only [AggQueryIn.evaluateAnnotated, AggQueryIn.evaluate]
  rw [evaluate_matchCount]
  simp only [GenPredIn.hasAggAtom, GenPredIn.entailsExistence,
    GenPredIn.comparedCols, ite_true, Multiset.map_map]
  refine Multiset.map_congr rfl (fun x _ => ?_)
  simp only [Function.comp_apply]
  set tok := matchToken cnt kap φ Q d (GenRow.plainTuple x.fst) with htok
  set row : Tuple (GenValue T K) (k + 1) :=
    Fin.append x.fst (fun _ : Fin 1 => Sum.inr (AggTok.tok tok)) with hrow
  -- the projection reads the left arm's columns back and keeps no token
  have hu : (fun j => ProjColIn.eval (dropCount k j) row)
      = fun j => (Sum.inl (AggValue.collapseSum (x.fst j)) : GenValue T K) := by
    funext j
    show (Sum.inl (AggValue.collapseSum (row (Fin.castAdd 1 j)))
      : GenValue T K) = _
    rw [hrow, Fin.append_left]
  have hzero : tokenLists (K := K)
      (fun j : Fin k => (Sum.inl (AggValue.collapseSum (x.fst j)))) = 0 := by
    unfold tokenLists
    refine Multiset.eq_zero_of_forall_notMem (fun b hb => ?_)
    obtain ⟨i, -, hi⟩ := (Multiset.mem_filterMap _ _).mp hb
    exact absurd hi (by simp)
  -- the compared token is scalar, so no pending factor is superseded
  have hA : Multiset.filterMap
      (fun i => match row i with
        | Sum.inl _ => (none : Option (List K))
        | Sum.inr a => if a.scalar = true then some a.annList
          else none)
      ({countCol k} : Finset (Fin (k + 1))).val ≠ 0 := by
    intro hcon
    have hmem : (tok.occs.map Prod.snd) ∈ Multiset.filterMap
        (fun i => match row i with
          | Sum.inl _ => (none : Option (List K))
          | Sum.inr a => if a.scalar = true then some a.annList
            else none)
        ({countCol k} : Finset (Fin (k + 1))).val :=
      (Multiset.mem_filterMap _ _).mpr ⟨countCol k,
        Finset.mem_val.mpr (Finset.mem_singleton_self _), by
          rw [hrow, Fin.append_right]
          simp [htok, matchToken]⟩
    rw [hcon] at hmem
    exact Multiset.notMem_zero _ hmem
  rw [hu, hzero, Multiset.inter_zero, Multiset.sub_zero,
    Multiset.filter_eq_self.mpr]
  -- the comparison is read in the scalar convention the token carries
  have hpred : (GenPredIn.aggCmp (c := 0) (countCol k)
        (countKinds_countCol k) op (TermGIn.const 0)).predsem
          (K := K) false row
      = tok.predProvScalar op 0 := by
    show (match row (countCol k) with
      | Sum.inl _ => (0 : K)
      | Sum.inr a => a.predProvOf op ((TermGIn.const (0 : T)).eval row)) = _
    rw [hrow, Fin.append_right]
    exact AggValue.predProvOf_of_scalar (a := tok) (by simp [htok, matchToken]) op 0
  rw [hpred]
  refine Prod.ext ?_ ?_
  · funext j
    show AggValue.collapseSum
        ((Sum.inl (AggValue.collapseSum (x.fst j)) : GenValue T K))
      = AggValue.collapseSum (x.fst j)
    rfl
  · show GenAnn.finalize ⟨x.snd.base * tok.predProvScalar op 0
        * (Multiset.map (fun l => SemiringWithMonus.delta l.sum)
            x.snd.pending).prod, 0⟩
      = GenAnn.finalize x.snd * tok.predProvScalar op 0
    rw [GenAnn.finalize_of_pending_zero]
    show _ = x.snd.base
      * (Multiset.map (fun l => SemiringWithMonus.delta l.sum)
          x.snd.pending).prod * tok.predProvScalar op 0
    rw [mul_right_comm]
  · exact fun _ _ h => hA h.1

/-! ### What a semijoin and an antijoin annotate -/

omit [DecidableEq K] [HasAltLinearOrder K] in
private theorem sum_fin_get {α : Type} (f : α → K) :
    ∀ L : List α, ∑ i : Fin L.length, f (L.get i) = (L.map f).sum
  | [] => by simp
  | a :: L => by
    rw [List.map_cons, List.sum_cons, ← sum_fin_get f L]
    show ∑ i : Fin (L.length + 1), f ((a :: L).get i) = _
    rw [Fin.sum_univ_succ]
    rfl

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- With no key columns the group sequence is the whole relation. -/
theorem havingGroup_nil_coe {m : ℕ} (r : AnnotatedRelation T K m) :
    (↑(Having.havingGroup (fun i : Fin 0 => i.elim0) r
        (fun i : Fin 0 => i.elim0)) : Multiset (AnnotatedTuple T K m))
      = (show Multiset (AnnotatedTuple T K m) from r) := by
  rw [Having.havingGroup_coe,
    Multiset.filter_eq_self.mpr (fun _ _ k' => k'.elim0)]

omit [DecidableEq K] in
/-- With no key columns the group's annotations sum to the relation's. -/
theorem annTotal_havingGroup {m : ℕ} (r : AnnotatedRelation T K m) :
    ((Having.havingGroup (fun i : Fin 0 => i.elim0) r
          (fun i : Fin 0 => i.elim0)).map Prod.snd).sum = r.annTotal := by
  show ((Multiset.map Prod.snd
    (↑(Having.havingGroup (fun i : Fin 0 => i.elim0) r
        (fun i : Fin 0 => i.elim0))
      : Multiset (AnnotatedTuple T K m)))).sum = _
  rw [havingGroup_nil_coe]
  rfl

/-- The occurrences a match token carries are the matching rows, their
`kap` values paired with their annotations. -/
theorem matchToken_occs (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) (u : Tuple T k) :
    (matchToken cnt kap φ Q d u).occs
      = (Having.havingGroup (fun i : Fin 0 => i.elim0)
          ((Sel φ Q).evaluateAnnotated d u) (fun i : Fin 0 => i.elim0)).map
        (fun p => (p.fst kap, p.snd)) := rfl

/-- The `⊕`-sum of a match token's occurrence annotations is the `⊕`-sum
of the annotations of the rows that match. -/
theorem sum_anns_matchToken (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) (u : Tuple T k) :
    ∑ i, (matchToken cnt kap φ Q d u).anns i
      = ((Sel φ Q).evaluateAnnotated d u).annTotal := by
  rw [show (fun i => (matchToken cnt kap φ Q d u).anns i)
      = fun i => ((matchToken cnt kap φ Q d u).occs.get i).snd from rfl,
    sum_fin_get Prod.snd, matchToken_occs, List.map_map]
  exact annTotal_havingGroup _

/-- Every occurrence a match token carries has the value of a matching
row in the counted column. -/
theorem mem_matchToken_occs (cnt : SeqAggFunc T) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K) (u : Tuple T k)
    {o : T × K} (ho : o ∈ (matchToken cnt kap φ Q d u).occs) :
    ∃ p ∈ (show Multiset (AnnotatedTuple T K l) from
      (Sel φ Q).evaluateAnnotated d u), o.fst = p.fst kap := by
  rw [matchToken_occs] at ho
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
  refine ⟨p, ?_, rfl⟩
  rw [← havingGroup_nil_coe ((Sel φ Q).evaluateAnnotated d u)]
  exact Multiset.mem_coe.mpr hp

/-- **The semijoin's annotation.** Each occurrence of the left arm keeps
its annotation, multiplied by the `⊕`-sum of the annotations of the rows
it matches – the provenance of "there is a match". -/
theorem evaluateAnnotated_semijoin (h_abs : absorptive K)
    (cnt : SeqAggFunc T) (hc : SeqAggFunc.Counts cnt) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (R : AggQuery T k (ColKind.allReg k))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K)
    (hnn : ∀ (u : Tuple T k), ∀ p ∈ (show Multiset (AnnotatedTuple T K l) from
        (Sel φ Q).evaluateAnnotated d u),
      ValueType.isNull (p.fst kap) = false) :
    (semijoin cnt kap φ R Q).evaluateAnnotated d
      = (R.evaluateAnnotated d).map (fun p =>
          ((p.fst, p.snd * ((Sel φ Q).evaluateAnnotated d p.fst).annTotal)
            : AnnotatedTuple T K k)) := by
  rw [semijoin, evaluateAnnotated_countSite]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  refine congrArg (fun a => ((p.fst, p.snd * a) : AnnotatedTuple T K k)) ?_
  rw [AggValue.predProvScalar_count_ne_zero h_abs _ hc (fun o ho => ?_),
    sum_anns_matchToken]
  obtain ⟨q, hq, ho'⟩ := mem_matchToken_occs cnt kap φ Q d p.fst ho
  rw [ho']
  exact hnn p.fst q hq

/-- **The antijoin's annotation.** Each occurrence of the left arm keeps
its annotation, multiplied by `𝟙 ⊖` the `⊕`-sum of the annotations of the
rows it matches. No hypothesis on `K` enters it. -/
theorem evaluateAnnotated_antijoin (cnt : SeqAggFunc T)
    (hc : SeqAggFunc.Counts cnt) (kap : Fin l)
    (φ : GenPredIn T k (ColKind.allReg l))
    (R : AggQuery T k (ColKind.allReg k))
    (Q : AggQueryIn T k l (ColKind.allReg l))
    (d : AnnotatedDatabase T K)
    (hnn : ∀ (u : Tuple T k), ∀ p ∈ (show Multiset (AnnotatedTuple T K l) from
        (Sel φ Q).evaluateAnnotated d u),
      ValueType.isNull (p.fst kap) = false) :
    (antijoin cnt kap φ R Q).evaluateAnnotated d
      = (R.evaluateAnnotated d).map (fun p =>
          ((p.fst,
            p.snd * (1 - ((Sel φ Q).evaluateAnnotated d p.fst).annTotal))
            : AnnotatedTuple T K k)) := by
  rw [antijoin, evaluateAnnotated_countSite]
  refine Multiset.map_congr rfl (fun p _ => ?_)
  refine congrArg (fun a => ((p.fst, p.snd * a) : AnnotatedTuple T K k)) ?_
  rw [AggValue.predProvScalar_count_eq_zero _ hc (fun o ho => ?_),
    sum_anns_matchToken]
  obtain ⟨q, hq, ho'⟩ := mem_matchToken_occs cnt kap φ Q d p.fst ho
  rw [ho']
  exact hnn p.fst q hq

end Semijoin

/-! ## The `FILTER` clause

The clause changes nothing about a group: the token carries all of its
occurrences, so the group's key and its existence factor are those of all
of them, and a filtered-out occurrence still witnesses it. What changes
is the value the token takes in a world, and it changes there in the same
way as over plain relations – the input policy drops what the clause
nulls out, so the aggregate reads exactly the occurrences of that world
the clause keeps. -/

section Filter

variable [ValueTypeNull T] {m : ℕ}

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The term encoding computes the clause's reading, for a
null-skipping aggregate**: nulling the rejected occurrences out and then
skipping them is cutting them from the sequence. This is why a
null-skipping `FILTER` needs nothing but a term. -/
theorem aggValOn_filterTerm_sqlOf (f : SeqAggFunc T) (op : CompOp)
    (t₁ t₂ t : Term T m) (U : List (AnnotatedTuple T K m))
    (W : Finset (Fin U.length)) :
    Having.aggValOn U (filterTerm op t₁ t₂ t) f.sqlOf W
      = Having.aggValOnWhen U (filterHolds op t₁ t₂) t f.sqlOf W := by
  show f.sqlOf ((Having.seqOf U W).map
      (fun p => (filterTerm op t₁ t₂ t).eval p.fst)) = _
  rw [show (fun p : AnnotatedTuple T K m => (filterTerm op t₁ t₂ t).eval p.fst)
      = (fun u => (filterTerm op t₁ t₂ t).eval u) ∘ Prod.fst from rfl,
    ← List.map_map]
  exact sqlOf_map_filterTerm f op t₁ t₂ t _ _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The same for a count. -/
theorem aggValOn_filterTerm_counting (f : SeqAggFunc T) (op : CompOp)
    (t₁ t₂ t : Term T m) (U : List (AnnotatedTuple T K m))
    (W : Finset (Fin U.length)) :
    Having.aggValOn U (filterTerm op t₁ t₂ t) f.counting W
      = Having.aggValOnWhen U (filterHolds op t₁ t₂) t f.counting W := by
  show f.counting ((Having.seqOf U W).map
      (fun p => (filterTerm op t₁ t₂ t).eval p.fst)) = _
  rw [show (fun p : AnnotatedTuple T K m => (filterTerm op t₁ t₂ t).eval p.fst)
      = (fun u => (filterTerm op t₁ t₂ t).eval u) ∘ Prod.fst from rfl,
    ← List.map_map]
  exact counting_map_filterTerm f op t₁ t₂ t _ _

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The token of a filtered aggregation reads the same way**: its value
in a world is the aggregate of the occurrences of that world the clause
keeps. -/
theorem valOn_ofGroup_filterTerm_sqlOf (f : SeqAggFunc T) (op : CompOp)
    (t₁ t₂ t : Term T m) (U : List (AnnotatedTuple T K m))
    (W : Finset (Fin U.length)) :
    (AggValue.ofGroup f.sqlOf (filterTerm op t₁ t₂ t) U).valOn
        (W.map (finCongr
          (AggValue.length_ofGroup_occs f.sqlOf
            (filterTerm op t₁ t₂ t) U)).toEmbedding)
      = Having.aggValOnWhen U (filterHolds op t₁ t₂) t f.sqlOf W := by
  rw [AggValue.valOn_ofGroup, aggValOn_filterTerm_sqlOf]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The same for a count. -/
theorem valOn_ofGroup_filterTerm_counting (f : SeqAggFunc T) (op : CompOp)
    (t₁ t₂ t : Term T m) (U : List (AnnotatedTuple T K m))
    (W : Finset (Fin U.length)) :
    (AggValue.ofGroup f.counting (filterTerm op t₁ t₂ t) U).valOn
        (W.map (finCongr
          (AggValue.length_ofGroup_occs f.counting
            (filterTerm op t₁ t₂ t) U)).toEmbedding)
      = Having.aggValOnWhen U (filterHolds op t₁ t₂) t f.counting W := by
  rw [AggValue.valOn_ofGroup, aggValOn_filterTerm_counting]

/-! ### Why a null-keeping aggregate has to be told about the clause

On a null-skipping aggregate and on a count, `FILTER` is a term: nulling
the rejected occurrences out and letting the input policy drop them is
cutting them from the sequence (`aggValOn_filterTerm_sqlOf`,
`aggValOn_filterTerm_counting`). On a null-keeping aggregate it is not a
term, and here is why: such an aggregate reads the null as a value, so it
reads the rejected occurrences too, and the clause has to cut the
sequence itself (`Having.aggValOnWhen`). -/

namespace FilterCounterexample

/-- The value domain of the counterexample: `ℕ` with a null adjoined. -/
abbrev V : Type := WithNull ℕ

/-- **A null-keeping aggregate**: the length of the sequence, nulls
included. This is `ARRAY_AGG`'s input policy – every value is read – in
the one shape a `ValueType` affords, there being no array in the domain:
what the aggregate returns is how many values it was given. -/
def len : SeqAggFunc V := fun L => WithNull.val L.length

/-- A group of two occurrences, carrying the values `1` and `2`. -/
def U : List (AnnotatedTuple V ℕ 1) :=
  [(fun _ => WithNull.val 1, 1), (fun _ => WithNull.val 2, 1)]

/-- The clause `x = 1`, which keeps the first occurrence and rejects the
second. -/
abbrev cl₁ : Term V 1 := TermIn.index 0

/-- Its right-hand side. -/
abbrev cl₂ : Term V 1 := TermIn.const (WithNull.val 1)

/-- **The term encoding over-counts.** With the clause's rejected
occurrence nulled out rather than removed, the null-keeping aggregate
reads two values where SQL's `FILTER` gives it one. -/
theorem filterTerm_ne_aggValOnWhen :
    Having.aggValOn U (filterTerm CompOp.eq cl₁ cl₂ (TermIn.index 0)) len
        Finset.univ
      ≠ Having.aggValOnWhen U (filterHolds CompOp.eq cl₁ cl₂)
        (TermIn.index 0) len Finset.univ := by
  decide

/-- The two values it reads, for the record: two against one. -/
theorem filterTerm_val :
    Having.aggValOn U (filterTerm CompOp.eq cl₁ cl₂ (TermIn.index 0)) len
      Finset.univ = WithNull.val 2 := by
  decide

theorem aggValOnWhen_val :
    Having.aggValOnWhen U (filterHolds CompOp.eq cl₁ cl₂) (TermIn.index 0) len
      Finset.univ = WithNull.val 1 := by
  decide

end FilterCounterexample

end Filter

/-! ## The token a filtered aggregation builds -/

section Where

variable [ValueType T] {c m n₁ : ℕ}

/-- **The token a filtered aggregation builds**: the occurrences of the
group the clause keeps, read in the scalar convention
(`AggValue.ofGroupWhen`). The group's existence guard is unchanged – it
is the pending factor over every occurrence – so a group all of whose
rows the clause rejects is still emitted, with the aggregate over
nothing. -/
theorem evaluate_gammaWhere (is : Tuple (Fin m) n₁) (φ : Selection T m)
    (t : TermIn T c m) (f : SeqAggFunc T)
    (q : AggQueryIn T c m (ColKind.allReg m)) (d : AnnotatedDatabase T K)
    {γ : Fin c → T} :
    (gammaWhere is φ t f q).evaluate d γ
      = (Multiset.ofList (groupByKey
          (((q.evaluate d γ).map GenRow.toAnnotated).map
            (fun p => ((fun k => p.fst (is k), p.snd)
              : AnnotatedTuple T K n₁)))).val).map (fun kv =>
        (⟨Fin.append (fun k => Sum.inl (kv.fst k))
            (fun _ : Fin 1 => Sum.inr (AggTok.tok (AggValue.ofGroupWhen f t
              φ.keeps (Having.havingGroup is
                ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst) γ))),
          ⟨1, {(Having.havingGroup is
              ((q.evaluate d γ).map GenRow.toAnnotated) kv.fst).map Prod.snd}⟩⟩
          : GenRow T K (n₁ + 1))) := by
  rw [gammaWhere, AggQueryIn.evaluate]
  refine Multiset.map_congr rfl (fun kv _ => ?_)
  refine congrArg (fun z => (z, _) : _ → GenRow T K (n₁ + 1)) ?_
  refine congrArg (Fin.append _) (funext fun j => ?_)
  obtain rfl : j = 0 := Fin.fin_one_eq_zero j
  rfl


end Where


end AggQueryIn
