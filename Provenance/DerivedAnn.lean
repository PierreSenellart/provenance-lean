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

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] {n : ℕ}

namespace AggQuery

/-- The `⊕`-sum of the annotations a query gives one tuple: what
duplicate elimination accumulates on it. -/
def annSum (q : AggQuery T n (ColKind.allReg n)) (d : AnnotatedDatabase T K)
    (u : Tuple T n) : K :=
  (Multiset.map Prod.snd (Multiset.filter
    (fun p : AnnotatedTuple T K n => p.1 = u) (q.evaluateAnnotated d))).sum

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

end AggQuery
