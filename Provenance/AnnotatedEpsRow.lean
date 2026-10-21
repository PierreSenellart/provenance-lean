/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AnnotatedDiffRow

/-!
# Duplicate elimination is necessary in the annotated algebra

A set of classes that generates the annotated algebra over `ℕ` contains
`ε` or `μ^∪`. The invariant is that, without them, every annotation a
query builds is at most `𝟙` as soon as the instance's are. Products, `δ`
(the support map), a difference and `𝟙 ⊖ s` keep it; a sum does not, and
the evaluator adds annotations in three places only:

* `ε` and `μ^∪`, which sum the annotations of the copies of a tuple;
* a `DISTINCT` window, which merges the occurrences of one value – out of
  the minimal signature, `count` not being its own distinct version
  (`count_distinct_ne`);
* the joint reading of a selection on aggregate values, a sum over the
  worlds of the families it reads. There the sum of the worlds' weights is
  at most `𝟙` (`GenPredIn.predsemJ_le_one`): `ℕ` is complemented, so a
  world's weight is a product over the occurrences and the sum over all
  worlds factors into `∏ (a + (𝟙 ⊖ a))`, which is `𝟙` where every `a` is.

`ε` of a relation holding one tuple twice, annotated `𝟙`, gives `2`
(`dedup_or_muSet_mem_of_generatesAnn`).

With the other rows this makes the basis `{∅, Π, σ, apply, γ, win, μ^⊎,
ε, −}` minimal: no proper subset generates the annotated algebra over both
`ℕ` and `ℕ × ℕ` (`annEpsOps_minimal`).
-/

/-! ## The weight of a world, over `ℕ` -/

section Weights

theorem nat_delta_le_one (a : ℕ) : SemiringWithMonus.delta a ≤ 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · rw [SemiringWithMonus.delta_zero]; exact Nat.zero_le 1
  · have := SemiringWithMonus.delta_natCast_pos (α := ℕ) h
    rw [Nat.cast_id] at this
    rw [this]

theorem nat_one_sub_le_one (a : ℕ) : ((1 : ℕ) - a : ℕ) ≤ 1 := Nat.sub_le 1 a

theorem nat_add_one_sub (a : ℕ) (h : a ≤ 1) : (a + ((1 : ℕ) - a) : ℕ) = 1 := by omega

theorem nat_mul_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  calc a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb
    _ = 1 := rfl

theorem nat_mprod_le_one : ∀ s : Multiset ℕ, (∀ a ∈ s, a ≤ 1) → s.prod ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; exact le_refl 1
  | cons a s ih =>
    intro h
    rw [Multiset.prod_cons]
    exact nat_mul_le_one (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

theorem nat_fprod_le_one {ι : Type} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := by
  unfold Finset.prod
  exact nat_mprod_le_one _ fun a ha => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
    exact h i hi

/-- `𝟙 ⊖ Σ` is `∏ (𝟙 ⊖ ·)` over a finite set, `ℕ` being complemented. -/
theorem nat_one_sub_fsum {ι : Type} (s : Finset ι) (f : ι → ℕ) :
    ((1 : ℕ) - ∑ i ∈ s, f i : ℕ) = ∏ i ∈ s, ((1 : ℕ) - f i : ℕ) := by
  unfold Finset.sum Finset.prod
  rw [monus_multiset_sum Nat.complemented, Multiset.map_map]
  rfl

/-- **The worlds of a flat family weigh `𝟙` together** when every
occurrence is annotated at most `𝟙`. -/
theorem nat_sum_worldAnn {N : ℕ} (α : Fin N → ℕ) (h : ∀ i, α i ≤ 1) :
    ∑ W : Finset (Fin N), (∏ i ∈ W, α i) * (1 - ∑ i ∈ Wᶜ, α i) = 1 := by
  have hprod := Finset.prod_add α (fun i => 1 - α i) (Finset.univ : Finset (Fin N))
  rw [Finset.powerset_univ] at hprod
  calc ∑ W : Finset (Fin N), (∏ i ∈ W, α i) * (1 - ∑ i ∈ Wᶜ, α i)
      = ∑ W : Finset (Fin N), (∏ i ∈ W, α i) * ∏ i ∈ Finset.univ \ W, (1 - α i) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [nat_one_sub_fsum, Finset.compl_eq_univ_sdiff]
    _ = ∏ i, (α i + (1 - α i)) := hprod.symm
    _ = 1 := Finset.prod_eq_one fun i _ => nat_add_one_sub _ (h i)

theorem nat_sum_worldAnn_le {N : ℕ} (α : Fin N → ℕ) (h : ∀ i, α i ≤ 1)
    (F : Finset (Finset (Fin N))) :
    ∑ W ∈ F, (∏ i ∈ W, α i) * (1 - ∑ i ∈ Wᶜ, α i) ≤ 1 := by
  calc ∑ W ∈ F, (∏ i ∈ W, α i) * (1 - ∑ i ∈ Wᶜ, α i)
      ≤ ∑ W : Finset (Fin N), (∏ i ∈ W, α i) * (1 - ∑ i ∈ Wᶜ, α i) :=
        Finset.sum_le_sum_of_subset (f := fun W => (∏ i ∈ W, α i) * (1 - ∑ i ∈ Wᶜ, α i))
          (Finset.subset_univ F)
    _ = 1 := nat_sum_worldAnn α h

theorem nat_sum_filter_le {α : Type} (s : Multiset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℕ) : ((s.filter p).map f).sum ≤ (s.map f).sum := by
  conv_rhs => rw [← Multiset.filter_add_not p s]
  rw [Multiset.map_add, Multiset.sum_add]
  exact Nat.le_add_right _ _

theorem nat_sum_product {α β : Type} (s : Multiset α) (t : Multiset β) (f : α → ℕ)
    (g : β → ℕ) : ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum
      = (s.map f).sum * (t.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_map,
      Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [← Multiset.sum_map_mul_left]
    rfl

end Weights

/-! ## The worlds of a selection weigh at most `𝟙` together -/

section JointWeights

variable {T : Type} [ValueType T]

/-- The weight of a world: its present product times `𝟙 ⊖` its absent sum. -/
def worldWeight {n : ℕ} (w : ℕ × ℕ × (Fin n → Option T)) : ℕ := w.1 * ((1 : ℕ) - w.2.1 : ℕ)

omit [ValueType T] in
theorem worldWeight_combineW {n : ℕ} (w₁ w₂ : ℕ × ℕ × (Fin n → Option T)) :
    worldWeight (combineW w₁ w₂) = worldWeight w₁ * worldWeight w₂ := by
  unfold worldWeight combineW
  dsimp only
  rw [Nat.complemented, mul_mul_mul_comm]

omit [ValueType T] in
/-- The presence choices over outer occurrences annotated at most `𝟙`
weigh `𝟙` together. -/
theorem nat_sum_memChoices {X : Type} (M : Multiset (X × ℕ)) (hM : ∀ o ∈ M, o.2 ≤ 1) :
    ((NestedValue.memChoices M).map (fun ms =>
      (ms.map (fun m => if m.2.2 = true then m.2.1 else ((1 : ℕ) - m.2.1 : ℕ))).prod)).sum
      = 1 := by
  induction M using Multiset.induction_on with
  | empty => simp [NestedValue.memChoices]
  | cons o M ih =>
    have ih' := ih (fun o' ho' => hM o' (Multiset.mem_cons_of_mem ho'))
    simp only [NestedValue.memChoices, Multiset.foldr_cons] at ih' ⊢
    rw [NestedValue.addMem, Multiset.map_bind, Multiset.sum_bind,
      show ({true, false} : Multiset Bool) = true ::ₘ {false} from rfl]
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, Multiset.map_map, Function.comp_def, Multiset.prod_cons,
      ite_true, Bool.false_eq_true, ite_false]
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, ih', mul_one, mul_one,
      nat_add_one_sub _ (hM o (Multiset.mem_cons_self _ _))]

/-- What a decision over a bag of occurrences weighs over `ℕ`, occurrence
by occurrence. -/
def natDecW {X : Type} (D : Multiset (X × ℕ × Bool)) : ℕ :=
  (D.map (fun m => if m.2.2 = true then m.2.1 else ((1 : ℕ) - m.2.1 : ℕ))).prod

/-- What a decision about an expression family weighs over `ℕ`. -/
def natLeafW (e : LeafKey T ℕ × Finset ℕ) : ℕ :=
  NestedValue.leafProd e * ((1 : ℕ) - NestedValue.leafAbs e : ℕ)

omit [ValueType T] in
/-- Over `ℕ`, what a decision keeps times `𝟙 ⊖` what it leaves out is a
product over the occurrences. -/
theorem nat_decProd_decAbs {X : Type} (D : Multiset (X × ℕ × Bool)) :
    NestedValue.decProd D * ((1 : ℕ) - NestedValue.decAbs D : ℕ) = natDecW D := by
  induction D using Multiset.induction_on with
  | empty => simp [NestedValue.decProd, NestedValue.decAbs, natDecW]
  | cons m D ih =>
    simp only [NestedValue.decProd, NestedValue.decAbs, natDecW, Multiset.map_cons,
      Multiset.prod_cons, Multiset.sum_cons] at ih ⊢
    rw [Nat.complemented, ← ih]
    rcases m with ⟨x, a, b⟩
    cases b
    · simp only [Bool.false_eq_true, ite_false, one_mul]
      exact mul_left_comm _ _ _
    · simp only [ite_true, Nat.sub_zero, one_mul]
      exact mul_assoc _ _ _

omit [ValueType T] in
/-- **Over `ℕ` a nested world's weight factors**: the value's own
occurrences, each expression family and each node apart. -/
theorem nat_world_ann {d : ℕ} (W : NestedValue.World T ℕ d) :
    W.ann = natDecW W.root * (W.leaf.map natLeafW).prod
      * (W.node.map (fun e => natDecW e.2.2)).prod := by
  have hL : (W.leaf.map natLeafW).prod = (W.leaf.map NestedValue.leafProd).prod
      * ((W.leaf.map NestedValue.leafAbs).map (fun a => (1 : ℕ) - a)).prod := by
    rw [Multiset.map_map, ← Multiset.prod_map_mul]; rfl
  have hN : (W.node.map (fun e => natDecW e.2.2)).prod
      = (W.node.map (fun e => NestedValue.decProd e.2.2)).prod
        * ((W.node.map (fun e => NestedValue.decAbs e.2.2)).map (fun a => (1 : ℕ) - a)).prod := by
    rw [Multiset.map_map, ← Multiset.prod_map_mul]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun e _ =>
      (nat_decProd_decAbs e.2.2).symm)
  rw [hL, hN, ← nat_decProd_decAbs, NestedValue.World.ann, NestedValue.World.presentProd,
    NestedValue.World.absentSum, Nat.complemented, Nat.complemented,
    monus_multiset_sum Nat.complemented, monus_multiset_sum Nat.complemented]
  ac_rfl

omit [ValueType T] in
/-- The positions one can keep of an expression family annotated at most
`𝟙` weigh `𝟙` together. -/
theorem nat_sum_leafChoices (κ : LeafKey T ℕ) (h : ∀ k ∈ κ.2, k ≤ 1) :
    (((Finset.range κ.2.length).powerset.val).map (fun S => natLeafW (κ, S))).sum = 1 := by
  have hle : ∀ i, κ.2.getD i 0 ≤ 1 := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases hi : κ.2[i]? with
    | none => exact Nat.zero_le 1
    | some k => exact h k (List.mem_of_getElem? hi)
  have hprod := Finset.prod_add (fun i => κ.2.getD i 0) (fun i => (1 : ℕ) - κ.2.getD i 0)
    (Finset.range κ.2.length)
  change ∑ S ∈ (Finset.range κ.2.length).powerset, natLeafW (κ, S) = 1
  calc ∑ S ∈ (Finset.range κ.2.length).powerset, natLeafW (κ, S)
      = ∑ S ∈ (Finset.range κ.2.length).powerset, (∏ i ∈ S, κ.2.getD i 0)
          * ∏ i ∈ Finset.range κ.2.length \ S, ((1 : ℕ) - κ.2.getD i 0 : ℕ) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        simp only [natLeafW, NestedValue.leafProd, NestedValue.leafAbs]
        rw [nat_one_sub_fsum]
    _ = ∏ i ∈ Finset.range κ.2.length, (κ.2.getD i 0 + ((1 : ℕ) - κ.2.getD i 0 : ℕ)) :=
        hprod.symm
    _ = 1 := Finset.prod_eq_one fun i _ => nat_add_one_sub _ (hle i)

omit [ValueType T] in
theorem nat_sum_foldr_addLeaf : ∀ (s : Multiset (LeafKey T ℕ)),
    (∀ κ ∈ s, ∀ k ∈ κ.2, k ≤ 1) →
    ((s.foldr NestedValue.addLeaf {0}).map (fun L => (L.map natLeafW).prod)).sum = 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons κ s ih =>
    intro h
    rw [Multiset.foldr_cons, NestedValue.addLeaf, Multiset.map_bind, Multiset.sum_bind]
    have ih' := ih fun κ' hκ' => h κ' (Multiset.mem_cons_of_mem hκ')
    calc _ = (((Finset.range κ.2.length).powerset.val).map (fun S => natLeafW (κ, S))).sum := by
          refine congrArg Multiset.sum (Multiset.map_congr rfl fun S _ => ?_)
          simp only [Multiset.map_map, Function.comp_def, Multiset.map_cons,
            Multiset.prod_cons]
          rw [Multiset.sum_map_mul_left, ih', mul_one]
      _ = 1 := nat_sum_leafChoices κ (h κ (Multiset.mem_cons_self _ _))

omit [ValueType T] in
theorem nat_sum_foldr_addNode : ∀ (s : Multiset (Σ j, NodeKey T ℕ j)),
    (∀ κ ∈ s, ∀ o ∈ κ.2.2, o.2 ≤ 1) →
    ((s.foldr NestedValue.addNode {0}).map
      (fun N => (N.map (fun e => natDecW e.2.2)).prod)).sum = 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons κ s ih =>
    intro h
    rw [Multiset.foldr_cons, NestedValue.addNode, Multiset.map_bind, Multiset.sum_bind]
    have ih' := ih fun κ' hκ' => h κ' (Multiset.mem_cons_of_mem hκ')
    calc _ = ((NestedValue.memChoices κ.2.2).map natDecW).sum := by
          refine congrArg Multiset.sum (Multiset.map_congr rfl fun D _ => ?_)
          simp only [Multiset.map_map, Function.comp_def, Multiset.map_cons,
            Multiset.prod_cons]
          rw [Multiset.sum_map_mul_left, ih', mul_one]
      _ = 1 := nat_sum_memChoices κ.2.2 (h κ (Multiset.mem_cons_self _ _))

omit [ValueType T] in
/-- **The worlds of a nested value weigh `𝟙` together** when every
annotation, at every storey, is at most `𝟙`. -/
theorem NestedValue.nat_sum_worlds_ann [DecidableEq T] (a : NestedValue T ℕ)
    (h : a.AnnsIn (· ≤ 1)) :
    (a.worlds.map NestedValue.World.ann).sum = 1 := by
  classical
  have hl : ∀ κ ∈ a.leaves, ∀ k ∈ κ.2, k ≤ 1 := fun κ hκ k hk => by
    obtain ⟨o, ho, hκo⟩ := Multiset.mem_bind.mp (Multiset.mem_dedup.mp hκ)
    exact NestInner.AnnsIn.leaves _ o.1 (h o ho).2 κ hκo k hk
  have hn : ∀ κ ∈ a.nodes, ∀ o ∈ κ.2.2, o.2 ≤ 1 := fun κ hκ o' ho' => by
    unfold NestedValue.nodes at hκ
    obtain ⟨o, ho, hκo⟩ := Multiset.mem_bind.mp (Multiset.mem_dedup.mp hκ)
    exact NestInner.AnnsIn.nodes _ o.1 (h o ho).2 _ hκo _ ho'
  unfold NestedValue.worlds
  simp only [Multiset.map_bind, Multiset.sum_bind, Multiset.map_map, Function.comp_def,
    nat_world_ann]
  calc _ = ((NestedValue.memChoices a.occs).map natDecW).sum := by
        refine congrArg Multiset.sum (Multiset.map_congr rfl fun R _ => ?_)
        calc _ = ((a.leaves.foldr NestedValue.addLeaf {0}).map (fun L =>
              natDecW R * (L.map natLeafW).prod)).sum := by
              refine congrArg Multiset.sum (Multiset.map_congr rfl fun L _ => ?_)
              rw [Multiset.sum_map_mul_left, nat_sum_foldr_addNode _ hn, mul_one]
          _ = natDecW R := by
              rw [Multiset.sum_map_mul_left, nat_sum_foldr_addLeaf _ hl, mul_one]
    _ = 1 := nat_sum_memChoices a.occs fun o ho => (h o ho).1

/-- **The worlds of one family weigh at most `𝟙` together.** -/
theorem classWorlds_weight_le {n : ℕ} (u : Tuple (GenValue T ℕ) n) (M : List (Fin n))
    (x₀ : AggTok T ℕ) (h : x₀.AnnsIn (· ≤ 1)) :
    ((classWorlds u M x₀).map worldWeight).sum ≤ 1 := by
  cases x₀ with
  | nest a =>
    simp only [classWorlds, Multiset.map_map]
    calc _ ≤ (a.worlds.map NestedValue.World.ann).sum :=
          nat_sum_filter_le a.worlds _ NestedValue.World.ann
      _ = 1 := NestedValue.nat_sum_worlds_ann a h
  | tok a =>
    rw [classWorlds_of_not_nest u M _ rfl, Multiset.map_map]
    have ha : (AggTok.tok a).flatExpr.AnnsIn (· ≤ 1) := AggExpr.annsIn_ofValue h
    exact nat_sum_worldAnn_le _ ha.anns _
  | expr e =>
    rw [classWorlds_of_not_nest u M _ rfl, Multiset.map_map]
    have ha : (AggTok.expr e).flatExpr.AnnsIn (· ≤ 1) := h
    exact nat_sum_worldAnn_le _ ha.anns _

open Classical in
/-- **The joint worlds of a row weigh at most `𝟙` together.** -/
theorem jointWorlds_weight_le {n : ℕ} (u : Tuple (GenValue T ℕ) n) (cols : List (Fin n))
    (hu : ∀ k a, u k = Sum.inr a → a.AnnsIn (· ≤ 1)) :
    ((jointWorlds u cols).map worldWeight).sum ≤ 1 := by
  unfold jointWorlds
  generalize ((tokCols u cols).map (fun p => p.2.classKey)).dedup = L
  induction L with
  | nil => simp [worldWeight]
  | cons φ L ih =>
    simp only [List.foldr_cons]
    split
    · exact ih
    · rename_i p₀ hf
      have hp₀ := mem_tokCols (List.mem_of_find?_eq_some hf)
      rw [Multiset.map_map]
      simp only [Function.comp_def, worldWeight_combineW]
      rw [nat_sum_product]
      exact nat_mul_le_one (classWorlds_weight_le u _ _ (hu _ _ hp₀.2)) ih

/-- **A selection's joint reading is at most `𝟙`** over `ℕ` when every
token of the row carries annotations at most `𝟙`. -/
theorem GenPredIn.predsemJ_le_one {c n : ℕ} {κ : Fin n → ColKind} (φ : GenPredIn T c κ)
    (neg : Bool) (u : Tuple (GenValue T ℕ) n) (γ : Fin c → T)
    (hu : ∀ k a, u k = Sum.inr a → a.AnnsIn (· ≤ 1)) : φ.predsemJ neg u γ ≤ 1 := by
  unfold GenPredIn.predsemJ
  refine le_trans (Multiset.sum_map_le_sum_map _ worldWeight fun w _ => ?_)
    (jointWorlds_weight_le u _ hu)
  unfold worldWeight
  split_ifs
  all_goals first | exact le_of_eq (mul_one _) | (rw [mul_zero]; exact Nat.zero_le _)

end JointWeights

/-! ## Every annotation a query without `ε` and `μ^∪` builds is at most `𝟙` -/

section Evaluate

variable {T : Type} [ValueType T]

/-- **A row's annotations are at most `𝟙`**: its concrete part and every
annotation the tokens it holds carry. Its pending factors are read only
through `δ`, which is at most `𝟙` whatever it reads. -/
def GenRow.Le1 {n : ℕ} (r : GenRow T ℕ n) : Prop :=
  r.snd.base ≤ 1 ∧ ∀ k a, r.fst k = Sum.inr a → a.AnnsIn (· ≤ 1)

omit [ValueType T] in
theorem GenRow.Le1.finalize {n : ℕ} {r : GenRow T ℕ n} (h : r.Le1) : r.snd.finalize ≤ 1 :=
  nat_mul_le_one h.1 (nat_mprod_le_one _ fun a ha => by
    obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 ha
    exact nat_delta_le_one _)

omit [ValueType T] in
theorem GenRow.le1_ofAnnotated {n : ℕ} {p : AnnotatedTuple T ℕ n} (h : p.2 ≤ 1) :
    (GenRow.ofAnnotated p).Le1 :=
  ⟨h, fun k a hk => by simp [GenRow.ofAnnotated] at hk⟩

theorem annsIn_tokenOf_le1 {c n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (X : AnnotatedRelation T ℕ n) (x : AnnotatedTuple T ℕ n) (γ : Fin c → T)
    (hX : ∀ q ∈ X, q.2 ≤ 1) (hx : x.2 ≤ 1) :
    (ValueFrame.tokenOfDist P O o w t f false X x γ).AnnsIn (· ≤ 1) := by
  have hU : ∀ q ∈ ValueFrame.frameListOf (α := AnnotatedTuple T ℕ n) Prod.fst P O o w X x,
      q.2 ≤ 1 := fun q hq => by
    rcases mem_frameListOf _ P O o w X x q hq with rfl | hq
    · exact hx
    · exact hX q hq
  simp only [ValueFrame.tokenOfDist, Bool.false_eq_true, ite_false]
  unfold ValueFrame.tokenOf
  split_ifs
  · exact AggValue.annsIn_ofGroup (Q := (· ≤ 1)) f t _ γ hU
  · exact AggValue.annsIn_ofScalarGroup (Q := (· ≤ 1)) f t _ γ hU

theorem annsIn_exprWhenOf_le1 {c n m p : ℕ} (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (w : ValueFrame T p) (t : TermIn T c n) (f : SeqAggFunc T)
    (keep : Tuple T n → Bool) (X : AnnotatedRelation T ℕ n) (x : AnnotatedTuple T ℕ n)
    (γ : Fin c → T) (hX : ∀ q ∈ X, q.2 ≤ 1) (hx : x.2 ≤ 1) :
    (ValueFrame.exprWhenOf P O o w t f false keep X x γ).AnnsIn (· ≤ 1) := by
  have hU : ∀ q ∈ ValueFrame.frameListOf (α := AnnotatedTuple T ℕ n) Prod.fst P O o w X x,
      q.2 ≤ 1 := fun q hq => by
    rcases mem_frameListOf _ P O o w X x q hq with rfl | hq
    · exact hx
    · exact hX q hq
  simp only [ValueFrame.exprWhenOf, Bool.false_eq_true, ite_false]
  exact AggExpr.annsIn_ofSeqWhen (Q := (· ≤ 1)) f t keep _ _ γ hU

/-- **Without `ε`, `μ^∪` and `DISTINCT` aggregates, every annotation a
query builds is at most `𝟙`** over `ℕ`, as soon as the instance's, the
context's tokens' and the rounds the holes are bound to are. -/
theorem le1_evaluate {d : AnnotatedDatabase T ℕ} {S : Set OpKind} (hS₁ : OpKind.dedup ∉ S)
    (hS₂ : OpKind.muSet ∉ S) {Θ : Set (SeqAggFunc T)} (hΘ : ∀ f : SeqAggFunc T, f.distinct ∉ Θ)
    (hD : ∀ k t (r : AnnotatedRelation T ℕ k), d.find k t = some r → ∀ a ∈ r, a.2 ≤ 1) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.inSig Θ → q.noExplode →
      ∀ (γ : Fin c → T) (E : EvalEnv T ℕ),
      (∀ k a, E.ctxAt c γ k = Sum.inr a → a.AnnsIn (· ≤ 1)) →
      (∀ p ∈ l, ∀ r ∈ E.holes p.1 p.2, r.Le1) →
      ∀ r ∈ q.evaluate d γ E, r.Le1 := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ _ γ E _ _ r hr
    revert hr
    simp only [AggQueryIn.evaluate]
    cases hf : d.find n s with
    | none => intro hr; exact absurd hr (Multiset.notMem_zero r)
    | some rn =>
      intro hr
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hr
      exact GenRow.le1_ofAnnotated (hD n s rn hf a ha)
  | Hole n s κ =>
    intro _ _ _ γ E _ hH r hr
    exact hH (s, n) (List.mem_singleton_self _) r (Multiset.mem_of_mem_filter hr)
  | Param pv ρ =>
    intro _ _ _ γ E hctx _ r hr
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows] at hr
    split at hr
    · rw [Multiset.mem_singleton] at hr
      subst hr
      refine ⟨le_refl 1, fun k a hk => ?_⟩
      revert hk
      show _root_.Sum.elim Sum.inl (E.ctxAt _ γ) (pv k) = Sum.inr a → a.AnnsIn (· ≤ 1)
      cases pv k with
      | inl v => intro hk; simp at hk
      | inr j => intro hk; exact hctx j a hk
    · exact absurd hr (Multiset.notMem_zero r)
  | Empty => intro _ _ _ _ _ _ _ r hr; exact absurd hr (Multiset.notMem_zero r)
  | Proj ps q ih =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨hb, ht⟩ := ih hu.2 hi.2 hx γ E hctx hH r₀ hr₀
    refine ⟨nat_mul_le_one hb (nat_mprod_le_one _ fun a ha => ?_),
      fun j a hj => ProjColIn.annsIn_eval (ps j) γ ht hj⟩
    obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 ha
    exact nat_delta_le_one _
  | Sel φ q hφ ih =>
    intro hu hi hx γ E hctx hH r hr
    have ih' := ih hu.2 hi.2 hx γ E hctx hH
    dsimp only [AggQueryIn.evaluate] at hr
    by_cases hagg : φ.hasAggAtom = true
    · rw [ite_eq_left hagg] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
      obtain ⟨hb, ht⟩ := ih' r₀ hr₀
      exact ⟨nat_mul_le_one hb (GenPredIn.predsemJ_le_one φ false r₀.fst γ ht), ht⟩
    · rw [ite_eq_right hagg] at hr
      exact ih' r (Multiset.mem_of_mem_filter hr)
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨hxm, hym⟩ := Multiset.mem_product.1 hxy
    obtain ⟨bx, tx⟩ := ih₁ hu.2.1 hi.1 hx.1 γ E hctx
      (fun p hp => hH p (List.mem_append_left _ hp)) x hxm
    obtain ⟨b_y, ty⟩ := ih₂ hu.2.2 hi.2 hx.2 γ E hctx
      (fun p hp => hH p (List.mem_append_right _ hp)) y hym
    refine ⟨nat_mul_le_one bx b_y, fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk; exact tx i a hk
    · simp only [Fin.append_right] at hk; exact ty i a hk
  | Apply q₁ q₂ ih₁ ih₂ =>
    rename_i c' n₁ n₂ κ₁ κ₂ l'
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hxm, hr⟩ := Multiset.mem_bind.1 hr
    obtain ⟨y, hym, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨bx, tx⟩ := ih₁ hu.2.1 hi.1 hx.1 γ E hctx hH x hxm
    obtain ⟨b_y, ty⟩ := ih₂ hu.2.2 hi.2 hx.2 _ _ (fun k a hk => by
      rw [EvalEnv.ctxAt_withCtx] at hk
      revert hk
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]; exact tx i a
      · rw [Fin.append_right]; exact hctx i a) (fun p hp => absurd hp List.not_mem_nil) y hym
    refine ⟨nat_mul_le_one bx b_y, fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk; exact tx i a hk
    · simp only [Fin.append_right] at hk; exact ty i a hk
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.1 hr with hr | hr
    · exact ih₁ hu.2.1 hi.1 hx.1 γ E hctx (fun p hp => hH p (List.mem_append_left _ hp)) r hr
    · exact ih₂ hu.2.2 hi.2 hx.2 γ E hctx (fun p hp => hH p (List.mem_append_right _ hp)) r hr
  | Dedup q ih => exact fun hu => absurd hu.1 hS₁
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hr
    obtain ⟨p₀, hp₀, rfl⟩ := Multiset.mem_map.1 hp
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp₀
    refine GenRow.le1_ofAnnotated (le_trans (Nat.sub_le _ _) ?_)
    exact (ih₁ hu.2.1 hi.1 hx.1 γ E hctx hH r₀ hr₀).finalize
  | Explode k hk q ih => exact fun _ _ hx => hx.elim
  | Retag hk q ih =>
    intro hu hi hx γ E hctx hH r hr
    exact ih hu hi hx γ E hctx hH r hr
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    refine forall_mem_muSumFix (P := GenRow.Le1) (fun X hX y hy => ?_)
      (ih₀ hu.2.1 hi.1 hx.1 γ E hctx (fun p hp => absurd hp List.not_mem_nil)) r hr
    refine ih₁ hu.2.2 hi.2 hx.2 γ _ (by simpa only [EvalEnv.ctxAt_assignHole] using hctx)
      (fun p hp r' hr' => ?_) y hy
    obtain rfl := List.mem_singleton.1 hp
    dsimp only at hr'
    rw [EvalEnv.assignHole_holes_self] at hr'
    exact hX r' hr'
  | MuSet s q₀ q₁ ih₀ ih₁ => exact fun hu => absurd hu.1 hS₂
  | Gamma is ts fs q keep ord ih =>
    rename_i c' m n₁ n₂ _ _
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨kv, hkv, rfl⟩ := Multiset.mem_map.1 hr
    set R := (q.evaluate d γ E).map GenRow.toAnnotated with hR
    have hRb : ∀ p ∈ R, p.2 ≤ 1 := by
      intro p hp
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hp
      exact (ih hu.2 hi.2.2.2 hx γ E hctx hH r₀ hr₀).finalize
    have hU : ∀ x ∈ Having.havingGroupOrd is ord R kv.1, x.2 ≤ 1 := by
      intro x hx'
      rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe] at hx'
      exact hRb x (Multiset.mem_of_mem_filter hx')
    refine ⟨le_refl 1, fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk; simp at hk
    · simp only [Fin.append_right, Sum.inr.injEq] at hk
      subst hk
      rw [AggTok.AnnsIn_setFam]
      split
      · exact AggValue.annsIn_ofGroup (Q := (· ≤ 1)) _ _ _ γ hU
      · exact AggExpr.annsIn_ofSeqWhen (Q := (· ≤ 1)) _ _ _ _ _ γ hU
  | GammaScalar ts fs q ord ih =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate, Multiset.mem_singleton] at hr
    subst hr
    refine ⟨le_refl 1, fun k a hk => ?_⟩
    simp only [Sum.inr.injEq] at hk
    subst hk
    rw [AggTok.AnnsIn_setFam]
    refine AggValue.annsIn_ofScalarGroup (Q := (· ≤ 1)) _ _ _ γ fun x hx' => ?_
    rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe] at hx'
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_filter hx')
    exact (ih hu.2 hi.2.2 hx γ E hctx hH r₀ hr₀).finalize
  | GammaNest is his p g q ih =>
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨gk, -, rfl⟩ := Multiset.mem_map.1 hr
    have hb := ih hu.2 hi.2.2 hx γ E hctx hH
    refine ⟨le_refl 1, fun k a hk => ?_⟩
    refine Fin.addCases (fun i hk => ?_) (fun i hk => ?_) k hk
    · simp only [Fin.append_left] at hk; simp at hk
    · simp only [Fin.append_right, Sum.inr.injEq] at hk
      subst hk
      intro o ho
      simp only [nestOfGroup, nestOfVals, NestedValue.occs_ofOccs, Multiset.map_map] at ho
      obtain ⟨row, hrow, rfl⟩ := Multiset.mem_map.1 ho
      have hrow' := hb row (Multiset.mem_of_mem_filter hrow)
      exact ⟨hrow'.finalize, GenValue.annsIn_innerAt _ (fun a ha =>
        ProjColIn.annsIn_eval p γ hrow'.2 ha) _⟩
  | ProvSum is his t q ih => exact fun hu => hu.elim
  | GammaTok is his ts fs a q keep ih => exact fun hu => hu.elim
  | Win P O o w t g q hrr dist keep ih =>
    rename_i c' n' m' p' κ' _ _ _
    intro hu hi hx γ E hctx hH r hr
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨x, hxm, rfl⟩ := Multiset.mem_map.1 hr
    have hdist : dist = false := by
      cases dist with
      | false => rfl
      | true => exact absurd hi.2.1 (hΘ g)
    subst hdist
    have hb := ih hu.2 hi.2.2.2.2 hx γ E hctx hH
    have hX : ∀ y ∈ (q.evaluate d γ E).map (GenRow.readAnnotated κ'), y.2 ≤ 1 := by
      intro y hy
      obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hy
      exact (hb r₀ hr₀).finalize
    obtain ⟨bx, tx⟩ := hb x hxm
    refine ⟨bx, fun k a hk => ?_⟩
    simp only [ValueFrame.windowGenRow] at hk
    refine Fin.lastCases (fun hk => ?_) (fun i hk => ?_) k hk
    · rw [Fin.snoc_last, Sum.inr.injEq] at hk
      subst hk
      rw [AggTok.AnnsIn_setFam]
      split
      · exact annsIn_tokenOf_le1 P O o w t g _ _ γ hX ((hb x hxm).finalize)
      · exact annsIn_exprWhenOf_le1 P O o w t g _ _ _ γ hX ((hb x hxm).finalize)
    · rw [Fin.snoc_castSucc] at hk; exact tx i a hk
  | WinExpr P O o ws ts fs g q keeps ih => exact fun _ hi => hi.elim

end Evaluate

/-! ## The witness -/

/-- **`count` is not its own distinct version**: on `[0, 0]` the one
reads `2`, the other `1`. So a `DISTINCT` window is out of the minimal
signature. -/
theorem count_distinct_ne (f : SeqAggFunc ℕ) : f.distinct ∉ ({SeqAggFunc.count} : Set _) := by
  intro h
  rw [Set.mem_singleton_iff] at h
  have h₂ : f.distinct [0, 0] = 2 := by rw [h]; rfl
  have h₁ : f.distinct [0] = 1 := by rw [h]; rfl
  have he : f.distinct [0, 0] = f.distinct [0] := by
    unfold SeqAggFunc.distinct
    congr 2
  omega

/-- **`ε(R)`.** -/
def epsWitness : AggQuery ℕ 1 (ColKind.allReg 1) := AggQueryIn.Dedup (AggQueryIn.Rel 1 "R")

/-- **The instance it tells apart from every query without `ε` and `μ^∪`**:
`R` holds `0` twice, annotated `𝟙`. -/
def dEps : AnnotatedDatabase ℕ ℕ :=
  AnnotatedDatabase.assign "R"
    (({(((fun _ => 0) : Tuple ℕ 1), 1), (((fun _ => 0) : Tuple ℕ 1), 1)}
      : Multiset (AnnotatedTuple ℕ ℕ 1)) : AnnotatedRelation ℕ ℕ 1) []

theorem dEps_le1 : ∀ k t (r : AnnotatedRelation ℕ ℕ k), dEps.find k t = some r →
    ∀ a ∈ r, a.2 ≤ 1 := by
  intro k t r hr a ha
  unfold dEps at hr
  by_cases h₁ : k = 1 ∧ t = "R"
  · obtain ⟨rfl, rfl⟩ := h₁
    rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
    subst hr
    have : a.2 = 1 := by
      rcases Multiset.mem_cons.1 ha with rfl | ha
      · rfl
      · rw [Multiset.mem_singleton] at ha; subst ha; rfl
    rw [this]
  · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h₁] at hr
    exact absurd hr (by
      rw [show AnnotatedDatabase.find k t ([] : AnnotatedDatabase ℕ ℕ) = none from rfl]
      simp)

/-- **`ε(R)` there holds `0` annotated `2`.** -/
theorem mem_evaluateAnnotated_epsWitness :
    ((((fun _ => 0) : Tuple ℕ 1), 2) : AnnotatedTuple ℕ ℕ 1)
      ∈ epsWitness.evaluateAnnotated dEps (fun _ => 0) := by
  show _ ∈ epsWitness.ann dEps (fun _ => 0) {}
  rw [epsWitness, AggQueryIn.ann_dedup, AggQueryIn.ann_Rel, dEps, AnnotatedDatabase.find_assign]
  dsimp only
  unfold PathSum.dedupK
  refine Multiset.mem_map.2 ⟨(fun _ => 0), Multiset.mem_dedup.2 (Multiset.mem_map.2
    ⟨_, Multiset.mem_cons_self _ _, rfl⟩), ?_⟩
  refine Prod.ext rfl ?_
  dsimp only
  unfold PathSum.wt
  rfl

theorem overSchema_epsWitness : epsWitness.overSchema schemaR := by
  simp [epsWitness, AggQueryIn.overSchema, schemaR_apply]

theorem usesOnly_epsWitness : epsWitness.usesOnly plainRecOps :=
  ⟨by simp [plainRecOps, plainOps, basisDD, basisOps], trivial⟩

/-- **`ε` or `μ^∪` is in every set generating the annotated algebra over
`ℕ`**: without them every annotation a query of the minimal signature
builds is at most `𝟙` when the instance's are (`le1_evaluate`), and
`ε(R)` gives `2` on `dEps`. -/
theorem dedup_or_muSet_mem_of_generatesAnn {S : Set OpKind}
    (h : GeneratesAnn ℕ ℕ schemaR SeqAggFunc.count S) :
    OpKind.dedup ∈ S ∨ OpKind.muSet ∈ S := by
  by_contra hS
  rw [not_or] at hS
  obtain ⟨q', -, hu', hi', ha', -, hm⟩ := h epsWitness overSchema_epsWitness
    usesOnly_epsWitness trivial trivial trivial
  obtain ⟨-, he⟩ := hm dEps (fun _ => 0) trivial
  have hmem := mem_evaluateAnnotated_epsWitness
  rw [← he] at hmem
  obtain ⟨r, hr, hre⟩ := Multiset.mem_map.1 hmem
  have hz := (le1_evaluate hS.1 hS.2 count_distinct_ne dEps_le1 q' hu' hi' ha'
    (fun _ => 0) {} (fun k => k.elim0) (fun p hp => absurd hp List.not_mem_nil)
    r hr).finalize
  have hfin : r.snd.finalize = 2 := congrArg Prod.snd hre
  omega

/-! ## The basis with `ε` is minimal -/

/-- **No proper subset of `{∅, Π, σ, apply, γ, win, μ^⊎, ε, −}` generates
the annotated algebra over both `ℕ` and `ℕ × ℕ`**, with the counting
aggregate: `∅`, `Π`, `γ`, `μ^⊎`, `win` and `σ` are inherited from the
plain rows, the apply because `×` is not in the set, `−` by the
zero-pattern invariant over `ℕ × ℕ`, and `ε` because `μ^∪` is not in the
set. -/
theorem annEpsOps_minimal {S : Set OpKind} (hS : S ⊆ annEpsOps)
    (hN : ∀ sch : Schema, GeneratesAnn ℕ ℕ sch SeqAggFunc.count S)
    (hP : ∀ sch : Schema, GeneratesAnn ℕ NatPair sch SeqAggFunc.count S) :
    S = annEpsOps := by
  refine Set.Subset.antisymm hS fun x hx => ?_
  have hout : ∀ y, y ∈ S → y ∉ annEpsOps → False := fun y hy hn => hn (hS hy)
  obtain ⟨he, hp, hg, hmu, hw, hsel, hpa⟩ := required_mem_of_generatesAnn hN
  cases x with
  | empty => exact he
  | proj => exact hp
  | sel => exact hsel
  | prod => exact absurd hx (by simp [annEpsOps])
  | apply =>
    rcases hpa with h | h
    · exact (hout _ h (by simp [annEpsOps])).elim
    · exact h
  | union => exact absurd hx (by simp [annEpsOps])
  | dedup =>
    rcases dedup_or_muSet_mem_of_generatesAnn (hN schemaR) with h | h
    · exact h
    · exact (hout _ h (by simp [annEpsOps])).elim
  | diff => exact diff_mem_of_generatesAnn (hP schemaRS)
  | gamma => exact hg
  | win => exact hw
  | muBag => exact hmu
  | muSet => exact absurd hx (by simp [annEpsOps])
