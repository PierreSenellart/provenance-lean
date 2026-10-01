/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggQueryAdequacy
import Provenance.Window

/-!
# A window over a whole partition is a join with its grouping

A window whose frame is the whole partition asks of each row exactly what a
grouping asks of its group. It should therefore be expressible without a
window at all: join every row with the group row of its own partition, and
keep the group's aggregate column.

That is what this module proves, over plain relations and over annotated
ones. The plain statement is a rearrangement. The annotated statement is
not: the join carries the group's existence factor `δ(⊕ U)` into the row's
annotation, which the window never produces, and the two agree only because
the group of a row *contains that row* – so the factor reads
`α ⊗ δ(α ⊕ β')`, which is `α` by δ-absorption. A frame that excluded the
current row would have no such identity, and no such rewriting.
-/

variable {T K : Type} {n m p : ℕ} [ValueType T]
variable [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

namespace ValueFrame

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **The whole partition is the group.** With the whole-partition frame, an
occurrence's frame is its partition, and its token is the token its
partition's group would carry. -/
theorem tokenOf_whole (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (ho : ∀ y z : Tuple T p, o.peer y z = true)
    (t : Term T n) (f : SeqAggFunc T)
    (X : Multiset (AnnotatedTuple T K n)) {x : AnnotatedTuple T K n}
    (hx : x ∈ X) :
    tokenOf P O o (whole : ValueFrame T p) t f X x
      = AggValue.ofGroup f t (Having.havingGroup P X (Tuple.key P x.fst)) := by
  have hpeer := frameListOf_of_peer (α := AnnotatedTuple T K n) Prod.fst P O o
    (whole : ValueFrame T p) X x ho (fun _ _ hab => ValueFrame.le_fst_of_le hab)
  have hs : (whole : ValueFrame T p).s (Tuple.key O x.fst) = true := rfl
  have hfil : frameOf (α := AnnotatedTuple T K n) Prod.fst P O whole X x
      = X.filter (fun y : AnnotatedTuple T K n =>
          ∀ k : Fin m, y.fst (P k) = x.fst (P k)) := by
    rw [frameOf_whole (α := AnnotatedTuple T K n) Prod.fst P O X hx]
    refine Multiset.filter_congr (fun y _ => ⟨fun h k => congrFun h k, fun h => ?_⟩)
    funext k
    exact h k
  unfold tokenOf
  rw [ite_eq_left hs, hpeer, hfil]
  rfl

end ValueFrame

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The group sequence of a key is the sorted list of the rows carrying
it. -/
theorem groupSeq_eq_sortList (P : Tuple (Fin n) m) (r : Relation T n)
    (g : Tuple T m) :
    Relation.groupSeq P r g
      = sortList (r.filter (fun u => ∀ k : Fin m, u (P k) = g k)) :=
  sortList_eq (Multiset.pairwise_sort _ _) (Multiset.sort_eq _ _)

/-! ## The join picks one group per row -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K] in
/-- **Joining on a key picks out one entry per row.** A table with distinct
keys, joined with a relation on the key, gives each row exactly the entry of
its own key – so the join has as many rows as the relation, one per row. -/
theorem filter_product_key {α β γ : Type} [DecidableEq γ]
    (R : Multiset α) (key : α → γ) (Keys : Multiset γ) (hK : Keys.Nodup)
    (hmem : ∀ a ∈ R, key a ∈ Keys) (row : γ → β)
    (P' : α × β → Prop) (inst : DecidablePred P')
    (hP : ∀ (a : α) (g : γ), P' (a, row g) ↔ key a = g) :
    @Multiset.filter _ P' inst (R.product (Keys.map row))
      = R.map (fun a => (a, row (key a))) := by
  let _ := inst
  induction R using Multiset.induction_on with
  | empty => rfl
  | cons a R ih =>
    have hfil : Multiset.filter (fun g => P' (a, row g)) Keys = {key a} := by
      rw [Multiset.filter_congr (fun g _ => hP a g), Multiset.filter_eq,
        Multiset.count_eq_one_of_mem hK (hmem a (Multiset.mem_cons_self a R))]
      rfl
    have hone : Multiset.filter P'
        (Multiset.map (Prod.mk a) (Multiset.map row Keys))
        = {(a, row (key a))} := by
      rw [Multiset.map_map, Multiset.filter_map]
      exact congrArg (Multiset.map (Prod.mk a ∘ row)) hfil
    rw [show (a ::ₘ R).product (Keys.map row) = (a ::ₘ R) ×ˢ (Keys.map row) from rfl,
      Multiset.cons_product, Multiset.filter_add, hone, Multiset.map_cons,
      show R ×ˢ Multiset.map row Keys = R.product (Multiset.map row Keys) from rfl,
      ih (fun b hb => hmem b (Multiset.mem_cons_of_mem hb))]
    rfl

namespace AggQueryIn

/-! ## The window written as a join

The composite is the one of the semantics: join the query with its own
grouping on the partition key, keep the original columns and the group's
aggregate column. -/

/-- The kind vector of a query joined with its grouping: the query's own
columns, then the group key, then the aggregate token. -/
abbrev winJoinKinds (n m : ℕ) : Fin (n + (m + 1)) → ColKind :=
  Fin.append (ColKind.allReg n) (ColKind.gammaKinds m 1)

/-- The position of an original column in the join. -/
abbrev winLeftPos (m : ℕ) (k : Fin n) : Fin (n + (m + 1)) := Fin.castAdd (m + 1) k

/-- The position of a group-key column in the join. -/
abbrev winKeyPos (n : ℕ) (j : Fin m) : Fin (n + (m + 1)) :=
  Fin.natAdd n (Fin.castAdd 1 j)

/-- The position of the aggregate column in the join. -/
abbrev winAggPos (n m : ℕ) : Fin (n + (m + 1)) := Fin.natAdd n (Fin.natAdd m 0)

theorem winLeftPos_kind (k : Fin n) : winJoinKinds n m (winLeftPos m k) = ColKind.reg :=
  Fin.append_left _ _ k

theorem winKeyPos_kind (j : Fin m) : winJoinKinds n m (winKeyPos n j) = ColKind.reg :=
  (Fin.append_right (ColKind.allReg n) (ColKind.gammaKinds m 1) _).trans
    (Fin.append_left _ _ j)

theorem winAggPos_kind : winJoinKinds n m (winAggPos n m) = ColKind.agg :=
  (Fin.append_right (ColKind.allReg n) (ColKind.gammaKinds m 1) _).trans
    (Fin.append_right _ _ 0)

/-- The projection keeping the original columns and the aggregate. -/
def winProj (n m : ℕ) : Tuple (ProjCol T (winJoinKinds n m)) (n + 1) :=
  Fin.snoc (fun k : Fin n => ProjColIn.term (TermGIn.index (winLeftPos m k) (winLeftPos_kind k)))
    (ProjColIn.token (winAggPos n m) winAggPos_kind)

omit [ValueType T] in
theorem winProj_kinds (n m : ℕ) :
    (fun j => ((winProj (T := T) n m) j).kind)
      = Fin.snoc (ColKind.allReg n) ColKind.agg := by
  funext j
  induction j using Fin.lastCases with
  | last => rw [winProj, Fin.snoc_last, Fin.snoc_last]; rfl
  | cast k => rw [winProj, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl

/-- **A window over a whole partition, written without a window**: join the
query with its grouping on the partition key, and keep the group's
aggregate column. -/
def winByJoin (P : Tuple (Fin n) m) (t : Term T n) (f : SeqAggFunc T)
    (q : AggQuery T n (ColKind.allReg n)) :
    AggQuery T (n + 1) (Fin.snoc (ColKind.allReg n) ColKind.agg) :=
  AggQueryIn.castKind (winProj_kinds n m)
    (AggQueryIn.Proj (winProj n m)
      (AggQueryIn.Sel
        (keyJoinCond (fun k : Fin m => winLeftPos m (P k)) (winKeyPos n)
          (fun k => winLeftPos_kind (P k)) winKeyPos_kind)
        (AggQueryIn.Prod q (AggQueryIn.Gamma P ![t] ![f] q))))

/-! ## Over plain relations -/

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- The key columns of the join read the partition key on the left and the
group key on the right. -/
theorem keyJoinCond_append (P : Tuple (Fin n) m) (u : Tuple T n)
    (y : Tuple T (m + 1)) :
    (keyJoinCond (T' := T) (fun k : Fin m => winLeftPos m (P k)) (winKeyPos n)
        (fun k => winLeftPos_kind (P k)) winKeyPos_kind).holdsPlain
      (Fin.append u y)
      ↔ ∀ k : Fin m, u (P k) = y (Fin.castAdd 1 k) := by
  rw [keyJoinCond_holdsPlain]
  exact forall_congr' (fun k => by
    rw [Fin.append_left, Fin.append_right])

/-- **A window over a whole partition is a join with its grouping**, over
plain relations: each row is matched with the group row of its own
partition, and keeps that group's aggregate.

The join is written with `IS NOT DISTINCT FROM` on the partition key, which
is the syntactic equality a window partitions by: two rows with a null key
are one partition, and land in one group. -/
theorem evaluatePlain_winByJoin (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (ho : ∀ y z : Tuple T p, o.peer y z = true)
    (t : Term T n) (f : SeqAggFunc T) (q : AggQuery T n (ColKind.allReg n))
    (d : Database T) :
    (winByJoin P t f q).evaluatePlain d
      = (AggQueryIn.Win P O o (ValueFrame.whole : ValueFrame T p) t f q).evaluatePlain d := by
  rw [winByJoin, AggQueryIn.evaluatePlain_castKind, AggQueryIn.evaluatePlain_Win_eq]
  simp only [AggQueryIn.evaluatePlain]
  generalize hr : q.evaluatePlain d = r
  set Keys : Multiset (Tuple T m) :=
    (Multiset.map (fun (u : Tuple T n) (k : Fin m) => u (P k)) r).dedup with hKeys
  have hmul : ∀ (A : Relation T n) (B : Relation T (m + 1)),
      A * B = Multiset.map
        (fun xy : Tuple T n × Tuple T (m + 1) => Fin.append xy.fst xy.snd)
        (Multiset.product A B) := fun _ _ => rfl
  -- each row is joined with the group row of its own partition, and no other
  rw [hmul, Multiset.filter_map, Multiset.map_map]
  refine Eq.trans (congrArg (Multiset.map _)
    (filter_product_key (γ := Tuple T m) r
      (fun u : Tuple T n => Tuple.key P u) Keys (Multiset.nodup_dedup _)
      (fun u hu => Multiset.mem_dedup.mpr (Multiset.mem_map_of_mem _ hu))
      (fun g : Tuple T m => (Fin.append g (fun j => ![f] j
        (List.map (![t] j).eval (Relation.groupSeq P r g))) : Tuple T (m + 1)))
      _ _ (fun u g => by
        show (keyJoinCond (T' := T) (fun k : Fin m => winLeftPos m (P k)) (winKeyPos n)
          (fun k => winLeftPos_kind (P k)) winKeyPos_kind).holdsPlain
          (Fin.append u _) ↔ _
        rw [keyJoinCond_append]
        dsimp only
        constructor
        · intro h
          funext k
          exact (h k).trans (Fin.append_left _ _ k)
        · intro h k
          rw [Fin.append_left]
          exact congrFun h k))) ?_
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun u hu => ?_)
  funext j
  induction j using Fin.lastCases with
  | last =>
    dsimp only [Function.comp_apply]
    rw [winProj, Fin.snoc_last, Fin.snoc_last]
    simp only [ProjColIn.evalPlain, winAggPos, Fin.append_right]
    show f (List.map t.eval (Relation.groupSeq P r (Tuple.key P u)))
      = ValueFrame.windowValue P O o ValueFrame.whole t f r u
    unfold ValueFrame.windowValue
    rw [ValueFrame.frameListOf_of_peer (α := Tuple T n) id P O o
        (ValueFrame.whole : ValueFrame T p) r u ho (fun _ _ h => h),
      groupSeq_eq_sortList,
      ValueFrame.frameOf_whole (α := Tuple T n) id P O r hu]
    refine congrArg (fun M => f ((sortList M).map t.eval)) ?_
    exact Multiset.filter_congr (fun v _ =>
      ⟨fun h => funext h, fun h k => congrFun h k⟩)
  | cast k =>
    dsimp only [Function.comp_apply]
    rw [winProj, Fin.snoc_castSucc, Fin.snoc_castSucc]
    simp only [ProjColIn.evalPlain, TermGIn.evalPlain, winLeftPos, Fin.append_left]

/-! ## Over annotated relations -/

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- On a lifted tuple the join condition reads the partition key on the left
and the group key on the right. -/
theorem keyJoinCond_holds_append (P : Tuple (Fin n) m)
    (u : Tuple (GenValue T K) n) (y : Tuple (GenValue T K) (m + 1)) :
    (keyJoinCond (T' := T) (fun k : Fin m => winLeftPos m (P k)) (winKeyPos n)
        (fun k => winLeftPos_kind (P k)) winKeyPos_kind).holds (Fin.append u y)
      ↔ ∀ k : Fin m, GenRow.plainTuple u (P k)
          = GenRow.plainTuple y (Fin.castAdd 1 k) := by
  rw [keyJoinCond_holds]
  refine forall_congr' (fun k => ?_)
  unfold GenRow.plainTuple
  rw [Fin.append_left, Fin.append_right]

/-- **A window over a whole partition is a join with its grouping**, over
annotated relations: the same rows with the same tokens, and the same
annotations. The join carries the group's existence factor `δ(⊕ U)` that the
window never produces, and the two agree only because the group of a row
*contains that row* – so the factor reads `α ⊗ δ(α ⊕ β')`, which is `α` by
δ-absorption. A frame excluding the current row would have no such identity,
and no such rewriting. -/
theorem evaluate_winByJoin (P : Tuple (Fin n) m) (O : Tuple (Fin n) p)
    (o : OrderSpec p) (ho : ∀ y z : Tuple T p, o.peer y z = true)
    (t : Term T n) (f : SeqAggFunc T) (q : AggQuery T n (ColKind.allReg n))
    (d : AnnotatedDatabase T K) :
    ((winByJoin P t f q).evaluate d).map (fun r => (r.fst, r.snd.finalize))
      = ((AggQueryIn.Win P O o (ValueFrame.whole : ValueFrame T p) t f q).evaluate d).map
          (fun r => (r.fst, r.snd.finalize)) := by
  have hagg : (keyJoinCond (T' := T) (fun k : Fin m => winLeftPos m (P k)) (winKeyPos n)
      (fun k => winLeftPos_kind (P k)) winKeyPos_kind).hasAggAtom = false :=
    keyJoinCond_hasAggAtom _ _ _ _
  -- the grouping, written as one row per distinct partition key
  have hGamma : (AggQueryIn.Gamma P ![t] ![f] q).evaluate d
      = Multiset.map (fun g : Tuple T m =>
          ((Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
              (fun j => Sum.inr (AggTok.tok (AggValue.ofGroup (![f] j) (![t] j)
                (Having.havingGroup P (q.evaluateAnnotated d) g)))),
            ⟨1, {(Having.havingGroup P (q.evaluateAnnotated d) g).map Prod.snd}⟩)
            : GenRow T K (m + 1)))
        ((Multiset.map (fun p : AnnotatedTuple T K n => Tuple.key P p.fst)
          (q.evaluateAnnotated d)).dedup) := by
    conv_rhs =>
      rw [show Multiset.map (fun p : AnnotatedTuple T K n => Tuple.key P p.fst)
            (q.evaluateAnnotated d)
          = Multiset.map Prod.fst (Multiset.map
              (fun p : AnnotatedTuple T K n =>
                ((fun k => p.fst (P k), p.snd) : AnnotatedTuple T K m))
              (q.evaluateAnnotated d)) from
          (Multiset.map_map Prod.fst
            (fun p : AnnotatedTuple T K n =>
              ((fun k => p.fst (P k), p.snd) : AnnotatedTuple T K m))
            (q.evaluateAnnotated d)).symm,
        ← map_fst_groupByKey, Multiset.map_map]
    rfl
  rw [winByJoin, AggQueryIn.evaluate_castKind, AggQueryIn.evaluate_Win_eq]
  simp only [AggQueryIn.evaluate, hagg, Bool.false_eq_true, ite_false] at hGamma ⊢
  rw [hGamma, Multiset.filter_map, Multiset.map_map, Multiset.map_map]
  refine Eq.trans (congrArg (Multiset.map _)
    (filter_product_key (γ := Tuple T m) (q.evaluate d)
      (fun r : GenRow T K n => Tuple.key P (GenRow.plainTuple r.fst))
      ((Multiset.map (fun p : AnnotatedTuple T K n => Tuple.key P p.fst)
        (q.evaluateAnnotated d)).dedup) (Multiset.nodup_dedup _)
      (fun r hr => Multiset.mem_dedup.mpr (by
        refine Multiset.mem_map.mpr ⟨GenRow.toAnnotated r, ?_, rfl⟩
        exact Multiset.mem_map_of_mem _ hr))
      (fun g : Tuple T m =>
        ((Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
            (fun j => Sum.inr (AggTok.tok (AggValue.ofGroup (![f] j) (![t] j)
              (Having.havingGroup P (q.evaluateAnnotated d) g)))),
          ⟨1, {(Having.havingGroup P (q.evaluateAnnotated d) g).map Prod.snd}⟩)
          : GenRow T K (m + 1)))
      _ _ (fun r g => by
        show (keyJoinCond (T' := T) (fun k : Fin m => winLeftPos m (P k)) (winKeyPos n)
          (fun k => winLeftPos_kind (P k)) winKeyPos_kind).holds
          (Fin.append r.fst _) ↔ _
        rw [keyJoinCond_holds_append]
        dsimp only
        have hy : ∀ k : Fin m, GenRow.plainTuple
            (Fin.append (fun k => (Sum.inl (g k) : GenValue T K))
              (fun j => Sum.inr (AggTok.tok (AggValue.ofGroup (![f] j) (![t] j)
                (Having.havingGroup P (q.evaluateAnnotated d) g)))))
            (Fin.castAdd 1 k) = g k := by
          intro k
          unfold GenRow.plainTuple
          rw [Fin.append_left]
          rfl
        constructor
        · intro h
          funext k
          exact (h k).trans (hy k)
        · intro h k
          rw [hy k]
          exact congrFun h k))) ?_
  unfold AggQueryIn.evaluateAnnotated
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl (fun r hr => ?_)
  dsimp only [Function.comp_apply]
  have hmemX : GenRow.toAnnotated r
      ∈ Multiset.map GenRow.toAnnotated (q.evaluate d) :=
    Multiset.mem_map_of_mem _ hr
  -- the group of the row's own partition, which contains the row
  set U : List (AnnotatedTuple T K n) :=
    Having.havingGroup P (Multiset.map GenRow.toAnnotated (q.evaluate d))
      (Tuple.key P (GenRow.plainTuple r.fst)) with hU
  have hmemU : GenRow.toAnnotated r ∈ U := by
    rw [hU, ← Multiset.mem_coe, Having.havingGroup_coe]
    exact Multiset.mem_filter.mpr ⟨hmemX, fun k => rfl⟩
  -- the projected row: the original columns and the group's token
  have hu' : (fun j => (winProj n m j).eval (Fin.append r.fst
        (Fin.append (fun k => (Sum.inl (Tuple.key P (GenRow.plainTuple r.fst) k)
            : GenValue T K))
          (fun j => Sum.inr (AggTok.tok (AggValue.ofGroup (![f] j) (![t] j) U))))))
      = (Fin.snoc (fun k => (Sum.inl ((GenRow.toAnnotated r).fst k) : GenValue T K))
          (Sum.inr (AggTok.tok (AggValue.ofGroup f t U)))
            : Tuple (GenValue T K) (n + 1)) := by
    funext j
    induction j using Fin.lastCases with
    | last =>
      rw [winProj, Fin.snoc_last, Fin.snoc_last]
      show Fin.append r.fst _ (winAggPos n m) = _
      rw [Fin.append_right, Fin.append_right]
      rfl
    | cast k =>
      rw [winProj, Fin.snoc_castSucc, Fin.snoc_castSucc]
      show Sum.inl (AggValue.collapseSum (Fin.append r.fst _ (winLeftPos m k))) = _
      rw [Fin.append_left]
      rfl
  have htok : ValueFrame.tokenOf P O o (ValueFrame.whole : ValueFrame T p) t f
      (Multiset.map GenRow.toAnnotated (q.evaluate d)) (GenRow.toAnnotated r)
      = AggValue.ofGroup f t U :=
    ValueFrame.tokenOf_whole P O o ho t f _ hmemX
  refine Prod.ext ?_ ?_
  · simp only [ValueFrame.windowRow, ValueFrame.tokenOfDist_false, htok]
    exact hu'
  -- the token lists of the projected row are the group's occurrence
  -- annotations, so the join keeps exactly the group's factor pending
  have htl : tokenLists (fun j => (winProj n m j).eval (Fin.append r.fst
        (Fin.append (fun k => (Sum.inl (Tuple.key P (GenRow.plainTuple r.fst) k)
            : GenValue T K))
          (fun j => Sum.inr (AggTok.tok (AggValue.ofGroup (![f] j) (![t] j) U))))))
      = {U.map Prod.snd} := by
    rw [hu', tokenLists_snoc]
    show {List.map Prod.snd (List.map (fun p => (t.eval p.fst, p.snd)) U)} = _
    rw [List.map_map]
    rfl
  simp only [ValueFrame.windowRow, GenAnn.finalize_of_pending_zero]
  show ((r.snd.base * 1) * (Multiset.map (fun l => SemiringWithMonus.delta l.sum)
      (r.snd.pending + {U.map Prod.snd}
        - (r.snd.pending + {U.map Prod.snd}) ∩ _)).prod
    * (Multiset.map (fun l => SemiringWithMonus.delta l.sum)
        ((r.snd.pending + {U.map Prod.snd}) ∩ _)).prod : K) = _
  rw [htl,
    show (r.snd.pending + {U.map Prod.snd}) ∩ {U.map Prod.snd}
        = {U.map Prod.snd} from
      le_antisymm Multiset.inter_le_right
        (Multiset.le_inter (Multiset.le_add_left _ _) le_rfl),
    Multiset.add_sub_cancel_right, mul_one]
  -- the row's own annotation is one of the group's, so δ-absorption applies
  have hmemann : r.snd.finalize ∈ U.map Prod.snd :=
    List.mem_map_of_mem hmemU
  have hsum : (U.map Prod.snd).sum
      = r.snd.finalize + ((U.map Prod.snd).erase r.snd.finalize).sum :=
    (List.perm_cons_erase hmemann).sum_eq
  rw [Multiset.map_singleton, Multiset.prod_singleton, hsum]
  exact SemiringWithMonus.delta_absorb _ _

end AggQueryIn
