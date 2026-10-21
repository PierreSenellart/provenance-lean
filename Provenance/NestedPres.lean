/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.JointHom

/-!
# Nested values under a homomorphism, at every storey

A homomorphism `f : K → K'` relates an evaluation over `K` and one over
`K'` row by row, and a second-level aggregation builds, from two related
groups of rows, two nested values. Their worlds correspond
(`NestedValue.WCorr`), and that is what every reading of a nested value
asks of them: this module proves it at every storey (`wcorr_of_rel`).

The two values are related family by family (`NestInner.Rel`). An
expression family is presented on each side by a listing, the target's a
tie-block permutation of the source's pushed through `f`, through the same
readings (`ListingRel`); such a pair moves positions along a bijection
under which every selection reads the same rows (`ListingRel.move`, off
`TiePerm.exists_equiv`). A node's occurrences are the two sides of one
bag of pairs, annotations pushed through `f` and inner values related.
Where two related families have one key on one side exactly when they
have one on the other (`KeysFaithful` – which a coherent evaluation gives),
both sides' worlds are the images of one bag of indices: a decision over
the root's pairs, a set of positions of each expression family, and a
decision over the pairs of each node, chosen once per node (`Zof`).
-/

@[expose] public section


namespace TiePerm

variable {α γ : Type} {eqv : α → α → Prop}

/-- One position more at the front, kept at the front. -/
def liftEquiv {n m : ℕ} (π : Fin n ≃ Fin m) : Fin (n + 1) ≃ Fin (m + 1) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr π).trans (finSuccEquiv m).symm)

@[simp] theorem liftEquiv_zero {n m : ℕ} (π : Fin n ≃ Fin m) : liftEquiv π 0 = 0 := by
  simp [liftEquiv]

@[simp] theorem liftEquiv_succ {n m : ℕ} (π : Fin n ≃ Fin m) (i : Fin n) :
    liftEquiv π i.succ = (π i).succ := by
  simp [liftEquiv]

@[simp] theorem liftEquiv_symm_zero {n m : ℕ} (π : Fin n ≃ Fin m) : (liftEquiv π).symm 0 = 0 := by
  rw [Equiv.symm_apply_eq, liftEquiv_zero]

@[simp] theorem liftEquiv_symm_succ {n m : ℕ} (π : Fin n ≃ Fin m) (i : Fin m) :
    (liftEquiv π).symm i.succ = (π.symm i).succ := by
  rw [Equiv.symm_apply_eq, liftEquiv_succ, Equiv.apply_symm_apply]

theorem seqOf_cons_map {n : ℕ} (a : α) (t : List α)
    (π : Fin (n + 1) ≃ Fin (t.length + 1)) (W : Finset (Fin (n + 1))) :
    Having.seqOf (a :: t) (W.map π.toEmbedding)
      = (if π.symm 0 ∈ W then [a] else [])
        ++ Having.seqOf t (Finset.univ.filter (fun i => π.symm i.succ ∈ W)) := by
  show (if (0 : Fin (t.length + 1)) ∈ W.map π.toEmbedding then [a] else [])
      ++ Having.seqOf t (Finset.univ.filter (fun i => i.succ ∈ W.map π.toEmbedding)) = _
  simp only [Finset.mem_map_equiv]

/-- **A tie-block permutation moves the elements along a bijection of
positions**, and a selection carried along it reads the same rows, in the
same order, as long as tied elements read alike. -/
theorem exists_equiv (rd : α → γ) (hrd : ∀ {a b}, eqv a b → rd a = rd b) :
    ∀ {l₁ l₂ : List α}, TiePerm eqv l₁ l₂ →
      ∃ π : Fin l₁.length ≃ Fin l₂.length, (∀ i, l₂.get (π i) = l₁.get i)
        ∧ ∀ W : Finset (Fin l₁.length),
          (Having.seqOf l₂ (W.map π.toEmbedding)).map rd = (Having.seqOf l₁ W).map rd := by
  intro l₁ l₂ h
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => i.elim0, fun _ => rfl⟩
  | @cons a t₁ t₂ _ ih =>
    obtain ⟨π, hg, hs⟩ := ih
    refine ⟨liftEquiv π, fun i => ?_, fun W => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · erw [liftEquiv_zero]; rfl
      · erw [liftEquiv_succ]; exact hg j
    · erw [seqOf_cons_map a t₂, liftEquiv_symm_zero]
      show List.map rd (_ ++ _) = List.map rd (_ ++ _)
      rw [List.map_append, List.map_append]
      refine congrArg₂ (· ++ ·) rfl ?_
      rw [← hs]
      congr 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
        liftEquiv_symm_succ]
  | @swap a b hab t₁ t₂ _ ih =>
    obtain ⟨π, hg, hs⟩ := ih
    refine ⟨(Equiv.swap 0 1).trans (liftEquiv (liftEquiv π)), fun i => ?_, fun W => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
        erw [show (1 : Fin (t₁.length + 1 + 1)) = (0 : Fin (t₁.length + 1)).succ from rfl,
          liftEquiv_succ, liftEquiv_zero]
        rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp only [Equiv.trans_apply]
          erw [show (0 : Fin (t₁.length + 1)).succ = (1 : Fin (t₁.length + 1 + 1)) from rfl,
            Equiv.swap_apply_right, liftEquiv_zero]
          rfl
        · simp only [Equiv.trans_apply]
          erw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff])
            (by simp [Fin.ext_iff]), liftEquiv_succ, liftEquiv_succ]
          exact hg k
    · set π₂ := (Equiv.swap (0 : Fin (t₁.length + 2)) 1).trans (liftEquiv (liftEquiv π))
      have hs0 : π₂.symm 0 = 1 := by
        simp only [π₂, Equiv.symm_trans_apply, Equiv.symm_swap]
        erw [liftEquiv_symm_zero]
        exact Equiv.swap_apply_left _ _
      have hs1 : π₂.symm (Fin.succ 0) = 0 := by
        simp only [π₂, Equiv.symm_trans_apply, Equiv.symm_swap]
        erw [liftEquiv_symm_succ, liftEquiv_symm_zero]
        exact Equiv.swap_apply_right _ _
      have hss : ∀ k : Fin t₂.length, π₂.symm k.succ.succ = (π.symm k).succ.succ := by
        intro k
        simp only [π₂, Equiv.symm_trans_apply, Equiv.symm_swap]
        erw [liftEquiv_symm_succ, liftEquiv_symm_succ]
        exact Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      have htail : (Finset.univ.filter (fun k : Fin t₂.length =>
            k.succ ∈ Finset.univ.filter (fun i : Fin (t₂.length + 1) =>
              i.succ ∈ W.map π₂.toEmbedding)))
          = (Finset.univ.filter (fun k : Fin t₁.length => k.succ.succ ∈ W)).map
              π.toEmbedding := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv, hss]
      have htail₁ : (Finset.univ.filter (fun k : Fin t₁.length =>
            k.succ ∈ Finset.univ.filter (fun i : Fin (t₁.length + 1) => i.succ ∈ W)))
          = Finset.univ.filter (fun k : Fin t₁.length => k.succ.succ ∈ W) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hrab : rd a = rd b := hrd hab
      show List.map rd (Having.seqOf (b :: a :: t₂) (W.map π₂.toEmbedding))
        = List.map rd (Having.seqOf (a :: b :: t₁) W)
      simp only [Having.seqOf, List.map_append]
      erw [htail, hs, htail₁]
      simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
      have hs1' : π₂.symm 1 = 0 := hs1
      erw [hs0, hs1']
      by_cases h0W : (0 : Fin (t₁.length + 2)) ∈ W <;> by_cases h1W : (1 : Fin (t₁.length + 2)) ∈ W
        <;> simp [h0W, h1W, hrab]
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
    obtain ⟨π₁, hg₁, hs₁⟩ := ih₁
    obtain ⟨π₂, hg₂, hs₂⟩ := ih₂
    refine ⟨π₁.trans π₂, fun i => by rw [Equiv.trans_apply, hg₂, hg₁], fun W => ?_⟩
    rw [show W.map (π₁.trans π₂).toEmbedding = (W.map π₁.toEmbedding).map π₂.toEmbedding by
      rw [Finset.map_map]; rfl, hs₂, hs₁]

end TiePerm

/-! ## A listing pair moves positions -/

section ListingMove

variable {T K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

theorem ListingRel.exists_move {f : K →+* K'} (D : ListingRel f T) :
    ∃ mv : Fin D.L.length ≃ Fin D.L'.length,
      (∀ i, D.ann' (D.L'.get (mv i)) = f (D.ann (D.L.get i)))
      ∧ ∀ W : Finset (Fin D.L.length),
        (Having.seqOf D.L' (W.map mv.toEmbedding)).map D.str'
          = (Having.seqOf D.L W).map D.str := by
  obtain ⟨π, hg, hs⟩ := TiePerm.exists_equiv D.str' D.heqv D.hperm
  have hl : D.L.length = (D.L.map D.e).length := (List.length_map _).symm
  refine ⟨(finCongr hl).trans π.symm, fun i => ?_, fun W => ?_⟩
  · have := hg (π.symm (finCongr hl i))
    rw [Equiv.apply_symm_apply] at this
    rw [Equiv.trans_apply, ← this]
    simp [D.hann]
  · have hW : W.map ((finCongr hl).trans π.symm).toEmbedding
        = (W.map (finCongr hl).toEmbedding).map π.symm.toEmbedding := by
      rw [Finset.map_map]; rfl
    have h2 := hs ((W.map (finCongr hl).toEmbedding).map π.symm.toEmbedding)
    rw [Finset.map_map, show (π.symm.toEmbedding.trans π.toEmbedding) = Function.Embedding.refl _
      from by ext; simp, Finset.map_refl] at h2
    rw [hW, ← h2, AggValue.seqOf_map D.e D.L hl W, List.map_map]
    exact List.map_congr_left (fun b _ => D.hstr b)

/-- **The positions a listing pair moves**, chosen. -/
noncomputable def ListingRel.move {f : K →+* K'} (D : ListingRel f T) :
    Fin D.L.length ≃ Fin D.L'.length :=
  Classical.choose D.exists_move

theorem ListingRel.move_ann {f : K →+* K'} (D : ListingRel f T) (i : Fin D.L.length) :
    D.ann' (D.L'.get (D.move i)) = f (D.ann (D.L.get i)) :=
  (Classical.choose_spec D.exists_move).1 i

theorem ListingRel.move_seqOf {f : K →+* K'} (D : ListingRel f T)
    (W : Finset (Fin D.L.length)) :
    (Having.seqOf D.L' (W.map D.move.toEmbedding)).map D.str'
      = (Having.seqOf D.L W).map D.str :=
  (Classical.choose_spec D.exists_move).2 W

end ListingMove

/-! ## Two towers related under a homomorphism -/

section Rel

variable {T K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

/-- **How two inner values correspond under a homomorphism**, storey by
storey. At storey `0` the two expressions belong to one family, presented
on each side by the listing the family is given (`lp`), through the same
readings; above, two nodes with the same outer aggregate and convention,
whose occurrences are the two sides of one bag of pairs – annotations
pushed through `f`, inner values corresponding. `LG` and `NG` restrict which
pairs are considered: the hypotheses of `wcorr_of_rel` are stated on them. -/
def NestInner.Rel (f : K →+* K') (lp : LeafKey T K → ListingRel f T)
    (LG : AggExpr T K' → AggExpr T K → Prop)
    (NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop) :
    (j : ℕ) → NestInner T K' j → NestInner T K j → Prop
  | 0, e', e => LG e' e ∧ (AggExpr.fam (K := K') e').family = (AggExpr.fam (K := K) e).family
      ∧ ∃ (ok : List (lp (leafKey (T := T) (K := K) e)).ρ → Prop)
        (val : List (lp (leafKey (T := T) (K := K) e)).ρ → T),
        AggExpr.PresBy (K := K) e (lp (leafKey e)).L (lp (leafKey e)).ann (lp (leafKey e)).str
          ok val
        ∧ AggExpr.PresBy (K := K') e' (lp (leafKey (T := T) (K := K) e)).L'
          (lp (leafKey (T := T) (K := K) e)).ann' (lp (leafKey (T := T) (K := K) e)).str' ok val
  | j + 1, Sum.inl x', Sum.inl x => NestInner.Rel f lp LG NG j x' x
  | j + 1, Sum.inr N', Sum.inr N => NG j N' N ∧ N'.agg = N.agg ∧ N'.scalar = N.scalar
      ∧ N'.fam.family = N.fam.family
      ∧ ∃ Z : Multiset ((NestInner T K' j × K' × NestInner T K j) × K),
        Z.map (fun z => (z.1.1, z.1.2.1)) = N'.occs ∧ Z.map (fun z => (z.1.2.2, z.2)) = N.occs
        ∧ ∀ z ∈ Z, z.1.2.1 = f z.2 ∧ NestInner.Rel f lp LG NG j z.1.1 z.1.2.2
  | _ + 1, Sum.inl _, Sum.inr _ => False
  | _ + 1, Sum.inr _, Sum.inl _ => False

variable {f : K →+* K'} {lp : LeafKey T K → ListingRel f T}
  {LG : AggExpr T K' → AggExpr T K → Prop}
  {NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop}

theorem annList_of_presBy {ρ β K₀ : Type} {e : AggExpr T K₀} {L : List β} {ann : β → K₀}
    {str : β → ρ} {ok : List ρ → Prop} {val : List ρ → T}
    (hP : e.PresBy L ann str ok val) : e.annList = L.map ann := by
  obtain ⟨h, ha, -, -⟩ := hP
  unfold AggExpr.annList
  refine List.ext_get (by simp [h]) (fun i h₁ h₂ => ?_)
  have := ha ⟨i, by simpa using h₂⟩
  simp only [AggExpr.anns] at this
  simp only [List.get_eq_getElem, List.getElem_map] at this ⊢
  exact this

/-- **The key a related expression family has on the target side.** -/
def lkey (lp : LeafKey T K → ListingRel f T) (κ : LeafKey T K) : LeafKey T K' :=
  (κ.1, (lp κ).L'.map (lp κ).ann')

theorem Rel.leafKey_eq {e' : AggExpr T K'} {e : AggExpr T K}
    (h : NestInner.Rel f lp LG NG 0 e' e) : leafKey e' = lkey lp (leafKey e) := by
  obtain ⟨-, hf, ok, val, -, hP'⟩ := h
  unfold lkey
  rw [show leafKey e' = (e'.fam.family, e'.annList) from rfl, hf, annList_of_presBy hP']
  rfl

theorem Rel.leaves : ∀ (j : ℕ) (x' : NestInner T K' j) (x : NestInner T K j),
    NestInner.Rel f lp LG NG j x' x →
      NestInner.leaves j x' = (NestInner.leaves j x).map (lkey lp)
  | 0, e', e, h => by
    show {leafKey e'} = Multiset.map (lkey lp) {leafKey e}
    rw [Multiset.map_singleton, Rel.leafKey_eq h]
  | j + 1, Sum.inl x', Sum.inl x, h => Rel.leaves j x' x h
  | j + 1, Sum.inr N', Sum.inr N, h => by
    obtain ⟨-, -, -, -, Z, h1, h2, h3⟩ := h
    show N'.occs.bind _ = (N.occs.bind _).map _
    rw [← h1, ← h2, Multiset.bind_map, Multiset.bind_map, Multiset.map_bind]
    exact Multiset.bind_congr (fun z hz => Rel.leaves j _ _ (h3 z hz).2)
  | _ + 1, Sum.inl _, Sum.inr _, h => h.elim
  | _ + 1, Sum.inr _, Sum.inl _, h => h.elim

/-- Every expression family a related value reads is that of a related
pair. -/
theorem Rel.mem_leaves : ∀ (j : ℕ) (x' : NestInner T K' j) (x : NestInner T K j),
    NestInner.Rel f lp LG NG j x' x → ∀ κ ∈ NestInner.leaves j x,
      ∃ e' e, NestInner.Rel f lp LG NG 0 e' e ∧ leafKey e = κ
  | 0, e', e, h, κ, hκ => ⟨e', e, h, (Multiset.mem_singleton.mp hκ).symm⟩
  | j + 1, Sum.inl x', Sum.inl x, h, κ, hκ => Rel.mem_leaves j x' x h κ hκ
  | j + 1, Sum.inr N', Sum.inr N, h, κ, hκ => by
    obtain ⟨-, -, -, -, Z, h1, h2, h3⟩ := h
    have hκ' : κ ∈ N.occs.bind (fun o => NestInner.leaves j o.1) := hκ
    rw [← h2, Multiset.bind_map] at hκ'
    obtain ⟨z, hz, hκz⟩ := Multiset.mem_bind.mp hκ'
    exact Rel.mem_leaves j _ _ (h3 z hz).2 κ hκz
  | _ + 1, Sum.inl _, Sum.inr _, h, _, _ => h.elim
  | _ + 1, Sum.inr _, Sum.inl _, h, _, _ => h.elim

/-- Every node a related value reads is that of a related pair. -/
theorem Rel.mem_nodes : ∀ (j : ℕ) (x' : NestInner T K' j) (x : NestInner T K j),
    NestInner.Rel f lp LG NG j x' x → ∀ e ∈ NestInner.nodes j x,
      ∃ N' N, NestInner.Rel f lp LG NG (e.1 + 1) (Sum.inr N') (Sum.inr N) ∧ N.key = e.2
  | 0, _, _, _, e, he => absurd he (Multiset.notMem_zero _)
  | j + 1, Sum.inl x', Sum.inl x, h, e, he => Rel.mem_nodes j x' x h e he
  | j + 1, Sum.inr N', Sum.inr N, h, e, he => by
    rcases Multiset.mem_cons.mp he with rfl | he
    · exact ⟨N', N, h, rfl⟩
    · obtain ⟨-, -, -, -, Z, h1, h2, h3⟩ := h
      have he' : e ∈ N.occs.bind (fun o => NestInner.nodes j o.1) := he
      rw [← h2, Multiset.bind_map] at he'
      obtain ⟨z, hz, hez⟩ := Multiset.mem_bind.mp he'
      exact Rel.mem_nodes j _ _ (h3 z hz).2 e hez
  | _ + 1, Sum.inl _, Sum.inr _, h, _, _ => h.elim
  | _ + 1, Sum.inr _, Sum.inl _, h, _, _ => h.elim

end Rel

/-! ## The nodes, decided once -/

section Nodes

variable {T K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

variable {f : K →+* K'} {lp : LeafKey T K → ListingRel f T}
  {LG : AggExpr T K' → AggExpr T K → Prop}
  {NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop}

/-- The bag of pairs a related node pair is the two sides of. -/
def PairsOf (f : K →+* K') (lp : LeafKey T K → ListingRel f T)
    (LG : AggExpr T K' → AggExpr T K → Prop)
    (NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop)
    (j : ℕ) (N' : NestNode T K' (NestInner T K' j)) (N : NestNode T K (NestInner T K j))
    (Z : Multiset ((NestInner T K' j × K' × NestInner T K j) × K)) : Prop :=
  Z.map (fun z => (z.1.1, z.1.2.1)) = N'.occs ∧ Z.map (fun z => (z.1.2.2, z.2)) = N.occs
    ∧ ∀ z ∈ Z, z.1.2.1 = f z.2 ∧ NestInner.Rel f lp LG NG j z.1.1 z.1.2.2

theorem rel_inr_iff {j : ℕ} {N' : NestNode T K' (NestInner T K' j)}
    {N : NestNode T K (NestInner T K j)} :
    NestInner.Rel f lp LG NG (j + 1) (Sum.inr N') (Sum.inr N)
      ↔ NG j N' N ∧ N'.agg = N.agg ∧ N'.scalar = N.scalar ∧ N'.fam.family = N.fam.family
        ∧ ∃ Z, PairsOf f lp LG NG j N' N Z := Iff.rfl

open Classical in
/-- **The bag of pairs chosen for a node**, by key: one for all the
copies of the node. -/
noncomputable def Zof (f : K →+* K') (lp : LeafKey T K → ListingRel f T)
    (LG : AggExpr T K' → AggExpr T K → Prop)
    (NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop)
    (j : ℕ) (κ : NodeKey T K j) : Multiset ((NestInner T K' j × K' × NestInner T K j) × K) :=
  if h : ∃ t : NestNode T K' (NestInner T K' j) × NestNode T K (NestInner T K j)
      × Multiset ((NestInner T K' j × K' × NestInner T K j) × K),
      NestInner.Rel f lp LG NG (j + 1) (Sum.inr t.1) (Sum.inr t.2.1) ∧ t.2.1.key = κ
        ∧ PairsOf f lp LG NG j t.1 t.2.1 t.2.2
  then (Classical.choose h).2.2 else 0

/-- **The key a related node has on the target side**, at its storey. -/
noncomputable def nkeyAt (f : K →+* K') (lp : LeafKey T K → ListingRel f T)
    (LG : AggExpr T K' → AggExpr T K → Prop)
    (NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop)
    (j : ℕ) (κ : NodeKey T K j) : NodeKey T K' j :=
  (κ.1, (Zof f lp LG NG j κ).map (fun z => (z.1.1, z.1.2.1)))

/-- **The key a related node has on the target side.** -/
noncomputable def nkey (f : K →+* K') (lp : LeafKey T K → ListingRel f T)
    (LG : AggExpr T K' → AggExpr T K → Prop)
    (NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop)
    (e : Σ j, NodeKey T K j) : Σ j, NodeKey T K' j :=
  ⟨e.1, nkeyAt f lp LG NG e.1 e.2⟩

/-- **The chosen bag presents every copy of a node**, and the copies on
the target side have the key it gives them – where two related nodes have
one key on one side exactly when they have one on the other. -/
theorem Rel.zof
    (hN : ∀ j N'₁ N₁ N'₂ N₂, NestInner.Rel f lp LG NG (j + 1) (Sum.inr N'₁) (Sum.inr N₁) →
      NestInner.Rel f lp LG NG (j + 1) (Sum.inr N'₂) (Sum.inr N₂) →
        (N'₁.key = N'₂.key ↔ N₁.key = N₂.key))
    {j : ℕ} {N' : NestNode T K' (NestInner T K' j)} {N : NestNode T K (NestInner T K j)}
    (h : NestInner.Rel f lp LG NG (j + 1) (Sum.inr N') (Sum.inr N)) :
    nkey f lp LG NG ⟨j, N.key⟩ = ⟨j, N'.key⟩ ∧ PairsOf f lp LG NG j N' N (Zof f lp LG NG j N.key) := by
  classical
  obtain ⟨-, -, -, hfam, Z, hZ⟩ := id h
  have hex : ∃ t : NestNode T K' (NestInner T K' j) × NestNode T K (NestInner T K j)
      × Multiset ((NestInner T K' j × K' × NestInner T K j) × K),
      NestInner.Rel f lp LG NG (j + 1) (Sum.inr t.1) (Sum.inr t.2.1) ∧ t.2.1.key = N.key
        ∧ PairsOf f lp LG NG j t.1 t.2.1 t.2.2 := ⟨(N', N, Z), h, rfl, hZ⟩
  have hz : Zof f lp LG NG j N.key = (Classical.choose hex).2.2 := by
    unfold Zof; exact dite_eq_left_of_eq_true (eq_true hex)
  obtain ⟨h₀, hk₀, hZ₀⟩ := Classical.choose_spec hex
  set t := Classical.choose hex
  have hk' : t.1.key = N'.key := (hN j _ _ _ _ h₀ h).mpr hk₀
  have hocc : t.2.1.occs = N.occs := congrArg Prod.snd hk₀
  have hocc' : t.1.occs = N'.occs := congrArg Prod.snd hk'
  refine ⟨?_, ?_⟩
  · unfold nkey nkeyAt
    rw [hz, hZ₀.1, hocc']
    show (⟨j, (N.fam.family, N'.occs)⟩ : Σ j, NodeKey T K' j) = ⟨j, (N'.fam.family, N'.occs)⟩
    rw [hfam]
  · rw [hz]
    exact ⟨hZ₀.1.trans hocc', hZ₀.2.1.trans hocc, hZ₀.2.2⟩

theorem Rel.nodes
    (hN : ∀ j N'₁ N₁ N'₂ N₂, NestInner.Rel f lp LG NG (j + 1) (Sum.inr N'₁) (Sum.inr N₁) →
      NestInner.Rel f lp LG NG (j + 1) (Sum.inr N'₂) (Sum.inr N₂) →
        (N'₁.key = N'₂.key ↔ N₁.key = N₂.key)) :
    ∀ (j : ℕ) (x' : NestInner T K' j) (x : NestInner T K j),
      NestInner.Rel f lp LG NG j x' x →
        NestInner.nodes j x' = (NestInner.nodes j x).map (nkey f lp LG NG)
  | 0, _, _, _ => rfl
  | j + 1, Sum.inl x', Sum.inl x, h => Rel.nodes hN j x' x h
  | j + 1, Sum.inr N', Sum.inr N, h => by
    have hk := (Rel.zof hN h).1
    obtain ⟨-, -, -, -, Z, h1, h2, h3⟩ := h
    show _ ::ₘ N'.occs.bind _ = (_ ::ₘ N.occs.bind _).map _
    rw [Multiset.map_cons, hk, ← h1, ← h2, Multiset.bind_map, Multiset.bind_map,
      Multiset.map_bind]
    exact congrArg _ (Multiset.bind_congr (fun z hz => Rel.nodes hN j _ _ (h3 z hz).2))
  | _ + 1, Sum.inl _, Sum.inr _, h => h.elim
  | _ + 1, Sum.inr _, Sum.inl _, h => h.elim

end Nodes

/-! ## Enumerations carried along -/

namespace NestedValue

theorem memChoices_map {X Y K₁ K₂ : Type} (g : X × K₁ → Y × K₂) :
    ∀ M : Multiset (X × K₁), memChoices (M.map g)
      = (memChoices M).map (Multiset.map (fun m => ((g (m.1, m.2.1)).1, (g (m.1, m.2.1)).2,
          m.2.2))) := by
  intro M
  induction M using Multiset.induction_on with
  | empty => simp [memChoices]
  | cons o M ih =>
    simp only [memChoices, Multiset.map_cons, Multiset.foldr_cons] at ih ⊢
    rw [ih, addMem, addMem, Multiset.map_bind]
    refine Multiset.bind_congr (fun b _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun ms _ => by simp)

end NestedValue

theorem Multiset.dedup_map_of_injOn {α β : Type} [DecidableEq α] [DecidableEq β]
    {g : α → β} {s : Multiset α} (hg : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) :
    (s.map g).dedup = s.dedup.map g := by
  refine (Multiset.Nodup.ext (Multiset.nodup_dedup _) ?_).mpr (fun b => ?_)
  · exact (Multiset.nodup_dedup s).map_on (fun x hx y hy hxy =>
      hg x (Multiset.mem_dedup.mp hx) y (Multiset.mem_dedup.mp hy) hxy)
  · simp only [Multiset.mem_dedup, Multiset.mem_map]

section Moves

variable {T K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

/-- The positions of a family of length `n` a set of numbers names. -/
def finsOf {n : ℕ} (S : Finset ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) ∈ S)

/-- **The positions a listing pair moves a set of positions to.** -/
noncomputable def ListingRel.moveS {f : K →+* K'} (D : ListingRel f T) (S : Finset ℕ) :
    Finset ℕ :=
  ((finsOf S : Finset (Fin D.L.length)).map D.move.toEmbedding).map Fin.valEmbedding

theorem finsOf_map_val {n : ℕ} (W : Finset (Fin n)) : finsOf (W.map Fin.valEmbedding) = W := by
  ext i
  simp only [finsOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Fin.valEmbedding_apply, Fin.val_inj, exists_eq_right]

theorem map_val_finsOf {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) :
    (finsOf S : Finset (Fin n)).map Fin.valEmbedding = S := by
  ext i
  simp only [finsOf, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact hj
  · intro hi; exact ⟨⟨i, Finset.mem_range.mp (hS hi)⟩, hi, rfl⟩

theorem range_powerset_val (n : ℕ) :
    (Finset.range n).powerset.val
      = (Finset.univ : Finset (Finset (Fin n))).val.map (fun W => W.map Fin.valEmbedding) := by
  have : (Finset.range n).powerset
      = (Finset.univ : Finset (Finset (Fin n))).map
        ⟨fun W => W.map Fin.valEmbedding, fun W₁ W₂ h => Finset.map_injective _ h⟩ := by
    ext S
    simp only [Finset.mem_powerset, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hS; exact ⟨finsOf S, map_val_finsOf hS⟩
    · rintro ⟨W, rfl⟩ i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_range.mpr j.isLt
  rw [this, Finset.map_val]
  rfl

/-- **Moving positions permutes the subsets of a family.** -/
theorem ListingRel.powerset_moveS {f : K →+* K'} (D : ListingRel f T) :
    (Finset.range D.L.length).powerset.val.map D.moveS
      = (Finset.range D.L'.length).powerset.val := by
  rw [range_powerset_val, range_powerset_val, Multiset.map_map]
  have hc : (D.moveS ∘ fun W : Finset (Fin D.L.length) => W.map Fin.valEmbedding)
      = (fun W => W.map Fin.valEmbedding) ∘ (fun W => W.map D.move.toEmbedding) := by
    funext W
    simp only [Function.comp_apply, ListingRel.moveS, finsOf_map_val]
  rw [hc, ← Multiset.map_map, ← Finset.map_univ_equiv (D.move.finsetCongr), Finset.map_val]
  rfl

theorem ListingRel.moveS_subset {f : K →+* K'} (D : ListingRel f T) (S : Finset ℕ) :
    D.moveS S ⊆ Finset.range D.L'.length := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_range.mpr j.isLt

theorem finsOf_moveS {f : K →+* K'} (D : ListingRel f T) (S : Finset ℕ) :
    (finsOf (D.moveS S) : Finset (Fin D.L'.length))
      = (finsOf S : Finset (Fin D.L.length)).map D.move.toEmbedding := by
  rw [ListingRel.moveS, finsOf_map_val]

theorem trS_eq_map_finsOf {n m : ℕ} (h : n = m) (S : Finset ℕ) :
    (trS S : Finset (Fin m)) = (finsOf S : Finset (Fin n)).map (finCongr h).toEmbedding := by
  ext i
  simp [trS, finsOf]

/-- **An expression presented by a listing reads a set of positions off the
rows it selects.** -/
theorem presBy_valOn {ρ β K₀ : Type} {e : AggExpr T K₀} {L : List β} {ann : β → K₀}
    {str : β → ρ} {ok : List ρ → Prop} {val : List ρ → T} (hP : e.PresBy L ann str ok val)
    (S : Finset ℕ) :
    e.valOn (trS S) = val ((Having.seqOf L (finsOf S)).map str)
      ∧ (e.IsWorld (trS S) ↔ ok ((Having.seqOf L (finsOf S)).map str)) := by
  obtain ⟨h, -, hw, hv⟩ := hP
  rw [trS_eq_map_finsOf h]
  exact ⟨hv _, hw _⟩

/-- **Two expressions presented by a listing pair read a set of positions
and its move alike.** -/
theorem ListingRel.read_moveS {f : K →+* K'} (D : ListingRel f T) {e : AggExpr T K}
    {e' : AggExpr T K'} {ok : List D.ρ → Prop} {val : List D.ρ → T}
    (hP : e.PresBy D.L D.ann D.str ok val) (hP' : e'.PresBy D.L' D.ann' D.str' ok val)
    (S : Finset ℕ) :
    e'.valOn (trS (D.moveS S)) = e.valOn (trS S)
      ∧ (e'.IsWorld (trS (D.moveS S)) ↔ e.IsWorld (trS S)) := by
  obtain ⟨hv', hw'⟩ := presBy_valOn hP' (D.moveS S)
  obtain ⟨hv, hw⟩ := presBy_valOn hP S
  rw [finsOf_moveS, D.move_seqOf] at hv' hw'
  exact ⟨hv'.trans hv.symm, hw'.trans hw.symm⟩

/-- **And weigh them alike, pushed through `f`.** -/
theorem ListingRel.prod_moveS {f : K →+* K'} (D : ListingRel f T) {S : Finset ℕ}
    (hS : S ⊆ Finset.range D.L.length) :
    ∏ i ∈ D.moveS S, (D.L'.map D.ann').getD i 0 = f (∏ i ∈ S, (D.L.map D.ann).getD i 0) := by
  rw [map_prod]
  conv_rhs => rw [← map_val_finsOf hS]
  simp only [ListingRel.moveS, Finset.prod_map]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Fin.valEmbedding_apply, Equiv.coe_toEmbedding]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp), List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some, List.getElem_map]
  have := D.move_ann i
  simp only [List.get_eq_getElem] at this
  exact this

theorem ListingRel.sum_moveS {f : K →+* K'} (D : ListingRel f T) (S : Finset ℕ) :
    ∑ i ∈ Finset.range D.L'.length \ D.moveS S, (D.L'.map D.ann').getD i 0
      = f (∑ i ∈ Finset.range D.L.length \ S, (D.L.map D.ann).getD i 0) := by
  have hc : Finset.range D.L'.length \ D.moveS S
      = D.moveS (Finset.range D.L.length \ S) := by
    have hu : D.moveS (Finset.range D.L.length) = Finset.range D.L'.length := by
      ext i
      simp only [ListingRel.moveS, finsOf, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        Finset.mem_range, true_and, Fin.valEmbedding_apply, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨j, ⟨k, -, rfl⟩, rfl⟩; exact (D.move k).isLt
      · intro hi
        exact ⟨⟨i, hi⟩, ⟨D.move.symm ⟨i, hi⟩, (D.move.symm ⟨i, hi⟩).isLt, by simp⟩, rfl⟩
    rw [← hu]
    ext i
    simp only [ListingRel.moveS, finsOf, Finset.mem_sdiff, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.valEmbedding_apply, Equiv.coe_toEmbedding, Finset.mem_range]
    constructor
    · rintro ⟨⟨j, ⟨k, hk, rfl⟩, rfl⟩, hn⟩
      exact ⟨D.move k, ⟨k, ⟨k.isLt, fun hkS => hn ⟨D.move k, ⟨k, hkS, rfl⟩, rfl⟩⟩, rfl⟩, rfl⟩
    · rintro ⟨j, ⟨k, ⟨hk, hkS⟩, rfl⟩, rfl⟩
      refine ⟨⟨D.move k, ⟨k, hk, rfl⟩, rfl⟩, ?_⟩
      rintro ⟨j', ⟨k', hk'S, hk'⟩, hj'⟩
      have : k' = k := D.move.injective (Fin.ext (by rw [hk']; exact hj'))
      exact hkS (this ▸ hk'S)
  rw [hc, map_sum]
  have hS' : Finset.range D.L.length \ S ⊆ Finset.range D.L.length := Finset.sdiff_subset
  conv_rhs => rw [← map_val_finsOf hS']
  simp only [ListingRel.moveS, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fin.valEmbedding_apply, Equiv.coe_toEmbedding]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp), List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some, List.getElem_map]
  have := D.move_ann i
  simp only [List.get_eq_getElem] at this
  exact this

end Moves

/-! ## The worlds of two related towers correspond -/

section Main

variable {T K K' : Type} [CommSemiringWithMonus K] [CommSemiringWithMonus K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

variable {f : K →+* K'} {lp : LeafKey T K → ListingRel f T}
  {LG : AggExpr T K' → AggExpr T K → Prop}
  {NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop}

/-- A decision about a node, over a bag of pairs. -/
abbrev PEntry (T K K' : Type) :=
  Σ j, NodeKey T K j × Multiset ((NestInner T K' j × K' × NestInner T K j) × K × Bool)

/-- One more node, decided over its chosen pairs. -/
def addNodeP (Zf : (j : ℕ) → NodeKey T K j → Multiset ((NestInner T K' j × K' × NestInner T K j) × K))
    (κ : Σ j, NodeKey T K j) (acc : Multiset (Multiset (PEntry T K K'))) :
    Multiset (Multiset (PEntry T K K')) :=
  (NestedValue.memChoices (Zf κ.1 κ.2)).bind (fun D => acc.map (⟨κ.1, κ.2, D⟩ ::ₘ ·))

instance (Zf : (j : ℕ) → NodeKey T K j →
    Multiset ((NestInner T K' j × K' × NestInner T K j) × K)) :
    LeftCommutative (addNodeP Zf) where
  left_comm κ₁ κ₂ acc := by
    unfold addNodeP
    simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr (fun S₂ _ => Multiset.bind_congr
      (fun S₁ _ => Multiset.map_congr rfl (fun ms _ => Multiset.cons_swap _ _ _)))

/-- The source side of a decision about a node. -/
def entK (e : PEntry T K K') : Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool) :=
  ⟨e.1, e.2.1, e.2.2.map (fun m => (m.1.2.2, m.2.1, m.2.2))⟩

/-- The target side of a decision about a node. -/
noncomputable def entK' (f : K →+* K') (lp : LeafKey T K → ListingRel f T)
    (LG : AggExpr T K' → AggExpr T K → Prop)
    (NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop)
    (e : PEntry T K K') : Σ j, NodeKey T K' j × Multiset (NestInner T K' j × K' × Bool) :=
  ⟨e.1, nkeyAt f lp LG NG e.1 e.2.1, e.2.2.map (fun m => (m.1.1, m.1.2.1, m.2.2))⟩

omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
theorem foldr_addNode_src
    (Zf : (j : ℕ) → NodeKey T K j → Multiset ((NestInner T K' j × K' × NestInner T K j) × K)) :
    ∀ s : Multiset (Σ j, NodeKey T K j),
      (∀ e ∈ s, (Zf e.1 e.2).map (fun z => (z.1.2.2, z.2)) = e.2.2) →
      s.foldr NestedValue.addNode {0} = (s.foldr (addNodeP Zf) {0}).map (Multiset.map entK) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro; simp
  | cons κ s ih =>
    intro hs
    rw [Multiset.foldr_cons, Multiset.foldr_cons, ih (fun e he => hs e (Multiset.mem_cons_of_mem he)),
      NestedValue.addNode, addNodeP, ← hs κ (Multiset.mem_cons_self _ _),
      NestedValue.memChoices_map, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun D _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun ms _ => ?_)
    simp only [Function.comp_apply, Multiset.map_cons]
    rfl

theorem foldr_addNode_tgt
    (s : Multiset (Σ j, NodeKey T K j)) :
    (s.map (nkey f lp LG NG)).foldr NestedValue.addNode {0}
      = (s.foldr (addNodeP (Zof f lp LG NG)) {0}).map (Multiset.map (entK' f lp LG NG)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons κ s ih =>
    rw [Multiset.map_cons, Multiset.foldr_cons, Multiset.foldr_cons, ih,
      NestedValue.addNode, addNodeP]
    show (NestedValue.memChoices ((Zof f lp LG NG κ.1 κ.2).map
        (fun z => (z.1.1, z.1.2.1)))).bind _ = _
    rw [NestedValue.memChoices_map, Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun D _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun ms _ => ?_)
    simp only [Function.comp_apply, Multiset.map_cons]
    rfl

omit [CommSemiringWithMonus K] [CommSemiringWithMonus K'] in
theorem mem_foldr_addNodeP
    {Zf : (j : ℕ) → NodeKey T K j → Multiset ((NestInner T K' j × K' × NestInner T K j) × K)} :
    ∀ {s : Multiset (Σ j, NodeKey T K j)} {Nd : Multiset (PEntry T K K')},
      Nd ∈ s.foldr (addNodeP Zf) {0} →
        Nd.map (fun e => (⟨e.1, e.2.1⟩ : Σ j, NodeKey T K j)) = s
          ∧ ∀ e ∈ Nd, e.2.2.map (fun m => (m.1, m.2.1)) = Zf e.1 e.2.1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro Nd h
    rw [Multiset.foldr_zero, Multiset.mem_singleton] at h
    subst h; simp
  | cons κ s ih =>
    intro Nd h
    rw [Multiset.foldr_cons, addNodeP] at h
    obtain ⟨D, hD, hN⟩ := Multiset.mem_bind.mp h
    obtain ⟨N₀, hN₀, rfl⟩ := Multiset.mem_map.mp hN
    obtain ⟨h1, h2⟩ := ih hN₀
    refine ⟨by rw [Multiset.map_cons, h1], fun e he => ?_⟩
    rcases Multiset.mem_cons.mp he with rfl | he
    · exact NestedValue.map_of_mem_memChoices hD
    · exact h2 e he

theorem foldr_addLeaf_tgt :
    ∀ s : Multiset (LeafKey T K), (∀ κ ∈ s, κ.2.length = (lp κ).L.length) →
      (s.map (lkey lp)).foldr NestedValue.addLeaf {0}
        = (s.foldr NestedValue.addLeaf {0}).map
          (Multiset.map (fun e => (lkey lp e.1, (lp e.1).moveS e.2))) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro; simp
  | cons κ s ih =>
    intro hs
    rw [Multiset.map_cons, Multiset.foldr_cons, Multiset.foldr_cons,
      ih (fun e he => hs e (Multiset.mem_cons_of_mem he)), NestedValue.addLeaf,
      NestedValue.addLeaf]
    rw [show (lkey lp κ).2.length = (lp κ).L'.length from List.length_map _,
      ← (lp κ).powerset_moveS, hs κ (Multiset.mem_cons_self _ _), Multiset.bind_map,
      Multiset.map_bind]
    refine Multiset.bind_congr (fun S _ => ?_)
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun ms _ => ?_)
    simp only [Function.comp_apply, Multiset.map_cons]

end Main

section Transfer

variable {T K K' : Type} [ValueType T] [CommSemiringWithMonus K] [CommSemiringWithMonus K']
  [DecidableEq K] [DecidableEq K']

attribute [local instance] CommSemiringWithMonus.toCommSemiringSW

variable {f : K →+* K'} {lp : LeafKey T K → ListingRel f T}
  {LG : AggExpr T K' → AggExpr T K → Prop}
  {NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop}

/-- **What a pair of related towers asks of its families**: two related
expression families have one key on one side exactly when they have one
on the other, and so do two related nodes. -/
def KeysFaithful (f : K →+* K') (lp : LeafKey T K → ListingRel f T)
    (LG : AggExpr T K' → AggExpr T K → Prop)
    (NG : (j : ℕ) → NestNode T K' (NestInner T K' j) → NestNode T K (NestInner T K j) → Prop) :
    Prop :=
  (∀ e'₁ e₁ e'₂ e₂, NestInner.Rel f lp LG NG 0 e'₁ e₁ → NestInner.Rel f lp LG NG 0 e'₂ e₂ →
      (leafKey e'₁ = leafKey e'₂ ↔ leafKey e₁ = leafKey e₂))
    ∧ ∀ j N'₁ N₁ N'₂ N₂, NestInner.Rel f lp LG NG (j + 1) (Sum.inr N'₁) (Sum.inr N₁) →
      NestInner.Rel f lp LG NG (j + 1) (Sum.inr N'₂) (Sum.inr N₂) →
        (N'₁.key = N'₂.key ↔ N₁.key = N₂.key)

omit [ValueType T] [CommSemiringWithMonus K] in
/-- The families a node holds, read off a bag its occurrences are the
image of. -/
theorem leaves_ofNode_eq {K₀ Y : Type} [DecidableEq T] [DecidableEq K₀] {j : ℕ}
    (N : NestNode T K₀ (NestInner T K₀ j)) (Z : Multiset Y) (g : Y → NestInner T K₀ j × K₀)
    (hZ : Z.map g = N.occs) :
    (NestedValue.ofNode N).leaves = (Z.bind (fun z => NestInner.leaves j (g z).1)).dedup := by
  show (N.occs.bind _).dedup = _
  rw [← hZ, Multiset.bind_map]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] in
open Classical in
theorem nodes_ofNode_eq {K₀ Y : Type} [DecidableEq T] [DecidableEq K₀] {j : ℕ}
    (N : NestNode T K₀ (NestInner T K₀ j)) (Z : Multiset Y) (g : Y → NestInner T K₀ j × K₀)
    (hZ : Z.map g = N.occs) :
    (NestedValue.ofNode N).nodes = (Z.bind (fun z => NestInner.nodes j (g z).1)).dedup := by
  show (N.occs.bind _).dedup = _
  rw [← hZ, Multiset.bind_map]
  rfl

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- **Two related inner values read alike under corresponding
decisions**: the target's decision is the source's moved position by
position on each expression family the value reads, and on each node it
reads both sides of one decision over the node's chosen pairs. -/
theorem val_of_rel (hK : KeysFaithful f lp LG NG) (D : NestDec T K) (D' : NestDec T K')
    (PL : LeafKey T K → Prop) (PN : (Σ j, NodeKey T K j) → Prop)
    (hLk : ∀ κ, PL κ → D'.leaf (lkey lp κ) = (lp κ).moveS (D.leaf κ))
    (hNk : ∀ e, PN e → ∃ Dc : Multiset ((NestInner T K' e.1 × K' × NestInner T K e.1) × K × Bool),
      D.node e.1 e.2 = Dc.map (fun m => (m.1.2.2, m.2.1, m.2.2))
      ∧ D'.node e.1 (nkeyAt f lp LG NG e.1 e.2) = Dc.map (fun m => (m.1.1, m.1.2.1, m.2.2))
      ∧ Dc.map (fun m => (m.1, m.2.1)) = Zof f lp LG NG e.1 e.2) :
    ∀ (i : ℕ) (x' : NestInner T K' i) (x : NestInner T K i), NestInner.Rel f lp LG NG i x' x →
      (∀ κ ∈ NestInner.leaves i x, PL κ) → (∀ e ∈ NestInner.nodes i x, PN e) →
        NestInner.val D' i x' = NestInner.val D i x
          ∧ (NestInner.ok D' i x' ↔ NestInner.ok D i x)
  | 0, e', e, h, hl, _ => by
    have hκ := hl (leafKey e) (Multiset.mem_singleton_self _)
    obtain ⟨-, -, ok, val, hP, hP'⟩ := id h
    have hk' := Rel.leafKey_eq h
    show AggExpr.valOn e' (trS (D'.leaf (leafKey e'))) = AggExpr.valOn e (trS (D.leaf (leafKey e)))
      ∧ (AggExpr.IsWorld e' (trS (D'.leaf (leafKey e'))) ↔ AggExpr.IsWorld e (trS (D.leaf (leafKey e))))
    rw [hk', hLk _ hκ]
    exact (lp (leafKey e)).read_moveS hP hP' _
  | i + 1, Sum.inl x', Sum.inl x, h, hl, hn => val_of_rel hK D D' PL PN hLk hNk i x' x h hl hn
  | i + 1, Sum.inr N', Sum.inr N, h, hl, hn => by
    obtain ⟨hnk, hZ⟩ := Rel.zof hK.2 h
    obtain ⟨-, hagg, hsc, -, -⟩ := id h
    obtain ⟨Dc, hD, hD', hDp⟩ := hNk ⟨i, N.key⟩ (hn _ (Multiset.mem_cons_self _ _))
    have hk : N'.key = nkeyAt f lp LG NG i N.key := by
      have := (Sigma.mk.inj_iff.mp hnk).2
      exact (eq_of_heq this).symm
    -- each element of the decision is one of the chosen pairs
    have hmem : ∀ m ∈ Dc, m.1.2.1 = f m.2.1 ∧ NestInner.Rel f lp LG NG i m.1.1 m.1.2.2
        ∧ (m.1.2.2, m.2.1) ∈ N.occs := by
      intro m hm
      have hz : (m.1, m.2.1) ∈ Zof f lp LG NG i N.key := by
        rw [← hDp]; exact Multiset.mem_map_of_mem _ hm
      obtain ⟨h₁, h₂⟩ := hZ.2.2 _ hz
      refine ⟨h₁, h₂, ?_⟩
      rw [← hZ.2.1]; exact Multiset.mem_map_of_mem (fun z => (z.1.2.2, z.2)) hz
    have hrec : ∀ m ∈ Dc, NestInner.val D' i m.1.1 = NestInner.val D i m.1.2.2
        ∧ (NestInner.ok D' i m.1.1 ↔ NestInner.ok D i m.1.2.2) := by
      intro m hm
      obtain ⟨-, hR, ho⟩ := hmem m hm
      refine val_of_rel hK D D' PL PN hLk hNk i _ _ hR (fun κ hκ => hl κ ?_)
        (fun e he => hn e (Multiset.mem_cons_of_mem ?_))
      · exact Multiset.mem_bind.mpr ⟨_, ho, hκ⟩
      · exact Multiset.mem_bind.mpr ⟨_, ho, he⟩
    show (N'.agg _ = N.agg _) ∧ ((_ ∧ _) ↔ (_ ∧ _))
    rw [hk, hD', hD, hagg, hsc]
    refine ⟨congrArg N.agg ?_, and_congr ?_ ?_⟩
    · rw [Multiset.filter_map, Multiset.filter_map, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr (Multiset.filter_congr (fun _ _ => Iff.rfl))
        (fun m hm => (hrec m (Multiset.mem_of_mem_filter hm)).1)
    · simp only [Multiset.mem_map]
      constructor
      · rintro (hs | ⟨_, ⟨m, hm, rfl⟩, hp⟩)
        · exact Or.inl hs
        · exact Or.inr ⟨_, ⟨m, hm, rfl⟩, hp⟩
      · rintro (hs | ⟨_, ⟨m, hm, rfl⟩, hp⟩)
        · exact Or.inl hs
        · exact Or.inr ⟨_, ⟨m, hm, rfl⟩, hp⟩
    · constructor
      · intro hall m' hm' hp
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hm'
        exact (hrec m hm).2.mp (hall _ (Multiset.mem_map_of_mem _ hm) hp)
      · intro hall m' hm' hp
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hm'
        exact (hrec m hm).2.mpr (hall _ (Multiset.mem_map_of_mem _ hm) hp)
  | _ + 1, Sum.inl _, Sum.inr _, h, _, _ => h.elim
  | _ + 1, Sum.inr _, Sum.inl _, h, _, _ => h.elim

omit [ValueType T] [DecidableEq K] [DecidableEq K'] in
/-- A decision over pairs weighs its two sides alike, pushed through `f`. -/
theorem decProd_decAbs_pair {A B : Type} (D : Multiset ((A × K' × B) × K × Bool))
    (hD : ∀ m ∈ D, m.1.2.1 = f m.2.1) :
    NestedValue.decProd (D.map (fun m => (m.1.1, m.1.2.1, m.2.2)))
        = f (NestedValue.decProd (D.map (fun m => (m.1.2.2, m.2.1, m.2.2))))
      ∧ NestedValue.decAbs (D.map (fun m => (m.1.1, m.1.2.1, m.2.2)))
        = f (NestedValue.decAbs (D.map (fun m => (m.1.2.2, m.2.1, m.2.2)))) := by
  unfold NestedValue.decProd NestedValue.decAbs
  rw [map_multiset_prod, map_multiset_sum, Multiset.map_map, Multiset.map_map, Multiset.map_map,
    Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine ⟨congrArg _ (Multiset.map_congr rfl (fun m hm => ?_)),
    congrArg _ (Multiset.map_congr rfl (fun m hm => ?_))⟩
  · simp only [Function.comp_apply]
    split <;> simp [hD m hm]
  · simp only [Function.comp_apply]
    split <;> simp [hD m hm]

/-- **Two related towers have corresponding worlds.** The source's worlds
and the target's are the images of one bag of indices: a decision over the
pairs of the root's occurrences, a set of positions of each expression
family the source holds – moved, on the target, by the family's listing
pair – and a decision over the chosen pairs of each node it holds. -/
theorem wcorr_of_rel (hK : KeysFaithful f lp LG NG) {j : ℕ}
    {N' : NestNode T K' (NestInner T K' j)} {N : NestNode T K (NestInner T K j)}
    (hr : NestInner.Rel f lp LG NG (j + 1) (Sum.inr N') (Sum.inr N)) :
    NestedValue.WCorr f (NestedValue.ofNode N') (NestedValue.ofNode N) := by
  classical
  obtain ⟨-, -, -, -, Zr, hZr1, hZr2, hZr3⟩ := id hr
  set b := NestedValue.ofNode N with hb
  set b' := NestedValue.ofNode N' with hb'
  -- the families the two sides hold
  have hLs := leaves_ofNode_eq N Zr (fun z => (z.1.2.2, z.2)) hZr2
  have hLt := leaves_ofNode_eq N' Zr (fun z => (z.1.1, z.1.2.1)) hZr1
  have hNs := nodes_ofNode_eq N Zr (fun z => (z.1.2.2, z.2)) hZr2
  have hNt := nodes_ofNode_eq N' Zr (fun z => (z.1.1, z.1.2.1)) hZr1
  have hmemL : ∀ κ ∈ b.leaves, ∃ e' e, NestInner.Rel f lp LG NG 0 e' e ∧ leafKey e = κ := by
    intro κ hκ
    rw [hLs, Multiset.mem_dedup] at hκ
    obtain ⟨z, hz, hκz⟩ := Multiset.mem_bind.mp hκ
    exact Rel.mem_leaves j _ _ (hZr3 z hz).2 κ hκz
  have hmemN : ∀ e ∈ b.nodes, ∃ M' M, NestInner.Rel f lp LG NG (e.1 + 1) (Sum.inr M') (Sum.inr M)
      ∧ M.key = e.2 := by
    intro e he
    rw [hNs, Multiset.mem_dedup] at he
    obtain ⟨z, hz, hez⟩ := Multiset.mem_bind.mp he
    exact Rel.mem_nodes j _ _ (hZr3 z hz).2 e hez
  have hleaves : b'.leaves = b.leaves.map (lkey lp) := by
    rw [hLt, hLs, ← Multiset.dedup_map_of_injOn]
    · congr 1
      rw [Multiset.map_bind]
      exact Multiset.bind_congr (fun z hz => Rel.leaves j _ _ (hZr3 z hz).2)
    · intro κ₁ hκ₁ κ₂ hκ₂ heq
      obtain ⟨e'₁, e₁, h₁, rfl⟩ := Rel.mem_leaves j _ _ (hZr3 _ (Multiset.mem_bind.mp hκ₁).choose_spec.1).2 κ₁
        (Multiset.mem_bind.mp hκ₁).choose_spec.2
      obtain ⟨e'₂, e₂, h₂, rfl⟩ := Rel.mem_leaves j _ _ (hZr3 _ (Multiset.mem_bind.mp hκ₂).choose_spec.1).2 _
        (Multiset.mem_bind.mp hκ₂).choose_spec.2
      rw [← Rel.leafKey_eq h₁, ← Rel.leafKey_eq h₂] at heq
      exact (hK.1 _ _ _ _ h₁ h₂).mp heq
  have hnodes : b'.nodes = b.nodes.map (nkey f lp LG NG) := by
    rw [hNt, hNs, ← Multiset.dedup_map_of_injOn]
    · congr 1
      rw [Multiset.map_bind]
      exact Multiset.bind_congr (fun z hz => Rel.nodes hK.2 j _ _ (hZr3 z hz).2)
    · rintro ⟨i₁, κ₁⟩ he₁ ⟨i₂, κ₂⟩ he₂ heq
      obtain ⟨z₁, hz₁, hez₁⟩ := Multiset.mem_bind.mp he₁
      obtain ⟨z₂, hz₂, hez₂⟩ := Multiset.mem_bind.mp he₂
      obtain ⟨M'₁, M₁, h₁, hk₁⟩ := Rel.mem_nodes j _ _ (hZr3 z₁ hz₁).2 _ hez₁
      obtain ⟨M'₂, M₂, h₂, hk₂⟩ := Rel.mem_nodes j _ _ (hZr3 z₂ hz₂).2 _ hez₂
      dsimp only at hk₁ hk₂ h₁ h₂
      rw [← hk₁, ← hk₂] at heq ⊢
      rw [(Rel.zof hK.2 h₁).1, (Rel.zof hK.2 h₂).1] at heq
      obtain ⟨hi, hh⟩ := Sigma.mk.inj_iff.mp heq
      cases hi
      rw [(hK.2 _ _ _ _ _ h₁ h₂).mp (eq_of_heq hh)]
  -- what the families carry
  have hlen : ∀ κ ∈ b.leaves, κ.2 = (lp κ).L.map (lp κ).ann := by
    intro κ hκ
    obtain ⟨e', e, h, rfl⟩ := hmemL κ hκ
    obtain ⟨-, -, ok, val, hP, -⟩ := id h
    exact annList_of_presBy hP
  have hzof : ∀ e ∈ b.nodes, (Zof f lp LG NG e.1 e.2).map (fun z => (z.1.2.2, z.2)) = e.2.2
      ∧ ∀ z ∈ Zof f lp LG NG e.1 e.2, z.1.2.1 = f z.2
        ∧ NestInner.Rel f lp LG NG e.1 z.1.1 z.1.2.2 := by
    intro e he
    obtain ⟨M', M, h, hk⟩ := hmemN e he
    obtain ⟨-, hZ⟩ := Rel.zof hK.2 h
    rw [← hk]
    exact ⟨hZ.2.1, hZ.2.2⟩
  -- the index bag, and the two worlds of an index
  obtain ⟨I, hI⟩ : ∃ I, I = (NestedValue.memChoices Zr).bind (fun R =>
      (b.leaves.foldr NestedValue.addLeaf {0}).bind (fun L =>
        (b.nodes.foldr (addNodeP (Zof f lp LG NG)) {0}).map (fun Nd => (R, L, Nd)))) := ⟨_, rfl⟩
  let φ : Multiset ((NestInner T K' j × K' × NestInner T K j) × K × Bool)
      × Multiset (LeafKey T K × Finset ℕ) × Multiset (PEntry T K K') → NestedValue.World T K j :=
    fun c =>
    ⟨c.1.map (fun m => (m.1.2.2, m.2.1, m.2.2)), c.2.1, c.2.2.map entK⟩
  let φ' : Multiset ((NestInner T K' j × K' × NestInner T K j) × K × Bool)
      × Multiset (LeafKey T K × Finset ℕ) × Multiset (PEntry T K K') → NestedValue.World T K' j :=
    fun c =>
    ⟨c.1.map (fun m => (m.1.1, m.1.2.1, m.2.2)),
      c.2.1.map (fun e => (lkey lp e.1, (lp e.1).moveS e.2)), c.2.2.map (entK' f lp LG NG)⟩
  refine ⟨_, I, φ, φ', ?_, ?_, fun c hc => ?_⟩
  · show (NestedValue.memChoices N.occs).bind _ = _
    rw [← hZr2, NestedValue.memChoices_map,
      foldr_addNode_src _ _ (fun e he => (hzof e he).1), hI]
    simp only [Multiset.bind_map, Multiset.map_bind, Multiset.map_map]
    rfl
  · show (NestedValue.memChoices N'.occs).bind _ = _
    rw [← hZr1, NestedValue.memChoices_map, hleaves, hnodes,
      foldr_addLeaf_tgt _ (fun κ hκ => by rw [hlen κ hκ, List.length_map]),
      foldr_addNode_tgt, hI]
    simp only [Multiset.bind_map, Multiset.map_bind, Multiset.map_map]
    rfl
  · rw [hI] at hc
    obtain ⟨R, hR, hc⟩ := Multiset.mem_bind.mp hc
    obtain ⟨L, hL, hc⟩ := Multiset.mem_bind.mp hc
    obtain ⟨Nd, hNd, rfl⟩ := Multiset.mem_map.mp hc
    have hRz : ∀ m ∈ R, (m.1, m.2.1) ∈ Zr := by
      intro m hm
      rw [← NestedValue.map_of_mem_memChoices hR]
      exact Multiset.mem_map_of_mem _ hm
    obtain ⟨hL1, hL2⟩ := NestedValue.mem_foldr_addLeaf_iff.mp hL
    obtain ⟨hN1, hN2⟩ := mem_foldr_addNodeP hNd
    -- the lookups
    have hLk : ∀ κ ∈ b.leaves, (φ' (R, L, Nd)).dec.leaf (lkey lp κ)
        = (lp κ).moveS ((φ (R, L, Nd)).dec.leaf κ) := by
      intro κ hκ
      rw [← hL1] at hκ
      obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hκ
      have h1 : (φ (R, L, Nd)).dec.leaf e.1 = e.2 :=
        NestedValue.leafSub_of_mem (by rw [hL1]; exact b.nodup_leaves) he
      have h2 : (φ' (R, L, Nd)).dec.leaf (lkey lp e.1) = (lp e.1).moveS e.2 := by
        refine NestedValue.leafSub_of_mem ?_
          (Multiset.mem_map_of_mem (fun e => (lkey lp e.1, (lp e.1).moveS e.2)) he)
        rw [Multiset.map_map]
        have : L.map (Prod.fst ∘ fun e : LeafKey T K × Finset ℕ =>
            (lkey lp e.1, (lp e.1).moveS e.2)) = b'.leaves := by
          rw [hleaves, ← hL1, Multiset.map_map]; rfl
        rw [this]; exact b'.nodup_leaves
      rw [h1, h2]
    have hNk : ∀ e ∈ b.nodes, ∃ Dc : Multiset ((NestInner T K' e.1 × K' × NestInner T K e.1)
        × K × Bool),
        (φ (R, L, Nd)).dec.node e.1 e.2 = Dc.map (fun m => (m.1.2.2, m.2.1, m.2.2))
        ∧ (φ' (R, L, Nd)).dec.node e.1 (nkeyAt f lp LG NG e.1 e.2)
          = Dc.map (fun m => (m.1.1, m.1.2.1, m.2.2))
        ∧ Dc.map (fun m => (m.1, m.2.1)) = Zof f lp LG NG e.1 e.2 := by
      intro e he
      rw [← hN1] at he
      obtain ⟨⟨i, κ, Dc⟩, hen, rfl⟩ := Multiset.mem_map.mp he
      refine ⟨Dc, ?_, ?_, hN2 _ hen⟩
      · refine NestedValue.nodeDec_of_mem ?_ (Multiset.mem_map_of_mem entK hen)
        rw [Multiset.map_map]
        have : Nd.map ((fun e : Σ j, NodeKey T K j × Multiset (NestInner T K j × K × Bool) =>
            (⟨e.1, e.2.1⟩ : Σ j, NodeKey T K j)) ∘ entK) = b.nodes := by
          rw [← hN1]; rfl
        rw [this]; exact b.nodup_nodes
      · refine NestedValue.nodeDec_of_mem ?_ (Multiset.mem_map_of_mem (entK' f lp LG NG) hen)
        rw [Multiset.map_map]
        have : Nd.map ((fun e : Σ j, NodeKey T K' j × Multiset (NestInner T K' j × K' × Bool) =>
            (⟨e.1, e.2.1⟩ : Σ j, NodeKey T K' j)) ∘ entK' f lp LG NG) = b'.nodes := by
          rw [hnodes, ← hN1, Multiset.map_map]; rfl
        rw [this]; exact b'.nodup_nodes
    have hv := val_of_rel hK (φ (R, L, Nd)).dec (φ' (R, L, Nd)).dec (· ∈ b.leaves) (· ∈ b.nodes)
      hLk hNk
    have hroot : ∀ m ∈ R, NestInner.val (φ' (R, L, Nd)).dec j m.1.1
          = NestInner.val (φ (R, L, Nd)).dec j m.1.2.2
        ∧ (NestInner.ok (φ' (R, L, Nd)).dec j m.1.1 ↔ NestInner.ok (φ (R, L, Nd)).dec j m.1.2.2) := by
      intro m hm
      have hz := hRz m hm
      have ho : (m.1.2.2, m.2.1) ∈ b.occs := by
        rw [show b.occs = N.occs from rfl, ← hZr2]
        exact Multiset.mem_map_of_mem (fun z => (z.1.2.2, z.2)) hz
      exact hv j _ _ (hZr3 _ hz).2 (fun κ hκ => NestedValue.mem_leaves ho hκ)
        (fun e he => NestedValue.mem_nodes ho he)
    -- the weights, family by family
    have hRf : ∀ m ∈ R, m.1.2.1 = f m.2.1 := fun m hm => (hZr3 _ (hRz m hm)).1
    have hNf : ∀ en ∈ Nd, ∀ m ∈ en.2.2, m.1.2.1 = f m.2.1 := by
      intro en hen m hm
      have hk : (⟨en.1, en.2.1⟩ : Σ j, NodeKey T K j) ∈ b.nodes := by
        rw [← hN1]; exact Multiset.mem_map_of_mem _ hen
      have hz : (m.1, m.2.1) ∈ Zof f lp LG NG en.1 en.2.1 := by
        rw [← hN2 en hen]; exact Multiset.mem_map_of_mem _ hm
      exact ((hzof _ hk).2 _ hz).1
    have hLf : ∀ e ∈ L, NestedValue.leafProd (lkey lp e.1, (lp e.1).moveS e.2)
          = f (NestedValue.leafProd e)
        ∧ NestedValue.leafAbs (lkey lp e.1, (lp e.1).moveS e.2) = f (NestedValue.leafAbs e) := by
      intro e he
      have hκ : e.1 ∈ b.leaves := by rw [← hL1]; exact Multiset.mem_map_of_mem _ he
      have hS := hL2 e he
      rw [hlen e.1 hκ, List.length_map] at hS
      unfold NestedValue.leafProd NestedValue.leafAbs lkey
      dsimp only
      rw [hlen e.1 hκ, List.length_map, List.length_map]
      exact ⟨(lp e.1).prod_moveS hS, (lp e.1).sum_moveS e.2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · show NestedValue.decProd (R.map _) * ((L.map _).map NestedValue.leafProd).prod
          * ((Nd.map (entK' f lp LG NG)).map _).prod
        = f (NestedValue.decProd (R.map _) * (L.map NestedValue.leafProd).prod
          * ((Nd.map entK).map _).prod)
      rw [map_mul, map_mul, (decProd_decAbs_pair R hRf).1, map_multiset_prod, map_multiset_prod,
        Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
      congr 2
      · exact congrArg Multiset.prod (Multiset.map_congr rfl (fun e he => (hLf e he).1))
      · exact Multiset.map_congr rfl (fun en hen => (decProd_decAbs_pair en.2.2 (hNf en hen)).1)
    · show NestedValue.decAbs (R.map _) + ((L.map _).map NestedValue.leafAbs).sum
          + ((Nd.map (entK' f lp LG NG)).map _).sum
        = f (NestedValue.decAbs (R.map _) + (L.map NestedValue.leafAbs).sum
          + ((Nd.map entK).map _).sum)
      rw [map_add, map_add, (decProd_decAbs_pair R hRf).2, map_multiset_sum, map_multiset_sum,
        Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
      congr 2
      · exact congrArg Multiset.sum (Multiset.map_congr rfl (fun e he => (hLf e he).2))
      · exact Multiset.map_congr rfl (fun en hen => (decProd_decAbs_pair en.2.2 (hNf en hen)).2)
    · show ((R.map _).filter _).map _ = ((R.map _).filter _).map _
      rw [Multiset.filter_map, Multiset.filter_map, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr (Multiset.filter_congr (fun _ _ => Iff.rfl))
        (fun m hm => (hroot m (Multiset.mem_of_mem_filter hm)).1)
    · constructor
      · intro hall m' hm' hp
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hm'
        exact (hroot m hm).2.mp (hall _ (Multiset.mem_map_of_mem _ hm) hp)
      · intro hall m' hm' hp
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hm'
        exact (hroot m hm).2.mpr (hall _ (Multiset.mem_map_of_mem _ hm) hp)

end Transfer
