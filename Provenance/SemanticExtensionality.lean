/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.Extensionality
import Mathlib.Tactic.Bound.Init
import all Provenance.DerivedAnn
import all Provenance.Extensionality
import all Provenance.FragQuery

/-!
# Extensionality for every semantics that extends semiring provenance

`Provenance.Extensionality` grades the m-semirings for one semantics, the
evaluator of the library. This module removes that dependence. A
*semantics* here is any function `S` from the closed queries of the
fragment syntax and the instances annotated in a semiring `K` to annotated
relations. It **extends semiring provenance**
(`ExtendsSemiringProvenance`) when base relations keep their annotations,
the unit is annotated `𝟙`, a projection keeps annotations, a union is the
multiset sum, a product multiplies, and duplicate elimination sums each
class, *on all arguments, negative ones included*. Nothing is asked of the
difference, the semijoin, or the antijoin, nor of homomorphisms, nor of any
agreement with SQL, and `K` is not assumed to have a monus.

For such an `S`:

* extensionality for `F₀` makes `⊗` commutative
  (`ExtendsSemiringProvenance.mul_comm_of_level0`);
* extensionality for `F₁` makes `(K, ⊕, ⊗)` a lattice
  (`ExtendsSemiringProvenance.isLatticeRig_of_level1`);
* extensionality for `F₂` gives every element a complement, whatever `S`
  does on negation (`ExtendsSemiringProvenance.isBooleanRig_of_level2`).

The complement comes from two pairs around a query `E` of arity `0` that
holds exactly when `R` is empty, its own annotation `c` being anything:
`R × E` against the empty query forces `b ⊗ c = 𝟘`, and `E ⊎ ε(Π∅ R)`
against the unit forces `c ⊕ b = 𝟙`. Neither compares values, so `NULL` plays
no part.

Over a commutative m-semiring the converse holds at `F₂`:
`exists_semantics_extensional_iff` says that a semantics extending semiring
provenance and extensional for `F₂` exists iff `K` is a Boolean m-semiring,
whatever its `δ`.
-/

@[expose] public section

namespace FragQueryIn

variable {T : Type} [ValueType T] {K : Type}

/-- The `⊕`-sum of the annotations one tuple carries, over any semiring. -/
def annCollapse [AddCommMonoid K] {n : ℕ} (r : AnnotatedRelation T K n) (u : Tuple T n) : K :=
  (Multiset.map Prod.snd (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u) r)).sum

/-- **A semantics extends semiring provenance** when it follows the clauses
of semiring provenance on the positive operators, for all arguments. The
negative operators are left free. -/
structure ExtendsSemiringProvenance [Semiring K]
    (S : ∀ n : ℕ, FragQuery T n → AnnotatedDatabase T K → AnnotatedRelation T K n) : Prop where
  rel : ∀ (n : ℕ) (s : String) (d : AnnotatedDatabase T K),
    S n (Rel n s) d = (d.find n s).getD (0 : Multiset (AnnotatedTuple T K n))
  empty : ∀ d : AnnotatedDatabase T K, S 0 Empty d = (0 : Multiset (AnnotatedTuple T K 0))
  unit : ∀ d : AnnotatedDatabase T K,
    S 0 Unit d = ({((fun j => j.elim0 : Tuple T 0), 1)} : Multiset (AnnotatedTuple T K 0))
  proj : ∀ {n m : ℕ} (ts : Tuple (TermGIn T 0 (ColKind.allReg n)) m) (q : FragQuery T n)
    (d : AnnotatedDatabase T K),
    S m (Proj ts q) d = (S n q d).map (fun p =>
      ((fun j => (ts j).evalPlain p.1 (fun _ => 0), p.2) : AnnotatedTuple T K _))
  sum : ∀ {n : ℕ} (q₁ q₂ : FragQuery T n) (d : AnnotatedDatabase T K),
    S n (Sum q₁ q₂) d = S n q₁ d + S n q₂ d
  prod : ∀ {n₁ n₂ : ℕ} (q₁ : FragQuery T n₁) (q₂ : FragQuery T n₂) (d : AnnotatedDatabase T K),
    S (n₁ + n₂) (Prod q₁ q₂) d = ((S n₁ q₁ d).product (S n₂ q₂ d)).map (fun xy =>
      ((Fin.append xy.1.1 xy.2.1, xy.1.2 * xy.2.2) : AnnotatedTuple T K _))
  dedup : ∀ {n : ℕ} (q : FragQuery T n) (d : AnnotatedDatabase T K),
    S n (Dedup q) d = ((S n q d).map Prod.fst).dedup.map (fun u =>
      ((u, annCollapse (S n q d) u) : AnnotatedTuple T K _))

/-- **`K` is extensional under `S` for the queries satisfying `F`**: two such
queries with the same plain semantics on every instance collapse, under `S`
and on every `K`-instance, to the same `K`-relation. -/
def ExtensionalUnder [Semiring K]
    (S : ∀ n : ℕ, FragQuery T n → AnnotatedDatabase T K → AnnotatedRelation T K n)
    (F : ∀ n : ℕ, FragQuery T n → Prop) : Prop :=
  ∀ (n : ℕ) (q₁ q₂ : FragQuery T n), F n q₁ → F n q₂ →
    (∀ (D : Database T) (γ : Fin 0 → T), q₁.semPlain D γ = q₂.semPlain D γ) →
    ∀ (d : AnnotatedDatabase T K) (u : Tuple T n), annCollapse (S n q₁ d) u = annCollapse (S n q₂ d) u

/-- The lattice laws of a semiring. -/
structure IsLatticeRig (K : Type) [Semiring K] : Prop where
  mul_comm : ∀ a b : K, a * b = b * a
  idempotent : idempotent K
  mulIdempotent : mulIdempotent K
  absorptive : absorptive K

/-- A semiring that is a lattice in which every element has a complement. -/
structure IsBooleanRig (K : Type) [Semiring K] : Prop extends IsLatticeRig K where
  exists_compl : ∀ b : K, ∃ c : K, b * c = 0 ∧ c + b = 1

section Collapse

variable [Semiring K]

private theorem annCollapse_singleton {n : ℕ} (p : AnnotatedTuple T K n) (u : Tuple T n) :
    annCollapse ({p} : Multiset (AnnotatedTuple T K n)) u = if p.1 = u then p.2 else 0 := by
  unfold annCollapse
  rw [Multiset.filter_singleton]
  split_ifs <;> simp

private theorem annCollapse_add {n : ℕ} (r s : Multiset (AnnotatedTuple T K n)) (u : Tuple T n) :
    annCollapse (r + s : Multiset (AnnotatedTuple T K n)) u = annCollapse r u + annCollapse s u := by
  unfold annCollapse
  rw [Multiset.filter_add, Multiset.map_add, Multiset.sum_add]

private theorem annCollapse_zero {n : ℕ} (u : Tuple T n) :
    annCollapse (0 : Multiset (AnnotatedTuple T K n)) u = 0 := by
  unfold annCollapse
  simp

private theorem annCollapse_map_nodup {n : ℕ} (s : Multiset (Tuple T n)) (hs : s.Nodup)
    (f : Tuple T n → K) (v : Tuple T n) :
    annCollapse (s.map (fun u => ((u, f u) : AnnotatedTuple T K n))) v
      = if v ∈ s then f v else 0 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.notMem_zero, ite_false]
    exact annCollapse_zero v
  | cons u s ih =>
    rw [Multiset.map_cons, ← Multiset.singleton_add, annCollapse_add, annCollapse_singleton,
      ih (Multiset.nodup_cons.mp hs).2]
    by_cases huv : u = v
    · subst huv
      simp [(Multiset.nodup_cons.mp hs).1]
    · simp [huv, Ne.symm huv]

/-- Duplicate elimination is invisible once collapsed. -/
private theorem annCollapse_dedup {n : ℕ} (r : Multiset (AnnotatedTuple T K n)) (v : Tuple T n) :
    annCollapse ((r.map Prod.fst).dedup.map
      (fun u => ((u, annCollapse (r : AnnotatedRelation T K n) u) : AnnotatedTuple T K n))) v
      = annCollapse r v := by
  rw [annCollapse_map_nodup _ (Multiset.nodup_dedup _)]
  split_ifs with hv
  · rfl
  · have hf : Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = v) r = 0 := by
      rw [Multiset.filter_eq_nil]
      intro p hp hpv
      exact hv (Multiset.mem_dedup.mpr (Multiset.mem_map.mpr ⟨p, hp, hpv⟩))
    unfold annCollapse
    rw [hf]
    simp

end Collapse

/-! ## The queries -/

/-- The swap of the two columns of a product of two relations of arity one. -/
abbrev swapCols : Tuple (TermGIn T 0 (ColKind.allReg (1 + 1))) (1 + 1) :=
  ![TermGIn.index 1 rfl, TermGIn.index 0 rfl]

/-- The left column of a product with a relation of arity `0`. -/
abbrev leftCol : Tuple (TermGIn T 0 (ColKind.allReg (1 + 0))) 1 := ![TermGIn.index 0 rfl]

/-- The projection of a relation of arity one on no column. -/
abbrev noCol : Tuple (TermGIn T 0 (ColKind.allReg 1)) 0 := fun j => j.elim0

/-- `ε(Π∅ R)`: the one empty tuple, exactly when `R` is non-empty. -/
abbrev nonEmptyR : FragQuery T 0 := Dedup (Proj noCol relR)

/-- `𝟏 − ε(Π∅ R)`: the one empty tuple, exactly when `R` is empty. -/
abbrev emptyR : FragQuery T 0 := Diff Unit nonEmptyR

/-- `E` tests that `R` is empty, on the plain semantics. -/
def TestsEmptyR (E : FragQuery T 0) : Prop :=
  ∀ (D : Database T) (γ : Fin 0 → T),
    (((show Multiset (Tuple T 1) from relR.semPlain D γ) = 0 →
        E.semPlain D γ = ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0)))
      ∧ ((show Multiset (Tuple T 1) from relR.semPlain D γ) ≠ 0 →
        E.semPlain D γ = (0 : Multiset (Tuple T 0))))

omit [ValueType T] in
private theorem tuple0_eq (u v : Tuple T 0) : u = v := funext (fun j => j.elim0)

private theorem semPlain_nonEmptyR (D : Database T) (γ : Fin 0 → T) :
    ((show Multiset (Tuple T 1) from relR.semPlain D γ) = 0 →
        (nonEmptyR (T := T)).semPlain D γ = (0 : Multiset (Tuple T 0)))
      ∧ ((show Multiset (Tuple T 1) from relR.semPlain D γ) ≠ 0 →
        (nonEmptyR (T := T)).semPlain D γ
          = ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0))) := by
  constructor
  · intro h0
    show (Multiset.map _ (relR.semPlain D γ)).dedup = 0
    rw [show relR.semPlain D γ = (0 : Multiset (Tuple T 1)) from h0]
    simp
  · intro hne
    obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero hne
    show (Multiset.map _ (relR.semPlain D γ)).dedup = _
    refine (Multiset.Nodup.ext (Multiset.nodup_dedup _) (Multiset.nodup_singleton _)).mpr
      (fun a => ?_)
    rw [Multiset.mem_dedup, Multiset.mem_singleton]
    exact ⟨fun _ => tuple0_eq _ _, fun _ => Multiset.mem_map.mpr ⟨v, hv, tuple0_eq _ _⟩⟩

/-- The difference tests emptiness. -/
theorem testsEmptyR_emptyR : TestsEmptyR (emptyR (T := T)) := by
  intro D γ
  have hne := semPlain_nonEmptyR (T := T) D γ
  constructor
  · intro h0
    show Multiset.filter _ ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0)) = _
    rw [Multiset.filter_singleton, ite_eq_left]
    show _ ∉ (show Multiset (Tuple T 0) from (nonEmptyR (T := T)).semPlain D γ)
    rw [show (nonEmptyR (T := T)).semPlain D γ = (0 : Multiset (Tuple T 0)) from hne.1 h0]
    exact Multiset.notMem_zero _
  · intro h
    show Multiset.filter _ ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0)) = _
    rw [Multiset.filter_singleton, ite_eq_right]
    · rfl
    show ¬ _ ∉ (show Multiset (Tuple T 0) from (nonEmptyR (T := T)).semPlain D γ)
    rw [show (nonEmptyR (T := T)).semPlain D γ
        = ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0)) from hne.2 h]
    simp

/-- The always-true match of a subquery row: `0 IS NOT DISTINCT FROM 0`. -/
abbrev matchAll : GenPredIn T (0 + 0) (ColKind.allReg 1) :=
  GenPredIn.cmp CompOp.syneq (TermGIn.const 0) (TermGIn.const 0)

/-- `SELECT 1 WHERE NOT EXISTS (SELECT * FROM R)`, on the empty tuple. -/
abbrev notExistsR (cnt : SeqAggFunc T) (hc : cnt.Counts) : FragQuery T 0 :=
  Antijoin cnt hc matchAll Unit (relRIn (0 + 0))

/-- `NOT EXISTS` tests emptiness. -/
theorem testsEmptyR_notExistsR (cnt : SeqAggFunc T) (hc : cnt.Counts) :
    TestsEmptyR (notExistsR (T := T) cnt hc) := by
  intro D γ
  have hm : ∀ u : Tuple T 0,
      (show Multiset (Tuple T 1) from
        matchesPlain matchAll (relRIn (0 + 0)).semPlain D γ u)
        = (show Multiset (Tuple T 1) from relR.semPlain D γ) := by
    intro u
    refine Multiset.filter_eq_self.mpr (fun v _ => ?_)
    unfold GenPredIn.holdsPlain GenPredIn.evalPlain3
    show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true
    simp [CompOp.eval3, CompOp.strict, CompOp.eval]
  constructor
  · intro h0
    show Multiset.filter _ ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0)) = _
    rw [Multiset.filter_singleton, ite_eq_left]
    show (show Multiset (Tuple T 1) from
      matchesPlain matchAll (relRIn (0 + 0)).semPlain D γ _) = 0
    rw [hm]
    exact h0
  · intro h
    show Multiset.filter _ ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0)) = _
    rw [Multiset.filter_singleton, ite_eq_right]
    · rfl
    show ¬ (show Multiset (Tuple T 1) from
      matchesPlain matchAll (relRIn (0 + 0)).semPlain D γ _) = 0
    rw [hm]
    exact h

/-! ## The computations under a semantics -/

variable [Semiring K]
  {S : ∀ n : ℕ, FragQuery T n → AnnotatedDatabase T K → AnnotatedRelation T K n}

private theorem prod_singletons (h : ExtendsSemiringProvenance S)
    {d : AnnotatedDatabase T K} {n₁ n₂ : ℕ} (e₁ : FragQuery T n₁) (e₂ : FragQuery T n₂)
    (v : Tuple T n₁) (w : Tuple T n₂) (a b : K)
    (h₁ : S n₁ e₁ d = ({(v, a)} : Multiset (AnnotatedTuple T K n₁)))
    (h₂ : S n₂ e₂ d = ({(w, b)} : Multiset (AnnotatedTuple T K n₂))) :
    S (n₁ + n₂) (Prod e₁ e₂) d
      = ({(Fin.append v w, a * b)} : Multiset (AnnotatedTuple T K (n₁ + n₂))) := by
  rw [h.prod, h₁, h₂]
  rw [show Multiset.product ({(v, a)} : Multiset (AnnotatedTuple T K n₁))
      ({(w, b)} : Multiset (AnnotatedTuple T K n₂)) = {((v, a), (w, b))} from
    Multiset.product_singleton (v, a) (w, b)]
  exact Multiset.map_singleton _ _

private theorem proj_singleton (h : ExtendsSemiringProvenance S)
    {d : AnnotatedDatabase T K} {n m : ℕ} (ts : Tuple (TermGIn T 0 (ColKind.allReg n)) m)
    (q : FragQuery T n) (p : AnnotatedTuple T K n)
    (hq : S n q d = ({p} : Multiset (AnnotatedTuple T K n))) :
    S m (Proj ts q) d
      = ({((fun j => (ts j).evalPlain p.1 (fun _ => 0), p.2) : AnnotatedTuple T K m)}
          : Multiset (AnnotatedTuple T K m)) := by
  rw [h.proj, hq]
  exact Multiset.map_singleton _ _

private theorem proj_prod_singletons (h : ExtendsSemiringProvenance S)
    {d : AnnotatedDatabase T K} (e₁ e₂ : FragQuery T 1) (x : T) (a b : K)
    (h₁ : S 1 e₁ d = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)))
    (h₂ : S 1 e₂ d = ({(![x], b)} : Multiset (AnnotatedTuple T K 1))) :
    S 1 (Proj projFst (Prod e₁ e₂)) d = ({(![x], a * b)} : Multiset (AnnotatedTuple T K 1)) := by
  rw [h.proj, h.prod, h₁, h₂]
  rw [show Multiset.product ({(![x], a)} : Multiset (AnnotatedTuple T K 1))
      ({(![x], b)} : Multiset (AnnotatedTuple T K 1)) = {((![x], a), (![x], b))} from
    Multiset.product_singleton (![x], a) (![x], b)]
  refine (congrArg (Multiset.map _) (Multiset.map_singleton _ _)).trans ?_
  refine (Multiset.map_singleton _ _).trans ?_
  refine congrArg (fun p : AnnotatedTuple T K 1 => ({p} : Multiset _)) (Prod.ext ?_ rfl)
  funext j
  rw [Fin.fin_one_eq_zero j]
  show Fin.append (![x]) (![x]) (Fin.castAdd 1 0) = x
  rw [Fin.append_left]
  rfl

private theorem rel_R_one (h : ExtendsSemiringProvenance S) (x : T) (a : K) :
    S 1 relR (oneTupleDb x a) = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) := by
  rw [h.rel]
  rfl

private theorem rel_R_two (h : ExtendsSemiringProvenance S) (x : T) (a b : K) :
    S 1 relR (twoRelDb x a b) = ({(![x], a)} : Multiset (AnnotatedTuple T K 1)) := by
  rw [h.rel]
  rfl

private theorem rel_S_two (h : ExtendsSemiringProvenance S) (x : T) (a b : K) :
    S 1 relS (twoRelDb x a b) = ({(![x], b)} : Multiset (AnnotatedTuple T K 1)) := by
  rw [h.rel]
  rfl

private theorem collapse_dedup (h : ExtendsSemiringProvenance S) {n : ℕ} (q : FragQuery T n)
    (d : AnnotatedDatabase T K) (u : Tuple T n) :
    annCollapse (S n (Dedup q) d) u = annCollapse (S n q d) u := by
  rw [h.dedup]
  exact annCollapse_dedup _ u

private theorem collapse_sum (h : ExtendsSemiringProvenance S) {n : ℕ} (q₁ q₂ : FragQuery T n)
    (d : AnnotatedDatabase T K) (u : Tuple T n) :
    annCollapse (S n (Sum q₁ q₂) d) u = annCollapse (S n q₁ d) u + annCollapse (S n q₂ d) u := by
  rw [h.sum]
  exact annCollapse_add _ _ u

/-! ## What extensionality forces -/

/-- **`⊗` is commutative** where `K` is extensional for `F₀` under `S`. -/
theorem ExtendsSemiringProvenance.mul_comm_of_level0 (h : ExtendsSemiringProvenance S)
    (hext : ExtensionalUnder S (fun _ q => q.level0)) (a b : K) : a * b = b * a := by
  have hplain : ∀ (D : Database T) (γ : Fin 0 → T),
      (Proj (swapCols (T := T)) (Prod relR relS)).semPlain D γ
        = (Prod relS relR).semPlain D γ := by
    intro D γ
    simp only [semPlain]
    rw [Multiset.map_map, show Multiset.product
        (((D.find 1 "S").getD (0 : Multiset (Tuple T 1))) : Multiset (Tuple T 1))
        ((D.find 1 "R").getD (0 : Multiset (Tuple T 1)))
      = (Multiset.product ((D.find 1 "R").getD (0 : Multiset (Tuple T 1)))
          ((D.find 1 "S").getD (0 : Multiset (Tuple T 1)))).map Prod.swap from
      (Multiset.map_swap_product _ _).symm, Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    obtain ⟨u, v⟩ := p
    funext k
    refine Fin.addCases (m := 1) (n := 1) (fun j => ?_) (fun j => ?_) k
    · rw [Fin.fin_one_eq_zero j]
      show Fin.append u v (Fin.natAdd 1 0) = Fin.append v u (Fin.castAdd 1 0)
      rw [Fin.append_right, Fin.append_left]
    · rw [Fin.fin_one_eq_zero j]
      show Fin.append u v (Fin.castAdd 1 0) = Fin.append v u (Fin.natAdd 1 0)
      rw [Fin.append_right, Fin.append_left]
  have := hext (1 + 1) (Proj swapCols (Prod relR relS)) (Prod relS relR)
    (by simp [level0]) (by simp [level0]) hplain (twoRelDb (0 : T) a b) (Fin.append ![0] ![0])
  rw [proj_singleton h _ _ _ (prod_singletons h _ _ _ _ _ _ (rel_R_two h _ _ _) (rel_S_two h _ _ _)),
    prod_singletons h _ _ _ _ _ _ (rel_S_two h _ _ _) (rel_R_two h _ _ _),
    annCollapse_singleton, annCollapse_singleton] at this
  rw [ite_eq_left, ite_eq_left] at this
  · exact this
  · rfl
  · funext k
    refine Fin.addCases (m := 1) (n := 1) (fun j => ?_) (fun j => ?_) k
    · rw [Fin.fin_one_eq_zero j]
      show Fin.append (![(0 : T)]) (![0]) (Fin.natAdd 1 0)
        = Fin.append (![(0 : T)]) (![0]) (Fin.castAdd 1 0)
      rw [Fin.append_right, Fin.append_left]
    · rw [Fin.fin_one_eq_zero j]
      show Fin.append (![(0 : T)]) (![0]) (Fin.castAdd 1 0)
        = Fin.append (![(0 : T)]) (![0]) (Fin.natAdd 1 0)
      rw [Fin.append_right, Fin.append_left]

private theorem plainEq_of_plainEquiv {n : ℕ} {e₁ e₂ : FragQuery T n}
    (hp : e₁.toAgg.PlainEquiv e₂.toAgg) (D : Database T) (γ : Fin 0 → T) :
    e₁.semPlain D γ = e₂.semPlain D γ :=
  (toAgg_plainEquiv_iff e₁ e₂).mp hp D γ

/-- **`(K, ⊕, ⊗)` is a lattice** where `K` is extensional for `F₁` under `S`. -/
theorem ExtendsSemiringProvenance.isLatticeRig_of_level1 (h : ExtendsSemiringProvenance S)
    (hext : ExtensionalUnder S (fun _ q => q.level1)) : IsLatticeRig K := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine h.mul_comm_of_level0 (fun n q₁ q₂ h₁ h₂ => hext n q₁ q₂ ?_ ?_)
    · exact level1_of_level0 q₁ h₁
    · exact level1_of_level0 q₂ h₂
  · intro a
    have := hext 1 pairAddIdem₁ pairAddIdem₂ (by simp [level1]) (by simp [level1])
      (plainEq_of_plainEquiv pairAddIdem_plainEquiv) (oneTupleDb (0 : T) a) ![0]
    rw [collapse_dedup h, collapse_dedup h, h.sum] at this
    rw [rel_R_one h] at this
    erw [annCollapse_add] at this
    have e : annCollapse ({(![0], a)} : Multiset (AnnotatedTuple T K 1)) ![(0 : T)] = a := by
      rw [annCollapse_singleton]
      exact ite_eq_left rfl
    erw [e] at this
    exact this.symm
  · intro a
    have := hext 1 pairMulIdem₁ pairMulIdem₂ (by simp [level1]) (by simp [level1])
      (plainEq_of_plainEquiv pairMulIdem_plainEquiv) (oneTupleDb (0 : T) a) ![0]
    rw [collapse_dedup h, collapse_dedup h,
      proj_prod_singletons h _ _ (0 : T) a a (rel_R_one h _ _) (rel_R_one h _ _), rel_R_one h,
      annCollapse_singleton, annCollapse_singleton] at this
    simpa using this.symm
  · intro b
    have := hext 1 pairAbs₁ pairAbs₂ (by simp [level1]) (by simp [level1])
      (plainEq_of_plainEquiv pairAbs_plainEquiv) (twoRelDb (0 : T) 1 b) ![0]
    rw [collapse_dedup h, collapse_dedup h, collapse_sum h,
      proj_prod_singletons h _ _ (0 : T) 1 b (rel_R_two h _ _ _) (rel_S_two h _ _ _), rel_R_two h,
      annCollapse_singleton, annCollapse_singleton] at this
    simpa using this.symm

/-! ## The complement -/

/-- The collapse of `Π₁(R × E)` is the annotation of `R` times the collapse
of `E`, whatever `E` holds: every tuple of arity `0` is the one tuple. -/
private theorem collapse_left_prod (h : ExtendsSemiringProvenance S) (E : FragQuery T 0) (x : T)
    (b : K) (u₀ : Tuple T 0) :
    annCollapse (S 1 (Proj (leftCol (T := T)) (Prod relR E)) (oneTupleDb x b)) ![x]
      = b * annCollapse (S 0 E (oneTupleDb x b)) u₀ := by
  rw [h.proj, h.prod, rel_R_one h]
  generalize (S 0 E (oneTupleDb x b)) = e
  show annCollapse (Multiset.map _ (Multiset.map _ (Multiset.product _ _))) _ = _
  unfold Multiset.product
  rw [Multiset.singleton_bind, Multiset.map_map, Multiset.map_map]
  refine Multiset.induction_on (p := fun e : Multiset (AnnotatedTuple T K 0) =>
    annCollapse (Multiset.map _ e) ![x] = b * annCollapse e u₀) e ?_ ?_
  · rw [Multiset.map_zero, annCollapse_zero, annCollapse_zero, mul_zero]
  · intro p s ih
    rw [Multiset.map_cons, ← Multiset.singleton_add, ← Multiset.singleton_add, annCollapse_add,
      annCollapse_add, ih, annCollapse_singleton, annCollapse_singleton, mul_add,
      ite_eq_left (tuple0_eq _ _), ite_eq_left]
    · rfl
    · funext j
      rw [Fin.fin_one_eq_zero j]
      show Fin.append (![x]) p.1 (Fin.castAdd 0 0) = x
      rw [Fin.append_left]
      rfl

/-- **Every element has a complement** where `K` is extensional for `F₂`
under `S`: the annotation `S` gives a query that tests the emptiness of `R`,
whatever it is, is the complement. -/
theorem ExtendsSemiringProvenance.compl_of_test (h : ExtendsSemiringProvenance S)
    (hext : ExtensionalUnder S (fun _ _ => True)) {E : FragQuery T 0} (hE : TestsEmptyR E)
    (b : K) (u₀ : Tuple T 0) :
    b * annCollapse (S 0 E (oneTupleDb (0 : T) b)) u₀ = 0
      ∧ annCollapse (S 0 E (oneTupleDb (0 : T) b)) u₀ + b = 1 := by
  constructor
  · have hplain : ∀ (D : Database T) (γ : Fin 0 → T),
        (Proj (leftCol (T := T)) (Prod relR E)).semPlain D γ = (pairExcl₂ (0 : T)).semPlain D γ := by
      intro D γ
      show Multiset.map _ (Multiset.map _ (Multiset.product
          (relR.semPlain D γ : Multiset (Tuple T 1)) (E.semPlain D γ : Multiset (Tuple T 0))))
        = Multiset.map _ (0 : Multiset (Tuple T 0))
      by_cases h0 : (show Multiset (Tuple T 1) from relR.semPlain D γ) = 0
      · rw [show (relR.semPlain D γ : Multiset (Tuple T 1)) = 0 from h0]
        simp [Multiset.product]
      · rw [show (E.semPlain D γ : Multiset (Tuple T 0)) = 0 from (hE D γ).2 h0]
        simp [Multiset.product]
    have := hext 1 _ _ trivial trivial hplain (oneTupleDb (0 : T) b) ![0]
    rw [collapse_left_prod h E 0 b u₀, h.proj, h.empty, Multiset.map_zero] at this
    rw [this]
    exact annCollapse_zero _
  · have hplain : ∀ (D : Database T) (γ : Fin 0 → T),
        (Sum E nonEmptyR).semPlain D γ = (Unit : FragQuery T 0).semPlain D γ := by
      intro D γ
      have hn := semPlain_nonEmptyR (T := T) D γ
      show (E.semPlain D γ : Multiset (Tuple T 0)) + (nonEmptyR.semPlain D γ : Multiset (Tuple T 0))
        = ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0))
      by_cases h0 : (show Multiset (Tuple T 1) from relR.semPlain D γ) = 0
      · rw [show (E.semPlain D γ : Multiset (Tuple T 0)) = _ from (hE D γ).1 h0,
          show (nonEmptyR.semPlain D γ : Multiset (Tuple T 0)) = 0 from hn.1 h0]
        exact add_zero ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0))
      · rw [show (E.semPlain D γ : Multiset (Tuple T 0)) = 0 from (hE D γ).2 h0,
          show (nonEmptyR.semPlain D γ : Multiset (Tuple T 0)) = _ from hn.2 h0]
        exact zero_add ({(fun j => j.elim0 : Tuple T 0)} : Multiset (Tuple T 0))
    have := hext 0 _ _ trivial trivial hplain (oneTupleDb (0 : T) b) u₀
    rw [collapse_sum h, collapse_dedup h, proj_singleton h _ _ _ (rel_R_one h _ _), h.unit,
      annCollapse_singleton, annCollapse_singleton, ite_eq_left (tuple0_eq _ _),
      ite_eq_left (tuple0_eq _ _)] at this
    exact this

/-- **Extensionality for `F₂` under a semantics that extends semiring
provenance makes `K` a Boolean algebra**, whatever the semantics does on
negation. -/
theorem ExtendsSemiringProvenance.isBooleanRig_of_level2 (h : ExtendsSemiringProvenance S)
    (hext : ExtensionalUnder S (fun _ _ => True)) : IsBooleanRig K where
  toIsLatticeRig := h.isLatticeRig_of_level1
    (fun n q₁ q₂ _ _ hp d u => hext n q₁ q₂ trivial trivial hp d u)
  exists_compl b := ⟨_, h.compl_of_test hext testsEmptyR_emptyR b (fun j => j.elim0)⟩

end FragQueryIn

/-! ## Over a commutative m-semiring -/

section Monus

variable {T : Type} [ValueType T] {K : Type} [CommSemiringWithMonus K] [DecidableEq K]
  [HasAltLinearOrder K]

open FragQueryIn

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- In a commutative m-semiring, a Boolean rig is a Boolean m-semiring: the
monus against `𝟙` is below the complement, hence disjoint from the element. -/
theorem FragQueryIn.IsBooleanRig.isBooleanSemiring (hR : IsBooleanRig K) : IsBooleanSemiring K := by
  have hL : IsLatticeSemiring K := ⟨hR.absorptive, hR.mulIdempotent⟩
  refine { hL with exclusive := fun a => ?_ }
  obtain ⟨c, hac, hca⟩ := hR.exists_compl a
  have hle : HSub.hSub (1 : K) a ≤ c :=
    (SemiringWithMonus.monus_spec 1 a c).mpr (by rw [add_comm, hca])
  refine le_antisymm ?_ zero_le
  calc a * HSub.hSub (1 : K) a ≤ a * c := hL.mul_le_mul le_rfl hle
    _ = 0 := hac

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- The semantics of the fragment extends semiring provenance. -/
theorem sem_extendsSemiringProvenance :
    ExtendsSemiringProvenance (T := T) (K := K) (fun _ q d => q.sem d (fun _ => 0)) where
  rel _ _ _ := rfl
  empty _ := rfl
  unit _ := rfl
  proj _ _ _ := rfl
  sum _ _ _ := rfl
  prod _ _ _ := rfl
  dedup _ _ := rfl

/-- **Over a commutative m-semiring, a semantics extending semiring
provenance and extensional for `F₂` exists iff `K` is a Boolean m-semiring**,
whatever its `δ`. -/
theorem exists_semantics_extensional_iff :
    (∃ S : ∀ n : ℕ, FragQuery T n → AnnotatedDatabase T K → AnnotatedRelation T K n,
        ExtendsSemiringProvenance S ∧ ExtensionalUnder S (fun _ _ => True))
      ↔ IsBooleanSemiring K := by
  constructor
  · rintro ⟨S, hS, hext⟩
    exact (hS.isBooleanRig_of_level2 hext).isBooleanSemiring
  · intro hB
    refine ⟨_, sem_extendsSemiringProvenance, fun n q₁ q₂ _ _ hp d u => ?_⟩
    have hE : Extensional T K AggQueryIn.InLevel2 := extensional_level2_iff.mpr hB
    have := hE q₁.toAgg q₂.toAgg ⟨q₁, rfl⟩ ⟨q₂, rfl⟩ ((toAgg_plainEquiv_iff q₁ q₂).mpr hp) d u
    rw [annSum_toAgg_evaluateAnnotated _ (fun _ => hB.absorptive),
      annSum_toAgg_evaluateAnnotated _ (fun _ => hB.absorptive)] at this
    exact this

/-! ## The copies themselves need not agree

Collapsing is necessary from `F₂` on. Splitting `R` on whether `S` is
non-empty returns `R` on every plain instance, without counting anything, and
gives one tuple two copies where `R` gives it one. -/

namespace FragQueryIn

/-- The base relation `S` of arity `1`, in a context. -/
abbrev relSIn (c : ℕ) : FragQueryIn T c 1 := Rel 1 "S"

/-- The always-true match of a row of `R` with a row of `S`. -/
abbrev matchAllR : GenPredIn T (1 + 0) (ColKind.allReg 1) :=
  GenPredIn.cmp CompOp.syneq (TermGIn.const 0) (TermGIn.const 0)

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
private theorem matchAllR_holds (v : Tuple T 1) (γ : Fin (1 + 0) → T) :
    (matchAllR (T := T)).holdsPlain v γ := by
  unfold GenPredIn.holdsPlain GenPredIn.evalPlain3
  show CompOp.syneq.eval3 (0 : T) 0 = Kleene.true
  simp [CompOp.eval3, CompOp.strict, CompOp.eval]

/-- **The split of `R`** on whether `S` is non-empty:
`SELECT x FROM R WHERE EXISTS (SELECT * FROM S) UNION ALL
SELECT x FROM R WHERE NOT EXISTS (SELECT * FROM S)`. -/
abbrev splitR (cnt : SeqAggFunc T) (hc : cnt.Counts) : FragQuery T 1 :=
  Sum (Semijoin cnt hc matchAllR relR (relSIn (1 + 0)))
    (Antijoin cnt hc matchAllR relR (relSIn (1 + 0)))

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **The split of `R` is `R`** on every plain instance. -/
theorem splitR_semPlain (cnt : SeqAggFunc T) (hc : cnt.Counts) (D : Database T) (γ : Fin 0 → T) :
    (splitR cnt hc).semPlain D γ = relR.semPlain D γ := by
  show Multiset.filter _ (relR.semPlain D γ) + Multiset.filter _ (relR.semPlain D γ)
    = (relR.semPlain D γ : Multiset (Tuple T 1))
  rw [add_comm]
  exact Multiset.filter_add_not _ _

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **The copies of the split**: on `R = {x : a}` and `S = {x : s}`, the tuple
has two copies, annotated `a ⊗ s` and `a ⊗ (𝟙 ⊖ s)`, where `R` gives it one,
annotated `a`. -/
theorem splitR_sem (cnt : SeqAggFunc T) (hc : cnt.Counts) (x : T) (a s : K) (γ : Fin 0 → T) :
    @Eq (Multiset (AnnotatedTuple T K 1)) ((splitR cnt hc).sem (twoRelDb x a s) γ)
      (({(![x], a * s)} : Multiset (AnnotatedTuple T K 1))
        + {(![x], a * HSub.hSub (1 : K) s)}) := by
  have hm : ∀ u : Tuple T 1, matchesAnn matchAllR (relSIn (1 + 0)).sem (twoRelDb x a s) γ u
      = ({(![x], s)} : Multiset (AnnotatedTuple T K 1)) := by
    intro u
    show Multiset.filter _ ({(![x], s)} : Multiset (AnnotatedTuple T K 1)) = _
    rw [Multiset.filter_singleton, ite_eq_left]
    exact matchAllR_holds _ _
  have ht : AnnotatedRelation.annTotal ({(![x], s)} : Multiset (AnnotatedTuple T K 1)) = s := by
    unfold AnnotatedRelation.annTotal
    rw [Multiset.map_singleton, Multiset.sum_singleton]
  show ({(![x], a * AnnotatedRelation.annTotal
        (matchesAnn matchAllR (relSIn (1 + 0)).sem (twoRelDb x a s) γ ![x]))}
        : Multiset (AnnotatedTuple T K 1))
      + {(![x], a * HSub.hSub (1 : K) (AnnotatedRelation.annTotal
        (matchesAnn matchAllR (relSIn (1 + 0)).sem (twoRelDb x a s) γ ![x])))} = _
  rw [hm, ht]

omit [DecidableEq K] [HasAltLinearOrder K] in
/-- **The copies differ, even with `𝟘` set aside**: `R` holds a copy annotated `𝟙`
that the split does not, as soon as neither `s` nor `𝟙 ⊖ s` is `𝟙`, in
particular for a variable `s` of `𝔹[X]`. -/
theorem splitR_copies_ne (cnt : SeqAggFunc T) (hc : cnt.Counts) (x : T) (s : K) (γ : Fin 0 → T)
    (h₁ : s ≠ 1) (h₂ : HSub.hSub (1 : K) s ≠ 1) :
    ((![x], (1 : K)) : AnnotatedTuple T K 1)
        ∈ (show Multiset (AnnotatedTuple T K 1) from relR.sem (twoRelDb x 1 s) γ)
      ∧ ((![x], (1 : K)) : AnnotatedTuple T K 1)
        ∉ (show Multiset (AnnotatedTuple T K 1) from (splitR cnt hc).sem (twoRelDb x 1 s) γ) := by
  constructor
  · show _ ∈ ({(![x], (1 : K))} : Multiset (AnnotatedTuple T K 1))
    exact Multiset.mem_singleton_self _
  · intro hmem
    have hmem' := hmem
    change _ ∈ (show Multiset (AnnotatedTuple T K 1) from (splitR cnt hc).sem (twoRelDb x 1 s) γ)
      at hmem'
    rw [show (show Multiset (AnnotatedTuple T K 1) from (splitR cnt hc).sem (twoRelDb x 1 s) γ)
      = _ from splitR_sem cnt hc x 1 s γ, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_singleton, one_mul, one_mul] at hmem'
    rcases hmem' with h | h
    · exact h₁ (congrArg Prod.snd h).symm
    · exact h₂ (congrArg Prod.snd h).symm

end FragQueryIn

end Monus
