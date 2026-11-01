/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.FragQuery
public import Provenance.SupportAdequacy
public import Provenance.Semirings.Nat
import Mathlib.Tactic.Bound.Init
import all Provenance.DerivedAnn

/-!
# The fragment semantics under homomorphisms, over `𝔹` and over `ℕ`

Three readings of the closed-form annotated semantics
`FragQueryIn.sem`, each an induction over the syntax, and together what
the extensionality theorem of `Provenance.Extensionality` needs.

* **Homomorphisms.** A semiring homomorphism `h : K →+* K'` commutes with
  the semantics (`FragQueryIn.sem_mapAnn`), provided it preserves the
  monus where the query uses one – a difference or an antijoin
  (`FragQueryIn.hasMonus`). Nothing is asked about `δ`, which the
  fragment never reads: this is what lets a point of a lattice
  m-semiring, which is a semiring homomorphism onto `𝔹` and nothing more,
  be pushed through a query of `F₁`.
* **Over `𝔹`.** A tuple is in the support of the annotated result exactly
  when it is in the plain result of the support of the instance
  (`FragQueryIn.mem_support_sem`), for every query of the fragment.
* **Over `ℕ`.** Reading an `ℕ`-annotation as a multiplicity
  (`AnnotatedRelation.unfold`), the plain semantics of the unfolded
  instance is the unfolded annotated semantics, on `F₀`
  (`FragQueryIn.semPlain_unfold`): the adequacy in `ℕ` of the positive
  fragment, with multiplicities in place of `𝟙`.
-/

@[expose] public section

variable {T : Type} [ValueType T]
variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]

/-! ## Pushing a function through the annotations -/

/-- The annotations of a relation, read through a function. -/
def AnnotatedRelation.mapAnn {K' : Type} (f : K → K') {n : ℕ} (r : AnnotatedRelation T K n) :
    AnnotatedRelation T K' n :=
  r.map (fun p => ((p.1, f p.2) : AnnotatedTuple T K' n))

/-- The annotations of a database, read through a function. -/
def AnnotatedDatabase.mapAnn {K' : Type} (f : K → K') (d : AnnotatedDatabase T K) :
    AnnotatedDatabase T K' :=
  d.map (fun e => (e.fst, ⟨e.snd.fst, e.snd.snd.mapAnn f⟩))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- `find` commutes with reading the annotations through a function. -/
theorem AnnotatedDatabase.find_mapAnn {K' : Type} (f : K → K') (n : ℕ) (s : String)
    (d : AnnotatedDatabase T K) :
    (d.mapAnn f).find n s = (d.find n s).map (AnnotatedRelation.mapAnn f) := by
  induction d with
  | nil =>
    unfold AnnotatedDatabase.mapAnn AnnotatedDatabase.find AnnotatedDatabase.find.f
    simp
  | cons hd tl ih =>
    unfold AnnotatedDatabase.mapAnn AnnotatedDatabase.find AnnotatedDatabase.find.f
    by_cases hcond : n = hd.snd.fst ∧ s = hd.fst
    · simp [hcond]
      have := hcond.left
      subst this
      rfl
    · simp [hcond]
      unfold AnnotatedDatabase.mapAnn AnnotatedDatabase.find at ih
      exact ih

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The tuples of a relation are untouched. -/
theorem AnnotatedRelation.map_fst_mapAnn {K' : Type} (f : K → K') {n : ℕ}
    (r : AnnotatedRelation T K n) :
    (r.mapAnn f).map Prod.fst = (show Multiset (AnnotatedTuple T K n) from r).map Prod.fst := by
  unfold AnnotatedRelation.mapAnn
  rw [Multiset.map_map]
  rfl

omit [DecidableEq K] in
/-- The `⊕`-sum of the annotations of a tuple, through a semiring
homomorphism. -/
theorem AnnotatedRelation.annSum_mapAnn {K' : Type} [CommSemiringWithMonus K']
    [DecidableEq K'] (h : K →+* K') {n : ℕ} (r : AnnotatedRelation T K n) (u : Tuple T n) :
    (r.mapAnn h).annSum u = h (r.annSum u) := by
  unfold AnnotatedRelation.annSum AnnotatedRelation.mapAnn
  rw [Multiset.filter_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  rfl

omit [ValueType T] [DecidableEq K] in
/-- The `⊕`-sum of all the annotations, through a semiring
homomorphism. -/
theorem AnnotatedRelation.annTotal_mapAnn {K' : Type} [CommSemiringWithMonus K']
    [DecidableEq K'] (h : K →+* K') {n : ℕ} (r : AnnotatedRelation T K n) :
    (r.mapAnn h).annTotal = h r.annTotal := by
  unfold AnnotatedRelation.annTotal AnnotatedRelation.mapAnn
  rw [Multiset.map_map, map_multiset_sum, Multiset.map_map]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A filter on the tuples passes under the pushforward. -/
theorem AnnotatedRelation.filter_mapAnn {K' : Type} (f : K → K') {n : ℕ}
    (r : AnnotatedRelation T K n) (P : Tuple T n → Prop) [DecidablePred P] :
    Multiset.filter (fun p : AnnotatedTuple T K' n => P p.1) (r.mapAnn f)
      = AnnotatedRelation.mapAnn f (Multiset.filter (fun p : AnnotatedTuple T K n => P p.1) r) := by
  unfold AnnotatedRelation.mapAnn
  rw [Multiset.filter_map]
  rfl

namespace FragQueryIn

/-- Whether a query uses the monus: a difference or an antijoin
somewhere. -/
def hasMonus : {c n : ℕ} → FragQueryIn T c n → Prop
  | _, _, Rel _ _ => False
  | _, _, Empty => False
  | _, _, Unit => False
  | _, _, Proj _ q => q.hasMonus
  | _, _, Sel _ q => q.hasMonus
  | _, _, Prod q₁ q₂ => q₁.hasMonus ∨ q₂.hasMonus
  | _, _, Apply q₁ q₂ => q₁.hasMonus ∨ q₂.hasMonus
  | _, _, Sum q₁ q₂ => q₁.hasMonus ∨ q₂.hasMonus
  | _, _, Dedup q => q.hasMonus
  | _, _, Diff _ _ => True
  | _, _, Semijoin _ _ _ q₁ q₂ => q₁.hasMonus ∨ q₂.hasMonus
  | _, _, Antijoin _ _ _ _ _ => True

/-- A query of `F₁` uses no monus. -/
theorem not_hasMonus_of_level1 : ∀ {c n : ℕ} (q : FragQueryIn T c n),
    q.level1 → ¬ q.hasMonus
  | _, _, Rel _ _, _, h => h
  | _, _, Empty, _, h => h
  | _, _, Unit, _, h => h
  | _, _, Proj _ q, hq, h => not_hasMonus_of_level1 q hq h
  | _, _, Sel _ q, hq, h => not_hasMonus_of_level1 q hq h
  | _, _, Prod q₁ q₂, hq, h =>
    h.elim (not_hasMonus_of_level1 q₁ hq.1) (not_hasMonus_of_level1 q₂ hq.2)
  | _, _, Apply q₁ q₂, hq, h =>
    h.elim (not_hasMonus_of_level1 q₁ hq.1) (not_hasMonus_of_level1 q₂ hq.2)
  | _, _, Sum q₁ q₂, hq, h =>
    h.elim (not_hasMonus_of_level1 q₁ hq.1) (not_hasMonus_of_level1 q₂ hq.2)
  | _, _, Dedup q, hq, h => not_hasMonus_of_level1 q hq h
  | _, _, Diff _ _, hq, _ => hq.elim
  | _, _, Semijoin _ _ _ q₁ q₂, hq, h =>
    h.elim (not_hasMonus_of_level1 q₁ hq.1) (not_hasMonus_of_level1 q₂ hq.2)
  | _, _, Antijoin _ _ _ _ _, hq, _ => hq.elim

/-! ## Homomorphisms -/

omit [DecidableEq K] in
/-- **The semantics commutes with a semiring homomorphism** that
preserves the monus where the query uses one. -/
theorem sem_mapAnn {K' : Type} [CommSemiringWithMonus K'] [DecidableEq K'] (h : K →+* K') :
    ∀ {c n : ℕ} (q : FragQueryIn T c n),
      (q.hasMonus → ∀ x y : K, h (x - y) = h x - h y) →
      ∀ (d : AnnotatedDatabase T K) (γ : Fin c → T),
      q.sem (d.mapAnn h) γ = (q.sem d γ).mapAnn h
  | _, n, Rel _ s, hsub, d, γ => by
    simp only [sem, AnnotatedDatabase.find_mapAnn]
    cases d.find n s <;> rfl
  | _, _, Empty, hsub, d, γ => rfl
  | _, _, Unit, hsub, d, γ => by
    simp only [sem, AnnotatedRelation.mapAnn, Multiset.map_singleton, map_one]
  | _, _, Proj ts q, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q hsub d γ]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.map_map, Multiset.map_map]
    rfl
  | _, _, Sel φ q, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q hsub d γ]
    exact AnnotatedRelation.filter_mapAnn h _ (fun v => φ.holdsPlain v γ)
  | _, _, Prod q₁ q₂, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q₁ (fun hm => hsub (Or.inl hm)) d γ,
      sem_mapAnn h q₂ (fun hm => hsub (Or.inr hm)) d γ]
    unfold AnnotatedRelation.mapAnn
    rw [AggQueryIn.product_map_map, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun xy _ => ?_)
    show (Fin.append xy.1.1 xy.2.1, h xy.1.2 * h xy.2.2) = (Fin.append xy.1.1 xy.2.1, h (xy.1.2 * xy.2.2))
    rw [map_mul]
  | _, _, Apply q₁ q₂, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q₁ (fun hm => hsub (Or.inl hm)) d γ]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.bind_map, Multiset.map_bind]
    refine Multiset.bind_congr (fun p _ => ?_)
    show (q₂.sem (d.mapAnn h) (Fin.append p.1 γ)).map _ = _
    rw [sem_mapAnn h q₂ (fun hm => hsub (Or.inr hm)) d _]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun y _ => ?_)
    show (Fin.append p.1 y.1, h p.2 * h y.2) = (Fin.append p.1 y.1, h (p.2 * y.2))
    rw [map_mul]
  | _, _, Sum q₁ q₂, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q₁ (fun hm => hsub (Or.inl hm)) d γ,
      sem_mapAnn h q₂ (fun hm => hsub (Or.inr hm)) d γ]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.map_add]
  | _, _, Dedup q, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q hsub d γ, AnnotatedRelation.map_fst_mapAnn]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun u _ => ?_)
    show (u, ((q.sem d γ).mapAnn h).annSum u) = (u, h ((q.sem d γ).annSum u))
    rw [AnnotatedRelation.annSum_mapAnn]
  | _, _, Diff q₁ q₂, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q₁ (fun _ => hsub trivial) d γ,
      sem_mapAnn h q₂ (fun _ => hsub trivial) d γ]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    show (p.1, h p.2 - ((q₂.sem d γ).mapAnn h).annSum p.1)
      = (p.1, h (p.2 - (q₂.sem d γ).annSum p.1))
    rw [AnnotatedRelation.annSum_mapAnn, hsub trivial]
  | _, _, Semijoin cnt hc φ q₁ q₂, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q₁ (fun hm => hsub (Or.inl hm)) d γ]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    show (p.1, h p.2 * (matchesAnn φ q₂.sem (d.mapAnn h) γ p.1).annTotal)
      = (p.1, h (p.2 * (matchesAnn φ q₂.sem d γ p.1).annTotal))
    unfold matchesAnn
    rw [sem_mapAnn h q₂ (fun hm => hsub (Or.inr hm)) d _,
      AnnotatedRelation.filter_mapAnn h _ (fun v => φ.holdsPlain v (Fin.append p.1 γ)),
      AnnotatedRelation.annTotal_mapAnn, map_mul]
  | _, _, Antijoin cnt hc φ q₁ q₂, hsub, d, γ => by
    simp only [sem]
    rw [sem_mapAnn h q₁ (fun _ => hsub trivial) d γ]
    unfold AnnotatedRelation.mapAnn
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    show (p.1, h p.2 * (1 - (matchesAnn φ q₂.sem (d.mapAnn h) γ p.1).annTotal))
      = (p.1, h (p.2 * (1 - (matchesAnn φ q₂.sem d γ p.1).annTotal)))
    unfold matchesAnn
    rw [sem_mapAnn h q₂ (fun _ => hsub trivial) d _,
      AnnotatedRelation.filter_mapAnn h _ (fun v => φ.holdsPlain v (Fin.append p.1 γ)),
      AnnotatedRelation.annTotal_mapAnn, map_mul, hsub trivial, map_one]

/-! ## Over `𝔹`: the support -/

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- `find` commutes with taking the support. -/
theorem _root_.AnnotatedDatabase.find_support (n : ℕ) (s : String)
    (d : AnnotatedDatabase T Bool) :
    d.support.find n s = (d.find n s).map AnnotatedRelation.support := by
  induction d with
  | nil =>
    unfold AnnotatedDatabase.support AnnotatedDatabase.find AnnotatedDatabase.find.f
      Database.find Database.find.f
    simp
  | cons hd tl ih =>
    unfold AnnotatedDatabase.support AnnotatedDatabase.find AnnotatedDatabase.find.f
      Database.find Database.find.f
    by_cases hcond : n = hd.snd.fst ∧ s = hd.fst
    · simp [hcond]
      have := hcond.left
      subst this
      rfl
    · simp [hcond]
      unfold AnnotatedDatabase.support AnnotatedDatabase.find Database.find at ih
      exact ih

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- Membership in the support: some copy of the tuple is annotated
true. -/
theorem _root_.AnnotatedRelation.mem_support {n : ℕ} (r : AnnotatedRelation T Bool n)
    (u : Tuple T n) :
    u ∈ r.support ↔ ∃ p ∈ (show Multiset (AnnotatedTuple T Bool n) from r),
      p.1 = u ∧ p.2 = true := by
  unfold AnnotatedRelation.support
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (Multiset.mem_filter.mp hp).1, rfl, (Multiset.mem_filter.mp hp).2⟩
  · rintro ⟨p, hp, rfl, hpt⟩
    exact ⟨p, Multiset.mem_filter.mpr ⟨hp, hpt⟩, rfl⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A sum of Booleans is true exactly when one of them is. -/
private theorem Bool.multiset_sum_eq_true_iff (s : Multiset Bool) :
    s.sum = true ↔ true ∈ s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.sum_cons, Multiset.mem_cons]
    show (b || s.sum) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (hb | hs)
      · exact Or.inl hb.symm
      · exact Or.inr hs
    · rintro (hb | hs)
      · exact Or.inl hb.symm
      · exact Or.inr hs

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- Over `𝔹`, the `⊕`-sum of the annotations of a tuple is true exactly
when the tuple is in the support. -/
theorem _root_.AnnotatedRelation.annSum_eq_true_iff {n : ℕ} (r : AnnotatedRelation T Bool n)
    (u : Tuple T n) : r.annSum u = true ↔ u ∈ r.support := by
  unfold AnnotatedRelation.annSum
  rw [Bool.multiset_sum_eq_true_iff, Multiset.mem_map, AnnotatedRelation.mem_support]
  constructor
  · rintro ⟨p, hp, hpt⟩
    exact ⟨p, (Multiset.mem_filter.mp hp).1, (Multiset.mem_filter.mp hp).2, hpt⟩
  · rintro ⟨p, hp, hpu, hpt⟩
    exact ⟨p, Multiset.mem_filter.mpr ⟨hp, hpu⟩, hpt⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- Over `𝔹`, the `⊕`-sum of all the annotations is true exactly when the
support is non-empty. -/
theorem _root_.AnnotatedRelation.annTotal_eq_true_iff {n : ℕ} (r : AnnotatedRelation T Bool n) :
    r.annTotal = true ↔ ∃ u, u ∈ r.support := by
  unfold AnnotatedRelation.annTotal
  rw [Bool.multiset_sum_eq_true_iff, Multiset.mem_map]
  constructor
  · rintro ⟨p, hp, hpt⟩
    exact ⟨p.1, (AnnotatedRelation.mem_support r p.1).mpr ⟨p, hp, rfl, hpt⟩⟩
  · rintro ⟨u, hu⟩
    obtain ⟨p, hp, -, hpt⟩ := (AnnotatedRelation.mem_support r u).mp hu
    exact ⟨p, hp, hpt⟩

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **Support adequacy over `𝔹`, for the whole fragment**: a tuple is in
the support of the annotated result exactly when it is in the plain
result of the support of the instance. -/
theorem mem_support_sem : ∀ {c n : ℕ} (q : FragQueryIn T c n) (d : AnnotatedDatabase T Bool)
    (γ : Fin c → T) (u : Tuple T n),
    u ∈ (q.sem d γ).support ↔ u ∈ (show Multiset (Tuple T n) from q.semPlain d.support γ)
  | _, n, Rel _ s, d, γ, u => by
    simp only [sem, semPlain, AnnotatedDatabase.find_support]
    cases d.find n s with
    | none =>
      show u ∈ AnnotatedRelation.support (0 : Multiset _) ↔ u ∈ (0 : Multiset (Tuple T n))
      rw [AnnotatedRelation.mem_support]
      simp
    | some r => exact Iff.rfl
  | _, _, Empty, d, γ, u => by
    show u ∈ AnnotatedRelation.support (0 : Multiset _) ↔ u ∈ (0 : Multiset (Tuple T 0))
    rw [AnnotatedRelation.mem_support]
    simp
  | _, _, Unit, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_singleton]
    constructor
    · rintro ⟨p, hp, rfl, -⟩
      rw [Multiset.mem_singleton] at hp
      rw [hp]
    · rintro rfl
      exact ⟨_, Multiset.mem_singleton_self _, rfl, rfl⟩
  | _, _, Proj ts q, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_map]
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hp
      refine ⟨p'.1, (mem_support_sem q d γ p'.1).mp ?_, rfl⟩
      exact (AnnotatedRelation.mem_support _ _).mpr ⟨p', hp', rfl, hpt⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp
        ((mem_support_sem q d γ v).mpr hv)
      exact ⟨_, Multiset.mem_map.mpr ⟨p, hp, rfl⟩, rfl, hpt⟩
  | _, _, Sel φ q, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_filter]
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨hp, hφ⟩ := Multiset.mem_filter.mp hp
      exact ⟨(mem_support_sem q d γ p.1).mp ((AnnotatedRelation.mem_support _ _).mpr
        ⟨p, hp, rfl, hpt⟩), hφ⟩
    · rintro ⟨hu, hφ⟩
      obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp
        ((mem_support_sem q d γ u).mpr hu)
      exact ⟨p, Multiset.mem_filter.mpr ⟨hp, hφ⟩, rfl, hpt⟩
  | _, _, Prod q₁ q₂, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_map]
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Multiset.mem_map.mp hp
      obtain ⟨hx, hy⟩ := Multiset.mem_product.mp hxy
      obtain ⟨hxt, hyt⟩ : x.2 = true ∧ y.2 = true := by
        have hpt' : (x.2 && y.2) = true := hpt
        simpa using hpt'
      refine ⟨(x.1, y.1), Multiset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (mem_support_sem q₁ d γ x.1).mp ((AnnotatedRelation.mem_support _ _).mpr
          ⟨x, hx, rfl, hxt⟩)
      · exact (mem_support_sem q₂ d γ y.1).mp ((AnnotatedRelation.mem_support _ _).mpr
          ⟨y, hy, rfl, hyt⟩)
    · rintro ⟨⟨v, w⟩, hvw, rfl⟩
      obtain ⟨hv, hw⟩ := Multiset.mem_product.mp hvw
      obtain ⟨x, hx, rfl, hxt⟩ := (AnnotatedRelation.mem_support _ _).mp
        ((mem_support_sem q₁ d γ v).mpr hv)
      obtain ⟨y, hy, rfl, hyt⟩ := (AnnotatedRelation.mem_support _ _).mp
        ((mem_support_sem q₂ d γ w).mpr hw)
      refine ⟨_, Multiset.mem_map.mpr ⟨(x, y), Multiset.mem_product.mpr ⟨hx, hy⟩, rfl⟩, rfl, ?_⟩
      show (x.2 && y.2) = true
      rw [hxt, hyt]
      rfl
  | _, _, Apply q₁ q₂, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_bind]
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨x, hx, hp⟩ := Multiset.mem_bind.mp hp
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hp
      obtain ⟨hxt, hyt⟩ : x.2 = true ∧ y.2 = true := by
        have hpt' : (x.2 && y.2) = true := hpt
        simpa using hpt'
      refine ⟨x.1, (mem_support_sem q₁ d γ x.1).mp ((AnnotatedRelation.mem_support _ _).mpr
        ⟨x, hx, rfl, hxt⟩), Multiset.mem_map.mpr ⟨y.1, ?_, rfl⟩⟩
      exact (mem_support_sem q₂ d _ y.1).mp ((AnnotatedRelation.mem_support _ _).mpr
        ⟨y, hy, rfl, hyt⟩)
    · rintro ⟨v, hv, hu⟩
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
      obtain ⟨x, hx, rfl, hxt⟩ := (AnnotatedRelation.mem_support _ _).mp
        ((mem_support_sem q₁ d γ v).mpr hv)
      obtain ⟨y, hy, rfl, hyt⟩ := (AnnotatedRelation.mem_support _ _).mp
        ((mem_support_sem q₂ d _ w).mpr hw)
      refine ⟨_, Multiset.mem_bind.mpr ⟨x, hx, Multiset.mem_map.mpr ⟨y, hy, rfl⟩⟩, rfl, ?_⟩
      show (x.2 && y.2) = true
      rw [hxt, hyt]
      rfl
  | _, _, Sum q₁ q₂, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_add]
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      rcases Multiset.mem_add.mp hp with hp | hp
      · exact Or.inl ((mem_support_sem q₁ d γ p.1).mp
          ((AnnotatedRelation.mem_support _ _).mpr ⟨p, hp, rfl, hpt⟩))
      · exact Or.inr ((mem_support_sem q₂ d γ p.1).mp
          ((AnnotatedRelation.mem_support _ _).mpr ⟨p, hp, rfl, hpt⟩))
    · rintro (hu | hu)
      · obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp
          ((mem_support_sem q₁ d γ u).mpr hu)
        exact ⟨p, Multiset.mem_add.mpr (Or.inl hp), rfl, hpt⟩
      · obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp
          ((mem_support_sem q₂ d γ u).mpr hu)
        exact ⟨p, Multiset.mem_add.mpr (Or.inr hp), rfl, hpt⟩
  | _, _, Dedup q, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_dedup, ← mem_support_sem q d γ u]
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hp
      exact (AnnotatedRelation.annSum_eq_true_iff _ _).mp hpt
    · intro hu
      refine ⟨(u, (q.sem d γ).annSum u), Multiset.mem_map.mpr ⟨u, ?_, rfl⟩, rfl,
        (AnnotatedRelation.annSum_eq_true_iff _ _).mpr hu⟩
      rw [Multiset.mem_dedup, Multiset.mem_map]
      obtain ⟨p, hp, rfl, -⟩ := (AnnotatedRelation.mem_support _ _).mp hu
      exact ⟨p, hp, rfl⟩
  | _, _, Diff q₁ q₂, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_filter, ← mem_support_sem q₁ d γ u,
      ← mem_support_sem q₂ d γ u]
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hp
      have hpt' : (p'.2 && !(q₂.sem d γ).annSum p'.1) = true := hpt
      obtain ⟨h1, h2⟩ : p'.2 = true ∧ (q₂.sem d γ).annSum p'.1 = false := by simpa using hpt'
      refine ⟨(AnnotatedRelation.mem_support _ _).mpr ⟨p', hp', rfl, h1⟩, fun h => ?_⟩
      rw [← AnnotatedRelation.annSum_eq_true_iff] at h
      exact Bool.false_ne_true (h2.symm.trans h)
    · rintro ⟨hu, hne⟩
      obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp hu
      refine ⟨_, Multiset.mem_map.mpr ⟨p, hp, rfl⟩, rfl, ?_⟩
      show (p.2 && !(q₂.sem d γ).annSum p.1) = true
      rw [hpt, Bool.eq_false_iff.mpr
        (fun h => hne ((AnnotatedRelation.annSum_eq_true_iff _ _).mp h))]
      rfl
  | _, _, Semijoin cnt hc φ q₁ q₂, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_filter, ← mem_support_sem q₁ d γ u]
    have hmatch : ∀ v : Tuple T _,
        (matchesAnn φ q₂.sem d γ v).annTotal = true
          ↔ (show Multiset (Tuple T _) from matchesPlain φ q₂.semPlain d.support γ v) ≠ 0 := by
      intro v
      rw [AnnotatedRelation.annTotal_eq_true_iff]
      refine Iff.trans (exists_congr (fun w => ?_))
        ⟨fun ⟨_, hw⟩ h0 => Multiset.notMem_zero _ (h0 ▸ hw), Multiset.exists_mem_of_ne_zero⟩
      unfold matchesAnn matchesPlain
      rw [AnnotatedRelation.mem_support, Multiset.mem_filter]
      constructor
      · rintro ⟨p, hp, rfl, hpt⟩
        obtain ⟨hp, hφ⟩ := Multiset.mem_filter.mp hp
        exact ⟨(mem_support_sem q₂ d _ p.1).mp ((AnnotatedRelation.mem_support _ _).mpr
          ⟨p, hp, rfl, hpt⟩), hφ⟩
      · rintro ⟨hw, hφ⟩
        obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp
          ((mem_support_sem q₂ d _ w).mpr hw)
        exact ⟨p, Multiset.mem_filter.mpr ⟨hp, hφ⟩, rfl, hpt⟩
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hp
      have hpt' : (p'.2 && (matchesAnn φ q₂.sem d γ p'.1).annTotal) = true := hpt
      obtain ⟨h1, h2⟩ : p'.2 = true ∧ (matchesAnn φ q₂.sem d γ p'.1).annTotal = true := by
        simpa using hpt'
      exact ⟨(AnnotatedRelation.mem_support _ _).mpr ⟨p', hp', rfl, h1⟩, (hmatch _).mp h2⟩
    · rintro ⟨hu, hm⟩
      obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp hu
      refine ⟨_, Multiset.mem_map.mpr ⟨p, hp, rfl⟩, rfl, ?_⟩
      show (p.2 && (matchesAnn φ q₂.sem d γ p.1).annTotal) = true
      rw [hpt, (hmatch _).mpr hm]
      rfl
  | _, _, Antijoin cnt hc φ q₁ q₂, d, γ, u => by
    simp only [sem, semPlain]
    rw [AnnotatedRelation.mem_support, Multiset.mem_filter, ← mem_support_sem q₁ d γ u]
    have hmatch : ∀ v : Tuple T _,
        (matchesAnn φ q₂.sem d γ v).annTotal = true
          ↔ (show Multiset (Tuple T _) from matchesPlain φ q₂.semPlain d.support γ v) ≠ 0 := by
      intro v
      rw [AnnotatedRelation.annTotal_eq_true_iff]
      refine Iff.trans (exists_congr (fun w => ?_))
        ⟨fun ⟨_, hw⟩ h0 => Multiset.notMem_zero _ (h0 ▸ hw), Multiset.exists_mem_of_ne_zero⟩
      unfold matchesAnn matchesPlain
      rw [AnnotatedRelation.mem_support, Multiset.mem_filter]
      constructor
      · rintro ⟨p, hp, rfl, hpt⟩
        obtain ⟨hp, hφ⟩ := Multiset.mem_filter.mp hp
        exact ⟨(mem_support_sem q₂ d _ p.1).mp ((AnnotatedRelation.mem_support _ _).mpr
          ⟨p, hp, rfl, hpt⟩), hφ⟩
      · rintro ⟨hw, hφ⟩
        obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp
          ((mem_support_sem q₂ d _ w).mpr hw)
        exact ⟨p, Multiset.mem_filter.mpr ⟨hp, hφ⟩, rfl, hpt⟩
    constructor
    · rintro ⟨p, hp, rfl, hpt⟩
      obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hp
      have hpt' : (p'.2 && !(matchesAnn φ q₂.sem d γ p'.1).annTotal) = true := hpt
      rw [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hpt'
      refine ⟨(AnnotatedRelation.mem_support _ _).mpr ⟨p', hp', rfl, hpt'.1⟩, ?_⟩
      by_contra hne
      exact absurd ((hmatch _).mpr hne) (by rw [hpt'.2]; exact Bool.false_ne_true)
    · rintro ⟨hu, hm⟩
      obtain ⟨p, hp, rfl, hpt⟩ := (AnnotatedRelation.mem_support _ _).mp hu
      refine ⟨_, Multiset.mem_map.mpr ⟨p, hp, rfl⟩, rfl, ?_⟩
      show (p.2 && !(matchesAnn φ q₂.sem d γ p.1).annTotal) = true
      rw [hpt, Bool.eq_false_iff.mpr (fun h => (hmatch _).mp h hm)]
      rfl

/-! ## Over `ℕ`: annotations as multiplicities -/

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **An `ℕ`-annotated relation, unfolded**: each copy of a tuple is
repeated as many times as its annotation says. -/
def _root_.AnnotatedRelation.unfold {n : ℕ} (r : AnnotatedRelation T ℕ n) : Relation T n :=
  Multiset.bind r (fun p : AnnotatedTuple T ℕ n => Multiset.replicate p.2 p.1)

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- An `ℕ`-annotated database, unfolded relation by relation. -/
def _root_.AnnotatedDatabase.unfold (d : AnnotatedDatabase T ℕ) : Database T :=
  d.map (fun e => (e.fst, ⟨e.snd.fst, e.snd.snd.unfold⟩))

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- `find` commutes with unfolding. -/
theorem _root_.AnnotatedDatabase.find_unfold (n : ℕ) (s : String) (d : AnnotatedDatabase T ℕ) :
    d.unfold.find n s = (d.find n s).map AnnotatedRelation.unfold := by
  induction d with
  | nil =>
    unfold AnnotatedDatabase.unfold AnnotatedDatabase.find AnnotatedDatabase.find.f
      Database.find Database.find.f
    simp
  | cons hd tl ih =>
    unfold AnnotatedDatabase.unfold AnnotatedDatabase.find AnnotatedDatabase.find.f
      Database.find Database.find.f
    by_cases hcond : n = hd.snd.fst ∧ s = hd.fst
    · simp [hcond]
      have := hcond.left
      subst this
      rfl
    · simp [hcond]
      unfold AnnotatedDatabase.unfold AnnotatedDatabase.find Database.find at ih
      exact ih

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- Binding over `n` copies of an element is `n` times binding over the
element. -/
private theorem Multiset.replicate_bind {α β : Type} (n : ℕ) (a : α) (g : α → Multiset β) :
    (Multiset.replicate n a).bind g = n • g a := by
  induction n with
  | zero => rw [Multiset.replicate_zero, Multiset.zero_bind, zero_nsmul]
  | succ n ih => rw [Multiset.replicate_succ, Multiset.cons_bind, ih, succ_nsmul, add_comm]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- Filtering `n` copies of an element keeps all or none of them. -/
private theorem Multiset.filter_replicate' {α : Type} (p : α → Prop) [DecidablePred p] (n : ℕ)
    (a : α) : (Multiset.replicate n a).filter p = if p a then Multiset.replicate n a else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.filter_cons, ih]
    by_cases h : p a
    · simp only [h, ite_true]
      rw [Multiset.singleton_add]
    · simp only [h, ite_false, zero_add]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- Binding something or nothing, according to a predicate, is binding
over the elements that satisfy it. -/
private theorem Multiset.bind_ite_zero {α β : Type} (s : Multiset α) (p : α → Prop)
    [DecidablePred p] (g : α → Multiset β) :
    (s.bind (fun x => if p x then g x else 0)) = (s.filter p).bind g := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.zero_bind, Multiset.filter_zero, Multiset.zero_bind]
  | cons a s ih =>
    rw [Multiset.cons_bind, ih, Multiset.filter_cons, Multiset.add_bind]
    by_cases h : p a
    · simp only [h, ite_true, Multiset.singleton_bind]
    · simp only [h, ite_false, Multiset.zero_bind]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- `m ⬝ n` copies are `m` times `n` copies. -/
private theorem Multiset.replicate_mul' {α : Type} (m n : ℕ) (a : α) :
    Multiset.replicate (m * n) a = m • Multiset.replicate n a := by
  induction m with
  | zero => rw [Nat.zero_mul, Multiset.replicate_zero, zero_nsmul]
  | succ m ih => rw [Nat.succ_mul, Multiset.replicate_add, ih, succ_nsmul]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A multiple passes out of a bind. -/
private theorem Multiset.bind_nsmul' {α β : Type} (s : Multiset α) (m : ℕ) (g : α → Multiset β) :
    (s.bind (fun x => m • g x)) = m • s.bind g := by
  induction m with
  | zero => simp only [zero_nsmul, Multiset.bind_zero]
  | succ m ih => simp only [succ_nsmul, Multiset.bind_add, ih]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A sum of values guarded by a predicate is the sum over the elements
that satisfy it. -/
private theorem Multiset.sum_map_ite_zero {α : Type} (s : Multiset α) (p : α → Prop)
    [DecidablePred p] (f : α → ℕ) :
    (s.map (fun x => if p x then f x else 0)).sum = ((s.filter p).map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.filter_cons, Multiset.map_add,
      Multiset.sum_add]
    by_cases h : p a
    · simp only [h, ite_true, Multiset.map_singleton, Multiset.sum_singleton]
    · simp only [h, ite_false, Multiset.map_zero, Multiset.sum_zero, zero_add]

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **The multiplicity of a tuple in the unfolding is the `⊕`-sum of its
annotations.** -/
theorem _root_.AnnotatedRelation.count_unfold {n : ℕ} (r : AnnotatedRelation T ℕ n)
    (u : Tuple T n) : Multiset.count u r.unfold = r.annSum u := by
  unfold AnnotatedRelation.unfold AnnotatedRelation.annSum
  rw [Multiset.count_bind]
  simp only [Multiset.count_replicate]
  exact Multiset.sum_map_ite_zero _ _ _

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **Adequacy in `ℕ` with multiplicities, on `F₀`**: the plain semantics
of the unfolded instance is the unfolded annotated semantics. A product
multiplies multiplicities, a union adds them, and the other operators of
`F₀` carry them along. -/
theorem semPlain_unfold : ∀ {c n : ℕ} (q : FragQueryIn T c n), q.level0 →
    ∀ (d : AnnotatedDatabase T ℕ) (γ : Fin c → T),
      q.semPlain d.unfold γ = (q.sem d γ).unfold
  | _, n, Rel _ s, _, d, γ => by
    simp only [sem, semPlain, AnnotatedDatabase.find_unfold]
    cases d.find n s with
    | none =>
      show (0 : Multiset (Tuple T n)) = AnnotatedRelation.unfold (0 : Multiset _)
      unfold AnnotatedRelation.unfold
      rw [Multiset.zero_bind]
    | some r => rfl
  | _, _, Empty, _, d, γ => by
    show (0 : Multiset (Tuple T 0)) = AnnotatedRelation.unfold (0 : Multiset _)
    unfold AnnotatedRelation.unfold
    rw [Multiset.zero_bind]
  | _, _, Unit, _, d, γ => by
    simp only [sem, semPlain]
    unfold AnnotatedRelation.unfold
    rw [Multiset.singleton_bind, Multiset.replicate_one]
  | _, _, Proj ts q, hq, d, γ => by
    simp only [sem, semPlain]
    rw [semPlain_unfold q hq d γ]
    unfold AnnotatedRelation.unfold
    rw [Multiset.map_bind, Multiset.bind_map]
    refine Multiset.bind_congr (fun p _ => ?_)
    rw [Multiset.map_replicate]
  | _, _, Sel φ q, hq, d, γ => by
    simp only [sem, semPlain]
    rw [semPlain_unfold q hq d γ]
    unfold AnnotatedRelation.unfold
    rw [Multiset.filter_bind, ← Multiset.bind_ite_zero]
    refine Multiset.bind_congr (fun p _ => ?_)
    rw [Multiset.filter_replicate']
  | _, _, Prod q₁ q₂, hq, d, γ => by
    simp only [sem, semPlain]
    rw [semPlain_unfold q₁ hq.1 d γ, semPlain_unfold q₂ hq.2 d γ]
    unfold AnnotatedRelation.unfold Multiset.product
    simp only [Multiset.map_bind, Multiset.bind_assoc, Multiset.bind_map, Multiset.map_map,
      Multiset.map_replicate, Multiset.replicate_bind]
    refine Multiset.bind_congr (fun x _ => ?_)
    simp only [Multiset.map_nsmul, Multiset.map_bind, Multiset.map_replicate]
    rw [← Multiset.bind_nsmul']
    refine Multiset.bind_congr (fun y _ => ?_)
    rw [← Multiset.replicate_mul']
    rfl
  | _, _, Apply q₁ q₂, hq, d, γ => by
    simp only [sem, semPlain]
    rw [semPlain_unfold q₁ hq.1 d γ]
    unfold AnnotatedRelation.unfold
    simp only [Multiset.bind_assoc, Multiset.bind_map, Multiset.replicate_bind]
    refine Multiset.bind_congr (fun x _ => ?_)
    rw [semPlain_unfold q₂ hq.2 d _]
    unfold AnnotatedRelation.unfold
    simp only [Multiset.map_bind, Multiset.map_replicate]
    rw [← Multiset.bind_nsmul']
    refine Multiset.bind_congr (fun y _ => ?_)
    rw [← Multiset.replicate_mul']
  | _, _, Sum q₁ q₂, hq, d, γ => by
    simp only [sem, semPlain]
    rw [semPlain_unfold q₁ hq.1 d γ, semPlain_unfold q₂ hq.2 d γ]
    unfold AnnotatedRelation.unfold
    rw [Multiset.add_bind]
  | _, _, Dedup _, hq, _, _ => hq.elim
  | _, _, Diff _ _, hq, _, _ => hq.elim
  | _, _, Semijoin _ _ _ _ _, hq, _, _ => hq.elim
  | _, _, Antijoin _ _ _ _ _, hq, _, _ => hq.elim

end FragQueryIn

end
