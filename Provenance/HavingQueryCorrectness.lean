/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.QueryToAgg
import Provenance.QueryAnnotatedDatabaseHom

/-!
# Query-level correctness of the fused HAVING operator vs the JOIN rewriting

This file proves the query-level correspondence between the possible-world
semantics of the fused `HAVING COUNT(*)` operator and its `JOIN`-based
rewriting, in absorptive commutative m-semirings in which `⊗` distributes
over `⊖`.

* **`C = 1`** (`AggQuery.havingSite_count_ge_one`): the fused
  `COUNT(*) ≥ 1` operator agrees – key by key, annotation by annotation –
  with the duplicate-eliminated key projection `ε(Π_{keys}(q))`, via the
  extensional characterization `groupByKey_eq_dedup_map` of duplicate
  elimination, `Having.havingGroup_coe`, and
  `Having.havingProv_count_ge_one`.

* **General `C`** (`Query.joinChain_count_correct`): the `C`-fold
  self-join chain `ε(Π_{#0}(joinChain q C))` gives every group key the
  `⊕`-sum `S_{C+1}` of the monomials of its `(C+1)`-element worlds, which
  is the fused `COUNT(*) ≥ C + 1` predicate provenance. The tie-broken
  comparison `<*` of the rewriting is materialized by an *occurrence
  identifier* column: the base query has columns (key, value, identifier)
  and the chain condition compares (value, identifier) pairs
  lexicographically, so any injective assignment of identifiers within
  each group – the sole hypothesis – realizes an arbitrary resolution of
  ties between equal values; duplicate values are fully supported. The
  statement is per key: a group with fewer than `C + 1` occurrences has
  provenance `𝟘` on both sides (the fused operator annotates its row with
  `𝟘`, the join query has no row for it).

The proof of the general case runs through three layers: the pure chain
algebra (`chainAgg`, summing to the elementary symmetric sum `esymm` of
the group's annotations over any strictly increasing enumeration), the
per-key evaluation invariant of the join chain
(`joinChain_eval_filter`), and the collapse of the fused semantics
(`Having.havingProv_count_ge` with `S_eq_esymm`).

* **`=`/`≤` comparisons** (`Query.joinChainDiff_count_eq_correct`,
  `Query.joinChainDiff_count_le_correct`): the remaining comparison
  operators are differences of two `≥` chains (`Q₂^{=C} = Q₂^{≥C} −
  Q₂^{≥C+1}` and `Q₂^{≤C} = Q₂^{≥1} − Q₂^{≥C+1}`), assembled through the
  `Diff` semantics: since a duplicate-eliminated relation has one row per
  key, per-key annotation sums commute with `Diff` (`diff_perKeySum`),
  and the group-level content is `Having.G_eq_S_monus_S` and
  `Having.atMost_eq_S_monus_S`.
-/

variable {T : Type} [ValueType T]

section GroupByKey

variable {K : Type} [SemiringWithMonus K] [DecidableEq K]

/-- **Extensional characterization of duplicate elimination.**
`groupByKey` produces exactly one row per distinct key of the input,
whose annotation is the `⊕`-sum of the annotations of the matching
rows. -/
theorem groupByKey_eq_dedup_map {n : ℕ} (r : AnnotatedRelation T K n) :
    (Multiset.ofList (groupByKey r).val : Multiset (AnnotatedTuple T K n))
      = (Multiset.dedup (Multiset.map Prod.fst r)).map
          (fun u => (u, (Multiset.map Prod.snd
            (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u) r)).sum)) := by
  have hL : (Multiset.ofList (groupByKey r).val
      : Multiset (AnnotatedTuple T K n)).Nodup := by
    rw [Multiset.coe_nodup]
    exact KeyValueList.nodup _ (groupByKey r).property
  have hR : ((Multiset.dedup (Multiset.map Prod.fst r)).map
      (fun u => ((u, (Multiset.map Prod.snd
        (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u) r)).sum)
        : AnnotatedTuple T K n))).Nodup := by
    refine Multiset.Nodup.map_on ?_ (Multiset.nodup_dedup _)
    intro u _ v _ h
    exact congrArg Prod.fst h
  rw [Multiset.Nodup.ext hL hR]
  intro a
  constructor
  · intro ha
    have ha' : a ∈ (groupByKey r).val := Multiset.mem_coe.mp ha
    have hkey : a.fst ∈ Multiset.map Prod.fst r :=
      (groupByKey_key_iff r a.fst).mp ⟨a.snd, ha'⟩
    have hval := groupByKey_value r a.fst a.snd ha'
    rw [Multiset.mem_map]
    exact ⟨a.fst, Multiset.mem_dedup.mpr hkey, by rw [← hval]; rfl⟩
  · intro ha
    rw [Multiset.mem_map] at ha
    obtain ⟨u, hu, hau⟩ := ha
    have hkey : u ∈ Multiset.map Prod.fst r := Multiset.mem_dedup.mp hu
    obtain ⟨w, hw⟩ := (groupByKey_key_iff r u).mpr hkey
    have hval := groupByKey_value r u w hw
    rw [← hau, ← hval]
    exact Multiset.mem_coe.mpr hw

end GroupByKey

section CountGeOne

open Having

variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]

/-- **Query-level correctness for `COUNT(*) ≥ 1`.** In an absorptive
commutative m-semiring in which `⊗` distributes over `⊖`, the fused
`HAVING COUNT(*) ≥ 1` site – with its output rows projected to the group
key – computes exactly the duplicate-eliminated key projection
`ε(Π_{keys}(q))` of the inner query, which is the `C = 1` join-based
query: one row per non-empty group, annotated by the `⊕`-sum of the
group's annotations. Stated against any general subquery whose annotated
evaluation is the classical inner query's. -/
theorem AggQuery.havingSite_count_ge_one
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    {m n₁ : ℕ} (is : Tuple (Fin m) n₁) (ts : Tuple (Term ℕ m) 1)
    (q : Query ℕ m) (hq : q.source) (d : AnnotatedDatabase ℕ K) :
    ((AggQuery.havingSite is ts ![SeqAggFunc.count] CompOp.ge 0
        (Term.const 1) (q.toAgg hq)).evaluateAnnotated d).map
      (fun p => ((fun k : Fin n₁ => p.fst (Fin.castAdd 1 k)), p.snd))
      = (ε (Π (fun k : Fin n₁ => Term.index (is k)) q)).evaluateAnnotated hq d := by
  rw [AggQuery.havingSite_evaluateAnnotated,
    Query.toAggHaving_input q hq d]
  set r : AnnotatedRelation ℕ K m := q.evaluateAnnotated hq d with hr
  -- The right-hand side: `ε ∘ Π` unfolds to `groupByKey` of the projected
  -- relation, which `groupByKey_eq_dedup_map` characterizes extensionally.
  have hRHS : (ε (Π (fun k : Fin n₁ => Term.index (is k)) q)).evaluateAnnotated hq d
      = Multiset.ofList (groupByKey
          (Multiset.map (fun p : AnnotatedTuple ℕ K m =>
            ((fun k : Fin n₁ => p.fst (is k)), p.snd)) r)).val := rfl
  rw [hRHS, groupByKey_eq_dedup_map]
  -- The left-hand side is now the closed form; fuse the two maps.
  rw [Multiset.map_map]
  -- The two key multisets are definitionally equal after fusing the maps;
  -- `Multiset.map_congr` takes the index equality and reduces the goal to
  -- the pointwise equality of the two row constructors.
  refine Multiset.map_congr ?_ fun g _ => ?_
  · rw [Multiset.map_map]
    rfl
  · refine Prod.ext ?_ ?_
    · -- The key part: extracting the first `n₁` columns of the fused row
      -- recovers the group key.
      funext k
      show Fin.append g (fun k => (![SeqAggFunc.count] k)
          ((havingGroup is r g).map (fun p => ((ts k).eval p.fst))))
          (Fin.castAdd 1 k)
        = g k
      exact Fin.append_left g _ k
    · -- The annotation part: the fused `COUNT(*) ≥ 1` provenance is the
      -- `⊕`-sum of the group's annotations (`havingProv_count_ge_one`),
      -- which is the annotation `ε` computes for the key `g`.
      refine Eq.trans (havingProv_count_ge_one h_abs h_distrib
        (havingGroup is r g) (ts 0)) ?_
      have h1 : ((havingGroup is r g).map (fun p => p.snd)).sum
          = (Multiset.map Prod.snd
              (Multiset.filter
                (fun p : AnnotatedTuple ℕ K m =>
                  ∀ k' : Fin n₁, p.fst (is k') = g k') r)).sum := by
        rw [← havingGroup_coe is r g, Multiset.map_coe, Multiset.sum_coe]
      rw [h1]
      congr 1
      rw [Multiset.filter_map, Multiset.map_map]
      refine Multiset.map_congr ?_ fun p _ => rfl
      refine Multiset.filter_congr fun p _ => ?_
      constructor
      · intro h
        funext k'
        exact h k'
      · intro h k'
        exact congrFun h k'

end CountGeOne

/-! ## The chain algebra of the `C`-fold self-join

The semantic content of the join chain: the annotated strictly increasing
chains over a multiset of (value, annotation) pairs, and their `⊕`-sum,
which is the elementary symmetric sum of the annotations – the multiset
form of the join-side provenance `Having.S`. -/

section ChainAlgebra

namespace Having

variable {V : Type} [LinearOrder V]
variable {K : Type} [CommSemiringWithMonus K]

/-- The elementary symmetric sum of a multiset of annotations: the
`⊕`-sum, over the `C`-element sub-multisets, of their `⊗`-products. This
is the position-free form of the join-side provenance `Having.S`
(`S_eq_esymm`). -/
def esymm (s : Multiset K) (C : ℕ) : K :=
  ((Multiset.powersetCard C s).map Multiset.prod).sum

@[simp] theorem esymm_zero (s : Multiset K) : esymm s 0 = 1 := by
  rw [esymm, Multiset.powersetCard_zero_left]
  simp

theorem esymm_cons (a : K) (s : Multiset K) (C : ℕ) :
    esymm (a ::ₘ s) (C + 1) = esymm s (C + 1) + a * esymm s C := by
  rw [esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add]
  congr 1
  rw [Multiset.map_map,
    show ((Multiset.prod ∘ Multiset.cons a) : Multiset K → K)
      = fun m => a * m.prod from funext fun m => Multiset.prod_cons a m,
    esymm]
  exact Multiset.sum_map_mul_left

/-- `Having.S` over a full position space is the elementary symmetric sum
of the annotation multiset: the join-side provenance only depends on the
multiset of the annotations, not on the position space carrying them. -/
theorem S_eq_esymm {ι : Type} [DecidableEq ι] [Fintype ι] (α : ι → K) (C : ℕ) :
    S α Finset.univ C = esymm (Multiset.map α Finset.univ.val) C := by
  unfold S esymm
  rw [Finset.sum_eq_multiset_sum, Multiset.powersetCard_map, Multiset.map_map,
    ← Finset.map_val_val_powersetCard, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun W _ => ?_)
  exact Finset.prod_eq_multiset_prod W α

/-- The annotated strictly increasing chains of length `C + 1` over a
multiset `G` of (value, annotation) pairs, each chain represented by its
last value and the `⊗`-product of its annotations. This is the semantic
content of the `C`-fold self-join chain of the join-based rewriting. -/
def chainAgg (G : Multiset (V × K)) : ℕ → Multiset (V × K)
  | 0 => G
  | C + 1 =>
      ((chainAgg G C ×ˢ G).filter (fun x => x.1.1 < x.2.1)).map
        (fun x => (x.2.1, x.1.2 * x.2.2))

theorem chainAgg_zero : ∀ C : ℕ, chainAgg (0 : Multiset (V × K)) C = 0
  | 0 => rfl
  | C + 1 => by
    rw [chainAgg, Multiset.product_zero, Multiset.filter_zero, Multiset.map_zero]

/-- The last value of a chain is one of the input values. -/
theorem chainAgg_fst_mem (G : Multiset (V × K)) :
    ∀ (C : ℕ), ∀ x ∈ chainAgg G C, x.1 ∈ G.map Prod.fst
  | 0, x, hx => Multiset.mem_map_of_mem _ hx
  | C + 1, x, hx => by
    rw [chainAgg] at hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    show y.2.1 ∈ G.map Prod.fst
    exact Multiset.mem_map_of_mem _
      (Multiset.mem_product.mp (Multiset.mem_filter.mp hy).1).2

theorem product_singleton_right {α β : Type} (s : Multiset α) (b : β) :
    s ×ˢ ({b} : Multiset β) = s.map (fun a => (a, b)) := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.zero_product, Multiset.map_zero]
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.add_product, Multiset.product_singleton, ih,
      Multiset.map_add, Multiset.map_singleton]

/-- Appending an occurrence whose value dominates every value of `G`: the
chains over `G + {u}` are the chains over `G` together with the chains
ending at `u` (a `u`-free chain extended by `u`, or `u` alone). -/
theorem chainAgg_add_of_max (G : Multiset (V × K)) (u : V × K)
    (hmax : ∀ v ∈ G.map Prod.fst, v < u.1) :
    ∀ C : ℕ, chainAgg (G + {u}) C
      = chainAgg G C
        + (match C with
           | 0 => ({u} : Multiset (V × K))
           | C' + 1 => (chainAgg G C').map (fun x => (u.1, x.2 * u.2)))
  | 0 => rfl
  | C + 1 => by
    have htail_fst : ∀ t : V × K, t ∈ ((match C with
        | 0 => ({u} : Multiset (V × K))
        | C' + 1 => (chainAgg G C').map
            (fun x : V × K => (u.1, x.2 * u.2))) : Multiset (V × K)) → t.1 = u.1 := by
      cases C with
      | zero =>
        intro t ht
        have ht' : t ∈ ({u} : Multiset (V × K)) := ht
        rw [Multiset.mem_singleton.mp ht']
      | succ C' =>
        intro t ht
        obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp ht
        rfl
    rw [chainAgg, chainAgg_add_of_max G u hmax C, Multiset.add_product,
      Multiset.product_add, Multiset.product_add, Multiset.filter_add,
      Multiset.filter_add, Multiset.filter_add, Multiset.map_add,
      Multiset.map_add, Multiset.map_add]
    have hA_u : ((chainAgg G C ×ˢ ({u} : Multiset (V × K))).filter
          (fun x => x.1.1 < x.2.1)).map (fun x => (x.2.1, x.1.2 * x.2.2))
        = (chainAgg G C).map (fun x => (u.1, x.2 * u.2)) := by
      have hall : Multiset.filter
          ((fun x : (V × K) × V × K => x.1.1 < x.2.1) ∘ fun a => (a, u))
          (chainAgg G C) = chainAgg G C :=
        Multiset.filter_eq_self.mpr fun x hx =>
          hmax x.1 (chainAgg_fst_mem G C x hx)
      rw [product_singleton_right, Multiset.filter_map, hall, Multiset.map_map]
      rfl
    have hBG : ((match C with
          | 0 => ({u} : Multiset (V × K))
          | C' + 1 => (chainAgg G C').map (fun x => (u.1, x.2 * u.2))) ×ˢ G).filter
          (fun x => x.1.1 < x.2.1) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx
      obtain ⟨h1, h2⟩ := Multiset.mem_product.mp hx
      rw [htail_fst x.1 h1]
      exact fun h => absurd (hmax x.2.1 (Multiset.mem_map_of_mem _ h2))
        (lt_asymm h)
    have hB_u : ((match C with
          | 0 => ({u} : Multiset (V × K))
          | C' + 1 => (chainAgg G C').map (fun x => (u.1, x.2 * u.2)))
            ×ˢ ({u} : Multiset (V × K))).filter (fun x => x.1.1 < x.2.1) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx
      obtain ⟨h1, h2⟩ := Multiset.mem_product.mp hx
      rw [htail_fst x.1 h1, Multiset.mem_singleton.mp h2]
      exact lt_irrefl u.1
    rw [hA_u, hBG, hB_u, Multiset.map_zero, add_zero, add_zero]
    rfl

/-- **The chain sum is the elementary symmetric sum.** Over a list of
(value, annotation) pairs with strictly increasing values, the `⊕`-sum of
the annotations of the strictly increasing chains of length `C + 1` is
the elementary symmetric sum of degree `C + 1` of the annotations. -/
theorem chainAgg_sum_of_sorted :
    ∀ (U : List (V × K)), U.Pairwise (fun p q => p.1 < q.1) → ∀ (C : ℕ),
    ((chainAgg (↑U : Multiset (V × K)) C).map Prod.snd).sum
      = esymm (↑(U.map Prod.snd) : Multiset K) (C + 1) := by
  intro U
  induction U using List.reverseRecOn with
  | nil =>
    intro _ C
    show ((chainAgg (0 : Multiset (V × K)) C).map Prod.snd).sum = esymm 0 (C + 1)
    rw [chainAgg_zero, Multiset.map_zero, Multiset.sum_zero, esymm,
      show Multiset.powersetCard (C + 1) (0 : Multiset K) = 0 from rfl,
      Multiset.map_zero, Multiset.sum_zero]
  | append_singleton U₀ u ih =>
    intro hU C
    obtain ⟨hU₀, -, hmax'⟩ := List.pairwise_append.mp hU
    have hmax : ∀ v ∈ (↑U₀ : Multiset (V × K)).map Prod.fst, v < u.1 := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hv
      exact hmax' p (Multiset.mem_coe.mp hp) u (List.mem_singleton_self u)
    have hcoe : (↑(U₀ ++ [u]) : Multiset (V × K)) = ↑U₀ + {u} :=
      (Multiset.coe_add U₀ [u]).symm
    have hsnd : (↑((U₀ ++ [u]).map Prod.snd) : Multiset K)
        = u.2 ::ₘ ↑(U₀.map Prod.snd) := by
      rw [List.map_append, ← Multiset.coe_add]
      show (↑(U₀.map Prod.snd) : Multiset K) + {u.2} = _
      rw [add_comm, Multiset.singleton_add]
    rw [hcoe, hsnd, chainAgg_add_of_max ↑U₀ u hmax C, Multiset.map_add,
      Multiset.sum_add, esymm_cons]
    cases C with
    | zero =>
      show ((chainAgg (↑U₀ : Multiset (V × K)) 0).map Prod.snd).sum
          + (({u} : Multiset (V × K)).map Prod.snd).sum
        = esymm (↑(U₀.map Prod.snd) : Multiset K) 1
          + u.2 * esymm (↑(U₀.map Prod.snd) : Multiset K) 0
      rw [ih hU₀ 0, Multiset.map_singleton, Multiset.sum_singleton, esymm_zero,
        mul_one]
    | succ C' =>
      show ((chainAgg (↑U₀ : Multiset (V × K)) (C' + 1)).map Prod.snd).sum
          + (((chainAgg (↑U₀ : Multiset (V × K)) C').map
              (fun x => (u.1, x.2 * u.2))).map Prod.snd).sum
        = esymm (↑(U₀.map Prod.snd) : Multiset K) (C' + 1 + 1)
          + u.2 * esymm (↑(U₀.map Prod.snd) : Multiset K) (C' + 1)
      rw [ih hU₀ (C' + 1), Multiset.map_map,
        show ((Prod.snd ∘ fun x : V × K => (u.1, x.2 * u.2)) : V × K → K)
          = fun x => x.2 * u.2 from rfl,
        Multiset.sum_map_mul_right, ih hU₀ C', mul_comm]

/-- Left coordinate of an appended tuple. -/
theorem append_coord_left {m n : ℕ} (x : Tuple ℕ m) (y : Tuple ℕ n)
    (i : ℕ) (h : i < m) (h' : i < m + n) :
    Fin.append x y ⟨i, h'⟩ = x ⟨i, h⟩ := by
  rw [show (⟨i, h'⟩ : Fin (m + n)) = Fin.castAdd n ⟨i, h⟩ from rfl, Fin.append_left]

/-- Right coordinate of an appended tuple, at offset `m + i`. -/
theorem append_coord_right {m n : ℕ} (x : Tuple ℕ m) (y : Tuple ℕ n)
    (i : ℕ) (h : i < n) (h' : m + i < m + n) :
    Fin.append x y ⟨m + i, h'⟩ = y ⟨i, h⟩ := by
  rw [show (⟨m + i, h'⟩ : Fin (m + n)) = Fin.natAdd m ⟨i, h⟩ from rfl, Fin.append_right]

/-- Right coordinate of an appended tuple, at offset `m`. -/
theorem append_coord_right₀ {m n : ℕ} (x : Tuple ℕ m) (y : Tuple ℕ n)
    (h : 0 < n) (h' : m < m + n) :
    Fin.append x y ⟨m, h'⟩ = y ⟨0, h⟩ := by
  rw [show (⟨m, h'⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, h⟩ from rfl, Fin.append_right]

theorem singleton_product {α β : Type} (a : α) (t : Multiset β) :
    ({a} : Multiset α) ×ˢ t = t.map (fun b => (a, b)) := by
  induction t using Multiset.induction_on with
  | empty => rw [Multiset.product_zero, Multiset.map_zero]
  | cons b t ih =>
    rw [← Multiset.singleton_add, Multiset.product_add, Multiset.product_singleton,
      ih, Multiset.map_add, Multiset.map_singleton]

theorem product_map_map {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (s : Multiset α) (t : Multiset β) :
    (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.zero_product, Multiset.zero_product,
      Multiset.map_zero]
  | cons a s ih =>
    rw [Multiset.map_cons, ← Multiset.singleton_add, ← Multiset.singleton_add a,
      Multiset.add_product, Multiset.add_product, singleton_product,
      singleton_product, ih, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl

theorem filter_product {α β : Type} (p : α → Prop) [DecidablePred p]
    (q : β → Prop) [DecidablePred q] (s : Multiset α) (t : Multiset β) :
    (s.filter p) ×ˢ (t.filter q)
      = (s ×ˢ t).filter (fun z => p z.1 ∧ q z.2) := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.filter_zero, Multiset.zero_product, Multiset.zero_product,
      Multiset.filter_zero]
  | cons a s ih =>
    rw [Multiset.filter_cons, ← Multiset.singleton_add a, Multiset.add_product,
      Multiset.add_product, Multiset.filter_add, ← ih, singleton_product,
      Multiset.filter_map]
    congr 1
    by_cases hpa : p a
    · rw [if_pos hpa, singleton_product]
      congr 1
      refine Multiset.filter_congr fun b _ => ?_
      show q b ↔ p a ∧ q b
      exact ⟨fun h => ⟨hpa, h⟩, fun h => h.2⟩
    · rw [if_neg hpa, Multiset.zero_product, eq_comm, Multiset.map_eq_zero]
      exact Multiset.filter_eq_nil.mpr fun b _ h => hpa h.1

end Having

end ChainAlgebra

/-! ## The join chain query and its per-key evaluation

The `C`-fold self-join chain of the join-based rewriting, over an arity-3
base query whose columns are (group key, compared value, occurrence
identifier). The identifier column materializes the tie-broken comparison
`<*`: the chain condition compares (value, identifier) pairs
lexicographically, so any injective assignment of identifiers within each
group realizes an arbitrary resolution of ties between equal values –
duplicate values (and duplicate whole occurrences) are fully supported. -/

section JoinChain

open Having

variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]

/-- The chain condition relating a new copy of the base query to the last
copy of the chain: equal group keys and lexicographically larger
(value, identifier) pair – the tie-broken comparison `<*`. -/
def chainCond (C : ℕ) : Selection ℕ (3 * (C + 1) + 3) :=
  Selection.And
    (Selection.BT (BoolTerm.EQ
      (Term.index ⟨0, by omega⟩) (Term.index ⟨3 * C + 3, by omega⟩)))
    (Selection.Or
      (Selection.BT (BoolTerm.LT
        (Term.index ⟨3 * C + 1, by omega⟩)
        (Term.index ⟨3 * C + 3 + 1, by omega⟩)))
      (Selection.And
        (Selection.BT (BoolTerm.EQ
          (Term.index ⟨3 * C + 1, by omega⟩)
          (Term.index ⟨3 * C + 3 + 1, by omega⟩)))
        (Selection.BT (BoolTerm.LT
          (Term.index ⟨3 * C + 2, by omega⟩)
          (Term.index ⟨3 * C + 3 + 2, by omega⟩)))))

/-- The `C`-fold self-join chain: `C + 1` copies of the base query, with
consecutive copies related by `chainCond`. Copy `j` occupies columns
`3j, 3j + 1, 3j + 2`. -/
def joinChain (q : Query ℕ 3) : (C : ℕ) → Query ℕ (3 * C + 3)
  | 0 => q
  | C + 1 =>
    σ (chainCond C)
      (@Query.Prod ℕ (3 * C + 3) 3 (3 * (C + 1) + 3) rfl (joinChain q C) q)

theorem joinChain_source (q : Query ℕ 3) (hq : q.source) :
    ∀ C : ℕ, (joinChain q C).source
  | 0 => hq
  | C + 1 => ⟨joinChain_source q hq C, hq⟩

/-- The combining map of one chain step: append the new copy's tuple and
multiply the annotations. -/
def chainCombine (C : ℕ) :
    (Tuple ℕ (3 * C + 3) × K) × (Tuple ℕ 3 × K)
      → Tuple ℕ (3 * (C + 1) + 3) × K :=
  fun z => (Fin.append z.1.1 z.2.1, z.1.2 * z.2.2)

/-- The (value, identifier) pairs of the group of key `a`, with their
annotations: the chain-algebra view of one group of the base relation. -/
def groupPairs (r : Multiset (Tuple ℕ 3 × K)) (a : ℕ) :
    Multiset ((ℕ ×ₗ ℕ) × K) :=
  (r.filter (fun p => p.1 ⟨0, by omega⟩ = a)).map
    (fun p => (toLex (p.1 ⟨1, by omega⟩, p.1 ⟨2, by omega⟩), p.2))

/-- **Per-key evaluation of the join chain.** Within the group of key `a`,
the rows of the `C`-fold chain, viewed through their last (value,
identifier) pair and their annotation, are exactly the annotated strictly
increasing chains of length `C + 1` of the group. -/
theorem joinChain_eval_filter (q : Query ℕ 3) (hq : q.source)
    (d : AnnotatedDatabase ℕ K) (a : ℕ) :
    ∀ C : ℕ,
    (Multiset.filter (fun p => p.1 ⟨0, by omega⟩ = a)
        ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)).map
      (fun p => (toLex (p.1 ⟨3 * C + 1, by omega⟩, p.1 ⟨3 * C + 2, by omega⟩),
        p.2))
      = chainAgg (groupPairs (q.evaluateAnnotated hq d) a) C
  | 0 => rfl
  | C + 1 => by
    have ih := joinChain_eval_filter q hq d a C
    have hstep : (joinChain q (C + 1)).evaluateAnnotated
          (joinChain_source q hq (C + 1)) d
        = @Multiset.filter _
            (fun ta : AnnotatedTuple ℕ K (3 * (C + 1) + 3) =>
              (chainCond C).eval ta.fst)
            ((chainCond C).evalDecidableAnnotated)
            (Multiset.map (chainCombine C)
              (Multiset.product
                ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)
                (q.evaluateAnnotated hq d))) := rfl
    have hGP : groupPairs (q.evaluateAnnotated hq d) a
        = Multiset.map (fun p : Tuple ℕ 3 × K =>
            (toLex (p.1 ⟨1, by omega⟩, p.1 ⟨2, by omega⟩), p.2))
            (Multiset.filter (fun p : Tuple ℕ 3 × K => p.1 ⟨0, by omega⟩ = a)
              (q.evaluateAnnotated hq d)) := rfl
    rw [hstep, Multiset.filter_filter, Multiset.filter_map, Multiset.map_map,
      chainAgg, ← ih, hGP, Having.product_map_map, Multiset.filter_map,
      Multiset.map_map, filter_product, Multiset.filter_filter]
    refine Multiset.map_congr (Multiset.filter_congr fun z _ => ?_) fun z _ => ?_
    · -- The chain predicate, transported through `chainCombine`.
      show ((Fin.append z.1.1 z.2.1 ⟨0, by omega⟩ = a)
            ∧ ((Fin.append z.1.1 z.2.1 ⟨0, by omega⟩
                  = Fin.append z.1.1 z.2.1 ⟨3 * C + 3, by omega⟩)
              ∧ ((Fin.append z.1.1 z.2.1 ⟨3 * C + 1, by omega⟩
                    < Fin.append z.1.1 z.2.1 ⟨3 * C + 3 + 1, by omega⟩)
                ∨ ((Fin.append z.1.1 z.2.1 ⟨3 * C + 1, by omega⟩
                      = Fin.append z.1.1 z.2.1 ⟨3 * C + 3 + 1, by omega⟩)
                  ∧ (Fin.append z.1.1 z.2.1 ⟨3 * C + 2, by omega⟩
                      < Fin.append z.1.1 z.2.1 ⟨3 * C + 3 + 2, by omega⟩)))))
        ↔ ((toLex (z.1.1 ⟨3 * C + 1, by omega⟩, z.1.1 ⟨3 * C + 2, by omega⟩)
              < toLex (z.2.1 ⟨1, by omega⟩, z.2.1 ⟨2, by omega⟩))
            ∧ ((z.1.1 ⟨0, by omega⟩ = a) ∧ (z.2.1 ⟨0, by omega⟩ = a)))
      rw [append_coord_left z.1.1 z.2.1 0 (by omega) (by omega),
        append_coord_left z.1.1 z.2.1 (3 * C + 1) (by omega) (by omega),
        append_coord_left z.1.1 z.2.1 (3 * C + 2) (by omega) (by omega),
        append_coord_right₀ z.1.1 z.2.1 (by omega) (by omega),
        append_coord_right z.1.1 z.2.1 1 (by omega) (by omega),
        append_coord_right z.1.1 z.2.1 2 (by omega) (by omega),
        Prod.Lex.lt_iff]
      constructor
      · rintro ⟨hka, hkeq, hlt⟩
        exact ⟨hlt, hka, hkeq ▸ hka⟩
      · rintro ⟨hlt, hka, hkya⟩
        exact ⟨hka, hka.trans hkya.symm, hlt⟩
    · -- The row image, transported through `chainCombine`.
      show (toLex (Fin.append z.1.1 z.2.1 ⟨3 * C + 3 + 1, by omega⟩,
              Fin.append z.1.1 z.2.1 ⟨3 * C + 3 + 2, by omega⟩),
            z.1.2 * z.2.2)
          = (toLex (z.2.1 ⟨1, by omega⟩, z.2.1 ⟨2, by omega⟩), z.1.2 * z.2.2)
      rw [append_coord_right z.1.1 z.2.1 1 (by omega) (by omega),
        append_coord_right z.1.1 z.2.1 2 (by omega) (by omega)]

end JoinChain

/-! ## Assembly: the join-based query computes the fused HAVING provenance -/

section Assembly

open Having

variable {K : Type} [CommSemiringWithMonus K] [DecidableEq K]

/-- Mapping to the annotation ignores a rebuilt data part. -/
theorem map_snd_map_pair {α β γ : Type} (f : α × β → γ) (s : Multiset (α × β)) :
    Multiset.map Prod.snd (s.map (fun p => (f p, p.snd))) = s.map Prod.snd := by
  rw [Multiset.map_map]
  rfl

/-- Per-key sums over a keyed rebuild of the distinct keys. -/
theorem perKeySum_dedup_map {α β : Type} [DecidableEq α] [AddCommMonoid β]
    (s : Multiset α) (F : α → β) (u : α) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
        ((Multiset.dedup s).map (fun v => (v, F v))))).sum
      = if u ∈ s then F u else 0 := by
  rw [Multiset.filter_map,
    show Multiset.filter ((fun p : α × β => p.fst = u) ∘ fun v => (v, F v))
        (Multiset.dedup s)
      = Multiset.filter (fun v => v = u) (Multiset.dedup s) from
      Multiset.filter_congr fun v _ => Iff.rfl,
    Multiset.filter_eq', Multiset.count_dedup]
  by_cases hu : u ∈ s
  · rw [if_pos hu, if_pos hu, show Multiset.replicate 1 u = {u} from rfl,
      Multiset.map_singleton, Multiset.map_singleton, Multiset.sum_singleton]
  · rw [if_neg hu, if_neg hu, show Multiset.replicate 0 u = 0 from rfl,
      Multiset.map_zero, Multiset.map_zero, Multiset.sum_zero]

/-- Per-key annotation sums are invariant under duplicate elimination. -/
theorem perKeySum_groupByKey {T : Type} [ValueType T] {n : ℕ}
    (r : AnnotatedRelation T K n) (u : Tuple T n) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
        (Multiset.ofList (groupByKey r).val))).sum
      = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u) r)).sum := by
  rw [groupByKey_eq_dedup_map, perKeySum_dedup_map]
  by_cases hu : u ∈ Multiset.map Prod.fst r
  · rw [if_pos hu]
    rfl
  · rw [if_neg hu,
      show Multiset.filter (fun p : Tuple T n × K => p.fst = u) r = 0 from
        Multiset.filter_eq_nil.mpr fun p hp hpu =>
          hu (hpu ▸ Multiset.mem_map_of_mem Prod.fst hp),
      Multiset.map_zero, Multiset.sum_zero]

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- Under global row-distinctness, the group sequence is strictly
increasing on its tuple part. -/
theorem havingGroup_pairwise_fst_lt {T : Type} [ValueType T] [HasAltLinearOrder K]
    {m n₁ : ℕ} (is : Tuple (Fin m) n₁) (r : AnnotatedRelation T K m)
    (g : Tuple T n₁) (hnodup : (r.map Prod.fst).Nodup) :
    (havingGroup is r g).Pairwise (fun p q => p.fst < q.fst) := by
  have hcoe_nodup : (↑((havingGroup is r g).map Prod.fst)
      : Multiset (Tuple T m)).Nodup := by
    rw [← Multiset.map_coe, havingGroup_coe]
    exact Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _)) hnodup
  have hne : (havingGroup is r g).Pairwise (fun p q => p.fst ≠ q.fst) :=
    List.pairwise_map.mp (Multiset.coe_nodup.mp hcoe_nodup)
  refine List.Pairwise.imp (fun hab => ?_)
    (List.Pairwise.and (havingGroup_pairwise is r g) hne)
  obtain ⟨hor, hnefst⟩ := hab
  rcases hor with h | heq
  · exact h
  · exact absurd heq hnefst

/-- A strict tuple inequality between arity-3 tuples with equal first
column is a strict lexicographic inequality on the (second, third)
column pairs. -/
theorem tuple3_lt_pairLt {p q : Tuple ℕ 3} (h0 : p ⟨0, by omega⟩ = q ⟨0, by omega⟩)
    (h : p < q) :
    toLex (p ⟨1, by omega⟩, p ⟨2, by omega⟩)
      < toLex (q ⟨1, by omega⟩, q ⟨2, by omega⟩) := by
  obtain ⟨i, hpre, hlt⟩ := h
  rw [Prod.Lex.lt_iff]
  rcases i with ⟨iv, hiv⟩
  have hiv3 : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
  rcases hiv3 with rfl | rfl | rfl
  · rw [show p ⟨0, hiv⟩ = q ⟨0, hiv⟩ from h0] at hlt
    exact absurd hlt (lt_irrefl _)
  · exact Or.inl hlt
  · exact Or.inr ⟨hpre ⟨1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega)), hlt⟩

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- The chain-algebra view of a group is the (value, identifier) image of
the group sequence. -/
theorem groupPairs_eq_havingGroup [HasAltLinearOrder K]
    (r : AnnotatedRelation ℕ K 3) (g : Tuple ℕ 1) :
    groupPairs r (g 0)
      = ↑((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3)) r g).map
          (fun p => (toLex (p.fst ⟨1, by omega⟩, p.fst ⟨2, by omega⟩), p.snd))) := by
  rw [← Multiset.map_coe, havingGroup_coe]
  unfold groupPairs
  refine Multiset.map_congr (Multiset.filter_congr fun p _ => ?_) fun p _ => rfl
  constructor
  · intro h k'
    rw [Fin.eq_zero k']
    exact h
  · intro h
    exact h 0

theorem piChain_source (q : Query ℕ 3) (hq : q.source) (C : ℕ) :
    ((Π (fun _ : Fin 1 => Term.index ⟨0, by omega⟩) (joinChain q C))).source := by
  exact joinChain_source q hq C

theorem q2_source (q : Query ℕ 3) (hq : q.source) (C : ℕ) :
    (ε (Π (fun _ : Fin 1 => Term.index ⟨0, by omega⟩) (joinChain q C))).source := by
  exact joinChain_source q hq C

/-- **Query-level correctness of the join-based rewriting, general `C`.**
In an absorptive commutative m-semiring in which `⊗` distributes over
`⊖`, for every group key `g`, the `⊕`-sum of the annotations that the
join-based query `ε(Π_{#0}(joinChain q C))` gives to `g` equals the
fused `HAVING COUNT(*) ≥ C + 1` predicate provenance of the group of `g`.
The hypothesis `hnodup` states that the occurrence identifiers of the
base query's third column make its rows pairwise distinct: it is the
formal counterpart of fixing an arbitrary tie-break `<*` between
occurrences with equal compared values, and is satisfiable for every
instance (annotate each occurrence with a distinct identifier).
The statement is per-key: a group with fewer than `C + 1` occurrences
has provenance `𝟘` on both sides – the fused operator gives its row a
`𝟘` annotation while the join query simply has no row for it. -/
theorem Query.joinChain_count_correct [HasAltLinearOrder K]
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts : Tuple (Term ℕ 3) 1) (C : ℕ) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((ε (Π (fun _ : Fin 1 => Term.index ⟨0, by omega⟩)
          (joinChain q C))).evaluateAnnotated (q2_source q hq C) d))).sum
      = havingProv
          (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g)
          (ts 0) SeqAggFunc.count CompOp.ge (C + 1) := by
  -- Abbreviations (all definitional).
  have hiff : ∀ p : AnnotatedTuple ℕ K (3 * C + 3),
      ((fun p : AnnotatedTuple ℕ K 1 => p.fst = g)
        ∘ fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
          ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩), p.snd)) p
      ↔ p.fst ⟨0, by omega⟩ = g 0 := by
    intro p
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext k'
      rw [Fin.eq_zero k']
      exact h
  have hpw : ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
      (q.evaluateAnnotated hq d) g).map
      (fun p => (toLex (p.fst ⟨1, by omega⟩, p.fst ⟨2, by omega⟩), p.snd))).Pairwise
      (fun x y => x.1 < y.1) := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {p} {q'} hp hq' hlt => ?_)
      (havingGroup_pairwise_fst_lt _ (q.evaluateAnnotated hq d) g hnodup)
    have hmemp := Multiset.mem_coe.mpr hp
    rw [havingGroup_coe] at hmemp
    have hmemq := Multiset.mem_coe.mpr hq'
    rw [havingGroup_coe] at hmemq
    have h0p := (Multiset.mem_filter.mp hmemp).2 0
    have h0q := (Multiset.mem_filter.mp hmemq).2 0
    exact tuple3_lt_pairLt (h0p.trans h0q.symm) hlt
  have hlist : Multiset.map (fun i => ((havingGroup
        (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
        (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ.val
      = (↑((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
          (q.evaluateAnnotated hq d) g).map Prod.snd) : Multiset K) := by
    rw [Fin.univ_val_map]
    congr 1
    conv_rhs => rw [← List.ofFn_get (havingGroup
      (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3)) (q.evaluateAnnotated hq d) g),
      List.map_ofFn]
    rfl
  calc (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((ε (Π (fun _ : Fin 1 => Term.index ⟨0, by omega⟩)
          (joinChain q C))).evaluateAnnotated (q2_source q hq C) d))).sum
      = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
          (Multiset.ofList (groupByKey
            ((Π (fun _ : Fin 1 => Term.index ⟨0, by omega⟩)
              (joinChain q C)).evaluateAnnotated (piChain_source q hq C) d)).val))).sum
        := rfl
    _ = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
          ((Π (fun _ : Fin 1 => Term.index ⟨0, by omega⟩)
            (joinChain q C)).evaluateAnnotated (piChain_source q hq C) d))).sum
        := perKeySum_groupByKey _ g
    _ = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
          (Multiset.map (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
              ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩), p.snd))
            ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)))).sum
        := rfl
    _ = (Multiset.map Prod.snd (Multiset.map (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
            ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩), p.snd))
          (Multiset.filter ((fun p : AnnotatedTuple ℕ K 1 => p.fst = g)
              ∘ fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
                ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩), p.snd))
            ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)))).sum
        := by rw [Multiset.filter_map]; rfl
    _ = (Multiset.map Prod.snd
          (Multiset.filter ((fun p : AnnotatedTuple ℕ K 1 => p.fst = g)
              ∘ fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
                ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩), p.snd))
            ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d))).sum
        := congrArg (fun m : Multiset K => m.sum)
            (map_snd_map_pair
              (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
                (fun _ : Fin 1 => p.fst ⟨0, by omega⟩))
              (Multiset.filter ((fun p : AnnotatedTuple ℕ K 1 => p.fst = g)
                  ∘ fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
                    ((fun _ : Fin 1 => p.fst ⟨0, by omega⟩), p.snd))
                ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)))
    _ = (Multiset.map Prod.snd
          (Multiset.filter (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
              p.fst ⟨0, by omega⟩ = g 0)
            ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d))).sum
        := congrArg (fun m => (Multiset.map Prod.snd m).sum)
            (Multiset.filter_congr fun p _ => hiff p)
    _ = (Multiset.map Prod.snd
          (Multiset.map (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
              (toLex (p.fst ⟨3 * C + 1, by omega⟩, p.fst ⟨3 * C + 2, by omega⟩),
                p.snd))
            (Multiset.filter (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
              p.fst ⟨0, by omega⟩ = g 0)
              ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)))).sum
        := (congrArg (fun m : Multiset K => m.sum)
            (map_snd_map_pair
              (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
                toLex (p.fst ⟨3 * C + 1, by omega⟩, p.fst ⟨3 * C + 2, by omega⟩))
              (Multiset.filter (fun p : AnnotatedTuple ℕ K (3 * C + 3) =>
                  p.fst ⟨0, by omega⟩ = g 0)
                ((joinChain q C).evaluateAnnotated (joinChain_source q hq C) d)))).symm
    _ = (Multiset.map Prod.snd
          (chainAgg (groupPairs (q.evaluateAnnotated hq d) (g 0)) C)).sum
        := congrArg (fun m => (Multiset.map Prod.snd m).sum)
            (joinChain_eval_filter q hq d (g 0) C)
    _ = (Multiset.map Prod.snd (chainAgg
          (↑((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).map
            (fun p => (toLex (p.fst ⟨1, by omega⟩, p.fst ⟨2, by omega⟩), p.snd))))
          C)).sum
        := by rw [groupPairs_eq_havingGroup (q.evaluateAnnotated hq d) g]
    _ = esymm (↑(((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g).map
          (fun p => (toLex (p.fst ⟨1, by omega⟩, p.fst ⟨2, by omega⟩), p.snd))).map
          Prod.snd) : Multiset K) (C + 1)
        := chainAgg_sum_of_sorted _ hpw C
    _ = esymm (↑((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
          (q.evaluateAnnotated hq d) g).map Prod.snd) : Multiset K) (C + 1)
        := by rw [List.map_map]; rfl
    _ = havingProv
          (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g)
          (ts 0) SeqAggFunc.count CompOp.ge (C + 1)
        := by
          rw [havingProv_count_ge h_abs h_distrib _ (ts 0) C, S_eq_esymm, hlist]


/-- One row per distinct key, at the multiset level: filtering a keyed
rebuild of the distinct keys by a key. -/
theorem filter_fst_dedup_map {α β : Type} [DecidableEq α]
    (s : Multiset α) (F : α → β) (u : α) :
    Multiset.filter (fun p => p.fst = u)
        ((Multiset.dedup s).map (fun v => (v, F v)))
      = if u ∈ s then ({(u, F u)} : Multiset (α × β)) else 0 := by
  rw [Multiset.filter_map,
    show Multiset.filter ((fun p : α × β => p.fst = u) ∘ fun v => (v, F v))
        (Multiset.dedup s)
      = Multiset.filter (fun v => v = u) (Multiset.dedup s) from
      Multiset.filter_congr fun v _ => Iff.rfl,
    Multiset.filter_eq', Multiset.count_dedup]
  by_cases hu : u ∈ s
  · rw [if_pos hu, if_pos hu, show Multiset.replicate 1 u = {u} from rfl,
      Multiset.map_singleton]
  · rw [if_neg hu, if_neg hu, show Multiset.replicate 0 u = 0 from rfl,
      Multiset.map_zero]

/-- Per-key sums through a key-preserving rebuild of the annotations. -/
theorem perKeySum_map_pair {α β γ : Type} [DecidableEq α] [AddCommMonoid γ]
    (G : α × β → γ) (s : Multiset (α × β)) (u : α) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
        (s.map (fun p => (p.fst, G p))))).sum
      = (Multiset.map G (Multiset.filter (fun p => p.fst = u) s)).sum := by
  rw [Multiset.filter_map]
  refine congrArg Multiset.sum ?_
  rw [Multiset.map_map]
  exact Multiset.map_congr (Multiset.filter_congr fun p _ => Iff.rfl)
    fun p _ => rfl

/-- **Per-key sums through `Diff`.** When the left argument of a
difference is duplicate-eliminated (one row per key), the per-key
annotation sum of the difference is the monus of the two per-key sums. -/
theorem diff_perKeySum {T : Type} [ValueType T] {n : ℕ}
    (q₁ q₂ : Query T n) (h₁ : q₁.source) (h₂ : q₂.source)
    (hd : (Query.Diff (ε q₁) q₂).source)
    (d : AnnotatedDatabase T K) (u : Tuple T n) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
        ((Query.Diff (ε q₁) q₂).evaluateAnnotated hd d))).sum
      = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
          ((ε q₁).evaluateAnnotated h₁ d))).sum
        - (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
            (q₂.evaluateAnnotated h₂ d))).sum := by
  refine Eq.trans (perKeySum_map_pair
    (fun p : Tuple T n × K => p.snd - ((((groupByKey
      (q₂.evaluateAnnotated h₂ d)).val.find? (·.1 = p.fst)).map
        Prod.snd).getD 0))
    ((ε q₁).evaluateAnnotated h₁ d) u) ?_
  refine Eq.trans (congrArg Multiset.sum
    (Multiset.map_congr
      (g := fun p : Tuple T n × K => p.snd - ((((groupByKey
        (q₂.evaluateAnnotated h₂ d)).val.find? (·.1 = u)).map
          Prod.snd).getD 0))
      rfl fun p hp => congrArg
        (fun v => p.snd - ((((groupByKey
          (q₂.evaluateAnnotated h₂ d)).val.find? (·.1 = v)).map
            Prod.snd).getD 0))
        (Multiset.mem_filter.mp hp).2)) ?_
  have hA : Multiset.filter (fun p => p.fst = u) ((ε q₁).evaluateAnnotated h₁ d)
      = if u ∈ Multiset.map Prod.fst (q₁.evaluateAnnotated h₁ d)
        then ({(u, (Multiset.map Prod.snd
          (Multiset.filter (fun p : AnnotatedTuple T K n => p.1 = u)
            (q₁.evaluateAnnotated h₁ d))).sum)} : Multiset (AnnotatedTuple T K n))
        else 0 :=
    Eq.trans
      (congrArg (Multiset.filter (fun p => p.fst = u))
        (groupByKey_eq_dedup_map (q₁.evaluateAnnotated h₁ d)))
      (filter_fst_dedup_map _ _ u)
  refine Eq.trans (congrArg (fun m : Multiset (Tuple T n × K) =>
    (Multiset.map (fun p : Tuple T n × K => p.snd - ((((groupByKey
      (q₂.evaluateAnnotated h₂ d)).val.find? (·.1 = u)).map
        Prod.snd).getD 0)) m).sum) hA) ?_
  by_cases hu : u ∈ Multiset.map Prod.fst (q₁.evaluateAnnotated h₁ d)
  · rw [if_pos hu, Multiset.map_singleton, Multiset.sum_singleton]
    exact congrArg₂ (fun a b : K => a - b)
      (perKeySum_groupByKey (q₁.evaluateAnnotated h₁ d) u).symm
      (groupByKey_find_eq_filter_sum (q₂.evaluateAnnotated h₂ d) u)
  · rw [if_neg hu, Multiset.map_zero, Multiset.sum_zero]
    have hnil : Multiset.filter (fun p : AnnotatedTuple T K n => p.fst = u)
        (q₁.evaluateAnnotated h₁ d) = 0 :=
      Multiset.filter_eq_nil.mpr fun p hp hpu =>
        hu (hpu ▸ Multiset.mem_map_of_mem Prod.fst hp)
    have hF0 : (Multiset.map Prod.snd (Multiset.filter
        (fun p : AnnotatedTuple T K n => p.fst = u)
        (q₁.evaluateAnnotated h₁ d))).sum = (0 : K) := by
      rw [hnil, Multiset.map_zero, Multiset.sum_zero]
    exact ((congrArg (fun a : K => a - (Multiset.map Prod.snd
        (Multiset.filter (fun p => p.fst = u)
          (q₂.evaluateAnnotated h₂ d))).sum)
        ((perKeySum_groupByKey (q₁.evaluateAnnotated h₁ d) u).trans hF0)).trans
      (zero_monus _)).symm

/-- The join-based query for `COUNT(*) ≥ C + 1`: project the `C`-fold
chain to its group key and eliminate duplicates. -/
def joinChainQuery (q : Query ℕ 3) (C : ℕ) : Query ℕ 1 :=
  ε (Π (fun _ : Fin 1 => Term.index ⟨0, by omega⟩) (joinChain q C))

/-- **Query-level correctness for `COUNT(*) = C + 1`.** The join-based
query `Q₂^{≥C+1} − Q₂^{≥C+2}` gives every group key the fused
`COUNT(*) = C + 1` predicate provenance. -/
theorem Query.joinChainDiff_count_eq_correct [HasAltLinearOrder K]
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts : Tuple (Term ℕ 3) 1) (C : ℕ) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((Query.Diff (joinChainQuery q C) (joinChainQuery q (C + 1))).evaluateAnnotated
          (by exact ⟨joinChain_source q hq C, joinChain_source q hq (C + 1)⟩) d))).sum
      = havingProv
          (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g)
          (ts 0) SeqAggFunc.count CompOp.eq (C + 1) := by
  have h₁ : (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((Query.Diff (joinChainQuery q C) (joinChainQuery q (C + 1))).evaluateAnnotated
          (by exact ⟨joinChain_source q hq C, joinChain_source q hq (C + 1)⟩) d))).sum
      = ((Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            ((joinChainQuery q C).evaluateAnnotated (q2_source q hq C) d))).sum
          - (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
              ((joinChainQuery q (C + 1)).evaluateAnnotated
                (q2_source q hq (C + 1)) d))).sum : K) :=
    diff_perKeySum _ _ (piChain_source q hq C) (q2_source q hq (C + 1)) _ d g
  have h₂ : ((Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            ((joinChainQuery q C).evaluateAnnotated (q2_source q hq C) d))).sum
          - (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
              ((joinChainQuery q (C + 1)).evaluateAnnotated
                (q2_source q hq (C + 1)) d))).sum : K)
      = (havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (C + 1)
          - havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (C + 1 + 1) : K) :=
    congrArg₂ (fun a b : K => a - b)
      (Query.joinChain_count_correct h_abs h_distrib q hq d hnodup ts C g)
      (Query.joinChain_count_correct h_abs h_distrib q hq d hnodup ts (C + 1) g)
  have h₃ : (havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (C + 1)
          - havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (C + 1 + 1) : K)
      = (S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1)
          - S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1 + 1) : K) :=
    congrArg₂ (fun a b : K => a - b)
      (havingProv_count_ge h_abs h_distrib
        (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
          (q.evaluateAnnotated hq d) g) (ts 0) C)
      (havingProv_count_ge h_abs h_distrib
        (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
          (q.evaluateAnnotated hq d) g) (ts 0) (C + 1))
  have h₄ : (S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1)
          - S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1 + 1) : K)
      = G (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1) :=
    (G_eq_S_monus_S h_abs h_distrib _ Finset.univ (C + 1)).symm
  have h₅ : G (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1)
      = havingProv
          (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g)
          (ts 0) SeqAggFunc.count CompOp.eq (C + 1) :=
    (havingProv_count_eq h_distrib
      (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
        (q.evaluateAnnotated hq d) g) (ts 0) C).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- **Query-level correctness for `COUNT(*) ≤ C`.** The join-based query
`Q₂^{≥1} − Q₂^{≥C+1}` gives every group key the fused `COUNT(*) ≤ C`
predicate provenance. -/
theorem Query.joinChainDiff_count_le_correct [HasAltLinearOrder K]
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts : Tuple (Term ℕ 3) 1) (C : ℕ) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((Query.Diff (joinChainQuery q 0) (joinChainQuery q C)).evaluateAnnotated
          (by exact ⟨joinChain_source q hq 0, joinChain_source q hq C⟩) d))).sum
      = havingProv
          (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g)
          (ts 0) SeqAggFunc.count CompOp.le C := by
  have h₁ : (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((Query.Diff (joinChainQuery q 0) (joinChainQuery q C)).evaluateAnnotated
          (by exact ⟨joinChain_source q hq 0, joinChain_source q hq C⟩) d))).sum
      = ((Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            ((joinChainQuery q 0).evaluateAnnotated (q2_source q hq 0) d))).sum
          - (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
              ((joinChainQuery q C).evaluateAnnotated (q2_source q hq C) d))).sum : K) :=
    diff_perKeySum _ _ (piChain_source q hq 0) (q2_source q hq C) _ d g
  have h₂ : ((Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
            ((joinChainQuery q 0).evaluateAnnotated (q2_source q hq 0) d))).sum
          - (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
              ((joinChainQuery q C).evaluateAnnotated (q2_source q hq C) d))).sum : K)
      = (havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (0 + 1)
          - havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (C + 1) : K) :=
    congrArg₂ (fun a b : K => a - b)
      (Query.joinChain_count_correct h_abs h_distrib q hq d hnodup ts 0 g)
      (Query.joinChain_count_correct h_abs h_distrib q hq d hnodup ts C g)
  have h₃ : (havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (0 + 1)
          - havingProv
            (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g)
            (ts 0) SeqAggFunc.count CompOp.ge (C + 1) : K)
      = (S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (0 + 1)
          - S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1) : K) :=
    congrArg₂ (fun a b : K => a - b)
      (havingProv_count_ge h_abs h_distrib
        (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
          (q.evaluateAnnotated hq d) g) (ts 0) 0)
      (havingProv_count_ge h_abs h_distrib
        (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
          (q.evaluateAnnotated hq d) g) (ts 0) C)
  have h₄ : (S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (0 + 1)
          - S (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
              (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ (C + 1) : K)
      = ∑ W ∈ Finset.univ.powerset.filter
          (fun W : Finset (Fin (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g).length) => 1 ≤ W.card ∧ W.card ≤ C),
          Having.T (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ W :=
    (atMost_eq_S_monus_S h_abs h_distrib _ Finset.univ C).symm
  have h₅ : (∑ W ∈ Finset.univ.powerset.filter
          (fun W : Finset (Fin (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g).length) => 1 ≤ W.card ∧ W.card ≤ C),
          Having.T (fun i => ((havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g).get i).snd) Finset.univ W)
      = havingProv
          (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g)
          (ts 0) SeqAggFunc.count CompOp.le C :=
    (havingProv_count_le h_distrib
      (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
        (q.evaluateAnnotated hq d) g) (ts 0) C).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))


/-- The join-based query realizing `COUNT(*) op (C + 1)`, for each
comparison operator `op`: chains for `≥` and `>`, differences of two
chains for `≤`, `<` and `=`, and the union of the `<`- and `>`-queries
for `≠`. -/
def Query.joinCountQuery (q : Query ℕ 3) : CompOp → ℕ → Query ℕ 1
  | .lt, C => Query.Diff (joinChainQuery q 0) (joinChainQuery q C)
  | .le, C => Query.Diff (joinChainQuery q 0) (joinChainQuery q (C + 1))
  | .eq, C => Query.Diff (joinChainQuery q C) (joinChainQuery q (C + 1))
  | .ne, C => Query.Sum
      (Query.Diff (joinChainQuery q 0) (joinChainQuery q C))
      (joinChainQuery q (C + 1))
  | .ge, C => joinChainQuery q C
  | .gt, C => joinChainQuery q (C + 1)

theorem Query.joinCountQuery_source (q : Query ℕ 3) (hq : q.source) :
    ∀ (op : CompOp) (C : ℕ), (Query.joinCountQuery q op C).source
  | .lt, C => by exact ⟨joinChain_source q hq 0, joinChain_source q hq C⟩
  | .le, C => by exact ⟨joinChain_source q hq 0, joinChain_source q hq (C + 1)⟩
  | .eq, C => by exact ⟨joinChain_source q hq C, joinChain_source q hq (C + 1)⟩
  | .ne, C => by exact ⟨⟨joinChain_source q hq 0, joinChain_source q hq C⟩,
      joinChain_source q hq (C + 1)⟩
  | .ge, C => q2_source q hq C
  | .gt, C => q2_source q hq (C + 1)

/-- Per-key annotation sums are additive across `Query.Sum`. -/
theorem sum_perKeySum {T : Type} [ValueType T] {n : ℕ}
    (q₁ q₂ : Query T n) (h₁ : q₁.source) (h₂ : q₂.source)
    (hs : (Query.Sum q₁ q₂).source)
    (d : AnnotatedDatabase T K) (u : Tuple T n) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
        ((Query.Sum q₁ q₂).evaluateAnnotated hs d))).sum
      = (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
          (q₁.evaluateAnnotated h₁ d))).sum
        + (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
            (q₂.evaluateAnnotated h₂ d))).sum := by
  show (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = u)
      (q₁.evaluateAnnotated h₁ d + q₂.evaluateAnnotated h₂ d))).sum = _
  rw [Multiset.filter_add, Multiset.map_add, Multiset.sum_add]

/-- **Query-level correctness of the JOIN rewriting for `COUNT(*)`, for
any comparison operator.** For every `op ∈ {<, ≤, =, ≠, ≥, >}`, every
threshold `C + 1 ≥ 1` and every group key, in an absorptive commutative
m-semiring whose `⊗` distributes over `⊖`, the join-based query
`Query.joinCountQuery q op C` gives the group key the fused
`COUNT(*) op (C + 1)` predicate provenance. -/
theorem Query.joinCount_correct [HasAltLinearOrder K]
    (h_abs : absorptive K) (h_distrib : mul_sub_left_distributive K)
    (q : Query ℕ 3) (hq : q.source) (d : AnnotatedDatabase ℕ K)
    (hnodup : ((q.evaluateAnnotated hq d).map Prod.fst).Nodup)
    (ts : Tuple (Term ℕ 3) 1) (op : CompOp) (C : ℕ) (g : Tuple ℕ 1) :
    (Multiset.map Prod.snd (Multiset.filter (fun p => p.fst = g)
        ((Query.joinCountQuery q op C).evaluateAnnotated
          (Query.joinCountQuery_source q hq op C) d))).sum
      = havingProv
          (havingGroup (fun _ : Fin 1 => (⟨0, by omega⟩ : Fin 3))
            (q.evaluateAnnotated hq d) g)
          (ts 0) SeqAggFunc.count op (C + 1) := by
  cases op with
  | lt =>
    rw [havingProv_count_lt]
    exact Query.joinChainDiff_count_le_correct h_abs h_distrib q hq d hnodup ts C g
  | le =>
    exact Query.joinChainDiff_count_le_correct h_abs h_distrib q hq d hnodup ts
      (C + 1) g
  | eq =>
    exact Query.joinChainDiff_count_eq_correct h_abs h_distrib q hq d hnodup ts C g
  | ne =>
    rw [havingProv_ne_split, havingProv_count_lt, havingProv_count_gt]
    refine Eq.trans (sum_perKeySum
      (Query.Diff (joinChainQuery q 0) (joinChainQuery q C))
      (joinChainQuery q (C + 1))
      (by exact ⟨joinChain_source q hq 0, joinChain_source q hq C⟩)
      (q2_source q hq (C + 1)) _ d g) ?_
    exact congrArg₂ (fun a b : K => a + b)
      (Query.joinChainDiff_count_le_correct h_abs h_distrib q hq d hnodup ts C g)
      (Query.joinChain_count_correct h_abs h_distrib q hq d hnodup ts (C + 1) g)
  | ge =>
    exact Query.joinChain_count_correct h_abs h_distrib q hq d hnodup ts C g
  | gt =>
    rw [havingProv_count_gt]
    exact Query.joinChain_count_correct h_abs h_distrib q hq d hnodup ts (C + 1) g

end Assembly
