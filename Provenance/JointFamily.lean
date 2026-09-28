/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggExpr

/-!
# Two occurrence families as one

What a predicate reading two aggregate values annotates is the `⊕` over
the worlds of the *union* of the two families it reads. The families of
two tokens are indexed separately – `Fin m` and `Fin n` – so the union
has to be built. `Having.catAnn` concatenates the two annotation
functions into one family on `Fin (m + n)`, `Having.leftFam` and
`Having.rightFam` are the two parts inside it, and `Having.catWorld`
pairs a world of each into a world of the concatenation, `leftPart` and
`rightPart` reading them back.

The reindexing lemmas say that reading a part of the concatenation is
reading the family it came from (`relAnn_catWorld_left` and its right
twin), and they need nothing of `K`. From them, a world of the union
carries the product of its two halves' annotations exactly where `K` is
complemented (`worldAnn_catWorld`) – so the split form in which a
two-family reading is usually written is the union reading there, and
need not be elsewhere.
-/

namespace Having

variable {K : Type} [CommSemiringWithMonus K]

/-- The concatenation of two occurrence families: `m + n` occurrences,
the first `m` of the left family and the last `n` of the right. -/
def catAnn {m n : ℕ} (α : Fin m → K) (β : Fin n → K) : Fin (m + n) → K :=
  Fin.append α β

omit [CommSemiringWithMonus K] in
@[simp] theorem catAnn_left {m n : ℕ} (α : Fin m → K) (β : Fin n → K)
    (i : Fin m) : catAnn α β (Fin.castAdd n i) = α i :=
  Fin.append_left α β i

omit [CommSemiringWithMonus K] in
@[simp] theorem catAnn_right {m n : ℕ} (α : Fin m → K) (β : Fin n → K)
    (j : Fin n) : catAnn α β (Fin.natAdd m j) = β j :=
  Fin.append_right α β j

variable (m n : ℕ)

/-- The left family inside the concatenation. -/
def leftFam : Finset (Fin (m + n)) := Finset.univ.map (Fin.castAddEmb n)

/-- The right family inside the concatenation. -/
def rightFam : Finset (Fin (m + n)) := Finset.univ.map (Fin.natAddEmb m)

variable {m n}

@[simp] theorem mem_leftFam_castAdd (i : Fin m) :
    Fin.castAdd n i ∈ leftFam m n :=
  Finset.mem_map_of_mem _ (Finset.mem_univ i)

@[simp] theorem mem_rightFam_natAdd (j : Fin n) :
    Fin.natAdd m j ∈ rightFam m n :=
  Finset.mem_map_of_mem _ (Finset.mem_univ j)

theorem notMem_leftFam_natAdd (j : Fin n) : Fin.natAdd m j ∉ leftFam m n := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_map.mp h
  have hv := congrArg Fin.val hi
  have := i.isLt
  simp [Fin.castAddEmb, Fin.val_natAdd] at hv
  omega

theorem notMem_rightFam_castAdd (i : Fin m) :
    Fin.castAdd n i ∉ rightFam m n := by
  intro h
  obtain ⟨j, -, hj⟩ := Finset.mem_map.mp h
  have hv := congrArg Fin.val hj
  have := i.isLt
  simp [Fin.natAddEmb, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- The two parts exhaust the concatenation. -/
theorem rightFam_eq_compl : rightFam m n = (leftFam m n)ᶜ := by
  ext k
  rw [Finset.mem_compl]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [mem_leftFam_castAdd i, not_true_eq_false, iff_false]
    exact notMem_rightFam_castAdd i
  · simp only [mem_rightFam_natAdd j, true_iff]
    exact notMem_leftFam_natAdd j

/-- A world of each family, as one world of the concatenation. -/
def catWorld {m n : ℕ} (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    Finset (Fin (m + n)) :=
  W₁.map (Fin.castAddEmb n) ∪ W₂.map (Fin.natAddEmb m)

@[simp] theorem mem_catWorld_castAdd (W₁ : Finset (Fin m))
    (W₂ : Finset (Fin n)) (i : Fin m) :
    Fin.castAdd n i ∈ catWorld W₁ W₂ ↔ i ∈ W₁ := by
  rw [catWorld, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨i', hi', he⟩ := Finset.mem_map.mp h
      have hv := congrArg Fin.val he
      simp [Fin.castAddEmb, Fin.val_castAdd] at hv
      exact (Fin.ext hv : i' = i) ▸ hi'
    · exact absurd (Finset.mem_of_subset
        (Finset.map_subset_map.mpr (Finset.subset_univ W₂)) h)
        (notMem_rightFam_castAdd i)
  · exact fun h => Or.inl (Finset.mem_map_of_mem _ h)

@[simp] theorem mem_catWorld_natAdd (W₁ : Finset (Fin m))
    (W₂ : Finset (Fin n)) (j : Fin n) :
    Fin.natAdd m j ∈ catWorld W₁ W₂ ↔ j ∈ W₂ := by
  rw [catWorld, Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact absurd (Finset.mem_of_subset
        (Finset.map_subset_map.mpr (Finset.subset_univ W₁)) h)
        (notMem_leftFam_natAdd j)
    · obtain ⟨j', hj', he⟩ := Finset.mem_map.mp h
      have hv := congrArg Fin.val he
      simp [Fin.natAddEmb, Fin.val_natAdd] at hv
      exact (Fin.ext hv : j' = j) ▸ hj'
  · exact fun h => Or.inr (Finset.mem_map_of_mem _ h)

@[simp] theorem castAdd_ne_natAdd (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  simp [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

@[simp] theorem natAdd_ne_castAdd (i : Fin m) (j : Fin n) :
    Fin.natAdd m j ≠ Fin.castAdd n i := (castAdd_ne_natAdd i j).symm

@[simp] theorem mem_map_castAddEmb (W₁ : Finset (Fin m)) (i : Fin m) :
    Fin.castAdd n i ∈ W₁.map (Fin.castAddEmb n) ↔ i ∈ W₁ := by
  constructor
  · intro h
    obtain ⟨i', hi', he⟩ := Finset.mem_map.mp h
    have hv := congrArg Fin.val he
    simp [Fin.castAddEmb, Fin.val_castAdd] at hv
    exact (Fin.ext hv : i' = i) ▸ hi'
  · exact fun h => Finset.mem_map_of_mem _ h

@[simp] theorem natAdd_notMem_map_castAddEmb (W₁ : Finset (Fin m))
    (j : Fin n) : Fin.natAdd m j ∉ W₁.map (Fin.castAddEmb n) :=
  fun h => notMem_leftFam_natAdd (m := m) j
    (Finset.mem_of_subset
      (Finset.map_subset_map.mpr (Finset.subset_univ W₁)) h)

@[simp] theorem mem_map_natAddEmb (W₂ : Finset (Fin n)) (j : Fin n) :
    Fin.natAdd m j ∈ W₂.map (Fin.natAddEmb m) ↔ j ∈ W₂ := by
  constructor
  · intro h
    obtain ⟨j', hj', he⟩ := Finset.mem_map.mp h
    have hv := congrArg Fin.val he
    simp [Fin.natAddEmb, Fin.val_natAdd] at hv
    exact (Fin.ext hv : j' = j) ▸ hj'
  · exact fun h => Finset.mem_map_of_mem _ h

@[simp] theorem castAdd_notMem_map_natAddEmb (W₂ : Finset (Fin n))
    (i : Fin m) : Fin.castAdd n i ∉ W₂.map (Fin.natAddEmb m) :=
  fun h => notMem_rightFam_castAdd (n := n) i
    (Finset.mem_of_subset
      (Finset.map_subset_map.mpr (Finset.subset_univ W₂)) h)

/-- The part of a world of the concatenation lying in the left family. -/
theorem catWorld_inter_leftFam (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    catWorld W₁ W₂ ∩ leftFam m n = W₁.map (Fin.castAddEmb n) := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    simp [Finset.mem_inter, notMem_leftFam_natAdd]

/-- What the left family misses of such a world. -/
theorem leftFam_sdiff_catWorld (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    leftFam m n \ catWorld W₁ W₂ = W₁ᶜ.map (Fin.castAddEmb n) := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    simp [Finset.mem_sdiff, notMem_leftFam_natAdd]

/-- The part lying in the right family. -/
theorem catWorld_inter_rightFam (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    catWorld W₁ W₂ ∩ rightFam m n = W₂.map (Fin.natAddEmb m) := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    simp [Finset.mem_inter, notMem_rightFam_castAdd]

/-- What the right family misses. -/
theorem rightFam_sdiff_catWorld (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    rightFam m n \ catWorld W₁ W₂ = W₂ᶜ.map (Fin.natAddEmb m) := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    simp [Finset.mem_sdiff, notMem_rightFam_castAdd]

/-- **Reading the left part of the concatenation is reading the family
it came from.** Nothing is asked of `K`: the relative annotation of the
left family at a concatenated world is the world annotation the left
family gives its own half. -/
theorem relAnn_catWorld_left (α : Fin m → K) (β : Fin n → K)
    (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    relAnn (catAnn α β) (leftFam m n) (catWorld W₁ W₂) = worldAnn α W₁ := by
  rw [relAnn, worldAnn, catWorld_inter_leftFam, leftFam_sdiff_catWorld,
    Finset.prod_map, Finset.sum_map]
  simp [Fin.castAddEmb, catAnn]

/-- The right-hand twin. -/
theorem relAnn_catWorld_right (α : Fin m → K) (β : Fin n → K)
    (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    relAnn (catAnn α β) (rightFam m n) (catWorld W₁ W₂) = worldAnn β W₂ := by
  rw [relAnn, worldAnn, catWorld_inter_rightFam, rightFam_sdiff_catWorld,
    Finset.prod_map, Finset.sum_map]
  simp [Fin.natAddEmb, catAnn]

/-- **A world of the union carries the product of its two halves'
annotations** – exactly where `K` is complemented, which is what the
split form in which two-family readings are usually written assumes. -/
theorem worldAnn_catWorld (hc : complemented K) (α : Fin m → K)
    (β : Fin n → K) (W₁ : Finset (Fin m)) (W₂ : Finset (Fin n)) :
    worldAnn (catAnn α β) (catWorld W₁ W₂) = worldAnn α W₁ * worldAnn β W₂ := by
  rw [← relAnn_univ, relAnn_split hc _ Finset.univ (leftFam m n),
    Finset.univ_inter, ← Finset.compl_eq_univ_sdiff, ← rightFam_eq_compl,
    relAnn_catWorld_left, relAnn_catWorld_right]

/-- The left half of a world of the concatenation. -/
def leftPart (W : Finset (Fin (m + n))) : Finset (Fin m) :=
  Finset.univ.filter (fun i => Fin.castAdd n i ∈ W)

/-- The right half of a world of the concatenation. -/
def rightPart (W : Finset (Fin (m + n))) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Fin.natAdd m j ∈ W)

@[simp] theorem mem_leftPart {W : Finset (Fin (m + n))} {i : Fin m} :
    i ∈ leftPart W ↔ Fin.castAdd n i ∈ W := by simp [leftPart]

@[simp] theorem mem_rightPart {W : Finset (Fin (m + n))} {j : Fin n} :
    j ∈ rightPart W ↔ Fin.natAdd m j ∈ W := by simp [rightPart]

@[simp] theorem leftPart_catWorld (W₁ : Finset (Fin m))
    (W₂ : Finset (Fin n)) : leftPart (catWorld W₁ W₂) = W₁ := by
  ext i; simp

@[simp] theorem rightPart_catWorld (W₁ : Finset (Fin m))
    (W₂ : Finset (Fin n)) : rightPart (catWorld W₁ W₂) = W₂ := by
  ext j; simp

@[simp] theorem catWorld_parts (W : Finset (Fin (m + n))) :
    catWorld (leftPart W) (rightPart W) = W := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp

/-- The worlds of the concatenation are the pairs of worlds. -/
def catWorldEquiv (m n : ℕ) :
    Finset (Fin m) × Finset (Fin n) ≃ Finset (Fin (m + n)) where
  toFun p := catWorld p.1 p.2
  invFun W := (leftPart W, rightPart W)
  left_inv p := by simp
  right_inv W := by simp

/-- **A sum over the worlds of the union is the double sum over pairs.** -/
theorem sum_catWorld {α : Type} [AddCommMonoid α]
    (f : Finset (Fin (m + n)) → α) :
    ∑ W : Finset (Fin (m + n)), f W
      = ∑ W₁ : Finset (Fin m), ∑ W₂ : Finset (Fin n), f (catWorld W₁ W₂) := by
  rw [show (∑ W₁ : Finset (Fin m), ∑ W₂ : Finset (Fin n), f (catWorld W₁ W₂))
      = ∑ p : Finset (Fin m) × Finset (Fin n), f (catWorld p.1 p.2) from
    (Fintype.sum_prod_type
      (fun p : Finset (Fin m) × Finset (Fin n) =>
        f (catWorld p.1 p.2))).symm]
  exact (Fintype.sum_equiv (catWorldEquiv m n) _ _ (fun p => rfl)).symm

/-! ## The joint reading of a test of two tokens -/

variable {T : Type} [ValueType T] [DecidableEq K]

/-- **What a predicate reading two aggregate values annotates**: the `⊕`
over the worlds of the union of the two families – those meeting each
*grouped* one, a scalar token being exempt as always – of the world's
annotation times the truth of the test there.

This is the definition; the structural rules `∧ ↦ ⊗` and `∨ ↦ ⊕`
compute it where the m-semiring's properties license them. -/
def jointPair (a b : AggValue T K) (P : T → T → Kleene) : K :=
  ∑ W ∈ Finset.univ.filter
      (fun W : Finset (Fin (a.occs.length + b.occs.length)) =>
        (a.scalar = true ∨ (leftPart W).Nonempty)
          ∧ (b.scalar = true ∨ (rightPart W).Nonempty)),
    worldAnn (catAnn a.anns b.anns) W
      * (if P (a.valOn (leftPart W)) (b.valOn (rightPart W)) = Kleene.true
          then 1 else 0)

omit [ValueType T] [DecidableEq K] in
/-- **The joint reading is the split double sum where `K` is
complemented**, which is how a two-family reading is usually written.
Where it is not, the double sum is not the union reading and this is the
one to use. -/
theorem jointPair_eq_split (hc : complemented K) (a b : AggValue T K)
    (P : T → T → Kleene) :
    jointPair a b P
      = ∑ W₁ ∈ Finset.univ.filter
          (fun W₁ : Finset (Fin a.occs.length) =>
            a.scalar = true ∨ W₁.Nonempty),
          ∑ W₂ ∈ Finset.univ.filter
            (fun W₂ : Finset (Fin b.occs.length) =>
              b.scalar = true ∨ W₂.Nonempty),
            worldAnn a.anns W₁ * worldAnn b.anns W₂
              * (if P (a.valOn W₁) (b.valOn W₂) = Kleene.true then 1 else 0) := by
  unfold jointPair
  rw [Finset.sum_filter, sum_catWorld, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun W₁ _ => ?_)
  by_cases h₁ : a.scalar = true ∨ W₁.Nonempty
  · rw [ite_eq_left h₁, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun W₂ _ => ?_)
    simp only [leftPart_catWorld, rightPart_catWorld, worldAnn_catWorld hc]
    by_cases h₂ : b.scalar = true ∨ W₂.Nonempty
    · simp only [h₁, h₂, and_self, ite_true, mul_assoc]
    · simp only [h₂, and_false, ite_false]
  · rw [ite_eq_right h₁]
    refine Finset.sum_eq_zero (fun W₂ _ => ?_)
    simp only [leftPart_catWorld, rightPart_catWorld, h₁, false_and,
      ite_false]

end Having
