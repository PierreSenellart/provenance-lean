import Mathlib.Computability.Language

import Provenance.SemiringWithMonus

/-!
# The regular-expression m-semiring (ProvSQL's `sr_regex`)

The semiring of languages over an alphabet of labels, with `⊕` the union,
`⊗` the concatenation, `𝟘 = ∅` and `𝟙 = {ε}`: `Language α` of Mathlib,
whose `Semiring` instance is exactly this. ProvSQL's `sr_regex`
(`src/semiring/Regex.h`, since 1.13.0) computes in it, each value written
as a regular expression, a product gate concatenating its factors in the
order of the query. **Concatenation does not commute**, which makes this
the first entry of the catalog whose multiplication is not commutative:
`not_commutative` below exhibits `a · b ≠ b · a`.

What ProvSQL claims of it, verified here:
- it is an m-semiring: the natural order is inclusion, the monus is the
  difference of languages (Mathlib's `OrderedSub` instance is precisely
  `monus_spec`), and `δ` is the indicator of being non-empty – ProvSQL
  *refuses* to compute the monus (`semiring-no-monus`: it needs automata,
  and `𝟙 ⊖ L = 𝟙` for a language without the empty word, which is right
  but registers no absence), but the monus exists, so the refusal is a
  gap of the implementation and not of the algebra;
- `⊕` is idempotent (`idempotent_add`) and the semiring is complemented
  (`complemented_of`), but **neither absorptive nor exclusive**
  (`not_absorptive`: `𝟙 ⊕ a ≠ 𝟙` as soon as `a` holds a non-empty word;
  `not_exclusive`: `{a} ⊗ (𝟙 ⊖ {a}) = {a} ≠ 𝟘`, the monus of `𝟙` by a
  language without the empty word being `𝟙` itself);
- every value has a Kleene star (Mathlib's `Language.kstar`), with the
  identities ProvSQL's simplifier applies: `(ε ∪ a)∗ = a∗`,
  `(a∗)∗ = a∗`, `∅∗ = ε∗ = ε`, and `a∗ = 𝟙 ⊕ a ⊗ a∗` on either side
  (`Language.one_add_self_mul_kstar_eq_kstar`,
  `Language.one_add_kstar_mul_self_eq_kstar`).

The restriction to *regular* languages is a representation matter:
ProvSQL writes its values as regular expressions and its operations keep
them regular, so its values form a subsemiring of this one, closed under
the star; the algebra is the same.
-/

namespace Language

variable {α : Type}

open Classical in
/-- ProvSQL's `Regex::delta`: the indicator of being non-empty. -/
noncomputable def deltaInd (l : Language α) : Language α :=
  if l = 0 then 0 else 1

theorem deltaInd_isIndicator : IsDeltaIndicator (deltaInd : Language α → Language α) where
  zero := by simp [deltaInd]
  nonzero := fun a ha => by simp [deltaInd, ha]

/-- `{ε}` is not `∅`. -/
theorem one_ne_zero' : (1 : Language α) ≠ 0 := fun h => by
  have hmem : [] ∈ (1 : Language α) := (mem_one []).mpr rfl
  rw [h] at hmem
  exact hmem

/-- Every positive natural-number cast is `𝟙`, union being idempotent. -/
theorem natCast_pos {n : ℕ} (hn : 0 < n) : ((n : Language α)) = 1 := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ k ih =>
    rw [Nat.cast_succ]
    cases Nat.eq_zero_or_pos k with
    | inl hk => rw [hk, Nat.cast_zero, zero_add]
    | inr hk => rw [ih hk, add_self]

/-- **Languages form an m-semiring**: inclusion for the order, the
difference for the monus, the indicator of non-emptiness for `δ`. -/
noncomputable instance instSemiringWithMonus : SemiringWithMonus (Language α) where
  add_le_add_left := fun _ _ h c => sup_le_sup_right h c
  exists_add_of_le := fun {_ b} h => ⟨b, (sup_eq_right.mpr h).symm⟩
  le_self_add := fun _ _ => le_sup_left
  le_add_self := fun _ _ => le_sup_right
  monus_spec := fun a b c => by
    rw [tsub_le_iff_right, add_comm]
  delta := deltaInd
  delta_zero := deltaInd_isIndicator.zero
  delta_natCast_pos := fun hn => by
    rw [natCast_pos hn]
    exact deltaInd_isIndicator.nonzero 1 one_ne_zero'
  delta_absorb := delta_absorb_indicator deltaInd_isIndicator

/-- `⊕` is idempotent: it is a union. -/
theorem idempotent_add : idempotent (Language α) := add_self

/-- **Concatenation does not commute**: two distinct letters in either
order are two distinct words. -/
theorem not_commutative {a b : α} (hab : a ≠ b) :
    ({[a]} : Language α) * {[b]} ≠ ({[b]} : Language α) * {[a]} := by
  intro h
  have hmem : [a, b] ∈ ({[a]} : Language α) * {[b]} :=
    mem_mul.mpr ⟨[a], rfl, [b], rfl, rfl⟩
  rw [h] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_mul.mp hmem
  rw [Set.mem_singleton_iff] at hx hy
  subst hx hy
  exact hab (List.cons.inj hxy).1.symm

/-- **Not absorptive**: `𝟙 ⊕ a ≠ 𝟙` as soon as `a` holds a non-empty
word – a longer derivation is not dropped next to a shorter one. -/
theorem not_absorptive {a : α} : (1 : Language α) + {[a]} ≠ 1 := by
  intro h
  have hmem : [a] ∈ (1 : Language α) + {[a]} := (mem_add _ _ _).mpr (Or.inr rfl)
  rw [h, mem_one] at hmem
  exact List.cons_ne_nil a [] hmem

/-- **Not exclusive**: `𝟙 ⊖ a` is `{ε}` whenever `a` has no empty word,
and then `a ⊗ (𝟙 ⊖ a) = a ≠ 𝟘`. (`sr_regex` claims no exclusivity; the
fact is recorded because the catalog counts its exclusive entries.) -/
theorem not_exclusive {a : α} :
    ({[a]} : Language α) * (1 - {[a]}) ≠ 0 := by
  intro h
  have hmem : [a] ∈ ({[a]} : Language α) * (1 - {[a]}) := by
    refine mem_mul.mpr ⟨[a], rfl, [], ?_, List.append_nil _⟩
    show [] ∈ (1 : Language α) ∧ [] ∉ ({[a]} : Language α)
    exact ⟨(mem_one []).mpr rfl, fun h => List.cons_ne_nil a []
      (Set.mem_singleton_iff.mp h).symm⟩
  rw [h] at hmem
  exact hmem

/-- **Complemented**: `𝟙 ⊖ (a ⊕ b) = (𝟙 ⊖ a) ⊗ (𝟙 ⊖ b)`, both sides being
`{ε}` exactly when neither language has the empty word. -/
theorem complemented_of : complemented (Language α) := by
  intro a b
  ext x
  constructor
  · intro hx
    obtain ⟨h1, hnab⟩ : x ∈ (1 : Language α) ∧ x ∉ a + b := hx
    obtain rfl : x = [] := (mem_one x).mp h1
    rw [mem_add] at hnab
    refine mem_mul.mpr ⟨[], ?_, [], ?_, rfl⟩
    · exact (⟨(mem_one []).mpr rfl, fun h => hnab (Or.inl h)⟩ :
        [] ∈ (1 : Language α) ∧ [] ∉ a)
    · exact (⟨(mem_one []).mpr rfl, fun h => hnab (Or.inr h)⟩ :
        [] ∈ (1 : Language α) ∧ [] ∉ b)
  · intro hx
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_mul.mp hx
    obtain ⟨hu1, hna⟩ : u ∈ (1 : Language α) ∧ u ∉ a := hu
    obtain ⟨hv1, hnb⟩ : v ∈ (1 : Language α) ∧ v ∉ b := hv
    obtain rfl : u = [] := (mem_one u).mp hu1
    obtain rfl : v = [] := (mem_one v).mp hv1
    refine (⟨(mem_one []).mpr rfl, fun h => ?_⟩ :
      [] ∈ (1 : Language α) ∧ [] ∉ a + b)
    rcases (mem_add _ _ _).mp h with h | h
    · exact hna h
    · exact hnb h

/-! ## The star identities ProvSQL's simplifier applies -/

/-- `∅∗ = ε`. -/
theorem kstar_zero : KStar.kstar (0 : Language α) = 1 := by
  ext x
  rw [mem_kstar, mem_one]
  constructor
  · rintro ⟨L, rfl, hL⟩
    cases L with
    | nil => rfl
    | cons y L => exact (hL y List.mem_cons_self).elim
  · rintro rfl
    exact ⟨[], rfl, fun y hy => (List.not_mem_nil hy).elim⟩

/-- `ε∗ = ε`. -/
theorem kstar_one : KStar.kstar (1 : Language α) = 1 := by
  ext x
  rw [mem_kstar, mem_one]
  constructor
  · rintro ⟨L, rfl, hL⟩
    exact List.flatten_eq_nil_iff.mpr fun y hy => (mem_one y).mp (hL y hy)
  · rintro rfl
    exact ⟨[], rfl, fun y hy => (List.not_mem_nil hy).elim⟩

/-- `(ε ∪ a)∗ = a∗`: the empty word is in every star already. -/
theorem kstar_one_add (a : Language α) : KStar.kstar (1 + a) = KStar.kstar a := by
  ext x
  rw [mem_kstar, mem_kstar]
  constructor
  · rintro ⟨L, rfl, hL⟩
    refine ⟨L.filter (· ≠ []), ?_, fun y hy => ?_⟩
    · rw [List.flatten_filter_ne_nil]
    · have hy' := List.mem_filter.mp hy
      rcases (mem_add _ _ _).mp (hL y hy'.1) with h | h
      · exact absurd ((mem_one y).mp h) (by simpa using hy'.2)
      · exact h
  · rintro ⟨L, rfl, hL⟩
    exact ⟨L, rfl, fun y hy => (mem_add _ _ _).mpr (Or.inr (hL y hy))⟩

/-- `KStar.kstar (KStar.kstar a) = KStar.kstar a`. -/
theorem kstar_kstar (a : Language α) : KStar.kstar (KStar.kstar a) = KStar.kstar a := by
  ext x
  constructor
  · intro hx
    rw [mem_kstar] at hx
    obtain ⟨L, rfl, hL⟩ := hx
    induction L with
    | nil => exact nil_mem_kstar a
    | cons y L ih =>
      rw [List.flatten_cons]
      have hy : y ∈ KStar.kstar a := hL y List.mem_cons_self
      have hrest : L.flatten ∈ KStar.kstar a := ih fun z hz => hL z (List.mem_cons_of_mem y hz)
      rw [mem_kstar] at hy hrest
      obtain ⟨Ly, rfl, hLy⟩ := hy
      obtain ⟨Lr, hLr, hLr'⟩ := hrest
      rw [hLr, ← List.flatten_append]
      exact join_mem_kstar fun z hz => by
        rcases List.mem_append.mp hz with h | h
        · exact hLy z h
        · exact hLr' z h
  · intro hx
    exact mem_kstar.mpr ⟨[x], by simp, fun y hy => by
      rw [List.mem_singleton] at hy
      exact hy ▸ hx⟩

end Language
