/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
module

public import Provenance.AnnotatedApproxRows
public import Provenance.AnnotatedChains
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Provenance.AnnotatedSum

/-!
# The apply row up to `≈` with occurrence identity

Annotated results are compared up to `≈`, equality up to rows annotated
`𝟘`: rows annotated `𝟘` and occurrences annotated `𝟘` are
dropped, and what is left is equal up to a one-to-one renaming of the
occurrences, which keeps which aggregate values share which occurrences.
`GeneratesAnnZ` reads an aggregate value only through its value; this
module compares aggregate values through their occurrences, using the
identities the evaluator stamps on them (`AggValue.oids`,
`AggExpr.oids`).

* `GenRow.zeqRen` is that comparison. An ordinary token and an aggregate
  expression are compared by what they compute and by their occurrences
  annotated otherwise than `𝟘` with their identities, renamed by one
  injective map for the whole result. A nested value is compared the same
  way at every storey of what its occurrences read, with its occurrences
  annotated `𝟘` dropped at every storey; its own occurrences carry no
  identity, and its family, renamed by a second injective map, says which
  nested values share them. What it does not record is which occurrence of
  one nested value is which occurrence of another of the same family.
* `GeneratesAnnRen` is the generation predicate up to it.
* `apply_mem_of_generatesAnnRen` is the apply row: over Boolean functions
  of two variables, a set generating up to it holds the apply.
* `annEpsOps_isBasis_in_class_ren` is the annotated basis theorem up to it,
  over `AnnBasisClass`: the nine classes generate, no proper subset of them
  does, and no set of classes does without the apply.
-/

@[expose] public section

variable {T K : Type} [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]

section Equivalence

/-- An ordinary token with its occurrences annotated `𝟘` dropped, together
with their identities, and its family forgotten. -/
def AggValue.zeroOccs (a : AggValue T K) : AggValue T K :=
  { a with
    occs := a.occs.filter (fun o => o.2 ≠ 0)
    oids := ((a.occs.zip a.oids).filter (fun p => p.1.2 ≠ 0)).map Prod.snd
    fam := FamId.none }

/-- The identities of a token's occurrences renamed. -/
def AggValue.renameOids (τ : OccId T → OccId T) (a : AggValue T K) : AggValue T K :=
  { a with oids := a.oids.map τ }

/-- **A family identifier with its family renamed** by `ϕ`: the column and
the terms applied since are kept, so two identifiers of one family stay of
one family. -/
def FamId.renameFamily (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T)) :
    FamId T → FamId T
  | .mk l k p c ts => .mk (ϕ (l, k, p)).1 (ϕ (l, k, p)).2.1 (ϕ (l, k, p)).2.2 c ts

/-- An aggregate expression read up to `≈`: its occurrences annotated `𝟘`
dropped together with their identities, the others' identities renamed by
`τ`, and its family by `φ`. -/
def AggExpr.zeqNorm (τ : OccId T → OccId T) (φ : FamId T → FamId T) (e : AggExpr T K) :
    AggExpr T K :=
  { e with
    occs := e.occs.filter (fun o => o.2.1 ≠ 0)
    fam := φ e.fam
    oids := (((e.occs.zip e.oids).filter (fun p => p.1.2.1 ≠ 0)).map Prod.snd).map τ }

/-- What an occurrence of a nested value reads, up to `≈`: at every storey
the occurrences annotated `𝟘` dropped, the identities of the expressions'
occurrences renamed by `τ`, and the families renamed by `ϕ`. -/
def NestInner.zeqNorm (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T)) :
    (j : ℕ) → NestInner T K j → NestInner T K j
  | 0, e => AggExpr.zeqNorm (T := T) (K := K) τ (FamId.renameFamily ϕ) e
  | j + 1, Sum.inl x => Sum.inl (NestInner.zeqNorm τ ϕ j x)
  | j + 1, Sum.inr N => Sum.inr ⟨N.agg, (N.occs.filter (fun o => o.2 ≠ 0)).map
      (fun o => (NestInner.zeqNorm τ ϕ j o.1, o.2)), N.scalar, FamId.renameFamily ϕ N.fam⟩

/-- A nested value read up to `≈`: its occurrences annotated `𝟘` dropped,
what the others read normalized at every storey, and its family renamed. -/
def NestedValue.zeqNorm (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T))
    (a : NestedValue T K) : NestedValue T K :=
  ⟨a.lev, a.agg, (a.occs.filter (fun o => o.2 ≠ 0)).map
    (fun o => (NestInner.zeqNorm τ ϕ a.lev o.1, o.2)), a.scalar, FamId.renameFamily ϕ a.fam⟩

/-- A column value read up to `≈`, its occurrence identities renamed by `τ`
and its families by `ϕ`. An ordinary token and an expression are read by
their occurrences annotated otherwise than `𝟘`, their identities saying
which occurrences they share with other values, and their families
forgotten. A nested value is read the same way at every storey of what its
occurrences read; its own occurrences carry no identity, and which ones two
nested values share is said by their families, which are renamed rather
than forgotten. -/
def GenValue.zeqNorm (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T)) :
    GenValue T K → GenValue T K
  | .inl v => .inl v
  | .inr (.tok a) => .inr (.tok (a.zeroOccs.renameOids τ))
  | .inr (.expr e) => .inr (.expr (e.zeqNorm τ (fun _ => FamId.none)))
  | .inr (.nest a) => .inr (.nest (a.zeqNorm τ ϕ))

/-- A result read up to `≈`: its rows annotated otherwise than `𝟘`, each
column read by `GenValue.zeqNorm τ ϕ`, with its annotation. -/
def GenRow.zeqNorm {n : ℕ} (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T))
    (R : Multiset (GenRow T K n)) : Multiset (Tuple (GenValue T K) n × K) :=
  (R.filter (fun r => r.snd.finalize ≠ 0)).map
    (fun r => (fun k => GenValue.zeqNorm τ ϕ (r.fst k), r.snd.finalize))

/-- **Two results equivalent up to `≈`**: equal once the rows
and occurrences annotated `𝟘` are dropped, up to a one-to-one renaming of
the occurrences and one of the families. -/
def GenRow.zeqRen {n : ℕ} (R R' : Multiset (GenRow T K n)) : Prop :=
  ∃ (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T)),
    Function.Injective τ ∧ Function.Injective ϕ ∧
      GenRow.zeqNorm τ ϕ R' = GenRow.zeqNorm id id R

end Equivalence

/-- **A set of classes generates the annotated algebra up to `≈` with
occurrence identity**: `GeneratesAnnZ` with `GenRow.zeqRen` in place of
`GenRow.zeroNorm`. -/
def GeneratesAnnRen (T : Type) [ValueType T] (K : Type) [CommSemiringWithMonus K]
    [DecidableEq K] [HasAltLinearOrder K] (sch : Schema) (cnt : SeqAggFunc T)
    (S : Set OpKind) : Prop :=
  ∀ {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ),
    q.overSchema sch → q.usesOnly plainRecOps → q.inMinimalSig cnt → q.noExplode →
      q.wellKinded (ColKind.allReg 0) HoleKinds.empty →
      ∃ q' : AggQuery T n κ,
        q'.overSchema sch ∧ q'.usesOnly S ∧ q'.inMinimalSig cnt ∧ q'.noExplode
          ∧ q'.wellKinded (ColKind.allReg 0) HoleKinds.empty
          ∧ ∀ (d : AnnotatedDatabase T K) (γ : Fin 0 → T), q.AnnSettlesAt d γ {} →
              q'.AnnSettlesAt d γ {}
                ∧ GenRow.zeqRen (q.evaluate d γ) (q'.evaluate d γ)

/-! ## Hitting the occurrences annotated `y`

The bound behind the row: in a query with no `apply`, every ordinary token
holding an occurrence annotated `y` holds one whose identity lies in a set
`Z` whose size depends on the query and not on the instance. -/

section Hitting

/-- **`Z` hits the token's occurrences annotated `y`**: if it holds one, it
holds one whose identity is in `Z`. -/
def AggValue.HitBy (y : K) (Z : Finset (OccId T)) (a : AggValue T K) : Prop :=
  (∃ p ∈ a.occs.zip a.oids, p.1.2 = y) → ∃ p ∈ a.occs.zip a.oids, p.1.2 = y ∧ p.2 ∈ Z

/-- The same of a column value: every ordinary token it holds is hit. -/
def GenValue.TokHit (y : K) (Z : Finset (OccId T)) (v : GenValue T K) : Prop :=
  ∀ a, v = Sum.inr (AggTok.tok a) → a.HitBy y Z

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
theorem AggValue.HitBy.mono {y : K} {Z Z' : Finset (OccId T)} {a : AggValue T K}
    (h : a.HitBy y Z) (hZ : Z ⊆ Z') : a.HitBy y Z' := fun he => by
  obtain ⟨p, hp, hy, hz⟩ := h he
  exact ⟨p, hp, hy, hZ hz⟩

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
theorem GenValue.TokHit.mono {y : K} {Z Z' : Finset (OccId T)} {v : GenValue T K}
    (h : GenValue.TokHit y Z v) (hZ : Z ⊆ Z') : GenValue.TokHit y Z' v :=
  fun a ha => (h a ha).mono hZ

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A regular value holds no token. -/
theorem GenValue.tokHit_inl (y : K) (Z : Finset (OccId T)) (v : T) :
    GenValue.TokHit y Z (Sum.inl v : GenValue T K) :=
  fun _ h => by cases h

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A token of another kind is no ordinary token. -/
theorem GenValue.tokHit_of_not_tok (y : K) (Z : Finset (OccId T)) (x : AggTok T K)
    (hx : ∀ a, x ≠ AggTok.tok a) : GenValue.TokHit y Z (Sum.inr x : GenValue T K) :=
  fun a h => absurd (Sum.inr.inj h) (hx a)

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **A term applied to a token keeps its occurrences.** -/
theorem GenValue.TokHit.postcompTerm {y : K} {Z : Finset (OccId T)} {x : AggTok T K}
    (h : GenValue.TokHit y Z (Sum.inr x)) (t : TermIn T 1 0) :
    GenValue.TokHit y Z (Sum.inr (x.postcompTerm t)) := by
  intro a ha
  cases x with
  | tok b =>
    have hb := h b rfl
    have : a = { b.postcomp t.unary with fam := b.fam.addTerm t } := by
      simp only [AggTok.postcompTerm, AggTok.postcomp, AggTok.setFam, Option.getD_none] at ha
      exact (AggTok.tok.inj (Sum.inr.inj ha)).symm
    subst this
    exact hb
  | nest b => simp [AggTok.postcompTerm, AggTok.postcomp, AggTok.setFam] at ha
  | expr b => simp [AggTok.postcompTerm, AggTok.postcomp, AggTok.setFam] at ha

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The occurrences of a listing paired with their positions. -/
theorem mem_zip_listing {α : Type} (g : α → T × K) (l : List α) (lab : ℕ)
    (ps : List (T ⊕ FamId T)) (key : List T) (p : (T × K) × OccId T) :
    p ∈ (l.map g).zip (OccId.listing lab ps key l.length)
      ↔ ∃ (i : ℕ) (hi : i < l.length), p = (g l[i], ⟨lab, ps, key, i⟩) := by
  rw [List.mem_iff_getElem]
  simp only [List.length_zip, List.length_map, OccId.listing, List.length_range, min_self,
    List.getElem_zip, List.getElem_map, List.getElem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

omit [CommSemiringWithMonus K] in
/-- **A token over a whole listing is hit by the identity of its first
occurrence annotated `y`.** -/
theorem AggValue.hitBy_listing (y : K) (Z : Finset (OccId T))
    {c m : ℕ} (f : SeqAggFunc T) (t : TermIn T c m) (U : List (AnnotatedTuple T K m))
    (γ : Fin c → T) (sc : Bool) (φ : FamId T) (lab : ℕ) (ps : List (T ⊕ FamId T))
    (key : List T)
    (hZ : (∃ p ∈ U, p.2 = y) →
      (⟨lab, ps, key, U.findIdx (fun p => decide (p.2 = y))⟩ : OccId T) ∈ Z) :
    ({ AggValue.ofGroup f t U γ with
        scalar := sc
        fam := φ
        oids := OccId.listing lab ps key U.length } : AggValue T K).HitBy y Z := by
  rintro ⟨p, hp, hy⟩
  have hp' := (mem_zip_listing (fun q : AnnotatedTuple T K m => (t.eval q.fst γ, q.snd)) U lab
    ps key p).1 (by simpa [AggValue.ofGroup] using hp)
  obtain ⟨i, hi, rfl⟩ := hp'
  have hex : ∃ q ∈ U, q.2 = y := ⟨U[i], List.getElem_mem hi, hy⟩
  have hlt : U.findIdx (fun p => decide (p.2 = y)) < U.length :=
    List.findIdx_lt_length_of_exists (by
      obtain ⟨q, hq, hqy⟩ := hex
      exact ⟨q, hq, by simpa using hqy⟩)
  have hfy : U[U.findIdx (fun p => decide (p.2 = y))].2 = y := by
    have := List.findIdx_getElem (w := hlt)
    simpa using this
  refine ⟨((t.eval U[U.findIdx (fun p => decide (p.2 = y))].fst γ,
      U[U.findIdx (fun p => decide (p.2 = y))].snd),
    ⟨lab, ps, key, U.findIdx (fun p => decide (p.2 = y))⟩), ?_, hfy, hZ hex⟩
  have := (mem_zip_listing (fun q : AnnotatedTuple T K m => (t.eval q.fst γ, q.snd)) U lab ps
    key _).2 ⟨_, hlt, rfl⟩
  simpa [AggValue.ofGroup] using this

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
theorem List.length_copyNums {α : Type} (e : α → α → Bool) :
    ∀ (seen l : List α), (List.copyNums e seen l).length = l.length
  | _, [] => rfl
  | seen, a :: l => by simp [List.copyNums, List.length_copyNums e (a :: seen) l]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The copy number of an element counts the equal ones before it. -/
theorem List.getElem_copyNums {α : Type} (e : α → α → Bool) :
    ∀ (seen l : List α) (i : ℕ) (hi : i < l.length),
      (List.copyNums e seen l)[i]'(by rw [List.length_copyNums]; exact hi)
        = (seen ++ (l.take i).reverse).countP (e l[i])
  | _, [], i, hi => absurd hi (Nat.not_lt_zero _)
  | seen, a :: l, 0, _ => by simp [List.copyNums]
  | seen, a :: l, i + 1, hi => by
    simp only [List.copyNums, List.getElem_cons_succ, List.take_succ_cons, List.reverse_cons]
    rw [List.getElem_copyNums e (a :: seen) l i (by simpa using hi)]
    simp only [List.cons_append, List.countP_append, List.countP_cons, List.countP_nil]
    omega

omit [CommSemiringWithMonus K] in
/-- **A window's token is hit by the identity of the first copy of its first
occurrence annotated `y`**: no equal element comes before it, so its copy
number is `0`. -/
theorem AggValue.hitBy_frame (y : K) (Z : Finset (OccId T)) {c m : ℕ} (f : SeqAggFunc T)
    (t : TermIn T c m) (F : List (AnnotatedTuple T K m)) (γ : Fin c → T) (sc : Bool)
    (φ : FamId T) (lab : ℕ) (ck : List (T ⊕ FamId T)) (key : List T)
    (part : List (AnnotatedTuple T K m)) (e : AnnotatedTuple T K m → AnnotatedTuple T K m → Bool)
    (he : ∀ a b, e a b = true ↔ a = b)
    (hZ : ∀ b ∈ F, b.2 = y → (⟨lab, ck, key, part.findIdx (e b)⟩ : OccId T) ∈ Z) :
    ({ AggValue.ofGroup f t F γ with
        scalar := sc
        fam := φ
        oids := List.zipWith (fun a n => (⟨lab, ck, key, part.findIdx (e a) + n⟩ : OccId T))
          F (List.copyNums e [] F) } : AggValue T K).HitBy y Z := by
  rintro ⟨p, hp, hy⟩
  simp only [AggValue.ofGroup] at hp ⊢
  have hlen : (List.copyNums e [] F).length = F.length := List.length_copyNums e [] F
  -- the occurrence held, at its position
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  simp only [List.length_zip, List.length_map, List.length_zipWith, hlen, min_self] at hi
  simp only [List.getElem_zip, List.getElem_map] at hy
  have hex : ∃ q ∈ F, decide (q.2 = y) = true := ⟨F[i], List.getElem_mem hi, by simpa using hy⟩
  set i0 := F.findIdx (fun q => decide (q.2 = y)) with hi0
  have hlt : i0 < F.length := List.findIdx_lt_length_of_exists hex
  have hfy : F[i0].2 = y := by simpa using List.findIdx_getElem (w := hlt)
  have hbefore : ∀ j (hj : j < i0), F[j].2 ≠ y := fun j hj => by
    simpa using List.not_of_lt_findIdx hj
  -- its copy number is `0`
  have hc0 : (List.copyNums e [] F)[i0]'(by rw [hlen]; exact hlt) = 0 := by
    rw [List.getElem_copyNums e [] F i0 hlt, List.nil_append, List.countP_eq_zero]
    intro q hq hqe
    rw [he] at hqe
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_reverse.1 hq)
    rw [List.length_take] at hj
    have hj' : j < i0 := lt_of_lt_of_le hj (min_le_left _ _)
    rw [List.getElem_take] at hqe
    exact hbefore j hj' (by rw [← hqe]; exact hfy)
  refine ⟨((t.eval F[i0].fst γ, F[i0].snd),
    ⟨lab, ck, key, part.findIdx (e F[i0])⟩), ?_, hfy, hZ _ (List.getElem_mem hlt) hfy⟩
  rw [List.mem_iff_getElem]
  refine ⟨i0, by simp [hlen, hlt], ?_⟩
  simp only [List.getElem_zip, List.getElem_map, List.getElem_zipWith, hc0, Nat.add_zero]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **A function applied to a value keeps the occurrences of its token.** -/
theorem GenValue.TokHit.map_postcomp {y : K} {Z : Finset (OccId T)} {v : GenValue T K}
    (h : GenValue.TokHit y Z v) (gf : T → T) :
    GenValue.TokHit y Z (Sum.map gf (AggTok.postcomp gf) v) := by
  intro a ha
  cases v with
  | inl _ => cases ha
  | inr x =>
    cases x with
    | tok b =>
      have : a = b.postcomp gf := (AggTok.tok.inj (Sum.inr.inj ha)).symm
      subst this
      exact h b rfl
    | nest b => cases ha
    | expr b => cases ha

omit [CommSemiringWithMonus K] [DecidableEq K] in
/-- **A term applied to a value keeps the occurrences of its token.** -/
theorem GenValue.TokHit.map_postcompTerm {y : K} {Z : Finset (OccId T)} {v : GenValue T K}
    (h : GenValue.TokHit y Z v) (t : TermIn T 1 0) :
    GenValue.TokHit y Z (Sum.map t.unary (AggTok.postcompTerm t) v) := by
  cases v with
  | inl _ => exact GenValue.tokHit_inl _ _ _
  | inr x => exact GenValue.TokHit.postcompTerm h t

end Hitting

/-! ## The bound, through every operator -/

section Bound

open Classical

variable [HasAltLinearOrder K]

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **A recursion that every round keeps keeps its sum**: if the base and
every round built from rows with a property have it, so does the sum of
the rounds. -/
theorem muSum_forall {α : Type} (P : α → Prop) (step : Multiset α → Multiset α)
    (hstep : ∀ X : Multiset α, (∀ x ∈ X, P x) → ∀ x ∈ step X, P x) :
    ∀ (b : ℕ) (M : Multiset α), (∀ x ∈ M, P x) → ∀ x ∈ muSum step b M, P x
  | 0, M, hM => hM
  | b + 1, M, hM => by
    intro x hx
    rcases Multiset.mem_add.1 hx with h | h
    · exact hM x h
    · exact muSum_forall P step hstep b (step M) (hstep M hM) x h

/-- **A row annotated `y` of a closed subquery holds only constants and
values of `V`**, by the bound on the values each row holds
(`rowBd_evaluate`). The zero is added for the window, which reads an
aggregate column as it. -/
theorem AggQueryIn.yrow_mem (y : K) {Θ : Set (SeqAggFunc T)} {Bd : T → K → Prop}
    (hB : BdClosed Bd) (Fv V : Finset T) (hyV : ∀ v, v ∉ Fv → Bd v y → v ∈ V)
    {c m : ℕ} {κ : Fin m → ColKind} (q : AggQueryIn T c m κ []) (hsig : q.inSig Θ)
    (hex : q.noExplode) {ρc : Fin c → ColKind} {HK : HoleKinds} (hwk : q.wellKinded ρc HK)
    (hF : ∀ x ∈ q.allConsts, x ∈ Fv) (d : AnnotatedDatabase T K)
    (hD : ∀ (m : ℕ) (s : String) (r : AnnotatedRelation T K m), d.find m s = some r →
      ∀ a ∈ r, TupBd (· ∈ Fv) Bd (a.1, a.2))
    (γ : Fin c → T) (C : Tuple (GenValue T K) c) (hγ : ∀ k, γ k ∈ Fv)
    (hC : ∀ k v, C k = Sum.inl v → v ∈ Fv) {r : GenRow T K m}
    (hr : r ∈ q.evaluate d γ (({} : EvalEnv T K).withCtx C)) (hy : r.snd.finalize = y)
    {k : Fin m} {v : T} (hk : r.fst k = Sum.inl v) :
    v ∈ Union.union (Union.union Fv V) {0} := by
  have h := rowBd_evaluate hB q hsig hex hwk (· ∈ Fv) hF
    (fun p _ rn hf a ha => hD p.1 p.2 rn hf a ha) γ _ (fun k _ => hγ k)
    (fun k v hv => hC k v (by rwa [EvalEnv.ctxAt_withCtx] at hv))
    (fun p hp => absurd hp List.not_mem_nil) r hr k v hk
  rw [hy] at h
  by_cases hv : v ∈ Fv
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (hyV v hv (h.resolve_left hv)))

omit [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K] in
/-- **An occurrence of a frame is the row's own, or a row of the relation in
the row's partition.** -/
theorem mem_frameListOf_key {α : Type} [LinearOrder α] {n m p : ℕ} (val : α → Tuple T n)
    (P : Tuple (Fin n) m) (O : Tuple (Fin n) p) (o : OrderSpec p) (w : ValueFrame T p)
    (X : Multiset α) (x y : α) (h : y ∈ ValueFrame.frameListOf val P O o w X x) :
    y = x ∨ (y ∈ X ∧ Tuple.key P (val y) = Tuple.key P (val x)) := by
  have h1 : y ∈ sortList (ValueFrame.frameOf val P O w X x) :=
    (OrderSpec.sortSeq_perm _).mem_iff.1 h
  rw [mem_sortList] at h1
  unfold ValueFrame.frameOf at h1
  split_ifs at h1
  · rcases Multiset.mem_cons.1 h1 with rfl | h1
    · exact Or.inl rfl
    · have := Multiset.mem_filter.1 (Multiset.mem_of_mem_erase h1)
      exact Or.inr ⟨this.1, this.2.1⟩
  · have := Multiset.mem_filter.1 (Multiset.mem_of_mem_erase h1)
    exact Or.inr ⟨this.1, this.2.1⟩

/-- **What a window reads of a row annotated `y` lies in the bounded set**:
its regular columns by `AggQueryIn.yrow_mem`, its aggregate ones read as
`0`. -/
theorem AggQueryIn.readAnnotated_yrow_mem (y : K) {Θ : Set (SeqAggFunc T)}
    {Bd : T → K → Prop} (hB : BdClosed Bd) (Fv V : Finset T)
    (hyV : ∀ v, v ∉ Fv → Bd v y → v ∈ V)
    {c m : ℕ} {κ : Fin m → ColKind} (q : AggQueryIn T c m κ []) (hsig : q.inSig Θ)
    (hex : q.noExplode) {ρc : Fin c → ColKind} {HK : HoleKinds} (hwk : q.wellKinded ρc HK)
    (hF : ∀ x ∈ q.allConsts, x ∈ Fv) (d : AnnotatedDatabase T K)
    (hD : ∀ (m : ℕ) (s : String) (r : AnnotatedRelation T K m), d.find m s = some r →
      ∀ a ∈ r, TupBd (· ∈ Fv) Bd (a.1, a.2))
    (γ : Fin c → T) (C : Tuple (GenValue T K) c) (hγ : ∀ k, γ k ∈ Fv)
    (hC : ∀ k v, C k = Sum.inl v → v ∈ Fv) {r : GenRow T K m}
    (hr : r ∈ q.evaluate d γ (({} : EvalEnv T K).withCtx C)) (hy : r.snd.finalize = y)
    (k : Fin m) : (GenRow.readAnnotated κ r).fst k ∈ Union.union (Union.union Fv V) {0} := by
  have hreg := AggQueryIn.evaluate_conform q d r hr k
  show GenRow.readTuple κ r.fst k ∈ _
  unfold GenRow.readTuple
  split
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · rename_i hk
    cases hv : r.fst k with
    | inr x =>
      rw [hv] at hreg
      exact absurd hreg.symm (by simpa [GenValue.kindOf] using hk)
    | inl v =>
      simp only [AggValue.collapseSum]
      exact AggQueryIn.yrow_mem y hB Fv V hyV q hsig hex hwk hF d hD γ C hγ hC hr hy hv

/-- **Without an `apply`, the ordinary tokens holding an occurrence
annotated `y` are hit by a set of identities of size bounded by the query**,
uniformly over the instances whose relations are within a bound closed
under the operations (`BdClosed`), where a value bounded by `y` and not a
constant lies in `V`. -/
theorem AggQueryIn.exists_hit (y : K) {S : Set OpKind} (hS : OpKind.apply ∉ S)
    {Θ : Set (SeqAggFunc T)} {Bd : T → K → Prop} (hB : BdClosed Bd) (Fv V : Finset T)
    (hyV : ∀ v, v ∉ Fv → Bd v y → v ∈ V) :
    ∀ {c n : ℕ} {κ : Fin n → ColKind} {l : List (String × ℕ)} (q : AggQueryIn T c n κ l),
      q.usesOnly S → q.inSig Θ → q.noExplode → ∀ {ρc : Fin c → ColKind} {HK : HoleKinds},
      q.wellKinded ρc HK → (∀ x ∈ q.allConsts, x ∈ Fv) →
      ∃ B : ℕ, ∀ (d : AnnotatedDatabase T K),
        (∀ (m : ℕ) (s : String) (r : AnnotatedRelation T K m), d.find m s = some r →
          ∀ a ∈ r, TupBd (· ∈ Fv) Bd (a.1, a.2)) →
        ∀ (γ : Fin c → T) (C : Tuple (GenValue T K) c), (∀ k, γ k ∈ Fv) →
          (∀ k v, C k = Sum.inl v → v ∈ Fv) →
          ∃ Z : Finset (OccId T), Z.card ≤ B ∧ ∀ (Z₀ : Finset (OccId T)) (E : EvalEnv T K),
            E.ctxAt c γ = C → (∀ k, GenValue.TokHit y Z₀ (C k)) →
            (∀ p ∈ l, ∀ r ∈ E.holes p.1 p.2, ∀ k, GenValue.TokHit y Z₀ (r.fst k)) →
            ∀ r ∈ q.evaluate d γ E, ∀ k, GenValue.TokHit y (Union.union Z₀ Z) (r.fst k) := by
  intro c n κ l q
  induction q with
  | Rel n s =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate] at hr
    split at hr
    · exact absurd hr (Multiset.notMem_zero r)
    · obtain ⟨p, -, rfl⟩ := Multiset.mem_map.1 hr
      exact GenValue.tokHit_inl _ _ _
  | Hole n s κh =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ hH r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate] at hr
    exact (hH (s, n) (List.mem_singleton_self _) r (Multiset.mem_of_mem_filter hr) k).mono
      Finset.subset_union_left
  | Param pv ρ =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E hE hCt _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate, EvalEnv.paramRows] at hr
    split at hr
    · rw [Multiset.mem_singleton] at hr
      subst hr
      dsimp only
      cases hpk : pv k with
      | inl v => exact GenValue.tokHit_inl _ _ _
      | inr j =>
        simp only [Sum.elim_inr, hE]
        exact (hCt j).mono Finset.subset_union_left
    · exact absurd hr (Multiset.notMem_zero r)
  | Empty =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate] at hr
    exact absurd hr (Multiset.notMem_zero r)
  | Proj ps q ih =>
    intro hu hsig hex ρc HK hwk hF
    obtain ⟨B, hB'⟩ := ih hu.2 hsig.2 hex hwk.2
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inr hx))
    refine ⟨B, fun d hD γ C hγ hC => ?_⟩
    obtain ⟨Z, hZ, hZ'⟩ := hB' d hD γ C hγ hC
    refine ⟨Z, hZ, fun Z₀ E hE hCt hH r hr k => ?_⟩
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
    have h := hZ' Z₀ E hE hCt hH r₀ hr₀
    dsimp only
    cases hp : ps k with
    | term t => exact GenValue.tokHit_inl _ _ _
    | token k' _ => exact h k'
    | aggTerm k' _ gf => exact (h k').map_postcomp gf
    | aggTermOf k' _ t => exact (h k').map_postcompTerm t
    | provTerm t => exact GenValue.tokHit_inl _ _ _
  | Sel φ q hφ ih =>
    intro hu hsig hex ρc HK hwk hF
    obtain ⟨B, hB'⟩ := ih hu.2 hsig.2 hex hwk.2
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inr hx))
    refine ⟨B, fun d hD γ C hγ hC => ?_⟩
    obtain ⟨Z, hZ, hZ'⟩ := hB' d hD γ C hγ hC
    refine ⟨Z, hZ, fun Z₀ E hE hCt hH r hr k => ?_⟩
    simp only [AggQueryIn.evaluate] at hr
    split at hr
    · obtain ⟨r₀, hr₀, rfl⟩ := Multiset.mem_map.1 hr
      exact hZ' Z₀ E hE hCt hH r₀ hr₀ k
    · exact hZ' Z₀ E hE hCt hH r (Multiset.mem_of_mem_filter hr) k
  | Prod q₁ q₂ ih₁ ih₂ =>
    intro hu hsig hex ρc HK hwk hF
    obtain ⟨B₁, hB₁⟩ := ih₁ hu.2.1 hsig.1 hex.1 hwk.1
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inl hx))
    obtain ⟨B₂, hB₂⟩ := ih₂ hu.2.2 hsig.2 hex.2 hwk.2
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inr hx))
    refine ⟨B₁ + B₂, fun d hD γ C hγ hC => ?_⟩
    obtain ⟨Z₁, hZ₁, hZ₁'⟩ := hB₁ d hD γ C hγ hC
    obtain ⟨Z₂, hZ₂, hZ₂'⟩ := hB₂ d hD γ C hγ hC
    refine ⟨Union.union Z₁ Z₂, (Finset.card_union_le _ _).trans (Nat.add_le_add hZ₁ hZ₂),
      fun Z₀ E hE hCt hH r hr k => ?_⟩
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨⟨x, y'⟩, hxy, rfl⟩ := Multiset.mem_map.1 hr
    rw [Multiset.product, Multiset.mem_bind] at hxy
    obtain ⟨x', hx', hxy'⟩ := hxy
    obtain ⟨y'', hy'', hxy''⟩ := Multiset.mem_map.1 hxy'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy''
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · dsimp only
      erw [Fin.append_left]
      exact (hZ₁' Z₀ E hE hCt (fun p hp => hH p (List.mem_append_left _ hp)) _ hx' i).mono
        (Finset.union_subset_union le_rfl Finset.subset_union_left)
    · dsimp only
      erw [Fin.append_right]
      exact (hZ₂' Z₀ E hE hCt (fun p hp => hH p (List.mem_append_right _ hp)) _ hy'' i).mono
        (Finset.union_subset_union le_rfl Finset.subset_union_right)
  | Apply q₁ q₂ ih₁ ih₂ =>
    intro hu
    exact absurd hu.1 hS
  | Sum q₁ q₂ ih₁ ih₂ =>
    intro hu hsig hex ρc HK hwk hF
    obtain ⟨B₁, hB₁⟩ := ih₁ hu.2.1 hsig.1 hex.1 hwk.1
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inl hx))
    obtain ⟨B₂, hB₂⟩ := ih₂ hu.2.2 hsig.2 hex.2 hwk.2
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inr hx))
    refine ⟨B₁ + B₂, fun d hD γ C hγ hC => ?_⟩
    obtain ⟨Z₁, hZ₁, hZ₁'⟩ := hB₁ d hD γ C hγ hC
    obtain ⟨Z₂, hZ₂, hZ₂'⟩ := hB₂ d hD γ C hγ hC
    refine ⟨Union.union Z₁ Z₂, (Finset.card_union_le _ _).trans (Nat.add_le_add hZ₁ hZ₂),
      fun Z₀ E hE hCt hH r hr k => ?_⟩
    simp only [AggQueryIn.evaluate] at hr
    rcases Multiset.mem_add.1 hr with h | h
    · exact (hZ₁' Z₀ E hE hCt (fun p hp => hH p (List.mem_append_left _ hp)) r h k).mono
        (Finset.union_subset_union le_rfl Finset.subset_union_left)
    · exact (hZ₂' Z₀ E hE hCt (fun p hp => hH p (List.mem_append_right _ hp)) r h k).mono
        (Finset.union_subset_union le_rfl Finset.subset_union_right)
  | Dedup q ih =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.1 hr
    exact GenValue.tokHit_inl _ _ _
  | Diff q₁ q₂ ih₁ ih₂ =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.1 hr
    exact GenValue.tokHit_inl _ _ _
  | Explode k hk q ih =>
    intro _ _ hx
    exact absurd hx (by simp [AggQueryIn.noExplode])
  | Retag hk q ih =>
    intro hu hsig hex ρc HK hwk hF
    obtain ⟨B, hB'⟩ := ih (by simpa [AggQueryIn.usesOnly] using hu)
      (by simpa [AggQueryIn.inSig] using hsig) (by simpa [AggQueryIn.noExplode] using hex) hwk
      (fun x hx => hF x (by simpa [AggQueryIn.allConsts] using hx))
    refine ⟨B, fun d hD γ C hγ hC => ?_⟩
    obtain ⟨Z, hZ, hZ'⟩ := hB' d hD γ C hγ hC
    refine ⟨Z, hZ, fun Z₀ E hE hCt hH r hr k => ?_⟩
    simp only [AggQueryIn.evaluate] at hr
    exact hZ' Z₀ E hE hCt hH r hr k
  | Mu s q₀ q₁ ih₀ ih₁ =>
    intro hu hsig hex ρc HK hwk hF
    obtain ⟨B₀, hB₀⟩ := ih₀ hu.2.1 hsig.1 hex.1 hwk.1
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inl hx))
    obtain ⟨B₁, hB₁⟩ := ih₁ hu.2.2 hsig.2 hex.2 hwk.2
      (fun x hx => hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inr hx))
    refine ⟨B₀ + B₁, fun d hD γ C hγ hC => ?_⟩
    obtain ⟨Z₁, hZ₁, hZ₁'⟩ := hB₀ d hD γ C hγ hC
    obtain ⟨Z₂, hZ₂, hZ₂'⟩ := hB₁ d hD γ C hγ hC
    refine ⟨Union.union Z₁ Z₂, (Finset.card_union_le _ _).trans (Nat.add_le_add hZ₁ hZ₂),
      fun Z₀ E hE hCt hH r hr => ?_⟩
    simp only [AggQueryIn.evaluate, muSumFix] at hr
    refine muSum_forall (fun r => ∀ k, GenValue.TokHit y (Union.union Z₀ (Union.union Z₁ Z₂))
        (r.fst k)) _ (fun X hX r' hr' k => ?_) _ _ (fun r' hr' k => ?_) r hr
    · have h := hZ₂' (Union.union Z₀ (Union.union Z₁ Z₂)) (E.assignHole s X) hE
        (fun k => (hCt k).mono Finset.subset_union_left)
        (fun p hp r'' hr'' k => by
          rw [List.mem_singleton] at hp
          subst hp
          rw [EvalEnv.assignHole_holes_self] at hr''
          exact hX r'' hr'' k) r' hr' k
      exact h.mono (Finset.union_subset le_rfl
        (Finset.subset_union_right.trans Finset.subset_union_right))
    · exact (hZ₁' Z₀ E hE hCt (fun p hp => absurd hp List.not_mem_nil) r' hr' k).mono
        (Finset.union_subset_union le_rfl Finset.subset_union_left)
  | MuSet s q₀ q₁ ih₀ ih₁ =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨p, -, rfl⟩ := Multiset.mem_map.1 hr
    exact GenValue.tokHit_inl _ _ _
  | @Gamma cG m n₁ n₂ lab rd is ts fs q keep ord ih =>
    intro hu hsig hex ρc HK hwk hF
    refine ⟨(Union.union (Union.union Fv V) {0} : Finset T).card ^ n₁,
      fun d hD γ C hγ hC => ?_⟩
    obtain ⟨E₀, hE₀⟩ : ∃ E₀ : EvalEnv T K, E₀ = ({} : EvalEnv T K).withCtx C := ⟨_, rfl⟩
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : AnnotatedRelation T K m,
        r₀ = (q.evaluate d γ E₀).map GenRow.toAnnotated := ⟨_, rfl⟩
    obtain ⟨ps, hps⟩ : ∃ ps : List (T ⊕ FamId T), ps = E₀.paramKey rd γ := ⟨_, rfl⟩
    refine ⟨(Fintype.piFinset (fun _ : Fin n₁ => Union.union (Union.union Fv V) {0})).image
        (fun g => (⟨lab, ps, List.ofFn g, (Having.havingGroupOrd is ord r₀ g).findIdx
          (fun p => decide (p.2 = y))⟩ : OccId T)), ?_, fun Z₀ E hE hCt hH r hr k => ?_⟩
    · refine (Finset.card_image_le).trans (le_of_eq ?_)
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hq : q.evaluate d γ E = q.evaluate d γ E₀ :=
      AggQueryIn.evaluate_congr_holes q d γ (fun p hp => absurd hp List.not_mem_nil)
        (by rw [hE, hE₀, EvalEnv.ctxAt_withCtx])
    have hpk : E.paramKey rd γ = ps := by
      rw [hps, EvalEnv.paramKey, EvalEnv.paramKey, hE, hE₀, EvalEnv.ctxAt_withCtx]
    simp only [AggQueryIn.evaluate] at hr
    rw [hq, ← hr₀, hpk] at hr
    obtain ⟨kv, -, rfl⟩ := Multiset.mem_map.1 hr
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · dsimp only
      erw [Fin.append_left]
      exact GenValue.tokHit_inl _ _ _
    · dsimp only
      erw [Fin.append_right]
      cases hkj : keep j with
      | some φ => exact GenValue.tokHit_of_not_tok _ _ _ (fun a h => by cases h)
      | none =>
        intro a ha
        simp only [AggTok.setFam, Option.getD_some] at ha
        rw [← AggTok.tok.inj (Sum.inr.inj ha)]
        refine (AggValue.hitBy_listing y _ (fs j) (ts j) _ γ false _ lab ps _ ?_).mono
          Finset.subset_union_right
        rintro ⟨p, hp, hpy⟩
        refine Finset.mem_image.2 ⟨kv.fst, Fintype.mem_piFinset.2 (fun i => ?_), rfl⟩
        rw [Having.mem_havingGroupOrd, ← Multiset.mem_coe, Having.havingGroup_coe] at hp
        obtain ⟨hp, hpk'⟩ := Multiset.mem_filter.1 hp
        rw [← hpk' i]
        rw [hr₀] at hp
        obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.1 hp
        have hreg := AggQueryIn.evaluate_conform q d r' (hE₀ ▸ hr') (is i)
        cases hv : r'.fst (is i) with
        | inr x =>
          rw [hv] at hreg
          exact absurd hreg (by simp [GenValue.kindOf, ColKind.allReg, ColKind.base])
        | inl v =>
          have hval : (GenRow.toAnnotated r').fst (is i) = v := by
            simp [GenRow.toAnnotated, GenRow.plainTuple, hv, AggValue.collapseSum]
          rw [hval]
          have hFq : ∀ x ∈ q.allConsts, x ∈ Fv := fun x hx =>
            hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inr hx)
          exact AggQueryIn.yrow_mem y hB Fv V hyV q hsig.2.2.2 hex hwk.2 hFq d hD γ C hγ hC
            (hE₀ ▸ hr') hpy hv
  | @GammaScalar cG m n₂ lab rd ts fs q ord ih =>
    intro hu hsig hex ρc HK hwk hF
    refine ⟨1, fun d hD γ C hγ hC => ?_⟩
    obtain ⟨E₀, hE₀⟩ : ∃ E₀ : EvalEnv T K, E₀ = ({} : EvalEnv T K).withCtx C := ⟨_, rfl⟩
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : AnnotatedRelation T K m,
        r₀ = (q.evaluate d γ E₀).map GenRow.toAnnotated := ⟨_, rfl⟩
    obtain ⟨ps, hps⟩ : ∃ ps : List (T ⊕ FamId T), ps = E₀.paramKey rd γ := ⟨_, rfl⟩
    refine ⟨{(⟨lab, ps, [], (Having.havingGroupOrd (fun k : Fin 0 => k.elim0) ord r₀
        (fun k : Fin 0 => k.elim0)).findIdx (fun p => decide (p.2 = y))⟩ : OccId T)},
      by simp, fun Z₀ E hE hCt hH r hr k => ?_⟩
    have hq : q.evaluate d γ E = q.evaluate d γ E₀ :=
      AggQueryIn.evaluate_congr_holes q d γ (fun p hp => absurd hp List.not_mem_nil)
        (by rw [hE, hE₀, EvalEnv.ctxAt_withCtx])
    have hpk : E.paramKey rd γ = ps := by
      rw [hps, EvalEnv.paramKey, EvalEnv.paramKey, hE, hE₀, EvalEnv.ctxAt_withCtx]
    simp only [AggQueryIn.evaluate] at hr
    rw [hq, ← hr₀, hpk, Multiset.mem_singleton] at hr
    subst hr
    intro a ha
    simp only [AggTok.setFam, Option.getD_some] at ha
    rw [← AggTok.tok.inj (Sum.inr.inj ha)]
    exact (AggValue.hitBy_listing y _ (fs k) (ts k) _ γ true _ lab ps []
      (fun _ => Finset.mem_singleton_self _)).mono Finset.subset_union_right
  | GammaNest is his p f q ih =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate] at hr
    obtain ⟨g, -, rfl⟩ := Multiset.mem_map.1 hr
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · dsimp only
      erw [Fin.append_left]
      exact GenValue.tokHit_inl _ _ _
    · dsimp only
      erw [Fin.append_right]
      exact GenValue.tokHit_of_not_tok _ _ _ (fun a h => by cases h)
  | ProvSum is his t q ih =>
    intro hu
    exact hu.elim
  | GammaTok is his ts fs a q keep ih =>
    intro hu
    exact hu.elim
  | @Win cW nW mW pW κw lab rd P O o w _ t f q hrr dist keep ih =>
    intro hu hsig hex ρc HK hwk hF
    have hFq : ∀ x ∈ q.allConsts, x ∈ Fv := fun x hx =>
      hF x (by simp only [AggQueryIn.allConsts, Finset.mem_union]; exact Or.inr hx)
    obtain ⟨B, hB'⟩ := ih hu.2 hsig.2.2.2.2 hex hwk.2 hFq
    refine ⟨B + (Union.union (Union.union Fv V) {0} : Finset T).card ^ nW,
      fun d hD γ C hγ hC => ?_⟩
    obtain ⟨Zc, hZc, hZc'⟩ := hB' d hD γ C hγ hC
    obtain ⟨E₀, hE₀⟩ : ∃ E₀ : EvalEnv T K, E₀ = ({} : EvalEnv T K).withCtx C := ⟨_, rfl⟩
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : AnnotatedRelation T K nW,
        r₀ = (q.evaluate d γ E₀).map (GenRow.readAnnotated κw) := ⟨_, rfl⟩
    obtain ⟨ps, hps⟩ : ∃ ps : List (T ⊕ FamId T), ps = E₀.paramKey rd γ := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : AnnotatedTuple T K nW → AnnotatedTuple T K nW → Bool,
        e = fun a b => @decide (a = b) (ValueFrame.annotatedTupleLinearOrder.toDecidableEq a b) :=
      ⟨_, rfl⟩
    have heq : ∀ a b, e a b = true ↔ a = b := fun a b => by
      rw [he]; exact @decide_eq_true_iff _ (ValueFrame.annotatedTupleLinearOrder.toDecidableEq a b)
    obtain ⟨part, hpart⟩ : ∃ part : Tuple T nW → List (AnnotatedTuple T K nW),
        part = fun tt => OrderSpec.sortSeq (Tuple.key O) (fun z : AnnotatedTuple T K nW => z.fst) o
          (sortList (α := AnnotatedTuple T K nW) ((r₀ : Multiset (AnnotatedTuple T K nW)).filter
            (fun z : AnnotatedTuple T K nW => Tuple.key P z.fst = Tuple.key P tt))) := ⟨_, rfl⟩
    refine ⟨Union.union Zc ((Fintype.piFinset
        (fun _ : Fin nW => Union.union (Union.union Fv V) {0})).image
        (fun tt => (⟨lab, ps, List.ofFn (Tuple.key P tt), (part tt).findIdx (e (tt, y))⟩
          : OccId T))), ?_, fun Z₀ E hE hCt hH r hr k => ?_⟩
    · refine (Finset.card_union_le _ _).trans (Nat.add_le_add hZc ((Finset.card_image_le).trans
        (le_of_eq ?_)))
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hq : q.evaluate d γ E = q.evaluate d γ E₀ :=
      AggQueryIn.evaluate_congr_holes q d γ (fun p hp => absurd hp List.not_mem_nil)
        (by rw [hE, hE₀, EvalEnv.ctxAt_withCtx])
    have hpk : E.paramKey rd γ = ps := by
      rw [hps, EvalEnv.paramKey, EvalEnv.paramKey, hE, hE₀, EvalEnv.ctxAt_withCtx]
    simp only [AggQueryIn.evaluate] at hr
    rw [hq, ← hr₀, hpk] at hr
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hr
    refine Fin.lastCases ?_ (fun i => ?_) k
    · unfold ValueFrame.windowGenRow
      dsimp only
      erw [Fin.snoc_last]
      cases keep with
      | some φ => exact GenValue.tokHit_of_not_tok _ _ _ (fun a h => by cases dist <;> cases h)
      | none =>
        intro a ha
        cases dist with
        | true =>
          simp only [AggTok.setFam, ite_true, Option.getD_none,
            ValueFrame.tokenOfDist] at ha
          rw [← AggTok.tok.inj (Sum.inr.inj ha)]
          rintro ⟨p, hp, -⟩
          simp [AggValue.mergeByValue] at hp
        | false =>
          simp only [AggTok.setFam, Bool.false_eq_true, ite_false, Option.getD_some,
            ValueFrame.tokenOfDist] at ha
          rw [← AggTok.tok.inj (Sum.inr.inj ha)]
          -- the occurrences annotated `y` of the frame give identities of the image
          have hZ : ∀ b ∈ ValueFrame.frameListOf (α := AnnotatedTuple T K nW) Prod.fst P O o w r₀
                (GenRow.readAnnotated κw x), b.2 = y →
              (⟨lab, ps, List.ofFn (Tuple.key P (GenRow.readAnnotated κw x).fst),
                (part (GenRow.readAnnotated κw x).fst).findIdx (e b)⟩ : OccId T)
                ∈ Union.union Zc ((Fintype.piFinset
                  (fun _ : Fin nW => Union.union (Union.union Fv V) {0})).image
                  (fun tt => (⟨lab, ps, List.ofFn (Tuple.key P tt),
                    (part tt).findIdx (e (tt, y))⟩ : OccId T))) := by
            intro b hb hby
            have hxr : GenRow.readAnnotated κw x ∈ r₀ := by
              rw [hr₀]; exact Multiset.mem_map_of_mem _ (hq ▸ hx)
            have hbr : b ∈ r₀
                ∧ Tuple.key P b.fst = Tuple.key P (GenRow.readAnnotated κw x).fst := by
              rcases mem_frameListOf_key (α := AnnotatedTuple T K nW) Prod.fst P O o w _ _ b hb
                with rfl | h
              · exact ⟨hxr, rfl⟩
              · exact h
            refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨b.fst, ?_, ?_⟩)
            · rw [Fintype.mem_piFinset]
              intro j
              have hb0 := hbr.1
              rw [hr₀] at hb0
              obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.1 hb0
              exact AggQueryIn.readAnnotated_yrow_mem y hB Fv V hyV q hsig.2.2.2.2 hex hwk.2 hFq
                d hD γ C hγ hC (hE₀ ▸ hr') hby j
            · have hb' : (b.fst, y) = b := Prod.ext rfl hby.symm
              rw [hpart]
              dsimp only
              rw [hbr.2, hb']
          unfold ValueFrame.tokenOf
          split
          · have := AggValue.hitBy_frame y _ f t
              (ValueFrame.frameListOf (α := AnnotatedTuple T K nW) Prod.fst P O o w r₀
                (GenRow.readAnnotated κw x)) γ false
              (FamId.mk lab (List.ofFn (GenRow.readAnnotated κw x).fst) ps 0 []) lab ps
              (List.ofFn (Tuple.key P (GenRow.readAnnotated κw x).fst))
              (part (GenRow.readAnnotated κw x).fst) e heq hZ
            refine AggValue.HitBy.mono ?_ Finset.subset_union_right
            subst hpart he
            exact this
          · have := AggValue.hitBy_frame y _ f t
              (ValueFrame.frameListOf (α := AnnotatedTuple T K nW) Prod.fst P O o w r₀
                (GenRow.readAnnotated κw x)) γ true
              (FamId.mk lab (List.ofFn (GenRow.readAnnotated κw x).fst) ps 0 []) lab ps
              (List.ofFn (Tuple.key P (GenRow.readAnnotated κw x).fst))
              (part (GenRow.readAnnotated κw x).fst) e heq hZ
            refine AggValue.HitBy.mono ?_ Finset.subset_union_right
            subst hpart he
            exact this
    · unfold ValueFrame.windowGenRow
      dsimp only
      erw [Fin.snoc_castSucc]
      exact (hZc' Z₀ E hE hCt (fun p hp => absurd hp List.not_mem_nil) x (hq ▸ hx) i).mono
        (Finset.union_subset_union le_rfl Finset.subset_union_left)
  | WinExpr P O o ws ts fs g q keeps ih =>
    intro _ _ _ ρc HK _ _
    refine ⟨0, fun d _ γ C _ _ => ⟨∅, by simp, fun Z₀ E _ _ _ r hr k => ?_⟩⟩
    simp only [AggQueryIn.evaluate, OccFam.toMultiset] at hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hr
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · dsimp only
      erw [Fin.snoc_last]
      exact GenValue.tokHit_of_not_tok _ _ _ (fun a h => by cases h)
    · dsimp only
      erw [Fin.snoc_castSucc]
      exact GenValue.tokHit_inl _ _ _

end Bound

/-! ## The witness -/

section Witness

/-- **Boolean functions of two variables**: `y` (`true`) and `x` (`false`).
`δ` is the identity, and the two variables are incomparable. -/
abbrev BoolXY := BoolFunc Bool

open Classical in
noncomputable instance : HasAltLinearOrder BoolXY := ⟨linearOrderOfSTO WellOrderingRel⟩

/-- The variable annotating the one row of `S`. -/
def yv : BoolXY := BoolFunc.var true

/-- The variable annotating every row of `R`. -/
def xv : BoolXY := BoolFunc.var false

theorem yv_not_le_xv : ¬ yv ≤ xv := fun h => by
  have := h (fun b => b)
  simp [yv, xv, BoolFunc.var] at this
  exact absurd this (by decide)

theorem yv_ne_zero : yv ≠ 0 := fun h => by
  have := congrFun h (fun b => b)
  simp [yv, BoolFunc.var] at this

/-- **The instance of size `n`**: `R` holds `2` to `n + 1`, each annotated
`x`, and `S` holds `1`, annotated `y`. -/
def dApply (n : ℕ) : AnnotatedDatabase ℕ BoolXY :=
  AnnotatedDatabase.assign "R"
    ((((Multiset.range n).map (fun i => (((fun _ => i + 2) : Tuple ℕ 1), xv)))
      : Multiset (AnnotatedTuple ℕ BoolXY 1)) : AnnotatedRelation ℕ BoolXY 1)
    (AnnotatedDatabase.assign "S"
      (({(((fun _ => 1) : Tuple ℕ 1), yv)} : Multiset (AnnotatedTuple ℕ BoolXY 1))
        : AnnotatedRelation ℕ BoolXY 1) [])

/-- **The right side**: the count of the rows of `S` below the parameter. -/
def applyRight : AggQueryIn ℕ 1 1 (fun _ => ColKind.agg) :=
  AggQueryIn.GammaScalar (lab := 1) (rd := fun _ => true)
    (fun _ => TermIn.index 0) (fun _ => SeqAggFunc.count)
    (AggQueryIn.Sel (GenPredIn.cmp CompOp.lt (TermGIn.index 0 rfl) (TermGIn.outer 0))
      (AggQueryIn.Rel 1 "S"))

/-- **`R ⊳ γ_∅[count](ϕ_{#1 < u}(S))`.** -/
def applyWitness : AggQuery ℕ 2 (Fin.append (ColKind.allReg 1) (fun _ : Fin 1 => ColKind.agg)) :=
  AggQueryIn.Apply (c := 0) (n₁ := 1) (n₂ := 1) (AggQueryIn.Rel 1 "R")
    (applyRight : AggQueryIn ℕ (1 + 0) 1 (fun _ => ColKind.agg))

theorem xv_ne_zero : xv ≠ 0 := fun h => by
  have := congrFun h (fun b => !b)
  simp [xv, BoolFunc.var] at this

/-- **The selection keeps the row of `S`** where the parameter is at least
`2`. -/
theorem evaluate_applySel (n u : ℕ) (hu : 2 ≤ u) (E : EvalEnv ℕ BoolXY) (γ : Fin 1 → ℕ)
    (hγ : γ 0 = u) :
    (AggQueryIn.Sel (GenPredIn.cmp CompOp.lt (TermGIn.index 0 rfl) (TermGIn.outer 0))
      (AggQueryIn.Rel 1 "S") : AggQueryIn ℕ 1 1 (ColKind.allReg 1)).evaluate (dApply n) γ E
      = {GenRow.ofAnnotated (((fun _ => 1) : Tuple ℕ 1), yv)} := by
  simp only [AggQueryIn.evaluate, GenPredIn.hasAggAtom, Bool.false_eq_true, ite_false]
  rw [show (dApply n).find 1 "S" = some (({(((fun _ => 1) : Tuple ℕ 1), yv)}
      : Multiset (AnnotatedTuple ℕ BoolXY 1)) : AnnotatedRelation ℕ BoolXY 1) by
    simp [dApply, AnnotatedDatabase.find_assign, AnnotatedDatabase.find_assign_of_ne]]
  show Multiset.filter _ (Multiset.map GenRow.ofAnnotated _) = _
  rw [Multiset.map_singleton, Multiset.filter_singleton, ite_eq_left_iff.2]
  intro hn
  exact absurd (by
    show (GenPredIn.cmp CompOp.lt (TermGIn.index 0 rfl) (TermGIn.outer 0) :
      GenPredIn ℕ 1 (ColKind.allReg 1)).eval3 (fun _ => Sum.inl 1) γ = Kleene.true
    simp only [GenPredIn.eval3, CompOp.eval3_eq_true_iff_noNulls]
    show 1 < γ 0
    omega) hn

/-- **The source's row for the parameter `i + 2`**: annotated `x`, its count
holding the one occurrence `1 : y`, whose identity records the parameter. -/
theorem applyWitness_row (n i : ℕ) (hi : i < n) :
    ∃ r ∈ applyWitness.evaluate (dApply n) (fun k => k.elim0) {}, r.snd.finalize ≠ 0 ∧
      ∃ a : AggValue ℕ BoolXY, r.fst (Fin.natAdd 1 (0 : Fin 1)) = Sum.inr (AggTok.tok a)
        ∧ a.zeroOccs.oids = [⟨1, [Sum.inl (i + 2)], [], 0⟩]
        ∧ ∃ v, a.zeroOccs.occs = [(v, yv)] := by
  -- the row of `R` for `i + 2`
  obtain ⟨x, hx⟩ : ∃ x : GenRow ℕ BoolXY 1,
      x = GenRow.ofAnnotated (((fun _ => i + 2) : Tuple ℕ 1), xv) := ⟨_, rfl⟩
  have hxR : x ∈ (AggQueryIn.Rel 1 "R" : AggQueryIn ℕ 0 1 (ColKind.allReg 1)).evaluate
      (dApply n) (fun k => k.elim0) {} := by
    simp only [AggQueryIn.evaluate, dApply, AnnotatedDatabase.find_assign]
    rw [hx]
    exact Multiset.mem_map_of_mem _ (Multiset.mem_map.2 ⟨i, Multiset.mem_range.2 hi, rfl⟩)
  -- the right side read at that row
  obtain ⟨γ', hγ'⟩ : ∃ γ' : Fin (1 + 0) → ℕ,
      γ' = Fin.append (GenRow.plainTuple x.fst) (fun k : Fin 0 => k.elim0) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E' : EvalEnv ℕ BoolXY,
      E' = ({} : EvalEnv ℕ BoolXY).withCtx
        (Fin.append x.fst (({} : EvalEnv ℕ BoolXY).ctxAt 0 (fun k => k.elim0))) := ⟨_, rfl⟩
  have hγ0 : γ' 0 = i + 2 := by
    rw [hγ', hx]
    rfl
  have hsel := evaluate_applySel n (i + 2) (by omega) E' γ' hγ0
  obtain ⟨U, hU⟩ : ∃ U : List (AnnotatedTuple ℕ BoolXY 1),
      U = Having.havingGroupOrd ((fun k : Fin 0 => k.elim0) : Tuple (Fin 1) 0) GroupOrder.unord
        (((AggQueryIn.Sel (GenPredIn.cmp CompOp.lt (TermGIn.index 0 rfl) (TermGIn.outer 0))
          (AggQueryIn.Rel 1 "S") : AggQueryIn ℕ 1 1 (ColKind.allReg 1)).evaluate (dApply n) γ'
            E').map GenRow.toAnnotated) ((fun k : Fin 0 => k.elim0) : Tuple ℕ 0) := ⟨_, rfl⟩
  have hUeq : U = [(((fun _ => 1) : Tuple ℕ 1), yv)] := by
    have hc : (↑U : Multiset (AnnotatedTuple ℕ BoolXY 1))
        = {(((fun _ => 1) : Tuple ℕ 1), yv)} := by
      rw [hU, Having.havingGroupOrd_unord, Having.havingGroup_coe, hsel, Multiset.map_singleton,
        GenRow.toAnnotated_ofAnnotated]
      exact Multiset.filter_eq_self.2 (fun p _ k => k.elim0)
    exact Multiset.coe_eq_singleton.1 hc
  have hps : E'.paramKey (fun _ => true) γ' = [Sum.inl (i + 2)] := by
    rw [hE', EvalEnv.paramKey, EvalEnv.ctxAt_withCtx, hx]
    rfl
  -- the row the apply builds
  refine ⟨⟨Fin.append (n := 1) x.fst (fun j : Fin 1 => Sum.inr ((AggTok.tok (AggValue.ofScalarGroup
      SeqAggFunc.count (TermIn.index 0) U γ')).setFam (.mk 1 [] [Sum.inl (i + 2)] j [])
      (some (OccId.listing 1 [Sum.inl (i + 2)] [] U.length)))),
      ⟨x.snd.base * 1, x.snd.pending + 0⟩⟩, ?_, ?_, ?_⟩
  · simp only [applyWitness, AggQueryIn.evaluate]
    refine Multiset.mem_bind.2 ⟨x, hxR, Multiset.mem_map.2 ⟨⟨fun j : Fin 1 =>
      Sum.inr ((AggTok.tok (AggValue.ofScalarGroup SeqAggFunc.count (TermIn.index 0) U γ')).setFam
        (.mk 1 [] [Sum.inl (i + 2)] j []) (some (OccId.listing 1 [Sum.inl (i + 2)] [] U.length))),
      ⟨1, 0⟩⟩, ?_, rfl⟩⟩
    rw [← hγ', ← hE', applyRight, AggQueryIn.evaluate, ← hU, hps]
    exact Multiset.mem_singleton_self _
  · rw [hx]
    simp [GenAnn.finalize, GenRow.ofAnnotated, xv_ne_zero]
  · refine ⟨_, rfl, ?_, ?_⟩
    · simp [AggValue.zeroOccs, AggValue.ofScalarGroup, AggValue.ofGroup, hUeq, OccId.listing,
        yv_ne_zero]
    · exact ⟨(TermIn.index 0 : TermIn ℕ (1 + 0) 1).eval (fun _ => 1) γ', by
        simp [AggValue.zeroOccs, AggValue.ofScalarGroup, AggValue.ofGroup, hUeq, yv_ne_zero]⟩

theorem overSchema_applyWitness : applyWitness.overSchema schemaRS := by
  simp [applyWitness, applyRight, AggQueryIn.overSchema, schemaRS, Schema.ofFn_apply]

theorem usesOnly_applyWitness : applyWitness.usesOnly plainRecOps := by
  simp [applyWitness, applyRight, AggQueryIn.usesOnly, plainRecOps, plainOps, basisDD, basisOps]

theorem inMinimalSig_applyWitness : applyWitness.inMinimalSig SeqAggFunc.count := by
  simp [applyWitness, applyRight, AggQueryIn.inMinimalSig, AggQueryIn.inSig, GenPredIn.noFun,
    TermGIn.noFun, TermIn.noFun]

theorem noExplode_applyWitness : applyWitness.noExplode := by
  simp [applyWitness, applyRight, AggQueryIn.noExplode]

theorem wellKinded_applyWitness :
    applyWitness.wellKinded (ColKind.allReg 0) HoleKinds.empty := by
  simp [applyWitness, applyRight, AggQueryIn.wellKinded, GenPredIn.outerOk, TermGIn.outerOk,
    TermIn.outerOk]
  show ¬ ColKind.reg.base = ColKind.agg
  decide

theorem noRec_applyWitness : applyWitness.noRec := by
  simp [applyWitness, applyRight, AggQueryIn.noRec]

end Witness

/-! ## The row -/

section Row

open Classical

omit [ValueType T] in
/-- **An occurrence a token keeps up to `≈` lies in a set hitting it**: a
token whose occurrences annotated otherwise than `𝟘` are one occurrence,
annotated `y`, has the identity of that occurrence in every set hitting
its occurrences annotated `y`. -/
theorem AggValue.oid_mem_of_zeroOccs {a : AggValue T K} {o : OccId T} {v : T} {y : K}
    {Z : Finset (OccId T)} (ho : a.zeroOccs.oids = [o]) (hv : a.zeroOccs.occs = [(v, y)])
    (hy : y ≠ 0) (hZ : a.HitBy y Z) : o ∈ Z := by
  simp only [AggValue.zeroOccs] at ho hv
  obtain ⟨p, hL, rfl⟩ := List.map_eq_singleton_iff.1 ho
  have hp : p ∈ (a.occs.zip a.oids).filter (fun p => p.1.2 ≠ 0) := by rw [hL]; simp
  obtain ⟨hpz, hp0⟩ := List.mem_filter.1 hp
  have hp1 : p.1 ∈ a.occs.filter (fun o => o.2 ≠ 0) :=
    List.mem_filter.2 ⟨(List.of_mem_zip hpz).1, hp0⟩
  rw [hv, List.mem_singleton] at hp1
  obtain ⟨p', hp', hp'y, hp'Z⟩ := hZ ⟨p, hpz, by rw [hp1]⟩
  have hp'L : p' ∈ (a.occs.zip a.oids).filter (fun p => p.1.2 ≠ 0) :=
    List.mem_filter.2 ⟨hp', by simpa [hp'y] using hy⟩
  rw [hL, List.mem_singleton] at hp'L
  rw [← hp'L]
  exact hp'Z

/-- **The apply row, up to `≈` with occurrence identity**: a set of classes
generating the annotated algebra up to `≈`, over Boolean functions of two
variables, holds the apply. The source `R ⊳ γ_∅[count](ϕ_{#1 < u}(S))` gives
each parameter its own occurrence of the row of `S`, annotated `y`; a query
without an apply hits all its occurrences annotated `y` with a set of
identities bounded by the query (`AggQueryIn.exists_hit`), so it cannot keep
`n` of them apart for `n` past that bound. -/
theorem apply_mem_of_generatesAnnRen {S : Set OpKind}
    (h : GeneratesAnnRen ℕ BoolXY schemaRS SeqAggFunc.count S) : OpKind.apply ∈ S := by
  by_contra hS
  obtain ⟨q', -, hu', hi', hx', hwk', hm⟩ := h applyWitness overSchema_applyWitness
    usesOnly_applyWitness inMinimalSig_applyWitness noExplode_applyWitness
    wellKinded_applyWitness
  -- the bound on the values a row annotated `y` holds
  obtain ⟨e, he⟩ : ∃ e : ℕ → BoolXY, e = fun v => if v = 1 then yv else xv := ⟨_, rfl⟩
  have hB : AggQueryIn.BdClosed (AggQueryIn.leBd (fun _ : ℕ => True) e) :=
    AggQueryIn.leBd_closed (fun _ => rfl) _ _
  have hyV : ∀ v, v ∉ q'.allConsts → AggQueryIn.leBd (fun _ : ℕ => True) e v yv →
      v ∈ ({1} : Finset ℕ) :=
    fun v _ hv => by
      by_contra h1
      rw [Finset.mem_singleton] at h1
      have := hv.2
      rw [he] at this
      simp only [h1, ite_false] at this
      exact yv_not_le_xv this
  obtain ⟨B, hBnd⟩ := AggQueryIn.exists_hit yv hS hB q'.allConsts {1} hyV q' hu' hi' hx' hwk'
    (fun x hx => hx)
  -- the instance of size `B + 1`
  have hD : ∀ (m : ℕ) (s : String) (r : AnnotatedRelation ℕ BoolXY m),
      (dApply (B + 1)).find m s = some r → ∀ a ∈ r, AggQueryIn.TupBd (· ∈ q'.allConsts)
        (AggQueryIn.leBd (fun _ : ℕ => True) e) (a.1, a.2) := by
    intro m s r hr a ha k
    refine Or.inr ⟨trivial, ?_⟩
    by_cases h1 : m = 1 ∧ s = "R"
    · obtain ⟨rfl, rfl⟩ := h1
      rw [dApply, AnnotatedDatabase.find_assign, Option.some.injEq] at hr
      subst hr
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
      show xv ≤ e (i + 2)
      rw [he]
      simp only [show i + 2 ≠ 1 by omega, ite_false]
      exact fun _ => le_rfl
    · rw [dApply, AnnotatedDatabase.find_assign_of_ne _ _ _ _ h1] at hr
      by_cases h2 : m = 1 ∧ s = "S"
      · obtain ⟨rfl, rfl⟩ := h2
        rw [AnnotatedDatabase.find_assign, Option.some.injEq] at hr
        subst hr
        rw [Multiset.mem_singleton.1 ha]
        show yv ≤ e 1
        rw [he]
        simp only [ite_true]
        exact fun _ => le_rfl
      · rw [AnnotatedDatabase.find_assign_of_ne _ _ _ _ h2] at hr
        exact absurd hr (by simp [AnnotatedDatabase.find, AnnotatedDatabase.find.f])
  obtain ⟨Z, hZ, hZ'⟩ := hBnd (dApply (B + 1)) hD (fun k => k.elim0) (fun k => k.elim0)
    (fun k => k.elim0) (fun k => k.elim0)
  have hhit : ∀ r ∈ q'.evaluate (dApply (B + 1)) (fun k => k.elim0), ∀ k,
      GenValue.TokHit yv (Union.union ∅ Z) (r.fst k) :=
    hZ' ∅ {} (funext fun k => k.elim0) (fun k => k.elim0) (fun p hp => absurd hp List.not_mem_nil)
  obtain ⟨-, τ, ϕ, hτ, -, heq⟩ := hm (dApply (B + 1)) (fun k => k.elim0)
    (AggQueryIn.annSettlesAt_of_noRec applyWitness noRec_applyWitness _ _ _)
  -- each parameter gives an identity of `Z`
  have hkey : ∀ i, LT.lt i (B + 1) → ∃ o ∈ Z, τ o = ⟨1, [Sum.inl (i + 2)], [], 0⟩ := by
    intro i hi
    obtain ⟨r, hr, hr0, a, ha, hao, v, hav⟩ := applyWitness_row (B + 1) i hi
    have hmem : ((fun k => GenValue.zeqNorm id id (r.fst k)), r.snd.finalize)
        ∈ GenRow.zeqNorm τ ϕ (q'.evaluate (dApply (B + 1)) (fun k => k.elim0)) := by
      rw [heq]
      exact Multiset.mem_map_of_mem _ (Multiset.mem_filter.2 ⟨hr, hr0⟩)
    obtain ⟨r', hr', hrr⟩ := Multiset.mem_map.1 hmem
    have hcol := congrFun (congrArg Prod.fst hrr) (Fin.natAdd 1 (0 : Fin 1))
    simp only [ha, GenValue.zeqNorm] at hcol
    cases hc : r'.fst (Fin.natAdd 1 (0 : Fin 1)) with
    | inl w => rw [hc] at hcol; simp at hcol
    | inr x =>
      cases x with
      | nest b => rw [hc] at hcol; simp at hcol
      | expr b => rw [hc] at hcol; simp at hcol
      | tok a' =>
        rw [hc] at hcol
        simp only [Sum.inr.injEq, AggTok.tok.injEq] at hcol
        have hoids := congrArg AggValue.oids hcol
        have hoccs := congrArg AggValue.occs hcol
        simp only [AggValue.renameOids] at hoids hoccs
        rw [hao] at hoids
        obtain ⟨o, ho, hτo'⟩ := List.map_eq_singleton_iff.1 hoids
        refine ⟨o, ?_, hτo'⟩
        have := AggValue.oid_mem_of_zeroOccs ho (hoccs.trans hav) yv_ne_zero
          (hhit r' (Multiset.mem_of_mem_filter hr') _ a' hc)
        simpa using this
  -- they are `B + 1` distinct identities of a set of at most `B`
  choose o ho hτo using hkey
  have hinj : Set.InjOn (fun i => if hi : LT.lt i (B + 1) then o i hi else ⟨0, [], [], 0⟩)
      (Finset.range (B + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only [dite_eq_left hi, dite_eq_left hj] at hij
    have := congrArg τ hij
    rw [hτo, hτo] at this
    simpa using this
  have hle := Finset.card_le_card_of_injOn _ (fun i hi => by
    simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢
    simp only [dite_eq_left hi]
    exact ho i hi) hinj
  rw [Finset.card_range] at hle
  omega

end Row

/-! ## The basis theorem up to `≈` with occurrence identity

`≈` with occurrence identity is finer than `≈` by value, so the rows up to
`≈` transfer; the constructions agree with their source row by row,
identities included, so the positive half holds with no renaming; and the
apply row says that no set of classes does without the apply. -/

section Basis

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **An expression read in the world a valuation realizes**, as a filter
of its occurrences. -/
theorem AggExpr.specialize_eq_filter (e : AggExpr T K) (ν : K → Bool) :
    e.specialize ν = e.g (fun j => e.aggs j
      (((e.occs.filter (fun o => ν o.2.1)).filter
        (fun z => z.2.2.1 j && z.2.2.2 j)).map (fun z => z.1 j))) := by
  unfold AggExpr.specialize AggExpr.valOn AggExpr.leafVal
  refine congrArg e.g (funext fun j => congrArg (e.aggs j) ?_)
  rw [AggExpr.leafSeq_eq_filter]
  congr 2
  exact Having.seqOf_filter_positions (fun o => ν o.2.1) e.occs

omit [ValueType T] in
/-- An expression read up to `≈` reads as itself in the world of its
occurrences annotated otherwise than `𝟘`. -/
theorem AggExpr.specialize_zeqNorm (τ : OccId T → OccId T) (φ : FamId T → FamId T)
    (e : AggExpr T K) :
    (e.zeqNorm τ φ).specialize (fun x : K => decide (x ≠ 0))
      = e.specialize (fun x : K => decide (x ≠ 0)) := by
  rw [AggExpr.specialize_eq_filter, AggExpr.specialize_eq_filter]
  refine congrArg e.g (funext fun j => congrArg (e.aggs j) ?_)
  have hz : (e.occs.filter (fun o => o.2.1 ≠ 0)).filter (fun o => decide (o.2.1 ≠ 0))
      = e.occs.filter (fun o => decide (o.2.1 ≠ 0)) := by
    rw [List.filter_filter]
    congr 1
    funext o
    simp
  show (((e.occs.filter (fun o => o.2.1 ≠ 0)).filter _).filter _).map _ = _
  erw [hz]
  rfl

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- A node read in the world a valuation realizes, occurrence by
occurrence. -/
theorem NestInner.specialize_node (ν : K → Bool) (j : ℕ)
    (N : NestNode T K (NestInner T K j)) :
    NestInner.specialize ν (j + 1) (Sum.inr N)
      = N.agg ((N.occs.filter (fun o => ν o.2 = true)).map
          (fun o => NestInner.specialize ν j o.1)) := by
  show N.agg (((N.occs.map (fun o => (o.1, o.2, ν o.2))).filter
      (fun m => m.2.2 = true)).map _) = _
  rw [Multiset.filter_map, Multiset.map_map]
  rfl

omit [ValueType T] in
/-- What an occurrence of a nested value reads, up to `≈`, reads as itself
in the world of its occurrences annotated otherwise than `𝟘`. -/
theorem NestInner.specialize_zeqNorm (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T)) :
    ∀ (j : ℕ) (x : NestInner T K j),
      NestInner.specialize (fun x : K => decide (x ≠ 0)) j (NestInner.zeqNorm τ ϕ j x)
        = NestInner.specialize (fun x : K => decide (x ≠ 0)) j x
  | 0, e => by
    have h := AggExpr.specialize_zeqNorm (K := K) τ (FamId.renameFamily ϕ) e
    unfold AggExpr.specialize at h
    rw [← NestInner.trS_realDec, ← NestInner.trS_realDec] at h
    exact h
  | j + 1, Sum.inl x => NestInner.specialize_zeqNorm τ ϕ j x
  | j + 1, Sum.inr N => by
    show NestInner.specialize _ (j + 1) (Sum.inr _) = _
    rw [NestInner.specialize_node, NestInner.specialize_node]
    show N.agg _ = N.agg _
    refine congrArg N.agg ?_
    rw [Multiset.filter_map, Multiset.map_map, Multiset.filter_filter]
    refine Multiset.map_congr (Multiset.filter_congr fun o _ => ?_) fun o _ => ?_
    · simp
    · exact NestInner.specialize_zeqNorm τ ϕ j o.1

/-- A nested value read up to `≈` reads as itself in the world of its
occurrences annotated otherwise than `𝟘`. -/
theorem NestedValue.specialize_zeqNorm (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T))
    (a : NestedValue T K) :
    (a.zeqNorm τ ϕ).specialize (fun x : K => decide (x ≠ 0))
      = a.specialize (fun x : K => decide (x ≠ 0)) := by
  rw [NestedValue.specialize_eq, NestedValue.specialize_eq]
  show a.agg _ = a.agg _
  refine congrArg a.agg ?_
  show (((a.occs.filter (fun o => o.2 ≠ 0)).map _).filter _).map _ = _
  rw [Multiset.filter_map, Multiset.map_map, Multiset.filter_filter]
  refine Multiset.map_congr (Multiset.filter_congr fun o _ => ?_) fun o _ => ?_
  · simp
  · exact NestInner.specialize_zeqNorm τ ϕ a.lev o.1

/-- **`≈` with occurrence identity reads no less than `≈` by value**: a
column value read in the world of its occurrences annotated otherwise than
`𝟘` is the same once its occurrences annotated `𝟘` are dropped and its
identities renamed. -/
theorem GenValue.zeroSpec_zeqNorm (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T)) (v : GenValue T K) :
    _root_.Sum.elim id (fun a => a.specialize (fun x : K => decide (x ≠ 0)))
        (GenValue.zeqNorm τ ϕ v)
      = _root_.Sum.elim id (fun a => a.specialize (fun x : K => decide (x ≠ 0))) v := by
  rcases v with v | x
  · rfl
  · cases x with
    | tok a =>
      show a.agg (((a.occs.filter (fun o => o.2 ≠ 0)).filter
          (fun o => decide (o.2 ≠ 0))).map Prod.fst)
        = a.agg ((a.occs.filter (fun o => decide (o.2 ≠ 0))).map Prod.fst)
      rw [List.filter_filter]
      congr 3
      funext o
      simp
    | nest a => exact NestedValue.specialize_zeqNorm τ ϕ a
    | expr a => exact AggExpr.specialize_zeqNorm τ _ a

/-- **A result's reading by value is a function of its reading up to `≈`
with occurrence identity**, whatever the renaming. -/
theorem GenRow.zeroNorm_eq_map_zeqNorm {n : ℕ} (τ : OccId T → OccId T)
    (ϕ : ℕ × List T × List (T ⊕ FamId T) → ℕ × List T × List (T ⊕ FamId T))
    (R : Multiset (GenRow T K n)) :
    GenRow.zeroNorm R = (GenRow.zeqNorm τ ϕ R).map
      (fun x => ((GenRow.zeroTuple x.1, x.2) : AnnotatedTuple T K n)) := by
  unfold GenRow.zeroNorm GenRow.zeqNorm
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun r _ => ?_
  simp only [Function.comp_apply]
  congr 1
  funext k
  exact (GenValue.zeroSpec_zeqNorm τ ϕ (r.fst k)).symm

/-- **Two results equivalent up to `≈` with occurrence identity are
equivalent up to `≈` by value.** -/
theorem GenRow.zeroNorm_eq_of_zeqRen {n : ℕ} {R R' : Multiset (GenRow T K n)}
    (h : GenRow.zeqRen R R') : GenRow.zeroNorm R' = GenRow.zeroNorm R := by
  obtain ⟨τ, ϕ, -, -, hτ⟩ := h
  rw [GenRow.zeroNorm_eq_map_zeqNorm τ ϕ R', GenRow.zeroNorm_eq_map_zeqNorm id id R, hτ]

omit [ValueType T] in
/-- **Two evaluations agreeing row by row up to finalization are equivalent
up to `≈` with occurrence identity**, with no renaming: the occurrences and
their identities are the rows' own. -/
theorem GenRow.zeqRen_of_fin {n : ℕ} {A B : Multiset (GenRow T K n)}
    (h : B.map GenRow.fin = A.map GenRow.fin) : GenRow.zeqRen A B := by
  refine ⟨id, id, Function.injective_id, Function.injective_id, ?_⟩
  have hz : ∀ R : Multiset (GenRow T K n), GenRow.zeqNorm id id R
      = ((R.map GenRow.fin).filter (fun x => x.2 ≠ 0)).map
          (fun x => ((fun k => GenValue.zeqNorm id id (x.1 k)), x.2)) := by
    intro R
    unfold GenRow.zeqNorm
    rw [Multiset.filter_map, Multiset.map_map]
    rfl
  rw [hz, hz, h]

variable [HasAltLinearOrder K]

/-- **Generation up to `≈` with occurrence identity is generation up to `≈`
by value.** -/
theorem GeneratesAnnRen.toGeneratesAnnZ {sch : Schema} {cnt : SeqAggFunc T} {S : Set OpKind}
    (h : GeneratesAnnRen T K sch cnt S) : GeneratesAnnZ T K sch cnt S := by
  intro n κ q ho hu hi ha hp
  obtain ⟨q', ho', hu', hi', ha', hp', hm⟩ := h q ho hu hi ha hp
  exact ⟨q', ho', hu', hi', ha', hp', fun d γ hs =>
    ⟨(hm d γ hs).1, GenRow.zeroNorm_eq_of_zeqRen (hm d γ hs).2⟩⟩

/-- **The nine classes generate the annotated algebra up to `≈` with
occurrence identity over every semiring of the class**: the constructions
agree with their source row by row up to finalization
(`exists_annEpsOps_match`), identities included. -/
theorem generatesAnnRen_annEpsOps_of_class (hK : AnnBasisClass K) (sch : Schema)
    (cnt : SeqAggFunc T) : GeneratesAnnRen T K sch cnt annEpsOps := by
  intro n κ q ho hu hi ha hp
  obtain ⟨ch, hnc⟩ :
      ∃ ch, AggQueryIn.NodeCorrect cnt ch (fun _ : AnnotatedDatabase T K => True) := by
    rcases hK with ⟨hδ, hR⟩ | hδ
    · exact ⟨false, AggQueryIn.nodeCorrect_succ cnt hδ hR⟩
    · exact ⟨true, AggQueryIn.nodeCorrect_chain cnt hδ⟩
  obtain ⟨q', ho', hu', hi', ha', hp', hm⟩ :=
    exists_annEpsOps_match sch cnt ch hnc q ho hu hi ha hp
  exact ⟨q', ho', hu', hi', ha', hp', fun d γ hs =>
    ⟨(hm d γ trivial hs).1, GenRow.zeqRen_of_fin (hm d γ trivial hs).2⟩⟩

end Basis

theorem annBasisClass_boolXY : AnnBasisClass BoolXY := Or.inr fun _ => rfl

/-- **No proper subset of the nine classes generates the annotated algebra
up to `≈` with occurrence identity over every semiring of the class**: the
rows up to `≈` by value transfer (`GeneratesAnnRen.toGeneratesAnnZ`). -/
theorem annEpsOps_minimal_in_class_ren {S : Set OpKind} (hS : S ⊆ annEpsOps)
    (h : ∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
      AnnBasisClass K → ∀ sch : Schema, GeneratesAnnRen ℕ K sch SeqAggFunc.count S) :
    S = annEpsOps :=
  annEpsOps_minimal_in_class_approx hS fun K _ _ _ hK sch =>
    GeneratesAnnRen.toGeneratesAnnZ (h K hK sch)

/-- **Every set generating the annotated algebra up to `≈` with occurrence
identity over the class holds the apply**, whatever else it holds: a
product does not replace it (`apply_mem_of_generatesAnnRen`, over Boolean
functions of two variables, a semiring of the class). -/
theorem apply_mem_of_generatesAnnRen_in_class {S : Set OpKind}
    (h : ∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
      AnnBasisClass K → ∀ sch : Schema, GeneratesAnnRen ℕ K sch SeqAggFunc.count S) :
    OpKind.apply ∈ S :=
  apply_mem_of_generatesAnnRen (h BoolXY annBasisClass_boolXY schemaRS)

/-- **The annotated basis theorem up to `≈` with occurrence identity, over
the class**: the nine classes generate the annotated algebra up to `≈` with
occurrence identity over every semiring of `AnnBasisClass`, no proper subset
of them does over all of those semirings, and no set of classes does
without the apply. -/
theorem annEpsOps_isBasis_in_class_ren :
    (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
      AnnBasisClass K → ∀ sch : Schema, GeneratesAnnRen ℕ K sch SeqAggFunc.count annEpsOps)
    ∧ (∀ S ⊆ annEpsOps,
      (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
        AnnBasisClass K → ∀ sch : Schema, GeneratesAnnRen ℕ K sch SeqAggFunc.count S) →
      S = annEpsOps)
    ∧ ∀ S : Set OpKind,
      (∀ (K : Type) [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K],
        AnnBasisClass K → ∀ sch : Schema, GeneratesAnnRen ℕ K sch SeqAggFunc.count S) →
      OpKind.apply ∈ S :=
  ⟨fun _ _ _ _ hK sch => generatesAnnRen_annEpsOps_of_class hK sch _,
    fun _ hS h => annEpsOps_minimal_in_class_ren hS h,
    fun _ h => apply_mem_of_generatesAnnRen_in_class h⟩
