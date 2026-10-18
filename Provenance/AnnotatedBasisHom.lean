/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AnnotatedBasisClass
import Provenance.AggQueryHom

/-!
# The matches of the annotated basis commute with homomorphisms

The query the annotated basis theorem builds over `{∅, Π, σ, apply, γ, win,
μ^⊎, ε, −}` reads no annotation, so one query serves every semiring of a
counter's class (`exists_annEpsOps_matchU`), and it gives the source's
annotated rows wherever the source settles. A homomorphism the source
commutes with therefore commutes with the match too: the match is the
source on both sides. Nothing is asked of the match's syntax – its labels
and recorded read sets may be those a construction copies, which
`AggQueryIn.evaluateAnnotated_hom` would not accept – only of the source.
-/

variable {T : Type} [ValueType T]

/-- **A homomorphism commuting with the source commutes with its match**,
wherever the source settles on both sides. -/
theorem annotatedMatch_hom {K K' : Type} [CommSemiringWithMonus K] [DecidableEq K]
    [HasAltLinearOrder K] [CommSemiringWithMonus K'] [DecidableEq K'] [HasAltLinearOrder K']
    (h : SemiringWithMonusHom K K') {n : ℕ} {κ : Fin n → ColKind} (q q' : AggQuery T n κ)
    (hm : ∀ d : AnnotatedDatabase T K, q.AnnSettlesAt d (fun _ => 0) {} →
      q'.evaluateAnnotated d = q.evaluateAnnotated d)
    (hm' : ∀ d : AnnotatedDatabase T K', q.AnnSettlesAt d (fun _ => 0) {} →
      q'.evaluateAnnotated d = q.evaluateAnnotated d)
    (d : AnnotatedDatabase T K)
    (hq : q.evaluateAnnotated (h.mapAnnotatedDatabase d)
      = SemiringWithMonusHom.mapAnnotatedRelation h (q.evaluateAnnotated d))
    (hs : q.AnnSettlesAt d (fun _ => 0) {})
    (hs' : q.AnnSettlesAt (h.mapAnnotatedDatabase d) (fun _ => 0) {}) :
    q'.evaluateAnnotated (h.mapAnnotatedDatabase d)
      = SemiringWithMonusHom.mapAnnotatedRelation h (q'.evaluateAnnotated d) := by
  rw [hm' _ hs', hq, hm d hs]

/-- **The annotated basis theorem's match commutes with homomorphisms.** For
every query of the annotated algebra in the minimal universe there is one
query over the nine classes which, between any two semirings where the
counter `ch` simulates a set recursion, commutes with every homomorphism
the source commutes with (`AggQueryIn.evaluateAnnotated_hom`), wherever the
source settles on both sides. -/
theorem exists_annEpsOps_match_hom (sch : Schema) (cnt : SeqAggFunc T) (ch : Bool)
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ) (ho : q.overSchema sch)
    (hu : q.usesOnly plainRecOps) (hi : q.inMinimalSig cnt) (ha : q.noExplode)
    (hp : q.wellKinded (ColKind.allReg 0) HoleKinds.empty) :
    ∃ q' : AggQuery T n κ,
      q'.overSchema sch ∧ q'.usesOnly annEpsOps ∧ q'.inMinimalSig cnt ∧ q'.noExplode
        ∧ ∀ {K K' : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
          [CommSemiringWithMonus K'] [DecidableEq K'] [HasAltLinearOrder K']
          (h : SemiringWithMonusHom K K'),
          AggQueryIn.NodeCorrect cnt ch (fun _ : AnnotatedDatabase T K => True) →
          AggQueryIn.NodeCorrect cnt ch (fun _ : AnnotatedDatabase T K' => True) →
          q.labelsDistinct → q.readsRecorded →
          q.sourceCols → q.allFramesContainSelf →
          ∀ d : AnnotatedDatabase T K, q.AnnSettlesAt d (fun _ => 0) {} →
            q.AnnSettlesAt (h.mapAnnotatedDatabase d) (fun _ => 0) {} →
            q'.evaluateAnnotated (h.mapAnnotatedDatabase d)
              = SemiringWithMonusHom.mapAnnotatedRelation h (q'.evaluateAnnotated d) := by
  obtain ⟨q', ho', hu', hi', ha', -, -, -, hm⟩ :=
    exists_annEpsOps_matchU sch cnt ch q ho hu hi ha hp
  refine ⟨q', ho', hu', hi', ha', fun h hn hn' hld hrr hsc hfc d hs hs' => ?_⟩
  refine annotatedMatch_hom h q q'
    (fun d hd => GenRow.map_toAnnotated_of_fin (hm hn d _ trivial hd).2)
    (fun d hd => GenRow.map_toAnnotated_of_fin (hm hn' d _ trivial hd).2)
    d (AggQueryIn.evaluateAnnotated_hom h q hld hrr hsc hfc d hs) hs hs'

/-- **Between two semirings of the support class** – `δ` the support map,
linear recursions settling early: `ℕ`, `ℕ[X]`, the tropical, Viterbi and
Łukasiewicz semirings – the match commutes with every homomorphism the
source commutes with. -/
theorem exists_annEpsOps_match_hom_support (sch : Schema) (cnt : SeqAggFunc T)
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ) (ho : q.overSchema sch)
    (hu : q.usesOnly plainRecOps) (hi : q.inMinimalSig cnt) (ha : q.noExplode)
    (hp : q.wellKinded (ColKind.allReg 0) HoleKinds.empty) :
    ∃ q' : AggQuery T n κ,
      q'.overSchema sch ∧ q'.usesOnly annEpsOps ∧ q'.inMinimalSig cnt ∧ q'.noExplode
        ∧ ∀ {K K' : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
          [CommSemiringWithMonus K'] [DecidableEq K'] [HasAltLinearOrder K']
          (h : SemiringWithMonusHom K K'),
          (∀ a : K, a ≠ 0 → SemiringWithMonus.delta a = 1) → PathSum.SettlesLinear K →
          (∀ a : K', a ≠ 0 → SemiringWithMonus.delta a = 1) → PathSum.SettlesLinear K' →
          q.labelsDistinct → q.readsRecorded →
          q.sourceCols → q.allFramesContainSelf →
          ∀ d : AnnotatedDatabase T K, q.AnnSettlesAt d (fun _ => 0) {} →
            q.AnnSettlesAt (h.mapAnnotatedDatabase d) (fun _ => 0) {} →
            q'.evaluateAnnotated (h.mapAnnotatedDatabase d)
              = SemiringWithMonusHom.mapAnnotatedRelation h (q'.evaluateAnnotated d) := by
  obtain ⟨q', h1, h2, h3, h4, hm⟩ := exists_annEpsOps_match_hom sch cnt false q ho hu hi ha hp
  exact ⟨q', h1, h2, h3, h4, fun h hδ hK hδ' hK' =>
    hm h (AggQueryIn.nodeCorrect_succ cnt hδ hK) (AggQueryIn.nodeCorrect_succ cnt hδ' hK')⟩

/-- **Between two semirings where `δ` is the identity** – the Boolean
algebras, `MinMax` – the match commutes with every homomorphism the source
commutes with. -/
theorem exists_annEpsOps_match_hom_delta_id (sch : Schema) (cnt : SeqAggFunc T)
    {n : ℕ} {κ : Fin n → ColKind} (q : AggQuery T n κ) (ho : q.overSchema sch)
    (hu : q.usesOnly plainRecOps) (hi : q.inMinimalSig cnt) (ha : q.noExplode)
    (hp : q.wellKinded (ColKind.allReg 0) HoleKinds.empty) :
    ∃ q' : AggQuery T n κ,
      q'.overSchema sch ∧ q'.usesOnly annEpsOps ∧ q'.inMinimalSig cnt ∧ q'.noExplode
        ∧ ∀ {K K' : Type} [CommSemiringWithMonus K] [DecidableEq K] [HasAltLinearOrder K]
          [CommSemiringWithMonus K'] [DecidableEq K'] [HasAltLinearOrder K']
          (h : SemiringWithMonusHom K K'),
          (∀ a : K, SemiringWithMonus.delta a = a) → (∀ a : K', SemiringWithMonus.delta a = a) →
          q.labelsDistinct → q.readsRecorded →
          q.sourceCols → q.allFramesContainSelf →
          ∀ d : AnnotatedDatabase T K, q.AnnSettlesAt d (fun _ => 0) {} →
            q.AnnSettlesAt (h.mapAnnotatedDatabase d) (fun _ => 0) {} →
            q'.evaluateAnnotated (h.mapAnnotatedDatabase d)
              = SemiringWithMonusHom.mapAnnotatedRelation h (q'.evaluateAnnotated d) := by
  obtain ⟨q', h1, h2, h3, h4, hm⟩ := exists_annEpsOps_match_hom sch cnt true q ho hu hi ha hp
  exact ⟨q', h1, h2, h3, h4, fun h hδ hδ' =>
    hm h (AggQueryIn.nodeCorrect_chain cnt hδ) (AggQueryIn.nodeCorrect_chain cnt hδ')⟩
