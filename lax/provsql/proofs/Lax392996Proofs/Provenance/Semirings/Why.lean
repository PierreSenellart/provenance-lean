import Lax392996Proofs.Provenance.SemiringWithMonus
import Lax392996Proofs.Provenance.Semirings.BoolFunc
import Lax392996.AnnotatedDatabases
import Lax392996.AnnotatedSemantics
import Lax392996.BooleanFunctions
import Lax392996.Databases
import Lax392996.MultisetSemantics
import Lax392996.ProbabilisticDatabases
import Lax392996.RelationalAlgebra
import Lax392996.RewritingRules
import Lax392996.SemiringsWithMonus
import Lax392996.WhyProvenance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace Lax392996.WhyProvenance.Why
end Lax392996.WhyProvenance.Why

namespace Lax392996Proofs.Foreign.Why
end Lax392996Proofs.Foreign.Why

/-!
# Why-provenance m-semiring `Why[X]`

This file defines the *Why* provenance semiring `Why α = Set (Set α)`.
Elements are sets of subsets of `α` (representing sets of witnesses). Addition
is union of families, and multiplication is pairwise union of witnesses.

`Why α` is idempotent but **not** absorptive when `α` is nonempty. It also
does **not** satisfy left-distributivity of multiplication over monus, contradicting
a claim in [Amsterdamer, Deutch & Tannen, *On the limitations of provenance for
queries with differences*, Table on p. 4][amsterdamer2011limitations].

## References

* [Amsterdamer, Deutch & Tannen, *On the limitations of provenance for queries
  with differences*][amsterdamer2011limitations]
-/

namespace Lax392996.WhyProvenance.Why

open Lax392996Proofs.Foreign.Why in
/-- The support-indicator `δ` of why-provenance: `𝟘` on the empty
witness family, `𝟙` otherwise. The witness-preserving identity choice
(ProvSQL's historical `Why::delta`) violates `delta_absorb` – `Why` is
not absorptive – so `δ` collapses group existence to a bare “exists”. -/
def _root_.Lax392996Proofs.Foreign.Why.deltaInd (a : Lax392996.WhyProvenance.Why α) : Lax392996.WhyProvenance.Why α :=
  ⟨{s | s = ∅ ∧ a.carrier.Nonempty}⟩

end Lax392996.WhyProvenance.Why

namespace Lax392996.WhyProvenance.Why

export Lax392996Proofs.Foreign.Why (deltaInd)

end Lax392996.WhyProvenance.Why

namespace Why
export Lax392996Proofs.Foreign.Why (deltaInd)
end Why

namespace Lax392996.WhyProvenance.Why

open Lax392996Proofs.Foreign.Why in
lemma _root_.Lax392996Proofs.Foreign.Why.deltaInd_zero : Lax392996Proofs.Foreign.Why.deltaInd (0 : Lax392996.WhyProvenance.Why α) = 0 := by
  ext z
  show z ∈ {s | s = ∅ ∧ (∅ : Set (Set α)).Nonempty} ↔ z ∈ (∅ : Set (Set α))
  simp

end Lax392996.WhyProvenance.Why

namespace Lax392996.WhyProvenance.Why

export Lax392996Proofs.Foreign.Why (deltaInd_zero)

end Lax392996.WhyProvenance.Why

namespace Why
export Lax392996Proofs.Foreign.Why (deltaInd_zero)
end Why

namespace Lax392996.WhyProvenance.Why

open Lax392996Proofs.Foreign.Why in
lemma _root_.Lax392996Proofs.Foreign.Why.carrier_nonempty_of_ne {a : Lax392996.WhyProvenance.Why α} (h : a ≠ 0) :
    a.carrier.Nonempty := by
  rcases Set.eq_empty_or_nonempty a.carrier with he | hne
  · exact absurd (by ext z; rw [he]; exact Iff.rfl) h
  · exact hne

end Lax392996.WhyProvenance.Why

namespace Lax392996.WhyProvenance.Why

export Lax392996Proofs.Foreign.Why (carrier_nonempty_of_ne)

end Lax392996.WhyProvenance.Why

namespace Why
export Lax392996Proofs.Foreign.Why (carrier_nonempty_of_ne)
end Why

namespace Lax392996.WhyProvenance.Why

open Lax392996Proofs.Foreign.Why in
lemma _root_.Lax392996Proofs.Foreign.Why.deltaInd_of_ne {a : Lax392996.WhyProvenance.Why α} (h : a ≠ 0) :
    Lax392996Proofs.Foreign.Why.deltaInd a = 1 := by
  ext z
  show z ∈ {s | s = ∅ ∧ a.carrier.Nonempty} ↔ z ∈ ({∅} : Set (Set α))
  simp [Lax392996Proofs.Foreign.Why.carrier_nonempty_of_ne h]

end Lax392996.WhyProvenance.Why

namespace Lax392996.WhyProvenance.Why

export Lax392996Proofs.Foreign.Why (deltaInd_of_ne)

end Lax392996.WhyProvenance.Why

namespace Why
export Lax392996Proofs.Foreign.Why (deltaInd_of_ne)
end Why

namespace Lax392996.WhyProvenance.Why

open Lax392996Proofs.Foreign.Why in
lemma _root_.Lax392996Proofs.Foreign.Why.zsf {a b : Lax392996.WhyProvenance.Why α} (h : a + b = 0) : a = 0 := by
  have hc : a.carrier ∪ b.carrier = (∅ : Set (Set α)) :=
    congrArg Lax392996.WhyProvenance.Why.carrier h
  have hx : a.carrier = ∅ := by
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    have hmem : w ∈ a.carrier ∪ b.carrier := Set.mem_union_left _ hw
    rw [hc] at hmem
    exact hmem
  ext z
  rw [hx]
  exact Iff.rfl

end Lax392996.WhyProvenance.Why

namespace Lax392996.WhyProvenance.Why

export Lax392996Proofs.Foreign.Why (zsf)

end Lax392996.WhyProvenance.Why

namespace Why
export Lax392996Proofs.Foreign.Why (zsf)
end Why

namespace Lax392996.WhyProvenance.Why

open Lax392996Proofs.Foreign.Why in
lemma _root_.Lax392996Proofs.Foreign.Why.one_ne_zero' : (1 : Lax392996.WhyProvenance.Why α) ≠ 0 := by
  intro h
  have := congrArg Lax392996.WhyProvenance.Why.carrier h
  exact Set.singleton_ne_empty (∅ : Set α) this

end Lax392996.WhyProvenance.Why

namespace Lax392996.WhyProvenance.Why

export Lax392996Proofs.Foreign.Why (one_ne_zero')

end Lax392996.WhyProvenance.Why

namespace Why
export Lax392996Proofs.Foreign.Why (one_ne_zero')
end Why

instance _root_.Lax392996Proofs.Foreign.instNontrivialWhy : Nontrivial (Lax392996.WhyProvenance.Why α) := ⟨0, 1, fun h => by
  have h' : (⟨∅⟩ : Lax392996.WhyProvenance.Why α) = ⟨{∅}⟩ := h
  injection h' with h''
  exact Set.singleton_ne_empty _ h''.symm⟩


