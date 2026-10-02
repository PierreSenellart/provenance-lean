/-
  Released under the MIT license as described in the file LICENSE.
  Authors: Pierre Senellart
-/
import Provenance.AggValue

/-!
# Aggregate expressions

SQL computes on the results of aggregates – `count(*) + 1`,
`x * 100 / sum(x) OVER (…)`, `CASE WHEN sum(x) > 0 THEN … END` – and so
do the ranks. A term that mentions a column of aggregate kind produces a
column of aggregate kind, and what that column carries is a formal
**aggregate expression** `e = g(a₁, …, a_p)`: the function `g` the term
computes, applied to the aggregate values `a₁, …, a_p` of the tuple it
reads. The regular values it reads are constants of `g`.

The worlds are the point. With `U_j` the occurrences of `a_j` and
`V = ⋃_j U_j`, a world of `e` is a subfamily `W ⊆ V` meeting `U_j` for
each *grouped* `a_j` – a scalar one is exempt, its empty world being one
of its worlds – and the value there is
`g(val_{a₁}(W ∩ U₁), …, val_{a_p}(W ∩ U_p))`. Reading one world at a time
is what makes the leaves answer together: two aggregates over the same
group are read over the same occurrences, and an expression of them is
not a function of their values separately.

An occurrence family is shared, so it is stored once: `occs` lists, per
occurrence, the value *every* leaf reads there and the occurrence's
annotation, and `reads` says which occurrences each leaf reads. That is
`V` with its `U_j`, and `covered` says `occs` is no larger than `V`.

`AggExpr.ofValue` embeds a token as the expression of itself, and
`AggExpr.predProv_ofValue` says the embedding changes no reading: the
expression of a token has the token's predicate provenance, in the
token's own convention. Any deterministic function of SQL can be `g`,
since only its value in each world is used.
-/

variable {T K : Type}

/-- **A formal aggregate expression**: a function of the aggregate values
a term reads, over one shared family of occurrences. -/
structure AggExpr (T K : Type) where
  /-- How many aggregate values the expression combines. -/
  arity : ℕ
  /-- The occurrence family `V`: per occurrence, the value each leaf reads
  there and the occurrence's annotation. -/
  occs : List ((Fin arity → T) × K)
  /-- The occurrences `U_j` each leaf reads. -/
  reads : Fin arity → Finset (Fin occs.length)
  /-- The aggregate each leaf reads its sequence with. -/
  aggs : Fin arity → SeqAggFunc T
  /-- Whether each leaf is read in the scalar convention. -/
  scalar : Fin arity → Bool
  /-- The function the term computes. -/
  g : (Fin arity → T) → T
  /-- `occs` is the union of the `U_j` and no larger. -/
  covered : ∀ i, ∃ j, i ∈ reads j

namespace AggExpr

/-- The occurrence annotations, as a function on positions. -/
def anns (e : AggExpr T K) : Fin e.occs.length → K :=
  fun i => (e.occs.get i).snd

/-- The sequence the `j`-th leaf reads in the world `W`: the values it
reads at the occurrences of `W` it reads, in order. -/
def leafSeq (e : AggExpr T K) (j : Fin e.arity)
    (W : Finset (Fin e.occs.length)) : List T :=
  (Having.seqOf e.occs (W ∩ e.reads j)).map (fun o => o.fst j)

/-- The value the `j`-th leaf takes in the world `W`. -/
def leafVal (e : AggExpr T K) (j : Fin e.arity)
    (W : Finset (Fin e.occs.length)) : T :=
  e.aggs j (e.leafSeq j W)

/-- **`W` is a world of the expression**: it meets the occurrences of
every *grouped* leaf. A scalar leaf is exempt – the empty world is one of
its worlds – which is the same case split `AggValue.predProv` and
`predProvScalar` make. -/
def IsWorld (e : AggExpr T K) (W : Finset (Fin e.occs.length)) : Prop :=
  ∀ j, e.scalar j = false → (W ∩ e.reads j).Nonempty

instance (e : AggExpr T K) : DecidablePred e.IsWorld :=
  fun _ => inferInstanceAs (Decidable (∀ _, _ → _))

/-- The value of the expression in the world `W`. -/
def valOn (e : AggExpr T K) (W : Finset (Fin e.occs.length)) : T :=
  e.g (fun j => e.leafVal j W)

/-- The deterministic reading: every occurrence present. -/
def collapse (e : AggExpr T K) : T := e.valOn Finset.univ

/-- **The displayed value**: the value of the expression in the family of
its occurrences that the database as it is keeps – those whose annotation
`hTop` maps to `true`. When every occurrence is annotated by sums and
products of input tokens this is every occurrence, and the displayed value
is the collapse; it is smaller when occurrences come through a difference
or a selection on aggregate values, which are kept for the worlds where
they exist and do not count in what SQL returns. -/
def disp (e : AggExpr T K) (hTop : K → Bool) : T :=
  e.valOn (Finset.univ.filter (fun i => hTop (e.anns i)))

/-- **Predicate provenance of a comparison against an expression**: the
`⊕`-sum, over the worlds of the expression, of the world's annotation
times the characteristic value of the comparison there. -/
def predProv [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (e : AggExpr T K) (op : CompOp) (c : T) : K :=
  ∑ W ∈ Finset.univ.filter (fun W => e.IsWorld W),
    Having.worldAnn e.anns W * Having.chi op (e.valOn W) c

/-- **Predicate provenance of an arbitrary three-valued test**, the
reading a range atom and a null test need: `predProv` is the case of a
comparison against a constant (`predProv_eq_predProvWith`). -/
def predProvWith [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (e : AggExpr T K) (P : T → Kleene) : K :=
  ∑ W ∈ Finset.univ.filter (fun W => e.IsWorld W),
    Having.worldAnn e.anns W * Having.chiOf P (e.valOn W)

/-- A comparison is the test that compares against the constant. -/
theorem predProv_eq_predProvWith [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (e : AggExpr T K) (op : CompOp) (c : T) :
    e.predProv op c = e.predProvWith (fun v => op.eval3 v c) := rfl

/-! ## The expression read as a column

An aggregate column holds one of these, so an expression owes what a
token owes: the convention it is read in, the family it carries, the
value it takes under a valuation of the annotations, and the values it
takes over its worlds. Each is the `AggValue` notion with `IsWorld` in
place of "non-empty if grouped" and the shared family in place of the
token's own. -/

/-- **The convention the expression is read in**: scalar exactly where
every leaf is, since the empty world is a world of the expression only
when no leaf demands an occurrence. -/
def isScalar (e : AggExpr T K) : Bool :=
  (List.finRange e.arity).all e.scalar

/-- The empty world is a world exactly in the scalar convention. -/
theorem isWorld_empty_iff (e : AggExpr T K) :
    e.IsWorld ∅ ↔ e.isScalar = true := by
  unfold IsWorld isScalar
  rw [List.all_eq_true]
  constructor
  · intro h j _
    by_cases hs : e.scalar j = true
    · exact hs
    · exact absurd (h j (by simpa using hs)) (by simp)
  · intro h j hj
    exact absurd (h j (List.mem_finRange j)) (by rw [hj]; exact Bool.false_ne_true)

/-- **The family the expression carries**: the annotations of the shared
occurrences, which is what the supersede test compares and what makes two
columns one family. -/
def annList (e : AggExpr T K) : List K := e.occs.map Prod.snd

/-- **The world a valuation of the annotations realizes**: the
occurrences it keeps. -/
def realizedWorld (e : AggExpr T K) (ν : K → Bool) :
    Finset (Fin e.occs.length) :=
  Finset.univ.filter (fun i => ν (e.anns i))

/-- **The world-faithful reading**: the value in the realized world. -/
def specialize (e : AggExpr T K) (ν : K → Bool) : T :=
  e.valOn (e.realizedWorld ν)

/-- A valuation that keeps every occurrence reads the collapse. -/
theorem specialize_of_forall (e : AggExpr T K) (ν : K → Bool)
    (h : ∀ x : K, ν x = true) : e.specialize ν = e.collapse := by
  unfold specialize collapse realizedWorld
  exact congrArg e.valOn (Finset.filter_true_of_mem (fun i _ => h _))

/-- `Val(e)`: the values the expression takes over its worlds, for a key
reading. -/
def vals [DecidableEq T] (e : AggExpr T K) : Finset T :=
  (Finset.univ.filter (fun W => e.IsWorld W)).image e.valOn

/-- **Reading the expression through a function**: the term `gf(e)`,
which is again an expression over the same family. -/
def postcomp (gf : T → T) (e : AggExpr T K) : AggExpr T K :=
  { e with g := fun v => gf (e.g v) }

@[simp] theorem valOn_postcomp (gf : T → T) (e : AggExpr T K)
    (W : Finset (Fin (postcomp gf e).occs.length)) :
    (postcomp gf e).valOn W = gf (e.valOn W) := rfl

/-- Mapping the annotations leaves the occurrence list's length, hence
the index type of a world, where it was. -/
theorem length_map_occs {K' : Type} (h : K → K') (e : AggExpr T K) :
    e.occs.length = (e.occs.map (fun o => (o.fst, h o.snd))).length := by
  rw [List.length_map]

/-- **The annotation pushforward**: the occurrences keep their values and
their readings, their annotations going through `h`. -/
def mapAnn {K' : Type} (h : K → K') (e : AggExpr T K) : AggExpr T K' where
  arity := e.arity
  occs := e.occs.map (fun o => (o.fst, h o.snd))
  reads := fun j => (e.reads j).map (finCongr (length_map_occs h e)).toEmbedding
  aggs := e.aggs
  scalar := e.scalar
  g := e.g
  covered := fun i => by
    obtain ⟨j, hj⟩ := e.covered ((finCongr (length_map_occs h e)).symm i)
    exact ⟨j, by
      rw [Finset.mem_map]
      exact ⟨_, hj, by simp⟩⟩

/-- The pushforward's occurrence list, by definition. -/
theorem occs_mapAnn {K' : Type} (h : K → K') (e : AggExpr T K) :
    (e.mapAnn h).occs = e.occs.map (fun o => (o.fst, h o.snd)) := rfl

/-- **The pushforward moves no value**: each leaf reads the same sequence
in the transported world, so the expression takes the same value. -/
theorem leafSeq_mapAnn {K' : Type} (h : K → K') (e : AggExpr T K)
    (j : Fin e.arity) (W : Finset (Fin e.occs.length)) :
    (e.mapAnn h).leafSeq j (W.map (finCongr (length_map_occs h e)).toEmbedding)
      = e.leafSeq j W := by
  show (Having.seqOf (e.occs.map (fun o => (o.fst, h o.snd)))
      ((W.map (finCongr (length_map_occs h e)).toEmbedding)
        ∩ (e.reads j).map (finCongr (length_map_occs h e)).toEmbedding)).map
      (fun o => o.fst j)
    = (Having.seqOf e.occs (W ∩ e.reads j)).map (fun o => o.fst j)
  rw [← Finset.map_inter,
    AggValue.seqOf_map (fun o : (Fin e.arity → T) × K => (o.fst, h o.snd))
      e.occs (length_map_occs h e) (W ∩ e.reads j), List.map_map]
  rfl

/-- Hence the value in a world, and the deterministic reading with it. -/
theorem valOn_mapAnn {K' : Type} (h : K → K') (e : AggExpr T K)
    (W : Finset (Fin e.occs.length)) :
    (e.mapAnn h).valOn (W.map (finCongr (length_map_occs h e)).toEmbedding)
      = e.valOn W :=
  congrArg (e.mapAnn h).g
    (funext (fun j => congrArg ((e.mapAnn h).aggs j) (leafSeq_mapAnn h e j W)))

@[simp] theorem collapse_mapAnn {K' : Type} (h : K → K') (e : AggExpr T K) :
    (e.mapAnn h).collapse = e.collapse := by
  unfold collapse
  rw [← valOn_mapAnn h e Finset.univ]
  exact congrArg (e.mapAnn h).valOn (Finset.map_univ_equiv _).symm

/-! ## A token is the expression of itself -/

/-- The expression that reads one aggregate value and returns it. -/
def ofValue (a : AggValue T K) : AggExpr T K where
  arity := 1
  occs := a.occs.map (fun o => ((fun _ : Fin 1 => o.fst), o.snd))
  reads := fun _ => Finset.univ
  aggs := fun _ => a.agg
  scalar := fun _ => a.scalar
  g := fun v => v 0
  covered := fun _ => ⟨0, Finset.mem_univ _⟩

@[simp] theorem arity_ofValue (a : AggValue T K) : (ofValue a).arity = 1 := rfl

@[simp] theorem scalar_ofValue (a : AggValue T K) (j : Fin (ofValue a).arity) :
    (ofValue a).scalar j = a.scalar := rfl

/-- The scalar convention of a token survives the embedding. -/
@[simp] theorem isScalar_ofValue (a : AggValue T K) :
    (ofValue a).isScalar = a.scalar := by
  unfold isScalar
  simp [ofValue, List.finRange_succ]

@[simp] theorem annList_ofValue (a : AggValue T K) :
    (ofValue a).annList = a.occs.map Prod.snd := by
  unfold annList ofValue
  rw [List.map_map]
  rfl

theorem length_ofValue_occs (a : AggValue T K) :
    a.occs.length = (ofValue a).occs.length := (List.length_map _).symm

@[simp] theorem anns_ofValue (a : AggValue T K) (i : Fin a.occs.length) :
    (ofValue a).anns (finCongr (length_ofValue_occs a) i) = a.anns i := by
  show ((a.occs.map (fun o => ((fun _ : Fin 1 => o.fst), o.snd))).get
    (finCongr (length_ofValue_occs a) i)).snd = _
  simp [AggValue.anns]

/-- The embedded token reads, in each world, what the token reads. -/
theorem valOn_ofValue (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    (ofValue a).valOn
        (W.map (finCongr (length_ofValue_occs a)).toEmbedding)
      = a.valOn W := by
  show a.agg ((Having.seqOf (a.occs.map _)
      ((W.map (finCongr (length_ofValue_occs a)).toEmbedding)
        ∩ Finset.univ)).map (fun o => o.fst (0 : Fin 1))) = _
  rw [Finset.inter_univ, AggValue.seqOf_map _ a.occs
    (length_ofValue_occs a) W, List.map_map]
  rfl

/-- A world of the embedded token is a world of the token: every world
where it is read scalar, the non-empty ones where it is not. -/
theorem isWorld_ofValue (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    (ofValue a).IsWorld
        (W.map (finCongr (length_ofValue_occs a)).toEmbedding)
      ↔ (a.scalar = true ∨ W.Nonempty) := by
  constructor
  · intro h
    by_cases hs : a.scalar = true
    · exact Or.inl hs
    · refine Or.inr ?_
      obtain ⟨i, hi⟩ := h ⟨0, by simp⟩ (by simpa using hs)
      obtain ⟨i₀, hi₀, -⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hi).1
      exact ⟨i₀, hi₀⟩
  · rintro (hs | ⟨i, hi⟩) j hj
    · exact absurd hs (by simpa using hj)
    · exact ⟨finCongr (length_ofValue_occs a) i, Finset.mem_inter.mpr
        ⟨Finset.mem_map_of_mem _ hi, Finset.mem_univ _⟩⟩

section PredProv

variable [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]

omit [ValueType T] [DecidableEq K] in
/-- The world annotation of an embedded world is the token's. -/
theorem worldAnn_ofValue (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    Having.worldAnn (ofValue a).anns
        (W.map (finCongr (length_ofValue_occs a)).toEmbedding)
      = Having.worldAnn a.anns W := by
  rw [AggValue.worldAnn_map_finCongr]
  exact congrArg (fun α => Having.worldAnn α W)
    (funext fun i => anns_ofValue a i)

/-- **The embedding changes no reading.** The expression of a token has
the token's predicate provenance, in the convention the token carries:
every world where it is read scalar, the non-empty ones where it is
not. -/
theorem predProv_ofValue (a : AggValue T K) (op : CompOp) (c : T) :
    (ofValue a).predProv op c = a.predProvOf op c := by
  unfold predProv
  rw [Finset.sum_filter]
  cases hs : a.scalar with
  | true =>
    rw [AggValue.predProvOf_of_scalar hs]
    unfold AggValue.predProvScalar
    refine (Fintype.sum_equiv
      (finCongr (length_ofValue_occs a)).finsetCongr
      (fun W => Having.worldAnn a.anns W * Having.chi op (a.valOn W) c)
      _ (fun W => ?_)).symm
    rw [Equiv.finsetCongr_apply,
      ite_eq_left ((isWorld_ofValue a W).mpr (Or.inl hs)),
      worldAnn_ofValue, valOn_ofValue]
  | false =>
    rw [AggValue.predProvOf_of_grouped hs]
    unfold AggValue.predProv
    rw [Finset.sum_filter]
    refine (Fintype.sum_equiv
      (finCongr (length_ofValue_occs a)).finsetCongr
      (fun W => if W.Nonempty then
        Having.worldAnn a.anns W * Having.chi op (a.valOn W) c else 0)
      _ (fun W => ?_)).symm
    rw [Equiv.finsetCongr_apply]
    by_cases hW : W.Nonempty
    · rw [ite_eq_left hW, ite_eq_left ((isWorld_ofValue a W).mpr (Or.inr hW)),
        worldAnn_ofValue, valOn_ofValue]
    · rw [ite_eq_right hW, ite_eq_right (fun hc =>
        hW (((isWorld_ofValue a W).mp hc).resolve_left (by simp [hs])))]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- The embedded token collapses to the token's collapse. -/
theorem collapse_ofValue (a : AggValue T K) :
    (ofValue a).collapse = a.collapse := by
  unfold collapse
  rw [AggValue.collapse_eq_valOn_univ,
    ← Finset.map_univ_equiv (finCongr (length_ofValue_occs a)),
    valOn_ofValue]

omit [ValueType T] [CommSemiringWithMonus K] [DecidableEq K] in
/-- **The displayed value of an embedded token is the token's displayed
value**: `AggValue.specialize`, its reading in the family of occurrences
the valuation realizes. -/
theorem disp_ofValue (a : AggValue T K) (hTop : K → Bool) :
    (ofValue a).disp hTop = a.specialize hTop := by
  unfold disp
  rw [AggValue.specialize_eq_valOn, ← valOn_ofValue]
  refine congrArg (ofValue a).valOn ?_
  ext j
  constructor
  · intro hj
    obtain ⟨hj', hmem⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_map.mpr ⟨finCongr (length_ofValue_occs a).symm j, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hj₂ : (ofValue a).anns j
          = a.anns (finCongr (length_ofValue_occs a).symm j) := by
        rw [← anns_ofValue a (finCongr (length_ofValue_occs a).symm j)]
        simp
      rw [← hj₂]
      exact hmem
    · simp
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Function.Embedding.coeFn_mk, anns_ofValue]
    exact (Finset.mem_filter.mp hi).2

end PredProv

/-! ## Unary expressions: a function of one aggregate value -/

/-- **A function of one aggregate value is an aggregate value**: the same
occurrences, read in the same convention, with the aggregate read through
`gf`. This is what a term mentioning one aggregate column produces –
`count(*) + 1`, the ranks – and it is not a shortcut: `valOn_postcomp`
says it reads in each world what the aggregate expression `gf(a)` reads
there, and `IsWorld_ofUnary` that it has the same worlds. -/
def _root_.AggValue.postcomp (gf : T → T) (a : AggValue T K) : AggValue T K :=
  ⟨fun L => gf (a.agg L), a.occs, a.scalar⟩

@[simp] theorem _root_.AggValue.occs_postcomp (gf : T → T) (a : AggValue T K) :
    (a.postcomp gf).occs = a.occs := rfl

@[simp] theorem _root_.AggValue.scalar_postcomp (gf : T → T) (a : AggValue T K) :
    (a.postcomp gf).scalar = a.scalar := rfl

@[simp] theorem _root_.AggValue.anns_postcomp (gf : T → T) (a : AggValue T K) :
    (a.postcomp gf).anns = a.anns := rfl

/-- **The value in a world is the function of the value there**, which is
`val_e(W) = g(val_a(W))` for a unary expression. -/
@[simp] theorem _root_.AggValue.valOn_postcomp (gf : T → T) (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    (a.postcomp gf).valOn W = gf (a.valOn W) := rfl

@[simp] theorem _root_.AggValue.collapse_postcomp (gf : T → T) (a : AggValue T K) :
    (a.postcomp gf).collapse = gf a.collapse := rfl

/-- The unary aggregate expression `gf(a)`, with `gf` where the document
puts it. -/
def ofUnary (gf : T → T) (a : AggValue T K) : AggExpr T K where
  arity := 1
  occs := a.occs.map (fun o => ((fun _ : Fin 1 => o.fst), o.snd))
  reads := fun _ => Finset.univ
  aggs := fun _ => a.agg
  scalar := fun _ => a.scalar
  g := fun v => gf (v (0 : Fin 1))
  covered := fun _ => ⟨0, Finset.mem_univ _⟩

/-- **Post-composing the aggregate is the unary expression**: the two
read the same value in each world. -/
theorem valOn_ofUnary (gf : T → T) (a : AggValue T K)
    (W : Finset (Fin (ofValue (a.postcomp gf)).occs.length)) :
    (ofValue (a.postcomp gf)).valOn W = (ofUnary gf a).valOn W := rfl

/-- … and they have the same worlds, the convention being the token's in
both. -/
theorem isWorld_ofUnary (gf : T → T) (a : AggValue T K)
    (W : Finset (Fin (ofValue (a.postcomp gf)).occs.length)) :
    (ofValue (a.postcomp gf)).IsWorld W ↔ (ofUnary gf a).IsWorld W := Iff.rfl

end AggExpr
