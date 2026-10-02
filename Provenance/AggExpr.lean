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
  there, the occurrence's annotation, and which leaves read it.

  The leaf membership sits in the occurrence rather than beside the list
  as a `Finset` of positions. Both say the same thing, and this way a
  recursion over the family carries it along (`AggExpr.exprProvAux`) and
  a reading of one leaf is a `List.filter` of the selected sequence
  rather than an intersection of position sets – so nothing has to be
  transported when the family is rebuilt at the same length. -/
  occs : List ((Fin arity → T) × K × (Fin arity → Bool))
  /-- The aggregate each leaf reads its sequence with. -/
  aggs : Fin arity → SeqAggFunc T
  /-- Whether each leaf is read in the scalar convention. -/
  scalar : Fin arity → Bool
  /-- The function the term computes. -/
  g : (Fin arity → T) → T
  /-- `occs` is the union of the `U_j` and no larger: every occurrence is
  read by some leaf. -/
  covered : ∀ i, ∃ j, (occs.get i).snd.snd j = true

namespace AggExpr

/-- The occurrence annotations, as a function on positions. -/
def anns (e : AggExpr T K) : Fin e.occs.length → K :=
  fun i => (e.occs.get i).snd.fst

/-- **The occurrences `U_j` the `j`-th leaf reads**, read off the family. -/
def reads (e : AggExpr T K) (j : Fin e.arity) : Finset (Fin e.occs.length) :=
  Finset.univ.filter (fun i => (e.occs.get i).snd.snd j = true)

/-- Membership of `U_j` is the occurrence's own flag. -/
@[simp] theorem mem_reads (e : AggExpr T K) (j : Fin e.arity)
    (i : Fin e.occs.length) :
    i ∈ e.reads j ↔ (e.occs.get i).snd.snd j = true := by
  rw [reads, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

/-- The sequence the `j`-th leaf reads in the world `W`: the values it
reads at the occurrences of `W` it reads, in order. -/
def leafSeq (e : AggExpr T K) (j : Fin e.arity)
    (W : Finset (Fin e.occs.length)) : List T :=
  (Having.seqOf e.occs (W ∩ e.reads j)).map (fun o => o.fst j)

/-- **A leaf reads a filter of the selected sequence.** With the leaf
flags in the occurrences, intersecting the world with `U_j` and then
selecting is selecting and then filtering – which is what lets a
recursion over the family read every leaf as it goes. -/
theorem leafSeq_eq_filter (e : AggExpr T K) (j : Fin e.arity)
    (W : Finset (Fin e.occs.length)) :
    e.leafSeq j W
      = ((Having.seqOf e.occs W).filter (fun z => z.snd.snd j)).map
        (fun z => z.fst j) := by
  unfold leafSeq
  rw [show W ∩ e.reads j
      = W.filter (fun i => (e.occs.get i).snd.snd j = true) from by
    ext i
    rw [Finset.mem_inter, mem_reads, Finset.mem_filter]]
  rw [Having.seqOf_filter_inter (fun z => z.snd.snd j) e.occs W]

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
def annList (e : AggExpr T K) : List K := e.occs.map (fun o => o.snd.fst)

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

/-- **A leaf's reading depends only on the values and the leaf flags.**
Stripping the annotations off the family and selecting there is
selecting and then stripping, so two families with the same stripped
list give every leaf the same sequence in corresponding worlds. -/
theorem leafSeq_of_strip {q : ℕ}
    {occs₁ occs₂ : List ((Fin q → T) × K × (Fin q → Bool))}
    (hstrip : occs₁.map (fun z => (z.fst, z.snd.snd))
      = occs₂.map (fun z => (z.fst, z.snd.snd)))
    (aggs : Fin q → SeqAggFunc T) (sc : Fin q → Bool) (g : (Fin q → T) → T)
    (cov₁ : ∀ i, ∃ l, (occs₁.get i).snd.snd l = true)
    (cov₂ : ∀ i, ∃ l, (occs₂.get i).snd.snd l = true)
    (hlen : occs₁.length = occs₂.length) (l : Fin q)
    (W : Finset (Fin occs₁.length)) :
    (AggExpr.mk q occs₁ aggs sc g cov₁).leafSeq l W
      = (AggExpr.mk q occs₂ aggs sc g cov₂).leafSeq l
        (W.map (finCongr hlen).toEmbedding) := by
  have h₁ : occs₁.length
      = (occs₁.map (fun z => (z.fst, z.snd.snd))).length :=
    (List.length_map _).symm
  have h₂ : occs₂.length
      = (occs₂.map (fun z => (z.fst, z.snd.snd))).length :=
    (List.length_map _).symm
  rw [leafSeq_eq_filter, leafSeq_eq_filter]
  show (((Having.seqOf occs₁ W).filter (fun z => z.snd.snd l)).map
      (fun z => z.fst l))
    = (((Having.seqOf occs₂ (W.map (finCongr hlen).toEmbedding)).filter
      (fun z => z.snd.snd l)).map (fun z => z.fst l))
  have key : (Having.seqOf occs₁ W).map (fun z => (z.fst, z.snd.snd))
      = (Having.seqOf occs₂ (W.map (finCongr hlen).toEmbedding)).map
        (fun z => (z.fst, z.snd.snd)) := by
    rw [← AggValue.seqOf_map _ occs₁ h₁ W,
      ← AggValue.seqOf_map _ occs₂ h₂ (W.map (finCongr hlen).toEmbedding),
      Having.seqOf_congr_list hstrip]
    refine congrArg (Having.seqOf _) ?_
    ext x
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨i', hi', rfl⟩ := hi
      exact ⟨Fin.cast hlen i', ⟨i', hi', rfl⟩, by simp⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨i', hi', rfl⟩ := hi
      exact ⟨Fin.cast h₁ i', ⟨i', hi', rfl⟩, by simp⟩
  have hf : ∀ (L₁ L₂ : List ((Fin q → T) × K × (Fin q → Bool))),
      L₁.map (fun z => (z.fst, z.snd.snd))
          = L₂.map (fun z => (z.fst, z.snd.snd)) →
        (L₁.filter (fun z => z.snd.snd l)).map (fun z => z.fst l)
          = (L₂.filter (fun z => z.snd.snd l)).map (fun z => z.fst l) := by
    intro L₁ L₂ hL
    have e₁ : (L₁.filter (fun z => z.snd.snd l)).map (fun z => z.fst l)
        = ((L₁.map (fun z => (z.fst, z.snd.snd))).filter
          (fun w => w.snd l)).map (fun w => w.fst l) := by
      rw [List.filter_map, List.map_map]
      rfl
    have e₂ : (L₂.filter (fun z => z.snd.snd l)).map (fun z => z.fst l)
        = ((L₂.map (fun z => (z.fst, z.snd.snd))).filter
          (fun w => w.snd l)).map (fun w => w.fst l) := by
      rw [List.filter_map, List.map_map]
      rfl
    rw [e₁, e₂, hL]
  exact hf _ _ key

/-- Two families with the same stripped list have the same worlds: the
condition reads the leaf flags and the conventions, not the
annotations. -/
theorem isWorld_of_strip {q : ℕ}
    {occs₁ occs₂ : List ((Fin q → T) × K × (Fin q → Bool))}
    (hstrip : occs₁.map (fun z => (z.fst, z.snd.snd))
      = occs₂.map (fun z => (z.fst, z.snd.snd)))
    (aggs : Fin q → SeqAggFunc T) (sc : Fin q → Bool) (g : (Fin q → T) → T)
    (cov₁ : ∀ i, ∃ l, (occs₁.get i).snd.snd l = true)
    (cov₂ : ∀ i, ∃ l, (occs₂.get i).snd.snd l = true)
    (hlen : occs₁.length = occs₂.length)
    (W : Finset (Fin occs₁.length)) :
    (AggExpr.mk q occs₁ aggs sc g cov₁).IsWorld W
      ↔ (AggExpr.mk q occs₂ aggs sc g cov₂).IsWorld
        (W.map (finCongr hlen).toEmbedding) := by
  have hflag : ∀ (i : Fin occs₁.length) (l : Fin q),
      (occs₁.get i).snd.snd l = (occs₂.get (Fin.cast hlen i)).snd.snd l := by
    intro i l
    have hi₂ : (i : ℕ) < occs₂.length := by rw [← hlen]; exact i.isLt
    have h' := congrArg (fun L => L[(i : ℕ)]?) hstrip
    simp only [List.getElem?_map, List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem hi₂, Option.map_some] at h'
    have heq := Option.some.inj h'
    have hres := congrArg (fun z : (Fin q → T) × (Fin q → Bool) => z.snd l) heq
    simpa only [List.get_eq_getElem, Fin.val_cast] using hres
  constructor
  · intro h l hsc
    obtain ⟨i, hi⟩ := h l hsc
    obtain ⟨hiW, hir⟩ := Finset.mem_inter.mp hi
    refine ⟨Fin.cast hlen i, Finset.mem_inter.mpr
      ⟨Finset.mem_map.mpr ⟨i, hiW, rfl⟩, ?_⟩⟩
    rw [mem_reads] at hir ⊢
    rw [← hflag i l]
    exact hir
  · intro h l hsc
    obtain ⟨j, hj⟩ := h l hsc
    obtain ⟨hjW, hjr⟩ := Finset.mem_inter.mp hj
    obtain ⟨i, hiW, rfl⟩ := Finset.mem_map.mp hjW
    refine ⟨i, Finset.mem_inter.mpr ⟨hiW, ?_⟩⟩
    rw [mem_reads] at hjr ⊢
    rw [hflag i l]
    exact hjr

/-- **`Val(e)` depends only on the values and the leaf flags**, so two
families that differ by a tie-block permutation – occurrences carrying
the same value vector and read by the same leaves – give the same set of
values. This is what lets an aggregate expression be read as a key. -/
theorem vals_congr [DecidableEq T] {q : ℕ}
    {occs₁ occs₂ : List ((Fin q → T) × K × (Fin q → Bool))}
    (aggs : Fin q → SeqAggFunc T) (sc : Fin q → Bool) (g : (Fin q → T) → T)
    (cov₁ : ∀ i, ∃ l, (occs₁.get i).snd.snd l = true)
    (cov₂ : ∀ i, ∃ l, (occs₂.get i).snd.snd l = true)
    (hstrip : occs₁.map (fun z => (z.fst, z.snd.snd))
      = occs₂.map (fun z => (z.fst, z.snd.snd))) :
    (AggExpr.mk q occs₁ aggs sc g cov₁).vals
      = (AggExpr.mk q occs₂ aggs sc g cov₂).vals := by
  have hlen : occs₁.length = occs₂.length := by
    have hc := congrArg List.length hstrip
    simpa only [List.length_map] using hc
  have hval : ∀ W : Finset (Fin occs₁.length),
      (AggExpr.mk q occs₁ aggs sc g cov₁).valOn W
        = (AggExpr.mk q occs₂ aggs sc g cov₂).valOn
          (W.map (finCongr hlen).toEmbedding) :=
    fun W => congrArg g (funext (fun l => congrArg (aggs l)
      (leafSeq_of_strip hstrip aggs sc g cov₁ cov₂ hlen l W)))
  have hback : ∀ W' : Finset (Fin occs₂.length),
      (W'.map (finCongr hlen.symm).toEmbedding).map
          (finCongr hlen).toEmbedding = W' := by
    intro W'
    rw [Finset.map_map]
    ext x
    simp
  ext x
  simp only [vals, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨W, hW, rfl⟩
    exact ⟨W.map (finCongr hlen).toEmbedding,
      (isWorld_of_strip hstrip aggs sc g cov₁ cov₂ hlen W).mp hW,
      (hval W).symm⟩
  · rintro ⟨W', hW', rfl⟩
    refine ⟨W'.map (finCongr hlen.symm).toEmbedding, ?_, ?_⟩
    · refine (isWorld_of_strip hstrip aggs sc g cov₁ cov₂ hlen _).mpr ?_
      rw [hback]
      exact hW'
    · rw [hval, hback]

/-- **Reading the expression through a function**: the term `gf(e)`,
which is again an expression over the same family. -/
def postcomp (gf : T → T) (e : AggExpr T K) : AggExpr T K :=
  { e with g := fun v => gf (e.g v) }

@[simp] theorem valOn_postcomp (gf : T → T) (e : AggExpr T K)
    (W : Finset (Fin (postcomp gf e).occs.length)) :
    (postcomp gf e).valOn W = gf (e.valOn W) := rfl

/-- **The annotation pushforward**: the occurrences keep their values,
their readings and which leaves read them, their annotations going
through `h`. -/
def mapAnn {K' : Type} (h : K → K') (e : AggExpr T K) : AggExpr T K' where
  arity := e.arity
  occs := e.occs.map (fun o => (o.fst, h o.snd.fst, o.snd.snd))
  aggs := e.aggs
  scalar := e.scalar
  g := e.g
  covered := fun i => by
    obtain ⟨j, hj⟩ := e.covered (Fin.cast (by rw [List.length_map]) i)
    refine ⟨j, ?_⟩
    show ((e.occs.map (fun o => (o.fst, h o.snd.fst, o.snd.snd))).get i).snd.snd j
      = true
    simp only [List.get_eq_getElem, List.getElem_map]
    exact hj

/-- Mapping the annotations leaves the occurrence list's length, hence
the index type of a world, where it was. -/
theorem length_map_occs {K' : Type} (h : K → K') (e : AggExpr T K) :
    e.occs.length = (e.mapAnn h).occs.length := by
  show _ = (e.occs.map _).length
  rw [List.length_map]

/-- The pushforward's occurrence list, by definition. -/
theorem occs_mapAnn {K' : Type} (h : K → K') (e : AggExpr T K) :
    (e.mapAnn h).occs
      = e.occs.map (fun o => (o.fst, h o.snd.fst, o.snd.snd)) := rfl

/-- **The pushforward moves no value**: each leaf reads the same sequence
in the transported world, so the expression takes the same value. The
leaf flags travel in the occurrences, so nothing has to be transported
but the world. -/
theorem leafSeq_mapAnn {K' : Type} (h : K → K') (e : AggExpr T K)
    (j : Fin e.arity) (W : Finset (Fin e.occs.length)) :
    (e.mapAnn h).leafSeq j (W.map (finCongr (length_map_occs h e)).toEmbedding)
      = e.leafSeq j W := by
  rw [leafSeq_eq_filter, leafSeq_eq_filter,
    show Having.seqOf (e.mapAnn h).occs
          (W.map (finCongr (length_map_occs h e)).toEmbedding)
        = (Having.seqOf e.occs W).map
          (fun o => (o.fst, h o.snd.fst, o.snd.snd)) from
      AggValue.seqOf_map _ e.occs (length_map_occs h e) W,
    List.filter_map, List.map_map]
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
  occs := a.occs.map
    (fun o => ((fun _ : Fin 1 => o.fst), o.snd, (fun _ : Fin 1 => true)))
  aggs := fun _ => a.agg
  scalar := fun _ => a.scalar
  g := fun v => v 0
  covered := fun i => ⟨0, by
    show ((a.occs.map (fun o => ((fun _ : Fin 1 => o.fst), o.snd,
      (fun _ : Fin 1 => true)))).get i).snd.snd 0 = true
    simp only [List.get_eq_getElem, List.getElem_map]⟩

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

/-- Every leaf of a token's expression reads every occurrence. -/
@[simp] theorem reads_ofValue (a : AggValue T K) (j : Fin (ofValue a).arity) :
    (ofValue a).reads j = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun i => ?_)
  rw [mem_reads]
  simp only [ofValue, List.get_eq_getElem, List.getElem_map]

theorem length_ofValue_occs (a : AggValue T K) :
    a.occs.length = (ofValue a).occs.length := (List.length_map _).symm

@[simp] theorem anns_ofValue (a : AggValue T K) (i : Fin a.occs.length) :
    (ofValue a).anns (finCongr (length_ofValue_occs a) i) = a.anns i := by
  show ((a.occs.map (fun o => ((fun _ : Fin 1 => o.fst), o.snd,
      (fun _ : Fin 1 => true)))).get
    (finCongr (length_ofValue_occs a) i)).snd.fst = _
  simp [AggValue.anns]

/-- The embedded token reads, in each world, what the token reads. -/
theorem valOn_ofValue (a : AggValue T K)
    (W : Finset (Fin a.occs.length)) :
    (ofValue a).valOn
        (W.map (finCongr (length_ofValue_occs a)).toEmbedding)
      = a.valOn W := by
  show a.agg ((Having.seqOf (a.occs.map _)
      ((W.map (finCongr (length_ofValue_occs a)).toEmbedding)
        ∩ (ofValue a).reads (0 : Fin 1))).map (fun o => o.fst (0 : Fin 1))) = _
  rw [reads_ofValue, Finset.inter_univ,
    AggValue.seqOf_map _ a.occs (length_ofValue_occs a) W, List.map_map]
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
    · refine ⟨finCongr (length_ofValue_occs a) i, Finset.mem_inter.mpr
        ⟨Finset.mem_map_of_mem _ hi, ?_⟩⟩
      rw [reads_ofValue]
      exact Finset.mem_univ _

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

/-- **A token's expression reads as the token does, for every test.**
`predProv_ofValue` is the case of a comparison against a constant. -/
theorem predProvWith_ofValue (a : AggValue T K) (P : T → Kleene) :
    (ofValue a).predProvWith P = a.predProvOfWith P := by
  unfold predProvWith
  rw [Finset.sum_filter]
  cases hs : a.scalar with
  | true =>
    rw [AggValue.predProvOfWith, hs]
    simp only [ite_true]
    unfold AggValue.predProvScalarWith
    refine (Fintype.sum_equiv
      (finCongr (length_ofValue_occs a)).finsetCongr
      (fun W => Having.worldAnn a.anns W * Having.chiOf P (a.valOn W))
      _ (fun W => ?_)).symm
    rw [Equiv.finsetCongr_apply,
      ite_eq_left ((isWorld_ofValue a W).mpr (Or.inl hs)),
      worldAnn_ofValue, valOn_ofValue]
  | false =>
    rw [AggValue.predProvOfWith, hs]
    simp only [Bool.false_eq_true, ite_false]
    unfold AggValue.predProvWith
    rw [Finset.sum_filter]
    refine (Fintype.sum_equiv
      (finCongr (length_ofValue_occs a)).finsetCongr
      (fun W => if W.Nonempty then
        Having.worldAnn a.anns W * Having.chiOf P (a.valOn W) else 0)
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
`count(*) + 1`, the ranks – and it is not a shortcut: `valOn_ofUnary`
says it reads in each world what the aggregate expression `gf(a)` reads
there, `isWorld_ofUnary` that it has the same worlds, and
`predProvWith_ofUnary` that a comparison against either has the same
predicate provenance. -/
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
  occs := a.occs.map
    (fun o => ((fun _ : Fin 1 => o.fst), o.snd, (fun _ : Fin 1 => true)))
  aggs := fun _ => a.agg
  scalar := fun _ => a.scalar
  g := fun v => gf (v (0 : Fin 1))
  covered := fun i => ⟨0, by
    simp only [List.get_eq_getElem, List.getElem_map]⟩

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

/-- **The unary expression and the post-composed token are one reading.**
`ofUnary` is the aggregate expression `gf(a)` of the document and
`AggValue.postcomp` is what a term over one aggregate column builds; they
have the same worlds and the same value in each, so a comparison against
either has the same predicate provenance. This is the sense in which
`ProjColIn.aggTerm` is not a shortcut. -/
theorem predProv_ofUnary [ValueType T] [CommSemiringWithMonus K] [DecidableEq K]
    (gf : T → T) (a : AggValue T K) (op : CompOp) (c : T) :
    (ofUnary gf a).predProv op c = (a.postcomp gf).predProvOf op c := by
  rw [← predProv_ofValue (a.postcomp gf) op c]
  rfl

/-- The same for an arbitrary three-valued test, which is what a range
atom and a null test read with. -/
theorem predProvWith_ofUnary [ValueType T] [CommSemiringWithMonus K]
    [DecidableEq K] (gf : T → T) (a : AggValue T K) (P : T → Kleene) :
    (ofUnary gf a).predProvWith P = (a.postcomp gf).predProvOfWith P := by
  rw [← predProvWith_ofValue (a.postcomp gf) P]
  rfl


end AggExpr
