/-
Independently reviewed and integrated UltraMath work: swarm `smwwxbtza`, member `m2`,
direction A. Production integration revision:
`54054b7051903bd4990d0dc78cdfcb61d0676288`, Lean 4.35.0.

The independently rebuilt candidate is `.ultramath/smwwxbtza/m2/CanonTransversal.lean`;
its proof report is `.ultramath/smwwxbtza/m2/Report.md`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Join
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Assembly
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Transport.Main

/-!
# Child-swap transport of the **canonical** atlas event

`AtlasRealization/Transport/Main.lean` proves that the *finite-model* diagram event
`Real.DiagEvent` is invariant under exchanging children, and that its position sum is constant on a
child-swap orbit.  Both statements are about the finite edge index `E` and both are stated with
`[Fintype V]` as soon as the sum is taken.

The canonical countable model (`Config V = Set (Sym2 V)`, witnesses `Finset (Sym2 V)`) has neither
a finite edge type nor a finite vertex type, and the event that matters there is the *canonical*
atlas event `CanonAtlas.CanonAtlasEvent` (`Canonical/Defs.lean`), which is **not** the finite
`Real.DiagEvent` of `AtlasRealization/Defs.lean`: its witnesses are finite sets of ambient edges
and its connectivity is ambient `Connects`.

This file proves the child-swap transport for the canonical event, with

* no `Fintype V` (arbitrary countable vertex type for the sums),
* no `Fintype (Sym2 V)` (the canonical edge type is never finite),
* the *same* physical leaf labels (`y : α → V` is untouched: the transport is a relabelling of
  internal positions and atlas edges only, the leaf-labelling `y` and the root `c` are literally
  unchanged),
* and the *same* edge-witness sets: the transported realization has witness family
  `a ↦ wit (aedgeEquiv.symm a)`, i.e. the same finite sets of ambient open edges, attached to the
  corresponding atlas edge.  Nothing is re-chosen and no edge of `ω` is used twice.

The position reindexing is the explicit `Equiv.arrowCongr I.σ (Equiv.refl V)` (positions are *not*
permuted among vertices; internal vertices keep their physical vertex), which is what makes the
`ℝ≥0∞`-valued position sum invariant without any finiteness assumption: `Equiv.tsum_eq` is applied
to that equivalence and the term is proved equal on the nose.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset

open scoped ENNReal

namespace CanonAtlas

open PercLib.CriticalLRP (Config Connects connSet edgeMeasure)
open PercLib.CriticalLRP.TreeExpansion (RTree)
open PercLib.CriticalLRP.TreeExpansion.Real (AEdge SwapIso nonempty_swapIso srcPos dstPos)

variable {V : Type*} [DecidableEq V]
variable {α : Type*} [DecidableEq α]

/-! ### Transport of a canonical realization -/

/-- **A canonical atlas realization transports along a child swap**, with the same ambient
witness sets attached to the corresponding atlas edges.  This is the canonical counterpart of
`Real.IsRealization.transport`; the proof is the same three fields, but nothing here needs a
finite edge index: the witnesses are `Finset (Sym2 V)` and the connectivity is ambient
`Connects`. -/
theorem isCanonRealization_transport {ω : Config V} {y : α → V} {c : V} {t t' : RTree α}
    (I : SwapIso t y t') {φ : t.IPos → V} {wit : AEdge t → Finset (Sym2 V)}
    (h : IsCanonRealization ω y c φ wit) :
    IsCanonRealization ω y c (I.phi φ) (fun a' => wit (I.aedgeEquiv.symm a')) where
  subset a' := h.subset _
  disjoint := by
    intro a' a'' hne
    exact h.disjoint _ _ fun h' => hne (I.aedgeEquiv.symm.injective h')
  conn := by
    intro a'
    have hc := h.conn (I.aedgeEquiv.symm a')
    rw [← I.srcPos_aedgeEquiv φ c (I.aedgeEquiv.symm a'),
      ← I.dstPos_aedgeEquiv φ (I.aedgeEquiv.symm a'), I.aedgeEquiv.apply_symm_apply] at hc
    exact hc

/-- The inverse direction of `canonAtlasRealization_transport`. -/
theorem isCanonRealization_transport_symm {ω : Config V} {y : α → V} {c : V} {t t' : RTree α}
    (I : SwapIso t y t') {φ : t.IPos → V} {wit' : AEdge t' → Finset (Sym2 V)}
    (h : IsCanonRealization ω y c (I.phi φ) wit') :
    IsCanonRealization ω y c φ (fun a => wit' (I.aedgeEquiv a)) where
  subset a := h.subset _
  disjoint := by
    intro a a' hne
    exact h.disjoint _ _ fun h' => hne (I.aedgeEquiv.injective h')
  conn := by
    intro a
    have hc := h.conn (I.aedgeEquiv a)
    rw [I.srcPos_aedgeEquiv φ c a, I.dstPos_aedgeEquiv φ a] at hc
    exact hc

/-! ### Transport of the canonical atlas event -/

/-- **The canonical atlas event does not see the child order.**  Transporting the position map
along the child-swap datum leaves `CanonAtlasEvent` unchanged, with the *same* finite witness sets:
the two inclusions below are the identity on witnesses up to `aedgeEquiv`, and the leaf labels `y`
and the root `c` are untouched. -/
theorem canonAtlasEvent_eq_of_swapIso {y : α → V} {c : V} {t t' : RTree α}
    (I : SwapIso t y t') (φ : t.IPos → V) :
    CanonAtlasEvent y c t φ = CanonAtlasEvent y c t' (I.phi φ) := by
  ext ω
  constructor
  · rintro ⟨wit, hreal⟩
    exact ⟨fun a' => wit (I.aedgeEquiv.symm a'), isCanonRealization_transport I hreal⟩
  · rintro ⟨wit, hreal⟩
    exact ⟨fun a => wit (I.aedgeEquiv a), isCanonRealization_transport_symm I hreal⟩

/-- For `t'` in the child-swap orbit of `t`, every canonical atlas event of `t` is a canonical
atlas event of `t'` at a transported position. -/
theorem exists_canonAtlasEvent_eq_of_mem_swapFiber {y : α → V} {c : V}
    {t : RTree α} (φ : t.IPos → V) {t' : RTree α} (h : t' ∈ RTree.swapFiber t) :
    ∃ φ' : t'.IPos → V, CanonAtlasEvent y c t φ = CanonAtlasEvent y c t' φ' := by
  obtain ⟨I⟩ := nonempty_swapIso t y h
  exact ⟨I.phi φ, canonAtlasEvent_eq_of_swapIso I φ⟩

/-- **The child-swap invariance of the canonical atlas union.**  The configurations realizing the
atlas of `t` for *some* assignment of internal vertices are exactly those realizing the atlas of
any other plane representative `t'` of the same non-plane tree.  This is the statement that lets
the union bound be taken over one representative per child-swap orbit. -/
theorem iUnion_canonAtlasEvent_eq_of_mem_swapFiber {y : α → V} {c : V} {t t' : RTree α}
    (h : t' ∈ RTree.swapFiber t) :
    (⋃ φ : t.IPos → V, CanonAtlasEvent y c t φ)
      = (⋃ φ' : t'.IPos → V, CanonAtlasEvent y c t' φ') := by
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.iUnion_subset fun φ => ?_
    obtain ⟨φ', hφ⟩ := exists_canonAtlasEvent_eq_of_mem_swapFiber (y := y) (c := c) φ h
    exact hφ ▸ Set.subset_iUnion (fun φ' : t'.IPos → V => CanonAtlasEvent y c t' φ') φ'
  · refine Set.iUnion_subset fun φ' => ?_
    obtain ⟨φ, hφ⟩ := exists_canonAtlasEvent_eq_of_mem_swapFiber (y := y) (c := c) φ'
      (RTree.swapFiber_symm h)
    exact hφ ▸ Set.subset_iUnion (fun φ : t.IPos → V => CanonAtlasEvent y c t φ) φ

/-! ### The `ℝ≥0∞`-valued position sum is constant on a child-swap orbit -/

/-- **Position-sum invariance of the canonical atlas event probability.**

For an arbitrary countable vertex type `V` — in particular with no `Fintype V` and no
`Fintype (Sym2 V)` — the sum over the internal positions of a shape of the probability of the
canonical atlas event is literally the same number for every plane representative of a non-plane
tree.  The reindexing is the explicit position equivalence `Equiv.arrowCongr I.σ (Equiv.refl V)`;
no finiteness of the sum is assumed (and none holds: the position space is infinite as soon as
`V` is), and no term is estimated, each term is *equal* by `canonAtlasEvent_eq_of_swapIso`. -/
theorem tsum_edgeMeasure_canonAtlasEvent_eq_of_mem_swapFiber [Countable V]
    (π : Sym2 V → unitInterval) {y : α → V} {c : V} {t : RTree α} {t' : RTree α}
    (h : t' ∈ RTree.swapFiber t) :
    (∑' φ : t.IPos → V, edgeMeasure π (CanonAtlasEvent y c t φ))
      = ∑' φ' : t'.IPos → V, edgeMeasure π (CanonAtlasEvent y c t' φ') := by
  obtain ⟨I⟩ := nonempty_swapIso t y h
  rw [← Equiv.tsum_eq (Equiv.arrowCongr I.σ (Equiv.refl V))
    (fun φ' : t'.IPos → V => edgeMeasure π (CanonAtlasEvent y c t' φ'))]
  exact tsum_congr fun φ => congrArg (edgeMeasure π) (canonAtlasEvent_eq_of_swapIso I φ)

/-! ### The product of connection probabilities is child-swap invariant -/

namespace Measure

/-- **The per-diagram BK product is invariant under a child swap.**  The product runs over the
atlas edges, and the child-swap correspondence `aedgeEquiv` is a bijection of the atlas edge types
which preserves *both* ends of every atlas edge (`srcPos_aedgeEquiv`, `dstPos_aedgeEquiv`).  Hence
the product over `AEdge t'` at the transported positions is literally the product over
`AEdge t` at the original positions: no factor is created, none is lost, and no estimate is
involved. -/
theorem atlasProduct_eq_of_swapIso {q : ℕ} (π : Sym2 V → unitInterval) (x : V) (f : Fin q → V)
    {t t' : RTree (Fin q)} (I : SwapIso t f t') (φ : t.IPos → V) :
    atlasProduct π x f t' (I.phi φ) = atlasProduct π x f t φ := by
  unfold atlasProduct
  refine (Fintype.prod_equiv I.aedgeEquiv
    (fun a : AEdge t => edgeMeasure π (connSet (srcPos t φ x a) (dstPos t φ f a)))
    (fun a' : AEdge t' =>
      edgeMeasure π (connSet (srcPos t' (I.phi φ) x a') (dstPos t' (I.phi φ) f a')))
    (fun a => ?_)).symm
  rw [I.srcPos_aedgeEquiv φ x a, I.dstPos_aedgeEquiv φ a]

/-- **The `ℝ≥0∞`-valued position sum of the BK product is constant on a child-swap orbit**, for an
arbitrary countable vertex type `V`.  The reindexing is the explicit position equivalence
`Equiv.arrowCongr I.σ (Equiv.refl V)`: an internal vertex keeps its physical vertex, only the
position *index* is moved.  The sum is not assumed finite (and is not finite for infinite `V`). -/
theorem tsum_atlasProduct_eq_of_mem_swapFiber [Countable V] (π : Sym2 V → unitInterval) (x : V)
    {q : ℕ} (f : Fin q → V) {t t' : RTree (Fin q)} (h : t' ∈ RTree.swapFiber t) :
    (∑' φ : t.IPos → V, atlasProduct π x f t φ)
      = ∑' φ' : t'.IPos → V, atlasProduct π x f t' φ' := by
  obtain ⟨I⟩ := nonempty_swapIso t f h
  calc (∑' φ : t.IPos → V, atlasProduct π x f t φ)
      = ∑' φ : t.IPos → V,
          atlasProduct π x f t' (Equiv.arrowCongr I.σ (Equiv.refl V) φ) :=
        tsum_congr fun φ => (atlasProduct_eq_of_swapIso π x f I φ).symm
    _ = ∑' φ' : t'.IPos → V, atlasProduct π x f t' φ' :=
        Equiv.tsum_eq (Equiv.arrowCongr I.σ (Equiv.refl V)) _

/-- The per-diagram canonical BK bound of `CanonAtlas.Measure.canonAtlasEvent_bk`, for an
arbitrary plane shape `t : RTree (Fin q)`.  The bundling of `t` with a labelling proof is *not*
needed for BK: the atlas edge type `AEdge t` is finite for every plane tree, and
`edgeMeasure_bk_atlas` quantifies over arbitrary `t : RTree α`.  This is the form in which the
orbit-representative union bound consumes BK, since the transversal is a `Finset (RTree _)`. -/
theorem edgeMeasure_canonAtlasEvent_le_atlasProduct [Countable V]
    (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (x : V) {q : ℕ} (f : Fin q → V) (t : RTree (Fin q))
    (φ : t.IPos → V) :
    edgeMeasure π (CanonAtlasEvent f x t φ) ≤ atlasProduct π x f t φ := by
  rw [canonAtlasEvent_eq_disjFam]
  exact PercLib.CriticalLRP.edgeMeasure_bk_atlas π hπ f x t φ

/-- `canonAtlasEvent_bk` is the labelled-shape case of
`edgeMeasure_canonAtlasEvent_le_atlasProduct`; recorded to tie the two forms together. -/
theorem canonAtlasEvent_bk' [Countable V] (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) {q : ℕ} (x : V)
    (f : Fin q → V) (t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin q) Finset.univ)
    (φ : (t : PercLib.CriticalLRP.TreeExpansion.RTree (Fin q)).IPos → V) :
    edgeMeasure π (CanonAtlasEvent f x t.1 φ) ≤ atlasProduct π x f t.1 φ :=
  edgeMeasure_canonAtlasEvent_le_atlasProduct π hπ x f t.1 φ

/-- A sum over the subtype of transversal elements of the position sums is the corresponding
finitary sum over the transversal itself.  The outer sum is over a finite index set (a `Finset`
subtype), the inner sums are not assumed finite. -/
theorem tsum_subtype_transversal {q : ℕ}
    (F : (r : RTree (Fin q)) → (r.IPos → V) → ℝ≥0∞) :
    (∑' r : {r : RTree (Fin q) // r ∈ RTree.transversal (Fin q)},
        ∑' φ : r.1.IPos → V, F r.1 φ)
      = ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, F r φ := by
  rw [tsum_fintype]
  exact Finset.sum_coe_sort (RTree.transversal (Fin q))
    (fun r => ∑' φ : r.IPos → V, F r φ)

end Measure

/-! ### Covering by one representative per child-swap orbit -/

/-- A fully labelled shape `IsLabelledShape t univ` is fully labelled in the sense of
`RTree.FullyLabelled` (which is `RTree.LT`'s carrier predicate): the leaf list is injective and
uses every label, so its length is the number of labels.  This is exactly the conversion needed to
feed a `LTon` shape to the orbit machinery of `RTree.transversal`, whose index type is
`RTree.LT`. -/
theorem fullyLabelled_of_isLabelledShape {q : ℕ} {t : RTree (Fin q)}
    (h : PercLib.CriticalLRP.TreeExpansion.Real.IsLabelledShape t Finset.univ) :
    PercLib.CriticalLRP.TreeExpansion.RTree.FullyLabelled t := by
  refine ⟨h.1, ?_⟩
  rw [← List.toFinset_card_of_nodup h.1, h.2, Finset.card_univ, Fintype.card_fin]

/-- The converse: a `RTree.FullyLabelled` shape (`RTree.LT`'s carrier predicate) is a fully
labelled shape in the `LTon` sense.  Only useful to identify the two shape families; the leaf list
is injective and has the cardinality of `Fin q`, so its leaf set is everything. -/
theorem isLabelledShape_of_fullyLabelled {q : ℕ} {t : RTree (Fin q)}
    (h : PercLib.CriticalLRP.TreeExpansion.RTree.FullyLabelled t) :
    PercLib.CriticalLRP.TreeExpansion.Real.IsLabelledShape t Finset.univ := by
  refine ⟨h.1, ?_⟩
  refine Finset.eq_univ_of_card _ ?_
  rw [List.toFinset_card_of_nodup h.1]
  exact h.2

/-- **The canonical cover is attained on a child-swap transversal.**  Every configuration in which
the root `x` is connected to all the terminals `f i` realizes the canonical atlas of some fully
labelled shape `t` at some positions; replacing `t` by the transversal representative `r` of its
child-swap orbit — and the positions by their transport along `SwapIso` — gives a canonical atlas
event of `r` containing the configuration.  This is the canonical counterpart of
`Real.diagEvent_iUnion_subset_transversal`, and it needs **no** `Fintype V` and no `Fintype
(Sym2 V)`: the transport of `canonAtlasEvent_eq_of_swapIso` is an identity of events. -/
theorem canonCover_subset_transversal_iUnion (x : V) {q : ℕ} (f : Fin q → V) :
    CanonCover q f x ⊆
      ⋃ r ∈ RTree.transversal (Fin q), ⋃ φ : r.IPos → V, CanonAtlasEvent f x r φ := by
  intro ω hω
  obtain ⟨⟨⟨t, hshape⟩, φ⟩, hmem⟩ := mem_canonCover.mp hω
  obtain ⟨r, ⟨hrT, hrt⟩, -⟩ :=
    RTree.transversal_spec (α := Fin q) ⟨t, fullyLabelled_of_isLabelledShape hshape⟩
  obtain ⟨φ', hφ'⟩ := exists_canonAtlasEvent_eq_of_mem_swapFiber (y := f) (c := x)
    (t := t) φ (t' := r) (RTree.swapFiber_symm hrt)
  refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hrT, Set.mem_iUnion.mpr ⟨φ', ?_⟩⟩⟩
  rw [← hφ']
  exact hmem

/-! ### The countable union bound over the transversal -/

/-- **Lemma I.4.16's union bound in the canonical countable model, over one representative per
child-swap orbit.**

For an arbitrary countable vertex type `V`, an opening `π` with `π e < 1` for every edge, a root
`x`, `1 ≤ q` terminals `f : Fin q → V`, the probability that `x` is joined to all the terminals is
at most the sum, over one plane representative `r` of each child-swap orbit (the finite transversal
`RTree.transversal (Fin q)`), of the sum over the internal positions `φ` of `r` of the BK product
over the `2q - 1` atlas edges of `r`.

No finite vertex set, no finite edge set, no box and no truncation of the configuration is used:
the cover is the countable union over `(r, φ)` (`CanonAtlas.countable_atlasIndex` for the full
family, and `Finset.countable_toSet`, `Countable` of the position space for the transversal), the
union bound is countable subadditivity (`measure_biUnion_le`, `measure_iUnion_le`), and each
diagram is bounded by the canonical BK law (`edgeMeasure_bk_atlas`).  The factor `2 ^ (q - 1)` of
plane multiplicity is *absent*: the union over all plane shapes is not taken at all, it is replaced
by the union over the transversal through the event identity of `canonAtlasEvent_eq_of_swapIso`. -/
theorem measure_labelEvent_le_sum_transversal_bk [Countable V] (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q) (x : V) (f : Fin q → V) :
    edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, Measure.atlasProduct π x f r φ := by
  classical
  have hcount : (↑(RTree.transversal (Fin q)) : Set (RTree (Fin q))).Countable :=
    (RTree.transversal (Fin q)).countable_toSet
  calc edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f)
      ≤ edgeMeasure π (CanonCover q f x) :=
        MeasureTheory.measure_mono (labelEvent_subset_canonCover x hq f)
    _ ≤ edgeMeasure π
          (⋃ r ∈ RTree.transversal (Fin q), ⋃ φ : r.IPos → V, CanonAtlasEvent f x r φ) :=
        MeasureTheory.measure_mono (canonCover_subset_transversal_iUnion x f)
    _ ≤ ∑' r : {r : RTree (Fin q) // r ∈ RTree.transversal (Fin q)},
          edgeMeasure π (⋃ φ : r.1.IPos → V, CanonAtlasEvent f x r.1 φ) :=
        MeasureTheory.measure_biUnion_le (edgeMeasure π) hcount
          (fun r => ⋃ φ : r.IPos → V, CanonAtlasEvent f x r φ)
    _ ≤ ∑' r : {r : RTree (Fin q) // r ∈ RTree.transversal (Fin q)},
          ∑' φ : r.1.IPos → V, edgeMeasure π (CanonAtlasEvent f x r.1 φ) :=
        ENNReal.tsum_le_tsum fun r => MeasureTheory.measure_iUnion_le _
    _ ≤ ∑' r : {r : RTree (Fin q) // r ∈ RTree.transversal (Fin q)},
          ∑' φ : r.1.IPos → V, Measure.atlasProduct π x f r.1 φ :=
        ENNReal.tsum_le_tsum fun r =>
          ENNReal.tsum_le_tsum fun φ =>
            Measure.edgeMeasure_canonAtlasEvent_le_atlasProduct π hπ x f r.1 φ
    _ = ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, Measure.atlasProduct π x f r φ := by
        exact Measure.tsum_subtype_transversal (fun r φ => Measure.atlasProduct π x f r φ)



/-! ### The exact plane multiplicity: orbit sums in `ℝ≥0∞`

`OrbitCount/Partition.lean` and `OrbitCount/Transversal.lean` prove the orbit decomposition of the
shape sum for `ℝ`-valued functions (that is the setting of the tree weight `RTree.wtL`, which is
`ℝ`-valued and sums over a finite vertex type).  The canonical atlas bound is `ℝ≥0∞`-valued, so the
decomposition is needed over `ℝ≥0∞`; the proofs are the same `Finset` manipulations and are
repeated here rather than transported, because the production statements are monomorphic in `ℝ`.
-/

namespace OrbitSum

open PercLib.CriticalLRP.TreeExpansion (RTree)

variable {α : Type*} [Fintype α] [DecidableEq α] [Fintype (RTree.LT α)]

/-- **The orbit partition sum, over `ℝ≥0∞`.**  Summing a function of the plane tree over the fully
labelled family is the same as summing its orbit sums. -/
theorem sum_LT_eq_sum_orbits_ennreal (g : RTree α → ℝ≥0∞) :
    (∑ t : RTree.LT α, g t.1) = ∑ S ∈ RTree.swapOrbits α, ∑ u ∈ S, g u := by
  have h := Finset.sum_biUnion (s := RTree.swapOrbits α) (t := id) (f := g)
    RTree.swapOrbits_pairwiseDisjoint
  rw [RTree.biUnion_swapOrbits] at h
  rw [Finset.sum_image (s := (Finset.univ : Finset (RTree.LT α)))
    (g := fun t : RTree.LT α => t.val) (f := g) (fun x _ y _ hxy => Subtype.ext hxy)] at h
  have h' : (∑ S ∈ RTree.swapOrbits α, ∑ u ∈ S, g u)
      = ∑ S ∈ RTree.swapOrbits α, ∑ u ∈ id S, g u :=
    Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun u _ => rfl
  rw [h']
  exact h

/-- **The orbit sum of an orbit-invariant function, over `ℝ≥0∞`**: the orbit cardinality times the
value at the chosen representative. -/
theorem sum_orbit_eq_card_ennreal (g : RTree α → ℝ≥0∞)
    (hg : ∀ t t' : RTree α, t' ∈ RTree.swapFiber t → g t' = g t)
    (S : {S : Finset (RTree α) // S ∈ RTree.swapOrbits α}) :
    ∑ u ∈ S.1, g u = (S.1.card : ℝ≥0∞) * g (RTree.orbitRep α S) := by
  have hspec : RTree.swapFiber (RTree.orbitRep α S) = S.1 := RTree.orbitRep_spec S
  have hconst : ∀ u ∈ S.1, g u = g (RTree.orbitRep α S) := by
    intro u hu
    exact hg (RTree.orbitRep α S) u (by rw [hspec]; exact hu)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-- The transversal sum is the sum over the chosen orbit representatives, over `ℝ≥0∞`. -/
theorem sum_transversal_eq_sum_orbits_ennreal (g : RTree α → ℝ≥0∞) :
    ∑ r ∈ RTree.transversal α, g r
      = ∑ S ∈ (RTree.swapOrbits α).attach, g (RTree.orbitRep α S) := by
  rw [RTree.transversal]
  exact Finset.sum_image (g := RTree.orbitRep α) RTree.orbitRep_injOn

/-- **The plane multiplicity is exactly the orbit size, over `ℝ≥0∞`.**  For a function constant on
child-swap classes, the sum over the fully labelled plane family is `2 ^ (#α - 1)` times the sum
over one representative per orbit.  Nothing is estimated: the factor is the exact number
`RTree.swapOrbits_card` of plane representatives of a non-plane tree. -/
theorem sum_LT_eq_pow_mul_sum_transversal_ennreal (g : RTree α → ℝ≥0∞)
    (hg : ∀ t t' : RTree α, t' ∈ RTree.swapFiber t → g t' = g t) :
    (∑ t : RTree.LT α, g t.1)
      = (2 : ℝ≥0∞) ^ (Fintype.card α - 1) * ∑ r ∈ RTree.transversal α, g r := by
  calc (∑ t : RTree.LT α, g t.1)
      = ∑ S ∈ RTree.swapOrbits α, ∑ u ∈ S, g u := sum_LT_eq_sum_orbits_ennreal g
    _ = ∑ S ∈ (RTree.swapOrbits α).attach, ∑ u ∈ (S : Finset (RTree α)), g u :=
        (Finset.sum_attach _ _).symm
    _ = ∑ S ∈ (RTree.swapOrbits α).attach,
          (2 : ℝ≥0∞) ^ (Fintype.card α - 1) * g (RTree.orbitRep α S) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [sum_orbit_eq_card_ennreal g hg S, RTree.swapOrbits_card S.2, Nat.cast_pow]
        norm_num
    _ = (2 : ℝ≥0∞) ^ (Fintype.card α - 1)
          * ∑ S ∈ (RTree.swapOrbits α).attach, g (RTree.orbitRep α S) := by
        rw [Finset.mul_sum]
    _ = (2 : ℝ≥0∞) ^ (Fintype.card α - 1) * ∑ r ∈ RTree.transversal α, g r := by
        rw [sum_transversal_eq_sum_orbits_ennreal g]

end OrbitSum

namespace Measure

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

/-- The fully labelled plane family `LTon (Fin q) univ` and the fully labelled family
`RTree.LT (Fin q)` of the orbit count have the same shape sum: the identity map is a bijection of
subtypes of `RTree (Fin q)` defined by propositionally equal predicates. -/
theorem sum_LTon_eq_sum_LT {q : ℕ} (g : RTree (Fin q) → ℝ≥0∞) :
    (∑ t : LTon (Fin q) Finset.univ, g t.1)
      = ∑ t : PercLib.CriticalLRP.TreeExpansion.RTree.LT (Fin q), g t.1 := by
  classical
  let e : LTon (Fin q) Finset.univ
      ≃ PercLib.CriticalLRP.TreeExpansion.RTree.LT (Fin q) :=
    { toFun := fun t => ⟨t.1, fullyLabelled_of_isLabelledShape t.2⟩
      invFun := fun t => ⟨t.1, isLabelledShape_of_fullyLabelled t.2⟩
      left_inv := fun t => rfl
      right_inv := fun t => rfl }
  exact Fintype.sum_equiv e (fun t : LTon (Fin q) Finset.univ => g t.1)
    (fun t : PercLib.CriticalLRP.TreeExpansion.RTree.LT (Fin q) => g t.1) fun t => rfl

/-- **The exact relation between the shape sum of `measure_labelEvent_le_tsum_shapes_bk` and the
orbit-representative sum.**  The two differ by exactly the plane multiplicity `2 ^ (q - 1)`:
every child-swap orbit of a fully labelled tree on `q` leaves has `2 ^ (q - 1)` plane
representatives, and the position sum of the BK product is constant on the orbit by
`tsum_atlasProduct_eq_of_mem_swapFiber`. -/
theorem tsum_shapes_eq_two_pow_mul_sum_transversal [Countable V]
    (π : Sym2 V → unitInterval) (x : V) {q : ℕ} (f : Fin q → V) :
    (∑' t : LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V, atlasProduct π x f t.1 φ)
      = (2 : ℝ≥0∞) ^ (q - 1)
          * ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, atlasProduct π x f r φ := by
  calc (∑' t : LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V, atlasProduct π x f t.1 φ)
      = ∑ t : LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V, atlasProduct π x f t.1 φ :=
        tsum_fintype _
    _ = ∑ t : PercLib.CriticalLRP.TreeExpansion.RTree.LT (Fin q),
          ∑' φ : t.1.IPos → V, atlasProduct π x f t.1 φ :=
        sum_LTon_eq_sum_LT (fun r : RTree (Fin q) => ∑' φ : r.IPos → V, atlasProduct π x f r φ)
    _ = (2 : ℝ≥0∞) ^ (Fintype.card (Fin q) - 1)
          * ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, atlasProduct π x f r φ :=
        OrbitSum.sum_LT_eq_pow_mul_sum_transversal_ennreal
          (fun r => ∑' φ : r.IPos → V, atlasProduct π x f r φ)
          (fun t t' h => (tsum_atlasProduct_eq_of_mem_swapFiber π x f h).symm)
    _ = (2 : ℝ≥0∞) ^ (q - 1)
          * ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, atlasProduct π x f r φ := by
        rw [Fintype.card_fin]

end Measure

namespace Measure

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

/-- **The orbit-representative bound implies the plane-sum bound**:
`measure_labelEvent_le_sum_transversal_bk` is at most `2 ^ (q - 1)` times smaller than the
right-hand side of `measure_labelEvent_le_tsum_shapes_bk`, and the factor is exactly the plane
multiplicity.  For `q = 1` it is `1`, i.e. the two bounds coincide. -/
theorem measure_labelEvent_le_two_pow_mul_sum_transversal_bk [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q) (x : V)
    (f : Fin q → V) :
    edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      (2 : ℝ≥0∞) ^ (q - 1)
        * ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, atlasProduct π x f r φ := by
  have hone : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (q - 1) :=
    one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine (measure_labelEvent_le_sum_transversal_bk π hπ hq x f).trans ?_
  calc (∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, atlasProduct π x f r φ)
      = 1 * ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, atlasProduct π x f r φ :=
        (one_mul _).symm
    _ ≤ (2 : ℝ≥0∞) ^ (q - 1)
          * ∑ r ∈ RTree.transversal (Fin q), ∑' φ : r.IPos → V, atlasProduct π x f r φ :=
        mul_le_mul_of_nonneg_right hone (by simp)

/-- **Production's plane-sum bound rederived from the transversal bound.**  This is
`CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk` obtained by the orbit-count route: the
transversal bound plus the exact plane multiplicity `2 ^ (q - 1)`.  It is *not* an independent
proof of the same inequality from scratch — the transversal bound is the stronger statement — but
it checks that the two summations differ by exactly the plane multiplicity and nothing else. -/
theorem measure_labelEvent_le_tsum_shapes_bk' [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q) (x : V)
    (f : Fin q → V) :
    edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑' t : LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V, atlasProduct π x f t.1 φ := by
  rw [tsum_shapes_eq_two_pow_mul_sum_transversal]
  exact measure_labelEvent_le_two_pow_mul_sum_transversal_bk π hπ hq x f

/-- The canonical position sum is definitionally the existing ENNReal atlas-side weight. -/
theorem tsum_atlasProduct_eq_posSumWtE (π : Sym2 V → unitInterval) (x : V)
    {q : ℕ} (f : Fin q → V) (t : RTree (Fin q)) :
    (∑' φ : t.IPos → V, atlasProduct π x f t φ) =
      PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE
        (fun a b => edgeMeasure π (connSet a b)) t f x :=
  rfl

/-- The canonical position sum is the ordinary countable ENNReal tree weight. -/
theorem tsum_atlasProduct_eq_wtE [Countable V] (π : Sym2 V → unitInterval) (x : V)
    {q : ℕ} (f : Fin q → V) (t : RTree (Fin q)) :
    (∑' φ : t.IPos → V, atlasProduct π x f t φ) =
      PercLib.CriticalLRP.I417Base.wtE (fun a b => edgeMeasure π (connSet a b)) t
        (fun p => f (RTree.leafOfPos t p)) x := by
  rw [tsum_atlasProduct_eq_posSumWtE]
  exact PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE_eq_wtE _ _ _ _

/-- The orbit-representative canonical BK bound in tree-weight form. -/
theorem measure_labelEvent_le_wtE_transversal_bk [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q)
    (x : V) (f : Fin q → V) :
    PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑ r ∈ RTree.transversal (Fin q),
        PercLib.CriticalLRP.I417Base.wtE (fun a b => edgeMeasure π (connSet a b)) r
          (fun p => f (RTree.leafOfPos r p)) x := by
  refine (measure_labelEvent_le_sum_transversal_bk π hπ hq x f).trans_eq ?_
  exact Finset.sum_congr rfl fun r _ => tsum_atlasProduct_eq_wtE π x f r

end Measure

end CanonAtlas

/-! ### Axiom audit -/

namespace CanonAudit

set_option linter.hashCommand false

#print axioms CanonAtlas.isCanonRealization_transport
#print axioms CanonAtlas.canonAtlasEvent_eq_of_swapIso
#print axioms CanonAtlas.iUnion_canonAtlasEvent_eq_of_mem_swapFiber
#print axioms CanonAtlas.tsum_edgeMeasure_canonAtlasEvent_eq_of_mem_swapFiber
#print axioms CanonAtlas.Measure.atlasProduct_eq_of_swapIso
#print axioms CanonAtlas.Measure.tsum_atlasProduct_eq_of_mem_swapFiber
#print axioms CanonAtlas.Measure.edgeMeasure_canonAtlasEvent_le_atlasProduct
#print axioms CanonAtlas.fullyLabelled_of_isLabelledShape
#print axioms CanonAtlas.canonCover_subset_transversal_iUnion
#print axioms CanonAtlas.isLabelledShape_of_fullyLabelled
#print axioms CanonAtlas.measure_labelEvent_le_sum_transversal_bk
#print axioms CanonAtlas.OrbitSum.sum_LT_eq_sum_orbits_ennreal
#print axioms CanonAtlas.OrbitSum.sum_orbit_eq_card_ennreal
#print axioms CanonAtlas.OrbitSum.sum_transversal_eq_sum_orbits_ennreal
#print axioms CanonAtlas.OrbitSum.sum_LT_eq_pow_mul_sum_transversal_ennreal
#print axioms CanonAtlas.Measure.sum_LTon_eq_sum_LT
#print axioms CanonAtlas.Measure.tsum_shapes_eq_two_pow_mul_sum_transversal
#print axioms CanonAtlas.Measure.measure_labelEvent_le_two_pow_mul_sum_transversal_bk
#print axioms CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk'
#print axioms CanonAtlas.Measure.tsum_atlasProduct_eq_posSumWtE
#print axioms CanonAtlas.Measure.tsum_atlasProduct_eq_wtE
#print axioms CanonAtlas.Measure.measure_labelEvent_le_wtE_transversal_bk

/-! Production declarations this file consumes, audited as well: -/
#print axioms CanonAtlas.Measure.canonAtlasEvent_bk
#print axioms CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk
#print axioms CanonAtlas.labelEvent_subset_canonCover
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.nonempty_swapIso
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.diagEvent_eq_of_swapIso
#print axioms PercLib.CriticalLRP.edgeMeasure_bk_atlas

end CanonAudit
