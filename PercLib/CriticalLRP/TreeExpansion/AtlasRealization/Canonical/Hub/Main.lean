/- Independently rebuilt and integrated from `smwx2gpeq`, member `m1` finding f1.
Production integration revision: `4a0f1d2a3c823f8e636a9296a0a909362bdee4d7`.

Production is read only (HEAD 4a0f1d2a3c823f8e636a9296a0a909362bdee4d7,
`.scratch/critical-lrp-orchestration`).

# The canonical hub regrouping

Definitions are in `CanonHub/Defs.lean`.  This file proves, in order:

* the restriction of a canonical atlas realization to the joint hub events, *with the very same
  witness family* (`isCanonRealization_restrictFam`, `canonAtlasEvent_subset_hubStarJoint`,
  `canonAtlasEvent_subset_hubAllJoint`, `canonAtlasEvent_subset_hubAllJoint_inter_offHubJoint`);
* the three-fold BK step at one hub and the `3k`-fold BK step at all hubs
  (`edgeMeasure_hubStarJoint_le`, `edgeMeasure_hubAllJoint_le`,
  `edgeMeasure_hubAllJoint_le_hubSplit`), i.e. joint values bounded by products of raw two-point
  factors -- never identified with them;
* the deterministic regrouping of the `2p - 1`-fold atlas product into `k` three-factor blocks
  and `2p - 1 - 3k` single factors (`atlasEdgeProd_eq_hubSplit`), reusing the finite-layer
  `Finset` algebra `Real.prod_hubAEdges` and the partition of `Real.hubAEdges_union_offHubAEdges`;
* the per-shape bound `edgeMeasure_canonAtlasEvent_le_hubSplit` and the hub selector
  `exists_canonHub_bound`, which applies `RTree.exists_hub_structure` with the parity condition
  as already proved.

Nothing here uses finiteness of `V`, of `Sym2 V`, or of a configuration; the only finite index is
the atlas edge set `Real.AEdge t` of one shape.  The probabilistic input is exactly the
independently proved finite-index canonical BK inequality `Percolation.bk_disjFam`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Defs

/-!
# Restriction, BK, regrouping and the hub selector
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas

open Finset

open PercLib.CriticalLRP (Config Connects connSet edgeMeasure)
open PercLib.CriticalLRP.Percolation (DisjFam bk_disjFam)
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real
  (AEdge srcPos dstPos hubStarAEdges hubAEdges offHubAEdges mem_hubAEdges_of_mem_star
   card_hubAEdges card_offHubAEdges hubAEdges_union_offHubAEdges
   disjoint_hubAEdges_offHubAEdges atlasEdgeEquiv pairwiseDisjoint_star_attach
   offHubAEdges_empty)

variable {V : Type*} [DecidableEq V]
variable {α : Type*}

/-! ### Restricting a disjoint occurrence to a subfamily

These are the witness-level lemmas: the restricted event is witnessed by the *same* family,
indexed by a subtype.  No independence and no new witness is produced. -/

/-- A disjoint occurrence restricts to any subfamily of its index type, with the same witness
family.  Canonical counterpart of `Real.disjOcc_restrict`, on `Percolation.DisjFam`. -/
theorem disjFam_subtype {E : Type*} {ι : Type*} (s : Finset ι) (A : ι → Set (Set E)) :
    DisjFam A ⊆ DisjFam (fun i : {i : ι // i ∈ s} => A i.1) := by
  rintro ω ⟨W, hsub, hmem, hdisj⟩
  exact ⟨fun i => W i.1, fun i => hsub i.1, fun i => hmem i.1,
    fun i j hij => hdisj i.1 j.1 (fun h => hij (Subtype.ext h))⟩

/-- A disjoint occurrence over a finite index set restricts to a smaller index set, with the same
witness family.  This is what turns "the whole atlas is realized" into "the `k` 3-stars are
realized" and "the remaining edges are realized" simultaneously. -/
theorem disjFam_subtype_of_subset {E : Type*} {ι : Type*} {s u : Finset ι} (h : u ⊆ s)
    (A : ι → Set (Set E)) :
    DisjFam (fun i : {i : ι // i ∈ s} => A i.1) ⊆
      DisjFam (fun i : {i : ι // i ∈ u} => A i.1) := by
  rintro ω ⟨W, hsub, hmem, hdisj⟩
  refine ⟨fun i => W ⟨i.1, h i.2⟩, ?_, ?_, ?_⟩
  · intro i
    exact hsub ⟨i.1, h i.2⟩
  · intro i
    exact hmem ⟨i.1, h i.2⟩
  · intro i j hij
    exact hdisj ⟨i.1, h i.2⟩ ⟨j.1, h j.2⟩
      (fun hh => hij (Subtype.ext (by simpa using congrArg Subtype.val hh)))

/-- **A canonical atlas realization restricts to every finite subfamily of atlas edges, with the
same witnesses.**  The three conclusions are exactly the three fields of `IsCanonRealization`
(`subset`, `conn`, `disjoint`) restricted along the subtype, so the witnesses are literally the
witnesses of the realization; in particular repeated physical vertices and degenerate (empty)
witnesses are preserved rather than replaced. -/
theorem isCanonRealization_restrictFam {ω : Config V} {y : α → V} {c : V} {t : RTree α}
    {φ : t.IPos → V} {wit : AEdge t → Finset (Sym2 V)}
    (h : IsCanonRealization ω y c φ wit) (s : Finset (AEdge t)) :
    (∀ i : {e : AEdge t // e ∈ s}, (wit i.1 : Set (Sym2 V)) ⊆ ω) ∧
      (∀ i : {e : AEdge t // e ∈ s},
        (wit i.1 : Set (Sym2 V)) ∈ atlasConnEvent y c t φ i.1) ∧
      (∀ i j : {e : AEdge t // e ∈ s}, i ≠ j → Disjoint (wit i.1) (wit j.1)) :=
  ⟨fun i => h.subset i.1, fun i => h.conn i.1,
    fun i j hij => h.disjoint i.1 j.1 (fun hh => hij (Subtype.ext hh))⟩

/-! ### The atlas event implies each joint hub event, with the same witnesses -/

/-- **The whole canonical atlas implies the joint three-arm value at every hub.**  The witness
family is the realization's own, restricted to the three edges of the 3-star of `v`. -/
theorem canonAtlasEvent_subset_hubStarJoint (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) (v : t.IPos) :
    CanonAtlasEvent y c t φ ⊆ hubStarJoint y c t φ v := by
  rw [canonAtlasEvent_eq_disjFam]
  exact disjFam_subtype (hubStarAEdges t v) _

/-- **The whole canonical atlas implies the joint hub event at all `k` hubs at once.**  One
configuration, one witness family, `3k` mutually disjoint witnesses. -/
theorem canonAtlasEvent_subset_hubAllJoint (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) (S : Finset t.IPos) :
    CanonAtlasEvent y c t φ ⊆ hubAllJoint y c t φ S := by
  rw [canonAtlasEvent_eq_disjFam]
  exact disjFam_subtype (hubAEdges t S) _

/-- **The whole canonical atlas implies both halves of the hub partition at once**, again with
the realization's own witnesses: the `3k` star edges and the `2p - 1 - 3k` remaining edges. -/
theorem canonAtlasEvent_subset_hubAllJoint_inter_offHubJoint (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) (S : Finset t.IPos) :
    CanonAtlasEvent y c t φ ⊆ hubAllJoint y c t φ S ∩ offHubJoint y c t φ S :=
  fun _ hω =>
    ⟨canonAtlasEvent_subset_hubAllJoint y c t φ S hω,
      by
        rw [canonAtlasEvent_eq_disjFam] at hω
        exact disjFam_subtype (offHubAEdges t S) _ hω⟩

/-- **The all-hub joint event implies each single-hub joint event**, because the 3-star of a hub
of `S` is a subfamily of the `3k` star edges.  So the `k` blocks of the regrouping are not
alternatives: they hold simultaneously in one configuration. -/
theorem hubAllJoint_subset_hubStarJoint {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V}
    {S : Finset t.IPos} {v : t.IPos} (hv : v ∈ S) :
    hubAllJoint y c t φ S ⊆ hubStarJoint y c t φ v :=
  disjFam_subtype_of_subset (fun _ he => mem_hubAEdges_of_mem_star hv he) _

/-! ### The regrouping algebra, in an arbitrary commutative monoid

The finite-layer `Real.prod_hubAEdges` is stated for `ℝ`-valued factors only, because the finite
Bernoulli layer's product is `Real.prob pr`.  The canonical product lives in `ℝ≥0∞`, so the same
`Finset` computation is repeated here once, in a general `CommMonoid`; the proof is the finite
one's, and it is still purely combinatorial (no probability, no hypothesis on `V`). -/

section Generic

variable {M : Type*} [CommMonoid M]

/-- The product over the 3-star of a hub, transported along the atlas edge identification. -/
theorem prod_hubStarAEdges_gen (t : RTree α) (v : t.IPos) {g : AEdge t → M} :
    ∏ e ∈ hubStarAEdges t v, g e
      = ∏ e ∈ RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2,
          g (atlasEdgeEquiv t e) := by
  rw [hubStarAEdges]
  exact Finset.prod_image (fun a _ b _ h => (atlasEdgeEquiv t).injective h)

/-- **The product over the `3k` hub edges is the product of the `k` three-factor blocks**, for
factors in any commutative monoid.  Pairwise disjointness of the 3-stars
(`Real.pairwiseDisjoint_star_attach`, from the already-proved parity condition) is what makes the
block product equal the product over the union, so no atlas edge is counted twice. -/
theorem prod_hubAEdges_gen (t : RTree α) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) {g : AEdge t → M} :
    ∏ v ∈ S, ∏ e ∈ hubStarAEdges t v, g e = ∏ e ∈ hubAEdges t S, g e := by
  have h1 : (∏ v ∈ S, ∏ e ∈ hubStarAEdges t v, g e)
      = ∏ v ∈ S, ∏ i ∈ RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2,
          g (atlasEdgeEquiv t i) :=
    Finset.prod_congr rfl (fun v _ => prod_hubStarAEdges_gen t v)
  have h2 : (∏ v ∈ S, ∏ i ∈ RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2,
        g (atlasEdgeEquiv t i))
      = ∏ p ∈ S.attach, ∏ i ∈ RTree.star t (RTree.pathOf t p.1).1 (RTree.pathOf t p.1).2,
          g (atlasEdgeEquiv t i) :=
    (Finset.prod_attach S (fun v =>
      ∏ i ∈ RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2,
        g (atlasEdgeEquiv t i))).symm
  have h3 : (∏ p ∈ S.attach, ∏ i ∈ RTree.star t (RTree.pathOf t p.1).1 (RTree.pathOf t p.1).2,
        g (atlasEdgeEquiv t i))
      = ∏ x ∈ RTree.hubEdgesIpos t S, g (atlasEdgeEquiv t x) := by
    simp only [RTree.hubEdgesIpos]
    exact (Finset.prod_biUnion (pairwiseDisjoint_star_attach t S hpar)).symm
  have h4 : (∏ x ∈ RTree.hubEdgesIpos t S, g (atlasEdgeEquiv t x))
      = ∏ e ∈ hubAEdges t S, g e :=
    (Finset.prod_image (s := RTree.hubEdgesIpos t S) (g := atlasEdgeEquiv t) (f := g)
      (fun a _ b _ h => (atlasEdgeEquiv t).injective h)).symm
  exact h1.trans (h2.trans (h3.trans h4))

end Generic

/-! ### The BK steps: joint values bounded by products of raw two-point factors -/

section BK

variable [Countable V]

/-- **Three-fold BK at one hub.**  The joint value at the 3-star of `v` (three simultaneously
disjoint open witnesses sharing the physical vertex `φ v`) is at most the product of the three
raw two-point connection probabilities of the same three atlas edges.

The two sides are different objects: the left is a joint three-arm probability, the right is a
product of three two-point probabilities.  Only the inequality is asserted. -/
theorem edgeMeasure_hubStarJoint_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (v : t.IPos) :
    edgeMeasure π (hubStarJoint y c t φ v) ≤ hubStarProd π y c t φ v := by
  have h := bk_disjFam π hπ
    (A := fun e : {e : AEdge t // e ∈ hubStarAEdges t v} =>
      connSet (srcPos t φ c e.1) (dstPos t φ y e.1))
    (fun e => PercLib.CriticalLRP.isUpper_connSet _ _)
    (fun e => PercLib.CriticalLRP.finiteWitness_connSet _ _)
  refine h.trans (le_of_eq ?_)
  unfold hubStarProd atlasConnEvent
  exact (Finset.prod_subtype (hubStarAEdges t v) (fun x => Iff.rfl)
    (fun e => edgeMeasure π (connSet (srcPos t φ c e) (dstPos t φ y e)))).symm

/-- **BK on the `3k` star edges.**  The simultaneous joint event at all hubs of `S` is at most
the product of the `3k` raw two-point factors of the star edges. -/
theorem edgeMeasure_hubAllJoint_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos) :
    edgeMeasure π (hubAllJoint y c t φ S)
      ≤ ∏ e ∈ hubAEdges t S, edgeMeasure π (atlasConnEvent y c t φ e) := by
  have h := bk_disjFam π hπ
    (A := fun e : {e : AEdge t // e ∈ hubAEdges t S} =>
      connSet (srcPos t φ c e.1) (dstPos t φ y e.1))
    (fun e => PercLib.CriticalLRP.isUpper_connSet _ _)
    (fun e => PercLib.CriticalLRP.finiteWitness_connSet _ _)
  refine h.trans (le_of_eq ?_)
  exact (Finset.prod_subtype (hubAEdges t S) (fun x => Iff.rfl)
    (fun e => edgeMeasure π (atlasConnEvent y c t φ e))).symm

/-- **BK on the remaining `2p - 1 - 3k` arms.**  The joint event of the edges not adjacent to a
hub of `S` is at most the product of their raw two-point factors. -/
theorem edgeMeasure_offHubJoint_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos) :
    edgeMeasure π (offHubJoint y c t φ S) ≤ offHubProd π y c t φ S := by
  have h := bk_disjFam π hπ
    (A := fun e : {e : AEdge t // e ∈ offHubAEdges t S} =>
      connSet (srcPos t φ c e.1) (dstPos t φ y e.1))
    (fun e => PercLib.CriticalLRP.isUpper_connSet _ _)
    (fun e => PercLib.CriticalLRP.finiteWitness_connSet _ _)
  refine h.trans (le_of_eq ?_)
  unfold offHubProd
  exact (Finset.prod_subtype (offHubAEdges t S) (fun x => Iff.rfl)
    (fun e => edgeMeasure π (atlasConnEvent y c t φ e))).symm

/-- The same bound, regrouped as `k` three-factor blocks, using the pairwise disjointness of the
3-stars of a one-parity-class hub set. -/
theorem edgeMeasure_hubAllJoint_le_hubSplit (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    edgeMeasure π (hubAllJoint y c t φ S) ≤ ∏ v ∈ S, hubStarProd π y c t φ v := by
  refine (edgeMeasure_hubAllJoint_le π hπ y c t φ S).trans (le_of_eq ?_)
  simp only [hubStarProd]
  exact (prod_hubAEdges_gen t S hpar).symm

end BK

/-! ### The full atlas product and its regrouping -/

section Regroup

variable [Countable V]

/-- **The whole canonical atlas is bounded by the `2p - 1`-fold product of raw two-point
factors.**  This is the per-diagram BK inequality for the canonical atlas event, with `V` only
countable; the same statement for `Fin q`-labelled shapes is
`CanonAtlas.Measure.canonAtlasEvent_bk`. -/
theorem edgeMeasure_canonAtlasEvent_le_atlasEdgeProd (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) :
    edgeMeasure π (CanonAtlasEvent y c t φ) ≤ atlasEdgeProd π y c t φ := by
  rw [canonAtlasEvent_eq_disjFam]
  unfold atlasEdgeProd
  exact bk_disjFam π hπ
    (A := fun e : AEdge t => connSet (srcPos t φ c e) (dstPos t φ y e))
    (fun e => PercLib.CriticalLRP.isUpper_connSet _ _)
    (fun e => PercLib.CriticalLRP.finiteWitness_connSet _ _)

/-- **The deterministic regrouping of the atlas product** into `k` blocks of three raw two-point
factors (the 3-stars of the hubs of `S`) and the `2p - 1 - 3k` single factors of the remaining
edges.

This is the identity form of `Real.atlasConnProd_eq_hubSplit`, transported from the finite
Bernoulli product `Real.prob pr` to the canonical `edgeMeasure π`.  It is a pure `Finset` product
statement: no probability is used, and it holds for a hub set of either parity class. -/
theorem atlasEdgeProd_eq_hubSplit (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    atlasEdgeProd π y c t φ = hubSplitProd π y c t φ S := by
  have hsplit : (∏ e : AEdge t, edgeMeasure π (atlasConnEvent y c t φ e))
      = (∏ e ∈ hubAEdges t S, edgeMeasure π (atlasConnEvent y c t φ e))
        * ∏ e ∈ offHubAEdges t S, edgeMeasure π (atlasConnEvent y c t φ e) := by
    rw [← hubAEdges_union_offHubAEdges t S]
    exact Finset.prod_union (disjoint_hubAEdges_offHubAEdges t S)
  have hregroup : (∏ e ∈ hubAEdges t S, edgeMeasure π (atlasConnEvent y c t φ e))
      = ∏ v ∈ S, hubStarProd π y c t φ v := by
    simp only [hubStarProd]
    exact (prod_hubAEdges_gen t S hpar).symm
  rw [atlasEdgeProd, hubSplitProd, ← hregroup]
  exact hsplit

/-- **The boundary case `k = 0`.**  With no hubs the `3k`-block product is `1` and all
`2p - 1` atlas edges are remaining edges, so the regrouped product is the full atlas product.
This is the `k = 0` instance of the source's Lemma I.4.16, and the canonical counterpart of
`Real.hubSplitConnProd_empty`. -/
theorem hubSplitProd_empty (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) :
    hubSplitProd π y c t φ ∅ = atlasEdgeProd π y c t φ := by
  simp only [hubSplitProd, Finset.prod_empty, one_mul, offHubProd, offHubAEdges_empty,
    atlasEdgeProd]

/-- **The per-shape canonical hub bound**: the probability that a configuration realizes the whole
atlas of `t` at `φ` is at most `k` three-factor blocks of raw two-point probabilities times the
`2p - 1 - 3k` raw two-point probabilities of the edges not adjacent to the hub set. -/
theorem edgeMeasure_canonAtlasEvent_le_hubSplit (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    edgeMeasure π (CanonAtlasEvent y c t φ) ≤ hubSplitProd π y c t φ S :=
  (edgeMeasure_canonAtlasEvent_le_atlasEdgeProd π hπ y c t φ).trans
    (le_of_eq (atlasEdgeProd_eq_hubSplit π y c t φ S hpar))

/-- **The hub selector, with the bound.**  For every shape with `p` leaves, every
`k ≤ ⌈(p - 1)/2⌉`, every edge law and every position assignment there is a hub set `S` of `k`
same-parity internal vertices, with `3k` star edges and `2p - 1 - 3k` remaining edges, such that the
canonical atlas event is bounded by the hub-regrouped product.

The hub set comes from `RTree.exists_hub_structure` (`TreeExpansion/Atlas/Structure.lean`) and the
parity condition is the one that theorem already proves; no new hypothesis is added and nothing
about `V` beyond countability is assumed. -/
theorem exists_canonHub_bound (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ S : Finset t.IPos,
      S.card = k ∧
      ((∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
        (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) ∧
      (hubAEdges t S).card = 3 * k ∧
      (offHubAEdges t S).card = 2 * t.numLeaves - 1 - 3 * k ∧
      3 * k ≤ 2 * t.numLeaves - 1 ∧
      edgeMeasure π (CanonAtlasEvent y c t φ) ≤ hubSplitProd π y c t φ S := by
  obtain ⟨S, hcard, hpar, -, -, -, -, -, -, -, h3k, -⟩ :=
    RTree.exists_hub_structure (k := k) t hk
  exact ⟨S, hcard, hpar,
    by rw [card_hubAEdges t S hpar, hcard],
    by rw [card_offHubAEdges t S hpar, hcard],
    h3k,
    edgeMeasure_canonAtlasEvent_le_hubSplit π hπ y c t φ S hpar⟩

end Regroup

/-! ### The consumer: the hub-regrouped label-event bound

This is the canonical counterpart of `Real.prob_le_sum_shapes_hubSplit`: one hub set per labelled
shape, `k` blocks of three raw two-point factors and `2p - 1 - 3k` single raw two-point factors.
It is the shape of the union bound of Lemma I.4.16 after the hub regrouping, on the canonical
model, with the per-diagram BK already discharged by `edgeMeasure_canonAtlasEvent_le_atlasEdgeProd`
and the hub selection by `RTree.exists_hub_structure`.

The identification of each block with an in-cluster three-point function, and of each single
factor with an in-cluster two-point function, is *not* part of this statement: the factors here
are raw canonical two-point connection probabilities `edgeMeasure π (connSet u v)`.
-/

/-! ### A hub selection for a whole labelled shape family -/

/-- **A hub selection indexed by the shape only.**  For every fully labelled shape on `q` labels,
`k` same-parity internal vertices, with `3k` star edges and `2p - 1 - 3k` remaining edges.

The selection depends on the shape alone: not on the positions of the internal vertices, not on
the terminal map, and not on the edge law.  That is what lets it be used uniformly inside a sum
over positions and terminals, and it is exactly how the source chooses hubs.  Purely
combinatorial: `RTree.exists_hub_structure` applied once per shape. -/
theorem exists_hubSelection {q k : ℕ} (hk : k ≤ (q - 1 + 1) / 2) :
    ∃ K : (t : LTon (Fin q) Finset.univ) → Finset t.1.IPos,
      ∀ t : LTon (Fin q) Finset.univ,
        (K t).card = k ∧
        ((∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 0) ∨
          (∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 1)) ∧
        (hubAEdges t.1 (K t)).card = 3 * k ∧
        (offHubAEdges t.1 (K t)).card = 2 * t.1.numLeaves - 1 - 3 * k := by
  classical
  have hnum : ∀ t : LTon (Fin q) Finset.univ, t.1.numLeaves = q := fun t =>
    numLeaves_of_isLabelledShape t.2
  have hex : ∀ t : LTon (Fin q) Finset.univ, ∃ S : Finset t.1.IPos,
      S.card = k ∧
      ((∀ v ∈ S, RTree.iposDepth t.1 v % 2 = 0) ∨
        (∀ v ∈ S, RTree.iposDepth t.1 v % 2 = 1)) := by
    intro t
    have hk' : k ≤ (t.1.numLeaves - 1 + 1) / 2 := by rw [hnum t]; exact hk
    obtain ⟨S, hcard, hpar, -⟩ := RTree.exists_hub_structure (k := k) t.1 hk'
    exact ⟨S, hcard, hpar⟩
  choose K hK using hex
  exact ⟨K, fun t =>
    ⟨(hK t).1, (hK t).2,
      by rw [card_hubAEdges t.1 (K t) (hK t).2, (hK t).1],
      by rw [card_offHubAEdges t.1 (K t) (hK t).2, (hK t).1]⟩⟩

section ShapeSum

variable [Countable V] [Fintype α] [DecidableEq α]

/-- **The hub-regrouped union bound, at a given shape-indexed hub selection.**  This is the
form in which the bound is used: the selection `K` is fixed before the terminal map `f` and the
positions `φ` vary, so one choice of hubs serves the whole sum. -/
theorem edgeMeasure_labelEvent_le_tsum_hubSplit_of_selection (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q) (x : V) (f : Fin q → V)
    (K : (t : LTon (Fin q) Finset.univ) → Finset t.1.IPos)
    (hK : ∀ t : LTon (Fin q) Finset.univ,
      (∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 0) ∨
        (∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 1)) :
    edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑' t : LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V,
        hubSplitProd π f x t.1 φ (K t) := by
  refine (Measure.measure_labelEvent_le_tsum_shapes_bk π hπ hq x f).trans ?_
  refine ENNReal.tsum_le_tsum fun t => ENNReal.tsum_le_tsum fun φ => ?_
  exact le_of_eq (atlasEdgeProd_eq_hubSplit π f x t.1 φ (K t) (hK t))

/-- **The hub-regrouped canonical union bound over shapes and internal positions.**

For every `q ≥ 1`, every `k ≤ ⌈(q - 1)/2⌉` and every edge law `π` with `π e < 1`, there is a
choice `K` of `k` same-parity hubs for every fully labelled shape `t` on `q` labels such that the
probability that `x` is connected to all `q` labelled terminals is at most the sum over shapes and
internal positions of the hub-regrouped product: at each shape `k` blocks of three raw two-point
factors and `2q - 1 - 3k` single raw two-point factors. -/
theorem edgeMeasure_labelEvent_le_tsum_hubSplit (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q) (x : V) (f : Fin q → V) {k : ℕ}
    (hk : k ≤ (q - 1 + 1) / 2) :
    ∃ K : (t : LTon (Fin q) Finset.univ) → Finset t.1.IPos,
      (∀ t : LTon (Fin q) Finset.univ,
        (K t).card = k ∧
        ((∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 0) ∨
          (∀ v ∈ K t, RTree.iposDepth t.1 v % 2 = 1)) ∧
        (hubAEdges t.1 (K t)).card = 3 * k ∧
        (offHubAEdges t.1 (K t)).card = 2 * t.1.numLeaves - 1 - 3 * k) ∧
      edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
        ∑' t : LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V,
          hubSplitProd π f x t.1 φ (K t) := by
  obtain ⟨K, hK⟩ := exists_hubSelection (q := q) (k := k) hk
  exact ⟨K, hK,
    edgeMeasure_labelEvent_le_tsum_hubSplit_of_selection π hπ hq x f K (fun t => (hK t).2.1)⟩

end ShapeSum

end CanonAtlas
