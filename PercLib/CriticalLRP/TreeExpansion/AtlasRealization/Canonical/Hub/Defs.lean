/- Independently rebuilt and integrated from `smwx2gpeq`, member `m1` findings f1/f2.
Production integration revision: `4a0f1d2a3c823f8e636a9296a0a909362bdee4d7`.

Definitions for the canonical hub layer. `markedHubBound` belongs here with the other
new definitions; raw two-point products are kept separate from the joint hub events.

Production is read only (HEAD 4a0f1d2a3c823f8e636a9296a0a909362bdee4d7,
`.scratch/critical-lrp-orchestration`).  This file is the new, self-contained `Defs.lean` of the
canonical-hub layer; nothing in production is modified and nothing here restates a production
definition.

Target: the *hub regrouping* of the tree-graph inequality (Lemma I.4.16 of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45),

carried from the finite Bernoulli layer `TreeExpansion/AtlasRealization/Hub/` to the **genuine
canonical model** `Config V = Set (Sym2 V)` of §I.1.2.

## Why a separate layer

`TreeExpansion/AtlasRealization/Hub/{Defs,Main,Probability}.lean` prove the regrouping for the
*finite* diagram event `Real.DiagEvent`, whose witnesses live in a finite edge type `E` and whose
probability is the finite Bernoulli product `Real.prob pr` on `Finset E`.  The hub combinatorics
there (`Real.hubStarAEdges`, `Real.hubAEdges`, `Real.offHubAEdges`, `Real.prod_hubAEdges`,
`Real.hubAEdges_union_offHubAEdges`) is pure `Finset` algebra on `Real.AEdge t` and is reused
unchanged; what is added here is the canonical witness and probabilistic layer around it:

* the atlas edges of a shape are `Real.AEdge t`, the same type, so no edge transport is needed;
* the witnesses are finite sets of *ambient* edges `Finset (Sym2 V)` inside a configuration
  `ω : Config V`, with `V` only countable -- no `[Fintype V]`, no `[Fintype (Sym2 V)]`, no box,
  no finite truncation of `ω`;
* the probability is the canonical independent-edge product law `edgeMeasure π` of §I.1.2,
  not a finite product `Real.prob pr`.

## What is defined, and what each thing means

The three events below are *joint* events: each is a disjoint occurrence over a finite set of
atlas edges, so a single configuration must supply one finite open witness per atlas edge, and
those witnesses must be pairwise edge-disjoint.

* `atlasConnEvent` -- the two-point connection event of a single atlas edge, as a subset of
  `Config V`.  It is one factor of the product side.
* `hubStarJoint y c t φ v` -- the joint three-arm value at the hub `v`: simultaneously
  edge-disjoint open witnesses for the three edges of `v`'s 3-star.  This is one event on three
  arms sharing the physical vertex `φ v`; it is deliberately not a product, and its measure is
  not `P(arm₁) · P(arm₂) · P(arm₃)`.  The product is only an upper bound for it
  (`CanonHub.Main.edgeMeasure_hubStarJoint_le`), which is the three-fold BK step.
* `hubAllJoint y c t φ S` -- the same at all `k` hubs of `S` at once: `3k` atlas edges, i.e.
  the whole `k`-block part of the regrouping, again as one joint event.
* `offHubJoint y c t φ S` -- the `2p - 1 - 3k` atlas edges not adjacent to a hub of `S`, as a
  joint event.
* `atlasEdgeProd` -- the full `2p - 1`-fold product of raw two-point connection probabilities of
  the atlas edges, i.e. the right-hand side of the per-diagram BK inequality.
* `hubStarProd` -- the three-factor block `∏_{e ∈ 3-star(v)} P(two ends of e)` of the same raw
  two-point factors.  It is the product side of the three-fold BK at `v`, and it is not the
  measure of `hubStarJoint`.
* `offHubProd`, `hubSplitProd` -- the `2p - 1 - 3k` single factors of the remaining edges, and
  the regrouped product `(k blocks of three) · (2p - 1 - 3k singletons)`.

Every factor in every product of this file is `edgeMeasure π (connSet u v)` -- the probability of
a raw two-point connection `u ↔ v` in the canonical law.  No factor here is a joint-pair or
in-cluster probability, and no factor is a three-point function: the three-point (joint) object
at a hub is the event `hubStarJoint`, and BK only bounds its measure by the product of three raw
two-point factors.  The identification of the raw factors with the source's in-cluster two-point
functions, and of `hubStarJoint` with the source's three-point function, is a separate step that
needs transitivity of the model; it is not asserted here.

## Degenerate and repeated data

`φ : t.IPos → V` and `y : α → V` are arbitrary: distinct internal vertices of the shape may be
placed on the same physical vertex, and distinct leaves may carry the same terminal.  Nothing
below assumes injectivity, and no witness is required to be nonempty.  An empty witness is
honest only when the two ends of its atlas edge coincide: for a canonical realization this is
production's `CanonAtlas.srcPos_eq_dstPos_of_wit_eq_empty` (proved, not assumed), so a degenerate
arm contributes the factor `P(u ↔ u) = 1` (production `edgeMeasure_connSet_self`) and consumes no
open edge (production `Percolation.disjFam_connSet_self_option`).
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Join
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Hub.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Defs

/-!
# Canonical joint-hub events and their product factors

Definitions only: the events `atlasConnEvent`, `hubStarJoint`, `hubAllJoint`, `offHubJoint` and
the product factors `atlasEdgeProd`, `hubStarProd`, `offHubProd`, `hubSplitProd`.  Every proof
about them is in `CanonHub/Main.lean`.
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
open PercLib.CriticalLRP.Percolation (DisjFam)
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real
  (AEdge srcPos dstPos hubStarAEdges hubAEdges offHubAEdges)

variable {V : Type*} [DecidableEq V]
variable {α : Type*}

/-! ### The two-point connection event of one atlas edge -/

/-- **The connection event of a single atlas edge** in the canonical model: the configuration
joins the upper end `srcPos t φ c e` of `e` to its lower end `dstPos t φ y e`.

This is a two-point event.  It is the only probabilistic object entering the product factors
below: `edgeMeasure π (atlasConnEvent y c t φ e)` is the raw two-point probability
`P(srcPos e ↔ dstPos e)` of the canonical law `edgeMeasure π`, with no conditioning, no joint
occurrence over several arms, and no cluster restriction. -/
def atlasConnEvent (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (e : AEdge t) : Set (Config V) :=
  connSet (srcPos t φ c e) (dstPos t φ y e)

/-- Membership in `atlasConnEvent`, unfolded. -/
theorem mem_atlasConnEvent {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V}
    {e : AEdge t} {ω : Config V} :
    ω ∈ atlasConnEvent y c t φ e ↔ Connects ω (srcPos t φ c e) (dstPos t φ y e) :=
  Iff.rfl

/-! ### The joint hub events -/

/-- **The joint three-arm value at the hub `v`.**  The configuration contains three pairwise
edge-disjoint finite sets of open edges, one for each edge of the 3-star of `v`
(`Real.hubStarAEdges t v`, always exactly three edges), each connecting the two ends of its own
atlas edge.

This is a single joint event on three arms that share the physical vertex `φ v`: the three
witnesses come from one configuration, are pairwise disjoint, and are not drawn
independently.  Its measure is the canonical three-point quantity of the 3-star;
`hubStarProd` is only an upper bound for it. -/
def hubStarJoint (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (v : t.IPos) : Set (Config V) :=
  DisjFam fun e : {e : AEdge t // e ∈ hubStarAEdges t v} => atlasConnEvent y c t φ e.1

/-- **The joint hub event at all hubs of `S`.**  Simultaneously edge-disjoint finite open
witnesses for all `3k` atlas edges of the 3-stars of the `k` hubs in `S`
(`Real.hubAEdges t S`).  One configuration, one family of witnesses -- not `k` independent
single-hub events. -/
def hubAllJoint (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (S : Finset t.IPos) : Set (Config V) :=
  DisjFam fun e : {e : AEdge t // e ∈ hubAEdges t S} => atlasConnEvent y c t φ e.1

/-- **The joint event of the remaining arms.**  Simultaneously edge-disjoint finite open
witnesses for the `2p - 1 - 3k` atlas edges that are not adjacent to a hub of `S`
(`Real.offHubAEdges t S`).  This is the "remaining edges of the tree that are not adjacent to a
vertex in this set" of the source, kept as a joint event rather than replaced by a product. -/
def offHubJoint (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (S : Finset t.IPos) : Set (Config V) :=
  DisjFam fun e : {e : AEdge t // e ∈ offHubAEdges t S} => atlasConnEvent y c t φ e.1

/-! ### The product factors

Each factor is the probability of one raw two-point connection.  Products of them are what BK
produces; the joint events above are what the moment layer evaluates.  The two are kept apart on
purpose.
-/

section Products

variable [Countable V]

/-- **The full atlas product**: the `2p - 1`-fold product of the raw two-point connection
probabilities of the atlas edges of `t` at the positions `φ`.  This is the right-hand side of the
per-diagram BK inequality (`CanonAtlas.Measure.atlasProduct` of the `Fin q`-labelled layer is the
same number). -/
noncomputable def atlasEdgeProd (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) : ℝ≥0∞ :=
  ∏ e : AEdge t, edgeMeasure π (atlasConnEvent y c t φ e)

/-- **The three-factor block of the hub `v`**: the product of the raw two-point connection
probabilities of the three edges of `v`'s 3-star.  This is the product side of the three-fold BK
step at `v`; it is not the measure of `hubStarJoint`, which is the joint value and is at most
this product. -/
noncomputable def hubStarProd (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (v : t.IPos) : ℝ≥0∞ :=
  ∏ e ∈ hubStarAEdges t v, edgeMeasure π (atlasConnEvent y c t φ e)

/-- **The `2p - 1 - 3k` single factors** of the atlas edges not adjacent to a hub of `S`. -/
noncomputable def offHubProd (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos) : ℝ≥0∞ :=
  ∏ e ∈ offHubAEdges t S, edgeMeasure π (atlasConnEvent y c t φ e)

/-- **The hub regrouping of the atlas product**: `k` blocks of three raw two-point factors (the
3-stars of the hubs of `S`) times the `2p - 1 - 3k` raw two-point factors of the remaining edges.

Every atlas edge occurs in exactly one factor: the 3-stars of a one-parity-class hub set are
pairwise disjoint (`Real.disjoint_hubStarAEdges`) and disjoint from the remaining edges
(`Real.disjoint_hubAEdges_offHubAEdges`), so no root edge and no parent/child down edge is
counted twice.  `CanonHub.Main.atlasEdgeProd_eq_hubSplit` proves the identity with
`atlasEdgeProd`. -/
noncomputable def hubSplitProd (π : Sym2 V → unitInterval) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos) : ℝ≥0∞ :=
  (∏ v ∈ S, hubStarProd π y c t φ v) * offHubProd π y c t φ S

end Products

/-- **The hub-regrouped marked bound**, in arm-labelling form: the sum over the arm tuples
`f : Fin p → V`, the fully labelled `(p + 1)`-leaf shapes and the positions of their internal
vertices, of the hub-regrouped product at the terminal tuple `markedExtend w f` (the `p` arms of
`x`, with the mark `w` as the last terminal), for a shape-indexed hub selection `K`.

Every factor is a raw two-point connection probability, not an in-cluster joint quantity. -/
noncomputable def markedHubBound {V : Type*} [Countable V] (π : Sym2 V → unitInterval)
    (x w : V) (p : ℕ)
    (K : (t : LTon (Fin (p + 1)) Finset.univ) → Finset t.1.IPos) : ℝ≥0∞ :=
  ∑' f : Fin p → V, ∑' t : LTon (Fin (p + 1)) Finset.univ,
    ∑' φ : t.1.IPos → V,
      hubSplitProd π (PercLib.CriticalLRP.I417Marked.markedExtend w f) x t.1 φ (K t)

end CanonAtlas
