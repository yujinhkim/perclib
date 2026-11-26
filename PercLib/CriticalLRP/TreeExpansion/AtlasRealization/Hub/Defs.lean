/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Swarm smwwr4usj / member m1.  New definitions for direction (A).

Integrated base: production commit `6b7eb1107b03297e4df33585eeac818682adb1d2`
(read-only checkout at `.scratch/critical-lrp-orchestration`), Lean 4.35.0.

This file is the independently built `Defs.lean` of the layer that transports the *hub
decomposition* (`TreeExpansion/Atlas`, `RTree.exists_hub_structure`) into the *realized atlas*
(`TreeExpansion/AtlasRealization`, `Real.AEdge`, `Real.DiagEvent`, `Real.bk_disjOcc`), so that
the BK product of an atlas can be regrouped into `k` three-point blocks and `2p - 1 - 3k`
two-point factors as in the proof of Lemma I.4.16 of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45,

and of Lemma I.4.16's use in Cases 1 and 2 of Proposition I.4.2.

## What is added, and what is *not*

The two layers do not currently meet:

* `Real.AEdge t = (t.IPos × Bool) ⊕ PUnit` (the realized atlas: the down edge of every internal
  vertex in each of the two child directions, plus the root edge);
* `RTree.AtlasEdge t = ({s : List Bool // s ∈ t.ipaths} × Bool) ⊕ PUnit` (the address form on
  which the hub selection `RTree.exists_hub_structure`, the 3-stars `RTree.star` and the edge
  partition `RTree.hubEdgesIpos`/`RTree.offHubEdgesIpos` live).

`atlasEdgeEquiv` is the identification, induced by the two round trips
`RTree.pathOf_iposOfPath`/`RTree.iposOfPath_pathOf`.  With it, `hubStarAEdges` is the 3-star of a
hub as a set of realized atlas edges, and `hubAEdges`/`offHubAEdges` are the two cells of the
`3k` / `2p - 1 - 3k` partition.

* `HubStarJoint` is the **joint value** at a hub: the disjoint occurrence of the three
  connection events of its 3-star — one single joint event, with three pairwise disjoint
  witnesses.  It is deliberately *not* a product.
* `hubStarConnProd` is the **product of the three two-point connection probabilities** of the
  same 3-star.  The two are separated: `prob_hubStarJoint_le` (in `HubBK.lean`) is the honest
  inequality joint value `≤` product, and it is the 3-fold BK step.
* `HubStarAllJoint` is the simultaneous version over all `k` hubs (`3k` edges); `atlasConnProd`
  is the full `2p - 1`-fold product and `hubSplitConnProd` its regrouping.

No probability is asserted here, and no definition below replaces a source hypothesis: every
one is a definitional packaging of data that already exists in production.  Nothing here
introduces an opaque predicate.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover
public import PercLib.CriticalLRP.TreeExpansion.Atlas.Structure

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]
variable {α : Type*}

/-! ### The address form and the realized form of the atlas edges -/

/-- The internal vertices of `t` are its internal addresses (the two round trips of
`Atlas/Bridge.lean`).  This is the identification behind every definition below. -/
noncomputable def pathEquiv (t : RTree α) :
    {s : List Bool // s ∈ RTree.ipaths t} ≃ t.IPos where
  toFun p := RTree.iposOfPath t p.1 p.2
  invFun v := RTree.pathOf t v
  left_inv p := Subtype.ext (by simpa using RTree.pathOf_iposOfPath t p.1 p.2)
  right_inv v := RTree.iposOfPath_pathOf t v

/-- **The atlas edges of the hub layer are the atlas edges of the realized layer**: the
down edges of the internal vertices in both directions plus the root edge, with the addresses
`{s // s ∈ ipaths t}` replaced by the internal vertices `t.IPos`. -/
noncomputable def atlasEdgeEquiv (t : RTree α) : RTree.AtlasEdge t ≃ AEdge t :=
  (pathEquiv t).prodCongr (Equiv.refl Bool) |>.sumCongr (Equiv.refl PUnit)

/-! ### The 3-stars, the hub edges and the remaining edges, as realized atlas edges -/

/-- The **3-star of the hub `v`** as a set of realized atlas edges: the two down edges of `v`
(in the two child directions) and the up edge of `v` (its parent's down edge, or the root edge
when `v` is the root of `t`).  Same-parity hubs are never parent and child, so the 3-stars of a
one-parity-class hub set are pairwise disjoint (`disjoint_hubStarAEdges`). -/
noncomputable def hubStarAEdges (t : RTree α) (v : t.IPos) : Finset (AEdge t) :=
  (RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2).image (atlasEdgeEquiv t)

/-- The `3k` atlas edges covered by the 3-stars of the hub set `S`. -/
noncomputable def hubAEdges (t : RTree α) (S : Finset t.IPos) : Finset (AEdge t) :=
  (RTree.hubEdgesIpos t S).image (atlasEdgeEquiv t)

/-- The `2p - 1 - 3k` atlas edges **not** adjacent to the hub set `S`: the paper's "remaining
edges of the tree that are not adjacent to a vertex in this set". -/
noncomputable def offHubAEdges (t : RTree α) (S : Finset t.IPos) : Finset (AEdge t) :=
  (RTree.offHubEdgesIpos t S).image (atlasEdgeEquiv t)

/-! ### The joint value at one hub, and the product of its three two-point factors -/

/-- **The three-point joint value at the hub `v`.**  The configuration contains three pairwise
disjoint witness sets, one for each edge of the 3-star at `v`, each connecting the two ends of
that edge.  This is a single joint event on the three arms at the hub: it is *not* a product of
two-point events, and the three witnesses come from one configuration. -/
def HubStarJoint (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) (v : t.IPos) : Set (Finset E) :=
  DisjOcc (fun e : {e : AEdge t // e ∈ hubStarAEdges t v} => ConnEvent ends y c t φ e.1)

/-- **The product of the three two-point connection probabilities** of the 3-star at `v`: the
right-hand side that the three-fold BK inequality produces for `HubStarJoint`. -/
noncomputable def hubStarConnProd (pr : E → ℝ) (ends : E → Sym2 V) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (v : t.IPos) : ℝ :=
  ∏ e ∈ hubStarAEdges t v, prob pr (ConnEvent ends y c t φ e)

/-- **All hubs at once**: the joint event that the `3k` edges of the `k` 3-stars are
simultaneously realized by pairwise disjoint witnesses.  Between `DiagEvent` and this event no
information is lost, since the witnesses are traced back to one configuration. -/
def HubStarAllJoint (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) (S : Finset t.IPos) : Set (Finset E) :=
  DisjOcc (fun e : {e : AEdge t // e ∈ hubAEdges t S} => ConnEvent ends y c t φ e.1)

/-! ### The full BK product and its hub regrouping -/

/-- The full `2p - 1`-fold BK product of the atlas of `t` at the position assignment `φ`. -/
noncomputable def atlasConnProd (pr : E → ℝ) (ends : E → Sym2 V) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) : ℝ :=
  ∏ e : AEdge t, prob pr (ConnEvent ends y c t φ e)

/-- **The hub regrouping of the atlas product**: `k` blocks of three factors (the 3-stars of
the hubs, `HubStarJoint`'s product side) times `2p - 1 - 3k` single factors (the edges not
adjacent to the hub set).  Each atlas edge occurs in exactly one factor; the root edge and a
hub's up edge are not counted twice because the hubs of `S` are pairwise non-adjacent. -/
noncomputable def hubSplitConnProd (pr : E → ℝ) (ends : E → Sym2 V) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos) : ℝ :=
  (∏ v ∈ S, hubStarConnProd pr ends y c t φ v) *
    ∏ e ∈ offHubAEdges t S, prob pr (ConnEvent ends y c t φ e)

end PercLib.CriticalLRP.TreeExpansion.Real
