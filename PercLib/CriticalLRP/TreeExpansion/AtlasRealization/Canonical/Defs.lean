/-
Independently built definitions for swarm `smwwtd5t5`, member `m1` (direction A: the
deterministic countable realization).

Target: step (2) of the proof of the generalized tree-graph inequality (Lemma I.4.16) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45,

in the **canonical countable model** `Config V = Set (Sym2 V)` of §I.1.2, on which the paper's
whole later argument runs.

## What production already has, and why it does not apply as it stands

`PercLib.CriticalLRP.TreeExpansion.AtlasRealization.{Defs,Realize,Cover}` fixes the semantics of
an *atlas*: for a labelled binary shape `t : RTree α` and positions `φ` of its internal vertices,
the atlas edges are `AEdge t = (t.IPos × Bool) ⊕ PUnit` (the two down edges of every internal
vertex, plus the edge from the root leaf to the root of the shape), `srcPos`/`dstPos` are the two
ends of an atlas edge, and `IsRealization ends s y c φ wit` says that the finite configuration
`s : Finset E` carries pairwise disjoint open witnesses `wit e ⊆ s` for the atlas edges, under
the edge-incidence map `ends : E → Sym2 V`. `Real.exists_realization` produces such a shape and
realization for **every** configuration in which the root `v` is joined to every label of a
nonempty finite set `Z` -- but only for a finite edge type `E` (`[Fintype E]`), because it travels
along `SimpleGraph.Walk`s of the finite open graph `TreeGraph.openGraph ends s`. The finite vertex
hypothesis `[Fintype V]` appears in the probabilistic consumer `Real.prob_le_sum_shapes`, through
the sum over positions `φ : t.IPos → V`.

Neither `[Fintype E]` nor `[Fintype V]` holds in the canonical model, where `E = Sym2 V` is
countable and infinite. The honest replacement, built in this directory, is a *finite edge set*
`W : Finset (Sym2 V)` selected from the configuration itself, viewed as a finite graph through
the inclusion `↥W → Sym2 V`. No `Fintype (Sym2 V)` and no truncation of the configuration is
used anywhere; the selected `W` is not a box and not a cluster approximation, and is not required
to contain "all" edges of anything -- it is just a finite set of open edges carrying the finitely
many required connections.

## Definitions introduced here

* `witLift w` -- the image in `Sym2 V` of a finite set `w : Finset ↥W` of edges of the finite
  graph `↥W`. All transports between the finite graph `↥W` and the canonical graph use this.
* `IsCanonRealization ω y c φ wit` -- the canonical analogue of `Real.IsRealization`: the
  witnesses are finite sets of *ambient* open edges of `ω`, pairwise disjoint, and each joins the
  two ends of its atlas edge by a path in `ω` that uses only the edges of `wit e` itself. The
  field names are those of `Real.IsRealization` so that the transport reads structurally.
* `CanonAtlasEvent y c t φ` -- the corresponding event on `Config V`: the configuration realizes
  the whole atlas of `t` at positions `φ` disjointly. Canonical counterpart of `Real.DiagEvent`.
* `CanonCover q y c` -- the union of the canonical atlas events over all fully labelled shapes on
  the labels `Fin q` and all position assignments: the canonical counterpart of the union in
  `Real.cover_union`, indexed by a sigma type over the finite shape family
  `LTon (Fin q) Finset.univ` and the countable position space `t.IPos → V`.

## Modelling choices, and why they are faithful

* The witnesses are required to lie *inside* `ω` (`subset`), not merely to be open in `ω`: this is
  what makes them honest witnesses for the event and makes the covering statement a statement
  about `ω` itself, whatever else `ω` contains.
* Disjointness is a property of *edges*, not vertices: distinct atlas edges may be assigned the
  same physical vertex by `φ` (repeated positions), exactly as in BK, where the disjoint
  occurrence is over edge sets.
* An empty witness is allowed only when the two ends coincide (the degenerate atlas edge of the
  source carries the factor `P(w ↔ w) = 1`); this is *proved*, not assumed, in `Cases.lean`
  (`CanonAtlas.srcPos_eq_dstPos_of_wit_eq_empty`), so no open edge is hidden behind a degenerate
  atlas edge.
* The shape index is `TreeExpansion.LTon (Fin q) Finset.univ`: a rooted binary shape whose leaf
  labels are `Fin q`, each used exactly once, i.e. "fully labelled" with the `q` terminals. Its
  `Fintype` instance (production `LTon.instFintype`) is what makes the shape family -- and hence
  the whole cover -- countable; this is used in `Cover.lean`. Nothing about the shapes is assumed
  beyond what production already proves.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Defs
public import PercLib.CriticalLRP.CountableProduct.Base

/-!
# Canonical atlas realization: definitions

The file contains definitions and their unfolding lemmas only; every proof about
configurations is in the sibling modules `Transport.lean`, `Cover.lean` and `Cases.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas

open Finset

open PercLib.CriticalLRP (Config Connects)

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos)

variable {V : Type*} [DecidableEq V]
variable {α : Type*}

/-! ### Lifting finite edge witnesses to the ambient countable edge type -/

/-- The image in the ambient edge type `Sym2 V` of a finite set `w` of edges of the finite graph
`↥W`, whose vertices are the edges of `W`.  Every witness set produced by the finite covering
theorem is transported to the ambient graph by this map. -/
def witLift {W : Finset (Sym2 V)} (w : Finset ↥W) : Finset (Sym2 V) :=
  w.image Subtype.val

theorem mem_witLift {W : Finset (Sym2 V)} {w : Finset ↥W} {e : Sym2 V} :
    e ∈ witLift w ↔ ∃ x ∈ w, (x : Sym2 V) = e :=
  Finset.mem_image

/-! ### Canonical realization of an atlas -/

/-- A **canonical realization** of the atlas of the shape `t` with internal positions `φ` in the
configuration `ω : Config V`.

`c` is the vertex at the root leaf and `y a` the vertex at the leaf labelled `a`.  The data is a
family `wit e` of finite sets of ambient edges for the atlas edges `e : AEdge t`, such that

* every `wit e` consists of open edges of `ω`;
* distinct atlas edges get edge-disjoint witnesses (no open edge is charged twice);
* each `wit e` connects the two ends of `e` by a path that uses only the edges of `wit e`.

This is `PercLib.CriticalLRP.TreeExpansion.Real.IsRealization` with the finite edge type `E`
replaced by the ambient countable edge type `Sym2 V`, and with the finite configuration
`s : Finset E` replaced by `ω`.  The empty witness is allowed and is honest: see
`CanonAtlas.srcPos_eq_dstPos_of_wit_eq_empty`. -/
structure IsCanonRealization (ω : Config V) (y : α → V) (c : V) {t : RTree α}
    (φ : t.IPos → V) (wit : AEdge t → Finset (Sym2 V)) : Prop where
  /-- every witness is a set of open edges of `ω` -/
  subset : ∀ e, (wit e : Set (Sym2 V)) ⊆ ω
  /-- distinct atlas edges have disjoint witnesses -/
  disjoint : ∀ e e', e ≠ e' → Disjoint (wit e) (wit e')
  /-- each witness connects the two ends of its atlas edge -/
  conn : ∀ e, Connects (wit e : Set (Sym2 V)) (srcPos t φ c e) (dstPos t φ y e)

/-- The **canonical atlas event** of the shape `t` at internal positions `φ`: the configuration
realizes the whole atlas of `t` by disjoint finite open witnesses.  Canonical counterpart of
`PercLib.CriticalLRP.TreeExpansion.Real.DiagEvent`. -/
def CanonAtlasEvent (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) : Set (Config V) :=
  {ω | ∃ wit : AEdge t → Finset (Sym2 V), IsCanonRealization ω y c φ wit}

/-- Membership in the canonical atlas event, unfolded. -/
theorem mem_canonAtlasEvent {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V}
    {ω : Config V} :
    ω ∈ CanonAtlasEvent y c t φ ↔
      ∃ wit : AEdge t → Finset (Sym2 V), IsCanonRealization ω y c φ wit :=
  Iff.rfl

/-- The **canonical atlas cover** of the terminally connected event: the union of the canonical
atlas events over all fully labelled shapes on the labels `Fin q` and all position assignments.
The index type is a sigma type over the finite (hence countable) shape family
`LTon (Fin q) Finset.univ` and the position space `t.IPos → V`, which is countable because
`t.IPos` is finite and `V` is countable (`CanonAtlas.countable_atlasIndex`).  This is the
canonical counterpart of the union in `Real.cover_union`. -/
def CanonCover (q : ℕ) (y : Fin q → V) (c : V) : Set (Config V) :=
  ⋃ p : (Σ t : LTon (Fin q) Finset.univ, t.1.IPos → V),
    CanonAtlasEvent y c p.1.1 p.2

/-- Membership in the canonical atlas cover, unfolded into the shape/position pair. -/
theorem mem_canonCover {q : ℕ} {y : Fin q → V} {c : V} {ω : Config V} :
    ω ∈ CanonCover q y c ↔
      ∃ p : (Σ t : LTon (Fin q) Finset.univ, t.1.IPos → V),
        ω ∈ CanonAtlasEvent y c p.1.1 p.2 :=
  Set.mem_iUnion

end CanonAtlas
