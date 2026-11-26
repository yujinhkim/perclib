/-
Independently built transport lemmas for swarm `smwwtd5t5`, member `m1` (direction A).

## What this file does and why it is indispensable

Production's covering theorem `PercLib.CriticalLRP.TreeExpansion.Real.exists_realization` lives on
a *finite* edge type `E` (`[Fintype E]`): its connectivity is
`TreeGraph.Conn ends s u v = (TreeGraph.openGraph ends s).Reachable u v`, where `s : Finset E` is
a finite configuration of edge labels and `ends : E → Sym2 V` maps a label to its unordered pair
of endpoints. The canonical countable model (`Config V = Set (Sym2 V)`, `Connects`, §I.1.2 of
Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1) has no finite edge type:
its edges are `Sym2 V` itself.

The bridge used in `Cover.lean` is the following. Given a finite set `W : Finset (Sym2 V)` of open
edges of a configuration `ω`, take the finite edge type `↥W` (the subtype of `Sym2 V` given by
`W`) and the inclusion `Subtype.val : ↥W → Sym2 V` as the incidence map. Then

  `treeConn_iff_connects` : `TreeGraph.Conn ↥W.univ u v ↔ Connects (witLift W.univ) u v`,

i.e. connectivity in the finite graph on `↥W` with *all* its edges open is exactly canonical
connectivity in the finite ambient configuration `W`, and more generally for any `F : Finset ↥W`
the two open graphs are equal (`openGraph_lift_le`, `openGraph_lift_ge` are the two inclusions,
proved edge by edge from the two adjacency characterisations). This is *not* an assumption: it is
proved by an explicit walk transport in both directions, `SimpleGraph.Reachable.mono` along the
two graph inclusions. It is emphatically not the case that `Connects` is assumed to be
`TreeGraph.Conn` or vice versa; the two unfoldings (an `∃` over edge labels versus a
`SimpleGraph.Walk` in `fromEdgeSet`) are both traversed.

`isCanonRealization_of_isRealization` then transports a whole production `Real.IsRealization` of
an atlas to the canonical `CanonAtlas.IsCanonRealization`, keeping every witness inside `W ⊆ ω`:
production's `IsRealization` already confines every witness to the selected finite `W`, so no
edge outside `W` -- no cutoff cluster, no box -- is ever needed.

The remaining content, that a finite `W` can always be selected from `ω` for finitely many
connection requirements, is in `Cover.lean`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Defs
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Realize

/-!
# Transport between the finite graph on `↥W` and the canonical countable graph
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas

open Finset

open PercLib.CriticalLRP (Config Connects)

open PercLib.CriticalLRP.TreeGraph (Conn openGraph openGraph_adj)

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos IsRealization)

variable {V : Type*} [DecidableEq V] [Countable V]
variable {α : Type*}

/-! ### The two open graphs coincide -/

/-- Every edge of the finite open graph on `↥W` is an open edge of the ambient configuration
`witLift F`. -/
theorem openGraph_lift_le {W : Finset (Sym2 V)} (F : Finset ↥W) :
    openGraph (Subtype.val : ↥W → Sym2 V) F ≤
      PercLib.CriticalLRP.openGraph ((witLift F : Finset (Sym2 V)) : Set (Sym2 V)) := by
  intro u v huv
  rw [openGraph_adj] at huv
  obtain ⟨⟨a, ha, hav⟩, hne⟩ := huv
  rw [PercLib.CriticalLRP.openGraph_adj]
  refine ⟨hne, ?_⟩
  rw [← hav]
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem Subtype.val ha)

/-- Conversely, every ambient open edge of `witLift F` is an edge of the finite open graph on
`↥W`. -/
theorem openGraph_lift_ge {W : Finset (Sym2 V)} (F : Finset ↥W) :
    PercLib.CriticalLRP.openGraph ((witLift F : Finset (Sym2 V)) : Set (Sym2 V)) ≤
      openGraph (Subtype.val : ↥W → Sym2 V) F := by
  intro u v huv
  rw [PercLib.CriticalLRP.openGraph_adj] at huv
  obtain ⟨hne, hmem⟩ := huv
  rw [openGraph_adj]
  refine ⟨?_, hne⟩
  obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hmem
  exact ⟨a, ha, hav⟩

/-- **Finite-endpoint connectivity is canonical connectivity.**  For a finite set `W` of ambient
edges and a finite set `F` of its elements, `TreeGraph.Conn` in the finite graph `↥W` with open
edges `F` is exactly `Connects` in the ambient configuration `witLift F`. -/
theorem treeConn_iff_connects {W : Finset (Sym2 V)} (F : Finset ↥W) (u v : V) :
    Conn (Subtype.val : ↥W → Sym2 V) F u v ↔
      Connects ((witLift F : Finset (Sym2 V)) : Set (Sym2 V)) u v :=
  ⟨fun h => SimpleGraph.Reachable.mono (openGraph_lift_le F) h,
    fun h => SimpleGraph.Reachable.mono (openGraph_lift_ge F) h⟩

/-! ### Witnesses stay inside the selected finite edge set -/

/-- The transported witness set is contained in `W`. -/
theorem witLift_subset {W : Finset (Sym2 V)} (F : Finset ↥W) : witLift F ⊆ W := by
  intro e he
  obtain ⟨a, _ha, hav⟩ := Finset.mem_image.mp he
  rw [← hav]
  exact a.2

theorem witLift_subset_coe {W : Finset (Sym2 V)} (F : Finset ↥W) :
    ((witLift F : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ (W : Set (Sym2 V)) :=
  fun _ he => witLift_subset F he

/-- The full finite graph is the selected edge set: `witLift` of `W.attach` is `W`. -/
@[simp]
theorem witLift_attach (W : Finset (Sym2 V)) : witLift W.attach = W := by
  rw [witLift, Finset.attach_image_val]

/-- The full finite graph is the selected edge set: `witLift univ = W`. -/
theorem witLift_univ (W : Finset (Sym2 V)) :
    witLift (Finset.univ : Finset ↥W) = W := by
  rw [Finset.univ_eq_attach]
  exact witLift_attach W

/-- **Connectivity in the finite graph on all of `↥W` is canonical connectivity in `W`.**  This is
the form in which the finite covering theorem is applied: `W : Finset (Sym2 V)` is the finite set
of open edges selected from the configuration, and `↥W` is the finite edge type on which
production's `Real.exists_realization` runs. -/
theorem treeConn_univ_iff_connects {W : Finset (Sym2 V)} (u v : V) :
    Conn (Subtype.val : ↥W → Sym2 V) (Finset.univ : Finset ↥W) u v ↔
      Connects ((W : Finset (Sym2 V)) : Set (Sym2 V)) u v := by
  rw [treeConn_iff_connects, witLift_univ]

/-! ### Transporting a realization of an atlas -/

/-- The canonical realization of an atlas obtained from a finite one: transport every witness
along the inclusion `↥W → Sym2 V`.  All witnesses stay inside `W`, hence inside `ω`. -/
theorem isCanonRealization_of_isRealization {W : Finset (Sym2 V)} {ω : Config V}
    (hW : (W : Set (Sym2 V)) ⊆ ω) [Fintype α] {y : α → V} {c : V} {t : RTree α}
    {φ : t.IPos → V} {wit : AEdge t → Finset ↥W}
    (h : IsRealization (Subtype.val : ↥W → Sym2 V) (Finset.univ) y c φ wit) :
    IsCanonRealization ω y c φ (fun e => witLift (wit e)) where
  subset e := fun x hx => hW (witLift_subset_coe (wit e) hx)
  disjoint e e' hne := by
    have hdisj := Finset.disjoint_left.mp (h.disjoint e e' hne)
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hx'
    have hab : a = b := Subtype.ext hba.symm
    subst hab
    exact hdisj ha hb
  conn e := (treeConn_iff_connects (wit e) _ _).mp (h.conn e)

end CanonAtlas
