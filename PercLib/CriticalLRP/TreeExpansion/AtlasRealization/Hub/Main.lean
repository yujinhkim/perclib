/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Swarm smwwr4usj / member m1.  Direction (A), part 1: the deterministic regrouping.

Integrated base: production commit `6b7eb1107b03297e4df33585eeac818682adb1d2`, Lean 4.35.0.

The definitions are in `Defs.lean` (`Real.atlasEdgeEquiv`, `Real.hubStarAEdges`,
`Real.hubAEdges`, `Real.offHubAEdges`, `Real.HubStarJoint`, `Real.hubStarConnProd`,
`Real.HubStarAllJoint`, `Real.atlasConnProd`, `Real.hubSplitConnProd`).

This file transports the hub partition of `RTree.exists_hub_structure`
(`TreeExpansion/Atlas/Structure.lean`) to the realized atlas of
`TreeExpansion/AtlasRealization` and proves:

* `mem_hubStarAEdges`, `mem_hubAEdges`, `mem_offHubAEdges` — the membership descriptions;
* `card_hubStarAEdges` (three edges at every hub), `card_hubAEdges` (`3k`) and
  `card_offHubAEdges` (`2p - 1 - 3k`), and `hubAEdges_union_offHubAEdges` /
  `disjoint_hubAEdges_offHubAEdges` — the partition of the atlas;
* `disjoint_hubStarAEdges` — the 3-stars of a one-parity-class hub set are pairwise disjoint,
  so no atlas edge is charged to two hubs (this is where "no doubled root/parent edge" lives:
  a hub's up edge is its parent's down edge, and same-parity hubs are never adjacent);
* `prod_hubStarAEdges`, `prod_hubAEdges`, `atlasConnProd_eq_hubSplit` — the product of the
  `2p - 1` atlas factors is exactly the `k` three-factor blocks times the `2p - 1 - 3k`
  remaining one-factor blocks.

Nothing probabilistic is used in this part; the BK inequalities are in `HubBKProb.lean`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Hub.Defs

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

/-! ### Membership in the transported hub edge sets -/

theorem mem_hubStarAEdges {t : RTree α} {v : t.IPos} {e : AEdge t} :
    e ∈ hubStarAEdges t v ↔
      ∃ e₀ ∈ RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2,
        atlasEdgeEquiv t e₀ = e :=
  Finset.mem_image

theorem mem_hubAEdges {t : RTree α} {S : Finset t.IPos} {e : AEdge t} :
    e ∈ hubAEdges t S ↔ ∃ v ∈ S, e ∈ hubStarAEdges t v := by
  rw [hubAEdges, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [RTree.hubEdgesIpos, Finset.mem_biUnion] at ha
    obtain ⟨p, hp, hpa⟩ := ha
    exact ⟨p.1, p.2, mem_hubStarAEdges.mpr ⟨a, hpa, rfl⟩⟩
  · rintro ⟨v, hv, he⟩
    rw [mem_hubStarAEdges] at he
    obtain ⟨e₀, h0, rfl⟩ := he
    refine ⟨e₀, ?_, rfl⟩
    simp only [RTree.hubEdgesIpos, Finset.mem_biUnion]
    exact ⟨⟨v, hv⟩, Finset.mem_attach S ⟨v, hv⟩, h0⟩

theorem mem_offHubAEdges {t : RTree α} {S : Finset t.IPos} {e : AEdge t} :
    e ∈ offHubAEdges t S ↔ ∃ e₀ ∉ RTree.hubEdgesIpos t S, atlasEdgeEquiv t e₀ = e := by
  simp only [offHubAEdges, Finset.mem_image, RTree.offHubEdgesIpos, Finset.mem_sdiff,
    Finset.mem_univ, true_and]

theorem mem_hubAEdges_of_mem_star {t : RTree α} {S : Finset t.IPos} {v : t.IPos}
    (hv : v ∈ S) {e : AEdge t} (he : e ∈ hubStarAEdges t v) : e ∈ hubAEdges t S :=
  mem_hubAEdges.mpr ⟨v, hv, he⟩

/-! ### Cardinalities: three edges per hub, and the `3k` / `2p - 1 - 3k` partition -/

theorem card_hubStarAEdges (t : RTree α) (v : t.IPos) : (hubStarAEdges t v).card = 3 := by
  rw [hubStarAEdges, Finset.card_image_of_injective _ (atlasEdgeEquiv t).injective,
    RTree.card_star]

theorem card_hubAEdges (t : RTree α) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    (hubAEdges t S).card = 3 * S.card := by
  rw [hubAEdges, Finset.card_image_of_injective _ (atlasEdgeEquiv t).injective,
    RTree.card_hubEdgesIpos t S hpar]

theorem card_offHubAEdges (t : RTree α) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    (offHubAEdges t S).card = 2 * t.numLeaves - 1 - 3 * S.card := by
  rw [offHubAEdges, Finset.card_image_of_injective _ (atlasEdgeEquiv t).injective,
    RTree.card_offHubEdgesIpos t S hpar]

/-- **The hub edges and the remaining edges partition the whole atlas.** -/
theorem hubAEdges_union_offHubAEdges (t : RTree α) (S : Finset t.IPos) :
    hubAEdges t S ∪ offHubAEdges t S = Finset.univ := by
  rw [hubAEdges, offHubAEdges, ← Finset.image_union, RTree.offHubEdgesIpos,
    Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  ext e
  exact ⟨fun _ => Finset.mem_univ e, fun _ => Finset.mem_image.mpr
    ⟨(atlasEdgeEquiv t).symm e, Finset.mem_univ _,
      (atlasEdgeEquiv t).apply_symm_apply e⟩⟩

/-- **No atlas edge is charged to a hub and to the remaining edges at once.** -/
theorem disjoint_hubAEdges_offHubAEdges (t : RTree α) (S : Finset t.IPos) :
    Disjoint (hubAEdges t S) (offHubAEdges t S) := by
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  simp only [hubAEdges, Finset.mem_image] at he
  simp only [offHubAEdges, Finset.mem_image] at he'
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨b, hb, hba⟩ := he'
  have hab : a = b := (atlasEdgeEquiv t).injective hba.symm
  subst hab
  exact (Finset.disjoint_left.mp (by
    rw [RTree.offHubEdgesIpos]; exact Finset.disjoint_sdiff) ha hb)

/-! ### The 3-stars of one parity class are pairwise disjoint -/

theorem same_parity_depth {t : RTree α} {S : Finset t.IPos}
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1))
    {v w : t.IPos} (hv : v ∈ S) (hw : w ∈ S) :
    (RTree.pathOf t v).1.length % 2 = (RTree.pathOf t w).1.length % 2 := by
  rcases hpar with h | h
  · have hv2 := h v hv
    have hw2 := h w hw
    simp only [RTree.iposDepth] at hv2 hw2
    rw [hv2, hw2]
  · have hv2 := h v hv
    have hw2 := h w hw
    simp only [RTree.iposDepth] at hv2 hw2
    rw [hv2, hw2]

/-- **The 3-stars of two distinct hubs of one parity class are disjoint.**  Hubs of one depth
parity are never parent and child (`RTree.not_parent_child_of_same_parity`), so the down edge
of one is never the up edge of the other. -/
theorem disjoint_hubStarAEdges {t : RTree α} {S : Finset t.IPos}
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1))
    {v w : t.IPos} (hv : v ∈ S) (hw : w ∈ S) (hne : v ≠ w) :
    Disjoint (hubStarAEdges t v) (hubStarAEdges t w) := by
  have hsame := same_parity_depth hpar hv hw
  have hneAddr : (RTree.pathOf t v).1 ≠ (RTree.pathOf t w).1 := by
    intro hc
    exact hne (RTree.pathOf_injective t (Subtype.ext hc))
  have hst := RTree.star_disjoint (RTree.pathOf t v).2 (RTree.pathOf t w).2 hneAddr hsame
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  rw [mem_hubStarAEdges] at he he'
  obtain ⟨a, ha, rfl⟩ := he
  obtain ⟨b, hb, hba⟩ := he'
  have hab : a = b := (atlasEdgeEquiv t).injective hba.symm
  subst hab
  exact (Finset.disjoint_left.mp hst ha hb)

theorem pairwiseDisjoint_star_attach (t : RTree α) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    (↑S.attach : Set {x // x ∈ S}).PairwiseDisjoint
      (fun p => RTree.star t (RTree.pathOf t p.1).1 (RTree.pathOf t p.1).2) := by
  intro a ha b hb hab
  have hne : a.1 ≠ b.1 := fun hc => hab (Subtype.ext hc)
  exact RTree.star_disjoint (RTree.pathOf t a.1).2 (RTree.pathOf t b.1).2
    (fun hc => hne (RTree.pathOf_injective t (Subtype.ext hc)))
    (same_parity_depth hpar a.2 b.2)

/-! ### The degenerate hub set: `k = 0` gives back the full atlas product -/

theorem hubAEdges_empty (t : RTree α) : hubAEdges t (∅ : Finset t.IPos) = ∅ := by
  rw [hubAEdges, RTree.hubEdgesIpos]
  simp

theorem hubEdgesIpos_empty (t : RTree α) :
    RTree.hubEdgesIpos t (∅ : Finset t.IPos) = ∅ := by
  rw [RTree.hubEdgesIpos]
  simp

theorem offHubAEdges_empty (t : RTree α) :
    offHubAEdges t (∅ : Finset t.IPos) = Finset.univ := by
  rw [offHubAEdges, RTree.offHubEdgesIpos, hubEdgesIpos_empty, Finset.sdiff_empty]
  ext e
  exact ⟨fun _ => Finset.mem_univ e, fun _ => Finset.mem_image.mpr
    ⟨(atlasEdgeEquiv t).symm e, Finset.mem_univ _,
      (atlasEdgeEquiv t).apply_symm_apply e⟩⟩

/-- With no hubs the regrouping is the identity: the `3k = 0` block product is `1` and the
`2p - 1 - 3k = 2p - 1` remaining edges are all atlas edges.  This is the boundary case the
paper's `k = 0` instance of Lemma I.4.16 uses. -/
theorem hubSplitConnProd_empty (pr : E → ℝ) (ends : E → Sym2 V) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) :
    hubSplitConnProd pr ends y c t φ ∅ = atlasConnProd pr ends y c t φ := by
  simp only [hubSplitConnProd, atlasConnProd, offHubAEdges_empty, Finset.prod_empty, one_mul]

/-! ### The regrouping of the atlas product -/

theorem prod_hubStarAEdges (t : RTree α) (v : t.IPos) {g : AEdge t → ℝ} :
    ∏ e ∈ hubStarAEdges t v, g e
      = ∏ e ∈ RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2,
          g (atlasEdgeEquiv t e) := by
  rw [hubStarAEdges]
  exact Finset.prod_image (fun a _ b _ h => (atlasEdgeEquiv t).injective h)

/-- **The product of the `3k` hub edges is the product of the `k` three-factor blocks.**  Uses
pairwise disjointness of the 3-stars (`pairwiseDisjoint_star_attach`): every atlas edge of the
hub set is counted in exactly one block, so no edge — in particular no root edge and no
parent/child down edge — is doubled. -/
theorem prod_hubAEdges (t : RTree α) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) {g : AEdge t → ℝ} :
    ∏ v ∈ S, ∏ e ∈ hubStarAEdges t v, g e = ∏ e ∈ hubAEdges t S, g e := by
  have h1 : (∏ v ∈ S, ∏ e ∈ hubStarAEdges t v, g e)
      = ∏ v ∈ S, ∏ i ∈ RTree.star t (RTree.pathOf t v).1 (RTree.pathOf t v).2,
          g (atlasEdgeEquiv t i) :=
    Finset.prod_congr rfl (fun v _ => prod_hubStarAEdges t v)
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

/-- **The atlas product is the hub-regrouped product.**  `2p - 1` factors on the left; `k`
blocks of three and `2p - 1 - 3k` single factors on the right, with the cardinalities
`card_hubAEdges` and `card_offHubAEdges`. -/
theorem atlasConnProd_eq_hubSplit (pr : E → ℝ) (ends : E → Sym2 V) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    atlasConnProd pr ends y c t φ = hubSplitConnProd pr ends y c t φ S := by
  have hsplit : ∏ e : AEdge t, prob pr (ConnEvent ends y c t φ e)
      = (∏ e ∈ hubAEdges t S, prob pr (ConnEvent ends y c t φ e))
        * ∏ e ∈ offHubAEdges t S, prob pr (ConnEvent ends y c t φ e) := by
    rw [← hubAEdges_union_offHubAEdges t S]
    exact Finset.prod_union (disjoint_hubAEdges_offHubAEdges t S)
  have hregroup : (∏ e ∈ hubAEdges t S, prob pr (ConnEvent ends y c t φ e))
      = ∏ v ∈ S, hubStarConnProd pr ends y c t φ v := by
    simp only [hubStarConnProd]
    rw [prod_hubAEdges t S hpar]
  rw [atlasConnProd, hubSplitConnProd, ← hregroup]
  exact hsplit

end PercLib.CriticalLRP.TreeExpansion.Real
