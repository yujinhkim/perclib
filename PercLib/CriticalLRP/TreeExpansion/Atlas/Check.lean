/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Check.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Arms

/-!
# Non-vacuity: the `p = 6`, `k = 2` instance of Case 2 of the paper

The proof of Proposition I.4.15 applies Lemma I.4.16 with `p = 6` and
`k = 2` (Case 2, `d = 3α + (Hydro)`), obtaining `(E|K|²)² (E|K|)^5` for `E|K|^6`.
This file checks that the combinatorial layer is non-vacuous at that instance: a concrete
six-leaf atlas has `5`
internal vertices and `11` atlas edges, a hub set of `2` internal vertices in one bipartition
class exists, its `3`-stars use `6` of the `11` edges, `5` edges remain, and the moment
exponent is `2·2 + 5 = 9 = 2·6 - 1 - 2`.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

theorem card_ipaths_atlasSix : (ipaths atlasSix).card = 5 := by
  rw [card_ipaths]
  decide

theorem card_ipos_atlasSix : Fintype.card (IPos atlasSix) = 5 := by
  rw [card_ipos_eq_card_ipaths, card_ipaths_atlasSix]

theorem card_atlasEdge_atlasSix : Fintype.card (AtlasEdge atlasSix) = 11 := by
  rw [card_atlasEdge_leaves]
  decide

theorem card_atlasLeaves_atlasSix : (atlasLeaves atlasSix).card = 7 := by
  rw [card_atlasLeaves]
  decide

/-- **Case 2 of the paper is a non-vacuous instance.** -/
theorem check_six_two :
    ∃ S : Finset (IPos atlasSix), S.card = 2 ∧
      (hubEdgesIpos atlasSix S).card = 6 ∧ (offHubEdgesIpos atlasSix S).card = 5 := by
  obtain ⟨S, hcard, -, h1, h2, -, -⟩ :=
    exists_hub_edge_partition_ipos atlasSix (k := 2) (by decide)
  exact ⟨S, hcard, by rw [h1], by rw [h2]; decide⟩

/-- The exponent bookkeeping at `p = 6`, `k = 2`: `2·2 + 5 = 9 = 2·6 - 1 - 2`. -/
theorem check_six_two_exponent :
    2 * 2 + (2 * 6 - 1 - 3 * 2) = 2 * 6 - 1 - 2 := by decide

end RTree

end PercLib.CriticalLRP.TreeExpansion
