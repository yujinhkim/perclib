/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Structure.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Arms

/-!
# The hub structure of Lemma I.4.16, packaged for a consumer

`exists_hub_edge_partition_ipos` gives the hub set and the edge split, `Arms.lean` gives the
three arms at a hub.  This file bundles them: a single statement that, for every atlas with
`p` leaves and every `k ≤ ⌈(p-1)/2⌉`, produces

* `k` internal vertices of `t` in one depth-parity class (so the hub positions are fixed and,
  as the paper says, "the vertices in the distinguished set are not summed over"),
* for each hub, its three-element 3-star, pairwise disjoint across hubs,
* three pairwise disjoint nonempty arms at each hub covering the `p + 1` atlas leaves,
* the `3k` star edges and the `2p - 1 - 3k` remaining edges, partitioning the atlas,
* the numerical side conditions `3k ≤ 2p - 1` and the moment exponent `2p - 1 - k`.

The BK inequality itself is not applied here.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-- **The hub structure of Lemma I.4.16 at a single atlas, in one statement.** -/
theorem exists_hub_structure (t : RTree α) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ S : Finset (IPos t),
      S.card = k ∧
      ((∀ v ∈ S, iposDepth t v % 2 = 0) ∨ (∀ v ∈ S, iposDepth t v % 2 = 1)) ∧
      (∀ v ∈ S, (star t (pathOf t v).1 (pathOf t v).2).card = 3) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        Disjoint (star t (pathOf t v).1 (pathOf t v).2)
          (star t (pathOf t w).1 (pathOf t w).2)) ∧
      (∀ v ∈ S, ∃ (l r : RTree α) (L R U : Finset (Option (List Bool))),
        subAt t (pathOf t v).1 = some (node l r) ∧
        L = (lpaths l).image (fun u => some (((pathOf t v).1 ++ [false]) ++ u)) ∧
        R = (lpaths r).image (fun u => some (((pathOf t v).1 ++ [true]) ++ u)) ∧
        U = atlasLeaves t \ (L ∪ R) ∧
        L.Nonempty ∧ R.Nonempty ∧ U.Nonempty ∧ none ∈ U ∧
        Disjoint L R ∧ Disjoint L U ∧ Disjoint R U ∧
        L ∪ R ∪ U = atlasLeaves t) ∧
      (hubEdgesIpos t S).card = 3 * k ∧
      (offHubEdgesIpos t S).card = 2 * t.numLeaves - 1 - 3 * k ∧
      hubEdgesIpos t S ∪ offHubEdgesIpos t S = Finset.univ ∧
      Disjoint (hubEdgesIpos t S) (offHubEdgesIpos t S) ∧
      3 * k ≤ 2 * t.numLeaves - 1 ∧
      2 * t.numLeaves - 1 - k = 2 * k + (2 * t.numLeaves - 1 - 3 * k) := by
  classical
  obtain ⟨S, hcard, hpar, hhub, hoff, hunion, hdisj⟩ := exists_hub_edge_partition_ipos t hk
  have hsame : ∀ a ∈ S, ∀ b ∈ S, iposDepth t a % 2 = iposDepth t b % 2 := by
    intro a ha b hb
    rcases hpar with h | h
    · rw [h a ha, h b hb]
    · rw [h a ha, h b hb]
  refine ⟨S, hcard, hpar, ?_, ?_, ?_, hhub, hoff, hunion, hdisj, ?_, ?_⟩
  · intro v _
    exact card_star (pathOf t v).2
  · intro v hv w hw hne
    have hne' : (pathOf t v).1 ≠ (pathOf t w).1 := by
      intro hc
      exact hne (pathOf_injective t (Subtype.ext hc))
    exact star_disjoint (pathOf t v).2 (pathOf t w).2 hne' (hsame v hv w hw)
  · intro v _
    exact leaf_arms_at_ipos t v
  · -- `3k ≤ 2p - 1`
    rcases eq_or_lt_of_le (show 1 ≤ t.numLeaves by have := numLeaves_pos t; omega) with hp | hp
    · -- the one-leaf atlas: only `k = 0` is admissible
      have hk0 : k = 0 := by
        rw [← hp] at hk
        simpa using hk
      subst hk0
      simp
    · exact three_mul_le_two_mul_sub_one hp hk
  · -- the moment exponent `2p - 1 - k = 2k + (2p - 1 - 3k)`
    rcases eq_or_lt_of_le (show 1 ≤ t.numLeaves by have := numLeaves_pos t; omega) with hp | hp
    · have hk0 : k = 0 := by
        rw [← hp] at hk
        simpa using hk
      subst hk0
      simp
    · exact moment_exponent hp hk

end RTree

end PercLib.CriticalLRP.TreeExpansion
