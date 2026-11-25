/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Arms.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Interface

/-!
# The atlas leaf set and the three arms at a hub

`Hub.lean` proves the leaf partition of the *tree* `t` at a hub: the leaves of `t` split into
the two downward arms and the rest.  For the three-fold BK step of Lemma I.4.16 the third arm
must be nonempty as well, and in the atlas it always is: it contains the root leaf `0`.

This file therefore models the atlas leaf set as `RTree.atlasLeaves t`, the `p` leaves of
`t` together with the root leaf `0` encoded as `none` — `p + 1` leaves in total, matching the
paper's "trees with `p + 1` leaves labelled `{0, ..., p}`".  `leaf_arms_atlas` then gives, at
every internal vertex, three pairwise disjoint **nonempty** arms whose union is the whole atlas
leaf set, with the root leaf in the third arm.  This is the deterministic input to the
three-point factor at a hub.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

@[simp] theorem some_mem_atlasLeaves {t : RTree α} {s : List Bool} :
    some s ∈ atlasLeaves t ↔ s ∈ lpaths t := by
  simp [atlasLeaves]

theorem mem_atlasLeaves {t : RTree α} {x : Option (List Bool)} :
    x ∈ atlasLeaves t ↔ x = none ∨ ∃ s ∈ lpaths t, x = some s := by
  cases x with
  | none => simp [atlasLeaves]
  | some s => simp

/-- The atlas of a tree with `p` leaves has `p + 1` leaves. -/
theorem card_atlasLeaves (t : RTree α) : (atlasLeaves t).card = t.numLeaves + 1 := by
  have hnone : none ∉ (lpaths t).image (fun s => some s) := by
    intro h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp h
    exact absurd hs (by simp)
  have hcard : ((lpaths t).image (fun s => some s)).card = t.numLeaves := by
    rw [Finset.card_image_of_injective _ (fun a b h => Option.some.inj h), card_lpaths]
  rw [atlasLeaves, Finset.card_insert_of_notMem hnone, hcard]

/-- An arm below a vertex: the leaves of the subtree at `w`, as atlas leaves. -/
theorem image_some_lpaths_subset_atlasLeaves {t T : RTree α} {w : List Bool}
    (hsub : subAt t w = some T) :
    (lpaths T).image (fun u => some (w ++ u)) ⊆ atlasLeaves t := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  rw [some_mem_atlasLeaves]
  exact mem_image_lpaths_of_subAt hsub hu

/-- **The three arms at a hub in the atlas.**  At every internal vertex of `t` the atlas
leaves split into the leaves below the left child, the leaves below the right child and the
remaining arm, which contains the root leaf `0`.  All three arms are nonempty and pairwise
disjoint, and together they are all `p + 1` atlas leaves: the deterministic input to the
three-fold BK step at a hub in the proof of Lemma I.4.16. -/
theorem leaf_arms_atlas {t : RTree α} {v : List Bool} (hv : v ∈ ipaths t) :
    ∃ (l r : RTree α) (L R U : Finset (Option (List Bool))),
      subAt t v = some (node l r) ∧
      L = (lpaths l).image (fun u => some ((v ++ [false]) ++ u)) ∧
      R = (lpaths r).image (fun u => some ((v ++ [true]) ++ u)) ∧
      U = atlasLeaves t \ (L ∪ R) ∧
      L.Nonempty ∧ R.Nonempty ∧ U.Nonempty ∧ none ∈ U ∧
      Disjoint L R ∧ Disjoint L U ∧ Disjoint R U ∧
      L ∪ R ∪ U = atlasLeaves t := by
  obtain ⟨l, r, L₀, R₀, U₀, hsub, hL₀, hR₀, -, hLn, hRn, hdLR, -, -, -⟩ := leaf_arms hv
  have hfl : subAt t (v ++ [false]) = some l := by rw [subAt_append, hsub]; simp
  have hfr : subAt t (v ++ [true]) = some r := by rw [subAt_append, hsub]; simp
  set L : Finset (Option (List Bool)) :=
    (lpaths l).image (fun u => some ((v ++ [false]) ++ u)) with hL
  set R : Finset (Option (List Bool)) :=
    (lpaths r).image (fun u => some ((v ++ [true]) ++ u)) with hR
  have hLsub : L ⊆ atlasLeaves t := image_some_lpaths_subset_atlasLeaves hfl
  have hRsub : R ⊆ atlasLeaves t := image_some_lpaths_subset_atlasLeaves hfr
  have hLR : Disjoint L R := by
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u', -, hu'⟩ := Finset.mem_image.mp hx'
    have h3 : (v ++ [true]) ++ u' = (v ++ [false]) ++ u := Option.some.inj hu'
    have h4 := congrArg (fun z => z.drop v.length) h3
    simp only [List.append_assoc, List.singleton_append, List.drop_left] at h4
    exact absurd (List.cons.inj h4).1 (by simp)
  have hnoneLR : none ∉ L ∪ R := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨u, -, hu⟩ := Finset.mem_image.mp h
      exact absurd hu (by simp)
    · obtain ⟨u, -, hu⟩ := Finset.mem_image.mp h
      exact absurd hu (by simp)
  have hnoneU : none ∈ atlasLeaves t \ (L ∪ R) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, hnoneLR⟩
  refine ⟨l, r, L, R, atlasLeaves t \ (L ∪ R), hsub, hL, hR, rfl, ?_, ?_, ?_, hnoneU,
    hLR, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := lpaths_nonempty l
    exact ⟨some ((v ++ [false]) ++ u), Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  · obtain ⟨u, hu⟩ := lpaths_nonempty r
    exact ⟨some ((v ++ [true]) ++ u), Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  · exact ⟨none, hnoneU⟩
  · refine Finset.disjoint_left.mpr fun x hx hxU => ?_
    exact (Finset.mem_sdiff.mp hxU).2 (Finset.mem_union_left _ hx)
  · refine Finset.disjoint_left.mpr fun x hx hxU => ?_
    exact (Finset.mem_sdiff.mp hxU).2 (Finset.mem_union_right _ hx)
  · rw [Finset.union_sdiff_of_subset (Finset.union_subset hLsub hRsub)]

/-- **The three arms at a hub of the atlas, indexed by production vertices.** -/
theorem leaf_arms_at_ipos (t : RTree α) (v : IPos t) :
    ∃ (l r : RTree α) (L R U : Finset (Option (List Bool))),
      subAt t (pathOf t v).1 = some (node l r) ∧
      L = (lpaths l).image (fun u => some (((pathOf t v).1 ++ [false]) ++ u)) ∧
      R = (lpaths r).image (fun u => some (((pathOf t v).1 ++ [true]) ++ u)) ∧
      U = atlasLeaves t \ (L ∪ R) ∧
      L.Nonempty ∧ R.Nonempty ∧ U.Nonempty ∧ none ∈ U ∧
      Disjoint L R ∧ Disjoint L U ∧ Disjoint R U ∧
      L ∪ R ∪ U = atlasLeaves t :=
  leaf_arms_atlas (pathOf t v).2

end RTree

end PercLib.CriticalLRP.TreeExpansion
