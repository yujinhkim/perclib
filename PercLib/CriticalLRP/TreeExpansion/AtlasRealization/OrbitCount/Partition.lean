/-
Independent UltraMath work, swarm `smwwsmqji`, member `m1`.
Production base `50c2eed0682a7e1b078ae771dbef463ebe00701d`, Lean 4.35.0 (read-only package
`.scratch/critical-lrp-orchestration`). Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Defs

/-!
# The child-swap orbits form a finite partition of the fully labelled family

This file proves the structural facts behind the shape count of (I.2.2)/(I.2.3):

* `mem_swapFiber_iff`, `swapFiber_disjoint_or_eq`: distinct orbits are disjoint, and the class of
  a plane tree determines its members;
* `swapOrbits_card`: every orbit of the fully labelled family over `α` has exactly
  `2 ^ (Fintype.card α - 1)` plane representatives (`RTree.card_swapFiber` rewritten);
* `biUnion_swapOrbits`, `sum_swapOrbits_card`: the orbits partition the fully labelled family;
* `card_swapOrbits_mul`, `card_swapOrbits_eq_div`: hence
  `#(orbits) * 2 ^ (#α - 1) = #(RTree.LT α)` exactly, so `#(orbits)` is `#(RTree.LT α)` divided by
  the plane multiplicity — no count is lost and none is invented;
* `card_swapOrbits_fin_le_dfactorial`: for `α = Fin p` this gives `#(orbits) ≤ (2p-3)!!` from
  production's `RTree.card_LT_fin_le`.  The inequality is not claimed to be an equality: the
  reverse inequality is not proved here.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-- All plane representatives of one non-plane tree have the same number of leaves. -/
theorem numLeaves_eq_of_mem_swapFiber [DecidableEq α] {t t' : RTree α} (h : t' ∈ swapFiber t) :
    t'.numLeaves = t.numLeaves :=
  (perm_of_mem_swapFiber h).length_eq

/-- A plane representative of a tree with distinct leaf labels again has distinct leaf labels. -/
theorem nodup_of_mem_swapFiber [DecidableEq α] {t t' : RTree α} (h : t' ∈ swapFiber t)
    (ht : t.leaves.Nodup) : t'.leaves.Nodup :=
  (perm_of_mem_swapFiber h).nodup_iff.mpr ht

/-- Membership determines the orbit, and conversely. -/
theorem mem_swapFiber_iff [DecidableEq α] {s t : RTree α} :
    t ∈ swapFiber s ↔ swapFiber t = swapFiber s := by
  constructor
  · exact swapFiber_congr
  · intro h
    have hmem : t ∈ swapFiber t := swapFiber_self t
    rwa [h] at hmem

/-- Two child-swap orbits are equal or disjoint. -/
theorem swapFiber_disjoint_or_eq [DecidableEq α] (s t : RTree α) :
    swapFiber s = swapFiber t ∨ Disjoint (swapFiber s) (swapFiber t) := by
  by_cases h : (swapFiber s ∩ swapFiber t).Nonempty
  · obtain ⟨u, hu⟩ := h
    rw [Finset.mem_inter] at hu
    exact Or.inl ((swapFiber_congr hu.1).symm.trans (swapFiber_congr hu.2))
  · refine Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr ?_)
    exact Finset.not_nonempty_iff_eq_empty.mp h

variable [Fintype α] [DecidableEq α] [Fintype (LT α)]

/-! ### The orbit family -/

/-- Membership in the orbit family. -/
theorem mem_swapOrbits {S : Finset (RTree α)} :
    S ∈ swapOrbits α ↔ ∃ t : LT α, swapFiber t.val = S := by
  rw [swapOrbits, Finset.mem_image]
  exact ⟨fun ⟨t, _, h⟩ => ⟨t, h⟩, fun ⟨t, h⟩ => ⟨t, Finset.mem_univ t, h⟩⟩

/-- Every orbit is nonempty. -/
theorem swapOrbits_nonempty {S : Finset (RTree α)} (hS : S ∈ swapOrbits α) : S.Nonempty := by
  obtain ⟨t, rfl⟩ := mem_swapOrbits.mp hS
  exact ⟨t.val, swapFiber_self t.val⟩

/-- Every orbit of the fully labelled family has exactly `2 ^ (#α - 1)` plane representatives. -/
theorem swapOrbits_card {S : Finset (RTree α)} (hS : S ∈ swapOrbits α) :
    S.card = 2 ^ (Fintype.card α - 1) := by
  obtain ⟨t, rfl⟩ := mem_swapOrbits.mp hS
  have hnd : t.val.leaves.Nodup := t.2.1
  have hnum : t.val.numLeaves = Fintype.card α := t.2.2
  rw [card_swapFiber t.val hnd, hnum]

/-- The chosen representative of an orbit belongs to it. -/
theorem orbitRep_spec (S : {S : Finset (RTree α) // S ∈ swapOrbits α}) :
    swapFiber (orbitRep α S) = S.1 :=
  (Classical.choose_spec (Finset.mem_image.mp S.2)).2

/-- The chosen representative of an orbit is a member of it. -/
theorem orbitRep_mem (S : {S : Finset (RTree α) // S ∈ swapOrbits α}) :
    orbitRep α S ∈ S.1 := by
  rw [← orbitRep_spec S]
  exact swapFiber_self _

/-- Distinct orbits are disjoint. -/
theorem swapOrbits_pairwiseDisjoint :
    Set.PairwiseDisjoint (swapOrbits α : Set (Finset (RTree α))) id := by
  intro S hS T hT hne
  rcases swapFiber_disjoint_or_eq (orbitRep α ⟨S, hS⟩) (orbitRep α ⟨T, hT⟩) with h | h
  · exact absurd (by rw [orbitRep_spec, orbitRep_spec] at h; simpa using h) hne
  · rwa [orbitRep_spec, orbitRep_spec] at h

/-- The orbits cover the fully labelled family. -/
theorem biUnion_swapOrbits :
    (swapOrbits α).biUnion id = Finset.univ.image (fun t : LT α => t.val) := by
  ext u
  constructor
  · intro hu
    obtain ⟨S, hS, huS⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨t, rfl⟩ := mem_swapOrbits.mp hS
    have hnd : u.leaves.Nodup := nodup_of_mem_swapFiber huS t.2.1
    have hnum : u.numLeaves = Fintype.card α := by
      rw [numLeaves_eq_of_mem_swapFiber huS]
      exact t.2.2
    refine Finset.mem_image.mpr ⟨⟨u, hnd, hnum⟩, Finset.mem_univ _, rfl⟩
  · intro hu
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hu
    refine Finset.mem_biUnion.mpr ⟨swapFiber t.val, mem_swapOrbits.mpr ⟨t, rfl⟩, ?_⟩
    exact swapFiber_self t.val

/-- The orbit cardinalities add up to the number of fully labelled plane trees. -/
theorem sum_swapOrbits_card :
    ∑ S ∈ swapOrbits α, S.card = Fintype.card (LT α) := by
  have h := Finset.card_biUnion (s := swapOrbits α) (t := id) swapOrbits_pairwiseDisjoint
  rw [biUnion_swapOrbits] at h
  rw [Finset.card_image_of_injective (s := (Finset.univ : Finset (LT α)))
    (f := fun t : LT α => t.val) (fun x y hxy => Subtype.ext hxy), Finset.card_univ] at h
  calc ∑ S ∈ swapOrbits α, S.card = ∑ S ∈ swapOrbits α, (id S).card :=
        Finset.sum_congr rfl fun S _ => rfl
    _ = Fintype.card (LT α) := h.symm

/-- **The orbit partition sum.**  Summing a function of the plane tree over the fully labelled
family is the same as summing its orbit sums. -/
theorem sum_LT_eq_sum_orbits (f : RTree α → ℝ) :
    (∑ t : LT α, f t.val) = ∑ S ∈ swapOrbits α, ∑ u ∈ S, f u := by
  have h := Finset.sum_biUnion (s := swapOrbits α) (t := id) (f := f)
    swapOrbits_pairwiseDisjoint
  rw [biUnion_swapOrbits] at h
  rw [Finset.sum_image (s := (Finset.univ : Finset (LT α)))
    (g := fun t : LT α => t.val) (f := f) (fun x _ y _ hxy => Subtype.ext hxy)] at h
  have h' : (∑ S ∈ swapOrbits α, ∑ u ∈ S, f u)
      = ∑ S ∈ swapOrbits α, ∑ u ∈ id S, f u :=
    Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun u _ => rfl
  rw [h']
  exact h

/-- **The exact orbit count.**  The number of child-swap orbits times the plane multiplicity is
the number of plane trees, with no rounding and no loss. -/
theorem card_swapOrbits_mul :
    (swapOrbits α).card * 2 ^ (Fintype.card α - 1) = Fintype.card (LT α) := by
  rw [← sum_swapOrbits_card]
  rw [Finset.sum_congr rfl fun S hS => swapOrbits_card hS]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-- The number of orbits is the plane count divided by the plane multiplicity. -/
theorem card_swapOrbits_eq_div :
    (swapOrbits α).card = Fintype.card (LT α) / 2 ^ (Fintype.card α - 1) := by
  refine Nat.eq_div_of_mul_eq_right (pow_ne_zero _ (by norm_num)) ?_
  rw [mul_comm]
  exact card_swapOrbits_mul

/-! ### The count for `Fin p` -/

/-- **The absolute shape count**: the number of non-plane trees with `p` distinctly labelled
leaves is at most the source double factorial `(2p-3)!!` (`VolumeMoments.M (p-1)`), because the
exact number of plane trees is `2 ^ (p-1)` times it (`RTree.card_LT_fin_le`). -/
theorem card_swapOrbits_fin_le_dfactorial (p : ℕ) :
    (swapOrbits (Fin p)).card ≤ VolumeMoments.M (p - 1) := by
  have hmul : (swapOrbits (Fin p)).card * 2 ^ (p - 1) = Fintype.card (LT (Fin p)) := by
    simpa using card_swapOrbits_mul (α := Fin p)
  have hle : (swapOrbits (Fin p)).card * 2 ^ (p - 1)
      ≤ 2 ^ (p - 1) * VolumeMoments.M (p - 1) := by
    rw [hmul]
    exact card_LT_fin_le p
  have hcancel : (swapOrbits (Fin p)).card * 2 ^ (p - 1)
      ≤ VolumeMoments.M (p - 1) * 2 ^ (p - 1) := by
    rwa [mul_comm (2 ^ (p - 1)) (VolumeMoments.M (p - 1))] at hle
  exact Nat.le_of_mul_le_mul_right hcancel (pow_pos (by norm_num : (0 : ℕ) < 2) _)

/-- The same count as a division: for `p ≥ 1` the number of non-plane trees with `p` labelled
leaves is exactly `#(RTree.LT (Fin p)) / 2 ^ (p-1)`. -/
theorem card_swapOrbits_fin_eq_div (p : ℕ) :
    (swapOrbits (Fin p)).card = Fintype.card (LT (Fin p)) / 2 ^ (p - 1) := by
  simpa using card_swapOrbits_eq_div (α := Fin p)

end RTree

end PercLib.CriticalLRP.TreeExpansion
