/-
Independent UltraMath work, swarm `smwwsmqji`, member `m1`.
Production base `50c2eed0682a7e1b078ae771dbef463ebe00701d`, Lean 4.35.0 (read-only package
`.scratch/critical-lrp-orchestration`). Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Partition
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Moment

/-!
# A fundamental domain for child swaps, and the exact transversal tree sum

`OrbitCount/Partition.lean` shows that the child-swap orbits partition the fully labelled plane
family `RTree.LT α` and that every orbit has `2 ^ (#α - 1)` members.  This file uses the chosen
fundamental domain `RTree.transversal α` (exactly one plane representative per orbit) to remove
the plane multiplicity from a shape sum *exactly*:

* `mem_transversal`, `orbitRep_mem_transversal`, `transversal_card`: the transversal is the image
  of the orbit family and has one element per orbit;
* `transversal_spec`: every fully labelled plane tree lies in the child-swap class of exactly one
  transversal element — the "one representative per orbit" index set a union bound over
  isomorphism classes needs;
* `sum_LT_eq_two_pow_mul_sum_transversal`: for any function constant on child-swap orbits,
  `∑_{t : RTree.LT α} f t = 2 ^ (#α - 1) * ∑_{r ∈ transversal α} f r`.  Consequently
  `treeSum_eq_sum_transversal`: the source tree sum `PercLib.CriticalLRP.TreeExpansion.treeSum`
  is exactly the transversal sum of `RTree.wtL`, with no factor `2 ^ (p - 1)`.

What this does **not** do: it is a statement about the shape sum (the weight side) only.  The
probability side needs the transport of an atlas realization across a child swap, which is not
proved here; see `Report.md`.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*} [Fintype α] [DecidableEq α] [Fintype (LT α)]

/-- Membership in the transversal. -/
theorem mem_transversal {r : RTree α} :
    r ∈ transversal α ↔
      ∃ S : {S : Finset (RTree α) // S ∈ swapOrbits α}, orbitRep α S = r := by
  rw [transversal, Finset.mem_image]
  exact ⟨fun ⟨S, _, h⟩ => ⟨S, h⟩, fun ⟨S, h⟩ => ⟨S, Finset.mem_attach _ S, h⟩⟩

/-- The chosen representative of an orbit is a transversal element. -/
theorem orbitRep_mem_transversal (S : {S : Finset (RTree α) // S ∈ swapOrbits α}) :
    orbitRep α S ∈ transversal α :=
  mem_transversal.mpr ⟨S, rfl⟩

/-- The chosen representatives of distinct orbits are distinct. -/
theorem orbitRep_injOn :
    Set.InjOn (orbitRep α) ↑(swapOrbits α).attach := by
  intro S _ T _ hST
  refine Subtype.ext ?_
  rw [← orbitRep_spec S, ← orbitRep_spec T, hST]

/-- The transversal has exactly one element per orbit. -/
theorem transversal_card : (transversal α).card = (swapOrbits α).card := by
  rw [transversal, Finset.card_image_of_injOn orbitRep_injOn, Finset.card_attach]

/-- The transversal has at most `(2p-3)!!` elements for `α = Fin p`. -/
theorem transversal_card_le_dfactorial (p : ℕ) :
    (transversal (Fin p)).card ≤ VolumeMoments.M (p - 1) := by
  rw [transversal_card]
  exact card_swapOrbits_fin_le_dfactorial p

/-- **Every plane tree has exactly one transversal representative of its class.** -/
theorem transversal_spec (t : LT α) :
    ∃! r : RTree α, r ∈ transversal α ∧ t.val ∈ swapFiber r := by
  refine ⟨orbitRep α ⟨swapFiber t.val, mem_swapOrbits.mpr ⟨t, rfl⟩⟩,
    ⟨orbitRep_mem_transversal _, ?_⟩, ?_⟩
  · rw [orbitRep_spec]
    exact swapFiber_self t.val
  · rintro r ⟨hrT, hr⟩
    obtain ⟨S', rfl⟩ := mem_transversal.mp hrT
    have hclass : S'.1 = swapFiber t.val := by
      rw [← orbitRep_spec S']
      exact (mem_swapFiber_iff.mp hr).symm
    rw [show S' = ⟨swapFiber t.val, mem_swapOrbits.mpr ⟨t, rfl⟩⟩ from Subtype.ext hclass]

/-- The orbit sum of a function constant on child-swap classes is the orbit cardinality times
the value at the chosen representative. -/
theorem sum_orbit_eq_card (f : RTree α → ℝ)
    (hf : ∀ t t' : RTree α, t' ∈ swapFiber t → f t' = f t)
    (S : {S : Finset (RTree α) // S ∈ swapOrbits α}) :
    ∑ u ∈ S.1, f u = (S.1.card : ℝ) * f (orbitRep α S) := by
  have hspec : swapFiber (orbitRep α S) = S.1 := orbitRep_spec S
  have hconst : ∀ u ∈ S.1, f u = f (orbitRep α S) := by
    intro u hu
    exact hf (orbitRep α S) u (by rw [hspec]; exact hu)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-- The orbit sum in terms of the plane multiplicity `2 ^ (#α - 1)`. -/
theorem sum_orbit_eq (f : RTree α → ℝ)
    (hf : ∀ t t' : RTree α, t' ∈ swapFiber t → f t' = f t)
    (S : {S : Finset (RTree α) // S ∈ swapOrbits α}) :
    ∑ u ∈ S.1, f u = (2 : ℝ) ^ (Fintype.card α - 1) * f (orbitRep α S) := by
  rw [sum_orbit_eq_card f hf S, swapOrbits_card S.2, Nat.cast_pow, Nat.cast_ofNat]

/-- Summing over the transversal is the same as summing over the orbit family. -/
theorem sum_transversal_eq_sum_orbits (f : RTree α → ℝ) :
    ∑ r ∈ transversal α, f r = ∑ S ∈ (swapOrbits α).attach, f (orbitRep α S) := by
  rw [transversal]
  exact Finset.sum_image (f := f) (g := orbitRep α) orbitRep_injOn

/-- **The plane multiplicity is exactly the orbit size.**  For a function constant on child-swap
classes, the plane sum is `2 ^ (#α - 1)` times the transversal sum. -/
theorem sum_LT_eq_two_pow_mul_sum_transversal (f : RTree α → ℝ)
    (hf : ∀ t t' : RTree α, t' ∈ swapFiber t → f t' = f t) :
    (∑ t : LT α, f t.val)
      = (2 : ℝ) ^ (Fintype.card α - 1) * ∑ r ∈ transversal α, f r := by
  calc (∑ t : LT α, f t.val)
      = ∑ S ∈ swapOrbits α, ∑ u ∈ S, f u := sum_LT_eq_sum_orbits f
    _ = ∑ S ∈ (swapOrbits α).attach, ∑ u ∈ (S : Finset (RTree α)), f u :=
        (Finset.sum_attach _ _).symm
    _ = ∑ S ∈ (swapOrbits α).attach, (2 : ℝ) ^ (Fintype.card α - 1) * f (orbitRep α S) :=
        Finset.sum_congr rfl fun S _ => sum_orbit_eq f hf S
    _ = (2 : ℝ) ^ (Fintype.card α - 1) * ∑ S ∈ (swapOrbits α).attach, f (orbitRep α S) := by
        rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ (Fintype.card α - 1) * ∑ r ∈ transversal α, f r := by
        rw [sum_transversal_eq_sum_orbits f]

/-! ### The weight corollary -/

/-- **The source tree sum is exactly the transversal sum of the tree weight.**  This removes the
plane multiplicity `2 ^ (p-1)` from the shape sum: no factor is lost, and none is left over. -/
theorem treeSum_eq_sum_transversal {V : Type*} [Fintype V]
    (k : V → V → ℝ) (p : ℕ) (hp : 1 ≤ p) (v : V) (x : Fin p → V) :
    treeSum k p v x = ∑ r ∈ transversal (Fin p), RTree.wtL k r x v := by
  classical
  have hplane := Real.sum_wtL_eq_two_pow_mul_treeSum k p hp v x
  have htrans := sum_LT_eq_two_pow_mul_sum_transversal (α := Fin p)
    (fun r => RTree.wtL k r x v) (fun t t' h => wtL_eq_of_mem_swapFiber k t h x v)
  rw [htrans] at hplane
  rw [show (2 : ℝ) ^ (Fintype.card (Fin p) - 1) = (2 : ℝ) ^ (p - 1) by simp] at hplane
  exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hplane).symm

end RTree

end PercLib.CriticalLRP.TreeExpansion
