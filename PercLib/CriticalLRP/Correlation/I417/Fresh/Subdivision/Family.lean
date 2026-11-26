/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Compose
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Poly

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# The finite coefficient-weighted diagram bound in the printed normalisation

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (supplied PDF pp. 45--46): the two-copy expansion produces tree
diagrams with `2p+2q+1` edges, `ℓ` of them on the `x`--`y` path, `3 ≤ ℓ ≤ p+q+1`, and `C_{p,q,ℓ}`
of them for each `ℓ`, each worth `χ^(2p+2q+1-ℓ) T^ℓ(x,y)`.

This file sums the pointwise composed-diagram bound `marked_fresh_le` over a finite family
and groups it by the composed depth `ℓ = ℓ₁ + ℓ₂`:

  `composed_family_le` — a finite family of (marked base, subdivided fresh) diagram pairs, with
  base depths `ℓ₁ ∈ [2, p+1]` and fresh depths `ℓ₂ ∈ [1, q]`, satisfies

    `∑_i base_i · fresh_i ≤ ∑_{ℓ ∈ [3, p+q+1]} C_ℓ · χ^(2p+2q+1-ℓ) · T^ℓ(x,y)`,

  `C_ℓ = #{i ∈ S | ℓ₁ i + ℓ₂ i = ℓ}` a finite cardinality.

Both ends of the range and the exponent normalisation are *derived*, not assumed:
`composed_depth_range`, `base_marked_depth_range`,
`subW_depth_le_numLeaves`.

**What is not provided here.**  This is a diagram-level bound for a family supplied by the consumer.
Turning it into a statement about the random configuration still needs (i) the event-level cover of
`I417Gen.freshMark` by the subdivided-edge family at general `q` (the combinatorics; member `m1`'s
direction) and (ii) the passage from the event cover to the diagram sum (union bound, BK per shape,
and the interchange of the `w`-sum with the family sum).  Production supplies the second half's
ingredients at `q ≤ 2` (`I417FreshTwo`) and the BK machinery (`TreeExpansion`); no probabilistic
claim is made or implied here.
-/

open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh.Subdivision

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Base

universe u

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **The finite coefficient-weighted composed diagram bound.**  Summing `marked_fresh_le` over a
finite family and grouping by the composed depth `ℓ₁+ℓ₂` gives the printed normalisation

  `∑_{ℓ ∈ [3, p+q+1]} C_ℓ · χ^(2p+2q+1-ℓ) · T^ℓ(x,y)`,

with `C_ℓ` the number of members whose composed depth equals `ℓ`.  The coefficient is a
cardinality, the range is proved, and no term is discarded: in particular the `ℓ = p+q+1` term can
be nonzero (`comb_subW_max`), and there is no `C_ℓ` at `ℓ < 3`. -/
theorem composed_family_le {α β : Type u} {ι : Type*} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (p q : ℕ) (S : Finset ι)
    (tb : ι → RTree α) (qm : (i : ι) → (tb i).LeafPos)
    (tf : ι → RTree β) (qf : (i : ι) → (tf i).LeafPos) (ℓ₂ : ι → ℕ) (w : ι → V) (x y : V)
    (hbase : ∀ i ∈ S, (tb i).numLeaves = p + 1)
    (hfresh : ∀ i ∈ S, (tf i).numLeaves = q)
    (h1a : ∀ i ∈ S, 2 ≤ RTree.depth (tb i) (qm i))
    (h2a : ∀ i ∈ S, 1 ≤ ℓ₂ i)
    (h2b : ∀ i ∈ S, ℓ₂ i ≤ RTree.depth (tf i) (qf i)) :
    (∑ i ∈ S, (∑' z : (tb i).LeafPos → V, (if z (qm i) = w i then 1 else 0) * wtE k (tb i) z x) *
        subW k (tf i) (qf i) (ℓ₂ i) (w i) y)
      ≤ ∑ ℓ ∈ Finset.Icc 3 (p + q + 1),
          ((S.filter (fun i => RTree.depth (tb i) (qm i) + ℓ₂ i = ℓ)).card : ℝ≥0∞) *
            (χ ^ (2 * p + 2 * q + 1 - ℓ) * iterPow k ℓ x y) := by
  classical
  -- depth side conditions, per member
  have hℓ₁le : ∀ i ∈ S, RTree.depth (tb i) (qm i) ≤ p + 1 := by
    intro i hi
    have h := RTree.depth_le_numLeaves (tb i) (qm i)
    have hb := hbase i hi
    omega
  have hℓ₂le : ∀ i ∈ S, ℓ₂ i ≤ q := by
    intro i hi
    have h := RTree.depth_le_numLeaves (tf i) (qf i)
    have hf := hfresh i hi
    have h2 := h2b i hi
    omega
  -- the pointwise bound
  have hpt : ∀ i ∈ S,
      (∑' z : (tb i).LeafPos → V, (if z (qm i) = w i then 1 else 0) * wtE k (tb i) z x) *
          subW k (tf i) (qf i) (ℓ₂ i) (w i) y
        ≤ χ ^ (2 * p + 2 * q + 1 - (RTree.depth (tb i) (qm i) + ℓ₂ i)) *
            iterPow k (RTree.depth (tb i) (qm i) + ℓ₂ i) x y :=
    fun i hi => marked_fresh_le k χ hχ p q (tb i) (qm i) (tf i) (qf i) (ℓ₂ i) (hbase i hi)
      (hfresh i hi) (h1a i hi) (h2a i hi) (h2b i hi) x (w i) y
  refine le_trans (Finset.sum_le_sum hpt) ?_
  -- group the family by the composed depth
  have hm : ∀ i ∈ S, RTree.depth (tb i) (qm i) + ℓ₂ i < p + q + 2 := by
    intro i hi
    have h1 := hℓ₁le i hi
    have h2 := hℓ₂le i hi
    omega
  rw [finset_sum_by_fiber S
    (fun ℓ => χ ^ (2 * p + 2 * q + 1 - ℓ) * iterPow k ℓ x y)
    (fun i => RTree.depth (tb i) (qm i) + ℓ₂ i) (p + q + 2) hm]
  -- cut `range (p+q+2)` down to `Icc 3 (p+q+1)`
  refine le_of_eq (Finset.sum_subset ?hsub ?hzero).symm
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    exact Finset.mem_range.mpr (by omega)
  · intro ℓ hℓmem hℓ
    simp only [Finset.mem_range] at hℓmem
    have hnot : ¬(3 ≤ ℓ ∧ ℓ ≤ p + q + 1) := by
      intro hc
      exact hℓ (Finset.mem_Icc.mpr hc)
    have hemp : S.filter (fun i => RTree.depth (tb i) (qm i) + ℓ₂ i = ℓ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i hi heq
      have h1 := hℓ₁le i hi
      have h2 := hℓ₂le i hi
      have h3 := h1a i hi
      have h4 := h2a i hi
      exact hnot ⟨by omega, by omega⟩
    rw [hemp]
    simp

end PercLib.CriticalLRP.I417Fresh.Subdivision
