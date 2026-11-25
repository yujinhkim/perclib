/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Interface.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Bridge

/-!
# Consumer interface for the I.4.16 combinatorial step

This file adds the arithmetic and adjacency facts that a consumer of
`exists_hub_edge_partition_ipos` needs when it turns the edge partition into factors of the
moment bound of Lemma I.4.16:

* `three_mul_le_two_mul_sub_one` — for `k ≤ ⌈(p-1)/2⌉` and `p ≥ 2` one has `3k ≤ 2p - 1`, so
  the natural-number expression `2p - 1 - 3k` for the number of remaining edges is the honest
  difference and not truncated subtraction (the decomposition statements are phrased in `ℕ`);
* `exponent_bookkeeping` — `3k + (2p - 1 - 3k) = 2p - 1`: counting the `3k` edges of the
  `k` stars and the `2p - 1 - 3k` remaining edges gives back the full `2p - 1` atlas edges;
* `moment_exponent` — `2p - 1 - k = 2k + (2p - 1 - 3k)`: at each of the `k` hubs a
  three-point function `E|K|^2` replaces three copies of `E|K|`, so `k` in-cluster factors
  (order `2` each) and `2p - 1 - 3k` two-point factors (order `1` each) have total order
  `2p - 1 - k`, one less than the ordinary tree-graph exponent `2p - 1` per hub;
* `not_parent_child_of_same_parity` — two distinct internal vertices of one depth parity are
  never parent and child, the graph-theoretic content of "the 3-stars of a one-class hub set
  are disjoint".

None of these mention probability: the BK step itself is not formalised here (see the
README).
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-! ### Arithmetic of the exponents -/

/-- `⌈(p-1)/2⌉` in the form used by `numLeaves`. -/
theorem ceil_half_eq (p : ℕ) : (p - 1 + 1) / 2 = p / 2 := by
  omega

/-- For `p ≥ 2` and `k ≤ ⌈(p-1)/2⌉` the number `3k` of edges in the stars never exceeds the
number `2p - 1` of atlas edges.  In particular `2 * p - 1 - 3 * k` is a genuine difference in
`ℕ` and not truncated subtraction. -/
theorem three_mul_le_two_mul_sub_one {p k : ℕ} (hp : 2 ≤ p) (hk : k ≤ (p - 1 + 1) / 2) :
    3 * k ≤ 2 * p - 1 := by
  rw [ceil_half_eq] at hk
  have h2 : 2 * k ≤ p := by omega
  omega

/-- The exponent bookkeeping of Lemma I.4.16: `k` stars of three edges and `2p - 1 - 3k`
remaining edges account for all `2p - 1` atlas edges, which is the exponent `2p - 1` of
`E|K|` in the ordinary tree-graph inequality. -/
theorem exponent_bookkeeping {p k : ℕ} (hp : 2 ≤ p) (hk : k ≤ (p - 1 + 1) / 2) :
    3 * k + (2 * p - 1 - 3 * k) = 2 * p - 1 := by
  have h := three_mul_le_two_mul_sub_one hp hk
  omega

/-- The moment exponent: `k` in-cluster factors of order `2` and `2p - 1 - 3k` two-point
factors of order `1` have total order `2p - 1 - k`, one less per hub than the ordinary
tree-graph exponent `2p - 1`. -/
theorem moment_exponent {p k : ℕ} (hp : 2 ≤ p) (hk : k ≤ (p - 1 + 1) / 2) :
    2 * p - 1 - k = 2 * k + (2 * p - 1 - 3 * k) := by
  have h := three_mul_le_two_mul_sub_one hp hk
  have hk1 : k ≤ 2 * p - 1 := by omega
  omega

/-! ### Digital version over a tree -/

/-- The conjunction of the previous three facts at an atlas with `t.numLeaves ≥ 2` leaves. -/
theorem atlas_arithmetic (t : RTree α) (ht : 2 ≤ t.numLeaves) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    3 * k ≤ 2 * t.numLeaves - 1 ∧
      3 * k + (2 * t.numLeaves - 1 - 3 * k) = 2 * t.numLeaves - 1 ∧
      2 * t.numLeaves - 1 - k = 2 * k + (2 * t.numLeaves - 1 - 3 * k) :=
  ⟨three_mul_le_two_mul_sub_one ht hk, exponent_bookkeeping ht hk, moment_exponent ht hk⟩

/-! ### Same-parity vertices are not adjacent -/

/-- Two distinct internal vertices of the same depth parity are never parent and child. -/
theorem not_parent_child_of_same_parity {s s' : List Bool}
    (hpar : s.length % 2 = s'.length % 2) (hne : s ≠ s') :
    s ≠ s'.dropLast ∧ s' ≠ s.dropLast := by
  constructor
  · intro h
    have hne' : s' ≠ [] := by
      rintro rfl
      exact hne (by rw [h]; rfl)
    have hlen := length_eq_dropLast_succ hne'
    rw [← h] at hlen
    exact mod_two_ne_mod_two_succ s.length (by rw [hlen] at hpar; exact hpar)
  · intro h
    have hsne : s ≠ [] := by
      rintro rfl
      exact hne (by rw [h]; rfl)
    have hlen := length_eq_dropLast_succ hsne
    rw [← h] at hlen
    exact mod_two_ne_mod_two_succ s'.length (by rw [hlen] at hpar; exact hpar.symm)

end RTree

end PercLib.CriticalLRP.TreeExpansion
