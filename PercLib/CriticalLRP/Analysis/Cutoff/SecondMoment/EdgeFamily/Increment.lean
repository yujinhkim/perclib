/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The quadratic edge weight is the exact increment of `|K_o|²`

Swarm `smwvc1d9z`, member `m2`, direction `d1`

Integration donor: `.ultramath/smwvc1d9z/m2`; independently reviewed at
`a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f` after one connectivity-composition repair in `Count.lean`..  The proof is the donor proof of swarm
`smwvbcnfb` member `m2` (`.ultramath/smwvbcnfb/m2/EdgeToVertex.lean`, section 2), re-stated
against this package's definition module `Defs.lean` and re-checked under the strict linter set.
The donor's `s(x,y) ∉ ω` hypothesis is dropped: the identity below holds for **every**
configuration, because an open edge connects its two endpoints, so both orientations of the
edge carry weight `0` while the increment is `0` as well (`cluster_union_singleton_eq`).

The content: for distinct `x y` and any configuration `ω`, opening the edge `{x,y}` changes the
square of the root cluster volume by exactly the unordered edge weight,

  `|K_o(ω ∪ {s(x,y)})|² = |K_o ω|² + quadEdgeWeight dt ω o s(x,y)`,

an identity of extended cardinalities with no finiteness hypothesis.  The four endpoint cases
are: both endpoints in `K_o` → weight `0`; only `x` → `2|K_o||K_y| + |K_y|²`; only `y` →
`2|K_o||K_x| + |K_x|²`; neither → `0`.

**Not claimed:** no `toReal` conversion (`|K| = ⊤` is handled inside `ℝ≥0∞`), no radius
derivative, and no interchange of any sum with this identity.  The identity is pointwise.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Count

/-!
# Exactness of the quadratic edge weight

`clusterVol_sq_union_pair_eq_add_quadEdgeWeight`: the unordered edge weight is the exact
increment of `|K_o|²` at a single edge.  This is the pointwise half of the `p = 2` edge ledger;
the count `sum_sum_mul_quadPairWeight` is the other half.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Finset
open scoped ENNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The volume of the cluster of a member of the root's cluster is the root's volume. -/
theorem clusterVol_eq_of_mem_cluster {ω : Config V} {o y : V} (hy : y ∈ cluster ω o) :
    clusterVol ω y = clusterVol ω o := by
  rw [clusterVol_eq_encard, clusterVol_eq_encard, cluster_eq_of_mem_cluster hy]

/-- **Evaluation of the oriented weight at a member of the root's cluster.**  The factor
`|K_b|` may be replaced by `|K_o|`. -/
theorem quadPairWeight_eq_of_connects (dt : V → V → Prop) (ω : Config V) (o : V) {b c : V}
    (hb : Connects ω o b) :
    quadPairWeight dt ω o b c
      = (if dt c b then (1 : ℝ≥0∞) else 0) * (if ¬ Connects ω b c then 1 else 0) *
          (2 * clusterVol ω o * clusterVol ω c + clusterVol ω c ^ 2) := by
  have hK : clusterVol ω b = clusterVol ω o := clusterVol_eq_of_mem_cluster (mem_cluster_iff.mpr hb)
  simp only [quadPairWeight, hK]
  rw [ite_eq_left hb, one_mul]

/-- The volume identity of the merge with the roles of the two endpoints exchanged. -/
theorem clusterVol_union_pair_eq_symm {ω : Config V} {o x y : V} (hxy : x ≠ y)
    (hy : y ∈ cluster ω o) (hx : x ∉ cluster ω o) :
    clusterVol (ω ∪ {s(x, y)}) o = clusterVol ω o + clusterVol ω x := by
  have h := clusterVol_union_pair_eq (ω := ω) (o := o) hxy.symm hy hx
  simpa [Sym2.eq_swap] using h

/-- **The exact quadratic increment of a single edge.**  For `x ≠ y` and *any* configuration,
opening the edge `{x,y}` changes `|K_o|²` by exactly the unordered edge weight of `{x,y}`. -/
theorem clusterVol_sq_union_pair_eq_add_quadEdgeWeight (dt : V → V → Prop)
    {ω : Config V} {o x y : V} (hxy : x ≠ y) (hdt : dt y x) (hdt' : dt x y) :
    (clusterVol (ω ∪ {s(x, y)}) o) ^ 2
      = (clusterVol ω o) ^ 2 + quadEdgeWeight dt ω o s(x, y) := by
  rw [quadEdgeWeight_mk]
  by_cases hx : x ∈ cluster ω o
  · by_cases hy : y ∈ cluster ω o
    · -- both endpoints inside the cluster: the merge changes nothing
      have hKx : cluster ω x = cluster ω o := cluster_eq_of_mem_cluster hx
      have hyx' : y ∈ cluster ω x := by rw [hKx]; exact hy
      have hKy : cluster ω y = cluster ω o := cluster_eq_of_mem_cluster hy
      have hxy' : x ∈ cluster ω y := by rw [hKy]; exact hx
      rw [quadPairWeight_eq_zero_of_connects dt ω o (mem_cluster_iff.mp hyx'),
        quadPairWeight_eq_zero_of_connects dt ω o (mem_cluster_iff.mp hxy'),
        add_zero, clusterVol_union_pair_eq_of_mem_cluster hxy hx hy, add_zero]
    · -- only `x` inside
      have hxo : Connects ω o x := (mem_cluster_iff (v := o) (w := x)).mp hx
      have hxc : ¬ Connects ω x y := fun h => hy (mem_cluster_iff.mpr (connects_trans hxo h))
      rw [quadPairWeight_eq_of_connects dt ω o hxo, ite_eq_left hxc,
        quadPairWeight_eq_zero_of_not_connects dt ω o hy,
        add_zero, clusterVol_union_pair_eq hxy hx hy, add_sq_ennreal, ite_eq_left hdt]
      ring
  · by_cases hy : y ∈ cluster ω o
    · -- only `y` inside
      have hyo : Connects ω o y := (mem_cluster_iff (v := o) (w := y)).mp hy
      have hyc : ¬ Connects ω y x := fun h => hx (mem_cluster_iff.mpr (connects_trans hyo h))
      rw [quadPairWeight_eq_zero_of_not_connects dt ω o hx,
        quadPairWeight_eq_of_connects dt ω o hyo, ite_eq_left hyc,
        zero_add, clusterVol_union_pair_eq_symm hxy hy hx, add_sq_ennreal, ite_eq_left hdt']
      ring
    · -- neither inside: the edge does not touch the cluster
      have ht : s(x, y) ∉ touchSet ω o := notMem_touchSet_pair hx hy
      rw [quadPairWeight_eq_zero_of_not_connects dt ω o hx,
        quadPairWeight_eq_zero_of_not_connects dt ω o hy,
        add_zero, clusterVol_eq_encard, clusterVol_eq_encard, cluster_union_singleton_eq ht,
        add_zero]

end PercLib.CriticalLRP
