/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The exact edge-to-vertex identity for the `p = 2` quadratic edge family

Swarm `smwvc1d9z`, member `m2`, direction `d1`

Integration donor: `.ultramath/smwvc1d9z/m2`; independently reviewed at
`a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f` after one connectivity-composition repair in `Count.lean`..

`Count.lean` proves the finite `2`-to-`1` count
`∑_{b ∈ B} ∑_{c ∈ B} h {b,c} · quadPairWeight b c = ∑_{e ∈ B.sym2} h e · quadEdgeWeight e`.
This file passes that count to the full infinite families, with no series interchange beyond the
`ℝ≥0∞` supremum formulation and no finiteness hypothesis:

* `exists_finset_sym2_subset` — every finite set of edges is contained in `B.sym2` for some
  finite vertex set `B` (take the union of the endpoint sets);
* `iSup_sum_sym2_eq_iSup_sum_prod` — the two finite-sum families have the same supremum;
* `tsum_quadEdgeWeight_eq_tsum_quadPairWeight` — **the edge-to-vertex identity**
  `∑' e : Sym2 V, quadEdgeWeight e = ∑' b, ∑' c, quadPairWeight b c`,
  and its product form `tsum_quadEdgeWeight_eq_tsum_prod`.

The `2` is not an average: the two ordered pairs `(b,c)` and `(c,b)` are summed separately, and
the diagonal `(b,b)` contributes `0` on both sides.  Everything is stated for an arbitrary range
predicate `dt`, an arbitrary configuration and root, and holds in `ℝ≥0∞` without hypotheses.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Count

/-!
# From the finite count to the infinite edge-to-vertex identity

The main result is `tsum_quadEdgeWeight_eq_tsum_quadPairWeight`: the `ℝ≥0∞`-valued `tsum` of
the unordered edge weights is the double `tsum` of the oriented endpoint-pair weights.  It is
obtained as the equality of the suprema of the finite restrictions, using the finite count
`sum_sym2_quadEdgeWeight` on both sides, so no interchange of a sum with an integral and no
summability hypothesis is involved.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Finset
open scoped ENNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-- Every finite set of edges is contained in the symmetric square of a finite vertex set: the
union of the endpoint sets. -/
theorem exists_finset_sym2_subset (t : Finset (Sym2 V)) : ∃ B : Finset V, t ⊆ B.sym2 := by
  classical
  refine ⟨t.biUnion (fun e => e.toFinset), fun e he => ?_⟩
  rw [Finset.mem_sym2_iff]
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr ha⟩

/-- **Cofinality of the edge windows.**  The supremum of the finite edge sums equals the
supremum of the finite ordered-pair sums: this is the `2`-to-`1` count passing to the limit of
finite restrictions. -/
theorem iSup_sum_sym2_eq_iSup_sum_prod (dt : V → V → Prop) (ω : Config V) (o : V) :
    (⨆ B : Finset V, ∑ e ∈ B.sym2, quadEdgeWeight dt ω o e)
      = ⨆ t : Finset (V × V), ∑ p ∈ t, quadPairWeight dt ω o p.1 p.2 := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup_le fun B => ?_
    have hprod : (∑ p ∈ B ×ˢ B, quadPairWeight dt ω o p.1 p.2)
        = ∑ b ∈ B, ∑ c ∈ B, quadPairWeight dt ω o b c := by
      rw [Finset.sum_product]
    rw [sum_sym2_quadEdgeWeight, ← hprod]
    exact le_iSup (fun t : Finset (V × V) => ∑ p ∈ t, quadPairWeight dt ω o p.1 p.2) (B ×ˢ B)
  · refine iSup_le fun t => ?_
    set B : Finset V := t.image Prod.fst ∪ t.image Prod.snd with hB
    have hsub : t ⊆ B ×ˢ B := by
      intro p hp
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_image_of_mem Prod.fst hp)
      · exact Finset.mem_union_right _
          (Finset.mem_image_of_mem Prod.snd hp)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)) ?_
    have hprod : (∑ p ∈ B ×ˢ B, quadPairWeight dt ω o p.1 p.2)
        = ∑ b ∈ B, ∑ c ∈ B, quadPairWeight dt ω o b c := by
      rw [Finset.sum_product]
    rw [hprod, ← sum_sym2_quadEdgeWeight]
    exact le_iSup (fun B : Finset V => ∑ e ∈ B.sym2, quadEdgeWeight dt ω o e) B

/-- **The edge-to-vertex identity.**  The `ℝ≥0∞` sum of the unordered edge weights over the
whole edge family `Sym2 V` equals the double sum of the oriented endpoint-pair weights over all
ordered pairs `(b,c)`.  Unconditional: no finiteness, no summability, no measurability. -/
theorem tsum_quadEdgeWeight_eq_tsum_quadPairWeight (dt : V → V → Prop) (ω : Config V) (o : V) :
    ∑' e : Sym2 V, quadEdgeWeight dt ω o e
      = ∑' b : V, ∑' c : V, quadPairWeight dt ω o b c := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum' (fun B : Finset V => B.sym2) (fun t => exists_finset_sym2_subset t),
    ← ENNReal.tsum_prod, ENNReal.tsum_eq_iSup_sum]
  exact iSup_sum_sym2_eq_iSup_sum_prod dt ω o

/-- The same identity in the shape of a single `tsum` over the product type. -/
theorem tsum_quadEdgeWeight_eq_tsum_prod (dt : V → V → Prop) (ω : Config V) (o : V) :
    ∑' e : Sym2 V, quadEdgeWeight dt ω o e
      = ∑' p : V × V, quadPairWeight dt ω o p.1 p.2 := by
  rw [tsum_quadEdgeWeight_eq_tsum_quadPairWeight, ENNReal.tsum_prod]

end PercLib.CriticalLRP
