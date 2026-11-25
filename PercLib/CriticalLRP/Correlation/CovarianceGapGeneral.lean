/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# `lem:BK_disjoint_clusters_covariance`, third display, in the canonical product model

Source: `.scratch/i52/source/Zd_renormalizationHD.tex`, lines 930-951.  For increasing
non-negative `F`, `G` (functions of the clusters of `x` and `y` respectively) with
`E_β F(K_x), E_β G(K_y) < ∞`:

  `E_β[F G 1(x ↮ y)] ≤ E_β F · E_β G`                                              (BK)

and

  `0 ≤ E_β[F G] − E_β F · E_β G ≤ E_β[F G 1(x ↔ y)]`.                              (FKG + BK)

The paper's Lemma `lem:disjoint_connections` is the special case
`F = 1{x↔y'}`, `G = 1{z↔w}` (see `HgapDisjointConnections.lean` for a direct proof).

Here both displays are proved in the canonical countable product model, at the level of
finitely witnessed increasing events determined by the clusters of `x` and of `y`
(`Percolation.FiniteWitness`, `ClusterEvent` from `BK/CanonicalBridge.lean`).  The first is the
existing theorem `edgeMeasure_twoCluster_bk`; the second is new.  The only hypothesis is
`π e < 1`, which that theorem inherits from BK.  No tree-graph inequality is used.
-/
module

public import PercLib.CriticalLRP.Correlation.HgapClusterWeights

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **The upper half of the third display of `lem:BK_disjoint_clusters_covariance`:**

`E[F G] ≤ E F · E G + E[F G 1(x ↔ y)]`.

`{x↮y} ∪ {x↔y}` covers everything; the `{x↮y}` part is bounded by `E F · E G` (BK,
`edgeMeasure_twoCluster_bk`), and `μ(A ∩ B)` is at most the sum of the two parts. -/
theorem edgeMeasure_covariance_gap_upper (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) (hdA : ClusterEvent x A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) (hdB : ClusterEvent y B) :
    (edgeMeasure π).real (A ∩ B) ≤
      (edgeMeasure π).real A * (edgeMeasure π).real B +
        (edgeMeasure π).real (A ∩ B ∩ {ω | Connects ω x y}) := by
  have hbk := edgeMeasure_twoCluster_bk π hπ x y A B hA hfA hdA hB hfB hdB
  have hcover : A ∩ B ⊆
      (A ∩ B ∩ {ω | ¬ Connects ω x y}) ∪ (A ∩ B ∩ {ω | Connects ω x y}) := by
    rintro ω ⟨h1, h2⟩
    by_cases h : Connects ω x y
    · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · exact Or.inl ⟨⟨h1, h2⟩, h⟩
  refine (real_measure_mono π hcover).trans ((real_measure_union_le π _ _).trans ?_)
  linarith [hbk]

/-- **The third display of `lem:BK_disjoint_clusters_covariance`, both halves:**

`0 ≤ E[F G] − E F · E G ≤ E[F G 1(x ↔ y)]`. -/
theorem edgeMeasure_covariance_gap (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (A B : Set (Config V))
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) (hdA : ClusterEvent x A)
    (hB : IsUpperSet B) (hfB : Percolation.FiniteWitness B) (hdB : ClusterEvent y B) :
    0 ≤ (edgeMeasure π).real (A ∩ B) -
          (edgeMeasure π).real A * (edgeMeasure π).real B ∧
      (edgeMeasure π).real (A ∩ B) - (edgeMeasure π).real A * (edgeMeasure π).real B ≤
        (edgeMeasure π).real (A ∩ B ∩ {ω | Connects ω x y}) := by
  have hfkg := edgeMeasure_fkg π A B hA hB hfA hfB
  have hupper := edgeMeasure_covariance_gap_upper π hπ x y A B hA hfA hdA hB hfB hdB
  constructor <;> linarith

end PercLib.CriticalLRP
