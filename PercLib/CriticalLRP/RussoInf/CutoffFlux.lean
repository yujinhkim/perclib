/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Instantiation for the cut-off model and the capped cluster-volume functional

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.1.

This file puts the abstract finite-pivotal-flux theorem
(`tsum_abs_pivotalFlux_le`) on the two objects of the paper:

* the `r`-derivative of the cut-off edge probability
  `q_e(r) = 1 - exp(-β J_r(e))` of Definition I.1.5, whose per-vertex mass is at
  most `β|J'(r)| (2⌈r⌉₊ + 1)^d` (the degree bound of the cut-off graph);
* the capped cluster-volume functional
  `g_{p,n,m}(ω) = min(((min(|K_o|, n))^p, m)`, which is bounded, measurable and
  a function of the cluster of `o`.

The conclusion is that the pivotal flux of the capped cluster moment is
absolutely summable as soon as `E|K_o|` is finite.
-/
module

public import PercLib.CriticalLRP.RussoInf.FluxMain
public import PercLib.CriticalLRP.KernelGeometry
public import PercLib.CriticalLRP.LatticeGeometry
public import PercLib.CriticalLRP.CountableProduct.Marks

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

namespace CutoffFlux

variable {d : ℕ}

/-- The `r`-derivative of the cut-off edge probability
`q_e(r) = 1 - exp(-β J_r(e))`, at edges of length at most `r` (and `0` beyond). -/
noncomputable def cutoffEdgeDeriv (K : ℝ → ℝ) (β K' r : ℝ) (e : Sym2 (Fin d → ℤ)) : ℝ :=
  if (FiniteVolume.edgeLen e : ℝ) ≤ r then
    β * K' * (1 - longRangeEdgeProbability β
      (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)))
  else 0

/-- The derivative weight is dominated by `β|J'(r)|` on the active edges. -/
theorem abs_cutoffEdgeDeriv_le {β K' r : ℝ} (hβ : 0 ≤ β) (hK' : 0 ≤ K') {K : ℝ → ℝ}
    (hq0 : ∀ e : Sym2 (Fin d → ℤ),
      0 ≤ longRangeEdgeProbability β
        (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)))
    (hq1 : ∀ e : Sym2 (Fin d → ℤ),
      longRangeEdgeProbability β
        (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)) ≤ 1)
    (e : Sym2 (Fin d → ℤ)) :
    |cutoffEdgeDeriv K β K' r e|
      ≤ β * K' * (if (FiniteVolume.edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0) := by
  unfold cutoffEdgeDeriv
  by_cases h : (FiniteVolume.edgeLen e : ℝ) ≤ r
  · rw [ite_eq_left h, ite_eq_left h, abs_of_nonneg]
    · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hβ hK')
      linarith [hq0 e]
    · exact mul_nonneg (mul_nonneg hβ hK') (by linarith [hq1 e])
  · rw [ite_eq_right h, ite_eq_right h, abs_zero, mul_zero]

/-- **The per-vertex degree bound for the cut-off derivative weights.** -/
theorem cutoff_edgeDeriv_degree {β K' r : ℝ} (hβ : 0 ≤ β) (hK' : 0 ≤ K') {K : ℝ → ℝ}
    (hq0 : ∀ e : Sym2 (Fin d → ℤ),
      0 ≤ longRangeEdgeProbability β
        (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)))
    (hq1 : ∀ e : Sym2 (Fin d → ℤ),
      longRangeEdgeProbability β
        (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)) ≤ 1) :
    ∀ x : Fin d → ℤ, ∀ u : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ u, |cutoffEdgeDeriv (d := d) K β K' r e|
          * (if x ∈ e then (1 : ℝ) else 0)
        ≤ β * K' * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ) := by
  intro x u
  refine le_trans (Finset.sum_le_sum fun e _ => ?_)
    (FiniteVolume.sum_activeWeight_incident_le x r (β * K') (mul_nonneg hβ hK') u)
  exact mul_le_mul_of_nonneg_right
    (abs_cutoffEdgeDeriv_le hβ hK' hq0 hq1 e) (by positivity)

end CutoffFlux

/-! ## The capped cluster-volume functional -/

/-- The capped cluster-volume functional `min(((min(|K_o|, n))^p, m)`, a bounded functional of the
cluster of `o`. -/
noncomputable def cappedClusterVol {V : Type*} (o : V) (p : ℕ) (n m : ℝ) (ω : Config V) : ℝ :=
  min ((((clusterVol ω o ⊓ ENNReal.ofReal n).toReal) ^ p)) m

theorem cappedClusterVol_bound {V : Type*} (o : V) (p : ℕ) (n m : ℝ) (hm : 0 ≤ m) :
    ∀ ω : Config V, |cappedClusterVol o p n m ω| ≤ max m 0 := by
  intro ω
  have h1 : cappedClusterVol o p n m ω ≤ m := min_le_right _ _
  have h2 : 0 ≤ cappedClusterVol o p n m ω :=
    le_min (by positivity) hm
  rw [abs_of_nonneg h2]
  exact h1.trans (le_max_left _ _)

theorem measurable_cappedClusterVol {V : Type*} [Countable V] (o : V) (p : ℕ) (n m : ℝ) :
    Measurable (cappedClusterVol (V := V) o p n m) := by
  have h : Measurable fun ω : Config V => clusterVol ω o := measurable_clusterVol o
  exact Measurable.min ((((h.inf measurable_const).ennreal_toReal).pow_const p)) measurable_const

theorem cappedClusterVol_dep {V : Type*} [Countable V] (o : V) (p : ℕ) (n m : ℝ) :
    ∀ ω η : Config V, cluster ω o = cluster η o →
      cappedClusterVol o p n m ω = cappedClusterVol o p n m η := by
  intro ω η h
  unfold cappedClusterVol clusterVol
  rw [show PercLib.Percolation.Bond.cluster ω o = PercLib.Percolation.Bond.cluster η o from h]

end PercLib.CriticalLRP
