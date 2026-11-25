/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Finite first moments and the literal critical parameter.  These are general
kernel-independent transports; no lattice supercriticality is asserted.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Critical

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
set_option autoImplicit false
open scoped ENNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V] {J : Sym2 V → ℝ} {hJ : ∀ e, 0 ≤ J e}

/-- Finite first moments at every vertex prevent almost-sure global percolation. -/
theorem infiniteClusterProb_eq_zero_of_forall_clusterVol_lintegral_lt_top
    {J : Sym2 V → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (h : ∀ v : V, ∫⁻ ω, clusterVol ω v ∂longRangeMeasure J hJ β < ⊤) :
    infiniteClusterProb J hJ β = 0 := by
  have hae : ∀ᵐ ω ∂(longRangeMeasure J hJ β), ∀ v : V, clusterVol ω v < ⊤ := by
    rw [ae_all_iff]
    intro v
    exact ae_lt_top (measurable_clusterVol v) (ne_of_lt (h v))
  have hnull : longRangeMeasure J hJ β {ω : Config V | ∃ v : V, clusterVol ω v = ⊤} = 0 := by
    have hcompl : {ω : Config V | ∃ v : V, clusterVol ω v = ⊤}
        ⊆ {ω : Config V | ¬ ∀ v : V, clusterVol ω v < ⊤} := by
      rintro ω ⟨v, hv⟩ hcontra
      exact absurd (hcontra v) (by rw [hv]; exact not_lt.mpr le_top)
    exact measure_mono_null hcompl (ae_iff.mp hae)
  rw [infiniteClusterProb, existsInfiniteClusterEvent]
  refine measure_mono_null ?_ hnull
  rintro ω ⟨v, hv⟩
  exact ⟨v, hv⟩

/-- A non-percolating parameter bounds the literal critical parameter from below,
provided percolation occurs at some finite parameter. -/
theorem le_criticalBeta_of_not_mem_of_nonempty
    (hne : (criticalBetaSet J hJ).Nonempty) {β : NNReal}
    (h : β ∉ criticalBetaSet J hJ) : β ≤ criticalBeta J hJ := by
  by_contra hnot
  have hba : criticalBeta J hJ < β := lt_of_not_ge hnot
  obtain ⟨a, ha, haβ⟩ := exists_between hba
  have ha_mem := mem_of_criticalBeta_lt hne ha
  have hβ_mem := criticalBetaSet_isUpperSet haβ.le ha_mem
  exact h hβ_mem

/-- The same lower bound from zero global percolation probability. -/
theorem le_criticalBeta_of_infiniteClusterProb_eq_zero_of_nonempty
    (hne : (criticalBetaSet J hJ).Nonempty) {β : NNReal}
    (h : infiniteClusterProb J hJ β = 0) : β ≤ criticalBeta J hJ := by
  apply le_criticalBeta_of_not_mem_of_nonempty hne
  rw [mem_criticalBetaSet_iff, h]
  exact zero_ne_one

/-- Finite first moments at every vertex bound the literal critical parameter from below,
provided percolation occurs at some finite parameter. -/
theorem le_criticalBeta_of_forall_clusterVol_lintegral_lt_top_of_nonempty
    (hne : (criticalBetaSet J hJ).Nonempty) {β : NNReal}
    (h : ∀ v : V, ∫⁻ ω, clusterVol ω v ∂longRangeMeasure J hJ β < ⊤) :
    β ≤ criticalBeta J hJ :=
  le_criticalBeta_of_infiniteClusterProb_eq_zero_of_nonempty hne
    (infiniteClusterProb_eq_zero_of_forall_clusterVol_lintegral_lt_top h)

#print axioms infiniteClusterProb_eq_zero_of_forall_clusterVol_lintegral_lt_top
#print axioms le_criticalBeta_of_not_mem_of_nonempty
#print axioms le_criticalBeta_of_infiniteClusterProb_eq_zero_of_nonempty
#print axioms le_criticalBeta_of_forall_clusterVol_lintegral_lt_top_of_nonempty

end PercLib.CriticalLRP

end
