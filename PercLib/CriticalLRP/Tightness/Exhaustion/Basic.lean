/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Exhaustion passage from finite subgraphs to a countable graph

Source: T. Hutchcroft, *Power-law bounds for critical long-range percolation below the
upper-critical dimension*, arXiv:2008.11197v2, proof of Theorem 2.3: "The infinite cases of
(2.8) and (2.9) follow straightforwardly from the finite cases by passing to the limit in an
exhaustion over finite subgraphs."

This file isolates that passage. No percolation estimate is proved here: the finite-subgraph
bound is an explicit hypothesis, and the only probabilistic input is the monotone continuity of
a measure along an increasing sequence of events
(`MeasureTheory.tendsto_measure_iUnion_atTop`).  Monotonicity in the running index is enough,
so no measurability of the approximating stages is required.
-/
module

public import PercLib.CriticalLRP.Tightness.MaxCluster

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace Exhaustion

/-! ## Abstract monotone transfer -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Monotone transfer, power form.**  If `μ (E i) ≤ (μ (F i)) ^ c` holds at every stage of an
increasing sequence, it holds in the limit. -/
theorem tendsto_pow_transfer {E F : ℕ → Set Ω} {E' F' : Set Ω} (hE : Monotone E) (hF : Monotone F)
    (hEun : E' = ⋃ i, E i) (hFun : F' = ⋃ i, F i) {c : ℕ}
    (h : ∀ i, μ (E i) ≤ (μ (F i)) ^ c) : μ E' ≤ (μ F') ^ c := by
  have hmain : μ (⋃ i, E i) ≤ (μ (⋃ i, F i)) ^ c := by
    refine le_of_tendsto_of_tendsto (MeasureTheory.tendsto_measure_iUnion_atTop (μ := μ) hE)
      tendsto_const_nhds (Eventually.of_forall fun i => ?_)
    exact (h i).trans (ENNReal.pow_le_pow_left (measure_mono (subset_iUnion F i)))
  simpa only [hEun, hFun] using hmain

/-- **Monotone transfer, product form** (the shape of (2.9)): a bound of the form
`μ (E i) ≤ (μ (F i)) ^ c * μ (G i)` passes to the limit. -/
theorem tendsto_prod_transfer {E F G : ℕ → Set Ω} {E' F' G' : Set Ω} (hE : Monotone E)
    (hF : Monotone F) (hG : Monotone G) (hEun : E' = ⋃ i, E i) (hFun : F' = ⋃ i, F i)
    (hGun : G' = ⋃ i, G i) {c : ℕ} (h : ∀ i, μ (E i) ≤ (μ (F i)) ^ c * μ (G i)) :
    μ E' ≤ (μ F') ^ c * μ G' := by
  have hmain : μ (⋃ i, E i) ≤ (μ (⋃ i, F i)) ^ c * μ (⋃ i, G i) := by
    refine le_of_tendsto_of_tendsto (MeasureTheory.tendsto_measure_iUnion_atTop (μ := μ) hE)
      tendsto_const_nhds (Eventually.of_forall fun i => ?_)
    refine (h i).trans (mul_le_mul' ?_ ?_)
    · exact ENNReal.pow_le_pow_left (measure_mono (subset_iUnion F i))
    · exact measure_mono (subset_iUnion G i)
  simpa only [hEun, hFun, hGun] using hmain

end Abstract

end Exhaustion

end PercLib.CriticalLRP
