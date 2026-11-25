/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/

module
public import PercLib.CriticalLRP.Analysis.Polygon.TailConstant
public import PercLib.CriticalLRP.Analysis.LogScaling
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_13

/-!
# Log-error scaling of the polygon tail
-/

namespace PercLib.CriticalLRP.Analysis

open PercLib.CriticalLRP Orchestration

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

/-- Evaluating an extended-real-valued log-error function at a positive power preserves the
error property, including both logarithmic integrability and convergence to zero. No decay
beyond the input hypothesis is inferred. -/
theorem isLogErrorFunction_toReal_comp_rpow {f : ℝ → ℝ≥0∞}
    (hh : IsLogErrorFunction (fun r => (f r).toReal)) {c : ℝ} (hc : 0 < c) :
    IsLogErrorFunction (fun r => (f (r ^ c)).toReal) := by
  refine ⟨?_, ?_⟩
  · simpa only [one_mul] using logarithmicallyIntegrable_comp_rpow_const_mul
      (fun r => (f r).toReal) hh.1 (C := 1) hc one_pos
  · exact hh.2.comp (tendsto_rpow_atTop hc)

/-- The polygon's additive tail term is a logarithmic error if the model-tail term itself is
one. The exponent is not probabilistic exponentiation of a tail: `nablaTail (r^c)` is the
source supremum evaluated at radius `r^c`. -/
theorem isLogErrorFunction_nablaTail_add_rpow_neg
    (M : SourceModelData) (hTail : IsLogErrorFunction (fun r => (M.nablaTail r).toReal))
    {c : ℝ} (hc : 0 < c) :
    IsLogErrorFunction (fun r => (M.nablaTail (r ^ c)).toReal + r ^ (-c)) := by
  have ht := isLogErrorFunction_toReal_comp_rpow hTail hc
  have hr : IsLogErrorFunction (fun r : ℝ => r ^ (-c)) := by
    simpa only [one_mul] using isLogErrorFunction_const_rpow_neg (a := c) hc (c := 1) one_pos
  simpa only [one_mul] using isLogErrorFunction_add ht hr
