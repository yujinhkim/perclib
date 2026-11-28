/-
Ultramath swarm `smwzlje3f`, member `m6`, direction `d6` (campaign direction (B)).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m6/Defs.lean`.

# Named finite-moment propositions for the Case-3 wrapper

`SourceModelData.secondMoment_asymptotic_case3_of_source_p21`
(`PercLib/CriticalLRP/Analysis/SecondMomentCase3/ProductGap/SourceConsumer.lean`, production
commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`) retains, among its explicit model-level
inputs,

* `h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤`,
* `h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤`,
* `hβ : (M.betaCrit : ℝ) ≠ 0`,

where `M.cutMoment p r = ∫⁻ ω, |K_0(ω)| ^ p ∂(M.cutLaw r)` is the `p`-th moment of the cluster
volume of the origin in the range-cutoff model at `β_c` (`Orchestration/Defs.lean`).

This file only *names* the propositions behind those inputs, so that a derivation or a retained
residual can be stated in one line and audited against the source.  No theorem is asserted here.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs

/-! # Finite cutoff moment propositions -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- The literal `h1` input of the Case-3 wrapper: the first cutoff moment is finite on the tail
`[r₀, ∞)`.  `M.cutMoment 1 r = M.cutMassAt r 0` (`cutMassAt_zero_eq_cutMoment`), so this is the
finiteness of the cutoff susceptibility `χ(r)`. -/
def CutoffMomentsFinite (r₀ : ℝ) : Prop := ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤

/-- The literal `h2` input of the Case-3 wrapper: the second cutoff moment is finite on
`[r₀, ∞)`. -/
def CutoffSecondMomentsFinite (r₀ : ℝ) : Prop := ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤

/-- Every positive cutoff moment of `|K_0|` is finite at every positive radius.  This is the
statement that the whole cutoff-moment family is finite, not just the first two orders. -/
def AllCutoffMomentsFinite : Prop :=
  ∀ r : ℝ, 0 < r → ∀ q : ℕ, 1 ≤ q → M.cutMoment q r ≠ ⊤

/-- The `hMa` shape of the `I420Case3` consumers (`case3_hAend_hAmid_cutPoly_source_of_HD_case3_*`),
written with `M.cutMoment` and the `ℓ + 1` shift of `(I.4.19)`;
`powMomentAt_cutProb_eq_cutMoment` identifies it with the literal `I420Case1.powMomentAt` form. -/
def RootMomentsFiniteUpTo (p : ℕ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p → M.cutMoment (ℓ + 1) r ≠ ⊤

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
