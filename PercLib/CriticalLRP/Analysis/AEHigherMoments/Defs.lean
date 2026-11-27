/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2): almost-everywhere / off-corner
higher-moment derivative and integration.

Definitions used by the a.e. (off-corner) form of Lemma I.4.22.  The analytic
content lives in `AEIncrement.lean`, `AELemmaI422.lean` and `AEMomentBound.lean`;
this file only fixes the vocabulary so that the hypotheses of the a.e. theorems
are named once and can be compared with the pointwise originals in
`PercLib.CriticalLRP.Analysis.Lemma_I_4_22`.
-/
module

public import Mathlib



/-! # Almost-everywhere higher-moment interface: Defs -/

set_option autoImplicit false

open MeasureTheory Filter Set

@[expose] public section

namespace PercLib.CriticalLRP.Analysis.AE

/-- `f` is absolutely continuous on every compact radius window of the tail `[r₀, ∞)`.

This is the corner-safe regularity that replaces a pointwise derivative hypothesis: it is the
form supplied by `VolumeMoments/FirstMoment/CornerSafe.lean` and derived for the cutoff first
mass from off-corner data in
`Analysis/Cutoff/OffCorner/AeDerivativeHandoff.cutMassReal_absolutelyContinuousOn_of_offCorner`. -/
def AbsolutelyContinuousOnTail (f : ℝ → ℝ) (r₀ : ℝ) : Prop :=
  ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R

/-- The derivative `f'` of `f` exists at almost every radius of the tail `[r₀, ∞)`.

This is the a.e. handoff shape of
`Analysis/Cutoff/OffCorner/AeDerivativeHandoff.ae_hasDerivAt_cutMassAt_toReal`; no derivative is
claimed at the corner radii. -/
def AeHasDerivAtOnTail (f f' : ℝ → ℝ) (r₀ : ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), HasDerivAt f (f' x) x

/-- The one-sided differential comparison `f' ≤ θ (a f + h)/x` holds at almost every radius of
the tail `[r₀, ∞)`.

The pointwise originals (`Analysis.Lemma_I_4_22.normalized_increment_le_of_driving_bound`,
`eventually_ratio_le_of_driving_bound`) assume it at every radius `≥ r₀`; off the corner set it
is only available a.e. -/
def AeDrivingBound (f f' θ h : ℝ → ℝ) (a r₀ : ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), f' x ≤ θ x * (a * f x + h x) / x

end PercLib.CriticalLRP.Analysis.AE
