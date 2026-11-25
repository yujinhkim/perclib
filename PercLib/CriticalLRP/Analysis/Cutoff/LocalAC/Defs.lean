/-
# Candidate definitions: hypothesis predicates for the integrable-majorant AC theory

Direction D3 (member `m7`, swarm `smwtrtcqs`), analysis only.  These are the only *new
mathematical definitions* of this packet; `LocalIntegrableAC.lean` contains the theorems.

The point of the three predicates is to isolate, as named hypotheses, exactly the data that the
reflexivity (monotone/antitone comparison) proof of the mean-value inequality with a variable
majorant consumes, so that the *regularity* demanded of the majorant `g` can be stated in its
weakest usable form:

* `PrimitiveDerivativeMajorant g a b` — the primitive of `g` has derivative `g u` at *every*
  interior point of the window.  This is what the comparison argument actually uses.  It is
  implied by continuity of `g` on the window (the hypothesis of the previously landed
  `IntervalAC.lean`), but it is strictly weaker: it only constrains `g` through its integral.
* `ContinuousAtOff g a b D` — `g` is continuous at every interior point outside the finite set
  `D`.  Allows genuine discontinuities (poles) at finitely many radii.
* `DerivBoundOff f g a b D` — `f` is differentiable at every interior point outside `D`, with
  `|f'| ≤ g` there.  This is the shape of the Russo-formula output.

Nothing here asserts that any particular model satisfies these predicates.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace PercLib.CriticalLRP.LocalAC

/-- The primitive of `g` has derivative `g u` at every interior point of the window `(a,b)`.

This is the exact hypothesis consumed by the antitone/monotone comparison in the mean-value
inequality for a radially varying majorant.  Continuity of `g` on `[a,b]` implies it
(`hasDerivAt_primitive_of_continuousAt` and `ContinuousOn.continuousAt`), but not conversely. -/
def PrimitiveDerivativeMajorant (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ u ∈ Ioo a b, HasDerivAt (fun s => ∫ t in a..s, g t) (g u) u

/-- `g` is continuous at every interior point of the window `(a,b)` outside the finite set `D`. -/
def ContinuousAtOff (g : ℝ → ℝ) (a b : ℝ) (D : Finset ℝ) : Prop :=
  ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) → ContinuousAt g u

/-- `f` is differentiable, with `|f'| ≤ g`, at every interior point of `(a,b)` outside the finite
set `D`.  No derivative is claimed at the points of `D`. -/
def DerivBoundOff (f g : ℝ → ℝ) (a b : ℝ) (D : Finset ℝ) : Prop :=
  ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) → DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u

/-- The step function `1_{(0,∞)}`: the witness that continuity of `f` cannot be dropped from the
incremental bound (it is differentiable with derivative `0` off the finite set `{0}`, but not
absolutely continuous). -/
noncomputable def stepFun : ℝ → ℝ := fun t => if 0 < t then 1 else 0

/-- The majorant `1` except at the single interior radius `0`: an interval-integrable majorant that
is continuous at every interior point outside `{0}` but not continuous on the closed window. -/
noncomputable def unitPole : ℝ → ℝ := fun t => if t = 0 then 0 else 1

end PercLib.CriticalLRP.LocalAC
