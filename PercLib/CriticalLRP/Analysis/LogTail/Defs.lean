/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Candidate mathematical definitions for swarm `smwtrtcqs`, member `m8`, direction D7
("logarithmically integrable open-triangle tail").

These are the only new objects introduced by this packet.  Every theorem about them lives in
`LogTailCore.lean` (norm-agnostic analysis) and `OpenTriangleLogTail.lean` (the model
application); neither of those files introduces a new definition.
-/
module

public import Mathlib

@[expose] public section

open Set
open scoped ENNReal

namespace PercLib.CriticalLRP.Analysis

/-- The **logarithmic majorant profile** `r ↦ C * (log (1 + r)) ^ (-p)`.

This is the shape of the pointwise bounds produced by the logarithmic-correction convolution
estimate (I.4.12) in Case 3 of `(HD)`: there `τ ∗ τ` and `∇(0,·)` are bounded by
`C / (log (1 + ‖·‖)) ^ 2`, i.e. `p = 2`.  Any `p > 1` already gives logarithmic integrability of
the antitone tail.  The profile is deliberately *not* identified with any kernel value. -/
noncomputable def logMajorant (C p r : ℝ) : ℝ := C * Real.log (1 + r) ^ (-p)

/-- The **power majorant profile** `r ↦ C * r ^ (-a)`, the shape of the polynomial bound (I.4.11)
of Case 2 of `(HD)` (`a = d - 6`), as opposed to the logarithmic profile `logMajorant`. -/
noncomputable def powMajorant (C a r : ℝ) : ℝ := C * r ^ (-a)

/-- `LogRadialBound nrm F C p` records the pointwise source-type decay hypothesis

`F x ≤ C * (log (1 + nrm x)) ^ (-p)` **at positive radius only**.

The restriction `0 < nrm x` is essential and not a convenience: the source bound is an estimate
for `x ≠ 0`, while the diagonal value `F 0` is the triangle diagram itself and is not small.  All
tail suprema below are taken at radii `r > 0`, so they never see the diagonal. -/
def LogRadialBound {ι : Type*} (nrm : ι → ℝ) (F : ι → ℝ≥0∞) (C p : ℝ) : Prop :=
  ∀ x : ι, 0 < nrm x → F x ≤ ENNReal.ofReal (logMajorant C p (nrm x))

/-- The **radial tail supremum** `sup {F x | r ≤ nrm x}`, the norm-agnostic form of the source's

`∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`.

It is an `ℝ≥0∞` supremum, so it is antitone in `r` with no hypothesis on `nrm` or `F` and with no
nonemptiness convention: an empty supremum is `0`.  For the model's normalized source norm it
coincides definitionally with `SourceModelData.nablaTail`. -/
noncomputable def radialTailSup {ι : Type*} (nrm : ι → ℝ) (F : ι → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  ⨆ x : ι, ⨆ (_ : r ≤ nrm x), F x

/-- `PowRadialBound nrm F C a` is the polynomial-decay analogue of `LogRadialBound`: `F` is at
most `C * (nrm x) ^ (-a)` at positive radius.  This is the hypothesis shape supplied by (I.4.11)
(Case 2 of `(HD)`, `a = d - 6 > 0`). -/
def PowRadialBound {ι : Type*} (nrm : ι → ℝ) (F : ι → ℝ≥0∞) (C a : ℝ) : Prop :=
  ∀ x : ι, 0 < nrm x → F x ≤ ENNReal.ofReal (powMajorant C a (nrm x))

end PercLib.CriticalLRP.Analysis
