/-
Integrated and independently rebuilt from accepted Ultramath `smwytmnfc`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwytmnfc`, member `m2`, direction d1, integrated at production base
`1ec5a682a47b12ced34931ce440a902cc4924184`.

# The source second-moment excluded error `𝓔_{2,r}` at the actual radial cutoff model

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, display (I.4.16) and the two definitions preceding it:

```
          |B_r| E|K| E|K|²  −  E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]
  E_{2,r} := ----------------------------------------------------
                       |B_r| E|K| E|K|²
```

and, using `∑_{y∈B_r}|K_y|² = ∑ 1(y∉K)|K_y|² + |K| #(K ∩ B_r)`,

```
          |B_r| E|K| E|K|²  −  E[|K| ∑_{y∈B_r} |K_y|²]  +  E[|K|³ |K ∩ B_r|]
  E_{2,r} = ---------------------------------------------------------------------
                              |B_r| E|K| E|K|²
```

with the *normalized* error `Ē_{2,r}` of (I.4.14)/(I.4.15)

```
  1 − Ē_{2,r} = (1 − E_{2,r}) (1 + H_r) (1 − E_{0,r}),
```

`H_r` the first-moment defect of Section I.4.1.

## What this file defines

The objects live in the `SourceModelData` namespace (mirroring the accepted first-moment packet
`PivotFlux.cutE0`/`PivotFlux.cutE1` of `Analysis/Cutoff/FluxODE/Defs.lean`), so that they are
reachable by dot notation as `M.p2ExclError`, `M.p2Ebar`, ... like `M.cutMoment` and `M.p2RHS`:

* `p2WindowProduct` — the denominator `|B_r| E|K| E|K|²` as an `ℝ≥0∞` (never truncated);
* `p2ExclError` — `𝓔_{2,r}` as a *real* number, obtained from the existing algebraic object
  `VolumeMoments.cE2` applied to the real cutoff moments `E_{b_c,r}|K|`, `E_{b_c,r}|K|²` and the
  real excluded window mass `E_{b_c,r}[|K|∑ 1(y∉K)|K_y|²]`;
* `p2H` — the source's `H_r := (β_c/α) r^{-α} E_{b_c,r}|K| − 1`;
* `p2Ebar` — `Ē_{2,r} = 1 − (1 − E_{2,r})(1 + H_r)(1 − E_{0,r})`, with `E_{0,r}` the model's own
  `PivotFlux.cutE0` (so `1 − E_{0,r} = |J'(r)| |B_r| r^{α+1}`);
* `p2Flux` — the (I.4.14) derivative value `β_c |J'(r)| · M.p2RHS r` in `ℝ`, i.e. the real
  second-moment flux before the pivoting identity; `M.rhsScalarTwo` is the same object written
  with `β_c(-K'(r))`, and `rhsScalarTwo_eq_p2Flux` (`Normalized.lean`) identifies the two for
  `0 < r`, using the accepted `M.deriv_K_nonpos`.

Nothing here asserts any asymptotic statement: `E_{2,r} → 0`, `H_r → 0`, `E_{0,r} → 0` are
*inputs* of the results in `Normalized.lean`, never derived from boundedness.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Covariance
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs
public import PercLib.CriticalLRP.VolumeMoments.ErrorTerms
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.Analysis.Cutoff.RowSum
public import PercLib.CriticalLRP.Analysis.Cutoff.MixedFluxDensityMonotone
public import PercLib.CriticalLRP.Analysis.ModelSecondMomentRV

/-! # Second-moment error: Defs -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The denominator and the two displayed forms of `𝓔_{2,r}` -/

/-- The denominator `|B_r| E_{β_c,r}|K| E_{β_c,r}|K|²` of (I.4.16), as an `ℝ≥0∞`.  The closed
window `B_r` is the model's own `M.ball r` and its cardinality is the finite `ncard`; no
truncation of any moment is performed. -/
def p2WindowProduct (r : ℝ) : ℝ≥0∞ :=
  ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r

/-- **The source second-moment excluded error `𝓔_{2,r}` of (I.4.16)**, as the real number

`(|B_r| E|K| E|K|² − E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]) / (|B_r| E|K| E|K|²)`.

This is the existing algebraic object `VolumeMoments.cE2` evaluated at the model's genuine
cutoff moments and excluded window mass.  The `ℝ≥0∞ → ℝ` conversion is made once, here, by
`ENNReal.toReal`; the theorems in `Bounds.lean` state exactly which finiteness hypotheses make
the conversion faithful (never a `⊤ ↦ 0` shortcut). -/
def p2ExclError (r : ℝ) : ℝ :=
  VolumeMoments.cE2 ((M.cutMoment 1 r).toReal) ((M.cutMoment 2 r).toReal)
    ((M.exclMassQuad r).toReal) ((M.ball r).ncard : ℝ)

/-- **The source's `H_r`** of Section I.4.1, `(β_c/α) r^{-α} E_{β_c,r}|K| − 1`, written in the
equivalent form `E|K| / ((α/β_c) r^α) − 1` so that `E|K| = (α/β_c) r^α (1 + H_r)` is an
identity rather than an estimate (`p2H_normalizes` in `Normalized.lean`). -/
def p2H (r : ℝ) : ℝ :=
  (M.cutMoment 1 r).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) - 1

/-- **The normalized second-moment error `Ē_{2,r}` of (I.4.15)**,

`1 − Ē_{2,r} = (1 − E_{2,r}) (1 + H_r) (1 − E_{0,r})`,

with `E_{0,r}` the model's own `PivotFlux.cutE0`, i.e. `1 − E_{0,r} = |J'(r)| |B_r| r^{α+1}`.
The convention is the one used for the first moment: `Ē` is *defined* by
`1 − Ē := (1−E_2)(1+H)(1−E_0)`, so that (I.4.15) reads `d/dr E|K|² = 3α(1 − Ē) r^{-1} E|K|²`. -/
def p2Ebar (r : ℝ) : ℝ :=
  1 - VolumeMoments.oneSubEbar2 (p2ExclError M r) (p2H M r) |deriv M.K r|
    ((M.ball r).ncard : ℝ) r M.α

/-- The `p = 2` derivative value of (I.4.14) in `ℝ`: `β_c |J'(r)| · M.p2RHS r`, where
`M.p2RHS r` is the source's `p = 2` right-hand side without the prefactor.  By
`p2Flux_eq_three_mul_exclMassQuad` this is `3 β_c |J'(r)| E[|K|∑ 1(y∉K)|K_y|²]`. -/
def p2Flux (r : ℝ) : ℝ :=
  (M.betaCrit : ℝ) * |deriv M.K r| * (M.p2RHS r).toReal

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
