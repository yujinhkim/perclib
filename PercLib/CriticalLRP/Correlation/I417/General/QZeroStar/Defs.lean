/-
Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m5`, direction `d2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `q = 0` connected star moment of Lemma I.4.17

This definition supports the exact one-copy `(p+1)`-point expansion of the `q = 0` moment gap.
Its Case-3 instantiation is `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]`.  The tree-count bound that estimates
that star by the `ell=3` and `ell=4` polygon terms is not supplied here.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.General.SourceForm

/-! # Definition of the connected star moment -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The definition -/

/-- **The `q = 0` connected star moment** `E[|K_x|^p 1(x ↔ y)]`, i.e.
`∫⁻ ω, 1(y ∈ K_x(ω)) · |K_x(ω)|^p ∂μ`.  This is the `(p+1)`-point object that the `q = 0`
instance of Lemma I.4.17 bounds from above; it involves a single copy of the configuration. -/
noncomputable def starMoment (π : Sym2 V → unitInterval) (x y : V) (p : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
    Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π)


end PercLib.CriticalLRP.I417Gen
