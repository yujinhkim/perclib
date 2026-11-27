/-
Integrated and independently rebuilt from accepted Ultramath `smwyue9wx`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwyue9wx`, member `m2`, direction d2 (Case 3 of Proposition I.4.15).

# The Case-3 driver of the second-moment error

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 3 (p. 47):

```
                          (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^4
                E_{2,r} ⪯ -----------------------------------
                             E_{β_c,r}|K| E_{β_c,r}|K|^2
```

The numerator of that display is produced from the paper's Lemma I.4.17 at `p = 3`, `q = 0`
(summed over the window `B_r`) together with the polygon estimate of Lemma I.4.18, which is
available at this base as
`I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii`
(`ℓ ≥ 4`) and `I418C.source_polyK_three_le_small_radius` (`ℓ = 3`, small radii).  The single
factor carrying the decay is therefore the *driver*

  `M.case3Driver c r = (M.nablaTail (r ^ c)).toReal + r ^ (-c)`,

i.e. exactly the bracket `∇_{r^c} + r^{-c}` of the source: `M.nablaTail` is the model's own
supremum tail of the uncut open triangle (not a proxy), evaluated at the radius `r ^ c`.

This file only introduces that name and its elementary properties (nonnegativity at positive
radius and the log-error property inherited from
`Analysis.isLogErrorFunction_nablaTail_add_rpow_neg`).  No asymptotic statement is made here;
`Case3.lean` carries the case's theorems.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentError.Normalized
public import PercLib.CriticalLRP.Analysis.TailLogIntegration

/-! # Definitions for the Case-3 second-moment error driver -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 decay driver `∇_{r^c} + r^{-c}`** of the proof of Proposition I.4.15: the model's
own uncut open-triangle tail `M.nablaTail` evaluated at the radius `r ^ c`, plus the polynomially
small additive term `r ^ (-c)`. -/
def case3Driver (c r : ℝ) : ℝ := (M.nablaTail (r ^ c)).toReal + r ^ (-c)

/-- The driver is nonnegative at positive radius. -/
theorem case3Driver_nonneg {c r : ℝ} (hr : 0 < r) : 0 ≤ M.case3Driver c r := by
  have h1 := M.nablaTail_toReal_nonneg (r ^ c)
  have h2 : (0 : ℝ) ≤ r ^ (-c) := (Real.rpow_pos_of_pos hr (-c)).le
  simp only [case3Driver]
  linarith

/-- The driver is nonnegative whenever the additive term is (in particular for `1 ≤ r`). -/
theorem case3Driver_nonneg_of_one_le {c r : ℝ} (hr : 1 ≤ r) : 0 ≤ M.case3Driver c r :=
  M.case3Driver_nonneg (lt_of_lt_of_le one_pos hr)

/-- **The per-vertex connected third window moment** `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]`, the summand
of the Case-3 numerator `M.connCubeMass r = E_{β_c,r}[|K_0|³ |K_0 ∩ B_r|]` (`E1Sign.ballF M r` is
the window as a finite set).  This is the object to which the source's Lemma I.4.17 at `p = 3`,
`q = 0` applies, one window vertex at a time. -/
def connCubeVertexMass (r : ℝ) (y : M.V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ 3 *
    (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(M.cutLaw r)

/-- **The driver is a logarithmic error function**: it is logarithmically integrable and tends to
zero.  This is `Analysis.isLogErrorFunction_nablaTail_add_rpow_neg`, i.e. Lemma I.4.18's tail
statement together with Lemma I.4.19; the hypothesis `hTail` is the model's own open-triangle
logarithmic tail. -/
theorem isLogErrorFunction_case3Driver
    (hTail : Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal)) {c : ℝ} (hc : 0 < c) :
    Analysis.IsLogErrorFunction (M.case3Driver c) :=
  Analysis.isLogErrorFunction_nablaTail_add_rpow_neg M hTail hc

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
