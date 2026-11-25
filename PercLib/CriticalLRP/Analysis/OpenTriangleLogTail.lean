/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwtrtcqs`, member `m8`, direction D7.

Lemma I.4.3 of Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1, p. 40):

  "If Cases 2 or 3 of (HD) hold then `∇_r` is logarithmically integrable",

where `∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)` is the open-triangle tail of §I.4.1.

The paper's proof produces, in Case 3, the pointwise bound (I.4.13)
`∇(0,x) ⪯ 1 / (log (1 + ‖x‖))^2`, and in Case 2 the polynomial bound (I.4.11)
`∇(0,x) ⪯ ‖x‖^{-d+6}` with `d > 6`.  This file supplies the *analysis* that converts such a
pointwise bound into logarithmic integrability of the tail of the **actual source model**, via the
norm-agnostic lemma `Analysis.isLogErrorFunction_radialTailSup`.

What is proved here: the conditional implication
`pointwise logarithmic bound on ∇(0,·) ⟹ ∇_r is a logarithmically integrable error function`,
at `SourceModelData` with the normalized source norm `M.S.dist 0 ·`, with no restriction to a
window, no compactness, and no use of Kozma's operator-square-root theorem.

What is *not* proved here: the convolution estimate (I.4.12) that produces the pointwise bound.
That remains an explicit hypothesis `hF` / `h`/`hfin` of every theorem below.
-/
module

public import PercLib.CriticalLRP.Analysis.LogTailCore
public import PercLib.CriticalLRP.Analysis.Polygon.Defs

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-- The source tail is *literally* the norm-agnostic radial tail supremum: the model's
`nablaTail` and `Analysis.radialTailSup` are the same `⨆`-expression. -/
theorem nablaTail_eq_radialTailSup (r : ℝ) :
    M.nablaTail r =
      Analysis.radialTailSup (fun y : M.V => M.S.dist 0 y)
        (fun y : M.V =>
          PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) r :=
  rfl

/-- The lattice origin maps to the vector origin. -/
theorem toVec_zero : toVec (0 : M.V) = 0 := by
  funext i
  simp [toVec]

/-- The source norm of the origin is zero, so the tail at a positive radius never sees the
diagonal value `∇(0,0) = ∇_{β_c}`. -/
theorem sdist_zero_zero : M.S.dist 0 (0 : M.V) = 0 := by
  simp [SourceNormData.dist, toVec_zero, M.S.ρ_zero]

/-- A point with positive source norm is not the origin. -/
theorem ne_zero_of_sdist_pos {y : M.V} (hy : 0 < M.S.dist 0 y) : y ≠ 0 := by
  rintro rfl
  rw [sdist_zero_zero] at hy
  exact lt_irrefl 0 hy

/-- **The real-valued tail is the supremum of the real-valued entries.**  Under the pointwise
logarithmic bound the extended-real tail `∇_r` is finite at every `r > 0`, so taking `.toReal`
loses nothing and `∇_r` is literally `sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)` computed in `ℝ`.  This is the
faithfulness statement for the source notation
`∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`. -/
theorem nablaTail_toReal_eq_iSup {C p : ℝ}
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p)
    {r : ℝ} (hr : 0 < r) :
    (M.nablaTail r).toReal =
      ⨆ y : M.V, ⨆ (_ : r ≤ M.S.dist 0 y),
        (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg
          M.betaCrit 0 y).toReal := by
  have hinner : ∀ y : M.V,
      (⨆ (_ : r ≤ M.S.dist 0 y),
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) ≠ ⊤ := by
    intro y
    by_cases h : r ≤ M.S.dist 0 y
    · rw [iSup_pos h]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hF y (lt_of_lt_of_le hr h))
    · simp [h]
  rw [nablaTail_eq_radialTailSup, Analysis.radialTailSup, ENNReal.toReal_iSup hinner]
  refine iSup_congr fun y => ?_
  refine ENNReal.toReal_iSup (fun (h : r ≤ M.S.dist 0 y) => ?_)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hF y (lt_of_lt_of_le hr h))

/-- **Logarithmic integrability of the source open-triangle tail.**

If the uncut open triangle is bounded by `C * (log (1 + ‖y‖)) ^ (-p)` at every nonzero lattice
point, with `p > 1`, then the source tail `r ↦ ∇_r` is a logarithmically integrable error
function: `∫^∞ ∇_r dr / r < ∞` and `∇_r → 0`.

This is the `ℝ≥0∞`-valued form of the hypothesis, which additionally controls `⊤`; use
`isLogErrorFunction_nablaTail_of_toReal_le` for the faithful real-valued (I.4.13) form. -/
theorem isLogErrorFunction_nablaTail {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  have := Analysis.isLogErrorFunction_radialTailSup (nrm := fun y : M.V => M.S.dist 0 y)
    (F := fun y : M.V =>
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) hC hp hF
  simpa only [nablaTail_eq_radialTailSup] using this

/-- **The faithful real-valued hypothesis.**  A pointwise bound on the *real* values of the open
triangle, together with finiteness of those values, gives the `ℝ≥0∞` bound used above.
The finiteness hypothesis is not cosmetic: `ENNReal.toReal` sends `⊤` to `0`, so a real-valued
bound alone carries no information about an infinite value. -/
theorem logRadialBound_of_toReal_le {C p : ℝ}
    (h : ∀ y : M.V, y ≠ 0 →
      (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
        ≤ Analysis.logMajorant C p (M.S.dist 0 y))
    (hfin : ∀ y : M.V, y ≠ 0 →
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤) :
    Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p := by
  intro y hy
  have hy0 : y ≠ 0 := ne_zero_of_sdist_pos M hy
  change PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y
      ≤ ENNReal.ofReal (Analysis.logMajorant C p (M.S.dist 0 y))
  rw [← ENNReal.ofReal_toReal (hfin y hy0)]
  exact ENNReal.ofReal_le_ofReal (h y hy0)

/-- **Lemma I.4.3, conditional on the source pointwise bound in its real-valued form.**

Given the pointwise bound `∇_{β_c}(0,y) ≤ C / (log (1 + ‖y‖))^p` for every nonzero lattice point
(with finite values and `p > 1`), the source open-triangle tail `∇_r` is a logarithmically
integrable error function. -/
theorem isLogErrorFunction_nablaTail_of_toReal_le {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (h : ∀ y : M.V, y ≠ 0 →
      (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
        ≤ Analysis.logMajorant C p (M.S.dist 0 y))
    (hfin : ∀ y : M.V, y ≠ 0 →
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) :=
  isLogErrorFunction_nablaTail M hC hp (logRadialBound_of_toReal_le M h hfin)

/-- **The open-triangle condition follows from the pointwise bound.**

Under the same pointwise logarithmic bound the source tail itself tends to `0` in `ℝ≥0∞`, i.e.
`∇_r → 0`.  This is the conclusion Kozma's theorem reaches from the triangle condition by an
operator argument; here it is read off from *uniform pointwise decay*, which is a strictly stronger
input — exactly the input that (I.4.13) supplies in Case 3 of `(HD)`. -/
theorem tendsto_nablaTail_zero {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Tendsto (fun r => M.nablaTail r) atTop (𝓝 0) := by
  have hof : Tendsto (fun r => ENNReal.ofReal (Analysis.logMajorant C p r)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (Analysis.tendsto_logMajorant_zero (C := C) (by linarith))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof
    (Eventually.of_forall fun r => zero_le) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  rw [nablaTail_eq_radialTailSup]
  exact Analysis.radialTailSup_le_logMajorant hC (by linarith) (by linarith) hF

/-! ### Case 2 of `(HD)`: polynomial decay suffices -/

/-- **`∇_r` is a logarithmically integrable error function under polynomial decay.**  This is the
Case 2 half of Lemma I.4.3: if `∇_{β_c}(0,y) ⪯ ‖y‖ ^ (-a)` with `a > 0` (the paper's (I.4.11)
gives `a = d - 6 > 0` when `d > 6`), no logarithmic correction is needed. -/
theorem isLogErrorFunction_nablaTail_of_pow {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (h : ∀ y : M.V, y ≠ 0 →
      (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
        ≤ Analysis.powMajorant C a (M.S.dist 0 y))
    (hfin : ∀ y : M.V, y ≠ 0 →
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  have hpow : Analysis.PowRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C a := by
    intro y hy
    have hy0 : y ≠ 0 := ne_zero_of_sdist_pos M hy
    change PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y
        ≤ ENNReal.ofReal (Analysis.powMajorant C a (M.S.dist 0 y))
    rw [← ENNReal.ofReal_toReal (hfin y hy0)]
    exact ENNReal.ofReal_le_ofReal (h y hy0)
  simpa only [nablaTail_eq_radialTailSup] using
    Analysis.isLogErrorFunction_radialTailSup_pow (nrm := fun y : M.V => M.S.dist 0 y)
      (F := fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
      hC ha hpow

end PercLib.CriticalLRP.Orchestration.SourceModelData
