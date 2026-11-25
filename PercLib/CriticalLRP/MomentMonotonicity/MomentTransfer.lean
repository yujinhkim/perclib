/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# All-order moment transfer along the monotone coupling

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.5 and p. 7: for every `r < ∞` there is
`ε = ε(r) > 0` with `J_r ≤ (1 − ε) J`, hence `P_{β,r} ⪯ P_{(1−ε)β}`.

The existing transports in the repository cover the first moment
(`lintegral_clusterVol_mono_of_le`) and the second (`lintegral_clusterVol_sq_mono_of_le`),
each with its own proof through the connection sums.  The cut-off moment obligation
`hutchcroft.i.1.5.step.cutoffmoments` asks for **every** `p ≥ 1`, so this file proves the
transport once, for an arbitrary measurable increasing functional of the configuration.

## Method

`edgeMeasure π` is the image of the single mark measure under the threshold map
`atParameter π` (`markMeasure_map_atParameter`), and `atParameter π u ⊆ atParameter κ u`
pointwise when `π ≤ κ`.  Hence for any `F` that is monotone for the inclusion order on
`Config V`,

  `∫⁻ F ∂(edgeMeasure π) = ∫⁻ u, F (atParameter π u) ∂(markMeasure V)
                        ≤ ∫⁻ u, F (atParameter κ u) ∂(markMeasure V) = ∫⁻ F ∂(edgeMeasure κ)`,

by `lintegral_map` and a single `lintegral_mono`.  No `tsum`, no BK inequality, no
finiteness hypothesis, and no countability of the level sets of `F` is used.

`clusterVol · o ^ q` is increasing in the configuration for every `q` (`clusterVol_mono`
plus monotonicity of `x ↦ x ^ q` on `ℝ≥0∞`), which yields the all-order transfer both for
the raw edge measures and for the Definition I.1.5 pair `P_{β,r}` / `P_{β(1−ε)}`.

No new definitions, no `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CutoffDominated
public import PercLib.CriticalLRP.CountableProduct.MonotoneMoments
public import PercLib.CriticalLRP.CountableProduct.Compatibility

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## The general monotone transport -/

/-- **Stochastic monotonicity, integrated against an increasing functional.**
If `π ≤ κ` edge by edge and `F : Config V → ℝ≥0∞` is measurable and monotone for the
inclusion order on configurations, then `∫⁻ F ∂P_π ≤ ∫⁻ F ∂P_κ`.

This is the all-orders version of `edgeMeasure_mono_of_le` (which is the case of an
indicator of an increasing event, `F = 1_A`). -/
theorem lintegral_mono_of_le_of_mono {π κ : Sym2 V → unitInterval} (hpq : ∀ e, π e ≤ κ e)
    {F : Config V → ℝ≥0∞} (hF : Measurable F) (hFmono : Monotone F) :
    (∫⁻ ω, F ω ∂(edgeMeasure π)) ≤ ∫⁻ ω, F ω ∂(edgeMeasure κ) := by
  have hπ : (∫⁻ ω, F ω ∂(edgeMeasure π))
      = ∫⁻ u : Sym2 V → ℝ, F (atParameter π u) ∂(markMeasure V) := by
    conv_lhs => rw [← markMeasure_map_atParameter π]
    exact lintegral_map hF (measurable_atParameter π)
  have hκ : (∫⁻ ω, F ω ∂(edgeMeasure κ))
      = ∫⁻ u : Sym2 V → ℝ, F (atParameter κ u) ∂(markMeasure V) := by
    conv_lhs => rw [← markMeasure_map_atParameter κ]
    exact lintegral_map hF (measurable_atParameter κ)
  rw [hπ, hκ]
  refine lintegral_mono fun u => hFmono fun e he => ?_
  exact lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (hpq e))

/-- Monotonicity of the cluster volume in the configuration: the form `Monotone` needs. -/
theorem clusterVol_mono' {ω ω' : Config V} (h : ω ≤ ω') (v : V) :
    clusterVol ω v ≤ clusterVol ω' v :=
  clusterVol_mono h v

/-- The `q`-th cluster moment is increasing in the edge probabilities, for every `q : ℕ`. -/
theorem lintegral_clusterVol_pow_mono_of_le {π κ : Sym2 V → unitInterval}
    (hpq : ∀ e, π e ≤ κ e) (o : V) (q : ℕ) :
    (∫⁻ ω, clusterVol ω o ^ q ∂(edgeMeasure π))
      ≤ ∫⁻ ω, clusterVol ω o ^ q ∂(edgeMeasure κ) :=
  lintegral_mono_of_le_of_mono hpq ((measurable_clusterVol o).pow_const q)
    (fun _ _ hab => pow_le_pow_left' (clusterVol_mono' hab o) q)

/-- The `p`-th cluster moment is increasing in the edge probabilities, for every real
`p ≥ 0`. -/
theorem lintegral_clusterVol_rpow_mono_of_le {π κ : Sym2 V → unitInterval}
    (hpq : ∀ e, π e ≤ κ e) (o : V) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ ω, clusterVol ω o ^ p ∂(edgeMeasure π))
      ≤ ∫⁻ ω, clusterVol ω o ^ p ∂(edgeMeasure κ) :=
  lintegral_mono_of_le_of_mono hpq ((measurable_clusterVol o).pow_const p)
    (fun _ _ hab => ENNReal.rpow_le_rpow (clusterVol_mono' hab o) hp)

/-! ## The first and second moments are the cases `q = 1`, `q = 2` of the general transport -/

example {π κ : Sym2 V → unitInterval} (hpq : ∀ e, π e ≤ κ e) (o : V) :
    (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))
      ≤ ∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ) := by
  simpa only [pow_one] using lintegral_clusterVol_pow_mono_of_le hpq o 1

example {π κ : Sym2 V → unitInterval} (hpq : ∀ e, π e ≤ κ e) (o : V) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π))
      ≤ ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ) := by
  simpa only [pow_two] using lintegral_clusterVol_pow_mono_of_le hpq o 2

/-! ## Definition I.1.5: transfer to the cut-off law at every order -/

namespace CutoffMomentTransfer

open FiniteVolume CutoffKernel CutoffLimit TreeExpansion PercLib.CriticalLRP.CutoffDominated

variable {d : ℕ} {K : ℝ → ℝ}

/-- **All-order moment domination by the subcritical uncut law** (Definition I.1.5,
p. 7): for `r ≥ 1` the `q`-th cluster moment of the cut-off law `P_{β,r}` is at most the
`q`-th cluster moment of the uncut law at the reduced parameter `β(1 − K r / K 1)`.

Nothing is assumed about either moment: the statement holds in `ℝ≥0∞`, with the value
`⊤` allowed on both sides, so it is not a conditional bound disguised as an identity. -/
theorem cutoff_lintegral_clusterVol_pow_le (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ) (q : ℕ) :
    (∫⁻ ω, clusterVol ω o ^ q ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg' hK d r) β))
      ≤ ∫⁻ ω, clusterVol ω o ^ q ∂(longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1))) :=
  lintegral_clusterVol_pow_mono_of_le
    (cutoff_edgeComparison hK hKnn hK0 hr hKr hK1 β) o q

/-- **Finiteness transfer at every order.**  A finite `q`-th moment of the uncut law at the
reduced parameter bounds the `q`-th moment of the cut-off law at `β`.  This is the step
that lets `hutchcroft.i.1.5.step.cutoffmoments` consume a moment bound for the dominating
(subcritical) law; it produces no such bound itself. -/
theorem cutoff_lintegral_clusterVol_pow_ne_top (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ) (q : ℕ)
    (hfin : (∫⁻ ω, clusterVol ω o ^ q ∂(longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)))) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o ^ q ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg' hK d r) β)) ≠ ⊤ :=
  ne_top_of_le_ne_top hfin
    (cutoff_lintegral_clusterVol_pow_le hK hKnn hK0 hr hKr hK1 β o q)

/-- The same transfer in the `p = 1` case, for comparison with the committed
`CutoffDominated.lintegral_clusterVol_cutoff_le`. -/
theorem cutoff_lintegral_clusterVol_le (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg' hK d r) β))
      ≤ ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1))) := by
  simpa only [pow_one] using cutoff_lintegral_clusterVol_pow_le hK hKnn hK0 hr hKr hK1 β o 1

end CutoffMomentTransfer

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.lintegral_mono_of_le_of_mono
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_pow_mono_of_le
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_rpow_mono_of_le
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.cutoff_lintegral_clusterVol_pow_le
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.cutoff_lintegral_clusterVol_pow_ne_top
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.cutoff_lintegral_clusterVol_le
