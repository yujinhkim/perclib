/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` FLUX identity: from the per-edge flux law to the edge sum

Swarm `smwvctsvt`, member `m2`, direction `d1`.

Integration donor: `.ultramath/smwvctsvt/m2`; independently checked at `1c0e4b0dd9575c3ef811ef57e2669b0e8387a1fa`.

`PerEdge.lean` proves the exact real-valued per-edge law

  `cutEdgeClosedWeight r e · pivotalFlux (M.cutLaw r) |K_0|² e
     = ∫ ω, (quadEdgeWeight (ω) 0 e).toReal`

for **every** unordered edge `e` of the cut-off model, with no boundedness or summability
hypothesis.  This file sums it over the edge family and identifies the result with the
vertex-side `p = 2` right-hand side, which is the remaining `p = 2` FLUX identity of the
critical long-range percolation project at a fixed radius.

## The chain

Writing `μ = M.cutLaw r` and `Q_e = quadEdgeWeight (·) 0 e`:

1. `∑'_e closedWeight e · pivotalFlux e = ∑'_e ∫ ω, (Q_e ω).toReal ∂μ` — the per-edge law.
2. Each term is `(∫⁻ ω, Q_e ω ∂μ).toReal`, because `Q_e` is almost surely finite
   (`ae_clusterVol_ne_top`, from the source's first-moment hypothesis) and nonnegative.
3. `∑'_e (∫⁻ Q_e).toReal = (∑'_e ∫⁻ Q_e).toReal` — `ENNReal.tsum_toReal_eq`, whose hypothesis
   `∀ e, ∫⁻ Q_e ≠ ⊤` is *proved* from the `EdgeFamily` exhaustion
   `∫⁻ ω, ∑'_e Q_e ω = M.p2RHS r`.
4. `∑'_e ∫⁻ Q_e = ∫⁻ ω, ∑'_e Q_e ω` — Tonelli in `ℝ≥0∞` (`MeasureTheory.lintegral_tsum`), no
   summability and no real exchange.
5. `∫⁻ ω, ∑'_e Q_e ω = M.p2RHS r` — the landed `EdgeFamily` exhaustion
   `lintegral_tsum_quadEdgeWeight_eq_p2RHS`.
6. `(M.p2RHS r).toReal = ∫ ω, (p2PaperSum r ω).toReal ∂μ` — the landed real-valued bridge
   `PivotFlux.integral_toReal_p2PaperSum`, under the explicit finiteness `M.p2RHS r ≠ ⊤`.

## What is claimed

* `tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_integral_toReal_p2PaperSum` — the FLUX identity.
* `tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo` — its `cutEdgeDeriv`/`coeffRHS` form,
  i.e. the exact `p = 2` derivative value `∑'_e cutEdgeDeriv r e · pivotalFlux e = rhsScalarTwo r`
  at a fixed radius.
* `p2RHS_ne_top_of_firstMoment` — the finiteness hypothesis `M.p2RHS r ≠ ⊤` is not extra: it is
  the landed `SecondMoment/Finiteness.p2RhsMass_ne_top` under the model's kernel regularity.

## What is *not* claimed

No differentiation in the radius: `r` is a fixed parameter throughout.  In particular there is
no two-sided derivative statement at an attained radius, and no shell term is claimed to vanish.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Flux.PerEdge
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Coeff
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Finiteness

/-!
# The `p = 2` FLUX identity at a fixed radius
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

/-! ## 1. The `p = 2` edge family in `ℝ≥0∞` -/

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The quadratic edge weight is almost surely finite as soon as every cluster volume is
almost surely finite. -/
theorem ae_quadEdgeWeight_ne_top (M : SourceModelData) (r : ℝ)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (e : Sym2 M.V) :
    ∀ᵐ ω ∂(M.cutLaw r),
      quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e ≠ ⊤ := by
  filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hω
  induction e using Sym2.ind with
  | h x y => exact quadEdgeWeight_ne_top _ ω (0 : M.V) x y hω

/-- Each edge of the quadratic edge family has finite `ℝ≥0∞`-mean, with the bound given by the
`EdgeFamily` exhaustion of `p2RHS`. -/
theorem lintegral_quadEdgeWeight_ne_top (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤)
    (hp2 : M.p2RHS r ≠ ⊤) (e : Sym2 M.V) :
    ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
        ∂(M.cutLaw r) ≠ ⊤ := by
  have hle : ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
        ∂(M.cutLaw r) ≤ M.p2RHS r := by
    rw [← lintegral_tsum_quadEdgeWeight_eq_p2RHS M r h1]
    exact lintegral_mono fun ω => ENNReal.le_tsum e
  exact ne_top_of_le_ne_top hp2 hle

/-- A single member of the quadratic edge family, as a real integral. -/
theorem integral_toReal_quadEdgeWeight (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤)
    (e : Sym2 M.V) :
    ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e).toReal
        ∂(M.cutLaw r)
      = (∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
          ∂(M.cutLaw r)).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
    (ENNReal.measurable_toReal.comp (measurable_quadEdgeWeight _ (0 : M.V) e)).aestronglyMeasurable]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [M.ae_quadEdgeWeight_ne_top r h1 e] with ω hω
  exact ENNReal.ofReal_toReal hω

/-! ## 2. The `p = 2` FLUX identity -/

/-- **The `p = 2` FLUX identity at a fixed radius.**

The closed-edge sum of the literal per-edge pivotal fluxes of the unbounded square `|K_0|²` is
the `cutLaw r`-mean of the paper's `p = 2` double sum.  Both finiteness inputs are explicit:
`M.cutMassAt r 0 ≠ ⊤` is the source's first cut-off moment (it supplies almost sure finiteness
of every cluster volume) and `M.p2RHS r ≠ ⊤` is the finiteness of the `p = 2` right-hand side
(see `p2RHS_ne_top_of_firstMoment` for its derivation from the model's kernel regularity). -/
theorem tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_integral_toReal_p2PaperSum
    (r : ℝ) (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    ∑' e : Sym2 M.V, M.cutEdgeClosedWeight r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e
      = ∫ ω, (PivotFlux.p2PaperSum M r ω).toReal ∂(M.cutLaw r) := by
  classical
  calc ∑' e : Sym2 M.V, M.cutEdgeClosedWeight r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e
      = ∑' e : Sym2 M.V,
          ∫ ω, (quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e).toReal
            ∂(M.cutLaw r) :=
        tsum_congr fun e => M.cutEdgeClosedWeight_mul_pivotalFlux_eq r h1 e
    _ = ∑' e : Sym2 M.V,
          (∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
            ∂(M.cutLaw r)).toReal :=
        tsum_congr fun e => M.integral_toReal_quadEdgeWeight r h1 e
    _ = (∑' e : Sym2 M.V,
          ∫⁻ ω, quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
            ∂(M.cutLaw r)).toReal :=
        (ENNReal.tsum_toReal_eq (fun e => M.lintegral_quadEdgeWeight_ne_top r h1 hp2 e)).symm
    _ = (∫⁻ ω, ∑' e : Sym2 M.V,
          quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e
            ∂(M.cutLaw r)).toReal := by
        rw [MeasureTheory.lintegral_tsum
          (fun e => (measurable_quadEdgeWeight _ (0 : M.V) e).aemeasurable)]
    _ = (M.p2RHS r).toReal := by
        rw [lintegral_tsum_quadEdgeWeight_eq_p2RHS M r h1]
    _ = ∫ ω, (PivotFlux.p2PaperSum M r ω).toReal ∂(M.cutLaw r) :=
        (PivotFlux.integral_toReal_p2PaperSum M r hp2).symm

/-- **The `p = 2` derivative value at a fixed radius**: the `cutEdgeDeriv` form of the FLUX
identity.  At every radius `r` the edge sum of the literal derivative weights against the
pivotal fluxes of the unbounded square is the accepted `p = 2` right-hand side
`M.rhsScalarTwo r = M.coeffRHS r · (M.p2RHS r).toReal`. -/
theorem tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo (r : ℝ)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e
      = M.rhsScalarTwo r := by
  rw [M.tsum_cutEdgeDeriv_mul_pivotalFlux r (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2),
    M.tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_integral_toReal_p2PaperSum r h1 hp2,
    PivotFlux.rhsScalarTwo_eq_integral_toReal_p2PaperSum M r hp2]

/-- **The FLUX identity in the source's `p2RHS` form.** -/
theorem tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_p2RHS_toReal (r : ℝ)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) :
    ∑' e : Sym2 M.V, M.cutEdgeClosedWeight r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e
      = (M.p2RHS r).toReal := by
  rw [M.tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_integral_toReal_p2PaperSum r h1 hp2,
    PivotFlux.integral_toReal_p2PaperSum M r hp2]

/-- **The FLUX identity in the paper's displayed excluded-mass form.** -/
theorem tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_exclMass (r : ℝ)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hq : M.exclMassQuad r ≠ ⊤)
    (hs : M.exclMassSqLin r ≠ ⊤) :
    ∑' e : Sym2 M.V, M.cutEdgeClosedWeight r e *
        pivotalFlux (M.cutLaw r) (fun ω => (clusterVol ω (0 : M.V)).toReal ^ 2) e
      = (M.exclMassQuad r).toReal + 2 * (M.exclMassSqLin r).toReal := by
  have hp2 : M.p2RHS r ≠ ⊤ := by
    simp only [SourceModelData.p2RHS]
    exact ENNReal.add_ne_top.mpr ⟨hq, ENNReal.mul_ne_top (by norm_num) hs⟩
  rw [M.tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_integral_toReal_p2PaperSum r h1 hp2,
    PivotFlux.integral_toReal_p2PaperSum_eq_source M r hq hs]

/-- The finiteness hypothesis `M.p2RHS r ≠ ⊤` of the FLUX identity is the landed
`SecondMoment/Finiteness` input: it follows from the source's first cut-off moment and the
model's kernel regularity, with no extra assumption. -/
theorem p2RHS_ne_top_of_firstMoment {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ)) {r : ℝ} (hr : 0 < r)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) : M.p2RHS r ≠ ⊤ := by
  refine M.p2RhsMass_ne_top hc hρ hr ?_
  simpa only [SourceModelData.cutMoment, SourceModelData.cutMassAt, pow_one] using h1

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.ae_quadEdgeWeight_ne_top
#print axioms SourceModelData.lintegral_quadEdgeWeight_ne_top
#print axioms SourceModelData.integral_toReal_quadEdgeWeight
#print axioms SourceModelData.tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_integral_toReal_p2PaperSum
#print axioms SourceModelData.tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo
#print axioms SourceModelData.tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_p2RHS_toReal
#print axioms SourceModelData.tsum_cutEdgeClosedWeight_mul_pivotalFlux_eq_exclMass
#print axioms SourceModelData.p2RHS_ne_top_of_firstMoment

end PercLib.CriticalLRP.Orchestration
