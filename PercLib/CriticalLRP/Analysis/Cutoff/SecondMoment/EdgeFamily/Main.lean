/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` quadratic edge family has expectation `p2RHS`

Swarm `smwvc1d9z`, member `m2`, direction `d1`

Integration donor: `.ultramath/smwvc1d9z/m2`; independently reviewed at
`a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f` after one connectivity-composition repair in `Count.lean`..

This file connects the abstract edge-to-vertex identity of `EdgeToVertex.lean` to the source
model.  Two steps:

* `quadPairWeight_eq_binomWeight` — on configurations with finite clusters, the ENNReal
  oriented-pair weight `2|K_b||K_c| + |K_c|²` is exactly the source's `p = 2` binomial pivot
  weight `PivotFlux.binomWeight M 2 r ω 0 b c`, i.e. the ENNReal form
  `ofReal ((|K_b| + |K_c|)² - |K_b|²)` of the change of `|K|²` under the merge.  The
  finiteness of *both* cluster volumes is used in exactly the two places where `toReal` meets
  `ofReal`; without it the two sides genuinely differ (an infinite cluster has `toReal = 0`),
  so the hypothesis is not removable and is kept explicit.

* `lintegral_tsum_quadEdgeWeight_eq_p2RHS` — the expectation of the whole **unordered edge
  family** of quadratic edge weights is the source's `p = 2` right-hand side
  `p2RHS r = E[|K| Σ_{y ∈ B_r, y ∉ K}|K_y|²] + 2 E[|K|² Σ_{y ∈ B_r, y ∉ K}|K_y|]`,
  under the source's own hypothesis that the first cutoff moment is finite (which supplies
  almost-sure finiteness of every cluster through the landed
  `PivotFlux.ae_clusterVol_ne_top`), and using the landed mass transport
  `PivotFlux.lintegral_paperSumP_two_eq_of_cutMass`.

**What is not proved here.**  This is an identity of expectations of *edge weights*; it does not
identify the real-valued `cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) F e` with the edge weight,
it does not contain the coefficient `β_c |K'(r)|`, and it does not differentiate anything in `r`.
In particular it is **not** a two-sided derivative statement at any radius, attained or not: the
radius enters only through the range predicate `M.S.dist c b ≤ r`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.EdgeToVertex
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Binomial

/-!
# The model-level `p = 2` edge-family identity

Main results: `quadPairWeight_eq_binomWeight` (the weight is the source's binomial pivot weight)
and `lintegral_tsum_quadEdgeWeight_eq_p2RHS` (the edge family's expectation is `p2RHS`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

/-! ## 1. The `p = 2` binomial increment in `ℝ≥0∞` -/

/-- **The quadratic increment of a finite cluster volume in `ℝ≥0∞`.**  For finite (extended)
cardinalities `x, y`,
`ofReal ((x + y)² - x²) = 2 x y + y²`.  The two `toReal`/`ofReal` conversions are the only place
where the finiteness hypotheses `x ≠ ⊤`, `y ≠ ⊤` are used. -/
theorem ofReal_sq_sub_sq_eq_two_mul_add_sq {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    ENNReal.ofReal ((x.toReal + y.toReal) ^ 2 - x.toReal ^ 2) = 2 * x * y + y ^ 2 := by
  have hx' : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hy' : 0 ≤ y.toReal := ENNReal.toReal_nonneg
  have hsub : (x.toReal + y.toReal) ^ 2 - x.toReal ^ 2
      = 2 * x.toReal * y.toReal + y.toReal ^ 2 := by ring
  rw [hsub]
  have hp1 : (0 : ℝ) ≤ 2 * x.toReal * y.toReal := by positivity
  have hp2 : (0 : ℝ) ≤ y.toReal ^ 2 := by positivity
  rw [ENNReal.ofReal_add hp1 hp2]
  rw [show (2 * x.toReal * y.toReal : ℝ) = 2 * (x.toReal * y.toReal) by ring]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [ENNReal.ofReal_mul hx']
  rw [ENNReal.ofReal_pow hy']
  rw [ENNReal.ofReal_toReal hx, ENNReal.ofReal_toReal hy]
  norm_num
  ring

/-! ## 2. The oriented pair weight is the source's binomial pivot weight -/

/-- The indicator of a measurable set of configurations is the corresponding `ite`. -/
theorem configIndicator_eq_ite {d : ℕ} (s : Set (Config (Fin d → ℤ))) (ω : Config (Fin d → ℤ)) :
    configIndicator s ω = (if ω ∈ s then (1 : ℝ≥0∞) else 0) := by
  simp [configIndicator, Set.indicator_apply]

/-- **The ENNReal oriented-pair weight is the source's `p = 2` binomial pivot weight**, on the
event that the two cluster volumes are finite.  This is the pointwise identification of the
`2`-to-`1` count with the paper's `((|K| + |K_y|)² - |K|²)`. -/
theorem quadPairWeight_eq_binomWeight (M : Orchestration.SourceModelData) (r : ℝ)
    (ω : Config M.V) (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) (b c : M.V) :
    quadPairWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) b c
      = PivotFlux.binomWeight M 2 r ω (0 : M.V) b c := by
  simp only [quadPairWeight, PivotFlux.binomWeight, clusterVolR_eq_toReal,
    configIndicator_eq_ite, Set.mem_ofPred_eq]
  rw [ofReal_sq_sub_sq_eq_two_mul_add_sq (hfin b) (hfin c)]
  by_cases h : ¬ Connects ω b c
  · simp [h]
  · simp [h]

/-! ## 3. The edge family of the source model -/

/-- On configurations with finite clusters, the source's `p = 2` double sum is the unordered
edge family of quadratic edge weights.  This is `tsum_quadEdgeWeight_eq_tsum_quadPairWeight`
composed with the pointwise identification. -/
theorem paperSumP_two_eq_tsum_quadEdgeWeight (M : Orchestration.SourceModelData) (r : ℝ)
    (ω : Config M.V) (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) :
    PivotFlux.paperSumP M 2 r ω
      = ∑' e : Sym2 M.V,
          quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e := by
  rw [tsum_quadEdgeWeight_eq_tsum_quadPairWeight]
  simp only [PivotFlux.paperSumP]
  exact tsum_congr fun b => tsum_congr fun c =>
    (quadPairWeight_eq_binomWeight M r ω hfin b c).symm

/-- **The `p = 2` quadratic edge family has expectation `p2RHS r`.**

The expectation of `∑' e, quadEdgeWeight e` over the cutoff law (`e` ranging over *all* unordered
pairs of lattice sites, the range predicate being `M.S.dist c b ≤ r`) is the source's `p = 2`
right-hand side.  The only hypothesis is finiteness of the first cutoff moment at the origin —
the source's own hypothesis at `β ≤ β_c` — which supplies almost-sure finiteness of every
cluster via `PivotFlux.ae_clusterVol_ne_top`. -/
theorem lintegral_tsum_quadEdgeWeight_eq_p2RHS (M : Orchestration.SourceModelData) (r : ℝ)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) :
    ∫⁻ ω, (∑' e : Sym2 M.V,
        quadEdgeWeight (fun c b : M.V => M.S.dist c b ≤ r) ω (0 : M.V) e)
      ∂(M.cutLaw r) = M.p2RHS r := by
  have hae : ∀ᵐ ω ∂(M.cutLaw r), ∀ v : M.V, clusterVol ω v ≠ ⊤ :=
    PivotFlux.ae_clusterVol_ne_top M r h1
  rw [lintegral_congr_ae
    (hae.mono fun ω hω => (paperSumP_two_eq_tsum_quadEdgeWeight M r ω hω).symm)]
  exact PivotFlux.lintegral_paperSumP_two_eq_of_cutMass M r h1

end PercLib.CriticalLRP
