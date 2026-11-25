/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` edge-to-vertex mass transport: measurability, covariance, integrals

Swarm `smwvbcnfb`, member `m3`, direction `d3`.

Integration donor: `.ultramath/smwvbcnfb/m3`; independently checked at
`8dbe14ef7e6200b83fb48c8568674f938e03bd50`.

Part 1 of `Main.lean`'s content, kept separate only for compile time: the measurability and the
translation covariance of the `p = 2` pair weights of `Defs.lean`, and the resulting covariance of
the three integrated kernels
* `a ↦ pivotWeightSq r ω a b c` (weight `|K_c|²`),
* `p ↦ clusterVol ω p.1 * pivotWeight r ω p.1 p.2.1 p.2.2` (the coupled weight of the cross term),
* `p ↦ clusterVol ω p.1 ^ 2 * ...` is *not* needed: the transport is performed on the pair
  `(clusterVol a, pivotWeight a b c)`, which is exactly what makes the excluded mass
  `E[|K_0|² ...]` appear.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Defs

/-!
# Measurability, covariance and `lintegral_map` for the `p = 2` pair weights
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace PivotFlux

open Orchestration

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. Measurability -/

/-- The `p = 2` pair weight is measurable in the configuration. -/
theorem measurable_pivotWeightSq (r : ℝ) (a b c : M.V) :
    Measurable fun ω : Config M.V => pivotWeightSq M r ω a b c := by
  have h1 : Measurable fun ω : Config M.V =>
      configIndicator {ω' : Config M.V | Connects ω' a b} ω :=
    measurable_configIndicator (measurableSet_connects a b)
  have h2 : Measurable fun ω : Config M.V =>
      configIndicator {ω' : Config M.V | ¬ Connects ω' b c} ω :=
    measurable_configIndicator (measurableSet_connects b c).compl
  have h3 : Measurable fun ω : Config M.V => clusterVol ω c ^ 2 :=
    (measurable_clusterVol c).pow_const 2
  exact ((h1.mul measurable_const).mul h2).mul h3

/-- The `p = 2` per-pair increment is measurable in the configuration. -/
theorem measurable_p2Weight (r : ℝ) (b c : M.V) :
    Measurable fun ω : Config M.V => p2Weight M r ω b c := by
  have h1 : Measurable fun ω : Config M.V =>
      2 * clusterVol ω (0 : M.V) * pivotWeight M r ω 0 b c :=
    (measurable_const.mul (measurable_clusterVol (0 : M.V))).mul
      (measurable_pivotWeight M r 0 b c)
  exact h1.add (measurable_pivotWeightSq M r 0 b c)

/-- The `p = 2` paper double sum is measurable. -/
theorem measurable_p2PaperSum (r : ℝ) :
    Measurable fun ω : Config M.V => p2PaperSum M r ω := by
  refine Measurable.tsum fun b => Measurable.tsum fun c => ?_
  exact measurable_p2Weight M r b c

/-- The squared excluded ball sum is measurable. -/
theorem measurable_ballSumSq (r : ℝ) :
    Measurable fun ω : Config M.V => ballSumSq M r ω := by
  refine Measurable.tsum fun c => ?_
  have h2 : Measurable fun ω : Config M.V =>
      configIndicator {ω' : Config M.V | ¬ Connects ω' (0 : M.V) c} ω :=
    measurable_configIndicator (measurableSet_connects (0 : M.V) c).compl
  exact (measurable_const.mul h2).mul ((measurable_clusterVol c).pow_const 2)

/-! ## 2. Translation covariance -/

/-- The `p = 2` pair weight is covariant under lattice translations. -/
theorem pivotWeightSq_shift (r : ℝ) (t : M.V) (ω : Config M.V) (a b c : M.V) :
    pivotWeightSq M r (shiftConfig t ω) (a + t) (b + t) (c + t)
      = pivotWeightSq M r ω a b c := by
  have hd : M.S.dist (c + t) (b + t) = M.S.dist c b := by
    simp only [SourceNormData.dist]
    rw [show (c + t) - (b + t) = c - b by abel]
  simp only [pivotWeightSq, hd, configIndicator_connects_shift t a b ω,
    configIndicator_not_connects_shift t b c ω, SourceModelData.clusterVol_shiftConfig]

/-! ## 3. Integration over a translated configuration -/

/-- The expectation of the `p = 2` pair weight is translation invariant. -/
theorem integral_pivotWeightSq_shift (r : ℝ) (a b c t : M.V) :
    ∫⁻ ω, pivotWeightSq M r ω (a + t) (b + t) (c + t) ∂(M.cutLaw r)
      = ∫⁻ ω, pivotWeightSq M r ω a b c ∂(M.cutLaw r) := by
  calc ∫⁻ ω, pivotWeightSq M r ω (a + t) (b + t) (c + t) ∂(M.cutLaw r)
      = ∫⁻ ω, pivotWeightSq M r (shiftConfig (-t) ω) a b c ∂(M.cutLaw r) := by
        refine lintegral_congr fun ω => ?_
        simpa using (pivotWeightSq_shift M r (-t) ω (a + t) (b + t) (c + t)).symm
    _ = ∫⁻ ω, pivotWeightSq M r ω a b c ∂((M.cutLaw r).map (shiftConfig (-t))) := by
        rw [lintegral_map (measurable_pivotWeightSq M r a b c) (measurable_shiftConfig (-t))]
    _ = _ := by rw [M.cutLaw_map_shiftConfig r (-t)]

/-- **The coupled weight of the cross term is covariant.**  The pair
`(clusterVol · a, pivotWeight · a b c)` transforms as a single unit, which is what allows the
`|K_0|` factor of the `p = 2` increment to be transported together with the pivot. -/
theorem clusterVol_mul_pivotWeight_shift (r : ℝ) (t : M.V) (ω : Config M.V) (a b c : M.V) :
    clusterVol (shiftConfig t ω) (a + t) * pivotWeight M r (shiftConfig t ω) (a + t) (b + t) (c + t)
      = clusterVol ω a * pivotWeight M r ω a b c := by
  rw [SourceModelData.clusterVol_shiftConfig, pivotWeight_shift]

/-- The expectation of the coupled cross-term weight is translation invariant. -/
theorem integral_clusterVol_mul_pivotWeight_shift (r : ℝ) (a b c t : M.V) :
    ∫⁻ ω, clusterVol ω (a + t) * pivotWeight M r ω (a + t) (b + t) (c + t) ∂(M.cutLaw r)
      = ∫⁻ ω, clusterVol ω a * pivotWeight M r ω a b c ∂(M.cutLaw r) := by
  calc ∫⁻ ω, clusterVol ω (a + t) * pivotWeight M r ω (a + t) (b + t) (c + t) ∂(M.cutLaw r)
      = ∫⁻ ω, clusterVol (shiftConfig (-t) ω) a
          * pivotWeight M r (shiftConfig (-t) ω) a b c ∂(M.cutLaw r) := by
        refine lintegral_congr fun ω => ?_
        simpa using (clusterVol_mul_pivotWeight_shift M r (-t) ω (a + t) (b + t) (c + t)).symm
    _ = ∫⁻ ω, clusterVol ω a * pivotWeight M r ω a b c
          ∂((M.cutLaw r).map (shiftConfig (-t))) := by
        rw [lintegral_map]
        · exact (measurable_clusterVol a).mul (measurable_pivotWeight M r a b c)
        · exact measurable_shiftConfig (-t)
    _ = _ := by rw [M.cutLaw_map_shiftConfig r (-t)]

end PivotFlux

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.PivotFlux

#print axioms measurable_pivotWeightSq
#print axioms measurable_p2Weight
#print axioms measurable_p2PaperSum
#print axioms measurable_ballSumSq
#print axioms pivotWeightSq_shift
#print axioms integral_pivotWeightSq_shift
#print axioms clusterVol_mul_pivotWeight_shift
#print axioms integral_clusterVol_mul_pivotWeight_shift

end PercLib.CriticalLRP.PivotFlux
