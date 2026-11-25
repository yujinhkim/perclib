/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` mass transport: from the paper double sum to the excluded masses

Swarm `smwvbcnfb`, member `m3`, direction `d3`.

Integration donor: `.ultramath/smwvbcnfb/m3`; independently checked at
`8dbe14ef7e6200b83fb48c8568674f938e03bd50`.

This file proves the two mass-transport steps that turn the `p = 2` paper double sum

  `∑_{b ∈ K_0} ∑_{c ∈ B_r(b)} 1(c ∉ K_0) (2 |K_0| |K_c| + |K_c|²)`

into the source's two excluded masses `2 · exclMassSqLin + exclMassQuad`:

* the **diagonal** term `|K_c|²` transports on its own, exactly like the `p = 1` weight, giving
  `E[|K_0| ∑_{c ∈ B_r} 1(c ∉ K_0) |K_c|²] = exclMassQuad`;
* the **cross** term `2 |K_0| |K_c|` transports as the *coupled* pair
  `(clusterVol · a, pivotWeight · a b c)`, and at the root `a ∈ K_0` one has `|K_a| = |K_0|`, so
  the transported weight is `|K_0|²` and the value is `2 · exclMassSqLin`.

The two transports use `tsum_mass_transport₃` (the same triple-sum transport as `p = 1`) on the
covariant kernels of `Basic.lean`.  Everything is `ℝ≥0∞`-valued, so no moment, integrability or
finiteness hypothesis enters: the series interchanges are `lintegral_tsum` and `ENNReal.tsum_add`,
which are unconditional.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Basic
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs

/-!
# `p = 2` mass transport and the vertex-side identification
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

/-! ## 1. The two triple-sum mass transports -/

/-- **Mass transport of the diagonal `|K_c|²` weight.**  The `p = 2` companion of
`PivotFlux.massTransport`. -/
theorem massTransportSq (r : ℝ) :
    (∑' b : M.V, ∑' c : M.V,
        ∫⁻ ω, pivotWeightSq M r ω (0 : M.V) b c ∂(M.cutLaw r))
      = ∑' a : M.V, ∑' c : M.V,
        ∫⁻ ω, pivotWeightSq M r ω a (0 : M.V) c ∂(M.cutLaw r) :=
  tsum_mass_transport₃
    (fun a b c => ∫⁻ ω, pivotWeightSq M r ω a b c ∂(M.cutLaw r))
    (fun a b c t => integral_pivotWeightSq_shift M r a b c t)

/-- **Mass transport of the coupled cross-term weight `|K_a| · pivotWeight a b c`.**

The extra factor `clusterVol ω a` is a cluster functional at the anchor, so it has to be
transported *together* with the pivot; the covariance is `clusterVol_mul_pivotWeight_shift`.
This is the step that produces the source's `|K|²` weight of the second excluded term. -/
theorem massTransportCross (r : ℝ) :
    (∑' b : M.V, ∑' c : M.V,
        ∫⁻ ω, clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c ∂(M.cutLaw r))
      = ∑' a : M.V, ∑' c : M.V,
        ∫⁻ ω, clusterVol ω a * pivotWeight M r ω a (0 : M.V) c ∂(M.cutLaw r) :=
  tsum_mass_transport₃
    (fun a b c => ∫⁻ ω, clusterVol ω a * pivotWeight M r ω a b c ∂(M.cutLaw r))
    (fun a b c t => integral_clusterVol_mul_pivotWeight_shift M r a b c t)

/-! ## 2. The root reductions: the transported sums are `|K_0|` times the excluded ball sums -/

/-- At the root `b = 0` the squared pivotal weight factors into the anchor indicator and the
squared excluded ball summand.  The `p = 2` companion of `tsum_pivotWeight_eq`. -/
theorem tsum_pivotWeightSq_eq (r : ℝ) (ω : Config M.V) (a : M.V) :
    (∑' c : M.V, pivotWeightSq M r ω a (0 : M.V) c)
      = configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω * ballSumSq M r ω := by
  have h : (∑' c : M.V, pivotWeightSq M r ω a (0 : M.V) c)
      = ∑' c : M.V, configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω *
          ((if M.S.ρ (toVec c) ≤ r then 1 else 0) *
            configIndicator {ω' : Config M.V | ¬ Connects ω' (0 : M.V) c} ω
              * clusterVol ω c ^ 2) :=
    tsum_congr fun c => by
      simp only [pivotWeightSq, SourceNormData.dist, sub_zero, mul_assoc]
  rw [h, ENNReal.tsum_mul_left]
  simp only [ballSumSq, mul_assoc]

/-- **The reindexed squared double sum is the excluded quadratic integrand.** -/
theorem tsum_tsum_pivotWeightSq_eq (r : ℝ) (ω : Config M.V) :
    (∑' a : M.V, ∑' c : M.V, pivotWeightSq M r ω a (0 : M.V) c)
      = clusterVol ω (0 : M.V) * ballSumSq M r ω := by
  calc (∑' a : M.V, ∑' c : M.V, pivotWeightSq M r ω a (0 : M.V) c)
      = ∑' a : M.V,
          configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω * ballSumSq M r ω :=
        tsum_congr fun a => tsum_pivotWeightSq_eq M r ω a
    _ = (∑' a : M.V, configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω)
          * ballSumSq M r ω := ENNReal.tsum_mul_right
    _ = clusterVol ω (0 : M.V) * ballSumSq M r ω := by rw [tsum_connects_indicator]

/-- On `a ∈ K_0` the cluster volumes of `a` and of `0` agree, so the transported cross term
carries the weight `|K_0|` at the anchor. -/
theorem clusterVol_eq_of_connects {ω : Config M.V} {a : M.V} (h : Connects ω a (0 : M.V)) :
    clusterVol ω a = clusterVol ω (0 : M.V) := by
  have hmem : a ∈ cluster ω (0 : M.V) := by
    rw [mem_cluster_iff]; exact connects_symm h
  rw [clusterVol_eq_encard, clusterVol_eq_encard, cluster_eq_of_mem_cluster hmem]

/-- **`∑_{a ∈ K_0} |K_a| = |K_0|²`.**  The vertex weights at the anchor collapse to the squared
cluster volume; this is where the source's `|K|²` weight of the cross term comes from. -/
theorem tsum_clusterVol_mul_connects (ω : Config M.V) :
    (∑' a : M.V, clusterVol ω a *
        configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω)
      = clusterVol ω (0 : M.V) ^ 2 := by
  have hterm : ∀ a : M.V, clusterVol ω a *
      configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω
      = clusterVol ω (0 : M.V) *
        configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω := by
    intro a
    by_cases h : Connects ω a (0 : M.V)
    · have hvol := clusterVol_eq_of_connects M h
      simp only [configIndicator, hvol]
    · simp only [configIndicator]
      simp only [Set.indicator_of_notMem
        (show ω ∉ {ω' : Config M.V | Connects ω' a (0 : M.V)} from h)]
      simp
  calc (∑' a : M.V, clusterVol ω a *
        configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω)
      = ∑' a : M.V, clusterVol ω (0 : M.V) *
          configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω :=
        tsum_congr hterm
    _ = clusterVol ω (0 : M.V) *
          (∑' a : M.V, configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω) :=
        ENNReal.tsum_mul_left
    _ = clusterVol ω (0 : M.V) * clusterVol ω (0 : M.V) := by rw [tsum_connects_indicator]
    _ = clusterVol ω (0 : M.V) ^ 2 := (sq _).symm

/-- **The reindexed cross double sum is `|K_0|²` times the excluded ball sum.** -/
theorem tsum_tsum_clusterVol_mul_pivotWeight_eq (r : ℝ) (ω : Config M.V) :
    (∑' a : M.V, ∑' c : M.V, clusterVol ω a * pivotWeight M r ω a (0 : M.V) c)
      = clusterVol ω (0 : M.V) ^ 2 * ballSum M r ω := by
  have houter : ∀ a : M.V, (∑' c : M.V, clusterVol ω a * pivotWeight M r ω a (0 : M.V) c)
      = clusterVol ω a *
          (configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω * ballSum M r ω) := by
    intro a
    rw [ENNReal.tsum_mul_left, tsum_pivotWeight_eq M r ω a]
  calc (∑' a : M.V, ∑' c : M.V, clusterVol ω a * pivotWeight M r ω a (0 : M.V) c)
      = ∑' a : M.V, clusterVol ω a *
          (configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω * ballSum M r ω) :=
        tsum_congr houter
    _ = ∑' a : M.V, (clusterVol ω a *
          configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω) * ballSum M r ω :=
        tsum_congr fun a => (mul_assoc _ _ _).symm
    _ = (∑' a : M.V, clusterVol ω a *
          configIndicator {ω' : Config M.V | Connects ω' a (0 : M.V)} ω) * ballSum M r ω :=
        ENNReal.tsum_mul_right
    _ = clusterVol ω (0 : M.V) ^ 2 * ballSum M r ω := by
        rw [tsum_clusterVol_mul_connects]

/-! ## 3. The squared excluded ball sum is the `exclSumQuad` window sum -/

/-- The `tsum` form of the squared rooted ball sum is the finite `Finset` sum over `ballF`. -/
theorem ballSumSq_eq_finset (r : ℝ) (ω : Config M.V) :
    ballSumSq M r ω = ∑ y ∈ E1Sign.ballF M r,
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2 := by
  unfold ballSumSq
  rw [tsum_eq_sum (s := E1Sign.ballF M r)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    have hyb : M.S.ρ (toVec y) ≤ r := (E1Sign.mem_ballF M).mp hy
    rw [ite_eq_left hyb, one_mul, configIndicator_not_connects_eq_compl_indicator]
  · intro c hc
    have hgt : r < M.S.ρ (toVec c) := by
      by_contra hle
      exact hc ((E1Sign.mem_ballF M).mpr (not_lt.mp hle))
    rw [ite_eq_right (not_le.mpr hgt)]
    simp

/-- `ballSumSq` is the `exclSumQuad` integrand of `SecondMoment/Defs`. -/
theorem ballSumSq_eq_exclSumQuad (r : ℝ) :
    ballSumSq M r = SourceModelData.exclSumQuad M r := by
  funext ω
  rw [ballSumSq_eq_finset, SourceModelData.exclSumQuad]

/-- `ballSum` is the `exclSumLin` integrand of `SecondMoment/Defs`. -/
theorem ballSum_eq_exclSumLin (r : ℝ) :
    ballSum M r = SourceModelData.exclSumLin M r := by
  funext ω
  rw [ballSum_eq_finset, SourceModelData.exclSumLin]

end PivotFlux

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.PivotFlux

#print axioms massTransportSq
#print axioms massTransportCross
#print axioms tsum_pivotWeightSq_eq
#print axioms tsum_tsum_pivotWeightSq_eq
#print axioms clusterVol_eq_of_connects
#print axioms tsum_clusterVol_mul_connects
#print axioms tsum_tsum_clusterVol_mul_pivotWeight_eq
#print axioms ballSumSq_eq_finset
#print axioms ballSumSq_eq_exclSumQuad
#print axioms ballSum_eq_exclSumLin

end PercLib.CriticalLRP.PivotFlux
