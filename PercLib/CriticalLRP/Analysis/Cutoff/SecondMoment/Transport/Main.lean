/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` infinite-volume edge-to-vertex reindexing: the vertex-side identity

Swarm `smwvbcnfb`, member `m3`, direction `d3`.

Integration donor: `.ultramath/smwvbcnfb/m3`; independently checked at
`8dbe14ef7e6200b83fb48c8568674f938e03bd50`.

**Main result.**  For every radius `r`, the expectation of the `p = 2` paper double sum is the
source's `p = 2` right-hand side:

  `∫⁻ ω, p2PaperSum r ω ∂(cutLaw r) = p2RHS r = exclMassQuad r + 2 · exclMassSqLin r`.

No moment, no finiteness and no summability hypothesis enters: everything is `ℝ≥0∞`-valued, so
every series interchange is `lintegral_tsum` and every mass-transport step is a genuine
`tsum_mass_transport₃` on a covariant kernel.  This is the `p = 2` companion of
`PivotFlux.lintegral_paperSum_eq_exclMass`, and it is exactly the missing reindexing: the `p = 1`
theorem cannot be applied to `|K_0|²` because the second-order increment is not linear in the
cluster, and the coefficient `2` together with the squared weight has to come out of
`flipDiff_sq`.

The two terms of the increment behave differently under transport:

* `|K_c|²` is a weight at the target only (`pivotWeightSq`) and transports by itself;
* the cross term `2 |K_0| |K_c|` carries a cluster functional at the *anchor*, so it must be
  transported as the coupled pair `(|K_a|, pivotWeight a b c)`; at the root `a ∈ K_0` one has
  `|K_a| = |K_0|`, and `∑_{a ∈ K_0} |K_a| = |K_0|²` produces exactly the source's `|K|²` weight.

`Main.lean` therefore also covers the case the `p = 1` mass transport cannot see: the same letter
`|K|` appears at two different vertices of the transported triple.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.Transport

/-!
# Vertex-side identity for the `p = 2` Russo sum
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

/-! ## 1. Interchange of the integral with the paper double sum -/

/-- The expectation of the `p = 2` paper double sum is the double sum of expectations. -/
theorem lintegral_p2PaperSum (r : ℝ) :
    ∫⁻ ω, p2PaperSum M r ω ∂(M.cutLaw r)
      = ∑' b : M.V, ∑' c : M.V,
          ∫⁻ ω, p2Weight M r ω b c ∂(M.cutLaw r) := by
  rw [show (fun ω => p2PaperSum M r ω)
      = fun ω => ∑' b : M.V, ∑' c : M.V, p2Weight M r ω b c from rfl]
  rw [lintegral_tsum]
  · refine tsum_congr fun b => ?_
    rw [lintegral_tsum]
    exact fun c => (measurable_p2Weight M r b c).aemeasurable
  · exact fun b => (Measurable.tsum fun c => measurable_p2Weight M r b c).aemeasurable

/-- The expectation of the `p = 2` per-pair increment splits into `2` times the cross-term
expectation plus the diagonal (`|K_c|²`) expectation. -/
theorem lintegral_p2Weight_eq (r : ℝ) (b c : M.V) :
    ∫⁻ ω, p2Weight M r ω b c ∂(M.cutLaw r)
      = 2 * (∫⁻ ω,
          clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c ∂(M.cutLaw r))
        + ∫⁻ ω, pivotWeightSq M r ω (0 : M.V) b c ∂(M.cutLaw r) := by
  have hcross : Measurable fun ω : Config M.V =>
      2 * clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c :=
    (measurable_const.mul (measurable_clusterVol (0 : M.V))).mul
      (measurable_pivotWeight M r 0 b c)
  have hsplit : (fun ω : Config M.V => p2Weight M r ω b c)
      = fun ω => 2 * clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c
          + pivotWeightSq M r ω (0 : M.V) b c := by
    funext ω
    simp only [p2Weight]
  rw [hsplit, lintegral_add_left hcross]
  congr 1
  have h2 : (fun ω : Config M.V =>
        2 * clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c)
      = fun ω => 2 * (clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c) := by
    funext ω
    exact mul_assoc _ _ _
  rw [h2]
  exact lintegral_const_mul (μ := M.cutLaw r) (2 : ℝ≥0∞)
    (f := fun ω : Config M.V => clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c)
    ((measurable_clusterVol (0 : M.V)).mul (measurable_pivotWeight M r 0 b c))

/-! ## 2. Interchange of the integral with the transported (root-anchored) double sums -/

/-- The expectation of the root-anchored coupled double sum is the double sum of expectations. -/
theorem lintegral_reindexed_cross (r : ℝ) :
    ∫⁻ ω, (∑' a : M.V, ∑' c : M.V,
        clusterVol ω a * pivotWeight M r ω a (0 : M.V) c) ∂(M.cutLaw r)
      = ∑' a : M.V, ∑' c : M.V,
          ∫⁻ ω, clusterVol ω a * pivotWeight M r ω a (0 : M.V) c ∂(M.cutLaw r) := by
  rw [lintegral_tsum]
  · refine tsum_congr fun a => ?_
    rw [lintegral_tsum]
    exact fun c =>
      ((measurable_clusterVol a).mul (measurable_pivotWeight M r a 0 c)).aemeasurable
  · exact fun a => (Measurable.tsum fun c =>
      (measurable_clusterVol a).mul (measurable_pivotWeight M r a 0 c)).aemeasurable

/-- The expectation of the root-anchored squared double sum is the double sum of expectations. -/
theorem lintegral_reindexed_sq (r : ℝ) :
    ∫⁻ ω, (∑' a : M.V, ∑' c : M.V, pivotWeightSq M r ω a (0 : M.V) c) ∂(M.cutLaw r)
      = ∑' a : M.V, ∑' c : M.V,
          ∫⁻ ω, pivotWeightSq M r ω a (0 : M.V) c ∂(M.cutLaw r) := by
  rw [lintegral_tsum]
  · refine tsum_congr fun a => ?_
    rw [lintegral_tsum]
    exact fun c => (measurable_pivotWeightSq M r a 0 c).aemeasurable
  · exact fun a => (Measurable.tsum fun c => measurable_pivotWeightSq M r a 0 c).aemeasurable

/-! ## 3. The vertex-side `p = 2` reindexing -/

/-- **Main theorem: the `p = 2` paper double sum has expectation `p2RHS`.**

The paper's double sum is `∑_{x ∈ K_0} ∑_{y ∈ B_r(x)} 1(y ∉ K_0) (2 |K_0| |K_y| + |K_y|²)`, the
`p = 2` increment of `flipDiff_clusterVol_sq_eq` summed over the pivot pairs.  Its expectation is
the source's `p = 2` right-hand side `exclMassQuad + 2 · exclMassSqLin`, divided by
`β_c |K'(r)|` — i.e. exactly the value `p2RHS` which the derivative identity of Lemma I.4.1 at
`p = 2` carries.

The proof is the two mass transports of `Transport.lean` (the cross term transported as the
coupled pair `(|K_a|, pivotWeight a b c)`, the diagonal term as `pivotWeightSq`), followed by the
root reductions `tsum_tsum_clusterVol_mul_pivotWeight_eq` and `tsum_tsum_pivotWeightSq_eq`, and the
identification of the rooted ball sums with the window sums `exclSumLin`/`exclSumQuad`. -/
theorem lintegral_p2PaperSum_eq_p2RHS (r : ℝ) :
    ∫⁻ ω, p2PaperSum M r ω ∂(M.cutLaw r) = M.p2RHS r := by
  set X : M.V → M.V → ℝ≥0∞ := fun b c =>
    ∫⁻ ω, clusterVol ω (0 : M.V) * pivotWeight M r ω (0 : M.V) b c ∂(M.cutLaw r) with hX
  set Y : M.V → M.V → ℝ≥0∞ := fun b c =>
    ∫⁻ ω, pivotWeightSq M r ω (0 : M.V) b c ∂(M.cutLaw r) with hY
  -- (1) interchange, (2) split of the per-pair increment
  have h1 : ∫⁻ ω, p2PaperSum M r ω ∂(M.cutLaw r)
      = ∑' b : M.V, ∑' c : M.V, (2 * X b c + Y b c) := by
    rw [lintegral_p2PaperSum M r]
    exact tsum_congr fun b => tsum_congr fun c => lintegral_p2Weight_eq M r b c
  -- (3) the double sums of the two terms separate
  have h2 : (∑' b : M.V, ∑' c : M.V, (2 * X b c + Y b c))
      = 2 * (∑' b : M.V, ∑' c : M.V, X b c) + ∑' b : M.V, ∑' c : M.V, Y b c := by
    have hinner : ∀ b : M.V, (∑' c : M.V, (2 * X b c + Y b c))
        = 2 * (∑' c : M.V, X b c) + ∑' c : M.V, Y b c := by
      intro b
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    calc (∑' b : M.V, ∑' c : M.V, (2 * X b c + Y b c))
        = ∑' b : M.V, (2 * (∑' c : M.V, X b c) + ∑' c : M.V, Y b c) :=
          tsum_congr hinner
      _ = (∑' b : M.V, 2 * (∑' c : M.V, X b c)) + ∑' b : M.V, ∑' c : M.V, Y b c :=
          ENNReal.tsum_add
      _ = 2 * (∑' b : M.V, ∑' c : M.V, X b c) + ∑' b : M.V, ∑' c : M.V, Y b c := by
          rw [ENNReal.tsum_mul_left]
  -- (4) the two mass transports
  have hX' : (∑' b : M.V, ∑' c : M.V, X b c)
      = ∑' a : M.V, ∑' c : M.V,
          ∫⁻ ω, clusterVol ω a * pivotWeight M r ω a (0 : M.V) c ∂(M.cutLaw r) := by
    rw [hX]; exact massTransportCross M r
  have hY' : (∑' b : M.V, ∑' c : M.V, Y b c)
      = ∑' a : M.V, ∑' c : M.V,
          ∫⁻ ω, pivotWeightSq M r ω a (0 : M.V) c ∂(M.cutLaw r) := by
    rw [hY]; exact massTransportSq M r
  -- (5) the root reductions, through the (unconditional) integral interchange
  have hX'' : (∑' a : M.V, ∑' c : M.V,
        ∫⁻ ω, clusterVol ω a * pivotWeight M r ω a (0 : M.V) c ∂(M.cutLaw r))
      = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 * ballSum M r ω ∂(M.cutLaw r) := by
    rw [← lintegral_reindexed_cross M r]
    exact lintegral_congr fun ω => tsum_tsum_clusterVol_mul_pivotWeight_eq M r ω
  have hY'' : (∑' a : M.V, ∑' c : M.V,
        ∫⁻ ω, pivotWeightSq M r ω a (0 : M.V) c ∂(M.cutLaw r))
      = ∫⁻ ω, clusterVol ω (0 : M.V) * ballSumSq M r ω ∂(M.cutLaw r) := by
    rw [← lintegral_reindexed_sq M r]
    exact lintegral_congr fun ω => tsum_tsum_pivotWeightSq_eq M r ω
  -- (6) identification with the source's two excluded masses
  have hXfin : (∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 * ballSum M r ω ∂(M.cutLaw r))
      = SourceModelData.exclMassSqLin M r := by
    rw [SourceModelData.exclMassSqLin, ballSum_eq_exclSumLin]
  have hYfin : (∫⁻ ω, clusterVol ω (0 : M.V) * ballSumSq M r ω ∂(M.cutLaw r))
      = SourceModelData.exclMassQuad M r := by
    rw [SourceModelData.exclMassQuad, ballSumSq_eq_exclSumQuad]
  rw [h1, h2, hX', hY', hX'', hY'', hXfin, hYfin, SourceModelData.p2RHS, add_comm]

end PivotFlux

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.PivotFlux

#print axioms lintegral_p2PaperSum
#print axioms lintegral_p2Weight_eq
#print axioms lintegral_reindexed_cross
#print axioms lintegral_reindexed_sq
#print axioms lintegral_p2PaperSum_eq_p2RHS

end PercLib.CriticalLRP.PivotFlux
