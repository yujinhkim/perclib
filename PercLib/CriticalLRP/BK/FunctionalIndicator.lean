/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.2.1 of Hutchcroft for general increasing functionals

This file instantiates the abstract layer-cake engine of `LayerCake.lean` on the edge-dependent
Bernoulli percolation law `edgeLaw p` of `CriticalPercLib.CriticalLRP.BK`, passing from the
indicator form of the two-cluster inequality (`twoCluster_bk`) to arbitrary non-negative increasing
functionals `F (K_x)`, `G (K_y)` of the clusters of two vertices, as in Lemma I.2.1 of
Hutchcroft, arXiv:2508.18807v1, p. 21.

The two-cluster inequality is *used*, not reproved: the input is `twoCluster_bk` of
`BK/GraphConsequences.lean`.  What is proved here is the layer-cake/monotone lift, i.e. the part of
Lemma I.2.1 that says "for every pair of increasing non-negative functions `F` and `G`".

The finite-witness hypothesis on level sets is what `twoCluster_bk` requires; it is discharged in
`LemmaI21Counts.lean` for functionals of the cluster size.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.LayerCake

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MonotoneCluster
attribute [local instance] Classical.propDecidable

/-- The cluster of `x` is monotone in the edge configuration. -/
theorem cluster_mono {G : BondGraph V E} {ω₁ ω₂ : Set E} (hω : ω₁ ⊆ ω₂) (x : V) :
    cluster G ω₁ x ⊆ cluster G ω₂ x := fun _ hy => conn_mono G hω hy

/-- For a functional `F` of vertex sets that is monotone under inclusion, the level sets of
`ω ↦ F (K_x ω)` are increasing (upper) events. -/
theorem isUpperSet_level_cluster {G : BondGraph V E} {F : Set V → ℝ}
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (x : V) (s : ℝ) :
    IsUpperSet {ω : Set E | s < F (cluster G ω x)} :=
  fun _ _ hω h => lt_of_lt_of_le h (hF _ _ (cluster_mono hω x))

/-- `{ω | s < F (K_x ω)}` only depends on the cluster of `x`. -/
theorem clusterDeterminedAt_level {G : BondGraph V E} {F : Set V → ℝ} (x : V) (s : ℝ) :
    ClusterDeterminedAt G x {ω : Set E | s < F (cluster G ω x)} := by
  intro ω ω' h
  simp only [Set.mem_ofPred_eq, h]

end MonotoneCluster

section TwoClusterENNReal
attribute [local instance] Classical.propDecidable

variable {G : BondGraph V E} {p : E → unitInterval}

/-- **Lemma I.2.1(i) in `ℝ≥0∞` measure form, indicator level.**  For increasing finitely witnessed
events `A`, `B` that are determined by the clusters of `x` and `y`, the two-cluster bound holds in
the `ℝ≥0∞` measure, not merely after applying `toReal`. -/
theorem twoCluster_bk_ennreal [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) (A B : Set (Set E)) (hA : IsUpperSet A)
    (hfA : FiniteWitness A) (hdA : ClusterDeterminedAt G x A) (hB : IsUpperSet B)
    (hfB : FiniteWitness B) (hdB : ClusterDeterminedAt G y B) :
    (edgeLaw p) (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤ (edgeLaw p) A * (edgeLaw p) B := by
  have hmono : MeasurableSet {ω : Set E | ¬ Conn G ω x y} :=
    (measurableSet_conn G x y).compl
  have hreal := twoCluster_bk G p hp x y A B hA hfA hdA hB hfB hdB
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at hreal
  have hne : (edgeLaw p) A * (edgeLaw p) B ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) hne).mp hreal

/-- **Two-cluster inequality for level sets of arbitrary non-negative increasing functionals**
(BK input form).  This is the hypothesis consumed by the layer-cake engine
`PercLib.CriticalLRP.Percolation.LayerCake.lintegral_mul_indicator_le_of_meas_lt`. -/
theorem twoCluster_levelMeas_le [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) {f g : Set E → ℝ}
    (hfu : ∀ s, IsUpperSet {ω | s < f ω}) (hfw : ∀ s, FiniteWitness {ω | s < f ω})
    (hfd : ∀ s, ClusterDeterminedAt G x {ω | s < f ω})
    (hgu : ∀ t, IsUpperSet {ω | t < g ω}) (hgw : ∀ t, FiniteWitness {ω | t < g ω})
    (hgd : ∀ t, ClusterDeterminedAt G y {ω | t < g ω}) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (edgeLaw p) ({ω | ¬ Conn G ω x y} ∩ {ω | s < f ω} ∩ {ω | t < g ω}) ≤
      (edgeLaw p) {ω | s < f ω} * (edgeLaw p) {ω | t < g ω} := by
  have h := twoCluster_bk_ennreal G p hp x y _ _ (hfu s) (hfw s) (hfd s) (hgu t) (hgw t) (hgd t)
  have hset : {ω : Set E | ¬ Conn G ω x y} ∩ {ω | s < f ω} ∩ {ω | t < g ω}
      = {ω | s < f ω} ∩ {ω | t < g ω} ∩ {ω : Set E | ¬ Conn G ω x y} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [hset]
  exact h

/-- **Lemma I.2.1(i), general increasing functionals, `ℝ≥0∞` form.**

For any non-negative measurable `f`, `g` on the configuration space whose level sets are increasing,
finitely witnessed events determined by the clusters of `x` and `y` respectively,

`∫_{x ↮ y} f g ≤ (∫ f) (∫ g)`.

The passage from the indicator form to `f`, `g` is `PercLib.CriticalLRP.Percolation.LayerCake.lintegral_mul_indicator_le_of_meas_lt`.
-/
theorem twoCluster_functional_le [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) {f g : Set E → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hfm : Measurable f) (hgm : Measurable g)
    (hfu : ∀ s, IsUpperSet {ω | s < f ω}) (hfw : ∀ s, FiniteWitness {ω | s < f ω})
    (hfd : ∀ s, ClusterDeterminedAt G x {ω | s < f ω})
    (hgu : ∀ t, IsUpperSet {ω | t < g ω}) (hgw : ∀ t, FiniteWitness {ω | t < g ω})
    (hgd : ∀ t, ClusterDeterminedAt G y {ω | t < g ω}) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (f ω * g ω) ∂(edgeLaw p)
      ≤ (∫⁻ ω, ENNReal.ofReal (f ω) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (g ω) ∂(edgeLaw p)) :=
  PercLib.CriticalLRP.Percolation.LayerCake.lintegral_mul_indicator_le_of_meas_lt hf0 hg0 hfm hgm
    (measurableSet_conn G x y).compl
    (fun s t hs ht => twoCluster_levelMeas_le G p hp x y hfu hfw hfd hgu hgw hgd s t hs ht)

/-- **Harris--FKG for general increasing functionals** on the percolation configuration space,
`ℝ≥0∞` form: `(∫ f)(∫ g) ≤ ∫ f g`. -/
theorem fkg_functional_le [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) {f g : Set E → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hfm : Measurable f) (hgm : Measurable g)
    (hfu : ∀ s, IsUpperSet {ω | s < f ω}) (hfw : ∀ s, FiniteWitness {ω | s < f ω})
    (hgu : ∀ t, IsUpperSet {ω | t < g ω}) (hgw : ∀ t, FiniteWitness {ω | t < g ω}) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂(edgeLaw p)) *
        (∫⁻ ω, ENNReal.ofReal (g ω) ∂(edgeLaw p))
      ≤ ∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂(edgeLaw p) := by
  refine PercLib.CriticalLRP.Percolation.LayerCake.lintegral_mul_ge_of_meas_lt hf0 hg0 hfm hgm (fun s t hs ht => ?_)
  have h := association_edge_finiteWitness p _ _ (hfu s) (hgu t) (hfw s) (hgw t)
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at h
  have hne : (edgeLaw p) {ω : Set E | s < f ω} * (edgeLaw p) {ω : Set E | t < g ω} ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  exact (ENNReal.toReal_le_toReal hne (measure_ne_top _ _)).mp h

end TwoClusterENNReal

end Percolation

end PercLib.CriticalLRP
