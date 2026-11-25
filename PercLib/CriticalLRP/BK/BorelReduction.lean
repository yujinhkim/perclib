/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The exact reduction for Lemma I.2.1 and real-valued forms

Two things are collected here.

1. `twoCluster_functional_of_borelBK`: **Lemma I.2.1(i) for *arbitrary* increasing functionals
   `F`, `G`** follows from a single indicator-level input, namely the two-cluster BK inequality for
   *all* increasing measurable cluster-determined events `A`, `B`.  This is the form in which the
   paper states the inequality for general `F, G` ("the first inequality is an immediate
   consequence of the BK inequality", p. 21, with the Borel form of BK from footnote 11).  The
   finite-witness version available in `BK/GraphConsequences.lean` does not suffice for functionals
   such as `1 {|K_x| = ∞}` that are not continuous from below, which is why
   `LemmaI21Final.lean` restricts to the continuity class; this theorem records that the
   continuity restriction is the *only* loss.

2. Real-valued forms (`toReal`) of the three displays, matching the paper's expectation
   notation, under the finiteness hypotheses that the paper states.

-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.LayerCake
public import PercLib.CriticalLRP.BK.FunctionalIndicator
public import PercLib.CriticalLRP.BK.FunctionalFromBelow

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

section Reduction
attribute [local instance] Classical.propDecidable

/-- **Lemma I.2.1(i) for arbitrary increasing functionals, conditional only on the general Borel
two-cluster BK inequality.**  Given the indicator inequality
`μ (A ∩ B ∩ {x ↮ y}) ≤ μ A · μ B` for *all* increasing measurable events `A` determined by the
cluster of `x` and `B` determined by the cluster of `y`, the functional inequality
`∫_{x↮y} F (K_x) G (K_y) ≤ (∫ F (K_x)) (∫ G (K_y))` holds for every non-negative increasing
functional of the clusters. -/
theorem twoCluster_functional_of_borelBK [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y))
    (hBK : ∀ A B : Set (Set E), IsUpperSet A → MeasurableSet A →
      ClusterDeterminedAt G x A → IsUpperSet B → MeasurableSet B →
      ClusterDeterminedAt G y B →
      (edgeLaw p) (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤ (edgeLaw p) A * (edgeLaw p) B) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) := by
  refine PercLib.CriticalLRP.Percolation.LayerCake.lintegral_mul_indicator_le_of_meas_lt (fun ω => hF0 (cluster G ω x))
    (fun ω => hH0 (cluster G ω y)) hFmeas hHmeas
    (measurableSet_conn G x y).compl (fun s t _ _ => ?_)
  rw [show {ω : Set E | ¬ Conn G ω x y} ∩ {ω | s < F (cluster G ω x)}
      ∩ {ω | t < H (cluster G ω y)}
      = {ω | s < F (cluster G ω x)} ∩ {ω | t < H (cluster G ω y)}
        ∩ {ω : Set E | ¬ Conn G ω x y} from by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto]
  exact hBK _ _ (isUpperSet_level_cluster hFmono x s)
    (hFmeas measurableSet_Ioi) (clusterDeterminedAt_level x s)
    (isUpperSet_level_cluster hHmono y t) (hHmeas measurableSet_Ioi)
    (clusterDeterminedAt_level y t)

end Reduction

section RealForms
attribute [local instance] Classical.propDecidable

/-- **Lemma I.2.1(i) in real (expectation) form**: `E[F (K_x) G (K_y) 1(x ↮ y)] ≤ E F (K_x) E G (K_y)`
for the continuity class, under the finiteness hypotheses of the paper. -/
theorem twoCluster_functional_toReal_le [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y))
    (hFfin : (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) ≠ ⊤)
    (hHfin : (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤) :
    (∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)).toReal
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)).toReal *
          (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)).toReal := by
  have hle := twoCluster_functional_lintegral_le G p hp x y 𝓔 h𝓔mono h𝓔 hF0 hH0 hFmono hHmono
    hFcont hHcont hFmeas hHmeas
  have hfinR : (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
      (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤ :=
    ENNReal.mul_ne_top hFfin hHfin
  have hfinL : (∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
      ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinR hle
  have h := (ENNReal.toReal_le_toReal hfinL hfinR).mpr hle
  rwa [ENNReal.toReal_mul] at h

/-- **Lemma I.2.1(iii)** in real form: `0 ≤ E F G - E F E G ≤ E[F G 1(x ↔ y)]`, first half. -/
theorem fkg_functional_toReal_le [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (x y : V) (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y))
    (hFfin : (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) ≠ ⊤)
    (hHfin : (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤)
    (hFGfin : (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y))
      ∂(edgeLaw p)) ≠ ⊤) :
    (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)).toReal *
        (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)).toReal
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y))
          ∂(edgeLaw p)).toReal := by
  have hle := fkg_functional_lintegral_le G p x y 𝓔 h𝓔mono hF0 hH0 hFmono hHmono hFcont hHcont
    hFmeas hHmeas
  have hfinL : (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
      (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) ≠ ⊤ :=
    ENNReal.mul_ne_top hFfin hHfin
  have h := (ENNReal.toReal_le_toReal hfinL hFGfin).mpr hle
  rwa [ENNReal.toReal_mul] at h

end RealForms

end Percolation

end PercLib.CriticalLRP
