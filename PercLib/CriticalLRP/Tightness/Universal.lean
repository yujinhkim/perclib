/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Universal tightness for the canonical countable long-range model

The real-threshold ancestor-closure/BK argument proves both per-scale displays (2.8) and (2.9)
for every nonempty finite window in a countable weighted graph. For the long-range parameters
`β : ℝ≥0` and nonnegative finite real `J`, the strict edge-probability hypothesis is automatic.
The existing edian arithmetic converts these displays into the tail bounds (2.5), (2.6), (2.7),
the `UniversalTightnessI23` bundle and its moment-ratio corollary.

As shown by `EndpointCounterexample`, the printed `k = 0` endpoint of Theorem 2.3 is false.
Every per-scale hypothesis here retains `1 ≤ k`, exactly as the source's proof requires.
-/
module

public import PercLib.CriticalLRP.Tightness.Infinite.Canonical
public import PercLib.CriticalLRP.Tightness.DisplaysToTightness

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace PercLib.CriticalLRP
namespace Percolation

open MeasureTheory Set
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Display (2.8)** for an arbitrary countable independent-edge law, at real thresholds. -/
theorem display28_edgeMeasure (W : Finset V) (hW : W.Nonempty)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    Display28 (edgeMeasure p) (fun ω => clusterMaxVol ω W) := by
  intro lam k hlam hk
  rw [edgeMeasure_eq_edgeLaw]
  exact Hutchcroft.Countable.canonicalMax_pow_bound_anyV W hW hlam hk p hp

/-- **Display (2.9)** for an arbitrary countable independent-edge law, at real thresholds. -/
theorem display29_edgeMeasure (W : Finset V) (hW : W.Nonempty) (u : V)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    Display29 (edgeMeasure p) (fun ω => clusterMaxVol ω W)
      (fun ω => clusterVolIn ω u (W : Set V)) := by
  intro lam k hlam hk
  rw [edgeMeasure_eq_edgeLaw]
  exact Hutchcroft.Countable.canonicalMeets_pow_bound_anyV W hW u hlam hk p hp

/-- **Theorem 2.3 (2.8)** for the actual long-range law, for every real `lam ≥ 1` and every
natural `k ≥ 1`. -/
theorem display28_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) :
    Display28 (longRangeMeasure J hJ β) (fun ω => clusterMaxVol ω W) := by
  rw [longRangeMeasure]
  exact display28_edgeMeasure W hW _ (bernoulliEdgeProb_lt_one hJ β)

/-- **Theorem 2.3 (2.9)** for the actual long-range law. -/
theorem display29_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) (u : V) :
    Display29 (longRangeMeasure J hJ β) (fun ω => clusterMaxVol ω W)
      (fun ω => clusterVolIn ω u (W : Set V)) := by
  rw [longRangeMeasure]
  exact display29_edgeMeasure W hW u _ (bernoulliEdgeProb_lt_one hJ β)

/-- Both per-scale displays of the corrected Theorem 2.3, in one package. -/
theorem per_scale_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) (u : V) :
    Display28 (longRangeMeasure J hJ β) (fun ω => clusterMaxVol ω W) ∧
    Display29 (longRangeMeasure J hJ β) (fun ω => clusterMaxVol ω W)
      (fun ω => clusterVolIn ω u (W : Set V)) :=
  ⟨display28_longRange hJ β W hW, display29_longRange hJ β W hW u⟩

/-- **(2.5)/(I.2.4)** for the actual long-range law. -/
theorem tailMaxI24_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) :
    TailMaxI24 (longRangeMeasure J hJ β) (fun ω => clusterMaxVol ω W)
      (edianMaxVol (longRangeMeasure J hJ β) W (exists_edianMaxVol W)) :=
  tailMaxI24_at_edian W (display28_longRange hJ β W hW)

/-- **(2.6)/(I.2.5)** for the actual long-range law. -/
theorem lowerI25_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) :
    LowerI25 (longRangeMeasure J hJ β) (fun ω => clusterMaxVol ω W)
      (edianMaxVol (longRangeMeasure J hJ β) W (exists_edianMaxVol W)) :=
  lowerI25_at_edian hW (display28_longRange hJ β W hW)

/-- **(2.7)/(I.2.6)** for the actual long-range law. -/
theorem tailI26_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) (u : V) :
    TailI26 (longRangeMeasure J hJ β) (fun ω => clusterVolIn ω u (W : Set V))
      (edianMaxVol (longRangeMeasure J hJ β) W (exists_edianMaxVol W)) :=
  tailI26_at_clusterVolIn W u (display29_longRange hJ β W hW u)

/-- **Universal tightness (I.2.3)** for the canonical countable long-range model: the edian exists
for the finite window, and both exponential-tail properties hold at it. -/
theorem universalTightnessI23_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) (u : V) :
    UniversalTightnessI23 (longRangeMeasure J hJ β) (fun ω => clusterMaxVol ω W)
      (fun ω => clusterVolIn ω u (W : Set V))
      (edianMaxVol (longRangeMeasure J hJ β) W (exists_edianMaxVol W)) :=
  universalTightnessI23_of_displays W u (display28_longRange hJ β W hW)
    (display29_longRange hJ β W hW u)

/-- **Corollary I.2.5** at the edian for the actual long-range law, now with no remaining
per-scale hypothesis. -/
theorem corollary_I_2_5_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (u : V) (hu : u ∈ W) (p q : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, clusterVolIn ω u (W : Set V) ^ (p + q) ∂(longRangeMeasure J hJ β) ≤
      ENNReal.ofReal (Tightness.momentConst p q) *
        ENNReal.ofReal ((edianMaxVol (longRangeMeasure J hJ β) W
          (exists_edianMaxVol W) : ℝ) ^ q) *
        ∫⁻ ω, clusterVolIn ω u (W : Set V) ^ p ∂(longRangeMeasure J hJ β) := by
  have hW : W.Nonempty := ⟨u, hu⟩
  exact corollary_I_2_5_at_edian_of_displays W u hu (display28_longRange hJ β W hW)
    (display29_longRange hJ β W hW u) p q hp

/-- **Corollary I.2.5 for real exponents `p, q ≥ 0`**, with the real-exponent layer-cake
constant `momentConstFull`. This is the source's exponent range, rather than merely naturals. -/
theorem corollary_I_2_5_real_longRange {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W : Finset V) (hW : W.Nonempty) (u : V) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∫⁻ ω, clusterVolIn ω u (W : Set V) ^ (p + q) ∂(longRangeMeasure J hJ β) ≤
      ENNReal.ofReal (momentConstFull p q) *
        ENNReal.ofReal ((edianMaxVol (longRangeMeasure J hJ β) W
          (exists_edianMaxVol W) : ℝ) ^ q) *
        ∫⁻ ω, clusterVolIn ω u (W : Set V) ^ p ∂(longRangeMeasure J hJ β) := by
  refine corollary_I_2_5_real_nonneg (measurable_clusterVolIn u (W : Set V)) ?_
    (one_le_edianMaxVol W (exists_edianMaxVol W))
    ((universalTightnessI23_longRange hJ β W hW u).single_tail) hp hq
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards with ω
  exact clusterVolIn_ne_top_of_finite ω u W.finite_toSet

end Percolation
end PercLib.CriticalLRP
