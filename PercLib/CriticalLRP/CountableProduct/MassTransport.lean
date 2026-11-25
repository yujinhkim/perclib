/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The mass-transport principle of Hutchcroft, *Critical long-range percolation I*,
at the level of the **genuine countable-product edge law** on `ℤ^d`.

The paper uses the mass-transport principle twice in the proof of Lemma I.5.8
(`eq:x12_derivative`):

* to exchange the roles of `0` and `x` in `∑_{x∈K} ∑_{y∈B_r(x)} …`, i.e. to replace
  the `x`-anchored ball by the origin-anchored ball; and
* to "exchange the roles of `0` and `y`", which is the step analysed in
  `I58Collapse.lean`.

The first is an instance of the single identity proved here:

    ∫ ∑_{x ∈ K_0} g x  dP  =  ∫ |K_0| · g 0  dP

for a translation-invariant law `P` on configurations and a nonnegative measurable
translation-covariant kernel `g`, `g (x + t) (shiftConfig t ω) = g x ω`.

This is *not* a reindexing statement about `tsum`
(cf. `Analysis/MassTransport.lean`): it uses the invariance
`μ.map (shiftConfig t) = μ` of the measure together with `lintegral_map`, in the same
way as `MassTransportI41.i41_massTransport`.  Everything is `ℝ≥0∞`-valued, so no
summability or integrability hypothesis is needed.

No `sorry`, no `admit`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.MassTransportI41

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal

namespace PercLib.CriticalLRP

variable {d : ℕ}

/-- **Per-site transport.**  For a translation-invariant law, the `P`-integral of
`1(0 ↔ x) · g x` does not depend on `x` once `g` is re-indexed at the origin. -/
theorem lintegral_connects_mul_shift
    (μ : Measure (Config (Fin d → ℤ))) (hμ : ∀ t : Fin d → ℤ, μ.map (shiftConfig t) = μ)
    (g : (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞)
    (hg : ∀ x, Measurable (g x))
    (hcov : ∀ (x t : Fin d → ℤ) (ω), g (x + t) (shiftConfig t ω) = g x ω)
    (x : Fin d → ℤ) :
    ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω ∂μ
      = ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω * g 0 ω ∂μ := by
  classical
  have hmeas : Measurable fun ω : Config (Fin d → ℤ) =>
      configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω :=
    (measurable_configIndicator (measurableSet_connects 0 x)).mul (hg x)
  have hind : ∀ ω : Config (Fin d → ℤ),
      configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} (shiftConfig x ω)
        = configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω := by
    intro ω
    have hiff : (shiftConfig x ω ∈ {ω' : Config (Fin d → ℤ) | Connects ω' 0 x})
        ↔ (ω ∈ {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0}) := by
      simpa using connects_shiftConfig_iff x ω (-x) 0
    simp only [configIndicator, Set.indicator_apply, hiff]
  have hcovx : ∀ ω : Config (Fin d → ℤ), g x (shiftConfig x ω) = g 0 ω := by
    intro ω
    simpa using hcov 0 x ω
  calc ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω ∂μ
      = ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω
          ∂(μ.map (shiftConfig x)) := by rw [hμ x]
    _ = ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} (shiftConfig x ω)
          * g x (shiftConfig x ω) ∂μ :=
        lintegral_map hmeas (measurable_shiftConfig x)
    _ = ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω * g 0 ω ∂μ :=
        lintegral_congr fun ω => by rw [hind ω, hcovx ω]

/-- **Mass-transport principle for the countable-product edge law of `ℤ^d`.**
For a translation-invariant law `μ` on configurations and a nonnegative measurable
translation-covariant kernel `g`,

    ∫ ∑_{x ∈ K_0} g x  dμ  =  ∫ |K_0| · g 0  dμ ,

where `∑_{x ∈ K_0} g x` is written out as `∑' x, 1(0 ↔ x) · g x` and `|K_0|` is the
`ℝ≥0∞` cluster volume `clusterVol`. -/
theorem lintegral_cluster_massTransport
    (μ : Measure (Config (Fin d → ℤ))) (hμ : ∀ t : Fin d → ℤ, μ.map (shiftConfig t) = μ)
    (g : (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞)
    (hg : ∀ x, Measurable (g x))
    (hcov : ∀ (x t : Fin d → ℤ) (ω), g (x + t) (shiftConfig t ω) = g x ω) :
    ∫⁻ ω, (∑' x, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω) ∂μ
      = ∫⁻ ω, clusterVol ω 0 * g 0 ω ∂μ := by
  classical
  have hstep : ∀ x : Fin d → ℤ,
      ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω ∂μ
        = ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω
            * g 0 ω ∂μ :=
    fun x => lintegral_connects_mul_shift μ hμ g hg hcov x
  have hsum : ∀ ω : Config (Fin d → ℤ),
      (∑' x, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω)
        = clusterVol ω 0 := by
    intro ω
    rw [← tsum_connects_indicator ω 0]
    simpa [Equiv.neg_apply] using Equiv.tsum_eq (Equiv.neg (Fin d → ℤ))
      (fun w : Fin d → ℤ => configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' w 0} ω)
  calc ∫⁻ ω, (∑' x, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω) ∂μ
      = ∑' x, ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω * g x ω ∂μ :=
        lintegral_tsum fun x =>
          ((measurable_configIndicator (measurableSet_connects 0 x)).mul (hg x)).aemeasurable
    _ = ∑' x, ∫⁻ ω, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω
            * g 0 ω ∂μ := tsum_congr hstep
    _ = ∫⁻ ω, (∑' x, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω
            * g 0 ω) ∂μ :=
        (lintegral_tsum fun x =>
          ((measurable_configIndicator (measurableSet_connects (-x) 0)).mul
            (hg 0)).aemeasurable).symm
    _ = ∫⁻ ω, (∑' x, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (-x) 0} ω)
            * g 0 ω ∂μ :=
        lintegral_congr fun _ => ENNReal.tsum_mul_right
    _ = ∫⁻ ω, clusterVol ω 0 * g 0 ω ∂μ :=
        lintegral_congr fun ω => by rw [hsum ω]

/-- **The paper's first transport step, `B_r(x) ↩ B_r`.**  With the ball stored as the
finite displacement set `S = B_r` and the integrand written in the relative coordinate
`w = y - x`, the cluster sum transports to a factor `|K_0|`:

    ∫ ∑_{x ∈ K_0} ∑_{w ∈ S} φ x w  dP  =  ∫ |K_0| ∑_{w ∈ S} φ 0 w  dP .

This is the step "the second equality follows by using the mass-transport principle to
exchange the roles of `0` and `x`" in the proof of Lemma I.5.8, in the form it is used
there: the `x`-anchored ball `B_r(x)` is replaced by the origin-anchored ball `B_r`. -/
theorem lintegral_cluster_ball_massTransport
    (μ : Measure (Config (Fin d → ℤ))) (hμ : ∀ t : Fin d → ℤ, μ.map (shiftConfig t) = μ)
    (S : Finset (Fin d → ℤ))
    (φ : (Fin d → ℤ) → (Fin d → ℤ) → Config (Fin d → ℤ) → ℝ≥0∞)
    (hφ : ∀ (x w : Fin d → ℤ), Measurable (φ x w))
    (hφcov : ∀ (x t w : Fin d → ℤ) (ω), φ (x + t) w (shiftConfig t ω) = φ x w ω) :
    ∫⁻ ω, (∑' x, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω
        * (∑ w ∈ S, φ x w ω)) ∂μ
      = ∫⁻ ω, clusterVol ω 0 * (∑ w ∈ S, φ 0 w ω) ∂μ := by
  have hg : ∀ x : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) => ∑ w ∈ S, φ x w ω :=
    fun x => Finset.measurable_sum S (fun w _ => hφ x w)
  have hcov : ∀ (x t : Fin d → ℤ) (ω : Config (Fin d → ℤ)),
      (∑ w ∈ S, φ (x + t) w (shiftConfig t ω)) = ∑ w ∈ S, φ x w ω := by
    intro x t ω
    exact Finset.sum_congr rfl fun w _ => hφcov x t w ω
  exact lintegral_cluster_massTransport μ hμ (fun x ω => ∑ w ∈ S, φ x w ω) hg hcov

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.lintegral_connects_mul_shift
#print axioms PercLib.CriticalLRP.lintegral_cluster_massTransport
#print axioms PercLib.CriticalLRP.lintegral_cluster_ball_massTransport