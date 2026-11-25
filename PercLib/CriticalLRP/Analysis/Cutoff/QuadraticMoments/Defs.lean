/-
Swarm `smwv9oxuv`, member `m4`, direction `d1`.

# The `p = 2` (quadratic) cluster-volume functional and its capped approximations

The `p = 1` infinite-volume Russo exchange (`RussoInf/Exchange`, `RussoInf/DominatedFlux`,
`RussoInf/CutoffFluxMajorant`) controls the pivotal flux of a functional `g` of the cluster of
`o` through the **supremum bound** `m` of `g`: every pivot weight is at most `2 m` times the
probability that the flipped edge touches the cluster (`abs_pivotalFlux_le`,
`summable_abs_weight_touch`).  At `p = 2` the functional is `g ω = |K_o|²`, which has no finite
supremum, so that route gives nothing at all: the dominating series
`e ↦ |c e| · 2 m · P(e touches K_o)` is infinite for every edge.

The objects here are the ones needed to replace the supremum bound by the **exact quadratic
increment** `2 |K| |K_y| + |K_y|²` of the source's Lemma I.4.1 at `p = 2`.  Nothing is asserted
in this file: it only names

* `realVol o ω` — the cluster volume `|K_o|` as a real number;
* `sqVol o ω` — its square, the `p = 2` observable;
* `capVol o N ω`, `capSqVol o N ω` — the cap at level `N ≥ 0`, whose pivotal flux is controlled
  by the `p = 1` machinery because it *is* bounded by `N²`.

The cap is a proof device only: on the event `|K_o| ≤ N` the capped observable agrees with the
`p = 2` one, and the cap is removed in `Main.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv

/-!
# Capped cluster-volume observables for the second cutoff moment

Real and extended-real volumes, the square functional and its monotone cap.  The cap is
used only to dominate quadratic pivotal flux by the first-moment flux; no radius derivative
is asserted here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace CappedMoments

variable {V : Type*} [Countable V]

/-- The cluster volume `|K_o|` of the origin, read as a real number.

For configurations with an infinite cluster of `o` this is `0` (the `ℝ≥0∞ → ℝ` coercion is
junk at `⊤`); every statement below that uses monotonicity of this quantity therefore carries an
explicit finiteness hypothesis, and the `p = 2` statements are used only on the event where the
second cutoff moment is finite. -/
noncomputable def realVol (o : V) (ω : Config V) : ℝ := (clusterVol ω o).toReal

/-- The `p = 2` observable: the square of the cluster volume of `o`. -/
noncomputable def sqVol (o : V) (ω : Config V) : ℝ := realVol o ω ^ 2

/-- The cluster volume capped at level `N`, read as a real number.  The cap is taken in `ℝ≥0∞`
first, so that an infinite cluster is capped at `N` rather than being sent to the junk value `0`
of `⊤.toReal`; this makes the capped quantity monotone in the configuration with no side
condition. -/
noncomputable def capVol (o : V) (N : ℝ) (ω : Config V) : ℝ :=
  (min (clusterVol ω o) (ENNReal.ofReal N)).toReal

/-- The `p = 2` observable with the cluster volume capped at level `N ≥ 0`.  For `N ≥ 0` this is
bounded by `N ^ 2`, so the `p = 1` pivot bounds (`abs_pivotalFlux_le`) apply to it. -/
noncomputable def capSqVol (o : V) (N : ℝ) (ω : Config V) : ℝ := capVol o N ω ^ 2

theorem realVol_nonneg (o : V) (ω : Config V) : 0 ≤ realVol o ω := ENNReal.toReal_nonneg

theorem capVol_eq (o : V) (N : ℝ) (ω : Config V) :
    capVol o N ω = (min (clusterVol ω o) (ENNReal.ofReal N)).toReal := rfl

theorem sqVol_nonneg (o : V) (ω : Config V) : 0 ≤ sqVol o ω := sq_nonneg _

/-- Monotonicity of the real cluster volume, on the event that the larger volume is finite. -/
theorem realVol_mono {ω ω' : Config V} {o : V} (hne : clusterVol ω' o ≠ ⊤)
    (h : clusterVol ω o ≤ clusterVol ω' o) : realVol o ω ≤ realVol o ω' :=
  ENNReal.toReal_mono hne h

theorem realVol_congr {ω ω' : Config V} {o : V} (h : clusterVol ω o = clusterVol ω' o) :
    realVol o ω = realVol o ω' := by
  simp only [realVol, h]

/-- The capped volume is monotone in the configuration, with no finiteness side condition. -/
theorem capVol_mono {ω ω' : Config V} {o : V} (N : ℝ) (h : clusterVol ω o ≤ clusterVol ω' o) :
    capVol o N ω ≤ capVol o N ω' :=
  ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _))
    (min_le_min h le_rfl)

theorem capVol_nonneg (o : V) (N : ℝ) (ω : Config V) : 0 ≤ capVol o N ω :=
  ENNReal.toReal_nonneg

theorem capVol_le (o : V) {N : ℝ} (hN : 0 ≤ N) (ω : Config V) : capVol o N ω ≤ N := by
  have h : min (clusterVol ω o) (ENNReal.ofReal N) ≤ ENNReal.ofReal N := min_le_right _ _
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hN] at this

theorem capVol_le_realVol {o : V} {N : ℝ} {ω : Config V} (hne : clusterVol ω o ≠ ⊤) :
    capVol o N ω ≤ realVol o ω :=
  ENNReal.toReal_mono hne (min_le_left _ _)

theorem capSqVol_nonneg (o : V) (N : ℝ) (ω : Config V) : 0 ≤ capSqVol o N ω := sq_nonneg _

theorem capSqVol_mono {ω ω' : Config V} {o : V} {N : ℝ} (hN : 0 ≤ N)
    (h : clusterVol ω o ≤ clusterVol ω' o) : capSqVol o N ω ≤ capSqVol o N ω' :=
  pow_le_pow_left₀ (capVol_nonneg o N ω) (capVol_mono N h) 2

theorem capSqVol_le (o : V) {N : ℝ} (hN : 0 ≤ N) (ω : Config V) : capSqVol o N ω ≤ N ^ 2 := by
  have h1 : capVol o N ω ≤ N := capVol_le o hN ω
  have h2 : 0 ≤ capVol o N ω := capVol_nonneg o N ω
  exact pow_le_pow_left₀ h2 h1 2

theorem sqVol_eq_of_le_cap {o : V} {N : ℝ} (ω : Config V) (h : clusterVol ω o ≠ ⊤)
    (hle : clusterVol ω o ≤ ENNReal.ofReal N) : capSqVol o N ω = sqVol o ω := by
  have hmin : min (clusterVol ω o) (ENNReal.ofReal N) = clusterVol ω o := min_eq_left hle
  have hc : capVol o N ω = realVol o ω := by simp only [capVol, realVol, hmin]
  simp only [capSqVol, sqVol, hc]

theorem measurable_realVol (o : V) : Measurable (realVol o) :=
  ENNReal.measurable_toReal.comp (measurable_clusterVol o)

theorem measurable_capVol (o : V) (N : ℝ) : Measurable (capVol o N) :=
  ENNReal.measurable_toReal.comp
    ((measurable_clusterVol o).min measurable_const)

theorem measurable_sqVol (o : V) : Measurable (sqVol o) :=
  (measurable_realVol o).pow_const 2

theorem measurable_capSqVol (o : V) (N : ℝ) : Measurable (capSqVol o N) :=
  (measurable_capVol o N).pow_const 2

end CappedMoments

end PercLib.CriticalLRP
