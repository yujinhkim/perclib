/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Standardized pivotal and binomial weights for the source defect

Model weights and error definitions from the reviewed D1D packet. The source
carries two distinct objects: derivative standardization itself and the exact
algebra of the resulting error. These definitions do not assume the missing
interchange of derivative with an infinite sum.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Defect
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.VolumeMoments.ErrorTerms
public import PercLib.CriticalLRP.MassTransportI41

@[expose] public section

namespace PercLib.CriticalLRP

namespace PivotFlux

open MeasureTheory Orchestration
open scoped ENNReal NNReal

variable (M : SourceModelData)

/-- The standardized `p = 1` pivotal weight of a single edge flip, at the source model.

`pivotWeight M r omega a b c` is the change of `|K_a|` (counted at the anchor `a`) when the
edge `{b,c}` is opened, *given* that `a` is connected to `b`, that `b` is not connected to
`c`, and that `c` lies in the ball `B_r(b)`: opening the edge merges `K_b` with `K_c`, so
the cluster volume grows by exactly `|K_c|`.  The three indicators are exactly the
`p = 1` collapse of the two binomial weights of `FiniteRusso.Binomial`; the only
difference is that `ENNReal`-valued subtraction is never taken, so an infinite cluster at
`c` contributes `top` rather than `0`.  The derivative factor `b_c|K'(r)|` is *not* part of
the weight: it is the standardization carried by the ODE statements below. -/
noncomputable def pivotWeight (r : ℝ) (ω : Config M.V) (a b c : M.V) : ℝ≥0∞ :=
  configIndicator {ω' : Config M.V | Connects ω' a b} ω *
    (if M.S.dist c b ≤ r then 1 else 0) *
    configIndicator {ω' : Config M.V | ¬ Connects ω' b c} ω * clusterVol ω c


/-- The root-anchored ball sum `sum_{y in B_r} 1(y notin K_0)|K_y|` as an `ENNReal` `tsum`
over the whole lattice.  All but finitely many terms vanish, because `B_r` is finite. -/
noncomputable def ballSum (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑' c : M.V, (if M.S.ρ (toVec c) ≤ r then 1 else 0) *
    configIndicator {ω' : Config M.V | ¬ Connects ω' (0 : M.V) c} ω * clusterVol ω c


/-- The paper's double sum of Lemma I.4.1 at `p = 1`:
`sum_{x in K} sum_{y in B_r(x)} 1(y notin K)|K_y|`, the integrand of the right-hand side of
(I.4.5) before the mass-transport step. -/
noncomputable def paperSum (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑' b : M.V, ∑' c : M.V, pivotWeight M r ω 0 b c


/-- The integrand after the mass-transport step:
`|K_0| sum_{y in B_r} 1(y notin K_0)|K_y|`, i.e. (definitionally) the integrand of
`E1Sign.exclMass`. -/
noncomputable def exclIntegrand (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  clusterVol ω (0 : M.V) * ballSum M r ω


/-- The standardization error `E_{0,r} = 1 - |K'(r)| |B_r| r^{a+1}` of the source, at the
model's own kernel.  `VolumeMoments.oneSubE0` is `1 - E_{0,r}` multiplied out. -/
noncomputable def cutE0 (r : ℝ) : ℝ :=
  1 - VolumeMoments.oneSubE0 |deriv M.K r| ((M.ball r).ncard : ℝ) r M.α


/-- The source defect `E_{1,r}` at the model's own cutoff moments. -/
noncomputable def cutE1 (r : ℝ) : ℝ :=
  VolumeMoments.cE1 (M.cutMassAt r 0).toReal (E1Sign.pairMass M r).toReal
    (E1Sign.connMass M r).toReal ((M.ball r).ncard : ℝ)

end PivotFlux
end PercLib.CriticalLRP

/-! ## Mass transport of the standardized flux (Lemma I.4.1, `p = 1`) -/

namespace PercLib.CriticalLRP
namespace PivotFlux

open MeasureTheory Orchestration
open scoped ENNReal NNReal

variable (M : SourceModelData)


/-- The `p`-th pivotal weight of a single edge flip: the change
`(|K_b| + |K_c|)^p − |K_b|^p` of the `p`-th cluster moment when the edge `{b,c}` merges the two
clusters, with the source's `ENNReal` convention for the difference (taken in `ℝ`). -/
noncomputable def binomWeight (p : ℕ) (r : ℝ) (ω : Config M.V) (a b c : M.V) : ℝ≥0∞ :=
  configIndicator {ω' : Config M.V | Connects ω' a b} ω *
    (if M.S.dist c b ≤ r then 1 else 0) *
    configIndicator {ω' : Config M.V | ¬ Connects ω' b c} ω *
    ENNReal.ofReal ((clusterVolR ω b + clusterVolR ω c) ^ p - clusterVolR ω b ^ p)


/-- The `p`-th flux double sum `sum_{x in K} sum_{y in B_r(x)} 1(y notin K)
((|K|+|K_y|)^p - |K|^p)` of Lemma I.4.1. -/
noncomputable def paperSumP (p : ℕ) (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑' b : M.V, ∑' c : M.V, binomWeight M p r ω 0 b c


/-- The rooted `p`-th flux integrand after the mass-transport step. -/
noncomputable def rootedSumP (p : ℕ) (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  clusterVol ω (0 : M.V) *
    ∑' c : M.V, (if M.S.ρ (toVec c) ≤ r then 1 else 0) *
      configIndicator {ω' : Config M.V | ¬ Connects ω' (0 : M.V) c} ω *
      ENNReal.ofReal ((clusterVolR ω (0 : M.V) + clusterVolR ω c) ^ p -
        clusterVolR ω (0 : M.V) ^ p)

end PivotFlux

end PercLib.CriticalLRP
