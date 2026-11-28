/-
Standalone development for swarm smwzuf8hm member m4: the weak-convergence hypothesis of the
I.1.7 chain, in the exact shape used by `PercLib.CriticalLRP.Analysis.ClusterVolumeTail.I17`,
derived from all-order moment asymptotics.
-/
module

public import PercLib.CriticalLRP.Analysis.MomentToChiSquare.Convergence
public import PercLib.CriticalLRP.Analysis.MomentToChiSquare.GaussianMoments

/-!
# The `hconv` hypothesis of the I.1.7 chain from moment asymptotics

`PercLib.CriticalLRP.Analysis.ClusterVolumeTail.I17` (`tendsto_tail_I17_of_moments`) and
`Orchestration`'s `model_tail_from_cutMoment` take as an explicit hypothesis the weak convergence

  `Tendsto (fun r => Measure.toProbabilityMeasure (sizeBiasedLaw (mu r))) atTop
     (𝓝 (Measure.toProbabilityMeasure Qinf))`

to `Qinf = law (Z ^ 2)`, `Z` standard normal (Proposition I.3.2's `Q∞` in the application of
(I.1.7)). The present file derives that hypothesis from the all-order moment asymptotics
`∫ x ^ k ∂(mu r) → (2k-1)!!`, by combining

* `tendsto_toProbabilityMeasure_chiSq` (`MomentToChiSquare.lean`) — moment asymptotics give weak
  convergence to `gammaMeasure (1/2) (1/2)`, and
* `Qinf_eq_gammaMeasure` (`GaussianMoments.lean`) — `Qinf` *is* `gammaMeasure (1/2) (1/2)`.

No moment asymptotics are proved here; they stay an explicit input, as in the source.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace SwarmM4

open PercLib.CriticalLRP.MomentProblem in
/-- **The `hconv` hypothesis of `Analysis/ClusterVolumeTail/I17`, from moment asymptotics.** For a
radius-indexed family of probability laws on `[0,∞)` whose `k`-th moments tend to `(2k-1)!!`, the
laws converge weakly to `Qinf`, the law of `Z ^ 2` for standard normal `Z`. -/
theorem tendsto_toProbabilityMeasure_Qinf (mu : ℝ → Measure ℝ)
    [inst : ∀ r, IsProbabilityMeasure (mu r)]
    (hsup : ∀ r, mu r (Set.Iio (0 : ℝ)) = 0)
    (hint : ∀ (r : ℝ) (k : ℕ), Integrable (fun x : ℝ => x ^ k) (mu r))
    (hmom : ∀ k : ℕ, Tendsto (fun r : ℝ => ∫ x, x ^ k ∂(mu r)) atTop
      (𝓝 ((oddFact k : ℝ)))) :
    Tendsto (fun r => Measure.toProbabilityMeasure (mu r)) atTop
      (𝓝 (Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf)) := by
  have h := tendsto_toProbabilityMeasure_chiSq mu hsup hint hmom
  have hcoe : (Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf : Measure ℝ)
      = (chiSq : Measure ℝ) := by
    have h1 : (Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf : Measure ℝ)
        = PercLib.CriticalLRP.Anchor.Qinf := rfl
    have h2 : (chiSq : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2) := rfl
    rw [h1, h2, Qinf_eq_gammaMeasure]
  have hgoal : Measure.toProbabilityMeasure PercLib.CriticalLRP.Anchor.Qinf = chiSq :=
    Subtype.ext hcoe
  rw [hgoal]
  exact h

end SwarmM4

/-! ### Axiom audit -/

set_option linter.hashCommand false

#print axioms SwarmM4.tendsto_toProbabilityMeasure_Qinf
