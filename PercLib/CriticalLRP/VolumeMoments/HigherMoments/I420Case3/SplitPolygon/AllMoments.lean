module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.DirectTail
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffAllMoments

/-! # All-order root finiteness in the split-polygon Case-3 assembly -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.hashCommand false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.I420Case3

open Orchestration
open Analysis.Route3

/-- A finite first cutoff moment supplies every root moment needed at any fixed order. -/
theorem powMomentAt_ne_top_of_finite_first (M : SourceModelData) {r : ℝ}
    (h1 : M.cutMoment 1 r ≠ ⊤) (m : ℕ) :
    I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤ := by
  exact Orchestration.cutMoment_ne_top_of_one M r h1 m

/-- Direct all-order Case-3 decorrelation at the actual normalized source, with the
root finite-moment premise discharged from the first cutoff moment. -/
theorem case3_hAend_hAmid_cutPoly_source_of_tail_of_first (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        tailEnvelope C n)
    (h1 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hmom : ∀ (r : ℝ), 1 ≤ r → ∀ m : ℕ,
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤ := by
    intro r hr m
    exact powMomentAt_ne_top_of_finite_first M (h1 r hr) m
  exact case3_hAend_hAmid_cutPoly_source_of_tail M hP hTri 𝓔 h𝓔mono h𝓔 p hp
    hθ0 hθ1 hTail hC hVolTail (fun r hr => hmom r hr 2)
      (fun r hr ℓ _ => hmom r hr (ℓ + 1))

/-- Normalized Case-3 errors at an arbitrary admissible pair of exponents, with
all required root moments supplied by a finite first cutoff moment. -/
theorem exists_case3_i421_cutPoly_source_of_tail_of_first (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p)
    (hℓ : ℓ + 1 ≤ p) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        tailEnvelope C n)
    (h1 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  have hmom : ∀ (r : ℝ), 1 ≤ r → ∀ m : ℕ,
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤ := by
    intro r hr m
    exact powMomentAt_ne_top_of_finite_first M (h1 r hr) m
  exact exists_case3_i421_cutPoly_source_of_tail M hP hTri 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ
    hθ0 hθ1 hTail hC hVolTail (fun r hr => hmom r hr 2)
      (fun r hr m _ _ => hmom r hr m)

#print axioms powMomentAt_ne_top_of_finite_first
#print axioms case3_hAend_hAmid_cutPoly_source_of_tail_of_first
#print axioms exists_case3_i421_cutPoly_source_of_tail_of_first

end PercLib.CriticalLRP.I420Case3
