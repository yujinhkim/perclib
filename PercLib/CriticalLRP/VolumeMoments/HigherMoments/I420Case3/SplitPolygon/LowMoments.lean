/- Integrated from `.scratch/case3-split-draft/LowMoments.lean` at production base
`9e49e56e18f74a180a1de08f2df47dedfaa5888b`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.TailLower
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffFourthMoments

/-! # Finite low-order cutoff moments and the cubic normalized error -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.hashCommand false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration
open Analysis.Route3

/-- In dimensions where the normalized source norm is a positive multiple of
`ℓ∞`, a finite first cutoff moment supplies every cutoff moment of order
`1,2,3,4` by the native third- and fourth-moment bounds. -/
theorem powMomentAt_ne_top_of_le_four (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ))
    {r : ℝ} (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) :
    ∀ m : ℕ, 1 ≤ m → m ≤ 4 → I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤ := by
  intro m hm hm4
  change M.cutMoment m r ≠ ⊤
  interval_cases m
  · exact h1
  · exact Orchestration.cutMoment_two_ne_top_of_one M hc hρ hr h1
  · exact Orchestration.cutMoment_three_ne_top_of_one M hc hρ hr h1
  · exact Orchestration.cutMoment_four_ne_top_of_one M hc hρ hr h1

/-- The normalized Case-3 error at `p = 3`, using the native third- and
fourth-moment bridges to discharge its entire required root-moment range. -/
theorem exists_case3_i421_cutPoly_source_of_tail_three (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        tailEnvelope C n)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    {c : ℝ} (hc : 0 < c)
    (hρ : ∀ z : M.V, M.S.ρ (toVec z) = c * (FiniteVolume.linfNorm z : ℝ))
    (h1 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) 3) atTop (𝓝 0) := by
  have hmom : ∀ r : ℝ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m → m ≤ 3 + 1 →
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤ := by
    intro r hr m hm hm4
    exact powMomentAt_ne_top_of_le_four M hc hρ (by linarith) (h1 r hr) m hm hm4
  exact exists_case3_i421_cutPoly_source_of_tail M hP hTri 𝓔 h𝓔mono h𝓔 3 ℓ
    (by omega) hℓ hθ0 hθ1 hTail hC hVolTail h2 hmom

#print axioms powMomentAt_ne_top_of_le_four
#print axioms exists_case3_i421_cutPoly_source_of_tail_three

end I420Case3

end PercLib.CriticalLRP
