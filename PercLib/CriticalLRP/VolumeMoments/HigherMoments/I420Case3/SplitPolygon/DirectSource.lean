/- Integrated from `.scratch/case3-split-draft/DirectSource.lean` at production base
`bcc1ad841c2aaf6a8d1dc28d5bf7cd885a304d65`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.DirectEventually
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.NearWindow

/-! # Direct Case-3 ratio limits at the actual source balls -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- The direct endpoint and middle-index Case-3 limits for the canonical cutoff
family on actual source balls. The normalized tree, polygon and near-ball work is
internal; moment finiteness, moment homogeneity and the source's two-moment inputs
remain explicit. -/
theorem case3_hAend_hAmid_cutPoly_source (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0))
    (hhom : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y =
          I420Case1.powMomentAt (M.cutProb r) (p - ℓ) 0)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    (hMb : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
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
  obtain ⟨c, C, hc, hC, hSplit⟩ := exists_hasSplitPolygonBound_cutPoly_near_far M hP hTri
  obtain ⟨c₀, hc₀, hχall⟩ := AuditM2.cutMassAt_ne_top_of_hP M hP
  obtain ⟨B, s, R, hB, hR, hcard, hfar, hratio⟩ := exists_source_near_far_ratio M hθ0 hθ1
  subst B
  subst R
  let W : ℝ → Finset M.V := fun r => (BallAverage.ball_finite M r).toFinset
  let Bthree : ℝ → ℝ := fun r => (M.nablaTail (r ^ θ)).toReal +
    (((s r).card : ℝ) / ((W r).card : ℝ)) * M.triSelf
  let Btail : ℝ → ℝ := fun r => C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))
  have hthree : Tendsto Bthree atTop (𝓝 0) := by
    have h := tendsto_near_far_factor M W s (fun r => r ^ θ)
      (tendsto_nablaTail_rpow M hθ0 hTail) hratio
    exact h
  have htail : Tendsto Btail atTop (𝓝 0) :=
    tendsto_rate_of_nablaTail M hc (tendsto_nablaTail_rpow M hc hTail)
  have hev : ∀ᶠ r : ℝ in atTop, 1 ≤ r := eventually_ge_atTop 1
  have hTree : ∀ (ℓ : ℕ), ℓ + 1 ≤ p → ∀ᶠ r in atTop,
      HasTreeExpansion (M.cutProb r) (0 : M.V) (W r) (ℓ + 1) (p - ℓ) p
        (cutPoly M r) (fun j => (I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℝ)) := by
    intro ℓ hℓ
    filter_upwards [hev] with r hr
    exact AuditM2.hasTreeExpansion_cutPoly M r (hχall r (by linarith)) (W r) hℓ
  have hPoly : ∀ᶠ r in atTop, HasSplitPolygonBound (M.cutProb r) (0 : M.V) (W r) p
      (cutPoly M r) (Bthree r) (Btail r) := by
    filter_upwards [hev] with r hr
    exact hSplit (by omega) hr (W r) (s r) (hcard r hr) (hfar r hr)
  have hcardEv : ∀ᶠ r in atTop, 0 < (W r).card := hev.mono hcard
  have hM1 : ∀ᶠ r in atTop, I420Case1.powMomentAt (M.cutProb r) 1 (0 : M.V) ≠ ⊤ := by
    filter_upwards [hev] with r hr
    rw [powMomentAt_cutProb_one M r]
    exact hχall r (by linarith)
  exact case3_hAend_hAmid_split_eventually (fun r => M.cutProb r) (0 : M.V) W 𝓔 h𝓔mono h𝓔 p hp
    (fun r e => AuditM2.cutProb_lt_one M r e) (fun r => cutPoly M r)
    (fun ℓ j => (I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℝ)) Bthree Btail
    (fun _ℓ j => AuditM1.composedCoeff_nonneg (_ℓ + 1) (p - _ℓ) j) hthree htail hTree hPoly
    hcardEv (hev.mono hhom) hM1 (hev.mono hMa) (hev.mono hMb) hc3 hgm

#print axioms case3_hAend_hAmid_cutPoly_source


end I420Case3

end PercLib.CriticalLRP
