/- Integrated from `.scratch/case3-split-draft/MomentHom.lean` at production base
`015696de774b5636928e2c2aac650a1f806d0e10`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.DirectSource
public import PercLib.CriticalLRP.Correlation.SecondMomentPermutation
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Triangle

/-! # Translation homogeneity for all cutoff cluster moments -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- Any profile-preserving vertex permutation preserves every canonical cluster
moment, including its cutoff specialization. -/
theorem powMomentAt_cutProb_perm (M : SourceModelData) (r : ℝ) (g : M.V ≃ M.V)
    (hg : ∀ e : Sym2 M.V, M.cutProb r (Sym2.map g e) = M.cutProb r e)
    (a : ℕ) (x : M.V) :
    I420Case1.powMomentAt (M.cutProb r) a (g x) = I420Case1.powMomentAt (M.cutProb r) a x := by
  rw [AuditM1.powMomentAt_eq_lintegral_cardFun, AuditM1.powMomentAt_eq_lintegral_cardFun]
  exact TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig (M.cutProb r) g hg a x

/-- Translation invariance of every cutoff cluster moment. -/
theorem powMomentAt_cutProb_apply_eq_zero (M : SourceModelData) (r : ℝ) (a : ℕ) (y : M.V) :
    I420Case1.powMomentAt (M.cutProb r) a y = I420Case1.powMomentAt (M.cutProb r) a 0 := by
  let g : M.V ≃ M.V := Equiv.addRight y
  have h := powMomentAt_cutProb_perm M r g
    (fun e => E1Sign.cutProb_shift_invariant M r y e) a (0 : M.V)
  simpa [g] using h

/-- The direct source-ball Case-3 assembly with all window homogeneity and
window finiteness obligations discharged by translation invariance. Only the
root moment-finiteness range remains as a separate hypothesis. -/
theorem case3_hAend_hAmid_cutPoly_source_of_finite (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0))
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
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
  have hhom : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y =
          I420Case1.powMomentAt (M.cutProb r) (p - ℓ) 0 := by
    intro r _ ℓ _ y _
    exact powMomentAt_cutProb_apply_eq_zero M r (p - ℓ) y
  have hMb : ∀ (r : ℝ), 1 ≤ r → ∀ (ℓ : ℕ), ℓ + 1 ≤ p →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤ := by
    intro r hr ℓ hℓ y _
    rw [powMomentAt_cutProb_apply_eq_zero M r (p - ℓ) y]
    have hidx : p - ℓ - 1 + 1 = p - ℓ := by omega
    rw [← hidx]
    exact hMa r hr (p - ℓ - 1) (by omega)
  exact case3_hAend_hAmid_cutPoly_source M hP hTri 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hTail
    hhom hMa hMb hc3 hgm

#print axioms powMomentAt_cutProb_perm
#print axioms powMomentAt_cutProb_apply_eq_zero
#print axioms case3_hAend_hAmid_cutPoly_source_of_finite

end I420Case3

end PercLib.CriticalLRP
