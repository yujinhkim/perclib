/- Integrated from `.scratch/case3-split-draft/NearWindow.lean` at production base
`637558828ebcb855d2104f1d334e9a69c2d1368f`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Model
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Assembly
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.ModelAssembly
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Tails

/-! # Source windows and the near-ball/window cardinality ratio -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Asymptotics

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- Every source ball of nonnegative radius is nonempty as a finite set. -/
theorem source_ball_card_pos (M : SourceModelData) {r : ℝ} (hr : 0 ≤ r) :
    0 < (BallAverage.ball_finite M r).toFinset.card := by
  have h0 : (0 : M.V) ∈ M.ball r := by
    change M.S.ρ (toVec (0 : M.V)) ≤ r
    have hz : toVec (0 : M.V) = 0 := by funext i; simp [toVec]
    rw [hz, M.S.ρ_zero]
    exact hr
  have hm : (0 : M.V) ∈ (BallAverage.ball_finite M r).toFinset :=
    (Set.Finite.mem_toFinset (BallAverage.ball_finite M r)).2 h0
  exact Finset.card_pos.mpr ⟨0, hm⟩

/-- For every `0 < θ < 1`, the actual finite source balls admit near sets at scale
`r^θ` whose cardinality ratio tends to zero. The returned far-region statement is
exactly the one consumed by the near/far threefold estimate. -/
theorem exists_source_near_far_ratio (M : SourceModelData) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ B s : ℝ → Finset M.V, ∃ R : ℝ → ℝ,
      B = (fun r => (BallAverage.ball_finite M r).toFinset) ∧
      R = (fun r => r ^ θ) ∧
      (∀ r : ℝ, 1 ≤ r → 0 < (B r).card) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y ∈ B r, y ∉ s r → R r ≤ M.S.dist 0 y) ∧
      Tendsto (fun r => ((s r).card : ℝ) / ((B r).card : ℝ)) atTop (𝓝 0) := by
  classical
  obtain ⟨K, hK, hball⟩ := I418C.NearBall.exists_near_ball M
  let B : ℝ → Finset M.V := fun r => (BallAverage.ball_finite M r).toFinset
  let R : ℝ → ℝ := fun r => r ^ θ
  let s : ℝ → Finset M.V := fun r =>
    if h : 1 ≤ r ^ θ then Classical.choose (hball (r ^ θ) h) else ∅
  have hb : ∀ᶠ r in atTop, ((1 : ℝ) / 2) * r ^ M.d ≤ ((B r).card : ℝ) := by
    have h := Analysis.I420Case2.ballCard_eventually_ge M (c := (1 : ℝ) / 2) (by norm_num)
    filter_upwards [h] with r hr
    have hc : (B r).card = (M.ball r).ncard := by
      dsimp [B]
      exact (Set.ncard_eq_toFinset_card (M.ball r) (BallAverage.ball_finite M r)).symm
    rw [hc]
    exact hr
  have hr : ∀ᶠ r : ℝ in atTop, 1 ≤ r := eventually_ge_atTop 1
  have hs : ∀ᶠ r in atTop,
      (∀ y : M.V, y ∉ s r → R r ≤ M.S.dist 0 y) ∧
      ((s r).card : ℝ) ≤ K * (R r) ^ (M.d : ℝ) := by
    filter_upwards [hr] with r hr1
    have hR : 1 ≤ r ^ θ := Real.one_le_rpow hr1 hθ0.le
    have hspec := Classical.choose_spec (hball (r ^ θ) hR)
    rw [show s r = Classical.choose (hball (r ^ θ) hR) from by
      dsimp [s]
      exact dite_eq_left hR]
    exact hspec
  have hcard : ∀ r : ℝ, 1 ≤ r → 0 < (B r).card := by
    intro r hr1
    exact source_ball_card_pos M (by linarith)
  let γ : ℝ := (1 - θ) * (M.d : ℝ)
  have hγ : 0 < γ := by
    have hd : 0 < (M.d : ℝ) := by exact_mod_cast M.hd
    dsimp [γ]
    positivity
  have hq : ∀ᶠ r in atTop, 0 ≤ ((s r).card : ℝ) / ((B r).card : ℝ) ∧
      ((s r).card : ℝ) / ((B r).card : ℝ) ≤ 2 * K * r ^ (-γ) := by
    filter_upwards [hs, hb, hr] with r hsr hbr hr1
    have hrpos : 0 < r := by linarith
    have hbpos : (0 : ℝ) < ((B r).card : ℝ) := by
      have hd : (0 : ℝ) < r ^ M.d := by positivity
      linarith
    have hhalfpos : (0 : ℝ) < ((1 : ℝ) / 2) * r ^ M.d := by positivity
    have hqnonneg : 0 ≤ ((s r).card : ℝ) / ((B r).card : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    refine ⟨hqnonneg, ?_⟩
    calc ((s r).card : ℝ) / ((B r).card : ℝ)
        ≤ (K * (r ^ θ) ^ (M.d : ℝ)) / ((B r).card : ℝ) :=
          div_le_div_of_nonneg_right hsr.2 hbpos.le
      _ ≤ (K * (r ^ θ) ^ (M.d : ℝ)) / (((1 : ℝ) / 2) * r ^ M.d) :=
          div_le_div_of_nonneg_left (by positivity) hhalfpos hbr
      _ = 2 * K * (r ^ (θ * (M.d : ℝ)) / r ^ (M.d : ℝ)) := by
        rw [← Real.rpow_natCast r M.d, ← Real.rpow_mul hrpos.le]
        ring
      _ = 2 * K * r ^ (θ * (M.d : ℝ) - (M.d : ℝ)) := by
        rw [Real.rpow_sub hrpos]
      _ = 2 * K * r ^ (-γ) := by
        congr 2
        dsimp [γ]
        ring
  have hq0 : ∀ᶠ r in atTop, 0 ≤ ((s r).card : ℝ) / ((B r).card : ℝ) :=
    hq.mono fun r h => h.1
  have hqle : ∀ᶠ r in atTop,
      ((s r).card : ℝ) / ((B r).card : ℝ) ≤ 2 * K * r ^ (-γ) :=
    hq.mono fun r h => h.2
  have hl : Tendsto (fun r : ℝ => 2 * K * r ^ (-γ)) atTop (𝓝 0) := by
    have hp := tendsto_rpow_neg_atTop hγ
    simpa using hp.const_mul (2 * K)
  have hlim : Tendsto (fun r => ((s r).card : ℝ) / ((B r).card : ℝ)) atTop (𝓝 0) :=
    squeeze_zero' hq0 hqle hl
  refine ⟨B, s, R, rfl, rfl, hcard, ?_, hlim⟩
  intro r hr1
  have hR : 1 ≤ r ^ θ := Real.one_le_rpow hr1 hθ0.le
  have hspec := Classical.choose_spec (hball (r ^ θ) hR)
  intro y _ hy
  rw [show s r = Classical.choose (hball (r ^ θ) hR) from by
    dsimp [s]
    exact dite_eq_left hR] at hy
  exact hspec.1 y hy

/-- The canonical cutoff near/far error bound at actual source balls and the
power-scale near sets. The unrescaled triangle-tail limit supplies both the
near-factor decay and every power-rescaled higher-depth tail limit. -/
theorem exists_case3_i421_cutPoly_source (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0))
    (hMa : ∀ r : ℝ, 1 ≤ r → I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    (hMb : ∀ (r : ℝ), 1 ≤ r →
      ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
        I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  obtain ⟨B, s, R, hB, hR, hcard, hfar, hratio⟩ := exists_source_near_far_ratio M hθ0 hθ1
  subst B
  subst R
  exact case3_i421_cutPoly_near_far M hP hTri 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ
    (fun r => (BallAverage.ball_finite M r).toFinset) s
    (fun r => r ^ θ) (fun r hr => hcard r hr) (fun r hr => hfar r hr)
    (tendsto_nablaTail_rpow M hθ0 hTail) hratio (power_nablaTail_limits M hTail)
    hMa hMb hc3 hgm

end I420Case3

end PercLib.CriticalLRP
