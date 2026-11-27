/-
Integrated Ultramath work, swarm `smwyop3kc`, member `m2`.
Production worktree: `.scratch/critical-lrp-orchestration` (read only), HEAD
`2e544875fbae83810bd1aa1de1d8faddcdeacc05`.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.Handoff

/-!
# The `p = 3` second induction with positivity only at orders `1, 2, 3`

`HigherMoments.SecondInduction.moment_three_asymptotic_of_decorrelation` takes
the decorrelation limits `hAend`, `hAmid` and the first-moment normalization
`r c_r |B_r| E|K| → α`, and concludes

`E|K|³ ~ 3 (E|K|²/E|K|)² E|K|`   and   `E|K|³` regularly varying of index `5α`.

Its positivity hypothesis `hmom` quantifies over every order `m`, which at the
canonical cutoff model would require finiteness of all moments.  As for the
upper-bound step, the padding `padMom` reduces it to the orders `1, 2, 3` that
the proof consumes.

`case3_moment_three_asymptotic` then states the `p = 3` second-induction
conclusion at the actual source cutoff family `M.cutProb`, from the Case-3
decorrelation limits.  Those limits are exactly the conclusion of the shipped
`I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3` at `p = 3`, so the
HD(3)/ODE/triangle package of that theorem can be substituted for `hAend`,
`hAmid` here without change.
-/

@[expose] public section

noncomputable section

open Filter Topology
open PercLib.CriticalLRP.Analysis
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The `p = 3` second induction with positivity only at orders `1, 2, 3`.** -/
theorem moment_three_asymptotic_of_decorrelation_of_pos {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} {A : ℕ → ℝ → ℝ} {Bcard c : ℝ → ℝ}
    (hmom : ∀ m, 1 ≤ m → m ≤ 3 → ∀ r : ℝ, 0 < r → 0 < mom m r)
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α) (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    (hB : ∀ r, 0 < r → 0 < Bcard r)
    (hmass : ∀ r, 0 < r → A (3 - 1) r = A 0 r)
    (hderivId : ∀ r, 0 < r → HasDerivAt (fun s => mom 3 s)
      (c r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ r) r)
    (hAend : Tendsto (fun r => A 0 r / (Bcard r * (mom 1 r * mom 3 r))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 →
      Tendsto (fun r => A ℓ r / (Bcard r * (mom (ℓ + 1) r * mom (3 - ℓ) r))) atTop (𝓝 1))
    (hc : Tendsto (fun r => r * c r * Bcard r * mom 1 r) atTop (𝓝 α)) :
    Tendsto (fun r => mom 3 r / mixedMoment 3 mom r) atTop (𝓝 1) ∧
      RegularlyVaryingAtTop (mom 3) ((2 * (3 : ℝ) - 1) * α) := by
  have hmem1 : padMom 3 mom 1 = mom 1 :=
    funext fun r => padMom_apply_of_mem mom r ⟨le_refl 1, by norm_num⟩
  have hmem2 : padMom 3 mom 2 = mom 2 :=
    funext fun r => padMom_apply_of_mem mom r ⟨by norm_num, by norm_num⟩
  have hmem3 : padMom 3 mom 3 = mom 3 :=
    funext fun r => padMom_apply_of_mem mom r ⟨by norm_num, by norm_num⟩
  obtain ⟨hlim, hRV⟩ :=
    SecondInduction.moment_three_asymptotic_of_decorrelation (α := α) hα
      (mom := padMom 3 mom) (A := A) (Bcard := Bcard) (c := c)
      (padMom_pos hmom) (by rw [hmem1]; exact hmommeas1) (by rw [hmem2]; exact hmommeas2)
      (by rw [hmem1]; exact h1) (by rw [hmem2]; exact h2) hB hmass
      (fun r hr => by rw [hmem3]; exact hderivId r hr)
      (by rw [hmem1, hmem3]; exact hAend)
      (fun ℓ h1ℓ h2ℓ => by
        refine (hAmid ℓ h1ℓ h2ℓ).congr' (Eventually.of_forall fun r => ?_)
        have hA : padMom 3 mom (ℓ + 1) r = mom (ℓ + 1) r :=
          padMom_apply_of_mem mom r ⟨by omega, by omega⟩
        have hB' : padMom 3 mom (3 - ℓ) r = mom (3 - ℓ) r :=
          padMom_apply_of_mem mom r ⟨by omega, by omega⟩
        simp only [hA, hB'])
      (hc.congr' (Eventually.of_forall fun r => by rw [hmem1]))
  refine ⟨hlim.congr' (Eventually.of_forall fun r => ?_), ?_⟩
  · rw [hmem3, mixedMoment_padMom 3 (by norm_num) mom r]
  · rw [hmem3] at hRV
    exact hRV

/-- **The `p = 3` second induction at the actual source cutoff family**, from the
Case-3 decorrelation limits.

`hAend`/`hAmid` are the two components of the conclusion of
`I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3` at `p = 3`, which
supplies them from `(HD)(3)`, the finite triangle condition, the first-moment
ODE package and the root moment range.  The conclusion is
`E|K|³ ~ 3 (E|K|²/E|K|)² E|K|` plus regular variation of `E|K|³` of index `5α`
at the genuine cutoff law `M.cutProb`. -/
theorem case3_moment_three_asymptotic (M : Orchestration.SourceModelData)
    (hAend : Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 3
        (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 → Tendsto
      (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        (I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
            I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) (3 - ℓ) r))) atTop (𝓝 1))
    (hmom : ∀ m, 1 ≤ m → m ≤ 3 → ∀ r : ℝ, 0 < r →
      0 < I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) m r)
    (hmommeas1 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    (hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α))
    {cr : ℝ → ℝ}
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => I420Case3.momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hc : Tendsto (fun r => r * cr r *
      I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
        I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) atTop (𝓝 M.α)) :
    Tendsto (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r /
        mixedMoment 3 (fun m r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) m r) r)
        atTop (𝓝 1) ∧
      RegularlyVaryingAtTop
        (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r)
        ((2 * (3 : ℝ) - 1) * M.α) := by
  have hmass : ∀ r, 0 < r →
      (fun ℓ r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
        (BallAverage.ball_finite M r).toFinset) (3 - 1) r =
      (fun ℓ r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
        (BallAverage.ball_finite M r).toFinset) 0 r := by
    intro r _
    exact (I420Case3.mixedExclR_cutProb_swap M r 1 3 _).symm
  exact moment_three_asymptotic_of_decorrelation_of_pos (mom := fun m r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) m r) M.hα hmom hmommeas1
    hmommeas2 hRV1 hRV2 (fun x hx => I420Case3.ballCard_pos M hx) hmass hderivId
    hAend hAmid hc

end PercLib.CriticalLRP.VolumeMoments.HigherMoments

namespace PercLib.CriticalLRP.I420Case3

open Orchestration
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The `p = 3` second-induction asymptotic at the source model, from `(HD)(3)`.**

The Case-3 limits are supplied by
`I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3` at `p = 3`, so the
hypotheses are exactly those of `case3_moment_three_bound_of_HD_case3` except
that the first-moment normalization is taken in limit form.  The conclusion is
the full `p = 3` assertion of Proposition I.4.20:
`E|K|³ ~ 3 (E|K|²/E|K|)² E|K|` and regular variation of `E|K|³` of index `5α`.
-/
theorem case3_moment_three_asymptotic_of_HD_case3 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hmommeas1 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    (hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α))
    {cr : ℝ → ℝ}
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => I420Case3.momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcT : Tendsto (fun r => r * cr r *
      I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
        I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) atTop (𝓝 M.α)) :
    Tendsto (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r /
        mixedMoment 3 (fun m r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) m r) r)
        atTop (𝓝 1) ∧
      RegularlyVaryingAtTop
        (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r)
        ((2 * (3 : ℝ) - 1) * M.α) := by
  obtain ⟨hAend, hAmid⟩ :=
    case3_hAend_hAmid_cutPoly_source_of_HD_case3 M hHD3 hTri hc hαd hlow hfin
      hβ hr₀ hderiv hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 3 (by norm_num) hθ0 hθ1 hMa hc3 hgm
  exact case3_moment_three_asymptotic M hAend hAmid
    (momOf_cutProb_pos_three M hMa) hmommeas1 hmommeas2 hRV1 hRV2 hderivId hcT

end PercLib.CriticalLRP.I420Case3
