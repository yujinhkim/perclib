/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

Connection to the **ratio-based** moment bound direction: the ratio form of the induction step
(`VolumeMoments/HigherMoments/I420Case3/RatioInduction/RatioBound.derivative_bound_ratio`, which
replaces the pointwise decorrelation bounds `hA0`/`hAmid` by the normalized limits that the three
cases of Proposition I.4.20 produce) feeds the a.e.-derivative comparison exactly as the
pointwise decorrelation bounds do.  `moment_upper_bound_of_percolation_ratio_ae` below is
`moment_upper_bound_of_percolation_ratio` with the everywhere derivative identity of Lemma I.4.1
replaced by absolute continuity plus an a.e. derivative identity on a tail, and with every other
input unchanged; the defect of the differential comparison is derived, not assumed.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.MomentPercolation
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.RatioBound


/-! # Almost-everywhere higher-moment interface: MomentRatio -/

set_option autoImplicit false
set_option linter.style.multiGoal false

open MeasureTheory Filter Set Topology
open scoped Topology

@[expose] public section

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.Analysis.AE

/-- **Step (I.4.19) of Proposition I.4.20 from decorrelation ratio limits, with an a.e.
derivative identity.**

Same as `moment_upper_bound_of_percolation_ratio`, except that

* `hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom p r) (c x * ∑ ℓ, C(p,ℓ) A ℓ x) x` is replaced
  by absolute continuity of `mom p` on every compact window of a tail plus the same identity
  almost everywhere on that tail, and
* measurability of `mom p` and of the derivative expression is assumed (only to manufacture the
  defect of the a.e. differential comparison).

The decorrelation limits `hAend`, `hAmid`, the mass transport `hmass`, the induction hypothesis
`hIH` and the first-moment normalisation `hc` are unchanged. -/
theorem moment_upper_bound_of_percolation_ratio_ae {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hpm : Measurable (mom p))
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α)
    (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : AbsolutelyContinuousOnTail (fun r => mom p r) r₀)
    (hSm : Measurable (fun x => c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)))
    (hderivId : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt (fun r => mom p r)
        (c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hBp : ∀ x, 0 < x → 0 < Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hmass : ∀ x, 0 < x → A 0 x = A (p - 1) x)
    (hAend : Tendsto (fun x => A 0 x / (Bcard x * (mom 1 x * mom p x))) atTop (𝓝 1))
    (hAmidT : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun x => A ℓ x / (Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x))) atTop (𝓝 1))
    (hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ p - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x)
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom p r ≤ (1 + ε) * mixedMoment p mom r := by
  obtain ⟨D⟩ := drivingTerm_RVPosData hp hα hmom hmommeas1 hmommeas2 h1 h2
  let N : ℝ → ℝ := fun x => ((p : ℝ) + 1) * α * mom p x + drivingTerm p α mom x
  let S : ℝ → ℝ := fun x => c x * (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ x)
  let R : ℝ → ℝ := fun x => S x * x / N x
  have hSm' : Measurable S := hSm
  have hNm : Measurable N := (hpm.const_mul _).add D.measurable_f
  have hRm : Measurable R := (hSm'.mul measurable_id).div hNm
  have hNpos : ∀ x, 0 < x → 0 < N x := by
    intro x hx
    have h1x : 0 < mom p x := hmom p x hx
    have h2x : 0 < drivingTerm p α mom x := drivingTerm_pos hp hα (hmom 1 x hx) (hmom 2 x hx)
    dsimp only [N]
    positivity
  have hfbd := derivative_bound_ratio hp hα hmom hBp hc0 hmass hAend hAmidT hIH hc
  have hRle : ∀ ε > 0, ∀ᶠ x in atTop, R x ≤ 1 + ε := by
    intro ε hε
    filter_upwards [hfbd ε hε, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hN := hNpos x hx0
    have hx' : S x * x ≤ (1 + ε) * N x := by
      have h := (le_div_iff₀ hx0).mp hx
      dsimp only [S, N]
      linarith
    dsimp only [R]
    rw [div_le_iff₀ hN]
    linarith
  obtain ⟨δ, hδm, hδ0, hδnn, hδR, hδle⟩ := exists_defect_of_eventually_one_add hRm hRle
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hRle 1 one_pos)
  let r₁ : ℝ := max r₀ X
  have hr₁r₀ : r₀ ≤ r₁ := le_max_left _ _
  have hr₁X : X ≤ r₁ := le_max_right _ _
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le hr₀ hr₁r₀
  have hAC₁ : AbsolutelyContinuousOnTail (fun r => mom p r) r₁ := by
    intro R' hR'
    refine AbsolutelyContinuousOnInterval.mono (hac R' (le_trans hr₁r₀ hR')) ?_
    rw [uIcc_of_le hR', uIcc_of_le (le_trans hr₁r₀ hR')]
    exact Icc_subset_Icc hr₁r₀ le_rfl
  have hAE₁ : AeHasDerivAtOnTail (fun r => mom p r) S r₁ :=
    ae_mono (Measure.restrict_mono (fun _ hx => le_trans hr₁r₀ hx) le_rfl) hderivId
  have hδ1 : ∀ x, r₁ ≤ x → |δ x| ≤ 1 := by
    intro x hx
    have hRx : R x ≤ 1 + 1 := hX x (le_trans hr₁X hx)
    have hb : δ x ≤ max 0 (R x - 1) := hδle x
    have hb' : max 0 (R x - 1) ≤ 1 := max_le (by norm_num) (by linarith)
    rw [abs_of_nonneg (hδnn x)]
    exact le_trans hb hb'
  have hfbdδ : ∀ᵐ x ∂(volume.restrict (Set.Ici r₁)), S x ≤ (1 + δ x) * (N x / x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₁pos hx
    have hN := hNpos x hx0
    have hRx : R x ≤ 1 + δ x := hδR x
    have hSN : S x = R x * (N x / x) := by
      dsimp only [R]
      field_simp
    rw [hSN]
    exact mul_le_mul_of_nonneg_right hRx (by positivity)
  refine moment_upper_bound_ae hp hα hmom hmommeas1 hmommeas2 h1 h2 hr₁pos hAC₁ hAE₁
    hδm hδ0 hδ1 ?_
  filter_upwards [hfbdδ] with x hx
  simpa only [mul_div_assoc] using hx

end PercLib.CriticalLRP.VolumeMoments.HigherMoments


set_option linter.hashCommand false

#print axioms
  PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_of_percolation_ratio_ae
