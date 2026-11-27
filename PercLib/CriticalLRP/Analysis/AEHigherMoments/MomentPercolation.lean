/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

The `p`-th moment induction step (I.4.19) of Proposition I.4.20 at the percolation inputs, with
the everywhere derivative identity of Lemma I.4.1 replaced by its off-corner (a.e.) form.

`VolumeMoments/HigherMoments/Main.moment_upper_bound_of_percolation` consumes

`hderivId : ∀ x, 0 < x → HasDerivAt (fun r => mom p r) (c x * ∑ ℓ, C(p,ℓ) A ℓ x) x`

at **every** positive radius.  Off the (null) set of attained radii only the a.e. statement is
available (`Analysis/Cutoff/OffCorner/AeDerivativeHandoff`), so the theorem below replaces it by

* absolute continuity of `mom p` on compact radius windows of a tail `[r₀, ∞)`, and
* the derivative identity almost everywhere on that tail,

and *derives* the measurable defect `δ → 0` needed by `Analysis.AE.ae_lemma_I_4_22_of_defect_bound`
from the decorrelation bound of `derivative_bound` and measurability of the derivative expression.
Neither the conclusion nor any of the other probabilistic inputs (`hmass`, `hA0`, `hAmid`, `hIH`,
`hc`) is changed, and no derivative is invented at a corner radius.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.MomentBound


/-! # Almost-everywhere higher-moment interface: MomentPercolation -/

set_option autoImplicit false
set_option linter.style.multiGoal false

open MeasureTheory Filter Set Topology
open scoped Topology

@[expose] public section

namespace PercLib.CriticalLRP.Analysis.AE

/-- **A vanishing defect from an asymptotic one.**

If a measurable `R` satisfies `R ≤ 1 + ε` eventually for every `ε > 0`, then there is a measurable
defect `δ ≥ 0` with `δ → 0` and `R ≤ 1 + δ` everywhere.  (Take `δ = max 0 (R - 1)`.) -/
theorem exists_defect_of_eventually_one_add {R : ℝ → ℝ} (hRm : Measurable R)
    (h : ∀ ε > 0, ∀ᶠ x in atTop, R x ≤ 1 + ε) :
    ∃ δ : ℝ → ℝ, Measurable δ ∧ Tendsto δ atTop (𝓝 0) ∧ (∀ x, 0 ≤ δ x) ∧
      (∀ x, R x ≤ 1 + δ x) ∧ (∀ x, δ x ≤ max 0 (R x - 1)) := by
  refine ⟨fun x => max 0 (R x - 1), measurable_const.max (hRm.sub measurable_const),
    ?_, fun x => le_max_left _ _, fun x => ?_, fun x => le_rfl⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨X, hX⟩ := eventually_atTop.1 (h (ε / 2) (by linarith))
    refine ⟨X, fun x hx => ?_⟩
    have hRx := hX x hx
    have h0 : (0 : ℝ) ≤ max 0 (R x - 1) := le_max_left _ _
    have hle : max 0 (R x - 1) ≤ ε / 2 := max_le (by linarith) (by linarith)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    linarith
  · have := le_max_right (0 : ℝ) (R x - 1)
    linarith

end PercLib.CriticalLRP.Analysis.AE

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.Analysis.AE

/-- **Step (I.4.19) of Proposition I.4.20 with an a.e. derivative identity.**

The hypotheses are those of `moment_upper_bound_of_percolation` with `hderivId` replaced by
absolute continuity of `mom p` plus the same derivative identity a.e. on a tail; the additional
measurability `Measurable (mom p)` and `Measurable (fun x => c x * ∑ ℓ, C(p,ℓ) A ℓ x)` are needed
only to produce the defect of the a.e. differential comparison (the paper's `(1+o(1))` factor).
The conclusion is unchanged. -/
theorem moment_upper_bound_of_percolation_ae {p : ℕ} (hp : 3 ≤ p) {α : ℝ} (hα : 0 < α)
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
    (hB : ∀ x, 0 < x → 0 ≤ Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hmass : ∀ x, 0 < x → A 0 x = A (p - 1) x)
    (hA0 : ∀ x, 0 < x → A 0 x ≤ Bcard x * (mom 1 x * mom p x))
    (hAmid : ∀ x, 0 < x → ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      A ℓ x ≤ Bcard x * (mom (ℓ + 1) x * mom (p - ℓ) x))
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
  have hfbd := derivative_bound hp hα hmom hB hc0 hmass hA0 hAmid hIH hc
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

#print axioms PercLib.CriticalLRP.Analysis.AE.exists_defect_of_eventually_one_add
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_of_percolation_ae
