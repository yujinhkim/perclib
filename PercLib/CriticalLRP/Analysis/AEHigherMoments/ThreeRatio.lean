/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

The **cubic packet** (`p = 3`) of step (I.4.19) with an a.e. derivative identity — the exact
interface consumed by
`I420Case3.case3_moment_three_bound_of_HD_case3` (`RatioInduction/Handoff.lean`) and hence by the
cubic Case-3 moment bound `case3_moment_three_bound_of_HD_case3`.

`moment_upper_bound_three_ratio_ae` is `moment_upper_bound_three_ratio` with the everywhere
derivative identity of Lemma I.4.1 replaced by absolute continuity of `mom 3` on compact windows
of a tail plus that identity almost everywhere; `moment_upper_bound_three_ratio_of_pos_ae` is the
same replacement in the padded form `moment_upper_bound_three_ratio_of_pos`, where positivity of
the moments is required only at orders `1, 2, 3` (the only orders the cubic step consumes).

All remaining premises are exactly those of the ratio form of the induction step.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.MomentRatio


/-! # Almost-everywhere higher-moment interface: ThreeRatio -/

set_option autoImplicit false
set_option linter.style.multiGoal false

open MeasureTheory Filter Set Topology
open scoped Topology

@[expose] public section

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.Analysis.AE

/-- **The cubic (`p = 3`) step (I.4.19) from decorrelation ratio limits, with an a.e. derivative
identity.** -/
theorem moment_upper_bound_three_ratio_ae {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ} (hmom : ∀ m x, 0 < x → 0 < mom m x)
    (hpm3 : Measurable (mom 3))
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α) (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : AbsolutelyContinuousOnTail (fun r => mom 3 r) r₀)
    (hSm : Measurable (fun x => c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)))
    (hderivId : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => mom 3 r)
      (c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hB : ∀ x, 0 < x → 0 < Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hmass : ∀ x, 0 < x → A 0 x = A (3 - 1) x)
    (hAend : Tendsto (fun x => A 0 x / (Bcard x * (mom 1 x * mom 3 x))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 →
      Tendsto (fun x => A ℓ x / (Bcard x * (mom (ℓ + 1) x * mom (3 - ℓ) x))) atTop (𝓝 1))
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom 3 r ≤ (1 + ε) * mixedMoment 3 mom r := by
  have hIH : ∀ ε > 0, ∀ᶠ x in atTop, ∀ m, 2 ≤ m → m ≤ 3 - 1 →
      mom m x ≤ (1 + ε) * dblFact (m - 1) * momentRatio mom x ^ ((m : ℝ) - 1) * mom 1 x := by
    intro ε hε
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact induction_hypothesis_three (hmom 1 x hx) (hmom 2 x hx).le hε.le
  exact moment_upper_bound_of_percolation_ratio_ae (p := 3) (by norm_num) hα hmom hpm3
    hmommeas1 hmommeas2 h1 h2 hr₀ hac hSm hderivId hB hc0 hmass hAend hAmid hIH hc

/-- **The cubic (`p = 3`) step (I.4.19) with an a.e. derivative identity and positivity only at
orders `1, 2, 3`.**

This is `moment_upper_bound_three_ratio_of_pos` with the everywhere derivative identity replaced
by absolute continuity plus an a.e. identity.  The other orders are padded by `padMom`, exactly
as in the production theorem, so no claim is made about the model at orders `≥ 4`. -/
theorem moment_upper_bound_three_ratio_of_pos_ae {α : ℝ} (hα : 0 < α)
    {mom : ℕ → ℝ → ℝ}
    (hmom : ∀ m, 1 ≤ m → m ≤ 3 → ∀ x, 0 < x → 0 < mom m x)
    (hpm3 : Measurable (mom 3))
    (hmommeas1 : Measurable (mom 1)) (hmommeas2 : Measurable (mom 2))
    (h1 : RegularlyVaryingAtTop (mom 1) α) (h2 : RegularlyVaryingAtTop (mom 2) (3 * α))
    {c Bcard : ℝ → ℝ} {A : ℕ → ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : AbsolutelyContinuousOnTail (fun r => mom 3 r) r₀)
    (hSm : Measurable (fun x => c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)))
    (hderivId : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => mom 3 r)
      (c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)) x)
    (hB : ∀ x, 0 < x → 0 < Bcard x) (hc0 : ∀ x, 0 < x → 0 ≤ c x)
    (hmass : ∀ x, 0 < x → A 0 x = A (3 - 1) x)
    (hAend : Tendsto (fun x => A 0 x / (Bcard x * (mom 1 x * mom 3 x))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 - 2 →
      Tendsto (fun x => A ℓ x / (Bcard x * (mom (ℓ + 1) x * mom (3 - ℓ) x))) atTop (𝓝 1))
    (hc : ∀ ε > 0, ∀ᶠ x in atTop, c x * Bcard x * mom 1 x * x ≤ (1 + ε) * α) :
    ∀ ε > 0, ∀ᶠ r in atTop, mom 3 r ≤ (1 + ε) * mixedMoment 3 mom r := by
  have hmem1 : padMom 3 mom 1 = mom 1 :=
    funext fun r => padMom_apply_of_mem mom r ⟨le_refl 1, by norm_num⟩
  have hmem2 : padMom 3 mom 2 = mom 2 :=
    funext fun r => padMom_apply_of_mem mom r ⟨by norm_num, by norm_num⟩
  have hmem3 : padMom 3 mom 3 = mom 3 :=
    funext fun r => padMom_apply_of_mem mom r ⟨by norm_num, by norm_num⟩
  have hpadpos : ∀ m x, 0 < x → 0 < padMom 3 mom m x := padMom_pos hmom
  have hpadmeas3 : Measurable (padMom 3 mom 3) := by rw [hmem3]; exact hpm3
  have hpadac : AbsolutelyContinuousOnTail (fun r => padMom 3 mom 3 r) r₀ := by
    rw [hmem3]
    exact hac
  have hpadId : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => padMom 3 mom 3 r)
      (c x * (∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) * A ℓ x)) x := by
    rw [hmem3]
    exact hderivId
  have hmain := moment_upper_bound_three_ratio_ae (mom := padMom 3 mom) hα hpadpos hpadmeas3
    (by rw [hmem1]; exact hmommeas1)
    (by rw [hmem2]; exact hmommeas2)
    (by rw [hmem1]; exact h1) (by rw [hmem2]; exact h2) hr₀ hpadac hSm hpadId hB hc0 hmass
    (by rw [hmem1, hmem3]; exact hAend)
    (fun ℓ h1ℓ h2ℓ => by
      refine (hAmid ℓ h1ℓ h2ℓ).congr' (Eventually.of_forall fun x => ?_)
      have hA : padMom 3 mom (ℓ + 1) x = mom (ℓ + 1) x :=
        padMom_apply_of_mem mom x ⟨by omega, by omega⟩
      have hB' : padMom 3 mom (3 - ℓ) x = mom (3 - ℓ) x :=
        padMom_apply_of_mem mom x ⟨by omega, by omega⟩
      simp only [hA, hB'])
    hc
  refine fun ε hε => (hmain ε hε).mono fun r hr => ?_
  rwa [hmem3, mixedMoment_padMom 3 (by norm_num) mom r] at hr

end PercLib.CriticalLRP.VolumeMoments.HigherMoments

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_three_ratio_ae
#print axioms
  PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_three_ratio_of_pos_ae
