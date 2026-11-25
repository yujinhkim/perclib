/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/

/-
Proposition I.4.2 lower comparison, in the same source model as the polygon assembly.


Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.4.1, Lemma I.4.5(2), Corollary I.4.8 and display (I.4.6).

## Finding formalized here

The polygon assembly (`Analysis/Polygon/Assembly.lean`,
`exists_uniform_source_polygon_bound_of_triangle_first_moment`) consumes the *sharp*
first-moment asymptotic `χ(r) / ((α/β_c) r^α) → 1` (there called `hP`, i.e. full
Proposition I.4.2).  This file proves that Proposition I.4.2's **lower** comparison — the
content of Corollary I.4.8, and all that `hχ`/`hχfin` of
`Polygon.Consumer.source_polygon_bound_of_cutoff_data` actually needs — follows from the
cutoff ODE (I.4.6) under two strictly weaker defect hypotheses.  The ODE is written in the
same normal form as `VolumeMoments.FirstMoment.first_moment_asymptotic_at_critical`:

  `F' t = (1 - Ē t) * β_c * t ^ (-α - 1) * (F t) ^ 2`,  `Ē t = 1 - (1 - E₀ t)(1 - E₁ t)`.

* `lower_of_ode_of_sign`: the defect satisfies `Ē ≥ 0`, i.e. `(1 - E₀)(1 - E₁) ≤ 1`, only
  *pointwise*.  Then the pointwise lower comparison `(α/β_c) r^α ≤ χ r` holds on `[r₀,∞)`.
  No vanishing of the defect is used, so no tree-graph inequality, no a priori bound
  (Lemma I.4.9) and no ball-averaged open-triangle tail (I.4.11) is required.
* `eventually_lower_of_ode_of_tendsto_defect`: only `Ē → 0` is assumed.  This is the paper's
  Corollary I.4.8 shape; it gives an eventual constant `α/(2β_c)`, which
  `ChiInput.exists_chi_lower_uniform_of_eventually` upgrades to a uniform `c₀ r^α ≤ χ r` for
  every `r > 0`, hence `hχfin` everywhere.

`bounded_defect_insufficient` is the matching sharpness statement: boundedness of the defect
(`|E₀|, |E₁| ≤ C`) does **not** suffice — the exact solution of (I.4.6) with constant defect
`E₀ = 0`, `E₁ = -1` is `F r = r/2`, which has `F → ∞` yet violates `(α/A) r^α ≤ F r`.  So the
*sign* supplied by Lemma I.4.7 (`0 ≤ 𝓔_{1,r}`, i.e. FKG) is load-bearing and cannot be
replaced by an `O(1)` error bound.  The two remaining hypotheses of the lower-bound route —
the cutoff ODE and `χ r → ∞` — are exactly items 2 and 1/4 of
`docs/CRITICAL_LRP_I42_CASE3.md`; nothing else is assumed.
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Assembly
public import PercLib.CriticalLRP.VolumeMoments.ODELowerComparison
public import PercLib.CriticalLRP.Analysis.BallRatioLogError

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I418C.ChiLower

open PercLib.CriticalLRP Orchestration

/-! ## The abstract lower comparison (Lemma I.4.5(2) fed by the defect's sign) -/

/-- **Lemma I.4.5(2) with a sign hypothesis instead of a vanishing one.**

If `F > 0` on `[r₀,∞)`, `F → ∞`, and `F' = (1 - Ē) A t^{-α-1} F²` with
`Ē = 1 - (1-E₀)(1-E₁)` nonnegative on `[r₀,∞)` (equivalently `(1-E₀)(1-E₁) ≤ 1`), then
`(α/A) r^α ≤ F r` for every `r ≥ r₀`.  `Ē ≥ 0` is exactly the comparison
`F' ≤ A t^{-α-1} F²` that Lemma I.4.5(2) consumes; no smallness of `Ē` is needed. -/
theorem lower_of_ode_of_sign {F F' E0 E1 : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hode : ∀ t, r₀ ≤ t →
      F' t = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2)
    (hsign : ∀ t, r₀ ≤ t → (1 - E0 t) * (1 - E1 t) ≤ 1) :
    ∀ r, r₀ ≤ r → α / A * r ^ α ≤ F r := by
  refine PercLib.CriticalLRP.VolumeMoments.lemma_I_4_5_two_nocont hA hα hr₀
    hderiv hpos hinf ?_
  intro t ht
  rw [hode t ht]
  have htpos : 0 < t := lt_of_lt_of_le hr₀ ht
  have hp : (0 : ℝ) ≤ t ^ (-α - 1) := (Real.rpow_pos_of_pos htpos _).le
  have hs : (0 : ℝ) ≤ (F t) ^ 2 := sq_nonneg _
  have h1 : 1 - (1 - (1 - E0 t) * (1 - E1 t)) ≤ 1 := by
    have := hsign t ht
    linarith
  have step1 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A ≤ 1 * A :=
    mul_le_mul_of_nonneg_right h1 hA.le
  have step2 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1)
      ≤ 1 * A * t ^ (-α - 1) := mul_le_mul_of_nonneg_right step1 hp
  have step3 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2
      ≤ 1 * A * t ^ (-α - 1) * (F t) ^ 2 := mul_le_mul_of_nonneg_right step2 hs
  calc (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2
      ≤ 1 * A * t ^ (-α - 1) * (F t) ^ 2 := step3
    _ = A * t ^ (-α - 1) * (F t) ^ 2 := by ring

/-- **Corollary I.4.8 shape: the defect only has to vanish.**

`Ē → 0` alone is enough for an eventual constant `α/(2A)`.  The factor `2` is the price of
not knowing the pointwise sign, and it is harmless: `hχ` of Lemma I.4.18 needs only *some*
positive constant. -/
theorem eventually_lower_of_ode_of_tendsto_defect {F F' E0 E1 : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hode : ∀ t, r₀ ≤ t →
      F' t = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2)
    (htend : Tendsto (fun t => 1 - (1 - E0 t) * (1 - E1 t)) atTop (𝓝 0)) :
    ∀ᶠ r : ℝ in atTop, α / (A * 2) * r ^ α ≤ F r := by
  have hA2 : 0 < A * 2 := by positivity
  have hev : ∀ᶠ t : ℝ in atTop, -1 ≤ 1 - (1 - E0 t) * (1 - E1 t) :=
    htend.eventually (eventually_ge_nhds (show (-1 : ℝ) < 0 by norm_num))
  obtain ⟨R, hR⟩ := eventually_atTop.1 hev
  have hineq : ∀ t, max R r₀ ≤ t → F' t ≤ (A * 2) * t ^ (-α - 1) * (F t) ^ 2 := by
    intro t ht
    have hle : -1 ≤ 1 - (1 - E0 t) * (1 - E1 t) := hR t (le_trans (le_max_left _ _) ht)
    have htpos : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le hr₀ (le_max_right _ _)) ht
    have hp : (0 : ℝ) ≤ t ^ (-α - 1) := (Real.rpow_pos_of_pos htpos _).le
    have hs : (0 : ℝ) ≤ (F t) ^ 2 := sq_nonneg _
    rw [hode t (le_trans (le_max_right _ _) ht)]
    have h1 : 1 - (1 - (1 - E0 t) * (1 - E1 t)) ≤ 2 := by linarith
    have e1 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A ≤ 2 * A :=
      mul_le_mul_of_nonneg_right h1 hA.le
    have e2 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1)
        ≤ 2 * A * t ^ (-α - 1) := mul_le_mul_of_nonneg_right e1 hp
    have e3 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2
        ≤ 2 * A * t ^ (-α - 1) * (F t) ^ 2 := mul_le_mul_of_nonneg_right e2 hs
    calc (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2
        ≤ 2 * A * t ^ (-α - 1) * (F t) ^ 2 := e3
      _ = (A * 2) * t ^ (-α - 1) * (F t) ^ 2 := by ring
  have hmain : ∀ r, max R r₀ ≤ r → α / (A * 2) * r ^ α ≤ F r :=
    PercLib.CriticalLRP.VolumeMoments.lemma_I_4_5_two_nocont hA2 hα
      (lt_of_lt_of_le hr₀ (le_max_right _ _))
      (fun t ht => hderiv t (le_trans (le_max_right _ _) ht))
      (fun t ht => hpos t (le_trans (le_max_right _ _) ht)) hinf hineq
  exact eventually_atTop.2 ⟨max R r₀, hmain⟩

/-- **Corollary I.4.8 exactly as the paper states its hypotheses.**

The paper writes (p. 37): *"The fact that `𝓔_{1,r}` is non-negative and `𝓔_{0,r} → 0` ensures
that the following lower bound always holds, without any assumptions on `d` and `α`"*.  This
theorem is that statement: no vanishing of `𝓔_{1,r}` is used, only its sign, and `𝓔_{0,r} → 0`
without a rate or a sign.  The output is eventual, with the halved constant `α/(2A)` that the
paper's `lim inf` leaves free.

Consequence for this repository: the polygon assembly's `hχ` does *not* need the tree-graph
inequality, the a priori bound of Lemma I.4.9 or the ball-averaged open-triangle tail of
I.4.11 — only the cutoff ODE, `χ r → ∞`, `0 ≤ 𝓔_{1,r}` (Lemma I.4.7, already landed) and
`𝓔_{0,r} → 0` (already landed as `Analysis/BallRatioLogError.lean`). -/
theorem eventually_lower_of_ode_of_E1_nonneg_of_tendsto_E0 {F F' E0 E1 : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hode : ∀ t, r₀ ≤ t →
      F' t = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t)
    (hE0 : Tendsto E0 atTop (𝓝 0)) :
    ∀ᶠ r : ℝ in atTop, α / (A * 2) * r ^ α ≤ F r := by
  have hA2 : 0 < A * 2 := by positivity
  have hle1 : ∀ᶠ t : ℝ in atTop, E0 t ≤ 1 :=
    hE0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hge : ∀ᶠ t : ℝ in atTop, -1 ≤ E0 t :=
    hE0.eventually (eventually_ge_nhds (show (-1 : ℝ) < 0 by norm_num))
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 hle1
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.1 hge
  have hineq : ∀ t, max (max R₁ R₂) r₀ ≤ t → F' t ≤ (A * 2) * t ^ (-α - 1) * (F t) ^ 2 := by
    intro t ht
    have ht1 : R₁ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have ht2 : R₂ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
    have htr : r₀ ≤ t := le_trans (le_max_right _ _) ht
    have htpos : 0 < t := lt_of_lt_of_le hr₀ htr
    have hp : (0 : ℝ) ≤ t ^ (-α - 1) := (Real.rpow_pos_of_pos htpos _).le
    have hs : (0 : ℝ) ≤ (F t) ^ 2 := sq_nonneg _
    have ha0 : (0 : ℝ) ≤ 1 - E0 t := by have := hR₁ t ht1; linarith
    have hkey : (1 - E0 t) * (1 - E1 t) ≤ 2 := by
      have hstep : (1 - E0 t) * (1 - E1 t) ≤ (1 - E0 t) * 1 :=
        mul_le_mul_of_nonneg_left (by have := hE1 t htr; linarith) ha0
      have h2 : (1 - E0 t) * 1 = 1 - E0 t := by ring
      have h3 : 1 - E0 t ≤ 2 := by have := hR₂ t ht2; linarith
      linarith
    rw [hode t htr]
    have h1 : 1 - (1 - (1 - E0 t) * (1 - E1 t)) ≤ 2 := by linarith
    have e1 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A ≤ 2 * A :=
      mul_le_mul_of_nonneg_right h1 hA.le
    have e2 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1)
        ≤ 2 * A * t ^ (-α - 1) := mul_le_mul_of_nonneg_right e1 hp
    have e3 : (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2
        ≤ 2 * A * t ^ (-α - 1) * (F t) ^ 2 := mul_le_mul_of_nonneg_right e2 hs
    calc (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2
        ≤ 2 * A * t ^ (-α - 1) * (F t) ^ 2 := e3
      _ = (A * 2) * t ^ (-α - 1) * (F t) ^ 2 := by ring
  have hmain : ∀ r, max (max R₁ R₂) r₀ ≤ r → α / (A * 2) * r ^ α ≤ F r :=
    PercLib.CriticalLRP.VolumeMoments.lemma_I_4_5_two_nocont hA2 hα
      (lt_of_lt_of_le hr₀ (le_max_right _ _))
      (fun t ht => hderiv t (le_trans (le_max_right _ _) ht))
      (fun t ht => hpos t (le_trans (le_max_right _ _) ht)) hinf hineq
  exact eventually_atTop.2 ⟨max (max R₁ R₂) r₀, hmain⟩

/-- The source's two signs `0 ≤ 𝓔_{0,r}, 𝓔_{1,r} ≤ 1` (Lemma I.4.7 gives `0 ≤ 𝓔_{1,r}`;
`𝓔_{0,r} → 0` gives `𝓔_{0,r} ≤ 1` eventually) imply the sign form used above. -/
theorem sign_of_errors_mem_Icc {E0 E1 : ℝ → ℝ}
    (h0 : ∀ t, 0 ≤ E0 t) (h0' : ∀ t, E0 t ≤ 1)
    (h1 : ∀ t, 0 ≤ E1 t) (h1' : ∀ t, E1 t ≤ 1) :
    ∀ t, (1 - E0 t) * (1 - E1 t) ≤ 1 := by
  intro t
  have a0 : (0 : ℝ) ≤ 1 - E0 t := by linarith [h0' t]
  have a1 : 1 - E0 t ≤ 1 := by linarith [h0 t]
  have b0 : (0 : ℝ) ≤ 1 - E1 t := by linarith [h1' t]
  have b1 : 1 - E1 t ≤ 1 := by linarith [h1 t]
  nlinarith [mul_le_mul a1 b1 b0 (by norm_num : (0 : ℝ) ≤ 1)]

/-! ## Sharpness: boundedness of the defect is not enough -/

/-- **The sign hypothesis is indispensable.**  There are `F > 0`, `F → ∞`, and a *bounded*
defect `E₀, E₁` with `F' = (1 - Ē) A t^{-α-1} F²`, for which the conclusion
`(α/A) r^α ≤ F r` fails.  The witness is the exact solution `F r = r/2` with `A = α = 1` and
constant defect `E₀ = 0`, `E₁ = -1`, i.e. `Ē = -1 < 0`.

Consequently no `|E₀|, |E₁| ≤ C` hypothesis can replace `Ē ≥ 0`: the covariance sign of
Lemma I.4.7 (`0 ≤ 𝓔_{1,r}`) is genuinely consumed by Corollary I.4.8. -/
theorem bounded_defect_insufficient :
    ∃ (F F' E0 E1 : ℝ → ℝ) (A α r₀ C : ℝ),
      0 < A ∧ 0 < α ∧ 0 < r₀ ∧ 0 ≤ C ∧
      (∀ t, r₀ ≤ t → HasDerivAt F (F' t) t) ∧
      (∀ t, r₀ ≤ t → 0 < F t) ∧
      Tendsto F atTop atTop ∧
      (∀ t, r₀ ≤ t → F' t
        = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * A * t ^ (-α - 1) * (F t) ^ 2) ∧
      (∀ t, r₀ ≤ t → |E0 t| ≤ C ∧ |E1 t| ≤ C) ∧
      ¬ (∀ r, r₀ ≤ r → α / A * r ^ α ≤ F r) := by
  refine ⟨fun t => t / 2, fun _ => 1 / 2, fun _ => 0, fun _ => -1, 1, 1, 1, 1,
    one_pos, one_pos, one_pos, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    simpa using (hasDerivAt_id (x := t)).div_const 2
  · intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    positivity
  · exact tendsto_id.atTop_div_const (by norm_num)
  · intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have htne : t ≠ 0 := ne_of_gt htpos
    have hpow : t ^ (-(1 : ℝ) - 1) = (t ^ 2)⁻¹ := by
      rw [show (-(1 : ℝ) - 1) = -(2 : ℝ) by norm_num,
        Real.rpow_neg htpos.le, Real.rpow_two]
    rw [hpow]
    field_simp
    ring
  · intro t _
    constructor <;> norm_num
  · intro hcontra
    have h2 := hcontra 2 (by norm_num)
    norm_num at h2

/-! ## Model-level statements for `SourceModelData` -/

variable (M : SourceModelData)

/-- **The normalization error `𝓔_{0,r}` of (I.4.6) at the source model, with `𝓔_{0,r} → 0`.**

The paper's `𝓔_{0,r}` is defined by `1 - 𝓔_{0,r} = |J'(r)| |B_r| r^{α+1}` (p. 35).  With
`|J'(r)| = |K'(r)|`, `|B_r| = (M.ball r).ncard` and the model's own regular-variation error
`δ` from `SourceModelData.exists_error`, this file constructs an `E0` satisfying that identity
for every `r > 0` and proves `E0 r → 0`.

The limit is not a new input: it is the second component of
`Analysis/BallRatioLogError.SourceModelData.isLogErrorFunction_one_sub_mul_ball_ratio`, which
is Lemma I.4.6 (`|B_r| = r^d + O(r^{d-1})`) multiplied into the kernel error `δ`. -/
theorem exists_normalizationError (M : SourceModelData) :
    ∃ E0 : ℝ → ℝ, Tendsto E0 atTop (𝓝 0) ∧
      ∀ r : ℝ, 0 < r → E0 r
        = 1 - |deriv M.K r| * ((M.ball r).ncard : ℝ) * r ^ (M.α + 1) := by
  obtain ⟨δ, hδeq, hδ⟩ := M.exists_error
  refine ⟨fun r => 1 - (1 + δ r) * (((M.ball r).ncard : ℝ) / r ^ M.d), ?_, ?_⟩
  · exact (SourceModelData.isLogErrorFunction_one_sub_mul_ball_ratio M hδ).2
  · intro r hr
    have hcomb : r ^ (-(M.d : ℝ) - M.α - 1) * r ^ (M.α + 1) = (r ^ M.d)⁻¹ := by
      rw [← Real.rpow_add hr]
      have hexp : -(M.d : ℝ) - M.α - 1 + (M.α + 1) = -(M.d : ℝ) := by ring
      rw [hexp, Real.rpow_neg hr.le, Real.rpow_natCast]
    have h1 : |deriv M.K r| = (1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1) := hδeq r hr
    have hid : |deriv M.K r| * ((M.ball r).ncard : ℝ) * r ^ (M.α + 1)
        = (1 + δ r) * (((M.ball r).ncard : ℝ) / r ^ M.d) := by
      calc |deriv M.K r| * ((M.ball r).ncard : ℝ) * r ^ (M.α + 1)
          = (1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1)
              * ((M.ball r).ncard : ℝ) * r ^ (M.α + 1) := by rw [h1]
        _ = (1 + δ r) * ((M.ball r).ncard : ℝ)
              * (r ^ (-(M.d : ℝ) - M.α - 1) * r ^ (M.α + 1)) := by ring
        _ = (1 + δ r) * ((M.ball r).ncard : ℝ) * (r ^ M.d)⁻¹ := by rw [hcomb]
        _ = (1 + δ r) * (((M.ball r).ncard : ℝ) / r ^ M.d) := by
            rw [div_eq_mul_inv]; ring
    rw [hid]

/-- **Proposition I.4.2's lower comparison at the source model, from the defect's sign.**

`F = (M.cutMassAt · 0).toReal` is the source's `E_{β_c,r}|K|` and the ODE is (I.4.6) in the
normal form of `first_moment_asymptotic_at_critical`.  The only non-ODE inputs are positivity,
`χ r → ∞` and the pointwise sign `Ē ≥ 0` on `[r₀,∞)`.  No sharp asymptotic, no vanishing
error and no tree-graph inequality is used. -/
theorem cutMassAt_rpow_le_of_ode_of_sign {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (hsign : ∀ t, r₀ ≤ t → (1 - E0 t) * (1 - E1 t) ≤ 1) :
    ∀ r, r₀ ≤ r → M.α / (M.betaCrit : ℝ) * r ^ M.α ≤ (M.cutMassAt r 0).toReal :=
  lower_of_ode_of_sign hβ M.hα hr₀ hderiv hpos hinf hode hsign

/-- **Corollary I.4.8 at the source model: `𝓔_{1,r} ≥ 0` and `𝓔_{0,r} → 0` suffice.**

This is the paper's own hypothesis set for the lower bound.  Note that `𝓔_{0,r} → 0` can be
discharged by `exists_normalizationError`, so the only genuinely remaining inputs are the
cutoff ODE (I.4.6) and `χ r → ∞`. -/
theorem eventually_cutMassAt_rpow_le_of_E1_nonneg_of_tendsto_E0 {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t)
    (hE0 : Tendsto E0 atTop (𝓝 0)) :
    ∀ᶠ r : ℝ in atTop,
      M.α / ((M.betaCrit : ℝ) * 2) * r ^ M.α ≤ (M.cutMassAt r 0).toReal :=
  eventually_lower_of_ode_of_E1_nonneg_of_tendsto_E0 hβ M.hα hr₀ hderiv hpos hinf hode hE1 hE0

/-- **`hχ` and `hχfin` of Lemma I.4.18 from Corollary I.4.8's hypotheses.** -/
theorem exists_chi_lower_uniform_and_finite_of_E1_nonneg_of_tendsto_E0
    {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t)
    (hE0 : Tendsto E0 atTop (𝓝 0)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r →
      c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal ∧ M.cutMassAt r 0 ≠ ⊤ := by
  have hc : 0 < M.α / ((M.betaCrit : ℝ) * 2) :=
    div_pos M.hα (by positivity)
  obtain ⟨c₀, hc₀, hχu⟩ :=
    ChiInput.exists_chi_lower_uniform_of_eventually M hc
      (eventually_cutMassAt_rpow_le_of_E1_nonneg_of_tendsto_E0 M hβ hr₀ hderiv hpos hinf
        hode hE1 hE0)
  exact ⟨c₀, hc₀, fun r hr =>
    ⟨hχu r hr, ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ hr (hχu r hr)⟩⟩

/-- **`χ r ⪰ r^α` at the source model from a vanishing defect (Corollary I.4.8).**

The conclusion is only eventual and only with a halved constant, which is the lacunarity the
paper's `lim inf` statement leaves; it is still enough for the uniform `c₀ r^α ≤ χ r` that
Lemma I.4.18 uses. -/
theorem eventually_cutMassAt_rpow_le_of_tendsto_defect {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (htend : Tendsto (fun t => 1 - (1 - E0 t) * (1 - E1 t)) atTop (𝓝 0)) :
    ∀ᶠ r : ℝ in atTop,
      M.α / ((M.betaCrit : ℝ) * 2) * r ^ M.α ≤ (M.cutMassAt r 0).toReal :=
  eventually_lower_of_ode_of_tendsto_defect hβ M.hα hr₀ hderiv hpos hinf hode htend

/-- **Both consumer inputs of Lemma I.4.18 derived from a vanishing defect.**

`hχ` (`c₀ r^α ≤ χ r` at every `r > 0`) and `hχfin` (`χ r ≠ ⊤`) of
`Polygon.Consumer.source_polygon_bound_of_cutoff_data`, obtained without Proposition I.4.2's
sharp `∼`. -/
theorem exists_chi_lower_uniform_and_finite_of_tendsto_defect {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (htend : Tendsto (fun t => 1 - (1 - E0 t) * (1 - E1 t)) atTop (𝓝 0)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r →
      c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal ∧ M.cutMassAt r 0 ≠ ⊤ := by
  have hc : 0 < M.α / ((M.betaCrit : ℝ) * 2) :=
    div_pos M.hα (by positivity)
  obtain ⟨c₀, hc₀, hχu⟩ :=
    ChiInput.exists_chi_lower_uniform_of_eventually M hc
      (eventually_cutMassAt_rpow_le_of_tendsto_defect M hβ hr₀ hderiv hpos hinf hode htend)
  exact ⟨c₀, hc₀, fun r hr =>
    ⟨hχu r hr, ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ hr (hχu r hr)⟩⟩

/-- **Lemma I.4.18 for `ℓ ≥ 4` with the sharp asymptotic replaced by a vanishing defect.**

Compare `ChiInput.exists_c0_source_polygon_bound`, whose hypothesis is
`χ(r) / ((α/β_c) r^α) → 1`.  Here that sharp ratio is replaced by the ODE (I.4.6), the
divergence `χ r → ∞`, positivity on a tail, and `Ē → 0`. -/
theorem exists_c0_source_polygon_bound_of_ode
    {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (htend : Tendsto (fun t => 1 - (1 - E0 t) * (1 - E1 t)) atTop (𝓝 0))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (r R trc : ℝ) (s : Finset M.V) (K cc : ℝ) (ell : ℕ),
        1 ≤ r → 0 ≤ K → 4 ≤ ell → cc = M.α / (4 * (M.d : ℝ)) →
        (∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y) →
        (∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc) →
        0 ≤ trc → (s.card : ℝ) ≤ K * R ^ (M.d : ℝ) →
        R = r ^ (M.α / (2 * (M.d : ℝ))) →
        ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
          ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) *
            ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  obtain ⟨c₀, hc₀, hχu⟩ :=
    exists_chi_lower_uniform_and_finite_of_tendsto_defect M hβ hr₀ hderiv hpos hinf hode htend
  refine ⟨c₀, hc₀, ?_⟩
  intro r R trc s K cc ell hr hK hell hct hfar htailc htrc hcard hR
  exact ChiInput.source_polygon_bound_of_uniform_chi M r R trc s hr hc₀ hK
    (fun r' hr' => (hχu r' hr').1) hTri hB2 hB3 hlink hell hct hfar htailc htrc hcard hR

/-- **Lemma I.4.18 for `ℓ ≥ 4` from Corollary I.4.8's hypotheses.**

The sharp asymptotic `hP` of `ChiInput.exists_c0_source_polygon_bound` is replaced by the
cutoff ODE (I.4.6), `χ r → ∞`, `𝓔_{1,r} ≥ 0` and `𝓔_{0,r} → 0`. -/
theorem exists_c0_source_polygon_bound_of_E1_nonneg
    {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t)
    (hE0 : Tendsto E0 atTop (𝓝 0))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (r R trc : ℝ) (s : Finset M.V) (K cc : ℝ) (ell : ℕ),
        1 ≤ r → 0 ≤ K → 4 ≤ ell → cc = M.α / (4 * (M.d : ℝ)) →
        (∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y) →
        (∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc) →
        0 ≤ trc → (s.card : ℝ) ≤ K * R ^ (M.d : ℝ) →
        R = r ^ (M.α / (2 * (M.d : ℝ))) →
        ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
          ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) *
            ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  obtain ⟨c₀, hc₀, hχu⟩ :=
    exists_chi_lower_uniform_and_finite_of_E1_nonneg_of_tendsto_E0 M hβ hr₀ hderiv hpos hinf
      hode hE1 hE0
  refine ⟨c₀, hc₀, ?_⟩
  intro r R trc s K cc ell hr hK hell hct hfar htailc htrc hcard hR
  exact ChiInput.source_polygon_bound_of_uniform_chi M r R trc s hr hc₀ hK
    (fun r' hr' => (hχu r' hr').1) hTri hB2 hB3 hlink hell hct hfar htailc htrc hcard hR

/-- **The module's headline `ℓ ≥ 4` polygon bound with `hP` replaced.**

Identical conclusion to `Assembly.exists_uniform_source_polygon_bound_of_triangle_first_moment`
— the full source form `C * ((M.nablaTail (r^c)).toReal + r^{-c}) * χ^{ℓ-3}` together with the
diagonal identity `⨆_x polyK … ℓ 0 x = polyK … ℓ 0 0` — but the sharp first-moment asymptotic
`hP` is replaced by the cutoff ODE (I.4.6), `χ r → ∞`, `0 ≤ 𝓔₁` and `𝓔₀ → 0`.  The body is the
landed assembly replayed at the weaker input; `c = α/(2d)` and the tail evaluation
`M.nablaTail (r^c)` are untouched. -/
theorem exists_uniform_source_polygon_bound_of_ode
    (M : SourceModelData) {r₀ : ℝ} {F' E0 E1 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * (M.betaCrit : ℝ) * t ^ (-M.α - 1)
        * ((M.cutMassAt t 0).toReal) ^ 2)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t)
    (hE0 : Tendsto E0 atTop (𝓝 0))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {ell : ℕ}, 4 ≤ ell → ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      (⨆ x : M.V, polyK (M.cutTwoPoint r) ell 0 x) = polyK (M.cutTwoPoint r) ell 0 0 ∧
      polyK (M.cutTwoPoint r) ell 0 x
        ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) *
          ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  obtain ⟨c₀, hc₀, hχu⟩ :=
    exists_chi_lower_uniform_and_finite_of_E1_nonneg_of_tendsto_E0 M hβ hr₀ hderiv hpos hinf
      hode hE1 hE0
  obtain ⟨Knear, hKnear, hnear⟩ := NearBall.exists_near_ball M
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
  refine ⟨M.α / (2 * (M.d : ℝ)), max 1 (M.triSelf * Knear / c₀),
    div_pos M.hα (mul_pos (by norm_num) hdpos),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ell hell r hr x
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have hχfin : M.cutMassAt r 0 ≠ ⊤ := (hχu r hrpos).2
  have hdiag : ∀ y : M.V, polyK (M.cutTwoPoint r) ell 0 y
      ≤ polyK (M.cutTwoPoint r) ell 0 0 :=
    fun y => M.source_polyK_le_diag r hχfin ell y
  constructor
  · have hbdd : BddAbove (Set.range (fun y : M.V => polyK (M.cutTwoPoint r) ell 0 y)) := by
      refine ⟨polyK (M.cutTwoPoint r) ell 0 0, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hdiag y
    exact le_antisymm (ciSup_le hdiag) (le_ciSup hbdd (0 : M.V))
  · obtain ⟨hB2, hB3, hlink⟩ := M.hB2_hB3_hlink_derived hTri
    have hexp : 0 ≤ M.α / (2 * (M.d : ℝ)) := div_nonneg M.hα.le (by positivity)
    have hnearR : 1 ≤ r ^ (M.α / (2 * (M.d : ℝ))) := Real.one_le_rpow hr hexp
    obtain ⟨s, hfar, hcard⟩ := hnear _ hnearR
    exact source_polygon_bound_tail_cc (c₀ := c₀) (K := Knear)
      (cc := M.α / (2 * (M.d : ℝ))) (ell := ell) M r
      (r ^ (M.α / (2 * (M.d : ℝ)))) s hr hc₀ hKnear.le
      hχfin hTri hB2 hB3 hlink hell
      le_rfl hfar hcard rfl ((hχu r hrpos).1) x

end PercLib.CriticalLRP.I418C.ChiLower
