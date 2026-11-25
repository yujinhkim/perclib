/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Proposition I.4.2, Case 3 (the triangle condition) and its proof.

## What this file does

The paper's proof of Case 3 applies Lemma I.4.5(3) at `f = E_{β_c,r}|K|` and gets (I.4.7).
Lemma I.4.5(3) is used with `f(r) → ∞`, and the paper supplies this by the flat assertion

  "Since `E_{β_c}|K| = ∞`, it follows from Lemma I.4.5 and (I.4.6) that the identity (I.4.7) holds"

(`paper.txt`, proof of Proposition I.4.2, p. 41).  The argument needs the lower critical two-point bound supplied by Theorem I.2.14 (p. 27),
which is not yet formalized in this repository. It is not a consequence of the triangle
condition alone: it is a lower bound on the critical two-point function. For
`α < 1` Theorem I.2.14 gives `P_{β_c}(x ↔ y) ≍ ‖x − y‖^{-d+α}` for every `x ≠ y`, whose lower
half is the hypothesis `hlow` below.

This file proves the divergence itself rigorously at the configured model:

* `I42C.uncutFirstMoment_eq_top_of_rpow_lower`:
  `c ‖x‖^{-d+α} ≤ P_{β_c}(0↔x)` for all `x ≠ 0`, together with `0 < α < d`, forces
  `E_{β_c}|K_0| = ∫⁻ |K_0| ∂P_{β_c} = ⊤`, i.e. the paper's `E_{β_c}|K| = ∞`.
  The mechanism is the honest lattice divergence: inside `B_r` every `‖x‖^{-d+α}` is at least
  `r^{-d+α}`, and `|B_r| ⪰ r^d` gives `∑_{x ∈ B_r, x ≠ 0} ‖x‖^{-d+α} ⪰ r^α → ∞`.
* `I42C.tendsto_cutMassAt_atTop_nhds_top`: consequently the cutoff masses
  `r ↦ M.cutMassAt r 0` diverge to `⊤`.  This is the `f → ∞` hypothesis (`hinf`) of the landed
  `VolumeMoments.FirstMoment.first_moment_asymptotic`, i.e. of formula (I.4.7).
* `I42C.tendsto_cutMassAt_toReal_atTop`: the real-valued form, conditional on the
  eventual finiteness of the cutoff mass.  That finiteness is *not* proved here; it is a
  separate source obligation (strict subcritical domination of the range-truncated law,
  `docs/CRITICAL_LRP_CUTOFF_DOMINATED.md`), and the `⊤ → atTop` transfer genuinely needs it
  because `(⊤ : ℝ≥0∞).toReal = 0`.

No `sorry`, no custom axioms.  Only `propext`, `Classical.choice`, `Quot.sound`.
-/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.RowSum
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Analysis.BallAverage
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Asymptotic

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP.I42C

open PercLib.CriticalLRP Orchestration

noncomputable section

variable (M : SourceModelData)

/-! ### The uncut first moment as a site series -/

/-- `E_{β_c}|K_0| = ∑_y P_{β_c}(0↔y)`, the identity behind the site sums below. -/
theorem lintegral_uncut_clusterVol_eq_tsum (M : SourceModelData) :
    ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)
      = ∑' y : M.V, M.twoPointE M.betaCrit 0 y := by
  have h := lintegral_clusterVol_eq_tsum_twoPoint (d := M.d) (J := M.kernel)
    M.kernel_nonneg M.betaCrit (0 : Fin M.d → ℤ)
  simpa [Orchestration.SourceModelData.law, Orchestration.SourceModelData.twoPointE,
    twoPointFunction] using h

/-! ### Divergence from the critical two-point lower bound -/

/-- The source's Theorem I.2.14 lower half (`α < 1` there, but the argument only needs the
lower bound and `0 < α < d`) forces the critical uncut first moment to be infinite. -/
theorem uncutFirstMoment_eq_top_of_rpow_lower
    {c : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)) = ⊤ := by
  classical
  obtain ⟨C, hC⟩ := BallAverage.exists_cube_bound M
  have hC0 : 0 ≤ C := BallAverage.cube_bound_nonneg M hC
  have hexp : (-(M.d : ℝ) + M.α) ≤ 0 := by
    have : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
    linarith
  rw [lintegral_uncut_clusterVol_eq_tsum M]
  -- the key estimate at a single radius
  have key : ∀ r : ℝ, max (2 * C) 4 ≤ r →
      ENNReal.ofReal (c / 2 ^ (M.d + 1) * r ^ M.α)
        ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := by
    intro r hr
    have hr4 : 4 ≤ r := le_trans (le_max_right _ _) hr
    have hr2C : 2 * C ≤ r := le_trans (le_max_left _ _) hr
    have hr0 : 0 < r := by linarith
    have hhalfpos : (0 : ℝ) < r / 2 := by linarith
    have hBfin : (M.ball r).Finite := BallAverage.ball_finite M r
    set s : Finset M.V := hBfin.toFinset.erase 0 with hs
    -- cardinality of `s`
    have h0mem : (0 : M.V) ∈ hBfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      change M.S.ρ (toVec (0 : M.V)) ≤ r
      have hz : toVec (0 : M.V) = 0 := by funext i; simp [Orchestration.toVec]
      rw [hz, M.S.ρ_zero]
      exact hr0.le
    have hcardeq : (s.card : ℝ) = ((M.ball r).ncard : ℝ) - 1 := by
      have h1 : s.card = hBfin.toFinset.card - 1 := Finset.card_erase_of_mem h0mem
      have h2 : (hBfin.toFinset.card : ℝ) = ((M.ball r).ncard : ℝ) := by
        rw [← Set.ncard_eq_toFinset_card (M.ball r) hBfin]
      have h3 : (1 : ℕ) ≤ hBfin.toFinset.card := Finset.card_pos.mpr ⟨0, h0mem⟩
      rw [h1, Nat.cast_sub h3, h2]
      norm_num
    have hcard : (r / 2) ^ M.d / 2 ≤ (s.card : ℝ) := by
      have hge := BallAverage.ball_ncard_ge M hC hC0 (r := r) (by linarith : C < r)
      have hCnon : (0 : ℝ) ≤ C := hC0
      have h1 : r / 2 ≤ r - C := by linarith
      have h2 : (r / 2) ^ M.d ≤ (r - C) ^ M.d := by
        exact pow_le_pow_left₀ (by linarith) h1 M.d
      have h3 : (2 : ℝ) ≤ (r / 2) ^ M.d := by
        have h2le : (2 : ℝ) ≤ r / 2 := by linarith
        calc (2 : ℝ) ≤ r / 2 := h2le
          _ = (r / 2) ^ 1 := (pow_one _).symm
          _ ≤ (r / 2) ^ M.d := pow_le_pow_right₀ (by linarith) M.hd
      rw [hcardeq]
      linarith
    -- termwise comparison
    have hterm : ∀ x ∈ s, ENNReal.ofReal (c * r ^ (-(M.d : ℝ) + M.α))
        ≤ ENNReal.ofReal (M.twoPoint M.betaCrit 0 x) := by
      intro x hx
      have hxmem : x ∈ M.ball r := by
        rw [← Set.Finite.mem_toFinset hBfin]
        exact Finset.mem_of_mem_erase hx
      have hxne : x ≠ 0 := Finset.ne_of_mem_erase hx
      have hdist : M.S.dist 0 x = M.S.ρ (toVec x) := by
        rw [Orchestration.SourceNormData.dist]
        have hsub : toVec ((0 : M.V) - x) = -(toVec x) := by
          rw [Orchestration.toVec_sub]
          have : toVec (0 : M.V) = 0 := by funext i; simp [Orchestration.toVec]
          rw [this, zero_sub]
        rw [hsub, M.S.ρ_neg]
      have hle : M.S.dist 0 x ≤ r := by
        rw [hdist]
        exact hxmem
      have hpos : 0 < M.S.dist 0 x :=
        Orchestration.SourceNormData.dist_pos M.S (x := (0 : M.V)) (y := x) (Ne.symm hxne)
      have hrpow : r ^ (-(M.d : ℝ) + M.α) ≤ (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) :=
        Real.rpow_le_rpow_of_nonpos hpos hle hexp
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hlow x hxne))
      exact mul_le_mul_of_nonneg_left hrpow hc.le
    have hsum1 : ∑ x ∈ s, ENNReal.ofReal (c * r ^ (-(M.d : ℝ) + M.α))
        ≤ ∑ x ∈ s, ENNReal.ofReal (M.twoPoint M.betaCrit 0 x) :=
      Finset.sum_le_sum hterm
    have hsum2 : ∑ x ∈ s, ENNReal.ofReal (c * r ^ (-(M.d : ℝ) + M.α))
        = ENNReal.ofReal (c * r ^ (-(M.d : ℝ) + M.α)) * (s.card : ℝ≥0∞) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hsum3 : ∑ x ∈ s, ENNReal.ofReal (M.twoPoint M.betaCrit 0 x)
        ≤ ∑' y : M.V, ENNReal.ofReal (M.twoPoint M.betaCrit 0 y) :=
      ENNReal.sum_le_tsum s
    have hsum4 : ∑' y : M.V, ENNReal.ofReal (M.twoPoint M.betaCrit 0 y)
        ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := by
      refine ENNReal.tsum_le_tsum fun y => ?_
      have : M.twoPointE M.betaCrit 0 y
          = (M.law M.betaCrit) {ω : Config M.V | Connects ω 0 y} := rfl
      rw [this,
        show M.twoPoint M.betaCrit 0 y
          = ((M.law M.betaCrit) {ω : Config M.V | Connects ω 0 y}).toReal from rfl]
      exact ENNReal.ofReal_toReal_le
    -- the arithmetic identity
    have harith : c / 2 ^ (M.d + 1) * r ^ M.α
        = c * r ^ (-(M.d : ℝ) + M.α) * (r / 2) ^ M.d / 2 := by
      have h1 : (r / 2) ^ M.d = r ^ M.d / 2 ^ M.d := div_pow r 2 M.d
      have h2 : r ^ (-(M.d : ℝ) + M.α) * r ^ M.d = r ^ M.α := by
        rw [← Real.rpow_natCast (x := r) (n := M.d), ← Real.rpow_add hr0]
        congr 1
        ring
      have h3 : (2 : ℝ) ^ (M.d + 1) = 2 ^ M.d * 2 := by
        rw [pow_succ]
      have hpos2 : (0 : ℝ) < 2 ^ M.d := by positivity
      rw [h1, h3]
      field_simp
      nlinarith [h2]
    calc ENNReal.ofReal (c / 2 ^ (M.d + 1) * r ^ M.α)
        = ENNReal.ofReal (c * r ^ (-(M.d : ℝ) + M.α) * (r / 2) ^ M.d / 2) := by
          rw [harith]
      _ ≤ ENNReal.ofReal (c * r ^ (-(M.d : ℝ) + M.α) * (s.card : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hcpos : 0 < c * r ^ (-(M.d : ℝ) + M.α) :=
            mul_pos hc (Real.rpow_pos_of_pos hr0 _)
          nlinarith [hcard]
      _ = ENNReal.ofReal (c * r ^ (-(M.d : ℝ) + M.α)) * (s.card : ℝ≥0∞) := by
          rw [ENNReal.ofReal_mul (le_of_lt (mul_pos hc (Real.rpow_pos_of_pos hr0 _)))]
          norm_num [ENNReal.ofReal_natCast]
      _ ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := by
          rw [← hsum2]
          exact le_trans hsum1 (le_trans hsum3 hsum4)
  -- conclude
  have hn : ∀ n : ℕ, (n : ℝ≥0∞) ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := by
    intro n
    have hc'0 : 0 < c / 2 ^ (M.d + 1) := by positivity
    have htend : Tendsto (fun r : ℝ => c / 2 ^ (M.d + 1) * r ^ M.α) atTop atTop :=
      Tendsto.const_mul_atTop hc'0 (tendsto_rpow_atTop M.hα)
    have hev1 : ∀ᶠ r : ℝ in atTop, (n : ℝ) ≤ c / 2 ^ (M.d + 1) * r ^ M.α :=
      htend.eventually (eventually_ge_atTop (n : ℝ))
    have hev2 : ∀ᶠ r : ℝ in atTop, max (2 * C) 4 ≤ r := eventually_ge_atTop _
    obtain ⟨r, hr1, hr2⟩ := (hev1.and hev2).exists
    calc (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by simp
      _ ≤ ENNReal.ofReal (c / 2 ^ (M.d + 1) * r ^ M.α) := ENNReal.ofReal_le_ofReal hr1
      _ ≤ ∑' y : M.V, M.twoPointE M.betaCrit 0 y := key r hr2
  rw [eq_top_iff, ← ENNReal.iSup_natCast]
  exact iSup_le hn


/-! ### The divergence of the cutoff masses

The paper's `E_{β_c}|K| = ∞` is the uncut critical first moment; the `f → ∞` hypothesis of
`VolumeMoments.FirstMoment.first_moment_asymptotic` (formula (I.4.7)) is the corresponding
statement about the *cutoff* masses `r ↦ E_{β_c,r}|K| = M.cutMassAt r 0`.  The passage
between them is the landed cutoff-moment limit `SourceModelData.tendsto_cutMoment`. -/

/-- **`E_{β_c,r}|K| → ∞`.**  `h f → ∞` of Lemma I.4.5(3), from `E_{β_c}|K| = ∞`. -/
theorem tendsto_cutMassAt_atTop_nhds_top
    (htop : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)) = ⊤) :
    Tendsto (fun r : ℝ => M.cutMassAt r 0) atTop (𝓝 ⊤) := by
  have h : Tendsto (fun r : ℝ => M.cutMoment 1 r) atTop
      (𝓝 (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit))) := by
    simpa using M.tendsto_cutMoment 1
  rw [htop] at h
  simpa only [Orchestration.SourceModelData.cutMassAt_zero_eq_cutMoment] using h

/-- **The real-valued divergence, i.e. the `hinf` hypothesis of
`first_moment_asymptotic`.**  The eventual finiteness `hfin` is genuinely needed for the
transfer, because `(⊤ : ℝ≥0∞).toReal = 0`; it is *not* proved here (it is the strict
subcritical domination of the range-truncated law). -/
theorem tendsto_cutMassAt_toReal_atTop
    (h : Tendsto (fun r : ℝ => M.cutMassAt r 0) atTop (𝓝 ⊤))
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have hlt : ENNReal.ofReal (max b 0) < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
  have hev : ∀ᶠ r : ℝ in atTop, ENNReal.ofReal (max b 0) < M.cutMassAt r 0 :=
    h.eventually (isOpen_Ioi.mem_nhds hlt)
  obtain ⟨i, hi⟩ := eventually_atTop.1 (hev.and hfin)
  refine ⟨i, fun r hr => ?_⟩
  obtain ⟨h1, h2⟩ := hi r hr
  have h3 : ENNReal.ofReal (max b 0) ≤ M.cutMassAt r 0 := le_of_lt h1
  have h4 : (ENNReal.ofReal (max b 0)).toReal ≤ (M.cutMassAt r 0).toReal :=
    ENNReal.toReal_mono h2 h3
  rw [ENNReal.toReal_ofReal (le_max_right b 0)] at h4
  exact le_trans (le_max_left b 0) h4


/-! ### Why the divergence is not removable

`first_moment_asymptotic` is the analytic core of Case 3: from the ODE `f' = A(1−h)r^{−α−1}f²`,
`h → 0` and `f → ∞` it concludes `f r / ((α/A) r^α) → 1`.  The `f → ∞` hypothesis is *not*
redundant, so the model-level divergence supplied above is a genuine obligation and cannot be
skipped.  The witness below has `f ≡ 1`, `h ≡ 1`: it satisfies every atomic hypothesis of the
ODE lemma except `f → ∞` (in particular the error is bounded and measurable), and its ratio
tends to `0`, not `1`. -/

/-- **`hinf` is essential in Lemma I.4.5(3) / `first_moment_asymptotic`.** -/
theorem exists_bounded_solution_ratio_zero :
    ∃ (f f' h : ℝ → ℝ) (A α r₀ C : ℝ), 0 < A ∧ 0 < α ∧ 0 < r₀ ∧ 0 < C ∧
      (∀ t, r₀ ≤ t → HasDerivAt f (f' t) t) ∧
      (∀ t, r₀ ≤ t → 0 < f t) ∧
      (∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) ∧
      Measurable h ∧ (∀ t, r₀ ≤ t → |h t| ≤ C) ∧
      ¬ Tendsto (fun r => f r / (α / A * r ^ α)) atTop (𝓝 1) := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 1, 1, 1, 1, 1,
    one_pos, one_pos, one_pos, one_pos, ?_, ?_, ?_, measurable_const, ?_, ?_⟩
  · intro t _
    simpa using (hasDerivAt_const (x := t) (c := (1 : ℝ)))
  · intro t _; norm_num
  · intro t _; norm_num
  · intro t _; norm_num
  · intro hcon
    have heq : (fun r : ℝ => (1 : ℝ) / (1 / 1 * r ^ (1 : ℝ))) = fun r : ℝ => r⁻¹ := by
      funext r
      simp
    rw [heq] at hcon
    have h3 : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    exact zero_ne_one (tendsto_nhds_unique h3 hcon)

/-! ### Plugging the divergence into the landed analytic core

The following is the shape in which Case 3 consumes the results above: the ODE (I.4.6) at the
cutoff mass, the vanishing `Ē_{1,r} → 0` and the divergence supplied by Theorem I.2.14 give the
first-order asymptotic.  The ODE and the vanishing are *not* proved here (the derivative-to-ODE
handoff and the Kozma input); they are named hypotheses, and `0 < β_c` is retained explicitly. -/

/-- **Proposition I.4.2, Case 3, with the divergence discharged.** -/
theorem first_moment_asymptotic_of_rpow_lower
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c)
    (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) * ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r => (M.cutMassAt r 0).toReal / (M.α / (M.betaCrit : ℝ) * r ^ M.α))
      atTop (𝓝 1) :=
  VolumeMoments.FirstMoment.first_moment_asymptotic hβ M.hα hr₀ hderiv hpos
    (tendsto_cutMassAt_toReal_atTop M
      (tendsto_cutMassAt_atTop_nhds_top M (uncutFirstMoment_eq_top_of_rpow_lower M hc hαd hlow))
      hfin)
    hode hmeas hC h0

end

end PercLib.CriticalLRP.I42C
