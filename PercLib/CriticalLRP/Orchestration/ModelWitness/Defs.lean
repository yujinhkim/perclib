/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Source-model non-vacuity witnesses.  Independently authored during audit
`smwp648b3` and recompiled by the integrator before module registration.
The unit normalized sup norm is `2‖·‖∞`; the kernel has the exact power-law
derivative from Definition I.1.3, with logarithmic error identically zero.
-/

/-
m3 audit scratch (swarm smwp648b3): non-vacuity witness for the source-model vocabulary.

`SourceModelData`/`SourceNormData` are quantified over by every `M.cutMoment` statement,
but no inhabitant is constructed anywhere in the campaign tree.  Here is one, with
*the source's own normalizations* (Hutchcroft, arXiv:2508.18807v1, Definition I.1.3,
display (*)): unit norm ball of Lebesgue volume `1`, kernel derivative
`|J'(r)| = r^{-d-α-1}` exactly (`δ ≡ 0`), hence `K r = r^{-d-α}/(d+α)` and
`K r = ∫_r^∞ |J'|`.  No fallback or relaxed field is used.
-/
module

public import PercLib.CriticalLRP.Orchestration.SourceModel

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- The normalized sup norm `ρ v = 2 ‖v‖∞` on `Fin d → ℝ`: its unit ball is the cube
`[-1/2, 1/2]^d`, of Lebesgue volume `1`. -/
noncomputable def sourceNormWitness (d : ℕ) : SourceNormData d where
  ρ := fun v => 2 * ‖v‖
  ρ_zero := by simp
  ρ_pos := fun v hv => by
    have h : 0 < ‖v‖ := norm_pos_iff.mpr hv
    linarith
  ρ_neg := by
    intro v
    simp
  ρ_add_le := by
    intro v w
    calc 2 * ‖v + w‖ ≤ 2 * (‖v‖ + ‖w‖) := by
          gcongr
          exact norm_add_le v w
      _ = 2 * ‖v‖ + 2 * ‖w‖ := by ring
  ρ_smul := by
    intro c v
    rw [norm_smul, Real.norm_eq_abs]
    ring
  ρ_continuous := by fun_prop
  unitBall_volume := by
    have hset : {v : Fin d → ℝ | 2 * ‖v‖ ≤ 1} = Metric.closedBall (0 : Fin d → ℝ) (1 / 2) := by
      ext v
      rw [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero]
      constructor <;> intro h <;> linarith
    rw [hset, MeasureTheory.volume_pi_closedBall (0 : Fin d → ℝ) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp [Real.volume_closedBall]


/-- **A genuine inhabitant of the paper-model structure.**  `d ≥ 1`, any `α > 0`, the
normalized sup norm `2‖·‖∞`, and the source-normalized kernel
`K r = r^{-d-α}/(d+α)`, whose derivative satisfies `|J'(r)| = r^{-d-α-1}` exactly
(`δ ≡ 0` in Definition I.1.3).  Every field of `SourceModelData` is discharged, so the
`M.cutMoment`-quantified theorems are not vacuous for want of a model. -/
noncomputable def sourceModelWitness (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) : SourceModelData where
  d := d
  hd := hd
  α := α
  hα := hα
  S := sourceNormWitness d
  K := fun r => r ^ (-(d : ℝ) - α) / ((d : ℝ) + α)
  K_nonneg := by
    intro r hr
    have hc : (0 : ℝ) < (d : ℝ) + α := by positivity
    exact div_nonneg (Real.rpow_nonneg hr.le _) hc.le
  K_antitone := by
    intro s hs t _ht hst
    have hc : (0 : ℝ) < (d : ℝ) + α := by positivity
    have hz : -(d : ℝ) - α ≤ 0 := by
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hs hst hz) hc.le
  K_diff := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    exact ((Real.hasDerivAt_rpow_const (p := -(d : ℝ) - α) (Or.inl hx0)).div_const
      ((d : ℝ) + α)).differentiableAt.differentiableWithinAt
  K_eq_integral := by
    intro r hr
    have hc : (0 : ℝ) < (d : ℝ) + α := by positivity
    have hderiv : ∀ s : ℝ, 0 < s →
        deriv (fun t : ℝ => t ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) s
          = -(s ^ (-(d : ℝ) - α - 1)) := by
      intro s hs
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hd1 : HasDerivAt (fun t : ℝ => t ^ (-(d : ℝ) - α))
          ((-(d : ℝ) - α) * s ^ (-(d : ℝ) - α - 1)) s :=
        Real.hasDerivAt_rpow_const (p := -(d : ℝ) - α) (Or.inl hs0)
      have h := hd1.div_const ((d : ℝ) + α)
      rw [h.deriv]
      field_simp
      ring
    have habs : ∀ s : ℝ, 0 < s → |-(s ^ (-(d : ℝ) - α - 1))| = s ^ (-(d : ℝ) - α - 1) := by
      intro s hs
      rw [abs_neg, abs_of_pos (Real.rpow_pos_of_pos hs _)]
    have hcongr : (∫ s in Ioi r, |deriv (fun t : ℝ => t ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) s|)
        = ∫ s in Ioi r, s ^ (-(d : ℝ) - α - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro s hs
      have hs0 : 0 < s := lt_trans hr (Set.mem_Ioi.mp hs)
      simp only [hderiv s hs0, habs s hs0]
    rw [hcongr, integral_Ioi_rpow_of_lt (by linarith : -(d : ℝ) - α - 1 < -1) hr]
    have e1 : -(d : ℝ) - α - 1 + 1 = -((d : ℝ) + α) := by ring
    rw [e1, show -(d : ℝ) - α = -((d : ℝ) + α) from by ring]
    field_simp
  exists_error := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro r hr
      have hc : (0 : ℝ) < (d : ℝ) + α := by positivity
      have hderiv : ∀ s : ℝ, 0 < s →
          deriv (fun t : ℝ => t ^ (-(d : ℝ) - α) / ((d : ℝ) + α)) s
            = -(s ^ (-(d : ℝ) - α - 1)) := by
        intro s hs
        have hs0 : s ≠ 0 := ne_of_gt hs
        have hd1 : HasDerivAt (fun t : ℝ => t ^ (-(d : ℝ) - α))
            ((-(d : ℝ) - α) * s ^ (-(d : ℝ) - α - 1)) s :=
          Real.hasDerivAt_rpow_const (p := -(d : ℝ) - α) (Or.inl hs0)
        have h := hd1.div_const ((d : ℝ) + α)
        rw [h.deriv]
        field_simp
        ring
      rw [hderiv r hr, abs_neg, abs_of_pos (Real.rpow_pos_of_pos hr _)]
      simp
    · refine ⟨?_, tendsto_const_nhds⟩
      refine ⟨measurable_const, 1, one_pos, ?_⟩
      have hfun : (fun r : ℝ => |(0 : ℝ)| / r) = fun _ => (0 : ℝ) := by
        funext r
        simp
      rw [hfun]
      exact integrableOn_zero

end PercLib.CriticalLRP.Orchestration.Witness

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- The witness profile is non-degenerate: it strictly decreases between the
real points `1` and `2`.  This does not assert that either point is attained at
a nonzero lattice distance, and does not invoke the raw sup-norm coefficient. -/
theorem sourceModelWitness_K_two_lt_one :
    (sourceModelWitness 1 le_rfl 1 zero_lt_one).K 2 < (sourceModelWitness 1 le_rfl 1 zero_lt_one).K 1 := by
  simp only [sourceModelWitness]
  norm_num [Real.rpow_neg]

end PercLib.CriticalLRP.Orchestration.Witness
