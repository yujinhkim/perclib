/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0 license.

# A7 — the threshold supplied by subcritical finiteness cannot be uniform

The formal counterpart of the source's sentence "`r₀(β)` is finite for every
`β_c/2 ≤ β < β_c` by sharpness of the phase transition" is
`SourceModelData.exists_threshold_cutMassAtBeta_le_two_alpha`
(`LargeRadiusMoments.lean`): the threshold

  `r₀(β) = max 1 ((χ_β / (2α/β))^(1/α))`,   `χ_β = E_β|K|`,

is explicit and finite at every fixed `β < β_c`.  The passage `β ↑ β_c` of
`MomentMonotonicity/Temperature.lean` instead needs **one** threshold on
`[β_c/2, β_c)`.  This file proves that the explicit threshold above cannot be
that one whenever the subcritical mean is unbounded as `β ↑ β_c`: it escapes to
infinity.  So the uniform a priori bound of the source genuinely needs the
bootstrap (Lemma I.4.5 plus the error bound), not sharpness alone; this is a
limitation of the bounding route, not a claim that such a uniform bound is false.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.ReducedMomentTransfer
public import PercLib.CriticalLRP.MomentMonotonicity.Temperature

/-!
# Escape of the explicit sharpness threshold

`not_bdd_threshold_of_tendsto_atTop` is purely analytic: if `χ : ℝ≥0 → ℝ` tends
to `atTop` at `β_c` from the left, the family
`β ↦ max 1 ((χ β / (2α/β))^(1/α))` is unbounded above on the left of `β_c`.
`SourceModelData.not_bdd_sharpness_threshold_of_subcritical_mean` instantiates it
at `χ_β = E_β|K_0|` of the actual source model.

The hypothesis `Tendsto χ (𝓝[<] β_c) atTop` is the `β ↑ β_c` divergence of the
subcritical mean (source Theorem I.4.2).  It is the exact input left open here;
nothing in this file derives it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

variable {M : SourceModelData}

/-- **The explicit sharpness threshold is not uniformly bounded** when the
subcritical mean tends to infinity.  Analytic form, for an arbitrary real
function `χ` of the intensity. -/
theorem not_bdd_threshold_of_tendsto_atTop {βc : ℝ≥0} (hβc : 0 < βc) {α : ℝ}
    (hα : 0 < α) {χ : ℝ≥0 → ℝ} (hχ : Tendsto χ (𝓝[<] βc) atTop) :
    ¬ ∃ B : ℝ, ∀ β : ℝ≥0, β < βc →
      max 1 ((χ β / (2 * α / (β : ℝ))) ^ (1 / α)) ≤ B := by
  rintro ⟨B, hB⟩
  haveI : NeBot (𝓝[<] βc) := nhdsLT_neBot_of_exists_lt ⟨0, hβc⟩
  have hβcR : (0 : ℝ) < (βc : ℝ) := by exact_mod_cast hβc
  have hαpos : (0 : ℝ) < α := hα
  -- a level above `B` that `χ` eventually exceeds
  set K : ℝ := (max B 1 + 1) ^ α * (4 * α / (βc : ℝ)) with hK
  have hKpos : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ (max B 1 + 1) ^ α :=
      Real.rpow_nonneg (by linarith [le_max_right B (1 : ℝ)]) α
    have h2 : (0 : ℝ) ≤ 4 * α / (βc : ℝ) := by positivity
    exact mul_nonneg h1 h2
  -- eventually `βc/2 < β < βc` and `χ β ≥ K`
  have hself : ∀ᶠ β : ℝ≥0 in 𝓝[<] βc, β < βc := self_mem_nhdsWithin
  have hhalf : ∀ᶠ β : ℝ≥0 in 𝓝[<] βc, βc / 2 < β := by
    have hmem : Set.Ioi (βc / 2) ∈ 𝓝 βc := isOpen_Ioi.mem_nhds (half_lt_self hβc)
    exact nhdsWithin_le_nhds hmem
  have hbig : ∀ᶠ β : ℝ≥0 in 𝓝[<] βc, K ≤ χ β := hχ.eventually (eventually_ge_atTop K)
  obtain ⟨β, hβK, hβhalf, hββc⟩ := (hbig.and (hhalf.and hself)).exists
  -- the denominator bound from `β > βc/2`
  have hβpos : (0 : ℝ) < (β : ℝ) := by
    have hlt : ((βc : ℝ)) / 2 < (β : ℝ) := by exact_mod_cast hβhalf
    have h2 : (0 : ℝ) < (βc : ℝ) / 2 := by linarith
    linarith
  have hden : 2 * α / (β : ℝ) < 4 * α / (βc : ℝ) := by
    have hb2 : (0 : ℝ) < (βc : ℝ) / 2 := by linarith
    have hlt : (βc : ℝ) / 2 < (β : ℝ) := by exact_mod_cast hβhalf
    have h := div_lt_div_of_pos_left (a := 2 * α) (b := (β : ℝ)) (c := (βc : ℝ) / 2)
      (by positivity) hb2 hlt
    have hid : (4 : ℝ) * α / (βc : ℝ) = 2 * α / ((βc : ℝ) / 2) := by
      field_simp
      norm_num
    rw [hid]
    exact h
  have hdenpos : (0 : ℝ) < 2 * α / (β : ℝ) := by positivity
  have hquot : (max B 1 + 1) ^ α < χ β / (2 * α / (β : ℝ)) := by
    rw [lt_div_iff₀ hdenpos]
    calc (max B 1 + 1) ^ α * (2 * α / (β : ℝ))
        < (max B 1 + 1) ^ α * (4 * α / (βc : ℝ)) := by
          refine mul_lt_mul_of_pos_left hden ?_
          exact Real.rpow_pos_of_pos (by linarith [le_max_right B (1 : ℝ)]) α
      _ = K := hK.symm
      _ ≤ χ β := hβK
  have hrpow : (max B 1 + 1 : ℝ) < (χ β / (2 * α / (β : ℝ))) ^ (1 / α) := by
    have hbase : (0 : ℝ) ≤ max B 1 + 1 := by linarith [le_max_right B (1 : ℝ)]
    calc (max B 1 + 1 : ℝ) = ((max B 1 + 1) ^ α) ^ (1 / α) := by
          rw [← Real.rpow_mul hbase, show α * (1 / α) = 1 by field_simp, Real.rpow_one]
      _ < (χ β / (2 * α / (β : ℝ))) ^ (1 / α) :=
          Real.rpow_lt_rpow (Real.rpow_nonneg hbase α) hquot (by positivity)
  have := hB β hββc
  have hle : max 1 ((χ β / (2 * α / (β : ℝ))) ^ (1 / α))
      = (χ β / (2 * α / (β : ℝ))) ^ (1 / α) := by
    refine max_eq_right ?_
    linarith [le_max_right B (1 : ℝ)]
  rw [hle] at this
  linarith [le_max_left B (1 : ℝ)]

/-- **At the actual source model: the explicit threshold escapes.**

If the uncut subcritical mean of the source model tends to infinity as
`β ↑ β_c`, then the thresholds
`max 1 ((E_β|K_0| / (2α/β))^(1/α))` are unbounded above on `[0, β_c)`; hence no
single `R` can serve for all `β < β_c` in that route. -/
theorem SourceModelData.not_bdd_sharpness_threshold_of_subcritical_mean
    (M : SourceModelData) {βc : ℝ≥0} (hβc : 0 < βc) (hβcEq : βc = M.betaCrit)
    (hχ : Tendsto
      (fun β : ℝ≥0 => (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)).toReal)
      (𝓝[<] βc) atTop) :
    ¬ ∃ B : ℝ, ∀ β : ℝ≥0, β < M.betaCrit →
      max 1 (((∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)).toReal / (2 * M.α / (β : ℝ)))
        ^ (1 / M.α)) ≤ B := by
  subst hβcEq
  exact not_bdd_threshold_of_tendsto_atTop hβc M.hα hχ

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.not_bdd_threshold_of_tendsto_atTop
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_bdd_sharpness_threshold_of_subcritical_mean
