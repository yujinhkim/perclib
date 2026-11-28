/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The uncut critical volume tail from the two-intensity comparison

Source: Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), proof of
Proposition I.4.15, Case 3 (p. 47):

> Since the triangle condition implies the volume-tail upper bound
> `P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}` [12, 75], we can bound the first moment from above by
> `E_{β_c,r}|K| = ∑_n P_{β_c,r}(|K| ≥ n) ≤ ...`

The citation `[12, 75]` is Barsky–Aizenman, *Percolation critical exponents under the triangle
condition*, Ann. Probab. 19 (1991) 1520–1536, and Hutchcroft, *On the derivation of mean-field
percolation critical exponents from the triangle condition*, J. Stat. Phys. 189 (2022) 6.
The content of `[75]` that produces the tail is exactly two theorems, which this file names
verbatim and then uses; nothing else of `[75]` is needed:

* `thm:DM_Chi` (two-intensity comparison). For a transitive weighted graph normalised so that
  `∑_{e ∈ E^→_o} J_e = 1`, every `β₂ ≥ β₁ > 0` and `n ≥ 0` satisfy
  `P_{β₂}(|K| ≥ n) ≤ (2/n + (4/β₁)|β₂ − β₁|²) χ_{β₁}`, where `χ_β = E_β|K|`.
  In the general (unnormalised) normalisation the factor `4` is multiplied by
  `A = ∑_{e ∈ E^→_o} J_e`; `TwoIntensityTailComparison A` below is that statement at the
  actual model, with the real susceptibility `lawSusceptibility`.
* `thm:main_chi` (mean-field susceptibility upper bound `χ_β ⪯ (β_c − β)^{-1}`), the main
  theorem of `[75]`, proved there from the triangle condition; `SusceptibilityBound K` below is
  that statement at the actual model.

The derivation performed here is the source's own step: take `β₁ = β_c − n^{-1/2}` and
`β₂ = β_c`, so that `|β₂ − β₁|² = 1/n`, `1/β₁ ≤ 2/β_c` once `n ≥ (2/β_c)²`, and
`χ_{β₁} ≤ K n^{1/2}`; then `P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}`. This yields production's predicate
`SourceModelData.CriticalVolumeTail C` with the explicit constant
`C = max 1 (max (2/β_c) (2K + 8AK/β_c))`.

Neither named input is proved here, and no triangle condition is assumed: this file is a
reduction of the cited tail to the two exact theorems of `[75]`, not a re-statement of the tail.
No cutoff law is used, so no cutoff-to-uncut monotonicity is invoked, and no finite-mean,
zero-percolation or radius-dependent moment input appears.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.TailLower

/-! A conditional derivation of the cited critical-volume tail and Case-3
moment gap from an explicit two-intensity comparison and susceptibility bound.
Those external probabilistic inputs are not proved or instantiated here. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- The real cluster-volume tail probability at intensity `β`, uncut and infinite-volume:
`P_β(|K_0| ≥ n)`.  At `β = β_c` this is `M.tailProb n` definitionally. -/
noncomputable def lawTail (β : ℝ≥0) (n : ℕ) : ℝ :=
  (M.law β).real {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}

/-- The extended-real susceptibility at intensity `β`, `χ_β = E_β|K_0|`. -/
noncomputable def lawSusceptibility (β : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)

theorem lawTail_betaCrit (n : ℕ) : M.lawTail M.betaCrit n = M.tailProb n := rfl

/-- `P_β(|K_0| ≥ n) ≤ 1`. -/
theorem lawTail_le_one (β : ℝ≥0) (n : ℕ) : M.lawTail β n ≤ 1 := by
  have : IsProbabilityMeasure (M.law β) := inferInstance
  have hm : M.law β {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  rw [lawTail, Measure.real]
  calc (M.law β {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal
      ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hm
    _ = 1 := by simp

/-- **Theorem `thm:DM_Chi` of [75], at the actual model.**  Two-intensity comparison of the
cluster-volume tail: for every `β₂ ≥ β₁ > 0` and `n ≥ 1`,
`P_{β₂}(|K_0| ≥ n) ≤ (2/n + (4A/β₁)|β₂ − β₁|²) χ_{β₁}`,
where `A = ∑_{e ∈ E^→_o} J_e` is the model's one-arm edge weight sum (`A = 1` under the
normalisation of `[75]`), and `χ_{β₁} = E_{β₁}|K_0|` is `lawSusceptibility`.  The source proves
this from the generalised Dewan–Muirhead inequality, which it derives from the relative entropy
method; that proof is not formalized here. -/
def TwoIntensityTailComparison (A : ℝ) : Prop :=
  ∀ (β₁ β₂ : ℝ≥0) (n : ℕ), 0 < β₁ → β₁ ≤ β₂ → 1 ≤ n →
    M.lawTail β₂ n ≤
      (2 / (n : ℝ) + 4 * A / (β₁ : ℝ) * ((β₂ : ℝ) - (β₁ : ℝ)) ^ 2) *
        (M.lawSusceptibility β₁).toReal

/-- **Theorem `thm:main_chi` of [75] (mean-field susceptibility upper bound)**, at the actual
model: `χ_β ≤ K/(β_c − β)` for every `β < β_c`.  `[75]` proves this from the triangle
condition; that proof is not formalized here. -/
def SusceptibilityBound (K : ℝ) : Prop :=
  ∀ β : ℝ≥0, β < M.betaCrit →
    M.lawSusceptibility β ≤ ENNReal.ofReal (K / ((M.betaCrit : ℝ) - (β : ℝ)))

/-- Pure real arithmetic of the source's optimisation step: with `b = √n` (so `b * b = n`),
`β₁ ≥ β_c/2` and `β_c − β₁ = 1/b`, the two-intensity right-hand side at `(β₁, β_c)` against a
susceptibility value `K * b` is at most `(2K + 8AK/β_c)/b`. -/
theorem twoIntensity_arith {n : ℕ} {bc β₁ K A b : ℝ}
    (hbc : 0 < bc) (hb1 : 0 < β₁) (hb : 0 < b) (hbsq : b * b = (n : ℝ))
    (hβ : bc ≤ 2 * β₁) (hK : 0 ≤ K) (hA : 0 ≤ A) (hdiff : bc - β₁ = 1 / b) :
    (2 / (n : ℝ) + 4 * A / β₁ * (bc - β₁) ^ 2) * (K * b) ≤ (2 * K + 8 * A * K / bc) / b := by
  have hbne : b ≠ 0 := hb.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [← hbsq]; positivity
  have hsq : (bc - β₁) ^ 2 = 1 / (n : ℝ) := by
    rw [hdiff, div_pow, one_pow, sq, ← hbsq]
  rw [hsq]
  have hfac : (2 / (n : ℝ) + 4 * A / β₁ * (1 / (n : ℝ))) * (K * b)
      = 2 * K / b + 4 * A * K / (β₁ * b) := by
    rw [← hbsq]
    field_simp
  rw [hfac]
  have hstep : 4 * A * K / (β₁ * b) ≤ 8 * A * K / (bc * b) := by
    have hb1le : 4 * A * K / β₁ ≤ 8 * A * K / bc := by
      have h2 : 1 / β₁ ≤ 2 / bc := by
        rw [div_le_div_iff₀ hb1 hbc]
        linarith
      calc 4 * A * K / β₁ = (4 * A * K) * (1 / β₁) := by ring
        _ ≤ (4 * A * K) * (2 / bc) := by
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 8 * A * K / bc := by ring
    calc 4 * A * K / (β₁ * b) = (4 * A * K / β₁) / b := by field_simp
      _ ≤ (8 * A * K / bc) / b := div_le_div_of_nonneg_right hb1le hb.le
      _ = 8 * A * K / (bc * b) := by field_simp
  have hcomb : 2 * K / b + 4 * A * K / (β₁ * b) ≤ 2 * K / b + 8 * A * K / (bc * b) := by
    linarith
  have hfinal : 2 * K / b + 8 * A * K / (bc * b) = (2 * K + 8 * A * K / bc) / b := by
    field_simp
  rw [← hfinal]
  exact hcomb

/-- **The cited critical volume tail from the two-intensity comparison and the mean-field
susceptibility bound.**  For every model with `β_c > 0`, an unnormalised two-intensity
comparison of constant `A ≥ 0` and a susceptibility bound of constant `K ≥ 0`, the uncut critical
cluster-volume tail satisfies `P_{β_c}(|K_0| ≥ n) ⪯ n^{-1/2}`, i.e. `M.CriticalVolumeTail C`
for the explicit `C = max 1 (max (2/β_c) (2K + 8AK/β_c))`.

This is the source's step `β₁ = β_c − n^{-1/2}`, `β₂ = β_c`. -/
theorem exists_criticalVolumeTail_of_twoIntensityComparison {A K : ℝ} (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hbc : 0 < (M.betaCrit : ℝ))
    (hDM : M.TwoIntensityTailComparison A) (hSus : M.SusceptibilityBound K) :
    ∃ C : ℝ, 0 ≤ C ∧ M.CriticalVolumeTail C := by
  set bc : ℝ := (M.betaCrit : ℝ) with hbcdef
  set C : ℝ := max 1 (max (2 / bc) (2 * K + 8 * A * K / bc)) with hCdef
  have hbcpos : 0 < bc := hbc
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hC2 : 2 / bc ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC3 : 2 * K + 8 * A * K / bc ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  refine ⟨C, hC0, M.criticalVolumeTail_of_pointwise (C := C) ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set b : ℝ := Real.sqrt (n : ℝ) with hbdef
  have hbpos : 0 < b := Real.sqrt_pos.2 hnpos
  have hbsq : b * b = (n : ℝ) := by
    rw [hbdef, Real.mul_self_sqrt hnpos.le]
  rcases le_or_gt (2 : ℝ) (bc * b) with hbig | hsmall
  · -- main regime: `β₁ = β_c − 1/√n ≥ β_c/2 > 0`
    have hle : 1 / b ≤ bc / 2 := by
      rw [div_le_div_iff₀ hbpos two_pos]
      linarith
    have hnonneg : (0 : ℝ) ≤ bc - 1 / b := by
      have : (0 : ℝ) < bc / 2 := by positivity
      linarith
    have hpos : 0 < bc - 1 / b := by
      have : (0 : ℝ) < bc / 2 := by positivity
      linarith
    set β₁ : ℝ≥0 := ⟨bc - 1 / b, hnonneg⟩ with hβ1def
    have hβ1coe : (β₁ : ℝ) = bc - 1 / b := rfl
    have hβ1posR : (0 : ℝ) < (β₁ : ℝ) := by rw [hβ1coe]; exact hpos
    have hβ1pos : 0 < β₁ := NNReal.coe_pos.1 hβ1posR
    have hβ1lt : β₁ < M.betaCrit := by
      refine NNReal.coe_lt_coe.1 ?_
      rw [hβ1coe, hbcdef]
      linarith [one_div_pos.2 hbpos]
    have hβdiff : (M.betaCrit : ℝ) - (β₁ : ℝ) = 1 / b := by
      rw [hβ1coe, hbcdef]
      ring
    have hDMapp := hDM β₁ M.betaCrit n hβ1pos (le_of_lt hβ1lt) hn
    have htoReal : (M.lawSusceptibility β₁).toReal ≤ K * b := by
      have h1 : (M.lawSusceptibility β₁).toReal
          ≤ (ENNReal.ofReal (K / ((M.betaCrit : ℝ) - (β₁ : ℝ)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hSus β₁ hβ1lt)
      have h2 : (ENNReal.ofReal (K / ((M.betaCrit : ℝ) - (β₁ : ℝ)))).toReal
          = K / ((M.betaCrit : ℝ) - (β₁ : ℝ)) :=
        ENNReal.toReal_ofReal (by rw [hβdiff]; positivity)
      have h3 : K / ((M.betaCrit : ℝ) - (β₁ : ℝ)) = K * b := by
        rw [hβdiff]
        field_simp
      rw [h2, h3] at h1
      exact h1
    have hnonneg' : 0 ≤ 2 / (n : ℝ) + 4 * A / (β₁ : ℝ) *
        ((M.betaCrit : ℝ) - (β₁ : ℝ)) ^ 2 := by
      have h4 : (0 : ℝ) ≤ 4 * A / (β₁ : ℝ) := div_nonneg (by positivity) hβ1posR.le
      have hsq : (0 : ℝ) ≤ ((M.betaCrit : ℝ) - (β₁ : ℝ)) ^ 2 := sq_nonneg _
      positivity
    have hbound := twoIntensity_arith (n := n) (bc := bc) (β₁ := (β₁ : ℝ)) (K := K) (A := A)
      (b := b) hbcpos hβ1posR hbpos hbsq (by rw [hβ1coe, hbcdef]; linarith) hK hA
      (by rw [hβ1coe]; ring)
    calc M.tailProb n
        ≤ (2 / (n : ℝ) + 4 * A / (β₁ : ℝ) * ((M.betaCrit : ℝ) - (β₁ : ℝ)) ^ 2) *
            (M.lawSusceptibility β₁).toReal := hDMapp
      _ ≤ (2 / (n : ℝ) + 4 * A / (β₁ : ℝ) * ((M.betaCrit : ℝ) - (β₁ : ℝ)) ^ 2) *
            (K * b) := mul_le_mul_of_nonneg_left htoReal hnonneg'
      _ ≤ (2 * K + 8 * A * K / bc) / b := hbound
      _ ≤ C / b := div_le_div_of_nonneg_right hC3 hbpos.le
      _ = C / Real.sqrt n := by rw [hbdef]
  · -- small regime: `n` is small, use `P ≤ 1` and `C ≥ 2/β_c > √n`
    have hble : b ≤ 2 / bc := by
      rw [le_div_iff₀ hbcpos]
      linarith
    have hCle : b ≤ C := le_trans hble hC2
    have h1 : 1 ≤ C / b := by
      rw [le_div_iff₀ hbpos]
      simpa using hCle
    calc M.tailProb n ≤ 1 := M.tailProb_le_one n
      _ ≤ C / b := h1
      _ = C / Real.sqrt n := by rw [hbdef]

/-- **Case-3 moment gap of I.4.15 from the two named theorems of [75].**  Production's
`case3_hgm_of_tail` derives the lower second-moment comparison
`c · (E_{β_c,r}|K|)^3 ≤ E_{β_c,r}|K|²` eventually from the uncut critical volume-tail envelope
`CriticalVolumeTail C` and finiteness of the cutoff second moment.  Composing it with
`exists_criticalVolumeTail_of_twoIntensityComparison` removes the volume-tail leaf: the moment
gap now follows from the two-intensity comparison and the mean-field susceptibility bound alone.
No cutoff-to-uncut monotonicity, triangle condition, finite-mean or radius-dependent input is
used beyond the explicit `h2`. -/
theorem exists_case3_hgm_of_twoIntensityComparison {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hbc : 0 < (M.betaCrit : ℝ)) (hDM : M.TwoIntensityTailComparison A)
    (hSus : M.SusceptibilityBound K) (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ r in atTop,
      c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
        ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r := by
  obtain ⟨C, hC, hTail⟩ :=
    M.exists_criticalVolumeTail_of_twoIntensityComparison hA hK hbc hDM hSus
  exact I420Case3.case3_hgm_of_tail M hC hTail h2

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration
set_option linter.hashCommand false
#print axioms SourceModelData.lawTail_betaCrit
#print axioms SourceModelData.lawTail_le_one
#print axioms SourceModelData.twoIntensity_arith
#print axioms SourceModelData.exists_criticalVolumeTail_of_twoIntensityComparison
#print axioms SourceModelData.exists_case3_hgm_of_twoIntensityComparison
end PercLib.CriticalLRP.Orchestration
