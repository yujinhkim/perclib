/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.ReducedCoefficients.Defs
public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs

/-!
# The critical mean is the supremum of the reduced-intensity means

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.5 and the sentence "noting that `r₀(β)` is finite for
every `β_c/2 ≤ β < β_c` by sharpness of the phase transition" in the proof of Lemma
I.4.9.

## What is proved

`SourceModelData.uncutMean β = E_β |K_0|` is the uncut first moment at intensity `β`
(`Defs.lean`).  For the *strict* coefficient `c_r = cutCoeffNN t₀ r` of Definition I.1.5
(`J_r ≤ c_r J` with `c_r < 1` at every `r > 0`, `c_r ≥ 1/2`, `c_r → 1`), the reduced
intensity `β_c * c_r` is genuinely subcritical, and the cutoff first moment at `β_c` is
bounded by the uncut first moment at that reduced intensity
(`cutMassAtBeta_le_uncutMean_mul`, the transfer of `MomentMonotonicity`).

* `uncutMean_eq_iSup_reduced_coeff`: at **every** intensity, `E_β|K_0| = ⨆_r E_{β c_r}|K_0|`
  is the supremum of the uncut means at the strictly reduced intensities — the formal
  counterpart of the paper's "the derivation of (I.4.15) above can be carried out at other
  values of `β ≤ β_c`".
* `uncutMean_ne_top_iff_exists_bdd_reduced_coeff`: consequently `E_β|K_0|` is finite **iff**
  the family `r ↦ E_{β c_r}|K_0|` is *bounded*, not merely finite termwise.
* `forall_lt_uncutMean_ne_top_iff_forall_reduced_ne_top`: the sharpness input *below* `β`
  is equivalent to finiteness of that family, so the difference between sharpness below
  `β` and sharpness at `β` is exactly the uniformity in `r`.
* `uncutMean_betaCrit_eq_iSup_reduced`, `uncutMean_betaCrit_ne_top_iff_exists_bdd_reduced`,
  `exists_reduced_uncutMean_gt_of_betaCrit_eq_top`: the same statements at `β_c`.
* `uncutMean_betaCrit_ne_top_iff_exists_bdd_reduced`: consequently the critical mean is
  finite **iff** the family `r ↦ E_{β_c c_r}|K_0|` of strictly subcritical means is
  *bounded*.
* `exists_reduced_uncutMean_gt_of_betaCrit_eq_top`: if the critical mean is infinite then
  the strictly subcritical means are unbounded above.

## Why this is the exact shape of the gap

The finite-mean set is a down-set (`uncutMean_mono`), so the sharpness input `hsub`
(`SubcriticalFiniteMean`: `E_β|K_0| ≠ ⊤` for every `β < β_c`) says precisely that every
member of the reduced family above is *finite*.  The three theorems above say that this
gives finiteness of `E_{β_c}|K_0|` if and only if the same family is *bounded*: the
comparison `J_r ≤ c_r J` with `c_r → 1` carries no slack, so no bound at a single
strictly smaller intensity (and no finite list of them) can supply the missing
uniformity.  This file does not prove `hsub`, and it does not prove that the reduced
family is bounded.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume

namespace SourceModelData

variable (M : SourceModelData)

/-- **The uncut first moment is nondecreasing in the intensity.**  Edge probabilities
increase with `β`, hence so does the cluster volume of the origin. -/
theorem uncutMean_mono {β γ : ℝ≥0} (h : β ≤ γ) : M.uncutMean β ≤ M.uncutMean γ := by
  simp only [SourceModelData.uncutMean, SourceModelData.law, longRangeMeasure]
  exact lintegral_clusterVol_mono
    (fun e => bernoulliEdgeProb_mono M.kernel M.kernel_nonneg h e) 0

/-- The uncut first moment is at least `1`: the cluster of the origin contains the
origin.  In particular a finite mean is not a vacuous condition. -/
theorem one_le_uncutMean (β : ℝ≥0) : 1 ≤ M.uncutMean β := by
  haveI : IsProbabilityMeasure (M.law β) := by
    rw [SourceModelData.law, longRangeMeasure]
    infer_instance
  calc (1 : ℝ≥0∞) = ∫⁻ _ω, (1 : ℝ≥0∞) ∂(M.law β) := by simp
    _ ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β) :=
        lintegral_mono (fun ω => one_le_clusterVol ω 0)

/-- The strict coefficient is at most `1`, at every radius. -/
theorem cutCoeff_le_one (t0 r : ℝ) : M.cutCoeff t0 r ≤ 1 := min_le_left _ _

/-- The `ℝ≥0` coefficient is at most `1`, at every radius: this is what makes
`β * c_r ≤ β` hold for the reduced intensity. -/
theorem cutCoeffNN_le_one (t0 r : ℝ) : M.cutCoeffNN t0 r ≤ 1 := by
  calc M.cutCoeffNN t0 r = Real.toNNReal (M.cutCoeff t0 r) := rfl
    _ ≤ Real.toNNReal 1 := Real.toNNReal_le_toNNReal (M.cutCoeff_le_one t0 r)
    _ = 1 := Real.toNNReal_one

/-- At a positive radius the outer `min 1` in `cutCoeff` is inactive: the coefficient is
literally `1 - min (1/2) (K r / (2 K t₀))`, the coefficient produced by the strict
domination `SourceModelData.cutKernel_le_scaled`. -/
theorem coe_cutCoeffNN {t0 r : ℝ} (ht0 : 0 < t0) (hr : 0 < r) :
    (M.cutCoeffNN t0 r : ℝ) = 1 - min (1 / 2) (M.K r / (2 * M.K t0)) := by
  have hKr : 0 < M.K r := M.K_pos hr
  have hKt0 : 0 < M.K t0 := M.K_pos ht0
  have hq : 0 ≤ M.K r / (2 * M.K t0) :=
    le_of_lt (div_pos hKr (by linarith))
  have hmin0 : 0 ≤ min (1 / 2) (M.K r / (2 * M.K t0)) := le_min (by norm_num) hq
  have hminle : min (1 / 2) (M.K r / (2 * M.K t0)) ≤ 1 :=
    le_trans (min_le_left _ _) (by norm_num)
  have hcoef0 : 0 ≤ 1 - min (1 / 2) (M.K r / (2 * M.K t0)) := by linarith
  have hcoefle : 1 - min (1 / 2) (M.K r / (2 * M.K t0)) ≤ 1 := by linarith
  simp only [SourceModelData.cutCoeffNN, SourceModelData.cutCoeff]
  rw [Real.coe_toNNReal _ (le_min zero_le_one hcoef0), min_eq_right hcoefle]

/-- At every positive radius the strict coefficient is at least `1/2`: the reduced
intensities `β * c_r` all lie in the window `[β/2, β)` used in the proof of Lemma I.4.9. -/
theorem half_le_cutCoeffNN {t0 r : ℝ} (ht0 : 0 < t0) (hr : 0 < r) :
    (1 / 2 : ℝ) ≤ (M.cutCoeffNN t0 r : ℝ) := by
  rw [M.coe_cutCoeffNN ht0 hr]
  have hq : 0 < M.K r / (2 * M.K t0) :=
    div_pos (M.K_pos hr) (by have := M.K_pos ht0; linarith)
  have hmin : 0 < min (1 / 2) (M.K r / (2 * M.K t0)) := lt_min (by norm_num) hq
  have hminle : min (1 / 2) (M.K r / (2 * M.K t0)) ≤ 1 / 2 := min_le_left _ _
  linarith

/-- At every positive radius the strict coefficient is strictly below `1`, so `β * c_r` is
strictly subcritical. -/
theorem cutCoeffNN_lt_one {t0 r : ℝ} (ht0 : 0 < t0) (hr : 0 < r) :
    M.cutCoeffNN t0 r < 1 := by
  rw [← NNReal.coe_lt_coe, M.coe_cutCoeffNN ht0 hr, NNReal.coe_one]
  have hq : 0 < M.K r / (2 * M.K t0) :=
    div_pos (M.K_pos hr) (by have := M.K_pos ht0; linarith)
  have hmin : 0 < min (1 / 2) (M.K r / (2 * M.K t0)) := lt_min (by norm_num) hq
  linarith

/-- **Definition I.1.5 for the source cutoff, in `ℝ≥0`-coefficient form**: the cutoff
kernel at radius `r` is dominated by `c_r • J` with `c_r = cutCoeffNN t₀ r`. -/
theorem cutKernel_le_cutCoeffNN {t0 r : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (hr : 0 < r) (e : Sym2 M.V) :
    M.cutKernel r e ≤ (M.cutCoeffNN t0 r : ℝ) * M.kernel e := by
  rw [M.coe_cutCoeffNN ht0 hr]
  exact M.cutKernel_le_scaled ht0 hr hlat e

/-- **The transfer of Definition I.1.5 at an arbitrary intensity**: if the cutoff kernel
is dominated by `c • J`, then the cutoff first moment at intensity `β` is bounded by the
*uncut* first moment at the reduced intensity `β * c`.  Both sides are extended reals, so
`⊤` is allowed. -/
theorem cutMassAtBeta_le_uncutMean_mul {r : ℝ} {c : ℝ≥0}
    (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (c : ℝ) * M.kernel e) (β : ℝ≥0) :
    M.cutMassAtBeta β r 0 ≤ M.uncutMean (β * c) := by
  simp only [SourceModelData.cutMassAtBeta, SourceModelData.uncutMean, SourceModelData.law,
    longRangeMeasure]
  refine lintegral_clusterVol_mono (fun e => ?_) 0
  refine CutoffDominated.bernoulliEdgeProb_le_of_mul_le (M.cutKernel_nonneg r)
    M.kernel_nonneg ?_
  calc (β : ℝ) * M.cutKernel r e ≤ (β : ℝ) * ((c : ℝ) * M.kernel e) :=
        mul_le_mul_of_nonneg_left (hdom e) β.coe_nonneg
    _ = ((β * c : ℝ≥0) : ℝ) * M.kernel e := by
        rw [NNReal.coe_mul]; ring

/-- **The critical mean is the supremum of the reduced-intensity means.**

For the strict Definition I.1.5 coefficient `c_r` at radius `r`, every cutoff mean at
`β_c` is bounded by the uncut mean at the strictly smaller intensity `β_c * c_r`
(`cutMassAtBeta_le_uncutMean_mul`), and the cutoff means increase to the critical mean
(`SourceModelData.iSup_cutMoment_eq`).  Hence the two suprema agree.  Nothing is assumed
finite. -/
theorem uncutMean_betaCrit_eq_iSup_reduced {t0 : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) :
    M.uncutMean M.betaCrit
      = ⨆ (r : ℝ) (_ : 0 < r), M.uncutMean (M.betaCrit * M.cutCoeffNN t0 r) := by
  refine le_antisymm ?_ ?_
  · have hsup : M.uncutMean M.betaCrit = ⨆ r : ℝ, M.cutMoment 1 r := by
      rw [M.iSup_cutMoment_eq 1]
      simp [SourceModelData.uncutMean]
    rw [hsup]
    refine iSup_le fun r => ?_
    rcases le_or_gt r 0 with hr | hr
    · have h12 : M.cutMoment 1 r ≤ M.cutMoment 1 1 := M.cutMoment_monotone 1 (by linarith)
      have h2 : M.cutMoment 1 1 ≤ M.uncutMean (M.betaCrit * M.cutCoeffNN t0 1) := by
        rw [← M.cutMassAt_zero_eq_cutMoment, ← M.cutMassAtBeta_betaCrit]
        exact M.cutMassAtBeta_le_uncutMean_mul
          (M.cutKernel_le_cutCoeffNN ht0 hlat one_pos) M.betaCrit
      exact le_trans h12 (le_trans h2 (le_iSup₂_of_le 1 one_pos le_rfl))
    · have h2 : M.cutMoment 1 r ≤ M.uncutMean (M.betaCrit * M.cutCoeffNN t0 r) := by
        rw [← M.cutMassAt_zero_eq_cutMoment, ← M.cutMassAtBeta_betaCrit]
        exact M.cutMassAtBeta_le_uncutMean_mul
          (M.cutKernel_le_cutCoeffNN ht0 hlat hr) M.betaCrit
      exact le_trans h2 (le_iSup₂_of_le r hr le_rfl)
  · refine iSup_le fun r => iSup_le fun _hr => ?_
    have hb : (0 : ℝ≥0) ≤ M.betaCrit := zero_le
    refine M.uncutMean_mono ?_
    calc M.betaCrit * M.cutCoeffNN t0 r ≤ M.betaCrit * 1 :=
          mul_le_mul_of_nonneg_left (M.cutCoeffNN_le_one t0 r) hb
      _ = M.betaCrit := mul_one M.betaCrit

/-- **Finiteness of the critical mean is boundedness of the reduced-intensity means.**

The sharpness input `hsub` gives that each `E_{β_c c_r}|K_0|` is finite; the critical
mean is finite exactly when those values are *uniformly* bounded, i.e. when a single
finite constant works for all radii. -/
theorem uncutMean_betaCrit_ne_top_iff_exists_bdd_reduced {t0 : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) :
    M.uncutMean M.betaCrit ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ (r : ℝ), 0 < r → M.uncutMean (M.betaCrit * M.cutCoeffNN t0 r) ≤ C := by
  constructor
  · intro hfin
    have hb : (0 : ℝ≥0) ≤ M.betaCrit := zero_le
    exact ⟨_, hfin, fun r _hr => M.uncutMean_mono (by
      calc M.betaCrit * M.cutCoeffNN t0 r ≤ M.betaCrit * 1 :=
            mul_le_mul_of_nonneg_left (M.cutCoeffNN_le_one t0 r) hb
        _ = M.betaCrit := mul_one M.betaCrit)⟩
  · rintro ⟨C, hC, hb⟩
    rw [M.uncutMean_betaCrit_eq_iSup_reduced ht0 hlat]
    exact ne_top_of_le_ne_top hC (iSup_le fun r => iSup_le fun hr => hb r hr)

/-- If the critical mean is infinite, the reduced-intensity means are unbounded above:
no finite constant bounds the strictly subcritical intensities supplied by Definition
I.1.5. -/
theorem exists_reduced_uncutMean_gt_of_betaCrit_eq_top {t0 : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0)
    (htop : M.uncutMean M.betaCrit = ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    ∃ r : ℝ, 0 < r ∧ C < M.uncutMean (M.betaCrit * M.cutCoeffNN t0 r) := by
  by_contra h
  push Not at h
  have hne : M.uncutMean M.betaCrit ≠ ⊤ :=
    (M.uncutMean_betaCrit_ne_top_iff_exists_bdd_reduced ht0 hlat).mpr
      ⟨C, hC, fun r hr => h r hr⟩
  exact hne htop


/-! ## The exact shape of the remaining gap

Combining the three statements above with the sharpness input `SubcriticalFiniteMean` gives
the literal situation of the source's passage to `β_c`: every reduced intensity has a
finite mean, and the critical mean is infinite exactly when those finite values are
unbounded.  So the missing uniformity is a statement about the behaviour of the family
`r ↦ E_{β_c c_r}|K_0|`, not a statement about any single intensity. -/

/-- **Finitely many, in particular one, reduced intensity never suffice.**  Under the
sharpness input, if the critical mean is infinite then every reduced-intensity mean is
finite and the family of them is unbounded above: no bound available at a single strictly
subcritical intensity can be promoted to a bound at `β_c`. -/
theorem subcritical_finite_and_reduced_unbounded {t0 : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (hβc : 0 < M.betaCrit)
    (hsub : M.SubcriticalFiniteMean) (htop : M.uncutMean M.betaCrit = ⊤) :
    (∀ r : ℝ, 0 < r → M.uncutMean (M.betaCrit * M.cutCoeffNN t0 r) ≠ ⊤) ∧
      ∀ C : ℝ≥0∞, C ≠ ⊤ →
        ∃ r : ℝ, 0 < r ∧ C < M.uncutMean (M.betaCrit * M.cutCoeffNN t0 r) := by
  refine ⟨fun r hr => hsub _ ?_, fun C hC =>
    M.exists_reduced_uncutMean_gt_of_betaCrit_eq_top ht0 hlat htop hC⟩
  have hclt : M.cutCoeffNN t0 r < 1 := M.cutCoeffNN_lt_one ht0 hr
  calc M.betaCrit * M.cutCoeffNN t0 r < M.betaCrit * 1 :=
        mul_lt_mul_of_pos_left hclt hβc
    _ = M.betaCrit := mul_one M.betaCrit

/-! ## Discharging the divergence hypothesis of the landed threshold-escape theorem

`SharpnessThresholdEscape.lean` proves that the explicit threshold
`max 1 ((E_β|K_0| / (2α/β))^(1/α))` cannot be uniform on `[β_c/2, β_c)` from a hypothesis
`Tendsto (E_β|K_0|).toReal (𝓝[<] β_c) atTop`.  The following turns the critical clause
`E_{β_c}|K_0| = ⊤` alone (together with the sharpness input and `β_c > 0`) into that
divergence, by exhibiting, for every bound `B`, one *explicitly reduced* intensity
`β = β_c c_r < β_c` at which the threshold already exceeds `B`. -/

/-- **The explicit sharpness threshold escapes from the critical clause alone.** -/
theorem not_bdd_sharpness_threshold_of_uncutMean_betaCrit_eq_top {t0 : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (hβc : 0 < M.betaCrit)
    (hsub : M.SubcriticalFiniteMean) (htop : M.uncutMean M.betaCrit = ⊤) :
    ¬ ∃ B : ℝ, ∀ β : ℝ≥0, β < M.betaCrit →
      max 1 (((M.uncutMean β).toReal / (2 * M.α / (β : ℝ))) ^ (1 / M.α)) ≤ B := by
  rintro ⟨B, hB⟩
  have hα : 0 < M.α := M.hα
  have hbc : (0 : ℝ) < (M.betaCrit : ℝ) := by exact_mod_cast hβc
  -- the amplitude
  set P : ℝ := max B 1 + 1 with hP
  have hP1 : (1 : ℝ) ≤ P := by rw [hP]; have := le_max_right B (1 : ℝ); linarith
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le one_pos hP1
  set K : ℝ := P ^ M.α * (4 * M.α / (M.betaCrit : ℝ)) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0 : ℝ) ≤ P ^ M.α := Real.rpow_nonneg hP0.le _
    have h2 : (0 : ℝ) ≤ 4 * M.α / (M.betaCrit : ℝ) := by positivity
    exact mul_nonneg h1 h2
  -- a reduced intensity whose mean exceeds `K`
  obtain ⟨r, hr, hgt⟩ :=
    M.exists_reduced_uncutMean_gt_of_betaCrit_eq_top ht0 hlat htop
      (C := ENNReal.ofReal K) ENNReal.ofReal_ne_top
  set c : ℝ≥0 := M.cutCoeffNN t0 r with hcdef
  set β : ℝ≥0 := M.betaCrit * c with hβdef
  have hcoef : (c : ℝ) = 1 - min (1 / 2) (M.K r / (2 * M.K t0)) := M.coe_cutCoeffNN ht0 hr
  have hKr : 0 < M.K r := M.K_pos hr
  have hKt0 : 0 < M.K t0 := M.K_pos ht0
  have hq : 0 < M.K r / (2 * M.K t0) := div_pos hKr (by linarith)
  have hminpos : 0 < min (1 / 2) (M.K r / (2 * M.K t0)) := lt_min (by norm_num) hq
  have hminle : min (1 / 2) (M.K r / (2 * M.K t0)) ≤ 1 / 2 := min_le_left _ _
  have hchalf : (1 / 2 : ℝ) ≤ (c : ℝ) := M.half_le_cutCoeffNN ht0 hr
  have hclt : (c : ℝ) < 1 := by exact_mod_cast M.cutCoeffNN_lt_one ht0 hr
  have hβcoe : (β : ℝ) = (M.betaCrit : ℝ) * (c : ℝ) := by
    rw [hβdef, NNReal.coe_mul]
  have hβpos : (0 : ℝ) < (β : ℝ) := by
    rw [hβcoe]; exact mul_pos hbc (by linarith)
  have hβhalf : (M.betaCrit : ℝ) / 2 ≤ (β : ℝ) := by
    rw [hβcoe]; nlinarith [hchalf, hbc.le]
  have hβlt : β < M.betaCrit := by
    rw [← NNReal.coe_lt_coe, hβcoe]
    nlinarith [hclt, hbc]
  have hβne : M.uncutMean β ≠ ⊤ := hsub β hβlt
  have hKχ : K < (M.uncutMean β).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hK0 hβne).mp hgt
  have hden : 2 * M.α / (β : ℝ) ≤ 4 * M.α / (M.betaCrit : ℝ) := by
    have h1 : 2 * M.α / (β : ℝ) ≤ 2 * M.α / ((M.betaCrit : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hβhalf
    have h2 : 2 * M.α / ((M.betaCrit : ℝ) / 2) = 4 * M.α / (M.betaCrit : ℝ) := by
      field_simp
      norm_num
    linarith [h1, h2]
  have hden0 : 0 < 2 * M.α / (β : ℝ) := by positivity
  set T : ℝ := ((M.uncutMean β).toReal / (2 * M.α / (β : ℝ))) ^ (1 / M.α) with hT
  have hquot : P ^ M.α < (M.uncutMean β).toReal / (2 * M.α / (β : ℝ)) := by
    rw [lt_div_iff₀ hden0]
    calc P ^ M.α * (2 * M.α / (β : ℝ))
        ≤ P ^ M.α * (4 * M.α / (M.betaCrit : ℝ)) :=
          mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hP0.le _)
      _ = K := hK.symm
      _ < (M.uncutMean β).toReal := hKχ
  have hPT : P < T := by
    have hbase : (0 : ℝ) ≤ P := hP0.le
    rw [hT]
    calc P = (P ^ M.α) ^ (1 / M.α) := by
          rw [← Real.rpow_mul hbase M.α (1 / M.α),
            show M.α * (1 / M.α) = 1 by
              rw [mul_one_div, div_self (ne_of_gt hα)], Real.rpow_one]
      _ < _ := Real.rpow_lt_rpow (Real.rpow_nonneg hbase _) hquot (by positivity)
  have hBT : B < T := by
    have h1 : B < P := by rw [hP]; have := le_max_left B (1 : ℝ); linarith
    linarith
  have hle : T ≤ B := le_trans (le_max_right (1 : ℝ) T) (hB β hβlt)
  linarith


/-! ## The same statement at an arbitrary intensity

The paper's proof of Lemma I.4.9 says that "the derivation of (I.4.15) above can be carried
out at other values of `β ≤ β_c`".  The formal counterpart of that step is the identity
below: at *every* intensity the uncut mean is the supremum of the uncut means at the
strictly reduced intensities supplied by Definition I.1.5. -/

/-- The cutoff first moment at an intensity is nondecreasing in the cutoff radius. -/
theorem cutMassAtBeta_mono_radius (β : ℝ≥0) {r r' : ℝ} (h : r ≤ r') :
    M.cutMassAtBeta β r 0 ≤ M.cutMassAtBeta β r' 0 := by
  simp only [SourceModelData.cutMassAtBeta, longRangeMeasure]
  refine lintegral_clusterVol_mono (fun e => ?_) 0
  exact bernoulliEdgeProb_mono_kernel (M.cutKernel_mono h) (M.cutKernel_nonneg r)
    (M.cutKernel_nonneg r') β e

/-- **At every intensity, the cutoff means increase to the uncut mean.** -/
theorem iSup_cutMassAtBeta_radius_eq (β : ℝ≥0) :
    (⨆ r : ℝ, M.cutMassAtBeta β r 0) = M.uncutMean β := by
  simpa only [SourceModelData.cutMassAtBeta, SourceModelData.uncutMean,
    SourceModelData.cutKernel, SourceModelData.kernel, SourceModelData.law, pow_one] using
    iSup_lintegral_clusterVol_pow_cutRadialSym M.S M.K_antitone M.K_nonneg
      M.tendsto_K_atTop_zero β 0 1

/-- The transfer of Definition I.1.5 at an arbitrary intensity, in coefficient form. -/
theorem cutMassAtBeta_le_uncutMean_coeff {t0 r : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (hr : 0 < r) (β : ℝ≥0) :
    M.cutMassAtBeta β r 0 ≤ M.uncutMean (β * M.cutCoeffNN t0 r) :=
  M.cutMassAtBeta_le_uncutMean_mul (M.cutKernel_le_cutCoeffNN ht0 hlat hr) β

/-- **The reduced intensities are cofinal in `[0, β]`.**  Since the strict coefficient
tends to `1` (the profile `K` tends to `0` at infinity), every `β' < β` is below some
reduced intensity `β * c_r`. -/
theorem exists_cutCoeffNN_mul_ge {t0 : ℝ} (ht0 : 0 < t0) {β : ℝ≥0} (hβ : 0 < β)
    {β' : ℝ≥0} (hβ' : β' < β) :
    ∃ r : ℝ, 0 < r ∧ β' ≤ β * M.cutCoeffNN t0 r := by
  have hKt0 : 0 < M.K t0 := M.K_pos ht0
  have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hβ'R : (β' : ℝ) < (β : ℝ) := by exact_mod_cast hβ'
  have hδ : 0 < 1 - (β' : ℝ) / (β : ℝ) := by
    rw [sub_pos, div_lt_one hβR]; exact hβ'R
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (M.tendsto_K_atTop_zero.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 2 * M.K t0 * (1 - (β' : ℝ) / (β : ℝ)) by
        have := hKt0; nlinarith)))
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  have hr1 : (1 : ℝ) ≤ max R 1 := le_max_right _ _
  have hKr : M.K (max R 1) < 2 * M.K t0 * (1 - (β' : ℝ) / (β : ℝ)) :=
    hR _ (le_max_left R 1)
  have hquot : M.K (max R 1) / (2 * M.K t0) < 1 - (β' : ℝ) / (β : ℝ) := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hminle : min (1 / 2) (M.K (max R 1) / (2 * M.K t0)) ≤ 1 - (β' : ℝ) / (β : ℝ) :=
    le_trans (min_le_right _ _) hquot.le
  have hcoe : (M.cutCoeffNN t0 (max R 1) : ℝ)
      = 1 - min (1 / 2) (M.K (max R 1) / (2 * M.K t0)) :=
    M.coe_cutCoeffNN ht0 (lt_of_lt_of_le one_pos hr1)
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, hcoe]
  have hmul : (β : ℝ) * min (1 / 2) (M.K (max R 1) / (2 * M.K t0))
      ≤ (β : ℝ) * (1 - (β' : ℝ) / (β : ℝ)) :=
    mul_le_mul_of_nonneg_left hminle hβR.le
  have hdiv : (β : ℝ) * ((β' : ℝ) / (β : ℝ)) = (β' : ℝ) := by
    field_simp
  nlinarith [hmul, hdiv]

/-- **The uncut mean at any intensity is the supremum of the uncut means at the reduced
intensities** `β * c_r` of Definition I.1.5. -/
theorem uncutMean_eq_iSup_reduced_coeff (β : ℝ≥0) {t0 : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) :
    M.uncutMean β = ⨆ (r : ℝ) (_ : 0 < r), M.uncutMean (β * M.cutCoeffNN t0 r) := by
  have hb : (0 : ℝ≥0) ≤ β := zero_le
  have hbdd : ∀ r : ℝ, M.cutMassAtBeta β r 0 ≤
      ⨆ (r : ℝ) (_ : 0 < r), M.uncutMean (β * M.cutCoeffNN t0 r) := by
    intro r
    rcases le_or_gt r 0 with hr | hr
    · refine le_trans (M.cutMassAtBeta_mono_radius β (by linarith : r ≤ 1)) ?_
      exact le_trans (M.cutMassAtBeta_le_uncutMean_coeff ht0 hlat one_pos β)
        (le_iSup₂_of_le 1 one_pos le_rfl)
    · exact le_trans (M.cutMassAtBeta_le_uncutMean_coeff ht0 hlat hr β)
        (le_iSup₂_of_le r hr le_rfl)
  refine le_antisymm ?_ ?_
  · rw [← M.iSup_cutMassAtBeta_radius_eq β]
    exact iSup_le hbdd
  · refine iSup_le fun r => iSup_le fun _hr => ?_
    refine M.uncutMean_mono ?_
    calc β * M.cutCoeffNN t0 r ≤ β * 1 :=
          mul_le_mul_of_nonneg_left (M.cutCoeffNN_le_one t0 r) hb
      _ = β := mul_one β

/-- **Finiteness at an intensity is boundedness of the reduced means at that intensity.**
This is the lossless form of the Definition I.1.5 comparison: the reduced intensities are
all strictly smaller than `β`, they are cofinal in `[0, β]`, and yet a bound is needed
for all of them. -/
theorem uncutMean_ne_top_iff_exists_bdd_reduced_coeff (β : ℝ≥0) {t0 : ℝ} (ht0 : 0 < t0)
    (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) :
    M.uncutMean β ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ (r : ℝ), 0 < r → M.uncutMean (β * M.cutCoeffNN t0 r) ≤ C := by
  have hb : (0 : ℝ≥0) ≤ β := zero_le
  constructor
  · intro hfin
    exact ⟨_, hfin, fun r _hr => M.uncutMean_mono (by
      calc β * M.cutCoeffNN t0 r ≤ β * 1 :=
            mul_le_mul_of_nonneg_left (M.cutCoeffNN_le_one t0 r) hb
        _ = β := mul_one β)⟩
  · rintro ⟨C, hC, hbdd⟩
    rw [M.uncutMean_eq_iSup_reduced_coeff β ht0 hlat]
    exact ne_top_of_le_ne_top hC (iSup_le fun r => iSup_le fun hr => hbdd r hr)

/-- **The sharpness input below `β` is *equivalent* to finiteness of the reduced family at
`β`.**

Every reduced intensity `β * c_r` is strictly below `β`, so `hsub` below `β` gives all of
them finite; conversely the reduced intensities are cofinal in `[0, β]`, so if all of them
have finite mean then every `β' < β` does.  Together with
`uncutMean_ne_top_iff_exists_bdd_reduced_coeff` this pins down the difference between the
sharpness input below `β` and sharpness at `β`: it is exactly the uniformity in `r`. -/
theorem forall_lt_uncutMean_ne_top_iff_forall_reduced_ne_top {β : ℝ≥0} (hβ : 0 < β)
    {t0 : ℝ} (ht0 : 0 < t0) :
    (∀ β' : ℝ≥0, β' < β → M.uncutMean β' ≠ ⊤) ↔
      ∀ r : ℝ, 0 < r → M.uncutMean (β * M.cutCoeffNN t0 r) ≠ ⊤ := by
  constructor
  · intro h r hr
    refine h _ ?_
    have hclt : M.cutCoeffNN t0 r < 1 := M.cutCoeffNN_lt_one ht0 hr
    calc β * M.cutCoeffNN t0 r < β * 1 := mul_lt_mul_of_pos_left hclt hβ
      _ = β := mul_one β
  · intro h β' hβ'
    obtain ⟨r, hr, hle⟩ := M.exists_cutCoeffNN_mul_ge ht0 hβ hβ'
    exact ne_top_of_le_ne_top (h r hr) (M.uncutMean_mono hle)


/-- **The sharpness input a single time, in the shape of the bootstrap interface.**

`hsub` is *equivalent* to: at every strictly subcritical intensity the cutoff first moment
is bounded uniformly in the cutoff radius.  This is the pair `(hbdd, hmin)` of
`VolumeMoments.FirstMoment.first_moment_bound_all_beta`, i.e. the source's
"`r₀(β)` is finite for every `β_c/2 ≤ β < β_c`", stated as a single condition.  No
lattice-spacing or coefficient data is needed: the two sides are equivalent as they
stand. -/
theorem subcriticalFiniteMean_iff_forall_bdd_cutMassAtBeta :
    M.SubcriticalFiniteMean ↔
      ∀ β : ℝ≥0, β < M.betaCrit →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, M.cutMassAtBeta β r 0 ≤ C := by
  constructor
  · intro hsub β hβ
    refine ⟨M.uncutMean β, hsub β hβ, fun r => ?_⟩
    rcases le_or_gt 0 r with hr | hr
    · exact M.cutMassAtBeta_le_law hr 0
    · refine le_trans (M.cutMassAtBeta_mono_radius β (le_of_lt hr)) ?_
      exact M.cutMassAtBeta_le_law le_rfl 0
  · intro h β hβ
    obtain ⟨C, hC, hbdd⟩ := h β hβ
    rw [← M.iSup_cutMassAtBeta_radius_eq β]
    exact ne_top_of_le_ne_top hC (iSup_le hbdd)

end SourceModelData


namespace Witness

/-- **The named sharpness input is literally the `hsub` hypothesis of the staged
`SecondMoment/SourceWitness/Sharpness.lean`.**

The staged off-corner derivative consumes
`∀ β, β < β_c → ∫⁻ ω, clusterVol ω 0 ∂(law β) ≠ ⊤`; `SubcriticalFiniteMean` is that
statement with the integral abbreviated to `uncutMean`, so the two are the same
proposition by definition and everything proved for `SubcriticalFiniteMean` applies to the
staged hypothesis without restatement. -/
theorem sourceModelWitness_subcriticalFiniteMean_iff (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) :
    (sourceModelWitness d hd α hα).SubcriticalFiniteMean ↔
      ∀ β : ℝ≥0, β < (sourceModelWitness d hd α hα).betaCrit →
        (∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
          ∂((sourceModelWitness d hd α hα).law β)) ≠ ⊤ :=
  Iff.rfl

/-- At the witness, the sharpness input below `β_c` is equivalent to finiteness of the
uncut mean at the reduced intensities `β_c * c_r` of Definition I.1.5. -/
theorem sourceModelWitness_forall_lt_iff_reduced (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {t0 : ℝ} (ht0 : 0 < t0) (hβ : 0 < (sourceModelWitness d hd α hα).betaCrit) :
    (∀ β' : ℝ≥0, β' < (sourceModelWitness d hd α hα).betaCrit →
        (sourceModelWitness d hd α hα).uncutMean β' ≠ ⊤) ↔
      ∀ r : ℝ, 0 < r →
        (sourceModelWitness d hd α hα).uncutMean
          ((sourceModelWitness d hd α hα).betaCrit *
            (sourceModelWitness d hd α hα).cutCoeffNN t0 r) ≠ ⊤ :=
  (sourceModelWitness d hd α hα).forall_lt_uncutMean_ne_top_iff_forall_reduced_ne_top
    hβ ht0

end Witness

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit (every new theorem) -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMean_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_uncutMean
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutCoeff_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutCoeffNN_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.coe_cutCoeffNN
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.half_le_cutCoeffNN
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutCoeffNN_lt_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_le_cutCoeffNN
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_uncutMean_mul
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_mono_radius
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_cutMassAtBeta_radius_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAtBeta_le_uncutMean_coeff
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_cutCoeffNN_mul_ge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMean_eq_iSup_reduced_coeff
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMean_ne_top_iff_exists_bdd_reduced_coeff
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.forall_lt_uncutMean_ne_top_iff_forall_reduced_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_subcriticalFiniteMean_iff
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_forall_lt_iff_reduced
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.subcriticalFiniteMean_iff_forall_bdd_cutMassAtBeta
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMean_betaCrit_eq_iSup_reduced
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncutMean_betaCrit_ne_top_iff_exists_bdd_reduced
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_reduced_uncutMean_gt_of_betaCrit_eq_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.subcritical_finite_and_reduced_unbounded
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_bdd_sharpness_threshold_of_uncutMean_betaCrit_eq_top
