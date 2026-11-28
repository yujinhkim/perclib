/-
Ultramath swarm `smwzqts7r`, member `m7`, direction `d1` (G).
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m7.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m7/src/M7Residual.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Defs
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.Models.BinaryTree.Subcritical.Basic
public import PercLib.CriticalLRP.Models.BinaryTree.CriticalPoint.Defs
public import PercLib.CriticalLRP.Models.BinaryTree.CriticalPoint.CriticalPoint

/-!
# Direction G: the exact residual between subcritical finiteness, uncut critical mean
divergence, and radius-uniform cutoff control

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1:

* p. 6: `β_c := inf{β ≥ 0 : an infinite cluster exists P_β-a.s.}`;
* Proposition I.4.2 and p. 35, verbatim: "Since `E_{β_c}|K| = ∞`, it follows from Lemma
  I.4.5 and (I.4.6) that the identity (I.4.7) holds".

The source asserts `E_{β_c}|K_0| = ⊤` and never proves it.  Production's
`I420Case3/CriticalDivergence.lean` records that the assertion is weaker than the
two-sided power-law two-point lower bound `hlow` and reduces it to a spatially averaged
lower bound (`criticalDivergence_of_ballLower`), which the source's Theorem I.2.14 only
supplies for `α < 1` — not in the `d = 6`, `α = 2` Case 3 at issue.  What is missing is
therefore an exact statement of *which* model input the assertion is.

This file supplies four things, all kernel-checked.

## 1. The critical assertion is *equivalent* to two other formulations

* `criticalDivergence_iff_no_uniform_cutoff`: `E_{β_c}|K_0| = ⊤` iff for every extended
  constant `C ≠ ⊤` there is a radius `r` with `C < E_{β_c,r}|K_0|`.  This is the exact
  negation of "radius-uniform cutoff control" `∃ C, ∀ r, E_{β_c,r}|K_0| ≤ C`; the proof
  uses only production's `iSup_cutMoment_eq`, i.e. `E_{β_c}|K_0| = ⨆_r E_{β_c,r}|K_0|`.
* `subcriticalFinite_iff_forall_uniform_cutoff`: subcritical finiteness
  `∀ β < β_c, E_β|K_0| < ⊤` iff `∀ β < β_c` there is a constant, *depending on `β`*,
  bounding `E_{β,r}|K_0|` in `r`.

The two differ exactly in the order of the quantifiers `∀ β` and `∃ C`.  Nothing in the
model's data negotiates that swap, which is why the assertion has to be an input.

* `criticalDivergence_of_cutMassAt_asymptotic`: the first-moment regularity hypothesis
  `hP` that production carries through the Case-1/2/3 chains,
  `E_{β_c,r}|K_0| / ((α/β_c) r^α) → 1`, already *implies* `E_{β_c}|K_0| = ⊤`.  The paper
  uses the implication in the other direction (p. 35, from `E_{β_c}|K| = ∞` to (I.4.7)),
  and production's `first_moment_asymptotic_of_critical_divergence` supplies it *given its
  ODE package* (`hfin`, `hβ`, `hr₀`, `hderiv`, `hpos`, `hode`, `hmeas`, `hC`, `h0`).
  Hence: `hP ⟹ E_{β_c}|K| = ⊤` unconditionally (only `0 < β_c` is needed), and
  `E_{β_c}|K| = ⊤` + ODE package `⟹ hP`.  So no production chain that already assumes
  `hP` needs `E_{β_c}|K| = ∞` as a separate hypothesis.

## 2. The cited `n^{-1/2}` volume tail is *strictly weaker* than the assertion

`criticalVolumeTail_of_uncut_ne_top`: `E_{β_c}|K_0| < ⊤` implies the source's cited input
`M.CriticalVolumeTail C` for `C = (E_{β_c}|K_0|)`, by Markov plus `√n ≤ n`.  So
`CriticalVolumeTail` cannot be used to obtain `E_{β_c}|K_0| = ⊤` and citing it introduces
no circularity in the Case-3 chain, while it also does not replace the assertion.

## 3. The assertion is *attainable*, with a positive critical parameter

`exists_kernel_subcritical_finite_and_critical_divergence`, in the paper's own
`longRangeMeasure J hJ β` / `criticalBeta J hJ` interface, on the nonzero binary-tree
kernel of `Models/BinaryTree/Subcritical/Basic.lean`: `β_c = log 2 > 0`, the mean is finite
at every `β < β_c` and infinite at `β_c` itself.  So subcritical finiteness is strictly
weaker than finiteness at `β_c`, and the residual in item 1 is not vacuous.

## 4. The positive phase interface

`exists_lintegral_clusterVol_law_eq_top_of_betaCrit_lt`: for `β > β_c` some vertex has
infinite expected cluster volume, from `mem_of_criticalBeta_lt` (zero–one law) and
`exists_lintegral_eq_top_of_infiniteClusterProb_pos`.  This is the only direction of the
`θ`/mean relation that holds: percolation gives divergence, `θ = 0` gives nothing (item 3
and `M7BinaryTree`).

Not claimed: the assertion for the paper's power-law kernels on `ℤ^d`; the *root* form
`M.uncutMean β = ⊤` for `β > β_c` (only `∃ v` is proved — passing to the root is a
translation-invariance transfer of the radial kernel, not formalised here); and any
sharpness (β-uniform) statement.  Nothing here converts an upper spatial bound into a
lower one, and nothing infers a finite mean from `θ = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The cutoff moments at an arbitrary temperature -/

/-- The cutoff moments increase to the uncut moment at *every* temperature.  This is
production's `iSup_lintegral_clusterVol_pow_cutRadialSym` with `M.betaCrit` replaced by a
free `β`, which is what comparing critical and subcritical cutoff means needs. -/
theorem iSup_cutMomentAt_eq (β : ℝ≥0) (p : ℕ) :
    (⨆ r : ℝ, M.cutMomentAt β p r) =
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law β) :=
  iSup_lintegral_clusterVol_pow_cutRadialSym M.S M.K_antitone M.K_nonneg
    M.tendsto_K_atTop_zero β 0 p

/-- Each cutoff moment is below the uncut moment, at every temperature. -/
theorem cutMomentAt_le_uncut (β : ℝ≥0) (p : ℕ) (r : ℝ) :
    M.cutMomentAt β p r ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law β) := by
  rw [← M.iSup_cutMomentAt_eq β p]
  exact le_iSup (fun r : ℝ => M.cutMomentAt β p r) r

/-- **Radius-uniform cutoff control is equivalent to finiteness of the uncut moment**, at
every temperature and every order.  Both directions are exact; the forward one is the
`iSup` identity, the backward one is monotonicity. -/
theorem exists_uniform_cutoff_bound_iff_uncut_ne_top (β : ℝ≥0) (p : ℕ) :
    (∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, M.cutMomentAt β p r ≤ C) ↔
      (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law β)) ≠ ⊤ := by
  constructor
  · rintro ⟨C, hC, hle⟩
    rw [← M.iSup_cutMomentAt_eq β p]
    exact ne_top_of_le_ne_top hC (iSup_le hle)
  · intro h
    exact ⟨_, h, fun r => M.cutMomentAt_le_uncut β p r⟩

/-- **The exact negation form.**  The uncut moment is infinite exactly when no constant
bounds the cutoff moments in the radius: for every extended constant `C ≠ ⊤` some radius
beats it.  This is the precise sense in which critical divergence *is* the failure of a
radius-uniform cutoff envelope. -/
theorem uncut_eq_top_iff_forall_exists_lt_cutMomentAt (β : ℝ≥0) (p : ℕ) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(M.law β)) = ⊤ ↔
      ∀ C : ℝ≥0∞, C ≠ ⊤ → ∃ r : ℝ, C < M.cutMomentAt β p r := by
  rw [← M.iSup_cutMomentAt_eq β p]
  constructor
  · intro htop C hC
    by_contra hcon
    push Not at hcon
    exact hC (top_le_iff.mp (htop ▸ iSup_le hcon))
  · intro h
    by_contra hne
    obtain ⟨r, hr⟩ := h (⨆ r : ℝ, M.cutMomentAt β p r) hne
    exact absurd (le_iSup (fun r : ℝ => M.cutMomentAt β p r) r) (not_le.mpr hr)

/-! ## The three formulations at the critical point -/

/-- **Uncut critical mean divergence = no radius-uniform cutoff control.** -/
theorem criticalDivergence_iff_no_uniform_cutoff :
    (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw) = ⊤ ↔
      ∀ C : ℝ≥0∞, C ≠ ⊤ → ∃ r : ℝ, C < M.cutMoment 1 r := by
  have h := M.uncut_eq_top_iff_forall_exists_lt_cutMomentAt M.betaCrit 1
  simpa only [SourceModelData.cutMomentAt_betaCrit, SourceModelData.criticalLaw,
    SourceModelData.law, pow_one] using h

/-- **Subcritical finiteness = per-temperature radius-uniform cutoff control.**  Note the
quantifier order: the constant depends on `β`.  Compare
`criticalDivergence_iff_no_uniform_cutoff`, where the constant has to be beaten at *some*
radius, with no `β` left to vary. -/
theorem subcriticalFinite_iff_forall_uniform_cutoff :
    (∀ β : ℝ≥0, β < M.betaCrit → (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤) ↔
      ∀ β : ℝ≥0, β < M.betaCrit →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, M.cutMomentAt β 1 r ≤ C :=
  forall_congr' fun β => imp_congr_right fun _ =>
    (by simpa only [pow_one] using (M.exists_uniform_cutoff_bound_iff_uncut_ne_top β 1).symm)

/-! ## The source's cited `n^{-1/2}` volume tail is strictly weaker

Markov's inequality at the uncut critical law: `n · P(|K_0| ≥ n) ≤ E_{β_c}|K_0|`.  Note
that this is a *lower* bound on the mean from the tail, so it cannot be used in reverse:
it shows `CriticalVolumeTail` follows from finiteness of the critical mean, not the other
way round, and the envelope `C/√n` is genuinely weaker than the `C/n` that finiteness
produces. -/

/-- Markov's inequality for the uncut critical cluster volume. -/
theorem mul_measure_tail_le_lintegral (n : ℕ) :
    (n : ℝ≥0∞) * M.criticalLaw
        {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw := by
  set s : Set (Config M.V) := {ω | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} with hs
  have hmeas : MeasurableSet s :=
    measurableSet_le measurable_const (measurable_clusterVol (0 : M.V))
  calc (n : ℝ≥0∞) * M.criticalLaw s
      = ∫⁻ _ω in s, (n : ℝ≥0∞) ∂M.criticalLaw := (setLIntegral_const s _).symm
    _ ≤ ∫⁻ ω in s, clusterVol ω (0 : M.V) ∂M.criticalLaw := by
        have hmono : ∫⁻ _ω in s, (n : ℝ≥0∞) ∂M.criticalLaw
            ≤ ∫⁻ ω in s, clusterVol ω (0 : M.V) ∂M.criticalLaw :=
          setLIntegral_mono' hmeas fun _ω hω => hω
        exact hmono
    _ ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw := setLIntegral_le_lintegral s _

/-- Real-valued Markov: `P_{β_c}(|K_0| ≥ n) ≤ n^{-1} E_{β_c}|K_0|` when the mean is
finite. -/
theorem tailProb_le_uncut_toReal_div
    (h : (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw) ≠ ⊤) (n : ℕ) (hn : 1 ≤ n) :
    M.tailProb n ≤
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw).toReal / (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) * M.tailProb n ≤
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw).toReal := by
    have h2 := ENNReal.toReal_mono h (M.mul_measure_tail_le_lintegral n)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2
  rw [le_div_iff₀ hnpos]
  calc M.tailProb n * (n : ℝ) = (n : ℝ) * M.tailProb n := by ring
    _ ≤ (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw).toReal := h1

/-- **`E_{β_c}|K_0| < ⊤` implies the source's cited uncut volume-tail input**, with the
constant equal to the mean.  Since `√n ≤ n` for `n ≥ 1`, the cited envelope `C n^{-1/2}`
is weaker than the `C n^{-1}` that Markov produces, so the citation cannot be supplying the
critical-mean divergence the Case-3 chain uses alongside it. -/
theorem criticalVolumeTail_of_uncut_ne_top
    (h : (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw) ≠ ⊤) :
    M.CriticalVolumeTail
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw).toReal := by
  refine M.criticalVolumeTail_of_pointwise fun n hn => ?_
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt h1
    calc Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) * 1 := (mul_one _).symm
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  calc M.tailProb n
      ≤ (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw).toReal / (n : ℝ) :=
        M.tailProb_le_uncut_toReal_div h n hn
    _ ≤ (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw).toReal / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_left ENNReal.toReal_nonneg hsqrtpos hsqrt_le

/-! ## The positive phase interface: supercritical means are infinite -/

/-- **Throughout the percolating phase the mean cluster size is infinite.**  For `β > β_c`
the zero–one law gives an infinite cluster a.s. at `β`, hence some vertex has an infinite
cluster with positive probability, hence its expected cluster volume is `⊤`.  This is the
"positive phase interface" and it is the only direction of the `θ`/mean relation that
holds: it derives divergence from percolation, never finiteness from `θ = 0`. -/
theorem exists_lintegral_clusterVol_law_eq_top_of_betaCrit_lt
    (hne : (criticalBetaSet M.kernel M.kernel_nonneg).Nonempty) {β : ℝ≥0}
    (hβ : M.betaCrit < β) :
    ∃ v : M.V, ∫⁻ ω, clusterVol ω v ∂(M.law β) = ⊤ := by
  have hmem : β ∈ criticalBetaSet M.kernel M.kernel_nonneg :=
    mem_of_criticalBeta_lt hne hβ
  rw [mem_criticalBetaSet_iff] at hmem
  refine exists_lintegral_eq_top_of_infiniteClusterProb_pos M.kernel M.kernel_nonneg β ?_
  rw [hmem]
  exact one_pos

/-! ## `hP` already implies the critical divergence -/

/-- **The first-moment regularity input `hP` implies `E_{β_c}|K_0| = ⊤`.**  If the critical
cutoff mean is asymptotic to `(α/β_c) r^α` with `α > 0` and `β_c > 0`, it is unbounded, so
no radius-uniform constant bounds it, so by
`criticalDivergence_iff_no_uniform_cutoff` the uncut critical mean is `⊤`.

This is the direction *opposite* to the source's use on p. 35; together with
`first_moment_asymptotic_of_critical_divergence` it makes `hP` and `E_{β_c}|K| = ⊤`
interderivable given the rest of the Case-3 package, and it makes the divergence hypothesis
redundant in any chain that already assumes `hP`. -/
theorem criticalDivergence_of_cutMassAt_asymptotic (hβ : 0 < M.betaCrit)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
        / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    M.uncutMean M.betaCrit = ⊤ := by
  have hβc : (0 : ℝ) < (M.betaCrit : ℝ) := by exact_mod_cast hβ
  have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos M.hα hβc
  have hdiv : (∫⁻ ω, clusterVol ω (0 : M.V) ∂M.criticalLaw) = ⊤ := by
    refine M.criticalDivergence_iff_no_uniform_cutoff.mpr fun C hC => ?_
    have hev : ∀ᶠ r : ℝ in atTop, (1 / 2 : ℝ) ≤
        (M.cutMassAt r 0).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) :=
      hP.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    have hpow : Tendsto (fun r : ℝ => (1 / 2) * (M.α / (M.betaCrit : ℝ)) * r ^ M.α)
        atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) (tendsto_rpow_atTop M.hα)
    have hall : ∀ᶠ r : ℝ in atTop,
        C.toReal < (1 / 2) * (M.α / (M.betaCrit : ℝ)) * r ^ M.α ∧
          ((1 / 2 : ℝ) ≤ (M.cutMassAt r 0).toReal
              / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) ∧ 1 ≤ r) :=
      (hpow.eventually_gt_atTop C.toReal).and (hev.and (eventually_ge_atTop 1))
    obtain ⟨r, hrlt, hrle, hr1⟩ := hall.exists
    have hrp : 0 < r ^ M.α := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < r) _
    have hden : 0 < (M.α / (M.betaCrit : ℝ)) * r ^ M.α := by positivity
    have hle : (1 / 2) * ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)
        ≤ (M.cutMassAt r 0).toReal := (le_div_iff₀ hden).mp hrle
    have hlt : C.toReal < (1 / 2) * ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) := by
      nlinarith [hrlt]
    have hgt : C.toReal < (M.cutMassAt r 0).toReal := lt_of_lt_of_le hlt hle
    refine ⟨r, ?_⟩
    rw [← M.cutMassAt_zero_eq_cutMoment r]
    by_contra hcon
    push Not at hcon
    exact absurd (ENNReal.toReal_mono hC hcon) (not_le.mpr hgt)
  simpa only [SourceModelData.uncutMean, SourceModelData.criticalLaw] using hdiv

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP

/-- **Subcritical finiteness does not imply a finite critical mean**, in the paper's own
`longRangeMeasure J hJ β` interface, on the nonzero binary-tree kernel: `β_c = log 2 > 0`,
`E_β|K_0| < ⊤` for every `β < β_c`, and `E_{β_c}|K_0| = ⊤`.  So the residual isolated in
`SourceModelData.subcriticalFinite_iff_forall_uniform_cutoff` versus
`SourceModelData.criticalDivergence_iff_no_uniform_cutoff` is a genuine gap and not an
artefact of the formulation, and the assertion `E_{β_c}|K| = ∞` of the source has at least
one attained, non-degenerate instance. -/
theorem exists_kernel_subcritical_finite_and_critical_divergence :
    ∃ (J : Sym2 (List (Fin 2)) → ℝ) (hJ : ∀ e, 0 ≤ J e),
      (∀ β : ℝ≥0, β < criticalBeta J hJ →
        ∫⁻ ω, clusterVol ω ([] : List (Fin 2)) ∂longRangeMeasure J hJ β < ⊤) ∧
      (∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure J hJ (criticalBeta J hJ)) = ⊤ :=
  ⟨binaryTreeKernel, binaryTreeKernel_nonneg,
    fun β hβ => lintegral_clusterVol_lt_top_of_lt_criticalBeta β hβ,
    by rw [criticalBeta_binaryTreeKernel_eq_logTwo]
       exact lintegral_clusterVol_binaryTreeKernel_eq_top logTwo
         (le_of_eq treeProb_coe_logTwo.symm)⟩

end PercLib.CriticalLRP

/-! ## Axiom audit -/

section Audit

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_cutMomentAt_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMomentAt_le_uncut
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_uniform_cutoff_bound_iff_uncut_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.uncut_eq_top_iff_forall_exists_lt_cutMomentAt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalDivergence_iff_no_uniform_cutoff
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.subcriticalFinite_iff_forall_uniform_cutoff
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.mul_measure_tail_le_lintegral
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tailProb_le_uncut_toReal_div
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_of_uncut_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_lintegral_clusterVol_law_eq_top_of_betaCrit_lt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalDivergence_of_cutMassAt_asymptotic
#print axioms PercLib.CriticalLRP.exists_kernel_subcritical_finite_and_critical_divergence
end Audit
