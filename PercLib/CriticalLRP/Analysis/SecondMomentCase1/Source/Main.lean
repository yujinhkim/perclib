/-
Ultramath swarm `smwznoz6j`, member `m4`, direction `d5`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m4.
Production base `a42ae967cb8649dffa6f108a7a474602dd8a0d76`; reviewed scratch source `.scratch/review-smwznoz6j/m4/CaseOneNoRadial.lean`.

# Proposition I.4.15, Case 1 (`d > 3α`): the consumer on the paper's own inputs

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, p. 42 and p. 44.
Proposition I.4.15 states: if any of the three conditions of Proposition I.4.2 hold then
`r ↦ E_{β_c,r}|K|²` is regularly varying of index `3α`; if moreover `d > 3α` (or the
triangle condition holds and `∇_r` is logarithmically integrable) then
`E_{β_c,r}|K|² ~ A r^{3α}` for some constant `A`.

Production `PercLib.CriticalLRP.Analysis.SecondMomentCase1` closes Case 1 modulo four
*radial/bookkeeping* hypotheses (`hac`, `hae`, `h1`, `hmeasE2`, `hmeasEbar`, plus `hmR` for the
`regularlyVarying` variant) and the redundancy `hβ`, `hκ`.  Those are not model assumptions:

* `hac`, `hae`, `hmR` are the radial regularity of `r ↦ (M.cutMoment 2 r).toReal`; production
  `PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.ac_and_ae_toReal_two_farTail` derives them from tail finiteness of
  the second cutoff moment alone (the window family it needs is constructed from countability of
  `M.V`);
* `h1` follows from `h2` (`SourceModelData.cutMoment_one_ne_top_of_two`);
* `hmeasE2`, `hmeasEbar` follow from `h1`, `h2`
  (`SourceModelData.measurable_p2ExclError_of_tail`, `measurable_p2Ebar_of_tail`), and `hmR` from
  `h2` (`measurable_rhsScalarTwo_of_tail`);
* `hβ` follows from `hP` (`SourceModelData.betaCrit_coe_ne_zero_of_hP`) and `hκ` from `hα`, `hβ`;
* `hE0log` is production `SourceModelData.logIntegrable_cutE0'`, with no hypotheses.

So the missing Case-1 assembly is the one that deletes them.  This file supplies it:

* `eventually_window_ratio_le_rpow_of_firstMomentUpper`,
  `eventually_p2ExclError_le_rpow_of_firstMomentUpper`,
  `p2ExclError_tendsto_zero_of_firstMomentUpper`,
  `logarithmicallyIntegrable_p2ExclError_of_firstMomentUpper` — the paper's Case-1 `⪯` chain
  runs on the **one-sided** bound `E_{β_c,r}|K| ≤ C r^α` alone, at the explicit constant
  `15 C³ 2^d`; neither the exact asymptotic `E_{β_c,r}|K| ~ (α/β_c) r^α`, nor a lower bound on
  `E_{β_c,r}|K|`, nor `β_c` itself is used;
* `tendsto_div_two_of_caseOne_no_ac`, `regularlyVarying_two_of_caseOne_no_ac` — Case 1 of
  Proposition I.4.15 with all six radial/bookkeeping inputs and the two redundant inputs deleted
  and nothing added: the retained inputs are `hα`, `h3α`, tail finiteness of the second cutoff
  moment, the first-moment asymptotic `hP`, and (for the `∼ A r^{3α}` branch) the
  log-integrability of the first-moment error `H_r` from Proposition I.4.2;
* `momentGap_of_caseOne_no_ac` — the Case-3 moment-gap input `hgm` is a *consequence* of Case 1,
  so in Case 1 it is not an independent hypothesis.

No `sorry`, `admit`, `native_decide`, `sorryAx` or custom axiom; no hypothesis asserts any part
of a conclusion.  Everything the paper's Case 1 asks for is retained at its own strength.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase1
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.ACAE
public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Consumers
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.MomentGapAudit.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.FiniteMoments.Main
public import PercLib.CriticalLRP.Analysis.TriangleAverage
public import PercLib.CriticalLRP.Analysis.SecondMomentCase1.Source.Defs

/-! # Case 1 of Proposition I.4.15 without the radial and bookkeeping inputs -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace CaseOne

open Orchestration

/-! ## 1. The Case-1 `⪯` chain from a one-sided first-moment bound

The paper's display in Case 1 is

```
  E_{2,r} ⪯ (E_{β_c,r}|K|)³ / |B_r| ⪯ r^{3α-d},
```

and the accepted `eventually_window_ratio_le_rpow` proves the second `⪯` from the two-sided
asymptotic `hP`.  Only the upper half of `hP` is used, so the bound below takes it as an explicit
one-sided inequality at a constant `C`.  The constants are exactly the accepted ones, with
`(α/β_c)³` replaced by `C³`. -/

/-- **The Case-1 window ratio from a one-sided first-moment bound.**
`15 (E_{β_c,r}|K|)³ / |B_r| ⪯ 15 C³ 2^d r^{3α-d}` whenever `E_{β_c,r}|K| ≤ C r^α` eventually.

The two ingredients are the accepted first-moment ratio `p2ExclError_le_caseOne` (which cancels
`(E|K|)²` exactly) and the landed lattice-ball lower sandwich
`TriangleAverage.eventually_pow_div_ncard_le`, `r^d/|B_r| ≤ 2^d`. -/
theorem eventually_window_ratio_le_rpow_of_firstMomentUpper (M : SourceModelData) {C : ℝ}
    (hC : 0 ≤ C) (hup : M.FirstMomentUpperAt C) :
    ∀ᶠ r : ℝ in atTop, 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
      ≤ 15 * C ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
  have hrpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  have hball := TriangleAverage.eventually_pow_div_ncard_le M
  filter_upwards [hup, hball, hrpos] with r hupr hballr hr
  have hbpos : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast SourceModelData.ball_ncard_pos M r hr.le
  have hpow : (0 : ℝ) < r ^ (3 * M.α - M.d) := Real.rpow_pos_of_pos hr _
  have hcube : (M.cutMoment 1 r).toReal ^ 3 ≤ (C * r ^ M.α) ^ 3 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg hupr 3
  have hstep : 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
      ≤ 15 * (C * r ^ M.α) ^ 3 / ((M.ball r).ncard : ℝ) := by
    have h1 : (0 : ℝ) ≤ 15 * (M.cutMoment 1 r).toReal ^ 3 := by positivity
    have h2 : (0 : ℝ) ≤ 15 * (C * r ^ M.α) ^ 3 := by positivity
    exact div_le_div_of_nonneg_right (by linarith) hbpos.le
  have hrpow3 : (r ^ M.α) ^ 3 = r ^ (3 * M.α) := by
    rw [← Real.rpow_natCast (r ^ M.α) 3, ← Real.rpow_mul hr.le]
    push_cast
    ring_nf
  have hid : 15 * (C * r ^ M.α) ^ 3 / ((M.ball r).ncard : ℝ)
      = 15 * C ^ 3 * (r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)) := by
    rw [mul_pow, hrpow3]
    field_simp
  have hrate : r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)
      ≤ (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
    have hsplit : r ^ (3 * M.α) = r ^ (3 * M.α - M.d) * r ^ M.d := by
      rw [← Real.rpow_natCast r M.d, ← Real.rpow_add hr,
        show 3 * M.α - (M.d : ℝ) + (M.d : ℝ) = 3 * M.α by ring]
    calc r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)
        = r ^ (3 * M.α - M.d) * (r ^ M.d / ((M.ball r).ncard : ℝ)) := by
          rw [hsplit]
          field_simp
      _ ≤ r ^ (3 * M.α - M.d) * (2 : ℝ) ^ M.d :=
          mul_le_mul_of_nonneg_left hballr hpow.le
      _ = (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by ring
  calc 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
      ≤ 15 * (C * r ^ M.α) ^ 3 / ((M.ball r).ncard : ℝ) := hstep
    _ = 15 * C ^ 3 * (r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)) := hid
    _ ≤ 15 * C ^ 3 * ((2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d)) :=
        mul_le_mul_of_nonneg_left hrate (by positivity)
    _ = 15 * C ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by ring

/-- **The Case-1 rate for the excluded second-moment error from a one-sided first-moment bound**:
`E_{2,r} ≤ 15 C³ 2^d r^{3α-d}` eventually. -/
theorem eventually_p2ExclError_le_rpow_of_firstMomentUpper (M : SourceModelData) {C : ℝ}
    (hC : 0 ≤ C) (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hup : M.FirstMomentUpperAt C) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ 15 * C ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
  filter_upwards [eventually_window_ratio_le_rpow_of_firstMomentUpper M hC hup,
    eventually_ge_atTop (0 : ℝ), h2] with r hw hr h2r
  exact (p2ExclError_le_caseOne M hr h2r).trans hw

/-- **`E_{2,r} → 0` in Case 1 from a one-sided first-moment bound.**  The hypothesis `3α < d`
is the paper's Case-1 condition; no lower bound on `E_{β_c,r}|K|` is used. -/
theorem p2ExclError_tendsto_zero_of_firstMomentUpper (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) (hup : M.FirstMomentUpperAt C) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hg : Tendsto (fun r : ℝ =>
      15 * C ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d)) atTop (𝓝 0) := by
    have h := (TriangleAverage.tendsto_rpow_neg_atTop_zero
      (a := 3 * M.α - M.d) (by linarith)).const_mul
      (15 * C ^ 3 * (2 : ℝ) ^ M.d)
    simpa only [mul_zero] using h
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (0 : ℝ), h2] with r hr h2r
    exact SourceModelData.p2ExclError_nonneg M r hr h2r
  · exact eventually_p2ExclError_le_rpow_of_firstMomentUpper M hC h2 hup

/-- **`E_{2,r}` is logarithmically integrable in Case 1 from a one-sided first-moment bound**:
`∫^∞ E_{2,r} dr/r ≤ ∫^∞ 15 C³ 2^d r^{3α-d-1} dr < ∞`. -/
theorem logarithmicallyIntegrable_p2ExclError_of_firstMomentUpper (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) (hup : M.FirstMomentUpperAt C) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 h2
  set r₁ : ℝ := max R₀ 1 with hr₁def
  have h2' : ∀ t : ℝ, r₁ ≤ t → M.cutMoment 2 t ≠ ⊤ := fun t ht =>
    hR₀ t (le_trans (le_max_left R₀ 1) ht)
  have h1' : ∀ t : ℝ, r₁ ≤ t → M.cutMoment 1 t ≠ ⊤ := fun t ht =>
    M.cutMoment_one_ne_top_of_two (h2' t ht)
  have hmeas : Measurable M.p2ExclError :=
    SourceModelData.measurable_p2ExclError_of_tail M h1' h2'
  have hb : ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ 15 * C ^ 3 * (2 : ℝ) ^ M.d * r ^ (-((M.d : ℝ) - 3 * M.α)) := by
    filter_upwards [eventually_p2ExclError_le_rpow_of_firstMomentUpper M hC h2 hup] with r hr
    simpa only [neg_sub] using hr
  have hnn : ∀ᶠ r : ℝ in atTop, 0 ≤ M.p2ExclError r := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), h2] with r hr h2r
    exact SourceModelData.p2ExclError_nonneg M r hr h2r
  exact ⟨hmeas, Analysis.integrableOn_abs_div_of_eventually_le_rpow_neg hmeas (by linarith) hnn hb⟩


/-! ## 2. Case 1 of Proposition I.4.15 with the radial and bookkeeping inputs discharged

`tendsto_div_two_of_caseOne_reduced` still takes `hac`, `hae`, `h1`, `hmeasE2`, `hmeasEbar`,
`hβ` and `hκ`.  None of them is a model assumption:

* `hac`, `hae` are produced by the far-tail radius calculus
  `PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.ac_and_ae_toReal_two_farTail`, whose only non-model input (a
  monotone edge-exhausting window family) is constructed from countability of `M.V`;
* `h1` is `h2`'s first moment (`SourceModelData.cutMoment_one_ne_top_of_two`);
* `hmeasE2`, `hmeasEbar` are `SourceModelData.measurable_p2ExclError_of_tail` /
  `measurable_p2Ebar_of_tail` applied to `h1`, `h2`, and `hmR` is
  `SourceModelData.measurable_rhsScalarTwo_of_tail`;
* `hβ` is forced by `hP` (`SourceModelData.betaCrit_coe_ne_zero_of_hP`) and `hκ` follows from
  `hα > 0` and `β_c > 0`.

The base point `r₀` is quantified existentially, because the conclusion is a limit at infinity. -/

/-- **Case 1 of Proposition I.4.15, `E_{β_c,r}|K|² ∼ A r^{3α}`, without radial inputs.**

Retained inputs: `0 < α`, the Case-1 hypothesis `3α < d`, tail finiteness of the second cutoff
moment, the first-moment asymptotic `hP` of Proposition I.4.2, and log-integrability of the
first-moment error `H_r`.  `hac`, `hae`, `h1`, `hβ`, `hκ`, `hmeasE2`, `hmeasEbar` are deleted and
nothing is added. -/
theorem tendsto_div_two_of_caseOne_no_ac (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨r₁, hAE⟩ := PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.ac_and_ae_toReal_two_farTail M
  obtain ⟨R, hR⟩ := eventually_atTop.1 h2
  set r₀ : ℝ := max r₁ (max R 1) with hr₀def
  have hRle : R ≤ r₀ := le_trans (le_max_left R 1) (le_max_right r₁ (max R 1))
  have h1le : (1 : ℝ) ≤ r₀ := le_trans (le_max_right R 1) (le_max_right r₁ (max R 1))
  have hr₀ : 0 < r₀ := lt_of_lt_of_le zero_lt_one h1le
  have h2' : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤ := fun t ht => hR t (le_trans hRle ht)
  have h1' : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤ := fun t ht =>
    M.cutMoment_one_ne_top_of_two (h2' t ht)
  obtain ⟨hac, hae⟩ := hAE (le_max_left r₁ (max R 1)) hr₀ h2'
  have hβ : (M.betaCrit : ℝ) ≠ 0 := M.betaCrit_coe_ne_zero_of_hP hP
  have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos hα (M.betaCrit_coe_pos hβ)
  exact tendsto_div_two_of_caseOne_reduced M hα hr₀ hβ h3α hκ hac hae h1' h2' hP hHlog
    (M.measurable_p2ExclError_of_tail h1' h2') (M.measurable_p2Ebar_of_tail hα h1' h2')

/-- **Case 1 of Proposition I.4.15, regular variation of index `3α`, without radial inputs.**
This is the first clause of the proposition in Case 1: it needs no log-integrability input, only
`hP` (for `H_r → 0`) and `E_{2,r} → 0` (supplied by Case 1's `d > 3α` rate). -/
theorem regularlyVarying_two_of_caseOne_no_ac (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  obtain ⟨r₁, hAE⟩ := PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.ac_and_ae_toReal_two_farTail M
  obtain ⟨R, hR⟩ := eventually_atTop.1 h2
  set r₀ : ℝ := max r₁ (max R 1) with hr₀def
  have hRle : R ≤ r₀ := le_trans (le_max_left R 1) (le_max_right r₁ (max R 1))
  have h1le : (1 : ℝ) ≤ r₀ := le_trans (le_max_right R 1) (le_max_right r₁ (max R 1))
  have hr₀ : 0 < r₀ := lt_of_lt_of_le zero_lt_one h1le
  have h2' : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤ := fun t ht => hR t (le_trans hRle ht)
  have h1' : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤ := fun t ht =>
    M.cutMoment_one_ne_top_of_two (h2' t ht)
  obtain ⟨hac, hae⟩ := hAE (le_max_left r₁ (max R 1)) hr₀ h2'
  have hβ : (M.betaCrit : ℝ) ≠ 0 := M.betaCrit_coe_ne_zero_of_hP hP
  have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos hα (M.betaCrit_coe_pos hβ)
  exact regularlyVarying_two_of_caseOne M hα hr₀ hβ h3α hκ hac
    (M.measurable_rhsScalarTwo_of_tail h2') hae h1' h2' hP

/-! ## 3. Case 1 yields `E_{β_c,r}|K|² ≍ (E_{β_c,r}|K|)³`

The paper uses the two-sided comparability `E_r|K|² ≍ (E_r|K|)³` ("by Proposition I.4.15") later
in the argument.  In Case 1 it is a consequence of the two asymptotic statements: `hP` pins the
first moment at scale `r^α` and the Case-1 conclusion pins the second at scale `r^{3α}`, so their
ratio is bounded above and below by positive constants.  The lower half is the Case-3 moment-gap
input `hgm`; the upper half is the opposite inequality, which uses the *lower* bound of `hP` and is
therefore **not** available from the one-sided Case-1 chain of section 1. -/

/-- **`E_{β_c,r}|K|² ≍ (E_{β_c,r}|K|)³` in Case 1.**  Two positive constants `c`, `C` with
`c (E|K|)³ ≤ E|K|² ≤ C (E|K|)³` eventually. -/
theorem exists_cube_comparable_of_caseOne_no_ac (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      c * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal ∧
        (M.cutMoment 2 r).toReal ≤ C * (M.cutMassAt r 0).toReal ^ 3 := by
  obtain ⟨A, hA, hT⟩ := tendsto_div_two_of_caseOne_no_ac M hα h3α h2 hP hHlog
  have hβ : (M.betaCrit : ℝ) ≠ 0 := M.betaCrit_coe_ne_zero_of_hP hP
  set T : ℝ := (M.α / (M.betaCrit : ℝ)) / 2 with hTdef
  have hT0 : 0 < T := by
    rw [hTdef]
    exact div_pos (div_pos hα (M.betaCrit_coe_pos hβ)) (by norm_num)
  have hsand : ∀ᶠ r : ℝ in atTop,
      T * r ^ M.α ≤ (M.cutMassAt r 0).toReal ∧
        (M.cutMassAt r 0).toReal ≤ 3 * T * r ^ M.α := by
    filter_upwards [M.eventually_sandwich_cutMassAt hα hβ hP] with r hr
    rw [hTdef]
    constructor
    · exact hr.1
    · linarith [hr.2]
  have hlow : ∀ᶠ r : ℝ in atTop, A / 2 * r ^ (3 * M.α) ≤ (M.cutMoment 2 r).toReal := by
    filter_upwards [hT (isOpen_Ioi.mem_nhds (by linarith : A / 2 < A)),
      eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hp : (0 : ℝ) < r ^ (3 * M.α) := Real.rpow_pos_of_pos hr0 _
    exact le_of_lt ((lt_div_iff₀ hp).1 hr)
  have hupp : ∀ᶠ r : ℝ in atTop, (M.cutMoment 2 r).toReal ≤ 2 * A * r ^ (3 * M.α) := by
    filter_upwards [hT (isOpen_Iio.mem_nhds (by linarith : A < 2 * A)),
      eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hp : (0 : ℝ) < r ^ (3 * M.α) := Real.rpow_pos_of_pos hr0 _
    exact le_of_lt ((div_lt_iff₀ hp).1 hr)
  refine ⟨(A / 2) / (27 * T ^ 3), (2 * A) / T ^ 3, by positivity, by positivity, ?_⟩
  filter_upwards [hsand, hlow, hupp, eventually_ge_atTop (1 : ℝ)] with r hs hl hu hr1
  have hr : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
  have hcu : T ^ 3 * r ^ (3 * M.α) ≤ (M.cutMassAt r 0).toReal ^ 3 := by
    have h := pow_le_pow_left₀ (mul_nonneg hT0.le (Real.rpow_pos_of_pos hr M.α).le) hs.1 3
    rwa [mul_pow, Case3MomentGapAudit.rpow_cube_eq hr] at h
  have hco : (M.cutMassAt r 0).toReal ^ 3 ≤ 27 * T ^ 3 * r ^ (3 * M.α) := by
    have h := pow_le_pow_left₀ ENNReal.toReal_nonneg hs.2 3
    have h3 : (3 * T * r ^ M.α) ^ 3 = 27 * T ^ 3 * r ^ (3 * M.α) := by
      rw [mul_pow, mul_pow, Case3MomentGapAudit.rpow_cube_eq hr]
      ring
    rwa [h3] at h
  constructor
  · have hstep : (A / 2) * (M.cutMassAt r 0).toReal ^ 3
        ≤ 27 * T ^ 3 * (M.cutMoment 2 r).toReal := by
      have h1 : (A / 2) * (M.cutMassAt r 0).toReal ^ 3
          ≤ (A / 2) * (27 * T ^ 3 * r ^ (3 * M.α)) :=
        mul_le_mul_of_nonneg_left hco (by linarith)
      have h2 : (A / 2) * (27 * T ^ 3 * r ^ (3 * M.α))
          = 27 * T ^ 3 * (A / 2 * r ^ (3 * M.α)) := by ring
      have h3 : 27 * T ^ 3 * (A / 2 * r ^ (3 * M.α))
          ≤ 27 * T ^ 3 * (M.cutMoment 2 r).toReal :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      linarith [h1, h3]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 27 * T ^ 3)]
    linarith [hstep]
  · have hstep : T ^ 3 * (M.cutMoment 2 r).toReal
        ≤ 2 * A * (M.cutMassAt r 0).toReal ^ 3 := by
      have h1 : T ^ 3 * (M.cutMoment 2 r).toReal ≤ T ^ 3 * (2 * A * r ^ (3 * M.α)) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      have h2 : T ^ 3 * (2 * A * r ^ (3 * M.α)) = 2 * A * (T ^ 3 * r ^ (3 * M.α)) := by ring
      have h3 : 2 * A * (T ^ 3 * r ^ (3 * M.α)) ≤ 2 * A * (M.cutMassAt r 0).toReal ^ 3 :=
        mul_le_mul_of_nonneg_left hcu (by linarith)
      linarith [h1, h3]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < T ^ 3)]
    linarith [hstep]

/-- **The Case-3 moment-gap input `hgm` is a consequence of Case 1.**  In Case 1 of Proposition
I.4.15 the moment gap is not an independent hypothesis: the second moment's asymptotic and the
first moment's asymptotic force `(E|K|)³ ⪯ E|K|²`. -/
theorem momentGap_of_caseOne_no_ac (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    M.MomentGap := by
  obtain ⟨A, hA, hT⟩ := tendsto_div_two_of_caseOne_no_ac M hα h3α h2 hP hHlog
  exact M.momentGap_of_tendsto_normalized hα (M.betaCrit_coe_ne_zero_of_hP hP) hP hA hT

/-! ## 4. Fidelity checks

Two checks that section 1 is a genuine weakening of the accepted Case-1 chain rather than a
different statement:

* `firstMomentUpperAt_of_hP` — the accepted first-moment asymptotic `hP` *implies* the one-sided
  bound, at the constant `2 (α/β_c)`, so nothing is lost and section 1 applies to every model
  satisfying the accepted hypotheses;
* `eventually_p2ExclError_le_rpow_recovered` — instantiating section 1 at that constant reproduces
  the accepted `eventually_p2ExclError_le_rpow` rate `15 · 8 · (α/β_c)³ · 2^d · r^{3α-d}`
  *exactly*, constants included. -/

/-- **The accepted first-moment asymptotic implies the one-sided bound** at the constant
`2 (α/β_c)`: the upper half of `eventually_sandwich_cutMassAt`, with `3/2` sharpened to `2` by
reading the limit at `2` directly. -/
theorem firstMomentUpperAt_of_hP (M : SourceModelData) (hα : 0 < M.α)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    M.FirstMomentUpperAt (2 * (M.α / (M.betaCrit : ℝ))) := by
  have hβ : (M.betaCrit : ℝ) ≠ 0 := M.betaCrit_coe_ne_zero_of_hP hP
  have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos hα (M.betaCrit_coe_pos hβ)
  have hlt : ∀ᶠ r : ℝ in atTop,
      (M.cutMassAt r 0).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) < 2 :=
    (tendsto_order.1 hP).2 2 (by norm_num)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hpos : (0 : ℝ) < (M.α / (M.betaCrit : ℝ)) * r ^ M.α :=
    mul_pos hκ (Real.rpow_pos_of_pos hr0 M.α)
  have heq : (M.cutMassAt r 0).toReal = (M.cutMoment 1 r).toReal := by
    rw [SourceModelData.cutMassAt_zero_eq_cutMoment]
  rw [heq, div_lt_iff₀ hpos] at hr
  change (M.cutMoment 1 r).toReal ≤ 2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α
  linarith [hr]

/-- **Constant fidelity**: the one-sided Case-1 chain, instantiated at the accepted first-moment
asymptotic, gives back `eventually_p2ExclError_le_rpow` with the accepted constant
`15 · 8 · (α/β_c)³ · 2^d`, exactly. -/
theorem eventually_p2ExclError_le_rpow_recovered (M : SourceModelData) (hα : 0 < M.α)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
  have hβ : (M.betaCrit : ℝ) ≠ 0 := M.betaCrit_coe_ne_zero_of_hP hP
  have hκ : 0 ≤ M.α / (M.betaCrit : ℝ) := (div_pos hα (M.betaCrit_coe_pos hβ)).le
  have hup := firstMomentUpperAt_of_hP M hα hP
  have hkey : 15 * (2 * (M.α / (M.betaCrit : ℝ))) ^ 3 * (2 : ℝ) ^ M.d
      = 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d := by ring
  filter_upwards [eventually_p2ExclError_le_rpow_of_firstMomentUpper M (C :=
    2 * (M.α / (M.betaCrit : ℝ))) (by positivity) h2 hup] with r hr
  rw [hkey] at hr
  exact hr

/-- **Proposition I.4.15 in Case 1 (`d > 3α`), both clauses, without radial inputs.**  Regular
variation of index `3α` together with the existence of the constant `A` in
`E_{β_c,r}|K|² ∼ A r^{3α}`. -/
theorem propositionI415_caseOne_no_ac (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) ∧
      ∃ A : ℝ, 0 < A ∧ Tendsto
        (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  ⟨regularlyVarying_two_of_caseOne_no_ac M hα h3α h2 hP,
    tendsto_div_two_of_caseOne_no_ac M hα h3α h2 hP hHlog⟩

/-! ## 5. Case 1 on the paper's own hypotheses

The last remaining bookkeeping input of section 2 is `h2`, tail finiteness of the second cutoff
moment.  It is not independent either: production
`SourceModelData.cutoffSecondMomentsFinite_of_firstMoment_asymptotic` derives it from `hP` alone
(the uniform lower comparison `χ(r) ⪰ r^α` gives `(M.cutMassAt r 0).toReal > 0`, hence
`≠ ⊤`, and finiteness of the first cutoff moment gives every higher one).

After that deletion the retained inputs of Case 1 of Proposition I.4.15 are exactly the paper's:

* `hα : 0 < α`;
* `h3α : 3α < d` — the Case-1 condition of Proposition I.4.15;
* `hP` — the first assertion of Proposition I.4.2 in Case 1, `E_{β_c,r}|K| ∼ (α/β_c) r^α`;
* `hHlog` — the second assertion of Proposition I.4.2 in Case 1, log-integrability of
  `H_r = (β_c/α) r^{-α} E_{β_c,r}|K| − 1`.

Nothing else. -/

/-- **`h2` is not an independent Case-1 input**: the first-moment asymptotic forces finiteness of
the second cutoff moment on a tail. -/
theorem eventually_cutMoment_two_ne_top_of_hP (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤ :=
  eventually_atTop.2 ⟨1, fun t ht =>
    M.cutoffSecondMomentsFinite_of_firstMoment_asymptotic hP 1 t ht⟩

/-- **Proposition I.4.15, Case 1 (`d > 3α`), on the paper's own hypotheses:
`E_{β_c,r}|K|² ∼ A r^{3α}`.** -/
theorem tendsto_div_two_of_caseOne_source (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  tendsto_div_two_of_caseOne_no_ac M hα h3α
    (eventually_cutMoment_two_ne_top_of_hP M hP) hP hHlog

/-- **Proposition I.4.15, Case 1, regular variation of index `3α`, on the paper's own
hypotheses** (no log-integrability input is needed for this clause). -/
theorem regularlyVarying_two_of_caseOne_source (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  regularlyVarying_two_of_caseOne_no_ac M hα h3α
    (eventually_cutMoment_two_ne_top_of_hP M hP) hP

/-- **Both clauses of Proposition I.4.15 in Case 1 (`d > 3α`), on the paper's own
hypotheses.**  This is the exact content of `tendsto_div_two_of_caseOne_source` together with
`regularlyVarying_two_of_caseOne_source`. -/
theorem propositionI415_caseOne_source (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) ∧
      ∃ A : ℝ, 0 < A ∧ Tendsto
        (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  ⟨regularlyVarying_two_of_caseOne_source M hα h3α hP,
    tendsto_div_two_of_caseOne_source M hα h3α hP hHlog⟩

/-- **`E_{β_c,r}|K|² ≍ (E_{β_c,r}|K|)³` in Case 1, on the paper's own hypotheses**, and hence
`∃ c C > 0`, `c (E|K|)³ ≤ E|K|² ≤ C (E|K|)³` eventually.  The lower half alone is the Case-3
moment-gap input `hgm`, which is therefore not an independent input in Case 1. -/
theorem exists_cube_comparable_of_caseOne_source (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      c * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal ∧
        (M.cutMoment 2 r).toReal ≤ C * (M.cutMassAt r 0).toReal ^ 3 :=
  exists_cube_comparable_of_caseOne_no_ac M hα h3α
    (eventually_cutMoment_two_ne_top_of_hP M hP) hP hHlog

/-- **The case-3 moment gap `hgm` in Case 1, on the paper's own hypotheses.** -/
theorem momentGap_of_caseOne_source (M : SourceModelData) (hα : 0 < M.α)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H) :
    M.MomentGap :=
  momentGap_of_caseOne_no_ac M hα h3α (eventually_cutMoment_two_ne_top_of_hP M hP) hP hHlog

end CaseOne
end PercLib.CriticalLRP
