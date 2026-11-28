/-
Ultramath swarm `smwzlje3f`, member `m1`, direction `d7`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m1/Audit.lean`.

# Audit of the Case-3 moment gap: normalisation, non-vacuity, circularity

Production `5d2d681` closes the Case-3 numerator of Proposition I.4.15 from the proved `(2,1)`
product gap and leaves, among the paper's own inputs, the moment gap

```
{c3 : ℝ} (hc3 : 0 < c3)
  (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
```

This file audits exactly that input.  Nothing here reproves or replaces any production
consumer; the results are statements about the *shape and strength* of `hgm`.

* `momentGap_iff_secondMomentLower` — normalisation: under the retained first-moment
  asymptotic `hP`, `hgm` is **equivalent** to a power lower bound `c r^{3α} ≤ E_{β_c,r}|K|²`
  at large `r`, which is the source's own displayed conclusion
  `(E_{β_c,r}|K|)³ ⪰ r^{3α}` (p. 47).  Hence the constant `c₃` is inert: `hgm` holds at some
  positive constant iff it holds at some other.  `MomentGapAt.mono` records the monotonicity.
* `momentGap_forces_cutMoment_two_ne_top` — non-vacuity: `hgm` together with `hP` *forces*
  `M.cutMoment 2 r ≠ ⊤` at large `r`, so `hgm` cannot be satisfied by the `toReal ⊤ = 0`
  degenerate reading of its right-hand side.  (The left-hand side `M.cutMassAt r 0` is already
  known to be finite at every positive radius from `hP`,
  production `AuditM2.cutMassAt_ne_top_of_hP`.)
* `momentGap_forces_cutMoment_two_tendsto_atTop` — the second moment itself diverges.
* `momentGap_of_tendsto_normalized` — circularity: the *conclusion* of
  `secondMoment_asymptotic_case3_of_source_p21` (together with `hP`) already implies `hgm`.
  So `hgm` is a consequence of the target asymptotic, and any derivation of `hgm` from the
  conclusion would be circular; in particular `hgm` is strictly weaker than the conclusion but
  not independent of it.
* `jensen_does_not_give_momentGap` — insufficiency: at the level of mass/second-moment profiles,
  finiteness together with Jensen (`(E|K|)² ≤ E|K|²`, the only automatic inequality between the
  two moments) does **not** give `hgm`.  Hence `hgm` needs a genuine spread/anti-concentration
  input, not a rearrangement of the moment inequalities.
* `regularlyVarying_does_not_give_power_lower` — the *bare* regular-variation conclusion of
  Proposition I.4.15 does not imply `hgm` either: `r ↦ r^a / log r` is regularly varying of
  index `a` for `a > 0` but is `o(r^a)`.  Only the stronger `∼ A r^{3α}` branch does.
* `momentGapAt_mul_pow_three_le_of_tendsto_normalized` — constant audit: if the normalised second
  moment converges to `A` then every admissible `c` has `c (α/β_c)^3 ≤ A`.
* `betaCrit_coe_ne_zero_of_hP`, `cutMoment_two_ne_top_of_hP_of_momentGap`,
  `cutMoment_one_ne_top_of_hP_of_momentGap`, `measurable_p2ExclError_of_hP_of_momentGap`,
  `measurable_p2Ebar_of_hP_of_momentGap`, `measurable_rhsScalarTwo_of_hP_of_momentGap`,
  `logIntegrable_cutE0_of_source` — redundancy audit: seven of the fourteen retained inputs
  (`hα`, `hβ`, `h1`, `h2`, `hmeasE2`, `hmeasEbar`, `hlogE0`) are not independent.
* `secondMoment_asymptotic_case3_of_source_p21_core` — the consumer with the seven genuinely
  independent inputs (`hac`, `hae`, `hP`, `hTri`, `hF`, `hlogH`, `hgm`), same conclusion and
  constants, nothing added.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.MomentGapAudit.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Bridge
public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Consumers
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.FirstMomentLogError

/-! # Case-3 moment gap: equivalence, non-vacuity, circularity -/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- Several hypotheses are kept for API/source fidelity even where the proof does not use them.
set_option linter.unusedVariables false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Case3MomentGapAudit

/-! ## Elementary real-variable lemmas -/

/-- `(r ^ α) ^ 3 = r ^ (3 * α)` for `r > 0`. -/
theorem rpow_cube_eq {r α : ℝ} (hr : 0 < r) : (r ^ α) ^ 3 = r ^ (3 * α) := by
  rw [← Real.rpow_natCast (r ^ α) 3, ← Real.rpow_mul hr.le]
  congr 1
  push_cast
  ring

/-- **Two-sided comparison of a first moment at scale `r ^ α`.**  `f r / (κ r ^ α) → 1` with
`κ > 0` gives the eventual sandwich `(κ/2) r^α ≤ f r ≤ (3κ/2) r^α`. -/
theorem eventually_sandwich_of_tendsto_div {f : ℝ → ℝ} {α κ : ℝ} (hκ : 0 < κ)
    (h : Tendsto (fun r : ℝ => f r / (κ * r ^ α)) atTop (𝓝 1)) :
    ∀ᶠ r : ℝ in atTop, κ / 2 * r ^ α ≤ f r ∧ f r ≤ 3 * κ / 2 * r ^ α := by
  have hlow : ∀ᶠ r : ℝ in atTop, (1 / 2 : ℝ) < f r / (κ * r ^ α) :=
    h (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hhigh : ∀ᶠ r : ℝ in atTop, f r / (κ * r ^ α) < (3 / 2 : ℝ) :=
    h (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) < 3 / 2))
  filter_upwards [hlow, hhigh, eventually_ge_atTop (1 : ℝ)] with r hl hh hr1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hp : 0 < κ * r ^ α := mul_pos hκ (Real.rpow_pos_of_pos hr α)
  refine ⟨?_, ?_⟩
  · have h' := (lt_div_iff₀ hp).1 hl
    linarith
  · have h' := (div_lt_iff₀ hp).1 hh
    linarith

/-- **A moment gap at scale `(E|K|)³` is a power lower bound at scale `r^{3α}`**, given a
two-sided comparison of the first moment with `κ r ^ α`.  This is the abstract core of
`momentGap_iff_secondMomentLower`. -/
theorem exists_const_mul_cube_le_iff {f g : ℝ → ℝ} {α : ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hfnn : ∀ᶠ r : ℝ in atTop, 0 ≤ f r)
    (hsand : ∀ᶠ r : ℝ in atTop, κ / 2 * r ^ α ≤ f r ∧ f r ≤ 3 * κ / 2 * r ^ α) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop, c * (f r) ^ 3 ≤ g r) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop, c * r ^ (3 * α) ≤ g r := by
  constructor
  · rintro ⟨c, hc, hcf⟩
    refine ⟨c * (κ / 2) ^ 3, mul_pos hc (pow_pos (by positivity) 3), ?_⟩
    filter_upwards [hcf, hsand, eventually_ge_atTop (1 : ℝ)] with r hcfr hs hr1
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have hpow : (κ / 2 * r ^ α) ^ 3 = (κ / 2) ^ 3 * r ^ (3 * α) := by
      rw [mul_pow, rpow_cube_eq hr]
    have hstep : (κ / 2) ^ 3 * r ^ (3 * α) ≤ (f r) ^ 3 := by
      rw [← hpow]
      exact pow_le_pow_left₀ (by positivity) hs.1 3
    calc c * (κ / 2) ^ 3 * r ^ (3 * α)
        = c * ((κ / 2) ^ 3 * r ^ (3 * α)) := by ring
      _ ≤ c * (f r) ^ 3 := mul_le_mul_of_nonneg_left hstep hc.le
      _ ≤ g r := hcfr
  · rintro ⟨c, hc, hcg⟩
    refine ⟨c / (3 * κ / 2) ^ 3, div_pos hc (pow_pos (by positivity) 3), ?_⟩
    filter_upwards [hcg, hsand, hfnn, eventually_ge_atTop (1 : ℝ)] with r hcgr hs hf hr1
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have hD : (3 * κ / 2) ^ 3 ≠ 0 := by positivity
    have hpow : (3 * κ / 2 * r ^ α) ^ 3 = (3 * κ / 2) ^ 3 * r ^ (3 * α) := by
      rw [mul_pow, rpow_cube_eq hr]
    have hstep : (f r) ^ 3 ≤ (3 * κ / 2) ^ 3 * r ^ (3 * α) := by
      rw [← hpow]
      exact pow_le_pow_left₀ hf hs.2 3
    calc c / (3 * κ / 2) ^ 3 * (f r) ^ 3
        ≤ c / (3 * κ / 2) ^ 3 * ((3 * κ / 2) ^ 3 * r ^ (3 * α)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = c * r ^ (3 * α) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hD]
      _ ≤ g r := hcgr

/-- **Finiteness plus Jensen does not give the moment gap.**  There are a mass profile `f` and a
second-moment profile `g` with `f r / r ^ α → 1` and `(f r)² ≤ g r` for all `r` (the only
automatic inequality between a mean and a second moment) such that no positive constant makes
`c (f r)³ ≤ g r` eventually.  So the gap `E|K|² ⪰ (E|K|)³` cannot be obtained from the moment
inequalities alone: it needs a spread/anti-concentration (tail) input. -/
theorem jensen_does_not_give_momentGap (α : ℝ) (hα : 0 < α) :
    ∃ f g : ℝ → ℝ, (∀ᶠ r : ℝ in atTop, 0 ≤ f r) ∧ (∀ r : ℝ, (f r) ^ 2 ≤ g r) ∧
      Tendsto (fun r : ℝ => f r / r ^ α) atTop (𝓝 1) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop, c * (f r) ^ 3 ≤ g r := by
  have hnonneg : ∀ᶠ r : ℝ in atTop, 0 ≤ r ^ α := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hr) α).le
  refine ⟨fun r => r ^ α, fun r => (r ^ α) ^ 2, hnonneg, fun r => le_rfl, ?_, ?_⟩
  · have hEq : (fun r : ℝ => r ^ α / r ^ α) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      exact div_self (ne_of_gt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hr) α))
    simpa using Tendsto.congr' hEq.symm tendsto_const_nhds
  · rintro ⟨c, hc, hge⟩
    have htop : Tendsto (fun r : ℝ => c * r ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα).const_mul_atTop hc
    have hbig : ∀ᶠ r : ℝ in atTop, (1 : ℝ) < c * r ^ α :=
      htop.eventually (eventually_gt_atTop (1 : ℝ))
    obtain ⟨r, h1r, h2r, h3r⟩ :=
      (hbig.and (hge.and (eventually_ge_atTop (1 : ℝ)))).exists
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one h3r
    have hsq : 0 < (r ^ α) ^ 2 := by
      have := Real.rpow_pos_of_pos hrpos α
      positivity
    have hfac : (r ^ α) ^ 2 * (c * r ^ α) ≤ (r ^ α) ^ 2 * 1 := by nlinarith [h2r]
    have hle : c * r ^ α ≤ 1 := (mul_le_mul_iff_right₀ hsq).1 hfac
    linarith

/-! ## Regular variation of index `a` is not enough for the gap -/

/-- `log (l * x) / log x → 1` for `l > 0`. -/
theorem tendsto_log_mul_div_log {l : ℝ} (hl : 0 < l) :
    Tendsto (fun x : ℝ => Real.log (l * x) / Real.log x) atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ => Real.log l / Real.log x) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  have h1 : Tendsto (fun x : ℝ => Real.log l / Real.log x + 1) atTop (𝓝 (0 + 1)) :=
    h0.add tendsto_const_nhds
  refine Tendsto.congr' ?_ (by simpa using h1)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hl0 : l ≠ 0 := ne_of_gt hl
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [Real.log_mul hl0 hx0]
  field_simp

/-- `r ↦ r ^ a / log r` is regularly varying of index `a` for `a > 0`. -/
theorem regularlyVarying_div_log (a : ℝ) (ha : 0 < a) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => r ^ a / Real.log r) a := by
  constructor
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    exact div_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hx0 a)) (ne_of_gt (Real.log_pos hx))
  · intro l hl
    have hinv : Tendsto (fun x : ℝ => Real.log x / Real.log (l * x)) atTop (𝓝 1) := by
      have h := (tendsto_log_mul_div_log hl).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      simpa [inv_div] using h
    have hkey : Tendsto (fun x : ℝ => l ^ a * (Real.log x / Real.log (l * x)))
        atTop (𝓝 (l ^ a * 1)) := tendsto_const_nhds.mul hinv
    refine Tendsto.congr' ?_ (by simpa using hkey)
    filter_upwards [eventually_gt_atTop (max 1 (2 / l))] with x hx
    have hx1 : (1 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
    have hlx : (1 : ℝ) < l * x := by
      have h2 : 2 / l ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx)
      have h3 : l * (2 / l) = 2 := by field_simp
      nlinarith [hl, h2]
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    have hloglx : Real.log (l * x) ≠ 0 := ne_of_gt (Real.log_pos hlx)
    have hxa : x ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx0 a)
    have hpow : (l * x) ^ a = l ^ a * x ^ a := Real.mul_rpow hl.le hx0.le
    rw [hpow]
    field_simp

/-- **Regular variation of index `a` does not give a power lower bound of index `a`.**  The
function `r ↦ r^a / log r` is regularly varying of index `a` (`a > 0`) but is `o(r^a)`, so no
positive constant bounds it from below by `c r^a` eventually.

Consequence for the audit: the *bare* regular-variation conclusion of Proposition I.4.15 does not
imply the Case-3 moment gap; only the stronger `E_{β_c,r}|K|² ∼ A r^{3α}` form with `A > 0` does
(`SourceModelData.momentGap_of_tendsto_normalized`). -/
theorem regularlyVarying_does_not_give_power_lower (a : ℝ) (ha : 0 < a) :
    ∃ g : ℝ → ℝ, Analysis.RegularlyVaryingAtTop g a ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop, c * r ^ a ≤ g r := by
  refine ⟨fun r : ℝ => r ^ a / Real.log r, regularlyVarying_div_log a ha, ?_⟩
  rintro ⟨c, hc, hge⟩
  have hratio : Tendsto (fun r : ℝ => (r ^ a / Real.log r) / r ^ a) atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ => (Real.log r)⁻¹) atTop (𝓝 0) :=
      Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop
    refine Tendsto.congr' ?_ hinv
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hxa : x ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx0 a)
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    field_simp
  have hc_le : ∀ᶠ r : ℝ in atTop, c ≤ (r ^ a / Real.log r) / r ^ a := by
    filter_upwards [hge, eventually_gt_atTop (1 : ℝ)] with r hr hx
    have hx0 : (0 : ℝ) < r := lt_trans zero_lt_one hx
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hx0 a)).2 hr
  have hcle : c ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hratio hc_le
  linarith

end Case3MomentGapAudit

namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- `M.betaCrit` is positive as a real number when it is nonzero. -/
theorem betaCrit_coe_pos (hβ : (M.betaCrit : ℝ) ≠ 0) : (0 : ℝ) < (M.betaCrit : ℝ) := by
  have h0 : M.betaCrit ≠ 0 := fun h => hβ (by rw [h]; simp)
  have hle : (0 : ℝ≥0) ≤ M.betaCrit := zero_le
  have hpos : (0 : ℝ≥0) < M.betaCrit := lt_of_le_of_ne hle (Ne.symm h0)
  simpa using NNReal.coe_lt_coe.mpr hpos

/-- The eventual two-sided comparison of `E_{β_c,r}|K|` with `(α/β_c) r^α` used by the
normalisation theorem.  Consequence of the retained first-moment asymptotic `hP`. -/
theorem eventually_sandwich_cutMassAt (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∀ᶠ r : ℝ in atTop,
      (M.α / (M.betaCrit : ℝ)) / 2 * r ^ M.α ≤ (M.cutMassAt r 0).toReal ∧
        (M.cutMassAt r 0).toReal ≤ 3 * (M.α / (M.betaCrit : ℝ)) / 2 * r ^ M.α :=
  Case3MomentGapAudit.eventually_sandwich_of_tendsto_div
    (div_pos hα (M.betaCrit_coe_pos hβ)) hP

/-- **Normalisation audit.**  Under the retained first-moment asymptotic, the retained moment gap
`hgm` is *equivalent* to the source's power lower bound `E_{β_c,r}|K|² ⪰ r^{3α}` (p. 47).  In
particular the constant `c₃` carries no source content: the gap holds at one positive constant
iff it holds at any other. -/
theorem momentGap_iff_secondMomentLower (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    M.MomentGap ↔ M.SecondMomentLower :=
  Case3MomentGapAudit.exists_const_mul_cube_le_iff (div_pos hα (M.betaCrit_coe_pos hβ))
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (M.eventually_sandwich_cutMassAt hα hβ hP)

/-- A larger admissible constant can be replaced by any smaller positive one. -/
theorem MomentGapAt.mono {c c' : ℝ} (hc' : 0 < c') (hle : c' ≤ c) (h : M.MomentGapAt c) :
    M.MomentGapAt c' := by
  filter_upwards [h] with r hr
  have hnn : 0 ≤ (M.cutMassAt r 0).toReal ^ 3 := by positivity
  exact le_trans (mul_le_mul_of_nonneg_right hle hnn) hr

/-- **Non-vacuity audit.**  The moment gap is a genuine inequality: together with `hP` it forces
the second cutoff moment to be finite at all large radii.  So `hgm` cannot be discharged by the
degenerate `(⊤ : ℝ≥0∞).toReal = 0` reading of its right-hand side. -/
theorem momentGap_forces_cutMoment_two_ne_top (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hgm : M.MomentGap) : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤ := by
  obtain ⟨c, hc, hcge⟩ := hgm
  filter_upwards [hcge, M.eventually_sandwich_cutMassAt hα hβ hP,
    eventually_ge_atTop (1 : ℝ)] with r hge hs hr1
  intro htop
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos hα (M.betaCrit_coe_pos hβ)
  have hbase : 0 < (M.α / (M.betaCrit : ℝ)) / 2 * r ^ M.α :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hr M.α)
  have hfpos : 0 < (M.cutMassAt r 0).toReal := lt_of_lt_of_le hbase hs.1
  rw [htop, ENNReal.toReal_top] at hge
  have hpos : 0 < c * (M.cutMassAt r 0).toReal ^ 3 := mul_pos hc (pow_pos hfpos 3)
  linarith

/-- The moment gap also forces the second cutoff moment itself to diverge. -/
theorem momentGap_forces_cutMoment_two_tendsto_atTop (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hgm : M.MomentGap) : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal) atTop atTop := by
  rw [M.momentGap_iff_secondMomentLower hα hβ hP] at hgm
  obtain ⟨c, hc, hlow⟩ := hgm
  refine Filter.tendsto_atTop_mono' (l := atTop)
    (f₁ := fun r : ℝ => c * r ^ (3 * M.α)) ?_ ?_
  · filter_upwards [hlow] with r h
    exact h
  · have h3 : 0 < 3 * M.α := by linarith
    exact (tendsto_rpow_atTop h3).const_mul_atTop hc

/-- **Circularity audit.**  The conclusion of `secondMoment_asymptotic_case3_of_source_p21`
(together with the retained `hP`) already implies the moment gap `hgm`.  So `hgm` is a
*consequence* of the target asymptotic: proving it from the conclusion would be circular, and it
is strictly weaker than the conclusion rather than independent of it. -/
theorem momentGap_of_tendsto_normalized (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {A : ℝ} (hA : 0 < A)
    (hratio : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A)) :
    M.MomentGap := by
  rw [M.momentGap_iff_secondMomentLower hα hβ hP]
  refine ⟨A / 2, by positivity, ?_⟩
  have hlow : ∀ᶠ r : ℝ in atTop, A / 2 < (M.cutMoment 2 r).toReal / r ^ (3 * M.α) :=
    hratio (isOpen_Ioi.mem_nhds (by linarith : A / 2 < A))
  filter_upwards [hlow, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have h3 : 0 < 3 * M.α := by linarith
  have hp : 0 < r ^ (3 * M.α) := Real.rpow_pos_of_pos hrpos (3 * M.α)
  have h' := (lt_div_iff₀ hp).1 hr
  linarith

/-- **Quantitative bridge, forward direction.**  `hgm` at a constant `c` gives the power lower
bound `c (α/β_c / 2)^3 r^{3α} ≤ E_{β_c,r}|K|²` at large `r`. -/
theorem momentGapAt_to_secondMomentLowerAt (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) (hgm : M.MomentGapAt c) :
    M.SecondMomentLowerAt (c * ((M.α / (M.betaCrit : ℝ)) / 2) ^ 3) := by
  filter_upwards [hgm, M.eventually_sandwich_cutMassAt hα hβ hP,
    eventually_ge_atTop (1 : ℝ)] with r hge hs hr1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hpow : ((M.α / (M.betaCrit : ℝ)) / 2 * r ^ M.α) ^ 3
      = ((M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * r ^ (3 * M.α) := by
    rw [mul_pow, Case3MomentGapAudit.rpow_cube_eq hr]
  have hstep : ((M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * r ^ (3 * M.α)
      ≤ (M.cutMassAt r 0).toReal ^ 3 := by
    rw [← hpow]
    exact pow_le_pow_left₀ (by positivity) hs.1 3
  calc c * ((M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * r ^ (3 * M.α)
      = c * (((M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * r ^ (3 * M.α)) := by ring
    _ ≤ c * (M.cutMassAt r 0).toReal ^ 3 := mul_le_mul_of_nonneg_left hstep hc.le
    _ ≤ (M.cutMoment 2 r).toReal := hge

/-- **Quantitative bridge, reverse direction.**  A power lower bound at `c` gives `hgm` at
`c / (3 α/β_c / 2)^3`. -/
theorem secondMomentLowerAt_to_momentGapAt (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) (hlow : M.SecondMomentLowerAt c) :
    M.MomentGapAt (c / (3 * (M.α / (M.betaCrit : ℝ)) / 2) ^ 3) := by
  have hD : (3 * (M.α / (M.betaCrit : ℝ)) / 2) ^ 3 ≠ 0 := by
    have : 0 < 3 * (M.α / (M.betaCrit : ℝ)) / 2 := by
      have := div_pos hα (M.betaCrit_coe_pos hβ)
      positivity
    positivity
  filter_upwards [hlow, M.eventually_sandwich_cutMassAt hα hβ hP,
    eventually_ge_atTop (1 : ℝ)] with r hcl hs hr1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hpow : (3 * (M.α / (M.betaCrit : ℝ)) / 2 * r ^ M.α) ^ 3
      = (3 * (M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * r ^ (3 * M.α) := by
    rw [mul_pow, Case3MomentGapAudit.rpow_cube_eq hr]
  have hstep : (M.cutMassAt r 0).toReal ^ 3
      ≤ (3 * (M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * r ^ (3 * M.α) := by
    rw [← hpow]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hs.2 3
  calc c / (3 * (M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * (M.cutMassAt r 0).toReal ^ 3
      ≤ c / (3 * (M.α / (M.betaCrit : ℝ)) / 2) ^ 3
          * ((3 * (M.α / (M.betaCrit : ℝ)) / 2) ^ 3 * r ^ (3 * M.α)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = c * r ^ (3 * M.α) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hD]
    _ ≤ (M.cutMoment 2 r).toReal := hcl

/-- The change of variables inside the Case-3 normalisation: `c (E|K|)³ / r^{3α}` equals
`c ((E|K|)/((α/β_c) r^α))³ (α/β_c)³`. -/
theorem mul_cube_div_rpow_eq (hκ : 0 < M.α / (M.betaCrit : ℝ)) {c r : ℝ} (hr : 0 < r) :
    c * (M.cutMassAt r 0).toReal ^ 3 / r ^ (3 * M.α)
      = c * (((M.cutMassAt r 0).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) ^ 3
        * (M.α / (M.betaCrit : ℝ)) ^ 3) := by
  have hκr : (M.α / (M.betaCrit : ℝ)) * r ^ M.α ≠ 0 :=
    ne_of_gt (mul_pos hκ (Real.rpow_pos_of_pos hr M.α))
  have hf : (M.cutMassAt r 0).toReal
      = ((M.cutMassAt r 0).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α))
        * ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) := by
    rw [div_mul_cancel₀ _ hκr]
  rw [hf, mul_pow, mul_pow, Case3MomentGapAudit.rpow_cube_eq hr]
  field_simp

/-- `c (E_{β_c,r}|K|)³ / r^{3α}` converges to `c (α/β_c)³` under the retained `hP`. -/
theorem mul_cube_div_rpow_tendsto (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) (c : ℝ) :
    Tendsto (fun r : ℝ => c * (M.cutMassAt r 0).toReal ^ 3 / r ^ (3 * M.α))
      atTop (𝓝 (c * (M.α / (M.betaCrit : ℝ)) ^ 3)) := by
  have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos hα (M.betaCrit_coe_pos hβ)
  have hstep : Tendsto (fun r : ℝ => ((M.cutMassAt r 0).toReal
        / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) ^ 3 * (M.α / (M.betaCrit : ℝ)) ^ 3)
      atTop (𝓝 (1 ^ 3 * (M.α / (M.betaCrit : ℝ)) ^ 3)) := (hP.pow 3).mul_const _
  have hcongr : (fun r : ℝ => c * (M.cutMassAt r 0).toReal ^ 3 / r ^ (3 * M.α))
      =ᶠ[atTop] (fun r : ℝ => c * (((M.cutMassAt r 0).toReal
        / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) ^ 3
        * (M.α / (M.betaCrit : ℝ)) ^ 3)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact M.mul_cube_div_rpow_eq hκ hr
  simpa using Tendsto.congr' hcongr.symm (hstep.const_mul c)

/-- **Constant audit, upper bound.**  If the second normalised moment converges to `A` and `hgm`
holds at the constant `c`, then `c (α/β_c)^3 ≤ A`.  Consequently the retained constant `c₃` of the
Case-3 wrapper can never exceed `A / (α/β_c)^3`: `hgm` is a lower-bound statement about `A`, not an
independent hypothesis about the constant. -/
theorem momentGapAt_mul_pow_three_le_of_tendsto_normalized (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {A c : ℝ} (hgm : M.MomentGapAt c)
    (hA : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A)) :
    c * (M.α / (M.betaCrit : ℝ)) ^ 3 ≤ A := by
  refine le_of_tendsto_of_tendsto (M.mul_cube_div_rpow_tendsto hα hβ hP c) hA ?_
  filter_upwards [hgm, eventually_ge_atTop (1 : ℝ)] with r hgr hr1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  exact div_le_div_of_nonneg_right hgr (Real.rpow_pos_of_pos hr (3 * M.α)).le

/-- **Constant audit, lower bound.**  Strictly below the threshold `A / (α/β_c)^3` the gap holds:
if `c (α/β_c)^3 < A` then `hgm` holds at `c`.  Together with the upper bound, the admissible
constants have supremum exactly `A / (α/β_c)^3`. -/
theorem momentGapAt_of_mul_pow_three_lt_tendsto_normalized (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {A c : ℝ} (hcA : c * (M.α / (M.betaCrit : ℝ)) ^ 3 < A)
    (hA : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A)) :
    M.MomentGapAt c := by
  filter_upwards [(M.mul_cube_div_rpow_tendsto hα hβ hP c).eventually_lt hA hcA,
    eventually_ge_atTop (1 : ℝ)] with r hlt hr1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  exact ((div_lt_div_iff_of_pos_right (Real.rpow_pos_of_pos hr (3 * M.α))).1 hlt).le

/-- **The moment gap is exactly positivity of the limiting constant.**  Given the retained `hP`
and the convergence `E_{β_c,r}|K|² / r^{3α} → A` (the `∼ A r^{3α}` conclusion of Proposition
I.4.15), the Case-3 moment gap holds **iff** `A > 0`.  This is the exact strength of `hgm`: it
carries no information beyond the sign of the constant in the conclusion, and conversely it
follows from that conclusion precisely when the constant is positive. -/
theorem momentGap_iff_pos_limit (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {A : ℝ} (hA : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A)) :
    M.MomentGap ↔ 0 < A := by
  constructor
  · rintro ⟨c, hc, hgc⟩
    have hle := M.momentGapAt_mul_pow_three_le_of_tendsto_normalized hα hβ hP hgc hA
    have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos hα (M.betaCrit_coe_pos hβ)
    have hpos : 0 < c * (M.α / (M.betaCrit : ℝ)) ^ 3 := mul_pos hc (pow_pos hκ 3)
    linarith
  · intro hApos
    have hκ : 0 < M.α / (M.betaCrit : ℝ) := div_pos hα (M.betaCrit_coe_pos hβ)
    have hκ3 : 0 < (M.α / (M.betaCrit : ℝ)) ^ 3 := pow_pos hκ 3
    refine ⟨A / (2 * (M.α / (M.betaCrit : ℝ)) ^ 3), by positivity, ?_⟩
    refine M.momentGapAt_of_mul_pow_three_lt_tendsto_normalized hα hβ hP ?_ hA
    have hpos : 0 < A / (2 * (M.α / (M.betaCrit : ℝ)) ^ 3)
        * (M.α / (M.betaCrit : ℝ)) ^ 3 := by positivity
    have heq : A / (2 * (M.α / (M.betaCrit : ℝ)) ^ 3) * (M.α / (M.betaCrit : ℝ)) ^ 3
        = A / 2 := by
      field_simp
    rw [heq]
    linarith

/-- **Ratio form of the moment gap**, the shape closest to `liminf > 0`: some positive constant
bounds `E_{β_c,r}|K|² / r^{3α}` from below eventually. -/
theorem momentGap_iff_exists_eventually_le_div (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    M.MomentGap ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop,
      c ≤ (M.cutMoment 2 r).toReal / r ^ (3 * M.α) := by
  rw [M.momentGap_iff_secondMomentLower hα hβ hP]
  constructor
  · rintro ⟨c, hc, hlow⟩
    exact ⟨c, hc, by
      filter_upwards [hlow, eventually_ge_atTop (1 : ℝ)] with r hr hr1
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hrpos (3 * M.α))).2 hr⟩
  · rintro ⟨c, hc, hlow⟩
    exact ⟨c, hc, by
      filter_upwards [hlow, eventually_ge_atTop (1 : ℝ)] with r hr hr1
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hrpos (3 * M.α))).1 hr⟩

/-! ## Redundancy audit: which retained inputs are not independent -/

/-- **`hβ` is not independent**: the retained first-moment asymptotic `hP` already forces
`β_c ≠ 0` (production `I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div`). -/
theorem betaCrit_coe_ne_zero_of_hP
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    (M.betaCrit : ℝ) ≠ 0 :=
  ne_of_gt (PercLib.CriticalLRP.I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div M hP)

/-- **`h2` is not independent**: `hgm` together with `hP` forces finiteness of the second cutoff
moment at *every* positive radius, because finiteness is monotone downwards in the radius
(production `cutMoment_ne_top_of_le`) and `hgm` gives it at arbitrarily large radii. -/
theorem cutMoment_two_ne_top_of_hP_of_momentGap (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hgm : M.MomentGap) : ∀ t : ℝ, 0 < t → M.cutMoment 2 t ≠ ⊤ := by
  obtain ⟨R, hR⟩ :=
    eventually_atTop.1 (M.momentGap_forces_cutMoment_two_ne_top hα hβ hP hgm)
  intro t _
  exact M.cutMoment_ne_top_of_le (le_max_left t R) 2 (hR (max t R) (le_max_right t R))

/-- **`h1` is not independent** either: finiteness of the first cutoff moment follows from
finiteness of the second (production `cutMoment_one_ne_top_of_two`). -/
theorem cutMoment_one_ne_top_of_hP_of_momentGap (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hgm : M.MomentGap) : ∀ t : ℝ, 0 < t → M.cutMoment 1 t ≠ ⊤ :=
  fun t ht =>
    M.cutMoment_one_ne_top_of_two (M.cutMoment_two_ne_top_of_hP_of_momentGap hα hβ hP hgm t ht)

/-! ## Measurability inputs: already consequences of `h1`, `h2` in production -/

/-- `Measurable M.p2ExclError` from `hP` and `hgm` alone.  Production
(`SecondMomentMeasurability.Consumers`) proves it from `h1`, `h2`, which the audit shows are
themselves consequences of `hP` and `hgm`. -/
theorem measurable_p2ExclError_of_hP_of_momentGap (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hgm : M.MomentGap) : Measurable M.p2ExclError :=
  M.measurable_p2ExclError_of_tail (r₀ := 1)
    (fun t ht =>
      M.cutMoment_one_ne_top_of_hP_of_momentGap hα hβ hP hgm t (lt_of_lt_of_le zero_lt_one ht))
    (fun t ht =>
      M.cutMoment_two_ne_top_of_hP_of_momentGap hα hβ hP hgm t (lt_of_lt_of_le zero_lt_one ht))

/-- `Measurable M.p2Ebar` from `hP` and `hgm` alone. -/
theorem measurable_p2Ebar_of_hP_of_momentGap (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hgm : M.MomentGap) : Measurable M.p2Ebar :=
  M.measurable_p2Ebar_of_tail hα (r₀ := 1)
    (fun t ht =>
      M.cutMoment_one_ne_top_of_hP_of_momentGap hα hβ hP hgm t (lt_of_lt_of_le zero_lt_one ht))
    (fun t ht =>
      M.cutMoment_two_ne_top_of_hP_of_momentGap hα hβ hP hgm t (lt_of_lt_of_le zero_lt_one ht))

/-- `Measurable M.rhsScalarTwo` (the `hmR` input of the `regularlyVarying` variants) from `hP`
and `hgm` alone. -/
theorem measurable_rhsScalarTwo_of_hP_of_momentGap (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hgm : M.MomentGap) : Measurable M.rhsScalarTwo :=
  M.measurable_rhsScalarTwo_of_tail (r₀ := 1)
    (fun t ht =>
      M.cutMoment_two_ne_top_of_hP_of_momentGap hα hβ hP hgm t (lt_of_lt_of_le zero_lt_one ht))

/-- **`hlogE0` is not independent**: production already proves
`LogarithmicallyIntegrable (PivotFlux.cutE0 M)` with no hypotheses at all
(`SourceModelData.logIntegrable_cutE0'`, from `CaseOne.logIntegrable_cutE0`). -/
theorem logIntegrable_cutE0_of_source :
    Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M) :=
  M.logIntegrable_cutE0'

/-- **The Case-3 consumer on its genuinely independent inputs.**  Same conclusion and same
constants as `secondMoment_asymptotic_case3_of_source_p21`, but only the seven inputs that the
audit does not derive from the others: the radial regularity `hac`, `hae`, the first-moment
asymptotic `hP`, the triangle/tail data `hTri`, `hF`, the logarithmically-integrable first-moment
error `hlogH`, and the moment gap `hgm`.  Every hypothesis deleted here (`hα`, `hβ`, `h1`, `h2`,
`hmeasE2`, `hmeasEbar`, `hlogE0`) is *proved* in this file from `hP` and `hgm` (or is the
structure field `M.hα`, or is the hypothesis-free production theorem
`logIntegrable_cutE0_of_source`); nothing is added. -/
theorem secondMoment_asymptotic_case3_of_source_p21_core {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  M.secondMoment_asymptotic_case3_of_source_p21 M.hα hr₀ (M.betaCrit_coe_ne_zero_of_hP hP)
    hac hae
    (fun t ht =>
      M.cutMoment_one_ne_top_of_hP_of_momentGap M.hα (M.betaCrit_coe_ne_zero_of_hP hP) hP
        ⟨c3, hc3, hgm⟩ t (lt_of_lt_of_le hr₀ ht))
    (fun t ht =>
      M.cutMoment_two_ne_top_of_hP_of_momentGap M.hα (M.betaCrit_coe_ne_zero_of_hP hP) hP
        ⟨c3, hc3, hgm⟩ t (lt_of_lt_of_le hr₀ ht))
    hP hTri hC₀ hp hF
    (M.measurable_p2ExclError_of_hP_of_momentGap M.hα (M.betaCrit_coe_ne_zero_of_hP hP) hP
      ⟨c3, hc3, hgm⟩)
    (M.measurable_p2Ebar_of_hP_of_momentGap M.hα (M.betaCrit_coe_ne_zero_of_hP hP) hP
      ⟨c3, hc3, hgm⟩)
    hlogH M.logIntegrable_cutE0_of_source hc3 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
