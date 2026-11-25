module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.Nonvacuity

/-!
# Off-corner `stdDegree`: the radius-local-uniform bound is false

Scratch development of swarm `smwudd7jf`, member `m2` (direction D1A).

`M.stdDegree r = #(ball r) * (-K'(r)) / gapFloor r` is the standardised incident majorant of
`PercLib.CriticalLRP.Analysis.Cutoff.OffCorner`.  This file checks the exact status of a
*radius-local-uniform* upper bound for it.

## What is established, exactly

`M.gapFloor r` is the minimum of `K s - K r` over attained support radii `s < r`, and an attained
radius `s₀` of the source norm is itself a candidate, so `gapFloor r ≤ K s₀ - K r → 0` as
`r ↘ s₀`.  Past the tail threshold `R` of `exists_deriv_bounds` the derivative is bounded away
from `0` there, so `stdDegree` grows at least like `(1/4)(s₀/(s₀+e))^(d+α+1) (r - s₀)⁻¹` as `r`
approaches each attained radius `s₀ > R` from above, and attained radii are unbounded above
(`exists_attainedRadii_gt`).  Hence:

* **no radius-local-uniform bound on a compact window**: `not_bddAbove_stdDegree_Ioo` — for every
  `a < s₀ < b` with `s₀` an attained radius past `R`, the image of `Ioo a b` under `stdDegree` is
  unbounded above.  This covers off-corner radii too, since the blow-up is one-sided on the whole
  window `(s₀, s₀+e)` and attained radii are a null set;
* **no `C * r^(-d-α-1)` eventual majorant**: `not_eventually_le_const_mul_rpow`.  In particular the
  `r^(-1-α)` tail estimate that a ball-count asymptotic `#(ball r) ≈ r^d`, a derivative decay
  `|K'| ≈ r^(-d-α-1)` and a *bounded* gap floor would produce is unavailable — the third input is
  what fails;
* consequently **no majorant of `stdDegree` can be bounded on those compact windows**
  (`not_bddAbove_of_stdDegree_le`).

## What is *not* claimed

Nothing here decides `IntegrableOn M.stdDegree (Ioi r₀)`.  Unboundedness on infinitely many windows
at infinity is compatible with integrability, so these results do **not** refute a decomposition
into a bounded compact part plus an integrable tail: only the "bounded compact part" half is
excluded, and the integrability half is left open.  In particular no non-integrability statement is
proved anywhere in this file, and no measurability of `r ↦ M.gapFloor r` (hence of `stdDegree`) is
available; the file mentions the reciprocal estimate only as the reason the *uniform-majorant*
target fails, never as a proof of non-integrability.

The strongest *correct* positive statements are also recorded:

* `gapFloor_ge_of_separated` / `stdDegree_le_of_separated`: a uniform bound on a compact
  subinterval of the tail with an explicit constant, under the exact hypothesis that the radius
  stays at distance `ε` above every attained radius below it;
* `exists_stdDegree_gt` / `not_bddAbove_stdDegree_Ioo`: the one-sided blow-up that shows the
  separation hypothesis cannot be dropped.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The gap floor is at most the gap to any attained radius below -/

/-- **Any attained radius below `r` supplies a candidate gap.**  If `s` is an attained radius,
`s < r`, and `r` is past the tail threshold `R` of `exists_deriv_bounds`, then `K` strictly
decreases across `[s, r]` and `s` enters the gap floor, so `gapFloor r ≤ K s - K r`. -/
theorem gapFloor_le_gap_to_attained {R s r : ℝ}
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hR : R < r) (hs : s ∈ M.attainedRadii) (hsr : s < r) :
    M.gapFloor r ≤ M.K s - M.K r := by
  have hspos : 0 < s := M.attainedRadii_pos hs
  have hlt : M.K r < M.K s := M.K_lt_of_lt_of_tail hR hlow hspos hsr
  refine M.gapFloor_le_of_pos ?_
  exact ⟨⟨hs, hsr⟩, by linarith⟩

/-- **The normalised ball is nonempty at every positive radius**, so its cardinality is at least
one.  (The origin is always in `M.ball r`.) -/
theorem one_le_ncard_ball {r : ℝ} (hr : 0 < r) : 1 ≤ (M.ball r).ncard := by
  have hmem : (0 : M.V) ∈ M.ball r := by
    have h0 : toVec (0 : M.V) = (0 : Fin M.d → ℝ) := by
      funext i
      simp [toVec]
    change M.S.ρ (toVec (0 : M.V)) ≤ r
    rw [h0, SourceNormData.ρ_zero]
    exact hr.le
  have hpos : 0 < (M.ball r).ncard :=
    Set.ncard_pos (M.finite_ball r) |>.mpr ⟨0, hmem⟩
  omega

/-! ## 2. The mean-value form of the gap -/

/-- On positive arguments the cutoff derivative is nonpositive, so `|K'| = -K'`. -/
theorem abs_deriv_eq_neg_deriv {t : ℝ} (ht : 0 < t) : |deriv M.K t| = -deriv M.K t :=
  abs_of_nonpos (M.deriv_K_nonpos ht)

/-- **The gap to a higher radius is at most the tail derivative times the distance.**  For
`0 < R < s < r`, the mean value theorem gives `K s - K r = |K'(ξ)| (r - s)` with `ξ ∈ (s, r)`;
the tail upper bound `|K'| ≤ 2 t^(-d-α-1)` and monotonicity of the negative power bound
`|K'(ξ)|` by `2 s^(-d-α-1)`. -/
theorem gap_le_of_deriv_bound {R s r : ℝ}
    (hupp : ∀ t : ℝ, R < t → |deriv M.K t| ≤ 2 * t ^ (-(M.d : ℝ) - M.α - 1))
    (hRpos : 0 < R) (hR : R < s) (hsr : s < r) :
    M.K s - M.K r ≤ (2 * s ^ (-(M.d : ℝ) - M.α - 1)) * (r - s) := by
  have hspos : 0 < s := lt_trans hRpos hR
  have hpneg : -(M.d : ℝ) - M.α - 1 ≤ 0 := by
    have h1 : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hcont : ContinuousOn M.K (Set.Icc s r) :=
    M.K_diff.continuousOn.mono fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le hspos hx.1)
  have hdiff : DifferentiableOn ℝ M.K (Set.Ioo s r) :=
    M.K_diff.mono fun x hx => Set.mem_Ioi.mpr (lt_trans hspos hx.1)
  obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope M.K hsr hcont hdiff
  have hξpos : 0 < ξ := lt_trans hspos hξ.1
  have habs : |deriv M.K ξ| = -deriv M.K ξ := M.abs_deriv_eq_neg_deriv hξpos
  have hbound : |deriv M.K ξ| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1) := by
    have h1 := hupp ξ (lt_trans hR hξ.1)
    have h2 : ξ ^ (-(M.d : ℝ) - M.α - 1) ≤ s ^ (-(M.d : ℝ) - M.α - 1) :=
      Real.rpow_le_rpow_of_nonpos hspos hξ.1.le hpneg
    linarith
  have hrsne : r - s ≠ 0 := by linarith
  have hkey : M.K r - M.K s = deriv M.K ξ * (r - s) := by
    rw [hslope]
    field_simp
  have hpos : 0 < r - s := by linarith
  have hfin : M.K s - M.K r = |deriv M.K ξ| * (r - s) := by
    have hneg : M.K s - M.K r = -(M.K r - M.K s) := by ring
    rw [hneg, hkey, habs]
    ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_right hbound hpos.le

/-! ## 3. The one-sided blow-up of `stdDegree` -/

/-- **`stdDegree` is bounded below on the right of an attained radius by the reciprocal of the
distance.**  For `r ∈ (s, s+e)` with `s` an attained radius past the tail threshold,

  `(1/2)(s+e)^(-d-α-1) / (2 s^(-d-α-1) (r-s)) ≤ stdDegree r`,

so `stdDegree` grows at least like `(r-s)⁻¹` there.  The numerator is `-K'(r)` up to the tail
lower bound; the denominator dominates the true gap `K s - K r`, which is a candidate in
`gapFloor r`. -/
theorem le_stdDegree_of_window {R s e : ℝ}
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hupp : ∀ t : ℝ, R < t → |deriv M.K t| ≤ 2 * t ^ (-(M.d : ℝ) - M.α - 1))
    (hRpos : 0 < R) (hR : R < s) (hs : s ∈ M.attainedRadii) (_he : 0 < e) :
    ∀ r ∈ Set.Ioo s (s + e),
      ((1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1)) /
        ((2 * s ^ (-(M.d : ℝ) - M.α - 1)) * (r - s)) ≤ M.stdDegree r := by
  intro r hr
  obtain ⟨hsr, hre⟩ := hr
  have hspos : 0 < s := lt_trans hRpos hR
  have hrpos : 0 < r := lt_trans hspos hsr
  have hRr : R < r := lt_trans hR hsr
  have hpneg : -(M.d : ℝ) - M.α - 1 ≤ 0 := by
    have h1 : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hlowr : (1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1) ≤ -deriv M.K r := by
    have h1 := hlow r hRr
    rw [M.abs_deriv_eq_neg_deriv hrpos] at h1
    have h2 : (s + e) ^ (-(M.d : ℝ) - M.α - 1) ≤ r ^ (-(M.d : ℝ) - M.α - 1) :=
      Real.rpow_le_rpow_of_nonpos hrpos hre.le hpneg
    linarith
  have hgapK : 0 < M.K s - M.K r := by
    have hlt := M.K_lt_of_lt_of_tail hRr hlow hspos hsr
    linarith
  have hgap : M.gapFloor r ≤ M.K s - M.K r := M.gapFloor_le_gap_to_attained hlow hRr hs hsr
  have hKle : M.K s - M.K r ≤ (2 * s ^ (-(M.d : ℝ) - M.α - 1)) * (r - s) :=
    M.gap_le_of_deriv_bound hupp hRpos hR hsr
  have hcpos : (0 : ℝ) < (1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1) := by
    have h : (0 : ℝ) < (s + e) ^ (-(M.d : ℝ) - M.α - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    linarith
  have hden : (0 : ℝ) < (2 * s ^ (-(M.d : ℝ) - M.α - 1)) * (r - s) := by
    have h1 : (0 : ℝ) < s ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hspos _
    have h2 : (0 : ℝ) < r - s := by linarith
    nlinarith
  have hstep1 :
      ((1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1)) /
          ((2 * s ^ (-(M.d : ℝ) - M.α - 1)) * (r - s))
        ≤ ((1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1)) / (M.K s - M.K r) :=
    div_le_div_of_nonneg_left hcpos.le hgapK hKle
  have hstep2 :
      ((1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1)) / (M.K s - M.K r)
        ≤ (-(deriv M.K r)) / M.gapFloor r :=
    div_le_div₀ (M.neg_deriv_K_nonneg hrpos) hlowr (M.gapFloor_pos r) hgap
  have hstep3 :
      (-(deriv M.K r)) / M.gapFloor r
        ≤ ((M.ball r).ncard : ℝ) * (-(deriv M.K r)) / M.gapFloor r := by
    have h1 : (0 : ℝ) ≤ (-(deriv M.K r)) / M.gapFloor r :=
      div_nonneg (M.neg_deriv_K_nonneg hrpos) (M.gapFloor_pos r).le
    have h2 : (1 : ℝ) ≤ ((M.ball r).ncard : ℝ) := by
      have := M.one_le_ncard_ball hrpos
      exact_mod_cast this
    calc (-(deriv M.K r)) / M.gapFloor r
        = 1 * ((-(deriv M.K r)) / M.gapFloor r) := by ring
      _ ≤ ((M.ball r).ncard : ℝ) * ((-(deriv M.K r)) / M.gapFloor r) :=
          mul_le_mul_of_nonneg_right h2 h1
      _ = ((M.ball r).ncard : ℝ) * (-(deriv M.K r)) / M.gapFloor r := by
          rw [mul_div_assoc]
  exact hstep1.trans (hstep2.trans hstep3)

/-- **`stdDegree` is unbounded above on every right-neighbourhood of an attained radius past the
tail threshold.** -/
theorem exists_stdDegree_gt {R s e C : ℝ}
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hupp : ∀ t : ℝ, R < t → |deriv M.K t| ≤ 2 * t ^ (-(M.d : ℝ) - M.α - 1))
    (hRpos : 0 < R) (hR : R < s) (hs : s ∈ M.attainedRadii) (he : 0 < e) :
    ∃ r ∈ Set.Ioo s (s + e), C < M.stdDegree r := by
  have hspos : 0 < s := lt_trans hRpos hR
  have hcpos : (0 : ℝ) < (1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1) := by
    have h : (0 : ℝ) < (s + e) ^ (-(M.d : ℝ) - M.α - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    linarith
  have hKpos : (0 : ℝ) < 2 * s ^ (-(M.d : ℝ) - M.α - 1) := by
    have h1 : (0 : ℝ) < s ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hspos _
    linarith
  set c : ℝ := (1 / 2) * (s + e) ^ (-(M.d : ℝ) - M.α - 1) with hcdef
  set Mγ : ℝ := 2 * s ^ (-(M.d : ℝ) - M.α - 1) with hMγdef
  have hApos : 0 < c / (Mγ * (max C 0 + 1)) := by
    have h1 : (0 : ℝ) < max C 0 + 1 := by positivity
    have : 0 < Mγ * (max C 0 + 1) := mul_pos hKpos h1
    exact div_pos hcpos this
  set t : ℝ := min (e / 2) (c / (Mγ * (max C 0 + 1))) with htdef
  have htpos : 0 < t := lt_min (by linarith) hApos
  have htle : t ≤ c / (Mγ * (max C 0 + 1)) := min_le_right _ _
  have htlt : t < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨s + t, ⟨by linarith, by linarith⟩, ?_⟩
  have hwindow := M.le_stdDegree_of_window hlow hupp hRpos hR hs he (s + t) ⟨by linarith, by linarith⟩
  have hsub : s + t - s = t := by ring
  rw [hsub] at hwindow
  refine lt_of_lt_of_le ?_ hwindow
  have hden : Mγ * t ≤ Mγ * (c / (Mγ * (max C 0 + 1))) :=
    mul_le_mul_of_nonneg_left htle hKpos.le
  have hdenpos : (0 : ℝ) < Mγ * t := mul_pos hKpos htpos
  have hdenpos' : (0 : ℝ) < Mγ * (c / (Mγ * (max C 0 + 1))) := by
    have h1 : (0 : ℝ) < max C 0 + 1 := by positivity
    exact mul_pos hKpos (div_pos hcpos (mul_pos hKpos h1))
  have hmono : c / (Mγ * (c / (Mγ * (max C 0 + 1)))) ≤ c / (Mγ * t) :=
    div_le_div_of_nonneg_left hcpos.le hdenpos hden
  have hval : c / (Mγ * (c / (Mγ * (max C 0 + 1)))) = max C 0 + 1 := by
    have h1 : (0 : ℝ) < max C 0 + 1 := by positivity
    have hne : c ≠ 0 := hcpos.ne'
    have hne2 : Mγ ≠ 0 := hKpos.ne'
    have hne3 : max C 0 + 1 ≠ 0 := h1.ne'
    field_simp
  rw [hval] at hmono
  have hCle : C ≤ max C 0 := le_max_left C 0
  linarith

/-! ## 4. The strongest correct positive statement: separation from attained radii -/

/-- **A separated radius has a positive gap floor.**  If `0 < R < a ≤ r ≤ b` and every attained
radius `s < r` satisfies `ε ≤ r - s` (so `r` is at distance at least `ε` above all attained radii
below it), then every strictly positive support gap at `r` is at least

  `δ = (1/2) b^(-d-α-1) · min ε (a - R)`,

because the gap `K s - K r` is `|K'(ξ)|(r-s)` by the mean value theorem and `|K'|` is bounded below
by `(1/2) b^(-d-α-1)` on `(R, b]`.  The gap floor is at least `min δ 1` (the `1` is the default
of `gapFloor` when no gap is positive). -/
theorem gapFloor_ge_of_separated {R a b ε r : ℝ}
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hRpos : 0 < R) (hRa : R < a) (har : a ≤ r) (hrb : r ≤ b) (hε : 0 < ε)
    (hsep : ∀ s ∈ M.attainedRadii, s < r → ε ≤ r - s) :
    min ((1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R)) 1 ≤ M.gapFloor r := by
  classical
  have h0 : (0 : ℝ) < M.d + M.α := by
    have h1 : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hpneg : -(M.d : ℝ) - M.α - 1 ≤ 0 := by linarith
  have hbpos : 0 < b := lt_of_lt_of_le (lt_trans hRpos hRa) (le_trans har hrb)
  have hcoef : (0 : ℝ) < (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) := by
    have h : (0 : ℝ) < b ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hbpos _
    linarith
  set δ : ℝ := (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R) with hδdef
  have hεle : min ε (a - R) ≤ ε := min_le_left _ _
  have hRle : min ε (a - R) ≤ a - R := min_le_right _ _
  have hδcoef : δ ≤ (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * ε := by
    have h := hcoef
    simp only [hδdef]
    exact mul_le_mul_of_nonneg_left hεle hcoef.le
  have hδR : δ ≤ (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * (a - R) := by
    simp only [hδdef]
    exact mul_le_mul_of_nonneg_left hRle hcoef.le
  -- every positive support gap is at least `δ`
  have hkey : ∀ s ∈ M.posGapRadii r, δ ≤ M.K s - M.K r := by
    intro s hs
    obtain ⟨⟨hsA, hsr⟩, -⟩ := hs
    have hspos : 0 < s := M.attainedRadii_pos hsA
    have hdist : ε ≤ r - s := hsep s hsA hsr
    have hMLow : ∀ t : ℝ, R < t → t ≤ b → (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t| := by
      intro t ht htb
      have h1 : (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) ≤ (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) := by
        have h2 : b ^ (-(M.d : ℝ) - M.α - 1) ≤ t ^ (-(M.d : ℝ) - M.α - 1) :=
          Real.rpow_le_rpow_of_nonpos (lt_trans hRpos ht) htb hpneg
        linarith
      have h3 : (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t| := hlow t ht
      linarith
    rcases le_or_gt R s with hsR | hsR
    · -- `s ≥ R`: mean value theorem on `[s, r]`
      have hcont : ContinuousOn M.K (Set.Icc s r) :=
        M.K_diff.continuousOn.mono fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le hspos hx.1)
      have hdiff : DifferentiableOn ℝ M.K (Set.Ioo s r) :=
        M.K_diff.mono fun x hx => Set.mem_Ioi.mpr (lt_trans hspos hx.1)
      obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope M.K hsr hcont hdiff
      have hRξ : R < ξ := lt_of_le_of_lt hsR hξ.1
      have hlowξ : (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K ξ| :=
        hMLow ξ hRξ (le_of_lt (lt_of_lt_of_le hξ.2 hrb))
      have hgapEq : M.K s - M.K r = |deriv M.K ξ| * (r - s) := by
        have hkey2 : M.K r - M.K s = deriv M.K ξ * (r - s) := by
          rw [hslope]; field_simp
        have hξpos : 0 < ξ := lt_trans hRpos hRξ
        have habs : |deriv M.K ξ| = -deriv M.K ξ := M.abs_deriv_eq_neg_deriv hξpos
        have hneg : M.K s - M.K r = -(M.K r - M.K s) := by ring
        rw [hneg, hkey2, habs]; ring
      rw [hgapEq]
      calc δ ≤ (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * ε := hδcoef
        _ ≤ |deriv M.K ξ| * (r - s) := by
            exact mul_le_mul hlowξ hdist (by linarith) (abs_nonneg _)
    · -- `s < R`: the monotone step to `R` and the mean value theorem on `[R, r]`
      have hKR : M.K R ≤ M.K s :=
        M.K_antitone (Set.mem_Ioi.mpr hspos) (Set.mem_Ioi.mpr hRpos) hsR.le
      have hRr : R < r := lt_of_lt_of_le hRa har
      have hcont : ContinuousOn M.K (Set.Icc R r) :=
        M.K_diff.continuousOn.mono fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le hRpos hx.1)
      have hdiff : DifferentiableOn ℝ M.K (Set.Ioo R r) :=
        M.K_diff.mono fun x hx => Set.mem_Ioi.mpr (lt_trans hRpos hx.1)
      obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope M.K hRr hcont hdiff
      have hlowξ : (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K ξ| :=
        hMLow ξ hξ.1 (le_of_lt (lt_of_lt_of_le hξ.2 hrb))
      have hgapEq : M.K R - M.K r = |deriv M.K ξ| * (r - R) := by
        have hkey2 : M.K r - M.K R = deriv M.K ξ * (r - R) := by
          rw [hslope]; field_simp
        have hξpos : 0 < ξ := lt_trans hRpos hξ.1
        have habs : |deriv M.K ξ| = -deriv M.K ξ := M.abs_deriv_eq_neg_deriv hξpos
        have hneg : M.K R - M.K r = -(M.K r - M.K R) := by ring
        rw [hneg, hkey2, habs]; ring
      have hmono : M.K R - M.K r ≤ M.K s - M.K r := by linarith
      have hRdist : a - R ≤ r - R := by linarith
      calc δ ≤ (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * (a - R) := hδR
        _ ≤ |deriv M.K ξ| * (r - R) := by
            exact mul_le_mul hlowξ hRdist (by linarith [hRa]) (abs_nonneg _)
        _ = M.K R - M.K r := hgapEq.symm
        _ ≤ M.K s - M.K r := hmono
  unfold gapFloor
  split_ifs with hne
  · have hle : δ ≤ (M.posGapRadiiFinset r).inf' hne (fun s => M.K s - M.K r) :=
      Finset.le_inf' hne (f := fun s => M.K s - M.K r)
        (fun s hs => hkey s ((M.mem_posGapRadiiFinset).mp hs))
    exact le_trans (min_le_left _ _) hle
  · exact le_trans (min_le_right _ _) le_rfl

/-- **The conditional radius-local-uniform bound.**  With the same separation hypothesis,
`stdDegree` is bounded on `[a, b]` by the explicit constant

  `#(ball r) · 2 a^(-d-α-1) / ((1/2) b^(-d-α-1) · min ε (a - R))`.

The blow-up theorems below show that the separation hypothesis cannot be dropped. -/
theorem stdDegree_le_of_separated {R a b ε r : ℝ}
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hupp : ∀ t : ℝ, R < t → |deriv M.K t| ≤ 2 * t ^ (-(M.d : ℝ) - M.α - 1))
    (hRpos : 0 < R) (hRa : R < a) (har : a ≤ r) (hrb : r ≤ b) (hε : 0 < ε)
    (hsep : ∀ s ∈ M.attainedRadii, s < r → ε ≤ r - s) :
    M.stdDegree r ≤ ((M.ball r).ncard : ℝ) * (2 * a ^ (-(M.d : ℝ) - M.α - 1)) /
      min ((1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R)) 1 := by
  have hapos : 0 < a := lt_trans hRpos hRa
  have hrpos : 0 < r := lt_of_lt_of_le hapos har
  have hbpos : 0 < b := lt_of_lt_of_le hapos (le_trans har hrb)
  have hRr : R < r := lt_of_lt_of_le hRa har
  have hpneg : -(M.d : ℝ) - M.α - 1 ≤ 0 := by
    have h1 : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hcoef : (0 : ℝ) < (1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) := by
    have h : (0 : ℝ) < b ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hbpos _
    linarith
  have hεle : min ε (a - R) ≤ ε := min_le_left _ _
  have hminpos : (0 : ℝ) < min ε (a - R) := lt_min hε (by linarith)
  have hδpos : (0 : ℝ) < min ((1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R)) 1 :=
    lt_min (mul_pos hcoef hminpos) one_pos
  have hγ : min ((1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R)) 1 ≤ M.gapFloor r :=
    M.gapFloor_ge_of_separated hlow hRpos hRa har hrb hε hsep
  have hKup : -(deriv M.K r) ≤ 2 * a ^ (-(M.d : ℝ) - M.α - 1) := by
    have h1 := hupp r hRr
    rw [M.abs_deriv_eq_neg_deriv hrpos] at h1
    have h2 : r ^ (-(M.d : ℝ) - M.α - 1) ≤ a ^ (-(M.d : ℝ) - M.α - 1) :=
      Real.rpow_le_rpow_of_nonpos hapos har hpneg
    linarith
  have hKnonneg : (0 : ℝ) ≤ -(deriv M.K r) := M.neg_deriv_K_nonneg hrpos
  have hnum_nonneg : (0 : ℝ) ≤ 2 * a ^ (-(M.d : ℝ) - M.α - 1) := by
    have h : (0 : ℝ) < a ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hapos _
    linarith
  have hratio : (-(deriv M.K r)) / M.gapFloor r ≤
      (2 * a ^ (-(M.d : ℝ) - M.α - 1)) /
        min ((1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R)) 1 :=
    div_le_div₀ hnum_nonneg hKup hδpos hγ
  have hnc : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := Nat.cast_nonneg _
  calc M.stdDegree r
      = ((M.ball r).ncard : ℝ) * ((-(deriv M.K r)) / M.gapFloor r) := by
        rw [stdDegree, mul_div_assoc]
    _ ≤ ((M.ball r).ncard : ℝ) *
          ((2 * a ^ (-(M.d : ℝ) - M.α - 1)) /
            min ((1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R)) 1) :=
        mul_le_mul_of_nonneg_left hratio hnc
    _ = ((M.ball r).ncard : ℝ) * (2 * a ^ (-(M.d : ℝ) - M.α - 1)) /
          min ((1 / 2) * b ^ (-(M.d : ℝ) - M.α - 1) * min ε (a - R)) 1 := by
        ring

/-! ## 5. Attained radii are unbounded, so the failure recurs at every scale -/

/-- **Attained radii are unbounded above**: `ρ (n • v) = n · ρ v` on the lattice. -/
theorem exists_attainedRadii_gt (B : ℝ) : ∃ s ∈ M.attainedRadii, B < s := by
  classical
  obtain ⟨v₁, hv₁⟩ : ∃ v : M.V, v ≠ 0 := by
    obtain ⟨i₀⟩ : Nonempty (Fin M.d) := ⟨⟨0, M.hd⟩⟩
    exact ⟨Pi.single i₀ (1 : ℤ), by
      intro h
      have h1 : (Pi.single i₀ (1 : ℤ) : M.V) i₀ = (0 : M.V) i₀ := by rw [h]
      simp at h1⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, v₁ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₁ (funext h)
  have htv : toVec v₁ ≠ 0 := by
    intro h
    exact hi₀ (by
      have h1 : ((v₁ i₀ : ℤ) : ℝ) = 0 := by
        have := congrFun h i₀
        simpa [toVec] using this
      exact_mod_cast h1)
  have hρpos : 0 < M.S.ρ (toVec v₁) := M.S.ρ_pos (toVec v₁) htv
  obtain ⟨n, hn⟩ : ∃ n : ℕ, B / M.S.ρ (toVec v₁) < n ∧ 1 ≤ n := by
    obtain ⟨m, hm⟩ := exists_nat_gt (B / M.S.ρ (toVec v₁))
    exact ⟨m + 1, by push_cast; linarith, by omega⟩
  have hn0 : (n : ℤ) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.2
      positivity
    exact_mod_cast this
  have hne : (n : ℤ) • v₁ ≠ 0 := by
    intro h
    have h1 := congrFun h i₀
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1
    exact mul_ne_zero hn0 hi₀ h1
  have hsmul : toVec ((n : ℤ) • v₁) = (n : ℝ) • toVec v₁ := by
    funext i
    simp only [toVec, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hrad : M.S.dist ((n : ℤ) • v₁) 0 = (n : ℝ) * M.S.ρ (toVec v₁) := by
    rw [SourceNormData.dist_zero_right, hsmul, M.S.ρ_smul, abs_of_nonneg (by positivity)]
  refine ⟨M.S.dist ((n : ℤ) • v₁) 0, M.mem_attainedRadii.mpr ⟨_, hne, rfl⟩, ?_⟩
  rw [hrad]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.2
  have h2 : B < (n : ℝ) * M.S.ρ (toVec v₁) := (div_lt_iff₀ hρpos).mp hn.1
  linarith

/-- **No uniform bound on a compact interval that contains an attained radius past the tail
threshold strictly inside it.** -/
theorem not_bddAbove_stdDegree_Ioo {R a b s : ℝ}
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hupp : ∀ t : ℝ, R < t → |deriv M.K t| ≤ 2 * t ^ (-(M.d : ℝ) - M.α - 1))
    (hRpos : 0 < R) (hR : R < s) (hs : s ∈ M.attainedRadii) (has : a < s) (hsb : s < b) :
    ¬ BddAbove (M.stdDegree '' Set.Ioo a b) := by
  rintro ⟨C, hC⟩
  obtain ⟨r, hr, hgt⟩ := M.exists_stdDegree_gt hlow hupp hRpos hR hs (e := b - s) (C := C) (by linarith)
  have hmem : r ∈ Set.Ioo a b := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have : M.stdDegree r ≤ C := hC ⟨r, hmem, rfl⟩
  linarith

/-- **Every pointwise majorant of `stdDegree` is unbounded on such a window.**  This is the
precise half of "bounded compact part + integrable tail" that fails: a function dominating
`stdDegree` pointwise cannot be bounded on a compact interval containing an attained radius past
the tail threshold strictly inside it.  It says nothing about integrability. -/
theorem not_bddAbove_of_stdDegree_le {R a b s : ℝ}
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hupp : ∀ t : ℝ, R < t → |deriv M.K t| ≤ 2 * t ^ (-(M.d : ℝ) - M.α - 1))
    (hRpos : 0 < R) (hR : R < s) (hs : s ∈ M.attainedRadii) (has : a < s) (hsb : s < b)
    {C : ℝ → ℝ} (hC : ∀ r : ℝ, M.stdDegree r ≤ C r) :
    ¬ BddAbove (C '' Set.Ioo a b) := by
  rintro ⟨B, hB⟩
  refine M.not_bddAbove_stdDegree_Ioo hlow hupp hRpos hR hs has hsb ⟨B, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact le_trans (hC r) (hB ⟨r, hr, rfl⟩)

/-- **The failure recurs at every scale**: above every bound `B` there is an attained radius `s`
such that `stdDegree` is unbounded above on `(s-1, s+1)`.  This is *not* a non-integrability
statement — an integrable function may be unbounded on infinitely many windows at infinity — it
only says that no majorant can be bounded on those compact windows. -/
theorem exists_unbounded_stdDegree_window (B : ℝ) :
    ∃ s ∈ M.attainedRadii, B < s ∧ ¬ BddAbove (M.stdDegree '' Set.Ioo (s - 1) (s + 1)) := by
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  obtain ⟨s, hs, hsB⟩ := M.exists_attainedRadii_gt (max B R)
  have hBs : B < s := lt_of_le_of_lt (le_max_left B R) hsB
  have hRs : R < s := lt_of_le_of_lt (le_max_right B R) hsB
  exact ⟨s, hs, hBs,
    M.not_bddAbove_stdDegree_Ioo hlow hupp hRpos hRs hs (by linarith) (by linarith)⟩

/-! ## 6. The `r^(-1-α)` tail majorant is false -/

/-- **There is no eventual bound `stdDegree r ≤ C r^(-d-α-1)`.**  Such a bound is what a
`r^(-1-α)` tail estimate (`#(ball r) ≈ r^d` times `|K'| ≈ r^(-d-α-1)` divided by a bounded gap
floor) would give; it is a sufficient, not a necessary, condition for integrability, and it is
unavailable.  It fails: above any scale
there is an attained radius `s₀` with

  `stdDegree r ≥ (1/4) (s₀/(s₀+1))^(d+α+1) (r - s₀)⁻¹`   on `(s₀, s₀+1)`

(`le_stdDegree_of_window` with `e = 1`), while `r^(-d-α-1) ≤ s₀^(-d-α-1)` there; the constant only
degenerates as `s₀ → 0`, so it is `≥ (1/4) 2^(-(d+α+1))` once `s₀ ≥ 1`. -/
theorem not_eventually_le_const_mul_rpow :
    ¬ ∃ (C r₀ : ℝ), ∀ r ∈ Set.Ioi r₀,
      M.stdDegree r ≤ C * r ^ (-(M.d : ℝ) - M.α - 1) := by
  rintro ⟨C, r₀, hC⟩
  obtain ⟨R, hRpos, -, hlow, hupp⟩ := M.exists_deriv_bounds
  obtain ⟨s, hs, hsB⟩ := M.exists_attainedRadii_gt (max r₀ R)
  have hr₀s : r₀ < s := lt_of_le_of_lt (le_max_left r₀ R) hsB
  have hRs : R < s := lt_of_le_of_lt (le_max_right r₀ R) hsB
  have hspos : 0 < s := M.attainedRadii_pos hs
  set C' : ℝ := |C| * s ^ (-(M.d : ℝ) - M.α - 1) + 1 with hC'def
  obtain ⟨r, hr, hgt⟩ :=
    M.exists_stdDegree_gt hlow hupp hRpos hRs hs (e := 1) (C := C') one_pos
  obtain ⟨hsr, hsr1⟩ := hr
  have hr₀r : r₀ < r := lt_trans hr₀s hsr
  have hbound := hC r (Set.mem_Ioi.mpr hr₀r)
  have hmono : r ^ (-(M.d : ℝ) - M.α - 1) ≤ s ^ (-(M.d : ℝ) - M.α - 1) := by
    refine Real.rpow_le_rpow_of_nonpos hspos hsr.le ?_
    have h1 : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hCs : C * r ^ (-(M.d : ℝ) - M.α - 1) ≤ C' := by
    have h1 : C * r ^ (-(M.d : ℝ) - M.α - 1) ≤ |C| * r ^ (-(M.d : ℝ) - M.α - 1) := by
      have h2 : (0 : ℝ) ≤ r ^ (-(M.d : ℝ) - M.α - 1) :=
        le_of_lt (Real.rpow_pos_of_pos (lt_trans hspos hsr) _)
      nlinarith [le_abs_self C, neg_abs_le C]
    have h2 : |C| * r ^ (-(M.d : ℝ) - M.α - 1) ≤ |C| * s ^ (-(M.d : ℝ) - M.α - 1) :=
      mul_le_mul_of_nonneg_left hmono (abs_nonneg C)
    simp only [hC'def]
    linarith
  linarith

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 7. Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.gapFloor_le_gap_to_attained
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_ncard_ball
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_deriv_eq_neg_deriv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.gap_le_of_deriv_bound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.le_stdDegree_of_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_stdDegree_gt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.gapFloor_ge_of_separated
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.stdDegree_le_of_separated
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_attainedRadii_gt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_bddAbove_stdDegree_Ioo
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_bddAbove_of_stdDegree_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_unbounded_stdDegree_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_eventually_le_const_mul_rpow
