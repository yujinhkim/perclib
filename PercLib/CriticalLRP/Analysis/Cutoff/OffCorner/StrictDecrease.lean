module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.Defs

/-!
# Strict decrease of the source profile past the tail threshold

Swarm `smwu19308`, member `m1`.

`SourceModelData.exists_deriv_bounds` gives `R > 0` with `|K' t| ≥ (1/2) t^(-d-α-1)` for `t > R`.
We never integrate: it is enough that `K` cannot be flat on a nondegenerate interval that reaches
past `R`.  If `0 < s < r`, `R < r` and `K s = K r`, antitonicity forces `K` to be constant on
`[s, r]`, hence `deriv K t = 0` for every `t ∈ (s, r)`; but `t = (max s R + r)/2` lies in that
interval *and* past `R`, where `|K' t| > 0`.  So `K r < K s`.

No global positivity of `deriv K` is assumed anywhere.  The tail hypothesis is necessary: the
structure allows `δ ≡ -1` on a bounded interval, hence a flat piece of `K` near `0`.
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

/-! ## 1. Strict decrease past the tail threshold -/

/-- **Strict decrease of `K` on positive arguments below a radius past the tail threshold.**
-/
theorem K_lt_of_lt_of_tail {R s r : ℝ} (hR : R < r)
    (hlow : ∀ t : ℝ, R < t → (1 / 2) * t ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K t|)
    (hs : 0 < s) (hsr : s < r) : M.K r < M.K s := by
  have hrpos : 0 < r := lt_trans hs hsr
  by_contra hcon
  push Not at hcon
  have hle : M.K r ≤ M.K s :=
    M.K_antitone (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr hrpos) hsr.le
  have hK : ∀ u ∈ Set.Ioo s r, M.K u = M.K s := by
    intro u hu
    have hu1 : s < u := hu.1
    have hu2 : u < r := hu.2
    have h1 : M.K u ≤ M.K s :=
      M.K_antitone (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr (lt_trans hs hu1)) hu1.le
    have h2 : M.K r ≤ M.K u :=
      M.K_antitone (Set.mem_Ioi.mpr (lt_trans hs hu1)) (Set.mem_Ioi.mpr hrpos) hu2.le
    exact le_antisymm h1 (le_trans hcon h2)
  set t : ℝ := (max s R + r) / 2 with htdef
  have hmaxr : max s R < r := max_lt hsr hR
  have hRt : R < t := by rw [htdef]; linarith [le_max_right s R]
  have hst : s < t := by rw [htdef]; linarith [le_max_left s R]
  have htr : t < r := by rw [htdef]; linarith
  have hev : M.K =ᶠ[𝓝 t] (fun _ => M.K s) := by
    have hopen : Set.Ioo s r ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hst, htr⟩
    filter_upwards [hopen] with u hu using hK u hu
  have hderiv0 : deriv M.K t = 0 := by
    rw [hev.deriv_eq]
    simp
  have ht0 : 0 < t := lt_trans hs hst
  have hpow : 0 < t ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos ht0 _
  have hlowt := hlow t hRt
  rw [hderiv0, abs_zero] at hlowt
  nlinarith

/-- **A flat left-neighbourhood forces a vanishing derivative.**  If `K` is constant on
`(lo, r)`, then the left difference quotients at `r` are eventually `0`; since `K` is
differentiable at `r`, the derivative is the limit of those quotients and therefore `0`.

This is the fact that removes any strict-decrease hypothesis from the open-probability
compatibility: a support edge with vanishing kernel gap makes `K` flat on `[s, r]`, and then the
cutoff derivative weight `β_c(-K'(r))·exp(-β_c J_r(e))` vanishes as well. -/
theorem deriv_eq_zero_of_flat_left {lo r : ℝ} (hlr : lo < r) (hr : 0 < r)
    (hconst : ∀ u : ℝ, lo < u → u < r → M.K u = M.K r) : deriv M.K r = 0 := by
  have hd : HasDerivAt M.K (deriv M.K r) r :=
    (M.K_diff.differentiableAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hr))).hasDerivAt
  have hleft : Tendsto (slope M.K r) (𝓝[<] r) (𝓝 (deriv M.K r)) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  have hmem : Set.Ioo lo r ∈ 𝓝[<] r := by
    have h1 : Set.Ioo lo (r + 1) ∈ 𝓝[<] r :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ⟨hlr, by linarith⟩)
    have h2 : Set.Iio r ∈ 𝓝[<] r := self_mem_nhdsWithin
    refine mem_of_superset (inter_mem h1 h2) ?_
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    exact ⟨hx1, hx3⟩
  have hzero : Tendsto (slope M.K r) (𝓝[<] r) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hmem] with y hy
    show (0 : ℝ) = slope M.K r y
    simp [slope, hconst y hy.1 hy.2]
  exact tendsto_nhds_unique hleft hzero

/-- The source profile is nonincreasing at positive arguments (`deriv K r ≤ 0`). -/
theorem deriv_K_nonpos {r : ℝ} (hr : 0 < r) : deriv M.K r ≤ 0 := by
  have h1 : derivWithin M.K (Set.Ioi 0) r ≤ 0 := M.K_antitone.derivWithin_nonpos
  rwa [derivWithin_of_isOpen isOpen_Ioi (Set.mem_Ioi.mpr hr)] at h1

/-- The cutoff derivative weight is nonnegative at every positive radius. -/
theorem neg_deriv_K_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ -(deriv M.K r) := by
  linarith [M.deriv_K_nonpos hr]

/-! ## 2. The gap floor -/

/-- **The gap floor is strictly positive at every radius.** -/
theorem gapFloor_pos (r : ℝ) : 0 < M.gapFloor r := by
  unfold gapFloor
  split_ifs with hne
  · rw [Finset.lt_inf'_iff]
    intro s hs
    exact ((M.mem_posGapRadiiFinset).mp hs).2
  · norm_num

/-- **The gap floor is a lower bound for every strictly positive support kernel gap.** -/
theorem gapFloor_le_of_pos {r s : ℝ} (hs : s ∈ M.posGapRadii r) :
    M.gapFloor r ≤ M.K s - M.K r := by
  unfold gapFloor
  split_ifs with hne
  · exact Finset.inf'_le _ ((M.mem_posGapRadiiFinset).mpr hs)
  · exact absurd ⟨s, (M.mem_posGapRadiiFinset).mpr hs⟩ hne

/-- **The degree constant is nonnegative.** -/
theorem stdDegree_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ M.stdDegree r := by
  unfold stdDegree
  have h1 : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := Nat.cast_nonneg _
  exact div_nonneg (mul_nonneg h1 (M.neg_deriv_K_nonneg hr)) (M.gapFloor_pos r).le

end SourceModelData

end PercLib.CriticalLRP.Orchestration
