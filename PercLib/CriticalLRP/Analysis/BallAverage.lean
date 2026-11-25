/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from independent submission `smwp648b3` direction D3, with its
measurability gap discharged by the new monotone-finite ballSum wrapper.
-/

/-
# Proposition I.4.2, step `I.4.2.s3`: from the log-integrability of `∇_r` to the
normalized open-triangle ball sum `r^{-d} Σ_{x ∈ B_r} ∇(0,x)`

Source: Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  In the course of the proof of Proposition I.4.2 (p. 24):

  "Moreover, `r^{-d} Σ_{x ∈ B_r} ∇(0,x)` is logarithmically integrable whenever
   `∇_r` is by a simple variation on Lemma I.4.13."

with the definitions of section I.4 (p. 17)

  `∇_β(0,x) = Σ_{y,z} P_β(0↔y) P_β(y↔z) P_β(z↔x)`,
  `∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`.

`∇_r` is a *tail supremum*, so the "simple variation" is not the `r^a ∫_r^∞`
transform of Lemma I.4.13 itself; the two-scale split at `R = √r` recorded in the
campaign's reconstruction of `hutchcroft.i.4.2.s3` is what is proved here:

  `r^{-d} Σ_{x ∈ B_r} ∇(0,x) ≤ 2^d ( ∇(0,0) r^{-d/2} + ∇_{√r} )`   (`r` large),

using only `|B_r| ≤ 2^d r^d`, `∇(0,x) ≤ ∇(0,0)` (finiteness of the triangle
diagram) and `∇(0,x) ≤ ∇_{‖x‖}` (the definition of the tail supremum).  Both
summands are log-integrable: `∫_1^∞ r^{-d/2-1} dr < ∞` for `d ≥ 1`, and

  `∫_1^∞ ∇_{√r} dr/r = 2 ∫_1^∞ ∇_u du/u`

by the one-dimensional change of variables `u = √r`.

## What is and is not claimed

* The result is stated with the paper's own inputs: finiteness of the triangle
  diagram (`∇_{β_c} < ∞`, here `∇_0 < ∞`) and log-integrability of `r ↦ ∇_r`.
  It says nothing about `∇_r → 0`; that is `hutchcroft.a.tri.tail`, a separate
  obligation (`nablaSup` is antitone in `r`, see `nablaSup_anti`).
* `openTriangleNabla` is the configured model's `∇_{β_c}(0,x)`, written as the
  three-fold convolution of `M.twoPoint` in `ℝ≥0∞`.  The `def`s of this file are
  candidates for `PercLib/CriticalLRP/Orchestration/Defs.lean` (the repository
  requires new definitions to live in `Basic.lean`/`Defs.lean`); everything after
  them is proof-only.
* The main conclusion is stated as finiteness of
  `∫⁻ r in Ioi R, r^{-d} (Σ_{x ∈ B_r} ∇(0,x)) / r`, which needs *no*
  measurability of the averaged sum (`lintegral_mono` is unconditional).  The
  translation to the repository's `ℝ`-valued `Analysis.LogarithmicallyIntegrable`
  is `logIntegrable_ballAverage` below (via
  `integrableOn_of_lintegral_ne_top`), where the measurability premise is
  carried explicitly (the convention of
  `VolumeMoments/FirstMoment/LogIntegrability.lean`).
-/
module

public import PercLib.CriticalLRP.Analysis.BallAverage.Defs
public import PercLib.CriticalLRP.LatticeGeometry.Cell.Scaling
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.LogIntegrability
public import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.BallAverage

open PercLib.CriticalLRP.Orchestration

/-! ## Elementary facts about the configured norm and its balls -/
theorem rho_nonneg {d : ℕ} (S : SourceNormData d) (x : Fin d → ℤ) : 0 ≤ S.ρ (toVec x) := by
  by_cases h : toVec x = (0 : Fin d → ℝ)
  · rw [h, S.ρ_zero]
  · exact (S.ρ_pos _ h).le

theorem ball_mono (M : SourceModelData) {s r : ℝ} (h : s ≤ r) : M.ball s ⊆ M.ball r :=
  fun _ hy => le_trans hy h

theorem exists_cube_bound (M : SourceModelData) :
    ∃ C : ℝ, ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C :=
  PercLib.CriticalLRP.LatticeGeometry.exists_unitCube_upper_bound M.S.ρ M.S.ρ_continuous

theorem cube_bound_nonneg (M : SourceModelData) {C : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C) : 0 ≤ C := by
  have h := hC 0 (fun _ => ⟨le_refl 0, zero_lt_one⟩)
  rw [M.S.ρ_zero] at h
  exact h

theorem volume_ball_ne_top (M : SourceModelData) {R : ℝ} (hR : 0 < R) :
    volume {x : Fin M.d → ℝ | M.S.ρ x ≤ R} ≠ ∞ := by
  have hv : volume {x : Fin M.d → ℝ | M.S.ρ x ≤ R} = ENNReal.ofReal (R ^ M.d) :=
    PercLib.CriticalLRP.LatticeGeometry.volume_rhoBall M.S.ρ_smul M.S.unitBall_volume hR
  rw [hv]
  exact ENNReal.ofReal_ne_top

/-- The lattice balls of the configured norm are finite. -/
theorem ball_finite (M : SourceModelData) (r : ℝ) : (M.ball r).Finite := by
  obtain ⟨C, hC⟩ := exists_cube_bound M
  have hC0 := cube_bound_nonneg M hC
  refine Set.Finite.subset
    (PercLib.CriticalLRP.LatticeGeometry.integer_centers_finite_of_volume_ne_top
      (d := M.d) (ρ := M.S.ρ) (C := C) (r := max r 0 + 1) M.S.ρ_add_le M.S.ρ_neg hC ?_) ?_
  · apply volume_ball_ne_top M
    have h1 : (0 : ℝ) ≤ max r 0 := le_max_right _ _
    linarith
  · intro y hy
    have hle : r ≤ max r 0 + 1 := by
      have := le_max_left r (0 : ℝ)
      linarith
    exact le_trans hy hle

/-- Upper half of Lemma I.4.6 beyond the cube constant: `|B_r| ≤ (r+C)^d`. -/
theorem ball_ncard_le (M : SourceModelData) {C r : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hrC : C < r) :
    ((M.ball r).ncard : ℝ) ≤ (r + C) ^ M.d :=
  (PercLib.CriticalLRP.LatticeGeometry.ncard_integer_centers_sandwich_real (d := M.d)
    (ρ := M.S.ρ) (C := C) (r := r) M.S.ρ_add_le M.S.ρ_neg hC M.S.ρ_smul M.S.unitBall_volume
    hC0 hrC).2

/-- Lower half of Lemma I.4.6 beyond the cube constant: `(r-C)^d ≤ |B_r|`. -/
theorem ball_ncard_ge (M : SourceModelData) {C r : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hrC : C < r) :
    (r - C) ^ M.d ≤ ((M.ball r).ncard : ℝ) :=
  (PercLib.CriticalLRP.LatticeGeometry.ncard_integer_centers_sandwich_real (d := M.d)
    (ρ := M.S.ρ) (C := C) (r := r) M.S.ρ_add_le M.S.ρ_neg hC M.S.ρ_smul M.S.unitBall_volume
    hC0 hrC).1

/-! ## The tail supremum `∇_r` -/

theorem le_nablaSup (M : SourceModelData) {f : M.V → ℝ≥0∞} {r : ℝ} {x : M.V}
    (h : r ≤ M.S.ρ (toVec x)) : f x ≤ nablaSup M f r :=
  le_iSup₂ (f := fun x (_ : r ≤ M.S.ρ (toVec x)) => f x) x h

theorem nablaSup_le_iff (M : SourceModelData) {f : M.V → ℝ≥0∞} {r : ℝ} {a : ℝ≥0∞} :
    nablaSup M f r ≤ a ↔ ∀ x : M.V, r ≤ M.S.ρ (toVec x) → f x ≤ a :=
  iSup₂_le_iff

theorem nablaSup_anti (M : SourceModelData) (f : M.V → ℝ≥0∞) {r s : ℝ} (h : r ≤ s) :
    nablaSup M f s ≤ nablaSup M f r :=
  (nablaSup_le_iff M).mpr fun x hx => le_nablaSup M (le_trans h hx)

theorem le_nablaSup_zero (M : SourceModelData) (f : M.V → ℝ≥0∞) (x : M.V) :
    f x ≤ nablaSup M f 0 :=
  le_nablaSup M (rho_nonneg M.S x)

theorem all_le_nablaSup_ne_top (M : SourceModelData) {f : M.V → ℝ≥0∞}
    (h : nablaSup M f 0 ≠ ⊤) : ∀ x : M.V, f x ≠ ⊤ := by
  intro x hx
  exact h (top_unique (hx ▸ le_nablaSup_zero M f x))

/-! ## Monotonicity helpers for `ℝ≥0∞` -/

theorem enn_mul_le_left {a b c : ℝ≥0∞} (h : b ≤ c) : a * b ≤ a * c := by
  gcongr

theorem enn_mul_le_right {a b c : ℝ≥0∞} (h : a ≤ b) : a * c ≤ b * c := by
  gcongr

/-! ## The unnormalized ball sum -/

theorem ballSum_const (M : SourceModelData) {S : Set M.V} (hS : S.Finite) (c : ℝ≥0∞) :
    ∑' x : M.V, S.indicator (fun _ => c) x = (S.ncard : ℝ≥0∞) * c := by
  have hzero : ∀ x ∉ hS.toFinset, S.indicator (fun _ => c) x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hc => hx ((hS.mem_toFinset).mpr hc)) _
  rw [tsum_eq_sum hzero]
  have h1 : Finset.sum hS.toFinset (fun x => S.indicator (fun _ => c) x)
      = Finset.sum hS.toFinset (fun _ => c) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact Set.indicator_of_mem ((hS.mem_toFinset).mp hx) _
  rw [h1, Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card S hS]

theorem ballSum_const_ball (M : SourceModelData) (r : ℝ) (c : ℝ≥0∞) :
    ∑' x : M.V, (M.ball r).indicator (fun _ => c) x = ((M.ball r).ncard : ℝ≥0∞) * c :=
  ballSum_const M (ball_finite M r) c

theorem indicator_add_diff (M : SourceModelData) {S T : Set M.V} (h : T ⊆ S)
    (f : M.V → ℝ≥0∞) :
    S.indicator f = T.indicator f + (S \ T).indicator f := by
  funext x
  by_cases hx : x ∈ S
  · by_cases hy : x ∈ T
    · simp [Set.indicator_of_mem, hx, hy]
    · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
  · have hy : x ∉ T := fun hc => hx (h hc)
    simp [Set.indicator_of_notMem, hx, hy]

theorem sqrt_le_self_of_one_le {r : ℝ} (hr : 1 ≤ r) : Real.sqrt r ≤ r := by
  have h0 : 0 ≤ r := le_trans zero_le_one hr
  calc Real.sqrt r ≤ Real.sqrt (r * r) := Real.sqrt_le_sqrt (by nlinarith)
    _ = r := Real.sqrt_mul_self h0

theorem ballSum_split (M : SourceModelData) (f : M.V → ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    ballSum M f r =
      ballSum M f (Real.sqrt r) + ∑' x : M.V, (M.ball r \ M.ball (Real.sqrt r)).indicator f x := by
  have hsub : M.ball (Real.sqrt r) ⊆ M.ball r :=
    ball_mono M (sqrt_le_self_of_one_le hr)
  rw [ballSum, ballSum, ← ENNReal.tsum_add]
  exact tsum_congr fun x => congrFun (indicator_add_diff M hsub f) x

/-! ## The two-scale inequality at `R = √r` -/

/-- The inner part `B_{√r}` of the ball sum, bounded by the number of its points
times `∇_0 = sup_x ∇(0,x)` (finiteness of the triangle diagram). -/
theorem ballSum_sqrt_le (M : SourceModelData) (f : M.V → ℝ≥0∞) (r : ℝ) :
    ballSum M f (Real.sqrt r) ≤ ((M.ball (Real.sqrt r)).ncard : ℝ≥0∞) * nablaSup M f 0 := by
  rw [ballSum]
  refine (ENNReal.tsum_le_tsum fun x => ?_).trans
    (le_of_eq (ballSum_const_ball M (Real.sqrt r) _))
  by_cases hx : x ∈ M.ball (Real.sqrt r)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    exact le_nablaSup_zero M f x
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- The outer part `B_r \ B_{√r} ⊆ {‖x‖ ≥ √r}`, bounded by `|B_r| · ∇_{√r}`. -/
theorem ballSum_diff_le (M : SourceModelData) (f : M.V → ℝ≥0∞) (r : ℝ) :
    (∑' x : M.V, (M.ball r \ M.ball (Real.sqrt r)).indicator f x) ≤
      ((M.ball r).ncard : ℝ≥0∞) * nablaSup M f (Real.sqrt r) := by
  have hstep : (∑' x : M.V, (M.ball r \ M.ball (Real.sqrt r)).indicator f x)
      ≤ ∑' x : M.V, (M.ball r).indicator (fun _ => nablaSup M f (Real.sqrt r)) x := by
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ M.ball r \ M.ball (Real.sqrt r)
    · have hxr : x ∈ M.ball r := hx.1
      have hle : Real.sqrt r ≤ M.S.ρ (toVec x) := le_of_lt (not_le.mp hx.2)
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxr]
      exact le_nablaSup M hle
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  exact hstep.trans (le_of_eq (ballSum_const_ball M r _))

/-! ## Lattice-ball cardinality in the form used for the normalised sum -/

theorem ball_ncard_cast_le (M : SourceModelData) {C : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) {r : ℝ} (hrC : C < r) :
    ((M.ball r).ncard : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ M.d * r ^ M.d) := by
  have h1 : ((M.ball r).ncard : ℝ) ≤ (r + C) ^ M.d := ball_ncard_le M hC hC0 hrC
  have h2 : (r + C) ^ M.d ≤ 2 ^ M.d * r ^ M.d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) M.d
  calc ((M.ball r).ncard : ℝ≥0∞) = ENNReal.ofReal ((M.ball r).ncard : ℝ) := by simp
    _ ≤ ENNReal.ofReal ((r + C) ^ M.d) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal (2 ^ M.d * r ^ M.d) := ENNReal.ofReal_le_ofReal h2

/-! ## The two-scale inequality at `R = √r` -/

section TwoScale

variable (M : SourceModelData) (f : M.V → ℝ≥0∞)

/-- **The two-scale inequality** at `R = √r` (the source's `R = √r`, *not* `r/2`). -/
theorem ballSum_two_scale {C r : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hr1 : 1 ≤ r) (hrC : C < r) (hrCs : C < Real.sqrt r) :
    ballSum M f r ≤
      ((M.ball (Real.sqrt r)).ncard : ℝ≥0∞) * nablaSup M f 0 +
        ((M.ball r).ncard : ℝ≥0∞) * nablaSup M f (Real.sqrt r) := by
  rw [ballSum_split M f hr1]
  exact add_le_add (ballSum_sqrt_le M f r) (ballSum_diff_le M f r)

theorem sqrt_pow_eq_rpow (M : SourceModelData) {r : ℝ} (hr : 0 ≤ r) :
    (Real.sqrt r) ^ M.d = r ^ ((M.d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (r ^ (1 / 2 : ℝ)) M.d,
    ← Real.rpow_mul hr]
  congr 1
  ring

/-- **`r^{-d} Σ_{x ∈ B_r} ∇(0,x) ≤ 2^d ( ∇_0 r^{-d/2} + ∇_{√r} )`**, the source's
two-scale split with the honest lattice-ball cardinalities. -/
theorem normalized_ballSum_le {C r : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hr1 : 1 ≤ r) (hrC : C < r) (hrCs : C < Real.sqrt r) :
    ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r ≤
      ENNReal.ofReal (2 ^ M.d) * (nablaSup M f 0 * ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))) +
        ENNReal.ofReal (2 ^ M.d) * nablaSup M f (Real.sqrt r) := by
  have hr : 0 < r := lt_of_le_of_lt hC0 hrC
  have hsqrtpow := sqrt_pow_eq_rpow M (le_of_lt hr)
  have hb1 := ball_ncard_cast_le M hC hC0 hrCs
  have hb2 := ball_ncard_cast_le M hC hC0 hrC
  have hcard1 : ((M.ball (Real.sqrt r)).ncard : ℝ≥0∞)
      ≤ ENNReal.ofReal (2 ^ M.d * r ^ ((M.d : ℝ) / 2)) := by
    rw [← hsqrtpow]
    exact hb1
  have hpow1 : r ^ (-(M.d : ℝ)) * r ^ ((M.d : ℝ) / 2) = r ^ (-(M.d : ℝ) / 2) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hpow2 : r ^ (-(M.d : ℝ)) * r ^ (M.d : ℝ) = 1 := by
    rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]
  have hreal1 : r ^ (-(M.d : ℝ)) * (2 ^ M.d * r ^ ((M.d : ℝ) / 2))
      = 2 ^ M.d * r ^ (-(M.d : ℝ) / 2) := by
    calc r ^ (-(M.d : ℝ)) * (2 ^ M.d * r ^ ((M.d : ℝ) / 2))
        = 2 ^ M.d * (r ^ (-(M.d : ℝ)) * r ^ ((M.d : ℝ) / 2)) := by ring
      _ = 2 ^ M.d * r ^ (-(M.d : ℝ) / 2) := by rw [hpow1]
  have hpow2' : r ^ (-(M.d : ℝ)) * r ^ M.d = 1 := by
    rw [← Real.rpow_natCast r M.d, hpow2]
  have hreal2 : r ^ (-(M.d : ℝ)) * (2 ^ M.d * r ^ M.d) = 2 ^ M.d := by
    calc r ^ (-(M.d : ℝ)) * (2 ^ M.d * r ^ M.d)
        = 2 ^ M.d * (r ^ (-(M.d : ℝ)) * r ^ M.d) := by ring
      _ = 2 ^ M.d := by rw [hpow2', mul_one]
  have hterm1 : ENNReal.ofReal (r ^ (-(M.d : ℝ))) *
      (ENNReal.ofReal (2 ^ M.d * r ^ ((M.d : ℝ) / 2)) * nablaSup M f 0)
      = ENNReal.ofReal (2 ^ M.d) * (nablaSup M f 0 * ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hreal1,
      ENNReal.ofReal_mul (by positivity), mul_assoc,
      mul_comm (ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))) (nablaSup M f 0)]
  have hterm2 : ENNReal.ofReal (r ^ (-(M.d : ℝ))) *
      (ENNReal.ofReal (2 ^ M.d * r ^ M.d) * nablaSup M f (Real.sqrt r))
      = ENNReal.ofReal (2 ^ M.d) * nablaSup M f (Real.sqrt r) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hreal2]
  calc ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r
      = ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r := rfl
    _ ≤ ENNReal.ofReal (r ^ (-(M.d : ℝ))) *
          (((M.ball (Real.sqrt r)).ncard : ℝ≥0∞) * nablaSup M f 0 +
            ((M.ball r).ncard : ℝ≥0∞) * nablaSup M f (Real.sqrt r)) :=
        enn_mul_le_left (ballSum_two_scale M f hC hC0 hr1 hrC hrCs)
    _ = ENNReal.ofReal (r ^ (-(M.d : ℝ))) *
            (((M.ball (Real.sqrt r)).ncard : ℝ≥0∞) * nablaSup M f 0) +
          ENNReal.ofReal (r ^ (-(M.d : ℝ))) *
            (((M.ball r).ncard : ℝ≥0∞) * nablaSup M f (Real.sqrt r)) := by
        rw [mul_add]
    _ ≤ ENNReal.ofReal (r ^ (-(M.d : ℝ))) *
            (ENNReal.ofReal (2 ^ M.d * r ^ ((M.d : ℝ) / 2)) * nablaSup M f 0) +
          ENNReal.ofReal (r ^ (-(M.d : ℝ))) *
            (ENNReal.ofReal (2 ^ M.d * r ^ M.d) * nablaSup M f (Real.sqrt r)) := by
        refine add_le_add ?_ ?_
        · exact enn_mul_le_left (enn_mul_le_right hcard1)
        · exact enn_mul_le_left (enn_mul_le_right hb2)
    _ = ENNReal.ofReal (2 ^ M.d) *
            (nablaSup M f 0 * ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))) +
          ENNReal.ofReal (2 ^ M.d) * nablaSup M f (Real.sqrt r) := by
        rw [hterm1, hterm2]

end TwoScale

/-! ## Log-integrability of the two summands -/

/-- `∫⁻_{r > R} r^a ≠ ⊤` for `a < -1`, `R > 0`. -/
theorem lintegral_Ioi_rpow_ne_top {a R : ℝ} (ha : a < -1) (hR : 0 < R) :
    ∫⁻ r in Ioi R, ENNReal.ofReal (r ^ a) ≠ ⊤ := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi R)] (fun r : ℝ => r ^ a) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_
    exact Real.rpow_nonneg (le_of_lt (lt_trans hR hr)) a
  have hint : IntegrableOn (fun r : ℝ => r ^ a) (Ioi R) volume :=
    integrableOn_Ioi_rpow_of_lt ha hR
  have hfin : ∫⁻ r in Ioi R, ENNReal.ofReal (r ^ a) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral
  exact ne_of_lt hfin

theorem ofReal_div_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ENNReal.ofReal a / ENNReal.ofReal b = ENNReal.ofReal (a / b) := by
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hb,
    ← ENNReal.ofReal_mul (p := a) (q := b⁻¹) ha, div_eq_mul_inv]

/-- The coefficient identity behind the change of variables `u = √r`:
`y / x = 2 * ((2√x)^{-1} * (y / √x))` for `x > 0`, in `ℝ≥0∞`. -/
theorem div_eq_two_mul_inv_sqrt {x : ℝ} (hx : 0 < x) (y : ℝ≥0∞) :
    y / ENNReal.ofReal x =
      2 * (ENNReal.ofReal ((2 * Real.sqrt x)⁻¹) * (y / ENNReal.ofReal (Real.sqrt x))) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hxne : ENNReal.ofReal x ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsne : ENNReal.ofReal (Real.sqrt x) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcne : ENNReal.ofReal ((2 * Real.sqrt x)⁻¹) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    positivity
  rcases eq_or_ne y ⊤ with hy | hy
  · subst hy
    have h1 : ENNReal.ofReal ((Real.sqrt x)⁻¹) * 2⁻¹ ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) (by norm_num)
    simp [ENNReal.top_div, hxne, hsne, h1]
  · conv_lhs => rw [← ENNReal.ofReal_toReal hy]
    conv_rhs => rw [← ENNReal.ofReal_toReal hy]
    rw [ofReal_div_ofReal ENNReal.toReal_nonneg hx, ofReal_div_ofReal ENNReal.toReal_nonneg hs,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← mul_assoc,
      ← ENNReal.ofReal_mul (p := 2) (q := (2 * Real.sqrt x)⁻¹)
        (by positivity : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (p := 2 * (2 * Real.sqrt x)⁻¹) (q := ENNReal.toReal y / Real.sqrt x)
        (by positivity : (0:ℝ) ≤ 2 * (2 * Real.sqrt x)⁻¹)]
    congr 1
    field_simp
    rw [Real.sq_sqrt hx.le]

/-- **Change of variables `u = √r`** for the log measure:
`∫_{r>R} g(√r) dr/r = 2 ∫_{u>√R} g(u) du/u`. -/
theorem lintegral_log_sqrt_eq (g : ℝ → ℝ≥0∞) (hg : Measurable g) {R : ℝ} (hR : 0 < R) :
    ∫⁻ r in Ioi R, g (Real.sqrt r) / ENNReal.ofReal r
      = 2 * ∫⁻ u in Ioi (Real.sqrt R), g u / ENNReal.ofReal u := by
  have hderiv : ∀ x ∈ Ioi R, HasDerivWithinAt Real.sqrt (2 * Real.sqrt x)⁻¹ (Ioi R) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hR hx)
    simpa [one_div] using (Real.hasDerivAt_sqrt hx0).hasDerivWithinAt
  have hinj : InjOn Real.sqrt (Ioi R) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := le_of_lt (lt_trans hR hx)
    have hy0 : 0 ≤ y := le_of_lt (lt_trans hR hy)
    calc x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx0).symm
      _ = (Real.sqrt y) ^ 2 := by rw [hxy]
      _ = y := Real.sq_sqrt hy0
  have himg : Real.sqrt '' Ioi R = Ioi (Real.sqrt R) := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Real.sqrt_lt_sqrt hR.le hx
    · intro hu
      have hu0 : 0 ≤ u := le_of_lt (lt_trans (Real.sqrt_pos.mpr hR) hu)
      refine ⟨u ^ 2, ?_, Real.sqrt_sq hu0⟩
      have h1 : Real.sqrt R < u := hu
      have h2 : Real.sqrt R < Real.sqrt (u ^ 2) := by rwa [Real.sqrt_sq hu0]
      exact (Real.sqrt_lt_sqrt_iff hR.le).mp h2
  have hJ := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi R) (f := Real.sqrt)
    (f' := fun x => (2 * Real.sqrt x)⁻¹) measurableSet_Ioi hderiv hinj
    (fun u => g u / ENNReal.ofReal u)
  rw [himg] at hJ
  have hJ' : ∫⁻ r in Ioi R, ENNReal.ofReal ((2 * Real.sqrt r)⁻¹) *
      (g (Real.sqrt r) / ENNReal.ofReal (Real.sqrt r))
      = ∫⁻ u in Ioi (Real.sqrt R), g u / ENNReal.ofReal u := by
    rw [hJ]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans hR hr
    rw [abs_of_pos (by positivity : (0:ℝ) < (2 * Real.sqrt r)⁻¹)]
  have hmeas : Measurable fun r : ℝ => ENNReal.ofReal ((2 * Real.sqrt r)⁻¹) *
      (g (Real.sqrt r) / ENNReal.ofReal (Real.sqrt r)) := by
    refine Measurable.mul (Measurable.ennreal_ofReal (by fun_prop)) ?_
    exact (hg.comp Real.continuous_sqrt.measurable).div
      (Measurable.ennreal_ofReal (by fun_prop))
  calc ∫⁻ r in Ioi R, g (Real.sqrt r) / ENNReal.ofReal r
      = ∫⁻ r in Ioi R, 2 * (ENNReal.ofReal ((2 * Real.sqrt r)⁻¹) *
          (g (Real.sqrt r) / ENNReal.ofReal (Real.sqrt r))) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr0 : 0 < r := lt_trans hR hr
        exact div_eq_two_mul_inv_sqrt hr0 (g (Real.sqrt r))
    _ = 2 * ∫⁻ r in Ioi R, ENNReal.ofReal ((2 * Real.sqrt r)⁻¹) *
          (g (Real.sqrt r) / ENNReal.ofReal (Real.sqrt r)) :=
        lintegral_const_mul 2 hmeas
    _ = 2 * ∫⁻ u in Ioi (Real.sqrt R), g u / ENNReal.ofReal u := by rw [hJ']

/-! ## Measurability of the tail supremum -/

theorem measurable_nablaSup (M : SourceModelData) (f : M.V → ℝ≥0∞) :
    Measurable (nablaSup M f) := by
  have h : nablaSup M f = fun r : ℝ => ⨆ x : M.V, if r ≤ M.S.ρ (toVec x) then f x else 0 := by
    funext r
    refine iSup_congr fun x => ?_
    by_cases hx : r ≤ M.S.ρ (toVec x)
    · simp [hx]
    · simp [hx]
  rw [h]
  exact Measurable.iSup fun x =>
    Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem mul_ne_top_of_top {a b : ℝ≥0∞} (hat : a ≠ ⊤) (hbt : b ≠ ⊤) : a * b ≠ ⊤ := by
  intro h
  rcases ENNReal.mul_eq_top.mp h with ⟨-, hb⟩ | ⟨ha, -⟩
  · exact hbt hb
  · exact hat ha

/-! ## The pointwise normalised two-scale bound -/

section Pointwise

variable (M : SourceModelData) (f : M.V → ℝ≥0∞)

/-- `r^{-d/2}`, in the form `((√r)^d)^{-1}`, where measurability in `r` is immediate. -/
theorem ofReal_rpow_neg_half (M : SourceModelData) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))
      = ((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ := by
  have h1 : r ^ (-(M.d : ℝ) / 2) = (r ^ ((M.d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt hr)]
    ring_nf
  rw [h1, ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr _),
    ← sqrt_pow_eq_rpow M (le_of_lt hr), ENNReal.ofReal_pow (Real.sqrt_nonneg r)]

/-- **Pointwise normalised two-scale inequality.**
`r^{-d} Σ_{x ∈ B_r} ∇(0,x) / r ≤ 2^d ( ∇_0 r^{-d/2-1} + ∇_{√r} / r )`. -/
theorem normalized_div_le {C r : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hr1 : 1 ≤ r) (hrC : C < r) (hrCs : C < Real.sqrt r) :
    (ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r) / ENNReal.ofReal r ≤
      ENNReal.ofReal (2 ^ M.d) *
          (nablaSup M f 0 * (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ *
            (ENNReal.ofReal r)⁻¹)) +
        ENNReal.ofReal (2 ^ M.d) * (nablaSup M f (Real.sqrt r) / ENNReal.ofReal r) := by
  have hr : 0 < r := lt_of_le_of_lt hC0 hrC
  have hhalf := ofReal_rpow_neg_half M hr
  have hmain := normalized_ballSum_le M f hC hC0 hr1 hrC hrCs
  have hstep : (ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r) / ENNReal.ofReal r
      ≤ (ENNReal.ofReal (2 ^ M.d) *
            (nablaSup M f 0 * ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))) +
          ENNReal.ofReal (2 ^ M.d) * nablaSup M f (Real.sqrt r)) / ENNReal.ofReal r := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact enn_mul_le_right hmain
  refine hstep.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, add_mul, hhalf]
  congr 1
  · rw [mul_assoc, mul_assoc]
  · rw [div_eq_mul_inv, mul_assoc]

end Pointwise

/-! ## Finiteness of the two summands -/

section Finiteness

variable (M : SourceModelData) (f : M.V → ℝ≥0∞)

/-- The `r^{-d/2-1}` summand is log-integrable: this is exactly where `1 ≤ d` is used. -/
theorem lintegral_inner_ne_top {R : ℝ} (hR : 0 < R) (hd : 0 < M.d) :
    ∫⁻ r in Ioi R,
        (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ * (ENNReal.ofReal r)⁻¹) ≠ ⊤ := by
  have hexp : -(M.d : ℝ) / 2 - 1 < -1 := by
    have hd' : (0 : ℝ) < M.d := by exact_mod_cast hd
    linarith
  refine ne_top_of_le_ne_top (lintegral_Ioi_rpow_ne_top hexp hR) (le_of_eq ?_)
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := lt_trans hR hr
  rw [← ofReal_rpow_neg_half M hr0, ← ENNReal.ofReal_inv_of_pos hr0, ← Real.rpow_neg_one r,
    ← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos hr0 _))]
  congr 1
  rw [← Real.rpow_add hr0]
  ring_nf

/-- The `∇_{√r}/r` summand: the change of variables `u = √r`. -/
theorem lintegral_outer_ne_top {R : ℝ} (hR : 1 ≤ R)
    (hlog : ∫⁻ r in Ioi 1, nablaSup M f r / ENNReal.ofReal r ≠ ⊤) :
    ∫⁻ r in Ioi R, nablaSup M f (Real.sqrt r) / ENNReal.ofReal r ≠ ⊤ := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hsqrtR : (1 : ℝ) ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hsub : Ioi (Real.sqrt R) ⊆ Ioi (1 : ℝ) := fun r hr => lt_of_le_of_lt hsqrtR hr
  rw [lintegral_log_sqrt_eq (nablaSup M f) (measurable_nablaSup M f) hRpos]
  exact mul_ne_top_of_top (by norm_num) (ne_top_of_le_ne_top hlog (lintegral_mono_set hsub))

end Finiteness

/-! ## The main theorem -/

section Main

variable (M : SourceModelData) (f : M.V → ℝ≥0∞)

/-- **`hutchcroft.i.4.2.s3`, analytic core.**
If the triangle diagram is finite (`∇_0 < ∞`) and `r ↦ ∇_r` is logarithmically
integrable, then `r ↦ r^{-d} Σ_{x ∈ B_r} ∇(0,x)` is logarithmically integrable,
expressed as finiteness of the `ℝ≥0∞`-`lintegral` against `dr/r`. -/
theorem lintegral_normalized_ballSum_ne_top {C R : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hR1 : 1 ≤ R) (hRC : C ≤ R) (hRCs : C ^ 2 ≤ R)
    (hTriangle : nablaSup M f 0 ≠ ⊤)
    (hlog : ∫⁻ r in Ioi 1, nablaSup M f r / ENNReal.ofReal r ≠ ⊤) :
    ∫⁻ r in Ioi R,
        (ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r) / ENNReal.ofReal r ≠ ⊤ := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hsmeas : Measurable fun r : ℝ => ENNReal.ofReal (Real.sqrt r) :=
    Measurable.ennreal_ofReal (by fun_prop)
  have hrmeas : Measurable fun r : ℝ => ENNReal.ofReal r :=
    Measurable.ennreal_ofReal measurable_id
  have hGmeas : Measurable fun r : ℝ =>
      ((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ * (ENNReal.ofReal r)⁻¹ :=
    ((hsmeas.pow_const M.d).inv).mul hrmeas.inv
  have hAmeas : Measurable fun r : ℝ => ENNReal.ofReal (2 ^ M.d) *
      (nablaSup M f 0 * (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ *
        (ENNReal.ofReal r)⁻¹)) :=
    measurable_const.mul (measurable_const.mul hGmeas)
  have hpoint : ∀ r ∈ Ioi R,
      (ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r) / ENNReal.ofReal r ≤
        ENNReal.ofReal (2 ^ M.d) *
            (nablaSup M f 0 * (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ *
              (ENNReal.ofReal r)⁻¹)) +
          ENNReal.ofReal (2 ^ M.d) * (nablaSup M f (Real.sqrt r) / ENNReal.ofReal r) := by
    intro r hr
    have hrR : R < r := hr
    have hr1 : 1 ≤ r := le_trans hR1 hrR.le
    have hrC : C < r := lt_of_le_of_lt hRC hrR
    have hrCs : C < Real.sqrt r := by
      have h1 : Real.sqrt (C ^ 2) < Real.sqrt r :=
        Real.sqrt_lt_sqrt (sq_nonneg C) (lt_of_le_of_lt hRCs hrR)
      rwa [Real.sqrt_sq hC0] at h1
    exact normalized_div_le M f hC hC0 hr1 hrC hrCs
  have hbound : (fun r => (ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r) /
        ENNReal.ofReal r) ≤ᵐ[volume.restrict (Ioi R)]
      (fun r => ENNReal.ofReal (2 ^ M.d) *
            (nablaSup M f 0 * (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ *
              (ENNReal.ofReal r)⁻¹)) +
          ENNReal.ofReal (2 ^ M.d) * (nablaSup M f (Real.sqrt r) / ENNReal.ofReal r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hpoint r hr
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
  rw [lintegral_add_left hAmeas]
  intro hcontra
  rcases ENNReal.add_eq_top.mp hcontra with h' | h'
  · have hGfin : ∫⁻ r in Ioi R,
        (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ * (ENNReal.ofReal r)⁻¹) ≠ ⊤ :=
      lintegral_inner_ne_top M hRpos (lt_of_lt_of_le zero_lt_one M.hd)
    have h1 : ∫⁻ r in Ioi R, ENNReal.ofReal (2 ^ M.d) *
        (nablaSup M f 0 * (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ *
          (ENNReal.ofReal r)⁻¹))
        = ENNReal.ofReal (2 ^ M.d) *
          (nablaSup M f 0 * ∫⁻ r in Ioi R,
            (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ * (ENNReal.ofReal r)⁻¹)) := by
      rw [lintegral_const_mul (r := ENNReal.ofReal (2 ^ M.d))
        (f := fun r => nablaSup M f 0 * (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ *
          (ENNReal.ofReal r)⁻¹)) (measurable_const.mul hGmeas)]
      rw [lintegral_const_mul (r := nablaSup M f 0)
        (f := fun r => (((ENNReal.ofReal (Real.sqrt r)) ^ M.d)⁻¹ *
          (ENNReal.ofReal r)⁻¹)) hGmeas]
    rw [h1] at h'
    exact (mul_ne_top_of_top ENNReal.ofReal_ne_top
      (mul_ne_top_of_top hTriangle hGfin)) h'
  · have hOfin : ∫⁻ r in Ioi R, nablaSup M f (Real.sqrt r) / ENNReal.ofReal r ≠ ⊤ :=
      lintegral_outer_ne_top M f hR1 hlog
    have h2 : ∫⁻ r in Ioi R, ENNReal.ofReal (2 ^ M.d) *
        (nablaSup M f (Real.sqrt r) / ENNReal.ofReal r)
        = ENNReal.ofReal (2 ^ M.d) *
          ∫⁻ r in Ioi R, nablaSup M f (Real.sqrt r) / ENNReal.ofReal r :=
      lintegral_const_mul (r := ENNReal.ofReal (2 ^ M.d))
        (f := fun r => nablaSup M f (Real.sqrt r) / ENNReal.ofReal r)
        (((measurable_nablaSup M f).comp Real.continuous_sqrt.measurable).div hrmeas)
    rw [h2] at h'
    exact (mul_ne_top_of_top ENNReal.ofReal_ne_top hOfin) h'

end Main

/-! ## Packaging in the repository's `ℝ`-valued `LogarithmicallyIntegrable` -/

section Packaging

variable (M : SourceModelData) (f : M.V → ℝ≥0∞)

theorem finset_sum_ne_top {ι : Type*} (s : Finset ι) {g : ι → ℝ≥0∞}
    (h : ∀ i ∈ s, g i ≠ ⊤) : Finset.sum s g ≠ ⊤ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro htop
      rcases ENNReal.add_eq_top.mp htop with h' | h'
      · exact h a (Finset.mem_insert_self a s) h'
      · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) h'

theorem ballSum_ne_top {f : M.V → ℝ≥0∞} (hfin : ∀ x, f x ≠ ⊤) (r : ℝ) :
    ballSum M f r ≠ ⊤ := by
  rw [ballSum]
  have hzero : ∀ x ∉ (ball_finite M r).toFinset, (M.ball r).indicator f x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hc => hx (((ball_finite M r).mem_toFinset).mpr hc)) _
  rw [tsum_eq_sum (s := (ball_finite M r).toFinset) hzero]
  refine finset_sum_ne_top _ fun x _ => ?_
  by_cases hx : x ∈ M.ball r
  · rw [Set.indicator_of_mem hx]
    exact hfin x
  · rw [Set.indicator_of_notMem hx]
    simp

/-- `∫⁻`-finiteness of `|h r| / r` against `dr` gives the `IntegrableOn` content of
`LogarithmicallyIntegrable`; the measurability of `h` is the explicit premise. -/
theorem integrableOn_of_lintegral_ne_top {h : ℝ → ℝ} (hmeas : Measurable h) {R : ℝ}
    (hR : 0 < R) (hne : ∫⁻ r in Ioi R, ENNReal.ofReal (|h r| / r) ≠ ⊤) :
    IntegrableOn (fun r => |h r| / r) (Ioi R) volume := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi R)] (fun r : ℝ => |h r| / r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact div_nonneg (abs_nonneg _) (le_of_lt (lt_trans hR hr))
  refine ⟨?_, ?_⟩
  · exact (hmeas.abs.div measurable_id).aestronglyMeasurable
  · exact (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_top_iff_ne_top.mpr hne)

/-- **`hutchcroft.i.4.2.s3` in the repository's `ℝ`-valued form.**
If the triangle diagram is finite (`∇_0 < ∞`) and `r ↦ ∇_r` is logarithmically
integrable, then `r ↦ r^{-d} Σ_{x ∈ B_r} ∇(0,x)` is logarithmically integrable. -/
theorem logIntegrable_ballAverage {C R : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hR1 : 1 ≤ R) (hRC : C ≤ R) (hRCs : C ^ 2 ≤ R)
    (hTriangle : nablaSup M f 0 ≠ ⊤)
    (hlog : ∫⁻ r in Ioi 1, nablaSup M f r / ENNReal.ofReal r ≠ ⊤)
    (hmeas : Measurable fun r => ENNReal.toReal (ballSum M f r) * r ^ (-(M.d : ℝ))) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable
      (fun r => ENNReal.toReal (ballSum M f r) * r ^ (-(M.d : ℝ))) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hfin := all_le_nablaSup_ne_top M hTriangle
  have hconv : ∀ r ∈ Ioi R, ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r
      = ENNReal.ofReal (ENNReal.toReal (ballSum M f r) * r ^ (-(M.d : ℝ))) := by
    intro r hr
    conv_lhs => rw [← ENNReal.ofReal_toReal (ballSum_ne_top M hfin r)]
    rw [mul_comm (ENNReal.ofReal (r ^ (-(M.d : ℝ))))
      (ENNReal.ofReal (ENNReal.toReal (ballSum M f r)))]
    exact (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
  have hmain := lintegral_normalized_ballSum_ne_top M f hC hC0 hR1 hRC hRCs hTriangle hlog
  have hEq : ∫⁻ r in Ioi R,
        (ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r) / ENNReal.ofReal r
      = ∫⁻ r in Ioi R,
          ENNReal.ofReal (|ENNReal.toReal (ballSum M f r) * r ^ (-(M.d : ℝ))| / r) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans hRpos hr
    rw [hconv r hr, ofReal_div_ofReal (by positivity) hr0]
    congr 1
    rw [abs_of_nonneg (by positivity)]
  refine ⟨hmeas, R, hRpos, ?_⟩
  refine integrableOn_of_lintegral_ne_top hmeas hRpos ?_
  rw [← hEq]
  exact hmain

/-- Every `ballSum` is finite under the global upper bound.  Its real value
is therefore monotone in the radius, hence measurable, and multiplication by
`r^{-d}` preserves measurability. -/
theorem measurable_normalized_ballSum_toReal (M : SourceModelData)
    {f : M.V → ℝ≥0∞} (hTriangle : nablaSup M f 0 ≠ ⊤) :
    Measurable (fun r : ℝ => ENNReal.toReal (ballSum M f r) * r ^ (-(M.d : ℝ))) := by
  have hfin := all_le_nablaSup_ne_top M hTriangle
  have hmono : Monotone (ballSum M f) := by
    intro r s hrs
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ M.ball r
    · have hxs : x ∈ M.ball s := le_trans hx hrs
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hreal : Monotone (fun r : ℝ => (ballSum M f r).toReal) := by
    intro r s hrs
    exact ENNReal.toReal_mono (ballSum_ne_top M hfin s) (hmono hrs)
  exact hreal.measurable.mul (by fun_prop)

end Packaging



/-! ## Instantiation at the paper's open triangle diagram -/

section Instantiation

variable (M : SourceModelData)

/-- **`hutchcroft.i.4.2.s3` at the configured open triangle diagram.**  The two
remaining hypotheses are exactly the paper's: finiteness of the tail supremum
(which the triangle condition `∇_{β_c} < ∞` supplies, given that `∇(0,0)` is the
maximum of `x ↦ ∇(0,x)`) and log-integrability of `r ↦ ∇_r`. -/
theorem lintegral_openTriangle_ne_top {C R : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hR1 : 1 ≤ R) (hRC : C ≤ R) (hRCs : C ^ 2 ≤ R)
    (hTriangle : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (hlog : ∫⁻ r in Ioi 1, nablaSup M (openTriangleNabla M) r / ENNReal.ofReal r ≠ ⊤) :
    ∫⁻ r in Ioi R,
        (ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M (openTriangleNabla M) r) /
          ENNReal.ofReal r ≠ ⊤ :=
  lintegral_normalized_ballSum_ne_top M (openTriangleNabla M) hC hC0 hR1 hRC hRCs
    hTriangle hlog

/-- The `ℝ`-valued form at the configured open triangle diagram. -/
theorem logIntegrable_openTriangle {C R : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hR1 : 1 ≤ R) (hRC : C ≤ R) (hRCs : C ^ 2 ≤ R)
    (hTriangle : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (hlog : ∫⁻ r in Ioi 1, nablaSup M (openTriangleNabla M) r / ENNReal.ofReal r ≠ ⊤) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable
      (fun r => ENNReal.toReal (ballSum M (openTriangleNabla M) r) * r ^ (-(M.d : ℝ))) :=
  logIntegrable_ballAverage M (openTriangleNabla M) hC hC0 hR1 hRC hRCs hTriangle hlog
    (measurable_normalized_ballSum_toReal M hTriangle)

/-- `∇_r = sup_{‖x‖ ≥ r} ∇(0,x)` is antitone in `r`, so the separate tail obligation
`hutchcroft.a.tri.tail` is exactly `Tendsto (nablaSup M f) atTop (𝓝 0)` together
with finiteness.  Stated here to keep the two obligations apart. -/
theorem tendsto_nablaSup_zero_iff (f : M.V → ℝ≥0∞) :
    Tendsto (nablaSup M f) atTop (𝓝 0) ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℝ, ∀ r ≥ N, nablaSup M f r ≤ ε :=
  ENNReal.tendsto_atTop_zero

end Instantiation


theorem enn_le_add_one_mul (a b c : ℝ≥0∞) : a * b + c ≤ (a + 1) * (b + c) := by
  have h1 : a * b ≤ (a + 1) * b := enn_mul_le_right (le_add_of_nonneg_right bot_le)
  have h2 : c ≤ (a + 1) * c := by
    rw [add_mul, one_mul]
    exact le_add_of_nonneg_left bot_le
  calc a * b + c ≤ (a + 1) * b + (a + 1) * c := add_le_add h1 h2
    _ = (a + 1) * (b + c) := (mul_add _ _ _).symm

/-! ## The convergence half: `∇_r → 0` gives `r^{-d} Σ_{x ∈ B_r} f x → 0` -/

section Convergence

variable (M : SourceModelData) (f : M.V → ℝ≥0∞)

/-- **`r^{-d} Σ_{x∈B_r} f x → 0` from `∇_r → 0`**, using the sharp `r^{-d/2}` rate of
`normalized_ballSum_le`.  Together with `logIntegrable_ballAverage` this is the
source's "supplemented error form" (`IsLogErrorFunction`): log-integrability of
`∇_r` plus `∇_r → 0` gives log-integrability of the averaged sum plus its
vanishing.  The hypothesis `∇_r → 0` is the separate `hutchcroft.a.tri.tail`
obligation and is not proved here. -/
theorem tendsto_normalized_ballSum_zero {C : ℝ}
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C)
    (hC0 : 0 ≤ C) (hTriangle : nablaSup M f 0 ≠ ⊤)
    (hconv : Tendsto (nablaSup M f) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(M.d : ℝ))) * ballSum M f r) atTop (𝓝 0) := by
  set K : ℝ≥0∞ := ENNReal.ofReal (2 ^ M.d) * (nablaSup M f 0 + 1) with hK
  have hKtop : K ≠ ⊤ := mul_ne_top_of_top ENNReal.ofReal_ne_top
    (fun h => hTriangle ((ENNReal.add_eq_top.mp h).resolve_right ENNReal.one_ne_top))
  have hdpos : (0 : ℝ) < M.d := by exact_mod_cast M.hd
  have hsq : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2))) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < (M.d : ℝ) / 2))
    simpa [Function.comp_def, neg_div] using h
  have hsqrt : Tendsto (fun r : ℝ => Real.sqrt r) atTop atTop := by
    simpa [Real.sqrt_eq_rpow] using tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)
  have htail : Tendsto (fun r : ℝ => nablaSup M f (Real.sqrt r)) atTop (𝓝 0) := hconv.comp hsqrt
  have hsum : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2)) +
      nablaSup M f (Real.sqrt r)) atTop (𝓝 0) := by
    have h := hsq.add htail
    simpa [Function.comp_def] using h
  have hmaj : Tendsto (fun r : ℝ => K * (ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2)) +
      nablaSup M f (Real.sqrt r))) atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_const_mul hKtop).tendsto 0).comp hsum
    simpa [Function.comp_def] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun r => bot_le) ?_
  filter_upwards [eventually_ge_atTop (max 1 (max (C + 1) (C ^ 2 + 1)))] with r hr
  have h1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
  have hR : max (C + 1) (C ^ 2 + 1) ≤ r := le_trans (le_max_right _ _) hr
  have hrC : C < r := lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ _) hR)
  have hrCsq : C ^ 2 + 1 ≤ r := le_trans (le_max_right _ _) hR
  have hrCs : C < Real.sqrt r := by
    have h2 : Real.sqrt (C ^ 2) < Real.sqrt r := Real.sqrt_lt_sqrt (sq_nonneg C) (by linarith)
    rwa [Real.sqrt_sq hC0] at h2
  refine (normalized_ballSum_le M f hC hC0 h1 hrC hrCs).trans ?_
  rw [hK, ← mul_add, mul_assoc]
  refine enn_mul_le_left ?_
  exact enn_le_add_one_mul (nablaSup M f 0) (ENNReal.ofReal (r ^ (-(M.d : ℝ) / 2)))
    (nablaSup M f (Real.sqrt r))

end Convergence


end PercLib.CriticalLRP.BallAverage
