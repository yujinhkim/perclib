/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m4/Pointwise.lean`.

Swarm `smwzlje3f`, member `m4`, direction `d4` — (E) the HD(3) / triangle / tail inputs.

# The pointwise decay of the two-point function in Case 3 of (HD)

Case 3 of (HD) (p. 9 of Hutchcroft, *Critical long-range percolation I*) is the pointwise bound

  `P_{β_c}(x ↔ y) ⪯ (log ‖x-y‖)^{-1} ‖x-y‖^{-d+2}`  for `x ≠ y`,

with `d = 6` and `α = 2`.  This file converts it, at the model's own normalized source norm
`S.ρ`, into the radial majorant `Wt (d-2) 1` used by the convolution assembly of
`CriticalLRPConv`:

  `|τ(z)| ≤ K · (1 + S.ρ z)^{-(d-2)} · (log (2 + S.ρ z))^{-1}`,

where `τ z = τ_{β_c}(0,z)`.

Two honest points about the conversion.

* The source bound printed for *all* `x ≠ y` is vacuous for small `‖x-y‖` (where the logarithm is
  negative or zero) and blows up as `‖x-y‖ ↓ 1`.  The conversion therefore does **not** use the
  source bound near the origin: there the trivial bound `τ ≤ 1` supplies the estimate, and the
  majorant is bounded below by the positive constant `Wt (d-2) 1 4`.  The source bound is used
  only for `‖x-y‖ ≥ 4`, exactly where its two factors are controlled by the majorant's.
* Nothing is assumed about the model beyond `SourceModelData`; the only percolation input is
  `twoPointFunction_le_one`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Defs
public import PercLib.CriticalLRP.Analysis.LatticeConvolution

set_option linter.style.longLine false
set_option linter.hashCommand false
@[expose] public section

open scoped ENNReal NNReal Topology
open Filter

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

open PercLib.CriticalLRP CriticalLRPConv

variable (M : SourceModelData)

/-! ## §0 Elementary facts about the source norm -/

/-- `toVec` is injective. -/
theorem toVec_injective : Function.Injective (toVec (d := M.d)) := by
  intro x y h
  funext i
  have hi : ((x i : ℤ) : ℝ) = ((y i : ℤ) : ℝ) := congrFun h i
  exact_mod_cast hi

/-- The lattice origin maps to the vector origin. -/
theorem toVec_zero : (toVec (d := M.d) (0 : M.V)) = 0 := by
  funext i
  simp [toVec]

/-- The source norm is nonnegative. -/
theorem sρ_nonneg (z : M.V) : 0 ≤ M.S.ρ (toVec z) := by
  rcases eq_or_ne z 0 with h0 | hz
  · subst h0
    rw [toVec_zero M, M.S.ρ_zero]
  · exact (M.S.ρ_pos _ (fun h => hz (toVec_injective M (by rw [toVec_zero M]; exact h)))).le

/-! ## §1 Translation invariance of the configured kernel -/

/-- The configured kernel `M.kernel = radialSym M.S M.K` is invariant under lattice translations,
because `radialSym` only sees `S.dist`, i.e. `S.ρ ∘ toVec ∘ (−)`. -/
theorem kernel_shift (a : M.V) (e : Sym2 M.V) :
    M.kernel (Sym2.map (fun x => x + a) e) = M.kernel e := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [kernel, radialSym_mk, Sym2.map_mk]
    have hxy : (x + a = y + a) ↔ (x = y) := by
      constructor
      · intro hh
        funext i
        have hi : x i + a i = y i + a i := congrFun hh i
        omega
      · intro hh
        rw [hh]
    have hd : M.S.dist (x + a) (y + a) = M.S.dist x y := by
      simp only [SourceNormData.dist]
      congr 1
      funext i
      simp only [toVec, Pi.add_apply, Pi.sub_apply]
      ring
    by_cases hEq : x = y
    · subst hEq
      simp
    · have hne : ¬ (x + a = y + a) := fun hh => hEq (hxy.mp hh)
      rw [ite_eq_right hne, ite_eq_right hEq, hd]

/-! ## §2 The two-point function at the origin and the real profile `τ` -/

/-- `M.twoPoint` is the real part of the configured `twoPointFunction`. -/
theorem twoPointFunction_toReal (β : ℝ≥0) (x y : M.V) :
    M.twoPoint β x y = (twoPointFunction M.kernel M.kernel_nonneg β x y).toReal := by
  change (M.law β).real {ω : Config M.V | Connects ω x y} = _
  rw [MeasureTheory.Measure.real_def]
  rfl

/-- `τ` is the model's two-point function at the origin. -/
theorem tau_eq_twoPoint (z : M.V) : M.tau z = M.twoPoint M.betaCrit 0 z := rfl

/-- The two-point function is symmetric. -/
theorem twoPoint_symm (β : ℝ≥0) (x y : M.V) : M.twoPoint β x y = M.twoPoint β y x := by
  rw [twoPointFunction_toReal, twoPointFunction_toReal, twoPointFunction_comm]

/-- By translation invariance the whole two-point function is carried by `τ`. -/
theorem tau_eq_twoPoint_sub (x y : M.V) :
    M.tau (y - x) = M.twoPoint M.betaCrit x y := by
  rw [twoPointFunction_toReal]
  change (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 (y - x)).toReal
      = (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit x y).toReal
  rw [twoPointFunction_eq_origin (J := M.kernel) M.kernel_shift M.kernel_nonneg M.betaCrit x y]

theorem tau_nonneg (z : M.V) : 0 ≤ M.tau z := ENNReal.toReal_nonneg

/-- `τ ≤ 1`: the only percolation input of this file. -/
theorem tau_le_one (z : M.V) : M.tau z ≤ 1 := by
  change (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z).toReal ≤ 1
  calc (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z).toReal
      ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) (twoPointFunction_le_one _ _ _ _ _)
    _ = 1 := by simp

/-- `τ` is exactly the `ℝ≥0∞`-valued two-point function, `ofReal`-wise. -/
theorem ofReal_tau (z : M.V) :
    ENNReal.ofReal (M.tau z) =
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z := by
  change ENNReal.ofReal ((twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z).toReal) = _
  exact ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top (by simp) (twoPointFunction_le_one _ _ _ _ _))

/-! ## §3 The source decay bound for `τ` -/

/-- Case 3 of (HD) gives the pointwise source decay of `τ` at every nonzero point,
in the exact shape printed by the source. -/
theorem tau_le_of_case3 (h : M.Case3HD) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : M.V, z ≠ 0 → M.tau z
      ≤ C * (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) := by
  obtain ⟨hd, hα, C, hC, hb⟩ := h
  refine ⟨C, hC, fun z hz => ?_⟩
  have hbz : M.twoPoint M.betaCrit z 0
      ≤ C * (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) := by
    have h0 := hb z 0 hz
    simpa using h0
  have h1 : M.tau z = M.twoPoint M.betaCrit z 0 := by
    have h := tau_eq_twoPoint_sub (M := M) (0 : M.V) z
    rw [sub_zero] at h
    rw [h]
    exact twoPoint_symm M M.betaCrit 0 z
  rw [h1]
  exact hbz

/-! ## §4 The radial majorant conversion -/

/-- For `r ≥ 4` the source decay profile `r ↦ (log r)^{-1} r^{-e}` (`e > 0`) is dominated by the
majorant `Wt e 1 r = (1+r)^{-e} (log (2+r))^{-1}`. -/
theorem log_inv_mul_rpow_le_Wt {e : ℝ} (he : 0 < e) {r : ℝ} (hr : 4 < r) :
    (Real.log r)⁻¹ * r ^ (-e) ≤ 2 * (2 : ℝ) ^ e * Wt e 1 r := by
  have hr0 : (0 : ℝ) < r := by linarith
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have hlog_pos : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log (2 + r) := Real.log_pos (by linarith)
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) e
  have hpow : r ^ (-e) ≤ (2 : ℝ) ^ e * (1 + r) ^ (-e) := by
    have hle : 1 + r ≤ 2 * r := by linarith
    have hmono : (2 * r) ^ (-e) ≤ (1 + r) ^ (-e) :=
      Real.rpow_le_rpow_of_nonpos h1r hle (by linarith)
    have hsplit : (2 * r) ^ (-e) = (2 : ℝ) ^ (-e) * r ^ (-e) :=
      Real.mul_rpow (by norm_num) hr0.le
    have h2e' : (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      simp
    calc r ^ (-e) = 1 * r ^ (-e) := (one_mul _).symm
      _ = ((2 : ℝ) ^ e * (2 : ℝ) ^ (-e)) * r ^ (-e) := by rw [h2e']
      _ = (2 : ℝ) ^ e * ((2 * r) ^ (-e)) := by rw [hsplit]; ring
      _ ≤ (2 : ℝ) ^ e * (1 + r) ^ (-e) := mul_le_mul_of_nonneg_left hmono h2e.le
  have hlog : (Real.log r)⁻¹ ≤ 2 * (Real.log (2 + r))⁻¹ := by
    have hle : Real.log (2 + r) ≤ 2 * Real.log r := by
      have h2 : 2 + r ≤ 2 * r := by linarith
      have h3 : Real.log (2 + r) ≤ Real.log (2 * r) := Real.log_le_log (by linarith) h2
      have h4 : Real.log (2 * r) = Real.log 2 + Real.log r :=
        Real.log_mul (by norm_num) hr0.ne'
      have h5 : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) (by linarith)
      rw [h4] at h3
      linarith
    have h6 : (2 * Real.log r)⁻¹ ≤ (Real.log (2 + r))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hlog2 hle
    have h7 : (2 * Real.log r)⁻¹ = (Real.log r)⁻¹ / 2 := by
      rw [mul_inv]
      ring
    rw [h7] at h6
    linarith
  have hstep : (Real.log r)⁻¹ * r ^ (-e) ≤
      2 * (2 : ℝ) ^ e * ((Real.log (2 + r))⁻¹ * (1 + r) ^ (-e)) := by
    have hA : (0 : ℝ) ≤ (Real.log r)⁻¹ := le_of_lt (inv_pos.mpr hlog_pos)
    calc (Real.log r)⁻¹ * r ^ (-e)
        ≤ (2 * (Real.log (2 + r))⁻¹) * ((2 : ℝ) ^ e * (1 + r) ^ (-e)) :=
          mul_le_mul hlog hpow (Real.rpow_nonneg hr0.le _) (by positivity)
      _ = 2 * (2 : ℝ) ^ e * ((Real.log (2 + r))⁻¹ * (1 + r) ^ (-e)) := by ring
  have hWt : Wt e 1 r = (1 + r) ^ (-e) * (Real.log (2 + r)) ^ (-1 : ℝ) := rfl
  rw [hWt, Real.rpow_neg_one]
  refine hstep.trans (le_of_eq ?_)
  ring

/-- **The Case-3 radial majorant for `τ`.**  Case 3 of (HD) yields a positive constant `K` with
`|τ(z)| ≤ K · (1 + S.ρ z)^{-(d-2)} · (log (2 + S.ρ z))^{-1}` for every lattice point `z`. -/
theorem exists_abs_tau_le_Wt (h : M.Case3HD) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : M.V,
      |M.tau z| ≤ K * Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  obtain ⟨C', hC', hsrc⟩ := M.tau_le_of_case3 ⟨hd6, hα2, C, hC, hb⟩
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  have he : 0 < (M.d : ℝ) - 2 := by rw [hdR]; norm_num
  have hW4 : 0 < Wt ((M.d : ℝ) - 2) 1 4 := Wt_pos (by norm_num)
  have hB : 0 < C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2) := by
    have h2 : (0:ℝ) < (2 : ℝ) ^ ((M.d : ℝ) - 2) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hA : 0 < 1 / Wt ((M.d : ℝ) - 2) 1 4 := by
    rw [one_div]
    exact inv_pos.mpr hW4
  refine ⟨max (1 / Wt ((M.d : ℝ) - 2) 1 4) (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)) + 1, ?_,
    fun z => ?_⟩
  · have h := le_max_left (1 / Wt ((M.d : ℝ) - 2) 1 4)
      (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2))
    linarith
  have hr : (0 : ℝ) ≤ M.S.ρ (toVec z) := M.sρ_nonneg z
  have hK1 : 1 / Wt ((M.d : ℝ) - 2) 1 4
      ≤ max (1 / Wt ((M.d : ℝ) - 2) 1 4) (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)) :=
    le_max_left _ _
  have hK2 : C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)
      ≤ max (1 / Wt ((M.d : ℝ) - 2) 1 4) (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)) :=
    le_max_right _ _
  rw [abs_of_nonneg (M.tau_nonneg z)]
  rcases le_or_gt (M.S.ρ (toVec z)) 4 with hle4 | hgt4
  · have h1 := M.tau_le_one z
    have h2 : Wt ((M.d : ℝ) - 2) 1 4 ≤ Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) :=
      Wt_antitone he (by norm_num) hr hle4
    have hstep : (1 : ℝ) ≤
        (1 / Wt ((M.d : ℝ) - 2) 1 4) * Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) := by
      have hh := mul_le_mul_of_nonneg_left h2 hA.le
      rw [one_div_mul_cancel (ne_of_gt hW4)] at hh
      exact hh
    refine h1.trans (hstep.trans ?_)
    refine mul_le_mul_of_nonneg_right (le_trans hK1 (le_add_of_nonneg_right (by norm_num))) ?_
    exact (Wt_pos hr).le
  · have hz : z ≠ 0 := by
      rintro rfl
      have h0 : M.S.ρ (toVec (0 : M.V)) = 0 := by rw [toVec_zero M, M.S.ρ_zero]
      rw [h0] at hgt4
      linarith
    have hsrcz := hsrc z hz
    have hexp : (-(M.d : ℝ) + 2) = -((M.d : ℝ) - 2) := by ring
    rw [hexp] at hsrcz
    have hlogstep : (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) ≤
        2 * (2 : ℝ) ^ ((M.d : ℝ) - 2) * Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) :=
      log_inv_mul_rpow_le_Wt he hgt4
    calc M.tau z ≤ C' * ((Real.log (M.S.ρ (toVec z)))⁻¹ *
          (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2))) := by
          rw [← mul_assoc]; exact hsrcz
      _ ≤ C' * (2 * (2 : ℝ) ^ ((M.d : ℝ) - 2) *
            Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z))) :=
          mul_le_mul_of_nonneg_left hlogstep hC'.le
      _ = (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)) *
            Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (le_trans hK2 (le_add_of_nonneg_right (by norm_num))) ?_
          exact (Wt_pos hr).le

end SourceModelData
end PercLib.CriticalLRP.Orchestration
