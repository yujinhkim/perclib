/-
Swarm `smwu4e7s3`, member `m1`, direction `d1` (Direction A:
the explicit *repaired*, shifted-log source-norm Case 3 input).

# What this file is

`Orchestration.HD`'s third disjunct (the printed v1 Case 3 hypothesis) reads

  `τ_{β_c}(x,y) ≤ C * (log ρ)⁻¹ * ρ ^ (-d+2)`,  `ρ = M.S.ρ (toVec (x - y))`,

which is *not* adopted here.  This file studies the documented repair in which the inner
logarithm is shifted: `(log (1 + ρ))⁻¹` in place of `(log ρ)⁻¹`, written `HDCase3Shifted` below.
The repaired hypothesis is strictly weaker than the printed one away from `ρ = 1` and, unlike it,
is defined at every `0 < ρ` (no `ρ = 1` singularity and no negative branch).

The conclusion proved is `Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal)` at the
model's own normalized radius `M.S.dist 0 ·`, by converting the repaired source-norm hypothesis
into the sup-norm shell hypothesis consumed by the landed literal Case 3 bridge
(`Analysis/OpenTriangle/Case3Literal/Main.lean`, `...case3Shell` family).

# Constants (all explicit, none dropped)

* `logShiftConst c` is the cost of `log (1 + s) ≤ K log (1 + c s)` for `0 < c ≤ 1`, `s ≥ 1`,
  spent on the **input** side together with the lower comparison
  `srcLowerUnit S * ‖z‖ ≤ S.ρ (toVec z)` (the exponent `-4` is negative, so `ρ ≥ c ‖z‖` reverses
  the power in the needed direction);
* `logUpperConst S` is the cost of `log (1 + S.dist 0 y) ≤ K log (1 + ‖y‖)`, spent on the
  **output** side together with the upper comparison `S.dist 0 y ≤ srcUpperConst S * ‖y‖`
  (an *upper* bound on the radius is what pushes the sup-norm profile up to the source radius);
* `case3Conv3ConstShell` is the landed Case 3 threefold profile constant.

Both norm-comparison constants of the campaign therefore appear, each in the direction in which
its inequality is usable; the input uses `srcLowerUnit`, the output uses `srcUpperConst`.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3SourceNorm.Defs
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Literal.Model
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3Literal.Main
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail
public import PercLib.CriticalLRP.Analysis.Polygon.Model
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell

/-!
# The repaired (shifted-log) source-norm Case 3 transport: proofs

This module proves, from the repaired source-norm hypothesis `Case3ShiftedBound M C`
(`(log (1 + ρ))⁻¹ ρ ^ (-4)` at the model's normalized norm, *not* the printed `(log ρ)⁻¹`), that the
model's open-triangle tail `r ↦ (M.nablaTail r).toReal` is a logarithmically integrable error
function at the actual `M.S.dist` radius.

The route is: `log_one_add_le_logShiftConst_mul` (two-regime logarithmic comparison) →
`HD_to_supNorm_case3Shifted` (source ⇒ sup-norm shell domination, spending `srcLowerUnit`) →
the landed literal bridge `Case3Literal/Main` (`...case3Shell` family), transported from
`Fin 6 → ℤ` to `Fin M.d → ℤ` under `M.d = 6` → `openTriangle_toReal_le_logMajorant_case3Shifted`
(spending `srcUpperConst` through `logUpperConst`) → `isLogErrorFunction_nablaTail_of_toReal_le`.

Every constant is explicit; no hypothesis is added at any stage.
-/

set_option autoImplicit false

set_option linter.hashCommand false

@[expose] public section

open scoped ENNReal NNReal Topology
open Filter

namespace PercLib.CriticalLRP.Orchestration.HD.Case3

open CriticalLRPConv

/-- Positivity of the auxiliary logarithmic constant. -/
theorem logShiftAux_nonneg {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : 0 ≤ logShiftAux c := by
  have hB : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : (0 : ℝ) ≤ Real.log (1 / c) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hc]
    simpa using hc1
  unfold logShiftAux
  positivity

/-- Positivity of the logarithmic comparison constant. -/
theorem logShiftConst_pos {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : 0 < logShiftConst c := by
  have hT : (0 : ℝ) < Real.log (1 + 2 / c) := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < 2 / c := by positivity
    linarith
  have h1c : (0 : ℝ) < Real.log (1 + c) := Real.log_pos (by linarith)
  have h1 : (0 : ℝ) < Real.log (1 + 2 / c) / Real.log (1 + c) := div_pos hT h1c
  have h2 := logShiftAux_nonneg hc hc1
  unfold logShiftConst
  linarith

/-- **The key logarithmic comparison.**  For `0 < c ≤ 1` and `s ≥ 1`,
`log (1 + s) ≤ logShiftConst c * log (1 + c * s)`.

Two regimes, and both are needed: for `s ≤ 2/c` the left side is bounded by `log (1 + 2/c)` and
the right factor by `log (1 + c)`; for `s ≥ 2/c` one uses `log (1 + s) ≤ log 2 + log s` and
`log (1 + c s) ≥ log s - log (1/c)`, together with `log s ≥ log 2 + log (1/c)`.  No logarithm is
dropped and no hypothesis on the size of `c` is needed beyond `0 < c ≤ 1`. -/
theorem log_one_add_le_logShiftConst_mul {c s : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hs : 1 ≤ s) :
    Real.log (1 + s) ≤ logShiftConst c * Real.log (1 + c * s) := by
  have hB : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : (0 : ℝ) ≤ Real.log (1 / c) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hc]
    simpa using hc1
  have h1c : (0 : ℝ) < Real.log (1 + c) := Real.log_pos (by linarith)
  have hlogcs : (0 : ℝ) < Real.log (1 + c * s) := Real.log_pos (by nlinarith)
  have hT : (0 : ℝ) < Real.log (1 + 2 / c) := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < 2 / c := by positivity
    linarith
  have hK : Real.log (1 + 2 / c) / Real.log (1 + c) ≤ logShiftConst c := by
    have := logShiftAux_nonneg hc hc1
    unfold logShiftConst
    linarith
  rcases lt_or_ge s (2 / c) with hcase | hcase
  · -- regime 1: `s ≤ 2/c`
    have hcase : s ≤ 2 / c := hcase.le
    have hlog1 : Real.log (1 + s) ≤ Real.log (1 + 2 / c) := by
      refine Real.log_le_log (by linarith) ?_
      linarith
    have hlog2 : Real.log (1 + c) ≤ Real.log (1 + c * s) := by
      refine Real.log_le_log (by linarith) ?_
      nlinarith
    have hstep : Real.log (1 + s) ≤
        (Real.log (1 + 2 / c) / Real.log (1 + c)) * Real.log (1 + c * s) := by
      calc Real.log (1 + s) ≤ Real.log (1 + 2 / c) := hlog1
        _ = (Real.log (1 + 2 / c) / Real.log (1 + c)) * Real.log (1 + c) := by
            field_simp
        _ ≤ (Real.log (1 + 2 / c) / Real.log (1 + c)) * Real.log (1 + c * s) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
    exact hstep.trans (mul_le_mul_of_nonneg_right hK hlogcs.le)
  · -- regime 2: `s ≥ 2/c`
    have hs2 : 2 / c ≤ s := hcase
    have hD : Real.log 2 + Real.log (1 / c) ≤ Real.log s := by
      have hmul : Real.log 2 + Real.log (1 / c) = Real.log (2 * (1 / c)) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      have h2c : 2 * (1 / c) = 2 / c := by field_simp
      rw [hmul, h2c]
      exact Real.log_le_log (by positivity) hs2
    have hlog1 : Real.log (1 + s) ≤ Real.log 2 + Real.log s := by
      have h2 : 1 + s ≤ 2 * s := by linarith
      calc Real.log (1 + s) ≤ Real.log (2 * s) := Real.log_le_log (by linarith) h2
        _ = Real.log 2 + Real.log s := Real.log_mul (by norm_num) (by linarith)
    have hlog2 : Real.log s - Real.log (1 / c) ≤ Real.log (1 + c * s) := by
      have hcs : Real.log (c * s) = Real.log c + Real.log s :=
        Real.log_mul hc.ne' (by linarith)
      have hneg : Real.log c = -Real.log (1 / c) := by
        rw [Real.log_div (by norm_num) hc.ne']
        simp
      have hle : Real.log (c * s) ≤ Real.log (1 + c * s) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    have hkey : Real.log 2 + Real.log s ≤
        logShiftAux c * (Real.log s - Real.log (1 / c)) := by
      have hmain : Real.log 2 + Real.log s ≤
          ((Real.log (1 / c) + 3 * Real.log 2) / Real.log 2) *
            (Real.log s - Real.log (1 / c)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hB]
        nlinarith
      simpa only [logShiftAux] using hmain
    have hstep : Real.log (1 + s) ≤
        logShiftAux c * Real.log (1 + c * s) :=
      calc Real.log (1 + s) ≤ Real.log 2 + Real.log s := hlog1
        _ ≤ logShiftAux c * (Real.log s - Real.log (1 / c)) := hkey
        _ ≤ logShiftAux c * Real.log (1 + c * s) :=
            mul_le_mul_of_nonneg_left hlog2 (logShiftAux_nonneg hc hc1)
    have hge : logShiftAux c ≤ logShiftConst c := by
      have hpos : (0 : ℝ) < Real.log (1 + 2 / c) / Real.log (1 + c) := div_pos hT h1c
      unfold logShiftConst
      linarith
    exact hstep.trans (mul_le_mul_of_nonneg_right hge hlogcs.le)

/-! ## §1 The repaired source hypothesis implies the sup-norm shell domination -/

/-- The literal two-point function of the configured model at the origin is the `ofReal` of the
model's real two-point probability.  This is the bridge between `M.twoPoint` (the source object of
the hypothesis) and `twoPointFunction` (the lattice object of the Case 3 chain). -/
theorem twoPointFunction_eq_ofReal_twoPoint (M : SourceModelData) (β : ℝ≥0) (x y : M.V) :
    twoPointFunction M.kernel M.kernel_nonneg β x y = ENNReal.ofReal (M.twoPoint β x y) := by
  rw [← ENNReal.ofReal_toReal (twoPointFunction_ne_top M.kernel M.kernel_nonneg β x y)]
  rfl

/-- **Input conversion.**  The repaired source-norm hypothesis at `M.S.ρ` implies the sup-norm
domination the literal Case 3 bridge consumes, at `‖z‖ ≥ 2` and with the explicit constant
`case3SupConst (srcLowerUnit S) C = C * logShiftConst c * c ^ (-4)`, `c = srcLowerUnit S`.

The two comparison steps are:
* `log`-factor: `log ‖z‖ ≤ logShiftConst c * log (1 + c ‖z‖) ≤ logShiftConst c * log (1 + ρ)`,
  using `c ‖z‖ ≤ ρ` and `‖z‖ ≥ 2 ≥ 1` (so no intermediate source shell is skipped: the estimate
  is produced for *every* `‖z‖ ≥ 2`, not only for large `‖z‖`);
* power factor: `ρ ^ (-4) ≤ (c ‖z‖) ^ (-4) = c ^ (-4) * ‖z‖ ^ (-4)`, the negative exponent
  reversing `ρ ≥ c ‖z‖`.

No hypothesis on `ρ` at small radius is required: `1 + ρ > 1` for every `ρ > 0`, so the repaired
logarithm is bounded below on every shell, including the intermediate ones. -/
theorem HD_to_supNorm_case3Shifted (M : SourceModelData) {C : ℝ} (hC : 0 ≤ C)
    (hHD : Case3ShiftedBound M C) :
    ∀ z : M.V, 2 ≤ ‖z‖ →
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z
        ≤ ENNReal.ofReal (case3SupConst (srcLowerUnit M.S) C * ‖z‖ ^ (-(6 : ℝ) + 2)
            * (Real.log ‖z‖)⁻¹) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz
    linarith
  have hc : 0 < srcLowerUnit M.S := srcLowerUnit_pos M.S M.hd
  have hc1 : srcLowerUnit M.S ≤ 1 := srcLowerUnit_le_one M.S
  have hzpos : 0 < ‖z‖ := by linarith
  have hz1 : (1 : ℝ) ≤ ‖z‖ := by linarith
  -- the source norm at the pair `(0, z)`
  have hρeq : M.S.ρ (toVec ((0 : M.V) - z)) = M.S.ρ (toVec z) := by
    rw [show toVec ((0 : M.V) - z) = -(toVec z) from by funext i; simp [toVec]]
    exact M.S.ρ_neg (toVec z)
  have hρpos : 0 < M.S.ρ (toVec z) := by
    refine M.S.ρ_pos _ ?_
    intro h
    refine hz0 (funext fun i => ?_)
    have hi := congrFun h i
    simp only [toVec, Pi.zero_apply] at hi
    exact_mod_cast hi
  have hlow : srcLowerUnit M.S * ‖z‖ ≤ M.S.ρ (toVec z) := by
    have h := srcLowerUnit_mul_linfNorm_le M.S M.hd z
    rwa [← coe_norm_eq_linfNorm z] at h
  -- the hypothesis at `(0, z)`
  have hHDz := hHD 0 z (Ne.symm hz0)
  rw [hρeq, show (-(6 : ℝ) + 2) = (-4 : ℝ) by norm_num] at hHDz
  -- the logarithmic comparison
  have hKpos : 0 < logShiftConst (srcLowerUnit M.S) := logShiftConst_pos hc hc1
  have hcspos : (0 : ℝ) ≤ srcLowerUnit M.S * ‖z‖ := (mul_pos hc hzpos).le
  have hlog1 : Real.log ‖z‖
      ≤ logShiftConst (srcLowerUnit M.S) * Real.log (1 + srcLowerUnit M.S * ‖z‖) := by
    refine le_trans ?_ (log_one_add_le_logShiftConst_mul hc hc1 hz1)
    exact Real.log_le_log hzpos (by linarith)
  have hlog2 : Real.log (1 + srcLowerUnit M.S * ‖z‖) ≤ Real.log (1 + M.S.ρ (toVec z)) := by
    refine Real.log_le_log (by linarith) ?_
    linarith
  have hlogspos : 0 < Real.log ‖z‖ := Real.log_pos (by linarith)
  have hlogρpos : 0 < Real.log (1 + M.S.ρ (toVec z)) :=
    Real.log_pos (by linarith)
  have hlogle : Real.log ‖z‖
      ≤ logShiftConst (srcLowerUnit M.S) * Real.log (1 + M.S.ρ (toVec z)) :=
    hlog1.trans (mul_le_mul_of_nonneg_left hlog2 hKpos.le)
  have hlog : (Real.log (1 + M.S.ρ (toVec z)))⁻¹
      ≤ logShiftConst (srcLowerUnit M.S) * (Real.log ‖z‖)⁻¹ := by
    have hquot : Real.log ‖z‖ / logShiftConst (srcLowerUnit M.S)
        ≤ Real.log (1 + M.S.ρ (toVec z)) := by
      rw [div_le_iff₀ hKpos]
      linarith [hlogle]
    have hstep : (Real.log (1 + M.S.ρ (toVec z)))⁻¹
        ≤ (Real.log ‖z‖ / logShiftConst (srcLowerUnit M.S))⁻¹ :=
      inv_anti₀ (by positivity) hquot
    calc (Real.log (1 + M.S.ρ (toVec z)))⁻¹
        ≤ (Real.log ‖z‖ / logShiftConst (srcLowerUnit M.S))⁻¹ := hstep
      _ = logShiftConst (srcLowerUnit M.S) / Real.log ‖z‖ := inv_div _ _
      _ = logShiftConst (srcLowerUnit M.S) * (Real.log ‖z‖)⁻¹ := div_eq_mul_inv _ _
  -- the power comparison
  have hbase : 0 < srcLowerUnit M.S * ‖z‖ := mul_pos hc hzpos
  have hmono : (M.S.ρ (toVec z)) ^ (-(4 : ℝ)) ≤ (srcLowerUnit M.S * ‖z‖) ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hbase hlow (by norm_num)
  have hsplit : (srcLowerUnit M.S * ‖z‖) ^ (-(4 : ℝ))
      = srcLowerUnit M.S ^ (-(4 : ℝ)) * ‖z‖ ^ (-(4 : ℝ)) :=
    Real.mul_rpow hc.le hzpos.le
  -- assembly
  have hcomb : C * (Real.log (1 + M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(4 : ℝ))
      ≤ case3SupConst (srcLowerUnit M.S) C * ‖z‖ ^ (-(4 : ℝ))
          * (Real.log ‖z‖)⁻¹ := by
    have h1 : C * (Real.log (1 + M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(4 : ℝ))
        ≤ C * (logShiftConst (srcLowerUnit M.S) * (Real.log ‖z‖)⁻¹)
            * (M.S.ρ (toVec z)) ^ (-(4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC)
        (Real.rpow_nonneg hρpos.le _)
    have h2 : C * (logShiftConst (srcLowerUnit M.S) * (Real.log ‖z‖)⁻¹)
          * (M.S.ρ (toVec z)) ^ (-(4 : ℝ))
        ≤ C * (logShiftConst (srcLowerUnit M.S) * (Real.log ‖z‖)⁻¹)
            * (srcLowerUnit M.S ^ (-(4 : ℝ)) * ‖z‖ ^ (-(4 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hsplit ▸ hmono)
        (mul_nonneg hC (mul_nonneg hKpos.le (inv_nonneg.mpr hlogspos.le)))
    refine h1.trans (h2.trans (le_of_eq ?_))
    unfold case3SupConst
    ring
  have hτ : twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z
      = ENNReal.ofReal (M.twoPoint M.betaCrit 0 z) :=
    twoPointFunction_eq_ofReal_twoPoint M M.betaCrit 0 z
  rw [hτ, show (-(6 : ℝ) + 2) = (-4 : ℝ) by norm_num]
  exact ENNReal.ofReal_le_ofReal (hHDz.trans hcomb)

/-! ## §2 Dimension transport of the landed literal Case 3 bridge

The landed bridge is stated on `Fin 6 → ℤ`.  The model's lattice is `M.V = Fin M.d → ℤ`, so the
transfer below is stated with the dimension as a variable and the hypothesis `d = 6` is
substituted; nothing else changes. -/

/-- Nonzero integers vectors have sup-norm at least `1`, at every dimension. -/
theorem one_le_norm_of_ne_zero_gen {d : ℕ} {z : Fin d → ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ ‖z‖ := by
  have hone : (1 : ℕ) ≤ FiniteVolume.linfNorm z :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hz (FiniteVolume.linfNorm_eq_zero_iff.mp h))
  rw [CriticalLRPConv.coe_norm_eq_linfNorm]
  exact_mod_cast hone

/-- **Dimension transport** of `openTriangle_le_ofReal_logMajorant_case3Shell` to an arbitrary
`d` with `d = 6`, together with the passage to `toReal`. -/
theorem openTriangle_toReal_le_logMajorant_case3Shell_gen {d : ℕ} (h6 : d = 6)
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin d → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z
        ≤ ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {x : Fin d → ℤ} (hx : x ≠ 0) :
    (TriTail.openTriangle J hJ β 0 x).toReal
      ≤ Analysis.logMajorant (case3Conv3ConstShell C) 2 ‖x‖ := by
  subst h6
  have h := openTriangle_le_ofReal_logMajorant_case3Shell (J := J) (hJ := hJ) (β := β)
    hJinv hC hHD hx
  have hnn : (0 : ℝ) ≤ Analysis.logMajorant (case3Conv3ConstShell C) 2 ‖x‖ :=
    Analysis.logMajorant_nonneg (case3Conv3ConstShell_nonneg hC) (norm_nonneg x)
  calc (TriTail.openTriangle J hJ β 0 x).toReal
      ≤ (ENNReal.ofReal (Analysis.logMajorant (case3Conv3ConstShell C) 2 ‖x‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = Analysis.logMajorant (case3Conv3ConstShell C) 2 ‖x‖ := ENNReal.toReal_ofReal hnn

/-- **Dimension transport** of finiteness (`openTriangle_ne_top_case3Shell`). -/
theorem openTriangle_ne_top_case3Shell_gen {d : ℕ} (h6 : d = 6)
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin d → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z
        ≤ ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin d → ℤ) : TriTail.openTriangle J hJ β 0 x ≠ ⊤ := by
  subst h6
  exact openTriangle_ne_top_case3Shell hJinv hC hHD x

/-- Positivity of the output-side logarithmic comparison constant. -/
theorem logUpperConst_pos {d : ℕ} (S : SourceNormData d) : 0 < logUpperConst S := by
  have hB : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hU : (0 : ℝ) ≤ Real.log (srcUpperConst S) :=
    Real.log_nonneg (one_le_srcUpperConst S)
  unfold logUpperConst
  positivity

/-- `x ^ (-2) = (x ^ 2)⁻¹` for `x > 0`. -/
theorem rpow_neg_two_eq_inv_sq {x : ℝ} (hx : 0 < x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_two]

/-- `(a / K) ^ (-2) = K ^ 2 * a ^ (-2)` for `a, K > 0`. -/
theorem div_rpow_neg_two {a K : ℝ} (ha : 0 < a) (hK : 0 < K) :
    (a / K) ^ (-2 : ℝ) = K ^ 2 * a ^ (-2 : ℝ) := by
  rw [rpow_neg_two_eq_inv_sq (by positivity), rpow_neg_two_eq_inv_sq ha, div_pow]
  field_simp

/-- Nonnegativity of the sup-norm conversion constant. -/
theorem case3SupConst_nonneg {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C) :
    0 ≤ case3SupConst c C := by
  have hK : 0 < logShiftConst c := logShiftConst_pos hc hc1
  have hp : (0 : ℝ) < c ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hc _
  unfold case3SupConst
  positivity

/-- Nonnegativity of the source-norm Case 3 constant. -/
theorem case3SrcConst_nonneg {d : ℕ} (S : SourceNormData d) (hd : 1 ≤ d) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ case3SrcConst S C := by
  have hc : 0 < srcLowerUnit S := srcLowerUnit_pos S hd
  have hc1 : srcLowerUnit S ≤ 1 := srcLowerUnit_le_one S
  have h1 : 0 ≤ case3Conv3ConstShell (case3SupConst (srcLowerUnit S) C) :=
    case3Conv3ConstShell_nonneg (case3SupConst_nonneg hc hc1 hC)
  have h2 : (0 : ℝ) < (logUpperConst S) ^ 2 := pow_pos (logUpperConst_pos S) 2
  unfold case3SrcConst
  positivity

/-- `(a⁻¹)^2 = a ^ (-2)` for `a > 0`. -/
theorem inv_sq_eq_rpow_neg_two {a : ℝ} (ha : 0 < a) : (a⁻¹) ^ 2 = a ^ (-2 : ℝ) := by
  rw [Real.rpow_neg ha.le, Real.rpow_two]
  exact inv_pow a 2

/-! ## §3 The pointwise bound at the model's normalized norm -/

/-- **The pointwise square-logarithmic bound at the literal open triangle of the configured
model, at the model's own normalized radius `M.S.dist 0 ·`.**

This is the source-shaped (I.4.13) conclusion: `∇_{β_c}(0,y) ⪯ (log (1 + ‖y‖_S)) ^ (-2)`, with
the constant `case3SrcConst M.S C` carrying the input conversion, the output logarithmic
comparison (squared, because the profile is a square of an inverse logarithm) and the landed
Case 3 threefold profile constant.  The nonzero convention is `y ≠ 0`; the radius is positive
there (`0 < M.S.dist 0 y`), which is the exact hypothesis shape of `LogRadialBound`. -/
theorem openTriangle_toReal_le_logMajorant_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) :
    ∀ y : M.V, y ≠ 0 →
      (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
        ≤ Analysis.logMajorant (case3SrcConst M.S C) 2 (M.S.dist 0 y) := by
  intro y hy
  have hc : 0 < srcLowerUnit M.S := srcLowerUnit_pos M.S M.hd
  have hc1 : srcLowerUnit M.S ≤ 1 := srcLowerUnit_le_one M.S
  have hKpos : 0 < logShiftConst (srcLowerUnit M.S) := logShiftConst_pos hc hc1
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hy1 : (1 : ℝ) ≤ ‖y‖ := one_le_norm_of_ne_zero_gen hy
  have hsup := openTriangle_toReal_le_logMajorant_case3Shell_gen (d := M.d) h6
    (J := M.kernel) (hJ := M.kernel_nonneg) (β := M.betaCrit)
    M.kernel_shift (case3SupConst_nonneg hc hc1 hC) (C := case3SupConst (srcLowerUnit M.S) C)
    (HD_to_supNorm_case3Shifted M hC hHD) hy
  -- the normalized norm dominates `c ‖y‖`
  have hdist : M.S.dist 0 y = M.S.ρ (toVec y) := by
    rw [SourceNormData.dist,
      show toVec ((0 : M.V) - y) = -(toVec y) from by funext i; simp [toVec]]
    exact M.S.ρ_neg (toVec y)
  have hlow : srcLowerUnit M.S * ‖y‖ ≤ M.S.dist 0 y := by
    have h := srcLowerUnit_mul_linfNorm_le M.S M.hd y
    rw [← coe_norm_eq_linfNorm y, ← hdist] at h
    exact h
  have hdistpos : 0 < M.S.dist 0 y := lt_of_lt_of_le (mul_pos hc hypos) hlow
  -- the upper norm comparison, used for the *output* logarithm
  have hup : M.S.dist 0 y ≤ srcUpperConst M.S * ‖y‖ := by
    have h := srcNorm_le_upper_linfNorm M.S y
    rwa [← coe_norm_eq_linfNorm y, ← hdist] at h
  have hU1 : (1 : ℝ) ≤ srcUpperConst M.S := one_le_srcUpperConst M.S
  have hUpos : 0 < srcUpperConst M.S := srcUpperConst_pos M.S
  have hKU : 0 < logUpperConst M.S := logUpperConst_pos M.S
  have hsupypos : 0 < Real.log (1 + ‖y‖) := Real.log_pos (by linarith)
  have hdistlogpos : 0 < Real.log (1 + M.S.dist 0 y) := Real.log_pos (by linarith)
  -- logarithm comparison at the radius
  have hlogU : Real.log (1 + M.S.dist 0 y) ≤ logUpperConst M.S * Real.log (1 + ‖y‖) := by
    have h1 : 1 + M.S.dist 0 y ≤ srcUpperConst M.S * (1 + ‖y‖) := by nlinarith
    have h2 : Real.log (1 + M.S.dist 0 y)
        ≤ Real.log (srcUpperConst M.S) + Real.log (1 + ‖y‖) := by
      calc Real.log (1 + M.S.dist 0 y)
          ≤ Real.log (srcUpperConst M.S * (1 + ‖y‖)) := Real.log_le_log (by linarith) h1
        _ = Real.log (srcUpperConst M.S) + Real.log (1 + ‖y‖) :=
            Real.log_mul hUpos.ne' (by linarith)
    have hlog1y : Real.log 2 ≤ Real.log (1 + ‖y‖) := Real.log_le_log (by norm_num) (by linarith)
    have hU0 : (0 : ℝ) ≤ Real.log (srcUpperConst M.S) := Real.log_nonneg hU1
    have h3 : Real.log (srcUpperConst M.S)
        ≤ (Real.log (srcUpperConst M.S) / Real.log 2) * Real.log (1 + ‖y‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.log_pos (by norm_num))]
      nlinarith
    unfold logUpperConst
    linarith
  -- the squared logarithm is therefore bounded in the needed direction
  have hquot : Real.log (1 + M.S.dist 0 y) / logUpperConst M.S ≤ Real.log (1 + ‖y‖) := by
    rw [div_le_iff₀ hKU]
    linarith
  have hrpow : (Real.log (1 + ‖y‖)) ^ (-2 : ℝ)
      ≤ (logUpperConst M.S) ^ 2 * (Real.log (1 + M.S.dist 0 y)) ^ (-2 : ℝ) := by
    have hmono : (Real.log (1 + ‖y‖)) ^ (-2 : ℝ)
        ≤ (Real.log (1 + M.S.dist 0 y) / logUpperConst M.S) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos
        (by positivity : (0 : ℝ) < Real.log (1 + M.S.dist 0 y) / logUpperConst M.S)
        hquot (by norm_num : (-2 : ℝ) ≤ 0)
    calc (Real.log (1 + ‖y‖)) ^ (-2 : ℝ)
        ≤ (Real.log (1 + M.S.dist 0 y) / logUpperConst M.S) ^ (-2 : ℝ) := hmono
      _ = (logUpperConst M.S) ^ 2 * (Real.log (1 + M.S.dist 0 y)) ^ (-2 : ℝ) :=
          div_rpow_neg_two hdistlogpos hKU
  have hKsup : 0 ≤ case3Conv3ConstShell (case3SupConst (srcLowerUnit M.S) C) :=
    case3Conv3ConstShell_nonneg
      (case3SupConst_nonneg hc hc1 hC)
  calc (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
      ≤ Analysis.logMajorant (case3Conv3ConstShell (case3SupConst (srcLowerUnit M.S) C)) 2 ‖y‖ :=
        hsup
    _ = case3Conv3ConstShell (case3SupConst (srcLowerUnit M.S) C)
          * (Real.log (1 + ‖y‖)) ^ (-2 : ℝ) := rfl
    _ ≤ case3Conv3ConstShell (case3SupConst (srcLowerUnit M.S) C)
          * ((logUpperConst M.S) ^ 2
              * (Real.log (1 + M.S.dist 0 y)) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrpow hKsup
    _ = Analysis.logMajorant (case3SrcConst M.S C) 2 (M.S.dist 0 y) := by
        unfold case3SrcConst Analysis.logMajorant
        ring

/-- **Finiteness of the literal open triangle of the configured model** under the repaired input.
Derived from the explicit square-logarithmic bound at `‖·‖`; no `⊤` is ever coerced to `0`. -/
theorem openTriangle_ne_top_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) (y : M.V) :
    TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤ :=
  openTriangle_ne_top_case3Shell_gen (d := M.d) h6 M.kernel_shift
    (case3SupConst_nonneg (srcLowerUnit_pos M.S M.hd) (srcLowerUnit_le_one M.S) hC)
    (C := case3SupConst (srcLowerUnit M.S) C) (HD_to_supNorm_case3Shifted M hC hHD) y

/-- **The source-shaped pointwise bound `LogRadialBound`** at the model's normalized norm. -/
theorem logRadialBound_openTriangle_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) :
    Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
      (case3SrcConst M.S C) 2 :=
  M.logRadialBound_of_toReal_le
    (openTriangle_toReal_le_logMajorant_case3Shifted M h6 hC hHD)
    (fun y _ => openTriangle_ne_top_case3Shifted M h6 hC hHD y)

/-- **Lemma I.4.3, Case 3, at the configured model, from the repaired (shifted-log) source
hypothesis.**  Under `M.d = 6` and the shifted-log domination at `M.S.ρ`, the source
open-triangle tail `∇_r = M.nablaTail r` is a logarithmically integrable error function:
`∫^∞ ∇_r dr / r < ∞` and `∇_r → 0`.

The conclusion is at the model's own radius `M.S.dist 0 ·`, not the sup-norm radius; the radius
change is where `srcUpperConst` and `logUpperConst` are spent. -/
theorem isLogErrorFunction_nablaTail_of_HD_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) :=
  M.isLogErrorFunction_nablaTail_of_toReal_le
    (case3SrcConst_nonneg M.S M.hd hC) (by norm_num : (1 : ℝ) < 2)
    (openTriangle_toReal_le_logMajorant_case3Shifted M h6 hC hHD)
    (fun y _ => openTriangle_ne_top_case3Shifted M h6 hC hHD y)

/-- **The two conjuncts displayed**: logarithmic integrability of the tail and its vanishing. -/
theorem nablaTail_logIntegrable_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) :
    Analysis.LogarithmicallyIntegrable (fun r => (M.nablaTail r).toReal) ∧
      Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0) :=
  isLogErrorFunction_nablaTail_of_HD_case3Shifted M h6 hC hHD

/-- **The explicit source-norm tail bound** `∇_r ≤ C (log (1 + r)) ^ (-2)` for `r > 0`, with the
constant `case3SrcConst M.S C`.  This is the `ℝ≥0∞`-valued (I.4.13) form at the source radius. -/
theorem nablaTail_le_logMajorant_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) {r : ℝ} (hr : 0 < r) :
    M.nablaTail r
      ≤ ENNReal.ofReal (Analysis.logMajorant (case3SrcConst M.S C) 2 r) := by
  have h := Analysis.radialTailSup_le_logMajorant
    (nrm := fun y : M.V => M.S.dist 0 y)
    (F := fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
    (case3SrcConst_nonneg M.S M.hd hC) (by norm_num : (0 : ℝ) ≤ 2) hr
    (logRadialBound_openTriangle_case3Shifted M h6 hC hHD)
  exact h

/-- **The real-valued source-norm tail bound** `(∇_r).toReal ≤ C (log (1 + r)) ^ (-2)`. -/
theorem nablaTail_toReal_le_logMajorant_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) {r : ℝ} (hr : 0 < r) :
    (M.nablaTail r).toReal ≤ Analysis.logMajorant (case3SrcConst M.S C) 2 r := by
  have h := Analysis.radialTailSup_toReal_le
    (nrm := fun y : M.V => M.S.dist 0 y)
    (F := fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
    (case3SrcConst_nonneg M.S M.hd hC) (by norm_num : (0 : ℝ) ≤ 2) hr
    (logRadialBound_openTriangle_case3Shifted M h6 hC hHD)
  exact h

/-- **`∇_r → 0` in `ℝ≥0∞`** under the repaired hypothesis.  As in Case 2 this is read off from
uniform pointwise decay, not from Kozma's operator argument. -/
theorem tendsto_nablaTail_zero_of_HD_case3Shifted (M : SourceModelData) (h6 : M.d = 6)
    {C : ℝ} (hC : 0 ≤ C) (hHD : Case3ShiftedBound M C) :
    Tendsto (fun r => M.nablaTail r) atTop (𝓝 0) :=
  M.tendsto_nablaTail_zero (case3SrcConst_nonneg M.S M.hd hC) (by norm_num : (1 : ℝ) < 2)
    (logRadialBound_openTriangle_case3Shifted M h6 hC hHD)

/-! ## §5 The repaired third disjunct, packaged -/

/-- **Lemma I.4.3, Case 3, under the repaired disjunct shape** `HDCase3Shifted M`:
`d = 6`, `α = 2`, and the shifted-log source domination for some `C > 0`. -/
theorem isLogErrorFunction_nablaTail_of_HDCase3Shifted (M : SourceModelData)
    (h : HDCase3Shifted M) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  obtain ⟨h6, -, C, hC, hHD⟩ := h
  exact isLogErrorFunction_nablaTail_of_HD_case3Shifted M h6 hC.le hHD

/-- The packaged bridge: pointwise source bound, finiteness, `LogRadialBound`, the tail bound in
`ℝ≥0∞` and in `ℝ`, and the error-function conclusion, all from the repaired input. -/
theorem case3SourceBridge_shifted (M : SourceModelData) (h6 : M.d = 6) {C : ℝ} (hC : 0 ≤ C)
    (hHD : Case3ShiftedBound M C) :
    (∀ y : M.V, y ≠ 0 →
        (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
          ≤ Analysis.logMajorant (case3SrcConst M.S C) 2 (M.S.dist 0 y)) ∧
      (∀ y : M.V,
        TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤) ∧
      Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
        (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
        (case3SrcConst M.S C) 2 ∧
      Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) ∧
      Tendsto (fun r => M.nablaTail r) atTop (𝓝 0) :=
  ⟨openTriangle_toReal_le_logMajorant_case3Shifted M h6 hC hHD,
    fun y => openTriangle_ne_top_case3Shifted M h6 hC hHD y,
    logRadialBound_openTriangle_case3Shifted M h6 hC hHD,
    isLogErrorFunction_nablaTail_of_HD_case3Shifted M h6 hC hHD,
    tendsto_nablaTail_zero_of_HD_case3Shifted M h6 hC hHD⟩

/-- **Honest comparison with the printed v1 hypothesis, on the shell where the printed logarithm is
positive.**  At `ρ ≥ 2`, `log (1 + ρ) ≤ log (2 ρ) = log 2 + log ρ ≤ 2 log ρ`, so the printed
(unshifted) domination implies the repaired one with constant `2 C` on that shell.

This is a *one-way* comparison and only on `ρ ≥ 2`.  No global equivalence is asserted: on
`1 < ρ < 2` the printed right-hand side is the smaller one (and on `0 < ρ < 1` it is negative), so
the printed hypothesis there is strictly stronger than the repaired one, and nothing in this file
identifies the two.  The repaired theorems above do not use this lemma. -/
theorem case3ShiftedBound_of_printedBound_shell (M : SourceModelData) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y
        ≤ C * (Real.log (M.S.dist x y))⁻¹ * (M.S.dist x y) ^ (-(6 : ℝ) + 2)) :
    ∀ x y : M.V, x ≠ y → 2 ≤ M.S.dist x y →
      M.twoPoint M.betaCrit x y
        ≤ (2 * C) * (Real.log (1 + M.S.dist x y))⁻¹ * (M.S.dist x y) ^ (-(6 : ℝ) + 2) := by
  intro x y hxy hρ
  have hρpos : 0 < M.S.dist x y := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogρ : Real.log 2 ≤ Real.log (M.S.dist x y) := Real.log_le_log (by norm_num) hρ
  have hlogpos : 0 < Real.log (M.S.dist x y) := by linarith
  have hkey : Real.log (1 + M.S.dist x y) ≤ 2 * Real.log (M.S.dist x y) := by
    have h2 : 1 + M.S.dist x y ≤ 2 * M.S.dist x y := by linarith
    have h3 : Real.log (1 + M.S.dist x y) ≤ Real.log (2 * M.S.dist x y) :=
      Real.log_le_log (by linarith) h2
    have h4 : Real.log (2 * M.S.dist x y)
        = Real.log 2 + Real.log (M.S.dist x y) :=
      Real.log_mul (by norm_num) hρpos.ne'
    linarith
  have hlog1pos : 0 < Real.log (1 + M.S.dist x y) := Real.log_pos (by linarith)
  have hinv : (Real.log (M.S.dist x y))⁻¹ ≤ 2 * (Real.log (1 + M.S.dist x y))⁻¹ := by
    have hquot : Real.log (1 + M.S.dist x y) / 2 ≤ Real.log (M.S.dist x y) := by linarith
    calc (Real.log (M.S.dist x y))⁻¹
        ≤ (Real.log (1 + M.S.dist x y) / 2)⁻¹ :=
          inv_anti₀ (by linarith) hquot
      _ = 2 * (Real.log (1 + M.S.dist x y))⁻¹ := by
          rw [inv_div]
          ring
  have hpow : 0 ≤ (M.S.dist x y) ^ (-(6 : ℝ) + 2) :=
    Real.rpow_nonneg hρpos.le _
  calc M.twoPoint M.betaCrit x y
      ≤ C * (Real.log (M.S.dist x y))⁻¹ * (M.S.dist x y) ^ (-(6 : ℝ) + 2) := h x y hxy
    _ ≤ C * (2 * (Real.log (1 + M.S.dist x y))⁻¹) * (M.S.dist x y) ^ (-(6 : ℝ) + 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hpow
        exact mul_le_mul_of_nonneg_left hinv hC
    _ = (2 * C) * (Real.log (1 + M.S.dist x y))⁻¹ * (M.S.dist x y) ^ (-(6 : ℝ) + 2) := by
        ring


end PercLib.CriticalLRP.Orchestration.HD.Case3

open PercLib.CriticalLRP.Orchestration.HD.Case3

#print axioms log_one_add_le_logShiftConst_mul
#print axioms HD_to_supNorm_case3Shifted
#print axioms openTriangle_toReal_le_logMajorant_case3Shell_gen
#print axioms openTriangle_ne_top_case3Shell_gen
#print axioms openTriangle_toReal_le_logMajorant_case3Shifted
#print axioms openTriangle_ne_top_case3Shifted
#print axioms logRadialBound_openTriangle_case3Shifted
#print axioms isLogErrorFunction_nablaTail_of_HD_case3Shifted
#print axioms nablaTail_le_logMajorant_case3Shifted
#print axioms nablaTail_toReal_le_logMajorant_case3Shifted
#print axioms tendsto_nablaTail_zero_of_HD_case3Shifted
#print axioms isLogErrorFunction_nablaTail_of_HDCase3Shifted
#print axioms case3SourceBridge_shifted
#print axioms case3ShiftedBound_of_printedBound_shell

#print axioms logShiftAux_nonneg
#print axioms logShiftConst_pos
#print axioms twoPointFunction_eq_ofReal_twoPoint
#print axioms one_le_norm_of_ne_zero_gen
#print axioms logUpperConst_pos
#print axioms rpow_neg_two_eq_inv_sq
#print axioms div_rpow_neg_two
#print axioms case3SupConst_nonneg
#print axioms case3SrcConst_nonneg
#print axioms inv_sq_eq_rpow_neg_two
#print axioms nablaTail_logIntegrable_case3Shifted
