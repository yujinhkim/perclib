/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m4/Main.lean`.

Swarm `smwzlje3f`, member `m4`, direction `d4` — (E) the HD(3) / triangle / tail inputs.

# `hTri` and `hF` from Case 3 of (HD): the two convolution stages and the model bridge

The Case-3 consumer of Proposition I.4.15 retains two structural inputs of §I.4.1:

* `hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤`
  — Kozma's triangle condition `∇_{β_c} < ∞`; the paper *assumes* it in the second assertion of
  Proposition I.4.15 and in its Case-3 proof, and only derives the *off-diagonal* bound (I.4.13)
  from (HD)(3).
* `hF` — the log-radial decay `∇_{β_c}(0,x) ⪯ (log ‖x‖)^{-2}` of (I.4.13).

This file derives **both** from Case 3 of (HD) alone, by running the source's convolution estimate
(I.4.12) twice at the actual source norm:

* **Stage 1** (`exists_tauConv_bound`): `τ` decays like `⟨·⟩^{-(d-2)} Λ^{-1}`, so the *strict* case
  `a + b = 2 + 2 < d = 6` of (I.4.12) gives `(τ * τ)(x) ⪯ ⟨x⟩^{-2} Λ(x)^{-2}`
  (`SrcNormConv.conv_tsum_le_srcNorm_via_sup`).
* **Stage 2** (`exists_tauConvConv_bound`): `τ` and `τ * τ` in the *marginal* case
  `a + b = 2 + 4 = d`, where (I.4.12) gives the single remaining logarithm
  `Λ^{-(1+2-1)} = Λ^{-2}` (`SrcNormConv.conv_tsum_le_marg_srcNorm`).

Then `openTriangle_eq_ofReal_tauConvConv` identifies the `ℝ≥0∞`-valued open triangle with
`ofReal` of the real triple convolution (translation invariance + symmetry of `twoPointFunction`),
which turns Stage 2 at a general point into `hF` and Stage 2 at the origin into `hTri`.

The final consumer `secondMoment_asymptotic_case3_of_case3HD` therefore has **no** `hTri` and
**no** `hF`: it takes Case 3 of (HD) instead.  Everything else is unchanged, including the
measurability, logarithmic-integrability, finiteness and moment-gap inputs.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Pointwise
public import PercLib.CriticalLRP.Analysis.TriTail.Defs
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer

set_option linter.style.longLine false
set_option linter.hashCommand false
@[expose] public section

open scoped ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

open PercLib.CriticalLRP CriticalLRPConv

variable (M : SourceModelData)

/-! ## §1 Nonnegativity of the transfer constants and of the convolutions -/

theorem srcTransferConst_nonneg (a b ah bh : ℝ) :
    0 ≤ SrcNormConv.srcTransferConst (d := M.d) M.S a b ah bh := by
  have hLU : (0 : ℝ) < srcLowerUnit M.S := srcLowerUnit_pos M.S M.hd
  have hLog : (0 : ℝ) < srcLogConst M.S := srcLogConst_pos M.S M.hd
  have hU : (0 : ℝ) < srcUpperConst M.S := srcUpperConst_pos M.S
  have hLogU : (0 : ℝ) < srcLogConstUpper M.S := SrcNormConv.srcLogConstUpper_pos M.S
  rw [SrcNormConv.srcTransferConst]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hLU.le _) (Real.rpow_nonneg hLog.le _))
      (mul_nonneg (Real.rpow_nonneg hLU.le _) (Real.rpow_nonneg hLog.le _)))
    (mul_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hLogU.le _))

/-- The stage-1 constant: the two profile constants times the strict-regime transfer and
region constants of (I.4.12) at `a = b = 2`, `â = b̂ = 1`. -/
noncomputable def stage1Const (Cτ : ℝ) : ℝ :=
  Cτ * Cτ * (SrcNormConv.srcTransferConst (d := M.d) M.S 2 2 1 1 *
    CriticalLRPConv.convConst M.d 2 2 1 1)

/-- The stage-2 constant: the marginal (`a + b = d`) transfer and assembly constants at
`a = 2`, `b = 4`, `â = 1`, `b̂ = 2`. -/
noncomputable def stage2Const (Cτ K₁ : ℝ) : ℝ :=
  Cτ * K₁ * SrcNormConv.srcMargConst (d := M.d) M.S 2 4 1 2

theorem stage1Const_nonneg {Cτ : ℝ} (hCτ : 0 ≤ Cτ) (hd6 : M.d = 6) :
    0 ≤ M.stage1Const Cτ := by
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  have h1 : (0 : ℝ) ≤ SrcNormConv.srcTransferConst (d := M.d) M.S 2 2 1 1 :=
    M.srcTransferConst_nonneg 2 2 1 1
  have h2 : (0 : ℝ) ≤ CriticalLRPConv.convConst M.d 2 2 1 1 :=
    SrcNormConv.convConst_nonneg M.hd (by norm_num) (by norm_num)
      (by rw [hdR]; norm_num) (by norm_num) (by norm_num)
  rw [stage1Const]
  exact mul_nonneg (mul_nonneg hCτ hCτ) (mul_nonneg h1 h2)

theorem stage2Const_nonneg {Cτ K₁ : ℝ} (hCτ : 0 ≤ Cτ) (hK₁ : 0 ≤ K₁) (hd6 : M.d = 6) :
    0 ≤ M.stage2Const Cτ K₁ := by
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  have h1 : (0 : ℝ) ≤ SrcNormConv.srcMargConst (d := M.d) M.S 2 4 1 2 :=
    SrcNormConv.srcMargConst_nonneg M.S M.hd (by norm_num) (by norm_num)
      (by rw [hdR]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [stage2Const]
  exact mul_nonneg (mul_nonneg hCτ hK₁) h1

/-- The double convolution of a nonnegative profile is nonnegative. -/
theorem tauConv_nonneg (x : M.V) : 0 ≤ M.tauConv x :=
  tsum_nonneg fun y => mul_nonneg (M.tau_nonneg y) (M.tau_nonneg (x - y))

/-- The triple convolution of a nonnegative profile is nonnegative. -/
theorem tauConvConv_nonneg (x : M.V) : 0 ≤ M.tauConvConv x :=
  tsum_nonneg fun y => mul_nonneg (M.tau_nonneg y) (M.tauConv_nonneg (x - y))

/-! ## §2 Stage 1: the strict case `a + b = 2 + 2 < d` -/

/-- **Stage 1 of (I.4.12) at the source model.**  From the Case-3 pointwise decay of `τ` the
double convolution `τ * τ` is summable everywhere and decays like `⟨·⟩^{-2} Λ^{-2}`. -/
theorem exists_tauConv_bound (h : M.Case3HD) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ (∀ x : M.V, Summable fun y : M.V => M.tau y * M.tau (x - y)) ∧
      ∀ x : M.V, |M.tauConv x| ≤ K₁ * Wt ((M.d : ℝ) - 4) 2 (M.S.ρ (toVec x)) := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  obtain ⟨Cτ, hCτ, hτ⟩ := M.exists_abs_tau_le_Wt ⟨hd6, hα2, C, hC, hb⟩
  have hCτ0 : 0 ≤ Cτ := hCτ.le
  have hab : (2 : ℝ) + 2 < (M.d : ℝ) := by rw [hdR]; norm_num
  have hK1 : ∀ x : M.V, Summable (fun y : M.V => M.tau y * M.tau (x - y)) ∧
      |∑' y : M.V, M.tau y * M.tau (x - y)| ≤
        Cτ * Cτ * (SrcNormConv.srcTransferConst (d := M.d) M.S 2 2 1 1 *
          (CriticalLRPConv.convConst M.d 2 2 1 1 *
            Wt ((M.d : ℝ) - 2 - 2) (1 + 1) (M.S.ρ (toVec x)))) := by
    intro x
    exact SrcNormConv.conv_tsum_le_srcNorm_via_sup (d := M.d) (S := M.S) M.hd
      (a := 2) (b := 2) (ah := 1) (bh := 1) (by norm_num) (by norm_num) hab
      (by norm_num) (by norm_num) (f := M.tau) (g := M.tau) (Cf := Cτ) (Cg := Cτ)
      hCτ0 hCτ0 hτ hτ x
  refine ⟨M.stage1Const Cτ, M.stage1Const_nonneg hCτ0 hd6, fun x => (hK1 x).1, fun x => ?_⟩
  rw [tauConv]
  refine (hK1 x).2.trans (le_of_eq ?_)
  rw [stage1Const,
    show ((M.d : ℝ) - 2 - 2) = ((M.d : ℝ) - 4) from by ring,
    show (1 : ℝ) + 1 = 2 from by norm_num]
  ring

/-! ## §3 Stage 2: the marginal case `a + b = 2 + 4 = d` -/

/-- **Stage 2 of (I.4.12) at the source model.**  `τ` copied against `τ * τ` in the marginal
regime `2 + 4 = d = 6` produces the single-logarithm target `Λ^{-2}` of (I.4.13). -/
theorem exists_tauConvConv_bound (h : M.Case3HD) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ (∀ x : M.V, Summable fun y : M.V => M.tau y * M.tauConv (x - y)) ∧
      ∀ x : M.V, |M.tauConvConv x| ≤ K₂ * Wt 0 2 (M.S.ρ (toVec x)) := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  obtain ⟨Cτ, hCτ, hτ⟩ := M.exists_abs_tau_le_Wt ⟨hd6, hα2, C, hC, hb⟩
  obtain ⟨K₁, hK₁, -, hb1⟩ := M.exists_tauConv_bound ⟨hd6, hα2, C, hC, hb⟩
  have hab : (2 : ℝ) + 4 = (M.d : ℝ) := by rw [hdR]; norm_num
  have hK2 : ∀ x : M.V, Summable (fun y : M.V => M.tau y * M.tauConv (x - y)) ∧
      |∑' y : M.V, M.tau y * M.tauConv (x - y)| ≤
        Cτ * K₁ * (SrcNormConv.srcMargConst (d := M.d) M.S 2 4 1 2 *
          SrcNormConv.srcMargTarget (d := M.d) M.S 1 2 x) := by
    intro x
    exact SrcNormConv.conv_tsum_le_marg_srcNorm (d := M.d) (S := M.S)
      (a := 2) (b := 4) (ah := 1) (bh := 2) (by norm_num) (by norm_num) hab
      (by norm_num) (by norm_num) (by norm_num) (f := M.tau) (g := M.tauConv)
      (Cf := Cτ) (Cg := K₁) hCτ.le hK₁ hτ hb1 x
  refine ⟨M.stage2Const Cτ K₁, M.stage2Const_nonneg hCτ.le hK₁ hd6, fun x => (hK2 x).1,
    fun x => ?_⟩
  rw [tauConvConv]
  refine (hK2 x).2.trans (le_of_eq ?_)
  rw [stage2Const, SrcNormConv.srcMargTarget, show (1 : ℝ) + 2 - 1 = 2 from by norm_num]
  ring

/-! ## §4 The model bridge: the open triangle is `ofReal` of the real triple convolution -/

/-- The `ℝ≥0∞`-valued two-point function is `ofReal` of the real profile. -/
theorem twoPointFunction_eq_ofReal_tau (x y : M.V) :
    twoPointFunction M.kernel M.kernel_nonneg M.betaCrit x y
      = ENNReal.ofReal (M.tau (y - x)) := by
  rw [twoPointFunction_eq_origin (J := M.kernel) M.kernel_shift M.kernel_nonneg M.betaCrit x y]
  exact (M.ofReal_tau (y - x)).symm

/-- **The bridge.**  The `ℝ≥0∞`-valued open triangle `∇_{β_c}(0,x)` is `ofReal` of the real
triple convolution `τ * τ * τ` of the origin profile.  Uses translation invariance
(`kernel_shift`), symmetry (`twoPointFunction_comm`) and `τ ≤ 1`. -/
theorem openTriangle_eq_ofReal_tauConvConv (x : M.V)
    (hinn : ∀ u : M.V, Summable (fun w : M.V => M.tau u * M.tau w * M.tau (x - u - w)))
    (hout : Summable (fun u : M.V => M.tau u * M.tauConv (x - u))) :
    TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x
      = ENNReal.ofReal (M.tauConvConv x) := by
  have hstep1 : TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x
      = ∑' u : M.V, ∑' v : M.V,
          ENNReal.ofReal (M.tau u * M.tau (v - u) * M.tau (x - v)) := by
    simp only [TriTail.openTriangle]
    refine tsum_congr fun u => tsum_congr fun v => ?_
    rw [show twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 u
        = ENNReal.ofReal (M.tau u) from (M.ofReal_tau u).symm]
    rw [twoPointFunction_eq_ofReal_tau (M := M) u v, twoPointFunction_eq_ofReal_tau (M := M) v x]
    have hA : ENNReal.ofReal (M.tau u) * ENNReal.ofReal (M.tau (v - u))
        = ENNReal.ofReal (M.tau u * M.tau (v - u)) :=
      (ENNReal.ofReal_mul (M.tau_nonneg u)).symm
    have hB : ENNReal.ofReal (M.tau u * M.tau (v - u)) * ENNReal.ofReal (M.tau (x - v))
        = ENNReal.ofReal (M.tau u * M.tau (v - u) * M.tau (x - v)) :=
      (ENNReal.ofReal_mul (mul_nonneg (M.tau_nonneg u) (M.tau_nonneg (v - u)))).symm
    calc ENNReal.ofReal (M.tau u) * ENNReal.ofReal (M.tau (v - u))
          * ENNReal.ofReal (M.tau (x - v))
        = ENNReal.ofReal (M.tau u * M.tau (v - u)) * ENNReal.ofReal (M.tau (x - v)) := by
          rw [hA]
      _ = ENNReal.ofReal (M.tau u * M.tau (v - u) * M.tau (x - v)) := hB
  rw [hstep1]
  have hstep2 : (∑' u : M.V, ∑' v : M.V,
        ENNReal.ofReal (M.tau u * M.tau (v - u) * M.tau (x - v)))
      = ∑' u : M.V, ENNReal.ofReal (M.tau u * M.tauConv (x - u)) := by
    refine tsum_congr fun u => ?_
    have hre : (∑' v : M.V, ENNReal.ofReal (M.tau u * M.tau (v - u) * M.tau (x - v)))
        = ∑' w : M.V, ENNReal.ofReal (M.tau u * M.tau w * M.tau (x - u - w)) := by
      have hG : ∀ v : M.V, ENNReal.ofReal (M.tau u * M.tau (v - u) * M.tau (x - v))
          = ENNReal.ofReal (M.tau u * M.tau (v - u) * M.tau (x - u - (v - u))) := by
        intro v
        rw [show x - v = x - u - (v - u) from by abel]
      simp only [hG]
      exact Equiv.tsum_eq (Equiv.subRight u)
        (fun w => ENNReal.ofReal (M.tau u * M.tau w * M.tau (x - u - w)))
    rw [hre]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun w => mul_nonneg (mul_nonneg (M.tau_nonneg u) (M.tau_nonneg w))
        (M.tau_nonneg (x - u - w))) (hinn u)]
    congr 1
    rw [show M.tauConv (x - u) = ∑' w : M.V, M.tau w * M.tau ((x - u) - w) from rfl]
    rw [← tsum_mul_left]
    exact tsum_congr fun w => by ring
  rw [hstep2]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun u => mul_nonneg (M.tau_nonneg u) (M.tauConv_nonneg (x - u))) hout]
  rfl

/-! ## §5 `hTri` and `hF` from Case 3 of (HD) -/

/-- **The triangle condition from Case 3 of (HD).**  `∇_{β_c}(0,0) < ⊤`: the real triple
convolution of `τ` converges at the origin, because `τ ⪯ ⟨·⟩^{-4} Λ^{-1}` and
`τ * τ ⪯ ⟨·⟩^{-2} Λ^{-2}` make the marginal product `⟨·⟩^{-6} Λ^{-3}` summable. -/
theorem openTriangleSelf_lt_top_of_case3 (h : M.Case3HD) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ := by
  obtain ⟨-, -, hsum1, -⟩ := M.exists_tauConv_bound h
  obtain ⟨-, -, hsum2, -⟩ := M.exists_tauConvConv_bound h
  have hinn : ∀ u : M.V, Summable (fun w : M.V => M.tau u * M.tau w * M.tau (0 - u - w)) := by
    intro u
    have h' := (hsum1 ((0 : M.V) - u)).mul_left (M.tau u)
    refine h'.congr fun w => ?_
    ring
  have hbridge := M.openTriangle_eq_ofReal_tauConvConv 0 hinn (hsum2 0)
  change TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 0 < ⊤
  rw [hbridge]
  exact ENNReal.ofReal_lt_top

/-- The majorant `Wt 0 2 s = (log (2+s))^{-2}` is dominated by the source's logarithmic profile
`logMajorant C 2 s = C (log (1+s))^{-2}` at positive radius. -/
theorem Wt_zero_two_le_logMajorant {C s : ℝ} (hC : 0 ≤ C) (hs : 0 < s) :
    C * Wt 0 2 s ≤ Analysis.logMajorant C 2 s := by
  have hle : Real.log (1 + s) ≤ Real.log (2 + s) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog1 : (0 : ℝ) < Real.log (1 + s) := Real.log_pos (by linarith)
  have hmono : (Real.log (2 + s)) ^ (-2 : ℝ) ≤ (Real.log (1 + s)) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlog1 hle (by norm_num)
  have hWt : Wt 0 2 s = (Real.log (2 + s)) ^ (-(2 : ℝ)) := by
    simp [CriticalLRPConv.Wt, CriticalLRPConv.LamR]
  rw [hWt, Analysis.logMajorant]
  exact mul_le_mul_of_nonneg_left hmono hC

/-- **`hF` from Case 3 of (HD).**  The open-triangle log-radial bound (I.4.13) with exponent
`p = 2`, at the model's own source norm `S.dist 0 ·`. -/
theorem logRadialBound_openTriangle_of_case3 (h : M.Case3HD) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ 2 := by
  obtain ⟨K₂, hK₂, hsum2, hb2⟩ := M.exists_tauConvConv_bound h
  obtain ⟨-, -, hsum1, -⟩ := M.exists_tauConv_bound h
  refine ⟨K₂, hK₂, fun y hy => ?_⟩
  have hinn : ∀ u : M.V, Summable (fun w : M.V => M.tau u * M.tau w * M.tau (y - u - w)) := by
    intro u
    have h' := (hsum1 (y - u)).mul_left (M.tau u)
    refine h'.congr fun w => ?_
    ring
  change TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y
      ≤ ENNReal.ofReal (Analysis.logMajorant K₂ 2 (M.S.dist 0 y))
  rw [M.openTriangle_eq_ofReal_tauConvConv y hinn (hsum2 y)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsd : M.S.dist 0 y = M.S.ρ (toVec y) := CriticalLRPConv.dist_zero_eq_srcNorm M.S y
  have hb : |M.tauConvConv y| ≤ K₂ * Wt 0 2 (M.S.dist 0 y) := by
    rw [hsd]
    exact hb2 y
  calc M.tauConvConv y ≤ K₂ * Wt 0 2 (M.S.dist 0 y) := (abs_le.mp hb).2
    _ ≤ Analysis.logMajorant K₂ 2 (M.S.dist 0 y) :=
        Wt_zero_two_le_logMajorant hK₂ hy

/-- **Lemma I.4.3 in Case 3 of (HD).**  The open-triangle tail `∇_r` is a logarithmically
integrable error function, which is the source's statement that "if Cases 2 or 3 of (HD) hold then
`∇_r` is logarithmically integrable".  This is the form consumed by the I.4.15/I.4.20 estimates
that need `∫^∞ ∇_r dr / r < ∞` and `∇_r → 0`. -/
theorem isLogErrorFunction_nablaTail_of_case3 (h : M.Case3HD) :
    Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal) := by
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3 h
  exact M.isLogErrorFunction_nablaTail hC₀ (by norm_num) hF

/-! ## §6 The Case-3 consumer with `hTri` and `hF` discharged -/

/-- **Proposition I.4.15, Case 3, from Case 3 of (HD).**  Identical to
`secondMoment_asymptotic_case3_of_source_p21` except that the two structural §I.4.1 inputs `hTri`
and `hF` are gone: they are *derived* from `(HD)(3)`.  Every other input — the ODE regularity
`hac`, `hae`, the first two cutoff moments `h1`, `h2`, the first-moment asymptotic `hP`, the
measurabilities, the logarithmic integrabilities and the moment gap `hgm` — is retained
unchanged. -/
theorem secondMoment_asymptotic_case3_of_case3HD (h : M.Case3HD)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have hα : 0 < M.α := by
    rw [h.2.1]
    norm_num
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3 h
  exact M.secondMoment_asymptotic_case3_of_source_p21 hα hr₀ hβ hac hae h1 h2 hP
    (M.openTriangleSelf_lt_top_of_case3 h) (C₀ := C₀) hC₀ (by norm_num) hF
    hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm

/-! ## §7 The remaining Case-3 source wrappers with `hTri` and `hF` discharged -/

/-- **`𝓔_{2,r} → 0` in Case 3, from Case 3 of (HD).**  `p2ExclError_tendsto_zero_of_source_p21`
without `hTri`, `hF`. -/
theorem p2ExclError_tendsto_zero_of_case3HD (h : M.Case3HD) {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3 h
  exact M.p2ExclError_tendsto_zero_of_source_p21 h1 h2 hP
    (M.openTriangleSelf_lt_top_of_case3 h) hC₀ (by norm_num) hF hc3 hgm

/-- **Logarithmic integrability of `𝓔_{2,r}` in Case 3, from Case 3 of (HD).**
`logIntegrable_p2ExclError_of_source_p21` without `hTri`, `hF`. -/
theorem logIntegrable_p2ExclError_of_case3HD (h : M.Case3HD) {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hmeas : Measurable M.p2ExclError)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3 h
  exact M.logIntegrable_p2ExclError_of_source_p21 h1 h2 hmeas hP
    (M.openTriangleSelf_lt_top_of_case3 h) hC₀ (by norm_num) hF hc3 hgm

/-- **Regular variation of `𝓔_{2,r}` in Case 3, from Case 3 of (HD).**
`regularlyVarying_two_of_source_p21` without `hTri`, `hF`. -/
theorem regularlyVarying_two_of_case3HD (h : M.Case3HD) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  have hα : 0 < M.α := by
    rw [h.2.1]
    norm_num
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3 h
  exact M.regularlyVarying_two_of_source_p21 hα hr₀ hβ hac hmR hae h1 h2 hP
    (M.openTriangleSelf_lt_top_of_case3 h) hC₀ (by norm_num) hF hc3 hgm

end SourceModelData
end PercLib.CriticalLRP.Orchestration
