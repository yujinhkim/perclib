/-
Scratch deliverable of swarm `smwu2am6k`, member `m1`, direction `d1`.

# Feeding the literal Case 2 profile into the source-model log tail

`Analysis/OpenTriangleLogTail.lean` already proves the *conditional* implication

`pointwise polynomial decay of ∇_{β_c}(0,·) ⟹ ∇_r = sup_{‖y‖ ≥ r} ∇_{β_c}(0,y) is a
logarithmically integrable error function`

at `SourceModelData` (`isLogErrorFunction_nablaTail_of_pow`), but it takes the pointwise decay as a
hypothesis.  This file discharges it from (HD)(2) of the source:

`hHD : ∀ x y, x ≠ y → τ_{β_c}(x,y) ≤ C (‖x-y‖_S)^{-d+2}` with `d > 6` and `C ≥ 1`

(the paper's `P_{β_c}(x↔y) ⪯ ‖x-y‖^{-d+2}` at the model's normalized source norm `S.ρ`).  The
literal open triangle is the uncut `TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 ·`
— not the cutoff `cutTriPoint`, not the BK/Gram interface, and not `TriangleAverage.defect`.

Two norm comparisons are consumed and recorded, both from `CriticalLRPConv`:

* input side, `srcLowerUnit M.S * ‖z‖ ≤ M.S.ρ (toVec z)` (`srcLowerUnit_mul_linfNorm_le`);
* output side, `M.S.ρ (toVec y) ≤ srcUpperConst M.S * ‖y‖` (`srcNorm_le_upper_linfNorm`).

Both constants survive into `HD.srcCase2Const`.  Nothing here bounds a normalized-norm quantity
without them, and nothing here is claimed at `y = 0`.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Literal.Defs
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Literal.Main
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail
public import PercLib.CriticalLRP.Analysis.Polygon.Model

/-! # Literal Case 2: Model

The configured-model Case 2 bound and logarithmically integrable open-triangle tail.
-/

set_option autoImplicit false


set_option linter.hashCommand false

@[expose] public section

open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration CriticalLRPConv Filter

/-- The lower comparison constant is `≥ 1` after the negative power `-(d-2)` (with `d > 2`).
This is the only place the input conversion `S.ρ`-decay → sup-norm decay spends a constant. -/
theorem one_le_srcLowerUnit_rpow (M : SourceModelData) (hd : 2 < M.d) :
    (1 : ℝ) ≤ (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) := by
  have hcl : 0 < srcLowerUnit M.S := srcLowerUnit_pos M.S M.hd
  have h1 : srcLowerUnit M.S ≤ 1 := srcLowerUnit_le_one M.S
  have hdR : (2 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
  have h3 : ((1 : ℝ)) ^ (-((M.d : ℝ) - 2)) ≤ (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos hcl h1 (by linarith)
  simpa using h3

/-- **The HD Case 2 domination, converted from the source norm to the lattice sup-norm.**

`hHD` is stated at `M.S.ρ`; the lattice theorem
`Orchestration.HD.openTriangle_toReal_le_powMajorant` is stated at the sup-norm `‖·‖`.  The
conversion costs exactly the factor `(srcLowerUnit M.S) ^ (-(d-2))`, which is `≥ 1`; no other loss
occurs. -/
theorem HD_to_supNorm (M : SourceModelData) (hd : 6 < M.d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    ∀ z : M.V, z ≠ 0 →
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z
        ≤ ENNReal.ofReal ((C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) *
            ‖z‖ ^ (-(M.d : ℝ) + 2)) := by
  intro z hz
  have hcl : 0 < srcLowerUnit M.S := srcLowerUnit_pos M.S M.hd
  have hdR : (2 : ℝ) < (M.d : ℝ) := by
    exact_mod_cast (show 2 < M.d by omega)
  have hexp : -(M.d : ℝ) + 2 = -((M.d : ℝ) - 2) := by ring
  -- the HD input at the pair `(0, z)`
  have h1 : M.twoPoint M.betaCrit 0 z ≤ C * (M.S.ρ (toVec (0 - z))) ^ (-((M.d : ℝ) - 2)) := by
    simpa only [hexp] using hHD 0 z (Ne.symm hz)
  have hρ : M.S.ρ (toVec (0 - z)) = M.S.ρ (toVec z) := by
    rw [show toVec ((0 : M.V) - z) = -(toVec z) from by funext i; simp [toVec]]
    exact M.S.ρ_neg (toVec z)
  rw [hρ] at h1
  -- the lower norm comparison, in the sup-norm
  have hlow : srcLowerUnit M.S * ‖z‖ ≤ M.S.ρ (toVec z) := by
    have h := srcLowerUnit_mul_linfNorm_le M.S M.hd z
    rwa [← coe_norm_eq_linfNorm z] at h
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hbase : 0 < srcLowerUnit M.S * ‖z‖ := mul_pos hcl hzpos
  have hmono : (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2))
      ≤ (srcLowerUnit M.S * ‖z‖) ^ (-((M.d : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos hbase hlow (by linarith)
  have hsplit : (srcLowerUnit M.S * ‖z‖) ^ (-((M.d : ℝ) - 2))
      = (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) * ‖z‖ ^ (-((M.d : ℝ) - 2)) :=
    Real.mul_rpow hcl.le hzpos.le
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hstep : C * (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2))
      ≤ (C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) * ‖z‖ ^ (-((M.d : ℝ) - 2)) := by
    have h := mul_le_mul_of_nonneg_left hmono hC0
    rwa [hsplit, ← mul_assoc] at h
  have hτ : (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z)
      = ENNReal.ofReal (M.twoPoint M.betaCrit 0 z) := by
    rw [← ENNReal.ofReal_toReal
      (Orchestration.HD.twoPointFunction_ne_top M.kernel M.kernel_nonneg M.betaCrit 0 z)]
    rfl
  rw [hτ, hexp]
  exact ENNReal.ofReal_le_ofReal (h1.trans hstep)

/-- **The Case 2 pointwise bound at the literal uncut open triangle of the configured model**,
in the source norm and in the exact shape consumed by
`isLogErrorFunction_nablaTail_of_pow`. -/
theorem openTriangle_toReal_le_powMajorant_case2 (M : SourceModelData) (hd : 6 < M.d) {C : ℝ}
    (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    ∀ y : M.V, y ≠ 0 →
      (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
        ≤ Analysis.powMajorant (HD.srcCase2Const M.d C M.S) ((M.d : ℝ) - 6) (M.S.dist 0 y) := by
  intro y hy
  have h2 : 2 < M.d := by omega
  have hC' : (1 : ℝ) ≤ C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) := by
    have h := M.one_le_srcLowerUnit_rpow h2
    nlinarith
  have hlat := Orchestration.HD.openTriangle_toReal_le_powMajorant
    (J := M.kernel) (hJ := M.kernel_nonneg) (β := M.betaCrit)
    M.kernel_shift hd (C := C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) hC'
    (M.HD_to_supNorm hd hC hHD) hy
  -- move the sup-norm bound to the source norm
  have hupper : M.S.ρ (toVec y) ≤ srcUpperConst M.S * ‖y‖ := by
    have h := srcNorm_le_upper_linfNorm M.S y
    rwa [← coe_norm_eq_linfNorm y] at h
  have hcup : 0 < srcUpperConst M.S := srcUpperConst_pos M.S
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hyρ : toVec y ≠ 0 := by
    intro h
    refine hy (funext fun i => ?_)
    have hi := congrFun h i
    simp only [toVec, Pi.zero_apply] at hi
    exact_mod_cast hi
  have hρpos : 0 < M.S.ρ (toVec y) := M.S.ρ_pos _ hyρ
  have hmono : (srcUpperConst M.S * ‖y‖) ^ (-((M.d : ℝ) - 6))
      ≤ (M.S.ρ (toVec y)) ^ (-((M.d : ℝ) - 6)) :=
    Real.rpow_le_rpow_of_nonpos hρpos hupper (by
      have : (6 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast Nat.le_of_lt hd
      linarith)
  have hsplit : (srcUpperConst M.S * ‖y‖) ^ (-((M.d : ℝ) - 6))
      = srcUpperConst M.S ^ (-((M.d : ℝ) - 6)) * ‖y‖ ^ (-((M.d : ℝ) - 6)) :=
    Real.mul_rpow hcup.le hypos.le
  have hprod : srcUpperConst M.S ^ ((M.d : ℝ) - 6) *
      srcUpperConst M.S ^ (-((M.d : ℝ) - 6)) = 1 := by
    rw [← Real.rpow_add hcup]
    simp
  have hdist : M.S.dist 0 y = M.S.ρ (toVec y) := by
    rw [SourceNormData.dist,
      show toVec ((0 : M.V) - y) = -(toVec y) from by funext i; simp [toVec]]
    exact M.S.ρ_neg (toVec y)
  have hswap : ‖y‖ ^ (-((M.d : ℝ) - 6))
      ≤ srcUpperConst M.S ^ ((M.d : ℝ) - 6) * (M.S.dist 0 y) ^ (-((M.d : ℝ) - 6)) := by
    rw [hdist]
    calc ‖y‖ ^ (-((M.d : ℝ) - 6))
        = (srcUpperConst M.S ^ ((M.d : ℝ) - 6) *
            srcUpperConst M.S ^ (-((M.d : ℝ) - 6))) *
              ‖y‖ ^ (-((M.d : ℝ) - 6)) := by rw [hprod, one_mul]
      _ = srcUpperConst M.S ^ ((M.d : ℝ) - 6) *
            (srcUpperConst M.S ^ (-((M.d : ℝ) - 6)) *
              ‖y‖ ^ (-((M.d : ℝ) - 6))) := by ring
      _ = srcUpperConst M.S ^ ((M.d : ℝ) - 6) *
            (srcUpperConst M.S * ‖y‖) ^ (-((M.d : ℝ) - 6)) := by rw [hsplit]
      _ ≤ srcUpperConst M.S ^ ((M.d : ℝ) - 6) *
            (M.S.ρ (toVec y)) ^ (-((M.d : ℝ) - 6)) :=
          mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hcup.le _)
  have hK : 0 ≤ HD.case2Const M.d (C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) :=
    Orchestration.HD.case2Const_nonneg hd hC'
  calc (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
      ≤ Analysis.powMajorant
          (HD.case2Const M.d (C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))))
          ((M.d : ℝ) - 6) ‖y‖ := hlat
    _ = HD.case2Const M.d (C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) *
          ‖y‖ ^ (-((M.d : ℝ) - 6)) := rfl
    _ ≤ HD.case2Const M.d (C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) *
          (srcUpperConst M.S ^ ((M.d : ℝ) - 6) *
            (M.S.dist 0 y) ^ (-((M.d : ℝ) - 6))) :=
        mul_le_mul_of_nonneg_left hswap hK
    _ = Analysis.powMajorant (HD.srcCase2Const M.d C M.S) ((M.d : ℝ) - 6) (M.S.dist 0 y) := by
        rw [HD.srcCase2Const, Analysis.powMajorant]
        ring

/-- **The explicit source-norm tail bound** `∇_r ⪯ r ^ (-(d-6))` at `M.nablaTail`, for `r > 0`.

This is the Case 2 bound (I.4.11) at the source tail `∇_r = sup_{‖y‖_S ≥ r} ∇_{β_c}(0,y)`, with the
NormShell constants of `srcCase2Const` and no statement at `r ≤ 0`. -/
theorem nablaTail_le_powMajorant_case2 (M : SourceModelData) (hd : 6 < M.d) {C : ℝ}
    (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    {r : ℝ} (hr : 0 < r) :
    M.nablaTail r
      ≤ ENNReal.ofReal (Analysis.powMajorant (HD.srcCase2Const M.d C M.S) ((M.d : ℝ) - 6) r) := by
  have h2 : 2 < M.d := by omega
  have hC' : (1 : ℝ) ≤ C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) := by
    have h := M.one_le_srcLowerUnit_rpow h2
    nlinarith
  have hbound := M.openTriangle_toReal_le_powMajorant_case2 hd hC hHD
  have hpow : Analysis.PowRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
      (HD.srcCase2Const M.d C M.S) ((M.d : ℝ) - 6) := by
    intro y hy
    dsimp only at hy ⊢
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [sdist_zero_zero] at hy
      exact lt_irrefl 0 hy
    rw [← ENNReal.ofReal_toReal
      (Orchestration.HD.openTriangle_ne_top M.kernel_shift hd hC'
        (M.HD_to_supNorm hd hC hHD) y)]
    exact ENNReal.ofReal_le_ofReal (hbound y hy0)
  have hexp : (0 : ℝ) ≤ (M.d : ℝ) - 6 := by
    have : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
    linarith
  have hmain := Analysis.radialTailSup_le_powMajorant
    (nrm := fun y : M.V => M.S.dist 0 y)
    (F := fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
    (by
      have hc1 : 0 ≤ HD.case2Const M.d (C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) :=
        Orchestration.HD.case2Const_nonneg hd hC'
      have hc2 : 0 ≤ srcUpperConst M.S ^ ((M.d : ℝ) - 6) :=
        Real.rpow_nonneg (srcUpperConst_pos M.S).le _
      rw [HD.srcCase2Const]
      exact mul_nonneg hc1 hc2) hexp hr hpow
  simpa only [nablaTail_eq_radialTailSup] using hmain

/-- **`∇_r → 0` in `ℝ≥0∞`** under (HD)(2), read off from the uniform pointwise decay.

This is the tail's vanishing, i.e. the statement the paper records as `∇_r → 0`.  It is *not*
Kozma's operator argument and it is *not* the triangle condition as an operator statement: it is
obtained from `nablaTail_le_powMajorant_case2` and `r ^ (-(d-6)) → 0`, exactly as the committed
`tendsto_nablaTail_zero` obtains the Case 3 analogue from a logarithmic pointwise bound. -/
theorem tendsto_nablaTail_zero_of_HD_case2 (M : SourceModelData) (hd : 6 < M.d) {C : ℝ}
    (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    Tendsto (fun r => M.nablaTail r) atTop (𝓝 0) := by
  have ha : (0 : ℝ) < (M.d : ℝ) - 6 := by
    have : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
    linarith
  have hof : Tendsto (fun r : ℝ => ENNReal.ofReal
      (Analysis.powMajorant (HD.srcCase2Const M.d C M.S) ((M.d : ℝ) - 6) r)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (Analysis.tendsto_powMajorant_zero (C := HD.srcCase2Const M.d C M.S) ha)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof
    (Eventually.of_forall fun r => zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  exact M.nablaTail_le_powMajorant_case2 hd hC hHD (by linarith)

/-- **Lemma I.4.3, Case 2, at the configured model**, with the pointwise profile discharged from
(HD)(2).

Under `d > 6` and `τ_{β_c}(x,y) ⪯ ‖x-y‖^{-d+2}` at nonzero differences, the source open-triangle
tail is a *logarithmically integrable error function*:
`∫^∞ ∇_r dr / r < ∞` and `∇_r → 0`, where `∇_r = M.nablaTail r` and `∇_{β_c}(0,y)` inside it is the
literal uncut `TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y`.

The two inputs of the landed conditional theorem are produced here:
`openTriangle_toReal_le_powMajorant_case2` (pointwise decay) and
`Orchestration.HD.openTriangle_ne_top` (finiteness, so that no `⊤` is read as `0`). -/
theorem isLogErrorFunction_nablaTail_of_HD_case2 (M : SourceModelData) (hd : 6 < M.d) {C : ℝ}
    (hC : 1 ≤ C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  have h2 : 2 < M.d := by omega
  have hC' : (1 : ℝ) ≤ C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2)) := by
    have h := M.one_le_srcLowerUnit_rpow h2
    nlinarith
  have hK : 0 ≤ HD.srcCase2Const M.d C M.S := by
    have hc1 : 0 ≤ HD.case2Const M.d (C * (srcLowerUnit M.S) ^ (-((M.d : ℝ) - 2))) :=
      Orchestration.HD.case2Const_nonneg hd hC'
    have hc2 : 0 ≤ srcUpperConst M.S ^ ((M.d : ℝ) - 6) :=
      Real.rpow_nonneg (srcUpperConst_pos M.S).le _
    rw [HD.srcCase2Const]
    exact mul_nonneg hc1 hc2
  have hfin : ∀ y : M.V, y ≠ 0 →
      TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤ :=
    fun y _ => Orchestration.HD.openTriangle_ne_top M.kernel_shift hd hC'
      (M.HD_to_supNorm hd hC hHD) y
  refine M.isLogErrorFunction_nablaTail_of_pow (C := HD.srcCase2Const M.d C M.S)
    (a := (M.d : ℝ) - 6) hK ?_ ?_ hfin
  · have : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
    linarith
  · exact M.openTriangle_toReal_le_powMajorant_case2 hd hC hHD

/-- **Lemma I.4.3, Case 2, at the configured model, in the literal shape of `HD M`'s second
disjunct.**

`Orchestration.HD M` is

`(3α < d) ∨ (6 < d ∧ ∃ C, 0 < C ∧ ∀ x y, x ≠ y → τ_{β_c}(x,y) ≤ C (S.ρ (x-y))^{-d+2}) ∨
  (d = 6 ∧ ...)`.

The hypothesis below is *verbatim* that second disjunct (`0 < C`, not `1 ≤ C`).  The only change is
the bookkeeping constant: `C` is replaced by `max 1 C`, which is the `C ≥ 1` that
`abs_le_conv_wt_of_case2` needs in order to cover the excluded origin.  No hypothesis is added and
no constant is silently dropped. -/
theorem isLogErrorFunction_nablaTail_of_HD_second_disjunct (M : SourceModelData)
    (h : 6 < M.d ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  obtain ⟨hd, C, hC, hHD⟩ := h
  refine M.isLogErrorFunction_nablaTail_of_HD_case2 hd (C := max 1 C) (le_max_left _ _) ?_
  intro x y hxy
  refine (hHD x y hxy).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C) ?_)
  exact Real.rpow_nonneg (src_nonneg M.S _) _

end PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.one_le_srcLowerUnit_rpow
#print axioms SourceModelData.HD_to_supNorm
#print axioms SourceModelData.openTriangle_toReal_le_powMajorant_case2
#print axioms SourceModelData.nablaTail_le_powMajorant_case2
#print axioms SourceModelData.isLogErrorFunction_nablaTail_of_HD_case2
#print axioms SourceModelData.tendsto_nablaTail_zero_of_HD_case2
#print axioms SourceModelData.isLogErrorFunction_nablaTail_of_HD_second_disjunct
