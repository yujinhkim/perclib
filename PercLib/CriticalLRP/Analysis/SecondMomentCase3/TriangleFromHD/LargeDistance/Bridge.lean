/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m1.
Latest independent rebuild at production HEAD `bd25afb1130f7fe93446b447f9a68a4d3aba08cc`; reviewed scratch source `.scratch/review-smwznoz6j/m1/Bridge.lean`.

Swarm `smwznoz6j`, member `m1`, direction `d2` — (G) non-vacuity of the literal Case 3 of (HD).

# The Case-3 convolution chain from the distance-restricted hypothesis `Case3HDLarge`

`TriangleFromHD/Main.lean` derives `hTri`, `hF`, Lemma I.4.3 and the Case-3 consumer of
Proposition I.4.15 from `M.Case3HD`.  The only use of the literal hypothesis in that chain is
`Pointwise.exists_abs_tau_le_Wt`, whose proof uses the printed bound only at `4 < ‖z‖` and uses
`τ ≤ 1` below.  This file re-runs the chain with `M.Case3HD` replaced by `M.Case3HDLarge`
(`Defs.lean`), using `exists_abs_tau_le_Wt_of_case3HDLarge` (`Main.lean`).

Every statement below is the production statement with `Case3HD` replaced by `Case3HDLarge`; the
three other inputs of `secondMoment_asymptotic_case3_of_source_p21` (ODE regularity, first- and
second-moment finiteness/asymptotics, measurability, logarithmic integrability and the moment gap
`hgm`) are retained verbatim.  Nothing here proves `Case3HDLarge`: it is the source's large-distance
(HD)(3) estimate, which in the doubly-marginal model is the lace-expansion input.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Main

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open scoped ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

open PercLib.CriticalLRP CriticalLRPConv

variable (M : SourceModelData)

/-! ## Stage 1 and Stage 2 of (I.4.12), `hTri`, `hF` and the Case-3 consumer from
`Case3HDLarge` -/

theorem exists_tauConv_bound_of_case3HDLarge (h : M.Case3HDLarge) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ (∀ x : M.V, Summable fun y : M.V => M.tau y * M.tau (x - y)) ∧
      ∀ x : M.V, |M.tauConv x| ≤ K₁ * Wt ((M.d : ℝ) - 4) 2 (M.S.ρ (toVec x)) := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  obtain ⟨Cτ, hCτ, hτ⟩ := M.exists_abs_tau_le_Wt_of_case3HDLarge ⟨hd6, hα2, C, hC, hb⟩
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


theorem exists_tauConvConv_bound_of_case3HDLarge (h : M.Case3HDLarge) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ (∀ x : M.V, Summable fun y : M.V => M.tau y * M.tauConv (x - y)) ∧
      ∀ x : M.V, |M.tauConvConv x| ≤ K₂ * Wt 0 2 (M.S.ρ (toVec x)) := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  obtain ⟨Cτ, hCτ, hτ⟩ := M.exists_abs_tau_le_Wt_of_case3HDLarge ⟨hd6, hα2, C, hC, hb⟩
  obtain ⟨K₁, hK₁, -, hb1⟩ := M.exists_tauConv_bound_of_case3HDLarge ⟨hd6, hα2, C, hC, hb⟩
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


theorem openTriangleSelf_lt_top_of_case3HDLarge (h : M.Case3HDLarge) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ := by
  obtain ⟨-, -, hsum1, -⟩ := M.exists_tauConv_bound_of_case3HDLarge h
  obtain ⟨-, -, hsum2, -⟩ := M.exists_tauConvConv_bound_of_case3HDLarge h
  have hinn : ∀ u : M.V, Summable (fun w : M.V => M.tau u * M.tau w * M.tau (0 - u - w)) := by
    intro u
    have h' := (hsum1 ((0 : M.V) - u)).mul_left (M.tau u)
    refine h'.congr fun w => ?_
    ring
  have hbridge := M.openTriangle_eq_ofReal_tauConvConv 0 hinn (hsum2 0)
  change TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 0 < ⊤
  rw [hbridge]
  exact ENNReal.ofReal_lt_top


theorem logRadialBound_openTriangle_of_case3HDLarge (h : M.Case3HDLarge) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ 2 := by
  obtain ⟨K₂, hK₂, hsum2, hb2⟩ := M.exists_tauConvConv_bound_of_case3HDLarge h
  obtain ⟨-, -, hsum1, -⟩ := M.exists_tauConv_bound_of_case3HDLarge h
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


theorem isLogErrorFunction_nablaTail_of_case3HDLarge (h : M.Case3HDLarge) :
    Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal) := by
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3HDLarge h
  exact M.isLogErrorFunction_nablaTail hC₀ (by norm_num) hF


theorem secondMoment_asymptotic_case3_of_case3HDLarge (h : M.Case3HDLarge)
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
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3HDLarge h
  exact M.secondMoment_asymptotic_case3_of_source_p21 hα hr₀ hβ hac hae h1 h2 hP
    (M.openTriangleSelf_lt_top_of_case3HDLarge h) (C₀ := C₀) hC₀ (by norm_num) hF
    hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm


/-! ## The remaining Case-3 source wrappers from `Case3HDLarge` -/

theorem p2ExclError_tendsto_zero_of_case3HDLarge (h : M.Case3HDLarge) {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3HDLarge h
  exact M.p2ExclError_tendsto_zero_of_source_p21 h1 h2 hP
    (M.openTriangleSelf_lt_top_of_case3HDLarge h) hC₀ (by norm_num) hF hc3 hgm


theorem logIntegrable_p2ExclError_of_case3HDLarge (h : M.Case3HDLarge) {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hmeas : Measurable M.p2ExclError)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3HDLarge h
  exact M.logIntegrable_p2ExclError_of_source_p21 h1 h2 hmeas hP
    (M.openTriangleSelf_lt_top_of_case3HDLarge h) hC₀ (by norm_num) hF hc3 hgm


theorem regularlyVarying_two_of_case3HDLarge (h : M.Case3HDLarge) {r₀ : ℝ} (hr₀ : 0 < r₀)
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
  obtain ⟨C₀, hC₀, hF⟩ := M.logRadialBound_openTriangle_of_case3HDLarge h
  exact M.regularlyVarying_two_of_source_p21 hα hr₀ hβ hac hmR hae h1 h2 hP
    (M.openTriangleSelf_lt_top_of_case3HDLarge h) hC₀ (by norm_num) hF hc3 hgm

end SourceModelData
end PercLib.CriticalLRP.Orchestration
