/-
Critical LRP I: kernel-factor split of the off-corner cutoff flux, and what it implies for the
per-vertex radius continuity `hcontinf`.

Swarm `smwuinbxz`, member `m3`, direction d3.  Self-contained packet: no production writes, no
axioms beyond the three standard ones.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.KernelFactor.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusPivotalWeight

/-!
# Off-corner kernel factor of the singleton flux

The infinite singleton flux of the cluster indicator is

`∑' e, cutEdgeDeriv r e * pivotalFlux (edgeMeasure (cutProb r)) 1{y ∈ K_0} e`,

and `cutEdgeDeriv r e = β_c (-K'(r)) exp (β_c K r) * exp (-(β_c K d_e))` on every activated
non-loop edge `e`, with the second factor *independent of `r`*.  Hence the flux factors as
`cutKernelFactor r * normalizedPivotMass y r`, separating

* `r ↦ cutKernelFactor r = β_c (-K'(r)) exp (β_c K r)`, continuous at `r` **exactly when**
  the kernel derivative `K'` is**, and
* `r ↦ normalizedPivotMass y r`, the only part that involves the infinite-volume law.

Consequences proved here:

* `continuousAt_normalizedPivotMass_iff_continuousAt_cutEdgeDeriv`: off corner, the individual
  edge weights (hence every summand of the flux) are continuous at `r` **iff** `K'` is continuous
  at `r`.  So no summand-wise or dominated-convergence proof of `hcontinf` can avoid an off-corner
  regularity hypothesis on `deriv M.K`, which the model data do not provide.
* `continuousAt_sMomentInfFlux_of_...`: `hcontinf` at `r` follows from continuity of `K'` and of
  the normalized pivotal mass at `r`.
* `continuousAt_deriv_of_continuousAt_sMomentInfFlux`: conversely, if `hcontinf` holds at `r`, the
  normalized pivotal mass is continuous and nonzero there, and `β_c ≠ 0`, then `deriv M.K` **is**
  continuous at `r`.  Thus any proof of `hcontinf` must establish off-corner continuity of the
  kernel derivative, an input absent from the recorded model fields.

The necessity results require the normalized pivotal mass (or its total) to be continuous and
nonzero at the point, in addition to flux continuity and `β_c ≠ 0`; without those hypotheses no
conclusion about `deriv M.K` is asserted here. `hcontinf` and `hGcont` themselves remain open.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The weight factors through the kernel factor -/

/-- **Pointwise factorization of the cutoff edge weight.**  For every radius and every edge the
weight is the kernel factor times the normalized cutoff factor. -/
theorem cutEdgeDeriv_eq_kernelFactor_mul_pivotFactor (r : ℝ) (e : Sym2 M.V) :
    M.cutEdgeDeriv r e = M.cutKernelFactor r * M.cutPivotFactor r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeDeriv_mk, cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy, mul_zero]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      by_cases hd : M.S.dist x y ≤ r
      · rw [ite_eq_left hd, ite_eq_left hd, FiniteVolume.cutoffProfile_of_le hd]
        rw [cutKernelFactor,
          show -((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r))
              = ((M.betaCrit : ℝ) * M.K r) + -((M.betaCrit : ℝ) * M.K (M.S.dist x y)) by ring,
          Real.exp_add]
        ring
      · rw [ite_eq_right hd, ite_eq_right hd, mul_zero]

/-- **Factorization of the infinite singleton flux.**  The whole radius dependence of the kernel
is carried by `cutKernelFactor`; everything else is the normalized pivotal mass. -/
theorem sMomentInfFlux_eq_kernelFactor_mul_normalizedPivotMass (y : M.V) (r : ℝ) :
    sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r
      = M.cutKernelFactor r * M.normalizedPivotMass y r := by
  simp only [sMomentInfFlux, infFluxOf, normalizedPivotMass]
  simp_rw [M.cutEdgeDeriv_eq_kernelFactor_mul_pivotFactor r, mul_assoc]
  rw [tsum_mul_left]

/-! ## 2. The activated edge weight is `-K'` times a nonvanishing continuous factor -/

/-- **Split form of the activated edge weight.**  On an edge of length at most `r`, the weight is
`-K'(r)` times `β_c exp (-(β_c (K d - K r)))`, whose vanishing is exactly `β_c = 0`. -/
theorem cutEdgeDeriv_eq_neg_deriv_mul {x y : M.V} (hxy : x ≠ y) {r : ℝ}
    (hdist : M.S.dist x y ≤ r) :
    M.cutEdgeDeriv r s(x, y) = -(deriv M.K r) * ((M.betaCrit : ℝ) *
      Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))) := by
  rw [M.cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_left hdist,
    FiniteVolume.cutoffProfile_of_le hdist]
  ring

/-- **Continuity of the individual edge weight off the corner set is exactly continuity of the
kernel derivative.**  Off corner every edge is either strictly shorter or strictly longer than
`r0`, so the activation indicator is locally constant and no jump intervenes. -/
theorem continuousAt_cutEdgeDeriv_iff_continuousAt_deriv (hβ : (M.betaCrit : ℝ) ≠ 0)
    {x y : M.V} (hxy : x ≠ y) {r0 : ℝ} (hr0 : 0 < r0) (hdist : M.S.dist x y < r0) :
    ContinuousAt (fun r => M.cutEdgeDeriv r s(x, y)) r0 ↔
      ContinuousAt (fun r => deriv M.K r) r0 := by
  have hKc : ContinuousAt M.K r0 :=
    (M.K_diff.differentiableAt (Ioi_mem_nhds hr0)).continuousAt
  have hcc : ContinuousAt (fun r : ℝ => (M.betaCrit : ℝ) * Real.exp
      (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))) r0 := by
    have h1 : ContinuousAt (fun r : ℝ => M.K (M.S.dist x y) - M.K r) r0 :=
      continuousAt_const.sub hKc
    have h2 : ContinuousAt (fun r : ℝ =>
        -((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r))) r0 := (h1.const_mul _).neg
    exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp h2)
  have hev : ∀ᶠ r in 𝓝 r0, M.cutEdgeDeriv r s(x, y)
      = -(deriv M.K r) * ((M.betaCrit : ℝ) * Real.exp
          (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))) :=
    Filter.Eventually.mono (Ici_mem_nhds hdist)
      fun r hr => M.cutEdgeDeriv_eq_neg_deriv_mul hxy hr
  constructor
  · intro hW
    have hneg : ContinuousAt (fun r => -(deriv M.K r)) r0 := by
      refine (hW.div hcc (mul_ne_zero hβ (Real.exp_ne_zero _))).congr ?_
      filter_upwards [hev] with r hr
      simp only [Pi.div_apply]
      rw [hr]
      exact mul_div_cancel_right₀ _ (mul_ne_zero hβ (Real.exp_ne_zero _))
    simpa only [Pi.neg_def, neg_neg] using hneg.neg
  · intro hK'
    refine (hK'.neg.mul hcc).congr ?_
    exact Filter.Eventually.mono hev fun r hr => hr.symm

/-- **No summand-wise route to `hcontinf` from the recorded model fields.**  If the kernel
derivative is discontinuous at an off-corner radius, then every activated edge weight, and hence
every summand of the infinite singleton flux, is discontinuous there. -/
theorem not_continuousAt_cutEdgeDeriv_of_not_continuousAt_deriv
    (hβ : (M.betaCrit : ℝ) ≠ 0) {x y : M.V} (hxy : x ≠ y) {r0 : ℝ} (hr0 : 0 < r0)
    (hdist : M.S.dist x y < r0) (hK' : ¬ ContinuousAt (fun r => deriv M.K r) r0) :
    ¬ ContinuousAt (fun r => M.cutEdgeDeriv r s(x, y)) r0 :=
  fun h => hK' ((M.continuousAt_cutEdgeDeriv_iff_continuousAt_deriv hβ hxy hr0 hdist).mp h)

/-! ## 3. Continuity of the kernel factor is continuity of the kernel derivative -/

/-- Continuity of `K'` at a positive radius gives continuity of the kernel factor there. -/
theorem continuousAt_cutKernelFactor_of_continuousAt_deriv {r0 : ℝ} (hr0 : 0 < r0)
    (hK' : ContinuousAt (fun r => deriv M.K r) r0) :
    ContinuousAt (fun r => M.cutKernelFactor r) r0 := by
  have hKc : ContinuousAt M.K r0 :=
    (M.K_diff.differentiableAt (Ioi_mem_nhds hr0)).continuousAt
  have hexp : ContinuousAt (fun r : ℝ => Real.exp ((M.betaCrit : ℝ) * M.K r)) r0 :=
    Real.continuous_exp.continuousAt.comp (hKc.const_mul _)
  have hprod : ContinuousAt (fun r : ℝ =>
      -((M.betaCrit : ℝ) * deriv M.K r) * Real.exp ((M.betaCrit : ℝ) * M.K r)) r0 :=
    ((hK'.const_mul _).neg).mul hexp
  refine hprod.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [cutKernelFactor]
  ring

/-- Conversely, for nonvanishing critical parameter the kernel factor is continuous only if the
kernel derivative is. -/
theorem continuousAt_deriv_of_continuousAt_cutKernelFactor (hβ : (M.betaCrit : ℝ) ≠ 0)
    {r0 : ℝ} (hr0 : 0 < r0) (hκ : ContinuousAt (fun r => M.cutKernelFactor r) r0) :
    ContinuousAt (fun r => deriv M.K r) r0 := by
  have hKc : ContinuousAt M.K r0 :=
    (M.K_diff.differentiableAt (Ioi_mem_nhds hr0)).continuousAt
  have hden : ContinuousAt (fun r : ℝ =>
      (M.betaCrit : ℝ) * Real.exp ((M.betaCrit : ℝ) * M.K r)) r0 :=
    continuousAt_const.mul (Real.continuous_exp.continuousAt.comp (hKc.const_mul _))
  have hdiv := hκ.div hden (mul_ne_zero hβ (Real.exp_ne_zero _))
  have hneg : ContinuousAt (fun r => -(deriv M.K r)) r0 := by
    refine hdiv.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.div_apply]
    rw [show M.cutKernelFactor r = -(deriv M.K r) *
        ((M.betaCrit : ℝ) * Real.exp ((M.betaCrit : ℝ) * M.K r)) by
      simp only [cutKernelFactor]; ring]
    exact mul_div_cancel_right₀ _ (mul_ne_zero hβ (Real.exp_ne_zero _))
  simpa only [Pi.neg_def, neg_neg] using hneg.neg

/-- **The kernel factor is continuous at a positive radius exactly when `K'` is.** -/
theorem continuousAt_cutKernelFactor_iff_continuousAt_deriv (hβ : (M.betaCrit : ℝ) ≠ 0)
    {r0 : ℝ} (hr0 : 0 < r0) :
    ContinuousAt (fun r => M.cutKernelFactor r) r0 ↔
      ContinuousAt (fun r => deriv M.K r) r0 :=
  ⟨M.continuousAt_deriv_of_continuousAt_cutKernelFactor hβ hr0,
    M.continuousAt_cutKernelFactor_of_continuousAt_deriv hr0⟩

/-! ## 4. Continuity of the infinite singleton flux at interior radii -/

/-- **Sufficiency: `hcontinf` from kernel and pivotal-mass continuity.**  The flux is the product of
the kernel factor and the normalized pivotal mass, so continuity of the two factors gives
continuity of the flux, with no summability or uniformity hypothesis. -/
theorem continuousAt_sMomentInfFlux_of_continuousAt_deriv {y : M.V} {r0 : ℝ} (hr0 : 0 < r0)
    (hK' : ContinuousAt (fun r => deriv M.K r) r0)
    (hB : ContinuousAt (M.normalizedPivotMass y) r0) :
    ContinuousAt (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv) r0 := by
  refine ((M.continuousAt_cutKernelFactor_of_continuousAt_deriv hr0 hK').mul hB).congr ?_
  exact Filter.Eventually.mono (Ioi_mem_nhds hr0)
    fun r _ => (M.sMomentInfFlux_eq_kernelFactor_mul_normalizedPivotMass y r).symm

/-- **Necessity: `hcontinf` forces off-corner continuity of the kernel derivative.**  If the
infinite singleton flux is continuous at an interior radius where the normalized pivotal mass is
continuous and nonzero, then `K'` is continuous there.  The model fields only give
`DifferentiableOn ℝ K (Ioi 0)`, so this is a genuine extra input for any proof of `hcontinf`. -/
theorem continuousAt_deriv_of_continuousAt_sMomentInfFlux (hβ : (M.betaCrit : ℝ) ≠ 0)
    {y : M.V} {r0 : ℝ} (hr0 : 0 < r0)
    (hB : ContinuousAt (M.normalizedPivotMass y) r0)
    (hBne : M.normalizedPivotMass y r0 ≠ 0)
    (hflux : ContinuousAt (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv) r0) :
    ContinuousAt (fun r => deriv M.K r) r0 := by
  have hprod : ContinuousAt (fun r => M.cutKernelFactor r * M.normalizedPivotMass y r) r0 :=
    hflux.congr (Filter.Eventually.mono (Ioi_mem_nhds hr0)
      fun r _ => M.sMomentInfFlux_eq_kernelFactor_mul_normalizedPivotMass y r)
  have hκ : ContinuousAt (fun r => M.cutKernelFactor r) r0 := by
    refine (hprod.div hB hBne).congr ?_
    filter_upwards [hB.eventually_ne hBne] with r hr
    simp only [Pi.div_apply]
    exact mul_div_cancel_right₀ _ hr
  exact (M.continuousAt_cutKernelFactor_iff_continuousAt_deriv hβ hr0).mp hκ

/-- **`hcontinf` in the exact form consumed by the endpoint wrapper**, from continuity of the
kernel derivative on the window together with continuity of the normalized pivotal mass. -/
theorem hcontinf_of_continuousAt_deriv_of_continuousAt_normalizedPivotMass {α β : ℝ}
    (hα : 0 < α) (hK' : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r => deriv M.K r) r)
    (hB : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt (M.normalizedPivotMass y) r) :
    ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt (sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r :=
  fun y r hr =>
    M.continuousAt_sMomentInfFlux_of_continuousAt_deriv (lt_trans hα hr.1) (hK' r hr)
      (hB y r hr)

/-- **What the recorded per-vertex continuity premise forces on the kernel.**  If `hcontinf` holds
on the window, the normalized pivotal masses are continuous and nonzero there, and `β_c ≠ 0`, then
`deriv M.K` is continuous on the whole window.  A proof of `hcontinf` therefore has to supply
off-corner `C¹` regularity of the kernel; the recorded fields (`DifferentiableOn ℝ K (Ioi 0)`) do
not. -/
theorem continuousAt_deriv_of_hcontinf {α β : ℝ} (hα : 0 < α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hB : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt (M.normalizedPivotMass y) r)
    (hBne : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, M.normalizedPivotMass y r ≠ 0)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt (sMomentInfFlux (0 : M.V)
      ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r) :
    ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r => deriv M.K r) r :=
  fun r hr =>
    M.continuousAt_deriv_of_continuousAt_sMomentInfFlux (y := (0 : M.V)) hβ (lt_trans hα hr.1)
      (hB _ r hr) (hBne _ r hr) (hcontinf _ r hr)

/-! ## 5. Bookkeeping: the normalized pivotal mass is nonnegative, and positive as soon as one
summand is -/

/-- The normalized cutoff factor is nonnegative. -/
theorem cutPivotFactor_nonneg (r : ℝ) (e : Sym2 M.V) : 0 ≤ M.cutPivotFactor r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      by_cases hd : M.S.dist x y ≤ r
      · rw [ite_eq_left hd]
        exact (Real.exp_pos _).le
      · rw [ite_eq_right hd]

/-- The normalized cutoff factor is at most one. -/
theorem cutPivotFactor_le_one (r : ℝ) (e : Sym2 M.V) : M.cutPivotFactor r e ≤ 1 := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      norm_num
    · rw [ite_eq_right hxy]
      by_cases hd : M.S.dist x y ≤ r
      · rw [ite_eq_left hd, Real.exp_le_one_iff]
        have hK : 0 ≤ M.K (M.S.dist x y) := M.K_nonneg _ (M.S.dist_pos hxy)
        have hβ : 0 ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
        nlinarith
      · rw [ite_eq_right hd]
        norm_num

/-- The normalized pivotal mass is nonnegative. -/
theorem normalizedPivotMass_nonneg (y : M.V) (r : ℝ) : 0 ≤ M.normalizedPivotMass y r :=
  tsum_nonneg fun e =>
    mul_nonneg (M.cutPivotFactor_nonneg r e) (by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω)

/-- **A single positive pivotal summand makes the normalized pivotal mass positive**, so the
nonvanishing hypothesis of `continuousAt_deriv_of_continuousAt_sMomentInfFlux` can be discharged
from any one edge with positive normalized pivotal flux. -/
theorem normalizedPivotMass_pos_of_pos_summand {y : M.V} {r : ℝ}
    (hsumm : Summable fun e : Sym2 M.V => M.cutPivotFactor r e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
    {e0 : Sym2 M.V} (hpos : 0 < M.cutPivotFactor r e0 *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e0) :
    0 < M.normalizedPivotMass y r :=
  lt_of_lt_of_le hpos (hsumm.le_tsum e0 fun e _ =>
    mul_nonneg (M.cutPivotFactor_nonneg r e) (by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω))

/-! ## 6. The edge weight really jumps at an attained length -/

/-- **The individual edge weight is discontinuous at its own length.**  With `K'` negative there the
weight is `0` on the left and `β_c (-K') > 0` at the length itself.  This is why the per-vertex
continuity `hcontinf` is only stated off the corner set. -/
theorem not_continuousAt_cutEdgeDeriv_at_dist (hβ : (M.betaCrit : ℝ) ≠ 0) {x y : M.V}
    (hxy : x ≠ y) (hK : deriv M.K (M.S.dist x y) < 0) :
    ¬ ContinuousAt (fun r => M.cutEdgeDeriv r s(x, y)) (M.S.dist x y) := by
  intro hcont
  have hval : M.cutEdgeDeriv (M.S.dist x y) s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist x y))) := M.cutEdgeDeriv_at_dist hxy
  have hne : ((M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist x y)))) ≠ 0 :=
    mul_ne_zero hβ (neg_ne_zero.mpr (ne_of_lt hK))
  have hleft : Tendsto (fun r => M.cutEdgeDeriv r s(x, y)) (𝓝[<] (M.S.dist x y)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (M.cutEdgeDeriv_eq_zero_of_lt_dist hr).symm
  have hright : Tendsto (fun r => M.cutEdgeDeriv r s(x, y)) (𝓝[<] (M.S.dist x y))
      (𝓝 ((M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist x y))))) := by
    have h := hcont.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (M.S.dist x y)))
    rwa [hval] at h
  have huniq : (0 : ℝ) = (M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist x y))) :=
    tendsto_nhds_unique hleft hright
  exact hne huniq.symm

/-! ## 7. The same obstruction for the summed flux `hGcont` -/

/-- **The summed flux factors through the same kernel factor.**  Summing the per-vertex identity
over all vertices pulls the kernel factor out of the `y`-sum with no summability hypothesis. -/
theorem tsum_sMomentInfFlux_eq_kernelFactor_mul (r : ℝ) :
    ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r
      = M.cutKernelFactor r * ∑' y : M.V, M.normalizedPivotMass y r := by
  rw [tsum_congr fun y => M.sMomentInfFlux_eq_kernelFactor_mul_normalizedPivotMass y r,
    tsum_mul_left]

/-- **`hGcont` forces the same kernel regularity.**  If the summed flux is continuous at an interior
radius where the total normalized pivotal mass is continuous and nonzero, then `K'` is continuous
there.  So the kernel derivative is a necessary input for `hGcont` as well, not only for
`hcontinf`. -/
theorem continuousAt_deriv_of_continuousAt_tsum_sMomentInfFlux (hβ : (M.betaCrit : ℝ) ≠ 0)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hS : ContinuousAt (fun r => ∑' y : M.V, M.normalizedPivotMass y r) r0)
    (hSne : (∑' y : M.V, M.normalizedPivotMass y r0) ≠ 0)
    (hG : ContinuousAt (fun r => ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) r0) :
    ContinuousAt (fun r => deriv M.K r) r0 := by
  have hprod : ContinuousAt
      (fun r => M.cutKernelFactor r * ∑' y : M.V, M.normalizedPivotMass y r) r0 :=
    hG.congr (Filter.Eventually.of_forall fun r =>
      M.tsum_sMomentInfFlux_eq_kernelFactor_mul r)
  have hκ : ContinuousAt (fun r => M.cutKernelFactor r) r0 := by
    refine (hprod.div hS hSne).congr ?_
    filter_upwards [hS.eventually_ne hSne] with r hr
    simp only [Pi.div_apply]
    exact mul_div_cancel_right₀ _ hr
  exact (M.continuousAt_cutKernelFactor_iff_continuousAt_deriv hβ hr0).mp hκ

/-- **Sufficiency for `hGcont`.**  Continuity of the kernel derivative and of the total normalized
pivotal mass gives continuity of the summed flux, again with no summability hypothesis. -/
theorem continuousAt_tsum_sMomentInfFlux_of_continuousAt_deriv {r0 : ℝ} (hr0 : 0 < r0)
    (hK' : ContinuousAt (fun r => deriv M.K r) r0)
    (hS : ContinuousAt (fun r => ∑' y : M.V, M.normalizedPivotMass y r) r0) :
    ContinuousAt (fun r => ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) r0 := by
  refine ((M.continuousAt_cutKernelFactor_of_continuousAt_deriv hr0 hK').mul hS).congr ?_
  exact Filter.Eventually.mono (Ioi_mem_nhds hr0) fun r _ =>
    (M.tsum_sMomentInfFlux_eq_kernelFactor_mul r).symm

/-- **Either `K'` is continuous off corner, or the normalized pivotal mass is not.**  In the form
that needs no separate continuity hypothesis on the pivotal mass: if `hcontinf` holds at an interior
radius with nonvanishing normalized pivotal mass, then the kernel derivative is continuous there
unless the pivotal mass itself is discontinuous there. -/
theorem continuousAt_deriv_or_not_continuousAt_normalizedPivotMass
    (hβ : (M.betaCrit : ℝ) ≠ 0) {y : M.V} {r0 : ℝ} (hr0 : 0 < r0)
    (hBne : M.normalizedPivotMass y r0 ≠ 0)
    (hflux : ContinuousAt (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv) r0) :
    ContinuousAt (fun r => deriv M.K r) r0 ∨ ¬ ContinuousAt (M.normalizedPivotMass y) r0 := by
  by_cases hB : ContinuousAt (M.normalizedPivotMass y) r0
  · exact Or.inl (M.continuousAt_deriv_of_continuousAt_sMomentInfFlux hβ hr0 hB hBne hflux)
  · exact Or.inr hB

/-! ## 8. The endpoint wrapper with `hcontinf`/`hGcont` replaced by kernel and pivotal-mass
continuity -/

/-- **The off-corner endpoint derivative without the black-box regularity premises.**  This is
`hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope` with `hcontinf` and `hGcont` derived from
continuity of `deriv M.K` and of the normalized pivotal masses on the window, holding the envelope
data `C`, `hCb`, `hKβ`, the second moment `h2β` and the off-corner hypothesis fixed. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_kernelC1
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 C : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Set.Ioo α β, -(deriv M.K r) ≤ C)
    (hKβ : deriv M.K β < 0)
    (hK' : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r => deriv M.K r) r)
    (hB : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt (M.normalizedPivotMass y) r)
    (hBsum : ∀ r ∈ Set.Ioo α β,
      ContinuousAt (fun r' => ∑' y : M.V, M.normalizedPivotMass y r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope T hTmono hT S hSmono hS hα0 hαr0
    hr0β hoff hKd h2β hC0 hCb hKβ
    (M.hcontinf_of_continuousAt_deriv_of_continuousAt_normalizedPivotMass hα0 hK' hB)
    fun r hr => M.continuousAt_tsum_sMomentInfFlux_of_continuousAt_deriv (hα0.trans hr.1)
      (hK' r hr) (hBsum r hr)


end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms cutEdgeDeriv_eq_kernelFactor_mul_pivotFactor
#print axioms sMomentInfFlux_eq_kernelFactor_mul_normalizedPivotMass
#print axioms cutEdgeDeriv_eq_neg_deriv_mul
#print axioms continuousAt_cutEdgeDeriv_iff_continuousAt_deriv
#print axioms not_continuousAt_cutEdgeDeriv_of_not_continuousAt_deriv
#print axioms continuousAt_cutKernelFactor_of_continuousAt_deriv
#print axioms continuousAt_deriv_of_continuousAt_cutKernelFactor
#print axioms continuousAt_cutKernelFactor_iff_continuousAt_deriv
#print axioms continuousAt_sMomentInfFlux_of_continuousAt_deriv
#print axioms continuousAt_deriv_of_continuousAt_sMomentInfFlux
#print axioms hcontinf_of_continuousAt_deriv_of_continuousAt_normalizedPivotMass
#print axioms continuousAt_deriv_of_hcontinf
#print axioms cutPivotFactor_nonneg
#print axioms cutPivotFactor_le_one
#print axioms normalizedPivotMass_nonneg
#print axioms normalizedPivotMass_pos_of_pos_summand
#print axioms not_continuousAt_cutEdgeDeriv_at_dist
#print axioms tsum_sMomentInfFlux_eq_kernelFactor_mul
#print axioms continuousAt_deriv_of_continuousAt_tsum_sMomentInfFlux
#print axioms continuousAt_deriv_or_not_continuousAt_normalizedPivotMass
#print axioms continuousAt_tsum_sMomentInfFlux_of_continuousAt_deriv
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_kernelC1
