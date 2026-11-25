module
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.NormalizedAggregate.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusHorizon.Main

/-!
# Left continuity of normalized pivotal mass and singleton flux
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- Left continuity of the full infinite-edge normalized pivotal mass from left continuity of
its fixed-edge event probabilities and a finite first cutoff moment at a larger radius. -/
theorem tendsto_normalizedPivotMass_nhdsLT (y : M.V) (e₀ : ℕ → Sym2 M.V)
    (he₀ : Function.Surjective e₀) {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ M.attainedRadii) (h1 : M.cutMoment 1 R ≠ ⊤) :
    Tendsto (M.normalizedPivotMass y) (𝓝[<] r0) (𝓝 (M.normalizedPivotMass y r0)) := by
  classical
  obtain ⟨ε, hε0, hε⟩ := M.exists_nhds_notMem_attainedRadii hoff
  set δ : ℝ := min (min ε (R - r0)) (r0 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hε0 (sub_pos.mpr hr0R)) (by linarith)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδR : δ ≤ R - r0 := (min_le_left _ _).trans (min_le_right _ _)
  have hδr : δ ≤ r0 / 2 := min_le_right _ _
  have hWindow : Metric.ball r0 δ ∈ 𝓝 r0 := Metric.ball_mem_nhds r0 hδ0
  have hfac : ∀ᶠ r in 𝓝[<] r0, ∀ e : Sym2 M.V,
      M.cutPivotFactor r e = M.cutPivotFactor r0 e := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hWindow] with r hr
    intro e
    have hr' : |r - r0| < δ := by rw [← Real.dist_eq]; exact hr
    have hrε : |r - r0| < ε := lt_of_lt_of_le hr' hδε
    exact M.cutPivotFactor_eq_of_cornerFree hε hrε e
  have hrlt : ∀ᶠ r in 𝓝[<] r0, r < R ∧ 0 < r := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hWindow] with r hr
    have hr' : |r - r0| < δ := by rw [← Real.dist_eq]; exact hr
    have h1' : r0 - δ < r := by
      rw [abs_lt] at hr'
      linarith [hr'.1]
    have h2' : r < r0 + δ := by
      rw [abs_lt] at hr'
      linarith [hr'.2]
    exact ⟨by linarith, by linarith⟩
  have hsumm : Summable (M.pivotMajorant r0 R) := M.summable_pivotMajorant h1
  have hbound : ∀ᶠ r in 𝓝[<] r0, ∀ e : Sym2 M.V,
      ‖M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖
        ≤ M.pivotMajorant r0 R e := by
    filter_upwards [hrlt] with r hr
    intro e
    have hrpos : 0 < r := hr.2
    have hrR : r ≤ R := hr.1.le
    have hpivnonneg : 0 ≤ pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω
    have hnn : 0 ≤ M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e :=
      mul_nonneg (M.cutPivotFactor_nonneg r0 e) hpivnonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
        ≤ M.cutPivotFactor r0 e * M.edgeTouchMass r e :=
          mul_le_mul_of_nonneg_left (M.pivotalFlux_singleton_le_edgeTouchMass y e)
            (M.cutPivotFactor_nonneg r0 e)
      _ ≤ M.cutPivotFactor r0 e * M.edgeTouchMass R e :=
          mul_le_mul_of_nonneg_left (M.edgeTouchMass_mono hrpos (lt_trans hr0 hr0R) hrR e)
            (M.cutPivotFactor_nonneg r0 e)
      _ = M.pivotMajorant r0 R e := rfl
  have htend : Tendsto (fun r => ∑' e : Sym2 M.V, M.cutPivotFactor r0 e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) (𝓝[<] r0)
      (𝓝 (∑' e : Sym2 M.V, M.cutPivotFactor r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := M.pivotMajorant r0 R) hsumm ?_ hbound
    intro e
    by_cases hs : inSupport M r0 e
    · exact (M.tendsto_nhdsLT_real_pivotalFlux_singleton y e e₀ he₀ hr0).const_mul
        (M.cutPivotFactor r0 e)
    · have hzero : M.cutPivotFactor r0 e = 0 := M.cutPivotFactor_eq_zero_of_not_inSupport r0 hs
      simp only [hzero, zero_mul]
      exact tendsto_const_nhds
  refine htend.congr' ?_
  filter_upwards [hfac] with r hr
  rw [normalizedPivotMass]
  exact tsum_congr fun e => by rw [hr e]

/-- Left continuity of singleton flux from finite first moment and derivative regularity. -/
theorem tendsto_sMomentInfFlux_nhdsLT_of_continuousAt_deriv
    (y : M.V) (e₀ : ℕ → Sym2 M.V) (he₀ : Function.Surjective e₀)
    {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ M.attainedRadii) (h1 : M.cutMoment 1 R ≠ ⊤)
    (hK' : ContinuousAt (fun r => deriv M.K r) r0) :
    Tendsto (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv) (𝓝[<] r0)
      (𝓝 (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r0)) := by
  have hnorm := M.tendsto_normalizedPivotMass_nhdsLT y e₀ he₀ hr0 hr0R hoff h1
  have hκ0 : Tendsto (fun r => M.cutKernelFactor r) (𝓝[<] r0)
      (𝓝 (M.cutKernelFactor r0)) :=
    (M.continuousAt_cutKernelFactor_of_continuousAt_deriv hr0 hK').mono_left nhdsWithin_le_nhds
  have hprod := (hκ0.mul hnorm).congr' (Filter.Eventually.of_forall fun r =>
    (M.sMomentInfFlux_eq_kernelFactor_mul_normalizedPivotMass y r).symm)
  rw [← M.sMomentInfFlux_eq_kernelFactor_mul_normalizedPivotMass y r0] at hprod
  exact hprod

/-- A left-continuity variant of the per-vertex flux regularity on a corner-free window. -/
theorem hleftinf_of_continuousAt_deriv
    (M : SourceModelData) (e₀ : ℕ → Sym2 M.V) (he₀ : Function.Surjective e₀)
    {α β : ℝ} (hα0 : 0 < α) (h1β : M.cutMoment 1 β ≠ ⊤)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hK' : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r => deriv M.K r) r) :
    ∀ y : M.V, ∀ r ∈ Set.Ioo α β,
      Tendsto (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) (𝓝[<] r)
        (𝓝 (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r)) := by
  intro y r hr
  exact M.tendsto_sMomentInfFlux_nhdsLT_of_continuousAt_deriv y e₀ he₀
    (hα0.trans hr.1) hr.2 (by rw [M.attainedRadii_eq_cornerRadii]; exact hoff r hr)
    h1β (hK' r hr)

end PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms tendsto_normalizedPivotMass_nhdsLT
#print axioms tendsto_sMomentInfFlux_nhdsLT_of_continuousAt_deriv
#print axioms hleftinf_of_continuousAt_deriv
