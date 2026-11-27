/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Borel measurability of the `p = 2` second-moment derivative weight

Swarm `smwyvlg99`, member `m2`, direction `d2`.

The remaining *measurability* input of the second-moment chain of Proposition I.4.15 is the
hypothesis

`hmR : Measurable M.rhsScalarTwo`

carried by `SourceModelData.regularlyVarying_two`,
`regularlyVarying_two_of_hP_of_ae_deriv`, `regularlyVarying_two_reduced`,
`momOf_two_regularlyVarying` (`Analysis/SecondMomentError/Normalized.lean`), by
`SecondMomentCase1`/`SecondMomentCase3` and by `ModelSecondMomentRV`.  This file **proves** it, from
inputs that are strictly weaker than the previously used ones, and never from continuity at an
attained radius.

## Why the landed radius regularity settles it

`rhsScalarTwo r = coeffRHS r * (p2RHS r).toReal` (`SecondMoment/Defs.lean`), and

* `(p2RHS ·).toReal` is **right continuous at every positive radius** by the landed
  `SourceModelData.tendsto_p2RHS_toReal_nhdsGT`: it needs `0 < r₀`, one strictly larger radius
  `r₁ > r₀` with `M.cutMoment 4 r₁ ≠ ⊤`, and nothing else.  No attained-radius condition is used
  and no two-sided statement at a sphere is asserted: at an attained radius the closed window jumps
  to its closed value, which is exactly the right limit that theorem proves;
* `coeffRHS = β_c (-K')` is **unconditionally Borel measurable** (`measurable_deriv`), since the
  derivative of *any* `ℝ → ℝ` function is measurable.  In particular the coefficient *continuity*
  that the landed pointwise statements take as a hypothesis (`ContinuousAt M.coeffRHS r₀`) is **not**
  needed for measurability;
* for `r ≤ 0` the excluded window is empty (`ballF_empty_of_neg`), and at `r = 0` the ball is the
  origin, whose excluded indicator vanishes because a vertex lies in its own cluster; hence
  `p2RHS r = 0` and `rhsScalarTwo r = 0` on `r ≤ 0`.

The generic engine is `measurable_of_tendsto_nhdsGT`: a real function that is right continuous on a
Borel set `s` and vanishes off `s` is Borel measurable.  It is proved by the dyadic right
approximants of `Defs.lean`, which approach each point *strictly* from the right, so the
`𝓝[>]`-form of right continuity applies verbatim; every approximant composition is measurable for
an *arbitrary* function because it factors through `ℤ`, and the limit is taken with
`measurable_of_tendsto_metrizable`.

Nothing here assumes `hac`, `hae`, any moment smoothness, or any left limit.

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Statistics

/-! # Right-continuity and Borel measurability -/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The generic engine: right continuity plus vanishing off a Borel set -/

/-- **A real function that is right continuous on a Borel set and vanishes off it is measurable.**

The approximants are the dyadic right points `x ↦ dyadicRight n x`, which lie strictly to the right
of `x`; the sequence `n ↦ f (dyadicRight n x)` therefore tends to `f x` by the `𝓝[>]`-hypothesis at
every point of `s`.  Nothing is assumed about `f` off `s` beyond the value `0`. -/
theorem measurable_of_tendsto_nhdsGT {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, Tendsto f (𝓝[>] x) (𝓝 (f x))) (h0 : ∀ x, x ∉ s → f x = 0) :
    Measurable f := by
  classical
  have hconv : ∀ x ∈ s, Tendsto (fun n : ℕ => f (Measurability.dyadicRight n x)) atTop
      (𝓝 (f x)) := fun x hx =>
    (hf x hx).comp (Measurability.tendsto_dyadicRight_nhdsGT x)
  have hmeas : ∀ n : ℕ,
      Measurable fun x : ℝ => if x ∈ s then f (Measurability.dyadicRight n x) else 0 := fun n =>
    Measurable.ite hs (Measurability.measurable_comp_dyadicRight f n) measurable_const
  have hlim : Tendsto
      (fun n : ℕ => fun x : ℝ => if x ∈ s then f (Measurability.dyadicRight n x) else 0)
      atTop (𝓝 fun x : ℝ => if x ∈ s then f x else 0) := by
    rw [tendsto_pi_nhds]
    intro x
    by_cases hx : x ∈ s
    · simpa [hx] using hconv x hx
    · simp [hx]
  have hF : Measurable fun x : ℝ => if x ∈ s then f x else 0 :=
    measurable_of_tendsto_metrizable hmeas hlim
  have hEq : (fun x : ℝ => if x ∈ s then f x else 0) = f := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, h0 x hx]
  rw [hEq] at hF
  exact hF

/-! ## 2. The excluded `p = 2` mass vanishes at nonpositive radius -/

namespace SourceModelData

variable (M : SourceModelData)

/-- At nonpositive radius the lattice ball is contained in the origin. -/
theorem ball_subset_singleton_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    M.ball r ⊆ ({0} : Set M.V) := by
  intro y hy
  have hy' : M.S.ρ (toVec y) ≤ r := hy
  have hzero : M.S.ρ (toVec y) = 0 :=
    le_antisymm (le_trans hy' hr) (BallAverage.rho_nonneg M.S y)
  have hy0 : y = 0 := by
    by_contra hne
    have htoVec : toVec y ≠ 0 := by
      intro h
      apply hne
      funext i
      have hi : ((y i : ℤ) : ℝ) = 0 := by simpa [toVec] using congrFun h i
      exact Int.cast_eq_zero.mp hi
    have hpos := M.S.ρ_pos (toVec y) htoVec
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  rw [Set.mem_singleton_iff]
  exact hy0

/-- Every vertex lies in its own cluster, so the excluded indicator at the origin vanishes. -/
theorem indicator_compl_cluster_zero (ω : Config M.V) :
    ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) (0 : M.V) = 0 := by
  have hmem : (0 : M.V) ∉ (cluster ω (0 : M.V))ᶜ := by
    simp [PercLib.Percolation.Bond.mem_cluster_self]
  rw [Set.indicator_of_notMem hmem]

/-- The quadratic excluded window sum vanishes for `r ≤ 0`. -/
theorem exclSumQuad_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) (ω : Config M.V) :
    M.exclSumQuad r ω = 0 := by
  refine Finset.sum_eq_zero fun y hy => ?_
  have hyball : y ∈ M.ball r := (E1Sign.mem_ballF M).mp hy
  have hy0 : y = 0 := by
    have h := M.ball_subset_singleton_zero_of_nonpos hr hyball
    rwa [Set.mem_singleton_iff] at h
  rw [hy0, M.indicator_compl_cluster_zero ω, zero_mul]

/-- The linear excluded window sum vanishes for `r ≤ 0`. -/
theorem exclSumLin_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) (ω : Config M.V) :
    M.exclSumLin r ω = 0 := by
  refine Finset.sum_eq_zero fun y hy => ?_
  have hyball : y ∈ M.ball r := (E1Sign.mem_ballF M).mp hy
  have hy0 : y = 0 := by
    have h := M.ball_subset_singleton_zero_of_nonpos hr hyball
    rwa [Set.mem_singleton_iff] at h
  rw [hy0, M.indicator_compl_cluster_zero ω, zero_mul]

/-- The `p = 2` excluded right-hand side vanishes for `r ≤ 0`. -/
theorem p2RHS_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) : M.p2RHS r = 0 := by
  simp [SourceModelData.p2RHS, SourceModelData.exclMassQuad, SourceModelData.exclMassSqLin,
    M.exclSumQuad_eq_zero_of_nonpos hr, M.exclSumLin_eq_zero_of_nonpos hr]

/-- The derivative weight vanishes for `r ≤ 0`. -/
theorem rhsScalarTwo_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) : M.rhsScalarTwo r = 0 := by
  simp [SourceModelData.rhsScalarTwo, M.p2RHS_eq_zero_of_nonpos hr]

/-! ## 3. Measurability of the excluded RHS and of the derivative weight -/

/-- **`r ↦ (M.p2RHS r)ᵗᵒᴿᵉᵃˡ` is Borel measurable.**

The only input is the conventional fourth-moment finiteness on a strictly larger radius, exactly
the hypothesis of the landed right-continuity `tendsto_p2RHS_toReal_nhdsGT`.  Values at `r ≤ 0` are
`0` by `p2RHS_eq_zero_of_nonpos`, so nothing is asserted about the cutoff law below radius `0`. -/
theorem measurable_p2RHS_toReal
    (h4 : ∀ x : ℝ, 0 < x → ∃ r1 : ℝ, x < r1 ∧ M.cutMoment 4 r1 ≠ ⊤) :
    Measurable fun r : ℝ => (M.p2RHS r).toReal := by
  refine measurable_of_tendsto_nhdsGT (s := Set.Ioi 0) measurableSet_Ioi ?_ ?_
  · intro x hx
    obtain ⟨r1, hr1, h4r1⟩ := h4 x hx
    exact M.tendsto_p2RHS_toReal_nhdsGT x hx hr1 h4r1
  · intro x hx
    simp only [Set.mem_Ioi, not_lt] at hx
    simp [M.p2RHS_eq_zero_of_nonpos hx]

/-- **`M.coeffRHS` is Borel measurable, with no continuity hypothesis.**  It is
`β_c (-K')` and the derivative of an arbitrary `ℝ → ℝ` function is measurable. -/
theorem measurable_coeffRHS : Measurable M.coeffRHS := by
  have h : M.coeffRHS = fun r : ℝ => (M.betaCrit : ℝ) * (-(deriv M.K r)) := rfl
  rw [h]
  exact measurable_const.mul (measurable_deriv M.K).neg

/-- **The remaining measurability input `hmR` of the second-moment chain, proved.**

`Measurable M.rhsScalarTwo` from fourth-moment finiteness on a strictly larger radius at every
positive radius.  No `hac`, no `hae`, no monotonicity of `rhsScalarTwo`, no continuity of
`M.coeffRHS` and no left limit at an attained radius is used. -/
theorem measurable_rhsScalarTwo
    (h4 : ∀ x : ℝ, 0 < x → ∃ r1 : ℝ, x < r1 ∧ M.cutMoment 4 r1 ≠ ⊤) :
    Measurable M.rhsScalarTwo := by
  have h := M.measurable_coeffRHS.mul (M.measurable_p2RHS_toReal h4)
  have hEq : (M.coeffRHS * fun r : ℝ => (M.p2RHS r).toReal) = M.rhsScalarTwo := by
    funext r
    rw [Pi.mul_apply]
    rfl
  rwa [hEq] at h

/-- The same from the global fourth-moment finiteness `∀ r > 0, M.cutMoment 4 r ≠ ⊤`. -/
theorem measurable_rhsScalarTwo_of_forall
    (h4 : ∀ r : ℝ, 0 < r → M.cutMoment 4 r ≠ ⊤) :
    Measurable M.rhsScalarTwo :=
  M.measurable_rhsScalarTwo fun x hx => ⟨x + 1, by linarith, h4 (x + 1) (by linarith)⟩

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.measurable_of_tendsto_nhdsGT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_eq_zero_of_nonpos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2RHS_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_rhsScalarTwo
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_rhsScalarTwo_of_forall
