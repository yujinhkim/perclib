/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.LeftExcludedMass.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.AttainedExcludedLeft
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity
public import PercLib.CriticalLRP.Analysis.Cutoff.MixedFluxDensityMonotone

/-!
# The left limit of the excluded mass at a cut-off corner

Swarm `smwv6er9k`, member `m5`, direction B5.

`E1Sign.exclMass M r` is the excluded expectation over the *closed* window `B_r = {ρ ≤ r}`.
At an attained radius (`r ∈ M.attainedRadii = M.cornerRadii`) the window acquires the sphere
`{ρ = r}` as `r` crosses it, so the mass may jump there; the left limit is the *strict*-window
mass `exclMassLt` of `LeftExcludedMass.Defs`.  This module proves, at **every positive radius**
(no sphere condition, no off-corner hypothesis):

* `tendsto_exclScalar_nhdsLT_strict` — `exclScalar r → exclScalarLt r₀` as `r ↑ r₀`, from a
  finite second and third cutoff moment at `r₀`;
* `pairMass_eq_pairMassLt_add_pairSphereMass` — the exact split of the closed pair mass into the
  strict-window mass plus the sphere layer;
* `exclScalar_eq_exclScalarLt_add_jump` — the exact jump formula
  `exclScalar r = exclScalarLt r + (pairSphereMass r).toReal - (sphereMass r).toReal`;
* `exclScalarLt_le_exclScalar` — the jump is nonnegative: the excluded mass can only jump *up*
  at a radius, so the left limit is at most the value;
* `exclScalarLt_eq_exclScalar_of_no_sphere` — off the sphere the new limit is the landed
  two-sided value (`PairMassRegularity.Main.tendsto_exclScalar_nhdsLT`), which is therefore a
  special case;
The scalar left limit and left corner derivative are proved separately in
`LeftExcludedMass.Scalar`.  No statement is made here about the right-hand side at a corner
(that is direction B6).  Finite moments are inputs everywhere; nothing is inferred from `θ = 0`
and no positivity of `betaCrit` is used.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The strict-window excluded integrand and its measurability -/

theorem measurable_exclMarkFunLt (r : ℝ) : Measurable (M.exclMarkFunLt r) := by
  have hmem : ∀ y : M.V, MeasurableSet {u : Sym2 M.V → ℝ |
      y ∈ cluster (atParameter (M.cutProb r) u) (0 : M.V)} := fun y =>
    (measurableSet_cluster_mem (0 : M.V) y).preimage (measurable_atParameter (M.cutProb r))
  have hsum : Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ M.ballFLt r,
        ((cluster (atParameter (M.cutProb r) u) (0 : M.V))ᶜ).indicator
          (fun _ => (1 : ℝ≥0∞)) y * clusterVol (atParameter (M.cutProb r) u) y := by
    refine Finset.measurable_sum _ fun y _ => ?_
    exact (measurable_const.indicator (hmem y).compl).mul
      ((measurable_clusterVol y).comp (measurable_atParameter (M.cutProb r)))
  exact (M.measurable_markVol r).mul hsum

/-! ## 2. The pairwise split in the strict window -/

theorem pairMarkFunLt_eq_conn_add_excl (r : ℝ) (u : Sym2 M.V → ℝ) :
    M.pairMarkFunLt r u = M.connMarkFunLt r u + M.exclMarkFunLt r u := by
  simp only [SourceModelData.pairMarkFunLt, SourceModelData.connMarkFunLt,
    SourceModelData.exclMarkFunLt, SourceModelData.markVol]
  rw [Finset.mul_sum, Finset.mul_sum (s := M.ballFLt r)
      (a := clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2),
    Finset.mul_sum (s := M.ballFLt r), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => E1Sign.summand_split M (atParameter (M.cutProb r) u) y

/-- **`pairMassLt = connMassLt + exclMassLt`**, the strict-window form of
`E1Sign.pairMass_eq`. -/
theorem pairMassLt_eq_connMassLt_add_exclMassLt (r : ℝ) :
    M.pairMassLt r = M.connMassLt r + M.exclMassLt r := by
  rw [SourceModelData.pairMassLt, SourceModelData.connMassLt, SourceModelData.exclMassLt]
  calc ∫⁻ u, M.pairMarkFunLt r u ∂(markMeasure M.V)
      = ∫⁻ u, (M.connMarkFunLt r u + M.exclMarkFunLt r u) ∂(markMeasure M.V) :=
        lintegral_congr fun u => M.pairMarkFunLt_eq_conn_add_excl r u
    _ = _ := lintegral_add_left (M.measurable_connMarkFunLt r) _

/-! ## 3. Finiteness from the second and third cutoff moments -/

theorem pairMassLt_ne_top (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) : M.pairMassLt r ≠ ⊤ :=
  ne_top_of_le_ne_top (E1Sign.pairMass_ne_top M r h2)
  (M.pairMassLt_le_pairMass (r := r))

theorem connMassLt_ne_top (r : ℝ) (h3 : M.cutMoment 3 r ≠ ⊤) : M.connMassLt r ≠ ⊤ :=
  ne_top_of_le_ne_top h3 (M.connMassLt_le_cutMoment_three r)

theorem exclMassLt_le_pairMassLt (r : ℝ) : M.exclMassLt r ≤ M.pairMassLt r := by
  rw [M.pairMassLt_eq_connMassLt_add_exclMassLt r]
  exact le_add_self

theorem exclMassLt_ne_top (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) : M.exclMassLt r ≠ ⊤ :=
  ne_top_of_le_ne_top (M.pairMassLt_ne_top r h2) (M.exclMassLt_le_pairMassLt r)


/-! ## 4. The left limit of the excluded mass at every positive radius -/

/-- **The left limit of the excluded mass at every positive radius.**  At a positive radius `r₀`
with a finite second and third cutoff moment, `exclScalar r` tends to the strict-window value
`exclScalarLt r₀` as `r ↑ r₀`.  No sphere condition is assumed: at an attained radius the closed
window `B_r` shrinks to `{ρ < r₀}`, and the difference is the sphere layer of §5. -/
theorem tendsto_exclScalar_nhdsLT_strict (r0 : ℝ) (hr0 : 0 < r0)
    (h2 : M.cutMoment 2 r0 ≠ ⊤) (h3 : M.cutMoment 3 r0 ≠ ⊤) :
    Tendsto M.exclScalar (𝓝[<] r0) (𝓝 (M.exclScalarLt r0)) := by
  have hpair := M.tendsto_pairMassReal_nhdsLT r0 hr0 (M.pairMassLt_ne_top r0 h2)
  have hconn := M.tendsto_connMassReal_nhdsLT r0 hr0 (M.connMassLt_ne_top r0 h3)
  have hsub := hpair.sub hconn
  have hlim : (M.pairMassLt r0).toReal - (M.connMassLt r0).toReal = M.exclScalarLt r0 := by
    rw [M.pairMassLt_eq_connMassLt_add_exclMassLt r0,
      ENNReal.toReal_add (M.connMassLt_ne_top r0 h3) (M.exclMassLt_ne_top r0 h2)]
    simp only [SourceModelData.exclScalarLt]
    ring
  rw [hlim] at hsub
  refine hsub.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hr0] with r hr
  exact (M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le (le_of_lt hr.2) h2).symm

/-- The same left limit with the moments taken at one strictly larger radius, matching the
interfaces of the landed off-corner theorems. -/
theorem tendsto_exclScalar_nhdsLT_strict_of_le {r0 r1 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤) :
    Tendsto M.exclScalar (𝓝[<] r0) (𝓝 (M.exclScalarLt r0)) :=
  M.tendsto_exclScalar_nhdsLT_strict r0 hr0
    (M.cutMoment_ne_top_of_le hr1.le 2 h2) (M.cutMoment_ne_top_of_le hr1.le 3 h3)

/-- Off the sphere the new left limit is the value: the landed
`PairMassRegularity.Main.tendsto_exclScalar_nhdsLT` is the special case `exclScalarLt = exclScalar`.
Both statements are left limits of the same function at the same filter, so the identification is
uniqueness of limits and not a re-proof of the landed theorem. -/
theorem exclScalarLt_eq_exclScalar_of_no_sphere {r0 : ℝ} (hr0 : 0 < r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    (h2 : M.cutMoment 2 r0 ≠ ⊤) (h3 : M.cutMoment 3 r0 ≠ ⊤) :
    M.exclScalarLt r0 = M.exclScalar r0 :=
  tendsto_nhds_unique (M.tendsto_exclScalar_nhdsLT_strict r0 hr0 h2 h3)
    (M.tendsto_exclScalar_nhdsLT hr0 hsphere h2 h3)

/-! ## 5. The exact sphere layer of the pair mass and the jump of the excluded mass -/

/-- **The closed pair mass is the strict-window pair mass plus the sphere layer.**  This is the
pair-mass analogue of the landed `connMass_eq_connMassLt_add_sphereMass`. -/
theorem pairMass_eq_pairMassLt_add_pairSphereMass (r : ℝ) :
    E1Sign.pairMass M r = M.pairMassLt r + M.pairSphereMass r := by
  rw [SourceModelData.pairMassLt, SourceModelData.pairSphereMass,
    M.pairMass_eq_lintegral_pairMarkFun, ← lintegral_add_left (M.measurable_pairMarkFunLt r)]
  congr 1
  funext u
  simp only [SourceModelData.pairMarkFunLt, SourceModelData.pairMarkFun]
  rw [← mul_add]
  congr 1
  have hbf : M.ballFLt r = (E1Sign.ballF M r).filter (fun y => M.S.ρ (toVec y) < r) := rfl
  rw [hbf]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := E1Sign.ballF M r)
    (p := fun y => M.S.ρ (toVec y) < r)
    (f := fun y => clusterVol (atParameter (M.cutProb r) u) y)
  rw [← hsplit]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr ?_
  intro y hy
  rw [E1Sign.mem_ballF] at hy
  constructor
  · intro h
    exact le_antisymm hy (not_lt.mp h)
  · intro h
    rw [h]
    exact not_lt.mpr le_rfl

theorem pairSphereMass_ne_top (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) : M.pairSphereMass r ≠ ⊤ := by
  have hsum : M.pairMassLt r + M.pairSphereMass r ≠ ⊤ := by
    rw [← M.pairMass_eq_pairMassLt_add_pairSphereMass r]
    exact E1Sign.pairMass_ne_top M r h2
  exact (ENNReal.add_ne_top.mp hsum).2

theorem sphereMass_ne_top (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) : M.sphereMass r ≠ ⊤ := by
  have hsum : M.connMassLt r + M.sphereMass r ≠ ⊤ := by
    rw [← M.connMass_eq_connMassLt_add_sphereMass r]
    exact E1Sign.connMass_ne_top M r h2
  exact (ENNReal.add_ne_top.mp hsum).2

/-- **The exact jump of the excluded mass at a radius.**  The value exceeds the left limit by the
*pair* sphere layer minus the *connected* sphere layer.  The two layers are not the same object:
the pair layer weighs every vertex of the sphere by `|K_y|`, the connected layer only those of the
sphere which lie in the cluster of the origin. -/
theorem exclScalar_eq_exclScalarLt_add_jump (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤)
    (h3 : M.cutMoment 3 r ≠ ⊤) :
    M.exclScalar r = M.exclScalarLt r +
      ((M.pairSphereMass r).toReal - (M.sphereMass r).toReal) := by
  have hpair : (E1Sign.pairMass M r).toReal =
      (M.pairMassLt r).toReal + (M.pairSphereMass r).toReal := by
    rw [M.pairMass_eq_pairMassLt_add_pairSphereMass r,
      ENNReal.toReal_add (M.pairMassLt_ne_top r h2) (M.pairSphereMass_ne_top r h2)]
  have hconn : (E1Sign.connMass M r).toReal =
      (M.connMassLt r).toReal + (M.sphereMass r).toReal := by
    rw [M.connMass_eq_connMassLt_add_sphereMass r,
      ENNReal.toReal_add (M.connMassLt_ne_top r h3) (M.sphereMass_ne_top r h2)]
  have hvalue := M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le (le_refl r) h2
  have hlt : M.exclScalarLt r = (M.pairMassLt r).toReal - (M.connMassLt r).toReal := by
    rw [M.pairMassLt_eq_connMassLt_add_exclMassLt r,
      ENNReal.toReal_add (M.connMassLt_ne_top r h3) (M.exclMassLt_ne_top r h2)]
    simp only [SourceModelData.exclScalarLt]
    ring
  rw [hvalue, hpair, hconn, hlt]
  ring

/-- **The connected sphere layer is at most the pair sphere layer.**  Per mark, a vertex of the
sphere which lies in the cluster of the origin contributes `|K|²` to the connected layer and `|K|²`
to the pair layer; a vertex of the sphere outside the cluster contributes `0` to the connected
layer and something nonnegative to the pair layer. -/
theorem sphereMass_le_pairSphereMass (r : ℝ) : M.sphereMass r ≤ M.pairSphereMass r := by
  rw [SourceModelData.sphereMass, SourceModelData.pairSphereMass]
  refine lintegral_mono fun u => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases h : y ∈ cluster (atParameter (M.cutProb r) u) (0 : M.V)
  · rw [Set.indicator_of_mem h, mul_one, pow_two]
    have hnonneg : 0 ≤ clusterVol (atParameter (M.cutProb r) u) (0 : M.V) := bot_le
    refine mul_le_mul_of_nonneg_left ?_ hnonneg
    rw [SourceModelData.markVol]
    exact le_of_eq (clusterVol_eq_of_connects (mem_cluster_iff.mp h))
  · rw [Set.indicator_of_notMem h, mul_zero]
    exact zero_le

/-- **The excluded mass can only jump up at a radius**: the left limit is at most the value. -/
theorem exclScalarLt_le_exclScalar (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤)
    (h3 : M.cutMoment 3 r ≠ ⊤) : M.exclScalarLt r ≤ M.exclScalar r := by
  have hle := ENNReal.toReal_mono (M.pairSphereMass_ne_top r h2) (M.sphereMass_le_pairSphereMass r)
  rw [M.exclScalar_eq_exclScalarLt_add_jump r h2 h3]
  linarith

end SourceModelData

end PercLib.CriticalLRP.Orchestration
