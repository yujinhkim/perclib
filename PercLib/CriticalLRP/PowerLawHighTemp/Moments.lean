/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# All natural cluster moments for the paper's raw-lattice kernel `lrKernel d α`

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.3 and §I.1.2: on `ℤ^d` each unordered pair `{x,y}` is
open independently with probability `1 − exp(−β J(x,y))`, where
`J(x,y) = 1(x ≠ y) ‖x − y‖^{−d−α}`.

The committed high-temperature module `IntensityMoments` proves that *every* natural
cluster-volume moment is finite for an `ℝ≥0`-valued intensity profile `J` whose off-diagonal
rows are bounded by `M`, at `β M < 1`.  `PowerLawHighTemp` discharges that row bound for the
power-law profile `‖z‖^{−s}`, `s = d + α > d`, and converts the resulting first moment to
the paper-literal kernel `lrKernel d α` (the `kernelJ` presentation of `CutoffDominated`).

What was still missing is the *corresponding conversion for all powers*: no committed
statement gives `∫⁻ |K_x|^k ≠ ⊤` for the paper's own `lrKernel` at `k ≥ 2`.  This file
closes that interface.  It adds no new probabilistic input: the analytic content is the
committed `power_lintegral_clusterVol_pow_ne_top`, and the only work is the exact
identification of the two laws, i.e. of the `ℝ≥0`-valued intensity profile with the paper's
`ℝ`-valued `lrKernel d α` (`intensityProfile_eq_bernoulliEdgeProb` rewrites the intensity law
into a `bernoulliEdgeProb` of the coerced kernel, and the two Bernoulli edge functions agree
because the kernels do; the shared `lrKernel_nonneg d α` is the proof argument on both sides,
so no proof-irrelevance step is needed, although `longRangeMeasure_proof_irrel` and
`bernoulliEdgeProb_proof_irrel` remain the tools for the routes that need them).  Nothing here
is a statement at `β_c`; the region is the explicit interval `β M < 1`.

## Main results

* `lrKernel_lintegral_clusterVol_pow_ne_top` — every natural cluster moment of the paper's
  law `P_β` for `lrKernel d α` is finite at every vertex, for `β M < 1`
  (`M = ∑_z ‖z‖_∞^{-d-α}`); the committed first-moment statement
  `lrKernel_lintegral_clusterVol_ne_top` is the case `k = 1` (checked below).
* `exists_beta_interval_lrKernel_clusterVol_pow_ne_top` — the same on a genuine positive
  interval `β < (M + 1)⁻¹`; also in the paper's named form `latticeLongRangeMeasure`.
* `modelProfile_cutoff_lintegral_clusterVol_pow_ne_top` and its radius-uniform interval
  form `exists_beta_interval_modelProfile_cutoff_lintegral_clusterVol_pow_ne_top` — every
  natural cluster moment of the **cut-off** law `P_{β,r}` of Definition I.1.5 is finite at
  every root, for every radius `r`, in the same high-temperature region, with an endpoint
  `β₀ = (M + 1)⁻¹` independent of `r`.  The point is that `J_r ≤ J` at the *same* `β`
  (the general lemma `cutoffSymKernel_lintegral_clusterVol_pow_le_uncut`), so no reduced
  parameter and no `r ≥ 1` hypothesis is needed for this domination direction.

## What is *not* claimed

No statement is made at `β_c`, at `β M ≥ 1`, or about the uniform-in-`r` first moment for
`β < β_c` (the paper's central remaining input).  Everything here is the high-temperature
region `β M < 1`, and the cut-off results are high-temperature statements about the
infinite lattice `ℤ^d`, not a finite-volume or finite-support approximation.

Intended production location: `PercLib/CriticalLRP/PowerLawHighTemp/Moments.lean`
(new proof-only module; no new definitions).  Namespace follows the existing
`PercLib.CriticalLRP.PowerLawHighTemp` results, so the new names sit next to
`lrKernel_lintegral_clusterVol_ne_top`, of which the `k = 1` case agrees.

No new definitions, no `sorry`, no `admit`, no `native_decide`, no custom axioms; the axiom
audit at the end of the file reports only `propext`, `choice`, `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.IntensityMoments
public import PercLib.CriticalLRP.MomentMonotonicity.MomentTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

@[expose] public section

noncomputable section

open Classical MeasureTheory Set
open PercLib.Percolation.Bond PercLib.Probability PercLib.CriticalLRP
open PercLib.CriticalLRP.FiniteVolume
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP.PowerLawHighTemp

/-! ## The two presentations of the paper's kernel

`lrKernel d α` is built from the Mathlib sup norm `‖x − y‖`; the high-temperature row-sum
bounds use the natural-valued `linfNorm`.  `coe_norm_eq_linfNorm` (committed) identifies
them, and the following evaluation lemma puts `lrKernel` in the displacement-profile form
`‖y − x‖_∞^{−d−α}` that `power_rowSum_le` and `IntensityMoments` consume. -/

/-- The paper's kernel evaluated on a pair, in displacement-profile form. -/
theorem lrKernel_mk_eq_linfNorm {d : ℕ} {α : ℝ} (x y : Fin d → ℤ) :
    PercLib.CriticalLRP.lrKernel d α s(x, y)
      = (linfNorm (y - x) : ℝ) ^ (-((d : ℝ) + α)) := by
  simp only [PercLib.CriticalLRP.lrKernel, Sym2.lift_mk]
  rw [coe_norm_eq_linfNorm (x - y), show x - y = -(y - x) by abel, linfNorm_neg]

/-- Agreement of the `ℝ≥0`-valued displacement profile with the paper's `ℝ`-valued
`lrKernel`, as functions on unordered pairs. -/
theorem coe_powerProfile_eq_lrKernel {d : ℕ} {α : ℝ}
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ,
      J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-((d : ℝ) + α)))) :
    (fun e => (J e : ℝ)) = PercLib.CriticalLRP.lrKernel d α := by
  funext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [hJ a b, Real.coe_toNNReal _ (powerProfile_nonneg (b - a)),
      lrKernel_mk_eq_linfNorm]

/-! ## Identification of the laws

The moment theorem of `IntensityMoments` is stated for `law (intensityProfile J β)`
(`J : Sym2 V → ℝ≥0`), while the paper's law is `longRangeMeasure (lrKernel d α) …` with an
`ℝ`-valued kernel.  `intensityProfile_eq_bernoulliEdgeProb` rewrites the first into a
`bernoulliEdgeProb` of the coerced kernel; after that the two measures differ only by the
nonnegativity proof argument of `bernoulliEdgeProb`, which `longRangeMeasure_proof_irrel`
removes.  This is the only conversion used below. -/

/-- The intensity law of a `ℝ≥0` power-law profile is the paper's `longRangeMeasure` for
`lrKernel d α`. -/
theorem law_intensityProfile_eq_longRangeMeasure {d : ℕ} {α : ℝ}
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ,
      J s(x, y) = Real.toNNReal ((linfNorm (y - x) : ℝ) ^ (-((d : ℝ) + α))))
    (β : ℝ≥0) :
    law (intensityProfile J β)
      = PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
          (PercLib.CriticalLRP.lrKernel_nonneg d α) β := by
  rw [intensityProfile_eq_bernoulliEdgeProb J β]
  have hfun : (fun e => (J e : ℝ)) = PercLib.CriticalLRP.lrKernel d α :=
    coe_powerProfile_eq_lrKernel hJ
  have hprob : bernoulliEdgeProb (fun e => (J e : ℝ)) (fun e => (J e).coe_nonneg) β
      = bernoulliEdgeProb (PercLib.CriticalLRP.lrKernel d α)
          (PercLib.CriticalLRP.lrKernel_nonneg d α) β := by
    refine funext fun e => Subtype.ext ?_
    rw [bernoulliEdgeProb_coe, bernoulliEdgeProb_coe]
    have key : ((J e : ℝ≥0) : ℝ) = PercLib.CriticalLRP.lrKernel d α e := congrFun hfun e
    rw [key]
  rw [hprob]
  rfl

/-! ## All natural cluster moments of the paper's model

The only probabilistic input is the committed `power_lintegral_clusterVol_pow_ne_top`
(`IntensityMoments`), which is stated for an `ℝ≥0` intensity profile with a row bound `M`.
The row bound for the power-law profile is discharged there from `s > d` via
`power_rowSum_le`; here `s = d + α` with `α > 0`, and the law is converted with
`law_intensityProfile_eq_longRangeMeasure` above. -/

/-- **Every natural cluster-volume moment of the paper's power-law model is finite** at
every lattice vertex, in the explicit high-temperature region `β M < 1` with
`M = ∑_z ‖z‖_∞^{-d-α}`.

This is the `k`-th-moment companion of the committed first-moment statement
`lrKernel_lintegral_clusterVol_ne_top`: the latter is the case `k = 1`.  Nothing is asserted
at or above `β M = 1`, and in particular nothing at `β_c`. -/
theorem lrKernel_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
      (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
        (PercLib.CriticalLRP.lrKernel_nonneg d α) β)) ≠ ⊤ := by
  obtain ⟨J, hJ⟩ := PercLib.Models.exists_sym2_kernel
    (fun z : Fin d → ℤ => Real.toNNReal ((linfNorm z : ℝ) ^ (-((d : ℝ) + α))))
    (fun z => by
      show Real.toNNReal ((linfNorm (-z) : ℝ) ^ (-((d : ℝ) + α)))
        = Real.toNNReal ((linfNorm z : ℝ) ^ (-((d : ℝ) + α)))
      rw [linfNorm_neg])
  have hmom := PercLib.CriticalLRP.Exploration.BFS.power_lintegral_clusterVol_pow_ne_top
    (d := d) hd (s := (d : ℝ) + α) (by linarith) hJ hβ x k
  rwa [law_intensityProfile_eq_longRangeMeasure hJ β] at hmom

/-- The same statement for the paper's named law `latticeLongRangeMeasure d α β`
(`CountableProduct.Critical`), which is `longRangeMeasure (lrKernel d α) …`
by definition. -/
theorem latticeLongRangeMeasure_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
      (PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ≠ ⊤ :=
  lrKernel_lintegral_clusterVol_pow_ne_top hd hα hβ x k

/-- Simultaneous form: all natural moments at a vertex are finite at once. -/
theorem lrKernel_forall_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    ∀ k : ℕ,
      (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
        (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
          (PercLib.CriticalLRP.lrKernel_nonneg d α) β)) ≠ ⊤ :=
  fun k => lrKernel_lintegral_clusterVol_pow_ne_top hd hα hβ x k

/-! ## A nonempty interval of parameters

`β M < 1` holds for every `β < (M + 1)⁻¹`, so the moment-finiteness region is a genuine
interval of positive length (with `β₀ > 0` produced by the theorem, not assumed). -/

/-- Elementary scalar comparison: `β < (M + 1)⁻¹` forces `β M < 1`, in `ℝ`. -/
theorem mul_lt_one_of_lt_inv_add_one {M : ℝ≥0} {β : ℝ≥0} (hβ : β < (M + 1)⁻¹) :
    (β : ℝ) * (M : ℝ) < 1 := by
  rcases eq_or_lt_of_le M.coe_nonneg with h0 | hpos
  · rw [← h0, mul_zero]; norm_num
  · have hβr : (β : ℝ) < ((M : ℝ) + 1)⁻¹ := by
      have h' : (β : ℝ) < (((M + 1)⁻¹ : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.mpr hβ
      rwa [NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one] at h'
    have hstep : (β : ℝ) * (M : ℝ) < ((M : ℝ) + 1)⁻¹ * (M : ℝ) :=
      mul_lt_mul_of_pos_right hβr hpos
    have hlt : ((M : ℝ) + 1)⁻¹ * (M : ℝ) < 1 := by
      rw [inv_mul_eq_div, div_lt_one (by linarith)]
      linarith
    linarith

/-- The same comparison in the `ℝ≥0∞` form used by the moment theorem. -/
theorem mul_coe_lt_one_of_lt_inv_add_one {M : ℝ≥0} {β : ℝ≥0} (hβ : β < (M + 1)⁻¹) :
    (β : ℝ≥0∞) * (M : ℝ≥0∞) < 1 := by
  rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, NNReal.coe_one]
  exact mul_lt_one_of_lt_inv_add_one hβ

/-- **A positive interval of parameters on which every natural cluster moment of the
paper's model is finite.**  The endpoint is `β₀ = (M + 1)⁻¹` with
`M = ∑_z ‖z‖_∞^{-d-α}`; the theorem produces it, so the high-temperature region is not a
single point.  No statement is made at `β₀` or beyond. -/
theorem exists_beta_interval_lrKernel_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (x : Fin d → ℤ) (k : ℕ),
      (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
        (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
          (PercLib.CriticalLRP.lrKernel_nonneg d α) β)) ≠ ⊤ := by
  refine ⟨((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)
    + 1)⁻¹, inv_pos.mpr (by positivity), fun β hβ x k => ?_⟩
  exact lrKernel_lintegral_clusterVol_pow_ne_top hd hα
    (mul_coe_lt_one_of_lt_inv_add_one hβ) x k

/-- The interval form for the paper's named law. -/
theorem exists_beta_interval_latticeLongRangeMeasure_clusterVol_pow_ne_top {d : ℕ}
    (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (x : Fin d → ℤ) (k : ℕ),
      (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
        (PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ≠ ⊤ := by
  obtain ⟨β₀, hpos, hfin⟩ := exists_beta_interval_lrKernel_clusterVol_pow_ne_top hd hα
  exact ⟨β₀, hpos, fun β hβ x k => hfin β hβ x k⟩

theorem power_kernelJ_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
      (PercLib.CriticalLRP.longRangeMeasure
        (PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin d → ℤ => (↑(linfNorm y) : ℝ) ^ (-((d : ℝ) + α)))
          (powerProfile_even ((d : ℝ) + α)))
        power_kernelJ_nonneg β)) ≠ ⊤ := by
  have h := lrKernel_lintegral_clusterVol_pow_ne_top hd hα hβ x k
  rwa [longRangeMeasure_congr
    (PercLib.CriticalLRP.PowerLawHighTemp.lrKernel_eq_power_kernelJ (d := d) (α := α))
    (PercLib.CriticalLRP.lrKernel_nonneg d α) power_kernelJ_nonneg β] at h

/-- The `k`-th moment theorem in the `t ↦ t^{-s}` presentation of `CutoffDominated`, where
the evenness proof is `CutoffLimit.profile_even` rather than `powerProfile_even`. -/
theorem power_uncut_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ k ∂
      (PercLib.CriticalLRP.longRangeMeasure
        (PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin d → ℤ => (↑(linfNorm y) : ℝ) ^ (-((d : ℝ) + α)))
          (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d)
            (fun t : ℝ => t ^ (-((d : ℝ) + α)))))
        (PercLib.CriticalLRP.CutoffLimit.uncutKernel_nonneg
          (K := fun t : ℝ => t ^ (-((d : ℝ) + α)))
          powerProfile_nonnegPos
          (powerProfile_zero (by linarith : (0 : ℝ) < (d : ℝ) + α)) d) γ)) ≠ ⊤ := by
  rw [longRangeMeasure_congr (kernelJ_even_irrel _ _ _) _ _ γ]
  exact power_kernelJ_lintegral_clusterVol_pow_ne_top hd hα hγ o k

/-! ## All natural moments of the cut-off law `P_{β,r}` of Definition I.1.5

The cut-off kernel `J_r = cutoffSymKernel K d r` satisfies `J_r ≤ J` for every radius `r`,
so at the *same* parameter `β` every fixed power of the cluster volume is dominated by its
uncut value at `β` (`lintegral_clusterVol_pow_mono_of_le` plus the per-edge comparison
`cutoffSymKernel_le_uncut`).  No smaller parameter and no `r ≥ 1` hypothesis is needed for
this direction.  Combined with the `k`-th moment theorem above, this gives all natural
cluster moments of the cut-off model, uniformly in the cut-off radius, in the
high-temperature region `β M < 1` — and only there: nothing is claimed at or above
`β M = 1`, and in particular nothing about the uniform-in-`r` first moment at `β < β_c`,
which remains an open input. -/

/-- **All-order cut-off moment domination at equal parameter.**  For any radial profile
`K` that is antitone and nonnegative and vanishes at `0`, and every radius `r`, the `q`-th
cluster moment of the cut-off law is at most the `q`-th cluster moment of the uncut law at
the **same** parameter `β`. -/
theorem cutoffSymKernel_lintegral_clusterVol_pow_le_uncut {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    (r : ℝ) (β : ℝ≥0) (o : Fin d → ℤ) (q : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ q ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.CutoffKernel.cutoffSymKernel K d r)
          (PercLib.CriticalLRP.CutoffLimit.cutoffSymKernel_nonneg' hK d r) β))
      ≤ ∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ q ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
            (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d) K))
          (PercLib.CriticalLRP.CutoffLimit.uncutKernel_nonneg
            (d := d) hKnn hK0) β) :=
  PercLib.CriticalLRP.lintegral_clusterVol_pow_mono_of_le
    (fun e => PercLib.CriticalLRP.CutoffDominated.bernoulliEdgeProb_le_of_mul_le
      (PercLib.CriticalLRP.CutoffLimit.cutoffSymKernel_nonneg' hK d r)
      (PercLib.CriticalLRP.CutoffLimit.uncutKernel_nonneg (d := d) hKnn hK0)
      (mul_le_mul_of_nonneg_left
        (PercLib.CriticalLRP.CutoffLimit.cutoffSymKernel_le_uncut hKnn hK0 r e) β.2))
    o q

/-- **Finiteness transfer at every order, uniform in the cut-off radius**: if the uncut
`q`-th moment is finite at `β`, so is the cut-off `q`-th moment at `β`, for every `r`. -/
theorem cutoffSymKernel_lintegral_clusterVol_pow_ne_top_of_uncut {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {β : ℝ≥0}
    (hfin : ∀ (o : Fin d → ℤ) (q : ℕ),
      (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ q ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.TreeExpansion.kernelJ
            (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
            (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d) K))
          (PercLib.CriticalLRP.CutoffLimit.uncutKernel_nonneg
            (d := d) hKnn hK0) β)) ≠ ⊤)
    (r : ℝ) (o : Fin d → ℤ) (q : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ q ∂
      (PercLib.CriticalLRP.longRangeMeasure
        (PercLib.CriticalLRP.CutoffKernel.cutoffSymKernel K d r)
        (PercLib.CriticalLRP.CutoffLimit.cutoffSymKernel_nonneg' hK d r) β)) ≠ ⊤ :=
  ne_top_of_le_ne_top (hfin o q)
    (cutoffSymKernel_lintegral_clusterVol_pow_le_uncut hK hKnn hK0 r β o q)

/-! ## The paper's own profile `J(r) = r^{-d-α}` -/

/-- The `k`-th moment theorem at the paper's radial profile `modelProfile d α`, in the
`CutoffDominated` presentation (`pdf` evenness, `uncutKernel_nonneg`). -/
theorem modelProfile_uncut_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ k ∂
      (PercLib.CriticalLRP.longRangeMeasure
        (PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
          (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d) (modelProfile d α)))
        (PercLib.CriticalLRP.CutoffLimit.uncutKernel_nonneg (d := d)
          (modelProfile_side_conditions hα).1 (modelProfile_side_conditions hα).2) γ)) ≠ ⊤ := by
  have hfun : PercLib.CriticalLRP.TreeExpansion.kernelJ
        (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
        (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d) (modelProfile d α))
      = PercLib.CriticalLRP.TreeExpansion.kernelJ
          (fun y : Fin d → ℤ => (↑(linfNorm y) : ℝ) ^ (-((d : ℝ) + α)))
          (PercLib.CriticalLRP.CutoffLimit.profile_even (d := d)
            (fun t : ℝ => t ^ (-((d : ℝ) + α)))) := by
    refine kernelJ_congr (funext fun y => ?_) _ _
    show (↑(linfNorm y) : ℝ) ^ (-(d : ℝ) - α) = (↑(linfNorm y) : ℝ) ^ (-((d : ℝ) + α))
    rw [show -(d : ℝ) - α = -((d : ℝ) + α) by ring]
  rw [longRangeMeasure_congr hfun _ _ γ]
  exact power_uncut_lintegral_clusterVol_pow_ne_top hd hα hγ o k

/-- **Every natural cluster moment of the paper's cut-off law `P_{β,r}` is finite**, at every
root and for every cut-off radius `r : ℝ`, throughout the high-temperature region
`β M < 1` with `M = ∑_z ‖z‖_∞^{-d-α}`.  The radius is unrestricted: `J_r ≤ J` at the same
`β` already gives the domination, so no `r ≥ 1` condition is needed for this direction. -/
theorem modelProfile_cutoff_lintegral_clusterVol_pow_ne_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {r : ℝ} {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ k ∂
      (PercLib.CriticalLRP.longRangeMeasure
        (PercLib.CriticalLRP.CutoffKernel.cutoffSymKernel (modelProfile d α) d r)
        (PercLib.CriticalLRP.CutoffLimit.cutoffSymKernel_nonneg'
          (modelProfile_antitoneOn d (by positivity)) d r) β)) ≠ ⊤ :=
  cutoffSymKernel_lintegral_clusterVol_pow_ne_top_of_uncut
    (modelProfile_antitoneOn d (by positivity))
    (modelProfile_side_conditions hα).1 (modelProfile_side_conditions hα).2
    (fun o k => modelProfile_uncut_lintegral_clusterVol_pow_ne_top hd hα hβ o k) r o k

/-- **A positive interval of parameters with finite cut-off moments of every order,
uniformly in the cut-off radius.**  The endpoint `β₀ = (M + 1)⁻¹` does not depend on `r`. -/
theorem exists_beta_interval_modelProfile_cutoff_lintegral_clusterVol_pow_ne_top {d : ℕ}
    (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (r : ℝ) (o : Fin d → ℤ) (k : ℕ),
      (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ k ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.CutoffKernel.cutoffSymKernel (modelProfile d α) d r)
          (PercLib.CriticalLRP.CutoffLimit.cutoffSymKernel_nonneg'
            (modelProfile_antitoneOn d (by positivity)) d r) β)) ≠ ⊤ := by
  refine ⟨((Real.toNNReal (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0)
    + 1)⁻¹, inv_pos.mpr (by positivity), fun β hβ r o k => ?_⟩
  exact modelProfile_cutoff_lintegral_clusterVol_pow_ne_top hd hα
    (mul_coe_lt_one_of_lt_inv_add_one hβ) o k

/-! ## Axiom audit and non-vacuity witnesses -/

#print axioms lrKernel_mk_eq_linfNorm
#print axioms coe_powerProfile_eq_lrKernel
#print axioms law_intensityProfile_eq_longRangeMeasure
#print axioms lrKernel_lintegral_clusterVol_pow_ne_top
#print axioms latticeLongRangeMeasure_lintegral_clusterVol_pow_ne_top
#print axioms lrKernel_forall_lintegral_clusterVol_pow_ne_top
#print axioms mul_lt_one_of_lt_inv_add_one
#print axioms mul_coe_lt_one_of_lt_inv_add_one
#print axioms exists_beta_interval_lrKernel_clusterVol_pow_ne_top
#print axioms exists_beta_interval_latticeLongRangeMeasure_clusterVol_pow_ne_top
#print axioms power_kernelJ_lintegral_clusterVol_pow_ne_top
#print axioms power_uncut_lintegral_clusterVol_pow_ne_top
#print axioms cutoffSymKernel_lintegral_clusterVol_pow_le_uncut
#print axioms cutoffSymKernel_lintegral_clusterVol_pow_ne_top_of_uncut
#print axioms modelProfile_uncut_lintegral_clusterVol_pow_ne_top
#print axioms modelProfile_cutoff_lintegral_clusterVol_pow_ne_top
#print axioms exists_beta_interval_modelProfile_cutoff_lintegral_clusterVol_pow_ne_top

/-- Agreement with the committed first-moment statement: the `k = 1` instance of
`lrKernel_lintegral_clusterVol_pow_ne_top` has *the same type* as
`PowerLawHighTemp.lrKernel_lintegral_clusterVol_ne_top`, so the two cannot disagree. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ∂
      (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
        (PercLib.CriticalLRP.lrKernel_nonneg d α) β)) ≠ ⊤ :=
  by simpa only [pow_one] using lrKernel_lintegral_clusterVol_pow_ne_top hd hα hβ x 1

/-- The committed first-moment theorem of `PowerLawHighTemp`, displayed here as the
`k = 1` case to make the agreement explicit. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (linfNorm z : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ∂
      (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
        (PercLib.CriticalLRP.lrKernel_nonneg d α) β)) ≠ ⊤ :=
  lrKernel_lintegral_clusterVol_ne_top hd hα hβ x

/-- At `β = 0` all moments of `lrKernel d α` are finite for every `d ≥ 1`, `α > 0`, so the
hypothesis `β M < 1` is satisfiable and the `k`-th moment theorem is non-vacuous. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
      (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
        (PercLib.CriticalLRP.lrKernel_nonneg d α) 0)) ≠ ⊤ :=
  lrKernel_lintegral_clusterVol_pow_ne_top (d := d) hd (α := α) hα (β := 0)
    (by rw [ENNReal.coe_zero, zero_mul]; exact zero_lt_one) x k

/-- Non-vacuity at a **positive** parameter: the interval theorem produces a positive
endpoint `β₀` such that every `β < β₀` (in particular a positive one) has all natural
cluster moments finite.  No numerical value of `β₀` is needed for this witness. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (x : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ k : ℕ,
      (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω x ^ k ∂
        (PercLib.CriticalLRP.longRangeMeasure (PercLib.CriticalLRP.lrKernel d α)
          (PercLib.CriticalLRP.lrKernel_nonneg d α) β)) ≠ ⊤ := by
  obtain ⟨β₀, hpos, hfin⟩ := exists_beta_interval_lrKernel_clusterVol_pow_ne_top hd hα
  exact ⟨β₀ / 2, half_pos hpos, fun k => hfin (β₀ / 2) (half_lt_self hpos) x k⟩

/-- Non-vacuity for the cut-off law at a **positive** parameter and an arbitrary radius:
some positive `β` has all natural cut-off moments finite at every root, uniformly in `r`. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (r : ℝ) (o : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ k : ℕ,
      (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω o ^ k ∂
        (PercLib.CriticalLRP.longRangeMeasure
          (PercLib.CriticalLRP.CutoffKernel.cutoffSymKernel (modelProfile d α) d r)
          (PercLib.CriticalLRP.CutoffLimit.cutoffSymKernel_nonneg'
            (modelProfile_antitoneOn d (by positivity)) d r) β)) ≠ ⊤ := by
  obtain ⟨β₀, hpos, hfin⟩ :=
    exists_beta_interval_modelProfile_cutoff_lintegral_clusterVol_pow_ne_top hd hα
  exact ⟨β₀ / 2, half_pos hpos, fun k => hfin (β₀ / 2) (half_lt_self hpos) r o k⟩

end PercLib.CriticalLRP.PowerLawHighTemp
