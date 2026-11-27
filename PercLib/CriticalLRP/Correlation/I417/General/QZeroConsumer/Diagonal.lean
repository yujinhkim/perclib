/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m6`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d9`.

# The diagonal `y = 0`: the `χ³ T` sharp profile is unattainable

`SharpProfile M C` (`Defs.lean`) is the single-term profile
`E[|K_0|³ 1(y ∈ K_0)] ≤ C χ³ T(0,y)` that implies the two-term target (`Main.lean`).  At the
basepoint it degenerates: `E[|K_0|³ 1(0 ∈ K_0)] = E|K_0|³` and `T(0,0) = 1`, so it demands
`E|K|³ ≤ C χ³`.  This file proves that this cannot hold with an `r`-independent `C` in the Case-3
regime, so the `χ³ T` profile — and every consumer statement built on it (`Sharp.lean`) — must be
replaced by the two-term source display, whose `T³(0,0) χ⁴` term is allowed to carry the extra
`χ²` (`T³(0,0) ≤ χ²`).

The argument is exact and uses only landed inputs: log-convexity of the cluster moments
(`I420Case3.MomentLogConvex.momR_succ_sq_le` at `j = 1`) and the Case-3 moment gap
`c₃ χ³ ≤ E|K|²`.  It gives `c₃² χ² ≤ C`, i.e. `χ` bounded — the diagonal obstruction.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.MomentLogConvex.Defs
public import PercLib.CriticalLRP.Correlation.ThirdMoment.ArmDecomposition

/-! # The diagonal case of the sharp profile -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

@[expose] public section

namespace PercLib.CriticalLRP.I417QZeroConsumer

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-- **The per-vertex numerator at the basepoint is the third moment**: `0 ∈ K_0` always, so the
indicator in `connCubeVertexMass r 0` is `1`. -/
theorem connCubeVertexMass_zero (r : ℝ) :
    M.connCubeVertexMass r (0 : M.V) = M.cutMoment 3 r := by
  have hind : ∀ ω : Config M.V,
      (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) (0 : M.V) = 1 := by
    intro ω
    exact Set.indicator_of_mem (PercLib.Percolation.Bond.mem_cluster_self ω 0) _
  simp only [SourceModelData.connCubeVertexMass, SourceModelData.cutMoment, hind, mul_one]

/-- The `I420Case1` power moments of the cutoff profile are the model's cutoff moments. -/
theorem powMomentAt_cutProb (r : ℝ) (k : ℕ) :
    PercLib.CriticalLRP.I420Case1.powMomentAt (M.cutProb r) k (0 : M.V) = M.cutMoment k r := by
  simp only [PercLib.CriticalLRP.I420Case1.powMomentAt, SourceModelData.cutMoment,
    M.cutLaw_eq_edgeMeasure]

/-- **Log-convexity of the cutoff cluster moments** in the division-free form
`(E|K|²)² ≤ E|K| · E|K|³`. -/
theorem cutMoment_two_sq_le (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤)
    (h3 : M.cutMoment 3 r ≠ ⊤) :
    (M.cutMoment 2 r).toReal ^ 2
      ≤ (M.cutMoment 1 r).toReal * (M.cutMoment 3 r).toReal := by
  have h := PercLib.CriticalLRP.I420Case3.MomentLogConvex.momR_succ_sq_le
    (π := M.cutProb r) (0 : M.V) (j := 1) le_rfl ?_ ?_ ?_
  · simpa only [PercLib.CriticalLRP.I420Case1.momR, powMomentAt_cutProb, Nat.add_one_sub_one,
      show (1 : ℕ) + 1 = 2 from rfl, show (1 : ℕ) + 2 = 3 from rfl] using h
  · rw [powMomentAt_cutProb]; exact h1
  · change PercLib.CriticalLRP.I420Case1.powMomentAt (M.cutProb r) 2 (0 : M.V) ≠ ⊤
    rw [powMomentAt_cutProb]; exact h2
  · change PercLib.CriticalLRP.I420Case1.powMomentAt (M.cutProb r) 3 (0 : M.V) ≠ ⊤
    rw [powMomentAt_cutProb]; exact h3

/-- **The sharp profile at the basepoint** forces `E|K|³ ≤ C χ³`. -/
theorem sharpProfile_forces_cutMoment_three (C : ℝ) (hsharp : SharpProfile M C)
    (r : ℝ) (hr : 1 ≤ r) (_h3 : M.cutMoment 3 r ≠ ⊤) :
    (M.cutMoment 3 r).toReal ≤ C * chi M r ^ 3 := by
  have h := hsharp r hr (0 : M.V)
  rw [connCubeVertexMass_zero, M.cutTwoPoint_self_eq_one, mul_one] at h
  exact h

/-- **The diagonal no-go.**  In the Case-3 regime (`c₃ χ³ ≤ E|K|²`) the sharp profile forces
`χ² ≤ C / c₃²`: an `r`-independent bound on the susceptibility.  Hence the `χ³ T` profile cannot
hold uniformly in `r` once `χ = E_{β_c,r}|K|` is unbounded; the two-term source display (whose
`ℓ = 3` term carries `T³(0,0) χ⁴`) is the correct form. -/
theorem sharpProfile_diag_no_go (C c3 : ℝ) (hc3 : 0 < c3) (hsharp : SharpProfile M C)
    (r : ℝ) (hr : 1 ≤ r) (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤)
    (h3 : M.cutMoment 3 r ≠ ⊤) (hgm : c3 * chi M r ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    chi M r ^ 2 ≤ C / c3 ^ 2 := by
  have hχ1 : 1 ≤ chi M r := one_le_chi M r (by rwa [M.cutMassAt_zero_eq_cutMoment])
  have hχ0 : 0 < chi M r := lt_of_lt_of_le one_pos hχ1
  have hlog := cutMoment_two_sq_le M r h1 h2 h3
  have hdiag := sharpProfile_forces_cutMoment_three M C hsharp r hr h3
  have hχeq : M.cutMassAt r 0 = M.cutMoment 1 r := M.cutMassAt_zero_eq_cutMoment r
  have hχ : chi M r = (M.cutMoment 1 r).toReal := by simp only [chi, hχeq]
  -- `c₃² χ⁶ ≤ (E|K|²)² ≤ E|K| · E|K|³ ≤ χ · C χ³ = C χ⁴`
  have hchain : c3 ^ 2 * chi M r ^ 6 ≤ C * chi M r ^ 4 := by
    have h1' : c3 * chi M r ^ 3 ≤ (M.cutMoment 2 r).toReal := hgm
    have hmono : (c3 * chi M r ^ 3) ^ 2 ≤ (M.cutMoment 2 r).toReal ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) h1' 2
    have hprod : (M.cutMoment 1 r).toReal * (M.cutMoment 3 r).toReal
        ≤ (M.cutMoment 1 r).toReal * (C * chi M r ^ 3) := by
      exact mul_le_mul_of_nonneg_left hdiag ENNReal.toReal_nonneg
    have hA1χ : (M.cutMoment 1 r).toReal = chi M r := hχ.symm
    calc c3 ^ 2 * chi M r ^ 6 = (c3 * chi M r ^ 3) ^ 2 := by ring
      _ ≤ (M.cutMoment 2 r).toReal ^ 2 := hmono
      _ ≤ (M.cutMoment 1 r).toReal * (M.cutMoment 3 r).toReal := hlog
      _ ≤ (M.cutMoment 1 r).toReal * (C * chi M r ^ 3) := hprod
      _ = C * chi M r ^ 4 := by rw [hA1χ]; ring
  -- divide by `χ⁴ > 0`
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < c3 ^ 2)]
  have hχ4 : 0 < chi M r ^ 4 := by positivity
  nlinarith [hchain, hχ4, pow_pos hχ0 2]

/-! ## The basepoint summand is bounded by the tree-graph third moment

Landed as `TreeExpansion.Native.third_moment_native` for a translation-invariant edge profile:
`E|K_0|³ ≤ 3 (E|K_0|)⁵`.  Instantiating at `π = M.cutProb r` gives the additive diagonal input
`D = 3 χ⁵` of `OffDiag.lean` with no extra hypothesis. -/

/-- `tau` of the cutoff profile is the truncated two-point function. -/
theorem tau_cutProb (r : ℝ) (a b : M.V) :
    PercLib.Percolation.Bond.tau (M.cutProb r) a b = M.cutTwoPointE r a b := rfl

/-- Translation invariance of `tau` at the cutoff profile, in the form the native tree-moment
theorem takes. -/
theorem tau_cutProb_translate (r : ℝ) (a b : M.V) :
    PercLib.Percolation.Bond.tau (M.cutProb r) a b
      = PercLib.Percolation.Bond.tau (M.cutProb r) (0 : M.V) (b - a) := by
  rw [tau_cutProb, tau_cutProb, M.cutTwoPointE_eq_ofReal, M.cutTwoPointE_eq_ofReal,
    M.cutTwoPoint_eq_sub]

/-- **The basepoint summand is at most `3 χ⁵`** — the `ℓ = 0` case of the classical tree-graph
inequality (Hutchcroft's Lemma I.4.16 at `p = 3`), instantiated at the cutoff profile. -/
theorem connCubeVertexMass_zero_le (r : ℝ) :
    M.connCubeVertexMass r (0 : M.V)
      ≤ 3 * (M.cutMassAt r 0) ^ 5 := by
  have h := PercLib.CriticalLRP.TreeExpansion.Native.third_moment_native
    (π := M.cutProb r) (tau_cutProb_translate M r)
  have h3 : ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω (0 : M.V)) ^ 3
      ∂(PercLib.Percolation.Bond.law (M.cutProb r))
      = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 3 ∂(M.cutLaw r) := by
    rw [M.cutLaw_eq_edgeMeasure]
    refine lintegral_congr fun ω => ?_
    rw [PercLib.CriticalLRP.Percolation.cardFun_eq_encard, clusterVol_eq_encard]
  have h1 : ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω (0 : M.V))
      ∂(PercLib.Percolation.Bond.law (M.cutProb r))
      = ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r) := by
    rw [M.cutLaw_eq_edgeMeasure]
    refine lintegral_congr fun ω => ?_
    rw [PercLib.CriticalLRP.Percolation.cardFun_eq_encard, clusterVol_eq_encard]
  have h1' : M.cutMassAt r 0
      = ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω (0 : M.V))
        ∂(PercLib.Percolation.Bond.law (M.cutProb r)) := h1.symm
  rw [connCubeVertexMass_zero, SourceModelData.cutMoment, ← h3, h1']
  exact h

end PercLib.CriticalLRP.I417QZeroConsumer
