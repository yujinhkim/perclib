/-
Integrated and independently rebuilt from accepted Ultramath `smwyspk27`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The source second-moment covariance estimate (I.4.16) at the actual radial cutoff model

Hutchcroft, *Critical long-range percolation I*, Lemma I.2.1(i) at `x = 0`, `y`, with the
increasing functionals `F = |K_0|` and `G = |K_y|²` gives, at the normalized source law
`M.cutLaw r` (`= edgeMeasure (M.cutProb r)`, with `M.cutProb r e < 1` for every edge),

  `E[ |K_0| |K_y|² 1(0 ↮ y) ] ≤ (E|K_0|) (E|K_y|²)`,

and `E|K_y|² = E|K_0|²` by the vertex reflection `x ↦ y - x` preserving `cutLaw r`.  Summing over
the finite window `B_r = E1Sign.ballF M r` yields the `p = 2` excluded-window comparison

  `M.exclMassQuad r ≤ |B_r| (M.cutMoment 1 r) (M.cutMoment 2 r)`.

This is *not* a bound on `quadPairMass`: the connected part `y ∈ K_0` is the third-moment term
`connCubeMass`, and the covariance estimate is two-sided with it retained
(`prodFactor ≤ exclMassQuad + connCubeMass` below).  No truncation of infinite cluster values is
needed: everything is stated in `ℝ≥0∞` and the two-cluster inequality is the `ℝ≥0∞` cardFun form
(`I420Case1.hrest_pow_le`), whose continuity hypotheses are discharged inside the library.

No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.ExclusionSwap.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect
public import PercLib.Percolation.Bond.ProfileRegularity

/-! # Finite-window and connected-term covariance at the actual cutoff law -/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

open PercLib.CriticalLRP.I420Case1

variable (M : SourceModelData)

/-! ## 1.  An increasing exhaustive sequence of finite edge sets -/

/-- A monotone exhaustion of the edge set of `M.V` by finite sets.  Only existence is used; it
discharges the continuity-from-below hypotheses of the two-cluster inequality. -/
theorem exists_edge_exhaustion :
    ∃ 𝓔 : ℕ → Finset (Sym2 M.V), Monotone 𝓔 ∧ ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n :=
  PercLib.Percolation.Bond.exists_finset_exhaustion

/-! ## 2.  `exclMassQuad` is the mixed excluded mass `E[|K_0| ∑_{y∈B_r} 1(y∉K_0)|K_y|²]` -/

/-- The `p = 2` excluded quadratic window mass is the `a = 1`, `b = 2` mixed excluded mass of the
Case-1 machinery at the cutoff law. -/
theorem exclMassQuad_eq_mixedExcl_window (r : ℝ) :
    M.exclMassQuad r = mixedExcl (M.cutProb r) (0 : M.V) 1 2 (E1Sign.ballF M r) := by
  simp only [SourceModelData.exclMassQuad, SourceModelData.exclSumQuad, mixedExcl,
    E1Sign.cutLaw_eq, pow_one]

/-- The window sum form: `exclMassQuad` is the sum over the finite window of the disconnected
`|K_0| |K_y|²` expectations. -/
theorem exclMassQuad_eq_sum_conn (r : ℝ) :
    M.exclMassQuad r =
      ∑ y ∈ E1Sign.ballF M r,
        ∫⁻ ω, {ω' : Config M.V | ¬ Connects ω' (0 : M.V) y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω * (clusterVol ω (0 : M.V) * clusterVol ω y ^ 2)
          ∂(M.cutLaw r) := by
  rw [M.exclMassQuad_eq_mixedExcl_window r, mixedExcl_eq_sum_lintegral]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine lintegral_congr fun ω => ?_
  exact congrArg (fun t => {ω' : Config M.V | ¬ Connects ω' (0 : M.V) y}.indicator
    (fun _ => (1 : ℝ≥0∞)) ω * (t * clusterVol ω y ^ 2)) (pow_one (clusterVol ω (0 : M.V)))

/-! ## 3.  The second cutoff moment is independent of the vertex

The reflection `x ↦ y - x` preserves `M.cutLaw r` and exchanges the clusters of `0` and `y`, so
`E|K_y|^k = E|K_0|^k` for every `k`.  We only need `k = 2` and (at the origin) `k = 1`. -/

theorem lintegral_clusterVol_pow_eq_zero (r : ℝ) (k : ℕ) (y : M.V) :
    ∫⁻ ω, clusterVol ω y ^ k ∂(M.cutLaw r)
      = ∫⁻ ω, clusterVol ω (0 : M.V) ^ k ∂(M.cutLaw r) := by
  rw [M.lintegral_reflEquiv r y ((measurable_clusterVol y).pow_const k)]
  refine lintegral_congr fun ω => ?_
  have hb : clusterVol (Hvol.permConfig (M.reflEquiv y) ω) y = clusterVol ω (0 : M.V) := by
    simpa only [M.reflEquiv_zero y] using M.clusterVol_reflEquiv y ω (0 : M.V)
  rw [hb]

theorem powMomentAt_one_zero (r : ℝ) :
    powMomentAt (M.cutProb r) 1 (0 : M.V) = M.cutMoment 1 r := by
  rw [powMomentAt, SourceModelData.cutMoment, E1Sign.cutLaw_eq]

theorem powMomentAt_two (r : ℝ) (y : M.V) :
    powMomentAt (M.cutProb r) 2 y = M.cutMoment 2 r := by
  rw [powMomentAt, SourceModelData.cutMoment]
  exact M.lintegral_clusterVol_pow_eq_zero r 2 y

/-! ## 4.  The two-cluster covariance estimate, site by site -/

/-- **Lemma I.2.1(i) for `|K_0|` and `|K_y|²` at the actual cutoff law.**
`E[1(0 ↮ y)|K_0||K_y|²] ≤ (E|K_0|) (E|K_0|²)`. -/
theorem conn_excl_covariance (r : ℝ) (y : M.V) :
    ∫⁻ ω, {ω' : Config M.V | ¬ Connects ω' (0 : M.V) y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω (0 : M.V) * clusterVol ω y ^ 2) ∂(M.cutLaw r)
      ≤ M.cutMoment 1 r * M.cutMoment 2 r := by
  obtain ⟨𝓔, hmono, hcov⟩ := M.exists_edge_exhaustion
  have h := hrest_pow_le (π := M.cutProb r) (E1Sign.cutProb_lt_one M r) 𝓔 hmono hcov
    (0 : M.V) y 1 2
  rw [powMomentAt_one_zero, powMomentAt_two] at h
  refine le_trans ?_ h
  refine lintegral_mono fun ω => ?_
  exact le_of_eq (by rw [pow_one])

/-! ## 5.  The window bound `exclMassQuad r ≤ |B_r| (M.cutMoment 1 r) (M.cutMoment 2 r)` -/

/-- **The excluded quadratic window sum over an arbitrary finite window.**  For every
`B : Finset M.V`,

`E[|K_0| ∑_{y∈B} 1(y∉K_0)|K_y|²] ≤ #B · (E|K_0|) (E|K_0|²)`,

the `p = 2` companion of `E1Sign.exclMass_le`. -/
theorem exclWindow_le_card_mul (r : ℝ) (B : Finset M.V) :
    ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ B,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2
      ∂(M.cutLaw r)
    ≤ (B.card : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) := by
  obtain ⟨𝓔, hmono, hcov⟩ := M.exists_edge_exhaustion
  have hm : (∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ B,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2
      ∂(M.cutLaw r))
      = mixedExcl (M.cutProb r) (0 : M.V) 1 2 B := by
    simp only [mixedExcl, E1Sign.cutLaw_eq, pow_one]
  have h := mixedExcl_le_prodFactor (π := M.cutProb r) (E1Sign.cutProb_lt_one M r) 𝓔 hmono hcov
    (0 : M.V) 1 2 B
  rw [hm]
  refine le_trans h (le_of_eq ?_)
  rw [prodFactor, Finset.sum_congr rfl (fun y _ => by
        rw [M.powMomentAt_one_zero r, M.powMomentAt_two r y]),
    Finset.sum_const, nsmul_eq_mul]

theorem exclMassQuad_le_ncard_mul (r : ℝ) :
    M.exclMassQuad r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) := by
  have hfun : M.exclMassQuad r
      = ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2
        ∂(M.cutLaw r) := by
    simp only [SourceModelData.exclMassQuad, SourceModelData.exclSumQuad]
  rw [hfun, ← E1Sign.card_ballF M r]
  exact M.exclWindow_le_card_mul r (E1Sign.ballF M r)

/-- The same bound in the source's left-associated form. -/
theorem exclMassQuad_le_ncard_mul' (r : ℝ) :
    M.exclMassQuad r ≤ ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r := by
  rw [mul_assoc]
  exact M.exclMassQuad_le_ncard_mul r

/-- The strict-window (`rho < r`) companion, on the finite set `M.ballFLt r`. -/
theorem exclMassQuadLt_le (r : ℝ) :
    M.exclMassQuadLt r ≤ (M.ballFLt r).card * (M.cutMoment 1 r * M.cutMoment 2 r) := by
  have hfun : M.exclMassQuadLt r
      = ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ M.ballFLt r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2
        ∂(M.cutLaw r) := by
    simp only [SourceModelData.exclMassQuadLt, SourceModelData.exclSumQuadLt]
  rw [hfun]
  exact M.exclWindow_le_card_mul r (M.ballFLt r)

/-- The shell (`rho = r`) companion, on the finite set `M.shellF r`. -/
theorem exclMassQuadShell_le (r : ℝ) :
    M.exclMassQuadShell r ≤ (M.shellF r).card * (M.cutMoment 1 r * M.cutMoment 2 r) := by
  have hfun : M.exclMassQuadShell r
      = ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ M.shellF r,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ 2
        ∂(M.cutLaw r) := by
    simp only [SourceModelData.exclMassQuadShell, SourceModelData.exclSumQuadShell]
  rw [hfun]
  exact M.exclWindow_le_card_mul r (M.shellF r)

/-- Since `exclMassQuad r = exclMassSqLin r` (`ExclusionSwap.Main`), the linear excluded window
sum obeys the same bound. -/
theorem exclMassSqLin_le_ncard_mul (r : ℝ) :
    M.exclMassSqLin r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) := by
  rw [← M.exclMassQuad_eq_exclMassSqLin r]
  exact M.exclMassQuad_le_ncard_mul r

/-- **The `p = 2` derivative right-hand side of (I.4.14)** is `3` times the excluded quadratic
window mass, hence obeys the covariance bound with the factor `3`. -/
theorem p2RHS_le (r : ℝ) :
    M.p2RHS r ≤ 3 * (((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r)) := by
  rw [M.p2RHS_eq_three_mul_exclMassQuad r]
  gcongr
  exact M.exclMassQuad_le_ncard_mul r

/-- **The same window bound assembled directly from the per-site covariance estimate.**  This is
the explicit "sum over `y` in the finite window of the disconnected `|K_0| |K_y|²` expectations"
form of the target: each summand is at most `M.cutMoment 1 r * M.cutMoment 2 r` by
`conn_excl_covariance`, and the window has `(M.ball r).ncard` elements. -/
theorem exclMassQuad_le_ncard_mul_via_sum (r : ℝ) :
    M.exclMassQuad r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) := by
  rw [M.exclMassQuad_eq_sum_conn r]
  calc ∑ y ∈ E1Sign.ballF M r,
        ∫⁻ ω, {ω' : Config M.V | ¬ Connects ω' (0 : M.V) y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω * (clusterVol ω (0 : M.V) * clusterVol ω y ^ 2)
          ∂(M.cutLaw r)
      ≤ ∑ _y ∈ E1Sign.ballF M r, (M.cutMoment 1 r * M.cutMoment 2 r) :=
        Finset.sum_le_sum fun y _ => M.conn_excl_covariance r y
    _ = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) := by
        rw [Finset.sum_const, E1Sign.card_ballF M r, nsmul_eq_mul]

/-! ## 6.  The lower covariance inequality, with the connected third moment retained

The Harris–FKG half of Lemma I.2.1 (`prodFactor_le_mixedExcl_add_window`) gives
`|B_r| (E|K|)(E|K|²) ≤ exclMassQuad r + E[|K_0|³ #(K_0 ∩ B_r)]`; the last term is exactly
`connCubeMass r = E[|K_0|³ #(K_0 ∩ B_r)]` (`quadPairMass = connCubeMass + exclMassQuad`). -/

/-- The mixed cluster-window moment `E[|K_0|³ #(K_0 ∩ B_r)]` at the cutoff law is
`connCubeMass`. -/
theorem windowMoment_three_eq_connCubeMass (r : ℝ) :
    I420Case1.windowMoment (M.cutProb r) (0 : M.V) 3 (E1Sign.ballF M r) = M.connCubeMass r := by
  simp only [I420Case1.windowMoment, connCubeMass, connCubeFun, markVol]
  rw [M.lintegral_mark_eq_cutLaw (fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 3 *
      ∑ y ∈ E1Sign.ballF M r,
        (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y)
    (((measurable_clusterVol (0 : M.V)).pow_const 3).mul
      (Finset.measurable_sum _ fun y _ =>
        measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y))) r,
    E1Sign.cutLaw_eq M r]
  refine lintegral_congr fun ω => ?_
  rw [clusterVolIn_coe_finset]
  refine congrArg (fun t => clusterVol ω (0 : M.V) ^ 3 * t) ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : y ∈ cluster ω (0 : M.V)
  · rw [Set.indicator_of_mem h, ite_eq_left h]
  · rw [Set.indicator_of_notMem h, ite_eq_right h]

/-- **The covariance estimate with the connected third moment retained.**
`|B_r| (E|K_0|)(E|K_0|²) ≤ exclMassQuad r + connCubeMass r`. -/
theorem ncard_mul_le_exclMassQuad_add_connCubeMass (r : ℝ) :
    ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r)
      ≤ M.exclMassQuad r + M.connCubeMass r := by
  obtain ⟨𝓔, hmono, hcov⟩ := M.exists_edge_exhaustion
  have h := prodFactor_le_mixedExcl_add_window (π := M.cutProb r) (E1Sign.cutProb_lt_one M r)
    𝓔 hmono hcov (0 : M.V) 1 2 (E1Sign.ballF M r)
  have hprod : prodFactor (M.cutProb r) (0 : M.V) 1 2 (E1Sign.ballF M r)
      = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) := by
    rw [prodFactor, Finset.sum_congr rfl (fun y _ => by
          rw [M.powMomentAt_one_zero r, M.powMomentAt_two r y]),
      Finset.sum_const, E1Sign.card_ballF M r, nsmul_eq_mul]
  rw [hprod, ← M.exclMassQuad_eq_mixedExcl_window r, M.windowMoment_three_eq_connCubeMass r] at h
  exact h

/-! ## 7.  The two-sided covariance estimate in the joint form `quadPairMass`

`quadPairMass r = connCubeMass r + exclMassQuad r` is the full joint window mass
(`SecondMoment.Regularity.Main`).  It is *not* bounded by `|B_r| (E|K|)(E|K|²)`: only its
disconnected part is, and the covariance estimate reads

  `|B_r| (E|K_0|)(E|K_0|²) ≤ quadPairMass r ≤ connCubeMass r + |B_r| (E|K_0|)(E|K_0|²)`,
-/

/-- The product factor is a *lower* bound for the full joint window mass. -/
theorem ncard_mul_le_quadPairMass (r : ℝ) :
    ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) ≤ M.quadPairMass r := by
  rw [M.quadPairMass_eq_connCube_add r]
  calc ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r)
      ≤ M.exclMassQuad r + M.connCubeMass r := M.ncard_mul_le_exclMassQuad_add_connCubeMass r
    _ = M.connCubeMass r + M.exclMassQuad r := add_comm _ _

/-- The full joint window mass exceeds the product factor by at most the connected third moment. -/
theorem quadPairMass_le_connCubeMass_add (r : ℝ) :
    M.quadPairMass r
      ≤ M.connCubeMass r + ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) := by
  rw [M.quadPairMass_eq_connCube_add r]
  gcongr
  exact M.exclMassQuad_le_ncard_mul r

/-- **The covariance estimate with the connected third moment retained.**
`quadPairMass r - |B_r| (E|K_0|)(E|K_0|²) ≤ connCubeMass r`. -/
theorem quadPairMass_sub_le_connCubeMass (r : ℝ) :
    M.quadPairMass r - ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r)
      ≤ M.connCubeMass r :=
  tsub_le_iff_right.mpr (M.quadPairMass_le_connCubeMass_add r)

/-! ## 8.  The real-valued form used by the source

`(exclMassQuad r).toReal ≤ |B_r| (M.cutMoment 1 r).toReal (M.cutMoment 2 r).toReal`, with the two
moments finite (the paper's standing finiteness in Lemma I.2.1's third display). -/

theorem exclMassQuad_toReal_le (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (M.exclMassQuad r).toReal
      ≤ ((M.ball r).ncard : ℝ) * ((M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
  have htop : ((M.ball r).ncard : ℝ≥0∞) * (M.cutMoment 1 r * M.cutMoment 2 r) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top h1 h2)
  have h := ENNReal.toReal_mono htop (M.exclMassQuad_le_ncard_mul r)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast] at h

end SourceModelData
end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_eq_mixedExcl_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_eq_sum_conn
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.conn_excl_covariance
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclWindow_le_card_mul
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_le_ncard_mul
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_le_ncard_mul'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_le_ncard_mul_via_sum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuadLt_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuadShell_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassSqLin_le_ncard_mul
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2RHS_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ncard_mul_le_exclMassQuad_add_connCubeMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ncard_mul_le_quadPairMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.quadPairMass_le_connCubeMass_add
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.quadPairMass_sub_le_connCubeMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassQuad_toReal_le
