/-
Accepted from Ultramath `smwzg77c3`, member `m7`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d6`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The diagonal obstruction to the `q = 0` two-term estimate

The target estimate of `Defs.lean` (`StarTwoTermBound`) is the `p = 3`, `q = 0` reading of
Hutchcroft, *Critical long-range percolation I*, Lemma I.4.17, demanded at *every* vertex `y`.

This file proves that the diagonal vertex `y = 0` cannot satisfy it in the source's own Case-3
regime.  Three landed facts suffice:

* `connCubeVertexMass_zero`: at `y = 0` the per-vertex numerator is the plain third cutoff moment,
  `M.connCubeVertexMass r 0 = M.cutMoment 3 r`, i.e. `E_{beta_c,r}|K_0|^3`.  Nothing `y`-dependent
  survives.
* `polyK_three_diag_le` / `polyK_four_diag_le`: at the diagonal the two matrix powers are
  `T^3(0,0) = nabla_r <= nabla = M.triSelf` (the triangle condition,
  `I418C.source_polyK_three_le_triSelf`)
  and `T^4(0,0) <= nabla * chi`.  So the right-hand side of the diagonal instance is at most
  `(C3 + C4) * nabla * chi^4`: **the diagonal carries only `chi^4`, not the `chi^5` that the third
  moment has.**
* `growth_of_higherMoment`: the source's Proposition I.4.20 at `p = 3`,
  `E|K|^3 ~ 3 (E|K|^2 / E|K|)^2 E|K|`, combined with the Case-3 relation
  `E|K|^2 >~ (E|K|)^3`, gives `3 * chi^5 <~ E|K|^3`.

Consequently the diagonal instance forces `3 * chi <= (C3 + C4) * nabla`, i.e. it bounds the
susceptibility by the triangle constant; since `chi -> infinity` in Case 3 while `nabla < infinity`,
**the unconditional two-term estimate is false for large `r`**, and the correct source-faithful
statement has to exclude a neighbourhood of the diagonal (`StarTwoTermBoundFar`), exactly as the
printed `l = 3` polygon display of Lemma I.4.18 is false at `x = 0`
(`I420Case3.one_le_polyK_three_of_chi_ne_top`, `I420Case3.one_le_Bpoly_of_hasPolygonBound`).

No `sorry`, no `admit`, no `native_decide`, no custom axioms, no `top`-to-`0` conversion: every
`RR>=0` step is either an identity or an inequality, and the real-valued statements divide only by
the strictly positive `chi^4` whose positivity is derived (`0 < chi`) rather than assumed.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Defs

/-! # The diagonal instance and the obstruction -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Smwzg77c3.M7

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C

variable (M : SourceModelData)

/-! ## The susceptibility is at least one -/

/-- Every cluster contains its basepoint, so the finite-cutoff susceptibility is at least `1`. -/
theorem one_le_cutMassAt (r : ℝ) : (1 : ℝ≥0∞) ≤ M.cutMassAt r 0 := by
  rw [← M.cutMassAtBeta_betaCrit r 0]
  exact M.one_le_cutMassAtBeta M.betaCrit r 0

/-- The real-valued form: `1 <= chi`, hence `chi` is positive. -/
theorem one_le_chi (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) : (1 : ℝ) ≤ chi M r := by
  have h := ENNReal.toReal_mono hχ (one_le_cutMassAt M r)
  simpa [chi] using h

theorem chi_pos (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) : 0 < chi M r :=
  lt_of_lt_of_le one_pos (one_le_chi M r hχ)

/-! ## The per-vertex numerator at the basepoint -/

/-- At `y = 0` the connected third window mass is the plain third cutoff moment
`E_{beta_c,r}|K_0|^3`. -/
theorem connCubeVertexMass_zero (r : ℝ) :
    M.connCubeVertexMass r (0 : M.V) = M.cutMoment 3 r := by
  rw [SourceModelData.connCubeVertexMass, SourceModelData.cutMoment]
  refine lintegral_congr fun ω => ?_
  rw [Set.indicator_of_mem (cluster_mem_self ω (0 : M.V)) (fun _ => (1 : ℝ≥0∞)), mul_one]

/-- The diagonal instance of `StarTwoTermBound`. -/
theorem diag_instance {C3 C4 : ℝ} (h : StarTwoTermBound M C3 C4) {r : ℝ} (hr : 1 ≤ r) :
    (M.cutMoment 3 r).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3 := by
  have h0 := h r hr (0 : M.V)
  rwa [connCubeVertexMass_zero] at h0

/-- The diagonal instance of the window form `StarTwoTermBoundWindow`. -/
theorem diag_instance_window {C3 C4 : ℝ} (h : StarTwoTermBoundWindow M C3 C4) {r : ℝ}
    (hr : 1 ≤ r) (h0 : (0 : M.V) ∈ E1Sign.ballF M r) :
    (M.cutMoment 3 r).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3 := by
  have h := h r hr (0 : M.V) h0
  rwa [connCubeVertexMass_zero] at h

/-! ## The two diagonal matrix powers -/

/-- The diagonal threefold cutoff power is at most the (finite) uncut triangle `nabla`. -/
theorem polyK_three_diag_le {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 ≤ M.triSelf := by
  obtain ⟨hB2, hB3, hlink⟩ := M.hB2_hB3_hlink_derived hTri
  exact I418C.source_polyK_three_le_triSelf M r hχ hTri hB2 hB3 hlink 0

/-- The diagonal fourfold cutoff power is at most `nabla * chi`: composition with the column sum
`sum_y T(y,0) = chi` of the landed `PowerInputs`. -/
theorem polyK_four_diag_le {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 ≤ M.triSelf * chi M r := by
  obtain ⟨hB2, hB3, hlink⟩ := M.hB2_hB3_hlink_derived hTri
  have hPI := M.source_powerInputs r hχ hTri hB2 hB3 hlink
  have hcol : (∑' z : M.V, M.cutTwoPoint r z 0) = chi M r := by
    have h1 : (∑' z : M.V, I418C.polyK (M.cutTwoPoint r) 1 z 0) = chi M r := by
      rw [hPI.colsum 1, pow_one]
      rfl
    rw [← h1]
    exact tsum_congr fun z => (polyK_one (M.cutTwoPoint r) z 0).symm
  have hsumL : Summable
      (fun z : M.V => I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) z * M.cutTwoPoint r z 0) := by
    have h := hPI.compSummable 1
    simpa only [polyK_one] using h
  have hsumR : Summable (fun z : M.V => M.triSelf * M.cutTwoPoint r z 0) := by
    have h : Summable (fun z : M.V => M.cutTwoPoint r z 0) := by
      simpa only [polyK_one] using hPI.colSummable 1
    exact h.mul_left M.triSelf
  calc I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0
      = ∑' z : M.V,
          I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) z * M.cutTwoPoint r z 0 :=
        polyK_succ (M.cutTwoPoint r) 3 (0 : M.V) 0
    _ ≤ ∑' z : M.V, M.triSelf * M.cutTwoPoint r z 0 := by
        refine Summable.tsum_le_tsum (fun z => ?_) hsumL hsumR
        exact mul_le_mul_of_nonneg_right (hPI.triSup z) (M.cutTwoPoint_nonneg r z 0)
    _ = M.triSelf * (∑' z : M.V, M.cutTwoPoint r z 0) := tsum_mul_left
    _ = M.triSelf * chi M r := by rw [hcol]

/-! ## The obstruction -/

/-- **The diagonal instance bounds the susceptibility by the triangle constant.**

If the two-term estimate holds at the basepoint, and the third moment has the source's
Proposition I.4.20 growth `K * chi^5 <= E|K|^3`, then `K * chi <= (C3 + C4) * nabla`.  In Case 3
`chi -> infinity` and `nabla < infinity`, so no choice of `C3`, `C4` can satisfy this for all
`r`. -/
theorem chi_le_of_diag {C3 C4 K : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hdiag : (M.cutMoment 3 r).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3)
    (hgrowth : K * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal) :
    K * chi M r ≤ (C3 + C4) * M.triSelf := by
  have hΛ : (0 : ℝ) ≤ M.triSelf := ENNReal.toReal_nonneg
  have hχnn : (0 : ℝ) ≤ chi M r := ENNReal.toReal_nonneg
  have hP3 := polyK_three_diag_le M hχ hTri
  have hP4 := polyK_four_diag_le M hχ hTri
  have hχ3 : (0 : ℝ) ≤ chi M r ^ 3 := pow_nonneg hχnn 3
  have hstep : K * chi M r ^ 5 ≤ (C3 + C4) * M.triSelf * chi M r ^ 4 := by
    refine hgrowth.trans (hdiag.trans ?_)
    have h1 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * chi M r ^ 4
        ≤ C3 * M.triSelf * chi M r ^ 4 := by
      have := mul_le_mul_of_nonneg_right hP3 (pow_nonneg hχnn 4)
      nlinarith
    have h2 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3
        ≤ C4 * M.triSelf * chi M r ^ 4 := by
      have hP4' : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3
          ≤ C4 * (M.triSelf * chi M r) * chi M r ^ 3 := by
        have := mul_le_mul_of_nonneg_left hP4 hC4
        nlinarith
      calc C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3
          ≤ C4 * (M.triSelf * chi M r) * chi M r ^ 3 := hP4'
        _ = C4 * M.triSelf * chi M r ^ 4 := by ring
    calc C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * chi M r ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3
        ≤ C3 * M.triSelf * chi M r ^ 4 + C4 * M.triSelf * chi M r ^ 4 := add_le_add h1 h2
      _ = (C3 + C4) * M.triSelf * chi M r ^ 4 := by ring
  have hχ4 : (0 : ℝ) < chi M r ^ 4 := by
    have hpos := chi_pos M r hχ
    positivity
  have hfac : K * chi M r ^ 5 = (K * chi M r) * chi M r ^ 4 := by ring
  have hfac2 : (C3 + C4) * M.triSelf * chi M r ^ 4 = ((C3 + C4) * M.triSelf) * chi M r ^ 4 := by
    ring
  rw [hfac, hfac2] at hstep
  exact le_of_mul_le_mul_right hstep hχ4

/-- **The unconditional two-term estimate fails at the basepoint.**  Version for
`StarTwoTermBound`. -/
theorem not_starTwoTermBound {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hgrowth : ∀ r : ℝ, 1 ≤ r → 3 * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hunbdd : ∀ B : ℝ, ∃ r : ℝ, 1 ≤ r ∧ B < 3 * chi M r) :
    ¬ StarTwoTermBound M C3 C4 := by
  intro h
  obtain ⟨r, hr, hbig⟩ := hunbdd ((C3 + C4) * M.triSelf)
  have hle := chi_le_of_diag M hC3 hC4 (hχ r hr) hTri (diag_instance M h hr) (hgrowth r hr)
  exact absurd hle (not_le.mpr hbig)

/-- **The unconditional window estimate fails at the basepoint.**  Version for the landed
consumer shape `StarTwoTermBoundWindow`, when the window contains the origin. -/
theorem not_starTwoTermBoundWindow {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (h0 : ∀ r : ℝ, 1 ≤ r → (0 : M.V) ∈ E1Sign.ballF M r)
    (hgrowth : ∀ r : ℝ, 1 ≤ r → 3 * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hunbdd : ∀ B : ℝ, ∃ r : ℝ, 1 ≤ r ∧ B < 3 * chi M r) :
    ¬ StarTwoTermBoundWindow M C3 C4 := by
  intro h
  obtain ⟨r, hr, hbig⟩ := hunbdd ((C3 + C4) * M.triSelf)
  have hle := chi_le_of_diag M hC3 hC4 (hχ r hr) hTri (diag_instance_window M h hr (h0 r hr))
    (hgrowth r hr)
  exact absurd hle (not_le.mpr hbig)

/-! ## The source's growth hypothesis

Proposition I.4.20 at `p = 3` reads `E|K|^3 ~ 3 (E|K|^2 / E|K|)^2 E|K|`, and the Case-3
relation `E|K|^2 >~ (E|K|)^3` then gives `E|K|^3 >~ 3 chi^5`.  The next lemma records exactly
that implication, at the level of the two cutoff moments. -/

/-- **From the higher-moment asymptotic to the growth used above.**  If the third moment has the
Proposition I.4.20 shape `3 * chi_2^2 / chi <= E|K|^3` and the second moment dominates `chi^3`,
then `3 * chi^5 <= E|K|^3`. -/
theorem growth_of_higherMoment {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤)
    (h20 : 3 * (M.cutMoment 2 r).toReal ^ 2 / chi M r ≤ (M.cutMoment 3 r).toReal)
    (h2 : chi M r ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    3 * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal := by
  have hχ0 := chi_pos M r hχ
  have hχ2nn : (0 : ℝ) ≤ (M.cutMoment 2 r).toReal := ENNReal.toReal_nonneg
  have hpow : chi M r ^ 5 ≤ (M.cutMoment 2 r).toReal ^ 2 / chi M r := by
    rw [le_div_iff₀ hχ0]
    have h6 : chi M r ^ 5 * chi M r = chi M r ^ 6 := by ring
    rw [h6]
    have hsq : (chi M r ^ 3) ^ 2 ≤ (M.cutMoment 2 r).toReal ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    calc chi M r ^ 6 = (chi M r ^ 3) ^ 2 := by ring
      _ ≤ (M.cutMoment 2 r).toReal ^ 2 := hsq
  calc 3 * chi M r ^ 5 ≤ 3 * ((M.cutMoment 2 r).toReal ^ 2 / chi M r) := by linarith [hpow]
    _ = 3 * (M.cutMoment 2 r).toReal ^ 2 / chi M r := by ring
    _ ≤ (M.cutMoment 3 r).toReal := h20

end PercLib.CriticalLRP.Smwzg77c3.M7

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.connCubeVertexMass_zero
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.polyK_three_diag_le
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.polyK_four_diag_le
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.chi_le_of_diag
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.not_starTwoTermBound
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.not_starTwoTermBoundWindow
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.growth_of_higherMoment
