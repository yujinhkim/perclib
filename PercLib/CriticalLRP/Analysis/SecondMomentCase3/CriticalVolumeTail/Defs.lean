/-
Ultramath swarm `smwzlje3f`, member `m5`, direction `d5`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m5/Defs.lean`.

# The uncut critical volume tail: the leaf under the Case-3 moment gap

Source: Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), proof of
Proposition I.4.15, Case 3, p. 47, verbatim:

> Since the triangle condition implies the volume-tail upper bound
> `P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}` [12, 75], we can bound the first moment from above by
>
> `E_{β_c,r}|K| = ∑_n P_{β_c,r}(|K| ≥ n) ≤ ∑_{n=1}^N P_{β_c}(|K| ≥ n) + ∑_{n>N} E_{β_c,r}|K|²/n²`
>
> `⪯ ∑_{n=1}^N n^{-1/2} + N^{-1} E_{β_c,r}|K|² ⪯ N^{1/2} + N^{-1} E_{β_c,r}|K|²`
>
> for every `r > 0` and integer `N ≥ 1`. Optimizing by taking
> `N = ⌈(E_{β_c,r}|K|²)^{2/3}⌉` yields the claim.

The citation `[12, 75]` is D. J. Barsky, M. Aizenman, *Percolation critical exponents under the
triangle condition*, Ann. Probab. 19 (1991) 1520–1536, and T. Hutchcroft, *On the derivation of
mean-field percolation critical exponents from the triangle condition*, J. Stat. Phys. 189 (2022)
6.  Neither is formalized in this repository, and production has no theorem concluding an upper
bound on the *uncut* `criticalLaw` cluster-volume tail (see the audit in `report.md`).

`CriticalVolumeTail M C` below is exactly the display's single probabilistic input, at the uncut
critical law `P_{β_c}` (not `P_{β_c,r}`, and not a finite-volume or torus law).  We prove that

* the *summatory* form actually written in the display (`∑_{n ≤ N} P_{β_c}(|K| ≥ n) ≤ C √N`)
  implies the pointwise envelope `P_{β_c}(|K| ≥ n) ≤ C/√n`, so the pointwise form is not a
  strengthening of what the source uses;
* together with finiteness of the cutoff second moment at a single radius, the envelope yields
  the moment gap `E_{β_c,r}|K|² ⪰ (E_{β_c,r}|K|)³` at that radius, for *every* `r > 0` and with
  the explicit constant `(4C+1)^{-3}` — no `∀ᶠ` qualifier is needed.

Nothing here is derived from the triangle condition: production's consequences of the triangle
condition (`nablaTail`, `isLogErrorFunction_nablaTail`, the polygon bounds) are open-triangle or
cutoff statements, and the uncut volume tail is cited in the source, not proved.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration

/-- **A nonincreasing real sequence whose partial sums grow like `C √N` is pointwise
`≤ C/√N`.**  This is the exact step that makes a pointwise tail envelope equivalent to the
summatory form used in the source's display: by monotonicity `N · a N ≤ ∑_{n ≤ N} a n`, so no
strength is lost by stating the hypothesis pointwise. -/
theorem le_div_sqrt_of_summatory {a : ℕ → ℝ} (hmono : ∀ n, a (n + 1) ≤ a n)
    {C : ℝ} (hsum : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Icc 1 N, a n ≤ C * Real.sqrt N)
    {N : ℕ} (hN : 1 ≤ N) : a N ≤ C / Real.sqrt N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hanti : Antitone a := antitone_nat_of_succ_le hmono
  have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by
    rw [Nat.card_Icc]
    simp
  have hle : (N : ℝ) * a N ≤ ∑ n ∈ Finset.Icc 1 N, a n := by
    have hconst : ∑ _n ∈ Finset.Icc 1 N, a N = ((Finset.Icc 1 N).card : ℝ) * a N := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc (N : ℝ) * a N = ∑ _n ∈ Finset.Icc 1 N, a N := by rw [hconst, hcard]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, a n :=
        Finset.sum_le_sum fun n hn => hanti (Finset.mem_Icc.1 hn).2
  have hmain : (N : ℝ) * a N ≤ C * Real.sqrt N := hle.trans (hsum N hN)
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by
    rw [← sq, Real.sq_sqrt (le_of_lt hNpos)]
  have key : ((N : ℝ) * a N) / Real.sqrt N = a N * Real.sqrt N := by
    rw [div_eq_iff hsqrtpos.ne', mul_assoc, hsq]
    ring
  have step : a N * Real.sqrt N ≤ C := by
    calc a N * Real.sqrt N = ((N : ℝ) * a N) / Real.sqrt N := key.symm
      _ ≤ (C * Real.sqrt N) / Real.sqrt N := div_le_div_of_nonneg_right hmain hsqrtpos.le
      _ = C := mul_div_cancel_right₀ C hsqrtpos.ne'
  calc a N = (a N * Real.sqrt N) / Real.sqrt N :=
        (mul_div_cancel_right₀ (a N) hsqrtpos.ne').symm
    _ ≤ C / Real.sqrt N := div_le_div_of_nonneg_right step hsqrtpos.le

namespace SourceModelData

variable (M : SourceModelData)

/-- The source's uncut critical volume-tail envelope `P_{β_c}(|K_0| ≥ n) ⪯ n^{-1/2}`:
`M.criticalLaw` is the law at `β_c` with no cutoff and no finite-volume restriction, and
`Analysis.Route3.tailEnvelope C n` is `C / √n`. -/
def CriticalVolumeTail (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
      Analysis.Route3.tailEnvelope C n

/-- The *summatory* form of the same input, i.e. the quantity that appears verbatim in the
source's display: `∑_{n ≤ N} P_{β_c}(|K_0| ≥ n) ≤ C √N` for every `N ≥ 1`.  This is the weakest
form of the input that the source's optimization uses. -/
def CriticalVolumeTailSummatory (C : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 1 N,
        (M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal
      ≤ C * Real.sqrt N

/-- `CriticalVolumeTail` is *definitionally* the hypothesis `hVolTail` of the I.4.20 Case-3
assemblers (`I420Case3.exists_case3_i421_cutPoly_source_of_tail`,
`I420Case3.SplitPolygon.AllMoments`, `I420Case3.SplitPolygon.LowMoments`), so in Case 3 the
I.4.15 chain below and the I.4.20 chain share one and the same leaf. -/
theorem criticalVolumeTail_iff_source_form {C : ℝ} :
    M.CriticalVolumeTail C ↔
      ∀ n : ℕ, 1 ≤ n →
        M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
          Analysis.Route3.tailEnvelope C n :=
  Iff.rfl

/-- `n ↦ P_{β_c}(|K_0| ≥ n)` is nonincreasing: the events `{|K_0| ≥ n}` are nested. -/
theorem toReal_tail_antitone :
    Antitone (fun n : ℕ =>
      (M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal) := by
  haveI : IsProbabilityMeasure M.criticalLaw :=
    inferInstanceAs (IsProbabilityMeasure (longRangeMeasure M.kernel M.kernel_nonneg M.betaCrit))
  intro m n hmn
  refine ENNReal.toReal_mono (measure_ne_top (M.criticalLaw) _) (measure_mono ?_)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact le_trans (by exact_mod_cast hmn) hω

/-- The real-valued pointwise bound is the enveloped form: `P_{β_c}(|K_0| ≥ n) ≤ C/√n` in `ℝ`
and `≤ tailEnvelope C n` in `ℝ≥0∞` say the same thing. -/
theorem criticalVolumeTail_of_pointwise {C : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → M.tailProb n ≤ C / Real.sqrt n) : M.CriticalVolumeTail C := by
  haveI : IsProbabilityMeasure M.criticalLaw :=
    inferInstanceAs (IsProbabilityMeasure (longRangeMeasure M.kernel M.kernel_nonneg M.betaCrit))
  intro n hn
  have hNpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hNpos
  have hreal : (M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal
      ≤ C / Real.sqrt n := h n hn
  have hne : M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≠ ⊤ :=
    measure_ne_top _ _
  rw [Analysis.Route3.tailEnvelope_eq_ofReal hn, ← ENNReal.ofReal_div_of_pos hsqrtpos]
  calc M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      = ENNReal.ofReal
          ((M.criticalLaw {ω : Config M.V |
            (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal) :=
        (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (C / Real.sqrt n) := ENNReal.ofReal_le_ofReal hreal

/-- `P_{β_c}(|K_0| ≥ n) ≤ 1`. -/
theorem tailProb_le_one (n : ℕ) : M.tailProb n ≤ 1 := by
  haveI : IsProbabilityMeasure M.criticalLaw :=
    inferInstanceAs (IsProbabilityMeasure (longRangeMeasure M.kernel M.kernel_nonneg M.betaCrit))
  have hle : M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤ 1 := by
    calc M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ M.criticalLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  calc M.tailProb n
      = (M.criticalLaw {ω : Config M.V |
          (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal := rfl
    _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hle
    _ = 1 := by simp

/-- **The frozen anchors' volume-tail asymptotic implies the envelope.**  The second conjunct of
production's `Orchestration/Frozen/HighDimensionalMoments.theorem_I_1_6` and
`Orchestration/Frozen/CriticalDimensionMoments.theorem_I_1_15` is the first-order asymptotic
`P_{β_c}(|K_0| ≥ n) ∼ c n^{-1/2}`.  That asymptotic — not merely its boundedness — already
implies the up-to-constants envelope `CriticalVolumeTail`, so the envelope is the *minimal*
consequence of the frozen Theorem I.1.6 needed for the Case-3 moment gap.  Both frozen anchors are
`by sorry` drafts in production and are not imported here. -/
theorem exists_criticalVolumeTail_of_tail_asymptotic {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n : ℕ => M.tailProb n / (c * (1 / Real.sqrt (n : ℝ)))) atTop (𝓝 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ M.CriticalVolumeTail C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((h.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))).and
      (eventually_ge_atTop 1))
  have hN1 : 1 ≤ N := (hN N le_rfl).2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  refine ⟨max (2 * c) (max (N : ℝ) 1), ?_,
    M.criticalVolumeTail_of_pointwise (C := max (2 * c) (max (N : ℝ) 1)) ?_⟩
  · exact le_trans (le_of_lt (by linarith : (0 : ℝ) < 2 * c)) (le_max_left _ _)
  · intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hC2c : 2 * c ≤ max (2 * c) (max (N : ℝ) 1) := le_max_left _ _
    have hCN : (N : ℝ) ≤ max (2 * c) (max (N : ℝ) 1) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    by_cases hcase : N ≤ n
    · have hr : M.tailProb n / (c * (1 / Real.sqrt (n : ℝ))) ≤ 2 := (hN n hcase).1
      have hdpos : 0 < c * (1 / Real.sqrt (n : ℝ)) := mul_pos hc (by positivity)
      have hle := (div_le_iff₀ hdpos).1 hr
      calc M.tailProb n ≤ 2 * (c * (1 / Real.sqrt (n : ℝ))) := hle
        _ = (2 * c) / Real.sqrt n := by
            field_simp
        _ ≤ max (2 * c) (max (N : ℝ) 1) / Real.sqrt n :=
            div_le_div_of_nonneg_right hC2c hsqrtpos.le
    · have hnN : n < N := Nat.lt_of_not_ge hcase
      have hsqrtle : Real.sqrt (n : ℝ) ≤ (N : ℝ) := by
        have h1 : (n : ℝ) ≤ (N : ℝ) ^ 2 := by
          have hlt : (n : ℝ) < (N : ℝ) := by exact_mod_cast hnN
          have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
          calc (n : ℝ) ≤ (N : ℝ) := le_of_lt hlt
            _ = (N : ℝ) * 1 := (mul_one _).symm
            _ ≤ (N : ℝ) * (N : ℝ) :=
                mul_le_mul_of_nonneg_left hN1' (by linarith : (0 : ℝ) ≤ (N : ℝ))
            _ = (N : ℝ) ^ 2 := (sq _).symm
        calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
          _ = (N : ℝ) := Real.sqrt_sq hNpos.le
      have hCle : Real.sqrt (n : ℝ) ≤ max (2 * c) (max (N : ℝ) 1) := le_trans hsqrtle hCN
      calc M.tailProb n ≤ 1 := M.tailProb_le_one n
        _ = Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ) := (div_self hsqrtpos.ne').symm
        _ ≤ max (2 * c) (max (N : ℝ) 1) / Real.sqrt (n : ℝ) :=
            div_le_div_of_nonneg_right hCle hsqrtpos.le

/-- The summatory form of the source's display implies the pointwise envelope, with the same
constant.  Hence `CriticalVolumeTail` is not stronger than what the source uses. -/
theorem criticalVolumeTail_of_summatory {C : ℝ}
    (h : M.CriticalVolumeTailSummatory C) : M.CriticalVolumeTail C :=
  M.criticalVolumeTail_of_pointwise fun n hn =>
    le_div_sqrt_of_summatory (fun m => M.toReal_tail_antitone (Nat.le_succ m))
      (fun N hN => h N hN) hn

/-- **Uncut versus cutoff, in the only direction that holds.**  The uncut envelope dominates the
cutoff tail at every radius, because the cutoff kernel is below the full kernel
(`cutLaw_tail_le_criticalLaw`).  In particular no bound on a cutoff tail `P_{β_c,r}` can produce
`CriticalVolumeTail` by monotonicity: the monotonicity goes the wrong way, which is exactly why the
uncut input has to be cited rather than derived from `h1`, `h2` or the triangle condition. -/
theorem cutLaw_tail_le_envelope {C r : ℝ} (hr : 0 < r) (h : M.CriticalVolumeTail C)
    (n : ℕ) (hn : 1 ≤ n) :
    M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
      Analysis.Route3.tailEnvelope C n :=
  le_trans (cutLaw_tail_le_criticalLaw M hr n) (h n hn)

/-- **The moment gap at a single radius, with the source's explicit constant.**  This is the
source's optimization `N = ⌈(E_{β_c,r}|K|²)^{2/3}⌉` applied to the display: from the uncut
envelope and `M.cutMoment 2 r ≠ ⊤` we get
`(4C+1)^{-3} (E_{β_c,r}|K|)³ ≤ E_{β_c,r}|K|²`, for every `r > 0` — not merely eventually, and with
no free constant `c₃`. -/
theorem momentGap_of_volumeTail {C : ℝ} (hC : 0 ≤ C) (hTail : M.CriticalVolumeTail C)
    {r : ℝ} (hr : 0 < r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (Analysis.Route3.ratioConst C)⁻¹ * (M.cutMassAt r 0).toReal ^ 3
      ≤ (M.cutMoment 2 r).toReal := by
  have hbase := cutMoment_one_cube_le_two_of_tail M hC hr hTail
  have h1fin : M.cutMoment 1 r ≠ ⊤ := by
    rw [M.cutMoment_one_eq_cutMassAt]
    exact ne_top_of_le_ne_top h2 (E1Sign.cutMassAt_le_cutMoment_two M r)
  have hreal : (M.cutMoment 1 r).toReal ^ 3
      ≤ Analysis.Route3.ratioConst C * (M.cutMoment 2 r).toReal := by
    have h := (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top h1fin)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2)).mpr hbase
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Analysis.Route3.ratioConst_nonneg hC)] using h
  rw [M.cutMassAt_zero_eq_cutMoment r]
  calc (Analysis.Route3.ratioConst C)⁻¹ * (M.cutMoment 1 r).toReal ^ 3
      ≤ (Analysis.Route3.ratioConst C)⁻¹
          * (Analysis.Route3.ratioConst C * (M.cutMoment 2 r).toReal) :=
        mul_le_mul_of_nonneg_left hreal
          (inv_nonneg.mpr (Analysis.Route3.ratioConst_nonneg hC))
    _ = (M.cutMoment 2 r).toReal := by
        rw [← mul_assoc, inv_mul_cancel₀ (Analysis.Route3.ratioConst_ne_zero hC), one_mul]

end SourceModelData

end Orchestration
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Orchestration.le_div_sqrt_of_summatory
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.toReal_tail_antitone
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_of_summatory
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_of_volumeTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tailProb_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_criticalVolumeTail_of_tail_asymptotic
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_of_pointwise
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_iff_source_form
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_le_envelope
