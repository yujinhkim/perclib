/-
Ultramath swarm `smwzqts7r`, member `m6`, direction `d5`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m6.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m6/Defs.lean`.

# Direction (C): the sharp per-radius critical volume tail

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 3, p. 47, verbatim:

> Since the triangle condition implies the volume-tail upper bound
> `P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}` [12, 75], we can bound the first moment from above by
> `E_{β_c,r}|K| = ∑_n P_{β_c,r}(|K| ≥ n) ≤ ∑_{n=1}^N P_{β_c}(|K| ≥ n) + ∑_{n>N} E_{β_c,r}|K|²/n²
>  ⪯ N^{1/2} + N^{-1} E_{β_c,r}|K|²`

Production (`CriticalVolumeTail`, `CriticalVolumeTail.UniformCutoff`) knows that the cited leaf
`SourceModelData.CriticalVolumeTail C` is *exactly* the statement that the cutoff tails
`P_{β_c,r}(|K_0| ≥ n)` admit one constant `C` uniform in `r`, and that the leaf implies the
Case-3 moment gap with constant `(4C+1)^{-3}`.  Production proves neither direction of the leaf
and does not relate it to any quantity it can compute.

This file proves the two things that *are* true and computable.

## §1 The second moment bounds the *per-radius* tail, sharply

For every radius `r > 0` with `E_{β_c,r}|K|² < ∞` and every `n ≥ 1`,

  `P_{β_c,r}(|K_0| ≥ n) ≤ (E_{β_c,r}|K|²)^{1/4} / √n`   (`cutLaw_tail_le_secondMoment`).

This is the envelope that the two available bounds — the trivial `P ≤ 1` and Markov
`P ≤ m/n²` — produce, and the exponent `1/4` is exact: `√n · min 1 (m/n²) ≤ m^{1/4}` is
attained at `n = ⌈√m⌉`, so no smaller power of the second moment can appear.  Consequently the
constant *must* depend on `r` unless the cutoff second moments are bounded in `r`; that is
`criticalVolumeTail_of_uniform_secondMoment`, which records the exact sufficient condition for the
cited leaf that the second-moment method gives and no more.

## §2 What the leaf is a statement about

`uniform_cutTail_constant` rewrites that consequence in the `UniformCutoff` language: a bound
`∀ r > 0, E_{β_c,r}|K|² ≤ K` gives the radius-uniform cutoff envelope with constant `K^{1/4}` and
hence `CriticalVolumeTail (K^{1/4})`.  So the `r`-uniformity in the cited leaf is a statement about
the *second-moment scale*, not about the triangle condition directly, and the second-moment method
delivers it only when the critical cutoff second moments are bounded.

Nothing in this file is a derivation of the cited leaf: §1 has an `r`-dependent constant by
construction, and §2 assumes exactly what is missing.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.UniformCutoff.Defs

/-! Per-radius second-moment tail estimates and explicit uniformity obstructions. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration

/-! ## §1 The crossover `√n · min 1 (m/n²) ≤ m^{1/4}` -/

/-- `m^{1/4}` written with square roots.  Used so that the proof only ever squares. -/
theorem quarterRoot_eq_sqrt_sqrt {m : ℝ} (hm : 0 ≤ m) :
    m ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt m) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hm]
  norm_num

/-- **The crossover inequality.**  For `n ≥ 1`,
`√n · min 1 (m/n²) ≤ √√m`.

The two branches are exactly the two bounds available for a probability `p` with second moment
`m`: `p ≤ 1` and `p ≤ m/n²`.  The exponent `1/4` is optimal for this pair of bounds: when
`m = n²` both branches equal `1` and the inequality is an equality, so no smaller power of `m`
works for all `n`. -/
theorem sqrt_mul_min_le_quarterRoot {m : ℝ} (hm : 0 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n * min 1 (m / (n : ℝ) ^ 2) ≤ Real.sqrt (Real.sqrt m) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set A : ℝ := Real.sqrt (Real.sqrt m) with hAdef
  set B : ℝ := Real.sqrt (n : ℝ) with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 < B := by rw [hBdef]; exact Real.sqrt_pos.2 hnpos
  have hA4 : A ^ 4 = m := by
    rw [hAdef]
    have h1 : Real.sqrt (Real.sqrt m) ^ 2 = Real.sqrt m :=
      Real.sq_sqrt (Real.sqrt_nonneg m)
    calc (Real.sqrt (Real.sqrt m)) ^ 4 = (Real.sqrt (Real.sqrt m) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt m) ^ 2 := by rw [h1]
      _ = m := Real.sq_sqrt hm
  have hB2 : B ^ 2 = (n : ℝ) := by rw [hBdef]; exact Real.sq_sqrt hnpos.le
  have hquot : m / (n : ℝ) ^ 2 = A ^ 4 / B ^ 4 := by
    rw [hA4, ← hB2]; ring
  rw [hquot]
  rcases le_or_gt B A with hBA | hAB
  · have h1 : min 1 (A ^ 4 / B ^ 4) ≤ 1 := min_le_left _ _
    calc B * min 1 (A ^ 4 / B ^ 4) ≤ B * 1 := mul_le_mul_of_nonneg_left h1 hB0.le
      _ = B := mul_one B
      _ ≤ A := hBA
  · have hlt : A ^ 4 / B ^ 4 < 1 := by
      rw [div_lt_one (by positivity)]
      exact pow_lt_pow_left₀ hAB hA0 (by norm_num : (4 : ℕ) ≠ 0)
    rw [min_eq_right hlt.le]
    have hgoal : B * (A ^ 4 / B ^ 4) = A ^ 4 / B ^ 3 := by
      field_simp
    rw [hgoal, div_le_iff₀ (by positivity)]
    have hA3 : A ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hA0 hAB.le 3
    nlinarith [hA3, hA0]

end Orchestration
end PercLib.CriticalLRP


namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- `tailEnvelope` is monotone in its constant. -/
theorem tailEnvelope_mono {C C' : ℝ} (h : C ≤ C') (n : ℕ) :
    Analysis.Route3.tailEnvelope C n ≤ Analysis.Route3.tailEnvelope C' n :=
  ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h (Real.sqrt_nonneg (n : ℝ)))

/-- **Markov at the second moment, in the model.**  For `r > 0`,
`P_{β_c,r}(|K_0| ≥ n) ≤ E_{β_c,r}|K|² / n²`. -/
theorem cutLaw_tail_le_secondMoment_div {r : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ M.cutMoment 2 r / (n : ℝ≥0∞) ^ 2 := by
  have hX : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) := measurable_clusterVol 0
  have hsub : {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ⊆ {ω : Config M.V | (n : ℝ≥0∞) ^ 2 ≤ clusterVol ω (0 : M.V) ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    exact pow_le_pow_left' hω 2
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hn0' : (n : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  have h := meas_ge_le_lintegral_div (μ := M.cutLaw r)
    (f := fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 2)
    ((hX.pow_const 2).aemeasurable) (ε := (n : ℝ≥0∞) ^ 2) hn0' (by simp)
  calc M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ^ 2 ≤ clusterVol ω (0 : M.V) ^ 2} :=
        measure_mono hsub
    _ ≤ (∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) ^ 2 ∂(M.cutLaw r)) / (n : ℝ≥0∞) ^ 2 := h
    _ = M.cutMoment 2 r / (n : ℝ≥0∞) ^ 2 := rfl

/-- **The sharp per-radius critical volume tail.**  For every radius `r > 0` at which the cutoff
second moment is finite, and every `n ≥ 1`,

  `P_{β_c,r}(|K_0| ≥ n) ≤ (E_{β_c,r}|K|²)^{1/4} / √n`.

This is the envelope produced by the two available bounds `P ≤ 1` and Markov
`P ≤ E|K|²/n²`, with the exact crossover exponent: no smaller power of the cutoff second moment
can appear, since `sqrt_mul_min_le_quarterRoot` is an equality at `E|K|² = n²`.  Consequently the
constant is genuinely
`r`-dependent, which is precisely the gap that `UniformCutoff.criticalVolumeTail_iff_uniform_cutTail`
exhibits in the cited leaf. -/
theorem cutLaw_tail_le_secondMoment {r : ℝ} (h2 : M.cutMoment 2 r ≠ ⊤)
    (n : ℕ) (hn : 1 ≤ n) :
    M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ Analysis.Route3.tailEnvelope ((M.cutMoment 2 r).toReal ^ ((1 : ℝ) / 4)) n := by
  haveI : IsProbabilityMeasure (M.cutLaw r) :=
    inferInstanceAs (IsProbabilityMeasure
      (longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit))
  set m : ℝ := (M.cutMoment 2 r).toReal with hmdef
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hmof : M.cutMoment 2 r = ENNReal.ofReal m := (ENNReal.ofReal_toReal h2).symm
  -- the two bounds
  have htriv : M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤ 1 := by
    calc M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ M.cutLaw r Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hmarkov : M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ ENNReal.ofReal (m / (n : ℝ) ^ 2) := by
    refine le_trans (M.cutLaw_tail_le_secondMoment_div hn) ?_
    rw [hmof, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
  -- combine
  have hmin : M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ ENNReal.ofReal (min 1 (m / (n : ℝ) ^ 2)) := by
    rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
    exact le_min htriv hmarkov
  refine le_trans hmin ?_
  have hquarter : (M.cutMoment 2 r).toReal ^ ((1 : ℝ) / 4) = m ^ ((1 : ℝ) / 4) := by
    rw [hmdef]
  have hsqrtpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hreal : min 1 (m / (n : ℝ) ^ 2) ≤ m ^ ((1 : ℝ) / 4) / Real.sqrt n := by
    rw [quarterRoot_eq_sqrt_sqrt hm0, le_div_iff₀ hsqrtpos]
    calc min 1 (m / (n : ℝ) ^ 2) * Real.sqrt n = Real.sqrt n * min 1 (m / (n : ℝ) ^ 2) :=
          mul_comm _ _
      _ ≤ Real.sqrt (Real.sqrt m) := sqrt_mul_min_le_quarterRoot hm0 hn
  rw [Analysis.Route3.tailEnvelope, hquarter]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **The uniform-in-`r` consequence.**  If the critical cutoff second moments are bounded by `K`
at every radius, then the cited uncut volume tail holds with constant `K^{1/4}`.

The hypothesis is the *exact* sufficient condition the second-moment method produces; at `β_c` the
cutoff second moments are unbounded, so this is not the source's route and is not presented as one.
What it does establish is where the difficulty of the cited leaf sits: in the `r`-uniformity of the
second-moment scale, not in the `n^{-1/2}` exponent. -/
theorem criticalVolumeTail_of_uniform_secondMoment {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ r : ℝ, 0 < r → M.cutMoment 2 r ≤ ENNReal.ofReal K) :
    M.CriticalVolumeTail (K ^ ((1 : ℝ) / 4)) := by
  refine (M.criticalVolumeTail_iff_uniform_cutTail (C := K ^ ((1 : ℝ) / 4))).mpr ?_
  intro r hr n hn
  have hKr : M.cutMoment 2 r ≤ ENNReal.ofReal K := hK r hr
  have hne : M.cutMoment 2 r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKr
  refine le_trans (M.cutLaw_tail_le_secondMoment hne n hn) ?_
  refine tailEnvelope_mono ?_ n
  have hle : (M.cutMoment 2 r).toReal ≤ K := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKr
    rwa [ENNReal.toReal_ofReal hK0] at h
  exact Real.rpow_le_rpow (ENNReal.toReal_nonneg) hle (by norm_num)

/-- **The Case-3 moment gap from a uniform bound on the critical cutoff second moment.**

This chains `cutLaw_tail_le_secondMoment` with production's `momentGap_of_volumeTail`, so the whole
Case-3 leaf is seen to be a statement about the second-moment scale: with
`E_{β_c,r}|K|² ≤ K` at every radius, the gap holds with the explicit constant
`(4K^{1/4}+1)^{-3}` and no further probabilistic input. -/
theorem momentGap_of_uniform_secondMoment {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ r : ℝ, 0 < r → M.cutMoment 2 r ≤ ENNReal.ofReal K)
    {r : ℝ} (hr : 0 < r) :
    (Analysis.Route3.ratioConst (K ^ ((1 : ℝ) / 4)))⁻¹ * (M.cutMassAt r 0).toReal ^ 3
      ≤ (M.cutMoment 2 r).toReal :=
  M.momentGap_of_volumeTail (Real.rpow_nonneg hK0 _)
    (M.criticalVolumeTail_of_uniform_secondMoment hK0 hK) hr
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hK r hr))

end SourceModelData
end Orchestration
end PercLib.CriticalLRP


/-! ## §3 The scale-truncated cited leaf

The source's display does not use the `n^{-1/2}` envelope at *all* scales: the head sum runs only
to `N`, and `N` is afterwards optimized to `⌈(E_{β_c,r}|K|²)^{2/3}⌉`.  So the only part of the cited
leaf that the Case-3 chain consumes is the envelope up to the source's own truncation scale
`Analysis.Route3.cutoffScale (E_{β_c,r}|K|²)`.  This section proves that the truncated form is
*sufficient*, with the same constant `(4C+1)³`, and that it is implied by production's leaf; hence
it is a genuine weakening of `CriticalVolumeTail`, not a restatement of it.

The three lemmas below are production's `sum_filter_head_le`, `partialSum_le`,
`cube_lintegral_le_of_tail` with the tail hypothesis restricted to `n ≤ N`.
-/

namespace PercLib.CriticalLRP.Analysis.Route3

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}

/-- **The head bound, truncated.**  Only the values of the envelope at scales `n ≤ N` are used. -/
theorem sum_filter_head_le_trunc {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hTail : ∀ n : ℕ, 1 ≤ n → n ≤ N → μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ tailEnvelope C n) (M : ℕ) :
    ∑ j ∈ (Finset.range M).filter (fun j => j + 1 ≤ N), μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
      ≤ ENNReal.ofReal (2 * C * Real.sqrt N) := by
  have hterm : ∀ j ∈ (Finset.range M).filter (fun j => j + 1 ≤ N),
      μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} ≤ ENNReal.ofReal (C / Real.sqrt ((j : ℝ) + 1)) := by
    intro j hj
    have h1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have h2 : j + 1 ≤ N := (Finset.mem_filter.1 hj).2
    have := hTail (j + 1) h1 h2
    simpa [tailEnvelope, Nat.cast_add, Nat.cast_one] using this
  have hfil : (Finset.range M).filter (fun j => j + 1 ≤ N) = Finset.range (min N M) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), hfil]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : ∑ j ∈ Finset.range (min N M), C / Real.sqrt ((j : ℝ) + 1)
      = C * ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
  rw [hsplit]
  have hmono : ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹
      ≤ ∑ j ∈ Finset.range N, (Real.sqrt ((j : ℝ) + 1))⁻¹ :=
    sum_range_inv_sqrt_mono (min_le_left N M)
  have hhead : ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹
      ≤ 2 * Real.sqrt (N : ℝ) := le_trans hmono (sum_range_inv_sqrt_le N)
  calc C * ∑ j ∈ Finset.range (min N M), (Real.sqrt ((j : ℝ) + 1))⁻¹
      ≤ C * (2 * Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left hhead hC
    _ = 2 * C * Real.sqrt (N : ℝ) := by ring

/-- **The split partial sum, truncated.**  The source's displayed estimate
`∑_{n ≤ N} P + ∑_{N < n} m₂/n² ≤ 2C√N + m₂/N`, with the envelope required only at `n ≤ N`. -/
theorem partialSum_le_trunc {C : ℝ} (hC : 0 ≤ C) (hX : Measurable X) {N : ℕ} (hN : 1 ≤ N)
    (hTail : ∀ n : ℕ, 1 ≤ n → n ≤ N → μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ tailEnvelope C n) (M : ℕ) :
    ∑ j ∈ Finset.range M, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}
      ≤ ENNReal.ofReal (2 * C * Real.sqrt N) + (∫⁻ ω, X ω ^ 2 ∂μ) / (N : ℝ≥0∞) := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range M)
    (p := fun j => j + 1 ≤ N) (f := fun j => μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω})]
  exact add_le_add (sum_filter_head_le_trunc hC hTail M) (sum_filter_tail_le hX hN M)

/-- **Route 3 of Proposition I.4.15 with the envelope truncated at the source's own scale.**

For a probability measure, a measurable integer-valued `X ≥ 1`, and the `n^{-1/2}` envelope
required only for `n ≤ cutoffScale (∫⁻ X²)`, the first moment is dominated by the cube root of the
second: `(∫⁻ X)³ ≤ (4C+1)³ ∫⁻ X²`.  This is production's `cube_lintegral_le_of_tail` with a strictly
weaker hypothesis on `n`, and the same constant. -/
theorem cube_lintegral_le_of_tail_trunc [IsProbabilityMeasure μ] (hX : Measurable X)
    (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) (hX1 : ∀ ω, 1 ≤ X ω) {C : ℝ}
    (hC : 0 ≤ C)
    (hTail : ∀ n : ℕ, 1 ≤ n → n ≤ cutoffScale (∫⁻ ω, X ω ^ 2 ∂μ).toReal →
      μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ tailEnvelope C n) :
    (∫⁻ ω, X ω ∂μ) ^ 3 ≤ ENNReal.ofReal (ratioConst C) * ∫⁻ ω, X ω ^ 2 ∂μ := by
  classical
  set m2 : ℝ≥0∞ := ∫⁻ ω, X ω ^ 2 ∂μ with hm2def
  rcases eq_or_ne m2 ⊤ with hm2top | hm2ne
  · rw [hm2top, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.2 (ratioConst_pos hC))]
    exact le_top
  set m : ℝ := m2.toReal with hmdef
  have hm2of : m2 = ENNReal.ofReal m := (ENNReal.ofReal_toReal hm2ne).symm
  have hmge : 1 ≤ m := by
    have h1 : (1 : ℝ≥0∞) ≤ m2 := by
      calc (1 : ℝ≥0∞) = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := by
            rw [lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ ω, X ω ^ 2 ∂μ :=
            lintegral_mono fun ω => by simpa using pow_le_pow_left' (hX1 ω) 2
    have := ENNReal.toReal_mono hm2ne h1
    simpa [hmdef] using this
  set t : ℝ := m ^ ((1 : ℝ) / 3) with htdef
  set N : ℕ := cutoffScale m with hNdef
  have hN1 : 1 ≤ N := one_le_cutoffScale hmge
  have hNne : (N : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hbound : ∫⁻ ω, X ω ∂μ
      ≤ ENNReal.ofReal (2 * C * Real.sqrt N) + m2 / (N : ℝ≥0∞) := by
    rw [PercLib.CriticalLRP.Tightness.lintegral_eq_tsum_meas_ge hX hint,
      ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun M => partialSum_le_trunc hC hX hN1 ?_ M
    intro n hn hle
    exact hTail n hn hle
  have hfin1 : ENNReal.ofReal (2 * C * Real.sqrt N) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin2 : m2 / (N : ℝ≥0∞) ≠ ⊤ := by
    rw [hm2of, ENNReal.div_eq_inv_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hNne) ENNReal.ofReal_ne_top
  have hfinT : ENNReal.ofReal (2 * C * Real.sqrt N) + m2 / (N : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩
  have hm1fin : ∫⁻ ω, X ω ∂μ ≠ ⊤ := ne_top_of_le_ne_top hfinT hbound
  have hreal : (∫⁻ ω, X ω ∂μ).toReal ≤ 2 * C * Real.sqrt N + m / N := by
    have h := ENNReal.toReal_mono hfinT hbound
    have hsplit : (ENNReal.ofReal (2 * C * Real.sqrt N) + m2 / (N : ℝ≥0∞)).toReal
        = 2 * C * Real.sqrt N + m / N := by
      rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_div, ← hmdef, ENNReal.toReal_natCast]
    linarith [h, hsplit ▸ h]
  have harith : 2 * C * Real.sqrt N + m / N ≤ (4 * C + 1) * t :=
    opt_arith hC hmge htdef (cutoffScale_ge (by linarith)) (cutoffScale_lt (by linarith))
  have hcube : t ^ 3 = m := by rw [htdef]; exact rpow_third_cube (by linarith)
  have hle : (∫⁻ ω, X ω ∂μ).toReal ≤ (4 * C + 1) * t := le_trans hreal harith
  have hpow : ((∫⁻ ω, X ω ∂μ).toReal) ^ 3 ≤ (((4 * C + 1) * t) ^ 3) :=
    pow_le_pow_left₀ (by positivity) hle 3
  have hm1eq : (∫⁻ ω, X ω ∂μ) = ENNReal.ofReal ((∫⁻ ω, X ω ∂μ).toReal) :=
    (ENNReal.ofReal_toReal hm1fin).symm
  calc (∫⁻ ω, X ω ∂μ) ^ 3
      = (ENNReal.ofReal ((∫⁻ ω, X ω ∂μ).toReal)) ^ 3 := by conv_lhs => rw [hm1eq]
    _ = ENNReal.ofReal (((∫⁻ ω, X ω ∂μ).toReal) ^ 3) := by
        rw [← ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal (((4 * C + 1) * t) ^ 3) := ENNReal.ofReal_le_ofReal hpow
    _ = ENNReal.ofReal (ratioConst C) * m2 := by
        rw [hm2of, ratioConst, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_pow, hcube]

end PercLib.CriticalLRP.Analysis.Route3

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-- **The scale-truncated cited leaf.**  The `n^{-1/2}` cutoff envelope at radius `r`, required only
up to the source's truncation scale `⌈(E_{β_c,r}|K|²)^{2/3}⌉`, with the constant still uniform in
`r`.  Strictly weaker than `CriticalVolumeTail C`
(`criticalVolumeTailUpToScale_of_volumeTail`) and sufficient for the Case-3 moment gap with the same
constant (`cube_cutMoment_le_of_volumeTailUpToScale`). -/
def CriticalVolumeTailUpToScale (C : ℝ) : Prop :=
  ∀ (r : ℝ), 0 < r → ∀ n : ℕ, 1 ≤ n →
    n ≤ Analysis.Route3.cutoffScale (M.cutMoment 2 r).toReal →
      M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ Analysis.Route3.tailEnvelope C n

/-- The cited full leaf implies the truncated one: this is the direction that makes the truncation
a genuine weakening. -/
theorem criticalVolumeTailUpToScale_of_volumeTail {C : ℝ} (h : M.CriticalVolumeTail C) :
    M.CriticalVolumeTailUpToScale C :=
  fun r hr n hn _ => M.cutLaw_tail_le_envelope hr h n hn

/-- **The Case-3 moment gap from the truncated leaf**, with the source's constant `(4C+1)³`. -/
theorem cube_cutMoment_le_of_volumeTailUpToScale {C : ℝ} (hC : 0 ≤ C)
    (hTail : M.CriticalVolumeTailUpToScale C) {r : ℝ} (hr : 0 < r) :
    (M.cutMoment 1 r) ^ 3 ≤ ENNReal.ofReal (Analysis.Route3.ratioConst C) * M.cutMoment 2 r := by
  have hmeas : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) := measurable_clusterVol 0
  have hint : ∀ ω : Config M.V,
      clusterVol ω (0 : M.V) = ⊤ ∨ ∃ m : ℕ, clusterVol ω (0 : M.V) = (m : ℝ≥0∞) :=
    fun ω => PercLib.CriticalLRP.clusterVol_eq_top_or_nat ω (0 : M.V)
  have hX1 : ∀ ω : Config M.V, 1 ≤ clusterVol ω (0 : M.V) :=
    fun ω => PercLib.CriticalLRP.one_le_clusterVol ω (0 : M.V)
  have hkey := Analysis.Route3.cube_lintegral_le_of_tail_trunc (μ := M.cutLaw r)
    (X := fun ω : Config M.V => clusterVol ω (0 : M.V)) hmeas hint hX1 hC
    (fun n hn hntr => hTail r hr n hn hntr)
  simpa [SourceModelData.cutMoment, pow_one] using hkey

/-- The `toReal`/`cutMassAt` form of the truncated-leaf moment gap, matching the shape of
production's `momentGap_of_volumeTail`. -/
theorem momentGap_of_volumeTailUpToScale {C : ℝ} (hC : 0 ≤ C)
    (hTail : M.CriticalVolumeTailUpToScale C) {r : ℝ} (hr : 0 < r)
    (hne : M.cutMoment 2 r ≠ ⊤) :
    (Analysis.Route3.ratioConst C)⁻¹ * (M.cutMassAt r 0).toReal ^ 3
      ≤ (M.cutMoment 2 r).toReal := by
  have hbase := M.cube_cutMoment_le_of_volumeTailUpToScale hC hTail hr
  · have h1fin : M.cutMoment 1 r ≠ ⊤ := by
      rw [M.cutMoment_one_eq_cutMassAt]
      exact ne_top_of_le_ne_top hne (E1Sign.cutMassAt_le_cutMoment_two M r)
    have hreal : (M.cutMoment 1 r).toReal ^ 3
        ≤ Analysis.Route3.ratioConst C * (M.cutMoment 2 r).toReal := by
      have h := (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top h1fin)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne)).mpr hbase
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

/-- **The Case-3 consumer interface, fed by the truncated leaf.**  The conclusion is *literally*
the hypothesis `hgm` of production's `exists_momentGap_of_volumeTail_soon` and of every Case-3
consumer in `CriticalVolumeTail/Main.lean` (`p2ExclError_tendsto_zero_of_polygonBundle`,
`logIntegrable_p2ExclError_of_polygonBundle`, `secondMoment_asymptotic_case3_p21`).  So replacing
the cited full envelope by the truncated one keeps the entire Case-3 chain intact. -/
theorem exists_momentGap_of_volumeTailUpToScale_soon {C : ℝ} (hC : 0 ≤ C) {r₀ : ℝ}
    (hTail : M.CriticalVolumeTailUpToScale C)
    (h2 : ∀ t : ℝ, max 1 r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal := by
  refine ⟨(Analysis.Route3.ratioConst C)⁻¹,
    inv_pos.mpr (Analysis.Route3.ratioConst_pos hC), ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 r₀)] with r hr
  exact M.momentGap_of_volumeTailUpToScale hC hTail
    (lt_of_lt_of_le one_pos (le_trans (le_max_left 1 r₀) hr)) (h2 r hr)

end PercLib.CriticalLRP.Orchestration.SourceModelData


/-! ## §4 The Case-3 moment gap does **not** imply the cited volume tail

The natural hope after reading the source's display is that the Case-3 *conclusion* — the moment
gap `E_{β_c,r}|K|³ ⪯ E_{β_c,r}|K|²` — already contains the cited input `P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}`,
which would make the citation [12, 75] redundant inside Case 3.  It does not, and this section
proves that with an explicit family of integer laws: the gap holds with constant one while the
`n^{-1/2}` envelope constant is arbitrarily large.

The papers's three-way structure is what makes this possible: the gap constrains `(E|K|, E|K|²)`,
which a *rare far* cluster inflates without affecting the tail at the scales where the envelope is
read.  Concretely, on the three-point space `{1, L, M}` with `P(X = 1) = 1 - q - p`,
`P(X = L) = q`, `P(X = M) = p` and `L = A⁶`, `M = A¹²`, `q = A⁻²`, `p = A⁻¹²`:

* `E X = A⁴ + 2 - q - p`, so `(E X)³ ≤ (A⁴+3)³ ≤ A¹² + A¹⁰`;
* `E X² = A¹² + A¹⁰ + 1 - q - p ≥ A¹² + A¹⁰`, so `(E X)³ ≤ E X²` — the gap with constant `1`;
* but `P(X ≥ L) = q + p = A⁻² + A⁻¹²`, so `√L · P(X ≥ L) = A + A⁻⁹ ≥ A`.

The third bullet violates `P(X ≥ n) ≤ C/√n` at `n = L` for every `C < A`.  So the cited leaf is a
genuine extra input, strictly stronger than the Case-3 conclusion, and the transport of the
`n^{-1/2}` exponent cannot be manufactured from the moment gap. -/

namespace PercLib.CriticalLRP.Orchestration

/-- **The moment gap does not give the tail.**  For every `B ≥ 1` there is a probability
distribution on three atoms `{1, L, M}` with `(E X)³ ≤ E X²` (the Case-3 moment gap with constant
one) and with `√L · P(X ≥ L) ≥ B`, i.e. the `n^{-1/2}` envelope constant is at least `B`. -/
theorem exists_momentGap_with_large_tail_envelope (B : ℝ) (hB : 1 ≤ B) :
    ∃ (L M q p : ℝ), 1 < L ∧ L < M ∧ 0 < q ∧ 0 < p ∧ q + p ≤ 1 ∧
      ((1 - q - p) + q * L + p * M) ^ 3
        ≤ (1 - q - p) + q * L ^ 2 + p * M ^ 2 ∧
      B ≤ Real.sqrt L * (q + p) := by
  set A : ℝ := max B 8 with hAdef
  have hA8 : 8 ≤ A := le_max_right B 8
  have hAB : B ≤ A := le_max_left B 8
  have hA0 : 0 < A := by linarith
  have hA1 : 1 < A := by linarith
  set q : ℝ := (A⁻¹) ^ 2 with hqdef
  set p : ℝ := (A⁻¹) ^ 12 with hpdef
  set L : ℝ := A ^ 6 with hLdef
  set M : ℝ := A ^ 12 with hMdef
  have hAinv : A⁻¹ ≤ 1 / 8 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hA8
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hq64 : q ≤ 1 / 64 := by
    rw [hqdef]
    have h8 : A⁻¹ ≤ (8 : ℝ)⁻¹ := by simpa using hAinv
    calc (A⁻¹) ^ 2 ≤ ((8 : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h8 2
      _ = 1 / 64 := by norm_num
  have hp64 : p ≤ 1 / 64 := by
    rw [hpdef]
    have h8 : A⁻¹ ≤ (8 : ℝ)⁻¹ := by simpa using hAinv
    have h8nn : (0 : ℝ) ≤ (8 : ℝ)⁻¹ := by norm_num
    calc (A⁻¹) ^ 12 ≤ ((8 : ℝ)⁻¹) ^ 12 := pow_le_pow_left₀ (by positivity) h8 12
      _ ≤ 1 / 64 := by norm_num
  have hqL : q * L = A ^ 4 := by
    rw [hqdef, hLdef]; field_simp
  have hpM : p * M = 1 := by
    rw [hpdef, hMdef]; field_simp
  have hqL2 : q * L ^ 2 = A ^ 10 := by
    rw [hqdef, hLdef]; field_simp
  have hpM2 : p * M ^ 2 = A ^ 12 := by
    rw [hpdef, hMdef]; field_simp
  -- the moment expressions
  have hm1eq : (1 - q - p) + q * L + p * M = A ^ 4 + 2 - q - p := by rw [hqL, hpM]; ring
  have hm2eq : (1 - q - p) + q * L ^ 2 + p * M ^ 2 = A ^ 12 + A ^ 10 + 1 - q - p := by
    rw [hqL2, hpM2]; ring
  -- `m₁ ≤ A⁴ + 3` and `m₁ ≥ 0`
  have hm1le : (1 - q - p) + q * L + p * M ≤ A ^ 4 + 3 := by
    rw [hm1eq]; linarith [hq0, hp0]
  have hm1nn : (0 : ℝ) ≤ (1 - q - p) + q * L + p * M := by
    rw [hm1eq]
    have : A ^ 4 ≥ 1 := one_le_pow₀ hA1.le
    linarith [hq0, hp0, this]
  -- the arithmetic core: `(A⁴+3)³ ≤ A¹² + A¹⁰`
  have hA2 : (64 : ℝ) ≤ A ^ 2 := by nlinarith
  have hA8one : (1 : ℝ) ≤ A ^ 8 := one_le_pow₀ hA1.le
  have hA4le8 : A ^ 4 ≤ A ^ 8 := by nlinarith
  have hkey : 9 * A ^ 8 + 27 * A ^ 4 + 27 ≤ A ^ 10 := by
    have h1 : 9 * A ^ 8 + 27 * A ^ 4 + 27 ≤ 63 * A ^ 8 := by nlinarith
    have h2 : 63 * A ^ 8 ≤ A ^ 10 := by
      have h3 : (0 : ℝ) < A ^ 8 := by positivity
      have : A ^ 10 = A ^ 2 * A ^ 8 := by ring
      nlinarith
    linarith
  have hexp : (A ^ 4 + 3) ^ 3 = A ^ 12 + 9 * A ^ 8 + 27 * A ^ 4 + 27 := by ring
  have hcube : (A ^ 4 + 3) ^ 3 ≤ A ^ 12 + A ^ 10 := by
    rw [hexp]; linarith
  have hmm : ((1 - q - p) + q * L + p * M) ^ 3
      ≤ (1 - q - p) + q * L ^ 2 + p * M ^ 2 := by
    have hstep : ((1 - q - p) + q * L + p * M) ^ 3 ≤ (A ^ 4 + 3) ^ 3 :=
      pow_le_pow_left₀ hm1nn hm1le 3
    have hnn : (0 : ℝ) ≤ 1 - q - p := by
      have : q + p ≤ 1 := by linarith
      linarith
    rw [hm2eq]
    linarith
  refine ⟨L, M, q, p, ?_, ?_, hq0, hp0, by linarith, hmm, ?_⟩
  · rw [hLdef]; nlinarith [pow_pos hA0 6, hA1]
  · rw [hLdef, hMdef]
    have := pow_pos hA0 6
    nlinarith [pow_pos hA0 6, hA1]
  · -- the envelope violation
    have hsqrt : Real.sqrt L = A ^ 3 := by
      rw [hLdef, show A ^ 6 = (A ^ 3) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hsqrt]
    have hval : A ^ 3 * (q + p) = A + A⁻¹ ^ 9 := by
      rw [hqdef, hpdef]; field_simp
    have hpos : (0 : ℝ) < A⁻¹ ^ 9 := by positivity
    rw [hval]
    linarith

/-- **No constant works.**  For every proposed envelope constant `C` there is a three-atom law
satisfying the Case-3 moment gap with constant one whose `n^{-1/2}` envelope constant exceeds `C`.
So `SourceModelData.CriticalVolumeTail C` is not implied by the Case-3 moment gap for any `C`. -/
theorem exists_momentGap_not_tailEnvelope (C : ℝ) :
    ∃ (L M q p : ℝ), 1 < L ∧ L < M ∧ 0 < q ∧ 0 < p ∧ q + p ≤ 1 ∧
      ((1 - q - p) + q * L + p * M) ^ 3
        ≤ (1 - q - p) + q * L ^ 2 + p * M ^ 2 ∧
      ¬ (Real.sqrt L * (q + p) ≤ C) := by
  obtain ⟨L, M, q, p, h1, h2, h3, h4, h5, hgap, hB⟩ :=
    exists_momentGap_with_large_tail_envelope (max C 1 + 1) (by linarith [le_max_right C 1])
  exact ⟨L, M, q, p, h1, h2, h3, h4, h5, hgap, by intro h; nlinarith [hB, h, le_max_left C 1]⟩

end PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.quarterRoot_eq_sqrt_sqrt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tailEnvelope_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_le_secondMoment_div
#print axioms PercLib.CriticalLRP.Orchestration.sqrt_mul_min_le_quarterRoot
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_le_secondMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_of_uniform_secondMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_of_uniform_secondMoment
#print axioms PercLib.CriticalLRP.Analysis.Route3.sum_filter_head_le_trunc
#print axioms PercLib.CriticalLRP.Analysis.Route3.partialSum_le_trunc
#print axioms PercLib.CriticalLRP.Analysis.Route3.cube_lintegral_le_of_tail_trunc
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.CriticalVolumeTailUpToScale
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTailUpToScale_of_volumeTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cube_cutMoment_le_of_volumeTailUpToScale
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_of_volumeTailUpToScale
#print axioms PercLib.CriticalLRP.Orchestration.exists_momentGap_with_large_tail_envelope
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_momentGap_of_volumeTailUpToScale_soon
#print axioms PercLib.CriticalLRP.Orchestration.exists_momentGap_not_tailEnvelope
