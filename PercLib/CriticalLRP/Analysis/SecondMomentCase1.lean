/-
Integrated and independently rebuilt from accepted Ultramath `smwyue9wx`, member `m1`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwyue9wx`, member `m1`, direction d1.

# Case 1 (d > 3α) of Proposition I.4.15: the second-moment error ratio

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 1:

```
  E_{β_c,r}[|K|³ |K ∩ B_r|] ≤ E_{β_c,r}[|K|⁴] ⪯ (E|K|²)(E|K|)⁴,
  so that   0 ≤ E_{2,r} ⪯ (E|K|)³ / |B_r| ⪯ r^{3α-d}
```

which is logarithmically integrable as soon as `d > 3α`.

The `p = 4`, `k = 1` generalized tree-graph inequality (Lemma I.4.16) is
`TreeExpansion.FivePoint.fourth_moment_free_mixed_le` in this repository; this file

* transfers it to the source cutoff law `M.cutProb r` (`cutMoment_four_mixed_le`),
  using only the shift invariance `E1Sign.cutProb_shift_invariant`, i.e. exactly the
  "root independence at `M.cutProb`" input, and no new tree-graph combinatorics;
* converts the *source* numerator `M.connCubeMass` (through the existing
  `M.connCubeMass_le_fourth` and `M.p2ExclError_le_connCubeMass_div`) into the
  Case-1 ratio `15 (E|K|)³ / |B_r|` (`p2ExclError_le_caseOne`);
* converts `(E|K|)³/|B_r|` into the rate `⪯ r^{3α-d}` using the first-moment
  asymptotic `hP` and the landed lattice-ball lower bound
  `TriangleAverage.eventually_pow_div_ncard_le` (`eventually_p2ExclError_le_rpow`);
* concludes `E_{2,r} → 0` and the logarithmic integrability of `E_{2,r}` when
  `d > 3α` (`p2ExclError_tendsto_zero_of_caseOne`,
  `integrableOn_abs_div_p2ExclError`, `logarithmicallyIntegrable_p2ExclError`).

The only carried (source-shaped) hypotheses are the first-moment asymptotic `hP`,
eventual finiteness of the second cutoff moment `h2`, and — for the packaged
`LogarithmicallyIntegrable` statement only — measurability of `r ↦ E_{2,r}` in the
radius, which is the same residual input isolated for `𝓔_{1,r}` at HEAD.  No
fourth-moment finiteness is assumed: it is *derived* from the mixed bound and the
second moment.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentError.Normalized
public import PercLib.CriticalLRP.Correlation.FourthMoment.Cases
public import PercLib.CriticalLRP.Analysis.TriangleAverage
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.LogIntegrability
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Measurability

/-! # Case 1 of Proposition I.4.15 -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP
namespace CaseOne

open Orchestration

/-! ## 1. The generalized tree-graph inequality at the cutoff law

`FivePoint.fourth_moment_all_k_le` at `k = 1` is Lemma I.4.16 with `p = 4`, `k = 1`:
`E|K|⁴ ≤ 5!! (E|K|²) (E|K|)⁴`.  Its hypothesis is full simultaneous translation
invariance of the edge-open profile, which for the cutoff law is
`E1Sign.cutProb_shift_invariant`.  Transporting along `M.cutLaw r = edgeMeasure
(M.cutProb r)` (`E1Sign.cutLaw_eq`, definitional) gives the bound in the model's own
`cutMoment` vocabulary. -/

/-- **Lemma I.4.16 at `p = 4`, `k = 1`, at the source cutoff law.**
`E_{β_c,r}|K|⁴ ≤ 15 (E_{β_c,r}|K|²) (E_{β_c,r}|K|)⁴`, unconditionally in `ℝ≥0∞`. -/
theorem cutMoment_four_mixed_le (M : SourceModelData) (r : ℝ) :
    M.cutMoment 4 r ≤ 15 * M.cutMoment 2 r * (M.cutMoment 1 r) ^ 4 := by
  have hq : ∀ x y g : M.V, M.cutProb r s(x + g, y + g) = M.cutProb r s(x, y) := by
    intro x y g
    simpa only [Sym2.map_mk] using E1Sign.cutProb_shift_invariant M r g s(x, y)
  have h := TreeExpansion.FivePoint.fourth_moment_all_k_le (M.cutProb r) hq 1 (by norm_num)
  rw [SourceModelData.cutMoment, SourceModelData.cutMoment, SourceModelData.cutMoment,
    E1Sign.cutLaw_eq]
  simp_rw [clusterVol, ← Percolation.cardFun_eq_encard]
  simpa only [pow_one] using h

/-- **Case 1 needs no fourth-moment hypothesis**: the mixed bound turns finiteness of
the second cutoff moment into finiteness of the fourth. -/
theorem cutMoment_four_ne_top_of_two (M : SourceModelData) {r : ℝ}
    (h2 : M.cutMoment 2 r ≠ ⊤) : M.cutMoment 4 r ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (cutMoment_four_mixed_le M r)
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h2) (ENNReal.pow_ne_top h1)

/-! ## 2. The Case-1 ratio `E_{2,r} ≤ 15 (E|K|)³ / |B_r|`

The existing `M.p2ExclError_le_fourth_div` puts `E_{2,r}` below
`E|K|⁴ / (|B_r| E|K| E|K|²)`; cancelling `E|K|²` against the mixed bound leaves
`15 (E|K|)³/|B_r|`.  The `(E|K|)²` factor cancels *exactly*, which is what makes the
exponent `3` in the Case-1 rate, not only a bounded ratio. -/

/-- The window denominator `|B_r| E|K| E|K|²` is positive in `ℝ` as soon as the two
moments are finite and `0 ≤ r`. -/
theorem window_den_pos (M : SourceModelData) {r : ℝ} (hr : 0 ≤ r)
    (h2 : M.cutMoment 2 r ≠ ⊤) :
    (0 : ℝ) < ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast SourceModelData.ball_ncard_pos M r hr
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := SourceModelData.one_le_cutMoment_one_toReal M r h1
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := SourceModelData.one_le_cutMoment_two_toReal M r h2
    linarith
  positivity

/-- **The Case-1 ratio of (I.4.16)**: `E_{2,r} ≤ 15 (E_{β_c,r}|K|)³ / |B_r|`.

This is the paper's `E_{2,r} ⪯ (E|K|)³/|B_r|` with the explicit constant `5!! = 15`
and no conversion loss: the numerator `E[|K|³ #(K ∩ B_r)]` enters only through the
already-proved `≤ E|K|⁴` (`M.connCubeMass_le_fourth`) inside
`M.p2ExclError_le_fourth_div`. -/
theorem p2ExclError_le_caseOne (M : SourceModelData) {r : ℝ} (hr : 0 ≤ r)
    (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.p2ExclError r ≤ 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ) := by
  have h4 : M.cutMoment 4 r ≠ ⊤ := cutMoment_four_ne_top_of_two M h2
  refine (M.p2ExclError_le_fourth_div r hr h2 h4).trans ?_
  have h4le : (M.cutMoment 4 r).toReal
      ≤ 15 * (M.cutMoment 2 r).toReal * (M.cutMoment 1 r).toReal ^ 4 := by
    have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
    have hfin : 15 * M.cutMoment 2 r * (M.cutMoment 1 r) ^ 4 ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h2) (ENNReal.pow_ne_top h1)
    have h := ENNReal.toReal_mono hfin (cutMoment_four_mixed_le M r)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow] at h
    simpa only [ENNReal.toReal_ofNat] using h
  have hden := window_den_pos M hr h2
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast SourceModelData.ball_ncard_pos M r hr
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := SourceModelData.one_le_cutMoment_one_toReal M r h1
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := SourceModelData.one_le_cutMoment_two_toReal M r h2
    linarith
  refine (div_le_iff₀ hden).mpr ?_
  have hid : 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
        * (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal)
      = 15 * (M.cutMoment 2 r).toReal * (M.cutMoment 1 r).toReal ^ 4 := by
    field_simp
  rw [hid]
  exact h4le

/-! ## 3. From the ratio to the rate `r^{3α-d}`

Two inputs are consumed here, both already on disk elsewhere:

* the first-moment asymptotic `hP` (`E_{β_c,r}|K| ~ (α/β_c) r^α`, the accepted
  `Analysis/MomentRegularVariation.lean` input), which turns the numerator
  `(E|K|)³` into `⪯ r^{3α}`;
* the landed lattice-ball **lower** sandwich `TriangleAverage.eventually_pow_div_ncard_le`,
  `r^d/|B_r| ≤ 2^d`, which turns the window `1/|B_r|` into `⪯ r^{-d}`.

Together they give `(E|K|)³/|B_r| ⪯ r^{3α-d}`, i.e. the paper's Case-1 rate. -/

/-- **The Case-1 window ratio `(E|K|)³/|B_r|` is `⪯ r^{3α-d}`.**

This is the purely analytic half of Case 1: it uses only the first-moment asymptotic `hP`
(for `E|K| ⪯ r^α`) and the lattice-ball lower sandwich `r^d/|B_r| ≤ 2^d`.  It is stated
separately from any moment/finiteness input so that *every* numerator bounded by
`15 (E|K|)³/|B_r|` — the source numerator `E[|K|³#(K ∩ B_r)]` and the error `E_{2,r}`
alike — inherits the rate `r^{3α-d}`. -/
theorem eventually_window_ratio_le_rpow (M : SourceModelData)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∀ᶠ r : ℝ in atTop, 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
      ≤ 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
  have hrpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  have hm1 : ∀ᶠ r : ℝ in atTop,
      (M.cutMoment 1 r).toReal ≤ 2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α := by
    have hlt : ∀ᶠ r : ℝ in atTop,
        (M.cutMassAt r 0).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) < 2 :=
      (tendsto_order.1 hP).2 2 (by norm_num)
    filter_upwards [hlt, hrpos] with r hr hrr
    have hpos : (0 : ℝ) < (M.α / (M.betaCrit : ℝ)) * r ^ M.α :=
      mul_pos hκ (Real.rpow_pos_of_pos hrr M.α)
    rw [SourceModelData.cutMassAt_zero_eq_cutMoment] at hr
    rw [div_lt_iff₀ hpos] at hr
    linarith
  have hball := TriangleAverage.eventually_pow_div_ncard_le M
  filter_upwards [hm1, hball, hrpos] with r hm1r hballr hr
  have hbpos : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast SourceModelData.ball_ncard_pos M r hr.le
  have hpow : (0 : ℝ) < r ^ (3 * M.α - M.d) := Real.rpow_pos_of_pos hr _
  have hcube : (M.cutMoment 1 r).toReal ^ 3
      ≤ (2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α) ^ 3 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg hm1r 3
  have hstep : 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
      ≤ 15 * (2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α) ^ 3
        / ((M.ball r).ncard : ℝ) := by
    have h1 : (0 : ℝ) ≤ 15 * (M.cutMoment 1 r).toReal ^ 3 := by positivity
    have h2' : (0 : ℝ) ≤ 15 * (2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α) ^ 3 := by positivity
    exact div_le_div_of_nonneg_right (by linarith) hbpos.le
  have hrpow3 : (r ^ M.α) ^ 3 = r ^ (3 * M.α) := by
    rw [← Real.rpow_natCast (r ^ M.α) 3, ← Real.rpow_mul hr.le]
    push_cast
    ring_nf
  have hid : 15 * (2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α) ^ 3 / ((M.ball r).ncard : ℝ)
      = 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)) := by
    rw [mul_pow, hrpow3]
    field_simp
    ring_nf
  have hrate : r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)
      ≤ (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
    have hsplit : r ^ (3 * M.α) = r ^ (3 * M.α - M.d) * r ^ M.d := by
      rw [← Real.rpow_natCast r M.d, ← Real.rpow_add hr,
        show 3 * M.α - (M.d : ℝ) + (M.d : ℝ) = 3 * M.α by ring]
    calc r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)
        = r ^ (3 * M.α - M.d) * (r ^ M.d / ((M.ball r).ncard : ℝ)) := by
          rw [hsplit]
          field_simp
      _ ≤ r ^ (3 * M.α - M.d) * (2 : ℝ) ^ M.d :=
          mul_le_mul_of_nonneg_left hballr hpow.le
      _ = (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by ring
  calc 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
      ≤ 15 * (2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α) ^ 3 / ((M.ball r).ncard : ℝ) := hstep
    _ = 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3
          * (r ^ (3 * M.α) / ((M.ball r).ncard : ℝ)) := hid
    _ ≤ 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * ((2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d)) := by
        refine mul_le_mul_of_nonneg_left hrate ?_
        positivity
    _ = 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
        ring_nf

/-- **The Case-1 rate for the excluded second-moment error.**  Under the first-moment
asymptotic `hP` and eventual finiteness of the second cutoff moment,

`E_{2,r} ≤ 15 · 8 · (α/β_c)³ · 2^d · r^{3α-d}` eventually,

with every constant explicit.  No bound on `E|K|⁴` or `E|K|²` beyond `hP` and the ball
count is used. -/
theorem eventually_p2ExclError_le_rpow (M : SourceModelData)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d) := by
  filter_upwards [eventually_window_ratio_le_rpow M hκ hP, eventually_ge_atTop (0 : ℝ), h2]
    with r hw hr h2r
  exact (p2ExclError_le_caseOne M hr h2r).trans hw

/-- **The source numerator ratio in Case 1.**  `E[|K|³ #(K ∩ B_r)] ≤ E|K|⁴` and the mixed
`p = 4`, `k = 1` bound give

`E[|K|³ #(K ∩ B_r)] / (|B_r| E|K| E|K|²) ≤ 15 (E|K|)³ / |B_r|`,

i.e. exactly the right-hand side of (I.4.16) bounded by the Case-1 quantity, with the
`(E|K|)²` factor cancelled exactly rather than merely bounded. -/
theorem connCubeMass_ratio_le_caseOne (M : SourceModelData) {r : ℝ} (hr : 0 ≤ r)
    (h2 : M.cutMoment 2 r ≠ ⊤) :
    (M.connCubeMass r).toReal
        / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal)
      ≤ 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ) := by
  have h4 : M.cutMoment 4 r ≠ ⊤ := cutMoment_four_ne_top_of_two M h2
  have hc : (M.connCubeMass r).toReal ≤ (M.cutMoment 4 r).toReal :=
    ENNReal.toReal_mono h4 (SourceModelData.connCubeMass_le_fourth M r)
  have h4le : (M.cutMoment 4 r).toReal
      ≤ 15 * (M.cutMoment 2 r).toReal * (M.cutMoment 1 r).toReal ^ 4 := by
    have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
    have hfin : 15 * M.cutMoment 2 r * (M.cutMoment 1 r) ^ 4 ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h2) (ENNReal.pow_ne_top h1)
    have h := ENNReal.toReal_mono hfin (cutMoment_four_mixed_le M r)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow] at h
    simpa only [ENNReal.toReal_ofNat] using h
  have hden : (0 : ℝ) < ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
      * (M.cutMoment 2 r).toReal :=
    window_den_pos M hr h2
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast SourceModelData.ball_ncard_pos M r hr
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := SourceModelData.one_le_cutMoment_one_toReal M r h1
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := SourceModelData.one_le_cutMoment_two_toReal M r h2
    linarith
  refine (div_le_iff₀ hden).mpr ?_
  have hid : 15 * (M.cutMoment 1 r).toReal ^ 3 / ((M.ball r).ncard : ℝ)
        * (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal)
      = 15 * (M.cutMoment 2 r).toReal * (M.cutMoment 1 r).toReal ^ 4 := by
    field_simp
  rw [hid]
  exact hc.trans h4le

/-- **Vanishing of the source numerator ratio in Case 1**: the exact `hratio` hypothesis of
`SourceModelData.regularlyVarying_two_reduced` / `regularlyVarying_two_of_connCubeRatio`,
discharged from `d > 3α`, the first-moment asymptotic and second-moment finiteness. -/
theorem connCubeMass_ratio_tendsto_zero_of_caseOne (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    Tendsto (fun r : ℝ => (M.connCubeMass r).toReal
      / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun r : ℝ =>
      15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d))
      atTop (𝓝 0) := by
    have h := (TriangleAverage.tendsto_rpow_neg_atTop_zero
      (a := 3 * M.α - M.d) (by linarith)).const_mul
      (15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d)
    simpa only [mul_zero] using h
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [h2, eventually_ge_atTop (0 : ℝ)] with r h2r hr
    exact div_nonneg ENNReal.toReal_nonneg (window_den_pos M hr h2r).le
  · filter_upwards [eventually_window_ratio_le_rpow M hκ hP, h2, eventually_ge_atTop (0 : ℝ)]
      with r hw h2r hr
    exact (connCubeMass_ratio_le_caseOne M hr h2r).trans hw

/-! ## 4. Case 1: `E_{2,r} → 0` -/

/-- **`E_{2,r} → 0` under the Case-1 hypothesis `d > 3α`** (`h3α`), from the ratio bound
and the first-moment asymptotic.  This is the paper's `lim_{r→∞} E_{2,r} = 0` in Case 1,
with the mixed `p = 4`, `k = 1` tree-graph inequality as the only moment input. -/
theorem p2ExclError_tendsto_zero_of_caseOne (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hg : Tendsto (fun r : ℝ =>
      15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d * r ^ (3 * M.α - M.d))
      atTop (𝓝 0) := by
    have h := (TriangleAverage.tendsto_rpow_neg_atTop_zero
      (a := 3 * M.α - M.d) (by linarith)).const_mul
      (15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d)
    simpa only [mul_zero] using h
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (0 : ℝ), h2] with r hr h2r
    exact SourceModelData.p2ExclError_nonneg M r hr h2r
  · exact eventually_p2ExclError_le_rpow M hκ hP h2

/-! ## 5. Case 1: logarithmic integrability of `E_{2,r}`

`∫^∞ |E_{2,r}| dr/r ⪯ ∫^∞ r^{3α-d-1} dr < ∞` since `3α - d < 0`.  The `|E_{2,r}|` is
removed by nonnegativity (`p2ExclError_nonneg`), so no absolute-value measurability input
is needed beyond measurability of `E_{2,r}` itself in the radius. -/

/-- **The logarithmic integral of `E_{2,r}` is finite in Case 1.** -/
theorem integrableOn_abs_div_p2ExclError (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hmeas : Measurable M.p2ExclError) :
    ∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r => |M.p2ExclError r| / r) (Ioi R) := by
  have hb : ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ 15 * 8 * (M.α / (M.betaCrit : ℝ)) ^ 3 * (2 : ℝ) ^ M.d
        * r ^ (-((M.d : ℝ) - 3 * M.α)) := by
    filter_upwards [eventually_p2ExclError_le_rpow M hκ hP h2] with r hr
    simpa only [neg_sub] using hr
  have hnn : ∀ᶠ r : ℝ in atTop, 0 ≤ M.p2ExclError r := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), h2] with r hr h2r
    exact SourceModelData.p2ExclError_nonneg M r hr h2r
  exact Analysis.integrableOn_abs_div_of_eventually_le_rpow_neg hmeas (by linarith) hnn hb

/-- **Case 1: `E_{2,r}` is a logarithmically integrable error function.**  This is the
`∫^∞ E_{2,r} dr/r < ∞` of the paper's Case 1; it is the input `tendsto_div_two` consumes
through `Ē_{2,r}`.  The measurability of `r ↦ E_{2,r}` is the single residual
radius-regularity input, exactly as for `𝓔_{1,r}` at HEAD. -/
theorem logarithmicallyIntegrable_p2ExclError (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hmeas : Measurable M.p2ExclError) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError :=
  ⟨hmeas, integrableOn_abs_div_p2ExclError M h3α hκ hP h2 hmeas⟩

/-! ## 6. Case 1: logarithmic integrability of the normalized error `Ē_{2,r}`

`1 − Ē_{2,r} = (1 − E_{2,r})(1 + H_r)(1 − E_{0,r})`, so `Ē_{2,r}` is the polynomial
`(E0 − H + H E0) + E2 (1 + H − E0 − H E0)` in the three source errors.  Once each of them
is bounded by `1` and log-integrable, so is `Ē_{2,r}`: the boundedness supplies the
coefficient, the log-integrability the integrand.  `E_{2,r}`'s log-integrability is
Case 1's content (section 5); `H_r`'s and `E_{0,r}`'s are the paper's Lemma I.4.6 /
Proposition I.4.2 inputs and are carried visibly. -/

/-- **Log-integrable functions are closed under pointwise absolute value.** -/
theorem logIntegrable_abs {h : ℝ → ℝ} (hh : Analysis.LogarithmicallyIntegrable h) :
    Analysis.LogarithmicallyIntegrable (fun r => |h r|) :=
  VolumeMoments.FirstMoment.logIntegrable_mono hh.1.abs hh (fun r _ => by rw [abs_abs])

/-- **Domination on a tail by a log-integrable function.** -/
theorem logIntegrable_of_eventually_abs_le {T g : ℝ → ℝ} (hmeasT : Measurable T)
    (hg : Analysis.LogarithmicallyIntegrable g)
    (hle : ∀ᶠ r : ℝ in atTop, |T r| ≤ |g r|) :
    Analysis.LogarithmicallyIntegrable T := by
  obtain ⟨_, r₀, hr₀, hint⟩ := hg
  obtain ⟨R, hR⟩ := eventually_atTop.1 hle
  refine ⟨hmeasT, max r₀ (max R 1), lt_max_of_lt_left hr₀, ?_⟩
  have hsub : Set.Ioi (max r₀ (max R 1)) ⊆ Set.Ioi r₀ :=
    Set.Ioi_subset_Ioi (le_max_left _ _)
  have hRle : R ≤ max r₀ (max R 1) :=
    le_trans (le_max_left R 1) (le_max_right r₀ (max R 1))
  refine Integrable.mono (hint.mono_set hsub)
    (Measurable.aestronglyMeasurable (hmeasT.abs.div measurable_id)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans (lt_max_of_lt_left hr₀) hx
  have hxR : R ≤ x := le_trans hRle hx.le
  have hleft : ‖|T x| / x‖ = |T x| / x := by
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hx0]
  have hright : ‖|g x| / x‖ = |g x| / x := by
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hx0]
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right (hR x hxR) hx0.le

/-- **The polynomial bound behind `Ē_{2,r}`**: if the two *defect* errors `b = H_r`,
`c = E_{0,r}` are at most `1` in absolute value then
`|1 − (1−a)(1+b)(1−c)| ≤ 4 (|a| + |b| + |c|)`, with no hypothesis on `a` beyond that it
appears linearly.  In particular `Ē_{2,r}` inherits any decay of `E_{2,r}` up to the
bounded factor `4`. -/
theorem abs_one_sub_mul_le (a b c : ℝ) (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |1 - (1 - a) * (1 + b) * (1 - c)| ≤ 4 * (|a| + |b| + |c|) := by
  have hkey : 1 - (1 - a) * (1 + b) * (1 - c)
      = (c - b + b * c) + a * (1 - c + b - b * c) := by ring
  have hbc2 : |b| * |c| ≤ |b| := by nlinarith [abs_nonneg b, abs_nonneg c, hc]
  have ht : |(1 : ℝ) - c| ≤ 2 := by
    have h := abs_sub (1 : ℝ) c
    rw [abs_one] at h
    linarith
  have ht' : |1 - c + b| ≤ 3 := by
    have h := abs_add_le (1 - c) b
    linarith [abs_nonneg (1 - c)]
  have hbc1 : |b * c| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg b, abs_nonneg c, hb]
  have ht'' : |1 - c + b - b * c| ≤ 4 := by
    have h : |1 - c + b - b * c| ≤ |1 - c + b| + |b * c| := by
      have h0 := abs_add_le (1 - c + b) (-(b * c))
      simpa only [sub_eq_add_neg, abs_neg] using h0
    linarith
  have h1 : |c - b + b * c| ≤ |b| + 2 * |c| := by
    have h := abs_add_le (c - b) (b * c)
    rw [abs_mul] at h
    have h' : |c - b| ≤ |b| + |c| := by
      have h2 := abs_sub c b
      linarith
    have hbc3 : |b| * |c| ≤ |c| := by nlinarith [abs_nonneg c, hb]
    linarith
  have hstep1 : |(c - b + b * c) + a * (1 - c + b - b * c)|
      ≤ |c - b + b * c| + |a| * |1 - c + b - b * c| := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul]
  have hstep2 : |a| * |1 - c + b - b * c| ≤ 4 * |a| := by
    nlinarith [ht'', abs_nonneg a]
  have hstep3 : |b| + 2 * |c| + 4 * |a| ≤ 4 * (|a| + |b| + |c|) := by
    nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
  rw [hkey]
  linarith [hstep1, h1, hstep2, hstep3]

/-- **Case 1: `Ē_{2,r}` is logarithmically integrable.**  All three source errors are
bounded by `1` eventually (they tend to `0`), so the polynomial identity for `Ē_{2,r}`
turns log-integrability of the three errors into log-integrability of `Ē_{2,r}`. -/
theorem logIntegrable_p2Ebar (M : SourceModelData)
    (hE2log : Analysis.LogarithmicallyIntegrable M.p2ExclError)
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H)
    (hE0log : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0))
    (hmeasEbar : Measurable M.p2Ebar) :
    Analysis.LogarithmicallyIntegrable M.p2Ebar := by
  have hbdd : ∀ᶠ r : ℝ in atTop, |M.p2ExclError r| ≤ 1 ∧ |M.p2H r| ≤ 1
      ∧ |PivotFlux.cutE0 M r| ≤ 1 := by
    have h1 : ∀ᶠ r : ℝ in atTop, |M.p2ExclError r| ≤ 1 := by
      have := hE2.norm.eventually (eventually_le_nhds (show ‖(0 : ℝ)‖ < 1 by norm_num))
      simpa only [Real.norm_eq_abs] using this
    have h2 : ∀ᶠ r : ℝ in atTop, |M.p2H r| ≤ 1 := by
      have := hH.norm.eventually (eventually_le_nhds (show ‖(0 : ℝ)‖ < 1 by norm_num))
      simpa only [Real.norm_eq_abs] using this
    have h3 : ∀ᶠ r : ℝ in atTop, |PivotFlux.cutE0 M r| ≤ 1 := by
      have := hE0.norm.eventually (eventually_le_nhds (show ‖(0 : ℝ)‖ < 1 by norm_num))
      simpa only [Real.norm_eq_abs] using this
    filter_upwards [h1, h2, h3] with r h1r h2r h3r
    exact ⟨h1r, h2r, h3r⟩
  have hg : Analysis.LogarithmicallyIntegrable (fun r : ℝ =>
      4 * (|M.p2ExclError r| + |M.p2H r| + |PivotFlux.cutE0 M r|)) := by
    have h1 := VolumeMoments.FirstMoment.logIntegrable_add (logIntegrable_abs hE2log)
      (logIntegrable_abs hHlog)
    have h2 := VolumeMoments.FirstMoment.logIntegrable_add h1 (logIntegrable_abs hE0log)
    exact VolumeMoments.FirstMoment.logIntegrable_const_mul 4 h2
  refine logIntegrable_of_eventually_abs_le hmeasEbar hg ?_
  filter_upwards [hbdd] with r ⟨h1r, h2r, h3r⟩
  have h := abs_one_sub_mul_le (M.p2ExclError r) (M.p2H r) (PivotFlux.cutE0 M r) h2r h3r
  have heq : (1 : ℝ) - (1 - M.p2ExclError r) * (1 + M.p2H r) * (1 - PivotFlux.cutE0 M r)
      = M.p2Ebar r := by
    rw [← M.one_sub_p2Ebar r]; ring
  rw [heq] at h
  have hR : |4 * (|M.p2ExclError r| + |M.p2H r| + |PivotFlux.cutE0 M r|)|
      = 4 * (|M.p2ExclError r| + |M.p2H r| + |PivotFlux.cutE0 M r|) := by
    rw [abs_of_nonneg]
    positivity
  rw [hR]
  exact h


/-! ## 7. Assembling Case 1: the `d > 3α` refinement of Proposition I.4.15

With `E_{2,r} → 0` and `Ē_{2,r}` logarithmically integrable discharged by sections 4–6, the
accepted closure `SourceModelData.tendsto_div_two` (`Analysis/SecondMomentError/Normalized.lean`)
gives `E_{β_c,r}|K|² ~ A r^{3α}`, and `regularlyVarying_two` gives regular variation of index
`3α`.  The radial regularity of `r ↦ E_{β_c,r}|K|²` (`hac`, `hae`), the measurability of the
derivative value (`hmR`), the tail finiteness `h1`, `h2` and the first-moment asymptotic `hP`
are all carried explicitly, unweakened. -/

/-- **Case 1 of Proposition I.4.15: `E_{β_c,r}|K|² ~ A r^{3α}` when `d > 3α`.** -/
theorem tendsto_div_two_of_caseOne (M : SourceModelData) (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H)
    (hE0log : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have h2fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤ :=
    (eventually_ge_atTop r₀).mono fun r hr => h2 r hr
  have hE2 : Tendsto M.p2ExclError atTop (𝓝 0) :=
    p2ExclError_tendsto_zero_of_caseOne M h3α hκ hP h2fin
  have hE2log : Analysis.LogarithmicallyIntegrable M.p2ExclError :=
    logarithmicallyIntegrable_p2ExclError M h3α hκ hP h2fin hmeasE2
  have hlog : Analysis.LogarithmicallyIntegrable M.p2Ebar :=
    logIntegrable_p2Ebar M hE2log hHlog hE0log hE2
      (M.p2H_tendsto_zero_of_hP hP) (PivotFlux.tendsto_cutE0 M) hmeasEbar
  exact M.tendsto_div_two_of_hP hα hr₀ hβ hac hae h1 h2 hP hE2 hlog

/-- **Case 1 of Proposition I.4.15: regular variation of index `3α` when `d > 3α`.**
Same inputs as `tendsto_div_two_of_caseOne`, plus measurability of the derivative value;
this is the first clause of the proposition, which does not need the logarithmic integral. -/
theorem regularlyVarying_two_of_caseOne (M : SourceModelData) (hα : 0 < M.α) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  have h2fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤ :=
    (eventually_ge_atTop r₀).mono fun r hr => h2 r hr
  exact M.regularlyVarying_two_of_hP_of_ae_deriv hα hr₀ hβ hac hmR hae h1 h2 hP
    (p2ExclError_tendsto_zero_of_caseOne M h3α hκ hP h2fin)

/-- **Case 1: `Ē_{2,r} → 0`.**  Combines the Case-1 vanishing of `E_{2,r}` with the two
discharged source inputs `H_r → 0` (from `hP`) and `E_{0,r} → 0`
(`PivotFlux.tendsto_cutE0`) through the existing `M.p2Ebar_tendsto_zero`. -/
theorem p2Ebar_tendsto_zero_of_caseOne (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    Tendsto M.p2Ebar atTop (𝓝 0) :=
  M.p2Ebar_tendsto_zero (p2ExclError_tendsto_zero_of_caseOne M h3α hκ hP h2)
    (M.p2H_tendsto_zero_of_hP hP) (PivotFlux.tendsto_cutE0 M)

/-- **Case 1 through the paper's own interface.**  The accepted
`SourceModelData.regularlyVarying_two_reduced` consumes the vanishing of the *right-hand
side of (I.4.16)*, `hratio`, together with finiteness of `M.connCubeMass`.  Both are
discharged here from `d > 3α`, `hP` and second-moment finiteness alone — no fourth-moment
hypothesis, no new error term.  The conclusion is second-moment regular variation of index
`3α`. -/
theorem regularlyVarying_two_of_connCubeRatio_of_caseOne (M : SourceModelData)
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  have h2fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤ :=
    (eventually_ge_atTop r₀).mono fun r hr => h2 r hr
  have hc : ∀ᶠ r : ℝ in atTop, M.connCubeMass r ≠ ⊤ := h2fin.mono fun r hr =>
    ne_top_of_le_ne_top (cutMoment_four_ne_top_of_two M hr)
      (SourceModelData.connCubeMass_le_fourth M r)
  exact M.regularlyVarying_two_reduced hα hr₀ hβ hac hmR hae h1 h2 hP hc
    (connCubeMass_ratio_tendsto_zero_of_caseOne M h3α hκ hP h2fin)

/-! ## 8. Bonus: log-integrability of `E_{0,r}` from the kernel's own error profile

The paper's Lemma I.4.6 supplies both `E_{0,r} → 0` and the log-integrability of `E_{0,r}`.
The vanishing is already discharged (`PivotFlux.tendsto_cutE0`); here the log-integrability is
*derived*, so that `logIntegrable_p2Ebar` needs only `H_r`'s log-integrability as an external
input.

`1 − E_{0,r} = |J'(r)| · |B_r| · r^{α+1}` and the source kernel satisfies
`|J'(r)| = (1 + δ_r) r^{-d-α-1}` with `δ` a logarithmically integrable error function
(`M.exists_error`).  Hence, with `m_r := |B_r| r^{-d}`,
`E_{0,r} = (1 − m_r) − δ_r m_r`, and everything reduces to `|1 − m_r| ⪯ 1/r`, which is the
two-sided lattice-ball sandwich `(r−C)^d ≤ |B_r| ≤ (r+C)^d` at `x = C/r`: for `0 ≤ x ≤ 1`,
`(1−x)^n ≥ 1 − (2^n−1) x` and `(1+x)^n ≤ 1 + (2^n−1) x`. -/

/-- For `0 ≤ x ≤ 1`: `(1 + x)^n ≤ 1 + (2^n − 1) x`. -/
theorem pow_one_add_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ n ≤ 1 + (2 ^ n - 1) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hx2 : x ^ 2 ≤ x := by nlinarith
    have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    calc (1 + x) ^ (n + 1) = (1 + x) ^ n * (1 + x) := by ring
      _ ≤ (1 + (2 ^ n - 1) * x) * (1 + x) := mul_le_mul_of_nonneg_right ih (by linarith)
      _ = 1 + (2 ^ n - 1) * x + x + (2 ^ n - 1) * x ^ 2 := by ring
      _ ≤ 1 + (2 ^ (n + 1) - 1) * x := by
          have h2 : (0 : ℝ) ≤ 2 ^ n - 1 := by linarith
          have hx2' : (2 ^ n - 1) * x ^ 2 ≤ (2 ^ n - 1) * x := by nlinarith
          nlinarith [hx2', hpow, hx0]

/-- For `0 ≤ x ≤ 1`: `1 − (2^n − 1) x ≤ (1 − x)^n`. -/
theorem pow_one_sub_ge (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (2 ^ n - 1) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    calc 1 - (2 ^ (n + 1) - 1) * x
        ≤ (1 - (2 ^ n - 1) * x) * (1 - x) := by
          have h2 : (0 : ℝ) ≤ 2 ^ n - 1 := by linarith
          have hexp : (1 - (2 ^ n - 1) * x) * (1 - x)
              = 1 - (2 ^ n - 1) * x - x + (2 ^ n - 1) * x ^ 2 := by ring
          have hx2 : (0 : ℝ) ≤ (2 ^ n - 1) * x ^ 2 := by positivity
          rw [hexp, hpow]
          nlinarith
      _ ≤ (1 - x) ^ n * (1 - x) := mul_le_mul_of_nonneg_right ih (by linarith)
      _ = (1 - x) ^ (n + 1) := by ring

/-- **The lattice-ball count is `r^d` up to `O(1/r)` relative error.**  From the two-sided
sandwich `(r−C)^d ≤ |B_r| ≤ (r+C)^d` with `x = C/r`. -/
theorem eventually_abs_ncard_mul_rpow_sub_one_le (M : SourceModelData) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in atTop,
      |((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)) - 1| ≤ K / r := by
  obtain ⟨C, hC⟩ := BallAverage.exists_cube_bound M
  have hC0 : 0 ≤ C := BallAverage.cube_bound_nonneg M hC
  refine ⟨(2 ^ M.d - 1) * C, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ 2 ^ M.d := one_le_pow₀ (by norm_num)
    nlinarith
  filter_upwards [eventually_gt_atTop (max C 1)] with r hr
  have hCr : C < r := lt_of_le_of_lt (le_max_left C 1) hr
  have h1r : (1 : ℝ) < r := lt_of_le_of_lt (le_max_right C 1) hr
  have hr0 : (0 : ℝ) < r := lt_trans one_pos h1r
  have hx0 : 0 ≤ C / r := div_nonneg hC0 hr0.le
  have hx1 : C / r ≤ 1 := by
    rw [div_le_one hr0]; exact hCr.le
  have hle := BallAverage.ball_ncard_le M hC hC0 hCr
  have hge := BallAverage.ball_ncard_ge M hC hC0 hCr
  have hrd : (0 : ℝ) < r ^ M.d := pow_pos hr0 M.d
  have hinv : r ^ (-(M.d : ℝ)) = (r ^ M.d)⁻¹ := by
    rw [Real.rpow_neg hr0.le, Real.rpow_natCast]
  have hsplit : (r + C) ^ M.d = r ^ M.d * (1 + C / r) ^ M.d := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hup : ((M.ball r).ncard : ℝ) / r ^ M.d ≤ (1 + C / r) ^ M.d := by
    rw [div_le_iff₀ hrd]
    calc ((M.ball r).ncard : ℝ) ≤ (r + C) ^ M.d := hle
      _ = r ^ M.d * (1 + C / r) ^ M.d := hsplit
      _ = (1 + C / r) ^ M.d * r ^ M.d := by ring
  have hdn : (1 - C / r) ^ M.d ≤ ((M.ball r).ncard : ℝ) / r ^ M.d := by
    rw [le_div_iff₀ hrd]
    calc (1 - C / r) ^ M.d * r ^ M.d = (r - C) ^ M.d := by
          rw [← mul_pow]
          congr 1
          field_simp
      _ ≤ ((M.ball r).ncard : ℝ) := hge
  have hup' : ((M.ball r).ncard : ℝ) / r ^ M.d ≤ 1 + (2 ^ M.d - 1) * (C / r) :=
    hup.trans (pow_one_add_le M.d hx0 hx1)
  have hdn' : 1 - (2 ^ M.d - 1) * (C / r) ≤ ((M.ball r).ncard : ℝ) / r ^ M.d :=
    (pow_one_sub_ge M.d hx0 hx1).trans hdn
  rw [hinv, ← div_eq_mul_inv, abs_sub_le_iff]
  have hK : (2 ^ M.d - 1) * (C / r) = (2 ^ M.d - 1) * C / r := by ring
  constructor <;> linarith [hdn', hup', hK]

/-- **`E_{0,r}` is logarithmically integrable**, from the model's own kernel error profile
`M.exists_error` and the lattice-ball sandwich.  This is the Lemma I.4.6 clause that
`logIntegrable_p2Ebar` consumes. -/
theorem logIntegrable_cutE0 (M : SourceModelData) :
    Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M) := by
  obtain ⟨δ, hδeq, hδlog, -⟩ := M.exists_error
  obtain ⟨K, hK0, hK⟩ := eventually_abs_ncard_mul_rpow_sub_one_le M
  have hδabs : Analysis.LogarithmicallyIntegrable (fun r => |δ r|) := logIntegrable_abs hδlog
  have hδbdd : Analysis.LogarithmicallyIntegrable (fun r => (1 + K) * |δ r|) :=
    VolumeMoments.FirstMoment.logIntegrable_const_mul (1 + K) hδabs
  have hinv : Analysis.LogarithmicallyIntegrable (fun r : ℝ => K * r ^ (-(1 : ℝ))) :=
    (Analysis.isLogErrorFunction_const_rpow_neg (a := 1) (r₀ := 1) one_pos one_pos).1
  have hmaj : Analysis.LogarithmicallyIntegrable
      (fun r => K * r ^ (-(1 : ℝ)) + (1 + K) * |δ r|) :=
    VolumeMoments.FirstMoment.logIntegrable_add hinv hδbdd
  refine logIntegrable_of_eventually_abs_le (I420Case3.measurable_cutE0 M) hmaj ?_
  filter_upwards [hK, eventually_gt_atTop (1 : ℝ)] with r hr h1r
  have hr0 : (0 : ℝ) < r := lt_trans one_pos h1r
  have hmpos : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)) := by positivity
  have hmle : ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)) ≤ 1 + K := by
    have hKr : K / r ≤ K := by
      rw [div_le_iff₀ hr0]
      nlinarith [hK0, le_of_lt h1r]
    linarith [(abs_le.1 (le_trans hr hKr)).2]
  -- the identity `E_{0,r} = (1 - m_r) - δ_r m_r`
  have hkey : PivotFlux.cutE0 M r = (1 - ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)))
      - δ r * (((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ))) := by
    have hexp : 1 - PivotFlux.cutE0 M r
        = (1 + δ r) * (((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ))) := by
      rw [SourceModelData.one_sub_cutE0 M r, hδeq r hr0]
      calc (1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1) * ((M.ball r).ncard : ℝ) * r ^ (M.α + 1)
          = (1 + δ r) * ((M.ball r).ncard : ℝ)
            * (r ^ (-(M.d : ℝ) - M.α - 1) * r ^ (M.α + 1)) := by ring
        _ = (1 + δ r) * ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)) := by
            rw [← Real.rpow_add hr0]
            norm_num
        _ = (1 + δ r) * (((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ))) := by ring
    have hsub : PivotFlux.cutE0 M r
        = 1 - ((1 + δ r) * (((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)))) := by linarith
    rw [hsub]
    ring
  rw [hkey]
  have hRHS : abs (K * r ^ (-(1 : ℝ)) + (1 + K) * abs (δ r))
      = K * r ^ (-(1 : ℝ)) + (1 + K) * abs (δ r) := by
    rw [abs_of_nonneg]
    have h1 : (0 : ℝ) ≤ K * r ^ (-(1 : ℝ)) :=
      mul_nonneg hK0 (le_of_lt (Real.rpow_pos_of_pos hr0 _))
    have h2 : (0 : ℝ) ≤ (1 + K) * |δ r| := by positivity
    linarith
  rw [hRHS]
  have hm1 : |1 - ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ))| ≤ K / r := by
    have h1 : (1 : ℝ) - ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ))
        = -(((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)) - 1) := by ring
    rw [h1, abs_neg]
    exact hr
  have hδm : |δ r * (((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)))|
      ≤ (1 + K) * |δ r| := by
    rw [abs_mul, abs_of_nonneg hmpos]
    nlinarith [hmle, abs_nonneg (δ r)]
  have hKr : K / r = K * r ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]
    ring
  calc |1 - ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ))
        - δ r * (((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)))|
      ≤ |1 - ((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ))|
        + |δ r * (((M.ball r).ncard : ℝ) * r ^ (-(M.d : ℝ)))| := abs_sub _ _
    _ ≤ K / r + (1 + K) * |δ r| := by linarith [hm1, hδm]
    _ = K * r ^ (-(1 : ℝ)) + (1 + K) * |δ r| := by rw [hKr]

/-! ## 9. The reduced forms, with `E_{0,r}`'s log-integrability derived

Section 8 removes `LogarithmicallyIntegrable (PivotFlux.cutE0 M)` from the hypothesis list of
`logIntegrable_p2Ebar`, so the only remaining external log-integrability input for the
normalized error is the first-moment defect `H_r` (the paper's Proposition I.4.2). -/

/-- **Case 1: `Ē_{2,r}` is logarithmically integrable**, with `E_{0,r}`'s log-integrability
derived from `M.exists_error` and the lattice-ball sandwich. -/
theorem logIntegrable_p2Ebar_of_caseOne (M : SourceModelData)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar) :
    Analysis.LogarithmicallyIntegrable M.p2Ebar :=
  logIntegrable_p2Ebar M
    (logarithmicallyIntegrable_p2ExclError M h3α hκ hP h2 hmeasE2) hHlog
    (logIntegrable_cutE0 M)
    (p2ExclError_tendsto_zero_of_caseOne M h3α hκ hP h2)
    (M.p2H_tendsto_zero_of_hP hP) (PivotFlux.tendsto_cutE0 M) hmeasEbar

/-- **Case 1 of Proposition I.4.15, reduced form**: `E_{β_c,r}|K|² ∼ A r^{3α}` when
`d > 3α`, with `E_{2,r} → 0`, `E_{0,r} → 0`, `H_r → 0`, the log-integrability of `E_{2,r}`
and of `E_{0,r}`, and the vanishing of the right-hand side of (I.4.16) all discharged.
What remains is the radial regularity of `E|K|²` (`hac`, `hae`), the measurability of the
derivative value (`hmR`) and of the two error profiles, the first-moment asymptotic `hP`,
tail finiteness of the two moments, and the log-integrability of `H_r`. -/
theorem tendsto_div_two_of_caseOne_reduced (M : SourceModelData) (hα : 0 < M.α) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have h2fin : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤ :=
    (eventually_ge_atTop r₀).mono fun r hr => h2 r hr
  have hE2 : Tendsto M.p2ExclError atTop (𝓝 0) :=
    p2ExclError_tendsto_zero_of_caseOne M h3α hκ hP h2fin
  exact M.tendsto_div_two_of_hP hα hr₀ hβ hac hae h1 h2 hP hE2
    (logIntegrable_p2Ebar_of_caseOne M h3α hκ hP h2fin hHlog hmeasE2 hmeasEbar)

end CaseOne
end PercLib.CriticalLRP
