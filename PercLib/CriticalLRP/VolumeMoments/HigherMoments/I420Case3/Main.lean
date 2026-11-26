/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Case 3 of Proposition I.4.20: from the discrepancy bound to (I.4.21) and to the
ratio hypothesis of the second induction.  Independent Ultramath work.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Bound

/-!
# Case 3 of Proposition I.4.20: the little-o and the ratio hypothesis

Source: Tom Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Case 3 of the proof of Proposition I.4.20 (paper.txt lines 2883--2887):

```
|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ} - E[|K|^{ℓ+1} Σ_{y∈B_r} 1(y∉K)|K_y|^{p-ℓ}]
   ⪯_p (∇_{r^c} + r^{-c}) (E|K|)^{2p}
   = o((E|K|²/E|K|)^{p-1} (E|K|)²),
```

the last step being Proposition I.4.15 (`E|K|² ≍ (E|K|)³`).

What this file proves:

* `biasTarget_ge_of_m2_ge` — the lower bound `(E|K|²/E|K|)^{p-1}(E|K|)² ≥
  c^{p-1}(E|K|)^{2p}` coming from `E|K|² ≥ c (E|K|)³` (Proposition I.4.15);
* `tendsto_div_biasTarget_zero` — (I.4.21) itself: the averaged discrepancy divided
  by the target tends to zero, since `∇_{r^c}+r^{-c} → 0`;
* `tendsto_div_zero_of_le_mul`, `tendsto_one_of_tendsto_div_sub` — the elementary
  comparisons converting a little-o of one normalisation into a little-o of another,
  and a little-o of the discrepancy into a ratio tending to one;
* `case3_i421_family` and `case3_hAmid_family` — the two statements for a family of
  cutoff laws and balls, in the exact shape of the hypotheses `hAend`/`hAmid` of
  `SecondInduction.derivative_ratio_tendsto`: for every `ℓ ≤ p`,
  `A_ℓ(r) / (|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}) → 1`.

The remaining source inputs are listed in the docstrings: Lemma I.4.17
(`HasTreeExpansion`), Lemma I.4.18 (`HasPolygonBound` with `Bpoly → 0`),
Proposition I.4.15 in the form `E|K|² ⪰ (E|K|)³`, homogeneity of the `(p-ℓ)`-th
moment (transitivity), finiteness of the moments involved, and the comparison
`E|K|^{ℓ+1}E|K|^{p-ℓ} ⪰ (E|K|²/E|K|)^{p-1}(E|K|)²` which the paper obtains from
the induction hypothesis `E|K|^m ≍ r^{(2m-1)α}`.  The ratio (I.4.20) itself is *not*
claimed unconditionally.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Finset Filter
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-! ## The index bookkeeping `a = ℓ+1`, `b = p-ℓ` -/

/-- The substitution of the source: for `ℓ ≤ p` the two moment indices `ℓ+1` and
`p-ℓ` add up to `p+1`, so that `2(a+b)+1-j = 2p+3-j` is the exponent of the tree
expansion at index `p`. -/
theorem succ_add_sub_eq (ℓ p : ℕ) (h : ℓ ≤ p) : ℓ + 1 + (p - ℓ) = p + 1 := by
  omega

/-- The exponent identity of the tree expansion under `a = ℓ+1`, `b = p-ℓ`. -/
theorem exponent_eq (ℓ p j : ℕ) (h : ℓ ≤ p) :
    2 * (ℓ + 1 + (p - ℓ)) + 1 - j = 2 * p + 3 - j := by
  rw [succ_add_sub_eq ℓ p h]
  omega

/-! ## The lower bound for the target of (I.4.21) -/

/-- **Proposition I.4.15 in the only form used by Case 3**: `E|K|² ≥ c (E|K|)³`
implies `(E|K|²/E|K|)^{p-1}(E|K|)² ≥ c^{p-1}(E|K|)^{2p}`. -/
theorem biasTarget_ge_of_m2_ge {m1 m2 c3 : ℝ} {p : ℕ} (hp : 1 ≤ p) (hm1 : 0 < m1)
    (hc3 : 0 < c3) (hgm : c3 * m1 ^ 3 ≤ m2) :
    c3 ^ (p - 1) * m1 ^ (2 * p) ≤ biasTarget m1 m2 p := by
  have hq : c3 * m1 ^ 2 ≤ m2 / m1 := by
    rw [le_div_iff₀ hm1]
    calc c3 * m1 ^ 2 * m1 = c3 * m1 ^ 3 := by ring
      _ ≤ m2 := hgm
  have hc3q : 0 < c3 * m1 ^ 2 := mul_pos hc3 (pow_pos hm1 2)
  have hexp : 2 * (p - 1) + 2 = 2 * p := by omega
  have h2 : (m1 ^ 2) ^ (p - 1) * m1 ^ 2 = m1 ^ (2 * p) := by
    rw [← pow_mul, ← pow_add, hexp]
  have hfirst : (c3 * m1 ^ 2) ^ (p - 1) * m1 ^ 2 = c3 ^ (p - 1) * m1 ^ (2 * p) := by
    rw [mul_pow]
    calc c3 ^ (p - 1) * (m1 ^ 2) ^ (p - 1) * m1 ^ 2
        = c3 ^ (p - 1) * ((m1 ^ 2) ^ (p - 1) * m1 ^ 2) := by ring
      _ = c3 ^ (p - 1) * m1 ^ (2 * p) := by rw [h2]
  rw [biasTarget, ← hfirst]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt hc3q) hq (p - 1))
    (by positivity)

/-- The target of (I.4.21) is positive under the hypotheses of Case 3. -/
theorem biasTarget_pos {m1 m2 c3 : ℝ} {p : ℕ} (hp : 1 ≤ p) (hm1 : 0 < m1) (hc3 : 0 < c3)
    (hgm : c3 * m1 ^ 3 ≤ m2) : 0 < biasTarget m1 m2 p := by
  have h := biasTarget_ge_of_m2_ge hp hm1 hc3 hgm
  have h2 : 0 < c3 ^ (p - 1) * m1 ^ (2 * p) := by positivity
  exact lt_of_lt_of_le h2 h

/-! ## (I.4.21): the averaged discrepancy is a little-o of the target -/

/-- **(I.4.21).**  Suppose the averaged discrepancy is bounded by
`C (∇_{r^c}+r^{-c})(E|K|)^{2p}` with `C ≥ 0`, that `∇_{r^c}+r^{-c} → 0`, and that
`E|K|² ≥ c (E|K|)³` (Proposition I.4.15).  Then
`D(r) / ((E|K|²/E|K|)^{p-1}(E|K|)²) → 0`. -/
theorem tendsto_div_biasTarget_zero {D m1 m2 Bpoly : ℝ → ℝ} {p : ℕ} {Cb c3 : ℝ}
    (hp : 1 ≤ p) (hCb : 0 ≤ Cb) (hc3 : 0 < c3) (hD0 : ∀ᶠ r in atTop, 0 ≤ D r)
    (hD : ∀ᶠ r in atTop, D r ≤ Cb * Bpoly r * m1 r ^ (2 * p))
    (hBpoly0 : ∀ᶠ r in atTop, 0 ≤ Bpoly r) (hpoly : Tendsto Bpoly atTop (𝓝 0))
    (hm1 : ∀ᶠ r in atTop, 0 < m1 r)
    (hgm : ∀ᶠ r in atTop, c3 * m1 r ^ 3 ≤ m2 r) :
    Tendsto (fun r => D r / biasTarget (m1 r) (m2 r) p) atTop (𝓝 0) := by
  have hmain : ∀ᶠ r in atTop,
      D r / biasTarget (m1 r) (m2 r) p ≤ (Cb / c3 ^ (p - 1)) * Bpoly r := by
    filter_upwards [hD, hD0, hBpoly0, hm1, hgm] with r hD hD0 hBpoly0 hm1 hgm
    have hbt := biasTarget_ge_of_m2_ge (p := p) hp hm1 hc3 hgm
    have hbtpos : 0 < biasTarget (m1 r) (m2 r) p :=
      biasTarget_pos (p := p) hp hm1 hc3 hgm
    rw [div_le_iff₀ hbtpos]
    have hcoef : 0 ≤ Cb / c3 ^ (p - 1) := div_nonneg hCb (by positivity)
    calc D r ≤ Cb * Bpoly r * m1 r ^ (2 * p) := hD
      _ = (Cb / c3 ^ (p - 1)) * Bpoly r * (c3 ^ (p - 1) * m1 r ^ (2 * p)) := by
          field_simp
      _ ≤ (Cb / c3 ^ (p - 1)) * Bpoly r * biasTarget (m1 r) (m2 r) p :=
          mul_le_mul_of_nonneg_left hbt (mul_nonneg hcoef hBpoly0)
  refine squeeze_zero' ?_ hmain ?_
  · filter_upwards [hD0, hm1, hgm] with r hD0 hm1 hgm
    exact div_nonneg hD0 (le_of_lt (biasTarget_pos (p := p) hp hm1 hc3 hgm))
  · simpa using hpoly.const_mul (Cb / c3 ^ (p - 1))

/-! ## Elementary conversions -/

/-- A little-o in one normalisation gives a little-o in a smaller one. -/
theorem tendsto_div_zero_of_le_mul {D den T : ℝ → ℝ} {c : ℝ}
    (hD : Tendsto (fun r => D r / T r) atTop (𝓝 0))
    (hD0 : ∀ᶠ r in atTop, 0 ≤ D r) (hT : ∀ᶠ r in atTop, 0 < T r) (hc : 0 < c)
    (hcmp : ∀ᶠ r in atTop, c * T r ≤ den r) :
    Tendsto (fun r => D r / den r) atTop (𝓝 0) := by
  have hbound : ∀ᶠ r in atTop, D r / den r ≤ (1 / c) * (D r / T r) := by
    filter_upwards [hD0, hT, hcmp] with r hD0 hT hcmp
    have hcT : 0 < c * T r := mul_pos hc hT
    have hden : 0 < den r := lt_of_lt_of_le hcT hcmp
    have h1 : D r / den r ≤ D r / (c * T r) := by
      rw [div_le_div_iff₀ hden hcT]
      exact mul_le_mul_of_nonneg_left hcmp hD0
    have h2 : D r / (c * T r) = (1 / c) * (D r / T r) := by
      field_simp
    rw [h2] at h1
    exact h1
  refine squeeze_zero' ?_ hbound ?_
  · filter_upwards [hD0, hT, hcmp] with r hD0 hT hcmp
    have hcT : 0 < c * T r := mul_pos hc hT
    exact div_nonneg hD0 (le_of_lt (lt_of_lt_of_le hcT hcmp))
  · have := hD.const_mul (1 / c)
    simpa using this

/-- A little-o of the discrepancy gives a ratio tending to one. -/
theorem tendsto_one_of_tendsto_div_sub {A den D : ℝ → ℝ}
    (hrel : ∀ᶠ r in atTop, D r = den r - A r)
    (hz : Tendsto (fun r => D r / den r) atTop (𝓝 0))
    (hne : ∀ᶠ r in atTop, den r ≠ 0) :
    Tendsto (fun r => A r / den r) atTop (𝓝 1) := by
  have hcongr : ∀ᶠ r in atTop, (1 - D r / den r) = A r / den r := by
    filter_upwards [hrel, hne] with r hrel hne
    rw [hrel]
    field_simp
    ring
  have hlim : Tendsto (fun r => 1 - D r / den r) atTop (𝓝 1) := by
    have := hz.const_sub 1
    simpa using this
  exact hlim.congr' hcongr

/-! ## (I.4.21) and the ratio hypothesis for a family of cutoff laws -/

/-- **(I.4.21) for a family of cutoff laws.**  For a family of laws `π r` and balls
`B r`, the averaged discrepancy of Case 3 satisfies
`|B_r|^{-1}(|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ} - A_ℓ(r))
   = o((E|K|²/E|K|)^{p-1}(E|K|)²)`, i.e. `discR / biasTarget → 0`.

Inputs: the tree expansion (Lemma I.4.17, `hTree`), the polygon bound (Lemma I.4.18,
`hPoly`) with `∇_{r^c}+r^{-c} → 0` (`hpoly`), finiteness of the moments
(`hM1`, `hMa`, `hMb`), non-degeneracy of the ball (`hcard`), and the lower bound
`E|K|² ≥ c(E|K|)³` of Proposition I.4.15 (`hgm`). -/
theorem case3_i421_family (π : ℝ → Sym2 V → unitInterval) (o : V) (B : ℝ → Finset V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (p ℓ : ℕ) (hp : 1 ≤ p) (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (poly : ℝ → V → ℕ → ℝ≥0∞) (C : ℕ → ℝ) (Bpoly : ℝ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hpoly : Tendsto Bpoly atTop (𝓝 0))
    (hTree : ∀ r, HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) C)
    (hPoly : ∀ r, HasPolygonBound (π r) o (B r) p (poly r) (Bpoly r))
    (hcard : ∀ r, 0 < (B r).card)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ r, I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (y : V), y ∈ B r → I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r) :
    Tendsto (fun r => discR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      biasTarget (momOf π o 1 r) (momOf π o 2 r) p) atTop (𝓝 0) := by
  have hbound : ∀ᶠ r in atTop, discR (π r) o (ℓ + 1) (p - ℓ) (B r) ≤
      coeffSum C p * Bpoly r * momOf π o 1 r ^ (2 * p) := by
    filter_upwards with r
    exact discR_le_polygon (hπ r) 𝓔 h𝓔mono h𝓔 hp hC (hTree r) (hPoly r) (hcard r)
      (hM1 r) (hMa r) (hMb r)
  have hD0 : ∀ᶠ r in atTop, 0 ≤ discR (π r) o (ℓ + 1) (p - ℓ) (B r) := by
    filter_upwards with r
    exact discR_nonneg (hπ r) 𝓔 h𝓔mono h𝓔 (hcard r) (hMa r) (hMb r)
  have hBpoly0 : ∀ᶠ r in atTop, 0 ≤ Bpoly r :=
    Eventually.of_forall fun r => (hPoly r).nonneg
  have hm1 : ∀ᶠ r in atTop, 0 < momOf π o 1 r :=
    Eventually.of_forall fun r => momR_pos (hM1 r)
  exact tendsto_div_biasTarget_zero hp (Finset.sum_nonneg fun j _ => hC j) hc3 hD0 hbound
    hBpoly0 hpoly hm1 hgm

/-- **The ratio hypothesis `hAend`/`hAmid` of the second induction, from Case 3.**
Given (I.4.21) and the comparison
`E|K|^{ℓ+1}E|K|^{p-ℓ} ⪰ (E|K|²/E|K|)^{p-1}(E|K|)²` (the source's induction
hypothesis `E|K|^m ≍ r^{(2m-1)α}`), the ratio of `A_ℓ(r)` to
`|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}` tends to `1`. -/
theorem case3_hAmid_of_i421 (π : ℝ → Sym2 V → unitInterval) (o : V) (B : ℝ → Finset V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (p ℓ : ℕ) (hp : 1 ≤ p) (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (hcard : ∀ r, 0 < (B r).card)
    (hhom : ∀ (r : ℝ) (y : V), y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ r, I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (y : V), y ∈ B r → I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    (hstep1 : Tendsto (fun r => discR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      biasTarget (momOf π o 1 r) (momOf π o 2 r) p) atTop (𝓝 0))
    {c3 c4 : ℝ} (hc3 : 0 < c3) (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r)
    (hc4 : 0 < c4) (hcmp : ∀ᶠ r in atTop, c4 * biasTarget (momOf π o 1 r) (momOf π o 2 r) p
      ≤ momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
  have hm1 : ∀ r, 0 < momOf π o 1 r := fun r => momR_pos (hM1 r)
  have hT : ∀ᶠ r in atTop, 0 < biasTarget (momOf π o 1 r) (momOf π o 2 r) p := by
    filter_upwards [hgm] with r hgm
    exact biasTarget_pos hp (hm1 r) hc3 hgm
  have hXpos : ∀ᶠ r in atTop, 0 < momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r := by
    filter_upwards [hT, hcmp] with r hT hcmp
    exact lt_of_lt_of_le (mul_pos hc4 hT) hcmp
  have hD0 : ∀ᶠ r in atTop, 0 ≤ discR (π r) o (ℓ + 1) (p - ℓ) (B r) := by
    filter_upwards with r
    exact discR_nonneg (hπ r) 𝓔 h𝓔mono h𝓔 (hcard r) (hMa r) (hMb r)
  have hstep2 : Tendsto (fun r => discR (π r) o (ℓ + 1) (p - ℓ) (B r) /
      (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r)) atTop (𝓝 0) :=
    tendsto_div_zero_of_le_mul hstep1 hD0 hT hc4 hcmp
  have hcardne : ∀ᶠ r in atTop, ((B r).card : ℝ) ≠ 0 := by
    filter_upwards with r
    have := hcard r
    exact_mod_cast ne_of_gt this
  have hrel : ∀ᶠ r in atTop, discR (π r) o (ℓ + 1) (p - ℓ) (B r) =
      momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r -
        (I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) / ballCard B r) := by
    filter_upwards [hcardne] with r hc
    have hP := I420Case1.prodFactor_toReal (π r) o (ℓ + 1) (p - ℓ) (B r) (hhom r)
    rw [discR, hP]
    simp only [ballCard, momOf, I420Case1.mixedExclR]
    field_simp
  have hne : ∀ᶠ r in atTop, momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r ≠ 0 :=
    hXpos.mono fun r h => h.ne'
  have hmain := tendsto_one_of_tendsto_div_sub hrel hstep2 hne
  refine hmain.congr' ?_
  filter_upwards [hcardne, hne] with r hc hne
  simp only [ballCard]
  field_simp

/-! ## The `hAend`/`hAmid` pair of the second induction -/

/-- **Case 3 produces the `hAend` and `hAmid` hypotheses of
`SecondInduction.derivative_ratio_tendsto`.**  The coefficients `C ℓ j` are the
universal integers `C_{a,b,j}` of Lemma I.4.17 at `a = ℓ+1`, `b = p-ℓ`; the polygon
bound is common to all `ℓ` because Lemma I.4.18 bounds the same matrix powers `T^j`.

The conclusion is the pair of limits on the left-hand side of (I.4.20):
for `ℓ = 0` (the paper's `hAend`) and for every `1 ≤ ℓ ≤ p-2` (the paper's `hAmid`),
`A_ℓ(r) / (|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}) → 1`.  The remaining index `ℓ = p-1` is
recovered in the source from mass transport, `A_{p-1} = A_0`. -/
theorem case3_hAend_hAmid (π : ℝ → Sym2 V → unitInterval) (o : V) (B : ℝ → Finset V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (p : ℕ) (hp : 3 ≤ p) (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (poly : ℝ → V → ℕ → ℝ≥0∞) (C : ℕ → ℕ → ℝ) (Bpoly : ℝ → ℝ) (hC : ∀ ℓ j, 0 ≤ C ℓ j)
    (hpoly : Tendsto Bpoly atTop (𝓝 0))
    (hTree : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p →
      HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) (C ℓ))
    (hPoly : ∀ r, HasPolygonBound (π r) o (B r) p (poly r) (Bpoly r))
    (hcard : ∀ r, 0 < (B r).card)
    (hhom : ∀ (r : ℝ) (ℓ : ℕ) (y : V), y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p → I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (ℓ : ℕ) (y : V), ℓ ≤ p → y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 c4 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r) (hc4 : 0 < c4)
    (hcmp : ∀ (ℓ : ℕ), ℓ ≤ p → ∀ᶠ r in atTop,
      c4 * biasTarget (momOf π o 1 r) (momOf π o 2 r) p
        ≤ momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o 1 p (B r) /
        (ballCard B r * (momOf π o 1 r * momOf π o p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
          (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
  have hone : ∀ ℓ, ℓ ≤ p → Tendsto (fun r =>
      I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
        (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
    intro ℓ hℓ
    have h1 : 1 ≤ p := by omega
    have hb := fun (r : ℝ) (y : V) (hy : y ∈ B r) => hMb r ℓ y hℓ hy
    refine case3_hAmid_of_i421 π o B 𝓔 h𝓔mono h𝓔 p ℓ h1 hπ hcard
      (fun r => hhom r ℓ) hM1 (hMa · ℓ hℓ) hb ?_ hc3 hgm hc4 (hcmp ℓ hℓ)
    exact case3_i421_family π o B 𝓔 h𝓔mono h𝓔 p ℓ h1 hπ poly (C ℓ) Bpoly (hC ℓ) hpoly
      (fun r => hTree r ℓ hℓ) hPoly hcard hM1 (hMa · ℓ hℓ)
      (fun r y hy => hMb r ℓ y hℓ hy) hc3 hgm
  exact ⟨hone 0 (by omega), fun ℓ h1 h2 => hone ℓ (by omega)⟩

end I420Case3

end PercLib.CriticalLRP
