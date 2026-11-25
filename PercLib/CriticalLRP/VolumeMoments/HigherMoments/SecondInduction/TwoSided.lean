/- Integrated from independently rebuilt Ultramath work.
Production base e756a603f08962e545c3c11bf9dd877b46c80d6f.
Scratch source: ../../.ultramath/smwvp122a/m2/M2/TwoSided.lean.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Main

/-!
# The second induction of Proposition I.4.20

This file carries out the paper's second induction step on `p`, i.e. the passage
from the decorrelation estimates (I.4.20) to the asymptotic
`E|K|^p ~ (2p-3)!! (E|K|²/E|K|)^(p-1) E|K|` by way of Lemma I.4.21.  The
percolation inputs stay explicit.

The analytic content is the finite weighted-average squeeze: with all weights
nonnegative and all normalised factors within `1 ± ε`, the weighted average of
the normalised decorrelators is within `1 ± ε` of the weighted average of the
exact ones, and the latter is `targetSum`.
-/

@[expose] public section

noncomputable section

open Finset Filter
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction

open PercLib.CriticalLRP.VolumeMoments
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-! ### The weighted-average squeeze -/

/-- A finite sum of terms `c i * u i * w i` with `|u i - 1| ≤ ε` and
nonnegative `c i`, `w i` differs from `∑ c i * w i` by at most `ε` times that
sum. -/
theorem abs_weighted_sum_sub_le {ι : Type*} (s : Finset ι) {c w u : ι → ℝ} {ε : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu : ∀ i ∈ s, |u i - 1| ≤ ε) :
    |(∑ i ∈ s, c i * u i * w i) - ∑ i ∈ s, c i * w i| ≤ ε * ∑ i ∈ s, c i * w i := by
  have hsplit : (∑ i ∈ s, c i * u i * w i) - ∑ i ∈ s, c i * w i
      = ∑ i ∈ s, c i * (u i - 1) * w i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit]
  refine (Finset.abs_sum_le_sum_abs (fun i => c i * (u i - 1) * w i) s).trans ?_
  have hstep : ∑ i ∈ s, |c i * (u i - 1) * w i| ≤ ∑ i ∈ s, ε * (c i * w i) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [mul_assoc, abs_mul, abs_mul, abs_of_nonneg (hc i hi), abs_of_nonneg (hw i hi)]
    have h1 : c i * |u i - 1| ≤ c i * ε := mul_le_mul_of_nonneg_left (hu i hi) (hc i hi)
    calc c i * (|u i - 1| * w i) = (c i * |u i - 1|) * w i := by ring
      _ ≤ (c i * ε) * w i := mul_le_mul_of_nonneg_right h1 (hw i hi)
      _ = ε * (c i * w i) := by ring
  refine hstep.trans_eq ?_
  rw [Finset.mul_sum]

/-- The weighted average of `u` with weights `c i * w i` is within `ε` of `1`
whenever each `u i` is. -/
theorem weighted_average_abs_le {ι : Type*} (s : Finset ι) {c w u : ι → ℝ} {ε : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu : ∀ i ∈ s, |u i - 1| ≤ ε)
    (hpos : 0 < ∑ i ∈ s, c i * w i) :
    |(∑ i ∈ s, c i * u i * w i) / (∑ i ∈ s, c i * w i) - 1| ≤ ε := by
  have hden : ∑ i ∈ s, c i * w i ≠ 0 := ne_of_gt hpos
  have h := abs_weighted_sum_sub_le s hc hw hu
  rw [div_sub_one hden, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  exact h

/-! ### The target sum as a single weighted sum -/

/-- `targetSum` is the weighted sum `(p+1) E|K|^p + ∑_{ℓ=1}^{p-2} C(p,ℓ) w_ℓ`
with the double-factorial weights of `targetWeight`.  The combinatorial input is
`∑_{ℓ=1}^{p-2} C(p,ℓ)(2ℓ-1)!!(2p-2ℓ-3)!! = (p-2)(2p-3)!!` (Lemma I.4.23 with
the end terms removed), together with `dblFact p = (2p-1) dblFact (p-1)`. -/
theorem targetSum_eq_weight_sum {p : ℕ} (hp : 3 ≤ p) {mom : ℕ → ℝ → ℝ} {r : ℝ} :
    targetSum p mom r
      = ((p : ℝ) + 1) * mom p r
        + ∑ j ∈ Finset.range (p - 2),
            ((p.choose (j + 1) : ℕ) : ℝ) * targetWeight p (j + 1) mom r := by
  have hterm : ∀ j ∈ Finset.range (p - 2),
      ((p.choose (j + 1) : ℕ) : ℝ) * targetWeight p (j + 1) mom r
        = (((p.choose (j + 1) : ℕ) : ℝ) * (dblFact (j + 1) * dblFact (p - 2 - j)))
            * (momentRatio mom r ^ ((p : ℝ) - 1) * mom 1 r) := by
    intro j hj
    have hj' : j ≤ p - 3 := by have := Finset.mem_range.1 hj; omega
    unfold targetWeight
    rw [show p - (j + 1) - 1 = p - 2 - j by omega]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, middle_sum_eq hp]
  unfold targetSum mixedMoment
  ring

/-- Splitting the `p`-term binomial sum of the derivative identity into its two
end terms and the `p-2` middle terms. -/
theorem sum_range_p_split {p : ℕ} (hp : 3 ≤ p) (g : ℕ → ℝ) :
    (∑ ℓ ∈ Finset.range p, g ℓ)
      = g 0 + g (p - 1) + ∑ j ∈ Finset.range (p - 2), g (j + 1) := by
  have e1 := Finset.sum_range_succ' g (p - 1)
  rw [show p - 1 + 1 = p by omega] at e1
  have e2 := Finset.sum_range_succ (fun i => g (i + 1)) (p - 2)
  rw [show p - 2 + 1 = p - 1 by omega] at e2
  rw [e2] at e1
  rw [e1]
  ring

/-! ### The exact factorisations of the individual terms -/

/-- The `ℓ = 0` end term of `normalizedSum`, written with the normalised end
decorrelator `A_0/(|B_r| E|K| E|K|^p)`. -/
theorem normalizedSum_zero_term {p : ℕ} {mom : ℕ → ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    {Bcard : ℝ → ℝ} {r : ℝ} (hB : Bcard r ≠ 0) (h1 : mom 1 r ≠ 0)
    (hpv : mom p r ≠ 0) :
    A 0 r / (Bcard r * mom 1 r)
      = (A 0 r / (Bcard r * (mom 1 r * mom p r))) * mom p r := by
  field_simp

/-- The `ℓ = p-1` end term of `normalizedSum`; mass transport identifies
`A_{p-1}` with `A_0`, and `C(p,p-1) = p`. -/
theorem normalizedSum_last_term {p : ℕ} (hp : 3 ≤ p) {mom : ℕ → ℝ → ℝ}
    {A : ℕ → ℝ → ℝ} {Bcard : ℝ → ℝ} {r : ℝ} (hmass : A (p - 1) r = A 0 r)
    (hB : Bcard r ≠ 0) (h1 : mom 1 r ≠ 0) (hpv : mom p r ≠ 0) :
    ((p.choose (p - 1) : ℕ) : ℝ) * (A (p - 1) r / (Bcard r * mom 1 r))
      = (p : ℝ) * ((A 0 r / (Bcard r * (mom 1 r * mom p r))) * mom p r) := by
  have hchoose : ((p.choose (p - 1) : ℕ) : ℝ) = (p : ℝ) := by
    have h := Nat.choose_succ_self_right (p - 1)
    rw [show p - 1 + 1 = p by omega] at h
    rw [h]
  rw [hchoose, hmass]
  field_simp

/-- **The double-factorial weight identity.**  The `ℓ`-th weight of the target
sum, multiplied by `E|K|`, is the product of the two moments of the
induction-hypothesis orders.  This is the exponent identity
`(E|K|²/E|K|)^ℓ · (E|K|²/E|K|)^(p-ℓ-1) = (E|K|²/E|K|)^(p-1)` in the form in
which the induction hypothesis enters the second induction. -/
theorem targetWeight_mul_mom_one {p ℓ : ℕ} (hp : 3 ≤ p) (hℓ1 : 1 ≤ ℓ) (hℓ2 : ℓ ≤ p - 2)
    {mom : ℕ → ℝ → ℝ} {r : ℝ} (hR : 0 < momentRatio mom r) :
    targetWeight p ℓ mom r * mom 1 r
      = mixedMoment (ℓ + 1) mom r * mixedMoment (p - ℓ) mom r := by
  have hpow := ratio_pow_mul (R := momentRatio mom r) hR hp (ℓ := ℓ - 1) (by omega)
  have hidx1 : (((ℓ + 1 : ℕ)) : ℝ) - 1 = (((ℓ - 1 + 2 : ℕ)) : ℝ) - 1 := by
    have h : (ℓ + 1 : ℕ) = (ℓ - 1 + 2 : ℕ) := by omega
    rw [h]
  have hidx2 : (((p - ℓ : ℕ)) : ℝ) - 1 = (((p - 1 - (ℓ - 1) : ℕ)) : ℝ) - 1 := by
    have h : p - ℓ = (p - 1 - (ℓ - 1) : ℕ) := by omega
    rw [h]
  have hdle : ℓ + 1 - 1 = ℓ := by omega
  simp only [mixedMoment, targetWeight, hdle]
  rw [hidx1, hidx2, ← hpow]
  ring

/-- The `ℓ`-th middle term of `normalizedSum`, factorised into the decorrelation
ratio, the two induction-hypothesis ratios and the double-factorial weight. -/
theorem normalizedSum_mid_term {p ℓ : ℕ} (hp : 3 ≤ p) (hℓ1 : 1 ≤ ℓ) (hℓ2 : ℓ ≤ p - 2)
    {mom : ℕ → ℝ → ℝ} {A : ℕ → ℝ → ℝ} {Bcard : ℝ → ℝ} {r : ℝ}
    (hB : Bcard r ≠ 0) (h1 : mom 1 r ≠ 0) (hR : 0 < momentRatio mom r)
    (hmom : ∀ m, mom m r ≠ 0) :
    A ℓ r / (Bcard r * mom 1 r)
      = (A ℓ r / (Bcard r * (mom (ℓ + 1) r * mom (p - ℓ) r)))
        * ((mom (ℓ + 1) r / mixedMoment (ℓ + 1) mom r)
            * (mom (p - ℓ) r / mixedMoment (p - ℓ) mom r))
        * targetWeight p ℓ mom r := by
  have hmul := targetWeight_mul_mom_one hp hℓ1 hℓ2 hR
  have htw : targetWeight p ℓ mom r
      = mixedMoment (ℓ + 1) mom r * mixedMoment (p - ℓ) mom r / mom 1 r := by
    rw [eq_div_iff h1]
    linarith [hmul]
  rw [htw]
  have hm1 : mom (ℓ + 1) r ≠ 0 := hmom _
  have hm2 : mom (p - ℓ) r ≠ 0 := hmom _
  have hx1 : mixedMoment (ℓ + 1) mom r ≠ 0 := mixedMoment_ne_zero hR h1
  have hx2 : mixedMoment (p - ℓ) mom r ≠ 0 := mixedMoment_ne_zero hR h1
  field_simp

/-! ### From eventual bounds to the weighted average -/

/-- If the end term is within `η` of `E` and the summed middle terms are within
`η` of `T`, then the quotient `(e+S)/(E+T)` is within `η` of `1`. -/
theorem ratio_abs_le_of_parts {e E S T η : ℝ} (hET : 0 < E + T)
    (hend : |e - E| ≤ η * E) (hmid : |S - T| ≤ η * T) :
    |(e + S) / (E + T) - 1| ≤ η := by
  have hnum : |(e + S) - (E + T)| ≤ η * (E + T) := by
    have hsplit : (e + S) - (E + T) = (e - E) + (S - T) := by ring
    rw [hsplit]
    refine (abs_add_le (e - E) (S - T)).trans ?_
    calc |e - E| + |S - T| ≤ η * E + η * T := add_le_add hend hmid
      _ = η * (E + T) := by ring
  have hEq : (e + S) / (E + T) - 1 = ((e + S) - (E + T)) / (E + T) := by
    field_simp
  rw [hEq, abs_div, abs_of_pos hET, div_le_iff₀ hET]
  exact hnum

/-- An eventual `|f - 1| ≤ η` statement, read off from `f → 1`. -/
theorem eventually_abs_sub_one_le {f : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (h : Tendsto f atTop (𝓝 1)) : ∀ᶠ r in atTop, |f r - 1| ≤ η := by
  have h2 : ∀ᶠ r in atTop, dist (f r) 1 < η := h.eventually (Metric.ball_mem_nhds 1 hη)
  filter_upwards [h2] with r hr
  rw [Real.dist_eq] at hr
  linarith

/-- **The second-induction ratio: the normalised decorrelation sum is
asymptotic to the target sum.**

This is the paper's passage from the decorrelation estimates (I.4.20) to the
derivative asymptotic (I.4.22), stated at the level of the finite sums: the
binomial sum of the `A_ℓ`, normalised by `|B_r| E|K|`, has the same asymptotic
size as `(p+1)E|K|^p + (p-2)(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|`.

The percolation content is entirely in the three hypotheses `hAend`
(decorrelation at `ℓ = 0`), `hAmid` (decorrelation at `1 ≤ ℓ ≤ p-2`) and `hIH`
(the induction hypothesis for the smaller moments); `hmass` is the mass
transport identity `A_0 = A_{p-1}`. -/
theorem normalizedSum_eventually {p : ℕ} (hp : 3 ≤ p) {mom : ℕ → ℝ → ℝ}
    {A : ℕ → ℝ → ℝ} {Bcard : ℝ → ℝ} (hmom : ∀ m r, 0 < r → 0 < mom m r)
    (hB : ∀ r, 0 < r → 0 < Bcard r)
    (hmass : ∀ r, 0 < r → A (p - 1) r = A 0 r)
    (hAend : Tendsto (fun r => A 0 r / (Bcard r * (mom 1 r * mom p r))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun r => A ℓ r / (Bcard r * (mom (ℓ + 1) r * mom (p - ℓ) r))) atTop (𝓝 1))
    (hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
      Tendsto (fun r => mom m r / mixedMoment m mom r) atTop (𝓝 1)) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      dist (normalizedSum p A Bcard mom r / targetSum p mom r) 1 < ε := by
  intro ε hε
  set η : ℝ := ε / 8 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hηlt : η < ε := by rw [hηdef]; linarith
  have hev_end : ∀ᶠ r in atTop,
      |A 0 r / (Bcard r * (mom 1 r * mom p r)) - 1| ≤ η :=
    eventually_abs_sub_one_le hη hAend
  have hev_mid : ∀ᶠ r in atTop, ∀ j ∈ Finset.range (p - 2),
      |(A (j + 1) r / (Bcard r * (mom (j + 1 + 1) r * mom (p - (j + 1)) r)))
        * ((mom (j + 1 + 1) r / mixedMoment (j + 1 + 1) mom r)
          * (mom (p - (j + 1)) r / mixedMoment (p - (j + 1)) mom r)) - 1| ≤ η := by
    rw [eventually_all_finset]
    intro j hj
    have hj1 : 1 ≤ j + 1 := by omega
    have hj2 : j + 1 ≤ p - 2 := by
      have := Finset.mem_range.1 hj
      omega
    have hdec := hAmid (j + 1) hj1 hj2
    have h1 := hIH (j + 1 + 1) (by omega) (by omega)
    have h2 := hIH (p - (j + 1)) (by omega) (by omega)
    exact eventually_abs_sub_one_le hη (by simpa using hdec.mul (h1.mul h2))
  filter_upwards [hev_end, hev_mid, eventually_gt_atTop (0 : ℝ)] with r hende hmidr hr
  -- positivity and the exact identities
  have hm1 : 0 < mom 1 r := hmom 1 r hr
  have hm2 : 0 < mom 2 r := hmom 2 r hr
  have hmp : 0 < mom p r := hmom p r hr
  have hR : 0 < momentRatio mom r := div_pos hm2 hm1
  have hmne : ∀ m, mom m r ≠ 0 := fun m => (hmom m r hr).ne'
  have hBne : Bcard r ≠ 0 := (hB r hr).ne'
  -- the exact identity for the numerator
  have hN : normalizedSum p A Bcard mom r
      = ((p : ℝ) + 1) * (A 0 r / (Bcard r * (mom 1 r * mom p r))) * mom p r
        + ∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            ((A (j + 1) r / (Bcard r * (mom (j + 1 + 1) r * mom (p - (j + 1)) r)))
              * ((mom (j + 1 + 1) r / mixedMoment (j + 1 + 1) mom r)
                * (mom (p - (j + 1)) r / mixedMoment (p - (j + 1)) mom r))
              * targetWeight p (j + 1) mom r) := by
    unfold normalizedSum
    rw [sum_range_p_split hp (fun ℓ => ((p.choose ℓ : ℕ) : ℝ) *
      (A ℓ r / (Bcard r * mom 1 r)))]
    have h0 : ((p.choose 0 : ℕ) : ℝ) * (A 0 r / (Bcard r * mom 1 r))
        = (A 0 r / (Bcard r * (mom 1 r * mom p r))) * mom p r := by
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
      exact normalizedSum_zero_term hBne (hmne 1) hmp.ne'
    have hl : ((p.choose (p - 1) : ℕ) : ℝ) * (A (p - 1) r / (Bcard r * mom 1 r))
        = (p : ℝ) * ((A 0 r / (Bcard r * (mom 1 r * mom p r))) * mom p r) :=
      normalizedSum_last_term hp (hmass r hr) hBne (hmne 1) hmp.ne'
    have hsum : (∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
          (A (j + 1) r / (Bcard r * mom 1 r)))
        = ∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            ((A (j + 1) r / (Bcard r * (mom (j + 1 + 1) r * mom (p - (j + 1)) r)))
              * ((mom (j + 1 + 1) r / mixedMoment (j + 1 + 1) mom r)
                * (mom (p - (j + 1)) r / mixedMoment (p - (j + 1)) mom r))
              * targetWeight p (j + 1) mom r) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : 1 ≤ j + 1 := by omega
      have hj2 : j + 1 ≤ p - 2 := by
        have := Finset.mem_range.1 hj
        omega
      rw [normalizedSum_mid_term (p := p) (ℓ := j + 1) hp hj1 hj2 hBne (hmne 1) hR hmne]
    rw [h0, hl, hsum]
    ring
  rw [hN, targetSum_eq_weight_sum (p := p) hp (mom := mom) (r := r)]
  -- the two bounds
  have hend : |((p : ℝ) + 1) * (A 0 r / (Bcard r * (mom 1 r * mom p r))) * mom p r
      - ((p : ℝ) + 1) * mom p r| ≤ η * (((p : ℝ) + 1) * mom p r) := by
    have hfac : ((p : ℝ) + 1) * (A 0 r / (Bcard r * (mom 1 r * mom p r))) * mom p r
        - ((p : ℝ) + 1) * mom p r
        = (((p : ℝ) + 1) * mom p r) * (A 0 r / (Bcard r * (mom 1 r * mom p r)) - 1) := by
      ring
    have hc : (0 : ℝ) ≤ ((p : ℝ) + 1) * mom p r := by positivity
    rw [hfac, abs_mul, abs_of_nonneg hc]
    calc (((p : ℝ) + 1) * mom p r) * |A 0 r / (Bcard r * (mom 1 r * mom p r)) - 1|
        ≤ (((p : ℝ) + 1) * mom p r) * η := mul_le_mul_of_nonneg_left hende hc
      _ = η * (((p : ℝ) + 1) * mom p r) := by ring
  have hw : ∀ j ∈ Finset.range (p - 2), 0 ≤ targetWeight p (j + 1) mom r := by
    intro j hj
    have hRle : 0 ≤ momentRatio mom r := hR.le
    have hpow : 0 < momentRatio mom r ^ ((p : ℝ) - 1) := Real.rpow_pos_of_pos hR _
    unfold targetWeight
    have := dblFact_pos (j + 1)
    have := dblFact_pos (p - (j + 1) - 1)
    positivity
  have hmid : |(∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            ((A (j + 1) r / (Bcard r * (mom (j + 1 + 1) r * mom (p - (j + 1)) r)))
              * ((mom (j + 1 + 1) r / mixedMoment (j + 1 + 1) mom r)
                * (mom (p - (j + 1)) r / mixedMoment (p - (j + 1)) mom r))
              * targetWeight p (j + 1) mom r))
      - (∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            targetWeight p (j + 1) mom r)|
      ≤ η * (∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            targetWeight p (j + 1) mom r) := by
    have hshape : (∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            ((A (j + 1) r / (Bcard r * (mom (j + 1 + 1) r * mom (p - (j + 1)) r)))
              * ((mom (j + 1 + 1) r / mixedMoment (j + 1 + 1) mom r)
                * (mom (p - (j + 1)) r / mixedMoment (p - (j + 1)) mom r))
              * targetWeight p (j + 1) mom r))
        = ∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            ((A (j + 1) r / (Bcard r * (mom (j + 1 + 1) r * mom (p - (j + 1)) r)))
              * ((mom (j + 1 + 1) r / mixedMoment (j + 1 + 1) mom r)
                * (mom (p - (j + 1)) r / mixedMoment (p - (j + 1)) mom r)))
            * targetWeight p (j + 1) mom r := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hshape]
    refine abs_weighted_sum_sub_le (Finset.range (p - 2))
      (c := fun j => ((p.choose (j + 1) : ℕ) : ℝ))
      (w := fun j => targetWeight p (j + 1) mom r)
      (u := fun j => (A (j + 1) r / (Bcard r * (mom (j + 1 + 1) r * mom (p - (j + 1)) r)))
              * ((mom (j + 1 + 1) r / mixedMoment (j + 1 + 1) mom r)
                * (mom (p - (j + 1)) r / mixedMoment (p - (j + 1)) mom r)))
      (fun j _ => by positivity) hw (fun j hj => hmidr j hj)
  have hpos : 0 < ((p : ℝ) + 1) * mom p r
      + ∑ j ∈ Finset.range (p - 2), ((p.choose (j + 1) : ℕ) : ℝ) *
            targetWeight p (j + 1) mom r := by
    have hs := targetSum_pos (p := p) hp hm1 hm2 hmp
    rw [targetSum_eq_weight_sum (p := p) hp (mom := mom) (r := r)] at hs
    exact hs
  rw [Real.dist_eq]
  have habs := ratio_abs_le_of_parts hpos hend hmid
  linarith

/-- **The second-induction ratio, in limit form.** -/
theorem normalizedSum_tendsto {p : ℕ} (hp : 3 ≤ p) {mom : ℕ → ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    {Bcard : ℝ → ℝ} (hmom : ∀ m r, 0 < r → 0 < mom m r)
    (hB : ∀ r, 0 < r → 0 < Bcard r)
    (hmass : ∀ r, 0 < r → A (p - 1) r = A 0 r)
    (hAend : Tendsto (fun r => A 0 r / (Bcard r * (mom 1 r * mom p r))) atTop (𝓝 1))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 →
      Tendsto (fun r => A ℓ r / (Bcard r * (mom (ℓ + 1) r * mom (p - ℓ) r))) atTop (𝓝 1))
    (hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
      Tendsto (fun r => mom m r / mixedMoment m mom r) atTop (𝓝 1)) :
    Tendsto (fun r => normalizedSum p A Bcard mom r / targetSum p mom r) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  exact Filter.eventually_atTop.1
    (normalizedSum_eventually hp hmom hB hmass hAend hAmid hIH ε hε)

end PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction
