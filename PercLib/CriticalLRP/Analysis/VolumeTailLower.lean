/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Doubling inverse scales and the eventual lower-tail estimate

Scale bookkeeping and measure assembly for Proposition I.3.1(1). The module
proves the inverse-doubling comparison and its application to a family of volume
laws. The full-law tail is allowed to be any uniform upper bound `T n` for the
cutoff tails; `VolumeTailModel` establishes that comparison at the canonical
percolation laws.

The conclusion has an explicit threshold and positive constant. It is not yet a
claim of the source's all-`n ≥ 1` formulation without a finite-initial correction.
-/

module

public import PercLib.CriticalLRP.Analysis.VolumeTailUpToConstants

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Analysis.I32

/-- Iterating `g (2 x) ≤ D g x` while all intermediate arguments remain at
least `1`, written in the descending-half form used for inverse scales. -/
theorem inverse_doubling_half_iter {g : ℝ → ℝ} {D : ℝ}
    (_hgpos : ∀ x : ℝ, 0 < x → 0 < g x) (hD : 0 < D)
    (hd : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x) :
    ∀ {k : ℕ} {x : ℝ}, (2 : ℝ) ^ k ≤ x → g x ≤ D ^ k * g (x / 2 ^ k) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp
  | succ k ih =>
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) _) hx
      have hx2 : (2 : ℝ) ^ k ≤ x / 2 := by
        rw [show (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k by ring] at hx
        linarith
      have hx2pos : 0 < x / 2 := by positivity
      have hx2ge : 1 ≤ x / 2 := by
        have hp : (2 : ℝ) ^ k ≥ 1 := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        have hx' : 2 ≤ x := by
          rw [show (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k by ring] at hx
          have hs : (2 : ℝ) ≤ 2 * 2 ^ k := by
            have hbound : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
            nlinarith
          exact hs.trans hx
        linarith
      have hfirst : g x ≤ D * g (x / 2) := by
        have h := hd (x / 2) hx2ge
        rw [show 2 * (x / 2) = x by ring] at h
        exact h
      have hrec := mul_le_mul_of_nonneg_left (ih hx2) hD.le
      calc
        g x ≤ D * g (x / 2) := hfirst
        _ ≤ D * (D ^ k * g ((x / 2) / 2 ^ k)) := hrec
        _ = D ^ (k + 1) * g (x / 2 ^ (k + 1)) := by
          have heq : (x / 2) / 2 ^ k = x / 2 ^ (k + 1) := by
            rw [pow_succ]
            field_simp
          rw [heq, pow_succ]
          ring

/-- Uniform inverse-scale comparison from doubling on `[1,∞)`. Both the
`c ≤ 1` case (monotonicity alone) and the `c > 1` case (iterated halving)
are included. -/
theorem inverse_doubling_scale_of_le_two {g : ℝ → ℝ} {D c : ℝ}
    (hgmono : Monotone g) (hgpos : ∀ x : ℝ, 0 < x → 0 < g x)
    (hD : 0 < D) (hc : 0 < c)
    (hd : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x) :
    ∃ N K : ℝ, 0 < K ∧ ∀ n : ℝ, N ≤ n → g n ≤ K * g (n / c) := by
  by_cases hc1 : c ≤ 1
  · refine ⟨1, 1, one_pos, fun n hn => ?_⟩
    have hnc : n ≤ n / c := by
      apply (le_div_iff₀ hc).2
      have hx : n * c ≤ n * 1 := mul_le_mul_of_nonneg_left hc1 (zero_le_one.trans hn)
      simpa using hx
    have hmono := hgmono hnc
    simpa using hmono
  · have hcgt : 1 < c := lt_of_not_ge hc1
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt c (by norm_num : (1 : ℝ) < (2 : ℝ))
    refine ⟨(2 : ℝ) ^ k, D ^ k, pow_pos hD _, fun n hn => ?_⟩
    have hbase := inverse_doubling_half_iter hgpos hD hd hn
    have hkc : c ≤ (2 : ℝ) ^ k := hk.le
    have hnpos : 0 < n := lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) _) hn
    have htarget : n / (2 : ℝ) ^ k ≤ n / c :=
      div_le_div_of_nonneg_left hnpos.le hc hk.le
    have hleft := mul_le_mul_of_nonneg_left (hgmono htarget) (pow_nonneg hD.le k)
    exact hbase.trans hleft


/-- Lower tail bound from a uniform size-biased band and a doubling inverse
scale. `T n` is any full-law upper bound for every cutoff tail at level `n`.
The threshold covers both the inverse-doubling comparison and the requirement
that the selected cutoff radius be at least one. -/
theorem exists_lower_tail_of_inverse_doubling
    {μ : ℝ → Measure ℝ} {f g T : ℝ → ℝ} {c C a q D α : ℝ}
    (hbase : ∀ r : ℝ, 1 ≤ r → IsProbabilityMeasure (sizeBiasedBaseLaw (μ r)))
    (hc : 0 < c) (hcC : c ≤ C) (ha : 0 < a) (hq : 0 < q) (hα : 0 < α)
    (hmean : ∀ r : ℝ, 1 ≤ r → a * r ^ α ≤ mean (μ r))
    (hband : ∀ r : ℝ, 1 ≤ r →
      q ≤ (sizeBiasedBaseLaw (μ r) (Icc (c * f r) (C * f r))).toReal)
    (hmono : ∀ r n : ℝ, (μ r (Ici n)).toReal ≤ T n)
    (hgmono : Monotone g) (hgpos : ∀ x : ℝ, 0 < x → 0 < g x)
    (hD : 0 < D) (hdouble : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x)
    (hgAtTop : Tendsto g atTop atTop) (hgf : ∀ x : ℝ, 0 < x → f (g x) = x) :
    ∃ N κ : ℝ, 0 < κ ∧ ∀ n : ℝ, N ≤ n → κ * (g n) ^ α / n ≤ T n := by
  have hC : 0 < C := hc.trans_le hcC
  obtain ⟨N, K, hK, hscale⟩ := inverse_doubling_scale_of_le_two hgmono hgpos hD hc hdouble
  have hscaled : Tendsto (fun n : ℝ => g (n / c)) atTop atTop :=
    hgAtTop.comp (tendsto_id.atTop_div_const hc)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hscaled.eventually (eventually_ge_atTop 1))
  let N₀ := max N (max M 1)
  have hN₀ : ∀ n : ℝ, N₀ ≤ n → (1 ≤ n ∧ N ≤ n ∧ M ≤ n) := by
    intro n hn
    have hnn : N ≤ n ∧ M ≤ n ∧ 1 ≤ n := by
      simpa [N₀, max_le_iff] using hn
    exact ⟨hnn.2.2, hnn.1, hnn.2.1⟩
  have hA : 0 < a * q * c / C := by positivity
  refine ⟨N₀, (a * q * c / C) * K ^ (-α), mul_pos hA (Real.rpow_pos_of_pos hK _), ?_⟩
  intro n hn
  obtain ⟨hn1, hnN, hnM⟩ := hN₀ n hn
  have hnpos : 0 < n := one_pos.trans_le hn1
  set r := g (n / c) with hrdef
  have hr : 1 ≤ r := hM n hnM
  have hrpos : 0 < r := one_pos.trans_le hr
  have hfr : f r = n / c := hgf _ (div_pos hnpos hc)
  let := hbase r hr
  have hmeanpos : 0 < mean (μ r) :=
    lt_of_lt_of_le (mul_pos ha (Real.rpow_pos_of_pos hrpos α)) (hmean r hr)
  have hper : mean (μ r) * (q / (C * f r)) ≤ T n := by
    apply (mean_mul_probLower_div_le_tail_toReal hmeanpos (hband r hr) ?_ hn1 ?_ ?_).trans
      (hmono r n)
    · rw [hfr]
      positivity
    · rw [hfr]
      field_simp
      norm_num
    · rw [hfr]
      exact mul_le_mul_of_nonneg_right hcC (div_nonneg hnpos.le hc.le)
  have hs : g n ≤ K * r := hscale n hnN
  have hsp := Real.rpow_le_rpow (hgpos n hnpos).le hs hα.le
  have hpow : K ^ (-α) * (g n) ^ α ≤ r ^ α := by
    calc
      K ^ (-α) * (g n) ^ α = (g n) ^ α / K ^ α := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hK.le]
        ring
      _ ≤ (K * r) ^ α / K ^ α := by
        exact div_le_div_of_nonneg_right hsp (Real.rpow_pos_of_pos hK α).le
      _ = r ^ α := by
        rw [Real.mul_rpow hK.le hrpos.le]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hK α)]
  calc
    (a * q * c / C) * K ^ (-α) * (g n) ^ α / n =
        (a * q * c / C) * (K ^ (-α) * (g n) ^ α / n) := by ring
    _ ≤ (a * q * c / C) * (r ^ α / n) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hnpos.le) hA.le
    _ = a * r ^ α * (q / (C * f r)) := by
      rw [hfr]
      field_simp [hc.ne', hC.ne', hnpos.ne']
    _ ≤ mean (μ r) * (q / (C * f r)) := by
      have hnonneg : 0 ≤ q / (C * f r) := by
        rw [hfr]
        positivity
      exact mul_le_mul_of_nonneg_right (hmean r hr) hnonneg
    _ ≤ T n := hper

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.inverse_doubling_half_iter
#print axioms PercLib.CriticalLRP.Analysis.I32.inverse_doubling_scale_of_le_two
#print axioms PercLib.CriticalLRP.Analysis.I32.exists_lower_tail_of_inverse_doubling
