/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# All-positive-natural-level tail estimates

The finite initial-range corrections for the upper and lower volume-tail bounds,
plus their assembly into Proposition I.3.1 for the canonical percolation laws.
-/

module

public import PercLib.CriticalLRP.Analysis.VolumeTailUpper
public import PercLib.CriticalLRP.Analysis.VolumeTailPercolation

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace PercLib.CriticalLRP.Analysis.I32

/-- Extend an asymptotic lower estimate from a real threshold to all positive
natural levels. Positivity of the small-level tails is an explicit premise. -/
theorem lower_tail_nat_of_tendsto_lower
    {g T : ℝ → ℝ} {N κ α : ℝ}
    (hgpos : ∀ x : ℝ, 0 < x → 0 < g x) (hκ : 0 < κ)
    (hbound : ∀ n : ℝ, N ≤ n → κ * (g n) ^ α / n ≤ T n)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → K * (g n) ^ α / n ≤ T n := by
  classical
  let M : ℕ := ⌈N⌉₊
  let S : Finset ℕ := (Finset.range M).filter (fun n => 1 ≤ n)
  let q : ℕ → ℝ := fun n => T n / (g n ^ α / n)
  have hqpos : ∀ n : ℕ, 1 ≤ n → 0 < q n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hgR : 0 < (g n) ^ α / n :=
      div_pos (Real.rpow_pos_of_pos (hgpos _ hnR) α) hnR
    exact div_pos (hpos n hn) hgR
  have hNl : ∀ n : ℕ, M ≤ n → N ≤ (n : ℝ) := by
    intro n hn
    exact (Nat.ceil_le.1 le_rfl).trans (Nat.cast_le.mpr hn)
  by_cases hs : S.Nonempty
  · let R : Finset ℝ := S.image q
    have hR : R.Nonempty := hs.image q
    let K := min κ (R.min' hR)
    have hminpos : 0 < R.min' hR := by
      apply (Finset.lt_min'_iff R hR).2
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
      exact hqpos i (Finset.mem_filter.1 hi).2
    have hK : 0 < K := lt_min hκ hminpos
    refine ⟨K, hK, ?_⟩
    intro n hn
    by_cases hnl : M ≤ n
    · have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      have hgR : 0 ≤ (g n) ^ α / n :=
        div_nonneg (Real.rpow_nonneg (hgpos _ hnR).le α) hnR.le
      calc
        K * (g n) ^ α / n = K * ((g n) ^ α / n) := by ring
        _ ≤ κ * ((g n) ^ α / n) :=
          mul_le_mul_of_nonneg_right (min_le_left κ (R.min' hR)) hgR
        _ ≤ T n := by simpa only [mul_div] using hbound n (hNl n hnl)
    · have hnlt : n < M := Nat.lt_of_not_ge hnl
      have hnS : n ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnlt, hn⟩
      have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      have hgR : 0 < (g n) ^ α / n :=
        div_pos (Real.rpow_pos_of_pos (hgpos _ hnR) α) hnR
      have hqmem : q n ∈ R := by
        apply Finset.mem_image.2
        exact ⟨n, hnS, rfl⟩
      have hratio_le : K ≤ q n :=
        (min_le_right κ (R.min' hR)).trans (Finset.min'_le R (q n) hqmem)
      have hmul := mul_le_mul_of_nonneg_right hratio_le hgR.le
      calc
        K * (g n) ^ α / n = K * ((g n) ^ α / n) := by ring
        _ ≤ q n * ((g n) ^ α / n) := hmul
        _ = T n := by
          dsimp [q]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos (hgpos _ hnR) α)]
  · refine ⟨κ, hκ, ?_⟩
    intro n hn
    by_cases hnl : M ≤ n
    · exact hbound n (hNl n hnl)
    · exfalso
      apply hs
      have hnS : n ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_of_not_ge hnl), hn⟩
      exact ⟨n, hnS⟩


/-- Extend an asymptotic upper estimate from a real threshold to every positive
natural level. Positivity of the small full-law tails is again an explicit premise. -/
theorem upper_tail_nat_of_tendsto_upper
    {g T : ℝ → ℝ} {N κ α : ℝ}
    (hgpos : ∀ x : ℝ, 0 < x → 0 < g x) (hκ : 0 < κ)
    (hbound : ∀ n : ℝ, N ≤ n → T n ≤ κ * (g n) ^ α / n)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < T n) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → T n ≤ K * (g n) ^ α / n := by
  classical
  let M : ℕ := ⌈N⌉₊
  let S : Finset ℕ := (Finset.range M).filter (fun n => 1 ≤ n)
  let q : ℕ → ℝ := fun n => T n / (g n ^ α / n)
  have hqpos : ∀ n : ℕ, 1 ≤ n → 0 < q n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hgR : 0 < (g n) ^ α / n :=
      div_pos (Real.rpow_pos_of_pos (hgpos _ hnR) α) hnR
    exact div_pos (hpos n hn) hgR
  have hNl : ∀ n : ℕ, M ≤ n → N ≤ (n : ℝ) := by
    intro n hn
    exact (Nat.ceil_le.1 le_rfl).trans (Nat.cast_le.mpr hn)
  by_cases hs : S.Nonempty
  · let K := κ + ∑ i ∈ S, q i
    have hsnonneg : 0 ≤ ∑ i ∈ S, q i := by
      apply Finset.sum_nonneg
      intro i hi
      exact (hqpos i (Finset.mem_filter.1 hi).2).le
    have hK : 0 < K := by
      dsimp [K]
      linarith
    refine ⟨K, hK, ?_⟩
    intro n hn
    by_cases hnl : M ≤ n
    · have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      have hgR : 0 ≤ (g n) ^ α / n :=
        div_nonneg (Real.rpow_nonneg (hgpos _ hnR).le α) hnR.le
      calc
        T n ≤ κ * (g n) ^ α / n := hbound n (hNl n hnl)
        _ = κ * ((g n) ^ α / n) := by ring
        _ ≤ K * ((g n) ^ α / n) := by
          apply mul_le_mul_of_nonneg_right ?_ hgR
          exact le_add_of_nonneg_right hsnonneg
        _ = K * (g n) ^ α / n := by ring
    · have hnlt : n < M := Nat.lt_of_not_ge hnl
      have hnS : n ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnlt, hn⟩
      have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      have hgR : 0 < (g n) ^ α / n :=
        div_pos (Real.rpow_pos_of_pos (hgpos _ hnR) α) hnR
      have hratio_le : q n ≤ K := by
        have hratio_sum : q n ≤ ∑ i ∈ S, q i := by
          exact Finset.single_le_sum (s := S) (f := q)
            (fun i hi => (hqpos i (Finset.mem_filter.1 hi).2).le) hnS
        exact hratio_sum.trans (le_add_of_nonneg_left hκ.le)
      calc
        T n = q n * ((g n) ^ α / n) := by
          dsimp [q]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos (hgpos _ hnR) α)]
        _ ≤ K * ((g n) ^ α / n) := mul_le_mul_of_nonneg_right hratio_le hgR.le
        _ = K * (g n) ^ α / n := by ring
  · refine ⟨κ, hκ, ?_⟩
    intro n hn
    by_cases hnl : M ≤ n
    · exact hbound n (hNl n hnl)
    · exfalso
      apply hs
      have hnS : n ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_of_not_ge hnl), hn⟩
      exact ⟨n, hnS⟩


/-- Both directions of Proposition I.3.1 for the canonical volume law, with the
full-law positivity used by the finite initial correction kept explicit. -/
theorem proposition_I_3_1_nat_of_restoration
    {V : Type*} [Countable V]
    {π : ℝ → Sym2 V → unitInterval} {πinf : Sym2 V → unitInterval} {o : V}
    {f g : ℝ → ℝ} {B C a q D c Dbl α : ℝ}
    (hρπ : ∀ r e, π r e ≤ πinf e)
    (hB : 0 < B) (hC : 0 < C) (hc : 0 < c) (hcC : c ≤ C)
    (ha : 0 < a) (hq : 0 < q) (hDbl : 0 < Dbl) (hα : 0 < α)
    (hfin : ∀ᵐ ω ∂edgeMeasure πinf, clusterVol ω o ≠ ⊤)
    (hL1 : ∀ r : ℝ, 1 ≤ r → Integrable (fun x : ℝ => x) (volumeLaw (π r) o))
    (hmeanLower : ∀ r : ℝ, 1 ≤ r → a * r ^ α ≤ mean (volumeLaw (π r) o))
    (hmeanUpper : ∀ r : ℝ, 1 ≤ r → mean (volumeLaw (π r) o) ≤ B * r ^ α)
    (hband : ∀ r : ℝ, 1 ≤ r →
      q ≤ (sizeBiasedBaseLaw (volumeLaw (π r) o)
        (Icc (c * f r) (C * f r))).toReal)
    (hTail : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 1 ≤ r →
      (sizeBiasedBaseLaw (volumeLaw (π r) o) (Iic (δ * f r))).toReal ≤ η)
    (hD : ∀ r : ℝ, 1 ≤ r → ∀ x : V,
      (∑' y : V, ENNReal.ofReal ((shiftProb πinf (π r) (s(x, y)) : unitInterval) : ℝ))
        ≤ ENNReal.ofReal (C * r ^ (-α)))
    (hG : ∀ h : NNReal, ∀ y : V, ghostHits πinf h y ≤ ghostHits πinf h o)
    (hf : ∀ r : ℝ, 1 ≤ r → 0 < f r)
    (hgmono : Monotone g) (hgpos : ∀ x : ℝ, 0 < x → 0 < g x)
    (hdouble : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ Dbl * g x)
    (hgAtTop : Tendsto g atTop atTop) (hgf : ∀ x : ℝ, 0 < x → f (g x) = x)
    (hTailPos : ∀ n : ℕ, 1 ≤ n → 0 < (volumeLaw πinf o (Ici (n : ℝ))).toReal) :
    ∃ Kl Ku : ℝ, 0 < Kl ∧ 0 < Ku ∧
      ∀ n : ℕ, 1 ≤ n → Kl * (g (n : ℝ)) ^ α / n ≤
          (volumeLaw πinf o (Ici (n : ℝ))).toReal ∧
        (volumeLaw πinf o (Ici (n : ℝ))).toReal ≤ Ku * (g (n : ℝ)) ^ α / n := by
  obtain ⟨Nl, κl, hκl, hLower⟩ := exists_volume_tail_lower_of_inverse_doubling
    hρπ hc hcC ha hq hα hfin hL1 hmeanLower hband hgmono hgpos hDbl hdouble hgAtTop hgf
  obtain ⟨Nu, κu, hκu, hUpper⟩ := exists_volume_tail_upper_of_inverse_doubling
    hρπ hB hC hα hfin (fun r hr => by
      have hrpos : 0 < r := one_pos.trans_le hr
      exact lt_of_lt_of_le (mul_pos ha (Real.rpow_pos_of_pos hrpos α)) (hmeanLower r hr))
    hL1 hmeanUpper hD hG hTail hf hgmono hgpos hDbl hdouble hgAtTop hgf
  obtain ⟨Kl, hKl, hLowerNat⟩ := lower_tail_nat_of_tendsto_lower hgpos hκl hLower hTailPos
  obtain ⟨Ku, hKu, hUpperNat⟩ := upper_tail_nat_of_tendsto_upper hgpos hκu hUpper hTailPos
  exact ⟨Kl, Ku, hKl, hKu, fun n hn => ⟨hLowerNat n hn, hUpperNat n hn⟩⟩

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.upper_tail_nat_of_tendsto_upper

#print axioms PercLib.CriticalLRP.Analysis.I32.proposition_I_3_1_nat_of_restoration
