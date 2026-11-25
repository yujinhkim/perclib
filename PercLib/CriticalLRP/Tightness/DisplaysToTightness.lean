/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Theorem 2.2 from Theorem 2.3: the conclusion step of universal tightness (I.2.3)

Hutchcroft, *Power-law bounds for critical long-range percolation below the upper-critical
dimension*, arXiv:2008.11197v2, §2.1.

This file formalises the passage

  Theorem 2.3 (displays (2.8) and (2.9))  ==>  Theorem 2.2 (displays (2.5), (2.6), (2.7))

i.e. the arithmetic half of the proof of universal tightness: the disjoint-occurrence product
bounds (2.8)/(2.9) -- proved elsewhere from Lemma 2.4 plus the BK inequality -- are turned into
the exponential tail above the edian (2.5), the lower bound at scale `eps * M` (2.6), and the
single-cluster exponential tail (2.7).  Nothing here uses percolation structure: the input is an
abstract probability measure and an `ℝ≥0∞`-valued integer-valued random variable.

The displays are stated with real `lam >= 1` and natural `k >= 1`, which is the range used in
the proof of Theorem 2.2 in the source (`k = ⌊log_3 α⌋ >= 1` for `α >= 9`, and the auxiliary
scale `3^{-k}(M-1)` of (2.6) is a real number).
-/
module

public import PercLib.CriticalLRP.Tightness.RealExponent

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Percolation

/-! ### The displays (2.8) and (2.9) as explicit hypotheses -/

/-- **Display (2.8)** of arXiv:2008.11197v2, Theorem 2.3: the `3^{k-1}+1`-fold
disjoint-occurrence bound for the maximum cluster size,
`P(|K_max(Λ)| ≥ 3^k λ) ≤ P(|K_max(Λ)| ≥ λ)^{3^{k-1}+1}`.

It is stated for real `lam ≥ 1` and natural `k ≥ 1`; in the paper it is a consequence of
Lemma 2.4 and the BK inequality. -/
def Display28 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (K : Ω → ℝ≥0∞) : Prop :=
  ∀ (lam : ℝ) (k : ℕ), 1 ≤ lam → 1 ≤ k →
    μ {ω | ENNReal.ofReal ((3 : ℝ) ^ k * lam) ≤ K ω} ≤
      (μ {ω | ENNReal.ofReal lam ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1) + 1)

/-- **Display (2.9)** of arXiv:2008.11197v2, Theorem 2.3: the single-cluster
disjoint-occurrence bound, one factor for `|K_u ∩ Λ|` and `3^{k-1}` factors for
`|K_max(Λ)|`. -/
def Display29 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (K X : Ω → ℝ≥0∞) : Prop :=
  ∀ (lam : ℝ) (k : ℕ), 1 ≤ lam → 1 ≤ k →
    μ {ω | ENNReal.ofReal ((3 : ℝ) ^ k * lam) ≤ X ω} ≤
      (μ {ω | ENNReal.ofReal lam ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1)) *
        μ {ω | ENNReal.ofReal lam ≤ X ω}

/-! ### Two real-arithmetic lemmas -/

/-- For `α ≥ 9` there is `k ≥ 1` with `3^k ≤ α` and `α / 9 ≤ 3^{k-1}`: the logarithm step
`k = ⌊log_3 α⌋` of the proof of (2.5)/(2.7), phrased without logarithms. -/
lemma exists_pow_three_interval {α : ℝ} (hα : 9 ≤ α) :
    ∃ k : ℕ, 1 ≤ k ∧ (3 : ℝ) ^ k ≤ α ∧ α / 9 ≤ (3 : ℝ) ^ (k - 1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt α (by norm_num : (1 : ℝ) < 3)
  have hex : ∃ k : ℕ, α < (3 : ℝ) ^ k := ⟨n, hn⟩
  have hspec : α < (3 : ℝ) ^ Nat.find hex := Nat.find_spec hex
  have hfind2 : 2 ≤ Nat.find hex := by
    rcases Nat.lt_or_ge (Nat.find hex) 2 with h | h
    · exfalso
      have hle : (3 : ℝ) ^ Nat.find hex ≤ (3 : ℝ) ^ 1 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at hle
      linarith
    · exact h
  have hlt : Nat.find hex - 1 < Nat.find hex := by omega
  have hge : (3 : ℝ) ^ (Nat.find hex - 1) ≤ α := not_lt.mp (Nat.find_min hex hlt)
  refine ⟨Nat.find hex - 1, by omega, hge, ?_⟩
  have h3 : (3 : ℝ) ^ Nat.find hex = 9 * (3 : ℝ) ^ (Nat.find hex - 1 - 1) := by
    rw [show Nat.find hex = (Nat.find hex - 1 - 1) + 2 from by omega, pow_add]
    norm_num
    ring
  rw [h3] at hspec
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 9)]
  linarith [hspec]

/-- For `0 < ε ≤ 1/9` there is `k ≥ 1` with `3^{k+1} ≤ 1/ε` and `1/(27ε) ≤ 3^{k-1}`: the
logarithm step `k = ⌊log_3(1/ε)⌋ - 1` of the proof of (2.6), phrased without logarithms. -/
lemma exists_pow_three_window {ε : ℝ} (hε0 : 0 < ε) (hε9 : ε ≤ 1 / 9) :
    ∃ k : ℕ, 1 ≤ k ∧ (3 : ℝ) ^ (k + 1) ≤ 1 / ε ∧ 1 / (27 * ε) ≤ (3 : ℝ) ^ (k - 1) := by
  have h9 : (9 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0]
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℝ) < 3)
  have hn' : ¬ ((3 : ℝ) ^ (n + 1) ≤ 1 / ε) := by
    have h3 : (3 : ℝ) ^ n < (3 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) n]
    linarith
  have hex : ∃ j : ℕ, ¬ ((3 : ℝ) ^ (j + 1) ≤ 1 / ε) := ⟨n, hn'⟩
  have hfind2 : 2 ≤ Nat.find hex := by
    rcases Nat.lt_or_ge (Nat.find hex) 2 with h | h
    · exfalso
      have hspec := Nat.find_spec hex
      have hle : (3 : ℝ) ^ (Nat.find hex + 1) ≤ (3 : ℝ) ^ (1 + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h92 : (3 : ℝ) ^ (1 + 1) = 9 := by norm_num
      rw [h92] at hle
      exact hspec (le_trans hle h9)
    · exact h
  have hlt : Nat.find hex - 1 < Nat.find hex := by omega
  have hA : (3 : ℝ) ^ (Nat.find hex - 1 + 1) ≤ 1 / ε := by
    have h := Nat.find_min hex hlt
    rw [not_not] at h
    exact h
  have hB : (1 : ℝ) / ε < (3 : ℝ) ^ (Nat.find hex + 1) := by
    have h := Nat.find_spec hex
    rw [not_le] at h
    exact h
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · simpa [Nat.sub_one_add_one (by omega : Nat.find hex ≠ 0)] using hA
  · have h3 : (3 : ℝ) ^ (Nat.find hex + 1) = 27 * (3 : ℝ) ^ (Nat.find hex - 1 - 1) := by
      rw [show Nat.find hex + 1 = (Nat.find hex - 1 - 1) + 3 from by omega, pow_add]
      norm_num
      ring
    rw [h3] at hB
    have hmul : ε * (1 / ε) < ε * (27 * (3 : ℝ) ^ (Nat.find hex - 1 - 1)) :=
      mul_lt_mul_of_pos_left hB hε0
    have hone : ε * (1 / ε) = 1 := by field_simp
    rw [hone] at hmul
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 27 * ε)]
    linarith [hmul]
/-! ### (2.5): the maximum cluster size has an exponential tail above the edian -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **(2.5) from (2.8)**: if the edian scale `M` satisfies `P(K ≥ M) ≤ e^{-1}` and the
`3^{k-1}+1`-fold bound (2.8) holds, then `P(K ≥ t) ≤ exp(-t/(9M))` for every `t ≥ M`.

This is the `α ≥ 9` part of the proof of Theorem 2.2 in arXiv:2008.11197v2 (the `α ≤ 9` part
is monotonicity together with `e^{-1} ≤ exp(-α/9)`). -/
theorem tailMax_of_display28 {K : Ω → ℝ≥0∞} {M : ℕ} (h28 : Display28 μ K) (hM1 : 1 ≤ M)
    (hmed : μ {ω | (M : ℝ≥0∞) ≤ K ω} ≤ ENNReal.ofReal (Real.exp (-1))) :
    TailMaxI24 μ K M := by
  intro t ht
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have h9M : (0 : ℝ) < 9 * (M : ℝ) := by positivity
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hmed' : μ {ω | ENNReal.ofReal (M : ℝ) ≤ K ω} ≤ ENNReal.ofReal (Real.exp (-1)) := by
    simpa [ENNReal.ofReal_natCast] using hmed
  rcases lt_or_ge t (9 * (M : ℝ)) with hlt | hge
  · have hmono : μ {ω | ENNReal.ofReal t ≤ K ω} ≤ μ {ω | ENNReal.ofReal (M : ℝ) ≤ K ω} :=
      measure_mono (fun ω hω => by
        simp only [mem_ofPred_eq] at hω ⊢
        exact le_trans (ENNReal.ofReal_le_ofReal ht) hω)
    refine le_trans hmono (le_trans hmed' ?_)
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_exp]
    have hq : t / (9 * (M : ℝ)) ≤ 1 := by
      rw [div_le_iff₀ h9M]
      linarith
    linarith
  · set α : ℝ := t / (M : ℝ) with hαdef
    have hα : 9 ≤ α := by
      rw [hαdef, le_div_iff₀ hMpos]
      linarith
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_pow_three_interval hα
    have hstep : μ {ω | ENNReal.ofReal t ≤ K ω} ≤
        μ {ω | ENNReal.ofReal ((3 : ℝ) ^ k * (M : ℝ)) ≤ K ω} := by
      apply measure_mono
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      refine le_trans ?_ hω
      apply ENNReal.ofReal_le_ofReal
      have hMle : (3 : ℝ) ^ k * (M : ℝ) ≤ α * (M : ℝ) := by
        nlinarith [hk2, hMpos]
      have hαM : α * (M : ℝ) = t := by
        rw [hαdef]
        field_simp
      linarith
    have hquot : t / (9 * (M : ℝ)) = α / 9 := by
      rw [hαdef]
      field_simp
    refine le_trans hstep (le_trans (h28 (M : ℝ) k hMreal hk1) ?_)
    calc (μ {ω | ENNReal.ofReal (M : ℝ) ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1) + 1)
        ≤ (ENNReal.ofReal (Real.exp (-1))) ^ ((3 : ℕ) ^ (k - 1) + 1) :=
          pow_le_pow_left₀ zero_le hmed' _
      _ = ENNReal.ofReal (Real.exp (-((((3 : ℕ) ^ (k - 1) + 1 : ℕ)) : ℝ))) := by
          rw [← ENNReal.ofReal_pow (Real.exp_pos (-1)).le]
          congr 1
          rw [← Real.exp_nat_mul]
          push_cast
          ring
      _ ≤ ENNReal.ofReal (Real.exp (-(t / (9 * (M : ℝ))))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.exp_le_exp, hquot]
          have hcast : ((((3 : ℕ) ^ (k - 1) + 1 : ℕ)) : ℝ) = (3 : ℝ) ^ (k - 1) + 1 := by
            push_cast
            ring
          rw [hcast]
          linarith

/-- **(2.7) from (2.9)**: if `P(|K_max| ≥ M) ≤ e^{-1}` and the single-cluster
disjoint-occurrence bound (2.9) holds, then
`P(|K_u ∩ Λ| ≥ t) ≤ e · P(|K_u ∩ Λ| ≥ M) · exp(-t/(9M))` for every `t ≥ M`. -/
theorem tailSingle_of_display29 {K X : Ω → ℝ≥0∞} {M : ℕ} (h29 : Display29 μ K X)
    (hM1 : 1 ≤ M) (hmed : μ {ω | (M : ℝ≥0∞) ≤ K ω} ≤ ENNReal.ofReal (Real.exp (-1))) :
    TailI26 μ X M := by
  intro t ht
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have h9M : (0 : ℝ) < 9 * (M : ℝ) := by positivity
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hmed' : μ {ω | ENNReal.ofReal (M : ℝ) ≤ K ω} ≤ ENNReal.ofReal (Real.exp (-1)) := by
    simpa [ENNReal.ofReal_natCast] using hmed
  rcases lt_or_ge t (9 * (M : ℝ)) with hlt | hge
  · have hmono : μ {ω | ENNReal.ofReal t ≤ X ω} ≤ μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} :=
      measure_mono (fun ω hω => by
        simp only [mem_ofPred_eq] at hω ⊢
        exact le_trans (ENNReal.ofReal_le_ofReal ht) hω)
    have hone : (1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * (M : ℝ))))) := by
      rw [ENNReal.one_le_ofReal]
      have hq : t / (9 * (M : ℝ)) ≤ 1 := by
        rw [div_le_iff₀ h9M]
        linarith
      have hexp : Real.exp (-1 : ℝ) ≤ Real.exp (-(t / (9 * (M : ℝ)))) := by
        rw [Real.exp_le_exp]
        linarith
      have hone' : (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by
        rw [← Real.exp_add]
        norm_num
      calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := hone'
        _ ≤ Real.exp 1 * Real.exp (-(t / (9 * (M : ℝ)))) :=
            mul_le_mul_of_nonneg_left hexp (Real.exp_pos 1).le
    calc μ {ω | ENNReal.ofReal t ≤ X ω}
        ≤ μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} := hmono
      _ = 1 * μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * (M : ℝ))))) *
            μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} := by
          exact mul_le_mul_of_nonneg_right hone zero_le
  · set α : ℝ := t / (M : ℝ) with hαdef
    have hα : 9 ≤ α := by
      rw [hαdef, le_div_iff₀ hMpos]
      linarith
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_pow_three_interval hα
    have hstep : μ {ω | ENNReal.ofReal t ≤ X ω} ≤
        μ {ω | ENNReal.ofReal ((3 : ℝ) ^ k * (M : ℝ)) ≤ X ω} := by
      apply measure_mono
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      refine le_trans ?_ hω
      apply ENNReal.ofReal_le_ofReal
      have hMle : (3 : ℝ) ^ k * (M : ℝ) ≤ α * (M : ℝ) := by
        nlinarith [hk2, hMpos]
      have hαM : α * (M : ℝ) = t := by
        rw [hαdef]
        field_simp
      linarith
    have hquot : t / (9 * (M : ℝ)) = α / 9 := by
      rw [hαdef]
      field_simp
    refine le_trans hstep (le_trans (h29 (M : ℝ) k hMreal hk1) ?_)
    have hpow : (μ {ω | ENNReal.ofReal (M : ℝ) ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1)) ≤
        ENNReal.ofReal (Real.exp (-(t / (9 * (M : ℝ))))) := by
      calc (μ {ω | ENNReal.ofReal (M : ℝ) ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1))
          ≤ (ENNReal.ofReal (Real.exp (-1))) ^ ((3 : ℕ) ^ (k - 1)) :=
            pow_le_pow_left₀ zero_le hmed' _
        _ = ENNReal.ofReal (Real.exp (-((((3 : ℕ) ^ (k - 1) : ℕ)) : ℝ))) := by
            rw [← ENNReal.ofReal_pow (Real.exp_pos (-1)).le]
            congr 1
            rw [← Real.exp_nat_mul]
            push_cast
            ring
        _ ≤ ENNReal.ofReal (Real.exp (-(t / (9 * (M : ℝ))))) := by
            apply ENNReal.ofReal_le_ofReal
            rw [Real.exp_le_exp, hquot]
            have hcast : ((((3 : ℕ) ^ (k - 1) : ℕ)) : ℝ) = (3 : ℝ) ^ (k - 1) := by
              push_cast
              ring
            rw [hcast]
            linarith
    calc (μ {ω | ENNReal.ofReal (M : ℝ) ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1)) *
          μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω}
        ≤ ENNReal.ofReal (Real.exp (-(t / (9 * (M : ℝ))))) *
            μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} := by
          exact mul_le_mul_of_nonneg_right hpow zero_le
      _ ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * (M : ℝ))))) *
            μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} := by
          apply mul_le_mul_of_nonneg_right _ zero_le
          apply ENNReal.ofReal_le_ofReal
          have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          calc Real.exp (-(t / (9 * (M : ℝ))))
              = 1 * Real.exp (-(t / (9 * (M : ℝ)))) := (one_mul _).symm
            _ ≤ Real.exp 1 * Real.exp (-(t / (9 * (M : ℝ)))) :=
                mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- **(2.6) from (2.8)**: if `M` is the edian of `K` (`P(K ≥ M) ≤ e^{-1}` and `M` minimal with
that property) and (2.8) holds, then `P(K < εM) ≤ 27ε` for `0 < ε ≤ 1`.

The three cases are those of the source: `εM < 1` is empty because `K ≥ 1` pointwise; `9ε ≥ 1`
is trivial; and for `εM ≥ 1 > 9ε` one applies (2.8) at the real scale `3^{-k}(M-1) ≥ εM`. -/
theorem lower_of_display28 {K : Ω → ℝ≥0∞} {M : ℕ} (hK : Measurable K)
    (hKpos : ∀ ω, 1 ≤ K ω) (h28 : Display28 μ K) (hM1 : 1 ≤ M)
    (hmin : ∀ n : ℕ, n < M → ENNReal.ofReal (Real.exp (-1)) < μ {ω | (n : ℝ≥0∞) ≤ K ω}) :
    LowerI25 μ K M := by
  intro ε hε0 hε1
  rcases lt_or_ge (ε * (M : ℝ)) 1 with hsmall | hbig
  · have hempty : {ω | K ω < ENNReal.ofReal (ε * (M : ℝ))} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      refine le_trans (ENNReal.ofReal_le_one.mpr (le_of_lt hsmall)) (hKpos ω)
    rw [hempty, measure_empty]
    exact zero_le
  rcases lt_or_ge (9 * ε) 1 with h9 | h9
  · -- main case: `εM ≥ 1` and `9ε < 1`
    have hε9 : ε ≤ 1 / 9 := by linarith
    have hMbig : (9 : ℝ) ≤ (M : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hε9 hε0.le, hε0, hbig]
    obtain ⟨k, hk1, hkA, hkB⟩ := exists_pow_three_window hε0 hε9
    have h3kpos : (0 : ℝ) < (3 : ℝ) ^ k := pow_pos (by norm_num) k
    have h3k1 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by
      rw [pow_succ]
      ring
    -- `3ε ≤ (3^k)⁻¹`
    have hkinv : 3 * ε ≤ ((3 : ℝ) ^ k)⁻¹ := by
      have hkey : 3 * ε * (3 : ℝ) ^ k ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hkA hε0.le
        rw [h3k1] at h
        have hεinv : ε * (1 / ε) = 1 := by field_simp
        calc 3 * ε * (3 : ℝ) ^ k = ε * (3 * (3 : ℝ) ^ k) := by ring
          _ ≤ ε * (1 / ε) := h
          _ = 1 := hεinv
      rw [show ((3 : ℝ) ^ k)⁻¹ = 1 / (3 : ℝ) ^ k from (one_div _).symm, le_div_iff₀ h3kpos]
      linarith
    -- the auxiliary real scale `3^{-k}(M-1)`
    set lam : ℝ := ((3 : ℝ) ^ k)⁻¹ * ((M : ℝ) - 1) with hlam
    have h2 : ε * (M : ℝ) ≤ 3 * ε * ((M : ℝ) - 1) := by
      nlinarith [hε0, hMbig, mul_le_mul_of_nonneg_left hMbig hε0.le]
    have h1 : 3 * ε * ((M : ℝ) - 1) ≤ lam := by
      rw [hlam]
      exact mul_le_mul_of_nonneg_right hkinv (by linarith)
    have hlam1 : 1 ≤ lam := by linarith
    have hEven : (3 : ℝ) ^ k * lam = (M : ℝ) - 1 := by
      rw [hlam, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt h3kpos), one_mul]
    -- apply (2.8) at the real scale `lam`
    have hdisp := h28 lam k hlam1 hk1
    rw [hEven] at hdisp
    have hmin' : ENNReal.ofReal (Real.exp (-1)) < μ {ω | (M - 1 : ℕ) ≤ K ω} :=
      hmin (M - 1) (by omega)
    have hmin'' : ENNReal.ofReal (Real.exp (-1)) <
        μ {ω | ENNReal.ofReal ((M : ℝ) - 1) ≤ K ω} := by
      have hcast : ((M : ℝ) - 1) = ((M - 1 : ℕ) : ℝ) := by
        rw [← Nat.cast_one, ← Nat.cast_sub hM1]
      rw [hcast]
      simpa [ENNReal.ofReal_natCast] using hmin'
    have hchain : ENNReal.ofReal (Real.exp (-1)) ≤
        (μ {ω | ENNReal.ofReal lam ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1) + 1) :=
      le_trans hmin''.le hdisp
    have hmono' : μ {ω | ENNReal.ofReal lam ≤ K ω} ≤
        μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω} :=
      measure_mono (fun ω hω => by
        simp only [mem_ofPred_eq] at hω ⊢
        exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hω)
    have hfin : ENNReal.ofReal (Real.exp (-1)) ≤
        (μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1) + 1) :=
      le_trans hchain (pow_le_pow_left₀ zero_le hmono' _)
    -- pass to real numbers
    set q : ℝ := (μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω}).toReal with hq
    have hq1 : q ≤ 1 := by
      have hle : μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω} ≤ 1 := by
        calc μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω} ≤ μ Set.univ :=
              measure_mono (subset_univ _)
          _ = 1 := measure_univ
      have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle
      simpa [hq] using h
    have hqpow : Real.exp (-1) ≤ q ^ ((3 : ℕ) ^ (k - 1) + 1) := by
      have hnt : (μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω}) ^ ((3 : ℕ) ^ (k - 1) + 1) ≠ ⊤ :=
        ENNReal.pow_ne_top (measure_ne_top μ _)
      have h := ENNReal.toReal_mono hnt hfin
      rw [ENNReal.toReal_ofReal (Real.exp_pos (-1)).le, ENNReal.toReal_pow] at h
      simpa [hq] using h
    have hNpos : (0 : ℝ) < (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ) := by positivity
    have hroot : Real.exp (-(1 / (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ))) ≤ q := by
      have heq : (Real.exp (-(1 / (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ)))) ^ ((3 : ℕ) ^ (k - 1) + 1)
          = Real.exp (-1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
      rw [← heq] at hqpow
      exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by positivity) (by positivity)).mp hqpow
    -- the complement
    have hmeas : MeasurableSet {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω} :=
      measurableSet_le measurable_const hK
    have hset : {ω | K ω < ENNReal.ofReal (ε * (M : ℝ))} =
        {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    rw [hset, measure_compl hmeas (measure_ne_top μ _), measure_univ]
    have hsub : μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω} ≤ 1 := by
      calc μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω} ≤ μ Set.univ :=
            measure_mono (subset_univ _)
        _ = 1 := measure_univ
    have htoReal : (1 - μ {ω | ENNReal.ofReal (ε * (M : ℝ)) ≤ K ω}).toReal = 1 - q := by
      rw [ENNReal.toReal_sub_of_le hsub (by simp), ENNReal.toReal_one, hq]
    rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sub_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤))
      (by positivity), htoReal]
    have step1 : 1 - q ≤ 1 - Real.exp (-(1 / (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ))) := by
      linarith
    have step2 : 1 - Real.exp (-(1 / (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ))) ≤
        1 / (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ) := by
      have h := Real.add_one_le_exp (-(1 / (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ)))
      linarith
    have step3 : 1 / (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ) ≤ 27 * ε := by
      have hcast2 : ((((3 : ℕ) ^ (k - 1) + 1 : ℕ)) : ℝ) = (3 : ℝ) ^ (k - 1) + 1 := by
        push_cast
        ring
      have hN : 1 / (27 * ε) ≤ (((3 : ℕ) ^ (k - 1) + 1 : ℕ) : ℝ) := by
        rw [hcast2]
        linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 27 * ε)] at hN
      rw [div_le_iff₀ hNpos]
      linarith
    linarith
  · -- trivial case: `9ε ≥ 1`
    have hle1 : μ {ω | K ω < ENNReal.ofReal (ε * (M : ℝ))} ≤ 1 := by
      calc μ {ω | K ω < ENNReal.ofReal (ε * (M : ℝ))} ≤ μ Set.univ :=
            measure_mono (subset_univ _)
        _ = 1 := measure_univ
    refine le_trans hle1 ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    linarith


/-- **The concentration ("tightness") form of Theorem 2.2**: with the same inputs, `K` lies in the
band `[εM, αM)` with probability at least `1 - (27ε + exp(-α/9))`.  This is the statement that
the maximum cluster size is of the same order as its edian with high probability, and it is
obtained from (2.5) and (2.6) by a union bound only. -/
theorem band_of_displays {K : Ω → ℝ≥0∞} {M : ℕ} (hK : Measurable K)
    (hKpos : ∀ ω, 1 ≤ K ω) (h28 : Display28 μ K) (hM1 : 1 ≤ M)
    (hmed : μ {ω | (M : ℝ≥0∞) ≤ K ω} ≤ ENNReal.ofReal (Real.exp (-1)))
    (hmin : ∀ n : ℕ, n < M → ENNReal.ofReal (Real.exp (-1)) < μ {ω | (n : ℝ≥0∞) ≤ K ω})
    {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    μ {ω | K ω < ENNReal.ofReal (ε * (M : ℝ)) ∨ ENNReal.ofReal (α * (M : ℝ)) ≤ K ω} ≤
      ENNReal.ofReal (27 * ε) + ENNReal.ofReal (Real.exp (-(α / 9))) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have h24 := tailMax_of_display28 h28 hM1 hmed (t := α * (M : ℝ)) (by nlinarith)
  have h25 := lower_of_display28 hK hKpos h28 hM1 hmin ε hε0 hε1
  have hquot : α * (M : ℝ) / (9 * (M : ℝ)) = α / 9 := by
    field_simp
  rw [hquot] at h24
  have hsub : {ω | K ω < ENNReal.ofReal (ε * (M : ℝ)) ∨
      ENNReal.ofReal (α * (M : ℝ)) ≤ K ω} ⊆
      {ω | K ω < ENNReal.ofReal (ε * (M : ℝ))} ∪ {ω | ENNReal.ofReal (α * (M : ℝ)) ≤ K ω} :=
    fun ω hω => hω
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  exact add_le_add h25 h24

end Abstract

/-! ### Theorem 2.2 at the paper's edian scale `M_β(W)` of a finite window -/

section Concrete

variable {V : Type*} [Countable V]

/-- `|K_v ∩ W| ≥ 1` whenever `v ∈ W`: the cluster of `v` always meets `W` in `v` itself. -/
lemma one_le_clusterVolIn (ω : Config V) {v : V} {W : Set V} (h : v ∈ W) :
    1 ≤ clusterVolIn ω v W := by
  rw [clusterVolIn_eq_tsum]
  have hmem : v ∈ cluster ω v ∩ W := ⟨cluster_mem_self ω v, h⟩
  have hterm : ((cluster ω v ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) v) = 1 := by
    rw [Set.indicator_of_mem hmem]
  calc (1 : ℝ≥0∞) = ((cluster ω v ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) v) := hterm.symm
    _ ≤ ∑' w : V, ((cluster ω v ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) w) := ENNReal.le_tsum v

/-- `|K_max(W)| ≥ 1` for a non-empty window: some cluster meets `W`. -/
lemma one_le_clusterMaxVol {W : Finset V} (hW : W.Nonempty) (ω : Config V) :
    1 ≤ clusterMaxVol ω W := by
  obtain ⟨w, hw⟩ := hW
  exact le_trans (one_le_clusterVolIn ω (v := w) (W := (W : Set V)) hw)
    (clusterVolIn_le_clusterMaxVol ω hw)

/-- **Display (2.5) from (2.8)** at the paper's scale `M_β(W) = edianMaxVol`. -/
theorem tailMaxI24_at_edian {μ : Measure (Config V)} [IsProbabilityMeasure μ] (W : Finset V)
    (h28 : Display28 μ (fun ω => clusterMaxVol ω W)) :
    TailMaxI24 μ (fun ω => clusterMaxVol ω W) (edianMaxVol μ W (exists_edianMaxVol W)) :=
  tailMax_of_display28 h28 (one_le_edianMaxVol W (exists_edianMaxVol W))
    (edianMaxVol_spec W (exists_edianMaxVol W))

/-- **Display (2.6) from (2.8)** at the paper's scale `M_β(W) = edianMaxVol`. -/
theorem lowerI25_at_edian {μ : Measure (Config V)} [IsProbabilityMeasure μ] {W : Finset V}
    (hW : W.Nonempty) (h28 : Display28 μ (fun ω => clusterMaxVol ω W)) :
    LowerI25 μ (fun ω => clusterMaxVol ω W) (edianMaxVol μ W (exists_edianMaxVol W)) :=
  lower_of_display28 (measurable_clusterMaxVol W) (fun ω => one_le_clusterMaxVol hW ω) h28
    (one_le_edianMaxVol W (exists_edianMaxVol W))
    (fun _n hn => edianOf_min (μ := μ) (X := fun ω => clusterMaxVol ω W)
      (hex := exists_edianMaxVol W) hn)

/-- **Display (2.7) from (2.9)** at the paper's scale, for the truncated cluster volume. -/
theorem tailI26_at_clusterVolIn {μ : Measure (Config V)} [IsProbabilityMeasure μ]
    (W : Finset V) (v : V)
    (h29 : Display29 μ (fun ω => clusterMaxVol ω W) (fun ω => clusterVolIn ω v (W : Set V))) :
    TailI26 μ (fun ω => clusterVolIn ω v (W : Set V)) (edianMaxVol μ W (exists_edianMaxVol W)) :=
  tailSingle_of_display29 h29 (one_le_edianMaxVol W (exists_edianMaxVol W))
    (edianMaxVol_spec W (exists_edianMaxVol W))

/-- **Theorem 2.2 from Theorem 2.3**, at the paper's scale: displays (2.8) and (2.9) imply the
whole universal-tightness hypothesis bundle (I.2.4)+(I.2.6) at the edian `M_β(W)`. -/
theorem universalTightnessI23_of_displays {μ : Measure (Config V)} [IsProbabilityMeasure μ]
    (W : Finset V) (v : V)
    (h28 : Display28 μ (fun ω => clusterMaxVol ω W))
    (h29 : Display29 μ (fun ω => clusterMaxVol ω W) (fun ω => clusterVolIn ω v (W : Set V))) :
    UniversalTightnessI23 μ (fun ω => clusterMaxVol ω W)
      (fun ω => clusterVolIn ω v (W : Set V)) (edianMaxVol μ W (exists_edianMaxVol W)) :=
  ⟨one_le_edianMaxVol W (exists_edianMaxVol W), tailMaxI24_at_edian W h28,
    tailI26_at_clusterVolIn W v h29⟩

/-- **The concentration form of Theorem 2.2 at the paper's edian scale `M_β(W)`**: the maximum
cluster size lies in `[ε M_β(W), α M_β(W))` with probability at least `1 - 27ε - exp(-α/9)`. -/
theorem band_at_edian {μ : Measure (Config V)} [IsProbabilityMeasure μ] {W : Finset V}
    (hW : W.Nonempty) (h28 : Display28 μ (fun ω => clusterMaxVol ω W))
    {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    μ {ω | clusterMaxVol ω W <
          ENNReal.ofReal (ε * ((edianMaxVol μ W (exists_edianMaxVol W) : ℕ) : ℝ)) ∨
        ENNReal.ofReal (α * ((edianMaxVol μ W (exists_edianMaxVol W) : ℕ) : ℝ)) ≤
          clusterMaxVol ω W} ≤
      ENNReal.ofReal (27 * ε) + ENNReal.ofReal (Real.exp (-(α / 9))) :=
  band_of_displays (measurable_clusterMaxVol W) (fun ω => one_le_clusterMaxVol hW ω) h28
    (one_le_edianMaxVol W (exists_edianMaxVol W))
    (edianMaxVol_spec W (exists_edianMaxVol W))
    (fun _n hn => edianOf_min (μ := μ) (X := fun ω => clusterMaxVol ω W)
      (hex := exists_edianMaxVol W) hn) hα hε0 hε1

/-- **Corollary I.2.5 from the displays**: the moment ratio at the edian scale now depends only on
(2.8) and (2.9), with all edian bookkeeping discharged. -/
theorem corollary_I_2_5_at_edian_of_displays {μ : Measure (Config V)} [IsProbabilityMeasure μ]
    (W : Finset V) (v : V) (hv : v ∈ W)
    (h28 : Display28 μ (fun ω => clusterMaxVol ω W))
    (h29 : Display29 μ (fun ω => clusterMaxVol ω W) (fun ω => clusterVolIn ω v (W : Set V)))
    (p q : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, clusterVolIn ω v (W : Set V) ^ (p + q) ∂μ ≤
      ENNReal.ofReal (Tightness.momentConst p q) *
        ENNReal.ofReal ((edianMaxVol μ W (exists_edianMaxVol W) : ℝ) ^ q) *
        ∫⁻ ω, clusterVolIn ω v (W : Set V) ^ p ∂μ :=
  corollary_I_2_5_at_edian v W hv (universalTightnessI23_of_displays W v h28 h29) p q hp

end Concrete

end PercLib.CriticalLRP.Percolation
