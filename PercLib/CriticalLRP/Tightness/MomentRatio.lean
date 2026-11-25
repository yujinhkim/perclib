/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Corollary I.2.5: moment ratios from the universal-tightness tail

Hutchcroft, arXiv:2508.18807v1, Theorem I.2.3 (universal tightness of the maximum cluster
size) states, among other things, the single-cluster exponential tail (I.2.6): for the edian
`M_β(Λ)` of `|K_max(Λ)|`,

  `P_β(|K_u ∩ Λ| ≥ λ M_β(Λ)) ≤ e · P_β(|K_u ∩ Λ| ≥ M_β(Λ)) · exp(-λ/9)`,  `λ ≥ 1`.

Corollary I.2.5 of the paper deduces from it the moment ratio

  `E_β |K_x ∩ W|^{p+q} ⪯_{p,q} M_β(W)^q · E_β |K_x ∩ W|^p`  (`p, q ≥ 0`).

Here we prove this implication for integer exponents `p ≥ 1`, `q ≥ 0`, for an arbitrary
`ℝ≥0∞`-valued integer-valued random variable `X` (all the paper's `|K ∩ W|` have this shape),
with an explicit constant.  The formal statement is `moment_ratio_le`; the exponential-tail
hypothesis (I.2.6) is an explicit named hypothesis, since it is a consequence of the BK
inequality established in [74] and is not reproved here.

The proof is the paper's: layer cake (integration by parts) `E X^k = ∑_n (n^k - (n-1)^k) T_n`,
split the sum at the scale `M`, use the mean-value bound `n^k - (n-1)^k ≤ k n^{k-1}` on the
lower part and the exponential tail on the upper part.
-/
module

public import PercLib.CriticalLRP.Tightness.DiscreteLayerCake
public import PercLib.CriticalLRP.Tightness.TailEstimates
public import PercLib.CriticalLRP.Tightness.MomentRatioAux

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Tightness

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The explicit constant in the moment ratio bound for exponents `p ≥ 1`, `q ≥ 0`. -/
noncomputable def momentConst (p q : ℕ) : ℝ :=
  ((p + q : ℕ) : ℝ) *
    (2 ^ q + Real.exp 1 * 2 ^ (p + q) * ((p + q).factorial : ℝ) * 9 ^ (p + q) * 36)

theorem momentConst_nonneg (p q : ℕ) : 0 ≤ momentConst p q := by
  unfold momentConst
  positivity

/-- **Corollary I.2.5 (integer exponents).**  Let `X ≥ 0` be integer-valued (or `∞`), let
`M ≥ 1` be a median-type scale and suppose the exponential tail bound (I.2.6) holds:
`μ{X ≥ t} ≤ e · μ{X ≥ M} · e^{-t/(9M)}` for all `t ≥ M`.  Then for integers `p ≥ 1`, `q ≥ 0`,
`∫⁻ X^{p+q} ≤ C(p,q) · M^q · ∫⁻ X^p` with `C(p,q) = momentConst p q`, both sides being allowed
to be `∞`. -/
theorem moment_ratio_le {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) {M : ℝ} (hM1 : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | ENNReal.ofReal t ≤ X ω}
      ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal M ≤ X ω})
    (p q : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ
      ≤ ENNReal.ofReal (momentConst p q) * ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
  classical
  have hM0 : (0:ℝ) < M := by linarith
  set k : ℕ := p + q with hkdef
  have hk1 : 1 ≤ k := by omega
  set S : ℕ → ℝ≥0∞ := fun n => μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} with hS
  set TM : ℝ≥0∞ := μ {ω | ENNReal.ofReal M ≤ X ω} with hTM
  have hTMapply : TM = μ {ω | ENNReal.ofReal M ≤ X ω} := hTM
  have hSapply : ∀ n : ℕ, S n = μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := fun n => by rw [hS]
  -- layer cake for exponent `k`
  have hlc : ∫⁻ ω, X ω ^ k ∂μ
      = ∑' n : ℕ, ((((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n) := by
    rw [lintegral_pow_eq_tsum_meas_ge hX hint k hk1]
  -- the two majorants
  set A : ℕ → ℝ≥0∞ := fun n => (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
      ((n : ℝ≥0∞) + 1) ^ (p - 1) * S n with hA
  set B : ℕ → ℝ≥0∞ := fun n => (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
      ((n : ℝ≥0∞) + 1) ^ (k - 1) *
      ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * M)))) * TM with hB
  have hAapply : ∀ n : ℕ, A n = (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
      ((n : ℝ≥0∞) + 1) ^ (p - 1) * S n := fun n => by rw [hA]
  have hBapply : ∀ n : ℕ, B n = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
      ((n : ℝ≥0∞) + 1) ^ (k - 1) *
      ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * M)))) * TM := fun n => by rw [hB]
  have hcasts : ∀ n : ℕ, ENNReal.ofReal ((n : ℝ) + 1) = ((n : ℝ≥0∞) + 1) := by
    intro n
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
    norm_num
  -- termwise bound
  have hterm : ∀ n : ℕ, (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n ≤ A n + B n := by
    intro n
    have hD : ((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k ≤
        (k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1) := pow_succ_sub_pow_le k hk1 n
    by_cases hcase : ((n : ℝ) + 1) ≤ M
    · -- lower part
      have hkq : k - 1 = q + (p - 1) := by omega
      have hMq : ((n : ℝ≥0∞) + 1) ^ q ≤ ENNReal.ofReal ((M + 1) ^ q) := by
        rw [ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ M + 1)]
        refine pow_le_pow_left' ?_ q
        rw [← hcasts n]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      calc (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
          ≤ ((k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1)) * S n := by gcongr
        _ = (k : ℝ≥0∞) * (((n : ℝ≥0∞) + 1) ^ (k - 1) * S n) := by ring
        _ ≤ (k : ℝ≥0∞) * ((ENNReal.ofReal ((M + 1) ^ q) * ((n : ℝ≥0∞) + 1) ^ (p - 1)) *
              S n) := by
            gcongr
            rw [hkq, pow_add]
            exact mul_le_mul_left hMq _
        _ = A n := by rw [hAapply]; ring
        _ ≤ A n + B n := le_self_add
    · -- upper part
      push Not at hcase
      have htail' := htail ((n : ℝ) + 1) (le_of_lt hcase)
      have hset : {ω : Ω | ENNReal.ofReal ((n : ℝ) + 1) ≤ X ω}
          = {ω : Ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := by rw [hcasts n]
      rw [hset] at htail'
      calc (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
          ≤ ((k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1)) * S n := by gcongr
        _ ≤ ((k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1)) *
              (ENNReal.ofReal (Real.exp 1 * Real.exp (-(((n : ℝ) + 1) / (9 * M)))) * TM) := by
            gcongr
        _ = B n := by
            rw [hBapply, ENNReal.ofReal_mul (Real.exp_pos 1).le]
            ring
        _ ≤ A n + B n := self_le_add_left _ _
  -- sum the majorants
  have hsum : ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
      ≤ ∑' n : ℕ, A n + ∑' n : ℕ, B n := by
    calc ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
        ≤ ∑' n : ℕ, (A n + B n) := ENNReal.tsum_le_tsum hterm
      _ = ∑' n : ℕ, A n + ∑' n : ℕ, B n := ENNReal.tsum_add
  -- bound `∑ A`
  have hSA : ∑' n : ℕ, A n ≤ (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
    have hpow := lintegral_pow_eq_tsum_meas_ge (μ := μ) hX hint p hp
    have hcmp : ∑' n : ℕ, ((n : ℝ≥0∞) + 1) ^ (p - 1) * S n ≤ ∫⁻ ω, X ω ^ p ∂μ := by
      rw [hpow]
      refine ENNReal.tsum_le_tsum fun n => ?_
      rw [hSapply]
      exact mul_le_mul_left (pow_sub_pow_ge p hp n) _
    calc ∑' n : ℕ, A n
        = (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
            ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ (p - 1) * S n) := by
          rw [show (∑' n : ℕ, A n) = ∑' n : ℕ, (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
              (((n : ℝ≥0∞) + 1) ^ (p - 1) * S n) from tsum_congr fun n => by rw [hAapply]; ring]
          rw [ENNReal.tsum_mul_left]
      _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by gcongr
  -- bound `∑ B`
  have hSB : ∑' n : ℕ, B n ≤
      (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        (ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
          * (4 * (9 * M)))) * TM := by
    have hc0 : (0:ℝ) < 1 / (9 * M) := by positivity
    have hc1 : 1 / (9 * M) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hte := tsum_pow_mul_exp_neg_succ_le (k - 1) hc0 hc1
    have hexp : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * M))))
        = ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (1 / (9 * M))))) := by
      intro n
      congr 2
      field_simp
    have hcinv : (1 / (9 * M))⁻¹ = 9 * M := by field_simp
    have h4 : 4 / (1 / (9 * M)) = 4 * (9 * M) := by field_simp
    rw [hcinv, h4] at hte
    calc ∑' n : ℕ, B n
        = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * TM *
            ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ (k - 1) *
              ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (1 / (9 * M)))))) := by
          rw [show (∑' n : ℕ, B n) = ∑' n : ℕ, ((k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * TM) *
              (((n : ℝ≥0∞) + 1) ^ (k - 1) *
                ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (1 / (9 * M)))))) from
            tsum_congr fun n => by rw [hBapply, hexp n]; ring]
          rw [ENNReal.tsum_mul_left]
      _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * TM *
            ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
              * (4 * (9 * M))) := by gcongr
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
            (ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
              * (4 * (9 * M)))) * TM := by ring
  -- assemble
  have hfin : ∫⁻ ω, X ω ^ k ∂μ ≤
      (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ +
      (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
          * (4 * (9 * M))) * TM := by
    rw [hlc]
    exact le_trans hsum (add_le_add hSA hSB)
  -- rewrite the second constant and use `M^p * P(X ≥ M) ≤ E X^p`
  have hMeq : ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
        * (4 * (9 * M)))
      = ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36) *
        ENNReal.ofReal (M ^ k) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hMk : M ^ k = M ^ (k - 1) * M := by
      rw [← pow_succ]
      congr 2
      omega
    rw [hMk]
    have h9 : (9 * M) ^ (k - 1) = 9 ^ (k - 1) * M ^ (k - 1) := by rw [mul_pow]
    rw [h9]
    field_simp
    ring
  rw [hMeq] at hfin
  -- final constant manipulations
  set D : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
    with hD
  have hMsplit : ENNReal.ofReal (M ^ k) = ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show k = q + p by omega, pow_add]
  have hTMp : ENNReal.ofReal (M ^ p) * TM ≤ ∫⁻ ω, X ω ^ p ∂μ := by
    rw [hTMapply, ENNReal.ofReal_pow hM0.le]
    exact ofReal_pow_mul_meas_le_lintegral hX hM0.le p
  have hM1 : ENNReal.ofReal ((M + 1) ^ q) ≤ ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (M + 1) ^ q ≤ (2 * M) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * M ^ q := by rw [mul_pow]
  -- bound the two summands
  have hb1 : (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) *
          ∫⁻ ω, X ω ^ p ∂μ := by
    have h1 : (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) ≤
        (k : ℝ≥0∞) * (ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q)) :=
      mul_le_mul_right hM1 (k : ℝ≥0∞)
    have h2 := mul_le_mul_left h1 (∫⁻ ω, X ω ^ p ∂μ)
    calc (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ
        ≤ ((k : ℝ≥0∞) * (ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q))) *
            ∫⁻ ω, X ω ^ p ∂μ := h2
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) *
            ∫⁻ ω, X ω ^ p ∂μ := by ring
  have hb2flat : (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
        (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p)) * TM
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D * ENNReal.ofReal (M ^ q) *
          ∫⁻ ω, X ω ^ p ∂μ := by
    calc (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
          (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p)) * TM
        = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
            ((ENNReal.ofReal (M ^ q)) * (ENNReal.ofReal (M ^ p) * TM)) := by ring
      _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
            (ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ) := by
          gcongr
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D * ENNReal.ofReal (M ^ q) *
            ∫⁻ ω, X ω ^ p ∂μ := by ring
  have hb2 : (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        (D * (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p))) * TM
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D * ENNReal.ofReal (M ^ q) *
          ∫⁻ ω, X ω ^ p ∂μ := by
    rw [show (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        (D * (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p))) * TM
        = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
          (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p)) * TM from by ring]
    exact hb2flat
  rw [hMsplit] at hfin
  -- now: combine constants
  have hconst : (k : ℝ) * 2 ^ q + (k : ℝ) * Real.exp 1 *
      ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
      ≤ momentConst p q := by
    have h2p : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have h9p : (9 : ℝ) ^ (k - 1) ≤ 9 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have hfac : ((k - 1).factorial : ℝ) ≤ ((k).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have step : ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
        ≤ ((2 : ℝ) ^ k * ((k).factorial : ℝ) * 9 ^ k * 36) := by
      have s1 : (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) ≤ (2 : ℝ) ^ k * ((k).factorial : ℝ) :=
        mul_le_mul h2p hfac (by positivity) (by positivity)
      have s2 : (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1)
          ≤ (2 : ℝ) ^ k * ((k).factorial : ℝ) * 9 ^ k :=
        mul_le_mul s1 h9p (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right s2 (by norm_num)
    have h1 : (k : ℝ) * Real.exp 1 * ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
        ≤ (k : ℝ) * Real.exp 1 * ((2 : ℝ) ^ k * ((k).factorial : ℝ) * 9 ^ k * 36) :=
      mul_le_mul_of_nonneg_left step (by positivity)
    have hconst_k : (k : ℝ) * 2 ^ q + (k : ℝ) * Real.exp 1 *
        ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
        ≤ (k : ℝ) * (2 ^ q + Real.exp 1 * 2 ^ k * ((k).factorial : ℝ) * 9 ^ k * 36) := by
      nlinarith [h1]
    have hmeq : (k : ℝ) * (2 ^ q + Real.exp 1 * 2 ^ k * ((k).factorial : ℝ) * 9 ^ k * 36)
        = momentConst p q := by
      rw [momentConst]
    rw [hmeq] at hconst_k
    exact hconst_k
  refine le_trans hfin ?_
  rw [hD] at hb2 ⊢
  have hA2 : (0:ℝ) ≤ (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36 := by positivity
  have hcomb : (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ +
      (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36) *
        ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ
      = ENNReal.ofReal ((k : ℝ) * 2 ^ q + (k : ℝ) * Real.exp 1 *
          ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)) *
        ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
    have e1 : (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) = ENNReal.ofReal ((k : ℝ) * 2 ^ q) :=
      natCast_mul_ofReal k (by positivity)
    have e2 : (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
        = ENNReal.ofReal ((k : ℝ) * Real.exp 1 *
            ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)) := by
      rw [natCast_mul_ofReal k (by positivity),
        ← ENNReal.ofReal_mul (p := (k : ℝ) * Real.exp 1)
          (q := (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36) (by positivity)]
    rw [e1, e2, ← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine le_trans (add_le_add hb1 hb2) (le_trans (le_of_eq hcomb) ?_)
  gcongr

end PercLib.CriticalLRP.Tightness
