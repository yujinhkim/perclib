/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Exponential tail bounds at high temperature

Turn the generic BFS exponential cluster-moment estimate into a tail estimate,
using the genuine infinite-volume cluster and the `epow` power extension.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Natural
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false

@[expose] public section

noncomputable section

open Classical MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-- `epow` with a real base greater than one retains the order at a natural index. -/
theorem le_of_epow_nat_le_of_one_lt (lam : ℝ) (hlam : 1 < lam) (n : ℕ) (b : ℕ∞)
    (h : epow (ENNReal.ofReal lam) (n : ℕ∞) ≤ epow (ENNReal.ofReal lam) b) :
    (n : ℕ∞) ≤ b := by
  by_cases hb : b = ⊤
  · rw [hb]
    exact le_top
  · by_contra hle
    have hlt : b < (n : ℕ∞) := lt_of_not_ge hle
    have hcast : (b.toNat : ℕ∞) < (n : ℕ∞) := by
      rw [ENat.natCast_toNat hb]
      exact hlt
    have hexp : (b.toNat : ℝ) < (n : ℝ) := by exact_mod_cast hcast
    have hbase : (1 : ℝ≥0∞) < ENNReal.ofReal lam := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      exact hlam
    have hpow : (ENNReal.ofReal lam) ^ (b.toNat : ℝ) < (ENNReal.ofReal lam) ^ (n : ℝ) :=
      ENNReal.rpow_lt_rpow_of_exponent_lt hbase ENNReal.ofReal_ne_top hexp
    have hl : (1 : ℝ≥0∞) ≤ ENNReal.ofReal lam := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hlam.le
    rw [← ENat.natCast_toNat hb, epow_natCast (ENNReal.ofReal lam) hl b.toNat,
      epow_natCast (ENNReal.ofReal lam) hl n] at h
    exact (not_le.mpr hpow) h

/-- Markov at `λ^n` converts the extended exponential moment into a genuine exponential
cluster-tail estimate. The cluster is not assumed a priori to be finite. -/
theorem measure_cluster_encard_ge_le_inv_mul_rpow
    {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m) (o : V)
    {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) (n : ℕ) :
    (prodBernoulli p) {ω | (n : ℕ∞) ≤ (cluster ω o).encard} ≤
      ENNReal.ofReal (1 / m) * ((ENNReal.ofReal lam) ^ (n : ℝ))⁻¹ := by
  let ε : ℝ≥0∞ := (ENNReal.ofReal lam) ^ (n : ℝ)
  have hlam0 : 0 ≤ lam := le_trans zero_le_one hlam.le
  have hbase0 : 0 < ENNReal.ofReal lam := ENNReal.ofReal_pos.mpr (by linarith)
  have hε0 : ε ≠ 0 := (ENNReal.rpow_pos hbase0 (ENNReal.ofReal_ne_top)).ne'
  have hεtop : ε ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hεpow : epow (ENNReal.ofReal lam) (n : ℕ∞) = ε :=
    epow_natCast (ENNReal.ofReal lam)
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlam.le) n
  have hmeas : AEMeasurable
      (fun ω => epow (ENNReal.ofReal lam) ((cluster ω o).encard)) (prodBernoulli p) :=
    ((measurable_epow _).comp (measurable_encard_cluster_ENat o)).aemeasurable
  have hmarkov := meas_ge_le_lintegral_div (μ := prodBernoulli p) hmeas hε0 hεtop
  have hmoment := lintegral_epow_encard_cluster_le_inv_mul hrow o hlam.le hm hm1 hcond
  have hset : {ω | ε ≤ epow (ENNReal.ofReal lam) ((cluster ω o).encard)}
      = {ω | (n : ℕ∞) ≤ (cluster ω o).encard} := by
    ext ω
    constructor <;> intro h <;> simp only [Set.mem_ofPred_eq] at h ⊢
    · rw [← hεpow] at h
      have hbase : (1 : ℝ≥0∞) < ENNReal.ofReal lam := by
        rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
        exact hlam
      exact le_of_epow_nat_le_of_one_lt lam hlam _ _ h
    · rw [← hεpow]
      exact epow_mono (ENNReal.ofReal lam)
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlam.le) h
  calc (prodBernoulli p) {ω | (n : ℕ∞) ≤ (cluster ω o).encard}
      = (prodBernoulli p) {ω | ε ≤ epow (ENNReal.ofReal lam) ((cluster ω o).encard)} :=
        congrArg (prodBernoulli p) hset.symm
    _ ≤ (∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)) / ε :=
        hmarkov
    _ ≤ ENNReal.ofReal (1 / m) / ε := ENNReal.div_le_div_right hmoment ε
    _ = ENNReal.ofReal (1 / m) * ε⁻¹ := div_eq_mul_inv (ENNReal.ofReal (1 / m)) ε

end PercLib.CriticalLRP.Exploration.BFS
