/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# High-temperature BFS cluster moments

Accepted from independent submission `smwpdapl6` direction D2.
Generic independent edge percolation under a uniform finite-partial row-sum
bound; no source-critical or cutoff instantiation is asserted here.
-/
module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Natural cluster moments from the exponential moment

Swarm `smwpdplm2` (member m2).  The scalar transfer of `PROOF.md` Lemma 6.1 applied to the
committed exponential-moment bound: for `λ > 1` and every `k`, the `k`-th moment of the
cluster volume is at most `C · k! / (log λ)^k` whenever `E[λ^{|K_o|}] ≤ C`.

The a.s. finiteness of the cluster (needed to replace `λ^{|K|}` by a real power of
`|K| = (cluster).encard.toNat`) is *derived* here from the exponential bound, not assumed.
-/
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Cluster
public import PercLib.Probability.Exploration.MomentBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open Classical MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open PercLib.Probability.ExplorationEnvelope
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-- **An exponential moment bound forces the cluster to be a.s. finite.** -/
theorem ae_encard_cluster_ne_top_of_epow_le {μ : Measure (Config V)} {o : V} {lam C : ℝ}
    (hlam : 1 < lam)
    (hint : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂μ ≤ ENNReal.ofReal C) :
    ∀ᵐ ω ∂μ, (cluster ω o).encard ≠ ⊤ := by
  have hmeas : Measurable fun ω : Config V => (cluster ω o).encard := measurable_encard_cluster_ENat o
  have hlt : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hint
  have hae := ae_lt_top ((measurable_epow _).comp hmeas) hlt
  have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by linarith : (0:ℝ) < lam)]
    exact hlam
  filter_upwards [hae] with ω hω htop
  simp only [Function.comp_apply] at hω
  rw [htop, epow_top_of_one_lt _ h1] at hω
  exact absurd hω (not_lt.mpr le_top)

/-- **The scalar transfer of `PROOF.md` Lemma 6.1.**  From `E[λ^{|K_o|}] ≤ C` and `λ > 1`,
every natural moment of the cluster volume is at most `C k! / (log λ)^k`. -/
theorem lintegral_pow_encard_cluster_le {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m)
    (o : V) {lam C : ℝ} (hlam : 1 < lam)
    (hC : ∀ n : ℕ, lam * envelope m lam n ≤ C) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (C * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := by
  have hlog : 0 < Real.log lam := Real.log_pos hlam
  have hc0 : (0:ℝ) ≤ (k.factorial : ℝ) / (Real.log lam) ^ k := by positivity
  have hint : ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal C :=
    lintegral_epow_cluster_le_of_envelope_bound hrow o hlam.le hC
  have hae := ae_encard_cluster_ne_top_of_epow_le hlam hint
  have hpt : ∀ᵐ ω ∂(prodBernoulli p),
      ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k)
        ≤ ENNReal.ofReal ((k.factorial : ℝ) / (Real.log lam) ^ k)
            * epow (ENNReal.ofReal lam) ((cluster ω o).encard) := by
    filter_upwards [hae] with ω hω
    have hx : (0:ℝ) ≤ ((cluster ω o).encard.toNat : ℝ) := by positivity
    have h1 := pow_le_factorial_div_log_mul_rpow hlam k hx
    have hpow : epow (ENNReal.ofReal lam) ((cluster ω o).encard)
        = ENNReal.ofReal (lam ^ ((cluster ω o).encard.toNat : ℝ)) := by
      conv_lhs => rw [← ENat.natCast_toNat hω]
      rw [epow_ofReal_pow hlam.le, Real.rpow_natCast]
    rw [hpow, ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal h1
  refine le_trans (lintegral_mono_ae hpt) ?_
  have hmeas : Measurable fun ω : Config V => epow (ENNReal.ofReal lam) ((cluster ω o).encard) :=
    (measurable_epow _).comp (measurable_encard_cluster_ENat o)
  rw [lintegral_const_mul _ hmeas]
  refine le_trans (mul_le_mul' le_rfl hint) ?_
  exact le_of_eq (by
    rw [mul_comm C ((k.factorial : ℝ) / (Real.log lam) ^ k)]
    exact (ENNReal.ofReal_mul hc0).symm)

/-- **The natural cluster moments, `0 < m ≤ 1`, sharp constant.** -/
theorem lintegral_pow_encard_cluster_le_inv_mul {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((1 / m) * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := by
  refine lintegral_pow_encard_cluster_le hrow o hlam (C := 1 / m) (fun n => ?_) k
  have hu : envelope m lam n ≤ 1 / (m * lam) := envelope_le_inv_mul hm hm1 hlam.le hcond n
  have hpos : (0:ℝ) < m * lam := by nlinarith
  have h1 : lam * envelope m lam n ≤ lam * (1 / (m * lam)) :=
    mul_le_mul_of_nonneg_left hu (by linarith)
  have h2 : lam * (1 / (m * lam)) = 1 / m := by field_simp
  linarith [h1, h2.le]

/-- **The natural cluster moments, `m = 0`.** -/
theorem lintegral_pow_encard_cluster_le_zero {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : m = 0) (o : V) {lam : ℝ} (hlam : 1 < lam) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (lam * ((k.factorial : ℝ) / (Real.log lam) ^ k)) := by
  refine lintegral_pow_encard_cluster_le hrow o hlam (C := lam) (fun n => ?_) k
  rw [hm]
  induction n with
  | zero => rw [envelope_zero]; linarith
  | succ n ih =>
      rw [envelope_succ, envelopeStep]
      simp only [zero_mul, Real.exp_zero]
      exact le_of_eq (mul_one lam)


/-! ### An admissible parameter exists -/

/-- **Theorem 2 of `PROOF.md`, exponential form.**  For `0 < m < 1` there is `λ > 1` with a
uniform exponential cluster moment bound. -/
theorem exists_lam_lintegral_epow_encard_cluster_le {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) (o : V) :
    ∃ lam : ℝ, 1 < lam ∧
      ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
        ≤ ENNReal.ofReal (1 / m) := by
  obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hm hm1
  exact ⟨lam, hlam, lintegral_epow_encard_cluster_le_inv_mul hrow o hlam.le hm hm1.le hcond⟩

/-- **Theorem 2 of `PROOF.md`, moment form.**  For `0 < m < 1` and every `k` there is `λ > 1`
with `E[|K_o|^k] ≤ k! / (m (log λ)^k)` uniformly in the root. -/
theorem exists_lam_lintegral_pow_encard_cluster_le {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : 0 < m) (hm1 : m < 1) (o : V) (k : ℕ) :
    ∃ lam : ℝ, 1 < lam ∧
      ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
        ≤ ENNReal.ofReal ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) := by
  obtain ⟨lam, hlam, hcond⟩ := exists_admissible_lambda hm hm1
  refine ⟨lam, hlam, ?_⟩
  refine (lintegral_pow_encard_cluster_le_inv_mul hrow o hlam hm hm1.le hcond k).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hlogk : Real.log lam ≠ 0 := ne_of_gt (Real.log_pos hlam)
  have hmeq : (1 / m) * ((k.factorial : ℝ) / (Real.log lam) ^ k)
      = (k.factorial : ℝ) / (m * (Real.log lam) ^ k) := by
    field_simp
  exact hmeq.le

/-! ### Interoperability with the diagonal-inclusive `RowSum` -/

/-- `RowSum`-flavoured exponential moment (row sums including the diagonal). -/
theorem lintegral_epow_encard_cluster_le_inv_mul_rowSum {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : RowSum p m) (o : V) {lam : ℝ} (hlam : 1 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) :
    ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (1 / m) :=
  lintegral_epow_encard_cluster_le_inv_mul (uniformRowBound_of_rowSum hrow) o hlam hm hm1 hcond

/-- `RowSum`-flavoured natural moments (row sums including the diagonal). -/
theorem lintegral_pow_encard_cluster_le_inv_mul_rowSum {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : RowSum p m) (o : V) {lam : ℝ} (hlam : 1 < lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ k) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal ((1 / m) * ((k.factorial : ℝ) / (Real.log lam) ^ k)) :=
  lintegral_pow_encard_cluster_le_inv_mul (uniformRowBound_of_rowSum hrow) o hlam hm hm1 hcond k


end PercLib.CriticalLRP.Exploration.BFS
