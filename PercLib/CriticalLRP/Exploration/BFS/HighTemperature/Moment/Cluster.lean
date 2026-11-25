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

# The cluster exponential moment (high temperature, uniform finite bound)

Swarm `smwpdplm2` (member m2).  Conclusion of the generation induction: at `k = 0` the
frontier is the single root, so the horizon moment at horizon `n` is at most `λ u_n`, and
`u_n ≤ 1/(m λ)` for `m λ ≤ e^{m-1}`.  Monotone convergence of the horizon moments to the
cluster moment (`lintegral_epow_encard_cluster_le`) gives the uniform exponential moment
bound of the actual (possibly infinite) cluster.

The hypothesis is the genuine finite-partial uniform row sum `RowSum p m`; nothing is
assumed about a critical point, about `m > 0` (the `m = 0` case is separated below), or
about the finiteness of the cluster.
-/
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Induction

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

/-! ### Measurability of the remaining-generation count -/

theorem measurable_N (o : V) (k n : ℕ) : Measurable fun ω : Config V => N o k n ω := by
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact measurable_encard_A o (k + j + 1)

/-! ### The horizon moment -/

/-- **The finite-horizon exponential moment.**  For `λ ≥ 1` the `λ`-th extended moment of
the number of vertices within `k` steps is at most `λ u_k`. -/
theorem lintegral_epow_horizon_le {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m)
    (o : V) {lam : ℝ} (hlam : 1 ≤ lam) (n : ℕ) :
    ∫⁻ ω, epow (ENNReal.ofReal lam) ((horizon ω o n).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (lam * envelope m lam n) := by
  have hm : 0 ≤ m := by
    simpa using hrow o ∅ (by simp)
  have hlam0 : 0 ≤ lam := le_trans zero_le_one hlam
  have hL1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlam
  have hL0 : ENNReal.ofReal lam ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hLtop : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
  have hu1 : 1 ≤ envelope m lam n := one_le_envelope hm hlam n
  have hU1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (envelope m lam n) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hu1
  have hA0 : ∀ ω : Config V, epow (ENNReal.ofReal (envelope m lam n)) ((A ω o 0).encard)
      = ENNReal.ofReal (envelope m lam n) := by
    intro ω
    rw [A_zero, Set.encard_singleton]
    exact epow_one hU1
  have hind := gen_moment_induction hrow o hlam n 0 (fun _ => (1 : ℝ≥0∞))
    (IsHistFun.const o 0 1)
  simp only [one_mul, hA0] at hind
  have hconst : ∫⁻ _ω : Config V, (ENNReal.ofReal (envelope m lam n) : ℝ≥0∞)
      ∂(prodBernoulli p) = ENNReal.ofReal (envelope m lam n) := by
    rw [lintegral_const, measure_univ, mul_one]
  rw [hconst] at hind
  have hmeas : Measurable fun ω : Config V => epow (ENNReal.ofReal lam) (N o 0 n ω) :=
    (measurable_epow _).comp (measurable_N o 0 n)
  calc ∫⁻ ω, epow (ENNReal.ofReal lam) ((horizon ω o n).encard) ∂(prodBernoulli p)
      = ∫⁻ ω, epow (ENNReal.ofReal lam) (1 + N o 0 n ω) ∂(prodBernoulli p) := by
        refine lintegral_congr (fun ω => ?_)
        rw [encard_horizon_eq_one_add_N]
    _ ≤ ∫⁻ ω, epow (ENNReal.ofReal lam) (1 : ℕ∞)
          * epow (ENNReal.ofReal lam) (N o 0 n ω) ∂(prodBernoulli p) := by
        refine lintegral_mono (fun ω => ?_)
        exact epow_add_le hL1 hL0 hLtop 1 (N o 0 n ω)
    _ = ∫⁻ ω, ENNReal.ofReal lam * epow (ENNReal.ofReal lam) (N o 0 n ω)
          ∂(prodBernoulli p) := by
        rw [epow_one hL1]
    _ = ENNReal.ofReal lam
          * ∫⁻ ω, epow (ENNReal.ofReal lam) (N o 0 n ω) ∂(prodBernoulli p) :=
        lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal lam * ENNReal.ofReal (envelope m lam n) := mul_le_mul' le_rfl hind
    _ = ENNReal.ofReal (lam * envelope m lam n) := (ENNReal.ofReal_mul hlam0).symm

/-! ### The cluster moment -/

/-- **The cluster exponential moment from a uniform envelope bound.** -/
theorem lintegral_epow_cluster_le_of_envelope_bound {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) {lam : ℝ} (hlam : 1 ≤ lam) {C : ℝ}
    (hC : ∀ n : ℕ, lam * envelope m lam n ≤ C) :
    ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal C := by
  refine lintegral_epow_encard_cluster_le (prodBernoulli p) o (ENNReal.ofReal lam)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlam) (ENNReal.ofReal C)
    (fun n => ?_)
  exact (lintegral_epow_horizon_le hrow o hlam n).trans (ENNReal.ofReal_le_ofReal (hC n))

/-- **The high-temperature exponential moment, `0 < m`, sharp constant `1/m`.**

For independent bond percolation on a countable vertex set with every finite partial row
sum at most `m ∈ (0,1]` and `m λ ≤ e^{m-1}`, the extended exponential moment of the actual
cluster is at most `1/m`, *uniformly in the root*.  The cluster is not assumed finite. -/
theorem lintegral_epow_encard_cluster_le_inv_mul
    {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m) (o : V) {lam : ℝ}
    (hlam : 1 ≤ lam) (hm : 0 < m) (hm1 : m ≤ 1)
    (hcond : m * lam ≤ Real.exp (m - 1)) :
    ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal (1 / m) := by
  refine lintegral_epow_cluster_le_of_envelope_bound hrow o hlam (C := 1 / m) (fun n => ?_)
  have hu : envelope m lam n ≤ 1 / (m * lam) := envelope_le_inv_mul hm hm1 hlam hcond n
  have hpos : (0:ℝ) < m * lam := by nlinarith
  have h1 : lam * envelope m lam n ≤ lam * (1 / (m * lam)) :=
    mul_le_mul_of_nonneg_left hu (le_trans zero_le_one hlam)
  have h2 : lam * (1 / (m * lam)) = 1 / m := by field_simp
  linarith [h1, h2.symm.le, h2.le]

/-- **The `m = 0` case**: all edge probabilities in the row sums vanish, the envelope is
identically `1`, and the moment is at most `λ`. -/
theorem lintegral_epow_encard_cluster_le_zero {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (hm : m = 0) (o : V) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∫⁻ ω, epow (ENNReal.ofReal lam) ((cluster ω o).encard) ∂(prodBernoulli p)
      ≤ ENNReal.ofReal lam := by
  refine lintegral_epow_cluster_le_of_envelope_bound hrow o hlam (C := lam) (fun n => ?_)
  rw [hm]
  induction n with
  | zero => rw [envelope_zero]; linarith
  | succ n ih =>
      rw [envelope_succ, envelopeStep]
      simp only [zero_mul, Real.exp_zero]
      exact le_of_eq (mul_one lam)

end PercLib.CriticalLRP.Exploration.BFS
