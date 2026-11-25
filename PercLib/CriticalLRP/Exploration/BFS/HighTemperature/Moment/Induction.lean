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

# The remaining-generation moment induction

Swarm `smwpdplm2` (member m2).  `PROOF.md` §5, Proposition 5.3 in fibre-integral form:

  `∫ G · λ^{N(k,n)} ≤ ∫ G · u_n^{|A_k|}`

for every history function `G` of the revealed block at step `k`, where `N(k,n)` counts the
generations `k, …, k+n-1` and `u_n` is the scalar envelope.  The `n → n+1` step uses the
committed one-step estimate `lintegral_bfs_epow_gen_envelopeStep` (whose `hfin` hypothesis is
discharged by `ae_finState_ne_none`), the induction hypothesis at step `k+1` applied to the
history function `G · λ^{|G_k|}`, and `epow_mul_le`/`epow_add_le`.
-/
public import PercLib.CriticalLRP.Exploration.BFS.HighTemperature.Moment.Defs
public import PercLib.Probability.Exploration.Envelope

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

/-! ### `epow` at the two degenerate exponents -/

theorem epow_zero (lam : ℝ≥0∞) : epow lam 0 = 1 := by
  simp [epow]

theorem epow_one_all (n : ℕ∞) : epow 1 n = 1 := by
  rw [epow]
  simp only [ENNReal.one_rpow, iSup_const]

/-! ### The fibre sum of the frontier weight -/

/-- **The frontier weight as a fibre sum.**  The integral of a (measurable) history weight
against `u^{|A_k|}` is the sum over the compressed-state fibres of the history mass times
`u^{|T_σ|}`; the `none` fibre is null by `ae_finState_ne_none`.

This is the identity that turns the statewise one-step estimate into an integral against
`u^{|A_k|}`. -/
theorem lintegral_epow_encard_A_eq_tsum {p : Sym2 V → unitInterval} {m : ℝ}
    (hrow : UniformRowBound p m) (o : V) (k : ℕ) {u : ℝ} (hu : 1 ≤ u)
    {G : Config V → ℝ≥0∞} (hGm : Measurable G) :
    ∫⁻ ω, G ω * epow (ENNReal.ofReal u) ((A ω o k).encard) ∂(prodBernoulli p)
      = ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * (ENNReal.ofReal u) ^ finStateCard σ := by
  classical
  rw [lintegral_eq_tsum_finState]
  refine tsum_congr (fun σ => ?_)
  cases σ with
  | none =>
      have hnull : prodBernoulli p {ω : Config V | finState ω o k = none} = 0 := by
        refine measure_mono_null ?_ (ae_iff.mp (ae_finState_ne_none hrow o k))
        intro ω hω
        simpa using hω
      rw [setLIntegral_measure_zero _ _ hnull, setLIntegral_measure_zero _ _ hnull]
      simp [finStateCard]
  | some QT =>
      obtain ⟨Q, T⟩ := QT
      have hfib : ∀ ω ∈ {ω : Config V | finState ω o k = some (Q, T)},
          G ω * epow (ENNReal.ofReal u) ((A ω o k).encard)
            = G ω * (ENNReal.ofReal u) ^ T.card := by
        intro ω hω
        have hA : (T : Set V) = A ω o k := (finState_eq_some_iff.mp hω).2
        rw [← hA, Set.encard_coe_eq_coe_finsetCard, epow_ofReal_pow hu T.card,
          ENNReal.ofReal_pow (by linarith) T.card]
      rw [setLIntegral_congr_fun (measurableSet_finState_eq o k (some (Q, T))) hfib]
      rw [lintegral_mul_const _ hGm]
      simp [finStateCard]

/-! ### The induction -/

/-- **The remaining-generation moment induction.**  For every history function `G` at step
`k` and every `n`, the `λ`-moment of the number of vertices in the next `n` generations is
bounded by the `u_n`-moment of the current frontier, where `u_n` is the scalar envelope
`u_{n+1} = e^{m (λ u_n - 1)}`.

No `hfin`, no degree bound, no finiteness of the cluster: the exponential factor is on the
*frontier*, whose a.s. finiteness is only used through `ae_finState_ne_none`. -/
theorem gen_moment_induction {p : Sym2 V → unitInterval} {m : ℝ} (hrow : UniformRowBound p m) (o : V)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ∀ n k, ∀ G : Config V → ℝ≥0∞, IsHistFun o k G →
      ∫⁻ ω, G ω * epow (ENNReal.ofReal lam) (N o k n ω) ∂(prodBernoulli p)
        ≤ ∫⁻ ω, G ω * epow (ENNReal.ofReal (envelope m lam n)) ((A ω o k).encard)
            ∂(prodBernoulli p) := by
  have hm : 0 ≤ m := by
    simpa using hrow o ∅ (by simp)
  have hlam0 : 0 ≤ lam := le_trans zero_le_one hlam
  have hL1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlam
  have hL0 : ENNReal.ofReal lam ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hLtop : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
  intro n
  induction n with
  | zero =>
      intro k G _
      have h1 : ∀ ω : Config V, epow (ENNReal.ofReal lam) (N o k 0 ω) = 1 :=
        fun ω => by rw [N_zero, epow_zero]
      have h2 : ∀ ω : Config V,
          epow (ENNReal.ofReal (envelope m lam 0)) ((A ω o k).encard) = 1 := by
        intro ω
        rw [envelope_zero, ENNReal.ofReal_one, epow_one_all]
      simp only [h1, h2, mul_one]
      exact le_rfl
  | succ n ih =>
      intro k G hG
      set u : ℝ := envelope m lam n with hu_def
      have hu1 : 1 ≤ u := one_le_envelope hm hlam n
      have hu0 : 0 ≤ u := le_trans zero_le_one hu1
      have hU1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal u := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hu1
      have hUt : ENNReal.ofReal u ≠ ⊤ := ENNReal.ofReal_ne_top
      obtain ⟨H, hH, hHfac⟩ := isHistFun_fibreData hG
      have hGm : Measurable G := hG.measurable
      -- the induction hypothesis at step `k+1`, applied to `G · λ^{|G_k|}`
      have hstep : ∫⁻ ω, (G ω * epow (ENNReal.ofReal lam) ((gen ω o k).encard))
            * epow (ENNReal.ofReal lam) (N o (k + 1) n ω) ∂(prodBernoulli p)
          ≤ ∫⁻ ω, (G ω * epow (ENNReal.ofReal lam) ((gen ω o k).encard))
            * epow (ENNReal.ofReal u) ((A ω o (k + 1)).encard) ∂(prodBernoulli p) :=
        ih (k + 1) _
          (hG.succ.mul (isHistFun_epow_encard_A o (k + 1) (ENNReal.ofReal lam)))
      calc ∫⁻ ω, G ω * epow (ENNReal.ofReal lam) (N o k (n + 1) ω) ∂(prodBernoulli p)
          = ∫⁻ ω, G ω * epow (ENNReal.ofReal lam)
              ((gen ω o k).encard + N o (k + 1) n ω) ∂(prodBernoulli p) := by
            refine lintegral_congr (fun ω => ?_)
            rw [N_succ]
        _ ≤ ∫⁻ ω, G ω * (epow (ENNReal.ofReal lam) ((gen ω o k).encard)
              * epow (ENNReal.ofReal lam) (N o (k + 1) n ω)) ∂(prodBernoulli p) := by
            refine lintegral_mono (fun ω => ?_)
            exact mul_le_mul' le_rfl (epow_add_le hL1 hL0 hLtop _ _)
        _ = ∫⁻ ω, (G ω * epow (ENNReal.ofReal lam) ((gen ω o k).encard))
              * epow (ENNReal.ofReal lam) (N o (k + 1) n ω) ∂(prodBernoulli p) := by
            refine lintegral_congr (fun ω => ?_)
            ring
        _ ≤ ∫⁻ ω, (G ω * epow (ENNReal.ofReal lam) ((gen ω o k).encard))
              * epow (ENNReal.ofReal u) ((A ω o (k + 1)).encard) ∂(prodBernoulli p) := hstep
        _ = ∫⁻ ω, (G ω * epow (ENNReal.ofReal lam) ((gen ω o k).encard))
              * epow (ENNReal.ofReal u) ((gen ω o k).encard) ∂(prodBernoulli p) := by
            refine lintegral_congr (fun ω => ?_)
            rfl
        _ ≤ ∫⁻ ω, G ω * epow (ENNReal.ofReal lam * ENNReal.ofReal u)
              ((gen ω o k).encard) ∂(prodBernoulli p) := by
            refine lintegral_mono (fun ω => ?_)
            rw [mul_assoc]
            exact mul_le_mul' le_rfl (epow_mul_le hL1 hU1 hLtop hUt _)
        _ = ∫⁻ ω, G ω * epow (ENNReal.ofReal (lam * u)) ((gen ω o k).encard)
              ∂(prodBernoulli p) := by
            rw [ENNReal.ofReal_mul hlam0]
        _ ≤ ∑' σ : FinState V,
              (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
                * (ENNReal.ofReal (envelopeStep m lam u)) ^ finStateCard σ :=
            lintegral_bfs_epow_gen_envelopeStep (p := p) (o := o) (k := k) (G := G)
              (H := H) (hH := hH) (hG := hHfac) (hlam := hlam) (hu := hu1)
              (hM := hrow) (hfin := ae_finState_ne_none hrow o k)
        _ = ∑' σ : FinState V,
              (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
                * (ENNReal.ofReal (envelope m lam (n + 1))) ^ finStateCard σ := by
            rw [hu_def, envelope_succ]
        _ = ∫⁻ ω, G ω * epow (ENNReal.ofReal (envelope m lam (n + 1)))
              ((A ω o k).encard) ∂(prodBernoulli p) :=
            (lintegral_epow_encard_A_eq_tsum hrow o k
              (one_le_envelope hm hlam (n + 1)) hGm).symm

end PercLib.CriticalLRP.Exploration.BFS
