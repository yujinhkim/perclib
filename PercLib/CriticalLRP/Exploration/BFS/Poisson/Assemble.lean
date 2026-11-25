/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The one-step estimate in generation-induction shape.

Direction 1 (swarm `smwpbvro2`, member m1).  Two cosmetic-but-load-bearing rewrites of the
directed-limit estimate `PoissonBoundLimit.lintegral_bfs_epow_le_rowBound'`:

* the deterministic budget `exp ((t-1) |T_σ| M)` is an `|T_σ|`-th power of the single
  per-vertex factor `exp ((t-1) M)`; with `t = λ u_n` that factor is exactly the envelope step
  `u_{n+1} = exp (M (λ u_n - 1))`;
* on the event that the exploration state is finite, the extended-power moment of the *true*
  generation `gen ω o k` is dominated by the estimated fresh moment.

The a.s. finiteness of the exploration state (`finState ω o k ≠ none`) is taken as an explicit
hypothesis `hfin`; proving it is *not* done here, and no statement about a cluster is made.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Limit

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond Finset
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-- The budget `exp ((t-1) (n M))` is the `n`-th power of the per-vertex factor
`exp ((t-1) M)`.  With `t = λ u_n` the latter is the envelope step `u_{n+1}`. -/
theorem ofReal_exp_card_mul (t : ℝ≥0∞) (M : ℝ) (n : ℕ) :
    ENNReal.ofReal (Real.exp ((t.toReal - 1) * ((n : ℝ) * M)))
      = (ENNReal.ofReal (Real.exp ((t.toReal - 1) * M))) ^ n := by
  have harg : (t.toReal - 1) * ((n : ℝ) * M) = (n : ℝ) * ((t.toReal - 1) * M) := by ring
  rw [harg, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le]

/-- **The one-step estimate with the budget as a power.**  Same hypotheses as
`lintegral_bfs_epow_le_rowBound'`, with the state weight written as
`(exp ((t-1) M)) ^ |T_σ|`. -/
theorem lintegral_bfs_epow_le_rowBound_pow [Countable V] (p : Sym2 V → unitInterval) (o : V)
    (k : ℕ) (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (t : ℝ≥0∞) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) {M : ℝ} (hM : UniformRowBound p M) :
    ∫⁻ ω, G ω * epow t ((freshEdgeSet (finState ω o k) ∩ ω).encard) ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * (ENNReal.ofReal (Real.exp ((t.toReal - 1) * M))) ^ finStateCard σ := by
  refine le_trans (lintegral_bfs_epow_le_rowBound' p o k G H hH hG t ht ht_top hM)
    (ENNReal.tsum_le_tsum fun σ => ?_)
  exact mul_le_mul' le_rfl (le_of_eq (ofReal_exp_card_mul t M (finStateCard σ)))

/-- **The moment of the true generation on the finite-state event.**  If the exploration state
after `k` steps is almost surely finite, the extended-power moment `∫ G · epow t (|gen ω o k|)`
of the *actual* generation is bounded by the history sum with budget `|T_σ| · M`.

The a.s. finiteness `hfin` is an explicit hypothesis: it is exactly the point at which the
`FinState.none` fibre (infinite frontier) would otherwise contribute. -/
theorem lintegral_bfs_epow_gen_le_rowBound [Countable V] (p : Sym2 V → unitInterval) (o : V)
    (k : ℕ) (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (t : ℝ≥0∞) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) {M : ℝ} (hM : UniformRowBound p M)
    (hfin : ∀ᵐ ω ∂(prodBernoulli p), finState ω o k ≠ none) :
    ∫⁻ ω, G ω * epow t ((gen ω o k).encard) ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * (ENNReal.ofReal (Real.exp ((t.toReal - 1) * M))) ^ finStateCard σ := by
  refine le_trans (lintegral_mono_ae ?_) (lintegral_bfs_epow_le_rowBound_pow p o k G H hH hG
    t ht ht_top hM)
  filter_upwards [hfin] with ω hω
  obtain ⟨Q, T, hQT⟩ : ∃ Q T : Finset V, finState ω o k = some (Q, T) := by
    cases h : finState ω o k with
    | none => exact absurd h hω
    | some QT => obtain ⟨Q, T⟩ := QT; exact ⟨Q, T, rfl⟩
  rw [hQT]
  exact mul_le_mul' le_rfl (epow_mono t ht (encard_gen_le_encard_freshEdgeSet_inter hQT))

/-- The committed `ExplorationEnvelope.UniformRowSum` (the repository's (R_m), in the same
finite-partial-sum form) implies `UniformRowBound` for the edge index. -/
theorem uniformRowBound_of_uniformRowSum {p : Sym2 V → unitInterval} {M : ℝ}
    (h : PercLib.Probability.ExplorationEnvelope.UniformRowSum
      (fun x y : V => (p (s(x, y)) : ℝ)) M) :
    UniformRowBound p M :=
  fun x t _ => h x t

/-- **The one-step estimate with the committed envelope step as state weight.**  Instantiating
`lintegral_bfs_epow_le_rowBound_pow` at `t = λ u` shows that the weight of a state with frontier
`T` is exactly `envelopeStep m λ u ^ |T|`, i.e. the recursion `u_{n+1} = exp (m (λ u_n - 1))`
of `PROOF.md` (5.1) evaluated at `u = u_n`. -/
theorem lintegral_bfs_epow_envelopeStep [Countable V] (p : Sym2 V → unitInterval) (o : V)
    (k : ℕ) (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    {m lam u : ℝ} (hlam : 1 ≤ lam) (hu : 1 ≤ u) (hM : UniformRowBound p m) :
    ∫⁻ ω, G ω * epow (ENNReal.ofReal (lam * u)) ((freshEdgeSet (finState ω o k) ∩ ω).encard)
        ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * (ENNReal.ofReal
                (PercLib.Probability.ExplorationEnvelope.envelopeStep m lam u)) ^ finStateCard σ := by
  have hlu1 : (1 : ℝ) ≤ lam * u := by nlinarith [hlam, hu]
  have hlu0 : (0 : ℝ) ≤ lam * u := le_trans zero_le_one hlu1
  have htoReal : (ENNReal.ofReal (lam * u)).toReal = lam * u := ENNReal.toReal_ofReal hlu0
  refine le_trans (lintegral_bfs_epow_le_rowBound_pow p o k G H hH hG
    (ENNReal.ofReal (lam * u)) (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlu1)
    ENNReal.ofReal_ne_top hM) ?_
  refine ENNReal.tsum_le_tsum fun σ => mul_le_mul' le_rfl (le_of_eq ?_)
  rw [htoReal, PercLib.Probability.ExplorationEnvelope.envelopeStep,
    show ((lam * u) - 1) * m = m * (lam * u - 1) by ring]

/-- **The genuinely-generation version of the envelope-step estimate**: on the a.s.-finite
state event, the extended-power moment of the true generation `gen ω o k` is bounded by the
history sum with the envelope-step weight `envelopeStep m λ u ^ |T_σ|`. -/
theorem lintegral_bfs_epow_gen_envelopeStep [Countable V] (p : Sym2 V → unitInterval) (o : V)
    (k : ℕ) (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    {m lam u : ℝ} (hlam : 1 ≤ lam) (hu : 1 ≤ u) (hM : UniformRowBound p m)
    (hfin : ∀ᵐ ω ∂(prodBernoulli p), finState ω o k ≠ none) :
    ∫⁻ ω, G ω * epow (ENNReal.ofReal (lam * u)) ((gen ω o k).encard) ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * (ENNReal.ofReal
                (PercLib.Probability.ExplorationEnvelope.envelopeStep m lam u)) ^ finStateCard σ := by
  have hlu1 : (1 : ℝ) ≤ lam * u := by nlinarith [hlam, hu]
  have hlu0 : (0 : ℝ) ≤ lam * u := le_trans zero_le_one hlu1
  have htoReal : (ENNReal.ofReal (lam * u)).toReal = lam * u := ENNReal.toReal_ofReal hlu0
  refine le_trans (lintegral_bfs_epow_gen_le_rowBound p o k G H hH hG
    (ENNReal.ofReal (lam * u)) (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlu1)
    ENNReal.ofReal_ne_top hM hfin) ?_
  refine ENNReal.tsum_le_tsum fun σ => mul_le_mul' le_rfl (le_of_eq ?_)
  rw [htoReal, PercLib.Probability.ExplorationEnvelope.envelopeStep,
    show ((lam * u) - 1) * m = m * (lam * u - 1) by ring]

end PercLib.CriticalLRP.Exploration.BFS
