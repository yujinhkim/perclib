/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The Bernoulli-Poisson budget at the countable BFS state.

Direction 1 (swarm `smwpbvro2`, member m1).  `PoissonBoundScalar` proves the finite-set
factor/product bound; this file feeds it into the committed adapted-revelation
factorization `PercLib.CriticalLRP.Exploration.BFS.lintegral_bfs_adapted_pgf_le`, and
records the exact hypothesis on the deterministic real budget function `bud : FinState V → ℝ`
that the generation induction of direction 2 has to supply.

Nothing here asserts that any `bud` is finite, that a frontier is finite, or that a cluster
moment is finite: the content is the implication "row-sum budget ⟹ exponential fresh-factor
bound", plus the unconditional partition identity of the `FinState` fibres.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Scalar
public import PercLib.CriticalLRP.Exploration.BFS.BFSProduct

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.Probability.ExplorationPoisson

variable {ι : Type*}

/-! ### The `unitInterval`-indexed form -/

/-- The `ℝ≥0∞` value `(unitInterval.toNNReal p : ℝ≥0∞)` is `ofReal` of the real value of `p`. -/
theorem coe_toNNReal_ennreal (p : unitInterval) :
    (unitInterval.toNNReal p : ℝ≥0∞) = ENNReal.ofReal (p : ℝ) := by
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]

theorem toReal_coe_toNNReal (p : unitInterval) :
    ((unitInterval.toNNReal p : ℝ≥0∞)).toReal = (p : ℝ) := by
  rw [coe_toNNReal_ennreal, ENNReal.toReal_ofReal p.2.1]

/-- **Finite-product Poisson bound at a `unitInterval` family.**  This is the form used by
`AdaptedReveal.PGF` (whose factors are `t * ↑(toNNReal (p e)) + (1 - ↑(toNNReal (p e)))`):
a finite set of coordinates with intensity sum at most `m` has fresh-product at most
`ofReal (exp ((t-1) m))`.

*Finite-`S` statement only*: `S` is a `Finset`, so this bounds a finite product of
one-coordinate factors, not an infinite product over a queried edge set. -/
theorem prod_pgfFactor_unitInterval_le_exp (p : ι → unitInterval) (t : ℝ≥0∞)
    (ht : 1 ≤ t) (ht_top : t ≠ ⊤) (S : Finset ι) {m : ℝ}
    (hm : ∑ e ∈ S, (p e : ℝ) ≤ m) :
    ∏ e ∈ S, (t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞)))
      ≤ ENNReal.ofReal (Real.exp ((t.toReal - 1) * m)) := by
  classical
  have ht1 : 1 ≤ t.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ht_top ht
  have hfac : ∀ e ∈ S, t * (unitInterval.toNNReal (p e) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (p e) : ℝ≥0∞))
      = ENNReal.ofReal t.toReal * ENNReal.ofReal (p e : ℝ)
          + (1 - ENNReal.ofReal (p e : ℝ)) := by
    intro e _
    conv_lhs => rw [← ENNReal.ofReal_toReal ht_top, coe_toNNReal_ennreal]
  rw [Finset.prod_congr rfl hfac]
  exact prod_pgfFactor_le_exp (fun e => (p e : ℝ)) (fun e => (p e).2.1) (fun e => (p e).2.2)
    t.toReal ht1 S hm

end PercLib.Probability.ExplorationPoisson

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-- **The one-step exponential budget on the BFS state.**  Given a deterministic real budget
`bud σ` dominating the total intensity `∑_{e ∈ S σ} p_e` of the fresh edge set of state `σ`,
the fresh pgf product is at most `exp ((t-1) bud σ)`, hence the adapted-revelation
factorization gives the stated upper bound for the fresh-moment integral.

All hypotheses are the ones of the committed `lintegral_bfs_adapted_pgf_le` (measurability of
the history function `H`, the factorization hypothesis `hG`, disjointness of the fresh set
from the revealed set) plus `1 ≤ t` finite.  No finiteness of `A k`, `P k` or of `queried` is
assumed; `S` is a `Finset` by definition, and the theorem is *finite-fresh-set only*. -/
theorem lintegral_bfs_adapted_pgf_le_of_budget (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (S : FinState V → Finset (Sym2 V))
    (hS : ∀ σ, Disjoint ((S σ : Finset (Sym2 V)) : Set (Sym2 V)) (revealFin σ))
    (t : ℝ≥0∞) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) (bud : FinState V → ℝ)
    (hbud : ∀ σ, ∑ e ∈ S σ, (p e : ℝ) ≤ bud σ) :
    ∫⁻ ω, G ω * t ^ openCount (S (finState ω o k)) ω ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * ENNReal.ofReal (Real.exp ((t.toReal - 1) * bud σ)) := by
  refine lintegral_bfs_adapted_pgf_le p o k G H hH hG S hS t
    (fun σ => ENNReal.ofReal (Real.exp ((t.toReal - 1) * bud σ))) ?_
  intro σ
  exact ExplorationPoisson.prod_pgfFactor_unitInterval_le_exp p t ht ht_top (S σ) (hbud σ)

/-! ### The unconditional partition of the `FinState` fibres -/

/-- The `FinState` fibres of the BFS state partition the configuration space: the integral of a
nonnegative function is the sum of its integrals over the fibres.  This is the unconditional
"history sum" that turns a state-dependent one-step bound into a single inequality. -/
theorem lintegral_eq_tsum_finState (μ : Measure (Config V)) (G : Config V → ℝ≥0∞) (o : V) (k : ℕ) :
    ∫⁻ ω, G ω ∂μ
      = ∑' σ : FinState V, ∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂μ := by
  have hdisj : Pairwise (Function.onFun Disjoint (fun σ : FinState V => {ω | finState ω o k = σ})) := by
    intro σ σ' hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    exact hne (hω.symm.trans hω')
  have hunion : (⋃ σ : FinState V, {ω | finState ω o k = σ}) = univ := by
    ext ω
    simp
  rw [← lintegral_iUnion (fun σ => measurableSet_finState_eq o k σ) hdisj G, hunion,
    Measure.restrict_univ]

end PercLib.CriticalLRP.Exploration.BFS
