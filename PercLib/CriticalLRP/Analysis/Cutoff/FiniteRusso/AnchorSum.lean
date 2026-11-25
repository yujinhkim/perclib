/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

Summing the per-anchor binomial flip weights over the anchored vertices of the merged cluster
produces the *source's* shape `|K|^{ℓ+1}|K_y|^{p−ℓ}` of the `ℓ`-sum in Lemma I.4.1: the extra power
of `|K|` is exactly the cardinality of the set of anchors.  In the source this summation is
performed by the mass-transport principle over the random cluster `K`; here it is performed
literally, over the finite cluster of the endpoint, inside one configuration.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.LowerEndpoint

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **From the anchored binomial weight to the source's `|K|^{ℓ+1}` weight.**  If the flipped
edge merges the cluster of `s e` (size `A`) with the disjoint cluster of `t e` (size `B`), then
summing the increment of the `p`-th moment over all anchors `x` in the merged cluster gives
`∑_{ℓ<p} C(p,ℓ) A^{ℓ+1} B^{p−ℓ}`: precisely the shape of the right-hand side of Lemma I.4.1 with
`A = |K|` and `B = |K_y|`. -/
theorem sum_clusterMoment_flip_eq_sum {s t : E → V} {e : E} {ω : Configuration E} (p : ℕ)
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    ∑ x ∈ cluster s t ω (s e),
        (clusterMoment s t x p (insert e ω) - clusterMoment s t x p ω)
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * ((cluster s t ω (s e)).card : ℝ) ^ (ℓ + 1)
          * ((cluster s t ω (t e)).card : ℝ) ^ (p - ℓ) := by
  classical
  have hconst : ∀ x ∈ cluster s t ω (s e),
      clusterMoment s t x p (insert e ω) - clusterMoment s t x p ω
        = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * ((cluster s t ω (s e)).card : ℝ) ^ ℓ
            * ((cluster s t ω (t e)).card : ℝ) ^ (p - ℓ) := by
    intro x hx
    rw [mem_cluster] at hx
    exact clusterMoment_flip_eq_sum p hxy (conn_symm hx)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hcard : ((cluster s t ω (s e)).card : ℝ) * ((cluster s t ω (s e)).card : ℝ) ^ ℓ
      = ((cluster s t ω (s e)).card : ℝ) ^ (ℓ + 1) := by
    rw [pow_succ]; ring
  calc ((cluster s t ω (s e)).card : ℝ)
        * ((p.choose ℓ : ℝ) * ((cluster s t ω (s e)).card : ℝ) ^ ℓ
            * ((cluster s t ω (t e)).card : ℝ) ^ (p - ℓ))
      = (p.choose ℓ : ℝ)
          * (((cluster s t ω (s e)).card : ℝ) * ((cluster s t ω (s e)).card : ℝ) ^ ℓ)
          * ((cluster s t ω (t e)).card : ℝ) ^ (p - ℓ) := by ring
    _ = (p.choose ℓ : ℝ) * ((cluster s t ω (s e)).card : ℝ) ^ (ℓ + 1)
          * ((cluster s t ω (t e)).card : ℝ) ^ (p - ℓ) := by rw [hcard]

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
