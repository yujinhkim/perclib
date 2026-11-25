/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

Candidate definition layer.  Nothing is asserted here: these are the objects used by
`Increment.lean`, `Binomial.lean` and `Main.lean`.  The point of the layer is to keep the
*genuine* normalized-norm cut-off profile of the model
(`longRangeEdgeProbability β (cutoffProfile K r (S.dist x y))`) as the only source of edge
probabilities, and to name the two parameter paths through the finite product law that the
incremental Russo identity integrates over.

Reference: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.3/I.1.5 (kernel and cut-off) and Lemma I.4.1 (the derivative formula).
-/
module

public import PercLib.CriticalLRP.CutoffRusso
public import PercLib.CriticalLRP.FiniteGraphCluster
public import PercLib.CriticalLRP.Analysis.Cutoff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The parameter vector obtained from `q` by replacing the coordinates in `S` by those of `p`.
`mixParam S p q` is the state of the product law after the edges of `S` have been moved to
their new probabilities and the remaining ones are still old. -/
noncomputable def mixParam (S : Finset E) (p q : E → ℝ) : E → ℝ :=
  fun e => if e ∈ S then p e else q e

theorem mixParam_apply (S : Finset E) (p q : E → ℝ) (e : E) :
    mixParam S p q e = if e ∈ S then p e else q e := rfl

@[simp] theorem mixParam_empty (p q : E → ℝ) : mixParam (∅ : Finset E) p q = q := by
  funext e; simp [mixParam]

@[simp] theorem mixParam_univ (p q : E → ℝ) : mixParam (univ : Finset E) p q = p := by
  funext e; simp [mixParam]

/-- The straight-line (affine interpolation) path in the parameter vector, from `p` at `t = 0`
to `q` at `t = 1`.  This is the path over which the incremental Russo identity integrates the
pivotal flux. -/
noncomputable def pathParam (p q : E → ℝ) (t : ℝ) : E → ℝ :=
  fun e => p e + t * (q e - p e)

@[simp] theorem pathParam_zero (p q : E → ℝ) : pathParam p q 0 = p := by
  funext e; simp [pathParam]

@[simp] theorem pathParam_one (p q : E → ℝ) : pathParam p q 1 = q := by
  funext e; simp [pathParam]

/-- The edge length of `e` in the genuine normalized norm of the source model: the `ρ`-distance
of the two endpoints.  This (rather than the Euclidean or `ℓ∞` length) is what drives the
general-norm cut-off profile. -/
noncomputable def normLen {d : ℕ} (S : Orchestration.SourceNormData d) (src dst : E → Fin d → ℤ)
    (e : E) : ℝ :=
  S.dist (src e) (dst e)

/-- The open-edge probabilities of the range-truncated source law at cut-off radius `r`, on a
finite edge set with prescribed endpoints and norm-driven lengths.  This is
`q_r(e) = 1 − exp(−β_c ∫_{‖e‖}^{r} |J'|)` with the source's `β_c` and `J`. -/
noncomputable def cutoffParam (K : ℝ → ℝ) (β : ℝ) (len : E → ℝ) (r : ℝ) :
    E → ℝ :=
  fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))

/-- The `p`-th moment of the anchored finite cluster volume at the vertex `x`, as an observable
of the finite edge configuration. -/
noncomputable def clusterMoment (s t : E → V) (x : V) (p : ℕ)
    (ω : Configuration E) : ℝ :=
  ((cluster s t ω x).card : ℝ) ^ p

/-- The finite-volume `p`-th cutoff cluster moment as a function of the cut-off radius. -/
noncomputable def cutoffMoment (K : ℝ → ℝ) (β : ℝ) (len : E → ℝ)
    (s t : E → V) (x : V) (p : ℕ) (r : ℝ) : ℝ :=
  expectation (cutoffParam K β len r) (clusterMoment s t x p)

/-- The pivotal flux of a finite product law: the total derivative weight of an edge-wise
increase of all edge probabilities.  It is `∑_e pivotalMass q e X`. -/
noncomputable def pivotalFlux (q : E → ℝ) (X : Configuration E → ℝ) : ℝ :=
  ∑ e, pivotalMass q e X

/-- The binomial pivotal weight of a single-edge flip in the case where the flipped edge merges
the anchored cluster of `x` (which is the cluster of `s e`) with a disjoint cluster of `t e`.
This is the per-configuration `ℓ`-sum of Lemma I.4.1. -/
noncomputable def leftWeight (s : E → V) (t : E → V) (x : V) (p : ℕ) (e : E)
    (τ : Configuration E) : ℝ := by
  classical
  exact if ¬ Conn s t τ (s e) (t e) ∧ Conn s t τ x (s e) then
      ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * ((cluster s t τ (s e)).card : ℝ) ^ ℓ
        * ((cluster s t τ (t e)).card : ℝ) ^ (p - ℓ)
    else 0

/-- The same weight in the mirrored case, where the anchored cluster is the cluster of `t e`. -/
noncomputable def rightWeight (s : E → V) (t : E → V) (x : V) (p : ℕ) (e : E)
    (τ : Configuration E) : ℝ := by
  classical
  exact if ¬ Conn s t τ (s e) (t e) ∧ Conn s t τ x (t e) then
      ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * ((cluster s t τ (t e)).card : ℝ) ^ ℓ
        * ((cluster s t τ (s e)).card : ℝ) ^ (p - ℓ)
    else 0

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
