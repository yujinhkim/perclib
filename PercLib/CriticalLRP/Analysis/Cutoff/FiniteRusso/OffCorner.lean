/-
Finite-volume generalized-norm Russo handoff (swarm `smwtrtcqs`, member `m6`, direction D2).

The **off-corner** form of the finite-volume Russo formula: at a radius `r` that is not the
norm-length of any edge of the finite edge set (so `r` is not a corner of the cut-off profile of
any edge), the derivative in `r` of the finite-volume `p`-th cluster moment exists and equals
`β|J'(r)|` times the pivotal flux, with every summand of the flux written as the binomial
`ℓ`-sum of Lemma I.4.1.

At a corner (`r = ‖e‖` for some `e`) the two-sided derivative does *not* exist in general, and no
statement is made there: the interval increment `cutoffMoment_increment` of `Main.lean` covers
corner endpoints without differentiating.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.Model

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

@[expose] public section

open Finset MeasureTheory intervalIntegral
open PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : ℝ → ℝ} {β : ℝ} {edgeLen : E → ℝ} {s t : E → V} {x : V} {p : ℕ}

/-- **Off-corner Russo formula** (finite volume, general norm length).  At a radius `r` that is
not equal to the norm-length of any edge, the derivative of the `p`-th cut-off cluster moment in
the cut-off radius is `β|J'(r)|` times the sum over the edges already switched on of their pivotal
mass.  This is the exact finite-volume content of the source's `∂_r E_{β,r}|K|^p` formula at a
radius away from the corners. -/
theorem hasDerivAt_cutoffMoment {K' r : ℝ} (hne : ∀ e, edgeLen e ≠ r)
    (hK : HasDerivAt K (-K') r) :
    HasDerivAt (fun r' => cutoffMoment K β edgeLen s t x p r')
      (β * K' * ∑ e ∈ univ.filter (fun e => edgeLen e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (cutoffParam K β edgeLen r) τ
            * (clusterMoment s t x p (insert e τ) - clusterMoment s t x p τ)) r :=
  hasDerivAt_expectation_cutoff edgeLen K K' hne hK (clusterMoment s t x p)

/-- The off-corner hypothesis holds automatically off the (finite) set of edge lengths. -/
theorem offCorner_of_notMem_range {r : ℝ} (hr : r ∉ Set.range edgeLen) : ∀ e, edgeLen e ≠ r :=
  fun e he => hr ⟨e, he⟩

/-- **Off-corner Russo formula, binomial form.**  Each summand of the pivotal flux is the
binomial `ℓ`-sum of Lemma I.4.1: the flip contributes `∑_{ℓ<p} C(p,ℓ) A^ℓ B^{p-ℓ}` when it
merges the anchored cluster (of size `A`) with a disjoint one (of size `B`), and nothing
otherwise. -/
theorem hasDerivAt_cutoffMoment_binomial {K' r : ℝ} (hne : ∀ e, edgeLen e ≠ r)
    (hK : HasDerivAt K (-K') r) :
    HasDerivAt (fun r' => cutoffMoment K β edgeLen s t x p r')
      (β * K' * ∑ e ∈ univ.filter (fun e => edgeLen e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (cutoffParam K β edgeLen r) τ
            * (leftWeight s t x p e τ + rightWeight s t x p e τ)) r := by
  have h := hasDerivAt_cutoffMoment (K := K) (β := β) (edgeLen := edgeLen) (s := s) (t := t)
    (x := x) (p := p) hne hK
  have hval : (∑ e ∈ univ.filter (fun e => edgeLen e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (cutoffParam K β edgeLen r) τ
            * (clusterMoment s t x p (insert e τ) - clusterMoment s t x p τ))
      = ∑ e ∈ univ.filter (fun e => edgeLen e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (cutoffParam K β edgeLen r) τ
            * (leftWeight s t x p e τ + rightWeight s t x p e τ) := by
    refine sum_congr rfl fun e _ => sum_congr rfl fun τ _ => ?_
    rw [clusterMoment_flip_eq_left_add_right]
  rw [hval] at h
  exact h

/-! ### The same at the source model -/

namespace SourceModel

variable (M : SourceModelData)

/-- **Off-corner Russo formula at the genuine normalized norm.**  At a radius that is not the
`ρ`-length of an edge, the derivative of the finite-volume source cutoff moment in the cut-off
radius is `β_c |J'(r)|` times the pivotal flux, with the `ℓ`-sum weights of Lemma I.4.1. -/
theorem hasDerivAt_moment {E : Type*} [Fintype E] [DecidableEq E] {V : Type*} [Fintype V]
    [DecidableEq V] (src dst : E → Fin M.d → ℤ) (s t : E → V) (x : V) (p : ℕ) {K' r : ℝ}
    (hne : ∀ e, len M src dst e ≠ r) (hK : HasDerivAt M.K (-K') r) :
    HasDerivAt (fun r' => moment M src dst s t x p r')
      ((M.betaCrit : ℝ) * K' * ∑ e ∈ univ.filter (fun e => len M src dst e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (param M src dst r) τ
            * (leftWeight s t x p e τ + rightWeight s t x p e τ)) r := by
  unfold moment param len
  exact hasDerivAt_cutoffMoment_binomial hne hK

end SourceModel

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
