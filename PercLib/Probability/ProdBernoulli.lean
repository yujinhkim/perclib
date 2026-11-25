/-
Adapted from PercolationContinuity (Anthropic, PBC), Copyright 2026.
Source: https://github.com/anthropics/formal-math/blob/795efb86f191735c5481675763537cfb4ff37e55/percolation/Percolation/Literature/LatticeModels/ProdBernoulli.lean
and ProdBernoulliProofs.lean at the same revision.
Released under the Apache License 2.0; see third_party/percolation/LICENSE
and third_party/percolation/NOTICE.

Modified for this project on 2026-11-12: namespace, focused Mathlib imports, Lean 4.35
public declarations, MeasurableEquiv.setOfPred, and Mathlib's equivalent
bernoulliMeasure spelling. The indicator specialization is stated directly
as a theorem. The constant-parameter specialization is a new corollary.
Renamed on 2026-11-13: the project root namespace and library became PercLib
(docs/DECISIONS.md, D-11). No definition, statement or proof was changed.
-/
module

public import PercLib.Meta.Tag

public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Inhomogeneous Bernoulli configurations

A configuration is a set of open indices. This is the inhomogeneous extension
of Mathlib's `ProbabilityTheory.setBernoulli`, using Mathlib's existing
Bernoulli laws, product measure and measurable equivalence on sets.

The definition and proofs are adapted from the pinned PercolationContinuity
sources above. They are also the probability vocabulary copied into
PercolationAudit.SiteCriticality.SolutionBasic at
`nitromannitol/percolation-after-anthropic@a5cc72bd7627f313abbb00bcb47616678abbeb35`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PercLib.Probability

variable {ι : Type*}

/-- Independent open indices, with open probability `p i` at index `i`. -/
@[tag "8NWX"] noncomputable def prodBernoulli (p : ι → unitInterval) : Measure (Set ι) :=
  .comap (fun s i => i ∈ s) <|
    Measure.infinitePi fun i : ι => bernoulliMeasure True False (p i)

/-- The spelling above is definitionally the weighted-Dirac definition in
the pinned upstream statement audit. -/
theorem prodBernoulli_eq_weighted (p : ι → unitInterval) :
    prodBernoulli p = .comap (fun s i => i ∈ s) (Measure.infinitePi fun i : ι =>
      unitInterval.toNNReal (p i) • Measure.dirac True +
        unitInterval.toNNReal (unitInterval.symm (p i)) • Measure.dirac False) := rfl

/-- The configuration law has total mass one. -/
instance instIsProbabilityMeasureProdBernoulli (p : ι → unitInterval) :
    IsProbabilityMeasure (prodBernoulli p) :=
  MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap <|
    .of_forall fun P => ⟨{i | P i}, rfl⟩

/-- Equivalently, push the product law forward from predicates to sets. -/
theorem prodBernoulli_eq_map (p : ι → unitInterval) :
    prodBernoulli p = .map (fun q : ι → Prop => {i | q i})
      (Measure.infinitePi fun i : ι => bernoulliMeasure True False (p i)) :=
  MeasurableEquiv.setOfPred.comap_symm

/-- With probability `p` on `u` and zero elsewhere, the law is Mathlib's
existing homogeneous set-Bernoulli distribution. -/
theorem prodBernoulli_indicator (u : Set ι) [DecidablePred (· ∈ u)] (p : unitInterval) :
    prodBernoulli (fun i => if i ∈ u then p else 0) = setBernoulli u p := by
  unfold prodBernoulli setBernoulli
  congr 1
  congr 1
  funext i
  by_cases hi : i ∈ u <;> simp [hi]

/-- Homogeneous percolation on all indices uses Mathlib's existing law. -/
theorem prodBernoulli_const (p : unitInterval) :
    prodBernoulli (fun _ : ι => p) = setBernoulli Set.univ p := by
  classical
  simpa using (prodBernoulli_indicator (Set.univ : Set ι) p)

end PercLib.Probability

