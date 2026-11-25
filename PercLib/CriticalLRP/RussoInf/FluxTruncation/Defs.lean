/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Level truncations of monotone configuration functionals

Integration donors: `.ultramath/smwvctsvt/m3/mirror/FluxTruncation.lean` and
`FluxTruncationModel.lean`, independently checked at 0b87f45527ec4090b7f9189ab48f7ade24cac41e.
Definitions migrated here so that the proof modules contain no new definitions.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.ToReal

/-!
# Monotone truncations of observations and cluster volumes
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The level `n` truncation `g ω ∧ n`, used to obtain a nonnegative observation as a monotone limit. -/
noncomputable def levelTrunc (g : Config V → ℝ) (n : ℕ) : Config V → ℝ :=
  fun ω => min (g ω) (n : ℝ)

/-- The increment of `g` from opening one edge, restricted to the event where that edge is closed. -/
noncomputable def closedIncr (g : Config V → ℝ) (e : Sym2 V) (ω : Config V) : ℝ :=
  if e ∈ ω then 0 else g (ω ∪ {e}) - g ω

/-- The cluster volume capped at level `n` in `ℝ≥0∞` before conversion to a real number. -/
noncomputable def clusterVolCap (n : ℕ) (ω : Config V) (o : V) : ℝ :=
  ((n : ℝ≥0∞) ⊓ clusterVol ω o).toReal

/-- The square of the level-capped cluster volume. -/
noncomputable def capSq (n : ℕ) (o : V) : Config V → ℝ :=
  fun ω => clusterVolCap n ω o ^ 2

end PercLib.CriticalLRP.Orchestration

end
