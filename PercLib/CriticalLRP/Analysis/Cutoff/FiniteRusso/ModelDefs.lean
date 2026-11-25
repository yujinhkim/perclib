/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Source-model finite-volume Russo parameters

These are the normalized-norm length, edge-profile, and moment wrappers at
`SourceModelData`. The finite-window Russo proofs import this definitions
module separately; no infinite-volume cutoff mass is defined here.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FiniteRusso.Defs

@[expose] public section

namespace PercLib.CriticalLRP.FiniteVolume.RussoHandoff

open PercLib.CriticalLRP.Orchestration

namespace SourceModel

variable (M : SourceModelData)

/-- The norm-length of a finite edge: the `ρ`-distance of its two lattice endpoints. -/
noncomputable def len {E : Type*} (src dst : E → Fin M.d → ℤ) (e : E) : ℝ :=
  normLen M.S src dst e

/-- The open-edge probabilities of the range-truncated source law on the finite edge set. -/
noncomputable def param {E : Type*} (src dst : E → Fin M.d → ℤ) (r : ℝ) : E → ℝ :=
  cutoffParam M.K (M.betaCrit : ℝ) (len M src dst) r

/-- The finite-volume `p`-th source cutoff cluster moment. -/
noncomputable def moment {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
    (src dst : E → Fin M.d → ℤ) (s t : E → V) (x : V) (p : ℕ) (r : ℝ) : ℝ :=
  cutoffMoment M.K (M.betaCrit : ℝ) (len M src dst) s t x p r

end SourceModel

end PercLib.CriticalLRP.FiniteVolume.RussoHandoff
