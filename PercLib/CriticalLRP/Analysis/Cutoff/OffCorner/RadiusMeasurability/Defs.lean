/-
Recovered continuation of `smwuges40/m5`: local event definitions for radius measurability.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling

/-!
# Forced-edge indicator events used by cutoff-radius measurability proofs

This module defines the events of forced-open and forced closed windows used by the
corresponding measurability proofs. No new moment or derivative premise is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The event that the window-truncated configuration with `e` forced **open** puts `y` in the
cluster of `0`. -/
def forcedOpenEvent (S : Finset (Sym2 M.V)) (e : Sym2 M.V) (E : Set (Config M.V)) :
    Set (Config M.V) :=
  (fun ω => cutConfig S (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω)) ⁻¹' E

/-- The event that the window-truncated configuration with `e` forced **closed** puts `y` in the
cluster of `0`. -/
def forcedClosedEvent (S : Finset (Sym2 M.V)) (e : Sym2 M.V) (E : Set (Config M.V)) :
    Set (Config M.V) :=
  (fun ω => cutConfig S (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω)) ⁻¹' E

/-- The event that the configuration with `e` forced **open** puts `y` in the cluster of `0`. -/
def rawOpenEvent (e : Sym2 M.V) (E : Set (Config M.V)) : Set (Config M.V) :=
  (fun ω => forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) ⁻¹' E

/-- The event that the configuration with `e` forced **closed** puts `y` in the cluster of `0`. -/
def rawClosedEvent (e : Sym2 M.V) (E : Set (Config M.V)) : Set (Config M.V) :=
  (fun ω => forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) ⁻¹' E

variable {M}

end SourceModelData

end PercLib.CriticalLRP.Orchestration
