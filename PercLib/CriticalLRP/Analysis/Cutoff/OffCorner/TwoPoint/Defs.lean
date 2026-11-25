/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Definitions for off-corner continuity of the cutoff two-point function.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity.Defs

/-!
# Configuration-space events for the off-corner continuity of the two-point function

The event families introduced here are the escape events and the finite-box connection
events used by the two-point and forced-edge continuity arguments.

* `escapeAt M v R` is the event that the cluster of `v` leaves the lattice ball of radius
  `R`; `escapeConf M R` is the case `v = 0`.  They are the configuration-space counterparts
  of `SourceModelData.markEscapeAt`; they do not mention the cutoff radius at all, so their
  `cutLaw`-probabilities are monotone in the radius.
* `restrictConf M D ω` is the sub-configuration carried by the finite edge set `D`, and
  `boxConn M D y` is the event that `0` is connected to `y` inside it.  These depend on the
  configuration only through the edges of `D`, which is what makes the finite-range
  variation bound applicable.
* `escapeForce M e η R` and `boxForce M e η D y` are the same two objects for the
  configuration in which the single edge `e` is forced to the state `η`; they carry the
  forced-open and forced-closed connection events appearing in the pivotal flux.

No theorem is asserted in this file.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The event that the open cluster of `v` is not contained in the lattice ball of radius
`R`: there is a lattice point outside that ball connected to `v`. -/
def escapeAt (v : M.V) (R : ℝ) : Set (Config M.V) :=
  {ω | ∃ z : M.V, z ∉ M.ball R ∧ Connects ω v z}

/-- The event that the open cluster of the origin leaves the lattice ball of radius `R`. -/
abbrev escapeConf (R : ℝ) : Set (Config M.V) := M.escapeAt (0 : M.V) R

/-- The sub-configuration carried by the finite edge set `D`. -/
def restrictConf (D : Finset (Sym2 M.V)) (ω : Config M.V) : Config M.V :=
  fun e => e ∈ D ∧ ω e

/-- The event that `v` is connected to `y` inside the sub-configuration carried by the finite
edge set `D`. -/
def boxConnAt (D : Finset (Sym2 M.V)) (v y : M.V) : Set (Config M.V) :=
  {ω | Connects (M.restrictConf D ω) v y}

/-- The event that the origin is connected to `y` inside the sub-configuration carried by
the finite edge set `D`. -/
abbrev boxConn (D : Finset (Sym2 M.V)) (y : M.V) : Set (Config M.V) :=
  M.boxConnAt D (0 : M.V) y

/-- The event that the cluster of the origin in the configuration with the single edge `e`
forced to the state `η` leaves the lattice ball of radius `R`. -/
def escapeForce (e : Sym2 M.V) (η : Config M.V) (R : ℝ) : Set (Config M.V) :=
  {ω | ∃ z : M.V, z ∉ M.ball R ∧ Connects (forceOn ({e} : Set (Sym2 M.V)) η ω) (0 : M.V) z}

/-- The event that the origin is connected to `y` inside the sub-configuration carried by the
finite edge set `D`, in the configuration with the single edge `e` forced to the state `η`. -/
def boxForce (e : Sym2 M.V) (η : Config M.V) (D : Finset (Sym2 M.V)) (y : M.V) :
    Set (Config M.V) :=
  {ω | Connects (M.restrictConf D (forceOn ({e} : Set (Sym2 M.V)) η ω)) (0 : M.V) y}

end SourceModelData

end PercLib.CriticalLRP.Orchestration
