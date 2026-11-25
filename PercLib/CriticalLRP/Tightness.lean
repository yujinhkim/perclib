/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.Tightness.MaxCluster
public import PercLib.CriticalLRP.Tightness.RealExponent
public import PercLib.CriticalLRP.Tightness.LemmaI26Averaging
public import PercLib.CriticalLRP.Tightness.LemmaI26Cutoff
public import PercLib.CriticalLRP.Tightness.TreePiecesBridge
public import PercLib.CriticalLRP.Tightness.BFSParent
public import PercLib.CriticalLRP.Tightness.ClusterWitness
public import PercLib.CriticalLRP.Tightness.MaxClusterPower
public import PercLib.CriticalLRP.Tightness.LongRangePower
public import PercLib.CriticalLRP.Tightness.TreePiecesExamples
public import PercLib.CriticalLRP.Tightness.DisplaysToTightness
public import PercLib.CriticalLRP.Tightness.Exhaustion.Locality
public import PercLib.CriticalLRP.Tightness.PointedPower
public import PercLib.CriticalLRP.Tightness.RealPieces
public import PercLib.CriticalLRP.Tightness.RealPower
public import PercLib.CriticalLRP.Tightness.CanonicalPower
public import PercLib.CriticalLRP.Tightness.Exhaustion.Restrict
public import PercLib.CriticalLRP.Tightness.EndpointCounterexample
public import PercLib.CriticalLRP.Tightness.Infinite.Power
public import PercLib.CriticalLRP.Tightness.Universal
public import PercLib.CriticalLRP.Tightness.BlockMaximum
public import PercLib.CriticalLRP.Tightness.LargestBlockMoment

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section
