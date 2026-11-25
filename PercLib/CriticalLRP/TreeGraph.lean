/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.TreeGraph.Connectivity
public import PercLib.CriticalLRP.TreeGraph.ThreePoint
public import PercLib.CriticalLRP.TreeGraph.ClusterMoments
public import PercLib.CriticalLRP.TreeGraph.Spatial
public import PercLib.CriticalLRP.TreeGraph.Extended
public import PercLib.CriticalLRP.TreeGraph.Monotone

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section
