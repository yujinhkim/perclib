/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.CountableProduct.Base
public import PercLib.CriticalLRP.CountableProduct.Marks
public import PercLib.CriticalLRP.CountableProduct.ZeroOne
public import PercLib.CriticalLRP.CountableProduct.Critical
public import PercLib.CriticalLRP.CountableProduct.TwoPoint
public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.CountableProduct.MonotoneMoments

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section
