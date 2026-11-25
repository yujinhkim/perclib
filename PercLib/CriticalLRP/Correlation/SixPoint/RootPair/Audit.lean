/- Integrated from reviewed Ultramath root-pair work.
Production base 1eaaabcf41deb59c0da2c83d0f2d7ad9d952510f.
Scratch source: ../../.ultramath/smwvlmbqa/m3/Audit.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.RootPair.Main
public import PercLib.CriticalLRP.Correlation.SixPoint.RootPair.Obstruction

/-!
# Standard-axiom audit for the root-in-pair diagram and arm-cost helpers.

The corrected diagram evaluation remains conditional on its displayed pointwise-cover input;
these `#print axioms` checks concern proof foundations, not existence of that cover.
-/

#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.hubChainRoot_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.tsum_hubChainRoot
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.tsum_slotChainRoot_five
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.tsum_slotChainRoot_native
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.tsum_fin105_slotChainRoot_five
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.fifth_moment_mixed_k2_le_of_chainRootBound
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction.zspan3_add_zdist_ge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction.zspan3_add_two_zdist_ge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction.fan_cost_reduction
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction.chain_cost_reduction
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction.root_pair_cost_reduction
#print axioms PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction.root_pair_cost_eq_five
#print axioms
  PercLib.CriticalLRP.TreeExpansion.HubRoot.Obstruction.chain_and_fan_cost_at_same_configuration
