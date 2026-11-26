/-
Coordinator axiom audit for the one-stage attachment history reindexing.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistSpine.Bridge

/-!
# Axiom audit for the one-stage `Hist` reindexing

This covers the new bridge only; the closed-form iterated-weight evaluation and its
packaging into the general fresh profile remain open.
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417HistToSpine

#print axioms prod_splitAt
#print axioms tsum_splitAt_prod
#print axioms iterPow_one_eq
#print axioms tsum_iterPow_succ
#print axioms tsum_iterPow_mul
#print axioms tsum_iterPow_chain
#print axioms splitAt_eq_of_decidableEq
#print axioms prod_splitWt
#print axioms histW_snoc_tsum
