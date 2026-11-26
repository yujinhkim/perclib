/-
Swarm `smwxii2d9`, member `m1`, direction d3 (`PINNED-EAR-ELIMINATION`).

Definitions for the root-socket evaluation of the `k = 2` slot products `slotProd2`.

The mathematical point of the pin is that the last surviving joint group has its centre summed
and one ear held (the "pin"), and the value of that step does not depend on which vertex of `V` is
pinned: `tsum_jointP_centre` has no condition on the pinned vertex.  Hence the pinned-ear caveat
is a condition on the sharing structure (the pin must be taken at a leaf of the current diagram)
and not on the vertex.

Definition content: `monomial2`, the value `(E|K|²)²(E|K|)³` of every socket evaluation.  It is
stated with an explicit basepoint so that the definition needs no algebraic structure on `V`.
The socket evaluations in `Main.lean` use it as their common right-hand side.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.Defs

/-!
# Root-socket evaluation: definitions

`monomial2` is the `p = 5`, `k = 2` value `(E|K|²)²(E|K|)³` in which every socket evaluation of
the fifteen socket theorems are stated.  It gives them a common right-hand side.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval2.RootSocket

variable {V : Type*}

/-- The `p = 5`, `k = 2` monomial `(E|K|²)²(E|K|)³` at the basepoint `v`.  Every socket sum of
this file is stated with basepoint `v = 0`; the basepoint is kept explicit so that the definition
needs no algebraic structure on `V`. -/
noncomputable def monomial2 (π : Sym2 V → unitInterval) (v : V) : ℝ≥0∞ :=
  (secondMoment π v) ^ 2 * (∑' x, tau π v x) ^ 3

end PercLib.CriticalLRP.SixPoint.SplitEval2.RootSocket
