/-
Bridge between the direction-A nine-tau diagram (`nineDiag`, `nineShapeChunk`, `Nine.NineDefs`)
and the direction-B diagram of `m2: Defs` (`ordProd`, `ordSlotU`, `ordSlotV`, `ordD`).

Both diagrams are the product of the same nine two-point factors on the split six-leaf tree; they
differ only in the order of the nine factors and in the argument order of the internal vertices.
These equalities let a direction-B evaluation of `ordD` be substituted directly into
`Nine.NineIntegration.fifth_moment_ordinary_le_of_nineShapeEval`.

Supplied by Ultramath `smwpv4yqm` member `m1` (direction d3, task direction A).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.NineCover
public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Defs

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- The direction-A diagram and the direction-B diagram are the same nine-factor product. -/
theorem nineDiag_eq_ordProd (π : Sym2 V → unitInterval) (j : Fin 7)
    (b0 b1 b2 b3 b4 t c u v w : V) :
    nineDiag π j b0 b1 b2 b3 b4 t u v w c = ordProd π j b0 b1 b2 b3 b4 t c u v w := by
  rw [nineDiag_eq_explicit]
  fin_cases j <;> simp [ordProd, Fin.prod_univ_six, Fin.succAbove, armSrc, armTgt] <;> ac_rfl

/-- `lift5 0 = 0`, so the root terminal is the same vector entry in both diagrams. -/
theorem lift5_zero : lift5 (0 : Fin 5) = (0 : Fin 6) := rfl

/-- The direction-A per-shape chunk and the direction-B per-shape diagram agree. -/
theorem nineShapeChunk_eq_ordD (π : Sym2 V → unitInterval) (T : Fin 6 → V) (k : Fin 15)
    (j : Fin 7) :
    nineShapeChunk π T k j = ordD π k j T := by
  by_cases h : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0
  · simp only [nineShapeChunk, ordD, h, ite_true, ordSlotU, nineShapeDiag, lift5_zero,
      nineDiag_eq_ordProd]
  · have h2 : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0 :=
      (pat_root_slot k).resolve_left h
    have h2' : lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2) = (0 : Fin 6) := by
      rw [h2]; rfl
    simp only [nineShapeChunk, ordD, h, ite_false, ordSlotV, nineShapeDiag, h2',
      nineDiag_eq_ordProd]

end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nineDiag_eq_ordProd
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nineShapeChunk_eq_ordD
