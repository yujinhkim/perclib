/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Six-terminal event shorthand, fourteen slot diagrams, and their fixed summation
permutations for the `p = 5`, `k = 1` mixed moment. Definitions and finite
permutation witnesses live here; the proof modules consume them.

Integrated from Ultramath `smwprafq1` member `m1` at base revision
`5c25062c071ed99bd44904ceb185d8dba8f9093f`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Defs
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Perm

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- The six-terminal arm system, as a predicate with the five comb slots and the sixth terminal. -/
def ShapeEv (G : SimpleGraph V) (b0 b1 b2 b3 b4 t : V) (j : Fin 7) (c u v w : V) : Prop :=
  CombSystem G b0 b1 b2 b3 b4 t u v w c j

/-! ## The fourteen slot diagrams -/
noncomputable def slotU (π : Sym2 V → unitInterval) (j : Fin 7) (b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  match j with
  | 0 => ∑' u, ∑' v, ∑' w, (jointP π b0 t u * (tau π b1 u * (tau π b2 v * (tau π b3 w * (tau π b4 w * (tau π u v * tau π v w))))))
  | 1 => ∑' v, ∑' c, ∑' w, (jointP π b0 c v * (tau π b1 c * (tau π t c * (tau π b2 v * (tau π b3 w * (tau π b4 w * tau π v w))))))
  | 2 => ∑' v, ∑' c, ∑' w, (jointP π b0 b1 v * (tau π b2 c * (tau π c v * (tau π t c * (tau π b3 w * (tau π b4 w * tau π v w))))))
  | 3 => ∑' v, ∑' w, ∑' c, (jointP π b0 b1 v * (tau π b2 v * (tau π b4 w * (tau π v w * (tau π b3 c * (tau π t c * tau π c w))))))
  | 4 => ∑' v, ∑' w, ∑' c, (jointP π b0 b1 v * (tau π b2 v * (tau π b3 w * (tau π v w * (tau π b4 c * (tau π t c * tau π c w))))))
  | 5 => ∑' c, ∑' v, ∑' w, (jointP π b0 b1 c * (tau π c v * (tau π b2 v * (tau π t c * (tau π b3 w * (tau π b4 w * tau π v w))))))
  | 6 => ∑' v, ∑' c, ∑' w, (tau π b3 w * (tau π b4 w * (tau π c w * (tau π t c * (tau π v c * (tau π b2 v * jointP π b0 b1 v))))))

noncomputable def slotV (π : Sym2 V → unitInterval) (j : Fin 7) (b0 b1 b2 b3 b4 t : V) : ℝ≥0∞ :=
  match j with
  | 0 => ∑' w, ∑' u, ∑' c, (jointP π b2 u w * (tau π b1 u * (tau π c u * (tau π b0 c * (tau π t c * (tau π b3 w * tau π b4 w))))))
  | 1 => ∑' w, ∑' u, ∑' c, (jointP π b2 u w * (tau π b0 u * (tau π c u * (tau π b1 c * (tau π t c * (tau π b3 w * tau π b4 w))))))
  | 2 => ∑' v, ∑' u, ∑' w, (jointP π b2 t v * (tau π u v * (tau π b0 u * (tau π b1 u * (tau π b3 w * (tau π b4 w * tau π v w))))))
  | 3 => ∑' w, ∑' u, ∑' c, (jointP π b2 u w * (tau π c w * (tau π b4 w * (tau π b0 u * (tau π b1 u * (tau π b3 c * tau π t c))))))
  | 4 => ∑' w, ∑' u, ∑' c, (jointP π b2 u w * (tau π c w * (tau π b3 w * (tau π b0 u * (tau π b1 u * (tau π b4 c * tau π t c))))))
  | 5 => ∑' w, ∑' c, ∑' u, (jointP π b2 c w * (tau π t c * (tau π u c * (tau π b0 u * (tau π b1 u * (tau π b3 w * tau π b4 w))))))
  | 6 => ∑' c, ∑' u, ∑' w, (jointP π b2 u c * (tau π c w * (tau π b3 w * (tau π b4 w * (tau π t c * (tau π b0 u * tau π b1 u))))))

def permU0 : Equiv.Perm (Fin 8) where
  toFun := ![5, 4, 6, 0, 1, 7, 3, 2]
  invFun := ![3, 4, 7, 6, 1, 0, 2, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permU1 : Equiv.Perm (Fin 8) where
  toFun := ![5, 6, 0, 4, 1, 7, 3, 2]
  invFun := ![2, 4, 7, 6, 3, 0, 1, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permU2 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 6, 4, 1, 7, 3, 2]
  invFun := ![0, 4, 7, 6, 3, 1, 2, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permU3 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 1, 6, 3, 7, 4, 2]
  invFun := ![0, 2, 7, 4, 6, 1, 3, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permU4 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 1, 6, 2, 7, 4, 3]
  invFun := ![0, 2, 4, 7, 6, 1, 3, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permU5 : Equiv.Perm (Fin 8) where
  toFun := ![5, 0, 6, 4, 1, 7, 3, 2]
  invFun := ![1, 4, 7, 6, 3, 0, 2, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permU6 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 1, 6, 4, 7, 3, 2]
  invFun := ![0, 2, 7, 6, 4, 1, 3, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permV0 : Equiv.Perm (Fin 8) where
  toFun := ![5, 6, 1, 7, 0, 4, 3, 2]
  invFun := ![4, 2, 7, 6, 5, 0, 1, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permV1 : Equiv.Perm (Fin 8) where
  toFun := ![5, 6, 0, 7, 1, 4, 3, 2]
  invFun := ![2, 4, 7, 6, 5, 0, 1, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permV2 : Equiv.Perm (Fin 8) where
  toFun := ![5, 4, 7, 6, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 1, 0, 3, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permV3 : Equiv.Perm (Fin 8) where
  toFun := ![5, 6, 7, 3, 1, 0, 4, 2]
  invFun := ![5, 4, 7, 3, 6, 0, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permV4 : Equiv.Perm (Fin 8) where
  toFun := ![5, 6, 7, 2, 1, 0, 4, 3]
  invFun := ![5, 4, 3, 7, 6, 0, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permV5 : Equiv.Perm (Fin 8) where
  toFun := ![5, 6, 7, 1, 0, 4, 3, 2]
  invFun := ![4, 3, 7, 6, 5, 0, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def permV6 : Equiv.Perm (Fin 8) where
  toFun := ![5, 6, 7, 1, 0, 4, 3, 2]
  invFun := ![4, 3, 7, 6, 5, 0, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- The slot diagram used for the `k`-th pattern: `slotU` when the root sits in comb slot `0`
and `slotV` when it sits in comb slot `2` (`pat_root_slot` says these exhaust the patterns). -/
noncomputable def slotD (π : Sym2 V → unitInterval) (T : Fin 6 → V) (k : Fin 15)
    (j : Fin 7) : ℝ≥0∞ :=
  if PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0 then
    slotU π j (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5)
  else
    slotV π j (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))
      (T (lift5 (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4))) (T 5)

end PercLib.CriticalLRP.TreeExpansion.SixPoint
