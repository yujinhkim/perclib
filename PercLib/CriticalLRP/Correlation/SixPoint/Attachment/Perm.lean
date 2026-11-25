/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Permutation invariance of an eight-fold extended sum, used to put the free variables of a
six-terminal tree diagram into the peeling order.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Final
public import PercLib.CriticalLRP.Correlation.SixPoint.FullMoment

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- `Fin 8 → V` as an eightfold product. -/
def fin8Prod : (Fin 8 → V) ≃ V × V × V × V × V × V × V × V where
  toFun X := (X 0, X 1, X 2, X 3, X 4, X 5, X 6, X 7)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
    p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2]
  left_inv X := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨a, b, c, d, e, f, g, h⟩ := p
    rfl

/-- An eightfold nested sum as one sum over `Fin 8 → V`. -/
theorem tsum_fin8 (G : (Fin 8 → V) → ℝ≥0∞) :
    (∑' X : Fin 8 → V, G X) =
      ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6, ∑' x7,
        G ![x0, x1, x2, x3, x4, x5, x6, x7] := by
  rw [← Equiv.tsum_eq fin8Prod.symm G]
  simp only [ENNReal.tsum_prod']
  rfl

/-- An eightfold sum is invariant under permuting the eight index positions. -/
theorem tsum_fin8_perm (σ : Equiv.Perm (Fin 8)) (G : (Fin 8 → V) → ℝ≥0∞) :
    (∑' X : Fin 8 → V, G (fun i => X (σ i))) = ∑' X : Fin 8 → V, G X :=
  Equiv.tsum_eq (Equiv.arrowCongr σ.symm (Equiv.refl V)) G

/-- The nested form of `tsum_fin8_perm`. -/
theorem tsum_eight_perm (σ : Equiv.Perm (Fin 8))
    (H : V → V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6, ∑' x7,
        H (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 0)) (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 1))
          (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 2)) (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 3))
          (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 4)) (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 5))
          (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 6)) (![x0, x1, x2, x3, x4, x5, x6, x7] (σ 7)))
      = ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6, ∑' x7,
          H x0 x1 x2 x3 x4 x5 x6 x7 := by
  rw [← tsum_fin8 (G := fun X => H (X (σ 0)) (X (σ 1)) (X (σ 2)) (X (σ 3)) (X (σ 4))
    (X (σ 5)) (X (σ 6)) (X (σ 7)))]
  rw [tsum_fin8_perm σ (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7))]
  rw [tsum_fin8 (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7))]
  rfl

end PercLib.CriticalLRP.TreeExpansion.SixPoint

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- The double star sum in the partner-first order. -/
theorem tsum_jointP_centre' [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (r : V) :
    (∑' q, ∑' c, jointP π r q c) = secondMoment π 0 := by
  rw [ENNReal.tsum_comm]
  exact tsum_jointP_centre π hq r

end PercLib.CriticalLRP.TreeExpansion.SixPoint
