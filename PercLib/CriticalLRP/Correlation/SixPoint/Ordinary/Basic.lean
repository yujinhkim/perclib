/-
Ordinary `p = 5`, `k = 0`: permutation infrastructure for the nine-tau diagrams.

Supplied by Ultramath `smwpv4yqm` member `m2` (direction `d1`, task B).

`tsum_nine_perm` lets the nine extended sums of a nine-tau diagram be permuted freely; it is
used to move the four internal sums `c,u,v,w` outside the five free-terminal sums so that the
free terminals can be summed out by the row/column-sum identities.  The nine block rotations
`ordPermA`, …, `ordPermI` put the four internal sums in the peeling order of the tree for each
of the seven split arms and each of the two root positions; they are pure permutations of the
summation indices and introduce no hypothesis.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Defs

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

set_option linter.unusedSimpArgs false

variable {V : Type*}

/-! ## Ninefold extended sums and their permutations -/

/-- `Fin 9 → V` as a ninefold product. -/
def fin9Prod : (Fin 9 → V) ≃ V × V × V × V × V × V × V × V × V where
  toFun X := (X 0, X 1, X 2, X 3, X 4, X 5, X 6, X 7, X 8)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
    p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2]
  left_inv X := by funext i; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨a, b, c, d, e, f, g, h, i⟩ := p
    rfl

/-- A ninefold nested sum as one sum over `Fin 9 → V`. -/
theorem tsum_fin9 (G : (Fin 9 → V) → ℝ≥0∞) :
    (∑' X : Fin 9 → V, G X) =
      ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6, ∑' x7, ∑' x8,
        G ![x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
  rw [← Equiv.tsum_eq fin9Prod.symm G]
  simp only [ENNReal.tsum_prod']
  rfl

/-- A ninefold extended sum is invariant under permuting the nine index positions. -/
theorem tsum_fin9_perm (σ : Equiv.Perm (Fin 9)) (G : (Fin 9 → V) → ℝ≥0∞) :
    (∑' X : Fin 9 → V, G (fun i => X (σ i))) = ∑' X : Fin 9 → V, G X :=
  Equiv.tsum_eq (Equiv.arrowCongr σ.symm (Equiv.refl V)) G

/-- The nested form of `tsum_fin9_perm`: the nine extended sums may be permuted freely. -/
theorem tsum_nine_perm (σ : Equiv.Perm (Fin 9))
    (H : V → V → V → V → V → V → V → V → V → ℝ≥0∞) :
    (∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6, ∑' x7, ∑' x8,
        H (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 0))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 1))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 2))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 3))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 4))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 5))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 6))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 7))
          (![x0, x1, x2, x3, x4, x5, x6, x7, x8] (σ 8)))
      = ∑' x0, ∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' x5, ∑' x6, ∑' x7, ∑' x8,
          H x0 x1 x2 x3 x4 x5 x6 x7 x8 := by
  rw [← tsum_fin9 (G := fun X => H (X (σ 0)) (X (σ 1)) (X (σ 2)) (X (σ 3)) (X (σ 4))
    (X (σ 5)) (X (σ 6)) (X (σ 7)) (X (σ 8)))]
  rw [tsum_fin9_perm σ (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7) (X 8))]
  rw [tsum_fin9 (G := fun X => H (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7) (X 8))]
  rfl

/-- An `Equiv.Perm (Fin 9)` from a vector and its inverse. -/
def perm9Of (v w : Fin 9 → Fin 9) (h₁ : ∀ i, w (v i) = i) (h₂ : ∀ i, v (w i) = i) :
    Equiv.Perm (Fin 9) where
  toFun := v
  invFun := w
  left_inv := h₁
  right_inv := h₂

/-- The block rotation `['5, 6, 7, 8, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermA : Equiv.Perm (Fin 9) :=
  perm9Of ![5, 6, 7, 8, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 0, 1, 2, 3] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['6, 5, 7, 8, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermB : Equiv.Perm (Fin 9) :=
  perm9Of ![6, 5, 7, 8, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 1, 0, 2, 3] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['6, 7, 5, 8, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermC : Equiv.Perm (Fin 9) :=
  perm9Of ![6, 7, 5, 8, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 2, 0, 1, 3] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['6, 7, 8, 5, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermD : Equiv.Perm (Fin 9) :=
  perm9Of ![6, 7, 8, 5, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 3, 0, 1, 2] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['7, 8, 6, 5, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermE : Equiv.Perm (Fin 9) :=
  perm9Of ![7, 8, 6, 5, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 3, 2, 0, 1] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['5, 7, 6, 8, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermF : Equiv.Perm (Fin 9) :=
  perm9Of ![5, 7, 6, 8, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 0, 2, 1, 3] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['7, 6, 8, 5, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermG : Equiv.Perm (Fin 9) :=
  perm9Of ![7, 6, 8, 5, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 3, 1, 0, 2] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['7, 8, 5, 6, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermH : Equiv.Perm (Fin 9) :=
  perm9Of ![7, 8, 5, 6, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 2, 3, 0, 1] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

/-- The block rotation `['7, 6, 5, 8, 0, 1, 2, 3, 4']` of the nine sums (four internal sums out, five
free-terminal sums in). -/
def ordPermI : Equiv.Perm (Fin 9) :=
  perm9Of ![7, 6, 5, 8, 0, 1, 2, 3, 4] ![4, 5, 6, 7, 8, 2, 1, 0, 3] (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)

end PercLib.CriticalLRP.TreeExpansion.SixPoint
