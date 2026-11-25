/-
Ordinary `p = 5`, `k = 0`: exact evaluation of the fourteen nine-tau slot diagrams.

Supplied by Ultramath `smwpv4yqm` member `m2` (direction `d1`, task B).

Each of the fourteen diagrams (seven split arms `j` times two root positions) is the product of
nine two-point factors of `Defs.ordProd` summed over the four internal points `c,u,v,w` and the
five free terminals.  Because the nine factors form a *tree* whose five leaves are exactly the
free terminals and whose remaining vertex is the fixed root, summing the leaves out with
`tau_row`/`tau_col` leaves a tree on five vertices, and its four edges give four more factors of
the susceptibility.  The result is `(∑' x, tau π 0 x) ^ 9` in every case, with no finiteness
hypothesis: all values stay in `ℝ≥0∞` and the summation permutations are `ENNReal` identities.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Basic
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Final

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

set_option linter.unusedSimpArgs false

variable {V : Type*} [Countable V] [AddCommGroup V] in
/-- **The slot diagram with the root in comb slot `0` evaluates to `χ ^ 9`.**  After the block
rotation `ordPerm` the five free terminals `b₁,…,b₄,t` are summed out (one factor `χ` each, since
each is a leaf of the nine-edge tree) and the residual four-edge tree on `{0,c,u,v,w}` contributes
`χ ^ 4`.  `hq` is used only through `tau_row`/`tau_col`. -/
theorem ordSlotU_tsum (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (j : Fin 7) (root : V) :
    (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, ordSlotU π j root b1 b2 b3 b4 t) =
      (∑' x, tau π 0 x) ^ 9 := by
  have hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x := fun a => tau_row π hq a
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x := fun b => tau_col π hq b
  fin_cases j
  · simp only [ordSlotU]
    refine (tsum_nine_perm ordPermA (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 0 root y4 y5 y6 y7 y8 y0 y1 y2 y3)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotU]
    refine (tsum_nine_perm ordPermB (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 1 root y4 y5 y6 y7 y8 y1 y0 y2 y3)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotU]
    refine (tsum_nine_perm ordPermC (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 2 root y4 y5 y6 y7 y8 y2 y0 y1 y3)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotU]
    refine (tsum_nine_perm ordPermD (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 3 root y4 y5 y6 y7 y8 y3 y0 y1 y2)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotU]
    refine (tsum_nine_perm ordPermD (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 4 root y4 y5 y6 y7 y8 y3 y0 y1 y2)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotU]
    refine (tsum_nine_perm ordPermB (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 5 root y4 y5 y6 y7 y8 y1 y0 y2 y3)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotU]
    refine (tsum_nine_perm ordPermC (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 6 root y4 y5 y6 y7 y8 y2 y0 y1 y3)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring

variable {V : Type*} [Countable V] [AddCommGroup V] in
/-- **The slot diagram with the root in comb slot `2` evaluates to `χ ^ 9`.**  Same argument for
the three patterns whose comb slot `2` carries the root; the residual four-edge tree on
`{0,c,u,v,w}` is a different tree for each split arm `j`, which is why the block rotation depends
on `j`. -/
theorem ordSlotV_tsum (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (j : Fin 7) (root : V) :
    (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, ordSlotV π j root b0 b1 b3 b4 t) =
      (∑' x, tau π 0 x) ^ 9 := by
  have hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x := fun a => tau_row π hq a
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x := fun b => tau_col π hq b
  fin_cases j
  · simp only [ordSlotV]
    refine (tsum_nine_perm ordPermE (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 0 y4 y5 root y6 y7 y8 y3 y2 y0 y1)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotV]
    refine (tsum_nine_perm ordPermE (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 1 y4 y5 root y6 y7 y8 y3 y2 y0 y1)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotV]
    refine (tsum_nine_perm ordPermF (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 2 y4 y5 root y6 y7 y8 y0 y2 y1 y3)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotV]
    refine (tsum_nine_perm ordPermG (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 3 y4 y5 root y6 y7 y8 y3 y1 y0 y2)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotV]
    refine (tsum_nine_perm ordPermG (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 4 y4 y5 root y6 y7 y8 y3 y1 y0 y2)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotV]
    refine (tsum_nine_perm ordPermH (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 5 y4 y5 root y6 y7 y8 y2 y3 y0 y1)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring
  · simp only [ordSlotV]
    refine (tsum_nine_perm ordPermI (H := fun y0 y1 y2 y3 y4 y5 y6 y7 y8 =>
      ordProd π 6 y4 y5 root y6 y7 y8 y2 y1 y0 y3)).trans ?_
    simp only [ordProd, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    ring

end PercLib.CriticalLRP.TreeExpansion.SixPoint
