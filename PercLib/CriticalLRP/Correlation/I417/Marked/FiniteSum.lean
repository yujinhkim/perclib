/-
An independently rebuilt direction (Ultramath swarm `smwwt6noq`, member `m2`, direction B).
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Marked.Numerics

/-!
# The finite-vertex form of the marked diagram expression

`I417Marked.Defs.labelledMarkedDiagram` is defined with `ℝ≥0∞`-valued `tsum`s, so that it applies
to the countably infinite canonical model where the two-point function may be `⊤`.  The
probability side, however, produces a **literal finite sum**: `Real.prob_le_sum_shapes` bounds

  `prob pr {ω | ∀ a ∈ Z, Conn ends ω v (y a)}`
  `≤ ∑ t : LTon α Z, ∑ φ : t.1.IPos → V, ∏ e : AEdge t.1, prob pr (ConnEvent ends y v t.1 φ e)`

with `[Fintype V]`, and each factor `prob pr (ConnEvent ... e)` is
`k (Real.srcPos t φ v e) (Real.dstPos t φ y e)` for `k a b := prob pr (connSet a b)`.

This file proves that the marked diagram sum is *exactly* that literal finite double sum, with
the marked label pinned at `w`:

* `tsum_label_eq_sum` -- the label assignments form a finite index type, so `tsum` is a
  `Finset.sum`;
* `posSumWtE_eq_sum` -- likewise for the assignments of vertices to the internal positions, so
  the `ℝ≥0∞` `tsum` of `Real.posSumWtE` is the finite atlas product sum;
* `labelledMarkedDiagram_eq_finiteSum` -- the composite: the marked diagram sum equals
  `∑_t ∑_y ∑_φ (1[y(mark) = w] · ∏_e k (src e) (dst e))`.

That is the exact finite-vertex input that a marked realization bound (the `(A)` side) must
supply.  The remaining, unproved step is the `ℝ → ℝ≥0∞` (`ENNReal.ofReal`) transfer of the
probability bound and the identification of `prob pr ∘ ConnEvent` with a symmetric kernel; this
file does **not** assume that transfer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP.TreeExpansion

universe u v

/-- **A finite label-assignment space**: for a finite vertex set the `ℝ≥0∞` `tsum` over the
assignments of vertices to the labels `Fin p ⊕ PUnit` is a finite sum. -/
theorem tsum_label_eq_sum {W : Type v} [Fintype W] (p : ℕ) (G : (Label p → W) → ℝ≥0∞) :
    (∑' y : Label p → W, G y) = ∑ y : Label p → W, G y := by
  rw [tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha)]

/-- **A finite vertex set: the atlas product summed over internal positions is a literal finite
sum.**  This is the quantity that the covering + BK bound `Real.prob_le_sum_shapes` produces. -/
theorem posSumWtE_eq_sum {α : Type u} {W : Type v} [Fintype W]
    (k : W → W → ℝ≥0∞) (t : RTree α) (y : α → W) (c : W) :
    Real.posSumWtE k t y c
      = ∑ φ : t.IPos → W,
          ∏ e : Real.AEdge t,
            k (Real.srcPos t φ c e) (Real.dstPos t φ y e) := by
  rw [Real.posSumWtE,
    tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha)]

/-- **The finite-vertex form of the marked diagram expression.**  For a finite vertex set the
labelled marked diagram sum is the literal finite double sum over labelled shapes, label
assignments (with the mark pinned at `w`) and internal position assignments of the atlas edge
product.  This is the exact shape of the right-hand side of `Real.prob_le_sum_shapes`, with the
marked label fixed. -/
theorem labelledMarkedDiagram_eq_finiteSum {W : Type v} [Fintype W] [DecidableEq W]
    (k : W → W → ℝ≥0∞) (p : ℕ) (x w : W) :
    labelledMarkedDiagram k p x w
      = ∑ t : LTon (Label p) (Finset.univ : Finset (Label p)),
          ∑ y : Label p → W,
            (if y (markLabel p) = w then 1 else 0) *
              ∑ φ : t.1.IPos → W,
                ∏ e : Real.AEdge t.1,
                  k (Real.srcPos t.1 φ x e) (Real.dstPos t.1 φ y e) := by
  classical
  rw [labelledMarkedDiagram]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [tsum_label_eq_sum p (fun y =>
    (if y (markLabel p) = w then 1 else 0) * Real.posSumWtE k t.1 y x)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [posSumWtE_eq_sum k t.1 y x]

end PercLib.CriticalLRP.I417Marked
