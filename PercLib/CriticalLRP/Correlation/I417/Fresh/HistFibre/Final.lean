/-
The packaged history-fibre evaluation, with the printed pin--mark depth
(direction `HISTORY-FIBRE-PACKAGING`, swarm `smwxfstjy`, member `m1`).
Proofs only; every definition is in `Defs.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistFibre.Main
public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistFibre.MarkDepth

/-!
# The history fibre of the general fresh cover, in the printed normal form

Combining `histFibre_eq_histW_slotW` / `histW_slotW_zero` with the identification
`markDepthK_eq_chainM` of the first slot's chain length with production's pin--mark depth.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417HistFibre

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **The fibre of one branch, as two chains.**  With the arm target `ga` still free, the fibre sum
over the split choices `k` is the product of the closed forms of the two base slots: the pin--mark
chain `y → w` (first slot) and the mark--arm chain `w → ga` (second slot), each times its own
`χ`-power. -/
theorem histFibre_eq_twoChains {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (k : (t : Fin n) → I417GenIter.Idx t) (y w ga : V) :
    I417HistToSpine.histFibre (fun _ => τ) y w k ga =
      (χ ^ I417SplitClosedForm.chainE n k 0 I417FreshDepth.idxZero *
          I417Base.iterPow τ (I417SplitClosedForm.chainM n k 0 I417FreshDepth.idxZero) y w) *
        (χ ^ I417SplitClosedForm.chainE n k 0 idxOne *
          I417Base.iterPow τ (I417SplitClosedForm.chainM n k 0 idxOne) w ga) := by
  rw [histFibre_eq_histW_slotW τ χ hχ k y w ga, histW_slotW_zero]

/-- **The value of one branch fibre with the free arm target summed**, in the printed normal form
`χ ^ (2(n+1) - ℓ) · T^ℓ(y,w)` with `ℓ = markDepthK n k` the number of legs of the pin--mark path
(i.e. the `ℓ` of Lemma I.4.17's fresh side). -/
theorem tsum_histFibre_markDepth {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (k : (t : Fin n) → I417GenIter.Idx t) (y w : V) :
    (∑' ga : V, I417HistToSpine.histFibre (fun _ => τ) y w k ga) =
      χ ^ (2 * (n + 1) - I417FreshDepth.markDepthK n k) *
        I417Base.iterPow τ (I417FreshDepth.markDepthK n k) y w := by
  rw [tsum_histFibre_chainM τ χ hχ k y w, markDepthK_eq_chainM]

/-- The same value with the `T`-power in the orientation of the printed normal form
`T^ℓ(w,y)` is **not** obtained here: it needs the symmetry of the kernel
`τ a b = τ b a` (true for `edgeMeasure π (connSet · ·)`) and a corresponding symmetry of
`I417Base.iterPow`, which is not proved in this package.  The `T^ℓ(y,w)` form above is the exact
conclusion; the transposition is the residual gap for matching `I417FreshDepth.genFreshProfile`
literally. -/
theorem tsum_histFibre_markDepth_premises {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) :
    (∀ a : V, ∑' b : V, τ a b = χ) →
      ∀ (k : (t : Fin n) → I417GenIter.Idx t) (y w : V),
        (∑' ga : V, I417HistToSpine.histFibre (fun _ => τ) y w k ga) =
          χ ^ (2 * (n + 1) - I417FreshDepth.markDepthK n k) *
            I417Base.iterPow τ (I417FreshDepth.markDepthK n k) y w := by
  intro hχ k y w
  exact tsum_histFibre_markDepth τ χ hχ k y w

end PercLib.CriticalLRP.I417HistFibre
