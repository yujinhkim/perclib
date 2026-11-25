/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
/-
Nearest-neighbour comparison objects for the explicit source-model witness.

The source-model witness `Witness.sourceModelWitness d hd α hα` uses the normalized
sup norm `ρ v = 2‖v‖∞` and the source kernel `K r = r^{-d-α}/(d+α)`, hence
`J_w(x,y) = (2‖x-y‖∞)^{-d-α}/(d+α)`; a nearest-neighbour pair of `ℤ^d` is at
normalized radius `2` and carries intensity `2^{-d-α}/(d+α)`.  To compare `β_c` of
the witness with ordinary nearest-neighbour bond percolation on `ℤ^d` we record
here the nearest-neighbour intensity `nnKernel d` (equal to `1` on pairs at
sup-norm distance one and `0` elsewhere) and the proposition `NNSupercritical d`
saying that this nearest-neighbour model percolates at some parameter.

`NNSupercritical d` is *not* proved in this file, nor anywhere in the campaign
tree at the time of writing: it is the supercritical half of nearest-neighbour
bond percolation on `ℤ^d` (`d ≥ 2`), i.e. `p_c(ℤ^d, bond) < 1`, which is a
genuine external theorem and not a restatement of `β_c > 0` for the long-range
witness.  It is exposed as a named hypothesis so that the companion module
`BetaCritPos.lean` can state exactly what remains open.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.CountableProduct.Critical

/-!
# Nearest-neighbour comparison objects for the explicit source-model witness

This module defines the unit nearest-neighbour intensity `nnKernel d` on `ℤ^d` and the
proposition `NNSupercritical d` (nearest-neighbour bond percolation percolates at some
parameter).  Nothing here asserts `NNSupercritical d`; it names the missing supercritical
input used by
`PercLib.CriticalLRP.Orchestration.ModelWitness.NNComparison.BetaCritPos`.
-/

@[expose] public section

set_option autoImplicit false

open scoped NNReal

namespace PercLib.CriticalLRP.Orchestration.Witness.NNComparison

open PercLib.CriticalLRP

/-- The nearest-neighbour intensity on `ℤ^d`: `1` on unordered pairs at sup-norm
(equivalently `ℓ¹`-) distance one, `0` elsewhere.  On the diagonal the value is
`0` automatically, because `‖0‖ ≠ 1`. -/
noncomputable def nnKernel (d : ℕ) : Sym2 (Fin d → ℤ) → ℝ :=
  Sym2.lift ⟨fun x y => if ‖x - y‖ = 1 then (1 : ℝ) else 0, by
    intro x y
    change (if ‖x - y‖ = 1 then (1 : ℝ) else 0)
      = (if ‖y - x‖ = 1 then (1 : ℝ) else 0)
    have h : ‖x - y‖ = ‖y - x‖ := by rw [← norm_neg, neg_sub]
    rw [h]⟩

theorem nnKernel_mk (d : ℕ) (x y : Fin d → ℤ) :
    nnKernel d s(x, y) = if ‖x - y‖ = 1 then (1 : ℝ) else 0 := rfl

theorem nnKernel_nonneg (d : ℕ) : ∀ e : Sym2 (Fin d → ℤ), 0 ≤ nnKernel d e := by
  intro e
  induction e using Sym2.ind with
  | _ x y => rw [nnKernel_mk]; split_ifs <;> norm_num

/-- The constant `c = 2^{-d-α}/(d+α)` relating the witness kernel to the paper's literal
power law `lrKernel d α`: the normalized sup norm contributes `2^{-d-α}` and the
source-normalized derivative `|K' r| = r^{-d-α-1}` contributes `(d+α)⁻¹`. -/
noncomputable def rescaleConstant (d : ℕ) (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(d : ℝ) - α) / ((d : ℝ) + α)

theorem rescaleConstant_pos {d : ℕ} {α : ℝ} (hα : 0 < α) : 0 < rescaleConstant d α := by
  unfold rescaleConstant
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by positivity)

/-- **The nearest-neighbour supercriticality input.**  Bond percolation on `ℤ^d`
with the unit nearest-neighbour intensity percolates almost surely at some
parameter `γ`; equivalently, at edge probability `1 - exp(-γ)`.

This is the standard fact `p_c(ℤ^d, bond) < 1` for `d ≥ 2`.  It is recorded as a
named `Prop` so that the companion module can state precisely which input is
still missing from the campaign tree, rather than assuming `β_c > 0` itself. -/
def NNSupercritical (d : ℕ) : Prop :=
  ∃ γ : NNReal, infiniteClusterProb (nnKernel d) (nnKernel_nonneg d) γ = 1

end PercLib.CriticalLRP.Orchestration.Witness.NNComparison
