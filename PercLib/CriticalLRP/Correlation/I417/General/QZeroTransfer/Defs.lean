/-
Accepted from Ultramath `smwzg77c3`, member `m5`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d10`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Finite-truncation forms of the `q = 0` star moment of Lemma I.4.17

The source object at `p = 3`, `q = 0` is the *one-copy* star moment
`starMoment π x y p = ∫⁻ ω, 1(x ↔ y) |K_x(ω)|^p` of `I417Gen`.  Its landed labelled expansion
`I417Gen.starMoment_eq_tsum_labelEvent` is an infinite sum over *all* label tuples `Fin p → V`,
while every BK / tree-graph / correlation bound in PercLib controls only finitely many labels (and
usually works in finite volume).  This file introduces the two truncations that bridge that gap:

* `labSum π x y p F` — the partial sum over a finite family `F` of label tuples, i.e. exactly the
  quantity a labelled union bound over finitely many labels produces;
* `truncMass ω x S` / `truncStar π x y p S` — the star moment with the cluster volume replaced by
  its mass inside a finite vertex set `S`, i.e. the object a finite-volume computation controls.

`Main.lean` proves that the source object is the supremum of both families and therefore that
uniform truncation bounds transfer to it, and conversely that any strict violation is already
witnessed on a finite truncation.

The right-hand side of the target is named `hgapRHS`, so that the two-term shape
`C3 · polyK 3 0 y · χ⁴ + C4 · polyK 4 0 y · χ³` with `χ = (M.cutMassAt r 0).toReal` is stated once.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main

/-! # Truncation definitions -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP

namespace Exhaustion

variable {V : Type*} [Countable V]

/-- **The finite-label truncation of the `q = 0` star moment.**  For a finite family `F` of label
tuples this is the partial sum `∑_{f ∈ F} μ(x ↔ y, f ⊆ K_x)` of the labelled expansion
`I417Gen.starMoment_eq_tsum_labelEvent`. -/
noncomputable def labSum (π : Sym2 V → unitInterval) (x y : V) (p : ℕ)
    (F : Finset (Fin p → V)) : ℝ≥0∞ :=
  ∑ f ∈ F, (edgeMeasure π) (I417A.labelEvent x f ∩ connSet x y)

/-- **The cluster mass inside a finite vertex set**, written as a finite sum so that no `encard`
case distinction is needed.  This is the `p = 1` truncation of `Percolation.cardFun (cluster ω x)`
(`iSup_truncMass` in `Main.lean`). -/
noncomputable def truncMass (ω : Config V) (x : V) (S : Finset V) : ℝ≥0∞ :=
  ∑ w ∈ S, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w

/-- **The star moment with the cluster volume truncated to a finite vertex set.**  This is the
finite-volume object: `starMoment_le_of_truncStar_le` in `Main.lean` shows that the source star
moment is the supremum of `truncStar π x y p S` over finite `S`. -/
noncomputable def truncStar (π : Sym2 V → unitInterval) (x y : V) (p : ℕ)
    (S : Finset V) : ℝ≥0∞ :=
  ∫⁻ ω, (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω * (truncMass ω x S) ^ p
    ∂(edgeMeasure π)

end Exhaustion

namespace Orchestration
namespace SourceModelData

/-- **The right-hand side of the `p = 3`, `q = 0` target.**  With `χ = (M.cutMassAt r 0).toReal`
this is `C3 · polyK (cutTwoPoint r) 3 0 y · χ⁴ + C4 · polyK (cutTwoPoint r) 4 0 y · χ³`, the
`ℓ = 3` and `ℓ = 4` terms of Lemma I.4.17. -/
noncomputable def hgapRHS (M : SourceModelData) (r : ℝ) (y : M.V) (C3 C4 : ℝ) : ℝ :=
  C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
    + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3

/-- `hgapRHS` is nonnegative for nonnegative constants: the cutoff two-point function is
nonnegative, so are its iterated powers. -/
theorem hgapRHS_nonneg (M : SourceModelData) (r : ℝ) (y : M.V) {C3 C4 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) : 0 ≤ M.hgapRHS r y C3 C4 := by
  have hT : ∀ a b : M.V, 0 ≤ M.cutTwoPoint r a b := fun a b => M.cutTwoPoint_nonneg r a b
  have hp3 : 0 ≤ I418C.polyK (M.cutTwoPoint r) 3 0 y := I418C.polyK_nonneg _ hT 3 0 y
  have hp4 : 0 ≤ I418C.polyK (M.cutTwoPoint r) 4 0 y := I418C.polyK_nonneg _ hT 4 0 y
  have hχ : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  unfold hgapRHS
  exact add_nonneg (mul_nonneg (mul_nonneg hC3 hp3) (pow_nonneg hχ 4))
    (mul_nonneg (mul_nonneg hC4 hp4) (pow_nonneg hχ 3))

end SourceModelData
end Orchestration

end PercLib.CriticalLRP
