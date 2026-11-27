/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m6`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d9`.

# The `ℝ≥0∞` parent of the two-term `q = 0` star gap, and its honest real form

`TwoTermStarGapE` (`Defs.lean`) is the natural extended-real parent of the target: the one-copy
star moment `starMoment (M.cutProb r) 0 y 3` bounded by
`ofReal C₃ * Kpow (cutTwoPointE r) 3 0 y * χ⁴ + ofReal C₄ * Kpow (cutTwoPointE r) 4 0 y * χ³`
with `χ = M.cutMassAt r 0` in `ℝ≥0∞`.  Here:

* `starRHSE_ne_top`, `starRHSE_toReal` — the parent is finite and its `toReal` is `starRHS`
  (`I418C.polyK` matrix powers, real `χ = (M.cutMassAt r 0).toReal`), at finite `χ`.
* `twoTermStarGapE_toReal` — the parent implies the real per-vertex target.
* `twoTermStarGap_toE` — the real per-vertex target implies the parent at finite star moment.

So the extended-real and real formulations are equivalent under the model's finiteness
hypotheses; no `⊤ ↦ 0` step is taken (an infinite `χ` gives `χ.toReal = 0`, which is excluded
rather than used).

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Main

/-! # Extended-real parent of the two-term star gap -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

@[expose] public section

namespace PercLib.CriticalLRP.I417QZeroConsumer

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.KernelPower
open PercLib.CriticalLRP.I417Gen

variable (M : SourceModelData)

/-- `starRHSE` is finite at finite truncated cluster mass. -/
theorem starRHSE_ne_top (C3 C4 : ℝ) (r : ℝ) (y : M.V) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    starRHSE M C3 C4 r y ≠ ⊤ := by
  have h3 : Kpow (M.cutTwoPointE r) 3 (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 y
  have h4 : Kpow (M.cutTwoPointE r) 4 (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ 4 0 y
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h3)
      (ENNReal.pow_ne_top hχ)
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h4)
      (ENNReal.pow_ne_top hχ)

/-- The `toReal` of the extended-real parent is the real right-hand side `starRHS`. -/
theorem starRHSE_toReal (C3 C4 : ℝ) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (r : ℝ) (y : M.V) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    (starRHSE M C3 C4 r y).toReal = starRHS M C3 C4 r y := by
  have h3 : Kpow (M.cutTwoPointE r) 3 (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ 3 0 y
  have h4 : Kpow (M.cutTwoPointE r) 4 (0 : M.V) y ≠ ⊤ :=
    M.cutKpow_ne_top_of_chi_ne_top r hχ 4 0 y
  have hp4 : (M.cutMassAt r 0) ^ 4 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hp3 : (M.cutMassAt r 0) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top hχ
  have hA := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C3)) h3) hp4
  have hB := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C4)) h4) hp3
  rw [starRHSE, ENNReal.toReal_add hA hB, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC3,
    ENNReal.toReal_ofReal hC4, ENNReal.toReal_pow, ENNReal.toReal_pow,
    M.cutKpow_toReal_eq_polyK r hχ 3 0 y, M.cutKpow_toReal_eq_polyK r hχ 4 0 y,
    starRHS, chi]

/-- **Extended-real parent `⟹` real per-vertex target** at finite truncated cluster mass. -/
theorem twoTermStarGapE_toReal (C3 C4 : ℝ) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hgapE : TwoTermStarGapE M C3 C4)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) : TwoTermStarGap M C3 C4 := by
  intro r hr y
  have hne := starRHSE_ne_top M C3 C4 r y (hχ r hr)
  have h := ENNReal.toReal_mono hne (hgapE r hr y)
  rw [M.connCubeVertexMass_eq_starMoment r y]
  rwa [starRHSE_toReal M C3 C4 hC3 hC4 r y (hχ r hr)] at h

/-- **Real per-vertex target `⟹` extended-real parent**, at finite star moment: the
`ofReal`/`toReal` round trip is exact on both sides, so the real form loses nothing. -/
theorem twoTermStarGap_toE (C3 C4 : ℝ) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hgap : TwoTermStarGap M C3 C4)
    (hSM : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V, starMoment (M.cutProb r) (0 : M.V) y 3 ≠ ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) : TwoTermStarGapE M C3 C4 := by
  intro r hr y
  have hne := starRHSE_ne_top M C3 C4 r y (hχ r hr)
  have htoReal := starRHSE_toReal M C3 C4 hC3 hC4 r y (hχ r hr)
  calc starMoment (M.cutProb r) (0 : M.V) y 3
      = ENNReal.ofReal ((starMoment (M.cutProb r) (0 : M.V) y 3).toReal) :=
        (ENNReal.ofReal_toReal (hSM r hr y)).symm
    _ = ENNReal.ofReal ((M.connCubeVertexMass r y).toReal) := by
        rw [M.connCubeVertexMass_eq_starMoment r y]
    _ ≤ ENNReal.ofReal (starRHS M C3 C4 r y) := ENNReal.ofReal_le_ofReal (hgap r hr y)
    _ = starRHSE M C3 C4 r y := by
        rw [← htoReal]
        exact ENNReal.ofReal_toReal hne

end PercLib.CriticalLRP.I417QZeroConsumer
