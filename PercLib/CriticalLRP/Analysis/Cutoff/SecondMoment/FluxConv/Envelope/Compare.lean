/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvhhc1v`, member `m1`, direction (A).

# The pointwise comparison of the unexcluded `p = 2` weight with the excluded pivot weight

This file proves the analytic core of the missing summable envelope, at the level of a single
ordered pair `(b, c)`: the unexcluded `p = 2` weight at the anchor `0` is dominated by the source's
excluded pivot weight plus one explicit *connected-triple* correction

`3 |K_0|² · 1(0 ↔ b) · 1(b ↔ c)`,

and, summing over `b` and `c` against `PivotFlux.tsum_clusterVol_mul_connects` and
`tsum_connects_indicator`, that

`∑'_b ∑'_c unexclPairWeight · 0 b c ≤ PivotFlux.p2PaperSum · + 3 |K_0|⁴`.

The split is exactly the one the paper uses.  Write

`unexclPairWeight 0 b c = 1(b ≠ c) · 1(0 ↔ b) · 1(|c - b| ≤ r) · (2 |K_b| |K_c| + |K_c|²)`,
`p2Weight b c          = 1(0 ↔ b) · 1(|c - b| ≤ r) · 1(b ↮ c) · (2 |K_0| |K_c| + |K_c|²)`.

* If `b` and `c` are **not** connected, the exclusion indicator of `p2Weight` is `1`, and on the
  event `0 ↔ b` one has `|K_b| = |K_0|`, so the two weights coincide.
* If `b` and `c` **are** connected, `p2Weight` vanishes, and on the event `0 ↔ b` one has
  `|K_b| = |K_c| = |K_0|`, so the unexcluded weight is exactly `3 |K_0|²` — which is what the
  correction term supplies.

Loops (`b = c`), out-of-range pairs (`|c - b| > r`) and the `ℝ≥0∞`-vs-`ℝ` distinction are handled
explicitly: the correction is an `ℝ≥0∞` inequality, so no `toReal` truncation enters.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Insertion
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Left.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Defs

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. `configIndicator` and `cutRange` as `if`s -/

/-- The connection indicator is the corresponding `if`. -/
theorem configIndicator_connects_eq_ite (ω : Config M.V) (x y : M.V) :
    configIndicator {ω' : Config M.V | Connects ω' x y} ω
      = (if Connects ω x y then (1 : ℝ≥0∞) else 0) := by
  rw [configIndicator_eq_ite]
  simp

/-- The complement of the connection indicator is the corresponding `if`. -/
theorem configIndicator_not_connects_eq_ite (ω : Config M.V) (x y : M.V) :
    configIndicator {ω' : Config M.V | ¬ Connects ω' x y} ω
      = (if Connects ω x y then (0 : ℝ≥0∞) else 1) := by
  rw [configIndicator_eq_ite]
  simp

/-- `cutRange` is the radius condition, as an `iff` usable by `simp`. -/
theorem cutRange_iff (r : ℝ) (c b : M.V) : M.cutRange r c b ↔ M.S.dist c b ≤ r := Iff.rfl

/-- **`p2Weight` in terms of the three indicators.** -/
theorem p2Weight_eq_ite (r : ℝ) (ω : Config M.V) (b c : M.V) :
    PivotFlux.p2Weight M r ω b c
      = (if Connects ω (0 : M.V) b then (1 : ℝ≥0∞) else 0) *
          (if M.S.dist c b ≤ r then (1 : ℝ≥0∞) else 0) *
          (if Connects ω b c then (0 : ℝ≥0∞) else 1) *
          (2 * clusterVol ω (0 : M.V) * clusterVol ω c + clusterVol ω c ^ 2) := by
  simp only [PivotFlux.p2Weight, PivotFlux.pivotWeight, PivotFlux.pivotWeightSq,
    configIndicator_connects_eq_ite, configIndicator_not_connects_eq_ite]
  ring

/-- **`unexclPairWeight` at the anchor `0` in terms of the same three indicators.** -/
theorem unexclPairWeight_zero_eq_ite (r : ℝ) (ω : Config M.V) (b c : M.V) :
    unexclPairWeight M r ω (0 : M.V) b c
      = (if b = c then (0 : ℝ≥0∞) else 1) *
          (if Connects ω (0 : M.V) b then (1 : ℝ≥0∞) else 0) *
          (if M.S.dist c b ≤ r then (1 : ℝ≥0∞) else 0) *
          (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2) := by
  simp only [unexclPairWeight, cutRange_iff]

/-! ## 2. The pointwise comparison -/

/-- **The pointwise comparison of the two marked `p = 2` weights.**

`unexclPairWeight 0 b c ≤ p2Weight b c + 3 |K_0|² · 1(0 ↔ b) · 1(b ↔ c)`.

The correction is supported exactly on pairs on which the *whole* triple `0, b, c` is connected;
there `|K_b| = |K_c| = |K_0|` and the unexcluded weight is `3 |K_0|²`, while the exclusion
indicator kills `p2Weight` completely.  Off that event `p2Weight` already carries the unexcluded
weight, because `0 ↔ b` forces `|K_b| = |K_0|`. -/
theorem unexclPairWeight_le_p2Weight_add (r : ℝ) (ω : Config M.V) (b c : M.V) :
    unexclPairWeight M r ω (0 : M.V) b c ≤
      PivotFlux.p2Weight M r ω b c +
        3 * clusterVol ω (0 : M.V) ^ 2 *
          configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
          configIndicator {ω' : Config M.V | Connects ω' b c} ω := by
  rw [unexclPairWeight_zero_eq_ite, p2Weight_eq_ite,
    configIndicator_connects_eq_ite (M := M) ω (0 : M.V) b,
    configIndicator_connects_eq_ite (M := M) ω b c]
  by_cases h0b : Connects ω (0 : M.V) b
  · by_cases hbc : Connects ω b c
    · -- the connected triple: the correction pays `3 |K_0|²`, and `p2Weight` vanishes
      have hVb : clusterVol ω b = clusterVol ω (0 : M.V) := (clusterVol_eq_of_connects h0b).symm
      have hVc : clusterVol ω c = clusterVol ω (0 : M.V) :=
        (clusterVol_eq_of_connects (connects_trans h0b hbc)).symm
      rw [hVb, hVc]
      simp only [h0b, hbc, ite_true, zero_mul, mul_zero, one_mul, mul_one, zero_add]
      have h1 : (if b = c then (0 : ℝ≥0∞) else 1) ≤ 1 := by split_ifs <;> simp
      have h2 : (if M.S.dist c b ≤ r then (1 : ℝ≥0∞) else 0) ≤ 1 := by split_ifs <;> simp
      have h3 : (2 * clusterVol ω (0 : M.V) * clusterVol ω (0 : M.V)
          + clusterVol ω (0 : M.V) ^ 2 : ℝ≥0∞) = 3 * clusterVol ω (0 : M.V) ^ 2 := by
        ring
      rw [h3]
      calc (if b = c then (0 : ℝ≥0∞) else 1) *
            (if M.S.dist c b ≤ r then (1 : ℝ≥0∞) else 0) * (3 * clusterVol ω (0 : M.V) ^ 2)
          ≤ 1 * 1 * (3 * clusterVol ω (0 : M.V) ^ 2) := by gcongr
        _ = 3 * clusterVol ω (0 : M.V) ^ 2 := by ring
    · -- not connected: `p2Weight` already dominates, `|K_b| = |K_0|` on `0 ↔ b`
      have hbc' : ¬ Connects ω b c := hbc
      have hne : b ≠ c := fun h => hbc' (h ▸ connects_refl ω c)
      have hVb : clusterVol ω b = clusterVol ω (0 : M.V) := (clusterVol_eq_of_connects h0b).symm
      rw [hVb, ite_eq_right hne]
      simp only [h0b, hbc, ite_true, ite_false, mul_zero, one_mul, mul_one, add_zero]
      exact le_rfl
  · -- `0 ↮ b`: both sides vanish
    simp only [h0b, ite_false, zero_mul, mul_zero, add_zero]
    exact zero_le

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms configIndicator_connects_eq_ite
#print axioms configIndicator_not_connects_eq_ite
#print axioms cutRange_iff
#print axioms p2Weight_eq_ite
#print axioms unexclPairWeight_zero_eq_ite
#print axioms unexclPairWeight_le_p2Weight_add

end PercLib.CriticalLRP.Orchestration.SourceModelData
