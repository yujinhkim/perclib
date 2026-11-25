/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwttizjk`, member `m4`, direction D8.

**Why the local clause has to be stated separately.**  This file gives a Lean-checked witness that
`LogarithmicallyIntegrable h` (the repository's global clause `∫_{r₀}^∞ |h r| dr / r < ∞`) does
*not* imply `IntegrableOnPositiveCompacts h`, and does not even imply local boundedness.

The witness is `invSpike`, which is `(x - 1)⁻¹` on `[1, 2]` and `0` elsewhere.  It is `0` on
`Ioi 3`, so its logarithmic integral over `Ioi 3` is that of the zero function; but on `[1, 2]`
(with `0 < 1 ≤ 2`) it has a non-integrable singularity at the interior point `1`, so it is neither
integrable there.  This is a statement about the *function* `h` on a compact, and has nothing to do
with any tail mass.

Consequence: a formalization which equated "logarithmically integrable" with the global clause
alone would be missing a hypothesis that the paper's use of `∫_{r₀}^{R}` needs.
-/
module

public import PercLib.CriticalLRP.Analysis.LogTailLocal.Core

/-!
# Non-redundance of the local clause

See the header comment above.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology Interval

namespace PercLib.CriticalLRP.Analysis.LogTailLocal

/-- The spike is measurable. -/
theorem measurable_invSpike : Measurable invSpike :=
  Measurable.ite measurableSet_Icc ((measurable_id.sub measurable_const).inv) measurable_const

/-- The logarithmically weighted spike vanishes on `Ioi 3`. -/
theorem invSpike_eq_zero_of_three_lt {r : ℝ} (hr : 3 < r) : invSpike r = 0 := by
  have : r ∉ Icc (1 : ℝ) 2 := by
    simp only [mem_Icc, not_and, not_le]
    intro _
    linarith
  simp [invSpike, this]

/-- **The spike satisfies the repository's global clause.**  Since it vanishes on `Ioi 3`, its
logarithmic density vanishes there. -/
theorem logarithmicallyIntegrable_invSpike : LogarithmicallyIntegrable invSpike := by
  refine ⟨measurable_invSpike, 3, by norm_num, ?_⟩
  refine IntegrableOn.congr_fun (s := Ioi (3 : ℝ)) (f := fun _ => (0 : ℝ)) integrableOn_zero
    (fun r hr => ?_) measurableSet_Ioi
  rw [invSpike_eq_zero_of_three_lt hr]
  simp

/-- `(x - 1)⁻¹` is not interval integrable across its singularity at `1`. -/
theorem not_intervalIntegrable_sub_inv_one :
    ¬ IntervalIntegrable (fun x : ℝ => (x - 1)⁻¹) volume 1 2 := by
  rw [intervalIntegrable_sub_inv_iff]
  simp

/-- The spike is not integrable on `[1, 2]`: it agrees there with `(x - 1)⁻¹`, which is not
interval integrable across the singularity at `1`. -/
theorem not_integrableOn_invSpike :
    ¬ IntegrableOn invSpike (Icc (1 : ℝ) 2) volume := by
  intro h
  apply not_intervalIntegrable_sub_inv_one
  rw [IntervalIntegrable]
  refine ⟨h.congr_fun (fun x hx => ?_) measurableSet_Icc |>.mono_set Ioc_subset_Icc_self,
    integrableOn_empty.mono_set (by simp)⟩
  simp only [invSpike, hx, ite_true]

/-- **The local clause is not a consequence of the global one.**  `invSpike` is logarithmically
integrable in the repository sense but is not integrable on the compact interval `[1, 2]` of
`(0, ∞)`. -/
theorem not_integrableOnPositiveCompacts_invSpike : ¬ IntegrableOnPositiveCompacts invSpike :=
  fun h => not_integrableOn_invSpike (h 1 2 one_pos (by norm_num))

/-- The spike is unbounded on `[1, 2]`: a bound together with measurability would make it integrable
there, contradicting `not_integrableOn_invSpike`. -/
theorem not_boundedOnPositiveCompacts_invSpike : ¬ BoundedOnPositiveCompacts invSpike := by
  intro h
  obtain ⟨C, hC⟩ := h 1 2 one_pos (by norm_num)
  refine not_integrableOn_invSpike (IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    measurable_invSpike.aestronglyMeasurable C ?_)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact hC r hr

/-- **The counterexample, in one statement.**  The global clause holds, the local clause fails, and
local boundedness fails too. -/
theorem invSpike_counterexample :
    LogarithmicallyIntegrable invSpike ∧ ¬ IntegrableOnPositiveCompacts invSpike ∧
      ¬ BoundedOnPositiveCompacts invSpike :=
  ⟨logarithmicallyIntegrable_invSpike, not_integrableOnPositiveCompacts_invSpike,
    not_boundedOnPositiveCompacts_invSpike⟩

end PercLib.CriticalLRP.Analysis.LogTailLocal
