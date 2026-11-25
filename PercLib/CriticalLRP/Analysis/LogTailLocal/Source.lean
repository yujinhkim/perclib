/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwttizjk`, member `m4`, direction D8.

The **local integrability clause of Lemma I.4.3** for the actual source open-triangle tail.

The accepted packet `PercLib/CriticalLRP/Analysis/OpenTriangleLogTail.lean` proves, from a
pointwise bound `∇_{β_c}(0, y) ≤ C (log (1 + ‖y‖)) ^ (-p)` with `p > 1` (or from the polynomial
bound of Case 2), that the source tail `r ↦ ∇_r` is **logarithmically integrable** in the
repository sense `∫_{r₀}^∞ ∇_r dr / r < ∞` and that `∇_r → 0`.

What that packet does *not* record is the paper's separate local clause: `∇_r` is a genuine
function of `r` near every finite radius, i.e. it is finite there and integrable on every
`[R1, R2]` with `0 < R1 ≤ R2`, so that `∫_{R1}^{R2}` and the improper integral `∫_{R1}^∞` are
limits of ordinary interval integrals.  This file supplies exactly that, and combines it with the
accepted global result.

The mechanism is short and uses no decay rate at all: `∇_r` is an `⨆` over `{y | r ≤ ‖y‖}`,
hence antitone in `r`; an antitone `ℝ≥0∞`-valued function is measurable; once it is finite at
`R1` (which a pointwise bound at any single positive radius gives) its `.toReal` is bounded by
`(∇_{R1}).toReal` on `[R1, R2]` and therefore integrable there.  **No logarithmic decay, no
`p > 1`, and in particular no tail-mass estimate enters the local clause.**

The remaining hypothesis of the source lemma I.4.3 stays exactly where the accepted packet left
it: the pointwise estimate on the uncut open triangle produced by the convolution estimate
(I.4.12) in Case 3 of `(HD)` (or (I.4.11) in Case 2).  It is carried as `hF`/`h`/`hfin` below and
is never assumed.
-/
module

public import PercLib.CriticalLRP.Analysis.LogTailLocal.Core
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail

/-!
# Local integrability of the source open-triangle tail

See the header comment above.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology Interval

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-! ### Shape of the actual tail -/

/-- **The source tail is antitone in the radius.**  `∇_r = sup_{‖y‖ ≥ r} ∇_{β_c}(0,y)` is a
supremum over a shrinking set, so this needs no hypothesis at all on `M` — in particular no
finiteness. -/
theorem antitone_nablaTail : Antitone M.nablaTail := by
  intro r r' hrr'
  rw [nablaTail_eq_radialTailSup M, nablaTail_eq_radialTailSup M]
  exact Analysis.antitone_radialTailSup _ _ hrr'

/-- The `ℝ≥0∞`-valued tail is measurable, being antitone. -/
theorem measurable_nablaTail : Measurable M.nablaTail :=
  (antitone_nablaTail M).measurable

/-- The real-valued tail `r ↦ ∇_r` is measurable, being `toReal` of an antitone function. -/
theorem measurable_nablaTail_toReal : Measurable (fun r => (M.nablaTail r).toReal) :=
  ENNReal.measurable_toReal.comp (measurable_nablaTail M)

/-! ### Finiteness at one radius

`ENNReal.toReal` sends `⊤` to `0`, so antitonicity of the real-valued tail is only available once
the values are known to be finite.  Finiteness at a single positive radius is enough, and a
pointwise bound at that radius is enough for finiteness. -/

/-- **Finiteness propagates rightwards.**  If the tail is finite at `R1` then its real value is at
most the real value at `R1` on `[R1, ∞)`. -/
theorem nablaTail_toReal_le {R1 r : ℝ} (hfin : M.nablaTail R1 ≠ ⊤) (hr : R1 ≤ r) :
    (M.nablaTail r).toReal ≤ (M.nablaTail R1).toReal :=
  Analysis.LogTailLocal.toReal_le_toReal_of_antitone (antitone_nablaTail M) hfin hr

/-- A pointwise logarithmic bound on the uncut open triangle makes the tail finite at every
positive radius. -/
theorem nablaTail_ne_top_of_logRadialBound {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p)
    {r : ℝ} (hr : 0 < r) : M.nablaTail r ≠ ⊤ := by
  rw [nablaTail_eq_radialTailSup M]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (Analysis.radialTailSup_le_logMajorant hC hp hr hF)

/-- The same, with the explicit real bound `(∇_r).toReal ≤ C (log (1 + r)) ^ (-p)`. -/
theorem nablaTail_toReal_le_logMajorant {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p)
    {r : ℝ} (hr : 0 < r) : (M.nablaTail r).toReal ≤ Analysis.logMajorant C p r := by
  rw [nablaTail_eq_radialTailSup M]
  exact Analysis.radialTailSup_toReal_le hC hp hr hF

/-- The polynomial (Case 2) analogue of `nablaTail_ne_top_of_logRadialBound`. -/
theorem nablaTail_ne_top_of_powRadialBound {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hF : Analysis.PowRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C a)
    {r : ℝ} (hr : 0 < r) : M.nablaTail r ≠ ⊤ := by
  rw [nablaTail_eq_radialTailSup M]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (Analysis.radialTailSup_le_powMajorant hC ha hr hF)

/-! ### Local integrability on `[R1, R2]`

Everything below is a compact-interval statement about the function `r ↦ ∇_r`.  It is not a
statement about the tail mass and carries no information at `∞`. -/

/-- **The local clause, from finiteness at the left endpoint.**  If the tail is finite at `R1`
then the real tail `r ↦ ∇_r` is integrable on `[R1, R2]` for every `R2`, hence in particular on
every `[R1, R2]` with `0 < R1 ≤ R2`, the range of the source's clause.  Positivity of `R1` and the
order of the endpoints are both unnecessary here; finiteness at `R1` is the whole hypothesis. -/
theorem integrableOn_nablaTail_toReal {R1 R2 : ℝ} (hfin : M.nablaTail R1 ≠ ⊤) :
    IntegrableOn (fun r => (M.nablaTail r).toReal) (Icc R1 R2) volume :=
  Analysis.LogTailLocal.integrableOn_Icc_toReal_of_antitone (antitone_nablaTail M) hfin R2

/-- Integrability of the logarithmic density `r ↦ ∇_r / r` on `[R1, R2]` for `0 < R1`, from
finiteness at `R1`.  Here the positivity of `R1` is used: it is what makes `1/r` bounded, and it is
the only reason the source restricts to compacta of `(0, ∞)`. -/
theorem integrableOn_nablaTail_toReal_div {R1 R2 : ℝ} (hR1 : 0 < R1)
    (hfin : M.nablaTail R1 ≠ ⊤) :
    IntegrableOn (fun r => (M.nablaTail r).toReal / r) (Icc R1 R2) volume :=
  Analysis.LogTailLocal.integrableOn_Icc_toReal_div_of_antitone (antitone_nablaTail M) hR1 hfin R2

/-- **The local clause, from a bound on the interval only.**  This is strictly weaker than
finiteness at `R1`: a real-valued bound on `[R1, R2]` suffices, since measurability is automatic.
No hypothesis at all on the relative position of `R1` and `R2` is needed. -/
theorem integrableOn_nablaTail_toReal_of_le {R1 R2 C : ℝ}
    (hb : ∀ r ∈ Icc R1 R2, (M.nablaTail r).toReal ≤ C) :
    IntegrableOn (fun r => (M.nablaTail r).toReal) (Icc R1 R2) volume :=
  IntegrableOn.of_bound isCompact_Icc.measure_lt_top
    (measurable_nablaTail_toReal M).aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact hb r hr)

/-- The `∀`-form: finiteness of the tail at every positive radius gives the local clause. -/
theorem integrableOnPositiveCompacts_nablaTail
    (hfin : ∀ r : ℝ, 0 < r → M.nablaTail r ≠ ⊤) :
    Analysis.LogTailLocal.IntegrableOnPositiveCompacts (fun r => (M.nablaTail r).toReal) :=
  Analysis.LogTailLocal.integrableOnPositiveCompacts_toReal_of_antitone (antitone_nablaTail M) hfin

/-- The real tail is bounded on every compact subinterval of `(0, ∞)`, by its value at the left
endpoint. -/
theorem boundedOnPositiveCompacts_nablaTail
    (hfin : ∀ r : ℝ, 0 < r → M.nablaTail r ≠ ⊤) :
    Analysis.LogTailLocal.BoundedOnPositiveCompacts (fun r => (M.nablaTail r).toReal) :=
  Analysis.LogTailLocal.boundedOnPositiveCompacts_toReal_of_antitone (antitone_nablaTail M) hfin

/-- The local clause for the logarithmic density `r ↦ ∇_r / r`. -/
theorem logWeightedIntegrableOnPositiveCompacts_nablaTail
    (hfin : ∀ r : ℝ, 0 < r → M.nablaTail r ≠ ⊤) :
    Analysis.LogTailLocal.LogWeightedIntegrableOnPositiveCompacts
      (fun r => (M.nablaTail r).toReal) :=
  Analysis.LogTailLocal.logWeightedIntegrableOnPositiveCompacts_toReal_of_antitone
    (antitone_nablaTail M) hfin

/-- **Interval-integrability form.**  For `R1 ≤ R2` the real tail is interval integrable on
`R1..R2`. -/
theorem intervalIntegrable_nablaTail {R1 R2 : ℝ} (hR2 : R1 ≤ R2)
    (hfin : M.nablaTail R1 ≠ ⊤) :
    IntervalIntegrable (fun r => (M.nablaTail r).toReal) volume R1 R2 :=
  PercLib.CriticalLRP.Analysis.intervalIntegrable_of_integrableOn_uIcc
    (by
      rw [uIcc_of_le hR2]
      exact integrableOn_nablaTail_toReal M hfin)

/-- Interval integrability of the logarithmic density on `R1..R2` for `0 < R1 ≤ R2`. -/
theorem intervalIntegrable_nablaTail_div {R1 R2 : ℝ} (hR1 : 0 < R1) (hR2 : R1 ≤ R2)
    (hfin : M.nablaTail R1 ≠ ⊤) :
    IntervalIntegrable (fun r => (M.nablaTail r).toReal / r) volume R1 R2 :=
  PercLib.CriticalLRP.Analysis.intervalIntegrable_of_integrableOn_uIcc
    (by
      rw [uIcc_of_le hR2]
      exact integrableOn_nablaTail_toReal_div M hR1 hfin)

/-- **The quantitative local logarithmic-integral bound.**  For `0 < R1 ≤ R2` and `∇_{R1} ≠ ⊤`,

`∫_{R1}^{R2} ∇_r dr / r ≤ ∇_{R1} · log (R2 / R1)`.

This is where antitonicity pays off quantitatively: the local logarithmic integral is controlled by
the value of the tail at the *left* endpoint, with the exact factor `log (R2/R1)`.  It is a
finite-radius statement and says nothing about the tail at `∞`. -/
theorem intervalIntegral_nablaTail_div_le {R1 R2 : ℝ} (hR1 : 0 < R1) (hR2 : R1 ≤ R2)
    (hfin : M.nablaTail R1 ≠ ⊤) :
    ∫ r in R1..R2, (M.nablaTail r).toReal / r ≤
      (M.nablaTail R1).toReal * Real.log (R2 / R1) := by
  have hmem : (0 : ℝ) ∉ uIcc R1 R2 := by
    rw [uIcc_of_le hR2]
    exact fun h => absurd h.1 (not_le.mpr hR1)
  have hg : IntervalIntegrable (fun r : ℝ => (M.nablaTail R1).toReal * r⁻¹) volume R1 R2 :=
    (continuousOn_id.inv₀ (fun r hr => by
      rw [uIcc_of_le hR2] at hr
      exact ne_of_gt (lt_of_lt_of_le hR1 hr.1))).intervalIntegrable.const_mul _
  have hle := intervalIntegral.integral_mono_on hR2
    (intervalIntegrable_nablaTail_div M hR1 hR2 hfin) hg (fun r hr => by
      have hr0 : 0 < r := lt_of_lt_of_le hR1 hr.1
      exact mul_le_mul_of_nonneg_right (nablaTail_toReal_le M hfin hr.1) (inv_nonneg.mpr hr0.le))
  calc ∫ r in R1..R2, (M.nablaTail r).toReal / r
      ≤ ∫ r in R1..R2, (M.nablaTail R1).toReal * r⁻¹ := hle
    _ = (M.nablaTail R1).toReal * Real.log (R2 / R1) := by
        rw [intervalIntegral.integral_const_mul, integral_inv hmem]

/-- **The local clause in the exact shape of the source's clause.**  For `0 < R1 ≤ R2` and
`∇_{R1} ≠ ⊤`, both the tail `r ↦ ∇_r` and its logarithmic density `r ↦ ∇_r / r` are integrable on
`[R1, R2]`.  (The two halves also hold with weaker hypotheses — see
`integrableOn_nablaTail_toReal` and `integrableOn_nablaTail_toReal_div`; they are collected here
because this is the pair of statements the paper's notation `∫_{R1}^{R2} ∇_r dr / r` needs.) -/
theorem integrableOn_nablaTail_Icc {R1 R2 : ℝ} (hR1 : 0 < R1) (hR2 : R1 ≤ R2)
    (hfin : M.nablaTail R1 ≠ ⊤) :
    IntegrableOn (fun r => (M.nablaTail r).toReal) (Icc R1 R2) volume ∧
      IntegrableOn (fun r => (M.nablaTail r).toReal / r) (Icc R1 R2) volume ∧
      IntervalIntegrable (fun r => (M.nablaTail r).toReal / r) volume R1 R2 :=
  ⟨integrableOn_nablaTail_toReal M hfin,
   integrableOn_nablaTail_toReal_div M hR1 hfin,
   intervalIntegrable_nablaTail_div M hR1 hR2 hfin⟩


end PercLib.CriticalLRP.Orchestration.SourceModelData
