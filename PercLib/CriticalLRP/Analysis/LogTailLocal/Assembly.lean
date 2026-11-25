/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwttizjk`, member `m4`, direction D8.

Assembly of the accepted global log-integrability results with the local clause, at the actual
source open-triangle tail.

The four clauses bundled by `nablaTail_sourceLog` below are what the paper uses when it writes
`∇_r` is logarithmically integrable and then integrates `∇_s ds/s` over `[r, R]`:

1. `∇_r → 0` and `∫_{r₀}^∞ ∇_r dr/r < ∞` (the accepted global clause, from the pointwise bound);
2. `r ↦ ∇_r` is finite and bounded on every `[R1, R2]` with `0 < R1 ≤ R2` (the local clause);
3. `r ↦ ∇_r` and `r ↦ ∇_r / r` are integrable on every such `[R1, R2]`;
4. `∫_{r₀}^{R} ∇_r dr/r` converges to `∫_{Ioi r₀} ∇_r dr/r` as `R → ∞`.

None of this is a statement about a tail mass, and none of it produces the pointwise bound: that
remains the convolution estimate (I.4.12) of Case 3 of `(HD)` (resp. (I.4.11) of Case 2), carried
as an explicit hypothesis in every theorem below.
-/
module

public import PercLib.CriticalLRP.Analysis.LogTailLocal.Source

/-!
# Assembly: source-style logarithmic integrability of `∇_r`

See the header comment above.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology Interval

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-! ### Case 3 of `(HD)`: the pointwise logarithmic bound -/

/-- **The local clause, from the pointwise logarithmic bound.**  This uses no rate at all beyond
finiteness at each positive radius; in particular `1 < p` is not needed. -/
theorem integrableOnPositiveCompacts_nablaTail_of_logRadialBound {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.LogTailLocal.IntegrableOnPositiveCompacts (fun r => (M.nablaTail r).toReal) :=
  integrableOnPositiveCompacts_nablaTail M
    (fun _ hr => nablaTail_ne_top_of_logRadialBound M hC hp hF hr)

/-- The local clause for the logarithmic density, from the pointwise logarithmic bound. -/
theorem logWeightedIntegrableOnPositiveCompacts_nablaTail_of_logRadialBound {C p : ℝ}
    (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.LogTailLocal.LogWeightedIntegrableOnPositiveCompacts
      (fun r => (M.nablaTail r).toReal) :=
  logWeightedIntegrableOnPositiveCompacts_nablaTail M
    (fun _ hr => nablaTail_ne_top_of_logRadialBound M hC hp hF hr)

/-- **Boundedness on compacts, quantitatively, from the pointwise bound.**  On `[R1, R2]` the real
tail is bounded by `C (log (1 + R1)) ^ (-p)`, the value of the majorant at the *left* endpoint. -/
theorem boundedOnPositiveCompacts_nablaTail_of_logRadialBound {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.LogTailLocal.BoundedOnPositiveCompacts (fun r => (M.nablaTail r).toReal) := by
  intro R1 R2 h1 _
  refine ⟨Analysis.logMajorant C p R1, fun r hr => ?_⟩
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (nablaTail_toReal_le_logMajorant M hC hp hF (lt_of_lt_of_le h1 hr.1)).trans
    (Analysis.logMajorant_le_logMajorant hC hp h1 hr.1)

/-- **The eventual bound needed by the ODE lemma.**  `RegularVariation.ode_log_identity` asks for a
constant `C` with `|h t| ≤ C` for all `t ≥ r₀`.  For `h = ∇` this is what the pointwise bound
supplies, with `C = C (log (1 + r₀)) ^ (-p)`.  No ODE is asserted here: this is only the shape of
the boundedness hypothesis, which the local clause by itself does *not* give. -/
theorem exists_bound_nablaTail_of_logRadialBound {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p)
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C' : ℝ, ∀ r : ℝ, r₀ ≤ r → |(M.nablaTail r).toReal| ≤ C' := by
  refine ⟨Analysis.logMajorant C p r₀, fun r hr => ?_⟩
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (nablaTail_toReal_le_logMajorant M hC hp hF (lt_of_lt_of_le hr₀ hr)).trans
    (Analysis.logMajorant_le_logMajorant hC hp hr₀ hr)

/-- **Source-style logarithmic integrability of `∇_r`.**  From the pointwise bound
`∇_{β_c}(0, y) ≤ C (log (1 + ‖y‖)) ^ (-p)` with `p > 1`, the tail is *both* globally
log-integrable with `∇_r → 0` and locally integrable on the compacta of `(0, ∞)`. -/
theorem sourceLogIntegrable_nablaTail {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.LogTailLocal.SourceLogIntegrable (fun r => (M.nablaTail r).toReal) :=
  ⟨(isLogErrorFunction_nablaTail M hC hp hF).1,
   integrableOnPositiveCompacts_nablaTail_of_logRadialBound M hC (by linarith) hF⟩

/-- **Source-style logarithmically integrable error function.** -/
theorem sourceLogErrorFunction_nablaTail {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.LogTailLocal.SourceLogErrorFunction (fun r => (M.nablaTail r).toReal) :=
  ⟨isLogErrorFunction_nablaTail M hC hp hF,
   integrableOnPositiveCompacts_nablaTail_of_logRadialBound M hC (by linarith) hF⟩

/-- **The improper logarithmic integral of the tail is a limit of interval integrals.**  Together
with `sourceLogErrorFunction_nablaTail` this is the faithful reading of the source's
`∫_{r₀}^∞ ∇_r dr / r < ∞`: every interval integral exists and the limit is finite. -/
theorem exists_tendsto_intervalIntegral_nablaTail_div {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Tendsto (fun R => ∫ r in r₀..R, (M.nablaTail r).toReal / r) atTop
        (𝓝 (∫ r in Ioi r₀, (M.nablaTail r).toReal / r)) := by
  obtain ⟨hm, r₀, hr₀, habs⟩ := (isLogErrorFunction_nablaTail M hC hp hF).1
  exact ⟨r₀, hr₀, Analysis.LogTailLocal.tendsto_intervalIntegral_div_id hm hr₀ habs⟩

/-- **The four clauses together, Case 3 of `(HD)`.**  This is the strongest source-style statement
available at the current HEAD: the global logarithmic integrability and `∇_r → 0` of the accepted
packet, the local clause, and the identification of the improper integral with a limit of interval
integrals.

The residual hypothesis is exactly `hF`: the pointwise bound on the uncut open triangle produced by
the logarithmic-correction convolution estimate (I.4.12) of Case 3 of `(HD)`.  It is not proved
anywhere at the current HEAD and is not assumed by this theorem. -/
theorem nablaTail_sourceLog {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) ∧
      Analysis.LogTailLocal.BoundedOnPositiveCompacts (fun r => (M.nablaTail r).toReal) ∧
      (∀ R1 R2 : ℝ, 0 < R1 → R1 ≤ R2 →
        IntegrableOn (fun r => (M.nablaTail r).toReal) (Icc R1 R2) volume) ∧
      (∀ R1 R2 : ℝ, 0 < R1 → R1 ≤ R2 →
        IntegrableOn (fun r => (M.nablaTail r).toReal / r) (Icc R1 R2) volume) ∧
      (∀ R1 R2 : ℝ, 0 < R1 → R1 ≤ R2 →
        IntervalIntegrable (fun r => (M.nablaTail r).toReal / r) volume R1 R2) ∧
      ∃ r₀ : ℝ, 0 < r₀ ∧
        Tendsto (fun R => ∫ r in r₀..R, (M.nablaTail r).toReal / r) atTop
          (𝓝 (∫ r in Ioi r₀, (M.nablaTail r).toReal / r)) := by
  refine ⟨isLogErrorFunction_nablaTail M hC hp hF,
    boundedOnPositiveCompacts_nablaTail M
      (fun _ hr => nablaTail_ne_top_of_logRadialBound M hC (by linarith) hF hr),
    ?_, ?_, ?_, exists_tendsto_intervalIntegral_nablaTail_div M hC hp hF⟩
  · intro R1 R2 h1 h2
    exact integrableOn_nablaTail_toReal M
      (nablaTail_ne_top_of_logRadialBound M hC (by linarith) hF h1)
  · intro R1 R2 h1 h2
    exact integrableOn_nablaTail_toReal_div M h1
      (nablaTail_ne_top_of_logRadialBound M hC (by linarith) hF h1)
  · intro R1 R2 h1 h2
    exact intervalIntegrable_nablaTail_div M h1 h2
      (nablaTail_ne_top_of_logRadialBound M hC (by linarith) hF h1)

/-! ### The faithful real-valued hypothesis

The `ℝ≥0∞`-valued `hF` above is stronger than what the source states: (I.4.13) bounds the real
value `∇_{β_c}(0, x)`.  The finiteness hypothesis `hfin` is not cosmetic — `ENNReal.toReal` sends
`⊤` to `0`, so a real-valued upper bound alone says nothing about an infinite value. -/

/-- **Real-valued form.**  Under the pointwise bound and finiteness of the uncut open triangle at
every nonzero point, all the clauses of `nablaTail_sourceLog` hold. -/
theorem nablaTail_sourceLog_of_toReal_le {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (h : ∀ y : M.V, y ≠ 0 →
      (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg
        M.betaCrit 0 y).toReal ≤ Analysis.logMajorant C p (M.S.dist 0 y))
    (hfin : ∀ y : M.V, y ≠ 0 →
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤) :
    Analysis.LogTailLocal.SourceLogErrorFunction (fun r => (M.nablaTail r).toReal) ∧
      ∃ r₀ : ℝ, 0 < r₀ ∧
        Tendsto (fun R => ∫ r in r₀..R, (M.nablaTail r).toReal / r) atTop
          (𝓝 (∫ r in Ioi r₀, (M.nablaTail r).toReal / r)) :=
  ⟨sourceLogErrorFunction_nablaTail M hC hp (logRadialBound_of_toReal_le M h hfin),
   exists_tendsto_intervalIntegral_nablaTail_div M hC hp (logRadialBound_of_toReal_le M h hfin)⟩

/-! ### Case 2 of `(HD)`: polynomial decay -/

/-- **The local clause from polynomial decay.**  As in the logarithmic case, no rate is needed for
the local clause; the polynomial decay is used only through finiteness of the tail. -/
theorem integrableOnPositiveCompacts_nablaTail_of_powRadialBound {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hF : Analysis.PowRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C a) :
    Analysis.LogTailLocal.SourceLogErrorFunction (fun r => (M.nablaTail r).toReal) :=
  ⟨Analysis.isLogErrorFunction_radialTailSup_pow hC ha hF,
   integrableOnPositiveCompacts_nablaTail M
     (fun _ hr => nablaTail_ne_top_of_powRadialBound M hC ha.le hF hr)⟩

/-- **Real-valued polynomial form (Case 2 of `(HD)`).** -/
theorem sourceLogErrorFunction_nablaTail_of_pow {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (h : ∀ y : M.V, y ≠ 0 →
      (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg
        M.betaCrit 0 y).toReal ≤ Analysis.powMajorant C a (M.S.dist 0 y))
    (hfin : ∀ y : M.V, y ≠ 0 →
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤) :
    Analysis.LogTailLocal.SourceLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  have hpow : Analysis.PowRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C a := by
    intro y hy
    have hy0 : y ≠ 0 := ne_zero_of_sdist_pos M hy
    change PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y
        ≤ ENNReal.ofReal (Analysis.powMajorant C a (M.S.dist 0 y))
    rw [← ENNReal.ofReal_toReal (hfin y hy0)]
    exact ENNReal.ofReal_le_ofReal (h y hy0)
  exact integrableOnPositiveCompacts_nablaTail_of_powRadialBound M hC ha hpow

end PercLib.CriticalLRP.Orchestration.SourceModelData
