/-
Integrated from the independently rebuilt and accepted
`.ultramath/smwyop3kc/m1/Main.lean` at production base
`e8c25f3936540fbe66322454ff596091b18b7436`.

# Radius measurability of the cutoff cluster statistics

Swarm `smwyop3kc`, member `m1`.  Self-contained packet: no production writes, no `sorry`/`admit`,
no `native_decide`, no new axiom, no new mathematical premise.

# The gap this file closes

At HEAD the only regularity in the cut-off radius recorded for the phase-1 cutoff statistics was
*monotonicity*: `E1Sign.pairMass_mono`, `E1Sign.connMass_mono`
(`Analysis/Cutoff/CutoffMomentContinuity.lean`) and `SourceModelData.cutMassAt_mono`
(`Analysis/Cutoff/Continuity.lean`), all with hypothesis `0 < r` and therefore saying nothing about
the radius interval `r ≤ 0`.  Consequently several `Measurable` facts were carried as explicit
hypotheses in the Case-3 scope chain and in the I.4.13 log-integrability chain:

* `CutoffDefect.measurable_cutE1_of_measurable_stats` (three statistic hypotheses),
* `CutoffDefect.aemeasurable_cutE1_of_aemeasurable_stats` (`hfin` plus two hypotheses),
* `I420Case3.measurable_cutError_of_stats`,
* `I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux` (`hmeas`),
* `CutoffDefect.integrableOn_cutE1_abs_div`, `logarithmicallyIntegrable_cutE1`,
  `isLogErrorFunction_cutE1` (`hmeas`).

All of them are discharged here, unconditionally.

# The two ingredients

* `MeasureTheory.aemeasurable_toReal_of_monotoneOn_Ioi` — for any `f : ℝ → ℝ≥0∞` monotone on a
  radius tail `(a, ∞)`, the real shadow `r ↦ (f r).toReal` is a.e. measurable there, **with no
  finiteness hypothesis**.  This is the point where a naive monotonicity argument fails:
  `ENNReal.toReal ⊤ = 0`, so `toReal ∘ f` is *not* monotone.  The proof avoids `toReal`
  monotonicity entirely.  It compares `f` with the globally measurable proxy
  `r ↦ f (a + exp (log (r - a)))`, monotone because `exp` is, and evaluates it at the substituted
  radius using the *identity* `a + exp (log (r - a)) = r` for `r > a`.  Because that is an
  identity and not an inequality, the value `⊤` is transported exactly and `toReal` is applied to
  the same extended nonnegative real on both sides.
* `MeasureTheory.measurable_of_measurable_inter_Ioi` — a real function whose Borel preimages meet
  `(c, ∞)` measurably and which agrees with a measurable function on `(-∞, c)` is measurable.  This
  is the "restrict to the monotone domain, then patch outside" step.  It is needed because the
  statistics are only known to be monotone on the positive half-line.

# Results

Generic: `measurable_toReal_exp_log`, `aemeasurable_toReal_of_monotoneOn_Ioi`,
`measurable_of_measurable_inter_Ioi`.

Statistics:
* `SourceModelData.ball_eq_empty_of_neg`, `ballF_empty_of_neg` — below radius `0` the lattice ball
  and the truncated window are empty, from nonnegativity of the source norm
  (`BallAverage.rho_nonneg`).
* `E1Sign.pairMass_eq_zero_of_neg`, `E1Sign.connMass_eq_zero_of_neg` — both statistics vanish for
  `r < 0`.
* `E1Sign.aemeasurable_pairMassReal`, `aemeasurable_connMassReal`,
  `SourceModelData.aemeasurable_cutMassAtReal` — **unconditional** `AEMeasurable` on
  `volume.restrict (Ioi 1)`.
* `E1Sign.measurable_pairMassReal`, `measurable_connMassReal` — **unconditional global
  `Measurable` on all of `ℝ`.**
* `E1Sign.aemeasurable_cutE1` — unconditional `AEMeasurable (fun r => cutE1 M r)` on `Ioi 1`
  (the `CutoffDefect` defect), with no `hfin`, `hpair` or `hconn`.

Defect and its consequences:
* `E1Sign.cutE1_eq_zero_of_neg` — for `r < 0` the ball count is `0`, so
  `cE1 A S T b = (b A² - S + T)/(b A²)` is `_ / 0 = 0`; the truncated-law defect vanishes.
* `E1Sign.cutError_eq_cutE0_of_neg` — hence below `0` the composite error collapses to the
  standardized defect `PivotFlux.cutE0 M`, which production proves globally measurable
  (`I420Case3.measurable_cutE0`).  The cutoff mass at `r ≤ 0` is *never analysed*; it does not
  need to be.
* `E1Sign.cutError_eq_exp_log`, `E1Sign.measurable_cutE1_exp_log` — the mixed proxy on `(0, ∞)`.
* `E1Sign.measurable_cutError`, `I420Case3.measurable_cutError` — **unconditional global
  `Measurable (I420Case3.cutError M)`**.
* `I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux_unconditional` — the shipped
  Case-3 wrapper with `hmeas` deleted.  Every other input (`hHD3`, `hTri`, `hc`, `hαd`, `hlow`,
  `hβ`, `hr₀`, `h2`, `hderiv`, `hflux`, `h0`, `𝓔`, `h𝓔mono`, `h𝓔`, `p`, `hp`, `hθ0`, `hθ1`,
  `hMa`, `hc3`, `hgm`) is passed through unchanged and none of them is derived here.
* `CutoffDefect.measurable_cutE1` — **unconditional global `Measurable` of the actual truncated-law
  defect `𝓔_{1,r}`**; `CutoffDefect.cutE1_eq_pivot`, `CutoffDefect.cutE1_eq_zero_of_neg`.
* `CutoffDefect.integrableOn_cutE1_abs_div_unconditional`,
  `logarithmicallyIntegrable_cutE1_unconditional`, `isLogErrorFunction_cutE1_unconditional` — the
  I.4.13 chain with its measurability input supplied.  `hT`, `h1` (finite first cutoff moment on a
  tail), `hC`, `hp`, `hF` (the pointwise `(HD)` bound `LogRadialBound`) and, for the last,
  `hTri` remain explicit: none is inferred from criticality, `θ = 0`, finite boxes or `β = β_c`.

# What is deliberately not claimed

* No continuity, and no `MonotoneOn` of any real shadow: the `⊤` values genuinely break it, and no
  `toReal`-monotonicity statement is used anywhere.
* No value of `pairMass`, `connMass` or `cutMassAt` at `r = 0` or below is identified with a source
  quantity.  Global `Measurable` of `r ↦ (M.cutMassAt r 0).toReal` is **not** claimed: nothing here
  determines the cutoff mass below `0`, and the argument for the defect is arranged so that it
  never needs to.
* No finiteness of any cutoff moment is assumed or derived; no `hTri` from `(HD)(3)`; no local
  boundedness of the defect; no I.4.20 claim.
-/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.LogIntegrable
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Measurability

/-! ## Generic radius-measurability lemmas -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace MeasureTheory

/-- The globally measurable proxy for the `toReal` shadow of a function monotone on `Ioi a`. -/
theorem measurable_toReal_exp_log {f : ℝ → ℝ≥0∞} {a : ℝ} (h : MonotoneOn f (Ioi a)) :
    Measurable fun r : ℝ => (f (a + Real.exp (Real.log (r - a)))).toReal := by
  have hmono : Monotone fun t : ℝ => f (a + Real.exp t) := by
    intro t t' htt'
    refine h ?_ ?_ ?_
    · simp only [mem_Ioi]; linarith [Real.exp_pos t]
    · simp only [mem_Ioi]; linarith [Real.exp_pos t']
    · linarith [Real.exp_le_exp.mpr htt']
  exact (ENNReal.measurable_toReal.comp hmono.measurable).comp
    (Real.measurable_log.comp (measurable_id.sub measurable_const))

/-- A function monotone on a radius tail has an a.e. measurable real-valued `toReal` shadow. -/
theorem aemeasurable_toReal_of_monotoneOn_Ioi {f : ℝ → ℝ≥0∞} {a : ℝ}
    (h : MonotoneOn f (Ioi a)) :
    AEMeasurable (fun r : ℝ => (f r).toReal) (volume.restrict (Ioi a)) := by
  refine AEMeasurable.congr (measurable_toReal_exp_log h).aemeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
  intro r hr
  have hpos : 0 < r - a := by have := mem_Ioi.mp hr; linarith
  have heq : a + Real.exp (Real.log (r - a)) = r := by rw [Real.exp_log hpos]; ring
  simp only [heq]

/-- A real function whose Borel preimages meet `(c, ∞)` measurably and which agrees with a
measurable function on `(-∞, c)` is measurable. -/
theorem measurable_of_measurable_inter_Ioi {g g' : ℝ → ℝ} {c : ℝ}
    (hIoi : ∀ s : Set ℝ, MeasurableSet s → MeasurableSet (g ⁻¹' s ∩ Ioi c))
    (hbelow : EqOn g g' (Iio c)) (hg' : Measurable g') : Measurable g := by
  intro s hs
  have h1 : MeasurableSet (g ⁻¹' s ∩ Ioi c) := hIoi s hs
  have hlt : MeasurableSet (g ⁻¹' s ∩ Iio c) := by
    have heq : g ⁻¹' s ∩ Iio c = g' ⁻¹' s ∩ Iio c := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Iio]
      exact ⟨fun h => ⟨by rw [← hbelow h.2]; exact h.1, h.2⟩,
        fun h => ⟨by rw [hbelow h.2]; exact h.1, h.2⟩⟩
    rw [heq]
    exact (hg' hs).inter measurableSet_Iio
  have hpt : MeasurableSet (g ⁻¹' s ∩ {c}) := by
    rcases em (g c ∈ s) with hc | hc
    · have heq : g ⁻¹' s ∩ {c} = {c} := by
        ext r
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hc, h⟩⟩
      rw [heq]
      exact measurableSet_singleton c
    · have heq : g ⁻¹' s ∩ {c} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun r hr => ?_
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hr
        exact hc (by rw [← hr.2]; exact hr.1)
      rw [heq]
      exact MeasurableSet.empty
  have hIic : MeasurableSet (g ⁻¹' s ∩ Iic c) := by
    have hsplit : Iic c = Iio c ∪ ({c} : Set ℝ) := by
      ext r
      simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
      exact ⟨fun h => (lt_or_eq_of_le h).elim Or.inl Or.inr,
        fun h => h.elim (fun h' => h'.le) (fun h' => h'.le)⟩
    have hun : g ⁻¹' s ∩ Iic c = (g ⁻¹' s ∩ Iio c) ∪ (g ⁻¹' s ∩ {c}) := by
      rw [hsplit, Set.inter_union_distrib_left]
    rw [hun]
    exact hlt.union hpt
  have hun : g ⁻¹' s = (g ⁻¹' s ∩ Ioi c) ∪ (g ⁻¹' s ∩ Iic c) := by
    ext r
    simp only [mem_inter_iff, mem_union, mem_Ioi, mem_Iic]
    constructor
    · intro h
      by_cases hc : c < r
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, le_of_not_gt hc⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  rw [hun]
  exact h1.union hIic

end MeasureTheory

/-! ## The radius tails of the three cutoff statistics -/

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The lattice ball is empty below radius `0`: the source norm is nonnegative. -/
theorem ball_eq_empty_of_neg {r : ℝ} (hr : r < 0) : M.ball r = ∅ := by
  ext y
  simp only [ball, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
  exact lt_of_lt_of_le hr (BallAverage.rho_nonneg M.S y)

/-- Below radius `0` the truncated window is empty. -/
theorem ballF_empty_of_neg {r : ℝ} (hr : r < 0) : E1Sign.ballF M r = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  rw [E1Sign.mem_ballF, M.ball_eq_empty_of_neg hr] at hy
  exact hy

/-- The cutoff mass is monotone in the radius on the whole positive half-line. -/
theorem monotoneOn_cutMassAt : MonotoneOn (fun r : ℝ => M.cutMassAt r 0) (Ioi 0) :=
  fun _ hr _ hr' hrr' => M.cutMassAt_mono (by simpa using hr) (by simpa using hr') hrr'

/-- Unconditional a.e. measurability in the radius of the real cutoff mass on `(1, ∞)`. -/
theorem aemeasurable_cutMassAtReal :
    AEMeasurable (fun r : ℝ => (M.cutMassAt r 0).toReal) (volume.restrict (Ioi 1)) := by
  refine aemeasurable_toReal_of_monotoneOn_Ioi (a := 1) ?_
  intro r hr r' hr' hrr'
  refine M.monotoneOn_cutMassAt (b := r') ?_ ?_ hrr'
  · simp only [mem_Ioi]; have := mem_Ioi.mp hr; linarith
  · simp only [mem_Ioi]; have := mem_Ioi.mp hr'; linarith

end SourceModelData

end Orchestration

namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- The pair mass is monotone in the radius on the whole positive half-line. -/
theorem monotoneOn_pairMass : MonotoneOn (pairMass M) (Ioi 0) :=
  fun _ hr _ _ hrr' => pairMass_mono M (by simpa using hr) hrr'

/-- The connected mass is monotone in the radius on the whole positive half-line. -/
theorem monotoneOn_connMass : MonotoneOn (connMass M) (Ioi 0) :=
  fun _ hr _ _ hrr' => connMass_mono M (by simpa using hr) hrr'

/-- Below radius `0` the pair mass vanishes: the window is empty. -/
theorem pairMass_eq_zero_of_neg {r : ℝ} (hr : r < 0) : pairMass M r = 0 := by
  unfold pairMass
  rw [M.ballF_empty_of_neg hr]
  simp

/-- Below radius `0` the connected mass vanishes: the window is empty. -/
theorem connMass_eq_zero_of_neg {r : ℝ} (hr : r < 0) : connMass M r = 0 := by
  unfold connMass
  rw [M.ballF_empty_of_neg hr]
  simp

/-- **Unconditional a.e. measurability of the real pair mass on `(1, ∞)`.** -/
theorem aemeasurable_pairMassReal :
    AEMeasurable (fun r : ℝ => (pairMass M r).toReal) (volume.restrict (Ioi 1)) := by
  refine aemeasurable_toReal_of_monotoneOn_Ioi (a := 1) ?_
  intro r hr r' hr' hrr'
  refine monotoneOn_pairMass M (b := r') ?_ ?_ hrr'
  · simp only [mem_Ioi]; have := mem_Ioi.mp hr; linarith
  · simp only [mem_Ioi]; have := mem_Ioi.mp hr'; linarith

/-- **Unconditional a.e. measurability of the real connected mass on `(1, ∞)`.** -/
theorem aemeasurable_connMassReal :
    AEMeasurable (fun r : ℝ => (connMass M r).toReal) (volume.restrict (Ioi 1)) := by
  refine aemeasurable_toReal_of_monotoneOn_Ioi (a := 1) ?_
  intro r hr r' hr' hrr'
  refine monotoneOn_connMass M (b := r') ?_ ?_ hrr'
  · simp only [mem_Ioi]; have := mem_Ioi.mp hr; linarith
  · simp only [mem_Ioi]; have := mem_Ioi.mp hr'; linarith

/-- The real pair mass is measurable on all of `ℝ`: it vanishes below `0`. -/
theorem measurable_pairMassReal : Measurable fun r : ℝ => (pairMass M r).toReal := by
  refine measurable_of_measurable_inter_Ioi (c := 0) (g' := fun _ => (0 : ℝ)) ?_ ?_
    measurable_const
  · intro s hs
    have hPm : Measurable fun r : ℝ => (pairMass M (Real.exp (Real.log r))).toReal := by
      have hmono : Monotone fun t : ℝ => pairMass M (Real.exp t) :=
        fun t t' htt' => pairMass_mono M (Real.exp_pos t) (Real.exp_le_exp.mpr htt')
      exact (ENNReal.measurable_toReal.comp hmono.measurable).comp Real.measurable_log
    have heq : (fun r : ℝ => (pairMass M r).toReal) ⁻¹' s ∩ Ioi 0
        = (fun r : ℝ => (pairMass M (Real.exp (Real.log r))).toReal) ⁻¹' s
          ∩ Ioi 0 := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [Real.exp_log h2]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rwa [Real.exp_log h2] at h1
    rw [heq]
    exact (hPm hs).inter measurableSet_Ioi
  · intro r hr
    simp only [mem_Iio] at hr
    simp [pairMass_eq_zero_of_neg M hr]

/-- The real connected mass is measurable on all of `ℝ`: it vanishes below `0`. -/
theorem measurable_connMassReal : Measurable fun r : ℝ => (connMass M r).toReal := by
  refine measurable_of_measurable_inter_Ioi (c := 0) (g' := fun _ => (0 : ℝ)) ?_ ?_
    measurable_const
  · intro s hs
    have hPm : Measurable fun r : ℝ => (connMass M (Real.exp (Real.log r))).toReal := by
      have hmono : Monotone fun t : ℝ => connMass M (Real.exp t) :=
        fun t t' htt' => connMass_mono M (Real.exp_pos t) (Real.exp_le_exp.mpr htt')
      exact (ENNReal.measurable_toReal.comp hmono.measurable).comp Real.measurable_log
    have heq : (fun r : ℝ => (connMass M r).toReal) ⁻¹' s ∩ Ioi 0
        = (fun r : ℝ => (connMass M (Real.exp (Real.log r))).toReal) ⁻¹' s
          ∩ Ioi 0 := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [Real.exp_log h2]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rwa [Real.exp_log h2] at h1
    rw [heq]
    exact (hPm hs).inter measurableSet_Ioi
  · intro r hr
    simp only [mem_Iio] at hr
    simp [connMass_eq_zero_of_neg M hr]

/-- **Unconditional a.e. measurability of the truncated-law defect on `(1, ∞)`.** -/
theorem aemeasurable_cutE1 :
    AEMeasurable (fun r : ℝ => CutoffDefect.cutE1 M r) (volume.restrict (Ioi 1)) := by
  have hmass : AEMeasurable (fun r : ℝ => (M.cutMassAt r 0).toReal)
      (volume.restrict (Ioi 1)) := M.aemeasurable_cutMassAtReal
  have hpair : AEMeasurable (fun r : ℝ => (pairMass M r).toReal)
      (volume.restrict (Ioi 1)) := aemeasurable_pairMassReal M
  have hconn : AEMeasurable (fun r : ℝ => (connMass M r).toReal)
      (volume.restrict (Ioi 1)) := aemeasurable_connMassReal M
  have hA2 : AEMeasurable (fun r : ℝ => (M.cutMassAt r 0).toReal ^ 2)
      (volume.restrict (Ioi 1)) := by
    have h := hmass.mul hmass
    refine h.congr ?_
    filter_upwards with r
    simp [pow_two]
  have hden : AEMeasurable (fun r : ℝ =>
      ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2)
      (volume.restrict (Ioi 1)) := (CutoffDefect.measurable_ball_ncard M).aemeasurable.mul hA2
  have hnum : AEMeasurable (fun r : ℝ =>
      ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2
        - (pairMass M r).toReal + (connMass M r).toReal) (volume.restrict (Ioi 1)) :=
    (hden.sub hpair).add hconn
  unfold CutoffDefect.cutE1 PercLib.CriticalLRP.VolumeMoments.cE1
  exact hnum.div hden

end E1Sign

end PercLib.CriticalLRP

/-! ## Global measurability of the Case-3 cutoff defect `cutError` -/

namespace PercLib.CriticalLRP

namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- The cutoff defect `cutE1` of the truncated law vanishes below radius `0`: the ball count is
`0`, so `cE1 A S T b = (b A² - S + T)/(b A²)` is `_ / 0 = 0`. -/
theorem cutE1_eq_zero_of_neg {r : ℝ} (hr : r < 0) : PivotFlux.cutE1 M r = 0 := by
  have hb : ((M.ball r).ncard : ℝ) = 0 := by
    rw [SourceModelData.ball_eq_empty_of_neg M hr]
    simp
  unfold PivotFlux.cutE1 PercLib.CriticalLRP.VolumeMoments.cE1
  simp [hb]

/-- Below radius `0` the composite error collapses to the standardized defect, which is
measurable for free. -/
theorem cutError_eq_cutE0_of_neg {r : ℝ} (hr : r < 0) :
    I420Case3.cutError M r = PivotFlux.cutE0 M r := by
  unfold I420Case3.cutError
  rw [cutE1_eq_zero_of_neg M hr]
  ring

/-- On the positive half-line the error is the mixed expression in which the radius argument of
the truncated-law defect has been replaced by the proxy `exp (log r)`. -/
theorem cutError_eq_exp_log {r : ℝ} (hr : 0 < r) :
    I420Case3.cutError M r
      = 1 - (1 - PivotFlux.cutE0 M r) *
        (1 - PivotFlux.cutE1 M (Real.exp (Real.log r))) := by
  rw [Real.exp_log hr]
  rfl

/-- The mixed proxy is measurable: the standardized defect is measurable globally
(`I420Case3.measurable_cutE0`), and the truncated-law defect at `exp (log r)` is a rational
function of the three radius statistics, each of which is a monotone `ℝ≥0∞`-valued function of
`exp (log r)` composed with `toReal` and `log`. -/
theorem measurable_cutE1_exp_log :
    Measurable fun r : ℝ => PivotFlux.cutE1 M (Real.exp (Real.log r)) := by
  have hA : Measurable fun r : ℝ => (M.cutMassAt (Real.exp (Real.log r)) 0).toReal := by
    have hmono : Monotone fun t : ℝ => M.cutMassAt (Real.exp t) 0 :=
      fun t t' htt' =>
        M.cutMassAt_mono (Real.exp_pos t) (Real.exp_pos t') (Real.exp_le_exp.mpr htt')
    exact (ENNReal.measurable_toReal.comp hmono.measurable).comp Real.measurable_log
  have hS : Measurable fun r : ℝ => (pairMass M (Real.exp (Real.log r))).toReal := by
    have hmono : Monotone fun t : ℝ => pairMass M (Real.exp t) :=
      fun t t' htt' => pairMass_mono M (Real.exp_pos t) (Real.exp_le_exp.mpr htt')
    exact (ENNReal.measurable_toReal.comp hmono.measurable).comp Real.measurable_log
  have hT : Measurable fun r : ℝ => (connMass M (Real.exp (Real.log r))).toReal := by
    have hmono : Monotone fun t : ℝ => connMass M (Real.exp t) :=
      fun t t' htt' => connMass_mono M (Real.exp_pos t) (Real.exp_le_exp.mpr htt')
    exact (ENNReal.measurable_toReal.comp hmono.measurable).comp Real.measurable_log
  have hb : Measurable fun r : ℝ => ((M.ball (Real.exp (Real.log r))).ncard : ℝ) :=
    (CutoffDefect.measurable_ball_ncard M).comp (Real.measurable_exp.comp Real.measurable_log)
  unfold PivotFlux.cutE1 PercLib.CriticalLRP.VolumeMoments.cE1
  measurability

/-- **The Case-3 cutoff defect is a measurable function of the radius on all of `ℝ`, with no
finiteness, positivity or no-sphere hypothesis.**  Below `0` it agrees with the globally
measurable `PivotFlux.cutE0`; above `0` with the measurable mixed proxy. -/
theorem measurable_cutError : Measurable (I420Case3.cutError M) := by
  refine measurable_of_measurable_inter_Ioi (c := 0) (g' := PivotFlux.cutE0 M) ?_ ?_
    (I420Case3.measurable_cutE0 M)
  · intro s hs
    have hE0 : Measurable fun r : ℝ => PivotFlux.cutE0 M r := I420Case3.measurable_cutE0 M
    have hE1 : Measurable fun r : ℝ => PivotFlux.cutE1 M (Real.exp (Real.log r)) :=
      measurable_cutE1_exp_log M
    have hProx : Measurable fun r : ℝ =>
        1 - (1 - PivotFlux.cutE0 M r) *
          (1 - PivotFlux.cutE1 M (Real.exp (Real.log r))) := by
      measurability
    have heq : (fun r : ℝ => I420Case3.cutError M r) ⁻¹' s ∩ Ioi 0
        = (fun r : ℝ =>
            1 - (1 - PivotFlux.cutE0 M r) *
              (1 - PivotFlux.cutE1 M (Real.exp (Real.log r)))) ⁻¹' s ∩ Ioi 0 := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← cutError_eq_exp_log M h2]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [cutError_eq_exp_log M h2]; exact h1, h2⟩
    rw [heq]
    exact (hProx hs).inter measurableSet_Ioi
  · intro r hr
    exact cutError_eq_cutE0_of_neg M hr

end E1Sign

end PercLib.CriticalLRP

/-! ## Case 3 with the measurability input deleted -/

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- **The Case-3 cutoff-defect error is globally measurable**, restated in the scope namespace. -/
theorem measurable_cutError (M : Orchestration.SourceModelData) : Measurable (cutError M) :=
  E1Sign.measurable_cutError M

/-- **`case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux` with `hmeas` removed.**

The hypothesis `hmeas : Measurable (cutError M)` of the shipped wrapper is discharged
unconditionally by `E1Sign.measurable_cutError`, so this version carries exactly one fewer
independent input.  Nothing else is weakened: `h2`, `hderiv`, `hflux`, `hlow`, `hTri`, `hMa`,
`hgm`, `hθ0`, `hθ1`, `hp` and `hHD3` are unchanged, and none of them is derived here. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux_unconditional
    (M : Orchestration.SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {F' : ℝ → ℝ} {c r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hderiv : ∀ t : ℝ, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (F' t) t)
    (hflux : ∀ t : ℝ, r₀ ≤ t →
      F' t = (M.betaCrit : ℝ) * |deriv M.K t| * (E1Sign.exclMass M t).toReal)
    (h0 : Tendsto (cutError M) atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) :=
  case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux (F' := F') (c := c) (r₀ := r₀) (θ := θ)
    (c3 := c3) M hHD3 hTri hc hαd hlow hβ hr₀ h2 hderiv hflux
    (E1Sign.measurable_cutError M) h0 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hMa hc3 hgm

end I420Case3

end PercLib.CriticalLRP

/-! ## The truncated-law defect is globally measurable, and the log-integrability inputs follow -/

namespace PercLib.CriticalLRP

namespace CutoffDefect

open Orchestration
open PercLib.CriticalLRP.BallAverage
open PercLib.CriticalLRP.Analysis

variable (M : SourceModelData)

/-- The truncated-law defect and the flux-pivot defect are the same function. -/
theorem cutE1_eq_pivot (r : ℝ) : cutE1 M r = PivotFlux.cutE1 M r := rfl

/-- Below radius `0` the truncated-law defect vanishes. -/
theorem cutE1_eq_zero_of_neg {r : ℝ} (hr : r < 0) : cutE1 M r = 0 :=
  E1Sign.cutE1_eq_zero_of_neg M hr

/-- **`𝓔_{1,r}` is a measurable function of the radius on all of `ℝ`, with no hypothesis.** -/
theorem measurable_cutE1 : Measurable (cutE1 M) := by
  have hzero : ∀ r : ℝ, r < 0 → cutE1 M r = 0 := fun r hr => cutE1_eq_zero_of_neg M hr
  refine MeasureTheory.measurable_of_measurable_inter_Ioi (c := 0) (g' := fun _ => (0 : ℝ)) ?_
    ?_ measurable_const
  · intro s hs
    have hPm : Measurable fun r : ℝ => cutE1 M (Real.exp (Real.log r)) :=
      E1Sign.measurable_cutE1_exp_log M
    have heq : (fun r : ℝ => cutE1 M r) ⁻¹' s ∩ Ioi 0
        = (fun r : ℝ => cutE1 M (Real.exp (Real.log r))) ⁻¹' s ∩ Ioi 0 := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [Real.exp_log h2]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rwa [Real.exp_log h2] at h1
    rw [heq]
    exact (hPm hs).inter measurableSet_Ioi
  · intro r hr
    exact hzero r hr

/-- **The `(HD)` logarithmic integrability of the defect needs no measurability input.**
This is `CutoffDefect.integrableOn_cutE1_abs_div` with its `hmeas` argument supplied by
`CutoffDefect.measurable_cutE1`. -/
theorem integrableOn_cutE1_abs_div_unconditional
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p) :
    ∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r => |cutE1 M r| / r) (Ioi R) :=
  integrableOn_cutE1_abs_div M hT h1 hC hp hF (measurable_cutE1 M).aemeasurable

/-- **`𝓔_{1,r}` is logarithmically integrable with no measurability input.** -/
theorem logarithmicallyIntegrable_cutE1_unconditional
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p) :
    Analysis.LogarithmicallyIntegrable (fun r => cutE1 M r) :=
  logarithmicallyIntegrable_cutE1 M hT h1 hC hp hF (measurable_cutE1 M)

/-- **`𝓔_{1,r}` is a log-error function with no measurability input.** -/
theorem isLogErrorFunction_cutE1_unconditional
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg
      M.betaCrit 0 < ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun y : M.V => M.S.dist 0 y)
      (fun y : M.V =>
        PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C p) :
    Analysis.IsLogErrorFunction (fun r => cutE1 M r) :=
  isLogErrorFunction_cutE1 M hTri h1 hC hp hF (measurable_cutE1 M)

end CutoffDefect

end PercLib.CriticalLRP

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms MeasureTheory.measurable_toReal_exp_log
#print axioms MeasureTheory.aemeasurable_toReal_of_monotoneOn_Ioi
#print axioms MeasureTheory.measurable_of_measurable_inter_Ioi
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ball_eq_empty_of_neg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ballF_empty_of_neg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.monotoneOn_cutMassAt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.aemeasurable_cutMassAtReal
#print axioms PercLib.CriticalLRP.E1Sign.monotoneOn_pairMass
#print axioms PercLib.CriticalLRP.E1Sign.monotoneOn_connMass
#print axioms PercLib.CriticalLRP.E1Sign.pairMass_eq_zero_of_neg
#print axioms PercLib.CriticalLRP.E1Sign.connMass_eq_zero_of_neg
#print axioms PercLib.CriticalLRP.E1Sign.aemeasurable_pairMassReal
#print axioms PercLib.CriticalLRP.E1Sign.aemeasurable_connMassReal
#print axioms PercLib.CriticalLRP.E1Sign.measurable_pairMassReal
#print axioms PercLib.CriticalLRP.E1Sign.measurable_connMassReal
#print axioms PercLib.CriticalLRP.E1Sign.aemeasurable_cutE1
#print axioms PercLib.CriticalLRP.E1Sign.cutE1_eq_zero_of_neg
#print axioms PercLib.CriticalLRP.E1Sign.cutError_eq_cutE0_of_neg
#print axioms PercLib.CriticalLRP.E1Sign.cutError_eq_exp_log
#print axioms PercLib.CriticalLRP.E1Sign.measurable_cutE1_exp_log
#print axioms PercLib.CriticalLRP.E1Sign.measurable_cutError
#print axioms PercLib.CriticalLRP.I420Case3.measurable_cutError
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux_unconditional
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_eq_pivot
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_eq_zero_of_neg
#print axioms PercLib.CriticalLRP.CutoffDefect.measurable_cutE1
#print axioms PercLib.CriticalLRP.CutoffDefect.integrableOn_cutE1_abs_div_unconditional
#print axioms PercLib.CriticalLRP.CutoffDefect.logarithmicallyIntegrable_cutE1_unconditional
#print axioms PercLib.CriticalLRP.CutoffDefect.isLogErrorFunction_cutE1_unconditional
