/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Radius-integral / edge-sum interchange for the cut-off pivotal mass

Swarm `smwv576pz`, member `m1`, direction A1 (repair and validation of the `smwv4hzkh` m7
packet).

The total pivotal weight of the cut-off first moment is a sum over the (countable) edge set,
`∑'_e pivotalTerm m r e`.  Everything the campaign did with it so far either bounded it
pointwise at a fixed radius or integrated it as an opaque function of `r`.  This file proves that
its interval integral may be taken term by term over the edges — a genuine change of the order of
summation (`∫_a^b ∑'_e = ∑'_e ∫_a^b`), not a comparison of two `tsum`s — and then reads the
result over the vertex decomposition of a finite observation, and over the signed per-edge Russo
fluxes of a single vertex.

The interchange engine (`intervalIntegral_tsum_eq_tsum_intervalIntegral`) is stated for an
arbitrary countable index type and an arbitrary summable constant majorant, and is proved from
Mathlib's `MeasureTheory.integral_tsum`, i.e. from Tonelli plus finiteness of the `ℝ≥0∞`-integral
of the norm series.  The model-level statements only feed it the landed interior-scale envelope
`weightedTouch_le_env` / `m1_summable_env` (for the signed flux: `m1_abs_flux_le_env`), so no new
analytic input is introduced.

The finite-observation vertex statement is *not* a restatement of `sMomentWeight`: the total
pivotal weight of an observation `A` carries the truncation bound `∑_{x∈A} |q x|` inside a `max`,
so the identity `sMomentWeight 0 A q = ∑_{x∈A} sMomentWeight 0 {x} q` is a real (`max` / `tsum`)
identity proved from `Defs.pivotalTerm_finset_sum`, not `rfl`.

What is *not* claimed here, and where the previous version of this packet was wrong, is the
closing section `5`: the `y`-independence of the *pivotal-weight* bound is a limitation of that
particular domination route only.  The vertex-order interchange `∑'_y ∫_r = ∫_r ∑'_y` for the
cut-mass flux is proved by a different route (monotone convergence over finite vertex sets) in
`Analysis/Cutoff/IntegralFluxInterchange.lean`; nothing here contradicts it.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PivotalWeight.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling

/-!
Term-by-term integration over the edge set of the cut-off pivotal mass.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The interchange engine -/

/-- **Tonelli for a compact radius window.**

Let `w : ι → ℝ → ℝ` be a countable family of functions on `[a,b]`, dominated in norm on `[a,b]`
by a summable constant family `bound`.  Then the interval integral of the pointwise series is
the series of the interval integrals.

Signed integrands are allowed: only `‖w i r‖ ≤ bound i` is used.  The proof does not use a
radius-uniform *summable majorant of the integrals*: the finiteness of `∑'_i ∫⁻ ‖w i‖ₑ` is
obtained from the pointwise majorant, and Mathlib's `MeasureTheory.integral_tsum` then performs
the interchange in one step. -/
theorem intervalIntegral_tsum_eq_tsum_intervalIntegral
    {ι : Type*} [Countable ι] {w : ι → ℝ → ℝ} {bound : ι → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmeas : ∀ i, Measurable (w i))
    (hbound : Summable bound) (hbound0 : ∀ i, 0 ≤ bound i)
    (hle : ∀ i r, r ∈ Set.Icc a b → ‖w i r‖ ≤ bound i) :
    ∫ r in a..b, (∑' i, w i r) = ∑' i, ∫ r in a..b, w i r := by
  classical
  have hb0 : 0 ≤ b - a := sub_nonneg.mpr hab
  -- pointwise bound of the `ℝ≥0∞`-integral of each `‖w i‖ₑ`
  have hlin : ∀ i, ∫⁻ r in Set.Ioc a b, ‖w i r‖ₑ ≤ ENNReal.ofReal ((b - a) * bound i) := by
    intro i
    have h1 : ∀ r ∈ Set.Ioc a b, ‖w i r‖ₑ ≤ ENNReal.ofReal (bound i) := by
      intro r hr
      rw [Real.enorm_eq_ofReal_abs, ← Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (hle i r (Set.Ioc_subset_Icc_self hr))
    calc ∫⁻ r in Set.Ioc a b, ‖w i r‖ₑ
        ≤ ∫⁻ _r in Set.Ioc a b, ENNReal.ofReal (bound i) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          exact h1 r hr
      _ = ENNReal.ofReal (bound i) * (volume (Set.Ioc a b)) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ = ENNReal.ofReal (bound i) * ENNReal.ofReal (b - a) := by rw [Real.volume_Ioc]
      _ = ENNReal.ofReal (bound i * (b - a)) := (ENNReal.ofReal_mul (hbound0 i)).symm
      _ = ENNReal.ofReal ((b - a) * bound i) := by rw [mul_comm]
  -- the norm series is finite
  have hseries : (∑' i, ∫⁻ r in Set.Ioc a b, ‖w i r‖ₑ)
      ≤ ENNReal.ofReal ((b - a) * ∑' i, bound i) := by
    calc (∑' i, ∫⁻ r in Set.Ioc a b, ‖w i r‖ₑ)
        ≤ ∑' i, ENNReal.ofReal ((b - a) * bound i) := ENNReal.tsum_le_tsum hlin
      _ = ENNReal.ofReal (∑' i, (b - a) * bound i) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg hb0 (hbound0 i))
            (hbound.mul_left _)).symm
      _ = ENNReal.ofReal ((b - a) * ∑' i, bound i) := by
          rw [hbound.tsum_mul_left]
  have hkey : ∫ r, (∑' i, w i r) ∂(volume.restrict (Set.Ioc a b))
      = ∑' i, ∫ r, w i r ∂(volume.restrict (Set.Ioc a b)) := by
    refine MeasureTheory.integral_tsum (μ := volume.restrict (Set.Ioc a b)) (f := w)
      (fun i => (hmeas i).aestronglyMeasurable) ?_
    exact ne_of_lt (lt_of_le_of_lt hseries ENNReal.ofReal_lt_top)
  calc ∫ r in a..b, (∑' i, w i r)
      = ∫ r, (∑' i, w i r) ∂(volume.restrict (Set.Ioc a b)) :=
        intervalIntegral.integral_of_le hab
    _ = ∑' i, ∫ r, w i r ∂(volume.restrict (Set.Ioc a b)) := hkey
    _ = ∑' i, ∫ r in a..b, w i r :=
        tsum_congr fun i => (intervalIntegral.integral_of_le hab).symm

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 2. Model level: the interior-scale envelope bounds every per-edge weight -/

/-- **Per-edge domination at every truncation bound.**  The landed interior-scale envelope
(`weightedTouch_le_env`) bounds the `m = 1` per-edge weight; multiplying by the nonnegative
factor `max m 0` bounds the per-edge weight at truncation bound `m`. -/
theorem pivotalTerm_le_env {a' b' ρ C m : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) {r : ℝ} (hr : r ∈ Set.Icc a' b') (e : Sym2 M.V) :
    M.pivotalTerm m r e ≤
      max m 0 * ((C / (-(deriv M.K ρ)) *
          Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        (|M.cutEdgeDeriv ρ e| *
          (2 * (M.cutLaw b').real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))) := by
  have h := M.weightedTouch_le_env ha' ha'b' hb'ρ hCb hC0 hKρ hr e
  unfold pivotalTerm
  calc |M.cutEdgeDeriv r e| *
        (2 * max m 0 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})
      = max m 0 * (|M.cutEdgeDeriv r e| *
          (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})) := by ring
    _ ≤ max m 0 * ((C / (-(deriv M.K ρ)) *
          Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        (|M.cutEdgeDeriv ρ e| *
          (2 * (M.cutLaw b').real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))) :=
        mul_le_mul_of_nonneg_left h (le_max_right m 0)

/-- The envelope family is summable at every truncation bound. -/
theorem summable_pivotalTerm_env {a' b' ρ C m : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) :
    Summable fun e : Sym2 M.V =>
      max m 0 * ((C / (-(deriv M.K ρ)) *
          Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        (|M.cutEdgeDeriv ρ e| *
          (2 * (M.cutLaw b').real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))) :=
  (M.m1_summable_env ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol).mul_left _

/-- **The per-edge pivotal weight series converges at every radius of the window.** -/
theorem summable_pivotalTerm_of_envelope {a' b' ρ C m : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    {r : ℝ} (hr : r ∈ Set.Icc a' b') :
    Summable fun e : Sym2 M.V => M.pivotalTerm m r e :=
  Summable.of_nonneg_of_le (fun e => M.pivotalTerm_nonneg m r e)
    (fun e => M.pivotalTerm_le_env ha' ha'b' hb'ρ hCb hC0 hKρ hr e)
    (M.summable_pivotalTerm_env ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol)

/-! ## 3. Term-by-term integration of the total pivotal weight -/

/-- **The interval integral of the total pivotal weight is the edge sum of the per-edge
interval integrals.**

This is the interchange between the two orderings `∫_a^b ∑'_e` and `∑'_e ∫_a^b`.  Both sides
are genuinely different constructions: the left-hand integrand is the real series that
`sMomentWeight` is defined as (`Defs.sMomentWeight_eq_tsum_pivotalTerm`), while the right-hand
side integrates each summand separately.

All analytic inputs are the landed envelope data at the interior scale `ρ ≥ b'`: positivity of
`-K'` is only used through `hKρ : deriv M.K ρ < 0` and the bound `hCb`. -/
theorem intervalIntegral_sMomentWeight_eq_tsum_integral
    {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b') (hb'ρ : b' ≤ ρ)
    (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (A : Finset M.V) (q : M.V → ℝ) :
    ∫ r in a'..b', sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V,
          ∫ r in a'..b', M.pivotalTerm (∑ x ∈ A, |q x|) r e := by
  classical
  have hΛ0 : 0 ≤ C / (-(deriv M.K ρ)) *
      Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) := by
    refine mul_nonneg (div_nonneg hC0 ?_) (Real.exp_nonneg _)
    linarith
  have h := intervalIntegral_tsum_eq_tsum_intervalIntegral (ι := Sym2 M.V)
    (w := fun e r => M.pivotalTerm (∑ x ∈ A, |q x|) r e)
    (bound := fun e => max (∑ x ∈ A, |q x|) 0 * ((C / (-(deriv M.K ρ)) *
      Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
      (|M.cutEdgeDeriv ρ e| *
        (2 * (M.cutLaw b').real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))))
    ha'b' (fun e => M.measurable_pivotalTerm _ e)
    (M.summable_pivotalTerm_env ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol)
    (fun e => mul_nonneg (le_max_right _ _)
      (mul_nonneg hΛ0 (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) measureReal_nonneg))))
    (fun e r hr => by
      rw [Real.norm_eq_abs, abs_of_nonneg (M.pivotalTerm_nonneg _ r e)]
      exact M.pivotalTerm_le_env ha' ha'b' hb'ρ hCb hC0 hKρ hr e)
  have hfun : (fun r => sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r)
      = fun r => ∑' e : Sym2 M.V, M.pivotalTerm (∑ x ∈ A, |q x|) r e :=
    funext fun r => M.sMomentWeight_eq_tsum_pivotalTerm A q r
  rw [hfun]
  exact h

/-- **Interval integrability of the total pivotal weight from the interior-scale envelope.**

Proved for an arbitrary finite observation `(A, q)` by reducing to the landed singleton case
`intervalIntegrable_pivotalWeight_of_envelope` and multiplying by the truncation bound. -/
theorem intervalIntegrable_sMomentWeight_of_envelope
    {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b') (hb'ρ : b' ≤ ρ)
    (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (A : Finset M.V) (q : M.V → ℝ) :
    IntervalIntegrable (fun r =>
      sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r) volume a' b' := by
  classical
  have hbase : IntervalIntegrable (fun r => ∑' e : Sym2 M.V, M.pivotalTerm 1 r e)
      volume a' b' := by
    have h := M.intervalIntegrable_pivotalWeight_of_envelope ha' ha'b' hb'ρ hCb hC0 hKρ hρ
      hvol (0 : M.V)
    simpa only [sMomentWeight_eq_tsum_pivotalTerm, Finset.sum_singleton, abs_one,
      pivotalTerm_one_eq] using h
  refine (hbase.const_mul (max (∑ x ∈ A, |q x|) 0)).congr ?_
  intro r hr
  rw [Set.uIoc_of_le ha'b'] at hr
  have hrIcc : r ∈ Set.Icc a' b' := Set.Ioc_subset_Icc_self hr
  change max (∑ x ∈ A, |q x|) 0 * (∑' e : Sym2 M.V, M.pivotalTerm 1 r e)
    = sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r
  rw [sMomentWeight_eq_tsum_pivotalTerm (A := A) (q := q)]
  rw [← Summable.tsum_mul_left (max (∑ x ∈ A, |q x|) 0)
    (M.summable_pivotalTerm_of_envelope ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol
      (m := 1) hrIcc)]
  exact (tsum_congr fun e => M.pivotalTerm_eq_smul_one (∑ x ∈ A, |q x|) r e).symm

/-- **The interval integral of the total pivotal weight of a finite observation is the vertex
sum of the interval integrals of its per-vertex weights.**

The per-vertex weight of `x` is the total pivotal weight of the singleton observation `{x}`.
The identity is a real one: the truncation bound `∑_{x∈A} |q x|` inside a `max` is what makes
`sMomentWeight 0 A q` differ from a literal `∑_{x∈A}`, and
`Defs.pivotalTerm_finset_sum` is the `max`-arithmetic that reconciles them, after which the
interchange is the finite-sum rule `intervalIntegral.integral_finsetSum`. -/
theorem intervalIntegral_sMomentWeight_eq_sum_vertex_integral
    {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b') (hb'ρ : b' ≤ ρ)
    (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (A : Finset M.V) (q : M.V → ℝ) :
    ∫ r in a'..b', sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r
      = ∑ x ∈ A, ∫ r in a'..b',
          sMomentWeight (0 : M.V) ({x} : Finset M.V) q M.cutProb M.cutEdgeDeriv r := by
  classical
  have hEqOn : Set.EqOn
      (fun r => sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r)
      (fun r => ∑ x ∈ A,
        sMomentWeight (0 : M.V) ({x} : Finset M.V) q M.cutProb M.cutEdgeDeriv r)
      (Set.uIcc a' b') := by
    intro r hr
    rw [Set.uIcc_of_le ha'b'] at hr
    have hrIcc : r ∈ Set.Icc a' b' := hr
    simp only [sMomentWeight_eq_tsum_pivotalTerm, Finset.sum_singleton]
    rw [← Summable.tsum_finsetSum (f := fun x e => M.pivotalTerm |q x| r e)
      (fun x _ => M.summable_pivotalTerm_of_envelope ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol
        (m := |q x|) hrIcc)]
    exact tsum_congr fun e => M.pivotalTerm_finset_sum A q r e
  have hInt : ∀ x ∈ A, IntervalIntegrable (fun r =>
      sMomentWeight (0 : M.V) ({x} : Finset M.V) q M.cutProb M.cutEdgeDeriv r)
      volume a' b' :=
    fun x _ => M.intervalIntegrable_sMomentWeight_of_envelope ha' ha'b' hb'ρ hCb hC0 hKρ hρ
      hvol ({x} : Finset M.V) q
  rw [intervalIntegral.integral_congr hEqOn]
  exact intervalIntegral.integral_finsetSum hInt

/-- **The interval integral of the total pivotal weight is the double sum of the per-edge,
per-vertex interval integrals.**

This composes the edge interchange with the finite vertex decomposition: on the right the
integrand is integrated first per edge and then summed over the finite observation.  It is the
form in which the per-vertex dominated quantities of the campaign (each `{x}` carries its own
weight `|q x|`) can be handled separately. -/
theorem intervalIntegral_sMomentWeight_eq_sum_vertex_tsum_integral
    {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b') (hb'ρ : b' ≤ ρ)
    (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (A : Finset M.V) (q : M.V → ℝ) :
    ∫ r in a'..b', sMomentWeight (0 : M.V) A q M.cutProb M.cutEdgeDeriv r
      = ∑ x ∈ A, ∑' e : Sym2 M.V,
          ∫ r in a'..b', M.pivotalTerm |q x| r e := by
  rw [M.intervalIntegral_sMomentWeight_eq_sum_vertex_integral
    ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol A q]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := M.intervalIntegral_sMomentWeight_eq_tsum_integral
    ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol ({x} : Finset M.V) q
  simpa only [Finset.sum_singleton] using h

/-- **The interval integral of the infinite pivotal flux is the edge sum of the per-edge
integrated fluxes.**

This is the same interchange as above, now for the *signed* per-edge Russo terms
`c_r(e) · pivot_r(e)`: the engine's norm hypothesis is met by the landed per-edge envelope
`m1_abs_flux_le_env`.  Consequently the integrated Russo flux of a single vertex can be
computed by integrating each edge separately, which is the edge-order counterpart of the
vertex-order integrated identity of `IntegralFluxInterchange.lean`. -/
theorem intervalIntegral_sMomentInfFlux_eq_tsum_integral
    {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b') (hb'ρ : b' ≤ ρ)
    (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) (y : M.V) :
    ∫ r in a'..b', sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V, ∫ r in a'..b', M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r)
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
  classical
  have hΛ0 : 0 ≤ C / (-(deriv M.K ρ)) *
      Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) := by
    refine mul_nonneg (div_nonneg hC0 ?_) (Real.exp_nonneg _)
    linarith
  have h := intervalIntegral_tsum_eq_tsum_intervalIntegral (ι := Sym2 M.V)
    (w := fun e r => M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
    (bound := fun e => (C / (-(deriv M.K ρ)) *
      Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
      (|M.cutEdgeDeriv ρ e| *
        (2 * (M.cutLaw b').real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})))
    ha'b'
    (fun e => (M.measurable_cutEdgeDeriv e).mul (M.measurable_pivotalFlux_singleton y e))
    (M.m1_summable_env ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol)
    (fun e => mul_nonneg hΛ0 (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) measureReal_nonneg)))
    (fun e r hr => M.m1_abs_flux_le_env ha' ha'b' hb'ρ hCb hC0 hKρ y hr e)
  have hfun : (fun r =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
      = fun r => ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r)
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    funext r
    rw [sMomentInfFlux, infFluxOf]
    exact tsum_congr fun e => by rw [M.cutLaw_eq_edgeMeasure r]
  rw [hfun]
  exact h

/-! ## 4. The signed flux series is interval integrable from the same envelope

The signed per-edge series itself is bounded on the window by the *sum* of the envelope, which is
a constant.  Hence the infinite flux of one vertex is interval integrable on every window where
the envelope data holds, with no extra moment input: this removes `hboundint`-type hypotheses
from statements about the integrated flux. -/

/-- **Interval integrability of the signed infinite flux of one vertex.** -/
theorem intervalIntegrable_sMomentInfFlux_of_envelope
    {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b') (hb'ρ : b' ≤ ρ)
    (hCb : ∀ r ∈ Set.Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) (y : M.V) :
    IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) volume a' b' := by
  classical
  have hΛ0 : 0 ≤ C / (-(deriv M.K ρ)) *
      Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) := by
    refine mul_nonneg (div_nonneg hC0 ?_) (Real.exp_nonneg _)
    linarith
  set env : Sym2 M.V → ℝ := fun e => (C / (-(deriv M.K ρ)) *
      Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
      (|M.cutEdgeDeriv ρ e| *
        (2 * (M.cutLaw b').real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})) with henv
  have henvsum : Summable env := M.m1_summable_env ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol
  have hfun : (fun r => sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      = fun r => ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r)
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    funext r
    rw [sMomentInfFlux, infFluxOf]
    exact tsum_congr fun e => by rw [M.cutLaw_eq_edgeMeasure r]
  have hmeas : Measurable fun r => sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r := by
    rw [hfun]
    exact Measurable.tsum fun e =>
      (M.measurable_cutEdgeDeriv e).mul (M.measurable_pivotalFlux_singleton y e)
  refine (intervalIntegrable_const (c := ∑' e, env e)).mono_fun'
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [Set.uIoc_of_le ha'b'] at hr
  have hrIcc : r ∈ Set.Icc a' b' := Set.Ioc_subset_Icc_self hr
  have hterm : ∀ e : Sym2 M.V, ‖M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖ ≤ env e := fun e =>
    M.m1_abs_flux_le_env ha' ha'b' hb'ρ hCb hC0 hKρ y hrIcc e
  have habs : Summable fun e : Sym2 M.V => ‖M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖ :=
    henvsum.of_nonneg_of_le (fun e => norm_nonneg _) hterm
  have hbound : ‖sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r‖ ≤ ∑' e, env e := by
    rw [sMomentInfFlux, infFluxOf]
    calc ‖∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          pivotalFlux (edgeMeasure (M.cutProb r))
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖
        = ‖∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
            pivotalFlux (M.cutLaw r)
              (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖ := by
          rw [M.cutLaw_eq_edgeMeasure r]
      _ ≤ ∑' e : Sym2 M.V, ‖M.cutEdgeDeriv r e *
            pivotalFlux (M.cutLaw r)
              (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖ :=
          norm_tsum_le_tsum_norm habs
      _ ≤ ∑' e, env e := habs.tsum_le_tsum hterm henvsum
  exact hbound

/-! ## 5. Scope of the pivotal-weight bound: a limitation of that route, not of the interchange

The per-vertex bound available from the pivotal weight is `|flux_y r| ≤ sMomentWeight 0 {y} 1 … r`
(`IntegralFluxInterchange.abs_sMomentInfFlux_le`), and at a *singleton* observation with unit
weight that quantity only sees the truncation bound `∑_{x∈{y}} |1| = 1`: it is the same real
number for every vertex `y` (production `SourceModelData.sMomentWeight_singleton_indep`).

Consequently, at a radius where that common value is positive, the family
`y ↦ sMomentWeight 0 {y} 1 … r` has no summable majorant on the infinite vertex set, and in
particular a estimate of the shape `|flux_y r| ≤ u y` *obtained from the pivotal weight* can never
have `Summable u`.

This is a limitation of the pivotal-weight domination route only.  It says nothing about the
vertex-order interchange `∑'_y ∫_r flux_y = ∫_r ∑'_y flux_y` for the cut-mass flux, which is
proved by a different argument (monotone convergence of the finite-vertex-set fundamental theorem
of calculus) in `Analysis/Cutoff/IntegralFluxInterchange.lean`.  Nothing in this section should be
read as a mathematical impossibility of that interchange. -/

/-- The total pivotal weight of a unit-weight singleton observation is independent of the
vertex: it is production `SourceModelData.sMomentWeight_singleton_indep` at the model's own cut
probability and edge derivative. -/
theorem pivotalWeight_singleton_const (r : ℝ) (y y' : M.V) :
    sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r
      = sMomentWeight (0 : M.V) ({y'} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r :=
  M.sMomentWeight_singleton_indep M.cutProb M.cutEdgeDeriv r y y'

/-- **The per-vertex pivotal weight is not summable in the vertex at a radius of positive weight.**

The family is constant in `y` (`pivotalWeight_singleton_const`) on the infinite vertex set
(`Resampling.infinite_vertex`). -/
theorem not_summable_pivotalWeight_singleton_of_pos (r : ℝ) (y : M.V)
    (hpos : 0 < sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r) :
    ¬ Summable fun y' : M.V =>
      sMomentWeight (0 : M.V) ({y'} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r := by
  have hconst : (fun y' : M.V =>
      sMomentWeight (0 : M.V) ({y'} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
      = fun _ => sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r :=
    funext fun y' => M.pivotalWeight_singleton_const r y' y
  rw [hconst]
  exact M.not_summable_const_of_pos (C := _) hpos

/-- **No summable vertex majorant of the per-vertex pivotal weight.**

At a radius where the unit-weight singleton pivotal weight is positive, there is no `u : M.V → ℝ`
with `Summable u` and `sMomentWeight 0 {y} 1 … r ≤ u y` for all `y`.  This is the precise form of
the statement that the pivotal-weight estimate cannot supply the vertex majorant; it is not a
statement about the per-vertex flux itself. -/
theorem not_exists_summable_majorant_pivotalWeight_singleton (r : ℝ) (y : M.V)
    (hpos : 0 < sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r) :
    ¬ ∃ u : M.V → ℝ, Summable u ∧ ∀ y' : M.V,
      sMomentWeight (0 : M.V) ({y'} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r ≤ u y' := by
  rintro ⟨u, hsum, hu⟩
  exact not_summable_of_const_le M hpos hu hsum

end SourceModelData

end PercLib.CriticalLRP.Orchestration
