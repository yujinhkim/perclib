/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m8`, direction d4 (consumer-side replacement for `hT3`).

# A consumer-side repair of the Case-3 numerator interface

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.

## The problem this file addresses

`PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3` reduces Proposition I.4.15, Case 3 to
three source-shaped inputs at the per-vertex level (`hgap`, `hT3`, `hpoly4`).  The `ℓ = 4`
input `hpoly4` is manufactured at all radii elsewhere; the `ℓ = 3` input

  `hT3 : ∀ r ≥ 1, ∀ y,  T^3_{β_c,r}(0,y) ≤ Cp * (∇_{r^c} + r^{-c})`

is the printed `ℓ = 3` case of Lemma I.4.18 and is **not available**.  This file does not try to
prove any new `ℓ = 3` estimate (that is a different direction); it changes the *consumer*, and
records three things.

### 1. The current consumer is vacuous (negative, machine-checked)

`M.cutTwoPoint r 0 0 = 1` gives `T^3_{β_c,r}(0,0) ≥ 1`
(`I420Case3.one_le_polyK_three_of_chi_ne_top`).  Hence the pointwise `hT3` — with a driver that
tends to `0`, as `hcase3` of `secondMoment_asymptotic_case3` demands — forces `Cp * drv r ≥ 1`
for all large `r`, contradicting `drv → 0`.  Consequently the hypothesis bundle `hcase3` of
`secondMoment_asymptotic_case3` is *uninhabited*: that theorem is true but vacuous.
See `not_pointwise_polyK_three_of_driver_tendsto_zero` and
`secondMomentCase3_hcase3_unsatisfiable`.

### 2. The exact weakened consumer input that suffices (positive)

What the summation actually needs is only the *window sum* of the threefold power, and what the
`ℓ = 3` term can honestly contribute is

* a **constant** times the number `N r` of window vertices that are still "near" (the honest
  local origin correction), plus
* `|B_r|` times a **vanishing** far factor.

`sum_perVertex_le_nearFar` and `connCubeMass_le_of_windowGap_nearFar` state and prove exactly
this replacement; the resulting residual in the Case-3 error is `A * N r / |B_r|`, and
`p2ExclError_le_invBall_add_driver` produces the error bound with that residual.

### 3. Two residuals, one harmless and one not (the Case-1-only limitation)

* The honest residual `N r / |B_r|` with `N r ⪯ r^{c d}`, `c < 1`, and `|B_r| ⪰ r^d` is bounded
  by `r^{(c-1)d}`, which **tends to `0` and is logarithmically integrable**
  (`logIntegrable_nearCount_ratio`, `tendsto_nearCount_ratio`); for a single origin vertex
  (`N ≡ 1`) this is the constant-over-`|B_r|` residual of `logIntegrable_inv_ball`.
* The column-sum substitute `∑_y T^3(0,y) = χ^3`
  (`sum_perVertex_le_column`) instead leaves `χ^3/|B_r|`, which **does not even tend to `0`**
  once `3α ≥ d` (`columnResidual_not_tendsto_zero`).  This is the machine-checked form of the
  "Case-1-only" limitation recorded in the header of `Case3.lean`.

Nothing here assumes a new analytic input beyond the two honest `ℓ = 3` inputs; the per-vertex
moment gap `hgap` is carried unchanged.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3

/-! # Consumer-side repair of the Case-3 numerator -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData
namespace SecondMomentCase3

/-! ## 1. The abstract window summation with a near/far budget for the `ℓ = 3` term

The source's `ℓ = 3` term, summed over the window `s`, is `C₃ (∑_{y∈s} T³(0,y)) χ⁴`.  Instead of
bounding every summand by the same vanishing factor (impossible: the origin summand is `≥ 1`), we
only ask for the *window sum*

  `∑_{y∈s} T³(0,y) ≤ A * N + s.card * B`,

with `A` a constant near/origin bound, `N` the number of window vertices still near, and `B` the
vanishing far factor.  Both the origin-only budget (`N = 1`) and the column-sum budget
(`A = Cp0 χ³`, `N = 1`, `B = 0`) are instances; see below. -/

theorem sum_perVertex_le_nearFar {ι : Type*} (s : Finset ι) (F T3 T4 : ι → ℝ)
    {χ drv C3 C4 Cp A B N : ℝ}
    (hF : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3)
    (hT3 : ∑ y ∈ s, T3 y ≤ A * N + (s.card : ℝ) * B)
    (hT4 : ∀ y ∈ s, T4 y ≤ Cp * drv * χ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hχ : 0 ≤ χ) :
    ∑ y ∈ s, F y ≤ C3 * A * N * χ ^ 4 + (s.card : ℝ) * (C3 * B + C4 * Cp * drv) * χ ^ 4 := by
  have hχ4 : (0 : ℝ) ≤ χ ^ 4 := pow_nonneg hχ 4
  have hsum3 : ∑ y ∈ s, C3 * T3 y * χ ^ 4 = C3 * (∑ y ∈ s, T3 y) * χ ^ 4 := by
    rw [Finset.sum_congr rfl (g := fun y => (C3 * χ ^ 4) * T3 y) fun y _ => by ring,
      ← Finset.mul_sum]
    ring
  have hsum4 : ∑ y ∈ s, C4 * T4 y * χ ^ 3 = C4 * (∑ y ∈ s, T4 y) * χ ^ 3 := by
    rw [Finset.sum_congr rfl (g := fun y => (C4 * χ ^ 3) * T4 y) fun y _ => by ring,
      ← Finset.mul_sum]
    ring
  have hT4sum : ∑ y ∈ s, T4 y ≤ (s.card : ℝ) * (Cp * drv * χ) := by
    calc ∑ y ∈ s, T4 y ≤ ∑ _y ∈ s, Cp * drv * χ := Finset.sum_le_sum hT4
      _ = (s.card : ℝ) * (Cp * drv * χ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hb3 : C3 * (∑ y ∈ s, T3 y) * χ ^ 4
      ≤ C3 * (A * N + (s.card : ℝ) * B) * χ ^ 4 := by
    have h1 : C3 * (∑ y ∈ s, T3 y) ≤ C3 * (A * N + (s.card : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hT3 hC3
    exact mul_le_mul_of_nonneg_right h1 hχ4
  have hb4 : C4 * (∑ y ∈ s, T4 y) * χ ^ 3
      ≤ C4 * ((s.card : ℝ) * (Cp * drv * χ)) * χ ^ 3 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT4sum hC4) (pow_nonneg hχ 3)
  have hmain : ∑ y ∈ s, F y
      ≤ (C3 * (∑ y ∈ s, T3 y) * χ ^ 4) + C4 * (∑ y ∈ s, T4 y) * χ ^ 3 := by
    calc ∑ y ∈ s, F y
        ≤ ∑ y ∈ s, (C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3) := Finset.sum_le_sum hF
      _ = (∑ y ∈ s, C3 * T3 y * χ ^ 4) + ∑ y ∈ s, C4 * T4 y * χ ^ 3 :=
          Finset.sum_add_distrib
      _ = (C3 * (∑ y ∈ s, T3 y) * χ ^ 4) + C4 * (∑ y ∈ s, T4 y) * χ ^ 3 := by
          rw [hsum3, hsum4]
  have hstep : C3 * (A * N + (s.card : ℝ) * B) * χ ^ 4
      + C4 * ((s.card : ℝ) * (Cp * drv * χ)) * χ ^ 3
      = C3 * A * N * χ ^ 4 + (s.card : ℝ) * (C3 * B + C4 * Cp * drv) * χ ^ 4 := by
    ring
  linarith [hmain, hb3, hb4, hstep.le, hstep.ge]

/-- **The origin-only budget.**  With a *constant* `A` charged only once (a single near vertex,
`N = 1`) and a vanishing far factor `B` charged `|s|` times, the window sum of the `ℓ = 3` term
is `C₃ A χ⁴ + |s| (C₃ B + C₄ Cp drv) χ⁴`.  The first piece is the honest local origin
correction: it is *not* multiplied by `|s|`. -/
theorem sum_perVertex_le_origin {ι : Type*} (s : Finset ι) (F T3 T4 : ι → ℝ)
    {χ drv C3 C4 Cp A B : ℝ}
    (hF : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3)
    (hT3 : ∑ y ∈ s, T3 y ≤ A + (s.card : ℝ) * B)
    (hT4 : ∀ y ∈ s, T4 y ≤ Cp * drv * χ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hχ : 0 ≤ χ) :
    ∑ y ∈ s, F y ≤ C3 * A * χ ^ 4 + (s.card : ℝ) * (C3 * B + C4 * Cp * drv) * χ ^ 4 := by
  have := sum_perVertex_le_nearFar s F T3 T4 (drv := drv) (C3 := C3) (C4 := C4) (Cp := Cp)
    (A := A) (B := B) (N := 1) hF (by simpa using hT3) hT4 hC3 hC4 hχ
  simpa using this

/-- **The column-sum budget (the classical, Case-1-only substitute).**  If the `ℓ = 3` window sum
is controlled only by the column sum `∑_y T³(0,y) = χ³`, i.e. `∑_{y∈s} T³(0,y) ≤ Cp0 χ³`, then the
window sum carries the separate piece `C₃ Cp0 χ⁷`.  After division by `|B_r| χ E|K|²` this is
`(C₃ Cp0 / c₃) χ³/|B_r|` — see `columnResidual_not_tendsto_zero` for why that is fatal in the
Case-3 regime. -/
theorem sum_perVertex_le_column {ι : Type*} (s : Finset ι) (F T3 T4 : ι → ℝ)
    {χ drv C3 C4 Cp Cp0 : ℝ}
    (hF : ∀ y ∈ s, F y ≤ C3 * T3 y * χ ^ 4 + C4 * T4 y * χ ^ 3)
    (hT3 : ∑ y ∈ s, T3 y ≤ Cp0 * χ ^ 3)
    (hT4 : ∀ y ∈ s, T4 y ≤ Cp * drv * χ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hχ : 0 ≤ χ) :
    ∑ y ∈ s, F y ≤ C3 * Cp0 * χ ^ 7 + (s.card : ℝ) * (C4 * Cp * drv) * χ ^ 4 := by
  have := sum_perVertex_le_origin s F T3 T4 (drv := drv) (C3 := C3) (C4 := C4) (Cp := Cp)
    (A := Cp0 * χ ^ 3) (B := 0) hF (by simpa using hT3) hT4 hC3 hC4 hχ
  have hid : C3 * (Cp0 * χ ^ 3) * χ ^ 4 = C3 * Cp0 * χ ^ 7 := by ring
  have hid2 : (s.card : ℝ) * (C3 * 0 + C4 * Cp * drv) * χ ^ 4
      = (s.card : ℝ) * (C4 * Cp * drv) * χ ^ 4 := by ring
  rw [hid, hid2] at this
  exact this

end SecondMomentCase3

/-! ## 2. The pointwise `ℓ = 3` hypothesis is unsatisfiable (the current consumer is vacuous)

`M.cutTwoPoint r 0 0 = 1`, so the diagonal threefold power is `≥ 1` at every radius
(`I420Case3.one_le_polyK_three_of_chi_ne_top`).  A *pointwise* bound of the form
`T^3(0,y) ≤ Cp * drv r` for every `y`, with `drv r → 0`, is therefore impossible: at `y = 0` it
reads `1 ≤ Cp * drv r` for every large `r`.

This is the exact reason why the hypothesis `hT3` of
`SecondMomentCase3.connCubeMass_le_of_windowGap` can never be supplied, and hence why the
hypothesis bundle `hcase3` of `secondMoment_asymptotic_case3` is uninhabited.  The repair is
*not* a better pointwise bound — it is the window-summed budget of Section 1. -/

variable (M : SourceModelData)

namespace SecondMomentCase3

/-- **No vanishing pointwise bound on `T^3_{β_c,r}(0,·)`.**  If the diagonal threefold power is at
least `1` (which it is as soon as `E_{β_c,r}|K| ≠ ⊤`, so that the `ℝ≥0∞`-to-`ℝ` transport is
valid), then a pointwise bound `T^3(0,y) ≤ Cp * drv r` for all `y` and all `r ≥ 1` forces
`Cp * drv r ≥ 1` for all large `r`; in particular it is incompatible with `drv → 0`. -/
theorem not_pointwise_polyK_three_of_driver_tendsto_zero
    (hχ : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    {c Cp : ℝ} (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    ¬ (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * M.case3Driver c r) := by
  intro h
  have hge : ∀ᶠ r : ℝ in atTop, 1 ≤ Cp * M.case3Driver c r := by
    filter_upwards [hχ, eventually_ge_atTop (1 : ℝ)] with r hχr hr
    exact le_trans (I420Case3.one_le_polyK_three_of_chi_ne_top M r hχr) (h r hr 0)
  have h0 : Tendsto (fun r : ℝ => Cp * M.case3Driver c r) atTop (𝓝 (Cp * 0)) :=
    hdrv.const_mul Cp
  have hlt : ∀ᶠ r : ℝ in atTop, Cp * M.case3Driver c r < 1 := by
    have := (tendsto_order.1 h0).2 1 (by rw [mul_zero]; norm_num)
    simpa using this
  obtain ⟨r, hr1, hr2⟩ := (hge.and hlt).exists
  linarith

/-- **The Case-3 input bundle `hcase3` of `secondMoment_asymptotic_case3` is uninhabited.**

`hcase3` asks simultaneously for `Cp > 0`, `case3Driver c → 0`, and the pointwise `ℓ = 3` bound.
Those three are contradictory at `y = 0` once `E_{β_c,r}|K| ≠ ⊤` eventually (which is hypothesis
`h1` of that theorem).  Consequently `secondMoment_asymptotic_case3` is true but *vacuous*: the
`ℓ = 3` slot must be replaced by the window-summed budget. -/
theorem hcase3_unsatisfiable {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤) :
    ¬ ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * M.case3Driver c r) ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
          ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
  rintro ⟨c, Cp, -, -, hdrv, -, hT3, -⟩
  exact not_pointwise_polyK_three_of_driver_tendsto_zero M (by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    rw [cutMassAt_zero_eq_cutMoment]
    exact h1 r hr) hdrv hT3
end SecondMomentCase3

/-! ## 3. The honest residual is harmless

The repaired consumer carries a residual of the shape `A * N r / |B_r|`.  Two models of `N`:

* `N ≡ 1` (a single origin vertex): the residual is `A / |B_r|`;
* `N r ⪯ r^{c d}` (the vertices still "near", i.e. of distance `< r^c`): the residual is
  `⪯ r^{(c-1)d}`, which vanishes and is logarithmically integrable as soon as `c < 1`.

Both are established here, unconditionally, from the landed lattice-ball sandwhich
`TriangleAverage.eventually_pow_div_ncard_le` (`r^d/|B_r| ≤ 2^d`) and `d ≥ 1`. -/

namespace SecondMomentCase3

/-- `r ↦ r^{-d}` is logarithmically integrable: `∫^∞ r^{-d-1} dr < ∞` because `d ≥ 1`. -/
theorem logIntegrable_rpow_neg_self (M : SourceModelData) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => r ^ (-(M.d : ℝ))) := by
  have hlt : -((M.d : ℝ) + 1) < -1 := by
    have : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
    linarith
  have hbase : IntegrableOn (fun r : ℝ => r ^ (-((M.d : ℝ) + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt hlt one_pos
  refine ⟨?_, 1, one_pos, hbase.congr_fun ?_ measurableSet_Ioi⟩
  · fun_prop
  · intro r hr
    change r ^ (-((M.d : ℝ) + 1)) = |r ^ (-(M.d : ℝ))| / r
    have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
    have hpos : (0 : ℝ) < r ^ (-(M.d : ℝ)) := Real.rpow_pos_of_pos hr0 _
    have h1 : -((M.d : ℝ) + 1) = -(M.d : ℝ) - 1 := by ring
    rw [abs_of_pos hpos, h1, Real.rpow_sub hr0, Real.rpow_one]

/-- **The `r^{(c-1)d}` residual is logarithmically integrable** (`c < 1`, `d ≥ 1`). -/
theorem logIntegrable_rpow_mul_rpow_neg_self (M : SourceModelData) {c : ℝ} (hc : c < 1)
    {K : ℝ} (hK : 0 ≤ K) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => K * r ^ ((c - 1) * (M.d : ℝ))) := by
  have hd : (0 : ℝ) < (M.d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one M.hd
  have hlt : (c - 1) * (M.d : ℝ) < 0 := by nlinarith
  have hbase : IntegrableOn (fun r : ℝ => r ^ ((c - 1) * (M.d : ℝ) - 1)) (Set.Ioi 1) := by
    refine integrableOn_Ioi_rpow_of_lt ?_ one_pos
    linarith
  have hmeas : Measurable (fun r : ℝ => K * r ^ ((c - 1) * (M.d : ℝ))) := by fun_prop
  refine ⟨hmeas, 1, one_pos, ?_⟩
  refine IntegrableOn.congr_fun (hbase.const_mul K) ?_ measurableSet_Ioi
  intro r hr
  change K * r ^ ((c - 1) * (M.d : ℝ) - 1) = |K * r ^ ((c - 1) * (M.d : ℝ))| / r
  have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
  have hpos : (0 : ℝ) < r ^ ((c - 1) * (M.d : ℝ)) := Real.rpow_pos_of_pos hr0 _
  have hnn : (0 : ℝ) ≤ K * r ^ ((c - 1) * (M.d : ℝ)) := by positivity
  rw [abs_of_nonneg hnn, mul_div_assoc]
  congr 1
  rw [show (c - 1) * (M.d : ℝ) - 1 = (c - 1) * (M.d : ℝ) + (-1) by ring,
    Real.rpow_add hr0, Real.rpow_neg_one, div_eq_mul_inv]

/-- The tail `r^{(c-1)d}` vanishes for `c < 1`. -/
theorem tendsto_rpow_mul_sub_one (M : SourceModelData) {c : ℝ} (hc : c < 1) {K : ℝ} :
    Tendsto (fun r : ℝ => K * r ^ ((c - 1) * (M.d : ℝ))) atTop (𝓝 0) := by
  have hd : (0 : ℝ) < (M.d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one M.hd
  have hgt : (0 : ℝ) < (1 - c) * (M.d : ℝ) := by nlinarith
  have h := (tendsto_rpow_neg_atTop hgt).const_mul K
  have hexp : (c - 1) * (M.d : ℝ) = -((1 - c) * (M.d : ℝ)) := by ring
  simpa [hexp] using h

/-- **`r ↦ 1/|B_r|` is logarithmically integrable** — the single-origin residual. -/
theorem logIntegrable_inv_ball (M : SourceModelData) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => ((M.ball r).ncard : ℝ)⁻¹) := by
  have hmono : Monotone (fun r : ℝ => ((M.ball r).ncard : ℝ)) := fun a b hab =>
    Nat.cast_le.mpr (Set.ncard_le_ncard (fun _ hy => le_trans hy hab) (BallAverage.ball_finite M b))
  have hmeas : Measurable (fun r : ℝ => ((M.ball r).ncard : ℝ)⁻¹) :=
    (Monotone.measurable hmono).inv
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le_const_mul (K := (2 : ℝ) ^ M.d)
    hmeas (logIntegrable_rpow_neg_self M) (by positivity) ?_
  filter_upwards [TriangleAverage.eventually_pow_div_ncard_le M, eventually_ge_atTop (1 : ℝ)]
    with r hratio hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hnat : (0 : ℝ) < r ^ ((M.d : ℝ)) := Real.rpow_pos_of_pos hr0 _
  have hnc : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast ball_ncard_pos M r hr0.le
  have h2 : r ^ ((M.d : ℝ)) ≤ (2 : ℝ) ^ M.d * ((M.ball r).ncard : ℝ) := by
    rw [Real.rpow_natCast]
    exact (div_le_iff₀ hnc).mp hratio
  have hkey : ((M.ball r).ncard : ℝ)⁻¹ ≤ (2 : ℝ) ^ M.d / r ^ ((M.d : ℝ)) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hnc hnat, one_mul]
    exact h2
  have hrhs : |r ^ (-(M.d : ℝ))| = (r ^ ((M.d : ℝ)))⁻¹ := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hr0 _), Real.rpow_neg hr0.le, Real.rpow_natCast]
  rw [abs_of_pos (inv_pos.mpr hnc), hrhs, ← div_eq_mul_inv]
  exact hkey

/-- **The single-origin residual vanishes.** -/
theorem tendsto_inv_ball (M : SourceModelData) :
    Tendsto (fun r : ℝ => ((M.ball r).ncard : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (TriangleAverage.tendsto_ball_ncard M)

end SecondMomentCase3

/-! ## 4. The repaired window consumer

Replacing the pointwise `hT3` of `connCubeMass_le_of_windowGap` by the window-summed
near/far budget gives the same shape of numerator bound, with the `ℓ = 3` term now split into a
near piece `C₃ A N χ⁴` (not multiplied by `|B_r|`) and a far piece folded into the `|B_r|`
coefficient. -/

namespace SecondMomentCase3

variable (M : SourceModelData)

/-- **Case 3, window assembly with a near/far budget for the `ℓ = 3` term.**

The conclusions is the analogue of `connCubeMass_le_of_windowGap` in which the impossible
pointwise `hT3` has been replaced by the summed hypothesis `hT3`. -/
theorem connCubeMass_le_of_windowGap_nearFar {c C3 C4 Cp A B : ℝ} (N : ℝ → ℝ)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3)
    (hT3 : ∀ r : ℝ, 1 ≤ r →
      ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ A * N r + ((M.ball r).ncard : ℝ) * B)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      C3 * A * N r * (M.cutMassAt r 0).toReal ^ 4
        + (C3 * B + C4 * Cp * M.case3Driver c r) * ((M.ball r).ncard : ℝ)
            * (M.cutMassAt r 0).toReal ^ 4 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hχ : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  rw [M.connCubeMass_toReal_eq_sum_vertex r (hc r hr)]
  have hT3' : ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
      ≤ A * N r + ((E1Sign.ballF M r).card : ℝ) * B := by
    rw [E1Sign.card_ballF M r]
    exact hT3 r hr
  have hmain := sum_perVertex_le_nearFar (s := E1Sign.ballF M r) (F := fun y =>
      (M.connCubeVertexMass r y).toReal)
    (T3 := fun y => I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y)
    (T4 := fun y => I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y)
    (χ := (M.cutMassAt r 0).toReal) (drv := M.case3Driver c r)
    (C3 := C3) (C4 := C4) (Cp := Cp) (A := A) (B := B) (N := N r)
    (hgap r hr) hT3' (fun y _ => hpoly4 r hr y) hC3 hC4 hχ
  calc ∑ y ∈ E1Sign.ballF M r, (M.connCubeVertexMass r y).toReal
      ≤ C3 * A * N r * (M.cutMassAt r 0).toReal ^ 4
        + ((E1Sign.ballF M r).card : ℝ)
            * (C3 * B + C4 * Cp * M.case3Driver c r) * (M.cutMassAt r 0).toReal ^ 4 := hmain
    _ = C3 * A * N r * (M.cutMassAt r 0).toReal ^ 4
        + (C3 * B + C4 * Cp * M.case3Driver c r) * ((M.ball r).ncard : ℝ)
            * (M.cutMassAt r 0).toReal ^ 4 := by
        rw [E1Sign.card_ballF M r]
        ring

end SecondMomentCase3

/-! ## 5. The error-level replacement, with the residual written out

Feeding the repaired numerator bound into the source's ratio `(I.4.16)` produces

  `E_{2,r} ≤ (A/c₃) · N r / |B_r| + (B/c₃) · (∇_{r^c} + r^{-c})`,

i.e. exactly the source's driver bound plus the honest near/origin residual `A N r/|B_r|`.  With
`N ≡ 1` this is the "constant over `|B_r|`" residual of the local origin correction; it is the
only piece that the pointwise `hT3` used to hide. -/

namespace SecondMomentCase3

variable (M : SourceModelData)

/-- **Case 3: the second-moment error with the near/origin residual.** -/
theorem p2ExclError_le_nearFar {c A B r₀ : ℝ} (N : ℝ → ℝ) {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      A * N r * (M.cutMassAt r 0).toReal ^ 4
        + B * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ (A / c3) * (N r / ((M.ball r).ncard : ℝ)) + (B / c3) * M.case3Driver c r := by
  filter_upwards [hnum, hgm, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)]
    with r hn hg hr hr1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have h2r := h2 r hr
  have h1r : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  have hχeq : (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
    rw [M.cutMassAt_zero_eq_cutMoment r]
  have hχ : (0 : ℝ) < (M.cutMassAt r 0).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1r
    rw [hχeq] at this
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2r
    linarith
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr0.le
  have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  have hnum0 : (0 : ℝ) ≤ (M.connCubeMass r).toReal := ENNReal.toReal_nonneg
  have hDpos : (0 : ℝ) < ((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4 := by
    have h4 : (0 : ℝ) < (M.cutMassAt r 0).toReal ^ 4 := by positivity
    positivity
  have hDle : ((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4
      ≤ ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal := by
    have h := mul_le_mul_of_nonneg_left hg (le_of_lt (mul_pos hb hχ))
    have heq : ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal
          * (c3 * (M.cutMassAt r 0).toReal ^ 3)
        = ((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4 := by ring
    linarith [heq.le, heq.ge, h]
  have hstep1 : (M.p2ExclError r) ≤ (M.connCubeMass r).toReal
      / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal) := by
    have h := M.p2ExclError_le_connCubeMass_div r hr0.le h2r (hc r hr1)
    rwa [hχeq] at h
  have hstep2 : (M.connCubeMass r).toReal
      / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal)
      ≤ (M.connCubeMass r).toReal
        / (((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4) :=
    div_le_div_of_nonneg_left hnum0 hDpos hDle
  have hstep3 : (M.connCubeMass r).toReal
      / (((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4)
      ≤ (A / c3) * (N r / ((M.ball r).ncard : ℝ)) + (B / c3) * M.case3Driver c r := by
    refine (div_le_iff₀ hDpos).mpr ?_
    have h1 : A * N r * (M.cutMassAt r 0).toReal ^ 4
        ≤ (A / c3) * (N r / ((M.ball r).ncard : ℝ))
            * (((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4) := by
      have he : (A / c3) * (N r / ((M.ball r).ncard : ℝ))
          * (((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4)
          = A * N r * (M.cutMassAt r 0).toReal ^ 4 := by
        field_simp
      linarith [he.le, he.ge]
    have h2 : B * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4
        ≤ (B / c3) * M.case3Driver c r
            * (((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4) := by
      have he : (B / c3) * M.case3Driver c r
          * (((M.ball r).ncard : ℝ) * c3 * (M.cutMassAt r 0).toReal ^ 4)
          = B * ((M.ball r).ncard : ℝ) * M.case3Driver c r
              * (M.cutMassAt r 0).toReal ^ 4 := by
        field_simp
      linarith [he.le, he.ge]
    linarith [hn, h1, h2]
  linarith [hstep1, hstep2, hstep3]

end SecondMomentCase3

/-! ## 6. The column-sum substitute really is Case-1-only

The alternative `ℓ = 3` input, "`∑_y T^3(0,y) ≤ χ^3`" (the column sum), produces the window bound
`C₃ Cp0 χ⁷ + |B_r| C₄ Cp drv χ⁴` (`sum_perVertex_le_column`).  After the source's division by
`|B_r| χ E|K|² ⪰ c₃ |B_r| χ⁴` this leaves

  `E_{2,r} ≤ (C₃ Cp0 / c₃) · χ³/|B_r| + (C₄ Cp / c₃) · (∇_{r^c} + r^{-c})`.

The second term is the source's driver and is harmless; the first term is not.  In the Case-3
regime (`3α ≥ d`) the first moment satisfies `χ ⪰ r^α` and the window `|B_r| ⪯ r^d`, so
`χ³/|B_r| ⪰ r^{3α-d} ≥ 1`: the residual does not even tend to `0`, let alone being
logarithmically integrable.  Hence the column-sum route can only work when `3α < d`, i.e. exactly
Case 1. -/

namespace SecondMomentCase3

/-- **An abstract non-vanishing criterion.**  If `g r ⪰ c r^a` and `0 < B r ⪯ D r^a` eventually,
then `g r / B r ⪰ c/D > 0` eventually and so `g/B` cannot tend to `0`. -/
theorem not_tendsto_zero_of_rpow_div {g B : ℝ → ℝ} {c D a : ℝ}
    (hc : 0 < c) (hD : 0 < D)
    (hg : ∀ᶠ r : ℝ in atTop, c * r ^ a ≤ g r)
    (hB : ∀ᶠ r : ℝ in atTop, 0 < B r ∧ B r ≤ D * r ^ a) :
    ¬ Tendsto (fun r : ℝ => g r / B r) atTop (𝓝 0) := by
  have hge : ∀ᶠ r : ℝ in atTop, c / D ≤ g r / B r := by
    filter_upwards [hg, hB, eventually_ge_atTop (1 : ℝ)] with r hgr hBr hr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
    have hra : (0 : ℝ) < r ^ a := Real.rpow_pos_of_pos hr0 a
    rw [div_le_div_iff₀ hD hBr.1]
    calc c * B r ≤ c * (D * r ^ a) := mul_le_mul_of_nonneg_left hBr.2 hc.le
      _ = (c * r ^ a) * D := by ring
      _ ≤ g r * D := mul_le_mul_of_nonneg_right hgr hD.le
  intro h0
  have hpos : (0 : ℝ) < c / D := div_pos hc hD
  have hlt : ∀ᶠ r : ℝ in atTop, g r / B r < c / D / 2 :=
    (tendsto_order.1 h0).2 (c / D / 2) (by linarith)
  obtain ⟨r, h1, h2⟩ := (hge.and hlt).exists
  linarith

variable (M : SourceModelData)

/-- **The column-sum residual `χ³/|B_r|` does not vanish when `3α ≥ d`.**

`hP` is the accepted first-moment asymptotic `E_{β_c,r}|K| ~ (α/β_c) r^α`; the ball count
`|B_r| ⪯ r^d` is `SourceModelData.ball_count`.  This is the precise, machine-checked content of
"the `ℓ = 3` column-sum substitute is Case-1-only". -/
theorem columnResidual_not_tendsto_zero (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hdα : (M.d : ℝ) ≤ 3 * M.α) :
    ¬ Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal ^ 3 / ((M.ball r).ncard : ℝ))
        atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := M.ball_count.isBigO.bound
  have hC' : ∀ᶠ r : ℝ in atTop, ((M.ball r).ncard : ℝ) ≤ max C 1 * r ^ ((M.d : ℝ)) := by
    filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with r hr hr0
    have h1 : ‖((M.ball r).ncard : ℝ)‖ ≤ C * ‖r ^ ((M.d : ℝ))‖ := by
      simpa using hr
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hr0 _)] at h1
    refine h1.trans ?_
    have hmono : (0 : ℝ) ≤ r ^ ((M.d : ℝ)) := Real.rpow_nonneg hr0 _
    exact mul_le_mul_of_nonneg_right (le_max_left C 1) hmono
  have hg : ∀ᶠ r : ℝ in atTop,
      (M.α / (M.betaCrit : ℝ) / 2) ^ 3 * r ^ (3 * M.α) ≤ (M.cutMassAt r 0).toReal ^ 3 := by
    have hhalf : ∀ᶠ r : ℝ in atTop,
        (1 / 2 : ℝ) ≤ (M.cutMassAt r 0).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) := by
      have hlt := (tendsto_order.1 hP).1 (1 / 2) (by norm_num)
      filter_upwards [hlt] with r hr
      exact le_of_lt hr
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    have hpos : (0 : ℝ) < (M.α / (M.betaCrit : ℝ)) * r ^ M.α :=
      mul_pos hκ (Real.rpow_pos_of_pos hr0 M.α)
    rw [le_div_iff₀ hpos] at hr
    have hcube : ((M.α / (M.betaCrit : ℝ) / 2) * r ^ M.α) ^ 3
        ≤ (M.cutMassAt r 0).toReal ^ 3 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 3
      nlinarith [hr]
    have hid : ((M.α / (M.betaCrit : ℝ) / 2) * r ^ M.α) ^ 3
        = (M.α / (M.betaCrit : ℝ) / 2) ^ 3 * r ^ (3 * M.α) := by
      rw [mul_pow, ← Real.rpow_natCast (r ^ M.α) 3, ← Real.rpow_mul hr0.le]
      push_cast
      ring_nf
    rwa [hid] at hcube
  have hB : ∀ᶠ r : ℝ in atTop, 0 < ((M.ball r).ncard : ℝ)
      ∧ ((M.ball r).ncard : ℝ) ≤ max C 1 * r ^ (3 * M.α) := by
    filter_upwards [hC', eventually_ge_atTop (1 : ℝ)] with r hr hr1
    refine ⟨by exact_mod_cast ball_ncard_pos M r (le_trans zero_le_one hr1), ?_⟩
    refine hr.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_exponent_le hr1 hdα
  exact not_tendsto_zero_of_rpow_div (c := (M.α / (M.betaCrit : ℝ) / 2) ^ 3)
    (D := max C 1) (a := 3 * M.α) (by positivity)
    (by have h : (1 : ℝ) ≤ max C 1 := le_max_right C 1; linarith)
    hg hB

end SecondMomentCase3

/-! ## 7. The residual as a logarithmic error function

The repaired error bound of Section 5 has the shape `residual + (B/c₃) · driver`.  To conclude
`E_{2,r} → 0` and `E_{2,r}` logarithmically integrable it remains to see that the residual is an
`IsLogErrorFunction`:

* the single-origin residual `A/|B_r|` (Section 7.1);
* the near-count residual `K r^{c d}/|B_r| ⪯ K 2^d r^{(c-1)d}` for `c < 1` (Section 7.2).

Both are `→ 0` and logarithmically integrable, so the presence of the residual costs nothing —
in sharp contrast to the `χ³/|B_r|` of Section 6. -/

namespace SecondMomentCase3

variable (M : SourceModelData)

/-- **The near-count residual vanishes.**  `N r ⪯ K r^{c d}` window vertices of distance `< r^c`,
divided by `|B_r| ⪰ r^d`, leave `⪯ K 2^d r^{(c-1)d} → 0` when `c < 1`. -/
theorem tendsto_nearCount_ratio {c K : ℝ} (hc : c < 1) (hK : 0 ≤ K) :
    Tendsto (fun r : ℝ => K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_rpow_mul_sub_one M hc (K := (2 : ℝ) ^ M.d * K)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
    exact div_nonneg (by positivity) (by exact_mod_cast Nat.zero_le _)
  · filter_upwards [TriangleAverage.eventually_pow_div_ncard_le M, eventually_ge_atTop (1 : ℝ)]
      with r hratio hr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
    have hnat : (0 : ℝ) < r ^ ((M.d : ℝ)) := Real.rpow_pos_of_pos hr0 _
    have hnc : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
      exact_mod_cast ball_ncard_pos M r hr0.le
    have h2 : r ^ ((M.d : ℝ)) ≤ (2 : ℝ) ^ M.d * ((M.ball r).ncard : ℝ) := by
      rw [Real.rpow_natCast]
      exact (div_le_iff₀ hnc).mp hratio
    have hinv : ((M.ball r).ncard : ℝ)⁻¹ ≤ (2 : ℝ) ^ M.d * (r ^ ((M.d : ℝ)))⁻¹ := by
      rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hnc hnat, one_mul]
      exact h2
    have hexp : c * (M.d : ℝ) + (-(M.d : ℝ)) = (c - 1) * (M.d : ℝ) := by ring
    have hrpow : r ^ (c * (M.d : ℝ)) * (r ^ ((M.d : ℝ)))⁻¹ = r ^ ((c - 1) * (M.d : ℝ)) := by
      rw [← Real.rpow_neg hr0.le, ← Real.rpow_add hr0, hexp]
    calc K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ)
        = K * r ^ (c * (M.d : ℝ)) * ((M.ball r).ncard : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ K * r ^ (c * (M.d : ℝ)) * ((2 : ℝ) ^ M.d * (r ^ ((M.d : ℝ)))⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 : ℝ) ^ M.d * (K * (r ^ (c * (M.d : ℝ)) * (r ^ ((M.d : ℝ)))⁻¹)) := by ring
      _ = (2 : ℝ) ^ M.d * K * r ^ ((c - 1) * (M.d : ℝ)) := by rw [hrpow]; ring

/-- **The near-count residual is logarithmically integrable.** -/
theorem logIntegrable_nearCount_ratio {c K : ℝ} (hc : c < 1) (hK : 0 ≤ K) :
    Analysis.LogarithmicallyIntegrable
      (fun r : ℝ => K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ)) := by
  have hmono : Monotone (fun r : ℝ => ((M.ball r).ncard : ℝ)) := fun a b hab =>
    Nat.cast_le.mpr (Set.ncard_le_ncard (fun _ hy => le_trans hy hab) (BallAverage.ball_finite M b))
  have hmeas : Measurable (fun r : ℝ => K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ)) :=
    (by fun_prop : Measurable fun r : ℝ => K * r ^ (c * (M.d : ℝ))).div
      (Monotone.measurable hmono)
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le_const_mul
    (K := (2 : ℝ) ^ M.d) hmeas
    (logIntegrable_rpow_mul_rpow_neg_self M hc (K := K) hK) (by positivity) ?_
  filter_upwards [TriangleAverage.eventually_pow_div_ncard_le M, eventually_ge_atTop (1 : ℝ)]
    with r hratio hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hnat : (0 : ℝ) < r ^ ((M.d : ℝ)) := Real.rpow_pos_of_pos hr0 _
  have hnc : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast ball_ncard_pos M r hr0.le
  have h2 : r ^ ((M.d : ℝ)) ≤ (2 : ℝ) ^ M.d * ((M.ball r).ncard : ℝ) := by
    rw [Real.rpow_natCast]
    exact (div_le_iff₀ hnc).mp hratio
  have hinv : ((M.ball r).ncard : ℝ)⁻¹ ≤ (2 : ℝ) ^ M.d * (r ^ ((M.d : ℝ)))⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hnc hnat, one_mul]
    exact h2
  have hexp : c * (M.d : ℝ) + (-(M.d : ℝ)) = (c - 1) * (M.d : ℝ) := by ring
  have hrpow : r ^ (c * (M.d : ℝ)) * (r ^ ((M.d : ℝ)))⁻¹ = r ^ ((c - 1) * (M.d : ℝ)) := by
    rw [← Real.rpow_neg hr0.le, ← Real.rpow_add hr0, hexp]
  have hnn : (0 : ℝ) ≤ K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ) := by positivity
  have hright : (0 : ℝ) ≤ K * r ^ ((c - 1) * (M.d : ℝ)) := by positivity
  rw [abs_of_nonneg hnn, abs_of_nonneg hright]
  calc K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ)
      = K * r ^ (c * (M.d : ℝ)) * ((M.ball r).ncard : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ K * r ^ (c * (M.d : ℝ)) * ((2 : ℝ) ^ M.d * (r ^ ((M.d : ℝ)))⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (2 : ℝ) ^ M.d * (K * r ^ ((c - 1) * (M.d : ℝ))) := by
        rw [← hrpow]; ring

/-- **The single-origin residual plus the source's driver is a logarithmic error function.** -/
theorem isLogErrorFunction_invBall_add_driver {c A B c3 : ℝ}
    (hdrv : Analysis.IsLogErrorFunction (M.case3Driver c)) :
    Analysis.IsLogErrorFunction
      (fun r : ℝ => (A / c3) * ((M.ball r).ncard : ℝ)⁻¹ + (B / c3) * M.case3Driver c r) :=
  ⟨VolumeMoments.FirstMoment.logIntegrable_add
      (VolumeMoments.FirstMoment.logIntegrable_const_mul _ (logIntegrable_inv_ball M))
      (VolumeMoments.FirstMoment.logIntegrable_const_mul _ hdrv.1),
    by
      have h := ((tendsto_inv_ball M).const_mul (A / c3)).add (hdrv.2.const_mul (B / c3))
      simpa using h⟩

/-- **The near-count residual plus the source's driver is a logarithmic error function.** -/
theorem isLogErrorFunction_nearCount_add_driver {c K A B c3 : ℝ} (hc : c < 1) (hK : 0 ≤ K)
    (hdrv : Analysis.IsLogErrorFunction (M.case3Driver c)) :
    Analysis.IsLogErrorFunction
      (fun r : ℝ => A * (K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ))
        + (B / c3) * M.case3Driver c r) :=
  ⟨VolumeMoments.FirstMoment.logIntegrable_add
      (VolumeMoments.FirstMoment.logIntegrable_const_mul _
        (logIntegrable_nearCount_ratio M hc hK))
      (VolumeMoments.FirstMoment.logIntegrable_const_mul _ hdrv.1),
    by
      have h := ((tendsto_nearCount_ratio M hc hK).const_mul A).add
        (hdrv.2.const_mul (B / c3))
      simpa using h⟩

end SecondMomentCase3

/-! ## 8. The exact near/far split of the `ℓ = 3` window sum

This is the bridge that makes the repaired consumer usable.  Lemma I.4.18's own proof splits
`∑_y` at radius `R`; applied to the `ℓ = 3` window sum at `R = r^c` it reads

  `∑_{y ∈ B_r} T^3(0,y) ≤ A · #{y ∈ B_r : ‖y‖ < r^c} + B · |B_r|`,

where `A` is the **constant** near bound (the honest local origin correction — the landed
`I418C.source_polyK_three_le_triSelf` supplies `A = M.triSelf`) and `B` is the **vanishing** far
factor.  Nothing is assumed about the near vertices beyond a uniform constant, and the near set
enters only through its cardinality, which is `⪯ r^{c d}` with `c < 1` — exactly the `N` of the
repaired budget. -/

namespace SecondMomentCase3

variable (M : SourceModelData)

/-- **The near/far split of the `ℓ = 3` window sum.** -/
theorem sum_polyK_three_le_nearFar (r c : ℝ) {A B : ℝ}
    (hnear : ∀ y : M.V, ¬ (r ^ c ≤ M.S.dist 0 y) →
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ A)
    (hfar : ∀ y : M.V, r ^ c ≤ M.S.dist 0 y →
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ B)
    (hB : 0 ≤ B) :
    ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
      ≤ A * (((E1Sign.ballF M r).filter (fun y => ¬ (r ^ c ≤ M.S.dist 0 y))).card : ℝ)
        + B * ((M.ball r).ncard : ℝ) := by
  classical
  set s := E1Sign.ballF M r with hs
  set p : M.V → Prop := fun y => r ^ c ≤ M.S.dist 0 y with hp
  have hsplit : ∑ y ∈ s, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
      = (∑ y ∈ s.filter p, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y)
        + ∑ y ∈ s.filter (fun y => ¬ p y), I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hnear' : ∑ y ∈ s.filter (fun y => ¬ p y),
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
      ≤ A * (((s.filter (fun y => ¬ p y)).card : ℝ)) := by
    calc ∑ y ∈ s.filter (fun y => ¬ p y), I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ ∑ _y ∈ s.filter (fun y => ¬ p y), A :=
          Finset.sum_le_sum fun y hy => hnear y (Finset.mem_filter.mp hy).2
      _ = A * (((s.filter (fun y => ¬ p y)).card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hfar' : ∑ y ∈ s.filter p, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
      ≤ ((M.ball r).ncard : ℝ) * B := by
    have h1 : ∑ y ∈ s.filter p, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ ∑ _y ∈ s.filter p, B := Finset.sum_le_sum fun y hy => hfar y (Finset.mem_filter.mp hy).2
    have h2 : ∑ _y ∈ s.filter p, B = (((s.filter p).card : ℝ)) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (((s.filter p).card : ℝ)) ≤ ((M.ball r).ncard : ℝ) := by
      have hle : s.filter p ⊆ s := Finset.filter_subset _ _
      have := Finset.card_le_card hle
      rw [hs, E1Sign.card_ballF M r] at this
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right h3 hB
    linarith [h1, h2.le, h2.ge, this]
  rw [hsplit]
  nlinarith [hnear', hfar']

end SecondMomentCase3

/-! ## 9. The repaired Case-3 conclusion

With the near-count residual in place, the source's two conclusions for `E_{2,r}` — vanishing and
logarithmic integrability — follow exactly as before; the near-count residual is harmless, so the
repair costs nothing downstream.  These are the consumer-side replacements for
`p2ExclError_tendsto_zero_of_case3` and `logIntegrable_p2ExclError_of_case3`. -/

namespace SecondMomentCase3

variable (M : SourceModelData)

/-- **Case 3, repaired: `E_{2,r} → 0`.**  Same conclusion as
`p2ExclError_tendsto_zero_of_case3`, with the impossible pointwise `ℓ = 3` input replaced by the
near-count budget `A · K r^{c d}` + `B · |B_r| · (∇_{r^c}+r^{-c})`. -/
theorem p2ExclError_tendsto_zero_of_case3_repaired {c K A B r₀ : ℝ} (hK : 0 ≤ K) (hc1 : c < 1)
    {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcm : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      A * (K * r ^ (c * (M.d : ℝ))) * (M.cutMassAt r 0).toReal ^ 4
        + B * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hle := p2ExclError_le_nearFar M (N := fun r : ℝ => K * r ^ (c * (M.d : ℝ)))
    (A := A) (B := B) hc3 h2 hcm hnum hgm
  have hres : Tendsto (fun r : ℝ =>
      (A / c3) * (K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_nearCount_ratio M hc1 hK).const_mul (A / c3)
    simpa using h
  have hdrv' : Tendsto (fun r : ℝ => (B / c3) * M.case3Driver c r) atTop (𝓝 0) := by
    have h := hdrv.const_mul (B / c3)
    simpa using h
  have hsum : Tendsto (fun r : ℝ =>
      (A / c3) * (K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ))
        + (B / c3) * M.case3Driver c r) atTop (𝓝 0) := by
    have h := hres.add hdrv'
    simpa using h
  refine squeeze_zero' ?_ hle hsum
  filter_upwards [eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  exact M.p2ExclError_nonneg r (le_trans zero_le_one hr1) (h2 r hr)

/-- **Case 3, repaired: `E_{2,r}` is logarithmically integrable.**  Same conclusion as
`logIntegrable_p2ExclError_of_case3`, with the near-count budget instead of the pointwise `ℓ = 3`
bound. -/
theorem logIntegrable_p2ExclError_of_case3_repaired {c K A B r₀ : ℝ}
    (hmeas : Measurable M.p2ExclError) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc1 : c < 1)
    {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcm : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      A * (K * r ^ (c * (M.d : ℝ))) * (M.cutMassAt r 0).toReal ^ 4
        + B * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Analysis.IsLogErrorFunction (M.case3Driver c)) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  have hle := p2ExclError_le_nearFar M (N := fun r : ℝ => K * r ^ (c * (M.d : ℝ)))
    (A := A) (B := B) hc3 h2 hcm hnum hgm
  have hdom := (isLogErrorFunction_nearCount_add_driver M (c := c) (K := K) (A := A / c3)
    (B := B) (c3 := c3) hc1 hK hdrv).1
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le hmeas hdom ?_
  filter_upwards [hle, eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hb hr hr1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hE0 : (0 : ℝ) ≤ M.p2ExclError r :=
    M.p2ExclError_nonneg r (le_trans zero_le_one hr1) (h2 r hr)
  have hN0 : (0 : ℝ) ≤ K * r ^ (c * (M.d : ℝ)) := by positivity
  have hb0 : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := by positivity
  have hd0 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
  have hh0 : (0 : ℝ) ≤ (A / c3) * (K * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ))
      + (B / c3) * M.case3Driver c r :=
    add_nonneg (mul_nonneg (div_nonneg hA hc3.le) (div_nonneg hN0 hb0))
      (mul_nonneg (div_nonneg hB hc3.le) hd0)
  rw [abs_of_nonneg hE0, abs_of_nonneg hh0]
  exact hb

end SecondMomentCase3

/-! ## 10. The `ℓ = 3` window budget, discharged from the landed near/far split

`I420Case3.sum_polyK_three_le_near_far` (landed) states, for a finite window `B` and any finite
`near ⊆ B` covering the far part,

  `∑_{y ∈ B} T^3(0,y) ≤ |B| · (∇_R) + |near| · ∇`

with `∇ = M.triSelf` the *uncut* triangle and `(M.nablaTail R).toReal` its sup-tail.  Taken with
`R = r^c` this is exactly the repaired budget: the far factor is the first half of
`case3Driver c r`, and the near factor is the constant `M.triSelf` charged `|near|` times.

The only remaining geometric input is the number of near window vertices,
`#{y ∈ B_r : ‖y‖ < r^c} ⪯ r^{c d}`; `nearFilter_card_le_ball_ncard` shows it is at most
`|B_{r^c}|`, and `SourceModelData.ball_count` gives `|B_ρ| ≈ ρ^d`, so it holds with `c d` — but
the final counting step is carried as an explicit hypothesis below rather than reproved. -/

namespace SecondMomentCase3

variable (M : SourceModelData)

/-- The uncut triangle at the origin is nonnegative. -/
theorem triSelf_nonneg : (0 : ℝ) ≤ M.triSelf := by
  have h : M.triSelf
      = (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 0).toReal :=
    rfl
  rw [h]
  exact ENNReal.toReal_nonneg

/-- In the model's norm, `dist 0 y = ‖y‖` (`ρ (-v) = ρ v`), so `M.ball r` is the `dist`-ball. -/
theorem dist_zero_eq (y : M.V) : M.S.dist 0 y = M.S.ρ (toVec y) := by
  change M.S.ρ (toVec ((0 : M.V) - y)) = M.S.ρ (toVec y)
  have h : toVec ((0 : M.V) - y) = -toVec y := by
    funext i
    simp [toVec]
  rw [h, M.S.ρ_neg]

/-- The near part of a window is contained in the ball of radius `R`. -/
theorem nearFilter_card_le_ball_ncard (r R : ℝ) :
    (((E1Sign.ballF M r).filter (fun y => ¬ (R ≤ M.S.dist 0 y))).card)
      ≤ (M.ball R).ncard := by
  classical
  have hsub : (E1Sign.ballF M r).filter (fun y => ¬ (R ≤ M.S.dist 0 y))
      ⊆ TriangleAverage.ballFinset M R := by
    intro y hy
    obtain ⟨-, hy2⟩ := Finset.mem_filter.mp hy
    refine (Set.Finite.mem_toFinset (BallAverage.ball_finite M R)).mpr ?_
    change M.S.ρ (toVec y) ≤ R
    rw [← dist_zero_eq M y]
    exact le_of_lt (not_le.mp hy2)
  have h1 := Finset.card_le_card hsub
  rwa [TriangleAverage.ballFinset_card] at h1

/-- **The repaired `ℓ = 3` window budget**, from the landed near/far split. -/
theorem polyK_three_window_budget (r R : ℝ)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
      ≤ M.triSelf * (((E1Sign.ballF M r).filter (fun y => ¬ (R ≤ M.S.dist 0 y))).card : ℝ)
        + ((M.ball r).ncard : ℝ) * (M.nablaTail R).toReal := by
  have hfar : ∀ y ∈ E1Sign.ballF M r,
      y ∉ (E1Sign.ballF M r).filter (fun y => ¬ (R ≤ M.S.dist 0 y)) → R ≤ M.S.dist 0 y := by
    intro y hyB hys
    by_contra hlt
    exact hys (Finset.mem_filter.mpr ⟨hyB, hlt⟩)
  have h := PercLib.CriticalLRP.I420Case3.sum_polyK_three_le_near_far M r R
    (E1Sign.ballF M r) ((E1Sign.ballF M r).filter (fun y => ¬ (R ≤ M.S.dist 0 y))) hfar hTri
  rw [← E1Sign.card_ballF M r]
  linarith [h]

/-- **The Case-3 second-moment error from the per-vertex gap and the near-count only.**

This is the consumer-side capstone: the impossible pointwise `ℓ = 3` hypothesis `hT3` is gone.
What remains is
* `hgap` — Lemma I.4.17 at `p = 3`, `q = 0` (the genuine remaining numerator input);
* the `ℓ = 4` polygon bound `hpoly4` (`exists_polygon_bound_four`, landed);
* the near-count `hcount` (bounded geometry, see the header of this section).

The conclusion has the source's driver plus the *harmless* near-count residual. -/
theorem p2ExclError_le_case3_nearCount {c C3 C4 Cp Kc r₀ : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcm : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3)
    (hcount : ∀ᶠ r : ℝ in atTop,
      (((E1Sign.ballF M r).filter (fun y => ¬ (r ^ c ≤ M.S.dist 0 y))).card : ℝ)
        ≤ Kc * r ^ (c * (M.d : ℝ)))
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ (C3 * M.triSelf / c3) * (Kc * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ))
        + ((C3 + C4 * Cp) / c3) * M.case3Driver c r := by
  have hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      (C3 * M.triSelf) * (Kc * r ^ (c * (M.d : ℝ))) * (M.cutMassAt r 0).toReal ^ 4
        + (C3 + C4 * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hcount] with r hr hcnt
    have hχ : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
    have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
    have hfar : (M.nablaTail (r ^ c)).toReal ≤ M.case3Driver c r := by
      simp only [SourceModelData.case3Driver]
      linarith [Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hr) (-c)]
    rw [M.connCubeMass_toReal_eq_sum_vertex r (hcm r hr)]
    have hT3' : ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ M.triSelf * (Kc * r ^ (c * (M.d : ℝ)))
          + ((E1Sign.ballF M r).card : ℝ) * (M.nablaTail (r ^ c)).toReal := by
      have hb := polyK_three_window_budget M r (r ^ c) hTri
      have hc' := hcnt
      have hcardR : ((E1Sign.ballF M r).card : ℝ) = ((M.ball r).ncard : ℝ) := by
        rw [E1Sign.card_ballF M r]
      rw [hcardR]
      nlinarith [hb, mul_le_mul_of_nonneg_left hc' (triSelf_nonneg M)]
    have hmain := sum_perVertex_le_nearFar (s := E1Sign.ballF M r)
      (F := fun y => (M.connCubeVertexMass r y).toReal)
      (T3 := fun y => I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y)
      (T4 := fun y => I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y)
      (χ := (M.cutMassAt r 0).toReal) (drv := M.case3Driver c r)
      (C3 := C3) (C4 := C4) (Cp := Cp) (A := M.triSelf)
      (B := (M.nablaTail (r ^ c)).toReal) (N := Kc * r ^ (c * (M.d : ℝ)))
      (hgap r hr) hT3' (fun y _ => hpoly4 r hr y) hC3 hC4 hχ
    calc ∑ y ∈ E1Sign.ballF M r, (M.connCubeVertexMass r y).toReal
        ≤ C3 * M.triSelf * (Kc * r ^ (c * (M.d : ℝ))) * (M.cutMassAt r 0).toReal ^ 4
          + ((E1Sign.ballF M r).card : ℝ)
              * (C3 * (M.nablaTail (r ^ c)).toReal + C4 * Cp * M.case3Driver c r)
              * (M.cutMassAt r 0).toReal ^ 4 := hmain
      _ ≤ (C3 * M.triSelf) * (Kc * r ^ (c * (M.d : ℝ))) * (M.cutMassAt r 0).toReal ^ 4
          + (C3 + C4 * Cp) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
              * (M.cutMassAt r 0).toReal ^ 4 := by
          rw [E1Sign.card_ballF M r]
          have h4 : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal ^ 4 := by positivity
          have hb : ((M.ball r).ncard : ℝ) * (C3 * (M.nablaTail (r ^ c)).toReal
              + C4 * Cp * M.case3Driver c r)
              ≤ ((M.ball r).ncard : ℝ) * ((C3 + C4 * Cp) * M.case3Driver c r) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [hfar, hC3, hdrv]
          have := mul_le_mul_of_nonneg_right hb h4
          linarith [this]
  exact p2ExclError_le_nearFar M (A := C3 * M.triSelf) (B := C3 + C4 * Cp)
    (N := fun r : ℝ => Kc * r ^ (c * (M.d : ℝ))) hc3 h2 hcm hnum hgm

end SecondMomentCase3


/-! ## Axiom audit -/

set_option linter.hashCommand false

namespace SecondMomentCase3

#print axioms sum_perVertex_le_nearFar
#print axioms sum_perVertex_le_origin
#print axioms sum_perVertex_le_column
#print axioms not_pointwise_polyK_three_of_driver_tendsto_zero
#print axioms hcase3_unsatisfiable
#print axioms logIntegrable_inv_ball
#print axioms connCubeMass_le_of_windowGap_nearFar
#print axioms p2ExclError_le_nearFar
#print axioms columnResidual_not_tendsto_zero
#print axioms tendsto_nearCount_ratio
#print axioms logIntegrable_nearCount_ratio
#print axioms isLogErrorFunction_nearCount_add_driver
#print axioms p2ExclError_tendsto_zero_of_case3_repaired
#print axioms logIntegrable_p2ExclError_of_case3_repaired
#print axioms polyK_three_window_budget
#print axioms nearFilter_card_le_ball_ncard
#print axioms p2ExclError_le_case3_nearCount

/-- **The ball-count upper bound** used by the near-count estimate. -/
theorem exists_ball_ncard_le_rpow :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in atTop,
      ((M.ball r).ncard : ℝ) ≤ K * r ^ ((M.d : ℝ)) := by
  obtain ⟨C, hC⟩ := M.ball_count.isBigO.bound
  refine ⟨max C 1, (lt_of_lt_of_le zero_lt_one (le_max_right C 1)).le, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  have h1 : ‖((M.ball r).ncard : ℝ)‖ ≤ C * ‖r ^ ((M.d : ℝ))‖ := by simpa using hr
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hr0 _)] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.rpow_nonneg hr0 _))

/-- **The near window has `⪯ r^{c d}` vertices.**  `nearFilter_card_le_ball_ncard` bounds the near
part by `|B_{r^c}|` and `exists_ball_ncard_le_rpow` at radius `r^c` gives `|B_{r^c}| ⪯ (r^c)^d =
r^{c d}`. -/
theorem exists_nearCount_bound (c : ℝ) (hc : 0 < c) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ r : ℝ in atTop,
      (((E1Sign.ballF M r).filter (fun y => ¬ (r ^ c ≤ M.S.dist 0 y))).card : ℝ)
        ≤ Kc * r ^ (c * (M.d : ℝ)) := by
  obtain ⟨K, hK, hKb⟩ := exists_ball_ncard_le_rpow M
  have hKc : ∀ᶠ r : ℝ in atTop,
      ((M.ball (r ^ c)).ncard : ℝ) ≤ K * (r ^ c) ^ ((M.d : ℝ)) :=
    (tendsto_rpow_atTop hc).eventually hKb
  refine ⟨K, hK, ?_⟩
  filter_upwards [hKc, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have h1 : (((E1Sign.ballF M r).filter (fun y => ¬ (r ^ c ≤ M.S.dist 0 y))).card : ℝ)
      ≤ ((M.ball (r ^ c)).ncard : ℝ) := by
    exact_mod_cast nearFilter_card_le_ball_ncard M r (r ^ c)
  refine h1.trans ?_
  rw [Real.rpow_mul hr0.le]
  exact hr

/-- **The Case-3 second-moment error with no smoothness input beyond the per-vertex gap.**

Same as `p2ExclError_le_case3_nearCount`, with the near-count hypothesis eliminated via
`exists_nearCount_bound`.  The remaining inputs are `hTri : ∇ < ∞`, the per-vertex Lemma I.4.17 at
`p = 3`, `q = 0` (`hgap`), the landed `ℓ = 4` polygon bound, and the moment gap. -/
theorem p2ExclError_le_case3_of_tri {c C3 C4 Cp r₀ : ℝ} (hc : 0 < c) (_hc1 : c < 1)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcm : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ r : ℝ in atTop, M.p2ExclError r
      ≤ (C3 * M.triSelf / c3) * (Kc * r ^ (c * (M.d : ℝ)) / ((M.ball r).ncard : ℝ))
        + ((C3 + C4 * Cp) / c3) * M.case3Driver c r := by
  obtain ⟨Kc, hKc, hcnt⟩ := exists_nearCount_bound M c hc
  exact ⟨Kc, hKc, p2ExclError_le_case3_nearCount M hC3 hC4 hTri hc3 h2 hcm hgap hcnt
    hpoly4 hgm⟩
#print axioms exists_ball_ncard_le_rpow
#print axioms exists_nearCount_bound
#print axioms p2ExclError_le_case3_of_tri

end SecondMomentCase3

end SourceModelData

end Orchestration

end CriticalLRP

end PercLib
