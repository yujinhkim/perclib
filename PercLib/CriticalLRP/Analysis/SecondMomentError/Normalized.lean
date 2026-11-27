/-
Integrated and independently rebuilt from accepted Ultramath `smwytmnfc`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwytmnfc`, member `m2`, direction d1, integrated at production base
`1ec5a682a47b12ced34931ce440a902cc4924184`.

# (I.4.14) and (I.4.15) at the source cutoff moments, and the error reduction

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15:

```
  d/dr E_{β_c,r}|K|² = 3 (1 − E_{2,r}) β_c |J'(r)| |B_r| E|K| E|K|²              (I.4.14)
                     = 3 α (1 − Ē_{2,r}) r⁻¹ E_{β_c,r}|K|²                        (I.4.15)
```

with `1 − Ē_{2,r} = (1 − E_{2,r})(1 + H_r)(1 − E_{0,r})`.

## What is proved here

`Defs.p2ExclError` is `E_{2,r}` and `Defs.p2Ebar` is `Ē_{2,r}`.

* `p2ExclMass_eq_window_mul_one_sub` — the excluded window mass *is* `|B_r| E|K| E|K|² (1−E_{2,r})`:
  the paper's pivot identity at `p = 2`, in `ℝ`;
* `p2Flux_eq_fourteen` — (I.4.14): the derivative value is
  `3(1−E_{2,r}) β_c |J'(r)| |B_r| E|K| E|K|²`;
* `p2H_normalizes` — `E|K| = (α/β_c) r^α (1 + H_r)`, i.e. `H_r` is the *exact* normalized
  first-moment deviation, not a bounded comparison;
* `p2Flux_eq_fifteen` — (I.4.15), obtained by instantiating the existing scalar normalization
  identity `VolumeMoments.second_moment_ODE_of_pivot`;
* `rhsScalarTwo_eq_p2Flux` — the two spellings of `β_c|J'(r)|` agree (`K' ≤ 0` is the antitone
  kernel's sign);
* `p2Ebar_tendsto_zero` — `Ē_{2,r} → 0` follows from the three *source* inputs `E_{2,r} → 0`,
  `H_r → 0`, `E_{0,r} → 0`; none of them is derived here, and in particular `E_{2,r} → 0` is
  **not** deduced from the boundedness (I.4.16) provides;
* `ratio_tendsto_one` and `regularlyVarying_two` — the ratio form
  `t · rhsScalarTwo t / (3α E_{β_c,t}|K|²) → 1` consumed by
  `SecondMomentRV.secondMoment_regularlyVarying_of_rhs`, and hence regular variation of index `3α`.

The remaining model-side obligations are exactly the ones named as hypotheses: the a.e. radial
identity (`hae`) with absolute continuity on compact windows (`hac`), measurability of `K'`-built
objects (`hmR`) and of the moment (`hmf`), and the three asymptotics `hE2`, `hH`, `hE0`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentError.Bounds
public import PercLib.CriticalLRP.Analysis.SecondMomentRV
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.TailLower

/-! # Second-moment error: Normalized -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

open SecondMomentError
open PercLib.CriticalLRP.Analysis

variable (M : SourceModelData)

/-! ## The `p = 2` pivot identity: `E[|K|∑1(y∉K)|K_y|²] = |B_r| E|K| E|K|² (1 − E_{2,r})` -/

/-- `(M.exclMassQuad r).toReal = |B_r| E|K| E|K|² (1 − E_{2,r})`: the numerator identity behind
(I.4.14), under the two finiteness hypotheses that make the moments real. -/
theorem p2ExclMass_eq_window_mul_one_sub (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (M.exclMassQuad r).toReal
      = ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal
        * (1 - M.p2ExclError r) := by
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2
    linarith
  have hden : ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
      * (M.cutMoment 2 r).toReal ≠ 0 := ne_of_gt (by positivity)
  simp only [p2ExclError, VolumeMoments.cE2]
  field_simp
  ring

/-! ## (I.4.14) -/

/-- The (I.4.14) derivative value is `3 β_c |J'(r)|` times the excluded window mass. -/
theorem p2Flux_eq_three_mul_exclMassQuad (r : ℝ) :
    M.p2Flux r = 3 * (M.betaCrit : ℝ) * |deriv M.K r| * (M.exclMassQuad r).toReal := by
  simp only [p2Flux]
  rw [M.p2RHS_toReal_eq_three_mul r]
  ring

/-- **Display (I.4.14)** at the source cutoff moments:
`d/dr E|K|² = 3 (1 − E_{2,r}) β_c |J'(r)| |B_r| E|K| E|K|²`. -/
theorem p2Flux_eq_fourteen (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.p2Flux r = 3 * (1 - M.p2ExclError r) * (M.betaCrit : ℝ) * |deriv M.K r|
      * ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
  rw [M.p2Flux_eq_three_mul_exclMassQuad r, M.p2ExclMass_eq_window_mul_one_sub r hr h2]
  ring

/-! ## The first-moment normalization `E|K| = (α/β_c) r^α (1 + H_r)` -/

/-- `H_r` is exactly the normalized deviation of the first cutoff moment: the identity
`E|K| = (α/β_c) r^α (1 + H_r)` of Section I.4.1 holds as a *definition* of `H_r`, given the
positivity of `α`, `β_c` and `r` that makes the normalizing constant non-zero. -/
theorem p2H_normalizes (r : ℝ) (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0) (hr : 0 < r) :
    (M.cutMoment 1 r).toReal = (M.α / (M.betaCrit : ℝ)) * r ^ M.α * (1 + M.p2H r) := by
  have hc : (M.α / (M.betaCrit : ℝ)) * r ^ M.α ≠ 0 :=
    mul_ne_zero (div_ne_zero (ne_of_gt hα) hβ) (Real.rpow_pos_of_pos hr M.α).ne'
  simp only [p2H]
  field_simp
  ring

/-! ## (I.4.15), via the accepted scalar normalization identity -/

/-- **Display (I.4.15)** at the source cutoff moments:

`d/dr E|K|² = 3 α (1 − Ē_{2,r}) r⁻¹ E_{β_c,r}|K|²`.

Obtained by instantiating `VolumeMoments.second_moment_ODE_of_pivot` — the accepted passage
(I.4.14) ⟹ (I.4.15) — at the model's moments, with `H = H_r` supplied by `p2H_normalizes` and
`E_{2,r}` supplied by the source definition; the second-moment error enters only through
`1 − Ē_{2,r} = (1 − E_{2,r})(1 + H_r)(1 − E_{0,r})`. -/
theorem p2Flux_eq_fifteen (r : ℝ) (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0) (hr : 0 < r)
    (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.p2Flux r = 3 * M.α * (1 - M.p2Ebar r) * r ^ (-1 : ℝ) * (M.cutMoment 2 r).toReal := by
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr.le
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := M.one_le_cutMoment_one_toReal r h1
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two_toReal r h2
    linarith
  have hAr := M.p2H_normalizes r hα hβ hr
  have hkey := VolumeMoments.second_moment_ODE_of_pivot
    (A := (M.cutMoment 1 r).toReal) (A2 := (M.cutMoment 2 r).toReal)
    (U := (M.exclMassQuad r).toReal) (b := ((M.ball r).ncard : ℝ))
    (J := |deriv M.K r|) (β := (M.betaCrit : ℝ)) (r := r) (α := M.α) (H := M.p2H r)
    hA hA2 hb hr hβ hAr
  rw [M.p2Flux_eq_three_mul_exclMassQuad r, hkey]
  simp only [p2ExclError, p2Ebar]
  ring

/-! ## The two spellings of the derivative value -/

/-- `M.rhsScalarTwo` is the same real number as `M.p2Flux` for a decreasing kernel: the source's
`β_c(-K'(r))` is `β_c|K'(r)|`.  This is the only place where the sign of `K'` is used. -/
theorem rhsScalarTwo_eq_p2Flux (r : ℝ) (hr : 0 < r) :
    M.rhsScalarTwo r = M.p2Flux r := by
  simp only [SourceModelData.rhsScalarTwo, SourceModelData.coeffRHS, p2Flux,
    abs_of_nonpos (M.deriv_K_nonpos hr)]

/-- **(I.4.14) in `rhsScalarTwo` vocabulary** — the form in which the a.e. radial derivative of
`r ↦ E_{β_c,r}|K|²` is available: the derivative value is
`3(1 − E_{2,r}) β_c |J'(r)| |B_r| E|K| E|K|²`. -/
theorem rhsScalarTwo_eq_fourteen (r : ℝ) (hr : 0 < r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.rhsScalarTwo r = 3 * (1 - M.p2ExclError r) * (M.betaCrit : ℝ) * |deriv M.K r|
      * ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
  rw [M.rhsScalarTwo_eq_p2Flux r hr, M.p2Flux_eq_fourteen r hr.le h2]

/-- **(I.4.15) in `rhsScalarTwo` vocabulary**:
`d/dr E|K|² = 3α (1 − Ē_{2,r}) r⁻¹ E_{β_c,r}|K|²`. -/
theorem rhsScalarTwo_eq_fifteen (r : ℝ) (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤) :
    M.rhsScalarTwo r = 3 * M.α * (1 - M.p2Ebar r) * r ^ (-1 : ℝ)
      * (M.cutMoment 2 r).toReal := by
  rw [M.rhsScalarTwo_eq_p2Flux r hr, M.p2Flux_eq_fifteen r hα hβ hr h1 h2]

/-! ## `H_r` is exactly the first-moment asymptotic `hP`

`M.p2H r = E|K| / ((α/β_c) r^α) − 1`, so `H_r → 0` is *the same statement* as the normalized
first-moment asymptotic `E_{β_c,r}|K| ∼ (α/β_c) r^α` (the accepted `hP` of
`Analysis/MomentRegularVariation.lean`).  Both directions are recorded, so that `hH` below can be
discharged by `hP` without any additional hypothesis. -/

theorem p2H_tendsto_zero_iff_hP :
    Tendsto M.p2H atTop (𝓝 0) ↔ Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) := by
  have hfun : (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) = fun r : ℝ => M.p2H r + 1 := by
    funext r
    simp only [p2H, M.cutMassAt_zero_eq_cutMoment r]
    ring
  constructor
  · intro h
    have h' : Tendsto (fun r : ℝ => M.p2H r + 1) atTop (𝓝 (0 + 1)) :=
      h.add (tendsto_const_nhds (x := (1 : ℝ)))
    rw [hfun]
    simpa using h'
  · intro h
    have h' : Tendsto (fun r : ℝ => M.p2H r + 1) atTop (𝓝 1) := hfun ▸ h
    have h'' : Tendsto (fun r : ℝ => M.p2H r + 1 - 1) atTop (𝓝 (1 - 1)) :=
      h'.sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using h''

/-- `H_r → 0` from the normalized first-moment asymptotic `hP`. -/
theorem p2H_tendsto_zero_of_hP (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
    / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    Tendsto M.p2H atTop (𝓝 0) :=
  M.p2H_tendsto_zero_iff_hP.mpr hP

/-! ## `Ē_{2,r}` in terms of the three source errors -/

/-- `1 − Ē_{2,r} = (1 − E_{2,r})(1 + H_r)(1 − E_{0,r})` with the model's `E_{0,r}`, i.e. with
`1 − E_{0,r} = |J'(r)| |B_r| r^{α+1}`.  This is the definition of `Ē_{2,r}`, unfolded. -/
theorem one_sub_p2Ebar (r : ℝ) :
    1 - M.p2Ebar r
      = (1 - M.p2ExclError r) * (1 + M.p2H r) * (1 - PivotFlux.cutE0 M r) := by
  simp only [p2Ebar, VolumeMoments.oneSubEbar2, PivotFlux.cutE0]
  ring

/-- The model's `E_{0,r}` is the paper's `1 − |J'(r)| |B_r| r^{α+1}`: this is
`1 − E_{0,r} = |J'(r)| |B_r| r^{α+1}` of Section I.4.1 at the cutoff kernel. -/
theorem one_sub_cutE0 (r : ℝ) :
    1 - PivotFlux.cutE0 M r
      = |deriv M.K r| * ((M.ball r).ncard : ℝ) * r ^ (M.α + 1) := by
  simp only [PivotFlux.cutE0, VolumeMoments.oneSubE0]
  ring

/-- **`Ē_{2,r} → 0` from the three source inputs.**  The paper's Lemma I.4.6 supplies
`E_{0,r} → 0` and `H_r → 0`, and (I.4.16) together with the Case-1/2 moment bounds supplies
`E_{2,r} → 0`.  All three are hypotheses here: no one of them is deduced from boundedness. -/
theorem p2Ebar_tendsto_zero (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0)) (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    Tendsto M.p2Ebar atTop (𝓝 0) := by
  have hprod : Tendsto (fun r : ℝ =>
      (1 - M.p2ExclError r) * (1 + M.p2H r) * (1 - PivotFlux.cutE0 M r)) atTop (𝓝 1) := by
    have hs1 : Tendsto (fun r : ℝ => (1 : ℝ) - M.p2ExclError r) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hE2
    have hs2 : Tendsto (fun r : ℝ => (1 : ℝ) + M.p2H r) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add hH
    have hs3 : Tendsto (fun r : ℝ => (1 : ℝ) - PivotFlux.cutE0 M r) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hE0
    have h := (hs1.mul hs2).mul hs3
    simpa using h
  have hone : Tendsto (fun r : ℝ =>
      1 - ((1 - M.p2ExclError r) * (1 + M.p2H r) * (1 - PivotFlux.cutE0 M r))) atTop
      (𝓝 (1 - 1)) := tendsto_const_nhds.sub hprod
  have hfe : (fun r : ℝ =>
      1 - ((1 - M.p2ExclError r) * (1 + M.p2H r) * (1 - PivotFlux.cutE0 M r)))
      =ᶠ[atTop] M.p2Ebar := by
    filter_upwards with r
    rw [← M.one_sub_p2Ebar r]
    ring
  simpa using hone.congr' hfe

/-- **From the right-hand side of (I.4.16) to `E_{2,r} → 0`.**  Since `0 ≤ E_{2,r}` and `E_{2,r}`
is at most the paper's ratio `E[|K|³|K ∩ B_r|]/(|B_r| E|K| E|K|²)`, a vanishing ratio squeezes
`E_{2,r}` to zero.  This is the only place where the upper half of (I.4.16) is used, and the
vanishing of the ratio is an *input* — the content of Cases 1 and 2 of the paper's proof, not a
consequence of (I.4.16). -/
theorem p2ExclError_tendsto_zero_of_connCubeRatio
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (hc : ∀ᶠ r : ℝ in atTop, M.connCubeMass r ≠ ⊤)
    (hratio : Tendsto (fun r : ℝ => (M.connCubeMass r).toReal
        / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal))
      atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hge : ∀ᶠ r : ℝ in atTop, 0 ≤ r := eventually_ge_atTop 0
  refine squeeze_zero' ?_ ?_ hratio
  · filter_upwards [hge, h2] with r hr h2r
    exact M.p2ExclError_nonneg r hr h2r
  · filter_upwards [hge, h2, hc] with r hr h2r hcr
    exact (M.p2ExclError_mem_Icc r hr h2r hcr).2

/-- **`E_{2,r} → 0` from the fourth moment**: the same squeeze with the paper's Case-1 majorant
`E|K|⁴/(|B_r| E|K| E|K|²)`.  (The vanishing of *this* ratio is Case 1's analytic input: it uses
the `p = 4`, `k = 1` generalized tree-graph inequality, which is proved as
`TreeExpansion.FivePoint.fourth_moment_mixed_le` in this repository.) -/
theorem p2ExclError_tendsto_zero_of_fourthRatio
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (h4 : ∀ᶠ r : ℝ in atTop, M.cutMoment 4 r ≠ ⊤)
    (hratio : Tendsto (fun r : ℝ => (M.cutMoment 4 r).toReal
        / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal))
      atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hge : ∀ᶠ r : ℝ in atTop, 0 ≤ r := eventually_ge_atTop 0
  refine squeeze_zero' ?_ ?_ hratio
  · filter_upwards [hge, h2] with r hr h2r
    exact M.p2ExclError_nonneg r hr h2r
  · filter_upwards [hge, h2, h4] with r hr h2r h4r
    exact M.p2ExclError_le_fourth_div r hr h2r h4r

/-- The bridge to the repository's real-valued cutoff moment: `M.cutMomentReal 2` is
`(M.cutMoment 2)ᵗᵒᴿᵉᵃˡ`.  In particular the a.e. derivative target `(T)` of
`Analysis/Cutoff/SecondMoment/FTC.lean` is the `hae` hypothesis of `regularlyVarying_two`, and
`cutMomentReal_absolutelyContinuousOn_two` supplies its `hac`. -/
theorem cutMomentReal_two_eq (r : ℝ) : M.cutMomentReal 2 r = (M.cutMoment 2 r).toReal := rfl

/-! ## The ratio form consumed by `SecondMomentRV` -/

/-- For `t > 0` the normalized ratio `t · (d/dr E|K|²) / (3α E|K|²)` is `1 − Ē_{2,t}`. -/
theorem ratio_eventually_eq (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    ∀ᶠ t : ℝ in atTop,
      t * M.rhsScalarTwo t / (3 * M.α * (M.cutMoment 2 t).toReal) = 1 - M.p2Ebar t := by
  filter_upwards [eventually_ge_atTop r₀] with t ht
  have htpos : 0 < t := lt_of_lt_of_le hr₀ ht
  have hA2 : (0 : ℝ) < (M.cutMoment 2 t).toReal := by
    have := M.one_le_cutMoment_two_toReal t (h2 t ht)
    linarith
  rw [M.rhsScalarTwo_eq_p2Flux t htpos,
    M.p2Flux_eq_fifteen t hα hβ htpos (h1 t ht) (h2 t ht), Real.rpow_neg_one]
  field_simp

/-- **The ratio asymptotic `t · rhsScalarTwo t / (3α E_{β_c,t}|K|²) → 1`**, i.e.
`f' ~ 3α f / t` for the second cutoff moment, from the three source errors.  This is exactly the
`hratio` hypothesis of `SecondMomentRV.secondMoment_regularlyVarying_of_rhs`. -/
theorem ratio_tendsto_one (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ =>
      t * M.rhsScalarTwo t / (3 * M.α * (M.cutMoment 2 t).toReal)) atTop (𝓝 1) := by
  have hzero := M.p2Ebar_tendsto_zero hE2 hH hE0
  have hone : Tendsto (fun t : ℝ => 1 - M.p2Ebar t) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hzero
  have hfe : (fun t : ℝ => 1 - M.p2Ebar t) =ᶠ[atTop]
      (fun t : ℝ => t * M.rhsScalarTwo t / (3 * M.α * (M.cutMoment 2 t).toReal)) :=
    Filter.EventuallyEq.symm (M.ratio_eventually_eq hα hβ hr₀ h1 h2)
  simpa using hone.congr' hfe

/-! ## Proposition I.4.15, Cases 1 and 2: the analytic output -/

/-- **Second-moment regular variation of index `3α`** from the source second-moment error.

The hypotheses split exactly as the paper's:

* `hac`, `hae` — the corner-safe radial identity for `r ↦ E_{β_c,r}|K|²` (absolute continuity on
  compact windows and the a.e. `HasDerivAt` with value `M.rhsScalarTwo`);
* `hmf`, `hmR` — measurability of the moment and of the derivative value;
* `hE2`, `hH`, `hE0` — the three error asymptotics `E_{2,r} → 0`, `H_r → 0`, `E_{0,r} → 0`;
* `h1`, `h2` — finiteness of the first and second cutoff moments on the tail.

`K' ≤ 0` is not a hypothesis: it is `M.deriv_K_nonpos`, from the antitone kernel.
`p2ExclError_tendsto_zero_of_connCubeRatio` below converts the *ratio* form of (I.4.16) — the
right-hand side of the display tending to zero, which is what Cases 1 and 2 of the paper prove
from the generalized tree-graph inequality — into `E_{2,r} → 0`, so that `hE2` can be discharged by
a moment bound rather than assumed.

Nothing else is assumed: in particular `E_{2,r} → 0` is an input, and the bound (I.4.16) proved in
`Bounds.lean` is not used to manufacture it. -/
theorem regularlyVarying_two (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmf : Measurable (fun r : ℝ => (M.cutMoment 2 r).toReal))
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  SecondMomentRV.secondMoment_regularlyVarying_of_rhs hα hr₀ hac
    (fun t ht => by
      have := M.one_le_cutMoment_two_toReal t (h2 t ht)
      linarith)
    hmf hmR hae (M.ratio_tendsto_one hα hβ hr₀ h1 h2 hE2 hH hE0)

/-- **`regularlyVarying_two` with the first-moment defect `H_r → 0` supplied by its source form**
`E_{β_c,r}|K| ∼ (α/β_c) r^α` (`hP`, the accepted first-moment asymptotic of
`Analysis/MomentRegularVariation.lean`), so that the only remaining error inputs are the
second-moment error `E_{2,r} → 0` and the kernel/ball normalization `E_{0,r} → 0`. -/
theorem regularlyVarying_two_of_hP (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmf : Measurable (fun r : ℝ => (M.cutMoment 2 r).toReal))
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two hα hr₀ hβ hac hmf hmR hae h1 h2 hE2
    (M.p2H_tendsto_zero_of_hP hP) hE0

/-- **The reduced form: every input that is already on disk is discharged.**

`H_r → 0` is `hP` (`p2H_tendsto_zero_iff_hP`), `E_{0,r} → 0` is the accepted
`PivotFlux.tendsto_cutE0`, and measurability of `r ↦ E_{β_c,r}|K|²` is
`SourceModelData.measurable_cutMoment_toReal` (monotonicity promotes tail finiteness to global
finiteness).  What remains is exactly: absolute continuity on compact windows (`hac`), the a.e.
radial identity (`hae`), measurability of the derivative value (`hmR`), the tail finiteness of the
two moments, and `E_{2,r} → 0`. -/
theorem regularlyVarying_two_of_hP_of_ae_deriv (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  have hfin : ∀ r : ℝ, M.cutMoment 2 r ≠ ⊤ := by
    intro r
    rcases le_total r r₀ with h | h
    · exact ne_top_of_le_ne_top (h2 r₀ le_rfl) (M.cutMoment_monotone 2 h)
    · exact h2 r h
  exact M.regularlyVarying_two hα hr₀ hβ hac
    (SourceModelData.measurable_cutMoment_toReal M 2 hfin) hmR hae h1 h2 hE2
    (M.p2H_tendsto_zero_of_hP hP) (PivotFlux.tendsto_cutE0 M)

/-- **The same conclusion with `E_{2,r} → 0` discharged by the vanishing of the right-hand side of
(I.4.16)** (the form in which Cases 1 and 2 of the paper supply it), rather than assumed. -/
theorem regularlyVarying_two_of_connCubeRatio (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmf : Measurable (fun r : ℝ => (M.cutMoment 2 r).toReal))
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hc : ∀ᶠ r : ℝ in atTop, M.connCubeMass r ≠ ⊤)
    (hratio : Tendsto (fun r : ℝ => (M.connCubeMass r).toReal
        / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal))
      atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two hα hr₀ hβ hac hmf hmR hae h1 h2
    (M.p2ExclError_tendsto_zero_of_connCubeRatio
      ((eventually_ge_atTop r₀).mono fun r hr => h2 r hr) hc hratio) hH hE0

/-- **The a.e. radial identity in the linear form of (I.4.15)**: wherever the second cutoff moment
has derivative `M.rhsScalarTwo t`, it also has derivative `3α (1 − Ē_{2,t}) E|K|² / t`.  This is the
exact hypothesis shape of `SecondMomentRV.secondMoment_tendsto_div`. -/
theorem ae_hasDerivAt_linear (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t) :
    ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal)
        (3 * M.α * (1 - M.p2Ebar t) * (M.cutMoment 2 t).toReal / t) t := by
  filter_upwards [hae, ae_restrict_mem measurableSet_Ici] with t ht hmem
  have ht0 : 0 < t := lt_of_lt_of_le hr₀ hmem
  have hval : M.rhsScalarTwo t
      = 3 * M.α * (1 - M.p2Ebar t) * (M.cutMoment 2 t).toReal / t := by
    rw [M.rhsScalarTwo_eq_fifteen t hα hβ ht0 (h1 t hmem) (h2 t hmem), Real.rpow_neg_one]
    ring
  rwa [hval] at ht

/-- **The `d > 3α` refinement of Proposition I.4.15** (second-moment `~ A r^{3α}`), from the source
second-moment error and its logarithmic integrability: `Ē_{2,r} → 0` and
`∫ |Ē_{2,r}| dr/r < ∞` give `E_{β_c,r}|K|² / r^{3α} → A` for some `A > 0`.  In the paper the
logarithmic integrability of `Ē_{2,r}` is what Case 1 supplies; here it is an input. -/
theorem tendsto_div_two (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0))
    (hlog : LogarithmicallyIntegrable M.p2Ebar) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  SecondMomentRV.secondMoment_tendsto_div hα hr₀ hac
    (fun t ht => by
      have := M.one_le_cutMoment_two_toReal t (h2 t ht)
      linarith)
    (M.ae_hasDerivAt_linear hα hβ hr₀ h1 h2 hae) hlog.1
    (M.p2Ebar_tendsto_zero hE2 hH hE0) hlog

/-- The `~ c r^{3α}` form of `tendsto_div_two`. -/
theorem tendsto_div_two_normalized (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0))
    (hlog : LogarithmicallyIntegrable M.p2Ebar) :
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / (c * r ^ (3 * M.α))) atTop (𝓝 1) :=
  SecondMomentRV.secondMoment_tendsto_div_normalized hα hr₀ hac
    (fun t ht => by
      have := M.one_le_cutMoment_two_toReal t (h2 t ht)
      linarith)
    (M.ae_hasDerivAt_linear hα hβ hr₀ h1 h2 hae) hlog.1
    (M.p2Ebar_tendsto_zero hE2 hH hE0) hlog

/-- **The reduced `d > 3α` refinement**: `H_r → 0` and `E_{0,r} → 0` discharged (`hP` and
`PivotFlux.tendsto_cutE0`); the inputs are `hac`, `hae`, `h1`, `h2`, `E_{2,r} → 0` and the
logarithmic integrability of `Ē_{2,r}`. -/
theorem tendsto_div_two_of_hP (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hlog : LogarithmicallyIntegrable M.p2Ebar) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  M.tendsto_div_two hα hr₀ hβ hac hae h1 h2 hE2 (M.p2H_tendsto_zero_of_hP hP)
    (PivotFlux.tendsto_cutE0 M) hlog

/-- **The headline reduced form**: second-moment regular variation of index `3α` from

* `hac`, `hae` — the corner-safe radial regularity of `r ↦ E_{β_c,r}|K|²`;
* `hmR` — measurability of `M.rhsScalarTwo`;
* `h1`, `h2` — tail finiteness of the first and second cutoff moments;
* `hP` — the first-moment asymptotic (accepted);
* `hc`, `hratio` — the vanishing of the right-hand side of (I.4.16).

`E_{0,r} → 0`, `H_r → 0`, the measurability of the moment and the (I.4.14)/(I.4.15) algebra are
all discharged inside. -/
theorem regularlyVarying_two_reduced (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hc : ∀ᶠ r : ℝ in atTop, M.connCubeMass r ≠ ⊤)
    (hratio : Tendsto (fun r : ℝ => (M.connCubeMass r).toReal
        / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal))
      atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_hP_of_ae_deriv hα hr₀ hβ hac hmR hae h1 h2 hP
    (M.p2ExclError_tendsto_zero_of_connCubeRatio
      ((eventually_ge_atTop r₀).mono fun r hr => h2 r hr) hc hratio)

/-- The same conclusion in the `momOf` spelling used by the higher-moment packet:
`r ↦ momOf (fun r => M.cutProb r) 0 2 r` is regularly varying of index `3α`. -/
theorem momOf_two_regularlyVarying (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmf : Measurable (fun r : ℝ => (M.cutMoment 2 r).toReal))
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) 0 2 r)
      (3 * M.α) := by
  have h := M.regularlyVarying_two hα hr₀ hβ hac hmf hmR hae h1 h2 hE2 hH hE0
  simpa only [I420Case3.momOf_cutProb_eq_toReal_cutMoment] using h

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
