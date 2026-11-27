/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m7`, direction d10.

# Case-3 hypothesis bundle: the ell = 3 clause is unsatisfiable per vertex, windowed it is true

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 3 (p. 47).  The Case-3 numerator is
`E_{b_c,r}[|K|^3 |K cap B_r|]` and the source bounds it, via Lemma I.4.17 at `p = 3`, `q = 0`
and Lemma I.4.18, by `|B_r| (grad_{r^c} + r^{-c}) (E_{b_c,r}|K|)^4`.

`PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3` encodes the two polygon inputs of that
chain as `hT3` (the `ell = 3` clause, *uniform over the window vertices* `y`) and `hpoly4`
(the `ell = 4` clause).  This file proves that the `hT3` clause -- hence the whole
`hcase3` bundle of `secondMoment_asymptotic_case3` -- is *unsatisfiable* whenever the driver
vanishes, and that the clause is nevertheless *true in the form the numerator actually uses*:
summed over the window.  The windowed form needs no driver at all: the two-scale split of the
landed triangle-diagram domination `T^3_{b_c,r}(0,y) <= grad_{b_c}(0,y)` at `R = sqrt r` gives

  `sum_{y in B_r} T^3(0,y) <= |B_{sqrt r}| grad(0,0) + |B_r| grad_{sqrt r}`,

and `|B_{sqrt r}| / |B_r| ~ r^{-d/2}` is polynomially small by the landed ball count
`M.ball_count` (Lemma I.4.6).  This is the same device the source itself uses for the
normalised open-triangle ball sum `r^{-d} sum_{x in B_r} grad(0,x)` in the proof of
Proposition I.4.2 (landed here as `BallAverage.ballSum_two_scale`); no local geometry at the
origin and no special treatment of `y = 0` is needed.

## Source scope and status

* `cutTwoPoint r 0 0 = 1` and the diagonal lower bound `1 <= T^3_{b_c,r}(0,0)` are landed
  (`SourceModelData.cutTwoPoint_self_eq_one`, `I420Case3.one_le_polyK_three_of_chi_ne_top`);
  the first is exactly the source's normalisation `T(x,x) = 1`.
* The printed `ell = 3` display of Lemma I.4.18 (`sup_x T^3(0,x) <= C (grad_{r^c}+r^{-c})`,
  which would have to tend to `0`) is therefore refuted at `x = 0`; see
  `I418C.one_le_polyK_three` and `I420Case3.CutPoly.Main.one_le_Bpoly_of_hasPolygonBound`.
  The present file records the *bundle-level* consequence and the repair.
* Nothing here proves the missing `p = 3`, `q = 0` moment-gap input `hgap` (Lemma I.4.17 at
  `p = 3`, `q = 0`); it is carried explicitly, as in `Case3.lean`.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Defs
public import PercLib.CriticalLRP.Analysis.BallAverage

/-! # The `ell = 3` clause of the Case-3 bundle -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Set
set_option linter.style.longLine false

open scoped ENNReal NNReal Topology BigOperators Asymptotics

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

open PercLib.CriticalLRP

/-! ## The windowed `ell = 3` bound (two-scale split at `R = sqrt r`) -/

/-- **The `ell = 3` polygon term, summed over the window.**

`sum_{y in B_r} T^3_{b_c,r}(0,y) <= |B_{sqrt r}| grad(0,0) + |B_r| grad_{sqrt r}`.

The near part of the window is charged to the (finite) triangle constant `grad(0,0) = triSelf`
at the cost of the cardinality `|B_{sqrt r}|`; the far part is charged to the triangle tail
`grad_{sqrt r} = nablaTail (sqrt r)` at the cost of the full window `|B_r|`.  The only inputs
are the landed domination `T^3_{b_c,r}(0,y) <= grad_{b_c}(0,y)`
(`cutTriPoint_le_triPoint`), the diagonal bound `grad(0,y) <= grad(0,0)` (`triPoint_le_self`)
and the definition of the tail (`triPoint_le_nablaTail`). -/
theorem sum_polyK_three_ballF_le_two_scale {r : ℝ} (hr : 1 ≤ r)
    (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y
      ≤ ((M.ball (Real.sqrt r)).ncard : ℝ) * M.triSelf
        + ((M.ball r).ncard : ℝ) * (M.nablaTail (Real.sqrt r)).toReal := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hr
  have hsqrt_le : Real.sqrt r ≤ r := BallAverage.sqrt_le_self_of_one_le hr
  have hsub : E1Sign.ballF M (Real.sqrt r) ⊆ E1Sign.ballF M r := by
    intro y hy
    rw [E1Sign.mem_ballF] at hy ⊢
    exact BallAverage.ball_mono M hsqrt_le hy
  have htail : (0 : ℝ) ≤ (M.nablaTail (Real.sqrt r)).toReal := M.nablaTail_toReal_nonneg _
  have hpoint : ∀ y ∈ E1Sign.ballF M r,
      I418C.polyK (M.cutTwoPoint r) 3 0 y
        ≤ M.triSelf * (if y ∈ E1Sign.ballF M (Real.sqrt r) then 1 else 0)
          + (M.nablaTail (Real.sqrt r)).toReal := by
    intro y _
    have h1 : I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ M.triPoint 0 y :=
      M.cutTriPoint_le_triPoint r hχ hTri y
    by_cases hyt : y ∈ E1Sign.ballF M (Real.sqrt r)
    · have h2 : M.triPoint 0 y ≤ M.triSelf := M.triPoint_le_self hTri y
      simp only [hyt, ite_true, mul_one]
      linarith
    · have hfar : Real.sqrt r ≤ M.S.dist 0 y := by
        rw [M.dist_zero_eq]
        by_contra hcon
        push Not at hcon
        have hmem : y ∈ M.ball (Real.sqrt r) := by
          change M.S.ρ (toVec y) ≤ Real.sqrt r
          exact le_of_lt hcon
        exact hyt ((E1Sign.mem_ballF M).mpr hmem)
      have h2 : M.triPoint 0 y ≤ (M.nablaTail (Real.sqrt r)).toReal :=
        M.triPoint_le_nablaTail (r := Real.sqrt r) hTri hfar
      simp only [hyt, ite_false, mul_zero, zero_add]
      linarith
  calc ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y
      ≤ ∑ y ∈ E1Sign.ballF M r,
          (M.triSelf * (if y ∈ E1Sign.ballF M (Real.sqrt r) then 1 else 0)
            + (M.nablaTail (Real.sqrt r)).toReal) := Finset.sum_le_sum hpoint
    _ = M.triSelf * ((E1Sign.ballF M (Real.sqrt r)).card : ℝ)
          + ((E1Sign.ballF M r).card : ℝ) * (M.nablaTail (Real.sqrt r)).toReal := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
          simp
        · rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((M.ball (Real.sqrt r)).ncard : ℝ) * M.triSelf
          + ((M.ball r).ncard : ℝ) * (M.nablaTail (Real.sqrt r)).toReal := by
        rw [E1Sign.card_ballF, E1Sign.card_ballF]
        ring

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## Lattice-ball cardinality: the `sqrt` ball is polynomially thinner -/

/-- **The ball count `|B_r| ~ r^d` (Lemma I.4.6) in eventual two-sided form**, with the
constants `1 - δ`, `1 + δ` of the `ε`-approximation. -/
theorem eventually_ball_ncard_between {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop,
      (1 - δ) * r ^ (M.d : ℝ) ≤ ((M.ball r).ncard : ℝ) ∧
        ((M.ball r).ncard : ℝ) ≤ (1 + δ) * r ^ (M.d : ℝ) := by
  have hd1 : 1 ≤ M.d := M.hd
  have hne : ∀ᶠ r : ℝ in atTop, (fun r : ℝ => r ^ (M.d : ℝ)) r ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact ne_of_gt (Real.rpow_pos_of_pos hr _)
  have hcount : (fun r : ℝ => ((M.ball r).ncard : ℝ)) ~[atTop]
      (fun r : ℝ => r ^ (M.d : ℝ)) := by
    simpa only [Real.rpow_natCast] using M.ball_count
  have hratio : Tendsto (fun r : ℝ => ((M.ball r).ncard : ℝ) / r ^ (M.d : ℝ)) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hcount
  have hmem : ∀ᶠ r : ℝ in atTop,
      ((M.ball r).ncard : ℝ) / r ^ (M.d : ℝ) ∈ Set.Ioo (1 - δ) (1 + δ) := by
    have hI : Set.Ioo (1 - δ) (1 + δ) ∈ 𝓝 (1 : ℝ) := by
      apply Ioo_mem_nhds
      · linarith
      · linarith
    exact hratio hI
  filter_upwards [hmem, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  rw [Set.mem_Ioo] at hr
  have hpos : (0 : ℝ) < r ^ (M.d : ℝ) := Real.rpow_pos_of_pos hr0 _
  constructor
  · rw [lt_div_iff₀ hpos] at hr
    linarith [hr.1]
  · rw [div_lt_iff₀ hpos] at hr
    linarith [hr.2]

/-- The same two-sided form at radius `sqrt r`, using `(sqrt r)^d = r^{d/2}`. -/
theorem eventually_ball_sqrt_ncard_between {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop,
      (1 - δ) * r ^ ((M.d : ℝ) / 2) ≤ ((M.ball (Real.sqrt r)).ncard : ℝ) ∧
        ((M.ball (Real.sqrt r)).ncard : ℝ) ≤ (1 + δ) * r ^ ((M.d : ℝ) / 2) := by
  have hsqrt : Tendsto (fun r : ℝ => Real.sqrt r) atTop atTop := Real.tendsto_sqrt_atTop
  have hcomp := hsqrt.eventually (M.eventually_ball_ncard_between hδ)
  filter_upwards [hcomp, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  have hsq : (Real.sqrt r) ^ (M.d : ℝ) = r ^ ((M.d : ℝ) / 2) := by
    rw [Real.rpow_natCast, BallAverage.sqrt_pow_eq_rpow M hr0]
  rw [hsq] at hr
  exact hr

/-- **The `sqrt`-ball is polynomially thinner than the ball**: `|B_{sqrt r}| / |B_r| → 0`.

The rate is `≤ 4 r^{-d/2}` eventually, which is what makes the windowed `ell = 3` term of the
Case-3 numerator converge (and logarithmically integrable) without any driver. -/
theorem tendsto_ball_sqrt_ncard_ratio_zero (hd : 1 ≤ M.d) :
    Tendsto (fun r : ℝ => ((M.ball (Real.sqrt r)).ncard : ℝ) / ((M.ball r).ncard : ℝ))
      atTop (𝓝 0) := by
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
  have hsmall := M.eventually_ball_ncard_between (δ := 1 / 2) (by norm_num)
  have hsmallsqrt := M.eventually_ball_sqrt_ncard_between (δ := 1 / 2) (by norm_num)
  refine squeeze_zero' (g := fun r : ℝ => 4 * r ^ (-(M.d : ℝ) / 2)) ?_ ?_ ?_
  · filter_upwards [hsmall] with r hr
    exact div_nonneg (Nat.cast_nonneg _) (by linarith [hr.1])
  · filter_upwards [hsmall, hsmallsqrt, eventually_gt_atTop (0 : ℝ)] with r h1 h2 hr0
    have hpow : (0 : ℝ) < r ^ (M.d : ℝ) := Real.rpow_pos_of_pos hr0 _
    have hden : (0 : ℝ) < (1 / 2) * r ^ (M.d : ℝ) := by positivity
    have hnum : ((M.ball (Real.sqrt r)).ncard : ℝ) ≤ 2 * r ^ ((M.d : ℝ) / 2) := by
      have := h2.2
      linarith
    have hden' : (1 / 2) * r ^ (M.d : ℝ) ≤ ((M.ball r).ncard : ℝ) := by
      have := h1.1
      linarith
    have hpos_num : (0 : ℝ) < ((M.ball r).ncard : ℝ) := lt_of_lt_of_le hden hden'
    have hbound : ((M.ball (Real.sqrt r)).ncard : ℝ) / ((M.ball r).ncard : ℝ)
        ≤ (2 * r ^ ((M.d : ℝ) / 2)) / ((1 / 2) * r ^ (M.d : ℝ)) :=
      div_le_div₀ (by positivity) hnum hden hden'
    have hsplit : (2 * r ^ ((M.d : ℝ) / 2)) / ((1 / 2) * r ^ (M.d : ℝ))
        = 4 * r ^ (-(M.d : ℝ) / 2) := by
      have hb : r ^ (M.d : ℝ) ≠ 0 := ne_of_gt hpow
      have h1 : r ^ (-(M.d : ℝ) / 2) * r ^ (M.d : ℝ) = r ^ ((M.d : ℝ) / 2) := by
        rw [← Real.rpow_add hr0]
        ring_nf
      rw [← h1]
      field_simp
      norm_num
    rw [hsplit] at hbound
    exact hbound
  · have hpos : (0 : ℝ) < (M.d : ℝ) / 2 := by
      have : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
      linarith
    have h : Tendsto (fun r : ℝ => r ^ (-(M.d : ℝ) / 2)) atTop (𝓝 0) := by
      simpa only [neg_div] using tendsto_rpow_neg_atTop hpos
    simpa using h.const_mul 4

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The windowed `ell = 3` clause in the form the numerator uses

`Case3.lean`'s `hT3` demands `T^3(0,y) ≤ Cp * driver r` at *every* window vertex `y`, which is
unsatisfiable because the diagonal entry `T^3(0,0)` is at least `1` while the driver vanishes.
The numerator only ever uses the *sum* over the window, and there the two-scale bound of
`sum_polyK_three_ballF_le_two_scale` together with the ball count gives the polynomial rate
`4 r^{-d/2}`. -/

/-- **Eventual `ell = 3` window clause with the explicit polynomial rate.**

`sum_{y in B_r} T^3(0,y) ≤ |B_r| (4 r^{-d/2} grad(0,0) + grad_{sqrt r})` eventually, with no
driver and no per-vertex uniformity: the `sqrt`-ball is thinner than the ball by `r^{-d/2}` by
`tendsto_ball_sqrt_ncard_ratio_zero`. -/
theorem eventually_sum_polyK_three_ballF_le_rate {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hχ : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∀ᶠ r : ℝ in atTop,
      (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
        ≤ ((M.ball r).ncard : ℝ)
          * ((1 + δ) / (1 - δ) * r ^ (-(M.d : ℝ) / 2) * M.triSelf
              + (M.nablaTail (Real.sqrt r)).toReal) := by
  have hsmall := M.eventually_ball_ncard_between (δ := δ) hδ
  have hsmallsqrt := M.eventually_ball_sqrt_ncard_between (δ := δ) hδ
  filter_upwards [hsmall, hsmallsqrt, hχ, eventually_ge_atTop (1 : ℝ)]
    with r h1 h2 hχr hr1
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hr1
  have htwo := M.sum_polyK_three_ballF_le_two_scale hr1 hχr hTri
  have htri : (0 : ℝ) ≤ M.triSelf := M.triPoint_nonneg 0 0
  have htail : (0 : ℝ) ≤ (M.nablaTail (Real.sqrt r)).toReal := M.nablaTail_toReal_nonneg _
  -- `|B_{sqrt r}| ≤ (1+δ) r^{d/2} ≤ (1+δ) r^{-d/2} |B_r| / (1-δ)`-free form: use the ratio
  have hratio : ((M.ball (Real.sqrt r)).ncard : ℝ)
      ≤ (1 + δ) * r ^ (-(M.d : ℝ) / 2) * ((M.ball r).ncard : ℝ) / (1 - δ) := by
    have hpos : (0 : ℝ) < r ^ ((M.d : ℝ) / 2) := Real.rpow_pos_of_pos hr0 _
    have hpos2 : (0 : ℝ) < r ^ (M.d : ℝ) := Real.rpow_pos_of_pos hr0 _
    have hd1 : (0 : ℝ) < 1 - δ := by linarith
    have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
      have hle := h1.1
      have hpos' : (0 : ℝ) < (1 - δ) * r ^ (M.d : ℝ) := by positivity
      linarith
    rw [le_div_iff₀ hd1]
    have hsplit : r ^ ((M.d : ℝ) / 2) = r ^ (-(M.d : ℝ) / 2) * r ^ (M.d : ℝ) := by
      rw [← Real.rpow_add hr0]
      ring_nf
    calc ((M.ball (Real.sqrt r)).ncard : ℝ) * (1 - δ)
        ≤ (1 + δ) * r ^ ((M.d : ℝ) / 2) * (1 - δ) := by
          have := h2.2
          nlinarith [h2.2]
    _ ≤ (1 + δ) * r ^ (-(M.d : ℝ) / 2) * ((M.ball r).ncard : ℝ) := by
        rw [hsplit]
        have := h1.1
        have hA : (0 : ℝ) ≤ (1 + δ) * r ^ (-(M.d : ℝ) / 2) := by positivity
        nlinarith [h1.1, hA, hpos, hpos2, Real.rpow_pos_of_pos hr0 (-(M.d : ℝ) / 2)]
  have hstep : ((M.ball (Real.sqrt r)).ncard : ℝ) * M.triSelf
      ≤ ((M.ball r).ncard : ℝ)
        * ((1 + δ) / (1 - δ) * r ^ (-(M.d : ℝ) / 2) * M.triSelf) := by
    have hd1 : (0 : ℝ) < 1 - δ := by linarith
    calc ((M.ball (Real.sqrt r)).ncard : ℝ) * M.triSelf
        ≤ ((1 + δ) * r ^ (-(M.d : ℝ) / 2) * ((M.ball r).ncard : ℝ) / (1 - δ)) * M.triSelf :=
          mul_le_mul_of_nonneg_right hratio htri
    _ = ((M.ball r).ncard : ℝ)
          * ((1 + δ) / (1 - δ) * r ^ (-(M.d : ℝ) / 2) * M.triSelf) := by
        field_simp
  calc (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
      ≤ ((M.ball (Real.sqrt r)).ncard : ℝ) * M.triSelf
          + ((M.ball r).ncard : ℝ) * (M.nablaTail (Real.sqrt r)).toReal := htwo
    _ ≤ ((M.ball r).ncard : ℝ)
          * ((1 + δ) / (1 - δ) * r ^ (-(M.d : ℝ) / 2) * M.triSelf)
          + ((M.ball r).ncard : ℝ) * (M.nablaTail (Real.sqrt r)).toReal := by
        linarith [hstep]
    _ = ((M.ball r).ncard : ℝ)
          * ((1 + δ) / (1 - δ) * r ^ (-(M.d : ℝ) / 2) * M.triSelf
              + (M.nablaTail (Real.sqrt r)).toReal) := by ring

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The Case-3 numerator from the windowed `ell = 3` clause -/

/-- **The Case-3 numerator from a windowed `ell = 3` input.**

Per window vertex `y` the moment gap (`hgap`) gives
`F y ≤ C₃ T^3(0,y) χ^4 + C₄ T^4(0,y) χ^3`; summing, the `ell = 3` half only needs the *sum*
`∑_y T^3(0,y) ≤ W` (no per-vertex uniformity, hence no driver), while the `ell = 4` half uses the
landed polygon bound `hT4` vertex by vertex. -/
theorem connCubeMass_toReal_le_of_windowed_ell_three
    {c Cp C3 C4 W r : ℝ} (_hCp : 0 ≤ Cp) (_hC3 : 0 ≤ C3) (_hC4 : 0 ≤ C4) (hr : 1 ≤ r)
    (hc : M.connCubeMass r ≠ ⊤)
    (hgap : ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hW : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y) ≤ W)
    (hT4 : ∀ x : M.V, I418C.polyK (M.cutTwoPoint r) 4 0 x
      ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    (M.connCubeMass r).toReal
      ≤ C3 * (M.cutMassAt r 0).toReal ^ 4 * W
        + C4 * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by
  rw [M.connCubeMass_toReal_eq_sum_vertex r hc]
  have hχnn : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
  have hdrvnn : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
  have hsum4 : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 0 y)
      ≤ ((M.ball r).ncard : ℝ) * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
    calc (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 0 y)
        ≤ ∑ _y ∈ E1Sign.ballF M r, Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal :=
          Finset.sum_le_sum fun y _ => hT4 y
      _ = ((E1Sign.ballF M r).card : ℝ) * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((M.ball r).ncard : ℝ) * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
          rw [E1Sign.card_ballF]
  have h3nn : (0 : ℝ) ≤ ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y :=
    Finset.sum_nonneg fun y _ => I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 y
  have h4nn : (0 : ℝ) ≤ ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 0 y :=
    Finset.sum_nonneg fun y _ => I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 4 0 y
  calc (∑ y ∈ E1Sign.ballF M r, (M.connCubeVertexMass r y).toReal)
      ≤ ∑ y ∈ E1Sign.ballF M r,
          (C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
            + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3) :=
        Finset.sum_le_sum hgap
    _ = C3 * (M.cutMassAt r 0).toReal ^ 4
          * (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
          + C4 * (M.cutMassAt r 0).toReal ^ 3
            * (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 0 y) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun x _ => by ring
        · exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ C3 * (M.cutMassAt r 0).toReal ^ 4 * W
          + C4 * (M.cutMassAt r 0).toReal ^ 3
            * (((M.ball r).ncard : ℝ) * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)) := by
        have h1 : C3 * (M.cutMassAt r 0).toReal ^ 4
              * (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
            ≤ C3 * (M.cutMassAt r 0).toReal ^ 4 * W :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        have h2 : C4 * (M.cutMassAt r 0).toReal ^ 3
              * (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 4 0 y)
            ≤ C4 * (M.cutMassAt r 0).toReal ^ 3
              * (((M.ball r).ncard : ℝ) * (Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)) :=
          mul_le_mul_of_nonneg_left hsum4 (by positivity)
        linarith [h1, h2]
    _ = C3 * (M.cutMassAt r 0).toReal ^ 4 * W
          + C4 * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal ^ 4 := by
        ring_nf

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 error bound from the windowed `ell = 3` clause.**

Dividing the windowed numerator bound by `|B_r| χ E|K|^2` and using the moment gap
`c₃ χ^3 ≤ E|K|^2` turns the numerator into the source's Case-3 error:
`E_{2,r} ≤ (C₃/c₃) (W/|B_r|) + (C₄ Cp/c₃) (grad_{r^c} + r^{-c})`.  No `hT3`
(`T^3(0,y) ≤ Cp * driver` uniformly in `y`) appears: the `ell = 3` half enters only through the
windowed number `W`. -/
theorem p2ExclError_le_of_windowed_ell_three
    {c Cp C3 C4 c₃ W r : ℝ} (_hCp : 0 ≤ Cp) (_hC3 : 0 ≤ C3) (_hC4 : 0 ≤ C4) (hc₃ : 0 < c₃)
    (hr : 1 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) (hcM : M.connCubeMass r ≠ ⊤)
    (hgap : ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hW : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y) ≤ W)
    (hT4 : ∀ x : M.V, I418C.polyK (M.cutTwoPoint r) 4 0 x
      ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    M.p2ExclError r
      ≤ (C3 / c₃) * (W / ((M.ball r).ncard : ℝ)) + (C4 * Cp / c₃) * M.case3Driver c r := by
  have hN := M.connCubeMass_toReal_le_of_windowed_ell_three (c := c) (Cp := Cp) (C3 := C3)
    (C4 := C4) (W := W) (r := r) _hCp _hC3 _hC4 hr hcM hgap hW hT4
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have h1r : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hχeq : (M.cutMoment 1 r).toReal = (M.cutMassAt r 0).toReal := by
    rw [M.cutMassAt_zero_eq_cutMoment r]
  have hE := M.p2ExclError_le_connCubeMass_div r hr0 h2 hcM
  rw [hχeq] at hE
  have hχ : (0 : ℝ) < (M.cutMassAt r 0).toReal := by
    have h := M.one_le_cutMoment_one_toReal r h1r
    rw [hχeq] at h
    linarith
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have h := M.one_le_cutMoment_two_toReal r h2
    linarith
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r hr0
  have hdrvnn : 0 ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
  have h3nn : (0 : ℝ) ≤ ∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y :=
    Finset.sum_nonneg fun y _ => I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 0 y
  have hWnn : (0 : ℝ) ≤ W := le_trans h3nn hW
  have hNnn : 0 ≤ C3 * (M.cutMassAt r 0).toReal ^ 4 * W
      + C4 * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r
          * (M.cutMassAt r 0).toReal ^ 4 := by
    have := hb
    have := hχ
    have := hWnn
    have := hdrvnn
    positivity
  have hden1 : (0 : ℝ) < c₃ * ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 4 := by
    have := hb
    have := hχ
    positivity
  have hden_le : c₃ * ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 4
      ≤ ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal := by
    have hgm' : c₃ * (M.cutMassAt r 0).toReal ^ 3 * (M.cutMassAt r 0).toReal
        ≤ (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal := by
      have := mul_le_mul_of_nonneg_right hgm hχ.le
      nlinarith [this]
    have hb' : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := hb.le
    calc c₃ * ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 4
        = ((M.ball r).ncard : ℝ)
            * (c₃ * (M.cutMassAt r 0).toReal ^ 3 * (M.cutMassAt r 0).toReal) := by ring
      _ ≤ ((M.ball r).ncard : ℝ)
            * ((M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal) :=
          mul_le_mul_of_nonneg_left hgm' hb'
      _ = ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal := by ring
  calc M.p2ExclError r
      ≤ (M.connCubeMass r).toReal
          / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal) := hE
    _ ≤ (C3 * (M.cutMassAt r 0).toReal ^ 4 * W
          + C4 * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
          / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal * (M.cutMoment 2 r).toReal) := by
        gcongr
    _ ≤ (C3 * (M.cutMassAt r 0).toReal ^ 4 * W
          + C4 * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
          / (c₃ * ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 4) := by
        apply div_le_div_of_nonneg_left hNnn hden1 hden_le
    _ = (C3 / c₃) * (W / ((M.ball r).ncard : ℝ)) + (C4 * Cp / c₃) * M.case3Driver c r := by
        field_simp

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Case 3 of Proposition I.4.15 without the unsatisfiable `hT3`.**

Hypotheses, all source-shaped and none of them the per-vertex polygon clause:

* `hP` — the accepted first-moment asymptotic `E_{b_c,r}|K| ~ (α/b_c) r^α` (Proposition I.4.2);
* `hTri` — the triangle condition `grad_{b_c} < ∞`;
* `hgap` — Lemma I.4.17 at `p = 3`, `q = 0` (the genuine missing source input, carried visibly);
* `hT4` — Lemma I.4.18 at `ell = 4`, i.e. the landed all-radius polygon bound;
* `hgm` — the moment gap `E|K|^2 >= c₃ (E|K|)^3`;
* `hdrv` — the triangle condition's consequence `grad_{r^c} + r^{-c} → 0`;
* `0 < c <= 1/2` so that `r^c <= sqrt r`.

The `ell = 3` term is handled by `eventually_sum_polyK_three_ballF_le_rate`: its contribution to
`E_{2,r}` is `(C₃/c₃)(3 r^{-d/2} grad(0,0) + grad_{sqrt r})`, which tends to zero polynomially.
In particular the driver does not enter the `ell = 3` half at all, and no vertex-uniform polygon
factor is required. -/
theorem p2ExclError_tendsto_zero_of_windowed_ell_three
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {c Cp C3 C4 c₃ : ℝ} (_hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (_hCp : 0 ≤ Cp) (_hC3 : 0 ≤ C3) (_hC4 : 0 ≤ C4) (hc₃ : 0 < c₃)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcM : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hT4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  obtain ⟨c₀, hc₀, hχall⟩ := I418C.ChiInput.exists_chi_lower_uniform_and_finite M hβ hP
  have hχev : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (hχall r hr).2
  -- the windowed `ell = 3` clause at `δ = 1/2`, i.e. rate `3 r^{-d/2}`
  have hrate := M.eventually_sum_polyK_three_ballF_le_rate (δ := 1 / 2)
    (by norm_num) (by norm_num) hχev hTri
  -- `grad_{sqrt r} → 0`
  have hnabla_zero : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun r => M.nablaTail_toReal_nonneg _) ?_ hdrv
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hpos : (0 : ℝ) < r ^ (-c) := Real.rpow_pos_of_pos hr (-c)
    simp only [case3Driver]
    linarith
  have hcomp : Tendsto (fun r : ℝ => (M.nablaTail (Real.sqrt r)).toReal) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun r => M.nablaTail_toReal_nonneg _) ?_
      hnabla_zero
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hcle : r ^ c ≤ Real.sqrt r := by
      have h1 : r ^ c ≤ r ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hr hc2
      rwa [← Real.sqrt_eq_rpow] at h1
    have h := M.nablaTail_antitone hcle
    exact ENNReal.toReal_mono (M.nablaTail_ne_top _ hTri) h
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by
    have : 0 < M.d := lt_of_lt_of_le Nat.zero_lt_one M.hd
    exact_mod_cast this
  have hpow : Tendsto (fun r : ℝ => r ^ (-(M.d : ℝ) / 2)) atTop (𝓝 0) := by
    have hpos : (0 : ℝ) < (M.d : ℝ) / 2 := by linarith
    simpa only [neg_div] using tendsto_rpow_neg_atTop hpos
  -- the full majorant
  have hX : Tendsto (fun r : ℝ => (3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf
      + (M.nablaTail (Real.sqrt r)).toReal) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => (3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf) atTop (𝓝 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hpow.const_mul (3 * M.triSelf)
    simpa using h1.add hcomp
  have hmaj : Tendsto (fun r : ℝ => (C3 / c₃) * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf
      + (M.nablaTail (Real.sqrt r)).toReal) + (C4 * Cp / c₃) * M.case3Driver c r)
      atTop (𝓝 0) := by
    have h1 := hX.const_mul (C3 / c₃)
    have h2 := hdrv.const_mul (C4 * Cp / c₃)
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact M.p2ExclError_nonneg r (le_trans zero_le_one hr) (h2 r hr)
  · filter_upwards [hrate, hgm, eventually_ge_atTop (1 : ℝ)] with r hW hgmr hr
    have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
    have hb : ((M.ball r).ncard : ℝ) ≠ 0 := by
      have := M.ball_ncard_pos r hr0
      positivity
    have hW3 : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
        ≤ ((M.ball r).ncard : ℝ)
          * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf
              + (M.nablaTail (Real.sqrt r)).toReal) := by
      refine hW.trans (le_of_eq ?_)
      norm_num
    have hstep := M.p2ExclError_le_of_windowed_ell_three (c := c) (Cp := Cp) (C3 := C3)
      (C4 := C4) (c₃ := c₃)
      (W := ((M.ball r).ncard : ℝ)
        * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf + (M.nablaTail (Real.sqrt r)).toReal))
      (r := r) _hCp _hC3 _hC4 hc₃ hr (h2 r hr) (hcM r hr) (hgap r hr) hW3 (hT4 r hr) hgmr
    rw [mul_div_cancel_left₀
      ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf + (M.nablaTail (Real.sqrt r)).toReal) hb] at hstep
    exact hstep

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The per-vertex clause of the bundle is unsatisfiable -/

/-- **No uniform vanishing polygon factor for `T^3` at `y = 0`.**

`T^3_{b_c,r}(0,0) >= 1` (`I420Case3.one_le_polyK_three_of_chi_ne_top`, from `T(0,0) = 1`) while
`case3Driver c r -> 0`, so the `ell = 3` clause

  `∀ r ≥ 1, ∀ y, T^3_{b_c,r}(0,y) <= Cp * (grad_{r^c} + r^{-c})`

of `connCubeMass_le_of_windowGap` / `secondMoment_asymptotic_case3` has no solution.  This is the
bundle-level form of the landed refutation of the printed `ell = 3` display of Lemma I.4.18. -/
theorem not_forall_polyK_three_le_case3Driver_of_tendsto {c Cp : ℝ} (_hCp : 0 < Cp)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0))
    (hχ : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤) :
    ¬ (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
        I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r) := by
  intro h
  have h1 : ∀ᶠ r : ℝ in atTop, (1 : ℝ) ≤ Cp * M.case3Driver c r := by
    filter_upwards [hχ, eventually_ge_atTop (1 : ℝ)] with r hχr hr
    exact le_trans (I420Case3.one_le_polyK_three_of_chi_ne_top M r hχr) (h r hr 0)
  have h2 : Tendsto (fun r : ℝ => Cp * M.case3Driver c r) atTop (𝓝 0) := by
    simpa using hdrv.const_mul Cp
  exact I420Case3.not_tendsto_zero_of_one_le_eventually h1 h2

/-- **The `hcase3` bundle of `secondMoment_asymptotic_case3` is unsatisfiable.**

The bundle asks for a vanishing driver together with the vertex-uniform `ell = 3` polygon bound;
`not_forall_polyK_three_le_case3Driver_of_tendsto` shows the two requirements are incompatible at `y = 0`.
Consequently the Case-3 theorem as assembled is vacuous, and the `ell = 3` input has to be
carried in a form that is actually available -- the windowed form of
`eventually_sum_polyK_three_ballF_le_rate`, which feeds
`p2ExclError_tendsto_zero_of_windowed_ell_three` without any per-vertex factor. -/
theorem not_exists_case3_bundle
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ¬ ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
        Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
        Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
        (∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
          I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * M.case3Driver c r) ∧
        (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
          I418C.polyK (M.cutTwoPoint r) 4 0 x
            ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
  rintro ⟨c, Cp, -, hCp, hdrv, -, h3, -⟩
  obtain ⟨c₀, hc₀, hχall⟩ := I418C.ChiInput.exists_chi_lower_uniform_and_finite M hβ hP
  have hχ : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (hχall r hr).2
  exact M.not_forall_polyK_three_le_case3Driver_of_tendsto hCp hdrv hχ h3

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The repaired bundle: existence and sufficiency -/

/-- **The triangle tail decay transfers to `sqrt r`**: if `grad_r → 0` then
`grad_{sqrt r} → 0`.  This is Lemma I.4.19's change of variables in the easy direction; only the
monotone reparametrisation is used. -/
theorem tendsto_nablaTail_sqrt_zero
    (hdecay : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.nablaTail (Real.sqrt r)).toReal) atTop (𝓝 0) :=
  hdecay.comp Real.tendsto_sqrt_atTop

/-- **The repaired Case-3 bundle exists.**

There are `c, Cp > 0` such that

* the `ell = 4` polygon clause of Lemma I.4.18 holds (this is the landed all-radius
  manufacturer `exists_polygonBound_four`, i.e. `I418C.exists_uniform_source_polygon_bound_
  of_triangle_first_moment_all_radii` at `ell = 4`), and
* the `ell = 3` clause holds in *windowed* form with an explicit vanishing driver
  `D r = (grad_{r^c} + r^{-c}) + grad_{sqrt r} + 3 r^{-d/2} grad(0,0)`,

with `D → 0` as soon as the triangle tail decays.  Contrast `not_exists_case3_bundle`: the
per-vertex `ell = 3` clause is unsatisfiable, the windowed one is a theorem. -/
theorem exists_repaired_case3_bundle
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hdecay : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (fun r : ℝ => M.case3Driver c r + (M.nablaTail (Real.sqrt r)).toReal
          + 3 * r ^ (-(M.d : ℝ) / 2) * M.triSelf) atTop (𝓝 0) ∧
      (∀ r : ℝ, 0 < r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 0 x
          ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) ∧
      (∀ᶠ r : ℝ in atTop,
        (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
          ≤ ((M.ball r).ncard : ℝ)
            * (M.case3Driver c r + (M.nablaTail (Real.sqrt r)).toReal
                + 3 * r ^ (-(M.d : ℝ) / 2) * M.triSelf)) := by
  obtain ⟨c, Cp, hc, hCp, hT4⟩ := M.exists_polygonBound_four hP hTri
  obtain ⟨c₀, hc₀, hχall⟩ := I418C.ChiInput.exists_chi_lower_uniform_and_finite M
    (I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div M hP) hP
  have hχev : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (hχall r hr).2
  have hrate := M.eventually_sum_polyK_three_ballF_le_rate (δ := 1 / 2)
    (by norm_num) (by norm_num) hχev hTri
  have hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ c) atTop atTop := tendsto_rpow_atTop hc
    have h2 : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0) :=
      hdecay.comp h1
    have h3 : Tendsto (fun r : ℝ => r ^ (-c)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
    have hmain : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal + r ^ (-c))
        atTop (𝓝 0) := by
      simpa using h2.add h3
    have hfun : (fun r : ℝ => (M.nablaTail (r ^ c)).toReal + r ^ (-c)) = M.case3Driver c := rfl
    rw [hfun] at hmain
    exact hmain
  have hsqrt := M.tendsto_nablaTail_sqrt_zero hdecay
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by
    have : 0 < M.d := lt_of_lt_of_le Nat.zero_lt_one M.hd
    exact_mod_cast this
  have hpow : Tendsto (fun r : ℝ => 3 * r ^ (-(M.d : ℝ) / 2) * M.triSelf)
      atTop (𝓝 0) := by
    have hpos : (0 : ℝ) < (M.d : ℝ) / 2 := by linarith
    have h := (tendsto_rpow_neg_atTop hpos : Tendsto (fun r : ℝ => r ^ (-((M.d : ℝ) / 2)))
      atTop (𝓝 0))
    simpa [neg_div, mul_assoc, mul_comm, mul_left_comm] using h.const_mul (3 * M.triSelf)
  refine ⟨c, Cp, hc, hCp, ?_, hT4, ?_⟩
  · simpa only [add_assoc, zero_add] using (hdrv.add hsqrt).add hpow
  · filter_upwards [hrate, eventually_ge_atTop (1 : ℝ)] with r hr hr1
    have hdrvnn : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
    have hcard : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := Nat.cast_nonneg _
    have hW3 : ((M.ball r).ncard : ℝ)
          * ((1 + 1 / 2) / (1 - 1 / 2) * r ^ (-(M.d : ℝ) / 2) * M.triSelf
              + (M.nablaTail (Real.sqrt r)).toReal)
        = ((M.ball r).ncard : ℝ)
          * (3 * r ^ (-(M.d : ℝ) / 2) * M.triSelf
              + (M.nablaTail (Real.sqrt r)).toReal) := by
      norm_num
    rw [hW3] at hr
    calc (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
        ≤ ((M.ball r).ncard : ℝ)
          * (3 * r ^ (-(M.d : ℝ) / 2) * M.triSelf
              + (M.nablaTail (Real.sqrt r)).toReal) := hr
      _ ≤ ((M.ball r).ncard : ℝ)
          * (M.case3Driver c r + (M.nablaTail (Real.sqrt r)).toReal
              + 3 * r ^ (-(M.d : ℝ) / 2) * M.triSelf) := by
        apply mul_le_mul_of_nonneg_left _ hcard
        linarith

/-- **The Case-3 driver is antitone in the exponent** (for `r >= 1`): a smaller exponent makes
both `r^c` smaller (hence the triangle tail larger) and `r^{-c}` larger. -/
theorem case3Driver_mono {c c' r : ℝ}
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hcc' : c' ≤ c) (hr : 1 ≤ r) :
    M.case3Driver c r ≤ M.case3Driver c' r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have h1 : M.nablaTail (r ^ c) ≤ M.nablaTail (r ^ c') :=
    M.nablaTail_antitone (Real.rpow_le_rpow_of_exponent_le hr hcc')
  have h1' : (M.nablaTail (r ^ c)).toReal ≤ (M.nablaTail (r ^ c')).toReal :=
    ENNReal.toReal_mono (M.nablaTail_ne_top _ hTri) h1
  have h2 : r ^ (-c) ≤ r ^ (-c') :=
    Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  simp only [case3Driver]
  linarith

/-- **Case 3 of Proposition I.4.15, with the `ell = 3` and `ell = 4` polygon inputs both
discharged.**

The remaining hypotheses are exactly

* `hP` (Proposition I.4.2's first-moment asymptotic) and `hTri` (the triangle condition), which
  together produce the `ell = 4` polygon clause via the landed all-radius manufacturer
  `exists_polygonBound_four`;
* `hdecay`, the triangle condition's tail decay `grad_r -> 0`, which makes the driver vanish;
* `hgap`, Lemma I.4.17 at `p = 3`, `q = 0` (the genuine missing source input);
* `hgm`, the moment gap `E|K|^2 >= c₃ (E|K|)^3`.

No per-vertex `ell = 3` polygon factor appears: that clause is unsatisfiable
(`not_exists_case3_bundle`) and is replaced by the windowed bound of
`eventually_sum_polyK_three_ballF_le_rate`. -/
theorem p2ExclError_tendsto_zero_of_case3_windowed
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hdecay : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcM : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    {C3 C4 c₃ : ℝ} (_hC3 : 0 ≤ C3) (_hC4 : 0 ≤ C4) (hc₃ : 0 < c₃)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hgm : ∀ᶠ r : ℝ in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  obtain ⟨c, Cp, hc, hCp, hT4⟩ := M.exists_polygonBound_four hP hTri
  set c' : ℝ := min c (1 / 2) with hc'_def
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'2 : c' ≤ 1 / 2 := min_le_right _ _
  have hc'c : c' ≤ c := min_le_left _ _
  have hT4' : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c' r * (M.cutMassAt r 0).toReal := by
    intro r hr x
    refine (hT4 r (lt_of_lt_of_le one_pos hr) x).trans ?_
    have hmono : M.case3Driver c r ≤ M.case3Driver c' r :=
      M.case3Driver_mono hTri hc'c hr
    have hχnn : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hmono hχnn, hCp]
  have hdrv' : Tendsto (M.case3Driver c') atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ c') atTop atTop := tendsto_rpow_atTop hc'
    have h2 : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c')).toReal) atTop (𝓝 0) :=
      hdecay.comp h1
    have h3 : Tendsto (fun r : ℝ => r ^ (-c')) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc'
    have hmain : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c')).toReal + r ^ (-c'))
        atTop (𝓝 0) := by
      simpa using h2.add h3
    have hfun : (fun r : ℝ => (M.nablaTail (r ^ c')).toReal + r ^ (-c')) = M.case3Driver c' :=
      rfl
    rw [hfun] at hmain
    exact hmain
  exact M.p2ExclError_tendsto_zero_of_windowed_ell_three hβ hP hTri hc' hc'2 hCp.le _hC3 _hC4
    hc₃ h2 hcM hgap hT4' hgm hdrv'

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## Logarithmic integrability of the repaired Case-3 error -/

/-- **Polynomial decay is logarithmically integrable**: `r ↦ r^{-d/2}` is logarithmically
integrable for `d ≥ 1`.  This is the landed `isLogErrorFunction_const_rpow_neg` (i.e.
`∫_1^∞ r^{-d/2-1} dr < ∞`) with the constant `1`. -/
theorem logIntegrable_rpow_neg_half (hd : 1 ≤ M.d) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => r ^ (-(M.d : ℝ) / 2)) := by
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast hd
  have h := Analysis.isLogErrorFunction_const_rpow_neg (a := (M.d : ℝ) / 2) (by linarith)
    (c := 1) one_pos
  have h1 : Analysis.LogarithmicallyIntegrable (fun r : ℝ => (1 : ℝ) * r ^ (-((M.d : ℝ) / 2))) :=
    h.1
  simpa only [one_mul, neg_div] using h1

/-- **`grad_{sqrt r}` is logarithmically integrable when the driver is**, given measurability of
`r ↦ (grad_r).toℝ`.  The comparison is `grad_{sqrt r} ≤ grad_{r^c} ≤ driver` for `c ≤ 1/2` and
`r ≥ 1` (Lemma I.4.19's change of variables, in the monotone direction). -/
theorem logIntegrable_nablaTail_sqrt {c : ℝ} (hTri :
    PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hc2 : c ≤ 1 / 2)
    (hmeas : Measurable (fun r : ℝ => (M.nablaTail r).toReal))
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c)) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => (M.nablaTail (Real.sqrt r)).toReal) := by
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le
    (hmeas.comp Real.continuous_sqrt.measurable) hlogdrv ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hcle : r ^ c ≤ Real.sqrt r := by
    have h1 : r ^ c ≤ r ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr hc2
    rwa [← Real.sqrt_eq_rpow] at h1
  have hmono : M.nablaTail (Real.sqrt r) ≤ M.nablaTail (r ^ c) := M.nablaTail_antitone hcle
  have hle : (M.nablaTail (Real.sqrt r)).toReal ≤ (M.nablaTail (r ^ c)).toReal :=
    ENNReal.toReal_mono (M.nablaTail_ne_top _ hTri) hmono
  have hdrv : (M.nablaTail (r ^ c)).toReal ≤ M.case3Driver c r := by
    have hpos : (0 : ℝ) < r ^ (-c) := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hr) (-c)
    simp only [case3Driver]
    linarith
  have hnn : (0 : ℝ) ≤ (M.nablaTail (Real.sqrt r)).toReal := M.nablaTail_toReal_nonneg _
  have hdrvnn : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
  rw [abs_of_nonneg hnn, abs_of_nonneg hdrvnn]
  exact hle.trans hdrv

/-- **Logarithmic integrability of the repaired Case-3 error.**

The majorant of `p2ExclError_le_of_windowed_ell_three`,
`(C₃/c₃)((1+δ)/(1-δ) r^{-d/2} grad(0,0) + grad_{sqrt r}) + (C₄ Cp/c₃) driver`, is logarithmically
integrable: the first summand by `logIntegrable_rpow_neg_half`, the second by
`logIntegrable_nablaTail_sqrt`, the last by hypothesis (Lemma I.4.19).  The only extra input beyond
`p2ExclError_tendsto_zero_of_windowed_ell_three` is measurability of `r ↦ E_{2,r}` (the same
obligation as `Case3.lean`'s `hmeasE2`) and of the model's triangle tail. -/
theorem logIntegrable_p2ExclError_of_windowed_ell_three
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {c Cp C3 C4 c₃ : ℝ} (_hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (_hCp : 0 ≤ Cp) (_hC3 : 0 ≤ C3) (_hC4 : 0 ≤ C4) (hc₃ : 0 < c₃)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcM : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hT4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hgm : ∀ᶠ r : ℝ in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c))
    (hmeasE2 : Measurable M.p2ExclError)
    (hmeasNab : Measurable (fun r : ℝ => (M.nablaTail r).toReal)) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨c₀, hc₀, hχall⟩ := I418C.ChiInput.exists_chi_lower_uniform_and_finite M hβ hP
  have hχev : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (hχall r hr).2
  have hrate := M.eventually_sum_polyK_three_ballF_le_rate (δ := 1 / 2)
    (by norm_num) (by norm_num) hχev hTri
  have hlogpow := M.logIntegrable_rpow_neg_half M.hd
  have hlognab := M.logIntegrable_nablaTail_sqrt hTri hc2 hmeasNab hlogdrv
  have hlogmaj : Analysis.LogarithmicallyIntegrable (fun r : ℝ =>
      (C3 / c₃) * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf
        + (M.nablaTail (Real.sqrt r)).toReal) + (C4 * Cp / c₃) * M.case3Driver c r) := by
    have h1 : Analysis.LogarithmicallyIntegrable
        (fun r : ℝ => (3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf) := by
      have h := VolumeMoments.FirstMoment.logIntegrable_const_mul (3 * M.triSelf) hlogpow
      simpa only [mul_comm, mul_left_comm, mul_assoc] using h
    have h2 : Analysis.LogarithmicallyIntegrable (fun r : ℝ =>
        (3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf + (M.nablaTail (Real.sqrt r)).toReal) :=
      VolumeMoments.FirstMoment.logIntegrable_add h1 hlognab
    have h3 := VolumeMoments.FirstMoment.logIntegrable_const_mul (C3 / c₃) h2
    have h4 := VolumeMoments.FirstMoment.logIntegrable_const_mul (C4 * Cp / c₃) hlogdrv
    exact VolumeMoments.FirstMoment.logIntegrable_add h3 h4
  refine Analysis.LogarithmicallyIntegrable.of_eventually_abs_le hmeasE2 hlogmaj ?_
  filter_upwards [hrate, hgm, eventually_ge_atTop (1 : ℝ)] with r hW hgmr hr
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have hb : ((M.ball r).ncard : ℝ) ≠ 0 := by
    have := M.ball_ncard_pos r hr0
    positivity
  have hW3 : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
      ≤ ((M.ball r).ncard : ℝ)
        * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf
            + (M.nablaTail (Real.sqrt r)).toReal) := by
    refine hW.trans (le_of_eq ?_)
    norm_num
  have hstep := M.p2ExclError_le_of_windowed_ell_three (c := c) (Cp := Cp) (C3 := C3)
    (C4 := C4) (c₃ := c₃)
    (W := ((M.ball r).ncard : ℝ)
      * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf + (M.nablaTail (Real.sqrt r)).toReal))
    (r := r) _hCp _hC3 _hC4 hc₃ hr (h2 r hr) (hcM r hr) (hgap r hr) hW3 (hT4 r hr) hgmr
  rw [mul_div_cancel_left₀
    ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf + (M.nablaTail (Real.sqrt r)).toReal) hb] at hstep
  have hE0 : (0 : ℝ) ≤ M.p2ExclError r :=
    M.p2ExclError_nonneg r hr0 (h2 r hr)
  have hmaj0 : (0 : ℝ) ≤ (C3 / c₃) * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf
      + (M.nablaTail (Real.sqrt r)).toReal) + (C4 * Cp / c₃) * M.case3Driver c r := by
    have htri : (0 : ℝ) ≤ M.triSelf := M.triPoint_nonneg 0 0
    have h1 : (0 : ℝ) ≤ (3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hr0 _)) htri
    have h2' : (0 : ℝ) ≤ (M.nablaTail (Real.sqrt r)).toReal := M.nablaTail_toReal_nonneg _
    have h3 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
    have h4 : (0 : ℝ) ≤ C3 / c₃ := div_nonneg _hC3 hc₃.le
    have h5 : (0 : ℝ) ≤ C4 * Cp / c₃ := div_nonneg (mul_nonneg _hC4 _hCp) hc₃.le
    exact add_nonneg (mul_nonneg h4 (add_nonneg h1 h2')) (mul_nonneg h5 h3)
  rw [abs_of_nonneg hE0, abs_of_nonneg hmaj0]
  exact hstep

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The Case-3 conclusion with both polygon clauses discharged -/

/-- **Logarithmic integrability of the repaired `E_{2,r}`, packaged.**  The triangle tail
`r ↦ (∇_r).toℝ` is taken in the source's log-error form (`IsLogErrorFunction`, Lemma I.4.13 +
Lemma I.4.19), which supplies both its measurability and the log-integrability of every
`∇_{r^c} + r^{-c}`; the `ell = 4` and `ell = 3` polygon clauses are discharged as in
`p2ExclError_tendsto_zero_of_case3_windowed`. -/
theorem logIntegrable_p2ExclError_of_case3_windowed
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hTail : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal))
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcM : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    {C3 C4 c₃ : ℝ} (_hC3 : 0 ≤ C3) (_hC4 : 0 ≤ C4) (hc₃ : 0 < c₃)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hgm : ∀ᶠ r : ℝ in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hmeasE2 : Measurable M.p2ExclError) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨c, Cp, hc, hCp, hT4⟩ := M.exists_polygonBound_four hP hTri
  set c' : ℝ := min c (1 / 2) with hc'_def
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'2 : c' ≤ 1 / 2 := min_le_right _ _
  have hc'c : c' ≤ c := min_le_left _ _
  have hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c') :=
    (Analysis.isLogErrorFunction_nablaTail_add_rpow_neg M hTail hc').1
  have hmeasNab : Measurable (fun r : ℝ => (M.nablaTail r).toReal) := hTail.1.1
  have hT4' : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c' r * (M.cutMassAt r 0).toReal := by
    intro r hr x
    refine (hT4 r (lt_of_lt_of_le one_pos hr) x).trans ?_
    have hmono : M.case3Driver c r ≤ M.case3Driver c' r :=
      M.case3Driver_mono hTri hc'c hr
    have hχnn : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hmono hχnn, hCp]
  exact M.logIntegrable_p2ExclError_of_windowed_ell_three hβ hP hTri hc' hc'2 hCp.le _hC3
    _hC4 hc₃ h2 hcM hgap hT4' hgm hlogdrv hmeasE2 hmeasNab

/-- **Proposition I.4.15, Case 3 (triangle condition), with the `ell = 3` polygon clause
replaced by the windowed bound that is actually true.**

`E_{b_c,r}|K|^2 / r^{3α} → A > 0`, from

* `hac`, `hae` — the corner-safe radial identity for `r ↦ E_{b_c,r}|K|^2`;
* `h1`, `h2` — finiteness of the first two cutoff moments on the tail;
* `hP` (Proposition I.4.2), `hTri` (triangle condition) and `hTail` (Lemma I.4.13's logarithmic
  tail decay of `∇_r`), which produce the `ell = 4` polygon clause and the vanishing driver;
* `hgap` — Lemma I.4.17 at `p = 3`, `q = 0` (carried, not proved);
* `hgm` — the moment gap;
* `hmeasE2`, `hmeasEbar` — the two measurability obligations (as in `Case3.lean`);
* `hlogH`, `hlogE0`, `hH` — the first-moment inputs of Proposition I.4.2.

The false `hT3` of `secondMoment_asymptotic_case3` does not appear. -/
theorem tendsto_div_two_of_case3_windowed
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hβ : (M.betaCrit : ℝ) ≠ 0) (hβpos : 0 < (M.betaCrit : ℝ))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hTail : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal))
    (hcM : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    {C3 C4 c₃ : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hc₃ : 0 < c₃)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hgm : ∀ᶠ r : ℝ in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    (hH : Tendsto M.p2H atTop (𝓝 0)) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have h2' : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤ :=
    fun r hr => h2 r (le_trans hr₀1 hr)
  have hdecay : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0) := hTail.2
  have hE2 : Tendsto M.p2ExclError atTop (𝓝 0) :=
    M.p2ExclError_tendsto_zero_of_case3_windowed hβpos hP hTri hdecay h2' hcM hC3 hC4 hc₃
      hgap hgm
  have hlogE2 : Analysis.LogarithmicallyIntegrable M.p2ExclError :=
    M.logIntegrable_p2ExclError_of_case3_windowed hβpos hP hTri hTail h2' hcM hC3 hC4 hc₃
      hgap hgm hmeasE2
  have hlogEbar : Analysis.LogarithmicallyIntegrable M.p2Ebar :=
    M.logIntegrable_p2Ebar hmeasEbar hlogE2 hlogH hlogE0 hH
  exact M.tendsto_div_two hα hr₀ hβ hac hae h1 h2 hE2 hH (PivotFlux.tendsto_cutE0 M) hlogEbar

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## Axiom audit of the key exports -/

section Audit

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_polyK_three_ballF_le_two_scale
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_ball_sqrt_ncard_ratio_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_sum_polyK_three_ballF_le_rate
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_windowed_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_of_windowed_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_windowed_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_forall_polyK_three_le_case3Driver_of_tendsto
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_bundle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_sqrt_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_repaired_case3_bundle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3Driver_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_case3_windowed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_rpow_neg_half
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_nablaTail_sqrt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_windowed_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_case3_windowed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_div_two_of_case3_windowed

end Audit
