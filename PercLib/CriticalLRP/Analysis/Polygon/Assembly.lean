/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.ChiInput
public import PercLib.CriticalLRP.Analysis.Polygon.NearBall
public import PercLib.CriticalLRP.Analysis.Polygon.TailConstant
public import PercLib.CriticalLRP.Analysis.Polygon.UncutLink

/-!
# A source-facing polygon assembly for Lemma I.4.18
-/

open MeasureTheory Filter Topology

open scoped ENNReal NNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I418C

open PercLib.CriticalLRP Orchestration

/-- The source-facing polygon estimate for `ell ≥ 4`, reduced to its finite-triangle and
first-moment hypotheses. The constants `c,C` are independent of the order, cutoff radius and
point. The diagonal equality is the source's diagonal-maximality statement, not only a bound.

This proves the content for `r ≥ 1`; the separate small-radius assembly and the triangle-case
first-moment asymptotic remain honest inputs. No unconditional `ell = 3` statement is made. -/
theorem exists_uniform_source_polygon_bound_of_triangle_first_moment
    (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {ell : ℕ}, 4 ≤ ell → ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      (⨆ x : M.V, polyK (M.cutTwoPoint r) ell 0 x) = polyK (M.cutTwoPoint r) ell 0 0 ∧
      polyK (M.cutTwoPoint r) ell 0 x
        ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) *
          ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  have hβ : 0 < (M.betaCrit : ℝ) := ChiInput.betaCrit_pos_of_tendsto_chi_div M hP
  obtain ⟨c₀, hc₀, hχu⟩ := ChiInput.exists_chi_lower_uniform M hβ hP
  obtain ⟨Knear, hKnear, hnear⟩ := NearBall.exists_near_ball M
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
  refine ⟨M.α / (2 * (M.d : ℝ)), max 1 (M.triSelf * Knear / c₀),
    div_pos M.hα (mul_pos (by norm_num) hdpos), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ell hell r hr x
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have hχfin : M.cutMassAt r 0 ≠ ⊤ :=
    ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ hrpos (hχu r hrpos)
  have hdiag : ∀ y : M.V, polyK (M.cutTwoPoint r) ell 0 y
      ≤ polyK (M.cutTwoPoint r) ell 0 0 :=
    fun y => M.source_polyK_le_diag r hχfin ell y
  constructor
  · have hbdd : BddAbove (Set.range (fun y : M.V => polyK (M.cutTwoPoint r) ell 0 y)) := by
      refine ⟨polyK (M.cutTwoPoint r) ell 0 0, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hdiag y
    exact le_antisymm (ciSup_le hdiag) (le_ciSup hbdd (0 : M.V))
  · obtain ⟨hB2, hB3, hlink⟩ := M.hB2_hB3_hlink_derived hTri
    have hexp : 0 ≤ M.α / (2 * (M.d : ℝ)) := div_nonneg M.hα.le (by positivity)
    have hnearR : 1 ≤ r ^ (M.α / (2 * (M.d : ℝ))) := Real.one_le_rpow hr hexp
    obtain ⟨s, hfar, hcard⟩ := hnear _ hnearR
    exact source_polygon_bound_tail_cc (c₀ := c₀) (K := Knear)
      (cc := M.α / (2 * (M.d : ℝ))) (ell := ell) M r
      (r ^ (M.α / (2 * (M.d : ℝ)))) s hr hc₀ hKnear.le
      hχfin hTri hB2 hB3 hlink hell
      le_rfl hfar hcard rfl (hχu r hrpos) x

end PercLib.CriticalLRP.I418C
