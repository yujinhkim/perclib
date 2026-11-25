/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

The source open-triangle tail and uniform polygon estimates with its correct constant.
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Consumer
public import PercLib.CriticalLRP.Analysis.TriTail

open MeasureTheory Measure
open scoped ENNReal NNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C

variable (M : SourceModelData)

-- The model-norm tail itself is defined in `Polygon/Defs.lean`.

/-- Membership form: `∇_{β_c}(0,y) ≤ ∇_r` for every `y` of norm at least `r`. -/
theorem le_nablaTail {r : ℝ} {y : M.V} (hy : r ≤ M.S.dist 0 y) :
    PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y
      ≤ M.nablaTail r :=
  le_iSup₂ (f := fun y (_ : r ≤ M.S.dist 0 y) =>
    PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) y hy

/-- **Finiteness of the tail from the triangle condition**: `∇_r ≤ ∇_{β_c} < ∞`.

This is the constant supplied by the Cauchy–Schwarz/diagonal bound
`∇(0,y) ≤ ∇_{β_c}(0,0)`; it is what makes `∇_{r^c}` a genuine real number rather than `⊤`. -/
theorem nablaTail_le_self (r : ℝ) :
    M.nablaTail r
      ≤ PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 := by
  refine iSup_le fun y => iSup_le fun _ => ?_
  exact PercLib.CriticalLRP.TriTail.openTriangle_le_diagonal M.kernel_shift
    M.kernel_nonneg M.betaCrit y

theorem nablaTail_ne_top (r : ℝ)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    M.nablaTail r ≠ ⊤ :=
  ne_top_of_le_ne_top hTri.ne (M.nablaTail_le_self r)

/-- The tail is monotone in the cutoff radius (as in the source, `∇_r` is decreasing in `r`). -/
theorem nablaTail_antitone : Antitone M.nablaTail := by
  intro a b hab
  refine iSup_le fun y => iSup_le fun hy => ?_
  exact le_iSup₂ (f := fun y (_ : a ≤ M.S.dist 0 y) =>
      PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
    y (le_trans hab hy)

/-- **`htailc`, discharged**: on the far region `‖y‖ ≥ r^cc`, the open triangle is at most the
tail constant `∇_{r^cc}`. -/
theorem triPoint_le_nablaTail {r : ℝ} {y : M.V}
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hy : r ≤ M.S.dist 0 y) :
    M.triPoint 0 y ≤ (M.nablaTail r).toReal :=
  ENNReal.toReal_mono (M.nablaTail_ne_top r hTri) (M.le_nablaTail hy)

/-- **`htrc`, discharged**: the tail constant is nonnegative. -/
theorem nablaTail_toReal_nonneg (r : ℝ) : 0 ≤ (M.nablaTail r).toReal :=
  ENNReal.toReal_nonneg

/-- The tail constant never exceeds the triangle constant `∇_{β_c}` (`∇_{r^c} ≤ ∇`). -/
theorem nablaTail_toReal_le_triSelf (r : ℝ)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    (M.nablaTail r).toReal ≤ M.triSelf :=
  ENNReal.toReal_mono hTri.ne (M.nablaTail_le_self r)

/-- Identification with the landed source tail `TriTail.openTriangleTail` (which is stated at the
lattice sup-norm `FiniteVolume.latticeDist`) whenever the model norm is that norm. -/
theorem nablaTail_eq_openTriangleTail (r : ℝ)
    (h : ∀ y : M.V, M.S.dist 0 y = FiniteVolume.latticeDist 0 y) :
    M.nablaTail r
      = PercLib.CriticalLRP.TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit r := by
  unfold nablaTail PercLib.CriticalLRP.TriTail.openTriangleTail
  refine iSup_congr fun y => ?_
  rw [h y]

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.I418C

open PercLib.CriticalLRP Orchestration

/-- **Lemma I.4.18 (`ℓ ≥ 4`) at the source's tail constant, for any admissible `c`.**

This is the assembly of `Polygon.Core.polygon_bound` re-run at the model level so that
(i) the RHS tail term is the source object `∇_{r^c} = SourceModelData.nablaTail (r^cc)`
rather than an unconstrained real, and
(ii) the only condition on the exponent is the genuinely needed `cc ≤ α/(2d)` (no sign
condition is required: `r > 0` here).

The source takes `R = r^{α/(2d)}`, so `cc = α/(2d)` is admissible and gives the printed
`C (∇_{r^c} + r^{-c}) (E|K|)^{ℓ-3}`; the previously landed choice `cc = α/(4d)` is the weaker
special case also recorded below. -/
theorem source_polygon_bound_tail_cc
    (M : SourceModelData)
    (r R : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hccd : cc ≤ M.α / (2 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ))))
    (hχ : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * ((M.nablaTail (r ^ cc)).toReal + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hr
  have hd1 : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
  have hcc2 : cc ≤ M.α / 2 := by
    have h : M.α / (2 * (M.d : ℝ)) ≤ M.α / 2 := by
      refine div_le_div_of_nonneg_left M.hα.le (by norm_num) ?_
      linarith
    linarith
  have hH : PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf (M.cutMassAt r 0).toReal :=
    M.source_powerInputs r hχfin hTri hB2 hB3 hlink
  have htail : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y →
      polyK (M.cutTwoPoint r) 3 0 y ≤ (M.nablaTail (r ^ cc)).toReal := fun y hy =>
    M.source_triTail r cc ((M.nablaTail (r ^ cc)).toReal) hB2 hB3 hlink
      (fun z hz => M.triPoint_le_nablaTail (r := r ^ cc) hTri hz) y hy
  have hRc : r ^ cc ≤ R := by
    rw [hR]
    exact Real.rpow_le_rpow_of_exponent_le hr hccd
  have hnab : (0 : ℝ) ≤ M.triSelf := le_trans (hH.nonneg 3 0 0) (hH.triSup 0)
  have hsplit := split_bound hH s (fun y => M.S.dist 0 y) R ((M.nablaTail (r ^ cc)).toReal)
    (M.nablaTail_toReal_nonneg _) hfar (fun y hy => htail y (le_trans hRc hy)) (ell := ell) hell
  have hRd : R ^ (M.d : ℝ) = r ^ (M.α / 2) := rpow_card hr M.hd hR
  have hcard' : M.triSelf * (s.card : ℝ) * ((M.cutMassAt r 0).toReal) ^ (ell - 4)
      ≤ M.triSelf * K * r ^ (M.α / 2) * ((M.cutMassAt r 0).toReal) ^ (ell - 4) := by
    have hy : (0 : ℝ) ≤ ((M.cutMassAt r 0).toReal) ^ (ell - 4) :=
      pow_nonneg ENNReal.toReal_nonneg _
    have h1 : (s.card : ℝ) ≤ K * r ^ (M.α / 2) := by
      refine le_trans hcard ?_
      rw [hRd]
    have h2 : M.triSelf * (s.card : ℝ) ≤ M.triSelf * (K * r ^ (M.α / 2)) :=
      mul_le_mul_of_nonneg_left h1 hnab
    calc M.triSelf * (s.card : ℝ) * ((M.cutMassAt r 0).toReal) ^ (ell - 4)
        ≤ M.triSelf * (K * r ^ (M.α / 2)) * ((M.cutMassAt r 0).toReal) ^ (ell - 4) :=
          mul_le_mul_of_nonneg_right h2 hy
      _ = M.triSelf * K * r ^ (M.α / 2) * ((M.cutMassAt r 0).toReal) ^ (ell - 4) := by ring
  have hnear := near_arith (nablaT := M.triSelf) (K := K) (c₀ := c₀) (r := r) (α := M.α)
    (cc := cc) (χ := (M.cutMassAt r 0).toReal) (ell := ell) hnab hK hc₀ hr hell hcc2 hχ
  have hC1 : (0 : ℝ) < max 1 (M.triSelf * K / c₀) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCp : M.triSelf * K / c₀ ≤ max 1 (M.triSelf * K / c₀) := le_max_right _ _
  have hχn : (0 : ℝ) ≤ ((M.cutMassAt r 0).toReal) ^ (ell - 3) :=
    pow_nonneg ENNReal.toReal_nonneg _
  have hrm : (0 : ℝ) ≤ r ^ (-cc) := le_of_lt (Real.rpow_pos_of_pos hr0 _)
  have hsum :
      (M.nablaTail (r ^ cc)).toReal * ((M.cutMassAt r 0).toReal) ^ (ell - 3)
        + (M.triSelf * K / c₀) * r ^ (-cc) * ((M.cutMassAt r 0).toReal) ^ (ell - 3)
      ≤ max 1 (M.triSelf * K / c₀) *
        ((M.nablaTail (r ^ cc)).toReal + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
    have h1 : (M.nablaTail (r ^ cc)).toReal * ((M.cutMassAt r 0).toReal) ^ (ell - 3)
        ≤ max 1 (M.triSelf * K / c₀) * (M.nablaTail (r ^ cc)).toReal
          * ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
      have hle : (M.nablaTail (r ^ cc)).toReal
          ≤ max 1 (M.triSelf * K / c₀) * (M.nablaTail (r ^ cc)).toReal := by
        nlinarith [le_max_left (1 : ℝ) (M.triSelf * K / c₀), M.nablaTail_toReal_nonneg (r ^ cc)]
      exact mul_le_mul_of_nonneg_right hle hχn
    have h2 : (M.triSelf * K / c₀) * r ^ (-cc) * ((M.cutMassAt r 0).toReal) ^ (ell - 3)
        ≤ max 1 (M.triSelf * K / c₀) * r ^ (-cc)
          * ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp hrm) hχn
    have h3 : max 1 (M.triSelf * K / c₀) * (M.nablaTail (r ^ cc)).toReal
          * ((M.cutMassAt r 0).toReal) ^ (ell - 3)
        + max 1 (M.triSelf * K / c₀) * r ^ (-cc) * ((M.cutMassAt r 0).toReal) ^ (ell - 3)
        = max 1 (M.triSelf * K / c₀) * ((M.nablaTail (r ^ cc)).toReal + r ^ (-cc))
          * ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by ring
    linarith [h1, h2, h3]
  have hdiag := fun x => M.source_polyK_le_diag r hχfin ell x
  intro x
  linarith [hdiag x, hsplit, hcard', hnear, hsum]

/-- **Lemma I.4.18 (`ℓ ≥ 4`) with the source's own constant `c = α/(2d)`.**

Instantiation of `source_polygon_bound_tail_cc` at `cc = α/(2d)` (the value forced by the
source's choice `R = r^{α/(2d)}`), with the tail `∇_{r^c}` read as the genuine source supremum. -/
theorem source_polygon_bound_tail_source_c
    (M : SourceModelData)
    (r R : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = M.α / (2 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ))))
    (hχ : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * ((M.nablaTail (r ^ cc)).toReal + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) :=
  source_polygon_bound_tail_cc M r R s hr hc₀ hK hχfin hTri hB2 hB3 hlink hell
    (le_of_eq hct) hfar hcard hR hχ

/-- **The `c = α/(4d)` special case** matching the previously landed constant choice. -/
theorem source_polygon_bound_of_cutoff_data_tail
    (M : SourceModelData)
    (r R : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = M.α / (4 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ))))
    (hχ : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * ((M.nablaTail (r ^ cc)).toReal + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  have hd1 : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
  refine source_polygon_bound_tail_cc M r R s hr hc₀ hK hχfin hTri hB2 hB3 hlink hell
    ?_ hfar hcard hR hχ
  rw [hct]
  have h2 : (0 : ℝ) < 2 * (M.d : ℝ) := by linarith
  refine div_le_div_of_nonneg_left M.hα.le h2 ?_
  linarith

/-- **The honest `ℓ = 3` case**: the printed display of Lemma I.4.18 at `ℓ = 3` would read
`T^3(0,x) ≤ C(∇_{r^c} + r^{-c})`, which cannot hold uniformly in `r` under the source's own
`∇_r → 0` (while `T^3(0,0) ≥ T(0,0)^3 = 1`).  What *is* available, and what the applications
use, is the constant bound `T^3(0,x) ≤ ∇_{β_c} = triSelf`: diagonal maximality at `ℓ = 3`
composed with `PowerInputs.ell_three_le`. -/
theorem source_polyK_three_le_triSelf
    (M : SourceModelData) (r : ℝ) (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) 3 0 x ≤ M.triSelf := by
  intro x
  refine (M.source_polyK_le_diag r hχfin 3 x).trans ?_
  exact (M.source_powerInputs r hχfin hTri hB2 hB3 hlink).ell_three_le

end PercLib.CriticalLRP.I418C
