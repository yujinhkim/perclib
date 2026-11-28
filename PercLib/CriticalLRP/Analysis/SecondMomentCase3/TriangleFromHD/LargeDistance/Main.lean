/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m1.
Latest independent rebuild at production HEAD `bd25afb1130f7fe93446b447f9a68a4d3aba08cc`; reviewed scratch source `.scratch/review-smwznoz6j/m1/Main.lean`.

Swarm `smwznoz6j`, member `m1`, direction `d2` — (G) non-vacuity of the literal Case 3 of (HD).

# What the literal (HD)(3) says at short distances, and the exact missing estimate

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, (HD) Case 3, p. 9.

This file proves three groups of statements about production's `SourceModelData.Case3HD`
(`TriangleFromHD/Defs.lean`), whose displayed content is

```
P_{βc}(x ↔ y) ⪯ (log ‖x − y‖)^{-1} ‖x − y‖^{-4}   for all x ≠ y,   d = 6, α = 2.
```

## §1 The distance content that the display silently assumes

* `one_le_srcNorm_of_case3HD` — `Case3HD` forces `1 ≤ ‖x − y‖` at every pair `x ≠ y`.  Indeed for
  `‖x − y‖ < 1` the printed right-hand side is *negative* while `P_{βc}(x ↔ y) ≥ 0`.
* `twoPoint_eq_zero_of_dist_eq_one` — at `‖x − y‖ = 1` the printed factor is `0⁻¹ = 0`, so
  `Case3HD` forces `P_{βc}(x ↔ y) = 0`.
* `not_case3HD_flatModel6` — the flattened normalized source norm of `Defs.lean` (`d = 6`, unit
  ball of volume `1`, `ρ(e₁) = 1/2`) carries a genuine `SourceModelData` at `d = 6`, `α = 2` on
  which `Case3HD` is **false**.  Hence `Case3HD` is not a consequence of the paper's normalization
  (∗) alone: it additionally asserts a lower bound on lattice distances.

## §2 The repair

`Case3HDPos` (bound where the printed log factor is positive) and `Case3HDLarge` (bound at
`4 < ‖x − y‖`, the region used by the convolution argument) are introduced in `Defs.lean`.  Here:

* `case3HDPos_of_case3HD`, `case3HDLarge_of_case3HDPos` — the literal hypothesis implies both;
* `exists_abs_tau_le_Wt_of_case3HDLarge` — `Case3HDLarge` produces the positive-log majorant
  `|τ(z)| ≤ K (1 + ‖z‖)^{-4} (log (2 + ‖z‖))^{-1}` that `TriangleFromHD/Pointwise` extracts from
  the literal hypothesis;
* `case3HDLarge_of_Wt_majorant` — conversely the majorant yields `Case3HDLarge`.

So `Case3HDLarge` is *equivalent* to the positive-log majorant consumed downstream
(`case3HDLarge_iff_Wt_majorant`), and it makes no assertion at short distances.  This is the
precise sense in which the exact missing model estimate is the distance-restricted form of
(HD)(3): it is the content the production chain uses, with the near-diagonal sign obstruction
removed.  No upper-to-lower inference and no lace-expansion input is used anywhere below.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Pointwise
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Defs

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## §1 The distance content of the literal `Case3HD` -/

/-- **The literal (HD)(3) forces every nonzero lattice distance to be at least one.**  For
`0 < ‖x − y‖ < 1` the printed right-hand side is negative (`log` negative, `‖x − y‖^{-4}`
positive, constant positive) while `P_{βc}(x ↔ y) ≥ 0`, so the displayed inequality fails. -/
theorem one_le_srcNorm_of_case3HD (h : M.Case3HD) {x y : M.V} (hxy : x ≠ y) :
    1 ≤ M.S.ρ (toVec (x - y)) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  have hs0 : 0 < M.S.ρ (toVec (x - y)) := M.S.dist_pos hxy
  have hlog : Real.log (M.S.ρ (toVec (x - y))) < 0 := Real.log_neg hs0 hlt
  have hinv : (Real.log (M.S.ρ (toVec (x - y))))⁻¹ < 0 := inv_lt_zero'.mpr hlog
  have hpow : 0 < (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) := Real.rpow_pos_of_pos hs0 _
  have hrhs : C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
      * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC hinv) hpow
  have hlhs : 0 ≤ M.twoPoint M.betaCrit x y := by
    rw [← M.tau_eq_twoPoint_sub x y]
    exact M.tau_nonneg (y - x)
  linarith [hb x y hxy]

/-- **The literal (HD)(3) forces the two-point function to vanish at distance exactly one.**
Lean's `(0 : ℝ)⁻¹ = 0`, so at `‖x − y‖ = 1` the printed right-hand side is `0`. -/
theorem twoPoint_eq_zero_of_dist_eq_one (h : M.Case3HD) {x y : M.V} (hxy : x ≠ y)
    (h1 : M.S.ρ (toVec (x - y)) = 1) : M.twoPoint M.betaCrit x y = 0 := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  have hle : M.twoPoint M.betaCrit x y
      ≤ C * (Real.log (1 : ℝ))⁻¹ * (1 : ℝ) ^ (-(M.d : ℝ) + 2) := by
    simpa only [h1] using hb x y hxy
  have hzero : C * (Real.log (1 : ℝ))⁻¹ * (1 : ℝ) ^ (-(M.d : ℝ) + 2) = 0 := by simp
  rw [hzero] at hle
  have hnn : 0 ≤ M.twoPoint M.betaCrit x y := by
    rw [← M.tau_eq_twoPoint_sub x y]
    exact M.tau_nonneg (y - x)
  linarith

/-- **`Case3HD` is false on the flattened normalized source norm at `d = 6`, `α = 2`.**  The
nonzero lattice vector `e₁` has source norm `1/2`, so §1 applies.  This does not assert anything
about the intended (Euclidean-like) normalization: it shows that the literal hypothesis is an
extra assumption on the norm, not a consequence of the paper's normalization (∗). -/
theorem not_case3HD_flatModel6 : ¬ flatModel6.Case3HD := by
  intro h
  have hne : (0 : Fin 6 → ℤ) ≠ FlatSix.flat6E1 := by
    intro he
    have h0 := congrFun he 0
    simp [FlatSix.flat6E1] at h0
  have hge := one_le_srcNorm_of_case3HD flatModel6 h
    (x := (0 : Fin 6 → ℤ)) (y := FlatSix.flat6E1) hne
  have hone : flatModel6.S.ρ (toVec ((0 : Fin 6 → ℤ) - FlatSix.flat6E1)) = 1 / 2 :=
    FlatSix.flatSourceNorm6_dist_e1
  have hge' : (1 : ℝ) ≤ 1 / 2 := hone ▸ hge
  norm_num at hge'

/-! ## §2 The distance-restricted forms imply the literal one, and are implied by it -/

/-- The literal (HD)(3) implies its positive-log form. -/
theorem case3HDPos_of_case3HD (h : M.Case3HD) : M.Case3HDPos := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  exact ⟨hd6, hα2, C, hC, fun x y hxy _ => hb x y hxy⟩

/-- The positive-log form implies the form used by the convolution argument. -/
theorem case3HDLarge_of_case3HDPos (h : M.Case3HDPos) : M.Case3HDLarge := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  exact ⟨hd6, hα2, C, hC, fun x y hxy h4 => hb x y hxy (by linarith)⟩

/-- The literal (HD)(3) implies the form used by the convolution argument. -/
theorem case3HDLarge_of_case3HD (h : M.Case3HD) : M.Case3HDLarge :=
  M.case3HDLarge_of_case3HDPos (M.case3HDPos_of_case3HD h)

/-- **The literal (HD)(3) and its positive-log form differ exactly by the short-distance
condition.**  If every nonzero lattice distance is at least one and the two-point function
vanishes at distance exactly one, then `Case3HD` and `Case3HDPos` are equivalent: the only
pairs at which the printed display says more than its positive-log form are those with
`‖x − y‖ = 1`. -/
theorem case3HD_iff_case3HDPos_of_far
    (hfar : ∀ x y : M.V, x ≠ y → 1 ≤ M.S.ρ (toVec (x - y)))
    (hone : ∀ x y : M.V, x ≠ y → M.S.ρ (toVec (x - y)) = 1 → M.twoPoint M.betaCrit x y = 0) :
    M.Case3HD ↔ M.Case3HDPos := by
  constructor
  · exact M.case3HDPos_of_case3HD
  · intro h
    obtain ⟨hd6, hα2, C, hC, hb⟩ := h
    refine ⟨hd6, hα2, C, hC, fun x y hxy => ?_⟩
    rcases lt_or_eq_of_le (hfar x y hxy) with hlt | heq
    · exact hb x y hxy hlt
    · rw [← heq, hone x y hxy heq.symm]
      have hzero : C * (Real.log (1 : ℝ))⁻¹ * (1 : ℝ) ^ (-(M.d : ℝ) + 2) = 0 := by simp
      rw [hzero]

/-! ## §3 The positive-log majorant from `Case3HDLarge`, and the converse -/

/-- The source decay bound for `τ` from `Case3HDLarge`, in the printed shape but only on the
region `4 < ‖z‖` where the convolution argument uses it. -/
theorem tau_le_of_case3HDLarge (h : M.Case3HDLarge) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : M.V, z ≠ 0 → 4 < M.S.ρ (toVec z) →
      M.tau z ≤ C * (Real.log (M.S.ρ (toVec z)))⁻¹
        * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  refine ⟨C, hC, fun z hz h4 => ?_⟩
  have h0 : M.twoPoint M.betaCrit z 0
      ≤ C * (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) := by
    simpa only [sub_zero] using hb z 0 hz (by simpa only [sub_zero] using h4)
  have h1 : M.tau z = M.twoPoint M.betaCrit z 0 := by
    have h := M.tau_eq_twoPoint_sub (0 : M.V) z
    rw [sub_zero] at h
    rw [h]
    exact M.twoPoint_symm M.betaCrit 0 z
  rw [h1]
  exact h0

/-- **The positive-log majorant `Wt` from `Case3HDLarge`.**  This is
`TriangleFromHD/Pointwise.exists_abs_tau_le_Wt` with the literal hypothesis replaced by the
distance-restricted one; the proof is the same and uses the source bound only at `4 < ‖z‖`,
exactly where `log_inv_mul_rpow_le_Wt` applies. -/
theorem exists_abs_tau_le_Wt_of_case3HDLarge (h : M.Case3HDLarge) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : M.V,
      |M.tau z| ≤ K * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) := by
  obtain ⟨hd6, hα2, C, hC, hb⟩ := h
  obtain ⟨C', hC', hsrc⟩ := M.tau_le_of_case3HDLarge ⟨hd6, hα2, C, hC, hb⟩
  have hdR : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  have he : 0 < (M.d : ℝ) - 2 := by rw [hdR]; norm_num
  have hW4 : 0 < CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4 := CriticalLRPConv.Wt_pos (by norm_num)
  have hB : 0 < C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2) := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ ((M.d : ℝ) - 2) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hA : 0 < 1 / CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4 := by
    rw [one_div]
    exact inv_pos.mpr hW4
  refine ⟨max (1 / CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4)
    (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)) + 1, ?_, fun z => ?_⟩
  · have h := le_max_left (1 / CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4)
      (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2))
    linarith
  have hr : (0 : ℝ) ≤ M.S.ρ (toVec z) := M.sρ_nonneg z
  have hK1 : 1 / CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4
      ≤ max (1 / CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4)
        (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)) :=
    le_max_left _ _
  have hK2 : C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)
      ≤ max (1 / CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4)
        (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)) :=
    le_max_right _ _
  rw [abs_of_nonneg (M.tau_nonneg z)]
  rcases le_or_gt (M.S.ρ (toVec z)) 4 with hle4 | hgt4
  · have h1 := M.tau_le_one z
    have h2 : CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4
        ≤ CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) :=
      CriticalLRPConv.Wt_antitone he (by norm_num) hr hle4
    have hstep : (1 : ℝ) ≤
        (1 / CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 4)
          * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) := by
      have hh := mul_le_mul_of_nonneg_left h2 hA.le
      rw [one_div_mul_cancel (ne_of_gt hW4)] at hh
      exact hh
    refine h1.trans (hstep.trans ?_)
    refine mul_le_mul_of_nonneg_right (le_trans hK1 (le_add_of_nonneg_right (by norm_num))) ?_
    exact (CriticalLRPConv.Wt_pos hr).le
  · have hz : z ≠ 0 := by
      rintro rfl
      have h0 : M.S.ρ (toVec (0 : M.V)) = 0 := by rw [toVec_zero M, M.S.ρ_zero]
      rw [h0] at hgt4
      linarith
    have hsrcz := hsrc z hz hgt4
    have hexp : (-(M.d : ℝ) + 2) = -((M.d : ℝ) - 2) := by ring
    rw [hexp] at hsrcz
    have hlogstep : (Real.log (M.S.ρ (toVec z)))⁻¹
          * (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) ≤
        2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)
          * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) :=
      log_inv_mul_rpow_le_Wt he hgt4
    calc M.tau z ≤ C' * ((Real.log (M.S.ρ (toVec z)))⁻¹
          * (M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2))) := by
          rw [← mul_assoc]
          exact hsrcz
      _ ≤ C' * (2 * (2 : ℝ) ^ ((M.d : ℝ) - 2)
            * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z))) :=
          mul_le_mul_of_nonneg_left hlogstep hC'.le
      _ = (C' * 2 * (2 : ℝ) ^ ((M.d : ℝ) - 2))
            * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (le_trans hK2 (le_add_of_nonneg_right (by norm_num))) ?_
          exact (CriticalLRPConv.Wt_pos hr).le

/-- **The converse: the positive-log majorant yields `Case3HDLarge`.**  At `4 < s` we have
`(1 + s)^{-4} ≤ s^{-4}` and `log s ≤ log (2 + s)`, so the majorant is at most the printed
right-hand side. -/
theorem case3HDLarge_of_Wt_majorant (hd6 : M.d = 6) (hα2 : M.α = 2) {K : ℝ} (hK : 0 < K)
    (hmaj : ∀ z : M.V,
      |M.tau z| ≤ K * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z))) :
    M.Case3HDLarge := by
  refine ⟨hd6, hα2, K, hK, fun x y hxy h4 => ?_⟩
  have hs : 0 < M.S.ρ (toVec (y - x)) := M.S.dist_pos (Ne.symm hxy)
  have h4' : 4 < M.S.ρ (toVec (y - x)) := by
    have h4'' : 4 < M.S.dist x y := h4
    rwa [← M.S.dist_comm x y] at h4''
  have hdR : (M.d : ℝ) - 2 = 4 := by rw [hd6]; norm_num
  have hz : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have h := hmaj (y - x)
  rw [hdR] at h
  have htau : M.tau (y - x) = M.twoPoint M.betaCrit x y := M.tau_eq_twoPoint_sub x y
  rw [abs_of_nonneg (M.tau_nonneg (y - x)), htau] at h
  -- compare the majorant with the printed right-hand side at `s = ‖y − x‖ > 4`
  have hpow : (1 + M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ))
      ≤ (M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs (by linarith) (by norm_num)
  have hlogpos : 0 < Real.log (M.S.ρ (toVec (y - x))) := Real.log_pos (by linarith)
  have hlog2pos : 0 < Real.log (2 + M.S.ρ (toVec (y - x))) := Real.log_pos (by linarith)
  have hlogle : Real.log (M.S.ρ (toVec (y - x)))
      ≤ Real.log (2 + M.S.ρ (toVec (y - x))) :=
    Real.log_le_log hs (by linarith)
  have hinv : (Real.log (2 + M.S.ρ (toVec (y - x))))⁻¹
      ≤ (Real.log (M.S.ρ (toVec (y - x))))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hlogpos hlogle
  have hWt : CriticalLRPConv.Wt 4 1 (M.S.ρ (toVec (y - x)))
      = (1 + M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ))
        * (Real.log (2 + M.S.ρ (toVec (y - x))))⁻¹ := by
    simp only [CriticalLRPConv.Wt, CriticalLRPConv.LamR]
    rw [show (-(1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  have hstep : K * CriticalLRPConv.Wt 4 1 (M.S.ρ (toVec (y - x)))
      ≤ K * (Real.log (M.S.ρ (toVec (y - x))))⁻¹
        * (M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ)) := by
    rw [hWt]
    have hK1 : K * (1 + M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ))
        ≤ K * (M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow hK.le
    have hnn : (0 : ℝ) ≤ K * (M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ)) := by positivity
    have hnn2 : (0 : ℝ) ≤ (Real.log (2 + M.S.ρ (toVec (y - x))))⁻¹ :=
      inv_nonneg.mpr hlog2pos.le
    calc K * ((1 + M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ))
          * (Real.log (2 + M.S.ρ (toVec (y - x))))⁻¹)
        = (K * (1 + M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ)))
            * (Real.log (2 + M.S.ρ (toVec (y - x))))⁻¹ := by ring
      _ ≤ (K * (M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ)))
            * (Real.log (M.S.ρ (toVec (y - x))))⁻¹ :=
          mul_le_mul hK1 hinv hnn2 hnn
      _ = K * (Real.log (M.S.ρ (toVec (y - x))))⁻¹
            * (M.S.ρ (toVec (y - x))) ^ (-(4 : ℝ)) := by ring
  refine h.trans (hstep.trans (le_of_eq ?_))
  have hsym : M.S.ρ (toVec (y - x)) = M.S.ρ (toVec (x - y)) := M.S.dist_comm x y
  rw [hsym]
  rw [show (-(M.d : ℝ) + 2) = -4 by rw [hd6]; norm_num]

/-- **`Case3HDLarge` is exactly the positive-log majorant `Wt` consumed by the convolution
argument.**  The distance-restricted form has no content below `‖z‖ = 4` beyond the trivial bound
`τ ≤ 1`, and there it is not sensitive to the sign of the printed logarithm. -/
theorem case3HDLarge_iff_Wt_majorant (hd6 : M.d = 6) (hα2 : M.α = 2) :
    M.Case3HDLarge ↔ ∃ K : ℝ, 0 < K ∧ ∀ z : M.V,
      |M.tau z| ≤ K * CriticalLRPConv.Wt ((M.d : ℝ) - 2) 1 (M.S.ρ (toVec z)) := by
  constructor
  · intro h
    exact M.exists_abs_tau_le_Wt_of_case3HDLarge h
  · rintro ⟨K, hK, hmaj⟩
    exact M.case3HDLarge_of_Wt_majorant hd6 hα2 hK hmaj

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
