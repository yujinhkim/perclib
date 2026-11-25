/-
Member `m1`, swarm `smwv9oxuv`, direction `d4` ("evolution in the radius").

# Finite-window remainder for the radius evolution of the cut-off law

This file proves the **quantitative first-order expansion, uniform in the edge**, of the
range-truncated source law along the radius: on a window `[r, r']` with `0 < r ≤ r'` and no
corner radius in between, the kernel gap of every edge of length `≤ r` moves by the *same*
additive amount `K r - K r'`, hence

* `1 - q_e(r') = (1 - q_e(r)) · exp (β_c (K r' - K r))`  (exact, all such edges at once),
* `q_e(r') - q_e(r) = (1 - q_e(r)) · (1 - exp (-β_c (K r - K r')))`  (exact),
* and with `x_e := β_c (K r - K r')` (the same number for every edge of the window),
  `|q_e(r') - q_e(r) - (1 - q_e(r)) x_e| ≤ (1 - q_e(r)) x_e² ≤ x_e²`

by the elementary sandwich `x - x² ≤ 1 - e^{-x} ≤ x` (`x ≥ 0`).  So the evolution of the law
over a radius window has a first-order term which is `x_e` times the **closed**-edge weight of
the edge (the excluded weight of the `p = 2` right-hand side) plus a remainder that is
*quadratic in the window length*, uniformly in the edge.

`abs_cutProb_sub_le_mul_sq` is the form a remainder/interchange estimate consumes: a single
number `x` (depending only on the kernel and the two radii) controls the whole window's edge
evolution, with no per-edge constant and no sum over edges.

## What is *not* proved here

This is the law-level (per-edge) remainder.  It does **not** differentiate
`M.cutMomentReal 2`: passing from the evolution of the edge probabilities to the evolution of
`E|K|²` is the exchange with the (infinite) edge and vertex series, i.e. the identity
`Σ_e coeffRHS r (E[|K|² | e closed] - E[|K|²]) = coeffRHS r (exclMassQuad + 2 exclMassSqLin)`,
which still needs its own majorant for the quadratic functional.  In particular nothing here
asserts the off-corner derivative, and no right-hand-side identity is claimed to imply it.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.ScalarFactor.Defs

/-!
# First-order remainder for cutoff probabilities on a radius window

The closed-edge probabilities acquire a common multiplicative factor on every edge of a
radius window.  Quadratic remainders are proved per edge and for finite closed-weight sums.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-! ## 3. The elementary sandwich for the exponential remainder -/

/-- `x - x² ≤ 1 - e^{-x} ≤ x` for `x ≥ 0`, hence `|1 - e^{-x} - x| ≤ x²`.  This is the
elementary modulus by which the window length enters the remainder. -/
theorem abs_one_sub_exp_neg_sub_le_sq {x : ℝ} (hx : 0 ≤ x) :
    |1 - Real.exp (-x) - x| ≤ x ^ 2 := by
  have hexp1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hexp2 : Real.exp (-x) ≤ 1 / (1 + x) := by
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have hge : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hinv : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos x) hx1).mpr hge
    have hexp : (Real.exp x)⁻¹ = Real.exp (-x) := by
      rw [← Real.exp_neg]
    have hone : (1 + x)⁻¹ = 1 / (1 + x) := one_div _ |>.symm
    rwa [hexp, hone] at hinv
  have hle : 1 - Real.exp (-x) ≤ x := by linarith
  have hge : x - x ^ 2 ≤ 1 - Real.exp (-x) := by
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have h1 : 1 - 1 / (1 + x) = x / (1 + x) := by
      field_simp
      ring
    have h2 : x / (1 + x) ≤ 1 - Real.exp (-x) := by
      have := hexp2
      linarith
    have h3 : x - x ^ 2 ≤ x / (1 + x) := by
      rw [le_div_iff₀ hx1]
      nlinarith [sq_nonneg x]
    linarith
  rw [abs_le]
  constructor <;> nlinarith


namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The kernel profile moves by a common additive shift -/

/-- On the window `s ≤ r ≤ r'` the truncated kernel gap `K s - K r` of an edge of length `s`
changes by exactly `K r - K r'`, **independent of `s`**.  This is the reason the whole window
evolves with one scalar: the profile `cutoffProfile K r s = K s - K r` shifts down by `K r` and
`K r` is the only `s`-dependent... er, `s`-independent... part. -/
theorem cutoffProfile_sub_of_le {r r' s : ℝ} (hs : s ≤ r) (hrr' : r ≤ r') :
    FiniteVolume.cutoffProfile M.K r' s - FiniteVolume.cutoffProfile M.K r s
      = M.K r - M.K r' := by
  rw [FiniteVolume.cutoffProfile_of_le (hs.trans hrr'), FiniteVolume.cutoffProfile_of_le hs]
  ring

/-- The same statement for an edge of the window, with the model's distance. -/
theorem cutoffProfile_dist_sub {r r' : ℝ} {x y : M.V} (_hxy : x ≠ y)
    (hd : M.S.dist x y ≤ r) (hrr' : r ≤ r') :
    FiniteVolume.cutoffProfile M.K r' (M.S.dist x y)
        - FiniteVolume.cutoffProfile M.K r (M.S.dist x y) = M.K r - M.K r' :=
  M.cutoffProfile_sub_of_le hd hrr'

/-! ## 2. Multiplicative evolution of the closed-edge probability -/

/-- **Exact evolution of the closed-edge probability.**  For an edge of the window, the
closed probability at `r'` is the closed probability at `r` times the *same* factor
`exp (β_c (K r' - K r))` for every edge.  Equivalently every excluded weight of the `p = 2`
right-hand side scales by one common factor as the radius grows across a corner-free window. -/
theorem one_sub_cutProb_mul_exp {r r' : ℝ} {x y : M.V} (hxy : x ≠ y)
    (hd : M.S.dist x y ≤ r) (hrr' : r ≤ r') :
    1 - ((M.cutProb r' s(x, y) : unitInterval) : ℝ)
      = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        Real.exp (-((M.betaCrit : ℝ) * (M.K r - M.K r'))) := by
  rw [M.one_sub_cutProb_eq_exp r' hxy (hd.trans hrr'), M.one_sub_cutProb_eq_exp r hxy hd,
    ← Real.exp_add]
  congr 1
  have hprof := M.cutoffProfile_sub_of_le (s := M.S.dist x y) hd hrr'
  have hprof' : FiniteVolume.cutoffProfile M.K r' (M.S.dist x y)
      = FiniteVolume.cutoffProfile M.K r (M.S.dist x y) + (M.K r - M.K r') := by linarith
  rw [hprof']
  ring

/-- **Exact first-order increment of the edge probability**, with the closed weight explicit:
`q_e(r') - q_e(r) = (1 - q_e(r)) (1 - e^{-x})` where `x = β_c (K r - K r')` is the same for
every edge of the window. -/
theorem cutProb_sub_eq {r r' : ℝ} {x y : M.V} (hxy : x ≠ y)
    (hd : M.S.dist x y ≤ r) (hrr' : r ≤ r') :
    ((M.cutProb r' s(x, y) : unitInterval) : ℝ)
        - ((M.cutProb r s(x, y) : unitInterval) : ℝ)
      = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        (1 - Real.exp (-((M.betaCrit : ℝ) * (M.K r - M.K r')))) := by
  have h := M.one_sub_cutProb_mul_exp hxy hd hrr'
  calc ((M.cutProb r' s(x, y) : unitInterval) : ℝ)
        - ((M.cutProb r s(x, y) : unitInterval) : ℝ)
      = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ))
          - (1 - ((M.cutProb r' s(x, y) : unitInterval) : ℝ)) := by ring
    _ = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ))
          - (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
            Real.exp (-((M.betaCrit : ℝ) * (M.K r - M.K r'))) := by rw [h]
    _ = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
          (1 - Real.exp (-((M.betaCrit : ℝ) * (M.K r - M.K r')))) := by ring

end SourceModelData

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 4. The finite-window remainder, uniform in the edge -/

/-- **First-order expansion of every window edge with a quadratic remainder and no per-edge
constant.**  With `x = β_c (K r - K r') ≥ 0` (the same number for every edge of the window),
`q_e(r') - q_e(r) = (1 - q_e(r)) x + R_e` with `|R_e| ≤ x²`.  This is the estimate a
remainder/interchange argument for `E|K|^2` consumes: one scalar `x` controls the whole window,
and the first-order term carries the *closed*-edge (excluded) weight. -/
theorem abs_cutProb_sub_le_mul_sq {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') {x y : M.V}
    (hxy : x ≠ y) (hd : M.S.dist x y ≤ r) :
    |((M.cutProb r' s(x, y) : unitInterval) : ℝ)
        - ((M.cutProb r s(x, y) : unitInterval) : ℝ)
        - (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
            ((M.betaCrit : ℝ) * (M.K r - M.K r'))|
      ≤ ((M.betaCrit : ℝ) * (M.K r - M.K r')) ^ 2 := by
  have hr' : (0 : ℝ) < r' := lt_of_lt_of_le hr hrr'
  have hKK : M.K r' ≤ M.K r := by
    exact M.K_antitone (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hr') hrr'
  have hx0 : 0 ≤ (M.betaCrit : ℝ) * (M.K r - M.K r') := by
    have : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
    have : 0 ≤ M.K r - M.K r' := by linarith
    exact mul_nonneg ‹(0 : ℝ) ≤ (M.betaCrit : ℝ)› this
  have hc0 : 0 ≤ 1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ) := by
    have hle : ((M.cutProb r s(x, y) : unitInterval) : ℝ) ≤ 1 := (M.cutProb r s(x, y)).2.2
    linarith
  have hc1 : 1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ) ≤ 1 := by
    have h0 : (0 : ℝ) ≤ ((M.cutProb r s(x, y) : unitInterval) : ℝ) := (M.cutProb r s(x, y)).2.1
    linarith
  have hrew : ((M.cutProb r' s(x, y) : unitInterval) : ℝ)
        - ((M.cutProb r s(x, y) : unitInterval) : ℝ)
        - (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
            ((M.betaCrit : ℝ) * (M.K r - M.K r'))
      = (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        ((1 - Real.exp (-((M.betaCrit : ℝ) * (M.K r - M.K r'))))
          - ((M.betaCrit : ℝ) * (M.K r - M.K r'))) := by
    rw [M.cutProb_sub_eq hxy hd hrr']
    ring
  rw [hrew, abs_mul, abs_of_nonneg hc0]
  have hscal := abs_one_sub_exp_neg_sub_le_sq hx0
  calc (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ))
        * |1 - Real.exp (-((M.betaCrit : ℝ) * (M.K r - M.K r')))
            - ((M.betaCrit : ℝ) * (M.K r - M.K r'))|
      ≤ 1 * ((M.betaCrit : ℝ) * (M.K r - M.K r')) ^ 2 :=
        mul_le_mul hc1 hscal (abs_nonneg _) (by norm_num)
    _ = ((M.betaCrit : ℝ) * (M.K r - M.K r')) ^ 2 := by ring

/-- **The window's excluded weights scale by one common factor.**  For any finite set `S` of
vertices whose edge to the origin lies in the window, the total closed probability
`Σ_{y ∈ S} (1 - q_{s(0,y)}(r))` — the per-vertex weight of the excluded sums
`exclSumQuad`/`exclSumLin` of the `p = 2` right-hand side — is multiplied by the single factor
`exp (β_c (K r' - K r))` when the radius grows from `r` to `r'`. -/
theorem sum_one_sub_cutProb_mul_exp {r r' : ℝ} (S : Finset M.V) (hS : ∀ y ∈ S, y ≠ 0)
    (hrr' : r ≤ r') (hd : ∀ y ∈ S, M.S.dist 0 y ≤ r) :
    ∑ y ∈ S, (1 - ((M.cutProb r' s(0, y) : unitInterval) : ℝ))
      = Real.exp (-((M.betaCrit : ℝ) * (M.K r - M.K r'))) *
        ∑ y ∈ S, (1 - ((M.cutProb r s(0, y) : unitInterval) : ℝ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [M.one_sub_cutProb_mul_exp (x := 0) (y := y) (Ne.symm (hS y hy)) (hd y hy) hrr',
    mul_comm]

end SourceModelData
end PercLib.CriticalLRP.Orchestration
/-! ## 5. The window-level remainder for the excluded weights of the `p = 2` RHS -/

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Finite-window remainder for the excluded window weight.**  For any finite vertex set `S`
whose edges to the origin lie in the window, the total closed probability `T(r)`, which is the
per-vertex weight of the excluded sums `exclSumQuad`/`exclSumLin` of the `p = 2` right-hand side,
changes by `-(1 - e^{-x}) T(r)`, i.e. by `-x T(r)` up to a remainder that is *quadratic in the
window scalar* `x = β_c (K r - K r')` and *linear in the window size*:

`|T(r') - T(r) + x T(r)| ≤ x² · |S|`.

No per-edge constant, no sum over the infinite edge set, and no differentiation of `|K|^2` is
involved: this is the law-level remainder that a `p = 2` interchange still has to multiply by
the (quadratic) functional increment. -/
theorem sum_one_sub_cutProb_sub_remainder {r r' : ℝ} (hr : 0 < r) (S : Finset M.V)
    (hS : ∀ y ∈ S, y ≠ 0) (hrr' : r ≤ r') (hd : ∀ y ∈ S, M.S.dist 0 y ≤ r) :
    |(∑ y ∈ S, (1 - ((M.cutProb r' s(0, y) : unitInterval) : ℝ)))
        - (∑ y ∈ S, (1 - ((M.cutProb r s(0, y) : unitInterval) : ℝ)))
        + ((M.betaCrit : ℝ) * (M.K r - M.K r')) *
            (∑ y ∈ S, (1 - ((M.cutProb r s(0, y) : unitInterval) : ℝ)))|
      ≤ ((M.betaCrit : ℝ) * (M.K r - M.K r')) ^ 2 * (S.card : ℝ) := by
  set T : ℝ := ∑ y ∈ S, (1 - ((M.cutProb r s(0, y) : unitInterval) : ℝ)) with hT
  set x : ℝ := (M.betaCrit : ℝ) * (M.K r - M.K r') with hx
  have hsum : (∑ y ∈ S, (1 - ((M.cutProb r' s(0, y) : unitInterval) : ℝ)))
      = Real.exp (-x) * T := by
    rw [hT, hx]
    exact M.sum_one_sub_cutProb_mul_exp S hS hrr' hd
  have hT0 : 0 ≤ T := by
    rw [hT]
    refine Finset.sum_nonneg fun y _ => ?_
    have hle : ((M.cutProb r s(0, y) : unitInterval) : ℝ) ≤ 1 := (M.cutProb r s(0, y)).2.2
    linarith
  have hTcard : T ≤ (S.card : ℝ) := by
    rw [hT]
    calc ∑ y ∈ S, (1 - ((M.cutProb r s(0, y) : unitInterval) : ℝ))
        ≤ ∑ _y ∈ S, (1 : ℝ) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have h0 : (0 : ℝ) ≤ ((M.cutProb r s(0, y) : unitInterval) : ℝ) :=
            (M.cutProb r s(0, y)).2.1
          linarith
      _ = (S.card : ℝ) := by simp
  have hx0 : 0 ≤ x := by
    have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
    have hr' : (0 : ℝ) < r' := lt_of_lt_of_le hr hrr'
    have hKK : M.K r' ≤ M.K r :=
      M.K_antitone (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hr') hrr'
    rw [hx]
    exact mul_nonneg hβ (by linarith)
  have hmain : (∑ y ∈ S, (1 - ((M.cutProb r' s(0, y) : unitInterval) : ℝ))) - T + x * T
      = (Real.exp (-x) - 1 + x) * T := by
    rw [hsum]; ring
  rw [hmain, abs_mul, abs_of_nonneg hT0]
  have h1 : |Real.exp (-x) - 1 + x| = |1 - Real.exp (-x) - x| := by
    rw [show Real.exp (-x) - 1 + x = -(1 - Real.exp (-x) - x) by ring, abs_neg]
  rw [h1]
  calc |1 - Real.exp (-x) - x| * T
      ≤ x ^ 2 * T := mul_le_mul_of_nonneg_right (abs_one_sub_exp_neg_sub_le_sq hx0) hT0
    _ ≤ x ^ 2 * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hTcard (by positivity)

end SourceModelData
end PercLib.CriticalLRP.Orchestration
