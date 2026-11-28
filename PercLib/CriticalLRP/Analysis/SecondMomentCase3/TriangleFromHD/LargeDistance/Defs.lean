/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m1.
Latest independent rebuild at production HEAD `bd25afb1130f7fe93446b447f9a68a4d3aba08cc`; reviewed scratch source `.scratch/review-smwznoz6j/m1/Defs.lean`.

Swarm `smwznoz6j`, member `m1`, direction `d2` — (G) non-vacuity of the literal Case 3 of (HD).

# The distance content of the literal (HD)(3), and the honest repair

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.
The hypothesis (HD) Case 3, p. 9, reads verbatim

```
3. d = 6, α = 2, and P_{βc}(x ↔ y) ⪯ (log ‖x − y‖)^{-1} ‖x − y‖^{-d+2} for all x ≠ y.
```

Production's `SourceModelData.Case3HD` transcribes that display at the model's own normalized
source norm `S.ρ`, which satisfies the paper's normalization (∗) of Definition I.1.3: the unit
ball of `‖·‖` has Lebesgue volume `1` (`SourceNormData.unitBall_volume`).

## Why the literal quantifier "for all x ≠ y" is not a property of the model class

`S.ρ : (Fin d → ℝ) → ℝ` is only assumed to be a norm whose unit ball has volume `1`; nothing
forces `1 ≤ S.ρ (toVec z)` for a nonzero lattice vector `z`.  The printed factor
`(log ‖x − y‖)^{-1}` is then

* negative when `‖x − y‖ < 1`, so the display asks the nonnegative quantity `P_{βc}(x ↔ y)` to be
  `≤` a negative number, which is impossible;
* zero at `‖x − y‖ = 1` in Lean (`(0 : ℝ)⁻¹ = 0`), so the display asks `P_{βc}(x ↔ y) = 0`.

Thus the literal display silently carries the extra hypotheses `1 ≤ ‖x − y‖` for all `x ≠ y`
(and `P_{βc}(x ↔ y) = 0` at `‖x − y‖ = 1`).  These are not consequences of the normalization
(∗): the source norm may be a flattened box of volume `1` that contains a nonzero lattice point.
`FlatSix` below constructs exactly such a norm in the dimension `d = 6` forced by Case 3, with
`ρ (e₁) = 1/2`, together with a genuine `SourceModelData` carrying it.

## The repair

The paper never uses the display at short distances: its own log-corrected convolution estimate
(I.4.12) is stated with `⟨x⟩ = 2 + ⌈‖x‖⌉` "to avoid division by zero", and (I.4.13) is stated
with `(log (1 + ‖x‖))^{-2}` for every `x ≠ 0`.  Production's conversion
(`TriangleFromHD/Pointwise.exists_abs_tau_le_Wt`) also uses the display only at `‖x − y‖ > 4`
and the trivial bound `τ ≤ 1` below that.

Accordingly this file introduces the two distance-restricted forms

* `Case3HDPos` — the display required only where the printed logarithmic factor is positive,
  i.e. at pairs with `1 < ‖x − y‖`;
* `Case3HDLarge` — the display required only at pairs with `4 < ‖x − y‖`, the exact region used
  by the convolution argument.

Both are implied by `Case3HD`, neither carries any short-distance assertion, and `Main.lean`
proves `Case3HDLarge` equivalent to the positive-log majorant `Wt` that the convolution argument
actually consumes.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Pointwise
public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## §1 The distance-restricted forms of (HD)(3) -/

/-- **Case 3 of (HD) at positive logarithmic factor.**  The printed display, required only at
pairs where `(log ‖x − y‖)^{-1}` is positive, i.e. `1 < ‖x − y‖`.  Near the diagonal the
hypothesis is silent, so this form is not refuted by the sign of the logarithm. -/
def Case3HDPos : Prop :=
  M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
    1 < M.S.ρ (toVec (x - y)) →
      M.twoPoint M.betaCrit x y
        ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
            * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)

/-- **Case 3 of (HD) on the region actually used by the convolution argument.**  The printed
display, required only at pairs with `4 < ‖x − y‖`: exactly the range in which
`TriangleFromHD/Pointwise.log_inv_mul_rpow_le_Wt` converts the source decay into the positive-log
majorant `Wt`.  Below that range the two-point function is controlled by the trivial bound
`τ ≤ 1`. -/
def Case3HDLarge : Prop :=
  M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
    4 < M.S.ρ (toVec (x - y)) →
      M.twoPoint M.betaCrit x y
        ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
            * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)

end SourceModelData

/-! ## §2 An admissible normalized source norm in dimension `6` with `ρ(e₁) = 1/2`

The source's normalization (∗) only fixes the Lebesgue volume of the unit ball.  The flattened box
`[-2,2] × [-1/2,1/2]³ × [-1/4,1/4]²` has volume `4 · 1 · (1/2)² = 1` and contains `e₁`, so the
Minkowski functional of the box is an admissible `SourceNormData 6` with `ρ(e₁) = 1/2 < 1`. -/

namespace FlatSix

/-- The half-side-lengths of the flattened box, chosen so that the box has volume one. -/
def flat6C : Fin 6 → ℝ := ![2, 1 / 2, 1 / 2, 1 / 2, 1 / 4, 1 / 4]

theorem flat6C_pos (i : Fin 6) : 0 < flat6C i := by
  fin_cases i <;> norm_num [flat6C]

/-- The Minkowski functional of the box `∏ i, [-flat6C i, flat6C i]`, written as
`sup_i |v i| / flat6C i`. -/
def flatNorm6 (v : Fin 6 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |v i| / flat6C i)

theorem le_flatNorm6 (v : Fin 6 → ℝ) (i : Fin 6) : |v i| / flat6C i ≤ flatNorm6 v :=
  Finset.le_sup' (fun i => |v i| / flat6C i) (Finset.mem_univ i)

theorem flatNorm6_le_one_iff (v : Fin 6 → ℝ) :
    flatNorm6 v ≤ 1 ↔ ∀ i, |v i| ≤ flat6C i := by
  rw [flatNorm6, Finset.sup'_le_iff]
  exact ⟨fun h i => (div_le_one (flat6C_pos i)).mp (h i (Finset.mem_univ i)),
    fun h i _ => (div_le_one (flat6C_pos i)).mpr (h i)⟩

/-- The unit ball of `flatNorm6` is exactly the flattened box. -/
theorem flatNorm6_unitBall :
    {v : Fin 6 → ℝ | flatNorm6 v ≤ 1}
      = Set.pi Set.univ (fun i => Set.Icc (-(flat6C i)) (flat6C i)) := by
  ext v
  rw [Set.mem_ofPred_eq, flatNorm6_le_one_iff]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]

theorem flatNorm6_zero : flatNorm6 0 = 0 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun i _ => ?_)
    simp
  · exact le_trans (by simp) (le_flatNorm6 (0 : Fin 6 → ℝ) 0)

theorem flatNorm6_pos {v : Fin 6 → ℝ} (hv : v ≠ 0) : 0 < flatNorm6 v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  exact lt_of_lt_of_le (div_pos (abs_pos.mpr hi) (flat6C_pos i)) (le_flatNorm6 v i)

theorem flatNorm6_neg (v : Fin 6 → ℝ) : flatNorm6 (-v) = flatNorm6 v := by
  simp only [flatNorm6, Pi.neg_apply, abs_neg]

theorem flatNorm6_add_le (v w : Fin 6 → ℝ) : flatNorm6 (v + w) ≤ flatNorm6 v + flatNorm6 w := by
  refine Finset.sup'_le _ _ (fun i _ => ?_)
  have h1 : |v i| / flat6C i ≤ flatNorm6 v := le_flatNorm6 v i
  have h2 : |w i| / flat6C i ≤ flatNorm6 w := le_flatNorm6 w i
  have hc : (0 : ℝ) < flat6C i := flat6C_pos i
  rw [div_le_iff₀ hc]
  have h1' : |v i| ≤ flatNorm6 v * flat6C i := (div_le_iff₀ hc).mp h1
  have h2' : |w i| ≤ flatNorm6 w * flat6C i := (div_le_iff₀ hc).mp h2
  calc |(v + w) i| = |v i + w i| := rfl
    _ ≤ |v i| + |w i| := abs_add_le _ _
    _ ≤ flatNorm6 v * flat6C i + flatNorm6 w * flat6C i := by linarith
    _ = (flatNorm6 v + flatNorm6 w) * flat6C i := by ring

theorem flatNorm6_smul (c : ℝ) (v : Fin 6 → ℝ) : flatNorm6 (c • v) = |c| * flatNorm6 v := by
  have h : (fun i => |(c • v) i| / flat6C i) = (fun i => |c| * (|v i| / flat6C i)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    ring
  rw [flatNorm6, h, flatNorm6]
  exact (Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty
    (f := fun i => |v i| / flat6C i) (fun x => |c| * x)
    (fun x y => mul_max_of_nonneg (a := |c|) x y (abs_nonneg c))).symm

theorem flatNorm6_continuous : Continuous flatNorm6 := by
  unfold flatNorm6
  fun_prop

/-- **The flattened normalized source norm on `Fin 6 → ℝ`.** -/
def flatSourceNorm6 : SourceNormData 6 where
  ρ := flatNorm6
  ρ_zero := flatNorm6_zero
  ρ_pos := fun _ hv => flatNorm6_pos hv
  ρ_neg := flatNorm6_neg
  ρ_add_le := flatNorm6_add_le
  ρ_smul := flatNorm6_smul
  ρ_continuous := flatNorm6_continuous
  unitBall_volume := by
    rw [flatNorm6_unitBall, MeasureTheory.volume_pi_pi]
    have hnonneg : ∀ i : Fin 6, (0 : ℝ) ≤ flat6C i - -(flat6C i) := by
      intro i
      have := flat6C_pos i
      linarith
    rw [show (∏ i : Fin 6, MeasureTheory.volume (Set.Icc (-(flat6C i)) (flat6C i)))
        = ∏ i : Fin 6, ENNReal.ofReal (flat6C i - -(flat6C i)) from by
      simp only [Real.volume_Icc]]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hnonneg i)]
    rw [show (∏ i : Fin 6, (flat6C i - -(flat6C i))) = 1 by
      simp only [flat6C, Fin.prod_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num]
    simp

/-- The first standard basis vector of `ℤ^6`. -/
def flat6E1 : Fin 6 → ℤ := ![1, 0, 0, 0, 0, 0]

/-- `toVec` of the first basis vector is the coordinate vector `(1,0,0,0,0,0)`. -/
theorem toVec_flat6E1 : toVec flat6E1 = (fun i : Fin 6 => (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i) := by
  funext i
  fin_cases i <;> simp [toVec, flat6E1]

/-- `ρ(e₁) = 1/2`: the flat source norm puts a nonzero lattice vector at distance `1/2`. -/
theorem flatNorm6_e1 : flatNorm6 (toVec flat6E1) = 1 / 2 := by
  rw [toVec_flat6E1, flatNorm6]
  refine le_antisymm ?_ ?_
  · rw [Finset.sup'_le_iff]
    intro i _
    fin_cases i <;> norm_num [flat6C]
  · refine le_trans (le_of_eq ?_) (le_flatNorm6 (fun i : Fin 6 => (![1, 0, 0, 0, 0, 0] : Fin 6 → ℝ) i) 0)
    norm_num [flat6C]

/-- The lattice distance of `e₁` from the origin in the flat source norm is `1/2`. -/
theorem flatSourceNorm6_dist_e1 : flatSourceNorm6.dist 0 flat6E1 = 1 / 2 := by
  rw [SourceNormData.dist, zero_sub]
  change flatNorm6 (toVec (-flat6E1)) = 1 / 2
  rw [show toVec (-flat6E1) = -toVec flat6E1 by
    funext i
    simp [toVec]]
  rw [flatNorm6_neg]
  exact flatNorm6_e1

theorem flatSourceNorm6_dist_e1_lt_one : flatSourceNorm6.dist 0 flat6E1 < 1 := by
  rw [flatSourceNorm6_dist_e1]
  norm_num

end FlatSix

/-! ## §3 A genuine source model carrying the flat norm at `d = 6`, `α = 2` -/

namespace SourceModelData

/-- Replacing the source norm of a `SourceModelData` by another admissible norm of the same
dimension; every field except `S` is unchanged. -/
def withNorm (M : SourceModelData) (S : SourceNormData M.d) : SourceModelData where
  d := M.d
  hd := M.hd
  α := M.α
  hα := M.hα
  S := S
  K := M.K
  K_nonneg := M.K_nonneg
  K_antitone := M.K_antitone
  K_diff := M.K_diff
  K_eq_integral := M.K_eq_integral
  exists_error := M.exists_error

end SourceModelData

/-- **A genuine `SourceModelData` with `d = 6`, `α = 2` and the flat source norm.**  Its kernel is
the source-normalized power law `K r = r^{-8}/8` of `ModelWitness.sourceModelWitness`. -/
def flatModel6 : SourceModelData :=
  (Witness.sourceModelWitness 6 (by norm_num) 2 (by norm_num)).withNorm FlatSix.flatSourceNorm6

theorem flatModel6_d : flatModel6.d = 6 := rfl

theorem flatModel6_α : flatModel6.α = 2 := rfl

theorem flatModel6_S : flatModel6.S = FlatSix.flatSourceNorm6 := rfl

end Orchestration
end PercLib.CriticalLRP
