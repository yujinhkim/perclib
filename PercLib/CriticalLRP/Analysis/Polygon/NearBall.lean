/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Finite near-ball selection and normalized lattice counting for polygon estimates.
-/
module

public import PercLib.CriticalLRP.Analysis.BallAverage
public import PercLib.CriticalLRP.Analysis.Polygon.Consumer

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I418C.NearBall

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-! ## The cube constant of the normalized norm -/

/-- The one landed input about `ρ`: its supremum on the unit cube is finite.  Bundled with
nonnegativity (`cube_bound_nonneg`) so that it can be used as an arithmetic parameter. -/
theorem exists_cube_const :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C := by
  obtain ⟨C, hC⟩ := PercLib.CriticalLRP.BallAverage.exists_cube_bound M
  exact ⟨C, PercLib.CriticalLRP.BallAverage.cube_bound_nonneg M hC, hC⟩

/-! ## `|B_R| ≤ K R^d`, uniformly in `R ≥ 1` -/

/-- **Explicit normalized ball count.**  For every cube bound `C ≥ 0` of the normalized norm
`ρ`, every lattice ball of radius `R ≥ 1` has at most `max (2^d) ((2C+1)^d) · R^d` points:
`(R+C)^d ≤ (2R)^d` when `R ≥ C`, and `B_R ⊆ B_{C+1}` when `R ≤ C`.

The bound is uniform in `R`, which is what the source's `|B_R| ≤ C R^d` step needs; the
restriction `R ≥ 1` is harmless because the assembly only evaluates it at
`R = r^{α/(2d)} ≥ 1` for `r ≥ 1`. -/
theorem card_le_of_cube_bound {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y : Fin M.d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → M.S.ρ y ≤ C) :
    ∀ R : ℝ, 1 ≤ R →
      ((M.ball R).ncard : ℝ) ≤ max (2 ^ M.d) ((2 * C + 1) ^ M.d) * R ^ (M.d : ℝ) := by
  intro R hR
  -- the natural-power form, converted to `Real.rpow` at the end
  have hnat : ((M.ball R).ncard : ℝ) ≤ max (2 ^ M.d) ((2 * C + 1) ^ M.d) * R ^ M.d := by
    rcases lt_or_ge C R with hCR | hRC
    · -- large `R`: `(R+C)^d ≤ (2R)^d = 2^d R^d`
      have h1 : ((M.ball R).ncard : ℝ) ≤ (R + C) ^ M.d :=
        PercLib.CriticalLRP.BallAverage.ball_ncard_le M hC hC0 hCR
      have h2 : (R + C) ^ M.d ≤ 2 ^ M.d * R ^ M.d := by
        have hle : R + C ≤ 2 * R := by linarith
        calc (R + C) ^ M.d ≤ (2 * R) ^ M.d := pow_le_pow_left₀ (by linarith) hle _
          _ = 2 ^ M.d * R ^ M.d := mul_pow 2 R M.d
      have h3 : 2 ^ M.d * R ^ M.d ≤ max (2 ^ M.d) ((2 * C + 1) ^ M.d) * R ^ M.d :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith
    · -- small `R`: the ball is contained in the fixed ball of radius `C+1`
      have hmono : (M.ball R).ncard ≤ (M.ball (C + 1)).ncard :=
        Set.ncard_le_ncard (PercLib.CriticalLRP.BallAverage.ball_mono M (by linarith))
          (PercLib.CriticalLRP.BallAverage.ball_finite M (C + 1))
      have h1 : ((M.ball (C + 1)).ncard : ℝ) ≤ ((C + 1) + C) ^ M.d :=
        PercLib.CriticalLRP.BallAverage.ball_ncard_le M hC hC0 (by linarith)
      have h1' : ((M.ball R).ncard : ℝ) ≤ (2 * C + 1) ^ M.d := by
        have hcast : ((M.ball R).ncard : ℝ) ≤ ((M.ball (C + 1)).ncard : ℝ) := by
          exact_mod_cast hmono
        have hEq : (C + 1) + C = 2 * C + 1 := by ring
        linarith [hcast, hEq ▸ h1]
      have hK0 : (0 : ℝ) < max (2 ^ M.d) ((2 * C + 1) ^ M.d) :=
        lt_of_lt_of_le (by positivity) (le_max_left _ _)
      have hRm : (1 : ℝ) ≤ R ^ M.d := one_le_pow₀ hR
      have h2 : (2 * C + 1) ^ M.d ≤ max (2 ^ M.d) ((2 * C + 1) ^ M.d) := le_max_right _ _
      have h3 : max (2 ^ M.d) ((2 * C + 1) ^ M.d)
          ≤ max (2 ^ M.d) ((2 * C + 1) ^ M.d) * R ^ M.d := by
        have := mul_le_mul_of_nonneg_left hRm hK0.le
        simpa using this
      linarith
  rw [Real.rpow_natCast]
  exact hnat

/-- **The normalized ball count of Lemma I.4.18.**  There is a positive constant `K`,
depending only on the model (through the cube constant of `ρ`), such that every lattice ball
of radius `R ≥ 1` has at most `K R^d` points. -/
theorem exists_card_const :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → ((M.ball R).ncard : ℝ) ≤ K * R ^ (M.d : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_cube_const M
  exact ⟨max (2 ^ M.d) ((2 * C + 1) ^ M.d),
    lt_of_lt_of_le (by positivity) (le_max_left _ _), card_le_of_cube_bound M hC0 hC⟩

/-- **Ball count below radius `1`.**  The complementary range, needed when the source's
`R = r^{α/(2d)}` (or the tail threshold `r^{α/(4d)}`) is smaller than `1`: for every
`0 < r ≤ 1` the ball of radius `r^{α/(4d)}` has at most `K r^{-α/(4d)}` points.

Note that `|B_R| ≤ K R^d` is *false* for `R < 1` (the ball always contains `0`, while
`R^d < 1`), so a separate statement is unavoidable; the compensating factor `r^{-c} ≥ 1` is
exactly the `r^{-c}` term of the source's `∇_R + C R^d/r^α`. -/
theorem exists_small_ball_count :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((M.ball (r ^ (M.α / (4 * (M.d : ℝ))))).ncard : ℝ)
        ≤ K * r ^ (-(M.α / (4 * (M.d : ℝ)))) := by
  have hcc0 : 0 < M.α / (4 * (M.d : ℝ)) := by
    have hdpos : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
    exact div_pos M.hα (by linarith)
  refine ⟨max 1 ((M.ball 1).ncard : ℝ),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun r hr hr1 => ?_⟩
  have hRp : r ^ (M.α / (4 * (M.d : ℝ))) ≤ 1 := Real.rpow_le_one hr.le hr1 hcc0.le
  have hmono : ((M.ball (r ^ (M.α / (4 * (M.d : ℝ))))).ncard : ℝ)
      ≤ ((M.ball 1).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard
      (PercLib.CriticalLRP.BallAverage.ball_mono M hRp)
      (PercLib.CriticalLRP.BallAverage.ball_finite M 1)
  have hone : (1 : ℝ) ≤ r ^ (-(M.α / (4 * (M.d : ℝ)))) := by
    have h := Real.rpow_le_rpow_of_nonpos hr hr1 (by linarith : -(M.α / (4 * (M.d : ℝ))) ≤ 0)
    simpa using h
  have hK1 : (1 : ℝ) ≤ max 1 ((M.ball 1).ncard : ℝ) := le_max_left _ _
  have hK2 : ((M.ball 1).ncard : ℝ) ≤ max 1 ((M.ball 1).ncard : ℝ) := le_max_right _ _
  have hK0 : (0 : ℝ) < max 1 ((M.ball 1).ncard : ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hstep : max 1 ((M.ball 1).ncard : ℝ)
      ≤ max 1 ((M.ball 1).ncard : ℝ) * r ^ (-(M.α / (4 * (M.d : ℝ)))) := by
    have := mul_le_mul_of_nonneg_left hone hK0.le
    simpa using this
  linarith [hmono, hK1, hstep]

/-! ## Near-ball selection -/

/-- **The near side of the source's near/far split, as a finite set.**  For every `R ≥ 1`
there is a finite `s : Finset M.V` containing the closed ball of radius `R` around `0`
(stated in the form `y ∉ s → R ≤ M.S.dist 0 y` used by `Polygon.Core.split_bound`) with
`|s| ≤ K R^d` for a constant `K` independent of `R`.

`hfar` is stronger than needed (`R < ‖y‖` off `s`), which is exactly what the source's
`‖y‖ ≥ R` far side uses. -/
theorem exists_near_ball :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → ∃ s : Finset M.V,
      (∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y) ∧ (s.card : ℝ) ≤ K * R ^ (M.d : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := exists_card_const M
  refine ⟨K, hK0, fun R hR => ?_⟩
  have hfin : (M.ball R).Finite := PercLib.CriticalLRP.BallAverage.ball_finite M R
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro y hy
    have hnot : y ∉ M.ball R := fun hc => hy ((Set.Finite.mem_toFinset hfin).2 hc)
    have hlt : R < M.S.ρ (toVec y) := lt_of_not_ge hnot
    rw [SourceModelData.dist_zero_eq M y]
    exact hlt.le
  · have h := hK R hR
    rwa [Set.ncard_eq_toFinset_card (M.ball R) hfin] at h

/-! ## The assembly with the ball data discharged -/

/-- **Lemma I.4.18 with the normalized ball count and near/far selection discharged.**

For every model `M` there is a positive constant `K` (the ball-count constant of
`exists_card_const`) with the following property.  For every `r ≥ 1`, every `ℓ ≥ 4`, and every
`x`, the `ℓ`-fold polygon diagram of the cutoff two-point function at `β_c` satisfies

  `T^ℓ_{β_c,r}(0,x) ≤ max 1 (∇_{β_c} K / c₀) (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^{ℓ-3}`,

with `c = α/(4d)`, `R = r^{α/(2d)}` chosen internally, and the near ball selected internally.

The remaining hypotheses are exactly the genuine analytic inputs of the landed theorem:
`hχfin` (finite cutoff first moment), `hTri` (`∇_{β_c} < ∞`), `hB2`/`hB3` (summability of the
two- and three-step convolutions of the uncut two-point function), `hlink` (the real threefold
convolution is bounded by the uncut open triangle), `htailc` (the uncut tail `∇_{r^c}`), and
`hχ` (the first-moment lower comparison `χ ⪰ r^α`). -/
theorem source_polygon_bound_sup_of_cutoff_data_uniform (M : SourceModelData) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r trc : ℝ) {c₀ : ℝ} {ell : ℕ},
      1 ≤ r → 0 < c₀ → 4 ≤ ell →
      M.cutMassAt r 0 ≠ ⊤ →
      PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ →
      (∀ u : M.V, Summable fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u) →
      (∀ y : M.V, Summable fun u =>
        (∑' v : M.V, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
          * M.twoPoint M.betaCrit u y) →
      (∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y) →
      (∀ y : M.V, r ^ (M.α / (4 * (M.d : ℝ))) ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc) →
      0 ≤ trc →
      c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal →
      ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
        ≤ max 1 (M.triSelf * K / c₀)
            * (trc + r ^ (-(M.α / (4 * (M.d : ℝ)))))
            * (M.cutMassAt r 0).toReal ^ (ell - 3) := by
  obtain ⟨K, hK0, hball⟩ := exists_near_ball M
  refine ⟨K, hK0, ?_⟩
  intro r trc c₀ ell hr hc₀ hell hχfin hTri hB2 hB3 hlink htailc htrc hχ x
  have hexp : (0 : ℝ) ≤ M.α / (2 * (M.d : ℝ)) :=
    div_nonneg M.hα.le (by positivity)
  have hR1 : 1 ≤ r ^ (M.α / (2 * (M.d : ℝ))) := Real.one_le_rpow hr hexp
  obtain ⟨s, hfar, hcard⟩ := hball _ hR1
  exact source_polygon_bound_of_cutoff_data M r _ trc s hr hc₀ hK0.le hχfin hTri hB2 hB3
    hlink hell rfl hfar htailc htrc hcard rfl hχ x

end PercLib.CriticalLRP.I418C.NearBall
