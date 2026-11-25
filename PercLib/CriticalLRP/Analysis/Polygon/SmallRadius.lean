/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma I.4.18 at small radii: `0 < r ≤ 1`

Proof-only results extending Lemma I.4.18 to every positive radius and to small-radii endpoint cases.

## What is missing in the landed assembly, and why

`Analysis/Polygon/Core.polygon_bound` — and every model-level consumer built on it
(`Model.source_polygon_bound`, `Consumer.source_polygon_bound_of_cutoff_data`,
`TailConstant.source_polygon_bound_tail_cc`,
`NearBall.source_polygon_bound_sup_of_cutoff_data_uniform`) — carries the hypothesis
`1 ≤ r`.  The source (Hutchcroft, *Critical long-range percolation I*, Lemma I.4.18,
`paper.txt` lines 2517–2540) claims the bound

  `sup_x T^ℓ_{β_c,r}(0,x) = T^ℓ_{β_c,r}(0,0) ≤ C (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^{ℓ-3}`

"for each integer ℓ ≥ 3" and, in the proof, "for every r > 0", with `R = r^{α/(2d)}`.

The `1 ≤ r` restriction is not cosmetic: the proof inserts the normalized ball count
`|B_R| ≤ K R^d`, which is **false** for `R < 1` because `0 ∈ B_R` always while
`R^d < 1` (this is proved below as `not_forall_card_le_rpow`).  At small `r` the near
ball is therefore *not* polynomial in `R`; what replaces the missing factor `R^d` is the
compensating factor `r^{-c} ≥ 1` of the source's own right-hand side, together with
`χ = E_{β_c,r}|K| ≥ 1` (which holds unconditionally because `T(0,0) = 1`).

## What is proved here

* `I418C.polygon_bound_small` — the abstract near/far split at the small near radius
  `R = r^cc`, with the compensating cardinality bound `|s| ≤ K r^{-cc}` and `χ ≥ 1`.
  It needs no `1 ≤ r`: the whole small-radius content is the choice of `R` and the
  cardinality bound.
* `SourceModelData.source_polygon_bound_small_of_finite` — the same at the actual model
  carrier, with `hTri` and *finiteness of `χ` at the cutoff* as the only analytic inputs
  (`hB2/hB3/hlink` are discharged by `UncutLink.source_powerInputs'`,
  `UncutLink.source_triTail'`).  `SourceModelData.source_polygon_bound_small` is the
  variant that *derives* finiteness from the first-moment comparison
  `c₀ r^α ≤ χ` instead.
* `SourceModelData.one_le_cutMassAt_toReal` — `χ ≥ 1` at every cutoff, which is the
  free input that converts `χ^{ℓ-4}` into `χ^{ℓ-3}`.
* `I418C.NearBall.exists_small_near_ball` — the finite near ball `B_{r^cc} ⊆ B_1` with
  `|B_{r^cc}| ≤ max 1 |B_1| · r^{-cc}`, uniformly for `0 < r ≤ 1`;
  `exists_small_near_ball_of_near_ball` shows it follows from the landed
  `NearBall.exists_near_ball` at `R = 1` (so it is a sharper constant, not a new input).
* `I418C.NearBall.not_forall_card_le_rpow` — the uniform card bound `|B_R| ≤ K R^d`
  genuinely fails on `(0,1]`, which is why the landed `1 ≤ r` proof cannot be reused.
* `SourceModelData.cutMassAt_ne_top_of_le` — finiteness of `χ` propagates down in `r`, so
  one finite cutoff `r₁ ≥ 1` covers the whole small-radius range.
* `I418C.exists_uniform_source_polygon_bound_small_radius_of_finite` — Lemma I.4.18 for
  `0 < r ≤ 1`, for **every** exponent `c > 0`, with constants independent of `r` and `ℓ`,
  from one finite cutoff; `..._small_radius` is the same with the Proposition-I.4.2-shaped
  hypothesis `hP` instead.
* `I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii` —
  the reconciliation: the landed `r ≥ 1` theorem (called verbatim) and the small-radius
  theorem give one statement for all `r > 0`, sharing one exponent `c` and one constant
  `C`.
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Assembly

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I418C

variable {V : Type*} [Zero V] [DecidableEq V] [Countable V]

/-! ## The abstract small-radius split -/

/-- **Small-radius near/far split.**  `split_bound` applied at the near radius `r ^ cc`
instead of at `R = r^{α/(2d)}`, combined with a cardinality bound of the *compensating*
form `|s| ≤ K r^{-cc}` (which is what the fixed unit ball gives for `0 < r ≤ 1`) and with
`χ ≥ 1`.

The extra factor `χ` (from `χ^{ℓ-4} ≤ χ^{ℓ-3}`) is the only place where `χ ≥ 1` enters;
`r^{-cc} ≥ 1` is not needed, so the statement is uniform in the size of `r`. -/
theorem polygon_bound_small
    {P : ℕ → V → V → ℝ} {nablaT χ : ℝ}
    (H : PowerInputs P nablaT χ)
    (s : Finset V) (w : V → ℝ) (r trc : ℝ) {K cc : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hχ1 : 1 ≤ χ)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hfar : ∀ y : V, y ∉ s → r ^ cc ≤ w y)
    (htail : ∀ y : V, r ^ cc ≤ w y → P 3 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * r ^ (-cc)) :
    P ell 0 0 ≤ max 1 (nablaT * K) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by
  have hsplit := split_bound H s w (r ^ cc) trc htrc hfar htail hell
  have hχ0 : 0 ≤ χ := le_trans zero_le_one hχ1
  have hχn : 0 ≤ χ ^ (ell - 3) := pow_nonneg hχ0 _
  have hχp : 0 ≤ χ ^ (ell - 4) := pow_nonneg hχ0 _
  have hnab : 0 ≤ nablaT := (H.nonneg 3 0 0).trans (H.triSup 0)
  have hrm : 0 ≤ r ^ (-cc) := (Real.rpow_pos_of_pos hr _).le
  -- the cardinality bound, with the compensating factor `r^{-cc}`
  have hstep1 : nablaT * (s.card : ℝ) * χ ^ (ell - 4)
      ≤ nablaT * K * r ^ (-cc) * χ ^ (ell - 4) := by
    have h1 : nablaT * (s.card : ℝ) ≤ nablaT * (K * r ^ (-cc)) :=
      mul_le_mul_of_nonneg_left hcard hnab
    calc nablaT * (s.card : ℝ) * χ ^ (ell - 4)
        ≤ nablaT * (K * r ^ (-cc)) * χ ^ (ell - 4) :=
          mul_le_mul_of_nonneg_right h1 hχp
      _ = nablaT * K * r ^ (-cc) * χ ^ (ell - 4) := by ring
  -- `χ ≥ 1` converts `χ^{ℓ-4}` into `χ^{ℓ-3}`
  have hmono : χ ^ (ell - 4) ≤ χ ^ (ell - 3) := pow_le_pow_right₀ hχ1 (by omega)
  have hstep2 : nablaT * K * r ^ (-cc) * χ ^ (ell - 4)
      ≤ nablaT * K * r ^ (-cc) * χ ^ (ell - 3) :=
    mul_le_mul_of_nonneg_left hmono (mul_nonneg (mul_nonneg hnab hK) hrm)
  -- absorb both terms into the maximum
  have hC1 : (1 : ℝ) ≤ max 1 (nablaT * K) := le_max_left _ _
  have hC2 : nablaT * K ≤ max 1 (nablaT * K) := le_max_right _ _
  have htr : trc * χ ^ (ell - 3) ≤ max 1 (nablaT * K) * trc * χ ^ (ell - 3) := by
    have h : trc ≤ max 1 (nablaT * K) * trc := by nlinarith [hC1, htrc]
    calc trc * χ ^ (ell - 3) ≤ (max 1 (nablaT * K) * trc) * χ ^ (ell - 3) :=
        mul_le_mul_of_nonneg_right h hχn
      _ = max 1 (nablaT * K) * trc * χ ^ (ell - 3) := by ring
  have hnr : nablaT * K * r ^ (-cc) * χ ^ (ell - 3)
      ≤ max 1 (nablaT * K) * r ^ (-cc) * χ ^ (ell - 3) := by
    have h1 : nablaT * K * r ^ (-cc) ≤ max 1 (nablaT * K) * r ^ (-cc) :=
      mul_le_mul_of_nonneg_right hC2 hrm
    exact mul_le_mul_of_nonneg_right h1 hχn
  have hsum : max 1 (nablaT * K) * trc * χ ^ (ell - 3)
        + max 1 (nablaT * K) * r ^ (-cc) * χ ^ (ell - 3)
      = max 1 (nablaT * K) * (trc + r ^ (-cc)) * χ ^ (ell - 3) := by ring
  linarith [hsplit, hstep1, hstep2, htr, hnr, hsum]

end PercLib.CriticalLRP.I418C

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C

variable (M : SourceModelData)

/-! ## `χ ≥ 1` at every cutoff, in `ℝ` -/

/-- **`(E_{β_c,r}|K|).toReal ≥ 1`.**  The diagonal `T_{β_c,r}(0,0) = 1` is one term of the
cluster mass `∑'_y T_{β_c,r}(y,0)`, so `cutMassAt r 0 ≥ 1`; finiteness (`hχfin`, itself
forced by any positive lower bound, see `ChiInput.cutMassAt_ne_top_of_le_toReal`) passes
this through `ℝ≥0∞.toReal`. -/
theorem one_le_cutMassAt_toReal (r : ℝ) (hχfin : M.cutMassAt r 0 ≠ ⊤) :
    1 ≤ (M.cutMassAt r 0).toReal := by
  have h : (1 : ℝ≥0∞) ≤ M.cutMassAt r 0 := by
    rw [← M.tsum_cutTwoPointE_eq_cutMassAt r 0]
    calc (1 : ℝ≥0∞) = M.cutTwoPointE r 0 0 := (M.cutTwoPointE_self_eq_one r 0).symm
      _ ≤ ∑' y, M.cutTwoPointE r 0 y := ENNReal.le_tsum 0
  have h2 := ENNReal.toReal_mono hχfin h
  simpa using h2

/-! ## Lemma I.4.18 at a small cutoff, at the model carrier -/

/-- **Lemma I.4.18, `ℓ ≥ 4`, small cutoff `0 < r ≤ 1`, from finite cutoff mass.**

The near ball `s` is required only to lie at distance `≥ r^cc` from `0` and to satisfy the
compensating count `|s| ≤ K r^{-cc}`; both are discharged by
`NearBall.exists_small_near_ball` for the ball `B_{r^cc}` at a later step.

The *only* first-moment input is `hχfin : M.cutMassAt r 0 ≠ ⊤`.  No first-moment lower
comparison is used at small radii — the factor `χ^{ℓ-3}` is produced directly from
`χ^{ℓ-4}` by `χ ≥ 1`, which is free (`one_le_cutMassAt_toReal`).  `χ ≥ 1`,
`PowerInputs`, and the cutoff/uncut tail comparison are all derived. -/
theorem source_polygon_bound_small_of_finite
    (r : ℝ) (s : Finset M.V) {K cc : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hfar : ∀ y : M.V, y ∉ s → r ^ cc ≤ M.S.dist 0 y)
    (hcard : (s.card : ℝ) ≤ K * r ^ (-cc)) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K) * ((M.nablaTail (r ^ cc)).toReal + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  have hχ1 : 1 ≤ (M.cutMassAt r 0).toReal := M.one_le_cutMassAt_toReal r hχfin
  have hH : PowerInputs (polyK (M.cutTwoPoint r)) M.triSelf (M.cutMassAt r 0).toReal :=
    M.source_powerInputs' r hχfin hTri
  have htail : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y →
      polyK (M.cutTwoPoint r) 3 0 y ≤ (M.nablaTail (r ^ cc)).toReal := fun y hy =>
    M.source_triTail' r cc ((M.nablaTail (r ^ cc)).toReal) hχfin hTri
      (fun z hz => M.triPoint_le_nablaTail (r := r ^ cc) hTri hz) y hy
  have hbound := polygon_bound_small hH s (fun y => M.S.dist 0 y) r
    ((M.nablaTail (r ^ cc)).toReal) hr hK hχ1 hell hfar htail
    (M.nablaTail_toReal_nonneg _) hcard
  exact fun x => (M.source_polyK_le_diag r hχfin ell x).trans hbound

/-- **Lemma I.4.18, `ℓ ≥ 4`, small cutoff `0 < r ≤ 1`, with the first-moment lower
comparison.**  Same as `source_polygon_bound_small_of_finite`, but finiteness of `χ` at
the cutoff is *derived* from the positive lower bound `c₀ r^α ≤ χ` rather than assumed
(`ChiInput.cutMassAt_ne_top_of_le_toReal`).  This is the shape that composes with the
paper's Proposition I.4.2. -/
theorem source_polygon_bound_small
    (r : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 0 < r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχ : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hfar : ∀ y : M.V, y ∉ s → r ^ cc ≤ M.S.dist 0 y)
    (hcard : (s.card : ℝ) ≤ K * r ^ (-cc)) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K) * ((M.nablaTail (r ^ cc)).toReal + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) :=
  M.source_polygon_bound_small_of_finite r s hr hK
    (PercLib.CriticalLRP.I418C.ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ hr hχ)
    hTri hell hfar hcard

/-- **Finiteness of `χ` at small cutoffs propagates downwards from one finite cutoff.**
`r ↦ E_{β_c,r}|K|` is nondecreasing, so a single finite value at `r₁ ≥ 1` covers the whole
small-radius range.  This is what lets the small-radius assembly run with no
Proposition-I.4.2 input at all. -/
theorem cutMassAt_ne_top_of_le {r r₁ : ℝ} (hrr₁ : r ≤ r₁)
    (hfin : M.cutMassAt r₁ 0 ≠ ⊤) : M.cutMassAt r 0 ≠ ⊤ := by
  refine ne_top_of_le_ne_top hfin ?_
  rw [M.cutMassAt_zero_eq_cutMoment r, M.cutMassAt_zero_eq_cutMoment r₁]
  exact M.cutMoment_monotone 1 hrr₁

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.I418C.NearBall

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-! ## The near ball below radius `1` -/

/-- **The small-radius near ball.**  For every `cc > 0` there is `K > 0` — namely
`max 1 |B_1|`, a constant of the model — such that for every `0 < r ≤ 1` the ball
`B_{r^cc}` is a finite set whose complement is at distance `≥ r^cc` from `0` and whose
cardinality satisfies the compensating bound `|B_{r^cc}| ≤ K r^{-cc}`.

This is the small-radius replacement for `exists_near_ball`: since `r^cc ≤ 1`, the ball
is contained in the *fixed* unit ball, so no polynomial growth in `R` is used.  (The
compensating `r^{-cc} ≥ 1` is exactly the `r^{-c}` term of the source's right-hand side.) -/
theorem exists_small_near_ball {cc : ℝ} (hcc : 0 < cc) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ s : Finset M.V,
      (∀ y : M.V, y ∉ s → r ^ cc ≤ M.S.dist 0 y) ∧ (s.card : ℝ) ≤ K * r ^ (-cc) := by
  refine ⟨max 1 ((M.ball 1).ncard : ℝ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr hr1
  have hR1 : r ^ cc ≤ 1 := Real.rpow_le_one hr.le hr1 hcc.le
  have hfin : (M.ball (r ^ cc)).Finite := PercLib.CriticalLRP.BallAverage.ball_finite M _
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro y hy
    have hnot : y ∉ M.ball (r ^ cc) := fun hc => hy ((Set.Finite.mem_toFinset hfin).2 hc)
    have hlt : r ^ cc < M.S.ρ (toVec y) := lt_of_not_ge hnot
    rw [SourceModelData.dist_zero_eq M y]
    exact hlt.le
  · have hmono : ((M.ball (r ^ cc)).ncard : ℝ) ≤ ((M.ball 1).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard
        (PercLib.CriticalLRP.BallAverage.ball_mono M hR1)
        (PercLib.CriticalLRP.BallAverage.ball_finite M 1)
    have hone : (1 : ℝ) ≤ r ^ (-cc) := by
      have h := Real.rpow_le_rpow_of_nonpos hr hr1 (by linarith : -cc ≤ 0)
      simpa using h
    have hK1 : (1 : ℝ) ≤ max 1 ((M.ball 1).ncard : ℝ) := le_max_left _ _
    have hK2 : ((M.ball 1).ncard : ℝ) ≤ max 1 ((M.ball 1).ncard : ℝ) := le_max_right _ _
    have hK0 : (0 : ℝ) < max 1 ((M.ball 1).ncard : ℝ) := lt_of_lt_of_le zero_lt_one hK1
    have hstep : max 1 ((M.ball 1).ncard : ℝ)
        ≤ max 1 ((M.ball 1).ncard : ℝ) * r ^ (-cc) := by
      simpa using mul_le_mul_of_nonneg_left hone hK0.le
    have hbound := (hmono.trans hK2).trans hstep
    rwa [Set.ncard_eq_toFinset_card (M.ball (r ^ cc)) hfin] at hbound

/-- **Compatibility with the landed near ball.**  The small-radius near ball above is not a
new obligation: it is *implied* by `NearBall.exists_near_ball` evaluated at `R = 1`, because
for `0 < r ≤ 1` the ball `B_{r^cc}` is inside `B_1` and `r^{-cc} ≥ 1`.  (The version above is
sharper: its constant is `max 1 |B_1|` rather than the cruder `max (2^d) ((2C+1)^d)` produced
by the normalized cube count at `R = 1`.) -/
theorem exists_small_near_ball_of_near_ball {cc : ℝ} (hcc : 0 < cc) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ s : Finset M.V,
      (∀ y : M.V, y ∉ s → r ^ cc ≤ M.S.dist 0 y) ∧ (s.card : ℝ) ≤ K * r ^ (-cc) := by
  obtain ⟨K, hK0, hK⟩ := exists_near_ball M
  refine ⟨K, hK0, fun r hr hr1 => ?_⟩
  obtain ⟨s, hfar, hcard⟩ := hK 1 le_rfl
  have hR1 : r ^ cc ≤ 1 := Real.rpow_le_one hr.le hr1 hcc.le
  have hone : (1 : ℝ) ≤ r ^ (-cc) := by
    have h := Real.rpow_le_rpow_of_nonpos hr hr1 (by linarith : -cc ≤ 0)
    simpa using h
  refine ⟨s, fun y hy => (hR1.trans (hfar y hy)), ?_⟩
  have hstep : K * (1 : ℝ) ^ (M.d : ℝ) ≤ K * r ^ (-cc) := by
    rw [Real.one_rpow, mul_one]
    simpa using mul_le_mul_of_nonneg_left hone hK0.le
  exact hcard.trans hstep

/-- **The normalized ball count cannot hold below radius `1`.**  For every model there is
no constant `K` with `|B_R| ≤ K R^d` for all `R ∈ (0,1]`: the ball contains `0`, so
`1 ≤ |B_R| ≤ K R^d → 0` as `R → 0`.  This is the precise obstruction that forces the
small-radius assembly above to use the fixed unit ball and the compensating `r^{-c}`;
it is not a source error (the source only evaluates the count at `R = r^{α/(2d)}` on the
range where the conclusion is applied, cf. Lemma I.4.19). -/
theorem not_forall_card_le_rpow :
    ¬ ∃ K : ℝ, ∀ R : ℝ, 0 < R → R ≤ 1 →
      ((M.ball R).ncard : ℝ) ≤ K * R ^ (M.d : ℝ) := by
  rintro ⟨K, hK⟩
  set R : ℝ := min 1 (1 / (2 * |K| + 1)) with hRdef
  have hden : (0 : ℝ) < 2 * |K| + 1 := by positivity
  have hRpos : 0 < R := lt_min one_pos (by positivity)
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRle : R ≤ 1 / (2 * |K| + 1) := min_le_right _ _
  have h0 : (0 : M.V) ∈ M.ball R := by
    simp only [SourceModelData.ball, Set.mem_ofPred_eq]
    rw [show toVec (0 : M.V) = 0 from by funext i; simp [PercLib.CriticalLRP.Orchestration.toVec],
      M.S.ρ_zero]
    exact hRpos.le
  have h1 : (1 : ℝ) ≤ ((M.ball R).ncard : ℝ) := by
    have hsub : ({0} : Set M.V) ⊆ M.ball R := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h0
    have h := Set.ncard_le_ncard hsub (PercLib.CriticalLRP.BallAverage.ball_finite M R)
    have hsingle : ({0} : Set M.V).ncard = 1 := by simp
    rw [hsingle] at h
    exact_mod_cast h
  exact absurd (h1.trans (hK R hRpos hR1)) (not_le.mpr (by
    have hRd : R ^ (M.d : ℝ) ≤ R := by
      rw [Real.rpow_natCast]
      exact pow_le_of_le_one hRpos.le hR1 (Nat.ne_of_gt M.hd)
    have h1 : K * R ^ (M.d : ℝ) ≤ |K| * R ^ (M.d : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hRpos.le _)
    have h2 : |K| * R ^ (M.d : ℝ) ≤ |K| * R :=
      mul_le_mul_of_nonneg_left hRd (abs_nonneg K)
    have h3 : |K| * R ≤ |K| * (1 / (2 * |K| + 1)) :=
      mul_le_mul_of_nonneg_left hRle (abs_nonneg K)
    have h4 : |K| * (1 / (2 * |K| + 1)) < 1 := by
      rw [mul_one_div, div_lt_one hden]
      linarith [abs_nonneg K]
    linarith [h1, h2, h3, h4]))

end PercLib.CriticalLRP.I418C.NearBall

namespace PercLib.CriticalLRP.I418C

open Filter Topology
open PercLib.CriticalLRP Orchestration

/-! ## Lemma I.4.18 for `0 < r ≤ 1`, with all ball data discharged -/

/-- **Lemma I.4.18 at small radii from one finite cutoff, uniformly in `r` and `ℓ`, for
every exponent `c > 0`.**

Because `polygon_bound_small` never uses `1 ≤ r` (the compensating factor `r^{-c}` and
`χ ≥ 1` replace the polynomial ball count), the small-radius half of Lemma I.4.18 holds
with *any* positive exponent `c`, with the constant
`C = max 1 (∇_{β_c} · max 1 |B_1|)` — a constant of the model, independent of `r` and `ℓ`.
The tail is the genuine source object `∇_{r^c} = M.nablaTail (r^c)`.

The *only* moment input is finiteness of `E_{β_c,r₁}|K|` at one cutoff `r₁ ≥ 1`
(monotonicity of `r ↦ E_{β_c,r}|K|` then gives it for every `r ≤ 1`).  In particular
neither Proposition I.4.2 nor the lower comparison `E|K| ⪰ r^α` is needed below radius `1`.

Being generic in `c` is what lets this compose with the landed `r ≥ 1` theorem
`exists_uniform_source_polygon_bound_of_triangle_first_moment`, whose exponent is only
existentially known. -/
theorem exists_uniform_source_polygon_bound_small_radius_of_finite
    (M : SourceModelData)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hfin : ∃ r₁ : ℝ, 1 ≤ r₁ ∧ M.cutMassAt r₁ 0 ≠ ⊤) :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ {ell : ℕ}, 4 ≤ ell → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : M.V,
        (⨆ x : M.V, polyK (M.cutTwoPoint r) ell 0 x) = polyK (M.cutTwoPoint r) ell 0 0 ∧
        polyK (M.cutTwoPoint r) ell 0 x
          ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) *
            ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  intro c hc
  obtain ⟨K, hK0, hball⟩ := NearBall.exists_small_near_ball M hc
  obtain ⟨r₁, hr₁, hfin₁⟩ := hfin
  refine ⟨max 1 (M.triSelf * K), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ell hell r hr hr1 x
  obtain ⟨s, hfar, hcard⟩ := hball r hr hr1
  have hχfin : M.cutMassAt r 0 ≠ ⊤ := M.cutMassAt_ne_top_of_le (le_trans hr1 hr₁) hfin₁
  have hdiag : ∀ y : M.V, polyK (M.cutTwoPoint r) ell 0 y
      ≤ polyK (M.cutTwoPoint r) ell 0 0 :=
    fun y => M.source_polyK_le_diag r hχfin ell y
  have hbdd : BddAbove (Set.range (fun y : M.V => polyK (M.cutTwoPoint r) ell 0 y)) :=
    ⟨polyK (M.cutTwoPoint r) ell 0 0, by
      rintro _ ⟨y, rfl⟩
      exact hdiag y⟩
  refine ⟨le_antisymm (ciSup_le hdiag) (le_ciSup hbdd (0 : M.V)), ?_⟩
  exact M.source_polygon_bound_small_of_finite (cc := c) r s hr hK0.le hχfin hTri hell
    hfar hcard x

/-- **Lemma I.4.18 at small radii, uniformly in `r` and `ℓ`, from Proposition I.4.2.**
The Proposition-I.4.2-shaped input `hP` is used *only* through finiteness of `χ` at one
cutoff (`r₁ = 1`); the lower comparison `E|K| ⪰ r^α` plays no other role below radius `1`. -/
theorem exists_uniform_source_polygon_bound_small_radius
    (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ {ell : ℕ}, 4 ≤ ell → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : M.V,
        (⨆ x : M.V, polyK (M.cutTwoPoint r) ell 0 x) = polyK (M.cutTwoPoint r) ell 0 0 ∧
        polyK (M.cutTwoPoint r) ell 0 x
          ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) *
            ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  have hβ : 0 < (M.betaCrit : ℝ) := ChiInput.betaCrit_pos_of_tendsto_chi_div M hP
  obtain ⟨c₀, hc₀, hχu⟩ := ChiInput.exists_chi_lower_uniform M hβ hP
  have hfin : ∃ r₁ : ℝ, 1 ≤ r₁ ∧ M.cutMassAt r₁ 0 ≠ ⊤ :=
    ⟨1, le_rfl,
      ChiInput.cutMassAt_ne_top_of_le_toReal M hc₀ one_pos (by simpa using hχu 1 one_pos)⟩
  exact exists_uniform_source_polygon_bound_small_radius_of_finite M hTri hfin

/-! ## Reconciliation with the landed `r ≥ 1` theorem -/

/-- **Lemma I.4.18 for every `r > 0`.**

The landed theorem `exists_uniform_source_polygon_bound_of_triangle_first_moment` is the
`r ≥ 1` half (it is invoked verbatim below, with its statement unchanged); the small-radius
half is `exists_uniform_source_polygon_bound_small_radius`, run at the *same* exponent `c`
(the landed theorem's existential `c`, which the small-radius half accepts because it is
generic in `c`).  The two constants are combined by `max`, which does not change either
claim on its own range.

Conclusion: there are `c, C > 0`, independent of `r` and `ℓ`, with

  `sup_x T^ℓ_{β_c,r}(0,x) = T^ℓ_{β_c,r}(0,0) ≤ C (∇_{r^c} + r^{-c}) χ^{ℓ-3}`

for every `ℓ ≥ 4` and every `r > 0`, `χ = (E_{β_c,r}|K|).toReal` and `∇_{r^c}` the genuine
model-norm tail `M.nablaTail (r^c)`.  (`ℓ = 3` is the separate constant bound
`TailConstant.source_polyK_three_le_triSelf`; the printed `ℓ = 3` display is false, see
`Core.one_le_polyK_three`.) -/
theorem exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii
    (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {ell : ℕ}, 4 ≤ ell → ∀ r : ℝ, 0 < r → ∀ x : M.V,
        (⨆ x : M.V, polyK (M.cutTwoPoint r) ell 0 x) = polyK (M.cutTwoPoint r) ell 0 0 ∧
        polyK (M.cutTwoPoint r) ell 0 x
          ≤ C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) *
            ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hlarge⟩ :=
    exists_uniform_source_polygon_bound_of_triangle_first_moment M hP hTri
  obtain ⟨C₂, hC₂, hsmall⟩ :=
    exists_uniform_source_polygon_bound_small_radius M hP hTri c₁ hc₁
  refine ⟨c₁, max C₁ C₂, hc₁, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro ell hell r hr x
  have hAB : (0 : ℝ) ≤ (M.nablaTail (r ^ c₁)).toReal + r ^ (-c₁) := by
    have h1 := M.nablaTail_toReal_nonneg (r ^ c₁)
    have h2 := Real.rpow_pos_of_pos hr (-c₁)
    linarith
  have hχk : (0 : ℝ) ≤ ((M.cutMassAt r 0).toReal) ^ (ell - 3) :=
    pow_nonneg ENNReal.toReal_nonneg _
  -- multiplying the constant by `max C₁ C₂` only increases the right-hand side
  have hmono : ∀ {D D' : ℝ}, D ≤ D' →
      D * ((M.nablaTail (r ^ c₁)).toReal + r ^ (-c₁)) *
          ((M.cutMassAt r 0).toReal) ^ (ell - 3)
        ≤ D' * ((M.nablaTail (r ^ c₁)).toReal + r ^ (-c₁)) *
          ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
    intro D D' hDD'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD' hAB) hχk
  rcases le_or_gt 1 r with hr1 | hr1
  · obtain ⟨hsup, hb⟩ := hlarge hell r hr1 x
    exact ⟨hsup, hb.trans (hmono (le_max_left _ _))⟩
  · obtain ⟨hsup, hb⟩ := hsmall hell r hr hr1.le x
    exact ⟨hsup, hb.trans (hmono (le_max_right _ _))⟩

end PercLib.CriticalLRP.I418C

namespace PercLib.CriticalLRP.I418C

open Filter Topology
open PercLib.CriticalLRP Orchestration

/-! ## The printed `ℓ = 3` case at small radii

The landed refutation of the printed `ℓ = 3` display (`Core.one_le_polyK_three` together
with `LowOrder.not_forall_le_tail_add_rpow`) is a **large-`r`** statement: it uses
`∇_{r^c} → 0` and `r^{-c} → 0` as `r → ∞`.  Below radius `1` the same display is *true*,
because the compensating factor satisfies `r^{-c} ≥ 1`; this closes the source's stated
range `ℓ ≥ 3` completely on `0 < r ≤ 1` (and leaves `ℓ ≥ 4` as the honest range on
`r ≥ 1`). -/

/-- **The printed `ℓ = 3` bound of Lemma I.4.18 at small radii.**  For `0 < r ≤ 1` and any
`c > 0`,
`sup_x T^3_{β_c,r}(0,x) ≤ max 1 (∇_{β_c}) (∇_{r^c} + r^{-c})`,
with no first-moment input at all: the diagonal maximality `T^3(0,x) ≤ T^3(0,0)` and the
constant bound `T^3_{β_c,r}(0,0) ≤ ∇_{β_c}` (the `ℓ = 3` case available at every cutoff) are
absorbed by `r^{-c} ≥ 1`. -/
theorem source_polyK_three_le_small_radius
    (M : SourceModelData) (r : ℝ) {c : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c)
    (hχfin : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) 3 0 x
      ≤ max 1 M.triSelf * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) := by
  have hrm : (1 : ℝ) ≤ r ^ (-c) := by
    have h := Real.rpow_le_rpow_of_nonpos hr hr1 (by linarith : -c ≤ 0)
    simpa using h
  have hnab := M.nablaTail_toReal_nonneg (r ^ c)
  have hX : (1 : ℝ) ≤ (M.nablaTail (r ^ c)).toReal + r ^ (-c) := by linarith
  have hC0 : (0 : ℝ) ≤ max 1 M.triSelf := le_trans zero_le_one (le_max_left _ _)
  intro x
  have hthree : polyK (M.cutTwoPoint r) 3 0 x ≤ M.triSelf :=
    (M.source_polyK_le_diag r hχfin 3 x).trans
      ((M.cutTriPoint_def r 0).trans_le (M.source_triSup' r hχfin hTri 0))
  calc polyK (M.cutTwoPoint r) 3 0 x ≤ M.triSelf := hthree
    _ ≤ max 1 M.triSelf := le_max_right _ _
    _ = max 1 M.triSelf * 1 := (mul_one _).symm
    _ ≤ max 1 M.triSelf * ((M.nablaTail (r ^ c)).toReal + r ^ (-c)) :=
        mul_le_mul_of_nonneg_left hX hC0

end PercLib.CriticalLRP.I418C
