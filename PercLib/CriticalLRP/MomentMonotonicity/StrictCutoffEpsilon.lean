/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Definition I.1.5: the *strict* cutoff domination at an arbitrary source norm

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 (`.scratch/source/paper.html#S1.Thmthm5@L435-L448`).

The parenthetical of Definition I.1.5 says: for every `r < ∞` there is `ε = ε r > 0`
with `J_r ≤ (1 - ε) J`, so that `P_{β_c, r}` is dominated by the subcritical
`P_{(1-ε) β_c}`.  This file proves that statement for the genuine `SourceModelData` of
`Orchestration/Data/Defs.lean`, at an arbitrary admissible `SourceNormData`, by a route
that never forms `J(0⁺)`.

## Why not `J r / J(0⁺)`

For the source power law `K s = s ^ (-d-α)` we have `K s → ∞` as `s ↓ 0`, so the formal
ratio `J r / J(0⁺)` is `0`: it is not positive, and the argument built on it gives only
the non-strict comparison `J_r ≤ J` (already available as
`SourceModelData.cutKernel_le_kernel`).  What is actually needed is a positive lower bound
`t₀` on the length of a nonzero lattice vector: then `J s ≤ J t₀` at every attained
distance `s ≥ t₀`, and `J r > 0`, so `ε r = min (1/2) (J r / (2 J t₀))` is a genuine
strict coefficient.

## The two inputs, proved here

* `SourceNormData.exists_attained_lattice_min` — there is a *nearest nonzero lattice
  vector*: `t₀ = ρ v₀ > 0` for some `v₀ ≠ 0`, and `t₀ ≤ ρ v` for every `v ≠ 0`.  The
  nonzero lattice points in the ball of radius `ρ v₁` form a finite nonempty set
  (`SourceNormData.finite_ball`, the finite-cell packing behind Lemma I.4.6), so `ρ`
  attains a minimum there, and every lattice point outside that ball is further away.
  `SourceNormData.exists_lattice_spacing` records the weaker lower-bound form used by the
  coefficient, obtained more cheaply from `exists_pos_mul_norm_le_of_pos_def` and the fact
  that a nonzero integer vector has norm at least `1`.
* `SourceModelData.K_pos` — `K r > 0` for every `r > 0`.  `K_eq_integral` writes `K r` as
  the tail integral of `|K'|`, and `exists_error` squeezes `|K' s|` between
  `(1/2) s ^ (-d-α-1)` and `2 s ^ (-d-α-1)` on a tail (`SourceModelData.exists_deriv_bounds`),
  so `K r` dominates a strictly positive convergent integral.

## The result

* `SourceModelData.exists_epsilon_domination`: for every `r > 0` there is `ε` with
  `0 < ε < 1` and `J_r ≤ (1 - ε) J` on **every** unordered pair, loops included, at an
  arbitrary admissible source norm; `ε` depends on `r` and the model only, never on the
  vertices.
* `SourceModelData.cutLaw_le_reduced`: hence `P_{β_c, r} ⪯ P_{(1-ε) β_c}` on increasing
  measurable events, and `SourceModelData.betaCrit_mul_lt_of_eps` says the reduced
  parameter is *strictly* below `β_c`.
* `SourceModelData.cutLaw_infiniteClusterProb_eq_zero`: so `P_{β_c, r}` has no infinite
  cluster (given `0 < β_c`), which is the literal printed conclusion.

Both regimes of `r` are covered by the same coefficient.  For `r < t₀` no nonzero lattice
vector has length `≤ r`, so `J_r ≡ 0` and the inequality is trivial; for `r ≥ t₀` the
factor `1/2` in the `min` keeps `ε < 1`.

## Non-vacuity

`Flat.flat_lattice_spacing` shows the flat normalized norm of `FlatNorm/Defs.lean` has
lattice spacing `1/2`, so no unit-spacing hypothesis is smuggled in, and
`Flat.flat_coefficient_value` computes the coefficient at `r = 1` there as `1/16` — where
the raw sup-norm coefficient `1 - K r / K 1` is `0`.  `Witness.sourceModelWitness`
inhabits `SourceModelData`, so the quantified statement is not vacuous.

## Scope

This is the printed domination and its stochastic consequence.  It is **not** a statement
that any cluster moment is finite: that is the separate obligation
`hutchcroft.i.1.5.step.cutoffmoments`, which needs a subcritical first-moment estimate
plus a tree-graph moment input, and nothing here asserts it.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Analysis.BallRatioLogError
public import PercLib.CriticalLRP.CutoffDominated

set_option autoImplicit false

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP LatticeGeometry FiniteVolume

variable {d : ℕ}

/-! ## A positive lattice spacing for an arbitrary admissible source norm -/

theorem SourceNormData.exists_lattice_spacing (S : SourceNormData d) (hd : 1 ≤ d) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ v : Fin d → ℤ, v ≠ 0 → t0 ≤ S.ρ (toVec v) := by
  have hd0 : 0 < d := hd
  obtain ⟨m, hmpos, hmle⟩ :=
    exists_pos_mul_norm_le_of_pos_def (d := d) S.ρ_add_le S.ρ_continuous S.ρ_smul
      (fun x hx => by
        by_contra hne
        exact absurd hx (ne_of_gt (S.ρ_pos x hne))) hd0
  refine ⟨m, hmpos, fun v hv => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hcast : ((1 : ℤ) : ℝ) ≤ ((|v j| : ℤ) : ℝ) := by
    exact_mod_cast Int.one_le_abs hj
  rw [Int.cast_abs] at hcast
  have hnorm : (1 : ℝ) ≤ ‖toVec v‖ := by
    have h1 : ‖(toVec v) j‖ ≤ ‖toVec v‖ := norm_le_pi_norm (toVec v) j
    have h2 : ‖(toVec v) j‖ = |((v j : ℤ) : ℝ)| := by
      simp [toVec, Real.norm_eq_abs]
    rw [h2] at h1
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ |((v j : ℤ) : ℝ)| := hcast
      _ ≤ ‖toVec v‖ := h1
  calc m = m * 1 := by ring
    _ ≤ m * ‖toVec v‖ := by gcongr
    _ ≤ S.ρ (toVec v) := hmle (toVec v)

/-- **A nearest nonzero lattice vector exists, and its length is a positive global lower
bound.**  Fix any nonzero lattice vector `v₁` and the finite set
`B = {v ≠ 0 : ρ v ≤ ρ v₁}` of nonzero lattice points in the `ρ`-ball of radius `ρ v₁`
(`SourceNormData.finite_ball`, which is `Lemma I.4.6`'s finite-cell packing).  `B` is
nonempty and finite, so `Finset.exists_min_image` produces `v₀ ∈ B` minimising `ρ` over
`B`.  Since `v ↦ ρ v` strictly exceeds `ρ v₁ ≥ ρ v₀` outside `B`, `ρ v₀` is the minimum
of `ρ` over *all* nonzero lattice points, and it is positive.

This is the literal `t₀` of the audited route to Definition I.1.5: an attained minimum of
the lattice distances, so `K t₀` is a value of the profile at an actually attained
argument.  It is *not* `J (0⁺)`, which diverges for the source power law. -/
theorem SourceNormData.exists_attained_lattice_min (S : SourceNormData d) (hd : 1 ≤ d) :
    ∃ t0 : ℝ, 0 < t0 ∧ (∃ v : Fin d → ℤ, v ≠ 0 ∧ S.ρ (toVec v) = t0) ∧
      ∀ v : Fin d → ℤ, v ≠ 0 → t0 ≤ S.ρ (toVec v) := by
  classical
  set v₁ : Fin d → ℤ := Pi.single ⟨0, hd⟩ 1 with hv₁
  have hv₁ne : v₁ ≠ 0 := by
    intro h
    have h1 := congrFun h ⟨0, hd⟩
    rw [hv₁] at h1
    simp at h1
  obtain ⟨C, hC⟩ := exists_unitCube_upper_bound S.ρ S.ρ_continuous
  have hC0 : 0 ≤ C := by
    have h := hC 0 (fun j => by simp)
    rwa [S.ρ_zero] at h
  have hfin : {z : Fin d → ℤ | S.ρ (toVec z) ≤ S.ρ (toVec v₁)}.Finite :=
    S.finite_ball hC hC0 _
  set B : Finset (Fin d → ℤ) := hfin.toFinset.filter (fun z => z ≠ 0) with hBdef
  have hBmem : ∀ z : Fin d → ℤ, z ∈ B ↔ z ≠ 0 ∧ S.ρ (toVec z) ≤ S.ρ (toVec v₁) := by
    intro z
    rw [hBdef, Finset.mem_filter, Set.Finite.mem_toFinset hfin]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hBne : B.Nonempty := ⟨v₁, (hBmem v₁).mpr ⟨hv₁ne, le_rfl⟩⟩
  obtain ⟨v₀, hv₀B, hmin⟩ := Finset.exists_min_image B (fun z => S.ρ (toVec z)) hBne
  have hv₀ne : v₀ ≠ 0 := ((hBmem v₀).mp hv₀B).1
  have hv₀le : S.ρ (toVec v₀) ≤ S.ρ (toVec v₁) := ((hBmem v₀).mp hv₀B).2
  have htoVec : toVec v₀ ≠ 0 := by
    intro h
    exact hv₀ne (funext fun j => by
      have h1 : ((v₀ j : ℤ) : ℝ) = 0 := congrFun h j
      exact_mod_cast h1)
  refine ⟨S.ρ (toVec v₀), S.ρ_pos (toVec v₀) htoVec, ⟨v₀, hv₀ne, rfl⟩, fun v hv => ?_⟩
  by_cases hle : S.ρ (toVec v) ≤ S.ρ (toVec v₁)
  · exact hmin v ((hBmem v).mpr ⟨hv, hle⟩)
  · push Not at hle
    linarith

theorem SourceModelData.exists_lattice_spacing (M : SourceModelData) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0 := by
  obtain ⟨t0, ht0, hlat⟩ := M.S.exists_lattice_spacing M.hd
  refine ⟨t0, ht0, fun v hv => ?_⟩
  have h := hlat v hv
  simpa [SourceNormData.dist, toVec] using h


/-! ## Strict positivity of the source profile -/

/-- **The derivative bounds behind `K > 0`.**  `exists_error` gives
`|K' s| = (1 + δ s) s ^ (-d-α-1)` with `δ → 0`, so on a tail `|K'|` is squeezed between
`(1/2) s ^ (-d-α-1)` and `2 s ^ (-d-α-1)`; the latter makes `|K'|` integrable there. -/
theorem SourceModelData.exists_deriv_bounds (M : SourceModelData) :
    ∃ R : ℝ, 0 < R ∧ IntegrableOn (fun s : ℝ => |deriv M.K s|) (Set.Ioi R) ∧
      (∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|) ∧
      (∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1)) := by
  obtain ⟨δ, hderiv, hlogerr⟩ := M.exists_error
  simp only [Analysis.IsLogErrorFunction, Analysis.LogarithmicallyIntegrable] at hlogerr
  obtain ⟨⟨-, -⟩, hδtend⟩ := hlogerr
  have hcpos : 0 < (M.d : ℝ) + M.α := by
    have h : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hexp : -(M.d : ℝ) - M.α - 1 < -1 := by linarith [M.hα]
  obtain ⟨R₁, hR₁⟩ := Metric.tendsto_atTop.1 hδtend (1 / 2) (by norm_num)
  set R : ℝ := max R₁ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hδbd : ∀ s : ℝ, R ≤ s → |δ s| < 1 / 2 := by
    intro s hs
    have h := hR₁ s (le_trans (le_max_left _ _) hs)
    rwa [Real.dist_eq, sub_zero] at h
  have hlow : ∀ s : ℝ, R < s →
      (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s| := by
    intro s hs
    have hs0 : 0 < s := lt_trans hRpos hs
    rw [hderiv s hs0]
    have h1 : -(1 / 2 : ℝ) < δ s := by
      have h2 := (abs_lt.mp (hδbd s hs.le)).1
      linarith
    have h2 : 0 < s ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hs0 _
    nlinarith
  have hupp : ∀ s : ℝ, R < s →
      |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1) := by
    intro s hs
    have hs0 : 0 < s := lt_trans hRpos hs
    rw [hderiv s hs0]
    have h1 : δ s < 1 / 2 := (abs_lt.mp (hδbd s hs.le)).2
    have h2 : 0 < s ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_pos_of_pos hs0 _
    nlinarith
  have hint : IntegrableOn (fun s : ℝ => |deriv M.K s|) (Set.Ioi R) := by
    have hg : IntegrableOn (fun s : ℝ => 2 * s ^ (-(M.d : ℝ) - M.α - 1))
        (Set.Ioi R) := (integrableOn_Ioi_rpow_of_lt hexp hRpos).const_mul 2
    rw [IntegrableOn] at hg ⊢
    refine Integrable.mono hg ((measurable_deriv M.K).abs.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hp : (0 : ℝ) ≤ s ^ (-(M.d : ℝ) - M.α - 1) :=
      (Real.rpow_pos_of_pos (lt_trans hRpos hs) _).le
    have hp2 : (0 : ℝ) ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1) := by linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hp2] using hupp s hs
  exact ⟨R, hRpos, hint, hlow, hupp⟩

/-- **The source profile is strictly positive.**  `K r = ∫_{Ioi r} |K'|` and `|K'|` is
bounded below by `(1/2) s^(-d-α-1)` on a tail, so the tail integral is at least a
strictly positive convergent integral.  Below the tail threshold, antitonicity of `K`
transfers positivity.

This is the fact that the withdrawn `J(r)/J(0⁺)` route assumed and that the source's
power law does not supply at `0⁺`: at positive arguments it is nevertheless true. -/
theorem SourceModelData.K_pos (M : SourceModelData) {r : ℝ} (hr : 0 < r) : 0 < M.K r := by
  obtain ⟨R, hRpos, hint, hlow, -⟩ := M.exists_deriv_bounds
  have hcpos : 0 < (M.d : ℝ) + M.α := by
    have h : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hexp : -(M.d : ℝ) - M.α - 1 < -1 := by linarith [M.hα]
  have hlarge : ∀ r : ℝ, R ≤ r → 0 < M.K r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
    rw [M.K_eq_integral r hrpos]
    have hintr : IntegrableOn (fun s : ℝ => |deriv M.K s|) (Set.Ioi r) :=
      hint.mono_set (Set.Ioi_subset_Ioi hr)
    have hgint : IntegrableOn (fun s : ℝ => (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1))
        (Set.Ioi r) := (integrableOn_Ioi_rpow_of_lt hexp hrpos).const_mul (1 / 2)
    have hcmp : ∫ s in Set.Ioi r, (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1)
        ≤ ∫ s in Set.Ioi r, |deriv M.K s| :=
      setIntegral_mono_on hgint hintr measurableSet_Ioi
        (fun s hs => hlow s (lt_of_le_of_lt hr hs))
    have hval : ∫ s in Set.Ioi r, (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1)
        = (1 / 2) * (r ^ (-(M.d : ℝ) - M.α) / ((M.d : ℝ) + M.α)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hrpos]
      have hb1 : -(M.d : ℝ) - M.α - 1 + 1 = -((M.d : ℝ) + M.α) := by ring
      rw [hb1, show -(M.d : ℝ) - M.α = -((M.d : ℝ) + M.α) from by ring]
      have hcne : (M.d : ℝ) + M.α ≠ 0 := ne_of_gt hcpos
      field_simp
    have hpos : 0 < (1 / 2) * (r ^ (-(M.d : ℝ) - M.α) / ((M.d : ℝ) + M.α)) := by
      have h1 : 0 < r ^ (-(M.d : ℝ) - M.α) := Real.rpow_pos_of_pos hrpos _
      positivity
    rw [hval] at hcmp
    linarith
  rcases le_or_gt R r with h | h
  · exact hlarge r h
  · have h1 : M.K R ≤ M.K r :=
      M.K_antitone (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hRpos) h.le
    have h2 : 0 < M.K R := hlarge R le_rfl
    linarith

/-! ## The strict edgewise domination -/

/-- **Definition I.1.5, strict coefficient, at an arbitrary admissible source norm.**

If `t₀ > 0` is a lower bound for the `ρ`-length of nonzero lattice vectors, the profile is
antitone and nonnegative on `(0,∞)`, and `K r > 0`, `K t₀ > 0`, then with
`ε r = min (1/2) (K r / (2 K t₀))` we have `J_r ≤ (1 - ε r) · J` at *every* unordered
pair of vertices, loops included.

This is the pair of inequalities that replaces the degenerate `J(r)/J(0⁺)` ratio.  For
`x ≠ y` at distance `s`:
* if `s > r` then `J_r (x,y) = 0` and there is nothing to prove;
* if `s ≤ r` then `J_r (x,y) = K s - K r`, and `ε r · K s ≤ ε r · K t₀ ≤ K r` because
  `K s ≤ K t₀` (this is exactly where `t₀ ≤ s` is used) and `ε r ≤ K r / (2 K t₀)`.

The two halves of the `min` are what keep `0 < ε r < 1` uniformly: the factor `1/2` bounds
`ε` away from `1`, and `K r / (2 K t₀)` is the `r`-dependent smallness. -/
theorem cutRadialSym_le_scaled {d : ℕ} (S : SourceNormData d) {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKnn : ∀ s : ℝ, 0 < s → 0 ≤ K s)
    {t0 r : ℝ} (ht0 : 0 < t0) (hKr : 0 < K r) (hKt0 : 0 < K t0)
    (hlat : ∀ v : Fin d → ℤ, v ≠ 0 → t0 ≤ S.ρ (toVec v)) (e : Sym2 (Fin d → ℤ)) :
    cutRadialSym S K r e ≤
      (1 - min (1 / 2) (K r / (2 * K t0))) * radialSym S K e := by
  have hcoef : (0 : ℝ) ≤ 1 - min (1 / 2) (K r / (2 * K t0)) := by
    have h : min (1 / 2) (K r / (2 * K t0)) ≤ 1 / 2 := min_le_left _ _
    linarith
  induction e using Sym2.ind with
  | _ x y =>
    rw [cutRadialSym, radialSym_mk, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
      simp
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      set s : ℝ := S.dist x y with hsdef
      have hspos : 0 < s := S.dist_pos hxy
      have hst0 : t0 ≤ s := by
        have h := hlat (x - y) (sub_ne_zero.mpr hxy)
        simpa [hsdef, SourceNormData.dist] using h
      rcases le_or_gt s r with hsr | hrs
      · rw [cutoffProfile_of_le hsr]
        have hKs : K s ≤ K t0 := hK (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hspos) hst0
        have hle : min (1 / 2) (K r / (2 * K t0)) ≤ K r / (2 * K t0) := min_le_right _ _
        have hfrac : (0 : ℝ) ≤ K r / (2 * K t0) := div_nonneg hKr.le (by linarith)
        have hεK : min (1 / 2) (K r / (2 * K t0)) * K s ≤ K r := by
          have h1 : min (1 / 2) (K r / (2 * K t0)) * K s ≤ (K r / (2 * K t0)) * K t0 :=
            mul_le_mul hle hKs (hKnn s hspos) hfrac
          have h2 : (K r / (2 * K t0)) * K t0 = K r / 2 := by
            field_simp
          linarith
        nlinarith
      · rw [cutoffProfile_of_lt hrs]
        exact mul_nonneg hcoef (hKnn s hspos)

/-- The same domination for the genuine source-model cutoff kernel. -/
theorem SourceModelData.cutKernel_le_scaled (M : SourceModelData) {t0 r : ℝ} (ht0 : 0 < t0)
    (hr : 0 < r) (hlat : ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) (e : Sym2 M.V) :
    M.cutKernel r e ≤ (1 - min (1 / 2) (M.K r / (2 * M.K t0))) * M.kernel e :=
  cutRadialSym_le_scaled M.S M.K_antitone M.K_nonneg ht0 (M.K_pos hr) (M.K_pos ht0)
    (fun v hv => by
      have h := hlat v hv
      simpa [SourceNormData.dist, toVec] using h) e

/-- **`hutchcroft.i.1.5.step.subcritical`, edgewise form, for the genuine source model.**

For every `r > 0` there is `ε = ε r` with `0 < ε < 1` and `J_r ≤ (1 - ε) J` at every
unordered pair, loops included; `ε` depends on `r` and the model only, never on the
vertices, and the statement holds at a completely arbitrary admissible source norm.

The explicit coefficient is `ε r = min (1/2) (K r / (2 K t₀))` where `t₀ > 0` is any
lattice-spacing lower bound (`SourceModelData.exists_lattice_spacing`). -/
theorem SourceModelData.exists_epsilon_domination (M : SourceModelData) {r : ℝ}
    (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ e : Sym2 M.V, M.cutKernel r e ≤ (1 - ε) * M.kernel e := by
  obtain ⟨t0, ht0, hlat⟩ := M.exists_lattice_spacing
  refine ⟨min (1 / 2) (M.K r / (2 * M.K t0)), ?_, ?_, ?_⟩
  · have hKr : 0 < M.K r := M.K_pos hr
    have hKt0 : 0 < M.K t0 := M.K_pos ht0
    have h : 0 < M.K r / (2 * M.K t0) := div_pos hKr (by linarith)
    exact lt_min (by norm_num) h
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · intro e
    exact M.cutKernel_le_scaled ht0 hr hlat e

/-- **The attained-minimum form for the source model.**  The coefficient of
`SourceModelData.exists_epsilon_domination` may be taken with `t₀` the *attained* minimum
of the distances from the origin to the nonzero lattice points. -/
theorem SourceModelData.exists_attained_lattice_min (M : SourceModelData) :
    ∃ t0 : ℝ, 0 < t0 ∧ (∃ v : M.V, v ≠ 0 ∧ M.S.dist v 0 = t0) ∧
      ∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0 := by
  obtain ⟨t0, ht0, hat, hlat⟩ := M.S.exists_attained_lattice_min M.hd
  refine ⟨t0, ht0, ?_, fun v hv => ?_⟩
  · obtain ⟨v, hv, hveq⟩ := hat
    exact ⟨v, hv, by simpa [SourceNormData.dist, toVec] using hveq⟩
  · simpa [SourceNormData.dist, toVec] using hlat v hv

/-- **The full audited form of `hutchcroft.i.1.5.step.subcritical`.**  A single `t₀`
simultaneously

* is positive and *attained*: it is the distance from the origin to an actual nonzero
  lattice vector `v₀`, `M.S.dist v₀ 0 = t₀` — no `0⁺` limiting argument is used;
* is a lower bound for every attained distance;
* yields, for every `r > 0`, the strict edgewise coefficient
  `ε r = min (1/2) (K r / (2 K t₀))`, which lies in `(0,1)`.

This closes the two points the independent audit left open — attaining `t₀` and the strict
domination — at an arbitrary admissible source norm. -/
theorem SourceModelData.exists_epsilon_domination_attained (M : SourceModelData) :
    ∃ t0 : ℝ, 0 < t0 ∧ (∃ v : M.V, v ≠ 0 ∧ M.S.dist v 0 = t0) ∧
      (∀ v : M.V, v ≠ 0 → t0 ≤ M.S.dist v 0) ∧
      ∀ (r : ℝ), 0 < r → ∀ e : Sym2 M.V,
        M.cutKernel r e ≤ (1 - min (1 / 2) (M.K r / (2 * M.K t0))) * M.kernel e := by
  obtain ⟨t0, ht0, hat, hlat⟩ := M.exists_attained_lattice_min
  exact ⟨t0, ht0, hat, hlat, fun r hr e => M.cutKernel_le_scaled ht0 hr hlat e⟩

/-! ## The stochastic domination at the critical parameter -/

/-- **`J_r ≤ (1-ε) J` implies the per-edge domination at the reduced parameter**: the
cutoff open probability at `β_c` is at most the *uncut* open probability at
`(1 - ε) β_c`. -/
theorem SourceModelData.cutKernel_edgeProb_le_reduced (M : SourceModelData) {r ε : ℝ}
    (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (1 - ε) * M.kernel e) (e : Sym2 M.V) :
    bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit e ≤
      bernoulliEdgeProb M.kernel M.kernel_nonneg
        (M.betaCrit * NNReal.mk (1 - ε) (by linarith)) e := by
  refine PercLib.CriticalLRP.CutoffDominated.bernoulliEdgeProb_le_of_mul_le
    (M.cutKernel_nonneg r) M.kernel_nonneg ?_
  have hcoef : ((M.betaCrit * NNReal.mk (1 - ε) (by linarith) : NNReal) : ℝ)
      = (M.betaCrit : ℝ) * (1 - ε) := by
    rw [NNReal.coe_mul, NNReal.coe_mk]
  rw [hcoef]
  have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.2
  nlinarith [hdom e]

/-- **`P_{β_c,r} ⪯ P_{(1-ε)β_c}`**: the cutoff law at the critical parameter of the
*uncut* kernel is stochastically dominated by the uncut law at the strictly reduced
parameter `(1 - ε) β_c`, on every increasing measurable event.

The reduced parameter is genuinely smaller than `β_c` whenever `ε > 0` and `β_c > 0`;
the present statement is the domination, and it makes no finiteness claim about moments
(that is `hutchcroft.i.1.5.step.cutoffmoments`, not proved here). -/
theorem SourceModelData.cutLaw_le_reduced (M : SourceModelData) {r ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (1 - ε) * M.kernel e)
    {A : Set (Config M.V)} (hA : MeasurableSet A) (hinc : IsIncreasing A) :
    M.cutLaw r A ≤ M.law (M.betaCrit * NNReal.mk (1 - ε) (by linarith)) A := by
  rw [SourceModelData.cutLaw, SourceModelData.law, longRangeMeasure]
  exact edgeMeasure_mono_of_le (M.cutKernel_edgeProb_le_reduced hε0 hε1 hdom) hA hinc

/-- **The reduced parameter is strictly below the critical parameter.**  This is the
"strictly" in the parenthetical of Definition I.1.5: the dominating law is taken at
`(1 - ε) β_c < β_c`, not at `β_c`. -/
theorem SourceModelData.betaCrit_mul_lt_of_eps (M : SourceModelData) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hβ : 0 < M.betaCrit) :
    M.betaCrit * NNReal.mk (1 - ε) (by linarith) < M.betaCrit := by
  have hc : NNReal.mk (1 - ε) (by linarith) < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_mk, NNReal.coe_one]
    linarith
  calc M.betaCrit * NNReal.mk (1 - ε) (by linarith) < M.betaCrit * 1 :=
        mul_lt_mul_of_pos_left hc hβ
    _ = M.betaCrit := mul_one _

/-- **Definition I.1.5, the printed conclusion: `P_{β_c,r}` has no infinite cluster.**

At an arbitrary admissible source norm and every `r > 0`, the cutoff law at the *uncut*
critical parameter is stochastically dominated by the uncut law at the strictly reduced
parameter `(1-ε) β_c < β_c`, where the uncut law has no infinite cluster by the definition
of `β_c` as a threshold (`infiniteClusterProb_eq_zero_of_lt_criticalBeta`).

`0 < β_c` is the paper's `hutchcroft.i.1.2.betac.pos`; it is kept as an explicit
hypothesis here rather than assumed silently.  Nothing about cluster moments is claimed. -/
theorem SourceModelData.cutLaw_infiniteClusterProb_eq_zero (M : SourceModelData) {r : ℝ}
    (hr : 0 < r) (hβ : 0 < M.betaCrit) :
    infiniteClusterProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit = 0 := by
  obtain ⟨t0, ht0, hlat⟩ := M.exists_lattice_spacing
  set ε : ℝ := min (1 / 2) (M.K r / (2 * M.K t0)) with hεdef
  have hKr : 0 < M.K r := M.K_pos hr
  have hKt0 : 0 < M.K t0 := M.K_pos ht0
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hKr (by linarith))
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hdom : ∀ e : Sym2 M.V, M.cutKernel r e ≤ (1 - ε) * M.kernel e :=
    fun e => M.cutKernel_le_scaled ht0 hr hlat e
  have hle := M.cutLaw_le_reduced hε0.le hε1.le hdom
    measurableSet_existsInfiniteCluster isIncreasing_existsInfiniteCluster
  have hpar : M.betaCrit * NNReal.mk (1 - ε) (by linarith) < M.betaCrit :=
    M.betaCrit_mul_lt_of_eps hε0 hε1 hβ
  have hzero : infiniteClusterProb M.kernel M.kernel_nonneg
      (M.betaCrit * NNReal.mk (1 - ε) (by linarith)) = 0 :=
    infiniteClusterProb_eq_zero_of_lt_criticalBeta hpar
  refine le_antisymm ?_ (by simp)
  rw [← hzero]
  exact hle

/-! ## Non-vacuity: a norm whose lattice spacing is `1/2` -/

namespace Flat

/-- The flat normalized norm of `FlatNorm/Defs.lean` has lattice spacing `1/2`: no nonzero
lattice vector is closer to the origin than `e₁`.  This is what forbids any proof that
silently assumes a unit lattice spacing (the raw sup-norm coefficient
`1 - K r / K 1` fails here). -/
theorem flat_lattice_spacing :
    ∀ v : Fin 2 → ℤ, v ≠ 0 → (1 / 2 : ℝ) ≤ flatSourceNorm.ρ (toVec v) := by
  have hcast : ∀ z : ℤ, z ≠ 0 → (1 : ℝ) ≤ |((z : ℤ) : ℝ)| := by
    intro z hz
    have h : ((1 : ℤ) : ℝ) ≤ ((|z| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hz
    rw [Int.cast_abs] at h
    simpa using h
  intro v hv
  have hρ : flatSourceNorm.ρ (toVec v)
      = max (|((v 0 : ℤ) : ℝ)| / 2) (8 * |((v 1 : ℤ) : ℝ)|) := rfl
  rw [hρ]
  rcases eq_or_ne (v 0) 0 with h0 | h0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      exact hv (by funext i; fin_cases i <;> simp [h0, h1])
    have h8 : (8 : ℝ) ≤ 8 * |((v 1 : ℤ) : ℝ)| := by
      have := hcast (v 1) h1
      nlinarith
    have := le_max_right (|((v 0 : ℤ) : ℝ)| / 2) (8 * |((v 1 : ℤ) : ℝ)|)
    linarith
  · have h2 : (1 / 2 : ℝ) ≤ |((v 0 : ℤ) : ℝ)| / 2 := by
      have := hcast (v 0) h0
      linarith
    have := le_max_left (|((v 0 : ℤ) : ℝ)| / 2) (8 * |((v 1 : ℤ) : ℝ)|)
    linarith

/-- **The strict coefficient at the flat norm is `1/16`, not `0`.**  With the source power
law `K s = s ^ (-3)` in `d = 2`, `α = 1`, the cutoff at `r = 1` gets
`ε = min (1/2) (K 1 / (2 K (1/2))) = min (1/2) (1/16) = 1/16`; the withdrawn coefficient
`1 - K r / K 1` would have given `0` and hence only `J_r ≤ J`.

This is a computation about the coefficient; the edgewise inequality itself is the
norm-level `cutRadialSym_le_scaled`, which is instantiated at `flatSourceNorm` and
`modelProfile 2 1` in `flat_edge_strict_domination` below.  (Nothing here claims that the
flat norm together with `modelProfile` is a `SourceModelData`; that would additionally need
`K_eq_integral` and `exists_error`.) -/
theorem flat_coefficient_value :
    min (1 / 2 : ℝ) (modelProfile 2 1 1 / (2 * modelProfile 2 1 (1 / 2))) = 1 / 16 := by
  simp only [modelProfile]
  norm_num [Real.rpow_neg]

/-- The strict edgewise domination at the flat norm, instantiated at the edge `(e₁, 0)`
of `ρ`-length `1/2`: the general theorem needs no unit-spacing hypothesis. -/
theorem flat_edge_strict_domination :
    cutRadialSym flatSourceNorm (modelProfile 2 1) 1 (s(e1, 0))
      ≤ (1 - min (1 / 2 : ℝ)
            (modelProfile 2 1 1 / (2 * modelProfile 2 1 (1 / 2)))) *
          radialSym flatSourceNorm (modelProfile 2 1) (s(e1, 0)) :=
  cutRadialSym_le_scaled flatSourceNorm
    (modelProfile_antitoneOn 2 (by norm_num))
    (fun s hs => (modelProfile_pos (d := 2) (α := (1 : ℝ)) hs).le)
    (t0 := 1 / 2) (r := 1) (by norm_num)
    (modelProfile_pos (d := 2) (α := (1 : ℝ)) one_pos)
    (modelProfile_pos (d := 2) (α := (1 : ℝ)) (by norm_num))
    flat_lattice_spacing (s(e1, 0))

end Flat

namespace Witness

/-- **Non-vacuity of the strict domination.**  The explicit witness model of
`ModelWitness/Defs.lean` satisfies the strict coefficient statement at every `r > 0`. -/
example (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ e : Sym2 (sourceModelWitness 1 le_rfl 1 zero_lt_one).V,
        (sourceModelWitness 1 le_rfl 1 zero_lt_one).cutKernel r e
          ≤ (1 - ε) * (sourceModelWitness 1 le_rfl 1 zero_lt_one).kernel e :=
  (sourceModelWitness 1 le_rfl 1 zero_lt_one).exists_epsilon_domination hr

end Witness

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceNormData.exists_lattice_spacing
#print axioms PercLib.CriticalLRP.Orchestration.SourceNormData.exists_attained_lattice_min
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_lattice_spacing
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_deriv_bounds
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.K_pos
#print axioms PercLib.CriticalLRP.Orchestration.cutRadialSym_le_scaled
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_le_scaled
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_epsilon_domination
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_epsilon_domination_attained
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_edgeProb_le_reduced
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_le_reduced
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_mul_lt_of_eps
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_infiniteClusterProb_eq_zero
#print axioms PercLib.CriticalLRP.Orchestration.Flat.flat_lattice_spacing
#print axioms PercLib.CriticalLRP.Orchestration.Flat.flat_coefficient_value
#print axioms PercLib.CriticalLRP.Orchestration.Flat.flat_edge_strict_domination
