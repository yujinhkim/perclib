/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m6.
Latest independent rebuild at production HEAD `16d9f2aa1e83afeda3fc66117e38ed3352b2e567`; reviewed scratch source `.scratch/review-smwznoz6j/m6/Defs.lean`.

# The parameter regime of the `(HD)`/`(HD+)` case split

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1:

* `(HD)` hypotheses 1–3, p. 9 (and production `Orchestration.HD`);
* `Proposition I.4.2`, p. 34 (three hypotheses, and the exponent comparison
  `2α < (d+α)/2` when `d > 3α`);
* `Corollary I.4.14 (The hydrodynamic condition)`, p. 41;
* `Remark I.4.4`, p. 34 (`H_r` is not logarithmically integrable when `d = 3α < 6`);
* `Theorem I.1.17`, p. 17 (hypothesis `d = 3α < 6` plus `(Hydro)`);
* `Definition I.5.1 / (HD+)`, p. 53 (four alternatives, alternative 4 being
  `d = 3α < 6` plus the hydrodynamic condition).

`(HD+)` is *defined* as `(HD) ∨ (d = 3α < 6 ∧ Hydro)`, so the discussion of "coverage"
is not about a theorem that the model satisfies an alternative, but about the parameter
behaviour of the alternatives themselves.  This file answers, kernel-checked:

* `hdplus_param_regime` : `(HD+)` forces `3α < d ∨ 3α = d ∨ (2 < α ∧ 6 < d)`.  Hence
  `(HD+)` never sits in the source's long-range low-dimensional regime
  (`d < 3α`, `α < 2`), never at the critical dimension with short-range tail
  (`d = 6`, `α > 2`), and never in `d < 6` with `α ≥ 2`.
* `hdplus_alpha_le_two_of_dim_six` : at `d = 6` the alternatives force `α ≤ 2`, which is
  exactly the source's restriction `d_eff = d_c = 6 and α ≤ 2` (p. 8).
* `hd_iff_of_marginal` : on the marginal curve `d = 3α` alternative 1 of `(HD)` is false, so
  `(HD)` reduces to the two two-point alternatives.  Consequently
  `not_hd_of_marginal_lt_six` : `(HD)` is *empty* on the curve `d = 3α < 6`, and
  `hdplus_iff_hydro_of_marginal_lt_six` : there `(HD+)` is *equivalent* to `(Hydro)`.
  This is the precise sense in which alternative 4 of `(HD+)` is not redundant.
* `twoPointLogBound_of_betaCrit_eq_zero` / `not_twoPointLogBound_of_dist_lt_one` : the two
  sharp caveats on alternative 3.  At `β_c = 0` it holds vacuously (when no nonzero lattice
  distance is below `1`), and if some nonzero lattice distance *is* below `1` it fails
  outright, for every `β_c` — the log factor is negative there.  So non-vacuity of `(HD)` 3
  is a statement about a model with `β_c > 0` and a norm with all lattice distances `≥ 1`.
* `hdplus_iff_twoPointLog_of_dim_six` : at the doubly-marginal point `d = 6`, `α = 2`
  `(HD+)` is *equivalent* to the log-corrected two-point estimate of `(HD)` 3.  So at
  that point the whole hypothesis is one model estimate; `(Hydro)` alone, or the
  arithmetic `d = 3α`, does not produce it.
* `hydro_iff_marginal_exponent` and `half_eq_two_alpha_of_marginal`: on the curve
  `d = 3α` the `(Hydro)` exponent `(d+α)/2` equals `2α`, and `two_alpha_lt_half_iff` is
  the exponent comparison `2α < (d+α)/2 ↔ d > 3α` used in Corollary I.4.14.
* `marginal_log_bound_not_o` : the Corollary-I.4.14 input `M_r ⪯ (E|K|)^2 log r` is, at
  the marginal exponent, *not* `o(r^{2α})`; the log factor blocks the deduction of
  `(Hydro)` on the curve, which is why alternative 4 assumes it (`Remark I.4.4`).
* `hd_forces_six_two_of_marginal_le_two` / `hdplus_marginal_dichotomy` : on the marginal
  line `d = 3α` with `α ≤ 2`, `(HD)` forces the doubly-marginal point `(6, 2)` and `(HD+)`
  is exactly `(6, 2)` or `(Hydro)` — there is no third possibility on that line.
* `hdplus_dim_six` / `hdplus_low_dim` : at `d = 6` the alternatives are exactly `α < 2` or
  `α = 2` with the source's log-corrected two-point estimate, and in dimensions `≤ 5` only
  alternative 1 and alternative 4 are available.
* Non-vacuity: `exists_hd`/`exists_hdplus` produce a genuine `SourceModelData` with
  `(HD)` (hence `(HD+)`) holding in every dimension `d ≥ 1`;
  `exists_at_marginal_curve`, `exists_overlap_case_one_two`, `exists_alpha_two` and
  `exists_six_two` show the parameter loci discussed above are inhabited by real models,
  so the collapses above are not statements about an empty parameter set.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs
public import PercLib.CriticalLRP.Analysis.RVAlgebra

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Topology

namespace PercLib.CriticalLRP.Orchestration

namespace HDRegime

open PercLib.CriticalLRP.Analysis

/-! ## The two two-point alternatives, named as in `(HD)` -/

/-- Alternative 2 of `(HD)` (source p. 9): `d > 6` together with
`P_{β_c}(x ↔ y) ⪯ ‖x − y‖^{-d+2}`, in the exact form used by `Orchestration.HD`
(normalized source norm `M.S.ρ` and exponent `-(d : ℝ) + 2`). -/
def TwoPointPowerBound (M : SourceModelData) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
    M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)

/-- Alternative 3 of `(HD)` (source p. 9): `d = 6`, `α = 2` and the log-corrected
two-point estimate `P_{β_c}(x ↔ y) ⪯ (log ‖x − y‖)^{-1} ‖x − y‖^{-d+2}`. -/
def TwoPointLogBound (M : SourceModelData) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
    M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
      * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)

/-- `(HD)` written with the two two-point alternatives named. -/
theorem hd_iff (M : SourceModelData) :
    HD M ↔ (3 * M.α < (M.d : ℝ)) ∨ (6 < M.d ∧ TwoPointPowerBound M) ∨
      (M.d = 6 ∧ M.α = 2 ∧ TwoPointLogBound M) :=
  Iff.rfl

/-- `(HD+)` (Definition I.5.1) written with alternative 4 named, i.e. the hypothesis of
Theorem I.1.17. -/
theorem hdplus_iff (M : SourceModelData) :
    HDplus M ↔ HD M ∨ ((M.d : ℝ) = 3 * M.α ∧ (M.d : ℝ) < 6 ∧ Hydro M) :=
  Iff.rfl

/-- Definition I.5.1 states that the four alternatives cover the hypotheses of
Theorem I.1.9 as listed in `(HD)`; at the level of the interfaces this is the inclusion
`HD ⟹ HD+`. -/
theorem hd_imp_hdplus (M : SourceModelData) (h : HD M) : HDplus M :=
  Or.inl h

/-! ## Two sharp caveats on alternative 3 of `(HD)` (the doubly-marginal point)

Alternative 3 is the only alternative available at `(6, 2)` (`hdplus_iff_twoPointLog_of_dim_six`),
so its satisfiability is worth pinning down.  Unlike the power bound of alternative 2, the
factor `(log ‖x − y‖)^{-1}` is **negative** when `‖x − y‖ < 1`, and it vanishes at
`‖x − y‖ = 1`; and at `β_c = 0` the two-point function vanishes identically.  Both facts
produce degenerate situations, recorded below. -/

/-- `toVec (x − y) ≠ 0` for `x ≠ y`: the embedding of the lattice into the norm space is
injective away from the origin. -/
theorem toVec_sub_ne_zero {M : SourceModelData} {x y : M.V} (hxy : x ≠ y) :
    toVec (x - y) ≠ 0 := by
  intro h
  apply hxy
  funext i
  have hi : ((x - y : M.V) i : ℝ) = 0 := by
    have := congrFun h i
    simpa [toVec] using this
  have hzi : (x - y : M.V) i = 0 := by exact_mod_cast hi
  have h2 : x i - y i = 0 := by simpa using hzi
  exact sub_eq_zero.mp h2

/-- At `β = 0` the law is the point mass at the empty configuration (`longRangeMeasure_zero`),
so distinct vertices are not connected and the two-point function vanishes.  Same argument as
production's `SourceModelData.twoPoint_zero_of_ne`, reproved here to keep the audit
self-contained. -/
theorem twoPoint_zero_of_ne (M : SourceModelData) {x y : M.V} (hxy : x ≠ y) :
    M.twoPoint 0 x y = 0 := by
  have hlaw : M.law 0 = Measure.dirac (∅ : Config M.V) :=
    longRangeMeasure_zero M.kernel M.kernel_nonneg
  have hnot : (∅ : Config M.V) ∉ {ω : Config M.V | Connects ω x y} := by
    simp only [Set.mem_ofPred_eq, Connects, PercLib.Percolation.Bond.openGraph_empty,
      SimpleGraph.reachable_bot]
    exact hxy
  change (M.law 0).real {ω : Config M.V | Connects ω x y} = 0
  rw [hlaw, Measure.dirac_real_apply, Set.indicator_of_notMem hnot]

/-- **Vacuity at `β_c = 0`.**  If `β_c = 0` and the norm has no nonzero lattice distance below
`1`, then alternative 3 of `(HD)` holds with the constant `1`, for trivial reasons: both sides
are `0` respectively nonnegative.  So a claim that `(HD)` 3 is satisfied says nothing about the
model unless `β_c > 0`, which is where the source's perturbative two-point input lives. -/
theorem twoPointLogBound_of_betaCrit_eq_zero (M : SourceModelData) (hβ : M.betaCrit = 0)
    (hmin : ∀ x y : M.V, x ≠ y → 1 ≤ M.S.ρ (toVec (x - y))) : TwoPointLogBound M := by
  refine ⟨1, one_pos, ?_⟩
  intro x y hxy
  have hz : M.twoPoint M.betaCrit x y = 0 := by
    rw [hβ]
    exact twoPoint_zero_of_ne M hxy
  have hρpos : 0 < M.S.ρ (toVec (x - y)) := M.S.ρ_pos _ (toVec_sub_ne_zero hxy)
  have hlog : 0 ≤ Real.log (M.S.ρ (toVec (x - y))) := Real.log_nonneg (hmin x y hxy)
  have hinv : 0 ≤ (Real.log (M.S.ρ (toVec (x - y))))⁻¹ := by
    rw [inv_eq_one_div]
    exact div_nonneg zero_le_one hlog
  have hpow : 0 ≤ (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) :=
    Real.rpow_nonneg hρpos.le _
  have hnn : 0 ≤ (1 : ℝ) * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
      * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) :=
    mul_nonneg (mul_nonneg zero_le_one hinv) hpow
  rw [hz]
  linarith

/-- **Alternative 3 is unsatisfiable for a norm with a lattice distance below `1`.**  If some
`x ≠ y` has `‖x − y‖ < 1`, the factor `(log ‖x − y‖)^{-1}` is negative, so the right-hand
side of the bound of `(HD)` 3 is negative, while the left-hand side is a probability.  For
every `β_c` and every constant `C > 0`, so `TwoPointLogBound M` fails outright — and then
`(HD+)` fails at the doubly-marginal point.  The source's own normalization at `d = 6` (unit
ball of volume `1`, Euclidean-like) has minimal nonzero lattice distance `(π³/6)^{1/6} ≈ 1.315`, so
the source statement is consistent; the formal `SourceNormData` does not enforce this. -/
theorem not_twoPointLogBound_of_dist_lt_one (M : SourceModelData) {x y : M.V} (hxy : x ≠ y)
    (hρ : M.S.ρ (toVec (x - y)) < 1) : ¬ TwoPointLogBound M := by
  rintro ⟨C, hC, hbound⟩
  have hρpos : 0 < M.S.ρ (toVec (x - y)) := M.S.ρ_pos _ (toVec_sub_ne_zero hxy)
  have hlog : Real.log (M.S.ρ (toVec (x - y))) < 0 := Real.log_neg hρpos hρ
  have hinv : (Real.log (M.S.ρ (toVec (x - y))))⁻¹ < 0 := by
    rw [inv_eq_one_div]
    exact div_neg_of_pos_of_neg one_pos hlog
  have hpow : 0 < (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) :=
    Real.rpow_pos_of_pos hρpos _
  have hneg : C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
      * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC hinv) hpow
  have hnonneg : 0 ≤ M.twoPoint M.betaCrit x y := by
    simp [SourceModelData.twoPoint]
  have := hbound x y hxy
  linarith

/-! ## Exponent comparisons: the boundary `d = 3α` -/
/-- The exponent comparison used in the proof of Corollary I.4.14 (p. 41):
`2α < (d+α)/2` exactly when `d > 3α`. -/
theorem two_alpha_lt_half_iff {α d : ℝ} :
    2 * α < (d + α) / 2 ↔ 3 * α < d := by
  constructor <;> intro h <;> linarith

/-- On the marginal curve `d = 3α` the hydrodynamic exponent `(d+α)/2` is exactly
`2α`, so `(Hydro)` is the sharp `M_r = o(r^{2α})` statement there. -/
theorem half_eq_two_alpha_of_marginal {α d : ℝ} (h : d = 3 * α) :
    (d + α) / 2 = 2 * α := by
  rw [h]; ring

/-- `(Hydro)` written with the marginal exponent `2α`, on the curve `d = 3α`. -/
theorem hydro_iff_marginal_exponent (M : SourceModelData) (h : (M.d : ℝ) = 3 * M.α) :
    Hydro M ↔ Tendsto (fun r : ℝ => (M.Mr r : ℝ) / r ^ (2 * M.α)) atTop (𝓝 0) := by
  unfold Hydro
  rw [show ((M.d : ℝ) + M.α) / 2 = 2 * M.α from by rw [h]; ring]

/-- The Corollary-I.4.14 input at the marginal exponent: `r ↦ r^{2α} log r` is not
`o(r^{2α})`.  Hence the bound `M_r ⪯ (E_{β_c,r}|K|)^2 log r` used to deduce `(Hydro)`
when `d > 3α` gives nothing on the curve `d = 3α`, matching Remark I.4.4. -/
theorem marginal_log_bound_not_o (M : SourceModelData) :
    ¬ Tendsto (fun r : ℝ => (r ^ (2 * M.α) * Real.log r) / r ^ (2 * M.α)) atTop (𝓝 0) := by
  have hlog : ¬ Tendsto (fun r : ℝ => Real.log r) atTop (𝓝 0) := by
    intro h
    have h2 : ∀ᶠ r : ℝ in atTop, Real.log r < 1 := h.eventually (Iio_mem_nhds one_pos)
    have h1 : ∀ᶠ r : ℝ in atTop, 1 ≤ Real.log r :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
    obtain ⟨r, hr1, hr2⟩ := (h1.and h2).exists
    linarith
  have hcongr : (fun r : ℝ => (r ^ (2 * M.α) * Real.log r) / r ^ (2 * M.α))
      =ᶠ[atTop] fun r : ℝ => Real.log r := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hne : r ^ (2 * M.α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr _)
    field_simp
  intro h
  exact hlog (h.congr' hcongr)

/-! ## The marginal curve `d = 3α` -/

/-- On the curve `d = 3α` alternative 1 of `(HD)` is false, so `(HD)` reduces to its two
two-point alternatives. -/
theorem hd_iff_of_marginal (M : SourceModelData) (h : (M.d : ℝ) = 3 * M.α) :
    HD M ↔ (6 < M.d ∧ TwoPointPowerBound M) ∨
      (M.d = 6 ∧ M.α = 2 ∧ TwoPointLogBound M) := by
  rw [hd_iff]
  constructor
  · rintro (h1 | h2 | h3)
    · exact absurd h1 (by linarith)
    · exact Or.inl h2
    · exact Or.inr h3
  · rintro (h2 | h3)
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)

/-- `(HD)` is empty on the marginal curve in low dimensions: `d = 3α < 6` satisfies
alternative 2 only if `d > 6`, and alternative 3 only if `d = 6`.  This is why the
fourth alternative of `(HD+)` (Theorem I.1.17's hypothesis) is needed there. -/
theorem not_hd_of_marginal_lt_six (M : SourceModelData) (h : (M.d : ℝ) = 3 * M.α)
    (h6 : (M.d : ℝ) < 6) : ¬ HD M := by
  intro hHD
  rw [hd_iff_of_marginal M h] at hHD
  rcases hHD with ⟨hlt, -⟩ | ⟨hd6, -⟩
  · have hlt' : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast hlt
    linarith
  · have : (M.d : ℝ) = 6 := by exact_mod_cast hd6
    linarith

/-- `(HD+)` is *equivalent* to `(Hydro)` on the marginal curve `d = 3α < 6`: the whole
hypothesis there is the hydrodynamic condition, and no two-point or triangle input is
required (nor can alternative 1 of `(HD)` help).  Source-wise this is the regime of
Theorem I.1.17, and the `(Hydro)` input there is precisely the one paper I defers to
paper III (Theorem III.1.11), since Corollary I.4.14 only produces `(Hydro)` under `(HD)`
and `(HD)` is empty on this curve (`not_hd_of_marginal_lt_six`). -/
theorem hdplus_iff_hydro_of_marginal_lt_six (M : SourceModelData) (h : (M.d : ℝ) = 3 * M.α)
    (h6 : (M.d : ℝ) < 6) : HDplus M ↔ Hydro M := by
  constructor
  · rintro (hHD | ⟨-, -, hHydro⟩)
    · exact absurd hHD (not_hd_of_marginal_lt_six M h h6)
    · exact hHydro
  · intro hHydro
    exact Or.inr ⟨h, h6, hHydro⟩

/-- On the marginal curve `d = 3α` the fourth alternative of `(HD+)` forces `α < 2`, so
it lives in the source's long-range regime (Figure 1: `α < 2` along `d = 3α`). -/
theorem alpha_lt_two_of_marginal_lt_six {α d : ℝ} (h : d = 3 * α) (h6 : d < 6) :
    α < 2 := by
  linarith

/-- Alternative 4 of `(HD+)` is incompatible with `(HD)`, so `(HD+)` is a union of a
disjoint pair at the level of parameters. -/
theorem not_hd_of_fourth (M : SourceModelData)
    (h : (M.d : ℝ) = 3 * M.α ∧ (M.d : ℝ) < 6 ∧ Hydro M) : ¬ HD M :=
  not_hd_of_marginal_lt_six M h.1 h.2.1

/-! ## The doubly-marginal point `d = 6`, `α = 2` -/

/-- Alternative 3 of `(HD)` excludes alternative 1: at `d = 6`, `α = 2` we have
`3α = d`. -/
theorem not_three_alpha_lt_of_dim_six {α d : ℝ} (hd : d = 6) (hα : α = 2) :
    ¬ (3 * α < d) := by
  rw [hd, hα]; norm_num

/-- Alternative 3 of `(HD)` excludes alternative 2 (`d = 6` is not `d > 6`). -/
theorem not_six_lt_of_dim_six (M : SourceModelData) (hd : M.d = 6) : ¬ (6 < M.d) := by
  rw [hd]; norm_num

/-- At the doubly-marginal point `d = 6`, `α = 2` the fourth alternative of `(HD+)` is
false, since it requires `d < 6`. -/
theorem not_fourth_of_dim_six (M : SourceModelData) (hd : M.d = 6) :
    ¬ ((M.d : ℝ) = 3 * M.α ∧ (M.d : ℝ) < 6 ∧ Hydro M) := by
  have hd' : (M.d : ℝ) = 6 := by exact_mod_cast hd
  rintro ⟨-, hlt, -⟩
  linarith

/-- **The doubly-marginal collapse.**  At `d = 6`, `α = 2` the alternatives of `(HD+)`
reduce to alternative 3 alone: `(HD+)` is equivalent to the log-corrected two-point
estimate `P_{β_c}(x ↔ y) ⪯ (log ‖x − y‖)^{-1} ‖x − y‖^{-4}`.  In particular neither
`(Hydro)` nor the arithmetic identity `d = 3α` produces `(HD+)` there. -/
theorem hdplus_iff_twoPointLog_of_dim_six (M : SourceModelData) (hd : M.d = 6)
    (hα : M.α = 2) : HDplus M ↔ TwoPointLogBound M := by
  have hd' : (M.d : ℝ) = 6 := by exact_mod_cast hd
  constructor
  · rintro (hHD | hfourth)
    · rw [hd_iff] at hHD
      rcases hHD with h1 | h2 | h3
      · exact absurd h1 (not_three_alpha_lt_of_dim_six hd' hα)
      · exact absurd h2.1 (not_six_lt_of_dim_six M hd)
      · exact h3.2.2
    · exact absurd hfourth (not_fourth_of_dim_six M hd)
  · intro hlog
    exact Or.inl (Or.inr (Or.inr ⟨hd, hα, hlog⟩))

/-! ## The parameter regime of `(HD+)` -/

/-- **Regime classification.**  Every alternative of `(HD+)` satisfies either the
marginal inequality `3α ≤ d` or the short-range condition `2 < α` with `d > 6`. -/
theorem hdplus_param_regime (M : SourceModelData) (h : HDplus M) :
    3 * M.α < (M.d : ℝ) ∨ 3 * M.α = (M.d : ℝ) ∨ (2 < M.α ∧ 6 < (M.d : ℝ)) := by
  rw [hdplus_iff] at h
  rcases h with hHD | ⟨hmarg, -, -⟩
  · rw [hd_iff] at hHD
    rcases hHD with h1 | h2 | h3
    · exact Or.inl h1
    · obtain ⟨h6, -⟩ := h2
      have h6' : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast h6
      rcases lt_trichotomy (3 * M.α) (M.d : ℝ) with hlt | heq | hgt
      · exact Or.inl hlt
      · exact Or.inr (Or.inl heq)
      · exact Or.inr (Or.inr ⟨by linarith, h6'⟩)
    · obtain ⟨hd6, hα2, -⟩ := h3
      have h6' : (M.d : ℝ) = 6 := by exact_mod_cast hd6
      exact Or.inr (Or.inl (by rw [h6', hα2]; norm_num))
  · exact Or.inr (Or.inl hmarg.symm)

/-- `(HD+)` never sits in the source's long-range low-dimensional regime
(`α < 2` together with `d < 3α`), where the asymptotic ODE is known to fail. -/
theorem hdplus_not_long_range_low_dim (M : SourceModelData) (h : HDplus M) :
    ¬ ((M.d : ℝ) < 3 * M.α ∧ M.α < 2) := by
  rintro ⟨h1, h2⟩
  rcases hdplus_param_regime M h with h3 | h3 | ⟨h4, -⟩
  · linarith
  · linarith
  · linarith

/-- At the critical dimension `d = 6` the alternatives force `α ≤ 2`, matching the
source's restriction that the `d_eff = d_c = 6` analysis requires `α ≤ 2` (p. 8). -/
theorem hdplus_alpha_le_two_of_dim_six (M : SourceModelData) (h : HDplus M)
    (hd : M.d = 6) : M.α ≤ 2 := by
  have hd' : (M.d : ℝ) = 6 := by exact_mod_cast hd
  rcases hdplus_param_regime M h with h3 | h3 | ⟨-, h6⟩
  · linarith
  · linarith
  · linarith

/-- `(HD+)` never sits in low dimension with a short-range tail (`d < 6`, `α ≥ 2`). -/
theorem hdplus_not_low_dim_short_range (M : SourceModelData) (h : HDplus M) :
    ¬ ((M.d : ℝ) < 6 ∧ 2 ≤ M.α) := by
  rintro ⟨h1, h2⟩
  rcases hdplus_param_regime M h with h3 | h3 | ⟨h4, h5⟩
  · linarith
  · linarith
  · linarith

/-- On the marginal line `d = 3α` inside the source's Levy-index range `α ≤ 2`, the only
`(HD)` alternative that can hold is the doubly-marginal one `d = 6`, `α = 2`: alternative
1 needs `3α < d`, alternative 2 needs `d > 6`, and alternative 3 is exactly
`d = 6`, `α = 2`. -/
theorem hd_forces_six_two_of_marginal_le_two (M : SourceModelData) (h : HD M)
    (hmarg : (M.d : ℝ) = 3 * M.α) (hα2 : M.α ≤ 2) : M.d = 6 ∧ M.α = 2 := by
  rw [hd_iff M] at h
  have hd6 : (M.d : ℝ) ≤ 6 := by linarith
  rcases h with h1 | ⟨h6, -⟩ | h3
  · linarith
  · have h6' : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast h6
    linarith
  · exact ⟨h3.1, h3.2.1⟩

/-- **Dichotomy on the marginal line.**  Under `α ≤ 2`, `(HD+)` on the line `d = 3α` is
exactly: the doubly-marginal point `d = 6`, `α = 2`, or the hydrodynamic condition.
So on that line the hypothesis class of the Case-3 chain has no third possibility. -/
theorem hdplus_marginal_dichotomy (M : SourceModelData) (h : HDplus M)
    (hmarg : (M.d : ℝ) = 3 * M.α) (hα2 : M.α ≤ 2) :
    (M.d = 6 ∧ M.α = 2) ∨ Hydro M := by
  rw [hdplus_iff M] at h
  rcases h with hHD | ⟨-, -, hHydro⟩
  · exact Or.inl (hd_forces_six_two_of_marginal_le_two M hHD hmarg hα2)
  · exact Or.inr hHydro

/-- **Coverage at the critical dimension.**  At `d = 6` the alternatives of `(HD+)` are
exactly `α < 2` (alternative 1, i.e. `3α < d`) or `α = 2` together with the source's
log-corrected two-point estimate (alternative 3).  Alternative 2 needs `d > 6` and
alternative 4 needs `d < 6`, so neither is available; in particular no `α > 2` point of
the critical dimension is reachable. -/
theorem hdplus_dim_six (M : SourceModelData) (hd : M.d = 6) :
    HDplus M ↔ 3 * M.α < (M.d : ℝ) ∨ (M.α = 2 ∧ TwoPointLogBound M) := by
  constructor
  · rintro (hHD | hfourth)
    · rw [hd_iff M] at hHD
      rcases hHD with h1 | h2 | h3
      · exact Or.inl h1
      · exact absurd h2.1 (not_six_lt_of_dim_six M hd)
      · exact Or.inr ⟨h3.2.1, h3.2.2⟩
    · exact absurd hfourth (not_fourth_of_dim_six M hd)
  · rintro (h1 | ⟨hα, hlog⟩)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inr ⟨hd, hα, hlog⟩))

/-- **Coverage in dimensions `≤ 5`.**  Both two-point alternatives of `(HD)` need
`d > 6` respectively `d = 6`, so below dimension `6` only alternative 1 of `(HD)` and the
marginal alternative 4 of `(HD+)` are available: the Case-3 two-point machinery cannot
fire there. -/
theorem hdplus_low_dim (M : SourceModelData) (h : HDplus M) (hd : M.d ≤ 5) :
    3 * M.α < (M.d : ℝ) ∨ ((M.d : ℝ) = 3 * M.α ∧ (M.d : ℝ) < 6 ∧ Hydro M) := by
  have hd5 : (M.d : ℝ) ≤ 5 := by exact_mod_cast hd
  rw [hdplus_iff M] at h
  rcases h with hHD | hfourth
  · rw [hd_iff M] at hHD
    rcases hHD with h1 | ⟨h6, -⟩ | h3
    · exact Or.inl h1
    · have h6' : (6 : ℝ) < (M.d : ℝ) := by exact_mod_cast h6
      linarith
    · have h6' : (M.d : ℝ) = 6 := by exact_mod_cast h3.1
      linarith
  · exact Or.inr hfourth

/-! ## The marginal regime: the exponents of `ζ` and `η` in Theorem I.1.17 -/

/-- A nonzero constant function is regularly varying of index `0`. -/
theorem regularlyVaryingAtTop_const {c : ℝ} (hc : c ≠ 0) :
    RegularlyVaryingAtTop (fun _ : ℝ => c) 0 := by
  constructor
  · filter_upwards with x using hc
  · intro l hl
    have h1 : (fun _ : ℝ => c / c) = fun _ : ℝ => (1 : ℝ) := by
      funext x
      exact div_self hc
    rw [h1, Real.rpow_zero]
    exact tendsto_const_nhds

/-- The quotient of regularly varying functions is regularly varying, with the difference
of the indices. -/
theorem regularlyVaryingAtTop_div {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RegularlyVaryingAtTop f a) (hg : RegularlyVaryingAtTop g b) :
    RegularlyVaryingAtTop (fun x => f x / g x) (a - b) := by
  have h := hf.mul hg.inv
  simpa [div_eq_mul_inv, sub_eq_add_neg] using h

/-- **Theorem I.1.17's regular-variation clause is a consequence, not an input.**

The source (p. 17) states that with `η(r) = 4 (E_{β_c,r}|K|)^2 / E_{β_c,r}|K|^2` and
`ζ(r) = (1/4) E_{β_c,r}|K|^2 / E_{β_c,r}|K|`, the functions `ζ` and `η` are regularly
varying of index `2α` and `−α`.  Both exponents are the difference of the two indices
supplied by Propositions I.4.2 and I.4.15, `α` for `E_{β_c,r}|K|` and `3α` for
`E_{β_c,r}|K|^2`; no dimension identity (`d = 3α` included) enters, and nothing about
the hydrodynamic condition is used.  Here `cutMoment 1` is `E_{β_c,r}|K|` and
`cutMoment 2` is `E_{β_c,r}|K|^2`. -/
theorem zeta_eta_regularlyVarying (M : SourceModelData)
    (hRV1 : RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 1 r).toReal) M.α)
    (hRV2 : RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α)) :
    RegularlyVaryingAtTop
        (fun r : ℝ => (1 / 4) * ((M.cutMoment 2 r).toReal / (M.cutMoment 1 r).toReal))
        (2 * M.α) ∧
      RegularlyVaryingAtTop
        (fun r : ℝ => 4 * ((M.cutMoment 1 r).toReal ^ 2 / (M.cutMoment 2 r).toReal))
        (-M.α) := by
  have hconstFour : RegularlyVaryingAtTop (fun _ : ℝ => (1 / 4 : ℝ)) 0 :=
    regularlyVaryingAtTop_const (by norm_num)
  have hconstTimesFour : RegularlyVaryingAtTop (fun _ : ℝ => (4 : ℝ)) 0 :=
    regularlyVaryingAtTop_const (by norm_num)
  constructor
  · have hquot : RegularlyVaryingAtTop
        (fun r : ℝ => (M.cutMoment 2 r).toReal / (M.cutMoment 1 r).toReal)
        (3 * M.α - M.α) := regularlyVaryingAtTop_div hRV2 hRV1
    have h := hconstFour.mul hquot
    have hidx : (0 : ℝ) + (3 * M.α - M.α) = 2 * M.α := by ring
    rw [hidx] at h
    exact h
  · have hsq : RegularlyVaryingAtTop
        (fun r : ℝ => (M.cutMoment 1 r).toReal * (M.cutMoment 1 r).toReal)
        (M.α + M.α) := hRV1.mul hRV1
    have hquot := regularlyVaryingAtTop_div hsq hRV2
    have h := hconstTimesFour.mul hquot
    have hidx : (0 : ℝ) + (M.α + M.α - 3 * M.α) = -M.α := by ring
    rw [hidx] at h
    simpa [pow_two] using h

/-! ## Non-vacuity: real models on each parameter locus -/

/-- **`(HD)` is satisfiable in every ambient dimension**, through alternative 1 with
`α = 1/8` (`3α = 3/8 < 1 ≤ d`).  The witness is the source-normalized model of
`ModelWitness.Defs` (unit-volume norm ball, `K r = r^{-d-α}/(d+α)`, zero log error), so
the hypothesis class of the Case-3 chain is non-empty. -/
theorem exists_hd (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : SourceModelData, M.d = d ∧ M.α = 1 / 8 ∧ HD M := by
  refine ⟨Witness.sourceModelWitness d hd (1 / 8) (by norm_num), rfl, rfl, ?_⟩
  refine Or.inl ?_
  change (3 : ℝ) * (1 / 8) < ((d : ℕ) : ℝ)
  have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

/-- `(HD+)` is satisfiable in every ambient dimension. -/
theorem exists_hdplus (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : SourceModelData, M.d = d ∧ HDplus M := by
  obtain ⟨M, hd', -, hHD⟩ := exists_hd d hd
  exact ⟨M, hd', hd_imp_hdplus M hHD⟩

/-- The short-range tail value `α = 2` is realized in every dimension, in particular at
the doubly-marginal point `(d, α) = (6, 2)` of `hdplus_iff_twoPointLog_of_dim_six`. -/
theorem exists_alpha_two (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : SourceModelData, M.d = d ∧ M.α = 2 :=
  ⟨Witness.sourceModelWitness d hd 2 (by norm_num), rfl, rfl⟩

/-- The doubly-marginal parameter point `(d, α) = (6, 2)` is realized by a model, so
`hdplus_iff_twoPointLog_of_dim_six` is not a statement about an empty locus. -/
theorem exists_six_two :
    ∃ M : SourceModelData, M.d = 6 ∧ M.α = 2 :=
  exists_alpha_two 6 (by norm_num)

/-- The marginal curve `d = 3α < 6` is realized (here `d = 3`, `α = 1`), and there
`(HD+)` is exactly `(Hydro)`. -/
theorem exists_at_marginal_curve :
    ∃ M : SourceModelData, (M.d : ℝ) = 3 * M.α ∧ (M.d : ℝ) < 6 := by
  refine ⟨Witness.sourceModelWitness 3 (by norm_num) 1 (by norm_num), ?_, ?_⟩
  · change ((3 : ℕ) : ℝ) = 3 * (1 : ℝ)
    norm_num
  · change ((3 : ℕ) : ℝ) < (6 : ℝ)
    norm_num

/-- A realized model on the marginal curve where `(HD+) ↔ (Hydro)`: the residual input of
the fourth alternative is exactly the hydrodynamic condition. -/
theorem exists_marginal_hdplus_iff_hydro :
    ∃ M : SourceModelData,
      (M.d : ℝ) = 3 * M.α ∧ (M.d : ℝ) < 6 ∧ (HDplus M ↔ Hydro M) := by
  obtain ⟨M, h1, h2⟩ := exists_at_marginal_curve
  exact ⟨M, h1, h2, hdplus_iff_hydro_of_marginal_lt_six M h1 h2⟩

/-- Alternatives 1 and 2 of `(HD)` are not disjoint as parameter conditions: at
`d = 7`, `α = 1` both `3α < d` and `6 < d` hold, and alternative 1 is actually
satisfied by the witness model.  Any case analysis splitting on `(HD)` that enumerates
the alternatives must therefore tolerate the overlap. -/
theorem exists_overlap_case_one_two :
    ∃ M : SourceModelData,
      M.d = 7 ∧ M.α = 1 ∧ 3 * M.α < (M.d : ℝ) ∧ 6 < (M.d : ℝ) ∧ HD M := by
  refine ⟨Witness.sourceModelWitness 7 (by norm_num) 1 (by norm_num), rfl, rfl, ?_, ?_, ?_⟩
  · change (3 : ℝ) * (1 : ℝ) < ((7 : ℕ) : ℝ)
    norm_num
  · change (6 : ℝ) < ((7 : ℕ) : ℝ)
    norm_num
  · exact Or.inl (by change (3 : ℝ) * (1 : ℝ) < ((7 : ℕ) : ℝ); norm_num)

end HDRegime

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit (only `propext`, `Classical.choice`, `Quot.sound` are permitted) -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hd_iff
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.toVec_sub_ne_zero
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.twoPoint_zero_of_ne
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.twoPointLogBound_of_betaCrit_eq_zero
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.not_twoPointLogBound_of_dist_lt_one
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_iff
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hd_imp_hdplus
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.two_alpha_lt_half_iff
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.half_eq_two_alpha_of_marginal
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hydro_iff_marginal_exponent
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.marginal_log_bound_not_o
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hd_iff_of_marginal
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.not_hd_of_marginal_lt_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_iff_hydro_of_marginal_lt_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.alpha_lt_two_of_marginal_lt_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.not_hd_of_fourth
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.not_three_alpha_lt_of_dim_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.not_six_lt_of_dim_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.not_fourth_of_dim_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hd_forces_six_two_of_marginal_le_two
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_marginal_dichotomy
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_dim_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_low_dim
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_iff_twoPointLog_of_dim_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_param_regime
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_not_long_range_low_dim
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_alpha_le_two_of_dim_six
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.hdplus_not_low_dim_short_range
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.regularlyVaryingAtTop_const
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.regularlyVaryingAtTop_div
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.zeta_eta_regularlyVarying
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.exists_hd
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.exists_hdplus
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.exists_alpha_two
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.exists_six_two
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.exists_at_marginal_curve
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.exists_marginal_hdplus_iff_hydro
#print axioms PercLib.CriticalLRP.Orchestration.HDRegime.exists_overlap_case_one_two
