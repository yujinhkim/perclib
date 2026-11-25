/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**Tail endpoints and ratio limits for Theorem I.2.11** (Hutchcroft, *Critical
long-range percolation I*, arXiv:2508.18807v1, p. 26).

Theorem I.2.11 is stated in the paper for the tail event `P(X ≥ x)`, i.e. for
`μ (Set.Ici x)`.  The exact Laplace–tail identity and the Abelian half of the
theorem in `Analysis/TauberianLaplace.lean` are stated for the *strict* tail
`μ (Set.Ioi x)`.  This file closes that gap, supplies the ratio limits of a
regularly varying `f`, and shows how the paper's `≥` statement assembles from
the strict-tail Tauberian implication.

**Scope.**  The complete "if and only if" of Theorem I.2.11 is *not* claimed
here: its remaining open ingredient is the strict-tail Tauberian converse
(Laplace asymptotics imply tail asymptotics), which is stated as an explicit
hypothesis wherever it is used (`laplace_asymptotic_iff_tail_ge_of_strict_converse`,
`tail_ge_asymptotic_of_antitone_converse`) and never as an axiom.  Everything
else below is unconditional and sorry-free, with standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`).

Contents:

* `tendsto_rpow_nhdsLT_one`: `c ↦ c ^ β` tends to `1` as `c ↑ 1` (from the
  left), for every real `β`.  This is what sharpens a one-sided comparison at
  `c < 1` to the sharp constant as `c → 1`.
* `exists_lt_rpow_of_lt_one`, `exists_rpow_neg_lt_of_one_lt`: the two forms in
  which that limit is used (`a < c ^ α` for `a < 1`, `c ^ (-α) < b` for `1 < b`).
* `tendsto_rv_ratio_mul`, `tendsto_rv_ratio_div`: for `f` regularly varying of
  index `-α` and `c > 0`,
  `f (c * x) / f x → c ^ (-α)` and `f (x / c) / f x → c ^ α`.
* `toReal_le_toReal_of_subset`: monotonicity of `s ↦ (μ s).toReal` for a
  probability measure.
* `eventually_pos_of_ratio_tendsto_one`: the ratio hypothesis itself forces
  `f x > 0` eventually; positivity of `f` is never assumed.
* `tendsto_tail_gt_of_tail_ge`: **`P(X ≥ x)` asymptotics imply `P(X > x)`
  asymptotics**, using `Set.Ici x ⊆ Set.Ioi (x / c)` for `0 < c < 1`, `x > 0`,
  and `f (x/c) / f x → c ^ α`, then `c ↑ 1`.  No atom or continuity assumption
  on `μ`: an atom at `x` only makes `μ (Ici x)` larger, and the two-sided
  comparison is closed by monotonicity, not by a null-set claim.
* `tendsto_tail_ge_of_tail_gt`: the converse implication, **`P(X > x)`
  asymptotics imply `P(X ≥ x)` asymptotics**, using `Set.Ici x ⊆ Set.Ioi (c * x)`
  and `f (c x) / f x → c ^ (-α)`, then `c ↑ 1`.
* `tendsto_tail_ge_iff_tail_gt`: the two tail formulations are equivalent, so
  the strict-tail choice of `Analysis/TauberianLaplace.lean` loses nothing.
* `integral_comp_laplace_rescale`, `tendsto_kernel_form_iff`: the substitution
  `h ∫_0^∞ e^{-hx} F x dx = ∫_0^∞ e^{-u} F (u/h) du` and the equivalence of the
  two forms of the Laplace hypothesis.
* `one_sub_exp_eq_setIntegral_indicator_Iic`,
  `integral_one_sub_exp_eq_laplace_tail_ge`: **the Laplace–tail identity with the
  non-strict tail**, `E_μ[1 - e^{-hX}] = h ∫_0^∞ e^{-hx} μ([x,∞)) dx`, exact for
  every probability measure `μ` carried by `[0,∞)` (no atom assumption).
* `laplace_tail_asymptotic_of_tail_ge`: **the Abelian half of Theorem I.2.11 in
  the paper's `≥` form**, with the exact constant `Γ(1-α)`, obtained by
  composing `tendsto_tail_gt_of_tail_ge` with
  `laplace_tail_asymptotic_of_tail`.
* `laplace_tail_asymptotic_of_tail_ge'`: the same statement, proved
  independently from the non-strict Laplace–tail identity, without the endpoint
  bridge (two proofs of one statement: a consistency check).
* `laplace_asymptotic_iff_tail_ge_of_strict_converse`: the assembly statement.
  If the strict-tail Tauberian implication holds for this `μ` (explicit
  hypothesis `hconv`, not an axiom), then Laplace asymptotics are equivalent to
  the paper's `μ (Set.Ici ·)` tail asymptotics.
* `tail_ge_asymptotic_of_antitone_converse`: the same assembly when the
  converse is available in the paper's antitone-function form (an explicit
  hypothesis `hconv` on bounded measurable antitone `F`); this is the form in
  which the remaining Tauberian converse is naturally stated;
  `tail_ge_asymptotic_of_antitone_kernel_converse` is the same with `hconv`
  stated in the kernel form `(∫ e^{-u} F (u/h))/f(1/h) → 1`.
* `tendsto_tail_ge_iff_tail_gt_rpow`, `laplace_tail_asymptotic_of_tail_ge_rpow`:
  the specialisations to the explicit power law `f x = x ^ (-α)`, recording that
  the regular-variation hypothesis is instantiable with the paper's constant
  placement.
-/
module

public import PercLib.CriticalLRP.Analysis.TauberianLaplace

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis

/-! ### The endpoint limit `c ↑ 1` of `c ↦ c ^ β` -/

/-- For every real `β`, `c ↦ c ^ β` tends to `1` as `c` tends to `1` from below. -/
theorem tendsto_rpow_nhdsLT_one (β : ℝ) :
    Tendsto (fun c : ℝ => c ^ β) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  have h : Tendsto (fun c : ℝ => c ^ β) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) ^ β)) :=
    (Real.continuousAt_rpow_const 1 β (Or.inl one_ne_zero)).tendsto
  rw [Real.one_rpow] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- For `a < 1` and `0 ≤ α` there is `c ∈ (0,1)` with `a < c ^ α`.  (One takes
`c` close to `1` when `a > 0`, and any `c` when `a ≤ 0`.) -/
theorem exists_lt_rpow_of_lt_one {a α : ℝ} (ha1 : a < 1) (_hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ a < c ^ α := by
  rcases lt_or_ge 0 a with ha0 | ha0
  · have hlim : Tendsto (fun c : ℝ => c ^ α) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_rpow_nhdsLT_one α
    have h1 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), a < c ^ α :=
      hlim.eventually (eventually_gt_nhds ha1)
    have h2 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), 0 < c :=
      (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    have h3 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), c < 1 := self_mem_nhdsWithin
    obtain ⟨c, hc1, hc2, hc3⟩ := (h1.and (h2.and h3)).exists
    exact ⟨c, hc2, hc3, hc1⟩
  · refine ⟨1 / 2, by norm_num, by norm_num, lt_of_le_of_lt ha0 ?_⟩
    exact Real.rpow_pos_of_pos (by norm_num) α

/-- For `1 < b` and any real `α` there is `c ∈ (0,1)` with `c ^ (-α) < b`.  (One
takes `c` close to `1`.) -/
theorem exists_rpow_neg_lt_of_one_lt {b α : ℝ} (hb : 1 < b) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ c ^ (-α) < b := by
  have hlim : Tendsto (fun c : ℝ => c ^ (-α)) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    tendsto_rpow_nhdsLT_one (-α)
  have h1 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), c ^ (-α) < b :=
    hlim.eventually (eventually_lt_nhds hb)
  have h2 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), 0 < c :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), c < 1 := self_mem_nhdsWithin
  obtain ⟨c, hc1, hc2, hc3⟩ := (h1.and (h2.and h3)).exists
  exact ⟨c, hc2, hc3, hc1⟩

/-! ### Ratio limits of a regularly varying function -/

/-- **Ratio limit at a fixed factor.**  If `f` is regularly varying at `∞` of
index `-α` and `c > 0`, then `f (c x) / f x → c ^ (-α)`. -/
theorem tendsto_rv_ratio_mul {f : ℝ → ℝ} {α c : ℝ} (hc : 0 < c)
    (hrv : RegularlyVaryingAtTop f (-α)) :
    Tendsto (fun x : ℝ => f (c * x) / f x) atTop (𝓝 (c ^ (-α))) :=
  hrv.2 c hc

/-- **Ratio limit at a fixed factor, quotient form.**  If `f` is regularly
varying at `∞` of index `-α` and `c > 0`, then `f (x / c) / f x → c ^ α`.  This
is the form used for the comparison `Ici x ⊆ Ioi (x / c)`. -/
theorem tendsto_rv_ratio_div {f : ℝ → ℝ} {α c : ℝ} (hc : 0 < c)
    (hrv : RegularlyVaryingAtTop f (-α)) :
    Tendsto (fun x : ℝ => f (x / c) / f x) atTop (𝓝 (c ^ α)) := by
  have h := hrv.2 c⁻¹ (inv_pos.2 hc)
  have hfun : (fun x : ℝ => f (c⁻¹ * x) / f x) = fun x : ℝ => f (x / c) / f x := by
    ext x; rw [inv_mul_eq_div]
  rw [hfun] at h
  have hpow : (c⁻¹) ^ (-α) = c ^ α := by
    rw [← Real.rpow_neg_one c, ← Real.rpow_mul hc.le,
      show (-1 : ℝ) * (-α) = α from by ring]
  rwa [hpow] at h

/-! ### Monotonicity of `toReal` and the forcing of eventual positivity -/

/-- For a probability measure, `s ↦ (μ s).toReal` is monotone in `s`. -/
theorem toReal_le_toReal_of_subset (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s t : Set ℝ} (hst : s ⊆ t) : (μ s).toReal ≤ (μ t).toReal := by
  have ht : μ t ≠ ∞ := by
    have h2 : μ t ≤ 1 := by
      have h3 : μ t ≤ μ Set.univ := measure_mono (Set.subset_univ t)
      rwa [IsProbabilityMeasure.measure_univ] at h3
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h2
  exact ENNReal.toReal_mono ht (measure_mono hst : μ s ≤ μ t)

/-- **The ratio hypothesis forces `f` to be eventually positive.**  If
`g x / (f x / Γ(1-α)) → 1` with `g ≥ 0` and `Γ(1-α) > 0`, then `f x > 0`
eventually.  In particular no positivity of `f` is an extra hypothesis of the
endpoint bridges. -/
theorem eventually_pos_of_ratio_tendsto_one {f g : ℝ → ℝ} {α : ℝ}
    (hα1 : α < 1) (hg : ∀ x, 0 ≤ g x)
    (h : Tendsto (fun x => g x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1)) :
    ∀ᶠ x : ℝ in atTop, 0 < f x := by
  have hα1' : (0 : ℝ) < 1 - α := by linarith
  have hΓpos : (0 : ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos hα1'
  have h1 : ∀ᶠ x : ℝ in atTop, (0 : ℝ) < g x / (f x / Real.Gamma (1 - α)) :=
    h.eventually (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [h1] with x hx
  by_contra hle
  push Not at hle
  have h2 : f x / Real.Gamma (1 - α) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hle hΓpos.le
  have h3 : g x / (f x / Real.Gamma (1 - α)) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (hg x) h2
  linarith

/-! ### Endpoint bridge: `≥` tail asymptotics imply `>` tail asymptotics -/

/-- **The non-strict tail asymptotic implies the strict one.**
For a probability measure `μ` and `f` regularly varying of index `-α`,
`0 ≤ α < 1`, if `μ (Set.Ici x) ~ f x / Γ(1-α)` then
`μ (Set.Ioi x) ~ f x / Γ(1-α)`.

The comparison is `Set.Ici x ⊆ Set.Ioi (x / c)` for `0 < c < 1`, `x > 0`, which
gives `μ (Ioi x) ≥ μ (Ici (x/c))`; after rescaling by `f x` the two sides differ
by `f (x/c) / f x → c ^ α`, and `c ↑ 1`.  No atom or continuity hypothesis on
`μ` is used. -/
theorem tendsto_tail_gt_of_tail_ge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrv : RegularlyVaryingAtTop f (-α))
    (htail : Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun x => (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1) := by
  classical
  have hα1' : (0 : ℝ) < 1 - α := by linarith
  have hΓpos : (0 : ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos hα1'
  have hfpos : ∀ᶠ x : ℝ in atTop, 0 < f x :=
    eventually_pos_of_ratio_tendsto_one hα1 (fun x => ENNReal.toReal_nonneg) htail
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bound: compare with `μ (Ici (x / c))` and let `c ↑ 1`
    intro a ha
    obtain ⟨c, hc0, hc1, hca⟩ := exists_lt_rpow_of_lt_one ha hα0
    have hxc : Tendsto (fun x : ℝ => x / c) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ => c⁻¹ * x) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos (inv_pos.2 hc0)).2 tendsto_id
      simpa [div_eq_inv_mul] using h1
    have hfc : ∀ᶠ x : ℝ in atTop, 0 < f (x / c) := hxc.eventually hfpos
    have hprod : Tendsto (fun x : ℝ => (μ (Set.Ici (x / c))).toReal
        / (f (x / c) / Real.Gamma (1 - α)) * (f (x / c) / f x)) atTop (𝓝 (c ^ α)) := by
      have h1 : Tendsto (fun x : ℝ => (μ (Set.Ici (x / c))).toReal
          / (f (x / c) / Real.Gamma (1 - α))) atTop (𝓝 1) := htail.comp hxc
      have h2 : Tendsto (fun x : ℝ => f (x / c) / f x) atTop (𝓝 (c ^ α)) :=
        tendsto_rv_ratio_div hc0 hrv
      have h3 := h1.mul h2
      rwa [one_mul] at h3
    have hlow : ∀ᶠ x : ℝ in atTop,
        (μ (Set.Ici (x / c))).toReal / (f (x / c) / Real.Gamma (1 - α)) * (f (x / c) / f x)
          ≤ (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α)) := by
      filter_upwards [hfpos, hfc, eventually_gt_atTop (0 : ℝ)] with x hfx hfcx hxpos
      have hsub : Set.Ici (x / c) ⊆ Set.Ioi x := by
        rw [Set.Ici_subset_Ioi]
        rw [lt_div_iff₀ hc0]
        nlinarith
      have hBA : (μ (Set.Ici (x / c))).toReal ≤ (μ (Set.Ioi x)).toReal :=
        toReal_le_toReal_of_subset μ hsub
      have hfcx' : f (x / c) ≠ 0 := ne_of_gt hfcx
      have hfx' : f x ≠ 0 := ne_of_gt hfx
      calc (μ (Set.Ici (x / c))).toReal / (f (x / c) / Real.Gamma (1 - α))
            * (f (x / c) / f x)
          = (μ (Set.Ici (x / c))).toReal * Real.Gamma (1 - α) / f x := by
            field_simp
        _ ≤ (μ (Set.Ioi x)).toReal * Real.Gamma (1 - α) / f x :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBA hΓpos.le) hfx.le
        _ = (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α)) := by
            field_simp
    filter_upwards [hprod.eventually (eventually_gt_nhds hca), hlow] with x h1 h2
    linarith
  · -- upper bound: `μ (Ioi x) ≤ μ (Ici x)`, and the latter ratio tends to `1`
    intro b hb
    have hle : ∀ᶠ x : ℝ in atTop,
        (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α))
          ≤ (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)) := by
      filter_upwards [hfpos] with x hx
      have htr : (μ (Set.Ioi x)).toReal ≤ (μ (Set.Ici x)).toReal :=
        toReal_le_toReal_of_subset μ Set.Ioi_subset_Ici_self
      exact div_le_div_of_nonneg_right htr (le_of_lt (div_pos hx hΓpos))
    filter_upwards [hle, htail.eventually (eventually_lt_nhds hb)] with x h1 h2
    linarith

/-! ### Endpoint bridge: `>` tail asymptotics imply `≥` tail asymptotics -/

/-- **The strict tail asymptotic implies the non-strict one.**
For a probability measure `μ` and `f` regularly varying of index `-α`,
`0 ≤ α < 1`, if `μ (Set.Ioi x) ~ f x / Γ(1-α)` then
`μ (Set.Ici x) ~ f x / Γ(1-α)`.

The comparison is `Set.Ici x ⊆ Set.Ioi (c x)` for `0 < c < 1`, `x > 0`, which
gives `μ (Ici x) ≤ μ (Ioi (c x))`; after rescaling by `f x` the right side is the
strict-tail ratio at `c x` times `f (c x) / f x → c ^ (-α)`, and `c ↑ 1`. -/
theorem tendsto_tail_ge_of_tail_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {α : ℝ} (_hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrv : RegularlyVaryingAtTop f (-α))
    (htail : Tendsto (fun x => (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1) := by
  classical
  have hα1' : (0 : ℝ) < 1 - α := by linarith
  have hΓpos : (0 : ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos hα1'
  have hfpos : ∀ᶠ x : ℝ in atTop, 0 < f x :=
    eventually_pos_of_ratio_tendsto_one hα1 (fun x => ENNReal.toReal_nonneg) htail
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bound: `μ (Ioi x) ≤ μ (Ici x)`, and the former ratio tends to `1`
    intro a ha
    have hle : ∀ᶠ x : ℝ in atTop,
        (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α))
          ≤ (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)) := by
      filter_upwards [hfpos] with x hx
      have htr : (μ (Set.Ioi x)).toReal ≤ (μ (Set.Ici x)).toReal :=
        toReal_le_toReal_of_subset μ Set.Ioi_subset_Ici_self
      exact div_le_div_of_nonneg_right htr (le_of_lt (div_pos hx hΓpos))
    filter_upwards [hle, htail.eventually (eventually_gt_nhds ha)] with x h1 h2
    linarith
  · -- upper bound: compare with `μ (Ioi (c x))` and let `c ↑ 1`
    intro b hb
    obtain ⟨c, hc0, hc1, hcb⟩ := exists_rpow_neg_lt_of_one_lt (α := α) hb
    have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hc0).2 tendsto_id
    have hfc : ∀ᶠ x : ℝ in atTop, 0 < f (c * x) := hcx.eventually hfpos
    have hprod : Tendsto (fun x : ℝ => (μ (Set.Ioi (c * x))).toReal
        / (f (c * x) / Real.Gamma (1 - α)) * (f (c * x) / f x)) atTop (𝓝 (c ^ (-α))) := by
      have h1 : Tendsto (fun x : ℝ => (μ (Set.Ioi (c * x))).toReal
          / (f (c * x) / Real.Gamma (1 - α))) atTop (𝓝 1) := htail.comp hcx
      have h2 : Tendsto (fun x : ℝ => f (c * x) / f x) atTop (𝓝 (c ^ (-α))) :=
        tendsto_rv_ratio_mul hc0 hrv
      have h3 := h1.mul h2
      rwa [one_mul] at h3
    have hup : ∀ᶠ x : ℝ in atTop,
        (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α))
          ≤ (μ (Set.Ioi (c * x))).toReal / (f (c * x) / Real.Gamma (1 - α))
              * (f (c * x) / f x) := by
      filter_upwards [hfpos, hfc, eventually_gt_atTop (0 : ℝ)] with x hfx hfcx hxpos
      have hsub : Set.Ici x ⊆ Set.Ioi (c * x) := by
        rw [Set.Ici_subset_Ioi]
        nlinarith
      have hBA : (μ (Set.Ici x)).toReal ≤ (μ (Set.Ioi (c * x))).toReal :=
        toReal_le_toReal_of_subset μ hsub
      have hfcx' : f (c * x) ≠ 0 := ne_of_gt hfcx
      have hfx' : f x ≠ 0 := ne_of_gt hfx
      calc (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α))
          = (μ (Set.Ici x)).toReal * Real.Gamma (1 - α) / f x := by
            field_simp
        _ ≤ (μ (Set.Ioi (c * x))).toReal * Real.Gamma (1 - α) / f x :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBA hΓpos.le) hfx.le
        _ = (μ (Set.Ioi (c * x))).toReal / (f (c * x) / Real.Gamma (1 - α))
              * (f (c * x) / f x) := by
            field_simp
    filter_upwards [hprod.eventually (eventually_lt_nhds hcb), hup] with x h1 h2
    linarith

/-! ### The Laplace–tail identity with the non-strict tail `μ (Set.Ici x)` -/

/-- `1 - e^{-h s} = ∫_0^∞ 1{x ≤ s} · h e^{-h x} dx` for `s ≥ 0`. -/
theorem one_sub_exp_eq_setIntegral_indicator_Iic {h s : ℝ} (hs : 0 ≤ s) :
    ∫ x in Set.Ioi (0 : ℝ), (Set.Iic s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x
      = 1 - Real.exp (-(h * s)) := by
  rw [← neg_mul]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt (fun x : ℝ => -Real.exp (-h * x)) (h * Real.exp (-h * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -h * x) (-h) x := by
      simpa using (hasDerivAt_id x).const_mul (-h)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-h * x)) (Real.exp (-h * x) * (-h)) x := h1.exp
    have h3 : HasDerivAt (fun x : ℝ => -Real.exp (-h * x)) (-(Real.exp (-h * x) * (-h))) x :=
      h2.neg
    convert h3 using 1
    ring
  have hint : IntervalIntegrable (fun x : ℝ => h * Real.exp (-h * x)) volume 0 s :=
    ((continuous_const.mul (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => -h * x)))).intervalIntegrable _ _
  have hclosed := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hmain : ∫ x in (0 : ℝ)..s, h * Real.exp (-h * x) = 1 - Real.exp (-h * s) := by
    rw [hclosed]
    have h0 : Real.exp (-h * 0) = 1 := by simp
    rw [h0]; ring
  rw [← hmain, intervalIntegral.integral_of_le hs,
    show Set.Ioc (0 : ℝ) s = Set.Ioi 0 ∩ Set.Iic s from rfl,
    ← MeasureTheory.setIntegral_indicator measurableSet_Iic]
  simp only [neg_mul]

/-- **The Laplace–tail identity, non-strict form.**  For a probability measure
`μ` on `ℝ` carried by `[0,∞)` and `h > 0`,

  `E_μ[1 - e^{-h X}] = h ∫_0^∞ e^{-h x} μ([x,∞)) dx`,

with `μ([x,∞)) = μ (Set.Ici x)`, the tail event printed in Theorem I.2.11.
The proof is the same Fubini argument as for the strict form in
`Analysis/TauberianLaplace.lean`; the only change is that the inner integral
`∫_s 1{x ≤ s} dμ(s) = μ (Set.Ici x)` instead of `μ (Set.Ioi x)`.  No atom or
continuity hypothesis on `μ` is needed: the identity is exact, not asymptotic. -/
theorem integral_one_sub_exp_eq_laplace_tail_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) {h : ℝ} (hh : 0 < h) :
    ∫ s, (1 - Real.exp (-(h * s))) ∂μ
      = h * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(h * x)) * (μ (Set.Ici x)).toReal := by
  classical
  have hae : ∀ᵐ s ∂μ, 0 ≤ s := by
    rw [MeasureTheory.ae_iff]
    convert hμ using 2
    ext x
    simp
  have hstep1 : ∫ s, (1 - Real.exp (-(h * s))) ∂μ
      = ∫ s, ∫ x in Set.Ioi (0 : ℝ),
          (Set.Iic s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x ∂volume ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with s hs
    exact (one_sub_exp_eq_setIntegral_indicator_Iic hs).symm
  have hmaj : Integrable (fun z : ℝ × ℝ => h * Real.exp (-(h * z.2)))
      (μ.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const _
    have h2 : Integrable (fun x : ℝ => h * Real.exp (-h * x)) (volume.restrict (Set.Ioi 0)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -h < 0) 0).const_mul h
    have h3 := h1.mul_prod h2
    have h4 : (fun z : ℝ × ℝ => (1:ℝ) * (h * Real.exp (-h * z.2)))
        = fun z : ℝ × ℝ => h * Real.exp (-(h * z.2)) := by
      ext z; rw [one_mul, neg_mul]
    rw [h4] at h3
    exact h3
  have hmeas : Measurable fun p : ℝ × ℝ =>
      (Set.Iic p.1).indicator (fun x : ℝ => h * Real.exp (-(h * x))) p.2 := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      measurableSet_le measurable_snd measurable_fst
    have hfun : Measurable fun p : ℝ × ℝ => h * Real.exp (-(h * p.2)) :=
      measurable_const.mul (Real.measurable_exp.comp ((measurable_const.mul measurable_snd).neg))
    exact hfun.indicator hset
  have hjoint : Integrable (Function.uncurry fun s x : ℝ =>
      (Set.Iic s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x)
      (μ.prod (volume.restrict (Ioi 0))) := by
    refine hmaj.mono hmeas.aestronglyMeasurable ?_
    filter_upwards with p
    obtain ⟨s, x⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [Set.indicator_apply]
    split_ifs with hxs
    · simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hh, Real.abs_exp]
      exact le_rfl
    · simp only [norm_zero]
      positivity
  rw [hstep1, integral_integral_swap hjoint]
  have hinner : ∀ x : ℝ, ∫ s, (Set.Iic s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x ∂μ
      = h * Real.exp (-(h * x)) * (μ (Set.Ici x)).toReal := by
    intro x
    have hfun : ∀ s : ℝ, (Set.Iic s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x
        = h * Real.exp (-(h * x)) * (Set.Ici x).indicator (fun _ => (1:ℝ)) s := by
      intro s
      simp only [Set.indicator_apply, Set.mem_Iic, Set.mem_Ici]
      split_ifs with h1 <;> ring
    have h1 : ∀ x : ℝ, ∫ s, h * Real.exp (-(h * x)) * (Set.Ici x).indicator (fun _ => (1:ℝ)) s ∂μ
        = h * Real.exp (-(h * x)) * (μ (Set.Ici x)).toReal := by
      intro x
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator_const (1:ℝ) measurableSet_Ici, Measure.real]
      simp
    simp only [hfun, h1]
  simp only [hinner]
  rw [← integral_const_mul]
  ring_nf

/-! ### The Abelian half of Theorem I.2.11 with the source's `≥` event -/

/-- **Theorem I.2.11, Abelian direction, for the tail event `P(X ≥ x)`.**
Let `μ` be a probability measure on `ℝ` carried by `[0,∞)` and let `f` be
regularly varying of index `-α`, `0 ≤ α < 1`.  If `μ (Set.Ici x) ~ f x / Γ(1-α)`
then `E_μ[1 - e^(-hX)] ~ f (1/h)` as `h ↓ 0`.

This is the form printed in the paper: the premise is the *non-strict* tail
`P(X ≥ x) = μ (Set.Ici x)`.  It is obtained from
`laplace_tail_asymptotic_of_tail` (whose premise is `μ (Set.Ioi ·)`) by the
endpoint bridge `tendsto_tail_gt_of_tail_ge`. -/
theorem laplace_tail_asymptotic_of_tail_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (htail : Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1/h))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  laplace_tail_asymptotic_of_tail μ hμ hα0 hα1 hfmeas hrv
    (tendsto_tail_gt_of_tail_ge μ hα0 hα1 hrv htail)

/-- **The Abelian direction in the paper's `≥` form, independent second proof.**
Identical statement to `laplace_tail_asymptotic_of_tail_ge`, but proved directly
from the non-strict Laplace–tail identity
`integral_one_sub_exp_eq_laplace_tail_ge`, *without* the endpoint bridge: apply
`tendsto_laplace_of_tail_asymptotic` to the antitone function
`x ↦ (μ (Set.Ici x)).toReal` and rewrite the Laplace integral with the identity.

Having two proofs is a check that the identity and the endpoint bridge agree;
the bridge proof is the one that generalises to arbitrary tail pairs, while this
one shows that the paper's `≥` formulation is available directly. -/
theorem laplace_tail_asymptotic_of_tail_ge'
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (htail : Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hanti : Antitone fun x : ℝ => (μ (Set.Ici x)).toReal := by
    intro a b hab
    exact toReal_le_toReal_of_subset μ (fun y hy => le_trans hab hy)
  have hF0 : ∀ x : ℝ, 0 ≤ (μ (Set.Ici x)).toReal := fun x => ENNReal.toReal_nonneg
  have hF1 : ∀ x : ℝ, (μ (Set.Ici x)).toReal ≤ 1 := by
    intro x
    have h2 : μ (Set.Ici x) ≤ 1 := by
      have h3 : μ (Set.Ici x) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rwa [IsProbabilityMeasure.measure_univ] at h3
    calc (μ (Set.Ici x)).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top h2
      _ = 1 := by simp
  have hm := tendsto_laplace_of_tail_asymptotic (F := fun x : ℝ => (μ (Set.Ici x)).toReal)
    hα0 hα1 hanti.measurable hF0 hF1 hfmeas hrv htail
  refine hm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [integral_one_sub_exp_eq_laplace_tail_ge μ hμ hh]

/-- **Assembly of both halves of Theorem I.2.11 in the paper's `≥` form.**
The strict-tail Tauberian implication is kept as an explicit hypothesis `hconv`
(it is not an axiom and not assumed silently): if Laplace asymptotics force
`μ (Set.Ioi ·) ~ f / Γ(1-α)`, then, combined with the endpoint bridge
`tendsto_tail_ge_of_tail_gt`, Laplace asymptotics are equivalent to the paper's
`μ (Set.Ici ·)` tail asymptotics.  The forward direction is unconditional
(`laplace_tail_asymptotic_of_tail_ge`); only the converse uses `hconv`. -/
theorem laplace_asymptotic_iff_tail_ge_of_strict_converse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (hconv : Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1/h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) →
      Tendsto (fun x => (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α)))
        atTop (𝓝 1)) :
    (Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
        atTop (𝓝 1) ↔
      Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1/h))
        (𝓝[>] (0 : ℝ)) (𝓝 1)) := by
  constructor
  · exact laplace_tail_asymptotic_of_tail_ge μ hμ hα0 hα1 hfmeas hrv
  · intro hL
    exact tendsto_tail_ge_of_tail_gt μ hα0 hα1 hrv (hconv hL)

/-! ### The two tail forms are equivalent -/

/-- **The strict and non-strict tail asymptotics are equivalent.**
For a probability measure `μ`, `f` regularly varying of index `-α` and
`0 ≤ α < 1`,
`μ (Set.Ici x) ~ f x / Γ(1-α)` iff `μ (Set.Ioi x) ~ f x / Γ(1-α)`.
This is the conjunction of the two endpoint bridges and shows in particular that
the strict-tail choice of `Analysis/TauberianLaplace.lean` loses nothing. -/
theorem tendsto_tail_ge_iff_tail_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrv : RegularlyVaryingAtTop f (-α)) :
    (Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
        atTop (𝓝 1) ↔
      Tendsto (fun x => (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α)))
        atTop (𝓝 1)) :=
  ⟨tendsto_tail_gt_of_tail_ge μ hα0 hα1 hrv,
    tendsto_tail_ge_of_tail_gt μ hα0 hα1 hrv⟩

/-! ### The rescaled form of the Laplace hypothesis -/

/-- **Rescaling identity for the Laplace hypothesis.**  For `h > 0` and any
`F : ℝ → ℝ`,
`h ∫_0^∞ e^{-h x} F x dx = ∫_0^∞ e^{-u} F (u/h) du`.
This is the substitution `u = h x`; it converts the `h ∫ e^{-hx} F` form of
Theorem I.2.11 into the `∫ e^{-u} F (u/h)` form. -/
theorem integral_comp_laplace_rescale {F : ℝ → ℝ} {h : ℝ} (hh : 0 < h) :
    h * (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(h * x)) * F x)
      = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * F (u / h) := by
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hcomp := integral_comp_mul_left_Ioi
    (fun u : ℝ => Real.exp (-u) * F (u / h)) (0 : ℝ) hh
  simp only [smul_eq_mul, mul_zero] at hcomp
  have hfun : (fun x : ℝ => Real.exp (-(h * x)) * F (h * x / h))
      = fun x : ℝ => Real.exp (-(h * x)) * F x := by
    ext x; rw [mul_div_cancel_left₀ x hh0]
  rw [hfun] at hcomp
  rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hh0, one_mul]

/-- **The two forms of the Laplace hypothesis are equivalent.**
`(∫_0^∞ e^{-u} F (u/h) du) / f (1/h) → 1` iff
`(h ∫_0^∞ e^{-h x} F x dx) / f (1/h) → 1` as `h ↓ 0`.  Immediate from
`integral_comp_laplace_rescale`; the two functions agree for `h > 0`. -/
theorem tendsto_kernel_form_iff {F f : ℝ → ℝ} :
    (Tendsto (fun h : ℝ => (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun h : ℝ => (h * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(h * x)) * F x) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1)) := by
  have heq : (fun h : ℝ => (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h))
      =ᶠ[𝓝[>] (0 : ℝ)]
        (fun h : ℝ => (h * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(h * x)) * F x) / f (1 / h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [integral_comp_laplace_rescale hh]
  exact ⟨fun hL => hL.congr' heq, fun hL => hL.congr' heq.symm⟩

/-! ### Lifting an antitone-function converse to the paper's `≥` statement -/

/-- **From an antitone-function Tauberian converse to the paper's `≥` statement.**
Suppose the strict-tail/Laplace Tauberian implication is available in the
following form (this is the shape of the remaining open obligation of Theorem
I.2.11, matching `tendsto_laplace_of_tail_asymptotic` with the implication
reversed): for every measurable, antitone, nonnegative `F` bounded by `1`,
`(h ∫_0^∞ e^{-hx} F x dx) / f (1/h) → 1` implies `F x ~ f x / Γ(1-α)`.

Then, for any probability measure `μ` carried by `[0,∞)` whose Laplace transform
satisfies `E_μ[1 - e^{-hX}] ~ f (1/h)`, the *non-strict* tail satisfies
`μ (Set.Ici x) ~ f x / Γ(1-α)`.

The proof applies the converse hypothesis to `F x = (μ (Set.Ioi x)).toReal`
(antitone, in `[0,1]`), identifying the Laplace hypothesis via
`integral_one_sub_exp_eq_laplace_tail`, and then transfers `Set.Ioi` to
`Set.Ici` with `tendsto_tail_ge_of_tail_gt`.  The converse hypothesis is an
explicit argument, not an axiom; nothing about the Tauberian argument itself is
assumed beyond the stated form. -/
theorem tail_ge_asymptotic_of_antitone_converse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrv : RegularlyVaryingAtTop f (-α))
    (hconv : ∀ F : ℝ → ℝ, Measurable F → Antitone F → (∀ x, 0 ≤ F x) →
      (∀ x, F x ≤ 1) →
      Tendsto (fun h : ℝ => (h * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(h * x)) * F x)
        / f (1 / h)) (𝓝[>] (0 : ℝ)) (𝓝 1) →
      Tendsto (fun x => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1))
    (hL : Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1) := by
  have hanti : Antitone fun x : ℝ => (μ (Set.Ioi x)).toReal := by
    intro a b hab
    exact toReal_le_toReal_of_subset μ (Set.Ioi_subset_Ioi hab)
  have hnonneg : ∀ x : ℝ, 0 ≤ (μ (Set.Ioi x)).toReal := fun x => ENNReal.toReal_nonneg
  have hle_one : ∀ x : ℝ, (μ (Set.Ioi x)).toReal ≤ 1 := by
    intro x
    have h2 : μ (Set.Ioi x) ≤ 1 := by
      have h3 : μ (Set.Ioi x) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rwa [IsProbabilityMeasure.measure_univ] at h3
    calc (μ (Set.Ioi x)).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top h2
      _ = 1 := by simp
  have hstep : Tendsto (fun h : ℝ =>
      (h * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(h * x)) * (μ (Set.Ioi x)).toReal)
        / f (1 / h)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [integral_one_sub_exp_eq_laplace_tail μ hμ hh]
  exact tendsto_tail_ge_of_tail_gt μ hα0 hα1 hrv
    (hconv _ hanti.measurable hanti hnonneg hle_one hstep)

/-- **The assembly with the converse stated in the kernel form
`(∫_0^∞ e^{-u} F (u/h) du) / f (1/h) → 1`.**

This is `tail_ge_asymptotic_of_antitone_converse` with the converse hypothesis
in the `∫ e^{-u} F (u/h)` form used in the statement of the remaining Tauberian
obligation.  Either form can be converted into the other with
`tendsto_kernel_form_iff`, so the two assembly theorems together accept the
converse in whichever of the two equivalent forms it is proved. -/
theorem tail_ge_asymptotic_of_antitone_kernel_converse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrv : RegularlyVaryingAtTop f (-α))
    (hconv : ∀ F : ℝ → ℝ, Measurable F → Antitone F → (∀ x, 0 ≤ F x) →
      (∀ x, F x ≤ 1) →
      Tendsto (fun h : ℝ => (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) →
      Tendsto (fun x => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1))
    (hL : Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1) := by
  refine tail_ge_asymptotic_of_antitone_converse μ hμ hα0 hα1 hrv ?_ hL
  intro F hFm hanti h0 h1 hk
  exact hconv F hFm hanti h0 h1 (tendsto_kernel_form_iff.2 hk)

/-! ### Specialisation to the power law `f x = x ^ (-α)` -/

/-- The endpoint equivalence for the explicit power law `f x = x ^ (-α)`.
This records that the regular-variation hypothesis of the bridges is
instantiable by an actual function (`regularlyVaryingAtTop_rpow`), with the
constant `Γ(1-α)` placed exactly as in Theorem I.2.11. -/
theorem tendsto_tail_ge_iff_tail_gt_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (Tendsto (fun x => (μ (Set.Ici x)).toReal / (x ^ (-α) / Real.Gamma (1 - α)))
        atTop (𝓝 1) ↔
      Tendsto (fun x => (μ (Set.Ioi x)).toReal / (x ^ (-α) / Real.Gamma (1 - α)))
        atTop (𝓝 1)) :=
  tendsto_tail_ge_iff_tail_gt μ hα0 hα1 (regularlyVaryingAtTop_rpow (-α))

/-- The Abelian half of Theorem I.2.11 in the paper's `≥` form for the explicit
power law `f x = x ^ (-α)`: if `P(X ≥ x) ∼ x ^ (-α) / Γ(1-α)` then
`E[1 - e^{-hX}] ∼ f (1/h) = (1/h) ^ (-α) = h ^ α` as `h ↓ 0`. -/
theorem laplace_tail_asymptotic_of_tail_ge_rpow
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (htail : Tendsto (fun x => (μ (Set.Ici x)).toReal / (x ^ (-α) / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / ((1 / h) ^ (-α)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  laplace_tail_asymptotic_of_tail_ge μ hμ hα0 hα1
    (by fun_prop : Measurable fun x : ℝ => x ^ (-α))
    (regularlyVaryingAtTop_rpow (-α)) htail

end PercLib.CriticalLRP.Analysis
