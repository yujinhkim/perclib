/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Removing the bound from the closed-event factorization of the pivotal flux

Swarm `smwvctsvt`, member `m3`, direction `d2`.

Production lands the closed-event factorization of the pivotal flux only for a **bounded**
observation `g` (`Orchestration.one_sub_mul_pivotalFlux_eq`):

  `(1 - q_e) * pivotalFlux mu g e = int omega, 1{e notin omega} (g (omega cup {e}) - g omega) dmu`.

Every version of the paper's per-edge flux at the *untruncated* cluster volume needs this
identity for the **unbounded** observation `|K_0|^2`, which the bounded theorem cannot supply.

This file removes the bound, without truncating the model:

* `levelTrunc g n = g and n`;
* `min_sub_min_eq` -- the clamp formula `min a n - min b n = min (max (n - b) 0) (a - b)` for
  `b <= a`, which makes the flip difference of the level truncation monotone in `n` and
  eventually equal to the untruncated flip difference;
* `ofReal_one_sub_mul_lintegral_flipDiff_eq` -- the `ENNReal` identity at the full observation,
  from the bounded real identity at `g and n` by monotone convergence. No integrability, no
  a.e.-finiteness and no domination enters;
* `one_sub_mul_pivotalFlux_eq_of_monotone` -- the **real** identity at the full observation for a
  measurable, nonnegative, `subset`-monotone real `g`.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.RussoInf.FluxTruncation.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.RussoInf.Merge

/-!
# From bounded to unbounded observations in the closed-edge factorization
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The level truncation and the flip difference -/

/-- The level truncation of a measurable functional is measurable. -/
theorem measurable_levelTrunc {g : Config V → ℝ} (hG : Measurable g) (n : ℕ) :
    Measurable (levelTrunc g n) :=
  hG.min measurable_const

/-- The level truncation of a nonnegative functional is bounded by its level. -/
theorem abs_levelTrunc_le {g : Config V → ℝ} (hnn : ∀ ω, 0 ≤ g ω) (n : ℕ)
    (ω : Config V) : |levelTrunc g n ω| ≤ (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : 0 ≤ min (g ω) (n : ℝ) := le_min (hnn ω) hn
  have h2 : min (g ω) (n : ℝ) ≤ (n : ℝ) := min_le_right _ _
  rw [levelTrunc, abs_of_nonneg h1]
  exact h2

/-- The level truncation is monotone in the configuration when `g` is. -/
theorem levelTrunc_mono {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') {n : ℕ} :
    ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → levelTrunc g n ω ≤ levelTrunc g n ω' :=
  fun ⦃_ _⦄ h => min_le_min (hmono h) le_rfl

/-- A configuration with the edge `e` deleted is contained in the same configuration with the
edge `e` added.  This is the comparison that makes the flip difference nonnegative. -/
theorem sdiff_singleton_subset_union_self (e : Sym2 V) (ω : Config V) :
    ω \ {e} ⊆ ω ∪ {e} := by
  intro x hx
  exact Set.mem_union_left _ hx.1

/-- **The flip difference as a difference over `union` and `sdiff`.** -/
theorem flipDiff_eq_union_sdiff (g : Config V → ℝ) (e : Sym2 V) (ω : Config V) :
    flipDiff g e ω = g (ω ∪ {e}) - g (ω \ {e}) := by
  simp only [flipDiff, forceOn_singleton_open_eq, forceOn_singleton_closed_eq]

/-- The flip difference of a monotone functional is nonnegative: opening `e` only adds edges. -/
theorem flipDiff_nonneg {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (e : Sym2 V) (ω : Config V) :
    0 ≤ flipDiff g e ω := by
  rw [flipDiff_eq_union_sdiff]
  exact sub_nonneg.mpr (hmono (sdiff_singleton_subset_union_self e ω))

/-! ## 2. The clamp formula for `min a n - min b n` -/

/-- **Clamp form of a difference of minima.**  For `b <= a`,
`min a n - min b n = min (max (n - b) 0) (a - b)`.  The right-hand side is manifestly monotone
in `n` and constant once `n >= a`, which is what the monotone-convergence argument needs. -/
theorem min_sub_min_eq {a b n : ℝ} (hab : b ≤ a) :
    min a n - min b n = min (max (n - b) 0) (a - b) := by
  rcases le_total n b with h | h
  · have h1 : min a n = n := min_eq_right (le_trans h hab)
    have h2 : min b n = n := min_eq_right h
    have h3 : max (n - b) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, h3, sub_self, min_eq_left (by linarith)]
  · rcases le_total n a with h1 | h1
    · have h2 : min a n = n := min_eq_right h1
      have h3 : min b n = b := min_eq_left h
      have h4 : max (n - b) 0 = n - b := max_eq_left (by linarith)
      rw [h2, h3, h4, min_eq_left (by linarith)]
    · have h2 : min a n = a := min_eq_left h1
      have h3 : min b n = b := min_eq_left (le_trans hab h1)
      have h4 : max (n - b) 0 = n - b := max_eq_left (by linarith)
      rw [h2, h3, h4, min_eq_right (by linarith)]

/-- **The flip difference of the level truncation, in clamp form.** -/
theorem flipDiff_levelTrunc_eq {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (e : Sym2 V) (ω : Config V)
    (n : ℕ) :
    flipDiff (levelTrunc g n) e ω
      = min (max ((n : ℝ) - g (ω \ {e})) 0) (g (ω ∪ {e}) - g (ω \ {e})) := by
  simp only [levelTrunc, flipDiff_eq_union_sdiff]
  exact min_sub_min_eq (hmono (sdiff_singleton_subset_union_self e ω))

/-- **The flip difference of the level truncation is monotone in the level.** -/
theorem flipDiff_levelTrunc_monotone {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (e : Sym2 V) (ω : Config V) :
    Monotone fun n : ℕ => flipDiff (levelTrunc g n) e ω := by
  intro m n hmn
  change flipDiff (levelTrunc g m) e ω ≤ flipDiff (levelTrunc g n) e ω
  rw [show flipDiff (levelTrunc g m) e ω
        = min (max ((m : ℝ) - g (ω \ {e})) 0) (g (ω ∪ {e}) - g (ω \ {e})) from
      flipDiff_levelTrunc_eq hmono e ω m,
    show flipDiff (levelTrunc g n) e ω
        = min (max ((n : ℝ) - g (ω \ {e})) 0) (g (ω ∪ {e}) - g (ω \ {e})) from
      flipDiff_levelTrunc_eq hmono e ω n]
  refine min_le_min (max_le_max ?_ le_rfl) le_rfl
  have h : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  linarith

/-- **The flip difference of the level truncation is eventually the untruncated one.** -/
theorem eventually_flipDiff_levelTrunc_eq (g : Config V → ℝ) (e : Sym2 V) (ω : Config V) :
    ∀ᶠ n : ℕ in Filter.atTop, flipDiff (levelTrunc g n) e ω = flipDiff g e ω := by
  refine Filter.eventually_atTop.mpr
    ⟨Nat.ceil (max (g (ω ∪ {e})) (g (ω \ {e}))) + 1, fun n hn => ?_⟩
  have hb : g (ω ∪ {e}) ≤ (n : ℝ) := by
    have h1 : max (g (ω ∪ {e})) (g (ω \ {e}))
        ≤ ((Nat.ceil (max (g (ω ∪ {e})) (g (ω \ {e}))) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (max (g (ω ∪ {e})) (g (ω \ {e}))) : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h2' : ((Nat.ceil (max (g (ω ∪ {e})) (g (ω \ {e}))) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast hn
      linarith
    linarith [le_max_left (g (ω ∪ {e})) (g (ω \ {e}))]
  have hc : g (ω \ {e}) ≤ (n : ℝ) := by
    have h1 : max (g (ω ∪ {e})) (g (ω \ {e}))
        ≤ ((Nat.ceil (max (g (ω ∪ {e})) (g (ω \ {e}))) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (max (g (ω ∪ {e})) (g (ω \ {e}))) : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h2' : ((Nat.ceil (max (g (ω ∪ {e})) (g (ω \ {e}))) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast hn
      linarith
    linarith [le_max_right (g (ω ∪ {e})) (g (ω \ {e}))]
  rw [flipDiff_eq_union_sdiff, flipDiff_eq_union_sdiff]
  simp only [levelTrunc, min_eq_left hb, min_eq_left hc]

/-- A monotone `Nat`-indexed family in `ENNReal` that is eventually constant has that constant
as its supremum. -/
theorem iSup_nat_eq_of_monotone_of_eventually_eq {f : ℕ → ℝ≥0∞} (hf : Monotone f)
    {c : ℝ≥0∞} (h : ∀ᶠ n : ℕ in Filter.atTop, f n = c) : (⨆ n, f n) = c := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · rw [← hN (max n N) (le_max_right n N)]
    exact hf (le_max_left n N)
  · calc c = f N := (hN N le_rfl).symm
      _ ≤ ⨆ n, f n := le_iSup f N

/-- **Pointwise sup of the level-truncated flip differences, in `ENNReal`.** -/
theorem iSup_ofReal_flipDiff_levelTrunc {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (e : Sym2 V) (ω : Config V) :
    (⨆ n : ℕ, ENNReal.ofReal (flipDiff (levelTrunc g n) e ω))
      = ENNReal.ofReal (flipDiff g e ω) := by
  refine iSup_nat_eq_of_monotone_of_eventually_eq ?_ ?_
  · exact fun m n hmn => ENNReal.ofReal_le_ofReal (flipDiff_levelTrunc_monotone hmono e ω hmn)
  · exact (eventually_flipDiff_levelTrunc_eq g e ω).mono fun n hn => by rw [hn]

/-! ## 3. The closed-event increment and its level truncations -/

/-- The closed-event increment of a measurable functional is measurable. -/
theorem measurable_closedIncr {g : Config V → ℝ} (hG : Measurable g) (e : Sym2 V) :
    Measurable (closedIncr g e) := by
  have h1 : Measurable fun ω : Config V => g (ω ∪ {e}) :=
    hG.comp (measurable_union_singleton e)
  exact Measurable.ite (measurableSet_mem e) measurable_const (h1.sub hG)

/-- The closed-event increment of a monotone functional is nonnegative. -/
theorem closedIncr_nonneg {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (e : Sym2 V) (ω : Config V) :
    0 ≤ closedIncr g e ω := by
  rw [closedIncr]
  by_cases h : e ∈ ω
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact sub_nonneg.mpr (hmono (Set.subset_union_left))

/-- The level truncation of the closed-event increment is monotone in the level. -/
theorem closedIncr_levelTrunc_monotone {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (e : Sym2 V) (ω : Config V) :
    Monotone fun n : ℕ => closedIncr (levelTrunc g n) e ω := by
  intro m n hmn
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  by_cases h : e ∈ ω
  · simp only [closedIncr, h, ite_true, le_refl]
  · simp only [closedIncr, h, ite_false, levelTrunc]
    have hab : g ω ≤ g (ω ∪ {e}) := hmono (Set.subset_union_left)
    rw [min_sub_min_eq hab (n := m), min_sub_min_eq hab (n := n)]
    refine min_le_min (max_le_max ?_ le_rfl) le_rfl
    linarith

/-- The closed-event increment of the level truncation is eventually the untruncated one. -/
theorem eventually_closedIncr_levelTrunc_eq (g : Config V → ℝ) (e : Sym2 V) (ω : Config V) :
    ∀ᶠ n : ℕ in Filter.atTop, closedIncr (levelTrunc g n) e ω = closedIncr g e ω := by
  refine Filter.eventually_atTop.mpr
    ⟨Nat.ceil (max (g (ω ∪ {e})) (g ω)) + 1, fun n hn => ?_⟩
  have hb : g (ω ∪ {e}) ≤ (n : ℝ) := by
    have h1 : max (g (ω ∪ {e})) (g ω)
        ≤ ((Nat.ceil (max (g (ω ∪ {e})) (g ω)) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (max (g (ω ∪ {e})) (g ω)) : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h2' : ((Nat.ceil (max (g (ω ∪ {e})) (g ω)) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast hn
      linarith
    linarith [le_max_left (g (ω ∪ {e})) (g ω)]
  have hc : g ω ≤ (n : ℝ) := by
    have h1 : max (g (ω ∪ {e})) (g ω)
        ≤ ((Nat.ceil (max (g (ω ∪ {e})) (g ω)) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (max (g (ω ∪ {e})) (g ω)) : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h2' : ((Nat.ceil (max (g (ω ∪ {e})) (g ω)) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast hn
      linarith
    linarith [le_max_right (g (ω ∪ {e})) (g ω)]
  simp only [closedIncr, levelTrunc, min_eq_left hb, min_eq_left hc]

/-- **Pointwise sup of the level-truncated closed-event increments, in `ENNReal`.** -/
theorem iSup_ofReal_closedIncr_levelTrunc {g : Config V → ℝ}
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (e : Sym2 V) (ω : Config V) :
    (⨆ n : ℕ, ENNReal.ofReal (closedIncr (levelTrunc g n) e ω))
      = ENNReal.ofReal (closedIncr g e ω) := by
  refine iSup_nat_eq_of_monotone_of_eventually_eq ?_ ?_
  · exact fun m n hmn => ENNReal.ofReal_le_ofReal (closedIncr_levelTrunc_monotone hmono e ω hmn)
  · exact (eventually_closedIncr_levelTrunc_eq g e ω).mono fun n hn => by rw [hn]

/-! ## 4. The per-level `ENNReal` identity, and closure under monotone limits -/

/-- The flip difference of a measurable functional is measurable. -/
theorem measurable_flipDiff {g : Config V → ℝ} (hG : Measurable g) (e : Sym2 V) :
    Measurable (flipDiff g e) := by
  have h1 : Measurable fun ω : Config V => g (ω ∪ {e}) :=
    hG.comp (measurable_union_singleton e)
  have h2 : Measurable fun ω : Config V => g (ω \ {e}) :=
    hG.comp (PercLib.Probability.measurable_diff_singleton e)
  have h := h1.sub h2
  rwa [show flipDiff g e = fun ω : Config V => g (ω ∪ {e}) - g (ω \ {e}) from
    funext fun ω => flipDiff_eq_union_sdiff g e ω]

/-- The flip difference of the level truncation is bounded by the level. -/
theorem flipDiff_levelTrunc_le {g : Config V → ℝ} (hnn : ∀ ω, 0 ≤ g ω) (e : Sym2 V)
    (ω : Config V) (n : ℕ) : flipDiff (levelTrunc g n) e ω ≤ (n : ℝ) := by
  rw [flipDiff_eq_union_sdiff]
  have h1 : 0 ≤ levelTrunc g n (ω \ {e}) := le_min (hnn _) (Nat.cast_nonneg n)
  have h2 : levelTrunc g n (ω ∪ {e}) ≤ (n : ℝ) := min_le_right _ _
  linarith

/-- The level truncation of the closed-event increment is bounded by the level. -/
theorem closedIncr_levelTrunc_le {g : Config V → ℝ} (hnn : ∀ ω, 0 ≤ g ω) (e : Sym2 V)
    (ω : Config V) (n : ℕ) : closedIncr (levelTrunc g n) e ω ≤ (n : ℝ) := by
  rw [closedIncr]
  by_cases h : e ∈ ω
  · rw [ite_eq_left h]; exact Nat.cast_nonneg n
  · rw [ite_eq_right h]
    have h1 : 0 ≤ levelTrunc g n ω := le_min (hnn _) (Nat.cast_nonneg n)
    have h2 : levelTrunc g n (ω ∪ {e}) ≤ (n : ℝ) := min_le_right _ _
    linarith

/-- A bounded nonnegative integrand has finite `lintegral` for a probability measure. -/
theorem lintegral_ofReal_ne_top_of_le {f : Config V → ℝ} {n : ℕ}
    (hF : ∀ ω : Config V, ENNReal.ofReal (f ω) ≤ ENNReal.ofReal (n : ℝ))
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≠ ⊤ := by
  have hle : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal (n : ℝ) := by
    calc ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ∫⁻ _ : Config V, ENNReal.ofReal (n : ℝ) ∂μ :=
          lintegral_mono hF
      _ = ENNReal.ofReal (n : ℝ) := by rw [lintegral_const, measure_univ, mul_one]
  exact ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := (n : ℝ))) hle

/-- **The closed-edge factorization at level `n`, in `ENNReal`.**  This is the landed bounded
real identity `one_sub_mul_pivotalFlux_eq` at `g ∧ n`, with both real integrals replaced by
their (finite) `ENNReal` counterparts. -/
theorem ofReal_one_sub_mul_lintegral_flipDiff_levelTrunc (π : Sym2 V → unitInterval)
    (e : Sym2 V) {g : Config V → ℝ} (hG : Measurable g) (hnn : ∀ ω, 0 ≤ g ω)
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') (m : ℕ) :
    ENNReal.ofReal (1 - (π e : ℝ))
        * (∫⁻ ω, ENNReal.ofReal (flipDiff (levelTrunc g m) e ω)
            ∂(PercLib.Percolation.Bond.law π))
      = ∫⁻ ω, ENNReal.ofReal (closedIncr (levelTrunc g m) e ω)
          ∂(PercLib.Percolation.Bond.law π) := by
  classical
  have hbdd := one_sub_mul_pivotalFlux_eq (V := V) π e
    (g := levelTrunc g m) (measurable_levelTrunc hG m) (C := (m : ℝ))
    (fun ω => abs_levelTrunc_le hnn m ω)
  have hmonoT : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → levelTrunc g m ω ≤ levelTrunc g m ω' :=
    levelTrunc_mono hmono
  have hflip : ∫ ω, flipDiff (levelTrunc g m) e ω
        ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, ENNReal.ofReal (flipDiff (levelTrunc g m) e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (flipDiff_nonneg hmonoT e))
      (measurable_flipDiff (measurable_levelTrunc hG m) e).aestronglyMeasurable
  have hincr : ∫ ω, closedIncr (levelTrunc g m) e ω
        ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, ENNReal.ofReal (closedIncr (levelTrunc g m) e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (closedIncr_nonneg hmonoT e))
      (measurable_closedIncr (measurable_levelTrunc hG m) e).aestronglyMeasurable
  have hAle := lintegral_ofReal_ne_top_of_le (fun ω =>
    ENNReal.ofReal_le_ofReal (flipDiff_levelTrunc_le hnn e ω m)) (PercLib.Percolation.Bond.law π)
  have hBle := lintegral_ofReal_ne_top_of_le (fun ω =>
    ENNReal.ofReal_le_ofReal (closedIncr_levelTrunc_le hnn e ω m)) (PercLib.Percolation.Bond.law π)
  have hq : (0 : ℝ) ≤ 1 - (π e : ℝ) := by
    have h := (π e).2.2; linarith
  have hstep : ENNReal.ofReal ((1 - (π e : ℝ))
        * (∫⁻ ω, ENNReal.ofReal (flipDiff (levelTrunc g m) e ω)
            ∂(PercLib.Percolation.Bond.law π)).toReal)
      = ENNReal.ofReal ((∫⁻ ω, ENNReal.ofReal (closedIncr (levelTrunc g m) e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal) := by
    rw [← hflip, ← hincr]
    exact congrArg ENNReal.ofReal hbdd
  rw [ENNReal.ofReal_mul hq, ENNReal.ofReal_toReal hAle, ENNReal.ofReal_toReal hBle] at hstep
  exact hstep

/-- **The closed-edge factorization at the full observation, in `ENNReal`.**

Two monotone-convergence steps remove the level truncation from
`ofReal_one_sub_mul_lintegral_flipDiff_levelTrunc`.  The statement is in `ℝ≥0∞`, so no
integrability, no a.e.-finiteness and no domination is required, and the degenerate case
`q_e = 1` (where the multiplier `1 - q_e` is `0`) is covered by the same identity. -/
theorem ofReal_one_sub_mul_lintegral_flipDiff_eq (π : Sym2 V → unitInterval) (e : Sym2 V)
    {g : Config V → ℝ} (hG : Measurable g) (hnn : ∀ ω, 0 ≤ g ω)
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') :
    ENNReal.ofReal (1 - (π e : ℝ))
        * (∫⁻ ω, ENNReal.ofReal (flipDiff g e ω)
            ∂(PercLib.Percolation.Bond.law π))
      = ∫⁻ ω, ENNReal.ofReal (closedIncr g e ω) ∂(PercLib.Percolation.Bond.law π) := by
  classical
  have hmeas_flip : ∀ m : ℕ, Measurable fun ω : Config V =>
      ENNReal.ofReal (flipDiff (levelTrunc g m) e ω) := fun m =>
    ENNReal.measurable_ofReal.comp (measurable_flipDiff (measurable_levelTrunc hG m) e)
  have hmeas_incr : ∀ m : ℕ, Measurable fun ω : Config V =>
      ENNReal.ofReal (closedIncr (levelTrunc g m) e ω) := fun m =>
    ENNReal.measurable_ofReal.comp (measurable_closedIncr (measurable_levelTrunc hG m) e)
  have hmono_flip : Monotone fun m : ℕ => fun ω : Config V =>
      ENNReal.ofReal (flipDiff (levelTrunc g m) e ω) :=
    fun m m' hmm' ω => ENNReal.ofReal_le_ofReal (flipDiff_levelTrunc_monotone hmono e ω hmm')
  have hmono_incr : Monotone fun m : ℕ => fun ω : Config V =>
      ENNReal.ofReal (closedIncr (levelTrunc g m) e ω) :=
    fun m m' hmm' ω => ENNReal.ofReal_le_ofReal (closedIncr_levelTrunc_monotone hmono e ω hmm')
  have hL : (⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal (flipDiff (levelTrunc g m) e ω)
        ∂(PercLib.Percolation.Bond.law π))
      = ∫⁻ ω, ENNReal.ofReal (flipDiff g e ω)
          ∂(PercLib.Percolation.Bond.law π) := by
    rw [← lintegral_iSup hmeas_flip hmono_flip]
    exact lintegral_congr fun ω => iSup_ofReal_flipDiff_levelTrunc hmono e ω
  have hR : (⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal (closedIncr (levelTrunc g m) e ω)
        ∂(PercLib.Percolation.Bond.law π))
      = ∫⁻ ω, ENNReal.ofReal (closedIncr g e ω)
          ∂(PercLib.Percolation.Bond.law π) := by
    rw [← lintegral_iSup hmeas_incr hmono_incr]
    exact lintegral_congr fun ω => iSup_ofReal_closedIncr_levelTrunc hmono e ω
  calc ENNReal.ofReal (1 - (π e : ℝ))
        * (∫⁻ ω, ENNReal.ofReal (flipDiff g e ω)
            ∂(PercLib.Percolation.Bond.law π))
      = ENNReal.ofReal (1 - (π e : ℝ))
          * (⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal (flipDiff (levelTrunc g m) e ω)
              ∂(PercLib.Percolation.Bond.law π)) := by rw [hL]
    _ = ⨆ m : ℕ, ENNReal.ofReal (1 - (π e : ℝ))
          * (∫⁻ ω, ENNReal.ofReal (flipDiff (levelTrunc g m) e ω)
              ∂(PercLib.Percolation.Bond.law π)) := by
        rw [ENNReal.mul_iSup]
    _ = ⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal (closedIncr (levelTrunc g m) e ω)
          ∂(PercLib.Percolation.Bond.law π) :=
        iSup_congr fun m => ofReal_one_sub_mul_lintegral_flipDiff_levelTrunc π e hG hnn hmono m
    _ = ∫⁻ ω, ENNReal.ofReal (closedIncr g e ω) ∂(PercLib.Percolation.Bond.law π) := hR

/-! ## 5. The real identity at the full observation -/

/-- **The closed-edge factorization of the pivotal flux at an unbounded monotone observation.**

For a measurable, nonnegative, `⊆`-monotone functional `g` on the independent-edge space,

  `(1 - q_e) * pivotalFlux μ g e = ∫ ω, 1{e ∉ ω} (g (ω ∪ {e}) - g ω) ∂μ`.

Nothing is bounded and nothing is truncated: the level truncation is removed by monotone
convergence.  This is the `ℝ`-image of `ofReal_one_sub_mul_lintegral_flipDiff_eq`; the finite
form that identifies the two sides with the model's edge increments carries the explicit
hypothesis `… ≠ ⊤` in `FluxTruncationModel`. -/
theorem one_sub_mul_pivotalFlux_eq_of_monotone (π : Sym2 V → unitInterval) (e : Sym2 V)
    {g : Config V → ℝ} (hG : Measurable g) (hnn : ∀ ω, 0 ≤ g ω)
    (hmono : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') :
    (1 - (π e : ℝ)) * pivotalFlux (PercLib.Percolation.Bond.law π) g e
      = ∫ ω, closedIncr g e ω ∂(PercLib.Percolation.Bond.law π) := by
  classical
  have hq : (0 : ℝ) ≤ 1 - (π e : ℝ) := by
    have h := (π e).2.2; linarith
  have hflip : ∫ ω, flipDiff g e ω ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, ENNReal.ofReal (flipDiff g e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (flipDiff_nonneg hmono e))
      (measurable_flipDiff hG e).aestronglyMeasurable
  have hincr : ∫ ω, closedIncr g e ω ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, ENNReal.ofReal (closedIncr g e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (closedIncr_nonneg hmono e))
      (measurable_closedIncr hG e).aestronglyMeasurable
  calc (1 - (π e : ℝ)) * pivotalFlux (PercLib.Percolation.Bond.law π) g e
      = (1 - (π e : ℝ)) * (∫ ω, flipDiff g e ω
          ∂(PercLib.Percolation.Bond.law π)) := rfl
    _ = (1 - (π e : ℝ)) * (∫⁻ ω, ENNReal.ofReal (flipDiff g e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal := by rw [hflip]
    _ = (ENNReal.ofReal (1 - (π e : ℝ))).toReal
          * (∫⁻ ω, ENNReal.ofReal (flipDiff g e ω)
              ∂(PercLib.Percolation.Bond.law π)).toReal := by
        rw [ENNReal.toReal_ofReal hq]
    _ = (ENNReal.ofReal (1 - (π e : ℝ))
          * (∫⁻ ω, ENNReal.ofReal (flipDiff g e ω)
              ∂(PercLib.Percolation.Bond.law π))).toReal := (ENNReal.toReal_mul).symm
    _ = (∫⁻ ω, ENNReal.ofReal (closedIncr g e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal := by
        rw [ofReal_one_sub_mul_lintegral_flipDiff_eq π e hG hnn hmono]
    _ = ∫ ω, closedIncr g e ω ∂(PercLib.Percolation.Bond.law π) := hincr.symm

end PercLib.CriticalLRP.Orchestration
