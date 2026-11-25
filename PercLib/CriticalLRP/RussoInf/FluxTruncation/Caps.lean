/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Removing the finite truncation from the real `p = 2` per-edge flux

Swarm `smwvctsvt`, member `m3`, direction `d2`.

`FluxTruncation` removes the *bound* from the closed-edge factorization of the pivotal flux: for a
measurable, nonnegative, `⊆`-monotone real functional `g`,

  `(1 - q_e) * pivotalFlux μ g e = ∫ ω, 1{e ∉ ω} (g (ω ∪ {e}) - g ω) ∂μ`.

The `p = 2` flux needs this at `g ω = (clusterVol ω 0).toReal ^ 2`.  That functional is *not*
pointwise monotone: `clusterVol` takes values in `ℝ≥0∞`, and `toReal` sends `⊤` to `0`, so at a
configuration whose origin cluster is infinite the functional drops to `0`.  This file removes the
defect the same way the paper does, by a truncation at the level of the *extended* volume:

* `clusterVolCap n ω o = (n ⊓ clusterVol ω o).toReal` — the capped cluster volume.  It is
  nonnegative, bounded by `n`, measurable, monotone in `ω` and monotone in `n`, **for every
  configuration** (the whole point of capping in `ℝ≥0∞` before taking `toReal`);
* `sq_sub_sq_monotone_nat` — for nonnegative monotone families `y ≤ x`, the difference of squares
  `x_n² - y_n²` is monotone.  This is what makes the flip difference of the capped square monotone
  in the cap, and hence what lets monotone convergence pass to the cap limit;
* `ofReal_one_sub_mul_lintegral_flipDiff_eq_of_mono_approx` — the `ℝ≥0∞` identity at the limit of a
  bounded monotone approximating family;
* `SourceModelData.one_sub_mul_pivotalFlux_clusterVol_sq` — **the real per-edge closed-event flux
  identity at the untruncated cluster volume**, at fixed `r` and an arbitrary edge `e`.  Its only
  hypothesis is the source's finite first cut-off moment `M.cutMoment 1 r ≠ ⊤`, which supplies the
  a.e. finiteness of every cluster volume (`PivotFlux.ae_forall_lt_top_clusterVol`) and hence the
  a.e. finiteness at the *flipped* configurations, via the enclosure
  `clusterVol_union_singleton_le` (opening one edge can only add the two endpoint clusters).

No radius is differentiated, no edge sum is taken and no moment finiteness beyond the first is
claimed.  The remaining step to the paper's FLUX identity is the edge sum
`Σ_e cutEdgeClosedWeight r e * pivotalFlux …` against `∫ (p2PaperSum).toReal`, which needs the
`ℝ≥0∞` edge decomposition and real summability; that is *not* claimed here.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.RussoInf.FluxTruncation.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Transport.ToReal

/-!
# Capped cluster volumes and the untruncated `p = 2` per-edge flux
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

/-! ## 1. The capped cluster volume -/

/-- The capped cluster volume is nonnegative. -/
theorem clusterVolCap_nonneg (n : ℕ) (ω : Config V) (o : V) : 0 ≤ clusterVolCap n ω o :=
  ENNReal.toReal_nonneg

/-- The capped cluster volume is bounded by the cap. -/
theorem clusterVolCap_le (n : ℕ) (ω : Config V) (o : V) : clusterVolCap n ω o ≤ (n : ℝ) := by
  have h : ((n : ℝ≥0∞) ⊓ clusterVol ω o) ≤ (n : ℝ≥0∞) := inf_le_left
  have h2 := ENNReal.toReal_mono (by simp : ((n : ℝ≥0∞)) ≠ ⊤) h
  simpa only [clusterVolCap, ENNReal.toReal_natCast] using h2

/-- The capped cluster volume is measurable in the configuration. -/
theorem measurable_clusterVolCap (n : ℕ) (o : V) :
    Measurable fun ω : Config V => clusterVolCap n ω o :=
  ((measurable_const (a := (n : ℝ≥0∞))).inf (measurable_clusterVol o)).ennreal_toReal

/-- The capped cluster volume is monotone in the configuration. -/
theorem clusterVolCap_mono (n : ℕ) (o : V) :
    ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → clusterVolCap n ω o ≤ clusterVolCap n ω' o := by
  intro ω ω' h
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) inf_le_left) ?_
  exact inf_le_inf le_rfl (clusterVol_mono (fun e he => h he) o)

/-- The capped cluster volume is monotone in the cap. -/
theorem clusterVolCap_mono_level (ω : Config V) (o : V) :
    Monotone fun n : ℕ => clusterVolCap n ω o := by
  intro m n hmn
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) inf_le_left) ?_
  refine inf_le_inf_right _ ?_
  exact_mod_cast hmn

/-- For a finite cluster volume, the cap is eventually the volume itself. -/
theorem eventually_clusterVolCap_eq (ω : Config V) (o : V) (h : clusterVol ω o ≠ ⊤) :
    ∀ᶠ n : ℕ in Filter.atTop, clusterVolCap n ω o = (clusterVol ω o).toReal := by
  refine Filter.eventually_atTop.mpr ⟨Nat.ceil (clusterVol ω o).toReal + 1, fun n hn => ?_⟩
  have hle : clusterVol ω o ≤ (n : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal h, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (clusterVol ω o).toReal
        ≤ ((Nat.ceil (clusterVol ω o).toReal : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (clusterVol ω o).toReal : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h2' : ((Nat.ceil (clusterVol ω o).toReal : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith
  simp only [clusterVolCap, (inf_eq_right).mpr hle]

/-- The capped square is measurable. -/
theorem measurable_capSq (n : ℕ) (o : V) : Measurable (capSq (V := V) n o) :=
  (measurable_clusterVolCap n o).pow_const 2

/-- The capped square is nonnegative. -/
theorem capSq_nonneg (n : ℕ) (o : V) (ω : Config V) : 0 ≤ capSq n o ω :=
  sq_nonneg _

/-- The capped square is monotone in the configuration. -/
theorem capSq_mono (n : ℕ) (o : V) :
    ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → capSq n o ω ≤ capSq n o ω' := by
  intro ω ω' h
  change clusterVolCap n ω o ^ 2 ≤ clusterVolCap n ω' o ^ 2
  have h1 := clusterVolCap_mono n o h
  have h2 := clusterVolCap_nonneg n ω o
  nlinarith

/-- The `toReal` of a capped natural is the minimum of the two. -/
theorem toReal_inf_nat_eq {α : ℝ≥0∞} (hα : α ≠ ⊤) (n : ℕ) :
    ((n : ℝ≥0∞) ⊓ α).toReal = min (n : ℝ) α.toReal := by
  have h1 : ((n : ℝ≥0∞) ⊓ α).toReal ≤ (n : ℝ) := by
    have h := ENNReal.toReal_mono (a := (n : ℝ≥0∞) ⊓ α) (b := (n : ℝ≥0∞))
      (by simp) inf_le_left
    simpa only [ENNReal.toReal_natCast] using h
  have h2 : ((n : ℝ≥0∞) ⊓ α).toReal ≤ α.toReal :=
    ENNReal.toReal_mono (a := (n : ℝ≥0∞) ⊓ α) hα inf_le_right
  refine le_antisymm (le_min h1 h2) ?_
  rcases le_total α.toReal (n : ℝ) with h | h
  · have hαn : α ≤ (n : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_toReal hα, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal h
    rw [(inf_eq_right).mpr hαn]
    exact min_le_right _ _
  · have hnα : (n : ℝ≥0∞) ≤ α := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_toReal hα]
      exact ENNReal.ofReal_le_ofReal h
    rw [(inf_eq_left).mpr hnα]
    exact min_le_left _ _

/-- A truncated difference of reals is the positive part of the difference. -/
theorem sub_min_eq_max_sub (k c : ℝ) : k - min k c = max 0 (k - c) := by
  rcases le_total k c with h | h
  · rw [min_eq_left h, max_eq_left (by linarith), sub_self]
  · rw [min_eq_right h, max_eq_right (by linarith)]

/-- **The capped volumes separate monotonically.**  For `β ≤ α` the difference of the capped
volumes `min n α - min n β` is monotone in the cap `n`.  The point of capping in `ℝ≥0∞` is that
this is true for *every* pair, including `α = ⊤`. -/
theorem toReal_inf_nat_sub_monotone {α β : ℝ≥0∞} (h : β ≤ α) :
    Monotone fun n : ℕ => ((n : ℝ≥0∞) ⊓ α).toReal - ((n : ℝ≥0∞) ⊓ β).toReal := by
  intro m n hmn
  change ((m : ℝ≥0∞) ⊓ α).toReal - ((m : ℝ≥0∞) ⊓ β).toReal
    ≤ ((n : ℝ≥0∞) ⊓ α).toReal - ((n : ℝ≥0∞) ⊓ β).toReal
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  by_cases hα : α = ⊤
  · by_cases hβ : β = ⊤
    · subst hβ; subst hα
      simp only [inf_top_eq, ENNReal.toReal_natCast, sub_self]
      exact le_refl 0
    · subst hα
      have h1 : ((m : ℝ≥0∞) ⊓ ⊤).toReal = (m : ℝ) := by simp
      have h2 : ((n : ℝ≥0∞) ⊓ ⊤).toReal = (n : ℝ) := by simp
      have h3 : ((m : ℝ≥0∞) ⊓ β).toReal = min (m : ℝ) β.toReal := toReal_inf_nat_eq hβ m
      have h4 : ((n : ℝ≥0∞) ⊓ β).toReal = min (n : ℝ) β.toReal := toReal_inf_nat_eq hβ n
      have e1 : ((m : ℝ) - min (m : ℝ) β.toReal) = max 0 ((m : ℝ) - β.toReal) :=
        sub_min_eq_max_sub _ _
      have e2 : ((n : ℝ) - min (n : ℝ) β.toReal) = max 0 ((n : ℝ) - β.toReal) :=
        sub_min_eq_max_sub _ _
      rw [h1, h2, h3, h4, e1, e2]
      exact max_le_max le_rfl (by linarith)
  · have hβ : β ≠ ⊤ := ne_top_of_le_ne_top hα h
    have hle : β.toReal ≤ α.toReal := ENNReal.toReal_mono hα h
    have h1 : ((m : ℝ≥0∞) ⊓ α).toReal = min (m : ℝ) α.toReal := toReal_inf_nat_eq hα m
    have h2 : ((n : ℝ≥0∞) ⊓ α).toReal = min (n : ℝ) α.toReal := toReal_inf_nat_eq hα n
    have h3 : ((m : ℝ≥0∞) ⊓ β).toReal = min (m : ℝ) β.toReal := toReal_inf_nat_eq hβ m
    have h4 : ((n : ℝ≥0∞) ⊓ β).toReal = min (n : ℝ) β.toReal := toReal_inf_nat_eq hβ n
    rw [h1, h2, h3, h4,
      min_comm (m : ℝ) α.toReal, min_comm (m : ℝ) β.toReal,
      min_comm (n : ℝ) α.toReal, min_comm (n : ℝ) β.toReal,
      min_sub_min_eq hle (n := (m : ℝ)), min_sub_min_eq hle (n := (n : ℝ))]
    refine min_le_min (max_le_max ?_ le_rfl) le_rfl
    linarith

/-- **A difference of squares of nonnegative families with monotone difference is monotone.** -/
theorem sq_sub_sq_monotone_nat {x y : ℕ → ℝ} (hxy : ∀ n, y n ≤ x n)
    (hy0 : ∀ n, 0 ≤ y n) (hx : Monotone x) (hy : Monotone y)
    (hd : Monotone fun n => x n - y n) : Monotone fun n => x n ^ 2 - y n ^ 2 := by
  intro m n hmn
  change x m ^ 2 - y m ^ 2 ≤ x n ^ 2 - y n ^ 2
  have h1 : x m - y m ≤ x n - y n := hd hmn
  have h2 : x m + y m ≤ x n + y n := add_le_add (hx hmn) (hy hmn)
  have h3 : 0 ≤ x m + y m := by linarith [hxy m, hy0 m]
  have h4 : 0 ≤ x n - y n := by linarith [hxy n]
  have key : ∀ k : ℕ, x k ^ 2 - y k ^ 2 = (x k - y k) * (x k + y k) := fun k => by ring
  rw [key m, key n]
  exact mul_le_mul h1 h2 h3 h4

/-- The flipped configuration `ω \ {e}` is contained in `ω ∪ {e}`. -/
theorem sdiff_singleton_subset_union_singleton (e : Sym2 V) (ω : Config V) :
    ω \ {e} ⊆ ω ∪ {e} :=
  sdiff_singleton_subset_union_self e ω

/-- Monotonicity in the cap of the difference of squared capped volumes. -/
theorem cap_sq_sub_monotone {α β : ℝ≥0∞} (h : β ≤ α) :
    Monotone fun n : ℕ =>
      ((n : ℝ≥0∞) ⊓ α).toReal ^ 2 - ((n : ℝ≥0∞) ⊓ β).toReal ^ 2 := by
  refine sq_sub_sq_monotone_nat ?_ (fun n => ENNReal.toReal_nonneg)
    (fun m n hmn => ?_) (fun m n hmn => ?_) (toReal_inf_nat_sub_monotone h)
  · intro n
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) inf_le_left) (inf_le_inf le_rfl h)
  · have hmn' : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hmn
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) inf_le_left)
      (inf_le_inf hmn' le_rfl)
  · have hmn' : (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hmn
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) inf_le_left)
      (inf_le_inf hmn' le_rfl)

/-! ## 2. The `ℝ≥0∞` and real identities at the limit of a monotone family -/

/-- **Closed-edge factorization at the limit of a monotone approximating family.**

`G n` is a nonnegative, `⊆`-monotone family whose flip differences and closed-event increments are
monotone in `n` and increase to those of `Glim` a.e.  Then the `ℝ≥0∞` closed-edge factorization
holds at `Glim`.

The proof is: apply the bounded-by-level factorization `ofReal_one_sub_mul_lintegral_flipDiff_eq`
to each `G n`, and pass to the limit by monotone convergence in `ℝ≥0∞`.  Nothing is assumed about
boundedness of `Glim`. -/
theorem ofReal_one_sub_mul_lintegral_flipDiff_eq_of_mono (π : Sym2 V → unitInterval)
    (e : Sym2 V) {G : ℕ → Config V → ℝ} {Glim : Config V → ℝ}
    (hG : ∀ n, Measurable (G n)) (hnn : ∀ n ω, 0 ≤ G n ω)
    (hmonoω : ∀ n, ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → G n ω ≤ G n ω')
    (hflipmono : ∀ ω : Config V, Monotone fun n : ℕ => flipDiff (G n) e ω)
    (hincrmono : ∀ ω : Config V, Monotone fun n : ℕ => closedIncr (G n) e ω)
    (hflip : ∀ᵐ ω ∂(PercLib.Percolation.Bond.law π),
      (⨆ n : ℕ, ENNReal.ofReal (flipDiff (G n) e ω))
        = ENNReal.ofReal (flipDiff Glim e ω))
    (hincr : ∀ᵐ ω ∂(PercLib.Percolation.Bond.law π),
      (⨆ n : ℕ, ENNReal.ofReal (closedIncr (G n) e ω))
        = ENNReal.ofReal (closedIncr Glim e ω)) :
    ENNReal.ofReal (1 - (π e : ℝ))
        * (∫⁻ ω, ENNReal.ofReal (flipDiff Glim e ω)
            ∂(PercLib.Percolation.Bond.law π))
      = ∫⁻ ω, ENNReal.ofReal (closedIncr Glim e ω)
          ∂(PercLib.Percolation.Bond.law π) := by
  classical
  have hmeas_flip : ∀ n : ℕ, Measurable fun ω : Config V =>
      ENNReal.ofReal (flipDiff (G n) e ω) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_flipDiff (hG n) e)
  have hmeas_incr : ∀ n : ℕ, Measurable fun ω : Config V =>
      ENNReal.ofReal (closedIncr (G n) e ω) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_closedIncr (hG n) e)
  have hmono_flip : Monotone fun n : ℕ => fun ω : Config V =>
      ENNReal.ofReal (flipDiff (G n) e ω) :=
    fun m n hmn ω => ENNReal.ofReal_le_ofReal (hflipmono ω hmn)
  have hmono_incr : Monotone fun n : ℕ => fun ω : Config V =>
      ENNReal.ofReal (closedIncr (G n) e ω) :=
    fun m n hmn ω => ENNReal.ofReal_le_ofReal (hincrmono ω hmn)
  have hL : (⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (flipDiff (G n) e ω)
        ∂(PercLib.Percolation.Bond.law π))
      = ∫⁻ ω, ENNReal.ofReal (flipDiff Glim e ω)
          ∂(PercLib.Percolation.Bond.law π) := by
    rw [← lintegral_iSup hmeas_flip hmono_flip]
    exact lintegral_congr_ae hflip
  have hR : (⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (closedIncr (G n) e ω)
        ∂(PercLib.Percolation.Bond.law π))
      = ∫⁻ ω, ENNReal.ofReal (closedIncr Glim e ω)
          ∂(PercLib.Percolation.Bond.law π) := by
    rw [← lintegral_iSup hmeas_incr hmono_incr]
    exact lintegral_congr_ae hincr
  calc ENNReal.ofReal (1 - (π e : ℝ))
        * (∫⁻ ω, ENNReal.ofReal (flipDiff Glim e ω)
            ∂(PercLib.Percolation.Bond.law π))
      = ENNReal.ofReal (1 - (π e : ℝ))
          * (⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (flipDiff (G n) e ω)
              ∂(PercLib.Percolation.Bond.law π)) := by rw [hL]
    _ = ⨆ n : ℕ, ENNReal.ofReal (1 - (π e : ℝ))
          * (∫⁻ ω, ENNReal.ofReal (flipDiff (G n) e ω)
              ∂(PercLib.Percolation.Bond.law π)) := by
        rw [ENNReal.mul_iSup]
    _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (closedIncr (G n) e ω)
          ∂(PercLib.Percolation.Bond.law π) :=
        iSup_congr fun n =>
          ofReal_one_sub_mul_lintegral_flipDiff_eq π e (hG n) (hnn n) (hmonoω n)
    _ = ∫⁻ ω, ENNReal.ofReal (closedIncr Glim e ω)
          ∂(PercLib.Percolation.Bond.law π) := hR

/-- **The real closed-edge factorization at the limit of a monotone family.** -/
theorem one_sub_mul_pivotalFlux_eq_of_mono (π : Sym2 V → unitInterval)
    (e : Sym2 V) {G : ℕ → Config V → ℝ} {Glim : Config V → ℝ}
    (hG : ∀ n, Measurable (G n)) (hGlim : Measurable Glim)
    (hnn : ∀ n ω, 0 ≤ G n ω)
    (hmonoω : ∀ n, ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → G n ω ≤ G n ω')
    (hflipmono : ∀ ω : Config V, Monotone fun n : ℕ => flipDiff (G n) e ω)
    (hincrmono : ∀ ω : Config V, Monotone fun n : ℕ => closedIncr (G n) e ω)
    (hflip : ∀ᵐ ω ∂(PercLib.Percolation.Bond.law π),
      (⨆ n : ℕ, ENNReal.ofReal (flipDiff (G n) e ω))
        = ENNReal.ofReal (flipDiff Glim e ω))
    (hincr : ∀ᵐ ω ∂(PercLib.Percolation.Bond.law π),
      (⨆ n : ℕ, ENNReal.ofReal (closedIncr (G n) e ω))
        = ENNReal.ofReal (closedIncr Glim e ω))
    (hflipnn : ∀ᵐ ω ∂(PercLib.Percolation.Bond.law π), 0 ≤ flipDiff Glim e ω)
    (hincrnn : ∀ᵐ ω ∂(PercLib.Percolation.Bond.law π), 0 ≤ closedIncr Glim e ω) :
    (1 - (π e : ℝ)) * pivotalFlux (PercLib.Percolation.Bond.law π) Glim e
      = ∫ ω, closedIncr Glim e ω ∂(PercLib.Percolation.Bond.law π) := by
  classical
  have hmain := ofReal_one_sub_mul_lintegral_flipDiff_eq_of_mono π e hG hnn hmonoω
    hflipmono hincrmono hflip hincr
  have hflipI : ∫ ω, flipDiff Glim e ω ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, ENNReal.ofReal (flipDiff Glim e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hflipnn
      (measurable_flipDiff hGlim e).aestronglyMeasurable
  have hincrI : ∫ ω, closedIncr Glim e ω ∂(PercLib.Percolation.Bond.law π)
      = (∫⁻ ω, ENNReal.ofReal (closedIncr Glim e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hincrnn
      (measurable_closedIncr hGlim e).aestronglyMeasurable
  have hq : (0 : ℝ) ≤ 1 - (π e : ℝ) := by
    have h := (π e).2.2; linarith
  calc (1 - (π e : ℝ)) * pivotalFlux (PercLib.Percolation.Bond.law π) Glim e
      = (1 - (π e : ℝ)) * (∫ ω, flipDiff Glim e ω
          ∂(PercLib.Percolation.Bond.law π)) := rfl
    _ = (1 - (π e : ℝ)) * (∫⁻ ω, ENNReal.ofReal (flipDiff Glim e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal := by rw [hflipI]
    _ = (ENNReal.ofReal (1 - (π e : ℝ))).toReal
          * (∫⁻ ω, ENNReal.ofReal (flipDiff Glim e ω)
              ∂(PercLib.Percolation.Bond.law π)).toReal := by
        rw [ENNReal.toReal_ofReal hq]
    _ = (ENNReal.ofReal (1 - (π e : ℝ))
          * (∫⁻ ω, ENNReal.ofReal (flipDiff Glim e ω)
              ∂(PercLib.Percolation.Bond.law π))).toReal := (ENNReal.toReal_mul).symm
    _ = (∫⁻ ω, ENNReal.ofReal (closedIncr Glim e ω)
          ∂(PercLib.Percolation.Bond.law π)).toReal := by rw [hmain]
    _ = ∫ ω, closedIncr Glim e ω ∂(PercLib.Percolation.Bond.law π) := hincrI.symm

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.min_sub_min_eq
#print axioms PercLib.CriticalLRP.Orchestration.iSup_ofReal_flipDiff_levelTrunc
#print axioms PercLib.CriticalLRP.Orchestration.iSup_ofReal_closedIncr_levelTrunc
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_one_sub_mul_lintegral_flipDiff_levelTrunc
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_one_sub_mul_lintegral_flipDiff_eq
#print axioms PercLib.CriticalLRP.Orchestration.one_sub_mul_pivotalFlux_eq_of_monotone
#print axioms PercLib.CriticalLRP.Orchestration.clusterVolCap_mono
#print axioms PercLib.CriticalLRP.Orchestration.cap_sq_sub_monotone
#print axioms PercLib.CriticalLRP.Orchestration.toReal_inf_nat_sub_monotone
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_one_sub_mul_lintegral_flipDiff_eq_of_mono
#print axioms PercLib.CriticalLRP.Orchestration.one_sub_mul_pivotalFlux_eq_of_mono
