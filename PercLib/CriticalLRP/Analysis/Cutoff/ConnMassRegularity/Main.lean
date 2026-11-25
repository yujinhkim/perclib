/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity
public import PercLib.CriticalLRP.Analysis.Cutoff.ConnMassRegularity.Defs

/-!
# Radius regularity of the connected window mass `connMass`

Landed at HEAD: `E1Sign.connMass_eq_mark` identifies

`connMass M r = ∫⁻ u, |K_r(u)|² · ∑_{y ∈ B_r} 1(y ∈ K_r(u)) dμ(u)`

on the common mark space, `E1Sign.connMass_mono` gives monotonicity in `r`, and
`SourceModelData.cutMoment` supplies the `p`-th cluster moment.  What was *not* known is any
regularity of `r ↦ connMass M r`: unlike `cutMoment`, the window `B_r = {ρ ≤ r}` itself moves
with `r`.

This file proves:

* `connMass_le_cutMoment_three` — `connMass M r ≤ M.cutMoment 3 r` (the window count is at
  most `|K_r|`), so finiteness of the third moment bounds `connMass`;
* `tendsto_connMassReal_nhdsGT` — **continuity from above** at every `r₀ > 0` from finiteness
  of the third moment at one strictly larger radius `r₁ > r₀`; the proof decomposes the moving
  window into `B_{r₀}` plus the annulus `B_r \ B_{r₀}` and controls the box-change/escape
  events exactly as in the landed `cutMoment` proof;
* `iSup_connMass_nat` — for `r n ↑ r₀` the *strict-window* mass `connMassLt` is the genuine
  supremum `⨆ n connMass M (r n)` (monotone convergence on the mark space);
* `tendsto_connMassReal_nhdsLT` — consequently `connMass` has a left limit, equal to
  `connMassLt M r₀`;
* `connMass_eq_connMassLt_add_sphereMass` — the exact decomposition
  `connMass M r₀ = connMassLt M r₀ + sphereMass M r₀`, and left continuity when that
  sphere layer vanishes;
* `tendsto_connMassReal_nhdsLT_of_no_sphere` — left continuity at every radius at which no
  lattice point lies on the sphere `{ρ = r₀}`;
* `continuousAt_connMassReal` — two-sided continuity at those radii (and, unconditionally,
  right continuity everywhere).

The sphere layer is a genuine obstruction: the window `B_r` is closed, so as `r ↑ r₀` the
sites with `ρ = r₀` are never counted, while `connMass M r₀` does count them.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/



set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## Measurability and the basic comparison with the third moment -/

theorem measurable_connMarkFun (r : ℝ) : Measurable (M.connMarkFun r) := by
  have hsum : Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y :=
    Finset.measurable_sum _ fun y _ =>
      measurable_const.indicator
        ((measurableSet_cluster_mem (0 : M.V) y).preimage (measurable_atParameter _))
  exact ((M.measurable_markVol r).pow_const 2).mul hsum

theorem measurable_connAnnulusFun (r0 r : ℝ) : Measurable (M.connAnnulusFun r0 r) := by
  have hsum : Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ (E1Sign.ballF M r).filter (fun y => y ∉ E1Sign.ballF M r0),
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y :=
    Finset.measurable_sum _ fun y _ =>
      measurable_const.indicator
        ((measurableSet_cluster_mem (0 : M.V) y).preimage (measurable_atParameter _))
  exact ((M.measurable_markVol r0).pow_const 2).mul hsum

theorem connMass_eq_lintegral_connMarkFun (r : ℝ) :
    E1Sign.connMass M r = ∫⁻ u, M.connMarkFun r u ∂(markMeasure M.V) :=
  E1Sign.connMass_eq_mark M r

/-- The window count is bounded by the cluster volume, hence `connMass ≤ cutMoment 3`. -/
theorem connMass_le_cutMoment_three (r : ℝ) :
    E1Sign.connMass M r ≤ M.cutMoment 3 r := by
  rw [M.connMass_eq_lintegral_connMarkFun, M.cutMoment_eq_mark 3 r]
  refine lintegral_mono fun u => ?_
  have hN : (∑ y ∈ E1Sign.ballF M r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y) ≤ M.markVol r u := by
    have hcl : (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
        ≤ ∑' y : M.V,
          (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y :=
      ENNReal.sum_le_tsum (E1Sign.ballF M r)
    rw [show M.markVol r u = ∑' y : M.V,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y from clusterVol_eq_tsum _ _]
    exact hcl
  calc (M.markVol r u) ^ 2 *
        ∑ y ∈ E1Sign.ballF M r,
          (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y
      ≤ (M.markVol r u) ^ 2 * M.markVol r u := by gcongr
    _ = (M.markVol r u) ^ 3 := by ring

/-- The per-mark integrand is monotone in the radius. -/
theorem connMarkFun_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    M.connMarkFun r ≤ M.connMarkFun r' := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  intro u
  have hvol : M.markVol r u ≤ M.markVol r' u :=
    M.clusterVol_atParameter_mono hr hr' hrr' u (0 : M.V)
  have hcl : cluster (atParameter (M.cutProb r) u) (0 : M.V) ⊆
      cluster (atParameter (M.cutProb r') u) (0 : M.V) :=
    cluster_mono (fun e he =>
      lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr' hrr' e))) 0
  have hsum1 : (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
      ≤ ∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y := by
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hy : y ∈ cluster (atParameter (M.cutProb r) u) (0 : M.V)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hcl hy)]
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  have hsum2 : (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
      ≤ ∑ y ∈ E1Sign.ballF M r',
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro y hy
      rw [E1Sign.mem_ballF] at hy ⊢
      exact BallAverage.ball_mono M hrr' hy
    · intro y _ _; exact zero_le
  exact mul_le_mul' (pow_le_pow_left' hvol 2) (le_trans hsum1 hsum2)

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The pointwise increment bound for the moving window

For `r₀ ≤ r ≤ r₁` the window `B_r` is `B_{r₀}` plus the annulus `B_r \ B_{r₀}`.  Off the
box-change and escape events the `r`-cluster equals the `r₀`-cluster, so the only new
contribution is the annulus; on those events the integrand is dominated by `|K_{r₁}|³`. -/

theorem connMarkFun_le_add {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hrr : r0 ≤ r) (hr1 : r ≤ r1)
    (u : Sym2 M.V → ℝ) :
    M.connMarkFun r u ≤
      M.connMarkFun r0 u + M.connAnnulusFun r0 r u +
        (M.markBoxChange r0 r R).indicator (fun u => (M.markVol r1 u) ^ 3) u +
        (M.markEscape r1 R).indicator (fun u => (M.markVol r1 u) ^ 3) u := by
  have hN : ∀ s : ℝ, (∑ y ∈ E1Sign.ballF M s,
      (cluster (atParameter (M.cutProb s) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y) ≤ M.markVol s u := by
    intro s
    have hcl : (∑ y ∈ E1Sign.ballF M s,
        (cluster (atParameter (M.cutProb s) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
        ≤ ∑' y : M.V,
          (cluster (atParameter (M.cutProb s) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y :=
      ENNReal.sum_le_tsum (E1Sign.ballF M s)
    rw [show M.markVol s u = ∑' y : M.V,
        (cluster (atParameter (M.cutProb s) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y from clusterVol_eq_tsum _ _]
    exact hcl
  have hcube : ∀ s : ℝ, M.connMarkFun s u ≤ (M.markVol s u) ^ 3 := by
    intro s
    have := hN s
    calc M.connMarkFun s u
        = (M.markVol s u) ^ 2 * (∑ y ∈ E1Sign.ballF M s,
            (cluster (atParameter (M.cutProb s) u) (0 : M.V)).indicator
              (fun _ => (1 : ℝ≥0∞)) y) := rfl
      _ ≤ (M.markVol s u) ^ 2 * M.markVol s u := by gcongr
      _ = (M.markVol s u) ^ 3 := by ring
  by_cases hbox : u ∈ M.markBoxChange r0 r R
  · rw [Set.indicator_of_mem hbox]
    have h1 : M.connMarkFun r u ≤ (M.markVol r u) ^ 3 := hcube r
    have h2 : (M.markVol r u) ^ 3 ≤ (M.markVol r1 u) ^ 3 :=
      pow_le_pow_left' (M.clusterVol_atParameter_mono (lt_of_lt_of_le hr0 hrr)
        (lt_of_lt_of_le (lt_of_lt_of_le hr0 hrr) hr1) hr1 u 0) 3
    calc M.connMarkFun r u
        ≤ (M.markVol r1 u) ^ 3 := le_trans h1 h2
      _ ≤ M.connMarkFun r0 u + M.connAnnulusFun r0 r u + (M.markVol r1 u) ^ 3 :=
          le_add_self
      _ ≤ M.connMarkFun r0 u + M.connAnnulusFun r0 r u + (M.markVol r1 u) ^ 3 +
            (M.markEscape r1 R).indicator (fun u => (M.markVol r1 u) ^ 3) u := le_self_add
  · rw [Set.indicator_of_notMem hbox]
    by_cases hesc : u ∈ M.markEscape r1 R
    · rw [Set.indicator_of_mem hesc]
      have h1 : M.connMarkFun r u ≤ (M.markVol r u) ^ 3 := hcube r
      have h2 : (M.markVol r u) ^ 3 ≤ (M.markVol r1 u) ^ 3 :=
        pow_le_pow_left' (M.clusterVol_atParameter_mono (lt_of_lt_of_le hr0 hrr)
        (lt_of_lt_of_le (lt_of_lt_of_le hr0 hrr) hr1) hr1 u 0) 3
      calc M.connMarkFun r u
          ≤ (M.markVol r1 u) ^ 3 := le_trans h1 h2
        _ ≤ M.connMarkFun r0 u + M.connAnnulusFun r0 r u + (M.markVol r1 u) ^ 3 :=
            le_add_self
        _ = M.connMarkFun r0 u + M.connAnnulusFun r0 r u + 0 + (M.markVol r1 u) ^ 3 := by
            rw [add_zero]
    · rw [Set.indicator_of_notMem hesc]
      have hesc' : u ∉ M.markEscape r R := fun h =>
        hesc (M.markEscape_mono (lt_of_lt_of_le hr0 hrr)
          (lt_of_lt_of_le (lt_of_lt_of_le hr0 hrr) hr1) hr1 h)
      have hV : M.markVol r u = M.markVol r0 u :=
        le_antisymm (M.clusterVol_le_of_notMem hbox hesc')
          (M.clusterVol_atParameter_mono hr0 (lt_of_lt_of_le hr0 hrr) hrr u 0)
      have hC : cluster (atParameter (M.cutProb r) u) (0 : M.V) =
          cluster (atParameter (M.cutProb r0) u) (0 : M.V) := by
        refine le_antisymm ?_ ?_
        · refine M.cluster_subset_of_eq_on_box (R := R) ?_ ?_
          · intro e he hmem
            exact M.lt_cutProb_r0_of_notMem_markBoxChange hbox he hmem
          · intro y hy
            by_contra hcon
            exact hesc' ⟨y, hcon, mem_cluster_iff.mpr hy⟩
        · exact cluster_mono (fun e he => lt_of_lt_of_le he
            (Subtype.coe_le_coe.mpr (M.cutProb_mono hr0 (lt_of_lt_of_le hr0 hrr) hrr e))) 0
      have hsub : E1Sign.ballF M r0 ⊆ E1Sign.ballF M r := by
        intro y hy
        rw [E1Sign.mem_ballF] at hy ⊢
        exact BallAverage.ball_mono M hrr hy
      have hsplit := Finset.sum_sdiff (s₁ := E1Sign.ballF M r0) (s₂ := E1Sign.ballF M r)
        (f := fun y => (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y) hsub
      simp only [add_zero]
      simp only [SourceModelData.connMarkFun, SourceModelData.connAnnulusFun, hV, hC]
      rw [← hsplit, Finset.sdiff_eq_filter, mul_add, add_comm]

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Integrated increment bound.**  For `0 < r₀ ≤ r ≤ r₁` the connected mass at `r` exceeds the
one at `r₀` by at most the annulus mass plus the `r₁`-clusters integrated over the box-change and
escape marks.  This is the moving-window analogue of the landed `cutMoment_le_add`. -/
theorem connMass_le_add {r0 r r1 R : ℝ} (hr0 : 0 < r0) (hrr : r0 ≤ r) (hr1 : r ≤ r1) :
    E1Sign.connMass M r ≤ E1Sign.connMass M r0 + M.connAnnulusMass r0 r +
      (∫⁻ u in M.markBoxChange r0 r R, (M.markVol r1 u) ^ 3 ∂(markMeasure M.V)) +
      (∫⁻ u in M.markEscape r1 R, (M.markVol r1 u) ^ 3 ∂(markMeasure M.V)) := by
  have hmono : ∫⁻ u, M.connMarkFun r u ∂(markMeasure M.V) ≤
      ∫⁻ u, (M.connMarkFun r0 u + M.connAnnulusFun r0 r u +
        (M.markBoxChange r0 r R).indicator (fun u => (M.markVol r1 u) ^ 3) u +
        (M.markEscape r1 R).indicator (fun u => (M.markVol r1 u) ^ 3) u)
        ∂(markMeasure M.V) :=
    lintegral_mono fun u => M.connMarkFun_le_add hr0 hrr hr1 u
  have h12 : Measurable fun u : Sym2 M.V → ℝ =>
      M.connMarkFun r0 u + M.connAnnulusFun r0 r u :=
    (M.measurable_connMarkFun r0).add (M.measurable_connAnnulusFun r0 r)
  have h123 : Measurable fun u : Sym2 M.V → ℝ =>
      M.connMarkFun r0 u + M.connAnnulusFun r0 r u +
        (M.markBoxChange r0 r R).indicator (fun u => (M.markVol r1 u) ^ 3) u :=
    h12.add (((M.measurable_markVol r1).pow_const 3).indicator
      (M.measurableSet_markBoxChange r0 r R))
  rw [lintegral_add_left h123, lintegral_add_left h12,
    lintegral_add_left (M.measurable_connMarkFun r0),
    lintegral_indicator (M.measurableSet_markBoxChange r0 r R)
      (fun u => (M.markVol r1 u) ^ 3),
    lintegral_indicator (M.measurableSet_markEscape r1 R)
      (fun u => (M.markVol r1 u) ^ 3)] at hmono
  rw [show E1Sign.connMass M r = ∫⁻ u, M.connMarkFun r u ∂(markMeasure M.V) from
      M.connMass_eq_lintegral_connMarkFun r,
    show E1Sign.connMass M r0 = ∫⁻ u, M.connMarkFun r0 u ∂(markMeasure M.V) from
      M.connMass_eq_lintegral_connMarkFun r0]
  simpa [SourceModelData.connAnnulusMass] using hmono

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The annulus mass is monotone and bounded by the third moment -/

theorem connAnnulusFun_mono {r0 r r' : ℝ} (hrr' : r ≤ r') :
    M.connAnnulusFun r0 r ≤ M.connAnnulusFun r0 r' := by
  intro u
  have hsub : (E1Sign.ballF M r).filter (fun y => y ∉ E1Sign.ballF M r0) ⊆
      (E1Sign.ballF M r').filter (fun y => y ∉ E1Sign.ballF M r0) := by
    refine Finset.filter_subset_filter _ ?_
    intro y hy
    rw [E1Sign.mem_ballF] at hy ⊢
    exact BallAverage.ball_mono M hrr' hy
  exact mul_le_mul' le_rfl
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le))

theorem connAnnulusMass_mono {r0 r r' : ℝ} (hrr' : r ≤ r') :
    M.connAnnulusMass r0 r ≤ M.connAnnulusMass r0 r' :=
  lintegral_mono fun u => M.connAnnulusFun_mono hrr' u

theorem connAnnulusFun_le_cube (r0 r : ℝ) (u : Sym2 M.V → ℝ) :
    M.connAnnulusFun r0 r u ≤ (M.markVol r0 u) ^ 3 := by
  have hN : (∑ y ∈ (E1Sign.ballF M r).filter (fun y => y ∉ E1Sign.ballF M r0),
      (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y) ≤ M.markVol r0 u := by
    have hcl : (∑ y ∈ (E1Sign.ballF M r).filter (fun y => y ∉ E1Sign.ballF M r0),
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
        ≤ ∑' y : M.V,
          (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y :=
      ENNReal.sum_le_tsum _
    rw [show M.markVol r0 u = ∑' y : M.V,
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y from clusterVol_eq_tsum _ _]
    exact hcl
  calc M.connAnnulusFun r0 r u
      = (M.markVol r0 u) ^ 2 * (∑ y ∈ (E1Sign.ballF M r).filter
          (fun y => y ∉ E1Sign.ballF M r0),
          (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y) := rfl
    _ ≤ (M.markVol r0 u) ^ 2 * M.markVol r0 u := by gcongr
    _ = (M.markVol r0 u) ^ 3 := by ring

theorem connAnnulusMass_le_cutMoment_three {r0 r : ℝ} :
    M.connAnnulusMass r0 r ≤ M.cutMoment 3 r0 := by
  rw [SourceModelData.connAnnulusMass, M.cutMoment_eq_mark 3 r0]
  exact lintegral_mono fun u => M.connAnnulusFun_le_cube r0 r u

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The annulus mass tends to zero from above

As `r ↓ r₀` the annulus `B_r \ B_{r₀}` shrinks to the empty set *as a set of lattice points*:
any fixed lattice point with `ρ > r₀` is eventually outside `B_r`, and points with `ρ ≤ r₀`
were never in the difference.  Since the annulus sum only counts lattice points of the fixed
finite set `B_{r₀ + 1}`, it eventually vanishes pointwise on the mark space, and the antitone
monotone convergence theorem for `lintegral` yields the limit. -/

theorem tendsto_connAnnulusMass_toReal (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.cutMoment 3 r0 ≠ ⊤) :
    Tendsto (fun r => (M.connAnnulusMass r0 r).toReal) (𝓝[>] r0) (𝓝 0) := by
  set rseq : ℕ → ℝ := fun n => r0 + r0 / ((n : ℝ) + 2) with hrseq
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hrpos : ∀ n : ℕ, r0 < rseq n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : 0 < r0 / ((n : ℝ) + 2) := div_pos hr0 h1
    simp only [hrseq]
    linarith
  have hdec : Antitone rseq := by
    intro n m hnm
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have hcast : ((n : ℝ) + 2) ≤ ((m : ℝ) + 2) := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    simp only [hrseq]
    have h3 : r0 / ((m : ℝ) + 2) ≤ r0 / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr0.le h1 hcast
    linarith
  have hlim : Tendsto rseq atTop (𝓝 r0) := by
    have h0 : Tendsto (fun n : ℕ => r0 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop h1
    simp only [hrseq]
    simpa using tendsto_const_nhds.add h0
  have hantiFinset : Antitone fun n : ℕ =>
      (E1Sign.ballF M (rseq n)).filter (fun y => y ∉ E1Sign.ballF M r0) := by
    intro n m hnm
    refine Finset.filter_subset_filter _ ?_
    intro y hy
    rw [E1Sign.mem_ballF] at hy ⊢
    exact le_trans hy (hdec hnm)
  have hpt : ∀ u : Sym2 M.V → ℝ, (⨅ n, M.connAnnulusFun r0 (rseq n) u) = 0 := by
    intro u
    have hex : ∀ y ∈ E1Sign.ballF M (rseq 0),
        ∃ n, y ∉ (E1Sign.ballF M (rseq n)).filter (fun y => y ∉ E1Sign.ballF M r0) := by
      intro y hy
      by_cases hmem : y ∈ E1Sign.ballF M r0
      · exact ⟨0, fun h => (Finset.mem_filter.mp h).2 hmem⟩
      · have hlt : r0 < M.S.ρ (toVec y) := by
          rw [E1Sign.mem_ballF] at hmem
          exact lt_of_not_ge hmem
        obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds hlt))
        refine ⟨N, fun h => ?_⟩
        have h1 : y ∈ E1Sign.ballF M (rseq N) := (Finset.mem_filter.mp h).1
        rw [E1Sign.mem_ballF] at h1
        exact absurd h1 (not_le.mpr (hN N le_rfl))
    classical
    let gg : {y // y ∈ E1Sign.ballF M (rseq 0)} → ℕ := fun y => Classical.choose (hex y.1 y.2)
    have hgg : ∀ (y : M.V) (hy : y ∈ E1Sign.ballF M (rseq 0)),
        y ∉ (E1Sign.ballF M (rseq (gg ⟨y, hy⟩))).filter
          (fun y => y ∉ E1Sign.ballF M r0) :=
      fun y hy => Classical.choose_spec (hex y hy)
    have hzero : ∀ n ≥ (E1Sign.ballF M (rseq 0)).attach.sup gg,
        M.connAnnulusFun r0 (rseq n) u = 0 := by
      intro n hn
      have hsubF : (E1Sign.ballF M (rseq n)).filter (fun y => y ∉ E1Sign.ballF M r0) ⊆
          E1Sign.ballF M (rseq 0) := by
        refine Finset.Subset.trans (Finset.filter_subset _ _) ?_
        intro y hy
        rw [E1Sign.mem_ballF] at hy ⊢
        exact le_trans hy (hdec (Nat.zero_le n))
      have hempty : (E1Sign.ballF M (rseq n)).filter (fun y => y ∉ E1Sign.ballF M r0) = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨y, hy⟩
        have hyF : y ∈ E1Sign.ballF M (rseq 0) := hsubF hy
        have h1 : gg ⟨y, hyF⟩ ≤ (E1Sign.ballF M (rseq 0)).attach.sup gg :=
          Finset.le_sup (f := gg) (Finset.mem_attach _ ⟨y, hyF⟩)
        have h2 := hgg y hyF
        exact h2 (hantiFinset (h1.trans hn) hy)
      simp only [SourceModelData.connAnnulusFun, hempty, Finset.sum_empty, mul_zero]
    exact le_antisymm
      ((iInf_le (fun n => M.connAnnulusFun r0 (rseq n) u)
        ((E1Sign.ballF M (rseq 0)).attach.sup gg)).trans_eq (hzero _ le_rfl)) zero_le
  have hanti : Antitone fun n : ℕ => M.connAnnulusFun r0 (rseq n) :=
    fun n m hnm => M.connAnnulusFun_mono (hdec hnm)
  have hantiMass : Antitone fun n : ℕ => M.connAnnulusMass r0 (rseq n) :=
    fun n m hnm => M.connAnnulusMass_mono (hdec hnm)
  have hfin0 : M.connAnnulusMass r0 (rseq 0) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin M.connAnnulusMass_le_cutMoment_three
  have hInf : (⨅ n, M.connAnnulusMass r0 (rseq n)) = 0 := by
    have h := lintegral_iInf (μ := markMeasure M.V)
      (fun n => M.measurable_connAnnulusFun r0 (rseq n)) hanti hfin0
    have hz : (∫⁻ u, ⨅ n, M.connAnnulusFun r0 (rseq n) u ∂(markMeasure M.V)) = 0 := by
      simp only [hpt, lintegral_zero]
    rw [hz] at h
    simpa only [SourceModelData.connAnnulusMass] using h.symm
  have hseq : Tendsto (fun n => M.connAnnulusMass r0 (rseq n)) atTop (𝓝 0) := by
    simpa only [hInf] using tendsto_atTop_iInf hantiMass
  have hreal : Tendsto (fun n => (M.connAnnulusMass r0 (rseq n)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hseq
    simpa [Function.comp_def] using h
  refine tendsto_zero_of_le_seq (g := fun r => (M.connAnnulusMass r0 r).toReal)
    (r := rseq) ?_ ?_ hrpos hreal
  · intro x y hx hxy
    exact ENNReal.toReal_mono
      (ne_top_of_le_ne_top hfin M.connAnnulusMass_le_cutMoment_three)
      (M.connAnnulusMass_mono hxy)
  · intro x
    exact ENNReal.toReal_nonneg

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## Continuity from above of the connected window mass

The proof follows the landed `cutMoment` proof, with the annulus term added.  The three error
terms are: the annulus `B_r \ B_{r₀}` (handled by monotone convergence on the mark space), the
box-change marks inside a fixed box (handled by the landed `tendsto_boxIntegral_pow`), and the
escape marks outside that box (handled by the landed shrinking-set lemma). -/

theorem tendsto_connMassReal_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (hfin : M.cutMoment 3 r1 ≠ ⊤) :
    Tendsto (fun r => (E1Sign.connMass M r).toReal) (𝓝[>] r0)
      (𝓝 ((E1Sign.connMass M r0).toReal)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hfin0 : M.cutMoment 3 r0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.cutMoment_monotone 3 hr1.le)
  have hInt : (∫⁻ a, (M.markVol r1 a) ^ 3 ∂(markMeasure M.V)) = M.cutMoment 3 r1 :=
    (M.cutMoment_eq_mark 3 r1).symm
  -- escape tail
  have hesc_tend : Tendsto (fun n : ℕ => (∫⁻ u in M.markEscape r1 (n : ℝ),
      (M.markVol r1 u) ^ 3 ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
    tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V)
      ((M.measurable_markVol r1).pow_const 3) (by rw [hInt]; exact hfin)
      (fun n => M.measurableSet_markEscape r1 (n : ℝ))
      (fun n m hnm => M.markEscape_antitone (by exact_mod_cast hnm))
      (M.measure_iInter_markEscape_zero_of_pow (p := 3) (by norm_num) r1 hfin)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hesc_tend) (ε / 3) (by linarith)
  have hN' : (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ 3
      ∂(markMeasure M.V)).toReal < ε / 3 := by
    have h := hN N le_rfl
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h
  -- box-change error
  have hbox := M.tendsto_boxIntegral_pow 3 r0 hr0 hr1 hfin (N : ℝ)
  obtain ⟨δ, hδ, hspec⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hbox) (ε / 3) (by linarith)
  -- annulus error
  have hann := M.tendsto_connAnnulusMass_toReal r0 hr0 hfin0
  obtain ⟨δ2, hδ2, hspec2⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hann) (ε / 3) (by linarith)
  refine ⟨min (min δ δ2) (r1 - r0), lt_min (lt_min hδ hδ2) (by linarith), ?_⟩
  intro r hr hdist
  rw [Real.dist_eq] at hdist ⊢
  have hr1' : r ≤ r1 := by
    rw [abs_lt] at hdist
    linarith [hdist.2, min_le_right (min δ δ2) (r1 - r0)]
  have hrpos : 0 < r := lt_trans hr0 hr
  have hboxsmall : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ 3
      ∂(markMeasure M.V)).toReal < ε / 3 := by
    have h2 : dist (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ 3
        ∂(markMeasure M.V)).toReal 0 < ε / 3 := by
      refine hspec hr ?_
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_left _ _))
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h2
  have hannsmall : (M.connAnnulusMass r0 r).toReal < ε / 3 := by
    have h2 : dist (M.connAnnulusMass r0 r).toReal 0 < ε / 3 := by
      refine hspec2 hr ?_
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_right _ _))
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h2
  -- finiteness of every term
  have hfr : E1Sign.connMass M r ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (le_trans (M.connMass_le_cutMoment_three r)
      (M.cutMoment_monotone 3 (a := r) hr1'))
  have hfr0 : E1Sign.connMass M r0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (le_trans (M.connMass_le_cutMoment_three r0)
      (M.cutMoment_monotone 3 hr1.le))
  have hannfin : M.connAnnulusMass r0 r ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (le_trans M.connAnnulusMass_le_cutMoment_three
      (M.cutMoment_monotone 3 hr1.le))
  have hUniv : (∫⁻ u : Sym2 M.V → ℝ, (M.markVol r1 u) ^ 3 ∂(markMeasure M.V)) ≠ ⊤ := by
    rw [hInt]
    exact hfin
  have hboxfin : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ 3
      ∂(markMeasure M.V)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hUniv ?_
    have hle := lintegral_mono_set (μ := markMeasure M.V) (f := fun u => (M.markVol r1 u) ^ 3)
      (s := M.markBoxChange r0 r (N : ℝ)) (Set.subset_univ _)
    rwa [Measure.restrict_univ] at hle
  have hescfin : (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ 3
      ∂(markMeasure M.V)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hUniv ?_
    have hle := lintegral_mono_set (μ := markMeasure M.V) (f := fun u => (M.markVol r1 u) ^ 3)
      (s := M.markEscape r1 (N : ℝ)) (Set.subset_univ _)
    rwa [Measure.restrict_univ] at hle
  have hsum : E1Sign.connMass M r0 + M.connAnnulusMass r0 r +
      (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ 3 ∂(markMeasure M.V)) +
      (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ 3 ∂(markMeasure M.V)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hfr0, hannfin⟩, hboxfin⟩, hescfin⟩
  have hincr := M.connMass_le_add hr0 hr.le hr1' (R := (N : ℝ))
  have hreal : (E1Sign.connMass M r).toReal ≤ (E1Sign.connMass M r0).toReal +
      (M.connAnnulusMass r0 r).toReal +
      (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ 3
        ∂(markMeasure M.V)).toReal +
      (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ 3
        ∂(markMeasure M.V)).toReal := by
    have h := ENNReal.toReal_mono hsum hincr
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hfr0, hannfin⟩, hboxfin⟩) hescfin,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfr0, hannfin⟩) hboxfin,
      ENNReal.toReal_add hfr0 hannfin] at h
  have hmono : (E1Sign.connMass M r0).toReal ≤ (E1Sign.connMass M r).toReal :=
    ENNReal.toReal_mono hfr (E1Sign.connMass_mono M hr0 hr.le)
  rw [abs_of_nonneg (by linarith)]
  linarith

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

/-! ## Left limit: monotone convergence to the strict-window mass -/

/-- A finite sum of indicators is the cardinality of the filtered finset. -/
theorem sum_indicator_eq_card {V : Type*} {s : Finset V} {C : Set V}
    [DecidablePred (fun y => y ∈ C)] :
    (∑ y ∈ s, (C.indicator (fun _ => (1 : ℝ≥0∞))) y)
      = ((s.filter (fun y => y ∈ C)).card : ℝ≥0∞) := by
  classical
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  simp

/-- For monotone `ℝ≥0∞`-sequences the product of the suprema is the supremum of the products. -/
theorem iSup_mul_iSup_nat {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n * b n) = (⨆ n, a n) * (⨆ n, b n) := by
  refine le_antisymm (iSup_le fun n => mul_le_mul' (le_iSup a n) (le_iSup b n)) ?_
  rw [ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  calc a n * b m ≤ a (max n m) * b (max n m) :=
        mul_le_mul' (ha (le_max_left n m)) (hb (le_max_right n m))
    _ ≤ ⨆ k, a k * b k := le_iSup (fun k => a k * b k) (max n m)

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Pointwise exhaustion of the strict window.**  For `r n ↑ r₀` the window sums over
`B_{r n}` increase to the sum over the strict window `{ρ < r₀}`. -/
theorem iSup_windowSum {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n) (hlt : ∀ n, r n < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0))
    (u : Sym2 M.V → ℝ) :
    (⨆ n, ∑ y ∈ E1Sign.ballF M (r n),
      (cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y)
      = ∑ y ∈ M.ballFLt r0,
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y := by
  classical
  have hr0 : 0 < r0 := lt_trans (hpos 0) (hlt 0)
  have hmonoProb : ∀ (n : ℕ) (e : Sym2 M.V),
      M.cutProb (r n) e ≤ M.cutProb (r (n + 1)) e :=
    fun n e => M.cutProb_mono (hpos n) (hpos (n + 1)) (hmono n) e
  have hlimProb : ∀ e : Sym2 M.V,
      Tendsto (fun n : ℕ => ((M.cutProb (r n) e : unitInterval) : ℝ)) atTop
        (𝓝 ((M.cutProb r0 e : unitInterval) : ℝ)) :=
    fun e => (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim
  have hmono_le : ∀ n m : ℕ, n ≤ m → r n ≤ r m := monotone_nat_of_le_succ hmono
  have hcl : ∀ n, cluster (atParameter (M.cutProb (r n)) u) (0 : M.V) ⊆
      cluster (atParameter (M.cutProb r0) u) (0 : M.V) :=
    fun n => cluster_mono (fun e he => lt_of_lt_of_le he
      (Subtype.coe_le_coe.mpr (M.cutProb_mono (hpos n) hr0 (le_of_lt (hlt n)) e))) 0
  have hsub : ∀ n, E1Sign.ballF M (r n) ⊆ M.ballFLt r0 := by
    intro n y hy
    rw [E1Sign.mem_ballF] at hy
    exact M.mem_ballFLt.mpr (lt_of_le_of_lt hy (hlt n))
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · calc (∑ y ∈ E1Sign.ballF M (r n),
        (cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
        ≤ ∑ y ∈ E1Sign.ballF M (r n),
          (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
          refine Finset.sum_le_sum fun y _ => ?_
          by_cases hy : y ∈ cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hcl n hy)]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ ≤ ∑ y ∈ M.ballFLt r0,
          (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y :=
          Finset.sum_le_sum_of_subset_of_nonneg (hsub n) (fun _ _ _ => zero_le)
  · set T := (M.ballFLt r0).filter
      (fun y => y ∈ cluster (atParameter (M.cutProb r0) u) (0 : M.V)) with hT
    have hS : (∑ y ∈ M.ballFLt r0,
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y) = (T.card : ℝ≥0∞) := by
      rw [sum_indicator_eq_card (C := cluster (atParameter (M.cutProb r0) u) (0 : M.V))]
    rw [hS]
    have hex : ∀ y ∈ T, ∃ n, y ∈ E1Sign.ballF M (r n) ∧
        y ∈ cluster (atParameter (M.cutProb (r n)) u) (0 : M.V) := by
      intro y hy
      rw [hT, Finset.mem_filter] at hy
      obtain ⟨hyw, hyc⟩ := hy
      have hρ : M.S.ρ (toVec y) < r0 := M.mem_ballFLt.mp hyw
      obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hlim.eventually (Ioi_mem_nhds hρ))
      obtain ⟨N₂, hN₂⟩ := exists_connects_atParameter_of_connects hmonoProb hlimProb
        (mem_cluster_iff.mp hyc)
      refine ⟨max N₁ N₂, ?_, ?_⟩
      · rw [E1Sign.mem_ballF]
        exact le_of_lt (hN₁ _ (le_max_left _ _))
      · exact mem_cluster_iff.mpr (connects_mono (fun e he => lt_of_lt_of_le he
          (Subtype.coe_le_coe.mpr (M.cutProb_mono (hpos N₂) (hpos (max N₁ N₂))
            (hmono_le N₂ (max N₁ N₂) (le_max_right _ _)) e))) hN₂)
    let gg : {y // y ∈ T} → ℕ := fun y => Classical.choose (hex y.1 y.2)
    have hgg : ∀ (y : M.V) (hy : y ∈ T), y ∈ E1Sign.ballF M (r (gg ⟨y, hy⟩)) ∧
        y ∈ cluster (atParameter (M.cutProb (r (gg ⟨y, hy⟩))) u) (0 : M.V) :=
      fun y hy => Classical.choose_spec (hex y hy)
    have key : ∀ N ≥ T.attach.sup gg, (T.card : ℝ≥0∞) ≤
        ∑ y ∈ E1Sign.ballF M (r N),
          (cluster (atParameter (M.cutProb (r N)) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
      intro N hN
      have hTsub : T ⊆ (E1Sign.ballF M (r N)).filter
          (fun y => y ∈ cluster (atParameter (M.cutProb (r N)) u) (0 : M.V)) := by
        intro y hy
        obtain ⟨h1, h2⟩ := hgg y hy
        have hle : gg ⟨y, hy⟩ ≤ T.attach.sup gg :=
          Finset.le_sup (f := gg) (Finset.mem_attach _ ⟨y, hy⟩)
        have hleN : gg ⟨y, hy⟩ ≤ N := hle.trans hN
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [E1Sign.mem_ballF] at h1 ⊢
          exact le_trans h1 (hmono_le _ _ hleN)
        · rw [E1Sign.mem_ballF] at h1
          exact cluster_mono (fun e he => lt_of_lt_of_le he (Subtype.coe_le_coe.mpr
            (M.cutProb_mono (hpos _) (hpos N) (hmono_le _ _ hleN) e))) 0 h2
      have hcard : (T.card : ℝ≥0∞) ≤ ((E1Sign.ballF M (r N)).filter
          (fun y => y ∈ cluster (atParameter (M.cutProb (r N)) u) (0 : M.V))).card := by
        exact_mod_cast Finset.card_le_card hTsub
      have hcardEq : (((E1Sign.ballF M (r N)).filter
          (fun y => y ∈ cluster (atParameter (M.cutProb (r N)) u) (0 : M.V))).card : ℝ≥0∞)
          = ∑ y ∈ E1Sign.ballF M (r N),
            (cluster (atParameter (M.cutProb (r N)) u) (0 : M.V)).indicator
              (fun _ => (1 : ℝ≥0∞)) y := by
        rw [sum_indicator_eq_card]
      rw [hcardEq] at hcard
      exact hcard
    exact le_iSup_of_le (T.attach.sup gg) (key _ le_rfl)

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem measurable_connMarkFunLt (r : ℝ) : Measurable (M.connMarkFunLt r) := by
  have hsum : Measurable fun u : Sym2 M.V → ℝ =>
      ∑ y ∈ M.ballFLt r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y :=
    Finset.measurable_sum _ fun y _ =>
      measurable_const.indicator
        ((measurableSet_cluster_mem (0 : M.V) y).preimage (measurable_atParameter _))
  exact ((M.measurable_markVol r).pow_const 2).mul hsum

/-- **Pointwise supremum of the mark integrands** along `r n ↑ r₀`. -/
theorem iSup_connMarkFun_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) (u : Sym2 M.V → ℝ) :
    (⨆ n, M.connMarkFun (r n) u) = M.connMarkFunLt r0 u := by
  classical
  have hr0 : 0 < r0 := lt_trans (hpos 0) (hlt 0)
  have hmonoProb : ∀ (n : ℕ) (e : Sym2 M.V),
      M.cutProb (r n) e ≤ M.cutProb (r (n + 1)) e :=
    fun n e => M.cutProb_mono (hpos n) (hpos (n + 1)) (hmono n) e
  have hlimProb : ∀ e : Sym2 M.V,
      Tendsto (fun n : ℕ => ((M.cutProb (r n) e : unitInterval) : ℝ)) atTop
        (𝓝 ((M.cutProb r0 e : unitInterval) : ℝ)) :=
    fun e => (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim
  have hvol : (⨆ n, M.markVol (r n) u) = M.markVol r0 u :=
    (CutoffMomentTransfer.clusterVol_atParameter_eq_iSup hmonoProb hlimProb u 0).symm
  have hvol2 : (⨆ n, (M.markVol (r n) u) ^ 2) = (M.markVol r0 u) ^ 2 := by
    rw [← ENNReal.iSup_pow, hvol]
  have hsum := M.iSup_windowSum hpos hlt hmono hlim u
  have hmonoA : Monotone fun n => (M.markVol (r n) u) ^ 2 := fun n m hnm =>
    pow_le_pow_left' (M.clusterVol_atParameter_mono (hpos n) (hpos m)
      ((monotone_nat_of_le_succ hmono) hnm) u 0) 2
  have hmonoB : Monotone fun n => ∑ y ∈ E1Sign.ballF M (r n),
      (cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y := by
    intro n m hnm
    calc (∑ y ∈ E1Sign.ballF M (r n),
          (cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y)
        ≤ ∑ y ∈ E1Sign.ballF M (r n),
          (cluster (atParameter (M.cutProb (r m)) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
          refine Finset.sum_le_sum fun y _ => ?_
          by_cases hy : y ∈ cluster (atParameter (M.cutProb (r n)) u) (0 : M.V)
          · have hmem : y ∈ cluster (atParameter (M.cutProb (r m)) u) (0 : M.V) :=
              cluster_mono (fun e he => lt_of_lt_of_le he (Subtype.coe_le_coe.mpr
                (M.cutProb_mono (hpos n) (hpos m)
                  ((monotone_nat_of_le_succ hmono) hnm) e))) 0 hy
            rw [Set.indicator_of_mem hy, Set.indicator_of_mem hmem]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ ≤ ∑ y ∈ E1Sign.ballF M (r m),
          (cluster (atParameter (M.cutProb (r m)) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le)
          intro y hy
          rw [E1Sign.mem_ballF] at hy ⊢
          exact le_trans hy ((monotone_nat_of_le_succ hmono) hnm)
  simp only [SourceModelData.connMarkFun, SourceModelData.connMarkFunLt]
  rw [← hvol2, ← hsum]
  exact iSup_mul_iSup_nat hmonoA hmonoB

/-- **Monotone convergence to the strict-window mass.**  For `r n ↑ r₀` the connected masses at
`r n` increase to `connMassLt M r₀`, the mass computed with the strict window `{ρ < r₀}`. -/
theorem iSup_connMass_nat {r : ℕ → ℝ} {r0 : ℝ} (hpos : ∀ n, 0 < r n)
    (hlt : ∀ n, r n < r0) (hmono : ∀ n, r n ≤ r (n + 1))
    (hlim : Tendsto r atTop (𝓝 r0)) :
    (⨆ n, E1Sign.connMass M (r n)) = M.connMassLt r0 := by
  have hmeas : ∀ n, Measurable (M.connMarkFun (r n)) := fun n => M.measurable_connMarkFun (r n)
  have hmonoFun : Monotone fun n => M.connMarkFun (r n) := fun n m hnm =>
    M.connMarkFun_mono (hpos n) ((monotone_nat_of_le_succ hmono) hnm)
  have hstep := lintegral_iSup (μ := markMeasure M.V) hmeas hmonoFun
  have hptfun : (fun u => ⨆ n, M.connMarkFun (r n) u) = M.connMarkFunLt r0 :=
    funext fun u => M.iSup_connMarkFun_nat hpos hlt hmono hlim u
  rw [hptfun] at hstep
  rw [SourceModelData.connMassLt]
  simpa only [M.connMass_eq_lintegral_connMarkFun] using hstep.symm

/-- The connected mass at a radius strictly below `r₀` is at most the strict-window mass at
`r₀`. -/
theorem connMass_le_connMassLt {r r0 : ℝ} (hr : 0 < r) (hrr : r < r0) :
    E1Sign.connMass M r ≤ M.connMassLt r0 := by
  have hr0 : 0 < r0 := lt_trans hr hrr
  rw [M.connMass_eq_lintegral_connMarkFun, SourceModelData.connMassLt]
  refine lintegral_mono fun u => ?_
  have hvol : M.markVol r u ≤ M.markVol r0 u :=
    M.clusterVol_atParameter_mono hr hr0 hrr.le u 0
  have hcl : cluster (atParameter (M.cutProb r) u) (0 : M.V) ⊆
      cluster (atParameter (M.cutProb r0) u) (0 : M.V) :=
    cluster_mono (fun e he => lt_of_lt_of_le he
      (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr0 hrr.le e))) 0
  have hsub : E1Sign.ballF M r ⊆ M.ballFLt r0 := by
    intro y hy
    rw [E1Sign.mem_ballF] at hy
    exact M.mem_ballFLt.mpr (lt_of_le_of_lt hy hrr)
  simp only [SourceModelData.connMarkFun, SourceModelData.connMarkFunLt]
  calc (M.markVol r u) ^ 2 * (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
      ≤ (M.markVol r0 u) ^ 2 * (∑ y ∈ E1Sign.ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y) := by gcongr
    _ ≤ (M.markVol r0 u) ^ 2 * (∑ y ∈ M.ballFLt r0,
        (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y) := by
        refine mul_le_mul' le_rfl ?_
        calc (∑ y ∈ E1Sign.ballF M r,
              (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
                (fun _ => (1 : ℝ≥0∞)) y)
              ≤ ∑ y ∈ E1Sign.ballF M r,
                (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
                  (fun _ => (1 : ℝ≥0∞)) y := by
                refine Finset.sum_le_sum fun y _ => ?_
                by_cases hy : y ∈ cluster (atParameter (M.cutProb r) u) (0 : M.V)
                · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hcl hy)]
                · rw [Set.indicator_of_notMem hy]
                  exact zero_le
            _ ≤ ∑ y ∈ M.ballFLt r0,
                (cluster (atParameter (M.cutProb r0) u) (0 : M.V)).indicator
                  (fun _ => (1 : ℝ≥0∞)) y :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)

theorem connMassLt_le_cutMoment_three (r : ℝ) :
    M.connMassLt r ≤ M.cutMoment 3 r := by
  rw [SourceModelData.connMassLt, M.cutMoment_eq_mark 3 r]
  refine lintegral_mono fun u => ?_
  have hN : (∑ y ∈ M.ballFLt r,
      (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
        (fun _ => (1 : ℝ≥0∞)) y) ≤ M.markVol r u := by
    have hcl : (∑ y ∈ M.ballFLt r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
        ≤ ∑' y : M.V,
          (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y :=
      ENNReal.sum_le_tsum _
    rw [show M.markVol r u = ∑' y : M.V,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y from clusterVol_eq_tsum _ _]
    exact hcl
  calc (M.markVol r u) ^ 2 * (∑ y ∈ M.ballFLt r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y)
      ≤ (M.markVol r u) ^ 2 * M.markVol r u := by gcongr
    _ = (M.markVol r u) ^ 3 := by ring

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## Left continuity of `connMass` and the exact sphere obstruction -/

theorem tendsto_connMassReal_nhdsLT (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.connMassLt r0 ≠ ⊤) :
    Tendsto (fun r => (E1Sign.connMass M r).toReal) (𝓝[<] r0)
      (𝓝 ((M.connMassLt r0).toReal)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set r : ℕ → ℝ := fun n => r0 - r0 / ((n : ℝ) + 2) with hrdef
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hrpos : ∀ n : ℕ, 0 < r n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : r0 / ((n : ℝ) + 2) < r0 := by
      rw [div_lt_iff₀ h1]
      nlinarith
    simp only [hrdef]
    linarith
  have hrlt : ∀ n : ℕ, r n < r0 := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : 0 < r0 / ((n : ℝ) + 2) := div_pos hr0 h1
    simp only [hrdef]
    linarith
  have hmono : ∀ n : ℕ, r n ≤ r (n + 1) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h3 : r0 / (((n : ℝ) + 1) + 2) ≤ r0 / ((n : ℝ) + 2) := by
      apply div_le_div_of_nonneg_left hr0.le h1
      linarith
    have hcast : (((n + 1 : ℕ)) : ℝ) + 2 = ((n : ℝ) + 1) + 2 := by push_cast; ring
    simp only [hrdef]
    rw [hcast]
    linarith
  have hlim : Tendsto r atTop (𝓝 r0) := by
    have h0 : Tendsto (fun n : ℕ => r0 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop h1
    simp only [hrdef]
    simpa using tendsto_const_nhds.sub h0
  have hseq := M.iSup_connMass_nat hrpos hrlt hmono hlim
  have hseqT : Tendsto (fun n => E1Sign.connMass M (r n)) atTop (𝓝 (M.connMassLt r0)) := by
    rw [← hseq]
    exact tendsto_atTop_iSup (monotone_nat_of_le_succ fun n =>
      E1Sign.connMass_mono M (hrpos n) (hmono n))
  have hrealSeq : Tendsto (fun n => (E1Sign.connMass M (r n)).toReal) atTop
      (𝓝 ((M.connMassLt r0).toReal)) :=
    (ENNReal.tendsto_toReal hfin).comp hseqT
  have hev : ∀ᶠ n : ℕ in atTop, (M.connMassLt r0).toReal - ε <
      (E1Sign.connMass M (r n)).toReal :=
    (tendsto_order.1 hrealSeq).1 ((M.connMassLt r0).toReal - ε) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨r0 - r N, by linarith [hrlt N], ?_⟩
  intro x hxIio hxdist
  have hx1 : r N < x := by
    rw [Real.dist_eq, abs_lt] at hxdist
    linarith [hxdist.1]
  have hx2 : x < r0 := hxIio
  have hxpos : 0 < x := lt_trans (hrpos N) hx1
  have hfinx : E1Sign.connMass M x ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.connMass_le_connMassLt hxpos hx2)
  have hN' : (M.connMassLt r0).toReal - ε < (E1Sign.connMass M (r N)).toReal := hN N le_rfl
  have h1 : (E1Sign.connMass M (r N)).toReal ≤ (E1Sign.connMass M x).toReal :=
    ENNReal.toReal_mono hfinx (E1Sign.connMass_mono M (hrpos N) hx1.le)
  have h2 : (E1Sign.connMass M x).toReal ≤ (M.connMassLt r0).toReal :=
    ENNReal.toReal_mono hfin (M.connMass_le_connMassLt hxpos hx2)
  have h3 : (M.connMassLt r0).toReal - ε < (E1Sign.connMass M x).toReal := lt_of_lt_of_le hN' h1
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- **Exact decomposition.**  `connMass` at `r` is the strict-window mass plus the sphere layer
`{ρ = r}`; the latter is precisely what is missed by the left limit. -/
theorem connMass_eq_connMassLt_add_sphereMass (r : ℝ) :
    E1Sign.connMass M r = M.connMassLt r + M.sphereMass r := by
  rw [M.connMass_eq_lintegral_connMarkFun, SourceModelData.connMassLt,
    SourceModelData.sphereMass, ← lintegral_add_left (M.measurable_connMarkFunLt r)]
  congr 1
  funext u
  simp only [SourceModelData.connMarkFun, SourceModelData.connMarkFunLt]
  rw [← mul_add]
  congr 1
  have hbf : M.ballFLt r = (E1Sign.ballF M r).filter (fun y => M.S.ρ (toVec y) < r) := rfl
  rw [hbf]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := E1Sign.ballF M r)
    (p := fun y => M.S.ρ (toVec y) < r)
    (f := fun y => (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
      (fun _ => (1 : ℝ≥0∞)) y)
  rw [← hsplit]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr ?_
  intro y hy
  rw [E1Sign.mem_ballF] at hy
  constructor
  · intro h
    exact le_antisymm hy (not_lt.mp h)
  · intro h
    rw [h]
    exact not_lt.mpr le_rfl

/-- The sphere layer vanishes at every radius at which no lattice point has norm exactly `r`. -/
theorem sphereMass_eq_zero_of_no_sphere {r : ℝ} (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r) :
    M.sphereMass r = 0 := by
  rw [SourceModelData.sphereMass]
  have hemp : (E1Sign.ballF M r).filter (fun y => M.S.ρ (toVec y) = r) = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨y, hy⟩
    exact h y (Finset.mem_filter.mp hy).2
  simp [hemp]

/-- **Left continuity of `connMass` at radii with no lattice point on the sphere.** -/
theorem tendsto_connMassReal_nhdsLT_of_sphereMass_eq_zero (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.connMassLt r0 ≠ ⊤) (hsphere : M.sphereMass r0 = 0) :
    Tendsto (fun r => (E1Sign.connMass M r).toReal) (𝓝[<] r0)
      (𝓝 ((E1Sign.connMass M r0).toReal)) := by
  have h0 : E1Sign.connMass M r0 = M.connMassLt r0 := by
    rw [M.connMass_eq_connMassLt_add_sphereMass, hsphere, add_zero]
  rw [h0]
  exact M.tendsto_connMassReal_nhdsLT r0 hr0 hfin

/-- **Two-sided continuity of the connected window mass** at every `r₀ > 0` with no lattice
point on the sphere `{ρ = r₀}`, from finiteness of the third moment at one strictly larger
radius.  (Right continuity holds at every radius; only left continuity needs the sphere
condition.) -/
theorem continuousAt_connMassReal (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (hfin : M.cutMoment 3 r1 ≠ ⊤) (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0) :
    ContinuousAt (fun r => (E1Sign.connMass M r).toReal) r0 := by
  have hfin0 : M.cutMoment 3 r0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.cutMoment_monotone 3 hr1.le)
  have hltfin : M.connMassLt r0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin0 (M.connMassLt_le_cutMoment_three r0)
  have hleft := M.tendsto_connMassReal_nhdsLT_of_sphereMass_eq_zero r0 hr0 hltfin
    (M.sphereMass_eq_zero_of_no_sphere hsphere)
  have hright := M.tendsto_connMassReal_nhdsGT r0 hr0 hr1 hfin
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, hspec1⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hleft) ε hε
  obtain ⟨δ2, hδ2, hspec2⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hright) ε hε
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  rcases lt_trichotomy x r0 with h | h | h
  · refine hspec1 (show x ∈ Set.Iio r0 from h) ?_
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx (min_le_left _ _)
  · subst h
    simpa using hε
  · refine hspec2 (show x ∈ Set.Ioi r0 from h) ?_
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx (min_le_right _ _)

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms measurable_connMarkFun
#print axioms measurable_connMarkFunLt
#print axioms measurable_connAnnulusFun
#print axioms connMass_eq_lintegral_connMarkFun
#print axioms connMass_le_cutMoment_three
#print axioms connMarkFun_mono
#print axioms connMarkFun_le_add
#print axioms connMass_le_add
#print axioms connAnnulusFun_mono
#print axioms connAnnulusMass_mono
#print axioms connAnnulusFun_le_cube
#print axioms connAnnulusMass_le_cutMoment_three
#print axioms tendsto_connAnnulusMass_toReal
#print axioms tendsto_connMassReal_nhdsGT
#print axioms iSup_windowSum
#print axioms iSup_connMarkFun_nat
#print axioms iSup_connMass_nat
#print axioms connMass_le_connMassLt
#print axioms connMassLt_le_cutMoment_three
#print axioms tendsto_connMassReal_nhdsLT
#print axioms connMass_eq_connMassLt_add_sphereMass
#print axioms sphereMass_eq_zero_of_no_sphere
#print axioms tendsto_connMassReal_nhdsLT_of_sphereMass_eq_zero
#print axioms continuousAt_connMassReal

#print axioms PercLib.CriticalLRP.sum_indicator_eq_card
#print axioms PercLib.CriticalLRP.iSup_mul_iSup_nat
