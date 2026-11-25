/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Radius regularity of every natural cut-off cluster moment

At the actual `SourceModelData`, for every `p : ℕ` and every `r₀ > 0`:

* `tendsto_cutMomentReal_nhdsLT` — **left continuity**, unconditional:
  `(M.cutMoment p r).toReal → (M.cutMoment p r₀).toReal` as `r ↑ r₀`.
  The engine is the landed all-order monotone convergence
  `CutoffMomentTransfer.iSup_lintegral_clusterVol_pow`, applied along `r n = r₀ - r₀/(n+2)`.
* `tendsto_cutMomentReal_nhdsGT` — **right continuity** from finiteness of the *same* moment at
  one strictly larger radius `r₁ > r₀` (`M.cutMoment p r₁ ≠ ⊤`), and only that.
  The proof is the dominated `markEscape` argument of `Analysis/Cutoff/Continuity`
  carried to the `p`-th power:
  on the common mark space the box-change event shrinks to the null set `boxNull` and the escape
  event is controlled by `markVolPow M p r₁`.
* `continuousAt_cutMomentReal` / `continuousOn_cutMomentReal` — two-sided continuity at a point,
  and on a compact radius window, again from a finite moment at a strictly larger radius.
* `cutMoment_le_window` / `cutMoment_ne_top_on_window` — monotone local boundedness on a radius
  window (no continuity involved); for `p = 1` this is `Analysis/Cutoff/Continuity`'s mass.
* `E1Sign.pairMass_eq_mark`, `E1Sign.connMass_eq_mark` — the joint window moments of
  `Analysis/Cutoff/Defect` read on the common mark space;
  `E1Sign.pairMass_mono`, `E1Sign.connMass_mono` — both are **nondecreasing** in the radius
  (for `0 < r ≤ r'`), hence `pairMass_le_window`, `connMass_le_window` and
  `pairMass_ne_top_on_window`, `connMass_ne_top_on_window` give local boundedness and finiteness
  on a radius window from the value at a strictly larger radius.

What is *not* claimed: continuity in `r` of `pairMass`/`connMass`, or of `exclMass`, or of the
excluded flux: their integrands carry the moving window `ballF M r`, whose comparison needs the
annulus estimate described in `REPORT.md`; no derivative, no absolute continuity, no claim about
the defect `cutE1` is made here.  The `p = 0` moment is the constant `1`
(`SourceModelData.cutMoment_zero`), so nothing above is vacuous at `p = 0`.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity.Defs

/-! # Radius regularity of every natural cut-off cluster moment

Left continuity of `r ↦ (M.cutMoment p r).toReal` at every `r₀ > 0`, right continuity from
finiteness of the same moment at one strictly larger radius, two-sided and window continuity,
monotone local boundedness, and the mark-space form and radius monotonicity of the joint window
moments `pairMass`/`connMass` of `Analysis/Cutoff/Defect`.  See the file header for the exact
statements and for what is not claimed. -/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem cutMoment_eq_mark (p : ℕ) (r : ℝ) :
    M.cutMoment p r =
      ∫⁻ u : Sym2 M.V → ℝ, (M.markVol r u) ^ p ∂(markMeasure M.V) := by
  have hlaw : M.cutMoment p r =
      ∫⁻ ω, clusterVol ω (0 : M.V) ^ p ∂(edgeMeasure (M.cutProb r)) := rfl
  rw [hlaw, ← markMeasure_map_atParameter]
  rw [lintegral_map ((measurable_clusterVol (0 : M.V)).pow_const p) (measurable_atParameter _)]
  simp only [SourceModelData.markVol]

/-- At `p = 1` the moment is the landed cut-off cluster mass: the `p = 1` case of everything below
reproduces `Analysis/Cutoff/Continuity`. -/
theorem cutMoment_one_eq_cutMassAt (r : ℝ) : M.cutMoment 1 r = M.cutMassAt r 0 := by
  simp only [SourceModelData.cutMoment, SourceModelData.cutMassAt, pow_one]

theorem cutMomentReal_one_eq_cutMassReal (r : ℝ) : M.cutMomentReal 1 r = M.cutMassReal r := by
  simp only [SourceModelData.cutMomentReal, SourceModelData.cutMassReal,
    M.cutMoment_one_eq_cutMassAt]

theorem iSup_cutMoment_nat {r : ℕ → ℝ} {r0 : ℝ} (hr : ∀ n, 0 < r n) (hr0 : 0 < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0)) (p : ℕ) :
    (⨆ n, M.cutMoment p (r n)) = M.cutMoment p r0 :=
  PercLib.CriticalLRP.CutoffMomentTransfer.iSup_lintegral_clusterVol_pow
    (p := fun n => M.cutProb (r n)) (q := M.cutProb r0)
    (fun n e => M.cutProb_mono (hr n) (hr (n + 1)) (hmono n) e)
    (fun e => (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim) (0 : M.V) p

theorem tendsto_cutMomentAt_nat {r : ℕ → ℝ} {r0 : ℝ} (hr : ∀ n, 0 < r n) (hr0 : 0 < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0)) (p : ℕ) :
    Tendsto (fun n => M.cutMoment p (r n)) atTop (𝓝 (M.cutMoment p r0)) := by
  rw [← M.iSup_cutMoment_nat hr hr0 hmono hlim p]
  exact tendsto_atTop_iSup (monotone_nat_of_le_succ fun n =>
    M.cutMoment_monotone p (hmono n))

theorem tendsto_cutMomentReal_nat {r : ℕ → ℝ} {r0 : ℝ} (hr : ∀ n, 0 < r n) (hr0 : 0 < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0)) (p : ℕ)
    (hfin : M.cutMoment p r0 ≠ ⊤) :
    Tendsto (fun n => (M.cutMoment p (r n)).toReal) atTop
      (𝓝 ((M.cutMoment p r0).toReal)) :=
  (ENNReal.tendsto_toReal hfin).comp (M.tendsto_cutMomentAt_nat hr hr0 hmono hlim p)

theorem cutMomentReal_le_of_le {r r' : ℝ} (hrr' : r ≤ r') (p : ℕ)
    (hfin : M.cutMoment p r' ≠ ⊤) :
    (M.cutMoment p r).toReal ≤ (M.cutMoment p r').toReal :=
  ENNReal.toReal_mono hfin (M.cutMoment_monotone p hrr')


/-! ## Left continuity -/

theorem tendsto_cutMomentReal_nhdsLT (p : ℕ) (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.cutMoment p r0 ≠ ⊤) :
    Tendsto (fun r => (M.cutMoment p r).toReal) (𝓝[<] r0)
      (𝓝 ((M.cutMoment p r0).toReal)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set r : ℕ → ℝ := fun n => r0 - r0 / ((n : ℝ) + 2) with hrdef
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hr : ∀ n : ℕ, 0 < r n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : r0 / ((n : ℝ) + 2) < r0 := by
      rw [div_lt_iff₀ h1]
      nlinarith
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
  have hseq := M.tendsto_cutMomentReal_nat hr hr0 hmono hlim p hfin
  have hev : ∀ᶠ n : ℕ in atTop, (M.cutMoment p r0).toReal - ε <
      (M.cutMoment p (r n)).toReal :=
    (tendsto_order.1 hseq).1 ((M.cutMoment p r0).toReal - ε) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hrN : r N < r0 := by
    have h1 : (0 : ℝ) < (N : ℝ) + 2 := hden N
    have h2 : 0 < r0 / ((N : ℝ) + 2) := div_pos hr0 h1
    simp only [hrdef]
    linarith
  refine ⟨r0 - r N, by linarith, ?_⟩
  intro x hxIio hxdist
  have hx1 : r N < x := by
    rw [Real.dist_eq, abs_lt] at hxdist
    linarith [hxdist.1]
  have hx2 : x < r0 := hxIio
  rw [Real.dist_eq]
  have hN' : (M.cutMoment p r0).toReal - ε < (M.cutMoment p (r N)).toReal := hN N le_rfl
  have hfinx : M.cutMoment p x ≠ ⊤ := ne_top_of_le_ne_top hfin (M.cutMoment_monotone p hx2.le)
  have h1 : (M.cutMoment p (r N)).toReal ≤ (M.cutMoment p x).toReal :=
    M.cutMomentReal_le_of_le hx1.le p hfinx
  have h2 : (M.cutMoment p x).toReal ≤ (M.cutMoment p r0).toReal :=
    M.cutMomentReal_le_of_le hx2.le p hfin
  have h3 : (M.cutMoment p r0).toReal - ε < (M.cutMoment p x).toReal := lt_of_lt_of_le hN' h1
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-! ## The power increment bound for continuity from above -/

theorem markVolPow_le_add_indicators {r0 r r1 R : ℝ} (hr : 0 < r) (hr1 : 0 < r1)
    (h11 : r ≤ r1) (u : Sym2 M.V → ℝ) (p : ℕ) :
    M.markVolPow p r u ≤
        M.markVolPow p r0 u +
        (M.markBoxChange r0 r R).indicator (M.markVolPow p r1) u +
        (M.markEscape r1 R).indicator (M.markVolPow p r1) u := by
  have h1 : (M.markVol r u) ^ p ≤ (M.markVol r1 u) ^ p :=
    pow_le_pow_left' (M.clusterVol_atParameter_mono hr hr1 h11 u 0) p
  by_cases hbox : u ∈ M.markBoxChange r0 r R
  · rw [Set.indicator_of_mem hbox]
    have h2 : (M.markVol r1 u) ^ p ≤ (M.markVol r0 u) ^ p + (M.markVol r1 u) ^ p :=
      le_add_self
    have h3 : (M.markVol r0 u) ^ p + (M.markVol r1 u) ^ p ≤
        (M.markVol r0 u) ^ p + (M.markVol r1 u) ^ p +
          (M.markEscape r1 R).indicator (fun u => (M.markVol r1 u) ^ p) u := le_self_add
    exact le_trans (le_trans h1 h2) h3
  · rw [Set.indicator_of_notMem hbox]
    simp only [add_zero]
    by_cases hesc : u ∈ M.markEscape r1 R
    · rw [Set.indicator_of_mem hesc]
      have h2 : (M.markVol r1 u) ^ p ≤ (M.markVol r0 u) ^ p + (M.markVol r1 u) ^ p :=
        le_add_self
      exact le_trans h1 h2
    · rw [Set.indicator_of_notMem hesc]
      have hesc' : u ∉ M.markEscape r R := fun h => hesc (M.markEscape_mono hr hr1 h11 h)
      have hbase : M.markVol r u ≤ M.markVol r0 u := by
        simpa [SourceModelData.markVol] using M.clusterVol_le_of_notMem hbox hesc'
      simpa using pow_le_pow_left' hbase p

theorem cutMoment_le_add {r0 r r1 R : ℝ} (hr : 0 < r) (hr1 : 0 < r1)
    (h11 : r ≤ r1) (p : ℕ) :
    M.cutMoment p r ≤ M.cutMoment p r0 +
      (∫⁻ u in M.markBoxChange r0 r R, (M.markVol r1 u) ^ p ∂(markMeasure M.V)) +
      (∫⁻ u in M.markEscape r1 R, (M.markVol r1 u) ^ p ∂(markMeasure M.V)) := by
  have hmono : ∫⁻ u, (M.markVol r u) ^ p ∂(markMeasure M.V) ≤
      ∫⁻ u, ((M.markVol r0 u) ^ p +
        (M.markBoxChange r0 r R).indicator (fun u => (M.markVol r1 u) ^ p) u +
        (M.markEscape r1 R).indicator (fun u => (M.markVol r1 u) ^ p) u)
        ∂(markMeasure M.V) :=
    lintegral_mono fun u => M.markVolPow_le_add_indicators hr hr1 h11 u p
  have hmeas2 : Measurable fun u : Sym2 M.V → ℝ =>
      (M.markVol r0 u) ^ p +
        (M.markBoxChange r0 r R).indicator (fun u => (M.markVol r1 u) ^ p) u :=
    ((M.measurable_markVol r0).pow_const p).add (((M.measurable_markVol r1).pow_const p).indicator
      (M.measurableSet_markBoxChange r0 r R))
  rw [lintegral_add_left hmeas2, lintegral_add_left ((M.measurable_markVol r0).pow_const p),
    lintegral_indicator (M.measurableSet_markBoxChange r0 r R) (fun u => (M.markVol r1 u) ^ p),
    lintegral_indicator (M.measurableSet_markEscape r1 R) (fun u => (M.markVol r1 u) ^ p)] at hmono
  rw [M.cutMoment_eq_mark p r, M.cutMoment_eq_mark p r0]
  exact hmono

theorem markVol_lt_top_ae {p : ℕ} (hp : 1 ≤ p) (r : ℝ) (hfin : M.cutMoment p r ≠ ⊤) :
    ∀ᵐ u ∂(markMeasure M.V), M.markVol r u < ⊤ := by
  have h1 : (∫⁻ u : Sym2 M.V → ℝ, (M.markVol r u) ^ p ∂(markMeasure M.V)) ≠ ⊤ := by
    rw [← M.cutMoment_eq_mark p r]
    exact hfin
  have h2 := ae_lt_top ((M.measurable_markVol r).pow_const p) h1
  filter_upwards [h2] with u hu
  by_contra htop
  rw [not_lt] at htop
  have htop' : M.markVol r u = ⊤ := top_le_iff.mp htop
  rw [htop'] at hu
  have hp0 : p ≠ 0 := by omega
  simp [hp0] at hu

theorem measure_iInter_markEscape_zero_of_pow {p : ℕ} (hp : 1 ≤ p) (r : ℝ)
    (hfin : M.cutMoment p r ≠ ⊤) :
    markMeasure M.V (⋂ n : ℕ, M.markEscape r (n : ℝ)) = 0 := by
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [M.markVol_lt_top_ae hp r hfin] with u hu hmem
  have htop : M.markVol r u = ⊤ :=
    M.clusterVol_eq_top_of_forall_mem_markEscape fun n => Set.mem_iInter.mp hmem n
  exact absurd htop hu.ne

theorem tendsto_boxIntegral_pow (p : ℕ) (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (_hr1 : r0 < r1)
    (hfin : M.cutMoment p r1 ≠ ⊤) (R : ℝ) :
    Tendsto (fun r => (∫⁻ u in M.markBoxChange r0 r R, (M.markVol r1 u) ^ p
      ∂(markMeasure M.V)).toReal) (𝓝[>] r0) (𝓝 0) := by
  set rseq : ℕ → ℝ := fun n => r0 + r0 / ((n : ℝ) + 2) with hrseq
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hrpos : ∀ n : ℕ, r0 < rseq n := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have h2 : 0 < r0 / ((n : ℝ) + 2) := div_pos hr0 h1
    simp only [hrseq]
    linarith
  have hseq : Tendsto rseq atTop (𝓝 r0) := by
    have h0 : Tendsto (fun n : ℕ => r0 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop h1
    simp only [hrseq]
    simpa using tendsto_const_nhds.add h0
  have hanti : Antitone fun n : ℕ => M.markBoxChange r0 (rseq n) R := by
    intro n m hnm
    refine M.markBoxChange_mono hr0 (lt_trans hr0 (hrpos m)) (lt_trans hr0 (hrpos n)) ?_
    have hd1 : (0 : ℝ) < (n : ℝ) + 2 := hden n
    have hd2 : (0 : ℝ) < (m : ℝ) + 2 := hden m
    have hcast : ((n : ℝ) + 2) ≤ ((m : ℝ) + 2) := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    simp only [hrseq]
    have : r0 / ((m : ℝ) + 2) ≤ r0 / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr0.le hd1 hcast
    linarith
  have hnull : markMeasure M.V (⋂ n : ℕ, M.markBoxChange r0 (rseq n) R) = 0 :=
    measure_mono_null (M.iInter_markBoxChange_subset hr0 hseq) (M.measure_boxNull r0 R)
  have hInt : (∫⁻ a, (M.markVol r1 a) ^ p ∂(markMeasure M.V)) = M.cutMoment p r1 :=
    (M.cutMoment_eq_mark p r1).symm
  have hconv : Tendsto (fun n : ℕ => (∫⁻ u in M.markBoxChange r0 (rseq n) R,
      (M.markVol r1 u) ^ p ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
    tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V)
      (f := fun u => (M.markVol r1 u) ^ p)
      ((M.measurable_markVol r1).pow_const p) (by rw [hInt]; exact hfin)
      (fun n => M.measurableSet_markBoxChange r0 (rseq n) R) hanti hnull
  refine tendsto_zero_of_le_seq (r := rseq) ?_ ?_ hrpos hconv
  · intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le (lt_trans hr0 hx) hxy
    have hsub : M.markBoxChange r0 x R ⊆ M.markBoxChange r0 y R :=
      M.markBoxChange_mono hr0 (lt_trans hr0 hx) hy hxy
    have hfin' : (∫⁻ u in M.markBoxChange r0 y R, (M.markVol r1 u) ^ p
        ∂(markMeasure M.V)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_set (Set.subset_univ _))
      rw [Measure.restrict_univ, hInt]
      exact hfin
    exact ENNReal.toReal_mono hfin' (lintegral_mono_set hsub)
  · intro x
    exact ENNReal.toReal_nonneg

/-! ## Right continuity -/

theorem tendsto_cutMomentReal_nhdsGT (p : ℕ) (hp : 1 ≤ p) (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ}
    (hr1 : r0 < r1) (hfin : M.cutMoment p r1 ≠ ⊤) :
    Tendsto (fun r => (M.cutMoment p r).toReal) (𝓝[>] r0)
      (𝓝 ((M.cutMoment p r0).toReal)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hInt : (∫⁻ a, (M.markVol r1 a) ^ p ∂(markMeasure M.V)) = M.cutMoment p r1 :=
    (M.cutMoment_eq_mark p r1).symm
  have hesc_tend : Tendsto (fun n : ℕ => (∫⁻ u in M.markEscape r1 (n : ℝ),
      (M.markVol r1 u) ^ p ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
    tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V)
      (f := fun u => (M.markVol r1 u) ^ p)
      ((M.measurable_markVol r1).pow_const p) (by rw [hInt]; exact hfin)
      (fun n => M.measurableSet_markEscape r1 (n : ℝ))
      (fun n m hnm => M.markEscape_antitone (by exact_mod_cast hnm))
      (M.measure_iInter_markEscape_zero_of_pow hp r1 hfin)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hesc_tend) (ε / 2) (by linarith)
  have hN' : (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ p
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h := hN N le_rfl
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h
  have hbox := M.tendsto_boxIntegral_pow p r0 hr0 hr1 hfin (N : ℝ)
  obtain ⟨δ, hδ, hspec⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hbox) (ε / 2) (by linarith)
  refine ⟨min δ (r1 - r0), lt_min hδ (by linarith), ?_⟩
  intro r hr hdist
  rw [Real.dist_eq] at hdist
  have hr1' : r ≤ r1 := by
    rw [abs_lt] at hdist
    linarith [hdist.2, min_le_right δ (r1 - r0)]
  have hrpos : 0 < r := lt_trans hr0 hr
  have hboxsmall : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ p
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h2 : dist (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ p
        ∂(markMeasure M.V)).toReal 0 < ε / 2 := by
      refine hspec hr ?_
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hdist (min_le_left δ (r1 - r0))
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h2
  have hfr : M.cutMoment p r ≠ ⊤ := ne_top_of_le_ne_top hfin (M.cutMoment_monotone p hr1')
  have hfr0 : M.cutMoment p r0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.cutMoment_monotone p hr1.le)
  have hUniv : (∫⁻ u in (Set.univ : Set (Sym2 M.V → ℝ)), (M.markVol r1 u) ^ p
      ∂(markMeasure M.V)) ≠ ⊤ := by
    rw [Measure.restrict_univ, hInt]
    exact hfin
  have hboxfin : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ p
      ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hUniv (lintegral_mono_set (Set.subset_univ _))
  have hescfin : (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ p
      ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hUniv (lintegral_mono_set (Set.subset_univ _))
  have hincr := M.cutMoment_le_add (r0 := r0) (r := r) (r1 := r1) (R := (N : ℝ)) hrpos
    (lt_trans hr0 hr1) hr1' p
  have hsum : M.cutMoment p r0 +
      (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ p ∂(markMeasure M.V)) +
      (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ p ∂(markMeasure M.V)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfr0, hboxfin⟩, hescfin⟩
  have hreal : (M.cutMoment p r).toReal ≤ (M.cutMoment p r0).toReal +
      (∫⁻ u in M.markBoxChange r0 r (N : ℝ), (M.markVol r1 u) ^ p
        ∂(markMeasure M.V)).toReal +
      (∫⁻ u in M.markEscape r1 (N : ℝ), (M.markVol r1 u) ^ p
        ∂(markMeasure M.V)).toReal := by
    have h := ENNReal.toReal_mono hsum hincr
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfr0, hboxfin⟩) hescfin,
      ENNReal.toReal_add hfr0 hboxfin] at h
  have hmono : (M.cutMoment p r0).toReal ≤ (M.cutMoment p r).toReal :=
    M.cutMomentReal_le_of_le hr.le p hfr
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-! ## Two-sided continuity -/

theorem continuousAt_cutMomentReal (p : ℕ) (hp : 1 ≤ p) (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ}
    (hr1 : r0 < r1) (hfin : M.cutMoment p r1 ≠ ⊤) :
    ContinuousAt (fun r => (M.cutMoment p r).toReal) r0 := by
  have hfin0 : M.cutMoment p r0 ≠ ⊤ := ne_top_of_le_ne_top hfin (M.cutMoment_monotone p hr1.le)
  have hleft := M.tendsto_cutMomentReal_nhdsLT p r0 hr0 hfin0
  have hright := M.tendsto_cutMomentReal_nhdsGT p hp r0 hr0 hr1 hfin
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

theorem continuousOn_cutMomentReal (p : ℕ) (hp : 1 ≤ p) {a b b' : ℝ} (ha : 0 < a)
    (hbb' : b < b') (hfin : M.cutMoment p b' ≠ ⊤) :
    ContinuousOn (fun r => (M.cutMoment p r).toReal) (Set.Icc a b) := by
  intro x hx
  exact (M.continuousAt_cutMomentReal p hp x (lt_of_lt_of_le ha hx.1)
    (lt_of_le_of_lt hx.2 hbb') hfin).continuousWithinAt

/-! ## The finite-exception fundamental theorem of calculus for every moment -/

theorem abs_sub_le_integral_cutMomentReal {a b : ℝ} (ha : 0 < a) (p : ℕ)
    (hp : 1 ≤ p) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMoment p b' ≠ ⊤) {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hDfin : (M.cornerRadii ∩ Set.Ioo a b).Finite)
    (hgood : ∀ u ∈ Set.Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ (fun r => (M.cutMoment p r).toReal) u ∧
        |deriv (fun r => (M.cutMoment p r).toReal) u| ≤ g u) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      |(M.cutMoment p y).toReal - (M.cutMoment p x).toReal| ≤ ∫ t in x..y, g t := by
  classical
  refine PercLib.CriticalLRP.IntervalAC.abs_sub_le_integral_of_finite_exception
    (M.continuousOn_cutMomentReal p hp ha hbb' hfin) hgcont hDfin.toFinset ?_
  intro u hu hmem
  exact hgood u hu fun hcorner => hmem (hDfin.mem_toFinset.mpr ⟨hcorner, hu⟩)

theorem cutMomentReal_absolutelyContinuousOn {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p : ℕ)
    (hp : 1 ≤ p) {b' : ℝ} (hbb' : b < b') (hfin : M.cutMoment p b' ≠ ⊤) {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hDfin : (M.cornerRadii ∩ Set.Ioo a b).Finite)
    (hgood : ∀ u ∈ Set.Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ (fun r => (M.cutMoment p r).toReal) u ∧
        |deriv (fun r => (M.cutMoment p r).toReal) u| ≤ g u) :
    AbsolutelyContinuousOnInterval (fun r => (M.cutMoment p r).toReal) a b := by
  have hgint : IntervalIntegrable g volume a b :=
    (hgcont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  exact PercLib.CriticalLRP.IntervalAC.absolutelyContinuousOnInterval_of_interval_bound hab hgint
    (M.abs_sub_le_integral_cutMomentReal ha p hp hbb' hfin hgcont hDfin hgood)

/-- **Local boundedness of every natural cutoff moment on a radius window**, from its value at a
strictly larger radius.  No continuity is asserted. -/
theorem cutMoment_le_window {a b b' : ℝ} (hbb' : b ≤ b') (p : ℕ) :
    ∀ r ∈ Set.Icc a b, M.cutMoment p r ≤ M.cutMoment p b' :=
  fun _r hr => M.cutMoment_monotone p (le_trans hr.2 hbb')

theorem cutMoment_ne_top_of_le {r r' : ℝ} (hrr' : r ≤ r') (p : ℕ)
    (h : M.cutMoment p r' ≠ ⊤) : M.cutMoment p r ≠ ⊤ :=
  ne_top_of_le_ne_top h (M.cutMoment_monotone p hrr')

theorem cutMoment_ne_top_on_window {a b b' : ℝ} (hbb' : b ≤ b') (p : ℕ)
    (h : M.cutMoment p b' ≠ ⊤) : ∀ r ∈ Set.Icc a b, M.cutMoment p r ≠ ⊤ :=
  fun _r hr => M.cutMoment_ne_top_of_le (le_trans hr.2 hbb') p h

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem ballF_mono {r r' : ℝ} (h : r ≤ r') :
    PercLib.CriticalLRP.E1Sign.ballF M r ⊆ PercLib.CriticalLRP.E1Sign.ballF M r' := by
  intro y hy
  rw [PercLib.CriticalLRP.E1Sign.mem_ballF] at hy ⊢
  exact PercLib.CriticalLRP.BallAverage.ball_mono M h hy

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.E1Sign

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

theorem pairMass_eq_mark (r : ℝ) :
    pairMass M r = ∫⁻ u : Sym2 M.V → ℝ,
      clusterVol (atParameter (M.cutProb r) u) (0 : M.V) *
        ∑ y ∈ ballF M r, clusterVol (atParameter (M.cutProb r) u) y
        ∂(markMeasure M.V) := by
  rw [pairMass, cutLaw_eq M r, ← markMeasure_map_atParameter]
  refine lintegral_map ?_ (measurable_atParameter _)
  exact (measurable_clusterVol (0 : M.V)).mul
    (Finset.measurable_sum (ballF M r) fun y _ => measurable_clusterVol y)

theorem connMass_eq_mark (r : ℝ) :
    connMass M r = ∫⁻ u : Sym2 M.V → ℝ,
      clusterVol (atParameter (M.cutProb r) u) (0 : M.V) ^ 2 *
        ∑ y ∈ ballF M r,
          (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
            (fun _ => (1 : ℝ≥0∞)) y
        ∂(markMeasure M.V) := by
  rw [connMass, cutLaw_eq M r, ← markMeasure_map_atParameter]
  refine lintegral_map ?_ (measurable_atParameter _)
  exact ((measurable_clusterVol (0 : M.V)).pow_const 2).mul
    (Finset.measurable_sum (ballF M r) fun y _ =>
      (measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y)))

theorem pairMass_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    pairMass M r ≤ pairMass M r' := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  rw [pairMass_eq_mark M r, pairMass_eq_mark M r']
  refine lintegral_mono fun u => ?_
  have hvol : ∀ y : M.V,
      clusterVol (atParameter (M.cutProb r) u) y ≤ clusterVol (atParameter (M.cutProb r') u) y :=
    fun y => M.clusterVol_atParameter_mono hr hr' hrr' u y
  have hsum1 : ∑ y ∈ ballF M r, clusterVol (atParameter (M.cutProb r) u) y
      ≤ ∑ y ∈ ballF M r, clusterVol (atParameter (M.cutProb r') u) y :=
    Finset.sum_le_sum fun y _ => hvol y
  have hsum2 : ∑ y ∈ ballF M r, clusterVol (atParameter (M.cutProb r') u) y
      ≤ ∑ y ∈ ballF M r', clusterVol (atParameter (M.cutProb r') u) y :=
    Finset.sum_le_sum_of_subset_of_nonneg (SourceModelData.ballF_mono M hrr')
      (fun x _ _ => bot_le)
  exact mul_le_mul' (hvol 0) (le_trans hsum1 hsum2)

theorem connMass_mono {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    connMass M r ≤ connMass M r' := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  rw [connMass_eq_mark M r, connMass_eq_mark M r']
  refine lintegral_mono fun u => ?_
  have hle : atParameter (M.cutProb r) u ≤ atParameter (M.cutProb r') u := by
    intro e he
    exact lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr' hrr' e))
  have hvol : ∀ y : M.V,
      clusterVol (atParameter (M.cutProb r) u) y ≤ clusterVol (atParameter (M.cutProb r') u) y :=
    fun y => M.clusterVol_atParameter_mono hr hr' hrr' u y
  have hcl : cluster (atParameter (M.cutProb r) u) (0 : M.V) ⊆
      cluster (atParameter (M.cutProb r') u) (0 : M.V) := cluster_mono hle 0
  have hsum1 : ∑ y ∈ ballF M r,
        (cluster (atParameter (M.cutProb r) u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y
      ≤ ∑ y ∈ ballF M r,
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y := by
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hy : y ∈ cluster (atParameter (M.cutProb r) u) (0 : M.V)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hcl hy)]
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  have hsum2 : ∑ y ∈ ballF M r,
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y
      ≤ ∑ y ∈ ballF M r',
        (cluster (atParameter (M.cutProb r') u) (0 : M.V)).indicator
          (fun _ => (1 : ℝ≥0∞)) y :=
    Finset.sum_le_sum_of_subset_of_nonneg (SourceModelData.ballF_mono M hrr')
      (fun x _ _ => bot_le)
  exact mul_le_mul' (pow_le_pow_left' (hvol 0) 2) (le_trans hsum1 hsum2)

theorem pairMass_ne_top_of_le {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    (h : pairMass M r' ≠ ⊤) : pairMass M r ≠ ⊤ :=
  ne_top_of_le_ne_top h (pairMass_mono M hr hrr')

theorem connMass_ne_top_of_le {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    (h : connMass M r' ≠ ⊤) : connMass M r ≠ ⊤ :=
  ne_top_of_le_ne_top h (connMass_mono M hr hrr')

/-- **Local boundedness of the joint window moment on a radius window**, from its value at a
strictly larger radius (no continuity is asserted). -/
theorem pairMass_le_window {a b b' : ℝ} (ha : 0 < a) (hbb' : b ≤ b') :
    ∀ r ∈ Set.Icc a b, pairMass M r ≤ pairMass M b' :=
  fun _r hr => pairMass_mono M (lt_of_lt_of_le ha hr.1) (le_trans hr.2 hbb')

theorem connMass_le_window {a b b' : ℝ} (ha : 0 < a) (hbb' : b ≤ b') :
    ∀ r ∈ Set.Icc a b, connMass M r ≤ connMass M b' :=
  fun _r hr => connMass_mono M (lt_of_lt_of_le ha hr.1) (le_trans hr.2 hbb')

theorem pairMass_ne_top_on_window {a b b' : ℝ} (ha : 0 < a) (hbb' : b ≤ b')
    (h : pairMass M b' ≠ ⊤) : ∀ r ∈ Set.Icc a b, pairMass M r ≠ ⊤ :=
  fun _r hr => ne_top_of_le_ne_top h (pairMass_le_window M ha hbb' _r hr)

theorem connMass_ne_top_on_window {a b b' : ℝ} (ha : 0 < a) (hbb' : b ≤ b')
    (h : connMass M b' ≠ ⊤) : ∀ r ∈ Set.Icc a b, connMass M r ≠ ⊤ :=
  fun _r hr => ne_top_of_le_ne_top h (connMass_le_window M ha hbb' _r hr)

end PercLib.CriticalLRP.E1Sign

/-! ## The public statements in `cutMomentReal` form -/

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem tendsto_cutMomentReal_nhdsLT' (p : ℕ) (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.cutMoment p r0 ≠ ⊤) :
    Tendsto (M.cutMomentReal p) (𝓝[<] r0) (𝓝 (M.cutMomentReal p r0)) :=
  M.tendsto_cutMomentReal_nhdsLT p r0 hr0 hfin

theorem tendsto_cutMomentReal_nhdsGT' (p : ℕ) (hp : 1 ≤ p) (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ}
    (hr1 : r0 < r1) (hfin : M.cutMoment p r1 ≠ ⊤) :
    Tendsto (M.cutMomentReal p) (𝓝[>] r0) (𝓝 (M.cutMomentReal p r0)) :=
  M.tendsto_cutMomentReal_nhdsGT p hp r0 hr0 hr1 hfin

theorem continuousAt_cutMomentReal' (p : ℕ) (hp : 1 ≤ p) (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ}
    (hr1 : r0 < r1) (hfin : M.cutMoment p r1 ≠ ⊤) :
    ContinuousAt (M.cutMomentReal p) r0 :=
  M.continuousAt_cutMomentReal p hp r0 hr0 hr1 hfin

theorem continuousOn_cutMomentReal' (p : ℕ) (hp : 1 ≤ p) {a b b' : ℝ} (ha : 0 < a)
    (hbb' : b < b') (hfin : M.cutMoment p b' ≠ ⊤) :
    ContinuousOn (M.cutMomentReal p) (Set.Icc a b) :=
  M.continuousOn_cutMomentReal p hp ha hbb' hfin

end SourceModelData

end PercLib.CriticalLRP.Orchestration

set_option linter.hashCommand false

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration PercLib.CriticalLRP.E1Sign

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_eq_mark
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_cutMoment_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMomentReal_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMomentReal_nhdsLT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markVol_lt_top_ae
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.measure_iInter_markEscape_zero_of_pow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markVolPow_le_add_indicators
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_le_add
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_boxIntegral_pow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMomentReal_nhdsGT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_cutMomentReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousOn_cutMomentReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_le_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_on_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ballF_mono
#print axioms PercLib.CriticalLRP.E1Sign.pairMass_eq_mark
#print axioms PercLib.CriticalLRP.E1Sign.connMass_eq_mark
#print axioms PercLib.CriticalLRP.E1Sign.pairMass_mono
#print axioms PercLib.CriticalLRP.E1Sign.connMass_mono
#print axioms PercLib.CriticalLRP.E1Sign.pairMass_le_window
#print axioms PercLib.CriticalLRP.E1Sign.connMass_le_window
#print axioms PercLib.CriticalLRP.E1Sign.pairMass_ne_top_on_window
#print axioms PercLib.CriticalLRP.E1Sign.connMass_ne_top_on_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_cutMomentReal'
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.continuousOn_cutMomentReal'
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.abs_sub_le_integral_cutMomentReal
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMomentReal_absolutelyContinuousOn
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMomentAt_nat
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMomentReal_le_of_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_ne_top_of_le
#print axioms PercLib.CriticalLRP.E1Sign.pairMass_ne_top_of_le
#print axioms PercLib.CriticalLRP.E1Sign.connMass_ne_top_of_le
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMomentReal_nhdsLT'
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMomentReal_nhdsGT'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_one_eq_cutMassAt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMomentReal_one_eq_cutMassReal
