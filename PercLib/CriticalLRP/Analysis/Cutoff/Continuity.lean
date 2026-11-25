/-
# Continuity of the cut-off cluster mass at every radius (D8)

At the actual `SourceModelData`, for `χ(r) = (M.cutMassAt r 0).toReal` (the source's
`E_{β_c,r}|K|`, Definition I.1.5) this file proves, with no derivative formula:

* `r ↦ cutoffProfile M.K r s` is continuous at every `r₀ > 0` (from `DifferentiableOn K (Ioi 0)`),
  hence every cut-off edge probability `r ↦ 1 - exp(-β_c J_r(e))` is continuous in `r`, and it is
  monotone in `r`.
* **Continuity from below** (`tendsto_cutMassReal_nhdsLT`): for `r₀ > 0`, `χ(r) → χ(r₀)` as
  `r ↑ r₀`, unconditionally (finiteness of `χ(r₀)` only for the real-valued form).  Monotone
  convergence for the cut-off law, via landed `PercLib.CriticalLRP.iSup_lintegral_clusterVol`.
* **Continuity from above** (`tendsto_cutMassReal_nhdsGT`): if `χ` is finite at some `r₁ > r₀`,
  then `χ(r) → χ(r₀)` as `r ↓ r₀`.  On this side the laws decrease and *every* edge of length
  `≤ r₀` changes its weight by the same amount `K r₀ - K r`, so the comparison is made on the mark
  space carrying all cut-off laws: the box-change event (a finite family of coordinate slabs
  inside one lattice ball) shrinks to the null set `boxNull`, and the escape event is controlled
  uniformly in `r` by the finite mean at `r₁`.
* **Two-sided continuity** (`continuousAt_cutMassReal`, `continuousOn_cutMassReal`) and the payoff
  `cutMassReal_absolutelyContinuousOn_of_finite`: the landed interval absolute-continuity theorem
  `SourceModelData.cutMassReal_absolutelyContinuousOn` applies with its `ContinuousOn` hypothesis
  discharged.  The Russo-type derivative premise `hgood` and the finite corner set remain explicit
  hypotheses of that theorem and are *not* proved here.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC
public import PercLib.CriticalLRP.CutoffLimit
public import PercLib.CriticalLRP.Analysis.BallAverage
public import PercLib.CriticalLRP.CountableProduct.Compatibility
public import PercLib.CriticalLRP.CountableProduct.Marks
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.Probability.ProductMeasure

/-! # Continuity of the cutoff cluster mass at every radius -/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

/-! ## Integrals over shrinking sets -/

/-- **Shrinking-set lemma.** For a finite measure `μ`, a measurable `f : α → ℝ≥0∞` with finite
integral, and a decreasing sequence of measurable sets whose intersection is `μ`-null, the integral
of `f` over the `n`-th set tends to `0`. -/
theorem tendsto_setLIntegral_toReal_of_antitone {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ a, f a ∂μ ≠ ⊤) {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hanti : Antitone s) (hinter : μ (⋂ n, s n) = 0) :
    Tendsto (fun n => (∫⁻ a in s n, f a ∂μ).toReal) atTop (𝓝 0) := by
  have hflt : ∀ᵐ a ∂μ, f a < ⊤ := ae_lt_top hf hfin
  have hfint : Integrable (fun a => (f a).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfin
  have hae : ∀ᵐ a ∂μ, ∃ N, a ∉ s N := by
    have h := measure_eq_zero_iff_ae_notMem.mp hinter
    simpa only [Set.mem_iInter, not_forall] using h
  have hlim : ∀ᵐ a ∂μ,
      Tendsto (fun n => (s n).indicator (fun a => (f a).toReal) a) atTop (𝓝 0) := by
    filter_upwards [hae] with a ha
    obtain ⟨N, hN⟩ := ha
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (Set.indicator_of_notMem (fun h => hN (hanti hn h)) _).symm
  have hbound : ∀ᶠ n : ℕ in atTop,
      ∀ᵐ a ∂μ, ‖(s n).indicator (fun a => (f a).toReal) a‖ ≤ (f a).toReal := by
    filter_upwards with n
    filter_upwards with a
    rw [Real.norm_eq_abs]
    by_cases ha : a ∈ s n
    · rw [Set.indicator_of_mem ha, abs_of_nonneg ENNReal.toReal_nonneg]
    · rw [Set.indicator_of_notMem ha, abs_zero]
      exact ENNReal.toReal_nonneg
  have hmain : Tendsto (fun n => ∫ a, (s n).indicator (fun a => (f a).toReal) a ∂μ)
      atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (F := fun n a =>
      (s n).indicator (fun a => (f a).toReal) a) (bound := fun a => (f a).toReal)
      (l := atTop) (μ := μ) ?_ hbound hfint hlim
    · simpa using this
    · filter_upwards with n
      exact (hf.ennreal_toReal.aemeasurable.indicator (hs n)).aestronglyMeasurable
  refine Tendsto.congr (fun n => ?_) hmain
  rw [integral_indicator (hs n)]
  exact integral_toReal (μ := μ.restrict (s n)) hf.aemeasurable.restrict
    (ae_restrict_of_ae hflt)



end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The cut-off profile is continuous in the cut-off radius -/

theorem abs_cutoffProfile_le (r s : ℝ) :
    |PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r s| ≤ |M.K s - M.K r| := by
  rw [PercLib.CriticalLRP.FiniteVolume.cutoffProfile]
  split_ifs with h
  · rfl
  · simp

theorem continuousAt_deriv_free_K (r0 : ℝ) (hr0 : 0 < r0) : ContinuousAt M.K r0 := by
  have h : DifferentiableAt ℝ M.K r0 :=
    M.K_diff.differentiableAt (isOpen_Ioi.mem_nhds hr0)
  exact h.continuousAt

/-- The cut-off profile is jointly continuous in the radius at every `r₀ > 0`. -/
theorem tendsto_cutoffProfile {ι : Type*} {l : Filter ι} {r : ι → ℝ} {r0 s : ℝ}
    (hr0 : 0 < r0) (hr : Tendsto r l (𝓝 r0)) :
    Tendsto (fun i => PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K (r i) s) l
      (𝓝 (PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r0 s)) := by
  have hK : ContinuousAt M.K r0 := M.continuousAt_deriv_free_K r0 hr0
  have hKr : Tendsto (fun i => M.K (r i)) l (𝓝 (M.K r0)) := hK.tendsto.comp hr
  rcases lt_trichotomy s r0 with h | h | h
  · -- `s < r₀`: eventually the left branch `K s - K r` applies
    have hev : ∀ᶠ i in l, s ≤ r i := hr.eventually (Ici_mem_nhds h)
    have h1 : Tendsto (fun i => M.K s - M.K (r i)) l
        (𝓝 (PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r0 s)) := by
      rw [PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le h.le]
      exact tendsto_const_nhds.sub hKr
    refine Tendsto.congr' (hev.mono ?_) h1
    intro i hi
    exact (PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le hi).symm
  · -- `s = r₀`: both branches are squeezed by `|K s - K r|`
    subst h
    have hlim : Tendsto (fun i => M.K s - M.K (r i)) l (𝓝 0) := by
      have h' := (tendsto_const_nhds : Tendsto (fun _ : ι => M.K s) l (𝓝 (M.K s))).sub hKr
      simpa using h'
    have habs : Tendsto (fun i => |PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K (r i) s|) l
        (𝓝 0) := by
      refine squeeze_zero (fun i => abs_nonneg _) (fun i => M.abs_cutoffProfile_le (r i) s) ?_
      simpa using hlim.abs
    have h0 : Tendsto
        (fun i => PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K (r i) s) l (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa [Real.norm_eq_abs] using habs
    have hval : PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K s s = 0 := by
      rw [PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le le_rfl]
      ring
    rwa [hval]
  · -- `r₀ < s`: eventually both profiles vanish
    have hev : ∀ᶠ i in l, r i < s := hr.eventually (Iio_mem_nhds h)
    refine Tendsto.congr' (hev.mono ?_) tendsto_const_nhds
    intro i hi
    rw [PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_lt h]
    exact (PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_lt hi).symm

/-! ## The cut-off edge probability -/

/-- `x ↦ 1 - exp(-(β x))` is monotone. -/
theorem one_sub_exp_mono {β : ℝ} (hβ : 0 ≤ β) {x y : ℝ} (hxy : x ≤ y) :
    1 - Real.exp (-(β * x)) ≤ 1 - Real.exp (-(β * y)) := by
  have h : Real.exp (-(β * y)) ≤ Real.exp (-(β * x)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  linarith

/-- The cut-off edge probability as a real number. -/
theorem cutProb_coe (r : ℝ) (e : Sym2 M.V) :
    ((M.cutProb r e : unitInterval) : ℝ) =
      1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) :=
  bernoulliEdgeProb_coe _ _ _ e

theorem cutKernel_diag (r : ℝ) (x : M.V) : M.cutKernel r (Sym2.mk x x) = 0 := by
  simp [SourceModelData.cutKernel, cutRadialSym, radialSym_mk]

theorem cutKernel_offdiag (r : ℝ) {x y : M.V} (h : x ≠ y) :
    M.cutKernel r (Sym2.mk x y) =
      PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y) := by
  simp [SourceModelData.cutKernel, cutRadialSym, radialSym_mk, h]

theorem cutProb_diag (r : ℝ) (x : M.V) :
    ((M.cutProb r (Sym2.mk x x) : unitInterval) : ℝ) = 0 := by
  rw [M.cutProb_coe, M.cutKernel_diag, mul_zero, neg_zero, Real.exp_zero]
  ring

/-- The cut-off edge probability is continuous in the cut-off radius. -/
theorem continuousAt_cutProb (r0 : ℝ) (hr0 : 0 < r0) (e : Sym2 M.V) :
    ContinuousAt (fun r => ((M.cutProb r e : unitInterval) : ℝ)) r0 := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      simp only [M.cutProb_diag]
      exact continuousAt_const
    · have key : ContinuousAt
          (fun r => PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y)) r0 := by
        exact M.tendsto_cutoffProfile (l := 𝓝 r0) (r := id) hr0 tendsto_id
      have hinner : ContinuousAt
          (fun r => -((M.betaCrit : ℝ) *
            PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) r0 :=
        (continuousAt_const.mul key).neg
      have h2 : ContinuousAt
          (fun r => 1 - Real.exp (-((M.betaCrit : ℝ) *
            PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))) r0 :=
        continuousAt_const.sub (Real.continuous_exp.continuousAt.comp hinner)
      exact h2.congr (Filter.Eventually.of_forall fun r => by
        change 1 - Real.exp (-((M.betaCrit : ℝ) *
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) =
            ((M.cutProb r (Sym2.mk x y) : unitInterval) : ℝ)
        rw [M.cutProb_coe, M.cutKernel_offdiag r hxy])

/-- The cut-off edge probability is monotone in the cut-off radius. -/
theorem cutProb_mono {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') (e : Sym2 M.V) :
    M.cutProb r e ≤ M.cutProb r' e := by
  refine Subtype.coe_le_coe.mp ?_
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutProb_diag, M.cutProb_diag]
    · rw [M.cutProb_coe, M.cutProb_coe, M.cutKernel_offdiag r hxy, M.cutKernel_offdiag r' hxy]
      have hle : PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y) ≤
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r' (M.S.dist x y) :=
        PercLib.CriticalLRP.FiniteVolume.cutoffProfile_mono_r M.K_antitone hr hr'
          (M.S.dist_pos hxy) h
      exact one_sub_exp_mono M.betaCrit.2 hle


/-! ## Monotone convergence from below: `χ(r) ↑ χ(r₀)` as `r ↑ r₀` -/

/-- The truncated law is the `edgeMeasure` of the cut-off edge probabilities. -/
theorem cutMassAt_eq_lintegral_edgeMeasure (r : ℝ) :
    M.cutMassAt r 0 = ∫⁻ ω, clusterVol ω 0 ∂(edgeMeasure (M.cutProb r)) := rfl

/-- **Continuity from below at the level of `ℝ≥0∞`.**  For a monotone sequence
`r n ↑ r₀` of positive cut-off radii, the cut-off cluster mass increases to its value at `r₀`.
No finiteness is needed. -/
theorem iSup_cutMassAt_nat {r : ℕ → ℝ} {r0 : ℝ} (hr : ∀ n, 0 < r n) (hr0 : 0 < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0)) :
    (⨆ n, M.cutMassAt (r n) 0) = M.cutMassAt r0 0 := by
  have h := PercLib.CriticalLRP.iSup_lintegral_clusterVol
    (p := fun n => M.cutProb (r n)) (q := M.cutProb r0) ?_ ?_ 0
  · simpa only [SourceModelData.cutMassAt_eq_lintegral_edgeMeasure] using h
  · intro n e
    exact M.cutProb_mono (hr n) (hr (n + 1)) (hmono n) e
  · intro e
    exact (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim

/-- Monotone convergence of the cut-off cluster mass along a sequence `r n ↑ r₀`, in `ℝ≥0∞`. -/
theorem tendsto_cutMassAt_nat {r : ℕ → ℝ} {r0 : ℝ} (hr : ∀ n, 0 < r n) (hr0 : 0 < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0)) :
    Tendsto (fun n => M.cutMassAt (r n) 0) atTop (𝓝 (M.cutMassAt r0 0)) := by
  rw [← M.iSup_cutMassAt_nat hr hr0 hmono hlim]
  exact tendsto_atTop_iSup (monotone_nat_of_le_succ fun n =>
    M.cutMassAt_mono (hr n) (hr (n + 1)) (hmono n))

/-- Monotone convergence of the **real** cut-off cluster mass along `r n ↑ r₀`, assuming the
mass is finite at the limit point. -/
theorem tendsto_cutMassReal_nat {r : ℕ → ℝ} {r0 : ℝ} (hr : ∀ n, 0 < r n) (hr0 : 0 < r0)
    (hmono : ∀ n, r n ≤ r (n + 1)) (hlim : Tendsto r atTop (𝓝 r0))
    (hfin : M.cutMassAt r0 0 ≠ ⊤) :
    Tendsto (fun n => M.cutMassReal (r n)) atTop (𝓝 (M.cutMassReal r0)) := by
  exact (ENNReal.tendsto_toReal hfin).comp (M.tendsto_cutMassAt_nat hr hr0 hmono hlim)

/-- Monotonicity of the real cut-off mass, in the form needed for the one-sided limit. -/
theorem cutMassReal_le_of_le {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    (hfin : M.cutMassAt r' 0 ≠ ⊤) : M.cutMassReal r ≤ M.cutMassReal r' := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  refine ENNReal.toReal_mono hfin (M.cutMassAt_mono hr hr' hrr')

/-- **Left continuity of the cut-off cluster mass at every positive radius** at which the mass is
finite: `χ(r) → χ(r₀)` as `r ↑ r₀`.  Since `χ` is nondecreasing this is the statement that `χ`
has no downward jump, and it holds with no hypothesis on the norm or on the corner set. -/
theorem tendsto_cutMassReal_nhdsLT (r0 : ℝ) (hr0 : 0 < r0)
    (hfin : M.cutMassAt r0 0 ≠ ⊤) :
    Tendsto M.cutMassReal (𝓝[<] r0) (𝓝 (M.cutMassReal r0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- the approximating sequence `r n = r₀ - r₀/(n+2)`
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
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop := by
        exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop h1
    simp only [hrdef]
    simpa using tendsto_const_nhds.sub h0
  have hseq := M.tendsto_cutMassReal_nat hr hr0 hmono hlim hfin
  have hev : ∀ᶠ n : ℕ in atTop, M.cutMassReal r0 - ε < M.cutMassReal (r n) :=
    (tendsto_order.1 hseq).1 (M.cutMassReal r0 - ε) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- the set of radii in `(r N, r₀)` works
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
  have hN' : M.cutMassReal r0 - ε < M.cutMassReal (r N) := hN N le_rfl
  have hfinx : M.cutMassAt x 0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin
      (M.cutMassAt_mono (lt_of_lt_of_le (hr N) hx1.le) hr0 hx2.le)
  have h1 : M.cutMassReal (r N) ≤ M.cutMassReal x :=
    M.cutMassReal_le_of_le (hr N) hx1.le hfinx
  have h2 : M.cutMassReal x ≤ M.cutMassReal r0 :=
    M.cutMassReal_le_of_le (lt_of_lt_of_le (hr N) hx1.le) hx2.le hfin
  have h3 : M.cutMassReal r0 - ε < M.cutMassReal x := lt_of_lt_of_le hN' h1
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith




variable (M : SourceModelData)

/-! ## The mark space -/

/-- The cut-off cluster mass as an integral over the mark space carrying every cut-off law. -/
theorem cutMassAt_eq_mark (r : ℝ) :
    M.cutMassAt r 0 =
      ∫⁻ u : Sym2 M.V → ℝ, clusterVol (atParameter (M.cutProb r) u) 0 ∂(markMeasure M.V) := by
  have hlaw : M.cutMassAt r 0 =
      ∫⁻ ω, clusterVol ω 0 ∂(edgeMeasure (M.cutProb r)) := rfl
  rw [hlaw, ← markMeasure_map_atParameter]
  rw [lintegral_map (measurable_clusterVol 0) (measurable_atParameter _)]

/-- A single uniform mark has probability zero of sitting exactly at its threshold. -/
theorem markMeasure_coord_singleton (e : Sym2 M.V) (c : ℝ) :
    markMeasure M.V {u : Sym2 M.V → ℝ | u e = c} = 0 := by
  have hset : {u : Sym2 M.V → ℝ | u e = c} =
      Set.pi ({e} : Finset (Sym2 M.V)) (fun i => if i = e then {c} else Set.univ) := by
    ext u
    constructor
    · intro hu i hi
      have hi' : i = e := by simpa using hi
      subst hi'
      simpa using hu
    · intro hu
      have h1 := hu e (Finset.mem_singleton_self e)
      simpa using h1
  rw [hset, markMeasure, Measure.infinitePi_pi]
  · have h1 : unif ({c} : Set ℝ) = 0 := by
      rw [unif, Measure.restrict_apply (measurableSet_singleton c)]
      exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    simpa using h1
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    simp

/-! ## The escape event on the mark space -/


theorem measurableSet_markEscape (r R : ℝ) : MeasurableSet (M.markEscape r R) := by
  have h : M.markEscape r R =
      ⋃ x : M.V, {u : Sym2 M.V → ℝ |
        x ∉ M.ball R ∧ Connects (atParameter (M.cutProb r) u) 0 x} := by
    ext u
    simp only [SourceModelData.markEscape, Set.mem_iUnion]
    exact exists_congr fun x => by simp
  rw [h]
  refine MeasurableSet.iUnion fun x => ?_
  by_cases hx : x ∈ M.ball R
  · have h0 : {u : Sym2 M.V → ℝ |
        x ∉ M.ball R ∧ Connects (atParameter (M.cutProb r) u) 0 x} = ∅ := by
      ext u
      simp [hx]
    rw [h0]
    exact MeasurableSet.empty
  · have h1 : {u : Sym2 M.V → ℝ | x ∉ M.ball R ∧
        Connects (atParameter (M.cutProb r) u) 0 x} =
        (atParameter (M.cutProb r)) ⁻¹' {ω : Config M.V | Connects ω (0 : M.V) x} := by
      ext u
      simp [hx]
    rw [h1]
    exact (measurableSet_connects (0 : M.V) x).preimage (measurable_atParameter _)

theorem markEscape_antitone {r : ℝ} {R R' : ℝ} (h : R ≤ R') :
    M.markEscape r R' ⊆ M.markEscape r R := by
  intro u hu
  obtain ⟨x, hx, hconn⟩ := hu
  exact ⟨x, fun hmem => hx (PercLib.CriticalLRP.BallAverage.ball_mono M h hmem), hconn⟩

/-- A finite set of lattice points is contained in some lattice ball. -/
theorem exists_ball_subset_of_finite {S : Set M.V} (hS : S.Finite) :
    ∃ N : ℕ, S ⊆ M.ball (N : ℝ) := by
  classical
  refine ⟨hS.toFinset.sup (fun x => ⌈M.S.ρ (toVec x)⌉₊), fun x hx => ?_⟩
  have hx' : x ∈ hS.toFinset := by simpa using hx
  have h1 : ⌈M.S.ρ (toVec x)⌉₊ ≤ hS.toFinset.sup (fun x => ⌈M.S.ρ (toVec x)⌉₊) :=
    Finset.le_sup (f := fun x => ⌈M.S.ρ (toVec x)⌉₊) hx'
  have h2 : M.S.ρ (toVec x) ≤ (⌈M.S.ρ (toVec x)⌉₊ : ℝ) := Nat.le_ceil _
  change M.S.ρ (toVec x) ≤ ((hS.toFinset.sup (fun x => ⌈M.S.ρ (toVec x)⌉₊) : ℕ) : ℝ)
  exact h2.trans (by exact_mod_cast h1)

/-- If the cluster of the origin leaves every lattice ball then it is infinite. -/
theorem clusterVol_eq_top_of_forall_mem_markEscape {r : ℝ} {u : Sym2 M.V → ℝ}
    (h : ∀ n : ℕ, u ∈ M.markEscape r (n : ℝ)) :
    clusterVol (atParameter (M.cutProb r) u) 0 = ⊤ := by
  have hinf : (cluster (atParameter (M.cutProb r) u) (0 : M.V)).Infinite := by
    intro hfin
    obtain ⟨N, hN⟩ := M.exists_ball_subset_of_finite hfin
    obtain ⟨x, hx, hconn⟩ := h N
    exact hx (hN (mem_cluster_iff.mpr hconn))
  have := (inInfiniteCluster_iff (atParameter (M.cutProb r) u) 0).mpr hinf
  simpa only [InInfiniteCluster] using this

/-- The intersection over all radii of the escape events is null, provided the cut-off mass at `r`
is finite. -/
theorem measure_iInter_markEscape_eq_zero (r : ℝ) (hfin : M.cutMassAt r 0 ≠ ⊤) :
    markMeasure M.V (⋂ n : ℕ, M.markEscape r (n : ℝ)) = 0 := by
  have hmeas : Measurable fun u : Sym2 M.V → ℝ =>
      clusterVol (atParameter (M.cutProb r) u) 0 :=
    (measurable_clusterVol (0 : M.V)).comp (measurable_atParameter _)
  have h1 : ∫⁻ u : Sym2 M.V → ℝ,
      clusterVol (atParameter (M.cutProb r) u) 0 ∂(markMeasure M.V) ≠ ⊤ := by
    rwa [← M.cutMassAt_eq_mark]
  have h2 : ∀ᵐ u ∂(markMeasure M.V),
      clusterVol (atParameter (M.cutProb r) u) 0 ≠ ⊤ := by
    filter_upwards [ae_lt_top hmeas h1] with u hu
    exact ne_of_lt hu
  have h3 : ∀ᵐ u ∂(markMeasure M.V), u ∉ ⋂ n : ℕ, M.markEscape r (n : ℝ) := by
    filter_upwards [h2] with u hu hmem
    exact hu (M.clusterVol_eq_top_of_forall_mem_markEscape fun n =>
      Set.mem_iInter.mp hmem n)
  exact measure_eq_zero_iff_ae_notMem.mpr h3

/-! ## Clusters inside a finite box -/


/-- Inside a box on whose edges two configurations agree, a cluster contained in the box is
contained in the other configuration's cluster. -/
theorem cluster_subset_of_eq_on_box {R : ℝ} {ω ω' : Config M.V}
    (hagree : ∀ e ∈ M.boxEdges R, e ∈ ω → e ∈ ω')
    (hsub : cluster ω (0 : M.V) ⊆ M.ball R) :
    cluster ω (0 : M.V) ⊆ cluster ω' (0 : M.V) := by
  intro y hy
  rw [mem_cluster_iff] at hy
  have hy' : Relation.ReflTransGen (openGraph ω).Adj (0 : M.V) y :=
    (SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω) (0 : M.V) y).mp hy
  clear hy
  have hmain : Relation.ReflTransGen (openGraph ω').Adj (0 : M.V) y := by
    induction hy' with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        rename_i b c
        have hb : b ∈ M.ball R :=
          hsub (mem_cluster_iff.mpr
            ((SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω) (0 : M.V) b).mpr hab))
        have hc : c ∈ M.ball R :=
          hsub (mem_cluster_iff.mpr
            ((SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω) (0 : M.V) c).mpr
              (Relation.ReflTransGen.tail hab hbc)))
        have hedge : s(b, c) ∈ ω := (openGraph_adj.mp hbc).2
        have hbox : s(b, c) ∈ M.boxEdges R := by
          rw [SourceModelData.boxEdges, Finset.mem_sym2_iff]
          intro a ha
          have ha' : a = b ∨ a = c := by simpa using ha
          rcases ha' with rfl | rfl
          · simpa using hb
          · simpa using hc
        have hopen : s(b, c) ∈ ω' := hagree _ hbox hedge
        exact Relation.ReflTransGen.tail ih (openGraph_adj.mpr ⟨hbc.ne, hopen⟩)
  exact mem_cluster_iff.mpr
    ((SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω') (0 : M.V) y).mpr hmain)


/-! ## The pointwise comparison of cluster volumes -/

theorem clusterVol_le_of_cluster_subset {ω ω' : Config M.V} {v : M.V}
    (h : cluster ω v ⊆ cluster ω' v) : clusterVol ω v ≤ clusterVol ω' v := by
  classical
  rw [clusterVol_eq_tsum ω v, clusterVol_eq_tsum ω' v]
  refine ENNReal.tsum_le_tsum fun w => ?_
  by_cases hw : w ∈ cluster ω v
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (h hw)]
  · rw [Set.indicator_of_notMem hw]
    exact bot_le


theorem measurableSet_markBoxChange (r0 r R : ℝ) :
    MeasurableSet (M.markBoxChange r0 r R) := by
  have h : M.markBoxChange r0 r R = ⋃ e ∈ M.boxEdges R,
      {u : Sym2 M.V → ℝ | (M.cutProb r0 e : ℝ) ≤ u e ∧ u e < (M.cutProb r e : ℝ)} := by
    ext u
    simp only [SourceModelData.markBoxChange, Set.mem_iUnion, exists_prop]
    exact exists_congr fun e => by simp
  rw [h]
  refine MeasurableSet.biUnion (M.boxEdges R).countable_toSet fun e _ => ?_
  exact (measurableSet_le measurable_const (measurable_pi_apply e)).inter
    (measurableSet_lt (measurable_pi_apply e) measurable_const)

theorem lt_cutProb_r0_of_notMem_markBoxChange {r0 r R : ℝ}
    {u : Sym2 M.V → ℝ} (hu : u ∉ M.markBoxChange r0 r R)
    {e : Sym2 M.V} (he : e ∈ M.boxEdges R) (hlt : u e < (M.cutProb r e : ℝ)) :
    u e < (M.cutProb r0 e : ℝ) := by
  by_contra hcon
  exact hu ⟨e, he, not_lt.mp hcon, hlt⟩

/-- **Pointwise comparison.**  Off the box-change and escape events the cut-off cluster at the
larger radius `r` is no larger than at `r₀`. -/
theorem clusterVol_le_of_notMem {r0 r R : ℝ}
    {u : Sym2 M.V → ℝ} (hbox : u ∉ M.markBoxChange r0 r R)
    (hesc : u ∉ M.markEscape r R) :
    clusterVol (atParameter (M.cutProb r) u) 0 ≤
      clusterVol (atParameter (M.cutProb r0) u) 0 := by
  refine M.clusterVol_le_of_cluster_subset ?_
  refine M.cluster_subset_of_eq_on_box (R := R) ?_ ?_
  · intro e he hmem
    exact M.lt_cutProb_r0_of_notMem_markBoxChange hbox he hmem
  · intro y hy
    by_contra hcon
    exact hesc ⟨y, hcon, mem_cluster_iff.mpr hy⟩

/-! ## Monotonicity of the two error events -/

theorem markBoxChange_mono {r0 r r' R : ℝ} (_hr0 : 0 < r0) (hr : 0 < r) (hr' : 0 < r')
    (h : r ≤ r') : M.markBoxChange r0 r R ⊆ M.markBoxChange r0 r' R := by
  rintro u ⟨e, he, h1, h2⟩
  exact ⟨e, he, h1, lt_of_lt_of_le h2 (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr' h e))⟩

theorem markEscape_mono {r r' R : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') :
    M.markEscape r R ⊆ M.markEscape r' R := by
  rintro u ⟨x, hx, hconn⟩
  refine ⟨x, hx, connects_mono (fun e he => ?_) hconn⟩
  exact lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr' h e))

theorem clusterVol_atParameter_mono {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r')
    (u : Sym2 M.V → ℝ) (o : M.V) :
    clusterVol (atParameter (M.cutProb r) u) o ≤
      clusterVol (atParameter (M.cutProb r') u) o :=
  clusterVol_mono (fun e he =>
    lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (M.cutProb_mono hr hr' h e))) o

/-! ## The box-change events shrink to a null set -/


theorem measure_boxNull (r0 R : ℝ) : markMeasure M.V (M.boxNull r0 R) = 0 := by
  have h : M.boxNull r0 R = ⋃ e : Sym2 M.V, ⋃ (_ : e ∈ M.boxEdges R),
      {u : Sym2 M.V → ℝ | u e = (M.cutProb r0 e : ℝ)} := by
    ext u
    simp only [SourceModelData.boxNull, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨e, he, hc⟩
      exact ⟨e, he, hc⟩
    · rintro ⟨e, he, hc⟩
      exact ⟨e, he, hc⟩
  rw [h]
  refine measure_iUnion_null fun e => ?_
  by_cases he : e ∈ M.boxEdges R
  · simp only [he, Set.iUnion_true]
    exact M.markMeasure_coord_singleton e _
  · simp only [he, Set.iUnion_false]
    exact measure_empty

/-- Along a strictly decreasing family of radii, the intersection of the box-change events is
contained in the null set `boxNull`. -/
theorem iInter_markBoxChange_subset {r : ℕ → ℝ} {r0 R : ℝ} (hr0 : 0 < r0)
    (hlim : Tendsto r atTop (𝓝 r0)) :
    (⋂ n : ℕ, M.markBoxChange r0 (r n) R) ⊆ M.boxNull r0 R := by
  classical
  intro u hu
  by_contra hcon
  have hwit : ∀ e ∈ M.boxEdges R, ∃ N : ℕ,
      ∀ n ≥ N, ¬((M.cutProb r0 e : ℝ) ≤ u e ∧ u e < (M.cutProb (r n) e : ℝ)) := by
    intro e he
    by_cases hlt : u e < (M.cutProb r0 e : ℝ)
    · refine ⟨0, fun n _ h => ?_⟩
      exact absurd h.1 (not_le.mpr hlt)
    · have hne : u e ≠ (M.cutProb r0 e : ℝ) := fun h => hcon ⟨e, he, h⟩
      have hgt : (M.cutProb r0 e : ℝ) < u e := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
      have htend : Tendsto (fun n => ((M.cutProb (r n) e : unitInterval) : ℝ)) atTop
          (𝓝 ((M.cutProb r0 e : ℝ))) :=
        (M.continuousAt_cutProb r0 hr0 e).tendsto.comp hlim
      have hev : ∀ᶠ n in atTop, ((M.cutProb (r n) e : unitInterval) : ℝ) < u e :=
        (tendsto_order.1 htend).2 _ hgt
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact ⟨N, fun n hn h => absurd h.2 (not_lt.mpr (le_of_lt (hN n hn)))⟩
  set N : ℕ := (M.boxEdges R).attach.sup
    (fun e => Classical.choose (hwit e.1 e.2)) with hN
  have hNspec : ∀ e ∈ M.boxEdges R,
      ¬((M.cutProb r0 e : ℝ) ≤ u e ∧ u e < (M.cutProb (r N) e : ℝ)) := by
    intro e he
    have h1 : Classical.choose (hwit e he) ≤ N := by
      rw [hN]
      exact Finset.le_sup (f := fun e : {x // x ∈ M.boxEdges R} =>
        Classical.choose (hwit e.1 e.2)) (Finset.mem_attach _ ⟨e, he⟩)
    exact Classical.choose_spec (hwit e he) N h1
  obtain ⟨e, he, h1, h2⟩ := Set.mem_iInter.mp hu N
  exact hNspec e he ⟨h1, h2⟩



theorem measurable_markVol (r : ℝ) : Measurable (M.markVol r) :=
  (measurable_clusterVol (0 : M.V)).comp (measurable_atParameter _)

/-! ## The increment bound and continuity from above -/

theorem clusterVol_le_add_indicators {r0 r r1 R : ℝ} (hr : 0 < r) (hr1 : 0 < r1)
    (h11 : r ≤ r1) (u : Sym2 M.V → ℝ) :
    M.markVol r u ≤ M.markVol r0 u +
        (M.markBoxChange r0 r R).indicator (M.markVol r1) u +
        (M.markEscape r1 R).indicator (M.markVol r1) u := by
  have h1 : M.markVol r u ≤ M.markVol r1 u :=
    M.clusterVol_atParameter_mono hr hr1 h11 u 0
  by_cases hbox : u ∈ M.markBoxChange r0 r R
  · rw [Set.indicator_of_mem hbox]
    have h2 : M.markVol r1 u ≤ M.markVol r0 u + M.markVol r1 u := le_add_self
    have h3 : M.markVol r0 u + M.markVol r1 u ≤
        M.markVol r0 u + M.markVol r1 u +
          (M.markEscape r1 R).indicator (M.markVol r1) u := le_self_add
    exact le_trans (le_trans h1 h2) h3
  · rw [Set.indicator_of_notMem hbox]
    simp only [add_zero]
    by_cases hesc : u ∈ M.markEscape r1 R
    · rw [Set.indicator_of_mem hesc]
      have h2 : M.markVol r1 u ≤ M.markVol r0 u + M.markVol r1 u := le_add_self
      exact le_trans h1 h2
    · rw [Set.indicator_of_notMem hesc]
      have hesc' : u ∉ M.markEscape r R := fun h => hesc (M.markEscape_mono hr hr1 h11 h)
      simpa [SourceModelData.markVol] using M.clusterVol_le_of_notMem hbox hesc'

theorem measurable_clusterVol_atParameter (r : ℝ) :
    Measurable fun u : Sym2 M.V → ℝ => clusterVol (atParameter (M.cutProb r) u) 0 :=
  (measurable_clusterVol (0 : M.V)).comp (measurable_atParameter _)


/-- **Increment bound across the window.**  For `r₀ < r ≤ r₁` the cut-off mass at `r` exceeds the
mass at `r₀` by at most the integral of the `r₁`-cluster volume over the box-change and escape
marks. -/
theorem cutMassAt_le_add {r0 r r1 R : ℝ} (hr : 0 < r) (hr1 : 0 < r1)
    (h11 : r ≤ r1) :
    M.cutMassAt r 0 ≤ M.cutMassAt r0 0 +
      (∫⁻ u in M.markBoxChange r0 r R, M.markVol r1 u ∂(markMeasure M.V)) +
      (∫⁻ u in M.markEscape r1 R, M.markVol r1 u ∂(markMeasure M.V)) := by
  have hmono : ∫⁻ u, M.markVol r u ∂(markMeasure M.V) ≤
      ∫⁻ u, (M.markVol r0 u +
        (M.markBoxChange r0 r R).indicator (M.markVol r1) u +
        (M.markEscape r1 R).indicator (M.markVol r1) u) ∂(markMeasure M.V) :=
    lintegral_mono fun u => M.clusterVol_le_add_indicators hr hr1 h11 u
  have hmeas2 : Measurable fun u : Sym2 M.V → ℝ =>
      M.markVol r0 u + (M.markBoxChange r0 r R).indicator (M.markVol r1) u :=
    (M.measurable_markVol r0).add ((M.measurable_markVol r1).indicator
      (M.measurableSet_markBoxChange r0 r R))
  rw [lintegral_add_left hmeas2, lintegral_add_left (M.measurable_markVol r0),
    lintegral_indicator (M.measurableSet_markBoxChange r0 r R) (M.markVol r1),
    lintegral_indicator (M.measurableSet_markEscape r1 R) (M.markVol r1)] at hmono
  rw [M.cutMassAt_eq_mark r, M.cutMassAt_eq_mark r0]
  exact hmono

/-- A monotone function on a right-neighbourhood of `r₀` which tends to `0` along one decreasing
sequence tends to `0`. -/
theorem tendsto_zero_of_le_seq {g : ℝ → ℝ} {r : ℕ → ℝ} {r0 : ℝ}
    (hmono : ∀ x y, r0 < x → x ≤ y → g x ≤ g y) (hnn : ∀ x, 0 ≤ g x)
    (hr : ∀ n, r0 < r n) (hseq : Tendsto (fun n => g (r n)) atTop (𝓝 0)) :
    Tendsto g (𝓝[>] r0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hseq) ε hε
  have hN' : g (r N) < ε := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hnn (r N))] at h
  refine ⟨r N - r0, by linarith [hr N], ?_⟩
  intro x hx hdist
  rw [Real.dist_eq] at hdist
  have hxN : x ≤ r N := by
    rw [abs_lt] at hdist
    linarith [hdist.2]
  have hle : g x ≤ g (r N) := hmono x (r N) hx hxN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn x)]
  exact lt_of_le_of_lt hle hN'


/-- The box-change integral is antitone in the radius, hence continuity from above follows from
convergence along one sequence. -/
theorem tendsto_boxIntegral (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (_hr1 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) (R : ℝ) :
    Tendsto (fun r => (∫⁻ u in M.markBoxChange r0 r R, M.markVol r1 u
      ∂(markMeasure M.V)).toReal) (𝓝[>] r0) (𝓝 0) := by
  -- the decreasing sequence `r n = r0 + r0/(n+2)`
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
  -- intersection of the box-change events along the sequence is null
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
  have hnull : markMeasure M.V (⋂ n : ℕ, M.markBoxChange r0 (rseq n) R) = 0 := by
    refine measure_mono_null (M.iInter_markBoxChange_subset hr0 hseq) (M.measure_boxNull r0 R)
  have hInt : (∫⁻ a, M.markVol r1 a ∂(markMeasure M.V)) = M.cutMassAt r1 0 := by
    rw [M.cutMassAt_eq_mark r1]
    rfl
  have hconv : Tendsto (fun n : ℕ => (∫⁻ u in M.markBoxChange r0 (rseq n) R,
      M.markVol r1 u ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
    tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V) (f := M.markVol r1)
      (M.measurable_markVol r1) (by rw [hInt]; exact hfin)
      (fun n => M.measurableSet_markBoxChange r0 (rseq n) R) hanti hnull
  refine tendsto_zero_of_le_seq (r := rseq) ?_ ?_ hrpos hconv
  · intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le (lt_trans hr0 hx) hxy
    have hsub : M.markBoxChange r0 x R ⊆ M.markBoxChange r0 y R :=
      M.markBoxChange_mono hr0 (lt_trans hr0 hx) hy hxy
    have hfin' : (∫⁻ u in M.markBoxChange r0 y R, M.markVol r1 u
        ∂(markMeasure M.V)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_set (Set.subset_univ _))
      simpa using hInt.symm ▸ hfin
    have hle : (∫⁻ u in M.markBoxChange r0 x R, M.markVol r1 u
          ∂(markMeasure M.V)) ≤
        ∫⁻ u in M.markBoxChange r0 y R, M.markVol r1 u ∂(markMeasure M.V) :=
      lintegral_mono_set hsub
    exact ENNReal.toReal_mono hfin' hle
  · intro x
    exact ENNReal.toReal_nonneg


/-- **Continuity from above of the cut-off cluster mass.**  If the cut-off mass is finite at some
strictly larger radius `r₁ > r₀`, then `χ(r) → χ(r₀)` as `r ↓ r₀`.

The proof compares the two cut-off laws on one mark space.  The box-change event is a finite
family of coordinate slabs which shrink to the null set `boxNull`; the escape event is controlled
uniformly in `r` by the finite mean at `r₁`. -/
theorem tendsto_cutMassReal_nhdsGT (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) :
    Tendsto M.cutMassReal (𝓝[>] r0) (𝓝 (M.cutMassReal r0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- the unrestricted integral of the comparison cluster volume
  have hInt : (∫⁻ a, M.markVol r1 a ∂(markMeasure M.V)) = M.cutMassAt r1 0 := by
    rw [M.cutMassAt_eq_mark r1]
    rfl
  -- Step 1: choose a lattice ball on which the escape term is small
  have hesc_tend : Tendsto (fun n : ℕ => (∫⁻ u in M.markEscape r1 (n : ℝ),
      M.markVol r1 u ∂(markMeasure M.V)).toReal) atTop (𝓝 0) :=
    tendsto_setLIntegral_toReal_of_antitone (μ := markMeasure M.V) (f := M.markVol r1)
      (M.measurable_markVol r1) (by rw [hInt]; exact hfin)
      (fun n => M.measurableSet_markEscape r1 (n : ℝ))
      (fun n m hnm => M.markEscape_antitone (by exact_mod_cast hnm))
      (M.measure_iInter_markEscape_eq_zero r1 hfin)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hesc_tend) (ε / 2) (by linarith)
  have hN' : (∫⁻ u in M.markEscape r1 (N : ℝ), M.markVol r1 u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h := hN N le_rfl
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h
  -- Step 2: on a right-neighbourhood the box-change term is small
  have hbox := M.tendsto_boxIntegral r0 hr0 hr1 hfin (N : ℝ)
  obtain ⟨δ, hδ, hspec⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hbox) (ε / 2) (by linarith)
  refine ⟨min δ (r1 - r0), lt_min hδ (by linarith), ?_⟩
  intro r hr hdist
  rw [Real.dist_eq] at hdist
  have hr1' : r ≤ r1 := by
    rw [abs_lt] at hdist
    linarith [hdist.2, min_le_right δ (r1 - r0)]
  have hrpos : 0 < r := lt_trans hr0 hr
  have hboxsmall : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), M.markVol r1 u
      ∂(markMeasure M.V)).toReal < ε / 2 := by
    have h2 : dist (∫⁻ u in M.markBoxChange r0 r (N : ℝ), M.markVol r1 u
        ∂(markMeasure M.V)).toReal 0 < ε / 2 := by
      refine hspec hr ?_
      rw [Real.dist_eq]
      exact lt_of_lt_of_le hdist (min_le_left δ (r1 - r0))
    simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h2
  -- Step 3: the increment bound in real numbers
  have hfr : M.cutMassAt r 0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.cutMassAt_mono hrpos (lt_trans hr0 hr1) hr1')
  have hfr0 : M.cutMassAt r0 0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.cutMassAt_mono hr0 (lt_trans hr0 hr1) hr1.le)
  have hUniv : (∫⁻ u in (Set.univ : Set (Sym2 M.V → ℝ)), M.markVol r1 u
      ∂(markMeasure M.V)) ≠ ⊤ := by
    rw [Measure.restrict_univ, hInt]
    exact hfin
  have hboxfin : (∫⁻ u in M.markBoxChange r0 r (N : ℝ), M.markVol r1 u
      ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hUniv (lintegral_mono_set (Set.subset_univ _))
  have hescfin : (∫⁻ u in M.markEscape r1 (N : ℝ), M.markVol r1 u
      ∂(markMeasure M.V)) ≠ ⊤ :=
    ne_top_of_le_ne_top hUniv (lintegral_mono_set (Set.subset_univ _))
  have hincr := M.cutMassAt_le_add (r0 := r0) (r := r) (r1 := r1) (R := (N : ℝ)) hrpos
    (lt_trans hr0 hr1) hr1'
  have hsum : M.cutMassAt r0 0 +
      (∫⁻ u in M.markBoxChange r0 r (N : ℝ), M.markVol r1 u ∂(markMeasure M.V)) +
      (∫⁻ u in M.markEscape r1 (N : ℝ), M.markVol r1 u ∂(markMeasure M.V)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfr0, hboxfin⟩, hescfin⟩
  have hreal : M.cutMassReal r ≤ M.cutMassReal r0 +
      (∫⁻ u in M.markBoxChange r0 r (N : ℝ), M.markVol r1 u
        ∂(markMeasure M.V)).toReal +
      (∫⁻ u in M.markEscape r1 (N : ℝ), M.markVol r1 u
        ∂(markMeasure M.V)).toReal := by
    have h := ENNReal.toReal_mono hsum hincr
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfr0, hboxfin⟩) hescfin,
      ENNReal.toReal_add hfr0 hboxfin] at h
  -- Step 4: conclude
  have hmono : M.cutMassReal r0 ≤ M.cutMassReal r :=
    M.cutMassReal_le_of_le hr0 hr.le hfr
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith


/-- **Two-sided continuity of the cut-off cluster mass.**  Finiteness of the mean at a strictly
larger radius gives continuity at `r₀` from both sides. -/
theorem continuousAt_cutMassReal (r0 : ℝ) (hr0 : 0 < r0) {r1 : ℝ} (hr1 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) :
    ContinuousAt M.cutMassReal r0 := by
  have hfin0 : M.cutMassAt r0 0 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (M.cutMassAt_mono hr0 (lt_trans hr0 hr1) hr1.le)
  have hleft := M.tendsto_cutMassReal_nhdsLT r0 hr0 hfin0
  have hright := M.tendsto_cutMassReal_nhdsGT r0 hr0 hr1 hfin
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

/-- **Continuity of the cut-off cluster mass on a compact radius window**, from finiteness of the
mean at any strictly larger radius.  This is the `ContinuousOn` hypothesis of the interval
absolute-continuity theorem `IntervalAC.abs_sub_le_integral_of_finite_exception`. -/
theorem continuousOn_cutMassReal {a b b' : ℝ} (ha : 0 < a) (hbb' : b < b')
    (hfin : M.cutMassAt b' 0 ≠ ⊤) :
    ContinuousOn M.cutMassReal (Set.Icc a b) := by
  intro x hx
  exact (M.continuousAt_cutMassReal x (lt_of_lt_of_le ha hx.1)
    (lt_of_le_of_lt hx.2 hbb') hfin).continuousWithinAt


/-- **Payoff: interval absolute continuity of the cut-off cluster mass.**  The endpoint continuity
proved above supplies the `ContinuousOn` hypothesis of
`SourceModelData.cutMassReal_absolutelyContinuousOn`, so the finite-exception FTC for `χ` holds
with no continuity assumption left over (the Russo-type derivative bound stays an explicit
premise). -/
theorem cutMassReal_absolutelyContinuousOn_of_finite {a b b' : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbb' : b < b') (hfin : M.cutMassAt b' 0 ≠ ⊤) {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hDfin : (M.cornerRadii ∩ Set.Ioo a b).Finite)
    (hgood : ∀ u ∈ Set.Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    AbsolutelyContinuousOnInterval M.cutMassReal a b :=
  M.cutMassReal_absolutelyContinuousOn hab
    (M.continuousOn_cutMassReal ha hbb' hfin) hgcont hDfin hgood

end SourceModelData

end PercLib.CriticalLRP.Orchestration

set_option linter.hashCommand false

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.tendsto_setLIntegral_toReal_of_antitone
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMassReal_nhdsLT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.markMeasure_coord_singleton
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measure_iInter_markEscape_eq_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cluster_subset_of_eq_on_box
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measure_boxNull
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iInter_markBoxChange_subset
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_le_add
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_boxIntegral
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMassReal_nhdsGT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_cutMassReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousOn_cutMassReal
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_absolutelyContinuousOn_of_finite
