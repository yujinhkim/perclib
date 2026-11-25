/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**The uniform convergence theorem for regularly varying functions
(Bingham–Goldie–Teugels, Theorem 1.2.1), measurable case.**

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), p. 25,
uses exactly this theorem: "if this holds and `f` is measurable then in fact
there must exist `α ∈ ℝ`, known as the index of `f`, such that
`lim f (λ x)/f x = λ^α` for every `λ > 0`, and moreover this convergence must
hold uniformly for `λ` in compact subsets of `(0,∞)` [24, Theorem 1.2.1]."

The index is part of the definition `RegularlyVaryingAtTop f α` used in this
development, so the analytical content formalised here is the *uniformity*.

Main results of this file:

* `exists_forall_exists_add_mem` – the Kestelman–Borwein–Ditor theorem
  (measurable case), the sole measure-theoretic input;
* `tendsto_uniform_additive` – uniform convergence on compact parameter sets
  for a measurable `H` with `H (x+u) - H x → 0` for every fixed `u`; the proof
  is the Csiszár–Erdős argument (the "fourth proof" in Bingham–Goldie–Teugels,
  quoted in Bingham–Ostaszewski, *Duality and the Kestelman–Borwein–Ditor
  theorem*, §4): bad points of a compact interval are moved by a null sequence
  into a positive-measure set, which the KBD theorem hits infinitely often;
* `tendsto_uniformly_ratio_of_regularlyVarying` – the multiplicative form
  (BGT Theorem 1.2.1) for `RegularlyVaryingAtTop`;
* `hasLocalUniformRatio_of_regularlyVarying` – the one-sided compact form
  consumed by `HasPotterBounds`.
-/
module

public import PercLib.CriticalLRP.Analysis.KaramataMain
public import PercLib.CriticalLRP.Analysis.RVAlgebra
public import PercLib.CriticalLRP.Analysis.PotterBounded

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal Pointwise BigOperators

namespace PercLib.CriticalLRP.Analysis

/-! ### Two set identities for translations -/

/-- For an injective `f`, a set `K` and a set `T`,
`K \ (K ∩ f ⁻¹' T) = f ⁻¹' (f '' K \ T)`. -/
theorem sdiff_inter_preimage_eq {f : ℝ → ℝ} (K T : Set ℝ) (hinj : Function.Injective f) :
    K \ (K ∩ f ⁻¹' T) = f ⁻¹' (f '' K \ T) := by
  ext t
  constructor
  · rintro ⟨htK, htbad⟩
    refine ⟨⟨t, htK, rfl⟩, ?_⟩
    rintro hmem
    exact htbad ⟨htK, hmem⟩
  · rintro ⟨⟨s, hsK, hst⟩, hnotin⟩
    have hst' : s = t := hinj hst
    subst hst'
    exact ⟨hsK, fun hbad => hnotin hbad.2⟩

/-- Translation invariance of Lebesgue measure, in the form `t ↦ t + z`. -/
theorem volume_preimage_add_right (z : ℝ) (A : Set ℝ) :
    volume ((fun t : ℝ => t + z) ⁻¹' A) = volume A := by
  simp [add_comm]

/-- The translate `z +ᵥ K` is the image of `K` under `t ↦ t + z`. -/
theorem vadd_set_eq_image_add_right (z : ℝ) (K : Set ℝ) :
    (z +ᵥ K : Set ℝ) = (fun t : ℝ => t + z) '' K := by
  ext s
  simp only [Set.mem_vadd_set, mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [vadd_eq_add, add_comm]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [vadd_eq_add, add_comm]⟩

/-- `K \ (K ∩ (· + z) ⁻¹' T)` has the measure of a subset of `(z +ᵥ K) \ K`
(namely of `(z +ᵥ K) \ T`, which is smaller because `K ⊆ T`). -/
theorem volume_sdiff_inter_preimage_le {K T : Set ℝ} (hKT : K ⊆ T) (z : ℝ) :
    volume (K \ (K ∩ (fun t : ℝ => t + z) ⁻¹' T))
      ≤ volume (((fun t : ℝ => t + z) '' K) \ K) := by
  have h1 : K \ (K ∩ (fun t : ℝ => t + z) ⁻¹' T)
      = (fun t : ℝ => t + z) ⁻¹' (((fun t : ℝ => t + z) '' K) \ T) :=
    sdiff_inter_preimage_eq K T (fun a b hab => add_right_cancel hab)
  rw [h1, volume_preimage_add_right]
  refine measure_mono ?_
  intro s hs
  exact ⟨hs.1, fun hK => hs.2 (hKT hK)⟩

/-! ### The Kestelman–Borwein–Ditor theorem -/

/-- **Kestelman–Borwein–Ditor theorem (measurable case).**
If `T ⊆ ℝ` is measurable with positive Lebesgue measure and `z n → 0`, then
some point of `T` is hit infinitely often by the null sequence: there is
`t ∈ T` such that for every `N` there is `n ≥ N` with `t + z n ∈ T`. -/
theorem exists_forall_exists_add_mem {T : Set ℝ} (hT : MeasurableSet T) (hTpos : 0 < volume T)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 0)) :
    ∃ t ∈ T, ∀ N : ℕ, ∃ n ≥ N, t + z n ∈ T := by
  obtain ⟨K, hKT, hKc, hKpos⟩ := hT.exists_lt_isCompact (r := (0 : ℝ≥0∞)) hTpos
  have hKcl : IsClosed K := hKc.isClosed
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ t ∈ T, ∃ N, ∀ n ≥ N, t + z n ∉ T`
  set B : ℕ → Set ℝ := fun N => {t ∈ K | ∀ n ≥ N, t + z n ∉ T} with hBdef
  have hBmeas : ∀ N, MeasurableSet (B N) := by
    intro N
    have hBN : B N = {t : ℝ | t ∈ K ∧ ∀ n ≥ N, t + z n ∉ T} := by rw [hBdef]
    rw [hBN]
    have hset : {t : ℝ | t ∈ K ∧ ∀ n ≥ N, t + z n ∉ T}
        = K ∩ ⋂ n ∈ Ici N, (fun t : ℝ => t + z n) ⁻¹' Tᶜ := by
      ext t
      simp
    rw [hset]
    exact hKc.measurableSet.inter (MeasurableSet.biInter (Set.to_countable _)
      (fun n _ => hT.compl.preimage (by fun_prop)))
  have hBmono : Monotone B := by
    intro N M hNM t ht
    exact ⟨ht.1, fun n hn => ht.2 n (le_trans hNM hn)⟩
  have hBunion : (⋃ N, B N) = K := by
    apply Subset.antisymm
    · exact iUnion_subset fun N => inter_subset_left
    · intro t ht
      have htT : t ∈ T := hKT ht
      obtain ⟨N, hN⟩ := hcon t htT
      exact mem_iUnion.2 ⟨N, ht, hN⟩
  have hlim : Tendsto (fun N => volume (B N)) atTop (𝓝 (volume K)) := by
    have h := tendsto_measure_iUnion_atTop (μ := volume) hBmono
    rwa [hBunion] at h
  have hhalf : volume K / 2 < volume K :=
    ENNReal.half_lt_self hKpos.ne' hKc.measure_lt_top.ne
  have hlimEv : ∀ᶠ N in atTop, volume K / 2 < volume (B N) :=
    hlim.eventually (eventually_gt_nhds hhalf)
  -- translation continuity: eventually `volume (z n +ᵥ K \ K) < volume K / 2`
  have hcont : Tendsto (fun n => volume ((z n +ᵥ K) \ K)) atTop (𝓝 (0 : ℝ≥0∞)) :=
    (tendsto_measure_vadd_sdiff_isCompact_isClosed (μ := volume) hKc hKcl).comp hz
  have hhalfpos : (0 : ℝ≥0∞) < volume K / 2 := by
    rw [ENNReal.div_pos_iff]
    exact ⟨hKpos.ne', by norm_num⟩
  have hev : ∀ᶠ n in atTop, volume ((z n +ᵥ K) \ K) < volume K / 2 :=
    hcont.eventually (eventually_lt_nhds hhalfpos)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hev.and hlimEv)
  have hMlt : volume ((z M +ᵥ K) \ K) < volume K / 2 := (hM M le_rfl).1
  have hMgt : volume K / 2 < volume (B M) := (hM M le_rfl).2
  have hsub : B M ⊆ K \ (K ∩ (fun t : ℝ => t + z M) ⁻¹' T) := by
    rintro t ⟨htK, htnot⟩
    exact ⟨htK, fun hbad => htnot M le_rfl hbad.2⟩
  have hle := volume_sdiff_inter_preimage_le hKT (z M)
  rw [vadd_set_eq_image_add_right] at hMlt
  have hlt : volume (B M) < volume K / 2 :=
    lt_of_le_of_lt (le_trans (measure_mono hsub) hle) hMlt
  exact absurd hMgt (not_lt.2 hlt.le)

/-! ### The additive uniform convergence theorem (Csiszár–Erdős proof) -/

/-- **Uniform convergence on compact parameter sets.**
If `H : ℝ → ℝ` is measurable and `H (x + u) - H x → 0` as `x → ∞` for every
fixed `u`, then the convergence is uniform in `u` on each compact interval.

This is the additive form of the uniform convergence theorem; the threshold
`X` is allowed to depend on the interval `[a,b]` and on `ε`. -/
theorem tendsto_uniform_additive {H : ℝ → ℝ} (hHmeas : Measurable H)
    (hH : ∀ u : ℝ, Tendsto (fun x : ℝ => H (x + u) - H x) atTop (𝓝 0))
    {a b : ℝ} (hab : a ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x ≥ X, ∀ u ∈ Icc a b, |H (x + u) - H x| ≤ ε := by
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  -- bad sequences
  choose x hx using fun n : ℕ => hcon (n : ℝ)
  choose u hu using fun n : ℕ => (hx n).2
  have hx_ge : ∀ n : ℕ, (n : ℝ) ≤ x n := fun n => (hx n).1
  have hxtop : Tendsto x atTop atTop := tendsto_atTop_mono hx_ge tendsto_natCast_atTop_atTop
  have humem : ∀ n, u n ∈ Icc a b := fun n => (hu n).1
  have hbad : ∀ n, ε < |H (x n + u n) - H (x n)| := fun n => (hu n).2
  -- pass to a convergent subsequence of the parameters
  obtain ⟨v, -, φ, hφmono, hφtend⟩ := isCompact_Icc.tendsto_subseq humem
  set x' : ℕ → ℝ := fun n => x (φ n) with hx'def
  set u' : ℕ → ℝ := fun n => u (φ n) with hu'def
  have hx'top : Tendsto x' atTop atTop := hxtop.comp hφmono.tendsto_atTop
  have hu'tend : Tendsto u' atTop (𝓝 v) := hφtend
  have hu'mem : ∀ n, u' n ∈ Icc a b := fun n => humem (φ n)
  have hbad' : ∀ n, ε < |H (x' n + u' n) - H (x' n)| := fun n => hbad (φ n)
  -- the positive-measure sets of good shifts
  set T : ℕ → Set ℝ := fun k =>
    ⋂ n ∈ Ici k, {y : ℝ | |H (x' n + (y + v)) - H (x' n)| < ε / 2} with hTdef
  have hTmeas : ∀ k, MeasurableSet (T k) := by
    intro k
    have hEq : T k = ⋂ n ∈ Ici k,
        (fun y : ℝ => |H (x' n + (y + v)) - H (x' n)|) ⁻¹' Iio (ε / 2) := by
      ext y
      simp [hTdef]
    rw [hEq]
    refine MeasurableSet.biInter (Set.to_countable _) (fun n _ => ?_)
    have h1 : Measurable fun y : ℝ => x' n + (y + v) :=
      measurable_const.add (measurable_id.add measurable_const)
    have h2 : Measurable fun y : ℝ => H (x' n + (y + v)) := hHmeas.comp h1
    have h3 : Measurable fun y : ℝ => H (x' n + (y + v)) - H (x' n) := h2.sub_const _
    exact h3.abs measurableSet_Iio
  have hTunion : (⋃ k, T k) = univ := by
    refine eq_univ_of_forall fun y => ?_
    have hcomp : Tendsto (fun n => H (x' n + (y + v)) - H (x' n)) atTop (𝓝 0) :=
      (hH (y + v)).comp hx'top
    have h0 : Tendsto (fun n => |H (x' n + (y + v)) - H (x' n)|) atTop (𝓝 0) := by
      simpa using hcomp.abs
    have hev : ∀ᶠ n in atTop, |H (x' n + (y + v)) - H (x' n)| < ε / 2 :=
      h0.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨k, hk⟩ := eventually_atTop.1 hev
    exact mem_iUnion.2 ⟨k, by
      simp only [hTdef, mem_iInter, mem_Ici, mem_ofPred_eq]
      exact fun n hn => hk n hn⟩
  -- some `T k` has positive measure
  have hex : ∃ k, 0 < volume (T k) := by
    by_contra h
    push Not at h
    have h0 : volume (⋃ k, T k) = 0 :=
      measure_iUnion_null fun k => le_antisymm (h k) bot_le
    rw [hTunion] at h0
    simp at h0
  obtain ⟨k, hkpos⟩ := hex
  -- KBD with the null sequence `u' n - v`
  have hz : Tendsto (fun n => u' n - v) atTop (𝓝 0) := by
    have h := hu'tend.sub (tendsto_const_nhds (x := v))
    simpa using h
  obtain ⟨t, -, hthits⟩ := exists_forall_exists_add_mem (hTmeas k) hkpos hz
  -- control at the fixed shift `t`
  have hux_top : Tendsto (fun n => u' n + x' n) atTop atTop := hu'tend.add_atTop hx'top
  have hshift : ∀ᶠ n in atTop, |H ((u' n + x' n) + t) - H (u' n + x' n)| < ε / 2 := by
    have hcomp := (hH t).comp hux_top
    have h0 : Tendsto (fun n => |H ((u' n + x' n) + t) - H (u' n + x' n)|) atTop (𝓝 0) := by
      simpa using hcomp.abs
    exact h0.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hshift
  -- a hit at a large index
  obtain ⟨n, hn_ge, hnT⟩ := hthits (max N k)
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn_ge
  have hnk : k ≤ n := le_trans (le_max_right _ _) hn_ge
  have hmemT : t + (u' n - v) ∈ T k := hnT
  have hmem : |H ((u' n + x' n) + t) - H (x' n)| < ε / 2 := by
    have h1 : |H (x' n + ((t + (u' n - v)) + v)) - H (x' n)| < ε / 2 := by
      have := hmemT
      simp only [hTdef, mem_iInter, mem_Ici, mem_ofPred_eq] at this
      exact this n hnk
    have h2 : x' n + ((t + (u' n - v)) + v) = (u' n + x' n) + t := by ring
    rwa [h2] at h1
  have hNn : |H ((u' n + x' n) + t) - H (u' n + x' n)| < ε / 2 := hN n hnN
  have htri : |H (u' n + x' n) - H (x' n)|
      ≤ |H (u' n + x' n) - H ((u' n + x' n) + t)| + |H ((u' n + x' n) + t) - H (x' n)| :=
    abs_sub_le _ _ _
  have hsymm : |H (u' n + x' n) - H ((u' n + x' n) + t)|
      = |H ((u' n + x' n) + t) - H (u' n + x' n)| := abs_sub_comm _ _
  rw [hsymm] at htri
  have hbad'' : ε < |H (u' n + x' n) - H (x' n)| := by
    have h := hbad' n
    rwa [add_comm (x' n) (u' n)] at h
  linarith [hbad'', htri, hNn, hmem]

/-! ### The multiplicative uniform convergence theorem (BGT Theorem 1.2.1) -/

/-- **Logarithmic ratio differences converge to zero.**
For measurable `f` regularly varying of index `α` and each fixed `u`,
`log |f (exp (x+u))| - log |f (exp x)| - α u → 0`. -/
theorem tendsto_log_abs_ratio_sub {f : ℝ → ℝ} {α : ℝ} (hmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f α) (u : ℝ) :
    Tendsto (fun x : ℝ => Real.log |f (Real.exp (x + u))| - Real.log |f (Real.exp x)| - α * u)
      atTop (𝓝 0) := by
  have hl : 0 < Real.exp u := Real.exp_pos u
  -- the ratio converges
  have hratio : Tendsto (fun x : ℝ => f (Real.exp u * Real.exp x) / f (Real.exp x)) atTop
      (𝓝 ((Real.exp u) ^ α)) :=
    (hrv.2 (Real.exp u) hl).comp Real.tendsto_exp_atTop
  have hrpos : (0 : ℝ) < (Real.exp u) ^ α := Real.rpow_pos_of_pos hl α
  -- eventually everything is nonzero and the ratio is positive
  have hne : ∀ᶠ x : ℝ in atTop, f (Real.exp x) ≠ 0 :=
    Real.tendsto_exp_atTop.eventually hrv.1
  have hne2 : ∀ᶠ x : ℝ in atTop, f (Real.exp u * Real.exp x) ≠ 0 :=
    ((Real.tendsto_exp_atTop.const_mul_atTop hl)).eventually hrv.1
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < f (Real.exp u * Real.exp x) / f (Real.exp x) :=
    hratio.eventually (eventually_gt_nhds hrpos)
  -- the logarithmic limit
  have hloglim : Tendsto (fun x : ℝ => Real.log |f (Real.exp (x + u))| - Real.log |f (Real.exp x)|)
      atTop (𝓝 (α * u)) := by
    have h1 : Tendsto (fun x : ℝ => Real.log (f (Real.exp u * Real.exp x) / f (Real.exp x)))
        atTop (𝓝 (Real.log ((Real.exp u) ^ α))) :=
      (Real.continuousAt_log hrpos.ne').tendsto.comp hratio
    have hval : Real.log ((Real.exp u) ^ α) = α * u := by
      rw [Real.log_rpow hl, Real.log_exp]
    rw [hval] at h1
    refine h1.congr' ?_
    filter_upwards [hne, hne2, hpos] with x hx hx2 hxp
    have harg : Real.exp (x + u) = Real.exp u * Real.exp x := by
      rw [Real.exp_add]; ring
    rw [harg, ← Real.log_div (abs_ne_zero.2 hx2) (abs_ne_zero.2 hx), ← abs_div,
      abs_of_pos hxp]
  have h2 := hloglim.sub_const (α * u)
  simpa using h2

/-- **Uniform convergence theorem for the absolute ratios** (BGT Theorem 1.2.1 in the
form needed for Potter's bounds).  For measurable `f` regularly varying of index `α`
and any `0 < a ≤ b`, the ratios `|f (l y)| / |f y|` converge to `l ^ α` uniformly for
`l ∈ [a,b]`. -/
theorem tendsto_uniformly_abs_ratio_of_regularlyVarying {f : ℝ → ℝ} {α : ℝ}
    (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f α)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {η : ℝ} (hη : 0 < η) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ y ≥ Y, ∀ l ∈ Icc a b,
      |(|f (l * y)| / |f y|) - l ^ α| ≤ η := by
  -- the logarithmic substitute
  set H : ℝ → ℝ := fun x => Real.log |f (Real.exp x)| - α * x with hHdef
  have hHmeas : Measurable H := by
    refine Measurable.sub ?_ ?_
    · exact Real.measurable_log.comp (hmeas.abs.comp Real.measurable_exp)
    · exact measurable_const.mul measurable_id
  have hHadd : ∀ u : ℝ, Tendsto (fun x : ℝ => H (x + u) - H x) atTop (𝓝 0) := by
    intro u
    have h := tendsto_log_abs_ratio_sub hmeas hrv u
    refine h.congr' ?_
    filter_upwards with x
    simp only [hHdef]
    ring
  -- the size of `l ^ α` on `[a,b]`
  set M : ℝ := max 1 (max (a ^ α) (b ^ α)) with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hrpow_le : ∀ l ∈ Icc a b, l ^ α ≤ M := by
    intro l hl
    have hlpos : 0 < l := lt_of_lt_of_le ha hl.1
    have h1 : l ^ α ≤ max (a ^ α) (b ^ α) := by
      rcases le_or_gt 0 α with hα | hα
      · exact le_trans (Real.rpow_le_rpow hlpos.le hl.2 hα) (le_max_right _ _)
      · exact le_trans (Real.rpow_le_rpow_of_nonpos ha hl.1 (le_of_lt hα)) (le_max_left _ _)
    exact le_trans h1 (le_max_right _ _)
  -- choose the logarithmic tolerance
  have hcont : Tendsto (fun t : ℝ => M * (Real.exp t - 1)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp t - 1) (𝓝 (0:ℝ)) (𝓝 (Real.exp 0 - 1)) :=
      (Real.continuous_exp.tendsto 0).sub_const 1
    rw [Real.exp_zero, sub_self] at h1
    simpa using h1.const_mul M
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (Iio_mem_nhds hη))
  set ε' : ℝ := δ / 2 with hε'def
  have hε'pos : 0 < ε' := by positivity
  have hε'bound : M * (Real.exp ε' - 1) ≤ η := by
    have h2 : M * (Real.exp ε' - 1) < η := hδ (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε'pos]
      linarith)
    exact le_of_lt h2
  -- uniform convergence in the logarithmic variable
  obtain ⟨X, hX⟩ := tendsto_uniform_additive hHmeas hHadd
    (a := Real.log a) (b := Real.log b) (Real.log_le_log ha hab) hε'pos
  -- eventual non-vanishing, in exponential coordinates
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 (Real.tendsto_exp_atTop.eventually hrv.1)
  refine ⟨max (max (Real.exp X) 1) (Real.exp Y₀ * max 1 (1 / a)), ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro y hy l hl
  have hY1 : 1 ≤ max (max (Real.exp X) 1) (Real.exp Y₀ * max 1 (1 / a)) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hy1 : 1 ≤ y := le_trans hY1 hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hexpX_le : Real.exp X ≤ y :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyY₀big : Real.exp Y₀ * max 1 (1 / a) ≤ y := le_trans (le_max_right _ _) hy
  have hexpY₀_le : Real.exp Y₀ ≤ y := by
    have h1 : 1 ≤ max 1 (1 / a) := le_max_left _ _
    have h2 : Real.exp Y₀ ≤ Real.exp Y₀ * max 1 (1 / a) := by nlinarith [Real.exp_pos Y₀]
    linarith
  have hyX : X ≤ Real.log y := by
    calc X = Real.log (Real.exp X) := (Real.log_exp X).symm
      _ ≤ Real.log y := Real.log_le_log (Real.exp_pos X) hexpX_le
  have hyY₀ : Y₀ ≤ Real.log y := by
    calc Y₀ = Real.log (Real.exp Y₀) := (Real.log_exp Y₀).symm
      _ ≤ Real.log y := Real.log_le_log (Real.exp_pos Y₀) hexpY₀_le
  have hlpos : 0 < l := lt_of_lt_of_le ha hl.1
  have hlogmem : Real.log l ∈ Icc (Real.log a) (Real.log b) :=
    ⟨Real.log_le_log ha hl.1, Real.log_le_log hlpos hl.2⟩
  have hkey := hX (Real.log y) hyX (Real.log l) hlogmem
  have hyl : Real.exp (Real.log y + Real.log l) = l * y := by
    rw [Real.exp_add, Real.exp_log hy0, Real.exp_log hlpos, mul_comm]
  -- `l * y` is still in the non-vanishing range
  have hly : Real.exp Y₀ ≤ l * y := by
    have h2 : a * (Real.exp Y₀ * max 1 (1 / a)) ≤ a * y := by
      have := hyY₀big
      nlinarith [ha.le]
    have h4 : 1 ≤ a * max 1 (1 / a) := by
      have h5 : a * (1 / a) = 1 := by field_simp
      have h6 : 1 / a ≤ max 1 (1 / a) := le_max_right _ _
      nlinarith [ha, h6]
    have h5 : Real.exp Y₀ ≤ a * (Real.exp Y₀ * max 1 (1 / a)) := by
      nlinarith [Real.exp_pos Y₀, h4]
    have h6 : a * y ≤ l * y := by nlinarith [hy0, hl.1]
    linarith
  have hyne : f y ≠ 0 := by
    have h1 : f (Real.exp (Real.log y)) ≠ 0 := hY₀ (Real.log y) hyY₀
    rwa [Real.exp_log hy0] at h1
  have hlyne : f (l * y) ≠ 0 := by
    have hlogly : Y₀ ≤ Real.log (l * y) := by
      calc Y₀ = Real.log (Real.exp Y₀) := (Real.log_exp Y₀).symm
        _ ≤ Real.log (l * y) := Real.log_le_log (Real.exp_pos Y₀) hly
    have h1 : f (Real.exp (Real.log (l * y))) ≠ 0 := hY₀ _ hlogly
    rwa [Real.exp_log (mul_pos hlpos hy0)] at h1
  -- identify the two logarithmic expressions
  have hHval : H (Real.log y + Real.log l) - H (Real.log y)
      = Real.log |f (l * y)| - Real.log |f y| - α * Real.log l := by
    have h1 : H (Real.log y + Real.log l)
        = Real.log |f (l * y)| - α * (Real.log y + Real.log l) := by
      simp only [hHdef, hyl]
    have h2 : H (Real.log y) = Real.log |f y| - α * Real.log y := by
      simp only [hHdef, Real.exp_log hy0]
    rw [h1, h2]
    ring
  rw [hHval] at hkey
  -- pass from logarithms of absolute values to the ratio
  have hratioeq : Real.log |f (l * y)| - Real.log |f y|
      = Real.log (|f (l * y)| / |f y|) :=
    (Real.log_div (abs_ne_zero.2 hlyne) (abs_ne_zero.2 hyne)).symm
  have hratiopos : 0 < |f (l * y)| / |f y| := by positivity
  have hlpow : 0 < l ^ α := Real.rpow_pos_of_pos hlpos α
  have hlogeq : α * Real.log l = Real.log (l ^ α) := by rw [Real.log_rpow hlpos]
  have hlogabs : |Real.log ((|f (l * y)| / |f y|) / l ^ α)| ≤ ε' := by
    rw [hratioeq, hlogeq] at hkey
    rwa [← Real.log_div hratiopos.ne' hlpow.ne'] at hkey
  -- `|log t| ≤ ε'` forces `|t - 1| ≤ exp ε' - 1`
  set t : ℝ := (|f (l * y)| / |f y|) / l ^ α with htdef
  have htpos : 0 < t := div_pos hratiopos hlpow
  have htlog : Real.log t ∈ Icc (-ε') ε' := by
    constructor
    · have := (abs_le.1 hlogabs).1; exact this
    · exact (abs_le.1 hlogabs).2
  have htexp_hi : t ≤ Real.exp ε' := by
    calc t = Real.exp (Real.log t) := (Real.exp_log htpos).symm
      _ ≤ Real.exp ε' := Real.exp_le_exp.2 htlog.2
  have htexp_lo : Real.exp (-ε') ≤ t := by
    calc Real.exp (-ε') ≤ Real.exp (Real.log t) := Real.exp_le_exp.2 htlog.1
      _ = t := Real.exp_log htpos
  have hexpneg : 1 - (Real.exp ε' - 1) ≤ Real.exp (-ε') := by
    have h1 : Real.exp (-ε') * Real.exp ε' = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h2 : 0 < Real.exp (-ε') := Real.exp_pos _
    have h3 : 0 < Real.exp ε' := Real.exp_pos _
    nlinarith [h1, h2, h3]
  have htclose : |t - 1| ≤ Real.exp ε' - 1 := by
    rw [abs_le]
    constructor
    · linarith [le_trans hexpneg htexp_lo]
    · linarith [htexp_hi]
  -- multiply by `l ^ α` and bound by `M`
  have hfinal : |(|f (l * y)| / |f y|) - l ^ α| ≤ l ^ α * (Real.exp ε' - 1) := by
    have hmul : l ^ α * |t - 1| ≤ l ^ α * (Real.exp ε' - 1) :=
      mul_le_mul_of_nonneg_left htclose hlpow.le
    have hkey2 : (|f (l * y)| / |f y|) - l ^ α = l ^ α * (t - 1) := by
      rw [htdef]
      field_simp
    rw [hkey2, abs_mul, abs_of_pos hlpow]
    exact hmul
  have hpowle : l ^ α * (Real.exp ε' - 1) ≤ M * (Real.exp ε' - 1) := by
    apply mul_le_mul_of_nonneg_right (hrpow_le l hl)
    have : 1 ≤ Real.exp ε' := Real.one_le_exp hε'pos.le
    linarith
  have hnonneg : 0 ≤ Real.exp ε' - 1 := by
    have : 1 ≤ Real.exp ε' := Real.one_le_exp hε'pos.le
    linarith
  linarith [hfinal, hpowle, hε'bound]

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.Analysis

/-! ### Potter's bounds from the uniform convergence theorem -/

/-- The `0 < ε ≤ 1/2` case of Potter's bounds: partition the logarithmic interval
into `n = ⌈log (x/y)⌉` equal pieces of length `u ≤ 1`, use the uniform logarithmic
convergence theorem on each piece, and sum the errors. -/
theorem potter_core {f : ℝ → ℝ} {α : ℝ} (hmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f α) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y| := by
  -- the logarithmic substitute
  set H : ℝ → ℝ := fun x => Real.log |f (Real.exp x)| - α * x with hHdef
  have hHmeas : Measurable H := by
    refine Measurable.sub ?_ ?_
    · exact Real.measurable_log.comp (hmeas.abs.comp Real.measurable_exp)
    · exact measurable_const.mul measurable_id
  have hHadd : ∀ u : ℝ, Tendsto (fun x : ℝ => H (x + u) - H x) atTop (𝓝 0) := by
    intro u
    have h := tendsto_log_abs_ratio_sub hmeas hrv u
    refine h.congr' ?_
    filter_upwards with x
    simp only [hHdef]
    ring
  -- the logarithmic tolerance
  obtain ⟨ε', hε'pos, hε'ε, hε'exp⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε / 2 ∧ Real.exp ε' ≤ 1 + ε := by
    have hcont : Tendsto (fun t : ℝ => Real.exp t) (𝓝 0) (𝓝 1) := by
      have h := Real.continuous_exp.tendsto 0
      simpa using h
    have hev : ∀ᶠ t in 𝓝 (0:ℝ), Real.exp t < 1 + ε :=
      hcont.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.1 hev
    have hminpos : 0 < min (ε / 2) (δ / 2) := lt_min (by linarith) (by linarith)
    refine ⟨min (ε / 2) (δ / 2), hminpos, min_le_left _ _, ?_⟩
    have hlt : Real.exp (min (ε / 2) (δ / 2)) < 1 + ε := hδ (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hminpos]
      have h2 : min (ε / 2) (δ / 2) ≤ δ / 2 := min_le_right _ _
      linarith)
    linarith
  -- uniform convergence of logarithmic increments on a unit window
  obtain ⟨X₀, hX₀⟩ := tendsto_uniform_additive hHmeas hHadd (a := 0) (b := 1)
    (by norm_num) hε'pos
  -- the tail where `f` does not vanish
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hrv.1
  refine ⟨max (max (Real.exp X₀) 1) Y₀, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro x y hy hyx
  have hYpos : 0 < max (max (Real.exp X₀) 1) Y₀ :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hy0 : 0 < y := lt_of_lt_of_le hYpos hy
  have hx0 : 0 < x := lt_of_lt_of_le hy0 hyx
  have hY₁ : Y₀ ≤ y := le_trans (le_max_right _ _) hy
  have hyX₀ : X₀ ≤ Real.log y := by
    have h1 : Real.exp X₀ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
    calc X₀ = Real.log (Real.exp X₀) := (Real.log_exp X₀).symm
      _ ≤ Real.log y := Real.log_le_log (Real.exp_pos X₀) h1
  have hfx0 : f x ≠ 0 := hY₀ x (le_trans hY₁ hyx)
  have hfy0 : f y ≠ 0 := hY₀ y hY₁
  have hfxa : 0 < |f x| := abs_pos.2 hfx0
  have hfya : 0 < |f y| := abs_pos.2 hfy0
  have hxypos : 0 < x / y := div_pos hx0 hy0
  have hxys : 1 ≤ x / y := (le_div_iff₀ hy0).2 (by linarith)
  rcases eq_or_lt_of_le hyx with hxy | hlt
  · -- degenerate case `x = y`
    subst hxy
    have h1 : y / y = 1 := div_self (ne_of_gt hy0)
    simp only [h1, Real.one_rpow, one_mul]
    constructor <;> nlinarith [abs_nonneg (f y), hε]
  -- main case `y < x`
  have hTpos : 0 < Real.log x - Real.log y := sub_pos.2 (Real.log_lt_log hy0 hlt)
  set T : ℝ := Real.log x - Real.log y with hTdef
  set n : ℕ := Nat.ceil T with hndef
  have hnpos : 0 < n := by rw [hndef]; exact Nat.ceil_pos.2 hTpos
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have hTle : T ≤ (n : ℝ) := by rw [hndef]; exact Nat.le_ceil T
  set u : ℝ := T / n with hudef
  have hu0 : 0 ≤ u := div_nonneg hTpos.le (Nat.cast_nonneg n)
  have hu1 : u ≤ 1 := by
    rw [hudef, div_le_one (by positivity)]
    exact hTle
  have hnu : (n : ℝ) * u = T := by
    rw [hudef]; field_simp
  -- the telescoping sum
  set g : ℕ → ℝ := fun j => H (Real.log y + (j : ℝ) * u) with hgdef
  have hstep : ∀ j ∈ Finset.range n, |g (j + 1) - g j| ≤ ε' := by
    intro j hj
    have hjlt : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.1 hj)
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hs : X₀ ≤ Real.log y + (j : ℝ) * u :=
      le_trans hyX₀ (le_add_of_nonneg_right (mul_nonneg hj0 hu0))
    have hmem : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, hu1⟩
    have h1 := hX₀ _ hs u hmem
    have harith : Real.log y + (j : ℝ) * u + u = Real.log y + ((j : ℝ) + 1) * u := by ring
    rw [harith] at h1
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := Nat.cast_add_one j
    have hgj : g j = H (Real.log y + (j : ℝ) * u) := rfl
    have hgj1 : g (j + 1) = H (Real.log y + ((j : ℝ) + 1) * u) := by
      simp only [hgdef, hcast]
    rw [hgj, hgj1]
    exact h1
  have hsum : |g n - g 0| ≤ (n : ℝ) * ε' := by
    have htel : ∑ j ∈ Finset.range n, (g (j + 1) - g j) = g n - g 0 :=
      Finset.sum_range_sub g n
    rw [← htel]
    calc |∑ j ∈ Finset.range n, (g (j + 1) - g j)|
        ≤ ∑ j ∈ Finset.range n, |g (j + 1) - g j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, ε' := Finset.sum_le_sum hstep
      _ = (n : ℝ) * ε' := by simp [Finset.sum_const, nsmul_eq_mul]
  have hgn : g n = H (Real.log x) := by
    simp only [hgdef, hnu, hTdef]
    congr 1
    ring
  have hg0 : g 0 = H (Real.log y) := by
    simp only [hgdef]
    simp
  have hHx : H (Real.log x) = Real.log |f x| - α * Real.log x := by
    simp only [hHdef, Real.exp_log hx0]
  have hHy : H (Real.log y) = Real.log |f y| - α * Real.log y := by
    simp only [hHdef, Real.exp_log hy0]
  rw [hgn, hg0, hHx, hHy] at hsum
  -- the logarithmic error, with the `+1` from the ceiling
  have hkey : |Real.log |f x| - Real.log |f y| - α * T| ≤ (n : ℝ) * ε' := by
    have h2 : Real.log |f x| - Real.log |f y| - α * T
        = (Real.log |f x| - α * Real.log x) - (Real.log |f y| - α * Real.log y) := by
      rw [hTdef]; ring
    rw [h2]; exact hsum
  set w : ℝ := Real.log (|f x| / |f y|) - α * T with hwdef
  have hwabs : |w| ≤ (T + 1) * ε' := by
    rw [hwdef, Real.log_div hfxa.ne' hfya.ne']
    refine le_trans hkey ?_
    have hn1 : (n : ℝ) ≤ T + 1 := by
      rw [hndef]; exact le_of_lt (Nat.ceil_lt_add_one hTpos.le)
    nlinarith [hε'pos]
  have hT0 : 0 ≤ T := hTpos.le
  have hxylog : Real.log (x / y) = T := by rw [Real.log_div hx0.ne' hy0.ne', hTdef]
  have hxynorm : |f x| = |f y| * (x / y) ^ α * Real.exp w := by
    have h1 : |f x| = |f y| * (|f x| / |f y|) := by field_simp
    have h2 : |f x| / |f y| = Real.exp (α * T + w) := by
      have h3 : Real.log (|f x| / |f y|) = α * T + w := by
        rw [hwdef]; ring
      rw [← Real.exp_log (div_pos hfxa hfya), h3]
    rw [h1, h2, Real.exp_add, Real.rpow_def_of_pos hxypos, hxylog]
    ring
  have hexp_le : Real.exp w ≤ (x / y) ^ ε' * Real.exp ε' := by
    have h1 : w ≤ (T + 1) * ε' := (abs_le.1 hwabs).2
    have h2 : Real.exp w ≤ Real.exp ((T + 1) * ε') := Real.exp_le_exp.2 h1
    have h3 : Real.exp ((T + 1) * ε') = (x / y) ^ ε' * Real.exp ε' := by
      rw [show (T + 1) * ε' = T * ε' + ε' by ring, Real.exp_add,
        Real.rpow_def_of_pos hxypos, hxylog]
    linarith [h2, h3]
  have hexp_ge : (x / y) ^ (-ε') * Real.exp (-ε') ≤ Real.exp w := by
    have h1 : -((T + 1) * ε') ≤ w := (abs_le.1 hwabs).1
    have h2 : Real.exp (-((T + 1) * ε')) ≤ Real.exp w := Real.exp_le_exp.2 h1
    have h3 : Real.exp (-((T + 1) * ε')) = (x / y) ^ (-ε') * Real.exp (-ε') := by
      rw [show -((T + 1) * ε') = T * (-ε') + (-ε') by ring, Real.exp_add,
        Real.rpow_def_of_pos hxypos, hxylog]
    linarith [h2, h3]
  have hsplit_lo : (x / y) ^ α * (x / y) ^ (-ε') = (x / y) ^ (α - ε') := by
    rw [← Real.rpow_add hxypos]; ring_nf
  have hsplit_hi : (x / y) ^ α * (x / y) ^ ε = (x / y) ^ (α + ε) :=
    (Real.rpow_add hxypos α ε).symm
  constructor
  · -- lower Potter bound
    rw [hxynorm]
    have hpow : (x / y) ^ (ε' - ε) ≤ 1 := by
      have h3 := Real.rpow_le_rpow_of_exponent_le hxys (show ε' - ε ≤ 0 by linarith)
      simpa using h3
    have hexpneg : 1 - ε ≤ Real.exp (-ε') := by
      have h3 : -ε' + 1 ≤ Real.exp (-ε') := Real.add_one_le_exp (-ε')
      have hle : ε' ≤ ε := by linarith
      linarith
    have hcoef : (1 - ε) * (x / y) ^ (α - ε)
        ≤ (x / y) ^ (α - ε') * Real.exp (-ε') := by
      have hs : (x / y) ^ (α - ε) = (x / y) ^ (α - ε') * (x / y) ^ (ε' - ε) := by
        rw [← Real.rpow_add hxypos]; ring_nf
      rw [hs]
      have hstep : (1 - ε) * (x / y) ^ (ε' - ε) ≤ Real.exp (-ε') * 1 :=
        mul_le_mul hexpneg hpow (Real.rpow_nonneg hxypos.le _) (Real.exp_pos _).le
      rw [mul_one] at hstep
      have hnn : 0 ≤ (x / y) ^ (α - ε') := Real.rpow_nonneg hxypos.le _
      have h2 := mul_le_mul_of_nonneg_right hstep hnn
      calc (1 - ε) * ((x / y) ^ (α - ε') * (x / y) ^ (ε' - ε))
          = ((1 - ε) * (x / y) ^ (ε' - ε)) * (x / y) ^ (α - ε') := by ring
        _ ≤ Real.exp (-ε') * (x / y) ^ (α - ε') := h2
        _ = (x / y) ^ (α - ε') * Real.exp (-ε') := by ring
    have hstep2 : (x / y) ^ (α - ε') * Real.exp (-ε') * |f y|
        ≤ |f y| * (x / y) ^ α * Real.exp w := by
      have h1 : (x / y) ^ α * ((x / y) ^ (-ε') * Real.exp (-ε'))
          ≤ (x / y) ^ α * Real.exp w :=
        mul_le_mul_of_nonneg_left hexp_ge (Real.rpow_nonneg hxypos.le α)
      have h2 : (x / y) ^ α * ((x / y) ^ (-ε') * Real.exp (-ε'))
          = (x / y) ^ (α - ε') * Real.exp (-ε') := by
        rw [← hsplit_lo]; ring
      have h3 : (x / y) ^ α * Real.exp w * |f y| = |f y| * (x / y) ^ α * Real.exp w := by
        ring
      calc (x / y) ^ (α - ε') * Real.exp (-ε') * |f y|
          = ((x / y) ^ α * ((x / y) ^ (-ε') * Real.exp (-ε'))) * |f y| := by rw [h2]
        _ ≤ ((x / y) ^ α * Real.exp w) * |f y| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |f y| * (x / y) ^ α * Real.exp w := h3
    calc (1 - ε) * (x / y) ^ (α - ε) * |f y|
        ≤ ((x / y) ^ (α - ε') * Real.exp (-ε')) * |f y| :=
          mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      _ ≤ |f y| * (x / y) ^ α * Real.exp w := hstep2
  · -- upper Potter bound
    rw [hxynorm]
    have hcoef : (x / y) ^ α * Real.exp w ≤ (1 + ε) * (x / y) ^ (α + ε) := by
      have h3 : (x / y) ^ ε' ≤ (x / y) ^ ε :=
        Real.rpow_le_rpow_of_exponent_le hxys (by linarith : ε' ≤ ε)
      have hmid : (x / y) ^ ε' * Real.exp ε' ≤ (x / y) ^ ε * (1 + ε) :=
        mul_le_mul h3 hε'exp (Real.exp_pos _).le (Real.rpow_nonneg hxypos.le _)
      have h1 : (x / y) ^ α * ((x / y) ^ ε' * Real.exp ε')
          ≤ (x / y) ^ α * ((x / y) ^ ε * (1 + ε)) :=
        mul_le_mul_of_nonneg_left hmid (Real.rpow_nonneg hxypos.le _)
      have h2 : (x / y) ^ α * ((x / y) ^ ε * (1 + ε)) = (1 + ε) * (x / y) ^ (α + ε) := by
        rw [← hsplit_hi]; ring
      calc (x / y) ^ α * Real.exp w
          ≤ (x / y) ^ α * ((x / y) ^ ε' * Real.exp ε') :=
            mul_le_mul_of_nonneg_left hexp_le (Real.rpow_nonneg hxypos.le _)
        _ ≤ (x / y) ^ α * ((x / y) ^ ε * (1 + ε)) := h1
        _ = (1 + ε) * (x / y) ^ (α + ε) := h2
    calc |f y| * (x / y) ^ α * Real.exp w
        = |f y| * ((x / y) ^ α * Real.exp w) := by ring
      _ ≤ |f y| * ((1 + ε) * (x / y) ^ (α + ε)) :=
          mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)
      _ = (1 + ε) * (x / y) ^ (α + ε) * |f y| := by ring

/-- **Potter's bounds** (BGT Theorem 1.5.6) for measurable regularly varying functions.
For every `ε > 0` there is `X ≥ 1` such that for all `x ≥ y ≥ X`,

  `(1 - ε) (x/y)^{α-ε} |f y| ≤ |f x| ≤ (1 + ε) (x/y)^{α+ε} |f y|`.

The `ε ≤ 1/2` case is `potter_core`; for larger `ε` the bounds are weaker, so the
same `X` works. -/
theorem hasPotterBounds_of_regularlyVarying {f : ℝ → ℝ} {α : ℝ} (hmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f α) : HasPotterBounds f α := by
  intro ε hε
  -- it suffices to treat `0 < ε ≤ 1/2`
  obtain ⟨ε₀, hε₀pos, hε₀le, hε₀ε⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ε₀ ≤ ε :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), min_le_right _ _, min_le_left _ _⟩
  obtain ⟨Y, hY1, hY⟩ := potter_core hmeas hrv hε₀pos hε₀le
  refine ⟨Y, hY1, fun x y hy hyx => ?_⟩
  obtain ⟨hlo, hhi⟩ := hY x y hy hyx
  have hy0 : 0 < y := lt_of_lt_of_le (by linarith : (0:ℝ) < 1) (le_trans hY1 hy)
  have hxy1 : 1 ≤ x / y := (le_div_iff₀ hy0).2 (by linarith)
  have hfyn : 0 ≤ |f y| := abs_nonneg _
  have hbase : 0 ≤ x / y := le_trans zero_le_one hxy1
  constructor
  · -- lower bound: `α - ε₀` and `1 - ε₀` are the stronger parameters
    have h1 : (x / y) ^ (α - ε) ≤ (x / y) ^ (α - ε₀) :=
      Real.rpow_le_rpow_of_exponent_le hxy1 (by linarith)
    have h2 : (1 - ε) * (x / y) ^ (α - ε) ≤ (1 - ε₀) * (x / y) ^ (α - ε₀) :=
      mul_le_mul (by linarith) h1 (Real.rpow_nonneg hbase _) (by linarith)
    calc (1 - ε) * (x / y) ^ (α - ε) * |f y|
        ≤ (1 - ε₀) * (x / y) ^ (α - ε₀) * |f y| :=
          mul_le_mul_of_nonneg_right h2 hfyn
      _ ≤ |f x| := hlo
  · -- upper bound
    have h1 : (x / y) ^ (α + ε₀) ≤ (x / y) ^ (α + ε) :=
      Real.rpow_le_rpow_of_exponent_le hxy1 (by linarith)
    have h2 : (1 + ε₀) * (x / y) ^ (α + ε₀) ≤ (1 + ε) * (x / y) ^ (α + ε) :=
      mul_le_mul (by linarith) h1 (Real.rpow_nonneg hbase _) (by linarith)
    calc |f x| ≤ (1 + ε₀) * (x / y) ^ (α + ε₀) * |f y| := hhi
      _ ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y| := mul_le_mul_of_nonneg_right h2 hfyn

end PercLib.CriticalLRP.Analysis


namespace PercLib.CriticalLRP.Analysis

/-! ### The `α < -1` half of Karamata's integral theorem (Lemma I.2.10) -/

/-- **Integrability of the tail for negative index.** If `f` is measurable, locally
integrable on `(0,∞)` and regularly varying of index `α < -1`, then `f` is
integrable on `(r,∞)` for every `r > 0`. -/
theorem integrableOn_Ioi_of_regularlyVarying {f : ℝ → ℝ} {α : ℝ} (hα : α < -1)
    (hmeas : Measurable f) (hloc : LocallyIntegrableOn f (Ioi 0))
    (hrv : RegularlyVaryingAtTop f α) (r : ℝ) (hr : 0 < r) :
    IntegrableOn f (Ioi r) := by
  classical
  set ε : ℝ := -(α + 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt : α + ε < -1 := by rw [hεdef]; linarith
  obtain ⟨X, hX1, hpot⟩ := hasPotterBounds_of_regularlyVarying hmeas hrv ε hεpos
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  set X' : ℝ := max X r with hX'def
  have hX'pos : 0 < X' := lt_of_lt_of_le hXpos (le_max_left _ _)
  have hrX' : r ≤ X' := le_max_right _ _
  have hXX' : X ≤ X' := le_max_left _ _
  -- the comparison function is integrable at infinity
  have hcmp : IntegrableOn (fun x : ℝ => ((1 + ε) * X' ^ (-(α + ε)) * |f X'|) * x ^ (α + ε))
      (Ioi X') := by
    have h1 : IntegrableOn (fun x : ℝ => x ^ (α + ε)) (Ioi X') :=
      (integrableOn_Ioi_rpow_iff hX'pos).2 hεlt
    exact h1.const_mul _
  have hpt : ∀ᵐ x ∂(volume.restrict (Ioi X')),
      ‖f x‖ ≤ ((1 + ε) * X' ^ (-(α + ε)) * |f X'|) * x ^ (α + ε) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxX' : X' ≤ x := le_of_lt hx
    have hx0 : 0 < x := lt_of_lt_of_le hX'pos hxX'
    have h1 := (hpot x X' hXX' hxX').2
    have h2 : (x / X') ^ (α + ε) = x ^ (α + ε) * X' ^ (-(α + ε)) := by
      rw [Real.div_rpow hx0.le hX'pos.le, Real.rpow_neg hX'pos.le]
      ring
    rw [h2] at h1
    rw [Real.norm_eq_abs]
    calc |f x| ≤ (1 + ε) * (x ^ (α + ε) * X' ^ (-(α + ε))) * |f X'| := h1
      _ = ((1 + ε) * X' ^ (-(α + ε)) * |f X'|) * x ^ (α + ε) := by ring
  have htail : IntegrableOn f (Ioi X') :=
    Integrable.mono' hcmp hmeas.aestronglyMeasurable.restrict hpt
  -- the bounded piece
  have hbdd : IntegrableOn f (Ioc r X') := by
    have h1 : IntegrableOn f (Icc r X') :=
      (locallyIntegrableOn_iff (isLocallyClosed_Ioi)).1 hloc (Icc r X')
        (fun x hx => lt_of_lt_of_le hr hx.1) isCompact_Icc
    exact h1.mono_set Ioc_subset_Icc_self
  have hunion : Ioi r = Ioc r X' ∪ Ioi X' := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      by_cases h : x ≤ X'
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · exact lt_of_le_of_lt hrX' h2
  rw [hunion]
  exact hbdd.union htail

/-- **Kararnata's integral theorem, negative index (paper Lemma I.2.10, second half).**
If `f` is measurable, locally integrable on `(0,∞)`, eventually positive and
regularly varying of index `α < -1`, then

  `∫_r^∞ f(s) ds ∼ -r f(r)/(α+1)`   as `r → ∞`.

Note on the printed source: the paper states the constant as `r f(r)/(1-α)`; the
correct constant is `-1/(α+1) = 1/(-α-1)`, as the substitution `s = r u` shows:
`∫_r^∞ f ∼ r f(r) ∫_1^∞ u^α du = r f(r) (-1/(α+1))`.  (For `f(s) = s^α`,
`∫_r^∞ s^α ds = r^{α+1}/(-α-1)`.)  The statement below is the correct one. -/
theorem lemma_I_2_10_tail {f : ℝ → ℝ} {α : ℝ} (hα : α < -1)
    (hmeas : Measurable f) (hloc : LocallyIntegrableOn f (Ioi 0))
    (hrv : RegularlyVaryingAtTop f α) :
    Tendsto (fun R => (∫ s in Ioi R, f s) / (R * f R)) atTop (𝓝 (-1 / (α + 1))) := by
  classical
  set ε : ℝ := -(α + 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt : α + ε < -1 := by rw [hεdef]; linarith
  obtain ⟨X, hX1, hpot⟩ := hasPotterBounds_of_regularlyVarying hmeas hrv ε hεpos
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hrv.1
  -- dominated convergence in the rescaled variable
  have hDCT : Tendsto (fun R : ℝ => ∫ u in Ioi (1 : ℝ), f (R * u) / f R) atTop
      (𝓝 (-1 / (α + 1))) := by
    have hmain : Tendsto (fun R : ℝ => ∫ u in Ioi (1 : ℝ), f (R * u) / f R) atTop
        (𝓝 (∫ u in Ioi (1 : ℝ), u ^ α)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (Ioi (1 : ℝ)))
        (bound := fun u : ℝ => (1 + ε) * u ^ (α + ε)) ?_ ?_ ?_ ?_
      · filter_upwards with R
        exact ((hmeas.comp (measurable_const.mul measurable_id)).div_const _).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop (max X Y₀)] with R hR
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu1 : (1 : ℝ) < u := hu
        have hR1 : (1 : ℝ) ≤ max X Y₀ := le_trans hX1 (le_max_left _ _)
        have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one (le_trans hR1 hR)
        have hRX : X ≤ R := le_trans (le_max_left _ _) hR
        have hRY₀ : Y₀ ≤ R := le_trans (le_max_right _ _) hR
        have hfR : f R ≠ 0 := hY₀ R hRY₀
        have hRu : R ≤ R * u := by nlinarith
        have h1 := (hpot (R * u) R hRX hRu).2
        rw [Real.norm_eq_abs, abs_div]
        rw [div_le_iff₀ (abs_pos.2 hfR)]
        calc |f (R * u)| ≤ (1 + ε) * (R * u / R) ^ (α + ε) * |f R| := h1
          _ = ((1 + ε) * u ^ (α + ε)) * |f R| := by
              rw [show R * u / R = u by rw [mul_comm R u, mul_div_cancel_right₀ u hR0.ne']]
      · have h1 : IntegrableOn (fun u : ℝ => u ^ (α + ε)) (Ioi (1 : ℝ)) :=
          (integrableOn_Ioi_rpow_iff one_pos).2 hεlt
        exact h1.const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := by have h := hu; rw [mem_Ioi] at h; linarith
        simpa [mul_comm] using hrv.2 u hu0
    have hval : (∫ u in Ioi (1 : ℝ), u ^ α) = -1 / (α + 1) := by
      rw [integral_Ioi_rpow_of_lt hα one_pos, Real.one_rpow, neg_div]
    rwa [hval] at hmain
  -- identify the rescaled integral with the original one
  refine hDCT.congr' ?_
  filter_upwards [eventually_ge_atTop (max 1 Y₀)] with R hR
  have hR1 : 1 ≤ max 1 Y₀ := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one (le_trans hR1 hR)
  have hRY₀ : Y₀ ≤ R := le_trans (le_max_right _ _) hR
  have hfR : f R ≠ 0 := hY₀ R hRY₀
  have hsubst : ∫ s in Ioi R, f s = R * ∫ u in Ioi (1 : ℝ), f (R * u) := by
    have h := integral_comp_mul_left_Ioi' (g := f) (a := (1 : ℝ)) (b := R) hR0
    rw [mul_one] at h
    rw [← h, smul_eq_mul]
  rw [hsubst, mul_div_mul_left _ _ hR0.ne', MeasureTheory.integral_div]

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.Analysis

/-! ### Further properties from the paper's Section I.2.2 (p. 25-27) -/

/-- **The uniform convergence theorem for the ratios** (BGT Theorem 1.2.1), in the
`HasLocalUniformRatio` form used by `Analysis/PotterBounded.lean`: for eventually
positive measurable `f` regularly varying of index `α`, the ratios `f (l y)/f y`
converge to `l ^ α` uniformly for `l` in compact subsets of `(0,∞)`.

Eventual positivity is used only to identify the ratio with its absolute value;
without it the content is `tendsto_uniformly_abs_ratio_of_regularlyVarying`. -/
theorem hasLocalUniformRatio_of_regularlyVarying {f : ℝ → ℝ} {α : ℝ} (hmeas : Measurable f)
    (hrv : RegularlyVaryingAtTop f α) (hpos : ∀ᶠ x in atTop, 0 < f x) :
    HasLocalUniformRatio f α := by
  intro δ hδ η hη
  obtain ⟨Y, hY1, hY⟩ := tendsto_uniformly_abs_ratio_of_regularlyVarying hmeas hrv
    (a := 1) (b := 1 + δ) one_pos (by linarith) hη
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.1 hpos
  refine ⟨max Y Y₁, le_trans hY1 (le_max_left _ _), fun y hy l hl => ?_⟩
  have hyY : Y ≤ y := le_trans (le_max_left _ _) hy
  have hyY₁ : Y₁ ≤ y := le_trans (le_max_right _ _) hy
  have hY1le : 1 ≤ max Y Y₁ := le_trans hY1 (le_max_left _ _)
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one (le_trans hY1le hy)
  have hl1 : 1 ≤ l := hl.1
  have hly1 : Y₁ ≤ l * y := le_trans hyY₁ (by nlinarith)
  have hlypos : 0 < f (l * y) := hY₁ _ hly1
  have hkey := hY y hyY l hl
  rwa [abs_of_pos hlypos, abs_of_pos (hY₁ y hyY₁)] at hkey

/-- **Karamata's integral theorem (paper Lemma I.2.10), unconditional form.**
If `f` is measurable, locally integrable on `(0,∞)`, eventually positive and
regularly varying of index `α > -1`, then `∫_1^r f ∼ r f(r)/(α+1)`.
Potter's bounds are now *derived* (`hasPotterBounds_of_regularlyVarying`), so this
is the paper's lemma with no additional hypothesis. -/
theorem lemma_I_2_10_of_regularlyVarying {f : ℝ → ℝ} {α : ℝ} (hα : -1 < α)
    (hmeas : Measurable f) (hloc : LocallyIntegrableOn f (Ioi 0))
    (hposf : ∀ᶠ x in atTop, 0 < f x) (hrv : RegularlyVaryingAtTop f α) :
    Tendsto (fun r => (∫ s in 1..r, f s) / (r * f r)) atTop (𝓝 (1 / (α + 1))) :=
  lemma_I_2_10 hα hmeas hloc hposf hrv (hasPotterBounds_of_regularlyVarying hmeas hrv)

/-- **Regular variation is preserved by asymptotic equivalence** (paper, p. 26):
if `f x / g x → 1` and `g` is regularly varying of index `α`, then so is `f`. -/
theorem RegularlyVaryingAtTop.of_tendsto_div {f g : ℝ → ℝ} {α : ℝ}
    (hg : RegularlyVaryingAtTop g α) (hfg : Tendsto (fun x : ℝ => f x / g x) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f α := by
  constructor
  · have h1 : ∀ᶠ x in atTop, 0 < f x / g x := hfg.eventually (eventually_gt_nhds zero_lt_one)
    filter_upwards [h1] with x hx
    intro h
    rw [h, zero_div] at hx
    exact lt_irrefl 0 hx
  · intro l hl
    obtain ⟨Y, hY⟩ := eventually_atTop.1 hg.1
    have hpos' : ∀ᶠ x in atTop, 0 < f x / g x := hfg.eventually (eventually_gt_nhds zero_lt_one)
    have hratio : (fun x : ℝ => f (l * x) / f x) =ᶠ[atTop]
        fun x => (f (l * x) / g (l * x)) / (f x / g x) * (g (l * x) / g x) := by
      filter_upwards [eventually_ge_atTop Y, eventually_ge_atTop (Y / l), hpos'] with x hx hxl hposx
      have hlx : Y ≤ l * x := by
        rw [div_le_iff₀ hl] at hxl
        linarith
      have hfx : f x ≠ 0 := by
        intro h
        rw [h, zero_div] at hposx
        exact lt_irrefl 0 hposx
      have hgx : g x ≠ 0 := hY x hx
      have hglx : g (l * x) ≠ 0 := hY (l * x) hlx
      field_simp
    have h2 : Tendsto (fun x : ℝ => (f (l * x) / g (l * x)) / (f x / g x) * (g (l * x) / g x))
        atTop (𝓝 (1 / 1 * l ^ α)) := by
      have hnum : Tendsto (fun x : ℝ => f (l * x) / g (l * x)) atTop (𝓝 1) :=
        hfg.comp ((tendsto_const_mul_atTop_of_pos hl).2 tendsto_id)
      exact (hnum.div hfg one_ne_zero).mul (hg.2 l hl)
    rw [div_one, one_mul] at h2
    exact h2.congr' (Filter.EventuallyEq.symm hratio)

/-- **Every regularly varying function is a power times a slowly varying one**
(paper, p. 26): `f x = x^α ℓ x` with `ℓ` slowly varying. -/
theorem slowlyVarying_div_rpow {f : ℝ → ℝ} {α : ℝ} (hrv : RegularlyVaryingAtTop f α) :
    SlowlyVaryingAtTop (fun x => f x / x ^ α) := by
  have h1 : RegularlyVaryingAtTop (fun x : ℝ => (x ^ α)⁻¹) (-α) :=
    (regularlyVaryingAtTop_rpow α).inv
  have h2 : RegularlyVaryingAtTop (fun x : ℝ => f x * (x ^ α)⁻¹) (α + -α) := hrv.mul h1
  have h3 : α + -α = 0 := by ring
  rw [h3] at h2
  simpa [SlowlyVaryingAtTop, div_eq_mul_inv] using h2

/-- **Regularly varying functions of negative index are logarithmically integrable
error functions** (paper, p. 26). -/
theorem isLogErrorFunction_of_regularlyVarying {f : ℝ → ℝ} {α : ℝ} (hα : α < 0)
    (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f α) :
    IsLogErrorFunction f := by
  classical
  set ε : ℝ := -α / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt : α + ε < 0 := by rw [hεdef]; linarith
  have hεlt' : α + ε - 1 < -1 := by linarith
  obtain ⟨X, hX1, hpot⟩ := hasPotterBounds_of_regularlyVarying hmeas hrv ε hεpos
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hbound : ∀ x ≥ X, |f x| ≤ ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε) := by
    intro x hx
    have h1 := (hpot x X le_rfl hx).2
    have h2 : (x / X) ^ (α + ε) = x ^ (α + ε) * X ^ (-(α + ε)) := by
      rw [Real.div_rpow (lt_of_lt_of_le hXpos hx).le hXpos.le, Real.rpow_neg hXpos.le]
      ring
    rw [h2] at h1
    calc |f x| ≤ (1 + ε) * (x ^ (α + ε) * X ^ (-(α + ε))) * |f X| := h1
      _ = ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε) := by ring
  constructor
  · constructor
    · exact hmeas
    · refine ⟨X, hXpos, ?_⟩
      have hcmp : IntegrableOn (fun x : ℝ => ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε - 1))
          (Ioi X) := by
        have h1 : IntegrableOn (fun x : ℝ => x ^ (α + ε - 1)) (Ioi X) :=
          (integrableOn_Ioi_rpow_iff hXpos).2 hεlt'
        exact h1.const_mul _
      refine hcmp.mono' ((hmeas.abs.div measurable_id).aestronglyMeasurable.restrict) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxX : X ≤ x := le_of_lt hx
      have hx0 : 0 < x := lt_of_lt_of_le hXpos hxX
      have h1 := hbound x hxX
      have hrpow : x ^ (α + ε) = x ^ (α + ε - 1) * x := by
        have h : x ^ (α + ε - 1 + 1) = x ^ (α + ε - 1) * x ^ (1 : ℝ) :=
          Real.rpow_add hx0 _ _
        rw [Real.rpow_one] at h
        rwa [show α + ε - 1 + 1 = α + ε by ring] at h
      have hgoal : |f x| / x ≤ ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε - 1) := by
        rw [div_le_iff₀ hx0]
        calc |f x| ≤ ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε) := h1
          _ = ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε - 1) * x := by
              rw [hrpow]; ring
      simpa [Real.norm_eq_abs, abs_div, abs_of_pos hx0] using hgoal
  · have hzero : Tendsto (fun x : ℝ => ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε))
        atTop (𝓝 0) := by
      have h2 : Tendsto (fun x : ℝ => x ^ (α + ε)) atTop (𝓝 0) := by
        have h := tendsto_rpow_neg_atTop (y := -(α + ε)) (by linarith : (0:ℝ) < -(α + ε))
        simpa using h
      simpa [mul_comm] using h2.const_mul ((1 + ε) * X ^ (-(α + ε)) * |f X|)
    refine squeeze_zero_norm'
      (a := fun x : ℝ => ((1 + ε) * X ^ (-(α + ε)) * |f X|) * x ^ (α + ε)) ?_ hzero
    filter_upwards [eventually_ge_atTop X] with x hx
    rw [Real.norm_eq_abs]
    exact hbound x hx

end PercLib.CriticalLRP.Analysis

/-! ### Axiom audit (all theorems of this file) -/

#print axioms PercLib.CriticalLRP.Analysis.sdiff_inter_preimage_eq
#print axioms PercLib.CriticalLRP.Analysis.volume_preimage_add_right
#print axioms PercLib.CriticalLRP.Analysis.vadd_set_eq_image_add_right
#print axioms PercLib.CriticalLRP.Analysis.volume_sdiff_inter_preimage_le
#print axioms PercLib.CriticalLRP.Analysis.exists_forall_exists_add_mem
#print axioms PercLib.CriticalLRP.Analysis.tendsto_uniform_additive
#print axioms PercLib.CriticalLRP.Analysis.tendsto_log_abs_ratio_sub
#print axioms PercLib.CriticalLRP.Analysis.tendsto_uniformly_abs_ratio_of_regularlyVarying
#print axioms PercLib.CriticalLRP.Analysis.potter_core
#print axioms PercLib.CriticalLRP.Analysis.hasPotterBounds_of_regularlyVarying
#print axioms PercLib.CriticalLRP.Analysis.integrableOn_Ioi_of_regularlyVarying
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_2_10_tail
#print axioms PercLib.CriticalLRP.Analysis.hasLocalUniformRatio_of_regularlyVarying
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_2_10_of_regularlyVarying
#print axioms PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.of_tendsto_div
#print axioms PercLib.CriticalLRP.Analysis.slowlyVarying_div_rpow
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_of_regularlyVarying
