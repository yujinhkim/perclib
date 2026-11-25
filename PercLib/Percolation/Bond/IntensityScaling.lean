/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 168 (Q-25), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Coupling.Monotone
public import PercLib.Probability.OpenEventHarris

/-!
# The intensity family: kernel scaling, kernel comparison and large intensity

For `q_β = intensityProfile J β`:

* **scaling**: `intensityProfile (c • J) β = intensityProfile J (c * β)`, so both critical
  intensities of `c • J` are those of `J` divided by `c` when `c > 0`, and are `⊤` when
  `c = 0`;
* **comparison**: `J ≤ J'` gives `q_β ≤ q'_β`, hence larger `τ`, `χ`, `θ` and smaller
  critical intensities;
* **large intensity**: each coordinate increases continuously to `1` when `J e > 0`
  (strictly) and is `0` when `J e = 0`; if `x` and `y` are joined in the support graph of
  `J`, then `τ(x, y) → 1` as `β → ∞`.

This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set Filter Topology PercLib.Probability
open scoped ENNReal NNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Scaling -/

/-- **Scaling the kernel is scaling the intensity.** -/
theorem intensityProfile_smul (J : Sym2 V → ℝ≥0) (c β : ℝ≥0) :
    intensityProfile (c • J) β = intensityProfile J (c * β) := by
  funext e
  apply Subtype.ext
  change 1 - Real.exp (-(β : ℝ) * (((c • J) e : ℝ≥0) : ℝ)) =
    1 - Real.exp (-((c * β : ℝ≥0) : ℝ) * (J e : ℝ))
  simp only [Pi.smul_apply, smul_eq_mul, NNReal.coe_mul]
  ring_nf

/-- Thresholds of a reparametrised family. If `g β = f (c * β)` with `c > 0`, the infimum
of the parameters where `g` is positive is that of `f` divided by `c`. -/
theorem sInf_pos_comp_mul (f g : ℝ≥0 → ℝ≥0∞) {c : ℝ≥0} (hc : 0 < c)
    (hg : ∀ β, g β = f (c * β)) :
    sInf {b : ℝ≥0∞ | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧ 0 < g β} =
      sInf {b : ℝ≥0∞ | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧ 0 < f β} / c := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hct : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  refine le_antisymm ?_ ?_
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    refine le_sInf ?_
    rintro _ ⟨γ, rfl, hγ⟩
    have hmem : ((γ / c : ℝ≥0) : ℝ≥0∞) ∈ {b : ℝ≥0∞ | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧ 0 < g β} :=
      ⟨γ / c, rfl, by rwa [hg, mul_div_cancel₀ _ hc.ne']⟩
    have hle := sInf_le hmem
    calc _ ≤ ((γ / c : ℝ≥0) : ℝ≥0∞) * c := mul_le_mul_left hle _
      _ = γ := by rw [← ENNReal.coe_mul, div_mul_cancel₀ _ hc.ne']
  · refine le_sInf ?_
    rintro _ ⟨β, rfl, hβ⟩
    refine ENNReal.div_le_of_le_mul ?_
    have hmem : ((c * β : ℝ≥0) : ℝ≥0∞) ∈ {b : ℝ≥0∞ | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧ 0 < f β} :=
      ⟨c * β, rfl, by rwa [← hg]⟩
    refine (sInf_le hmem).trans (le_of_eq ?_)
    rw [ENNReal.coe_mul, mul_comm]

/-- **Scaling the kernel divides the root critical intensity.** -/
theorem rootCriticalIntensity_smul (J : Sym2 V → ℝ≥0) {c : ℝ≥0} (hc : 0 < c) (x : V) :
    rootCriticalIntensity (c • J) x = rootCriticalIntensity J x / c :=
  sInf_pos_comp_mul _ _ hc fun β => by rw [intensityProfile_smul]

/-- **Scaling the kernel divides the global critical intensity.** -/
theorem globalCriticalIntensity_smul (J : Sym2 V → ℝ≥0) {c : ℝ≥0} (hc : 0 < c) :
    globalCriticalIntensity (c • J) = globalCriticalIntensity J / c :=
  sInf_pos_comp_mul _ _ hc fun β => by rw [intensityProfile_smul]

/-- The zero kernel has row sums zero. -/
theorem rowSum_zero_smul_le (J : Sym2 V → ℝ≥0) (v : V) :
    (∑' w, if w = v then 0 else (((0 : ℝ≥0) • J) s(v, w) : ℝ≥0∞)) ≤ (0 : ℝ≥0) := by
  classical
  simp

/-- **The zero kernel never percolates:** its global critical intensity is `⊤`. -/
theorem globalCriticalIntensity_zero_smul [Countable V] (J : Sym2 V → ℝ≥0) :
    globalCriticalIntensity ((0 : ℝ≥0) • J) = ⊤ := by
  classical
  refine sInf_eq_top.2 ?_
  rintro _ ⟨β, rfl, hβ⟩
  rw [law_exists_infinite_intensity_eq_zero _ 0 (rowSum_zero_smul_le J) β (by simp)] at hβ
  exact absurd hβ (lt_irrefl _)

/-- **The zero kernel never percolates:** its root critical intensity is `⊤`. -/
theorem rootCriticalIntensity_zero_smul [Countable V] (J : Sym2 V → ℝ≥0) (x : V) :
    rootCriticalIntensity ((0 : ℝ≥0) • J) x = ⊤ := by
  classical
  refine sInf_eq_top.2 ?_
  rintro _ ⟨β, rfl, hβ⟩
  rw [law_cluster_infinite_intensity_eq_zero _ 0 (rowSum_zero_smul_le J) β (by simp) x] at hβ
  exact absurd hβ (lt_irrefl _)

/-! ### Comparison of kernels -/

/-- **A larger kernel gives a larger profile.** -/
theorem intensityProfile_le_of_le {J J' : Sym2 V → ℝ≥0} (h : J ≤ J') (β : ℝ≥0) :
    intensityProfile J β ≤ intensityProfile J' β := fun e => by
  change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) ≤ 1 - Real.exp (-(β : ℝ) * (J' e : ℝ))
  have h1 : (β : ℝ) * (J e : ℝ) ≤ (β : ℝ) * (J' e : ℝ) :=
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (h e)) β.coe_nonneg
  have h2 := Real.exp_le_exp.2 (show -(β : ℝ) * (J' e : ℝ) ≤ -(β : ℝ) * (J e : ℝ) by linarith)
  linarith

/-- A larger kernel connects with larger probability. -/
theorem tau_le_of_le [Countable V] {J J' : Sym2 V → ℝ≥0} (h : J ≤ J') (β : ℝ≥0) (x y : V) :
    tau (intensityProfile J β) x y ≤ tau (intensityProfile J' β) x y :=
  prodBernoulli_mono_event _ _ (intensityProfile_le_of_le h β) (measurableSet_conn x y)
    (isUpperSet_conn x y)

/-- A larger kernel percolates with larger probability. -/
theorem law_cluster_infinite_le_of_le [Countable V] {J J' : Sym2 V → ℝ≥0} (h : J ≤ J')
    (β : ℝ≥0) (x : V) :
    law (intensityProfile J β) {ω | (cluster ω x).Infinite} ≤
      law (intensityProfile J' β) {ω | (cluster ω x).Infinite} :=
  prodBernoulli_mono_event _ _ (intensityProfile_le_of_le h β)
    (measurableSet_cluster_infinite x) (isUpperSet_cluster_infinite x)

/-- A larger kernel has a larger probability that some cluster is infinite. -/
theorem law_exists_cluster_infinite_le_of_le [Countable V] {J J' : Sym2 V → ℝ≥0}
    (h : J ≤ J') (β : ℝ≥0) :
    law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} ≤
      law (intensityProfile J' β) {ω | ∃ x, (cluster ω x).Infinite} := by
  refine prodBernoulli_mono_event _ _ (intensityProfile_le_of_le h β) ?_ ?_
  · rw [ofPred_exists]
    exact MeasurableSet.iUnion fun x => measurableSet_cluster_infinite x
  · rintro ω ω' hωω' ⟨x, hx⟩
    exact ⟨x, isUpperSet_cluster_infinite x hωω' hx⟩

/-- A larger kernel has a larger susceptibility. -/
theorem chi_le_of_le [Countable V] {J J' : Sym2 V → ℝ≥0} (h : J ≤ J') (β : ℝ≥0) (x : V) :
    chi (intensityProfile J β) x ≤ chi (intensityProfile J' β) x :=
  lintegral_prodBernoulli_mono _ _ (intensityProfile_le_of_le h β)
    ((measurable_of_countable _).comp (measurable_encard_cluster x))
    fun _ _ hωω' => ENat.toENNReal_le.2 (encard_le_encard (cluster_mono hωω' x))

/-- **A larger kernel has a smaller root critical intensity.** -/
theorem rootCriticalIntensity_anti [Countable V] {J J' : Sym2 V → ℝ≥0} (h : J ≤ J') (x : V) :
    rootCriticalIntensity J' x ≤ rootCriticalIntensity J x := by
  refine sInf_le_sInf ?_
  rintro _ ⟨β, rfl, hβ⟩
  exact ⟨β, rfl, lt_of_lt_of_le hβ (law_cluster_infinite_le_of_le h β x)⟩

/-- **A larger kernel has a smaller global critical intensity.** -/
theorem globalCriticalIntensity_anti [Countable V] {J J' : Sym2 V → ℝ≥0} (h : J ≤ J') :
    globalCriticalIntensity J' ≤ globalCriticalIntensity J := by
  refine sInf_le_sInf ?_
  rintro _ ⟨β, rfl, hβ⟩
  exact ⟨β, rfl, lt_of_lt_of_le hβ (law_exists_cluster_infinite_le_of_le h β)⟩

/-! ### One coordinate as a function of the intensity -/

/-- The open probability of a pair is continuous in the intensity. -/
theorem continuous_intensityProfile (J : Sym2 V → ℝ≥0) (e : Sym2 V) :
    Continuous fun β : ℝ≥0 => (intensityProfile J β e : ℝ) := by
  change Continuous fun β : ℝ≥0 => 1 - Real.exp (-(β : ℝ) * (J e : ℝ))
  fun_prop

/-- The open probability of a pair is monotone in the intensity. -/
theorem monotone_intensityProfile (J : Sym2 V → ℝ≥0) (e : Sym2 V) :
    Monotone fun β : ℝ≥0 => (intensityProfile J β e : ℝ) :=
  fun _ _ h => intensityProfile_mono J h e

/-- The open probability of a pair of positive intensity is strictly monotone. -/
theorem strictMono_intensityProfile (J : Sym2 V → ℝ≥0) {e : Sym2 V} (he : 0 < J e) :
    StrictMono fun β : ℝ≥0 => (intensityProfile J β e : ℝ) := by
  intro β β' h
  change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) < 1 - Real.exp (-(β' : ℝ) * (J e : ℝ))
  have hJ : (0 : ℝ) < J e := by exact_mod_cast he
  have h1 : (β : ℝ) * (J e : ℝ) < (β' : ℝ) * (J e : ℝ) :=
    mul_lt_mul_of_pos_right (by exact_mod_cast h) hJ
  have h2 := Real.exp_lt_exp.2 (show -(β' : ℝ) * (J e : ℝ) < -(β : ℝ) * (J e : ℝ) by linarith)
  linarith

/-- A pair of zero intensity is never open. -/
theorem intensityProfile_eq_zero_of_eq_zero (J : Sym2 V → ℝ≥0) {e : Sym2 V} (he : J e = 0)
    (β : ℝ≥0) : intensityProfile J β e = 0 := by
  apply Subtype.ext
  change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) = 0
  simp [he]

/-- **A pair of positive intensity is open with probability tending to `1`.** -/
theorem tendsto_intensityProfile_atTop (J : Sym2 V → ℝ≥0) {e : Sym2 V} (he : 0 < J e) :
    Tendsto (fun β : ℝ≥0 => (intensityProfile J β e : ℝ)) atTop (𝓝 1) := by
  change Tendsto (fun β : ℝ≥0 => 1 - Real.exp (-(β : ℝ) * (J e : ℝ))) atTop (𝓝 1)
  have hJ : (0 : ℝ) < J e := by exact_mod_cast he
  have h1 : Tendsto (fun β : ℝ≥0 => (β : ℝ) * (J e : ℝ)) atTop atTop :=
    Tendsto.atTop_mul_const hJ (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  rw [sub_zero] at h3
  refine h3.congr fun β => ?_
  simp [Function.comp, neg_mul]

/-- An open walk in the complete graph: its pairs being open forces the connection. -/
private theorem setOf_edges_subset_conn {x y : V} (p : (⊤ : SimpleGraph V).Walk x y)
    [DecidableEq V] :
    {ω : Config V | ((p.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω} ⊆ conn x y := by
  intro ω hω
  refine ⟨p.transfer (openGraph ω) fun e he => ?_⟩
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨hω (by simpa using he), SimpleGraph.not_isDiag_of_mem_edgeSet _ (p.edges_subset_edgeSet he)⟩

/-- **Large intensity connects the support graph.** If `x` and `y` are joined in the support
graph of `J`, then `τ(x, y) → 1` as `β → ∞`. No countability is needed. -/
theorem tendsto_tau_intensityProfile_atTop (J : Sym2 V → ℝ≥0) {x y : V}
    (h : (SimpleGraph.fromEdgeSet {e | 0 < J e}).Reachable x y) :
    Tendsto (fun β : ℝ≥0 => tau (intensityProfile J β) x y) atTop (𝓝 1) := by
  classical
  obtain ⟨w⟩ := h
  have hpos : ∀ e ∈ w.edges, 0 < J e := fun e he => by
    have := w.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at this
    exact this.1
  set p : (⊤ : SimpleGraph V).Walk x y := w.mapLe le_top
  have hpe : p.edges = w.edges := SimpleGraph.Walk.edges_map _ _ |>.trans (by simp)
  set F : Finset (Sym2 V) := p.edges.toFinset
  have hlow : ∀ β : ℝ≥0, ((∏ e ∈ F, unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0) :
      ℝ≥0∞) ≤ tau (intensityProfile J β) x y := fun β => by
    rw [ENNReal.ofNNReal_finsetProd, ← prodBernoulli_subset]
    exact measure_mono (setOf_edges_subset_conn p)
  have hprod : Tendsto (fun β : ℝ≥0 =>
      ((∏ e ∈ F, unitInterval.toNNReal (intensityProfile J β e) : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 1) := by
    rw [← ENNReal.coe_one, ENNReal.tendsto_coe]
    rw [← Finset.prod_const_one (s := F)]
    refine tendsto_finsetProd F fun e he => ?_
    rw [← NNReal.tendsto_coe]
    have he' : e ∈ w.edges := by rw [← hpe]; simpa [F] using he
    simpa using tendsto_intensityProfile_atTop J (hpos e he')
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hprod tendsto_const_nhds hlow
    fun β => tau_le_one _ x y

/-! ### Non-vacuity -/

/-- On `Bool` with `J ≡ 1`, the two vertices connect with probability tending to `1`. -/
example : Tendsto (fun β : ℝ≥0 => tau (intensityProfile (fun _ : Sym2 Bool => 1) β) false true)
    atTop (𝓝 1) := by
  refine tendsto_tau_intensityProfile_atTop _ (SimpleGraph.Adj.reachable ?_)
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨by simp, by decide⟩

/-- Halving and doubling: on `ℕ` with `J ≡ 1`, the threshold of `2 • J` is half that of
`J`, and the zero kernel has threshold `⊤`. -/
example : rootCriticalIntensity ((2 : ℝ≥0) • fun _ : Sym2 ℕ => (1 : ℝ≥0)) 0 =
      rootCriticalIntensity (fun _ : Sym2 ℕ => (1 : ℝ≥0)) 0 / 2 ∧
    globalCriticalIntensity ((0 : ℝ≥0) • fun _ : Sym2 ℕ => (1 : ℝ≥0)) = ⊤ :=
  ⟨by simpa using rootCriticalIntensity_smul (fun _ : Sym2 ℕ => (1 : ℝ≥0)) (c := 2) (by norm_num) 0,
    globalCriticalIntensity_zero_smul _⟩

end PercLib.Percolation.Bond
