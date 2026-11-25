/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The pivotal flux of a cluster functional, and finite pivotal flux

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.1 and its proof.  The paper writes
Russo's formula in infinite volume as

  `∂/∂r E_{β,r} |K|^p = β|J'(r)| ∑_{x∈K} ∑_{y ∈ B_r(x)} 1(y ∉ K)
        ((|K| + |K_y|)^p − |K|^p)`,

and remarks that applying Russo's formula "to these moments directly in infinite
volume when `β ≤ β_c` and `r < ∞` is a standard consequence of the sharpness of
the phase transition".  The two quantitative inputs isolated here are:

* **locality**: flipping the state of an edge `e` changes no functional of the
  cluster of `o` unless `e` touches that cluster (`flipDiff_eq_zero`), so the
  `e`-th pivot weight is at most `2 sup |g|` times the probability that `e`
  touches the cluster (`abs_pivotalFlux_le`);
* **the degree bound**: the pivot weights of the edges incident to the vertices
  of a finite edge set are at most `D` per vertex
  (`FiniteVolume.sum_touchSet_le`).

Consequently the pivotal flux is absolutely summable as soon as the expected
cluster volume `∫⁻ |K|` is finite — `tsum_abs_pivotalFlux_le`.  This is the
"finite pivotal flux" half of the missing sharpness input of Lemma I.4.1; the
remaining step is the exchange of the `r`-derivative with the infinite edge sum.
-/
module

public import PercLib.CriticalLRP.RussoInf.Geometry
public import PercLib.CriticalLRP.RussoInf.Degree
public import PercLib.CriticalLRP.CountableProduct.Base

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The change of a functional of the configuration when the state of the edge `e` is changed from
closed to open.  This is the summand of the pivotal (Russo) sum. -/
noncomputable def flipDiff (g : Config V → ℝ) (e : Sym2 V) (ω : Config V) : ℝ :=
  g (forceOn {e} {e} ω) - g (forceOn {e} ∅ ω)

/-- The pivotal flux of the edge `e` for the functional `g`: the mean flip difference. -/
noncomputable def pivotalFlux (μ : Measure (Config V)) (g : Config V → ℝ) (e : Sym2 V) : ℝ :=
  ∫ ω, flipDiff g e ω ∂μ

theorem measurableSet_touchSet_mem {o : V} (e : Sym2 V) :
    MeasurableSet {ω : Config V | e ∈ touchSet ω o} := by
  have h : {ω : Config V | e ∈ touchSet ω o}
      = ⋃ v : (e : Set V), {ω : Config V | (v : V) ∈ cluster ω o} := by
    ext ω
    simp only [mem_touchSet, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, hcv⟩
      exact ⟨⟨v, hv⟩, hcv⟩
    · rintro ⟨⟨v, hv⟩, hcv⟩
      exact ⟨v, hv, hcv⟩
  rw [h]
  exact MeasurableSet.iUnion fun v => measurableSet_cluster_mem o (v : V)

/-- The indicator of the touching set, in `if` form, is measurable. -/
theorem measurable_touchInd {o : V} (e : Sym2 V) :
    Measurable fun ω : Config V => (if e ∈ touchSet ω o then (1 : ℝ) else 0) := by
  have h : Measurable fun ω : Config V =>
      ({ω : Config V | e ∈ touchSet ω o}.indicator (fun _ => (1 : ℝ))) ω :=
    Measurable.indicator (measurable_const : Measurable fun _ : Config V => (1 : ℝ))
      (measurableSet_touchSet_mem (o := o) e)
  have hfun : (fun ω : Config V => (if e ∈ touchSet ω o then (1 : ℝ) else 0))
      = ({ω : Config V | e ∈ touchSet ω o}.indicator (fun _ => (1 : ℝ))) := by
    funext ω
    by_cases hmem : e ∈ touchSet ω o
    · rw [ite_eq_left hmem,
        Set.indicator_of_mem (show ω ∈ {ω : Config V | e ∈ touchSet ω o} from hmem)]
    · rw [ite_eq_right hmem,
        Set.indicator_of_notMem (show ω ∉ {ω : Config V | e ∈ touchSet ω o} from hmem)]
  rw [hfun]
  exact h

/-- The indicator of the cluster of `o`, in `if` form, is measurable. -/
theorem measurable_clusterInd {o : V} (x : V) :
    Measurable fun ω : Config V => (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
  have h : Measurable fun ω : Config V =>
      ({ω : Config V | x ∈ cluster ω o}.indicator (fun _ => (1 : ℝ))) ω :=
    Measurable.indicator (measurable_const : Measurable fun _ : Config V => (1 : ℝ))
      (measurableSet_cluster_mem o x)
  have hfun : (fun ω : Config V => (if x ∈ cluster ω o then (1 : ℝ) else 0))
      = ({ω : Config V | x ∈ cluster ω o}.indicator (fun _ => (1 : ℝ))) := by
    funext ω
    by_cases hmem : x ∈ cluster ω o
    · rw [ite_eq_left hmem,
        Set.indicator_of_mem (show ω ∈ {ω : Config V | x ∈ cluster ω o} from hmem)]
    · rw [ite_eq_right hmem,
        Set.indicator_of_notMem (show ω ∉ {ω : Config V | x ∈ cluster ω o} from hmem)]
  rw [hfun]
  exact h

/-- The flip difference is bounded by twice the sup norm. -/
theorem abs_flipDiff_le_sup {g : Config V → ℝ} {m : ℝ} (hbound : ∀ ω, |g ω| ≤ m)
    (e : Sym2 V) (ω : Config V) :
    |flipDiff g e ω| ≤ 2 * m := by
  unfold flipDiff
  calc |g (forceOn {e} {e} ω) - g (forceOn {e} ∅ ω)|
      ≤ |g (forceOn {e} {e} ω)| + |g (forceOn {e} ∅ ω)| := abs_sub _ _
    _ ≤ m + m := add_le_add (hbound _) (hbound _)
    _ = 2 * m := by ring

/-- The integral of the touching-set indicator is the probability that `e` touches the cluster. -/
theorem integral_touchInd {o : V} (μ : Measure (Config V)) (e : Sym2 V) :
    ∫ ω : Config V, (if e ∈ touchSet ω o then (1 : ℝ) else 0) ∂μ
      = μ.real {ω : Config V | e ∈ touchSet ω o} := by
  have hfun : (fun ω : Config V => (if e ∈ touchSet ω o then (1 : ℝ) else 0))
      = ({ω : Config V | e ∈ touchSet ω o}.indicator (fun _ => (1 : ℝ))) := by
    funext ω
    by_cases hmem : e ∈ touchSet ω o
    · rw [ite_eq_left hmem,
        Set.indicator_of_mem (show ω ∈ {ω : Config V | e ∈ touchSet ω o} from hmem)]
    · rw [ite_eq_right hmem,
        Set.indicator_of_notMem (show ω ∉ {ω : Config V | e ∈ touchSet ω o} from hmem)]
  rw [hfun]
  exact integral_indicator_one (measurableSet_touchSet_mem e)

/-- The integral of the cluster indicator is the probability that `x` lies in the cluster. -/
theorem integral_clusterInd {o : V} (μ : Measure (Config V)) (x : V) :
    ∫ ω : Config V, (if x ∈ cluster ω o then (1 : ℝ) else 0) ∂μ
      = μ.real {ω : Config V | x ∈ cluster ω o} := by
  have hfun : (fun ω : Config V => (if x ∈ cluster ω o then (1 : ℝ) else 0))
      = ({ω : Config V | x ∈ cluster ω o}.indicator (fun _ => (1 : ℝ))) := by
    funext ω
    by_cases hmem : x ∈ cluster ω o
    · rw [ite_eq_left hmem,
        Set.indicator_of_mem (show ω ∈ {ω : Config V | x ∈ cluster ω o} from hmem)]
    · rw [ite_eq_right hmem,
        Set.indicator_of_notMem (show ω ∉ {ω : Config V | x ∈ cluster ω o} from hmem)]
  rw [hfun]
  exact integral_indicator_one (measurableSet_cluster_mem o x)

/-- The `ℝ≥0∞`-valued cluster indicator is measurable. -/
theorem measurable_clusterIndENN {o : V} (x : V) :
    Measurable fun ω : Config V => (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) := by
  have h : Measurable fun ω : Config V =>
      ENNReal.ofReal (if x ∈ cluster ω o then (1 : ℝ) else 0) :=
    ENNReal.measurable_ofReal.comp (measurable_clusterInd x)
  have hfun : (fun ω : Config V => (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0))
      = fun ω : Config V => ENNReal.ofReal (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
    funext ω
    by_cases hmem : x ∈ cluster ω o <;> simp [hmem]
  rw [hfun]
  exact h

/-- The `ℝ≥0∞`-integral of a cluster indicator is the probability of the cluster event. -/
theorem lintegral_clusterIndENN {o : V} (μ : Measure (Config V)) (x : V) :
    ∫⁻ ω : Config V, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ
      = μ {ω : Config V | x ∈ cluster ω o} := by
  rw [← lintegral_indicator_one (measurableSet_cluster_mem o x)]
  exact lintegral_congr fun ω => by
    by_cases h : x ∈ cluster ω o
    · simp only [ite_eq_left h,
        Set.indicator_of_mem (show ω ∈ {ω : Config V | x ∈ cluster ω o} from h), Pi.one_apply]
    · simp only [ite_eq_right h,
        Set.indicator_of_notMem (show ω ∉ {ω : Config V | x ∈ cluster ω o} from h)]

/-- Integrability of the real-valued cluster indicator. -/
theorem integrable_clusterInd {o : V} (μ : Measure (Config V)) [IsFiniteMeasure μ] (x : V) :
    Integrable (fun ω : Config V => (if x ∈ cluster ω o then (1 : ℝ) else 0)) μ := by
  refine Integrable.of_bound (Measurable.aestronglyMeasurable (measurable_clusterInd x)) 1 ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  by_cases h : x ∈ cluster ω o <;> simp [h]

/-- **Locality of the pivot**: the flip difference of a functional of the cluster of `o` vanishes
unless the flipped edge touches that cluster. -/
theorem flipDiff_eq_zero {o : V} {g : Config V → ℝ}
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    {e : Sym2 V} {ω : Config V} (h : e ∉ touchSet ω o) :
    flipDiff g e ω = 0 := by
  have h1 : cluster (forceOn {e} {e} ω) o = cluster ω o :=
    cluster_forceOn_singleton_eq_of_notMem_touchSet h {e}
  have h2 : cluster (forceOn {e} ∅ ω) o = cluster ω o :=
    cluster_forceOn_singleton_eq_of_notMem_touchSet h ∅
  unfold flipDiff
  rw [hdep _ _ h1, hdep _ _ h2, sub_self]

/-- The flip difference is bounded by twice the sup norm, and supported on the touching set. -/
theorem abs_flipDiff_le {o : V} {g : Config V → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hbound : ∀ ω, |g ω| ≤ m)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (e : Sym2 V) (ω : Config V) :
    |flipDiff g e ω| ≤ 2 * m * (if e ∈ touchSet ω o then (1 : ℝ) else 0) := by
  by_cases h : e ∈ touchSet ω o
  · rw [ite_eq_left h, mul_one]
    exact abs_flipDiff_le_sup hbound e ω
  · rw [ite_eq_right h, mul_zero]
    rw [flipDiff_eq_zero hdep h, abs_zero]

/-- **The pivot bound.**  For a bounded functional of the cluster of `o`, the absolute pivotal flux
of `e` is at most `2 sup |g|` times the probability that `e` touches the cluster. -/
theorem abs_pivotalFlux_le {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ ω, |g ω| ≤ m)
    (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (e : Sym2 V) :
    |pivotalFlux μ g e| ≤ 2 * m * μ.real {ω : Config V | e ∈ touchSet ω o} := by
  classical
  set s : Set (Config V) := {ω : Config V | e ∈ touchSet ω o} with hs_def
  have hs : MeasurableSet s := measurableSet_touchSet_mem e
  have hmeasf : Measurable (flipDiff g e) := by
    unfold flipDiff
    exact (hmeas.comp (measurable_forceOn _ _)).sub (hmeas.comp (measurable_forceOn _ _))
  have hpt : ∀ ω, ‖flipDiff g e ω‖ ≤ (2 * m) * (s.indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    have hif : (if e ∈ touchSet ω o then (1 : ℝ) else 0)
        = s.indicator (fun _ => (1 : ℝ)) ω := by
      by_cases hmem : e ∈ touchSet ω o
      · have hmem' : ω ∈ s := by rw [hs_def]; exact hmem
        rw [ite_eq_left hmem, Set.indicator_of_mem hmem']
      · have hmem' : ω ∉ s := by rw [hs_def]; exact hmem
        rw [ite_eq_right hmem, Set.indicator_of_notMem hmem']
    rw [Real.norm_eq_abs, ← hif]
    exact abs_flipDiff_le hm hbound hdep e ω
  have hind : Integrable (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω)) μ := by
    refine Integrable.of_bound (Measurable.aestronglyMeasurable ?_) 1 ?_
    · fun_prop
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases hmem : ω ∈ s <;> simp [Set.indicator_apply, hmem]
  have hInt : Integrable (fun ω => (2 * m) * (s.indicator (fun _ => (1 : ℝ)) ω)) μ :=
    hind.const_mul _
  calc |pivotalFlux μ g e| = |∫ ω, flipDiff g e ω ∂μ| := rfl
    _ ≤ ∫ ω, ‖flipDiff g e ω‖ ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun ω => flipDiff g e ω) (μ := μ))
    _ ≤ ∫ ω, (2 * m) * (s.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hInt
          (Eventually.of_forall hpt)
    _ = (2 * m) * μ.real s := by
        rw [integral_const_mul,
          show ∫ a, s.indicator (fun _ => (1 : ℝ)) a ∂μ = μ.real s from
            integral_indicator_one hs]

/-! ## The total pivot weight attached to a finite set of edges -/

/-- The finite vertex set covered by a finite set of edges. -/
noncomputable def edgeVertices (u : Finset (Sym2 V)) : Finset V :=
  u.biUnion (fun e => e.toFinset)

theorem mem_edgeVertices {u : Finset (Sym2 V)} {x : V} {e : Sym2 V} (he : e ∈ u) (hx : x ∈ e) :
    x ∈ edgeVertices u :=
  Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hx⟩

/-- **Vertex-bounded total pivot weight.**  The number of edges of `u` touching the cluster,
weighted by `|c|`, is at most `D` per cluster vertex among the endpoints of `u`. -/
theorem sum_touchSet_weight_le {o : V} (c : Sym2 V → ℝ) {D : ℝ}
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (u : Finset (Sym2 V)) (ω : Config V) :
    ∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)
      ≤ D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) := by
  classical
  set S : Finset V := (edgeVertices u).filter (fun x => x ∈ cluster ω o) with hS
  have h1 : ∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)
      ≤ ∑ e ∈ u, |c e| * ∑ x ∈ S, (if x ∈ e then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun e he => ?_
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    by_cases h : e ∈ touchSet ω o
    · rw [ite_eq_left h]
      obtain ⟨x, hxe, hxK⟩ := h
      have hxS : x ∈ S := Finset.mem_filter.mpr ⟨mem_edgeVertices he hxe, hxK⟩
      have h2 := Finset.single_le_sum (f := fun x => if x ∈ e then (1 : ℝ) else 0)
        (fun i _ => by positivity) hxS
      simpa [hxe] using h2
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg fun i _ => by positivity
  refine h1.trans ?_
  have hswap : ∑ e ∈ u, |c e| * ∑ x ∈ S, (if x ∈ e then (1 : ℝ) else 0)
      = ∑ x ∈ S, ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  calc ∑ x ∈ S, ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0)
      ≤ ∑ _x ∈ S, D := Finset.sum_le_sum fun x _ => hdeg x u
    _ = D * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The cardinality of a finite set of cluster points is at most the extended cluster volume. -/
theorem card_filter_cluster_le_clusterVol {o : V} (S : Finset V) (ω : Config V) :
    ((S.filter (fun x => x ∈ cluster ω o)).card : ℝ≥0∞) ≤ clusterVol ω o := by
  classical
  set T : Finset V := S.filter (fun x => x ∈ cluster ω o) with hT
  have h1 : ∀ x : V, (T : Set V).indicator (fun _ => (1 : ℝ≥0∞)) x
      ≤ (cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ T
    · have hxK : x ∈ cluster ω o := by
        have := hx
        rw [hT] at this
        exact (Finset.mem_filter.mp this).2
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hx]
      simp
  calc ((T).card : ℝ≥0∞)
      = ∑' x : V, (T : Set V).indicator (fun _ => (1 : ℝ≥0∞)) x := by
        rw [tsum_indicator_eq_encard (T : Set V), encard_coe_eq_ncard_coe T.finite_toSet,
          Set.ncard_coe_finset]
    _ ≤ ∑' x : V, (cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) x := ENNReal.tsum_le_tsum h1
    _ = clusterVol ω o := (clusterVol_eq_tsum ω o).symm

end PercLib.CriticalLRP
