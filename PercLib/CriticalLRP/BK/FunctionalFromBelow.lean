/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Two-cluster correlation inequalities for functionals continuous from below

This file assembles Lemma I.2.1 of Hutchcroft, arXiv:2508.18807v1, p. 21, for arbitrary
non-negative increasing functionals `F (K_x)`, `G (K_y)` of the clusters of two vertices which are
*monotone* and *continuous from below along a finite exhaustion of the edge set*
(`s < F (K_x) → s < F (K_x ∩ E_n)` for some `n`).  The three displays of the lemma are obtained:

* `twoCluster_functional_lintegral_le` : `∫_{x↮y} F G ≤ (∫ F)(∫ G)` (BK);
* `fkg_functional_lintegral_le` : `(∫ F)(∫ G) ≤ ∫ F G` (Harris--FKG);
* `twoCluster_middle_lintegral` and `twoCluster_upper_lintegral` : the two companion inequalities.

All three hold when `F`, `G` are monotone, continuous from below, non-negative and
measurable as functions of the configuration; the only percolation input is `bkEdge` (BK for
increasing finitely witnessed events, with the internal-witness refinement
`twoCluster_bk_internal`).  No use is made of BK for general Borel increasing events.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.LayerCake
public import PercLib.CriticalLRP.BK.FunctionalIndicator
public import PercLib.CriticalLRP.BK.InternalWitness

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section LevelSets
attribute [local instance] Classical.propDecidable

/-- The level set of a monotone functional of the full cluster is the union of the level sets of
its truncations, when the functional is continuous from below. -/
theorem level_eq_iUnion_level_trunc (𝓔 : ℕ → Finset E) {G : BondGraph V E} {F : Set V → ℝ}
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (x : V) (s : ℝ)
    (hFcont : ∀ ω : Set E, s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)) :
    (⋃ n, {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)})
      = {ω : Set E | s < F (cluster G ω x)} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨n, hn⟩ => lt_of_lt_of_le hn
      (hFmono _ _ (cluster_mono Set.inter_subset_left x)),
    fun h => hFcont ω h⟩

/-- **Two-cluster BK inequality for level sets** of monotone, continuous-from-below functionals. -/
theorem twoCluster_level_le_of_continuous [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n)
    {F H : Set V → ℝ} (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (s t : ℝ) :
    (edgeLaw p) ({ω : Set E | ¬ Conn G ω x y} ∩ {ω | s < F (cluster G ω x)}
        ∩ {ω | t < H (cluster G ω y)})
      ≤ (edgeLaw p) {ω | s < F (cluster G ω x)} * (edgeLaw p) {ω | t < H (cluster G ω y)} := by
  have hAunion := level_eq_iUnion_level_trunc 𝓔 (G := G) (F := F) hFmono x s (hFcont · s)
  have hBunion := level_eq_iUnion_level_trunc 𝓔 (G := G) (F := H) hHmono y t (hHcont · t)
  have := twoCluster_bk_iUnion G p hp x y
    (fun n => {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)})
    (fun n => {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)})
    (fun n => isUpperSet_level_trunc (G := G) 𝓔 hFmono x n s)
    (monotone_level_trunc (G := G) 𝓔 h𝓔mono hFmono x s)
    (fun n => internalWitnessAt_level (G := G) 𝓔 x n s)
    (fun n => isUpperSet_level_trunc (G := G) 𝓔 hHmono y n t)
    (monotone_level_trunc (G := G) 𝓔 h𝓔mono hHmono y t)
    (fun n => internalWitnessAt_level (G := G) 𝓔 y n t)
  have hord : {ω : Set E | s < F (cluster G ω x)} ∩ {ω | t < H (cluster G ω y)}
      ∩ {ω : Set E | ¬ Conn G ω x y}
      = {ω : Set E | ¬ Conn G ω x y} ∩ {ω | s < F (cluster G ω x)}
        ∩ {ω | t < H (cluster G ω y)} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [hAunion, hBunion, hord] at this
  exact this

/-- **Harris--FKG for level sets** of monotone, continuous-from-below functionals: no
finiteness/witness condition is needed, since the union-limit argument is monotone in the right
direction. -/
theorem association_level_le_of_continuous [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔)
    {F H : Set V → ℝ} (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T) (x y : V)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (s t : ℝ) :
    (edgeLaw p) {ω | s < F (cluster G ω x)} * (edgeLaw p) {ω | t < H (cluster G ω y)}
      ≤ (edgeLaw p) ({ω | s < F (cluster G ω x)} ∩ {ω | t < H (cluster G ω y)}) := by
  have hAunion := level_eq_iUnion_level_trunc 𝓔 (G := G) (F := F) hFmono x s (hFcont · s)
  have hBunion := level_eq_iUnion_level_trunc 𝓔 (G := G) (F := H) hHmono y t (hHcont · t)
  have hAm : Monotone fun n => {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} :=
    monotone_level_trunc 𝓔 h𝓔mono hFmono x s
  have hBm : Monotone fun n => {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)} :=
    monotone_level_trunc 𝓔 h𝓔mono hHmono y t
  have hstep : ∀ n, (edgeLaw p) {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} *
      (edgeLaw p) {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)}
      ≤ (edgeLaw p) ({ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} ∩
        {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)}) := by
    intro n
    have h := association_edge_finiteWitness p _ _
      (isUpperSet_level_trunc (G := G) 𝓔 hFmono x n s)
      (isUpperSet_level_trunc (G := G) 𝓔 hHmono y n t)
      (finiteWitness_of_internalWitnessAt (internalWitnessAt_level (G := G) 𝓔 x n s))
      (finiteWitness_of_internalWitnessAt (internalWitnessAt_level (G := G) 𝓔 y n t))
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at h
    exact (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (measure_ne_top _ _)).mp h
  have hmono : Monotone fun n => {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} ∩
      {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)} :=
    fun m n hmn => Set.inter_subset_inter (hAm hmn) (hBm hmn)
  calc (edgeLaw p) {ω | s < F (cluster G ω x)} * (edgeLaw p) {ω | t < H (cluster G ω y)}
      = (⨆ n, (edgeLaw p) {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)}) *
          ⨆ n, (edgeLaw p) {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)} := by
        rw [← hAunion, ← hBunion, measure_iUnion_of_monotone hAm, measure_iUnion_of_monotone hBm]
    _ = ⨆ n, (edgeLaw p) {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} *
          (edgeLaw p) {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)} :=
        iSup_mul_iSup_eq _ _ (fun m n hmn => measure_mono (hAm hmn))
          (fun m n hmn => measure_mono (hBm hmn))
    _ ≤ ⨆ n, (edgeLaw p) ({ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} ∩
          {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)}) := iSup_mono hstep
    _ = (edgeLaw p) ({ω | s < F (cluster G ω x)} ∩ {ω | t < H (cluster G ω y)}) := by
        have hun : (⋃ n, {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)} ∩
            {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)})
            = (⋃ n, {ω : Set E | s < F (cluster G (ω ∩ (𝓔 n : Set E)) x)}) ∩
              (⋃ n, {ω : Set E | t < H (cluster G (ω ∩ (𝓔 n : Set E)) y)}) := by
          ext ω
          simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨n, h1, h2⟩
            exact ⟨⟨n, h1⟩, ⟨n, h2⟩⟩
          · rintro ⟨⟨n, h1⟩, ⟨m, h2⟩⟩
            exact ⟨max n m, hAm (le_max_left n m) h1, hBm (le_max_right n m) h2⟩
        rw [← measure_iUnion_of_monotone hmono, hun, hAunion, hBunion]

end LevelSets

section LemmaI21
attribute [local instance] Classical.propDecidable

/-- **Lemma I.2.1(i)** for increasing functionals: the two-cluster correlation inequality
`∫_{x ↮ y} F (K_x) G (K_y) ≤ (∫ F (K_x)) (∫ G (K_y))`, `ℝ≥0∞` form. -/
theorem twoCluster_functional_lintegral_le [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n)
    {F H : Set V → ℝ} (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y)) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) :=
  PercLib.CriticalLRP.Percolation.LayerCake.lintegral_mul_indicator_le_of_meas_lt (fun ω => hF0 (cluster G ω x))
    (fun ω => hH0 (cluster G ω y)) hFmeas hHmeas
    (measurableSet_conn G x y).compl
    (fun s t _ _ => twoCluster_level_le_of_continuous G p hp x y 𝓔 h𝓔mono h𝓔
      hFmono hHmono hFcont hHcont s t)

/-- **Harris--FKG** for increasing functionals: `(∫ F (K_x))(∫ G (K_y)) ≤ ∫ F (K_x) G (K_y)`,
`ℝ≥0∞` form. -/
theorem fkg_functional_lintegral_le [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (x y : V) (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔)
    {F H : Set V → ℝ} (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y)) :
    (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
        (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p))
      ≤ ∫⁻ ω, ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p) :=
  PercLib.CriticalLRP.Percolation.LayerCake.lintegral_mul_ge_of_meas_lt (fun ω => hF0 (cluster G ω x))
    (fun ω => hH0 (cluster G ω y)) hFmeas hHmeas
    (fun s t _ _ => association_level_le_of_continuous G p 𝓔 h𝓔mono hFmono hHmono x y
      hFcont hHcont s t)

end LemmaI21

/-! ### The companion inequalities of Lemma I.2.1 -/

section Companions
attribute [local instance] Classical.propDecidable

/-- Additivity of the expectation over the split `{x ↔ y} ⊔ {x ↮ y}`. -/
theorem lintegral_split_conn {E : Type v} [MeasurableSpace (Set E)] {μ : Measure (Set E)}
    {G : BondGraph V E} (x y : V) (hm : MeasurableSet {ω : Set E | Conn G ω x y})
    {u : Set E → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ ω, u ω ∂μ
      = ∫⁻ ω, {ω : Set E | ¬ Conn G ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω * u ω ∂μ
        + ∫⁻ ω, ({ω : Set E | Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω * u ω ∂μ := by
  have hfun : (fun ω : Set E => u ω) = fun ω =>
      {ω : Set E | ¬ Conn G ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω * u ω
        + ({ω : Set E | Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω * u ω := by
    funext ω
    by_cases h : Conn G ω x y
    · have h' : ω ∉ ({ω : Set E | ¬ Conn G ω x y}) := fun hc => hc h
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h, h']
    · have h' : ω ∉ ({ω : Set E | Conn G ω x y}) := h
      have h'' : ω ∈ ({ω : Set E | ¬ Conn G ω x y}) := h
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h, h', h'']
  rw [hfun]
  have hm' : MeasurableSet {ω : Set E | ¬ Conn G ω x y} := hm.compl
  exact lintegral_add_left ((measurable_const.indicator hm').mul hu)
    (fun ω => ({ω : Set E | Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω * u ω)

/-- **Lemma I.2.1(ii)**: `P(A)P(B) - E[F G 1(x ↔ y)] ≤ E[F G 1(x ↮ y)]`, written without
subtraction: `(∫ F)(∫ G) ≤ ∫_{x↮y} F G + ∫_{x↔y} F G`. -/
theorem twoCluster_middle_lintegral [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n)
    {F H : Set V → ℝ} (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y)) :
    (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
        (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p))
      ≤ ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)
        + ∫⁻ ω, ({ω : Set E | Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p) := by
  have hu : Measurable fun ω : Set E =>
      ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) :=
    (hFmeas.mul hHmeas).ennreal_ofReal
  rw [← lintegral_split_conn (μ := edgeLaw p) x y (measurableSet_conn G x y) hu]
  exact fkg_functional_lintegral_le G p x y 𝓔 h𝓔mono hF0 hH0 hFmono hHmono hFcont hHcont
    hFmeas hHmeas

/-- **Lemma I.2.1(iii)**, second half: `E[F G] - E F E G ≤ E[F G 1(x ↔ y)]`, written without
subtraction. -/
theorem twoCluster_upper_lintegral [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n)
    {F H : Set V → ℝ} (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y)) :
    ∫⁻ ω, ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p))
        + ∫⁻ ω, ({ω : Set E | Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p) := by
  have hu : Measurable fun ω : Set E =>
      ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) :=
    (hFmeas.mul hHmeas).ennreal_ofReal
  have hadd := lintegral_split_conn (μ := edgeLaw p) x y (measurableSet_conn G x y) hu
  have hbk := twoCluster_functional_lintegral_le G p hp x y 𝓔 h𝓔mono h𝓔 hF0 hH0 hFmono hHmono
    hFcont hHcont hFmeas hHmeas
  rw [hadd]
  exact add_le_add hbk le_rfl

/-- **Lemma I.2.1(iii)**, first half: `0 ≤ E[F G] - E F E G`. -/
theorem fkg_functional_lintegral_le' [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (x y : V) (𝓔 : ℕ → Finset E) (h𝓔mono : Monotone 𝓔)
    {F H : Set V → ℝ} (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (t : ℝ), t < H (cluster G ω y) →
      ∃ n, t < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y)) :
    (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
        (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p))
      ≤ ∫⁻ ω, ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p) :=
  fkg_functional_lintegral_le G p x y 𝓔 h𝓔mono hF0 hH0 hFmono hHmono hFcont hHcont
    hFmeas hHmeas

end Companions

end Percolation

end PercLib.CriticalLRP
