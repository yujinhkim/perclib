/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The per-site `hrest` and `h2` estimates of Lemma I.5.8 in the canonical model

Source: T. Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1),
Lemma I.2.1 (`lem:BK_disjoint_clusters_covariance`) and the first two displayed
remainder estimates in the proof of Lemma I.5.8 (`lem:gyration_derivative2`,
eq. `eq:x12_derivative`), audited against
`.scratch/i52/source/Zd_renormalizationHD.tex` lines 927-941 and 2806-2825.

What is proved here, on the canonical independent-edge space
`Config V = Set (Sym2 V)` with the genuine product law `edgeMeasure π` (and with
the cluster cardinality `cardFun` taking the value `⊤` on infinite clusters):

* `fkg_functional_ennreal` : Harris--FKG `(∫ F(K_x))(∫ G(K_y)) ≤ ∫ F(K_x)G(K_y)`
  for increasing measurable functionals of the clusters, in `ℝ≥0∞` (no
  integrability hypotheses).
* `twoCluster_ennreal` : the BK inequality
  `∫_{x ↮ y} F(K_x)G(K_y) ≤ (∫ F(K_x))(∫ G(K_y))`.
* `hrest_generic` : the exact mechanism of the paper's first two remainder
  estimates, with the paper's *enlarged* form:
  `(∫F(K_x))(∫G(K_y)) - ∫_{x ↮ y} F(K_x)G(K_y) ≤ ∫_{x ↔ y} F(K_x)G(K_x)`.
  The last step uses `G(K_y) = G(K_x)` on `{x ↔ y}` (`cluster_eq_iff`), which is
  also what makes the paper's `|K|^2 1(y ∈ K)` appear.
* `hrest_cardFun` : the paper's `hrest` itself, `F = G = |K|`.
* `h2_spatFun` : the paper's `h2`, `F = S(K) = ∑_{z ∈ K} q z`, `G = |K|`.
* real-valued corollaries `hrest_cardFun_real`, `h2_spatFun_real`, and the
  lattice/translation-invariant forms with `(E|K|)^2` instead of
  `E|K_x| · E|K_y|` (`hrest_lattice`, `h2_lattice`).

Scope: the four *displayed* estimates of Lemma I.5.8 are conditional in
`VolumeMoments/I58Remainder.lean`; here the first two (`hrest`, `h2`) are
*proved* in the canonical model, unconditionally apart from the standing
hypothesis `π e < 1` (needed for BK) and the fixed edge exhaustion `𝓔`.  The
cross-term estimates `hR3`/`hR4`, the mass-transport identities and the
derivative identity `eq:x12_derivative` are not addressed here.
-/
module

public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.BK.ClusterCardinal
public import PercLib.CriticalLRP.CountableProduct.FKGProduct
public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.BK.FunctionalENNReal
public import PercLib.CriticalLRP.BK.FunctionalFromBelow
public import PercLib.CriticalLRP.BK.InternalWitness
public import PercLib.CriticalLRP.BK.LayerCake

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP
namespace Hrest

variable {V : Type*} [Countable V]

/-! ## 1. Harris--FKG for `ℝ≥0∞`-valued increasing functionals of two clusters

This is the second display of Lemma I.2.1 at the functional level.  The proof
truncates at `n`, applies the layer-cake engine of `BK/LayerCake.lean` (whose
level-set hypothesis is discharged by the *measurable-event* FKG
`edgeMeasure_fkg_measurable_ennreal`, so no finite-witness condition is needed),
and passes to the limit by monotone convergence. -/
theorem fkg_functional_ennreal {π : Sym2 V → unitInterval} {x y : V}
    {F G : Set V → ℝ≥0∞}
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hGmono : ∀ S T : Set V, S ⊆ T → G S ≤ G T)
    (hFmeas : Measurable fun ω : Config V => F (cluster ω x))
    (hGmeas : Measurable fun ω : Config V => G (cluster ω y)) :
    (∫⁻ ω, F (cluster ω x) ∂(edgeMeasure π)) *
        (∫⁻ ω, G (cluster ω y) ∂(edgeMeasure π))
      ≤ ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂(edgeMeasure π) := by
  classical
  -- the truncated inequality, for each truncation level `n`
  have hstep : ∀ n : ℕ,
      (∫⁻ ω, min (F (cluster ω x)) (n : ℝ≥0∞) ∂(edgeMeasure π)) *
          (∫⁻ ω, min (G (cluster ω y)) (n : ℝ≥0∞) ∂(edgeMeasure π))
        ≤ ∫⁻ ω, min (F (cluster ω x)) (n : ℝ≥0∞) *
            min (G (cluster ω y)) (n : ℝ≥0∞) ∂(edgeMeasure π) := by
    intro n
    have hf0 : ∀ ω : Config V, 0 ≤ Percolation.truncFun n F (cluster ω x) :=
      fun ω => Percolation.truncFun_nonneg n F _
    have hg0 : ∀ ω : Config V, 0 ≤ Percolation.truncFun n G (cluster ω y) :=
      fun ω => Percolation.truncFun_nonneg n G _
    have hfm : Measurable fun ω : Config V => Percolation.truncFun n F (cluster ω x) :=
      Percolation.measurable_truncFun hFmeas n
    have hgm : Measurable fun ω : Config V => Percolation.truncFun n G (cluster ω y) :=
      Percolation.measurable_truncFun hGmeas n
    have hlev : ∀ s t : ℝ, 0 < s → 0 < t →
        (edgeMeasure π) {ω : Config V | s < Percolation.truncFun n F (cluster ω x)} *
            (edgeMeasure π) {ω : Config V | t < Percolation.truncFun n G (cluster ω y)}
          ≤ (edgeMeasure π) ({ω : Config V | s < Percolation.truncFun n F (cluster ω x)} ∩
              {ω : Config V | t < Percolation.truncFun n G (cluster ω y)}) := by
      intro s t hs ht
      have hA : {ω : Config V | s < Percolation.truncFun n F (cluster ω x)}
          = {ω : Config V | ENNReal.ofReal s < min (F (cluster ω x)) (n : ℝ≥0∞)} := by
        ext ω
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
          ← Percolation.ofReal_truncFun n F (cluster ω x)]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hs)).symm
      have hB : {ω : Config V | t < Percolation.truncFun n G (cluster ω y)}
          = {ω : Config V | ENNReal.ofReal t < min (G (cluster ω y)) (n : ℝ≥0∞)} := by
        ext ω
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
          ← Percolation.ofReal_truncFun n G (cluster ω y)]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)).symm
      have hmA : MeasurableSet
          {ω : Config V | ENNReal.ofReal s < min (F (cluster ω x)) (n : ℝ≥0∞)} :=
        measurableSet_lt measurable_const (hFmeas.min measurable_const)
      have hmB : MeasurableSet
          {ω : Config V | ENNReal.ofReal t < min (G (cluster ω y)) (n : ℝ≥0∞)} :=
        measurableSet_lt measurable_const (hGmeas.min measurable_const)
      have huA : IsUpperSet
          {ω : Config V | ENNReal.ofReal s < min (F (cluster ω x)) (n : ℝ≥0∞)} := by
        intro a b hab ha
        exact lt_of_lt_of_le ha (min_le_min (hFmono _ _ (cluster_mono (fun e he => hab he) x))
          le_rfl)
      have huB : IsUpperSet
          {ω : Config V | ENNReal.ofReal t < min (G (cluster ω y)) (n : ℝ≥0∞)} := by
        intro a b hab ha
        exact lt_of_lt_of_le ha (min_le_min (hGmono _ _ (cluster_mono (fun e he => hab he) y))
          le_rfl)
      rw [hA, hB]
      exact edgeMeasure_fkg_measurable_ennreal π hmA hmB huA huB
    have h := Percolation.LayerCake.lintegral_mul_ge_of_meas_lt (μ := edgeMeasure π)
      hf0 hg0 hfm hgm hlev
    have hmul : (fun ω : Config V => ENNReal.ofReal
          (Percolation.truncFun n F (cluster ω x) * Percolation.truncFun n G (cluster ω y)))
        = fun ω => ENNReal.ofReal (Percolation.truncFun n F (cluster ω x)) *
            ENNReal.ofReal (Percolation.truncFun n G (cluster ω y)) :=
      funext fun ω => ENNReal.ofReal_mul (Percolation.truncFun_nonneg n F (cluster ω x))
    rw [hmul] at h
    simpa only [Percolation.ofReal_truncFun] using h
  -- monotone convergence in `n`
  have hmono : Monotone fun n : ℕ => fun ω : Config V =>
      min (F (cluster ω x)) (n : ℝ≥0∞) * min (G (cluster ω y)) (n : ℝ≥0∞) := by
    intro m n hmn ω
    exact mul_le_mul' (min_le_min le_rfl (by exact_mod_cast hmn))
      (min_le_min le_rfl (by exact_mod_cast hmn))
  have hmeasn : ∀ n : ℕ, Measurable fun ω : Config V =>
      min (F (cluster ω x)) (n : ℝ≥0∞) * min (G (cluster ω y)) (n : ℝ≥0∞) := fun n =>
    (hFmeas.min measurable_const).mul (hGmeas.min measurable_const)
  have hL : ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂(edgeMeasure π)
      = ⨆ n : ℕ, ∫⁻ ω, min (F (cluster ω x)) (n : ℝ≥0∞) *
          min (G (cluster ω y)) (n : ℝ≥0∞) ∂(edgeMeasure π) := by
    rw [← lintegral_iSup hmeasn hmono]
    congr 1
    funext ω
    conv_lhs =>
      rw [← Percolation.iSup_min_natCast (F (cluster ω x)),
        ← Percolation.iSup_min_natCast (G (cluster ω y)),
        Percolation.iSup_mul_iSup_eq
          (fun n : ℕ => min (F (cluster ω x)) (n : ℝ≥0∞))
          (fun n : ℕ => min (G (cluster ω y)) (n : ℝ≥0∞))
          (fun m n hmn => min_le_min le_rfl (by exact_mod_cast hmn))
          (fun m n hmn => min_le_min le_rfl (by exact_mod_cast hmn))]
  calc (∫⁻ ω, F (cluster ω x) ∂(edgeMeasure π)) *
        (∫⁻ ω, G (cluster ω y) ∂(edgeMeasure π))
      = (⨆ n : ℕ, ∫⁻ ω, min (F (cluster ω x)) (n : ℝ≥0∞) ∂(edgeMeasure π)) *
          (⨆ n : ℕ, ∫⁻ ω, min (G (cluster ω y)) (n : ℝ≥0∞) ∂(edgeMeasure π)) := by
        rw [Percolation.lintegral_eq_iSup_truncFun hFmeas,
          Percolation.lintegral_eq_iSup_truncFun hGmeas]
        simp only [Percolation.ofReal_truncFun]
    _ = ⨆ n : ℕ, (∫⁻ ω, min (F (cluster ω x)) (n : ℝ≥0∞) ∂(edgeMeasure π)) *
          (∫⁻ ω, min (G (cluster ω y)) (n : ℝ≥0∞) ∂(edgeMeasure π)) :=
        (Percolation.iSup_mul_iSup_eq _ _
          (fun m n hmn => lintegral_mono fun ω => min_le_min le_rfl (by exact_mod_cast hmn))
          (fun m n hmn => lintegral_mono fun ω => min_le_min le_rfl (by exact_mod_cast hmn)))
    _ ≤ ⨆ n : ℕ, ∫⁻ ω, min (F (cluster ω x)) (n : ℝ≥0∞) *
          min (G (cluster ω y)) (n : ℝ≥0∞) ∂(edgeMeasure π) := iSup_mono hstep
    _ = ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂(edgeMeasure π) := hL.symm

end Hrest
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Hrest.fkg_functional_ennreal

namespace PercLib.CriticalLRP
namespace Hrest

variable {V : Type*} [Countable V]

/-! ## 2. BK for two clusters, in the canonical model

Direct transport of `Percolation.twoCluster_functional_ennreal` (Lemma I.2.1(i)
for `ℝ≥0∞`-valued functionals) along `edgeMeasure π = edgeLaw π`,
`cluster (idBondGraph V) ω x = cluster ω x` and `Conn (idBondGraph V) ω x y ↔
Connects ω x y`. -/
theorem twoCluster_ennreal {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (x y : V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    {F G : Set V → ℝ≥0∞}
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hGmono : ∀ S T : Set V, S ⊆ T → G S ≤ G T)
    (hFcont : ∀ (ω : Config V) (s : ℝ≥0∞), s < F (cluster ω x) →
      ∃ n, s < F (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x))
    (hGcont : ∀ (ω : Config V) (s : ℝ≥0∞), s < G (cluster ω y) →
      ∃ n, s < G (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) y))
    (hFmeas : Measurable fun ω : Config V => F (cluster ω x))
    (hGmeas : Measurable fun ω : Config V => G (cluster ω y)) :
    ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (F (cluster ω x) * G (cluster ω y)) ∂(edgeMeasure π)
      ≤ (∫⁻ ω, F (cluster ω x) ∂(edgeMeasure π)) *
          (∫⁻ ω, G (cluster ω y) ∂(edgeMeasure π)) := by
  rw [edgeMeasure_eq_edgeLaw]
  have h := Percolation.twoCluster_functional_ennreal (idBondGraph V) π hπ x y
    𝓔 h𝓔mono h𝓔 hFmono hGmono
    (fun ω s hs => by
      rw [cluster_idBondGraph] at hs
      obtain ⟨n, hn⟩ := hFcont ω s hs
      exact ⟨n, by rwa [cluster_idBondGraph]⟩)
    (fun ω s hs => by
      rw [cluster_idBondGraph] at hs
      obtain ⟨n, hn⟩ := hGcont ω s hs
      exact ⟨n, by rwa [cluster_idBondGraph]⟩)
    (by simpa only [cluster_idBondGraph] using hFmeas)
    (by simpa only [cluster_idBondGraph] using hGmeas)
  simpa only [cluster_idBondGraph, conn_idBondGraph_iff] using h

/-! ## 3. Cluster agreement on `{x ↔ y}` and the split of the integral -/

/-- On the connection event the two clusters agree, so `G (K_y) = G (K_x)`. -/
theorem integral_conn_agree {π : Sym2 V → unitInterval} (x y : V)
    (F G : Set V → ℝ≥0∞) :
    ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (F (cluster ω x) * G (cluster ω y)) ∂(edgeMeasure π)
      = ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (F (cluster ω x) * G (cluster ω x)) ∂(edgeMeasure π) := by
  refine lintegral_congr fun ω => ?_
  by_cases h : Connects ω x y
  · have hmem : ω ∈ {ω : Config V | Connects ω x y} := h
    rw [Set.indicator_of_mem hmem, one_mul, one_mul, cluster_eq_iff.mpr h]
  · have hmem : ω ∉ {ω : Config V | Connects ω x y} := h
    rw [Set.indicator_of_notMem hmem, zero_mul, zero_mul]

/-- The decomposition of an expectation into its connection and
disconnection parts (`1 = 1(x ↔ y) + 1(x ↮ y)`), as a restriction integral. -/
theorem integral_split_conn {π : Sym2 V → unitInterval} (x y : V) {H : Config V → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ ω, H ω ∂(edgeMeasure π)
      = ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω * H ω
          ∂(edgeMeasure π)
        + ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω * H ω
          ∂(edgeMeasure π) := by
  classical
  have hm : MeasurableSet {ω : Config V | Connects ω x y} := measurableSet_connects x y
  have hA : ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω * H ω
        ∂(edgeMeasure π)
      = ∫⁻ ω in {ω : Config V | Connects ω x y}, H ω ∂(edgeMeasure π) := by
    rw [← lintegral_indicator hm H]
    refine lintegral_congr fun ω => ?_
    by_cases h : ω ∈ {ω : Config V | Connects ω x y}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  have hBc : ∫⁻ ω, ({ω : Config V | Connects ω x y})ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω * H ω
        ∂(edgeMeasure π)
      = ∫⁻ ω in ({ω : Config V | Connects ω x y})ᶜ, H ω ∂(edgeMeasure π) := by
    rw [← lintegral_indicator hm.compl H]
    refine lintegral_congr fun ω => ?_
    by_cases h : ω ∈ ({ω : Config V | Connects ω x y})ᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  have hB : ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω * H ω
        ∂(edgeMeasure π)
      = ∫⁻ ω, ({ω : Config V | Connects ω x y})ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω * H ω
          ∂(edgeMeasure π) := by
    rw [Set.compl_ofPred]
  rw [hA, hB, hBc, lintegral_add_compl H hm]

/-! ## 4. The `hrest` mechanism at the level of arbitrary increasing functionals

This is the exact content of the first two displayed remainder estimates of the
proof of Lemma I.5.8 (source lines 2806-2825): the BK inequality bounds the
disconnection term by `E F(K_x) E G(K_y)`, Harris--FKG bounds `E F(K_x)G(K_y)`
from below by the same product, and on `{x ↔ y}` the two clusters coincide, so
the connection part is `E F(K_x)G(K_x)`.  Nothing is assumed about the joint law
beyond the canonical independent-edge law; the only probabilistic inputs are
`fkg_functional_ennreal` and `twoCluster_ennreal`, both proved above. -/
theorem hrest_generic {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    {F G : Set V → ℝ≥0∞}
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hGmono : ∀ S T : Set V, S ⊆ T → G S ≤ G T)
    (hFcont : ∀ (ω : Config V) (s : ℝ≥0∞), s < F (cluster ω x) →
      ∃ n, s < F (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x))
    (hGcont : ∀ (ω : Config V) (s : ℝ≥0∞), s < G (cluster ω y) →
      ∃ n, s < G (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) y))
    (hFmeas : Measurable fun ω : Config V => F (cluster ω x))
    (hGmeas : Measurable fun ω : Config V => G (cluster ω y)) :
    (∫⁻ ω, F (cluster ω x) ∂(edgeMeasure π)) *
        (∫⁻ ω, G (cluster ω y) ∂(edgeMeasure π))
      - ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (F (cluster ω x) * G (cluster ω y)) ∂(edgeMeasure π)
      ≤ ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (F (cluster ω x) * G (cluster ω x)) ∂(edgeMeasure π) := by
  have hfkg := fkg_functional_ennreal (π := π) (x := x) (y := y) hFmono hGmono hFmeas hGmeas
  have hsplit := integral_split_conn (π := π) x y (H := fun ω => F (cluster ω x) * G (cluster ω y))
    (hFmeas.mul hGmeas)
  have hagree := integral_conn_agree (π := π) x y F G
  rw [tsub_le_iff_right]
  calc (∫⁻ ω, F (cluster ω x) ∂(edgeMeasure π)) *
        (∫⁻ ω, G (cluster ω y) ∂(edgeMeasure π))
      ≤ ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂(edgeMeasure π) := hfkg
    _ = ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (F (cluster ω x) * G (cluster ω y)) ∂(edgeMeasure π)
        + ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (F (cluster ω x) * G (cluster ω y)) ∂(edgeMeasure π) := hsplit
    _ = ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (F (cluster ω x) * G (cluster ω x)) ∂(edgeMeasure π)
        + ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (F (cluster ω x) * G (cluster ω y)) ∂(edgeMeasure π) := by rw [hagree]

end Hrest
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Hrest.twoCluster_ennreal
#print axioms PercLib.CriticalLRP.Hrest.integral_conn_agree
#print axioms PercLib.CriticalLRP.Hrest.integral_split_conn
#print axioms PercLib.CriticalLRP.Hrest.hrest_generic

namespace PercLib.CriticalLRP
namespace Hrest

variable {V : Type*} [Countable V]

/-! ## 5. `hrest`: the paper's first remainder estimate with `F = G = |K|

Source: the display following `eq:x12_derivative`,
`|(E_r |K|)^2 - E_r [1(y ∉ K) |K| |K_y|]| ≤ E_r [|K|^2 1(y ∈ K)]`
(`Zd_renormalizationHD.tex` lines 2806-2817).

In the canonical model `K = cluster ω x`, `K_y = cluster ω y`,
`1(y ∉ K) = 1(x ↮ y)`, `1(y ∈ K) = 1(x ↔ y)` and `|K|` is `cardFun`, taking the
value `⊤` on infinite clusters (the convention of the paper, where the
inequality remains valid for infinite expectations). -/

/-- Transfer of the continuity-from-below hypothesis for `cardFun`. -/
theorem cardFun_cont_canonical (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (x : V) :
    ∀ (ω : Config V) (s : ℝ≥0∞), s < Percolation.cardFun (cluster ω x) →
      ∃ n, s < Percolation.cardFun (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x) := by
  intro ω s hs
  obtain ⟨n, hn⟩ := Percolation.cardFun_cont 𝓔 h𝓔mono h𝓔 (idBondGraph V) x ω s
    (by simpa only [cluster_idBondGraph] using hs)
  exact ⟨n, by simpa only [cluster_idBondGraph] using hn⟩

theorem measurable_cardFun_cluster_canonical (x : V) :
    Measurable fun ω : Config V => Percolation.cardFun (cluster ω x) := by
  simpa only [cluster_idBondGraph] using
    (Percolation.measurable_cardFun_cluster (idBondGraph V) x)

/-- **The paper's first remainder estimate** (`hrest`), upper bound half:
`(E|K_x|)(E|K_y|) - E[1(x ↮ y)|K_x||K_y|] ≤ E[1(x ↔ y)|K_x|^2]`. -/
theorem hrest_cardFun {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π))
      - ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)
      ≤ ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π) :=
  hrest_generic hπ x y 𝓔 h𝓔mono h𝓔 Percolation.cardFun_mono Percolation.cardFun_mono
    (cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 x) (cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 y)
    (measurable_cardFun_cluster_canonical x) (measurable_cardFun_cluster_canonical y)

/-- **The paper's first remainder estimate**, lower bound half (BK):
`E[1(x ↮ y)|K_x||K_y|] ≤ (E|K_x|)(E|K_y|)`.  Together with `hrest_cardFun` this
is the paper's absolute-value bound. -/
theorem hrest_cardFun_bk {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) :
    ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
        ∂(edgeMeasure π)
      ≤ (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) :=
  twoCluster_ennreal hπ x y 𝓔 h𝓔mono h𝓔 Percolation.cardFun_mono Percolation.cardFun_mono
    (cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 x) (cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 y)
    (measurable_cardFun_cluster_canonical x) (measurable_cardFun_cluster_canonical y)

/-! ## 6. `h2`: the paper's second remainder estimate with the spatial moment
`S(K) = ∑_{z ∈ K} q z` in place of one factor of `|K|

Source: the display following "For the second expectation we have by similar
reasoning" (`Zd_renormalizationHD.tex` lines 2819-2826):
`| |B_r| (E_r|K|)(E_r S(K)) - E_r [S(K) ∑_{y ∈ B_r} 1(y ∉ K)|K_y|] |
 ≤ E_r[|K| |K ∩ B_r| S(K)]`, per site
`|(E|K_x|)(E S(K_x)) - E[1(x ↮ y) S(K_x)|K_y|]| ≤ E[1(x ↔ y) S(K_x)|K_x|]`.
The spatial weights `q z = <z,u>^2` are nonnegative, which is all the mechanism
uses; `S` is `⊤` on clusters of infinite mass, as in the paper. -/

/-- The `ℝ≥0∞`-valued spatial moment `S(K) = ∑_{z ∈ K} q z`. -/
noncomputable def spatFun (q : V → ℝ≥0∞) (S : Set V) : ℝ≥0∞ :=
  ∑' z, q z * S.indicator (fun _ => (1 : ℝ≥0∞)) z

theorem spatFun_mono (q : V → ℝ≥0∞) : Monotone (spatFun q) := by
  intro S T hST
  refine ENNReal.tsum_le_tsum fun z => ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hST hz)]
  · rw [Set.indicator_of_notMem hz]
    simp

theorem measurable_spatFun_cluster (q : V → ℝ≥0∞) (x : V) :
    Measurable fun ω : Config V => spatFun q (cluster ω x) := by
  have hfun : (fun ω : Config V => spatFun q (cluster ω x))
      = fun ω => ∑' z, q z * (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) z := rfl
  rw [hfun]
  refine Measurable.tsum fun z => ?_
  refine measurable_const.mul ?_
  have hind : (fun ω : Config V => (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) z)
      = {ω : Config V | z ∈ cluster ω x}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases h : z ∈ cluster ω x
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by exact h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by simpa using h)]
  rw [hind]
  exact measurable_const.indicator (measurableSet_cluster_mem x z)

/-- The cluster is the union of its restrictions to an exhausting sequence of
finite edge sets (canonical-model form of `Percolation.cluster_eq_iUnion_inter`). -/
theorem cluster_eq_iUnion_inter_canonical (𝓔 : ℕ → Finset (Sym2 V))
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (ω : Config V) (x : V) :
    cluster ω x = ⋃ n, cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x := by
  simp only [← cluster_idBondGraph]
  exact Percolation.cluster_eq_iUnion_inter 𝓔 h𝓔mono h𝓔 (G := idBondGraph V) ω x

theorem spatFun_cont (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (q : V → ℝ≥0∞) (x : V) :
    ∀ (ω : Config V) (s : ℝ≥0∞), s < spatFun q (cluster ω x) →
      ∃ n, s < spatFun q (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x) := by
  classical
  intro ω s hs
  rw [spatFun, ENNReal.tsum_eq_iSup_sum] at hs
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hs
  let f : V → ℕ := fun z => if h : ∃ n, z ∈ cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x
    then Classical.choose h else 0
  have hf : ∀ z, (∃ n, z ∈ cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x) →
      z ∈ cluster (ω ∩ (𝓔 (f z) : Set (Sym2 V))) x := by
    intro z h
    simp only [f, dite_eq_left h]
    exact Classical.choose_spec h
  have hsub : ∀ z ∈ t, z ∈ cluster ω x →
      z ∈ cluster (ω ∩ (𝓔 (t.sup f) : Set (Sym2 V))) x := by
    intro z hz hzK
    have h1 : z ∈ ⋃ n, cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x := by
      rw [← cluster_eq_iUnion_inter_canonical 𝓔 h𝓔mono h𝓔 ω x]
      exact hzK
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h1
    have hz' : z ∈ cluster (ω ∩ (𝓔 (f z) : Set (Sym2 V))) x := hf z ⟨n, hn⟩
    exact cluster_mono (fun e he => Set.inter_subset_inter_right ω
      (Finset.coe_subset.mpr (h𝓔mono (Finset.le_sup (f := f) hz))) he) x hz'
  refine ⟨t.sup f, lt_of_lt_of_le ht ?_⟩
  calc ∑ z ∈ t, q z * (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) z
      ≤ ∑ z ∈ t, q z * (cluster (ω ∩ (𝓔 (t.sup f) : Set (Sym2 V))) x).indicator
          (fun _ => (1 : ℝ≥0∞)) z := by
        refine Finset.sum_le_sum fun z hz => ?_
        refine mul_le_mul_of_nonneg_left ?_ (zero_le)
        by_cases h : z ∈ cluster ω x
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hsub z hz h)]
        · rw [Set.indicator_of_notMem h]
          simp
    _ ≤ ∑' z, q z * (cluster (ω ∩ (𝓔 (t.sup f) : Set (Sym2 V))) x).indicator
          (fun _ => (1 : ℝ≥0∞)) z := ENNReal.sum_le_tsum t
    _ = spatFun q (cluster (ω ∩ (𝓔 (t.sup f) : Set (Sym2 V))) x) := rfl

/-- **The paper's second remainder estimate** (`h2`), upper bound half. -/
theorem h2_spatFun {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (q : V → ℝ≥0∞) :
    (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π))
      - ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y)) ∂(edgeMeasure π)
      ≤ ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π) :=
  hrest_generic hπ x y 𝓔 h𝓔mono h𝓔 (spatFun_mono q) Percolation.cardFun_mono
    (spatFun_cont 𝓔 h𝓔mono h𝓔 q x) (cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 y)
    (measurable_spatFun_cluster q x) (measurable_cardFun_cluster_canonical y)

/-- **The paper's second remainder estimate**, lower bound half (BK). -/
theorem h2_spatFun_bk {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (q : V → ℝ≥0∞) :
    ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y)) ∂(edgeMeasure π)
      ≤ (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)) *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) :=
  twoCluster_ennreal hπ x y 𝓔 h𝓔mono h𝓔 (spatFun_mono q) Percolation.cardFun_mono
    (spatFun_cont 𝓔 h𝓔mono h𝓔 q x) (cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 y)
    (measurable_spatFun_cluster q x) (measurable_cardFun_cluster_canonical y)

end Hrest
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Hrest.hrest_cardFun
#print axioms PercLib.CriticalLRP.Hrest.hrest_cardFun_bk
#print axioms PercLib.CriticalLRP.Hrest.h2_spatFun
#print axioms PercLib.CriticalLRP.Hrest.h2_spatFun_bk

namespace PercLib.CriticalLRP
namespace Hrest

variable {V : Type*} [Countable V]

/-! ## 7. Real-valued forms (the shape of the paper's displayed estimates)

The `ℝ≥0∞` statements above are unconditional; passing to real numbers requires
the three expectations appearing in the estimate to be finite, which under the
paper's hypotheses is what makes `(E|K|)^2` meaningful.  With `a` the product of
the two volume expectations, `b` the disconnection term and `c` the connection
term, `hrest_cardFun` gives `a - b ≤ c` and `hrest_cardFun_bk` gives `b ≤ a`; in
`ℝ` these two are exactly `|a - b| ≤ c`. -/

/-- Real form of the paper's first remainder estimate. -/
theorem hrest_cardFun_real {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hy : (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal *
        (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)).toReal
      - (∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal := by
  set a : ℝ≥0∞ := (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) *
    (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) with ha
  set b : ℝ≥0∞ := ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
    (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
    ∂(edgeMeasure π) with hb
  set c : ℝ≥0∞ := ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
    (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
    ∂(edgeMeasure π) with hcd
  have hba : b ≤ a := hrest_cardFun_bk hπ x y 𝓔 h𝓔mono h𝓔
  have hle : a - b ≤ c := hrest_cardFun hπ x y 𝓔 h𝓔mono h𝓔
  have hane : a ≠ ⊤ := ENNReal.mul_ne_top hx hy
  have h1 : a.toReal - b.toReal ≤ c.toReal := by
    have hcne : c ≠ ⊤ := by rw [hcd]; exact hc
    have h2 : (a - b).toReal ≤ c.toReal := ENNReal.toReal_mono hcne hle
    rwa [ENNReal.toReal_sub_of_le hba hane] at h2
  have h2 : b.toReal ≤ a.toReal := ENNReal.toReal_mono hane hba
  have hae : a.toReal = (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal *
      (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)).toReal := by
    rw [ha, ENNReal.toReal_mul]
  have hbe : b.toReal = (∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator
      (fun _ => (1 : ℝ≥0∞)) ω *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
      ∂(edgeMeasure π)).toReal := by rw [hb]
  have hce : c.toReal = (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
      (fun _ => (1 : ℝ≥0∞)) ω *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)).toReal := by rw [hcd]
  rw [← hae, ← hbe, ← hce, abs_sub_le_iff]
  exact ⟨h1, by linarith⟩

/-- Real form of the paper's second remainder estimate (`h2`). -/
theorem h2_spatFun_real {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (q : V → ℝ≥0∞)
    (hx : (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hy : (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal *
        (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)).toReal
      - (∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal := by
  set a : ℝ≥0∞ := (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)) *
    (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) with ha
  set b : ℝ≥0∞ := ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
    (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y))
    ∂(edgeMeasure π) with hb
  set c : ℝ≥0∞ := ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
    (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
    ∂(edgeMeasure π) with hcd
  have hba : b ≤ a := h2_spatFun_bk hπ x y 𝓔 h𝓔mono h𝓔 q
  have hle : a - b ≤ c := h2_spatFun hπ x y 𝓔 h𝓔mono h𝓔 q
  have hane : a ≠ ⊤ := ENNReal.mul_ne_top hx hy
  have h1 : a.toReal - b.toReal ≤ c.toReal := by
    have hcne : c ≠ ⊤ := by rw [hcd]; exact hc
    have h2 : (a - b).toReal ≤ c.toReal := ENNReal.toReal_mono hcne hle
    rwa [ENNReal.toReal_sub_of_le hba hane] at h2
  have h2 : b.toReal ≤ a.toReal := ENNReal.toReal_mono hane hba
  have hae : a.toReal = (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal *
      (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)).toReal := by
    rw [ha, ENNReal.toReal_mul]
  have hbe : b.toReal = (∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator
      (fun _ => (1 : ℝ≥0∞)) ω *
      (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y))
      ∂(edgeMeasure π)).toReal := by rw [hb]
  have hce : c.toReal = (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
      (fun _ => (1 : ℝ≥0∞)) ω *
      (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)).toReal := by rw [hcd]
  rw [← hae, ← hbe, ← hce, abs_sub_le_iff]
  exact ⟨h1, by linarith⟩

/-! ## 8. The paper's `(E|K|)^2` form

The source writes both factors of the first term as `E_r |K|`, i.e. it uses that
`E|K_y| = E|K_x|`.  In the canonical model on `Z^d` this is translation
invariance of `edgeMeasure π` for a translation-invariant `π` (available in the
repository as `edgeMeasure_shift_invariant`, together with
`cluster_shiftConfig`); here it enters explicitly as the symmetry hypothesis
`hvol`, so that the arithmetic content of the paper's display is separated from
the symmetry. -/

/-- The paper's `hrest` display, with both main-term factors equal to
`E|K_x|` (uses the symmetry `E|K_y| = E|K_x|` as a hypothesis). -/
theorem hrest_site_real {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (hvol : (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π))
      = (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)))
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal ^ 2
      - (∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal := by
  have h := hrest_cardFun_real hπ x y 𝓔 h𝓔mono h𝓔 hx (by rw [hvol]; exact hx) hc
  rw [hvol] at h
  simpa only [sq] using h

/-- The paper's `h2` display, with `E|K|` (uses `E|K_y| = E|K_x|`). -/
theorem h2_site_real {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1) (x y : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (q : V → ℝ≥0∞)
    (hvol : (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π))
      = (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)))
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hq : (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal *
        (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal
      - (∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal := by
  have h := h2_spatFun_real hπ x y 𝓔 h𝓔mono h𝓔 q hq (by rw [hvol]; exact hx) hc
  rw [hvol] at h
  calc |(∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal *
        (∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal - _|
      = |(∫⁻ ω, spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal *
        (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal - _| := by
        rw [mul_comm]
    _ ≤ _ := h

end Hrest
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Hrest.hrest_cardFun_real
#print axioms PercLib.CriticalLRP.Hrest.h2_spatFun_real
#print axioms PercLib.CriticalLRP.Hrest.hrest_site_real
#print axioms PercLib.CriticalLRP.Hrest.h2_site_real
