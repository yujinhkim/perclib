/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.CountableProduct.Lattice
public import PercLib.CriticalLRP.Analysis.MassTransport
public import PercLib.CriticalLRP.LatticeGeometry
public import PercLib.CriticalLRP.MomentExpansion

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PercLib.CriticalLRP

variable {d : ℕ}

noncomputable def clusterVolR (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ) : ℝ :=
  ((cluster ω v).ncard : ℝ)

theorem clusterVolR_eq_toReal (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ) :
    clusterVolR ω v = (clusterVol ω v).toReal := by
  unfold clusterVolR clusterVol
  rw [Set.ncard_def]
  by_cases h : (cluster ω v).Finite
  · rw [h.encard_eq_coe_toFinset_card]
    simp
  · rw [Set.encard_eq_top_iff.mpr (by simpa using h)]
    simp

theorem measurable_clusterVolR (v : Fin d → ℤ) :
    Measurable fun ω : Config (Fin d → ℤ) => clusterVolR ω v := by
  have h : (fun ω => clusterVolR ω v) = fun ω => (clusterVol ω v).toReal := by
    funext ω; exact clusterVolR_eq_toReal ω v
  rw [h]
  exact (measurable_clusterVol v).ennreal_toReal

theorem clusterVolR_nonneg (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ) :
    0 ≤ clusterVolR ω v := by
  unfold clusterVolR; positivity

theorem clusterVolR_shiftConfig (a : Fin d → ℤ) (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ) :
    clusterVolR (shiftConfig a ω) (v + a) = clusterVolR ω v := by
  unfold clusterVolR
  rw [cluster_shiftConfig]
  rw [Set.ncard_image_of_injective]
  intro x y hxy
  simpa using hxy

theorem clusterVolR_eq_of_connects {ω : Config (Fin d → ℤ)} {a b : Fin d → ℤ}
    (h : Connects ω a b) : clusterVolR ω a = clusterVolR ω b := by
  unfold clusterVolR
  rw [cluster_eq_iff.mpr h]

theorem connects_shiftConfig_iff (a : Fin d → ℤ) (ω : Config (Fin d → ℤ))
    (x y : Fin d → ℤ) :
    Connects (shiftConfig a ω) (x + a) (y + a) ↔ Connects ω x y := by
  constructor
  · intro h
    have hb : Connects (shiftConfig (-a) (shiftConfig a ω)) ((x + a) + -a) ((y + a) + -a) :=
      connects_shiftConfig (-a) h
    rw [shiftConfig_neg_shift] at hb
    simpa using hb
  · exact connects_shiftConfig a

theorem tsum_mass_transport₃ {G : Type*} [AddCommGroup G] [Countable G]
    (F : G → G → G → ℝ≥0∞)
    (hF : ∀ (a b c t : G), F (a + t) (b + t) (c + t) = F a b c) :
    (∑' b, ∑' c, F 0 b c) = ∑' a, ∑' c, F a 0 c := by
  have h1 : (∑' p : G × G, F 0 p.1 p.2) = ∑' b, ∑' c, F 0 b c :=
    ENNReal.tsum_prod'
  have h2 : (∑' p : G × G, F p.1 0 p.2) = ∑' a, ∑' c, F a 0 c :=
    ENNReal.tsum_prod'
  rw [← h1, ← h2]
  have hstep : ∀ p : G × G, F 0 p.1 p.2 = F (-p.1) 0 (p.2 - p.1) := by
    intro p
    have h := hF (-p.1) 0 (p.2 - p.1) p.1
    simpa using h
  rw [tsum_congr hstep]
  let e : G × G ≃ G × G :=
    { toFun := fun p => (-p.1, p.2 - p.1)
      invFun := fun q => (-q.1, q.2 - q.1)
      left_inv := by
        rintro ⟨b, c⟩
        simp only [Prod.mk.injEq]
        constructor <;> abel
      right_inv := by
        rintro ⟨b, c⟩
        simp only [Prod.mk.injEq]
        constructor <;> abel }
  have he : ∀ p : G × G, (e p).1 = -p.1 ∧ (e p).2 = p.2 - p.1 := fun p => ⟨rfl, rfl⟩
  calc (∑' p : G × G, F (-p.1) 0 (p.2 - p.1))
      = ∑' p : G × G, F (e p).1 0 (e p).2 := by
        refine tsum_congr fun p => ?_
        rw [(he p).1, (he p).2]
    _ = ∑' q : G × G, F q.1 0 q.2 := Equiv.tsum_eq e (fun q => F q.1 0 q.2)

/-- The indicator of a measurable set of configurations, as an `ℝ≥0∞`-valued function. -/
noncomputable def configIndicator (s : Set (Config (Fin d → ℤ))) (ω : Config (Fin d → ℤ)) :
    ℝ≥0∞ :=
  s.indicator (fun _ => 1) ω

theorem measurable_configIndicator {s : Set (Config (Fin d → ℤ))} (hs : MeasurableSet s) :
    Measurable (configIndicator s) :=
  Measurable.indicator measurable_const hs

open PercLib.CriticalLRP.FiniteVolume in
/-- The lattice weight of the proof of Lemma I.4.1,
`1(a↔b) 1(‖c−b‖≤r) 1(b↮c) ((|K_b|+|K_c|)^p − |K_b|^p)`. -/
noncomputable def russoTripleWeight (p : ℕ) (r : ℝ) (ω : Config (Fin d → ℤ))
    (a b c : Fin d → ℤ) : ℝ≥0∞ :=
  configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' a b} ω *
    (if (linfNorm (c - b) : ℝ) ≤ r then 1 else 0) *
    configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' b c} ω *
    ENNReal.ofReal ((clusterVolR ω b + clusterVolR ω c) ^ p - clusterVolR ω b ^ p)

open PercLib.CriticalLRP.FiniteVolume in
theorem measurable_russoTripleWeight (p : ℕ) (r : ℝ) (a b c : Fin d → ℤ) :
    Measurable fun ω : Config (Fin d → ℤ) => russoTripleWeight p r ω a b c := by
  unfold russoTripleWeight
  have h1 : Measurable fun ω : Config (Fin d → ℤ) => configIndicator {ω' | Connects ω' a b} ω :=
    measurable_configIndicator (measurableSet_connects a b)
  have h2 : Measurable fun ω : Config (Fin d → ℤ) =>
      configIndicator {ω' | ¬ Connects ω' b c} ω :=
    measurable_configIndicator (measurableSet_connects b c).compl
  have h3 : Measurable fun ω : Config (Fin d → ℤ) =>
      ENNReal.ofReal ((clusterVolR ω b + clusterVolR ω c) ^ p - clusterVolR ω b ^ p) := by
    apply Measurable.ennreal_ofReal
    exact (((measurable_clusterVolR b).add (measurable_clusterVolR c)).pow_const p).sub
      ((measurable_clusterVolR b).pow_const p)
  exact ((h1.mul measurable_const).mul h2).mul h3

theorem configIndicator_connects_shift (t a b : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' (a + t) (b + t)}
        (shiftConfig t ω)
      = configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' a b} ω := by
  classical
  by_cases h : Connects ω a b
  · have h' : shiftConfig t ω ∈ {ω' : Config (Fin d → ℤ) | Connects ω' (a + t) (b + t)} :=
      (connects_shiftConfig_iff t ω a b).mpr h
    have hmem : ω ∈ {ω' : Config (Fin d → ℤ) | Connects ω' a b} := h
    rw [configIndicator, Set.indicator_of_mem h', configIndicator, Set.indicator_of_mem hmem]
  · have h' : shiftConfig t ω ∉ {ω' : Config (Fin d → ℤ) | Connects ω' (a + t) (b + t)} :=
      fun hh => h ((connects_shiftConfig_iff t ω a b).mp hh)
    have hmem : ω ∉ {ω' : Config (Fin d → ℤ) | Connects ω' a b} := h
    rw [configIndicator, Set.indicator_of_notMem h', configIndicator, Set.indicator_of_notMem hmem]

theorem configIndicator_not_connects_shift (t b c : Fin d → ℤ) (ω : Config (Fin d → ℤ)) :
    configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' (b + t) (c + t)}
        (shiftConfig t ω)
      = configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' b c} ω := by
  classical
  by_cases h : Connects ω b c
  · have h' : shiftConfig t ω ∉ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' (b + t) (c + t)} :=
      fun hh => hh ((connects_shiftConfig_iff t ω b c).mpr h)
    have hmem : ω ∉ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' b c} := by simpa using h
    rw [configIndicator, Set.indicator_of_notMem h', configIndicator, Set.indicator_of_notMem hmem]
  · have h' : shiftConfig t ω ∈ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' (b + t) (c + t)} :=
      fun hh => h ((connects_shiftConfig_iff t ω b c).mp hh)
    have hmem : ω ∈ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' b c} := h
    rw [configIndicator, Set.indicator_of_mem h', configIndicator, Set.indicator_of_mem hmem]

open PercLib.CriticalLRP.FiniteVolume in
theorem russoTripleWeight_shift (p : ℕ) (r : ℝ) (t : Fin d → ℤ)
    (ω : Config (Fin d → ℤ)) (a b c : Fin d → ℤ) :
    russoTripleWeight p r (shiftConfig t ω) (a + t) (b + t) (c + t)
      = russoTripleWeight p r ω a b c := by
  simp only [russoTripleWeight, configIndicator_connects_shift t a b ω,
    configIndicator_not_connects_shift t b c ω, clusterVolR_shiftConfig]
  have hsub : (c + t) - (b + t) = c - b := by abel
  rw [hsub]

/-! ## The paper's integrands -/

open PercLib.CriticalLRP.FiniteVolume in
/-- The integrand of the left-hand side of the Russo formula in the proof of
Lemma I.4.1: `∑_{x∈K} ∑_{y∈B_r(x)} 1(y∉K)((|K|+|K_y|)^p − |K|^p)`. -/
noncomputable def russoLHS (p : ℕ) (r : ℝ) (ω : Config (Fin d → ℤ)) : ℝ≥0∞ :=
  ∑' x, ∑' y,
    configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω *
      (if (linfNorm (y - x) : ℝ) ≤ r then 1 else 0) *
      configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
      ENNReal.ofReal ((clusterVolR ω 0 + clusterVolR ω y) ^ p - clusterVolR ω 0 ^ p)

open PercLib.CriticalLRP.FiniteVolume in
/-- The integrand after the mass-transport step:
`|K| ∑_{y∈B_r} 1(y∉K)((|K|+|K_y|)^p − |K|^p)`. -/
noncomputable def russoRHS (p : ℕ) (r : ℝ) (ω : Config (Fin d → ℤ)) : ℝ≥0∞ :=
  clusterVol ω 0 * ∑' y,
    (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
      configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
      ENNReal.ofReal ((clusterVolR ω 0 + clusterVolR ω y) ^ p - clusterVolR ω 0 ^ p)

open PercLib.CriticalLRP.FiniteVolume in
theorem russoLHS_eq_triple (p : ℕ) (r : ℝ) (ω : Config (Fin d → ℤ)) :
    russoLHS p r ω = ∑' x, ∑' y, russoTripleWeight p r ω 0 x y := by
  refine tsum_congr fun x => ?_
  by_cases hx : Connects ω 0 x
  · have hvol : clusterVolR ω x = clusterVolR ω 0 := clusterVolR_eq_of_connects (connects_symm hx)
    refine tsum_congr fun y => ?_
    have hind : configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' x y} ω
        = configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω := by
      classical
      by_cases h : Connects ω x y
      · have h0y : Connects ω 0 y := hx.trans h
        have hx_not : ω ∉ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' x y} := by simpa using h
        have h0_not : ω ∉ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} := by simpa using h0y
        rw [configIndicator, Set.indicator_of_notMem hx_not,
          configIndicator, Set.indicator_of_notMem h0_not]
      · have h0y : ¬ Connects ω 0 y := fun hh => h (connects_symm hx |>.trans hh)
        have hx_mem : ω ∈ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' x y} := h
        have h0_mem : ω ∈ {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} := h0y
        rw [configIndicator, Set.indicator_of_mem hx_mem,
          configIndicator, Set.indicator_of_mem h0_mem]
    simp only [russoLHS, russoTripleWeight, hvol, hind]
  · have hx0 : configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω = 0 := by
      classical
      rw [configIndicator, Set.indicator_of_notMem (by simpa using hx)]
    simp only [russoLHS, russoTripleWeight]
    rw [hx0]
    simp

theorem tsum_connects_indicator (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ) :
    (∑' a, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' a v} ω) = clusterVol ω v := by
  classical
  rw [clusterVol_eq_tsum]
  refine tsum_congr fun a => ?_
  rw [configIndicator, Set.indicator_apply]
  by_cases h : Connects ω a v
  · have hmem : a ∈ cluster ω v := by rw [mem_cluster_iff]; exact connects_symm h
    have hif : ω ∈ {ω' : Config (Fin d → ℤ) | Connects ω' a v} := h
    rw [ite_eq_left hif, Set.indicator_of_mem hmem]
  · have hmem : a ∉ cluster ω v := by rw [mem_cluster_iff]; exact fun hh => h (connects_symm hh)
    have hif : ω ∉ {ω' : Config (Fin d → ℤ) | Connects ω' a v} := h
    rw [ite_eq_right hif, Set.indicator_of_notMem hmem]

open PercLib.CriticalLRP.FiniteVolume in
theorem russoRHS_eq_triple (p : ℕ) (r : ℝ) (ω : Config (Fin d → ℤ)) :
    russoRHS p r ω = ∑' a, ∑' c, russoTripleWeight p r ω a 0 c := by
  have hfac : ∀ a : Fin d → ℤ, (∑' c, russoTripleWeight p r ω a 0 c)
      = configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' a 0} ω *
        (∑' c, (if (linfNorm c : ℝ) ≤ r then 1 else 0) *
          configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 c} ω *
          ENNReal.ofReal ((clusterVolR ω 0 + clusterVolR ω c) ^ p - clusterVolR ω 0 ^ p)) := by
    intro a
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun c => ?_
    simp only [russoTripleWeight, sub_zero, mul_assoc]
  calc russoRHS p r ω
      = clusterVol ω 0 * ∑' c, (if (linfNorm c : ℝ) ≤ r then 1 else 0) *
          configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 c} ω *
          ENNReal.ofReal ((clusterVolR ω 0 + clusterVolR ω c) ^ p - clusterVolR ω 0 ^ p) := rfl
    _ = (∑' a, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' a 0} ω) *
          ∑' c, (if (linfNorm c : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 c} ω *
            ENNReal.ofReal ((clusterVolR ω 0 + clusterVolR ω c) ^ p - clusterVolR ω 0 ^ p) := by
        rw [tsum_connects_indicator]
    _ = ∑' a, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' a 0} ω *
          (∑' c, (if (linfNorm c : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 c} ω *
            ENNReal.ofReal ((clusterVolR ω 0 + clusterVolR ω c) ^ p - clusterVolR ω 0 ^ p)) := by
        rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' c, russoTripleWeight p r ω a 0 c := by
        exact tsum_congr fun a => (hfac a).symm


/-! ## The mass-transport identity for Lemma I.4.1 -/

namespace MassTransportI41

variable (μ : Measure (Config (Fin d → ℤ)))

open PercLib.CriticalLRP.FiniteVolume in
theorem massTransport_russo (hμ : ∀ t : Fin d → ℤ, μ.map (shiftConfig t) = μ)
    (p : ℕ) (r : ℝ) :
    (∑' b, ∑' c, ∫⁻ ω, russoTripleWeight p r ω 0 b c ∂μ) =
      ∑' a, ∑' c, ∫⁻ ω, russoTripleWeight p r ω a 0 c ∂μ := by
  refine tsum_mass_transport₃ (fun a b c => ∫⁻ ω, russoTripleWeight p r ω a b c ∂μ) ?_
  intro a b c t
  calc ∫⁻ ω, russoTripleWeight p r ω (a + t) (b + t) (c + t) ∂μ
      = ∫⁻ ω, russoTripleWeight p r (shiftConfig (-t) ω) a b c ∂μ := by
        refine lintegral_congr fun ω => ?_
        simpa using (russoTripleWeight_shift p r (-t) ω (a + t) (b + t) (c + t)).symm
    _ = ∫⁻ ω, russoTripleWeight p r ω a b c ∂(μ.map (shiftConfig (-t))) := by
        rw [lintegral_map (measurable_russoTripleWeight p r a b c) (measurable_shiftConfig (-t))]
    _ = ∫⁻ ω, russoTripleWeight p r ω a b c ∂μ := by rw [hμ (-t)]

open PercLib.CriticalLRP.FiniteVolume in
theorem lintegral_russoTriple_tsum (p : ℕ) (r : ℝ) :
    ∫⁻ ω, (∑' b, ∑' c, russoTripleWeight p r ω 0 b c) ∂μ =
      ∑' b, ∑' c, ∫⁻ ω, russoTripleWeight p r ω 0 b c ∂μ := by
  rw [lintegral_tsum]
  · refine tsum_congr fun b => ?_
    rw [lintegral_tsum]
    intro c
    exact (measurable_russoTripleWeight p r 0 b c).aemeasurable
  · intro b
    exact (Measurable.tsum fun c =>
      measurable_russoTripleWeight p r 0 b c).aemeasurable

open PercLib.CriticalLRP.FiniteVolume in
theorem lintegral_russoTriple_tsum' (p : ℕ) (r : ℝ) :
    ∫⁻ ω, (∑' a, ∑' c, russoTripleWeight p r ω a 0 c) ∂μ =
      ∑' a, ∑' c, ∫⁻ ω, russoTripleWeight p r ω a 0 c ∂μ := by
  rw [lintegral_tsum]
  · refine tsum_congr fun a => ?_
    rw [lintegral_tsum]
    intro c
    exact (measurable_russoTripleWeight p r a 0 c).aemeasurable
  · intro a
    exact (Measurable.tsum fun c =>
      measurable_russoTripleWeight p r a 0 c).aemeasurable

/-- **Lemma I.4.1, mass-transport step.** For any translation-invariant law on
configurations of `ℤ^d`, the expectation of the Russo integrand
`∑_{x∈K} ∑_{y∈B_r(x)} 1(y∉K)((|K|+|K_y|)^p − |K|^p)` equals the expectation of
`|K| ∑_{y∈B_r} 1(y∉K)((|K|+|K_y|)^p − |K|^p)`.

This is the `ℝ≥0∞` form; it is unconditional (no summability or finiteness of
moments is assumed, and the truncated subtraction of `ℝ≥0∞` agrees with the
real difference on the event that the clusters are finite). -/
theorem i41_massTransport (hμ : ∀ t : Fin d → ℤ, μ.map (shiftConfig t) = μ)
    (p : ℕ) (r : ℝ) :
    ∫⁻ ω, russoLHS p r ω ∂μ = ∫⁻ ω, russoRHS p r ω ∂μ := by
  calc ∫⁻ ω, russoLHS p r ω ∂μ
      = ∫⁻ ω, (∑' x, ∑' y, russoTripleWeight p r ω 0 x y) ∂μ :=
        lintegral_congr fun ω => russoLHS_eq_triple p r ω
    _ = ∑' x, ∑' y, ∫⁻ ω, russoTripleWeight p r ω 0 x y ∂μ :=
        lintegral_russoTriple_tsum μ p r
    _ = ∑' a, ∑' c, ∫⁻ ω, russoTripleWeight p r ω a 0 c ∂μ :=
        massTransport_russo μ hμ p r
    _ = ∫⁻ ω, (∑' a, ∑' c, russoTripleWeight p r ω a 0 c) ∂μ :=
        (lintegral_russoTriple_tsum' μ p r).symm
    _ = ∫⁻ ω, russoRHS p r ω ∂μ :=
        lintegral_congr fun ω => (russoRHS_eq_triple p r ω).symm

end MassTransportI41


/-! ## The binomial step of Lemma I.4.1 -/

namespace BinomialI41

open PercLib.CriticalLRP.FiniteVolume

/-- On the event that the cluster of `v` is finite, the `ℝ≥0∞` cluster volume is the
`ofReal` of the real cardinality `clusterVolR`. -/
theorem clusterVol_eq_ofReal_clusterVolR {ω : Config (Fin d → ℤ)} {v : Fin d → ℤ}
    (h : clusterVol ω v ≠ ⊤) :
    clusterVol ω v = ENNReal.ofReal (clusterVolR ω v) := by
  rw [clusterVolR_eq_toReal, ENNReal.ofReal_toReal h]

/-- The single-site binomial identity in `ℝ≥0∞` form. -/
theorem ofReal_mul_pow_sub_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    ENNReal.ofReal a * ENNReal.ofReal ((a + b) ^ p - a ^ p)
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ENNReal.ofReal a ^ (ℓ + 1) *
          ENNReal.ofReal b ^ (p - ℓ) := by
  have hdiff : 0 ≤ (a + b) ^ p - a ^ p := by
    have hle : a ^ p ≤ (a + b) ^ p := pow_le_pow_left₀ ha (by linarith) p
    linarith
  rw [← ENNReal.ofReal_mul ha]
  rw [mul_pow_sub_pow_eq_sum_choose]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  · intro ℓ hℓ
    positivity

/-- **The pointwise binomial form of (I.4.1)** on the event that every cluster is
finite. -/
theorem russoRHS_eq_binomial_of_finite {ω : Config (Fin d → ℤ)}
    (h : ∀ v, clusterVol ω v ≠ ⊤) (p : ℕ) (r : ℝ) :
    russoRHS p r ω =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * clusterVol ω 0 ^ (ℓ + 1) *
        ∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
          configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
          clusterVol ω y ^ (p - ℓ) := by
  set V0 : ℝ := clusterVolR ω 0 with hV0
  set A : (Fin d → ℤ) → ℝ≥0∞ := fun y =>
    (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
      configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω with hA
  have h0 : clusterVol ω 0 = ENNReal.ofReal V0 := clusterVol_eq_ofReal_clusterVolR (h 0)
  have hy : ∀ y, clusterVol ω y = ENNReal.ofReal (clusterVolR ω y) := fun y =>
    clusterVol_eq_ofReal_clusterVolR (h y)
  -- Step 1: unfold the definition and rewrite `|K|` on the outside.
  have step1 : russoRHS p r ω =
      ENNReal.ofReal V0 * ∑' y, A y *
        ENNReal.ofReal ((V0 + clusterVolR ω y) ^ p - V0 ^ p) := by
    unfold russoRHS
    rw [h0]
  -- Step 2: pull the outer `|K|` inside the sum.
  have step2 : ENNReal.ofReal V0 * ∑' y, A y *
        ENNReal.ofReal ((V0 + clusterVolR ω y) ^ p - V0 ^ p)
      = ∑' y, A y * (ENNReal.ofReal V0 *
          ENNReal.ofReal ((V0 + clusterVolR ω y) ^ p - V0 ^ p)) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun y => ?_
    ac_rfl
  -- Step 3: apply the binomial identity at each `y`.
  have step3 : ∀ y, A y * (ENNReal.ofReal V0 *
        ENNReal.ofReal ((V0 + clusterVolR ω y) ^ p - V0 ^ p))
      = A y * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ENNReal.ofReal V0 ^ (ℓ + 1) *
          ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ) := by
    intro y
    rw [ofReal_mul_pow_sub_pow V0 (clusterVolR ω y) (clusterVolR_nonneg ω 0)
      (clusterVolR_nonneg ω y) p]
  -- Step 4: distribute and exchange the finite sum with the `tsum`.
  have step4 : (∑' y, A y * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ENNReal.ofReal V0 ^ (ℓ + 1) * ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ))
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ENNReal.ofReal V0 ^ (ℓ + 1) *
          ∑' y, A y * ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ) := by
    have hdist : ∀ y, A y * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ENNReal.ofReal V0 ^ (ℓ + 1) * ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ)
        = ∑ ℓ ∈ Finset.range p, A y * ((p.choose ℓ : ℝ≥0∞) *
            ENNReal.ofReal V0 ^ (ℓ + 1) * ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ)) :=
      fun y => Finset.mul_sum ..
    rw [tsum_congr hdist]
    rw [Summable.tsum_finsetSum (s := Finset.range p)]
    · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun y => ?_
      ac_rfl
    · intro ℓ hℓ
      exact ENNReal.summable
  calc russoRHS p r ω
      = ENNReal.ofReal V0 * ∑' y, A y *
          ENNReal.ofReal ((V0 + clusterVolR ω y) ^ p - V0 ^ p) := step1
    _ = ∑' y, A y * (ENNReal.ofReal V0 *
          ENNReal.ofReal ((V0 + clusterVolR ω y) ^ p - V0 ^ p)) := step2
    _ = ∑' y, A y * ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
          ENNReal.ofReal V0 ^ (ℓ + 1) * ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ) :=
        tsum_congr step3
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * ENNReal.ofReal V0 ^ (ℓ + 1) *
          ∑' y, A y * ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ) := step4
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * clusterVol ω 0 ^ (ℓ + 1) *
          ∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
            clusterVol ω y ^ (p - ℓ) := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        rw [hA]
        have hpow : ENNReal.ofReal V0 ^ (ℓ + 1) = clusterVol ω 0 ^ (ℓ + 1) := by rw [h0]
        have hsum : (∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
              configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
              ENNReal.ofReal (clusterVolR ω y) ^ (p - ℓ))
            = ∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
              configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
              clusterVol ω y ^ (p - ℓ) := by
          refine tsum_congr fun y => ?_
          rw [hy y]
        rw [hpow, hsum]


/-- The `ofReal` increment is the extended-volume increment of the paper. -/
theorem ofReal_pow_sub_pow_eq_vol (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    ENNReal.ofReal ((a + b) ^ p - a ^ p)
      = (ENNReal.ofReal a + ENNReal.ofReal b) ^ p - ENNReal.ofReal a ^ p := by
  have hdiff : 0 ≤ (a + b) ^ p - a ^ p := by
    have hle : a ^ p ≤ (a + b) ^ p := pow_le_pow_left₀ ha (by linarith) p
    linarith
  rw [ENNReal.ofReal_sub ((a + b) ^ p) (by positivity : (0 : ℝ) ≤ a ^ p),
    ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_pow ha, ENNReal.ofReal_add ha hb]

/-- On the event that all clusters are finite, the Russo integrand written with
`ofReal` of the real cluster volume is the paper's `(|K|+|K_y|)^p − |K|^p`
written with the extended cluster volume. -/
theorem russoLHS_eq_clusterVol_form {ω : Config (Fin d → ℤ)}
    (h : ∀ v, clusterVol ω v ≠ ⊤) (p : ℕ) (r : ℝ) :
    russoLHS p r ω =
      ∑' x, ∑' y, configIndicator {ω' : Config (Fin d → ℤ) | Connects ω' 0 x} ω *
        (if (linfNorm (y - x) : ℝ) ≤ r then 1 else 0) *
        configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
        ((clusterVol ω 0 + clusterVol ω y) ^ p - clusterVol ω 0 ^ p) := by
  refine tsum_congr fun x => ?_
  refine tsum_congr fun y => ?_
  rw [show ENNReal.ofReal ((clusterVolR ω 0 + clusterVolR ω y) ^ p - clusterVolR ω 0 ^ p)
      = (clusterVol ω 0 + clusterVol ω y) ^ p - clusterVol ω 0 ^ p from by
    rw [ofReal_pow_sub_pow_eq_vol (clusterVolR ω 0) (clusterVolR ω y)
        (clusterVolR_nonneg ω 0) (clusterVolR_nonneg ω y) p,
      ← clusterVol_eq_ofReal_clusterVolR (h 0), ← clusterVol_eq_ofReal_clusterVolR (h y)]]

end BinomialI41


/-! ## The integrated binomial form (I.4.1) -/

namespace BinomialI41

open PercLib.CriticalLRP.FiniteVolume

variable (μ : Measure (Config (Fin d → ℤ)))

theorem measurable_binomSummand (p : ℕ) (r : ℝ) (ℓ : ℕ) :
    Measurable fun ω : Config (Fin d → ℤ) =>
      (p.choose ℓ : ℝ≥0∞) * clusterVol ω 0 ^ (ℓ + 1) *
        (∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
          configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
          clusterVol ω y ^ (p - ℓ)) := by
  have hterm : ∀ y : Fin d → ℤ, Measurable fun ω : Config (Fin d → ℤ) =>
      (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
        configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
        clusterVol ω y ^ (p - ℓ) := by
    intro y
    exact (measurable_const.mul
      (measurable_configIndicator (measurableSet_connects 0 y).compl)).mul
      ((measurable_clusterVol y).pow_const _)
  have hsum : Measurable fun ω : Config (Fin d → ℤ) =>
      ∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
        configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
        clusterVol ω y ^ (p - ℓ) :=
    Measurable.tsum hterm
  exact (measurable_const.mul ((measurable_clusterVol 0).pow_const _)).mul hsum

/-- **Lemma I.4.1 in binomial form at the level of the countable model**: after the
mass-transport step, the expectation of `|K| ∑_{y∈B_r} 1(y∉K)((|K|+|K_y|)^p − |K|^p)`
is the paper's binomial sum
`∑_{ℓ<p} binom(p,ℓ) E[ |K|^{ℓ+1} ∑_{y∈B_r} 1(y∉K)|K_y|^{p−ℓ} ]`.

The only hypothesis is that clusters are almost surely finite (which holds for the
cut-off model `P_{β,r}` at `β ≤ β_c`, by domination by a subcritical measure and
sharpness); no moment finiteness is assumed, the identity being in `ℝ≥0∞`. -/
theorem i41_binomial (hfin : ∀ v : Fin d → ℤ, μ {ω : Config (Fin d → ℤ) | clusterVol ω v = ⊤} = 0)
    (p : ℕ) (r : ℝ) :
    ∫⁻ ω, russoRHS p r ω ∂μ =
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, clusterVol ω 0 ^ (ℓ + 1) *
          (∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
            clusterVol ω y ^ (p - ℓ)) ∂μ := by
  have hae : ∀ᵐ ω ∂μ, ∀ v : Fin d → ℤ, clusterVol ω v ≠ ⊤ := by
    rw [ae_all_iff]
    intro v
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin v)] with ω h
    exact h
  calc ∫⁻ ω, russoRHS p r ω ∂μ
      = ∫⁻ ω, (∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) * clusterVol ω 0 ^ (ℓ + 1) *
          ∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
            clusterVol ω y ^ (p - ℓ)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ω h
        exact russoRHS_eq_binomial_of_finite h p r
    _ = ∑ ℓ ∈ Finset.range p, ∫⁻ ω, (p.choose ℓ : ℝ≥0∞) * clusterVol ω 0 ^ (ℓ + 1) *
          (∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
            clusterVol ω y ^ (p - ℓ)) ∂μ :=
        lintegral_finsetSum _ (fun ℓ hℓ => measurable_binomSummand p r ℓ)
    _ = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, clusterVol ω 0 ^ (ℓ + 1) *
          (∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
            clusterVol ω y ^ (p - ℓ)) ∂μ := by
        refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        conv_lhs =>
          enter [2, ω]
          rw [mul_assoc]
        rw [lintegral_const_mul]
        exact ((measurable_clusterVol 0).pow_const _).mul
          (Measurable.tsum fun y =>
            (measurable_const.mul
              (measurable_configIndicator (measurableSet_connects 0 y).compl)).mul
              ((measurable_clusterVol y).pow_const _))

end BinomialI41


/-! ## The cut-off kernel on `Sym2 (ℤ^d)` and the instantiation of the identity -/

namespace CutoffKernel

open PercLib.CriticalLRP.FiniteVolume

/-- The cut-off kernel `J_r(x,y) = 1(x ≠ y) ∫_{‖x−y‖}^r |J'|` of Definition I.1.5,
as a function of the unordered pair. -/
noncomputable def cutoffSymKernel (K : ℝ → ℝ) (d : ℕ) (r : ℝ) :
    Sym2 (Fin d → ℤ) → ℝ :=
  Sym2.lift ⟨fun x y => if x = y then 0 else cutoffProfile K r (linfNorm (x - y)), by
    intro x y
    show (if x = y then (0 : ℝ) else cutoffProfile K r (linfNorm (x - y)))
      = (if y = x then 0 else cutoffProfile K r (linfNorm (y - x)))
    by_cases h : x = y
    · subst h
      simp
    · have h' : y ≠ x := fun hh => h hh.symm
      rw [ite_eq_right h, ite_eq_right h']
      rw [show y - x = -(x - y) by abel, linfNorm_neg]⟩

theorem cutoffSymKernel_mk (K : ℝ → ℝ) (d : ℕ) (r : ℝ) (x y : Fin d → ℤ) :
    cutoffSymKernel K d r s(x, y) = if x = y then 0 else cutoffProfile K r (linfNorm (x - y)) :=
  rfl

/-- Nonnegativity of the cut-off kernel for a nonnegative antitone profile. -/
theorem cutoffSymKernel_nonneg {K : ℝ → ℝ} (hK : AntitoneOn K (Set.Ioi 0))
    {d : ℕ} {r : ℝ} (hr : 0 < r) (e : Sym2 (Fin d → ℤ)) :
    0 ≤ cutoffSymKernel K d r e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [cutoffSymKernel_mk]
    by_cases h : x = y
    · simp [h]
    · rw [ite_eq_right h]
      rcases le_or_gt ((linfNorm (x - y) : ℝ)) r with hsr | hsr
      · refine cutoffProfile_nonneg hK ?_ hr hsr
        rw [lt_iff_le_and_ne]
        constructor
        · exact_mod_cast linfNorm_nonneg _
        · intro hz
          have hz' : linfNorm (x - y) = 0 := by exact_mod_cast hz.symm
          exact h (sub_eq_zero.mp (linfNorm_eq_zero_iff.mp hz'))
      · rw [cutoffProfile_of_lt hsr]

/-- Translation invariance of the cut-off kernel. -/
theorem cutoffSymKernel_shift (K : ℝ → ℝ) (d : ℕ) (r : ℝ) (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    cutoffSymKernel K d r (Sym2.map (fun x : Fin d → ℤ => x + a) e)
      = cutoffSymKernel K d r e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk, cutoffSymKernel_mk, cutoffSymKernel_mk]
    by_cases h : x = y
    · subst h
      simp
    · have h' : x + a ≠ y + a := fun hh => h (add_right_cancel hh)
      rw [ite_eq_right h', ite_eq_right h]
      rw [show (x + a) - (y + a) = x - y by abel]

/-- **The mass-transport step of Lemma I.4.1 for the cut-off model `P_{β,r}`**:
for the genuine cut-off kernel on `ℤ^d` and any `β ≥ 0`, `r > 0`, the expectation of
the Russo integrand equals the expectation of `|K| ∑_{y∈B_r} 1(y∉K)((|K|+|K_y|)^p − |K|^p)`.

(No finiteness of moments is assumed: the identity is in `ℝ≥0∞` and the truncated
subtraction agrees with the real difference on the a.s. finite-cluster event.) -/
theorem i41_cutoff_massTransport (K : ℝ → ℝ) (hK : AntitoneOn K (Set.Ioi 0))
    (d : ℕ) (r : ℝ) (hr : 0 < r) (β : NNReal) (p : ℕ) :
    ∫⁻ ω, russoLHS p r ω ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg hK hr) β)
      = ∫⁻ ω, russoRHS p r ω ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg hK hr) β) := by
  refine MassTransportI41.i41_massTransport _ ?_ p r
  intro t
  exact edgeMeasure_shift_invariant (bernoulliEdgeProb (cutoffSymKernel K d r)
      (cutoffSymKernel_nonneg hK hr) β)
    (bernoulliEdgeProb_shift (fun a e => cutoffSymKernel_shift K d r a e)
      (cutoffSymKernel_nonneg hK hr) β) t

/-- **Lemma I.4.1 in binomial form for the cut-off model**, assuming clusters are
almost surely finite (which is the only extra input used by the paper, via sharpness
of the phase transition at `β ≤ β_c`). -/
theorem i41_cutoff_binomial (K : ℝ → ℝ) (hK : AntitoneOn K (Set.Ioi 0))
    (d : ℕ) (r : ℝ) (hr : 0 < r) (β : NNReal) (p : ℕ)
    (hfin : ∀ v : Fin d → ℤ, longRangeMeasure (cutoffSymKernel K d r)
      (cutoffSymKernel_nonneg hK hr) β {ω : Config (Fin d → ℤ) | clusterVol ω v = ⊤} = 0) :
    ∫⁻ ω, russoRHS p r ω ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg hK hr) β)
      = ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ≥0∞) *
        ∫⁻ ω, clusterVol ω 0 ^ (ℓ + 1) *
          (∑' y, (if (linfNorm y : ℝ) ≤ r then 1 else 0) *
            configIndicator {ω' : Config (Fin d → ℤ) | ¬ Connects ω' 0 y} ω *
            clusterVol ω y ^ (p - ℓ)) ∂(longRangeMeasure (cutoffSymKernel K d r)
              (cutoffSymKernel_nonneg hK hr) β) :=
  BinomialI41.i41_binomial _ hfin p r

end CutoffKernel

end PercLib.CriticalLRP
