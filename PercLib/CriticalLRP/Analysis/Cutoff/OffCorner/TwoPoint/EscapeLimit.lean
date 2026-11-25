/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Escape probabilities of the cutoff cluster at a fixed base point tend to zero.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.Temperature
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.Defs

/-!
# The cluster of a base point escapes to infinity with probability zero

For a fixed cutoff radius `r`, a base point `v` and finite cutoff mass at `v`, the cluster of
`v` is almost surely finite, hence almost surely contained in some lattice ball.
Consequently the probability that it meets the complement of a ball of radius `R` tends to
`0` as `R → ∞`.  This is the configuration-space form of the shrinking-escape nullity
already used for the pair mass.

The escape events `escapeAt v R` do not mention the cutoff radius: they are increasing events
in the configuration, so their `cutLaw`-probabilities are monotone in the cutoff radius.
That is what lets the bound be taken uniformly in a right-neighbourhood of a radius.

The only hypothesis is finiteness of the first cutoff moment at `r`, in the form
`M.cutMassAt r v ≠ ⊤`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The escape event is antitone in the radius. -/
theorem escapeAt_antitone {R R' : ℝ} (h : R ≤ R') (v : M.V) :
    M.escapeAt v R' ⊆ M.escapeAt v R := by
  rintro ω ⟨z, hz, hc⟩
  exact ⟨z, fun hmem => hz (PercLib.CriticalLRP.BallAverage.ball_mono M h hmem), hc⟩

/-- The escape event is an increasing event of the configuration. -/
theorem isIncreasing_escapeAt (v : M.V) (R : ℝ) : IsIncreasing (M.escapeAt v R) := by
  rintro ω ω' h ⟨z, hz, hc⟩
  exact ⟨z, hz, connects_mono h hc⟩

/-- The escape event is measurable. -/
theorem measurableSet_escapeAt (v : M.V) (R : ℝ) : MeasurableSet (M.escapeAt v R) := by
  have h : M.escapeAt v R
      = ⋃ z : {z : M.V // z ∉ M.ball R}, {ω : Config M.V | Connects ω v (z : M.V)} := by
    ext ω
    simp only [escapeAt, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨z, hz, hc⟩ => ⟨⟨z, hz⟩, hc⟩, fun ⟨z, hc⟩ => ⟨z, z.2, hc⟩⟩
  rw [h]
  exact MeasurableSet.iUnion fun z => measurableSet_connects v (z : M.V)

/-- **The cluster of a base point is almost surely finite** under the cutoff law, from
finiteness of the first cutoff moment at that point. -/
theorem ae_cluster_finite_at {r : ℝ} (v : M.V) (hfin : M.cutMassAt r v ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), ¬ (PercLib.CriticalLRP.cluster ω v).Infinite := by
  have hmeas : Measurable fun ω : Config M.V => PercLib.CriticalLRP.clusterVol ω v :=
    PercLib.CriticalLRP.measurable_clusterVol v
  have hint : (∫⁻ ω, PercLib.CriticalLRP.clusterVol ω v ∂(M.cutLaw r)) ≠ ⊤ := hfin
  filter_upwards [ae_lt_top hmeas hint] with ω hω
  intro hinf
  exact ne_of_lt hω ((PercLib.CriticalLRP.inInfiniteCluster_iff ω v).mpr hinf)

/-- **The shrinking escape events have empty essential intersection.** -/
theorem measure_iInter_escapeAt {r : ℝ} (v : M.V) (hfin : M.cutMassAt r v ≠ ⊤) :
    (M.cutLaw r) (⋂ n : ℕ, M.escapeAt v (n : ℝ)) = 0 := by
  refine measure_mono_null ?_ (ae_iff.mp (M.ae_cluster_finite_at v hfin))
  intro ω hω hcl
  obtain ⟨N, hN⟩ := M.exists_ball_subset_of_finite (Set.not_infinite.mp hcl)
  obtain ⟨z, hz, hc⟩ := Set.mem_iInter.mp hω N
  exact hz (hN (PercLib.CriticalLRP.mem_cluster_iff.mpr hc))

/-- **Escape probabilities vanish in the limit.** -/
theorem tendsto_escapeAt {r : ℝ} (v : M.V) (hfin : M.cutMassAt r v ≠ ⊤) :
    Tendsto (fun n : ℕ => ((M.cutLaw r) (M.escapeAt v (n : ℝ))).toReal) atTop (𝓝 0) := by
  have hmono : Antitone fun n : ℕ => M.escapeAt v (n : ℝ) := fun a b hab =>
    M.escapeAt_antitone (by exact_mod_cast hab) v
  have hlim : Tendsto (fun n : ℕ => (M.cutLaw r) (M.escapeAt v (n : ℝ))) atTop
      (𝓝 ((M.cutLaw r) (⋂ n : ℕ, M.escapeAt v (n : ℝ)))) :=
    tendsto_measure_iInter_atTop (fun n => (M.measurableSet_escapeAt v _).nullMeasurableSet)
      hmono ⟨0, measure_ne_top _ _⟩
  rw [M.measure_iInter_escapeAt v hfin] at hlim
  exact (ENNReal.tendsto_toReal_iff (x := 0) (fun n => measure_ne_top _ _) (by simp)).mpr hlim

/-- **Escape probabilities at the origin vanish in the limit.** -/
theorem tendsto_escapeConf {r : ℝ} (hfin : M.cutMassAt r 0 ≠ ⊤) :
    Tendsto (fun n : ℕ => ((M.cutLaw r) (M.escapeConf (n : ℝ))).toReal) atTop (𝓝 0) :=
  M.tendsto_escapeAt (0 : M.V) hfin

/-- **Escape probabilities are eventually small**, at any base point. -/
theorem exists_escapeAt_lt {r : ℝ} (v : M.V) (hfin : M.cutMassAt r v ≠ ⊤) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (M.cutLaw r).real (M.escapeAt v (n : ℝ)) < ε := by
  have h := M.tendsto_escapeAt v hfin
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h' := hN n hn
  have hnn : (0 : ℝ) ≤ ((M.cutLaw r) (M.escapeAt v (n : ℝ))).toReal := ENNReal.toReal_nonneg
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h'

end SourceModelData

end PercLib.CriticalLRP.Orchestration
