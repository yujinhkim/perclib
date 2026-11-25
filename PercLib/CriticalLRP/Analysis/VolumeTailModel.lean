/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Canonical cutoff-to-full-law tail comparison

Monotone coupling for the percolation/cluster-volume tails used in Proposition
I.3.1. Infinite-cluster configurations are adjoined before comparing increasing
events, since `ENNReal.toReal` is not monotone at `⊤`. Almost-everywhere finiteness
then makes these enlarged events agree nullly with the image tail events.
The same monotonicity transfers full-law finiteness to every cutoff law.
-/

module

public import PercLib.CriticalLRP.Analysis.VolumeLaw
public import PercLib.CriticalLRP.CountableProduct.Marks

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- The real-valued image of a cluster-volume tail event. -/
def tailEvent {n : ℝ} (o : V) : Set (Config V) :=
  {ω | n ≤ (clusterVol ω o).toReal}

/-- Tail event enlarged by infinite clusters. This is increasing even though
`ENNReal.toReal` alone is not monotone at infinity. -/
def tailOrInfinite {n : ℝ} (o : V) : Set (Config V) :=
  {ω | n ≤ (clusterVol ω o).toReal ∨ InInfiniteCluster ω o}

theorem volumeLaw_tail_eq_tailEvent {n : ℝ} (π : Sym2 V → unitInterval) (o : V) :
    volumeLaw π o (Ici n) = edgeMeasure π (tailEvent (n := n) o) := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  rw [volumeLaw, Measure.map_apply hm measurableSet_Ici]
  rfl

theorem measurableSet_tailEvent {n : ℝ} (o : V) :
    MeasurableSet (tailEvent (n := n) o) :=
  measurableSet_le measurable_const (ENNReal.measurable_toReal.comp (measurable_clusterVol o))

theorem measurableSet_tailOrInfinite {n : ℝ} (o : V) :
    MeasurableSet (tailOrInfinite (n := n) o) := by
  have hA := measurableSet_tailEvent (n := n) o
  have hi := measurableSet_inInfiniteCluster o
  exact hA.union hi

theorem isIncreasing_tailOrInfinite {n : ℝ} (o : V) :
    IsIncreasing (tailOrInfinite (n := n) o) := by
  intro ω ω' hsub hmem
  change n ≤ (clusterVol ω' o).toReal ∨ InInfiniteCluster ω' o
  change n ≤ (clusterVol ω o).toReal ∨ InInfiniteCluster ω o at hmem
  rcases hmem with hle | hinf
  · by_cases hfull : InInfiniteCluster ω' o
    · exact Or.inr hfull
    · refine Or.inl (hle.trans ((ENNReal.toReal_le_toReal ?_ hfull).2 (clusterVol_mono hsub o)))
      intro htop
      apply hfull
      change clusterVol ω' o = ⊤
      apply top_unique
      show ⊤ ≤ clusterVol ω' o
      rw [← htop]
      exact clusterVol_mono hsub o
  · refine Or.inr ?_
    change clusterVol ω' o = ⊤
    change clusterVol ω o = ⊤ at hinf
    apply top_unique
    show ⊤ ≤ clusterVol ω' o
    rw [← hinf]
    exact clusterVol_mono hsub o

/-- Full-law domination of real cutoff tails, assuming finite clusters almost
everywhere at both parameters so the enlarged events differ only nullly from
the image tail events. -/
theorem volumeLaw_tail_toReal_mono {π ρ : Sym2 V → unitInterval}
    (hρπ : ∀ e, ρ e ≤ π e) (o : V)
    (hfinρ : ∀ᵐ ω ∂edgeMeasure ρ, clusterVol ω o ≠ ⊤)
    (hfinπ : ∀ᵐ ω ∂edgeMeasure π, clusterVol ω o ≠ ⊤) {n : ℝ} :
    (volumeLaw ρ o (Ici n)).toReal ≤ (volumeLaw π o (Ici n)).toReal := by
  have hmono : edgeMeasure ρ (tailOrInfinite (n := n) o) ≤
      edgeMeasure π (tailOrInfinite (n := n) o) :=
    edgeMeasure_mono_of_le hρπ (measurableSet_tailOrInfinite o) (isIncreasing_tailOrInfinite o)
  have hρ : tailOrInfinite (n := n) o =ᵐ[edgeMeasure ρ] tailEvent (n := n) o := by
    filter_upwards [hfinρ] with ω hω
    by_cases h : n ≤ (clusterVol ω o).toReal
    · simp [tailOrInfinite, tailEvent, h]
    · have hi : ¬ InInfiniteCluster ω o := hω
      simp [tailOrInfinite, tailEvent, h, hi]
  have hπ : tailOrInfinite (n := n) o =ᵐ[edgeMeasure π] tailEvent (n := n) o := by
    filter_upwards [hfinπ] with ω hω
    by_cases h : n ≤ (clusterVol ω o).toReal
    · simp [tailOrInfinite, tailEvent, h]
    · have hi : ¬ InInfiniteCluster ω o := hω
      simp [tailOrInfinite, tailEvent, h, hi]
  rw [measure_congr hρ, measure_congr hπ] at hmono
  rw [volumeLaw_tail_eq_tailEvent, volumeLaw_tail_eq_tailEvent]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmono


/-- Full-law finite clusters force cutoff finite clusters, by monotonicity of the
infinite-cluster event itself. -/
theorem ae_finite_of_volumeLaw_mono {π ρ : Sym2 V → unitInterval}
    (hρπ : ∀ e, ρ e ≤ π e) (o : V)
    (hfinπ : ∀ᵐ ω ∂edgeMeasure π, clusterVol ω o ≠ ⊤) :
    ∀ᵐ ω ∂edgeMeasure ρ, clusterVol ω o ≠ ⊤ := by
  have hnull : edgeMeasure ρ {ω : Config V | InInfiniteCluster ω o} = 0 := by
    apply le_zero_iff.mp
    calc
      edgeMeasure ρ {ω : Config V | InInfiniteCluster ω o} ≤
          edgeMeasure π {ω : Config V | InInfiniteCluster ω o} :=
        edgeMeasure_mono_of_le hρπ (measurableSet_inInfiniteCluster o)
          (isIncreasing_inInfiniteCluster o)
      _ = 0 := by
        change edgeMeasure π {ω : Config V | clusterVol ω o = ⊤} = 0
        simpa only [not_not] using ae_iff.mp hfinπ
  change edgeMeasure ρ {ω : Config V | clusterVol ω o = ⊤} = 0 at hnull
  apply ae_iff.mpr
  simpa only [not_not] using hnull

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.volumeLaw_tail_toReal_mono

#print axioms PercLib.CriticalLRP.ae_finite_of_volumeLaw_mono
