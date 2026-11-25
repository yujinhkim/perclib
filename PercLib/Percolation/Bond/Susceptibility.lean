/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New glue for the D-2 interface, using pinned mathlib's measurable set cardinality,
ENNReal cardinality sum, and Tonelli theorem. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Susceptibility as the sum of connection probabilities

Cluster volume remains ENat-valued, and its expectation and the sum remain
ENNReal-valued. In particular, neither side of the identity is assumed finite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The cluster is a measurable set-valued function on a countable vertex type. -/
theorem measurable_cluster [Countable V] (x : V) :
    Measurable (fun ω : Config V => cluster ω x) := by
  apply Measurable.of_mem
  intro y
  exact (measurableSet_conn x y).mem

/-- The full ENat-valued cluster volume is measurable, including infinite volume. -/
theorem measurable_encard_cluster [Countable V] (x : V) :
    Measurable (fun ω : Config V => (cluster ω x).encard) :=
  measurable_encard.comp (measurable_cluster x)

/-- Cardinality is the sum of connection indicators, including infinite cardinality. -/
theorem encard_cluster_eq_tsum (ω : Config V) (x : V) :
    ((cluster ω x).encard : ℝ≥0∞) =
      ∑' y, (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  rw [← ENNReal.tsum_set_one, tsum_subtype (cluster ω x) (fun _ => (1 : ℝ≥0∞))]
  congr 1

/-- The P-3 target: measurable ENat volume and the infinite-valued identity. -/
def SusceptibilityIdentity (V : Type*) [Countable V] : Prop :=
  (∀ x : V, Measurable (fun ω : Config V => (cluster ω x).encard)) ∧
    ∀ (q : Sym2 V → unitInterval) (x : V), chi q x = ∑' y, tau q x y

/-- Expected cluster volume is the sum of all two-point probabilities. -/
theorem chi_eq_tsum_tau [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    chi q x = ∑' y, tau q x y := by
  simp_rw [chi, encard_cluster_eq_tsum]
  rw [lintegral_tsum (fun y =>
    (measurable_const.indicator (measurableSet_conn x y)).aemeasurable)]
  congr 1
  funext y
  exact lintegral_indicator_one (measurableSet_conn x y)

/-- Both parts of the susceptibility target hold for every countable vertex type. -/
theorem susceptibilityIdentity (V : Type*) [Countable V] : SusceptibilityIdentity V :=
  ⟨measurable_encard_cluster, chi_eq_tsum_tau⟩

-- The empty configuration has one vertex in its cluster; the length-zero term
-- is retained even when no edge is open.
example (x : V) : ((cluster (∅ : Config V) x).encard : ℝ≥0∞) = 1 := by
  simp [cluster_empty]

example (q : Sym2 Unit → unitInterval) : chi q () = 1 := by
  rw [chi_eq_tsum_tau]
  simp [tau_self]

-- A genuinely infinite susceptibility is covered by the same identity.
example : chi (fun _ : Sym2 ℕ => 1) 0 = ∞ := by
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := by
    ext y
    simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]
  simp [chi, law, PercLib.Probability.prodBernoulli_const, hc]

end PercLib.Percolation.Bond
