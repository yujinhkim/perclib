/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 117 (Q-1), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.HarrisDecreasing
public import PercLib.Probability.OpenEventHarris

/-!
# Harris for non-connection events and for cluster volumes

Bond corollaries of `PercLib.Probability.HarrisDecreasing` on the D-2 interface: two
non-connection events are positively correlated, a connection and a non-connection event
are negatively correlated, and the cluster volume of `x` is positively correlated with
the connection of `u` and `v`. This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Non-connection events are decreasing. -/
theorem isLowerSet_compl_conn (x y : V) : IsLowerSet (conn x y : Set (Config V))ᶜ :=
  (isUpperSet_conn x y).compl

/-- **Two non-connection events are positively correlated.** -/
theorem law_harris_compl_conn [Countable V] (q : Sym2 V → unitInterval) (x y u v : V) :
    law q (conn x y)ᶜ * law q (conn u v)ᶜ ≤ law q ((conn x y)ᶜ ∩ (conn u v)ᶜ) :=
  prodBernoulli_harris_of_isLowerSet q (isLowerSet_compl_conn x y) (isLowerSet_compl_conn u v)
    (measurableSet_conn x y).compl (measurableSet_conn u v).compl

/-- **A connection and a non-connection event are negatively correlated.** -/
theorem law_conn_inter_compl_le [Countable V] (q : Sym2 V → unitInterval) (x y u v : V) :
    law q (conn x y ∩ (conn u v)ᶜ) ≤ tau q x y * (1 - tau q u v) := by
  have h := prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet q (isUpperSet_conn x y)
    (isLowerSet_compl_conn u v) (measurableSet_conn x y) (measurableSet_conn u v).compl
  rw [prob_compl_eq_one_sub (measurableSet_conn u v)] at h
  exact h

/-- The cluster volume is monotone in the configuration. -/
theorem monotone_encard_cluster (x : V) :
    Monotone fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞) :=
  fun _ _ h => ENat.toENNReal_le.2 (encard_le_encard (cluster_mono h x))

/-- **The cluster volume of `x` and the connection of `u` and `v` are positively
correlated.** -/
theorem chi_mul_tau_le_setLIntegral [Countable V] (q : Sym2 V → unitInterval) (x u v : V) :
    chi q x * tau q u v ≤ ∫⁻ ω in conn u v, ((cluster ω x).encard : ℝ≥0∞) ∂law q := by
  have hg : Monotone ((conn u v).indicator fun _ : Config V => (1 : ℝ≥0∞)) :=
    fun a b h => by
      by_cases ha : a ∈ conn u v
      · simp [ha, isUpperSet_conn u v h ha]
      · simp [ha]
  have h := prodBernoulli_lintegral_mul_le q (monotone_encard_cluster x) hg
    ((measurable_of_countable _).comp (measurable_encard_cluster x))
    (measurable_const.indicator (measurableSet_conn u v))
  rw [lintegral_indicator_const (measurableSet_conn u v), one_mul] at h
  rw [chi, tau, law, ← lintegral_indicator (measurableSet_conn u v)]
  convert h using 2
  funext ω
  by_cases hω : ω ∈ conn u v <;> simp [hω]

/-! Non-vacuity on `Bool` with the single pair open with probability `1/2`. -/

example :
    let q : Sym2 Bool → unitInterval := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
    law q (conn false true ∩ (conn true false)ᶜ) ≤
      tau q false true * (1 - tau q true false) :=
  law_conn_inter_compl_le _ false true true false

example :
    let q : Sym2 Bool → unitInterval := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩
    chi q false * tau q false true ≤
      ∫⁻ ω in conn false true, ((cluster ω false).encard : ℝ≥0∞) ∂law q :=
  chi_mul_tau_le_setLIntegral _ false false true

end PercLib.Percolation.Bond
