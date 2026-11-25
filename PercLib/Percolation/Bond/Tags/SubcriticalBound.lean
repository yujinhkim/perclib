/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-56 correspondence wrappers for the subcritical-bound article. All mathematical
inputs are proved in the imported modules; no literature assumptions are added.
-/
module

public import PercLib.Percolation.Bond.Intensity

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal Classical

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- The full row-sum conclusion: the bound at every root and simultaneous finiteness. -/
@[tag "53Z9"]
theorem subcritical_bound_and_finiteness [Countable V] (q : Sym2 V → unitInterval)
    (m : ℝ≥0∞) (hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m) (hm : m < 1) :
    (∀ v, chi q v ≤ (1-m)⁻¹) ∧ (∀ᵐ ω ∂law q, ∀ v, (cluster ω v).Finite) :=
  ⟨chi_le_inv_one_sub_of_rowSum q m hrow hm, ae_all_clusters_finite_of_rowSum q m hrow hm⟩

/-- Simple-path witnesses and their exact distinct-coordinate cylinder probability. -/
@[tag "YFF7"]
theorem simple_path_certificates_and_probability (q : Sym2 V → unitInterval) (x y : V) :
    (∀ ω ∈ conn x y, ∃ p : (⊤ : SimpleGraph V).Path x y,
      (p.1.edges.toFinset : Set (Sym2 V)) ⊆ ω) ∧
    (∀ p : (⊤ : SimpleGraph V).Path x y,
      law q {ω | (p.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} =
        ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) := by
  refine ⟨fun ω hω => Set.mem_iUnion.mp (conn_subset_iUnion_path x y hω), ?_⟩
  intro p
  exact prodBernoulli_subset q p.1.edges.toFinset

/-- The recurrence and the inductive bound are bundled under the same assertion. -/
@[tag "UMQY"]
theorem walk_recurrence_and_geometric_bound (a : V → V → ℝ≥0∞) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, a v w) ≤ m) :
    (∀ n v, walkSum a (n+1) v = ∑' w, a v w * walkSum a n w) ∧
    (∀ n v, walkSum a n v ≤ m^n) :=
  ⟨walkSum_succ a, walkSum_le_pow a m hrow⟩

/-- The full chain from susceptibility through walk weights to the geometric sum. -/
@[tag "F12C"]
theorem susceptibility_walk_geometric_chain [Countable V] (q : Sym2 V → unitInterval)
    (m : ℝ≥0∞) (hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m) (_hm : m < 1) (x : V) :
    chi q x = ∑' y, tau q x y ∧
    chi q x ≤ ∑' n, walkSum
      (offDiagonal (fun v w => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞))) n x ∧
    (∑' n, walkSum
      (offDiagonal (fun v w => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞))) n x) ≤
        ∑' n : ℕ, m^n ∧
    (∑' n : ℕ, m^n) = (1-m)⁻¹ :=
  ⟨chi_eq_tsum_tau q x, chi_le_tsum_walkSum q x,
    ENNReal.tsum_le_tsum (fun n => walkSum_le_pow _ m hrow n x), ENNReal.tsum_geometric m⟩

/-- Finite expected cluster volumes give zero probability of an infinite root cluster
and simultaneous almost-sure finiteness on a countable vertex type. -/
@[tag "012G"]
theorem finite_susceptibility_implies_cluster_finiteness [Countable V]
    (q : Sym2 V → unitInterval) (hchi : ∀ x, chi q x < ⊤) :
    (∀ x, law q {ω | (cluster ω x).Infinite} = 0) ∧
    (∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite) := by
  have hx (x : V) : ∀ᵐ ω ∂law q, (cluster ω x).Finite := by
    have hm : Measurable (fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞)) :=
      (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster x)
    filter_upwards [ae_lt_top hm (hchi x).ne] with ω hω
    exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp hω)
  refine ⟨fun x => ?_, ae_all_iff.mpr hx⟩
  have h := hx x
  rw [ae_iff] at h
  simpa only [Set.not_finite] using h

/-- The intensity row estimate and its subcritical susceptibility consequence. -/
@[tag "E771"]
theorem intensity_row_and_susceptibility_bound [Countable V]
    (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0) :
    (∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (intensityProfile J β s(v,w)) : ℝ≥0∞)) ≤ (β : ℝ≥0∞)*M) ∧
    ((β : ℝ≥0∞)*M < 1 → ∀ v,
      chi (intensityProfile J β) v ≤ (1-(β : ℝ≥0∞)*M)⁻¹) :=
  ⟨intensity_rowSum_le J M hJ β, chi_intensity_le J M hJ β⟩

/-- Both threshold bounds, including the zero-row case and its vanishing off-diagonal rates. -/
@[tag "JZ47"]
theorem critical_intensity_bounds_and_zero_case [Countable V]
    (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) :
    ((M : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J) ∧
    (∀ x, (M : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x) ∧
    (M = 0 → (∀ v w, w ≠ v → J s(v,w) = 0) ∧
      globalCriticalIntensity J = ⊤ ∧ (∀ x, rootCriticalIntensity J x = ⊤)) := by
  refine ⟨inv_le_globalCriticalIntensity J M hJ,
    inv_le_rootCriticalIntensity J M hJ, ?_⟩
  intro hM
  subst M
  have hz : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ 0 := by
    simpa using hJ
  refine ⟨?_, globalCriticalIntensity_eq_top_of_rowSum_zero J hz,
    rootCriticalIntensity_eq_top_of_rowSum_zero J hz⟩
  intro v w hvw
  have hterm : (if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ 0 :=
    (ENNReal.le_tsum w).trans (hz v)
  simpa [hvw] using hterm

-- Nonzero subcritical profile; diagonal coordinates need not be masked in the law.
example : (∀ v : Bool, chi (fun _ => (⟨1/2, by norm_num⟩ : unitInterval)) v ≤
    (1-(1/2 : ℝ≥0∞))⁻¹) ∧
    (∀ᵐ ω ∂law (fun _ : Sym2 Bool => (⟨1/2, by norm_num⟩ : unitInterval)),
      ∀ v, (cluster ω v).Finite) := by
  apply subcritical_bound_and_finiteness _ (1/2) _ (by norm_num)
  have hp : (unitInterval.toNNReal (⟨1/2, by norm_num⟩ : unitInterval) : ℝ≥0∞) = 1/2 := by
    change ((1/2 : ℝ≥0) : ℝ≥0∞) = _
    simp
  intro v
  cases v <;> norm_num [tsum_fintype, hp]

-- The zero-row branch gives infinite thresholds on an infinite vertex type.
example : (globalCriticalIntensity (fun _ : Sym2 ℕ => (0 : ℝ≥0)) = ⊤) ∧
    (∀ x, rootCriticalIntensity (fun _ : Sym2 ℕ => (0 : ℝ≥0)) x = ⊤) :=
  ((critical_intensity_bounds_and_zero_case (fun _ => 0) 0 (by simp)).2.2 rfl).2

end PercLib.Percolation.Bond
