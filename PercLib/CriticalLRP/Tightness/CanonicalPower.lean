/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Canonical finite-window events and the real per-scale bounds

At the identity bond graph the finite-window events of `RealPower` are exactly the tail events of
`Percolation.clusterMaxVol` and `clusterVolIn`. This module proves those deterministic equalities
and then transports the two finite-product real-threshold probability bounds to the canonical
independent-edge law.
-/
module

public import PercLib.CriticalLRP.Tightness.RealPower
public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.Tightness.LemmaI26Averaging

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP PercLib.CriticalLRP.Percolation MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

section CanonicalEvents

variable {V : Type*} [Countable V]

/-- The finite-window cluster volume is a finite filtered cardinality. -/
theorem clusterVolIn_eq_connects_filter (ω : Config V) (u : V) (W : Finset V) :
    clusterVolIn ω u (W : Set V) = ((W.filter (fun y => Connects ω u y)).card : ℝ≥0∞) := by
  classical
  have hset : (cluster ω u) ∩ (W : Set V) = ((W.filter (fun y => Connects ω u y) : Finset V) : Set V) := by
    ext y
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter, mem_cluster_iff]
    tauto
  rw [clusterVolIn, hset, Set.encard_coe_eq_coe_finsetCard]
  push_cast
  rfl

/-- A natural lower bound on the pointed finite-window cluster volume has exactly the connected
window-subset formulation used by `Meets`. -/
theorem le_clusterVolIn_id_iff (ω : Config V) (u : V) (W : Finset V) (n : ℕ) :
    (n : ℝ≥0∞) ≤ clusterVolIn ω u (W : Set V) ↔
      ∃ t : Finset V, t ⊆ W ∧ n ≤ t.card ∧ ∀ y ∈ t, Conn (idBondGraph V) ω u y := by
  rw [clusterVolIn_eq_connects_filter]
  constructor
  · intro h
    refine ⟨W.filter (fun y => Connects ω u y), Finset.filter_subset _ _, ?_, ?_⟩
    · exact_mod_cast h
    · intro y hy
      rw [conn_idBondGraph_iff]
      exact (Finset.mem_filter.mp hy).2
  · rintro ⟨t, htW, hcard, hconn⟩
    have hsub : t ⊆ W.filter (fun y => Connects ω u y) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨htW hy, (conn_idBondGraph_iff ω u y).mp (hconn y hy)⟩
    have hc := Finset.card_le_card hsub
    exact_mod_cast hcard.trans hc

/-- Exact canonical form of the real unpointed event. -/
theorem maxMeetsReal_id_eq_tail {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) {lam : ℝ} [Nonempty V] (hlam : 1 ≤ lam) :
    MaxMeetsReal (idBondGraph V) W lam =
      {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W} := by
  let : Nonempty (Sym2 V) := ⟨s(Classical.arbitrary V, Classical.arbitrary V)⟩
  rw [maxMeetsReal_eq_ceil]
  have hn : 1 ≤ ⌈lam⌉₊ := Nat.ceil_pos.mpr (zero_lt_one.trans_le hlam)
  ext ω
  have hiff : ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W ↔
      (⌈lam⌉₊ : ℝ≥0∞) ≤ Percolation.clusterMaxVol ω W := by
    obtain htop | ⟨n, hn'⟩ := clusterMaxVol_integer ω W
    · simp [htop]
    · rw [hn', ENNReal.ofReal_le_natCast, Nat.cast_le, ← Nat.ceil_le]
  constructor
  · intro h
    apply hiff.mpr
    obtain ⟨t, htW, hcard, u, hconn⟩ := h
    have hpos : 0 < t.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have huv : Connects ω u v := (conn_idBondGraph_iff ω u v).mp (hconn v hv)
    have hcl : cluster ω u = cluster ω v := by
      rw [cluster_eq_iff]
      exact huv
    have hnum : (⌈lam⌉₊ : ℝ≥0∞) ≤ clusterVolIn ω u (W : Set V) :=
      (le_clusterVolIn_id_iff ω u W ⌈lam⌉₊).mpr ⟨t, htW, hcard, hconn⟩
    rw [clusterVolIn, hcl] at hnum
    exact hnum.trans (clusterVolIn_le_clusterMaxVol ω (htW hv))
  · intro h
    obtain ⟨v, hvW, hv⟩ := (le_clusterMaxVol_iff hn W ω).mp (hiff.mp h)
    obtain ⟨t, htW, hcard, hconn⟩ := (le_clusterVolIn_id_iff ω v W ⌈lam⌉₊).mp hv
    exact ⟨t, htW, hcard, v, hconn⟩

/-- Exact canonical form of the real pointed event. -/
theorem meetsReal_id_eq_tail {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (u : V) {lam : ℝ} [Nonempty V] (hlam : 1 ≤ lam) :
    MeetsReal (idBondGraph V) W lam u =
      {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  let : Nonempty (Sym2 V) := ⟨s(Classical.arbitrary V, Classical.arbitrary V)⟩
  rw [meetsReal_eq_ceil]
  ext ω
  have hiff : ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V) ↔
      (⌈lam⌉₊ : ℝ≥0∞) ≤ clusterVolIn ω u (W : Set V) := by
    obtain htop | ⟨n, hn'⟩ := clusterVolIn_integer ω u (W : Set V)
    · simp [htop]
    · rw [hn', ENNReal.ofReal_le_natCast, Nat.cast_le, ← Nat.ceil_le]
  constructor
  · intro h
    apply hiff.mpr
    obtain ⟨t, htW, hcard, hconn⟩ := h
    exact (le_clusterVolIn_id_iff ω u W ⌈lam⌉₊).mpr ⟨t, htW, hcard, hconn⟩
  · intro h
    exact (le_clusterVolIn_id_iff ω u W ⌈lam⌉₊).mp (hiff.mp h)

end CanonicalEvents

section FiniteCanonicalBounds

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- (2.8) at real thresholds for the canonical finite-vertex independent graph, in `Measure.real`
form. -/
theorem canonicalMax_real_pow_bound (W : Finset V) (hW : W.Nonempty)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real {ω | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
      ((edgeLaw p).real {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1) + 1) := by
  let : Nonempty V := ⟨hW.choose⟩
  let : Nonempty (Sym2 V) := ⟨s(hW.choose, hW.choose)⟩
  have h3 : 1 ≤ (3 : ℝ) ^ k * lam := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hlam
  have h := maxMeets_real_pow_bound (idBondGraph V) W hlam hk p hp
  rw [maxMeetsReal_id_eq_tail W (lam := 3 ^ k * lam) h3,
    maxMeetsReal_id_eq_tail W hlam] at h
  exact h

/-- (2.9) at real thresholds for the canonical finite-vertex independent graph, in `Measure.real`
form. -/
theorem canonicalMeets_real_pow_bound (W : Finset V) (hW : W.Nonempty) (u : V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeLaw p).real {ω | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
      ((edgeLaw p).real {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1)) *
      (edgeLaw p).real {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  let : Nonempty V := ⟨hW.choose⟩
  let : Nonempty (Sym2 V) := ⟨s(hW.choose, hW.choose)⟩
  have h3 : 1 ≤ (3 : ℝ) ^ k * lam := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hlam
  have h := meetsReal_pow_bound (idBondGraph V) W u hlam hk p hp
  rw [maxMeetsReal_id_eq_tail W hlam] at h
  rw [meetsReal_id_eq_tail W u (lam := 3 ^ k * lam) h3,
    meetsReal_id_eq_tail W u hlam] at h
  exact h

/-- The same two canonical bounds also apply to `edgeMeasure`, the canonical presentation of the
independent-edge law, by the established `edgeMeasure_eq_edgeLaw` identification. -/
theorem canonicalMax_edgeMeasure_real_pow_bound (W : Finset V) (hW : W.Nonempty)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeMeasure p).real {ω | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
      ((edgeMeasure p).real {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1) + 1) := by
  rw [edgeMeasure_eq_edgeLaw]
  exact canonicalMax_real_pow_bound W hW hlam hk p hp

/-- Pointed `edgeMeasure` form. -/
theorem canonicalMeets_edgeMeasure_real_pow_bound (W : Finset V) (hW : W.Nonempty) (u : V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    (edgeMeasure p).real {ω | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
      ((edgeMeasure p).real {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1)) *
      (edgeMeasure p).real {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  rw [edgeMeasure_eq_edgeLaw]
  exact canonicalMeets_real_pow_bound W hW u hlam hk p hp

/-- Convert a real-valued number power bound on probability masses to the corresponding
    `ℝ≥0∞` inequality. -/
lemma ennreal_pow_bound_of_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} {c : ℕ}
    (h : μ.real A ≤ (μ.real B) ^ c) : μ A ≤ (μ B) ^ c := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ A)
    (ENNReal.pow_ne_top (measure_ne_top μ B))).mp
  simpa only [Measure.real, ENNReal.toReal_pow] using h

/-- Product-form counterpart for the pointed display. -/
lemma ennreal_mul_pow_bound_of_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B C : Set Ω} {c : ℕ}
    (h : μ.real A ≤ (μ.real B) ^ c * μ.real C) : μ A ≤ (μ B) ^ c * μ C := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ A)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (measure_ne_top μ B))
      (measure_ne_top μ C))).mp
  simpa only [Measure.real, ENNReal.toReal_pow, ENNReal.toReal_mul] using h

end FiniteCanonicalBounds

/-! ## Finite canonical bounds in raw `ℝ≥0∞` measure form -/
section FiniteCanonicalENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Canonical finite `(2.8)`, ready to instantiate `Display28`. -/
theorem canonicalMax_pow_bound (W : Finset V) (hW : W.Nonempty)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeLaw p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
      (edgeLaw p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1) + 1) :=
  ennreal_pow_bound_of_real (canonicalMax_real_pow_bound W hW hlam hk p hp)

/-- Canonical finite `(2.9)`, ready to instantiate `Display29`. -/
theorem canonicalMeets_pow_bound (W : Finset V) (hW : W.Nonempty) (u : V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeLaw p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
      (edgeLaw p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1)) *
      edgeLaw p {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} :=
  ennreal_mul_pow_bound_of_real (canonicalMeets_real_pow_bound W hW u hlam hk p hp)

/-- The canonical countable-law presentation of finite `(2.8)` in finite-vertex scope. -/
theorem canonicalMax_edgeMeasure_pow_bound (W : Finset V) (hW : W.Nonempty)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeMeasure p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
      (edgeMeasure p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1) + 1) := by
  rw [edgeMeasure_eq_edgeLaw]
  exact canonicalMax_pow_bound W hW hlam hk p hp

/-- The canonical countable-law presentation of finite `(2.9)` in finite-vertex scope. -/
theorem canonicalMeets_edgeMeasure_pow_bound (W : Finset V) (hW : W.Nonempty) (u : V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeMeasure p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
      (edgeMeasure p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1)) *
      edgeMeasure p {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  rw [edgeMeasure_eq_edgeLaw]
  exact canonicalMeets_pow_bound W hW u hlam hk p hp



end FiniteCanonicalENNReal

end Hutchcroft
