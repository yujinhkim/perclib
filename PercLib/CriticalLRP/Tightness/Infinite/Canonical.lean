/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Canonical arbitrary-countable-vertex per-scale bounds

The arbitrary-vertex `MaxMeetsReal` and `MeetsReal` events are identified with the repository's
actual finite-window `clusterMaxVol` and `clusterVolIn`. The finite-ancestor-closure BK estimates
then yield (2.8) and (2.9), at real thresholds, in raw `ℝ≥0∞` measure form. No whole-cluster
finiteness is used.
-/
module

public import PercLib.CriticalLRP.Tightness.Infinite.RealPower
public import PercLib.CriticalLRP.Tightness.CanonicalPower

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

namespace Countable

section CanonicalEvents

variable {V : Type*} [Countable V]

/-- The arbitrary-vertex real maximum-cluster event, in canonical form. -/
theorem maxMeetsReal_id_eq_tail_anyV (W : Finset V) {lam : ℝ} [Nonempty V] (hlam : 1 ≤ lam) :
    MaxMeetsReal (idBondGraph V) W lam =
      {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W} := by
  let : Nonempty (Sym2 V) := ⟨s(Classical.arbitrary V, Classical.arbitrary V)⟩
  rw [maxMeetsReal_eq_ceil_anyV]
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

/-- The arbitrary-vertex real pointed event, in canonical form. -/
theorem meetsReal_id_eq_tail_anyV (W : Finset V) (u : V) {lam : ℝ} [Nonempty V]
    (hlam : 1 ≤ lam) :
    MeetsReal (idBondGraph V) W lam u =
      {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  let : Nonempty (Sym2 V) := ⟨s(Classical.arbitrary V, Classical.arbitrary V)⟩
  rw [meetsReal_eq_ceil_anyV]
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

section CanonicalBounds

variable {V : Type*} [Countable V]

/-- Canonical finite-window `(2.8)` at a real threshold, for an arbitrary countable vertex type. -/
theorem canonicalMax_pow_bound_anyV (W : Finset V) (hW : W.Nonempty)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeLaw p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
      (edgeLaw p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1) + 1) := by
  let : Nonempty V := ⟨hW.choose⟩
  let : Nonempty (Sym2 V) := ⟨s(hW.choose, hW.choose)⟩
  apply ennreal_pow_bound_of_real
  have h3 : 1 ≤ (3 : ℝ) ^ k * lam :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hlam
  have h := maxMeetsReal_pow_bound_anyV (idBondGraph V) W hlam hk p hp
  rw [maxMeetsReal_id_eq_tail_anyV W (lam := 3 ^ k * lam) h3,
    maxMeetsReal_id_eq_tail_anyV W hlam] at h
  exact h

/-- Canonical finite-window `(2.9)` at a real threshold, for an arbitrary countable vertex type. -/
theorem canonicalMeets_pow_bound_anyV (W : Finset V) (hW : W.Nonempty) (u : V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeLaw p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
      (edgeLaw p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1)) *
      edgeLaw p {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  let : Nonempty V := ⟨hW.choose⟩
  let : Nonempty (Sym2 V) := ⟨s(hW.choose, hW.choose)⟩
  apply ennreal_mul_pow_bound_of_real
  have h3 : 1 ≤ (3 : ℝ) ^ k * lam :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hlam
  have h := meetsReal_pow_bound_anyV (idBondGraph V) W u hlam hk p hp
  rw [maxMeetsReal_id_eq_tail_anyV W hlam] at h
  rw [meetsReal_id_eq_tail_anyV W u (lam := 3 ^ k * lam) h3,
    meetsReal_id_eq_tail_anyV W u hlam] at h
  exact h

/-- Canonical `(2.8)` under `edgeMeasure`. -/
theorem canonicalMax_edgeMeasure_pow_bound_anyV (W : Finset V) (hW : W.Nonempty)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeMeasure p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
      (edgeMeasure p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1) + 1) := by
  rw [edgeMeasure_eq_edgeLaw]
  exact canonicalMax_pow_bound_anyV W hW hlam hk p hp

/-- Canonical `(2.9)` under `edgeMeasure`. -/
theorem canonicalMeets_edgeMeasure_pow_bound_anyV (W : Finset V) (hW : W.Nonempty) (u : V)
    {lam : ℝ} {k : ℕ} (hlam : 1 ≤ lam) (hk : 1 ≤ k)
    (p : Sym2 V → unitInterval) (hp : ∀ e, p e < 1) :
    edgeMeasure p {ω | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
      (edgeMeasure p {ω | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1)) *
      edgeMeasure p {ω | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  rw [edgeMeasure_eq_edgeLaw]
  exact canonicalMeets_pow_bound_anyV W hW u hlam hk p hp

end CanonicalBounds

end Countable

end Hutchcroft
