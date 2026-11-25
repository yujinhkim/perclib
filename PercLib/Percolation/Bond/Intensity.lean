/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for P-6 (issue 40), written on 2026-11-14, from pinned mathlib's real
exponential and ENNReal sums and the P-5 row-sum theorems. No upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.RowSum

/-! # Intensity parametrisation: subcritical bound and thresholds

For a finite nonnegative pair intensity `J` and a finite parameter `β ≥ 0`, the profile
`intensityProfile J β` opens the pair `e` with probability `1 - exp (-β J e)`.

If every off-diagonal row of `J` sums to at most `M`, then:

* `chi_intensity_le`: when `β M < 1`, `chi ≤ (1 - β M)⁻¹` at every vertex;
* `law_exists_infinite_intensity_eq_zero`: when `β M < 1`, almost surely no cluster is
  infinite;
* `inv_le_rootCriticalIntensity` and `inv_le_globalCriticalIntensity`: every threshold
  is at least `M⁻¹`.

The case `M = 0` is covered by the same statements, because `(0 : ℝ≥0∞)⁻¹ = ⊤`; no
division by zero occurs. `rootCriticalIntensity_eq_top_of_rowSum_zero`,
`globalCriticalIntensity_eq_top_of_rowSum_zero` and `chi_intensity_eq_one_of_rowSum_zero`
spell it out. No hypothesis is placed on the diagonal of `J`. Nothing is asserted at
`β M = 1` or above it.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- At parameter zero no pair is open. -/
theorem intensityProfile_zero (J : Sym2 V → ℝ≥0) (e : Sym2 V) :
    intensityProfile J 0 e = 0 := by
  apply Subtype.ext
  change 1 - Real.exp (-((0 : ℝ≥0) : ℝ) * (J e : ℝ)) = 0
  simp

/-- The open probability increases with the parameter. -/
theorem intensityProfile_mono (J : Sym2 V → ℝ≥0) {β β' : ℝ≥0} (h : β ≤ β') (e : Sym2 V) :
    intensityProfile J β e ≤ intensityProfile J β' e := by
  change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) ≤ 1 - Real.exp (-(β' : ℝ) * (J e : ℝ))
  have h1 : (β : ℝ) * (J e : ℝ) ≤ (β' : ℝ) * (J e : ℝ) :=
    mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 h) (J e).coe_nonneg
  have h2 : Real.exp (-(β' : ℝ) * (J e : ℝ)) ≤ Real.exp (-(β : ℝ) * (J e : ℝ)) :=
    Real.exp_le_exp.2 (by linarith)
  linarith

/-- The open probability `1 - exp (-β J e)` is at most `β J e`. -/
theorem intensityProfile_toNNReal_le (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V) :
    unitInterval.toNNReal (intensityProfile J β e) ≤ β * J e := by
  rw [← NNReal.coe_le_coe, NNReal.coe_mul]
  change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) ≤ (β : ℝ) * (J e : ℝ)
  have h := Real.add_one_le_exp (-(β : ℝ) * (J e : ℝ))
  linarith

/-- A row bound `M` on the intensity gives the row bound `β M` on the profile, in the
off-diagonal form used by P-5. -/
theorem intensity_rowSum_le (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0) (v : V) :
    (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (intensityProfile J β s(v,w)) : ℝ≥0∞)) ≤ (β : ℝ≥0∞) * M := by
  calc (∑' w, if w = v then 0 else
        (unitInterval.toNNReal (intensityProfile J β s(v,w)) : ℝ≥0∞))
      ≤ ∑' w, (β : ℝ≥0∞) * (if w = v then 0 else (J s(v,w) : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun w => ?_
        split_ifs
        · simp
        · rw [← ENNReal.coe_mul]
          exact ENNReal.coe_le_coe.2 (intensityProfile_toNNReal_le J β _)
    _ = (β : ℝ≥0∞) * ∑' w, (if w = v then 0 else (J s(v,w) : ℝ≥0∞)) :=
        ENNReal.tsum_mul_left
    _ ≤ (β : ℝ≥0∞) * M := by
        gcongr
        exact hJ v

/-- **Subcritical bound.** If every off-diagonal row of `J` sums to at most `M` and
`β M < 1`, then `chi ≤ (1 - β M)⁻¹` at every vertex. -/
theorem chi_intensity_le [Countable V] (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (x : V) :
    chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) * M)⁻¹ :=
  chi_le_inv_one_sub_of_rowSum _ _ (intensity_rowSum_le J M hJ β) hβ x

/-- Under the same hypotheses the susceptibility is finite. -/
theorem chi_intensity_lt_top [Countable V] (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (x : V) :
    chi (intensityProfile J β) x < ⊤ :=
  chi_lt_top_of_rowSum _ _ (intensity_rowSum_le J M hJ β) hβ x

/-- When `β M < 1`, almost surely no cluster is infinite. -/
theorem law_exists_infinite_intensity_eq_zero [Countable V] (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) :
    law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
  have h := ae_all_clusters_finite_of_rowSum _ _ (intensity_rowSum_le J M hJ β) hβ
  rw [ae_iff] at h
  refine measure_mono_null ?_ h
  rintro ω ⟨x, hx⟩ hall
  exact hx (hall x)

/-- When `β M < 1`, the cluster of a given vertex is almost surely finite. -/
theorem law_cluster_infinite_intensity_eq_zero [Countable V] (J : Sym2 V → ℝ≥0)
    (M : ℝ≥0) (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) (x : V) :
    law (intensityProfile J β) {ω | (cluster ω x).Infinite} = 0 := by
  refine measure_mono_null ?_ (law_exists_infinite_intensity_eq_zero J M hJ β hβ)
  intro ω hω
  exact ⟨x, hω⟩

/-- A parameter at which some cluster is infinite with positive probability is at least
`M⁻¹`. -/
theorem inv_le_of_law_exists_infinite_pos [Countable V] {J : Sym2 V → ℝ≥0} {M : ℝ≥0}
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) {β : ℝ≥0}
    (hpos : 0 < law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite}) :
    (M : ℝ≥0∞)⁻¹ ≤ β := by
  by_contra h
  rw [not_le] at h
  have hβ : (β : ℝ≥0∞) * M < 1 := ENNReal.mul_lt_of_lt_div (by rwa [one_div])
  exact hpos.ne' (law_exists_infinite_intensity_eq_zero J M hJ β hβ)

/-- **Global threshold.** The global threshold is at least `M⁻¹`. -/
theorem inv_le_globalCriticalIntensity [Countable V] (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) :
    (M : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J := by
  unfold globalCriticalIntensity
  refine le_sInf ?_
  rintro b ⟨β, rfl, hpos⟩
  exact inv_le_of_law_exists_infinite_pos hJ hpos

/-- **Root threshold.** The threshold at every root is at least `M⁻¹`. -/
theorem inv_le_rootCriticalIntensity [Countable V] (J : Sym2 V → ℝ≥0) (M : ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ M) (x : V) :
    (M : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x := by
  unfold rootCriticalIntensity
  refine le_sInf ?_
  rintro b ⟨β, rfl, hpos⟩
  exact inv_le_of_law_exists_infinite_pos hJ
    (hpos.trans_le (measure_mono fun _ hω => ⟨x, hω⟩))

/-- **`M = 0`.** With vanishing off-diagonal rows the global threshold is infinite. -/
theorem globalCriticalIntensity_eq_top_of_rowSum_zero [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ 0) :
    globalCriticalIntensity J = ⊤ := by
  have h := inv_le_globalCriticalIntensity J 0 fun v => by
    rw [ENNReal.coe_zero]
    exact hJ v
  rwa [ENNReal.coe_zero, ENNReal.inv_zero, top_le_iff] at h

/-- **`M = 0`.** With vanishing off-diagonal rows every root threshold is infinite. -/
theorem rootCriticalIntensity_eq_top_of_rowSum_zero [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ 0) (x : V) :
    rootCriticalIntensity J x = ⊤ := by
  have h := inv_le_rootCriticalIntensity J 0 (fun v => by
    rw [ENNReal.coe_zero]
    exact hJ v) x
  rwa [ENNReal.coe_zero, ENNReal.inv_zero, top_le_iff] at h

/-- **`M = 0`.** With vanishing off-diagonal rows the susceptibility is one at every
finite parameter and every vertex. -/
theorem chi_intensity_eq_one_of_rowSum_zero [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : ∀ v, (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ 0) (β : ℝ≥0) (x : V) :
    chi (intensityProfile J β) x = 1 := by
  apply le_antisymm _ (one_le_chi _ x)
  have h := chi_intensity_le J 0 (fun v => by
    rw [ENNReal.coe_zero]
    exact hJ v) β (by simp) x
  simpa using h

/-- At parameter zero the susceptibility is one, for every intensity. -/
theorem chi_intensity_zero [Countable V] (J : Sym2 V → ℝ≥0) (x : V) :
    chi (intensityProfile J 0) x = 1 :=
  chi_eq_one_of_offDiagonal_zero _ (fun _ _ _ => intensityProfile_zero J _) x

end PercLib.Percolation.Bond

/-! ### Non-vacuity -/
section Witnesses

open PercLib.Percolation.Bond
open scoped ENNReal NNReal

/-- A nonzero row bound with `β M < 1`: the constant intensity one on `Bool` has
off-diagonal rows equal to one, and at `β = 1/2` the susceptibility is at most two. -/
example : chi (intensityProfile (fun _ : Sym2 Bool => (1 : ℝ≥0)) (1 / 2)) false ≤
    (1 - ((1 / 2 : ℝ≥0) : ℝ≥0∞) * ((1 : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  chi_intensity_le _ 1 (fun v => by cases v <;> simp [tsum_fintype])
    (1 / 2) (by
      rw [ENNReal.coe_one, mul_one]
      exact ENNReal.coe_lt_one_iff.2 (by norm_num)) false

/-- With `M = 1` both thresholds are at least one. -/
example : 1 ≤ globalCriticalIntensity (fun _ : Sym2 Bool => (1 : ℝ≥0)) ∧
    1 ≤ rootCriticalIntensity (fun _ : Sym2 Bool => (1 : ℝ≥0)) false := by
  have h1 := inv_le_globalCriticalIntensity (fun _ : Sym2 Bool => (1 : ℝ≥0)) 1
    (fun v => by cases v <;> simp [tsum_fintype])
  have h2 := inv_le_rootCriticalIntensity (fun _ : Sym2 Bool => (1 : ℝ≥0)) 1
    (fun v => by cases v <;> simp [tsum_fintype]) false
  rw [ENNReal.coe_one, inv_one] at h1 h2
  exact ⟨h1, h2⟩

/-- `M = 0` with a nonzero diagonal on an infinite vertex type: the thresholds are
infinite. -/
example :
    globalCriticalIntensity (fun e : Sym2 ℕ => if e.IsDiag then (1 : ℝ≥0) else 0) = ⊤ ∧
      rootCriticalIntensity (fun e : Sym2 ℕ => if e.IsDiag then (1 : ℝ≥0) else 0) 0 = ⊤ := by
  refine ⟨globalCriticalIntensity_eq_top_of_rowSum_zero _ ?_,
    rootCriticalIntensity_eq_top_of_rowSum_zero _ ?_ 0⟩ <;>
  · intro v
    refine le_of_eq (ENNReal.tsum_eq_zero.2 fun w => ?_)
    by_cases h : w = v
    · simp [h]
    · simp [h, Sym2.mk_isDiag_iff, Ne.symm h]

end Witnesses
