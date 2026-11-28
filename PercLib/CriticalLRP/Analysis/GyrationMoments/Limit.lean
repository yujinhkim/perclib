/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwzt36y2`, member `m4`, direction `d10`.

# The exact sup/tsum interchange for the cutoff spatial moments

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.5.1 (Proposition I.5.2, p. 53--54) and Lemma I.5.7 (p. 53).

The paper works with `F_r = E_{β_c,r}[Σ_{x∈K} <x,u>²]` and lets `r → ∞`; the model-level
identity `E_{β_c,r}[Σ_{x∈K} w] = Σ_y w y · P_{β_c,r}(0 ↔ y)` is
`M2.displacementMoment_eq_tsum`, and the uncut quantity is `M2.gyrationMomentUncut`.

`GyrationMoments/Defs.lean` proves the one-sided uniform bound
`gyrationMoment_le_uncut` and explicitly leaves the converse sup/`tsum` interchange open
("The converse limit interchange is not asserted").  This file proves that converse exactly:
for a monotone-in-`r` family of weights against the cutoff two-point function,

  `Σ_y w y · (⨆_r τ_r(0,y)) = ⨆_r Σ_y w y · τ_r(0,y)`,

so `gyrationMomentUncut M = ⨆_r gyrationMoment M r` and every even displacement moment
satisfies the analogous identity.  Consequences:

* `gyrationMoment_tendsto_uncut` — the cutoff gyration numerator converges to the uncut one
  as `r → ∞` (in `ℝ≥0∞`, no finiteness needed);
* `displacementMomentUncut_eq_iSup` and its `Tendsto` form for every `2p`-th displacement
  moment;
* `exists_uniform_bound_iff` — a radius-uniform finite bound on the cutoff numerators is
  equivalent to finiteness of the uncut numerator, which is the exact form in which
  Proposition I.5.2's `ξ₂²` uses the uncut spatial moment;
* the `ℝ`-valued `toReal` limits under the explicit finiteness hypothesis.

Nothing here proves Lemma I.5.7 (the gyration ODE), any two-point asymptotic, or any part
of Proposition I.5.2 beyond this limit interchange.
-/
module

public import PercLib.CriticalLRP.Analysis.GyrationMoments.Defs

/-! # Sup/tsum interchange for the gyration numerators -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.M2

/-! ## §1 The abstract interchange

The only order-theoretic input is monotonicity in the radius: for a finite index set a
sum of suprema is at most the supremum of the sums, because one common radius dominates
finitely many.  No measurability or integrability is used anywhere. -/

/-- For two monotone `ℝ≥0∞`-families the sum of the suprema is the supremum of the sums. -/
theorem add_iSup_of_monotone {A B : ℝ → ℝ≥0∞} (hA : Monotone A) (hB : Monotone B) :
    (⨆ r, A r) + (⨆ r, B r) = ⨆ r, A r + B r :=
  ENNReal.iSup_add_iSup_of_monotone hA hB

/-- A finite sum of suprema of a monotone family is at most the supremum of the finite sums. -/
theorem finset_sum_iSup_le_iSup_sum {β : Type*} (F : ℝ → β → ℝ≥0∞)
    (hF : ∀ r r', r ≤ r' → ∀ b, F r b ≤ F r' b) :
    ∀ s : Finset β, (∑ b ∈ s, ⨆ r, F r b) ≤ ⨆ r, ∑ b ∈ s, F r b := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      refine (add_le_add le_rfl ih).trans ?_
      exact le_of_eq (add_iSup_of_monotone (fun r r' h => hF r r' h a)
        (fun r r' h => Finset.sum_le_sum fun b _ => hF r r' h b))

/-- **The sup/`tsum` interchange for a monotone family against a fixed weight.** -/
theorem tsum_mul_iSup_eq_iSup_tsum {ι : Type*} [Countable ι] (w : ι → ℝ≥0∞)
    (F : ℝ → ι → ℝ≥0∞) (hF : ∀ r r', r ≤ r' → ∀ i, F r i ≤ F r' i) :
    (∑' i, w i * ⨆ r, F r i) = ⨆ r, ∑' i, w i * F r i := by
  refine le_antisymm ?_ (iSup_le fun r =>
    ENNReal.tsum_le_tsum fun i => mul_le_mul_right (le_iSup (fun r => F r i) r) (w i))
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  simp only [ENNReal.mul_iSup]
  refine (finset_sum_iSup_le_iSup_sum (fun r i => w i * F r i)
    (fun r r' h i => mul_le_mul_right (hF r r' h i) (w i)) s).trans ?_
  exact iSup_le fun r => (ENNReal.sum_le_tsum s).trans (le_iSup (fun r => ∑' i, w i * F r i) r)

/-! ## §2 The model: cutoff two-point functions increase to the uncut one -/

/-- The uncut critical two-point function is the supremum of the cutoff ones. -/
theorem uncutTwoPointE_eq_iSup (M : SourceModelData) (y : M.V) :
    uncutTwoPointE M y = ⨆ r : ℝ, cutTwoPointE M r y :=
  (M.iSup_connects_eq (0 : M.V) y).symm

/-- **The exact sup/`tsum` interchange for the gyration numerator.** -/
theorem gyrationMomentUncut_eq_iSup (M : SourceModelData) :
    gyrationMomentUncut M = ⨆ r : ℝ, gyrationMoment M r := by
  have h : ∀ r : ℝ, gyrationMoment M r
      = ∑' y : M.V, ENNReal.ofReal (dot (toVec y) (toVec y)) * cutTwoPointE M r y :=
    fun r => gyrationMoment_eq_tsum M r
  simp only [gyrationMomentUncut, h, uncutTwoPointE_eq_iSup]
  exact tsum_mul_iSup_eq_iSup_tsum _ _ (fun r r' hr i => cutTwoPointE_mono M hr i)

/-- **The cutoff gyration numerator converges to the uncut critical one** as `r → ∞`.
No finiteness is assumed: both sides may be `⊤`. -/
theorem gyrationMoment_tendsto_uncut (M : SourceModelData) :
    Tendsto (fun r : ℝ => gyrationMoment M r) atTop (𝓝 (gyrationMomentUncut M)) := by
  rw [gyrationMomentUncut_eq_iSup]
  exact tendsto_atTop_iSup fun r r' h => gyrationMoment_mono M h

/-- The `ℝ`-valued form: if the uncut gyration numerator is finite then the real-valued
cutoff numerators converge to its real value. -/
theorem tendsto_toReal_gyrationMoment_uncut (M : SourceModelData)
    (h : gyrationMomentUncut M ≠ ⊤) :
    Tendsto (fun r : ℝ => (gyrationMoment M r).toReal) atTop
      (𝓝 (gyrationMomentUncut M).toReal) :=
  (ENNReal.tendsto_toReal h).comp (gyrationMoment_tendsto_uncut M)

/-! ## §3 The same for every even displacement moment -/

/-- The `2p`-th displacement moment is nondecreasing in the cutoff radius. -/
theorem displacementMoment_mono (M : SourceModelData) (p : ℕ) (u : Fin M.d → ℝ)
    {r r' : ℝ} (h : r ≤ r') :
    displacementMoment M p r u ≤ displacementMoment M p r' u := by
  rw [displacementMoment_eq_tsum M p r u, displacementMoment_eq_tsum M p r' u]
  exact ENNReal.tsum_le_tsum fun y => mul_le_mul_right (cutTwoPointE_mono M h y) _

/-- The uncut `2p`-th displacement moment `E_{β_c}[Σ_{x∈K} <x,u>^{2p}]`, as the weighted
two-point sum against the uncut critical two-point function. -/
noncomputable def displacementMomentUncut (M : SourceModelData) (p : ℕ)
    (u : Fin M.d → ℝ) : ℝ≥0∞ :=
  ∑' y : M.V, ENNReal.ofReal ((dot (toVec y) u) ^ (2 * p)) * uncutTwoPointE M y

/-- **The exact sup/`tsum` interchange for each even displacement moment.** -/
theorem displacementMomentUncut_eq_iSup (M : SourceModelData) (p : ℕ) (u : Fin M.d → ℝ) :
    displacementMomentUncut M p u = ⨆ r : ℝ, displacementMoment M p r u := by
  have h : ∀ r : ℝ, displacementMoment M p r u
      = ∑' y : M.V, ENNReal.ofReal ((dot (toVec y) u) ^ (2 * p)) * cutTwoPointE M r y :=
    fun r => displacementMoment_eq_tsum M p r u
  simp only [displacementMomentUncut, h, uncutTwoPointE_eq_iSup]
  exact tsum_mul_iSup_eq_iSup_tsum _ _ (fun r r' hr i => cutTwoPointE_mono M hr i)

/-- The cutoff displacement moment converges to its uncut value. -/
theorem displacementMoment_tendsto_uncut (M : SourceModelData) (p : ℕ)
    (u : Fin M.d → ℝ) :
    Tendsto (fun r : ℝ => displacementMoment M p r u) atTop
      (𝓝 (displacementMomentUncut M p u)) := by
  rw [displacementMomentUncut_eq_iSup]
  exact tendsto_atTop_iSup fun r r' h => displacementMoment_mono M p u h

/-- The `ℝ`-valued form of the displacement-moment limit. -/
theorem tendsto_toReal_displacementMoment_uncut (M : SourceModelData) (p : ℕ)
    (u : Fin M.d → ℝ) (h : displacementMomentUncut M p u ≠ ⊤) :
    Tendsto (fun r : ℝ => (displacementMoment M p r u).toReal) atTop
      (𝓝 (displacementMomentUncut M p u).toReal) :=
  (ENNReal.tendsto_toReal h).comp (displacementMoment_tendsto_uncut M p u)

/-! ## §4 A radius-uniform bound is exactly finiteness of the uncut numerator -/

/-- **Uniform-in-radius control is exact.**  A finite bound on the cutoff gyration
numerators, uniform in the cutoff radius, exists if and only if the uncut critical gyration
numerator is finite.  This is the converse of `gyrationMoment_le_uncut`; it is *not* an
inference from a per-radius bound. -/
theorem exists_uniform_gyration_bound_iff (M : SourceModelData) :
    (∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ r : ℝ, gyrationMoment M r ≤ K) ↔
      gyrationMomentUncut M ≠ ⊤ := by
  constructor
  · rintro ⟨K, hK, hb⟩
    rw [gyrationMomentUncut_eq_iSup]
    exact ne_top_of_le_ne_top hK (iSup_le hb)
  · intro h
    exact ⟨gyrationMomentUncut M, h, fun r => gyrationMoment_le_uncut M r⟩

/-- The displacement-moment form of `exists_uniform_gyration_bound_iff`. -/
theorem exists_uniform_displacement_bound_iff (M : SourceModelData) (p : ℕ)
    (u : Fin M.d → ℝ) :
    (∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ r : ℝ, displacementMoment M p r u ≤ K) ↔
      displacementMomentUncut M p u ≠ ⊤ := by
  constructor
  · rintro ⟨K, hK, hb⟩
    rw [displacementMomentUncut_eq_iSup]
    exact ne_top_of_le_ne_top hK (iSup_le hb)
  · intro h
    exact ⟨displacementMomentUncut M p u, h, fun r => by
      rw [displacementMomentUncut_eq_iSup]
      exact le_iSup (fun r => displacementMoment M p r u) r⟩

end PercLib.CriticalLRP.Orchestration.M2

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.M2.add_iSup_of_monotone
#print axioms PercLib.CriticalLRP.Orchestration.M2.finset_sum_iSup_le_iSup_sum
#print axioms PercLib.CriticalLRP.Orchestration.M2.tsum_mul_iSup_eq_iSup_tsum
#print axioms PercLib.CriticalLRP.Orchestration.M2.uncutTwoPointE_eq_iSup
#print axioms PercLib.CriticalLRP.Orchestration.M2.gyrationMomentUncut_eq_iSup
#print axioms PercLib.CriticalLRP.Orchestration.M2.gyrationMoment_tendsto_uncut
#print axioms PercLib.CriticalLRP.Orchestration.M2.tendsto_toReal_gyrationMoment_uncut
#print axioms PercLib.CriticalLRP.Orchestration.M2.displacementMoment_mono
#print axioms PercLib.CriticalLRP.Orchestration.M2.displacementMomentUncut_eq_iSup
#print axioms PercLib.CriticalLRP.Orchestration.M2.displacementMoment_tendsto_uncut
#print axioms PercLib.CriticalLRP.Orchestration.M2.tendsto_toReal_displacementMoment_uncut
#print axioms PercLib.CriticalLRP.Orchestration.M2.exists_uniform_gyration_bound_iff
#print axioms PercLib.CriticalLRP.Orchestration.M2.exists_uniform_displacement_bound_iff
