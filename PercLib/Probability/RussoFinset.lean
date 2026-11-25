/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 145 (Q-19), written on 2026-11-14 by PROVER-E. They transport the
finite-index Russo formula of `PercLib.Probability.Russo` to events on an arbitrary index
type that depend on finitely many coordinates. No upstream proof is copied.
-/
module

public import PercLib.Probability.ProductExpectation
public import PercLib.Probability.Russo

/-!
# Russo's formula for events depending on finitely many coordinates

An event `A ⊆ Set ι` depends only on the coordinates in a finite set `F` when
`ω ∈ A ↔ ω ∩ F ∈ A`. Its probability is then a probability on `Set F`
(`prodBernoulli_real_eq_restrict`), and the finite-index Russo formula applies. For an
increasing such event, in the intensity parametrisation `p_b(e) = 1 - e^{-b J(e)}`:

`d/db P_b(A) = ∑_{e ∈ F} J(e) e^{-b J(e)} P_b(insert e ω ∈ A ∧ ω \ {e} ∉ A)`

as a derivative within any parameter set on which the profile has that form on `F`
(`event_intensity_real_hasDerivWithinAt_of_dependsOn`). This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Probability

variable {ι : Type*}

/-- **Restriction to finitely many coordinates.** The probability of an event depending
only on the coordinates in `F` is a probability for the profile restricted to `F`. -/
theorem prodBernoulli_real_eq_restrict (r : ι → unitInterval) (F : Finset ι)
    {B : Set (Set ι)} (hB : ∀ ω, ω ∈ B ↔ ω ∩ ↑F ∈ B) :
    (prodBernoulli r).real B =
      (prodBernoulli (fun i : F => r i)).real {u : Set F | Subtype.val '' u ∈ B} := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set F)) :=
    Measurable.of_mem fun i => (measurableSet_mem i.val).mem
  rw [← prodBernoulli_map_restrict r F, measureReal_def, measureReal_def,
    Measure.map_apply hm (Set.toFinite _).measurableSet]
  congr 2
  ext ω
  simp only [mem_preimage, mem_ofPred_eq]
  rw [hB ω]
  have : Subtype.val '' (Subtype.val ⁻¹' ω : Set F) = ω ∩ ↑F := by
    ext i
    simp [and_comm]
  rw [this]

/-- The pivotal event of an event depending on `F`, at a coordinate of `F`, also depends
only on `F`. -/
theorem pivotal_dependsOn {F : Finset ι} {A : Set (Set ι)} (hdep : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A)
    {e : ι} (he : e ∈ F) (ω : Set ι) :
    ω ∈ {ω : Set ι | insert e ω ∈ A ∧ ω \ {e} ∉ A} ↔
      ω ∩ ↑F ∈ {ω : Set ι | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  have h1 : insert e ω ∩ ↑F = insert e (ω ∩ ↑F) ∩ ↑F := by
    ext i; by_cases hi : i = e <;> simp [hi, he]
  have h2 : (ω \ {e}) ∩ ↑F = (ω ∩ ↑F) \ {e} ∩ ↑F := by
    ext i; by_cases hi : i = e <;> simp [hi, and_comm]
  simp only [mem_ofPred_eq]
  rw [hdep (insert e ω), hdep (ω \ {e}), hdep (insert e (ω ∩ ↑F)), hdep ((ω ∩ ↑F) \ {e}),
    h1, h2]

/-- **Russo's formula, intensity form, for an increasing event depending on finitely many
coordinates.** The derivative is taken within any parameter set `s` on which the profile
has the intensity form on `F`; outside `F` the profile is arbitrary. -/
theorem event_intensity_real_hasDerivWithinAt_of_dependsOn (J : ι → ℝ) (F : Finset ι)
    (β : ℝ) (p : ℝ → ι → unitInterval) (s : Set ℝ)
    (ht : ∀ e ∈ F, (p β e : ℝ) = 1 - Real.exp (-β * J e))
    (hs : ∀ b ∈ s, ∀ e ∈ F, (p b e : ℝ) = 1 - Real.exp (-b * J e))
    {A : Set (Set ι)} (hA : IsUpperSet A) (hdep : ∀ ω, ω ∈ A ↔ ω ∩ ↑F ∈ A) :
    HasDerivWithinAt (fun b => (prodBernoulli (p b)).real A)
      (∑ e ∈ F, (J e * Real.exp (-β * J e)) *
        (prodBernoulli (p β)).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A}) s β := by
  classical
  set A' : Set (Set F) := {u | Subtype.val '' u ∈ A}
  have hA' : IsUpperSet A' := fun u v huv hu => hA (image_mono huv) hu
  have h := FiniteProfile.event_intensity_real_hasDerivWithinAt (E := F) (fun e => J e) β
    (fun b e => p b e) s (fun e => ht e e.2) (fun b hb e => hs b hb e e.2) hA'
  have hpiv : ∀ e : F, {u : Set F | insert e u ∈ A' ∧ u \ {e} ∉ A'} =
      {u : Set F | Subtype.val '' u ∈ {ω : Set ι | insert (e : ι) ω ∈ A ∧ ω \ {(e : ι)} ∉ A}} := by
    intro e
    ext u
    simp only [A', mem_ofPred_eq, image_insert_eq,
      image_sdiff Subtype.val_injective, image_singleton]
  convert h using 1
  · funext b
    exact prodBernoulli_real_eq_restrict (p b) F hdep
  · rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hpiv e, prodBernoulli_real_eq_restrict (p β) F (pivotal_dependsOn hdep e.2)]

/-! ### Non-vacuity -/

/-- One coordinate `0` of `ℕ`, intensity `J = 1`: the event "`0` is open" has derivative
`e^{-β}` within `[0, ∞)`, as the formula predicts. -/
example (β : ℝ) (hβ : 0 ≤ β) :
    HasDerivWithinAt (fun b => (prodBernoulli (fun _ : ℕ =>
        (⟨1 - Real.exp (-max b 0), by
          constructor
          · simp only [sub_nonneg]; exact Real.exp_le_one_iff.2 (by simp)
          · simp only [sub_le_self_iff]; exact (Real.exp_pos _).le⟩ : unitInterval))).real
        {ω | 0 ∈ ω})
      (∑ e ∈ ({0} : Finset ℕ), ((1 : ℝ) * Real.exp (-β * 1)) *
        (prodBernoulli (fun _ : ℕ => (⟨1 - Real.exp (-max β 0), by
          constructor
          · simp only [sub_nonneg]; exact Real.exp_le_one_iff.2 (by simp)
          · simp only [sub_le_self_iff]; exact (Real.exp_pos _).le⟩ : unitInterval))).real
          {ω | insert e ω ∈ {ω : Set ℕ | 0 ∈ ω} ∧ ω \ {e} ∉ {ω : Set ℕ | 0 ∈ ω}})
      (Ici 0) β := by
  refine event_intensity_real_hasDerivWithinAt_of_dependsOn (fun _ => 1) {0} β _ (Ici 0)
    (fun e _ => by simp [max_eq_left hβ]) (fun b hb e _ => by simp [max_eq_left (mem_Ici.1 hb)])
    (fun _ _ h h0 => h h0) (fun ω => by simp)

end PercLib.Probability
