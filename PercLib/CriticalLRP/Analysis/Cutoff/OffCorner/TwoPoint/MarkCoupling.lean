/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Quantitative mark-space coupling bound for the long-range law.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Marks

/-!
# Finite-range variation bound for the long-range law

The long-range law `edgeMeasure q` is the law of the thresholded independent marks
`atParameter q` under `markMeasure V` (`markMeasure_map_atParameter`).  Two profiles `p` and
`q` that differ only on a finite set `D` therefore produce configurations that differ only
on the event that some mark `u e` with `e ∈ D` lies in the interval between the two
thresholds.  That event has probability at most the `ℓ¹` distance of the profiles on `D`,
so *every* measurable event has probabilities that differ by at most that quantity.

This is the quantitative form of `edgeMeasure_mono_of_le`: the monotone coupling of the
paper is replaced by an explicit bound, with no monotonicity hypothesis on the event and no
uniformity in the volume.  The bound is stated for finite `D` only; in infinite volume the
`ℓ¹` distance of two cutoff kernels is infinite, which is why any continuity argument for
the two-point function has to localise to a fixed box first.

No moment finiteness and no differentiability is used here.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- The uniform measure of a half-open interval inside `[0,1]`. -/
theorem unif_Ico {a b : ℝ} (h0 : 0 ≤ a) (h1 : b ≤ 1) :
    unif (Set.Ico a b) = ENNReal.ofReal (b - a) := by
  rw [unif, Measure.restrict_apply measurableSet_Ico]
  have hI : Set.Ico a b ∩ Set.Icc (0 : ℝ) 1 = Set.Ico a b := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · rintro ⟨hlt, hle⟩
      exact ⟨⟨hlt, hle⟩, ⟨le_trans h0 hlt, le_trans (le_of_lt hle) h1⟩⟩
  rw [hI, Real.volume_Ico]

/-- The mark measure of the set of marks whose `e`-th coordinate lies in a half-open
interval of `[0,1]`. -/
theorem markMeasure_Ico (e : Sym2 V) {a b : ℝ} (h0 : 0 ≤ a) (h1 : b ≤ 1) :
    markMeasure V {u : Sym2 V → ℝ | u e ∈ Set.Ico a b} = ENNReal.ofReal (b - a) := by
  classical
  have hset : {u : Sym2 V → ℝ | u e ∈ Set.Ico a b}
      = Set.pi ({e} : Finset (Sym2 V)) (fun i => if i = e then Set.Ico a b else Set.univ) := by
    ext u
    simp only [Set.mem_pi]
    constructor
    · intro h i hi
      have hie : i = e := by simpa using hi
      subst hie
      rw [ite_eq_left rfl]
      exact h
    · intro h
      have h' := h e (by simp)
      rw [ite_eq_left rfl] at h'
      exact h'
  rw [markMeasure, hset, Measure.infinitePi_pi]
  · rw [Finset.prod_singleton, ite_eq_left rfl, unif_Ico h0 h1]
  · intro i hi
    have hie : i = e := by simpa using hi
    subst hie
    rw [ite_eq_left rfl]
    exact measurableSet_Ico

/-- **Finite-range variation bound.**  If two edge profiles differ only on the finite set
`D`, then the probabilities of any measurable event under the two laws differ by at most
the `ℓ¹` distance of the profiles on `D`. -/
theorem edgeMeasure_abs_sub_le (p q : Sym2 V → unitInterval) (D : Finset (Sym2 V))
    (hD : ∀ e, p e ≠ q e → e ∈ D) (A : Set (Config V)) (hA : MeasurableSet A) :
    |(edgeMeasure p A).toReal - (edgeMeasure q A).toReal|
      ≤ ∑ e ∈ D, |(p e : ℝ) - (q e : ℝ)| := by
  classical
  have hkey : ∀ r : Sym2 V → unitInterval,
      edgeMeasure r A = (markMeasure V) ((atParameter r) ⁻¹' A) := by
    intro r
    have hstep := Measure.map_apply (μ := markMeasure V) (f := atParameter r)
      (measurable_atParameter r) (s := A) hA
    calc edgeMeasure r A = (markMeasure V).map (atParameter r) A := by
          rw [markMeasure_map_atParameter r]
      _ = (markMeasure V) ((atParameter r) ⁻¹' A) := hstep
  -- The set of marks at which the two thresholded configurations can differ.
  set T : Set (Sym2 V → ℝ) := ⋃ e ∈ D,
    {u : Sym2 V → ℝ | u e ∈ Set.Ico (min (p e : ℝ) (q e : ℝ)) (max (p e : ℝ) (q e : ℝ))}
    with hTdef
  -- Off `T` the two thresholded configurations coincide.
  have hmem : ∀ (u : Sym2 V → ℝ) (e : Sym2 V),
      u e ∈ Set.Ico (min (p e : ℝ) (q e : ℝ)) (max (p e : ℝ) (q e : ℝ)) → u ∈ T := by
    intro u e hu
    simp only [hTdef, Set.mem_iUnion, exists_prop]
    refine ⟨e, Finset.mem_coe.mpr (hD e ?_), hu⟩
    rintro hpq
    rw [hpq, min_self, max_self] at hu
    exact absurd hu.1 (not_le.mpr hu.2)
  have hagree : ∀ u : Sym2 V → ℝ, u ∉ T →
      (atParameter p u ∈ A ↔ atParameter q u ∈ A) := by
    intro u hu
    have hspec : ∀ e : Sym2 V,
        ¬ (min (p e : ℝ) (q e : ℝ) ≤ u e ∧ u e < max (p e : ℝ) (q e : ℝ)) :=
      fun e hcon => hu (hmem u e hcon)
    have hcfg : atParameter p u = atParameter q u := by
      funext e
      apply propext
      have hp_le : (p e : ℝ) ≤ max (p e : ℝ) (q e : ℝ) := le_max_left _ _
      have hq_le : (q e : ℝ) ≤ max (p e : ℝ) (q e : ℝ) := le_max_right _ _
      have hp_ge : min (p e : ℝ) (q e : ℝ) ≤ (p e : ℝ) := min_le_left _ _
      have hq_ge : min (p e : ℝ) (q e : ℝ) ≤ (q e : ℝ) := min_le_right _ _
      rcases not_and_or.mp (hspec e) with hlt | hge
      · rw [not_le] at hlt
        exact iff_of_true (lt_of_lt_of_le hlt hp_ge) (lt_of_lt_of_le hlt hq_ge)
      · rw [not_lt] at hge
        exact iff_of_false (not_lt.mpr (le_trans hp_le hge))
          (not_lt.mpr (le_trans hq_le hge))
    rw [hcfg]
  have hsub_p : (atParameter p) ⁻¹' A ⊆ (atParameter q) ⁻¹' A ∪ T := by
    intro u hu
    by_cases h : u ∈ T
    · exact Or.inr h
    · exact Or.inl ((hagree u h).mp hu)
  have hsub_q : (atParameter q) ⁻¹' A ⊆ (atParameter p) ⁻¹' A ∪ T := by
    intro u hu
    by_cases h : u ∈ T
    · exact Or.inr h
    · exact Or.inl ((hagree u h).mpr hu)
  have hTbound : markMeasure V T
      ≤ ∑ e ∈ D, ENNReal.ofReal |(p e : ℝ) - (q e : ℝ)| := by
    refine le_trans (measure_biUnion_finset_le D _) (Finset.sum_le_sum fun e _ => ?_)
    have hnn : (0 : ℝ) ≤ min (p e : ℝ) (q e : ℝ) := le_min (p e).2.1 (q e).2.1
    have hle1 : max (p e : ℝ) (q e : ℝ) ≤ 1 := max_le (p e).2.2 (q e).2.2
    rw [markMeasure_Ico e hnn hle1, max_sub_min_eq_abs, abs_sub_comm]
  have h1 : edgeMeasure p A ≤ edgeMeasure q A + markMeasure V T := by
    rw [hkey p, hkey q]
    exact le_trans (measure_mono hsub_p) (measure_union_le _ _)
  have h2 : edgeMeasure q A ≤ edgeMeasure p A + markMeasure V T := by
    rw [hkey p, hkey q]
    exact le_trans (measure_mono hsub_q) (measure_union_le _ _)
  set C : ℝ := ∑ e ∈ D, |(p e : ℝ) - (q e : ℝ)| with hCdef
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun e _ => abs_nonneg _
  have hCtop : (∑ e ∈ D, ENNReal.ofReal |(p e : ℝ) - (q e : ℝ)|) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun e _ => ENNReal.ofReal_ne_top
  have hTreal : (markMeasure V T).toReal ≤ C := by
    refine le_trans (ENNReal.toReal_mono hCtop hTbound) ?_
    rw [hCdef, ENNReal.toReal_sum fun e _ => ENNReal.ofReal_ne_top]
    exact le_of_eq (Finset.sum_congr rfl fun e _ => ENNReal.toReal_ofReal (abs_nonneg _))
  have hpp : edgeMeasure p A ≠ ⊤ := measure_ne_top _ _
  have hqp : edgeMeasure q A ≠ ⊤ := measure_ne_top _ _
  have hTp : markMeasure V T ≠ ⊤ := measure_ne_top _ _
  rw [abs_le]
  constructor
  · have hx := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hpp, hTp⟩) h2
    rw [ENNReal.toReal_add hpp hTp] at hx
    linarith
  · have hx := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqp, hTp⟩) h1
    rw [ENNReal.toReal_add hqp hTp] at hx
    linarith

end PercLib.CriticalLRP
