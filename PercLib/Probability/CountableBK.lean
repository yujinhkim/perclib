/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Corresponds to `truncation`, `disjointOccurrence_eq_iUnion_truncation`,
`measurableSet_disjointOccurrence` and `percolation_bk` in NearCritical/CountableBK.lean,
to `profileEventProbability_cylinder`, `percolationProfile_cylinder_bk_of_uniform_lt_one`
and `percolationProfile_bk_of_uniform_lt_one` in NearCritical/ProfileCountableBKStrict.lean,
and to `eventProbability_cylinder` in NearCritical/CylinderBK.lean, all at
tomhutchcroft/near-critical-diffusivity, revision
c820fea91a7482c1755de0ec94ecb9f59ccfcacc (reuse permission: DECISIONS R-3).
The uniform bound `P < 1` of the profile source is removed: endpoint-complete finite BK
(ProfileBK.lean) is applied on each finite truncation. The lattice cylinder bridge is
replaced by the general-index marginal identity `prodBernoulli_map_restrict`.
Under D-24 this proof file adds no definition: the truncation of an event `A` to a
finite coordinate set `s` is written out as `(fun η : Set s => Subtype.val '' η) ⁻¹' A`.
The exhaustion is the directed family of all finite coordinate sets, so no sequence
is chosen. The upstream source was not readable from the session that wrote this
file, so the Lean text is new; no upstream code is copied and no upstream licence is
asserted.
-/
module

public import PercLib.Probability.CylinderDisjointOccurrence
public import PercLib.Probability.ProfileBK

/-! # BK for increasing events on a countable index set

For increasing `A` and `B`, disjoint occurrence `A □ B` is the directed union over
finite coordinate sets `s` of the cylinder events "`A` and `B` occur disjointly using
open coordinates in `s` only". Each is a finite-cylinder disjoint occurrence of the
truncations, whose cylinders lie inside `A` and `B`. Finite BK for arbitrary profiles
and continuity from below give `P(A □ B) ≤ P(A) P(B)` for every profile, with no
uniform bound below one. The events `A` and `B` need not be measurable: the right side
uses the outer measure. Only `A □ B` is shown measurable.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace PercLib.Probability
variable {ι : Type*}

/-- The probability of a finite-cylinder event is that of its base event under the
restricted profile, for an arbitrary profile. -/
theorem measureReal_preimage_restrict (p : ι → unitInterval) (s : Finset ι)
    (A : Set (Set s)) :
    (prodBernoulli p).real ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' A) =
      (prodBernoulli (fun i : s => p i)).real A := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  rw [← prodBernoulli_map_restrict, measureReal_def, measureReal_def,
    Measure.map_apply hm (Set.toFinite A).measurableSet]

/-- The truncation of an increasing event to a coordinate set is increasing. -/
theorem isUpperSet_truncation (s : Set ι) {A : Set (Set ι)} (hA : IsUpperSet A) :
    IsUpperSet ((fun η : Set s => Subtype.val '' η) ⁻¹' A) :=
  fun _ _ h hη => hA (image_mono h) hη

/-- The cylinder of the truncation of an increasing event lies inside the event. -/
theorem preimage_restrict_truncation_subset (s : Set ι) {A : Set (Set ι)}
    (hA : IsUpperSet A) :
    (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        ((fun η : Set s => Subtype.val '' η) ⁻¹' A) ⊆ A := by
  intro ω hω
  have h : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) ∈ A := hω
  rw [Subtype.image_preimage_coe] at h
  exact hA inter_subset_right h

/-- Disjoint occurrence of truncations, read on the ambient configuration: the events
occur disjointly with finite open witnesses inside `s`. -/
theorem mem_preimage_restrict_disjointOccurrence_truncation_iff (s : Set ι)
    {A B : Set (Set ι)} (hA : IsUpperSet A) (hB : IsUpperSet B) (ω : Set ι) :
    ω ∈ (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        disjointOccurrence ((fun η : Set s => Subtype.val '' η) ⁻¹' A)
          ((fun η : Set s => Subtype.val '' η) ⁻¹' B) ↔
      ∃ F H : Set ι, F.Finite ∧ H.Finite ∧ Disjoint F H ∧ F ⊆ ω ∧ H ⊆ ω ∧
        F ⊆ s ∧ H ⊆ s ∧ F ∈ A ∧ H ∈ B := by
  rw [mem_preimage, mem_disjointOccurrence_iff_open (isUpperSet_truncation s hA)
    (isUpperSet_truncation s hB)]
  constructor
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩
    refine ⟨Subtype.val '' F, Subtype.val '' H, hF.image _, hH.image _,
      hd.image Subtype.val_injective.injOn (subset_univ _) (subset_univ _), ?_, ?_,
      ?_, ?_, hFA, hHB⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hFω hx
    · rintro _ ⟨x, hx, rfl⟩
      exact hHω hx
    · rintro _ ⟨x, _, rfl⟩
      exact x.property
    · rintro _ ⟨x, _, rfl⟩
      exact x.property
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hFs, hHs, hFA, hHB⟩
    refine ⟨Subtype.val ⁻¹' F, Subtype.val ⁻¹' H,
      hF.preimage Subtype.val_injective.injOn, hH.preimage Subtype.val_injective.injOn,
      hd.preimage _, preimage_mono hFω, preimage_mono hHω, ?_, ?_⟩
    · change Subtype.val '' (Subtype.val ⁻¹' F : Set s) ∈ A
      rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hFs]
    · change Subtype.val '' (Subtype.val ⁻¹' H : Set s) ∈ B
      rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hHs]

/-- Disjoint occurrence of increasing events is the union, over finite coordinate
sets, of the cylinders of disjoint occurrence of the truncations. -/
theorem disjointOccurrence_eq_iUnion_truncation {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    disjointOccurrence A B = ⋃ s : Finset ι,
      (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
        disjointOccurrence ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' A)
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' B) := by
  ext ω
  simp only [mem_iUnion]
  constructor
  · intro h
    obtain ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩ :=
      (mem_disjointOccurrence_iff_open hA hB ω).mp h
    refine ⟨(hF.union hH).toFinset, ?_⟩
    rw [mem_preimage_restrict_disjointOccurrence_truncation_iff _ hA hB]
    refine ⟨F, H, hF, hH, hd, hFω, hHω, ?_, ?_, hFA, hHB⟩
    · intro i hi
      simp [hi]
    · intro i hi
      simp [hi]
  · rintro ⟨s, hs⟩
    obtain ⟨F, H, hF, hH, hd, hFω, hHω, _, _, hFA, hHB⟩ :=
      (mem_preimage_restrict_disjointOccurrence_truncation_iff _ hA hB ω).mp hs
    exact (mem_disjointOccurrence_iff_open hA hB ω).mpr
      ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩

/-- The truncated disjoint occurrences increase with the coordinate set. -/
theorem directed_preimage_restrict_disjointOccurrence_truncation {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Directed (· ⊆ ·) fun s : Finset ι =>
      (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
        disjointOccurrence ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' A)
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' B) := by
  intro s t
  have hsub (u v : Finset ι) (huv : u ⊆ v) (ω : Set ι)
      (hω : ω ∈ (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (u : Set ι))) ⁻¹'
        disjointOccurrence ((fun η : Set (u : Set ι) => Subtype.val '' η) ⁻¹' A)
          ((fun η : Set (u : Set ι) => Subtype.val '' η) ⁻¹' B)) :
      ω ∈ (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (v : Set ι))) ⁻¹'
        disjointOccurrence ((fun η : Set (v : Set ι) => Subtype.val '' η) ⁻¹' A)
          ((fun η : Set (v : Set ι) => Subtype.val '' η) ⁻¹' B) := by
    obtain ⟨F, H, hF, hH, hd, hFω, hHω, hFs, hHs, hFA, hHB⟩ :=
      (mem_preimage_restrict_disjointOccurrence_truncation_iff _ hA hB ω).mp hω
    have huv' : (u : Set ι) ⊆ v := Finset.coe_subset.mpr huv
    exact (mem_preimage_restrict_disjointOccurrence_truncation_iff _ hA hB ω).mpr
      ⟨F, H, hF, hH, hd, hFω, hHω, hFs.trans huv', hHs.trans huv', hFA, hHB⟩
  exact ⟨s ∪ t, hsub s (s ∪ t) Finset.subset_union_left,
    hsub t (s ∪ t) Finset.subset_union_right⟩

/-- Finite-cylinder events are measurable. -/
theorem measurableSet_preimage_restrict (s : Set ι) (C : Set (Set s)) [Finite s] :
    MeasurableSet ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' C) := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  exact hm (Set.toFinite C).measurableSet

/-- On a countable index set, disjoint occurrence of increasing events is measurable,
whether or not the events themselves are. -/
theorem measurableSet_disjointOccurrence [Countable ι] {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    MeasurableSet (disjointOccurrence A B) := by
  rw [disjointOccurrence_eq_iUnion_truncation hA hB]
  exact MeasurableSet.iUnion fun s => measurableSet_preimage_restrict _ _

/-- BK for increasing finite-cylinder events under an arbitrary profile on an arbitrary
index type. -/
theorem cylinder_profile_bk (p : ι → unitInterval) (s : Finset ι) (A B : Set (Set s))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (prodBernoulli p).real
        (disjointOccurrence ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' A)
          ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' B)) ≤
      (prodBernoulli p).real ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' A) *
        (prodBernoulli p).real ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' B) := by
  have hD : disjointOccurrence ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' A)
      ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' B) =
      (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' disjointOccurrence A B :=
    disjointOccurrence_preimage_restrict (s : Set ι) A B
  rw [hD, measureReal_preimage_restrict, measureReal_preimage_restrict,
    measureReal_preimage_restrict]
  exact finite_bernoulliProfile_bk _ A B hA hB

/-- BK for increasing events under an arbitrary profile on a countable index set.
`A` and `B` need not be measurable; their measures are outer measures. -/
theorem countable_profile_bk [Countable ι] (p : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prodBernoulli p (disjointOccurrence A B) ≤ prodBernoulli p A * prodBernoulli p B := by
  set μ := prodBernoulli p
  rw [disjointOccurrence_eq_iUnion_truncation hA hB,
    (directed_preimage_restrict_disjointOccurrence_truncation hA hB).measure_iUnion]
  refine iSup_le fun s => ?_
  have h : μ.real
      (disjointOccurrence
        ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' A))
        ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' B))) ≤
      μ.real ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' A)) *
        μ.real ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' B)) :=
    cylinder_profile_bk p s ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' A)
      ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' B)
      (isUpperSet_truncation _ hA) (isUpperSet_truncation _ hB)
  rw [disjointOccurrence_preimage_restrict (s : Set ι)] at h
  have hreal : μ ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
        disjointOccurrence ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' A)
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' B)) ≤
      μ ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' A)) *
        μ ((fun ω : Set ι => (Subtype.val ⁻¹' ω : Set (s : Set ι))) ⁻¹'
          ((fun η : Set (s : Set ι) => Subtype.val '' η) ⁻¹' B)) := by
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul]
    exact h
  exact hreal.trans (mul_le_mul' (measure_mono (preimage_restrict_truncation_subset _ hA))
    (measure_mono (preimage_restrict_truncation_subset _ hB)))

/-- The real-valued form of countable profile BK. -/
theorem countable_profile_bk_real [Countable ι] (p : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (prodBernoulli p).real (disjointOccurrence A B) ≤
      (prodBernoulli p).real A * (prodBernoulli p).real B := by
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (countable_profile_bk p hA hB)
/-- BK for increasing events under a homogeneous law on a countable index set, at
every parameter. -/
theorem countable_bk [Countable ι] (p : unitInterval) {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prodBernoulli (fun _ : ι => p) (disjointOccurrence A B) ≤
      prodBernoulli (fun _ : ι => p) A * prodBernoulli (fun _ : ι => p) B :=
  countable_profile_bk _ hA hB

/-- **Product bound for finitely many disjoint increasing events.** Iterated disjoint
occurrence `(⋯((A □ B₁) □ B₂) ⋯) □ Bₖ` of increasing events on a countable index set has
probability at most the product of their probabilities, for every profile. -/
theorem countable_profile_bk_foldl [Countable ι] (p : ι → unitInterval)
    (Bs : List (Set (Set ι))) (hBs : ∀ B ∈ Bs, IsUpperSet B) {A : Set (Set ι)}
    (hA : IsUpperSet A) :
    prodBernoulli p (Bs.foldl disjointOccurrence A) ≤
      prodBernoulli p A * (Bs.map fun B => prodBernoulli p B).prod := by
  induction Bs generalizing A with
  | nil => simp
  | cons B Bs ih =>
    have hB : IsUpperSet B := hBs B List.mem_cons_self
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    refine (ih (fun C hC => hBs C (List.mem_cons_of_mem _ hC))
      (isUpperSet_disjointOccurrence hA hB)).trans ?_
    exact mul_le_mul_left (countable_profile_bk p hA hB) _


-- A profile on `ℕ` tending to one, with coordinate `0` surely closed.
example : (prodBernoulli (fun n : ℕ =>
      (⟨1 - 1 / ((n : ℝ) + 1), by
        constructor
        · rw [sub_nonneg, div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        · have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
          linarith⟩ : unitInterval))).real
    (disjointOccurrence {ω | 1 ∈ ω} {ω | 2 ∈ ω}) ≤
    (prodBernoulli (fun n : ℕ =>
      (⟨1 - 1 / ((n : ℝ) + 1), by
        constructor
        · rw [sub_nonneg, div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        · have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
          linarith⟩ : unitInterval))).real {ω | 1 ∈ ω} *
    (prodBernoulli (fun n : ℕ =>
      (⟨1 - 1 / ((n : ℝ) + 1), by
        constructor
        · rw [sub_nonneg, div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        · have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
          linarith⟩ : unitInterval))).real {ω | 2 ∈ ω} :=
  countable_profile_bk_real _ (fun _ _ h hi => h hi) (fun _ _ h hi => h hi)

-- The homogeneous law at a parameter above `1/2`, three events on `ℕ`.
example (p : unitInterval) :
    prodBernoulli (fun _ : ℕ => p)
        ([{ω : Set ℕ | 1 ∈ ω}, {ω | 2 ∈ ω}].foldl disjointOccurrence {ω | 0 ∈ ω}) ≤
      prodBernoulli (fun _ : ℕ => p) {ω | 0 ∈ ω} *
        (prodBernoulli (fun _ : ℕ => p) {ω | 1 ∈ ω} *
          prodBernoulli (fun _ : ℕ => p) {ω | 2 ∈ ω}) := by
  have h := countable_profile_bk_foldl (fun _ : ℕ => p) [{ω : Set ℕ | 1 ∈ ω}, {ω | 2 ∈ ω}]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro B (rfl | rfl) <;> exact fun _ _ h hi => h hi)
    (A := {ω | 0 ∈ ω}) (fun _ _ h hi => h hi)
  simpa using h

-- An increasing event with no finite witness: "infinitely many open coordinates".
-- It never occurs disjointly with finite certificates.
example :
    disjointOccurrence {ω : Set ℕ | ω.Infinite} Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω h
  obtain ⟨F, _, hF, _, _, _, _, hFA, _⟩ :=
    (mem_disjointOccurrence_iff_open (fun _ _ h hi => hi.mono h) isUpperSet_univ ω).mp h
  exact hFA hF

end PercLib.Probability
