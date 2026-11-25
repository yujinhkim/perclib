/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Corresponds to `finite_bernoulliProfile_bk_of_uniform_lt_one` in
NearCritical/ProfileBKStrict.lean at tomhutchcroft/near-critical-diffusivity,
revision c820fea91a7482c1755de0ec94ecb9f59ccfcacc (reuse permission: DECISIONS R-3),
and removes its restriction that every coordinate be below one, as issue 71 asks.
Route: low-density BK for profiles bounded by `1/2` (the induction of BKLowDensity.lean
with a coordinate-dependent parameter), exact OR-refinement of each coordinate into
`m` copies with its own parameter, and continuity in the profile for coordinates equal
to one (`q_t = (1 - t) q`). The three refinement lemmas of the first section correspond
to the same-named lemmas of NearCritical/BKAllParameters.lean at the same revision;
the homogeneous-only results of that file are not needed and are not ported. The
upstream source was not readable from the session that
wrote this file, so the Lean text is new; no upstream code is copied and no upstream
licence is asserted.
-/
module

public import PercLib.Probability.BKEndpoints
public import PercLib.Probability.BKLowDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Finite BK for arbitrary Bernoulli profiles

For a finite index type and an arbitrary profile `p : E → unitInterval`, including
coordinates that are surely open or surely closed,
`P_p(A □ B) ≤ P_p(A) P_p(B)` for increasing `A` and `B`.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical
namespace PercLib.Probability
variable {E : Type*}

/-! ## Refinement of coordinates -/

/-- A homogeneous finite law at a probability parameter has total weight one. -/
theorem finiteExpectation_const_one [Fintype E] {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    finiteExpectation q (fun _ : Set E => (1 : ℝ)) = 1 := by
  have h := finiteExpectation_eq_integral (⟨q, hq0, hq1⟩ : unitInterval)
    (fun _ : Set E => (1 : ℝ))
  rw [h]
  simp

/-- Increasing events pull back to increasing events of the refined coordinates. -/
theorem isUpperSet_preimage_image_fst {m : ℕ} {A : Set (Set E)} (hA : IsUpperSet A) :
    IsUpperSet ((fun ω : Set (E × Fin m) => Prod.fst '' ω) ⁻¹' A) :=
  fun _ _ h hω => hA (image_mono h) hω

/-- Disjoint occurrence of increasing events pulls back into disjoint occurrence of
the pullbacks: a certificate is lifted to all open refined copies above it. -/
theorem preimage_image_fst_disjointOccurrence_subset {m : ℕ} {A B : Set (Set E)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (fun ω : Set (E × Fin m) => Prod.fst '' ω) ⁻¹' disjointOccurrence A B ⊆
      disjointOccurrence ((fun ω : Set (E × Fin m) => Prod.fst '' ω) ⁻¹' A)
        ((fun ω : Set (E × Fin m) => Prod.fst '' ω) ⁻¹' B) := by
  intro ω hω
  obtain ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHB⟩ :=
    (mem_disjointOccurrence_iff_open hA hB _).mp hω
  have hlift (K : Set E) (hK : K ⊆ Prod.fst '' ω) :
      Prod.fst '' (ω ∩ Prod.fst ⁻¹' K) = K := by
    ext e
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro he
      obtain ⟨x, hxω, rfl⟩ := hK he
      exact ⟨x, ⟨hxω, he⟩, rfl⟩
  have hfin (K : Set E) (hK : K.Finite) : (ω ∩ Prod.fst ⁻¹' K).Finite :=
    (hK.prod (Set.finite_univ (α := Fin m))).subset fun x hx => ⟨hx.2, trivial⟩
  refine (mem_disjointOccurrence_iff_open (isUpperSet_preimage_image_fst hA)
    (isUpperSet_preimage_image_fst hB) ω).mpr
    ⟨ω ∩ Prod.fst ⁻¹' F, ω ∩ Prod.fst ⁻¹' H, hfin F hF, hfin H hH,
      (hd.preimage Prod.fst).mono inter_subset_right inter_subset_right,
      inter_subset_left, inter_subset_left, ?_, ?_⟩
  · change Prod.fst '' (ω ∩ Prod.fst ⁻¹' F) ∈ A
    rwa [hlift F hFω]
  · change Prod.fst '' (ω ∩ Prod.fst ⁻¹' H) ∈ B
    rwa [hlift H hHω]

/-! ## Profile expectations as finite sums -/

/-- Probabilities under a finite profile are explicit weighted sums. -/
theorem measureReal_prodBernoulli_eq_sum [Fintype E] (p : E → unitInterval)
    (C : Set (Set E)) :
    (prodBernoulli p).real C =
      ∑ ω : Set E, C.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, if i ∈ ω then (p i : ℝ) else 1 - (p i : ℝ) := by
  rw [← integral_prodBernoulli]
  exact (integral_indicator_one (Set.toFinite C).measurableSet).symm

/-- The weighted sum of an observable is continuous in a real-valued profile. -/
theorem continuous_profileSum [Fintype E] (f : Set E → ℝ) :
    Continuous fun r : E → ℝ =>
      ∑ ω : Set E, f ω * ∏ i : E, if i ∈ ω then r i else 1 - r i := by
  apply continuous_finsetSum
  intro ω _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  by_cases hi : i ∈ ω
  · simp only [hi, ite_true]
    exact continuous_apply i
  · simp only [hi, ite_false]
    exact continuous_const.sub (continuous_apply i)

/-- Splitting a weighted sum according to the extra coordinate of `Option E`. -/
theorem profileSum_option [Fintype E] (r : Option E → ℝ) (f : Set (Option E) → ℝ) :
    ∑ ω : Set (Option E), f ω * ∏ i : Option E, (if i ∈ ω then r i else 1 - r i) =
      (1 - r none) * ∑ η : Set E, f (Option.some '' η) *
          ∏ i : E, (if i ∈ η then r (some i) else 1 - r (some i)) +
        r none * ∑ η : Set E, f (insert none (Option.some '' η)) *
          ∏ i : E, (if i ∈ η then r (some i) else 1 - r (some i)) := by
  rw [sum_sets_option]
  simp [Fintype.prod_option, Finset.mul_sum, mul_left_comm]

/-- Weighted sums are invariant under a coordinate bijection. -/
theorem profileSum_image_equiv {F : Type*} [Fintype E] [Fintype F] (e : E ≃ F)
    (r : F → ℝ) (f : Set F → ℝ) :
    ∑ η : Set E, f (e '' η) * ∏ i : E, (if i ∈ η then r (e i) else 1 - r (e i)) =
      ∑ ω : Set F, f ω * ∏ i : F, (if i ∈ ω then r i else 1 - r i) := by
  rw [← e.setCongr.sum_comp (fun ω : Set F => f ω * ∏ i : F, if i ∈ ω then r i else 1 - r i)]
  apply Finset.sum_congr rfl
  intro η _
  simp only [Equiv.setCongr_apply]
  congr 1
  rw [← e.prod_comp (fun i : F => if i ∈ e '' η then r i else 1 - r i)]
  simp

/-- Weighted sums are monotone in the observable for probability profiles. -/
theorem profileSum_mono [Fintype E] {r : E → ℝ} (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    {f g : Set E → ℝ} (hfg : ∀ η, f η ≤ g η) :
    ∑ ω : Set E, f ω * ∏ i : E, (if i ∈ ω then r i else 1 - r i) ≤
      ∑ ω : Set E, g ω * ∏ i : E, (if i ∈ ω then r i else 1 - r i) := by
  apply Finset.sum_le_sum
  intro η _
  apply mul_le_mul_of_nonneg_right (hfg η)
  apply Finset.prod_nonneg
  intro i _
  have := hr0 i
  have := hr1 i
  split <;> linarith

/-! ## Low-density BK for profiles -/

/-- The statement of BK for a real profile, written as weighted sums. -/
theorem profileBK_option [Fintype E] {r : Option E → ℝ} (hr0 : ∀ i, 0 ≤ r i)
    (hrHalf : ∀ i, r i ≤ 1/2)
    (hBK : ∀ A B : Set (Set E), IsUpperSet A → IsUpperSet B →
      ∑ η : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) η *
          ∏ i : E, (if i ∈ η then r (some i) else 1 - r (some i)) ≤
        (∑ η : Set E, A.indicator (fun _ => (1 : ℝ)) η *
          ∏ i : E, (if i ∈ η then r (some i) else 1 - r (some i))) *
        (∑ η : Set E, B.indicator (fun _ => (1 : ℝ)) η *
          ∏ i : E, (if i ∈ η then r (some i) else 1 - r (some i))))
    (A B : Set (Set (Option E))) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    ∑ ω : Set (Option E), (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : Option E, (if i ∈ ω then r i else 1 - r i) ≤
      (∑ ω : Set (Option E), A.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : Option E, (if i ∈ ω then r i else 1 - r i)) *
      (∑ ω : Set (Option E), B.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : Option E, (if i ∈ ω then r i else 1 - r i)) := by
  -- Abbreviations for the tail weights, sections and their probabilities.
  set w : Set E → ℝ := fun η => ∏ i : E, (if i ∈ η then r (some i) else 1 - r (some i))
    with hw
  set ep : Set (Set E) → ℝ := fun C => ∑ η : Set E, C.indicator (fun _ => (1 : ℝ)) η * w η
    with hep
  set A0 := (fun θ : Set E => Option.some '' θ) ⁻¹' A
  set A1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' A
  set B0 := (fun θ : Set E => Option.some '' θ) ⁻¹' B
  set B1 := (fun θ : Set E => insert none (Option.some '' θ)) ⁻¹' B
  have hp0 := hr0 none
  have hpH := hrHalf none
  have ht0 : ∀ i : E, 0 ≤ r (some i) := fun i => hr0 (some i)
  have ht1 : ∀ i : E, r (some i) ≤ 1 := fun i => (hrHalf (some i)).trans (by norm_num)
  have hm (C D : Set (Set E)) (hCD : C ⊆ D) : ep C ≤ ep D := by
    apply profileSum_mono ht0 ht1
    intro η
    by_cases h : η ∈ C
    · simp [h, hCD h]
    · simp only [indicator_of_notMem h]
      exact indicator_nonneg (fun _ _ => by norm_num) _
  have h00 := hBK A0 B0 (isUpperSet_preimage_some hA) (isUpperSet_preimage_some hB)
  have h10 := hBK A1 B0 (isUpperSet_preimage_insert_none hA) (isUpperSet_preimage_some hB)
  have h01 := hBK A0 B1 (isUpperSet_preimage_some hA) (isUpperSet_preimage_insert_none hB)
  change ep (disjointOccurrence A0 B0) ≤ ep A0 * ep B0 at h00
  change ep (disjointOccurrence A1 B0) ≤ ep A1 * ep B0 at h10
  change ep (disjointOccurrence A0 B1) ≤ ep A0 * ep B1 at h01
  -- The closed section of disjoint occurrence is disjoint occurrence of the sections.
  have hclosed : (fun η : Set E => (disjointOccurrence A B).indicator (fun _ => (1 : ℝ))
      (Option.some '' η)) = (disjointOccurrence A0 B0).indicator (fun _ => (1 : ℝ)) := by
    funext η
    simp only [indicator, disjointOccurrence_image_some_iff hA hB]
    rfl
  -- The open section is bounded by inclusion-exclusion.
  have hopen : ∑ η : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ))
      (insert none (Option.some '' η)) * w η ≤
      ep (disjointOccurrence A1 B0) + ep (disjointOccurrence A0 B1) -
        ep (disjointOccurrence A0 B0) := by
    have h := profileSum_mono ht0 ht1
      (fun η => indicator_disjointOccurrence_insert_none_le hA hB η)
    refine h.trans (le_of_eq ?_)
    simp only [hep, hw, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rfl
  have hclosed' : ∑ η : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ))
      (Option.some '' η) * w η = ep (disjointOccurrence A0 B0) := by
    apply Finset.sum_congr rfl
    intro η _
    rw [congrFun hclosed η]
  rw [profileSum_option, profileSum_option, profileSum_option]
  change (1 - r none) * (∑ η : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ))
      (Option.some '' η) * w η) + r none * (∑ η : Set E,
        (disjointOccurrence A B).indicator (fun _ => (1 : ℝ))
          (insert none (Option.some '' η)) * w η) ≤
    ((1 - r none) * ep A0 + r none * ep A1) * ((1 - r none) * ep B0 + r none * ep B1)
  rw [hclosed']
  have hc : 0 ≤ 1 - 2 * r none := by linarith
  have hfirst : (1 - r none) * ep (disjointOccurrence A0 B0) +
      r none * ∑ η : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ))
        (insert none (Option.some '' η)) * w η ≤
      (1 - 2 * r none) * (ep A0 * ep B0) + r none * (ep A1 * ep B0 + ep A0 * ep B1) := by
    nlinarith [mul_le_mul_of_nonneg_left hopen hp0, mul_le_mul_of_nonneg_left h00 hc,
      mul_le_mul_of_nonneg_left h10 hp0, mul_le_mul_of_nonneg_left h01 hp0]
  exact hfirst.trans (bk_step_arithmetic (hm _ _ (section_closed_subset_open hA))
    (hm _ _ (section_closed_subset_open hB)))

/-- Low-density BK for real profiles bounded by `1/2`, as weighted sums. -/
theorem profileSum_bk_le_half [Fintype E] {r : E → ℝ} (hr0 : ∀ i, 0 ≤ r i)
    (hrHalf : ∀ i, r i ≤ 1/2) (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    ∑ ω : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i) ≤
      (∑ ω : Set E, A.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i)) *
      (∑ ω : Set E, B.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i)) := by
  revert r A B
  refine Fintype.induction_empty_option
    (P := fun α [Fintype α] => ∀ {r : α → ℝ}, (∀ i, 0 ≤ r i) → (∀ i, r i ≤ 1/2) →
      ∀ A B : Set (Set α), IsUpperSet A → IsUpperSet B →
      ∑ ω : Set α, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) ω *
          ∏ i : α, (if i ∈ ω then r i else 1 - r i) ≤
        (∑ ω : Set α, A.indicator (fun _ => (1 : ℝ)) ω *
          ∏ i : α, (if i ∈ ω then r i else 1 - r i)) *
        (∑ ω : Set α, B.indicator (fun _ => (1 : ℝ)) ω *
          ∏ i : α, (if i ∈ ω then r i else 1 - r i))) ?_ ?_ ?_ E
  · intro α β hβ e hBK r hr0 hrHalf A B hA hB
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := hBK (r := fun i => r (e i)) (fun i => hr0 _) (fun i => hrHalf _)
      ((fun θ : Set α => e '' θ) ⁻¹' A) ((fun θ : Set α => e '' θ) ⁻¹' B)
      (isUpperSet_preimage_image e hA) (isUpperSet_preimage_image e hB)
    have hind (C : Set (Set β)) : ((fun θ : Set α => e '' θ) ⁻¹' C).indicator
        (fun _ => (1 : ℝ)) = fun η => C.indicator (fun _ => (1 : ℝ)) (e '' η) := by
      funext η
      simp only [indicator, mem_preimage]
    have hD : (disjointOccurrence ((fun θ : Set α => e '' θ) ⁻¹' A)
        ((fun θ : Set α => e '' θ) ⁻¹' B)).indicator (fun _ => (1 : ℝ)) =
        fun η => (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) (e '' η) := by
      funext η
      simp only [indicator, disjointOccurrence_image_equiv_iff e hA hB]
    rw [hD, hind, hind, profileSum_image_equiv e r, profileSum_image_equiv e r,
      profileSum_image_equiv e r] at h
    convert h using 3
  · intro r _ _ A B _ _
    have hr : r = fun _ => 0 := funext fun i => i.elim
    subst hr
    have h := lowDensityBK_empty 0 A B
    simpa [finiteExpectation] using h
  · intro α _ hBK r hr0 hrHalf A B hA hB
    exact profileBK_option hr0 hrHalf
      (fun A B hA hB => hBK (fun i => hr0 _) (fun i => hrHalf _) A B hA hB) A B hA hB

/-! ## Exact refinement of each coordinate -/

/-- Refining coordinate `e` into `m` copies open with probability `q e` each, and
declaring `e` open when one copy is, gives the profile `1 - (1 - q e) ^ m`. -/
theorem profileSum_image_fst [Fintype E] (m : ℕ) {q : E → ℝ} (hq0 : ∀ e, 0 ≤ q e)
    (hq1 : ∀ e, q e ≤ 1) (f : Set E → ℝ) :
    ∑ ω : Set (E × Fin m), f (Prod.fst '' ω) *
        ∏ x : E × Fin m, (if x ∈ ω then q x.1 else 1 - q x.1) =
      ∑ ω : Set E, f ω * ∏ e : E,
        (if e ∈ ω then 1 - (1 - q e) ^ m else 1 - (1 - (1 - q e) ^ m)) := by
  let φ : (E → Set (Fin m)) ≃ Set (E × Fin m) :=
    { toFun := fun g => {x | x.2 ∈ g x.1}
      invFun := fun ω e => {j | (e, j) ∈ ω}
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let W : E → Set (Fin m) → ℝ := fun e s => ∏ j : Fin m, if j ∈ s then q e else 1 - q e
  let N : (E → Set (Fin m)) → Set E := fun g => {e | (g e).Nonempty}
  let S : Set E → E → Finset (Set (Fin m)) := fun T e =>
    Finset.univ.filter fun s => (s.Nonempty ↔ e ∈ T)
  have hWsum (e : E) : ∑ s : Set (Fin m), W e s = 1 := by
    have h := finiteExpectation_const_one (E := Fin m) (hq0 e) (hq1 e)
    simpa [finiteExpectation, W] using h
  have hP0 (e : E) : ∑ s ∈ Finset.univ.filter (fun s : Set (Fin m) => ¬ s.Nonempty), W e s =
      (1 - q e) ^ m := by
    simp only [Set.not_nonempty_iff_eq_empty, Finset.filter_eq', Finset.mem_univ, ite_true,
      Finset.sum_singleton]
    simp [W]
  have hP1 (e : E) : ∑ s ∈ Finset.univ.filter (fun s : Set (Fin m) => s.Nonempty), W e s =
      1 - (1 - q e) ^ m := by
    rw [eq_sub_iff_add_eq, ← hP0 e, Finset.sum_filter_add_sum_filter_not, hWsum e]
  have hfactor (T : Set E) (e : E) :
      (if e ∈ T then 1 - (1 - q e) ^ m else 1 - (1 - (1 - q e) ^ m)) =
        ∑ s ∈ S T e, W e s := by
    by_cases he : e ∈ T
    · simp only [he, ite_true, S, iff_true]
      exact (hP1 e).symm
    · simp only [he, ite_false, S, iff_false]
      rw [hP0]
      ring
  have hfiber (T : Set E) :
      Fintype.piFinset (S T) = Finset.univ.filter (fun g => N g = T) := by
    ext g
    simp [Fintype.mem_piFinset, S, N, Set.ext_iff]
  have hL : ∑ ω : Set (E × Fin m), f (Prod.fst '' ω) *
        ∏ x : E × Fin m, (if x ∈ ω then q x.1 else 1 - q x.1) =
      ∑ g : E → Set (Fin m), f (N g) * ∏ e : E, W e (g e) := by
    rw [← φ.sum_comp]
    apply Finset.sum_congr rfl
    intro g _
    have himg : Prod.fst '' (φ g) = N g := by
      ext e
      simp [φ, N, Set.Nonempty]
    rw [himg, Fintype.prod_prod_type]
    rfl
  rw [hL]
  symm
  calc ∑ T : Set E, f T * ∏ e : E,
        (if e ∈ T then 1 - (1 - q e) ^ m else 1 - (1 - (1 - q e) ^ m))
      = ∑ T : Set E, ∑ g ∈ Finset.univ.filter (fun g => N g = T),
          f (N g) * ∏ e : E, W e (g e) := by
        apply Finset.sum_congr rfl
        intro T _
        simp only [hfactor, Finset.prod_univ_sum, Finset.mul_sum, hfiber]
        apply Finset.sum_congr rfl
        intro g hg
        rw [(Finset.mem_filter.mp hg).2]
    _ = ∑ g : E → Set (Fin m), f (N g) * ∏ e : E, W e (g e) :=
        Finset.sum_fiberwise Finset.univ N _

/-- BK for every real profile of the form `1 - (1 - q e) ^ m` with `0 ≤ q e ≤ 1/2`. -/
theorem profileSum_bk_refine [Fintype E] (m : ℕ) {q : E → ℝ} (hq0 : ∀ e, 0 ≤ q e)
    (hqHalf : ∀ e, q e ≤ 1/2) (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    ∑ ω : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) ω *
        ∏ e : E, (if e ∈ ω then 1 - (1 - q e) ^ m else 1 - (1 - (1 - q e) ^ m)) ≤
      (∑ ω : Set E, A.indicator (fun _ => (1 : ℝ)) ω *
        ∏ e : E, (if e ∈ ω then 1 - (1 - q e) ^ m else 1 - (1 - (1 - q e) ^ m))) *
      (∑ ω : Set E, B.indicator (fun _ => (1 : ℝ)) ω *
        ∏ e : E, (if e ∈ ω then 1 - (1 - q e) ^ m else 1 - (1 - (1 - q e) ^ m))) := by
  have hq1 : ∀ e, q e ≤ 1 := fun e => (hqHalf e).trans (by norm_num)
  have hpull (C : Set (Set E)) :
      ∑ ω : Set E, C.indicator (fun _ => (1 : ℝ)) ω *
          ∏ e : E, (if e ∈ ω then 1 - (1 - q e) ^ m else 1 - (1 - (1 - q e) ^ m)) =
        ∑ ω : Set (E × Fin m),
          ((fun ω : Set (E × Fin m) => Prod.fst '' ω) ⁻¹' C).indicator (fun _ => (1 : ℝ)) ω *
          ∏ x : E × Fin m, (if x ∈ ω then q x.1 else 1 - q x.1) := by
    rw [← profileSum_image_fst m hq0 hq1 (C.indicator fun _ => (1 : ℝ))]
    exact Finset.sum_congr rfl fun ω _ => rfl
  rw [hpull, hpull, hpull]
  have hlow := profileSum_bk_le_half (r := fun x : E × Fin m => q x.1) (fun x => hq0 x.1)
    (fun x => hqHalf x.1) _ _ (isUpperSet_preimage_image_fst (m := m) hA)
    (isUpperSet_preimage_image_fst (m := m) hB)
  refine le_trans ?_ hlow
  apply profileSum_mono (r := fun x : E × Fin m => q x.1) (fun x => hq0 x.1)
    (fun x => hq1 x.1)
  intro ω
  exact indicator_le_indicator_of_subset
    (preimage_image_fst_disjointOccurrence_subset hA hB) (fun _ => zero_le_one) ω

/-- A coordinate parameter below one is the refinement of a parameter at most `1/2`,
for every number of copies `m ≥ 1` with `(1/2) ^ m ≤ 1 - p`. -/
theorem refinement_parameter {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (hm : m ≠ 0)
    (hbase : (1/2 : ℝ) ^ m ≤ 1 - p) :
    0 ≤ 1 - (1 - p) ^ ((m : ℝ)⁻¹) ∧ 1 - (1 - p) ^ ((m : ℝ)⁻¹) ≤ 1/2 ∧
      1 - (1 - (1 - (1 - p) ^ ((m : ℝ)⁻¹))) ^ m = p := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h1p : 0 ≤ 1 - p := by linarith
  have hx1 : (1 - p) ^ ((m : ℝ)⁻¹) ≤ 1 :=
    Real.rpow_le_one h1p (by linarith) (by positivity)
  have hxhalf : 1/2 ≤ (1 - p) ^ ((m : ℝ)⁻¹) := by
    have h : ((1/2 : ℝ) ^ m) ^ ((m : ℝ)⁻¹) = 1/2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_inv_cancel₀ hm',
        Real.rpow_one]
    rw [← h]
    exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
  refine ⟨by linarith, by linarith, ?_⟩
  rw [sub_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul h1p, inv_mul_cancel₀ hm',
    Real.rpow_one]
  ring

/-- BK as weighted sums for every real profile with values in `[0, 1)`. -/
theorem profileSum_bk_of_lt_one [Fintype E] {r : E → ℝ} (hr0 : ∀ e, 0 ≤ r e)
    (hr1 : ∀ e, r e < 1) (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    ∑ ω : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i) ≤
      (∑ ω : Set E, A.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i)) *
      (∑ ω : Set E, B.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i)) := by
  have hn (e : E) : ∃ n : ℕ, (1/2 : ℝ) ^ n < 1 - r e :=
    exists_pow_lt_of_lt_one (sub_pos.mpr (hr1 e)) (by norm_num)
  choose n hn using hn
  set m := 1 + ∑ e, n e with hmdef
  have hm : m ≠ 0 := by omega
  have hbase (e : E) : (1/2 : ℝ) ^ m ≤ 1 - r e := by
    refine (pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_).trans (hn e).le
    have := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    omega
  have hq (e : E) := refinement_parameter (hr0 e) (hr1 e).le hm (hbase e)
  have h := profileSum_bk_refine m (q := fun e => 1 - (1 - r e) ^ ((m : ℝ)⁻¹))
    (fun e => (hq e).1) (fun e => (hq e).2.1) A B hA hB
  simp only [(hq _).2.2] at h
  exact h

/-! ## Arbitrary profiles -/

/-- BK as weighted sums for every real profile with values in `[0, 1]`. -/
theorem profileSum_bk [Fintype E] {r : E → ℝ} (hr0 : ∀ e, 0 ≤ r e)
    (hr1 : ∀ e, r e ≤ 1) (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    ∑ ω : Set E, (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i) ≤
      (∑ ω : Set E, A.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i)) *
      (∑ ω : Set E, B.indicator (fun _ => (1 : ℝ)) ω *
        ∏ i : E, (if i ∈ ω then r i else 1 - r i)) := by
  -- Scale the profile by `1 - t` with `t = 1 / (k + 2)` and let `k → ∞`.
  let rk : ℕ → E → ℝ := fun k e => (1 - 1 / ((k : ℝ) + 2)) * r e
  have hlim : Tendsto rk atTop (𝓝 r) := by
    have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have ht : Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h2
    refine tendsto_pi_nhds.mpr fun e => ?_
    have h := ht.mul_const (r e)
    rw [one_mul] at h
    exact h
  have hk (k : ℕ) := profileSum_bk_of_lt_one (r := rk k)
    (fun e => by
      have : (0 : ℝ) ≤ 1 - 1 / ((k : ℝ) + 2) := by
        rw [sub_nonneg, div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      exact mul_nonneg this (hr0 e))
    (fun e => by
      have hpos : 0 < 1 / ((k : ℝ) + 2) := by positivity
      calc (1 - 1 / ((k : ℝ) + 2)) * r e ≤ (1 - 1 / ((k : ℝ) + 2)) * 1 := by
            apply mul_le_mul_of_nonneg_left (hr1 e)
            rw [sub_nonneg, div_le_one (by positivity)]
            linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        _ < 1 := by linarith)
    A B hA hB
  have hc (f : Set E → ℝ) := ((continuous_profileSum f).tendsto r).comp hlim
  exact le_of_tendsto_of_tendsto' (hc _) ((hc _).mul (hc _)) hk

/-- **Finite BK for arbitrary Bernoulli profiles.** For increasing events on a finite
index type and any profile, including coordinates equal to zero or one,
`P(A □ B) ≤ P(A) P(B)`. -/
theorem finite_bernoulliProfile_bk [Fintype E] (p : E → unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (prodBernoulli p).real (disjointOccurrence A B) ≤
      (prodBernoulli p).real A * (prodBernoulli p).real B := by
  simp only [measureReal_prodBernoulli_eq_sum]
  exact profileSum_bk (fun e => (p e).property.1) (fun e => (p e).property.2) A B hA hB

/-- **Finite BK for arbitrary Bernoulli profiles**, as an inequality of measures. -/
theorem finite_bernoulliProfile_bk_measure [Fintype E] (p : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prodBernoulli p (disjointOccurrence A B) ≤ prodBernoulli p A * prodBernoulli p B := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul]
  exact finite_bernoulliProfile_bk p A B hA hB

-- Mixed endpoints and unequal interior coordinates on a three-point index type.
example : (prodBernoulli (fun i : Fin 3 =>
      if i = 0 then (1 : unitInterval) else if i = 1 then 0
      else (⟨3/4, by norm_num, by norm_num⟩ : unitInterval))).real
    (disjointOccurrence {ω | (0 : Fin 3) ∈ ω} {ω | (2 : Fin 3) ∈ ω}) ≤
    (prodBernoulli (fun i : Fin 3 =>
      if i = 0 then (1 : unitInterval) else if i = 1 then 0
      else (⟨3/4, by norm_num, by norm_num⟩ : unitInterval))).real {ω | (0 : Fin 3) ∈ ω} *
    (prodBernoulli (fun i : Fin 3 =>
      if i = 0 then (1 : unitInterval) else if i = 1 then 0
      else (⟨3/4, by norm_num, by norm_num⟩ : unitInterval))).real {ω | (2 : Fin 3) ∈ ω} :=
  finite_bernoulliProfile_bk _ _ _ (fun _ _ h hi => h hi) (fun _ _ h hi => h hi)

-- The empty index type.
example (p : Empty → unitInterval) :
    (prodBernoulli p).real (disjointOccurrence Set.univ Set.univ) ≤
      (prodBernoulli p).real Set.univ * (prodBernoulli p).real Set.univ :=
  finite_bernoulliProfile_bk p _ _ isUpperSet_univ isUpperSet_univ

end PercLib.Probability
