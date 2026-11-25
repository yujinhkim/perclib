/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 124, Q-8). No upstream proof is copied.
-/
module

public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.Transport.Reindexing
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Mixing and ergodicity of Bernoulli product measures

Let `e : ℕ → ι ≃ ι` be a sequence of relabellings that preserve `prodBernoulli p` and that
eventually move every finite set of coordinates off every other finite set. Then the
relabellings are mixing: `P(A ∩ e_n⁻¹ B) → P(A) P(B)` for measurable `A`, `B`. Hence every
measurable event invariant under all `e_n` has probability `0` or `1`, and every measurable
invariant `ℕ∞`-valued observable is almost surely constant.

The proof approximates `A` and `B` by finite cylinders (mathlib's
`exists_measure_symmDiff_lt_of_generateFrom_isSetRing`); far-apart cylinders are independent
(`prodBernoulli_indepFun_finset`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology symmDiff

namespace PercLib.Probability

variable {ι : Type*}

/-! ### Approximation by finite cylinders -/

/-- Every measurable event is approximated in measure by an event depending on finitely many
coordinates. -/
theorem exists_finset_measure_symmDiff_lt (μ : Measure (Set ι)) [IsFiniteMeasure μ]
    {A : Set (Set ι)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (F : Finset ι) (S : Set (F → Prop)), MeasurableSet S ∧
      μ ({ω : Set ι | (fun i : F => (i : ι) ∈ ω) ∈ S} ∆ A) < ε := by
  obtain ⟨t, ht, hlt⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ)
    (C := (measurableCylinders (fun _ : ι => Prop) : Set (Set (Set ι))))
    isSetRing_measurableCylinders
    ⟨{Set.univ}, countable_singleton _,
      Set.singleton_subset_iff.2 (univ_mem_measurableCylinders (fun _ : ι => Prop)), by simp⟩
    generateFrom_measurableCylinders.symm hA hε
  obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders _).1 ht
  exact ⟨F, S, hS, hlt⟩

/-- A finite cylinder event is measurable. -/
theorem measurableSet_finset_cylinder (F : Finset ι) {S : Set (F → Prop)}
    (hS : MeasurableSet S) :
    MeasurableSet {ω : Set ι | (fun i : F => (i : ι) ∈ ω) ∈ S} :=
  (measurable_pi_iff.2 fun (i : F) => measurable_set_mem (i : ι) :
    Measurable fun (ω : Set ι) (i : F) => (i : ι) ∈ ω) hS

/-! ### Independence of far-apart cylinders -/

/-- A cylinder on `F` is independent of a relabelled cylinder on `G` when the relabelling
moves `F` off `G`. -/
theorem prodBernoulli_cylinder_inter_preimage (p : ι → unitInterval) (e : ι ≃ ι)
    (F G : Finset ι) (hFG : ∀ i ∈ F, e i ∉ G) {S : Set (F → Prop)} {T : Set (G → Prop)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    prodBernoulli p ({ω : Set ι | (fun i : F => (i : ι) ∈ ω) ∈ S} ∩
        (fun ω : Set ι => e '' ω) ⁻¹' {ω : Set ι | (fun j : G => (j : ι) ∈ ω) ∈ T}) =
      prodBernoulli p {ω : Set ι | (fun i : F => (i : ι) ∈ ω) ∈ S} *
        prodBernoulli p ((fun ω : Set ι => e '' ω) ⁻¹'
          {ω : Set ι | (fun j : G => (j : ι) ∈ ω) ∈ T}) := by
  classical
  set G' : Finset ι := G.map e.symm.toEmbedding with hG'
  have hmem : ∀ j : G, e.symm j ∈ G' := fun j =>
    Finset.mem_map_of_mem e.symm.toEmbedding j.2
  have hdisj : Disjoint F G' := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 hi'
    refine hFG i hi ?_
    rw [← hji]
    simpa using hj
  set φ : (G' → Prop) → (G → Prop) := fun χ j => χ ⟨e.symm j, hmem j⟩ with hφ
  have hφm : Measurable φ := measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hind := (prodBernoulli_indepFun_finset p F G' hdisj).comp measurable_id hφm
  have hpre : (fun ω : Set ι => e '' ω) ⁻¹' {ω : Set ι | (fun j : G => (j : ι) ∈ ω) ∈ T} =
      (φ ∘ fun (ω : Set ι) (i : G') => (i : ι) ∈ ω) ⁻¹' T := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, Function.comp_apply, hφ, Set.mem_image_equiv]
  rw [hpre]
  exact hind.measure_inter_preimage_eq_mul S T hS hT

/-! ### Mixing -/

theorem inter_symmDiff_inter_subset' (A A' C C' : Set (Set ι)) :
    (A ∩ C) ∆ (A' ∩ C') ⊆ (A ∆ A') ∪ (C ∆ C') := by
  intro ω
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union]
  tauto

/-- **Mixing.** Relabellings that preserve the law and separate finite sets are mixing. -/
theorem prodBernoulli_tendsto_inter_preimage (p : ι → unitInterval) (e : ℕ → ι ≃ ι)
    (hpres : ∀ n, MeasurePreserving (fun ω : Set ι => e n '' ω)
      (prodBernoulli p) (prodBernoulli p))
    (hsep : ∀ F G : Finset ι, ∀ᶠ n in atTop, ∀ i ∈ F, e n i ∉ G)
    {A B : Set (Set ι)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n => prodBernoulli p (A ∩ (fun ω => e n '' ω) ⁻¹' B)) atTop
      (𝓝 (prodBernoulli p A * prodBernoulli p B)) := by
  set μ := prodBernoulli p with hμ
  -- Reduce to real-valued measures.
  have hreal : Tendsto (fun n => μ.real (A ∩ (fun ω => e n '' ω) ⁻¹' B)) atTop
      (𝓝 (μ.real A * μ.real B)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε4 : 0 < ε / 4 := by positivity
    obtain ⟨F, S, hS, hAS⟩ := exists_finset_measure_symmDiff_lt μ hA
      (ENNReal.ofReal_pos.2 hε4)
    obtain ⟨G, T, hT, hBT⟩ := exists_finset_measure_symmDiff_lt μ hB
      (ENNReal.ofReal_pos.2 hε4)
    set A' := {ω : Set ι | (fun i : F => (i : ι) ∈ ω) ∈ S} with hA'
    set B' := {ω : Set ι | (fun j : G => (j : ι) ∈ ω) ∈ T} with hB'
    have hA'm : MeasurableSet A' := measurableSet_finset_cylinder F hS
    have hB'm : MeasurableSet B' := measurableSet_finset_cylinder G hT
    have hAS' : μ.real (A' ∆ A) < ε / 4 := by
      rw [measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hAS
        |>.trans_eq (ENNReal.toReal_ofReal hε4.le)
    have hBT' : μ.real (B' ∆ B) < ε / 4 := by
      rw [measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hBT
        |>.trans_eq (ENNReal.toReal_ofReal hε4.le)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hsep F G)
    refine ⟨N, fun n hn => ?_⟩
    set Tn := fun ω : Set ι => e n '' ω with hTn
    have hTm : Measurable Tn := (hpres n).measurable
    have hfac : μ.real (A' ∩ Tn ⁻¹' B') = μ.real A' * μ.real B' := by
      rw [measureReal_def, measureReal_def, measureReal_def,
        prodBernoulli_cylinder_inter_preimage p (e n) F G (hN n hn) hS hT,
        (hpres n).measure_preimage hB'm.nullMeasurableSet, ENNReal.toReal_mul]
    have h1 : |μ.real (A ∩ Tn ⁻¹' B) - μ.real (A' ∩ Tn ⁻¹' B')| ≤
        μ.real (A' ∆ A) + μ.real (B' ∆ B) := by
      refine (abs_measureReal_sub_le_measureReal_symmDiff
        (hA.inter (hTm hB)).nullMeasurableSet
        (hA'm.inter (hTm hB'm)).nullMeasurableSet).trans ?_
      refine (measureReal_mono (inter_symmDiff_inter_subset' _ _ _ _)).trans
        ((measureReal_union_le _ _).trans ?_)
      rw [← Set.preimage_symmDiff, (hpres n).measureReal_preimage
        (hB.symmDiff hB'm).nullMeasurableSet, symmDiff_comm A, symmDiff_comm B]
    have hA1 : μ.real A ≤ 1 := measureReal_le_one
    have hB1 : μ.real B' ≤ 1 := measureReal_le_one
    have hA0 : 0 ≤ μ.real A := measureReal_nonneg
    have hB0 : 0 ≤ μ.real B' := measureReal_nonneg
    have h2 : |μ.real A' - μ.real A| ≤ μ.real (A' ∆ A) :=
      abs_measureReal_sub_le_measureReal_symmDiff hA'm.nullMeasurableSet hA.nullMeasurableSet
    have h3 : |μ.real B' - μ.real B| ≤ μ.real (B' ∆ B) :=
      abs_measureReal_sub_le_measureReal_symmDiff hB'm.nullMeasurableSet hB.nullMeasurableSet
    have h4 : |μ.real A' * μ.real B' - μ.real A * μ.real B| ≤
        μ.real (A' ∆ A) + μ.real (B' ∆ B) := by
      have : μ.real A' * μ.real B' - μ.real A * μ.real B =
          (μ.real A' - μ.real A) * μ.real B' + μ.real A * (μ.real B' - μ.real B) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
      have := mul_le_mul h2 hB1 hB0 measureReal_nonneg
      have := mul_le_mul hA1 h3 (abs_nonneg _) zero_le_one
      nlinarith
    rw [Real.dist_eq]
    calc |μ.real (A ∩ Tn ⁻¹' B) - μ.real A * μ.real B|
        ≤ |μ.real (A ∩ Tn ⁻¹' B) - μ.real (A' ∩ Tn ⁻¹' B')| +
            |μ.real A' * μ.real B' - μ.real A * μ.real B| := by
          rw [← hfac]; exact abs_sub_le _ _ _
      _ ≤ 2 * (μ.real (A' ∆ A) + μ.real (B' ∆ B)) := by linarith
      _ < ε := by linarith
  have h := ENNReal.tendsto_ofReal hreal
  have e1 : ∀ X : Set (Set ι), ENNReal.ofReal (μ.real X) = μ X := fun X =>
    ofReal_measureReal (measure_ne_top μ X)
  simp only [ENNReal.ofReal_mul measureReal_nonneg, e1] at h
  exact h

/-! ### Ergodicity -/

/-- An element of `ℝ≥0∞` equal to its square is `0`, `1` or `∞`. -/
theorem eq_zero_or_one_of_eq_mul_self (x : ℝ≥0∞) (hx : x ≠ ∞) (h : x = x * x) :
    x = 0 ∨ x = 1 := by
  by_cases h0 : x = 0
  · exact Or.inl h0
  · right
    have h' : x * 1 = x * x := by rw [mul_one]; exact h
    exact ((ENNReal.mul_right_inj h0 hx).1 h').symm

/-- **Ergodicity.** A measurable event invariant under every relabelling has probability `0`
or `1`. -/
theorem prodBernoulli_eq_zero_or_one_of_invariant (p : ι → unitInterval) (e : ℕ → ι ≃ ι)
    (hpres : ∀ n, MeasurePreserving (fun ω : Set ι => e n '' ω)
      (prodBernoulli p) (prodBernoulli p))
    (hsep : ∀ F G : Finset ι, ∀ᶠ n in atTop, ∀ i ∈ F, e n i ∉ G)
    {A : Set (Set ι)} (hA : MeasurableSet A)
    (hinv : ∀ n, (fun ω : Set ι => e n '' ω) ⁻¹' A = A) :
    prodBernoulli p A = 0 ∨ prodBernoulli p A = 1 := by
  have h := prodBernoulli_tendsto_inter_preimage p e hpres hsep hA hA
  simp only [hinv, Set.inter_self] at h
  exact eq_zero_or_one_of_eq_mul_self _ (measure_ne_top _ _)
    (tendsto_nhds_unique tendsto_const_nhds h)

/-- **Ergodicity for observables.** A measurable `ℕ∞`-valued observable invariant under every
relabelling is almost surely constant. -/
theorem prodBernoulli_ae_eq_const_of_invariant (p : ι → unitInterval) (e : ℕ → ι ≃ ι)
    (hpres : ∀ n, MeasurePreserving (fun ω : Set ι => e n '' ω)
      (prodBernoulli p) (prodBernoulli p))
    (hsep : ∀ F G : Finset ι, ∀ᶠ n in atTop, ∀ i ∈ F, e n i ∉ G)
    {f : Set ι → ℕ∞} (hf : Measurable f) (hinv : ∀ n ω, f (e n '' ω) = f ω) :
    ∃ c : ℕ∞, ∀ᵐ ω ∂(prodBernoulli p), f ω = c := by
  have h01 : ∀ c : ℕ∞, prodBernoulli p {ω | f ω = c} = 0 ∨
      prodBernoulli p {ω | f ω = c} = 1 := fun c =>
    prodBernoulli_eq_zero_or_one_of_invariant p e hpres hsep
      (hf (measurableSet_singleton c)) fun n => by
        ext ω
        simp only [mem_preimage, mem_ofPred_eq, hinv]
  by_contra hne
  have hzero : ∀ c : ℕ∞, prodBernoulli p {ω | f ω = c} = 0 := by
    intro c
    refine (h01 c).resolve_right fun h1 => hne ⟨c, ?_⟩
    rw [ae_iff]
    have hc : MeasurableSet {ω | f ω = c} := hf (measurableSet_singleton c)
    have := prob_compl_eq_one_sub (μ := prodBernoulli p) hc
    rw [h1, tsub_self] at this
    exact this
  have : (Set.univ : Set (Set ι)) = ⋃ c : ℕ∞, {ω | f ω = c} := by
    ext ω
    simp
  have hu := measure_iUnion_null hzero
  rw [← this, measure_univ] at hu
  exact one_ne_zero hu

/-! ### A criterion for separation -/

/-- Separation holds when each coordinate is sent to each coordinate only finitely often. -/
theorem eventually_forall_notMem_of_finite (e : ℕ → ι ≃ ι)
    (he : ∀ i j : ι, {n | e n i = j}.Finite) (F G : Finset ι) :
    ∀ᶠ n in atTop, ∀ i ∈ F, e n i ∉ G := by
  have hfin : (⋃ i ∈ F, ⋃ j ∈ G, {n | e n i = j}).Finite :=
    F.finite_toSet.biUnion fun i _ => G.finite_toSet.biUnion fun j _ => he i j
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hfin.eventually_cofinite_notMem] with n hn i hi hj
  exact hn (Set.mem_biUnion hi (Set.mem_biUnion hj rfl))

/-- The law-preservation hypothesis holds when each relabelling preserves the profile. -/
theorem measurePreserving_image_of_invariant (p : ι → unitInterval) (e : ι ≃ ι)
    (hp : ∀ i, p (e i) = p i) :
    MeasurePreserving (fun ω : Set ι => e '' ω) (prodBernoulli p) (prodBernoulli p) :=
  ⟨measurable_image_equiv e, prodBernoulli_map_image_invariant p e hp⟩

/-! ### Non-vacuity -/

/-- Shifts of `ℤ` with any constant profile satisfy both hypotheses, so every shift-invariant
measurable event has probability `0` or `1`. -/
example (r : unitInterval) {A : Set (Set ℤ)} (hA : MeasurableSet A)
    (hinv : ∀ n : ℕ, (fun ω : Set ℤ => Equiv.addRight (n : ℤ) '' ω) ⁻¹' A = A) :
    prodBernoulli (fun _ : ℤ => r) A = 0 ∨ prodBernoulli (fun _ : ℤ => r) A = 1 :=
  prodBernoulli_eq_zero_or_one_of_invariant _ (fun n : ℕ => Equiv.addRight (n : ℤ))
    (fun n => measurePreserving_image_of_invariant _ _ fun _ => rfl)
    (eventually_forall_notMem_of_finite _ fun i j =>
      (Set.subsingleton_of_forall_eq (j - i).toNat fun n (hn : i + (n : ℤ) = j) => by
        omega).finite)
    hA hinv

/-- A concrete invariant event: some coordinate of `ℤ` is open. -/
example (r : unitInterval) :
    prodBernoulli (fun _ : ℤ => r) {ω : Set ℤ | ω.Nonempty} = 0 ∨
      prodBernoulli (fun _ : ℤ => r) {ω : Set ℤ | ω.Nonempty} = 1 := by
  refine prodBernoulli_eq_zero_or_one_of_invariant _ (fun n : ℕ => Equiv.addRight (n : ℤ))
    (fun n => measurePreserving_image_of_invariant _ _ fun _ => rfl)
    (eventually_forall_notMem_of_finite _ fun i j =>
      (Set.subsingleton_of_forall_eq (j - i).toNat fun n (hn : i + (n : ℤ) = j) => by
        omega).finite) ?_ fun n => ?_
  · have : {ω : Set ℤ | ω.Nonempty} = ⋃ i : ℤ, {ω | i ∈ ω} := by
      ext ω
      simp [Set.Nonempty]
    rw [this]
    exact MeasurableSet.iUnion fun i => measurableSet_mem i
  · ext ω
    simp only [mem_preimage, mem_ofPred_eq, Set.image_nonempty]

end PercLib.Probability

end
