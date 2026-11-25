/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Harris--FKG on the genuine countable independent-edge product law

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.2.1, p. 20:

  "if F(ω) and G(ω) are increasing functions of the percolation configuration then they are
   non-negatively correlated:  E F(ω)G(ω) ≥ E F(ω) E G(ω).  In particular, if A and B are two
   increasing events ... then P(A ∩ B) ≥ P(A)P(B)."

The repository already proves the *finite-witness* version (`edgeMeasure_fkg`, i.e. FKG for
increasing events that are finitely witnessed, hence cylinder events).  Harris--FKG for arbitrary
increasing **Borel** events does not follow from that by naive cylinder approximation: the `1`-cap
outer approximations of an increasing event can strictly increase its measure (take the event "some
sparse edge `e_k` is open"), and the `0`-cap inner approximations can lose it entirely (take "the
cluster is infinite" or "infinitely many edges are open").  Neither bound is a valid approximation.

This file closes that gap by a genuine finite-coordinate martingale argument, developed for the
general countable product law `prodLaw π = Measure.infinitePi (coordLaw π)` on `ι → Prop`
(`ι` any countable index type) and then specialized to the canonical model:

* `tailAvg π S A x` is the *explicit* conditional probability of `A` given the coordinates in `S`:
  the tail law of `{y | glue x y ∈ A}`.  `cylAvg π S A ω := tailAvg π S A (ω|_S)`.
* `map_pair_restrS`: the joint law of `(ω|_S, ω|_{S^c})` is the product of the two marginals
  (independence of disjoint coordinate blocks).
* `integral_prodLaw_glue`: Fubini change of variables along the gluing bijection.
* `integral_cylAvg_mul`: the tower (conditional-expectation) identity
  `∫ G·cylAvg_S A = ∫ G·1_A` for bounded measurable `G` depending only on the coordinates in `S`.
* `err π S A = ∫ |1_A − cylAvg_S A|`, and `ErrVanish` is the assertion that this error can be made
  arbitrarily small by enlarging `S`.  `errVanish_of_measurable` proves it for *every* measurable
  event by a Dynkin `π`-`λ` induction (`MeasurableSpace.induction_on_inter` over square cylinders),
  using the two-term estimate `err S A ≤ 2(μ A − μ B) + err S B` for `B ⊆ A` and the finite-union
  bound `err_biUnion_range_le`.
* `fkg_pi_bernoulli`: finite-product FKG for increasing functions on `(κ → Prop)`, obtained from
  Mathlib's Ahlswede--Daykin `fkg` through the repository's `expectation_mul_expectation_le`.
* `fkg_events`: **Harris--FKG for arbitrary increasing measurable events** on `prodLaw π`.
* `edgeMeasure_fkg_measurable`, `longRangeMeasure_fkg_measurable`: the same statement for the
  paper's law `P_β` on `Config V = Set (Sym2 V)`.

No `sorry`, no custom axioms.  The only inputs are Mathlib's product-measure/Fubini machinery and
the repository's finite Bernoulli FKG.
-/

module

public import PercLib.CriticalLRP.CylinderRusso
public import PercLib.CriticalLRP.CountableProduct.Marks
public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.BK.LayerCake

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped Topology
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

section Product

variable {ι : Type*} [Countable ι]

attribute [local instance] Classical.propDecidable

/-- The per-coordinate Bernoulli law. -/
noncomputable abbrev coordLaw (π : ι → unitInterval) : ι → Measure Prop :=
  fun i => bernoulliMeasure True False (π i)

/-- The countable independent product law on `ι → Prop`. -/
noncomputable abbrev prodLaw (π : ι → unitInterval) : Measure (ι → Prop) :=
  Measure.infinitePi (coordLaw π)

instance (π : ι → unitInterval) : IsProbabilityMeasure (prodLaw π) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (coordLaw π)))

/-- Restriction of a configuration to a coordinate set. -/
def restrS (S : Set ι) (ω : ι → Prop) : (i : ↥S) → Prop := fun i => ω ↑i

/-- Restriction of a configuration to the complement of a coordinate set. -/
def restrT (S : Set ι) (ω : ι → Prop) : (j : ↥(Sᶜ)) → Prop := fun j => ω ↑j

/-- Glue a configuration on `S` and one on `Sᶜ` into a configuration on `ι`. -/
def glueS (S : Set ι) (x : (i : ↥S) → Prop) (y : (j : ↥(Sᶜ)) → Prop) : ι → Prop :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else y ⟨i, by simpa using h⟩

theorem glueS_restrS (S : Set ι) (ω : ι → Prop) : glueS S (restrS S ω) (restrT S ω) = ω := by
  funext i
  by_cases h : i ∈ S
  · simp [glueS, restrS, h]
  · simp [glueS, restrT, h]

theorem measurable_restrS (S : Set ι) : Measurable (restrS S) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply _

theorem measurable_restrT (S : Set ι) : Measurable (restrT S) :=
  measurable_pi_iff.mpr fun j => measurable_pi_apply _

theorem measurable_glueS (S : Set ι) :
    Measurable fun p : ((i : ↥S) → Prop) × ((j : ↥(Sᶜ)) → Prop) => glueS S p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i ∈ S
  · simp only [glueS, dite_eq_left h]
    exact (measurable_pi_apply (⟨i, h⟩ : ↥S)).comp measurable_fst
  · simp only [glueS, dite_eq_right h]
    exact (measurable_pi_apply (⟨i, by simpa using h⟩ : ↥(Sᶜ))).comp measurable_snd

/-- **Joint law of the two restrictions.** The restrictions of the product configuration to
`S` and to `Sᶜ` are independent, with laws the corresponding product measures. -/
theorem map_pair_restrS (π : ι → unitInterval) (S : Set ι) :
    (prodLaw π).map (fun ω => (restrS S ω, restrT S ω)) =
      (Measure.infinitePi (fun i : S => coordLaw π i)).prod
        (Measure.infinitePi (fun j : ↥(Sᶜ) => coordLaw π j)) := by
  have h_ind : IndepFun (restrS S) (restrT S) (prodLaw π) := by
    have h := (iIndepFun_infinitePi (P := coordLaw π) (X := fun _ (q : Prop) => q)
      (fun _ => by fun_prop)).indepFun_set S Sᶜ disjoint_compl_right
      (fun _ => by fun_prop)
    exact h
  have hmap := h_ind.map_prod_eq_prod_map_map (measurable_restrS S).aemeasurable
    (measurable_restrT S).aemeasurable
  rw [hmap]
  congr 1
  · exact Measure.map_infinitePi_infinitePi_of_inj (P := coordLaw π) (f := Subtype.val)
      Subtype.val_injective
  · exact Measure.map_infinitePi_infinitePi_of_inj (P := coordLaw π) (f := Subtype.val)
      Subtype.val_injective


/-! ## Tail averaging -/

/-- The tail law on the complement of a coordinate set. -/
noncomputable abbrev tailLaw (π : ι → unitInterval) (S : Set ι) : Measure ((j : ↥(Sᶜ)) → Prop) :=
  Measure.infinitePi (fun j : ↥(Sᶜ) => coordLaw π j)

instance (π : ι → unitInterval) (S : Set ι) : IsProbabilityMeasure (tailLaw π S) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun j : ↥(Sᶜ) => coordLaw π j)))

/-- The tail event that the glued configuration lies in `A`. -/
def tailSet (S : Set ι) (A : Set (ι → Prop)) (x : (i : ↥S) → Prop) :
    Set ((j : ↥(Sᶜ)) → Prop) :=
  {y | glueS S x y ∈ A}

/-- The conditional probability of `A` given the coordinates in `S`. -/
noncomputable def tailAvg (π : ι → unitInterval) (S : Set ι) (A : Set (ι → Prop))
    (x : (i : ↥S) → Prop) : ℝ :=
  (tailLaw π S).real (tailSet S A x)

theorem tailAvg_nonneg (π : ι → unitInterval) (S : Set ι) (A : Set (ι → Prop))
    (x : (i : ↥S) → Prop) : 0 ≤ tailAvg π S A x :=
  measureReal_nonneg

theorem measureReal_univ_prob {α : Type*} {m : MeasurableSpace α} (μ : Measure α)
    [IsProbabilityMeasure μ] : μ.real (Set.univ : Set α) = 1 := by
  simp [Measure.real]

theorem tailAvg_le_one (π : ι → unitInterval) (S : Set ι) (A : Set (ι → Prop))
    (x : (i : ↥S) → Prop) : tailAvg π S A x ≤ 1 := by
  have h : (tailLaw π S).real (tailSet S A x) ≤ (tailLaw π S).real Set.univ :=
    measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
  rwa [measureReal_univ_prob] at h

theorem tailAvg_mono (π : ι → unitInterval) (S : Set ι) {A B : Set (ι → Prop)} (hAB : A ⊆ B)
    (x : (i : ↥S) → Prop) : tailAvg π S A x ≤ tailAvg π S B x :=
  measureReal_mono (fun y hy => hAB hy) (measure_ne_top _ _)

theorem measurable_glueS_right (S : Set ι) (x : (i : ↥S) → Prop) :
    Measurable fun y : (j : ↥(Sᶜ)) → Prop => glueS S x y := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i ∈ S
  · simp only [glueS, dite_eq_left h]; exact measurable_const
  · simp only [glueS, dite_eq_right h]; exact measurable_pi_apply _

theorem measurableSet_tailSet (S : Set ι) {A : Set (ι → Prop)} (hA : MeasurableSet A)
    (x : (i : ↥S) → Prop) : MeasurableSet (tailSet S A x) :=
  hA.preimage (measurable_glueS_right S x)

theorem tailAvg_compl (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) (x : (i : ↥S) → Prop) :
    tailAvg π S Aᶜ x = 1 - tailAvg π S A x := by
  have hm := measurableSet_tailSet S hA x
  have hsum : (tailLaw π S).real (tailSet S Aᶜ x) + (tailLaw π S).real (tailSet S A x) = 1 := by
    have h := measureReal_add_measureReal_compl (μ := tailLaw π S) hm
    rw [measureReal_univ_prob] at h
    have hc : tailSet S Aᶜ x = (tailSet S A x)ᶜ := by
      ext y; simp [tailSet]
    rw [← hc] at h
    linarith
  simp only [tailAvg]
  linarith


theorem tailAvg_union (π : ι → unitInterval) (S : Set ι) {A B : Set (ι → Prop)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hdisj : Disjoint A B)
    (x : (i : ↥S) → Prop) :
    tailAvg π S (A ∪ B) x = tailAvg π S A x + tailAvg π S B x := by
  have hAB : tailSet S (A ∪ B) x = tailSet S A x ∪ tailSet S B x := by
    ext y; simp [tailSet]
  have hd : Disjoint (tailSet S A x) (tailSet S B x) := by
    rw [Set.disjoint_left]
    intro y hy hyB
    exact (Set.disjoint_left.mp hdisj hy) hyB
  rw [tailAvg, hAB, measureReal_union hd (measurableSet_tailSet S hB x)
    (measure_ne_top _ _) (measure_ne_top _ _)]
  rfl

theorem measurable_tailAvg (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) : Measurable (tailAvg π S A) := by
  have hmeas : MeasurableSet
      {p : ((i : ↥S) → Prop) × ((j : ↥(Sᶜ)) → Prop) | glueS S p.1 p.2 ∈ A} :=
    hA.preimage (measurable_glueS S)
  have key : Measurable fun x : (i : ↥S) → Prop =>
      (tailLaw π S) {y : (j : ↥(Sᶜ)) → Prop | glueS S x y ∈ A} := by
    have hlint : Measurable fun x : (i : ↥S) → Prop =>
        ∫⁻ y, (if glueS S x y ∈ A then (1 : ℝ≥0∞) else 0) ∂(tailLaw π S) :=
      Measurable.lintegral_prod_right (ν := tailLaw π S)
        (f := fun (x : (i : ↥S) → Prop) (y : (j : ↥(Sᶜ)) → Prop) =>
          if glueS S x y ∈ A then (1 : ℝ≥0∞) else 0) (by
          refine Measurable.ite ?_ measurable_const measurable_const
          exact hmeas)
    convert hlint using 1
    ext x
    exact (lintegral_indicator_one (measurableSet_tailSet S hA x)).symm
  exact key.ennreal_toReal

/-- Cylinder average: the conditional probability of `A` given the coordinates in `S`. -/
noncomputable def cylAvg (π : ι → unitInterval) (S : Set ι) (A : Set (ι → Prop))
    (ω : ι → Prop) : ℝ :=
  tailAvg π S A (restrS S ω)

theorem measurable_cylAvg (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) : Measurable (cylAvg π S A) :=
  (measurable_tailAvg π S hA).comp (measurable_restrS S)

theorem cylAvg_nonneg (π : ι → unitInterval) (S : Set ι) (A : Set (ι → Prop))
    (ω : ι → Prop) : 0 ≤ cylAvg π S A ω := tailAvg_nonneg π S A _

theorem cylAvg_le_one (π : ι → unitInterval) (S : Set ι) (A : Set (ι → Prop))
    (ω : ι → Prop) : cylAvg π S A ω ≤ 1 := tailAvg_le_one π S A _

theorem cylAvg_mono (π : ι → unitInterval) (S : Set ι) {A B : Set (ι → Prop)} (hAB : A ⊆ B)
    (ω : ι → Prop) : cylAvg π S A ω ≤ cylAvg π S B ω := tailAvg_mono π S hAB _


/-- The head law on a coordinate set. -/
noncomputable abbrev headLaw (π : ι → unitInterval) (S : Set ι) : Measure ((i : ↥S) → Prop) :=
  Measure.infinitePi (fun i : ↥S => coordLaw π i)

instance (π : ι → unitInterval) (S : Set ι) : IsProbabilityMeasure (headLaw π S) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun i : ↥S => coordLaw π i)))

theorem restrS_glueS (S : Set ι) (x : (i : ↥S) → Prop) (y : (j : ↥(Sᶜ)) → Prop) :
    restrS S (glueS S x y) = x := by
  funext i
  simp [restrS, glueS, i.2]

theorem restrT_glueS (S : Set ι) (x : (i : ↥S) → Prop) (y : (j : ↥(Sᶜ)) → Prop) :
    restrT S (glueS S x y) = y := by
  funext j
  have hj : ¬ (↑j ∈ S) := j.2
  simp [restrT, glueS, hj]

theorem integrable_of_abs_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hm : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

theorem integrable_of_abs_le_one {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hm : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    Integrable f μ :=
  integrable_of_abs_le hm hb

/-- **Fubini formula for the product law**: integrating over the product configuration is the
same as first sampling the coordinates in `S`, then the ones outside. -/
theorem integral_prodLaw_glue (π : ι → unitInterval) (S : Set ι) {F : (ι → Prop) → ℝ}
    (hFm : Measurable F) (hFb : ∀ ω, |F ω| ≤ 1) :
    ∫ ω, F ω ∂(prodLaw π)
      = ∫ x, ∫ y, F (glueS S x y) ∂(tailLaw π S) ∂(headLaw π S) := by
  classical
  have hmap : Measurable fun ω : ι → Prop => (restrS S ω, restrT S ω) :=
    (measurable_restrS S).prodMk (measurable_restrT S)
  have hFint : Integrable F (prodLaw π) := integrable_of_abs_le_one hFm hFb
  have hFcomp : ∀ p : ((i : ↥S) → Prop) × ((j : ↥(Sᶜ)) → Prop),
      |F (glueS S p.1 p.2)| ≤ 1 := fun p => hFb _
  have hFcompm : Measurable fun p : ((i : ↥S) → Prop) × ((j : ↥(Sᶜ)) → Prop) =>
      F (glueS S p.1 p.2) := hFm.comp (measurable_glueS S)
  have hFprod : Integrable (fun p : ((i : ↥S) → Prop) × ((j : ↥(Sᶜ)) → Prop) =>
      F (glueS S p.1 p.2)) ((headLaw π S).prod (tailLaw π S)) :=
    integrable_of_abs_le_one hFcompm hFcomp
  calc ∫ ω, F ω ∂(prodLaw π)
      = ∫ ω, F (glueS S (restrS S ω) (restrT S ω)) ∂(prodLaw π) := by
        simp only [glueS_restrS]
    _ = ∫ p, F (glueS S p.1 p.2) ∂((prodLaw π).map fun ω => (restrS S ω, restrT S ω)) :=
        (integral_map hmap.aemeasurable (hFm.comp (measurable_glueS S)).aestronglyMeasurable).symm
    _ = ∫ p, F (glueS S p.1 p.2) ∂((headLaw π S).prod (tailLaw π S)) := by
        rw [map_pair_restrS]
    _ = ∫ x, ∫ y, F (glueS S x y) ∂(tailLaw π S) ∂(headLaw π S) :=
        integral_prod _ hFprod

/-- The tail average as a Bochner integral. -/
theorem tailAvg_eq_integral (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) (x : (i : ↥S) → Prop) :
    tailAvg π S A x
      = ∫ y, (if glueS S x y ∈ A then (1 : ℝ) else 0) ∂(tailLaw π S) := by
  have hm := measurableSet_tailSet S hA x
  rw [tailAvg, ← integral_indicator_one hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : glueS S x y ∈ A <;> simp [tailSet, Set.indicator, hy]


/-- **Tower (conditional-expectation) identity** for the cylinder average. -/
theorem integral_cylAvg_mul (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) {G : (ι → Prop) → ℝ} (hGm : Measurable G)
    (hG0 : ∀ ω, 0 ≤ G ω) (hG1 : ∀ ω, G ω ≤ 1)
    (hGc : ∃ Gx : ((i : ↥S) → Prop) → ℝ, ∀ (x y), G (glueS S x y) = Gx x) :
    ∫ ω, G ω * cylAvg π S A ω ∂(prodLaw π)
      = ∫ ω, G ω * (if ω ∈ A then (1 : ℝ) else 0) ∂(prodLaw π) := by
  classical
  obtain ⟨Gx, hGx⟩ := hGc
  have hfact : ∀ (x : (i : ↥S) → Prop) (y : (j : ↥(Sᶜ)) → Prop),
      G (glueS S x y) * cylAvg π S A (glueS S x y) = Gx x * tailAvg π S A x := by
    intro x y
    rw [hGx x y, cylAvg, restrS_glueS]
  have hfact2 : ∀ (x : (i : ↥S) → Prop) (y : (j : ↥(Sᶜ)) → Prop),
      G (glueS S x y) * (if glueS S x y ∈ A then (1 : ℝ) else 0)
        = Gx x * (if glueS S x y ∈ A then (1 : ℝ) else 0) := by
    intro x y; rw [hGx x y]
  have hFA : ∀ ω, |G ω * cylAvg π S A ω| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (mul_nonneg (hG0 ω) (cylAvg_nonneg π S A ω))]
    calc G ω * cylAvg π S A ω ≤ 1 * 1 := by
          exact mul_le_mul (hG1 ω) (cylAvg_le_one π S A ω) (cylAvg_nonneg π S A ω) zero_le_one
      _ = 1 := one_mul 1
  have hFB : ∀ ω, |G ω * (if ω ∈ A then (1 : ℝ) else 0)| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (mul_nonneg (hG0 ω) (by split <;> norm_num))]
    calc G ω * (if ω ∈ A then (1 : ℝ) else 0) ≤ 1 * 1 := by
          refine mul_le_mul (hG1 ω) ?_ ?_ zero_le_one
          · split <;> norm_num
          · split <;> norm_num
      _ = 1 := one_mul 1
  have hFAm : Measurable fun ω => G ω * cylAvg π S A ω := hGm.mul (measurable_cylAvg π S hA)
  have hFBm : Measurable fun ω => G ω * (if ω ∈ A then (1 : ℝ) else 0) :=
    hGm.mul (Measurable.ite hA measurable_const measurable_const)
  calc ∫ ω, G ω * cylAvg π S A ω ∂(prodLaw π)
      = ∫ x, ∫ y, G (glueS S x y) * cylAvg π S A (glueS S x y)
          ∂(tailLaw π S) ∂(headLaw π S) := integral_prodLaw_glue π S hFAm hFA
    _ = ∫ x, ∫ y, Gx x * tailAvg π S A x ∂(tailLaw π S) ∂(headLaw π S) := by
        simp only [hfact]
    _ = ∫ x, Gx x * tailAvg π S A x ∂(headLaw π S) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [integral_const]
    _ = ∫ x, Gx x * (∫ y, (if glueS S x y ∈ A then (1 : ℝ) else 0) ∂(tailLaw π S))
          ∂(headLaw π S) := by
        simp only [tailAvg_eq_integral π S hA]
    _ = ∫ x, ∫ y, Gx x * (if glueS S x y ∈ A then (1 : ℝ) else 0)
          ∂(tailLaw π S) ∂(headLaw π S) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ x, ∫ y, G (glueS S x y) * (if glueS S x y ∈ A then (1 : ℝ) else 0)
          ∂(tailLaw π S) ∂(headLaw π S) := by
        simp only [hfact2]
    _ = ∫ ω, G ω * (if ω ∈ A then (1 : ℝ) else 0) ∂(prodLaw π) :=
        (integral_prodLaw_glue π S hFBm hFB).symm


theorem cylAvg_union (π : ι → unitInterval) (S : Set ι) {A B : Set (ι → Prop)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hdisj : Disjoint A B) (ω : ι → Prop) :
    cylAvg π S (A ∪ B) ω = cylAvg π S A ω + cylAvg π S B ω :=
  tailAvg_union π S hA hB hdisj _

theorem cylAvg_compl (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) (ω : ι → Prop) : cylAvg π S Aᶜ ω = 1 - cylAvg π S A ω :=
  tailAvg_compl π S hA _


/-- Cylinder average of a cylinder event is its indicator. -/
theorem cylAvg_cylinder (π : ι → unitInterval) (S T : Finset ι) (hTS : ↑T ⊆ (↑S : Set ι))
    (t : ι → Set Prop) (ω : ι → Prop) :
    cylAvg π (↑S : Set ι) ((T : Set ι).pi t) ω
      = if ω ∈ (T : Set ι).pi t then 1 else 0 := by
  classical
  have hx : ∀ y : (j : ↥((↑S : Set ι)ᶜ)) → Prop,
      (glueS (↑S : Set ι) (restrS (↑S : Set ι) ω) y ∈ (T : Set ι).pi t
        ↔ ω ∈ (T : Set ι).pi t) := by
    intro y
    simp only [Set.mem_pi]
    constructor
    · intro h i hi
      have hiS : i ∈ S := hTS (by simpa using hi)
      have := h i hi
      simpa [glueS, restrS, hiS] using this
    · intro h i hi
      have hiS : i ∈ S := hTS (by simpa using hi)
      simpa [glueS, restrS, hiS] using h i hi
  rw [cylAvg, tailAvg]
  by_cases hω : ω ∈ (T : Set ι).pi t
  · have huniv : tailSet (↑S : Set ι) ((T : Set ι).pi t) (restrS (↑S : Set ι) ω) = Set.univ := by
      ext y; simp only [tailSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hx y |>.mpr hω
    rw [huniv, measureReal_univ_prob, ite_eq_left hω]
  · have hempty : tailSet (↑S : Set ι) ((T : Set ι).pi t) (restrS (↑S : Set ι) ω) = ∅ := by
      ext y; simp only [tailSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hh => hω (hx y |>.mp hh)
    rw [hempty, measureReal_empty, ite_eq_right hω]

/-- The indicator of an event as a real-valued function (with a fixed `Decidable` instance). -/
noncomputable def indSet (A : Set (ι → Prop)) : (ι → Prop) → ℝ :=
  A.indicator (fun _ => (1 : ℝ))

theorem indSet_apply (A : Set (ι → Prop)) (ω : ι → Prop) :
    indSet A ω = if ω ∈ A then (1 : ℝ) else 0 :=
  rfl

theorem indSet_union_of_disjoint {A B : Set (ι → Prop)} (h : Disjoint A B) (ω : ι → Prop) :
    indSet (A ∪ B) ω = indSet A ω + indSet B ω := by
  by_cases ha : ω ∈ A
  · have hb : ω ∉ B := fun hb => (Set.disjoint_left.mp h ha) hb
    simp [indSet, Set.indicator, ha, hb]
  · by_cases hb : ω ∈ B
    · simp [indSet, Set.indicator, ha, hb]
    · have hu : ω ∉ A ∪ B := fun hu => hu.elim ha hb
      simp [indSet, Set.indicator, ha, hb, hu]

/-- The `L¹` error of the cylinder average at coordinate set `S`. -/
noncomputable def err (π : ι → unitInterval) (S : Finset ι) (A : Set (ι → Prop)) : ℝ :=
  ∫ ω, |indSet A ω - cylAvg π (↑S : Set ι) A ω| ∂(prodLaw π)

theorem err_zero_of_cylinder (π : ι → unitInterval) (T : Finset ι) (t : ι → Set Prop) :
    err π T ((T : Set ι).pi t) = 0 := by
  have h : ∀ ω : ι → Prop,
      |indSet ((T : Set ι).pi t) ω - cylAvg π (↑T : Set ι) ((T : Set ι).pi t) ω|
        = 0 := by
    intro ω
    rw [cylAvg_cylinder π T T (by simp) t ω]
    by_cases hω : ω ∈ (T : Set ι).pi t
    · rw [ite_eq_left hω, indSet_apply, ite_eq_left hω]; ring
    · rw [ite_eq_right hω, indSet_apply, ite_eq_right hω]; ring
  simp only [err, h]
  exact integral_zero _ _


/-- The cylinder average of the empty event vanishes. -/
theorem cylAvg_empty (π : ι → unitInterval) (S : Set ι) (ω : ι → Prop) :
    cylAvg π S (∅ : Set (ι → Prop)) ω = 0 := by
  have h : tailSet S (∅ : Set (ι → Prop)) (restrS S ω) = ∅ := by
    ext y; simp [tailSet]
  simp [cylAvg, tailAvg, h]

theorem err_nonneg (π : ι → unitInterval) (S : Finset ι) (A : Set (ι → Prop)) :
    0 ≤ err π S A := integral_nonneg fun _ => abs_nonneg _

theorem abs_indicator_sub_cylAvg_le_one (π : ι → unitInterval) (S : Finset ι) {A : Set (ι → Prop)}
    (ω : ι → Prop) :
    |indSet A ω - cylAvg π (↑S : Set ι) A ω| ≤ 1 := by
  have h0 : (0:ℝ) ≤ cylAvg π (↑S : Set ι) A ω := cylAvg_nonneg π _ A ω
  have h1 : cylAvg π (↑S : Set ι) A ω ≤ 1 := cylAvg_le_one π _ A ω
  rw [abs_le]
  have := indSet_apply A ω
  constructor
  · by_cases h : ω ∈ A
    · rw [this, ite_eq_left h]; simp; linarith
    · rw [this, ite_eq_right h]; simp; linarith
  · by_cases h : ω ∈ A
    · rw [this, ite_eq_left h]; simp; linarith
    · rw [this, ite_eq_right h]; simp; linarith

theorem integrable_err_integrand (π : ι → unitInterval) (S : Finset ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) :
    Integrable (fun ω => |indSet A ω - cylAvg π (↑S : Set ι) A ω|)
      (prodLaw π) :=
  integrable_of_abs_le_one
    (((Measurable.ite hA measurable_const measurable_const).sub (measurable_cylAvg π _ hA)).abs)
    (fun ω => by rw [abs_abs]; exact abs_indicator_sub_cylAvg_le_one π S ω)

/-- The cylinder average of a measurable event integrates to the probability of the event. -/
theorem integral_cylAvg (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) :
    ∫ ω, cylAvg π S A ω ∂(prodLaw π) = (prodLaw π).real A := by
  have h := integral_cylAvg_mul π S hA (G := fun _ => (1 : ℝ)) measurable_const
    (fun _ => zero_le_one) (fun _ => le_refl 1) ⟨fun _ => 1, fun x y => rfl⟩
  simp only [one_mul] at h
  rw [h, ← integral_indicator_one hA]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]

/-- Reflection invariance of the error under complements. -/
theorem err_compl (π : ι → unitInterval) (S : Finset ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) : err π S Aᶜ = err π S A := by
  simp only [err]
  apply integral_congr_ae
  filter_upwards with ω
  rw [cylAvg_compl (π := π) (S := (↑S : Set ι)) (A := A) hA]
  rw [indSet_apply Aᶜ ω, indSet_apply A ω]
  by_cases h : ω ∈ A
  · have h' : ω ∉ Aᶜ := by simpa [Set.mem_compl_iff] using h
    rw [ite_eq_right h', ite_eq_left h, zero_sub, abs_neg]
  · have h' : ω ∈ Aᶜ := by simpa [Set.mem_compl_iff] using h
    rw [ite_eq_left h', ite_eq_right h, zero_sub, abs_neg,
      show (1 : ℝ) - (1 - cylAvg π (↑S : Set ι) A ω) = cylAvg π (↑S : Set ι) A ω by ring]


theorem err_union_le (π : ι → unitInterval) (S : Finset ι) {A B : Set (ι → Prop)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hdisj : Disjoint A B) :
    err π S (A ∪ B) ≤ err π S A + err π S B := by
  classical
  have hAB : MeasurableSet (A ∪ B) := hA.union hB
  have hpt : ∀ ω, |indSet (A ∪ B) ω - cylAvg π (↑S : Set ι) (A ∪ B) ω|
      ≤ |indSet A ω - cylAvg π (↑S : Set ι) A ω|
        + |indSet B ω - cylAvg π (↑S : Set ι) B ω| := by
    intro ω
    have h1 : indSet (A ∪ B) ω = indSet A ω + indSet B ω := indSet_union_of_disjoint hdisj ω
    rw [h1, cylAvg_union π (↑S : Set ι) hA hB hdisj]
    have h2 : indSet A ω + indSet B ω
        - (cylAvg π (↑S : Set ι) A ω + cylAvg π (↑S : Set ι) B ω)
        = (indSet A ω - cylAvg π (↑S : Set ι) A ω)
          + (indSet B ω - cylAvg π (↑S : Set ι) B ω) := by ring
    rw [h2]
    exact abs_add_le _ _
  have hInt : Integrable (fun ω => |indSet A ω - cylAvg π (↑S : Set ι) A ω|
      + |indSet B ω - cylAvg π (↑S : Set ι) B ω|) (prodLaw π) :=
    (integrable_err_integrand π S hA).add (integrable_err_integrand π S hB)
  calc err π S (A ∪ B)
      = ∫ ω, |indSet (A ∪ B) ω - cylAvg π (↑S : Set ι) (A ∪ B) ω|
          ∂(prodLaw π) := rfl
    _ ≤ ∫ ω, (|indSet A ω - cylAvg π (↑S : Set ι) A ω|
          + |indSet B ω - cylAvg π (↑S : Set ι) B ω|) ∂(prodLaw π) :=
        integral_mono (integrable_err_integrand π S hAB) hInt hpt
    _ = err π S A + err π S B := by
        rw [integral_add (integrable_err_integrand π S hA) (integrable_err_integrand π S hB)]
        rfl


theorem measurable_indSet {A : Set (ι → Prop)} (hA : MeasurableSet A) : Measurable (indSet A) := by
  rw [indSet]
  exact measurable_const.indicator hA

theorem abs_sub_le_one_of_mem_Icc {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : |a - b| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith

theorem err_empty (π : ι → unitInterval) (S : Finset ι) : err π S ∅ = 0 := by
  have h : ∀ ω : ι → Prop, |indSet (∅ : Set (ι → Prop)) ω - cylAvg π (↑S : Set ι) ∅ ω| = 0 := by
    intro ω
    rw [cylAvg_empty, indSet_apply]
    simp
  simp only [err, h]
  exact integral_zero _ _

/-- The error vanishes on cylinder events once the coordinate set contains their support. -/
theorem err_cylinder (π : ι → unitInterval) (S T : Finset ι) (hTS : T ⊆ S) (t : ι → Set Prop) :
    err π S ((T : Set ι).pi t) = 0 := by
  have h : ∀ ω : ι → Prop,
      |indSet ((T : Set ι).pi t) ω - cylAvg π (↑S : Set ι) ((T : Set ι).pi t) ω| = 0 := by
    intro ω
    rw [cylAvg_cylinder π S T (by simpa using hTS) t ω]
    by_cases hω : ω ∈ (T : Set ι).pi t
    · rw [ite_eq_left hω, indSet_apply, ite_eq_left hω]; ring
    · rw [ite_eq_right hω, indSet_apply, ite_eq_right hω]; ring
  simp only [err, h]
  exact integral_zero _ _

theorem integral_indSet (π : ι → unitInterval) {A : Set (ι → Prop)} (hA : MeasurableSet A) :
    ∫ ω, indSet A ω ∂(prodLaw π) = (prodLaw π).real A := by
  rw [indSet]
  exact integral_indicator_one hA

theorem integrable_cylAvg (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) : Integrable (cylAvg π S A) (prodLaw π) :=
  integrable_of_abs_le_one (measurable_cylAvg π S hA) (fun ω => by
    rw [abs_of_nonneg (cylAvg_nonneg π S A ω)]
    exact cylAvg_le_one π S A ω)

theorem integral_add_three {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {F1 F2 F3 : α → ℝ} (h1 : Integrable F1 μ) (h2 : Integrable F2 μ) (h3 : Integrable F3 μ) :
    ∫ ω, F1 ω + F2 ω + F3 ω ∂μ = ∫ ω, F1 ω ∂μ + ∫ ω, F2 ω ∂μ + ∫ ω, F3 ω ∂μ := by
  have c1 : ∫ ω, (F1 ω + F2 ω) ∂μ = ∫ ω, F1 ω ∂μ + ∫ ω, F2 ω ∂μ := integral_add h1 h2
  have c2 : ∫ ω, ((F1 ω + F2 ω) + F3 ω) ∂μ = ∫ ω, (F1 ω + F2 ω) ∂μ + ∫ ω, F3 ω ∂μ :=
    integral_add (h1.add h2) h3
  rw [show ∫ ω, F1 ω + F2 ω + F3 ω ∂μ = ∫ ω, ((F1 ω + F2 ω) + F3 ω) ∂μ from rfl, c2, c1]

/-- The two-term estimate: passing from `B ⊆ A` to `A` costs twice the measure gap. -/
theorem err_le_of_subset (π : ι → unitInterval) (S : Finset ι) {B A : Set (ι → Prop)}
    (hB : MeasurableSet B) (hA : MeasurableSet A) (hBA : B ⊆ A) :
    err π S A ≤ 2 * ((prodLaw π).real A - (prodLaw π).real B) + err π S B := by
  have hsub : ∀ ω : ι → Prop, indSet B ω ≤ indSet A ω := by
    intro ω
    rw [indSet_apply B ω, indSet_apply A ω]
    by_cases h : ω ∈ B
    · rw [ite_eq_left h, ite_eq_left (hBA h)]
    · rw [ite_eq_right h]; split <;> norm_num
  have hsubc : ∀ ω : ι → Prop, cylAvg π (↑S : Set ι) B ω ≤ cylAvg π (↑S : Set ι) A ω :=
    fun ω => cylAvg_mono π _ hBA ω
  -- pointwise three-term bound
  have hpt : ∀ ω, |indSet A ω - cylAvg π (↑S : Set ι) A ω|
      ≤ |indSet A ω - indSet B ω| + |indSet B ω - cylAvg π (↑S : Set ι) B ω|
        + |cylAvg π (↑S : Set ι) B ω - cylAvg π (↑S : Set ι) A ω| := by
    intro ω
    have h : indSet A ω - cylAvg π (↑S : Set ι) A ω
        = (indSet A ω - indSet B ω) + (indSet B ω - cylAvg π (↑S : Set ι) B ω)
          + (cylAvg π (↑S : Set ι) B ω - cylAvg π (↑S : Set ι) A ω) := by ring
    rw [h]
    exact abs_add_three _ _ _
  -- integrability
  have hmA := measurable_indSet hA
  have hmB := measurable_indSet hB
  have hS : ∀ (C : Set (ι → Prop)), MeasurableSet C →
      Integrable (fun ω => |indSet C ω - cylAvg π (↑S : Set ι) C ω|) (prodLaw π) :=
    fun C hC => integrable_err_integrand π S hC
  have hind01 : ∀ (C : Set (ι → Prop)) (ω : ι → Prop), 0 ≤ indSet C ω ∧ indSet C ω ≤ 1 := by
    intro C ω; rw [indSet_apply C ω]; split <;> norm_num
  have h1 : Integrable (fun ω => |indSet A ω - indSet B ω|) (prodLaw π) :=
    integrable_of_abs_le_one ((hmA.sub hmB).abs) (fun ω => by
      rw [abs_abs]
      exact abs_sub_le_one_of_mem_Icc (hind01 A ω).1 (hind01 A ω).2 (hind01 B ω).1 (hind01 B ω).2)
  have h3 : Integrable (fun ω => |cylAvg π (↑S : Set ι) B ω - cylAvg π (↑S : Set ι) A ω|)
      (prodLaw π) :=
    integrable_of_abs_le_one (((measurable_cylAvg π _ hB).sub (measurable_cylAvg π _ hA)).abs)
      (fun ω => by
        rw [abs_abs]
        exact abs_sub_le_one_of_mem_Icc (cylAvg_nonneg π _ B ω) (cylAvg_le_one π _ B ω)
          (cylAvg_nonneg π _ A ω) (cylAvg_le_one π _ A ω))
  -- value of the first and third integral
  have hval1 : ∫ ω, |indSet A ω - indSet B ω| ∂(prodLaw π)
      = (prodLaw π).real A - (prodLaw π).real B := by
    have hEq : ∀ ω, |indSet A ω - indSet B ω| = indSet A ω - indSet B ω := by
      intro ω
      have hle : 0 ≤ indSet A ω - indSet B ω := by linarith [hsub ω]
      rw [abs_of_nonneg hle]
    rw [funext hEq, integral_sub (integrable_of_abs_le_one (measurable_indSet hA) (fun ω => by
        rw [indSet_apply]; split <;> norm_num))
      (integrable_of_abs_le_one (measurable_indSet hB) (fun ω => by
        rw [indSet_apply]; split <;> norm_num))]
    rw [integral_indSet (π := π) (A := A) hA, integral_indSet (π := π) (A := B) hB]
  have hval3 : ∫ ω, |cylAvg π (↑S : Set ι) B ω - cylAvg π (↑S : Set ι) A ω| ∂(prodLaw π)
      = (prodLaw π).real A - (prodLaw π).real B := by
    have hEq : ∀ ω, |cylAvg π (↑S : Set ι) B ω - cylAvg π (↑S : Set ι) A ω|
        = cylAvg π (↑S : Set ι) A ω - cylAvg π (↑S : Set ι) B ω := by
      intro ω
      have hle : cylAvg π (↑S : Set ι) B ω - cylAvg π (↑S : Set ι) A ω ≤ 0 := by linarith [hsubc ω]
      rw [abs_of_nonpos hle]
      ring
    rw [funext hEq, integral_sub (integrable_cylAvg π S hA) (integrable_cylAvg π S hB),
      integral_cylAvg π _ hA, integral_cylAvg π _ hB]
  calc err π S A
      = ∫ ω, |indSet A ω - cylAvg π (↑S : Set ι) A ω| ∂(prodLaw π) := rfl
    _ ≤ ∫ ω, (|indSet A ω - indSet B ω| + |indSet B ω - cylAvg π (↑S : Set ι) B ω|
          + |cylAvg π (↑S : Set ι) B ω - cylAvg π (↑S : Set ι) A ω|) ∂(prodLaw π) :=
        integral_mono (hS A hA) ((h1.add (hS B hB)).add h3) hpt
    _ = (prodLaw π).real A - (prodLaw π).real B + err π S B
          + ((prodLaw π).real A - (prodLaw π).real B) := by
        have hstep := integral_add_three (μ := prodLaw π) h1 (hS B hB) h3
        rw [hstep, hval1, hval3]
        rfl
    _ = 2 * ((prodLaw π).real A - (prodLaw π).real B) + err π S B := by ring


theorem err_biUnion_range_le (π : ι → unitInterval) (S : Finset ι) (f : ℕ → Set (ι → Prop))
    (hmeas : ∀ i, MeasurableSet (f i)) (hdisj : Pairwise fun i j => Disjoint (f i) (f j)) (n : ℕ) :
    err π S (⋃ i ∈ Finset.range n, f i) ≤ ∑ i ∈ Finset.range n, err π S (f i) := by
  induction n with
  | zero => simp [err_empty]
  | succ n ih =>
    have h1 : (⋃ i ∈ Finset.range (n + 1), f i) = (⋃ i ∈ Finset.range n, f i) ∪ f n := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert]
      exact Set.union_comm _ _
    have hdj : Disjoint (⋃ i ∈ Finset.range n, f i) (f n) := by
      rw [Set.disjoint_left]
      intro ω hω hωn
      simp only [Set.mem_iUnion, Finset.mem_range] at hω
      obtain ⟨i, hi, hωi⟩ := hω
      exact (Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hi)) hωi) hωn
    have hmB : MeasurableSet (⋃ i ∈ Finset.range n, f i) :=
      MeasurableSet.biUnion (Finset.countable_toSet _) (fun i _ => hmeas i)
    rw [h1, Finset.sum_range_succ]
    calc err π S ((⋃ i ∈ Finset.range n, f i) ∪ f n)
        ≤ err π S (⋃ i ∈ Finset.range n, f i) + err π S (f n) :=
          err_union_le π S hmB (hmeas n) hdj
      _ ≤ (∑ i ∈ Finset.range n, err π S (f i)) + err π S (f n) := by linarith


/-- The Dynkin-style property: the cylinder-average error can be made arbitrarily small by
enlarging the coordinate set. -/
def ErrVanish (π : ι → unitInterval) (A : Set (ι → Prop)) : Prop :=
  ∀ ε > 0, ∃ S₀ : Finset ι, ∀ S : Finset ι, S₀ ⊆ S → err π S A < ε

theorem errVanish_empty (π : ι → unitInterval) : ErrVanish π ∅ := by
  intro ε hε
  exact ⟨∅, fun S _ => by rw [err_empty]; exact hε⟩

theorem errVanish_cylinder (π : ι → unitInterval) (T : Finset ι) (t : ι → Set Prop) :
    ErrVanish π ((T : Set ι).pi t) := by
  intro ε hε
  exact ⟨T, fun S hS => by rw [err_cylinder π S T hS t]; exact hε⟩

theorem errVanish_compl (π : ι → unitInterval) {A : Set (ι → Prop)} (hA : MeasurableSet A)
    (ih : ErrVanish π A) : ErrVanish π Aᶜ := by
  intro ε hε
  obtain ⟨S₀, hS₀⟩ := ih ε hε
  exact ⟨S₀, fun S hS => by rw [err_compl π S hA]; exact hS₀ S hS⟩

theorem errVanish_iUnion (π : ι → unitInterval) (f : ℕ → Set (ι → Prop))
    (hfd : Pairwise fun i j => Disjoint (f i) (f j)) (hfm : ∀ i, MeasurableSet (f i))
    (ih : ∀ i, ErrVanish π (f i)) : ErrVanish π (⋃ i, f i) := by
  intro ε hε
  let B : ℕ → Set (ι → Prop) := fun n => ⋃ i ∈ Finset.range n, f i
  have hBmeas : ∀ n, MeasurableSet (B n) := fun n =>
    MeasurableSet.biUnion (Finset.countable_toSet _) (fun i _ => hfm i)
  have hBmono : Monotone B := fun m n hmn =>
    Set.biUnion_subset_biUnion_left
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hmn))
  have hUnionB : ⋃ n, B n = ⋃ i, f i := by
    apply le_antisymm
    · exact Set.iUnion_subset fun n => Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
    · exact Set.iUnion_subset fun i =>
        Set.subset_iUnion_of_subset (i + 1) (Set.subset_biUnion_of_mem (Finset.self_mem_range_succ i))
  have hAmeas : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hfm
  have htend0 : Tendsto (fun n => (prodLaw π) (B n)) atTop (𝓝 ((prodLaw π) (⋃ i, f i))) := by
    have h := tendsto_measure_iUnion_atTop (μ := prodLaw π) hBmono
    rwa [hUnionB] at h
  have htend : Tendsto (fun n => (prodLaw π).real (B n)) atTop
      (𝓝 ((prodLaw π).real (⋃ i, f i))) := by
    have h2 : Tendsto (fun n => ((prodLaw π) (B n)).toReal) atTop
        (𝓝 (((prodLaw π) (⋃ i, f i)).toReal)) :=
      (ENNReal.tendsto_toReal (measure_ne_top (prodLaw π) (⋃ i, f i))).comp htend0
    simpa [Measure.real] using h2
  obtain ⟨N, hN⟩ : ∃ N, (prodLaw π).real (⋃ i, f i) - (prodLaw π).real (B N) < ε / 4 := by
    have hev : ∀ᶠ n in atTop, (prodLaw π).real (⋃ i, f i) - ε / 4 < (prodLaw π).real (B n) :=
      (tendsto_order.1 htend).1 _ (by linarith [hε])
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    exact ⟨N, by linarith [hN N le_rfl]⟩
  choose Sf hSf using fun i : ℕ => ih i (ε / (2 * (N + 1))) (by positivity)
  refine ⟨(Finset.range N).biUnion Sf, fun S hS => ?_⟩
  have hsmall : ∀ i ∈ Finset.range N, err π S (f i) < ε / (2 * (N + 1)) := by
    intro i hi
    exact hSf i S (le_trans (Finset.subset_biUnion_of_mem Sf hi) hS)
  have hBN : err π S (B N) ≤ ε / 2 := by
    refine le_trans (err_biUnion_range_le π S f hfm hfd N) ?_
    refine le_trans (Finset.sum_le_sum fun i hi => le_of_lt (hsmall i hi)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpos : (0:ℝ) ≤ ε / (2 * ((N:ℝ) + 1)) := by positivity
    have : (N:ℝ) ≤ (N:ℝ) + 1 := by linarith
    calc (N:ℝ) * (ε / (2 * ((N:ℝ) + 1))) ≤ ((N:ℝ) + 1) * (ε / (2 * ((N:ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_right this hpos
      _ = ε / 2 := by field_simp
  have hsub : B N ⊆ ⋃ i, f i := by
    refine Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
  calc err π S (⋃ i, f i)
      ≤ 2 * ((prodLaw π).real (⋃ i, f i) - (prodLaw π).real (B N)) + err π S (B N) :=
        err_le_of_subset π S (hBmeas N) hAmeas hsub
    _ < 2 * (ε / 4) + ε / 2 := by nlinarith [hN, hBN]
    _ = ε := by ring


theorem errVanish_of_measurable (π : ι → unitInterval) (A : Set (ι → Prop)) (hA : MeasurableSet A) :
    ErrVanish π A := by
  induction A, hA using MeasurableSpace.induction_on_inter
    (m := (inferInstance : MeasurableSpace (ι → Prop)))
    (s := squareCylinders fun _ => {t : Set Prop | MeasurableSet t})
    (generateFrom_squareCylinders (α := fun _ : ι => Prop)).symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet) (fun _ => Set.mem_ofPred.mpr MeasurableSet.univ))
  case empty => exact errVanish_empty π
  case basic t ht =>
    obtain ⟨s, u, hu, rfl⟩ := ht
    simp only [Set.mem_univ_pi] at hu
    exact errVanish_cylinder π s u
  case compl t htm ih => exact errVanish_compl π htm ih
  case iUnion f hfd hfm ih => exact errVanish_iUnion π f hfd hfm ih

theorem exists_err_lt (π : ι → unitInterval) (A : Set (ι → Prop)) (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) : ∃ S : Finset ι, err π S A < ε := by
  obtain ⟨S₀, hS₀⟩ := errVanish_of_measurable π A hA ε hε
  exact ⟨S₀, hS₀ S₀ (subset_refl _)⟩


theorem headLaw_eq_pi (π : ι → unitInterval) (S : Finset ι) :
    headLaw π (↑S : Set ι)
      = Measure.pi (fun i : ↥(↑S : Set ι) =>
          bernoulliMeasure True False
            (⟨(π i : ℝ), Set.mem_Icc.mpr ⟨(π i).2.1, (π i).2.2⟩⟩ : unitInterval)) := by
  rw [headLaw, Measure.infinitePi_eq_pi]

/-- Finite-product Harris--FKG for increasing functions on `(ι → Prop)`-space. -/
theorem fkg_pi_bernoulli {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (h₁ h₂ : (κ → Prop) → ℝ)
    (h1a : ∀ y, 0 ≤ h₁ y) (h2a : ∀ y, 0 ≤ h₂ y)
    (h1m : Monotone h₁) (h2m : Monotone h₂) :
    (∫ y, h₁ y ∂(Measure.pi (fun i =>
        bernoulliMeasure True False (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval))))
      * (∫ y, h₂ y ∂(Measure.pi (fun i =>
        bernoulliMeasure True False (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval))))
      ≤ ∫ y, h₁ y * h₂ y ∂(Measure.pi (fun i =>
        bernoulliMeasure True False (⟨p i, Set.mem_Icc.mpr ⟨hp0 i, hp1 i⟩⟩ : unitInterval))) := by
  classical
  rw [integral_pi_bernoulli p hp0 hp1 h₁, integral_pi_bernoulli p hp0 hp1 h₂,
    integral_pi_bernoulli p hp0 hp1 (fun y => h₁ y * h₂ y)]
  refine expectation_mul_expectation_le p hp0 hp1 (fun c => h₁ fun i => i ∈ c)
    (fun c => h₂ fun i => i ∈ c) (fun c => h1a _) (fun c => h2a _) ?_ ?_
  · intro c d hcd
    exact h1m fun i hi => hcd hi
  · intro c d hcd
    exact h2m fun i hi => hcd hi

theorem fkg_headLaw (π : ι → unitInterval) (S : Finset ι)
    (h₁ h₂ : ((i : ↥(↑S : Set ι)) → Prop) → ℝ)
    (h1a : ∀ y, 0 ≤ h₁ y) (h2a : ∀ y, 0 ≤ h₂ y)
    (h1m : Monotone h₁) (h2m : Monotone h₂) :
    (∫ x, h₁ x ∂headLaw π (↑S : Set ι)) * (∫ x, h₂ x ∂headLaw π (↑S : Set ι))
      ≤ ∫ x, h₁ x * h₂ x ∂headLaw π (↑S : Set ι) := by
  rw [headLaw_eq_pi (π := π) S]
  exact fkg_pi_bernoulli (fun i : ↥(↑S : Set ι) => (π i : ℝ)) (fun i => (π i).2.1)
    (fun i => (π i).2.2) h₁ h₂ h1a h2a h1m h2m

theorem integral_cylAvg_mul_cylAvg (π : ι → unitInterval) (S : Finset ι)
    {A B : Set (ι → Prop)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ ω, cylAvg π (↑S : Set ι) A ω * cylAvg π (↑S : Set ι) B ω ∂(prodLaw π)
      = ∫ x, tailAvg π (↑S : Set ι) A x * tailAvg π (↑S : Set ι) B x
          ∂(headLaw π (↑S : Set ι)) := by
  have hmap : (prodLaw π).map (restrS (↑S : Set ι)) = headLaw π (↑S : Set ι) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := coordLaw π) (f := Subtype.val)
      Subtype.val_injective
  rw [← hmap]
  have hm : Measurable fun x : (i : ↥(↑S : Set ι)) → Prop =>
      tailAvg π (↑S : Set ι) A x * tailAvg π (↑S : Set ι) B x :=
    (measurable_tailAvg π _ hA).mul (measurable_tailAvg π _ hB)
  rw [integral_map (measurable_restrS (↑S : Set ι)).aemeasurable hm.aestronglyMeasurable]
  rfl

theorem indSet_mul (A B : Set (ι → Prop)) (ω : ι → Prop) :
    indSet A ω * indSet B ω = indSet (A ∩ B) ω := by
  rw [indSet_apply A ω, indSet_apply B ω, indSet_apply (A ∩ B) ω]
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

theorem abs_cylAvg_mul_sub_le (π : ι → unitInterval) (S : Finset ι) (A B : Set (ι → Prop))
    (ω : ι → Prop) :
    |cylAvg π (↑S : Set ι) A ω * cylAvg π (↑S : Set ι) B ω - indSet A ω * indSet B ω|
      ≤ |indSet A ω - cylAvg π (↑S : Set ι) A ω| + |indSet B ω - cylAvg π (↑S : Set ι) B ω| := by
  have hφA0 : 0 ≤ cylAvg π (↑S : Set ι) A ω := cylAvg_nonneg π _ A ω
  have hφA1 : cylAvg π (↑S : Set ι) A ω ≤ 1 := cylAvg_le_one π _ A ω
  have hb0 : 0 ≤ indSet B ω := by rw [indSet_apply B ω]; split <;> norm_num
  have hb1 : indSet B ω ≤ 1 := by rw [indSet_apply B ω]; split <;> norm_num
  have e : cylAvg π (↑S : Set ι) A ω * cylAvg π (↑S : Set ι) B ω - indSet A ω * indSet B ω
      = (cylAvg π (↑S : Set ι) A ω - indSet A ω) * indSet B ω
        + cylAvg π (↑S : Set ι) A ω * (cylAvg π (↑S : Set ι) B ω - indSet B ω) := by ring
  rw [e]
  have hb_abs : |indSet B ω| ≤ 1 := by rw [abs_of_nonneg hb0]; exact hb1
  have hφA_abs : |cylAvg π (↑S : Set ι) A ω| ≤ 1 := by
    rw [abs_of_nonneg hφA0]; exact hφA1
  have h1 : |(cylAvg π (↑S : Set ι) A ω - indSet A ω) * indSet B ω|
      ≤ |indSet A ω - cylAvg π (↑S : Set ι) A ω| := by
    rw [abs_mul, abs_sub_comm (cylAvg π (↑S : Set ι) A ω) (indSet A ω)]
    calc |indSet A ω - cylAvg π (↑S : Set ι) A ω| * |indSet B ω|
        ≤ |indSet A ω - cylAvg π (↑S : Set ι) A ω| * 1 :=
          mul_le_mul_of_nonneg_left hb_abs (abs_nonneg _)
      _ = |indSet A ω - cylAvg π (↑S : Set ι) A ω| := mul_one _
  have h2 : |cylAvg π (↑S : Set ι) A ω * (cylAvg π (↑S : Set ι) B ω - indSet B ω)|
      ≤ |indSet B ω - cylAvg π (↑S : Set ι) B ω| := by
    rw [abs_mul, abs_sub_comm (cylAvg π (↑S : Set ι) B ω) (indSet B ω)]
    calc |cylAvg π (↑S : Set ι) A ω| * |indSet B ω - cylAvg π (↑S : Set ι) B ω|
        ≤ 1 * |indSet B ω - cylAvg π (↑S : Set ι) B ω| :=
          mul_le_mul_of_nonneg_right hφA_abs (abs_nonneg _)
      _ = |indSet B ω - cylAvg π (↑S : Set ι) B ω| := one_mul _
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)


theorem exists_err_pair_lt (π : ι → unitInterval) (A B : Set (ι → Prop))
    (hA : MeasurableSet A) (hB : MeasurableSet B) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ι, err π S A < ε ∧ err π S B < ε := by
  obtain ⟨SA, hSA⟩ := errVanish_of_measurable π A hA ε hε
  obtain ⟨SB, hSB⟩ := errVanish_of_measurable π B hB ε hε
  exact ⟨SA ∪ SB, hSA _ Finset.subset_union_left, hSB _ Finset.subset_union_right⟩

theorem indSet_mem_Icc (A : Set (ι → Prop)) (ω : ι → Prop) :
    0 ≤ indSet A ω ∧ indSet A ω ≤ 1 := by
  rw [indSet_apply A ω]
  split <;> norm_num

theorem tailAvg_monotone (π : ι → unitInterval) (S : Set ι) {A : Set (ι → Prop)}
    (hAu : IsUpperSet A) : Monotone (tailAvg π S A) := by
  intro x x' hxx
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro y hy
  refine hAu ?_ hy
  intro i
  by_cases hi : i ∈ S
  · have := hxx ⟨i, hi⟩
    simpa [glueS, hi] using this
  · simp [glueS, hi]

theorem integral_cylAvg_eq_tailAvg (π : ι → unitInterval) (S : Finset ι) {A : Set (ι → Prop)}
    (hA : MeasurableSet A) :
    ∫ ω, cylAvg π (↑S : Set ι) A ω ∂(prodLaw π)
      = ∫ x, tailAvg π (↑S : Set ι) A x ∂(headLaw π (↑S : Set ι)) := by
  have hmap : (prodLaw π).map (restrS (↑S : Set ι)) = headLaw π (↑S : Set ι) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := coordLaw π) (f := Subtype.val)
      Subtype.val_injective
  rw [← hmap,
    integral_map (measurable_restrS (↑S : Set ι)).aemeasurable
      (measurable_tailAvg π _ hA).aestronglyMeasurable]
  rfl

theorem integral_cylAvg_eq_tailAvg' (π : ι → unitInterval) (S : Finset ι) {T : Set ι}
    (hT : T = ↑S) {A : Set (ι → Prop)} (hA : MeasurableSet A) :
    ∫ ω, cylAvg π T A ω ∂(prodLaw π)
      = ∫ x, tailAvg π T A x ∂(headLaw π T) := by
  subst hT
  exact integral_cylAvg_eq_tailAvg π S hA

theorem integral_cylAvg_mul_cylAvg' (π : ι → unitInterval) (S : Finset ι) {T : Set ι}
    (hT : T = ↑S) {A B : Set (ι → Prop)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ ω, cylAvg π T A ω * cylAvg π T B ω ∂(prodLaw π)
      = ∫ x, tailAvg π T A x * tailAvg π T B x ∂(headLaw π T) := by
  subst hT
  exact integral_cylAvg_mul_cylAvg π S hA hB

/-- **Harris--FKG for arbitrary increasing measurable events** on the countable product law. -/
theorem fkg_events (π : ι → unitInterval) {A B : Set (ι → Prop)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    (prodLaw π).real A * (prodLaw π).real B ≤ (prodLaw π).real (A ∩ B) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨S, hSA, hSB⟩ := exists_err_pair_lt π A B hA hB (ε := ε / 3) (by linarith)
  let T : Set ι := ↑S
  have hT : T = ↑S := rfl
  have hφA : ∫ ω, cylAvg π T A ω ∂(prodLaw π) = (prodLaw π).real A := integral_cylAvg π T hA
  have hφB : ∫ ω, cylAvg π T B ω ∂(prodLaw π) = (prodLaw π).real B := integral_cylAvg π T hB
  have htailA : ∫ ω, cylAvg π T A ω ∂(prodLaw π) = ∫ x, tailAvg π T A x ∂(headLaw π T) :=
    integral_cylAvg_eq_tailAvg' π S hT hA
  have htailB : ∫ ω, cylAvg π T B ω ∂(prodLaw π) = ∫ x, tailAvg π T B x ∂(headLaw π T) :=
    integral_cylAvg_eq_tailAvg' π S hT hB
  have hmul : ∫ ω, cylAvg π T A ω * cylAvg π T B ω ∂(prodLaw π)
      = ∫ x, tailAvg π T A x * tailAvg π T B x ∂(headLaw π T) :=
    integral_cylAvg_mul_cylAvg' π S hT hA hB
  have hfkg : (∫ x, tailAvg π T A x ∂(headLaw π T))
      * (∫ x, tailAvg π T B x ∂(headLaw π T))
      ≤ ∫ x, tailAvg π T A x * tailAvg π T B x ∂(headLaw π T) :=
    fkg_headLaw π S _ _ (fun x => tailAvg_nonneg π _ A x) (fun x => tailAvg_nonneg π _ B x)
      (tailAvg_monotone π _ hAu) (tailAvg_monotone π _ hBu)
  -- pointwise comparison of the product with the indicators
  have hpt : ∀ ω : ι → Prop, cylAvg π T A ω * cylAvg π T B ω
      ≤ indSet A ω * indSet B ω
        + (|indSet A ω - cylAvg π T A ω| + |indSet B ω - cylAvg π T B ω|) := by
    intro ω
    have h := abs_cylAvg_mul_sub_le π S A B ω
    have h2 := (abs_le.mp h).2
    have h3 : |indSet A ω - cylAvg π (↑S : Set ι) A ω| = |indSet A ω - cylAvg π T A ω| := by rw [hT]
    have h4 : |indSet B ω - cylAvg π (↑S : Set ι) B ω| = |indSet B ω - cylAvg π T B ω| := by rw [hT]
    rw [h3, h4] at h2
    linarith
  -- integrability
  have hprod : Integrable (fun ω : ι → Prop => indSet A ω * indSet B ω) (prodLaw π) :=
    integrable_of_abs_le_one ((measurable_indSet hA).mul (measurable_indSet hB)) (fun ω => by
      rw [abs_le]
      constructor <;>
        nlinarith [(indSet_mem_Icc A ω).1, (indSet_mem_Icc A ω).2,
          (indSet_mem_Icc B ω).1, (indSet_mem_Icc B ω).2])
  have herrA : Integrable (fun ω : ι → Prop => |indSet A ω - cylAvg π T A ω|) (prodLaw π) := by
    rw [hT]; exact integrable_err_integrand π S hA
  have herrB : Integrable (fun ω : ι → Prop => |indSet B ω - cylAvg π T B ω|) (prodLaw π) := by
    rw [hT]; exact integrable_err_integrand π S hB
  have hleft : Integrable (fun ω : ι → Prop => cylAvg π T A ω * cylAvg π T B ω) (prodLaw π) :=
    integrable_of_abs_le_one ((measurable_cylAvg π T hA).mul (measurable_cylAvg π T hB))
      (fun ω => by
        rw [abs_le]
        constructor
        · have := cylAvg_nonneg π T A ω; have := cylAvg_nonneg π T B ω; nlinarith
        · have h1 := cylAvg_le_one π T A ω; have h2 := cylAvg_le_one π T B ω
          have h3 := cylAvg_nonneg π T A ω; have h4 := cylAvg_nonneg π T B ω
          nlinarith)
  have hdist : ∫ ω, cylAvg π T A ω * cylAvg π T B ω ∂(prodLaw π)
      ≤ (prodLaw π).real (A ∩ B) + err π S A + err π S B := by
    have e1 : ∫ ω, (indSet A ω * indSet B ω
        + (|indSet A ω - cylAvg π T A ω| + |indSet B ω - cylAvg π T B ω|)) ∂(prodLaw π)
        = ∫ ω, indSet A ω * indSet B ω ∂(prodLaw π)
          + ∫ ω, (|indSet A ω - cylAvg π T A ω| + |indSet B ω - cylAvg π T B ω|)
              ∂(prodLaw π) := integral_add hprod (herrA.add herrB)
    have e2 : ∫ ω, (|indSet A ω - cylAvg π T A ω| + |indSet B ω - cylAvg π T B ω|)
        ∂(prodLaw π) = err π S A + err π S B := by
      rw [integral_add herrA herrB]
      rfl
    have e3 : ∫ ω, indSet A ω * indSet B ω ∂(prodLaw π) = (prodLaw π).real (A ∩ B) := by
      rw [← integral_indSet (π := π) (A := A ∩ B) (hA.inter hB)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (indSet_mul A B ω))
    have mono : ∫ ω, cylAvg π T A ω * cylAvg π T B ω ∂(prodLaw π)
        ≤ ∫ ω, (indSet A ω * indSet B ω
            + (|indSet A ω - cylAvg π T A ω| + |indSet B ω - cylAvg π T B ω|)) ∂(prodLaw π) :=
      integral_mono hleft (hprod.add (herrA.add herrB)) hpt
    linarith
  calc (prodLaw π).real A * (prodLaw π).real B
      = (∫ ω, cylAvg π T A ω ∂(prodLaw π)) * (∫ ω, cylAvg π T B ω ∂(prodLaw π)) := by
        rw [hφA, hφB]
    _ = (∫ x, tailAvg π T A x ∂(headLaw π T)) * (∫ x, tailAvg π T B x ∂(headLaw π T)) := by
        rw [htailA, htailB]
    _ ≤ ∫ x, tailAvg π T A x * tailAvg π T B x ∂(headLaw π T) := hfkg
    _ = ∫ ω, cylAvg π T A ω * cylAvg π T B ω ∂(prodLaw π) := hmul.symm
    _ ≤ (prodLaw π).real (A ∩ B) + err π S A + err π S B := hdist
    _ ≤ (prodLaw π).real (A ∩ B) + ε := by linarith

end Product

/-! ## The paper's model: `edgeMeasure` and `P_β` on `Config V = Set (Sym2 V)` -/

section Canonical

variable {V : Type*} [Countable V]

/-- `prodLaw` over the edge set `Sym2 V` is definitionally the canonical independent-edge law. -/
theorem edgeMeasure_eq_prodLaw (π : Sym2 V → unitInterval) :
    edgeMeasure π = prodLaw π := by
  rw [edgeMeasure_eq_infinitePi]

/-- **Harris--FKG for arbitrary increasing measurable events** under the canonical
independent-edge law `P_π` of §I.1.2.  No finite-witness hypothesis. -/
theorem edgeMeasure_fkg_measurable (π : Sym2 V → unitInterval) {A B : Set (Config V)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    (edgeMeasure π).real A * (edgeMeasure π).real B ≤ (edgeMeasure π).real (A ∩ B) := by
  rw [edgeMeasure_eq_prodLaw]
  exact fkg_events π hA hB hAu hBu

/-- Harris--FKG for increasing measurable events in the `ℝ≥0∞`-valued form of the paper. -/
theorem edgeMeasure_fkg_measurable_ennreal (π : Sym2 V → unitInterval) {A B : Set (Config V)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    edgeMeasure π A * edgeMeasure π B ≤ edgeMeasure π (A ∩ B) := by
  have h := edgeMeasure_fkg_measurable π hA hB hAu hBu
  rw [← ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) (measure_ne_top _ _),
    ENNReal.toReal_mul]
  exact h

/-- **Harris--FKG for the law `P_β` of §I.1.2**, for arbitrary increasing measurable events. -/
theorem longRangeMeasure_fkg_measurable {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    {A B : Set (Config V)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    (longRangeMeasure J hJ β).real A * (longRangeMeasure J hJ β).real B
      ≤ (longRangeMeasure J hJ β).real (A ∩ B) := by
  rw [longRangeMeasure]
  exact edgeMeasure_fkg_measurable _ hA hB hAu hBu

/-- Harris--FKG for `P_β` in `ℝ≥0∞`-valued form. -/
theorem longRangeMeasure_fkg_measurable_ennreal {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) {A B : Set (Config V)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    longRangeMeasure J hJ β A * longRangeMeasure J hJ β B
      ≤ longRangeMeasure J hJ β (A ∩ B) := by
  rw [longRangeMeasure]
  exact edgeMeasure_fkg_measurable_ennreal _ hA hB hAu hBu

/-! ## Increasing observables: the first display of §I.2.1 -/

/-- **Harris--FKG for increasing observables, `ℝ≥0∞`-valued form**: for measurable nonnegative
`f`, `g` increasing in the configuration, the level sets `{s < f}` and `{t < g}` are increasing
measurable events, so the event form applies to them, and the layer-cake engine of
`BK/LayerCake.lean` gives `(∫ f)(∫ g) ≤ ∫ f g`. -/
theorem edgeMeasure_fkg_functional (π : Sym2 V → unitInterval) {f g : Config V → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf : Measurable f) (hg : Measurable g)
    (hfu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → f ω ≤ f ω')
    (hgu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂(edgeMeasure π))
        * (∫⁻ ω, ENNReal.ofReal (g ω) ∂(edgeMeasure π))
      ≤ ∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂(edgeMeasure π) := by
  refine Percolation.LayerCake.lintegral_mul_ge_of_meas_lt hf0 hg0 hf hg fun s t hs ht => ?_
  exact edgeMeasure_fkg_measurable_ennreal π (measurableSet_lt measurable_const hf)
    (measurableSet_lt measurable_const hg)
    (fun a b hab ha => lt_of_lt_of_le ha (hfu hab)) (fun a b hab ha => lt_of_lt_of_le ha (hgu hab))

/-- **Harris--FKG for bounded increasing observables**, real-valued form: the displayed
`E F(ω)G(ω) ≥ E F(ω) E G(ω)` of §I.2.1 for observables with `0 ≤ f, g ≤ 1`. -/
theorem edgeMeasure_fkg_functional_real (π : Sym2 V → unitInterval) {f g : Config V → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf1 : ∀ ω, f ω ≤ 1) (hg1 : ∀ ω, g ω ≤ 1)
    (hf : Measurable f) (hg : Measurable g)
    (hfu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → f ω ≤ f ω')
    (hgu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') :
    (∫ ω, f ω ∂(edgeMeasure π)) * (∫ ω, g ω ∂(edgeMeasure π))
      ≤ ∫ ω, f ω * g ω ∂(edgeMeasure π) := by
  have h := edgeMeasure_fkg_functional π hf0 hg0 hf hg hfu hgu
  have hfI : Integrable f (edgeMeasure π) :=
    integrable_of_abs_le hf (C := 1) (fun ω => by rw [abs_of_nonneg (hf0 ω)]; exact hf1 ω)
  have hgI : Integrable g (edgeMeasure π) :=
    integrable_of_abs_le hg (C := 1) (fun ω => by rw [abs_of_nonneg (hg0 ω)]; exact hg1 ω)
  have hfgI : Integrable (fun ω => f ω * g ω) (edgeMeasure π) :=
    integrable_of_abs_le (hf.mul hg) (C := 1) (fun ω => by
      rw [abs_of_nonneg (mul_nonneg (hf0 ω) (hg0 ω))]
      nlinarith [hf1 ω, hg1 ω, hf0 ω, hg0 ω])
  have e1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂(edgeMeasure π)
      = ENNReal.ofReal (∫ ω, f ω ∂(edgeMeasure π)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfI (Filter.Eventually.of_forall hf0)).symm
  have e2 : ∫⁻ ω, ENNReal.ofReal (g ω) ∂(edgeMeasure π)
      = ENNReal.ofReal (∫ ω, g ω ∂(edgeMeasure π)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgI (Filter.Eventually.of_forall hg0)).symm
  have e3 : ∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂(edgeMeasure π)
      = ENNReal.ofReal (∫ ω, f ω * g ω ∂(edgeMeasure π)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfgI
      (Filter.Eventually.of_forall fun ω => mul_nonneg (hf0 ω) (hg0 ω))).symm
  rw [e1, e2, e3, ← ENNReal.ofReal_mul (integral_nonneg hf0)] at h
  exact ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => mul_nonneg (hf0 ω) (hg0 ω)) |>.mp h

/-- Harris--FKG for increasing observables under the paper's law `P_β` (first display of §I.2.1). -/
theorem longRangeMeasure_fkg_functional {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    {f g : Config V → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf : Measurable f) (hg : Measurable g)
    (hfu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → f ω ≤ f ω')
    (hgu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂(longRangeMeasure J hJ β))
        * (∫⁻ ω, ENNReal.ofReal (g ω) ∂(longRangeMeasure J hJ β))
      ≤ ∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂(longRangeMeasure J hJ β) := by
  rw [longRangeMeasure]
  exact edgeMeasure_fkg_functional _ hf0 hg0 hf hg hfu hgu

/-- Harris--FKG for bounded increasing observables under `P_β`, real-valued form. -/
theorem longRangeMeasure_fkg_functional_real {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    {f g : Config V → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf1 : ∀ ω, f ω ≤ 1) (hg1 : ∀ ω, g ω ≤ 1)
    (hf : Measurable f) (hg : Measurable g)
    (hfu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → f ω ≤ f ω')
    (hgu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω') :
    (∫ ω, f ω ∂(longRangeMeasure J hJ β)) * (∫ ω, g ω ∂(longRangeMeasure J hJ β))
      ≤ ∫ ω, f ω * g ω ∂(longRangeMeasure J hJ β) := by
  rw [longRangeMeasure]
  exact edgeMeasure_fkg_functional_real _ hf0 hg0 hf1 hg1 hf hg hfu hgu

/-- **Harris--FKG for integrable increasing observables** in the exact form of the first display of
§I.2.1: for measurable nonnegative `f`, `g` increasing in the configuration with `f`, `g` and `f g`
integrable, `E(f g) ≥ E f · E g`. -/
theorem edgeMeasure_fkg_functional_integrable (π : Sym2 V → unitInterval) {f g : Config V → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf : Measurable f) (hg : Measurable g)
    (hfu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → f ω ≤ f ω')
    (hgu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω')
    (hfI : Integrable f (edgeMeasure π)) (hgI : Integrable g (edgeMeasure π))
    (hfgI : Integrable (fun ω => f ω * g ω) (edgeMeasure π)) :
    (∫ ω, f ω ∂(edgeMeasure π)) * (∫ ω, g ω ∂(edgeMeasure π))
      ≤ ∫ ω, f ω * g ω ∂(edgeMeasure π) := by
  have h := edgeMeasure_fkg_functional π hf0 hg0 hf hg hfu hgu
  have e1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂(edgeMeasure π)
      = ENNReal.ofReal (∫ ω, f ω ∂(edgeMeasure π)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfI
      (Filter.Eventually.of_forall hf0)).symm
  have e2 : ∫⁻ ω, ENNReal.ofReal (g ω) ∂(edgeMeasure π)
      = ENNReal.ofReal (∫ ω, g ω ∂(edgeMeasure π)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgI
      (Filter.Eventually.of_forall hg0)).symm
  have e3 : ∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂(edgeMeasure π)
      = ENNReal.ofReal (∫ ω, f ω * g ω ∂(edgeMeasure π)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfgI
      (Filter.Eventually.of_forall fun ω => mul_nonneg (hf0 ω) (hg0 ω))).symm
  rw [e1, e2, e3, ← ENNReal.ofReal_mul (integral_nonneg hf0)] at h
  exact ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => mul_nonneg (hf0 ω) (hg0 ω)) |>.mp h

/-- Harris--FKG for integrable increasing observables under the paper's law `P_β`. -/
theorem longRangeMeasure_fkg_functional_integrable {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    {f g : Config V → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hf : Measurable f) (hg : Measurable g)
    (hfu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → f ω ≤ f ω')
    (hgu : ∀ ⦃ω ω' : Config V⦄, ω ⊆ ω' → g ω ≤ g ω')
    (hfI : Integrable f (longRangeMeasure J hJ β)) (hgI : Integrable g (longRangeMeasure J hJ β))
    (hfgI : Integrable (fun ω => f ω * g ω) (longRangeMeasure J hJ β)) :
    (∫ ω, f ω ∂(longRangeMeasure J hJ β)) * (∫ ω, g ω ∂(longRangeMeasure J hJ β))
      ≤ ∫ ω, f ω * g ω ∂(longRangeMeasure J hJ β) := by
  rw [longRangeMeasure]
  exact edgeMeasure_fkg_functional_integrable _ hf0 hg0 hf hg hfu hgu hfI hgI hfgI

/-! ## Compatibility: the previous finite-witness form is a special case

`Percolation.FiniteWitness A` says that every `ω ∈ A` has a finite witness `s ⊆ ω` with `s ∈ A`;
for an increasing `A` this exhibits `A` as a countable union of open cylinders, so `A` is Borel.
Hence the earlier `edgeMeasure_fkg` (finite-witness FKG) is the special case of
`edgeMeasure_fkg_measurable` in which the events happen to be finitely witnessed. -/

/-- A finitely witnessed increasing event is measurable (it is a countable union of cylinders). -/
theorem measurableSet_of_finiteWitness {A : Set (Config V)} (hAu : IsUpperSet A)
    (h : Percolation.FiniteWitness A) : MeasurableSet A := by
  have hcyl : ∀ s : Finset (Sym2 V),
      MeasurableSet {ω : Config V | (s : Set (Sym2 V)) ⊆ ω} := by
    intro s
    have hEq : {ω : Config V | (s : Set (Sym2 V)) ⊆ ω}
        = ⋂ i : Sym2 V, ⋂ (_ : i ∈ s), {ω : Config V | i ∈ ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.subset_def, Set.mem_iInter, Set.mem_ofPred_eq]
      tauto
    rw [hEq]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_mem i
  have hA : A = ⋃ (s : Finset (Sym2 V)) (_ : (s : Set (Sym2 V)) ∈ A),
      {ω : Config V | (s : Set (Sym2 V)) ⊆ ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hω
      obtain ⟨s, hs, hsA⟩ := h ω hω
      exact ⟨s, hsA, hs⟩
    · rintro ⟨s, hsA, hs⟩
      exact hAu hs hsA
  rw [hA]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ => hcyl s

/-- **Finite-witness FKG is a special case**: the earlier `edgeMeasure_fkg` follows from the
general measurable-event form. -/
theorem edgeMeasure_fkg_of_finiteWitness (π : Sym2 V → unitInterval) {A B : Set (Config V)}
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : Percolation.FiniteWitness A) (hfB : Percolation.FiniteWitness B) :
    (edgeMeasure π).real A * (edgeMeasure π).real B ≤ (edgeMeasure π).real (A ∩ B) :=
  edgeMeasure_fkg_measurable π (measurableSet_of_finiteWitness hA hfA)
    (measurableSet_of_finiteWitness hB hfB) hA hB

/-- **Instantiation to a non-cylindrical event**: the infinite-cluster indicators of two vertices
are nonnegatively correlated under `edgeMeasure π`.  These events have no finite witness, so this
is exactly the case the earlier finite-witness FKG could not cover; it is a check that the general
theorem applies. -/
theorem edgeMeasure_fkg_infiniteCluster (π : Sym2 V → unitInterval) (x y : V) :
    (edgeMeasure π).real {ω : Config V | InInfiniteCluster ω x}
        * (edgeMeasure π).real {ω : Config V | InInfiniteCluster ω y}
      ≤ (edgeMeasure π).real ({ω : Config V | InInfiniteCluster ω x}
          ∩ {ω : Config V | InInfiniteCluster ω y}) :=
  edgeMeasure_fkg_measurable π (measurableSet_inInfiniteCluster x)
    (measurableSet_inInfiniteCluster y) (isIncreasing_inInfiniteCluster x)
    (isIncreasing_inInfiniteCluster y)

end Canonical
