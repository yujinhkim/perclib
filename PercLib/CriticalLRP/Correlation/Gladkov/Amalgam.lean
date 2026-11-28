/-
Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2,
Lemma 3.1 ([GZ24, Lemma 4.2]) in the deterministic case: the amalgamated
configuration is independent of the complementary amalgamation and has the
original law.

The paper's Lemma 3.1 is stated for a set `S(C1,C2)` built by a decision tree.
This file proves the case in which the revealed set is a fixed set `T`, which is
the base case of the induction behind Lemma 3.1.

Model: two independent copies of the inhomogeneous Bernoulli law, encoded as the
single product law `prodBernoulli (twoProfile q)` on `Set (ι × Bool)`, where the
copy `b` of a configuration is `copy b ω = {i | (i,b) ∈ ω}`.

Paper convention: `C1 →_T C2` is `C1` on `T` and `C2` off `T`; here this is
`amalFirst T ω`, and the complementary amalgamation `C2 →_T C1` is
`amalSecond T ω`.
-/
module

public import PercLib.Probability.Characterization
public import PercLib.Probability.DeterminedIndependence

/-! The independence and law-preservation results for amalgamation over a fixed
revealed coordinate set. This is the deterministic base case, not the full
random decision-tree argument for Gladkov's inequality. -/

set_option autoImplicit false

/-!
# The amalgamation lemma for a fixed revealed set

For a fixed set `T` of coordinates and two independent Bernoulli configurations,
the pair `(C1 →_T C2, C2 →_T C1)` consists of two independent copies of the
original law. This is the deterministic case of the decision-tree independence
lemma that underlies the proof of Gladkov's three-point inequality.

The proof has four steps, all of them unconditional:

* the `b`-th copy of `prodBernoulli (twoProfile q)` is `prodBernoulli q`;
* flipping the two copies exactly off `T` preserves `prodBernoulli (twoProfile q)`;
* coordinate events determined by the two copies are independent;
* the flip converts the amalgamated pair into the plain pair `(C1, C2)`.
-/

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

variable {ι : Type*}

/-- The profile of the two-copy index type, which does not depend on the copy. -/
def twoProfile (q : ι → unitInterval) : ι × Bool → unitInterval := fun x => q x.1

/-- The `b`-th copy of a two-copy configuration. -/
def copy (b : Bool) (ω : Set (ι × Bool)) : Set ι := {i | (i, b) ∈ ω}

/-- `C1 →_T C2`: the first copy on `T`, the second copy off `T`. -/
def amalFirst (T : Set ι) (ω : Set (ι × Bool)) : Set ι :=
  {i | (i ∈ T ∧ (i, false) ∈ ω) ∨ (i ∉ T ∧ (i, true) ∈ ω)}

/-- `C2 →_T C1`: the second copy on `T`, the first copy off `T`. -/
def amalSecond (T : Set ι) (ω : Set (ι × Bool)) : Set ι :=
  {i | (i ∈ T ∧ (i, true) ∈ ω) ∨ (i ∉ T ∧ (i, false) ∈ ω)}

/-! ### The marginals -/

theorem measurable_copy (b : Bool) : Measurable (copy b : Set (ι × Bool) → Set ι) := by
  refine Measurable.of_mem fun i => ?_
  exact measurable_set_mem (i, b)

theorem measurable_amalFirst (T : Set ι) :
    Measurable (amalFirst T : Set (ι × Bool) → Set ι) := by
  classical
  refine Measurable.of_mem fun i => ?_
  by_cases h : i ∈ T
  · have hEq : (fun ω : Set (ι × Bool) => i ∈ amalFirst T ω) =
        fun ω => (i, false) ∈ ω := by
      funext ω
      simp [amalFirst, h]
    rw [hEq]
    exact measurable_set_mem (i, false)
  · have hEq : (fun ω : Set (ι × Bool) => i ∈ amalFirst T ω) =
        fun ω => (i, true) ∈ ω := by
      funext ω
      simp [amalFirst, h]
    rw [hEq]
    exact measurable_set_mem (i, true)

theorem measurable_amalSecond (T : Set ι) :
    Measurable (amalSecond T : Set (ι × Bool) → Set ι) := by
  classical
  refine Measurable.of_mem fun i => ?_
  by_cases h : i ∈ T
  · have hEq : (fun ω : Set (ι × Bool) => i ∈ amalSecond T ω) =
        fun ω => (i, true) ∈ ω := by
      funext ω
      simp [amalSecond, h]
    rw [hEq]
    exact measurable_set_mem (i, true)
  · have hEq : (fun ω : Set (ι × Bool) => i ∈ amalSecond T ω) =
        fun ω => (i, false) ∈ ω := by
      funext ω
      simp [amalSecond, h]
    rw [hEq]
    exact measurable_set_mem (i, false)

/-- Each copy of the two-copy law is the original law. -/
theorem map_copy (q : ι → unitInterval) (b : Bool) :
    (prodBernoulli (twoProfile q)).map (copy b) = prodBernoulli q := by
  classical
  refine (map_prodBernoulli_eq_iff (twoProfile q) (measurable_copy b) q).2 fun F => ?_
  have hpre : copy b ⁻¹' {ω : Set ι | (F : Set ι) ⊆ ω} =
      {ω : Set (ι × Bool) |
        ((F.image (fun i => (i, b)) : Finset (ι × Bool)) : Set (ι × Bool)) ⊆ ω} := by
    ext ω
    simp only [Set.mem_preimage, Finset.coe_image, Set.subset_def, copy]
    constructor
    · rintro h y ⟨i, hi, rfl⟩
      exact h i hi
    · intro h i hi
      exact h (i, b) ⟨i, hi, rfl⟩
  rw [hpre, prodBernoulli_subset]
  rw [Finset.prod_image
    (f := fun x : ι × Bool => (unitInterval.toNNReal (twoProfile q x) : ℝ≥0∞))
    (g := fun i => (i, b)) (s := F) (fun x _ y _ hxy => by simpa using hxy)]
  exact Finset.prod_congr rfl fun i _ => by simp [twoProfile]

/-! ### The flip of the two copies off `T` -/

/-- Exchange the two copies exactly at the coordinates outside `T`. -/
noncomputable def flipIdx (T : Set ι) (x : ι × Bool) : ι × Bool := by
  classical
  exact (x.1, if x.1 ∈ T then x.2 else Bool.not x.2)

theorem flipIdx_fst (T : Set ι) (x : ι × Bool) : (flipIdx T x).1 = x.1 := rfl

theorem flipIdx_involutive (T : Set ι) : Function.Involutive (flipIdx T) := by
  intro x
  obtain ⟨i, b⟩ := x
  by_cases h : i ∈ T <;> simp [flipIdx, h]

/-- The flip at the level of configurations. -/
def flipConfig (T : Set ι) (ω : Set (ι × Bool)) : Set (ι × Bool) := {x | flipIdx T x ∈ ω}

theorem flipConfig_involutive (T : Set ι) : Function.Involutive (flipConfig T) := by
  intro ω
  ext x
  simp [flipConfig, flipIdx_involutive T x]

theorem measurable_flipConfig (T : Set ι) : Measurable (flipConfig T) := by
  refine Measurable.of_mem fun x => ?_
  exact measurable_set_mem (flipIdx T x)

/-- The flip of the two copies off `T` preserves the two-copy law. -/
theorem flipConfig_map (q : ι → unitInterval) (T : Set ι) :
    (prodBernoulli (twoProfile q)).map (flipConfig T) = prodBernoulli (twoProfile q) := by
  classical
  refine (map_prodBernoulli_eq_iff (twoProfile q) (measurable_flipConfig T) (twoProfile q)).2
    fun F => ?_
  have hpre : (flipConfig T) ⁻¹' {ω : Set (ι × Bool) | (F : Set (ι × Bool)) ⊆ ω} =
      {ω : Set (ι × Bool) |
        ((F.image (flipIdx T) : Finset (ι × Bool)) : Set (ι × Bool)) ⊆ ω} := by
    ext ω
    simp only [Set.mem_preimage, Finset.coe_image, Set.subset_def, flipConfig]
    constructor
    · rintro h y ⟨x, hx, rfl⟩
      exact h x hx
    · intro h x hx
      exact h (flipIdx T x) ⟨x, hx, rfl⟩
  rw [hpre, prodBernoulli_subset]
  rw [Finset.prod_image
    (f := fun x : ι × Bool => (unitInterval.toNNReal (twoProfile q x) : ℝ≥0∞))
    (g := flipIdx T) (s := F)
    (fun x _ y _ hxy => Function.Involutive.injective (flipIdx_involutive T) hxy)]
  exact Finset.prod_congr rfl fun x _ => by simp [twoProfile, flipIdx_fst]

/-- Flipping off `T` turns the amalgamated pair into the plain pair of copies. -/
theorem amalFirst_flipConfig (T : Set ι) (ω : Set (ι × Bool)) :
    amalFirst T (flipConfig T ω) = copy false ω := by
  classical
  ext i
  by_cases h : i ∈ T <;> simp [amalFirst, flipConfig, copy, flipIdx, h]

theorem amalSecond_flipConfig (T : Set ι) (ω : Set (ι × Bool)) :
    amalSecond T (flipConfig T ω) = copy true ω := by
  classical
  ext i
  by_cases h : i ∈ T <;> simp [amalSecond, flipConfig, copy, flipIdx, h]

/-! ### Independence of the two copies -/

theorem disjoint_copy_coords :
    Disjoint {x : ι × Bool | x.2 = false} {x : ι × Bool | x.2 = true} := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : x.2 = false := hx
  have h2 : x.2 = true := hx'
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- An event about one copy is determined by the coordinates of that copy. -/
theorem copy_determined (b : Bool) (A : Set (Set ι)) {ω ω' : Set (ι × Bool)}
    (h : ω ∩ {x : ι × Bool | x.2 = b} = ω' ∩ {x : ι × Bool | x.2 = b}) :
    (copy b ω ∈ A ↔ copy b ω' ∈ A) := by
  have hc : copy b ω = copy b ω' := by
    ext i
    have key : (i, b) ∈ ω ↔ (i, b) ∈ ω' := by
      have := congrArg (fun s : Set (ι × Bool) => (i, b) ∈ s) h
      simpa using this
    simpa [copy] using key
  rw [hc]

/-- The events about the two separate copies are independent. -/
theorem copy_indep (q : ι → unitInterval) {A B : Set (Set ι)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    prodBernoulli (twoProfile q) {ω | copy false ω ∈ A ∧ copy true ω ∈ B} =
      prodBernoulli (twoProfile q) {ω | copy false ω ∈ A} *
        prodBernoulli (twoProfile q) {ω | copy true ω ∈ B} := by
  have h := prodBernoulli_inter_of_determined (twoProfile q)
    (P := {x : ι × Bool | x.2 = false}) (Q := {x : ι × Bool | x.2 = true}) disjoint_copy_coords
    (hA.preimage (measurable_copy false)) (hB.preimage (measurable_copy true))
    (fun _ _ h => copy_determined false A h) (fun _ _ h => copy_determined true B h)
  have hset : copy false ⁻¹' A ∩ copy true ⁻¹' B
      = {ω : Set (ι × Bool) | copy false ω ∈ A ∧ copy true ω ∈ B} := by
    ext ω
    rfl
  rw [hset] at h
  exact h

/-! ### The amalgamation lemma -/

/-- **Deterministic amalgamation lemma.** For a fixed set `T` of coordinates, the two
amalgamations `C1 →_T C2` and `C2 →_T C1` of two independent Bernoulli configurations
are independent, and each of them has the original law.

This is Gladkov's Lemma 3.1 for a revealed set that does not depend on the
configuration; it is the base case of the decision-tree induction. -/
theorem amalgam_indep (q : ι → unitInterval) (T : Set ι) {A B : Set (Set ι)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    prodBernoulli (twoProfile q) {ω | amalFirst T ω ∈ A ∧ amalSecond T ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  have hE : MeasurableSet {ω : Set (ι × Bool) |
      amalFirst T ω ∈ A ∧ amalSecond T ω ∈ B} :=
    (hA.preimage (measurable_amalFirst T)).inter (hB.preimage (measurable_amalSecond T))
  have hstep : prodBernoulli (twoProfile q) {ω | amalFirst T ω ∈ A ∧ amalSecond T ω ∈ B} =
      prodBernoulli (twoProfile q) {ω | copy false ω ∈ A ∧ copy true ω ∈ B} := by
    have hset : (flipConfig T) ⁻¹' {ω : Set (ι × Bool) |
        amalFirst T ω ∈ A ∧ amalSecond T ω ∈ B} =
        {ω : Set (ι × Bool) | copy false ω ∈ A ∧ copy true ω ∈ B} := by
      ext ω
      simp [amalFirst_flipConfig, amalSecond_flipConfig]
    rw [← hset, ← Measure.map_apply (measurable_flipConfig T) hE, flipConfig_map]
  have h1 : prodBernoulli (twoProfile q) {ω | copy false ω ∈ A} = prodBernoulli q A := by
    rw [← map_copy q false]
    exact (Measure.map_apply (measurable_copy false) hA).symm
  have h2 : prodBernoulli (twoProfile q) {ω | copy true ω ∈ B} = prodBernoulli q B := by
    rw [← map_copy q true]
    exact (Measure.map_apply (measurable_copy true) hB).symm
  rw [hstep, copy_indep q hA hB, h1, h2]

/-- The first amalgamation alone has the original law. -/
theorem map_amalFirst (q : ι → unitInterval) (T : Set ι) :
    (prodBernoulli (twoProfile q)).map (amalFirst T) = prodBernoulli q := by
  have hfun : (amalFirst T) = (copy false) ∘ (flipConfig T) := by
    funext ω
    rw [Function.comp_apply, ← amalFirst_flipConfig T (flipConfig T ω),
      flipConfig_involutive T ω]
  rw [hfun, ← Measure.map_map (measurable_copy false) (measurable_flipConfig T),
    flipConfig_map, map_copy]

/-! ### Non-vacuity

With `T = univ` both amalgamations are the two copies themselves, and with
`T = ∅` they are the two copies swapped; both are instances of the main theorem. -/

example (ω : Set (ι × Bool)) : amalFirst (Set.univ : Set ι) ω = copy false ω := by
  ext i
  simp [amalFirst, copy]

example (ω : Set (ι × Bool)) : amalFirst (∅ : Set ι) ω = copy true ω := by
  ext i
  simp [amalFirst, copy]

example (q : ι → unitInterval) {A B : Set (Set ι)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    prodBernoulli (twoProfile q) {ω | copy false ω ∈ A ∧ copy true ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  simpa [amalFirst, amalSecond, copy] using amalgam_indep q (Set.univ : Set ι) hA hB

end PercLib.GladkovAmalgam

/-! ### Axiom audit -/

#print axioms PercLib.GladkovAmalgam.amalgam_indep
#print axioms PercLib.GladkovAmalgam.map_amalFirst
#print axioms PercLib.GladkovAmalgam.map_copy
#print axioms PercLib.GladkovAmalgam.flipConfig_map
#print axioms PercLib.GladkovAmalgam.copy_indep
