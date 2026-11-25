/-
The independence argument adapts the method of bondPercolation_inter_of_disjoint
and bondPercolation_finiteEnergy in Tom Hutchcroft's near-critical-diffusivity,
Percolation/Literature/FiniteEnergy.lean at
c820fea91a7482c1755de0ec94ecb9f59ccfcacc, under native-source permission R-3.
Here the assignment is fixed, the profile is inhomogeneous, and the law is
PercLib's existing prodBernoulli. The overwrite proof uses mathlib directly.
-/
module

public import PercLib.Probability.Cylinder
public import PercLib.Probability.ProdBernoulliIndependence
public import Mathlib.Data.Sym.Sym2

/-! # Finite-energy identities

Finite assignments have their exact product probability, independently of every
measurable event determined by the complementary coordinates. Overwriting a
block fixes its profile at zero or one. Ambient indices need not be countable;
for bonds they include the diagonal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {ι : Type*}

/-- Exact probability of a finite assignment, including closed coordinates. -/
theorem prodBernoulli_inter_finset_eq [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) :
    prodBernoulli p {ω | ω ∩ (F : Set ι) = (a : Set ι)} =
      (∏ i ∈ a, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
        ∏ i ∈ F \ a, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  classical
  rw [prodBernoulli_eq_map]
  change (Measure.map (MeasurableEquiv.setOfPred : (ι → Prop) ≃ᵐ Set ι)
    (Measure.infinitePi fun i => bernoulliMeasure True False (p i))) _ = _
  rw [MeasurableEquiv.setOfPred.map_apply]
  have h : MeasurableEquiv.setOfPred ⁻¹' {ω | ω ∩ (F : Set ι) = (a : Set ι)} =
      Set.pi (F : Set ι) (fun i => ({i ∈ a} : Set Prop)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe,
      Set.mem_singleton_iff]
    constructor
    · intro h i hi
      have := Set.ext_iff.mp h i
      simpa [hi] using this
    · intro h
      ext i
      by_cases hi : i ∈ F
      · simpa [hi] using h i hi
      · simp [hi, show i ∉ a from fun ha' => hi (ha ha')]
  rw [h, Measure.infinitePi_pi (μ := fun i : ι => bernoulliMeasure True False (p i))
    (s := F) (t := fun i => ({i ∈ a} : Set Prop))
    (fun i _ => measurableSet_singleton (i ∈ a)), ← Finset.prod_sdiff ha, mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [hi, bernoulliMeasure_def]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.mem_sdiff.mp hi |>.2, bernoulliMeasure_def]

private theorem measurable_subtype_image (S : Set ι) :
    Measurable (fun u : Set S => Subtype.val '' u) := by
  classical
  apply Measurable.of_mem
  intro i
  by_cases hi : i ∈ S
  · simpa only [Set.mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, hi, exists_true_left] using (measurable_set_mem (⟨i, hi⟩ : S))
  · have h : (fun u : Set S => i ∈ Subtype.val '' u) = fun _ => False := by
      funext u
      simp [Set.mem_image, hi]
    rw [h]
    exact measurable_const

/-- A finite assignment is independent of any measurable event determined by
coordinates outside the assigned block. The determination hypothesis is stated
as invariance under changes inside the block. -/
theorem prodBernoulli_inter_pattern [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) (B : Set (Set ι)) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set ι, ω \ (F : Set ι) = ω' \ (F : Set ι) →
      (ω ∈ B ↔ ω' ∈ B)) :
    prodBernoulli p (B ∩ {ω | ω ∩ (F : Set ι) = (a : Set ι)}) =
      prodBernoulli p B * (∏ i ∈ a, (unitInterval.toNNReal (p i) : ℝ≥0∞)) *
        ∏ i ∈ F \ a, (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  classical
  let S : Set ι := F
  let A : Set (Set S) := {{i : S | (i : ι) ∈ a}}
  let D : Set (Set (Sᶜ : Set ι)) := (fun u => Subtype.val '' u) ⁻¹' B
  have hD : MeasurableSet D := hB.preimage (measurable_subtype_image Sᶜ)
  have hA : MeasurableSet A := measurableSet_singleton _
  have hpreA : {ω : Set ι | {i : S | (i : ι) ∈ ω} ∈ A} =
      {ω | ω ∩ (F : Set ι) = (a : Set ι)} := by
    ext ω
    change ({i : S | (i : ι) ∈ ω} = {i : S | (i : ι) ∈ a}) ↔ _
    constructor
    · intro h
      ext i
      by_cases hi : i ∈ F
      · exact (and_iff_left hi).trans (Set.ext_iff.mp h ⟨i, hi⟩)
      · simp [hi, show i ∉ a from fun h => hi (ha h)]
    · intro h
      ext i
      have hi : (i : ι) ∈ F := i.property
      simpa [hi] using Set.ext_iff.mp h (i : ι)
  have hpreD : {ω : Set ι | {i : (Sᶜ : Set ι) | (i : ι) ∈ ω} ∈ D} = B := by
    ext ω
    change (Subtype.val '' {i : (Sᶜ : Set ι) | (i : ι) ∈ ω}) ∈ B ↔ ω ∈ B
    apply houtside
    ext i
    simp [S, Set.mem_image, and_comm]
  have h := prodBernoulli_block_inter p Sᶜ S (disjoint_compl_left)
    D A hD hA
  change prodBernoulli p
    ({ω | {i : (Sᶜ : Set ι) | (i : ι) ∈ ω} ∈ D} ∩ {ω | {i : S | (i : ι) ∈ ω} ∈ A}) = _ at h
  rw [hpreD, hpreA, prodBernoulli_inter_finset_eq p F a ha] at h
  exact h.trans (mul_assoc _ _ _).symm

/-- Overwriting any block by a fixed assignment fixes precisely those marginals.
The finiteness of the block is unnecessary for this pushforward identity. -/
theorem prodBernoulli_map_overwrite (p : ι → unitInterval)
    (F a : Set ι) (ha : a ⊆ F) [DecidablePred (· ∈ F)] [DecidablePred (· ∈ a)] :
    (prodBernoulli p).map (fun ω => (ω \ F) ∪ a) =
      prodBernoulli (fun i => if i ∈ F then (if i ∈ a then 1 else 0) else p i) := by
  classical
  let f : ι → Prop → Prop := fun i b => (b ∧ i ∉ F) ∨ i ∈ a
  have hf : ∀ i, Measurable (f i) := by intro i; dsimp [f]; fun_prop
  have hS : Measurable (fun q : ι → Prop => {i | q i}) :=
    MeasurableEquiv.setOfPred.measurable
  have ho : Measurable (fun ω : Set ι => (ω \ F) ∪ a) := by fun_prop
  rw [prodBernoulli_eq_map, Measure.map_map ho hS, prodBernoulli_eq_map]
  change (Measure.infinitePi fun i => bernoulliMeasure True False (p i)).map
    ((fun q : ι → Prop => {i | q i}) ∘ (fun q i => f i (q i))) = _
  rw [← Measure.map_map hS (by fun_prop), Measure.infinitePi_map_pi _ hf]
  congr 1
  congr 1
  funext i
  rw [map_bernoulliMeasure]
  by_cases hi : i ∈ F
  · by_cases hai : i ∈ a <;> simp [f, hi, hai]
  · have hai : i ∉ a := fun h => hi (ha h)
    simp [f, hi, hai]

/-- Every strictly interior finite assignment has positive probability inside
any positive measurable event determined by its complementary coordinates. -/
theorem prodBernoulli_inter_pattern_pos [DecidableEq ι] (p : ι → unitInterval)
    (F a : Finset ι) (ha : a ⊆ F) (B : Set (Set ι)) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set ι, ω \ (F : Set ι) = ω' \ (F : Set ι) →
      (ω ∈ B ↔ ω' ∈ B)) (hpos : 0 < prodBernoulli p B)
    (hp : ∀ i ∈ F, 0 < p i ∧ p i < 1) :
    0 < prodBernoulli p (B ∩ {ω | ω ∩ (F : Set ι) = (a : Set ι)}) := by
  rw [prodBernoulli_inter_pattern p F a ha B hB houtside]
  apply pos_iff_ne_zero.mpr
  apply mul_ne_zero (mul_ne_zero (ne_of_gt hpos) ?_) ?_
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have h : 0 < unitInterval.toNNReal (p i) := (hp i (ha hi)).1
    exact ne_of_gt (by exact_mod_cast h)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have h : 0 < unitInterval.toNNReal (unitInterval.symm (p i)) := by
      change 0 < (unitInterval.symm (p i) : ℝ)
      rw [unitInterval.coe_symm_eq]
      exact sub_pos.mpr (hp i (Finset.mem_sdiff.mp hi).1).2
    exact ne_of_gt (by exact_mod_cast h)

/-- Inserting a single bond fixes its marginal at one, even for a loop. -/
theorem prodBernoulli_map_insert_bond {V : Type*} [DecidableEq (Sym2 V)]
    (p : Sym2 V → unitInterval) (e : Sym2 V) :
    (prodBernoulli p).map (fun ω => insert e ω) =
      prodBernoulli (Function.update p e 1) := by
  have hp : (fun i => if i ∈ ({e} : Set (Sym2 V)) then
      (if i ∈ ({e} : Set (Sym2 V)) then (1 : unitInterval) else 0) else p i) =
      Function.update p e 1 := by
    funext i
    by_cases h : i = e <;> simp [h]
  have h := prodBernoulli_map_overwrite p {e} {e} (Set.Subset.refl _)
  rw [hp] at h
  have hf : (fun ω : Set (Sym2 V) => (ω \ {e}) ∪ {e}) = fun ω => insert e ω := by
    funext ω
    ext i
    by_cases hi : i = e <;> simp [hi]
  rw [hf] at h
  exact h

/-- Deleting a single bond fixes its marginal at zero, even for a loop. -/
theorem prodBernoulli_map_delete_bond {V : Type*} [DecidableEq (Sym2 V)]
    (p : Sym2 V → unitInterval) (e : Sym2 V) :
    (prodBernoulli p).map (fun ω => ω \ {e}) =
      prodBernoulli (Function.update p e 0) := by
  have hp : (fun i => if i ∈ ({e} : Set (Sym2 V)) then
      (if i ∈ (∅ : Set (Sym2 V)) then (1 : unitInterval) else 0) else p i) =
      Function.update p e 0 := by
    funext i
    simp [Function.update_apply]
  simpa only [hp, Set.union_empty] using
    prodBernoulli_map_overwrite p {e} ∅ (Set.empty_subset _)

/-- The one-bond open factor is independent of any measurable event determined
by all other bonds. No non-diagonal hypothesis is needed. -/
theorem prodBernoulli_inter_bond_open {V : Type*} (p : Sym2 V → unitInterval)
    (e : Sym2 V) (B : Set (Set (Sym2 V))) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set (Sym2 V), ω \ {e} = ω' \ {e} → (ω ∈ B ↔ ω' ∈ B)) :
    prodBernoulli p (B ∩ {ω | e ∈ ω}) =
      prodBernoulli p B * (unitInterval.toNNReal (p e) : ℝ≥0∞) := by
  classical
  have heq : {ω : Set (Sym2 V) | ω ∩ {e} = {e}} = {ω | e ∈ ω} := by
    ext ω
    simp [Set.inter_eq_right]
  simpa [heq] using prodBernoulli_inter_pattern p {e} {e} (Finset.Subset.refl _)
    B hB (by simpa using houtside)

/-- The one-bond closed factor, including diagonal bonds. -/
theorem prodBernoulli_inter_bond_closed {V : Type*} (p : Sym2 V → unitInterval)
    (e : Sym2 V) (B : Set (Set (Sym2 V))) (hB : MeasurableSet B)
    (houtside : ∀ ω ω' : Set (Sym2 V), ω \ {e} = ω' \ {e} → (ω ∈ B ↔ ω' ∈ B)) :
    prodBernoulli p (B ∩ {ω | e ∉ ω}) = prodBernoulli p B *
      (unitInterval.toNNReal (unitInterval.symm (p e)) : ℝ≥0∞) := by
  classical
  simpa [Set.inter_singleton_eq_empty] using
    prodBernoulli_inter_pattern p {e} ∅ (Finset.empty_subset _) B hB (by simpa using houtside)

-- Endpoint, empty-block, non-vacuity, and diagonal witnesses.
example : prodBernoulli (fun b : Bool => if b then 1 else 0)
    {ω | ω ∩ ({false, true} : Set Bool) = {true}} = 1 := by
  simpa using prodBernoulli_inter_finset_eq (fun b : Bool => if b then 1 else 0)
    {false, true} {true} (by simp)

example (p : ι → unitInterval) (B : Set (Set ι)) :
    prodBernoulli p (B ∩ {ω | ω ∩ (∅ : Set ι) = ∅}) = prodBernoulli p B := by
  simp

example : 0 < prodBernoulli (fun _ : Bool => ⟨(1/2 : ℝ), by constructor <;> norm_num⟩)
    {ω | ω ∩ ({false, true} : Set Bool) = {true}} := by
  simpa using prodBernoulli_inter_pattern_pos
    (fun _ : Bool => ⟨(1/2 : ℝ), by constructor <;> norm_num⟩)
    {false, true} {true} (by simp) Set.univ MeasurableSet.univ
    (by simp) (by simp) (by
        intro i hi
        constructor
        · change (0 : ℝ) < 1 / 2
          norm_num
        · change (1 / 2 : ℝ) < 1
          norm_num)

example (p : Sym2 Bool → unitInterval) :
    prodBernoulli p {ω | s(false, false) ∉ ω} =
      (unitInterval.toNNReal (unitInterval.symm (p s(false, false))) : ℝ≥0∞) := by
  simpa using prodBernoulli_inter_bond_closed p s(false, false) Set.univ
    MeasurableSet.univ (by simp)

end PercLib.Probability
