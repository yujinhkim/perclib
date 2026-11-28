/-
A compiled counterexample showing that the invariance hypothesis `SelfDetermined` of
`PercLib.CriticalLRP.Correlation.Gladkov.RandomAmalgam` cannot be dropped.

Setting: `ι = Unit`, so a configuration is a pair of bits `(C1, C2)`. The revealed set is
`{()}` exactly when the first copy is open and the second is closed at the only coordinate,
and `∅` otherwise. This is a measurable selection from the two-member family
`{univ, ∅}`, but the coordinate can be *excluded* from `S` only by inspecting it, so `S` is
not self-determined.

The conclusion of the amalgamation lemma genuinely fails: `C2 →_S C1` contains the
coordinate exactly when both copies are open there, an event of probability `1/4` under
`q ≡ 1/2`, whereas its law should put mass `1/2` on that coordinate. Membership of a
coordinate is thus being decided *after* it is revealed, which is precisely what
[GZ24, Lemma 4.2] forbids by assigning each coordinate to `S` before revealing it.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.RandomAmalgam

/-!
# The invariance hypothesis is not automatic

This file compiles the failure of the random-`T` amalgamation conclusion for a measurable
revealed set that is not self-determined: the amalgamated configuration does not have the
original law, so it cannot be independent of the complementary amalgamation with the
original marginals.
-/

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.GladkovAmalgam

/-- The constant open probability `1/2` on the one-point index type. -/
noncomputable def halfUnit : Unit → unitInterval := fun _ => ⟨1/2, by norm_num⟩

/-- The two-member family of revealed sets: index `1` reveals the only coordinate. -/
noncomputable def badFam : ℕ → Set Unit := fun n => if n = 1 then Set.univ else ∅

/-- Reveal the coordinate when the first copy is open and the second is closed there. This
inspects the coordinate it decides about, so it is not self-determined. -/
noncomputable def badIdx (ω : Set (Unit × Bool)) : ℕ := by
  classical
  exact if ((), false) ∈ ω ∧ ((), true) ∉ ω then 1 else 0

theorem badFam_zero : badFam 0 = (∅ : Set Unit) := by
  unfold badFam
  split_ifs <;> simp_all

theorem badFam_one : badFam 1 = (Set.univ : Set Unit) := by
  unfold badFam
  split_ifs <;> simp_all

/-- On the branch that reveals the coordinate, the index is `1`. -/
theorem badIdx_of_mixed (ω : Set (Unit × Bool)) (hf : ((), false) ∈ ω)
    (ht : ((), true) ∉ ω) : badIdx ω = 1 := by
  unfold badIdx
  split_ifs
  · rfl
  · simp_all

/-- On every other branch the index is `0`. -/
theorem badIdx_of_not (ω : Set (Unit × Bool))
    (h : ¬(((), false) ∈ ω ∧ ((), true) ∉ ω)) : badIdx ω = 0 := by
  unfold badIdx
  split_ifs
  simp_all

/-- The selection is measurable: every set of configurations is measurable here. -/
theorem badFam_measurable :
    ∀ i : Unit, MeasurableSet {ω : Set (Unit × Bool) | i ∈ badFam (badIdx ω)} :=
  fun _ => MeasurableSet.of_discrete

/-- The selection violates self-determination: the two configurations in which exactly one
copy is open at the only coordinate agree on the revealed coordinates of the first, yet
they select different indices. -/
theorem badIdx_not_selfDetermined : ¬ SelfDetermined badFam badIdx := by
  intro h
  have h0 : badIdx ({((), true)} : Set (Unit × Bool)) = 0 :=
    badIdx_of_not _ (by simp)
  have h1 : badIdx ({((), false)} : Set (Unit × Bool)) = 1 :=
    badIdx_of_mixed _ (by simp) (by simp)
  have hagree : ({((), true)} : Set (Unit × Bool)) ∩
        {x : Unit × Bool | x.1 ∈ badFam (badIdx {((), true)})} =
      ({((), false)} : Set (Unit × Bool)) ∩
        {x : Unit × Bool | x.1 ∈ badFam (badIdx {((), true)})} := by
    rw [h0, badFam_zero]
    simp
  have hne := h _ _ hagree
  rw [h0, h1] at hne
  exact absurd hne (by decide)

/-! ### The failing event -/

theorem mem_amalSecond_empty (ω : Set (Unit × Bool)) :
    () ∈ amalSecond (∅ : Set Unit) ω ↔ ((), false) ∈ ω := by
  simp [amalSecond]

theorem mem_amalSecond_univ (ω : Set (Unit × Bool)) :
    () ∈ amalSecond (Set.univ : Set Unit) ω ↔ ((), true) ∈ ω := by
  simp [amalSecond]

/-- **The failure.** With this revealed set, the second amalgamation contains the only
coordinate exactly when both copies are open there. -/
theorem bad_amalSecond_iff (ω : Set (Unit × Bool)) :
    () ∈ amalSecondRand badFam badIdx ω ↔ ((), false) ∈ ω ∧ ((), true) ∈ ω := by
  by_cases hf : ((), false) ∈ ω <;> by_cases ht : ((), true) ∈ ω
  · rw [amalSecondRand, revealed, badIdx_of_not ω (by simp [ht]), badFam_zero,
      mem_amalSecond_empty]
    exact iff_of_true hf ⟨hf, ht⟩
  · rw [amalSecondRand, revealed, badIdx_of_mixed ω hf ht, badFam_one, mem_amalSecond_univ]
    exact iff_of_false ht (by simp [ht])
  · rw [amalSecondRand, revealed, badIdx_of_not ω (by simp [hf]), badFam_zero,
      mem_amalSecond_empty]
    exact iff_of_false hf (by simp [hf])
  · rw [amalSecondRand, revealed, badIdx_of_not ω (by simp [hf]), badFam_zero,
      mem_amalSecond_empty]
    exact iff_of_false hf (by simp [hf])

theorem bad_amalSecond_eq :
    {ω : Set (Unit × Bool) | () ∈ amalSecondRand badFam badIdx ω} =
      {ω : Set (Unit × Bool) |
        ((↑({((), false), ((), true)} : Finset (Unit × Bool)) : Set (Unit × Bool)) ⊆ ω)} := by
  ext ω
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, bad_amalSecond_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  · intro h
    exact ⟨h (by simp), h (by simp)⟩

/-- The mass of the failing event is `1/4` under `q ≡ 1/2`. -/
theorem bad_second_mass :
    prodBernoulli (twoProfile halfUnit)
      {ω : Set (Unit × Bool) | () ∈ amalSecondRand badFam badIdx ω} =
        ((1/4 : ℝ≥0) : ℝ≥0∞) := by
  have hprod : ∏ x ∈ ({((), false), ((), true)} : Finset (Unit × Bool)),
      (unitInterval.toNNReal (twoProfile halfUnit x) : ℝ≥0∞) = ((1/4 : ℝ≥0) : ℝ≥0∞) := by
    rw [Finset.prod_insert (by simp), Finset.prod_singleton]
    have h1 : unitInterval.toNNReal (twoProfile halfUnit ((), false)) = 1/2 := rfl
    have h2 : unitInterval.toNNReal (twoProfile halfUnit ((), true)) = 1/2 := rfl
    rw [h1, h2, ← ENNReal.coe_mul]
    norm_num
  rw [bad_amalSecond_eq, prodBernoulli_subset]
  exact hprod

/-- The original law puts mass `1/2` on the same coordinate. -/
theorem good_mass :
    prodBernoulli halfUnit {s : Set Unit | () ∈ s} = ((1/2 : ℝ≥0) : ℝ≥0∞) := by
  rw [prodBernoulli_setOf_mem]
  rfl

/-- **The independence conclusion needs more than measurability.** There is a measurable
selection of the revealed set for which `C2 →_S C1` does not have the original law; hence
no random-`T` version of the amalgamation lemma can drop the invariance hypothesis. -/
theorem not_marginal_automatic :
    ¬ (∀ (Sfam : ℕ → Set Unit) (idx : Set (Unit × Bool) → ℕ),
        (∀ i : Unit, MeasurableSet {ω : Set (Unit × Bool) | i ∈ Sfam (idx ω)}) →
        ∀ A : Set (Set Unit), MeasurableSet A →
          prodBernoulli (twoProfile halfUnit) {ω : Set (Unit × Bool) |
            amalSecondRand Sfam idx ω ∈ A} = prodBernoulli halfUnit A) := by
  intro h
  have hbad := h badFam badIdx badFam_measurable {s : Set Unit | () ∈ s}
    (measurableSet_mem ())
  rw [show {ω : Set (Unit × Bool) | amalSecondRand badFam badIdx ω ∈ {s : Set Unit | () ∈ s}}
      = {ω : Set (Unit × Bool) | () ∈ amalSecondRand badFam badIdx ω} from rfl,
    bad_second_mass, good_mass] at hbad
  exact absurd hbad (by norm_num)

/-! ### A second witness: a tree with assignments made before revealing

The next witness has exactly the shape of a decision tree that assigns each coordinate to
`S` or its complement *before* revealing it. The tree queries `false` first and assigns it to
the complement; on the branch `(C1(false), C2(false)) = (true, false)` it queries `true`,
assigns it to `S`, and stops; on every other branch it stops immediately. Hence
`S = {true}` exactly when `(C1(false), C2(false)) = (true, false)`.

This `S` is realizable by an "assign before reveal" tree, yet it is not self-determined: the
membership of `true` in `S` is decided by the values at `false`, which is not in `S`. So the
invariance hypothesis of the main theorem and the [GZ24, Lemma 4.2] hypothesis are genuinely
different conditions, and formalising the latter still needs the sequential transcript
argument. -/

/-- The revealed family of the two-coordinate tree: index `1` reveals `true`. -/
noncomputable def treeFam (n : ℕ) : Set Bool :=
  if n = 1 then {true} else ∅

/-- The index of the two-coordinate tree. -/
noncomputable def treeIdx (ω : Set (Bool × Bool)) : ℕ := by
  classical
  exact if (false, false) ∈ ω ∧ (false, true) ∉ ω then 1 else 0

theorem treeFam_zero : treeFam 0 = (∅ : Set Bool) := by
  unfold treeFam
  split_ifs <;> simp_all

theorem treeFam_one : treeFam 1 = ({true} : Set Bool) := by
  unfold treeFam
  split_ifs <;> simp_all

theorem treeIdx_of_mixed (ω : Set (Bool × Bool)) (hf : (false, false) ∈ ω)
    (ht : (false, true) ∉ ω) : treeIdx ω = 1 := by
  unfold treeIdx
  split_ifs
  · rfl
  · simp_all

theorem treeIdx_of_not (ω : Set (Bool × Bool))
    (h : ¬((false, false) ∈ ω ∧ (false, true) ∉ ω)) : treeIdx ω = 0 := by
  unfold treeIdx
  split_ifs
  simp_all

/-- **The "assign before reveal" tree is not self-determined.**  The configuration
`{(false,false), (true,false)}` has both copies open at `true` and first copy open at
`false`, so the tree reveals `true`; the configuration `{(false,true), (true,false)}`
agrees with it on the coordinate `true` in both copies, yet the tree stops immediately on it
and reveals nothing. -/
theorem treeIdx_not_selfDetermined : ¬ SelfDetermined treeFam treeIdx := by
  intro h
  have h0 : treeIdx ({((false, false)), ((true, false))} : Set (Bool × Bool)) = 1 := by
    refine treeIdx_of_mixed _ ?_ ?_ <;> simp
  have h1 : treeIdx ({((false, true)), ((true, false))} : Set (Bool × Bool)) = 0 := by
    refine treeIdx_of_not _ ?_
    simp
  have hagree : ({((false, false)), ((true, false))} : Set (Bool × Bool)) ∩
        {x : Bool × Bool | x.1 ∈ treeFam (treeIdx {((false, false)), ((true, false))})} =
      ({((false, true)), ((true, false))} : Set (Bool × Bool)) ∩
        {x : Bool × Bool | x.1 ∈ treeFam (treeIdx {((false, false)), ((true, false))})} := by
    rw [h0, treeFam_one]
    ext x
    obtain ⟨e, b⟩ := x
    cases e <;> cases b <;> simp
  have hne := h _ _ hagree
  rw [h0, h1] at hne
  exact absurd hne (by decide)

end PercLib.GladkovAmalgam
