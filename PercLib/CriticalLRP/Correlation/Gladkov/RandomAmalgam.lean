/-
Amalgamation over a randomly revealed set, extending the deterministic case in
`PercLib.CriticalLRP.Correlation.Gladkov.Amalgam`.

Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2,
Lemma 3.1 (= [GZ24, Lemma 4.2]), states the independence for a revealed set
`S(C1, C2)` produced by a decision tree. This file proves a random-`T` version
under an explicit invariance hypothesis on the revealed set, and the companion
file `RandomAmalgamCounterexample.lean` shows that hypothesis is not automatic.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.Amalgam

/-!
# Amalgamation over a random revealed set

Let `μ = prodBernoulli (twoProfile q)` be the law of two independent copies
`C1, C2` of a Bernoulli configuration on `ι`, and let `S(ω)` be a revealed set that is
selected measurably from a *countable* family of sets `Sfam : ℕ → Set ι`.

The main theorem `prodBernoulli_random_amalgam_indep` proves Gladkov's conclusion

`(C1 →_S C2)` and `(C2 →_S C1)` are independent, each with law `prodBernoulli q`,

for the random revealed set `S`, under two hypotheses beyond the choice of `Sfam` and
of the selection map `idx`:

* `hS`: the set-valued map `ω ↦ Sfam (idx ω)` is measurable;
* `hInv` (`SelfDetermined`): `S(ω)` depends only on `ω` restricted to the coordinates
  of `S(ω)` itself, in both copies. Equivalently, `S` is invariant under changing the
  configuration off the revealed set.

The proof only uses the deterministic lemma together with a countable partition of the
underlying probability space: on the fibre `{idx = n}` the random amalgamation is the
deterministic amalgamation over `Sfam n`, and the flip off `Sfam n` preserves that fibre
precisely because of `hInv`. Every weight in the resulting `tsum` is the actual
probability of a fibre, so no indicator weight is ever borrowed. The flip is the
measure preserving involution `flipConfig (Sfam n)` of the deterministic file.

`SelfDetermined` holds for the cluster-boundary revealed sets of [GZ24, Example 4.4]
(the revealed set contains every coordinate its value depends on), and for the
degenerate families that select a fixed set or `univ`.

Scope: the revealed set is required to be selected from a *countable* family `Sfam : ℕ → Set ι`.
This is exactly [GZ24, Lemma 4.2]'s setting of a finite graph, where only finitely many sets
`S` are possible, so an index `idx : Set (ι × Bool) → ℕ` always exists. For an infinite graph
the family of possible revealed sets can be uncountable, and the partition argument would need
either the countability of the atoms of positive mass or the decision-tree formalisation
below; neither is done here.

`SelfDetermined` does *not* follow from measurability (`RandomAmalgamCounterexample.lean`
compiles a witness whose conclusion fails), and it is not [GZ24, Lemma 4.2]'s hypothesis
either: that lemma assigns each coordinate to `S` or its complement *before* revealing it,
which is a property of the decision tree rather than of the resulting map `ω ↦ S(ω)`. The
same file compiles an "assign before reveal" tree that is not self-determined. Formalising
the general lemma therefore still needs the sequential transcript argument, which is not
done here.
-/

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

variable {ι : Type*}

/-! ### The random revealed set and its amalgamations -/

/-- The revealed set, selected from the countable family `Sfam` by the index `idx`. -/
def revealed (Sfam : ℕ → Set ι) (idx : Set (ι × Bool) → ℕ) (ω : Set (ι × Bool)) : Set ι :=
  Sfam (idx ω)

/-- `C1 →_S C2` for the random revealed set `S = revealed Sfam idx ω`. -/
def amalFirstRand (Sfam : ℕ → Set ι) (idx : Set (ι × Bool) → ℕ)
    (ω : Set (ι × Bool)) : Set ι :=
  amalFirst (revealed Sfam idx ω) ω

/-- `C2 →_S C1` for the random revealed set `S = revealed Sfam idx ω`. -/
def amalSecondRand (Sfam : ℕ → Set ι) (idx : Set (ι × Bool) → ℕ)
    (ω : Set (ι × Bool)) : Set ι :=
  amalSecond (revealed Sfam idx ω) ω

/-- The fibre of the selection map on which it takes the value `n`. -/
def fiber (idx : Set (ι × Bool) → ℕ) (n : ℕ) : Set (Set (ι × Bool)) := {ω | idx ω = n}

@[simp] theorem mem_fiber {idx : Set (ι × Bool) → ℕ} {n : ℕ} {ω : Set (ι × Bool)} :
    ω ∈ fiber idx n ↔ idx ω = n := Iff.rfl

/-- **Self-determination of the revealed set.** Two configurations that agree on the
revealed coordinates of the first (in both copies) select the same revealed set. This is
the off-`T` invariance hypothesis: `S(ω)` depends only on `ω` restricted to `S(ω)`. -/
def SelfDetermined (Sfam : ℕ → Set ι) (idx : Set (ι × Bool) → ℕ) : Prop :=
  ∀ ω ω' : Set (ι × Bool),
    ω ∩ {x : ι × Bool | x.1 ∈ Sfam (idx ω)} = ω' ∩ {x : ι × Bool | x.1 ∈ Sfam (idx ω)} →
      idx ω' = idx ω

/-! ### Measurability of the amalgamations -/

/-- The indicator of a revealed coordinate is a measurable function of the configuration,
provided the selected set is measurable as a set of coordinates. -/
theorem measurable_revealed_mem {Sfam : ℕ → Set ι} {idx : Set (ι × Bool) → ℕ}
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)}) (i : ι) :
    MeasurableSet {ω : Set (ι × Bool) | i ∈ revealed Sfam idx ω} := hS i

theorem measurable_amalFirstRand {Sfam : ℕ → Set ι} {idx : Set (ι × Bool) → ℕ}
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)}) :
    Measurable (amalFirstRand Sfam idx) := by
  refine Measurable.of_mem fun i => ?_
  have hEq : (fun ω : Set (ι × Bool) => i ∈ amalFirstRand Sfam idx ω) =
      fun ω => (i ∈ Sfam (idx ω) ∧ (i, false) ∈ ω) ∨ (i ∉ Sfam (idx ω) ∧ (i, true) ∈ ω) := by
    funext ω
    simp [amalFirstRand, revealed, amalFirst]
  rw [hEq]
  have h1 : Measurable fun ω : Set (ι × Bool) => i ∈ Sfam (idx ω) :=
    measurableSet_setOfPred.mp (hS i)
  exact (h1.and (measurable_set_mem (i, false))).or
    (h1.not.and (measurable_set_mem (i, true)))

theorem measurable_amalSecondRand {Sfam : ℕ → Set ι} {idx : Set (ι × Bool) → ℕ}
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)}) :
    Measurable (amalSecondRand Sfam idx) := by
  refine Measurable.of_mem fun i => ?_
  have hEq : (fun ω : Set (ι × Bool) => i ∈ amalSecondRand Sfam idx ω) =
      fun ω => (i ∈ Sfam (idx ω) ∧ (i, true) ∈ ω) ∨ (i ∉ Sfam (idx ω) ∧ (i, false) ∈ ω) := by
    funext ω
    simp [amalSecondRand, revealed, amalSecond]
  rw [hEq]
  have h1 : Measurable fun ω : Set (ι × Bool) => i ∈ Sfam (idx ω) :=
    measurableSet_setOfPred.mp (hS i)
  exact (h1.and (measurable_set_mem (i, true))).or
    (h1.not.and (measurable_set_mem (i, false)))

/-! ### The flip fixes the revealed coordinates -/

/-- The flip off `T` fixes every coordinate whose first component lies in `T`. -/
theorem flipIdx_eq_self {T : Set ι} {x : ι × Bool} (hx : x.1 ∈ T) : flipIdx T x = x := by
  obtain ⟨i, b⟩ := x
  simp [flipIdx, hx]

/-- Flipping off `T` does not change the configuration on `T` (in either copy). -/
theorem flipConfig_inter_revealed (T : Set ι) (ω : Set (ι × Bool)) :
    flipConfig T ω ∩ {x : ι × Bool | x.1 ∈ T} = ω ∩ {x : ι × Bool | x.1 ∈ T} := by
  ext x
  obtain ⟨i, b⟩ := x
  by_cases hi : i ∈ T
  · simp [flipConfig, flipIdx, hi]
  · simp [hi]

/-- **The flip preserves the fibre.** This is where `SelfDetermined` is used: flipping off
the revealed set leaves the configuration on the revealed set unchanged, so the revealed
set itself is unchanged. -/
theorem idx_flipConfig_eq {Sfam : ℕ → Set ι} {idx : Set (ι × Bool) → ℕ}
    (hInv : SelfDetermined Sfam idx) (ω : Set (ι × Bool)) :
    idx (flipConfig (Sfam (idx ω)) ω) = idx ω :=
  hInv ω _ (flipConfig_inter_revealed (Sfam (idx ω)) ω).symm

theorem preimage_fiber_flipConfig {Sfam : ℕ → Set ι} {idx : Set (ι × Bool) → ℕ}
    (hInv : SelfDetermined Sfam idx) (n : ℕ) :
    (flipConfig (Sfam n)) ⁻¹' fiber idx n = fiber idx n := by
  ext ω
  constructor
  · intro h
    have hstep := idx_flipConfig_eq hInv (flipConfig (Sfam n) ω)
    rw [h, flipConfig_involutive] at hstep
    exact hstep
  · intro h
    have h1 : idx (flipConfig (Sfam (idx ω)) ω) = n := by
      rw [idx_flipConfig_eq hInv ω, h]
    rwa [h] at h1

/-! ### The main theorem -/

/-- **Random revealed set amalgamation.** For a revealed set selected measurably from a
countable family and satisfying self-determination, the two amalgamations
`C1 →_S C2` and `C2 →_S C1` are independent and each has the original law.

The joint probability is computed by partitioning over the countable family of fibres and
using the deterministic flip on each fibre; the weights appearing in the `tsum` are the
actual probabilities of the fibres. -/
theorem prodBernoulli_random_amalgam_indep (q : ι → unitInterval) {Sfam : ℕ → Set ι}
    {idx : Set (ι × Bool) → ℕ} (hidx : Measurable idx)
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)})
    (hInv : SelfDetermined Sfam idx) {A B : Set (Set ι)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    prodBernoulli (twoProfile q) {ω : Set (ι × Bool) |
        amalFirstRand Sfam idx ω ∈ A ∧ amalSecondRand Sfam idx ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  have hFirst := measurable_amalFirstRand (Sfam := Sfam) (idx := idx) hS
  have hSecond := measurable_amalSecondRand (Sfam := Sfam) (idx := idx) hS
  have hE : MeasurableSet {ω : Set (ι × Bool) |
      amalFirstRand Sfam idx ω ∈ A ∧ amalSecondRand Sfam idx ω ∈ B} :=
    (hA.preimage hFirst).inter (hB.preimage hSecond)
  have hC : MeasurableSet {ω : Set (ι × Bool) | copy false ω ∈ A ∧ copy true ω ∈ B} :=
    (hA.preimage (measurable_copy false)).inter (hB.preimage (measurable_copy true))
  have hfiber : ∀ n : ℕ, MeasurableSet (fiber idx n) := fun n =>
    hidx (measurableSet_singleton n)
  have hdisj : Pairwise (Function.onFun Disjoint (fiber idx)) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro ω hm hn
    exact hmn (Eq.trans (Eq.symm (mem_fiber.mp hm)) (mem_fiber.mp hn))
  have hstep : ∀ n : ℕ,
      prodBernoulli (twoProfile q) (fiber idx n ∩ {ω : Set (ι × Bool) |
          amalFirstRand Sfam idx ω ∈ A ∧ amalSecondRand Sfam idx ω ∈ B}) =
      prodBernoulli (twoProfile q) (fiber idx n ∩ {ω : Set (ι × Bool) |
          copy false ω ∈ A ∧ copy true ω ∈ B}) := by
    intro n
    have hFixedMeas : MeasurableSet (fiber idx n ∩ {ω : Set (ι × Bool) |
        amalFirst (Sfam n) ω ∈ A ∧ amalSecond (Sfam n) ω ∈ B}) :=
      (hfiber n).inter ((hA.preimage (measurable_amalFirst (Sfam n))).inter
        (hB.preimage (measurable_amalSecond (Sfam n))))
    have hRand : fiber idx n ∩ {ω : Set (ι × Bool) |
        amalFirstRand Sfam idx ω ∈ A ∧ amalSecondRand Sfam idx ω ∈ B} =
        fiber idx n ∩ {ω : Set (ι × Bool) |
          amalFirst (Sfam n) ω ∈ A ∧ amalSecond (Sfam n) ω ∈ B} := by
      ext ω
      by_cases h : idx ω = n
      · simp [h, amalFirstRand, amalSecondRand, revealed]
      · simp [h]
    have hpre : (flipConfig (Sfam n)) ⁻¹' {ω : Set (ι × Bool) |
        amalFirst (Sfam n) ω ∈ A ∧ amalSecond (Sfam n) ω ∈ B} =
        {ω : Set (ι × Bool) | copy false ω ∈ A ∧ copy true ω ∈ B} := by
      ext ω
      simp [amalFirst_flipConfig, amalSecond_flipConfig]
    have hmap : (prodBernoulli (twoProfile q)).map (flipConfig (Sfam n)) =
        prodBernoulli (twoProfile q) := flipConfig_map q (Sfam n)
    have hmove : prodBernoulli (twoProfile q) (fiber idx n ∩ {ω : Set (ι × Bool) |
        amalFirst (Sfam n) ω ∈ A ∧ amalSecond (Sfam n) ω ∈ B}) =
        prodBernoulli (twoProfile q) ((flipConfig (Sfam n)) ⁻¹' (fiber idx n ∩
          {ω : Set (ι × Bool) | amalFirst (Sfam n) ω ∈ A ∧
            amalSecond (Sfam n) ω ∈ B})) := by
      calc prodBernoulli (twoProfile q) (fiber idx n ∩ {ω : Set (ι × Bool) |
            amalFirst (Sfam n) ω ∈ A ∧ amalSecond (Sfam n) ω ∈ B})
          = (prodBernoulli (twoProfile q)).map (flipConfig (Sfam n)) (fiber idx n ∩
              {ω : Set (ι × Bool) | amalFirst (Sfam n) ω ∈ A ∧
                amalSecond (Sfam n) ω ∈ B}) := by rw [hmap]
        _ = prodBernoulli (twoProfile q) ((flipConfig (Sfam n)) ⁻¹' (fiber idx n ∩
              {ω : Set (ι × Bool) | amalFirst (Sfam n) ω ∈ A ∧
                amalSecond (Sfam n) ω ∈ B})) :=
              Measure.map_apply (measurable_flipConfig (Sfam n)) hFixedMeas
    rw [hRand, hmove, Set.preimage_inter, preimage_fiber_flipConfig hInv n, hpre]
  have hunion : ∀ C : Set (Set (ι × Bool)), (⋃ n, fiber idx n ∩ C) = C := by
    intro C
    rw [← Set.iUnion_inter]
    have hcover : (⋃ n, fiber idx n) = Set.univ := by
      ext ω
      simp [fiber]
    rw [hcover, Set.univ_inter]
  have hcopy1 : prodBernoulli (twoProfile q) {ω : Set (ι × Bool) | copy false ω ∈ A} =
      prodBernoulli q A := by
    rw [← map_copy q false]
    exact (Measure.map_apply (measurable_copy false) hA).symm
  have hcopy2 : prodBernoulli (twoProfile q) {ω : Set (ι × Bool) | copy true ω ∈ B} =
      prodBernoulli q B := by
    rw [← map_copy q true]
    exact (Measure.map_apply (measurable_copy true) hB).symm
  have hdisj' : ∀ C : Set (Set (ι × Bool)),
      Pairwise (Function.onFun Disjoint fun n => fiber idx n ∩ C) := by
    intro C m n hmn
    exact (hdisj hmn).mono (Set.inter_subset_left) (Set.inter_subset_left)
  calc prodBernoulli (twoProfile q) {ω : Set (ι × Bool) |
        amalFirstRand Sfam idx ω ∈ A ∧ amalSecondRand Sfam idx ω ∈ B}
      = prodBernoulli (twoProfile q) (⋃ n, fiber idx n ∩ {ω : Set (ι × Bool) |
          amalFirstRand Sfam idx ω ∈ A ∧ amalSecondRand Sfam idx ω ∈ B}) := by
        rw [hunion]
    _ = ∑' n, prodBernoulli (twoProfile q) (fiber idx n ∩ {ω : Set (ι × Bool) |
          amalFirstRand Sfam idx ω ∈ A ∧ amalSecondRand Sfam idx ω ∈ B}) := by
        refine measure_iUnion (hdisj' _) fun n => (hfiber n).inter hE
    _ = ∑' n, prodBernoulli (twoProfile q) (fiber idx n ∩ {ω : Set (ι × Bool) |
          copy false ω ∈ A ∧ copy true ω ∈ B}) := tsum_congr hstep
    _ = prodBernoulli (twoProfile q) (⋃ n, fiber idx n ∩ {ω : Set (ι × Bool) |
          copy false ω ∈ A ∧ copy true ω ∈ B}) := by
        refine (measure_iUnion (hdisj' _) fun n => (hfiber n).inter hC).symm
    _ = prodBernoulli (twoProfile q) {ω : Set (ι × Bool) |
          copy false ω ∈ A ∧ copy true ω ∈ B} := by rw [hunion]
    _ = prodBernoulli (twoProfile q) {ω : Set (ι × Bool) | copy false ω ∈ A} *
          prodBernoulli (twoProfile q) {ω : Set (ι × Bool) | copy true ω ∈ B} :=
        copy_indep q hA hB
    _ = prodBernoulli q A * prodBernoulli q B := by rw [hcopy1, hcopy2]

/-- The first random amalgamation alone has the original law. -/
theorem prodBernoulli_random_amalFirst (q : ι → unitInterval) {Sfam : ℕ → Set ι}
    {idx : Set (ι × Bool) → ℕ} (hidx : Measurable idx)
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)})
    (hInv : SelfDetermined Sfam idx) {A : Set (Set ι)} (hA : MeasurableSet A) :
    prodBernoulli (twoProfile q) {ω : Set (ι × Bool) | amalFirstRand Sfam idx ω ∈ A} =
      prodBernoulli q A := by
  have h := prodBernoulli_random_amalgam_indep q hidx hS hInv hA MeasurableSet.univ
  simpa using h

/-- The second random amalgamation alone has the original law. -/
theorem prodBernoulli_random_amalSecond (q : ι → unitInterval) {Sfam : ℕ → Set ι}
    {idx : Set (ι × Bool) → ℕ} (hidx : Measurable idx)
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)})
    (hInv : SelfDetermined Sfam idx) {B : Set (Set ι)} (hB : MeasurableSet B) :
    prodBernoulli (twoProfile q) {ω : Set (ι × Bool) | amalSecondRand Sfam idx ω ∈ B} =
      prodBernoulli q B := by
  have h := prodBernoulli_random_amalgam_indep q hidx hS hInv MeasurableSet.univ hB
  simpa using h

/-- The random amalgamation has the original law, as an identity of push-forward laws. -/
theorem map_random_amalFirst (q : ι → unitInterval) {Sfam : ℕ → Set ι}
    {idx : Set (ι × Bool) → ℕ} (hidx : Measurable idx)
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)})
    (hInv : SelfDetermined Sfam idx) :
    (prodBernoulli (twoProfile q)).map (amalFirstRand Sfam idx) = prodBernoulli q := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_amalFirstRand hS) hA]
  exact prodBernoulli_random_amalFirst q hidx hS hInv hA

/-- **The joint law of the random amalgamations.** As an identity of push-forward laws, the
pair of random amalgamations is a pair of independent configurations with the original law. -/
theorem map_random_amalgam_prod (q : ι → unitInterval) {Sfam : ℕ → Set ι}
    {idx : Set (ι × Bool) → ℕ} (hidx : Measurable idx)
    (hS : ∀ i : ι, MeasurableSet {ω : Set (ι × Bool) | i ∈ Sfam (idx ω)})
    (hInv : SelfDetermined Sfam idx) :
    (prodBernoulli (twoProfile q)).map
        (fun ω : Set (ι × Bool) => (amalFirstRand Sfam idx ω, amalSecondRand Sfam idx ω)) =
      (prodBernoulli q).prod (prodBernoulli q) := by
  have hmeas : Measurable fun ω : Set (ι × Bool) =>
      (amalFirstRand Sfam idx ω, amalSecondRand Sfam idx ω) :=
    (measurable_amalFirstRand hS).prodMk (measurable_amalSecondRand hS)
  refine Measure.ext_prod fun {A B} (hA : MeasurableSet A) (hB : MeasurableSet B) => ?_
  rw [Measure.map_apply hmeas (hA.prod hB), Measure.prod_prod]
  exact prodBernoulli_random_amalgam_indep q hidx hS hInv hA hB

/-! ### Non-vacuity: the hypotheses hold for fixed and for total revealed sets -/

/-- A family with a single member, the fixed set `T`: this is the deterministic lemma. -/
theorem selfDetermined_const (T : Set ι) :
    SelfDetermined (fun _ => T) (fun _ => 0) := fun _ _ _ => rfl

/-- A constant index makes every revealed set fixed, so the deterministic lemma applies. -/
theorem random_amalgam_indep_const (q : ι → unitInterval) (T : Set ι)
    {A B : Set (Set ι)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    prodBernoulli (twoProfile q) {ω : Set (ι × Bool) |
        amalFirst T ω ∈ A ∧ amalSecond T ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  have h := prodBernoulli_random_amalgam_indep (Sfam := fun _ => T) (idx := fun _ => 0)
    q measurable_const (fun i => (measurableSet_mem i).preimage measurable_const)
    (selfDetermined_const T) hA hB
  simpa [amalFirstRand, amalSecondRand, revealed] using h

end PercLib.GladkovAmalgam
