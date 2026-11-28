/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Gladkov's amalgamation lemma for an arbitrary decision tree on a finite graph
(arXiv:2408.08457v2, Lemma 3.1 = [GZ24, Lemma 4.2]), proved unconditionally.

Main result: let `σ` be a consistent strategy on the finite edge type `ι` and let
`S(C1,C2)` be the set of queried edges decided `"S"` (edges never queried are not in it).
Then `C1 →_S C2` and `C2 →_S C1` are independent and both have the law of a single
Bernoulli configuration. No self-determination hypothesis and no countable family of
candidate sets is used.

The proof is the reconstruction argument: encoding the pair `(C1 →_S C2, C2 →_S C1)` as
one configuration `treeConfig σ` on `ι × Bool`, the transcript of the run can be recomputed
from the encoded pair by running the tree backwards (`readback`), which shows that
`treeConfig` is injective; and a step decided `"S"` keeps both copies of its edge while a
step decided `"S̄"` (or an unqueried edge) swaps them, so each atom of the product law has
the same mass as its image. Hence `treeConfig` preserves `prodBernoulli (twoProfile q)`,
which gives the joint law.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.Defs
public import PercLib.Probability.Exploration.Transcript

/-!
# The decision-tree amalgamation lemma

`prodBernoulli_treeFirst_second_indep` is the main statement. The deterministic lemma
`PercLib.GladkovAmalgam.amalgam_indep` is the special case of a tree that queries a fixed
set of edges.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

variable {ι : Type*}

/-! ### The bits of a configuration -/

/-- The value of a configuration at one coordinate, as a bit. -/
noncomputable def bitOf {κ : Type*} (ω : Set κ) (x : κ) : Bool := by
  classical
  exact decide (x ∈ ω)

theorem bitOf_eq_true {κ : Type*} {ω : Set κ} {x : κ} : bitOf ω x = true ↔ x ∈ ω := by
  classical
  simp [bitOf]

theorem bitOf_eq_false {κ : Type*} {ω : Set κ} {x : κ} : bitOf ω x = false ↔ x ∉ ω := by
  classical
  simp [bitOf]

theorem bitOf_congr {κ : Type*} {ω ω' : Set κ} {x : κ} (h : x ∈ ω ↔ x ∈ ω') :
    bitOf ω x = bitOf ω' x := by
  by_cases hx : x ∈ ω
  · rw [bitOf_eq_true.2 hx, bitOf_eq_true.2 (h.1 hx)]
  · rw [bitOf_eq_false.2 hx, bitOf_eq_false.2 fun hc => hx (h.2 hc)]

/-- Two coordinates carrying the same value have the same bit, also across configurations. -/
theorem bitOf_eq_of_iff {κ : Type*} {ω ω' : Set κ} {x y : κ} (h : x ∈ ω ↔ y ∈ ω') :
    bitOf ω x = bitOf ω' y := by
  by_cases hx : x ∈ ω
  · rw [bitOf_eq_true.2 hx, bitOf_eq_true.2 (h.1 hx)]
  · rw [bitOf_eq_false.2 hx, bitOf_eq_false.2 fun hc => hx (h.2 hc)]

/-- The bit of a coordinate always equals the bit of its value elsewhere. -/
theorem bitOf_eq_of_iff' {κ κ' : Type*} {ω : Set κ} {ω' : Set κ'} {x : κ} {y : κ'}
    (h : x ∈ ω ↔ y ∈ ω') : bitOf ω x = bitOf ω' y := by
  by_cases hx : x ∈ ω
  · rw [bitOf_eq_true.2 hx, bitOf_eq_true.2 (h.1 hx)]
  · rw [bitOf_eq_false.2 hx, bitOf_eq_false.2 fun hc => hx (h.2 hc)]

theorem bit_eq_bitOf {ν : Set (ι × Bool)} {x : ι × Bool} : bit ν x = bitOf ν x := rfl

/-- Two coordinates carrying the same value have the same bit, even when they sit in
different configurations. -/
theorem bit_eq_of_iff {ν ν' : Set (ι × Bool)} {x y : ι × Bool} (h : x ∈ ν ↔ y ∈ ν') :
    bit ν x = bit ν' y := by
  by_cases hx : x ∈ ν
  · rw [bit_eq_true.2 hx, bit_eq_true.2 (h.1 hx)]
  · rw [bit_eq_false.2 hx, bit_eq_false.2 fun hc => hx (h.2 hc)]

/-! ### Reconstruction of the transcript from the amalgamated pair -/

theorem readStep_of_none {σ : Tree ι} {η : Set (ι × Bool)} {τ : List (Rec ι)}
    (h : σ τ = none) : readStep σ η τ = τ := by
  unfold readStep
  rw [h]

theorem readStep_of_some {σ : Tree ι} {η : Set (ι × Bool)} {τ : List (Rec ι)} {i : ι}
    {c : Bool} (h : σ τ = some (i, c)) :
    readStep σ η τ =
      τ ++ [⟨i, c, bit η (i, firstCopy c), bit η (i, secondCopy c)⟩] := by
  unfold readStep
  rw [h]

theorem readN_succ (σ : Tree ι) (η : Set (ι × Bool)) (n : ℕ) :
    readN σ η (n + 1) = readStep σ η (readN σ η n) := rfl

/-- **Unique reconstruction.** Running the tree backwards from the amalgamated pair
reproduces the transcript of the run. -/
theorem readN_treeConfig {σ : Tree ι} [Fintype ι] (hσ : Consistent σ) (ν : Set (ι × Bool)) :
    ∀ n : ℕ, n ≤ Fintype.card ι → readN σ (treeConfig σ ν) n = runN σ ν n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hn' : n ≤ Fintype.card ι := le_trans (Nat.le_succ n) hn
      have hIH := ih hn'
      have hread : readN σ (treeConfig σ ν) (n + 1) =
          readStep σ (treeConfig σ ν) (runN σ ν n) := by
        rw [readN_succ, hIH]
      have hrun : runN σ ν (n + 1) = step σ ν (runN σ ν n) := rfl
      rw [hread, hrun]
      rcases hc : σ (runN σ ν n) with _ | ⟨i, c⟩
      · rw [readStep_of_none hc, step_of_none hc]
      · rw [readStep_of_some hc, step_of_some hc]
        have hmem : (⟨i, c, bit ν (i, false), bit ν (i, true)⟩ : Rec ι) ∈ trace σ ν := by
          have hpre : runN σ ν (n + 1) <+: trace σ ν := prefix_runN σ ν hn
          refine hpre.subset ?_
          rw [show runN σ ν (n + 1) =
            runN σ ν n ++ [⟨i, c, bit ν (i, false), bit ν (i, true)⟩] from step_of_some hc]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hcls := treeSet_iff_class hσ ν hmem
        cases c
        · -- the edge is decided `"S̄"`: the tree swaps the two copies of the edge
          have hnot : i ∉ treeSet σ ν := by
            rw [hcls]
            exact Bool.false_ne_true
          have hA := (mem_treeConfig_of_not_mem hnot).2
          have hB := (mem_treeConfig_of_not_mem hnot).1
          simp only [firstCopy, secondCopy, Bool.not_false]
          rw [bit_eq_of_iff hA, bit_eq_of_iff hB]
        · -- the edge is decided `"S"`: both copies keep their place
          have hmem' : i ∈ treeSet σ ν := by
            rw [hcls]
          have hA := (mem_treeConfig_of_mem hmem').1
          have hB := (mem_treeConfig_of_mem hmem').2
          simp only [firstCopy, secondCopy, Bool.not_true]
          rw [bit_eq_of_iff hA, bit_eq_of_iff hB]

theorem readback_treeConfig {σ : Tree ι} [Fintype ι] (hσ : Consistent σ)
    (ν : Set (ι × Bool)) : readback σ (treeConfig σ ν) = trace σ ν :=
  readN_treeConfig hσ ν (Fintype.card ι) le_rfl

theorem readSet_treeConfig {σ : Tree ι} [Fintype ι] (hσ : Consistent σ)
    (ν : Set (ι × Bool)) : readSet σ (treeConfig σ ν) = treeSet σ ν := by
  rw [readSet, treeSet, readback_treeConfig hσ ν]

/-- **The reconstruction inverts the tree.** -/
theorem unamal_treeConfig {σ : Tree ι} [Fintype ι] (hσ : Consistent σ)
    (ν : Set (ι × Bool)) :
    unamal σ (treeConfig σ ν) = ν := by
  ext x
  obtain ⟨i, b⟩ := x
  simp only [unamal, Set.mem_ofPred_eq, readSet_treeConfig hσ ν]
  cases b
  · by_cases h : i ∈ treeSet σ ν
    · simp [h, (mem_treeConfig_of_mem h).1]
    · simp [h, (mem_treeConfig_of_not_mem h).2]
  · by_cases h : i ∈ treeSet σ ν
    · simp [h, (mem_treeConfig_of_mem h).2]
    · simp [h, (mem_treeConfig_of_not_mem h).1]

theorem treeConfig_injective {σ : Tree ι} [Fintype ι] (hσ : Consistent σ) :
    Function.Injective (treeConfig σ) :=
  Function.LeftInverse.injective (g := unamal σ) (fun ν => unamal_treeConfig hσ ν)

theorem treeConfig_unamal {σ : Tree ι} [Fintype ι] (hσ : Consistent σ)
    (η : Set (ι × Bool)) :
    treeConfig σ (unamal σ η) = η := by
  obtain ⟨ν, hν⟩ := (Finite.injective_iff_surjective.1 (treeConfig_injective hσ)) η
  rw [← hν, unamal_treeConfig hσ ν]

/-- The fibre of the encoding is a singleton: the run is uniquely determined by the
amalgamated pair. -/
theorem fiber_treeConfig {σ : Tree ι} [Fintype ι] (hσ : Consistent σ) (η : Set (ι × Bool)) :
    {ν : Set (ι × Bool) | treeConfig σ ν = η} = {unamal σ η} := by
  ext ν
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    rw [← h, unamal_treeConfig hσ ν]
  · intro h
    rw [h]
    exact treeConfig_unamal hσ η

/-! ### The tree only permutes the two copies of each edge -/

theorem treeConfig_eq_pairConfig_iff {σ : Tree ι} [Fintype ι] {ν : Set (ι × Bool)}
    {a b : Set ι} : treeConfig σ ν = pairConfig a b ↔
      treeFirst σ ν = a ∧ treeSecond σ ν = b := by
  constructor
  · intro h
    constructor
    · ext i
      have := congrArg (fun s : Set (ι × Bool) => (i, false) ∈ s) h
      simpa [treeConfig, pairConfig] using this
    · ext i
      have := congrArg (fun s : Set (ι × Bool) => (i, true) ∈ s) h
      simpa [treeConfig, pairConfig] using this
  · rintro ⟨h1, h2⟩
    ext x
    obtain ⟨i, b⟩ := x
    cases b <;> simp [treeConfig, pairConfig, h1, h2]

theorem mem_pairConfig_false {a b : Set ι} {i : ι} :
    (i, false) ∈ pairConfig a b ↔ i ∈ a := by
  simp [pairConfig]

theorem mem_pairConfig_true {a b : Set ι} {i : ι} : (i, true) ∈ pairConfig a b ↔ i ∈ b := by
  simp [pairConfig]

/-! ### The tree preserves the product law -/

/-- The mass of one prescribed value of one coordinate. -/
def wt {κ : Type*} (p : κ → unitInterval) (x : κ) (b : Bool) : ℝ≥0∞ :=
  if b then (unitInterval.toNNReal (p x) : ℝ≥0∞)
    else (unitInterval.toNNReal (unitInterval.symm (p x)) : ℝ≥0∞)

/-- The mass of a single configuration is the product of the masses of its coordinates. -/
theorem prodBernoulli_singleton {κ : Type*} [Fintype κ] (p : κ → unitInterval) (ω : Set κ) :
    prodBernoulli p {ω} = ∏ x, wt p x (bitOf ω x) := by
  have h := prodBernoulli_transcript p id Function.injective_id (fun x => bitOf ω x)
  have hset : {ω' : Set κ | ∀ x, id x ∈ ω' ↔ bitOf ω x = true} = {ω} := by
    ext ω'
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, id]
    constructor
    · intro h
      ext x
      have := h x
      rwa [bitOf_eq_true] at this
    · intro h x
      rw [h, bitOf_eq_true]
  rw [hset] at h
  simpa [wt] using h

theorem wt_twoProfile_eq (q : ι → unitInterval) (i : ι) (b x : Bool) :
    wt (twoProfile q) (i, b) x = wt q i x := by
  cases b <;> cases x <;> rfl

theorem wt_twoProfile_fst {q : ι → unitInterval} {i : ι} {b : Bool} :
    wt (twoProfile q) (i, false) b = wt (twoProfile q) (i, true) b := by
  cases b <;> rfl

theorem wt_twoProfile_snd {q : ι → unitInterval} {i : ι} {b : Bool} :
    wt (twoProfile q) (i, true) b = wt (twoProfile q) (i, false) b :=
  (wt_twoProfile_fst (q := q) (i := i) (b := b)).symm

/-- The tree keeps the two values of every edge as a set: a step decided `"S"` fixes both
copies, every other edge has its two copies exchanged. -/
theorem prod_wt_treeConfig {σ : Tree ι} [Fintype ι] (q : ι → unitInterval)
    (ν : Set (ι × Bool)) :
    (∏ x : ι × Bool, wt (twoProfile q) x (bitOf (treeConfig σ ν) x)) =
      ∏ x : ι × Bool, wt (twoProfile q) x (bitOf ν x) := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool, Fintype.prod_bool]
  by_cases h : i ∈ treeSet σ ν
  · have h1 : bitOf (treeConfig σ ν) (i, false) = bitOf ν (i, false) :=
      bitOf_congr (mem_treeConfig_of_mem h).1
    have h2 : bitOf (treeConfig σ ν) (i, true) = bitOf ν (i, true) :=
      bitOf_congr (mem_treeConfig_of_mem h).2
    rw [h1, h2]
  · have h1 : bitOf (treeConfig σ ν) (i, false) = bitOf ν (i, true) :=
      bitOf_eq_of_iff (mem_treeConfig_of_not_mem h).1
    have h2 : bitOf (treeConfig σ ν) (i, true) = bitOf ν (i, false) :=
      bitOf_eq_of_iff (mem_treeConfig_of_not_mem h).2
    rw [h1, h2, wt_twoProfile_snd (b := bitOf ν (i, false)),
      wt_twoProfile_snd (b := bitOf ν (i, true)), mul_comm]

/-- The tree preserves the product law at the level of single configurations. -/
theorem prodBernoulli_treeConfig {σ : Tree ι} [Fintype ι] (q : ι → unitInterval)
    (ν : Set (ι × Bool)) :
    prodBernoulli (twoProfile q) {treeConfig σ ν} = prodBernoulli (twoProfile q) {ν} := by
  rw [prodBernoulli_singleton, prodBernoulli_singleton]
  exact prod_wt_treeConfig q ν

theorem prod_wt_pairConfig [Fintype ι] (q : ι → unitInterval) (a b : Set ι) :
    (∏ x : ι × Bool, wt (twoProfile q) x (bitOf (pairConfig a b) x)) =
      (∏ i, wt q i (bitOf a i)) * ∏ i, wt q i (bitOf b i) := by
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  have h1 : bitOf (pairConfig a b) (i, false) = bitOf a i :=
    bitOf_eq_of_iff' mem_pairConfig_false
  have h2 : bitOf (pairConfig a b) (i, true) = bitOf b i :=
    bitOf_eq_of_iff' mem_pairConfig_true
  rw [h1, h2, wt_twoProfile_eq, wt_twoProfile_eq, mul_comm]

/-- **The atom probabilities of the amalgamated pair.** -/
theorem prodBernoulli_treeConfig_atom {σ : Tree ι} [Fintype ι] (q : ι → unitInterval)
    (hσ : Consistent σ) (a b : Set ι) :
    prodBernoulli (twoProfile q) {ω | treeFirst σ ω = a ∧ treeSecond σ ω = b} =
      prodBernoulli q {a} * prodBernoulli q {b} := by
  have hset : {ω : Set (ι × Bool) | treeFirst σ ω = a ∧ treeSecond σ ω = b}
      = {ω | treeConfig σ ω = pairConfig a b} := by
    ext ω
    exact treeConfig_eq_pairConfig_iff.symm
  rw [hset, fiber_treeConfig hσ (pairConfig a b),
    ← prodBernoulli_treeConfig q (unamal σ (pairConfig a b)), treeConfig_unamal hσ,
    prodBernoulli_singleton, prodBernoulli_singleton, prodBernoulli_singleton,
    prod_wt_pairConfig]

/-! ### From atoms to arbitrary events -/

/-- A measure of a finite set is the sum of its values on the singletons. -/
theorem measure_eq_sum_finset {κ : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (μ : Measure κ) (t : Finset κ) : μ (t : Set κ) = ∑ x ∈ t, μ {x} := by
  have h : (t : Set κ) = ⋃ x ∈ t, ({x} : Set κ) := by
    ext y
    simp
  rw [h]
  exact measure_biUnion_finset (f := fun x : κ => ({x} : Set κ))
    (fun x _ y _ hxy => by
      rw [Function.onFun]
      exact Set.disjoint_singleton.2 hxy)
    (fun x _ => measurableSet_singleton x)

/-- A measure of a set in a finite space is the sum of its values on the singletons. -/
theorem measure_eq_sum_filter {κ : Type*} [MeasurableSpace κ] [Fintype κ]
    [MeasurableSingletonClass κ] (μ : Measure κ) (s : Set κ) [DecidablePred (· ∈ s)] :
    μ s = ∑ x ∈ Finset.univ.filter (fun x => x ∈ s), μ {x} := by
  have hset : ((Finset.univ.filter (fun x => x ∈ s) : Finset κ) : Set κ) = s := by
    ext x
    simp
  calc μ s = μ ((Finset.univ.filter (fun x => x ∈ s) : Finset κ) : Set κ) := by rw [hset]
    _ = ∑ x ∈ Finset.univ.filter (fun x => x ∈ s), μ {x} := measure_eq_sum_finset μ _

/-- **Gladkov's amalgamation lemma for a decision tree.** For any consistent tree on a
finite graph, `C1 →_S C2` and `C2 →_S C1` are independent and both are distributed as a
single Bernoulli configuration. -/
theorem prodBernoulli_treeFirst_second_indep {σ : Tree ι} [Fintype ι] (q : ι → unitInterval)
    (hσ : Consistent σ) (A B : Set (Set ι)) :
    prodBernoulli (twoProfile q) {ω | treeFirst σ ω ∈ A ∧ treeSecond σ ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  classical
  have hμ : ∀ c : Set ι × Set ι,
      prodBernoulli (twoProfile q) {ω | (treeFirst σ ω, treeSecond σ ω) = c}
        = prodBernoulli q {c.1} * prodBernoulli q {c.2} := by
    rintro ⟨a, b⟩
    have hset : {ω : Set (ι × Bool) | (treeFirst σ ω, treeSecond σ ω) = (a, b)}
        = {ω | treeFirst σ ω = a ∧ treeSecond σ ω = b} := by
      ext ω
      simp [Prod.ext_iff]
    rw [hset]
    exact prodBernoulli_treeConfig_atom q hσ a b
  have hmain : {ω : Set (ι × Bool) | treeFirst σ ω ∈ A ∧ treeSecond σ ω ∈ B}
      = ⋃ c ∈ (Finset.univ.filter (fun c : Set ι × Set ι => c.1 ∈ A ∧ c.2 ∈ B)),
          {ω | (treeFirst σ ω, treeSecond σ ω) = c} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(treeFirst σ ω, treeSecond σ ω), ⟨h1, h2⟩, rfl⟩
    · rintro ⟨c, ⟨h1, h2⟩, hp⟩
      have e1 : c.1 = treeFirst σ ω := (congrArg Prod.fst hp).symm
      have e2 : c.2 = treeSecond σ ω := (congrArg Prod.snd hp).symm
      exact ⟨e1 ▸ h1, e2 ▸ h2⟩
  have hdisj : (↑(Finset.univ.filter (fun c : Set ι × Set ι => c.1 ∈ A ∧ c.2 ∈ B)) :
      Set (Set ι × Set ι)).PairwiseDisjoint
      (fun c => {ω : Set (ι × Bool) | (treeFirst σ ω, treeSecond σ ω) = c}) := by
    intro c _ c' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    exact hne (h1.symm.trans h2)
  have hmeas : ∀ c ∈ (Finset.univ.filter (fun c : Set ι × Set ι => c.1 ∈ A ∧ c.2 ∈ B)),
      MeasurableSet {ω : Set (ι × Bool) |
      (treeFirst σ ω, treeSecond σ ω) = c} := fun c _ => MeasurableSet.of_discrete
  rw [hmain, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl fun c _ => hμ c]
  have hfilter : (Finset.univ.filter (fun c : Set ι × Set ι => c.1 ∈ A ∧ c.2 ∈ B))
      = (Finset.univ.filter (fun a : Set ι => a ∈ A)) ×ˢ
        (Finset.univ.filter (fun b : Set ι => b ∈ B)) := by
    ext c
    simp [Finset.mem_product]
  have hsum : (∑ c ∈ (Finset.univ.filter (fun c : Set ι × Set ι => c.1 ∈ A ∧ c.2 ∈ B)),
        prodBernoulli q {c.1} * prodBernoulli q {c.2}) =
      (∑ a ∈ Finset.univ.filter (fun a : Set ι => a ∈ A), prodBernoulli q {a}) *
        (∑ b ∈ Finset.univ.filter (fun b : Set ι => b ∈ B), prodBernoulli q {b}) := by
    rw [Finset.sum_mul_sum (f := fun a : Set ι => prodBernoulli q {a})
      (g := fun b : Set ι => prodBernoulli q {b})]
    rw [hfilter, Finset.sum_product]
  rw [hsum, measure_eq_sum_filter (prodBernoulli q) A, measure_eq_sum_filter (prodBernoulli q) B]

/-- The first amalgamation alone has the original law. -/
theorem prodBernoulli_treeFirst {σ : Tree ι} [Fintype ι] (q : ι → unitInterval)
    (hσ : Consistent σ) (A : Set (Set ι)) :
    prodBernoulli (twoProfile q) {ω | treeFirst σ ω ∈ A} = prodBernoulli q A := by
  have h := prodBernoulli_treeFirst_second_indep q hσ A Set.univ
  simpa using h

/-- The second amalgamation alone has the original law. -/
theorem prodBernoulli_treeSecond {σ : Tree ι} [Fintype ι] (q : ι → unitInterval)
    (hσ : Consistent σ) (B : Set (Set ι)) :
    prodBernoulli (twoProfile q) {ω | treeSecond σ ω ∈ B} = prodBernoulli q B := by
  have h := prodBernoulli_treeFirst_second_indep q hσ Set.univ B
  simpa using h

theorem unamal_injective {σ : Tree ι} [Fintype ι] (hσ : Consistent σ) :
    Function.Injective (unamal σ) := by
  intro x y h
  rw [← treeConfig_unamal hσ x, ← treeConfig_unamal hσ y, h]

/-- **The adaptive flip preserves the product law.** The map sending a configuration to the
pair `(C1 →_S C2, C2 →_S C1)`, encoded as one configuration on `ι × Bool`, is a
measure-preserving bijection of the configuration space. -/
theorem map_treeConfig {σ : Tree ι} [Fintype ι] (q : ι → unitInterval) (hσ : Consistent σ) :
    (prodBernoulli (twoProfile q)).map (treeConfig σ) = prodBernoulli (twoProfile q) := by
  classical
  have hfib : ∀ x : Set (ι × Bool),
      prodBernoulli (twoProfile q) {unamal σ x} = prodBernoulli (twoProfile q) {x} := by
    intro x
    rw [← prodBernoulli_treeConfig q (unamal σ x), treeConfig_unamal hσ x]
  refine Measure.ext fun S _ => ?_
  rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  have hpre : treeConfig σ ⁻¹' S =
      ⋃ x ∈ Finset.univ.filter (fun x : Set (ι × Bool) => x ∈ S),
        ({unamal σ x} : Set (Set (ι × Bool))) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_singleton_iff]
    exact ⟨fun hy => ⟨treeConfig σ y, hy, (unamal_treeConfig hσ y).symm⟩, by
      rintro ⟨x, hx, rfl⟩
      rwa [treeConfig_unamal hσ x]⟩
  rw [hpre, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun x _ => hfib x,
      measure_eq_sum_filter (prodBernoulli (twoProfile q)) S]
  · intro x _ y _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro z h1 h2
    simp only [Set.mem_singleton_iff] at h1 h2
    exact hne (unamal_injective hσ (h1.symm.trans h2))
  · intro x _
    exact measurableSet_singleton (unamal σ x)

/-! ### Measurability of the encoded amalgamations -/

theorem measurable_treeConfig {σ : Tree ι} [Fintype ι] :
    Measurable (treeConfig σ) :=
  measurable_of_finite _

theorem measurable_treeFirst {σ : Tree ι} [Fintype ι] :
    Measurable (treeFirst (ι := ι) σ) :=
  measurable_of_finite _

theorem measurable_treeSecond {σ : Tree ι} [Fintype ι] :
    Measurable (treeSecond (ι := ι) σ) :=
  measurable_of_finite _

theorem measurable_treePair {σ : Tree ι} [Fintype ι] :
    Measurable fun ω => (treeFirst σ ω, treeSecond σ ω) :=
  measurable_of_finite _

/-- The joint law of the two amalgamations, as an identity of push-forward laws. -/
theorem map_treeConfig_pair {σ : Tree ι} [Fintype ι] (q : ι → unitInterval)
    (hσ : Consistent σ) :
    (prodBernoulli (twoProfile q)).map (fun ω => (treeFirst σ ω, treeSecond σ ω)) =
      (prodBernoulli q).prod (prodBernoulli q) := by
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply measurable_treePair (hA.prod hB), Measure.prod_prod]
  exact prodBernoulli_treeFirst_second_indep q hσ A B

end PercLib.GladkovAmalgam
