/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated from the independently reviewed Ultramath candidate `smx01s0xw/m4`, direction `d2`.

# The canonical layer cake, susceptibility row sums, and finite-window tail limits

Sources: Hutchcroft, *On the derivation of mean-field percolation critical exponents from the
triangle condition* (arXiv:2106.06400), proof of Theorem 1.3, and *Critical long-range
percolation I* (arXiv:2508.18807v1), Proposition I.4.15, Case 3 (p. 47).  These use the identities
`E_{β,r}|K| = ∑_n P_{β,r}(|K| ≥ n)` and `χ_β = E_β|K_0| = ∑_y τ_β(0,y)`.

`Entropy/TailAssembly.lean` proves the *finite* combinatorial tail sum
`∑_{k ≤ n} P(v ≥ k) = E[v ∧ n]` for a `ℕ`-valued volume on a finite probability space, and it lists
as a remaining gap the layer-cake identity for the infinite-volume `ℝ≥0∞`-valued
`lawSusceptibility` `χ_β = E_β|K_0| = ∫⁻ ω, clusterVol ω 0 ∂(M.law β)`, and summability of the
tail series.  This file closes exactly that gap at the canonical model law `M.law β`, with no
finite-volume truncation and no finiteness assumption on `χ_β`:

* `lintegral_eq_tsum_meas_lt`, `lintegral_min_eq_sum_meas_le`: the layer-cake identity and its
  truncation for a measurable integer-valued `ℝ≥0∞`-valued function on an arbitrary measure space.
  Integer-valuedness is carried by `IntValued`, the honest `ℕ∞`-image condition; the identity is
  false for general `ℝ≥0∞`-valued functions, so the hypothesis cannot be dropped.
* `lawSusceptibility_eq_tsum_lawTailAt`: `χ_β = ∑' k, P_β(|K_0| ≥ k+1)` in `ℝ≥0∞`, the exact
  infinite layer cake at the model law.
* `lintegral_min_clusterVol_eq_sum`: the truncated identity
  `E_β[|K_0| ∧ n] = ∑_{k=1}^{n} P_β(|K_0| ≥ k)` at the model law.
* `sum_lawTailAt_le_lawSusceptibility`, `mul_lawTailAt_le_lawSusceptibility` and the real forms
  `sum_lawTail_le_toReal`, `lawTail_mul_le_toReal`: `∑_{k ≤ n} P_β(|K_0| ≥ k) ≤ χ_β` and the Markov
  bound `P_β(|K_0| ≥ n) ≤ χ_β / n`.  The real (`M.lawTail`) forms carry the explicit hypothesis
  `χ_β ≠ ⊤`, since `ENNReal.toReal ⊤ = 0` makes them false when `χ_β = ⊤`; the extended-nonnegative
  forms are unconditional.  No finite mean is assumed.
* `summable_lawTail_of_ne_top`, `summable_tsum_lawTail_eq_toReal`: a finite `χ_β` makes the
  tail series summable, and then `χ_β = ∑_{k ≥ 1} P_β(|K_0| ≥ k)` holds as an equality of real
  numbers — the summability is derived, not assumed.
* `lawSusceptibility_eq_iSup_lintegral_min`: `χ_β = ⨆_n E_β[|K_0| ∧ n]`, the monotone convergence of
  the truncated expectations to the full susceptibility.
* `cutMoment_one_eq_tsum_cutLawTailAt`, `cutLaw_lintegral_min_eq_sum`,
  `sum_cutLawTail_le_cutMoment_one`: the same layer cake at the cutoff law `M.cutLaw r`, where the
  source's Case 3 actually uses it: `E_{β_c,r}|K| = ∑_{n ≥ 1} P_{β_c,r}(|K| ≥ n)` as an identity of
  `M.cutMoment 1 r`, its truncation, and the real bound `∑_{n ≤ N} P_{β_c,r}(|K| ≥ n) ≤
  E_{β_c,r}|K|`.
* `lawTailAt_eq_iSup_lawWindowTail`, `lawSusceptibility_eq_iSup_lintegral_clusterVolIn`: the
  faithful finite-window limits `P_β(|K_0| ≥ k) = ⨆_n P_β(|K_0 ∩ F_n| ≥ k)` and
  `χ_β = ⨆_n E_β|K_0 ∩ F_n|` along a monotone exhaustion `F_n ↑ V`, by continuity from below and
  monotone convergence.  The only nontrivial step is that a finite threshold below a countable
  supremum of integer-valued terms is attained (`exists_coe_le_of_le_iSup`).
* `lawSusceptibility_eq_tsum_twoPointENN`, `lawSusceptibility_eq_tsum_twoPoint`: the source's
  row-sum identity `χ_β = E_β|K_0| = ∑_y τ_β(0,y)`, relating `lawSusceptibility` to the model's
  two-point function `M.twoPoint`.
* `lawTail_one`, `lawSusceptibility_zero`: the exact values `P_β(|K_0| ≥ 1) = 1` and `χ_0 = 1`.  The
  second is a nonvacuity and consistency check: it evaluates the row-sum identity in a case
  (`β = 0`, where `M.law 0 = dirac ∅` and `|K_0| = 1`) whose value is known independently.
* `not_forall_sum_lawTail_le_toReal_of_eq_top`,
  `not_twoIntensityTailComparison_of_lawSusceptibility_eq_top`: the hypothesis `χ_{β₁} ≠ ⊤` is
  *necessary*, not an artefact.  At `χ_β = ⊤` the real tail-sum bound fails at `n = 1` (`1 ≤ 0`),
  and `SourceModelData.TwoIntensityTailComparison A` itself is false (take `β₁ = β₂`, `n = 1`).
  So any real-valued two-intensity comparison at the model must establish finiteness of the
  lower-intensity susceptibility; the source is consistent with this because there `χ_{β₁}` is a
  real number, and production's own use of `hDM` comes with `SusceptibilityBound`.

Nothing here assumes the triangle condition, a finite critical mean, finiteness of the cutoff first
moment in the extended-nonnegative statements, or any of the entropy inputs of `TailAssembly`.
The real-valued cutoff bound states its `cutMoment 1 r ≠ ⊤` hypothesis explicitly.  What is *not*
proved here: the passage from these identities to `SourceModelData.TwoIntensityTailComparison`
still needs the transcript relative-entropy bound and the revealment estimate of the source, which
are outside this file's scope.  The finite-graph
formalism `TreeGraph.clusterF`/`TreeGraph.clusterVol` (finite edge subsets with an explicit `ends`
map, used for the tree expansion) is *not* related to the global cluster volume here: the faithful
canonical finite-volume object at the model law is the windowed `clusterVolIn`, which is what
`lawTailAt_eq_iSup_lawWindowTail` and `lawSusceptibility_eq_iSup_lintegral_clusterVolIn` handle.
-/
module

public import
  PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.TwoIntensityComparison

/-!
# Canonical layer cake for the cluster volume

The layer-cake identities for a measurable integer-valued function, and their instantiation at the
canonical long-range model law `P_β = M.law β`.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.LayerCake

/-! ### Integer-valued extended nonnegative reals -/

/-- The extended nonnegative reals that are natural numbers or `⊤`, i.e. the image of `ℕ∞`.  This
is the exact hypothesis needed for the layer-cake identity. -/
def IntValued {α : Type*} (f : α → ℝ≥0∞) : Prop :=
  ∀ a, ∃ n : ℕ, f a = (n : ℝ≥0∞) ∨ f a = ⊤

/-- `IntValued` is the same condition as being the coercion of an `ℕ∞`-valued function. -/
theorem intValued_iff {α : Type*} {f : α → ℝ≥0∞} :
    IntValued f ↔ ∀ a, ∃ g : ℕ∞, f a = ((g : ℕ∞) : ℝ≥0∞) := by
  constructor
  · rintro h a
    obtain ⟨n, hn | hn⟩ := h a
    · exact ⟨n, by rw [hn, ENat.toENNReal_coe]⟩
    · exact ⟨⊤, by rw [hn, ENat.toENNReal_top]⟩
  · rintro h a
    obtain ⟨g, hg⟩ := h a
    cases g using ENat.recTopCoe with
    | top => exact ⟨0, Or.inr (by rw [hg, ENat.toENNReal_top])⟩
    | coe n => exact ⟨n, Or.inl (by rw [hg, ENat.toENNReal_coe])⟩

/-! ### Counting the natural numbers below an extended natural -/

/-- A natural number `n` equals the number of naturals `k < n`. -/
theorem tsum_indicator_lt_nat (n : ℕ) :
    ∑' k : ℕ,
      (if (k : ℝ≥0∞) < (n : ℝ≥0∞) then (1 : ℝ≥0∞) else 0) = (n : ℝ≥0∞) := by
  have hiff : ∀ k : ℕ, ((k : ℝ≥0∞) < (n : ℝ≥0∞)) = (k < n) := fun k =>
    propext (by exact_mod_cast Iff.rfl)
  have h : ∀ k : ℕ, (if (k : ℝ≥0∞) < (n : ℝ≥0∞) then (1 : ℝ≥0∞) else 0)
      = (if k < n then (1 : ℝ≥0∞) else 0) := by
    intro k
    simp only [hiff k]
  rw [tsum_congr h, tsum_eq_sum (s := Finset.range n)]
  · have h1 : ∀ k ∈ Finset.range n, (if k < n then (1 : ℝ≥0∞) else 0) = 1 := by
      intro k hk
      simp [Finset.mem_range.1 hk]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hk]

/-- `⊤` equals the number of naturals below it. -/
theorem tsum_indicator_lt_top :
    ∑' k : ℕ,
      (if (k : ℝ≥0∞) < (⊤ : ℝ≥0∞) then (1 : ℝ≥0∞) else 0) = ⊤ := by
  have h : ∀ k : ℕ,
      (if (k : ℝ≥0∞) < (⊤ : ℝ≥0∞) then (1 : ℝ≥0∞) else 0) = 1 := by
    intro k
    simp
  rw [tsum_congr h]
  simp

/-- **The pointwise counting identity** for an integer-valued extended nonnegative real: `x` is the
number of naturals below it. -/
theorem tsum_indicator_lt {x : ℝ≥0∞} (h : ∃ n : ℕ, x = (n : ℝ≥0∞) ∨ x = ⊤) :
    ∑' k : ℕ, (if (k : ℝ≥0∞) < x then (1 : ℝ≥0∞) else 0) = x := by
  obtain ⟨n, hn | hn⟩ := h
  · rw [hn]
    exact tsum_indicator_lt_nat n
  · rw [hn]
    exact tsum_indicator_lt_top

/-- **The layer-cake identity for integer-valued functions on a general measure space.**  For a
measurable `f : α → ℝ≥0∞` taking only values in `ℕ∞ ⊆ ℝ≥0∞`,
`∫⁻ a, f a ∂μ = ∑' k, μ {a | k < f a}`.  Neither finiteness of the integral nor `σ`-finiteness of
`μ` is assumed. -/
theorem lintegral_eq_tsum_meas_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (hint : IntValued f) :
    ∫⁻ a, f a ∂μ = ∑' k : ℕ, μ {a | (k : ℝ≥0∞) < f a} := by
  set A : ℕ → Set α := fun k => {a | (k : ℝ≥0∞) < f a } with hA
  have hAmeas : ∀ k : ℕ, MeasurableSet (A k) := fun k =>
    measurableSet_lt measurable_const hf
  have hpt : ∀ a, f a = ∑' k : ℕ, (A k).indicator (fun _ => (1 : ℝ≥0∞)) a := by
    intro a
    have h1 : ∀ k : ℕ, (A k).indicator (fun _ => (1 : ℝ≥0∞)) a
        = (if (k : ℝ≥0∞) < f a then (1 : ℝ≥0∞) else 0) := by
      intro k
      simp only [Set.indicator_apply, hA, Set.mem_ofPred_eq]
    rw [tsum_congr h1, tsum_indicator_lt (hint a)]
  calc ∫⁻ a, f a ∂μ
      = ∫⁻ a, ∑' k : ℕ, (A k).indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ :=
        lintegral_congr hpt
    _ = ∑' k : ℕ, ∫⁻ a, (A k).indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ :=
        lintegral_tsum fun k => (Measurable.indicator measurable_const (hAmeas k)).aemeasurable
    _ = ∑' k : ℕ, μ (A k) := by
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator_const (hAmeas k) (1 : ℝ≥0∞), one_mul]

/-! ### The truncated layer cake -/

/-- The pointwise minimum of an integer-valued extended nonnegative real with a natural number is
integer-valued. -/
theorem intValued_min {α : Type*} {f : α → ℝ≥0∞} (hint : IntValued f) (n : ℕ) :
    IntValued fun a => min (f a) (n : ℝ≥0∞) := by
  intro a
  obtain ⟨m, hm | hm⟩ := hint a
  · refine ⟨min m n, Or.inl ?_⟩
    change min (f a) (n : ℝ≥0∞) = ((min m n : ℕ) : ℝ≥0∞)
    rw [hm]
    rcases le_total m n with hle | hle
    · rw [min_eq_left hle, min_eq_left (by exact_mod_cast hle)]
    · rw [min_eq_right hle, min_eq_right (by exact_mod_cast hle)]
  · refine ⟨n, Or.inl ?_⟩
    change min (f a) (n : ℝ≥0∞) = (n : ℝ≥0∞)
    rw [hm]
    simp

/-- The strict and non-strict integer thresholds agree: for integer-valued `x`, `k < x` is the same
as `k + 1 ≤ x`. -/
theorem lt_iff_succ_le {x : ℝ≥0∞}
    (h : ∃ n : ℕ, x = (n : ℝ≥0∞) ∨ x = ⊤) (k : ℕ) :
    (k : ℝ≥0∞) < x ↔ ((k + 1 : ℕ) : ℝ≥0∞) ≤ x := by
  obtain ⟨n, hn | hn⟩ := h
  · rw [hn]
    exact_mod_cast Iff.rfl
  · rw [hn]
    simp

/-- **The truncated layer-cake identity.**  For a measurable integer-valued `f`,
`∫⁻ min (f) n = ∑_{k=1}^{n} μ {a | k ≤ f a}`. -/
theorem lintegral_min_eq_sum_meas_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (hint : IntValued f) (n : ℕ) :
    ∫⁻ a, min (f a) (n : ℝ≥0∞) ∂μ =
      ∑ k ∈ Finset.Icc 1 n, μ {a | (k : ℝ≥0∞) ≤ f a} := by
  have hfm : Measurable fun a => min (f a) (n : ℝ≥0∞) := hf.min measurable_const
  rw [lintegral_eq_tsum_meas_lt hfm (intValued_min hint n)]
  have hset_lt : ∀ k : ℕ, k < n →
      {a | (k : ℝ≥0∞) < min (f a) (n : ℝ≥0∞)} =
        {a | ((k + 1 : ℕ) : ℝ≥0∞) ≤ f a} := by
    intro k hk
    ext a
    simp only [Set.mem_ofPred_eq]
    rw [lt_min_iff, lt_iff_succ_le (hint a) k]
    constructor
    · rintro ⟨h1, -⟩
      exact h1
    · intro h1
      exact ⟨h1, by exact_mod_cast hk⟩
  have hset_ge : ∀ k : ℕ, ¬ k < n →
      {a | (k : ℝ≥0∞) < min (f a) (n : ℝ≥0∞)} = ∅ := by
    intro k hk
    refine eq_empty_of_forall_notMem fun a ha => ?_
    have h1 : (n : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast (Nat.le_of_not_lt hk)
    exact absurd ha (not_lt.2 (le_trans (min_le_right _ _) h1))
  have hcongr : ∀ k : ℕ, μ {a | (k : ℝ≥0∞) < min (f a) (n : ℝ≥0∞)}
      = (if k < n then μ {a | ((k + 1 : ℕ) : ℝ≥0∞) ≤ f a} else 0) := by
    intro k
    by_cases hk : k < n
    · rw [hset_lt k hk]
      simp [hk]
    · rw [hset_ge k hk]
      simp [hk]
  rw [tsum_congr hcongr, tsum_eq_sum (s := Finset.range n)]
  swap
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hk]
  have h1 : ∀ k ∈ Finset.range n,
      (if k < n then μ {a | ((k + 1 : ℕ) : ℝ≥0∞) ≤ f a} else 0)
      = μ {a | ((k + 1 : ℕ) : ℝ≥0∞) ≤ f a} := by
    intro k hk
    simp [Finset.mem_range.1 hk]
  rw [Finset.sum_congr rfl h1, ← Finset.Ico_succ_right_eq_Icc 1 n,
    Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-! ### Attaining a finite bound below a countable supremum -/

/-- An integer-valued term strictly below a natural number is at most the predecessor. -/
theorem le_pred_of_lt_coe_nat {x : ℝ≥0∞}
    (hint : ∃ n : ℕ, x = (n : ℝ≥0∞) ∨ x = ⊤) {m : ℕ}
    (h : x < (m : ℝ≥0∞)) : x ≤ ((m - 1 : ℕ) : ℝ≥0∞) := by
  obtain ⟨n, hn | hn⟩ := hint
  · rw [hn] at h ⊢
    have : n < m := by exact_mod_cast h
    exact_mod_cast (show n ≤ m - 1 by omega)
  · rw [hn] at h
    simp at h

/-- **A finite threshold below a countable supremum of integer-valued terms is attained.**  This is
what turns continuity from below into an identity of tail probabilities along a monotone
exhaustion. -/
theorem exists_coe_le_of_le_iSup {f : ℕ → ℝ≥0∞}
    (hint : ∀ n, ∃ j : ℕ, f n = (j : ℝ≥0∞) ∨ f n = ⊤) {m : ℕ}
    (h : (m : ℝ≥0∞) ≤ ⨆ n, f n) : ∃ n, (m : ℝ≥0∞) ≤ f n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨0, by simp⟩
  by_contra hcon
  have hcon' : ∀ n, f n < (m : ℝ≥0∞) := fun n =>
    not_le.1 fun hle => hcon ⟨n, hle⟩
  have hbound : ∀ n, f n ≤ ((m - 1 : ℕ) : ℝ≥0∞) := fun n =>
    le_pred_of_lt_coe_nat (hint n) (hcon' n)
  have hsup : (⨆ n, f n) ≤ ((m - 1 : ℕ) : ℝ≥0∞) := iSup_le hbound
  have hle : (m : ℝ≥0∞) ≤ ((m - 1 : ℕ) : ℝ≥0∞) := le_trans h hsup
  have : m ≤ m - 1 := by exact_mod_cast hle
  omega

end PercLib.CriticalLRP.LayerCake

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP

variable (M : SourceModelData)

/-! ### The tail at the model law, in extended nonnegative form -/

/-- The tail event `{|K_0| ≥ k}` is measurable for the model law. -/
theorem measurableSet_lawTailEvent (k : ℕ) :
    MeasurableSet {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} :=
  measurableSet_le measurable_const (measurable_clusterVol 0)

/-- `P_β(|K_0| ≥ k)` in `ℝ≥0∞`, without the `toReal` of `lawTail`.  This is the form in which the
layer cake holds without any finiteness hypothesis. -/
noncomputable def lawTailAt (β : ℝ≥0) (k : ℕ) : ℝ≥0∞ :=
  (M.law β) {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}

theorem lawTailAt_def (β : ℝ≥0) (k : ℕ) :
    M.lawTailAt β k =
      (M.law β) {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} :=
  rfl

/-- The real-valued `lawTail` is the `toReal` of the extended-nonnegative tail. -/
theorem lawTail_eq_toReal_lawTailAt (β : ℝ≥0) (k : ℕ) :
    M.lawTail β k = (M.lawTailAt β k).toReal := rfl

theorem lawTailAt_le_one (β : ℝ≥0) (k : ℕ) : M.lawTailAt β k ≤ 1 := by
  have : IsProbabilityMeasure (M.law β) :=
    inferInstanceAs (IsProbabilityMeasure (longRangeMeasure M.kernel M.kernel_nonneg β))
  calc M.lawTailAt β k ≤ M.law β Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem lawTailAt_ne_top (β : ℝ≥0) (k : ℕ) : M.lawTailAt β k ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (M.lawTailAt_le_one β k)

/-- The critical law is the model law at `β_c`, so its tail is `lawTailAt` at `β_c`. -/
theorem criticalLaw_tail_eq_lawTailAt (k : ℕ) :
    M.criticalLaw {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      = M.lawTailAt M.betaCrit k :=
  rfl

/-- The cluster volume at the model law is integer-valued in the layer-cake sense. -/
theorem intValued_clusterVol (v : M.V) :
    LayerCake.IntValued fun ω : Config M.V => clusterVol ω v := by
  intro ω
  obtain ⟨g, hg⟩ : ∃ g : ℕ∞,
      clusterVol ω v = ((g : ℕ∞) : ℝ≥0∞) := ⟨_, clusterVol_eq_encard ω v⟩
  cases g using ENat.recTopCoe with
  | top => exact ⟨0, Or.inr (hg.trans ENat.toENNReal_top)⟩
  | coe n => exact ⟨n, Or.inl (hg.trans (ENat.toENNReal_coe n))⟩

/-! ### The infinite layer cake at the model law -/

/-- **The layer cake identity for the canonical susceptibility**:
`χ_β = E_β|K_0| = ∑' k, P_β(|K_0| ≥ k + 1)`, in `ℝ≥0∞` and with no finiteness hypothesis. -/
theorem lawSusceptibility_eq_tsum_lawTailAt (β : ℝ≥0) :
    M.lawSusceptibility β = ∑' k : ℕ, M.lawTailAt β (k + 1) := by
  change (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) = _
  rw [LayerCake.lintegral_eq_tsum_meas_lt (measurable_clusterVol (0 : M.V))
    (M.intValued_clusterVol 0)]
  refine tsum_congr fun k => ?_
  have hset : {ω : Config M.V | (k : ℝ≥0∞) < clusterVol ω (0 : M.V)}
      = {ω : Config M.V | ((k + 1 : ℕ) : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact LayerCake.lt_iff_succ_le (M.intValued_clusterVol 0 ω) k
  rw [hset]
  rfl

/-- **The truncated layer cake at the model law**:
`E_β[|K_0| ∧ n] = ∑_{k=1}^{n} P_β(|K_0| ≥ k)`. -/
theorem lintegral_min_clusterVol_eq_sum (β : ℝ≥0) (n : ℕ) :
    ∫⁻ ω, min (clusterVol ω (0 : M.V)) (n : ℝ≥0∞) ∂(M.law β)
      = ∑ k ∈ Finset.Icc 1 n, M.lawTailAt β k :=
  LayerCake.lintegral_min_eq_sum_meas_le (measurable_clusterVol (0 : M.V))
    (M.intValued_clusterVol 0) n

/-- Reindexing the finite tail sums: `∑_{k<n} P(|K_0| ≥ k+1) = ∑_{k=1}^{n} P(|K_0| ≥ k)`. -/
theorem sum_range_lawTailAt_succ (β : ℝ≥0) (n : ℕ) :
    ∑ k ∈ Finset.range n, M.lawTailAt β (k + 1) =
      ∑ k ∈ Finset.Icc 1 n, M.lawTailAt β k := by
  rw [← Finset.Ico_succ_right_eq_Icc 1 n, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- **Monotone convergence of the truncated expectations**: `χ_β = ⨆_n E_β[|K_0| ∧ n]`, obtained by
passing the countable tail series to its partial sums (equivalently `lintegral_iSup` for
`min (|K_0|) n ↑ |K_0|`).  No finiteness hypothesis. -/
theorem lawSusceptibility_eq_iSup_lintegral_min (β : ℝ≥0) :
    M.lawSusceptibility β
      = ⨆ n : ℕ, ∫⁻ ω, min (clusterVol ω (0 : M.V)) (n : ℝ≥0∞) ∂(M.law β) := by
  have h : ∀ n : ℕ, ∫⁻ ω, min (clusterVol ω (0 : M.V)) (n : ℝ≥0∞) ∂(M.law β)
      = ∑ k ∈ Finset.range n, M.lawTailAt β (k + 1) := by
    intro n
    rw [M.lintegral_min_clusterVol_eq_sum β n, M.sum_range_lawTailAt_succ β n]
  rw [M.lawSusceptibility_eq_tsum_lawTailAt β, ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr fun n => (h n).symm

/-- **The tail sum is dominated by the susceptibility**, in `ℝ≥0∞`: no finiteness assumption. -/
theorem sum_lawTailAt_le_lawSusceptibility (β : ℝ≥0) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, M.lawTailAt β k ≤ M.lawSusceptibility β := by
  rw [← M.lintegral_min_clusterVol_eq_sum β n]
  exact lintegral_mono fun ω => min_le_left _ _

/-- **Markov's inequality for the cluster volume**, in `ℝ≥0∞` and without finiteness assumptions:
`n · P_β(|K_0| ≥ n) ≤ χ_β`. -/
theorem mul_lawTailAt_le_lawSusceptibility (β : ℝ≥0) (n : ℕ) :
    (n : ℝ≥0∞) * M.lawTailAt β n ≤ M.lawSusceptibility β := by
  set s : Set (Config M.V) :=
    {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} with hs
  have h1 : (n : ℝ≥0∞) * M.lawTailAt β n =
      ∫⁻ ω in s, (n : ℝ≥0∞) ∂(M.law β) := by
    rw [setLIntegral_const]
    rfl
  have h2 : ∫⁻ ω in s, (n : ℝ≥0∞) ∂(M.law β)
      ≤ ∫⁻ ω in s, clusterVol ω (0 : M.V) ∂(M.law β) :=
    setLIntegral_mono' (M.measurableSet_lawTailEvent n) fun ω hω => hω
  have h3 : ∫⁻ ω in s, clusterVol ω (0 : M.V) ∂(M.law β) ≤ M.lawSusceptibility β :=
    setLIntegral_le_lintegral s _
  calc (n : ℝ≥0∞) * M.lawTailAt β n = ∫⁻ ω in s, (n : ℝ≥0∞) ∂(M.law β) := h1
    _ ≤ ∫⁻ ω in s, clusterVol ω (0 : M.V) ∂(M.law β) := h2
    _ ≤ M.lawSusceptibility β := h3

/-! ### The trivial lower tail and the necessity of finiteness -/

/-- The root cluster always contains the root, so `{|K_0| ≥ 1}` is the full event. -/
theorem lawTailAt_one (β : ℝ≥0) : M.lawTailAt β 1 = 1 := by
  have : IsProbabilityMeasure (M.law β) :=
    inferInstanceAs (IsProbabilityMeasure (longRangeMeasure M.kernel M.kernel_nonneg β))
  have hset : {ω : Config M.V | ((1 : ℕ) : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} =
      Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    change ((1 : ℕ) : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)
    obtain ⟨n, hn | hn⟩ := M.intValued_clusterVol (0 : M.V) ω
    · have hn' : clusterVol ω (0 : M.V) = (n : ℝ≥0∞) := hn
      rw [hn']
      have hpos : clusterVol ω (0 : M.V) ≠ 0 := ne_of_gt (clusterVol_pos ω (0 : M.V))
      have hn0 : n ≠ 0 := by
        rw [hn'] at hpos
        simpa using hpos
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0
    · have hn' : clusterVol ω (0 : M.V) = ⊤ := hn
      rw [hn']
      exact le_top
  rw [lawTailAt, hset, measure_univ]

/-- `P_β(|K_0| ≥ 1) = 1` in real form. -/
theorem lawTail_one (β : ℝ≥0) : M.lawTail β 1 = 1 := by
  rw [M.lawTail_eq_toReal_lawTailAt, M.lawTailAt_one, ENNReal.toReal_one]

/-- **The finiteness hypothesis `χ_β ≠ ⊤` cannot be dropped from the real-valued tail-sum bound**:
at `χ_β = ⊤` the right-hand side `(χ_β).toReal` is `0` while the left-hand side is at least
`P_β(|K_0| ≥ 1) = 1`.  This is why the extended-nonnegative `sum_lawTailAt_le_lawSusceptibility` is
the unconditional form, and why any real-valued conclusion such as
`SourceModelData.TwoIntensityTailComparison` must come with `χ_{β₁} ≠ ⊤`. -/
theorem not_forall_sum_lawTail_le_toReal_of_eq_top (β : ℝ≥0)
    (h : M.lawSusceptibility β = ⊤) :
    ¬ ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 n, M.lawTail β k ≤ (M.lawSusceptibility β).toReal := by
  intro hb
  have h1 := hb 1 le_rfl
  rw [h, ENNReal.toReal_top, Finset.Icc_self, Finset.sum_singleton, M.lawTail_one] at h1
  norm_num at h1

/-- **The source-level two-intensity comparison forces a finite susceptibility at the lower
intensity.**  With `β₁ = β₂` and `n = 1` its right-hand side is `2 · (χ_{β₁}).toReal`, so at
`χ_{β₁} = ⊤` it would assert `1 ≤ 0`.  This is an exactness statement about the interface
`SourceModelData.TwoIntensityTailComparison`, not a defect of the source: there `χ_{β₁}` is a real
number. -/
theorem not_twoIntensityTailComparison_of_lawSusceptibility_eq_top {A : ℝ}
    (β : ℝ≥0) (hβ : 0 < β) (h : M.lawSusceptibility β = ⊤) :
    ¬ M.TwoIntensityTailComparison A := by
  intro hDM
  have hbound := hDM β β 1 hβ le_rfl le_rfl
  rw [h, ENNReal.toReal_top, M.lawTail_one] at hbound
  have hzero : (4 * A / (β : ℝ) * ((β : ℝ) - (β : ℝ)) ^ 2) = 0 := by ring
  rw [hzero] at hbound
  norm_num at hbound

/-! ### The real-valued consequences, at finite susceptibility -/

/-- **The real tail sum is dominated by the real susceptibility**, under the explicit hypothesis
`χ_β ≠ ⊤`.  This is the form `∑_{k ≤ n} P_{β₁}(|K_0| ≥ k) ≤ χ_{β₁}` used in the source's
two-intensity comparison. -/
theorem sum_lawTail_le_toReal (β : ℝ≥0) (n : ℕ) (hχ : M.lawSusceptibility β ≠ ⊤) :
    ∑ k ∈ Finset.Icc 1 n, M.lawTail β k ≤ (M.lawSusceptibility β).toReal := by
  have hsum : (∑ k ∈ Finset.Icc 1 n, M.lawTailAt β k).toReal
      = ∑ k ∈ Finset.Icc 1 n, M.lawTail β k := by
    rw [ENNReal.toReal_sum fun k _ => M.lawTailAt_ne_top β k]
    exact Finset.sum_congr rfl fun k _ => (M.lawTail_eq_toReal_lawTailAt β k).symm
  calc ∑ k ∈ Finset.Icc 1 n, M.lawTail β k
      = (∑ k ∈ Finset.Icc 1 n, M.lawTailAt β k).toReal := hsum.symm
    _ ≤ (M.lawSusceptibility β).toReal :=
        ENNReal.toReal_mono hχ (M.sum_lawTailAt_le_lawSusceptibility β n)

/-- **The real Markov bound** `n · P_β(|K_0| ≥ n) ≤ χ_β`, under the explicit hypothesis
`χ_β ≠ ⊤`. -/
theorem lawTail_mul_le_toReal (β : ℝ≥0) (n : ℕ) (hχ : M.lawSusceptibility β ≠ ⊤) :
    (n : ℝ) * M.lawTail β n ≤ (M.lawSusceptibility β).toReal := by
  have h := ENNReal.toReal_mono hχ (M.mul_lawTailAt_le_lawSusceptibility β n)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← M.lawTail_eq_toReal_lawTailAt β n] at h

/-- **A finite susceptibility makes the tail series summable.**  This is the summability of
`n ↦ P_β(|K_0| ≥ n)` that the layer-cake passage needs; it is a consequence of `χ_β ≠ ⊤`, not a
separate hypothesis. -/
theorem summable_lawTail_of_ne_top (β : ℝ≥0) (hχ : M.lawSusceptibility β ≠ ⊤) :
    Summable fun k : ℕ => M.lawTail β (k + 1) := by
  have htsum : (∑' k : ℕ, M.lawTailAt β (k + 1)) ≠ ⊤ := by
    rw [← M.lawSusceptibility_eq_tsum_lawTailAt β]
    exact hχ
  have h : Summable fun k : ℕ => (M.lawTailAt β (k + 1)).toReal :=
    ENNReal.summable_toReal htsum
  simpa only [M.lawTail_eq_toReal_lawTailAt] using h

/-- **The source's layer-cake identity in real form**: at finite susceptibility the tail series is
summable and `χ_β = ∑_{k ≥ 1} P_β(|K_0| ≥ k)`.  This is the exact equality behind
`sum_lawTail_le_toReal`; the summability conjunct is what makes the real `tsum` meaningful (for
`χ_β = ⊤` both sides would be `0` by Lean's `tsum` convention). -/
theorem summable_tsum_lawTail_eq_toReal (β : ℝ≥0) (hχ : M.lawSusceptibility β ≠ ⊤) :
    Summable (fun k : ℕ => M.lawTail β (k + 1)) ∧
      ∑' k : ℕ, M.lawTail β (k + 1) = (M.lawSusceptibility β).toReal := by
  refine ⟨M.summable_lawTail_of_ne_top β hχ, ?_⟩
  have h1 : ∑' k : ℕ, M.lawTail β (k + 1)
      = ∑' k : ℕ, (M.lawTailAt β (k + 1)).toReal :=
    tsum_congr fun k => M.lawTail_eq_toReal_lawTailAt β (k + 1)
  rw [h1, ← ENNReal.tsum_toReal_eq fun k => M.lawTailAt_ne_top β (k + 1),
    ← M.lawSusceptibility_eq_tsum_lawTailAt β]

/-- The critical-law form of `sum_lawTail_le_toReal`: the function `M.tailProb` is exactly
`M.lawTail M.betaCrit`. -/
theorem sum_tailProb_le_toReal (n : ℕ) (hχ : M.lawSusceptibility M.betaCrit ≠ ⊤) :
    ∑ k ∈ Finset.Icc 1 n, M.tailProb k ≤ (M.lawSusceptibility M.betaCrit).toReal := by
  have h := M.sum_lawTail_le_toReal M.betaCrit n hχ
  rwa [Finset.sum_congr rfl fun k _ => M.lawTail_betaCrit k] at h

/-! ### The layer cake at the cutoff law of the source's Case 3

The source's Proposition I.4.15, Case 3 (p. 47), writes verbatim
`E_{β_c,r}|K| = ∑_{n=1}^{∞} P_{β_c,r}(|K| ≥ n)`.  The statements below are that identity at the
cutoff law `M.cutLaw r` and its first moment `M.cutMoment 1 r`, together with the truncation and the
real form that the source uses to bound `E_{β_c,r}|K|` by `∑_{n ≤ N} P_{β_c}(|K| ≥ n)`. -/

/-- `P_{β_c,r}(|K_0| ≥ k)` at the cutoff law: the source's `P_{β_c,r}(|K| ≥ n)`. -/
noncomputable def cutLawTailAt (r : ℝ) (k : ℕ) : ℝ≥0∞ :=
  (M.cutLaw r) {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}

theorem cutLawTailAt_eq (r : ℝ) (k : ℕ) :
    M.cutLawTailAt r k = (M.cutLaw r) {ω : Config M.V |
      (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} :=
  rfl

theorem cutLawTailAt_ne_top (r : ℝ) (k : ℕ) : M.cutLawTailAt r k ≠ ⊤ := by
  have : IsProbabilityMeasure (M.cutLaw r) :=
    inferInstanceAs (IsProbabilityMeasure
      (longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit))
  have hle : M.cutLawTailAt r k ≤ 1 := by
    calc M.cutLawTailAt r k ≤ M.cutLaw r Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

/-- The cutoff first moment is the cluster volume integral at the cutoff law. -/
theorem cutMoment_one_eq_lintegral_clusterVol (r : ℝ) :
    M.cutMoment 1 r = ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r) := by
  change (∫⁻ ω, (clusterVol ω (0 : M.V)) ^ 1 ∂(M.cutLaw r)) = _
  simp only [pow_one]

/-- **The source's identity `E_{β_c,r}|K| = ∑_{n ≥ 1} P_{β_c,r}(|K| ≥ n)`.** -/
theorem cutMoment_one_eq_tsum_cutLawTailAt (r : ℝ) :
    M.cutMoment 1 r = ∑' k : ℕ, M.cutLawTailAt r (k + 1) := by
  rw [M.cutMoment_one_eq_lintegral_clusterVol r,
    LayerCake.lintegral_eq_tsum_meas_lt (measurable_clusterVol (0 : M.V))
      (M.intValued_clusterVol 0)]
  refine tsum_congr fun k => ?_
  have hset : {ω : Config M.V | (k : ℝ≥0∞) < clusterVol ω (0 : M.V)}
      = {ω : Config M.V | ((k + 1 : ℕ) : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact LayerCake.lt_iff_succ_le (M.intValued_clusterVol 0 ω) k
  rw [hset]
  rfl

/-- **The truncated layer cake at the cutoff law**: `E_{β_c,r}[|K_0| ∧ n] = ∑_{k=1}^{n}
P_{β_c,r}(|K_0| ≥ k)`. -/
theorem cutLaw_lintegral_min_eq_sum (r : ℝ) (n : ℕ) :
    ∫⁻ ω, min (clusterVol ω (0 : M.V)) (n : ℝ≥0∞) ∂(M.cutLaw r)
      = ∑ k ∈ Finset.Icc 1 n, M.cutLawTailAt r k :=
  LayerCake.lintegral_min_eq_sum_meas_le (measurable_clusterVol (0 : M.V))
    (M.intValued_clusterVol 0) n

/-- **The source's bound `∑_{n=1}^{N} P_{β_c,r}(|K| ≥ n) ≤ E_{β_c,r}|K|`** in real form, at finite
cutoff first moment. -/
theorem sum_cutLawTail_le_cutMoment_one (r : ℝ) (n : ℕ) (h : M.cutMoment 1 r ≠ ⊤) :
    ∑ k ∈ Finset.Icc 1 n,
        (M.cutLaw r).real {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ (M.cutMoment 1 r).toReal := by
  have hsum : (∑ k ∈ Finset.Icc 1 n, M.cutLawTailAt r k).toReal
      = ∑ k ∈ Finset.Icc 1 n,
          (M.cutLaw r).real {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} := by
    rw [ENNReal.toReal_sum fun k _ => M.cutLawTailAt_ne_top r k]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hle : ∑ k ∈ Finset.Icc 1 n, M.cutLawTailAt r k ≤ M.cutMoment 1 r := by
    rw [← M.cutLaw_lintegral_min_eq_sum r n, M.cutMoment_one_eq_lintegral_clusterVol r]
    exact lintegral_mono fun ω => min_le_left _ _
  calc ∑ k ∈ Finset.Icc 1 n,
        (M.cutLaw r).real {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      = (∑ k ∈ Finset.Icc 1 n, M.cutLawTailAt r k).toReal := hsum.symm
    _ ≤ (M.cutMoment 1 r).toReal := ENNReal.toReal_mono h hle

/-! ### Finite-window tails and their limits -/

/-- **Continuity from below for the cluster-volume tail along a monotone exhaustion**: the tail
probability is the supremum of the tail probabilities of the finite windows `F n`,
`P_β(|K_0| ≥ k) = ⨆_n P_β(|K_0 ∩ F_n| ≥ k)`. -/
theorem lawTailAt_eq_iSup_lawWindowTail (β : ℝ≥0) (k : ℕ) (F : ℕ → Finset M.V)
    (hmono : Monotone F) (hF : ∀ s : Finset M.V, ∃ n, s ⊆ F n) :
    M.lawTailAt β k = ⨆ n, (M.law β) {ω : Config M.V |
      (k : ℝ≥0∞) ≤ clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V)} := by
  have hset : {ω : Config M.V | (k : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      = ⋃ n, {ω : Config M.V |
          (k : ℝ≥0∞) ≤ clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      have hint : ∀ n, ∃ j : ℕ,
          clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V) = (j : ℝ≥0∞) ∨
          clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V) = ⊤ := by
        intro n
        obtain ⟨g, hg⟩ : ∃ g : ℕ∞,
            clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V)
              = ((g : ℕ∞) : ℝ≥0∞) := ⟨_, rfl⟩
        cases g using ENat.recTopCoe with
        | top => exact ⟨0, Or.inr (hg.trans ENat.toENNReal_top)⟩
        | coe j => exact ⟨j, Or.inl (hg.trans (ENat.toENNReal_coe j))⟩
      refine LayerCake.exists_coe_le_of_le_iSup hint ?_
      rw [← clusterVol_eq_iSup_window ω (0 : M.V) F hF]
      exact h
    · rintro ⟨n, hn⟩
      refine le_trans hn ?_
      have h1 : clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V)
          ≤ clusterVolIn ω (0 : M.V) Set.univ := clusterVolIn_mono (Set.subset_univ _)
      rwa [clusterVolIn_univ] at h1
  rw [lawTailAt, hset]
  refine Monotone.measure_iUnion fun m n hmn => ?_
  refine fun ω hω => ?_
  exact le_trans hω (clusterVolIn_mono (Finset.coe_subset.2 (hmono hmn)))

/-- **Monotone convergence of the windowed susceptibility**:
`χ_β = ⨆_n E_β|K_0 ∩ F_n|` along a monotone exhaustion.  This is the faithful finite-volume limit
of the first moment; it needs no finiteness hypothesis on `χ_β`. -/
theorem lawSusceptibility_eq_iSup_lintegral_clusterVolIn (β : ℝ≥0) (F : ℕ → Finset M.V)
    (hmono : Monotone F) (hF : ∀ s : Finset M.V, ∃ n, s ⊆ F n) :
    M.lawSusceptibility β = ⨆ n, ∫⁻ ω,
      clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V) ∂(M.law β) := by
  have hmono' : Monotone fun n : ℕ => fun ω : Config M.V =>
      clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V) := by
    intro m n hmn ω
    exact clusterVolIn_mono (Finset.coe_subset.2 (hmono hmn))
  have hmeas : ∀ n : ℕ, Measurable fun ω : Config M.V =>
      clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V) :=
    fun n => measurable_clusterVolIn 0 _
  have hpt : (fun ω : Config M.V => clusterVol ω (0 : M.V))
      = fun ω => ⨆ n, clusterVolIn ω (0 : M.V) ((F n : Finset M.V) : Set M.V) :=
    funext fun ω => clusterVol_eq_iSup_window ω (0 : M.V) F hF
  change (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) = _
  rw [hpt, lintegral_iSup hmeas hmono']

/-! ### The susceptibility as a two-point row sum -/

/-- **The row-sum identity for the susceptibility**: `χ_β = ∑_y P_β(0 ↔ y)`, in `ℝ≥0∞`. -/
theorem lawSusceptibility_eq_tsum_twoPointENN (β : ℝ≥0) :
    M.lawSusceptibility β
      = ∑' y : M.V, (M.law β) {ω : Config M.V | Connects ω (0 : M.V) y} := by
  have hf : ∀ y : M.V, Measurable fun ω : Config M.V =>
      (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y := fun y =>
    Measurable.indicator measurable_const (measurableSet_cluster_mem (0 : M.V) y)
  have key : ∫⁻ ω, ∑' y : M.V, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        ∂(M.law β)
      = ∑' y : M.V, (M.law β) {ω : Config M.V | Connects ω (0 : M.V) y} := by
    rw [lintegral_tsum fun y => (hf y).aemeasurable]
    refine tsum_congr fun y => ?_
    have hcongr : ∀ a : Config M.V, (cluster a (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        = {ω : Config M.V | y ∈ cluster ω (0 : M.V)}.indicator (fun _ => (1 : ℝ≥0∞)) a := by
      intro a
      by_cases h : y ∈ cluster a (0 : M.V)
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show a ∈ {ω : Config M.V | y ∈ cluster ω (0 : M.V)} from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem
            (show a ∉ {ω : Config M.V | y ∈ cluster ω (0 : M.V)} from h)]
    rw [lintegral_congr hcongr,
      lintegral_indicator_const (measurableSet_cluster_mem (0 : M.V) y) (1 : ℝ≥0∞), one_mul]
    rw [show {ω : Config M.V |
        y ∈ cluster ω (0 : M.V)}
        = {ω : Config M.V | Connects ω (0 : M.V) y} from Set.ext fun ω => mem_cluster_iff]
  calc M.lawSusceptibility β
      = ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β) := rfl
    _ = ∫⁻ ω, ∑' y : M.V, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
          ∂(M.law β) := lintegral_congr fun ω => clusterVol_eq_tsum ω (0 : M.V)
    _ = ∑' y : M.V, (M.law β) {ω : Config M.V | Connects ω (0 : M.V) y} := key

/-- **The source's row-sum identity** `χ_β = E_β|K_0| = ∑_y τ_β(0,y)`, in terms of the model's
two-point function `M.twoPoint`. -/
theorem lawSusceptibility_eq_tsum_twoPoint (β : ℝ≥0) :
    M.lawSusceptibility β = ∑' y : M.V, ENNReal.ofReal (M.twoPoint β (0 : M.V) y) := by
  rw [M.lawSusceptibility_eq_tsum_twoPointENN β]
  refine tsum_congr fun y => ?_
  change (M.law β) {ω : Config M.V | Connects ω (0 : M.V) y}
    = ENNReal.ofReal ((M.law β).real {ω : Config M.V | Connects ω (0 : M.V) y})
  exact (ENNReal.ofReal_toReal (measure_ne_top (M.law β) _)).symm

/-- **Nonvacuity check: the row-sum identity computes the susceptibility at zero intensity.**
At `β = 0` no edge is open, so `|K_0| = 1` and the row sum `∑_y τ_0(0,y)` is `τ_0(0,0) = 1` plus
vanishing off-diagonal terms.  This checks `lawSusceptibility_eq_tsum_twoPoint` against a case
whose value is known independently, and it exhibits a parameter at which the hypothesis
`χ_β ≠ ⊤` of the real-valued bounds is satisfied. -/
theorem lawSusceptibility_zero : M.lawSusceptibility 0 = 1 := by
  have hdiag : M.twoPoint 0 (0 : M.V) (0 : M.V) = 1 := by
    have hlaw : M.law 0 = Measure.dirac (∅ : Config M.V) :=
      longRangeMeasure_zero M.kernel M.kernel_nonneg
    have huniv : {ω : Config M.V | Connects ω (0 : M.V) (0 : M.V)} = Set.univ :=
      Set.eq_univ_of_forall fun ω => connects_refl ω (0 : M.V)
    change (M.law 0).real {ω : Config M.V | Connects ω (0 : M.V) (0 : M.V)} = 1
    rw [huniv, hlaw, Measure.dirac_real_apply]
    simp
  have hoff : ∀ y : M.V, y ≠ 0 → M.twoPoint 0 (0 : M.V) y = 0 := by
    intro y hy
    have hlaw : M.law 0 = Measure.dirac (∅ : Config M.V) :=
      longRangeMeasure_zero M.kernel M.kernel_nonneg
    have hnot : (∅ : Config M.V) ∉ {ω : Config M.V | Connects ω (0 : M.V) y} := by
      simp only [Set.mem_ofPred_eq, Connects, PercLib.Percolation.Bond.openGraph_empty,
        SimpleGraph.reachable_bot]
      exact Ne.symm hy
    change (M.law 0).real {ω : Config M.V | Connects ω (0 : M.V) y} = 0
    rw [hlaw, Measure.dirac_real_apply, Set.indicator_of_notMem hnot]
  rw [M.lawSusceptibility_eq_tsum_twoPoint 0,
    tsum_eq_single (0 : M.V) (fun y hy => ?_)]
  · rw [hdiag, ENNReal.ofReal_one]
  · rw [hoff y hy, ENNReal.ofReal_zero]

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.Orchestration

set_option linter.hashCommand false in
#print axioms PercLib.CriticalLRP.LayerCake.lintegral_eq_tsum_meas_lt

set_option linter.hashCommand false in
#print axioms PercLib.CriticalLRP.LayerCake.lintegral_min_eq_sum_meas_le

set_option linter.hashCommand false in
#print axioms PercLib.CriticalLRP.LayerCake.exists_coe_le_of_le_iSup

set_option linter.hashCommand false in
#print axioms SourceModelData.lawSusceptibility_eq_tsum_lawTailAt

set_option linter.hashCommand false in
#print axioms SourceModelData.lintegral_min_clusterVol_eq_sum

set_option linter.hashCommand false in
#print axioms SourceModelData.sum_range_lawTailAt_succ

set_option linter.hashCommand false in
#print axioms SourceModelData.lawSusceptibility_eq_iSup_lintegral_min

set_option linter.hashCommand false in
#print axioms SourceModelData.sum_lawTailAt_le_lawSusceptibility

set_option linter.hashCommand false in
#print axioms SourceModelData.mul_lawTailAt_le_lawSusceptibility

set_option linter.hashCommand false in
#print axioms SourceModelData.sum_lawTail_le_toReal

set_option linter.hashCommand false in
#print axioms SourceModelData.summable_tsum_lawTail_eq_toReal

set_option linter.hashCommand false in
#print axioms SourceModelData.lawTail_mul_le_toReal

set_option linter.hashCommand false in
#print axioms SourceModelData.summable_lawTail_of_ne_top

set_option linter.hashCommand false in
#print axioms SourceModelData.sum_tailProb_le_toReal

set_option linter.hashCommand false in
#print axioms SourceModelData.lawTail_one

set_option linter.hashCommand false in
#print axioms SourceModelData.not_forall_sum_lawTail_le_toReal_of_eq_top

set_option linter.hashCommand false in
#print axioms SourceModelData.not_twoIntensityTailComparison_of_lawSusceptibility_eq_top

set_option linter.hashCommand false in
#print axioms SourceModelData.cutMoment_one_eq_tsum_cutLawTailAt

set_option linter.hashCommand false in
#print axioms SourceModelData.cutLaw_lintegral_min_eq_sum

set_option linter.hashCommand false in
#print axioms SourceModelData.sum_cutLawTail_le_cutMoment_one

set_option linter.hashCommand false in
#print axioms SourceModelData.lawTailAt_eq_iSup_lawWindowTail

set_option linter.hashCommand false in
#print axioms SourceModelData.lawSusceptibility_eq_iSup_lintegral_clusterVolIn

set_option linter.hashCommand false in
#print axioms SourceModelData.lawSusceptibility_eq_tsum_twoPointENN

set_option linter.hashCommand false in
#print axioms SourceModelData.lawSusceptibility_eq_tsum_twoPoint

set_option linter.hashCommand false in
#print axioms SourceModelData.lawSusceptibility_zero

end PercLib.CriticalLRP.Orchestration
