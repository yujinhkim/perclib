/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Five-point tree-graph infrastructure supplied by Ultramath `smwpj8umm` member m2
and integrated from a verified candidate. The full deterministic five-point
realization and fourth-moment theorem are not asserted by these modules.
-/
module

/-
Seven-fold BK at the native countable law: seven increasing events with seven pairwise
disjoint finite open certificates have probability at most the product of their probabilities.

This is the `n = 7` companion of `prodBernoulli_five_wit_le`
(`PercLib.CriticalLRP.Correlation.ThirdMoment`), which is the `n = 5` case used for the
third moment.  The fourth cluster moment requires seven certificates per tree shape.
-/
public import PercLib.CriticalLRP.Correlation.ThirdMoment

open Set MeasureTheory
open scoped ENNReal
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

/-- Seven pairwise disjoint finite certificates lying in `ω` force `ω` into the six-fold
nested disjoint occurrence `((((((A₀ □ A₁) □ A₂) □ A₃) □ A₄) □ A₅) □ A₆)`. -/
theorem mem_foldl_disjointOccurrence_of_seven {ι : Type*}
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Set (Set ι)}
    (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁) (h₂ : IsUpperSet A₂) (h₃ : IsUpperSet A₃)
    (h₄ : IsUpperSet A₄) (h₅ : IsUpperSet A₅) (h₆ : IsUpperSet A₆) {ω : Set ι}
    {W₀ W₁ W₂ W₃ W₄ W₅ W₆ : Set ι}
    (hf₀ : W₀.Finite) (hf₁ : W₁.Finite) (hf₂ : W₂.Finite) (hf₃ : W₃.Finite)
    (hf₄ : W₄.Finite) (hf₅ : W₅.Finite) (hf₆ : W₆.Finite)
    (hs₀ : W₀ ⊆ ω) (hs₁ : W₁ ⊆ ω) (hs₂ : W₂ ⊆ ω) (hs₃ : W₃ ⊆ ω)
    (hs₄ : W₄ ⊆ ω) (hs₅ : W₅ ⊆ ω) (hs₆ : W₆ ⊆ ω)
    (hm₀ : W₀ ∈ A₀) (hm₁ : W₁ ∈ A₁) (hm₂ : W₂ ∈ A₂) (hm₃ : W₃ ∈ A₃)
    (hm₄ : W₄ ∈ A₄) (hm₅ : W₅ ∈ A₅) (hm₆ : W₆ ∈ A₆)
    (hd₀₁ : Disjoint W₀ W₁) (hd₀₂ : Disjoint W₀ W₂) (hd₀₃ : Disjoint W₀ W₃)
    (hd₀₄ : Disjoint W₀ W₄) (hd₀₅ : Disjoint W₀ W₅) (hd₀₆ : Disjoint W₀ W₆)
    (hd₁₂ : Disjoint W₁ W₂) (hd₁₃ : Disjoint W₁ W₃) (hd₁₄ : Disjoint W₁ W₄)
    (hd₁₅ : Disjoint W₁ W₅) (hd₁₆ : Disjoint W₁ W₆)
    (hd₂₃ : Disjoint W₂ W₃) (hd₂₄ : Disjoint W₂ W₄) (hd₂₅ : Disjoint W₂ W₅)
    (hd₂₆ : Disjoint W₂ W₆) (hd₃₄ : Disjoint W₃ W₄) (hd₃₅ : Disjoint W₃ W₅)
    (hd₃₆ : Disjoint W₃ W₆) (hd₄₅ : Disjoint W₄ W₅) (hd₄₆ : Disjoint W₄ W₆)
    (hd₅₆ : Disjoint W₅ W₆) :
    ω ∈ List.foldl disjointOccurrence A₀ [A₁, A₂, A₃, A₄, A₅, A₆] := by
  -- one step of the iteration: from a certificate `S` for the current event and a fresh
  -- certificate `W ∈ B`, get `S ∪ W` as a certificate for `current □ B`.
  have step : ∀ {S : Set ι} {C : Set (Set ι)} {B : Set (Set ι)} {W : Set ι},
      IsUpperSet C → IsUpperSet B → S.Finite → C ∈ [C] → S ∈ C → W.Finite → W ∈ B →
      Disjoint S W → S ∪ W ∈ disjointOccurrence C B := by
    intro S C B W _ hB hSf _ hSC hWf hWB hd
    exact (mem_disjointOccurrence_iff_open ‹IsUpperSet C› hB (S ∪ W)).mpr
      ⟨S, W, hSf, hWf, hd, subset_union_left, subset_union_right, hSC, hWB⟩
  -- telescoping family of certificates and events
  have hB₁ : IsUpperSet (disjointOccurrence A₀ A₁) := isUpperSet_disjointOccurrence h₀ h₁
  have hB₂ : IsUpperSet (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) :=
    isUpperSet_disjointOccurrence hB₁ h₂
  have hB₃ : IsUpperSet (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) :=
    isUpperSet_disjointOccurrence hB₂ h₃
  have hB₄ : IsUpperSet (disjointOccurrence
      (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄) :=
    isUpperSet_disjointOccurrence hB₃ h₄
  have hB₅ : IsUpperSet (disjointOccurrence (disjointOccurrence
      (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄) A₅) :=
    isUpperSet_disjointOccurrence hB₄ h₅
  -- step 1: `ω ∈ A₀ □ A₁` and `W₀ ∪ W₁` is a certificate for it
  have h1 : ω ∈ disjointOccurrence A₀ A₁ :=
    (mem_disjointOccurrence_iff_open h₀ h₁ ω).mpr
      ⟨W₀, W₁, hf₀, hf₁, hd₀₁, hs₀, hs₁, hm₀, hm₁⟩
  have hu1 : W₀ ∪ W₁ ∈ disjointOccurrence A₀ A₁ :=
    (mem_disjointOccurrence_iff_open h₀ h₁ (W₀ ∪ W₁)).mpr
      ⟨W₀, W₁, hf₀, hf₁, hd₀₁, subset_union_left, subset_union_right, hm₀, hm₁⟩
  -- step 2
  have h2 : ω ∈ disjointOccurrence (disjointOccurrence A₀ A₁) A₂ :=
    (mem_disjointOccurrence_iff_open hB₁ h₂ ω).mpr
      ⟨W₀ ∪ W₁, W₂, hf₀.union hf₁, hf₂, disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩,
        union_subset hs₀ hs₁, hs₂, hu1, hm₂⟩
  have hu2 : W₀ ∪ W₁ ∪ W₂ ∈ disjointOccurrence (disjointOccurrence A₀ A₁) A₂ :=
    (mem_disjointOccurrence_iff_open hB₁ h₂ (W₀ ∪ W₁ ∪ W₂)).mpr
      ⟨W₀ ∪ W₁, W₂, hf₀.union hf₁, hf₂, disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩,
        subset_union_left, subset_union_right, hu1, hm₂⟩
  -- step 3
  have h3 : ω ∈ disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃ :=
    (mem_disjointOccurrence_iff_open hB₂ h₃ ω).mpr
      ⟨W₀ ∪ W₁ ∪ W₂, W₃, (hf₀.union hf₁).union hf₂, hf₃,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hd₀₃, hd₁₃⟩, hd₂₃⟩,
        union_subset (union_subset hs₀ hs₁) hs₂, hs₃, hu2, hm₃⟩
  have hu3 : W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∈
      disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃ :=
    (mem_disjointOccurrence_iff_open hB₂ h₃ (W₀ ∪ W₁ ∪ W₂ ∪ W₃)).mpr
      ⟨W₀ ∪ W₁ ∪ W₂, W₃, (hf₀.union hf₁).union hf₂, hf₃,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hd₀₃, hd₁₃⟩, hd₂₃⟩,
        subset_union_left, subset_union_right, hu2, hm₃⟩
  -- step 4
  have h4 : ω ∈ disjointOccurrence
      (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄ :=
    (mem_disjointOccurrence_iff_open hB₃ h₄ ω).mpr
      ⟨W₀ ∪ W₁ ∪ W₂ ∪ W₃, W₄, ((hf₀.union hf₁).union hf₂).union hf₃, hf₄,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr
          ⟨hd₀₄, hd₁₄⟩, hd₂₄⟩, hd₃₄⟩,
        union_subset (union_subset (union_subset hs₀ hs₁) hs₂) hs₃, hs₄, hu3, hm₄⟩
  have hu4 : W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∈
      disjointOccurrence (disjointOccurrence (disjointOccurrence (disjointOccurrence
        A₀ A₁) A₂) A₃) A₄ :=
    (mem_disjointOccurrence_iff_open hB₃ h₄ (W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄)).mpr
      ⟨W₀ ∪ W₁ ∪ W₂ ∪ W₃, W₄, ((hf₀.union hf₁).union hf₂).union hf₃, hf₄,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr
          ⟨hd₀₄, hd₁₄⟩, hd₂₄⟩, hd₃₄⟩,
        subset_union_left, subset_union_right, hu3, hm₄⟩
  -- step 5
  have h5 : ω ∈ disjointOccurrence (disjointOccurrence
      (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄) A₅ :=
    (mem_disjointOccurrence_iff_open hB₄ h₅ ω).mpr
      ⟨W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄, W₅, (((hf₀.union hf₁).union hf₂).union hf₃).union hf₄, hf₅,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr
          ⟨disjoint_union_left.mpr ⟨hd₀₅, hd₁₅⟩, hd₂₅⟩, hd₃₅⟩, hd₄₅⟩,
        union_subset (union_subset (union_subset (union_subset hs₀ hs₁) hs₂) hs₃) hs₄, hs₅,
        hu4, hm₅⟩
  have hu5 : W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∪ W₅ ∈ disjointOccurrence (disjointOccurrence
      (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄) A₅ :=
    (mem_disjointOccurrence_iff_open hB₄ h₅ (W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∪ W₅)).mpr
      ⟨W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄, W₅, (((hf₀.union hf₁).union hf₂).union hf₃).union hf₄, hf₅,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr
          ⟨disjoint_union_left.mpr ⟨hd₀₅, hd₁₅⟩, hd₂₅⟩, hd₃₅⟩, hd₄₅⟩,
        subset_union_left, subset_union_right, hu4, hm₅⟩
  -- step 6
  have h6 : ω ∈ disjointOccurrence (disjointOccurrence (disjointOccurrence
      (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄) A₅) A₆ :=
    (mem_disjointOccurrence_iff_open hB₅ h₆ ω).mpr
      ⟨W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∪ W₅, W₆,
        ((((hf₀.union hf₁).union hf₂).union hf₃).union hf₄).union hf₅, hf₆,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr
          ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hd₀₆, hd₁₆⟩, hd₂₆⟩, hd₃₆⟩,
            hd₄₆⟩, hd₅₆⟩,
        union_subset (union_subset (union_subset (union_subset (union_subset hs₀ hs₁) hs₂)
          hs₃) hs₄) hs₅, hs₆, hu5, hm₆⟩
  have hlist : List.foldl disjointOccurrence A₀ [A₁, A₂, A₃, A₄, A₅, A₆]
      = disjointOccurrence (disjointOccurrence (disjointOccurrence
          (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄)
            A₅) A₆ := rfl
  rw [hlist]
  exact h6

/-- **Seven-fold BK at the native countable law.**  Seven increasing cylinder events with
seven pairwise disjoint finite open certificates have probability at most the product of
their probabilities, for every profile on a countable coordinate set. -/
theorem prodBernoulli_seven_wit_le {ι : Type*} [Countable ι] (p : ι → unitInterval)
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Set (Set ι)}
    (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁) (h₂ : IsUpperSet A₂) (h₃ : IsUpperSet A₃)
    (h₄ : IsUpperSet A₄) (h₅ : IsUpperSet A₅) (h₆ : IsUpperSet A₆) :
    prodBernoulli p
      {ω | ∃ W₀ W₁ W₂ W₃ W₄ W₅ W₆ : Set ι,
            W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧ W₅.Finite ∧
              W₆.Finite ∧
            W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧ W₅ ⊆ ω ∧ W₆ ⊆ ω ∧
            W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧ W₅ ∈ A₅ ∧ W₆ ∈ A₆ ∧
            Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
              Disjoint W₀ W₅ ∧ Disjoint W₀ W₆ ∧
            Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧ Disjoint W₁ W₅ ∧
              Disjoint W₁ W₆ ∧
            Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₂ W₅ ∧ Disjoint W₂ W₆ ∧
            Disjoint W₃ W₄ ∧ Disjoint W₃ W₅ ∧ Disjoint W₃ W₆ ∧
            Disjoint W₄ W₅ ∧ Disjoint W₄ W₆ ∧ Disjoint W₅ W₆}
      ≤ prodBernoulli p A₀ * (prodBernoulli p A₁ * (prodBernoulli p A₂ *
          (prodBernoulli p A₃ * (prodBernoulli p A₄ * (prodBernoulli p A₅ *
            prodBernoulli p A₆))))) := by
  have hmono : prodBernoulli p
      {ω | ∃ W₀ W₁ W₂ W₃ W₄ W₅ W₆ : Set ι,
            W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧ W₅.Finite ∧
              W₆.Finite ∧
            W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧ W₅ ⊆ ω ∧ W₆ ⊆ ω ∧
            W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧ W₅ ∈ A₅ ∧ W₆ ∈ A₆ ∧
            Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
              Disjoint W₀ W₅ ∧ Disjoint W₀ W₆ ∧
            Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧ Disjoint W₁ W₅ ∧
              Disjoint W₁ W₆ ∧
            Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₂ W₅ ∧ Disjoint W₂ W₆ ∧
            Disjoint W₃ W₄ ∧ Disjoint W₃ W₅ ∧ Disjoint W₃ W₆ ∧
            Disjoint W₄ W₅ ∧ Disjoint W₄ W₆ ∧ Disjoint W₅ W₆}
      ≤ prodBernoulli p (List.foldl disjointOccurrence A₀ [A₁, A₂, A₃, A₄, A₅, A₆]) := by
    refine measure_mono ?_
    rintro ω ⟨W₀, W₁, W₂, W₃, W₄, W₅, W₆, hf₀, hf₁, hf₂, hf₃, hf₄, hf₅, hf₆,
      hs₀, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hm₀, hm₁, hm₂, hm₃, hm₄, hm₅, hm₆,
      hd₀₁, hd₀₂, hd₀₃, hd₀₄, hd₀₅, hd₀₆, hd₁₂, hd₁₃, hd₁₄, hd₁₅, hd₁₆,
      hd₂₃, hd₂₄, hd₂₅, hd₂₆, hd₃₄, hd₃₅, hd₃₆, hd₄₅, hd₄₆, hd₅₆⟩
    exact mem_foldl_disjointOccurrence_of_seven h₀ h₁ h₂ h₃ h₄ h₅ h₆
      hf₀ hf₁ hf₂ hf₃ hf₄ hf₅ hf₆ hs₀ hs₁ hs₂ hs₃ hs₄ hs₅ hs₆
      hm₀ hm₁ hm₂ hm₃ hm₄ hm₅ hm₆
      hd₀₁ hd₀₂ hd₀₃ hd₀₄ hd₀₅ hd₀₆ hd₁₂ hd₁₃ hd₁₄ hd₁₅ hd₁₆
      hd₂₃ hd₂₄ hd₂₅ hd₂₆ hd₃₄ hd₃₅ hd₃₆ hd₄₅ hd₄₆ hd₅₆
  refine hmono.trans ?_
  have hbk := countable_profile_bk_foldl p [A₁, A₂, A₃, A₄, A₅, A₆]
    (by intro B hB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
        rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h₁, h₂, h₃, h₄, h₅, h₆]) h₀
  simpa using hbk

/-- Sanity check: the five-fold statement is the `n = 5` special case of the same
pattern (imported, not reproved). -/
example {ι : Type*} [Countable ι] (p : ι → unitInterval)
    {A₀ A₁ A₂ A₃ A₄ : Set (Set ι)} (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁)
    (h₂ : IsUpperSet A₂) (h₃ : IsUpperSet A₃) (h₄ : IsUpperSet A₄) :
    prodBernoulli p
      {ω | ∃ W₀ W₁ W₂ W₃ W₄ : Set ι,
            W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧
            W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧
            W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧
            Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
            Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧
            Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₃ W₄}
      ≤ prodBernoulli p A₀ * (prodBernoulli p A₁ *
          (prodBernoulli p A₂ * (prodBernoulli p A₃ * prodBernoulli p A₄))) :=
  PercLib.CriticalLRP.TreeExpansion.prodBernoulli_five_wit_le p h₀ h₁ h₂ h₃ h₄

end PercLib.CriticalLRP.TreeExpansion.FivePoint
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.prodBernoulli_seven_wit_le
