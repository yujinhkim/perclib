/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
A conditional native third-moment reduction. Fivefold BK, Tonelli, and the
three five-factor tree sums are proved. The deterministic binary-arm
hypothesis remains exactly that: an exposed statement, not a completed proof.
-/

module

/-
Swarm smwj545c0 member m1 — infinite-native third cluster moment, `E|K_0|^3 <= 3 (E|K_0|)^5`
(Hutchcroft, arXiv:2508.18807v1, (I.2.2)/(I.2.3) at p = 3), reduced to a purely deterministic
binary-arm decomposition of the open graph.

File contents, in order
* `prodBernoulli_five_wit_le` (five-fold BK at the native countable law) and its witness algebra;
* extended-sum algebra: `tsum_two_mul`, `tsum_three_mul`, `tsum_permute_three_two`,
  `tsum_row_eq`, `tsum_col_eq`;
* `shape_one/two/three`: each labelled binary tree on four leaves contributes exactly `chi^5`;
* `lintegral_cardFun_cube_eq`: `E|K_x|^3` as the triple sum of three-point connection
  probabilities (Tonelli in `R>=0-infty`);
* `four_point_of_arm_decomposition`: (I.2.2) at `k = 3` from the deterministic arm decomposition
  (`ShapeWitness`, `ShapeEvent`);
* `third_moment_le_of_four_point`, `third_moment_le_of_arm_decomposition`: the two reductions.

`ShapeWitness`, `ShapeEvent` and `walkEdges` are provided by `Defs.lean`;
the open binary-arm hypothesis is deliberately not hidden by the reduction.
-/
public import PercLib.CriticalLRP.Correlation.ThirdMoment.Defs
public import PercLib.CriticalLRP.VolumeMoments.ErrorBounds
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.CountableBK
public import PercLib.Probability.DisjointOccurrenceAlgebra

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

variable {V : Type*}


open PercLib.Probability

/-! ## Five-fold pairwise-disjoint certificates imply the iterated disjoint occurrence -/

/-- If five increasing events have five pairwise disjoint finite open certificates at `ω`, then
`ω` lies in the four-fold nested disjoint occurrence `(((A₀ □ A₁) □ A₂) □ A₃) □ A₄`.  This is the
`n = 5` case of "pairwise disjoint witnesses imply the iterated disjoint occurrence", obtained by
iterating `mem_disjointOccurrence_iff_open` (only `IsUpperSet` monotonicity and pairwise
disjointness of finite sets is used). -/
theorem mem_foldl_disjointOccurrence_of_five {ι : Type*} {A₀ A₁ A₂ A₃ A₄ : Set (Set ι)}
    (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁) (h₂ : IsUpperSet A₂)
    (h₃ : IsUpperSet A₃) (h₄ : IsUpperSet A₄) {ω : Set ι}
    {W₀ W₁ W₂ W₃ W₄ : Set ι}
    (hf₀ : W₀.Finite) (hf₁ : W₁.Finite) (hf₂ : W₂.Finite) (hf₃ : W₃.Finite)
    (hf₄ : W₄.Finite)
    (hs₀ : W₀ ⊆ ω) (hs₁ : W₁ ⊆ ω) (hs₂ : W₂ ⊆ ω) (hs₃ : W₃ ⊆ ω) (hs₄ : W₄ ⊆ ω)
    (hm₀ : W₀ ∈ A₀) (hm₁ : W₁ ∈ A₁) (hm₂ : W₂ ∈ A₂) (hm₃ : W₃ ∈ A₃) (hm₄ : W₄ ∈ A₄)
    (hd₀₁ : Disjoint W₀ W₁) (hd₀₂ : Disjoint W₀ W₂) (hd₀₃ : Disjoint W₀ W₃)
    (hd₀₄ : Disjoint W₀ W₄) (hd₁₂ : Disjoint W₁ W₂) (hd₁₃ : Disjoint W₁ W₃)
    (hd₁₄ : Disjoint W₁ W₄) (hd₂₃ : Disjoint W₂ W₃) (hd₂₄ : Disjoint W₂ W₄)
    (hd₃₄ : Disjoint W₃ W₄) :
    ω ∈ List.foldl disjointOccurrence A₀ [A₁, A₂, A₃, A₄] := by
  have hB₁ : IsUpperSet (disjointOccurrence A₀ A₁) := isUpperSet_disjointOccurrence h₀ h₁
  have hB₂ : IsUpperSet (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) :=
    isUpperSet_disjointOccurrence hB₁ h₂
  have hB₃ : IsUpperSet (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) :=
    isUpperSet_disjointOccurrence hB₂ h₃
  -- step 1: `ω ∈ A₀ □ A₁`
  have h₁' : ω ∈ disjointOccurrence A₀ A₁ :=
    (mem_disjointOccurrence_iff_open h₀ h₁ ω).mpr
      ⟨W₀, W₁, hf₀, hf₁, hd₀₁, hs₀, hs₁, hm₀, hm₁⟩
  -- `W₀ ∪ W₁` is itself a certificate for `A₀ □ A₁`
  have hu₁ : W₀ ∪ W₁ ∈ disjointOccurrence A₀ A₁ :=
    (mem_disjointOccurrence_iff_open h₀ h₁ (W₀ ∪ W₁)).mpr
      ⟨W₀, W₁, hf₀, hf₁, hd₀₁, subset_union_left, subset_union_right, hm₀, hm₁⟩
  -- step 2: `ω ∈ (A₀ □ A₁) □ A₂`
  have h₂' : ω ∈ disjointOccurrence (disjointOccurrence A₀ A₁) A₂ :=
    (mem_disjointOccurrence_iff_open hB₁ h₂ ω).mpr
      ⟨W₀ ∪ W₁, W₂, hf₀.union hf₁, hf₂, disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩,
        union_subset hs₀ hs₁, hs₂, hu₁, hm₂⟩
  have hu₂ : W₀ ∪ W₁ ∪ W₂ ∈ disjointOccurrence (disjointOccurrence A₀ A₁) A₂ :=
    (mem_disjointOccurrence_iff_open hB₁ h₂ (W₀ ∪ W₁ ∪ W₂)).mpr
      ⟨W₀ ∪ W₁, W₂, hf₀.union hf₁, hf₂, disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩,
        subset_union_left, subset_union_right, hu₁, hm₂⟩
  -- step 3
  have h₃' : ω ∈ disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃ :=
    (mem_disjointOccurrence_iff_open hB₂ h₃ ω).mpr
      ⟨W₀ ∪ W₁ ∪ W₂, W₃, (hf₀.union hf₁).union hf₂, hf₃,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hd₀₃, hd₁₃⟩, hd₂₃⟩,
        union_subset (union_subset hs₀ hs₁) hs₂, hs₃, hu₂, hm₃⟩
  have hu₃ : W₀ ∪ W₁ ∪ W₂ ∪ W₃ ∈
      disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃ :=
    (mem_disjointOccurrence_iff_open hB₂ h₃ (W₀ ∪ W₁ ∪ W₂ ∪ W₃)).mpr
      ⟨W₀ ∪ W₁ ∪ W₂, W₃, (hf₀.union hf₁).union hf₂, hf₃,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hd₀₃, hd₁₃⟩, hd₂₃⟩,
        subset_union_left, subset_union_right, hu₂, hm₃⟩
  -- step 4
  have h₄' : ω ∈ disjointOccurrence
      (disjointOccurrence (disjointOccurrence (disjointOccurrence A₀ A₁) A₂) A₃) A₄ :=
    (mem_disjointOccurrence_iff_open hB₃ h₄ ω).mpr
      ⟨W₀ ∪ W₁ ∪ W₂ ∪ W₃, W₄, ((hf₀.union hf₁).union hf₂).union hf₃, hf₄,
        disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr
          ⟨hd₀₄, hd₁₄⟩, hd₂₄⟩, hd₃₄⟩,
        union_subset (union_subset (union_subset hs₀ hs₁) hs₂) hs₃, hs₄, hu₃, hm₄⟩
  have hlist : List.foldl disjointOccurrence A₀ [A₁, A₂, A₃, A₄]
      = disjointOccurrence (disjointOccurrence (disjointOccurrence
          (disjointOccurrence A₀ A₁) A₂) A₃) A₄ := rfl
  rw [hlist]
  exact h₄'

/-- **Five-fold BK at the native countable law.**  Five increasing cylinder events with five
pairwise disjoint finite open certificates have probability at most the product of their
probabilities, for every profile on a countable coordinate set.  (Two-fold BK
`countable_profile_bk` iterated; the product form is `countable_profile_bk_foldl`.) -/
theorem prodBernoulli_five_wit_le {ι : Type*} [Countable ι] (p : ι → unitInterval)
    {A₀ A₁ A₂ A₃ A₄ : Set (Set ι)}
    (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁) (h₂ : IsUpperSet A₂)
    (h₃ : IsUpperSet A₃) (h₄ : IsUpperSet A₄) :
    prodBernoulli p
      {ω | ∃ W₀ W₁ W₂ W₃ W₄ : Set ι,
            W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧
            W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧
            W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧
            Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
            Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧
            Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₃ W₄}
      ≤ prodBernoulli p A₀ * (prodBernoulli p A₁ *
          (prodBernoulli p A₂ * (prodBernoulli p A₃ * prodBernoulli p A₄))) := by
  have hmono : prodBernoulli p
      {ω | ∃ W₀ W₁ W₂ W₃ W₄ : Set ι,
            W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧
            W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧
            W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ W₃ ∈ A₃ ∧ W₄ ∈ A₄ ∧
            Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
            Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧
            Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₃ W₄} ≤
      prodBernoulli p (List.foldl disjointOccurrence A₀ [A₁, A₂, A₃, A₄]) := by
    refine measure_mono ?_
    rintro ω ⟨W₀, W₁, W₂, W₃, W₄, hf₀, hf₁, hf₂, hf₃, hf₄, hs₀, hs₁, hs₂, hs₃, hs₄,
      hm₀, hm₁, hm₂, hm₃, hm₄, hd₀₁, hd₀₂, hd₀₃, hd₀₄, hd₁₂, hd₁₃, hd₁₄, hd₂₃, hd₂₄, hd₃₄⟩
    exact mem_foldl_disjointOccurrence_of_five (W₀ := W₀) (W₁ := W₁) (W₂ := W₂)
      (W₃ := W₃) (W₄ := W₄) h₀ h₁ h₂ h₃ h₄ hf₀ hf₁ hf₂ hf₃ hf₄
      hs₀ hs₁ hs₂ hs₃ hs₄ hm₀ hm₁ hm₂ hm₃ hm₄
      hd₀₁ hd₀₂ hd₀₃ hd₀₄ hd₁₂ hd₁₃ hd₁₄ hd₂₃ hd₂₄ hd₃₄
  refine hmono.trans ?_
  have hbk := countable_profile_bk_foldl p [A₁, A₂, A₃, A₄]
    (by intro B hB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
        rcases hB with rfl | rfl | rfl | rfl
        exacts [h₁, h₂, h₃, h₄]) h₀
  simpa using hbk



variable {V : Type*}

theorem tsum_two_mul (f g : V → ℝ≥0∞) :
    (∑' y, ∑' z, f y * g z) = (∑' y, f y) * (∑' z, g z) := by
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun _ => ENNReal.tsum_mul_left

theorem tsum_three_mul (f g h : V → ℝ≥0∞) :
    (∑' y, ∑' z, ∑' w, f y * g z * h w)
      = (∑' y, f y) * (∑' z, g z) * (∑' w, h w) := by
  calc (∑' y, ∑' z, ∑' w, f y * g z * h w)
      = ∑' y, ∑' z, (f y * g z) * (∑' w, h w) :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_mul_left
    _ = ∑' y, (∑' z, f y * g z) * (∑' w, h w) :=
        tsum_congr fun _ => ENNReal.tsum_mul_right
    _ = (∑' y, ∑' z, f y * g z) * (∑' w, h w) := ENNReal.tsum_mul_right
    _ = ((∑' y, f y) * (∑' z, g z)) * (∑' w, h w) := by rw [tsum_two_mul]

/-- A constant factors out of a triple extended sum. -/
theorem tsum_const_mul_three (C : ℝ≥0∞) (X : V → V → V → ℝ≥0∞) :
    (∑' y, ∑' z, ∑' w, C * X y z w) = C * ∑' y, ∑' z, ∑' w, X y z w := by
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun _ => by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun _ => ENNReal.tsum_mul_left

theorem tsum_move_last_four (G : V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, G a b c d) = ∑' d, ∑' a, ∑' b, ∑' c, G a b c d := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, G a b c d) = ∑' a, ∑' b, ∑' d, ∑' c, G a b c d :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
    _ = ∑' a, ∑' d, ∑' b, ∑' c, G a b c d := tsum_congr fun _ => ENNReal.tsum_comm
    _ = ∑' d, ∑' a, ∑' b, ∑' c, G a b c d := ENNReal.tsum_comm

/-- Move the last two summation indices of a five-fold extended sum to the front. -/
theorem tsum_permute_three_two (F : V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e)
      = ∑' d, ∑' e, ∑' a, ∑' b, ∑' c, F a b c d e := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e)
      = ∑' a, ∑' b, ∑' c, ∑' e, ∑' d, F a b c d e :=
        tsum_congr fun _ => tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' e, ∑' c, ∑' d, F a b c d e :=
        tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm
    _ = ∑' a, ∑' e, ∑' b, ∑' c, ∑' d, F a b c d e :=
        tsum_congr fun _ => ENNReal.tsum_comm
    _ = ∑' e, ∑' a, ∑' b, ∑' c, ∑' d, F a b c d e := ENNReal.tsum_comm
    _ = ∑' e, ∑' d, ∑' a, ∑' b, ∑' c, F a b c d e :=
        tsum_congr fun e => tsum_move_last_four (fun a b c d => F a b c d e)
    _ = ∑' d, ∑' e, ∑' a, ∑' b, ∑' c, F a b c d e := ENNReal.tsum_comm

theorem tsum_row_eq [AddCommGroup V] (T : V → V → ℝ≥0∞) (o : V)
    (hinv : ∀ a b : V, T a b = T o (b - a)) (a : V) :
    (∑' b, T a b) = ∑' x, T o x := by
  rw [tsum_congr fun b => hinv a b]
  have h := (Equiv.tsum_eq (Equiv.addRight a) (fun x : V => T o (x - a))).symm
  simpa using h

theorem tsum_col_eq [AddCommGroup V] (T : V → V → ℝ≥0∞) (o : V)
    (hsymm : ∀ a b : V, T a b = T b a)
    (hinv : ∀ a b : V, T a b = T o (b - a)) (b : V) :
    (∑' a, T a b) = ∑' x, T o x := by
  rw [tsum_congr fun a => hsymm a b]
  exact tsum_row_eq T o hinv b



variable {V : Type*}

/-- Pulling a constant out and evaluating the double sum over the branch vertices. -/
theorem endgame [AddCommGroup V] [Countable V] (T : V → V → ℝ≥0∞) (o : V)
    (hrow : ∀ a, (∑' b, T a b) = ∑' x, T o x) :
    (∑' u, ∑' v, T o u * T u v * ((∑' x, T o x) * (∑' x, T o x) * (∑' x, T o x)))
      = (∑' x, T o x) ^ 5 := by
  set X : ℝ≥0∞ := ∑' x, T o x with hX
  have hinner : ∀ u : V, (∑' v, T o u * T u v * (X * X * X)) = (T o u * (X * X * X)) * X := by
    intro u
    rw [show (∑' v, T o u * T u v * (X * X * X))
        = ∑' v, (T o u * (X * X * X)) * T u v from
      tsum_congr fun v => by ring]
    rw [ENNReal.tsum_mul_left, hrow u]
  rw [show (∑' u, ∑' v, T o u * T u v * (X * X * X))
      = ∑' u, (T o u * (X * X * X)) * X from tsum_congr fun u => hinner u]
  have hstep : (∑' u : V, (T o u * (X * X * X)) * X)
      = (∑' u : V, T o u * (X * X * X)) * X := ENNReal.tsum_mul_right
  rw [hstep]
  have hstep2 : (∑' u : V, T o u * (X * X * X)) = (∑' u : V, T o u) * (X * X * X) :=
    ENNReal.tsum_mul_right
  rw [hstep2]
  rw [show (∑' u : V, T o u) = X from hrow o]
  ring

/-- **Shape 1.**  `(0,y)` at `u`, `(z,w)` at `v`, spine `u—v`: the sum over the three leaf
variables and the two branch vertices is `χ⁵`.  The terms `u = v` are included and are the
degenerate star trees. -/
theorem shape_one [AddCommGroup V] [Countable V] (T : V → V → ℝ≥0∞) (o : V)
    (hrow : ∀ a, (∑' b, T a b) = ∑' x, T o x)
    (hcol : ∀ b, (∑' a, T a b) = ∑' x, T o x) :
    (∑' y, ∑' z, ∑' w, ∑' u, ∑' v, T o u * T u v * (T u y * T z v * T v w))
      = (∑' x, T o x) ^ 5 := by
  have h3 : ∀ u v : V, (∑' y, ∑' z, ∑' w, T u y * T z v * T v w)
      = (∑' x, T o x) * (∑' x, T o x) * (∑' x, T o x) := by
    intro u v
    rw [tsum_three_mul, hrow u, hcol v, hrow v]
  rw [tsum_permute_three_two (F := fun a b c d e => T o d * T d e * (T d a * T b e * T e c))]
  refine (tsum_congr fun u => tsum_congr fun v => ?_).trans (endgame T o hrow)
  rw [tsum_const_mul_three, h3 u v]

/-- **Shape 2.**  `(0,z)` at `u`, `(y,w)` at `v`, spine `u—v`. -/
theorem shape_two [AddCommGroup V] [Countable V] (T : V → V → ℝ≥0∞) (o : V)
    (hrow : ∀ a, (∑' b, T a b) = ∑' x, T o x)
    (hcol : ∀ b, (∑' a, T a b) = ∑' x, T o x) :
    (∑' y, ∑' z, ∑' w, ∑' u, ∑' v, T o u * T u v * (T u z * T y v * T v w))
      = (∑' x, T o x) ^ 5 := by
  have h3 : ∀ u v : V, (∑' y, ∑' z, ∑' w, T u z * T y v * T v w)
      = (∑' x, T o x) * (∑' x, T o x) * (∑' x, T o x) := by
    intro u v
    rw [show (∑' y, ∑' z, ∑' w, T u z * T y v * T v w)
        = ∑' y, ∑' z, ∑' w, (fun y => T y v) y * (fun z => T u z) z * T v w from
      tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => by ring]
    rw [tsum_three_mul, hcol v, hrow u, hrow v]
  rw [tsum_permute_three_two (F := fun a b c d e => T o d * T d e * (T d b * T a e * T e c))]
  refine (tsum_congr fun u => tsum_congr fun v => ?_).trans (endgame T o hrow)
  rw [tsum_const_mul_three, h3 u v]

/-- **Shape 3.**  `(0,w)` at `u`, `(y,z)` at `v`, spine `u—v`. -/
theorem shape_three [AddCommGroup V] [Countable V] (T : V → V → ℝ≥0∞) (o : V)
    (hrow : ∀ a, (∑' b, T a b) = ∑' x, T o x)
    (hcol : ∀ b, (∑' a, T a b) = ∑' x, T o x) :
    (∑' y, ∑' z, ∑' w, ∑' u, ∑' v, T o u * T u v * (T u w * T y v * T v z))
      = (∑' x, T o x) ^ 5 := by
  have h3 : ∀ u v : V, (∑' y, ∑' z, ∑' w, T u w * T y v * T v z)
      = (∑' x, T o x) * (∑' x, T o x) * (∑' x, T o x) := by
    intro u v
    rw [show (∑' y, ∑' z, ∑' w, T u w * T y v * T v z)
        = ∑' y, ∑' z, ∑' w, (fun y => T y v) y * (fun z => T v z) z * T u w from
      tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => by ring]
    rw [tsum_three_mul, hcol v, hrow v, hrow u]
  rw [tsum_permute_three_two (F := fun a b c d e => T o d * T d e * (T d c * T a e * T e b))]
  refine (tsum_congr fun u => tsum_congr fun v => ?_).trans (endgame T o hrow)
  rw [tsum_const_mul_three, h3 u v]



variable {V : Type*}

/-- A product of three indicator functions is the indicator of the triple intersection. -/
theorem indicator_mul_three {α : Type*} (s t u : Set α) :
    ((s.indicator (fun _ => (1 : ℝ≥0∞))) * (t.indicator (fun _ => (1 : ℝ≥0∞)))
        * u.indicator (fun _ => (1 : ℝ≥0∞)))
      = (s ∩ t ∩ u).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext a
  simp only [Pi.mul_apply]
  by_cases h1 : a ∈ s <;> by_cases h2 : a ∈ t <;> by_cases h3 : a ∈ u <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2, h3]

/-- **The indicator expansion of `E|K_0|³`.**  `|K_x|³ = ∑_{y,z,w} 1{y,z,w ∈ K_x}`, so by
Tonelli the third moment is the triple sum of the three-point joint connection probabilities.
No finiteness and no summability hypothesis: everything is in `ℝ≥0∞`. -/
theorem lintegral_cardFun_cube_eq [Countable V] (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 3 ∂(law π)
      = ∑' y, ∑' z, ∑' w, law π (conn x y ∩ conn x z ∩ conn x w) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : V → Config V → ℝ≥0∞,
      ∀ (y : V) (ω : Config V),
        f y ω = (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    ⟨fun y ω => (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω, fun _ _ => rfl⟩
  have hfm : ∀ y, Measurable (f y) := by
    intro y
    rw [show f y = fun ω => (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω from funext (hf y)]
    exact measurable_const.indicator (measurableSet_conn x y)
  have hcard : ∀ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω x) = ∑' y, f y ω := by
    intro ω
    rw [PercLib.CriticalLRP.Percolation.cardFun_eq_encard, encard_cluster_eq_tsum]
    exact tsum_congr fun y => (hf y ω).symm
  have hcube : ∀ ω, (∑' y, f y ω) ^ 3 = ∑' y, ∑' z, ∑' w, f y ω * f z ω * f w ω := by
    intro ω
    rw [tsum_three_mul (f := fun y => f y ω) (g := fun z => f z ω) (h := fun w => f w ω)]
    ring
  have hjoint : ∀ y z w : V,
      ∫⁻ ω, f y ω * f z ω * f w ω ∂(law π) = law π (conn x y ∩ conn x z ∩ conn x w) := by
    intro y z w
    have hfun : (fun ω => f y ω * f z ω * f w ω)
        = ((conn x y).indicator (fun _ => (1 : ℝ≥0∞))
            * (conn x z).indicator (fun _ => (1 : ℝ≥0∞))
            * (conn x w).indicator (fun _ => (1 : ℝ≥0∞))) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [hf y ω, hf z ω, hf w ω]
    rw [hfun, indicator_mul_three]
    exact lintegral_indicator_one
      ((measurableSet_conn x y).inter (measurableSet_conn x z) |>.inter
        (measurableSet_conn x w))
  calc ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ 3 ∂(law π)
      = ∫⁻ ω, ∑' y, ∑' z, ∑' w, f y ω * f z ω * f w ω ∂(law π) := by
        refine lintegral_congr fun ω => ?_
        rw [hcard ω, hcube ω]
    _ = ∑' y, ∫⁻ ω, ∑' z, ∑' w, f y ω * f z ω * f w ω ∂(law π) := by
        refine lintegral_tsum fun y => ?_
        exact (Measurable.tsum fun z => Measurable.tsum fun w =>
          (hfm y).mul (hfm z) |>.mul (hfm w)).aemeasurable
    _ = ∑' y, ∑' z, ∫⁻ ω, ∑' w, f y ω * f z ω * f w ω ∂(law π) := by
        refine tsum_congr fun y => lintegral_tsum fun z => ?_
        exact (Measurable.tsum fun w => (hfm y).mul (hfm z) |>.mul (hfm w)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, ∫⁻ ω, f y ω * f z ω * f w ω ∂(law π) := by
        refine tsum_congr fun y => tsum_congr fun z => lintegral_tsum fun w => ?_
        exact ((hfm y).mul (hfm z) |>.mul (hfm w)).aemeasurable
    _ = ∑' y, ∑' z, ∑' w, law π (conn x y ∩ conn x z ∩ conn x w) := by
        exact tsum_congr fun y => tsum_congr fun z => tsum_congr fun w => hjoint y z w



variable {V : Type*}

theorem walkEdges_finite [Countable V] {ω : Config V} {a b : V}
    (p : (openGraph ω).Walk a b) : (walkEdges p).Finite := by
  classical
  have h : walkEdges p = (↑p.edges.toFinset : Set (Sym2 V)) := by
    ext e; simp [walkEdges]
  rw [h]
  exact Finset.finite_toSet _

theorem walkEdges_subset [Countable V] {ω : Config V} {a b : V}
    (p : (openGraph ω).Walk a b) : walkEdges p ⊆ ω := by
  intro e he
  exact PercLib.CriticalLRP.edgeSet_openGraph_subset
    (SimpleGraph.Walk.edges_subset_edgeSet p he)

theorem mem_conn_walkEdges [Countable V] {ω : Config V} {a b : V}
    (p : (openGraph ω).Walk a b) : walkEdges p ∈ conn a b := by
  obtain ⟨q, hq⟩ := PercLib.CriticalLRP.exists_walk_top_of_walk p
  show PercLib.CriticalLRP.Connects (walkEdges p) a b
  rw [← PercLib.CriticalLRP.pathConnects_iff]
  exact ⟨q, fun e he => by rw [hq] at he; exact he⟩

theorem disjoint_walkEdges [Countable V] {ω : Config V} {a b c d : V}
    (p : (openGraph ω).Walk a b) (q : (openGraph ω).Walk c d)
    (h : p.edges.Disjoint q.edges) : Disjoint (walkEdges p) (walkEdges q) :=
  Set.disjoint_left.mpr fun _e he he' => h he he'

/-- Five pairwise edge-disjoint walks of one binary shape produce the five disjoint finite
certificates of `ShapeEvent`. -/
theorem shapeEvent_mem [Countable V] {ω : Config V} {root a b c u v : V}
    (h : ShapeWitness (openGraph ω) root a b c u v) :
    ω ∈ ShapeEvent (V := V) root a b c u v := by
  obtain ⟨p, q, s, t, r, hpq, hps, hpt, hpr, hqs, hqt, hqr, hst, hsr, htr⟩ := h
  exact ⟨walkEdges p, walkEdges q, walkEdges s, walkEdges t, walkEdges r,
    walkEdges_finite p, walkEdges_finite q, walkEdges_finite s,
    walkEdges_finite t, walkEdges_finite r,
    walkEdges_subset p, walkEdges_subset q, walkEdges_subset s,
    walkEdges_subset t, walkEdges_subset r,
    mem_conn_walkEdges p, mem_conn_walkEdges q, mem_conn_walkEdges s,
    mem_conn_walkEdges t, mem_conn_walkEdges r,
    disjoint_walkEdges p q hpq, disjoint_walkEdges p s hps,
    disjoint_walkEdges p t hpt, disjoint_walkEdges p r hpr,
    disjoint_walkEdges q s hqs, disjoint_walkEdges q t hqt,
    disjoint_walkEdges q r hqr, disjoint_walkEdges s t hst,
    disjoint_walkEdges s r hsr, disjoint_walkEdges t r htr⟩

/-! ### The measure bound for one shape -/

/-- **Union bound plus five-fold BK for one tree shape.**  The union over all branch pairs
`(u,v)` of the shape event has measure at most the sum of the five two-point factors. -/
theorem shapeEvent_le [Countable V] (π : Sym2 V → unitInterval) (root a b c : V) :
    law π (⋃ uv : V × V, ShapeEvent (V := V) root a b c uv.1 uv.2)
      ≤ ∑' uv : V × V, tau π root uv.1 * tau π uv.1 uv.2 *
          (tau π uv.1 a * tau π b uv.2 * tau π uv.2 c) := by
  have hterm : ∀ uv : V × V, law π (ShapeEvent (V := V) root a b c uv.1 uv.2)
      ≤ tau π root uv.1 *
          (tau π a uv.1 * (tau π b uv.2 * (tau π c uv.2 * tau π uv.1 uv.2))) := by
    intro uv
    exact prodBernoulli_five_wit_le (p := π) (A₀ := conn root uv.1)
      (A₁ := conn a uv.1) (A₂ := conn b uv.2) (A₃ := conn c uv.2) (A₄ := conn uv.1 uv.2)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
  refine ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hterm)).trans (le_of_eq ?_)
  exact tsum_congr fun uv => by
    rw [tau_comm π a uv.1, tau_comm π c uv.2]
    ring

/-! ### The four-point tree-graph inequality from the arm decomposition -/

/-- **The four-point tree-graph inequality (I.2.2) at `k = 3`, from the deterministic binary-arm
decomposition.**  The hypothesis says: whenever `0, y, z, w` lie in one open component, one of the
three labelled binary trees on the four leaves is realised by five pairwise edge-disjoint walks in
the open graph.  (For the H-shaped tree only the middle shape is available, so the disjunction is
genuinely needed.)  Everything else is proved here. -/
theorem four_point_of_arm_decomposition [Countable V] (π : Sym2 V → unitInterval)
    (root y z w : V)
    (harm : ∀ (ω : Config V), PercLib.CriticalLRP.Connects ω root y → PercLib.CriticalLRP.Connects ω root z →
        PercLib.CriticalLRP.Connects ω root w →
      (∃ u v, ShapeWitness (openGraph ω) root y z w u v) ∨
      (∃ u v, ShapeWitness (openGraph ω) root z y w u v) ∨
      (∃ u v, ShapeWitness (openGraph ω) root w y z u v)) :
    law π (conn root y ∩ conn root z ∩ conn root w)
      ≤ ∑' u, ∑' v,
          (tau π root u * tau π u v * (tau π u y * tau π z v * tau π v w)
            + tau π root u * tau π u v * (tau π u z * tau π y v * tau π v w)
            + tau π root u * tau π u v * (tau π u w * tau π y v * tau π v z)) := by
  have hcover : (conn root y ∩ conn root z ∩ conn root w) ⊆
      ((⋃ uv : V × V, ShapeEvent (V := V) root y z w uv.1 uv.2)
        ∪ (⋃ uv : V × V, ShapeEvent (V := V) root z y w uv.1 uv.2))
        ∪ (⋃ uv : V × V, ShapeEvent (V := V) root w y z uv.1 uv.2) := by
    rintro ω ⟨⟨h0y, h0z⟩, h0w⟩
    rcases harm ω h0y h0z h0w with ⟨u, v, hw⟩ | ⟨u, v, hw⟩ | ⟨u, v, hw⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨(u, v), shapeEvent_mem hw⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨(u, v), shapeEvent_mem hw⟩))
    · exact Or.inr (Set.mem_iUnion.mpr ⟨(u, v), shapeEvent_mem hw⟩)
  have hsplit : ∀ A B C : V → V → ℝ≥0∞,
      (∑' u, ∑' v, (A u v + B u v + C u v))
        = (∑' u, ∑' v, A u v) + (∑' u, ∑' v, B u v) + (∑' u, ∑' v, C u v) := by
    intro A B C
    simp only [ENNReal.tsum_add]
  have h₁ := shapeEvent_le (V := V) π root y z w
  have h₂ := shapeEvent_le (V := V) π root z y w
  have h₃ := shapeEvent_le (V := V) π root w y z
  calc law π (conn root y ∩ conn root z ∩ conn root w)
      ≤ law π (((⋃ uv : V × V, ShapeEvent (V := V) root y z w uv.1 uv.2)
          ∪ (⋃ uv : V × V, ShapeEvent (V := V) root z y w uv.1 uv.2))
          ∪ (⋃ uv : V × V, ShapeEvent (V := V) root w y z uv.1 uv.2)) :=
        measure_mono hcover
    _ ≤ law π ((⋃ uv : V × V, ShapeEvent (V := V) root y z w uv.1 uv.2)
          ∪ (⋃ uv : V × V, ShapeEvent (V := V) root z y w uv.1 uv.2))
          + law π (⋃ uv : V × V, ShapeEvent (V := V) root w y z uv.1 uv.2) :=
        measure_union_le _ _
    _ ≤ (law π (⋃ uv : V × V, ShapeEvent (V := V) root y z w uv.1 uv.2)
          + law π (⋃ uv : V × V, ShapeEvent (V := V) root z y w uv.1 uv.2))
          + law π (⋃ uv : V × V, ShapeEvent (V := V) root w y z uv.1 uv.2) :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ∑' u, ∑' v,
          (tau π root u * tau π u v * (tau π u y * tau π z v * tau π v w)
            + tau π root u * tau π u v * (tau π u z * tau π y v * tau π v w)
            + tau π root u * tau π u v * (tau π u w * tau π y v * tau π v z)) := by
        rw [hsplit]
        rw [← ENNReal.tsum_prod (f := fun u v =>
              tau π root u * tau π u v * (tau π u y * tau π z v * tau π v w)),
            ← ENNReal.tsum_prod (f := fun u v =>
              tau π root u * tau π u v * (tau π u z * tau π y v * tau π v w)),
            ← ENNReal.tsum_prod (f := fun u v =>
              tau π root u * tau π u v * (tau π u w * tau π y v * tau π v z))]
        exact add_le_add (add_le_add h₁ h₂) h₃



variable {V : Type*}

/-- **The infinite-native third cluster moment from the four-point tree-graph inequality.**

Let `τ x y = P(x↔y)` be the two-point function of Bernoulli bond percolation with edge law
`law π` on a countable abelian group `V`, with `τ` translation invariant
(`hinv : τ a b = τ 0 (b-a)`, the paper's "transitivity").  Assume the pointwise four-point
tree-graph inequality, i.e. (I.2.2) of the paper at `k = 3`:

`P(0↔y, 0↔z, 0↔w) ≤ ∑_{u,v} [ τ(0,u)τ(u,v) ( τ(u,y)τ(z,v)τ(v,w)
                                    + τ(u,z)τ(y,v)τ(v,w)
                                    + τ(u,w)τ(y,v)τ(v,z) ) ]`,

the three terms being the three isomorphism classes of labelled binary trees on the four leaves
`0,y,z,w` (each read as a product of two-point probabilities along the tree, summed over the two
unlabelled degree-3 vertices `u,v`).  Then

`E|K_0|³ ≤ 3 (E|K_0|)⁵`.

The multiplicity `3` is exactly the number of such trees; the degenerate `u = v` terms are the
star trees.  No finiteness hypothesis on `E|K_0|` is needed (`ℝ≥0∞` throughout); the conclusion
is then trivial at `E|K_0| = ∞` and sharp in the mean-finite regime. -/
theorem third_moment_le_of_four_point [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a))
    (hfour : ∀ y z w : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w)
        ≤ ∑' u, ∑' v,
            (tau π 0 u * tau π u v * (tau π u y * tau π z v * tau π v w)
              + tau π 0 u * tau π u v * (tau π u z * tau π y v * tau π v w)
              + tau π 0 u * tau π u v * (tau π u w * tau π y v * tau π v z))) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)) ^ 3 ∂(law π)
      ≤ 3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π)) ^ 5 := by
  have hsymm : ∀ a b : V, tau π a b = tau π b a := fun a b => tau_comm π a b
  have hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x :=
    fun a => tsum_row_eq (tau π) 0 hinv a
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x :=
    fun b => tsum_col_eq (tau π) 0 hsymm hinv b
  have hmean : (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π))
      = ∑' x, tau π 0 x := by
    rw [show (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π))
        = ∫⁻ ω, ((cluster ω 0).encard : ℝ≥0∞) ∂(law π) from by
      refine lintegral_congr fun ω => ?_
      exact PercLib.CriticalLRP.Percolation.cardFun_eq_encard _]
    exact chi_eq_tsum_tau π 0
  rw [lintegral_cardFun_cube_eq π 0, hmean]
  calc ∑' y, ∑' z, ∑' w, law π (conn 0 y ∩ conn 0 z ∩ conn 0 w)
      ≤ ∑' y, ∑' z, ∑' w, ∑' u, ∑' v,
          (tau π 0 u * tau π u v * (tau π u y * tau π z v * tau π v w)
            + tau π 0 u * tau π u v * (tau π u z * tau π y v * tau π v w)
            + tau π 0 u * tau π u v * (tau π u w * tau π y v * tau π v z)) :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
          ENNReal.tsum_le_tsum fun w => hfour y z w
    _ = 3 * (∑' x, tau π 0 x) ^ 5 := by
        simp only [ENNReal.tsum_add]
        rw [shape_one (tau π) 0 hrow hcol, shape_two (tau π) 0 hrow hcol,
          shape_three (tau π) 0 hrow hcol]
        ring



variable {V : Type*}

/-- **`E|K_0|³ ≤ 3 (E|K_0|)⁵` from the deterministic binary-arm decomposition alone.**

This is the composition of `third_moment_le_of_four_point` with
`four_point_of_arm_decomposition`.  The only hypothesis beyond translation invariance of the
two-point function is the purely deterministic statement that in every configuration the three
connections `0↔y`, `0↔z`, `0↔w` exhibit one of the three labelled binary trees on the four leaves
as five pairwise edge-disjoint walks of the open graph. -/
theorem third_moment_le_of_arm_decomposition [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a))
    (harm : ∀ (y z w : V) (ω : Config V),
      PercLib.CriticalLRP.Connects ω 0 y → PercLib.CriticalLRP.Connects ω 0 z →
      PercLib.CriticalLRP.Connects ω 0 w →
      (∃ u v, ShapeWitness (openGraph ω) 0 y z w u v) ∨
      (∃ u v, ShapeWitness (openGraph ω) 0 z y w u v) ∨
      (∃ u v, ShapeWitness (openGraph ω) 0 w y z u v)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)) ^ 3 ∂(law π)
      ≤ 3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π)) ^ 5 :=
  third_moment_le_of_four_point π hinv
    fun y z w => four_point_of_arm_decomposition π 0 y z w (harm y z w)


end PercLib.CriticalLRP.TreeExpansion
