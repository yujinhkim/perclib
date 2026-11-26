/-
Theorems for direction `FREE-ARM-PROFILE-ASSEMBLY` (swarm `smwxh86dl`, member `m2`).
Proofs only; every definition is in `Defs.lean`, the axiom audit is `Check.lean`.

# What this file proves

* `iterPow_le_chi_pow` — a chain of `m ≥ 1` legs is at most `χ ^ m` (row sums only, no symmetry).
* `tsum_histFibre_markDepth_symm` — the reviewed branch value of `smwxfstjy/m1` in the kernel
  orientation `T ^ ℓ (w,y)` of the printed normal form (symmetry of `τ`, nothing else).
* `histFibre_le_branchVal` — **the arm target is not summed**: the fibre of one branch with the
  selected arm pinned at an arbitrary `ga` (production's `genShape` pins it to `g j`) is still at
  most the printed monomial.
* `card_depthFiber`, `sum_markDepthK_mul` — the finite grouping of the branches by their
  pin--mark depth, with production's coefficient `genCoeff`.
* `tsum_histFibre_le_genProfileSum` — the sum over all branches of the fibre, bounded by the
  coefficient-weighted polynomial.
* `tsum_histW_eq_tsum_histFibre` — the fibre decomposition of the unrestricted history sum.
* `tsum_pinned_le_tsum` — the pinned-arm sub-family is a sub-sum of the unrestricted one, so
  dropping the pinning only enlarges the sum (the direction that an upper bound needs).
* `tsum_histW_le_genProfileSum`, `tsum_pinned_histW_le_genProfileSum` — the two history sums.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Profile.Defs

/-!
# Assembly of the actual pinned-history cover into `genFreshProfile`

Uses the real split-choice/fibre decomposition; the bound is not a general marked-moment theorem.
-/


open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshProfile

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## 1. One chain of at least one leg contributes at most `χ ^ m` -/

/-- **A chain of `m ≥ 1` legs is at most `χ ^ m`.**  Only the constant *row* sum of the kernel is
used: the chain evaluated at a fixed far endpoint is one term of the sum over the far endpoint,
which `tsum_iterPow_chain` evaluates as `χ ^ m`.  No symmetry and no further hypothesis. -/
theorem iterPow_le_chi_pow {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) {m : ℕ} (hm : 1 ≤ m) (a b : V) :
    I417Base.iterPow τ m a b ≤ χ ^ m := by
  refine (ENNReal.le_tsum (f := fun c => I417Base.iterPow τ m a c) b).trans ?_
  rw [I417HistToSpine.tsum_iterPow_chain hχ m hm a]

/-! ## 2. The branch value in the orientation of the printed normal form -/

/-- **The reviewed branch value, transposed.**  `smwxfstjy/m1`'s `tsum_histFibre_markDepth`
evaluates the free arm target with the kernel power in the orientation `T ^ ℓ (y,w)`; the printed
normal form (and `GenFreshEval`/`genFreshProfile`) uses `T ^ ℓ (w,y)`.  Symmetry of the kernel is
exactly what identifies them (`I417Base.iterPow_comm`), and it is the only extra input. -/
theorem tsum_histFibre_markDepth_symm {n : ℕ} {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (hτ : ∀ a b : V, τ a b = τ b a)
    (k : (t : Fin n) → I417GenIter.Idx t) (y w : V) :
    (∑' ga : V, I417HistToSpine.histFibre (fun _ => τ) y w k ga) =
      χ ^ (2 * (n + 1) - I417FreshDepth.markDepthK n k) *
        I417Base.iterPow τ (I417FreshDepth.markDepthK n k) w y := by
  rw [I417HistFibre.tsum_histFibre_markDepth τ χ hχ k y w]
  exact congrArg (fun z => χ ^ (2 * (n + 1) - I417FreshDepth.markDepthK n k) * z)
    (I417Base.iterPow_comm τ hτ (I417FreshDepth.markDepthK n k) y w)

/-- **The pinned arm target costs nothing.**  The fibre of one branch, with the selected arm's
target held fixed at an arbitrary vertex `ga`, is still at most the printed monomial
`χ ^ (2(n+1) - ℓ) · T ^ ℓ (w,y)`: the pinned value is one term of the sum over the arm target,
which `tsum_histFibre_markDepth_symm` evaluates.  This replaces the per-slot arm accounting that
the fibre package left open. -/
theorem histFibre_le_branchVal {n : ℕ} {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (hτ : ∀ a b : V, τ a b = τ b a)
    (k : (t : Fin n) → I417GenIter.Idx t) (y w ga : V) :
    I417HistToSpine.histFibre (fun _ => τ) y w k ga ≤ branchVal τ χ n k w y := by
  refine (ENNReal.le_tsum
    (f := fun ga' => I417HistToSpine.histFibre (fun _ => τ) y w k ga') ga).trans ?_
  rw [tsum_histFibre_markDepth_symm hχ hτ k y w]
  rfl

/-- The same bound with the monomial written out. -/
theorem histFibre_le_profileTerm {n : ℕ} {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (hτ : ∀ a b : V, τ a b = τ b a)
    (k : (t : Fin n) → I417GenIter.Idx t) (y w ga : V) :
    I417HistToSpine.histFibre (fun _ => τ) y w k ga ≤
      χ ^ (2 * (n + 1) - I417FreshDepth.markDepthK n k) *
        I417Base.iterPow τ (I417FreshDepth.markDepthK n k) w y :=
  histFibre_le_branchVal hχ hτ k y w ga

/-! ## 3. The depth fibres and the coefficients -/

/-- The pin--mark depth of a branch lies in the printed range `1 ≤ ℓ ≤ n + 1`. -/
theorem mem_Icc_markDepthK {n : ℕ} (k : (t : Fin n) → I417GenIter.Idx t) :
    I417FreshDepth.markDepthK n k ∈ Finset.Icc 1 (n + 1) :=
  Finset.mem_Icc.mpr ⟨I417FreshDepth.markDepthK_pos k, I417FreshDepth.markDepthK_le k⟩

/-- **The cardinality of a depth fibre is production's coefficient `C_ℓ`.** -/
theorem card_depthFiber (n ℓ : ℕ) :
    (depthFiber n ℓ).card = I417FreshDepth.depthCount n ℓ := by
  rw [I417FreshDepth.depthCount]
  exact (Fintype.card_ofFinset (p := {k : ((t : Fin n) → I417GenIter.Idx t) |
      I417FreshDepth.markDepthK n k = ℓ}) (depthFiber n ℓ) (fun k => by simp [depthFiber])).symm

/-- **Grouping the branches by their pin--mark depth.**  A finite sum over the split-choice
tuples of a function of `markDepthK` alone is the coefficient-weighted sum over the depths
`1, …, n + 1`. -/
theorem sum_markDepthK_mul (n : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑ k : (t : Fin n) → I417GenIter.Idx t, f (I417FreshDepth.markDepthK n k)) =
      ∑ ℓ ∈ Finset.Icc 1 (n + 1), (depthFiber n ℓ).card * f ℓ := by
  classical
  have hmaps : ∀ k ∈ (Finset.univ : Finset ((t : Fin n) → I417GenIter.Idx t)),
      I417FreshDepth.markDepthK n k ∈ Finset.Icc 1 (n + 1) :=
    fun k _ => mem_Icc_markDepthK k
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun k => f (I417FreshDepth.markDepthK n k))]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hterm : ∀ k ∈ Finset.univ.filter
      (fun i : (t : Fin n) → I417GenIter.Idx t => I417FreshDepth.markDepthK n i = ℓ),
      f (I417FreshDepth.markDepthK n k) = f ℓ := by
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- **The coefficient fibres add up to the branch count.**  Summing the coefficients of the
printed normal form over the depths gives exactly the number of split-choice tuples of the cover,
`2 ^ n * n !` (`I417GenIter.card_histChoices_eq`): no branch is lost and none is counted twice in
the grouping `sum_markDepthK_mul`. -/
theorem sum_depthCount_eq_card (n : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 (n + 1), I417FreshDepth.depthCount n ℓ =
      Fintype.card ((t : Fin n) → I417GenIter.Idx t) := by
  have h := sum_markDepthK_mul n (fun _ => (1 : ℝ≥0∞))
  rw [Finset.sum_congr rfl (fun ℓ (_ : ℓ ∈ Finset.Icc 1 (n + 1)) => by
    rw [card_depthFiber, mul_one])] at h
  have h2 : (∑ ℓ ∈ Finset.Icc 1 (n + 1),
      ((I417FreshDepth.depthCount n ℓ : ℕ) : ℝ≥0∞)) =
      ((Fintype.card ((t : Fin n) → I417GenIter.Idx t) : ℕ) : ℝ≥0∞) := by
    rw [← h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  refine Nat.cast_injective (R := ℝ≥0∞) ?_
  push_cast
  exact h2

/-! ## 4. The sum over all branches -/

/-- **The unrestricted arm sum over all branches is bounded by the printed polynomial.** -/
theorem tsum_histFibre_le_genProfileSum {n : ℕ} {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (hτ : ∀ a b : V, τ a b = τ b a) (y w ga : V) :
    (∑' k : (t : Fin n) → I417GenIter.Idx t,
        I417HistToSpine.histFibre (fun _ => τ) y w k ga) ≤ genProfileSum τ χ n w y := by
  have h1 : (∑ k : (t : Fin n) → I417GenIter.Idx t, branchVal τ χ n k w y) =
      ∑ ℓ ∈ Finset.Icc 1 (n + 1), (depthFiber n ℓ).card *
        (χ ^ (2 * (n + 1) - ℓ) * I417Base.iterPow τ ℓ w y) := by
    rw [← sum_markDepthK_mul n
      (fun ℓ => χ ^ (2 * (n + 1) - ℓ) * I417Base.iterPow τ ℓ w y)]
    rfl
  have h2 : (∑ ℓ ∈ Finset.Icc 1 (n + 1), (depthFiber n ℓ).card *
        (χ ^ (2 * (n + 1) - ℓ) * I417Base.iterPow τ ℓ w y)) =
      ∑ ℓ ∈ Finset.Icc 1 (n + 1), (I417FreshDepth.depthCount n ℓ : ℝ≥0∞) *
        (χ ^ (2 * (n + 1) - ℓ) * I417Base.iterPow τ ℓ w y) := by
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [card_depthFiber]
  refine (ENNReal.tsum_le_tsum fun k => histFibre_le_branchVal hχ hτ k y w ga).trans ?_
  rw [tsum_fintype, genProfileSum, h1, h2]

/-! ## 5. The fibre decomposition of the unrestricted history sum -/

/-- **The unrestricted history sum is the sum of the branch fibres.**  The split-choice map
partitions the attachment histories, and `histFibre` is the fibre sum over one class. -/
theorem tsum_histW_eq_tsum_histFibre {n : ℕ}
    (W : (i : I417GenIter.Idx n) → V → V → ℝ≥0∞) (y w ga : V) :
    (∑' H : I417GenIter.Hist V n, I417HistToSpine.histW W H y w ga) =
      ∑' k : (t : Fin n) → I417GenIter.Idx t,
        I417HistToSpine.histFibre W y w k ga := by
  classical
  have hsplit : ∀ H : I417GenIter.Hist V n,
      I417HistToSpine.histW W H y w ga =
        ∑' k : (t : Fin n) → I417GenIter.Idx t,
          if I417FreshDepth.splitChoices H = k then
            I417HistToSpine.histW W H y w ga else 0 := by
    intro H
    rw [tsum_eq_single (I417FreshDepth.splitChoices H)]
    · simp
    · intro k hk
      simp [Ne.symm hk]
  have hfib : ∀ k : (t : Fin n) → I417GenIter.Idx t,
      (∑' H : I417GenIter.Hist V n,
        if I417FreshDepth.splitChoices H = k then
          I417HistToSpine.histW W H y w ga else 0) =
        ∑' H : {H : I417GenIter.Hist V n // I417FreshDepth.splitChoices H = k},
          I417HistToSpine.histW W H.1 y w ga := by
    intro k
    have h1 : (∑' H : {H : I417GenIter.Hist V n // I417FreshDepth.splitChoices H = k},
        I417HistToSpine.histW W H.1 y w ga) =
        ∑' H : I417GenIter.Hist V n,
          {H : I417GenIter.Hist V n | I417FreshDepth.splitChoices H = k}.indicator
            (fun H => I417HistToSpine.histW W H y w ga) H :=
      tsum_subtype {H : I417GenIter.Hist V n | I417FreshDepth.splitChoices H = k}
        (fun H => I417HistToSpine.histW W H y w ga)
    rw [h1]
    refine tsum_congr fun H => ?_
    by_cases hk : I417FreshDepth.splitChoices H = k
    · simp [Set.indicator_apply, hk]
    · simp [Set.indicator_apply, hk]
  calc (∑' H : I417GenIter.Hist V n, I417HistToSpine.histW W H y w ga)
      = ∑' H : I417GenIter.Hist V n, ∑' k : (t : Fin n) → I417GenIter.Idx t,
          if I417FreshDepth.splitChoices H = k then
            I417HistToSpine.histW W H y w ga else 0 := tsum_congr hsplit
    _ = ∑' k : (t : Fin n) → I417GenIter.Idx t, ∑' H : I417GenIter.Hist V n,
          if I417FreshDepth.splitChoices H = k then
            I417HistToSpine.histW W H y w ga else 0 := ENNReal.tsum_comm
    _ = ∑' k : (t : Fin n) → I417GenIter.Idx t,
          I417HistToSpine.histFibre W y w k ga := tsum_congr hfib

/-! ## 6. Pinning the arms is a sub-sum of the unrestricted sum -/

/-- **The pinned-arm sub-family is a sub-sum.**  For any predicate `p` on histories the sum over
the histories satisfying `p` is at most the unrestricted sum.  Applied to production's
`pinnedArm` this is the step that turns `genShape`'s pinned history sum into the unrestricted
one, in the direction that an upper bound needs. -/
theorem tsum_pinned_le_tsum {n : ℕ} (W : (i : I417GenIter.Idx n) → V → V → ℝ≥0∞)
    (p : I417GenIter.Hist V n → Prop) (y w ga : V) :
    (∑' H : {H : I417GenIter.Hist V n // p H}, I417HistToSpine.histW W H.1 y w ga) ≤
      ∑' H : I417GenIter.Hist V n, I417HistToSpine.histW W H y w ga := by
  classical
  have h1 : (∑' H : {H : I417GenIter.Hist V n // p H},
      I417HistToSpine.histW W H.1 y w ga) =
      ∑' H : I417GenIter.Hist V n,
        {H : I417GenIter.Hist V n | p H}.indicator
          (fun H => I417HistToSpine.histW W H y w ga) H :=
    tsum_subtype {H : I417GenIter.Hist V n | p H}
      (fun H => I417HistToSpine.histW W H y w ga)
  rw [h1]
  refine ENNReal.tsum_le_tsum fun H => ?_
  by_cases hp : p H
  · simp [Set.indicator_apply, hp]
  · simp [Set.indicator_apply, hp]

/-- **The unrestricted history sum is bounded by the printed polynomial.** -/
theorem tsum_histW_le_genProfileSum {n : ℕ} {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (hτ : ∀ a b : V, τ a b = τ b a) (y w ga : V) :
    (∑' H : I417GenIter.Hist V n,
        I417HistToSpine.histW (fun _ => τ) H y w ga) ≤ genProfileSum τ χ n w y :=
  (le_of_eq (tsum_histW_eq_tsum_histFibre (fun _ => τ) y w ga)).trans
    (tsum_histFibre_le_genProfileSum hχ hτ y w ga)

/-- **The pinned-arm history sum is bounded by the printed polynomial**, with no hypothesis on
the pinning data beyond `p` being a predicate on histories. -/
theorem tsum_pinned_histW_le_genProfileSum {n : ℕ} {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (hτ : ∀ a b : V, τ a b = τ b a)
    (p : I417GenIter.Hist V n → Prop) (y w ga : V) :
    (∑' H : {H : I417GenIter.Hist V n // p H},
        I417HistToSpine.histW (fun _ => τ) H.1 y w ga) ≤ genProfileSum τ χ n w y :=
  (tsum_pinned_le_tsum (fun _ => τ) p y w ga).trans
    (tsum_histW_le_genProfileSum hχ hτ y w ga)

end PercLib.CriticalLRP.I417FreshProfile
