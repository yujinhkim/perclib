/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m1.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m1/Obstruction.lean`.
-/

/-
Ultramath `smwzqts7r`, member `m1`, direction `d2`.

# The `p = 6`, `k = 2` two-hub cover is false in general

Production proves (`Correlation/SixPoint/MixedK2/Counterexample/Cycle6/Main.lean`) that the
`p = 5`, `k = 2` two-hub pointwise cover `hpoint` of
`fifth_moment_mixed_k2_le_of_hubBound` fails for the translation-invariant step profile on
`ZMod 6` at `θ = 1/64`.  This file proves the `p = 6` analogue: the cover

  `law π (⋂_{x ∈ {y,z,w,q,r,s}} conn 0 x) ≤ ∑' t : Fin 945, slotK2Six π (pat t) 0 ![y,z,w,q,r,s]`

of `HubK2.SixCover` fails at the degenerate tuple `(0,3,3,3,3,3)` for every family of `945`
leaf labellings, once `θ < 1/130` (we use `θ = 1/256`).

Mechanism: on `ZMod 6` with the step profile, `0 ↔ 3` holds as soon as the three unit edges
`0—1—2—3` are open, so the left side is at least `θ³`; but every two-hub slot diagram needs
six two-point factors whose exponent sum is at least `6` (each hub has two leaves, one root
link and one residual leaf), so the right side is at most `945 · 36 · 64 · θ⁶`.  For
`θ = 1/256` we have `2177280 · θ⁶ < θ³`.

Consequently the `p = 6` two-hub slot family cannot discharge `HubK2.SixCover`: the honest
cover of Lemma I.4.16 has to be the full `945`-tree union bound with the degenerate
(collapsed) configurations handled by the tree structure itself, not by the two-hub collapse.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Main
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Cycle6.Main

/-! A six-cycle refutation of the collapsed two-hub event-cover construction. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.Counterexample.Cycle6
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.HubK2

namespace PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample

variable {V : Type*}

/-! ## General-parameter versions of the step-profile bounds

The counterexample infrastructure of production is stated at the fixed `θ = 1/64`; the `p = 6`
two-hub diagram needs the smaller `θ = 1/256`, so we redo the two-point bound at a general `θ`
from the (already general) cylinder estimate `law_subset_of_step`. -/

/-- Cylinder probability of a forward arc at a general parameter. -/
theorem law_fwdArc_gen (θ : unitInterval) (x : ZMod 6) {k : ℕ} (hk : k ≤ 6) :
    law (stepProfile θ) {ω : Config (ZMod 6) | (fwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω}
      = (unitInterval.toNNReal θ : ℝ≥0∞) ^ k := by
  rw [law_subset_of_step (θ := θ) (F := fwdArc x k) ?_, card_fwdArc x hk]
  · intro e he
    obtain ⟨t, -, rfl⟩ := mem_fwdArc_iff.1 he
    exact eAt_mem_stepSet x t

/-- Cylinder probability of a backward arc at a general parameter. -/
theorem law_bwdArc_gen (θ : unitInterval) (x : ZMod 6) {k : ℕ} (hk : k ≤ 6) :
    law (stepProfile θ) {ω : Config (ZMod 6) | (bwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω}
      = (unitInterval.toNNReal θ : ℝ≥0∞) ^ (6 - k) := by
  rw [law_subset_of_step (θ := θ) (F := bwdArc x k) ?_, card_bwdArc x hk]
  · intro e he
    obtain ⟨i, -, rfl⟩ := mem_bwdArc_iff.1 he
    exact eAt_mem_stepSet x _

/-- The two-point bound at a general parameter. -/
theorem law_conn_le_gen (θ : unitInterval) {x y : ZMod 6} (hxy : x ≠ y) :
    law (stepProfile θ) (conn x y) ≤
      (unitInterval.toNNReal θ : ℝ≥0∞) ^ (y - x).val
        + (unitInterval.toNNReal θ : ℝ≥0∞) ^ (6 - (y - x).val) := by
  have hk6 : (y - x).val ≤ 6 := le_of_lt (ZMod.val_lt _)
  set k := (y - x).val with hkdef
  have hk6' : k ≤ 6 := by rw [hkdef]; exact hk6
  set A : Set (Config (ZMod 6)) := {ω | (fwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω} with hA
  set B : Set (Config (ZMod 6)) := {ω | (bwdArc x k : Set (Sym2 (ZMod 6))) ⊆ ω} with hB
  set C : Set (Config (ZMod 6)) := ⋃ (e : {e : Sym2 (ZMod 6) // e ∉ stepSet}),
    {ω : Config (ZMod 6) | (e.1 : Sym2 (ZMod 6)) ∈ ω} with hC
  have hsub : conn x y ⊆ A ∪ (B ∪ C) := by
    have h := conn_subset_arcs hxy hkdef.symm
    simpa [A, B, C] using h
  calc law (stepProfile θ) (conn x y)
      ≤ law (stepProfile θ) (A ∪ (B ∪ C)) := measure_mono hsub
    _ = law (stepProfile θ) ((A ∪ B) ∪ C) := by rw [Set.union_assoc]
    _ ≤ law (stepProfile θ) (A ∪ B) + law (stepProfile θ) C := measure_union_le _ _
    _ ≤ (law (stepProfile θ) A + law (stepProfile θ) B) + law (stepProfile θ) C :=
        add_le_add (measure_union_le A B) (le_refl _)
    _ = (unitInterval.toNNReal θ : ℝ≥0∞) ^ k
          + (unitInterval.toNNReal θ : ℝ≥0∞) ^ (6 - k) := by
        rw [show law (stepProfile θ) A = (unitInterval.toNNReal θ : ℝ≥0∞) ^ k from by
              rw [hA]; exact law_fwdArc_gen θ x hk6',
            show law (stepProfile θ) B = (unitInterval.toNNReal θ : ℝ≥0∞) ^ (6 - k) from by
              rw [hB]; exact law_bwdArc_gen θ x hk6',
            show law (stepProfile θ) C = 0 from by rw [hC]; exact law_not_step θ,
            add_zero]
    _ = (unitInterval.toNNReal θ : ℝ≥0∞) ^ (y - x).val
          + (unitInterval.toNNReal θ : ℝ≥0∞) ^ (6 - (y - x).val) := by rw [hkdef]

/-- The two-point function of the step profile at a general parameter. -/
theorem tau_le_gen (θ : unitInterval) (hθ : unitInterval.toNNReal θ ≤ 1) (x y : ZMod 6) :
    tau (stepProfile θ) x y ≤ 2 * (unitInterval.toNNReal θ : ℝ≥0∞) ^ cdist x y := by
  by_cases hxy : x = y
  · subst hxy
    rw [tau, conn_self, measure_univ, cdist_self, pow_zero, mul_one]
    norm_num
  · have h := law_conn_le_gen θ hxy
    have h1 : (unitInterval.toNNReal θ : ℝ≥0∞) ^ (y - x).val
        ≤ (unitInterval.toNNReal θ : ℝ≥0∞) ^ cdist x y := by
      refine pow_le_pow_right_of_le_one' ?_ ?_
      · simpa using hθ
      · rw [cdist]; exact min_le_left _ _
    have h2 : (unitInterval.toNNReal θ : ℝ≥0∞) ^ (6 - (y - x).val)
        ≤ (unitInterval.toNNReal θ : ℝ≥0∞) ^ cdist x y := by
      refine pow_le_pow_right_of_le_one' ?_ ?_
      · simpa using hθ
      · rw [cdist]; exact min_le_right _ _
    calc tau (stepProfile θ) x y
        = law (stepProfile θ) (conn x y) := rfl
      _ ≤ _ + _ := h
      _ ≤ _ + _ := add_le_add h1 h2
      _ = 2 * (unitInterval.toNNReal θ : ℝ≥0∞) ^ cdist x y := by rw [two_mul]

/-- A joint connection probability is dominated by one of its two arms. -/
theorem jointP_le_gen (θ : unitInterval) (hθ : unitInterval.toNNReal θ ≤ 1) (a b c : ZMod 6) :
    jointP (stepProfile θ) a b c
      ≤ 2 * (unitInterval.toNNReal θ : ℝ≥0∞) ^ max (cdist a c) (cdist b c) := by
  rcases le_total (cdist a c) (cdist b c) with h | h
  · rw [Nat.max_eq_right h]
    refine (measure_mono (s := conn a c ∩ conn b c) (t := conn b c)
      Set.inter_subset_right).trans (tau_le_gen θ hθ b c)
  · rw [Nat.max_eq_left h]
    refine (measure_mono (s := conn a c ∩ conn b c) (t := conn a c)
      Set.inter_subset_left).trans (tau_le_gen θ hθ a c)

/-- The six-factor bound: a two-hub slot diagram at fixed hubs is at most
`2 ^ 6 θ ^ (exponent sum)`. -/
theorem hubStarSix_le_gen (θ : unitInterval) (hθ : unitInterval.toNNReal θ ≤ 1)
    {a b d e f g c1 c2 : ZMod 6}
    (hE : 6 ≤ max (cdist a c1) (cdist b c1) + cdist 0 c1
      + max (cdist d c2) (cdist e c2) + cdist 0 c2 + cdist f c1 + cdist g c2) :
    hubStarSix (stepProfile θ) (0 : ZMod 6) a b d e f g c1 c2
      ≤ 64 * (unitInterval.toNNReal θ : ℝ≥0∞) ^ 6 := by
  set ee : ℝ≥0∞ := (unitInterval.toNNReal θ : ℝ≥0∞) with hee
  have hpow : ee ^ (max (cdist a c1) (cdist b c1) + cdist 0 c1
      + max (cdist d c2) (cdist e c2) + cdist 0 c2 + cdist f c1 + cdist g c2)
      ≤ ee ^ 6 := by
    refine pow_le_pow_right_of_le_one' ?_ hE
    rw [hee]; simpa using hθ
  have h1 : jointP (stepProfile θ) a b c1 ≤ 2 * ee ^ max (cdist a c1) (cdist b c1) :=
    jointP_le_gen θ hθ a b c1
  have h2 : tau (stepProfile θ) 0 c1 ≤ 2 * ee ^ cdist 0 c1 := tau_le_gen θ hθ 0 c1
  have h3 : jointP (stepProfile θ) d e c2 ≤ 2 * ee ^ max (cdist d c2) (cdist e c2) :=
    jointP_le_gen θ hθ d e c2
  have h4 : tau (stepProfile θ) 0 c2 ≤ 2 * ee ^ cdist 0 c2 := tau_le_gen θ hθ 0 c2
  have h5 : tau (stepProfile θ) f c1 ≤ 2 * ee ^ cdist f c1 := tau_le_gen θ hθ f c1
  have h6 : tau (stepProfile θ) g c2 ≤ 2 * ee ^ cdist g c2 := tau_le_gen θ hθ g c2
  calc hubStarSix (stepProfile θ) (0 : ZMod 6) a b d e f g c1 c2
      ≤ ((2 * ee ^ max (cdist a c1) (cdist b c1) * (2 * ee ^ cdist 0 c1)) *
          (2 * ee ^ max (cdist d c2) (cdist e c2) * (2 * ee ^ cdist 0 c2))) *
          (2 * ee ^ cdist f c1 * (2 * ee ^ cdist g c2)) := by
        unfold hubStarSix
        gcongr
    _ = 64 * ee ^ (max (cdist a c1) (cdist b c1) + cdist 0 c1
          + max (cdist d c2) (cdist e c2) + cdist 0 c2 + cdist f c1 + cdist g c2) := by
        rw [pow_add, pow_add, pow_add, pow_add, pow_add]
        ring
    _ ≤ 64 * ee ^ 6 := mul_le_mul' le_rfl hpow

end PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample

namespace PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample

open PercLib.CriticalLRP.Counterexample.Cycle6
open PercLib.CriticalLRP.TreeExpansion.HubK2

/-! ## The little-`θ` instance `θ = 1/256` -/

/-- The opening probability `1/256`. -/
def theta256 : unitInterval := ⟨1 / 256, by norm_num⟩

theorem toNNReal_theta256 : unitInterval.toNNReal theta256 = 1 / 256 := rfl

theorem theta256_le_one : unitInterval.toNNReal theta256 ≤ 1 := by
  rw [toNNReal_theta256, ← NNReal.coe_le_coe]
  push_cast
  norm_num

/-- The degenerate leaf vector `(0, 3, 3, 3, 3, 3)`. -/
def leaves6 : Fin 6 → ZMod 6 := ![0, 3, 3, 3, 3, 3]

theorem leaves6_eq (i : Fin 6) : leaves6 i = if i = 0 then (0 : ZMod 6) else 3 := by
  fin_cases i <;> rfl

/-- The leaf vector with the single `0` in slot `i`. -/
def L0 (i : Fin 6) : Fin 6 → ZMod 6 := fun j => if j = i then 0 else 3

/-! ## The exponent count

Each hub carries a joint pair of leaves, a link to the root and one residual leaf.  Whatever slot
carries the unique `0`, the exponent sum of the six two-point factors is at least `6`:
`cdist 0 c + cdist 3 c = 3` on the six-cycle. -/
theorem exp_ite (i : Fin 6) (c1 c2 : ZMod 6) :
    6 ≤ max (cdist (L0 i 0) c1) (cdist (L0 i 1) c1) + cdist 0 c1
      + max (cdist (L0 i 2) c2) (cdist (L0 i 3) c2) + cdist 0 c2
      + cdist (L0 i 4) c1 + cdist (L0 i 5) c2 := by
  have k1 := cdist_zero_three c1
  have k2 := cdist_zero_three c2
  fin_cases i <;>
    simp only [L0, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceEq, ↓reduceIte] <;>
    omega

/-! ## The slot bound at `θ = 1/256` -/

/-- **Every two-hub slot at the degenerate tuple is at most `36 · 64 · θ⁶`.** -/
theorem slotK2Six_le256 (σ : Equiv.Perm (Fin 6)) :
    slotK2Six (stepProfile theta256) σ (0 : ZMod 6) leaves6
      ≤ 36 * (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6) := by
  obtain ⟨i, hi⟩ := σ.surjective 0
  have hL : ∀ j : Fin 6, leaves6 (σ j) = L0 i j := by
    intro j
    rw [leaves6_eq, L0]
    by_cases hj : j = i
    · rw [hj, hi]; simp
    · have hne : σ j ≠ 0 := fun hh => hj (σ.injective (by rw [hh, hi]))
      rw [ite_neg_eq hne, ite_neg_eq hj]
  simp only [slotK2Six]
  rw [hL 0, hL 1, hL 2, hL 3, hL 4, hL 5]
  calc ∑' c1 : ZMod 6, ∑' c2 : ZMod 6,
        hubStarSix (stepProfile theta256) (0 : ZMod 6)
          (L0 i 0) (L0 i 1) (L0 i 2) (L0 i 3) (L0 i 4) (L0 i 5) c1 c2
      ≤ ∑' _c1 : ZMod 6, ∑' _c2 : ZMod 6, (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6) :=
        ENNReal.tsum_le_tsum fun c1 => ENNReal.tsum_le_tsum fun c2 => by
          simpa only [toNNReal_theta256] using
            hubStarSix_le_gen theta256 theta256_le_one (exp_ite i c1 c2)
    _ = 36 * (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6) := by
        rw [tsum_congr (fun c1 => tsum_zmod6_const _), tsum_zmod6_const]
        ring

/-! ## The numerical comparison -/

theorem num_lt_nn :
    (945 : ℝ≥0) * (36 * (64 * (1 / 256 : ℝ≥0) ^ 6)) < (1 / 256 : ℝ≥0) ^ 3 := by
  rw [← NNReal.coe_lt_coe]
  push_cast
  norm_num

theorem num_lt :
    (945 : ℝ≥0∞) * (36 * (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6))
      < ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 3 := by
  have hthis : ((945 : ℝ≥0) * (36 * (64 * ((1 / 256 : ℝ≥0)) ^ 6)) : ℝ≥0∞)
      < (((1 / 256 : ℝ≥0) ^ 3 : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.2 num_lt_nn
  calc (945 : ℝ≥0∞) * (36 * (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6))
      = ((945 : ℝ≥0) * (36 * (64 * (1 / 256 : ℝ≥0) ^ 6)) : ℝ≥0∞) := by push_cast; ring
    _ < (((1 / 256 : ℝ≥0) ^ 3 : ℝ≥0) : ℝ≥0∞) := hthis
    _ = ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 3 := by push_cast; ring

/-! ## The refutation -/

theorem sixConnSet_degenerate :
    sixConnSet (0 : ZMod 6) 0 3 3 3 3 3 = conn (0 : ZMod 6) 3 := by
  unfold sixConnSet
  rw [conn_self, Set.univ_inter, Set.inter_self, Set.inter_self, Set.inter_self,
    Set.inter_self]

/-- The three unit edges `0—1—2—3` force `0 ↔ 3`. -/
theorem eps_cube_le_law_conn_three256 :
    ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 3 ≤ law (stepProfile theta256) (conn (0 : ZMod 6) 3) := by
  have hcyl : law (stepProfile theta256)
      {ω : Config (ZMod 6) | (fwdArc (0 : ZMod 6) 3 : Set (Sym2 (ZMod 6))) ⊆ ω}
      = ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 3 := by
    rw [law_fwdArc_gen theta256 0 (by norm_num : 3 ≤ 6), toNNReal_theta256]
  rw [← hcyl]
  refine measure_mono ?_
  intro ω hω
  rw [mem_conn_iff]
  have := subset_fwdArc_imp_reach (x := (0 : ZMod 6)) (k := 3) hω
  simpa [vtx] using this

/-- **The `p = 6`, `k = 2` two-hub cover fails at the step profile with `θ = 1/256`.**

For every family of `945` leaf labellings, the pointwise bound of `HubK2.SixCover` is violated
at the degenerate tuple `(0, 3, 3, 3, 3, 3)`. -/
theorem sixCover_false256 (pat : Fin 945 → Equiv.Perm (Fin 6)) :
    ¬ SixCover (stepProfile theta256) (0 : ZMod 6) pat := by
  intro h
  have hlow : ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 3
      ≤ law (stepProfile theta256) (sixConnSet (0 : ZMod 6) 0 3 3 3 3 3) := by
    rw [sixConnSet_degenerate]
    exact eps_cube_le_law_conn_three256
  have hcover := h 0 3 3 3 3 3
  have hhigh : (∑' t : Fin 945,
      slotK2Six (stepProfile theta256) (pat t) (0 : ZMod 6) ![0, 3, 3, 3, 3, 3])
      ≤ (945 : ℝ≥0∞) * (36 * (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6)) := by
    have hstep : (∑' t : Fin 945,
        slotK2Six (stepProfile theta256) (pat t) (0 : ZMod 6) ![0, 3, 3, 3, 3, 3])
        ≤ ∑' _t : Fin 945, (36 * (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6)) :=
      ENNReal.tsum_le_tsum fun t => slotK2Six_le256 (pat t)
    simpa only [tsum_fin945_const] using hstep
  have hchain : ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 3
      ≤ (945 : ℝ≥0∞) * (36 * (64 * ((1 / 256 : ℝ≥0) : ℝ≥0∞) ^ 6)) :=
    hlow.trans (hcover.trans hhigh)
  exact absurd hchain (not_le.2 num_lt)

end PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample
