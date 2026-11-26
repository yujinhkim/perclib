/-
Swarm `smwxh86dl`, member `m3`, direction `d3` (`MOMENT-ARITHMETIC-CLOSURE`).

The `p = 5`, `k = 2` shape-mass assembly: Lemma I.4.16 at `p = 5` and the largest admissible
`k = ⌈(p-1)/2⌉ = 2`, i.e.

  `E|K|^5 ≤ 105 * (E|K|^2)^2 * (E|K|)^3`.

What is proved here, on the genuine `SixShape` event and the standard `ℝ≥0∞` codomain:

* `fifth_moment_le_sum_shapeTotal` — **unconditional at production HEAD**: the fifth moment is
  bounded by the sum of the `105 = 15 * 7` shape masses, with the four internal witnesses
  summed inside the measure of each shape event, exactly as `sixPoint_le_sixShapeChunk`
  produces them.  No pointwise diagram premise, no independence, no finiteness.
* `fifth_moment_k2_le_of_shapeTotal` — from one mass bound per shape, the native inequality.
* `shapeTotal_mid_le` — the fifteen middle-split (`j = 2`) masses are **proved** to be at most
  `(E|K|²)²(E|K|)³` by the production evaluation `SixPoint.TwoJointEval.Assembly`, so they
  never need to appear as a hypothesis again.
* `fifth_moment_k2_le_of_offmid` — hence only the six off-middle splits `j ≠ 2` are open.

This replaces the `hpoint` premise of the existing `k = 2` consumer
(`MixedK2.Assembly.fifth_moment_le_of_hubDiagrams`) by the *proved* deterministic cover.  The
remaining input is the mass of the `90` off-middle shape events, nothing else.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.Defs

/-!
# The fifth-moment reduction with middle-split masses discharged

The final `k = 2` bound remains conditional on off-middle shape masses or
on the not-yet-proved root-class collapse.
-/


open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

variable {V : Type*}

/-- **The fifth moment is bounded by the `105` shape masses** (unconditional).  The first step
is the exact joint-probability expansion `lintegral_cardFun_five_eq`; the second is the
deterministic six-terminal cover `sixPoint_le_sixShapeChunk`, regrouped so that the four
internal witnesses `c, u, v, w` stay inside the measure of each shape event; the last is the
interchange of the five terminal sums with the `15 × 7` shape index.

No diagram is evaluated here, and no hypothesis is used. -/
theorem fifth_moment_le_sum_shapeTotal [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      ∑' k : Fin 15, ∑' j : Fin 7, shapeTotal π 0 k j := by
  rw [lintegral_cardFun_five_eq π 0]
  calc ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r)
      ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' k : Fin 15, ∑' j : Fin 7,
          shapeMass π 0 k j y z w q r := by
        refine ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
          ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
            ENNReal.tsum_le_tsum fun r => ?_
        rw [← iInter_six_conn y z w q r]
        simpa only [shapeMass, shapeVec] using
          sixPoint_le_sixShapeChunk (V := V) π ![0, y, z, w, q, r]
    _ = ∑' p : Fin 15 × Fin 7, shapeTotal π 0 p.1 p.2 :=
        tsum_five_fin15_fin7_swap (fun y z w q r k j => shapeMass π 0 k j y z w q r)
    _ = ∑' k : Fin 15, ∑' j : Fin 7, shapeTotal π 0 k j :=
        (tsum_fin15_fin7 (fun k j => shapeTotal π 0 k j)).symm

/-- **The `k = 2` moment bound from one mass bound per shape.**  If every one of the `105`
shape masses is at most `(E|K|²)²(E|K|)³`, then the native fifth-moment inequality of
Lemma I.4.16 at `p = 5`, `k = 2` holds.  No pointwise diagram, no independence. -/
theorem fifth_moment_k2_le_of_shapeTotal [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hS : ∀ (k : Fin 15) (j : Fin 7), shapeTotal π 0 k j ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
        105 * secondMoment π 0 ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    calc ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
            (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π)
        ≤ ∑' k : Fin 15, ∑' j : Fin 7, shapeTotal π 0 k j :=
          fifth_moment_le_sum_shapeTotal π
      _ ≤ ∑' _k : Fin 15, ∑' _j : Fin 7, shapeCost π 0 :=
          ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => hS k j
      _ = 15 * (7 * shapeCost π 0) := by
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]
      _ = 105 * shapeCost π 0 := by ring
      _ = 105 * secondMoment π 0 ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
          rw [shapeCost]; ring
  simpa only [secondMoment, ← firstMoment_eq, firstMoment] using hmain

/-- **The fifteen middle-split masses are bounded by the production evaluation.**  For the
split at comb arm `2`, `SixPoint.TwoJointEval.Assembly` evaluates all fifteen labelled
patterns to `(E|K|²)²(E|K|)³` under profile invariance, so no hypothesis is needed at `j = 2`.

The proof is a `Fin 15` case split over those fifteen theorems; nothing is re-derived. -/
theorem shapeTotal_mid_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∀ k : Fin 15, shapeTotal π 0 k 2 ≤ shapeCost π 0 := by
  intro k
  fin_cases k
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat0 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat1 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat2 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat3 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat4 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat5 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_id π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat7 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat8 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat9 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat10 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat11 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat12 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat13 π hq
  · simp only [shapeTotal, shapeMass, shapeVec, shapeCost]
    exact PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat14 π hq

/-- **The `k = 2` moment bound from the six off-middle splits only.**  The middle split
`j = 2` is discharged by `shapeTotal_mid_le`; the surviving hypothesis names exactly the `90`
shape masses that production does not evaluate at HEAD. -/
theorem fifth_moment_k2_le_of_offmid [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (hoff : ∀ (k : Fin 15) (j : Fin 7), j ≠ 2 → shapeTotal π 0 k j ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine fifth_moment_k2_le_of_shapeTotal π fun k j => ?_
  by_cases hj : j = 2
  · subst hj
    exact shapeTotal_mid_le π hq k
  · exact hoff k j hj

/-! ## The two root classes of the fifteen labelled patterns

`SixPoint.pat_root_slot` says the root `T 0` sits in comb slot `0` or comb slot `2` in every
pattern.  The counts below are the machine-checked accounting of how the `105 = 15 * 7` shapes
split: `12 * 7` with the root in slot `0` and `3 * 7` with the root in slot `2`.  Only the two
root slots matter for the *mass* (the five non-root terminals are summed over all of `V`), so
`105` shape bounds reduce to the `14` masses of the two root classes at each of the seven
splits — a reduction whose last step, the reindexing of the four free terminal sums, is *not*
formalised here. -/

/-- Twelve of the fifteen labelled patterns place the root in comb slot `0`. -/
theorem card_pat_root_zero :
    (Finset.univ.filter (fun k : Fin 15 =>
      PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0)).card = 12 := by
  decide

/-- Three of the fifteen labelled patterns place the root in comb slot `2`. -/
theorem card_pat_root_two :
    (Finset.univ.filter (fun k : Fin 15 =>
      PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0)).card = 3 := by
  decide

/-- The two root classes partition the fifteen patterns. -/
theorem card_pat_root_sum :
    (Finset.univ.filter (fun k : Fin 15 =>
        PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0 = 0)).card +
      (Finset.univ.filter (fun k : Fin 15 =>
        PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2 = 0)).card = 15 := by
  rw [card_pat_root_zero, card_pat_root_two]

/-- The `105 = 15 * 7` shape indices split `12 * 7 + 3 * 7` between the two root classes. -/
theorem shape_index_split : 12 * 7 + 3 * 7 = (105 : ℕ) := by norm_num

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.card_pat_root_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.fifth_moment_le_sum_shapeTotal
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.fifth_moment_k2_le_of_shapeTotal
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal_mid_le
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.fifth_moment_k2_le_of_offmid

/-! ## The root-class reduction: what the residual really is

The five non-root terminals of a shape are summed over all of `V`, so the *mass* of a shape
depends on the pattern `k` only through the comb slot that holds the root: permuting the four
free labels is a reindexing of four independent sums over `V`.  Hence the `105 = 15 * 7` mass
bounds collapse onto at most `14` masses `(root slot, split)`.

The collapse itself is a reindexing of the four free terminal sums by the permutation relating
the two patterns' leaf assignments; it is isolated below as the hypothesis `hcollapse` and is
**not** formalised in this file (the fifteen leaf assignments are the entries of
`FivePoint.pat`, and the reindexing needs `Equiv.tsum_eq` on `Fin 4 → V`).  Everything else —
the cover, the moment expansion, the middle-split discharge, and the `105` arithmetic — is
proved. -/

theorem patSlot0_root : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat patSlot0 0 = 0 := by
  decide

theorem patSlot2_root : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat patSlot2 2 = 0 := by
  decide

/-- **The `k = 2` moment bound from the twelve off-middle root-class masses.**  The hypotheses
are: one mass bound per root class at each off-middle split (twelve masses), plus the collapse
of the fifteen labelled patterns onto their root classes.  The middle split `j = 2` is
discharged internally by `shapeTotal_mid_le`. -/
theorem fifth_moment_k2_le_of_rootClass_bounds [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (h0 : ∀ j : Fin 7, j ≠ 2 → shapeTotal π 0 patSlot0 j ≤ shapeCost π 0)
    (h2 : ∀ j : Fin 7, j ≠ 2 → shapeTotal π 0 patSlot2 j ≤ shapeCost π 0)
    (hcollapse : ∀ (k : Fin 15) (j : Fin 7),
      shapeTotal π 0 k j ≤
        max (shapeTotal π 0 patSlot0 j) (shapeTotal π 0 patSlot2 j)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine fifth_moment_k2_le_of_shapeTotal π fun k j => ?_
  by_cases hj : j = 2
  · subst hj
    exact shapeTotal_mid_le π hq k
  · refine (hcollapse k j).trans (max_le ?_ ?_)
    · exact h0 j hj
    · exact h2 j hj

set_option linter.hashCommand false

#print axioms fifth_moment_k2_le_of_rootClass_bounds

end PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass
