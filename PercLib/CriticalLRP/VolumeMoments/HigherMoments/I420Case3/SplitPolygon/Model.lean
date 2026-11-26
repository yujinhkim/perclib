/- Integrated from `.scratch/case3-split-draft/Model.lean` at production base
`727647257a78a7d38f1feca20bb09fd18b284bdb`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Main

/-! # A near/far averaged threefold bound for the genuine cutoff powers -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- The real threefold sum over a finite window, split into a near set and a far
complement. No decay of the diagonal threefold entry is assumed. -/
theorem sum_polyK_three_le_near_far (M : SourceModelData) (r R : ℝ)
    (B s : Finset M.V)
    (hfar : ∀ y ∈ B, y ∉ s → R ≤ M.S.dist 0 y)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    (∑ y ∈ B, I418C.polyK (M.cutTwoPoint r) 3 0 y) ≤
      (B.card : ℝ) * (M.nablaTail R).toReal + (s.card : ℝ) * M.triSelf := by
  classical
  obtain ⟨hB2, hB3, hlink⟩ := M.hB2_hB3_hlink_derived hTri
  have hmono : ∀ y : M.V, I418C.polyK (M.cutTwoPoint r) 3 0 y ≤ M.triPoint 0 y := by
    intro y
    exact (I418C.polyK_three_mono (fun _ _ => M.cutTwoPoint_nonneg r _ _)
      (fun x y => M.cutTwoPoint_le_twoPoint r x y) hB2 hB3 y).trans (hlink y)
  have hnn : 0 ≤ M.triSelf := by
    have h := hmono (0 : M.V)
    have h0 : 0 ≤ I418C.polyK (M.cutTwoPoint r) 3 0 0 := by
      exact I418C.polyK_nonneg _ (fun _ _ => M.cutTwoPoint_nonneg r _ _) 3 0 0
    exact h0.trans (h.trans (M.triPoint_le_self hTri 0))
  have hpoint : ∀ y ∈ B, I418C.polyK (M.cutTwoPoint r) 3 0 y ≤
      (M.nablaTail R).toReal + if y ∈ s then M.triSelf else 0 := by
    intro y hyB
    by_cases hys : y ∈ s
    · rw [ite_eq_left hys]
      exact (hmono y).trans ((M.triPoint_le_self hTri y).trans (by
        exact le_add_of_nonneg_left (M.nablaTail_toReal_nonneg R)))
    · rw [ite_eq_right hys, add_zero]
      exact (hmono y).trans (M.triPoint_le_nablaTail (r := R) hTri (hfar y hyB hys))
  have hfil : B.filter (· ∈ s) ⊆ s := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  calc (∑ y ∈ B, I418C.polyK (M.cutTwoPoint r) 3 0 y)
      ≤ ∑ y ∈ B, ((M.nablaTail R).toReal + if y ∈ s then M.triSelf else 0) :=
        Finset.sum_le_sum hpoint
    _ = (B.card : ℝ) * (M.nablaTail R).toReal +
          ∑ y ∈ B, if y ∈ s then M.triSelf else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ = (B.card : ℝ) * (M.nablaTail R).toReal +
          ((B.filter (· ∈ s)).card : ℝ) * M.triSelf := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B.card : ℝ) * (M.nablaTail R).toReal + (s.card : ℝ) * M.triSelf := by
        have hc : ((B.filter (· ∈ s)).card : ℝ) ≤ (s.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hfil
        exact add_le_add_right (mul_le_mul_of_nonneg_right hc hnn) _

/-- The same near/far bound in the exact averaged form required by
`HasSplitPolygonBound.three`. -/
theorem cutPoly_three_sum_le_near_far (M : SourceModelData) (r R : ℝ)
    (B s : Finset M.V) (hcard : 0 < B.card)
    (hfar : ∀ y ∈ B, y ∉ s → R ≤ M.S.dist 0 y)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    ∑ y ∈ B, cutPoly M r y 3 ≤ (B.card : ℝ≥0∞) *
      ENNReal.ofReal ((M.nablaTail R).toReal +
        ((s.card : ℝ) / (B.card : ℝ)) * M.triSelf) := by
  classical
  have hreal := sum_polyK_three_le_near_far M r R B s hfar hTri
  have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
  have hhr : (∑ y ∈ B, I418C.polyK (M.cutTwoPoint r) 3 0 y) ≤
      (B.card : ℝ) * ((M.nablaTail R).toReal +
        ((s.card : ℝ) / (B.card : ℝ)) * M.triSelf) := by
    calc (∑ y ∈ B, I418C.polyK (M.cutTwoPoint r) 3 0 y)
        ≤ (B.card : ℝ) * (M.nablaTail R).toReal + (s.card : ℝ) * M.triSelf := hreal
      _ = (B.card : ℝ) * ((M.nablaTail R).toReal +
          ((s.card : ℝ) / (B.card : ℝ)) * M.triSelf) := by
        field_simp
  change (∑ y ∈ B, ENNReal.ofReal (I418C.polyK (M.cutTwoPoint r) 3 0 y)) ≤ _
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · calc ENNReal.ofReal (∑ y ∈ B, I418C.polyK (M.cutTwoPoint r) 3 0 y)
        ≤ ENNReal.ofReal ((B.card : ℝ) * ((M.nablaTail R).toReal +
          ((s.card : ℝ) / (B.card : ℝ)) * M.triSelf)) := ENNReal.ofReal_le_ofReal hhr
      _ = (B.card : ℝ≥0∞) * ENNReal.ofReal ((M.nablaTail R).toReal +
          ((s.card : ℝ) / (B.card : ℝ)) * M.triSelf) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  · intro y _
    exact cutPoly_nonneg M r y 3

/-- A genuine split-polygon bound for the cutoff matrix powers. Its threefold
factor is a near/cardinality term plus the open-triangle tail; its higher-depth
factor is the existing Lemma-I.4.18 tail rate. -/
theorem exists_hasSplitPolygonBound_cutPoly_near_far (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {p : ℕ}, 1 ≤ p → ∀ {r R : ℝ}, 1 ≤ r →
      ∀ (B s : Finset M.V), 0 < B.card →
      (∀ y ∈ B, y ∉ s → R ≤ M.S.dist 0 y) →
        HasSplitPolygonBound (M.cutProb r) 0 B p (cutPoly M r)
          ((M.nablaTail R).toReal + ((s.card : ℝ) / (B.card : ℝ)) * M.triSelf)
          (C * ((M.nablaTail (r ^ c)).toReal + r ^ (-c))) := by
  obtain ⟨c, C, hc, hC, hb⟩ := CutPoly.cutPoly_le_rate M hP hTri
  refine ⟨c, C, hc, hC, ?_⟩
  intro p _hp r R hr B s hcard hfar
  have hthree_nonneg : 0 ≤ (M.nablaTail R).toReal +
      ((s.card : ℝ) / (B.card : ℝ)) * M.triSelf :=
    add_nonneg (M.nablaTail_toReal_nonneg R)
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
  refine ⟨hthree_nonneg, by positivity,
    cutPoly_three_sum_le_near_far M r R B s hcard hfar hTri, ?_⟩
  intro y hy j hj
  have h4 : 4 ≤ j := (Finset.mem_Icc.mp hj).1
  exact hb h4 hr y

/-- Convergence of the near/far threefold factor is exactly reduced to the
triangle-tail limit and the near-ball/window cardinality ratio. -/
theorem tendsto_near_far_factor (M : SourceModelData) (B s : ℝ → Finset M.V) (R : ℝ → ℝ)
    (hTail : Tendsto (fun r => (M.nablaTail (R r)).toReal) atTop (𝓝 0))
    (hCard : Tendsto (fun r => ((s r).card : ℝ) / ((B r).card : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun r => (M.nablaTail (R r)).toReal +
      (((s r).card : ℝ) / ((B r).card : ℝ)) * M.triSelf) atTop (𝓝 0) := by
  have hmul : Tendsto (fun r => (((s r).card : ℝ) / ((B r).card : ℝ)) * M.triSelf)
      atTop (𝓝 0) := by
    simpa using hCard.mul_const M.triSelf
  simpa using hTail.add hmul

end I420Case3

end PercLib.CriticalLRP
