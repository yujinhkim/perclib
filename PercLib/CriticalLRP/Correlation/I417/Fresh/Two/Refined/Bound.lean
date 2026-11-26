/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m1` artifact
`.ultramath/smwx5p94b/m1/M1Fresh`. Production integration revision:
`9c345df8dcb6d4027a2e61d7a7785abf4df111cf`. The coordinator assigns the production
namespace and fully qualified imports; the mathematical statements are unchanged.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Refined.Cover

/-!
# The `q = 2` fresh-copy factor, evaluated

For a fixed arm label `j : Fin 2` and the other label `j'`, the four-edge cover of
`PercLib.CriticalLRP.I417FreshTwo.Refined.exists_refined_branch` gives, for each arm tuple `g`,

  `P(freshMark y g j w) ≤ ∑_p [ τ(y,p)τ(p,w)τ(w,g j)τ(p,g j') + τ(y,w)τ(w,p)τ(p,g j)τ(p,g j') ]`,

and summing the two labelled arms out (with the constant row sum `χ`) evaluates the two families
to `χ²·T²(w,y)` and `χ³·T(w,y)`.  Both carry exactly **four** two-point factors, so the fresh side
of Lemma I.4.17 at `q = 2` has the printed `2q = 4` edges rather than the five of the
`hubStar`/three-terminal reading `χ³T² + 2χ²T³`.

This file is the analytic half: `tsum_freshMark_le_refined` is the bound
`F(y,w) ≤ freshTwoRefined π χ y w`.  It uses only `π e < 1` (BK) and the constant row sum.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo.Refined

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## Summing the two labelled arms out -/

/-- The two labelled arms sum independently, in either order. -/
theorem tsum_fin2_mul_swap (f k : V → ℝ≥0∞) :
    (∑' g : Fin 2 → V, f (g 1) * k (g 0)) = (∑' z : V, f z) * (∑' z : V, k z) := by
  have h := Equiv.tsum_eq (I417Fresh.finTwoArrowEquiv V).symm
    (fun g : Fin 2 → V => f (g 1) * k (g 0))
  rw [← h]
  simp only [I417Fresh.symm_finTwoArrow_zero, I417Fresh.symm_finTwoArrow_one]
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

/-- `τ` is symmetric. -/
theorem tau_comm (π : Sym2 V → unitInterval) (a b : V) :
    I417Fresh.tau π a b = I417Fresh.tau π b a := by
  rw [I417Fresh.tau, I417Fresh.tau, I417Fresh.connSet_swap]

/-- The refined fresh majorant in the kernel-power form `χ²·T²(w,y) + χ³·T(w,y)`. -/
theorem freshTwoRefined_eq (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (y w : V) :
    freshTwoRefined π χ y w =
      χ ^ 2 * I417Base.iterPow (I417FreshTwo.kernel π) 2 w y +
        χ ^ 3 * I417Base.iterPow (I417FreshTwo.kernel π) 1 w y := by
  unfold freshTwoRefined
  rw [← I417FreshTwo.iterPow_two_eq π w y, I417FreshTwo.iterPow_one,
    I417FreshTwo.kernel_def]

/-! ## The pointwise four-edge bound -/

/-- **The `j = 0` fresh event is contained in the union of the two four-edge shape families.** -/
theorem freshMark_subset_refined_zero (y w : V) (g : Fin 2 → V) :
    I417Gen.freshMark y g 0 w ⊆
      ((⋃ p : V, ShapeA y w (g 0) (g 1) p) ∪ ⋃ p : V, ShapeB y w (g 0) (g 1) p) := by
  rintro ω ⟨hDO, hlab⟩
  have hg1 : Connects ω y (g 1) := by
    rw [I417A.labelEvent_eq_iInter] at hlab
    exact Set.mem_iInter.mp hlab 1
  rcases exists_refined_branch hDO hg1 with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact Or.inl (Set.mem_iUnion.mpr ⟨p, hp⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨p, hp⟩)

/-- **The `j = 1` fresh event is contained in the union of the two four-edge shape families**,
with the two arm labels exchanged. -/
theorem freshMark_subset_refined_one (y w : V) (g : Fin 2 → V) :
    I417Gen.freshMark y g 1 w ⊆
      ((⋃ p : V, ShapeA y w (g 1) (g 0) p) ∪ ⋃ p : V, ShapeB y w (g 1) (g 0) p) := by
  rintro ω ⟨hDO, hlab⟩
  have hg0 : Connects ω y (g 0) := by
    rw [I417A.labelEvent_eq_iInter] at hlab
    exact Set.mem_iInter.mp hlab 0
  rcases exists_refined_branch hDO hg0 with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact Or.inl (Set.mem_iUnion.mpr ⟨p, hp⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨p, hp⟩)

/-- The union of the two `j = 0` shape families is bounded by four two-point factors. -/
theorem shape_union_le_zero (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (y w : V)
    (g : Fin 2 → V) :
    (edgeMeasure π) ((⋃ p : V, ShapeA y w (g 0) (g 1) p) ∪
        ⋃ p : V, ShapeB y w (g 0) (g 1) p) ≤
      ∑' p : V, (I417Fresh.tau π y p * I417Fresh.tau π p w * I417Fresh.tau π w (g 0) *
          I417Fresh.tau π p (g 1) +
        I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 0) *
          I417Fresh.tau π p (g 1)) := by
  refine le_trans (measure_union_le _ _) ?_
  rw [ENNReal.tsum_add]
  refine add_le_add ?_ ?_
  · refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun p => ?_)
    refine le_trans (le_of_eq ?_) (tree4_le π hπ (connSet y p) (connSet p w) (connSet w (g 0))
      (connSet p (g 1)) (isUpper_connSet y p) (isUpper_connSet p w) (isUpper_connSet w (g 0))
      (isUpper_connSet p (g 1)) (finiteWitness_connSet y p) (finiteWitness_connSet p w)
      (finiteWitness_connSet w (g 0)) (finiteWitness_connSet p (g 1)))
    rfl
  · refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun p => ?_)
    refine le_trans (le_of_eq ?_) (tree4_le π hπ (connSet y w) (connSet w p) (connSet p (g 0))
      (connSet p (g 1)) (isUpper_connSet y w) (isUpper_connSet w p) (isUpper_connSet p (g 0))
      (isUpper_connSet p (g 1)) (finiteWitness_connSet y w) (finiteWitness_connSet w p)
      (finiteWitness_connSet p (g 0)) (finiteWitness_connSet p (g 1)))
    rfl

/-- **The four-edge bound for the `q = 2` fresh-copy probability, `j = 0`.** -/
theorem freshMark_measure_le_refined_zero (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (g : Fin 2 → V) :
    (edgeMeasure π) (I417Gen.freshMark y g 0 w) ≤
      ∑' p : V, (I417Fresh.tau π y p * I417Fresh.tau π p w * I417Fresh.tau π w (g 0) *
          I417Fresh.tau π p (g 1) +
        I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 0) *
          I417Fresh.tau π p (g 1)) :=
  le_trans (measure_mono (freshMark_subset_refined_zero y w g))
    (shape_union_le_zero π hπ y w g)

/-- **The four-edge bound for the `q = 2` fresh-copy probability, `j = 1`.** -/
theorem freshMark_measure_le_refined_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (g : Fin 2 → V) :
    (edgeMeasure π) (I417Gen.freshMark y g 1 w) ≤
      ∑' p : V, (I417Fresh.tau π y p * I417Fresh.tau π p w * I417Fresh.tau π w (g 1) *
          I417Fresh.tau π p (g 0) +
        I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 1) *
          I417Fresh.tau π p (g 0)) :=
  le_trans (measure_mono (freshMark_subset_refined_one y w g))
    (shape_union_le_zero π hπ y w (fun i => g (Equiv.swap 0 1 i)))

/-! ## Summing the arms out -/

/-- `∑_g τ(w, g 0)·τ(p, g 1) = χ²`. -/
theorem tsum_arm_pair (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, I417Fresh.hubArmSum π v = χ) (wm p : V) :
    (∑' g : Fin 2 → V, I417Fresh.tau π wm (g 0) * I417Fresh.tau π p (g 1)) = χ ^ 2 := by
  rw [I417Fresh.tsum_fin2_mul]
  rw [show (∑' z : V, I417Fresh.tau π wm z) = χ from hχ wm,
    show (∑' z : V, I417Fresh.tau π p z) = χ from hχ p]
  ring

/-- `∑_g τ(w, g 1)·τ(p, g 0) = χ²`. -/
theorem tsum_arm_pair_swap (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, I417Fresh.hubArmSum π v = χ) (wm p : V) :
    (∑' g : Fin 2 → V, I417Fresh.tau π wm (g 1) * I417Fresh.tau π p (g 0)) = χ ^ 2 := by
  rw [tsum_fin2_mul_swap]
  rw [show (∑' z : V, I417Fresh.tau π wm z) = χ from hχ wm,
    show (∑' z : V, I417Fresh.tau π p z) = χ from hχ p]
  ring

/-- **The summed `j = 0` fresh-copy factor has four two-point factors.** -/
theorem tsum_freshMark_le_refined_zero (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, I417Fresh.hubArmSum π v = χ) :
    (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g 0 w)) ≤
      freshTwoRefined π χ y w := by
  have hterm : ∀ p : V,
      (∑' g : Fin 2 → V, (I417Fresh.tau π y p * I417Fresh.tau π p w * I417Fresh.tau π w (g 0) *
          I417Fresh.tau π p (g 1) +
        I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 0) *
          I417Fresh.tau π p (g 1)))
        = I417Fresh.tau π y p * I417Fresh.tau π p w * χ ^ 2 +
          I417Fresh.tau π y w * I417Fresh.tau π w p * χ ^ 2 := by
    intro p
    rw [ENNReal.tsum_add]
    congr 1
    · have hpull : ∀ g : Fin 2 → V, I417Fresh.tau π y p * I417Fresh.tau π p w *
          I417Fresh.tau π w (g 0) * I417Fresh.tau π p (g 1)
          = (I417Fresh.tau π y p * I417Fresh.tau π p w) *
            (I417Fresh.tau π w (g 0) * I417Fresh.tau π p (g 1)) := fun g => by ring
      simp only [hpull, ENNReal.tsum_mul_left, tsum_arm_pair π χ hχ w p]
    · have hpull : ∀ g : Fin 2 → V, I417Fresh.tau π y w * I417Fresh.tau π w p *
          I417Fresh.tau π p (g 0) * I417Fresh.tau π p (g 1)
          = (I417Fresh.tau π y w * I417Fresh.tau π w p) *
            (I417Fresh.tau π p (g 0) * I417Fresh.tau π p (g 1)) := fun g => by ring
      simp only [hpull, ENNReal.tsum_mul_left, tsum_arm_pair π χ hχ p p]
  refine le_trans (ENNReal.tsum_le_tsum fun g => freshMark_measure_le_refined_zero π hπ y w g) ?_
  rw [ENNReal.tsum_comm]
  rw [show (∑' p : V, ∑' g : Fin 2 → V, (I417Fresh.tau π y p * I417Fresh.tau π p w *
        I417Fresh.tau π w (g 0) * I417Fresh.tau π p (g 1) +
      I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 0) *
        I417Fresh.tau π p (g 1)))
      = ∑' p : V, (I417Fresh.tau π y p * I417Fresh.tau π p w * χ ^ 2 +
        I417Fresh.tau π y w * I417Fresh.tau π w p * χ ^ 2) from tsum_congr hterm]
  rw [ENNReal.tsum_add]
  have hA : (∑' p : V, I417Fresh.tau π y p * I417Fresh.tau π p w * χ ^ 2)
      = χ ^ 2 * I417Base.iterPow (I417FreshTwo.kernel π) 2 w y := by
    rw [ENNReal.tsum_mul_right,
      show (∑' p : V, I417Fresh.tau π y p * I417Fresh.tau π p w)
        = ∑' p : V, I417Fresh.tau π w p * I417Fresh.tau π p y from
        tsum_congr fun p => by rw [tau_comm π y p, tau_comm π p w]; ring,
      ← I417FreshTwo.iterPow_two_eq π w y]
    ring
  have hB : (∑' p : V, I417Fresh.tau π y w * I417Fresh.tau π w p * χ ^ 2)
      = χ ^ 3 * I417Base.iterPow (I417FreshTwo.kernel π) 1 w y := by
    rw [ENNReal.tsum_mul_right,
      show (∑' p : V, I417Fresh.tau π y w * I417Fresh.tau π w p)
        = I417Fresh.tau π y w * χ from by
        rw [ENNReal.tsum_mul_left, show (∑' z : V, I417Fresh.tau π w z) = χ from hχ w],
      I417FreshTwo.iterPow_one, I417FreshTwo.kernel_def, tau_comm π y w]
    ring
  rw [freshTwoRefined_eq, ← hA, ← hB]

/-- **The summed `j = 1` fresh-copy factor has four two-point factors.** -/
theorem tsum_freshMark_le_refined_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, I417Fresh.hubArmSum π v = χ) :
    (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g 1 w)) ≤
      freshTwoRefined π χ y w := by
  have hpt : ∀ g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g 1 w) ≤
      ∑' p : V, (I417Fresh.tau π y p * I417Fresh.tau π p w * I417Fresh.tau π w (g 1) *
          I417Fresh.tau π p (g 0) +
        I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 1) *
          I417Fresh.tau π p (g 0)) := by
    intro g
    have h := le_trans (measure_mono (freshMark_subset_refined_one y w g))
      (shape_union_le_zero π hπ y w (![g 1, g 0]))
    simpa using h
  have hterm : ∀ p : V,
      (∑' g : Fin 2 → V, (I417Fresh.tau π y p * I417Fresh.tau π p w * I417Fresh.tau π w (g 1) *
          I417Fresh.tau π p (g 0) +
        I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 1) *
          I417Fresh.tau π p (g 0)))
        = I417Fresh.tau π y p * I417Fresh.tau π p w * χ ^ 2 +
          I417Fresh.tau π y w * I417Fresh.tau π w p * χ ^ 2 := by
    intro p
    rw [ENNReal.tsum_add]
    congr 1
    · have hpull : ∀ g : Fin 2 → V, I417Fresh.tau π y p * I417Fresh.tau π p w *
          I417Fresh.tau π w (g 1) * I417Fresh.tau π p (g 0)
          = (I417Fresh.tau π y p * I417Fresh.tau π p w) *
            (I417Fresh.tau π w (g 1) * I417Fresh.tau π p (g 0)) := fun g => by ring
      simp only [hpull, ENNReal.tsum_mul_left, tsum_arm_pair_swap π χ hχ w p]
    · have hpull : ∀ g : Fin 2 → V, I417Fresh.tau π y w * I417Fresh.tau π w p *
          I417Fresh.tau π p (g 1) * I417Fresh.tau π p (g 0)
          = (I417Fresh.tau π y w * I417Fresh.tau π w p) *
            (I417Fresh.tau π p (g 1) * I417Fresh.tau π p (g 0)) := fun g => by ring
      simp only [hpull, ENNReal.tsum_mul_left, tsum_arm_pair_swap π χ hχ p p]
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_comm]
  rw [show (∑' p : V, ∑' g : Fin 2 → V, (I417Fresh.tau π y p * I417Fresh.tau π p w *
        I417Fresh.tau π w (g 1) * I417Fresh.tau π p (g 0) +
      I417Fresh.tau π y w * I417Fresh.tau π w p * I417Fresh.tau π p (g 1) *
        I417Fresh.tau π p (g 0)))
      = ∑' p : V, (I417Fresh.tau π y p * I417Fresh.tau π p w * χ ^ 2 +
        I417Fresh.tau π y w * I417Fresh.tau π w p * χ ^ 2) from tsum_congr hterm]
  rw [ENNReal.tsum_add]
  have hA : (∑' p : V, I417Fresh.tau π y p * I417Fresh.tau π p w * χ ^ 2)
      = χ ^ 2 * I417Base.iterPow (I417FreshTwo.kernel π) 2 w y := by
    rw [ENNReal.tsum_mul_right,
      show (∑' p : V, I417Fresh.tau π y p * I417Fresh.tau π p w)
        = ∑' p : V, I417Fresh.tau π w p * I417Fresh.tau π p y from
        tsum_congr fun p => by rw [tau_comm π y p, tau_comm π p w]; ring,
      ← I417FreshTwo.iterPow_two_eq π w y]
    ring
  have hB : (∑' p : V, I417Fresh.tau π y w * I417Fresh.tau π w p * χ ^ 2)
      = χ ^ 3 * I417Base.iterPow (I417FreshTwo.kernel π) 1 w y := by
    rw [ENNReal.tsum_mul_right,
      show (∑' p : V, I417Fresh.tau π y w * I417Fresh.tau π w p)
        = I417Fresh.tau π y w * χ from by
        rw [ENNReal.tsum_mul_left, show (∑' z : V, I417Fresh.tau π w z) = χ from hχ w],
      I417FreshTwo.iterPow_one, I417FreshTwo.kernel_def, tau_comm π y w]
    ring
  rw [freshTwoRefined_eq, ← hA, ← hB]

/-- **The `q = 2` fresh-copy factor has four two-point factors, for every arm label.** -/
theorem tsum_freshMark_le_refined (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, I417Fresh.hubArmSum π v = χ) (j : Fin 2) :
    (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshTwoRefined π χ y w := by
  fin_cases j
  · exact tsum_freshMark_le_refined_zero π hπ y w χ hχ
  · exact tsum_freshMark_le_refined_one π hπ y w χ hχ

/-- **The `q = 2` fresh-copy factor in kernel-power form**: four two-point factors,
`χ²·T²(w,y) + χ³·T(w,y)`. -/
theorem tsum_freshMark_le_refined_iterPow (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, I417Fresh.hubArmSum π v = χ) (j : Fin 2) :
    (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      χ ^ 2 * I417Base.iterPow (I417FreshTwo.kernel π) 2 w y +
        χ ^ 3 * I417Base.iterPow (I417FreshTwo.kernel π) 1 w y :=
  le_trans (tsum_freshMark_le_refined π hπ y w χ hχ j) (le_of_eq (freshTwoRefined_eq π χ y w))

end PercLib.CriticalLRP.I417FreshTwo.Refined
