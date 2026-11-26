/- Independently rebuilt from the accepted `smwx05qau` component, member `m1`.
Production integration revision: `5bd358885b7d12588d7216ae2d6dcee3a9dd5622`.

# Lemma I.4.17 at `q = 2`, arbitrary `p`: the polygon composition

Source: T. Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45).

Everything here is `ℝ≥0∞`-valued and unconditional apart from BK (`π e < 1`, used only through the
already proved fresh-side and marked-side reductions) and the constant-row-sum hypothesis
`∀ v, χ(v) = χ`, which is the abstract form of transitivity of the mean cluster volume and is
supplied by `I417Example.meanVol_eq_of_transitive`.

Contents:

* `iterPow_one`, `iterPow_two_eq`, `iterPow_three_eq`, `iterPow_add_right` — powers of the
  two-point kernel; `iterPow_add_right` is the polygon identity
  `∑_w T^ℓ(x,w)T^m(w,y) = T^(ℓ+m)(x,y)` that raises the exponent when the mark `w` is summed out.
* `tsum_sTerm1_poly`, `tsum_sTerm2_poly`, `tsum_sTerm3_poly`, `tsum_leafShape_eq_poly` — the exact
  evaluation of the summed `q = 2` fresh diagram with the two labelled arms summed out:
  `∑_g leafShape π y w g = χ³T²(w,y) + 2χ²T³(w,y)`.
* `tsum_freshMark_le_poly` — the resulting bound on the fresh-copy factor of I.4.17 at `q = 2`.
* `moment_gap_two_le_poly` — the **complete** composition: the moment gap
  `E|K_x|^p E|K_y|² − E[|K_x|^p|K_y|²1(x↮y)]` is bounded by an explicit finite sum of genuine
  polygon monomials.  Each monomial is `χ^a·T^b(x,y)` with `a + b = 2p+6`; the `y`-legs are
  `b = ℓ+2` and `b = ℓ+3` for `ℓ` the marked depth in `[2,p+1]`, i.e. the final `T`-powers lie in
  `[4,p+4]` and the coefficients are `2·C(p,ℓ)` and `4·C(p,ℓ)` with `C = nonplaneMarkedCount p`.
* `fourArmFresh_eq`, `moment_gap_two_le_poly_fourArm` — the **exact conditional reduction** to the
  paper's exponent: if the fresh-copy factor at `q = 2` is bounded by the four-factor single-hub
  family `∑_a τ(w,a)τ(a,y)χ(a)²`, then the gap is at most
  `∑_{ℓ∈[4,p+3]} 2·C(p,ℓ-2)·χ^(2p+5-ℓ)·T^ℓ(x,y)` — the paper's
  `∑_{3≤ℓ≤p+q+1} C_{p,q,ℓ}T^ℓ(x,y)(E|K|)^{2p+2q+1-ℓ}` at `q = 2`, with `ℓ ∈ [4,p+3] ⊂ [3,p+3]`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Defs
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth
public import PercLib.CriticalLRP.Correlation.I417Example.Trans

/-! The exact fresh two-arm evaluation and its arbitrary-base-order composition.
The paper's exponent appears only under the explicit four-arm fresh hypothesis. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo

open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417Base
open PercLib.CriticalLRP.I417MarkedTransversal

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## Powers of the two-point kernel -/

/-- `T¹ = τ`. -/
theorem iterPow_one (k : V → V → ℝ≥0∞) (a b : V) : I417Base.iterPow k 1 a b = k a b := by
  change (∑' u : V, k a u * (if u = b then 1 else 0)) = k a b
  exact I417Base.tsum_mul_indicator_right (fun u => k a u) b

/-- `T²(a,b) = ∑_u τ(a,u)τ(u,b)`. -/
theorem iterPow_two_eq (π : Sym2 V → unitInterval) (a b : V) :
    I417Base.iterPow (kernel π) 2 a b = ∑' u : V, tau π a u * tau π u b := by
  change (∑' u : V, kernel π a u * I417Base.iterPow (kernel π) 1 u b) = _
  refine tsum_congr fun u => ?_
  rw [iterPow_one]
  rfl

/-- `T³(a,b) = ∑_{u,v} τ(a,u)τ(u,v)τ(v,b)`. -/
theorem iterPow_three_eq (π : Sym2 V → unitInterval) (a b : V) :
    I417Base.iterPow (kernel π) 3 a b =
      ∑' u : V, ∑' v : V, tau π a u * tau π u v * tau π v b := by
  change (∑' u : V, kernel π a u * I417Base.iterPow (kernel π) 2 u b) = _
  calc (∑' u : V, kernel π a u * I417Base.iterPow (kernel π) 2 u b)
      = ∑' u : V, kernel π a u * (∑' v : V, tau π u v * tau π v b) := by
        refine tsum_congr fun u => ?_
        rw [iterPow_two_eq]
    _ = ∑' u : V, ∑' v : V, kernel π a u * (tau π u v * tau π v b) := by
        refine tsum_congr fun u => ?_
        rw [ENNReal.tsum_mul_left]
    _ = ∑' u : V, ∑' v : V, tau π a u * tau π u v * tau π v b := by
        refine tsum_congr fun u => tsum_congr fun v => ?_
        rw [kernel_def]
        ring

/-- **The polygon identity for kernel powers**: summing the mark out multiplies the powers.
`∑_w T^ℓ(x,w)·T^m(w,y) = T^(ℓ+m)(x,y)`. -/
theorem iterPow_add_right (k : V → V → ℝ≥0∞) (n m : ℕ) (x y : V) :
    (∑' w : V, I417Base.iterPow k n x w * I417Base.iterPow k m w y)
      = I417Base.iterPow k (n + m) x y := by
  induction m generalizing y with
  | zero =>
      have h0 : ∀ w : V, I417Base.iterPow k 0 w y = (if w = y then 1 else 0) := fun w => rfl
      simp only [h0]
      rw [I417Base.tsum_mul_indicator_right, Nat.add_zero]
  | succ m ih =>
      have hstep : ∀ w : V, I417Base.iterPow k (m + 1) w y
          = ∑' u : V, I417Base.iterPow k m w u * k u y :=
        fun w => I417Base.iterPow_succ_right k m w y
      simp only [hstep]
      calc (∑' w : V, I417Base.iterPow k n x w * ∑' u : V,
              I417Base.iterPow k m w u * k u y)
          = ∑' w : V, ∑' u : V, I417Base.iterPow k n x w *
              (I417Base.iterPow k m w u * k u y) := by
            refine tsum_congr fun w => ?_
            rw [ENNReal.tsum_mul_left]
        _ = ∑' u : V, ∑' w : V, I417Base.iterPow k n x w *
              (I417Base.iterPow k m w u * k u y) := ENNReal.tsum_comm
        _ = ∑' u : V, (∑' w : V, I417Base.iterPow k n x w *
              I417Base.iterPow k m w u) * k u y := by
            refine tsum_congr fun u => ?_
            rw [show (∑' w : V, I417Base.iterPow k n x w *
                  (I417Base.iterPow k m w u * k u y))
                = ∑' w : V, (I417Base.iterPow k n x w *
                  I417Base.iterPow k m w u) * k u y from
                tsum_congr fun w => by ring]
            rw [ENNReal.tsum_mul_right]
        _ = ∑' u : V, I417Base.iterPow k (n + m) x u * k u y := by
            refine tsum_congr fun u => ?_
            rw [ih u]
        _ = I417Base.iterPow k (n + m + 1) x y :=
            (I417Base.iterPow_succ_right k (n + m) x y).symm
        _ = I417Base.iterPow k (n + (m + 1)) x y := by
            have harith : n + m + 1 = n + (m + 1) := by omega
            rw [harith]

/-! ## The exact `q = 2` fresh diagram, summed over the two labelled arms -/

theorem tsum_sTerm1_poly (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχsum : ∀ v : V, hubArmSum π v = χ) (y w : V) :
    (∑' u : V, ∑' v : V, sTerm1 π y w u v) = χ ^ 3 * iterPow (kernel π) 2 w y := by
  have hstep : ∀ u : V, (∑' v : V, sTerm1 π y w u v) = tau π w u * tau π u y * χ ^ 3 := by
    intro u
    have hpull : ∀ v : V, sTerm1 π y w u v =
        (tau π w u * tau π u y * (χ * χ)) * tau π u v := by
      intro v
      simp only [sTerm1, hχsum]
      ring
    simp only [hpull]
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' i : V, tau π u i) = χ from hχsum u]
    ring
  simp only [hstep]
  rw [ENNReal.tsum_mul_right]
  rw [show (∑' u : V, tau π w u * tau π u y) = iterPow (kernel π) 2 w y from
    (iterPow_two_eq π w y).symm]
  ring

theorem tsum_sTerm2_poly (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχsum : ∀ v : V, hubArmSum π v = χ) (y w : V) :
    (∑' u : V, ∑' v : V, sTerm2 π y w u v) = χ ^ 2 * iterPow (kernel π) 3 w y := by
  have hpull : ∀ u v : V, sTerm2 π y w u v =
      (χ * χ) * (tau π w v * tau π v u * tau π u y) := by
    intro u v
    simp only [sTerm2, hχsum]
    ring
  simp only [hpull, ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm, ← iterPow_three_eq π w y]
  ring

theorem tsum_sTerm3_poly (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχsum : ∀ v : V, hubArmSum π v = χ) (y w : V) :
    (∑' u : V, ∑' v : V, sTerm3 π y w u v) = χ ^ 2 * iterPow (kernel π) 3 w y := by
  have hpull : ∀ u v : V, sTerm3 π y w u v =
      (χ * χ) * (tau π w u * tau π u v * tau π v y) := by
    intro u v
    simp only [sTerm3, hχsum]
    ring
  simp only [hpull, ENNReal.tsum_mul_left]
  rw [← iterPow_three_eq π w y]
  ring

/-- **The summed `q = 2` fresh diagram evaluates exactly to a two-term polygon polynomial.** -/
theorem tsum_leafShape_eq_poly (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχsum : ∀ v : V, hubArmSum π v = χ) (y w : V) :
    (∑' g : Fin 2 → V, leafShape π y w g) = freshTwoPoly π χ y w := by
  rw [tsum_leafShape_eq]
  simp only [ENNReal.tsum_add]
  rw [tsum_sTerm1_poly π χ hχsum y w, tsum_sTerm2_poly π χ hχsum y w,
    tsum_sTerm3_poly π χ hχsum y w]
  simp only [freshTwoPoly]
  ring

/-- **The `q = 2` hub-star diagram sum is at most `χ³T²(w,y) + 2χ²T³(w,y)`.** -/
theorem tsum_hubStar_le_poly (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (χ : ℝ≥0∞)
    (hχsum : ∀ v : V, hubArmSum π v = χ) (y w : V) :
    (∑' g : Fin 2 → V, (edgeMeasure π) (hubStar y w g)) ≤ freshTwoPoly π χ y w :=
  le_trans (ENNReal.tsum_le_tsum fun g => hubStar_measure_le_leafShape π hπ y w g)
    (le_of_eq (tsum_leafShape_eq_poly π χ hχsum y w))

/-- **The fresh-copy factor of I.4.17 at `q = 2`**, evaluated. -/
theorem tsum_freshMark_le_poly (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (χ : ℝ≥0∞)
    (hχsum : ∀ v : V, hubArmSum π v = χ) (y w : V) (j : Fin 2) :
    (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshTwoPoly π χ y w :=
  le_trans (fresh_factor_le_hubStar π y w j) (tsum_hubStar_le_poly π hπ χ hχsum y w)

/-! ## The `Fin 2 × V` index set -/

/-- The two label copies of the marked fresh index set contribute a factor `2`. -/
theorem tsum_finTwo_mul (f : V → ℝ≥0∞) :
    (∑' jw : Fin 2 × V, f jw.2) = 2 * ∑' w : V, f w := by
  rw [ENNReal.tsum_prod']
  rw [tsum_fintype]
  simp [Finset.sum_const, two_mul]

/-! ## The `q = 2` moment gap: the complete polygon composition -/

/-- **Lemma I.4.17 at `q = 2`, arbitrary `p`: the polygon composition, evaluated.**

`E|K_x|^p E|K_y|² − E[|K_x|^p|K_y|²1(x↮y)]` is at most

`2·∑_{ℓ∈[2,p+1]} C(p,ℓ)·χ^(2p+4-ℓ)·T^(ℓ+2)(x,y)
   + 2·∑_{ℓ∈[2,p+1]} 2·C(p,ℓ)·χ^(2p+3-ℓ)·T^(ℓ+3)(x,y)`,

with `C = nonplaneMarkedCount p`, `χ = E|K|` and `T` the two-point matrix.  Every summand is a
genuine polygon monomial produced by (i) the marked bound `jointPow ≤ ∑_ℓ C(p,ℓ)χ^(2p+1-ℓ)T^ℓ(x,w)`,
(ii) the evaluated `q = 2` fresh factor `χ³T²(w,y) + 2χ²T³(w,y)` of `tsum_freshMark_le_poly`, and
(iii) the polygon identity `∑_w T^ℓ(x,w)T^m(w,y) = T^(ℓ+m)(x,y)`.

Each monomial `χ^a·T^b(x,y)` has `a + b = 2p+6` and `b ∈ [4,p+4]`; the two `y`-legs have length `2`
and `3`.  This is the `q = 2` composition with the five-factor fresh bound, i.e. one `χ` more than
the paper's normalisation `2p+2q+1 = 2p+5`; see `moment_gap_two_le_poly_fourArm` for the exact
four-factor input that lands on `2p+5`. -/
theorem moment_gap_two_le_poly (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) (p : ℕ) (hp : 1 ≤ p) :
    I417A.momentProd π x y p 2 - I417A.rawDiff π x y p 2 ≤
      2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (I417.meanVol π x ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 2) x y))
      + 2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1),
            ((2 : ℝ≥0∞) * (nonplaneMarkedCount p ℓ : ℝ≥0∞)) *
            (I417.meanVol π x ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 3) x y)) := by
  classical
  set χ : ℝ≥0∞ := I417.meanVol π x with hχdef
  have hχsum : ∀ v : V, hubArmSum π v = χ := by
    intro v
    change (∑' z : V, (edgeMeasure π) (connSet v z)) = χ
    rw [hχdef]
    exact hχ v
  refine le_trans (I417Gen.moment_gap_tsub_le_marked π x y (p := p) (q := 2) (by norm_num)) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun jw : Fin 2 × V =>
    mul_le_mul' le_rfl (tsum_freshMark_le_poly π hπ χ hχsum y jw.2 jw.1)) ?_
  rw [tsum_finTwo_mul (fun w => I417Gen.jointPow π x p w * freshTwoPoly π χ y w)]
  refine le_trans (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun w =>
    mul_le_mul' (jointPow_le_nonplane_markedDepth π hπ χ (fun v => hχsum v) x hp w)
      le_rfl)) ?_
  simp only [freshTwoPoly]
  simp only [show (fun a b : V => (edgeMeasure π) (connSet a b)) = kernel π from rfl]
  have hterm : ∀ ℓ ∈ Finset.Icc 2 (p + 1),
      (∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (χ ^ 3 * iterPow (kernel π) 2 w y + 2 * (χ ^ 2 * iterPow (kernel π) 3 w y)))
        = (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (χ ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
          + ((2 : ℝ≥0∞) * (nonplaneMarkedCount p ℓ : ℝ≥0∞)) *
            (χ ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have h1 : 2 * p + 1 - ℓ + 3 = 2 * p + 4 - ℓ := by omega
    have h2 : 2 * p + 1 - ℓ + 2 = 2 * p + 3 - ℓ := by omega
    have hsplit : ∀ w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (χ ^ 3 * iterPow (kernel π) 2 w y + 2 * (χ ^ 2 * iterPow (kernel π) 3 w y))
        = ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * χ ^ 3)) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 2 w y)
          + (((2 : ℝ≥0∞) * (nonplaneMarkedCount p ℓ : ℝ≥0∞)) *
              (χ ^ (2 * p + 1 - ℓ) * χ ^ 2)) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 3 w y) := by
      intro w
      ring
    simp only [hsplit]
    rw [ENNReal.tsum_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    rw [iterPow_add_right (kernel π) ℓ 2 x y, iterPow_add_right (kernel π) ℓ 3 x y]
    rw [← pow_add, h1, ← pow_add, h2]
    ring
  have hpush : ∀ w : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w)) *
        (χ ^ 3 * iterPow (kernel π) 2 w y + 2 * (χ ^ 2 * iterPow (kernel π) 3 w y))
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (χ ^ 3 * iterPow (kernel π) 2 w y + 2 * (χ ^ 2 * iterPow (kernel π) 3 w y)) :=
    fun w => Finset.sum_mul ..
  simp only [hpush]
  rw [I417Base.tsum_finset_sum]
  rw [show (∑ ℓ ∈ Finset.Icc 2 (p + 1),
        ∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (χ ^ 3 * iterPow (kernel π) 2 w y + 2 * (χ ^ 2 * iterPow (kernel π) 3 w y)))
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1),
          ((nonplaneMarkedCount p ℓ : ℝ≥0∞) *
              (χ ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
            + ((2 : ℝ≥0∞) * (nonplaneMarkedCount p ℓ : ℝ≥0∞)) *
              (χ ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 3) x y))
      from Finset.sum_congr rfl fun ℓ hℓ => hterm ℓ hℓ]
  rw [Finset.sum_add_distrib]
  exact le_of_eq (by ring)

/-! ## The exact four-factor fresh input and the paper's exponent `2p+5` -/

/-- The single-hub four-arm fresh family evaluates to `χ²·T²(w,y)`: four two-point factors. -/
theorem fourArmFresh_eq (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχsum : ∀ v : V, hubArmSum π v = χ) (y w : V) :
    fourArmFresh π y w = χ ^ 2 * iterPow (kernel π) 2 w y := by
  have hpull : ∀ a : V, kernel π w a * kernel π a y * (hubArmSum π a * hubArmSum π a)
      = (χ * χ) * (tau π w a * tau π a y) := by
    intro a
    simp only [hχsum, kernel_def]
    ring
  simp only [fourArmFresh, hpull, ENNReal.tsum_mul_left]
  rw [show (∑' a : V, tau π w a * tau π a y) = iterPow (kernel π) 2 w y from
    (iterPow_two_eq π w y).symm]
  ring

/-- **The `q = 2` moment gap from the four-factor fresh input**, in the marked-depth index. -/
theorem moment_gap_two_le_poly_fourArm_aux (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) (p : ℕ) (hp : 1 ≤ p)
    (hfresh : ∀ (j : Fin 2) (w : V),
      (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤ fourArmFresh π y w) :
    I417A.momentProd π x y p 2 - I417A.rawDiff π x y p 2 ≤
      2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (I417.meanVol π x ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)) := by
  classical
  set χ : ℝ≥0∞ := I417.meanVol π x with hχdef
  have hχsum : ∀ v : V, hubArmSum π v = χ := by
    intro v
    change (∑' z : V, (edgeMeasure π) (connSet v z)) = χ
    rw [hχdef]
    exact hχ v
  refine le_trans (I417Gen.moment_gap_tsub_le_marked π x y (p := p) (q := 2) (by norm_num)) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun jw : Fin 2 × V =>
    mul_le_mul' le_rfl (le_trans (hfresh jw.1 jw.2)
      (le_of_eq (fourArmFresh_eq π χ hχsum y jw.2)))) ?_
  rw [tsum_finTwo_mul (fun w => I417Gen.jointPow π x p w * (χ ^ 2 * iterPow (kernel π) 2 w y))]
  refine le_trans (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun w =>
    mul_le_mul' (jointPow_le_nonplane_markedDepth π hπ χ (fun v => hχsum v) x hp w)
      le_rfl)) ?_
  simp only [show (fun a b : V => (edgeMeasure π) (connSet a b)) = kernel π from rfl]
  have hterm : ∀ ℓ ∈ Finset.Icc 2 (p + 1),
      (∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (χ ^ 2 * iterPow (kernel π) 2 w y))
        = (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (χ ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have h1 : 2 * p + 1 - ℓ + 2 = 2 * p + 3 - ℓ := by omega
    have hsplit : ∀ w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) * (χ ^ 2 * iterPow (kernel π) 2 w y)
        = ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * χ ^ 2)) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 2 w y) := by
      intro w
      ring
    simp only [hsplit, ENNReal.tsum_mul_left]
    rw [iterPow_add_right (kernel π) ℓ 2 x y]
    rw [← pow_add, h1]
    try ring
  have hpush : ∀ w : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w)) *
        (χ ^ 2 * iterPow (kernel π) 2 w y)
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (χ ^ 2 * iterPow (kernel π) 2 w y) := fun w => Finset.sum_mul ..
  simp only [hpush]
  rw [I417Base.tsum_finset_sum]
  rw [show (∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (χ ^ 2 * iterPow (kernel π) 2 w y))
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
      from Finset.sum_congr rfl fun ℓ hℓ => hterm ℓ hℓ]

/-- **Lemma I.4.17 at `q = 2`, arbitrary `p`, in the paper's normalisation.**

If the fresh-copy factor at `q = 2` is bounded by the four-factor single-hub family
`fourArmFresh π y w = ∑_a τ(w,a)τ(a,y)χ(a)²`, then

`E|K_x|^p E|K_y|² − E[|K_x|^p|K_y|²1(x↮y)]
   ≤ ∑_{ℓ∈[4,p+3]} 2·C(p,ℓ−2)·χ^(2p+5-ℓ)·T^ℓ(x,y)`,

i.e. the `q = 2` case of the paper's `∑_{3≤ℓ≤p+q+1} C_{p,q,ℓ} T^ℓ(x,y)(E|K|)^{2p+2q+1-ℓ}`: the index
range `[4,p+3]` is inside `[3,p+3] = [3,p+q+1]`, every summand is a genuine polygon monomial with
exponent exactly `2p+5-ℓ`, and the coefficient `2·C(p,ℓ−2)` is the two label copies `Fin 2` times
the non-plane marked count at depth `ℓ−2`.  The statement below carries the index as `ℓm = ℓ−2`,
so the summand is read at `ℓ = ℓm+2` and the `T`-powers run over exactly `[4,p+3]`; the exponent
is written in the `2p+5-ℓ` form to make that identification literal. -/
theorem moment_gap_two_le_poly_fourArm (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) (p : ℕ) (hp : 1 ≤ p)
    (hfresh : ∀ (j : Fin 2) (w : V),
      (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤ fourArmFresh π y w) :
    I417A.momentProd π x y p 2 - I417A.rawDiff π x y p 2 ≤
      ∑ ℓm ∈ Finset.Icc 2 (p + 1), ((2 : ℝ≥0∞) * (nonplaneMarkedCount p ℓm : ℝ≥0∞)) *
        (I417.meanVol π x ^ (2 * p + 5 - (ℓm + 2)) *
          iterPow (kernel π) (ℓm + 2) x y) := by
  refine le_trans (moment_gap_two_le_poly_fourArm_aux π hπ x y hχ p hp hfresh) ?_
  have h2 : (2 : ℝ≥0∞) * (∑ ℓm ∈ Finset.Icc 2 (p + 1),
        (nonplaneMarkedCount p ℓm : ℝ≥0∞) *
          (I417.meanVol π x ^ (2 * p + 3 - ℓm) * iterPow (kernel π) (ℓm + 2) x y))
      = ∑ ℓm ∈ Finset.Icc 2 (p + 1),
          ((2 : ℝ≥0∞) * (nonplaneMarkedCount p ℓm : ℝ≥0∞)) *
            (I417.meanVol π x ^ (2 * p + 3 - ℓm) * iterPow (kernel π) (ℓm + 2) x y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓm _ => by ring
  rw [h2]
  refine le_of_eq (Finset.sum_congr rfl fun ℓm hℓm => ?_)
  simp only [Finset.mem_Icc] at hℓm
  rw [show 2 * p + 5 - (ℓm + 2) = 2 * p + 3 - ℓm from by omega]

/-! ## The vertex-transitive specialisation -/

/-- **The vertex-transitive specialisation, no subcritical assumption.**

For a vertex-transitive opening profile (every vertex is the image of `x` under a permutation
preserving `π`) the mean cluster volume is constant
(`I417Example.meanVol_eq_of_transitive`), so the polygon composition applies as it stands. -/
theorem moment_gap_two_le_poly_transitive (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) (hp : 1 ≤ p)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    I417A.momentProd π x y p 2 - I417A.rawDiff π x y p 2 ≤
      2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (I417.meanVol π x ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 2) x y))
      + 2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1),
            ((2 : ℝ≥0∞) * (nonplaneMarkedCount p ℓ : ℝ≥0∞)) *
            (I417.meanVol π x ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 3) x y)) :=
  moment_gap_two_le_poly π hπ x y (I417Example.meanVol_eq_of_transitive π x htrans) p hp

/-! ### Axiom audit -/

set_option linter.hashCommand false

#print axioms iterPow_add_right
#print axioms tsum_leafShape_eq_poly
#print axioms tsum_freshMark_le_poly
#print axioms moment_gap_two_le_poly
#print axioms fourArmFresh_eq
#print axioms moment_gap_two_le_poly_fourArm_aux
#print axioms moment_gap_two_le_poly_fourArm
#print axioms moment_gap_two_le_poly_transitive

end PercLib.CriticalLRP.I417FreshTwo
