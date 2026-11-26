/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Case 3 of Proposition I.4.20: the polygon summation.  Independent Ultramath work.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Defs

/-!
# Summing the tree expansion of Lemma I.4.17 against the polygon bound of
Lemma I.4.18

This file performs the two summations that constitute Case 3 of the proof of
Proposition I.4.20 (paper.txt lines 2883--2887):

* over the pairs `y ∈ B_r`, turning the per-pair tree expansion of Lemma I.4.17 into
  a bound on the whole discrepancy `prodFactor - mixedExcl`;
* over the path lengths `j ∈ [3, p+2]`, using the *uniform-in-`y`* polygon bound of
  Lemma I.4.18 to replace `T^j(o,y)(E|K|)^{2p+3-j}` by
  `(∇_{r^c}+r^{-c})(E|K|)^{2p}` and then to collect the coefficients into the single
  constant `Σ_j C_j`.

The result is the Case 3 display of the paper,
`|B_r| E|K|^a E|K|^b - A_ℓ(r) ≤ |B_r| (Σ_j C_j)(∇_{r^c}+r^{-c})(E|K|)^{2p}`,
and its averaged form
`|B_r|^{-1}(|B_r| E|K|^a E|K|^b - A_ℓ(r)) ≤ (Σ_j C_j)(∇_{r^c}+r^{-c})(E|K|)^{2p}`.

The two remaining ingredients, Lemmas I.4.17 and I.4.18, enter only through the
structures `HasTreeExpansion` and `HasPolygonBound`; nothing else is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Finset
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-! ## The exponent identity of the polygon summation -/

/-- On the range `3 ≤ j ≤ 2p+3` of path lengths of the tree expansion, the two
powers of `E|K|` multiply back to `(E|K|)^{2p}`. -/
theorem polygon_pow_identity (M : ℝ≥0∞) {p j : ℕ} (h3 : 3 ≤ j) (hj : j ≤ 2 * p + 3) :
    M ^ (2 * p + 3 - j) * M ^ (j - 3) = M ^ (2 * p) := by
  rw [← pow_add]
  congr 1
  omega

/-- For `p ≥ 1` the path lengths `3 ≤ j ≤ p+2` of the tree expansion lie in the
range `3 ≤ j ≤ 2p+3` required by `pow_mul_pow_sub`. -/
theorem le_two_mul_add_three {p j : ℕ} (hp : 1 ≤ p) (hj : j ≤ p + 2) : j ≤ 2 * p + 3 := by
  omega

/-! ## Summation over the ball at a fixed path length -/

/-- The polygon bound of Lemma I.4.18, summed over the `|B|` pairs of the ball:
`Σ_{y∈B} T^j(o,y) ≤ |B| (∇_{r^c}+r^{-c})(E|K|)^{j-3}`. -/
theorem sum_poly_le (B : Finset V) (poly : V → ℕ → ℝ≥0∞) (M : ℝ≥0∞) (j : ℕ) (Bpoly : ℝ)
    (h : ∀ y ∈ B, poly y j ≤ ENNReal.ofReal Bpoly * M ^ (j - 3)) :
    ∑ y ∈ B, poly y j ≤ (B.card : ℝ≥0∞) * (ENNReal.ofReal Bpoly * M ^ (j - 3)) := by
  calc ∑ y ∈ B, poly y j
      ≤ ∑ _y ∈ B, (ENNReal.ofReal Bpoly * M ^ (j - 3)) := Finset.sum_le_sum h
    _ = B.card • (ENNReal.ofReal Bpoly * M ^ (j - 3)) := Finset.sum_const _
    _ = (B.card : ℝ≥0∞) * (ENNReal.ofReal Bpoly * M ^ (j - 3)) := by rw [nsmul_eq_mul]

/-- The tree expansion as a sum over path lengths of sums over the ball. -/
theorem sum_treePoly_eq (B : Finset V) (poly : V → ℕ → ℝ≥0∞) (C : ℕ → ℝ) (M : ℝ≥0∞)
    (p : ℕ) :
    ∑ y ∈ B, treePoly poly C M p y
      = ∑ j ∈ Finset.Icc 3 (p + 2), ∑ y ∈ B,
          ENNReal.ofReal (C j) * poly y j * M ^ (2 * p + 3 - j) := by
  simp only [treePoly]
  exact Finset.sum_comm

/-! ## The polygon summation -/

/-- **The polygon summation of Case 3.**  If the `T`-powers satisfy the polygon
bound of Lemma I.4.18 with factor `Bpoly = ∇_{r^c}+r^{-c}`, then the whole tree
expansion of Lemma I.4.17 over the ball is at most
`|B| (Σ_j C_j) (∇_{r^c}+r^{-c}) (E|K|)^{2p}`. -/
theorem polygon_sum_le {π : Sym2 V → unitInterval} {o : V} {B : Finset V} {p : ℕ}
    (hp : 1 ≤ p) {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ} {Bpoly : ℝ}
    (hC : ∀ j, 0 ≤ C j) (hPoly : HasPolygonBound π o B p poly Bpoly) :
    ∑ y ∈ B, treePoly poly C (I420Case1.powMomentAt π 1 o) p y ≤
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) * ENNReal.ofReal Bpoly *
        I420Case1.powMomentAt π 1 o ^ (2 * p) := by
  let M := I420Case1.powMomentAt π 1 o
  have hswap := sum_treePoly_eq B poly C M p
  have hstep : ∀ j ∈ Finset.Icc 3 (p + 2),
      ∑ y ∈ B, ENNReal.ofReal (C j) * poly y j * M ^ (2 * p + 3 - j)
        = ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) * (∑ y ∈ B, poly y j) := by
    intro j _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hbound : ∀ j ∈ Finset.Icc 3 (p + 2),
      ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) * (∑ y ∈ B, poly y j)
        ≤ ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
            ((B.card : ℝ≥0∞) * (ENNReal.ofReal Bpoly * M ^ (j - 3))) := by
    intro j hj
    have h3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj2 : j ≤ p + 2 := (Finset.mem_Icc.mp hj).2
    have hsumj := sum_poly_le B poly M j Bpoly fun y hy =>
      hPoly.bound y hy j (Finset.mem_Icc.mpr ⟨h3, hj2⟩)
    exact mul_le_mul_right hsumj _

  have hcollapse : ∀ j ∈ Finset.Icc 3 (p + 2),
      ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
          ((B.card : ℝ≥0∞) * (ENNReal.ofReal Bpoly * M ^ (j - 3)))
        = (B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly *
            (ENNReal.ofReal (C j) * M ^ (2 * p)) := by
    intro j hj
    have h3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj2 : j ≤ p + 2 := (Finset.mem_Icc.mp hj).2
    calc ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
          ((B.card : ℝ≥0∞) * (ENNReal.ofReal Bpoly * M ^ (j - 3)))
        = ENNReal.ofReal (C j) * (M ^ (2 * p + 3 - j) * M ^ (j - 3)) *
            ((B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly) := by ring
      _ = ENNReal.ofReal (C j) * M ^ (2 * p) *
            ((B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly) := by
          rw [polygon_pow_identity (p := p) M h3 (le_two_mul_add_three hp hj2)]
      _ = (B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly *
            (ENNReal.ofReal (C j) * M ^ (2 * p)) := by ring
  calc ∑ y ∈ B, treePoly poly C M p y
      = ∑ j ∈ Finset.Icc 3 (p + 2), ∑ y ∈ B,
          ENNReal.ofReal (C j) * poly y j * M ^ (2 * p + 3 - j) := hswap
    _ = ∑ j ∈ Finset.Icc 3 (p + 2),
          ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) * (∑ y ∈ B, poly y j) :=
        Finset.sum_congr rfl hstep
    _ ≤ ∑ j ∈ Finset.Icc 3 (p + 2),
          ENNReal.ofReal (C j) * M ^ (2 * p + 3 - j) *
            ((B.card : ℝ≥0∞) * (ENNReal.ofReal Bpoly * M ^ (j - 3))) :=
        Finset.sum_le_sum hbound
    _ = ∑ j ∈ Finset.Icc 3 (p + 2),
          (B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly *
            (ENNReal.ofReal (C j) * M ^ (2 * p)) := Finset.sum_congr rfl hcollapse
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly *
          (∑ j ∈ Finset.Icc 3 (p + 2), ENNReal.ofReal (C j) * M ^ (2 * p)) := by
        rw [Finset.mul_sum]
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly *
          ((∑ j ∈ Finset.Icc 3 (p + 2), ENNReal.ofReal (C j)) * M ^ (2 * p)) := by
        rw [Finset.sum_mul]
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal Bpoly *
          (ENNReal.ofReal (coeffSum C p) * M ^ (2 * p)) := by
        rw [coeffSum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hC j)]
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) * ENNReal.ofReal Bpoly *
          M ^ (2 * p) := by ring

/-! ## The Case 3 discrepancy bound -/

/-- **The Case 3 chain at the level of the canonical law.**  From the tree expansion
of Lemma I.4.17 (per pair) and the polygon bound of Lemma I.4.18 (uniform in the
pair), the product factor exceeds the excluded mixed marked expectation by at most
`|B| (Σ_j C_j)(∇_{r^c}+r^{-c})(E|K|)^{2p}`. -/
theorem prodFactor_le_mixedExcl_add_polygon {π : Sym2 V → unitInterval} {o : V}
    {B : Finset V} {a b p : ℕ} (hp : 1 ≤ p) {poly : V → ℕ → ℝ≥0∞} {C : ℕ → ℝ}
    {Bpoly : ℝ} (hC : ∀ j, 0 ≤ C j) (hTree : HasTreeExpansion π o B a b p poly C)
    (hPoly : HasPolygonBound π o B p poly Bpoly) :
    I420Case1.prodFactor π o a b B ≤ I420Case1.mixedExcl π o a b B +
      (B.card : ℝ≥0∞) * ENNReal.ofReal (coeffSum C p) * ENNReal.ofReal Bpoly *
        I420Case1.powMomentAt π 1 o ^ (2 * p) := by
  have hsum : ∑ y ∈ B, pairFactor π o y a b ≤
      ∑ y ∈ B, (pairExcl π o y a b + treePoly poly C
        (I420Case1.powMomentAt π 1 o) p y) := Finset.sum_le_sum hTree.expansion
  rw [Finset.sum_add_distrib, sum_pairFactor] at hsum
  have hstep : ∑ y ∈ B, pairExcl π o y a b = I420Case1.mixedExcl π o a b B :=
    sum_pairExcl o a b B
  rw [hstep] at hsum
  exact hsum.trans (add_le_add_right (polygon_sum_le hp hC hPoly) _)

end I420Case3

end PercLib.CriticalLRP
