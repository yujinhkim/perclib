/-
The outer moment composition of Lemma I.4.17, discharged by the summed fresh bound
(direction `(B) UNRESTRICTED-FIBRE EVALUATION`, swarm `smwxtabcx`, member `m2`).

Read-only against production `repo/.scratch/critical-lrp-orchestration`
(HEAD `1cf119aa54facb618600bb09077747b6a3b891f3`, Lean 4.35.0).  Nothing outside
`.ultramath/smwxtabcx/m2/` is written.

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45):

  `0 ≤ E|K|^p E|K|^q − E[|K_x|^p|K_y|^q 1(x ↮ y)] ≤ ∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) χ^{2p+2q+1−ℓ}`.

This file contains **no new definitions**.  It composes three inputs, all already in the
repository:

* production `I417Gen.moment_gap_tsub_le_marked` — the marked two-copy expansion, with the fresh
  factor in the summed form `∑_{g : Fin q → V} P(freshMark y g j w)`;
* production `I417MarkedTransversal.jointPow_le_nonplane_markedDepth` — the base (marked) side
  `E[|K_x|^p 1(w ∈ K_x)] ≤ ∑_{ℓ∈[2,p+1]} C^base_{p,ℓ} χ^{2p+1-ℓ} T^ℓ(x,w)`;
* `Main.summedFreshProfile` — the fresh side `∑_g P(freshMark y g j w) ≤
  ∑_{m∈[1,q]} C^fresh_{q,m} χ^{2q-m} T^m(w,y)`, which `Main` proves at every `q ≥ 1`.

The composition is the paper's polygon step: `∑_w T^ℓ(x,w) T^m(w,y) = T^{ℓ+m}(x,y)`
(production `I417FreshTwo.iterPow_add_right`, an equality, no symmetry needed), so every composed
term has `χ`-exponent plus path length `(2p+1-ℓ) + (2q-m) + (ℓ+m) = 2p+2q+1` and path length
`ℓ+m ∈ [3, p+q+1]`.  The result is the printed normal form, un-grouped over the pair `(ℓ,m)`;
grouping by `L = ℓ+m` with `C_{p,q,L} = q ∑_{ℓ+m=L} C^base_{p,ℓ} C^fresh_{q,m}` is pure finite-sum
bookkeeping on this polynomial.

The `q`-fold factor is the number of marked terminals `j : Fin q` (the summed expansion carries
`∑_{jw : Fin q × V}` and the fresh bound does not depend on `j`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.SummedFresh.Defs
public import PercLib.CriticalLRP.Correlation.I417.SummedFresh.Main
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth
public import PercLib.CriticalLRP.Correlation.I417.General.Main

/-! Composition of the summed fresh and marked depth-polynomial bounds. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417SummedFresh

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## 1. Elementary sum lemmas -/

/-- A sum over a countable type of a finite sum is the finite sum of the sums. -/
theorem tsum_finsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → V → ℝ≥0∞) :
    (∑' a : V, ∑ i ∈ s, f i a) = ∑ i ∈ s, ∑' a : V, f i a := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [ENNReal.tsum_add, ih]

/-- A summand that does not depend on the `Fin q` coordinate: summing over `Fin q × V` gives
`q` copies. -/
theorem tsum_fin_snd (q : ℕ) (f : V → ℝ≥0∞) :
    (∑' jw : Fin q × V, f jw.2) = (q : ℝ≥0∞) * ∑' w : V, f w := by
  rw [ENNReal.tsum_prod']
  have h2 : (∑' j : Fin q, ∑' w : V, f (j, w).2) = ∑' _j : Fin q, ∑' w : V, f w :=
    tsum_congr fun _ => rfl
  rw [h2, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 2. The polygon step on one pair of depths -/

/-- **One composed pair of monomials, summed over the mark.**  The product of the base monomial
`a · χ^α · T^ℓ(x,w)` and the fresh monomial `b · χ^β · T^m(w,y)`, summed over `w`, is
`(a b) · χ^(α+β) · T^(ℓ+m)(x,y)`: the paper's polygon identity, an equality. -/
theorem tsum_pair_monomial (κ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (a b : ℝ≥0∞) (α β ℓ m : ℕ) (x y : V) :
    (∑' w : V,
        (a * (χ ^ α * I417Base.iterPow κ ℓ x w)) *
          (b * (χ ^ β * I417Base.iterPow κ m w y)))
      = (a * b) * (χ ^ (α + β) * I417Base.iterPow κ (ℓ + m) x y) := by
  have hterm : ∀ w : V,
      (a * (χ ^ α * I417Base.iterPow κ ℓ x w)) *
          (b * (χ ^ β * I417Base.iterPow κ m w y)) =
        (a * b * (χ ^ α * χ ^ β)) *
          (I417Base.iterPow κ ℓ x w * I417Base.iterPow κ m w y) := by
    intro w
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, I417FreshTwo.iterPow_add_right κ ℓ m x y,
    ← pow_add]
  ring

/-! ## 3. The composed polynomial -/

/-- **The product of the base and fresh polynomials, mark summed out.**  The `(ℓ,m)` term of the
base polynomial times the `(ℓ,m)` term of the fresh polynomial, summed over the mark `w`, collects
into the composed monomial `χ^(2p+2q+1-(ℓ+m)) · T^(ℓ+m)(x,y)` with coefficient `C^base_ℓ C^fresh_m`. -/
theorem tsum_base_mul_fresh (κ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (p q : ℕ) (Cb Cf : ℕ → ℕ) (x y : V) :
    (∑' w : V,
        (∑ ℓ ∈ Finset.Icc 2 (p + 1),
            (Cb ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * I417Base.iterPow κ ℓ x w)) *
          (∑ m ∈ Finset.Icc 1 q,
            (Cf m : ℝ≥0∞) * (χ ^ (2 * q - m) * I417Base.iterPow κ m w y)))
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑ m ∈ Finset.Icc 1 q,
          ((Cb ℓ * Cf m : ℕ) : ℝ≥0∞) *
            (χ ^ (2 * p + 2 * q + 1 - (ℓ + m)) * I417Base.iterPow κ (ℓ + m) x y) := by
  have hpt : ∀ w : V,
      (∑ ℓ ∈ Finset.Icc 2 (p + 1),
          (Cb ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * I417Base.iterPow κ ℓ x w)) *
          (∑ m ∈ Finset.Icc 1 q,
            (Cf m : ℝ≥0∞) * (χ ^ (2 * q - m) * I417Base.iterPow κ m w y)) =
        ∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑ m ∈ Finset.Icc 1 q,
          ((Cb ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * I417Base.iterPow κ ℓ x w)) *
            ((Cf m : ℝ≥0∞) * (χ ^ (2 * q - m) * I417Base.iterPow κ m w y)) :=
    fun w => Finset.sum_mul_sum _ _ _ _
  rw [tsum_congr hpt]
  rw [tsum_finsetSum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [tsum_finsetSum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hℓ1, hℓ2⟩ := Finset.mem_Icc.mp hℓ
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  rw [tsum_pair_monomial κ χ (Cb ℓ : ℝ≥0∞) (Cf m : ℝ≥0∞)
    (2 * p + 1 - ℓ) (2 * q - m) ℓ m x y]
  have hexp : 2 * p + 1 - ℓ + (2 * q - m) = 2 * p + 2 * q + 1 - (ℓ + m) := by omega
  rw [hexp]
  push_cast
  ring

/-- Pulling the `q`-fold multiplicity of the marked terminal into the composed coefficients. -/
theorem mul_compCoeff (r p q : ℕ) (Cb Cf : ℕ → ℕ) (X : ℕ → ℕ → ℝ≥0∞) :
    (r : ℝ≥0∞) * (∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑ m ∈ Finset.Icc 1 q,
        ((Cb ℓ * Cf m : ℕ) : ℝ≥0∞) * X ℓ m) =
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑ m ∈ Finset.Icc 1 q,
        ((r * Cb ℓ * Cf m : ℕ) : ℝ≥0∞) * X ℓ m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

/-! ## 4. Lemma I.4.17 at general `p, q`, unconditional -/

/-- **Lemma I.4.17, arbitrary `p, q ≥ 1`, in the printed normal form (un-grouped over `(ℓ,m)`).**

For every `π` with `π e < 1`, every constant row sum `χ` of the two-point kernel and all vertices
`x, y`:

`E|K|^p E|K|^q − E[|K_x|^p|K_y|^q 1(x ↮ y)] ≤
  ∑_{ℓ∈[2,p+1]} ∑_{m∈[1,q]} q · C^base_{p,ℓ} · C^fresh_{q,m} · χ^{2p+2q+1-(ℓ+m)} · T^{ℓ+m}(x,y)`,

with `C^base` production's non-plane marked-depth count, `C^fresh_{q,m} = I417FreshDepth.genCoeff q m`
the number of fresh branches of pin--mark depth `m`, and every term obeying
`(exponent) + (path length) = 2p + 2q + 1`, `3 ≤ ℓ + m ≤ p + q + 1`.

All premises are explicit: `[Countable V]`, `[DecidableEq V]`, `π e < 1`, `1 ≤ p`, `1 ≤ q`, and
the constant row sum `χ`.  Nothing else is assumed, and no step is conditional. -/
theorem moment_gap_le_pairPoly (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {χ : ℝ≥0∞}
    (hχ : ∀ v : V, ∑' z : V, I417Fresh.tau π v z = χ) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑ m ∈ Finset.Icc 1 q,
        ((q * I417MarkedTransversal.nonplaneMarkedCount p ℓ *
            I417FreshDepth.genCoeff q m : ℕ) : ℝ≥0∞) *
          (χ ^ (2 * p + 2 * q + 1 - (ℓ + m)) *
            I417Base.iterPow (I417Fresh.tau π) (ℓ + m) x y) := by
  classical
  -- the base (marked) side
  have hbase : ∀ w : V,
      I417Gen.jointPow π x p w ≤
        ∑ ℓ ∈ Finset.Icc 2 (p + 1),
          (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (χ ^ (2 * p + 1 - ℓ) * I417Base.iterPow (I417Fresh.tau π) ℓ x w) :=
    fun w => I417MarkedTransversal.jointPow_le_nonplane_markedDepth π hπ χ hχ x hp w
  -- the fresh side, in the summed form
  have hfresh : ∀ (j : Fin q) (w : V),
      (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
        ∑ m ∈ Finset.Icc 1 q,
          (I417FreshDepth.genCoeff q m : ℝ≥0∞) *
            (χ ^ (2 * q - m) * I417Base.iterPow (I417Fresh.tau π) m w y) :=
    fun j w => summedFreshProfile π hπ q hq χ hχ y w j
  refine (I417Gen.moment_gap_tsub_le_marked π x y (p := p) hq).trans ?_
  refine (ENNReal.tsum_le_tsum fun jw : Fin q × V =>
    mul_le_mul' (hbase jw.2) (hfresh jw.1 jw.2)).trans ?_
  -- sum over the marked terminal and vertex
  rw [tsum_fin_snd q (fun w => (∑ ℓ ∈ Finset.Icc 2 (p + 1),
        (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * I417Base.iterPow (I417Fresh.tau π) ℓ x w)) *
      (∑ m ∈ Finset.Icc 1 q,
        (I417FreshDepth.genCoeff q m : ℝ≥0∞) *
          (χ ^ (2 * q - m) * I417Base.iterPow (I417Fresh.tau π) m w y)))]
  rw [tsum_base_mul_fresh]
  exact le_of_eq (mul_compCoeff q p q (fun ℓ => I417MarkedTransversal.nonplaneMarkedCount p ℓ)
    (fun m => I417FreshDepth.genCoeff q m)
    (fun ℓ m => χ ^ (2 * p + 2 * q + 1 - (ℓ + m)) *
      I417Base.iterPow (I417Fresh.tau π) (ℓ + m) x y))

end PercLib.CriticalLRP.I417SummedFresh
