/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Case 3 (`(∇)`-triangle condition) of the decorrelation estimate of Proposition I.4.20:
definitions.  Independent Ultramath reconstruction; not integrated into production.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main

/-!
# Definitions for Case 3 of Proposition I.4.20 (the triangle condition)

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1.  The relevant places in `paper.txt` are

* Lemma I.4.17 (lines 2454--2515), the upper tree expansion
  `E|K|^a E|K|^b - E[|K_x|^a|K_y|^b 1(x ↮ y)]
     ≤ Σ_{j=3}^{a+b+1} C_{a,b,j} T^j(x,y) (E|K|)^{2(a+b)+1-j}`;
* Lemma I.4.18 (lines 2517--2546), the polygon estimate
  `sup_x T^j(0,x) ≤ C (∇_{r^c} + r^{-c}) (E|K|)^{j-3}` for `j ≥ 3`;
* Case 3 of the proof of Proposition I.4.20 (lines 2883--2887), where the two are
  combined into
  `E|K|^{ℓ+1}E|K|^{p-ℓ} - (1/|B_r|) E[|K|^{ℓ+1}Σ_{y∈B_r}1(y∉K)|K_y|^{p-ℓ}]
     ⪯_p (∇_{r^c}+r^{-c})(E|K|)^{2p} = o((E|K|²/E|K|)^{p-1}(E|K|)²)`.

Nothing here is an analytic input: the file records the *quantities* of that
display on the canonical independent-edge law `edgeMeasure π` of §I.1.2, exactly as
`I420Case1.Defs` records the Case 1 quantities.  The two source lemmas are carried
as the structures `HasTreeExpansion` and `HasPolygonBound`; every consequence drawn
from them is proved in `I420Case3.Polygon` and `I420Case3.Main`.

## Layout

* `pairFactor`, `pairExcl` are the two sides of the pair bound of Lemma I.4.17 at a
  single pair `(o,y)`; their `y`-sums are `I420Case1.prodFactor`, `mixedExcl`.
* `treePoly` is the right-hand side of the expansion: a finite sum over the path
  lengths `3 ≤ j ≤ p+2`, weighted by the `T`-powers `poly`.
* `coeffSum` is the total coefficient `Σ_{j=3}^{p+2} C_j` of that expansion.
* `discR` is the averaged discrepancy
  `|B|^{-1}(prodFactor - mixedExcl)` in `ℝ`, the left-hand side of Case 3;
  `biasTarget` is the target `(E|K|²/E|K|)^{p-1}(E|K|)²` of (I.4.21).
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-! ## The pair-level quantities of Lemma I.4.17 -/

/-- The **pair product factor** `E|K_o|^a · E|K_y|^b` of Lemma I.4.17 at the pair
`(o,y)`; it is the `y`-summand of `I420Case1.prodFactor`. -/
noncomputable def pairFactor (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) : ℝ≥0∞ :=
  I420Case1.powMomentAt π a o * I420Case1.powMomentAt π b y

/-- The **pair excluded expectation** `E[1(o ↮ y)|K_o|^a|K_y|^b]` of Lemma I.4.17 at
the pair `(o,y)`; it is the `y`-summand of `I420Case1.mixedExcl`. -/
noncomputable def pairExcl (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      (clusterVol ω o ^ a * clusterVol ω y ^ b) ∂(edgeMeasure π)

/-- The `y`-sum of `pairFactor` is `I420Case1.prodFactor`. -/
theorem sum_pairFactor (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) (B : Finset V) :
    ∑ y ∈ B, pairFactor π o y a b = I420Case1.prodFactor π o a b B := rfl

/-- The `y`-sum of `pairExcl` is `I420Case1.mixedExcl`. -/
theorem sum_pairExcl {π : Sym2 V → unitInterval} (o : V) (a b : ℕ) (B : Finset V) :
    ∑ y ∈ B, pairExcl π o y a b = I420Case1.mixedExcl π o a b B :=
  (I420Case1.mixedExcl_eq_sum_lintegral π o a b B).symm

/-! ## The tree expansion of Lemma I.4.17 -/

/-- The **right-hand side of the tree expansion** of Lemma I.4.17 at the pair
`(o,y)`: `Σ_{j=3}^{p+2} C_j T^j(o,y) (E|K|)^{2p+3-j}`, with `p = a+b-1`, the
`T`-powers `poly` and the universal coefficients `C` of the source. -/
noncomputable def treePoly (poly : V → ℕ → ℝ≥0∞) (C : ℕ → ℝ) (M : ℝ≥0∞) (p : ℕ)
    (y : V) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Icc 3 (p + 2), ENNReal.ofReal (C j) * poly y j * M ^ (2 * p + 3 - j)

/-- **Lemma I.4.17 as an explicit source input**, in additive form: for every
`y ∈ B` the pair product factor is at most the pair excluded expectation plus the
tree expansion.  The paper proves this for `a = ℓ+1`, `b = p-ℓ`, `p = a+b-1`,
`M = E|K|`, with integers `C = C_{a,b,j}` counting the tree diagrams whose `x`--`y`
path has length `j ∈ [3, a+b+1]`.

The additive (rather than subtractive) form is the one the source's proof produces;
the non-negativity of the discrepancy is the separate BK estimate
`pairExcl ≤ pairFactor` (`I420Case1.hrest_pow_le`). -/
structure HasTreeExpansion (π : Sym2 V → unitInterval) (o : V) (B : Finset V)
    (a b p : ℕ) (poly : V → ℕ → ℝ≥0∞) (C : ℕ → ℝ) : Prop where
  /-- The expansion holds on the pairs of `B`. -/
  expansion : ∀ y ∈ B, pairFactor π o y a b ≤
    pairExcl π o y a b + treePoly poly C (I420Case1.powMomentAt π 1 o) p y

/-- **Lemma I.4.18 as an explicit source input**: the polygon powers `T^j` are
uniformly bounded by `(∇_{r^c}+r^{-c})(E|K|)^{j-3}` for `j ≥ 3`, `Bpoly` being the
factor `∇_{r^c}+r^{-c}` (lines 2519--2523). -/
structure HasPolygonBound (π : Sym2 V → unitInterval) (o : V) (B : Finset V) (p : ℕ)
    (poly : V → ℕ → ℝ≥0∞) (Bpoly : ℝ) : Prop where
  /-- `∇_{r^c}+r^{-c}` is non-negative. -/
  nonneg : 0 ≤ Bpoly
  /-- The polygon bound, uniformly in `y ∈ B` (the source's `sup_x T^j(0,x)`). -/
  bound : ∀ y ∈ B, ∀ j ∈ Finset.Icc 3 (p + 2),
    poly y j ≤ ENNReal.ofReal Bpoly * I420Case1.powMomentAt π 1 o ^ (j - 3)

/-- The total coefficient `Σ_{j=3}^{p+2} C_j` of the tree expansion. -/
noncomputable def coeffSum (C : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 3 (p + 2), C j

/-! ## The discrepancy and the target of (I.4.21) -/

/-- The **averaged discrepancy**
`|B|^{-1}(|B| E|K|^a E|K|^b - A_ℓ(r))` of Case 3, in `ℝ`, for the pair of indices
`(a,b)`.  This is the left-hand side of the Case 3 display. -/
noncomputable def discR (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) (B : Finset V) : ℝ :=
  ((I420Case1.prodFactor π o a b B).toReal - (I420Case1.mixedExcl π o a b B).toReal) /
    (B.card : ℝ)

/-- The **normalized target of (I.4.21)**, `(E|K|²/E|K|)^{p-1}(E|K|)²`: the
right-hand side of (I.4.21) after removing the common factor `|B_r|`. -/
noncomputable def biasTarget (m1 m2 : ℝ) (p : ℕ) : ℝ :=
  (m2 / m1) ^ (p - 1) * m1 ^ 2

/-- `biasTarget` in the paper's exponent notation, with the real exponent
`(p : ℝ) - 1`; the two agree for `p ≥ 1` by `Real.rpow_natCast`. -/
theorem biasTarget_eq_rpow (m1 m2 : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    biasTarget m1 m2 p = (m2 / m1) ^ ((p : ℝ) - 1) * m1 ^ 2 := by
  unfold biasTarget
  rw [← Real.rpow_natCast (m2 / m1) (p - 1), Nat.cast_sub hp, Nat.cast_one]

/-- The **moment family** of a family of laws: `mom m r = E_{β,r}|K|^m`. -/
noncomputable def momOf (π : ℝ → Sym2 V → unitInterval) (o : V) (m : ℕ) (r : ℝ) : ℝ :=
  I420Case1.momR (π r) m o

/-- The **ball cardinality** `|B_r|` of a family of balls, as a real number. -/
noncomputable def ballCard (B : ℝ → Finset V) (r : ℝ) : ℝ := ((B r).card : ℝ)

end I420Case3

end PercLib.CriticalLRP
