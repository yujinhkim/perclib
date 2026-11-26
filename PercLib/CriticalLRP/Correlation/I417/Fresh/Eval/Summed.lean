/-
Independently rebuilt and integrated from `smwx9itnu/m1`. Production
integration revision `3163cff3d90175d69f2612903830a27bdf5c0ab6`.
The coordinator supplies the fully applied 48-term aggregation and its
moment composition; only the strict build and global axiom audit determine acceptance.
-/
/-
Independently built for swarm `smwx9itnu`, member `m1`, direction Q4-SUMMED-EVALUATION.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Branch
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Defs

/-!
# The summed `q = 4` fresh-copy factor of Lemma I.4.17

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text pp. 45--46).

The accepted `q = 4` event cover (`I417FreshFour.Refined.freshMark_subset_q4Shape`) and its BK bound
(`freshMark_measure_le_q4`) give, for every arm tuple `g`, selected arm `j` and ordering
`i1, i2, i3` of the other three labels,

  `P(freshMark y g j w) ≤ ∑_{k1,k2,k3} ∑_{z1,z2,z3} ∏_{8 legs} τ(leg)`,

a sum of `2 · 4 · 6 = 48` members of eight two-point factors each.  This file evaluates that sum and
sums it over the four-arm tuple:

* `Equiv.tsum_eq` along `armEquiv4 j i1 i2 i3` reindexes `∑' g : Fin 4 → V` to
  `∑' pa : V × V × V × V`; the four **arm labels are retained**, the sum is a bijective
  reindexing, not a collapse to multisets;
* `arms_inner` moves the arm tuple to the innermost position, where each of the four arms is an
  independent one-variable sum contributing `χ` (`tsum_arm_four_tuple`);
* `ev_<n>` (`Q4Eval.Branch`) evaluates each of the 48 members to `χ^(8-ℓ) T^ℓ`, with `ℓ` the length
  of the `y`--`w` path: each skeleton vertex off the path supplies exactly one `χ` and the path legs
  compose into `iterPow`;
* `tsum_fin2`, `tsum_fin2_bool`, `tsum_fin2_bool_bool` expand the three finite index sums, and the
  48 evaluated members recombine into `freshFourProfile`.

The `T`-power range of the result is `[1, 4]` (`ℓ = 4, 3, 2, 1` with coefficients `6, 12, 15, 15`),
each monomial has `(8 - ℓ) + ℓ = 8 = 2q` two-point factors, and there is no `T⁰` term and no power
above `4`, so after composition with the `2p + 1`-edge marked side the printed range
`3 ≤ ℓ₁ + ℓ₂ ≤ p + q + 1` and the normalisation `2p + 9` are attained.

Only the constant row sum `∑_z τ(v,z) = χ` and BK (`π e < 1`) are used; no moment, finiteness or
subcriticality hypothesis.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFour.Eval

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **The `q = 4` fresh-copy factor, summed over the four-arm tuple and evaluated.**  For the
selected arm `j : Fin 4` and any ordering `i1, i2, i3` of the other three labels,

  `∑_g P(freshMark y g j w) ≤ 6 χ⁴ T⁴ + 12 χ⁵ T³ + 15 χ⁶ T² + 15 χ⁷ T(w,y)`,

with `T^ℓ = iterPow (kernel π) ℓ w y`, each monomial carrying `2q = 8` two-point factors. -/
theorem tsum_q4_le_profile (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, ∑' z : V, tau π v z = χ)
    (j i1 i2 i3 : Fin 4) (h01 : j ≠ i1) (h02 : j ≠ i2) (h03 : j ≠ i3)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) :
    (∑' g : Fin 4 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshFourProfile π χ y w := by
  refine le_trans (ENNReal.tsum_le_tsum fun g => freshMark_measure_le_q4 π hπ y w g j i1 i2 i3) ?_
  have hre : (∑' g : Fin 4 → V,
        ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
          ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
            ∏ i, tau π
              (q4Legs k1 k2 k3 z1 z2 z3 y w (g j) (g i1) (g i2) (g i3) i).1
              (q4Legs k1 k2 k3 z1 z2 z3 y w (g j) (g i1) (g i2) (g i3) i).2) =
      (∑' pa : V × V × V × V,
        ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
          ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
            ∏ i, tau π
              (q4Legs k1 k2 k3 z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).1
              (q4Legs k1 k2 k3 z1 z2 z3 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2 i).2) :=
    Equiv.tsum_eq (armEquiv4 j i1 i2 i3 h01 h02 h03 h12 h13 h23)
      (fun p : V × V × V × V =>
        ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
          ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
            ∏ i, tau π
              (q4Legs k1 k2 k3 z1 z2 z3 y w p.1 p.2.1 p.2.2.1 p.2.2.2 i).1
              (q4Legs k1 k2 k3 z1 z2 z3 y w p.1 p.2.1 p.2.2.1 p.2.2.2 i).2)
  refine le_trans (le_of_eq hre) ?_
  rw [arms_inner]
  conv_lhs => simp only [tsum_fin2, tsum_fin2_bool, tsum_fin2_bool_bool]
  rw [ev_0 π y w χ hχ, ev_1 π y w χ hχ, ev_2 π y w χ hχ, ev_3 π y w χ hχ, ev_4 π y w χ hχ, ev_5 π y w χ hχ, ev_6 π y w χ hχ, ev_7 π y w χ hχ, ev_8 π y w χ hχ, ev_9 π y w χ hχ, ev_10 π y w χ hχ, ev_11 π y w χ hχ, ev_12 π y w χ hχ, ev_13 π y w χ hχ, ev_14 π y w χ hχ, ev_15 π y w χ hχ, ev_16 π y w χ hχ, ev_17 π y w χ hχ, ev_18 π y w χ hχ, ev_19 π y w χ hχ, ev_20 π y w χ hχ, ev_21 π y w χ hχ, ev_22 π y w χ hχ, ev_23 π y w χ hχ, ev_24 π y w χ hχ, ev_25 π y w χ hχ, ev_26 π y w χ hχ, ev_27 π y w χ hχ, ev_28 π y w χ hχ, ev_29 π y w χ hχ, ev_30 π y w χ hχ, ev_31 π y w χ hχ, ev_32 π y w χ hχ, ev_33 π y w χ hχ, ev_34 π y w χ hχ, ev_35 π y w χ hχ, ev_36 π y w χ hχ, ev_37 π y w χ hχ, ev_38 π y w χ hχ, ev_39 π y w χ hχ, ev_40 π y w χ hχ, ev_41 π y w χ hχ, ev_42 π y w χ hχ, ev_43 π y w χ hχ, ev_44 π y w χ hχ, ev_45 π y w χ hχ, ev_46 π y w χ hχ, ev_47 π y w χ hχ]
  rw [freshFourProfile]
  refine le_of_eq ?_
  ring

/-- **The `q = 4` fresh-copy factor for every selected arm `j : Fin 4`.** -/
theorem tsum_freshMark_le_profile (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (j : Fin 4) :
    (∑' g : Fin 4 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshFourProfile π χ y w := by
  fin_cases j
  · exact tsum_q4_le_profile π hπ y w χ hχ 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact tsum_q4_le_profile π hπ y w χ hχ 1 2 3 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact tsum_q4_le_profile π hπ y w χ hχ 2 3 0 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact tsum_q4_le_profile π hπ y w χ hχ 3 0 1 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

end PercLib.CriticalLRP.I417FreshFour.Eval
