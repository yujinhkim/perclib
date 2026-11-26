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

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Four.Refined.Bound
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Main

/-!
# Definitions for the summed `q = 4` fresh-diagram evaluation

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text pp. 45--46).

Two definitions only, both new to this swarm:

* `armEquiv4` — for four distinct labels `a b c d : Fin 4`, the reindexing
  `(Fin 4 → V) ≃ V × V × V × V`, `g ↦ (g a, g b, g c, g d)`.  This is what turns the four-arm
  sum of the fresh event into the four independent arm sums of a diagram, and it is the `q = 4`
  analogue of `I417FreshThree.Refined.armEquiv`.  Retaining all four labels is exactly the
  "retaining outer 4 arm labels" requirement: the sum over `g : Fin 4 → V` is *not* collapsed to a
  sum over multisets, it is reindexed bijectively.

* `freshFourProfile` — the `q = 4` fresh-side polynomial in the normalisation of Lemma I.4.17,
  `6 χ⁴ T⁴ + 12 χ⁵ T³ + 15 χ⁶ T² + 15 χ⁷ T`, with `T^ℓ = iterPow (kernel π) ℓ w y`.  Every
  monomial carries `(8 - ℓ) + ℓ = 8 = 2q` two-point factors; the coefficients are the numbers of
  members of the accepted cover with `ℓ = 4, 3, 2, 1` (`Q4Eval.Branch`).

Definitions only in this file.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.show false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFour.Eval

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The four labelled arms as a tuple -/

/-- **The four-arm reindexing.**  For four *distinct* labels `a b c d : Fin 4`, evaluation at the
four coordinates is a bijection `(Fin 4 → V) ≃ V × V × V × V`.  The inverse puts the four values
back at the four labelled slots and is defined by a four-way `if`; the distinctness hypotheses make
the four cases exhaustive. -/
def armEquiv4 (a b c d : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : (Fin 4 → V) ≃ V × V × V × V where
  toFun g := (g a, g b, g c, g d)
  invFun p i := if i = a then p.1 else if i = b then p.2.1 else if i = c then p.2.2.1
    else p.2.2.2
  left_inv g := by
    funext i
    by_cases h1 : i = a
    · simp [h1]
    by_cases h2 : i = b
    · simp [h2, h1, hab.symm]
    by_cases h3 : i = c
    · simp [h3, h1, h2, hac.symm, hbc.symm]
    · have h4 : i = d := by
        have hi := i.isLt
        have ha := a.isLt
        have hb := b.isLt
        have hc := c.isLt
        have hd := d.isLt
        have h1' : i.val ≠ a.val := fun h => h1 (Fin.ext h)
        have h2' : i.val ≠ b.val := fun h => h2 (Fin.ext h)
        have h3' : i.val ≠ c.val := fun h => h3 (Fin.ext h)
        have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
        have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
        have had' : a.val ≠ d.val := fun h => had (Fin.ext h)
        have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
        have hbd' : b.val ≠ d.val := fun h => hbd (Fin.ext h)
        have hcd' : c.val ≠ d.val := fun h => hcd (Fin.ext h)
        exact Fin.ext (by omega)
      simp [h4, h1, h2, h3, had.symm, hbd.symm, hcd.symm]
  right_inv p := by
    have e1 : (if a = a then p.1 else if a = b then p.2.1 else if a = c then p.2.2.1
        else p.2.2.2) = p.1 := by simp
    have e2 : (if b = a then p.1 else if b = b then p.2.1 else if b = c then p.2.2.1
        else p.2.2.2) = p.2.1 := by simp [hab.symm]
    have e3 : (if c = a then p.1 else if c = b then p.2.1 else if c = c then p.2.2.1
        else p.2.2.2) = p.2.2.1 := by simp [hac.symm, hbc.symm]
    have e4 : (if d = a then p.1 else if d = b then p.2.1 else if d = c then p.2.2.1
        else p.2.2.2) = p.2.2.2 := by simp [had.symm, hbd.symm, hcd.symm]
    show ((if a = a then p.1 else if a = b then p.2.1 else if a = c then p.2.2.1
        else p.2.2.2), (if b = a then p.1 else if b = b then p.2.1 else if b = c then p.2.2.1
        else p.2.2.2), (if c = a then p.1 else if c = b then p.2.1 else if c = c then p.2.2.1
        else p.2.2.2), (if d = a then p.1 else if d = b then p.2.1 else if d = c then p.2.2.1
        else p.2.2.2)) = p
    rw [e1, e2, e3, e4]

/-! ## The `q = 4` fresh-side polynomial -/

/-- **The `q = 4` fresh-side polynomial** in the normalisation of Lemma I.4.17:
`6 χ⁴ T⁴ + 12 χ⁵ T³ + 15 χ⁶ T² + 15 χ⁷ T(w,y)`.  Each monomial carries `2q = 8` two-point
factors, split as `(8 - ℓ) + ℓ` with `T`-power `ℓ ∈ [1, 4]` (the printed range `3 ≤ ℓ ≤ p+q+1`
after composition with the `2p + 1`-edge marked side, see `Q4Eval.Summed`); the coefficients
`6, 12, 15, 15` are the cardinalities `#{members of the accepted cover with that ℓ}`. -/
noncomputable def freshFourProfile (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (y w : V) : ℝ≥0∞ :=
  6 * (χ ^ 4 * iterPow (kernel π) 4 w y) + 12 * (χ ^ 5 * iterPow (kernel π) 3 w y) +
    15 * (χ ^ 6 * iterPow (kernel π) 2 w y) + 15 * (χ ^ 7 * iterPow (kernel π) 1 w y)

end PercLib.CriticalLRP.I417FreshFour.Eval
