/-
Scratch deliverable of swarm `smwu2am6k`, member `m1`, direction `d1`
("literal Case 2 open triangle, then its log tail").

Nothing here is a production file: the whole development lives under
`.ultramath/smwu2am6k/m1/` and imports the committed `PercLib` modules read-only.

# Definitions

Two objects are introduced.

* `litT J hJ β` is the *real-valued radial profile of the literal lattice two-point function*
  `z ↦ (τ_β(0,z)).toReal`.  It is the function to which the abstract Case 2 convolution
  assembly `Orchestration.HD.triple_convolution_case2` is applied, and the main theorem of
  `Main.lean` identifies the abstract iterated convolution of `litT` with the literal open
  triangle `TriTail.openTriangle J hJ β 0 ·`.
* `case2Const d C` is the explicit constant produced by that assembly: the second/triple
  convolution constant of `triple_convolution_case2` written as a single number.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Profile
public import PercLib.CriticalLRP.Analysis.TriTailLogTail
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell
public import PercLib.CriticalLRP.CountableProduct.Lattice

/-! # Literal Case 2: Defs

Definitions for the literal real two-point profile and Case 2 constants.
-/

set_option autoImplicit false


set_option linter.hashCommand false

@[expose] public section

open scoped ENNReal

namespace PercLib.CriticalLRP.Orchestration.HD

open CriticalLRPConv

variable {d : ℕ}

/-- The real radial profile of the literal two-point function at the origin,
`litT z = (τ_β(0,z)).toReal`.

The two-point function is a probability, so this coercion loses nothing: `ofReal_litT` recovers
the `ℝ≥0∞`-valued source object exactly. -/
noncomputable def litT (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (z : Fin d → ℤ) : ℝ :=
  (twoPointFunction J hJ β 0 z).toReal

/-- The explicit constant of the abstract Case 2 second/triple convolution
(`triple_convolution_case2`), collected into a single number so that the literal statements can
quote it without repeating the bracketing. -/
noncomputable def case2Const (d : ℕ) (C : ℝ) : ℝ :=
  (C * (2 : ℝ) ^ ((d : ℝ) - 2)) * (C * (2 : ℝ) ^ ((d : ℝ) - 2)) *
    convConst d 2 2 0 0 * (C * (2 : ℝ) ^ ((d : ℝ) - 2)) * convConst d 4 2 0 0

/-- The Case 2 constant carried by the *source-model* statement.

Two norm-comparison constants of `CriticalLRPConv` appear and are not disposable:

* `srcLowerUnit S` (in `(0,1]`) converts the HD input from the source norm `S.ρ` to the lattice
  sup-norm: `srcLowerUnit S * ‖z‖ ≤ S.ρ (toVec z)`, so with `d > 2` the negative power obeys
  `(S.ρ) ^ (-d+2) ≤ (srcLowerUnit S) ^ (-d+2) * ‖z‖ ^ (-d+2)`;
* `srcUpperConst S` (`≥ 1`) converts the *output* back to the source norm:
  `S.ρ ≤ srcUpperConst S ‖z‖`,
  so `‖z‖ ^ (-(d-6)) ≤ (srcUpperConst S) ^ (d-6) * (S.ρ) ^ (-(d-6))`.

Both directions are the correct ones — the first uses the *lower* comparison because the exponent is
negative, the second the *upper* one because the bound has to be re-expressed in the larger norm. -/
noncomputable def srcCase2Const (d : ℕ) (C : ℝ) (S : SourceNormData d) : ℝ :=
  case2Const d (C * srcLowerUnit S ^ (-((d : ℝ) - 2))) * srcUpperConst S ^ ((d : ℝ) - 6)

theorem litT_nonneg (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (z : Fin d → ℤ) : 0 ≤ litT J hJ β z :=
  ENNReal.toReal_nonneg

theorem litT_zero (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal) :
    litT J hJ β 0 = 1 := by
  rw [litT, twoPointFunction_self, ENNReal.toReal_one]

/-- The two-point function is a probability, so it is never `⊤`. -/
theorem twoPointFunction_ne_top (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : Fin d → ℤ) : twoPointFunction J hJ β x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (twoPointFunction_le_one J hJ β x y)

/-- `litT` recovers the source object: coerced back to `ℝ≥0∞` it *is* the two-point function. -/
theorem ofReal_litT (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (z : Fin d → ℤ) : ENNReal.ofReal (litT J hJ β z) = twoPointFunction J hJ β 0 z :=
  ENNReal.ofReal_toReal (twoPointFunction_ne_top J hJ β 0 z)

/-- The profile is a probability. -/
theorem litT_le_one (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (z : Fin d → ℤ) : litT J hJ β z ≤ 1 := by
  rw [litT]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (twoPointFunction_le_one J hJ β 0 z)

/-- The Case 2 constant is nonnegative (needed to move between `ℝ` and `ℝ≥0∞` bounds). -/
theorem case2Const_nonneg {C : ℝ} (hd : 6 < d) (hC : 1 ≤ C) : 0 ≤ case2Const d C := by
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) - 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hd4 : (2 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast (show 4 < d by omega)
  have h2 : 0 ≤ convConst d 2 2 0 0 :=
    SrcNormConv.convConst_nonneg (show 1 ≤ d by omega) (by norm_num) (by norm_num) hd4
      (by norm_num) (by norm_num)
  have h4 : 0 ≤ convConst d 4 2 0 0 :=
    SrcNormConv.convConst_nonneg (show 1 ≤ d by omega) (by norm_num) (by norm_num)
      (by exact_mod_cast hd) (by norm_num) (by norm_num)
  unfold case2Const
  positivity

end PercLib.CriticalLRP.Orchestration.HD

#print axioms PercLib.CriticalLRP.Orchestration.HD.litT_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.HD.litT_zero
#print axioms PercLib.CriticalLRP.Orchestration.HD.twoPointFunction_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.HD.ofReal_litT
#print axioms PercLib.CriticalLRP.Orchestration.HD.litT_le_one
#print axioms PercLib.CriticalLRP.Orchestration.HD.case2Const_nonneg
