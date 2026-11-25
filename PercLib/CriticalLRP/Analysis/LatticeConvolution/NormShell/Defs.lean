module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.BallShell
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.TailShell
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.LatticeGeometry.Cell.Normalization

/-!
# Constants for the arbitrary normalized-norm ball/tail shells

Definition layer only: lower/upper norm-comparison constants, the logarithmic comparison
constants and the counting constant used by the transferred shell estimates.  The
specification lemmas are in `NormShell.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

open PercLib.CriticalLRP.Orchestration

variable {d : ℕ}

/-- The **lower norm-comparison constant** of a normalized source norm: the supremum of the
numbers `r` such that `r ‖v‖_∞ ≤ S.ρ v` for every `v : Fin d → ℝ`.

For `d ≥ 1` this is a strictly positive real number with `srcLowerConst S * ‖v‖ ≤ S.ρ v`,
proved in `NormShell.lean` from `S.ρ_add_le`, `S.ρ_smul`, `S.ρ_pos` and `S.ρ_continuous`
(finite-dimensional norm equivalence). -/
noncomputable def srcLowerConst (S : SourceNormData d) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ ∀ v : Fin d → ℝ, r * ‖v‖ ≤ S.ρ v}

/-- The sum of the `S.ρ`-lengths of the standard basis vectors of `Fin d → ℝ`.  It is an
explicit upper norm-comparison constant: `S.ρ v ≤ srcBasisConst S * ‖v‖` for every real
vector `v`, by the triangle inequality and absolute homogeneity alone. -/
noncomputable def srcBasisConst (S : SourceNormData d) : ℝ :=
  ∑ i : Fin d, S.ρ (Pi.single i (1 : ℝ))

/-- The **upper norm-comparison constant**: `srcBasisConst S` clamped below at `1`. -/
noncomputable def srcUpperConst (S : SourceNormData d) : ℝ := max 1 (srcBasisConst S)

/-- The lower comparison constant clamped into `(0, 1]`.  Clamping at `1` is what makes the
weight comparison `Wt e c (S.ρ (toVec y)) ≤ C * Wt e c ‖y‖_∞` come out with a constant
`≥ 1`. -/
noncomputable def srcLowerUnit (S : SourceNormData d) : ℝ := min (srcLowerConst S) 1

/-- The cardinality constant of the lattice ball count in the `S.ρ`-radius:
`#{y : S.ρ (toVec y) ≤ r} ≤ srcCountConst S * (1 + r)^d`. -/
noncomputable def srcCountConst (S : SourceNormData d) : ℝ :=
  (3 / srcLowerUnit S + 3) ^ (d : ℝ)

/-- The logarithmic comparison constant between `log (2 + S.ρ (toVec y))` and
`log (2 + ‖y‖_∞)`: `log (2 + ‖y‖_∞) ≤ srcLogConst S * log (2 + S.ρ (toVec y))`. -/
noncomputable def srcLogConst (S : SourceNormData d) : ℝ :=
  1 + Real.log (2 + 1 / srcLowerUnit S) / Real.log 2

/-- The logarithmic comparison constant between `log (2 + S₀)` and `log (2 + S₀ / C)` for
`C = srcUpperConst S ≥ 1`: `log (2 + S₀) ≤ srcLogConstUpper S * log (2 + S₀ / C)`. -/
noncomputable def srcLogConstUpper (S : SourceNormData d) : ℝ :=
  1 + Real.log (2 + srcUpperConst S) / Real.log 2

/-- The full constant of the transferred weighted tail-shell estimate (`γ > 0` case),
before the final rescaling of `S₀`. -/
noncomputable def srcTailConst (S : SourceNormData d) (γ c : ℝ) : ℝ :=
  srcUpperConst S ^ γ * srcLogConstUpper S ^ c

/-- The full constant of the transferred pure-logarithmic tail-shell estimate (the `γ = 0`,
`c > 1` case, where the exponent drops to `c - 1`). -/
noncomputable def srcTailConstPureLog (S : SourceNormData d) (c : ℝ) : ℝ :=
  srcLogConstUpper S ^ (c - 1)

end CriticalLRPConv
