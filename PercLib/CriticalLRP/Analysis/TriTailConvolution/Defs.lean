/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Profiles and convolutions for the open-triangle computation

Definitions for the exact Gram/autocorrelation computation in
`TriTailConvolution.Main`, integrated from accepted Ultramath `smwyq4kak`,
member `m1`.  The real profile is converted to `ℝ≥0∞` explicitly; theorems in
`Main` carry the nonnegativity and summability needed for that conversion.
-/
module

public import PercLib.CriticalLRP.Analysis.TriTailNormalization.Defs

/-! # Definitions for the convolution computation -/

@[expose] public section

open scoped ENNReal

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ}

/-- A real profile, read as an `ℝ≥0∞`-valued function.  This is the shape in which the lattice
convolution algebra (`conv`, `refl`, `conv_assoc`, `conv_comm`) is stated. -/
noncomputable def ofRealFn (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (f z)

/-- **The triple lattice convolution** `f * f * f`, as a real number:
`(f * f * f) x = ∑_p (∑_q f q · f (p - q)) · f (x - p)`.  `Main` proves summability of the inner
sums from summability of `f`; the definition itself is a total (possibly divergent) `tsum`. -/
noncomputable def tripleConv (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ :=
  fun x => ∑' p, (∑' q, f q * f (p - q)) * f (x - p)

/-- The autocorrelation kernel of a profile, as an `ℝ≥0∞`-valued function of the *difference*:
`Γ_f(u,v) = (f * f∨)(u - v)`. -/
noncomputable def gramProfile (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ≥0∞ :=
  conv (ofRealFn f) (refl (ofRealFn f))

end PercLib.CriticalLRP.TriTail
