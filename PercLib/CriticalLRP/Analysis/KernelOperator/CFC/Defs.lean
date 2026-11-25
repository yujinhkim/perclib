/-
# Square roots via CFC and the real structure on `ℓ²`

Accepted from swarm `smwtvrwnn` member `m7`, direction D6B.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
The nonnegative square root of a cube in a unital C⋆-algebra, and the canonical embedding of
real-valued into complex-valued `ℓ²` functions.  Positivity and complex-extension proofs are in the
consumer module rather than hidden in these definitions.
-/

@[expose] public section
noncomputable section

open scoped NNReal InnerProduct InnerProductSpace ComplexConjugate ComplexOrder ENNReal lp

namespace CFC

section Abstract

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive square root of `B ^ 3`, i.e. `B ^ (3/2)`.  Defined for every element `B` of a
unital C⋆-algebra through the non-unital continuous functional calculus (`CFC.sqrt`). -/
noncomputable def sqrtCube (B : A) : A := sqrt (B ^ 3)

end Abstract

end CFC

namespace Realification

section L2

variable {V : Type*}

/-- Real-valued `ℓ²` functions, regarded as complex-valued ones. -/
def ofRealLp (f : lp (fun _ : V => ℝ) 2) : lp (fun _ : V => ℂ) 2 :=
  ⟨fun v => ((f v : ℝ) : ℂ), by
    refine memℓp_gen ?_
    have hf : Summable fun v => ‖f v‖ ^ (2 : ℝ≥0∞).toReal :=
      (lp.memℓp f).summable (by norm_num)
    simpa only [Complex.norm_real] using hf⟩

end L2

end Realification
