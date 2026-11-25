/-
Consistency cross-check between the two signed ODE lemmas of the paper.

`Analysis.lemma_I_5_26_signed_ode` (the formalized Lemma I.5.26) takes the
two-term hypothesis `(r f' - a f)/h → A` and concludes `f/h → A/(b-a)`.
`I421Signed.tendsto_two_term_error_of_driving_ode` shows that the signed
Lemma I.4.21 hypothesis `f' ~ (a f + h)/r` produces exactly that two-term limit
with `A = 1`; instantiating I.5.26 with it returns the same conclusion
`f/h → 1/(b-a)` that the signed Lemma I.4.21 gives directly.  So the two
independently formalized signed ODE lemmas agree at `A = 1`.

This is a cross-check, not a new theorem: both sides are already proved.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21_Signed.I421Signed
public import PercLib.CriticalLRP.Analysis.Lemma_I_5_26

@[expose] public section

open Filter
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.I421Signed

/-- Lemma I.5.26 applied to the two-term error forced by the signed
Lemma I.4.21, giving `f/h → 1/(b-a)`. -/
theorem lemma_I_5_26_signed_ode_via_I_4_21 {f f' h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (1 / (b - a))) :=
  lemma_I_5_26_signed_ode D ha hab hderiv
    (tendsto_two_term_error_of_driving_ode D ha hab hderiv hasym)

end PercLib.CriticalLRP.Analysis.I421Signed
