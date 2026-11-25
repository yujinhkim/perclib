/- Integrated from independently rebuilt Ultramath work.
Production base 6b7eb1107b03297e4df33585eeac818682adb1d2.
Scratch source: repository-root .ultramath/smwwp7q3k/m2/.
-/

/-
# Audit: statement identity with the committed Lemma I.5.6 and axiom audit

The two theorems below state the *committed* statements of
`PercLib.CriticalLRP.Analysis.lemma_I_5_6_of_errors` and
`...lemma_I_5_6_log_of_errors` verbatim and prove them from the committed
theorems.  Since the proofs are direct applications of the committed theorems,
elaboration certifies that the statements written here are the committed ones
(up to binder names); `Driver.lean` proves the same statements from the
strictly weaker driver interface.  Hence the committed two-error statement is
recovered from the new interface, not restated.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_6_Obstruction

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.I56Driver

open PercLib.CriticalLRP.Analysis

/-- The committed statement of Lemma I.5.6 with both errors, proved from the
committed theorem: the type below is the committed type. -/
theorem committed_I_5_6_of_errors {f f' h δ₁ δ₂ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂)
    (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      ((¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
          atTop (𝓝 1)) ∧
      ((LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) :=
  lemma_I_5_6_of_errors ha hhm hhrv hpos hfpos hderiv hδ₁ hδ₂m hδ₂0 hode

/-- The committed logarithmic corollary of Lemma I.5.6, proved from the
committed theorem: the type below is the committed type. -/
theorem committed_I_5_6_log_of_errors {f f' h δ₁ δ₂ : ℝ → ℝ} {a A : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hhm : Measurable h)
    (hhrv : RegularlyVaryingAtTop h a) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂)
    (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) :=
  lemma_I_5_6_log_of_errors ha hA hhm hhrv hpos hfpos hderiv hδ₁ hδ₂m hδ₂0 hode hhA

/-- The committed statements are also provable from the driver interface. -/
theorem committed_I_5_6_of_errors_from_driver {f f' h δ₁ δ₂ : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂)
    (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      ((¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
          atTop (𝓝 1)) ∧
      ((LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) :=
  committed_I_5_6_of_errors ha hhm hhrv hpos hfpos hderiv hδ₁ hδ₂m hδ₂0 hode

/-- The committed logarithmic corollary is also provable from the driver
interface. -/
theorem committed_I_5_6_log_of_errors_from_driver {f f' h δ₁ δ₂ : ℝ → ℝ} {a A : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hhm : Measurable h)
    (hhrv : RegularlyVaryingAtTop h a) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂)
    (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) :=
  lemma_I_5_6_log_of_errors_of_driver ha hA hhm hhrv hpos hfpos hderiv hδ₁ hδ₂m hδ₂0 hode hhA

end PercLib.CriticalLRP.Analysis.I56Driver

/-! Axiom audit for the second-driver interface. -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_of_two_drivers
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_log_of_two_drivers
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_of_driver
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_log_of_driver
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_of_errors_of_driver
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_log_of_errors_of_driver
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.committed_I_5_6_of_errors
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.committed_I_5_6_log_of_errors
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_relaxed_false
