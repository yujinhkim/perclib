/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The mass-transport principle for translation-invariant functions, in the form
used in the proof of Hutchcroft, *Critical long-range percolation I*, Lemma I.4.1:
equations (I.4.2) and (I.4.3), p. 34.

Nothing here is probabilistic: it is a reindexing statement for `tsum` over a
countable additive group (in the application `G = ℤ ^ d`).
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory

namespace PercLib.CriticalLRP.Analysis

variable {G : Type*} [AddCommGroup G] [Countable G]

/-- **Mass-transport principle, `k`-fold form** (paper (I.4.3)).
If `F : (Fin k → G) → ℝ≥0∞` is invariant under simultaneous translation, then the
sum of `F` over the tuples with `i`-th coordinate `0` does not depend on `i`. -/
theorem tsum_mass_transport {k : ℕ} (F : (Fin k → G) → ENNReal)
    (hF : ∀ (v : Fin k → G) (t : G), F (fun i => v i + t) = F v) (i j : Fin k) :
    (∑' v : {v : Fin k → G // v i = 0}, F v.1)
      = (∑' v : {v : Fin k → G // v j = 0}, F v.1) := by
  classical
  let e : {v : Fin k → G // v i = 0} ≃ {v : Fin k → G // v j = 0} :=
    { toFun := fun v => ⟨fun m => v.1 m - v.1 j, by simp⟩
      invFun := fun w => ⟨fun m => w.1 m - w.1 i, by simp⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext m
        simp only [Subtype.coe_mk]
        rw [v.2]
        abel
      right_inv := by
        intro w
        apply Subtype.ext
        funext m
        simp only [Subtype.coe_mk]
        rw [w.2]
        abel }
  have hstep : ∀ v : {v : Fin k → G // v i = 0}, F (e v).1 = F v.1 := by
    intro v
    have h := hF v.1 (-v.1 j)
    have hve : (e v).1 = fun m => v.1 m + (-v.1 j) := by
      funext m
      show v.1 m - v.1 j = v.1 m + (-v.1 j)
      abel
    rw [hve, h]
  calc (∑' v : {v : Fin k → G // v i = 0}, F v.1)
      = ∑' v : {v : Fin k → G // v i = 0}, F (e v).1 := by
        exact (tsum_congr hstep).symm
    _ = ∑' v : {v : Fin k → G // v j = 0}, F v.1 := Equiv.tsum_eq e (fun w => F w.1)

/-- **Mass-transport principle, two-point form** (paper (I.4.2)). -/
theorem tsum_mass_transport₂ (F : G → G → ENNReal)
    (hF : ∀ (x y : G) (t : G), F (x + t) (y + t) = F x y) :
    (∑' x : G, F 0 x) = ∑' x : G, F x 0 := by
  have h : ∀ x : G, F 0 x = F (-x) 0 := by
    intro x
    have := hF 0 x (-x)
    simpa using this.symm
  rw [show (∑' x : G, F 0 x) = ∑' x : G, F (-x) 0 from tsum_congr h]
  exact Equiv.tsum_eq (Equiv.neg G) (fun x => F x 0)

end PercLib.CriticalLRP.Analysis
