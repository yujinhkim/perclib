/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The paper's quadratic spatial weight is not translation invariant

Companion to `HvolRootIndependence.lean`.  That file proves that the *volume*
expectation `E |K_x|` is root independent for a translation-invariant edge law
(`hvol_cardFun`) and that the *spatial* moment is root independent only when its
weight is translation invariant (`hspat_shift`), the exact covariance identity
being `spatFun_covariance`.

This file records the negative side of the second statement: the paper's weight
`q_u(z) = <z,u>^2` (`VolumeMoments/I58Remainder.lean`, Definition of `q`) is not
translation invariant for `u != 0`, so `hspat_shift` **cannot** be applied to
`S(K) = sum_{x in K} q_u(x)`.  There is therefore no root-independence of
`E S(K_y)`; what is available is the covariance identity, and this is exactly
why the source keeps `S(K)` attached to the cluster of the origin and only ever
translates the *volume* factor `|K_y|`.  (Elementary algebra on top of the proved
covariance identity gives
`E S(K_y) = E S(K_0) + 2 <y,u> E sum_{x in K_0} <x,u> + <y,u>^2 E|K_0|`;
that real-valued decomposition is *not* formalized here — only the algebraic fact
that the weight itself fails to be invariant.)

Model: canonical independent percolation; nothing here is an abstract weighted
model.  No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58Remainder
public import PercLib.CriticalLRP.Correlation.Hrest

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP
namespace Hvol

/-- `dot u (single coordinate)` is the corresponding coordinate of `u`. -/
theorem dot_basis (d : ℕ) (u : Fin d → ℝ) (i : Fin d) :
    I58.dot u (fun j : Fin d => (if j = i then (1 : ℤ) else 0)) = u i := by
  simp only [I58.dot, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ i (fun j => u j)]
  simp

/-- **The paper's quadratic weight is not translation invariant.**  For a nonzero
direction `u` there is a lattice translation `a` with `q_u(a) != q_u(0)`; hence
the invariance hypothesis `hq` of `Hvol.hspat_shift` fails for `q_u`, and
`E S(K_y)` is not root independent in general. -/
theorem q_not_shift_invariant {d : ℕ} (u : Fin d → ℝ) (hu : u ≠ 0) :
    ∃ a : I58.Site d, I58.q u (0 + a) ≠ I58.q u (0 : I58.Site d) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    have hzero : ∀ i, u i = 0 := by
      intro j
      by_contra hj
      exact h ⟨j, hj⟩
    exact hu (funext hzero)
  refine ⟨fun j => if j = i then (1 : ℤ) else 0, ?_⟩
  rw [zero_add, I58.q, I58.q, dot_basis d u i]
  have h0 : I58.dot u (0 : I58.Site d) = 0 := by simp [I58.dot]
  rw [h0, show (0 : ℝ) ^ 2 = 0 by norm_num]
  exact pow_ne_zero 2 hi

end Hvol
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Hvol.dot_basis
#print axioms PercLib.CriticalLRP.Hvol.q_not_shift_invariant
