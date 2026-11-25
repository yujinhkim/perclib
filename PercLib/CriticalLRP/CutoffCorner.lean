/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The corner of the cut-off kernel at `r = ‖x − y‖`.

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Definition I.1.5
and Lemma I.4.1.  The cut-off profile `J_r(s) = ∫_s^r |J'|` (for `s ≤ r`, and `0`
for `s > r`) is not differentiable at `r = s`: its left derivative is `0` while its
right derivative is `|J'(s)|`.  Consequently the two-sided derivative in Lemma
I.4.1 does not exist at `r` equal to an edge length of the lattice, and the phrase
"for every `r > 0`" in the paper has to be read as "for every `r` outside the
locally finite set of edge lengths" (equivalently, almost everywhere); this is what
the paper's use of the identity as a differential equation requires.

This file makes that remark precise; the positive results (`hasDerivAt_cutoffProfile`
for `s < r`, `hasDerivAt_cutoffEdgeProbability`) are in `KernelGeometry`.
-/
module

public import PercLib.CriticalLRP.KernelGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Set

namespace PercLib.CriticalLRP.FiniteVolume

/-- The cut-off profile is identically zero to the *left* of `r = s`, so its left
derivative at `s` vanishes. -/
theorem hasDerivWithinAt_cutoffProfile_Iic {K : ℝ → ℝ} {s : ℝ} :
    HasDerivWithinAt (fun r' => cutoffProfile K r' s) 0 (Iic s) s := by
  refine (hasDerivWithinAt_const (x := s) (s := Iic s) (c := (0 : ℝ))).congr ?_ ?_
  · intro r' hr'
    rcases lt_or_eq_of_le (show r' ≤ s from hr') with h | h
    · rw [cutoffProfile, ite_eq_right (not_le.mpr h)]
    · subst h
      rw [cutoffProfile, ite_eq_left le_rfl, sub_self]
  · rw [cutoffProfile, ite_eq_left le_rfl, sub_self]

/-- For `r > s` the cut-off profile is `K s − K r`, so its right derivative at
`s` is `−K'(s) = |J'(s)|` when `K' = −|J'|`. -/
theorem hasDerivWithinAt_cutoffProfile_Ioi {K : ℝ → ℝ} {K' s : ℝ}
    (hK : HasDerivAt K (-K') s) :
    HasDerivWithinAt (fun r' => cutoffProfile K r' s) K' (Ioi s) s := by
  have hder : HasDerivAt (fun r' => K s - K r') K' s := by
    have := hK.const_sub (K s)
    simpa using this
  refine hder.hasDerivWithinAt.congr ?_ ?_
  · intro r' hr'
    rw [cutoffProfile, ite_eq_left (le_of_lt hr')]
  · rw [cutoffProfile, ite_eq_left le_rfl, sub_self]

/-- **The cut-off profile has a genuine corner at `r = s`**: the two-sided
derivative does not exist when `K'(s) ≠ 0`. -/
theorem not_hasDerivAt_cutoffProfile {K : ℝ → ℝ} {K' s L : ℝ}
    (hK : HasDerivAt K (-K') s) (hK' : K' ≠ 0) :
    ¬ HasDerivAt (fun r' => cutoffProfile K r' s) L s := by
  intro h
  have hleft : HasDerivWithinAt (fun r' => cutoffProfile K r' s) L (Iic s) s :=
    h.hasDerivWithinAt
  have hleft0 : HasDerivWithinAt (fun r' => cutoffProfile K r' s) 0 (Iic s) s :=
    hasDerivWithinAt_cutoffProfile_Iic
  have e1 : derivWithin (fun r' => cutoffProfile K r' s) (Iic s) s = L :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic s)
  have e0 : derivWithin (fun r' => cutoffProfile K r' s) (Iic s) s = 0 :=
    hleft0.derivWithin (uniqueDiffWithinAt_Iic s)
  have hL : L = 0 := by rw [← e1, e0]
  subst hL
  have hright : HasDerivWithinAt (fun r' => cutoffProfile K r' s) K' (Ioi s) s :=
    hasDerivWithinAt_cutoffProfile_Ioi hK
  have hright0 : HasDerivWithinAt (fun r' => cutoffProfile K r' s) 0 (Ioi s) s :=
    h.hasDerivWithinAt
  have e2 : derivWithin (fun r' => cutoffProfile K r' s) (Ioi s) s = K' :=
    hright.derivWithin (uniqueDiffWithinAt_Ioi s)
  have e3 : derivWithin (fun r' => cutoffProfile K r' s) (Ioi s) s = 0 :=
    hright0.derivWithin (uniqueDiffWithinAt_Ioi s)
  exact hK' (by rw [← e2, e3])

/-- The open probability of an edge of length `s` under the cut-off kernel also has
a genuine corner at `r = s`: it is constant (`0`) on `r ≤ s` and increases with
right derivative `β|J'(s)|` at `s`. -/
theorem hasDerivWithinAt_cutoffEdgeProbability_Iic {K : ℝ → ℝ} {s β : ℝ} :
    HasDerivWithinAt (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      0 (Iic s) s := by
  refine (hasDerivWithinAt_const (x := s) (s := Iic s) (c := (0 : ℝ))).congr ?_ ?_
  · intro r' hr'
    rcases lt_or_eq_of_le (show r' ≤ s from hr') with h | h
    · rw [cutoffProfile, ite_eq_right (not_le.mpr h), longRangeEdgeProbability_zero_right]
    · subst h
      rw [cutoffProfile, ite_eq_left le_rfl, sub_self, longRangeEdgeProbability_zero_right]
  · rw [cutoffProfile, ite_eq_left le_rfl, sub_self, longRangeEdgeProbability_zero_right]

theorem hasDerivWithinAt_cutoffEdgeProbability_Ioi {K : ℝ → ℝ} {K' s β : ℝ}
    (hK : HasDerivAt K (-K') s) :
    HasDerivWithinAt (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      (β * K') (Ioi s) s := by
  have hinner : HasDerivWithinAt (fun r' => cutoffProfile K r' s) K' (Ioi s) s :=
    hasDerivWithinAt_cutoffProfile_Ioi hK
  have h1 : HasDerivWithinAt (fun r' => β * cutoffProfile K r' s) (β * K') (Ioi s) s :=
    hinner.const_mul β
  have h2 : HasDerivWithinAt (fun r' => -(β * cutoffProfile K r' s)) (-(β * K'))
      (Ioi s) s := h1.neg
  have h3 : HasDerivWithinAt (fun r' => Real.exp (-(β * cutoffProfile K r' s)))
      (Real.exp (-(β * cutoffProfile K s s)) * (-(β * K'))) (Ioi s) s := h2.exp
  have h4 : HasDerivWithinAt
      (fun r' => 1 - Real.exp (-(β * cutoffProfile K r' s)))
      (0 - Real.exp (-(β * cutoffProfile K s s)) * (-(β * K'))) (Ioi s) s :=
    (hasDerivWithinAt_const (x := s) (s := Ioi s) (c := (1 : ℝ))).sub h3
  have hval : (0 : ℝ) - Real.exp (-(β * cutoffProfile K s s)) * (-(β * K')) = β * K' := by
    rw [cutoffProfile_of_le le_rfl, sub_self, mul_zero, neg_zero, Real.exp_zero]
    ring
  rw [hval] at h4
  have hfun : (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      = fun r' => 1 - Real.exp (-(β * cutoffProfile K r' s)) := rfl
  rw [hfun]
  exact h4

/-- **The cut-off edge probability has a genuine corner at an edge length.** -/
theorem not_hasDerivAt_cutoffEdgeProbability {K : ℝ → ℝ} {K' s β L : ℝ}
    (hK : HasDerivAt K (-K') s) (hβK' : β * K' ≠ 0) :
    ¬ HasDerivAt (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s)) L s := by
  intro h
  have hleft : HasDerivWithinAt
      (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s)) L (Iic s) s :=
    h.hasDerivWithinAt
  have hleft0 : HasDerivWithinAt
      (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s)) 0 (Iic s) s :=
    hasDerivWithinAt_cutoffEdgeProbability_Iic
  have e1 : derivWithin (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      (Iic s) s = L := hleft.derivWithin (uniqueDiffWithinAt_Iic s)
  have e0 : derivWithin (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      (Iic s) s = 0 := hleft0.derivWithin (uniqueDiffWithinAt_Iic s)
  have hL : L = 0 := by rw [← e1, e0]
  subst hL
  have hright : HasDerivWithinAt
      (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s)) (β * K') (Ioi s) s :=
    hasDerivWithinAt_cutoffEdgeProbability_Ioi hK
  have hright0 : HasDerivWithinAt
      (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s)) 0 (Ioi s) s :=
    h.hasDerivWithinAt
  have e2 : derivWithin (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      (Ioi s) s = β * K' := hright.derivWithin (uniqueDiffWithinAt_Ioi s)
  have e3 : derivWithin (fun r' => longRangeEdgeProbability β (cutoffProfile K r' s))
      (Ioi s) s = 0 := hright0.derivWithin (uniqueDiffWithinAt_Ioi s)
  exact hβK' (by rw [← e2, e3])

end PercLib.CriticalLRP.FiniteVolume
