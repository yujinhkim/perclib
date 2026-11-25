/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# One-sided corner derivatives of the normalized cut-off source law

Accepted from swarm `smwtvrwnn`, member `m8`, direction D1D.

`M.cutProb r e = 1 - exp (-(β_c J_r (e)))` with `J_r (s) = cutoffProfile K r s = K s - K r`
for `s ≤ r` and `0` for `r < s` (`FiniteVolume.cutoffProfile`, closed convention `s ≤ r`).
Consequently, at a radius `r` equal to an edge length `s`, the two-sided `r`-derivative of the
edge probability does not exist; it has a *left* derivative `0` and a *right* derivative
`β_c (-K'(r)) = β_c |K'(r)|` (`CutoffCorner.hasDerivWithinAt_cutoffEdgeProbability_*`).

This file lifts that corner structure to the actual model and to finite windows.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.CornerOneSided.Defs
public import PercLib.CriticalLRP.CutoffCorner
public import PercLib.CriticalLRP.CylinderRusso
public import PercLib.CriticalLRP.RussoFinite

/-!
One-sided derivatives of cutoff edge probabilities and finite-window expectations, including
exact corner jumps and a conditional left-endpoint cutoff-mass theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

@[simp] theorem cutEdgeDerivLeft_mk (r : ℝ) (x y : M.V) :
    M.cutEdgeDerivLeft r s(x, y) =
      (if x = y then 0 else
        (if M.S.dist x y < r then
          (M.betaCrit : ℝ) * (-(deriv M.K r)) *
            Real.exp (-((M.betaCrit : ℝ) *
              FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
         else 0)) := rfl

/-- **Exact left/right weight decomposition at every radius.**

The strict weight and the closed weight of a non-loop edge differ only when the edge length is
*exactly* the radius, and then the difference is the corner weight `β_c (-K'(r)) = β_c |K'(r)|`
(the `exp` factor being `exp 0 = 1`).  This is the per-edge "shell" decomposition: crossing the
radius `r` activates exactly the edges of length `r`. -/
theorem cutEdgeDeriv_sub_cutEdgeDerivLeft_mk (r : ℝ) (x y : M.V) :
    M.cutEdgeDeriv r s(x, y) - M.cutEdgeDerivLeft r s(x, y) =
      (if x = y then 0 else
        (if M.S.dist x y = r then (M.betaCrit : ℝ) * (-(deriv M.K r)) else 0)) := by
  rw [M.cutEdgeDeriv_mk, M.cutEdgeDerivLeft_mk]
  by_cases hxy : x = y
  · rw [ite_eq_left hxy, ite_eq_left hxy, sub_self, ite_eq_left hxy]
  · rw [ite_eq_right hxy, ite_eq_right hxy, ite_eq_right hxy]
    rcases lt_trichotomy (M.S.dist x y) r with hlt | heq | hgt
    · rw [ite_eq_left (le_of_lt hlt), ite_eq_left hlt, ite_eq_right (ne_of_lt hlt), sub_self]
    · have hprof : FiniteVolume.cutoffProfile M.K r (M.S.dist x y) = 0 := by
        rw [heq, FiniteVolume.cutoffProfile_of_le le_rfl, sub_self]
      rw [ite_eq_left heq.le, ite_eq_right (not_lt.mpr heq.ge), ite_eq_left heq, hprof,
        mul_zero, neg_zero, Real.exp_zero, mul_one, sub_zero]
    · rw [ite_eq_right (not_le.mpr hgt), ite_eq_right (not_lt.mpr hgt.le),
        ite_eq_right (ne_of_gt hgt), sub_self]

/-- The edge probability of a non-loop edge is the long-range edge probability of the cut-off
profile of the model's own distance. -/
theorem cutProb_coe_mk_of_ne {r : ℝ} {x y : M.V} (hxy : x ≠ y) :
    ((M.cutProb r s(x, y) : unitInterval) : ℝ)
      = longRangeEdgeProbability (M.betaCrit : ℝ)
          (FiniteVolume.cutoffProfile M.K r (M.S.dist x y)) := by
  rw [M.cutProb_coe_eq, M.cutKernel_mk, ite_eq_right hxy]
  rfl

/-- The edge probability of a loop edge vanishes identically. -/
theorem cutProb_coe_loop (r : ℝ) (x : M.V) :
    ((M.cutProb r s(x, x) : unitInterval) : ℝ) = 0 := by
  rw [M.cutProb_coe_eq, M.cutKernel_mk, ite_eq_left rfl]
  simp

/-- The left (strict) derivative of the actual source cut-off edge probability, at every radius.

At a radius `r` at which `M.K` is differentiable, the edge probability `r' ↦ q_{r'}(e)`,
restricted to `r' ≤ r`, has derivative `M.cutEdgeDerivLeft r e`.  Off the corner set this is the
two-sided weight `M.cutEdgeDeriv r e`. -/
theorem hasDerivWithinAt_cutProb_Iic {r : ℝ} (hKd : DifferentiableAt ℝ M.K r)
    (e : Sym2 M.V) :
    HasDerivWithinAt (fun r' => ((M.cutProb r' e : unitInterval) : ℝ))
      (M.cutEdgeDerivLeft r e) (Set.Iic r) r := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeDerivLeft_mk, ite_eq_left rfl,
        show (fun r' => ((M.cutProb r' s(x, x) : unitInterval) : ℝ)) = fun _ => (0 : ℝ) from
          funext fun r' => M.cutProb_coe_loop r' x]
      exact (hasDerivWithinAt_const (x := r) (s := Set.Iic r) (c := (0 : ℝ)))
    · rw [M.cutEdgeDerivLeft_mk, ite_eq_right hxy]
      rcases lt_trichotomy (M.S.dist x y) r with hlt | heq | hgt
      · have hw : (if M.S.dist x y < r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0)
            = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) :=
          ite_eq_left hlt
        rw [hw]
        have h := (FiniteVolume.hasDerivAt_cutoffEdgeProbability (K := M.K)
          (K' := -(deriv M.K r)) (r := r) (s := M.S.dist x y) hlt
          (by simpa using hKd.hasDerivAt) (β := (M.betaCrit : ℝ))).hasDerivWithinAt (s := Set.Iic r)
        exact h.congr (fun r' _ => M.cutProb_coe_mk_of_ne hxy)
          (M.cutProb_coe_mk_of_ne hxy)
      · have hw : (if M.S.dist x y < r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0) = 0 :=
          ite_eq_right (not_lt.mpr heq.ge)
        rw [hw]
        have hKd' : DifferentiableAt ℝ M.K (M.S.dist x y) := by
          rw [heq]; exact hKd
        have hcorner := FiniteVolume.hasDerivWithinAt_cutoffEdgeProbability_Iic (K := M.K)
          (s := M.S.dist x y) (β := (M.betaCrit : ℝ))
        rw [heq] at hcorner
        exact hcorner.congr (fun r' _ => by simpa [heq] using M.cutProb_coe_mk_of_ne hxy)
          (by simpa [heq] using M.cutProb_coe_mk_of_ne hxy)
      · have hw : (if M.S.dist x y < r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0) = 0 :=
          ite_eq_right (not_lt.mpr hgt.le)
        rw [hw]
        have h := (FiniteVolume.hasDerivAt_cutoffEdgeProbability_if (K := M.K)
          (K' := -(deriv M.K r)) (r := r) (s := M.S.dist x y) (ne_of_gt hgt)
          (by simpa using hKd.hasDerivAt) (β := (M.betaCrit : ℝ))).hasDerivWithinAt (s := Set.Iic r)
        rw [ite_eq_right (not_le.mpr hgt)] at h
        exact h.congr (fun r' _ => M.cutProb_coe_mk_of_ne hxy)
          (M.cutProb_coe_mk_of_ne hxy)

/-- The right (closed) derivative of the actual source cut-off edge probability, at every
radius.  At a corner radius `r = M.S.dist x y` this is the full corner weight
`β_c |K'(r)|`, larger than the left derivative `M.cutEdgeDerivLeft r e = 0`. -/
theorem hasDerivWithinAt_cutProb_Ici {r : ℝ} (hKd : DifferentiableAt ℝ M.K r)
    (e : Sym2 M.V) :
    HasDerivWithinAt (fun r' => ((M.cutProb r' e : unitInterval) : ℝ))
      (M.cutEdgeDeriv r e) (Set.Ici r) r := by
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeDeriv_mk, ite_eq_left rfl,
        show (fun r' => ((M.cutProb r' s(x, x) : unitInterval) : ℝ)) = fun _ => (0 : ℝ) from
          funext fun r' => M.cutProb_coe_loop r' x]
      exact (hasDerivWithinAt_const (x := r) (s := Set.Ici r) (c := (0 : ℝ)))
    · rw [M.cutEdgeDeriv_mk, ite_eq_right hxy]
      rcases lt_trichotomy (M.S.dist x y) r with hlt | heq | hgt
      · have hw : (if M.S.dist x y ≤ r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0)
            = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) :=
          ite_eq_left hlt.le
        rw [hw]
        have h := (FiniteVolume.hasDerivAt_cutoffEdgeProbability (K := M.K)
          (K' := -(deriv M.K r)) (r := r) (s := M.S.dist x y) hlt
          (by simpa using hKd.hasDerivAt) (β := (M.betaCrit : ℝ))).hasDerivWithinAt (s := Set.Ici r)
        exact h.congr (fun r' _ => M.cutProb_coe_mk_of_ne hxy)
          (M.cutProb_coe_mk_of_ne hxy)
      · have hprof : FiniteVolume.cutoffProfile M.K r (M.S.dist x y) = 0 := by
          rw [heq, FiniteVolume.cutoffProfile_of_le le_rfl, sub_self]
        have hw : (if M.S.dist x y ≤ r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0)
            = (M.betaCrit : ℝ) * (-(deriv M.K r)) := by
          rw [ite_eq_left heq.le, hprof, mul_zero, neg_zero, Real.exp_zero, mul_one]
        rw [hw]
        have hKd' : DifferentiableAt ℝ M.K (M.S.dist x y) := by
          rw [heq]; exact hKd
        have hcorner := FiniteVolume.hasDerivWithinAt_cutoffEdgeProbability_Ioi (K := M.K)
          (K' := -(deriv M.K (M.S.dist x y))) (s := M.S.dist x y) (β := (M.betaCrit : ℝ))
          (by simpa using hKd'.hasDerivAt)
        rw [heq] at hcorner
        exact (hcorner.congr (fun r' _ => by simpa [heq] using M.cutProb_coe_mk_of_ne hxy)
          (by simpa [heq] using M.cutProb_coe_mk_of_ne hxy)).Ici_of_Ioi
      · have hw : (if M.S.dist x y ≤ r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0) = 0 :=
          ite_eq_right (not_le.mpr hgt)
        rw [hw]
        have h := (FiniteVolume.hasDerivAt_cutoffEdgeProbability_if (K := M.K)
          (K' := -(deriv M.K r)) (r := r) (s := M.S.dist x y) (ne_of_gt hgt)
          (by simpa using hKd.hasDerivAt) (β := (M.betaCrit : ℝ))).hasDerivWithinAt (s := Set.Ici r)
        rw [ite_eq_right (not_le.mpr hgt)] at h
        exact h.congr (fun r' _ => M.cutProb_coe_mk_of_ne hxy)
          (M.cutProb_coe_mk_of_ne hxy)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## One-sided (finite-window) Russo identities

The finite-window Russo identity `hasDerivAt_integral_cutFun` is two-sided and therefore needs
an off-corner radius.  Here we prove the *one-sided* version: at every radius, and for every
choice of one-sided derivative weights of the edge probabilities, the window expectation has the
corresponding one-sided derivative.  The window is finite, so no moment or domination hypothesis
is needed.
-/

namespace PercLib.CriticalLRP.FiniteVolume

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
/-- One-sided derivative of one factor of the product law in the parameter `t`. -/
theorem hasDerivWithinAt_weightFactor (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ} {s : Set ℝ}
    (hP : ∀ e, HasDerivWithinAt (P e) (P' e) s t) (e : E) (c : Configuration E) :
    HasDerivWithinAt (fun t' => if e ∈ c then P e t' else 1 - P e t')
      (if e ∈ c then P' e else -P' e) s t := by
  by_cases h : e ∈ c
  · have hfun : (fun t' => if e ∈ c then P e t' else 1 - P e t') = P e := by
      funext t'; simp [h]
    have hder : (if e ∈ c then P' e else -P' e) = P' e := by simp [h]
    rw [hfun, hder]; exact hP e
  · have hfun : (fun t' => if e ∈ c then P e t' else 1 - P e t') = fun t' => 1 - P e t' := by
      funext t'; simp [h]
    have hder : (if e ∈ c then P' e else -P' e) = -P' e := by simp [h]
    rw [hfun, hder]; exact HasDerivWithinAt.const_sub (1 : ℝ) (hP e)

/-- One-sided derivative of the weight of a single configuration in the parameter `t`. -/
theorem hasDerivWithinAt_configurationLaw (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ} {s : Set ℝ}
    (hP : ∀ e, HasDerivWithinAt (P e) (P' e) s t) (c : Configuration E) :
    HasDerivWithinAt (fun t' => configurationLaw (fun e => P e t') c)
      (∑ e, sliceWeight (fun e => P e t) e c * (if e ∈ c then P' e else -P' e)) s t := by
  have h := HasDerivWithinAt.finsetProd (s := s) (x := t) (u := (univ : Finset E))
    (f := fun e t' => if e ∈ c then P e t' else 1 - P e t')
    (f' := fun e => if e ∈ c then P' e else -P' e)
    (fun i _ => hasDerivWithinAt_weightFactor P P' hP i c)
  convert h using 1
  · funext t'
    simp only [configurationLaw, Finset.prod_apply]
  · simp only [sliceWeight, smul_eq_mul]

/-- **One-sided Russo formula** (finite volume, expectation form). -/
theorem hasDerivWithinAt_expectation (P : E → ℝ → ℝ) (P' : E → ℝ) {t : ℝ} {s : Set ℝ}
    (hP : ∀ e, HasDerivWithinAt (P e) (P' e) s t) (X : Configuration E → ℝ) :
    HasDerivWithinAt (fun t' => expectation (fun e => P e t') X)
      (∑ e, P' e * pivotalMass (fun e => P e t) e X) s t := by
  classical
  set pt : E → ℝ := fun e => P e t with hpt
  have hterm : ∀ c : Configuration E,
      HasDerivWithinAt (fun t' => configurationLaw (fun e => P e t') c * X c)
        ((∑ e, sliceWeight pt e c * (if e ∈ c then P' e else -P' e)) * X c) s t :=
    fun c => (hasDerivWithinAt_configurationLaw P P' hP c).mul_const (X c)
  have hsum := HasDerivWithinAt.sum (u := (univ : Finset (Configuration E)))
    (fun c _ => hterm c)
  have hkey : ∀ e : E, ∑ c : Configuration E,
        sliceWeight pt e c * (if e ∈ c then P' e else -P' e) * X c
      = P' e * pivotalMass pt e X := by
    intro e
    rw [← sum_filter_add_sum_filter_not (s := (univ : Finset (Configuration E)))
      (p := fun c => e ∈ c)
      (f := fun c => sliceWeight pt e c * (if e ∈ c then P' e else -P' e) * X c)]
    have h1 : ∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => e ∈ c),
        sliceWeight pt e c * (if e ∈ c then P' e else -P' e) * X c
        = P' e * ∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => e ∈ c),
            sliceWeight pt e c * X c := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun c hc => ?_
      rw [mem_filter] at hc
      have hif : (if e ∈ c then P' e else -P' e) = P' e := by simp [hc.2]
      rw [hif]; ring
    have h2 : ∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => ¬ e ∈ c),
        sliceWeight pt e c * (if e ∈ c then P' e else -P' e) * X c
        = -(P' e * ∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => e ∉ c),
            sliceWeight pt e c * X c) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine sum_congr rfl fun c hc => ?_
      rw [mem_filter] at hc
      have hif : (if e ∈ c then P' e else -P' e) = -P' e := by simp [hc.2]
      rw [hif]; ring
    rw [h1, h2]
    have hstep : P' e * ∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => e ∈ c),
          sliceWeight pt e c * X c
        + -(P' e * ∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => e ∉ c),
          sliceWeight pt e c * X c)
        = P' e * ((∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => e ∈ c),
              sliceWeight pt e c * X c)
            - ∑ c ∈ (univ : Finset (Configuration E)).filter (fun c => e ∉ c),
              sliceWeight pt e c * X c) := by ring
    rw [hstep]
    congr 1
    rw [sum_filter_mem_eq e (fun c => sliceWeight pt e c * X c)]
    unfold pivotalMass
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun τ _ => by rw [sliceWeight_insert]; ring
  have hval : (∑ c : Configuration E,
        (∑ e, sliceWeight pt e c * (if e ∈ c then P' e else -P' e)) * X c)
      = ∑ e, P' e * pivotalMass pt e X := by
    calc ∑ c : Configuration E,
          (∑ e, sliceWeight pt e c * (if e ∈ c then P' e else -P' e)) * X c
        = ∑ c : Configuration E, ∑ e,
            (sliceWeight pt e c * (if e ∈ c then P' e else -P' e)) * X c := by
          simp only [Finset.sum_mul]
      _ = ∑ e, ∑ c : Configuration E,
            (sliceWeight pt e c * (if e ∈ c then P' e else -P' e)) * X c :=
          Finset.sum_comm
      _ = ∑ e, P' e * pivotalMass pt e X :=
          sum_congr rfl fun e _ => hkey e
  have hfun : (fun t' => expectation (fun e => P e t') X)
      = (∑ i : Configuration E, fun t' => configurationLaw (fun e => P e t') i * X i) := by
    funext t'
    simp only [expectation, Finset.sum_apply]
  rw [hfun, ← hval]
  exact hsum

end PercLib.CriticalLRP.FiniteVolume

namespace PercLib.CriticalLRP

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- One-sided Russo formula for cylinder observables on the countable model. -/
theorem hasDerivWithinAt_integral_edgeMeasure_cylinder
    (πt : ℝ → Sym2 V → unitInterval) (π' : Sym2 V → ℝ)
    (S : Finset (Sym2 V)) (g : (S → Prop) → ℝ) {t : ℝ} {u : Set ℝ}
    (hderiv : ∀ e : Sym2 V,
      HasDerivWithinAt (fun t' => ((πt t' e : unitInterval) : ℝ)) (π' e) u t) :
    HasDerivWithinAt (fun t' => ∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure (πt t')))
      (∑ e : S, π' e.1 *
        FiniteVolume.pivotalMass (fun e : S => ((πt t e : unitInterval) : ℝ)) e
          (fun c => g (fun i => i ∈ c))) u t := by
  classical
  have hcyl : ∀ t' : ℝ, (∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure (πt t')))
      = expectation (fun e : S => ((πt t' e : unitInterval) : ℝ))
          (fun c => g (fun i => i ∈ c)) :=
    fun t' => integral_edgeMeasure_cylinder (πt t') S g
  simp only [hcyl]
  exact FiniteVolume.hasDerivWithinAt_expectation
    (E := S) (P := fun e t' => ((πt t' e.1 : unitInterval) : ℝ))
    (P' := fun e => π' e.1) (t := t) (s := u) (fun e => hderiv e.1)
    (X := fun c => g (fun i => i ∈ c))

/-- **One-sided finite-window Russo derivative.** -/
theorem hasDerivWithinAt_integral_cutFun (πt : ℝ → Sym2 V → unitInterval) (π' : Sym2 V → ℝ)
    (S : Finset (Sym2 V)) (g : Config V → ℝ) {t : ℝ} {u : Set ℝ}
    (hderiv : ∀ e : Sym2 V, HasDerivWithinAt
      (fun t' => ((πt t' e : unitInterval) : ℝ)) (π' e) u t) :
    HasDerivWithinAt (fun t' => ∫ ω : Config V, cutFun S g ω ∂(edgeMeasure (πt t')))
      (∑ e : S, π' e.1 * pivotalFlux (edgeMeasure (πt t)) (cutFun S g) e.1) u t := by
  classical
  have hcyl := hasDerivWithinAt_integral_edgeMeasure_cylinder (V := V) πt π' S
    (fun y : S → Prop => g (restrConfig S y)) hderiv
  have hL : (fun t' => ∫ ω : Config V, cutFun S g ω ∂(edgeMeasure (πt t')))
      = fun t' => ∫ ω : Config V, (fun y : S → Prop => g (restrConfig S y)) (S.restrict ω)
          ∂(edgeMeasure (πt t')) := by
    funext t'
    exact integral_congr_ae (Eventually.of_forall fun ω => (cutFun_apply S g ω))
  rw [hL]
  refine hcyl.congr_deriv ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pivotalFlux_cutFun (πt t) S g e.2]

end PercLib.CriticalLRP

/-! ## One-sided finite-window Russo identities at the actual source model -/

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Left one-sided finite-window Russo identity.**

For every finite edge window `S`, every functional `g` and every radius `r` at which `M.K` is
differentiable, the window expectation `r' ↦ ∫ cutFun S g ∂(M.cutLaw r')`, restricted to
`r' ≤ r`, has derivative the finite pivotal sum with the *strict* edge weights
`M.cutEdgeDerivLeft r`.  There is no off-corner hypothesis: the corner is absorbed into the
strict weight. -/
theorem hasDerivWithinAt_integral_cutFun_cutLaw_Iic (S : Finset (Sym2 M.V))
    (g : Config M.V → ℝ) {r : ℝ} (hKd : DifferentiableAt ℝ M.K r) :
    HasDerivWithinAt (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r'))
      (∑ e ∈ S, M.cutEdgeDerivLeft r e * pivotalFlux (M.cutLaw r) (cutFun S g) e)
      (Set.Iic r) r := by
  have hgen := hasDerivWithinAt_integral_cutFun (V := M.V) (πt := M.cutProb)
    (π' := M.cutEdgeDerivLeft r) S g (t := r) (u := Set.Iic r)
    (fun e => M.hasDerivWithinAt_cutProb_Iic hKd e)
  have hfun : (fun r' => ∫ ω : Config M.V, cutFun S g ω ∂(edgeMeasure (M.cutProb r')))
      = fun r' => ∫ ω : Config M.V, cutFun S g ω ∂(M.cutLaw r') := by
    funext r'
    rw [M.cutLaw_eq_edgeMeasure]
  rw [hfun] at hgen
  refine hgen.congr_deriv ?_
  rw [← M.cutLaw_eq_edgeMeasure r,
    Finset.sum_coe_sort S (fun e => M.cutEdgeDerivLeft r e *
      pivotalFlux (M.cutLaw r) (cutFun S g) e)]

/-- **Right one-sided finite-window Russo identity**, with the closed edge weights
`M.cutEdgeDeriv r`.  At a corner radius the difference from the left identity is carried
entirely by the edges of length exactly `r`. -/
theorem hasDerivWithinAt_integral_cutFun_cutLaw_Ici (S : Finset (Sym2 M.V))
    (g : Config M.V → ℝ) {r : ℝ} (hKd : DifferentiableAt ℝ M.K r) :
    HasDerivWithinAt (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r'))
      (∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e)
      (Set.Ici r) r := by
  have hgen := hasDerivWithinAt_integral_cutFun (V := M.V) (πt := M.cutProb)
    (π' := M.cutEdgeDeriv r) S g (t := r) (u := Set.Ici r)
    (fun e => M.hasDerivWithinAt_cutProb_Ici hKd e)
  have hfun : (fun r' => ∫ ω : Config M.V, cutFun S g ω ∂(edgeMeasure (M.cutProb r')))
      = fun r' => ∫ ω : Config M.V, cutFun S g ω ∂(M.cutLaw r') := by
    funext r'
    rw [M.cutLaw_eq_edgeMeasure]
  rw [hfun] at hgen
  refine hgen.congr_deriv ?_
  rw [← M.cutLaw_eq_edgeMeasure r,
    Finset.sum_coe_sort S (fun e => M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (cutFun S g) e)]

/-- **The corner flux is the jump of the finite-window Russo derivative.**

The right derivative minus the left derivative is the sum of the per-edge weight jumps; by
`M.cutEdgeDeriv_sub_cutEdgeDerivLeft_mk` each jump is `β_c |K'(r)|` on the window edges of
length exactly `r` and `0` otherwise.  This is the exact left/right weight decomposition at the
level of the finite-window expectation. -/
theorem sum_cutEdgeDeriv_sub_sum_left (S : Finset (Sym2 M.V)) (g : Config M.V → ℝ) (r : ℝ) :
    (∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e)
        - (∑ e ∈ S, M.cutEdgeDerivLeft r e * pivotalFlux (M.cutLaw r) (cutFun S g) e)
      = ∑ e ∈ S, (M.cutEdgeDeriv r e - M.cutEdgeDerivLeft r e) *
          pivotalFlux (M.cutLaw r) (cutFun S g) e := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- The jump weight of a non-loop edge is nonnegative when the kernel decreases at `r`. -/
theorem cutEdgeDeriv_sub_cutEdgeDerivLeft_nonneg {r : ℝ} (hK' : deriv M.K r ≤ 0)
    (e : Sym2 M.V) : 0 ≤ M.cutEdgeDeriv r e - M.cutEdgeDerivLeft r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeDeriv_sub_cutEdgeDerivLeft_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      by_cases he : M.S.dist x y = r
      · rw [ite_eq_left he]
        have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := by positivity
        nlinarith
      · rw [ite_eq_right he]

/-- **No two-sided derivative at a corner with nonzero flux.**

If the left and right one-sided derivatives of the finite-window expectation at `r` differ, then
the two-sided derivative does not exist.  (This is the negative statement only: nothing here
claims that the one-sided derivatives differ in general.) -/
theorem not_exists_hasDerivAt_integral_cutFun_of_jump_ne_zero (S : Finset (Sym2 M.V))
    (g : Config M.V → ℝ) {r : ℝ} (hKd : DifferentiableAt ℝ M.K r)
    (hne : (∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e)
      ≠ ∑ e ∈ S, M.cutEdgeDerivLeft r e * pivotalFlux (M.cutLaw r) (cutFun S g) e) :
    ¬ ∃ L, HasDerivAt (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r')) L r := by
  rintro ⟨L, hL⟩
  have hleft := M.hasDerivWithinAt_integral_cutFun_cutLaw_Iic S g hKd
  have hright := M.hasDerivWithinAt_integral_cutFun_cutLaw_Ici S g hKd
  have e1 : derivWithin (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r')) (Set.Iic r) r
      = ∑ e ∈ S, M.cutEdgeDerivLeft r e * pivotalFlux (M.cutLaw r) (cutFun S g) e :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic r)
  have e2 : derivWithin (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r')) (Set.Iic r) r = L :=
    hL.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic r)
  have e3 : derivWithin (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r')) (Set.Ici r) r
      = ∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e :=
    hright.derivWithin (uniqueDiffWithinAt_Ici r)
  have e4 : derivWithin (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r')) (Set.Ici r) r = L :=
    hL.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici r)
  refine hne ?_
  calc (∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e)
      = derivWithin (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r')) (Set.Ici r) r := e3.symm
    _ = L := e4
    _ = derivWithin (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r')) (Set.Iic r) r := e2.symm
    _ = ∑ e ∈ S, M.cutEdgeDerivLeft r e * pivotalFlux (M.cutLaw r) (cutFun S g) e := e1

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## A closed-ball corner example: the two-edge path

Consider two edges of lengths `s₁ < s₂` under the independent edge law with open probability
`q_r(s) = 1 - exp (-(β J_r (s)))`.  The probability that *both* edges are open is the product
`q_r(s₁) q_r(s₂)`; this is the finite-window expectation of the event that the two-edge path
`0 — 1 — 2` is completely open, i.e. of the cluster reaching the boundary point of the closed ball
of radius `s₂`.

At `r = s₂` the ball boundary is attained.  The product has left derivative `0` (the second
factor is `0` and is flat on the left) and right derivative
`(1 - exp (-(β (K s₁ - K s₂)))) β |K'(s₂)| > 0`.  So the one-sided values differ: there is a
genuine corner in the closed convention `s ≤ r`, and no two-sided derivative.
-/

namespace PercLib.CriticalLRP.FiniteVolume

theorem edgeOpenProb_self_eq_zero (K : ℝ → ℝ) (β s : ℝ) :
    edgeOpenProb K β s s = 0 := by
  simp [edgeOpenProb, cutoffProfile_of_le le_rfl, longRangeEdgeProbability]

/-- **Closed-ball corner of the two-edge path.** -/
theorem two_edge_path_oneSided_deriv_ne
    {K : ℝ → ℝ} {K' s₁ s₂ β : ℝ} (h12 : s₁ < s₂) (hK : HasDerivAt K (-K') s₂)
    (hβ : 0 < β) (hK' : 0 < K') (hgap : 0 < K s₁ - K s₂) :
    HasDerivWithinAt (fun r => edgeOpenProb K β r s₁ * edgeOpenProb K β r s₂) 0
        (Set.Iic s₂) s₂ ∧
      HasDerivWithinAt (fun r => edgeOpenProb K β r s₁ * edgeOpenProb K β r s₂)
        ((1 - Real.exp (-(β * (K s₁ - K s₂)))) * (β * K')) (Set.Ici s₂) s₂ ∧
      0 < (1 - Real.exp (-(β * (K s₁ - K s₂)))) * (β * K') := by
  have hprof : cutoffProfile K s₂ s₁ = K s₁ - K s₂ := cutoffProfile_of_le h12.le
  -- the first (strictly shorter) edge: smooth at `s₂`
  have h1 : HasDerivAt (fun r => edgeOpenProb K β r s₁)
      (β * K' * Real.exp (-(β * (K s₁ - K s₂)))) s₂ := by
    have h := hasDerivAt_cutoffEdgeProbability (K := K) (K' := K') (r := s₂) (s := s₁) h12 hK β
    rw [hprof] at h
    exact h
  -- the second (boundary) edge: left derivative `0`, right derivative `β K'`
  have h2l : HasDerivWithinAt (fun r => edgeOpenProb K β r s₂) 0 (Set.Iic s₂) s₂ :=
    hasDerivWithinAt_cutoffEdgeProbability_Iic (K := K) (s := s₂) (β := β)
  have h2r : HasDerivWithinAt (fun r => edgeOpenProb K β r s₂) (β * K') (Set.Ici s₂) s₂ :=
    (hasDerivWithinAt_cutoffEdgeProbability_Ioi (K := K) (K' := K') (s := s₂) (β := β)
      hK).Ici_of_Ioi
  have hq1 : edgeOpenProb K β s₂ s₁ = 1 - Real.exp (-(β * (K s₁ - K s₂))) := by
    simp [edgeOpenProb, hprof, longRangeEdgeProbability]
  have hq2 : edgeOpenProb K β s₂ s₂ = 0 := edgeOpenProb_self_eq_zero K β s₂
  refine ⟨?_, ?_, ?_⟩
  · -- left derivative: `q₁' · 0 + q₁ · 0 = 0`
    have hprod := h1.hasDerivWithinAt.mul h2l
    have hval : β * K' * Real.exp (-(β * (K s₁ - K s₂))) * edgeOpenProb K β s₂ s₂
        + edgeOpenProb K β s₂ s₁ * 0 = 0 := by
      rw [hq2]; ring
    rw [hval] at hprod
    exact hprod
  · -- right derivative: `q₁' · 0 + q₁ · (β K')`
    have hprod := h1.hasDerivWithinAt.mul h2r
    have hval : β * K' * Real.exp (-(β * (K s₁ - K s₂))) * edgeOpenProb K β s₂ s₂
        + edgeOpenProb K β s₂ s₁ * (β * K')
        = (1 - Real.exp (-(β * (K s₁ - K s₂)))) * (β * K') := by
      rw [hq2, hq1]; ring
    rw [hval] at hprod
    exact hprod
  · -- positivity: `q₁(s₂) > 0` and `β K' > 0`
    have hexp : Real.exp (-(β * (K s₁ - K s₂))) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [mul_pos hβ hgap]
    have hq1pos : 0 < 1 - Real.exp (-(β * (K s₁ - K s₂))) := by linarith
    exact mul_pos hq1pos (mul_pos hβ hK')

end PercLib.CriticalLRP.FiniteVolume

/-! ## Compatibility with the landed off-corner derivative, and a non-vacuity instance -/

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- Off the corner set the strict and the closed weights coincide, so the one-sided formulae
`hasDerivWithinAt_cutProb_Iic/_Ici` specialize to the landed two-sided derivative
`hasDerivAt_cutProb_off`. -/
theorem cutEdgeDerivLeft_eq_cutEdgeDeriv_of_notMem_cornerRadii {r : ℝ}
    (hoff : r ∉ M.cornerRadii) : M.cutEdgeDerivLeft r = M.cutEdgeDeriv r := by
  funext e
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeDerivLeft_mk, M.cutEdgeDeriv_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      have hne : M.S.dist x y ≠ r := fun h => hoff ⟨x, y, hxy, h⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [ite_eq_left hlt, ite_eq_left hlt.le]
      · rw [ite_eq_right (not_lt.mpr hgt.le), ite_eq_right (not_le.mpr hgt)]

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.FiniteVolume

/-- **Non-vacuity of the two-edge corner example.**  With the decreasing linear kernel
`K t = 2 - t` (so `K' = 1` at `r = 2`), open probability parameter `β = 1` and lengths
`s₁ = 1 < s₂ = 2`, the hypotheses of `two_edge_path_oneSided_deriv_ne` are met: the left
derivative of the two-edge cluster probability at `r = 2` is `0` while its right derivative is
`1 - exp (-1) > 0`. -/
theorem two_edge_path_linear_witness :
    HasDerivWithinAt
        (fun r => edgeOpenProb (fun t => 2 - t) 1 r 1 * edgeOpenProb (fun t => 2 - t) 1 r 2)
        0 (Set.Iic 2) 2 ∧
      HasDerivWithinAt
        (fun r => edgeOpenProb (fun t => 2 - t) 1 r 1 * edgeOpenProb (fun t => 2 - t) 1 r 2)
        (1 - Real.exp (-1)) (Set.Ici 2) 2 ∧
      0 < 1 - Real.exp (-1) := by
  have h := two_edge_path_oneSided_deriv_ne (K := fun t => 2 - t) (K' := 1)
    (s₁ := 1) (s₂ := 2) (β := 1) (by norm_num)
    (by simpa using (hasDerivAt_id (2 : ℝ)).const_sub (2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simpa [show (1 : ℝ) - 2 = -1 by norm_num] using h

end PercLib.CriticalLRP.FiniteVolume

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The corner jump of the finite-window Russo derivative is strictly positive** when the kernel
decreases at `r` and some window edge of length exactly `r` carries a positive pivotal flux.

Together with `not_exists_hasDerivAt_integral_cutFun_of_jump_ne_zero` this gives a concrete,
non-vacuous failure of two-sided differentiability of the finite-window expectation at a closed
corner: the right derivative strictly exceeds the left one, while the expectation itself is
continuous there (`M.continuousAt_cutProb`, endpoint facts only). -/
theorem sum_left_lt_sum_of_corner_flux_pos (S : Finset (Sym2 M.V)) (g : Config M.V → ℝ)
    {r : ℝ} (hK' : deriv M.K r ≤ 0)
    (hflux : ∀ e ∈ S, 0 ≤ pivotalFlux (M.cutLaw r) (cutFun S g) e)
    (hpos : ∃ e ∈ S, M.cutEdgeDeriv r e - M.cutEdgeDerivLeft r e ≠ 0 ∧
      0 < pivotalFlux (M.cutLaw r) (cutFun S g) e) :
    (∑ e ∈ S, M.cutEdgeDerivLeft r e * pivotalFlux (M.cutLaw r) (cutFun S g) e)
      < ∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e := by
  have hkey := M.sum_cutEdgeDeriv_sub_sum_left S g r
  have hpos_sum : 0 < ∑ e ∈ S, (M.cutEdgeDeriv r e - M.cutEdgeDerivLeft r e) *
      pivotalFlux (M.cutLaw r) (cutFun S g) e := by
    obtain ⟨e0, he0, hne0, hfl0⟩ := hpos
    refine Finset.sum_pos' (fun e he => ?_) ⟨e0, he0, ?_⟩
    · exact mul_nonneg (M.cutEdgeDeriv_sub_cutEdgeDerivLeft_nonneg hK' e) (hflux e he)
    · exact mul_pos
        (lt_of_le_of_ne (M.cutEdgeDeriv_sub_cutEdgeDerivLeft_nonneg hK' e0) (Ne.symm hne0)) hfl0
  linarith

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Consistency check**: off the corner set, the two one-sided statements glue back to the
landed two-sided derivative `M.hasDerivAt_cutProb_off`.  This is a sanity check on
`hasDerivWithinAt_cutProb_Iic/_Ici` and `cutEdgeDerivLeft_eq_cutEdgeDeriv_of_notMem_cornerRadii`,
not a new input. -/
theorem hasDerivAt_cutProb_off_of_oneSided {r : ℝ} (hoff : r ∉ M.cornerRadii)
    (hKd : DifferentiableAt ℝ M.K r) (e : Sym2 M.V) :
    HasDerivAt (fun r' => ((M.cutProb r' e : unitInterval) : ℝ)) (M.cutEdgeDeriv r e) r := by
  have hleft := M.hasDerivWithinAt_cutProb_Iic hKd e
  rw [M.cutEdgeDerivLeft_eq_cutEdgeDeriv_of_notMem_cornerRadii hoff] at hleft
  have hright := M.hasDerivWithinAt_cutProb_Ici hKd e
  have hunion := hleft.union hright
  rw [Set.Iic_union_Ici] at hunion
  simpa using hunion

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Endpoint upgrade: interval differentiability with a continuous derivative family gives
one-sided differentiability at the corner -/

open MeasureTheory Filter Set
open scoped Topology
namespace PercLib.CriticalLRP.Orchestration

/-- Endpoint upgrade: differentiability on an interval plus continuity of the derivative at the
right endpoint gives the one-sided derivative there. -/
theorem hasDerivWithinAt_Iic_of_hasDerivAt_Ioo {f F : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt f (F x) x)
    (hcont : ContinuousWithinAt f (Set.Ioo a b) b)
    (hF : Tendsto F (𝓝[<] b) (𝓝 L)) :
    HasDerivWithinAt f L (Set.Iic b) b := by
  have hs : Set.Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT hab
  have hdiffOn : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt
  have hderiv : Tendsto (fun x => deriv f x) (𝓝[<] b) (𝓝 L) := by
    refine hF.congr' ?_
    filter_upwards [hs] with x hx
    exact (hdiff x hx).deriv.symm
  exact hasDerivWithinAt_Iic_of_tendsto_deriv hdiffOn hcont hs hderiv

namespace SourceModelData

variable (M : SourceModelData)

/-- Model-level one-sided mass derivative at a corner, from interval differentiability with an
explicit derivative family and continuity of that family at the corner from the left.
The continuity of `M.cutMassReal` itself is discharged by `tendsto_cutMassReal_nhdsLT`. -/
theorem hasDerivWithinAt_cutMassReal_Iic_of_interval_deriv (F : ℝ → ℝ) {a b L : ℝ}
    (hab : a < b) (hb : 0 < b) (hfin : M.cutMassAt b 0 ≠ ⊤)
    (hdiff : ∀ r ∈ Set.Ioo a b, HasDerivAt M.cutMassReal (F r) r)
    (hF : Tendsto F (𝓝[<] b) (𝓝 L)) :
    HasDerivWithinAt M.cutMassReal L (Set.Iic b) b := by
  have hleft : Tendsto M.cutMassReal (𝓝[<] b) (𝓝 (M.cutMassReal b)) :=
    M.tendsto_cutMassReal_nhdsLT b hb hfin
  have hcont : ContinuousWithinAt M.cutMassReal (Set.Ioo a b) b := by
    rw [ContinuousWithinAt]
    have hIoi : Set.Ioi a ∈ 𝓝 b := Ioi_mem_nhds hab
    have hset : Set.Ioo a b = Set.Iio b ∩ Set.Ioi a := by
      ext x; simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
      constructor <;> intro h <;> exact ⟨h.2, h.1⟩
    rw [hset, nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hIoi)]
    exact hleft
  exact hasDerivWithinAt_Iic_of_hasDerivAt_Ioo hab hdiff hcont hF

end SourceModelData

end PercLib.CriticalLRP.Orchestration
