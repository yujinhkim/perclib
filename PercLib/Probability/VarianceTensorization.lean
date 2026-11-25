/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-70: variance tensorisation (Efron–Stein) for finite Bernoulli profiles, the
variance lower bound on the homogeneous Russo derivative of an increasing event, and the
odds-ratio monotonicity it implies. Uses the finite-profile vocabulary of Russo.lean; no
new definition is introduced.
-/
module

public import PercLib.Probability.Russo
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section
noncomputable section

namespace PercLib.Probability.FiniteProfile
open Finset
open scoped Classical
variable {E : Type*} [Fintype E]

/-! ### Linearity and positivity of the profile expectation -/

lemma expectation_add (q : E → ℝ) (f g : (E → Bool) → ℝ) :
    expectation q (fun ω => f ω + g ω) = expectation q f + expectation q g := by
  simp only [expectation, add_mul, sum_add_distrib]

lemma expectation_sub (q : E → ℝ) (f g : (E → Bool) → ℝ) :
    expectation q (fun ω => f ω - g ω) = expectation q f - expectation q g := by
  simp only [expectation, sub_mul, sum_sub_distrib]

lemma expectation_const_mul (q : E → ℝ) (c : ℝ) (f : (E → Bool) → ℝ) :
    expectation q (fun ω => c * f ω) = c * expectation q f := by
  simp only [expectation, mul_sum, mul_assoc]

lemma sum_weight (q : E → ℝ) : ∑ ω, weight q ω = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun e (b : Bool) => if b then q e else 1 - q e)]
  simp

lemma expectation_const (q : E → ℝ) (c : ℝ) : expectation q (fun _ => c) = c := by
  simp only [expectation, ← mul_sum, sum_weight, mul_one]

lemma weight_nonneg {q : E → ℝ} (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1) (ω : E → Bool) :
    0 ≤ weight q ω :=
  prod_nonneg fun e _ => by
    have := hq e
    split_ifs
    · exact this.1
    · linarith [this.2]

lemma expectation_mono {q : E → ℝ} (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    {f g : (E → Bool) → ℝ} (h : ∀ ω, f ω ≤ g ω) : expectation q f ≤ expectation q g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_right (h ω) (weight_nonneg hq ω)

/-! ### Averaging out one coordinate -/

omit [Fintype E] in
lemma force_force (a : E) (b c : Bool) (ω : E → Bool) :
    force a b (force a c ω) = force a b ω := by
  simp [force, Function.update_idem]

omit [Fintype E] in
lemma force_comm {a e : E} (h : a ≠ e) (b c : Bool) (ω : E → Bool) :
    force a b (force e c ω) = force e c (force a b ω) := by
  simp only [force]
  exact (Function.update_comm h b c ω).symm

omit [Fintype E] in
lemma force_self (a : E) (ω : E → Bool) : force a (ω a) ω = ω := by
  simp [force]

/-- Pairing a configuration with its flip at `a` replaces the weight of coordinate `a` by
the one-coordinate average. -/
lemma paired_average (q : E → ℝ) (a : E) (h : (E → Bool) → ℝ) (ω : E → Bool) :
    h ω * weight q ω + h (flip a ω) * weight q (flip a ω) =
      (q a * h (force a true ω) + (1 - q a) * h (force a false ω)) *
        deletedWeight q a ω := by
  rw [weight_split q a ω, weight_split q a (flip a ω), deletedWeight_flip, flip_apply_self]
  cases hω : ω a
  · have hf : flip a ω = force a true ω := by simp [force, flip, hω]
    have hc : force a false ω = ω := by rw [← hω, force_self]
    simp only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hf, hc]
    ring
  · have hf : flip a ω = force a false ω := by simp [force, flip, hω]
    have ho : force a true ω = ω := by rw [← hω, force_self]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [hf, ho]
    ring

/-- Tower property: averaging out one coordinate does not change the expectation. This is
an identity of polynomials in the profile. -/
theorem expectation_average (q : E → ℝ) (a : E) (h : (E → Bool) → ℝ) :
    expectation q (fun ω => q a * h (force a true ω) + (1 - q a) * h (force a false ω)) =
      expectation q h := by
  set G : (E → Bool) → ℝ := fun ω => q a * h (force a true ω) + (1 - q a) * h (force a false ω)
    with hG
  have hGf (b : Bool) (ω : E → Bool) : G (force a b ω) = G ω := by
    simp only [hG, force_force]
  have h1 := sum_congr (s₁ := (univ : Finset (E → Bool))) rfl
    (fun ω _ => paired_average q a h ω)
  have h2 := sum_congr (s₁ := (univ : Finset (E → Bool))) rfl
    (fun ω _ => paired_average q a G ω)
  simp only [hGf] at h2
  rw [sum_add_distrib, sum_flip a (fun ω => h ω * weight q (ω))] at h1
  rw [sum_add_distrib, sum_flip a (fun ω => G ω * weight q (ω))] at h2
  have h3 : ∀ ω, (q a * G ω + (1 - q a) * G ω) = G ω := fun ω => by ring
  simp only [h3] at h2
  unfold expectation
  linarith

omit [Fintype E] in
/-- The increment of the one-coordinate average at another coordinate. -/
lemma difference_average (q : E → ℝ) {a e : E} (hae : a ≠ e) (f : (E → Bool) → ℝ)
    (ω : E → Bool) :
    difference e (fun ω => q a * f (force a true ω) + (1 - q a) * f (force a false ω)) ω =
      q a * difference e f (force a true ω) + (1 - q a) * difference e f (force a false ω) := by
  simp only [difference, force_comm hae]
  ring

omit [Fintype E] in
lemma force_eq_of_difference_eq_zero {e : E} {f : (E → Bool) → ℝ}
    (hf : ∀ ω, difference e f ω = 0) (b : Bool) (ω : E → Bool) :
    f (force e b ω) = f ω := by
  have h := hf ω
  simp only [difference, sub_eq_zero] at h
  conv_rhs => rw [← force_self e ω]
  cases b <;> cases ω e <;> simp [h]

omit [Fintype E] in
/-- An observable with no increment at any coordinate is constant. -/
lemma eq_const_of_difference_eq_zero [Finite E] {f : (E → Bool) → ℝ}
    (hf : ∀ e ω, difference e f ω = 0) (ω : E → Bool) : f ω = f (fun _ => false) := by
  have := Fintype.ofFinite E
  have key : ∀ T : Finset E, f ω = f (fun e => if e ∈ T then false else ω e) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T _ ih =>
      rw [ih, ← force_eq_of_difference_eq_zero (hf a) false]
      congr 1
      funext j
      by_cases hj : j = a
      · subst hj; simp [force]
      · simp [force, hj]
  simpa using key univ

/-! ### Efron–Stein -/

/-- Efron–Stein on the coordinates in `S`, for an observable without increments outside `S`. -/
theorem variance_le_sum_on (q : E → ℝ) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1) (S : Finset E) :
    ∀ f : (E → Bool) → ℝ, (∀ e ∉ S, ∀ ω, difference e f ω = 0) →
      expectation q (fun ω => f ω ^ 2) - expectation q f ^ 2 ≤
        ∑ e ∈ S, q e * (1 - q e) * expectation q (fun ω => difference e f ω ^ 2) := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hf
    have hc : f = fun _ => f (fun _ => false) :=
      funext (eq_const_of_difference_eq_zero (fun e => hf e (notMem_empty e)))
    rw [hc, expectation_const, expectation_const]
    simp
  | insert a S haS ih =>
    intro f hf
    set g : (E → Bool) → ℝ := fun ω => q a * f (force a true ω) + (1 - q a) * f (force a false ω)
      with hg
    have hqa := hq a
    -- the averaged observable has no increment outside `S`
    have hgS : ∀ e ∉ S, ∀ ω, difference e g ω = 0 := by
      intro e he ω
      by_cases hea : e = a
      · subst hea
        simp only [difference, hg, force_force, sub_self]
      · rw [hg, difference_average q (Ne.symm hea)]
        have he' : e ∉ insert a S := by simp [hea, he]
        simp [hf e he']
    have hIH := ih g hgS
    -- variance decomposition at coordinate `a`
    have hmean : expectation q g = expectation q f := expectation_average q a f
    have hsq : expectation q (fun ω => f ω ^ 2) =
        q a * (1 - q a) * expectation q (fun ω => difference a f ω ^ 2) +
          expectation q (fun ω => g ω ^ 2) := by
      rw [← expectation_average q a (fun ω => f ω ^ 2), ← expectation_const_mul,
        ← expectation_add]
      congr 1
      funext ω
      simp only [hg, difference]
      ring
    -- averaging decreases the squared increments at the other coordinates
    have hcmp : ∀ e ∈ S, q e * (1 - q e) * expectation q (fun ω => difference e g ω ^ 2) ≤
        q e * (1 - q e) * expectation q (fun ω => difference e f ω ^ 2) := by
      intro e he
      have hae : a ≠ e := fun h => haS (h ▸ he)
      have hqe := hq e
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hqe.1 (by linarith [hqe.2]))
      rw [← expectation_average q a (fun ω => difference e f ω ^ 2)]
      apply expectation_mono hq
      intro ω
      rw [hg, difference_average q hae]
      nlinarith [sq_nonneg (difference e f (force a true ω) - difference e f (force a false ω)),
        mul_nonneg hqa.1 (sub_nonneg.mpr hqa.2)]
    rw [sum_insert haS]
    have := sum_le_sum hcmp
    rw [hmean] at hIH
    linarith

/-- **Efron–Stein inequality for finite Bernoulli profiles** (R428). For a profile with
values in `[0,1]`, endpoints allowed, the variance `E_q[f²] - (E_q f)²` is at most
`∑ₑ qₑ(1-qₑ) E_q[(Δₑ f)²]`. -/
theorem variance_le_sum_difference_sq (q : E → ℝ) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (f : (E → Bool) → ℝ) :
    expectation q (fun ω => f ω ^ 2) - expectation q f ^ 2 ≤
      ∑ e, q e * (1 - q e) * expectation q (fun ω => difference e f ω ^ 2) :=
  variance_le_sum_on q hq univ f (fun e he => absurd (mem_univ e) he)

/-- The variance is the expectation of the squared centred observable. -/
theorem variance_eq_expectation_sq (q : E → ℝ) (f : (E → Bool) → ℝ) :
    expectation q (fun ω => f ω ^ 2) - expectation q f ^ 2 =
      expectation q (fun ω => (f ω - expectation q f) ^ 2) := by
  have h : (fun ω => (f ω - expectation q f) ^ 2) =
      fun ω => (f ω ^ 2 + (-2 * expectation q f) * f ω) + expectation q f ^ 2 := by
    funext ω; ring
  rw [h, expectation_add, expectation_add, expectation_const_mul, expectation_const]
  ring

theorem variance_nonneg (q : E → ℝ) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (f : (E → Bool) → ℝ) : 0 ≤ expectation q (fun ω => f ω ^ 2) - expectation q f ^ 2 := by
  rw [variance_eq_expectation_sq, ← expectation_const q 0]
  exact expectation_mono hq fun ω => sq_nonneg _

/-! ### Increasing events: variance bound on the Russo derivative -/

omit [Fintype E] in
lemma eventValue_sq (A : Set (Set E)) (ω : E → Bool) : eventValue A ω ^ 2 = eventValue A ω := by
  unfold eventValue; split_ifs <;> norm_num

lemma expectation_eventValue_mem_Icc {q : E → ℝ} (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (A : Set (Set E)) : expectation q (eventValue A) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← expectation_const q 0]
    exact expectation_mono hq fun ω => by unfold eventValue; split_ifs <;> norm_num
  · rw [← expectation_const q 1]
    exact expectation_mono hq fun ω => by unfold eventValue; split_ifs <;> norm_num

/-- Variance bound for an increasing event with the pivotal sum written out, for any
profile with values in `[0,1]`. -/
theorem event_variance_le_pivotal (q : E → ℝ) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    {A : Set (Set E)} (hA : IsUpperSet A) :
    expectation q (eventValue A) * (1 - expectation q (eventValue A)) ≤
      ∑ e, q e * (1 - q e) * expectation q (fun ω => if pivotal A e ω then 1 else 0) := by
  have h := variance_le_sum_difference_sq q hq (eventValue A)
  simp only [eventValue_sq, difference_eventValue hA] at h
  have hsq : ∀ (P : Prop) [Decidable P], ((if P then (1 : ℝ) else 0) ^ 2) = if P then 1 else 0 :=
    fun P _ => by split_ifs <;> norm_num
  simp only [hsq] at h
  nlinarith [h]

/-- The homogeneous event polynomial `F(p) = E_p[1_A]` and its Russo derivative. -/
lemma event_homogeneous_hasDerivAt (p : ℝ) (A : Set (Set E)) (hA : IsUpperSet A) :
    HasDerivAt (fun u => expectation (fun _ : E => u) (eventValue A))
      (∑ e, expectation (fun _ : E => p) (fun ω => if pivotal A e ω then 1 else 0)) p := by
  simpa using event_hasDerivAt (fun _ u => u) (fun _ => 1) p (fun _ => hasDerivAt_id p) hA

/-- **GI8Q.** For an increasing event and `F(p) = P_p(A)` (as the event polynomial),
`p(1-p) F'(p) ≥ F(p)(1-F(p))`. Holds on the closed interval `[0,1]`. -/
theorem event_variance_le_deriv {A : Set (Set E)} (hA : IsUpperSet A) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    expectation (fun _ : E => p) (eventValue A) *
        (1 - expectation (fun _ : E => p) (eventValue A)) ≤
      p * (1 - p) * deriv (fun u => expectation (fun _ : E => u) (eventValue A)) p := by
  rw [(event_homogeneous_hasDerivAt p A hA).deriv, mul_sum]
  exact event_variance_le_pivotal (fun _ => p) (fun _ => hp) hA

private lemma prodBernoulli_real_eq_expectation (r : E → unitInterval) (A : Set (Set E)) :
    (prodBernoulli r).real A = expectation (fun e => (r e : ℝ)) (eventValue A) := by
  rw [← MeasureTheory.integral_indicator_one (Set.toFinite A).measurableSet,
    integral_prodBernoulli_eq_expectation]
  rfl

/-- **GI8Q**, probability form: with `F(u) = P_u(A)` for the homogeneous product law
(extended outside `[0,1]` by clamping), `p(1-p) F'(p) ≥ F(p)(1-F(p))` for `0 < p < 1`. -/
theorem prodBernoulli_event_variance_le_deriv {A : Set (Set E)} (hA : IsUpperSet A) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (prodBernoulli (fun _ : E => Set.projIcc 0 1 zero_le_one p)).real A *
        (1 - (prodBernoulli (fun _ : E => Set.projIcc 0 1 zero_le_one p)).real A) ≤
      p * (1 - p) *
        deriv (fun u => (prodBernoulli (fun _ : E => Set.projIcc 0 1 zero_le_one u)).real A) p := by
  have heq : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (prodBernoulli (fun _ : E => Set.projIcc 0 1 zero_le_one u)).real A =
        expectation (fun _ : E => u) (eventValue A) := by
    intro u hu
    rw [prodBernoulli_real_eq_expectation, Set.projIcc_of_mem zero_le_one hu]
  have hev : (fun u => (prodBernoulli (fun _ : E => Set.projIcc 0 1 zero_le_one u)).real A) =ᶠ[nhds p]
      fun u => expectation (fun _ : E => u) (eventValue A) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with u hu
    exact heq u (Set.Ioo_subset_Icc_self hu)
  rw [hev.deriv_eq, heq p (Set.Ioo_subset_Icc_self hp)]
  exact event_variance_le_deriv hA (Set.Ioo_subset_Icc_self hp)

/-! ### Odds-ratio monotonicity -/

lemma expectation_eventValue_pos {q : E → ℝ} (hq : ∀ e, q e ∈ Set.Ioo (0 : ℝ) 1)
    {A : Set (Set E)} (hA : IsUpperSet A) (hne : A.Nonempty) :
    0 < expectation q (eventValue A) := by
  have hq' : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1 := fun e => Set.Ioo_subset_Icc_self (hq e)
  obtain ⟨s, hs⟩ := hne
  have huniv : toSet (fun _ : E => true) ∈ A := hA (by simp [toSet]) hs
  have hw : 0 < weight q (fun _ => true) := prod_pos fun e _ => by simpa using (hq e).1
  unfold expectation
  calc (0 : ℝ) < eventValue A (fun _ => true) * weight q (fun _ => true) := by
        simpa [eventValue, huniv] using hw
    _ ≤ ∑ ω, eventValue A ω * weight q ω :=
        single_le_sum (f := fun ω => eventValue A ω * weight q ω)
          (fun ω _ => mul_nonneg (by unfold eventValue; split_ifs <;> norm_num)
            (weight_nonneg hq' ω)) (mem_univ _)

lemma expectation_eventValue_lt_one {q : E → ℝ} (hq : ∀ e, q e ∈ Set.Ioo (0 : ℝ) 1)
    {A : Set (Set E)} (hA : IsUpperSet A) (hnu : A ≠ Set.univ) :
    expectation q (eventValue A) < 1 := by
  have hq' : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1 := fun e => Set.Ioo_subset_Icc_self (hq e)
  have hempty : toSet (fun _ : E => false) ∉ A := by
    intro h
    apply hnu
    exact Set.eq_univ_of_forall fun s => hA (by simp [toSet]) h
  have hw : 0 < weight q (fun _ => false) := prod_pos fun e _ => by simpa using (hq e).2
  have h1 : 0 < expectation q (fun ω => 1 - eventValue A ω) := by
    unfold expectation
    calc (0 : ℝ) < (1 - eventValue A (fun _ => false)) * weight q (fun _ => false) := by
          simpa [eventValue, hempty] using hw
      _ ≤ ∑ ω, (1 - eventValue A ω) * weight q ω :=
          single_le_sum (f := fun ω => (1 - eventValue A ω) * weight q ω)
            (fun ω _ => mul_nonneg (by unfold eventValue; split_ifs <;> norm_num)
              (weight_nonneg hq' ω)) (mem_univ _)
  rw [expectation_sub, expectation_const] at h1
  linarith

/-- The function `p ↦ [F/(1-F)] / [p/(1-p)]` is monotone on `(0,1)`. -/
theorem odds_ratio_monotoneOn {A : Set (Set E)} (hA : IsUpperSet A) (hne : A.Nonempty)
    (hnu : A ≠ Set.univ) :
    MonotoneOn (fun u => expectation (fun _ : E => u) (eventValue A) /
        (1 - expectation (fun _ : E => u) (eventValue A)) * ((1 - u) / u)) (Set.Ioo 0 1) := by
  set F : ℝ → ℝ := fun u => expectation (fun _ : E => u) (eventValue A) with hF
  set D : ℝ → ℝ := fun u =>
    ∑ e, expectation (fun _ : E => u) (fun ω => if pivotal A e ω then 1 else 0) with hD
  have hFd : ∀ u, HasDerivAt F (D u) u := fun u => event_homogeneous_hasDerivAt u A hA
  have hpos : ∀ u ∈ Set.Ioo (0 : ℝ) 1, 0 < F u := fun u hu =>
    expectation_eventValue_pos (fun _ => hu) hA hne
  have hlt : ∀ u ∈ Set.Ioo (0 : ℝ) 1, F u < 1 := fun u hu =>
    expectation_eventValue_lt_one (fun _ => hu) hA hnu
  have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun u => F u / (1 - F u) * ((1 - u) / u))
      ((D u * (1 - F u) - F u * (-D u)) / (1 - F u) ^ 2 * ((1 - u) / u) +
        F u / (1 - F u) * ((-1 * u - (1 - u) * 1) / u ^ 2)) u := by
    intro u hu
    have h1 : 1 - F u ≠ 0 := by linarith [hlt u hu]
    have h2 : u ≠ 0 := hu.1.ne'
    exact ((hFd u).div ((hFd u).const_sub 1) h1).mul
      (((hasDerivAt_id u).const_sub 1).div (hasDerivAt_id u) h2)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
  · intro u hu
    exact (hderiv u hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    exact (hderiv u hu).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    have hvar := event_variance_le_pivotal (fun _ : E => u)
      (fun _ => Set.Ioo_subset_Icc_self hu) hA
    rw [← mul_sum] at hvar
    change F u * (1 - F u) ≤ u * (1 - u) * D u at hvar
    have hF1 : 0 < 1 - F u := by linarith [hlt u hu]
    have hu0 := hu.1
    have key : (D u * (1 - F u) - F u * (-D u)) / (1 - F u) ^ 2 * ((1 - u) / u) +
        F u / (1 - F u) * ((-1 * u - (1 - u) * 1) / u ^ 2) =
        (u * (1 - u) * D u - F u * (1 - F u)) / ((1 - F u) ^ 2 * u ^ 2) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by linarith) (by positivity)

/-- **6ITM.** For an increasing event that is neither empty nor everything, and
`0 < a < b < 1`: `F(b)/(1-F(b)) ≥ F(a)/(1-F(a)) · b(1-a)/(a(1-b))`, with `F` the event
polynomial. -/
theorem odds_ratio_le {A : Set (Set E)} (hA : IsUpperSet A) (hne : A.Nonempty)
    (hnu : A ≠ Set.univ) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    expectation (fun _ : E => a) (eventValue A) /
        (1 - expectation (fun _ : E => a) (eventValue A)) * (b * (1 - a) / (a * (1 - b))) ≤
      expectation (fun _ : E => b) (eventValue A) /
        (1 - expectation (fun _ : E => b) (eventValue A)) := by
  have hm := odds_ratio_monotoneOn hA hne hnu ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab.le
  simp only at hm
  set Fa := expectation (fun _ : E => a) (eventValue A) /
    (1 - expectation (fun _ : E => a) (eventValue A))
  set Fb := expectation (fun _ : E => b) (eventValue A) /
    (1 - expectation (fun _ : E => b) (eventValue A))
  have hb0 : 0 < b := ha.trans hab
  have h1b : 0 < 1 - b := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hfac : 0 < b / (1 - b) := div_pos hb0 h1b
  have := mul_le_mul_of_nonneg_right hm hfac.le
  have e1 : Fa * ((1 - a) / a) * (b / (1 - b)) = Fa * (b * (1 - a) / (a * (1 - b))) := by
    field_simp
  have e2 : Fb * ((1 - b) / b) * (b / (1 - b)) = Fb := by
    field_simp
  linarith

/-- **6ITM**, probability form for the homogeneous product law. -/
theorem prodBernoulli_odds_ratio_le {A : Set (Set E)} (hA : IsUpperSet A) (hne : A.Nonempty)
    (hnu : A ≠ Set.univ) {a b : unitInterval} (ha : 0 < (a : ℝ)) (hab : (a : ℝ) < b)
    (hb : (b : ℝ) < 1) :
    (prodBernoulli (fun _ : E => a)).real A / (1 - (prodBernoulli (fun _ : E => a)).real A) *
        (b * (1 - a) / (a * (1 - b))) ≤
      (prodBernoulli (fun _ : E => b)).real A / (1 - (prodBernoulli (fun _ : E => b)).real A) := by
  simp only [prodBernoulli_real_eq_expectation]
  exact odds_ratio_le hA hne hnu ha hab hb

/-! ### Non-vacuity witnesses (D-5) -/

/-- At deterministic profiles (every `q e ∈ {0,1}`) both sides of Efron–Stein vanish. -/
example (q : E → ℝ) (hq : ∀ e, q e = 0 ∨ q e = 1) (f : (E → Bool) → ℝ) :
    expectation q (fun ω => f ω ^ 2) - expectation q f ^ 2 = 0 ∧
      ∑ e, q e * (1 - q e) * expectation q (fun ω => difference e f ω ^ 2) = 0 := by
  have hq' : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1 := fun e => by
    rcases hq e with h | h <;> simp [h]
  have hz : ∑ e, q e * (1 - q e) * expectation q (fun ω => difference e f ω ^ 2) = 0 :=
    sum_eq_zero fun e _ => by rcases hq e with h | h <;> simp [h]
  refine ⟨le_antisymm ?_ (variance_nonneg q hq' f), hz⟩
  simpa [hz] using variance_le_sum_difference_sq q hq' f

private lemma singleton_event (p : ℝ) :
    expectation (fun _ : Unit => p) (eventValue {s : Set Unit | () ∈ s}) = p := by
  have h : eventValue {s : Set Unit | () ∈ s} = fun ω => if ω () then 1 else 0 := by
    funext ω
    unfold eventValue toSet
    by_cases hω : ω () <;> simp [hω]
  rw [h, expectation_singleton]

/-- One coordinate and `A = {s | () ∈ s}`: GI8Q is an equality, `p(1-p)·1 = p(1-p)`. -/
example (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    expectation (fun _ : Unit => p) (eventValue {s : Set Unit | () ∈ s}) *
        (1 - expectation (fun _ : Unit => p) (eventValue {s : Set Unit | () ∈ s})) =
      p * (1 - p) *
        deriv (fun u => expectation (fun _ : Unit => u) (eventValue {s : Set Unit | () ∈ s})) p ∧
    expectation (fun _ : Unit => p) (eventValue {s : Set Unit | () ∈ s}) *
        (1 - expectation (fun _ : Unit => p) (eventValue {s : Set Unit | () ∈ s})) ≤
      p * (1 - p) *
        deriv (fun u => expectation (fun _ : Unit => u) (eventValue {s : Set Unit | () ∈ s})) p := by
  refine ⟨?_, event_variance_le_deriv (fun _ _ hst h => hst h) hp⟩
  simp only [singleton_event, deriv_id'', mul_one]

/-- One coordinate and `A = {s | () ∈ s}`: 6ITM is an equality, and its hypotheses hold. -/
example (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    expectation (fun _ : Unit => a) (eventValue {s : Set Unit | () ∈ s}) /
        (1 - expectation (fun _ : Unit => a) (eventValue {s : Set Unit | () ∈ s})) *
        (b * (1 - a) / (a * (1 - b))) =
      expectation (fun _ : Unit => b) (eventValue {s : Set Unit | () ∈ s}) /
        (1 - expectation (fun _ : Unit => b) (eventValue {s : Set Unit | () ∈ s})) ∧
    expectation (fun _ : Unit => a) (eventValue {s : Set Unit | () ∈ s}) /
        (1 - expectation (fun _ : Unit => a) (eventValue {s : Set Unit | () ∈ s})) *
        (b * (1 - a) / (a * (1 - b))) ≤
      expectation (fun _ : Unit => b) (eventValue {s : Set Unit | () ∈ s}) /
        (1 - expectation (fun _ : Unit => b) (eventValue {s : Set Unit | () ∈ s})) := by
  refine ⟨?_, odds_ratio_le (fun _ _ hst h => hst h) ⟨Set.univ, trivial⟩
    (fun h => by
      have h0 : (∅ : Set Unit) ∈ ({s : Set Unit | () ∈ s}) := h ▸ Set.mem_univ _
      simp at h0)
    ha hab hb⟩
  simp only [singleton_event]
  have h1a : 1 - a ≠ 0 := by linarith
  have h1b : 1 - b ≠ 0 := by linarith
  field_simp

end PercLib.Probability.FiniteProfile
