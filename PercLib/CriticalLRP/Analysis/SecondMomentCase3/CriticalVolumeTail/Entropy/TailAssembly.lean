/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Assembling the two-intensity volume-tail comparison from relative entropy

Source: T. Hutchcroft, *On the derivation of mean-field percolation critical exponents from the
triangle condition* (arXiv:2106.06400), Section 3 and the proof of Theorem 1.3:

* the generalised Pinsker inequality (3.2) (Dewan--Muirhead [15, Lemma 2.12]),
  `|μ(A) - ν(A)|^2 ≤ 2 D_KL(μ‖ν) max {μ(A), ν(A)}`;
* the two-intensity comparison (3.8),
  `P_{β₂}(|K| ≥ n) ≤ 2 P_{β₁}(|K| ≥ n) + (4/β₁)|β₂ - β₁|² ∑_{k=1}^n P_{β₁}(|K| ≥ k)`,
  with the factor `4` multiplied by `A = ∑_{e ∈ E^→_o} J_e` in the unnormalised model.

The source reaches (3.8) as follows.  Theorem 3.1 gives
`|P_{β₂}(A) - P_{β₁}(A)|² ≤ (|β₂-β₁|²/min{β₁,β₂}) max{P_{β₁}(A),P_{β₂}(A)} ∑_e J_e Rev_{β₁}(T,e)`
for an event `A` Borel-computed by a decision tree `T`; the cluster exploration for
`A = {|K| ≥ n}` reveals only edges meeting at most `n` vertices, so that
`∑_e J_e Rev_{β₁}(T,e) ≤ A ∑_{k ≤ n} P_{β₁}(|K| ≥ k)`; and the two-case comparison of the two
event masses then yields (3.8), after which Markov's inequality gives the `χ_{β₁}` form.

**What this file proves, and what it does not.**  The two inputs above (the transcript
relative-entropy bound, and the revealment/exploration estimate) are *not* proved here: they
enter as the explicitly named hypotheses `hKL` and `hRev`.  What is proved here is the assembly:

* `event_mass_diff_sq_le`: the generalised Pinsker inequality (3.2) on a finite probability
  space, valid for *all* events, including the degenerate cases `P(A) = 0` and `P(A) = 1` where
  the interior form `pinsker_general` does not apply;
* `event_mass_le_of_kl`: the source's two-case deduction `a ≤ 2 b + 8 κ` from
  `(a - b)^2 ≤ 2 κ max {a,b}`, i.e. (3.8) with `κ` the relevant relative entropy;
* `sum_tailMass_eq_expect_min`: the exact tail-sum identity `∑_{k ≤ n} P(v ≥ k) = E[v ∧ n]`
  (the source's display `E_{β₁}[|K| ∧ n] = ∑_{k=1}^{n} P_{β₁}(|K| ≥ k)`), together with
  `sum_tailMass_le_expect` (`∑_{k ≤ n} P(v ≥ k) ≤ E v`) and `mul_tailMass_le_expect`
  (`n P(v ≥ n) ≤ E v`, Markov), for a `ℕ`-valued volume `v`;
* `twoIntensity_tail_le_sum`, `twoIntensity_tail_le_susceptibility`: the finite assembly (3.8)
  and its `(2/n + (4A/β₁)(β₂-β₁)²) χ_{β₁}` corollary, on an abstract finite probability space;
* `finiteBond_tail_twoIntensity` and `finiteBond_tail_twoIntensity_of_revealment`: the same two
  statements instantiated at the finite weighted Bernoulli weights `confWeight J β` of
  `Entropy/Bernoulli.lean`, with all density hypotheses discharged;
* `log_sum_ineq_tsum`, `bkl_eventMass_le_kl_tsum`, `event_mass_le_of_kl_tsum`: the *countable*
  form of the same three statements, which is the form that applies to the transcript space
  `{0,1,∅}^ℕ` of the source (the finite-sum lemmas above are not applicable there).

What is still needed for the canonical infinite-volume model is listed, in the exact form in which
it is missing, in the final section of this file; none of it is claimed here.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Entropy.Pinsker

/-!
# From finite relative entropy to the two-intensity volume-tail comparison
-/

set_option autoImplicit false

@[expose] public section

open Finset

namespace LRP

/-! ### The generalised Pinsker inequality (3.2), including degenerate events -/

section BinaryKL

variable {α : Type*} [Fintype α]

omit [Fintype α] in
/-- A finset on which a strictly positive function has zero sum is empty. -/
theorem eq_empty_of_sum_eq_zero {s : Finset α} {g : α → ℝ} (hg : ∀ x, 0 < g x)
    (h : ∑ x ∈ s, g x = 0) : s = ∅ := by
  rcases s.eq_empty_or_nonempty with h0 | ⟨x, hx⟩
  · exact h0
  · exact absurd h (ne_of_gt (Finset.sum_pos (fun y _ => hg y) ⟨x, hx⟩))

/-- **Nonnegativity of the finite relative entropy** (the Gibbs inequality at the trivial
partition). -/
theorem kl_nonneg (f g : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x)
    (hf1 : ∑ x, f x = 1) (hg1 : ∑ x, g x = 1) :
    0 ≤ ∑ x, f x * Real.log (f x / g x) := by
  have h := log_sum_ineq (s := Finset.univ) (f := f) (g := g) (fun x _ => hf x) (fun x _ => hg x)
  rw [hf1, hg1] at h
  simpa using h

/-- **Coarse-graining of the relative entropy to an event.**  The binary divergence of the pair
of event masses is at most the relative entropy: this is the two-bin Gibbs inequality obtained by
applying the log-sum inequality on the event and on its complement.  Unlike
`LRP.pinsker_general` no interiority hypothesis is needed. -/
theorem bkl_eventMass_le_kl (f g : α → ℝ) (s : Finset α) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 < g x) (hf1 : ∑ x, f x = 1) (hg1 : ∑ x, g x = 1) :
    bkl (∑ x ∈ s, f x) (∑ x ∈ s, g x) ≤ ∑ x, f x * Real.log (f x / g x) := by
  classical
  have h1 := log_sum_ineq (s := s) (f := f) (g := g) (fun x _ => hf x) (fun x _ => hg x)
  have h2 := log_sum_ineq (s := sᶜ) (f := f) (g := g) (fun x _ => hf x) (fun x _ => hg x)
  have hfc : (∑ x ∈ sᶜ, f x) = 1 - ∑ x ∈ s, f x := by
    have h := Finset.sum_add_sum_compl s f
    rw [hf1] at h
    linarith
  have hgc : (∑ x ∈ sᶜ, g x) = 1 - ∑ x ∈ s, g x := by
    have h := Finset.sum_add_sum_compl s g
    rw [hg1] at h
    linarith
  have hsplit : ∑ x, f x * Real.log (f x / g x)
      = ∑ x ∈ s, f x * Real.log (f x / g x)
        + ∑ x ∈ sᶜ, f x * Real.log (f x / g x) :=
    (Finset.sum_add_sum_compl s _).symm
  rw [bkl, ← hfc, ← hgc]
  linarith

/-- **Generalised Pinsker inequality (3.2) on a finite space, all events allowed.**  For two
probability masses on a finite type and *any* event, the squared difference of the event masses
is at most twice the relative entropy times the larger of the two masses.  This is the form of
Dewan--Muirhead's inequality (3.2) used in the proof of Theorem 3.1 of the source; the degenerate
cases where one of the masses is `0` or `1` are reduced to `bkl_eventMass_le_kl` and the interior
form `LRP.binary_kl_sq_le'`. -/
theorem event_mass_diff_sq_le (f g : α → ℝ) (s : Finset α) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 < g x) (hf1 : ∑ x, f x = 1) (hg1 : ∑ x, g x = 1) :
    (∑ x ∈ s, f x - ∑ x ∈ s, g x) ^ 2
      ≤ 2 * (∑ x, f x * Real.log (f x / g x)) * max (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  classical
  set a := ∑ x ∈ s, f x with ha
  set b := ∑ x ∈ s, g x with hb
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun x _ => hf x
  have ha1 : a ≤ 1 := by
    have h : a ≤ ∑ x, f x := by
      rw [ha]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun x _ _ => hf x
    linarith
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun x _ => (hg x).le
  have hb1 : b ≤ 1 := by
    have h : b ≤ ∑ x, g x := by
      rw [hb]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun x _ _ => (hg x).le
    linarith
  have hbc : b = 1 - ∑ x ∈ sᶜ, g x := by
    have h := Finset.sum_add_sum_compl s g
    rw [hg1, ← hb] at h
    linarith
  rcases eq_or_lt_of_le hb0 with hzero | hpos
  · -- `b = 0`: then `s = ∅`, so both event masses vanish
    have hs : s = ∅ := eq_empty_of_sum_eq_zero hg (by rw [← hb]; exact hzero.symm)
    have hae : a = 0 := by rw [ha, hs]; simp
    have hbe : b = 0 := by rw [hb, hs]; simp
    rw [hae, hbe]
    simp
  rcases eq_or_lt_of_le hb1 with hone | hlt
  · -- `b = 1`: then the complement carries no mass for `g`, hence none for `f` either
    have hcomp : ∑ x ∈ sᶜ, g x = 0 := by linarith
    have hs : sᶜ = ∅ := eq_empty_of_sum_eq_zero hg hcomp
    have hfc : ∑ x ∈ sᶜ, f x = 0 := by rw [hs]; simp
    have hae : a = 1 := by
      have h := Finset.sum_add_sum_compl s f
      rw [hf1, ← ha] at h
      linarith
    have hb1' : max (1 : ℝ) 1 = 1 := max_self 1
    have hk := kl_nonneg f g hf hg hf1 hg1
    rw [hae, hone, hb1']
    nlinarith
  · -- interior case
    have hbin := binary_kl_sq_le' ha0 ha1 hpos hlt
    have hkl := bkl_eventMass_le_kl f g s hf hg hf1 hg1
    rw [← ha, ← hb] at hkl
    have hmax : 0 ≤ max a b := le_trans ha0 (le_max_left _ _)
    calc (a - b) ^ 2 ≤ 2 * max a b * bkl a b := hbin
      _ ≤ 2 * max a b * (∑ x, f x * Real.log (f x / g x)) := by
        refine mul_le_mul_of_nonneg_left hkl ?_
        linarith
      _ = 2 * (∑ x, f x * Real.log (f x / g x)) * max a b := by ring

end BinaryKL

/-! ### The source's two-case deduction from (3.2) to the linear event bound -/

/-- **Two-case step of the proof of Theorem 1.3 of the source.**  If the squared difference of
two event masses is controlled by `2 κ max {a,b}`, then `a ≤ 2 b + 8 κ`.  If `a ≤ 2 b` this is
immediate; otherwise `a > 2 b`, so `max {a,b} = a` and `a - b > a/2`, whence
`a²/4 < (a-b)² ≤ 2 κ a`, i.e. `a < 8 κ`.  This is exactly the source's passage from (3.9) to
(3.8). -/
theorem two_le_add_eight_mul (a b κ : ℝ) (hb : 0 ≤ b) (hκ : 0 ≤ κ)
    (h : (a - b) ^ 2 ≤ 2 * κ * max a b) : a ≤ 2 * b + 8 * κ := by
  rcases le_or_gt a (2 * b) with hle | hgt
  · linarith
  · have hba : b ≤ a := by linarith
    have hmax : max a b = a := max_eq_left hba
    have ha : 0 < a := by linarith
    rw [hmax] at h
    have hsq : (a / 2) ^ 2 < (a - b) ^ 2 := by
      have hhalf : a / 2 < a - b := by linarith
      nlinarith
    have h1 : a ^ 2 / 4 < 2 * κ * a := by
      have hsq' : a ^ 2 / 4 < (a - b) ^ 2 := by nlinarith
      exact lt_of_lt_of_le hsq' h
    have h2 : a * a < 8 * κ * a := by nlinarith
    have h3 : a < 8 * κ := lt_of_mul_lt_mul_right h2 ha.le
    linarith

/-! ### The relative entropy bound on an event, and the linear form used in the assembly -/

section EventBound

variable {α : Type*} [Fintype α]

/-- **Generalised Pinsker applied to an event with a relative-entropy budget.**  If the relative
entropy from `g` to `f` is at most `κ`, then the `f`-mass of any event is at most twice its
`g`-mass plus `8 κ`.  No interiority condition is imposed: unlike `LRP.pinsker_general` the
degenerate events are covered by `LRP.event_mass_diff_sq_le`. -/
theorem event_mass_le_of_kl (f g : α → ℝ) (s : Finset α) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 < g x) (hf1 : ∑ x, f x = 1) (hg1 : ∑ x, g x = 1) {κ : ℝ}
    (hκ : ∑ x, f x * Real.log (f x / g x) ≤ κ) (hκ0 : 0 ≤ κ) :
    ∑ x ∈ s, f x ≤ 2 * (∑ x ∈ s, g x) + 8 * κ := by
  have h := event_mass_diff_sq_le f g s hf hg hf1 hg1
  have hb0 : 0 ≤ ∑ x ∈ s, g x := Finset.sum_nonneg fun x _ => (hg x).le
  have hmax : 0 ≤ max (∑ x ∈ s, f x) (∑ x ∈ s, g x) :=
    le_trans hb0 (le_max_right _ _)
  refine two_le_add_eight_mul _ _ κ hb0 hκ0 ?_
  calc (∑ x ∈ s, f x - ∑ x ∈ s, g x) ^ 2
      ≤ 2 * (∑ x, f x * Real.log (f x / g x)) * max (∑ x ∈ s, f x) (∑ x ∈ s, g x) := h
    _ ≤ 2 * κ * max (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
      refine mul_le_mul_of_nonneg_right ?_ hmax
      linarith

end EventBound

/-! ### Finite tail sums of an `ℕ`-valued volume

The two inequalities below are the elementary content of `E[v] = ∑_{k ≥ 1} P(v ≥ k)`.  They are
stated for a `ℕ`-valued `vol` (the cluster volume `|K|`) with no hypothesis `1 ≤ vol x`, so that
they apply verbatim to any finite approximation. -/

section Volume

variable {α : Type*} [Fintype α]

/-- **The truncated tail-sum identity in exact form.**  For any masses `f` (no positivity needed)
and any `ℕ`-valued volume,
`∑_{k=1}^{n} P(v ≥ k) = E[min (v) n]`.  This is the source's display
`E_{β₁}[|K| ∧ n] = ∑_{k=1}^{n} P_{β₁}(|K| ≥ k)` in the proof of Theorem 1.3. -/
theorem sum_tailMass_eq_expect_min (f : α → ℝ) (vol : α → ℕ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f x)
      = ∑ x, f x * ((min (vol x) n : ℕ) : ℝ) := by
  classical
  have hstep : ∀ k ∈ Finset.Icc 1 n, (∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f x)
      = ∑ x, if k ≤ vol x then f x else 0 := by
    intro k _
    rw [Finset.sum_filter]
  have hinner : ∀ x : α, (∑ k ∈ Finset.Icc 1 n, (if k ≤ vol x then f x else 0))
      = f x * ((((Finset.Icc 1 n).filter (fun k => k ≤ vol x))).card : ℝ) := by
    intro x
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard : ∀ x : α, (((Finset.Icc 1 n).filter (fun k => k ≤ vol x))).card
      = min (vol x) n := by
    intro x
    have hset : (Finset.Icc 1 n).filter (fun k => k ≤ vol x) = Finset.Icc 1 (min (vol x) n) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hset, Nat.card_Icc]
    omega
  calc ∑ k ∈ Finset.Icc 1 n, (∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f x)
      = ∑ k ∈ Finset.Icc 1 n, ∑ x, (if k ≤ vol x then f x else 0) :=
        Finset.sum_congr rfl hstep
    _ = ∑ x, ∑ k ∈ Finset.Icc 1 n, (if k ≤ vol x then f x else 0) := Finset.sum_comm
    _ = ∑ x, f x * (((Finset.Icc 1 n).filter (fun k => k ≤ vol x)).card : ℝ) :=
        Finset.sum_congr rfl fun x _ => hinner x
    _ = ∑ x, f x * ((min (vol x) n : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hcard x]

/-- **The truncated tail-sum identity as an inequality.**  `∑_{k=1}^{n} P(v ≥ k) ≤ E[v]`; this is
`sum_tailMass_eq_expect_min` together with `min (v) n ≤ v`. -/
theorem sum_tailMass_le_expect (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (vol : α → ℕ)
    (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f x)
      ≤ ∑ x, f x * (vol x : ℝ) := by
  rw [sum_tailMass_eq_expect_min]
  refine Finset.sum_le_sum fun x _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hf x)
  exact_mod_cast min_le_left (vol x) n

/-- **Markov's inequality for a `ℕ`-valued volume.**  `n P(v ≥ n) ≤ E[v]`. -/
theorem mul_tailMass_le_expect (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (vol : α → ℕ)
    (n : ℕ) :
    (n : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f x)
      ≤ ∑ x, f x * (vol x : ℝ) := by
  classical
  have h1 : ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f x * (n : ℝ)
      ≤ ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f x * (vol x : ℝ) := by
    refine Finset.sum_le_sum fun x hx => ?_
    have hxn : n ≤ vol x := (Finset.mem_filter.mp hx).2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hxn) (hf x)
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f x * (vol x : ℝ)
      ≤ ∑ x, f x * (vol x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun x _ _ => mul_nonneg (hf x) (Nat.cast_nonneg _)
  calc (n : ℝ) * (∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f x)
      = ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f x * (n : ℝ) := by
        rw [mul_comm, Finset.sum_mul]
    _ ≤ ∑ x, f x * (vol x : ℝ) := le_trans h1 h2

end Volume

/-! ### The finite two-intensity comparison (3.8) and its susceptibility form

`f₁` and `f₂` are the masses of the finite law at intensities `β₁` and `β₂` on a finite
configuration space `α`, and `vol` is the (integer-valued) cluster volume of the origin.  The only
probabilistic input is the relative-entropy budget `hKL`. -/

section Assembly

variable {α : Type*} [Fintype α]

/-- **The finite form of (3.8) of the source.**  For two probability masses on a finite type, an
`ℕ`-valued volume `vol`, intensities `0 < β₁ ≤ β₂` and a constant `A ≥ 0`,
`P₂(v ≥ n) ≤ 2 P₁(v ≥ n) + (4A/β₁)(β₂-β₁)² ∑_{k=1}^{n} P₁(v ≥ k)`, granted the relative-entropy
budget `D(f₂‖f₁) ≤ ((β₂-β₁)²/(2β₁)) A ∑_{k=1}^{n} P₁(v ≥ k)`.  The passage from the budget to
the display is `event_mass_le_of_kl` followed by the identity `8 · (Δβ)²/(2β₁) = 4 (Δβ)²/β₁`.
The hypothesis `β₁ ≤ β₂` is part of the source's statement; the argument itself only uses
`0 < β₁`, so it is bound as `_hβ` here. -/
theorem twoIntensity_tail_le_sum (f₁ f₂ : α → ℝ) (vol : α → ℕ)
    (hf₁ : ∀ x, 0 < f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (h₁ : ∑ x, f₁ x = 1) (h₂ : ∑ x, f₂ x = 1)
    {β₁ β₂ A : ℝ} (hβ₁ : 0 < β₁) (_hβ : β₁ ≤ β₂) (hA : 0 ≤ A) {n : ℕ}
    (hKL : ∑ x, f₂ x * Real.log (f₂ x / f₁ x)
      ≤ (β₂ - β₁) ^ 2 / (2 * β₁) * (A * ∑ k ∈ Finset.Icc 1 n,
          ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x)) :
    ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f₂ x
      ≤ 2 * (∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f₁ x)
        + 4 * A / β₁ * (β₂ - β₁) ^ 2
          * ∑ k ∈ Finset.Icc 1 n,
              ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x := by
  classical
  have hS0 : 0 ≤ ∑ k ∈ Finset.Icc 1 n,
      ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun x _ => (hf₁ x).le
  have hκ0 : 0 ≤ (β₂ - β₁) ^ 2 / (2 * β₁)
      * (A * ∑ k ∈ Finset.Icc 1 n,
          ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x) := by
    have h1 : (0 : ℝ) ≤ (β₂ - β₁) ^ 2 / (2 * β₁) := by positivity
    exact mul_nonneg h1 (mul_nonneg hA hS0)
  have hmain := event_mass_le_of_kl f₂ f₁
    (Finset.univ.filter (fun x => n ≤ vol x)) hf₂ hf₁ h₂ h₁ hKL hκ0
  have hcoef : 8 * ((β₂ - β₁) ^ 2 / (2 * β₁)
      * (A * ∑ k ∈ Finset.Icc 1 n, ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x))
      = 4 * A / β₁ * (β₂ - β₁) ^ 2
        * ∑ k ∈ Finset.Icc 1 n,
            ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x := by
    field_simp
    ring
  linarith [hmain]

/-- **The susceptibility form of the finite two-intensity comparison.**  With the tail-sum
inequalities `∑_{k≤n} P₁(v ≥ k) ≤ E₁ v` and `n P₁(v ≥ n) ≤ E₁ v`, (3.8) gives
`P₂(v ≥ n) ≤ (2/n + (4A/β₁)(β₂-β₁)²) E₁ v`, which is the finite form of
`P_{β₂}(|K| ≥ n) ≤ (2/n + (4/β₁)|β₂-β₁|²) χ_{β₁}` (times `A` in the unnormalised model). -/
theorem twoIntensity_tail_le_susceptibility (f₁ f₂ : α → ℝ) (vol : α → ℕ)
    (hf₁ : ∀ x, 0 < f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x)
    (h₁ : ∑ x, f₁ x = 1) (h₂ : ∑ x, f₂ x = 1)
    {β₁ β₂ A : ℝ} (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (hA : 0 ≤ A)
    {n : ℕ} (hn : 1 ≤ n)
    (hKL : ∑ x, f₂ x * Real.log (f₂ x / f₁ x)
      ≤ (β₂ - β₁) ^ 2 / (2 * β₁) * (A * ∑ k ∈ Finset.Icc 1 n,
          ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x)) :
    ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f₂ x
      ≤ (2 / (n : ℝ) + 4 * A / β₁ * (β₂ - β₁) ^ 2)
        * ∑ x, f₁ x * (vol x : ℝ) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hf₁' : ∀ x, 0 ≤ f₁ x := fun x => (hf₁ x).le
  have hmain := twoIntensity_tail_le_sum f₁ f₂ vol hf₁ hf₂ h₁ h₂ hβ₁ hβ hA hKL
  have hχ0 : 0 ≤ ∑ x, f₁ x * (vol x : ℝ) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hf₁ x).le (Nat.cast_nonneg (vol x))
  have hmarkov := mul_tailMass_le_expect f₁ hf₁' vol n
  have htail := sum_tailMass_le_expect f₁ hf₁' vol n
  have hb : ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f₁ x
      ≤ (∑ x, f₁ x * (vol x : ℝ)) / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    nlinarith [hmarkov]
  have hC : 0 ≤ 4 * A / β₁ * (β₂ - β₁) ^ 2 := by positivity
  calc ∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f₂ x
      ≤ 2 * (∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f₁ x)
        + 4 * A / β₁ * (β₂ - β₁) ^ 2
          * ∑ k ∈ Finset.Icc 1 n,
              ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x := hmain
    _ ≤ 2 * ((∑ x, f₁ x * (vol x : ℝ)) / (n : ℝ))
        + 4 * A / β₁ * (β₂ - β₁) ^ 2 * ∑ x, f₁ x * (vol x : ℝ) := by
        have h1 : 2 * (∑ x ∈ Finset.univ.filter (fun x => n ≤ vol x), f₁ x)
            ≤ 2 * ((∑ x, f₁ x * (vol x : ℝ)) / (n : ℝ)) := by linarith
        have h2 : 4 * A / β₁ * (β₂ - β₁) ^ 2
            * ∑ k ∈ Finset.Icc 1 n, ∑ x ∈ Finset.univ.filter (fun x => k ≤ vol x), f₁ x
            ≤ 4 * A / β₁ * (β₂ - β₁) ^ 2 * ∑ x, f₁ x * (vol x : ℝ) :=
          mul_le_mul_of_nonneg_left htail hC
        linarith
    _ = (2 / (n : ℝ) + 4 * A / β₁ * (β₂ - β₁) ^ 2) * ∑ x, f₁ x * (vol x : ℝ) := by
        ring

end Assembly

/-! ### Instantiation at the finite weighted Bernoulli weights

The two theorems of this section are the previous ones with `f_β = confWeight J β` the product
Bernoulli weight of `Entropy/Bernoulli.lean` on the finite configuration space `E → Bool`; the
probability hypotheses are discharged by `LRP.sum_confWeight` and `LRP.bem_pos`.  The revealment
version isolates the two probabilistic inputs of the source: the transcript relative-entropy
bound `hKL` (Theorem 3.1 / (3.7)) and the revealment estimate `hRev`. -/

section Bernoulli

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- Every configuration of the finite weighted Bernoulli model has strictly positive mass. -/
theorem confWeight_pos {J : E → ℝ} {β : ℝ} (hJ : ∀ e, 0 < J e) (hβ : 0 < β)
    (ω : E → Bool) : 0 < confWeight J β ω := by
  rw [confWeight]
  exact Finset.prod_pos fun e _ => bem_pos hJ hβ e (ω e)

/-- **The finite two-intensity volume-tail comparison at the weighted Bernoulli weights.**
`P_{β₂}(v ≥ n) ≤ (2/n + (4A/β₁)(β₂-β₁)²) E_{β₁} v` for the product Bernoulli weights on a finite
edge set, from the relative-entropy budget `hKL`.  `vol` is the cluster volume of the origin,
which is an independent parameter here: no graph structure is used. -/
theorem finiteBond_tail_twoIntensity (J : E → ℝ) (hJ : ∀ e, 0 < J e)
    (vol : (E → Bool) → ℕ) {β₁ β₂ A : ℝ} (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂)
    (hA : 0 ≤ A) {n : ℕ} (hn : 1 ≤ n)
    (hKL : ∑ ω, confWeight J β₂ ω * Real.log (confWeight J β₂ ω / confWeight J β₁ ω)
      ≤ (β₂ - β₁) ^ 2 / (2 * β₁) * (A * ∑ k ∈ Finset.Icc 1 n,
          ∑ ω ∈ Finset.univ.filter (fun ω => k ≤ vol ω), confWeight J β₁ ω)) :
    ∑ ω ∈ Finset.univ.filter (fun ω => n ≤ vol ω), confWeight J β₂ ω
      ≤ (2 / (n : ℝ) + 4 * A / β₁ * (β₂ - β₁) ^ 2)
        * ∑ ω, confWeight J β₁ ω * (vol ω : ℝ) := by
  have hβ₂ : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ
  exact twoIntensity_tail_le_susceptibility (confWeight J β₁) (confWeight J β₂) vol
    (fun ω => confWeight_pos hJ hβ₁ ω) (fun ω => (confWeight_pos hJ hβ₂ ω).le)
    (sum_confWeight J β₁) (sum_confWeight J β₂) hβ₁ hβ hA hn hKL

/-- **The finite two-intensity comparison from its two named probabilistic inputs.**  The
relative entropy is bounded through a per-edge revealment vector `Rev : E → ℝ` (the source's
`Rev_{β₁}(T,e)` for a decision tree `T` computing `{v ≥ n}`), and the revealment vector is bounded
through the tail sums.  Both inputs are hypotheses; neither is proved in this file. -/
theorem finiteBond_tail_twoIntensity_of_revealment (J : E → ℝ) (hJ : ∀ e, 0 < J e)
    (vol : (E → Bool) → ℕ) (Rev : E → ℝ) {β₁ β₂ A : ℝ} (hβ₁ : 0 < β₁)
    (hβ : β₁ ≤ β₂)
    (hA : 0 ≤ A) {n : ℕ} (hn : 1 ≤ n)
    (hKL : ∑ ω, confWeight J β₂ ω * Real.log (confWeight J β₂ ω / confWeight J β₁ ω)
      ≤ (β₂ - β₁) ^ 2 / (2 * β₁) * ∑ e, J e * Rev e)
    (hRev : ∑ e, J e * Rev e
      ≤ A * ∑ k ∈ Finset.Icc 1 n,
          ∑ ω ∈ Finset.univ.filter (fun ω => k ≤ vol ω), confWeight J β₁ ω) :
    ∑ ω ∈ Finset.univ.filter (fun ω => n ≤ vol ω), confWeight J β₂ ω
      ≤ (2 / (n : ℝ) + 4 * A / β₁ * (β₂ - β₁) ^ 2)
        * ∑ ω, confWeight J β₁ ω * (vol ω : ℝ) := by
  have hc : (0 : ℝ) ≤ (β₂ - β₁) ^ 2 / (2 * β₁) := by positivity
  exact finiteBond_tail_twoIntensity J hJ vol hβ₁ hβ hA hn
    (le_trans hKL (mul_le_mul_of_nonneg_left hRev hc))

end Bernoulli

/-! ### A consistency witness

The finite comparison is not vacuous: below, all of its hypotheses are discharged simultaneously on
a two-point space with a non-constant volume.  This is necessarily the degenerate case
`β₁ = β₂` (hence zero relative entropy); the case `β₁ < β₂` at a genuine one-edge model requires
the per-edge Bernoulli estimate of Lemma 3.3 of the source, which is *not* proved in this file. -/

/-- **Witness.**  On `α = Bool` with `vol = (if ω = true then 2 else 1)`, constant masses `1/2`,
`β₁ = β₂ = 1`, `A = 1` and `n = 1`, the hypotheses of `LRP.twoIntensity_tail_le_susceptibility`
hold and its conclusion reads `1 ≤ 3`. -/
theorem twoIntensity_tail_le_susceptibility_witness :
    (∑ _ω ∈ Finset.univ.filter (fun ω : Bool => 1 ≤ (if ω = true then 2 else 1)),
        (1 / 2 : ℝ))
      ≤ (2 / ((1 : ℕ) : ℝ) + 4 * 1 / 1 * ((1 : ℝ) - 1) ^ 2)
        * ∑ ω : Bool, (1 / 2 : ℝ)
            * (((if ω = true then 2 else 1) : ℕ) : ℝ) := by
  refine twoIntensity_tail_le_susceptibility (α := Bool) (f₁ := fun _ => (1 / 2 : ℝ))
    (f₂ := fun _ => (1 / 2 : ℝ)) (vol := fun ω => if ω = true then 2 else 1)
    (β₁ := 1) (β₂ := 1) (A := 1) (n := 1) (fun _ => by norm_num) (fun _ => by norm_num)
    ?_ ?_ one_pos le_rfl zero_le_one le_rfl ?_
  · rw [Fintype.sum_bool]; norm_num
  · rw [Fintype.sum_bool]; norm_num
  · norm_num

/-! ### The countable form needed for a transcript space

The transcript `X = (X_1, X_2, …)` in the source's proof takes values in the *countable* space
`{0,1,∅}^ℕ`, so the finite-sum form of (3.2) proved above does not apply to the laws of `X` and
`Y` directly.  This section proves the countable form: the log-sum inequality for countable sums,
the coarse-graining of the relative entropy to an event, and the event bound `a ≤ 2b + 8κ`.  The
proofs are the finite ones with `∑` replaced by `∑'`; the degenerate cases use that a strictly
positive mass on a subtype of zero total mass forces the subtype to be empty. -/

section CountableTranscript

variable {α : Type*}

/-- A `tsum` over an empty subtype vanishes. -/
theorem tsum_subtype_empty (f : α → ℝ) : (∑' x : {x // x ∈ (∅ : Set α)}, f x) = 0 := by
  rw [_root_.tsum_subtype]
  simp

/-- A `tsum` over a subtype whose carrier is empty vanishes. -/
theorem tsum_subtype_of_eq_empty {s : Set α} (f : α → ℝ) (hs : s = ∅) :
    (∑' x : s, f x) = 0 := by
  subst hs
  exact tsum_subtype_empty f

/-- **Log-sum inequality for countable sums**. -/
theorem log_sum_ineq_tsum {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x)
    (hfs : Summable f) (hgs : Summable g)
    (hkls : Summable fun x => f x * Real.log (f x / g x))
    (hF : 0 < ∑' x, f x) (hG : 0 < ∑' x, g x) :
    (∑' x, f x) * Real.log ((∑' x, f x) / (∑' x, g x))
      ≤ ∑' x, f x * Real.log (f x / g x) := by
  classical
  have hc : 0 < (∑' x, f x) / (∑' x, g x) := div_pos hF hG
  have hpt : ∀ x, f x - ((∑' y, f y) / (∑' y, g y)) * g x
      ≤ f x * Real.log ((f x / g x) / ((∑' y, f y) / (∑' y, g y))) := by
    intro x
    rcases eq_or_lt_of_le (hf x) with h0 | hpos
    · rw [← h0]
      simp only [zero_mul, zero_sub, neg_le_iff_add_nonneg, zero_add]
      exact mul_nonneg hc.le (le_of_lt (hg x))
    · have hlog := one_sub_inv_le_log (div_pos (div_pos hpos (hg x)) hc)
      have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
      have hkey : f x * (1 - ((f x / g x) / ((∑' y, f y) / (∑' y, g y)))⁻¹)
          = f x - ((∑' y, f y) / (∑' y, g y)) * g x := by
        field_simp
      rwa [hkey] at hmul
  have hgc : Summable fun x => ((∑' y, f y) / (∑' y, g y)) * g x := hgs.mul_left _
  have hsub : Summable fun x => f x - ((∑' y, f y) / (∑' y, g y)) * g x := hfs.sub hgc
  have hpt2 : ∀ x, f x * Real.log ((f x / g x) / ((∑' y, f y) / (∑' y, g y)))
      = f x * Real.log (f x / g x) - f x * Real.log ((∑' y, f y) / (∑' y, g y)) := by
    intro x
    rcases eq_or_lt_of_le (hf x) with h0 | hpos
    · rw [← h0]; simp
    · rw [Real.log_div (ne_of_gt (div_pos hpos (hg x))) (ne_of_gt hc), mul_sub]
  have hsum2 : Summable fun x =>
      f x * Real.log ((f x / g x) / ((∑' y, f y) / (∑' y, g y))) :=
    (hkls.sub (hfs.mul_right _)).congr fun x => (hpt2 x).symm
  have hL : ∑' x, (f x - ((∑' y, f y) / (∑' y, g y)) * g x) = 0 := by
    rw [hfs.tsum_sub hgc, tsum_mul_left]
    field_simp
    ring
  have hkey : 0 ≤ ∑' x, f x * Real.log ((f x / g x) / ((∑' y, f y) / (∑' y, g y))) := by
    rw [← hL]
    exact hsub.tsum_le_tsum hpt hsum2
  have hsplit : ∑' x, f x * Real.log ((f x / g x) / ((∑' y, f y) / (∑' y, g y)))
      = (∑' x, f x * Real.log (f x / g x))
        - (∑' x, f x) * Real.log ((∑' y, f y) / (∑' y, g y)) := by
    calc ∑' x, f x * Real.log ((f x / g x) / ((∑' y, f y) / (∑' y, g y)))
        = ∑' x, (f x * Real.log (f x / g x)
            - f x * Real.log ((∑' y, f y) / (∑' y, g y))) := tsum_congr hpt2
      _ = (∑' x, f x * Real.log (f x / g x))
            - ∑' x, f x * Real.log ((∑' y, f y) / (∑' y, g y)) :=
          hkls.tsum_sub (hfs.mul_right _)
      _ = (∑' x, f x * Real.log (f x / g x))
            - (∑' x, f x) * Real.log ((∑' y, f y) / (∑' y, g y)) := by rw [tsum_mul_right]
  rw [hsplit] at hkey
  linarith

/-- A subtype carrying a strictly positive function of zero total mass is empty. -/
theorem eq_empty_of_tsum_subtype_eq_zero {s : Set α} {g : α → ℝ} (hg : ∀ x, 0 < g x)
    (hgs : Summable g) (h : ∑' x : s, g x = 0) : s = ∅ := by
  rcases s.eq_empty_or_nonempty with h0 | ⟨x, hx⟩
  · exact h0
  · exact absurd h (ne_of_gt (Summable.tsum_pos (hgs.subtype _) (fun y => (hg _).le)
      ⟨x, hx⟩ (hg x)))

/-- A nonnegative function of zero total mass on a subtype vanishes there. -/
theorem eq_zero_of_tsum_subtype_eq_zero {s : Set α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hfs : Summable f) (h : ∑' x : s, f x = 0) {x : α} (hx : x ∈ s) : f x = 0 := by
  by_contra hne
  exact absurd h (ne_of_gt (Summable.tsum_pos (hfs.subtype _) (fun y => hf _)
    ⟨x, hx⟩ (lt_of_le_of_ne (hf x) (Ne.symm hne))))


/-- **Two-bin coarse-graining of the countable relative entropy.** -/
theorem bkl_eventMass_le_kl_tsum {f g : α → ℝ} (s : Set α) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 < g x) (hfs : Summable f) (hgs : Summable g)
    (hkls : Summable fun x => f x * Real.log (f x / g x))
    (hsplit_f : ∑' x : (sᶜ : Set α), f x = 1 - ∑' x : s, f x)
    (hsplit_g : ∑' x : (sᶜ : Set α), g x = 1 - ∑' x : s, g x)
    (hB : 0 < ∑' x : s, g x) (hBc : 0 < ∑' x : (sᶜ : Set α), g x) :
    bkl (∑' x : s, f x) (∑' x : s, g x) ≤ ∑' x, f x * Real.log (f x / g x) := by
  classical
  have hfS : Summable fun x : s => f x := hfs.subtype _
  have hgS : Summable fun x : s => g x := hgs.subtype _
  have hfT : Summable fun x : (sᶜ : Set α) => f x := hfs.subtype _
  have hgT : Summable fun x : (sᶜ : Set α) => g x := hgs.subtype _
  have hklS : Summable fun x : s => f x * Real.log (f x / g x) := hkls.subtype _
  have hklT : Summable fun x : (sᶜ : Set α) => f x * Real.log (f x / g x) := hkls.subtype _
  have hA0 : 0 ≤ ∑' x : s, f x := tsum_nonneg fun y => hf _
  have hAc0 : 0 ≤ ∑' x : (sᶜ : Set α), f x := tsum_nonneg fun y => hf _
  have h1 : (∑' x : s, f x) * Real.log ((∑' x : s, f x) / (∑' x : s, g x))
      ≤ ∑' x : s, f x * Real.log (f x / g x) := by
    rcases eq_or_lt_of_le hA0 with h0 | hpos
    · have hz : ∀ y : s, f y = 0 := fun y =>
        eq_zero_of_tsum_subtype_eq_zero (fun x => hf x) hfs h0.symm y.2
      have hsum0 : (∑' x : s, f x * Real.log (f x / g x)) = 0 := by
        have hcongr : (∑' x : s, f x * Real.log (f x / g x)) = ∑' _x : s, (0 : ℝ) :=
          tsum_congr fun y => by rw [hz y, zero_mul]
        rw [hcongr, tsum_zero]
      rw [← h0, hsum0]
      simp
    · exact log_sum_ineq_tsum (fun y => hf _) (fun y => hg _) hfS hgS hklS hpos hB
  have h2 : (∑' x : (sᶜ : Set α), f x)
        * Real.log ((∑' x : (sᶜ : Set α), f x) / (∑' x : (sᶜ : Set α), g x))
      ≤ ∑' x : (sᶜ : Set α), f x * Real.log (f x / g x) := by
    rcases eq_or_lt_of_le hAc0 with h0 | hpos
    · have hz : ∀ y : (sᶜ : Set α), f y = 0 := fun y =>
        eq_zero_of_tsum_subtype_eq_zero (fun x => hf x) hfs h0.symm y.2
      have hsum0 : (∑' x : (sᶜ : Set α), f x * Real.log (f x / g x)) = 0 := by
        have hcongr : (∑' x : (sᶜ : Set α), f x * Real.log (f x / g x))
            = ∑' _x : (sᶜ : Set α), (0 : ℝ) :=
          tsum_congr fun y => by rw [hz y, zero_mul]
        rw [hcongr, tsum_zero]
      rw [← h0, hsum0]
      simp
    · exact log_sum_ineq_tsum (fun y => hf _) (fun y => hg _) hfT hgT hklT hpos hBc
  have hsplit := hkls.tsum_subtype_add_tsum_subtype_compl s
  rw [bkl, ← hsplit_f, ← hsplit_g]
  linarith

/-- **The countable form of the event bound `a ≤ 2b + 8κ`.**  This is the form of the
generalised Pinsker step that applies to the laws of the source's infinite transcripts. -/
theorem event_mass_le_of_kl_tsum {f g : α → ℝ} (s : Set α) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 < g x) (hfs : Summable f) (hgs : Summable g)
    (hf1 : ∑' x, f x = 1) (hg1 : ∑' x, g x = 1)
    (hkls : Summable fun x => f x * Real.log (f x / g x))
    {κ : ℝ} (hκ : ∑' x, f x * Real.log (f x / g x) ≤ κ) (hκ0 : 0 ≤ κ) :
    ∑' x : s, f x ≤ 2 * (∑' x : s, g x) + 8 * κ := by
  classical
  have hFs : (∑' x : s, f x) + (∑' x : (sᶜ : Set α), f x) = 1 :=
    (hfs.tsum_subtype_add_tsum_subtype_compl s).trans hf1
  have hGs : (∑' x : s, g x) + (∑' x : (sᶜ : Set α), g x) = 1 :=
    (hgs.tsum_subtype_add_tsum_subtype_compl s).trans hg1
  have hA0 : 0 ≤ ∑' x : s, f x := tsum_nonneg fun y => hf _
  have hAc0 : 0 ≤ ∑' x : (sᶜ : Set α), f x := tsum_nonneg fun y => hf _
  have hB0 : 0 ≤ ∑' x : s, g x := tsum_nonneg fun y => (hg _).le
  have hBc0 : 0 ≤ ∑' x : (sᶜ : Set α), g x := tsum_nonneg fun y => (hg _).le
  rcases eq_or_lt_of_le hB0 with hBzero | hBpos
  · -- `B = 0` forces `s = ∅`, hence `A = 0`
    have hs : s = ∅ := eq_empty_of_tsum_subtype_eq_zero hg hgs hBzero.symm
    have hAz : ∑' x : s, f x = 0 := tsum_subtype_of_eq_empty f hs
    rw [hAz, ← hBzero]
    simp only [mul_zero, zero_add]
    linarith
  rcases lt_or_ge (∑' x : s, g x) 1 with hBone_lt | hBone_ge
  · -- interior case `0 < B < 1`
    have hsplit_f : ∑' x : (sᶜ : Set α), f x = 1 - ∑' x : s, f x := by linarith
    have hsplit_g : ∑' x : (sᶜ : Set α), g x = 1 - ∑' x : s, g x := by linarith
    have hBc : 0 < ∑' x : (sᶜ : Set α), g x := by linarith
    have hA1 : ∑' x : s, f x ≤ 1 := by linarith
    have hbin := binary_kl_sq_le' hA0 hA1 hBpos hBone_lt
    have hcl := bkl_eventMass_le_kl_tsum s hf hg hfs hgs hkls hsplit_f hsplit_g hBpos hBc
    have hmax : 0 ≤ max (∑' x : s, f x) (∑' x : s, g x) := le_trans hB0 (le_max_right _ _)
    have hsq : ((∑' x : s, f x) - (∑' x : s, g x)) ^ 2
        ≤ 2 * κ * max (∑' x : s, f x) (∑' x : s, g x) := by
      have hstep : (∑' x : s, f x - ∑' x : s, g x) ^ 2
          ≤ 2 * max (∑' x : s, f x) (∑' x : s, g x)
            * (∑' x, f x * Real.log (f x / g x)) := le_trans hbin (by
              refine mul_le_mul_of_nonneg_left hcl ?_
              linarith)
      calc ((∑' x : s, f x) - (∑' x : s, g x)) ^ 2
          ≤ 2 * max (∑' x : s, f x) (∑' x : s, g x)
            * (∑' x, f x * Real.log (f x / g x)) := hstep
        _ ≤ 2 * max (∑' x : s, f x) (∑' x : s, g x) * κ := by
            refine mul_le_mul_of_nonneg_left hκ ?_
            linarith
        _ = 2 * κ * max (∑' x : s, f x) (∑' x : s, g x) := by ring
    exact two_le_add_eight_mul _ _ κ hB0 hκ0 hsq
  · -- `B = 1` forces `A = 1`
    have hBone : ∑' x : s, g x = 1 := le_antisymm (by linarith) hBone_ge
    have hBcz : ∑' x : (sᶜ : Set α), g x = 0 := by linarith
    have hs : sᶜ = ∅ := eq_empty_of_tsum_subtype_eq_zero hg hgs hBcz
    have hAcz : ∑' x : (sᶜ : Set α), f x = 0 := tsum_subtype_of_eq_empty f hs
    have hAone : ∑' x : s, f x = 1 := by linarith
    rw [hAone, hBone]
    linarith

end CountableTranscript

/-! ### What is still needed for the canonical infinite-volume model

Every theorem above lives on a *finite* probability space (two masses `f₁`, `f₂` on a finite type
`α`, or the product Bernoulli weights `confWeight J β` on `E → Bool` for a finite edge type `E`),
except the countable section, which lives on a countable type but still with honest `tsum`s.
The canonical long-range model of the source is a product measure `P_β` on `{0,1}^E` for a
countable weighted graph `G = (V, E, J)`; production's interface is `SourceModelData`, whose
`M.law β` is a probability measure on `Config M.V` and whose `M.lawTail β n` is
`P_β(|K_0| ≥ n)`.  Four inputs were isolated here for the passage to
`SourceModelData.TwoIntensityTailComparison A`.  The first three are not proved in this file.
The sibling module `CriticalVolumeTail/CanonicalTail` has since discharged the fourth: its
extended-nonnegative tail and Markov bounds are unconditional, while its real-valued forms state
the necessary `lawSusceptibility β ≠ ⊤` hypothesis.

1. *The transcript relative-entropy bound (3.7) of the source.*  Fix a decision tree `T` and
   `0 < β₁ ≤ β₂`, let `ω₁, ω₂` be sampled from `P_{β₁}, P_{β₂}`, let `T_1, T_2, …` be the queried
   edges and set `X_i = ω₂(T_i)`, `Y_i = ω₁(T_i)`, padded with `∅` after halting.  Then
   `X = (X_1, X_2, …)` and `Y = (Y_1, Y_2, …)` take values in `{0,1,∅}^ℕ`, and the required input
   is `D_KL(X‖Y) ≤ ((β₂-β₁)²/(2β₁)) ∑_e J_e Rev_{β₁}(T,e)`, the hypothesis `hKL` above.
   The source obtains it from the chain rule (3.3) over the query index, the per-edge Bernoulli
   estimate of Lemma 3.3, and the limit `k → ∞` justified by lower semicontinuity of the relative
   entropy.  The finite chain rule is direction (B) of this swarm and Lemma 3.3 is direction (A);
   the `k → ∞` step needs the countable transcript space.  Note that this input *implies* that the
   law of `X` is absolutely continuous with respect to that of `Y`; absolute continuity is a
   consequence of a finite relative entropy, not a separate hypothesis.
2. *The event is computed by the tree.*  `{ω : |K_0(ω)| ≥ n}` must be Borel-computed by `T` in the
   source's sense, giving `𝒜 ⊆ {0,1,∅}^ℕ` with `P_{β₁}(|K_0| ≥ n) = P(Y ∈ 𝒜)` and
   `P_{β₂}(|K_0| ≥ n) = P(X ∈ 𝒜)`.  Here `vol` stands for `|K_0|` and is an opaque parameter, so
   this identification is entirely outside the present file; in particular the finite Bernoulli
   model has no cluster structure at all.
3. *The revealment estimate.*  `∑_e J_e Rev_{β₁}(T,e) ≤ A ∑_{k ≤ n} P_{β₁}(|K_0| ≥ k)` with
   `A = ∑_{e ∈ E^→_o} J_e`; this is the hypothesis `hRev` above and is direction (C).
4. *The layer-cake identity for the infinite susceptibility — now supplied by `CanonicalTail`.*
   Passing the truncated tail sum
   `∑_{k ≤ n} P_{β₁}(|K_0| ≥ k)` to `χ_{β₁} = E_{β₁}|K_0|` at the level of production's
   `ℝ≥0∞`-valued `lawSusceptibility` needs the layer-cake identity
   `E|K_0| = ∑_{k ≥ 1} P(|K_0| ≥ k)` for a `ℕ`-valued random variable on an infinite measure
   space, together with summability of the tail series and `P(|K_0| ≥ n) ≤ χ/n`.
   `CanonicalTail` proves these at `M.law β`, at the cutoff law, and for monotone finite-window
   exhaustions.  The tail sum and Markov bounds given there, rather than the finite forms in this
   file, are therefore the appropriate canonical-model ingredients.

At the level of *paths* the step from relative entropy to the event bound is available in the form
needed: `event_mass_le_of_kl_tsum` gives `P(X ∈ 𝒜) ≤ 2 P(Y ∈ 𝒜) + 8 κ` for any subset `𝒜` of a
countable space and any relative-entropy budget `κ`, with the degenerate cases handled.  Granted
(1)–(4), the numerical assembly proved in this file is exactly what the source does next:
`two_le_add_eight_mul` turns (3.9) into
`P_{β₂}(|K_0| ≥ n) ≤ 2 P_{β₁}(|K_0| ≥ n) + (4A/β₁)(β₂-β₁)² ∑_{k≤n} P_{β₁}(|K_0| ≥ k)`
(this is `twoIntensity_tail_le_sum`, or `event_mass_le_of_kl_tsum` followed by the same algebra in
the countable setting, with `f_β` the law of the transcript and `vol = |K_0|`), and
`mul_tailMass_le_expect` together with `sum_tailMass_le_expect` turns that into
`(2/n + (4A/β₁)(β₂-β₁)²) χ_{β₁}`, which is `SourceModelData.TwoIntensityTailComparison A`. -/

end LRP

namespace LRP

set_option linter.hashCommand false in
#print axioms LRP.eq_empty_of_sum_eq_zero

set_option linter.hashCommand false in
#print axioms LRP.kl_nonneg

set_option linter.hashCommand false in
#print axioms LRP.bkl_eventMass_le_kl

set_option linter.hashCommand false in
#print axioms LRP.event_mass_diff_sq_le

set_option linter.hashCommand false in
#print axioms LRP.two_le_add_eight_mul

set_option linter.hashCommand false in
#print axioms LRP.event_mass_le_of_kl

set_option linter.hashCommand false in
#print axioms LRP.sum_tailMass_eq_expect_min

set_option linter.hashCommand false in
#print axioms LRP.sum_tailMass_le_expect

set_option linter.hashCommand false in
#print axioms LRP.mul_tailMass_le_expect

set_option linter.hashCommand false in
#print axioms LRP.tsum_subtype_empty

set_option linter.hashCommand false in
#print axioms LRP.tsum_subtype_of_eq_empty

set_option linter.hashCommand false in
#print axioms LRP.log_sum_ineq_tsum

set_option linter.hashCommand false in
#print axioms LRP.eq_empty_of_tsum_subtype_eq_zero

set_option linter.hashCommand false in
#print axioms LRP.eq_zero_of_tsum_subtype_eq_zero

set_option linter.hashCommand false in
#print axioms LRP.bkl_eventMass_le_kl_tsum

set_option linter.hashCommand false in
#print axioms LRP.event_mass_le_of_kl_tsum

set_option linter.hashCommand false in
#print axioms LRP.twoIntensity_tail_le_sum

set_option linter.hashCommand false in
#print axioms LRP.twoIntensity_tail_le_susceptibility

set_option linter.hashCommand false in
#print axioms LRP.confWeight_pos

set_option linter.hashCommand false in
#print axioms LRP.finiteBond_tail_twoIntensity

set_option linter.hashCommand false in
#print axioms LRP.finiteBond_tail_twoIntensity_of_revealment

set_option linter.hashCommand false in
#print axioms LRP.twoIntensity_tail_le_susceptibility_witness

end LRP
