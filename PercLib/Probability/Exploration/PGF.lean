/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Finite Bernoulli generating functions and their Poisson exponential bound.

Accepted from independent submission `smwp9xgrt` direction D2.
These are finite-configuration and scalar ingredients, not an infinite-volume
cluster-moment theorem.  The adapted-revelation and exploration bridges remain open.
-/
module

/-
`PROOF.md` Lemma 4.2 and 4.3: the pgf of a sum of independent Bernoulli variables over a finite
edge set, in exact finite-configuration form, and its exponential bound.

This is the whole *analytic* content of the one-step estimate `PROOF.md` Lemma 4.4: it says
`E[t^{#open edges in S}] = ∏_{e∈S}(1 + p_e (t-1)) ≤ exp((t-1) ∑_{e∈S} p_e)` for `t ≥ 1`.
It is stated for a finite edge set; it does not by itself bound the size of an infinite cluster.
-/
public import PercLib.Probability.Exploration.Envelope.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

@[expose] public section

open Finset

namespace PercLib.Probability.ExplorationEnvelope

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Pointwise comparison of finite products of nonnegative reals (the ordered-monoid
`Finset.prod_le_prod` does not apply to `ℝ`, so we prove the nonnegative version once). -/
theorem prod_le_prod_of_nonneg {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hmem : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hga : 0 ≤ g a := le_trans hfa (hfg a (Finset.mem_insert_self a s))
    have ihs : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (hmem i hi)) (fun i hi => hfg i (hmem i hi))
    have hfs : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hf i (hmem i hi))
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s)) ihs hfs hga

/-- Expand the product of the two binomial factors. Auxiliary form of `PROOF.md` Lemma 4.2. -/
theorem prod_one_add_mul_sub_one_eq_sum (p : ι → ℝ) (t : ℝ) :
    ∏ e, (1 + p e * (t - 1))
      = ∑ s ∈ (univ : Finset ι).powerset,
          (∏ i ∈ s, p i * t) * ∏ i ∈ (univ : Finset ι) \ s, (1 - p i) := by
  rw [← Finset.prod_add (fun e => p e * t) (fun e => 1 - p e) (univ : Finset ι)]
  refine Finset.prod_congr rfl ?_
  intro e _
  ring

/-- **`PROOF.md` Lemma 4.2 (Bernoulli-sum pgf identity, finite-configuration form).**
Summing the exact configuration weight times `t^{#open}` over all configurations gives the
product `∏_e (1 + p_e (t-1))`, i.e. `E[t^{#open}]` for independent edge variables. -/
theorem sum_configWeight_mul_pow (p : ι → ℝ) (t : ℝ) :
    ∑ s ∈ (univ : Finset ι).powerset, configWeight p s * t ^ s.card
      = ∏ e, (1 + p e * (t - 1)) := by
  rw [prod_one_add_mul_sub_one_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [configWeight, Finset.compl_eq_univ_sdiff, Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- **`PROOF.md` Lemma 4.3.** The Bernoulli-sum pgf is bounded by the Poisson(`(t-1)∑p`) pgf:
`∏_e (1 + p_e (t-1)) ≤ exp ((t-1) ∑_e p_e)` for `0 ≤ p_e ≤ 1` and `t ≥ 1`. -/
theorem sum_configWeight_mul_pow_le (p : ι → ℝ) (t : ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (ht : 1 ≤ t) :
    ∑ s ∈ (univ : Finset ι).powerset, configWeight p s * t ^ s.card
      ≤ Real.exp ((t - 1) * ∑ e, p e) := by
  rw [sum_configWeight_mul_pow]
  have hle : ∀ e ∈ (univ : Finset ι), 1 + p e * (t - 1) ≤ Real.exp (p e * (t - 1)) := by
    intro e _
    have h := Real.add_one_le_exp (p e * (t - 1))
    linarith
  have hnn : ∀ e ∈ (univ : Finset ι), (0:ℝ) ≤ 1 + p e * (t - 1) := by
    intro e _
    have : 0 ≤ p e * (t - 1) := mul_nonneg (hp0 e) (by linarith)
    linarith
  refine le_trans (prod_le_prod_of_nonneg hnn hle) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun e _ => by
    have := mul_le_mul_of_nonneg_right (hp1 e) (by linarith : (0:ℝ) ≤ t - 1)
    linarith)

end PercLib.Probability.ExplorationEnvelope

namespace PercLib.Probability.ExplorationEnvelope

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`PROOF.md` Lemma 4.4, per-vertex form, exactly computed.** For a finite set `S` of edges and
`t ≥ 1`, the `S`-tilted total configuration weight is `∏_{e∈S}(1 + p_e (t-1))`, i.e. the pgf of
`#(open edges of S)`. -/
theorem sum_tiltedWeight_eq_prod (p : ι → ℝ) (t : ℝ) (S : Finset ι) :
    ∑ s ∈ (univ : Finset ι).powerset, tiltedWeight p t S s
      = ∏ e ∈ S, (1 + p e * (t - 1)) := by
  have hmain : ∏ e ∈ (univ : Finset ι), (p e * (if e ∈ S then t else 1) + (1 - p e))
      = ∑ s ∈ (univ : Finset ι).powerset,
          (∏ i ∈ s, p i * (if i ∈ S then t else 1))
            * ∏ i ∈ (univ : Finset ι) \ s, (1 - p i) :=
    Finset.prod_add _ _ _
  have hstep : (∑ s ∈ (univ : Finset ι).powerset, tiltedWeight p t S s)
      = ∑ s ∈ (univ : Finset ι).powerset,
          (∏ i ∈ s, p i * (if i ∈ S then t else 1))
            * ∏ i ∈ (univ : Finset ι) \ s, (1 - p i) := by
    refine Finset.sum_congr rfl ?_
    intro s _
    rw [tiltedWeight, Finset.compl_eq_univ_sdiff]
  have hfun : ∀ e, p e * (if e ∈ S then t else 1) + (1 - p e)
      = if e ∈ S then (1 + p e * (t - 1)) else 1 := by
    intro e
    by_cases h : e ∈ S
    · simp [h]; ring
    · simp [h]
  have hprod : (∏ e ∈ (univ : Finset ι), (p e * (if e ∈ S then t else 1) + (1 - p e)))
      = ∏ e, (if e ∈ S then (1 + p e * (t - 1)) else 1) :=
    Finset.prod_congr rfl (fun e _ => hfun e)
  have hg : (∏ e, (if e ∈ S then (1 + p e * (t - 1)) else 1))
      = ∏ e ∈ S, (1 + p e * (t - 1)) := by
    rw [← Finset.prod_subset (f := fun e => if e ∈ S then (1 + p e * (t - 1)) else 1)
      (s₁ := S) (s₂ := (univ : Finset ι)) (Finset.subset_univ S) (fun x _ hx => by simp [hx])]
    exact Finset.prod_congr rfl (fun e he => by simp [he])
  rw [hstep, ← hmain, hprod, hg]

/-- **`PROOF.md` §4, per-vertex Poisson domination.** If the edge parameters inside `S` sum to at
most `m`, then for `t ≥ 1` the tilted weight of the number of open edges of `S` is at most
`exp ((t-1) m)` — the pgf of a Poisson(`m`) variable at `t`. This is the per-vertex input of the
frontier exploration, in exact finite-configuration form. -/
theorem sum_tiltedWeight_le_exp (p : ι → ℝ) (t : ℝ) (S : Finset ι) {m : ℝ}
    (hp0 : ∀ e, 0 ≤ p e) (ht : 1 ≤ t) (hS : ∑ e ∈ S, p e ≤ m) :
    ∑ s ∈ (univ : Finset ι).powerset, tiltedWeight p t S s ≤ Real.exp ((t - 1) * m) := by
  rw [sum_tiltedWeight_eq_prod]
  have hle : ∀ e ∈ S, 1 + p e * (t - 1) ≤ Real.exp (p e * (t - 1)) := by
    intro e _
    have h := Real.add_one_le_exp (p e * (t - 1))
    linarith
  have hnn : ∀ e ∈ S, (0:ℝ) ≤ 1 + p e * (t - 1) := by
    intro e _
    have : 0 ≤ p e * (t - 1) := mul_nonneg (hp0 e) (by linarith)
    linarith
  refine le_trans (prod_le_prod_of_nonneg hnn hle) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hsum : ∑ e ∈ S, p e * (t - 1) = (∑ e ∈ S, p e) * (t - 1) := by
    rw [Finset.sum_mul]
  rw [hsum, mul_comm (∑ e ∈ S, p e) (t - 1)]
  exact mul_le_mul_of_nonneg_left hS (by linarith : (0:ℝ) ≤ t - 1)

end PercLib.Probability.ExplorationEnvelope
