/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Definitions for the scalar envelope and finite configuration weights.

Accepted from independent submission `smwp9xgrt` direction D2.
These are finite-configuration and scalar ingredients, not an infinite-volume
cluster-moment theorem.  The adapted-revelation and exploration bridges remain open.
-/
module

/-
Definitions for the frontier-exploration branching envelope of `PROOF.md`
(swarm smwp9xgrt, member m2, direction d2).

This file lives in the member directory and is imported by no production module; it changes
nothing outside `.ultramath/smwp9xgrt/m2/`.
-/
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

@[expose] public section

open Finset

namespace PercLib.Probability.ExplorationEnvelope

/-- One step of the envelope recursion: `u ↦ exp (m * (λ * u - 1))`. -/
noncomputable def envelopeStep (m lam u : ℝ) : ℝ := Real.exp (m * (lam * u - 1))

/-- The envelope sequence `u_0 = 1`, `u_{n+1} = exp (m * (λ * u_n - 1))` of `PROOF.md` (5.1).
It is the number of "units of λ-weight" carried by one vertex of the frontier after `n`
generations of the exploration. -/
noncomputable def envelope (m lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | (n + 1) => envelopeStep m lam (envelope m lam n)

@[simp]
theorem envelope_zero (m lam : ℝ) : envelope m lam 0 = 1 := rfl

theorem envelope_succ (m lam : ℝ) (n : ℕ) :
    envelope m lam (n + 1) = envelopeStep m lam (envelope m lam n) := rfl

/-- **Uniform real row-sum hypothesis** (R_m) of `PROOF.md` §1, stated as "every finite partial row
sum is at most `m`". For a nonnegative kernel this is the same as `∑_y p x y ≤ m` and it avoids
the junk value of `sSup` for an unbounded row. -/
def UniformRowSum {V : Type*} (p : V → V → ℝ) (m : ℝ) : Prop :=
  ∀ x : V, ∀ s : Finset V, ∑ y ∈ s, p x y ≤ m

/-- Weight of a finite open-edge configuration under independent Bernoulli edge probabilities. -/
noncomputable def configWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (s : Finset ι) : ℝ :=
  (∏ e ∈ s, p e) * ∏ e ∈ sᶜ, (1 - p e)

end PercLib.Probability.ExplorationEnvelope

namespace PercLib.Probability.ExplorationEnvelope

/-- Exact probability of the configuration `s ⊆ ι` times `t^{#(open edges of s inside S)}`:
the `S`-tilted configuration weight, used for the per-vertex Poisson domination
(`PROOF.md` Lemma 4.4 with the edge set `S` and `t ≥ 1`). -/
noncomputable def tiltedWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (t : ℝ) (S s : Finset ι) : ℝ :=
  (∏ e ∈ s, p e * (if e ∈ S then t else 1)) * ∏ e ∈ sᶜ, (1 - p e)

end PercLib.Probability.ExplorationEnvelope
