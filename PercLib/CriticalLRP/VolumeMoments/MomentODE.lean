/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1 — the triangular system of moment ODEs (I.1.3) / (I.4.4) and
its exact solution.

The paper (p. 8) writes the limiting system of ODEs for the critical cut-off
cluster-volume moments as

  (I.1.3)  (d/dr) E_{βc,r}|K|^p ~ βc r^{-α-1} ∑_{ℓ=0}^{p-1} C(p,ℓ)
             E_{βc,r}|K|^{ℓ+1} E_{βc,r}|K|^{p-ℓ},

and Theorem I.1.6 states (verified against the arXiv LaTeX source
`Zd_renormalizationHD.tex`, `\label{eq:hd_moments_main}`)

  (I.1.6)  E_{βc,r}|K|^p ~ (2p-3)!! A^{p-1} (α/βc) r^{(2p-1)α}.

This file proves that the right-hand side of (I.1.6), with `A` replaced by an
arbitrary constant `B`, is an *exact* solution of the system (I.1.3) — for every
`B`, with no error term.  Consequences:

* `B` is free: the system does not determine `A` (cf. Remark I.1.8: `A` is
  non-universal, it is the exponential of an error integral).
* For `p = 1` the formula is `(α/β) r^α`, i.e. Proposition I.4.2's asymptotic
  first moment `E_{βc,r}|K| ~ (α/βc) r^α`.
* The whole computation is a single application of Lemma I.4.23
  (`lemma_I_4_23`): the binomial convolution `∑_ℓ C(p,ℓ)(2ℓ-1)!!(2p-2ℓ-3)!!`
  reproduces `(2p-1)!!`, which is exactly the arithmetic reason that the powers
  `r^{(2p-1)α}` and the constants of (I.1.6) are consistent with (I.1.3).
-/
module

public import PercLib.CriticalLRP.VolumeMoments.Convolution

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.VolumeMoments

section Ansatz

variable {α β B : ℝ}

/-- The ansatz of Theorem I.1.6 with the constant `A` replaced by `B`:
`v_p(r) = (2p-3)!! B^{p-1} (α/β) r^{(2p-1)α}`. -/
def mom (p : ℕ) (r : ℝ) : ℝ :=
  (M (p - 1) : ℝ) * B ^ (p - 1) * (α / β) * r ^ ((2 * (p : ℝ) - 1) * α)

lemma mom_one (r : ℝ) : mom (α := α) (β := β) (B := B) 1 r = (α / β) * r ^ α := by
  unfold mom
  norm_num

lemma mom_two (r : ℝ) : mom (α := α) (β := β) (B := B) 2 r = B * (α / β) * r ^ (3 * α) := by
  unfold mom
  norm_num

/-! ### The one-step product identity -/

/-- `v_{ℓ+1}(r) · v_{p-ℓ}(r) = (2ℓ-1)!! (2p-2ℓ-3)!! B^{p-1} (α/β)^2 r^{2pα}`. -/
theorem mom_mul {r : ℝ} (hr : 0 < r) {p ℓ : ℕ} (hℓ : ℓ < p) :
    mom (α := α) (β := β) (B := B) (ℓ + 1) r * mom (α := α) (β := β) (B := B) (p - ℓ) r
      = ((M ℓ : ℝ) * (M (p - 1 - ℓ) : ℝ)) * B ^ (p - 1) * (α / β) ^ 2
        * r ^ (2 * (p : ℝ) * α) := by
  have h1 : ℓ + 1 - 1 = ℓ := by omega
  have h2 : p - ℓ - 1 = p - 1 - ℓ := by omega
  have h3 : ℓ + (p - 1 - ℓ) = p - 1 := by omega
  have hc1 : ((ℓ + 1 : ℕ) : ℝ) = (ℓ : ℝ) + 1 := by push_cast; ring
  have hc2 : ((p - ℓ : ℕ) : ℝ) = (p : ℝ) - (ℓ : ℝ) := by
    rw [Nat.cast_sub hℓ.le]
  unfold mom
  rw [h1, h2, hc1, hc2]
  generalize hE1 : (2 * ((ℓ : ℝ) + 1) - 1) * α = E1
  generalize hE2 : (2 * ((p : ℝ) - (ℓ : ℝ)) - 1) * α = E2
  generalize hA : B ^ ℓ = B1
  generalize hA2 : B ^ (p - 1 - ℓ) = B2
  have hexp : E1 + E2 = 2 * (p : ℝ) * α := by rw [← hE1, ← hE2]; ring
  have hB : B1 * B2 = B ^ (p - 1) := by rw [← hA, ← hA2, ← pow_add, h3]
  calc (M ℓ : ℝ) * B1 * (α / β) * r ^ E1 * ((M (p - 1 - ℓ) : ℝ) * B2 * (α / β) * r ^ E2)
      = ((M ℓ : ℝ) * (M (p - 1 - ℓ) : ℝ)) * (B1 * B2) * ((α / β) * (α / β))
        * (r ^ E1 * r ^ E2) := by ring
    _ = ((M ℓ : ℝ) * (M (p - 1 - ℓ) : ℝ)) * B ^ (p - 1) * (α / β) ^ 2
          * r ^ (2 * (p : ℝ) * α) := by
        rw [hB, ← Real.rpow_add hr, hexp]
        ring

/-! ### The exact solution of the moment ODE system -/

/-- **The exact solution of (I.1.3).** For every `α, β > 0`, every `B` and every
`p ≥ 1`, the function `r ↦ (2p-3)!! B^{p-1} (α/β) r^{(2p-1)α}` satisfies the
moment ODE of the paper exactly on `(0,∞)`:
`v_p'(r) = β r^{-α-1} ∑_{ℓ<p} C(p,ℓ) v_{ℓ+1}(r) v_{p-ℓ}(r)`. -/
theorem moment_ODE_exact {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (B : ℝ) (p : ℕ) (hp : 1 ≤ p)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (mom (α := α) (β := β) (B := B) p)
      (β * r ^ (-α - 1) * ∑ ℓ ∈ Finset.range p,
        ((p.choose ℓ : ℕ) : ℝ) * mom (α := α) (β := β) (B := B) (ℓ + 1) r
          * mom (α := α) (β := β) (B := B) (p - ℓ) r) r := by
  have hsum : (∑ ℓ ∈ Finset.range p,
        ((p.choose ℓ : ℕ) : ℝ) * mom (α := α) (β := β) (B := B) (ℓ + 1) r
          * mom (α := α) (β := β) (B := B) (p - ℓ) r)
      = (M p : ℝ) * B ^ (p - 1) * (α / β) ^ 2 * r ^ (2 * (p : ℝ) * α) := by
    have hstep : ∀ ℓ ∈ Finset.range p,
        ((p.choose ℓ : ℕ) : ℝ) * mom (α := α) (β := β) (B := B) (ℓ + 1) r
            * mom (α := α) (β := β) (B := B) (p - ℓ) r
          = (((p.choose ℓ : ℕ) : ℝ) * ((M ℓ : ℝ) * (M (p - 1 - ℓ) : ℝ)))
              * (B ^ (p - 1) * (α / β) ^ 2 * r ^ (2 * (p : ℝ) * α)) := by
      intro ℓ hℓ
      calc ((p.choose ℓ : ℕ) : ℝ) * mom (α := α) (β := β) (B := B) (ℓ + 1) r
            * mom (α := α) (β := β) (B := B) (p - ℓ) r
          = ((p.choose ℓ : ℕ) : ℝ) * (mom (α := α) (β := β) (B := B) (ℓ + 1) r
              * mom (α := α) (β := β) (B := B) (p - ℓ) r) := by ring
        _ = (((p.choose ℓ : ℕ) : ℝ) * ((M ℓ : ℝ) * (M (p - 1 - ℓ) : ℝ)))
              * (B ^ (p - 1) * (α / β) ^ 2 * r ^ (2 * (p : ℝ) * α)) := by
            rw [mom_mul (α := α) (β := β) (B := B) hr (Finset.mem_range.1 hℓ)]
            ring
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
    have hcoef : (∑ ℓ ∈ Finset.range p,
          ((p.choose ℓ : ℕ) : ℝ) * ((M ℓ : ℝ) * (M (p - 1 - ℓ) : ℝ))) = (M p : ℝ) := by
      have h := lemma_I_4_23 p hp
      rw [← h, SA]
      push_cast
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      ring
    rw [hcoef]
    ring_nf
  rw [hsum]
  have hpow : HasDerivAt (fun s : ℝ => s ^ ((2 * (p : ℝ) - 1) * α))
      (((2 * (p : ℝ) - 1) * α) * r ^ ((2 * (p : ℝ) - 1) * α - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hr))
  have hd := hpow.const_mul ((M (p - 1) : ℝ) * B ^ (p - 1) * (α / β))
  have hM : (M p : ℝ) = (2 * (p : ℝ) - 1) * (M (p - 1) : ℝ) := by
    have h := M_succ (p - 1)
    have hpe : p - 1 + 1 = p := by omega
    rw [hpe] at h
    have hc : ((M p : ℕ) : ℝ) = ((2 * (p - 1) + 1) * M (p - 1) : ℕ) := by rw [h]
    rw [hc]
    have hpm : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp]; norm_num
    push_cast
    rw [hpm]
    ring
  have hE : (2 * (p : ℝ) - 1) * α - 1 = 2 * (p : ℝ) * α - α - 1 := by ring
  have key : ((M (p - 1) : ℝ) * B ^ (p - 1) * (α / β))
        * (((2 * (p : ℝ) - 1) * α) * r ^ ((2 * (p : ℝ) - 1) * α - 1))
      = β * r ^ (-α - 1) * ((M p : ℝ) * B ^ (p - 1) * (α / β) ^ 2 * r ^ (2 * (p : ℝ) * α)) := by
    rw [hE]
    have hsplit : β * r ^ (-α - 1) * ((M p : ℝ) * B ^ (p - 1) * (α / β) ^ 2 * r ^ (2 * (p : ℝ) * α))
        = β * (M p : ℝ) * B ^ (p - 1) * (α / β) ^ 2 * (r ^ (-α - 1) * r ^ (2 * (p : ℝ) * α)) := by
      ring
    rw [hsplit, ← Real.rpow_add hr,
      show -α - 1 + 2 * (p : ℝ) * α = 2 * (p : ℝ) * α - α - 1 by ring, hM]
    field_simp
  rw [← key]
  exact hd

/-! ### Consistency with Proposition I.4.20 -/

/-- **Proposition I.4.20 holds exactly for the ansatz of Theorem I.1.6.**
Proposition I.4.20 (paper p. 48) states
`E|K|^p ∼ (2p-3)!! (E|K|²/E|K|)^{p-1} E|K|`.  For the exact solution of (I.1.3)
shown above this is an identity, not just an asymptotic statement: with
`v_p = (2p-3)!! B^{p-1}(α/β) r^{(2p-1)α}` one has `v_2/v_1 = B r^{2α}`, so
`(2p-3)!! (v_2/v_1)^{p-1} v_1 = v_p` for every `p ≥ 1`. -/
theorem mom_ratio {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (B : ℝ) (p : ℕ) (hp : 1 ≤ p)
    {r : ℝ} (hr : 0 < r) :
    mom (α := α) (β := β) (B := B) p r
      = (M (p - 1) : ℝ)
          * (mom (α := α) (β := β) (B := B) 2 r / mom (α := α) (β := β) (B := B) 1 r) ^ (p - 1)
          * mom (α := α) (β := β) (B := B) 1 r := by
  have hLHS : mom (α := α) (β := β) (B := B) p r
      = (M (p - 1) : ℝ) * B ^ (p - 1) * (α / β) * r ^ ((2 * (p : ℝ) - 1) * α) := rfl
  rw [hLHS, mom_one, mom_two]
  -- the ratio is `B * r^{2α}`
  have hratio : B * (α / β) * r ^ (3 * α) / ((α / β) * r ^ α) = B * r ^ (2 * α) := by
    have h1 : r ^ (3 * α) = r ^ (2 * α) * r ^ α := by
      rw [← Real.rpow_add hr]; congr 1; ring
    rw [h1]
    field_simp
  rw [hratio]
  -- `(B r^{2α})^{p-1} = B^{p-1} r^{2α(p-1)}`
  have hpow : (B * r ^ (2 * α)) ^ (p - 1) = B ^ (p - 1) * r ^ ((2 * α) * ((p : ℝ) - 1)) := by
    rw [mul_pow, ← Real.rpow_natCast (r ^ (2 * α)) (p - 1), ← Real.rpow_mul hr.le]
    congr 2
    rw [Nat.cast_sub hp]
    norm_num
  rw [hpow]
  -- assemble the exponents
  have hexp : (2 * α) * ((p : ℝ) - 1) + α = (2 * (p : ℝ) - 1) * α := by ring
  have h1 : r ^ ((2 * α) * ((p : ℝ) - 1)) * r ^ α = r ^ ((2 * (p : ℝ) - 1) * α) := by
    rw [← Real.rpow_add hr, hexp]
  rw [← h1]
  ring

end Ansatz

end PercLib.CriticalLRP.VolumeMoments
