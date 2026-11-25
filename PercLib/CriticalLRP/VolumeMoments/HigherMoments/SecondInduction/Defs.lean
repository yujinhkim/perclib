/- Integrated from independently rebuilt Ultramath work.
Production base e756a603f08962e545c3c11bf9dd877b46c80d6f.
Scratch source: ../../.ultramath/smwvp122a/m2/M2/Defs.lean.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.RVData

/-!
# Notation for the *second* induction of Proposition I.4.20

The upper-bound induction (I.4.19) is already in production
(`HigherMoments.moment_upper_bound_of_percolation`).  The paper then runs a
second induction on `p` proving the two-sided asymptotic

`E|K|^p ~ (2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`.

After the decorrelation estimates (I.4.20)/(I.4.21) have replaced the
expectation `A_ℓ` by `|B_r|` times the product of two moments, the derivative
identity of Lemma I.4.1 assumes the shape

`(E|K|^p)' ~ (1/r) [ (p+1)α E|K|^p + h(r) ]`,

with driving term `h = drivingTerm p α mom`, and Lemma I.4.21 converts it into
the asymptotic.  This file fixes the two quantities that make the conversion
statable without committing to a particular bookkeeping of the finite sum:
`targetSum` (the bracket `(p+1) E|K|^p + (p-2)(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|`,
which is `α`-independent) and `normalizedSum` (the paper's binomial sum
`∑_ℓ C(p,ℓ) A_ℓ`, normalised by `|B_r| E|K|`).  `targetWeight` is the
`ℓ`-th summand of `targetSum` in the form produced by the induction
hypothesis `E|K|^m ~ (2m-3)!! (E|K|²/E|K|)^(m-1) E|K|`.
-/

@[expose] public section

noncomputable section

open Finset

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction

open PercLib.CriticalLRP.VolumeMoments
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- The `α`-independent bracket of the second-induction derivative ratio,
`(p+1) E|K|^p + (p-2) (2p-3)!! (E|K|²/E|K|)^(p-1) E|K|`.  It is
`(p+1) E|K|^p + drivingTerm p α mom / α`. -/
def targetSum (p : ℕ) (mom : ℕ → ℝ → ℝ) (r : ℝ) : ℝ :=
  ((p : ℝ) + 1) * mom p r + ((p : ℝ) - 2) * mixedMoment p mom r

/-- The paper's binomial sum of the decorrelators, normalised by
`|B_r| E|K|`: `∑_{ℓ<p} C(p,ℓ) A_ℓ(r) / (|B_r| E|K|(r))`.
This is exactly `(r (E|K|^p)') / (r c_r |B_r| E|K|)` by Lemma I.4.1. -/
def normalizedSum (p : ℕ) (A : ℕ → ℝ → ℝ) (Bcard : ℝ → ℝ) (mom : ℕ → ℝ → ℝ)
    (r : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * (A ℓ r / (Bcard r * mom 1 r))

/-- The `ℓ`-th summand weight of `targetSum` for `1 ≤ ℓ ≤ p-2`, in the shape
produced by the induction hypothesis:
`(2ℓ-1)!!(2p-2ℓ-3)!! (E|K|²/E|K|)^(p-1) E|K|`. -/
def targetWeight (p : ℕ) (ℓ : ℕ) (mom : ℕ → ℝ → ℝ) (r : ℝ) : ℝ :=
  dblFact ℓ * dblFact (p - ℓ - 1) * (momentRatio mom r ^ ((p : ℝ) - 1) * mom 1 r)

/-- `targetWeight` is `(2ℓ-1)!!(2p-2ℓ-3)!!` times the ratio power, made
explicit for the paper comparison. -/
theorem targetWeight_eq (p ℓ : ℕ) (mom : ℕ → ℝ → ℝ) (r : ℝ) :
    targetWeight p ℓ mom r =
      dblFact ℓ * dblFact (p - ℓ - 1) * momentRatio mom r ^ ((p : ℝ) - 1) * mom 1 r := by
  unfold targetWeight
  ring

theorem mixedMoment_eq_dblFact_ratio {p : ℕ} {mom : ℕ → ℝ → ℝ} {r : ℝ} :
    mixedMoment p mom r = dblFact (p - 1) * momentRatio mom r ^ ((p : ℝ) - 1) * mom 1 r :=
  rfl

/-- `mixedMoment` never vanishes when the moment ratio is positive and `E|K|` is
nonzero: the double factorial and the ratio power are positive, and the sign is
that of `E|K|`. -/
theorem mixedMoment_ne_zero {m : ℕ} {mom : ℕ → ℝ → ℝ} {r : ℝ}
    (hR : 0 < momentRatio mom r) (h1 : mom 1 r ≠ 0) :
    mixedMoment m mom r ≠ 0 := by
  unfold mixedMoment
  exact mul_ne_zero
    (mul_ne_zero (dblFact_ne_zero _) (Real.rpow_pos_of_pos hR _).ne') h1

/-- `targetWeight` never vanishes under the same hypotheses. -/
theorem targetWeight_ne_zero {p ℓ : ℕ} {mom : ℕ → ℝ → ℝ} {r : ℝ}
    (hR : 0 < momentRatio mom r) (h1 : mom 1 r ≠ 0) :
    targetWeight p ℓ mom r ≠ 0 := by
  unfold targetWeight
  exact mul_ne_zero
    (mul_ne_zero (dblFact_ne_zero _) (dblFact_ne_zero _))
    (mul_ne_zero (Real.rpow_pos_of_pos hR _).ne' h1)

/-- `targetSum` in terms of the driving term: it is the bracket whose `α`
multiple is the paper's `(p+1)α E|K|^p + h`. -/
theorem targetSum_eq_ratio {p : ℕ} {α : ℝ} {mom : ℕ → ℝ → ℝ} {r : ℝ} :
    ((p : ℝ) + 1) * α * mom p r + drivingTerm p α mom r = α * targetSum p mom r := by
  unfold targetSum
  rw [drivingTerm_eq_smul]
  ring

theorem targetSum_pos {p : ℕ} (hp : 3 ≤ p) {mom : ℕ → ℝ → ℝ} {r : ℝ}
    (h1 : 0 < mom 1 r) (h2 : 0 < mom 2 r) (hp_pos : 0 < mom p r) :
    0 < targetSum p mom r := by
  unfold targetSum
  have hm : 0 < mixedMoment p mom r := mixedMoment_pos h1 h2
  have hcoef : 0 < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hfirst : 0 < ((p : ℝ) + 1) * mom p r := by
    have : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    exact mul_pos this hp_pos
  have hsecond : 0 ≤ ((p : ℝ) - 2) * mixedMoment p mom r := le_of_lt (mul_pos hcoef hm)
  linarith

end PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction
