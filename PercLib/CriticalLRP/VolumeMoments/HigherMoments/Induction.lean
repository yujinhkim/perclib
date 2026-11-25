/- Integrated from independently rebuilt Ultramath work.
Production base ed48eea0fa7697ac0e16db08e39b60ebb7c70e02.
Scratch source: ../../.ultramath/smwvlmbqa/m2/Induction.lean; migrated to current namespaces.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.RVData

/-!
# The induction step of Proposition I.4.20

Source: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, proof of Proposition I.4.20, pp. 49--50.

The paper's upper-bound induction is the following chain.

1. Lemma I.4.1 gives the exact derivative identity
   `d/dr E|K|^p = β|J'(r)| ∑_{ℓ<p} C(p,ℓ) A_ℓ(r)` with
   `A_ℓ(r) = E[|K|^{ℓ+1} ∑_{y∈B_r} 1(y∉K)|K_y|^{p-ℓ}]`.
   Mass transport makes the two end terms `ℓ = 0` and `ℓ = p-1` equal.
2. Lemma I.2.1 (decorrelation) bounds each `A_ℓ` by `|B_r|` times the product
   of the two corresponding moments.
3. The induction hypothesis for the smaller moments and
   `∑_{ℓ=1}^{p-2} C(p,ℓ)(2ℓ-1)!!(2p-2ℓ-3)!! = (p-2)(2p-3)!!` turn this into
   `f'(r) ≤ (1+o(1)) ((p+1)α f(r) + h(r))/r`
   with `h = α(p-2)(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|`.
4. Lemma I.4.22 applies because `h` is regularly varying of index
   `(2p-1)α > (p+1)α`, and the gap `(2p-1)α-(p+1)α = (p-2)α` exactly cancels
   the constant `α(p-2)(2p-3)!!`, leaving `(2p-3)!!(E|K|²/E|K|)^(p-1)E|K|`.

This file performs steps 3 and 4 in general `p`, with the percolation inputs of
steps 1 and 2 left as explicit hypotheses (`hderivId`, `hmass`, `hA0`,
`hAmid`, and the first-moment normalisation `hc`).  Nothing here asserts the
tree-graph inequality or the first/second moment asymptotics themselves.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open PercLib.CriticalLRP.Analysis
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-! ### Absorption of the product of the `(1+ε)` factors -/

/-- For every `ε > 0` there is `δ > 0` with `(1+δ)^3 ≤ 1+ε`; this lets the
three `(1+o(1))` factors produced by the induction hypothesis (twice) and the
first-moment normalisation be absorbed into a single `1+ε`. -/
theorem exists_one_add_pow_three_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ 3 ≤ 1 + ε := by
  by_cases h9 : ε ≤ 9
  · refine ⟨ε / 8, by positivity, ?_⟩
    nlinarith [hε, h9, sq_nonneg ε, pow_pos hε 3, sq_nonneg (ε ^ 2)]
  · have h9' : 9 < ε := not_le.1 h9
    refine ⟨1, one_pos, ?_⟩
    nlinarith

/-! ### Step 3: the pointwise finite-sum bound -/

/-- Splitting the exponent bookkeeping: for `ℓ ≤ p-3` the product of the two
powers of the ratio occurring in the `ℓ`-th middle term is the single power
`(E|K|²/E|K|)^(p-1)` of the target. -/
theorem ratio_pow_mul {R : ℝ} (hR : 0 < R) {p ℓ : ℕ} (hp : 3 ≤ p) (hℓ : ℓ ≤ p - 3) :
    R ^ (((ℓ + 2 : ℕ) : ℝ) - 1) * R ^ (((p - 1 - ℓ : ℕ) : ℝ) - 1) =
      R ^ ((p : ℝ) - 1) := by
  rw [← Real.rpow_add hR]
  congr 1
  have h1 : ((ℓ + 2 : ℕ) : ℝ) = (ℓ : ℝ) + 2 := by push_cast; ring
  have h2 : ((p - 1 - ℓ : ℕ) : ℝ) = (p : ℝ) - 1 - (ℓ : ℝ) := by
    have hle : ℓ ≤ p - 1 := by omega
    rw [Nat.cast_sub hle]
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    rw [h3]
  rw [h1, h2]
  ring

/-- **The pointwise finite-sum bound of the induction step.**  With the mass
transport identification of the two end terms, the decorrelation bounds, and
the induction hypothesis for the smaller moments, the binomial sum of the
derivative identity is bounded by the `(p+1) E|K|^p E|K|` term plus
`(p-2)(2p-3)!! (E|K|²/E|K|)^(p-1) E|K|²`. -/
theorem sum_bound {p : ℕ} (hp : 3 ≤ p) {mom : ℕ → ℝ → ℝ} {Bcard : ℝ → ℝ}
    {A : ℕ → ℝ → ℝ} {r δ : ℝ} (hδ : 0 ≤ δ)
    (hB : 0 ≤ Bcard r) (hnn : ∀ m, 0 ≤ mom m r)
    (h1 : 0 < mom 1 r) (h2 : 0 < mom 2 r)
    (hmass : A 0 r = A (p - 1) r)
    (hA0 : A 0 r ≤ Bcard r * (mom 1 r * mom p r))
    (hAmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → A ℓ r ≤ Bcard r * (mom (ℓ + 1) r * mom (p - ℓ) r))
    (hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
      mom m r ≤ (1 + δ) * dblFact (m - 1) * momentRatio mom r ^ ((m : ℝ) - 1) * mom 1 r) :
    (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ r)
      ≤ Bcard r * ((p : ℝ) + 1) * (mom 1 r * mom p r)
        + Bcard r * (1 + δ) ^ 2 * (((p : ℝ) - 2) * mixedMoment p mom r * mom 1 r) := by
  have hR : 0 < momentRatio mom r := momentRatio_pos h1 h2
  -- (i) split the sum into the two end terms and the middle range
  have e1 : (∑ ℓ ∈ Finset.range p, ((p.choose ℓ : ℕ) : ℝ) * A ℓ r)
      = (∑ ℓ ∈ Finset.range (p - 1), ((p.choose (ℓ + 1) : ℕ) : ℝ) * A (ℓ + 1) r)
        + ((p.choose 0 : ℕ) : ℝ) * A 0 r := by
    have h := Finset.sum_range_succ' (fun ℓ => ((p.choose ℓ : ℕ) : ℝ) * A ℓ r) (p - 1)
    rw [show p - 1 + 1 = p by omega] at h
    exact h
  have e2 : (∑ ℓ ∈ Finset.range (p - 1), ((p.choose (ℓ + 1) : ℕ) : ℝ) * A (ℓ + 1) r)
      = (∑ ℓ ∈ Finset.range (p - 2), ((p.choose (ℓ + 1) : ℕ) : ℝ) * A (ℓ + 1) r)
        + ((p.choose (p - 1) : ℕ) : ℝ) * A (p - 1) r := by
    have h := Finset.sum_range_succ
      (fun ℓ => ((p.choose (ℓ + 1) : ℕ) : ℝ) * A (ℓ + 1) r) (p - 2)
    rw [show p - 2 + 1 = p - 1 by omega] at h
    exact h
  have hchoose0 : ((p.choose 0 : ℕ) : ℝ) = 1 := by simp
  have hchooseLast : ((p.choose (p - 1) : ℕ) : ℝ) = (p : ℝ) := by
    have h := Nat.choose_succ_self_right (p - 1)
    rw [show p - 1 + 1 = p by omega] at h
    rw [h]
  -- (ii) the two end terms
  have hend : ((p.choose (p - 1) : ℕ) : ℝ) * A (p - 1) r
      + ((p.choose 0 : ℕ) : ℝ) * A 0 r
      ≤ Bcard r * ((p : ℝ) + 1) * (mom 1 r * mom p r) := by
    have hA : A (p - 1) r ≤ Bcard r * (mom 1 r * mom p r) := by
      rw [← hmass]; exact hA0
    have heq : ((p.choose (p - 1) : ℕ) : ℝ) * A (p - 1) r
        + ((p.choose 0 : ℕ) : ℝ) * A 0 r = ((p : ℝ) + 1) * A (p - 1) r := by
      rw [hchooseLast, hchoose0, one_mul, hmass]
      ring
    rw [heq]
    calc ((p : ℝ) + 1) * A (p - 1) r
        ≤ ((p : ℝ) + 1) * (Bcard r * (mom 1 r * mom p r)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = Bcard r * ((p : ℝ) + 1) * (mom 1 r * mom p r) := by ring
  -- (iii) the middle terms
  have hterm : ∀ ℓ ∈ Finset.range (p - 2),
      ((p.choose (ℓ + 1) : ℕ) : ℝ) * A (ℓ + 1) r
        ≤ ((p.choose (ℓ + 1) : ℕ) : ℝ) *
            (Bcard r * ((1 + δ) ^ 2 * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ)) *
              (momentRatio mom r ^ ((p : ℝ) - 1) * (mom 1 r * mom 1 r)))) := by
    intro ℓ hℓ
    have hℓle : ℓ ≤ p - 3 := by have := Finset.mem_range.1 hℓ; omega
    have hAℓ := hAmid (ℓ + 1) (by omega) (by omega)
    have e : ℓ + 1 + 1 = ℓ + 2 := by omega
    have f : p - (ℓ + 1) = p - 1 - ℓ := by omega
    rw [e, f] at hAℓ
    have hIH1 := hIH (ℓ + 2) (by omega) (by omega)
    have hIH2 := hIH (p - 1 - ℓ) (by omega) (by omega)
    have hd1 : ℓ + 2 - 1 = ℓ + 1 := by omega
    have hd2 : p - 1 - ℓ - 1 = p - 2 - ℓ := by omega
    rw [hd1] at hIH1
    rw [hd2] at hIH2
    have hb1 : 0 ≤ (1 + δ) * dblFact (ℓ + 1) *
        momentRatio mom r ^ (((ℓ + 2 : ℕ) : ℝ) - 1) * mom 1 r := by
      have hD : 0 < dblFact (ℓ + 1) := dblFact_pos _
      have hR' : 0 < momentRatio mom r ^ (((ℓ + 2 : ℕ) : ℝ) - 1) := Real.rpow_pos_of_pos hR _
      have hd : 0 ≤ (1 + δ) := by linarith
      have hm1 : 0 ≤ mom 1 r := h1.le
      positivity
    have hprod := mul_le_mul hIH1 hIH2 (hnn (p - 1 - ℓ)) hb1
    have hshape : ((1 + δ) * dblFact (ℓ + 1) *
          momentRatio mom r ^ (((ℓ + 2 : ℕ) : ℝ) - 1) * mom 1 r)
        * ((1 + δ) * dblFact (p - 2 - ℓ) *
          momentRatio mom r ^ (((p - 1 - ℓ : ℕ) : ℝ) - 1) * mom 1 r)
        = (1 + δ) ^ 2 * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ)) *
            (momentRatio mom r ^ ((p : ℝ) - 1) * (mom 1 r * mom 1 r)) := by
      rw [← ratio_pow_mul hR hp hℓle]
      ring
    rw [hshape] at hprod
    have hstep : Bcard r * (mom (ℓ + 2) r * mom (p - 1 - ℓ) r)
        ≤ Bcard r * ((1 + δ) ^ 2 * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ)) *
            (momentRatio mom r ^ ((p : ℝ) - 1) * (mom 1 r * mom 1 r))) :=
      mul_le_mul_of_nonneg_left hprod hB
    have hcoef : (0 : ℝ) ≤ ((p.choose (ℓ + 1) : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (hAℓ.trans hstep) hcoef
  -- (iv) sum the middle terms and factor out the common multiplier
  have hsum := Finset.sum_le_sum hterm
  have hfac1 : (∑ ℓ ∈ Finset.range (p - 2), ((p.choose (ℓ + 1) : ℕ) : ℝ) *
        (Bcard r * ((1 + δ) ^ 2 * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ)) *
          (momentRatio mom r ^ ((p : ℝ) - 1) * (mom 1 r * mom 1 r)))))
      = (Bcard r * (1 + δ) ^ 2 *
            (momentRatio mom r ^ ((p : ℝ) - 1) * (mom 1 r * mom 1 r))) *
          (∑ ℓ ∈ Finset.range (p - 2),
            ((p.choose (ℓ + 1) : ℕ) : ℝ) * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    ring
  have hfac2 : (Bcard r * (1 + δ) ^ 2 *
        (momentRatio mom r ^ ((p : ℝ) - 1) * (mom 1 r * mom 1 r))) *
      (∑ ℓ ∈ Finset.range (p - 2),
        ((p.choose (ℓ + 1) : ℕ) : ℝ) * (dblFact (ℓ + 1) * dblFact (p - 2 - ℓ)))
      = Bcard r * (1 + δ) ^ 2 * (((p : ℝ) - 2) * mixedMoment p mom r * mom 1 r) := by
    rw [middle_sum_eq hp]
    unfold mixedMoment
    ring
  -- (v) assemble
  rw [e1, e2]
  linarith [hend, hsum.trans_eq (hfac1.trans hfac2)]

end PercLib.CriticalLRP.VolumeMoments.HigherMoments
