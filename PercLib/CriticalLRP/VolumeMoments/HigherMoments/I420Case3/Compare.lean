/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Case 3 of Proposition I.4.20: reducing the comparison premise to the induction
hypothesis of the second induction.  Independent Ultramath work.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.SecondInduction.Defs

/-!
# The comparison premise of Case 3 is the induction hypothesis `hIH`

The Case 3 bound of `I420Case3.Main` needs, for each `ℓ`, a lower bound
`E|K|^{ℓ+1} E|K|^{p-ℓ} ⪰ (E|K|²/E|K|)^{p-1}(E|K|)²` on the denominator.  The paper
obtains it "from the induction hypothesis", namely the first-order asymptotic
established for the smaller moments.

This file shows that it *is* that hypothesis.  Writing
`mixedMoment m = (2m-3)!!(E|K|²/E|K|)^{m-1}E|K|` for the paper's target, the two
mixed moments at indices `ℓ+1` and `p-ℓ` multiply to
`(2ℓ-1)!!(2p-2ℓ-3)!! (E|K|²/E|K|)^{p-1}(E|K|)²`; hence
`E|K|^m ~ mixedMoment m` for `m = ℓ+1` and `m = p-ℓ` (which is exactly the
`hIH` hypothesis of `SecondInduction.derivative_ratio_tendsto` for
`1 ≤ ℓ ≤ p-2`) implies the comparison with the explicit constant
`(2ℓ-1)!!(2p-2ℓ-3)!!/4`.

For `ℓ = 0` (the paper's `hAend`) the index `p` is *not* a smaller moment, so the
comparison is a genuinely separate input there: it needs the lower bound
`E|K|^p ⪰ r^{(2p-1)α}`, which the source has from the tree-graph inequality and
monotonicity before the second induction.  That case is left as an explicit
premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Filter
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

open PercLib.CriticalLRP.VolumeMoments.HigherMoments

variable {V : Type*} [Countable V]

/-- **The product of the two mixed moments.**  For `1 ≤ ℓ ≤ p-2`,
`mixedMoment (ℓ+1) · mixedMoment (p-ℓ)` equals
`(2ℓ-1)!!(2p-2ℓ-3)!! (E|K|²/E|K|)^{p-1}(E|K|)²`. -/
theorem mixedMoment_mul_eq (ℓ p : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ p - 2) {mom : ℕ → ℝ → ℝ}
    {r : ℝ} (hR : 0 < momentRatio mom r) (hp : 1 ≤ p) :
    mixedMoment (ℓ + 1) mom r * mixedMoment (p - ℓ) mom r =
      dblFact ℓ * dblFact (p - ℓ - 1) * biasTarget (mom 1 r) (mom 2 r) p := by
  have hpl : 1 ≤ p - ℓ := by omega
  have hcast1 : ((ℓ + 1 : ℕ) : ℝ) - 1 = (ℓ : ℝ) := by push_cast; ring
  have hcast2 : ((p - ℓ : ℕ) : ℝ) - 1 = ((p - ℓ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpl]
    norm_num
  have hidx : (ℓ + 1) - 1 = ℓ := rfl
  have hm1 : mixedMoment (ℓ + 1) mom r = dblFact ℓ * momentRatio mom r ^ (ℓ : ℝ) * mom 1 r := by
    have h : mixedMoment (ℓ + 1) mom r = dblFact ((ℓ + 1) - 1) *
        momentRatio mom r ^ (((ℓ + 1 : ℕ) : ℝ) - 1) * mom 1 r := rfl
    rw [h, hidx, hcast1]
  have hm2 : mixedMoment (p - ℓ) mom r =
      dblFact (p - ℓ - 1) * momentRatio mom r ^ ((p - ℓ - 1 : ℕ) : ℝ) * mom 1 r := by
    have h : mixedMoment (p - ℓ) mom r = dblFact ((p - ℓ) - 1) *
        momentRatio mom r ^ (((p - ℓ : ℕ) : ℝ) - 1) * mom 1 r := rfl
    rw [h, hcast2]
  have hkey : (ℓ : ℝ) + ((p - ℓ - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    have hA : ((p - ℓ : ℕ) : ℝ) = (p : ℝ) - (ℓ : ℝ) := by
      rw [Nat.cast_sub (by omega : ℓ ≤ p)]
    have hB : ((p - ℓ - 1 : ℕ) : ℝ) = ((p - ℓ : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hpl]
      norm_num
    rw [hB, hA]
    ring
  have hRpow : momentRatio mom r ^ (ℓ : ℝ) * momentRatio mom r ^ ((p - ℓ - 1 : ℕ) : ℝ)
      = momentRatio mom r ^ ((p : ℝ) - 1) := by
    rw [← Real.rpow_add hR, hkey]
  calc mixedMoment (ℓ + 1) mom r * mixedMoment (p - ℓ) mom r
      = (dblFact ℓ * momentRatio mom r ^ (ℓ : ℝ) * mom 1 r) *
          (dblFact (p - ℓ - 1) * momentRatio mom r ^ ((p - ℓ - 1 : ℕ) : ℝ) * mom 1 r) := by
        rw [hm1, hm2]
    _ = dblFact ℓ * dblFact (p - ℓ - 1) * (momentRatio mom r ^ (ℓ : ℝ) *
          momentRatio mom r ^ ((p - ℓ - 1 : ℕ) : ℝ)) * (mom 1 r * mom 1 r) := by ring
    _ = dblFact ℓ * dblFact (p - ℓ - 1) * momentRatio mom r ^ ((p : ℝ) - 1) *
          (mom 1 r * mom 1 r) := by rw [hRpow]
    _ = dblFact ℓ * dblFact (p - ℓ - 1) * biasTarget (mom 1 r) (mom 2 r) p := by
        rw [biasTarget_eq_rpow (mom 1 r) (mom 2 r) hp, momentRatio]
        ring

/-- **The comparison premise from the induction hypothesis.**  If the smaller
moments satisfy `E|K|^m ~ mixedMoment m` for `2 ≤ m ≤ p-1` — the `hIH` hypothesis of
`SecondInduction.derivative_ratio_tendsto` — then, for `1 ≤ ℓ ≤ p-2`,
`(2ℓ-1)!!(2p-2ℓ-3)!!/4 · (E|K|²/E|K|)^{p-1}(E|K|)² ≤ E|K|^{ℓ+1}E|K|^{p-ℓ}`
eventually. -/
theorem eventually_comparison_of_ih (ℓ p : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ p - 2) (hp : 1 ≤ p)
    {mom : ℕ → ℝ → ℝ}
    (hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
      Tendsto (fun r => mom m r / mixedMoment m mom r) atTop (𝓝 1))
    (hpos1 : ∀ᶠ r in atTop, 0 < mom 1 r) (hpos2 : ∀ᶠ r in atTop, 0 < mom 2 r) :
    ∀ᶠ r in atTop, (dblFact ℓ * dblFact (p - ℓ - 1) / 4) *
        biasTarget (mom 1 r) (mom 2 r) p ≤ mom (ℓ + 1) r * mom (p - ℓ) r := by
  have hA := hIH (ℓ + 1) (by omega) (by omega)
  have hB := hIH (p - ℓ) (by omega) (by omega)
  have hgeA : ∀ᶠ r in atTop, (1 / 2 : ℝ) ≤ mom (ℓ + 1) r / mixedMoment (ℓ + 1) mom r :=
    hA.eventually (Ici_mem_nhds (by norm_num))
  have hgeB : ∀ᶠ r in atTop, (1 / 2 : ℝ) ≤ mom (p - ℓ) r / mixedMoment (p - ℓ) mom r :=
    hB.eventually (Ici_mem_nhds (by norm_num))
  filter_upwards [hgeA, hgeB, hpos1, hpos2] with r hA hB hpos1 hpos2
  have hmA : 0 < mixedMoment (ℓ + 1) mom r := mixedMoment_pos hpos1 hpos2
  have hmB : 0 < mixedMoment (p - ℓ) mom r := mixedMoment_pos hpos1 hpos2
  have hRA : (1 / 2) * mixedMoment (ℓ + 1) mom r ≤ mom (ℓ + 1) r := by
    calc (1 / 2) * mixedMoment (ℓ + 1) mom r
        ≤ (mom (ℓ + 1) r / mixedMoment (ℓ + 1) mom r) * mixedMoment (ℓ + 1) mom r :=
          mul_le_mul_of_nonneg_right hA (le_of_lt hmA)
      _ = mom (ℓ + 1) r := by field_simp
  have hRB : (1 / 2) * mixedMoment (p - ℓ) mom r ≤ mom (p - ℓ) r := by
    calc (1 / 2) * mixedMoment (p - ℓ) mom r
        ≤ (mom (p - ℓ) r / mixedMoment (p - ℓ) mom r) * mixedMoment (p - ℓ) mom r :=
          mul_le_mul_of_nonneg_right hB (le_of_lt hmB)
      _ = mom (p - ℓ) r := by field_simp
  have hprod : (1 / 2 * (1 / 2 : ℝ)) *
      (mixedMoment (ℓ + 1) mom r * mixedMoment (p - ℓ) mom r)
      ≤ mom (ℓ + 1) r * mom (p - ℓ) r := by
    rw [show (1 / 2 * (1 / 2 : ℝ)) * (mixedMoment (ℓ + 1) mom r * mixedMoment (p - ℓ) mom r)
        = ((1 / 2) * mixedMoment (ℓ + 1) mom r) *
            ((1 / 2) * mixedMoment (p - ℓ) mom r) by ring]
    exact mul_le_mul hRA hRB (by positivity) (le_trans (by linarith) hRA)
  rw [mixedMoment_mul_eq ℓ p h1 h2 (momentRatio_pos hpos1 hpos2) hp] at hprod
  refine le_trans (le_of_eq ?_) hprod
  ring

/-- **Case 3 with the `hIH` hypothesis of the second induction.**  This is
`case3_hAend_hAmid` with, for `1 ≤ ℓ ≤ p-2`, the comparison premise discharged from
`hIH : E|K|^m ~ (2m-3)!!(E|K|²/E|K|)^{m-1}E|K|` for the smaller moments `m ≤ p-1` —
the same hypothesis that `SecondInduction.derivative_ratio_tendsto` takes.  Only the
`ℓ = 0` case keeps an explicit comparison premise, because there the index `p` is the
moment being estimated rather than a smaller one. -/
theorem case3_hAend_hAmid_of_hIH (π : ℝ → Sym2 V → unitInterval) (o : V)
    (B : ℝ → Finset V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1) (poly : ℝ → V → ℕ → ℝ≥0∞)
    (C : ℕ → ℕ → ℝ) (Bpoly : ℝ → ℝ) (hC : ∀ ℓ j, 0 ≤ C ℓ j)
    (hpoly : Tendsto Bpoly atTop (𝓝 0))
    (hTree : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p →
      HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) (C ℓ))
    (hPoly : ∀ r, HasPolygonBound (π r) o (B r) p (poly r) (Bpoly r))
    (hcard : ∀ r, 0 < (B r).card)
    (hhom : ∀ (r : ℝ) (ℓ : ℕ) (y : V), y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hM2 : ∀ r, I420Case1.powMomentAt (π r) 2 o ≠ ⊤)
    (hMa : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p → I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (ℓ : ℕ) (y : V), ℓ ≤ p → y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r)
    (hIH : ∀ m, 2 ≤ m → m ≤ p - 1 →
      Tendsto (fun r => momOf π o m r / mixedMoment m (momOf π o) r) atTop (𝓝 1))
    {c4 : ℝ} (hc4 : 0 < c4)
    (hcmp0 : ∀ᶠ r in atTop, c4 * biasTarget (momOf π o 1 r) (momOf π o 2 r) p
      ≤ momOf π o 1 r * momOf π o p r) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o 1 p (B r) /
        (ballCard B r * (momOf π o 1 r * momOf π o p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
          (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
  have hp1 : 1 ≤ p := by omega
  have hpos1 : ∀ᶠ r in atTop, 0 < momOf π o 1 r :=
    Eventually.of_forall fun r => momR_pos (hM1 r)
  have hpos2 : ∀ᶠ r in atTop, 0 < momOf π o 2 r :=
    Eventually.of_forall fun r => momR_pos (hM2 r)
  have hmid : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
      (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
        (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
    intro ℓ h1 h2
    have hℓp : ℓ ≤ p := by omega
    have hb := fun (r : ℝ) (y : V) (hy : y ∈ B r) => hMb r ℓ y hℓp hy
    have hstep1 := case3_i421_family π o B 𝓔 h𝓔mono h𝓔 p ℓ hp1 hπ poly (C ℓ) Bpoly
      (hC ℓ) hpoly (fun r => hTree r ℓ hℓp) hPoly hcard hM1 (hMa · ℓ hℓp) hb hc3 hgm
    have hcmp := eventually_comparison_of_ih ℓ p h1 h2 hp1 hIH hpos1 hpos2
    exact case3_hAmid_of_i421 π o B 𝓔 h𝓔mono h𝓔 p ℓ hp1 hπ hcard
      (fun r => hhom r ℓ) hM1 (hMa · ℓ hℓp) hb hstep1 hc3 hgm
      (by exact div_pos (mul_pos (dblFact_pos ℓ) (dblFact_pos (p - ℓ - 1))) (by norm_num)) hcmp
  have hend : Tendsto (fun r => I420Case1.mixedExclR (π r) o 1 p (B r) /
      (ballCard B r * (momOf π o 1 r * momOf π o p r))) atTop (𝓝 1) := by
    have hb := fun (r : ℝ) (y : V) (hy : y ∈ B r) => hMb r 0 y (by omega) hy
    have hstep1 := case3_i421_family π o B 𝓔 h𝓔mono h𝓔 p 0 hp1 hπ poly (C 0) Bpoly
      (hC 0) hpoly (fun r => hTree r 0 (by omega)) hPoly hcard hM1 (hMa · 0 (by omega)) hb
      hc3 hgm
    exact case3_hAmid_of_i421 π o B 𝓔 h𝓔mono h𝓔 p 0 hp1 hπ hcard (fun r => hhom r 0) hM1
      (hMa · 0 (by omega)) hb hstep1 hc3 hgm hc4 hcmp0
  exact ⟨hend, hmid⟩

end I420Case3

end PercLib.CriticalLRP
