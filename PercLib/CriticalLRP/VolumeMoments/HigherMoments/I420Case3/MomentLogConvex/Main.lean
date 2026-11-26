/-
Case 3 of Proposition I.4.20 without the moment-comparison premise.

Independent Ultramath work (member `m4` of swarm `smwxuymqb`), production base
`6569f9781a4bf1ef35843ff3cd468b1d934c4527`.

`I420Case3.Main.case3_hAend_hAmid` carries the denominator comparison

  `hcmp : ∀ ℓ ≤ p, c4 * biasTarget m₁ m₂ p ≤ m_(ℓ+1) · m_(p-ℓ)`

as an explicit source input, and `I420Case3.Compare.case3_hAend_hAmid_of_hIH`
derives it for `1 ≤ ℓ ≤ p-2` from the second induction's hypothesis `hIH` while
leaving the `ℓ = 0` case as the separate premise `hcmp0`.

`MomentLogConvex.biasTarget_le_mul_momR` shows that the comparison is a
consequence of log-convexity of the cluster moment sequence
(`(E|K|^(j+1))^2 ≤ E|K|^j E|K|^(j+2)`), with constant `c4 = 1`, and therefore
needs neither `hIH` nor any asymptotic input.  The two theorems below are the
resulting reductions:

* `case3_hAend_hAmid_of_hIH'` — `Compare`'s theorem with `hcmp0` deleted;
* `case3_hAend_hAmid'` — `Main`'s theorem with `hcmp` deleted (and `hIH` is not
  needed at all).

Statements, hypothesis order and conclusions are those of the production
theorems; only the deleted comparison premise differs.  This *weakens* an input
the source obtains from the induction hypothesis; it does not restate or
strengthen the source's asymptotic content.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Compare
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.MomentLogConvex.Defs

/-! # Case 3 wrappers with the denominator comparison proved by log-convexity -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-! ## The comparison in `momOf` form -/

/-- The comparison of `MomentLogConvex.biasTarget_le_mul_momR`, transported to the
`I420Case3.momOf` moment family along a family of laws. -/
theorem biasTarget_le_mul_momOf (π : ℝ → Sym2 V → unitInterval) (o : V) {p : ℕ}
    (hp : 3 ≤ p) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = p + 1) (r : ℝ)
    (hfin : ∀ i : ℕ, 1 ≤ i → i ≤ p + 1 → I420Case1.powMomentAt (π r) i o ≠ ⊤) :
    biasTarget (momOf π o 1 r) (momOf π o 2 r) p ≤ momOf π o a r * momOf π o b r :=
  MomentLogConvex.biasTarget_le_mul_momR (π := π r) o hp ha hb hab hfin

/-- Moments of order `1, …, p+1` are finite, in the form used below. -/
theorem powMomentAt_ne_top_of_le_succ {π : Sym2 V → unitInterval} {o : V} {p : ℕ}
    (hMa : ∀ ℓ : ℕ, ℓ ≤ p → I420Case1.powMomentAt π (ℓ + 1) o ≠ ⊤) :
    ∀ i : ℕ, 1 ≤ i → i ≤ p + 1 → I420Case1.powMomentAt π i o ≠ ⊤ := by
  intro i hi hle
  have h := hMa (i - 1) (by omega)
  have hi' : i - 1 + 1 = i := by omega
  rwa [hi'] at h

/-! ## `Compare`'s theorem with `hcmp0` deleted -/

/-- **Case 3 with the `hIH` hypothesis of the second induction, and no separate
`ℓ = 0` comparison premise.**

This is `I420Case3.case3_hAend_hAmid_of_hIH` with the implicit `c4`, its
positivity hypothesis and the eventual comparison `hcmp0` removed: they are
supplied at `c4 = 1` by `biasTarget_le_mul_momOf`. -/
theorem case3_hAend_hAmid_of_hIH' (π : ℝ → Sym2 V → unitInterval) (o : V)
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
      Tendsto (fun r => momOf π o m r / VolumeMoments.HigherMoments.mixedMoment m
        (momOf π o) r) atTop (𝓝 1)) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o 1 p (B r) /
        (ballCard B r * (momOf π o 1 r * momOf π o p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
          (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
  have hcmp0 : ∀ᶠ r in atTop,
      biasTarget (momOf π o 1 r) (momOf π o 2 r) p ≤ momOf π o 1 r * momOf π o p r :=
    Eventually.of_forall fun r =>
      biasTarget_le_mul_momOf (p := p) (a := 1) (b := p) π o hp (by omega) (by omega)
        (by omega) r (powMomentAt_ne_top_of_le_succ (hMa r))
  refine case3_hAend_hAmid_of_hIH π o B 𝓔 h𝓔mono h𝓔 p hp hπ poly C Bpoly hC hpoly hTree
    hPoly hcard hhom hM1 hM2 hMa hMb hc3 hgm hIH (c4 := 1) (by norm_num) ?_
  simpa only [one_mul] using hcmp0

/-! ## `Main`'s theorem with `hcmp` deleted -/

/-- **Case 3 with no moment-comparison premise at all.**

This is `I420Case3.case3_hAend_hAmid` with the implicit `c4`, its positivity
hypothesis and the comparison `hcmp` removed.  The comparison is supplied at
`c4 = 1` from `biasTarget_le_mul_momOf` for each index that the conclusion uses
(`ℓ = 0` and `1 ≤ ℓ ≤ p-2`), so neither `hcmp` nor the second induction's
hypothesis `hIH` is required. -/
theorem case3_hAend_hAmid' (π : ℝ → Sym2 V → unitInterval) (o : V)
    (B : ℝ → Finset V) (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    (hπ : ∀ (r : ℝ) (e : Sym2 V), π r e < 1)
    (poly : ℝ → V → ℕ → ℝ≥0∞) (C : ℕ → ℕ → ℝ) (Bpoly : ℝ → ℝ) (hC : ∀ ℓ j, 0 ≤ C ℓ j)
    (hpoly : Tendsto Bpoly atTop (𝓝 0))
    (hTree : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p →
      HasTreeExpansion (π r) o (B r) (ℓ + 1) (p - ℓ) p (poly r) (C ℓ))
    (hPoly : ∀ r, HasPolygonBound (π r) o (B r) p (poly r) (Bpoly r))
    (hcard : ∀ r, 0 < (B r).card)
    (hhom : ∀ (r : ℝ) (ℓ : ℕ) (y : V), y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y = I420Case1.powMomentAt (π r) (p - ℓ) o)
    (hM1 : ∀ r, I420Case1.powMomentAt (π r) 1 o ≠ ⊤)
    (hMa : ∀ (r : ℝ) (ℓ : ℕ), ℓ ≤ p → I420Case1.powMomentAt (π r) (ℓ + 1) o ≠ ⊤)
    (hMb : ∀ (r : ℝ) (ℓ : ℕ) (y : V), ℓ ≤ p → y ∈ B r →
      I420Case1.powMomentAt (π r) (p - ℓ) y ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf π o 1 r ^ 3 ≤ momOf π o 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (π r) o 1 p (B r) /
        (ballCard B r * (momOf π o 1 r * momOf π o p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
          (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
  have hone : ∀ ℓ, ℓ ≤ p - 1 → Tendsto (fun r =>
      I420Case1.mixedExclR (π r) o (ℓ + 1) (p - ℓ) (B r) /
        (ballCard B r * (momOf π o (ℓ + 1) r * momOf π o (p - ℓ) r))) atTop (𝓝 1) := by
    intro ℓ hℓ
    have hℓp : ℓ ≤ p := by omega
    have hb1 : 1 ≤ ℓ + 1 := by omega
    have hb2 : 1 ≤ p - ℓ := by omega
    have hb3 : ℓ + 1 + (p - ℓ) = p + 1 := by omega
    have hb := fun (r : ℝ) (y : V) (hy : y ∈ B r) => hMb r ℓ y hℓp hy
    refine case3_hAmid_of_i421 π o B 𝓔 h𝓔mono h𝓔 p ℓ (by omega) hπ hcard
      (fun r => hhom r ℓ) hM1 (fun r => hMa r ℓ hℓp) hb ?_ hc3 hgm (c4 := 1)
      (by norm_num) ?_
    · exact case3_i421_family π o B 𝓔 h𝓔mono h𝓔 p ℓ (by omega) hπ poly (C ℓ) Bpoly (hC ℓ)
        hpoly (fun r => hTree r ℓ hℓp) hPoly hcard hM1 (fun r => hMa r ℓ hℓp)
        (fun r y hy => hMb r ℓ y hℓp hy) hc3 hgm
    · refine Eventually.of_forall fun r => ?_
      have h := biasTarget_le_mul_momOf (p := p) (a := ℓ + 1) (b := p - ℓ) π o hp hb1 hb2
        hb3 r (powMomentAt_ne_top_of_le_succ (hMa r))
      simpa only [one_mul] using h
  exact ⟨hone 0 (by omega), fun ℓ h1 h2 => hone ℓ (by omega)⟩

end I420Case3

end PercLib.CriticalLRP
