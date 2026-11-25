/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m3/.
-/

/- From the source's order inputs to the hypotheses of the Case 1 squeeze.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main

/-!
# Reducing the source's order inputs to the hypotheses of `case1_decorrelation`

The two asymptotic hypotheses of `I420Case1.case1_decorrelation` are exactly the two
`≍`/`⪯` computations of Case 1 of the proof of Proposition I.4.20:

* `hWmom : E|K|^{p+2} ⪯_p r^{(2p+3)α}` is the chain
  `E[|K|^{p+1}|K ∩ B_r|] ≤ E|K|^{p+2} ⪯_p (E|K|)^{2p+3} ≍_p r^{(2p+3)α}`,
  where the middle `⪯_p` is the tree-graph inequality (I.2.3)
  (`TreeExpansion.clusterMoment_le_dfactorial` in the repository) and the last
  `≍_p` is Proposition I.4.2 (`E|K| ≍ r^α`).
* `hP : c r^{d+2pα} ≤ |B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}` is
  `|B_r|E|K|^{ℓ+1}E|K|^{p-ℓ} ≍_p r^d r^{(2ℓ+1)α} r^{(2p-2ℓ-1)α} = r^{d+2pα}`,
  combining `|B_r| ≍ r^d` with the two regular-variation estimates
  `E|K|^m ≍ r^{(2m-1)α}`.

`wMom_order_of_treegraph` and `prodFactor_order_of_asymptotics` below perform exactly
these two algebraic steps.  They are stated for arbitrary functions of `r`, so they
carry the source's order inputs (`≍` at `E|K|`, `|B_r| ≍ r^d`, the tree-graph
constant) as explicit real-valued hypotheses and record precisely what is still
missing: the tree-graph inequality in the canonical model at general `p`, and the
regular variation of `E|K|` with a two-sided comparison constant, both source inputs
of Proposition I.4.20 that are not re-proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case1

variable {V : Type*} [Countable V]

/-- **The tree-graph + regular-variation step for `hWmom`.**
If `M r = E|K|^{p+2} ≤ K (E|K|)^{2p+3}` (the tree-graph inequality (I.2.3)) and
`E|K| ≤ c₁ r^α` (the upper half of `E|K| ≍ r^α`), then
`M r ≤ K c₁^{2p+3} r^{(2p+3)α}`. -/
theorem wMom_order_of_treegraph {M M₁ : ℝ → ℝ} {K c₁ α : ℝ} (p : ℕ)
    (hK : 0 ≤ K)
    (hTG : ∀ r : ℝ, 0 < r → M r ≤ K * (M₁ r) ^ (2 * p + 3))
    (hM₁ : ∀ r : ℝ, 0 < r → 0 ≤ M₁ r)
    (h₁ : ∀ r : ℝ, 0 < r → M₁ r ≤ c₁ * r ^ α) :
    ∀ r : ℝ, 0 < r → M r ≤ (K * c₁ ^ (2 * p + 3)) * r ^ ((2 * (p : ℝ) + 3) * α) := by
  intro r hr
  have hrpow : (0 : ℝ) ≤ r ^ α := Real.rpow_nonneg (le_of_lt hr) α
  have hM₁r : (0 : ℝ) ≤ M₁ r := hM₁ r hr
  have hpow : (M₁ r) ^ (2 * p + 3) ≤ (c₁ * r ^ α) ^ (2 * p + 3) :=
    pow_le_pow_left₀ hM₁r (h₁ r hr) _
  calc M r ≤ K * (M₁ r) ^ (2 * p + 3) := hTG r hr
    _ ≤ K * (c₁ * r ^ α) ^ (2 * p + 3) := mul_le_mul_of_nonneg_left hpow hK
    _ = (K * c₁ ^ (2 * p + 3)) * r ^ ((2 * (p : ℝ) + 3) * α) := by
        rw [mul_pow, ← Real.rpow_natCast (r ^ α) (2 * p + 3),
          ← Real.rpow_mul (le_of_lt hr)]
        rw [show α * ((2 * p + 3 : ℕ) : ℝ) = (2 * (p : ℝ) + 3) * α by push_cast; ring]
        ring

/-- **The `≍` step for `hP`.**  If `c_B r^d ≤ |B_r|`, `c₁ r^{(2ℓ+1)α} ≤ E|K|^{ℓ+1}` and
`c₂ r^{(2p-2ℓ-1)α} ≤ E|K|^{p-ℓ}`, then
`(c_B c₁ c₂) r^{d+2pα} ≤ |B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}`; this is the paper's
`|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ} ≍ r^{d+2pα}` with explicit constants. -/
theorem prodFactor_order_of_asymptotics (π : Sym2 V → unitInterval) (o : V)
    (p ℓ : ℕ) (hℓ : ℓ ≤ p) {d α cB c₁ c₂ : ℝ}
    (hcB : 0 ≤ cB) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (B : ℝ → Finset V)
    (hBcard : ∀ r : ℝ, 0 < r → cB * r ^ d ≤ ((B r).card : ℝ))
    (h₁ : ∀ r : ℝ, 0 < r →
      c₁ * r ^ ((2 * ((ℓ : ℝ) + 1) - 1) * α) ≤ momR π (ℓ + 1) o)
    (h₂ : ∀ r : ℝ, 0 < r →
      c₂ * r ^ ((2 * (((p - ℓ : ℕ) : ℝ)) - 1) * α) ≤ momR π (p - ℓ) o) :
    ∀ r : ℝ, 0 < r →
      (cB * c₁ * c₂) * r ^ (d + 2 * (p : ℝ) * α) ≤
        ((B r).card : ℝ) * (momR π (ℓ + 1) o * momR π (p - ℓ) o) := by
  intro r hr
  have hrp : (0 : ℝ) < r := hr
  have hd0 : (0 : ℝ) ≤ r ^ d := Real.rpow_nonneg (le_of_lt hr) d
  have ht1 : (0 : ℝ) ≤ r ^ ((2 * ((ℓ : ℝ) + 1) - 1) * α) := Real.rpow_nonneg (le_of_lt hr) _
  have ht2 : (0 : ℝ) ≤ r ^ ((2 * (((p - ℓ : ℕ) : ℝ)) - 1) * α) :=
    Real.rpow_nonneg (le_of_lt hr) _
  have hA : (cB * r ^ d) * (c₁ * r ^ ((2 * ((ℓ : ℝ) + 1) - 1) * α))
      ≤ ((B r).card : ℝ) * momR π (ℓ + 1) o :=
    mul_le_mul (hBcard r hr) (h₁ r hr) (mul_nonneg hc₁ ht1)
      (le_trans (mul_nonneg hcB hd0) (hBcard r hr))
  have hA2 : ((cB * r ^ d) * (c₁ * r ^ ((2 * ((ℓ : ℝ) + 1) - 1) * α)))
        * (c₂ * r ^ ((2 * (((p - ℓ : ℕ) : ℝ)) - 1) * α))
      ≤ (((B r).card : ℝ) * momR π (ℓ + 1) o) * momR π (p - ℓ) o :=
    mul_le_mul hA (h₂ r hr) (mul_nonneg hc₂ ht2)
      (mul_nonneg (le_trans (mul_nonneg hcB hd0) (hBcard r hr)) ENNReal.toReal_nonneg)
  have hexp : r ^ d * r ^ ((2 * ((ℓ : ℝ) + 1) - 1) * α)
        * r ^ ((2 * (((p - ℓ : ℕ) : ℝ)) - 1) * α) = r ^ (d + 2 * (p : ℝ) * α) := by
    rw [← Real.rpow_add hrp, ← Real.rpow_add hrp]
    congr 1
    rw [Nat.cast_sub hℓ]
    ring
  calc (cB * c₁ * c₂) * r ^ (d + 2 * (p : ℝ) * α)
      = ((cB * r ^ d) * (c₁ * r ^ ((2 * ((ℓ : ℝ) + 1) - 1) * α)))
          * (c₂ * r ^ ((2 * (((p - ℓ : ℕ) : ℝ)) - 1) * α)) := by
        rw [← hexp]; ring
    _ ≤ (((B r).card : ℝ) * momR π (ℓ + 1) o) * momR π (p - ℓ) o := hA2
    _ = ((B r).card : ℝ) * (momR π (ℓ + 1) o * momR π (p - ℓ) o) := by ring

end I420Case1

end PercLib.CriticalLRP
