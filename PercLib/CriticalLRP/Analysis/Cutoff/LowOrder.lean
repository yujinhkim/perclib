/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m2/LowOrder.lean ; imports migrated;
auxiliary definitions and probability instances are collected in `Defs.lean`.
-/

/-
The `ℓ = 3` boundary of Lemma I.4.18.

The source's near-sum step writes the near contribution of a general `ℓ` as
`|B_R| (E|K|)^{ℓ-4}`, which for `ℓ = 3` would read `|B_R| (E|K|)^{-1}`: the exponent
`ℓ - 4` is negative at `ℓ = 3`.  This module records what actually happens there.

Because the two-point matrix has `T(x,x) = 1` (reflexivity of `↔`, `Basic.lean`), the
threefold power has `T³(0,0) ≥ T(0,0)³ = 1` at **every** cutoff.  Since the right-hand side
`C (∇_{r^c} + r^{-c}) (E|K|)^{0} = C (∇_{r^c} + r^{-c})` of the displayed conclusion tends to
`0` along the far tail (`∇_{r^c} → 0` for a summable `∇`, `r^{-c} → 0`), the `ℓ = 3` instance of
the displayed conclusion is *false* for the two-point matrix `T(x,y) = P(x ↔ y)`.  The
correct source-faithful statement therefore starts at `ℓ = 4`, where `ℓ - 4 ≥ 0` and the
`|B_R| (E|K|)^{ℓ-4}` step is legitimate.

Nothing here is assumed: `cutThreefold` is the ℓ = 3 convolution of `M.cutTwoPointE`, and the
two theorems prove the two halves of the contradiction.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.RowSum

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

section Generic

variable {V : Type*} [Countable V]

omit [Countable V] in
/-- A nonnegative kernel with unit diagonal has threefold convolution at the diagonal at
least `1`: the constant path `x → x → x` contributes `κ x x * κ x x * κ x x = 1`. -/
theorem one_le_threefold_tsum (κ : V → V → ℝ≥0∞) {x : V} (h : κ x x = 1) :
    (1 : ℝ≥0∞) ≤ ∑' y, ∑' z, κ x y * κ y z * κ z x := by
  have key : (fun z : V => κ x x * κ x z * κ z x) x = 1 := by
    show κ x x * κ x x * κ x x = 1
    rw [h, one_mul, one_mul]
  calc (1 : ℝ≥0∞) = (fun z : V => κ x x * κ x z * κ z x) x := key.symm
    _ ≤ ∑' z, κ x x * κ x z * κ z x :=
        ENNReal.le_tsum (f := fun z => κ x x * κ x z * κ z x) x
    _ ≤ ∑' y, ∑' z, κ x y * κ y z * κ z x :=
        ENNReal.le_tsum (f := fun y => ∑' z, κ x y * κ y z * κ z x) x

/-- No bound of the shape used at `ℓ = 3` in Lemma I.4.18 can hold for a quantity that is at
least `1` at every scale, when the far tail vanishes and the polynomial factor decays. -/
theorem not_forall_le_tail_add_rpow (T3 : ℝ → ℝ) (hT3 : ∀ r : ℝ, 0 < r → 1 ≤ T3 r)
    (C c : ℝ) (_hC : 0 < C) (hc : 0 < c) (tail : ℝ → ℝ)
    (hlim : Tendsto tail atTop (𝓝 0)) :
    ¬ ∀ r : ℝ, 0 < r → T3 r ≤ C * (tail r + r ^ (-c)) := by
  intro h
  have htend : Tendsto (fun r : ℝ => C * (tail r + r ^ (-c))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => tail r + r ^ (-c)) atTop (𝓝 (0 + 0)) :=
      hlim.add (tendsto_rpow_neg_atTop hc)
    simpa using h1.const_mul C
  have hev : ∀ᶠ r : ℝ in atTop, C * (tail r + r ^ (-c)) < 1 :=
    htend.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨r, hlt, hr⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists
  have hpos : 0 < r := by linarith
  have h1 := hT3 r hpos
  have h2 := h r hpos
  linarith

end Generic

namespace SourceModelData

/-- **The `ℓ = 3` diagonal is at least one, at every cutoff.** -/
theorem one_le_cutThreefold (M : SourceModelData) (r : ℝ) : 1 ≤ M.cutThreefold r :=
  one_le_threefold_tsum (κ := M.cutTwoPointE r) (M.cutTwoPointE_self_eq_one r 0)

/-- **The `ℓ = 3` instance of Lemma I.4.18's conclusion is refutable at the model.**

The truncated threefold convolution at the origin is at least `1` for every cutoff
(`one_le_cutThreefold`), so it cannot be bounded by `C (∇_{r^c} + r^{-c}) (E|K|)^0` once the
far tail `∇_{r^c}` decays: that right-hand side tends to `0`.  The source's own near-sum step
at `ℓ = 3` would need `1 ≤ |B_R| (E|K|)^{-1}`, i.e. `E|K| ≤ |B_R| ≍ R^d = r^{α/2}`, which
contradicts `E|K| ⪰ r^α`.  Hence the source-faithful statement starts at `ℓ = 4`, where
`ℓ - 4 ≥ 0` and the step `|B_R| (E|K|)^{ℓ-4}` is legitimate. -/
theorem not_source_ell_three_bound (M : SourceModelData) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (tail : ℝ → ℝ) (htail : ∀ r : ℝ, 0 ≤ tail r) (hlim : Tendsto tail atTop (𝓝 0)) :
    ¬ ∀ r : ℝ, 0 < r → M.cutThreefold r ≤ ENNReal.ofReal (C * (tail r + r ^ (-c))) := by
  intro h
  have htend : Tendsto (fun r : ℝ => C * (tail r + r ^ (-c))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => tail r + r ^ (-c)) atTop (𝓝 (0 + 0)) :=
      hlim.add (tendsto_rpow_neg_atTop hc)
    simpa using h1.const_mul C
  have hev : ∀ᶠ r : ℝ in atTop, C * (tail r + r ^ (-c)) < 1 :=
    htend.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨r, hlt, hr⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists
  have hpos : 0 < r := by linarith
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C * (tail r + r ^ (-c))) :=
    le_trans (M.one_le_cutThreefold r) (h r hpos)
  have hx0 : 0 ≤ C * (tail r + r ^ (-c)) := by
    have hrn : 0 ≤ r ^ (-c) := Real.rpow_nonneg (by linarith) _
    exact mul_nonneg hC.le (by linarith [htail r])
  have h3 : (1 : ℝ) ≤ C * (tail r + r ^ (-c)) := by
    have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h1
    rwa [ENNReal.toReal_one, ENNReal.toReal_ofReal hx0] at ht
  linarith

end SourceModelData

end PercLib.CriticalLRP.Orchestration
