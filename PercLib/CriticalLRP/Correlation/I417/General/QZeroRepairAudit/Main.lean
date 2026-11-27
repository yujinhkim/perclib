/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

Ultramath swarm `smwziumdb`, member `m2`, direction `d5`.

# The exact per-vertex split: star = product gap + covariance, and the Case-3 window identity

`Defs.lean` isolated the four per-vertex objects.  This file proves the exact identities that
separate the paper's **product-minus-excluded** Case-3 numerator from the one-copy **star** moment:

* `jointVert_eq_excl_add_star` —
  `E[|K_o|^a|K_y|^b] = E[1(o↮y)|K_o|^a|K_y|^b] + E[1(o↔y)|K_o|^{a+b}]`
  (exact, in `ℝ≥0∞`, no finiteness hypothesis; the second term uses `K_y = K_o` on `{o ↔ y}`);
* `prodVert_le_jointVert` — Harris/FKG: the product factor is dominated by the joint moment
  (the `q ≥ 1` component of Lemma I.2.1 applied to the marked functionals `|K_o|^a`, `|K_y|^b`);
* `exclVert_le_prodVert` — BK: the excluded moment is dominated by the product factor
  (`I420Case1.hrest_pow_le`);
* `gapVert_le_starVert` — consequently `0 ≤ gap ≤ star` at every vertex: the star *is* an upper
  bound for the product gap, and the difference is the covariance;
* `starVert_toReal_eq_gapVert_add_covVert` — the **exact identity** `star = gap + cov` in `ℝ`,
  with the covariance `Cov(|K_o|^a, |K_y|^b) ≥ 0`;
* `starVert_self_eq_powMomentAt`, `exclVert_self_eq_zero`, `gapVert_self_eq_prodVert` — at the
  diagonal the excluded moment vanishes, so the product gap collapses to `χ · E|K|²` while the
  star collapses to `E|K|³`: this is the exact mechanism of the diagonal obstruction, and it shows
  that the product-gap target is *not* refuted at the diagonal.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Defs

/-! # Independently reviewed Case-3 repair-audit module: Main -/


noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace QZeroRepairAudit

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. Bridge to the `Connects`-indicator form

`I420Case1.hrest_pow_le` and `hrest_pow_le_add` are stated with the connection indicator
`{ω | Connects ω o y}`; `starVert`/`exclVert` are stated with the cluster indicator.  These two
lemmas change the form (exactly, not up to anything). -/

/-- The cluster indicator at `y` is the connection indicator `o ↔ y`. -/
theorem starVert_eq_connIndicator (π : Sym2 V → unitInterval) (o y : V) (p : ℕ) :
    starVert π o y p
      = ∫⁻ ω, {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          clusterVol ω o ^ p ∂(edgeMeasure π) := by
  simp only [starVert]
  refine lintegral_congr fun ω => ?_
  rw [I420Case1.indicator_cluster (V := V) ω o y, mul_comm]

/-- The excluded integrand is the `¬ Connects`-indicator form of `I420Case1.hrest_pow_le`. -/
theorem exclVert_eq_connIndicator (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) :
    exclVert π o y a b
      = ∫⁻ ω, {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (clusterVol ω o ^ a * clusterVol ω y ^ b) ∂(edgeMeasure π) := by
  simp only [exclVert]
  refine lintegral_congr fun ω => ?_
  rw [I420Case1.indicator_compl_cluster (V := V) ω o y]
  ring

/-- Measurability of the `o ↔ y` connection indicator, as a function of the configuration. -/
theorem measurable_connIndicator (o y : V) :
    Measurable (fun ω : Config V =>
      {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω) :=
  measurable_const.indicator (measurableSet_connects (V := V) o y)

/-- Measurability of the `o ↮ y` disconnection indicator. -/
theorem measurable_notConnIndicator (o y : V) :
    Measurable (fun ω : Config V =>
      {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω) :=
  measurable_const.indicator (measurableSet_connects (V := V) o y).compl

/-- Measurability of `ω ↦ |K_o|^a |K_y|^b`. -/
theorem measurable_clusterVol_mul (o y : V) (a b : ℕ) :
    Measurable (fun ω : Config V => clusterVol ω o ^ a * clusterVol ω y ^ b) :=
  ((measurable_clusterVol (V := V) o).pow_const a).mul
    ((measurable_clusterVol (V := V) y).pow_const b)


/-- **Split an integral along a pointwise partition.**  If `H = F + G` pointwise and `F` is
measurable, then `∫ H = ∫ F + ∫ G`.  Stated with all three integrands explicit so that the shape
of the goal is never ambiguous. -/
theorem lintegral_eq_add_of_pointwise (μ : Measure (Config V)) {F G H : Config V → ℝ≥0∞}
    (hF : Measurable F) (h : ∀ ω, H ω = F ω + G ω) :
    ∫⁻ ω, H ω ∂μ = (∫⁻ ω, F ω ∂μ) + ∫⁻ ω, G ω ∂μ := by
  rw [show (∫⁻ ω, H ω ∂μ) = ∫⁻ ω, (F ω + G ω) ∂μ from
    lintegral_congr h]
  exact lintegral_add_left hF G

/-! ## 2. The exact partition identity `joint = excl + star` -/

/-- On `{o ↔ y}` the two clusters agree, so `|K_y|^b = |K_o|^b`. -/
theorem clusterVol_eq_of_connects {ω : Config V} {o y : V} (h : Connects ω o y) :
    clusterVol ω y = clusterVol ω o := by
  have hcl : cluster ω y = cluster ω o := cluster_eq_iff.2 h.symm
  simp only [clusterVol, hcl]

/-- **The exact per-vertex partition identity**
`E[|K_o|^a |K_y|^b] = E[1(o ↮ y)|K_o|^a|K_y|^b] + E[1(o ↔ y)|K_o|^{a+b}]`.

This is an identity, not an inequality, and it holds in `ℝ≥0∞` with no finiteness hypothesis.  The
second summand is the one-copy star moment at exponent `a+b`; the first is the subtracted term of
Lemma I.4.17.  In particular the joint moment, *not* the product factor, is the sum of the two. -/
theorem jointVert_eq_excl_add_star (π : Sym2 V → unitInterval) (o y : V) (a b : ℕ) :
    jointVert π o y a b = exclVert π o y a b + starVert π o y (a + b) := by
  rw [exclVert_eq_connIndicator, starVert_eq_connIndicator, jointVert]
  refine lintegral_eq_add_of_pointwise (edgeMeasure π)
    (F := fun ω => {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      (clusterVol ω o ^ a * clusterVol ω y ^ b))
    (G := fun ω => {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      clusterVol ω o ^ (a + b))
    (H := fun ω => clusterVol ω o ^ a * clusterVol ω y ^ b)
    ((measurable_notConnIndicator (V := V) o y).mul
      (measurable_clusterVol_mul (V := V) o y a b)) ?_
  intro ω
  by_cases hc : Connects ω o y
  · have hc' : clusterVol ω y = clusterVol ω o := clusterVol_eq_of_connects hc
    have h1 : {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 :=
      Set.indicator_of_notMem (s := {ω' : Config V | ¬ Connects ω' o y}) (by simpa using hc) _
    have h2 : {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 :=
      Set.indicator_of_mem (s := {ω' : Config V | Connects ω' o y}) hc _
    rw [h1, h2, hc', zero_mul, zero_add, one_mul, ← pow_add]
  · have h1 : {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 :=
      Set.indicator_of_mem (s := {ω' : Config V | ¬ Connects ω' o y}) hc _
    have h2 : {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 :=
      Set.indicator_of_notMem (s := {ω' : Config V | Connects ω' o y}) hc _
    rw [h2, h1, zero_mul, add_zero, one_mul]

/-! ## 3. The two halves of Lemma I.2.1 and the sandwich `0 ≤ gap ≤ star` -/

/-- **Harris/FKG half**: the product factor is dominated by the joint moment,
`E|K_o|^a E|K_y|^b ≤ E[|K_o|^a|K_y|^b]`.  In covariance form this is
`Cov(|K_o|^a,|K_y|^b) ≥ 0`, which is the reason the star strictly exceeds the product gap. -/
theorem prodVert_le_jointVert (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o y : V) (a b : ℕ) :
    prodVert π o y a b ≤ jointVert π o y a b := by
  have h := I420Case1.hrest_pow_le_add (V := V) (π := π) hπ 𝓔 h𝓔mono h𝓔 o y a b
  have hcombine : (∫⁻ ω, {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω o ^ a * clusterVol ω y ^ b) ∂(edgeMeasure π)) +
      ∫⁻ ω, {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω o ^ a * clusterVol ω o ^ b) ∂(edgeMeasure π) = jointVert π o y a b := by
    rw [jointVert]
    refine (lintegral_eq_add_of_pointwise (edgeMeasure π)
      (F := fun ω => {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω o ^ a * clusterVol ω y ^ b))
      (G := fun ω => {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω o ^ a * clusterVol ω o ^ b))
      (H := fun ω => clusterVol ω o ^ a * clusterVol ω y ^ b)
      ((measurable_notConnIndicator (V := V) o y).mul
        (measurable_clusterVol_mul (V := V) o y a b)) ?_).symm
    intro ω
    by_cases hc : Connects ω o y
    · have hc' : clusterVol ω y = clusterVol ω o := clusterVol_eq_of_connects hc
      have h1 : {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 :=
        Set.indicator_of_notMem (s := {ω' : Config V | ¬ Connects ω' o y}) (by simpa using hc) _
      have h2 : {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 :=
        Set.indicator_of_mem (s := {ω' : Config V | Connects ω' o y}) hc _
      rw [h1, h2, hc', zero_mul, zero_add, one_mul]
    · have h1 : {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 :=
        Set.indicator_of_mem (s := {ω' : Config V | ¬ Connects ω' o y}) hc _
      have h2 : {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 :=
        Set.indicator_of_notMem (s := {ω' : Config V | Connects ω' o y}) hc _
      rw [h2, h1, zero_mul, add_zero, one_mul]
  exact h.trans (le_of_eq hcombine)

/-- **BK half**: the excluded moment is dominated by the product factor
(`I420Case1.hrest_pow_le`, i.e. the nonnegativity half of Lemma I.2.1). -/
theorem exclVert_le_prodVert (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o y : V) (a b : ℕ) :
    exclVert π o y a b ≤ prodVert π o y a b := by
  rw [exclVert_eq_connIndicator]
  exact I420Case1.hrest_pow_le (V := V) (π := π) hπ 𝓔 h𝓔mono h𝓔 o y a b

/-- **`0 ≤ gap ≤ star`**, i.e. `prod − excl ≤ star`.  This is display (I.4.16) at the per-vertex
level: the product gap is nonnegative (BK) and dominated by the one-copy star (Harris).  The
inequality is strict in general; the difference is the covariance
(`starVert_toReal_eq_gapVert_add_covVert`). -/
theorem gapVert_le_starVert (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o y : V) (a b : ℕ) :
    gapVert π o y a b ≤ starVert π o y (a + b) := by
  have hEq : (∫⁻ ω, {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        clusterVol ω o ^ (a + b) ∂(edgeMeasure π))
      = ∫⁻ ω, {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω o ^ a * clusterVol ω o ^ b) ∂(edgeMeasure π) := by
    refine lintegral_congr fun ω => ?_
    rw [pow_add]
  rw [gapVert, tsub_le_iff_left, exclVert_eq_connIndicator, starVert_eq_connIndicator, prodVert,
    hEq]
  exact I420Case1.hrest_pow_le_add (V := V) (π := π) hπ 𝓔 h𝓔mono h𝓔 o y a b

/-- **The exact identity** `star = gap + cov` in `ℝ`, under the two finiteness hypotheses that make
the `ℝ≥0∞` truncated subtractions faithful.  The covariance term is
`Cov(|K_o|^a, |K_y|^b) = E[|K_o|^a|K_y|^b] − E|K_o|^a E|K_y|^b ≥ 0`.

Consequence: *any* bound on the product gap `gap` alone leaves the covariance uncontrolled, so it
does not bound the star.  Conversely, `gap` bound + covariance bound does bound the star. -/
theorem starVert_toReal_eq_gapVert_add_covVert (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o y : V) (a b : ℕ)
    (hP : prodVert π o y a b ≠ ⊤) (hJ : jointVert π o y a b ≠ ⊤) :
    (starVert π o y (a + b)).toReal
      = (gapVert π o y a b).toReal + (covVert π o y a b).toReal := by
  have hEP : exclVert π o y a b ≤ prodVert π o y a b :=
    exclVert_le_prodVert π hπ 𝓔 h𝓔mono h𝓔 o y a b
  have hPJ : prodVert π o y a b ≤ jointVert π o y a b :=
    prodVert_le_jointVert π hπ 𝓔 h𝓔mono h𝓔 o y a b
  have hJe : jointVert π o y a b = exclVert π o y a b + starVert π o y (a + b) :=
    jointVert_eq_excl_add_star π o y a b
  have hEtop : exclVert π o y a b ≠ ⊤ := ne_top_of_le_ne_top hP hEP
  have hStop : starVert π o y (a + b) ≠ ⊤ := by
    rw [hJe] at hJ
    exact (ENNReal.add_ne_top.mp hJ).2
  have hG : (gapVert π o y a b).toReal
      = (prodVert π o y a b).toReal - (exclVert π o y a b).toReal :=
    ENNReal.toReal_sub_of_le hEP hP
  have hC : (covVert π o y a b).toReal
      = (jointVert π o y a b).toReal - (prodVert π o y a b).toReal :=
    ENNReal.toReal_sub_of_le hPJ hJ
  have hS : (starVert π o y (a + b)).toReal
      = (jointVert π o y a b).toReal - (exclVert π o y a b).toReal := by
    have h := congrArg ENNReal.toReal hJe
    rw [ENNReal.toReal_add hEtop hStop] at h
    have h2 := ENNReal.toReal_mono hP hEP
    have h1 := ENNReal.toReal_mono hJ hPJ
    linarith
  have h1 : (prodVert π o y a b).toReal ≤ (jointVert π o y a b).toReal :=
    ENNReal.toReal_mono hJ hPJ
  have h2 : (exclVert π o y a b).toReal ≤ (prodVert π o y a b).toReal :=
    ENNReal.toReal_mono hP hEP
  rw [hG, hC, hS]
  ring

/-! ## 4. The diagonal: the two targets separate cleanly -/

/-- The excluded moment at the diagonal vanishes (`o ∈ K_o` always). -/
theorem exclVert_self_eq_zero (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) :
    exclVert π o o a b = 0 := by
  have hzero : ∀ ω : Config V,
      clusterVol ω o ^ a *
        ((cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) o * clusterVol ω o ^ b) = 0 := by
    intro ω
    have hmem : o ∈ cluster ω o := cluster_mem_self ω o
    have h0 : (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) o = 0 :=
      Set.indicator_of_notMem (s := (cluster ω o)ᶜ) (by simpa using hmem) _
    rw [h0, zero_mul, mul_zero]
  simp only [exclVert]
  rw [show (fun ω : Config V => clusterVol ω o ^ a *
      ((cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) o * clusterVol ω o ^ b)) = fun _ => 0
    from funext hzero]
  simp

/-- The star at the diagonal is the plain moment `E|K_o|^p`. -/
theorem starVert_self_eq_powMomentAt (π : Sym2 V → unitInterval) (o : V) (p : ℕ) :
    starVert π o o p = I420Case1.powMomentAt π p o := by
  simp only [starVert, I420Case1.powMomentAt]
  refine lintegral_congr fun ω => ?_
  have hmem : o ∈ cluster ω o := cluster_mem_self ω o
  simp only [Set.indicator_of_mem (s := cluster ω o) hmem, mul_one]

/-- The joint moment at the diagonal is `E|K_o|^{a+b}`. -/
theorem jointVert_self_eq_powMomentAt (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) :
    jointVert π o o a b = I420Case1.powMomentAt π (a + b) o := by
  simp only [jointVert, I420Case1.powMomentAt]
  refine lintegral_congr fun ω => ?_
  rw [← pow_add]

/-- **At the diagonal the product gap collapses to the product factor**: the excluded moment is
zero, so the product gap is `E|K_o|^a · E|K_o|^b`.  At `(a,b) = (1,2)` this is `χ · E|K|²`, which
is `≍ χ⁴` in Case 3 — *not* the `E|K|³ ≍ χ⁵` of the star.  So the product-gap target is not
refuted at `y = 0`, while the star target is. -/
theorem gapVert_self_eq_prodVert (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) :
    gapVert π o o a b = prodVert π o o a b := by
  rw [gapVert, exclVert_self_eq_zero, tsub_zero]

/-- At the diagonal the covariance is `E|K_o|^{a+b} − E|K_o|^a E|K_o|^b ≥ 0`. -/
theorem covVert_self_eq (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) :
    covVert π o o a b = I420Case1.powMomentAt π (a + b) o - prodVert π o o a b := by
  rw [covVert, jointVert_self_eq_powMomentAt]

end QZeroRepairAudit
end PercLib.CriticalLRP
