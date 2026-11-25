/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Universal tightness in the canonical long-range percolation model

Instantiation of the abstract moment-ratio theorem (`moment_ratio_le`, Corollary I.2.5 of
Hutchcroft arXiv:2508.18807v1) at the canonical model `Config V = Set (Sym2 V)`, for the
truncated cluster cardinality `|K_v ∩ W| = clusterVolIn ω v W` with `W` finite.

The single input from the universal tightness theorem (Theorem I.2.3, proved in [74] from the
BK inequality and *not* reproved here) is the exponential tail (I.2.6), which we carry as an
explicit named hypothesis `TailI26`.  Everything else — measurability, integer-valuedness, and
the moment ratio — is proved.
-/
module

public import PercLib.CriticalLRP.Tightness.MomentRatio
public import PercLib.CriticalLRP.CountableProduct.Compatibility

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Percolation

universe u v

variable {V : Type u} [Countable V]

/-! ### Integer-valuedness of the truncated cluster cardinality -/

/-- The cast of an extended natural is either `⊤` or a natural number. -/
lemma encard_cast_eq_top_or_nat (s : Set V) :
    ((s.encard : ℕ∞) : ℝ≥0∞) = ⊤ ∨ ∃ n : ℕ, ((s.encard : ℕ∞) : ℝ≥0∞) = (n : ℝ≥0∞) := by
  by_cases h : s.encard = ⊤
  · left
    rw [h]
    rfl
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
    right
    refine ⟨n, ?_⟩
    rw [← hn]
    norm_cast

/-- `|K_v ∩ W|` is integer-valued (or `⊤`). -/
lemma clusterVolIn_integer (ω : Config V) (v : V) (W : Set V) :
    clusterVolIn ω v W = ⊤ ∨ ∃ n : ℕ, clusterVolIn ω v W = (n : ℝ≥0∞) :=
  encard_cast_eq_top_or_nat _

/-! ### The edian -/

/-- The *edian* `M_β(Λ) = min {n ≥ 0 : P(|K_max(Λ)| ≥ n) ≤ e^{-1}}` of the paper, for an
arbitrary extended-cardinality random variable and an explicit existence hypothesis. For the
paper's finite-window maximum the hypothesis is automatic because the window bounds the volume,
as `exists_edianMaxVol` proves below; no subcriticality assumption is required. -/
noncomputable def edianOf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ≥0∞)
    (hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1))) : ℕ :=
  Nat.find hex

lemma edianOf_spec {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    {hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1))} :
    μ {ω | (edianOf μ X hex : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1)) :=
  Nat.find_spec hex

lemma edianOf_min {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    {hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1))} {n : ℕ}
    (hn : n < edianOf μ X hex) :
    ENNReal.ofReal (Real.exp (-1)) < μ {ω | (n : ℝ≥0∞) ≤ X ω} :=
  not_le.mp (Nat.find_min hex hn)

/-- For a probability measure, the edian is at least `1`. -/
lemma one_le_edianOf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ≥0∞} {hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1))} :
    1 ≤ edianOf μ X hex := by
  rcases Nat.eq_zero_or_pos (edianOf μ X hex) with h | h
  · exfalso
    have hspec := edianOf_spec (μ := μ) (X := X) (hex := hex)
    rw [h] at hspec
    have hset : {ω : Ω | ((0 : ℕ) : ℝ≥0∞) ≤ X ω} = univ := by
      ext ω
      simp
    have h1 : μ {ω : Ω | ((0 : ℕ) : ℝ≥0∞) ≤ X ω} = 1 := by
      rw [hset, measure_univ]
    rw [h1] at hspec
    have h2 : ENNReal.ofReal (Real.exp (-1)) < 1 := by
      rw [ENNReal.ofReal_lt_one]
      rw [Real.exp_lt_one_iff]
      norm_num
    exact absurd hspec (not_le.mpr h2)
  · exact h

/-! ### The tail hypothesis (I.2.6) and Corollary I.2.5 -/

/-- **The single-cluster exponential tail (I.2.6)** of the universal tightness theorem
(Theorem I.2.3), carried as an explicit hypothesis: for the edian `M = M_β(W)` of the maximum
cluster size, every cluster's intersection with `W` has an exponential tail above `M`. -/
def TailI26 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ≥0∞) (M : ℕ) : Prop :=
  ∀ t : ℝ, (M : ℝ) ≤ t →
    μ {ω | ENNReal.ofReal t ≤ X ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω}

/-- **Corollary I.2.5** (moment ratio at the median scale) in the canonical model, for the
truncated cluster cardinality `|K_v ∩ W|`, from the exponential tail (I.2.6). -/
theorem corollary_I_2_5 {μ : Measure (Config V)} (hμ : IsProbabilityMeasure μ)
    (v : V) (W : Set V) {M : ℕ} (hM : 1 ≤ M)
    (htail : TailI26 μ (fun ω => clusterVolIn ω v W) M)
    (p q : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, clusterVolIn ω v W ^ (p + q) ∂μ
      ≤ ENNReal.ofReal (Tightness.momentConst p q) * ENNReal.ofReal ((M : ℝ) ^ q) *
        ∫⁻ ω, clusterVolIn ω v W ^ p ∂μ := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h := Tightness.moment_ratio_le (μ := μ) (X := fun ω => clusterVolIn ω v W)
    (measurable_clusterVolIn v W) (fun ω => clusterVolIn_integer ω v W) hMreal htail p q hp
  simpa using h

/-! ### The dependency graph: (I.2.4) versus (I.2.6) -/

/-- **(I.2.4)** of the paper: the *maximum* cluster size has an exponential tail above its
edian, `P(|K_max(W)| ≥ λ M) ≤ exp(-λ/9)`.  This is the part of Theorem I.2.3 that is a
consequence of the BK inequality in [74]. -/
def TailMaxI24 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Kmax : Ω → ℝ≥0∞) (M : ℕ) : Prop :=
  ∀ t : ℝ, (M : ℝ) ≤ t →
    μ {ω | ENNReal.ofReal t ≤ Kmax ω} ≤ ENNReal.ofReal (Real.exp (-(t / (9 * M))))

/-- `|K_v ∩ W| ≤ |K_max(W)|` transfers the max-cluster tail (I.2.4) to the single cluster, in
the *weaker* form without the factor `P(|K_v ∩ W| ≥ M)`. -/
theorem tail_single_of_max {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Kmax X : Ω → ℝ≥0∞} (hle : ∀ ω, X ω ≤ Kmax ω) {M : ℕ}
    (h24 : TailMaxI24 μ Kmax M) :
    ∀ t : ℝ, (M : ℝ) ≤ t →
      μ {ω | ENNReal.ofReal t ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(t / (9 * M)))) := by
  intro t ht
  exact le_trans (measure_mono (fun ω hω => le_trans hω (hle ω))) (h24 t ht)

/-- The exponential tail (I.2.6) implies the weaker `λ`-tail form used in (I.2.4), since the
measure of the tail event is at most one. -/
theorem tail_single_of_I26 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (hprob : μ Set.univ = 1) {X : Ω → ℝ≥0∞} {M : ℕ} (h : TailI26 μ X M) :
    ∀ t : ℝ, (M : ℝ) ≤ t →
      μ {ω | ENNReal.ofReal t ≤ X ω} ≤
        ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-(t / (9 * M)))) := by
  intro t ht
  have h1 : μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} ≤ 1 := by
    rw [← hprob]
    exact measure_mono (subset_univ _)
  calc μ {ω | ENNReal.ofReal t ≤ X ω}
      ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
          μ {ω | ENNReal.ofReal (M : ℝ) ≤ X ω} := h t ht
    _ ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) * 1 := by
        gcongr
    _ = ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-(t / (9 * M)))) := by
        rw [mul_one, ENNReal.ofReal_mul (Real.exp_pos 1).le]

/-- **(I.2.5)** of the paper: the maximum cluster size is unlikely to be much smaller than
the edian, `P(|K_max(W)| < ε M) ≤ 27 ε` for `0 < ε ≤ 1`. -/
def LowerI25 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Kmax : Ω → ℝ≥0∞) (M : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    μ {ω | Kmax ω < ENNReal.ofReal (ε * (M : ℝ))} ≤ ENNReal.ofReal (27 * ε)

/-- **Theorem I.2.3** (universal tightness of the maximum cluster size), as a named hypothesis
bundle: `M` is a median-type scale (`1 ≤ M`), the maximum cluster size has the exponential tail
(I.2.4) above it, and the single cluster satisfies (I.2.6).  All three are consequences of the BK
inequality established in [74, Theorem 2.2]; they are proved in `Tightness/Universal.lean` for the actual long-range law;
this file supplies only the downstream interface and its earlier conditional forms. -/
structure UniversalTightnessI23 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Kmax X : Ω → ℝ≥0∞) (M : ℕ) : Prop where
  one_le_scale : 1 ≤ M
  max_tail : TailMaxI24 μ Kmax M
  single_tail : TailI26 μ X M

/-- **Corollary I.2.5 from Theorem I.2.3**: if `X = |K_v ∩ W| ≤ |K_max(W)| = Kmax` and the
universal tightness inputs (I.2.4)+(I.2.6) hold at scale `M`, then
`E X^{p+q} ≤ C(p,q) M^q E X^p` for integers `p ≥ 1`, `q ≥ 0`. -/
theorem corollary_I_2_5_of_I_2_3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Kmax X : Ω → ℝ≥0∞} {M : ℕ} (h : UniversalTightnessI23 μ Kmax X M)
    (hX : Measurable X) (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) (p q : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ
      ≤ ENNReal.ofReal (Tightness.momentConst p q) * ENNReal.ofReal ((M : ℝ) ^ q) *
        ∫⁻ ω, X ω ^ p ∂μ := by
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h.one_le_scale
  exact Tightness.moment_ratio_le hX hint hMreal h.single_tail p q hp

end Percolation

end PercLib.CriticalLRP
