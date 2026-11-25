/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Universal tightness in the canonical model: edian existence, window monotonicity,
  and Corollary I.2.5 for real exponents

Hutchcroft, arXiv:2508.18807v1, Theorem I.2.3 and Corollary I.2.5.

This file supplies four things that the existing `Tightness/` development leaves implicit:

1. **Existence of the edian from a.e. finiteness.**  `edianOf` (and hence the paper's
   `M_β(W)`) is defined as `min{n : μ{n ≤ X} ≤ e^{-1}}`, and every lemma in
   `Tightness/MaxCluster.lean` carries the existence of such an `n` as an explicit hypothesis.
   Here it is *derived*: for a finite measure and an a.e. finite extended cardinality `X` the
   admissible set is nonempty, because `{n ≤ X} ↓ {X = ⊤}` and the latter is null.

2. **Monotonicity.**  The edian is monotone in the random variable, and the window functionals
   `|K_v ∩ W|`, `|K_max(W)|` and the edian `M_β(W)` are monotone in the window `W`.  (This is
   the trivial half of "universal tightness"; it makes the family of scales coherent across
   windows.)

3. **Corollary I.2.5 for real exponents** -- the generality in which the paper states and uses
   it -- for an arbitrary `ℝ≥0∞`-valued a.e. finite `X`, obtained from `Tightness/momentConstR`
   (the real-exponent layer cake) by truncating to `ℝ`, and then instantiated at `|K_v ∩ W|` in
   the canonical model.  `corollary_I_2_5_real` covers `p > 0`, `q ≥ 0`;
   `corollary_I_2_5_real_nonneg` covers the paper's full range `p, q ≥ 0` (at `p = 0` the
   right-hand side is `M^q`, since `E X^0 = 1`).

4. **The abstract part of Lemma I.2.6**: the edian bounds the moments from below,
   `(M-1)^p · e^{-1} ≤ E X^p` (and `(M-1)/e ≤ E X`), complementing the upper bound of
   Corollary I.2.5.  The paper's extra factor `1/|B_r|` comes from a transitivity/counting
   argument that is not in this file.

The only input from Theorem I.2.3 is the exponential tail (I.2.6), carried as `TailI26`.
Nothing here reproves (I.2.3) itself: in particular neither (I.2.4) nor (I.2.5) is derived.
-/
module

public import PercLib.CriticalLRP.Tightness.MaxCluster
public import PercLib.CriticalLRP.Tightness.MomentRatio
public import PercLib.CriticalLRP.Tightness.RealMomentRatio

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Percolation

variable {V : Type*} [Countable V]

/-! ### 1. Existence of the edian from a.e. finiteness -/

/-- **Existence of the edian.**  If `μ` is a finite measure and `X` is a.e. finite, then the
admissible set `{n : μ{n ≤ X} ≤ e^{-1}}` of the paper's edian definition is nonempty. -/
theorem exists_edian_of_ae_finite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ≥0∞} (hX : Measurable X) (hfin : μ {ω | X ω = ⊤} = 0) :
    ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1)) := by
  have hanti : Antitone fun n : ℕ => {ω : Ω | (n : ℝ≥0∞) ≤ X ω} := by
    intro a b hab ω hω
    have hcast : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hab
    exact le_trans hcast hω
  have hInter : (⋂ n : ℕ, {ω : Ω | (n : ℝ≥0∞) ≤ X ω}) = {ω : Ω | X ω = ⊤} := by
    ext ω
    simp only [mem_iInter]
    constructor
    · intro h
      by_contra hne
      obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ≥0∞) = X ω :=
        ⟨(X ω).toNNReal, ENNReal.coe_toNNReal hne⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ, r < n := exists_nat_gt r
      have hle : (n : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by
        rw [hr]; exact h n
      have h2 : (n : ℝ≥0) ≤ r := by exact_mod_cast hle
      exact absurd h2 (not_le.mpr hn)
    · intro h n
      show (n : ℝ≥0∞) ≤ X ω
      rw [h]
      exact le_top
  have htend := tendsto_measure_iInter_atTop
    (fun n => (hX measurableSet_Ici).nullMeasurableSet) hanti ⟨0, (measure_lt_top μ _).ne⟩
  have hInter' : (⋂ n : ℕ, X ⁻¹' Set.Ici (n : ℝ≥0∞)) = {ω : Ω | X ω = ⊤} := hInter
  rw [hInter', hfin] at htend
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-1)) := by
    rw [ENNReal.ofReal_pos]
    exact Real.exp_pos _
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (eventually_lt_nhds hpos))
  exact ⟨N, le_of_lt (hN N le_rfl)⟩

/-- **Monotonicity of the edian.**  If `X ≤ Y` pointwise then `edian X ≤ edian Y`. -/
theorem edianOf_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ≥0∞}
    (hXY : ∀ ω, X ω ≤ Y ω)
    {hexX : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1))}
    {hexY : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-1))} :
    edianOf μ X hexX ≤ edianOf μ Y hexY := by
  refine Nat.find_min' hexX ?_
  refine le_trans (measure_mono (fun ω hω => le_trans hω (hXY ω))) ?_
  exact edianOf_spec

/-! ### 2. Window monotonicity in the canonical model -/

omit [Countable V] in
/-- `|K_v ∩ W|` is monotone in the window `W`. -/
theorem clusterVolIn_mono_window (ω : Config V) (v : V) {W W' : Set V} (h : W ⊆ W') :
    clusterVolIn ω v W ≤ clusterVolIn ω v W' := by
  have h1 : ((cluster ω v) ∩ W).encard ≤ ((cluster ω v) ∩ W').encard :=
    Set.encard_mono (Set.inter_subset_inter subset_rfl h)
  rw [clusterVolIn, clusterVolIn]
  exact_mod_cast h1

/-- `|K_max(W)|` is monotone in the window `W`. -/
theorem clusterMaxVol_mono_window (ω : Config V) {W W' : Finset V} (h : W ⊆ W') :
    clusterMaxVol ω W ≤ clusterMaxVol ω W' := by
  refine Finset.sup_le fun w hw => ?_
  exact le_trans (clusterVolIn_mono_window ω w (by simpa using h))
    (clusterVolIn_le_clusterMaxVol ω (h hw))

/-- The edian `M_β(W)` of the maximum cluster size is monotone in the window `W`. -/
theorem edianMaxVol_mono_window {μ : Measure (Config V)} {W W' : Finset V} (h : W ⊆ W')
    (hexW : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤ ENNReal.ofReal (Real.exp (-1)))
    (hexW' : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W'} ≤
      ENNReal.ofReal (Real.exp (-1))) :
    edianMaxVol μ W hexW ≤ edianMaxVol μ W' hexW' :=
  edianOf_mono (fun ω => clusterMaxVol_mono_window ω h) (hexX := hexW) (hexY := hexW')

/-! ### 3. The real-exponent moment ratio for extended cardinalities -/

/-- Transfer of the tail event from `X : Ω → ℝ≥0∞` to its real truncation `X.toReal`, using
a.e. finiteness. -/
lemma measure_toReal_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hfin : μ {ω | X ω = ⊤} = 0) (t : ℝ) :
    μ {ω : Ω | t ≤ (X ω).toReal} = μ {ω : Ω | ENNReal.ofReal t ≤ X ω} := by
  have haefin : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := measure_eq_zero_iff_ae_notMem.mp hfin
  refine measure_congr ?_
  filter_upwards [haefin] with ω hω
  exact propext (ENNReal.ofReal_le_iff_le_toReal hω).symm

/-- Transfer of the `r`-th moment from `X : Ω → ℝ≥0∞` to its real truncation. -/
lemma lintegral_rpow_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hfin : μ {ω | X ω = ⊤} = 0) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ω, X ω ^ r ∂μ = ∫⁻ ω, ENNReal.ofReal ((X ω).toReal ^ r) ∂μ := by
  have haefin : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := measure_eq_zero_iff_ae_notMem.mp hfin
  refine lintegral_congr_ae ?_
  filter_upwards [haefin] with ω hω
  calc X ω ^ r = (ENNReal.ofReal (X ω).toReal) ^ r := by rw [ENNReal.ofReal_toReal hω]
    _ = ENNReal.ofReal ((X ω).toReal ^ r) :=
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr

/-- The real-exponent layer cake applied to `ℝ≥0∞`-valued a.e. finite `X`: transferring the
statement from `X.toReal` by a.e. equality. -/
theorem moment_ratio_le_rpow_ennreal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (hfin : μ {ω | X ω = ⊤} = 0)
    {M : ℝ} (hM : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | ENNReal.ofReal t ≤ X ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal M ≤ X ω})
    {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ ≤
      ENNReal.ofReal (Tightness.momentConstR p q) * ENNReal.ofReal (M ^ q) *
        ∫⁻ ω, X ω ^ p ∂μ := by
  have htail' : ∀ t : ℝ, M ≤ t → μ {ω : Ω | t ≤ (X ω).toReal} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω : Ω | M ≤ (X ω).toReal} := by
    intro t ht
    rw [measure_toReal_le hfin t, measure_toReal_le hfin M]
    exact htail t ht
  have hmain := Tightness.moment_ratio_le_rpow hX.ennreal_toReal
    (fun ω => ENNReal.toReal_nonneg) hM htail' hp hq
  rw [lintegral_rpow_toReal hfin (by linarith : (0 : ℝ) ≤ p + q),
    lintegral_rpow_toReal hfin hp.le]
  exact hmain

/-- The case `p = 0` of Corollary I.2.5 for extended cardinalities. -/
theorem moment_le_rpow_ennreal_of_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hfin : μ {ω | X ω = ⊤} = 0) {M : ℝ} (hM : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | ENNReal.ofReal t ≤ X ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal M ≤ X ω})
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, X ω ^ r ∂μ ≤
      ENNReal.ofReal (1 + Real.exp 1 * r * 9 ^ r * Real.Gamma r) * ENNReal.ofReal (M ^ r) := by
  have htail' : ∀ t : ℝ, M ≤ t → μ {ω : Ω | t ≤ (X ω).toReal} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω : Ω | M ≤ (X ω).toReal} := by
    intro t ht
    rw [measure_toReal_le hfin t, measure_toReal_le hfin M]
    exact htail t ht
  have hmain := Tightness.moment_le_rpow_of_tail hX.ennreal_toReal
    (fun ω => ENNReal.toReal_nonneg) hM htail' hr
  rw [lintegral_rpow_toReal hfin hr.le]
  exact hmain

/-- **Corollary I.2.5 for real exponents** from the exponential tail (I.2.6): for an a.e. finite
extended cardinality `X` (any `|K_v ∩ W|`, `|K_max(W)|`, ...) and real `p > 0`, `q ≥ 0`,

  `E X^{p+q} ≤ C(p,q) M^q E X^p`,  `C(p,q) = momentConstR p q`. -/
theorem corollary_I_2_5_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (hfin : μ {ω | X ω = ⊤} = 0)
    {M : ℕ} (hM : 1 ≤ M) (h : TailI26 μ X M) {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ ≤
      ENNReal.ofReal (Tightness.momentConstR p q) * ENNReal.ofReal ((M : ℝ) ^ q) *
        ∫⁻ ω, X ω ^ p ∂μ :=
  moment_ratio_le_rpow_ennreal hX hfin (by exact_mod_cast hM) h hp hq

/-- **Corollary I.2.5 for real exponents at the paper's scale**, for the truncated cluster
cardinality `|K_v ∩ W|` in the canonical model: from the single-cluster exponential tail
(I.2.6) at the edian scale `M`. -/
theorem corollary_I_2_5_real_clusterVolIn {μ : Measure (Config V)} (v : V) (W : Set V)
    {M : ℕ} (hM : 1 ≤ M) (hfin : μ {ω | clusterVolIn ω v W = ⊤} = 0)
    (h : TailI26 μ (fun ω => clusterVolIn ω v W) M) {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ∫⁻ ω, clusterVolIn ω v W ^ (p + q) ∂μ ≤
      ENNReal.ofReal (Tightness.momentConstR p q) * ENNReal.ofReal ((M : ℝ) ^ q) *
        ∫⁻ ω, clusterVolIn ω v W ^ p ∂μ :=
  corollary_I_2_5_real (measurable_clusterVolIn v W) hfin hM h hp hq


/-! ### 3b. The abstract part of Lemma I.2.6: the edian bounds the moments from below -/

/-- Markov's bound for extended cardinalities: `M^p μ{M ≤ X} ≤ E X^p`. -/
theorem ofReal_rpow_mul_meas_le_lintegral_ennreal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hX : Measurable X) (hfin : μ {ω | X ω = ⊤} = 0)
    {M : ℝ} (hM : 0 ≤ M) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (M ^ p) * μ {ω | ENNReal.ofReal M ≤ X ω} ≤ ∫⁻ ω, X ω ^ p ∂μ := by
  rw [← measure_toReal_le hfin M, lintegral_rpow_toReal hfin hp.le]
  exact Tightness.ofReal_rpow_mul_meas_le_lintegral hX.ennreal_toReal hM hp

/-- **Lemma I.2.6, abstract part.**  For a probability measure and an extended cardinality `X`,
the edian `M = min{n : μ{n ≤ X} ≤ e^{-1}}` satisfies

  `(M-1)^p · e^{-1} ≤ E X^p`,   `p > 0`,

i.e. the moments bound the edian from below.  (The paper's Lemma I.2.6 states the special case
`X = |K ∩ B_{2r}|` with the extra factor `1/|B_r|`, which comes from a transitivity/counting
argument over the translates of the window; that counting step is not part of this file.)

The proof is the minimality half of the edian definition (`μ{M-1 ≤ X} > e^{-1}`) together with
Markov's inequality applied on the event `{M-1 ≤ X}`. -/
theorem edian_moment_lower_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hfin : μ {ω | X ω = ⊤} = 0)
    {hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1))}
    {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (((edianOf μ X hex : ℝ) - 1) ^ p) * ENNReal.ofReal (Real.exp (-1)) ≤
      ∫⁻ ω, X ω ^ p ∂μ := by
  set M : ℕ := edianOf μ X hex with hMdef
  have hM1 : 1 ≤ M := one_le_edianOf
  have hMreal : (0 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  -- minimality of the edian: `M - 1` is not admissible
  have hmin : ENNReal.ofReal (Real.exp (-1)) < μ {ω | ((M - 1 : ℕ) : ℝ≥0∞) ≤ X ω} := by
    have := edianOf_min (μ := μ) (X := X) (hex := hex) (n := M - 1) (by omega)
    simpa [hMdef] using this
  -- the cast identity `((M-1 : ℕ) : ℝ≥0∞) = ofReal ((M : ℝ) - 1)`
  have hcast : ((M - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((M : ℝ) - 1) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_sub hM1, Nat.cast_one]
  have hmarkov := ofReal_rpow_mul_meas_le_lintegral_ennreal hX hfin hMreal hp (M := (M : ℝ) - 1)
  calc ENNReal.ofReal (((M : ℝ) - 1) ^ p) * ENNReal.ofReal (Real.exp (-1))
      ≤ ENNReal.ofReal (((M : ℝ) - 1) ^ p) * μ {ω | ((M - 1 : ℕ) : ℝ≥0∞) ≤ X ω} :=
        mul_le_mul_right (le_of_lt hmin) _
    _ = ENNReal.ofReal (((M : ℝ) - 1) ^ p) *
          μ {ω | ENNReal.ofReal ((M : ℝ) - 1) ≤ X ω} := by rw [hcast]
    _ ≤ ∫⁻ ω, X ω ^ p ∂μ := hmarkov

/-- **Lemma I.2.6 with `p = 1`**: for a probability measure, `(M - 1)/e ≤ E X`, i.e. the edian is
at most `e E X + 1`. -/
theorem edian_sub_one_div_exp_le_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hfin : μ {ω | X ω = ⊤} = 0)
    {hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-1))} :
    ENNReal.ofReal (((edianOf μ X hex : ℝ) - 1) / Real.exp 1) ≤ ∫⁻ ω, X ω ∂μ := by
  have h := edian_moment_lower_bound hX hfin (hex := hex) (p := 1) one_pos
  simp only [Real.rpow_one, ENNReal.rpow_one] at h
  have hMge : (0 : ℝ) ≤ (edianOf μ X hex : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (edianOf μ X hex : ℝ) := by
      exact_mod_cast one_le_edianOf (μ := μ) (X := X) (hex := hex)
    linarith
  have heq : ENNReal.ofReal (((edianOf μ X hex : ℝ) - 1) / Real.exp 1)
      = ENNReal.ofReal ((edianOf μ X hex : ℝ) - 1) * ENNReal.ofReal (Real.exp (-1)) := by
    rw [← ENNReal.ofReal_mul hMge, Real.exp_neg]
    congr 1
  simpa only [heq] using h


/-! ### 3c. Corollary I.2.5 on the full range `p, q ≥ 0` -/

/-- A constant valid on the whole range `p, q ≥ 0`.  For `p > 0` it dominates `momentConstR p q`
(it is `momentConstR p q + 1`), and at `p = 0` Lean's convention `x / 0 = 0` makes it equal to
`1 + e q 9^q Γ(q)`, the constant of `moment_le_rpow_of_tail` -- the `p = 0` case, where the
right-hand side of the paper's estimate is `M^q E X^0 = M^q`. -/
noncomputable def momentConstFull (p q : ℝ) : ℝ :=
  (p + q) / p + 1 + Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)

lemma momentConstR_le_momentConstFull (p q : ℝ) :
    Tightness.momentConstR p q ≤ momentConstFull p q := by
  unfold Tightness.momentConstR momentConstFull
  linarith [show (0 : ℝ) ≤ 1 from zero_le_one]

/-- **Corollary I.2.5 for the full range `p, q ≥ 0`** (the paper's statement), for an arbitrary
a.e. finite extended cardinality `X` with the exponential tail (I.2.6) at a scale `M ≥ 1`:

  `E X^{p+q} ≤ C(p,q) M^q E X^p`  for all real `p, q ≥ 0`,  `C = momentConstFull p q`.

The `p = 0` case uses `E X^0 = 1` in `ℝ≥0∞`; the paper's `E|K_x ∩ W|^0` is `1` because
`|K_x ∩ W| ≥ 1`. -/
theorem corollary_I_2_5_real_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hfin : μ {ω | X ω = ⊤} = 0) {M : ℕ} (hM : 1 ≤ M) (h : TailI26 μ X M)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ ≤
      ENNReal.ofReal (momentConstFull p q) * ENNReal.ofReal ((M : ℝ) ^ q) *
        ∫⁻ ω, X ω ^ p ∂μ := by
  have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hX0 : ∫⁻ ω, X ω ^ ((0 : ℝ)) ∂μ = 1 := by
    simp only [ENNReal.rpow_zero, lintegral_one, measure_univ]
  rcases eq_or_lt_of_le hp with hp0 | hppos
  · -- `p = 0`: `E X^0 = 1`
    subst hp0
    rw [zero_add, hX0, mul_one]
    rcases eq_or_lt_of_le hq with hq0 | hqpos
    · -- `p = q = 0`
      subst hq0
      have hc : momentConstFull 0 0 = 1 := by simp [momentConstFull]
      rw [hc]
      simp
    · -- `p = 0 < q`
      have hc : momentConstFull 0 q = 1 + Real.exp 1 * q * 9 ^ q * Real.Gamma q := by
        simp [momentConstFull]
      rw [hc]
      exact moment_le_rpow_ennreal_of_tail hX hfin hM' h hqpos
  · -- `p > 0`
    refine le_trans (moment_ratio_le_rpow_ennreal hX hfin hM' h hppos hq) ?_
    refine mul_le_mul_left (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (momentConstR_le_momentConstFull p q)) _) _

/-! ### 4. Packaging at the edian scale -/

omit [Countable V] in
/-- Truncation to a finite window makes cluster cardinality finite, independently of
subcriticality of the infinite-volume graph. -/
lemma clusterVolIn_ne_top_of_finite {V : Type*} (ω : Config V) (v : V) {W : Set V}
    (hW : W.Finite) : clusterVolIn ω v W ≠ ⊤ := by
  have hfin : (cluster ω v ∩ W).Finite := hW.subset Set.inter_subset_right
  have hencard : (cluster ω v ∩ W).encard ≠ ⊤ := by
    intro htop
    exact Set.not_infinite.mpr hfin (Set.encard_eq_top_iff.mp htop)
  rw [clusterVolIn]
  exact_mod_cast hencard

/-- The maximum truncated cluster size in a finite window is always finite. -/
lemma clusterMaxVol_ne_top (ω : Config V) (W : Finset V) : clusterMaxVol ω W ≠ ⊤ := by
  intro htop
  obtain ⟨w, hw, htopw⟩ := Finset.sup_eq_top_iff.mp htop
  exact clusterVolIn_ne_top_of_finite ω w W.finite_toSet htopw

/-- A finite-window maximum cluster has zero probability of being infinite for every measure. -/
lemma ae_finite_clusterMaxVol {μ : Measure (Config V)} (W : Finset V) :
    μ {ω | clusterMaxVol ω W = ⊤} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards with ω
  exact clusterMaxVol_ne_top ω W

/-- If the maximum cluster size in a window is a.e. finite then so is `|K_v ∩ W|` for `v ∈ W`
(it is bounded by the maximum). -/
theorem ae_finite_clusterVolIn {μ : Measure (Config V)} (v : V) {W : Finset V} (hv : v ∈ W)
    (h : μ {ω | clusterMaxVol ω W = ⊤} = 0) :
    μ {ω | clusterVolIn ω v (W : Set V) = ⊤} = 0 := by
  refine measure_mono_null (fun ω hω => ?_) h
  by_contra hne
  have hlt : clusterMaxVol ω W < ⊤ := lt_top_iff_ne_top.mpr hne
  have hne' : clusterVolIn ω v (W : Set V) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (clusterVolIn_le_clusterMaxVol ω hv) hlt)
  exact hne' hω

/-- Existence of the edian `M_β(W)` of the maximum cluster size in every finite window.
No subcriticality hypothesis is needed. -/
theorem exists_edianMaxVol {μ : Measure (Config V)} [IsFiniteMeasure μ] (W : Finset V) :
    ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤ ENNReal.ofReal (Real.exp (-1)) :=
  exists_edian_of_ae_finite (measurable_clusterMaxVol W) (ae_finite_clusterMaxVol W)

/-- **Corollary I.2.5 for real exponents at the paper's scale `M_β(W)`**, for `|K_v ∩ W|` with
`v ∈ W`: from the single-cluster exponential tail (I.2.6) at the edian of the *maximum* cluster
size, `E|K_v ∩ W|^{p+q} ≤ C(p,q) M_β(W)^q E|K_v ∩ W|^p` for real `p > 0`, `q ≥ 0`.

Only (I.2.6) remains a probabilistic hypothesis. The finite-window cardinalities are
automatically finite, so the edian exists without a subcriticality hypothesis. -/
theorem corollary_I_2_5_real_at_edian {μ : Measure (Config V)} [IsProbabilityMeasure μ]
    (v : V) (W : Finset V) (hv : v ∈ W)
    (h : TailI26 μ (fun ω => clusterVolIn ω v (W : Set V))
      (edianMaxVol μ W (exists_edianMaxVol W)))
    {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ∫⁻ ω, clusterVolIn ω v (W : Set V) ^ (p + q) ∂μ ≤
      ENNReal.ofReal (Tightness.momentConstR p q) *
        ENNReal.ofReal ((edianMaxVol μ W (exists_edianMaxVol W) : ℝ) ^ q) *
        ∫⁻ ω, clusterVolIn ω v (W : Set V) ^ p ∂μ :=
  corollary_I_2_5_real_clusterVolIn v (W : Set V)
    (one_le_edianMaxVol W (exists_edianMaxVol W))
    (by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards with ω
      exact clusterVolIn_ne_top_of_finite ω v W.finite_toSet) h hp hq

/-- **The `p = 0` case of Corollary I.2.5 in the canonical model**: the exponential tail (I.2.6)
at scale `M` alone gives `E|K_v ∩ W|^r ≤ (1 + e r 9^r Γ(r)) M^r` for every real `r > 0`. -/
theorem moment_le_rpow_clusterVolIn {μ : Measure (Config V)} [IsProbabilityMeasure μ]
    (v : V) (W : Set V) {M : ℕ} (hM : 1 ≤ M)
    (hfin : μ {ω | clusterVolIn ω v W = ⊤} = 0)
    (h : TailI26 μ (fun ω => clusterVolIn ω v W) M) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, clusterVolIn ω v W ^ r ∂μ ≤
      ENNReal.ofReal (1 + Real.exp 1 * r * 9 ^ r * Real.Gamma r) *
        ENNReal.ofReal ((M : ℝ) ^ r) :=
  moment_le_rpow_ennreal_of_tail (measurable_clusterVolIn v W) hfin
    (by exact_mod_cast hM) h hr

end Percolation

end PercLib.CriticalLRP
