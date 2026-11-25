/-
# Covariance and finite-moment bounds for the error `cE1`

The aggregated covariance is first stated in `ℝ≥0∞`, where an infinite mean
cluster volume causes no subtraction of infinities. The quotient bound for
`cE1` is then derived from its real finite-denominator form.
-/
module

public import PercLib.CriticalLRP.BK.FunctionalInterface
public import PercLib.CriticalLRP.Correlation.HvolRootIndependence
public import PercLib.CriticalLRP.MassTransportI41
public import PercLib.CriticalLRP.VolumeMoments.ErrorTerms

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.VolumeMoments

open MeasureTheory

open scoped ENNReal NNReal

/-- The finite-denominator algebra in Lemma I.4.7. The two premises are the
lower (FKG) and upper (BK plus connected-component) covariance bounds. -/
theorem cE1_bounds_of_covariance {A S T b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (h_lower : b * A ^ 2 ≤ S) (h_upper : S - b * A ^ 2 ≤ T) :
    0 ≤ cE1 A S T b ∧ cE1 A S T b ≤ T / (b * A ^ 2) := by
  have hden : 0 < b * A ^ 2 := mul_pos hb (sq_pos_of_pos hA)
  have hnum0 : 0 ≤ b * A ^ 2 - S + T := by linarith
  have hnum : b * A ^ 2 - S + T ≤ T := by linarith
  constructor
  · exact div_nonneg hnum0 hden.le
  · exact div_le_div_of_nonneg_right hnum hden.le

end PercLib.CriticalLRP.VolumeMoments

namespace PercLib.CriticalLRP.Hrest

open MeasureTheory

open scoped ENNReal NNReal

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- Expected cluster cardinality is at least one, since the root always
belongs to its own cluster. -/
theorem one_le_lintegral_cardFun {π : Sym2 V → unitInterval} (x : V) :
    1 ≤ ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π) := by
  have hmem (ω : Config V) : (1 : ℝ≥0∞) ≤ Percolation.cardFun (cluster ω x) := by
    rcases (cluster ω x).finite_or_infinite with hfin | hinf
    · rw [Percolation.cardFun_eq_ncard hfin]
      exact_mod_cast (Set.ncard_pos hfin).mpr ⟨x, cluster_mem_self ω x⟩
    · rw [Percolation.cardFun_eq_top hinf]
      exact le_top
  calc
    (1 : ℝ≥0∞) = ∫⁻ _ω, (1 : ℝ≥0∞) ∂(edgeMeasure π) := by simp
    _ ≤ _ := lintegral_mono hmem

/-- The finite-window intersection count is at most the extended cluster
cardinality, hence `|K ∩ B| |K|² ≤ |K|³`. -/
theorem connected_window_mul_sq_le {V : Type*} [Countable V] (x : V) (B : Finset V)
    (ω : Config V) :
    ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)) ≤
      Percolation.cardFun (cluster ω x) ^ 3 := by
  classical
  have hcard : ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) ≤
      Percolation.cardFun (cluster ω x) := by
    rcases (cluster ω x).finite_or_infinite with hfin | hinf
    · rw [Percolation.cardFun_eq_ncard hfin]
      exact_mod_cast Set.ncard_le_ncard
        (show ((B.filter fun y => y ∈ cluster ω x) : Set V) ⊆ cluster ω x from
          fun y hy => (Finset.mem_filter.mp hy).2) hfin
    · rw [Percolation.cardFun_eq_top hinf]
      exact le_top
  calc
    ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)) ≤
        Percolation.cardFun (cluster ω x) *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)) := by
      exact mul_le_mul_of_nonneg_right hcard zero_le
    _ = Percolation.cardFun (cluster ω x) ^ 3 := by ring

/-- Finite-sum interchange for the full joint cluster-volume moment. -/
theorem lintegral_joint_cardFun_sum {π : Sym2 V → unitInterval} (x : V) (B : Finset V) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) *
        ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) =
      ∑ y ∈ B, ∫⁻ ω, Percolation.cardFun (cluster ω x) *
        Percolation.cardFun (cluster ω y) ∂(edgeMeasure π) := by
  have hmeasx : Measurable fun ω : Config V => Percolation.cardFun (cluster ω x) :=
    measurable_cardFun_cluster_canonical x
  simp_rw [Finset.mul_sum]
  exact lintegral_finsetSum B fun y _ =>
    hmeasx.mul (measurable_cardFun_cluster_canonical y)

/-- On each configuration, the connected indicators add up to the cardinality
of the finite window inside the cluster. -/
theorem connected_cardFun_sum_eq (x : V) (B : Finset V) (ω : Config V) :
    (∑ y ∈ B, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))) =
      ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)) := by
  classical
  calc
    (∑ y ∈ B, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))) =
        ∑ y ∈ B, if y ∈ cluster ω x then
          Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : Connects ω x y
      · have hmem : ω ∈ {ω : Config V | Connects ω x y} := h
        rw [Set.indicator_of_mem hmem, one_mul, ite_eq_left (mem_cluster_iff.mpr h)]
      · have hmem : ω ∉ {ω : Config V | Connects ω x y} := h
        rw [Set.indicator_of_notMem hmem, zero_mul,
          ite_eq_right (fun hy => h (mem_cluster_iff.mp hy))]
    _ = ∑ _y ∈ B.filter (fun y => y ∈ cluster ω x),
          Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x) := by
      rw [Finset.sum_ite]
      simp
    _ = _ := by simp

/-- Integral form of the finite-window connected-moment identity. -/
theorem lintegral_connected_cardFun_sum {π : Sym2 V → unitInterval} (x : V) (B : Finset V) :
    (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) =
      ∑ y ∈ B, ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π) := by
  calc
    (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) =
      ∫⁻ ω, ∑ y ∈ B, {ω : Config V | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π) := lintegral_congr fun ω => (connected_cardFun_sum_eq x B ω).symm
    _ = _ := lintegral_finsetSum B fun y _ =>
      (measurable_const.indicator (measurableSet_connects x y)).mul
        ((measurable_cardFun_cluster_canonical x).mul
          (measurable_cardFun_cluster_canonical x))

/-- Sum of per-site joint cluster-volume moments and their connected parts:
the covariance sandwich of Lemma I.4.7 without real subtraction. Here the
first joint expectation contains both connected and disconnected pairs. -/
theorem joint_cardFun_sum_covariance {π : Sym2 V → unitInterval}
    (hπ : ∀ e, π e < 1) (x : V) (B : Finset V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (A : ℝ≥0∞)
    (hA : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) = A)
    (hvol : ∀ y ∈ B,
      (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) = A) :
    (B.card : ℝ≥0∞) * A ^ 2 ≤
        ∑ y ∈ B, ∫⁻ ω, Percolation.cardFun (cluster ω x) *
          Percolation.cardFun (cluster ω y) ∂(edgeMeasure π) ∧
      (∑ y ∈ B, ∫⁻ ω, Percolation.cardFun (cluster ω x) *
          Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) ≤
        (B.card : ℝ≥0∞) * A ^ 2 +
          ∑ y ∈ B, ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
            ∂(edgeMeasure π) := by
  have hmeasx : Measurable fun ω : Config V => Percolation.cardFun (cluster ω x) :=
    measurable_cardFun_cluster_canonical x
  have hfkg (y : V) (hy : y ∈ B) : A ^ 2 ≤
      ∫⁻ ω, Percolation.cardFun (cluster ω x) *
        Percolation.cardFun (cluster ω y) ∂(edgeMeasure π) := by
    have hmeasy : Measurable fun ω : Config V => Percolation.cardFun (cluster ω y) :=
      measurable_cardFun_cluster_canonical y
    calc
      A ^ 2 = (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) *
          (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) := by
        rw [hA, hvol y hy, sq]
      _ ≤ _ := fkg_functional_ennreal Percolation.cardFun_mono
        Percolation.cardFun_mono hmeasx hmeasy
  have hsplit (y : V) :
      (∫⁻ ω, Percolation.cardFun (cluster ω x) *
          Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) =
        (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)) +
        ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π) := by
    have hmeasy : Measurable fun ω : Config V => Percolation.cardFun (cluster ω y) :=
      measurable_cardFun_cluster_canonical y
    calc
      (∫⁻ ω, Percolation.cardFun (cluster ω x) *
          Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) =
          (∫⁻ ω, {ω : Config V | Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
            ∂(edgeMeasure π)) +
          ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
            ∂(edgeMeasure π) := integral_split_conn x y (hmeasx.mul hmeasy)
      _ = _ := by rw [integral_conn_agree x y]
  constructor
  · calc
      (B.card : ℝ≥0∞) * A ^ 2 = ∑ _y ∈ B, A ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun y hy => hfkg y hy
  · calc
      (∑ y ∈ B, ∫⁻ ω, Percolation.cardFun (cluster ω x) *
          Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) =
          ∑ y ∈ B, ((∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
            ∂(edgeMeasure π)) +
          ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
            ∂(edgeMeasure π)) := Finset.sum_congr rfl fun y _ => hsplit y
      _ = (∑ y ∈ B, ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
            ∂(edgeMeasure π)) +
          ∑ y ∈ B, ∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
            ∂(edgeMeasure π) := Finset.sum_add_distrib
      _ ≤ (∑ y ∈ B, ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
            ∂(edgeMeasure π)) + ∑ _y ∈ B, A ^ 2 := by
          apply add_le_add le_rfl
          apply Finset.sum_le_sum
          intro y hy
          calc
            (∫⁻ ω, {ω : Config V | ¬ Connects ω x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
                (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
                ∂(edgeMeasure π)) ≤
                (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) *
                  (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) :=
              hrest_cardFun_bk hπ x y 𝓔 h𝓔mono h𝓔
            _ = A ^ 2 := by rw [hA, hvol y hy, sq]
      _ = (B.card : ℝ≥0∞) * A ^ 2 +
          ∑ y ∈ B, ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
            ∂(edgeMeasure π) := by simp [mul_comm, add_comm]

/-- **Finite-expectation form of Lemma I.4.7**, in the canonical product
model. The unrestricted `ℝ≥0∞` covariance inequality is
`joint_cardFun_sum_covariance`; real-valued `cE1` additionally requires the
finite, positive denominator and finite connected moment used here. -/
theorem lemma_I_4_7_of_finite {π : Sym2 V → unitInterval}
    (hπ : ∀ e, π e < 1) (x : V) (B : Finset V) (hB : B.Nonempty)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (A : ℝ≥0∞)
    (hA : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) = A)
    (hvol : ∀ y ∈ B,
      (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) = A)
    (hAfin : A ≠ ∞)
    (hTfin : (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) := by
  let Ssum : ℝ≥0∞ := ∑ y ∈ B, ∫⁻ ω, Percolation.cardFun (cluster ω x) *
    Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
  let Tsum : ℝ≥0∞ := ∑ y ∈ B, ∫⁻ ω, {ω : Config V | Connects ω x y}.indicator
    (fun _ => (1 : ℝ≥0∞)) ω *
    (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
    ∂(edgeMeasure π)
  let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
    ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
  let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
    (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
    ∂(edgeMeasure π)
  have hS : J = Ssum := lintegral_joint_cardFun_sum x B
  have hT : T = Tsum := lintegral_connected_cardFun_sum x B
  have hc := joint_cardFun_sum_covariance hπ x B 𝓔 h𝓔mono h𝓔 A hA hvol
  change (B.card : ℝ≥0∞) * A ^ 2 ≤ Ssum ∧ Ssum ≤
    (B.card : ℝ≥0∞) * A ^ 2 + Tsum at hc
  have hTsum_fin : Tsum ≠ ∞ := by rw [← hT]; exact hTfin
  have hQfin : (B.card : ℝ≥0∞) * A ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top hAfin)
  have hRhsfin : (B.card : ℝ≥0∞) * A ^ 2 + Tsum ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hQfin, hTsum_fin⟩
  have hSsum_fin : Ssum ≠ ∞ := ne_top_of_le_ne_top hRhsfin hc.2
  have hlow := ENNReal.toReal_mono hSsum_fin hc.1
  have hupp := ENNReal.toReal_mono hRhsfin hc.2
  rw [ENNReal.toReal_add hQfin hTsum_fin] at hupp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hlow hupp
  have hApos : 0 < A.toReal := by
    have hmean : 1 ≤ A := by rw [← hA]; exact one_le_lintegral_cardFun x
    exact ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hmean)) hAfin
  have hb : 0 < (B.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hB)
  apply VolumeMoments.cE1_bounds_of_covariance hApos hb
  · change (B.card : ℝ) * A.toReal ^ 2 ≤ J.toReal
    rw [hS]
    exact hlow
  · change J.toReal - (B.card : ℝ) * A.toReal ^ 2 ≤ T.toReal
    rw [hS, hT]
    linarith

/-- **The `E₁ ≤ 3A³ / |B|` step used after Lemma I.4.7.** The
third-moment bound is the separate tree-graph input; finite connected moments
then follow from `connected_window_mul_sq_le`. -/
theorem cE1_le_three_mul_cube_div_of_finite {π : Sym2 V → unitInterval}
    (hπ : ∀ e, π e < 1) (x : V) (B : Finset V) (hB : B.Nonempty)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n) (A : ℝ≥0∞)
    (hA : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) = A)
    (hvol : ∀ y ∈ B,
      (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) = A)
    (hAfin : A ≠ ∞)
    (hthird : (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 3 ∂(edgeMeasure π)) ≤
      (3 : ℝ≥0∞) * A ^ 5) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        3 * A.toReal ^ 3 / B.card := by
  let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
    ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
  let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
    (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
    ∂(edgeMeasure π)
  have hcube : T ≤ ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 3 ∂(edgeMeasure π) :=
    lintegral_mono fun ω => connected_window_mul_sq_le x B ω
  have h3fin : (3 : ℝ≥0∞) * A ^ 5 ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hAfin)
  have hcubefin : (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 3
      ∂(edgeMeasure π)) ≠ ∞ := ne_top_of_le_ne_top h3fin hthird
  have hTfin : T ≠ ∞ := ne_top_of_le_ne_top hcubefin hcube
  have hbase := lemma_I_4_7_of_finite hπ x B hB 𝓔 h𝓔mono h𝓔 A hA hvol hAfin hTfin
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  have hTreal : T.toReal ≤
      (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 3 ∂(edgeMeasure π)).toReal :=
    ENNReal.toReal_mono hcubefin hcube
  have h3real : (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 3
      ∂(edgeMeasure π)).toReal ≤ 3 * A.toReal ^ 5 := by
    have h := ENNReal.toReal_mono h3fin hthird
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using h
  have hmean : 1 ≤ A := by rw [← hA]; exact one_le_lintegral_cardFun x
  have hApos : 0 < A.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hmean)) hAfin
  have hb : 0 < (B.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hB)
  have hden : 0 < (B.card : ℝ) * A.toReal ^ 2 := mul_pos hb (sq_pos_of_pos hApos)
  calc
    T.toReal / ((B.card : ℝ) * A.toReal ^ 2) ≤
        (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 3 ∂(edgeMeasure π)).toReal /
          ((B.card : ℝ) * A.toReal ^ 2) := div_le_div_of_nonneg_right hTreal hden.le
    _ ≤ (3 * A.toReal ^ 5) / ((B.card : ℝ) * A.toReal ^ 2) :=
      div_le_div_of_nonneg_right h3real hden.le
    _ = 3 * A.toReal ^ 3 / (B.card : ℝ) := by
      field_simp [hApos.ne', hb.ne']

end PercLib.CriticalLRP.Hrest

namespace PercLib.CriticalLRP.Hvol

open MeasureTheory

open scoped ENNReal NNReal

variable {d : ℕ}

attribute [local instance] Classical.propDecidable

/-- **Finite-expectation Lemma I.4.7 on `Z^d`**. Translation invariance of
the edge probabilities proves the equal-site mean-volume hypothesis; it is not
left as an extra assumption. The remaining finite-moment premises are the
ones needed by the real quotient `cE1`. -/
theorem lemma_I_4_7_shift_of_finite {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (hπ : ∀ e, π e < 1) (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (𝓔 : ℕ → Finset (Sym2 (Fin d → ℤ))) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ 𝓔 n)
    (hAfin : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ∞)
    (hTfin : (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) := by
  exact Hrest.lemma_I_4_7_of_finite hπ x B hB 𝓔 h𝓔mono h𝓔
    (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) rfl
    (fun y _ => hvol_cardFun hπshift x y) hAfin hTfin

/-- **Finite-expectation Lemma I.4.7 for the paper's long-range law.** The
canonical edge exhaustion is chosen internally. Positivity of the mean follows
from `one_le_lintegral_cardFun`; no separate positivity premise is required. -/
theorem lemma_I_4_7_latticeLongRange_of_finite (d : ℕ) (α : ℝ) (β : NNReal)
    (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(latticeLongRangeMeasure d α β)) ≠ ∞)
    (hTfin : (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(latticeLongRangeMeasure d α β)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(latticeLongRangeMeasure d α β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(latticeLongRangeMeasure d α β)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(latticeLongRangeMeasure d α β)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) := by
  let := Encodable.ofCountable (Sym2 (Fin d → ℤ))
  simp only [latticeLongRangeMeasure, longRangeMeasure] at *
  exact lemma_I_4_7_shift_of_finite
    (bernoulliEdgeProb_shift (lrKernel_shift_invariant d α) (lrKernel_nonneg d α) β)
    (bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β) x B hB
    (Percolation.edgeExhaustion (E := Sym2 (Fin d → ℤ)))
    Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover hAfin hTfin

end PercLib.CriticalLRP.Hvol

namespace PercLib.CriticalLRP.Hrest

open MeasureTheory

open scoped ENNReal NNReal

variable {V : Type*} [Countable V]

namespace MomentFiniteness

attribute [local instance] Classical.propDecidable

/-- The extended cardinality of a cluster is at least one. -/
theorem one_le_cardFun (x : V) (ω : Config V) :
    (1 : ℝ≥0∞) ≤ Percolation.cardFun (cluster ω x) := by
  rcases (cluster ω x).finite_or_infinite with hfin | hinf
  · rw [Percolation.cardFun_eq_ncard hfin]
    exact_mod_cast (Set.ncard_pos hfin).mpr ⟨x, cluster_mem_self ω x⟩
  · rw [Percolation.cardFun_eq_top hinf]
    exact le_top

/-- A cluster size is dominated by its square. -/
theorem cardFun_le_cardFun_sq (x : V) (ω : Config V) :
    Percolation.cardFun (cluster ω x) ≤
      Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x) := by
  calc Percolation.cardFun (cluster ω x)
      = 1 * Percolation.cardFun (cluster ω x) := (one_mul _).symm
    _ ≤ _ := mul_le_mul (one_le_cardFun x ω) le_rfl (by simp) (by simp)

/-- Finiteness of the first cluster-volume moment follows from the second. -/
theorem ne_top_of_cardFun_sq {π : Sym2 V → unitInterval} (x : V)
    (h2 : (∫⁻ ω, Percolation.cardFun (cluster ω x) *
      Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤ :=
  ne_top_of_le_ne_top h2 (lintegral_mono fun ω => cardFun_le_cardFun_sq x ω)

/-- Finiteness of a connected-window moment follows from the second moment. -/
theorem ne_top_of_aggregated {π : Sym2 V → unitInterval} (x : V) (B : Finset V)
    (h2 : (∫⁻ ω, Percolation.cardFun (cluster ω x) *
      Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤) :
    (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top B.card) h2) ?_
  calc (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π))
      ≤ ∫⁻ ω, (B.card : ℝ≥0∞) * (Percolation.cardFun (cluster ω x) *
          Percolation.cardFun (cluster ω x)) ∂(edgeMeasure π) := by
        refine lintegral_mono fun ω => ?_
        refine mul_le_mul ?_ le_rfl (by simp) (by simp)
        exact_mod_cast Finset.card_filter_le B (fun y => y ∈ cluster ω x)
    _ = (B.card : ℝ≥0∞) * ∫⁻ ω, Percolation.cardFun (cluster ω x) *
          Percolation.cardFun (cluster ω x) ∂(edgeMeasure π) :=
        lintegral_const_mul _ ((Hrest.measurable_cardFun_cluster_canonical x).mul
          (Hrest.measurable_cardFun_cluster_canonical x))

end MomentFiniteness
end PercLib.CriticalLRP.Hrest

namespace PercLib.CriticalLRP.Hvol

open MeasureTheory

open scoped ENNReal NNReal

variable {d : ℕ}

attribute [local instance] Classical.propDecidable

/-- **Lemma I.4.7 for the cutoff law of Definition I.1.5**, with finite
first and connected-window moments. This is the `P_{β,r}` law denoted by
`E_{β,r}` in the source. The uncut-law theorem above is an auxiliary instance. -/
theorem lemma_I_4_7_cutoff_of_finite (K : ℝ → ℝ) (hK : AntitoneOn K (Set.Ioi 0))
    (d : ℕ) (r : ℝ) (hr : 0 < r) (β : NNReal)
    (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞)
    (hTfin : (∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) := by
  let := Encodable.ofCountable (Sym2 (Fin d → ℤ))
  simp only [longRangeMeasure] at *
  exact Hrest.lemma_I_4_7_of_finite
    (π := bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    (bernoulliEdgeProb_lt_one (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    x B hB
    (Percolation.edgeExhaustion (E := Sym2 (Fin d → ℤ)))
    Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover
    (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(edgeMeasure (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β))) rfl
    (fun y _ => Hvol.hvol_cardFun
      (bernoulliEdgeProb_shift (CutoffKernel.cutoffSymKernel_shift K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) x y) hAfin hTfin

/-- **Lemma I.4.7 for the cutoff law with one finite premise.** Finiteness of
the second cluster-volume moment supplies both finiteness premises. -/
theorem lemma_I_4_7_cutoff_of_secondMoment (K : ℝ → ℝ) (hK : AntitoneOn K (Set.Ioi 0))
    (d : ℕ) (r : ℝ) (hr : 0 < r) (β : NNReal)
    (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (h2 : (∫⁻ ω, Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) :=
  lemma_I_4_7_cutoff_of_finite K hK d r hr β x B hB
    (Hrest.MomentFiniteness.ne_top_of_cardFun_sq x h2)
    (Hrest.MomentFiniteness.ne_top_of_aggregated x B h2)

end PercLib.CriticalLRP.Hvol
