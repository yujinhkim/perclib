/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` untruncated per-edge identity: removing the truncation `A`

Swarm `smwvc1d9z`, member `m1`, direction `d5`.

Integration donor: `.ultramath/smwvc1d9z/m1/mirror/Main.lean`, reviewed at `a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f`.

Production lands, for `p = 1`, the *closed-event full-cluster limit*
`SourceModelData.iSup_ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncrFull`
(`Analysis/Cutoff/Fibre/RussoAssembly/Main.lean` §11): the supremum over finite truncations `A` of
the standardized closed-event flux of `|K_0 ∩ A|` is the `cutLaw r`-integral of the *untruncated*
edge increment.  The `p = 2` packet stops at finite truncation `A`
(donor `.ultramath/smwvbcnfb/m1/P2Excluded.lean`, reused here by import).  This file supplies the
missing step at `p = 2`, exactly parallel to §11, in `ℝ≥0∞`:

* `qPairIncrFull`, `qEdgeIncrFull` (`Defs.lean`) — the untruncated quadratic increments;
* `iSup_qPairIncr_eq_qPairIncrFull`, `iSup_qEdgeIncr_eq_qEdgeIncrFull` — the pointwise
  `A ↑ univ` limits;
* `measurable_qPairIncrFull`, `measurable_qEdgeIncrFull`;
* `ofReal_one_sub_mul_pivotalFlux_sq_eq_lintegral_qEdgeIncr` — the truncated closed-event
  factorization in `ℝ≥0∞`;
* `iSup_ofReal_one_sub_mul_pivotalFlux_sq_eq_lintegral_qEdgeIncrFull` — **the main theorem**;
* `one_sub_mul_pivotalFlux_sq_le_lintegral_qEdgeIncrFull` — the honest real-valued consequence
  when the full-cluster flux is finite;
* `qPairIncrFull_eq_top`, `qEdgeIncrFull_eq_top`, `not_exists_real_eq_qEdgeIncrFull` — the `p = 2`
  shadow of the `RussoAssembly/Main` §12 obstruction: there is **no** real-valued untruncated
  per-edge identity, because the far cluster volume may be `⊤`.

## What is *not* claimed

Nothing here differentiates in `r`: `r` is a fixed parameter and no radius limit or radius
continuity is asserted.  No two-sided differentiability at attained radii is claimed.  The
truncation is removed only in `ℝ≥0∞`; the passage back to `ℝ` needs the a.e. finiteness of the far
cluster volume, which is stated as a hypothesis rather than assumed to hold.  No `⊤` is read as `0`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.QuadraticClosed.P2Excluded
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Limit

/-!
# The `p = 2` closed-event full-cluster limit
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. Pointwise inputs at the untruncated quadratic level -/

omit [Countable V] in
/-- A vertex paired with itself contributes nothing at the untruncated quadratic level: the
paper's exclusion indicator `1(b ↮ b)` fails. -/
theorem qPairIncrFull_self (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o x : V) :
    qPairIncrFull d ω o x x = 0 := by
  simp only [qPairIncrFull]
  by_cases h : Connects ω o x <;> simp [h]

omit [Countable V] in
/-- The untruncated quadratic edge increment splits into its two ordered-pair orientations. -/
theorem qEdgeIncrFull_mk (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o x y : V) :
    qEdgeIncrFull d hd ω o s(x, y) = qPairIncrFull d ω o x y + qPairIncrFull d ω o y x := by
  simp only [qEdgeIncrFull, Sym2.lift_mk]
  by_cases h : d x y
  · rw [ite_eq_left h, one_mul]
  · have h1 : ¬ d y x := fun hh => h ((hd y x).mp hh)
    rw [ite_eq_right h, zero_mul, qPairIncrFull, qPairIncrFull]
    simp [h, h1]

omit [Countable V] in
/-- A loop contributes nothing at the untruncated quadratic level. -/
theorem qEdgeIncrFull_loop (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o x : V) :
    qEdgeIncrFull d hd ω o s(x, x) = 0 := by
  rw [qEdgeIncrFull_mk, qPairIncrFull_self, add_zero]

/-! ## 2. Measurability -/

theorem measurable_qPairIncrFull (d : V → V → Prop) [DecidableRel d] (o : V) (b c : V) :
    Measurable fun ω : Config V => qPairIncrFull d ω o b c := by
  have h1 : Measurable fun ω : Config V => (if Connects ω o b then (1 : ℝ≥0∞) else 0) :=
    measurable_connects_ite o b
  have h3 : Measurable fun ω : Config V => (if ¬ Connects ω b c then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (p := fun ω => ¬ Connects ω b c) (measurableSet_connects b c).compl
      measurable_const measurable_const
  have h4 : Measurable fun ω : Config V => clusterVol ω o := measurable_clusterVol o
  have h5 : Measurable fun ω : Config V => clusterVol ω c := measurable_clusterVol c
  have hinner : Measurable fun ω : Config V =>
      2 * clusterVol ω o * clusterVol ω c + clusterVol ω c ^ 2 :=
    ((h4.const_mul 2).mul h5).add (h5.pow_const 2)
  exact ((h1.mul measurable_const).mul h3).mul hinner

theorem measurable_qEdgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) (e : Sym2 V) :
    Measurable fun ω : Config V => qEdgeIncrFull d hd ω o e := by
  induction e using Sym2.ind with
  | h x y =>
    simp only [qEdgeIncrFull, Sym2.lift_mk]
    exact measurable_const.mul
      ((measurable_qPairIncrFull (d := d) o x y).add
        (measurable_qPairIncrFull (d := d) o y x))

/-! ## 3. Monotonicity in the truncation, and the `A ↑ univ` limit -/

/-- The `ℝ≥0∞` truncation of the spatial moment is monotone in the truncating finset. -/
theorem monotone_sMomentTruncENN_finset (q : V → ℝ) (o : V) (ω : Config V) :
    Monotone fun A : Finset V => sMomentTruncENN q o A ω := by
  intro A B hAB
  simp only [sMomentTruncENN]
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun _ _ _ => zero_le

/-- The `ℝ≥0∞` truncations increase to the genuine infinite-volume spatial moment. -/
theorem iSup_sMomentTruncENN_finset (q : V → ℝ) (o : V) (ω : Config V) :
    (⨆ A : Finset V, sMomentTruncENN q o A ω) = spatialMomentENN q o ω := by
  simp only [sMomentTruncENN, spatialMomentENN]
  refine le_antisymm (iSup_le fun A => ENNReal.sum_le_tsum A) ?_
  rw [ENNReal.tsum_eq_iSup_sum]

/-- **With unit weights the truncation limit is the full cluster volume.** -/
theorem iSup_sMomentTruncENN_one_eq_clusterVol (o : V) (ω : Config V) :
    (⨆ A : Finset V, sMomentTruncENN (fun _ => (1 : ℝ)) o A ω) = clusterVol ω o := by
  rw [iSup_sMomentTruncENN_finset]
  rw [spatialMomentENN, ← clusterVolIn_univ (ω := ω) (v := o), clusterVolIn_eq_tsum]
  refine tsum_congr fun x => ?_
  simp only [Set.inter_univ, ENNReal.ofReal_one]

/-- **The supremum of a product of two monotone `ℝ≥0∞` families is the product of suprema.**  The
index set is the directed poset of finite vertex sets, and directedness is what lets the two
suprema be taken at a common index. -/
theorem iSup_mul_iSup_of_monotone {X Y : Finset V → ℝ≥0∞} (hX : Monotone X) (hY : Monotone Y) :
    (⨆ A, X A) * (⨆ A, Y A) = ⨆ A, X A * Y A := by
  refine le_antisymm ?_ (iSup_le fun A => mul_le_mul' (le_iSup X A) (le_iSup Y A))
  rw [ENNReal.iSup_mul]
  refine iSup_le fun A => ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun B =>
    le_iSup_of_le (A ∪ B) (mul_le_mul' (hX Finset.subset_union_left) (hY Finset.subset_union_right))

/-- The `A ↑ univ` limit of the quadratic weight `2|K_0 ∩ A||K_c ∩ A| + |K_c ∩ A|²`. -/
theorem iSup_quad_pair {X Y : Finset V → ℝ≥0∞} (hX : Monotone X) (hY : Monotone Y) :
    (⨆ A : Finset V, 2 * X A * Y A + Y A ^ 2)
      = 2 * (⨆ A, X A) * (⨆ A, Y A) + (⨆ A, Y A) ^ 2 := by
  have h2X : Monotone fun A : Finset V => 2 * X A := fun a b h =>
    mul_le_mul' le_rfl (hX h)
  have hY2 : Monotone fun A : Finset V => Y A ^ 2 := fun a b h => by
    change Y a ^ 2 ≤ Y b ^ 2
    gcongr
    exact hY h
  have hf : Monotone fun A : Finset V => 2 * X A * Y A := fun a b h =>
    mul_le_mul' (mul_le_mul' le_rfl (hX h)) (hY h)
  rw [← iSup_add_iSup_of_monotone hf hY2]
  congr 1
  · rw [← iSup_mul_iSup_of_monotone h2X hY, ← ENNReal.mul_iSup]
  · exact (ENNReal.iSup_pow (fun A => Y A) 2).symm

/-- The truncated quadratic ordered-pair increment is monotone in the truncation. -/
theorem monotone_qPairIncr_trunc (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o b c : V) :
    Monotone fun A : Finset V => qPairIncr d ω o A b c := by
  intro A B hAB
  have hX : sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
      ≤ sMomentTruncENN (fun _ => (1 : ℝ)) o B ω :=
    monotone_sMomentTruncENN_finset (fun _ => (1 : ℝ)) o ω hAB
  have hY : sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
      ≤ sMomentTruncENN (fun _ => (1 : ℝ)) c B ω :=
    monotone_sMomentTruncENN_finset (fun _ => (1 : ℝ)) c ω hAB
  simp only [qPairIncr]
  refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
  · exact mul_le_mul' (mul_le_mul' le_rfl hX) hY
  · rw [pow_two, pow_two]
    exact mul_le_mul' hY hY

/-- **The ordered-pair `A ↑ univ` limit.** -/
theorem iSup_qPairIncr_eq_qPairIncrFull (d : V → V → Prop) [DecidableRel d] (ω : Config V)
    (o b c : V) :
    (⨆ A : Finset V, qPairIncr d ω o A b c) = qPairIncrFull d ω o b c := by
  have hX : Monotone fun A : Finset V => sMomentTruncENN (fun _ => (1 : ℝ)) o A ω :=
    monotone_sMomentTruncENN_finset _ _ _
  have hY : Monotone fun A : Finset V => sMomentTruncENN (fun _ => (1 : ℝ)) c A ω :=
    monotone_sMomentTruncENN_finset _ _ _
  have hO := iSup_sMomentTruncENN_one_eq_clusterVol (V := V) o ω
  have hC := iSup_sMomentTruncENN_one_eq_clusterVol (V := V) c ω
  simp only [qPairIncr, qPairIncrFull]
  rw [← ENNReal.mul_iSup, iSup_quad_pair hX hY, hO, hC]

/-- **The unordered-edge `A ↑ univ` limit.** -/
theorem iSup_qEdgeIncr_eq_qEdgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (e : Sym2 V) :
    (⨆ A : Finset V, qEdgeIncr d hd ω o A e) = qEdgeIncrFull d hd ω o e := by
  induction e using Sym2.ind with
  | h x y =>
    have h : (⨆ A : Finset V, qEdgeIncr d hd ω o A s(x, y))
        = ⨆ A : Finset V, (qPairIncr d ω o A x y + qPairIncr d ω o A y x) :=
      iSup_congr fun A => qEdgeIncr_mk d hd ω o A x y
    rw [h, ← iSup_add_iSup_of_monotone (monotone_qPairIncr_trunc d ω o x y)
        (monotone_qPairIncr_trunc d ω o y x),
      iSup_qPairIncr_eq_qPairIncrFull, iSup_qPairIncr_eq_qPairIncrFull, qEdgeIncrFull_mk]

/-! ## 4. The truncated closed-event identity in `ℝ≥0∞`

The `p = 2` counterpart of the landed `p = 1` `ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncr`.
-/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The closed-event factorization at truncation `A`, in `ℝ≥0∞`, for the square functional.**

`(1 - q_e(r)) · pivotalFlux_r(|K_0 ∩ A|²) e` is the `cutLaw r`-integral of the `ℝ≥0∞` quadratic
edge increment.  The pointwise passage to `ℝ≥0∞` is the landed
`ofReal_sqIncr_closed_eq_qEdgeIncr`; the nonnegativity of the closed-edge quadratic increment is
the binomial expansion `2ab + b² ≥ 0` of nonnegative truncated moments.  Both directions of the
`ℝ ↔ ℝ≥0∞` conversion are guarded: `qEdgeIncr` is bounded by `6|A|²`, so `ofReal` and `toReal` are
mutually inverse here. -/
theorem ofReal_one_sub_mul_pivotalFlux_sq_eq_lintegral_qEdgeIncr (A : Finset M.V) (r : ℝ)
    {x y : M.V} (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    ENNReal.ofReal ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r)
          (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) s(x, y))
      = ∫⁻ ω, qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)
          ∂(M.cutLaw r) := by
  classical
  have hlaw : M.cutLaw r = PercLib.Percolation.Bond.law (M.cutProb r) := M.cutLaw_eq_edgeMeasure r
  have hflip := one_sub_mul_pivotalFlux_sq_eq (V := M.V) (M.cutProb r) (0 : M.V) A s(x, y)
  rw [hlaw]
  rw [hflip]
  rw [← hlaw]
  have hmn : ∀ (v : M.V) (ω : Config M.V),
      (0 : ℝ) ≤ sMomentTrunc (fun _ => (1 : ℝ)) v A ω := fun v ω =>
    sMomentTrunc_nonneg (fun _ => zero_le_one) v A ω
  have hnn : ∀ ω : Config M.V, (0 : ℝ) ≤
      (if s(x, y) ∈ ω then (0 : ℝ) else
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)}) ^ 2
          - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2)) := by
    intro ω
    by_cases h : s(x, y) ∈ ω
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, sMomentTrunc_sq_union_edge_sub (V := M.V) A (0 : M.V) ω hxy]
      have e1 : (0 : ℝ) ≤ 2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
          * sMomentTrunc (fun _ => (1 : ℝ)) y A ω
          + sMomentTrunc (fun _ => (1 : ℝ)) y A ω ^ 2 := by
        nlinarith [hmn (0 : M.V) ω, hmn y ω,
          mul_nonneg (hmn (0 : M.V) ω) (hmn y ω),
          sq_nonneg (sMomentTrunc (fun _ => (1 : ℝ)) y A ω)]
      have e2 : (0 : ℝ) ≤ 2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
          * sMomentTrunc (fun _ => (1 : ℝ)) x A ω
          + sMomentTrunc (fun _ => (1 : ℝ)) x A ω ^ 2 := by
        nlinarith [hmn (0 : M.V) ω, hmn x ω,
          mul_nonneg (hmn (0 : M.V) ω) (hmn x ω),
          sq_nonneg (sMomentTrunc (fun _ => (1 : ℝ)) x A ω)]
      split_ifs
      · linarith
      · linarith
      · linarith
      · norm_num
  have hpoint : ∀ ω : Config M.V,
      (if s(x, y) ∈ ω then (0 : ℝ) else
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)}) ^ 2
          - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2))
      = (qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal := by
    intro ω
    rw [← ofReal_sqIncr_closed_eq_qEdgeIncr (cutDist M r) (cutDist_symm M r) (o := (0 : M.V)) A
      hxy (show cutDist M r x y from hdist)]
    exact (ENNReal.toReal_ofReal (hnn ω)).symm
  have hEq : (∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)}) ^ 2
          - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2)) ∂(M.cutLaw r))
      = (∫⁻ ω, qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)
          ∂(M.cutLaw r)).toReal := by
    rw [show (∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)}) ^ 2
            - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2)) ∂(M.cutLaw r))
        = ∫ ω, (qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal
            ∂(M.cutLaw r) from integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      ((measurable_qEdgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A s(x, y)).ennreal_toReal
        |>.aestronglyMeasurable)]
    exact congrArg ENNReal.toReal (lintegral_congr fun ω =>
      ENNReal.ofReal_toReal
        (qEdgeIncr_ne_top (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)))
  rw [hEq, ENNReal.ofReal_toReal (M.lintegral_qEdgeIncr_ne_top A r s(x, y))]

end SourceModelData

/-! ## 5. Monotonicity of the edge increment, and the right-hand `A ↑ univ` limit -/

/-- The quadratic edge increment is monotone in the truncating vertex set. -/
theorem qEdgeIncr_subset {A B : Finset V} (hAB : A ⊆ B) (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (e : Sym2 V) :
    qEdgeIncr d hd ω o A e ≤ qEdgeIncr d hd ω o B e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [qEdgeIncr_mk, qEdgeIncr_mk]
    exact add_le_add (monotone_qPairIncr_trunc d ω o x y hAB) (monotone_qPairIncr_trunc d ω o y x hAB)

/-- **The right-hand `A ↑ univ` limit.**  The `cutLaw r`-integral of the untruncated quadratic
edge increment is the supremum over finite truncations of the truncated integrals: monotone
convergence for the nonnegative edge series.  No derivative, no moment hypothesis and no
summability enters. -/
theorem lintegral_qEdgeIncrFull_eq_iSup (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (μ : Measure (Config V)) (o : V) (e : Sym2 V) :
    (∫⁻ ω, qEdgeIncrFull d hd ω o e ∂μ) = ⨆ A : Finset V, ∫⁻ ω, qEdgeIncr d hd ω o A e ∂μ := by
  rw [← lintegral_iSup_directed
    (f := fun A : Finset V => fun ω => qEdgeIncr d hd ω o A e)
    (fun A => (measurable_qEdgeIncr d hd o A e).aemeasurable)
    (fun A B => ⟨A ∪ B,
      fun ω => qEdgeIncr_subset Finset.subset_union_left d hd ω o e,
      fun ω => qEdgeIncr_subset Finset.subset_union_right d hd ω o e⟩)]
  exact lintegral_congr fun ω => (iSup_qEdgeIncr_eq_qEdgeIncrFull d hd ω o e).symm

namespace SourceModelData

variable (M : SourceModelData)

/-- **The closed-event full-cluster limit for the square functional.**

Taking `A → ∞` over all finite vertex sets of the closed-event factorization at `p = 2` gives
exactly the `cutLaw r`-integral of the *untruncated* quadratic edge increment.  This is the `p = 2`
counterpart of the `p = 1` `iSup_ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncrFull`, and it
is the step that the finite-truncation `p = 2` packet was missing.

It is stated in `ℝ≥0∞` and needs the distance support `dist x y ≤ r` (outside it the flip increment
is nonzero while `qEdgeIncr` vanishes).  The unboundedness of `|K_0|²` is absorbed by `ℝ≥0∞`, not
by reading `⊤` as `0`: no a.e. finiteness and no moment hypothesis is used. -/
theorem iSup_ofReal_one_sub_mul_pivotalFlux_sq_eq_lintegral_qEdgeIncrFull (r : ℝ) {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    (⨆ A : Finset M.V, ENNReal.ofReal ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r)
          (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) s(x, y)))
      = ∫⁻ ω, qEdgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
          ∂(M.cutLaw r) := by
  have hstep : (⨆ A : Finset M.V, ENNReal.ofReal
        ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
          pivotalFlux (M.cutLaw r)
            (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) s(x, y)))
      = ⨆ A : Finset M.V, ∫⁻ ω,
          qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y) ∂(M.cutLaw r) :=
    iSup_congr fun A => M.ofReal_one_sub_mul_pivotalFlux_sq_eq_lintegral_qEdgeIncr A r hxy hdist
  rw [hstep, ← lintegral_iSup_directed
    (f := fun A : Finset M.V => fun ω =>
      qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y))
    (fun A => (measurable_qEdgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A s(x, y)).aemeasurable)
    (fun A B => ⟨A ∪ B,
      fun ω => qEdgeIncr_subset Finset.subset_union_left (cutDist M r) (cutDist_symm M r) ω
        (0 : M.V) s(x, y),
      fun ω => qEdgeIncr_subset Finset.subset_union_right (cutDist M r) (cutDist_symm M r) ω
        (0 : M.V) s(x, y)⟩)]
  exact lintegral_congr fun ω =>
    iSup_qEdgeIncr_eq_qEdgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)

/-- **The honest conditional per-edge statement at the full cluster volume, `p = 2`.**

For a genuine edge of length `≤ r`, every finite truncation of the closed-event standardized
*quadratic* flux is bounded by the `cutLaw r`-expectation of the untruncated quadratic edge
increment, **provided** that expectation is finite.

The finiteness is a real hypothesis: with `∫⁻ qEdgeIncrFull = ⊤` the right-hand side would be `0`
(`ENNReal.toReal_top`) and the inequality would be false for any nonzero flux.  This is the `p = 2`
analogue of the landed `p = 1` `one_sub_mul_pivotalFlux_le_lintegral_edgeIncrFull`. -/
theorem one_sub_mul_pivotalFlux_sq_le_lintegral_qEdgeIncrFull (r : ℝ) {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r)
    (hfin : ∫⁻ ω, qEdgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
      ∂(M.cutLaw r) ≠ ⊤) (A : Finset M.V) :
    (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r)
          (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) s(x, y)
      ≤ (∫⁻ ω, qEdgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
          ∂(M.cutLaw r)).toReal := by
  have hle : ENNReal.ofReal ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
      pivotalFlux (M.cutLaw r)
        (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) s(x, y))
      ≤ ∫⁻ ω, qEdgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
          ∂(M.cutLaw r) := by
    rw [← M.iSup_ofReal_one_sub_mul_pivotalFlux_sq_eq_lintegral_qEdgeIncrFull r hxy hdist]
    exact le_iSup (fun A : Finset M.V => ENNReal.ofReal
      ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r)
          (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) s(x, y))) A
  rwa [ENNReal.ofReal_le_iff_le_toReal hfin] at hle

end SourceModelData

/-! ## 6. The `p = 2` obstruction: no real-valued full-cluster per-edge identity

`ℝ≥0∞` subtraction is truncated, so the *increment* of a full cluster volume is not a real function
of the configuration: if the far cluster is infinite, `qPairIncrFull` is `⊤`, while any real-valued
candidate `t` satisfies `ENNReal.ofReal t ≠ ⊤`.  Any per-edge `p = 2` identity of the form
`β_c (-K'(r)) · (real full quadratic flip moment) = ∫⁻ qEdgeIncrFull` therefore cannot be proved by
the closed-event factorization alone: it needs the *a.e.* finiteness of the far cluster volume,
a genuine analytic input about the source model.  This is the `p = 2` shadow of the landed `p = 1`
`RussoAssembly/Main` §12 obstructions.
-/

/-- A `⊤`-valued ordered-pair untruncated quadratic increment. -/
theorem qPairIncrFull_eq_top (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o b c : V)
    (hb : Connects ω o b) (hcb : d c b) (hbc : ¬ Connects ω b c)
    (hvol : clusterVol ω c = ⊤) : qPairIncrFull d ω o b c = ⊤ := by
  rw [qPairIncrFull, ite_eq_left hb, ite_eq_left hcb, ite_eq_left hbc, hvol]
  simp

/-- **The `p = 2` obstruction is broader than the `p = 1` one.**  The quadratic weight
`2|K_0||K_c| + |K_c|²` is `⊤` as soon as the *origin* cluster is infinite and the far cluster is
nonempty — so at `p = 2` the a.e. finiteness needed for a real-valued identity must hold for
**both** clusters, not only for the far one as in the linear `p = 1` weight `|K_c|`. -/
theorem qPairIncrFull_eq_top_of_clusterVol_left (d : V → V → Prop) [DecidableRel d]
    (ω : Config V) (o b c : V) (hb : Connects ω o b) (hcb : d c b)
    (hbc : ¬ Connects ω b c) (hvol : clusterVol ω o = ⊤) (hc : clusterVol ω c ≠ 0) :
    qPairIncrFull d ω o b c = ⊤ := by
  rw [qPairIncrFull, ite_eq_left hb, ite_eq_left hcb, ite_eq_left hbc, hvol]
  simp only [one_mul]
  rw [ENNReal.mul_top (by norm_num), ENNReal.top_mul hc, top_add]

/-- A `⊤`-valued unordered-edge untruncated quadratic increment. -/
theorem qEdgeIncrFull_eq_top (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) {x y : V}
    (hb : Connects ω o x) (hyx : d y x) (hnc : ¬ Connects ω x y)
    (hvol : clusterVol ω y = ⊤) : qEdgeIncrFull d hd ω o s(x, y) = ⊤ := by
  rw [qEdgeIncrFull_mk, qPairIncrFull_eq_top d ω o x y hb hyx hnc hvol]
  simp

/-- **The obstruction at `p = 2`.**  At a configuration whose far cluster is infinite (and where
the excluded pattern holds), there is **no** real number `t` whose `ENNReal.ofReal` is the
untruncated quadratic edge increment.  So the full-cluster `p = 2` per-edge identity cannot be
stated in `ℝ` with a `pivotalFlux` of a real-valued full quadratic moment: the closed-event
factorization of `one_sub_mul_pivotalFlux_sq_eq` (a real identity) cannot be pushed to the full
cluster volume without an a.e. finiteness hypothesis. -/
theorem not_exists_real_eq_qEdgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) {x y : V}
    (hb : Connects ω o x) (hyx : d y x) (hnc : ¬ Connects ω x y)
    (hvol : clusterVol ω y = ⊤) :
    ¬ ∃ t : ℝ, ENNReal.ofReal t = qEdgeIncrFull d hd ω o s(x, y) := by
  rintro ⟨t, ht⟩
  rw [qEdgeIncrFull_eq_top d hd ω o hb hyx hnc hvol] at ht
  exact ENNReal.ofReal_ne_top ht

end PercLib.CriticalLRP.Orchestration
