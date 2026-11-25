/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Lemma I.5.8, the two cross-term estimates (`T3`, `T4` of `eq:x12_derivative`),
at the level of the finite weighted model of `I58Remainder`.

Source: `.scratch/i52/source/Zd_renormalizationHD.tex`, proof of
`lem:gyration_derivative2`, lines ~2820-2870 ("Let us now consider the last
three terms, which we expect should approximately cancel to zero ... Putting all
these estimates together yields the claim").

Proved here, with no `sorry` and no new axioms:

* `ex_T3_eq_pairSum`, `ex_T4_eq_pairSum` — step (a) of the paper: the cross-term
  expectations are exactly the pair sums against the disjoint-occurrence weights
  `1(y notin K) 1(x in K) 1(z in K_y)`.
* `pairAll_sum_qx`, `pairAll_sum_qz`, `pairAll_sum_qy` — the identifications the
  paper attributes to mass transport: the *enlarged* weights (`x`,`y`,`z` all in
  `K`) summed against `q(x)`, `q(z-y)`, `q(y)` are exactly
  `E[1(y in K)|K|S(K)]`, `E[1(y in K)|K| sum_{z in K} q(z-y)]` and
  `E[1(y in K)|K|^2 q(y)]`.  In the model these are exact counting identities.
* `T4_bound` — the paper's displayed cross-term estimate **verbatim**:
  `|sum_{y in B} E T4| <= (1/2) G + (1/2) Gq` with `G = E[|K||K cap B|S(K)]` and
  `Gq = E[|K|^2 S(K cap B)]`.
* `T3_bound` — `|sum_{y in B} E T3| <= (3/2) G + Gq` (see the source note below).
* `lemma_I_5_8_assembly_cross` — the final error assembly with these constants,
  giving `|D - M| <= 5 U + 7 G`.

The only probabilistic inputs that remain hypotheses, with provenance:

* `hgap` — the per-pair covariance-gap bound of `lem:disjoint_connections`
  (`0 <= P(0<->x)P(y<->z) - P(0<->x nleftrightarrow y<->z) <= P(0<->x<->y<->z)`).
  In this repository that is `PercLib.CriticalLRP.longRange_twoCluster_gap_le`
  (`Correlation/TwoClusterGap.lean`), whose own named remaining gap is the
  transport of the tree-graph inequality to the canonical countable model.
* `hprod` — the vanishing of the independent-product part of the pair sum
  ("the second equality follows since `sum_{x,z} P(0<->x)P(y<->z)<x,u><z-y,u> = 0`
  by symmetry").  This one is **fully discharged** from symmetry: see §13.
  `parity_zero_of_reflect` proves `sum_x tau0 x <x,u> = 0` from `x |-> -x`
  symmetry of the site set and of the two-point function,
  `parity_zero_of_reflect_about` proves `sum_z tauy z <z-y,u> = 0` from reflection
  about `y`, `prodTerm_vanish` turns the factorisation `pairProd x z =
  tau0 x * tauy z` plus those two into the vanishing, and
  `prodTerm_vanish_of_reflect` / `prodTerm_vanish_qy_of_reflect` chain them.

Mass transport: this is a **global** identity, not a per-site one.  Summing over `y` and
using translation invariance of the measure together with `B = -B`, the second `T3` half
`sum_{y in B} sum_{x,z} P(x,y,z in K) q(z-y)` equals `sum_{y in B} sum_{x,z} P(x,y,z in K) q(x)`,
which is `G = E[|K| |K cap B| S(K)]`.  That layer is proved in §15 (`pairSum_qz_shift`,
`T3_second_half_sum_eq`), with the model symmetries named there.  Consequently the
`1/2 + 1/2` split of `T3` gives `G` (`T3_bound_global`) and the assembly gives `3U + 6G`
(`lemma_I_5_8_assembly_global`), matching the source's `3U + 5G` shape.  The source's
printed `(1/2) G` for `T3` therefore carries an extra factor `1/2` relative to this split;
that factor discrepancy is recorded, not resolved.

§12 records arithmetic showing that the identity is genuinely global: for a *single* site
`y` the two halves differ (`39, 15, 30` against `39, 39, 39` for the deterministic cluster
`{0,2e_1,3e_1}`), and `sum_y B_y != sum_y A_y` when the ambient set is not translation
invariant.  Those examples do **not** refute the paper's mass-transport step, which is the
summed identity under translation invariance.

Scope: everything below is an abstract finite weighted model with the listed model
hypotheses.  Nothing here asserts that translation invariance, `B = -B`, `0 in K` or the
reflection symmetries have been verified in the canonical countable product model.
In particular, the `hTI` formulation used in `T3_bound_global` is *not* the intended
model's two-root mass transport: with a finite ambient set and a rooted cluster it
admits only degenerate instances. `VolumeMoments/I58Nonvacuity.lean` proves this and
provides the usable summed-identity alternative `T3_bound_MTP`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58Remainder

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace PercLib.CriticalLRP.I58

variable {d : ℕ} {Ω : Type*} [Fintype Ω]

/-! ## 1. Counting lemmas for indicator sums over a finite ambient site set -/

/-- Summing `1(x in C) f x` over an ambient finite set `V` containing `C` gives the sum over `C`. -/
lemma sum_indIn_mul_of_subset {V C : Finset (Site d)} (hCV : C ⊆ V) (f : Site d → ℝ) :
    (∑ x ∈ V, (if x ∈ C then (1 : ℝ) else 0) * f x) = ∑ x ∈ C, f x := by
  have h : ∀ x, (if x ∈ C then (1 : ℝ) else 0) * f x = if x ∈ C then f x else 0 := by
    intro x; by_cases hx : x ∈ C <;> simp [hx]
  simp only [h]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hCV]

/-- The same for the constant function `1`: the cardinality of `C`. -/
lemma sum_indIn_of_subset {V C : Finset (Site d)} (hCV : C ⊆ V) :
    (∑ x ∈ V, (if x ∈ C then (1 : ℝ) else 0)) = (C.card : ℝ) := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hCV]
  simp

/-- `sum_{y in B} 1(y in K) f y = sum_{y in K cap B} f y`. -/
lemma sum_indIn_mul_inter (K : Ω → Finset (Site d)) (B : Finset (Site d)) (f : Site d → ℝ)
    (ω : Ω) :
    (∑ y ∈ B, indIn K y ω * f y) = ∑ y ∈ K ω ∩ B, f y := by
  have h : ∀ y, indIn K y ω * f y = if y ∈ K ω then f y else 0 := by
    intro y
    simp only [indIn]
    by_cases hy : y ∈ K ω <;> simp [hy]
  simp only [h]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]

/-! ## 2. Rearranging expectations of finite pair sums -/

/-- `sum_{x,z} E[F x z] a x b z = E[sum_{x,z} F x z a x b z]`. -/
lemma ex_sum_sum_mul {ι κ : Type*} (w : Ω → ℝ) (A : Finset ι) (C : Finset κ)
    (F : ι → κ → Ω → ℝ) (a : ι → ℝ) (b : κ → ℝ) :
    (∑ x ∈ A, ∑ z ∈ C, (ex w (F x z)) * (a x * b z))
      = ex w (fun ω => ∑ x ∈ A, ∑ z ∈ C, F x z ω * (a x * b z)) := by
  have key : ∀ (x : ι) (z : κ), (ex w (F x z)) * (a x * b z)
      = ∑ ω, w ω * (F x z ω * (a x * b z)) := by
    intro x z
    rw [ex, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => key x z))]
  rw [ex]
  have h1 : (∑ x ∈ A, ∑ z ∈ C, ∑ ω, w ω * (F x z ω * (a x * b z)))
      = ∑ x ∈ A, ∑ ω, ∑ z ∈ C, w ω * (F x z ω * (a x * b z)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact Finset.sum_comm (f := fun (z : κ) (ω : Ω) => w ω * (F x z ω * (a x * b z)))
  rw [h1]
  rw [Finset.sum_comm (f := fun (x : ι) (ω : Ω) =>
    ∑ z ∈ C, w ω * (F x z ω * (a x * b z)))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-- The `a = 1` case: `sum_x sum_z E[F x z] b z = E[sum_x sum_z F x z b z]`. -/
lemma ex_sum_sum_mul_one' {ι κ : Type*} (w : Ω → ℝ) (A : Finset ι) (C : Finset κ)
    (F : ι → κ → Ω → ℝ) (b : κ → ℝ) :
    (∑ x ∈ A, ∑ z ∈ C, (ex w (F x z)) * b z)
      = ex w (fun ω => ∑ x ∈ A, ∑ z ∈ C, F x z ω * b z) := by
  simpa using ex_sum_sum_mul (w := w) A C F (fun _ => (1 : ℝ)) b

/-- The `b = 1` case: `sum_x sum_z E[F x z] a x = E[sum_x sum_z F x z a x]`. -/
lemma ex_sum_sum_mul_one {ι κ : Type*} (w : Ω → ℝ) (A : Finset ι) (C : Finset κ)
    (F : ι → κ → Ω → ℝ) (a : ι → ℝ) :
    (∑ x ∈ A, ∑ z ∈ C, (ex w (F x z)) * a x)
      = ex w (fun ω => ∑ x ∈ A, ∑ z ∈ C, F x z ω * a x) := by
  simpa using ex_sum_sum_mul (w := w) A C F a (fun _ => (1 : ℝ))

/-! ## 3. The per-pair weights

For fixed `y`, `pairDisj x y z` is the paper's `Pr(0<->x nleftrightarrow y<->z)` read in the
model, and `pairAll x y z` is the enlarged weight `Pr(x,y,z in K)`.  Both are genuine
expectations in the finite model. -/

/-- `Pr(x, y, z` all in the cluster `K`)`. -/
noncomputable def pairAll (w : Ω → ℝ) (K : Ω → Finset (Site d)) (x y z : Site d) : ℝ :=
  ex w (fun ω => indIn K x ω * indIn K y ω * indIn K z ω)

/-- `Pr(0 <-> x, y notin K, y <-> z)`: the disjoint-occurrence weight of the cross terms. -/
noncomputable def pairDisj (w : Ω → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (x y z : Site d) : ℝ :=
  ex w (fun ω => indOut K y ω * indIn K x ω * indIn (Ky y) z ω)

lemma pairAll_nonneg (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (K : Ω → Finset (Site d))
    (x y z : Site d) : 0 ≤ pairAll w K x y z :=
  ex_nonneg hw fun ω =>
    mul_nonneg (mul_nonneg (indIn_nonneg K x ω) (indIn_nonneg K y ω)) (indIn_nonneg K z ω)

lemma kcard_nonneg (K : Ω → Finset (Site d)) (ω : Ω) : 0 ≤ kcard K ω := by
  simp only [kcard]
  positivity

/-! ## 4. The pair decompositions of `T3` and `T4` -/

/-- Step (a) of the paper for `T3`. -/
theorem ex_T3_eq_pairSum (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (V : Finset (Site d)) (y : Site d)
    (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ ω, Ky y ω ⊆ V) :
    ex w (T3 u K Ky y)
      = ∑ x ∈ V, ∑ z ∈ V, pairDisj w K Ky x y z * (dot u x * dot u (z - y)) := by
  have hpt : T3 u K Ky y
      = fun ω => ∑ x ∈ V, ∑ z ∈ V,
          (indOut K y ω * indIn K x ω * indIn (Ky y) z ω) * (dot u x * dot u (z - y)) := by
    funext ω
    have hx : kDot u K ω = ∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * dot u x :=
      (sum_indIn_mul_of_subset (hK ω) (dot u)).symm
    have hz : (∑ z ∈ Ky y ω, dot u (z - y))
        = ∑ z ∈ V, (if z ∈ Ky y ω then (1 : ℝ) else 0) * dot u (z - y) :=
      (sum_indIn_mul_of_subset (hKy ω) (fun z => dot u (z - y))).symm
    unfold T3
    rw [hx, hz]
    have e2 : indOut K y ω * ((∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * dot u x)
          * (∑ z ∈ V, (if z ∈ Ky y ω then (1 : ℝ) else 0) * dot u (z - y)))
        = ∑ x ∈ V, ∑ z ∈ V,
            (indOut K y ω * indIn K x ω * indIn (Ky y) z ω) * (dot u x * dot u (z - y)) := by
      have e1 : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * dot u x)
          * (∑ z ∈ V, (if z ∈ Ky y ω then (1 : ℝ) else 0) * dot u (z - y))
          = ∑ x ∈ V, ∑ z ∈ V, ((if x ∈ K ω then (1 : ℝ) else 0) * dot u x)
              * ((if z ∈ Ky y ω then (1 : ℝ) else 0) * dot u (z - y)) :=
        Finset.sum_mul_sum V V _ _
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by simp only [indIn]; ring
    rw [← e2]
    ring
  rw [hpt]
  simp only [pairDisj]
  rw [← ex_sum_sum_mul]

/-- Step (a) of the paper for `T4`. -/
theorem ex_T4_eq_pairSum (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (V : Finset (Site d)) (y : Site d)
    (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ ω, Ky y ω ⊆ V) :
    ex w (T4 u K Ky y)
      = ∑ x ∈ V, ∑ z ∈ V, pairDisj w K Ky x y z * (dot u x * dot u y) := by
  have hpt : T4 u K Ky y
      = fun ω => ∑ x ∈ V, ∑ z ∈ V,
          (indOut K y ω * indIn K x ω * indIn (Ky y) z ω) * (dot u x * dot u y) := by
    funext ω
    have hz : kcard (Ky y) ω = ∑ z ∈ V, (if z ∈ Ky y ω then (1 : ℝ) else 0) :=
      (sum_indIn_of_subset (hKy ω)).symm
    have hx : kDot u K ω = ∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * dot u x :=
      (sum_indIn_mul_of_subset (hK ω) (dot u)).symm
    unfold T4
    rw [hz, hx]
    have e2 : indOut K y ω * dot u y
          * ((∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * dot u x)
            * (∑ z ∈ V, (if z ∈ Ky y ω then (1 : ℝ) else 0)))
        = ∑ x ∈ V, ∑ z ∈ V,
            (indOut K y ω * indIn K x ω * indIn (Ky y) z ω) * (dot u x * dot u y) := by
      have e1 : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * dot u x)
          * (∑ z ∈ V, (if z ∈ Ky y ω then (1 : ℝ) else 0))
          = ∑ x ∈ V, ∑ z ∈ V, ((if x ∈ K ω then (1 : ℝ) else 0) * dot u x)
              * (if z ∈ Ky y ω then (1 : ℝ) else 0) :=
        Finset.sum_mul_sum V V _ _
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by simp only [indIn]; ring
    rw [← e2]
    ring
  rw [hpt]
  simp only [pairDisj]
  rw [← ex_sum_sum_mul]

/-! ## 5. The enlarged weights against the nonnegative spatial moments -/

/-- `sum_{x,z} pairAll(x,y,z) q(x) = E[1(y in K)|K|S(K)]`. -/
theorem pairAll_sum_qx (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (V : Finset (Site d)) (y : Site d) (hK : ∀ ω, K ω ⊆ V) :
    (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u x)
      = ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω) := by
  have hp : (fun ω => ∑ x ∈ V, ∑ z ∈ V, (indIn K x ω * indIn K y ω * indIn K z ω) * q u x)
      = (fun ω => indIn K y ω * kcard K ω * kS u K ω) := by
    funext ω
    have hx : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * q u x) = kS u K ω := by
      rw [sum_indIn_mul_of_subset (hK ω) (q u)]; rfl
    have hz : (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0)) = kcard K ω :=
      sum_indIn_of_subset (hK ω)
    have e2 : indIn K y ω * ((∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * q u x)
          * (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0)))
        = ∑ x ∈ V, ∑ z ∈ V, (indIn K x ω * indIn K y ω * indIn K z ω) * q u x := by
      have e1 : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0) * q u x)
          * (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0))
          = ∑ x ∈ V, ∑ z ∈ V, ((if x ∈ K ω then (1 : ℝ) else 0) * q u x)
              * (if z ∈ K ω then (1 : ℝ) else 0) :=
        Finset.sum_mul_sum V V _ _
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by simp only [indIn]; ring
    rw [← e2, hx, hz]
    ring
  simp only [pairAll]
  rw [ex_sum_sum_mul_one, hp]

/-- `sum_{x,z} pairAll(x,y,z) q(z-y) = E[1(y in K)|K| sum_{z in K} q(z-y)]`. -/
theorem pairAll_sum_qz (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (V : Finset (Site d)) (y : Site d) (hK : ∀ ω, K ω ⊆ V) :
    (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y))
      = ex w (fun ω => indIn K y ω * kcard K ω * (∑ z ∈ K ω, q u (z - y))) := by
  have hp : (fun ω => ∑ x ∈ V, ∑ z ∈ V,
        (indIn K x ω * indIn K y ω * indIn K z ω) * q u (z - y))
      = (fun ω => indIn K y ω * kcard K ω * (∑ z ∈ K ω, q u (z - y))) := by
    funext ω
    have hz : (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0) * q u (z - y))
        = ∑ z ∈ K ω, q u (z - y) := sum_indIn_mul_of_subset (hK ω) (fun z => q u (z - y))
    have hx : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0)) = kcard K ω :=
      sum_indIn_of_subset (hK ω)
    have e2 : indIn K y ω * ((∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0))
          * (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0) * q u (z - y)))
        = ∑ x ∈ V, ∑ z ∈ V, (indIn K x ω * indIn K y ω * indIn K z ω) * q u (z - y) := by
      have e1 : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0))
          * (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0) * q u (z - y))
          = ∑ x ∈ V, ∑ z ∈ V, (if x ∈ K ω then (1 : ℝ) else 0)
              * ((if z ∈ K ω then (1 : ℝ) else 0) * q u (z - y)) :=
        Finset.sum_mul_sum V V _ _
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by simp only [indIn]; ring
    rw [← e2, hx, hz]
    ring
  simp only [pairAll]
  rw [ex_sum_sum_mul_one']
  rw [hp]

/-- `sum_{x,z} pairAll(x,y,z) q(y) = E[1(y in K)|K|^2 q(y)]`. -/
theorem pairAll_sum_qy (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (V : Finset (Site d)) (y : Site d) (hK : ∀ ω, K ω ⊆ V) :
    (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u y)
      = ex w (fun ω => indIn K y ω * (kcard K ω) ^ 2 * q u y) := by
  have hp : (fun ω => ∑ x ∈ V, ∑ z ∈ V, (indIn K x ω * indIn K y ω * indIn K z ω) * q u y)
      = (fun ω => indIn K y ω * (kcard K ω) ^ 2 * q u y) := by
    funext ω
    have hx : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0)) = kcard K ω :=
      sum_indIn_of_subset (hK ω)
    have e2 : indIn K y ω * q u y * ((∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0))
          * (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0)))
        = ∑ x ∈ V, ∑ z ∈ V, (indIn K x ω * indIn K y ω * indIn K z ω) * q u y := by
      have e1 : (∑ x ∈ V, (if x ∈ K ω then (1 : ℝ) else 0))
          * (∑ z ∈ V, (if z ∈ K ω then (1 : ℝ) else 0))
          = ∑ x ∈ V, ∑ z ∈ V, (if x ∈ K ω then (1 : ℝ) else 0)
              * (if z ∈ K ω then (1 : ℝ) else 0) :=
        Finset.sum_mul_sum V V _ _
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by simp only [indIn]; ring
    rw [← e2, hx]
    ring
  simp only [pairAll]
  rw [ex_sum_sum_mul_one, hp]

/-! ## 6. Elementary bound on the quadratic weight of a difference -/

/-- `q(z - y) <= 2 q(z) + 2 q(y)`; this is what replaces the paper's invalid
"mass-transport identification" of the second `T3` half. -/
lemma q_sub_le_two (u : Fin d → ℝ) (z y : Site d) :
    q u (z - y) ≤ 2 * q u z + 2 * q u y := by
  have h := abs_mul_le_half (dot u z) (dot u y)
  have h1 : -(dot u z * dot u y) ≤ |dot u z * dot u y| := neg_le_abs _
  rw [q_sub]
  simp only [q]
  nlinarith [h, h1]

/-- Summed form: `sum_{z in K} q(z - y) <= 2 S(K) + 2 |K| q(y)`. -/
lemma sum_q_sub_le (u : Fin d → ℝ) (A : Finset (Site d)) (y : Site d) :
    (∑ z ∈ A, q u (z - y)) ≤ 2 * sMoment u A + 2 * (A.card : ℝ) * q u y := by
  refine (Finset.sum_le_sum fun z _ => q_sub_le_two u z y).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h2 : (∑ z ∈ A, 2 * q u z) = 2 * sMoment u A := by
    rw [← Finset.mul_sum]
    rfl
  rw [h2]
  exact le_of_eq (by ring)

/-! ## 7. Per-site cross-term bounds from the covariance-gap hypothesis -/

/-- **`T4` per site.** With the per-pair covariance-gap bound `hgap` and the vanishing
of the independent-product part `hprod`, the `<y,u>`-weighted cross term satisfies the
paper's `1/2, 1/2` split. -/
theorem T4_per_y (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V : Finset (Site d)) (y : Site d) (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ ω, Ky y ω ⊆ V)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod : (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y)) = 0) :
    |ex w (T4 u K Ky y)|
      ≤ (1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω)
        + (1 / 2) * ex w (fun ω => indIn K y ω * (kcard K ω) ^ 2 * q u y) := by
  rw [ex_T4_eq_pairSum w u K Ky V y hK hKy]
  have hsub : (∑ x ∈ V, ∑ z ∈ V,
        (pairDisj w K Ky x y z - pairProd x z) * (dot u x * dot u y))
      + (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y))
      = ∑ x ∈ V, ∑ z ∈ V, pairDisj w K Ky x y z * (dot u x * dot u y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [← hsub, hprod, add_zero]
  calc |∑ x ∈ V, ∑ z ∈ V, (pairDisj w K Ky x y z - pairProd x z) * (dot u x * dot u y)|
      ≤ ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * |dot u x * dot u y| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun x hx => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun z hz => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hgap x hx z hz) (abs_nonneg _)
    _ ≤ (1 / 2) * (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u x)
        + (1 / 2) * (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u y) := by
        simpa only [q] using
          weighted_pair_abs_le V V (fun x z => pairAll w K x y z)
            (fun x _ z _ => pairAll_nonneg w hw K x y z) (dot u) (fun _ => dot u y)
    _ = _ := by
        rw [pairAll_sum_qx w u K V y hK, pairAll_sum_qy w u K V y hK]

/-- **`T3` per site.** Same inputs; the second half carries the weight
`sum_{z in K} q(z-y)` rather than `q(x)`. -/
theorem T3_per_y (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V : Finset (Site d)) (y : Site d) (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ ω, Ky y ω ⊆ V)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod : (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0) :
    |ex w (T3 u K Ky y)|
      ≤ (1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω)
        + (1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω * (∑ z ∈ K ω, q u (z - y))) := by
  rw [ex_T3_eq_pairSum w u K Ky V y hK hKy]
  have hsub : (∑ x ∈ V, ∑ z ∈ V,
        (pairDisj w K Ky x y z - pairProd x z) * (dot u x * dot u (z - y)))
      + (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y)))
      = ∑ x ∈ V, ∑ z ∈ V, pairDisj w K Ky x y z * (dot u x * dot u (z - y)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [← hsub, hprod, add_zero]
  calc |∑ x ∈ V, ∑ z ∈ V,
        (pairDisj w K Ky x y z - pairProd x z) * (dot u x * dot u (z - y))|
      ≤ ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * |dot u x * dot u (z - y)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun x hx => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun z hz => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hgap x hx z hz) (abs_nonneg _)
    _ ≤ (1 / 2) * (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u x)
        + (1 / 2) * (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y)) := by
        simpa only [q] using
          weighted_pair_abs_le V V (fun x z => pairAll w K x y z)
            (fun x _ z _ => pairAll_nonneg w hw K x y z) (dot u) (fun z => dot u (z - y))
    _ = _ := by
        rw [pairAll_sum_qx w u K V y hK, pairAll_sum_qz w u K V y hK]

/-! ## 8. The product part of the pair sum vanishes by reflection symmetry -/

/-- The paper's "the second equality follows since `sum_{x,z} P(0<->x)P(y<->z)
<x,u><z-y,u> = 0` by symmetry": if the product weight factorises and each factor
satisfies its one-point parity identity (reflection `w |-> -w`), the whole product
term vanishes. -/
theorem prodTerm_vanish (u : Fin d → ℝ) (V : Finset (Site d)) (y : Site d)
    (pairProd : Site d → Site d → ℝ) (tau0 tauy : Site d → ℝ)
    (hfac : ∀ x z : Site d, pairProd x z = tau0 x * tauy z)
    (h0 : (∑ x ∈ V, tau0 x * dot u x) = 0)
    (hy : (∑ z ∈ V, tauy z * dot u (z - y)) = 0) :
    (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0 := by
  have hsum : (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y)))
      = (∑ x ∈ V, tau0 x * dot u x) * (∑ z ∈ V, tauy z * dot u (z - y)) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by
      rw [hfac]; ring
  rw [hsum, h0, zero_mul]

/-- The `<y,u>`-weighted product part vanishes in the same way. -/
theorem prodTerm_vanish_qy (u : Fin d → ℝ) (V : Finset (Site d)) (y : Site d)
    (pairProd : Site d → Site d → ℝ) (tau0 tauy : Site d → ℝ)
    (hfac : ∀ x z : Site d, pairProd x z = tau0 x * tauy z)
    (h0 : (∑ x ∈ V, tau0 x * dot u x) = 0) :
    (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y)) = 0 := by
  have hsum : (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y))
      = (∑ x ∈ V, tau0 x * dot u x) * (dot u y * (∑ z ∈ V, tauy z)) := by
    have h1 : (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y))
        = ∑ x ∈ V, (tau0 x * dot u x) * (dot u y * (∑ z ∈ V, tauy z)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      have hz : (∑ z ∈ V, pairProd x z * (dot u x * dot u y))
          = ∑ z ∈ V, (tau0 x * dot u x) * (dot u y * tauy z) :=
        Finset.sum_congr rfl fun z _ => by rw [hfac]; ring
      rw [hz, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h1, Finset.sum_mul]
  rw [hsum, h0, zero_mul]

/-! ## 9. Summing over the ball -/

/-- `sum_{y in B} E[1(y in K)|K|S(K)] = E[|K||K cap B|S(K)]`. -/
theorem ex_sum_indIn_kS (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (B : Finset (Site d)) :
    (∑ y ∈ B, ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω))
      = ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  rw [← ex_sum]
  have hp : (fun ω => ∑ y ∈ B, indIn K y ω * kcard K ω * kS u K ω)
      = (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
    funext ω
    have h : (∑ y ∈ B, indIn K y ω) = kap K B ω := by
      have := congr_fun (sum_indIn K B) ω
      simpa only [Finset.sum_apply] using this
    rw [← Finset.sum_mul, ← Finset.sum_mul, h]
    ring
  rw [hp]

/-- `sum_{y in B} E[1(y in K)|K|^2 q(y)] = E[|K|^2 S(K cap B)]`. -/
theorem ex_sum_indIn_q (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (B : Finset (Site d)) :
    (∑ y ∈ B, ex w (fun ω => indIn K y ω * (kcard K ω) ^ 2 * q u y))
      = ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)) := by
  rw [← ex_sum]
  have hp : (fun ω => ∑ y ∈ B, indIn K y ω * (kcard K ω) ^ 2 * q u y)
      = (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)) := by
    funext ω
    have h1 : (∑ y ∈ B, indIn K y ω * (kcard K ω) ^ 2 * q u y)
        = (kcard K ω) ^ 2 * (∑ y ∈ B, indIn K y ω * q u y) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [h1, sum_indIn_mul_inter]
    rfl
  rw [hp]

/-- Pointwise bound behind the `T3` estimate: the `sum_{z in K} q(z-y)` weight is at most
`2 S(K) + 2 |K| q(y)`, which is what produces `(3/2) G + Gq` instead of `(1/2) G`. -/
theorem ex_sum_indIn_qz_le (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (B : Finset (Site d)) :
    (∑ y ∈ B, ex w (fun ω => indIn K y ω * kcard K ω * (∑ z ∈ K ω, q u (z - y))))
      ≤ 2 * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)
        + 2 * ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)) := by
  rw [← ex_sum]
  rw [← ex_const_mul, ← ex_const_mul, ← ex_add]
  refine (ex_mono hw fun ω => ?_)
  have hkap : (∑ y ∈ B, indIn K y ω) = kap K B ω := by
    have := congr_fun (sum_indIn K B) ω
    simpa only [Finset.sum_apply] using this
  have hstep : (∑ y ∈ B, indIn K y ω * kcard K ω * (∑ z ∈ K ω, q u (z - y)))
      ≤ ∑ y ∈ B, indIn K y ω * kcard K ω
          * (2 * sMoment u (K ω) + 2 * (kcard K ω) * q u y) := by
    refine Finset.sum_le_sum fun y _ => ?_
    have h1 := sum_q_sub_le u (K ω) y
    have h2 := mul_le_mul_of_nonneg_left h1
      (mul_nonneg (indIn_nonneg K y ω) (kcard_nonneg K ω))
    calc indIn K y ω * kcard K ω * (∑ z ∈ K ω, q u (z - y))
        ≤ indIn K y ω * kcard K ω
            * (2 * sMoment u (K ω) + 2 * (kcard K ω) * q u y) := h2
      _ = _ := rfl
  refine hstep.trans ?_
  have hsplit : (∑ y ∈ B, indIn K y ω * kcard K ω
        * (2 * sMoment u (K ω) + 2 * (kcard K ω) * q u y))
      = (∑ y ∈ B, indIn K y ω * kcard K ω * (2 * sMoment u (K ω)))
        + (∑ y ∈ B, indIn K y ω * kcard K ω * (2 * (kcard K ω) * q u y)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsplit]
  have ha : (∑ y ∈ B, indIn K y ω * kcard K ω * (2 * sMoment u (K ω)))
      = 2 * (kcard K ω * kap K B ω * sMoment u (K ω)) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hkap]
    ring
  have hb : (∑ y ∈ B, indIn K y ω * kcard K ω * (2 * (kcard K ω) * q u y))
      = 2 * ((kcard K ω) ^ 2 * sMoment u (K ω ∩ B)) := by
    have hpt : ∀ y, indIn K y ω * kcard K ω * (2 * (kcard K ω) * q u y)
        = (2 * (kcard K ω) ^ 2) * (indIn K y ω * q u y) := by
      intro y; ring
    simp only [hpt]
    rw [← Finset.mul_sum, sum_indIn_mul_inter]
    simp only [sMoment, mul_assoc]
  rw [ha, hb]
  simp only [kS]
  exact le_of_eq rfl

/-! ## 10. The summed cross-term estimates -/

/-- **The paper's displayed `T4` estimate, verbatim.** -/
theorem T4_bound (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) (hK : ∀ ω, K ω ⊆ V)
    (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod : ∀ y ∈ B, (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y)) = 0) :
    |∑ y ∈ B, ex w (T4 u K Ky y)|
      ≤ (1 / 2) * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)
        + (1 / 2) * ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : (∑ y ∈ B, |ex w (T4 u K Ky y)|)
      ≤ ∑ y ∈ B, ((1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω)
          + (1 / 2) * ex w (fun ω => indIn K y ω * (kcard K ω) ^ 2 * q u y)) :=
    Finset.sum_le_sum fun y hy =>
      T4_per_y w hw u K Ky V y hK (hKy y hy) pairProd (hgap y hy) (hprod y hy)
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ex_sum_indIn_kS,
    ex_sum_indIn_q]

/-- **The `T3` estimate.** The paper displays `(1/2) G`; the correct second half is the
`sum_{z in K} q(z-y)` weight, which is bounded here by `2 G + 2 Gq`, giving `(3/2) G + Gq`. -/
theorem T3_bound (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) (hK : ∀ ω, K ω ⊆ V)
    (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod : ∀ y ∈ B, (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0) :
    |∑ y ∈ B, ex w (T3 u K Ky y)|
      ≤ (3 / 2) * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)
        + ex w (fun ω => (kcard K ω) ^ 2 * sMoment u (K ω ∩ B)) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : (∑ y ∈ B, |ex w (T3 u K Ky y)|)
      ≤ ∑ y ∈ B, ((1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω)
          + (1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω
              * (∑ z ∈ K ω, q u (z - y)))) :=
    Finset.sum_le_sum fun y hy =>
      T3_per_y w hw u K Ky V y hK (hKy y hy) pairProd (hgap y hy) (hprod y hy)
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ex_sum_indIn_kS]
  have h2 := ex_sum_indIn_qz_le w hw u K B
  linarith

/-! ## 11. The final error assembly with the proved cross-term bounds -/

/-- Numerical bookkeeping: `T0` error `U`, `T2` error `G`, `T3` error `(3/2)G + Gq`,
`T4` error `(1/2)G + (1/2)Gq`, and `Gq <= U`, give `3U + 5G` replaced by `5U + 7G`. -/
theorem abs_assembly_cross (a b c e U0 G Gq : ℝ)
    (h1 : |a| ≤ U0) (h2 : |b| ≤ G) (h3 : |c| ≤ (3 / 2) * G + Gq)
    (h4 : |e| ≤ (1 / 2) * G + (1 / 2) * Gq) (h5 : Gq ≤ U0) :
    |a + 2 * b - 2 * c - 4 * e| ≤ 5 * U0 + 7 * G := by
  have ha := abs_le.mp h1
  have hb := abs_le.mp h2
  have hc := abs_le.mp h3
  have he := abs_le.mp h4
  rw [abs_le]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, he.1, he.2]

/-- **Lemma I.5.8 with the two cross-term estimates proved.**

`derivTerm` is the four-term right-hand side of `eq:x12_derivative` of the source and
`mainTerm` its two factored main terms.  Compared with `lemma_I_5_8_assembly`, the two
hypotheses `hR3` and `hR4` are **removed**: they are replaced by

* the per-pair covariance-gap bound `hgap` (the paper's `lem:disjoint_connections`,
  available in this repository as `PercLib.CriticalLRP.longRange_twoCluster_gap_le`);
* the vanishing of the independent-product part `hprod3`, `hprod4`
  (the paper's "= 0 by symmetry", derived from reflection symmetry in
  `prodTerm_vanish`, `prodTerm_vanish_qy`);
* twice membership of the cluster in a finite ambient set `V`, needed only to make the
  finite pair sums over `x,z` well defined.

The two remaining displayed hypotheses are `hR0` (the first remainder, direction (E))
and `hR2` (the second remainder).  The constants are `5U + 7G` in place of the paper's
`3U + 5G`: the loss is entirely in `T3`, whose second AM-GM half is
`(1/2) sum_y E[1(y in K)|K| sum_{z in K} q(z-y)]` rather than `(1/2) G`. -/
theorem lemma_I_5_8_assembly_cross
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) {r : ℝ}
    (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod3 : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0)
    (hprod4 : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y)) = 0)
    (hR0 : |(∑ y ∈ B, ex w (T0 u K Ky y)) -
        (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (hR2 : |(∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)) :
    |derivTerm w u K Ky B - mainTerm w u K B|
      ≤ 5 * (uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 7 * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  rw [derivTerm_sub_mainTerm]
  exact abs_assembly_cross _ _ _ _ _ _ _
    hR0 hR2
    (T3_bound w hw u K Ky V B hK hKy pairProd hgap hprod3)
    (T4_bound w hw u K Ky V B hK hKy pairProd hgap hprod4)
    (Gq_le_U u K B hw hB)


/-! ## 12. Machine-checked arithmetic: the identity is global, not per-site

The paper's second `T3` half at a **single** site `y`, on a deterministic cluster `K`, is
`|K| * sum_{z in K} q(z - y)`, while the corresponding first half is `|K| * S(K)`.  These
differ pointwise (and the two summed halves differ when the ambient set is not translation
invariant), which is exactly why the mass-transport step needs the translation layer of
§15.  It is **not** a counterexample to the paper, whose identity is the summed one.

In dimension `1` with `u = e_1` the dictionary is `Site 1 = Fin 1 -> Z`, `x = x_0 e_1`,
`q u (x e_1) = x_0^2`, so both sides become `Z`-sums:

* `K = {0, 2, 3}`, `B = {0, 1, 2, 3}`: second half `= 84`, first half (`G`) `= 117`.
* `K = {0, 1, 100}`, `B = K`: second half `= 118812 > 90009 = G`.
-/

/-- Second `T3` half for the deterministic cluster `{0,2,3} ⊆ Z`: `84`. -/
theorem second_half_demo_023 :
    (∑ y ∈ ({0, 2, 3} : Finset ℤ),
        (∑ z ∈ ({0, 2, 3} : Finset ℤ), (((z - y : ℤ)) : ℝ) ^ 2)) * 3 = 84 := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- The corresponding `G` for `K = {0,2,3} ⊆ B = {0,1,2,3}`: `117`. -/
theorem G_demo_023 :
    3 * 3 * (∑ z ∈ ({0, 2, 3} : Finset ℤ), ((z : ℤ) : ℝ) ^ 2) = 117 := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- Second `T3` half for the deterministic cluster `{0,1,100} ⊆ Z`: `118812`. -/
theorem second_half_demo_01100 :
    (∑ y ∈ ({0, 1, 100} : Finset ℤ),
        (∑ z ∈ ({0, 1, 100} : Finset ℤ), (((z - y : ℤ)) : ℝ) ^ 2)) * 3 = 118812 := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- The corresponding `G` for `K = {0,1,100} ⊆ B = K`: `90009`, strictly smaller. -/
theorem G_demo_01100 :
    3 * (3 * (∑ z ∈ ({0, 1, 100} : Finset ℤ), ((z : ℤ) : ℝ) ^ 2)) = 90009 := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]


/-! ## 13. Discharging the parity identities from reflection symmetry

`prodTerm_vanish` and `prodTerm_vanish_qy` reduce the paper's "`= 0` by symmetry" to the
two one-point parity identities `sum_x tau0 x <x,u> = 0` and
`sum_z tauy z <z-y,u> = 0`.  Those are *proved* here from the two reflection symmetries
of the model: of the site set (a symmetric box) and of the two-point function. -/

/-- **Reflection about the origin.** On a site set closed under `x |-> -x`, the sum of
`f x * <x,u>` vanishes for any `f` invariant under `x |-> -x` (in particular for the
two-point function `f x = P(0<->x)`, which is reflection symmetric). -/
theorem parity_zero_of_reflect (u : Fin d → ℝ) (f : Site d → ℝ) {V : Finset (Site d)}
    (hV : ∀ x, x ∈ V ↔ -x ∈ V) (hf : ∀ x, f (-x) = f x) :
    (∑ x ∈ V, f x * dot u x) = 0 := by
  have hbij : (∑ x ∈ V, f x * dot u x) = ∑ x ∈ V, -(f x * dot u x) := by
    refine Finset.sum_bij (fun x (_ : x ∈ V) => -x) ?_ ?_ ?_ ?_
    · intro a ha
      exact (hV a).mp ha
    · intro a1 _ a2 _ h
      simpa using congrArg (fun w : Site d => -w) h
    · intro b hb
      exact ⟨-b, (hV b).mp hb, by simp⟩
    · intro a ha
      show f a * dot u a = -(f (-a) * dot u (-a))
      rw [hf a, dot_neg]
      ring
  rw [Finset.sum_neg_distrib] at hbij
  linarith

/-- **Reflection about `y`.** On a site set closed under `z |-> y + y - z`, the sum of
`f z * <z - y,u>` vanishes for any `f` invariant under that reflection (in particular
for `f z = P(y <-> z)`, which equals `P(0 <-> z - y)` and is reflection symmetric about
`y`). -/
theorem parity_zero_of_reflect_about (u : Fin d → ℝ) (y : Site d) (f : Site d → ℝ)
    {V : Finset (Site d)} (hV : ∀ z, z ∈ V ↔ (y + y - z) ∈ V)
    (hf : ∀ z, f (y + y - z) = f z) :
    (∑ z ∈ V, f z * dot u (z - y)) = 0 := by
  have hbij : (∑ z ∈ V, f z * dot u (z - y))
      = ∑ z ∈ V, -(f z * dot u (z - y)) := by
    refine Finset.sum_bij (fun z (_ : z ∈ V) => y + y - z) ?_ ?_ ?_ ?_
    · intro a ha
      exact (hV a).mp ha
    · intro a1 _ a2 _ h
      have key : ∀ a : Site d, y + y - (y + y - a) = a := fun a => by abel
      simpa only [key] using congrArg (fun w : Site d => y + y - w) h
    · intro b hb
      exact ⟨y + y - b, (hV b).mp hb, by abel⟩
    · intro a ha
      show f a * dot u (a - y) = -(f (y + y - a) * dot u (y + y - a - y))
      rw [hf a]
      have hsub : y + y - a - y = -(a - y) := by abel
      rw [hsub, dot_neg]
      ring
  rw [Finset.sum_neg_distrib] at hbij
  linarith

/-- **The product part vanishes, from reflection symmetry alone.** -/
theorem prodTerm_vanish_of_reflect (u : Fin d → ℝ) (V : Finset (Site d)) (y : Site d)
    (pairProd : Site d → Site d → ℝ) (tau0 tauy : Site d → ℝ)
    (hfac : ∀ x z : Site d, pairProd x z = tau0 x * tauy z)
    (hV : ∀ x, x ∈ V ↔ -x ∈ V) (hV' : ∀ z, z ∈ V ↔ (y + y - z) ∈ V)
    (h0 : ∀ x, tau0 (-x) = tau0 x) (hy : ∀ z, tauy (y + y - z) = tauy z) :
    (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0 :=
  prodTerm_vanish u V y pairProd tau0 tauy hfac
    (parity_zero_of_reflect u tau0 hV h0) (parity_zero_of_reflect_about u y tauy hV' hy)

/-- **The `<y,u>`-weighted product part vanishes, from reflection symmetry alone.** -/
theorem prodTerm_vanish_qy_of_reflect (u : Fin d → ℝ) (V : Finset (Site d)) (y : Site d)
    (pairProd : Site d → Site d → ℝ) (tau0 tauy : Site d → ℝ)
    (hfac : ∀ x z : Site d, pairProd x z = tau0 x * tauy z)
    (hV : ∀ x, x ∈ V ↔ -x ∈ V) (h0 : ∀ x, tau0 (-x) = tau0 x) :
    (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y)) = 0 :=
  prodTerm_vanish_qy u V y pairProd tau0 tauy hfac
    (parity_zero_of_reflect u tau0 hV h0)


/-! ## 14. Capstone: the assembly with the product part discharged

Only `hgap` (the paper's `lem:disjoint_connections`), the two remaining displayed
estimates `hR0`, `hR2`, and the reflection symmetries of the two-point function are
inputs.  `hR3` and `hR4` are theorems. -/

theorem lemma_I_5_8_assembly_cross_of_reflect
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) {r : ℝ}
    (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2)
    (pairProd : Site d → Site d → ℝ) (tau0 tauy : Site d → ℝ)
    (hfac : ∀ x z : Site d, pairProd x z = tau0 x * tauy z)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hV : ∀ x, x ∈ V ↔ -x ∈ V)
    (hV' : ∀ y ∈ B, ∀ z : Site d, z ∈ V ↔ (y + y - z) ∈ V)
    (h0 : ∀ x, tau0 (-x) = tau0 x)
    (h1 : ∀ y ∈ B, ∀ z, tauy (y + y - z) = tauy z)
    (hR0 : |(∑ y ∈ B, ex w (T0 u K Ky y)) -
        (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (hR2 : |(∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)) :
    |derivTerm w u K Ky B - mainTerm w u K B|
      ≤ 5 * (uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 7 * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) :=
  lemma_I_5_8_assembly_cross w hw u K Ky V B hK hKy hB pairProd hgap
    (fun y hy => prodTerm_vanish_of_reflect u V y pairProd tau0 tauy hfac hV
      (hV' y hy) h0 (h1 y hy))
    (fun y _ => prodTerm_vanish_qy_of_reflect u V y pairProd tau0 tauy hfac hV h0)
    hR0 hR2

/-! `P(r, x, y, z` all in the cluster `K`)`, with the root site `r` explicit. -/
noncomputable def pairAt (w : Ω → ℝ) (K : Ω → Finset (Site d)) (r x y z : Site d) : ℝ :=
  ex w (fun ω => indIn K r ω * indIn K x ω * indIn K y ω * indIn K z ω)

lemma pairAt_swap24 (w : Ω → ℝ) (K : Ω → Finset (Site d)) (r b a : Site d) :
    pairAt w K r b 0 a = pairAt w K r a 0 b := by
  simp only [pairAt]
  congr 1
  funext ω
  ring

lemma pairAll_eq_pairAt (w : Ω → ℝ) (K : Ω → Finset (Site d))
    (h0K : ∀ ω, (0 : Site d) ∈ K ω) (x y z : Site d) :
    pairAll w K x y z = pairAt w K 0 x y z := by
  simp only [pairAll, pairAt]
  congr 1
  funext ω
  simp only [indIn]
  rw [ite_eq_left (h0K ω)]
  ring

lemma pairAt_eq_pairAll (w : Ω → ℝ) (K : Ω → Finset (Site d))
    (h0K : ∀ ω, (0 : Site d) ∈ K ω) (r x z : Site d) :
    pairAt w K r x 0 z = pairAll w K x r z := by
  simp only [pairAll, pairAt]
  congr 1
  funext ω
  simp only [indIn]
  rw [ite_eq_left (h0K ω)]
  ring

lemma sum_shift_bij (V : Finset (Site d)) (t : Site d)
    (hV : ∀ x : Site d, (x ∈ V ↔ x + t ∈ V)) (f g : Site d → ℝ)
    (hg : ∀ x, g (x + t) = f x) :
    (∑ x ∈ V, f x) = ∑ a ∈ V, g a := by
  refine Finset.sum_bij (fun x (_ : x ∈ V) => x + t) ?_ ?_ ?_ ?_
  · intro a ha
    exact (hV a).mp ha
  · intro a1 _ a2 _ h
    simpa using h
  · intro b hb
    refine ⟨b + -t, ?_, by abel⟩
    rw [hV (b + -t)]
    have h1 : b + -t + t = b := by abel
    rw [h1]
    exact hb
  · intro a ha
    exact (hg a).symm

lemma sum_neg_eq (B : Finset (Site d)) (hB : ∀ y : Site d, (y ∈ B ↔ -y ∈ B))
    (f : Site d → ℝ) : (∑ y ∈ B, f (-y)) = ∑ y ∈ B, f y := by
  refine Finset.sum_bij (fun y (_ : y ∈ B) => -y) ?_ ?_ ?_ ?_
  · intro a ha
    exact (hB a).mp ha
  · intro a1 _ a2 _ h
    simpa using h
  · intro b hb
    exact ⟨-b, (hB b).mp hb, by simp⟩
  · intro a ha
    simp

/-- **Conditional global identity, with a deliberately restricted hypothesis.**

For a single site `y`, the second `T3` half at `y` equals the first at `-y`.

**Usability warning.** The root-blind `pairAt` invariance `hTI` below is *not*
translation invariance of the intended percolation model. Together with finite
`K ⊆ V` and `0 ∈ K`, it forces every positive-weight configuration to have empty
`K`; finite translation invariance `hVy` is also impossible at nonzero shifts.
This theorem is therefore a conditional algebraic reduction, not an instantiated
mass-transport proof. `VolumeMoments/I58Nonvacuity.lean` proves that vacuity and
supplies the satisfiable `T3_bound_MTP` interface using only the summed two-root
identity actually needed downstream. Do not use `hTI` as a model hypothesis.

`sum_{x,z} P(x,y,z in K) q(z-y) = E[1(-y in K) |K| S(K)]`.

The hypotheses are translation invariance of the **measure** (`hTI`) and of the finite
ambient set (`hVy`), plus `0 in K` and `K subset V`. -/
theorem pairSum_qz_shift (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (V : Finset (Site d)) (y : Site d)
    (h0K : ∀ ω, (0 : Site d) ∈ K ω) (hKV : ∀ ω, K ω ⊆ V)
    (hVy : ∀ x : Site d, (x ∈ V ↔ x - y ∈ V))
    (hTI : ∀ (p q r s t : Site d),
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t)) :
    (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y))
      = ex w (fun ω => indIn K (-y) ω * kcard K ω * kS u K ω) := by
  have h1 : (∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y))
      = ∑ x ∈ V, ∑ z ∈ V, pairAt w K 0 x y z * q u (z - y) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
    rw [pairAll_eq_pairAt w K h0K]
  rw [h1]
  have h2 : (∑ x ∈ V, ∑ z ∈ V, pairAt w K 0 x y z * q u (z - y))
      = ∑ x ∈ V, ∑ a ∈ V, pairAt w K 0 x y (a + y) * q u a := by
    refine Finset.sum_congr rfl fun x _ => ?_
    refine sum_shift_bij V (-y) ?_ (fun z => pairAt w K 0 x y z * q u (z - y))
      (fun a => pairAt w K 0 x y (a + y) * q u a) ?_
    · intro z
      simpa only [sub_eq_add_neg] using hVy z
    · intro a
      have h1 : a + -y + y = a := by abel
      have h2 : a + -y = a - y := by abel
      rw [h1, h2]
  rw [h2]
  have h3 : (∑ x ∈ V, ∑ a ∈ V, pairAt w K 0 x y (a + y) * q u a)
      = ∑ b ∈ V, ∑ a ∈ V, pairAt w K 0 (b + y) y (a + y) * q u a := by
    refine sum_shift_bij V (-y) ?_ (fun x => ∑ a ∈ V, pairAt w K 0 x y (a + y) * q u a)
      (fun b => ∑ a ∈ V, pairAt w K 0 (b + y) y (a + y) * q u a) ?_
    · intro z
      simpa only [sub_eq_add_neg] using hVy z
    · intro b
      have h1 : b + -y + y = b := by abel
      rw [h1]
  rw [h3]
  have h4 : (∑ b ∈ V, ∑ a ∈ V, pairAt w K 0 (b + y) y (a + y) * q u a)
      = ∑ b ∈ V, ∑ a ∈ V, pairAt w K (-y) b 0 a * q u a := by
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    have h := hTI (-y) b 0 a y
    simp only [neg_add_cancel, zero_add] at h
    rw [← h]
  rw [h4]
  have h5 : (∑ b ∈ V, ∑ a ∈ V, pairAt w K (-y) b 0 a * q u a)
      = ∑ a ∈ V, ∑ b ∈ V, pairAt w K (-y) a 0 b * q u a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      congrArg (fun t => t * q u a) (pairAt_swap24 w K (-y) b a)
  rw [h5]
  have h6 : (∑ a ∈ V, ∑ b ∈ V, pairAt w K (-y) a 0 b * q u a)
      = ∑ a ∈ V, ∑ b ∈ V, pairAll w K a (-y) b * q u a := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pairAt_eq_pairAll w K h0K]
  rw [h6, pairAll_sum_qx w u K V (-y) hKV]

/-- Summed form: `sum_{y in B}` of the second `T3` half equals `G`, provided `B = -B`. -/
theorem T3_second_half_sum_eq (w : Ω → ℝ) (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (V B : Finset (Site d))
    (h0K : ∀ ω, (0 : Site d) ∈ K ω) (hKV : ∀ ω, K ω ⊆ V)
    (hVy : ∀ y ∈ B, ∀ x : Site d, (x ∈ V ↔ x - y ∈ V))
    (hTI : ∀ (p q r s t : Site d),
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t))
    (hBsym : ∀ y : Site d, (y ∈ B ↔ -y ∈ B)) :
    (∑ y ∈ B, ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y))
      = ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  have h1 : (∑ y ∈ B, ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y))
      = ∑ y ∈ B, ex w (fun ω => indIn K (-y) ω * kcard K ω * kS u K ω) :=
    Finset.sum_congr rfl fun y hy =>
      pairSum_qz_shift w u K V y h0K hKV (hVy y hy) hTI
  rw [h1, sum_neg_eq B hBsym (fun z => ex w (fun ω => indIn K z ω * kcard K ω * kS u K ω))]
  exact ex_sum_indIn_kS w u K B

/-- **Conditional `T3` bound `≤ G`, not a canonical model instantiation.**

The `1/2 + 1/2` split of two halves, each summed to `G`, gives `G`. The printed
`(1/2) G` has an additional factor `1/2` relative to this split. As warned
above, the `hTI`-based hypotheses are not realisable nontrivially; the
satisfiable replacement is `T3_bound_MTP` in `I58Nonvacuity.lean`. This
algebra is retained only as a conditional reduction. -/
theorem T3_bound_global (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) (hK : ∀ ω, K ω ⊆ V)
    (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0)
    (h0K : ∀ ω, (0 : Site d) ∈ K ω)
    (hVy : ∀ y ∈ B, ∀ x : Site d, (x ∈ V ↔ x - y ∈ V))
    (hTI : ∀ (p q r s t : Site d),
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t))
    (hBsym : ∀ y : Site d, (y ∈ B ↔ -y ∈ B)) :
    |∑ y ∈ B, ex w (T3 u K Ky y)|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : (∑ y ∈ B, |ex w (T3 u K Ky y)|)
      ≤ ∑ y ∈ B, ((1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω)
          + (1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω
              * (∑ z ∈ K ω, q u (z - y)))) :=
    Finset.sum_le_sum fun y hy =>
      T3_per_y w hw u K Ky V y hK (hKy y hy) pairProd (hgap y hy) (hprod y hy)
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ex_sum_indIn_kS]
  have heq : (∑ y ∈ B, ex w (fun ω => indIn K y ω * kcard K ω
        * (∑ z ∈ K ω, q u (z - y))))
      = ∑ y ∈ B, ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y) :=
    Finset.sum_congr rfl fun y _ => (pairAll_sum_qz w u K V y hK).symm
  rw [heq, T3_second_half_sum_eq w u K V B h0K hK hVy hTI hBsym]
  linarith

/-- Numerical bookkeeping for the sharpened assembly: with `T3 <= G` (not `G/2`), the
conclusion is `3U + 6G`, i.e. the source's `3U + 5G` shape. -/
theorem abs_assembly_global (a b c e U0 G Gq : ℝ)
    (h1 : |a| ≤ U0) (h2 : |b| ≤ G) (h3 : |c| ≤ G)
    (h4 : |e| ≤ (1 / 2) * G + (1 / 2) * Gq) (h5 : Gq ≤ U0) :
    |a + 2 * b - 2 * c - 4 * e| ≤ 3 * U0 + 6 * G := by
  have ha := abs_le.mp h1
  have hb := abs_le.mp h2
  have hc := abs_le.mp h3
  have he := abs_le.mp h4
  rw [abs_le]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, he.1, he.2]

/-- **Lemma I.5.8 with `T3` and `T4` proved and the global mass-transport layer in place.**
The two displayed cross-term estimates are theorems; the remaining inputs are `hR0`, `hR2`,
the covariance-gap bound `hgap` (source `lem:disjoint_connections`), and the model
symmetries `hTI` (translation invariance of the measure), `hVy` (`V - y = V`), `hBsym`
(`B = -B`), `h0K` (`0 in K`). -/
theorem lemma_I_5_8_assembly_global
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) {r : ℝ}
    (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod3 : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0)
    (hprod4 : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y)) = 0)
    (h0K : ∀ ω, (0 : Site d) ∈ K ω)
    (hVy : ∀ y ∈ B, ∀ x : Site d, (x ∈ V ↔ x - y ∈ V))
    (hTI : ∀ (p q r s t : Site d),
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t))
    (hBsym : ∀ y : Site d, (y ∈ B ↔ -y ∈ B))
    (hR0 : |(∑ y ∈ B, ex w (T0 u K Ky y)) -
        (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (hR2 : |(∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)) :
    |derivTerm w u K Ky B - mainTerm w u K B|
      ≤ 3 * (uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 6 * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  rw [derivTerm_sub_mainTerm]
  exact abs_assembly_global _ _ _ _ _ _ _
    hR0 hR2
    (T3_bound_global w hw u K Ky V B hK hKy pairProd hgap hprod3 h0K hVy hTI hBsym)
    (T4_bound w hw u K Ky V B hK hKy pairProd hgap hprod4)
    (Gq_le_U u K B hw hB)

end PercLib.CriticalLRP.I58

#print axioms PercLib.CriticalLRP.I58.sum_indIn_mul_of_subset
#print axioms PercLib.CriticalLRP.I58.sum_indIn_of_subset
#print axioms PercLib.CriticalLRP.I58.sum_indIn_mul_inter
#print axioms PercLib.CriticalLRP.I58.ex_sum_sum_mul
#print axioms PercLib.CriticalLRP.I58.ex_sum_sum_mul_one
#print axioms PercLib.CriticalLRP.I58.ex_sum_sum_mul_one'
#print axioms PercLib.CriticalLRP.I58.pairAll_nonneg
#print axioms PercLib.CriticalLRP.I58.ex_T3_eq_pairSum
#print axioms PercLib.CriticalLRP.I58.ex_T4_eq_pairSum
#print axioms PercLib.CriticalLRP.I58.pairAll_sum_qx
#print axioms PercLib.CriticalLRP.I58.pairAll_sum_qz
#print axioms PercLib.CriticalLRP.I58.pairAll_sum_qy
#print axioms PercLib.CriticalLRP.I58.q_sub_le_two
#print axioms PercLib.CriticalLRP.I58.sum_q_sub_le
#print axioms PercLib.CriticalLRP.I58.T3_per_y
#print axioms PercLib.CriticalLRP.I58.T4_per_y
#print axioms PercLib.CriticalLRP.I58.prodTerm_vanish
#print axioms PercLib.CriticalLRP.I58.prodTerm_vanish_qy
#print axioms PercLib.CriticalLRP.I58.ex_sum_indIn_kS
#print axioms PercLib.CriticalLRP.I58.ex_sum_indIn_q
#print axioms PercLib.CriticalLRP.I58.ex_sum_indIn_qz_le
#print axioms PercLib.CriticalLRP.I58.T3_bound
#print axioms PercLib.CriticalLRP.I58.T4_bound
#print axioms PercLib.CriticalLRP.I58.abs_assembly_cross
#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly_cross

#print axioms PercLib.CriticalLRP.I58.second_half_demo_023
#print axioms PercLib.CriticalLRP.I58.G_demo_023
#print axioms PercLib.CriticalLRP.I58.second_half_demo_01100
#print axioms PercLib.CriticalLRP.I58.G_demo_01100

#print axioms PercLib.CriticalLRP.I58.parity_zero_of_reflect
#print axioms PercLib.CriticalLRP.I58.parity_zero_of_reflect_about
#print axioms PercLib.CriticalLRP.I58.prodTerm_vanish_of_reflect
#print axioms PercLib.CriticalLRP.I58.prodTerm_vanish_qy_of_reflect

#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly_cross_of_reflect
#print axioms PercLib.CriticalLRP.I58.pairAt
#print axioms PercLib.CriticalLRP.I58.pairAll_eq_pairAt
#print axioms PercLib.CriticalLRP.I58.pairAt_eq_pairAll
#print axioms PercLib.CriticalLRP.I58.sum_shift_bij
#print axioms PercLib.CriticalLRP.I58.sum_neg_eq
#print axioms PercLib.CriticalLRP.I58.pairSum_qz_shift
#print axioms PercLib.CriticalLRP.I58.T3_second_half_sum_eq
#print axioms PercLib.CriticalLRP.I58.T3_bound_global
#print axioms PercLib.CriticalLRP.I58.abs_assembly_global
#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly_global
