/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Exact finite-volume deterministic merge and quadratic cross-term identities for
the quadratic functional `x ↦ ⟨x,u⟩²` of Hutchcroft, "Critical long-range
percolation I", arXiv:2508.18807v1, §I.5.2 (Lemma I.5.7, Lemma I.5.8).

The paper works with the quadratic weight `q_u(x) = ⟨x,u⟩²` on `ℤ^d`.  For the
purposes of the *algebra* only the scalar coordinate `w x = ⟨x,u⟩` is used:
`q_u(z - x) = (w z - w x)²`, `q_u(y) = (w y)²`.  Accordingly everything below is
stated for an arbitrary weight `w : V → ℝ`; the instantiation is
`w x = ⟪x, u⟫_ℝ`, which is additive in `x`, and that additivity is the only
property of `w` used by the paper's rewriting `z - x = (z - y) + (y - 0) + (0 - x)`.

Contents:

* `sq_sub_eq_trinomial`, `sq_sub_eq_absolute`: the translated trinomial
  expansion `(α - γ)² = (α - β)² + (β - γ)² + 2(α - β)(β - γ)` and the
  expansion of the shift `(β - α)² = β² + α² - 2αβ`.
* `sum_sq_sub_shift`, `sum_sq_sub_shift_absolute`: the same after summing over a
  finite cluster `B`, with the base point moved from `a` to `b`; these are the
  exact forms of the paper's step `z - x = (z - y) + (y - 0)`.
* `sum_sum_sq_sub_cross` and `sum_sum_sq_sub_cross_of_centred`: the exact
  two-cluster quadratic cross term.  It has the shape

      |K_o| S(K_y) + |K_y| S(K_o) + |K_o||K_y| q_u(y)

  of the merge increment, plus three explicitly signed correction terms which
  are absent in the translation-invariant (mass-transport) infinite-volume
  picture and which the finite-volume derivation must carry.
* `sum_sum_sq_pairEnergy_merge`: the merge increment of the full pairwise
  quadratic energy `∑_{x,z∈K}(w z - w x)²`, in which the cross term occurs
  with the coefficient `2` and hence produces the literal `2|K_o||K_y|q_u(y)`.
* `quadMoment`, `centredMoment`, `centredLinear`: the absolute, centred and
  centred-linear cluster moments.
* `quadMoment_flip_eq`, `quadMoment_flip_sub_of_not_conn`: the first pivotal
  formula for a merging edge (the merged moment splits additively).
* `centredMoment_flip_sub_of_not_conn`, `centredMoment_flip_trinomial`,
  `centredMoment_flip_absolute`: the first pivotal formula in centred form and
  its trinomial decomposition into the paper's main, fluctuation and linear
  cross terms.
* `quadMoment_far_decomposition`, `quadMoment_far_decomposition_relative`: the
  per-edge decomposition of the moment of the far cluster `K_y` that produces
  the paper's `|K_y|⟨y,u⟩²`, `∑_{z∈K_y}⟨z-y,u⟩²` and
  `2⟨y,u⟩∑_{z∈K_y}⟨z-y,u⟩` terms (absolute form) and the corresponding
  `|K_y|⟨y,u⟩² + |K_y|⟨x,u⟩² - 2|K_y|⟨x,u⟩⟨y,u⟩` terms (relative form).
* `quadMoment_far_sub_centred`: the exact difference between the absolute and
  the relative moment of `K_y` (the finite-volume replacement for the paper's
  mass-transport step, producing its third and sixth terms).
* `quadMoment_diff_of_conn_left`, `quadMoment_diff_of_conn_right`,
  `quadMoment_diff_of_not_conn_both`: the complete case analysis for the
  pivotal increment of the quadratic moment at an arbitrary base point `o`
  (`o` in the cluster of `s e`, in that of `t e`, or in neither).
* `crossMoment_clusters`, `pairEnergy_merge_clusters`,
  `pairEnergy_merge_increment_of_centred`: the cluster-level cross term and the
  merge increment of the pairwise quadratic energy, where the coefficient of
  `|K_o||K_y| q_u` is the literal `2`.
* `pivotalSum_quadMoment_eq_farMoment`, `pivotalSum_quadMoment_eq_decomposition`:
  the exact finite-configuration rewriting of the Russo pivotal sum for
  `∑_{x∈K}⟨x,u⟩²` into the sum over pivotal edges of the moment of the far
  cluster, and into its main/fluctuation/linear decomposition -- the
  finite-volume, exact form of the first display in the proof of Lemma I.5.8.
* `pivotalContribution`, `pivotalSum_quadMoment_eq_pivotalContribution`,
  `hasDerivAt_expectation_quadMoment_rooted`: the rooted version for an
  arbitrary base point `o`, giving the exact Russo derivative of
  `E_{β,r}[∑_{x∈K_o}⟨x,u⟩²]` as a sum over edges of rooted pivotal
  contributions.
* `hasDerivAt_expectation_quadMoment` and `secondDeriv_expectation_quadMoment`:
  the first-order (Russo) and second-order (pair-pivotal) formulas for the
  quadratic moment, the latter obtained from `RussoSecondOrder`.
* `quadMoment_nonneg`, `centredMoment_nonneg`, `sum_sum_sq_nonneg`: the
  elementary sign facts used by the error estimates.

No probability, no continuity and no mass-transport principle is assumed: all
identities are exact finite sums over a finite graph and its finite
configuration space.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.SpatialMoments
public import PercLib.CriticalLRP.RussoSecondOrder

set_option autoImplicit true

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.FiniteVolume

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The translated trinomial expansion -/

/-- `(α - γ)² = (α - β)² + (β - γ)² + 2(α - β)(β - γ)`.  This is the paper's
expansion of `⟨z - x, u⟩²` after writing `z - x = (z - y) + (y - x)`; it is the
`u`-coordinate form of the identity, and requires no structure on `V`. -/
theorem sq_sub_eq_trinomial (α β γ : ℝ) :
    (α - γ) ^ 2 = (α - β) ^ 2 + (β - γ) ^ 2 + 2 * (α - β) * (β - γ) := by
  ring

/-- `(β - α)² = β² + α² - 2αβ`: the shift expansion used for the paper's
`⟨y - x, u⟩² = ⟨y,u⟩² + ⟨x,u⟩² - 2⟨x,u⟩⟨y,u⟩`. -/
theorem sq_sub_eq_absolute (α β : ℝ) :
    (β - α) ^ 2 = β ^ 2 + α ^ 2 - 2 * α * β := by
  ring

/-! ### Summed shift identities on a finite cluster -/

/-- **Translated trinomial expansion, summed over a finite cluster.**  Moving
the base point of the quadratic moment from `a` to `b` costs the leading term
`|B|·(w b - w a)²` plus the linear cross term with the centred first moment. -/
theorem sum_sq_sub_shift {B : Finset V} (w : V → ℝ) (a b : V) :
    ∑ z ∈ B, (w z - w a) ^ 2
      = (∑ z ∈ B, (w z - w b) ^ 2) + (B.card : ℝ) * (w b - w a) ^ 2
        + 2 * (w b - w a) * (∑ z ∈ B, (w z - w b)) := by
  have hcard : (B.card : ℝ) * (w b - w a) ^ 2 = ∑ _z ∈ B, (w b - w a) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hcard, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sq_sub_eq_trinomial (w z) (w b) (w a)]
  ring

/-- **Translated trinomial expansion in absolute coordinates.**  Summed form of
`(w z - w a)² = (w z - w b)² + (w b)² + (w a)² - 2 (w a)(w b) + 2(w b - w a)(w z - w b)`. -/
theorem sum_sq_sub_shift_absolute {B : Finset V} (w : V → ℝ) (a b : V) :
    ∑ z ∈ B, (w z - w a) ^ 2
      = (∑ z ∈ B, (w z - w b) ^ 2) + (B.card : ℝ) * (w b) ^ 2
        + (B.card : ℝ) * (w a) ^ 2 - 2 * (B.card : ℝ) * (w a) * (w b)
        + 2 * (w b - w a) * (∑ z ∈ B, (w z - w b)) := by
  rw [sum_sq_sub_shift w a b]
  have h1 : (B.card : ℝ) * (w b - w a) ^ 2
      = (B.card : ℝ) * (w b) ^ 2 + (B.card : ℝ) * (w a) ^ 2
        - 2 * (B.card : ℝ) * (w a) * (w b) := by
    rw [sq_sub_eq_absolute (w a) (w b)]; ring
  rw [h1]; ring

/-- **The exact two-cluster quadratic cross term.**  For finite clusters `A`, `B`
and base points `a ∈ A`, `b ∈ B` (in the application `a = x`, `b = y`,
`A = K_x`, `B = K_y`),

  `∑_{x∈A} ∑_{z∈B} (w z - w x)²`

equals the merge-increment shape `|A| S_b(B) + |B| S_a(A) + |A||B| (w b - w a)²`
together with the three signed correction terms produced by the two centred
first moments.  All coefficients are exact. -/
theorem sum_sum_sq_sub_cross {A B : Finset V} (w : V → ℝ) (a b : V) :
    ∑ x ∈ A, ∑ z ∈ B, (w z - w x) ^ 2
      = (A.card : ℝ) * (B.card : ℝ) * (w b - w a) ^ 2
        + (A.card : ℝ) * (∑ z ∈ B, (w z - w b) ^ 2)
        + (B.card : ℝ) * (∑ x ∈ A, (w x - w a) ^ 2)
        + 2 * (A.card : ℝ) * (w b - w a) * (∑ z ∈ B, (w z - w b))
        - 2 * (B.card : ℝ) * (w b - w a) * (∑ x ∈ A, (w x - w a))
        - 2 * (∑ x ∈ A, (w x - w a)) * (∑ z ∈ B, (w z - w b)) := by
  have hinner : ∀ x : V, ∑ z ∈ B, (w z - w x) ^ 2
      = (∑ z ∈ B, (w z - w b) ^ 2) + (B.card : ℝ) * (w b - w x) ^ 2
        + 2 * (w b - w x) * (∑ z ∈ B, (w z - w b)) :=
    fun x => sum_sq_sub_shift w x b
  have hstep : ∑ x ∈ A, ∑ z ∈ B, (w z - w x) ^ 2
      = ∑ x ∈ A, ((∑ z ∈ B, (w z - w b) ^ 2) + (B.card : ℝ) * (w b - w x) ^ 2
        + 2 * (w b - w x) * (∑ z ∈ B, (w z - w b))) :=
    Finset.sum_congr rfl fun x _ => hinner x
  rw [hstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hS1 : ∑ _x ∈ A, (∑ z ∈ B, (w z - w b) ^ 2)
      = (A.card : ℝ) * (∑ z ∈ B, (w z - w b) ^ 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hS2 : ∑ x ∈ A, (B.card : ℝ) * (w b - w x) ^ 2
      = (B.card : ℝ) * (∑ x ∈ A, (w b - w x) ^ 2) := by
    rw [← Finset.mul_sum]
  have hS3 : ∑ x ∈ A, 2 * (w b - w x) * (∑ z ∈ B, (w z - w b))
      = 2 * (∑ x ∈ A, (w b - w x)) * (∑ z ∈ B, (w z - w b)) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hS1, hS2, hS3]
  have hB2 : ∑ x ∈ A, (w b - w x) ^ 2 = ∑ x ∈ A, (w x - w b) ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hB2, sum_sq_sub_shift (B := A) w b a]
  have hlin : ∑ x ∈ A, (w b - w x)
      = (A.card : ℝ) * (w b - w a) - (∑ x ∈ A, (w x - w a)) := by
    have : ∑ x ∈ A, (w b - w x)
        = ∑ x ∈ A, ((w b - w a) - (w x - w a)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [this, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hlin]
  ring

/-- **Centred cross term.**  If both clusters have vanishing centred first
moment (their base points are their `u`-centroids), the two-cluster cross term
is exactly the merge-increment shape
`|A||B|(w b - w a)² + |A| S_b(B) + |B| S_a(A)`. -/
theorem sum_sum_sq_sub_cross_of_centred {A B : Finset V} (w : V → ℝ) (a b : V)
    (hA : ∑ x ∈ A, (w x - w a) = 0) (hB : ∑ z ∈ B, (w z - w b) = 0) :
    ∑ x ∈ A, ∑ z ∈ B, (w z - w x) ^ 2
      = (A.card : ℝ) * (B.card : ℝ) * (w b - w a) ^ 2
        + (A.card : ℝ) * (∑ z ∈ B, (w z - w b) ^ 2)
        + (B.card : ℝ) * (∑ x ∈ A, (w x - w a) ^ 2) := by
  rw [sum_sum_sq_sub_cross, hA, hB]
  ring

/-- **Merge of the pairwise quadratic energy.**  For disjoint clusters `A`, `B`
the full pairwise energy `∑_{x,z∈K}(w z - w x)²` of the union splits into the
two internal energies plus twice the cross term.  Composing with
`sum_sum_sq_sub_cross` this is the identity whose cross term carries the literal
coefficient `2|A||B|` in front of `(w b - w a)²`, i.e. `2|K_o||K_y|q_u(y)` for
`w y = ⟨y,u⟩`. -/
theorem sum_sum_sq_pairEnergy_merge {A B : Finset V} (hAB : Disjoint A B) (w : V → ℝ) :
    ∑ x ∈ A ∪ B, ∑ z ∈ A ∪ B, (w z - w x) ^ 2
      = (∑ x ∈ A, ∑ z ∈ A, (w z - w x) ^ 2)
        + (∑ x ∈ B, ∑ z ∈ B, (w z - w x) ^ 2)
        + 2 * (∑ x ∈ A, ∑ z ∈ B, (w z - w x) ^ 2) := by
  have hcross : ∑ x ∈ B, ∑ z ∈ A, (w z - w x) ^ 2
      = ∑ x ∈ A, ∑ z ∈ B, (w z - w x) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
    ring
  simp only [Finset.sum_union hAB]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcross]
  ring

/-! ### Cluster moments attached to the quadratic weight -/

/-- The absolute quadratic spatial moment `∑_{x∈K_o} (w x)²` of the cluster of
`o`.  It is `spatialMoment` for the weight `q x = (w x)²`, i.e. `q_u` for
`w x = ⟨x,u⟩`. -/
noncomputable def quadMoment (s t : E → V) (w : V → ℝ) (o : V) (ω : Finset E) : ℝ :=
  spatialMoment s t (fun x => (w x) ^ 2) o ω

/-- The centred quadratic moment `∑_{x∈K_o} (w x - w o)²`. -/
noncomputable def centredMoment (s t : E → V) (w : V → ℝ) (o : V) (ω : Finset E) : ℝ :=
  ∑ x ∈ cluster s t ω o, (w x - w o) ^ 2

/-- The centred linear moment `∑_{x∈K_o} (w x - w o)`: the first moment about
the base point, which controls the signed cross terms of the merge identities. -/
noncomputable def centredLinear (s t : E → V) (w : V → ℝ) (o : V) (ω : Finset E) : ℝ :=
  ∑ x ∈ cluster s t ω o, (w x - w o)

/-- Base change for the quadratic moment: connected base points give the same
cluster, hence the same moment. -/
theorem quadMoment_base_of_conn {s t : E → V} (w : V → ℝ) {ω : Finset E} {o x : V}
    (h : Conn s t ω o x) : quadMoment s t w o ω = quadMoment s t w x ω :=
  spatialMoment_base_of_conn (fun y => (w y) ^ 2) h

/-! ### First pivotal formula for a merging edge -/

/-- **First pivotal formula (additive form).**  Opening a pivotal edge `e`
merges the cluster of `s e` with the disjoint cluster of `t e`, so the
quadratic moment of the enlarged cluster is the sum of the two old moments. -/
theorem quadMoment_flip_eq {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    quadMoment s t w (s e) (insert e ω)
      = quadMoment s t w (s e) ω + quadMoment s t w (t e) ω :=
  spatialMoment_insert_of_not_conn (fun y => (w y) ^ 2) hxy

/-- **First pivotal formula (increment form).**  The increment of the quadratic
moment of the cluster of `s e` is exactly the quadratic moment of the far
cluster `K_y`, the finite-volume form of the paper's
`1(y ∉ K) ∑_{z∈K_y}⟨z,u⟩²`. -/
theorem quadMoment_flip_sub_of_not_conn {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    quadMoment s t w (s e) (insert e ω) - quadMoment s t w (s e) ω
      = ∑ z ∈ cluster s t ω (t e), (w z) ^ 2 := by
  rw [quadMoment_flip_eq w hxy]
  simp [quadMoment, spatialMoment]

/-- **First pivotal formula for the far cluster.**  Opening the pivotal edge `e`
also merges the cluster of `t e`; written from that side the increment is the
moment of the cluster of `s e`. -/
theorem quadMoment_flip_eq_right {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    quadMoment s t w (t e) (insert e ω)
      = quadMoment s t w (t e) ω + quadMoment s t w (s e) ω := by
  unfold quadMoment spatialMoment
  have hunion : cluster s t (insert e ω) (t e)
      = cluster s t ω (t e) ∪ cluster s t ω (s e) := by
    ext z
    rw [mem_cluster_insert_right, mem_union]
  rw [hunion, sum_union (disjoint_comm.mpr (disjoint_cluster_of_not_conn hxy))]

/-- **First pivotal formula (centred increment form).**  In centred coordinates
about the base point `s e` the increment is the centred moment of the far
cluster about `s e`. -/
theorem centredMoment_flip_sub_of_not_conn {s t : E → V} (w : V → ℝ) {e : E}
    {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e)) :
    centredMoment s t w (s e) (insert e ω) - centredMoment s t w (s e) ω
      = ∑ z ∈ cluster s t ω (t e), (w z - w (s e)) ^ 2 := by
  unfold centredMoment
  rw [cluster_insert_union_of_not_conn hxy,
    sum_union (disjoint_cluster_of_not_conn hxy)]
  ring

/-- **First pivotal formula, translated trinomial expansion.**  The increment of
the centred moment of the cluster of `s e` decomposes into the centred moment of
the far cluster about `t e`, the leading term `|K_y| (w y - w x)²` and the linear
cross term with the centred first moment of the far cluster.  This is the
per-edge form of the paper's expansion of `∑_{z∈K_y}⟨z-x,u⟩²`. -/
theorem centredMoment_flip_trinomial {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    centredMoment s t w (s e) (insert e ω) - centredMoment s t w (s e) ω
      = centredMoment s t w (t e) ω
        + ((cluster s t ω (t e)).card : ℝ) * (w (t e) - w (s e)) ^ 2
        + 2 * (w (t e) - w (s e)) * centredLinear s t w (t e) ω := by
  rw [centredMoment_flip_sub_of_not_conn w hxy]
  exact sum_sq_sub_shift (B := cluster s t ω (t e)) w (s e) (t e)

/-- **First pivotal formula, absolute-coordinate form.**  Expanding
`(w y - w x)² = (w y)² + (w x)² - 2 (w x)(w y)` in
`centredMoment_flip_trinomial` produces the three main terms `|K_y|⟨y,u⟩²`,
`|K_y|⟨x,u⟩²` and `-2|K_y|⟨x,u⟩⟨y,u⟩` of the paper's decomposition (its first,
third and sixth terms), with the two fluctuation/linear terms carrying the
centred moment of `K_y`. -/
theorem centredMoment_flip_absolute {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    centredMoment s t w (s e) (insert e ω) - centredMoment s t w (s e) ω
      = centredMoment s t w (t e) ω
        + ((cluster s t ω (t e)).card : ℝ) * (w (t e)) ^ 2
        + ((cluster s t ω (t e)).card : ℝ) * (w (s e)) ^ 2
        - 2 * ((cluster s t ω (t e)).card : ℝ) * (w (s e)) * (w (t e))
        + 2 * (w (t e) - w (s e)) * centredLinear s t w (t e) ω := by
  rw [centredMoment_flip_sub_of_not_conn w hxy]
  exact sum_sq_sub_shift_absolute (B := cluster s t ω (t e)) w (s e) (t e)

/-! ### Decomposition of the far-cluster moment -/

/-- **Decomposition of the far cluster's absolute moment** (the paper's first,
second and fourth terms): the moment of `K_y` about the origin is
`|K_y|⟨y,u⟩²` plus the internal fluctuation `∑_{z∈K_y}⟨z-y,u⟩²` plus the linear
term `2⟨y,u⟩ ∑_{z∈K_y}⟨z-y,u⟩`. -/
theorem quadMoment_far_decomposition {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E} :
    ∑ z ∈ cluster s t ω (t e), (w z) ^ 2
      = ((cluster s t ω (t e)).card : ℝ) * (w (t e)) ^ 2
        + ∑ z ∈ cluster s t ω (t e), (w z - w (t e)) ^ 2
        + 2 * (w (t e)) * (∑ z ∈ cluster s t ω (t e), (w z - w (t e))) := by
  have hcard : ((cluster s t ω (t e)).card : ℝ) * (w (t e)) ^ 2
      = ∑ _z ∈ cluster s t ω (t e), (w (t e)) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hcard, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

/-- **Decomposition of the far cluster's moment about the pivotal point `x`**
(the paper's first, third and sixth terms together with the fluctuations): the
moment of `K_y` about `x = s e` is
`|K_y|⟨y,u⟩² + |K_y|⟨x,u⟩² - 2|K_y|⟨x,u⟩⟨y,u⟩` plus the internal fluctuation and
the linear term.  The three leading terms are exactly the ones that produce
`2|B_r|E|K| S_r` and `(E|K|)² ∑_{y∈B_r}⟨y,u⟩²` after summing over the cluster
and using mass transport; the remaining two are the signed error terms. -/
theorem quadMoment_far_decomposition_relative {s t : E → V} (w : V → ℝ) {e : E}
    {ω : Finset E} :
    ∑ z ∈ cluster s t ω (t e), (w z - w (s e)) ^ 2
      = ((cluster s t ω (t e)).card : ℝ) * (w (t e)) ^ 2
        + ((cluster s t ω (t e)).card : ℝ) * (w (s e)) ^ 2
        - 2 * ((cluster s t ω (t e)).card : ℝ) * (w (s e)) * (w (t e))
        + ∑ z ∈ cluster s t ω (t e), (w z - w (t e)) ^ 2
        + 2 * (w (t e) - w (s e)) * (∑ z ∈ cluster s t ω (t e), (w z - w (t e))) := by
  rw [sum_sq_sub_shift_absolute (B := cluster s t ω (t e)) w (s e) (t e)]
  ring

/-! ### The exact finite-configuration pivotal sum -/

/-- For a configuration `τ` and an edge `e`, the quadratic moment of the far
cluster `K_{t e}` when `e` is pivotal (its endpoints are not connected), and `0`
otherwise.  This is the exact finite-volume counterpart of the paper's summand
`1(y ∉ K) ∑_{z∈K_y}⟨z,u⟩²`. -/
noncomputable def farMomentIfPivotal (s t : E → V) (w : V → ℝ) (e : E)
    (τ : Finset E) : ℝ := by
  classical
  exact if h : ¬ Conn s t τ (s e) (t e) then ∑ z ∈ cluster s t τ (t e), (w z) ^ 2 else 0

/-- **Exact pivotal sum for the quadratic moment.**  For a fixed base point
`o = s e`, the difference of the quadratic moment across the flip of `e` is
`0` when `e` is not pivotal and is the quadratic moment of the far cluster
`K_{t e}` when it is.  This is the exact finite-volume form of the inner sum
`∑_{x∈K} ∑_{y∈B_r(x)} 1(y ∉ K) ∑_{z∈K_y} ⟨z,u⟩²` in the proof of Lemma I.5.8,
with the spatial kernel replaced by the finite edge set and the indicator
`1(y ∉ K)` by pivotality. -/
theorem pivotalSum_quadMoment_eq_farMoment
    (s t : E → V) (w : V → ℝ) (len : E → ℝ) (K : ℝ → ℝ) {r β : ℝ} :
    ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * (quadMoment s t w (s e) (insert e τ) - quadMoment s t w (s e) τ)
      = ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * farMomentIfPivotal s t w e τ := by
  classical
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun τ _ => ?_
  by_cases hxy : ¬ Conn s t τ (s e) (t e)
  · rw [quadMoment_flip_sub_of_not_conn w hxy]
    unfold farMomentIfPivotal
    rw [dite_eq_left hxy]
  · have hconn : Conn s t τ (s e) (t e) := not_not.mp hxy
    have hsame : quadMoment s t w (s e) (insert e τ) = quadMoment s t w (s e) τ := by
      simp only [quadMoment, spatialMoment, cluster_insert_of_conn hconn]
    rw [hsame, sub_self]
    unfold farMomentIfPivotal
    rw [dite_eq_right hxy]

/-! ### First pivotal formula at an arbitrary base point -/

/-- **Pivotal increment at a base point inside the cluster of `s e`.**  If `o`
is connected to `s e` (so `o` lies in the merged cluster, the paper's `x ∈ K`),
opening the pivotal edge `e` adds exactly the quadratic moment of the far
cluster `K_{t e}`. -/
theorem quadMoment_diff_of_conn_left {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    {o : V} (hxy : ¬ Conn s t ω (s e) (t e)) (h : Conn s t ω o (s e)) :
    quadMoment s t w o (insert e ω) - quadMoment s t w o ω
      = quadMoment s t w (t e) ω := by
  have hnot : ¬ Conn s t ω o (t e) := fun h2 => hxy ((conn_symm h).trans h2)
  have hleft : quadMoment s t w o (insert e ω) = quadMoment s t w (s e) (insert e ω) :=
    quadMoment_base_of_conn w (conn_mono (subset_insert e ω) h)
  have hright : quadMoment s t w o ω = quadMoment s t w (s e) ω :=
    quadMoment_base_of_conn w h
  rw [hleft, hright, quadMoment_flip_eq w hxy]
  ring

/-- **Pivotal increment at a base point inside the cluster of `t e`.**  The
symmetric case: if `o` is connected to `t e`, opening `e` adds the quadratic
moment of the cluster of `s e`. -/
theorem quadMoment_diff_of_conn_right {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    {o : V} (hxy : ¬ Conn s t ω (s e) (t e)) (h : Conn s t ω o (t e)) :
    quadMoment s t w o (insert e ω) - quadMoment s t w o ω
      = quadMoment s t w (s e) ω := by
  have hleft : quadMoment s t w o (insert e ω) = quadMoment s t w (t e) (insert e ω) :=
    quadMoment_base_of_conn w (conn_mono (subset_insert e ω) h)
  have hright : quadMoment s t w o ω = quadMoment s t w (t e) ω :=
    quadMoment_base_of_conn w h
  rw [hleft, hright, quadMoment_flip_eq_right w hxy]
  ring

/-- **Pivotal increment at a base point outside both clusters.**  If `o` is
connected to neither endpoint (the paper's `y ∉ K` for a point `y` outside the
cluster of the origin), opening the pivotal edge `e` does not change the moment
of the cluster of `o`. -/
theorem quadMoment_diff_of_not_conn_both {s t : E → V} (w : V → ℝ) {e : E}
    {ω : Finset E} {o : V} (h1 : ¬ Conn s t ω o (s e)) (h2 : ¬ Conn s t ω o (t e)) :
    quadMoment s t w o (insert e ω) - quadMoment s t w o ω = 0 := by
  have hcl : cluster s t (insert e ω) o = cluster s t ω o :=
    cluster_insert_of_not_conn_both h1 h2
  simp only [quadMoment, spatialMoment, hcl, sub_self]

/-! ### Cluster-level quadratic cross terms -/

/-- **Quadratic cross term between the two clusters merged by `e`.**  This is
`sum_sum_sq_sub_cross` for `A = K_{s e}`, `B = K_{t e}`, `a = s e`, `b = t e`:
the merge-increment shape `|K_y| S(K_o) + |K_o| S(K_y) + |K_o||K_y| q_u(y - x)`
with `S` the *centred* quadratic moment and `q_u(y - x) = (w y - w x)²`,
together with the three signed correction terms generated by the centred first
moments of the two clusters (two linear terms and the bilinear product
`-2 L(K_o)L(K_y)`).  In the translation-invariant infinite-volume picture the
centred first moments vanish on average and only the leading shape survives. -/
theorem crossMoment_clusters {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E} :
    ∑ x ∈ cluster s t ω (s e), ∑ z ∈ cluster s t ω (t e), (w z - w x) ^ 2
      = ((cluster s t ω (s e)).card : ℝ) * ((cluster s t ω (t e)).card : ℝ)
          * (w (t e) - w (s e)) ^ 2
        + ((cluster s t ω (s e)).card : ℝ) * centredMoment s t w (t e) ω
        + ((cluster s t ω (t e)).card : ℝ) * centredMoment s t w (s e) ω
        + 2 * ((cluster s t ω (s e)).card : ℝ) * (w (t e) - w (s e))
            * centredLinear s t w (t e) ω
        - 2 * ((cluster s t ω (t e)).card : ℝ) * (w (t e) - w (s e))
            * centredLinear s t w (s e) ω
        - 2 * centredLinear s t w (s e) ω * centredLinear s t w (t e) ω := by
  rw [sum_sum_sq_sub_cross (A := cluster s t ω (s e)) (B := cluster s t ω (t e))
    w (s e) (t e)]
  rfl

/-- **Merge increment of the pairwise quadratic energy of two clusters.**  For
the two clusters merged by the pivotal edge `e`, the pairwise energy
`∑_{x,z∈K}(w z - w x)²` of the union is the sum of the two internal energies
plus twice the cross term; with `crossMoment_clusters` this is the identity that
carries the literal coefficient `2|K_o||K_y|` in front of `q_u(y)`. -/
theorem pairEnergy_merge_clusters {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    ∑ x ∈ cluster s t (insert e ω) (s e), ∑ z ∈ cluster s t (insert e ω) (s e),
        (w z - w x) ^ 2
      = (∑ x ∈ cluster s t ω (s e), ∑ z ∈ cluster s t ω (s e), (w z - w x) ^ 2)
        + (∑ x ∈ cluster s t ω (t e), ∑ z ∈ cluster s t ω (t e), (w z - w x) ^ 2)
        + 2 * (∑ x ∈ cluster s t ω (s e), ∑ z ∈ cluster s t ω (t e),
            (w z - w x) ^ 2) := by
  rw [cluster_insert_union_of_not_conn hxy]
  exact sum_sum_sq_pairEnergy_merge (disjoint_cluster_of_not_conn hxy) w

/-- **Merge increment of the pairwise quadratic energy, leading terms.**  With
both clusters centred at their base points, the increment of the pairwise energy
`∑_{x,z∈K}(w z - w x)²` when `e` is opened is

  `E(K_y) + 2 (|K_y| S(K_o) + |K_o| S(K_y) + |K_o||K_y| q_u(y - x))`,

where `S` is the centred quadratic moment and `q_u(y - x) = (w y - w x)²`.
This is the exact finite form of the expression
`|K_y| S(K_o) + |K_o| S(K_y) + 2|K_o||K_y| q_u(y)` in which the coefficient `2`
multiplying `|K_o||K_y| q_u` arises from the ordered-pair (double-counted) cross
term of the pairwise energy; for a single ordered cross term the coefficient of
`|K_o||K_y| q_u` is `1`, as shown by `crossMoment_clusters`. -/
theorem pairEnergy_merge_increment_of_centred {s t : E → V} (w : V → ℝ) {e : E}
    {ω : Finset E} (hxy : ¬ Conn s t ω (s e) (t e))
    (h1 : centredLinear s t w (s e) ω = 0)
    (h2 : centredLinear s t w (t e) ω = 0) :
    (∑ x ∈ cluster s t (insert e ω) (s e), ∑ z ∈ cluster s t (insert e ω) (s e),
        (w z - w x) ^ 2)
        - (∑ x ∈ cluster s t ω (s e), ∑ z ∈ cluster s t ω (s e), (w z - w x) ^ 2)
      = (∑ x ∈ cluster s t ω (t e), ∑ z ∈ cluster s t ω (t e), (w z - w x) ^ 2)
        + 2 * (((cluster s t ω (s e)).card : ℝ) * ((cluster s t ω (t e)).card : ℝ)
            * (w (t e) - w (s e)) ^ 2
          + ((cluster s t ω (s e)).card : ℝ) * centredMoment s t w (t e) ω
          + ((cluster s t ω (t e)).card : ℝ) * centredMoment s t w (s e) ω) := by
  rw [pairEnergy_merge_clusters w hxy, crossMoment_clusters (s := s) (t := t) w (e := e) (ω := ω),
    h1, h2]
  ring

/-! ### Nonnegativity -/

theorem quadMoment_nonneg (s t : E → V) (w : V → ℝ) (o : V) (ω : Finset E) :
    0 ≤ quadMoment s t w o ω := by
  unfold quadMoment spatialMoment
  exact Finset.sum_nonneg fun x _ => sq_nonneg (w x)

theorem centredMoment_nonneg (s t : E → V) (w : V → ℝ) (o : V) (ω : Finset E) :
    0 ≤ centredMoment s t w o ω := by
  unfold centredMoment
  exact Finset.sum_nonneg fun x _ => sq_nonneg (w x - w o)

theorem sum_sum_sq_nonneg {A B : Finset V} (w : V → ℝ) :
    0 ≤ ∑ x ∈ A, ∑ z ∈ B, (w z - w x) ^ 2 :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Absolute versus relative far-cluster moment.**  For any base point `o`,
the absolute quadratic moment of a cluster differs from its moment about `o` by
an explicit linear correction.  With `o = x = s e` this is the exact
finite-volume replacement for the paper's mass-transport step that turns
`∑_{z∈K_y}⟨z,u⟩²` into `∑_{z∈K_y}⟨z-x,u⟩²`, and it produces the third and sixth
terms of the six-term expansion. -/
theorem quadMoment_far_sub_centred {s t : E → V} (w : V → ℝ) {e : E} {ω : Finset E}
    (o : V) :
    (∑ z ∈ cluster s t ω (t e), (w z) ^ 2)
        - (∑ z ∈ cluster s t ω (t e), (w z - w o) ^ 2)
      = 2 * (w o) * (∑ z ∈ cluster s t ω (t e), w z)
        - ((cluster s t ω (t e)).card : ℝ) * (w o) ^ 2 := by
  have hcard : ((cluster s t ω (t e)).card : ℝ) * (w o) ^ 2
      = ∑ _z ∈ cluster s t ω (t e), (w o) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hpt : ∀ z ∈ cluster s t ω (t e),
      (w z) ^ 2 - (w z - w o) ^ 2 = 2 * (w o) * w z - (w o) ^ 2 := by
    intro z _
    ring
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, hcard,
    Finset.mul_sum]

/-! ### Decomposition of the pivotal sum -/

/-- The T1/T3/T6 + fluctuation + linear decomposition of the far-cluster
moment, with the non-pivotal case set to `0`.  Its value in the pivotal case is
`quadMoment_far_decomposition_relative`. -/
noncomputable def farMomentDecomp (s t : E → V) (w : V → ℝ) (e : E) (τ : Finset E) : ℝ := by
  classical
  exact if h : ¬ Conn s t τ (s e) (t e) then
      ((cluster s t τ (t e)).card : ℝ) * (w (t e)) ^ 2
      + (∑ z ∈ cluster s t τ (t e), (w z - w (t e)) ^ 2)
      + 2 * (w (t e)) * (∑ z ∈ cluster s t τ (t e), (w z - w (t e)))
    else 0

theorem farMomentIfPivotal_eq_decomp (s t : E → V) (w : V → ℝ) (e : E) (τ : Finset E) :
    farMomentIfPivotal s t w e τ = farMomentDecomp s t w e τ := by
  classical
  by_cases h : ¬ Conn s t τ (s e) (t e)
  · unfold farMomentIfPivotal farMomentDecomp
    rw [dite_eq_left h, dite_eq_left h]
    exact quadMoment_far_decomposition (s := s) (t := t) (w := w) (e := e) (ω := τ)
  · unfold farMomentIfPivotal farMomentDecomp
    rw [dite_eq_right h, dite_eq_right h]

/-- **Exact decomposition of the pivotal sum for the quadratic moment.**  The
Russo pivotal sum of `∑_{x∈K}⟨x,u⟩²` is, edge by edge, the sum of the paper's
leading term `|K_y|⟨y,u⟩²`, the internal fluctuation
`∑_{z∈K_y}⟨z-y,u⟩²` and the linear term `2⟨y,u⟩∑_{z∈K_y}⟨z-y,u⟩` (with
`y = t e`).  This is the exact finite-volume content of the first, second and
fourth terms of the six-term expansion displayed in the proof of Lemma I.5.8;
no mass-transport step is performed, so the remaining two terms of the paper
(the third one `∑_{x∈K}⟨x,u⟩² ∑_y 1(y∉K)|K_y|` and the sixth one
`-2∑_{x∈K}⟨x,u⟩∑_y⟨y,u⟩1(y∉K)|K_y|`) appear only after replacing the absolute
moment of `K_y` by its moment about `x = s e` via `quadMoment_far_sub_centred`
and `quadMoment_far_decomposition_relative`. -/
theorem pivotalSum_quadMoment_eq_decomposition
    (s t : E → V) (w : V → ℝ) (len : E → ℝ) (K : ℝ → ℝ) {r β : ℝ} :
    ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * (quadMoment s t w (s e) (insert e τ) - quadMoment s t w (s e) τ)
      = ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * farMomentDecomp s t w e τ := by
  rw [pivotalSum_quadMoment_eq_farMoment]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [farMomentIfPivotal_eq_decomp]

/-! ### The rooted pivotal contribution -/

/-- The contribution of a single edge `e` and configuration `τ` to the pivotal
sum of the quadratic moment of the cluster of a fixed base point `o`: it is the
quadratic moment of the far cluster when `e` is pivotal and `o` lies in the
cluster of `s e` (resp. of `t e`), and `0` otherwise.  This is the exact
finite-volume form of the paper's `x ∈ K`, `y ∉ K` bookkeeping. -/
noncomputable def pivotalContribution (s t : E → V) (w : V → ℝ) (o : V) (e : E)
    (τ : Finset E) : ℝ := by
  classical
  exact if h : ¬ Conn s t τ (s e) (t e) then
      (if h2 : Conn s t τ o (s e) then ∑ z ∈ cluster s t τ (t e), (w z) ^ 2 else 0)
      + (if h3 : Conn s t τ o (t e) then ∑ z ∈ cluster s t τ (s e), (w z) ^ 2 else 0)
    else 0

/-- **Rooted pivotal sum.**  For an arbitrary base point `o` the flip difference
of the quadratic moment of the cluster of `o` is exactly the rooted pivotal
contribution.  This is the exact finite-volume form of the paper's derivative
display, before any mass-transport step. -/
theorem pivotalSum_quadMoment_eq_pivotalContribution
    (s t : E → V) (w : V → ℝ) (o : V) (len : E → ℝ) (K : ℝ → ℝ) {r β : ℝ} :
    ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * (quadMoment s t w o (insert e τ) - quadMoment s t w o τ)
      = ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * pivotalContribution s t w o e τ := by
  classical
  have hqm : ∀ (x : V) (υ : Finset E), quadMoment s t w x υ = ∑ z ∈ cluster s t υ x, (w z) ^ 2 :=
    fun _ _ => rfl
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun τ _ => ?_
  by_cases hxy : ¬ Conn s t τ (s e) (t e)
  · by_cases h2 : Conn s t τ o (s e)
    · have hnot : ¬ Conn s t τ o (t e) := fun h3 => hxy ((conn_symm h2).trans h3)
      rw [quadMoment_diff_of_conn_left w hxy h2]
      unfold pivotalContribution
      rw [dite_eq_left hxy, dite_eq_left h2, dite_eq_right hnot]
      simp only [hqm]
      ring
    · by_cases h3 : Conn s t τ o (t e)
      · rw [quadMoment_diff_of_conn_right w hxy h3]
        unfold pivotalContribution
        rw [dite_eq_left hxy, dite_eq_right h2, dite_eq_left h3]
        simp only [hqm]
        ring
      · rw [quadMoment_diff_of_not_conn_both w h2 h3]
        unfold pivotalContribution
        rw [dite_eq_left hxy, dite_eq_right h2, dite_eq_right h3]
        ring
  · have hconn : Conn s t τ (s e) (t e) := not_not.mp hxy
    have hsame : quadMoment s t w o (insert e τ) = quadMoment s t w o τ := by
      simp only [quadMoment, spatialMoment, cluster_insert_of_conn hconn]
    rw [hsame, sub_self]
    unfold pivotalContribution
    rw [dite_eq_right hxy]

/-- **Russo's formula for the quadratic moment with the rooted pivotal
contribution.**  The derivative in `r` of `E_{β,r}[∑_{x∈K_o}⟨x,u⟩²]` is
`β|J'(r)|` times the sum over edges of the rooted pivotal contributions. -/
theorem hasDerivAt_expectation_quadMoment_rooted
    (s t : E → V) (w : V → ℝ) (o : V) (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ)
    {r β : ℝ} (hne : ∀ e, len e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
        (quadMoment s t w o))
      (β * K' * ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * pivotalContribution s t w o e τ) r := by
  rw [← pivotalSum_quadMoment_eq_pivotalContribution]
  exact hasDerivAt_expectation_spatialMoment s t (fun x => (w x) ^ 2) o len K K' hne hK

/-! ### First and second pivotal formulas at the level of expectations -/

/-- Russo's formula for the quadratic moment of the finite cutoff model: the
derivative is `β|J'(r)|` times the pivotal mass of the quadratic moment.  This
is `hasDerivAt_expectation_spatialMoment` for the weight `q x = (w x)²`. -/
theorem hasDerivAt_expectation_quadMoment
    (s t : E → V) (w : V → ℝ) (o : V) (len : E → ℝ) (K : ℝ → ℝ) (K' : ℝ)
    {r β : ℝ} (hne : ∀ e, len e ≠ r) (hK : HasDerivAt K (-K') r) :
    HasDerivAt
      (fun r' => expectation (fun e => longRangeEdgeProbability β (cutoffProfile K r' (len e)))
        (quadMoment s t w o))
      (β * K' * ∑ e ∈ (univ : Finset E).filter (fun e => len e ≤ r),
        ∑ τ ∈ (univ : Finset (Configuration E)).filter (fun τ => e ∉ τ),
          configurationLaw (fun e => longRangeEdgeProbability β (cutoffProfile K r (len e))) τ
            * (quadMoment s t w o (insert e τ) - quadMoment s t w o τ)) r :=
  hasDerivAt_expectation_spatialMoment s t (fun x => (w x) ^ 2) o len K K' hne hK

/-- **Second pivotal (pair-pivotal) formula for the quadratic moment.**  Along a
linear profile of edge probabilities the second derivative of the expectation of
the quadratic moment is the pair-pivotal double sum, with no diagonal term.
This is the second-order Russo identity specialised to `∑_{x∈K}⟨x,u⟩²`. -/
theorem secondDeriv_expectation_quadMoment (s t : E → V) (w : V → ℝ) (o : V)
    (p v : E → ℝ) (x : ℝ) :
    deriv (deriv fun u => expectation (fun e => p e + u * v e) (quadMoment s t w o)) x
      = ∑ e, ∑ f ∈ (univ : Finset E).erase e, v e * v f *
          pairPivotalMass (fun e => p e + x * v e) e f (quadMoment s t w o) :=
  deriv_deriv_expectation_add_mul p v (quadMoment s t w o) x

end PercLib.CriticalLRP.FiniteVolume

#print axioms PercLib.CriticalLRP.FiniteVolume.sq_sub_eq_trinomial
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_sq_sub_shift
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_sq_sub_shift_absolute
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_sum_sq_sub_cross
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_sum_sq_sub_cross_of_centred
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_sum_sq_pairEnergy_merge
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_flip_eq
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_flip_sub_of_not_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.centredMoment_flip_sub_of_not_conn
#print axioms PercLib.CriticalLRP.FiniteVolume.centredMoment_flip_trinomial
#print axioms PercLib.CriticalLRP.FiniteVolume.centredMoment_flip_absolute
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_far_decomposition
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_far_decomposition_relative
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_flip_eq_right
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_diff_of_conn_left
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_diff_of_conn_right
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_diff_of_not_conn_both
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_far_sub_centred
#print axioms PercLib.CriticalLRP.FiniteVolume.crossMoment_clusters
#print axioms PercLib.CriticalLRP.FiniteVolume.pairEnergy_merge_clusters
#print axioms PercLib.CriticalLRP.FiniteVolume.pairEnergy_merge_increment_of_centred
#print axioms PercLib.CriticalLRP.FiniteVolume.quadMoment_nonneg
#print axioms PercLib.CriticalLRP.FiniteVolume.centredMoment_nonneg
#print axioms PercLib.CriticalLRP.FiniteVolume.sum_sum_sq_nonneg
#print axioms PercLib.CriticalLRP.FiniteVolume.farMomentIfPivotal_eq_decomp
#print axioms PercLib.CriticalLRP.FiniteVolume.pivotalSum_quadMoment_eq_decomposition
#print axioms PercLib.CriticalLRP.FiniteVolume.pivotalContribution
#print axioms PercLib.CriticalLRP.FiniteVolume.pivotalSum_quadMoment_eq_pivotalContribution
#print axioms PercLib.CriticalLRP.FiniteVolume.hasDerivAt_expectation_quadMoment_rooted
#print axioms PercLib.CriticalLRP.FiniteVolume.pivotalSum_quadMoment_eq_farMoment
#print axioms PercLib.CriticalLRP.FiniteVolume.hasDerivAt_expectation_quadMoment
#print axioms PercLib.CriticalLRP.FiniteVolume.secondDeriv_expectation_quadMoment
