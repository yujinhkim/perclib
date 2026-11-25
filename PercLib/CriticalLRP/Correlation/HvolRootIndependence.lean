/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Root-independence of the per-site volume expectation: discharging `hvol`

Source: T. Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1),
Lemma I.2.1 / Lemma I.5.8.  Audited against
`.scratch/i52/source/Zd_renormalizationHD.tex` lines 2770-2830 (the last display of
`eq:x12_derivative` and the two displayed remainder estimates that follow it) and
`Correlation/Hrest.lean` sections 8 (`hvol` hypothesis).

## What the paper does

The two displayed remainder estimates of the proof of Lemma I.5.8 are written with
`\E_r |K|` in **both** factors of the main term:

  `|(\E_r|K|)^2 sum_{y in B_r} q_y - \E_r[|K| sum_{y in B_r} 1(y notin K)|K_y| q_y]|`
  `  <= sum_{y in B_r} q_y \E_r[|K|^2 1(y in K)]`,

  `| |B_r| (\E_r|K|)(\E_r S(K)) - \E_r[S(K) sum_{y in B_r} 1(y notin K)|K_y|] |`
  `  <= \E_r[|K||K cap B_r| S(K)]`,

where `K` is the cluster of the origin, `K_y` the cluster of `y`, and
`S(K) = sum_{x in K} <x,u>^2`.  The step from the per-site form (which is what
BK/FKG actually gives, and what `Correlation/Hrest.lean` proves) to these
displays uses exactly two symmetry facts:

* `\E_r |K_y| = \E_r |K|` for every `y`  (called `hvol` in `Correlation/Hrest.lean`);
* `S(K)` is a functional of the cluster of the **origin** only, so the factor
  `\E_r S(K)` does not depend on `y` and summing over `y in B_r` produces the
  factor `|B_r|`.

The first is translation invariance of the law on `Z^d`; the second is *not*
root-independence of a spatial expectation but the trivial fact that the same
cluster enters every term.  See section 8 below for the exact statement, and for
the sharp observation that the quadratic weight `q z = <z,u>^2` is **not**
translation invariant, so `\E S(K_y)` genuinely depends on `y`; what survives is
the covariance identity `\E S(K_y) = \E [S(K_0) shifted by y]`.

## What is proved here

For the canonical independent-edge model `Config V = Set (Sym2 V)` with the
genuine product law `edgeMeasure π` and `cardFun` the extended cluster
cardinality (value `⊤` on infinite clusters):

* `cardFun_image_of_injective` / `cardFun_image_equiv` / `cardFun_image_add`:
  `cardFun (t '' S) = cardFun S` for an injective `t`; in particular the
  `cardFun (Set.image t S) = cardFun S` equivalence.
* `lintegral_comp_of_map_eq`: the `lintegral` reindexing behind every
  "translation invariance of the law" argument.
* `lintegral_cardFun_root_indep`: the abstract root-independence statement — its
  only inputs are (i) `μ.map T = μ` and (ii) cluster covariance
  `cluster (T ω) (e v) = e '' cluster ω v`.  Both are hypotheses with names
  here; both are *discharged* in the next item for the lattice model.
* `hvol_cardFun`: **`hvol` is proved** on `Z^d` for any translation-invariant
  edge probability `π`, from `edgeMeasure_shift_invariant` and
  `cluster_shiftConfig`.  Also its `toReal` form `hvol_cardFun_toReal`.
* `hrest_site_real_shift`, `h2_site_real_shift`: the per-site displays of
  `Correlation/Hrest.lean` with the `hvol` **argument removed** and the
  translation-invariance hypothesis `hπshift` supplying it.
* `sum_lintegral_cardFun`: the "repeated mean" identity
  `sum_{y in B} \E |K_y| = |B| * \E |K_o|` — the origin of the factor `|B_r|`.
* `spatFun_image_equiv`, `spatFun_image_add`, `lintegral_spatFun_root_indep`,
  `spatFun_covariance`: exact covariance of the spatial moment, and
  root-independence when the weight *is* translation invariant.

## Scope, stated exactly

Model: **canonical** independent percolation on `Sym2 (Fin d -> Z)` with the
product law `edgeMeasure π` (`CountableProduct`), not an abstract weighted model.
Everything here is about that model.

Companion files:
* `HvolPermutation.lean` replaces the translation of `Z^d` by an arbitrary
  vertex permutation `g` with `π (Sym2.map g e) = π e`, and obtains `hvol` on
  `Fin d -> ZMod n` (the finite torus) with no further hypotheses.  The lattice
  theorem `hvol_cardFun` below is the special case `g = (· + a)`.
* `HvolWeightNotInvariant.lean` records that the paper's quadratic weight
  `q_u(z) = <z,u>^2` is *not* translation invariant, so the spatial
  root-independence lemma `hspat_shift` below does not apply to `S(K)`; the
  covariance identity `spatFun_covariance` is what is available.

Still needed as input (not discharged here, and not implied by symmetry):
`hx : \int cardFun (cluster . x) != ⊤` (finiteness of the expected cluster
volume — the sharpness/HD input) and, for BK, `π e < 1` with a fixed edge
exhaustion `𝓔`.  No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.Hrest

set_option autoImplicit true

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP
namespace Hvol

variable {V : Type*} [Countable V]

/-! ## 1. `cardFun` is invariant under injective relabellings of the vertex set -/

/-- The extended cluster cardinality depends only on the cardinality: an injective
map of the vertex set carries `cardFun S` to `cardFun S`. -/
theorem cardFun_image_of_injective {W : Type*} {f : V → W} (hf : Function.Injective f)
    (S : Set V) : Percolation.cardFun (f '' S) = Percolation.cardFun S := by
  rcases S.finite_or_infinite with hS | hS
  · rw [Percolation.cardFun_eq_ncard (hS.image f), Percolation.cardFun_eq_ncard hS,
      Set.ncard_image_of_injective S hf]
  · rw [Percolation.cardFun_eq_top (hS.image hf.injOn), Percolation.cardFun_eq_top hS]

/-- The `cardFun (Set.image t S) = cardFun S` equivalence, for a bijection `t`. -/
theorem cardFun_image_equiv {W : Type*} (e : V ≃ W) (S : Set V) :
    Percolation.cardFun (e '' S) = Percolation.cardFun S :=
  cardFun_image_of_injective e.injective S

/-- Cluster cardinality is invariant under lattice translation of the vertex set. -/
theorem cardFun_image_add {d : ℕ} (a : Fin d → ℤ) (S : Set (Fin d → ℤ)) :
    Percolation.cardFun ((fun u => u + a) '' S) = Percolation.cardFun S :=
  cardFun_image_of_injective (fun _ _ h => by simpa using h) S

/-! ## 2. Reindexing a `lintegral` along a measure-preserving map -/

/-- `lintegral` reindexing: the content of "the law is translation invariant". -/
theorem lintegral_comp_of_map_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : α → α} (hT : Measurable T) (hinv : μ.map T = μ) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ a, f (T a) ∂μ = ∫⁻ a, f a ∂μ := by
  rw [← lintegral_map hf hT, hinv]

/-! ## 3. The abstract root-independence statement

Nothing here uses more than measure preservation and cluster covariance; this is
the exact pair of premises that a torus or any other stationary model has to
supply. -/

/-- **Root independence of the expected cluster cardinality.**  If `T` preserves
`μ` and clusters transform covariantly under `T` and the vertex bijection `e`,
then `E|K_{e v}| = E|K_v|`. -/
theorem lintegral_cardFun_root_indep (μ : Measure (Config V)) {T : Config V → Config V}
    (hT : Measurable T) (hinv : μ.map T = μ) {e : V → V} (he : Function.Injective e)
    (hcov : ∀ ω v, cluster (T ω) (e v) = e '' cluster ω v) (v : V) :
    ∫⁻ ω, Percolation.cardFun (cluster ω (e v)) ∂μ
      = ∫⁻ ω, Percolation.cardFun (cluster ω v) ∂μ := by
  have h1 : ∫⁻ ω, Percolation.cardFun (cluster (T ω) (e v)) ∂μ
      = ∫⁻ ω, Percolation.cardFun (cluster ω (e v)) ∂μ :=
    lintegral_comp_of_map_eq hT hinv (Hrest.measurable_cardFun_cluster_canonical (e v))
  rw [← h1]
  refine lintegral_congr fun ω => ?_
  rw [hcov ω v]
  exact cardFun_image_of_injective he (cluster ω v)

/-! ## 4. The lattice translation group and cluster covariance -/

/-- Translation of lattice sites by `a`, as a permutation.  Written out (rather
than using `Equiv.addRight`) so that `siteShift a u` is definitionally `u + a`. -/
noncomputable def siteShift {d : ℕ} (a : Fin d → ℤ) : Equiv.Perm (Fin d → ℤ) where
  toFun u := u + a
  invFun u := u - a
  left_inv u := by simp
  right_inv u := by simp

@[simp] theorem siteShift_apply {d : ℕ} (a u : Fin d → ℤ) : siteShift a u = u + a := rfl

theorem siteShift_image {d : ℕ} (a : Fin d → ℤ) (S : Set (Fin d → ℤ)) :
    (siteShift a : (Fin d → ℤ) → (Fin d → ℤ)) '' S = (fun u => u + a) '' S := rfl

/-- `hvol` on `Z^d`: for a translation-invariant edge probability, the expected
extended cluster cardinality does not depend on the root.

This is the hypothesis `hvol` of `Correlation/Hrest.hrest_site_real` and
`Correlation/Hrest.h2_site_real`, proved rather than assumed. -/
theorem hvol_cardFun {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπ : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), π (Sym2.map (fun x => x + a) e) = π e)
    (x y : Fin d → ℤ) :
    ∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
      = ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π) := by
  have hcov : ∀ (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ),
      cluster (shiftConfig (y - x) ω) ((fun u => u + (y - x)) v)
        = (fun u => u + (y - x)) '' cluster ω v := by
    intro ω v
    exact cluster_shiftConfig (y - x) ω v
  have h := lintegral_cardFun_root_indep (edgeMeasure π) (measurable_shiftConfig (y - x))
    (edgeMeasure_shift_invariant π hπ (y - x)) (e := fun u => u + (y - x))
    (fun _ _ h => by simpa using h) hcov x
  have hxy : x + (y - x) = y := by
    funext i
    simp
  simpa only [hxy] using h

/-- The real form of `hvol`, i.e. the exact shape in which `hrest_site_real`
uses it (the finiteness of the first moment is *not* consumed by this identity). -/
theorem hvol_cardFun_toReal {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπ : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), π (Sym2.map (fun x => x + a) e) = π e)
    (x y : Fin d → ℤ) :
    (∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)).toReal
      = (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal := by
  rw [hvol_cardFun hπ x y]

/-! ## 5. The per-site remainder estimates with `hvol` discharged

`Correlation/Hrest.hrest_site_real` and `h2_site_real` each take the symmetry
`hvol` as a hypothesis; the versions below replace it by translation invariance
of `π`. -/

/-- The paper's `hrest` display (both main-term factors `E|K|`), for a
translation-invariant `π`, with `hvol` proved in `hvol_cardFun`. -/
theorem hrest_site_real_shift {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (hπ : ∀ e, π e < 1) (x y : Fin d → ℤ) (𝓔 : ℕ → Finset (Sym2 (Fin d → ℤ)))
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ 𝓔 n)
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal ^ 2
      - (∫⁻ ω, {ω : Config (Fin d → ℤ) | ¬ Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal :=
  Hrest.hrest_site_real (V := Fin d → ℤ) hπ x y 𝓔 h𝓔mono h𝓔
    (hvol_cardFun hπshift x y) hx hc

/-- The paper's `h2` display (spatial moment `S(K)` against `E|K|`), for a
translation-invariant `π`, with `hvol` proved in `hvol_cardFun`. -/
theorem h2_site_real_shift {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (hπ : ∀ e, π e < 1) (x y : Fin d → ℤ) (𝓔 : ℕ → Finset (Sym2 (Fin d → ℤ)))
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ 𝓔 n)
    (q : (Fin d → ℤ) → ℝ≥0∞)
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hq : (∫⁻ ω, Hrest.spatFun q (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal *
        (∫⁻ ω, Hrest.spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal
      - (∫⁻ ω, {ω : Config (Fin d → ℤ) | ¬ Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal :=
  Hrest.h2_site_real (V := Fin d → ℤ) hπ x y 𝓔 h𝓔mono h𝓔 q
    (hvol_cardFun hπshift x y) hx hq hc

/-! ## 6. The repeated mean: summing the per-site volume over a window

This is where the factor `|B_r|` of the paper's second display comes from. -/

/-- **Repeated mean.**  Summing `E|K_y|` over a finite window `B` multiplies the
per-site value by `|B|`.  This is the identity that converts the per-site
estimate `h2_site_real` into the paper's display
`|B_r| (E_r|K|) (E_r S(K)) - ...`. -/
theorem sum_lintegral_cardFun {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπ : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), π (Sym2.map (fun x => x + a) e) = π e)
    (B : Finset (Fin d → ℤ)) (o : Fin d → ℤ) :
    ∑ y ∈ B, ∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
      = (B.card : ℝ≥0∞) * ∫⁻ ω, Percolation.cardFun (cluster ω o) ∂(edgeMeasure π) := by
  rw [Finset.sum_congr rfl (fun y _ => hvol_cardFun hπ o y), Finset.sum_const, nsmul_eq_mul]

/-- The same identity at the level of the real main term `(E|K|)(E S(K))` of the
paper's display, summed over the window. -/
theorem sum_cardFun_mul_spatFun {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπ : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), π (Sym2.map (fun x => x + a) e) = π e)
    (B : Finset (Fin d → ℤ)) (o : Fin d → ℤ) (q : (Fin d → ℤ) → ℝ≥0∞) :
    ∑ y ∈ B, ((∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)).toReal
        * (∫⁻ ω, Hrest.spatFun q (cluster ω o) ∂(edgeMeasure π)).toReal)
      = (B.card : ℝ) *
        ((∫⁻ ω, Percolation.cardFun (cluster ω o) ∂(edgeMeasure π)).toReal
          * (∫⁻ ω, Hrest.spatFun q (cluster ω o) ∂(edgeMeasure π)).toReal) := by
  have hterm : ∀ y ∈ B, ((∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)).toReal
      * (∫⁻ ω, Hrest.spatFun q (cluster ω o) ∂(edgeMeasure π)).toReal)
      = ((∫⁻ ω, Percolation.cardFun (cluster ω o) ∂(edgeMeasure π)).toReal
        * (∫⁻ ω, Hrest.spatFun q (cluster ω o) ∂(edgeMeasure π)).toReal) := by
    intro y _
    rw [hvol_cardFun hπ o y]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-! ## 7. The spatial moment: exact covariance, and root-independence when the
weight is translation invariant -/

/-- The indicator computation behind every "reindex the spatial moment" step. -/
theorem indicator_image_apply {W : Type*} (e : V ≃ W) (S : Set V) (w : V) :
    (e '' S).indicator (fun _ => (1 : ℝ≥0∞)) (e w) = S.indicator (fun _ => (1 : ℝ≥0∞)) w := by
  have hmem : e w ∈ e '' S ↔ w ∈ S := by
    constructor
    · rintro ⟨u, hu, h⟩
      rwa [e.injective h] at hu
    · intro hw
      exact ⟨w, hw, rfl⟩
  by_cases hw : w ∈ S
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hmem.mpr hw)]
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (hmem.mp h))]

/-- **Covariance of the spatial moment** under a relabelling `e` of vertices. -/
theorem spatFun_image_equiv {W : Type*} (e : V ≃ W) (q : W → ℝ≥0∞) (S : Set V) :
    Hrest.spatFun q (e '' S) = Hrest.spatFun (fun v => q (e v)) S := by
  simp only [Hrest.spatFun]
  rw [← Equiv.tsum_eq e (fun z => q z * (e '' S).indicator (fun _ => (1 : ℝ≥0∞)) z)]
  exact tsum_congr fun w => by rw [indicator_image_apply]

/-- The same, for a lattice translation. -/
theorem spatFun_image_add {d : ℕ} (a : Fin d → ℤ) (q : (Fin d → ℤ) → ℝ≥0∞)
    (S : Set (Fin d → ℤ)) :
    Hrest.spatFun q ((fun u => u + a) '' S) = Hrest.spatFun (fun w => q (w + a)) S :=
  spatFun_image_equiv (siteShift a) q S

/-- **Root independence of the expected spatial moment**, when the weight is
invariant under the relabelling: `E S(K_{e v}) = E S(K_v)`. -/
theorem lintegral_spatFun_root_indep (μ : Measure (Config V)) {T : Config V → Config V}
    (hT : Measurable T) (hinv : μ.map T = μ) {e : V ≃ V}
    (hcov : ∀ ω v, cluster (T ω) (e v) = e '' cluster ω v)
    (q : V → ℝ≥0∞) (hq : ∀ v, q (e v) = q v) (v : V) :
    ∫⁻ ω, Hrest.spatFun q (cluster ω (e v)) ∂μ
      = ∫⁻ ω, Hrest.spatFun q (cluster ω v) ∂μ := by
  have h1 : ∫⁻ ω, Hrest.spatFun q (cluster (T ω) (e v)) ∂μ
      = ∫⁻ ω, Hrest.spatFun q (cluster ω (e v)) ∂μ :=
    lintegral_comp_of_map_eq hT hinv (Hrest.measurable_spatFun_cluster q (e v))
  rw [← h1]
  refine lintegral_congr fun ω => ?_
  rw [hcov ω v, spatFun_image_equiv e q (cluster ω v)]
  exact tsum_congr fun w => by simp only [hq]

/-- Root independence of the expected spatial moment for a translation-invariant
weight on `Z^d`. -/
theorem hspat_shift {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (q : (Fin d → ℤ) → ℝ≥0∞) (hq : ∀ (a w : Fin d → ℤ), q (w + a) = q w)
    (x y : Fin d → ℤ) :
    ∫⁻ ω, Hrest.spatFun q (cluster ω y) ∂(edgeMeasure π)
      = ∫⁻ ω, Hrest.spatFun q (cluster ω x) ∂(edgeMeasure π) := by
  have hcov : ∀ (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ),
      cluster (shiftConfig (y - x) ω) (siteShift (y - x) v)
        = siteShift (y - x) '' cluster ω v := by
    intro ω v
    rw [siteShift_apply, siteShift_image]
    exact cluster_shiftConfig (y - x) ω v
  have h := lintegral_spatFun_root_indep (edgeMeasure π) (measurable_shiftConfig (y - x))
    (edgeMeasure_shift_invariant π hπshift (y - x)) hcov q
    (fun v => hq (y - x) v) x
  have hxy : siteShift (y - x) x = y := by
    rw [siteShift_apply]
    funext i
    simp
  simpa only [hxy] using h

/-- **The exact replacement when the weight is *not* translation invariant**
(which is the case for the paper's `q z = <z,u>^2`): the expectation of the
spatial moment of the cluster of `x + a` is the expectation of the spatially
*shifted* moment of the cluster of `x`.  Root independence of `E S(K_y)` itself
is false for the quadratic weight; this identity is what is actually available,
and it is why the paper keeps `S(K)` attached to the cluster of the origin and
only ever translates `K_y` inside the volume factor. -/
theorem spatFun_covariance {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (q : (Fin d → ℤ) → ℝ≥0∞) (x a : Fin d → ℤ) :
    ∫⁻ ω, Hrest.spatFun q (cluster ω (x + a)) ∂(edgeMeasure π)
      = ∫⁻ ω, Hrest.spatFun (fun w => q (w + a)) (cluster ω x) ∂(edgeMeasure π) := by
  have h1 : ∫⁻ ω, Hrest.spatFun q (cluster (shiftConfig a ω) (x + a)) ∂(edgeMeasure π)
      = ∫⁻ ω, Hrest.spatFun q (cluster ω (x + a)) ∂(edgeMeasure π) :=
    lintegral_comp_of_map_eq (measurable_shiftConfig a) (edgeMeasure_shift_invariant π hπshift a)
      (Hrest.measurable_spatFun_cluster q (x + a))
  rw [← h1]
  refine lintegral_congr fun ω => ?_
  rw [cluster_shiftConfig a ω x, spatFun_image_add]

/-- The spatial moment of a translated cluster, pointwise: this is the exact
sense in which `S` is *not* root independent. -/
theorem spatFun_translate_pointwise {d : ℕ} (q : (Fin d → ℤ) → ℝ≥0∞) (a : Fin d → ℤ)
    (ω : Config (Fin d → ℤ)) (v : Fin d → ℤ) :
    Hrest.spatFun q (cluster (shiftConfig a ω) (v + a))
      = Hrest.spatFun (fun w => q (w + a)) (cluster ω v) := by
  rw [cluster_shiftConfig a ω v, spatFun_image_add]

/-! ## 8. Windowed assembly: from the per-site estimates to the paper's displays

`Correlation/Hrest.lean` proves the per-site estimates; the paper writes them
summed over `y in B_r` with the factor `|B_r|` in front of the main term.  The
two lemmas here are the exact finite-sum bookkeeping for that step; the second
half of section 9 discharges `hvol` inside the summand. -/

/-- **Generic windowed assembly.**  If a per-site bound `|A - b y| <= c y` holds
for every `y` in a finite window with `A` independent of `y`, then the
`w`-weighted sums satisfy the same bound with `sum w y` times `A` in front. -/
theorem abs_sum_weighted_le {ι : Type*} (B : Finset ι) (w : ι → ℝ) (A : ℝ)
    (b c : ι → ℝ) (hw : ∀ y ∈ B, 0 ≤ w y) (h : ∀ y ∈ B, |A - b y| ≤ c y) :
    |(∑ y ∈ B, w y) * A - ∑ y ∈ B, w y * b y| ≤ ∑ y ∈ B, w y * c y := by
  have hEq : (∑ y ∈ B, w y) * A - ∑ y ∈ B, w y * b y = ∑ y ∈ B, w y * (A - b y) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hEq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
  rw [abs_mul, abs_of_nonneg (hw y hy)]
  exact mul_le_mul_of_nonneg_left (h y hy) (hw y hy)

/-- The unweighted (`w = 1`) special case: the `|B|` factor appears in front. -/
theorem abs_sum_le_sum_of_per_site {ι : Type*} (B : Finset ι) (A : ℝ) (b c : ι → ℝ)
    (h : ∀ y ∈ B, |A - b y| ≤ c y) :
    |(B.card : ℝ) * A - ∑ y ∈ B, b y| ≤ ∑ y ∈ B, c y := by
  have h' := abs_sum_weighted_le B (fun _ => (1 : ℝ)) A b c (fun _ _ => zero_le_one) h
  simpa using h'

/-! ## 9. The canonical windowed displays with `hvol` discharged -/

/-- **The paper's first displayed remainder estimate** of Lemma I.5.8, summed over
the window, in the canonical model and for a translation-invariant `π`:

`|(sum_{y in B} w y) (E|K|)^2 - sum_{y in B} w y E[1(0 not~ y) |K| |K_y|]|`
`  <= sum_{y in B} w y E[1(0 ~ y) |K|^2]`,

with `w y = <y,u>^2` in the paper (any nonnegative `w` works).  No symmetry
hypothesis: `hvol` is used only inside `hrest_site_real_shift`. -/
theorem volume_window_display {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (hπ : ∀ e, π e < 1) (x : Fin d → ℤ) (𝓔 : ℕ → Finset (Sym2 (Fin d → ℤ)))
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ 𝓔 n)
    (B : Finset (Fin d → ℤ)) (w : (Fin d → ℤ) → ℝ) (hw : ∀ y ∈ B, 0 ≤ w y)
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : ∀ y ∈ B, (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(∑ y ∈ B, w y) *
        (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal ^ 2
      - ∑ y ∈ B, w y *
        (∫⁻ ω, {ω : Config (Fin d → ℤ) | ¬ Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ ∑ y ∈ B, w y *
        (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal :=
  abs_sum_weighted_le B w _ _ _ hw fun y hy =>
    hrest_site_real_shift hπshift hπ x y 𝓔 h𝓔mono h𝓔 hx (hc y hy)

/-- **The paper's second displayed remainder estimate** of Lemma I.5.8, summed
over the window, in the canonical model and for a translation-invariant `π`:

`| |B| (E|K|)(E S(K)) - sum_{y in B} E[1(0 not~ y) S(K) |K_y|]|`
`  <= sum_{y in B} E[1(0 ~ y) S(K) |K|]`.

The factor `|B|` in front of the main term is exactly the repeated mean
`sum_{y in B} E|K_y| = |B| E|K|` (theorem `sum_lintegral_cardFun`), which is
what `hvol` supplies.  The right-hand side is identified with
`E[|K ∩ B| |K| S(K)]` in `mass_window_display_canonical`. -/
theorem mass_window_display {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (hπ : ∀ e, π e < 1) (x : Fin d → ℤ) (𝓔 : ℕ → Finset (Sym2 (Fin d → ℤ)))
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ 𝓔 n)
    (B : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ≥0∞)
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hq : (∫⁻ ω, Hrest.spatFun q (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : ∀ y ∈ B, (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤) :
    |(B.card : ℝ) *
        ((∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal *
          (∫⁻ ω, Hrest.spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal)
      - ∑ y ∈ B,
        (∫⁻ ω, {ω : Config (Fin d → ℤ) | ¬ Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ ∑ y ∈ B,
        (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
          ∂(edgeMeasure π)).toReal :=
  abs_sum_le_sum_of_per_site B _ _ _ fun y hy =>
    h2_site_real_shift hπshift hπ x y 𝓔 h𝓔mono h𝓔 q hx hq (hc y hy)

/-- Counting: the number of sites of the window connected to `x` is the
cardinality of `K_x ∩ B`. -/
theorem sum_conn_indicator_eq_cardFun {d : ℕ} (x : Fin d → ℤ) (B : Finset (Fin d → ℤ))
    (ω : Config (Fin d → ℤ)) :
    ∑ y ∈ B, ({ω' : Config (Fin d → ℤ) | Connects ω' x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω)
      = Percolation.cardFun (cluster ω x ∩ (B : Set (Fin d → ℤ))) := by
  classical
  have hcoe : ((B.filter (fun y => Connects ω x y) : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))
      = cluster ω x ∩ (B : Set (Fin d → ℤ)) := by
    ext y
    rw [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe,
      mem_cluster_iff, and_comm]
  have hfin : (cluster ω x ∩ (B : Set (Fin d → ℤ))).Finite :=
    (B.finite_toSet).subset Set.inter_subset_right
  have hcard : (cluster ω x ∩ (B : Set (Fin d → ℤ))).ncard
      = (B.filter (fun y => Connects ω x y)).card := by
    rw [← hcoe, Set.ncard_coe_finset]
  have hstep : ∀ y : Fin d → ℤ,
      ({ω' : Config (Fin d → ℤ) | Connects ω' x y}.indicator (fun _ => (1 : ℝ≥0∞)) ω)
        = if Connects ω x y then (1 : ℝ≥0∞) else 0 := by
    intro y
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_congr rfl (fun y _ => hstep y), Finset.sum_boole,
    Percolation.cardFun_eq_ncard hfin, hcard]

/-- Finite linearity: the sum over the window of the connection terms is the
expectation of `|K_x ∩ B|` times the observable. -/
theorem sum_lintegral_conn {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (f : Config (Fin d → ℤ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∑ y ∈ B, ∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω * f ω ∂(edgeMeasure π)
      = ∫⁻ ω, Percolation.cardFun (cluster ω x ∩ (B : Set (Fin d → ℤ))) * f ω
          ∂(edgeMeasure π) := by
  classical
  rw [← lintegral_finsetSum]
  · refine lintegral_congr fun ω => ?_
    rw [← Finset.sum_mul, sum_conn_indicator_eq_cardFun]
  · intro y _
    exact (measurable_const.indicator (measurableSet_connects x y)).mul hf

/-- **The paper's second remainder estimate, in its printed summed form**, with
the right-hand side identified as `E[|K ∩ B| |K| S(K)]`.  This is the display

`| |B| (E|K|)(E S(K)) - E[S(K) sum_{y in B} 1(y notin K) |K_y|] |`
`  <= E[|K| |K ∩ B| S(K)]`

of Lemma I.5.8 (with the disconnection term written as a per-site sum, which is
the same object by finite linearity) in the canonical model, for
translation-invariant `π`, with `hvol` proved rather than assumed. -/
theorem mass_window_display_canonical {d : ℕ} {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (hπ : ∀ e, π e < 1) (x : Fin d → ℤ) (𝓔 : ℕ → Finset (Sym2 (Fin d → ℤ)))
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ 𝓔 n)
    (B : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ≥0∞)
    (hx : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hq : (∫⁻ ω, Hrest.spatFun q (cluster ω x) ∂(edgeMeasure π)) ≠ ⊤)
    (hc : ∀ y ∈ B, (∫⁻ ω, {ω : Config (Fin d → ℤ) | Connects ω x y}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
        ∂(edgeMeasure π)) ≠ ⊤)
    :
    |(B.card : ℝ) *
        ((∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)).toReal *
          (∫⁻ ω, Hrest.spatFun q (cluster ω x) ∂(edgeMeasure π)).toReal)
      - ∑ y ∈ B,
        (∫⁻ ω, {ω : Config (Fin d → ℤ) | ¬ Connects ω x y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω *
          (Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω y))
          ∂(edgeMeasure π)).toReal|
      ≤ (∫⁻ ω, Percolation.cardFun (cluster ω x ∩ (B : Set (Fin d → ℤ))) *
          (Percolation.cardFun (cluster ω x) * Hrest.spatFun q (cluster ω x))
          ∂(edgeMeasure π)).toReal := by
  refine (mass_window_display hπshift hπ x 𝓔 h𝓔mono h𝓔 B q hx hq hc).trans (le_of_eq ?_)
  rw [← ENNReal.toReal_sum hc]
  congr 1
  rw [sum_lintegral_conn x B
    (fun ω => Hrest.spatFun q (cluster ω x) * Percolation.cardFun (cluster ω x))
    ((Hrest.measurable_spatFun_cluster q x).mul
      (Hrest.measurable_cardFun_cluster_canonical x))]
  refine lintegral_congr fun ω => ?_
  ring

/-! ## 10. Non-vacuity: `hvol` holds in the paper's own model

The translation-invariance hypothesis `hπshift` is not an artefact: it is
satisfied by the law `P_β` of §I.1.2 itself, so `hvol` is *unconditional* in that
model (no hypothesis on `β`, `α`, `d`). -/

/-- `hvol` for the paper's law `P_β = latticeLongRangeMeasure d α β`
(`J(x,y) = |x-y|^{-d-α}`), with no hypotheses left. -/
theorem hvol_cardFun_latticeLongRange (d : ℕ) (α : ℝ) (β : NNReal)
    (x y : Fin d → ℤ) :
    ∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(latticeLongRangeMeasure d α β)
      = ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(latticeLongRangeMeasure d α β) :=
  hvol_cardFun (bernoulliEdgeProb_shift (lrKernel_shift_invariant d α)
    (lrKernel_nonneg d α) β) x y

/-- The repeated-mean identity in the paper's model. -/
theorem sum_lintegral_cardFun_latticeLongRange (d : ℕ) (α : ℝ) (β : NNReal)
    (B : Finset (Fin d → ℤ)) (o : Fin d → ℤ) :
    ∑ y ∈ B, ∫⁻ ω, Percolation.cardFun (cluster ω y) ∂(latticeLongRangeMeasure d α β)
      = (B.card : ℝ≥0∞) *
        ∫⁻ ω, Percolation.cardFun (cluster ω o) ∂(latticeLongRangeMeasure d α β) :=
  sum_lintegral_cardFun (bernoulliEdgeProb_shift (lrKernel_shift_invariant d α)
    (lrKernel_nonneg d α) β) B o

end Hvol
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Hvol.cardFun_image_of_injective
#print axioms PercLib.CriticalLRP.Hvol.cardFun_image_equiv
#print axioms PercLib.CriticalLRP.Hvol.cardFun_image_add
#print axioms PercLib.CriticalLRP.Hvol.lintegral_comp_of_map_eq
#print axioms PercLib.CriticalLRP.Hvol.lintegral_cardFun_root_indep
#print axioms PercLib.CriticalLRP.Hvol.hvol_cardFun
#print axioms PercLib.CriticalLRP.Hvol.hvol_cardFun_toReal
#print axioms PercLib.CriticalLRP.Hvol.hrest_site_real_shift
#print axioms PercLib.CriticalLRP.Hvol.h2_site_real_shift
#print axioms PercLib.CriticalLRP.Hvol.sum_lintegral_cardFun
#print axioms PercLib.CriticalLRP.Hvol.sum_cardFun_mul_spatFun
#print axioms PercLib.CriticalLRP.Hvol.indicator_image_apply
#print axioms PercLib.CriticalLRP.Hvol.spatFun_image_equiv
#print axioms PercLib.CriticalLRP.Hvol.spatFun_image_add
#print axioms PercLib.CriticalLRP.Hvol.lintegral_spatFun_root_indep
#print axioms PercLib.CriticalLRP.Hvol.hspat_shift
#print axioms PercLib.CriticalLRP.Hvol.spatFun_covariance
#print axioms PercLib.CriticalLRP.Hvol.spatFun_translate_pointwise
#print axioms PercLib.CriticalLRP.Hvol.abs_sum_weighted_le
#print axioms PercLib.CriticalLRP.Hvol.abs_sum_le_sum_of_per_site
#print axioms PercLib.CriticalLRP.Hvol.volume_window_display
#print axioms PercLib.CriticalLRP.Hvol.mass_window_display
#print axioms PercLib.CriticalLRP.Hvol.sum_conn_indicator_eq_cardFun
#print axioms PercLib.CriticalLRP.Hvol.sum_lintegral_conn
#print axioms PercLib.CriticalLRP.Hvol.mass_window_display_canonical
#print axioms PercLib.CriticalLRP.Hvol.hvol_cardFun_latticeLongRange
#print axioms PercLib.CriticalLRP.Hvol.sum_lintegral_cardFun_latticeLongRange
