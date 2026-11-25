/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m2/I417B/Defs.lean ; module path rewritten only.
-/

/-
# Lemma I.4.17, `p = 2`, `q = 1`: the two-copy events of the restored coupling

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (p. 45), and its printed `p = 2, q = 1` display

  `E|K|² E|K| − E[|Kx|² |Ky| 1(x ↮ y)] ≤ T³(x,y) (E|K|)⁴ + 2 T⁴(x,y) (E|K|)³`.

The printed proof reads `Ky` as the cluster of `y` in the **base** configuration `ω` and claims
`Ky ⊆ K̃y` on `{y ∉ Kx}` for the restored configuration `ω̃`; that inclusion is false
(`Correlation/PrintedEventFails.lean`, `not_cluster_subset_forceOn_compl`), and the printed
identity `P(x₁,…,x_p ∈ Kx, y₁,…,y_q ∈ K̃y) = P(x₁…∈Kx) P(y₁…∈K̃y)` hides an unjustified
resampling step.

The repair used here is the one that already fixes Lemma I.4.12 in this repository
(`Correlation/TwoClusterGap.lean`, `Correlation/I411/ApartGap.lean`): keep the printed coupling
`ω̃ = restoreMap x (ω₂, ω₁) = forceOn (touchSet ω₁ x)ᶜ ω₂ ω₁` (base `ω₁` on the edges touching
its cluster `Kx(ω₁)`, fresh `ω₂` elsewhere) and read the cluster of `y` as the **restored**
cluster `K̃y = Ky(ω̃)`, whose membership is *exactly* characterised by
`mem_cluster_forceOn_compl_iff`:

  `y ∉ Kx(ω₁) → (y₁ ∈ K̃y ↔ ∃ an ω₂-open walk y → y₁ with all vertices outside Kx(ω₁))`.

With this reading the printed dichotomy "either `y ∈ Kx` or some `yᵢ ∉ Ky`" becomes the
**provable** dichotomy recorded in `I417B/Cover.lean`:

* `x₁, x₂ ∈ Kx(ω₁)` and `y₁ ∈ Ky(ω₂)` (the two independent copies),
* and *not* the restored configuration satisfying `y ∉ Kx` and `y₁ ∈ K̃y`
  (the "diagonal" case, whose measure is the excluded moment `E[|Kx|² |Ky| 1(x↮y)]`),

then either

* `y ∈ Kx(ω₁)` — the `yInSet` alternative, with the *base* cluster containing all three of
  `x₁, x₂, y`; or
* `y ∉ Kx(ω₁)`, `y₁ ∉ K̃y`, and then every `ω₂`-walk from `y` to `y₁` meets the base cluster
  `Kx(ω₁)`, so some marked vertex `w ∈ Kx(ω₁)` lies on a simple `ω₂`-path from `y` to `y₁`
  (`exists_fresh_disjOcc_of_no_avoid`).  Writing the mark as the disjoint occurrence
  `{y↔w} ∘ {w↔y₁}` inside the fresh copy is exactly what makes the two copies independent:
  the base condition is `x₁, x₂, w ∈ Kx(ω₁)`, the fresh condition is `{y↔w} ∘ {w↔y₁}`.

Everything is stated on `Config V × Config V` with the **first** coordinate fresh (`ω₂`) and the
**second** base (`ω₁`), matching `restoreMap o (ω₂, ω₁)`.

No `sorry`, no custom axioms; definitions only in this file.
-/
module

public import PercLib.CriticalLRP.Correlation.I411.ApartGap

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The two independent copies.  `ω₂` is the fresh configuration, `ω₁` the base one. -/
abbrev TwoCopy (V : Type*) := Config V × Config V

/-- **The product event**: `y₁` lies in the cluster of `y` in the fresh configuration and `x₁`,
`x₂` lie in the cluster of `x` in the base configuration.  Its `μ ⊗ μ`-measure is
`P(y₁ ∈ Ky) · P(x₁,x₂ ∈ Kx)`, a product of two one-copy events, one per copy. -/
def prodSet (x y x₁ x₂ y₁ : V) : Set (TwoCopy V) :=
  connSet y y₁ ×ˢ (connSet x x₁ ∩ connSet x x₂)

/-- **The diagonal event.**  Both `x₁` and `x₂` lie in the base cluster of `x`, `y` lies
*outside* it, and `y₁` lies in the cluster of `y` in the **restored** configuration
`restoreMap x (ω₂,ω₁)`.  Since `Kx(ω̃) = Kx(ω₁)` exactly and `x ↮ y` in `ω̃` is `y ∉ Kx(ω₁)`,
the `μ ⊗ μ`-measure of this event is the excluded moment `E[|Kx|² |Ky| 1(x ↮ y)]`
(`I417B/Measure.lean`, `tsum_diagSet`). -/
def diagSet (x y x₁ x₂ y₁ : V) : Set (TwoCopy V) :=
  {p | p.2 ∈ connSet x x₁ ∩ connSet x x₂ ∧ p.2 ∉ connSet x y ∧
    restoreMap x p ∈ connSet y y₁}

/-- **The `y ∈ Kx` alternative**: the base cluster of `x` contains `y` as well as `x₁, x₂`,
while the fresh copy still connects `y` to `y₁`. -/
def yInSet (x y x₁ x₂ y₁ : V) : Set (TwoCopy V) :=
  connSet y y₁ ×ˢ (connSet x x₁ ∩ connSet x x₂ ∩ connSet x y)

/-- **The marked crossing alternative** at `w`: the base cluster of `x` contains `x₁, x₂` and the
mark `w`, and in the fresh copy the two walks `y → w` and `w → y₁` occur with disjoint finite
witnesses (`{y↔w} ∘ {w↔y₁}`).  The two factors live in different coordinates, so this is the
point at which the two copies separate. -/
def markSet (x y x₁ x₂ y₁ w : V) : Set (TwoCopy V) :=
  Percolation.DisjointOccurrence (connSet y w) (connSet w y₁) ×ˢ
    (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w)

/-- The mark event as the repository's `disjSet`.  Definitional unfolding, recorded so that the
BK bound `bk_connSet_ennreal` applies verbatim. -/
theorem markFresh_eq_disjSet (y y₁ w : V) :
    Percolation.DisjointOccurrence (connSet y w) (connSet w y₁) = disjSet y w w y₁ := rfl

/-- **The excluded moment** of the printed `p = 2`, `q = 1` display,
`E[|Kx|² |Ky| 1(x ↮ y)] = ∫ |Kx|² 1(y ∉ Kx) |Ky|`, in `ℝ≥0∞` so that infinite clusters carry no
subtraction and no finiteness hypothesis is needed. -/
noncomputable def exclMomentSq (π : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω x ^ 2 * (cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
    clusterVol ω y ∂(edgeMeasure π)

/-- The **expected squared cluster volume** `E|Kx|²` and the expected volume `E|Ky|`, again in
`ℝ≥0∞`. -/
noncomputable def volSq (π : Sym2 V → unitInterval) (x : V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω x ^ 2 ∂(edgeMeasure π)

/-- The **second moment of the cluster of `x` through the vertex `w`**,
`E[|Kx|² 1(w ∈ Kx)]`, in `ℝ≥0∞`.  It is the base-copy factor of the marked crossing event at `w`;
bounding it by tree diagrams is the task of the diagram analysis. -/
noncomputable def jointSq (π : Sym2 V → unitInterval) (x w : V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω x ^ 2 * (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w ∂(edgeMeasure π)

open scoped Classical in
/-- The **mean cluster volume** `E|K_v| = ∑_w P(v ↔ w)`, in `ℝ≥0∞`.  On a transitive graph this
does not depend on `v`, and it is the paper's `E|K|`. -/
noncomputable def meanVol (π : Sym2 V → unitInterval) (v : V) : ℝ≥0∞ :=
  ∑' w : V, (edgeMeasure π) (connSet v w)

/-- `T²(x,y) = ∑_a τ(x,a) τ(a,y)`, the two-fold power of the two-point matrix, written out. -/
noncomputable def T2 (π : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' a : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a y)

/-- `T³(x,y) = ∑_{a,b} τ(x,a) τ(a,b) τ(b,y)`, the three-fold power of the two-point matrix. -/
noncomputable def T3 (π : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' a : V, ∑' b : V,
    (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
      (edgeMeasure π) (connSet b y)

/-- `T⁴(x,y) = ∑_{a,b,c} τ(x,a) τ(a,b) τ(b,c) τ(c,y)`, the four-fold power. -/
noncomputable def T4 (π : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' a : V, ∑' b : V, ∑' c : V,
    (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
      (edgeMeasure π) (connSet b c) * (edgeMeasure π) (connSet c y)

/-- The two excess families of the `p = 2`, `q = 1` two-copy expansion, in their reduced
(one-copy-factor) form: `E[|Kx|²1(y∈Kx)] E|K_y| + ∑_w E[|Kx|²1(w∈Kx)] P(y↔w) E|K_w|`.  This is the
quantity a diagram/tree-graph bound has to dominate; see `Final.I417_p21_of_diagram`. -/
noncomputable def excess (π : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ :=
  jointSq π x y * meanVol π y +
    ∑' w : V, jointSq π x w * ((edgeMeasure π) (connSet y w) * meanVol π w)

end PercLib.CriticalLRP.I417
