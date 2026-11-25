/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvgnqju`, member `m1`, direction (A).

# The unexcluded quadratic ghost envelope for the fixed-radius `p = 2` flux

`FluxConv.Insertion` reduces the fixed-radius window-flux convergence
`M.windowFlux (S n) r → M.rhsScalarTwo r` to a *summable marked envelope* that dominates, for every
edge `e`, the flip difference of the windowed square `cutFun S |K₀|²` and of the untruncated
square `|K₀|²` at the closed configuration `ω \ {e}`.  The exact closed ghost is the `ℝ≥0∞` edge
weight `quadEdgeWeight (cutRange r)`, which carries the excluded indicator `1(b ↮ c)` and the
cluster volumes of the *windowed* configuration.

This file defines the envelope the paper's `p = 2` estimate actually produces: the same oriented
pair weight with the exclusion indicator *dropped*, evaluated at the full configuration.  It is
not the closed ghost (dropping `1(b ↮ c)` makes it strictly larger), but it is dominated by the
excluded paper sum plus one cubic cluster term, so its mean is still finite:

* `unexclPairWeight M r ω o b c` — `1(o ↔ b) · 1(|c-b| ≤ r) · 1(b ≠ c) · (2|K_b||K_c| + |K_c|²)`,
  the oriented `p = 2` increment with the exclusion indicator removed;
* `unexclEdgeWeight M r ω o e` — the unordered-edge form (sum of the two orientations, `0` on the
  diagonal edge), exactly the object to integrate against the source's coefficient `cutEdgeDeriv`;
* `ghostEnvelope M r e ω` — the real envelope, the edge weight at the closed configuration
  `ω \ {e}`.

The paper's excluded double sum is `PivotFlux.p2PaperSum` (`SecondMoment/Transport/Defs`), whose
expectation is `M.p2RHS r` (`PivotFlux.lintegral_p2PaperSum_eq_p2RHS`).  The pointwise comparison
`∑_b ∑_c unexclPairWeight ≤ p2PaperSum + 3 |K_₀|⁴` is assembled in `Summable.lean` from
`Compare.lean` and `Correction.lean`; it makes the full envelope summable under a finite fourth
cutoff moment.

No mathematical statement is asserted here beyond the elementary API of these definitions.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Insertion
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.EdgeFamily.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Left.Main

/-!
# Definitions of the unexcluded ghost weights

Definitions only, plus the elementary measurability/monotonicity API.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The unexcluded oriented pair weight -/

/-- **The unexcluded `p = 2` oriented endpoint-pair weight.**  This is `quadPairWeight` with the
pivotal exclusion indicator `1(b ↮ c)` removed, and with the extra factor `1(b ≠ c)` that makes the
diagonal pair carry no weight (so that the edge-to-vertex reindexing is exact).  The `b = c`
coordinate is not needed for the ghost — only genuine edges are differentiated — but keeping it
makes `unexclEdgeWeight` vanish on diagonal edges, as `quadEdgeWeight` does. -/
noncomputable def unexclPairWeight (r : ℝ) (ω : Config M.V) (o b c : M.V) : ℝ≥0∞ :=
  (if b = c then 0 else 1) * (if Connects ω o b then 1 else 0) *
    (if M.cutRange r c b then 1 else 0) *
      (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2)

/-- **The unexcluded `p = 2` unordered edge weight**: the sum of the two orientations. -/
noncomputable def unexclEdgeWeight (r : ℝ) (ω : Config M.V) (o : M.V) (e : Sym2 M.V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun x y => unexclPairWeight M r ω o x y + unexclPairWeight M r ω o y x,
    fun _ _ => add_comm _ _⟩ e

/-- **The real ghost envelope**: the unexcluded edge weight at the *closed* configuration
`ω \ {e}`, in real value.  Its mean is finite by `Summable.lean` under a finite fourth cutoff moment;
it dominates both the windowed and the untruncated flip differences of `|K₀|²` at every edge. -/
noncomputable def ghostEnvelope (r : ℝ) (e : Sym2 M.V) (ω : Config M.V) : ℝ :=
  (unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e).toReal

/-! ## 2. Elementary API of the pair weight -/

/-- The edge weight splits into its two orientations. -/
theorem unexclEdgeWeight_mk (r : ℝ) (ω : Config M.V) (o x y : M.V) :
    unexclEdgeWeight M r ω o s(x, y)
      = unexclPairWeight M r ω o x y + unexclPairWeight M r ω o y x :=
  Sym2.lift_mk ..

/-- The unexcluded edge weight only depends on the unordered pair. -/
theorem unexclEdgeWeight_swap (r : ℝ) (ω : Config M.V) (o x y : M.V) :
    unexclEdgeWeight M r ω o s(x, y) = unexclEdgeWeight M r ω o s(y, x) := by
  rw [unexclEdgeWeight_mk, unexclEdgeWeight_mk, add_comm]

/-- A degenerate oriented pair carries no weight. -/
theorem unexclPairWeight_self (r : ℝ) (ω : Config M.V) (o x : M.V) :
    unexclPairWeight M r ω o x x = 0 := by
  simp only [unexclPairWeight, ite_true, zero_mul]

/-- The degenerate edge carries no weight. -/
theorem unexclEdgeWeight_diag (r : ℝ) (ω : Config M.V) (o x : M.V) :
    unexclEdgeWeight M r ω o s(x, x) = 0 := by
  simp only [unexclEdgeWeight_mk, unexclPairWeight_self, add_zero]

/-- A single oriented pair: the exact `quadPairWeight` is dominated by the unexcluded weight. -/
theorem quadPairWeight_le_unexclPairWeight (r : ℝ) (ω : Config M.V) (o : M.V) {x y : M.V}
    (hxy : x ≠ y) :
    quadPairWeight (M.cutRange r) ω o x y ≤ unexclPairWeight M r ω o x y := by
  by_cases hc : Connects ω x y
  · rw [quadPairWeight_eq_zero_of_connects (M.cutRange r) ω o hc]
    exact zero_le
  · simp only [quadPairWeight, unexclPairWeight, hxy, hc, ite_false, one_mul]
    exact le_of_eq (by ac_rfl)

/-- **Dropping the exclusion indicator.**  On a genuine edge, the exact closed ghost is dominated
by the unexcluded edge weight, at the same configuration. -/
theorem quadEdgeWeight_le_unexclEdgeWeight (r : ℝ) (ω : Config M.V) (o : M.V) (e : Sym2 M.V) :
    quadEdgeWeight (M.cutRange r) ω o e ≤ unexclEdgeWeight M r ω o e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [quadEdgeWeight_mk, unexclEdgeWeight_mk]
    refine add_le_add ?_ ?_
    · by_cases hxy : x = y
      · subst hxy
        rw [quadPairWeight_self, unexclPairWeight_self]
      · exact quadPairWeight_le_unexclPairWeight M r ω o hxy
    · by_cases hxy : x = y
      · subst hxy
        rw [quadPairWeight_self, unexclPairWeight_self]
      · exact quadPairWeight_le_unexclPairWeight M r ω o (fun h => hxy h.symm)

/-- **Monotonicity of the unexcluded pair weight in the configuration.**  Every ingredient of the
unexcluded weight — the connection indicator and the two cluster volumes — is monotone in the
configuration, which is exactly what the exclusion indicator destroys for the closed ghost. -/
theorem unexclPairWeight_mono (r : ℝ) {ω ω' : Config M.V} (h : ∀ e : Sym2 M.V, e ∈ ω → e ∈ ω')
    (o b c : M.V) : unexclPairWeight M r ω o b c ≤ unexclPairWeight M r ω' o b c := by
  have hconn : (if Connects ω o b then (1 : ℝ≥0∞) else 0)
      ≤ (if Connects ω' o b then 1 else 0) := by
    by_cases hc : Connects ω o b
    · rw [ite_eq_left hc, ite_eq_left (connects_mono h hc)]
    · rw [ite_eq_right hc]
      exact zero_le
  have harith : (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2 : ℝ≥0∞)
      ≤ 2 * clusterVol ω' b * clusterVol ω' c + clusterVol ω' c ^ 2 := by
    gcongr
    · exact clusterVol_mono h b
    · exact clusterVol_mono h c
    · exact clusterVol_mono h c
  calc unexclPairWeight M r ω o b c
      = (if b = c then 0 else 1) * (if Connects ω o b then 1 else 0) *
          (if M.cutRange r c b then 1 else 0) *
            (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2) := rfl
    _ ≤ (if b = c then 0 else 1) * (if Connects ω' o b then 1 else 0) *
          (if M.cutRange r c b then 1 else 0) *
            (2 * clusterVol ω' b * clusterVol ω' c + clusterVol ω' c ^ 2) := by
        gcongr
    _ = unexclPairWeight M r ω' o b c := rfl

/-- Monotonicity of the unexcluded edge weight. -/
theorem unexclEdgeWeight_mono (r : ℝ) {ω ω' : Config M.V} (h : ∀ a : Sym2 M.V, a ∈ ω → a ∈ ω')
    (o : M.V) (e : Sym2 M.V) : unexclEdgeWeight M r ω o e ≤ unexclEdgeWeight M r ω' o e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [unexclEdgeWeight_mk, unexclEdgeWeight_mk]
    exact add_le_add (unexclPairWeight_mono M r h o x y) (unexclPairWeight_mono M r h o y x)

/-- The unexcluded pair weight is finite when all cluster volumes at the configuration are. -/
theorem unexclPairWeight_ne_top (r : ℝ) (ω : Config M.V) (o b c : M.V)
    (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) : unexclPairWeight M r ω o b c ≠ ⊤ := by
  simp only [unexclPairWeight]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_
  · split_ifs <;> simp
  · split_ifs <;> simp
  · split_ifs <;> simp
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (hfin b)) (hfin c),
        ENNReal.pow_ne_top (hfin c)⟩

/-- The unexcluded edge weight is finite when all cluster volumes at the configuration are. -/
theorem unexclEdgeWeight_ne_top (r : ℝ) (ω : Config M.V) (o : M.V) (e : Sym2 M.V)
    (hfin : ∀ v : M.V, clusterVol ω v ≠ ⊤) : unexclEdgeWeight M r ω o e ≠ ⊤ := by
  induction e using Sym2.ind with
  | h x y =>
    rw [unexclEdgeWeight_mk]
    exact ENNReal.add_ne_top.mpr
      ⟨unexclPairWeight_ne_top M r ω o x y hfin, unexclPairWeight_ne_top M r ω o y x hfin⟩

/-! ## 3. Measurability -/

/-- The unexcluded pair weight is measurable in the configuration. -/
theorem measurable_unexclPairWeight (r : ℝ) (o b c : M.V) :
    Measurable fun ω : Config M.V => unexclPairWeight M r ω o b c := by
  have h1 : Measurable fun ω : Config M.V => (if Connects ω o b then (1 : ℝ≥0∞) else 0) :=
    measurable_const.indicator (measurableSet_cluster_mem o b)
  have h3 : Measurable fun ω : Config M.V =>
      (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2 : ℝ≥0∞) :=
    (((measurable_clusterVol b).const_mul 2).mul (measurable_clusterVol c)).add
      ((measurable_clusterVol c).pow_const 2)
  have h0 : Measurable fun _ : Config M.V => (if b = c then (0 : ℝ≥0∞) else 1) :=
    measurable_const
  have h2 : Measurable fun _ : Config M.V => (if M.cutRange r c b then (1 : ℝ≥0∞) else 0) :=
    measurable_const
  exact ((h0.mul h1).mul h2).mul h3

/-- The unexcluded edge weight is measurable in the configuration. -/
theorem measurable_unexclEdgeWeight (r : ℝ) (o : M.V) (e : Sym2 M.V) :
    Measurable fun ω : Config M.V => unexclEdgeWeight M r ω o e := by
  induction e using Sym2.ind with
  | h x y =>
    have hfun : (fun ω : Config M.V => unexclEdgeWeight M r ω o s(x, y))
        = fun ω => unexclPairWeight M r ω o x y + unexclPairWeight M r ω o y x :=
      funext fun ω => unexclEdgeWeight_mk M r ω o x y
    rw [hfun]
    exact (measurable_unexclPairWeight M r o x y).add (measurable_unexclPairWeight M r o y x)

/-- The ghost envelope is measurable in the configuration. -/
theorem measurable_ghostEnvelope (r : ℝ) (e : Sym2 M.V) :
    Measurable fun ω : Config M.V => ghostEnvelope M r e ω :=
  ENNReal.measurable_toReal.comp
    ((measurable_unexclEdgeWeight M r (0 : M.V) e).comp
      (PercLib.Probability.measurable_diff_singleton e))

/-- The ghost envelope is nonnegative. -/
theorem ghostEnvelope_nonneg (r : ℝ) (e : Sym2 M.V) (ω : Config M.V) :
    0 ≤ ghostEnvelope M r e ω := ENNReal.toReal_nonneg

/-! ## 4. Closing one coordinate only increases the unexcluded weight -/

/-- The unexcluded edge weight at the closed configuration `ω \ {e}` is dominated by the value at
`ω`: this is where dropping the exclusion indicator pays off. -/
theorem unexclEdgeWeight_sdiff_le (r : ℝ) (ω : Config M.V) (o : M.V) (e : Sym2 M.V) :
    unexclEdgeWeight M r (ω \ {e}) o e ≤ unexclEdgeWeight M r ω o e :=
  unexclEdgeWeight_mono M r (fun _ ha => Set.mem_of_mem_sdiff ha) o e

/-! ## 5. Cubic majorant and the full envelope -/

/-- The cubic merge majorant of the square-flip increment at an edge with endpoints `x, y`.
It uses no exclusion indicator. -/
noncomputable def bigPair (γ : Config M.V) (x y : M.V) : ℝ≥0∞ :=
  2 * clusterVol γ (0 : M.V) ^ 2 + 3 * clusterVol γ x ^ 2 + 3 * clusterVol γ y ^ 2

/-- The unordered-edge form of the cubic merge majorant. -/
noncomputable def bigEdge (γ : Config M.V) (e : Sym2 M.V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun x y => bigPair M γ x y, by intro x y; simp only [bigPair]; ring⟩ e

/-- The `ℝ≥0∞` envelope: the unexcluded closed ghost, with the cubic merge majorant added
exactly on edges outside the radius-derivative support. -/
noncomputable def envelopeE (r : ℝ) (e : Sym2 M.V) (ω : Config M.V) : ℝ≥0∞ :=
  unexclEdgeWeight M r (ω \ {e}) (0 : M.V) e +
    (if M.cutEdgeDeriv r e = 0 then bigEdge M (ω \ {e}) e else 0)

/-- The real envelope provided to `FluxConv.Insertion`. Its summability at a positive radius
is proved in `Envelope/Summable.lean` from a finite fourth cutoff moment. -/
noncomputable def envelope (r : ℝ) (e : Sym2 M.V) (ω : Config M.V) : ℝ :=
  (envelopeE M r e ω).toReal

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms unexclPairWeight
#print axioms unexclEdgeWeight
#print axioms ghostEnvelope
#print axioms unexclEdgeWeight_mk
#print axioms unexclEdgeWeight_diag
#print axioms quadEdgeWeight_le_unexclEdgeWeight
#print axioms unexclPairWeight_mono
#print axioms unexclEdgeWeight_mono
#print axioms unexclPairWeight_ne_top
#print axioms unexclEdgeWeight_ne_top
#print axioms measurable_unexclPairWeight
#print axioms measurable_unexclEdgeWeight
#print axioms measurable_ghostEnvelope
#print axioms unexclEdgeWeight_sdiff_le

end PercLib.CriticalLRP.Orchestration.SourceModelData
