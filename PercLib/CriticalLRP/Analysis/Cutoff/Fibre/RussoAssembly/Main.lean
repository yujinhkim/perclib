/-
Swarm `smwu62ffl`, member `m1`, direction D1C (expectation-level standardized excluded-flux
assembly).

# Closed-event bridge: the landed real per-edge identity *is* the `ℝ≥0∞` edge increment

`Analysis/Cutoff/ExcludedFlux` proves, per genuine edge `{x,y}` of length `≤ r`, the identity

`cutEdgeDeriv r s(x,y) * pivotalFlux (cutLaw r) (sMomentTrunc 1 0 A) s(x,y)
   = β_c (-K'(r)) * ∫ ω, 1{s(x,y) ∉ ω} * (excluded real increment) ∂cutLaw r`,

whereas `E1Sign.exclMass` is assembled from the `ℝ≥0∞`-valued `pairIncr` / `edgeIncr`
(`pairIncrFull` / `edgeIncrFull` untruncated).  This file supplies the missing pointwise bridge
between the two, and the resulting *per-edge* and *finite-window* identities with `β_c` and
`-deriv K` factored out.

Contents:

* `not_connects_iff_of_connects_left/right`: around the anchor, `¬0↔y` and `¬x↔y` agree;
* `exclIncr`: the closed-event excluded increment as a named object;
* `ofReal_exclIncr_eq_pairIncr_add`: its `ℝ≥0∞` value is exactly the sum of the two ordered-pair
  increments `pairIncr … x y + pairIncr … y x`, with **both** ordered directions;
* `ofReal_closed_exclIncr_eq_edgeIncr`: inserting the closed-event indicator `1{s(x,y) ∉ ω}` gives
  exactly the unordered edge increment `edgeIncr`;
* `cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr(_of_dist)`: the per-edge identity rewritten at
  `∫⁻ edgeIncr`, for **every** edge (loops and out-of-range edges give `0 = 0`);
* `sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr`: the finite-window sum, with `β_c (-K')`
  factored out and the ordered-pair double sum on the right.

Nothing here takes a derivative through a sum, assumes a moment, or reindexes ordered pairs by
inspection: the ordered↔unordered step is the landed `sum_pairIncr_eq_sum_edgeIncr`.

-/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.RussoAssembly.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Truncation
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Expectation.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.PaperSum

/-!
Closed-event bridge from the landed real per-edge excluded-flux identity to the `ℝ≥0∞` edge
increment (both ordered directions, every edge), the resulting per-edge and finite-window
standardized identities with `β_c` and `-deriv K` factored, the expectation-level truncation of
`E1Sign.exclMass` in `ℝ≥0∞` (finite windows, untruncated windows, and the per-edge decomposition),
the closed-event full-cluster limit, and the exact obstruction to a real-valued full-cluster
per-edge identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Set
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. Connection transfer around the anchor -/

/-- If `o` is connected to `x`, then `y` is connected to `x` exactly when it is connected to
`o`: the closed events `{x ↮ y}` and `{o ↮ y}` coincide.  (Both directions of the `↔` are used
below, so this is not a one-way implication.) -/
theorem not_connects_iff_of_connects_left {ω : Config V} {o x y : V}
    (hx : Connects ω o x) : (¬ Connects ω x y ↔ ¬ Connects ω o y) := by
  constructor
  · intro h hy
    exact h (connects_trans (connects_symm hx) hy)
  · intro h hxy
    exact h (connects_trans hx hxy)

/-- The mirror of `not_connects_iff_of_connects_left`. -/
theorem not_connects_iff_of_connects_right {ω : Config V} {o x y : V}
    (hy : Connects ω o y) : (¬ Connects ω y x ↔ ¬ Connects ω o x) :=
  not_connects_iff_of_connects_left (o := o) (x := y) (y := x) hy

/-- If the anchor is connected to both endpoints, the edge already connects them. -/
theorem connects_of_connects_anchor {ω : Config V} {o x y : V}
    (hx : Connects ω o x) (hy : Connects ω o y) : Connects ω x y :=
  connects_trans (connects_symm hx) hy

/-! ## 2. The closed-event excluded increment (defined in `D1CDefs`) -/

theorem exclIncr_nonneg (ω : Config V) (o : V) (A : Finset V) (x y : V) :
    0 ≤ exclIncr ω o A x y := by
  unfold exclIncr
  refine add_nonneg ?_ ?_
  · by_cases h : Connects ω o x ∧ ¬ Connects ω o y
    · rw [ite_eq_left h]; exact sMomentTrunc_nonneg (fun _ => zero_le_one) _ _ _
    · rw [ite_eq_right h]
  · by_cases h : Connects ω o y ∧ ¬ Connects ω o x
    · rw [ite_eq_left h]; exact sMomentTrunc_nonneg (fun _ => zero_le_one) _ _ _
    · rw [ite_eq_right h]

/-! ## 3. The truncated cluster volume is bounded, hence never `⊤` -/

theorem sMomentTruncENN_one_le_card (c : V) (A : Finset V) (ω : Config V) :
    sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ≤ (A.card : ℝ≥0∞) := by
  rw [sMomentTruncENN]
  calc ∑ x ∈ A, (cluster ω c).indicator (fun x => ENNReal.ofReal ((fun _ => (1 : ℝ)) x)) x
      ≤ ∑ _x ∈ A, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : x ∈ cluster ω c
        · rw [Set.indicator_of_mem h, ENNReal.ofReal_one]
        · rw [Set.indicator_of_notMem h]; exact zero_le
    _ = (A.card : ℝ≥0∞) := by simp

theorem sMomentTruncENN_ne_top (c : V) (A : Finset V) (ω : Config V) :
    sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (sMomentTruncENN_one_le_card c A ω)

theorem pairIncr_ne_top (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A : Finset V) (b c : V) : pairIncr d ω o A b c ≠ ⊤ := by
  have h1 : (if Connects ω o b then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
  have h2 : (if d c b then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
  have h3 : (if ¬ Connects ω b c then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
  have hle : pairIncr d ω o A b c ≤ (A.card : ℝ≥0∞) := by
    rw [pairIncr]
    calc (if Connects ω o b then (1 : ℝ≥0∞) else 0) * (if d c b then 1 else 0) *
          (if ¬ Connects ω b c then 1 else 0) * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
        ≤ 1 * 1 * 1 * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω := by gcongr
      _ = sMomentTruncENN (fun _ => (1 : ℝ)) c A ω := by simp
      _ ≤ (A.card : ℝ≥0∞) := sMomentTruncENN_one_le_card c A ω
  exact ne_top_of_le_ne_top (by simp) hle

theorem edgeIncr_ne_top (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (A : Finset V) (e : Sym2 V) :
    edgeIncr d hd ω o A e ≠ ⊤ := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [edgeIncr_mk]
    exact ENNReal.add_ne_top.2 ⟨pairIncr_ne_top d ω o A x y, pairIncr_ne_top d ω o A y x⟩

/-! ## 4. The pointwise bridge: excluded increment = sum of the two ordered-pair increments

Neither direction is assumed: the `ℝ≥0∞` side carries the extra factor `1{x ↮ y}` (the event
that the edge does not already connect its endpoints by another route) and the `ℝ` side carries
the extra factor `1{s(x,y) ∉ ω}` (the closed event of the flip).  On `{x ↮ y}` neither factor can
be `0` while the other is `1` when the anchor hypothesis holds, which is what the four-case
analysis establishes. -/

/-- **Left ordered direction.**  The `x`-anchored excluded term is the contribution carried by
the `x,y` ordered pair once its distance condition is supplied. -/
theorem ofReal_exclIncr_left (ω : Config V) (o : V) (A : Finset V) (x y : V) :
    ENNReal.ofReal
        (if Connects ω o x ∧ ¬ Connects ω o y then
          sMomentTrunc (fun _ => (1 : ℝ)) y A ω else 0)
      = (if Connects ω o x then (1 : ℝ≥0∞) else 0) *
          (if ¬ Connects ω x y then 1 else 0) *
          sMomentTruncENN (fun _ => (1 : ℝ)) y A ω := by
  by_cases hx : Connects ω o x
  · by_cases hy : Connects ω o y
    · have hxy : Connects ω x y := connects_of_connects_anchor hx hy
      rw [ite_eq_right (by tauto), ite_eq_left hx, ite_eq_right (by simpa using hxy)]
      simp
    · have hxy : ¬ Connects ω x y := fun h => hy (connects_trans hx h)
      rw [ite_eq_left ⟨hx, hy⟩, ite_eq_left hx, ite_eq_left hxy]
      simp only [mul_one, one_mul]
      exact ofReal_sMomentTrunc (fun _ => zero_le_one) y A ω
  · rw [ite_eq_right (by tauto), ite_eq_right hx]
    simp

/-- **Right ordered direction.**  The mirrored contribution at the `y,x` ordered pair. -/
theorem ofReal_exclIncr_right (ω : Config V) (o : V) (A : Finset V) (x y : V) :
    ENNReal.ofReal
        (if Connects ω o y ∧ ¬ Connects ω o x then
          sMomentTrunc (fun _ => (1 : ℝ)) x A ω else 0)
      = (if Connects ω o y then (1 : ℝ≥0∞) else 0) *
          (if ¬ Connects ω y x then 1 else 0) *
          sMomentTruncENN (fun _ => (1 : ℝ)) x A ω := by
  by_cases hy : Connects ω o y
  · by_cases hx : Connects ω o x
    · have hyx : Connects ω y x := connects_of_connects_anchor hy hx
      rw [ite_eq_right (by tauto), ite_eq_left hy, ite_eq_right (by simpa using hyx)]
      simp
    · have hyx : ¬ Connects ω y x := fun h => hx (connects_trans hy h)
      rw [ite_eq_left ⟨hy, hx⟩, ite_eq_left hy, ite_eq_left hyx]
      simp only [mul_one, one_mul]
      exact ofReal_sMomentTrunc (fun _ => zero_le_one) x A ω
  · rw [ite_eq_right (by tauto), ite_eq_right hy]
    simp

/-- **The excluded increment is the sum of both ordered-pair increments.** -/
theorem ofReal_exclIncr_eq_pairIncr_add (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (A : Finset V) (x y : V)
    (hyx : d y x) :
    ENNReal.ofReal (exclIncr ω o A x y) = pairIncr d ω o A x y + pairIncr d ω o A y x := by
  unfold exclIncr
  rw [ENNReal.ofReal_add
    (by
      by_cases h : Connects ω o x ∧ ¬ Connects ω o y
      · rw [ite_eq_left h]; exact sMomentTrunc_nonneg (fun _ => zero_le_one) _ _ _
      · rw [ite_eq_right h])
    (by
      by_cases h : Connects ω o y ∧ ¬ Connects ω o x
      · rw [ite_eq_left h]; exact sMomentTrunc_nonneg (fun _ => zero_le_one) _ _ _
      · rw [ite_eq_right h])]
  rw [ofReal_exclIncr_left ω o A x y, ofReal_exclIncr_right ω o A x y]
  simp only [pairIncr]
  rw [show (if d y x then (1 : ℝ≥0∞) else 0) = 1 from ite_eq_left hyx,
    show (if d x y then (1 : ℝ≥0∞) else 0) = 1 from ite_eq_left ((hd y x).mp hyx)]
  ring

/-- **The closed-event excluded increment is the unordered edge increment.**

`edgeIncr` already vanishes when the edge is open (it connects its own endpoints), so inserting
the closed-event indicator `1{s(x,y) ∉ ω}` changes nothing; and on the closed event the excluded
increment is exactly `pairIncr x y + pairIncr y x`.  This holds for **every** pair `(x,y)`,
including the loop `s(x,x)` and edges outside the derivative support. -/
theorem ofReal_closed_exclIncr_eq_edgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (A : Finset V) (x y : V)
    (hyx : d y x) :
    ENNReal.ofReal (if s(x, y) ∈ ω then 0 else exclIncr ω o A x y)
      = edgeIncr d hd ω o A s(x, y) := by
  by_cases h : s(x, y) ∈ ω
  · rw [ite_eq_left h]
    by_cases hxy : x = y
    · subst hxy
      rw [edgeIncr_loop]
      simp
    · rw [edgeIncr_mk]
      have hc : Connects ω x y :=
        SimpleGraph.Adj.reachable (openGraph_adj.mpr ⟨hxy, h⟩)
      rw [pairIncr, pairIncr]
      simp [hc, connects_symm hc]
  · rw [ite_eq_right h, ofReal_exclIncr_eq_pairIncr_add d hd ω o A x y hyx, edgeIncr_mk]

/-! ## 5. The per-edge identity at `∫⁻ edgeIncr` -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **Per-edge standardized excluded-flux identity at the `ℝ≥0∞` edge increment.**

For a genuine edge `{x,y}` of length `≤ r`, the literal per-edge Russo flux of the truncated
cluster moment is `β_c (-K'(r))` times the `cutLaw r`-expectation of the `ℝ≥0∞` edge increment
`edgeIncr (cutDist M r) … 0 A s(x,y)`.

The real→`ℝ≥0∞` conversion here is honest: `edgeIncr` is bounded by `|A|` (`edgeIncr_ne_top`), so
`ENNReal.ofReal ((edgeIncr ω).toReal) = edgeIncr ω` pointwise and no `⊤` is read as `0`.  The
closed-event factorisation `1 - q_e(r)` is the landed `one_sub_mul_pivotalFlux_eq`. -/
theorem cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr_of_dist (A : Finset M.V) {r : ℝ} {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    M.cutEdgeDeriv r s(x, y) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          (∫⁻ ω, edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)
            ∂(M.cutLaw r)).toReal := by
  rw [M.cutEdgeDeriv_mul_pivotalFlux_eq_excl A hxy hdist]
  have hpt : ∀ ω : Config M.V,
      (if s(x, y) ∈ ω then (0 : ℝ) else exclIncr ω (0 : M.V) A x y)
        = (edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal := by
    intro ω
    have hyx : cutDist M r y x := (cutDist_symm M r x y).mp hdist
    rw [← ofReal_closed_exclIncr_eq_edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A x y
      hyx]
    refine (ENNReal.toReal_ofReal ?_).symm
    by_cases h : s(x, y) ∈ ω
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact exclIncr_nonneg ω (0 : M.V) A x y
  have hEq : (∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else exclIncr ω (0 : M.V) A x y)
        ∂(M.cutLaw r))
      = ∫ ω, (edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal
          ∂(M.cutLaw r) := integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hEq]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
    ((measurable_edgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A s(x, y)).ennreal_toReal
      |>.aestronglyMeasurable)]
  exact congrArg (fun t => (M.betaCrit : ℝ) * (-(deriv M.K r)) * t)
    (congrArg ENNReal.toReal (lintegral_congr fun ω =>
      ENNReal.ofReal_toReal
        (edgeIncr_ne_top (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y))))

/-- **The per-edge identity for every edge.**  On a loop (`x = y`) or an edge of length `> r` both
sides vanish: `cutEdgeDeriv` is `0` by construction, and the distance indicator inside `edgeIncr`
is `0`.  So the identity needs no support hypothesis. -/
theorem cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr (A : Finset M.V) (r : ℝ) (e : Sym2 M.V) :
    M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          (∫⁻ ω, edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e
            ∂(M.cutLaw r)).toReal := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeDeriv_mk, ite_eq_left rfl, zero_mul]
      simp [edgeIncr_loop]
    · by_cases hdist : M.S.dist x y ≤ r
      · exact M.cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr_of_dist A hxy hdist
      · rw [M.cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_right hdist, zero_mul]
        have hedge : (fun ω : Config M.V =>
              edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y))
            = fun _ => 0 := by
          funext ω
          rw [edgeIncr_mk]
          have h1 : ¬ cutDist M r x y := hdist
          have h2 : ¬ cutDist M r y x := fun hh => hdist ((cutDist_symm M r y x).mp hh)
          simp [pairIncr, h1, h2]
        rw [hedge]
        simp

/-- The `cutLaw r`-integrability of the `ℝ≥0∞` edge increment: bounded by `2|A|`. -/
theorem lintegral_edgeIncr_ne_top (A : Finset M.V) (r : ℝ) (e : Sym2 M.V) :
    ∫⁻ ω, edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e ∂(M.cutLaw r) ≠ ⊤ := by
  have hb : ∀ ω : Config M.V,
      edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e
        ≤ ((A.card : ℝ≥0∞) + (A.card : ℝ≥0∞)) := by
    induction e using Sym2.ind with
    | _ x y =>
      intro ω
      rw [edgeIncr_mk]
      have h1 : pairIncr (cutDist M r) ω (0 : M.V) A x y ≤ (A.card : ℝ≥0∞) := by
        refine le_trans ?_ (sMomentTruncENN_one_le_card y A ω)
        rw [pairIncr]
        have h2 : (if Connects ω (0 : M.V) x then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
        have h3 : (if cutDist M r y x then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
        have h4 : (if ¬ Connects ω x y then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
        calc (if Connects ω (0 : M.V) x then (1 : ℝ≥0∞) else 0) *
              (if cutDist M r y x then 1 else 0) * (if ¬ Connects ω x y then 1 else 0) *
                sMomentTruncENN (fun _ => (1 : ℝ)) y A ω
            ≤ 1 * 1 * 1 * sMomentTruncENN (fun _ => (1 : ℝ)) y A ω := by gcongr
          _ = sMomentTruncENN (fun _ => (1 : ℝ)) y A ω := by simp
      have h5 : pairIncr (cutDist M r) ω (0 : M.V) A y x ≤ (A.card : ℝ≥0∞) := by
        refine le_trans ?_ (sMomentTruncENN_one_le_card x A ω)
        rw [pairIncr]
        have h2 : (if Connects ω (0 : M.V) y then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
        have h3 : (if cutDist M r x y then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
        have h4 : (if ¬ Connects ω y x then (1 : ℝ≥0∞) else 0) ≤ 1 := by split <;> simp
        calc (if Connects ω (0 : M.V) y then (1 : ℝ≥0∞) else 0) *
              (if cutDist M r x y then 1 else 0) * (if ¬ Connects ω y x then 1 else 0) *
                sMomentTruncENN (fun _ => (1 : ℝ)) x A ω
            ≤ 1 * 1 * 1 * sMomentTruncENN (fun _ => (1 : ℝ)) x A ω := by gcongr
          _ = sMomentTruncENN (fun _ => (1 : ℝ)) x A ω := by simp
      exact add_le_add h1 h5
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
  simp

/-- **The finite-window standardized excluded-flux sum at the actual source law.**

For a finite vertex window `X` and a finite truncation `A`, the sum over the edges inside `X` of
the literal per-edge Russo fluxes of the truncated cluster moment `|K_0 ∩ A|` is `β_c (-K'(r))`
times the `cutLaw r`-expectation of the ordered-pair double sum of the excluded increments over
`X × X`.

All the reindexing is the landed `sum_pairIncr_eq_sum_edgeIncr` (closed edges → two ordered
directions, diagonal handled), and the `1 - q_e` mass transport is the landed
`one_sub_mul_pivotalFlux_eq`.  No summability, moment finiteness or derivative interchange enters.
-/
theorem sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr (A X : Finset M.V) (r : ℝ) :
    ∑ e ∈ X.sym2, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          (∫⁻ ω, (∑ x ∈ X, ∑ y ∈ X,
            pairIncr (cutDist M r) ω (0 : M.V) A x y) ∂(M.cutLaw r)).toReal := by
  rw [Finset.sum_congr rfl (fun e _ => M.cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr A r e)]
  rw [← Finset.mul_sum]
  congr 1
  rw [← ENNReal.toReal_sum (fun e _ => M.lintegral_edgeIncr_ne_top A r e)]
  rw [← lintegral_finsetSum (μ := M.cutLaw r)
    (f := fun e ω => edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e)
    (s := X.sym2)
    (fun e _ => measurable_edgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A e)]
  exact congrArg ENNReal.toReal (lintegral_congr fun ω =>
    (sum_pairIncr_eq_sum_edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A X).symm)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.not_connects_iff_of_connects_left
#print axioms PercLib.CriticalLRP.Orchestration.not_connects_iff_of_connects_right
#print axioms PercLib.CriticalLRP.Orchestration.connects_of_connects_anchor
#print axioms PercLib.CriticalLRP.Orchestration.exclIncr_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.sMomentTruncENN_one_le_card
#print axioms PercLib.CriticalLRP.Orchestration.sMomentTruncENN_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.pairIncr_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncr_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_exclIncr_left
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_exclIncr_right
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_exclIncr_eq_pairIncr_add
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_closed_exclIncr_eq_edgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr_of_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_edgeIncr_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr

end PercLib.CriticalLRP.Orchestration

/-! # Part II: expectation-level assembly at `E1Sign.exclMass`

The finite-window identity above is a statement about one configuration-window pair.  This part
transports it under `cutLaw r`, in `ℝ≥0∞` where no `⊤` has to be read as `0`, and then reads the
resulting supremum off against `E1Sign.exclMass`.

* `windowSum`, `windowSumFull`: the window/truncation sums, named;
* `iSup_windowSum_eq_tsum`: `⨆_X windowSum A X = Σ'_p pairIncr A` for each configuration;
* `iSup_lintegral_windowSum`, `exclMass_eq_iSup_iSup_lintegral_window`: the double truncation
  supremum under `cutLaw r` is `exclMass` (monotone convergence, directed index);
* `iSup_windowSum_eq_windowSumFull`, `exclMass_eq_iSup_lintegral_windowSumFull`: the same with the
  truncation `A` removed first — the untruncated window form of `exclMass`;
* `exclMass_eq_tsum_lintegral_edgeIncrFull`: the untruncated **per-edge** decomposition of
  `exclMass`, `exclMass = Σ'_e ∫⁻ edgeIncrFull e`, which is the literal infinite-lattice form at
  `PivotFlux.paperSum` and `E1Sign.exclMass`;
* `lintegral_windowSum_le_exclMass`, `sum_cutEdgeDeriv_mul_pivotalFlux_le_exclMass`: the
  standardized finite-window flux is dominated by `β_c (-K'(r)) · exclMass.toReal`, with
  `exclMass ≠ ⊤` **explicit** (without it, `toReal ⊤ = 0` would falsely force the flux to vanish);
* `iSup_codeWindow_diag_lintegral`, `tendsto_sum_cutEdgeDeriv_mul_pivotalFlux`,
  `iSup_sum_cutEdgeDeriv_mul_pivotalFlux`: the standardized Russo sums increase to
  `β_c (-K'(r)) · exclMass.toReal` along the canonical cofinal window sequence — this is the
  honest infinite-lattice statement, and it needs `deriv M.K r ≤ 0` because a supremum of reals
  does not commute with multiplying by a negative constant;
* `iSup_edgeIncr_eq_edgeIncrFull`, `ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncr`,
  `iSup_ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncrFull`: the **closed-event
  full-cluster limit** in `ℝ≥0∞`;
* `ofReal_toReal_eq_self_iff`, `pairIncrFull_eq_top`, `not_exists_real_eq_pairIncrFull_of_clusterVol_top`:
  the exact obstruction to a real-valued full-cluster per-edge identity.
-/

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 6. Window and truncation sums -/

theorem monotone_windowSum_window (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A : Finset V) : Monotone fun X : Finset V => windowSum d ω o A X := by
  intro X Y hXY
  change windowSum d ω o A X ≤ windowSum d ω o A Y
  have h1 : windowSum d ω o A X = ∑ p ∈ X ×ˢ X, pairIncr d ω o A p.1 p.2 := by
    rw [windowSum]
    exact (Finset.sum_product X X (fun p : V × V => pairIncr d ω o A p.1 p.2)).symm
  have h2 : windowSum d ω o A Y = ∑ p ∈ Y ×ˢ Y, pairIncr d ω o A p.1 p.2 := by
    rw [windowSum]
    exact (Finset.sum_product Y Y (fun p : V × V => pairIncr d ω o A p.1 p.2)).symm
  rw [h1, h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.product_subset_product hXY hXY)
    (fun _ _ _ => zero_le)

theorem monotone_windowSum_trunc (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    {A B : Finset V} (hAB : A ⊆ B) (X : Finset V) :
    windowSum d ω o A X ≤ windowSum d ω o B X := by
  rw [windowSum, windowSum]
  exact Finset.sum_le_sum fun x _ =>
    Finset.sum_le_sum fun y _ => pairIncr_subset hAB d ω o x y

theorem windowSum_le_windowSum_of_subsets (d : V → V → Prop) [DecidableRel d] (ω : Config V)
    (o : V) {A B X Y : Finset V} (hAB : A ⊆ B) (hXY : X ⊆ Y) :
    windowSum d ω o A X ≤ windowSum d ω o B Y :=
  le_trans (monotone_windowSum_trunc d ω o hAB X) (monotone_windowSum_window d ω o B hXY)

theorem measurable_windowSum (d : V → V → Prop) [DecidableRel d] (o : V) (A : Finset V)
    (X : Finset V) : Measurable fun ω : Config V => windowSum d ω o A X :=
  Finset.measurable_sum X fun x _ =>
    Finset.measurable_sum X fun y _ => measurable_pairIncr d o A x y

theorem iSup_windowSum_eq_tsum (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A : Finset V) :
    (⨆ X : Finset V, windowSum d ω o A X) = ∑' p : V × V, pairIncr d ω o A p.1 p.2 := by
  have h : (⨆ X : Finset V, windowSum d ω o A X)
      = ⨆ X : Finset V, ∑ p ∈ X ×ˢ X, pairIncr d ω o A p.1 p.2 :=
    iSup_congr fun X => by
      rw [windowSum]
      exact (Finset.sum_product X X (fun p : V × V => pairIncr d ω o A p.1 p.2)).symm
  rw [h, ENNReal.tsum_eq_iSup_sum]
  exact iSup_square_sum_eq_iSup_finset_sum _

/-- **The window supremum under the law.**  Monotone convergence for the directed family of
square windows, at fixed truncation `A`. -/
theorem iSup_lintegral_windowSum (M : SourceModelData) (A : Finset M.V) (r : ℝ) :
    (⨆ X : Finset M.V, ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V) A X ∂(M.cutLaw r))
      = ∫⁻ ω, (∑' p : M.V × M.V,
          pairIncr (cutDist M r) ω (0 : M.V) A p.1 p.2) ∂(M.cutLaw r) := by
  rw [← lintegral_iSup_directed
    (f := fun X : Finset M.V => fun ω => windowSum (cutDist M r) ω (0 : M.V) A X)
    (fun X => (measurable_windowSum (cutDist M r) (0 : M.V) A X).aemeasurable)
    (fun X Y => ⟨X ∪ Y,
      fun ω => monotone_windowSum_window (cutDist M r) ω (0 : M.V) A Finset.subset_union_left,
      fun ω => monotone_windowSum_window (cutDist M r) ω (0 : M.V) A Finset.subset_union_right⟩)]
  exact lintegral_congr fun ω => iSup_windowSum_eq_tsum (cutDist M r) ω (0 : M.V) A

/-- **Expectation-level finite-truncation identity, in window form.**

The double supremum over a finite vertex truncation `A` and a finite window `X` of the summed
ordered-pair excluded increment is exactly `E1Sign.exclMass`.  This is the literal match for the
finite-window flux identity: it is the same `windowSum` on both sides. -/
theorem exclMass_eq_iSup_iSup_lintegral_window (M : SourceModelData) (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ A : Finset M.V, ⨆ X : Finset M.V,
          ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V) A X ∂(M.cutLaw r) := by
  rw [exclMass_eq_iSup_lintegral_pairIncr M r]
  exact iSup_congr fun A => (iSup_lintegral_windowSum M A r).symm

/-- Every finite window/truncation expectation is dominated by the excluded mass. -/
theorem lintegral_windowSum_le_exclMass (M : SourceModelData) (A X : Finset M.V) (r : ℝ) :
    ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V) A X ∂(M.cutLaw r)
      ≤ E1Sign.exclMass M r := by
  calc ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V) A X ∂(M.cutLaw r)
      ≤ ∫⁻ ω, (⨆ X' : Finset M.V, windowSum (cutDist M r) ω (0 : M.V) A X')
          ∂(M.cutLaw r) :=
        lintegral_mono fun ω =>
          le_iSup (fun X' : Finset M.V => windowSum (cutDist M r) ω (0 : M.V) A X') X
    _ = ∫⁻ ω, (∑' p : M.V × M.V,
          pairIncr (cutDist M r) ω (0 : M.V) A p.1 p.2) ∂(M.cutLaw r) :=
        lintegral_congr fun ω => iSup_windowSum_eq_tsum (cutDist M r) ω (0 : M.V) A
    _ ≤ E1Sign.exclMass M r := lintegral_tsum_pairIncr_le_exclMass M r A

/-! ## 7. The standardized finite-window flux, dominated by `exclMass`

The sign of `deriv M.K r` is *not* assumed by the identity, but it is needed for the supremum in
the next section: `⨆` of reals does not commute with multiplication by a negative constant.
`exclMass ≠ ⊤` is likewise explicit: without it, `toReal ⊤ = 0` would force the (nonnegative)
standardized flux to vanish. -/

/-- **The standardized finite-window excluded flux is dominated by `β_c (-K'(r)) exclMass`.**

This is the finite-window Russo majorant at the actual source law, with `β_c` and `-deriv K`
factored out and `exclMass` on the right.  `hK'` is the sign of the source's slope and `hE` is the
finiteness of the excluded mass; both are genuinely needed (see above). -/
theorem sum_cutEdgeDeriv_mul_pivotalFlux_le_exclMass (M : SourceModelData) (A X : Finset M.V)
    {r : ℝ} (hK' : deriv M.K r ≤ 0) (hE : E1Sign.exclMass M r ≠ ⊤) :
    ∑ e ∈ X.sym2, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e
      ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal := by
  rw [M.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr A X r]
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact ENNReal.toReal_mono hE (lintegral_windowSum_le_exclMass M A X r)
  · exact mul_nonneg (M.betaCrit.coe_nonneg) (by linarith)

/-! ## 8. The supremum of the standardized Russo sums along the cofinal window sequence -/

/-- The diagonal window sequence is cofinal in the product of the truncation and window indices. -/
theorem iSup_codeWindow_diag_lintegral (M : SourceModelData) (r : ℝ) :
    (⨆ k : ℕ, ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V)
        (codeWindow M.V k) (codeWindow M.V k) ∂(M.cutLaw r))
      = E1Sign.exclMass M r := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => ?_
    rw [exclMass_eq_iSup_iSup_lintegral_window M r]
    exact le_iSup_of_le (f := fun A : Finset M.V => ⨆ X : Finset M.V,
        ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V) A X ∂(M.cutLaw r)) (codeWindow M.V k)
      (le_iSup_of_le (f := fun X : Finset M.V =>
          ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V) (codeWindow M.V k) X ∂(M.cutLaw r))
        (codeWindow M.V k) le_rfl)
  · rw [exclMass_eq_iSup_iSup_lintegral_window M r]
    refine iSup_le fun A => iSup_le fun X => ?_
    obtain ⟨k, hk⟩ := exists_codeWindow_subset M.V (A ∪ X)
    refine le_iSup_of_le k (lintegral_mono fun ω => ?_)
    exact windowSum_le_windowSum_of_subsets (cutDist M r) ω (0 : M.V)
      (fun x hx => hk (Finset.mem_union_left _ hx)) (fun x hx => hk (Finset.mem_union_right _ hx))

theorem tendsto_lintegral_codeWindow_diag (M : SourceModelData) (r : ℝ) :
    Filter.Tendsto (fun k : ℕ => ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V)
        (codeWindow M.V k) (codeWindow M.V k) ∂(M.cutLaw r))
      Filter.atTop (nhds (E1Sign.exclMass M r)) := by
  rw [← iSup_codeWindow_diag_lintegral M r]
  refine tendsto_atTop_iSup fun i j hij => lintegral_mono fun ω => ?_
  exact windowSum_le_windowSum_of_subsets (cutDist M r) ω (0 : M.V)
    (monotone_codeWindow M.V hij) (monotone_codeWindow M.V hij)

/-- **The standardized Russo sums increase to `β_c (-K'(r)) exclMass`.**

The supremum in `ℝ` is taken along the monotone sequence of diagonal windows, so no supremum of
reals is commuted with anything: it is an honest limit statement, obtained from
`ENNReal.tendsto_toReal` and `Filter.Tendsto.const_mul`. -/
theorem tendsto_sum_cutEdgeDeriv_mul_pivotalFlux (M : SourceModelData) (r : ℝ)
    (hE : E1Sign.exclMass M r ≠ ⊤) :
    Filter.Tendsto (fun k : ℕ => ∑ e ∈ (codeWindow M.V k).sym2,
        M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) (codeWindow M.V k)) e)
      Filter.atTop
      (nhds ((M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal)) := by
  have h : Filter.Tendsto (fun k : ℕ => (∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V)
        (codeWindow M.V k) (codeWindow M.V k) ∂(M.cutLaw r)).toReal)
      Filter.atTop (nhds ((E1Sign.exclMass M r).toReal)) :=
    (ENNReal.tendsto_toReal hE).comp (tendsto_lintegral_codeWindow_diag M r)
  have h2 := h.const_mul ((M.betaCrit : ℝ) * (-(deriv M.K r)))
  refine h2.congr' ?_
  filter_upwards with k
  exact (M.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr
    (codeWindow M.V k) (codeWindow M.V k) r).symm

/-- **The infinite-lattice standardized excluded-flux statement.**

Two halves, both at the actual source law:

* every finite truncation/window standardized Russo sum is dominated by
  `β_c (-K'(r)) · exclMass.toReal` (`sum_cutEdgeDeriv_mul_pivotalFlux_le_exclMass`);
* along the canonical cofinal diagonal windows the standardized Russo sums converge to exactly
  that value (`tendsto_sum_cutEdgeDeriv_mul_pivotalFlux`).

A supremum form in `ℝ` is deliberately *not* stated: `ℝ` is only a conditionally complete linear
order, so `⨆` of an unbounded family of reals is `0` by the junk-value convention, and a
`⨆`-statement would silently be the wrong theorem whenever the excluded mass is infinite.
The honest formulation is the limit along the monotone cofinal sequence. -/
theorem sum_cutEdgeDeriv_mul_pivotalFlux_tendsto_and_le (M : SourceModelData) {r : ℝ}
    (hK' : deriv M.K r ≤ 0) (hE : E1Sign.exclMass M r ≠ ⊤) :
    (∀ (A X : Finset M.V), ∑ e ∈ X.sym2, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e
      ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal)
    ∧ Filter.Tendsto (fun k : ℕ => ∑ e ∈ (codeWindow M.V k).sym2,
        M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) (codeWindow M.V k)) e)
      Filter.atTop
      (nhds ((M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal)) :=
  ⟨fun A X => sum_cutEdgeDeriv_mul_pivotalFlux_le_exclMass M A X hK' hE,
    tendsto_sum_cutEdgeDeriv_mul_pivotalFlux M r hE⟩

/-- **The finite partial sums above are the partial sums of `sMomentInfFlux`.**

`sMomentInfFlux 0 A 1 M.cutProb M.cutEdgeDeriv r` is by definition the `tsum` over unordered
edges of `cutEdgeDeriv r e * pivotalFlux_r(|K_0 ∩ A|) e`, so the finite-window sums of
`sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr` are its partial sums over `X.sym2` and the
convergence statement `tendsto_sum_cutEdgeDeriv_mul_pivotalFlux` is the convergence of those
partial sums.  (No summability is claimed: the `tsum` in `ℝ` is the junk-valued one outside the
absolutely summable regime.) -/
theorem sMomentInfFlux_eq_tsum_pairIncrFlux (M : SourceModelData) (A : Finset M.V) (r : ℝ) :
    sMomentInfFlux (0 : M.V) A (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e := rfl

/-! ## 9. Removing the truncation: the untruncated window form of `exclMass` -/

theorem iSup_windowSum_eq_windowSumFull (d : V → V → Prop) [DecidableRel d] (ω : Config V)
    (o : V) (X : Finset V) :
    (⨆ A : Finset V, windowSum d ω o A X) = windowSumFull d ω o X := by
  have h : (⨆ A : Finset V, windowSum d ω o A X)
      = ⨆ A : Finset V, ∑ p ∈ X ×ˢ X, pairIncr d ω o A p.1 p.2 :=
    iSup_congr fun A => by
      rw [windowSum]
      exact (Finset.sum_product X X (fun p : V × V => pairIncr d ω o A p.1 p.2)).symm
  rw [h, ← sum_iSup_eq_iSup_sum (X ×ˢ X) (fun A p => pairIncr d ω o A p.1 p.2)
    (fun p => monotone_pairIncr_trunc d ω o p.1 p.2)]
  rw [windowSumFull]
  rw [show (∑ x ∈ X, ∑ y ∈ X, pairIncrFull d ω o x y)
      = ∑ p ∈ X ×ˢ X, pairIncrFull d ω o p.1 p.2 from
    (Finset.sum_product X X (fun p : V × V => pairIncrFull d ω o p.1 p.2)).symm]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact iSup_pairIncr_eq_pairIncrFull d ω o p.1 p.2

theorem iSup_lintegral_windowSum_eq_lintegral_windowSumFull (M : SourceModelData) (r : ℝ)
    (X : Finset M.V) :
    (⨆ A : Finset M.V, ∫⁻ ω, windowSum (cutDist M r) ω (0 : M.V) A X ∂(M.cutLaw r))
      = ∫⁻ ω, windowSumFull (cutDist M r) ω (0 : M.V) X ∂(M.cutLaw r) := by
  rw [← lintegral_iSup_directed
    (f := fun A : Finset M.V => fun ω => windowSum (cutDist M r) ω (0 : M.V) A X)
    (fun A => (measurable_windowSum (cutDist M r) (0 : M.V) A X).aemeasurable)
    (fun A B => ⟨A ∪ B,
      fun ω => monotone_windowSum_trunc (cutDist M r) ω (0 : M.V) Finset.subset_union_left X,
      fun ω => monotone_windowSum_trunc (cutDist M r) ω (0 : M.V) Finset.subset_union_right X⟩)]
  exact lintegral_congr fun ω => iSup_windowSum_eq_windowSumFull (cutDist M r) ω (0 : M.V) X

/-- **The untruncated window form of the excluded mass.**  Removing the finite truncation `A`
first (monotone convergence) and then taking the window supremum gives `exclMass` with the full
cluster volumes `|K_c|` inside the weight. -/
theorem exclMass_eq_iSup_lintegral_windowSumFull (M : SourceModelData) (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ X : Finset M.V,
          ∫⁻ ω, windowSumFull (cutDist M r) ω (0 : M.V) X ∂(M.cutLaw r) := by
  rw [exclMass_eq_iSup_iSup_lintegral_window M r, iSup_comm]
  exact iSup_congr fun X => iSup_lintegral_windowSum_eq_lintegral_windowSumFull M r X

/-! ## 10. The untruncated per-edge decomposition of `exclMass` -/

theorem measurable_pairIncrFull (d : V → V → Prop) [DecidableRel d] (o : V) (b c : V) :
    Measurable fun ω : Config V => pairIncrFull d ω o b c := by
  have h1 : Measurable fun ω : Config V => (if Connects ω o b then (1 : ℝ≥0∞) else 0) :=
    measurable_connects_ite o b
  have h2 : Measurable fun ω : Config V => (if ¬ Connects ω b c then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (p := fun ω => ¬ Connects ω b c) (measurableSet_connects b c).compl
      measurable_const measurable_const
  exact ((h1.mul measurable_const).mul h2).mul (measurable_clusterVol c)

theorem measurable_edgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) (e : Sym2 V) :
    Measurable fun ω : Config V => edgeIncrFull d hd ω o e := by
  induction e using Sym2.ind with
  | _ x y =>
    have h0 : Measurable fun _ : Config V => (if d x y then (1 : ℝ≥0∞) else 0) := measurable_const
    have hxy : Measurable fun ω : Config V => (if Connects ω o x then (1 : ℝ≥0∞) else 0) :=
      measurable_connects_ite o x
    have hyx : Measurable fun ω : Config V => (if Connects ω o y then (1 : ℝ≥0∞) else 0) :=
      measurable_connects_ite o y
    have hnx : Measurable fun ω : Config V => (if ¬ Connects ω x y then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (p := fun ω => ¬ Connects ω x y) (measurableSet_connects x y).compl
        measurable_const measurable_const
    have hny : Measurable fun ω : Config V => (if ¬ Connects ω y x then (1 : ℝ≥0∞) else 0) :=
      Measurable.ite (p := fun ω => ¬ Connects ω y x) (measurableSet_connects y x).compl
        measurable_const measurable_const
    have hVy : Measurable fun ω : Config V => clusterVol ω y := measurable_clusterVol y
    have hVx : Measurable fun ω : Config V => clusterVol ω x := measurable_clusterVol x
    have h := h0.mul (((hxy.mul hnx).mul hVy).add ((hyx.mul hny).mul hVx))
    simp only [edgeIncrFull, Sym2.lift_mk]
    exact h

/-- **The untruncated per-edge decomposition of the excluded mass.**

`E1Sign.exclMass` is the sum over unordered edges of the `cutLaw r`-expectation of the full
(untruncated) edge increment.  This is the literal statement at `PivotFlux.paperSum` (via the
landed `paperSum_eq_tsum_edgeIncrFull` and `PivotFlux.lintegral_paperSum_eq_exclMass`) and at
`E1Sign.exclMass`, and it is unconditional in `ℝ≥0∞`: Tonelli for the nonnegative edge series, no
summability and no moment hypothesis. -/
theorem exclMass_eq_tsum_lintegral_edgeIncrFull (M : SourceModelData) (r : ℝ) :
    E1Sign.exclMass M r
      = ∑' e : Sym2 M.V,
          ∫⁻ ω, edgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) e
            ∂(M.cutLaw r) := by
  rw [← PivotFlux.lintegral_paperSum_eq_exclMass M r]
  rw [show (fun ω : Config M.V => PivotFlux.paperSum M r ω)
      = fun ω => ∑' e : Sym2 M.V,
          edgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) e from
    funext fun ω => paperSum_eq_tsum_edgeIncrFull M r ω]
  exact lintegral_tsum fun e =>
    (measurable_edgeIncrFull (cutDist M r) (cutDist_symm M r) (0 : M.V) e).aemeasurable

/-! ## 11. The closed-event full-cluster limit, in `ℝ≥0∞`

The finite-window identity `sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr` is a statement at
truncation `A`.  Removing `A` on the right is `iSup_pairIncr_eq_pairIncrFull`; removing it on the
left requires passing the closed-event factorisation `one_sub_mul_pivotalFlux_eq` through the
truncation supremum.  The next three lemmas do exactly that, and they are the precise
"missing closed-event full-cluster limit": it holds in `ℝ≥0∞`, and it does **not** survive a
round trip through `ℝ` when the far cluster is infinite (§12). -/

theorem iSup_edgeIncr_eq_edgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (e : Sym2 V) :
    (⨆ A : Finset V, edgeIncr d hd ω o A e) = edgeIncrFull d hd ω o e := by
  induction e using Sym2.ind with
  | _ x y =>
    have h : (⨆ A : Finset V, edgeIncr d hd ω o A s(x, y))
        = ⨆ A : Finset V, (pairIncr d ω o A x y + pairIncr d ω o A y x) :=
      iSup_congr fun A => edgeIncr_mk d hd ω o A x y
    rw [h, ← iSup_add_iSup_of_monotone (monotone_pairIncr_trunc d ω o x y)
        (monotone_pairIncr_trunc d ω o y x),
      iSup_pairIncr_eq_pairIncrFull d ω o x y, iSup_pairIncr_eq_pairIncrFull d ω o y x,
      edgeIncrFull_mk]

namespace SourceModelData

variable (M : SourceModelData)

/-- **The closed-event factorization at truncation `A`, in `ℝ≥0∞`.**

`(1 - q_e(r)) · pivotalFlux_r(|K_0 ∩ A|) e` is the `cutLaw r`-integral of the `ℝ≥0∞` edge
increment.  Both directions of the conversion are guarded: `edgeIncr` is bounded by `2|A|`, so
`ofReal` and `toReal` are mutually inverse here. -/
theorem ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncr (A : Finset M.V) (r : ℝ)
    {x y : M.V} (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    ENNReal.ofReal ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y))
      = ∫⁻ ω, edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)
          ∂(M.cutLaw r) := by
  have hlaw : M.cutLaw r = PercLib.Percolation.Bond.law (M.cutProb r) := M.cutLaw_eq_edgeMeasure r
  have hC : ∀ ω : Config M.V,
      |sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω| ≤ (A.card : ℝ) := by
    intro ω
    simpa using abs_sMomentTrunc_le (fun _ => (1 : ℝ)) (0 : M.V) A ω
  have hflip := one_sub_mul_pivotalFlux_eq (M.cutProb r) s(x, y)
    (measurable_sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) hC
  rw [hlaw]
  rw [hflip]
  rw [← hlaw]
  have hpt : ∀ ω : Config M.V,
      (if s(x, y) ∈ ω then (0 : ℝ) else
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)})
            - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω))
        = (if s(x, y) ∈ ω then (0 : ℝ) else exclIncr ω (0 : M.V) A x y) := by
    intro ω
    by_cases h : s(x, y) ∈ ω
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      exact sMomentTrunc_union_edge_sub A (0 : M.V) ω hxy
  have hpt2 : ∀ ω : Config M.V,
      (if s(x, y) ∈ ω then (0 : ℝ) else exclIncr ω (0 : M.V) A x y)
        = (edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal := by
    intro ω
    have hyx : cutDist M r y x := (cutDist_symm M r x y).mp hdist
    rw [← ofReal_closed_exclIncr_eq_edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A x y
      hyx]
    refine (ENNReal.toReal_ofReal ?_).symm
    by_cases h : s(x, y) ∈ ω
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact exclIncr_nonneg ω (0 : M.V) A x y
  have hEq : (∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)})
          - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω)) ∂(M.cutLaw r))
      = (∫⁻ ω, edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)
          ∂(M.cutLaw r)).toReal := by
    rw [show (∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)})
            - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω)) ∂(M.cutLaw r))
        = ∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else exclIncr ω (0 : M.V) A x y)
            ∂(M.cutLaw r) from integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [show (∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else exclIncr ω (0 : M.V) A x y)
          ∂(M.cutLaw r))
        = ∫ ω, (edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal
            ∂(M.cutLaw r) from integral_congr_ae (Filter.Eventually.of_forall hpt2)]
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      ((measurable_edgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A s(x, y)).ennreal_toReal
        |>.aestronglyMeasurable)]
    exact congrArg ENNReal.toReal (lintegral_congr fun ω =>
      ENNReal.ofReal_toReal
        (edgeIncr_ne_top (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)))
  rw [hEq, ENNReal.ofReal_toReal (M.lintegral_edgeIncr_ne_top A r s(x, y))]

/-- **The closed-event full-cluster limit in `ℝ≥0∞`.**

Taking `A → ∞` (over all finite vertex sets) of the closed-event factorization gives exactly the
`cutLaw r`-integral of the *untruncated* edge increment.  This is the limit lemma that the
finite-window identity was missing; it is stated at the actual source law and needs the distance
support `dist x y ≤ r` (outside it the flip increment is nonzero while `edgeIncr` vanishes). -/
theorem iSup_ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncrFull (r : ℝ) {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    (⨆ A : Finset M.V, ENNReal.ofReal ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)))
      = ∫⁻ ω, edgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
          ∂(M.cutLaw r) := by
  have hstep : (⨆ A : Finset M.V, ENNReal.ofReal
        ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
          pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)))
      = ⨆ A : Finset M.V, ∫⁻ ω,
          edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y) ∂(M.cutLaw r) :=
    iSup_congr fun A => M.ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncr A r hxy hdist
  rw [hstep, ← lintegral_iSup_directed
    (f := fun A : Finset M.V => fun ω =>
      edgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y))
    (fun A => (measurable_edgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A s(x, y)).aemeasurable)
    (fun A B => ⟨A ∪ B,
      fun ω => edgeIncr_subset Finset.subset_union_left (cutDist M r) (cutDist_symm M r) ω
        (0 : M.V) s(x, y),
      fun ω => edgeIncr_subset Finset.subset_union_right (cutDist M r) (cutDist_symm M r) ω
        (0 : M.V) s(x, y)⟩)]
  exact lintegral_congr fun ω =>
    iSup_edgeIncr_eq_edgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)

/-- **The honest conditional per-edge statement at the full cluster volume.**

For a genuine edge of length `≤ r`, every finite truncation of the closed-event standardized flux
is bounded by the `cutLaw r`-expectation of the *untruncated* edge increment, **provided** that
expectation is finite.  The finiteness is a real hypothesis: with `∫⁻ edgeIncrFull = ⊤` the
right-hand side would be `0` (`ENNReal.toReal_top`) and the inequality would be false for any
nonzero flux.  Passing from this bound to an exact per-edge identity would additionally require a
real-valued full cluster moment, which does not exist (see §12). -/
theorem one_sub_mul_pivotalFlux_le_lintegral_edgeIncrFull (r : ℝ) {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r)
    (hfin : ∫⁻ ω, edgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
      ∂(M.cutLaw r) ≠ ⊤) (A : Finset M.V) :
    (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y)
      ≤ (∫⁻ ω, edgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
          ∂(M.cutLaw r)).toReal := by
  have hle : ENNReal.ofReal ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
      pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y))
      ≤ ∫⁻ ω, edgeIncrFull (cutDist M r) (cutDist_symm M r) ω (0 : M.V) s(x, y)
          ∂(M.cutLaw r) := by
    rw [← M.iSup_ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncrFull r hxy hdist]
    exact le_iSup (fun A : Finset M.V => ENNReal.ofReal
      ((1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) s(x, y))) A
  rwa [ENNReal.ofReal_le_iff_le_toReal hfin] at hle

end SourceModelData

/-! ## 12. The obstruction: no real-valued full-cluster per-edge identity

`ℝ≥0∞` subtraction is truncated, so the *increment* of a full cluster volume is not a real
function of the configuration: if the far cluster is infinite, `pairIncrFull` is `⊤`, while any
real-valued candidate `t` satisfies `ENNReal.ofReal t ≠ ⊤`.  Equivalently, the real shadow
`ENNReal.toReal` sends `⊤` to `0` (`ENNReal.toReal_top`), so `ofReal ∘ toReal` is the identity only
on the `⊤`-free part (`ofReal_toReal_eq_self_iff`).  Any per-edge identity of the form
`β_c (-K'(r)) · (real full flip moment) = ∫⁻ edgeIncrFull` therefore cannot be proved by the
closed-event factorisation alone: it needs the *a.e.* finiteness of the far cluster volume, which
is a genuine analytic input about the source model and is not available at `HEAD`. -/

/-- `ofReal` and `toReal` are mutually inverse exactly on the finite part of `ℝ≥0∞`. -/
theorem ofReal_toReal_eq_self_iff (a : ℝ≥0∞) : ENNReal.ofReal a.toReal = a ↔ a ≠ ⊤ := by
  constructor
  · intro h
    rintro rfl
    exact ENNReal.ofReal_ne_top h
  · intro h
    exact ENNReal.ofReal_toReal h

/-- A `⊤`-valued ordered-pair full increment. -/
theorem pairIncrFull_eq_top (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o b c : V)
    (hb : Connects ω o b) (hcb : d c b) (hbc : ¬ Connects ω b c)
    (hvol : clusterVol ω c = ⊤) : pairIncrFull d ω o b c = ⊤ := by
  rw [pairIncrFull, ite_eq_left hb, ite_eq_left hcb, ite_eq_left hbc, hvol, one_mul, one_mul,
    one_mul]

/-- A `⊤`-valued unordered-edge full increment. -/
theorem edgeIncrFull_eq_top (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) {x y : V}
    (hb : Connects ω o x) (hyx : d y x) (hnc : ¬ Connects ω x y)
    (hvol : clusterVol ω y = ⊤) : edgeIncrFull d hd ω o s(x, y) = ⊤ := by
  rw [edgeIncrFull_mk, pairIncrFull_eq_top d ω o x y hb hyx hnc hvol]
  simp

/-- **The obstruction, in the sharp form used by the write-up.**  At a configuration whose far
cluster is infinite (and where the excluded pattern holds), there is **no** real number `t` whose
`ENNReal.ofReal` is the full edge increment.  So the full-cluster per-edge identity cannot be
stated in `ℝ` with a `pivotalFlux` of a real-valued full moment, and the closed-event
factorisation of `one_sub_mul_pivotalFlux_eq` (which is a real identity) cannot be pushed to the
full cluster volume without an a.e. finiteness hypothesis. -/
theorem not_exists_real_eq_edgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) {x y : V}
    (hb : Connects ω o x) (hyx : d y x) (hnc : ¬ Connects ω x y)
    (hvol : clusterVol ω y = ⊤) :
    ¬ ∃ t : ℝ, ENNReal.ofReal t = edgeIncrFull d hd ω o s(x, y) := by
  rintro ⟨t, ht⟩
  rw [edgeIncrFull_eq_top d hd ω o hb hyx hnc hvol] at ht
  exact ENNReal.ofReal_ne_top ht

/-- The obstruction is not vacuous as a phenomenon on an infinite vertex set: the all-open
configuration has full cluster volume `⊤` at every vertex, so the `⊤`-valuedness of the untruncated
increments genuinely occurs.  (The all-open configuration is connected everywhere, so it does not
itself exhibit the excluded pattern; exhibiting both at once needs a configuration with an infinite
cluster and a disconnected far endpoint, which is not constructed here.) -/
theorem conn_univ (a b : V) : Connects (Set.univ : Config V) a b := by
  by_cases hab : a = b
  · subst hab; exact connects_refl _ _
  · exact SimpleGraph.Adj.reachable (openGraph_adj.mpr ⟨hab, Set.mem_univ _⟩)

theorem cluster_univ (c : V) : cluster (Set.univ : Config V) c = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  exact mem_cluster_iff.mpr (conn_univ c v)

theorem inInfiniteCluster_univ [Infinite V] (c : V) :
    InInfiniteCluster (Set.univ : Config V) c :=
  (inInfiniteCluster_iff_infinite _ c).mpr (by
    rw [cluster_univ]
    exact Set.infinite_univ)

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit (Part II) -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.monotone_windowSum_window
#print axioms PercLib.CriticalLRP.Orchestration.monotone_windowSum_trunc
#print axioms PercLib.CriticalLRP.Orchestration.windowSum_le_windowSum_of_subsets
#print axioms PercLib.CriticalLRP.Orchestration.measurable_windowSum
#print axioms PercLib.CriticalLRP.Orchestration.iSup_windowSum_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.iSup_lintegral_windowSum
#print axioms PercLib.CriticalLRP.Orchestration.exclMass_eq_iSup_iSup_lintegral_window
#print axioms PercLib.CriticalLRP.Orchestration.lintegral_windowSum_le_exclMass
#print axioms PercLib.CriticalLRP.Orchestration.sum_cutEdgeDeriv_mul_pivotalFlux_le_exclMass
#print axioms PercLib.CriticalLRP.Orchestration.iSup_codeWindow_diag_lintegral
#print axioms PercLib.CriticalLRP.Orchestration.tendsto_lintegral_codeWindow_diag
#print axioms PercLib.CriticalLRP.Orchestration.tendsto_sum_cutEdgeDeriv_mul_pivotalFlux
#print axioms PercLib.CriticalLRP.Orchestration.sum_cutEdgeDeriv_mul_pivotalFlux_tendsto_and_le
#print axioms PercLib.CriticalLRP.Orchestration.sMomentInfFlux_eq_tsum_pairIncrFlux
#print axioms PercLib.CriticalLRP.Orchestration.iSup_windowSum_eq_windowSumFull
#print axioms PercLib.CriticalLRP.Orchestration.iSup_lintegral_windowSum_eq_lintegral_windowSumFull
#print axioms PercLib.CriticalLRP.Orchestration.exclMass_eq_iSup_lintegral_windowSumFull
#print axioms PercLib.CriticalLRP.Orchestration.measurable_pairIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.measurable_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.exclMass_eq_tsum_lintegral_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.iSup_edgeIncr_eq_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.iSup_ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_sub_mul_pivotalFlux_le_lintegral_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_toReal_eq_self_iff
#print axioms PercLib.CriticalLRP.Orchestration.pairIncrFull_eq_top
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncrFull_eq_top
#print axioms PercLib.CriticalLRP.Orchestration.not_exists_real_eq_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.conn_univ
#print axioms PercLib.CriticalLRP.Orchestration.cluster_univ
#print axioms PercLib.CriticalLRP.Orchestration.inInfiniteCluster_univ

end PercLib.CriticalLRP.Orchestration
