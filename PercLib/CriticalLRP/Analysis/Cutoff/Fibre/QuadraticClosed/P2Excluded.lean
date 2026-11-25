/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` closed-edge conditional-expectation identity and its edge-to-vertex form

Swarm `smwvbcnfb`, member `m1`, direction `d1`.

Integration donor: `.ultramath/smwvc1d9z/m1/mirror/P2Excluded.lean`;
its two definitions were migrated to `QuadraticClosed/Defs.lean` at `a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f`.

The paper (Hutchcroft, *Critical long-range percolation I*, Lemma I.4.1, proof) writes the
infinite-volume Russo sum at `p = 2` as

  `∂_r E|K|² = β|J'(r)| Σ_{x∈K} Σ_{y∈B_r(x)} 1(y∉K) ((|K|+|K_y|)² − |K|²)`,

and then applies the mass-transport principle to turn it into
`β|J'(r)| E[ |K| Σ_{y∈B_r} 1(y∉K) ((|K|+|K_y|)² − |K|²) ]`, whose two excluded terms are
`E[|K|Σ 1(y∉K)|K_y|²] + 2 E[|K|²Σ 1(y∉K)|K_y|]`.

The landed `p = 1` packet performs this reindexing edge by edge: the factor `1 - q_e(r)` of the
literal derivative weight `M.cutEdgeDeriv r e` is not a passive scalar but cancels the
closed-edge reweighting of the flip law (`ExcludedFlux.one_sub_mul_pivotalFlux_eq`), after which
the per-edge flux of the truncated cluster moment `|K_0 ∩ A|` becomes an *excluded* increment
supported on `{0 ↔ x} ∩ {y ∉ K_0}` (`SourceModelData.cutEdgeDeriv_mul_pivotalFlux_eq_excl`),
which is then reindexed from unordered edges to ordered pairs
(`Fibre.Reindex.sum_pairs_eq_sum_sym2`).

This file performs the same two steps for the **quadratic** observation `|K_0|²`, with the
quadratic flip calculus of `RussoInf/QuadraticFlux` (`flipDiff_sq`) and the exact single-edge
merge identity of `RussoInf/Merge`:

* `sMomentTrunc_sq_union_edge_sub` — the complete pointwise law of the `p = 2` increment of the
  truncated cluster volume under opening one edge: `2|K_0∩A||K_y∩A| + |K_y∩A|²` on the excluded
  event and `0` elsewhere (the exact quadratic companion of the landed linear
  `sMomentTrunc_union_edge_sub`);
* `one_sub_mul_pivotalFlux_sq_eq` — the closed-edge conditional-expectation identity of the
  **square** flip: `(1 - q_e) · pivotalFlux ((|K_0∩A|)²) e` is the `μ`-mean of the quadratic
  increment restricted to the closed event `{e ∉ ω}`;
* `cutEdgeDeriv_mul_pivotalFlux_sq_eq_excl` — the per-edge identity at the actual source model,
  in the paper's standardized excluded form: the literal per-edge Russo flux of `|K_0 ∩ A|²` is
  `β_c(-K'(r))` times the closed-edge expectation of the **two** excluded increments
  `2|K_0∩A||K_y∩A| + |K_y∩A|²` and `2|K_0∩A||K_x∩A| + |K_x∩A|²`;
* `qPairIncr`, `qEdgeIncr` — the `p = 2` ordered-pair and unordered-edge excluded increments in
  `ℝ≥0∞`, with the diagonal splitting `qEdgeIncr s(x,y) = qPairIncr x y + qPairIncr y x` and
  vanishing on the diagonal, so that `sum_pairs_eq_sum_sym2` applies verbatim;
* `ofReal_quadIncr_closed_eq_qEdgeIncr` — the honest real-to-`ℝ≥0∞` conversion on the closed
  event (the increment there is a nonnegative real, and `qEdgeIncr` is finite);
* `cutEdgeDeriv_mul_pivotalFlux_sq_eq_qEdgeIncr` — the per-edge identity in `ℝ≥0∞` form, valid
  for **every** edge (loops and out-of-window edges included, where both sides vanish);
* `sum_cutEdgeDeriv_mul_pivotalFlux_sq_eq_sum_qPairIncr` — the finite-window identity: the sum of
  the literal per-edge fluxes over the edges of a finite vertex window is `β_c(-K'(r))` times the
  `cutLaw r`-expectation of the ordered-pair double sum
  `Σ_{x∈X} Σ_{y∈X} qPairIncr x y`.

## What is *not* claimed

Nothing here differentiates anything in `r`; no infinite edge sum is interchanged with an
integral, and no `⊤` is read as `0`.  The truncation `A` is kept: the observation `|K_0 ∩ A|²` is
bounded by `|A|²`, which is what makes the closed-edge factorisation unconditional.  The passage
`A ↑ univ` (and the identification of the resulting supremum with `M.exclMassQuad + 2 M.exclMassSqLin`
through the general-`p` mass transport `PivotFlux.lintegral_paperSumP_eq_rooted` and the pointwise
collapse `rootedSumP_two_eq`) is stated separately and is *not* proved here.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.RussoInf.Merge
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.QuadraticClosed.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Reindex
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.RussoAssembly.Main

/-!
# The `p = 2` excluded per-edge identity and its finite-window reindexing
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The `p = 2` increment of the truncated cluster volume, all cases -/

/-- **The `p = 2` increment of the truncated spatial moment under one edge flip.**

Opening the edge `s(x,y)` changes `|K_0 ∩ A|²` by exactly the source's
`2|K_0∩A||K_y∩A| + |K_y∩A|²` when `0` is already connected to `x` but not to `y`, by the
mirror expression with `x` and `y` exchanged in the opposite case, and by `0` otherwise.

This is the complete quadratic companion of the landed linear `sMomentTrunc_union_edge_sub`: the
coefficient `2` and the square are the binomial expansion `(a + b)² − a² = 2ab + b²` of the
*linear* increment `b`, not an assumption. -/
theorem sMomentTrunc_sq_union_edge_sub (A : Finset V) (o : V) (ω : Config V) {x y : V}
    (hxy : x ≠ y) :
    sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)}) ^ 2
        - sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2
      = (if Connects ω o x ∧ ¬ Connects ω o y then
          2 * sMomentTrunc (fun _ => (1 : ℝ)) o A ω * sMomentTrunc (fun _ => (1 : ℝ)) y A ω
            + sMomentTrunc (fun _ => (1 : ℝ)) y A ω ^ 2
          else 0)
        + (if Connects ω o y ∧ ¬ Connects ω o x then
          2 * sMomentTrunc (fun _ => (1 : ℝ)) o A ω * sMomentTrunc (fun _ => (1 : ℝ)) x A ω
            + sMomentTrunc (fun _ => (1 : ℝ)) x A ω ^ 2
          else 0) := by
  classical
  have key : ∀ (c₁ c₂ : Prop) [Decidable c₁] [Decidable c₂] (a b₁ b₂ : ℝ), (c₁ → ¬ c₂) →
      (a + ((if c₁ then b₁ else 0) + (if c₂ then b₂ else 0))) ^ 2 - a ^ 2
        = (if c₁ then 2 * a * b₁ + b₁ ^ 2 else 0)
          + (if c₂ then 2 * a * b₂ + b₂ ^ 2 else 0) := by
    intro c₁ c₂ _ _ a b₁ b₂ hnc
    by_cases h1 : c₁
    · have h2 : ¬ c₂ := fun h => hnc h1 h
      simp [h1, h2]
      ring
    · by_cases h2 : c₂
      · simp [h1, h2]
        ring
      · simp [h1, h2]
  set a : ℝ := sMomentTrunc (fun _ => (1 : ℝ)) o A ω with ha
  set b₁ : ℝ := sMomentTrunc (fun _ => (1 : ℝ)) y A ω with hb₁
  set b₂ : ℝ := sMomentTrunc (fun _ => (1 : ℝ)) x A ω with hb₂
  set u : ℝ := sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)}) with hu
  have hlin := sMomentTrunc_union_edge_sub (V := V) A o ω hxy
  rw [← ha, ← hb₁, ← hb₂, ← hu] at hlin
  have hrepr : u = a + ((if Connects ω o x ∧ ¬ Connects ω o y then b₁ else 0)
      + (if Connects ω o y ∧ ¬ Connects ω o x then b₂ else 0)) := by linarith
  rw [hrepr]
  exact key (Connects ω o x ∧ ¬ Connects ω o y)
    (Connects ω o y ∧ ¬ Connects ω o x) a b₁ b₂ (fun h hc => h.2 hc.1)

/-! ## 2. The closed-edge conditional expectation of the square flip -/

/-- **The `(1 - q_e)` factor is absorbed by the closed-edge event for the square functional.**

For the truncated cluster volume `|K_0 ∩ A|` (bounded by `|A|`, so the bounded-observation
hypothesis of the landed `one_sub_mul_pivotalFlux_eq` is met with `C = |A|²`), multiplying the
`p = 2` pivotal flux by the closed-edge probability `1 - q_e` gives exactly the `μ`-mean of the
quadratic increment of the *closed* configuration.

No moment finiteness, no domination and no model hypothesis enters; `A` is arbitrary and finite. -/
theorem one_sub_mul_pivotalFlux_sq_eq (π : Sym2 V → unitInterval) (o : V) (A : Finset V)
    (e : Sym2 V) :
    (1 - (π e : ℝ)) * pivotalFlux (PercLib.Percolation.Bond.law π)
        (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2) e
      = ∫ ω, (if e ∈ ω then 0 else
          (sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {e}) ^ 2
            - sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2))
        ∂(PercLib.Percolation.Bond.law π) := by
  classical
  have hG : Measurable fun ω : Config V =>
      sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2 := (measurable_sMomentTrunc _ _ _).pow_const 2
  have hC : ∀ ω : Config V,
      |sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2| ≤ ((A.card : ℝ)) ^ 2 := by
    intro ω
    have h1 : |sMomentTrunc (fun _ => (1 : ℝ)) o A ω| ≤ (A.card : ℝ) := by
      simpa using abs_sMomentTrunc_le (fun _ => (1 : ℝ)) o A ω
    have h0 : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  exact one_sub_mul_pivotalFlux_eq π e hG (C := ((A.card : ℝ)) ^ 2) hC

end PercLib.CriticalLRP.Orchestration

/-! ## 3. The per-edge `p = 2` identity at the source model, standardized excluded form -/

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

namespace SourceModelData

variable (M : SourceModelData)

/-- **The per-edge standardized `p = 2` flux identity at the actual source model.**

For a genuine edge `{x,y}` of length `≤ r` — the support of the derivative weight — the literal
per-edge Russo flux of the *square* of the truncated cluster volume is `β_c(-K'(r))` times the
closed-edge expectation of the source's quadratic increment:

`2|K_0∩A||K_y∩A| + |K_y∩A|²` on the excluded event `{0 ↔ x} ∩ {y ∉ K_0}`, `2|K_0∩A||K_x∩A| +
|K_x∩A|²` on the mirror event, and the closed-edge indicator in all cases.

Both the coefficient `2` and the squares are produced by `sMomentTrunc_sq_union_edge_sub`, i.e. by
the binomial expansion of the *linear* merge increment; the factor `exp(-β_c J_r(e)) = 1 - q_e(r)`
of `M.cutEdgeDeriv` is absorbed by the closed-edge event through
`one_sub_mul_pivotalFlux_sq_eq`.

The statement is per edge: no summability in `e`, no moment finiteness and no interchange of the
`r`-derivative with an infinite sum enters. -/
theorem cutEdgeDeriv_mul_pivotalFlux_sq_eq_excl (A : Finset M.V) {r : ℝ} {x y : M.V}
    (hxy : x ≠ y) (hdist : M.S.dist x y ≤ r) :
    M.cutEdgeDeriv r s(x, y) *
        pivotalFlux (M.cutLaw r)
          (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          ∫ ω, (if s(x, y) ∈ ω then 0 else
              ((if Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y then
                  2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                      * sMomentTrunc (fun _ => (1 : ℝ)) y A ω
                    + sMomentTrunc (fun _ => (1 : ℝ)) y A ω ^ 2
                else 0)
              + (if Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x then
                  2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                      * sMomentTrunc (fun _ => (1 : ℝ)) x A ω
                    + sMomentTrunc (fun _ => (1 : ℝ)) x A ω ^ 2
                else 0)))
            ∂(M.cutLaw r) := by
  classical
  have hcoef : M.cutEdgeDeriv r s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K r))
        * (1 - ((M.cutProb r s(x, y) : unitInterval) : ℝ)) := by
    rw [M.cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_left hdist,
      ← M.one_sub_cutProb_eq_exp r hxy hdist]
  rw [hcoef, M.cutLaw_eq_edgeMeasure, mul_assoc,
    one_sub_mul_pivotalFlux_sq_eq (V := M.V) (M.cutProb r) (0 : M.V) A s(x, y)]
  refine congrArg (fun t => (M.betaCrit : ℝ) * (-(deriv M.K r)) * t) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hpt := sMomentTrunc_sq_union_edge_sub (V := M.V) A (0 : M.V) ω hxy
  dsimp only
  by_cases h : s(x, y) ∈ ω
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    exact hpt

end SourceModelData

/-! ## 4. The `p = 2` excluded increments in `ℝ≥0∞` -/

/-- A vertex paired with itself contributes nothing: the paper's exclusion indicator
`1(b ↮ b)` fails. -/
theorem qPairIncr_self (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V)
    (A : Finset V) (x : V) : qPairIncr d ω o A x x = 0 := by
  simp [qPairIncr]

/-- The edge increment splits into its two ordered-pair orientations. -/
theorem qEdgeIncr_mk (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o : V) (A : Finset V) (x y : V) :
    qEdgeIncr d hd ω o A s(x, y) = qPairIncr d ω o A x y + qPairIncr d ω o A y x := by
  simp only [qEdgeIncr, Sym2.lift_mk]
  by_cases h : d x y
  · rw [ite_eq_left h, one_mul]
  · have h1 : ¬ d y x := fun hh => h ((hd y x).mp hh)
    rw [ite_eq_right h, zero_mul, qPairIncr, qPairIncr]
    simp [h, h1]

/-- The ordered-pair `p = 2` increment is measurable in the configuration. -/
theorem measurable_qPairIncr (d : V → V → Prop) [DecidableRel d] (o : V) (A : Finset V) (b c : V) :
    Measurable fun ω : Config V => qPairIncr d ω o A b c := by
  have h1 : Measurable fun ω : Config V => (if Connects ω o b then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_connects o b) measurable_const measurable_const
  have h3 : Measurable fun ω : Config V => (if ¬ Connects ω b c then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_connects b c).compl measurable_const measurable_const
  have h5 : Measurable fun ω : Config V => sMomentTruncENN (fun _ => (1 : ℝ)) c A ω :=
    measurable_sMomentTruncENN _ _ _
  have h4 : Measurable fun ω : Config V => sMomentTruncENN (fun _ => (1 : ℝ)) o A ω :=
    measurable_sMomentTruncENN _ _ _
  have hinner : Measurable fun ω : Config V =>
      2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
        + sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ^ 2 :=
    ((h4.const_mul 2).mul h5).add (h5.pow_const 2)
  exact (h1.mul measurable_const).mul h3 |>.mul hinner

/-- The edge `p = 2` increment is measurable in the configuration. -/
theorem measurable_qEdgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) (A : Finset V) (e : Sym2 V) :
    Measurable fun ω : Config V => qEdgeIncr d hd ω o A e := by
  induction e using Sym2.ind with
  | h x y =>
    simp only [qEdgeIncr, Sym2.lift_mk]
    exact measurable_const.mul
      ((measurable_qPairIncr (d := d) o A x y).add (measurable_qPairIncr (d := d) o A y x))

/-- The truncated spatial moment is bounded by the cardinality of the truncation. -/
theorem sMomentTruncENN_one_le_card' (c : V) (A : Finset V) (ω : Config V) :
    sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ≤ (A.card : ℝ≥0∞) := by
  simp only [sMomentTruncENN]
  calc ∑ x ∈ A, (cluster ω c).indicator (fun _ => ENNReal.ofReal (1 : ℝ)) x
      ≤ ∑ _x ∈ A, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : x ∈ cluster ω c
        · rw [Set.indicator_of_mem h]
          simp
        · rw [Set.indicator_of_notMem h]
          simp
    _ = (A.card : ℝ≥0∞) := by simp

/-- The ordered-pair `p = 2` increment is bounded by `3 |A|²`. -/
theorem qPairIncr_le (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o : V) (A : Finset V)
    (b c : V) :
    qPairIncr d ω o A b c
      ≤ 3 * ((A.card : ℝ≥0∞)) ^ 2 := by
  have hb : sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ≤ (A.card : ℝ≥0∞) := by
    exact sMomentTruncENN_one_le_card' c A ω
  have ho : sMomentTruncENN (fun _ => (1 : ℝ)) o A ω ≤ (A.card : ℝ≥0∞) := by
    exact sMomentTruncENN_one_le_card' o A ω
  have hinner : 2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
        * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
      + sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ^ 2
      ≤ 3 * ((A.card : ℝ≥0∞)) ^ 2 := by
    have h1 : 2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
          * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
        ≤ 2 * ((A.card : ℝ≥0∞)) ^ 2 := by
      calc 2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
            * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
          = 2 * (sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
              * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω) := by ring
        _ ≤ 2 * ((A.card : ℝ≥0∞) * (A.card : ℝ≥0∞)) := by gcongr
        _ = 2 * ((A.card : ℝ≥0∞)) ^ 2 := by ring
    have h2 : sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ^ 2 ≤ ((A.card : ℝ≥0∞)) ^ 2 := by
      gcongr
    calc 2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
          * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
        + sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ^ 2
        ≤ 2 * ((A.card : ℝ≥0∞)) ^ 2 + ((A.card : ℝ≥0∞)) ^ 2 := add_le_add h1 h2
      _ = 3 * ((A.card : ℝ≥0∞)) ^ 2 := by ring
  calc qPairIncr d ω o A b c
      ≤ 1 * 1 * 1 * (2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
          * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
          + sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ^ 2) := by
        rw [qPairIncr]
        gcongr
        · split <;> simp
        · split <;> simp
        · split <;> simp
    _ = 2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
          * sMomentTruncENN (fun _ => (1 : ℝ)) c A ω
          + sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ^ 2 := by rw [one_mul, one_mul, one_mul]
    _ ≤ 3 * ((A.card : ℝ≥0∞)) ^ 2 := hinner

/-- The edge `p = 2` increment is bounded by `6 |A|²`. -/
theorem qEdgeIncr_le (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o : V) (A : Finset V) (e : Sym2 V) :
    qEdgeIncr d hd ω o A e ≤ ((6 * A.card ^ 2 : ℕ) : ℝ≥0∞) := by
  induction e using Sym2.ind with
  | h x y =>
    rw [qEdgeIncr_mk]
    refine le_trans (add_le_add (qPairIncr_le d ω o A x y) (qPairIncr_le d ω o A y x)) ?_
    have hb : (3 * ((A.card : ℝ≥0∞)) ^ 2 + 3 * ((A.card : ℝ≥0∞)) ^ 2)
        = ((6 * A.card ^ 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
    rw [hb]

/-- The edge `p = 2` increment is finite. -/
theorem qEdgeIncr_ne_top (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o : V) (A : Finset V) (e : Sym2 V) :
    qEdgeIncr d hd ω o A e ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (qEdgeIncr_le d hd ω o A e)

/-! ## 5. The honest real-to-`ℝ≥0∞` conversion of the closed-edge increment -/

/-- `ofReal` of the quadratic merge increment `2ab + b²` is the `ℝ≥0∞` binomial expression. -/
theorem ofReal_two_mul_add_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (2 * a * b + b ^ 2)
      = 2 * ENNReal.ofReal a * ENNReal.ofReal b + ENNReal.ofReal b ^ 2 := by
  have h1 : (0 : ℝ) ≤ 2 * a := by linarith
  have h2 : (0 : ℝ) ≤ b ^ 2 := by positivity
  rw [ENNReal.ofReal_add (by positivity) h2, ENNReal.ofReal_pow hb]
  congr 2
  rw [show (2 : ℝ) * a * b = (2 * a) * b by ring, ENNReal.ofReal_mul h1,
    show (2 : ℝ) * a = 2 * a by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **The closed-edge `p = 2` increment in `ℝ≥0∞`.**  Pointwise in the configuration and for
*every* edge `s(x,y)` of a genuine pair with `d x y`, the `ofReal` of the increment
`1(e ∉ ω)·(|K_0∩A|² after opening e − |K_0∩A|²)` is the `ℝ≥0∞` edge increment `qEdgeIncr`.

The indicator `1(e ∈ ω)` is genuinely needed on the left: when the edge is already open, the
increment is `0` while the paper's weight must also vanish, which it does through `1(b ↮ c)`
(an open edge connects its endpoints). -/
theorem ofReal_sqIncr_closed_eq_qEdgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) {ω : Config V} {o : V} (A : Finset V) {x y : V}
    (hxy : x ≠ y) (hdxy : d x y) :
    ENNReal.ofReal (if s(x, y) ∈ ω then 0 else
        (sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)}) ^ 2
          - sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2))
      = qEdgeIncr d hd ω o A s(x, y) := by
  classical
  have hmn : ∀ (v : V), 0 ≤ sMomentTrunc (fun _ => (1 : ℝ)) v A ω :=
    fun v => sMomentTrunc_nonneg (fun _ => zero_le_one) v A ω
  -- the two excluded increments, named
  set L1 : ℝ := 2 * sMomentTrunc (fun _ => (1 : ℝ)) o A ω
      * sMomentTrunc (fun _ => (1 : ℝ)) y A ω + sMomentTrunc (fun _ => (1 : ℝ)) y A ω ^ 2
    with hL1
  set L2 : ℝ := 2 * sMomentTrunc (fun _ => (1 : ℝ)) o A ω
      * sMomentTrunc (fun _ => (1 : ℝ)) x A ω + sMomentTrunc (fun _ => (1 : ℝ)) x A ω ^ 2
    with hL2
  have hsplit := sMomentTrunc_sq_union_edge_sub (V := V) A o ω hxy
  rw [qEdgeIncr_mk]
  by_cases he : s(x, y) ∈ ω
  · -- an open edge connects its endpoints, so both exclusion indicators vanish
    have hc : Connects ω x y :=
      SimpleGraph.Adj.reachable (openGraph_adj.mpr ⟨hxy, he⟩)
    have hyx : Connects ω y x := connects_symm hc
    have h1 : qPairIncr d ω o A x y = 0 := by simp [qPairIncr, hc]
    have h2 : qPairIncr d ω o A y x = 0 := by simp [qPairIncr, hyx]
    rw [ite_eq_left he, ENNReal.ofReal_zero, h1, h2, add_zero]
  · rw [ite_eq_right he]
    by_cases hx : Connects ω o x
    · by_cases hy : Connects ω o y
      · -- both endpoints in the cluster: the increment vanishes and so does the weight
        have hc : Connects ω x y := connects_trans (connects_symm hx) hy
        have hc' : Connects ω y x := connects_symm hc
        have h1 : qPairIncr d ω o A x y = 0 := by simp [qPairIncr, hc]
        have h2 : qPairIncr d ω o A y x = 0 := by simp [qPairIncr, hc']
        have hz : sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)}) ^ 2
            - sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2 = 0 := by
          rw [hsplit]
          simp [hx, hy]
        rw [h1, h2, add_zero, hz, ENNReal.ofReal_zero]
      · -- the excluded case: `2|K_0∩A||K_y∩A| + |K_y∩A|²`
        have hc : ¬ Connects ω x y := fun h => hy (connects_trans hx h)
        have h1 : qPairIncr d ω o A x y
            = 2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
                * sMomentTruncENN (fun _ => (1 : ℝ)) y A ω
              + sMomentTruncENN (fun _ => (1 : ℝ)) y A ω ^ 2 := by
          simp [qPairIncr, hx, hy, hc, hdxy, (hd y x).mpr hdxy]
        have h2 : qPairIncr d ω o A y x = 0 := by simp [qPairIncr, hy]
        have hz : sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)}) ^ 2
            - sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2 = L1 := by
          rw [hsplit, hL1]
          simp [hx, hy]
        rw [h1, h2, add_zero, hz, hL1, ofReal_two_mul_add_sq _ _ (hmn o) (hmn y),
          ofReal_sMomentTrunc (fun _ => zero_le_one), ofReal_sMomentTrunc (fun _ => zero_le_one)]
    · by_cases hy : Connects ω o y
      · -- the mirror excluded case
        have hc : ¬ Connects ω y x := fun h => hx (connects_trans hy h)
        have h1 : qPairIncr d ω o A x y = 0 := by simp [qPairIncr, hx]
        have h2 : qPairIncr d ω o A y x
            = 2 * sMomentTruncENN (fun _ => (1 : ℝ)) o A ω
                * sMomentTruncENN (fun _ => (1 : ℝ)) x A ω
              + sMomentTruncENN (fun _ => (1 : ℝ)) x A ω ^ 2 := by
          simp [qPairIncr, hx, hy, hc, hdxy, (hd y x).mpr hdxy]
        have hz : sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)}) ^ 2
            - sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2 = L2 := by
          rw [hsplit, hL2]
          simp [hx, hy]
        rw [h1, h2, zero_add, hz, hL2, ofReal_two_mul_add_sq _ _ (hmn o) (hmn x),
          ofReal_sMomentTrunc (fun _ => zero_le_one), ofReal_sMomentTrunc (fun _ => zero_le_one)]
      · have h1 : qPairIncr d ω o A x y = 0 := by simp [qPairIncr, hx]
        have h2 : qPairIncr d ω o A y x = 0 := by simp [qPairIncr, hy]
        have hz : sMomentTrunc (fun _ => (1 : ℝ)) o A (ω ∪ {s(x, y)}) ^ 2
            - sMomentTrunc (fun _ => (1 : ℝ)) o A ω ^ 2 = 0 := by
          rw [hsplit]
          simp [hx, hy]
        rw [h1, h2, add_zero, hz, ENNReal.ofReal_zero]

end PercLib.CriticalLRP.Orchestration

/-! ## 6. The per-edge identity in `ℝ≥0∞` form, and the finite-window reindexing -/

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

namespace SourceModelData

variable (M : SourceModelData)

/-- **The per-edge `p = 2` flux identity in `ℝ≥0∞` edge-increment form.**

For *every* edge `e` (loops and edges of length `> r` included, where both sides vanish), the
literal per-edge Russo flux of the square of the truncated cluster volume is `β_c(-K'(r))` times
the `cutLaw r`-mean of the `ℝ≥0∞` quadratic edge increment `qEdgeIncr`.

The real-to-`ℝ≥0∞` conversion is honest: `qEdgeIncr` is bounded by `6|A|²`, so
`ofReal ((qEdgeIncr ω).toReal) = qEdgeIncr ω` pointwise and no `⊤` is read as `0`; the closed-edge
factorisation is `cutEdgeDeriv_mul_pivotalFlux_sq_eq_excl`. -/
theorem cutEdgeDeriv_mul_pivotalFlux_sq_eq_qEdgeIncr (A : Finset M.V) (r : ℝ) (e : Sym2 M.V) :
    M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) e
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          (∫⁻ ω, qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e
            ∂(M.cutLaw r)).toReal := by
  classical
  induction e using Sym2.ind with
  | h x y =>
    by_cases hxy : x = y
    · -- a loop: the derivative weight and the edge increment both vanish
      subst hxy
      rw [M.cutEdgeDeriv_mk, ite_eq_left rfl, zero_mul]
      have hzero : ∀ ω : Config M.V,
          qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, x) = 0 := by
        intro ω
        rw [qEdgeIncr_mk, qPairIncr_self, add_zero]
      simp only [hzero, lintegral_zero, ENNReal.toReal_zero, mul_zero]
    · by_cases hdist : M.S.dist x y ≤ r
      · -- the genuine edge: `1 - q_e` is the closed-edge probability
        rw [M.cutEdgeDeriv_mul_pivotalFlux_sq_eq_excl A hxy hdist]
        refine congrArg (fun t => (M.betaCrit : ℝ) * (-(deriv M.K r)) * t) ?_
        have hmn : ∀ (v : M.V) (ω : Config M.V),
            0 ≤ sMomentTrunc (fun _ => (1 : ℝ)) v A ω := fun v ω =>
          sMomentTrunc_nonneg (fun _ => zero_le_one) v A ω
        -- the nonnegativity of the closed-edge quadratic increment, in closed form
        have hYnn : ∀ ω : Config M.V, (0 : ℝ) ≤
            (if s(x, y) ∈ ω then 0 else
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
                ((if Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y then
                    2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                        * sMomentTrunc (fun _ => (1 : ℝ)) y A ω
                      + sMomentTrunc (fun _ => (1 : ℝ)) y A ω ^ 2
                  else 0)
                + (if Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x then
                    2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                        * sMomentTrunc (fun _ => (1 : ℝ)) x A ω
                      + sMomentTrunc (fun _ => (1 : ℝ)) x A ω ^ 2
                  else 0)))
              = (qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal := by
          intro ω
          have hcase : (if s(x, y) ∈ ω then (0 : ℝ) else
                ((if Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y then
                    2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                        * sMomentTrunc (fun _ => (1 : ℝ)) y A ω
                      + sMomentTrunc (fun _ => (1 : ℝ)) y A ω ^ 2
                  else 0)
                + (if Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x then
                    2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                        * sMomentTrunc (fun _ => (1 : ℝ)) x A ω
                      + sMomentTrunc (fun _ => (1 : ℝ)) x A ω ^ 2
                  else 0)))
              = (if s(x, y) ∈ ω then 0 else
                  (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A (ω ∪ {s(x, y)}) ^ 2
                    - sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2)) := by
            by_cases h : s(x, y) ∈ ω
            · rw [ite_eq_left h, ite_eq_left h]
            · rw [ite_eq_right h, ite_eq_right h,
                sMomentTrunc_sq_union_edge_sub (V := M.V) A (0 : M.V) ω hxy]
          rw [hcase, ← ofReal_sqIncr_closed_eq_qEdgeIncr (cutDist M r) (cutDist_symm M r)
            (o := (0 : M.V)) A hxy (show cutDist M r x y from hdist)]
          exact (ENNReal.toReal_ofReal (hYnn ω)).symm
        have hEq : (∫ ω, (if s(x, y) ∈ ω then (0 : ℝ) else
              ((if Connects ω (0 : M.V) x ∧ ¬ Connects ω (0 : M.V) y then
                  2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                      * sMomentTrunc (fun _ => (1 : ℝ)) y A ω
                    + sMomentTrunc (fun _ => (1 : ℝ)) y A ω ^ 2
                else 0)
              + (if Connects ω (0 : M.V) y ∧ ¬ Connects ω (0 : M.V) x then
                  2 * sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω
                      * sMomentTrunc (fun _ => (1 : ℝ)) x A ω
                    + sMomentTrunc (fun _ => (1 : ℝ)) x A ω ^ 2
                else 0))) ∂(M.cutLaw r))
            = ∫ ω, (qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)).toReal
                ∂(M.cutLaw r) :=
          integral_congr_ae (Filter.Eventually.of_forall hpoint)
        rw [hEq, integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
          ((measurable_qEdgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A s(x, y)).ennreal_toReal
            |>.aestronglyMeasurable)]
        exact congrArg ENNReal.toReal (lintegral_congr fun ω =>
          ENNReal.ofReal_toReal
            (qEdgeIncr_ne_top (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y)))
      · -- an edge of length `> r`: both the derivative weight and the increment vanish
        rw [M.cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_right hdist, zero_mul]
        have h1 : ¬ cutDist M r x y := hdist
        have h2 : ¬ cutDist M r y x := fun h => hdist ((cutDist_symm M r y x).mp h)
        have hzero : ∀ ω : Config M.V,
            qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A s(x, y) = 0 := by
          intro ω
          rw [qEdgeIncr_mk]
          simp [qPairIncr, h1, h2]
        simp only [hzero, lintegral_zero, ENNReal.toReal_zero, mul_zero]

/-- The `cutLaw r`-integral of the quadratic edge increment is finite. -/
theorem lintegral_qEdgeIncr_ne_top (A : Finset M.V) (r : ℝ) (e : Sym2 M.V) :
    ∫⁻ ω, qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e ∂(M.cutLaw r) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_
    (lintegral_mono fun ω => qEdgeIncr_le (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e)
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.natCast_ne_top _

/-- **The finite-window `p = 2` reindexing identity.**

For a finite vertex window `X` and a finite truncation `A`, the sum over the edges inside `X` of
the literal per-edge Russo fluxes of the square of the truncated cluster volume is `β_c(-K'(r))`
times the `cutLaw r`-mean of the ordered-pair double sum of the quadratic excluded increments over
`X × X`.

The ordered ↔ unordered reindexing is `sum_pairs_eq_sum_sym2` applied to `qPairIncr` (which
vanishes on the diagonal) and `qEdgeIncr` (which splits over an edge into its two orientations).
No summability, no moment finiteness and no derivative interchange enters. -/
theorem sum_cutEdgeDeriv_mul_pivotalFlux_sq_eq_sum_qPairIncr (A X : Finset M.V) (r : ℝ) :
    ∑ e ∈ X.sym2, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A ω ^ 2) e
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
          (∫⁻ ω, (∑ x ∈ X, ∑ y ∈ X,
            qPairIncr (cutDist M r) ω (0 : M.V) A x y) ∂(M.cutLaw r)).toReal := by
  classical
  rw [Finset.sum_congr rfl (fun e _ => M.cutEdgeDeriv_mul_pivotalFlux_sq_eq_qEdgeIncr A r e)]
  rw [← Finset.mul_sum]
  refine congrArg (fun t => (M.betaCrit : ℝ) * (-(deriv M.K r)) * t) ?_
  rw [← ENNReal.toReal_sum (fun e _ => M.lintegral_qEdgeIncr_ne_top A r e)]
  rw [← lintegral_finsetSum (μ := M.cutLaw r)
    (f := fun e ω => qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e)
    (s := X.sym2)
    (fun e _ => measurable_qEdgeIncr (cutDist M r) (cutDist_symm M r) (0 : M.V) A e)]
  exact congrArg ENNReal.toReal (lintegral_congr fun ω =>
    (sum_pairs_eq_sum_sym2 (φ := fun x y => qPairIncr (cutDist M r) ω (0 : M.V) A x y)
      (ε := fun e => qEdgeIncr (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A e)
      (fun x => qPairIncr_self (cutDist M r) ω (0 : M.V) A x)
      (fun x y => qEdgeIncr_mk (cutDist M r) (cutDist_symm M r) ω (0 : M.V) A x y) X).symm)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.sMomentTrunc_sq_union_edge_sub
#print axioms PercLib.CriticalLRP.Orchestration.one_sub_mul_pivotalFlux_sq_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_sq_eq_excl
#print axioms PercLib.CriticalLRP.Orchestration.qPairIncr
#print axioms PercLib.CriticalLRP.Orchestration.qEdgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.qPairIncr_self
#print axioms PercLib.CriticalLRP.Orchestration.qEdgeIncr_mk
#print axioms PercLib.CriticalLRP.Orchestration.measurable_qPairIncr
#print axioms PercLib.CriticalLRP.Orchestration.measurable_qEdgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.qPairIncr_le
#print axioms PercLib.CriticalLRP.Orchestration.qEdgeIncr_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_two_mul_add_sq
#print axioms PercLib.CriticalLRP.Orchestration.ofReal_sqIncr_closed_eq_qEdgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_sq_eq_qEdgeIncr
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_cutEdgeDeriv_mul_pivotalFlux_sq_eq_sum_qPairIncr

end PercLib.CriticalLRP.Orchestration
