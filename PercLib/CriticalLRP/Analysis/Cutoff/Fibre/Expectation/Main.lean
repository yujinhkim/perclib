/-
Swarm `smwu10gjo`, member `m3`, direction A (expectation-level finite-truncation fibre assembly).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.PaperSumLimit
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Expectation.Defs

/-!
# Expectation-level finite-truncation assembly of the excluded mass

At `HEAD`, `PercLib.CriticalLRP.Orchestration.paperSum_eq_iSup_tsum_pairIncr` identifies the paper's
double sum pointwise with the supremum over finite vertex truncations of the summed ordered-pair
excluded increment, and `PivotFlux.lintegral_paperSum_eq_exclMass` identifies its
`cutLaw r`-integral with `E1Sign.exclMass M r` (unconditionally, in `ℝ≥0∞`).  This file performs
the *expectation*-level step: the truncation supremum is taken under the measure, by genuine
monotone convergence
(`MeasureTheory.lintegral_iSup_directed`, which needs the countable index `Finset M.V` and
`Directed (· ≤ ·)` of the truncations), not by an algebraic rewrite.

Main results (all unconditional in `ℝ≥0∞`, no finite moment):

* `exclMass_eq_iSup_lintegral_pairIncr` :
  `E1Sign.exclMass M r = ⨆ A : Finset M.V, ∫⁻ ω, Σ'_p pairIncr (cutDist M r) ω 0 A p.1 p.2`;
* `exclMass_eq_iSup_tsum_lintegral_pairIncr` : the doubled per-pair expectation form, obtained by
  Tonelli (`lintegral_tsum`) for the nonnegative `ℝ≥0∞` sum over the countable pair index;
* `exclMass_eq_iSup_tsum_tsum_lintegral_pairIncr` : the same as an iterated double sum;
* `exclMass_eq_iSup_lintegral_edgeIncr` / `exclMass_eq_iSup_tsum_lintegral_edgeIncr` : the
  `Sym2` edge form, where each edge carries its two ordered-pair contributions;
* sequential (window) forms with the cofinal windows of `Defs`, including the honest truncation
  limit `tendsto_lintegral_window`;
* the real wrapper `toReal_exclMass_eq_iSup_toReal_window`, which needs `exclMass ≠ ⊤` — exactly the
  finiteness that the `ℝ≥0∞` statements do not need.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Measurability of the fibre integrands in the configuration

Each factor is either a constant, the indicator of a measurable connectivity event
(`measurableSet_connects`), or the truncated cluster volume (`measurable_sMomentTruncENN`). -/

/-- The connectivity indicator is a measurable function of the configuration. -/
theorem measurable_connects_ite (o b : V) :
    Measurable fun ω : Config V => (if Connects ω o b then (1 : ℝ≥0∞) else 0) :=
  Measurable.ite (measurableSet_connects o b) measurable_const measurable_const

/-- The ordered-pair excluded increment is a measurable function of the configuration. -/
theorem measurable_pairIncr (d : V → V → Prop) [DecidableRel d] (o : V) (A : Finset V)
    (b c : V) : Measurable fun ω : Config V => pairIncr d ω o A b c := by
  have h1 : Measurable fun ω : Config V => (if Connects ω o b then (1 : ℝ≥0∞) else 0) :=
    measurable_connects_ite o b
  have h2 : Measurable fun _ : Config V => (if d c b then (1 : ℝ≥0∞) else 0) := measurable_const
  have h3 : Measurable fun ω : Config V => (if ¬ Connects ω b c then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (p := fun ω => ¬ Connects ω b c) (measurableSet_connects b c).compl
      measurable_const measurable_const
  have h4 : Measurable fun ω : Config V => sMomentTruncENN (fun _ => (1 : ℝ)) c A ω :=
    measurable_sMomentTruncENN (fun _ => (1 : ℝ)) c A
  exact ((h1.mul h2).mul h3).mul h4

/-- The summed ordered-pair excluded increment is a measurable function of the configuration. -/
theorem measurable_tsum_pairIncr (d : V → V → Prop) [DecidableRel d] (o : V) (A : Finset V) :
    Measurable fun ω : Config V => ∑' p : V × V, pairIncr d ω o A p.1 p.2 :=
  Measurable.tsum fun p => measurable_pairIncr d o A p.1 p.2

/-- The two ordered orientations of one edge, as a measurable function of the configuration. -/
theorem measurable_edgeTerm (d : V → V → Prop) [DecidableRel d] (o : V) (A : Finset V)
    (x y : V) : Measurable fun ω : Config V =>
      (if d x y then (1 : ℝ≥0∞) else 0) *
        ((if Connects ω o x then (1 : ℝ≥0∞) else 0) *
            (if ¬ Connects ω x y then (1 : ℝ≥0∞) else 0) *
            sMomentTruncENN (fun _ => (1 : ℝ)) y A ω
          + (if Connects ω o y then (1 : ℝ≥0∞) else 0) *
            (if ¬ Connects ω y x then (1 : ℝ≥0∞) else 0) *
            sMomentTruncENN (fun _ => (1 : ℝ)) x A ω) := by
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
  have hAy : Measurable fun ω : Config V => sMomentTruncENN (fun _ => (1 : ℝ)) y A ω :=
    measurable_sMomentTruncENN (fun _ => (1 : ℝ)) y A
  have hAx : Measurable fun ω : Config V => sMomentTruncENN (fun _ => (1 : ℝ)) x A ω :=
    measurable_sMomentTruncENN (fun _ => (1 : ℝ)) x A
  exact measurable_const.mul (((hxy.mul hnx).mul hAy).add ((hyx.mul hny).mul hAx))

/-- The edge excluded increment is a measurable function of the configuration. -/
theorem measurable_edgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) (A : Finset V) (e : Sym2 V) :
    Measurable fun ω : Config V => edgeIncr d hd ω o A e := by
  induction e using Sym2.ind with
  | h x y =>
    have h := measurable_edgeTerm (V := V) d o A x y
    simpa only [edgeIncr, Sym2.lift_mk] using h

/-- The summed edge excluded increment is a measurable function of the configuration. -/
theorem measurable_tsum_edgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) (A : Finset V) :
    Measurable fun ω : Config V => ∑' e : Sym2 V, edgeIncr d hd ω o A e :=
  Measurable.tsum fun e => measurable_edgeIncr d hd o A e

/-! ## Monotonicity and directedness in the truncation set -/

theorem sMomentTruncENN_subset {A B : Finset V} (hAB : A ⊆ B) (q : V → ℝ) (o : V)
    (ω : Config V) : sMomentTruncENN q o A ω ≤ sMomentTruncENN q o B ω :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB fun _ _ _ => by simp

theorem pairIncr_subset {A B : Finset V} (hAB : A ⊆ B) (d : V → V → Prop) [DecidableRel d]
    (ω : Config V) (o b c : V) : pairIncr d ω o A b c ≤ pairIncr d ω o B b c := by
  unfold pairIncr
  gcongr
  exact sMomentTruncENN_subset hAB (fun _ => (1 : ℝ)) c ω

theorem edgeIncr_subset {A B : Finset V} (hAB : A ⊆ B) (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (e : Sym2 V) :
    edgeIncr d hd ω o A e ≤ edgeIncr d hd ω o B e := by
  induction e using Sym2.ind with
  | h x y =>
    simp only [edgeIncr, Sym2.lift_mk]
    gcongr
    · exact sMomentTruncENN_subset hAB (fun _ => (1 : ℝ)) y ω
    · exact sMomentTruncENN_subset hAB (fun _ => (1 : ℝ)) x ω

theorem tsum_pairIncr_subset {A B : Finset V} (hAB : A ⊆ B) (d : V → V → Prop) [DecidableRel d]
    (o : V) (ω : Config V) :
    (∑' p : V × V, pairIncr d ω o A p.1 p.2) ≤ ∑' p : V × V, pairIncr d ω o B p.1 p.2 :=
  ENNReal.tsum_le_tsum fun p => pairIncr_subset hAB d ω o p.1 p.2

theorem tsum_edgeIncr_subset {A B : Finset V} (hAB : A ⊆ B) (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) (ω : Config V) :
    (∑' e : Sym2 V, edgeIncr d hd ω o A e) ≤ ∑' e : Sym2 V, edgeIncr d hd ω o B e :=
  ENNReal.tsum_le_tsum fun e => edgeIncr_subset hAB d hd ω o e

theorem monotone_tsum_pairIncr (d : V → V → Prop) [DecidableRel d] (o : V) (ω : Config V) :
    Monotone fun A : Finset V => ∑' p : V × V, pairIncr d ω o A p.1 p.2 :=
  fun _ _ hAB => tsum_pairIncr_subset hAB d o ω

theorem monotone_tsum_edgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) (ω : Config V) :
    Monotone fun A : Finset V => ∑' e : Sym2 V, edgeIncr d hd ω o A e :=
  fun _ _ hAB => tsum_edgeIncr_subset hAB d hd o ω

theorem directed_tsum_pairIncr (d : V → V → Prop) [DecidableRel d] (o : V) :
    Directed (· ≤ ·) fun A : Finset V => fun ω : Config V =>
      ∑' p : V × V, pairIncr d ω o A p.1 p.2 :=
  fun A B => ⟨A ∪ B, fun ω => monotone_tsum_pairIncr d o ω Finset.subset_union_left,
    fun ω => monotone_tsum_pairIncr d o ω Finset.subset_union_right⟩

theorem directed_tsum_edgeIncr (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (o : V) :
    Directed (· ≤ ·) fun A : Finset V => fun ω : Config V =>
      ∑' e : Sym2 V, edgeIncr d hd ω o A e :=
  fun A B => ⟨A ∪ B, fun ω => monotone_tsum_edgeIncr d hd o ω Finset.subset_union_left,
    fun ω => monotone_tsum_edgeIncr d hd o ω Finset.subset_union_right⟩

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable (M : SourceModelData)

/-! ## The truncated expectation is monotone in the truncation set

The monotone family of `ℝ≥0∞`-valued expectations to which the monotone convergence theorem is
applied below.  Monotonicity is *pointwise* in the integrand (`pairIncr_subset`), so no moment
finiteness enters. -/

theorem monotone_lintegral_tsum_pairIncr (r : ℝ) :
    Monotone fun A : Finset M.V =>
      ∫⁻ ω, (∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2) ∂(M.cutLaw r) :=
  fun _ _ hAB => lintegral_mono fun ω => tsum_pairIncr_subset hAB (cutDist M r) 0 ω

theorem monotone_lintegral_tsum_edgeIncr (r : ℝ) :
    Monotone fun A : Finset M.V =>
      ∫⁻ ω, (∑' e : Sym2 M.V, edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e)
        ∂(M.cutLaw r) :=
  fun _ _ hAB =>
    lintegral_mono fun ω => tsum_edgeIncr_subset hAB (cutDist M r) (cutDist_symm M r) 0 ω

/-! ## The expectation-level truncation identity (ordered-pair form)

This is the actual interchange of `⨆_{A}` with `∫⁻`, via monotone convergence: the landed pointwise
identity `paperSum = ⨆ A, Σ'_p pairIncr …` is transported under `cutLaw r` using
`MeasureTheory.lintegral_iSup_directed`, whose side conditions are measurability of each finite
truncation (`measurable_tsum_pairIncr`) and directedness of the truncations
(`directed_tsum_pairIncr`). -/

/-- **Expectation-level finite-truncation identity of the excluded mass.** -/
theorem exclMass_eq_iSup_lintegral_pairIncr (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ A : Finset M.V,
          ∫⁻ ω, (∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2)
            ∂(M.cutLaw r) := by
  calc E1Sign.exclMass M r
      = ∫⁻ ω, PivotFlux.paperSum M r ω ∂(M.cutLaw r) :=
        (PivotFlux.lintegral_paperSum_eq_exclMass M r).symm
    _ = ∫⁻ ω, ⨆ A : Finset M.V,
          (∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2) ∂(M.cutLaw r) :=
        lintegral_congr fun ω => paperSum_eq_iSup_tsum_pairIncr M r ω
    _ = ⨆ A : Finset M.V,
          ∫⁻ ω, (∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2)
            ∂(M.cutLaw r) :=
        lintegral_iSup_directed
          (fun A => (measurable_tsum_pairIncr (cutDist M r) 0 A).aemeasurable)
          (directed_tsum_pairIncr (cutDist M r) 0)

/-- **Doubled per-pair expectation form.**  Tonelli (`lintegral_tsum`) for the nonnegative sum over
the countable ordered-pair index moves the expectation inside the fibre sum. -/
theorem exclMass_eq_iSup_tsum_lintegral_pairIncr (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ A : Finset M.V, ∑' p : M.V × M.V,
          ∫⁻ ω, pairIncr (cutDist M r) ω 0 A p.1 p.2 ∂(M.cutLaw r) := by
  rw [exclMass_eq_iSup_lintegral_pairIncr M r]
  refine iSup_congr fun A => ?_
  exact lintegral_tsum fun p => (measurable_pairIncr (cutDist M r) 0 A p.1 p.2).aemeasurable

/-- The same doubled form written as an iterated double sum over the two ordered-pair indices. -/
theorem exclMass_eq_iSup_tsum_tsum_lintegral_pairIncr (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ A : Finset M.V, ∑' b : M.V, ∑' c : M.V,
          ∫⁻ ω, pairIncr (cutDist M r) ω 0 A b c ∂(M.cutLaw r) := by
  rw [exclMass_eq_iSup_tsum_lintegral_pairIncr M r]
  refine iSup_congr fun A => ?_
  exact ENNReal.tsum_prod (f := fun b c => ∫⁻ ω, pairIncr (cutDist M r) ω 0 A b c
    ∂(M.cutLaw r))

/-! ## The expectation-level truncation identity (edge form)

`edgeIncr` is the `Sym2`-indexed form of the excluded increment, i.e. each edge carries the two
ordered contributions of the pair weight.  The same monotone convergence argument applies; the only
new input is measurability of the edge increment (`measurable_tsum_edgeIncr`). -/

/-- **Expectation-level finite-truncation identity, `Sym2` edge form.** -/
theorem exclMass_eq_iSup_lintegral_edgeIncr (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ A : Finset M.V,
          ∫⁻ ω, (∑' e : Sym2 M.V,
            edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e) ∂(M.cutLaw r) := by
  calc E1Sign.exclMass M r
      = ∫⁻ ω, PivotFlux.paperSum M r ω ∂(M.cutLaw r) :=
        (PivotFlux.lintegral_paperSum_eq_exclMass M r).symm
    _ = ∫⁻ ω, ⨆ A : Finset M.V,
          (∑' e : Sym2 M.V, edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e)
            ∂(M.cutLaw r) :=
        lintegral_congr fun ω => paperSum_eq_iSup_tsum_edgeIncr M r ω
    _ = ⨆ A : Finset M.V,
          ∫⁻ ω, (∑' e : Sym2 M.V,
            edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e) ∂(M.cutLaw r) :=
        lintegral_iSup_directed
          (fun A => (measurable_tsum_edgeIncr (cutDist M r) (cutDist_symm M r) 0 A).aemeasurable)
          (directed_tsum_edgeIncr (cutDist M r) (cutDist_symm M r) 0)

/-- **Doubled per-edge expectation form.** -/
theorem exclMass_eq_iSup_tsum_lintegral_edgeIncr (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ A : Finset M.V, ∑' e : Sym2 M.V,
          ∫⁻ ω, edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e ∂(M.cutLaw r) := by
  rw [exclMass_eq_iSup_lintegral_edgeIncr M r]
  refine iSup_congr fun A => ?_
  exact lintegral_tsum fun e =>
    (measurable_edgeIncr (cutDist M r) (cutDist_symm M r) 0 A e).aemeasurable

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable (M : SourceModelData)

/-! ## Sequential form: the explicit cofinal window sequence

`Defs.codeWindow` is the monotone exhausting sequence `{v | code v ≤ k}` of finite vertex sets.
Replacing the `Finset`-indexed supremum by this sequence turns the truncation identity into an
honest sequential limit of expectations (`tendsto_lintegral_codeWindow`). -/

/-- The expectation-level truncation identity along the canonical window sequence. -/
theorem exclMass_eq_iSup_lintegral_codeWindow (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ k : ℕ, ∫⁻ ω, (∑' p : M.V × M.V,
          pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2) ∂(M.cutLaw r) := by
  rw [exclMass_eq_iSup_lintegral_pairIncr M r]
  exact (iSup_codeWindow_eq M.V _ (monotone_lintegral_tsum_pairIncr M r)).symm

/-- The window expectations converge to the supremum over all finite truncations. -/
theorem tendsto_lintegral_codeWindow_iSup (r : ℝ) :
    Filter.Tendsto (fun k : ℕ => ∫⁻ ω, (∑' p : M.V × M.V,
        pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2) ∂(M.cutLaw r))
      Filter.atTop
      (nhds (⨆ A : Finset M.V, ∫⁻ ω, (∑' p : M.V × M.V,
        pairIncr (cutDist M r) ω 0 A p.1 p.2) ∂(M.cutLaw r))) :=
  tendsto_codeWindow M.V _ (monotone_lintegral_tsum_pairIncr M r)

/-- **The expectation-level truncation limit.**  The truncated expectations converge to the
excluded mass.  This is a genuine limit statement about `ℝ≥0∞`-valued expectations: no finiteness,
no derivative, and no interchange beyond monotone convergence is used. -/
theorem tendsto_lintegral_codeWindow (r : ℝ) :
    Filter.Tendsto (fun k : ℕ => ∫⁻ ω, (∑' p : M.V × M.V,
        pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2) ∂(M.cutLaw r))
      Filter.atTop (nhds (E1Sign.exclMass M r)) := by
  rw [exclMass_eq_iSup_lintegral_pairIncr M r]
  exact tendsto_lintegral_codeWindow_iSup M r

/-- Pointwise (configuration-wise) version of the same truncation limit: the summed ordered-pair
excluded increments converge to the paper's double sum for every configuration. -/
theorem tendsto_tsum_pairIncr_codeWindow (r : ℝ) (ω : Config M.V) :
    Filter.Tendsto (fun k : ℕ => ∑' p : M.V × M.V,
        pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2)
      Filter.atTop (nhds (PivotFlux.paperSum M r ω)) := by
  have hmono : Monotone fun k : ℕ => ∑' p : M.V × M.V,
      pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2 :=
    fun i j hij => monotone_tsum_pairIncr (cutDist M r) 0 ω (monotone_codeWindow M.V hij)
  have h := tendsto_atTop_iSup hmono
  rw [show (⨆ k : ℕ, ∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2)
      = ⨆ A : Finset M.V, ∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2 from
    iSup_codeWindow_eq M.V _ (monotone_tsum_pairIncr (cutDist M r) 0 ω)] at h
  rw [paperSum_eq_iSup_tsum_pairIncr M r ω]
  exact h

/-- Edge form of the sequential truncation identity. -/
theorem exclMass_eq_iSup_lintegral_codeWindow_edgeIncr (r : ℝ) :
    E1Sign.exclMass M r
      = ⨆ k : ℕ, ∫⁻ ω, (∑' e : Sym2 M.V,
          edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 (codeWindow M.V k) e)
            ∂(M.cutLaw r) := by
  rw [exclMass_eq_iSup_lintegral_edgeIncr M r]
  exact (iSup_codeWindow_eq M.V _ (monotone_lintegral_tsum_edgeIncr M r)).symm

/-- **The expectation-level truncation limit, `Sym2` edge form.** -/
theorem tendsto_lintegral_codeWindow_edgeIncr (r : ℝ) :
    Filter.Tendsto (fun k : ℕ => ∫⁻ ω, (∑' e : Sym2 M.V,
        edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 (codeWindow M.V k) e)
          ∂(M.cutLaw r))
      Filter.atTop (nhds (E1Sign.exclMass M r)) := by
  rw [exclMass_eq_iSup_lintegral_edgeIncr M r]
  exact tendsto_codeWindow M.V _ (monotone_lintegral_tsum_edgeIncr M r)

/-! ## The real-valued wrapper

`ENNReal.toReal` does not commute with a supremum of finite terms whose supremum is infinite, so
the real form of the truncation limit needs the finiteness of the excluded mass itself.  That is
exactly the analytic input the `ℝ≥0∞` statements avoid; the hypothesis is left explicit. -/

/-- Real form of the truncation limit, with the finiteness of the excluded mass as an explicit
hypothesis. -/
theorem toReal_exclMass_eq_iSup_toReal_codeWindow (r : ℝ) (h : E1Sign.exclMass M r ≠ ⊤) :
    (E1Sign.exclMass M r).toReal
      = ⨆ k : ℕ, (∫⁻ ω, (∑' p : M.V × M.V,
          pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2) ∂(M.cutLaw r)).toReal := by
  have hsup : (⨆ k : ℕ, ∫⁻ ω, (∑' p : M.V × M.V,
      pairIncr (cutDist M r) ω 0 (codeWindow M.V k) p.1 p.2) ∂(M.cutLaw r)) ≠ ⊤ := by
    rw [← exclMass_eq_iSup_lintegral_codeWindow M r]
    exact h
  rw [exclMass_eq_iSup_lintegral_codeWindow M r]
  exact ENNReal.toReal_iSup fun k => ne_top_of_le_ne_top hsup (le_iSup_of_le k le_rfl)

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable (M : SourceModelData)

/-! ## Corollaries: domination by the excluded mass, and pair/edge agreement

The truncation identity is a supremum, so every finite truncation is dominated by the excluded mass
(the usable form for a later domination argument), and the ordered-pair and `Sym2` edge forms have
the same expectation-level supremum. -/

/-- Every finite truncation of the ordered-pair expectation is dominated by the excluded mass. -/
theorem lintegral_tsum_pairIncr_le_exclMass (r : ℝ) (A : Finset M.V) :
    ∫⁻ ω, (∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2) ∂(M.cutLaw r)
      ≤ E1Sign.exclMass M r := by
  rw [exclMass_eq_iSup_lintegral_pairIncr M r]
  exact le_iSup (fun A : Finset M.V =>
    ∫⁻ ω, (∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2) ∂(M.cutLaw r)) A

/-- Every finite truncation of the edge expectation is dominated by the excluded mass. -/
theorem lintegral_tsum_edgeIncr_le_exclMass (r : ℝ) (A : Finset M.V) :
    ∫⁻ ω, (∑' e : Sym2 M.V, edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e)
        ∂(M.cutLaw r)
      ≤ E1Sign.exclMass M r := by
  rw [exclMass_eq_iSup_lintegral_edgeIncr M r]
  exact le_iSup (fun A : Finset M.V => ∫⁻ ω, (∑' e : Sym2 M.V,
    edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e) ∂(M.cutLaw r)) A

/-- The expectation-level ordered-pair and edge truncation suprema coincide. -/
theorem iSup_lintegral_pairIncr_eq_iSup_lintegral_edgeIncr (r : ℝ) :
    (⨆ A : Finset M.V,
        ∫⁻ ω, (∑' p : M.V × M.V, pairIncr (cutDist M r) ω 0 A p.1 p.2) ∂(M.cutLaw r))
      = ⨆ A : Finset M.V, ∫⁻ ω, (∑' e : Sym2 M.V,
          edgeIncr (cutDist M r) (cutDist_symm M r) ω 0 A e) ∂(M.cutLaw r) := by
  rw [← exclMass_eq_iSup_lintegral_pairIncr M r,
    ← exclMass_eq_iSup_lintegral_edgeIncr M r]

end PercLib.CriticalLRP.Orchestration
