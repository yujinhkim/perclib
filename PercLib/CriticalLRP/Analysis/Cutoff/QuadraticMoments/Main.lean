/-
Swarm `smwv9oxuv`, member `m4`, direction `d1`.

# The `p = 2` pivot increment, and the first-moment domination of the quadratic pivot series

## The obstruction this file removes

The infinite-volume Russo exchange (`RussoInf/Exchange`) controls the pivotal flux of a
functional `g` of the cluster of `o` through the *supremum* bound `m` of `g`: every pivot weight
is at most `2 m` times the probability that the flipped edge touches the cluster
(`abs_flipDiff_le`, `abs_pivotalFlux_le`, `summable_abs_weight_touch`).  At `p = 2` the
functional is `g ω = |K_o|²`, which has no finite supremum, so *every* series obtained from that
route is infinite and the exchange cannot even be stated.

The source's Lemma I.4.1 at `p = 2` keeps the exact increment

  `(|K| + |K_y|)² − |K|² = 2 |K| |K_y| + |K_y|²`

instead.  The linear factor `|K_y|` is exactly the increment of the *first* moment, so the
quadratic pivot weight is controlled by the first-moment pivot weight, for which the whole
`p = 1` machinery (and its landed total `β_c (−K') · exclMass`) is available.  That comparison is
the content of this file.

## What is proved

* `flipDiff_capSqVol_eq` — the exact quadratic increment: the flip difference of the capped
  square `(|K_o| ∧ N)²` is `A² − B²` in the capped volumes `A ≥ B` of the two configurations.
* `abs_flipDiff_capSqVol_le` — **`|flipDiff ((|K| ∧ N)²) e ω| ≤ 2 N · flipDiff (|K| ∧ N) e ω`.**
  The supremum bound `m` of the `p = 1` route is replaced by the *linear* pivot increment, with
  the explicit factor `2 N` and no finiteness hypothesis.
* `flipDiff_capVol_le_realVol` — on the event that the cluster of `o` is finite, capping costs
  nothing: `flipDiff (|K| ∧ N) ≤ flipDiff |K|`.  Hence, on that event,
  `|flipDiff ((|K|∧N)²) e ω| ≤ 2 N · flipDiff |K| e ω`, i.e. the quadratic pivot weight of the
  capped observable is bounded by the first-moment pivot weight.
* `abs_pivotalFlux_capSqVol_le` — the integrated form
  `|pivotalFlux μ ((|K|∧N)²) e| ≤ 2 N · pivotalFlux μ (|K|∧N) e`.
* `summable_abs_pivotalFlux_capSqVol`, `abs_tsum_pivotalFlux_capSqVol_le` — the comparison test
  for the quadratic pivotal *series*: summable `e ↦ |c e| · pivotalFlux μ (|K|∧N) e` implies
  summability of the quadratic series with total at most `2 N` times the linear total.

Nothing here is a statement about `d/dr E|K|²`; the remaining step (the vertex re-indexing that
turns the quadratic pivotal series into `exclMassQuad + 2 · exclMassSqLin`, and final cap removal)
is stated exactly in `REPORT.md`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.QuadraticMoments.Defs
public import PercLib.CriticalLRP.RussoInf.FluxBase

/-!
# Capped quadratic flip increments and pivotal-series domination

The exact capped-square flip difference is bounded by `2 N` times its capped linear
counterpart.  Pointwise, integral and series comparisons are proved here; cap removal and
radius differentiation remain separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.show false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace CappedMoments

variable {V : Type*} [Countable V]

/-! ### The flip of the closed state is a sub-configuration of the flip of the open state -/

theorem forceOn_closed_subset_open (e : Sym2 V) (ω : Config V) :
    forceOn {e} ∅ ω ⊆ forceOn {e} {e} ω := by
  intro x hx
  have h := hx
  simp only [forceOn] at h
  simp only [forceOn]
  rcases h with h | h
  · exact Or.inl h
  · exact absurd h (by simp)

/-- Opening one edge can only increase the cluster volume of `o`. -/
theorem clusterVol_flip_le (e : Sym2 V) (o : V) (ω : Config V) :
    clusterVol (forceOn {e} ∅ ω) o ≤ clusterVol (forceOn {e} {e} ω) o :=
  clusterVol_mono (fun _ hx => forceOn_closed_subset_open e ω hx) o

/-! ### The exact quadratic increment

`flipDiff` of the capped square is `A² − B²` with `A ≥ B ≥ 0` the capped and then the true
cluster volumes of the two flipped configurations.  The identity `A² − B² = (A − B)(A + B)` is
the source's `2 |K| |K_y| + |K_y|²` in the variables of the flip: `A − B` is the volume of the
merged far cluster, `B` (or `A`) the anchored one. -/

theorem flipDiff_capVol_eq (o : V) (N : ℝ) (e : Sym2 V) (ω : Config V) :
    flipDiff (capVol o N) e ω
      = capVol o N (forceOn {e} {e} ω) - capVol o N (forceOn {e} ∅ ω) := rfl

theorem flipDiff_capSqVol_eq (o : V) (N : ℝ) (e : Sym2 V) (ω : Config V) :
    flipDiff (capSqVol o N) e ω
      = capVol o N (forceOn {e} {e} ω) ^ 2 - capVol o N (forceOn {e} ∅ ω) ^ 2 := rfl

/-- **The capped pivot increment is at most `2 N` times the capped linear pivot increment.**

This is the exact quadratic increment of Lemma I.4.1 at `p = 2` with the cap in place: no
finiteness of the cluster, no supremum bound of the observable, and no moment enters. -/
theorem abs_flipDiff_capSqVol_le (o : V) {N : ℝ} (hN : 0 ≤ N) (e : Sym2 V) (ω : Config V) :
    |flipDiff (capSqVol o N) e ω| ≤ 2 * N * flipDiff (capVol o N) e ω := by
  set A : ℝ := capVol o N (forceOn {e} {e} ω) with hAdef
  set B : ℝ := capVol o N (forceOn {e} ∅ ω) with hBdef
  have hBA : B ≤ A := capVol_mono N (clusterVol_flip_le e o ω)
  have hA : A ≤ N := capVol_le o hN _
  have hB : 0 ≤ B := capVol_nonneg o N _
  rw [flipDiff_capSqVol_eq, flipDiff_capVol_eq, ← hAdef, ← hBdef]
  have hfac : A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ A - B),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ A + B)]
  nlinarith

/-- On a finite cluster the `ℝ≥0∞` cap is the real cap. -/
theorem capVol_eq_min {o : V} {N : ℝ} (hN : 0 ≤ N) {ω : Config V}
    (hne : clusterVol ω o ≠ ⊤) : capVol o N ω = min (realVol o ω) N := by
  rw [capVol, realVol, ENNReal.toReal_min hne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hN]

/-- **Capping costs nothing on the event that the cluster of `o` is finite.** -/
theorem flipDiff_capVol_le_realVol {o : V} {N : ℝ} (hN : 0 ≤ N) {e : Sym2 V} {ω : Config V}
    (hne : clusterVol (forceOn {e} {e} ω) o ≠ ⊤) :
    flipDiff (capVol o N) e ω ≤ flipDiff (realVol o) e ω := by
  have hneB : clusterVol (forceOn {e} ∅ ω) o ≠ ⊤ :=
    ne_top_of_le_ne_top hne (clusterVol_flip_le e o ω)
  set A : ℝ := realVol o (forceOn {e} {e} ω) with hAdef
  set B : ℝ := realVol o (forceOn {e} ∅ ω) with hBdef
  have hAB : B ≤ A := realVol_mono hne (clusterVol_flip_le e o ω)
  have hcapA : capVol o N (forceOn {e} {e} ω) = min A N := capVol_eq_min hN hne
  have hcapB : capVol o N (forceOn {e} ∅ ω) = min B N := capVol_eq_min hN hneB
  have hkey : min A N - min B N ≤ A - B := by
    have h := abs_min_sub_min_le_max (a := A) (b := N) (c := B) (d := N)
    have h2 : max |A - B| |N - N| = A - B := by
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), abs_of_nonneg (by linarith)]
    rw [h2] at h
    exact le_trans (le_abs_self _) h
  unfold flipDiff
  rw [hcapA, hcapB]
  linarith

/-- The uncapped first-moment pivot increment is nonnegative, on the finite event. -/
theorem flipDiff_realVol_nonneg {o : V} {e : Sym2 V} {ω : Config V}
    (hne : clusterVol (forceOn {e} {e} ω) o ≠ ⊤) :
    0 ≤ flipDiff (realVol o) e ω := by
  have hle : realVol o (forceOn {e} ∅ ω) ≤ realVol o (forceOn {e} {e} ω) :=
    realVol_mono hne (clusterVol_flip_le e o ω)
  unfold flipDiff
  linarith

/-! ### The integrated pivot bounds -/

/-- **The quadratic pivot weight is bounded by the linear one.**  The `p = 1` supremum bound
`2 m` is replaced by `2 N` times the first-moment pivot increment of the same edge. -/
theorem abs_pivotalFlux_capSqVol_le (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (o : V) {N : ℝ} (hN : 0 ≤ N) (e : Sym2 V)
    (hInt : Integrable (fun ω => flipDiff (capVol o N) e ω) μ) :
    |pivotalFlux μ (capSqVol o N) e| ≤ 2 * N * pivotalFlux μ (capVol o N) e := by
  have hbnd : ∀ ω : Config V,
      ‖flipDiff (capSqVol o N) e ω‖ ≤ 2 * N * flipDiff (capVol o N) e ω := by
    intro ω
    rw [Real.norm_eq_abs]
    exact abs_flipDiff_capSqVol_le o hN e ω
  calc |pivotalFlux μ (capSqVol o N) e|
      = ‖∫ ω, flipDiff (capSqVol o N) e ω ∂μ‖ := by
        simp only [pivotalFlux, Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖flipDiff (capSqVol o N) e ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 2 * N * flipDiff (capVol o N) e ω ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
          (hInt.const_mul (2 * N)) (Eventually.of_forall hbnd)
    _ = 2 * N * ∫ ω, flipDiff (capVol o N) e ω ∂μ := integral_const_mul _ _
    _ = 2 * N * pivotalFlux μ (capVol o N) e := rfl

/-- The capped first-moment pivot increment is nonnegative, with no side condition. -/
theorem flipDiff_capVol_nonneg (o : V) (N : ℝ) (e : Sym2 V) (ω : Config V) :
    0 ≤ flipDiff (capVol o N) e ω := by
  have h := capVol_mono (o := o) N (clusterVol_flip_le e o ω)
  unfold flipDiff
  linarith

/-- **The quadratic pivot weight is bounded by the first-moment pivot weight** on the event that
the cluster of `o` is finite, i.e. with the cap removed from the dominator. -/
theorem abs_pivotalFlux_capSqVol_le_realVol (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (o : V) {N : ℝ} (hN : 0 ≤ N) (e : Sym2 V)
    (hInt : Integrable (fun ω => flipDiff (capVol o N) e ω) μ)
    (hIntR : Integrable (fun ω => flipDiff (realVol o) e ω) μ)
    (hfin : ∀ᵐ ω ∂μ, clusterVol (forceOn {e} {e} ω) o ≠ ⊤) :
    |pivotalFlux μ (capSqVol o N) e| ≤ 2 * N * pivotalFlux μ (realVol o) e := by
  refine (abs_pivotalFlux_capSqVol_le μ o hN e hInt).trans ?_
  have hmono : pivotalFlux μ (capVol o N) e ≤ pivotalFlux μ (realVol o) e := by
    unfold pivotalFlux
    exact integral_mono_of_nonneg
      (Eventually.of_forall fun ω => flipDiff_capVol_nonneg o N e ω) hIntR
      (hfin.mono fun ω hω => flipDiff_capVol_le_realVol hN hω)
  exact mul_le_mul_of_nonneg_left hmono (by linarith)

set_option maxHeartbeats 2000000 in
-- the `tsum` comparison over `Sym2 V` is a heavy unification problem
/-- **Comparison test for the quadratic pivotal series.**

If the first-moment pivotal series of the edge weights `c` is absolutely summable, then the
quadratic pivotal series of the capped square is summable with total at most `2 N` times the
first-moment total.  This is the exact input the `p = 2` exchange needs in place of the
unavailable supremum bound `m = sup |K_o|²`. -/
theorem summable_abs_pivotalFlux_capSqVol (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (o : V) {N : ℝ} (hN : 0 ≤ N) (c : Sym2 V → ℝ)
    (hInt : ∀ e : Sym2 V, Integrable (fun ω => flipDiff (capVol o N) e ω) μ)
    (hdom : Summable fun e : Sym2 V => |c e| * pivotalFlux μ (capVol o N) e) :
    Summable fun e : Sym2 V => c e * pivotalFlux μ (capSqVol o N) e := by
  have hb : ∀ e : Sym2 V, ‖c e * pivotalFlux μ (capSqVol o N) e‖
      ≤ 2 * N * (|c e| * pivotalFlux μ (capVol o N) e) := by
    intro e
    rw [Real.norm_eq_abs, abs_mul]
    have h := abs_pivotalFlux_capSqVol_le μ o hN e (hInt e)
    calc |c e| * |pivotalFlux μ (capSqVol o N) e|
        ≤ |c e| * (2 * N * pivotalFlux μ (capVol o N) e) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = 2 * N * (|c e| * pivotalFlux μ (capVol o N) e) := by ring
  have hnorm : Summable fun e : Sym2 V => ‖c e * pivotalFlux μ (capSqVol o N) e‖ :=
    Summable.of_nonneg_of_le (fun e => norm_nonneg _) hb (hdom.mul_left (2 * N))
  exact hnorm.of_norm

-- **The quadratic pivotal total is at most `2 N` times the first-moment pivotal total.**
set_option maxHeartbeats 2000000 in
-- the `tsum` comparison over `Sym2 V` is a heavy unification problem
theorem abs_tsum_pivotalFlux_capSqVol_le (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (o : V) {N : ℝ} (hN : 0 ≤ N) (c : Sym2 V → ℝ)
    (hInt : ∀ e : Sym2 V, Integrable (fun ω => flipDiff (capVol o N) e ω) μ)
    (hdom : Summable fun e : Sym2 V => |c e| * pivotalFlux μ (capVol o N) e) :
    |∑' e : Sym2 V, c e * pivotalFlux μ (capSqVol o N) e|
      ≤ 2 * N * ∑' e : Sym2 V, |c e| * pivotalFlux μ (capVol o N) e := by
  have hsum := summable_abs_pivotalFlux_capSqVol μ o hN c hInt hdom
  have hsum' : Summable fun e : Sym2 V => |c e * pivotalFlux μ (capSqVol o N) e| :=
    hsum.abs
  have h1 : |∑' e : Sym2 V, c e * pivotalFlux μ (capSqVol o N) e|
      ≤ ∑' e : Sym2 V, |c e * pivotalFlux μ (capSqVol o N) e| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun e : Sym2 V => c e * pivotalFlux μ (capSqVol o N) e) hsum')
  have hb : ∀ e : Sym2 V, |c e * pivotalFlux μ (capSqVol o N) e|
      ≤ 2 * N * (|c e| * pivotalFlux μ (capVol o N) e) := by
    intro e
    rw [abs_mul]
    have h := abs_pivotalFlux_capSqVol_le μ o hN e (hInt e)
    calc |c e| * |pivotalFlux μ (capSqVol o N) e|
        ≤ |c e| * (2 * N * pivotalFlux μ (capVol o N) e) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = 2 * N * (|c e| * pivotalFlux μ (capVol o N) e) := by ring
  have h2 : ∑' e : Sym2 V, |c e * pivotalFlux μ (capSqVol o N) e|
      ≤ ∑' e : Sym2 V, 2 * N * (|c e| * pivotalFlux μ (capVol o N) e) :=
    Summable.tsum_le_tsum hb hsum' (hdom.mul_left (2 * N))
  have h3 : ∑' e : Sym2 V, 2 * N * (|c e| * pivotalFlux μ (capVol o N) e)
      = 2 * N * ∑' e : Sym2 V, |c e| * pivotalFlux μ (capVol o N) e :=
    tsum_mul_left
  rw [h3] at h2
  exact h1.trans h2

end CappedMoments

end PercLib.CriticalLRP
