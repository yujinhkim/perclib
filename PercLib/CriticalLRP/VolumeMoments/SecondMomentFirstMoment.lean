/-
Independent, file-scoped contribution of swarm member `m1` (`smwon1exs`), direction (B).
Compiled artifact for the second-moment bootstrap.  Reviewer handoff: `REPORT.md` beside this
file.

## Scope

The campaign already proves, on an arbitrary countable vertex set and under the homogeneity
hypothesis `hS : ∀ a, ∫⁻ |K_a| ≤ ∫⁻ |K_o|`,

* `lintegral_clusterVol_sq_le_cube`   : `∫⁻ |K_o|² ≤ (∫⁻ |K_o|) * (∫⁻ |K_o|) * (∫⁻ |K_o|)`,
* `lintegral_clusterVol_sq_le_cube_pow` : `∫⁻ |K_o|^2 ≤ (∫⁻ |K_o|)^3`,
* `lintegral_clusterVol_sq_ne_top`    : `∫⁻ |K_o| ≠ ⊤ → ∫⁻ |K_o|² ≠ ⊤`,

and on `Z^d` with a shift-invariant edge law it discharges `hS` by translation invariance
(`lintegral_clusterVol_shift_invariant`), giving `lintegral_clusterVol_sq_le_cube_lattice` and
`lintegral_clusterVol_sq_le_cube_lattice_pow`.

What was *not* in the library at commit `2f0ab92c271b59808c7b9ff848785ff8f69763a5`:

1. no `_ne_top` (finiteness *conclusion*) form of the lattice bound;
2. no conversion of "the root mean is finite" into "the mean is finite at *every* vertex" on
   `Z^d`, so the all-roots scope was left implicit;
3. no `longRangeMeasure` / `latticeLongRangeMeasure` instance of the finiteness conclusion,
   i.e. nothing at the paper's own law `P_β` of Definition I.1.3;
4. the uncut `Hvol.lemma_I_4_7_shift_of_finite` / `Hvol.lemma_I_4_7_latticeLongRange_of_finite`
   still carry the connected-window moment `hTfin` as an independent premise, although it is
   dominated by `|B|` times the second moment which the cubic bound already supplies, and the
   cutoff `Hvol.lemma_I_4_7_cutoff_of_secondMoment` still carries `h2` although
   `Hvol.cutoffSecondMoment_ne_top_of_firstMoment` already derives it from the first moment.

This file closes exactly items 1–4 and nothing else.  It is *not* a paper theorem and adds no
new mathematical input: it is a bundling of the existing cubic-in-first-moment bound.

## Honest boundary

The conclusion `∫⁻ |K_o|² ≠ ⊤` is obtained from `∫⁻ |K_o| ≠ ⊤`.  It therefore says nothing at a
parameter where the first moment is infinite: there the cubic bound reads
`∫⁻ |K_o|² ≤ ⊤` and is vacuous.  In particular this does *not* give a finite second moment at
`β = β_c` when `χ(β_c) = ∞`; supplying `∫⁻ |K_o| ≠ ⊤` at the relevant `β` is the genuine
remaining input (sharpness / subcritical finiteness of the mean), which is not proved here and
is not proved in the campaign.

No `sorry`, no `admit`, no `native_decide`, no custom axiom, no `Def` machinery, no root-draft
import.  Axiom sets are printed at the end of the file.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.SecondMoment
public import PercLib.CriticalLRP.VolumeMoments.SecondMomentCutoff
public import PercLib.CriticalLRP.VolumeMoments.ErrorBounds
public import PercLib.CriticalLRP.Correlation.I411.RealQuotient

set_option autoImplicit false
set_option linter.unusedSectionVars false
/-
Adapted from `.ultramath/smwon1exs/m1/SecondMomentLattice.lean`.
Source APIs compiled at caf78abfc0a005e712ae49b23379a9c64a7a7048.
Licence: Apache-2.0, matching the PercLib sources.
-/

/-
Independent, proof-only transport module. Every theorem supplied here is
conditional: it transports a finite first cluster-volume moment to a finite
second moment, or a redundant input of the corresponding existing provider
to a finite first moment. It does not supply sharpness or a paper root proof.
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

/-! ## 1. One root versus every root on `Z^d` -/

/-- On `Z^d` with a shift-invariant edge law, the expected cluster volume at one vertex is
*equal* to the expected cluster volume at any other vertex.  (Equality, not merely `≤`; this
is the statement that `hS` in `lintegral_clusterVol_sq_le_cube` is an identity on the
lattice.) -/
theorem lintegral_clusterVol_shift_eq {d : ℕ} (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (a o : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π)) =
      (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) := by
  rw [lintegral_clusterVol_shift_invariant π hπinv a,
    lintegral_clusterVol_shift_invariant π hπinv o]

/-- **Finiteness of the mean does not depend on the root.**  A single finite root mean gives
finiteness at every vertex, and conversely. -/
theorem forall_lintegral_clusterVol_ne_top_iff {d : ℕ}
    (π : Sym2 (Fin d → ℤ) → unitInterval)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (o : Fin d → ℤ) :
    (∀ a : Fin d → ℤ, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure π)) ≠ ⊤) ↔
      (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤ := by
  constructor
  · intro h
    exact h o
  · intro h a
    rw [lintegral_clusterVol_shift_eq π hπinv a o]
    exact h

/-! ## 2. The finiteness conclusion on `Z^d` -/

/-- **A finite first moment forces a finite second moment on `Z^d`**, for any shift-invariant
edge law with `π e < 1`.  No homogeneity hypothesis is passed by the caller: translation
invariance supplies it. -/
theorem lintegral_clusterVol_mul_self_ne_top_of_shift {d : ℕ}
    (π : Sym2 (Fin d → ℤ) → unitInterval) (hπ : ∀ e, π e < 1)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤ :=
  lintegral_clusterVol_sq_ne_top π hπ o
    (fun a => le_of_eq (lintegral_clusterVol_shift_eq π hπinv a o)) hfin

/-- The same in the literal power notation `|K_o| ^ 2`. -/
theorem lintegral_clusterVol_pow_two_ne_top_of_shift {d : ℕ}
    (π : Sym2 (Fin d → ℤ) → unitInterval) (hπ : ∀ e, π e < 1)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o ^ 2 ∂(edgeMeasure π)) ≠ ⊤ := by
  simpa only [pow_two] using
    lintegral_clusterVol_mul_self_ne_top_of_shift π hπ hπinv o hfin

/-- **The second moment is finite at every vertex** as soon as it is finite at one, on `Z^d`
with a shift-invariant edge law.  This is the all-roots form; it is not the statement that a
single root's finiteness is a global assumption. -/
theorem forall_lintegral_clusterVol_mul_self_ne_top_iff {d : ℕ}
    (π : Sym2 (Fin d → ℤ) → unitInterval) (hπ : ∀ e, π e < 1)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (o : Fin d → ℤ) :
    (∀ a : Fin d → ℤ,
        (∫⁻ ω, clusterVol ω a * clusterVol ω a ∂(edgeMeasure π)) ≠ ⊤) ↔
      (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤ := by
  constructor
  · intro h2
    refine ne_top_of_le_ne_top (h2 o) (lintegral_mono fun ω => ?_)
    simpa only [Percolation.cardFun_eq_encard] using
      Hrest.MomentFiniteness.cardFun_le_cardFun_sq o ω
  · intro h1 a
    refine lintegral_clusterVol_mul_self_ne_top_of_shift π hπ hπinv a ?_
    rwa [lintegral_clusterVol_shift_eq π hπinv a o]

/-- **The real-valued quadratic bound**: when the first moment is finite,
`E |K_o|² ≤ (E |K_o|)³` holds in `ℝ`, via `ENNReal.toReal`.  Passing to `ℝ` is legitimate here
precisely because both sides are finite; on `⊤` the inequality is *not* preserved by
`toReal`. -/
theorem lintegral_clusterVol_pow_two_toReal_le_cube_of_shift {d : ℕ}
    (π : Sym2 (Fin d → ℤ) → unitInterval) (hπ : ∀ e, π e < 1)
    (hπinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o ^ 2 ∂(edgeMeasure π)).toReal ≤
      ((∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))).toReal ^ 3 := by
  have hcube := lintegral_clusterVol_sq_le_cube_lattice_pow π hπ hπinv o
  have hcube_ne : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ^ 3 ≠ ⊤ :=
    ENNReal.pow_ne_top hfin
  calc (∫⁻ ω, clusterVol ω o ^ 2 ∂(edgeMeasure π)).toReal
      ≤ ((∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ^ 3).toReal :=
        ENNReal.toReal_mono hcube_ne hcube
    _ = ((∫⁻ ω, clusterVol ω o ∂(edgeMeasure π))).toReal ^ 3 :=
        ENNReal.toReal_pow _ 3

/-! ## 3. The paper's law `P_β` of Definition I.1.3 -/

/-- The finiteness conclusion for an arbitrary translation-invariant kernel, i.e. for the
paper's `P_β` law `longRangeMeasure J hJ β`. -/
theorem longRange_lintegral_clusterVol_mul_self_ne_top {d : ℕ}
    (J : Sym2 (Fin d → ℤ) → ℝ)
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ β)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(longRangeMeasure J hJ β)) ≠ ⊤ := by
  have h := lintegral_clusterVol_mul_self_ne_top_of_shift (bernoulliEdgeProb J hJ β)
    (bernoulliEdgeProb_lt_one hJ β) (bernoulliEdgeProb_shift hJinv hJ β) o (by
      simpa only [longRangeMeasure] using hfin)
  simpa only [longRangeMeasure] using h

/-- The finiteness conclusion at `J(x,y) = ‖x - y‖^{-d-α}`, i.e. at
`latticeLongRangeMeasure d α β`. -/
theorem latticeLongRange_lintegral_clusterVol_mul_self_ne_top (d : ℕ) (α : ℝ)
    (β : NNReal) (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(latticeLongRangeMeasure d α β)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(latticeLongRangeMeasure d α β)) ≠ ⊤ := by
  have h := longRange_lintegral_clusterVol_mul_self_ne_top (lrKernel d α)
    (lrKernel_shift_invariant d α) (lrKernel_nonneg d α) β o hfin
  simpa only [latticeLongRangeMeasure] using h

/-- The same at the paper's law in the `cardFun` notation used by the I.4.7 providers, which is
literally the hypothesis `h2` of the cutoff/uncut `lemma_I_4_7_*_of_secondMoment` theorems. -/
theorem latticeLongRange_cardFun_mul_self_ne_top (d : ℕ) (α : ℝ) (β : NNReal)
    (x : Fin d → ℤ)
    (h1 : (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(latticeLongRangeMeasure d α β)) ≠ ∞) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)
      ∂(latticeLongRangeMeasure d α β)) ≠ ∞ := by
  have h := latticeLongRange_lintegral_clusterVol_mul_self_ne_top d α β x (by
    simpa only [Percolation.cardFun_eq_encard] using h1)
  simpa only [Percolation.cardFun_eq_encard] using h

/-! ## 4. Removing the redundant moments from the I.4.7 providers -/

/-- **Lemma I.4.7 on `Z^d` with a single moment premise.**  Identical conclusion to
`Hvol.lemma_I_4_7_shift_of_finite`, with the connected-window moment `hTfin` deleted: it is
dominated by `|B|` times the second moment, and the second moment follows from `hAfin` by
translation invariance. -/
theorem lemma_I_4_7_shift_of_firstMoment {d : ℕ}
    {π : Sym2 (Fin d → ℤ) → unitInterval}
    (hπshift : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (hπ : ∀ e, π e < 1) (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (𝓔 : ℕ → Finset (Sym2 (Fin d → ℤ))) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ 𝓔 n)
    (hAfin : (∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(edgeMeasure π)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) := by
  refine Hvol.lemma_I_4_7_shift_of_finite hπshift hπ x B hB 𝓔 h𝓔mono h𝓔 hAfin ?_
  have h2 : (∫⁻ ω, Percolation.cardFun (cluster ω x) *
      Percolation.cardFun (cluster ω x) ∂(edgeMeasure π)) ≠ ∞ := by
    have h := lintegral_clusterVol_mul_self_ne_top_of_shift π hπ hπshift x (by
      simpa only [Percolation.cardFun_eq_encard] using hAfin)
    simpa only [Percolation.cardFun_eq_encard] using h
  exact Hrest.MomentFiniteness.ne_top_of_aggregated x B h2

/-- **Lemma I.4.7 at the paper's long-range law with a single moment premise.**  Identical
conclusion to `Hvol.lemma_I_4_7_latticeLongRange_of_finite`, with `hTfin` deleted. -/
theorem lemma_I_4_7_latticeLongRange_of_firstMoment (d : ℕ) (α : ℝ) (β : NNReal)
    (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(latticeLongRangeMeasure d α β)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(latticeLongRangeMeasure d α β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(latticeLongRangeMeasure d α β)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(latticeLongRangeMeasure d α β)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) := by
  refine Hvol.lemma_I_4_7_latticeLongRange_of_finite d α β x B hB hAfin ?_
  exact Hrest.MomentFiniteness.ne_top_of_aggregated x B
    (latticeLongRange_cardFun_mul_self_ne_top d α β x hAfin)

/-- **Lemma I.4.7 at the Definition I.1.5 cutoff law with a single moment premise.**  Identical
conclusion to `Hvol.lemma_I_4_7_cutoff_of_secondMoment`, with the second-moment premise `h2`
deleted, using `Hvol.cutoffSecondMoment_ne_top_of_firstMoment`. -/
theorem lemma_I_4_7_cutoff_of_firstMoment (K : ℝ → ℝ) (hK : AntitoneOn K (Set.Ioi 0))
    (d : ℕ) (r : ℝ) (hr : 0 < r) (β : NNReal)
    (x : Fin d → ℤ) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞) :
    let J : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω x).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x))
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    let A : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    0 ≤ VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ∧
      VolumeMoments.cE1 A.toReal J.toReal T.toReal B.card ≤
        T.toReal / (B.card * A.toReal ^ 2) :=
  Hvol.lemma_I_4_7_cutoff_of_secondMoment K hK d r hr β x B hB
    (by
      simpa only [Percolation.cardFun_eq_encard] using
        Hvol.cutoffSecondMoment_ne_top_of_firstMoment K hK d r hr β x hAfin)

/-! ## 5. Downstream: the joint-window premise of Lemma I.4.11 -/

/-- **Lemma I.4.11 on `Z^d` with the joint-window moment removed.**  The conclusion is
identical to `I411.lemma_I_4_11_of_finite`, with `hJfin` deleted: `hJfin` is bounded by the
*sum* of the second cluster moments at `0` and at the sites of `B`
(`joint_windowMoment_le_sum_second_moments`, no factor `|B|` needed), and all of those follow
from `hAfin` by translation invariance.

The averaged five-factor sum `hDfin` is deliberately **not** removed.  It is an `ℝ≥0∞`
finiteness statement about `∑_a ∑_b τ(0,a) τ(a,b) τ(b,y)`, not about a cluster moment; the
argument of this file does not derive it from a finite first moment, and deleting it would
replace a premise by an unearned claim.  It is left exactly where the campaign already has
it. -/
theorem lemma_I_4_11_of_firstMoment {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w) ≠ ∞)
    (hDfin : (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b *
          twoPointFunction J hJ β b y) ≠ ∞) :
    let A : ℝ≥0∞ := ∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)
    let Jm : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω 0) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(longRangeMeasure J hJ β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω 0).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω 0) * Percolation.cardFun (cluster ω 0))
      ∂(longRangeMeasure J hJ β)
    VolumeMoments.cE1 A.toReal Jm.toReal T.toReal B.card ≤
      (B.card : ℝ)⁻¹ * (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b *
          twoPointFunction J hJ β b y).toReal := by
  have h1 : (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)) ≠ ∞ := by
    rw [lintegral_clusterVol_eq_tsum_twoPoint hJ β 0]
    exact hAfin
  have hshift : ∀ y : Fin d → ℤ,
      (∫⁻ ω, clusterVol ω y ∂(longRangeMeasure J hJ β)) =
        (∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)) := by
    intro y
    have hy := lintegral_clusterVol_shift_invariant (bernoulliEdgeProb J hJ β)
      (bernoulliEdgeProb_shift hJinv hJ β) y
    have h0 := lintegral_clusterVol_shift_invariant (bernoulliEdgeProb J hJ β)
      (bernoulliEdgeProb_shift hJinv hJ β) 0
    simpa only [longRangeMeasure] using hy.trans h0.symm
  have h2all : ∀ y : Fin d → ℤ,
      (∫⁻ ω, Percolation.cardFun (cluster ω y) * Percolation.cardFun (cluster ω y)
        ∂(longRangeMeasure J hJ β)) ≠ ∞ := by
    intro y
    have hy : (∫⁻ ω, clusterVol ω y ∂(longRangeMeasure J hJ β)) ≠ ∞ := by
      rw [hshift y]; exact h1
    have h := longRange_lintegral_clusterVol_mul_self_ne_top J hJinv hJ β y hy
    simpa only [Percolation.cardFun_eq_encard] using h
  refine I411.lemma_I_4_11_of_finite hJinv hJ β B hB hAfin ?_ hDfin
  have hjoint := joint_windowMoment_le_sum_second_moments (bernoulliEdgeProb J hJ β)
    (0 : Fin d → ℤ) B
  refine ne_top_of_le_ne_top ?_ (by simpa only [longRangeMeasure] using hjoint)
  rw [ENNReal.sum_ne_top]
  intro y _
  exact ENNReal.add_ne_top.mpr ⟨h2all 0, h2all y⟩

/-! ## 6. Axiom audit -/

#print axioms PercLib.CriticalLRP.lintegral_clusterVol_shift_eq
#print axioms PercLib.CriticalLRP.forall_lintegral_clusterVol_ne_top_iff
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_mul_self_ne_top_of_shift
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_pow_two_ne_top_of_shift
#print axioms PercLib.CriticalLRP.forall_lintegral_clusterVol_mul_self_ne_top_iff
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_pow_two_toReal_le_cube_of_shift
#print axioms PercLib.CriticalLRP.longRange_lintegral_clusterVol_mul_self_ne_top
#print axioms PercLib.CriticalLRP.latticeLongRange_lintegral_clusterVol_mul_self_ne_top
#print axioms PercLib.CriticalLRP.latticeLongRange_cardFun_mul_self_ne_top
#print axioms PercLib.CriticalLRP.lemma_I_4_7_shift_of_firstMoment
#print axioms PercLib.CriticalLRP.lemma_I_4_7_latticeLongRange_of_firstMoment
#print axioms PercLib.CriticalLRP.lemma_I_4_7_cutoff_of_firstMoment
#print axioms PercLib.CriticalLRP.lemma_I_4_11_of_firstMoment

end PercLib.CriticalLRP
