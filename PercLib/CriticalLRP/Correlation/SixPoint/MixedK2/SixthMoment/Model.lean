/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m1.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m1/Model.lean`.
-/

/-
Ultramath `smwzqts7r`, member `m1`, direction `d2`.

# `CaseTwo.SixthMomentMixed` from the `945`-shape cover

Production's `CaseTwo.SixthMomentMixed M` (`Analysis/SecondMomentCase2/Source/Defs.lean`) is the
statement `E_{β_c,r}|K|^6 ≤ 945 (E_{β_c,r}|K|^2)^2 (E_{β_c,r}|K|)^5` for every radius `r ≥ 0`,
i.e. Hutchcroft's Lemma I.4.16 at `p = 6`, `k = 2` at the model's normalized cutoff law.

This file discharges the passage from the `945`-shape cover to that predicate.  The bookkeeping
is: the cutoff moment `M.cutMoment p r` is the `p`-th moment of `cardFun (cluster · 0)` under
the cutoff law `law (M.cutProb r)` (production's `cutMoment_eq_lintegral_cardFun`); the profile
`M.cutProb r` is fully translation invariant (production's `cutProb_shift_invariant`); the sixth
moment is the sixfold sum of joint connection probabilities (`lintegral_cardFun_six_eq`); the
`945`-shape sum can be taken outside (`tsum_six_fin945_swap`); and each shape contributes at
most `(E|K|^2)^2 (E|K|)^5` (`tsum_slotK2Six_six`, `one_le_susceptibility`).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Triangle
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Covariance

/-! The conditional sixfold cover reduction at the normalized model cutoff law. -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Topology
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.SixthMoment

open PercLib.CriticalLRP.TreeExpansion.HubK2

variable (M : SourceModelData)

/-- The cutoff opening profile is invariant under simultaneous translation of both
endpoints.  Immediate from production's `cutProb_shift_invariant`. -/
theorem cutProb_translate (r : ℝ) (x y g : M.V) :
    M.cutProb r s(x + g, y + g) = M.cutProb r s(x, y) := by
  have h := PercLib.CriticalLRP.E1Sign.cutProb_shift_invariant M r g s(x, y)
  rw [Sym2.map_mk] at h
  exact h

/-- **`CaseTwo.SixthMomentMixed M` from the `945`-shape cover.**

The single hypothesis is `HubK2.SixCover` at every radius: the deterministic union bound of the
proof of Lemma I.4.16, i.e. a cover of the sixfold joint connection probability by the `945`
two-hub slot diagrams.  Everything else — the sixfold moment identity, the shape/diagram
evaluation, the exponent bookkeeping and the passage to the cutoff law — is proved. -/
theorem sixthMomentMixed_of_sixCover (pat : Fin 945 → Equiv.Perm (Fin 6))
    (hcover : ∀ (r : ℝ), 0 ≤ r → SixCover (M.cutProb r) (0 : M.V) pat) :
    PercLib.CriticalLRP.CaseTwo.SixthMomentMixed M := by
  intro r hr
  have habs : SixthMomentLe (M.cutProb r) (0 : M.V) :=
    sixth_moment_of_sixCover (M.cutProb r) (0 : M.V) pat (cutProb_translate M r) (hcover r hr)
  rw [M.cutMoment_eq_lintegral_cardFun r 6 0, M.cutMoment_eq_lintegral_cardFun r 2 0,
    M.cutMoment_eq_lintegral_cardFun r 1 0]
  simp only [pow_one]
  exact habs

end PercLib.CriticalLRP.SixthMoment

namespace PercLib.CriticalLRP.SixthMoment

open PercLib.CriticalLRP.TreeExpansion.HubK2

variable (M : SourceModelData)

/-- **Case 2 of Proposition I.4.15, with the `945`-shape cover as the only remaining input.**

Combining `sixthMomentMixed_of_sixCover` with production's
`CaseTwo.p2ExclError_tendsto_zero_of_caseTwo'` (which already discharges universal tightness
via Corollary I.2.5): under `d = 3α`, (Hydro), the first-moment asymptotic `hP` and eventual
finiteness of the second cutoff moment, the excluded-error term `E_{2,r}` of (I.4.14) vanishes.

This is *not* an unconditional model theorem: `SixCover` is retained explicitly. -/
theorem p2ExclError_tendsto_zero_of_sixCover (pat : Fin 945 → Equiv.Perm (Fin 6))
    (hcover : ∀ (r : ℝ), 0 ≤ r → SixCover (M.cutProb r) (0 : M.V) pat)
    (hd : (M.d : ℝ) = 3 * M.α)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  refine PercLib.CriticalLRP.CaseTwo.p2ExclError_tendsto_zero_of_caseTwo' M hd hκ hP hH h2 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  exact sixthMomentMixed_of_sixCover M pat hcover r hr

end PercLib.CriticalLRP.SixthMoment

namespace PercLib.CriticalLRP.SixthMoment

open PercLib.CriticalLRP.TreeExpansion.HubK2
open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable (M : SourceModelData)

/-- **`CaseTwo.SixthMomentMixed M` from an abstract `945`-event cover.**

This is the non-vacuous residual form of the proof of Lemma I.4.16: the sixfold joint
connection event is covered by `945` shape events, and every shape has total mass at most
`(E|K|^2)^2 (E|K|)^5`.  Nothing here presupposes that the shapes are the two-hub slot diagrams
(which is good: `HubK2SixCounterexample.sixCover_false256` shows that they are not). -/
theorem sixthMomentMixed_of_eventCover
    {E : Fin 945 → (Fin 6 → M.V) → Set (Config M.V)}
    (hcover : ∀ (r : ℝ), 0 ≤ r → ∀ y z w q r' s : M.V,
      conn (0 : M.V) y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r' ∩ conn 0 s ⊆
        ⋃ t : Fin 945, E t ![y, z, w, q, r', s])
    (hbound : ∀ (r : ℝ), 0 ≤ r → ∀ t : Fin 945,
      (∑' L : Fin 6 → M.V, law (M.cutProb r) (E t L))
        ≤ secondMoment (M.cutProb r) (0 : M.V) ^ 2
          * (∑' x, tau (M.cutProb r) (0 : M.V) x) ^ 5) :
    PercLib.CriticalLRP.CaseTwo.SixthMomentMixed M := by
  intro r hr
  have habs : SixthMomentLe (M.cutProb r) (0 : M.V) :=
    sixth_moment_of_eventCover (M.cutProb r) (0 : M.V) (hcover r hr) (hbound r hr)
  rw [M.cutMoment_eq_lintegral_cardFun r 6 0, M.cutMoment_eq_lintegral_cardFun r 2 0,
    M.cutMoment_eq_lintegral_cardFun r 1 0]
  simp only [pow_one]
  exact habs

end PercLib.CriticalLRP.SixthMoment
