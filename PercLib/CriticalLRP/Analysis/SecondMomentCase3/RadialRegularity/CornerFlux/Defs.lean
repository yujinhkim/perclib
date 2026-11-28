/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m3.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m3/Defs.lean`.
-/

module

/-
Corner pivot package for the critical long-range percolation source model.

Direction (F): the measure-side corner fact for the simple connecting pivotal event.
This file introduces the two model objects the direction asks about:

* `cornerGap y s` — the probability that `0` and `y` are **still connected after the
  direct edge `s(0,y)` is forced closed**; at an attained radius `s = ‖y‖` this is the
  quantity that decides whether the corner contributes to the pivotal flux;
* `directPivot y s` — the pivotal flux of that one edge for the cluster indicator of `y`,
  i.e. the corner summand of Lemma I.4.1 at the edge `s(0,y)`.

No theorem is claimed here beyond definitional unfolding.
-/
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.CornerContinuity.Defs

/-! ## Direct-pivotal mass and summed singleton flux at attained radii -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The event that the origin is connected to `y`. -/
def connEvent (y : M.V) : Set (Config M.V) := {ω : Config M.V | Connects ω (0 : M.V) y}

theorem measurableSet_connEvent (y : M.V) : MeasurableSet (M.connEvent y) :=
  measurableSet_cluster_mem (0 : M.V) y

theorem connEvent_eq_cluster (y : M.V) :
    M.connEvent y = {σ : Config M.V | y ∈ cluster σ (0 : M.V)} := rfl

/-- The **corner gap** at the direct edge `s(0,y)`: the probability, under the cutoff law
at radius `s`, that `0` and `y` remain connected after the direct edge is forced closed.
This is exactly `1 - directPivot`; it is the measure-side quantity that decides whether the
corner at `s = ‖y‖` contributes to the pivotal flux. -/
def cornerGap (y : M.V) (s : ℝ) : ℝ :=
  (M.cutLaw s).real {ω : Config M.V | Connects (forceOn ({s(0, y)} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V) y}

/-- The pivotal flux of the single edge `s(0,y)` for the cluster indicator of `y`: the
corner summand of Lemma I.4.1 at the attained radius `s = ‖y‖`. -/
def directPivot (y : M.V) (s : ℝ) : ℝ :=
  pivotalFlux (M.cutLaw s) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) s(0, y)

/-- The length `‖e‖` of an unordered pair of vertices, for the source norm. -/
noncomputable def sourceEdgeLen (e : Sym2 M.V) : ℝ :=
  Sym2.lift ⟨fun x z => M.S.dist x z, fun x z => (SourceNormData.dist_comm M.S x z).symm⟩ e

theorem sourceEdgeLen_mk (x z : M.V) : M.sourceEdgeLen s(x, z) = M.S.dist x z :=
  Sym2.lift_mk _ x z

/-- The **pointwise left limit of the flux summand** at an attained radius `s`: a corner edge
(one of length exactly `s`) contributes `0` to the limit from below, every shorter edge
contributes its value at `s`, and every longer edge contributes `0`.  The corner jump of the
full flux is the difference between this and the value at `s`. -/
noncomputable def cornerLimitTerm (g : Config M.V → ℝ) (s : ℝ) (e : Sym2 M.V) : ℝ :=
  if M.sourceEdgeLen e < s then M.m8FluxTerm g s e else 0

/-- The total first-moment flux of the singleton observation `{y}` as a function of the cutoff
radius: the left-hand side of the a.e. form of Lemma I.4.1 for `p = 1`. -/
noncomputable def firstFlux (y : M.V) (r : ℝ) : ℝ :=
  sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r

theorem m8FluxTerm_eq_cutEdgeDeriv_mul (g : Config M.V → ℝ) (r : ℝ) (e : Sym2 M.V) :
    M.m8FluxTerm g r e = M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) g e := rfl

end SourceModelData

end PercLib.CriticalLRP.Orchestration
