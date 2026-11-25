/-
Direction A, generality check: the moment-invariance lemma is not specific to the
translation action.  Any vertex permutation `g` with `π (Sym2.map g e) = π e` gives the
same conclusion for `edgeMeasure π`, via `Hvol.permConfig`; this covers the finite-torus
model `V = Fin d → ZMod n` and any vertex-transitive model, not only `ZMod`-translations.

Nothing here is used by the `p = 4`, `k = 2` target; it is the "abstract theorem" half of
Direction A's reusable API.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.RootIndependence
public import PercLib.CriticalLRP.Correlation.HvolPermutation

open MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*} [Countable V]

/-- **Moment invariance along a `π`-preserving vertex permutation.**  For every power `n`,
`E |K_{g x}|^n = E |K_x|^n` under `edgeMeasure π`. -/
theorem lintegral_cardFun_pow_permConfig (π : Sym2 V → unitInterval) (g : V ≃ V)
    (hπ : ∀ e : Sym2 V, π (Sym2.map g e) = π e) (n : ℕ) (x : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω (g x))) ^ n
        ∂(PercLib.CriticalLRP.edgeMeasure π)
      = ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ n
        ∂(PercLib.CriticalLRP.edgeMeasure π) :=
  lintegral_cardFun_pow_root_indep (PercLib.CriticalLRP.edgeMeasure π)
    (PercLib.CriticalLRP.Hvol.measurable_permConfig g)
    (PercLib.CriticalLRP.Hvol.edgeMeasure_permConfig_invariant π g hπ)
    (e := ⇑g) g.injective (fun ω v => PercLib.CriticalLRP.Hvol.cluster_permConfig g ω v) n x

/-- The `n = 2` case, in the `secondMoment` shape (recall `edgeMeasure π` is `law π` by
`PercLib.CriticalLRP.edgeMeasure_eq_law`). -/
theorem secondMoment_permConfig (π : Sym2 V → unitInterval) (g : V ≃ V)
    (hπ : ∀ e : Sym2 V, π (Sym2.map g e) = π e) (x : V) :
    secondMoment π (g x) = secondMoment π x :=
  lintegral_cardFun_pow_permConfig π g hπ 2 x

/-- **The second moment is root-free on the finite torus** `(Fin d → ZMod n)`, for any
translation-invariant profile: no lattice structure, no moment finiteness. -/
theorem secondMoment_torus_root_independent {d n : ℕ} [NeZero n]
    (π : Sym2 (Fin d → ZMod n) → unitInterval)
    (hπ : ∀ (a : Fin d → ZMod n) (e : Sym2 (Fin d → ZMod n)),
      π (Sym2.map (fun x => x + a) e) = π e)
    (x y : Fin d → ZMod n) :
    secondMoment π x = secondMoment π y := by
  have h := secondMoment_permConfig π (PercLib.CriticalLRP.Hvol.torusShift (y - x))
    (fun e => hπ (y - x) e) x
  have hxy : x + (y - x) = y := by
    funext i
    simp
  simpa only [PercLib.CriticalLRP.Hvol.torusShift_apply, hxy] using h.symm

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.secondMoment_permConfig
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.secondMoment_torus_root_independent

end PercLib.CriticalLRP.TreeExpansion.FivePoint
