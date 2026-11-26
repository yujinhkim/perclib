/-
Independently rebuilt and integrated from the accepted `smwx8o5tv/m2` artifact
`.ultramath/smwx8o5tv/m2/Q4`. Production integration revision:
`89f3b5eed8eb492ac975beb090e1d5e2fd9685ba`. Definitions, including `Diag`
and `baseDiag`, are confined to `Defs.lean`; the remaining files prove their
properties and the q=4 cover/BK bound, not its weighted moment evaluation.
-/
/-
Independently built for swarm `smwx8o5tv`, member `m2`, direction Q4-FINITE-COVER.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Four.Refined.Cover
public import PercLib.CriticalLRP.Correlation.I417Example.BK

/-!
# Lemma I.4.17 at `q = 4`: the BK bound for the eight-edge family

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (supplied paper text lines 2444--2464).

Composing the `q = 4` event cover `freshMark_subset_q4Shape` with

* the union bound over the six-fold family (`k1, k2, k3, z1, z2, z3`), and
* `q`-fold BK for each member (`I417Example.bk_fin_ennreal`, applied after reindexing the
  index-generic shape along `Fintype.equivFin`),

gives, for every arm tuple `g`, selected arm `j` and ordering of the three other labels,

  `P(freshMark y g j w) ≤ ∑_{k1,k2,k3,z1,z2,z3} ∏_{8 legs} τ(leg)`

a sum of `2 · 4 · 6 = 48` terms of **eight** two-point factors each: the `2q = 8` edges of Lemma
I.4.17 at `q = 4`.

**What is not provided here.**  The evaluation of this 48-term sum into the printed normalisation
`∑_ℓ C_ℓ χ^(8-ℓ) T^ℓ(w,y)` (and then its composition with the `2p + 1`-edge marked side into
`2p + 9`).  That is a diagram-evaluation step: it needs the substitution `∑_v τ(a,v) = χ` at the
three attachment vertices and the arm sums, exactly the step that `Fresh/Three/Refined/Summed.lean`
performs by hand for the eight `q = 3` diagrams, and that
`Correlation/I417/Fresh/Subdivision` performs structurally for a consumer-supplied family.  See
`Q4/verify_q4_family.py` for an independent check of the depth profile of the 48 members.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFour.Refined

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- **BK for the index-generic shape.**  For any finite index type, the disjoint occurrence of the
leg events costs at most the product of the two-point functions — `8` factors for the `q = 4`
family.  The proof reindexes along `Fintype.equivFin` and applies `q`-fold BK
(`I417Example.bk_fin_ennreal`). -/
theorem shapeOfI_measure_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {ι : Type*} [Fintype ι] (L : ι → V × V) :
    (edgeMeasure π) (ShapeOfI L) ≤ ∏ i, tau π (L i).1 (L i).2 := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hre : ShapeOfI L = ShapeOfI (fun k => L (e.symm k)) := by
    ext ω
    constructor
    · rintro ⟨E, h1, h2, h3⟩
      exact ⟨fun k => E (e.symm k), fun k => h1 _, fun k => h2 _,
        fun k l hkl => h3 _ _ (fun h => hkl (by simpa using congrArg e h))⟩
    · rintro ⟨E, h1, h2, h3⟩
      exact ⟨fun i => E (e i), fun i => by simpa using h1 (e i),
        fun i => by simpa using h2 (e i),
        fun i j hij => h3 _ _ (fun h => hij (by simpa using congrArg e.symm h))⟩
  rw [hre, shapeOfI_fin]
  refine le_trans (I417Example.bk_fin_ennreal π hπ
    (fun k : Fin (Fintype.card ι) => connSet (L (e.symm k)).1 (L (e.symm k)).2)
    (fun k => isUpper_connSet _ _) (fun k => finiteWitness_connSet _ _)) ?_
  rw [Fintype.prod_equiv e (fun i => tau π (L i).1 (L i).2)
    (fun k => tau π (L (e.symm k)).1 (L (e.symm k)).2) (fun i => by simp)]
  exact le_rfl

/-- **The `q = 4` fresh-side BK bound.**  For every arm tuple, the fresh marked event costs at most
the sum over the `2 · 4 · 6 = 48` eight-leg diagrams of the products of their eight two-point
factors.  This is the `q = 4` analogue of `Fresh/Three/Refined/freshMark_measure_le_shapes`. -/
theorem freshMark_measure_le_q4 (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (g : Fin 4 → V) (j i1 i2 i3 : Fin 4) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤
      ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
        ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
          ∏ i, tau π
            (q4Legs k1 k2 k3 z1 z2 z3 y w (g j) (g i1) (g i2) (g i3) i).1
            (q4Legs k1 k2 k3 z1 z2 z3 y w (g j) (g i1) (g i2) (g i3) i).2 := by
  classical
  refine le_trans (measure_mono (freshMark_subset_q4Shape y w g j i1 i2 i3)) ?_
  rw [q4Shape]
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k1 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k2 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun k3 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun z1 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun z2 => ?_)
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun z3 => ?_)
  exact shapeOfI_measure_le π hπ _

end PercLib.CriticalLRP.I417FreshFour.Refined
