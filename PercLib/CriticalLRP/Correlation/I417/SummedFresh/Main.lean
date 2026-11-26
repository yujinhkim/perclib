/-
The summed fresh-side evaluation of Lemma I.4.17 at general `q`
(direction `(B) UNRESTRICTED-FIBRE EVALUATION`, swarm `smwxtabcx`, member `m2`).

Read-only against production `repo/.scratch/critical-lrp-orchestration`
(HEAD `1cf119aa54facb618600bb09077747b6a3b891f3`, Lean 4.35.0).  Nothing outside
`.ultramath/smwxtabcx/m2/` is written.

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (pp. 45--46): the two-copy expansion gives tree
diagrams with `2p + 2q + 1` edges, `3 ≤ ℓ ≤ p + q + 1` of them on the path from `x` to `y`; the
fresh side carries exactly `2q` edges.

# What is proved

The fresh factor of the marked expansion is `∑_{g : Fin q → V} P(freshMark y g j w)`.  Production
bounds it per arm tuple `g` (`I417GenIter.GenFreshEval`, `I417FreshProfile.genFreshEval_genCoeff`)
by a polynomial that does not depend on `g`; such a bound cannot be summed over the infinite type
`Fin q → V`.  Here the **sum** is evaluated instead:

1. `prod_tau_eq_histW` — production's BK/union cover
   (`I417GenIter.tsum_freshMark_le_genShape`) is literally the history weight `histW`;
2. `tsum_pinned_swap` — the `g`-sum and the history sum are exchanged.  For a fixed history `H`
   the arm tuples pinning its arms are in bijection with the selected arm's target `g j`
   (`armFibreEquiv`), so `∑_g ∑_{H pinned} F H (g j) = ∑_H ∑_a F H a`.  Nothing is counted twice
   and no `g`-independent bound is summed;
3. `tsum_histW_tsum_eq_freshProfileSum` — the unrestricted history sum with the arm target summed
   is *exactly* `∑_{ℓ∈[1,q]} C_ℓ χ^(2q-ℓ) T^ℓ(w,y)`, by production's
   `tsum_histW_eq_tsum_histFibre` (fibre decomposition) and
   `tsum_histFibre_markDepth_symm` (the two-chain closed form of one branch, with the free arm
   target summed inside, kernel symmetry only for the `T^ℓ(w,y)` orientation);
4. `tsum_freshMark_le_freshProfileSum` and its `q = 1` counterpart assemble
   `SummedFreshProfile π q` for every `q ≥ 1`.

Every monomial keeps exactly `2q` kernel factors, `2q - ℓ` of them fully summed (`χ`) and `ℓ` on
the pin--mark path (`T^ℓ(w,y)`), with `ℓ ∈ [1,q]`: the printed edge count and depth range.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.SummedFresh.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Poly

/-! The summed fresh-profile evaluation. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false

@[expose] public section

namespace PercLib.CriticalLRP.I417SummedFresh

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## 1. The two-point kernel, its symmetry, and production's cover as a history weight -/

/-- The two-point function is symmetric.  (The only use of symmetry in this file: the branch
value of production is a power in the orientation `T^ℓ(y,w)` and the printed normal form uses
`T^ℓ(w,y)`.) -/
theorem tau_symm (π : Sym2 V → unitInterval) (a b : V) :
    I417Fresh.tau π a b = I417Fresh.tau π b a :=
  I417Base.edgeMeasure_connSet_comm π a b

/-- Production's product of the `2(n+1)` two-point factors of a history is its `histW` weight. -/
theorem prod_tau_eq_histW (π : Sym2 V → unitInterval) {n : ℕ} (H : I417GenIter.Hist V n)
    (y w a : V) :
    (∏ i : I417GenIter.Idx n,
        I417Fresh.tau π (H.legs y w a i).1 (H.legs y w a i).2) =
      I417HistToSpine.histW (fun _ => I417Fresh.tau π) H y w a := rfl

/-! ## 2. Exchanging the arm sum with the history sum -/

/-- **The summed cover reindexed.**  Summing production's per-tuple cover over all arm tuples and
then exchanging the two sums: for a fixed history `H` the arm tuples that pin its arms are indexed
by the selected arm's target `g j` alone (`armFibreEquiv`), so the pinned double sum is exactly the
unrestricted `∑_H ∑_a`. -/
theorem tsum_pinned_swap {q : ℕ} (F : I417GenIter.Hist V (q - 1) → V → ℝ≥0∞) (j : Fin q)
    (e : Fin (q - 1) ≃ {i : Fin q // i ≠ j}) :
    (∑' g : Fin q → V,
        ∑' H : {H : I417GenIter.Hist V (q - 1) //
          ∀ t : Fin (q - 1), H.arm t = g (e t).1},
          F H.1 (g j)) =
      ∑' H : I417GenIter.Hist V (q - 1), ∑' a : V, F H a := by
  classical
  have hstep : ∀ g : Fin q → V,
      (∑' H : {H : I417GenIter.Hist V (q - 1) //
          ∀ t : Fin (q - 1), H.arm t = g (e t).1},
          F H.1 (g j)) =
        ∑' H : I417GenIter.Hist V (q - 1),
          {H : I417GenIter.Hist V (q - 1) |
            ∀ t : Fin (q - 1), H.arm t = g (e t).1}.indicator (fun H => F H (g j)) H :=
    fun g => tsum_subtype {H : I417GenIter.Hist V (q - 1) |
      ∀ t : Fin (q - 1), H.arm t = g (e t).1} (fun H => F H (g j))
  rw [tsum_congr hstep, ENNReal.tsum_comm]
  refine tsum_congr fun H => ?_
  have hg : ∀ g : Fin q → V,
      {H' : I417GenIter.Hist V (q - 1) |
          ∀ t : Fin (q - 1), H'.arm t = g (e t).1}.indicator (fun H' => F H' (g j)) H =
        {g' : Fin q → V | ∀ t : Fin (q - 1), H.arm t = g' (e t).1}.indicator
          (fun g' => F H (g' j)) g := by
    intro g
    simp only [Set.indicator_apply]
    by_cases h : ∀ t : Fin (q - 1), H.arm t = g (e t).1 <;> simp [h]
  rw [tsum_congr hg, ← tsum_subtype {g : Fin q → V | ∀ t : Fin (q - 1), H.arm t = g (e t).1}
    (fun g => F H (g j))]
  exact (armFibreEquiv H e).tsum_eq (fun a => F H a)

/-! ## 3. The unrestricted history sum with the selected arm target summed -/

/-- **The history fibre with the arm target summed is the printed fresh polynomial.**

`∑_H ∑_a histW H y w a = ∑_{ℓ∈[1,q]} C_ℓ · χ^(2q-ℓ) · T^ℓ(w,y)`, with `C_ℓ` production's
`genCoeff q ℓ`.  The proof decomposes the history sum into the finitely many split-choice fibres
(`tsum_histW_eq_tsum_histFibre`), evaluates each fibre exactly
(`tsum_histFibre_markDepth_symm`: the pin--mark chain `T^ℓ(y,w)`, transposed by `tau_symm`, times
`χ` for every other leg, with the arm target summed by the row sum), and groups the fibres by their
pin--mark depth (`sum_markDepthK_mul`, `card_depthFiber`). -/
theorem tsum_histW_tsum_eq_freshProfileSum (π : Sym2 V → unitInterval) {χ : ℝ≥0∞}
    (hχ : ∀ v : V, ∑' z : V, I417Fresh.tau π v z = χ) {q : ℕ} (hq : 1 ≤ q) (y w : V) :
    (∑' H : I417GenIter.Hist V (q - 1), ∑' a : V,
        I417HistToSpine.histW (fun _ => I417Fresh.tau π) H y w a) =
      freshProfileSum π χ q w y := by
  classical
  have hτ : ∀ a b : V, I417Fresh.tau π a b = I417Fresh.tau π b a := tau_symm π
  -- decompose each history into its split-choice fibre
  have hfib : (∑' H : I417GenIter.Hist V (q - 1), ∑' a : V,
        I417HistToSpine.histW (fun _ => I417Fresh.tau π) H y w a) =
      ∑' a : V, ∑' H : I417GenIter.Hist V (q - 1),
        I417HistToSpine.histW (fun _ => I417Fresh.tau π) H y w a := ENNReal.tsum_comm
  rw [hfib]
  rw [tsum_congr fun a =>
    I417FreshProfile.tsum_histW_eq_tsum_histFibre (fun _ => I417Fresh.tau π) y w a]
  rw [ENNReal.tsum_comm]
  -- evaluate each branch of the finite split-choice type
  rw [tsum_congr fun k =>
    I417FreshProfile.tsum_histFibre_markDepth_symm hχ hτ k y w]
  rw [tsum_fintype]
  -- group the branches by the pin--mark depth
  rw [I417FreshProfile.sum_markDepthK_mul (q - 1)
    (fun ℓ => χ ^ (2 * ((q - 1) + 1) - ℓ) * I417Base.iterPow (I417Fresh.tau π) ℓ w y)]
  -- identify the coefficients and the index range
  rw [Nat.sub_add_cancel hq]
  rw [freshProfileSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [I417FreshProfile.card_depthFiber]
  rfl

/-! ## 4. The summed fresh bound -/

/-- **Lemma I.4.17, fresh side, general `q ≥ 2`, in the genuinely summed form.**

The fresh marked event summed over all arm tuples is bounded by the printed fresh polynomial
`∑_{ℓ∈[1,q]} C_ℓ χ^(2q-ℓ) T^ℓ(w,y)`: exactly `2q` kernel factors, `ℓ ∈ [1,q]` of them on the
pin--mark path.  Premises: `π e < 1` (BK), `[Countable V]`, `[DecidableEq V]`, the constant row
sum `χ`.  No finiteness, subcriticality or transitivity is used. -/
theorem tsum_freshMark_le_freshProfileSum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 2 ≤ q) {χ : ℝ≥0∞}
    (hχ : ∀ v : V, ∑' z : V, I417Fresh.tau π v z = χ) (y w : V) (j : Fin q) :
    (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshProfileSum π χ q w y := by
  classical
  obtain ⟨e⟩ := I417GenIter.exists_armEnum (q := q) (by omega : 1 ≤ q) j
  refine (I417GenIter.tsum_freshMark_le_genShape π hπ hq y w j e).trans ?_
  rw [show (∑' g : Fin q → V,
        ∑' H : {H : I417GenIter.Hist V (q - 1) //
          ∀ t : Fin (q - 1), H.arm t = g (e t).1},
          ∏ i : I417GenIter.Idx (q - 1),
            I417Fresh.tau π (H.1.legs y w (g j) i).1 (H.1.legs y w (g j) i).2) =
      ∑' g : Fin q → V,
        ∑' H : {H : I417GenIter.Hist V (q - 1) //
          ∀ t : Fin (q - 1), H.arm t = g (e t).1},
          I417HistToSpine.histW (fun _ => I417Fresh.tau π) H.1 y w (g j) from
    tsum_congr fun g => tsum_congr fun H => prod_tau_eq_histW π H.1 y w (g j)]
  rw [tsum_pinned_swap (fun H a => I417HistToSpine.histW (fun _ => I417Fresh.tau π) H y w a)
    j e]
  exact le_of_eq (tsum_histW_tsum_eq_freshProfileSum π hχ (by omega : 1 ≤ q) y w)

/-! ## 5. The `q = 1` case -/

/-- The single coefficient at `q = 1`. -/
theorem genCoeff_one_one : I417FreshDepth.genCoeff 1 1 = 1 := by
  rw [I417FreshDepth.genCoeff, Nat.sub_self]
  exact I417FreshDepth.depthCount_zero

/-- **Lemma I.4.17, fresh side, `q = 1`.**  The fresh marked event contains the disjoint
occurrence `{y↔w} ∘ {w↔g 0}`, so BK gives `P(freshMark) ≤ T(y,w)·τ(w,g 0)`, and the single arm is
summed out with the constant row sum: the value is `χ · T(w,y)`, i.e. the printed monomial at
`ℓ = 1`. -/
theorem tsum_freshMark_le_freshProfileSum_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {χ : ℝ≥0∞} (hχ : ∀ v : V, ∑' z : V, I417Fresh.tau π v z = χ) (y w : V) (j : Fin 1) :
    (∑' g : Fin 1 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshProfileSum π χ 1 w y := by
  classical
  have hj : j = (0 : Fin 1) := Subsingleton.elim j 0
  subst hj
  have hle : ∀ g : Fin 1 → V,
      (edgeMeasure π) (I417Gen.freshMark y g (0 : Fin 1) w) ≤
        I417Fresh.tau π y w * I417Fresh.tau π w (g 0) := by
    intro g
    have hsub : I417Gen.freshMark y g (0 : Fin 1) w ⊆ disjSet y w w (g 0) := by
      rw [← I417.markFresh_eq_disjSet]
      exact Set.inter_subset_left
    exact (measure_mono hsub).trans (bk_connSet_ennreal π hπ y w w (g 0))
  have hsum : (∑' g : Fin 1 → V, I417Fresh.tau π w (g 0)) =
      ∑' z : V, I417Fresh.tau π w z :=
    (I417Fresh.finOneArrowEquiv V).tsum_eq (fun z => I417Fresh.tau π w z)
  have hR : freshProfileSum π χ 1 w y = χ * I417Fresh.tau π w y := by
    rw [freshProfileSum, Finset.Icc_self, Finset.sum_singleton, genCoeff_one_one, Nat.cast_one,
      one_mul, show 2 * 1 - 1 = 1 from rfl, pow_one, I417Fresh.Subdivision.iterPow_one]
  rw [hR]
  calc (∑' g : Fin 1 → V, (edgeMeasure π) (I417Gen.freshMark y g (0 : Fin 1) w))
      ≤ ∑' g : Fin 1 → V, I417Fresh.tau π y w * I417Fresh.tau π w (g 0) :=
        ENNReal.tsum_le_tsum hle
    _ = I417Fresh.tau π y w * ∑' g : Fin 1 → V, I417Fresh.tau π w (g 0) :=
        ENNReal.tsum_mul_left
    _ = I417Fresh.tau π y w * ∑' z : V, I417Fresh.tau π w z := by rw [hsum]
    _ = I417Fresh.tau π y w * χ := by rw [hχ w]
    _ = χ * I417Fresh.tau π w y := by rw [mul_comm, tau_symm π y w]

/-! ## 6. The summed fresh profile at every positive `q` -/

/-- **The genuinely summed fresh-side input of Lemma I.4.17, at every `q ≥ 1`.**

Premises: `[Countable V]`, `[DecidableEq V]`, `π : Sym2 V → unitInterval` with `π e < 1`
(only used for the BK step of production's cover), and the constant row sum
`∀ v, ∑_z τ(v,z) = χ`. -/
theorem summedFreshProfile (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) :
    ∀ q : ℕ, 1 ≤ q → SummedFreshProfile π q := by
  intro q hq
  rcases Nat.eq_or_lt_of_le hq with h1 | h1
  · subst h1
    exact fun χ hχ y w j => tsum_freshMark_le_freshProfileSum_one π hπ hχ y w j
  · exact fun χ hχ y w j => tsum_freshMark_le_freshProfileSum π hπ (by omega) hχ y w j

/-! ## 7. The bound in production's `Subdivision.freshPoly` normalisation -/

/-- `freshProfileSum` is production's `Subdivision.freshPoly` with the cover's own coefficients. -/
theorem freshProfileSum_eq_freshPoly (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (q : ℕ) (w y : V) :
    freshProfileSum π χ q w y =
      I417Fresh.Subdivision.freshPoly (I417Fresh.tau π) χ q (I417FreshDepth.genCoeff q) w y :=
  rfl

/-- **The summed fresh bound in the normalisation consumed by the diagram-evaluation API**
(`I417Fresh.Subdivision.freshPoly`, `fresh_family_by_depth`, `marked_fresh_le`,
`composed_family_le`).  Same content as `summedFreshProfile`, with production's own name for the
polynomial. -/
theorem tsum_freshMark_le_freshPoly (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    {q : ℕ} (hq : 1 ≤ q) {χ : ℝ≥0∞}
    (hχ : ∀ v : V, ∑' z : V, I417Fresh.tau π v z = χ) (y w : V) (j : Fin q) :
    (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      I417Fresh.Subdivision.freshPoly (I417Fresh.tau π) χ q
        (I417FreshDepth.genCoeff q) w y := by
  rw [← freshProfileSum_eq_freshPoly]
  exact summedFreshProfile π hπ q hq χ hχ y w j


end PercLib.CriticalLRP.I417SummedFresh
