/-
Member `m1` of swarm `smwxuymqb`, direction `(D)`: independent audit of the completed
general Lemma I.4.17 primitive against the Case 3 interfaces of Proposition I.4.20,
at production HEAD `6569f9781a4bf1ef35843ff3cd468b1d934c4527` (Lean 4.35.0).

Everything here is stated in production vocabulary; the file adds no mathematics of
its own beyond the reconciliation lemmas it proves.  Purpose:

* §0 pins the exact production signatures (so that the audit text cannot drift),
* §1 prints the axiom dependence of the primitive,
* §2 machine-checks the moment bridges `clusterVol = cardFun`, `pairFactor = momentProd`,
  `pairExcl = rawDiff`, `meanVol = E|K|`,
* §3 checks the composition's printed normal form against `I420Case3.treePoly`,
* §4 verifies that the I.4.17 primitive discharges the `HasTreeExpansion.expansion`
  obligation, and records the residual hypotheses.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Composition.Models
public import PercLib.CriticalLRP.Correlation.I417.Measure
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Compare

/-! # Case 3 moment bridges and tree expansion -/

set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP

namespace AuditM1

/-! ## §0. Signature pins -/

/-- Pin of `I417SummedClose.moment_gap_le_markedGapPoly`: the general I.4.17 bound is
stated at `(x, y)`, with the second factor `E|K_y|^q` *not* moved to the basepoint, and
under the single row-constancy hypothesis `hχ` on the **first** moment `meanVol`. -/
theorem pin_moment_gap_le_markedGapPoly {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V) {p q : ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      I417SummedClose.markedGapPoly π p q (I417.meanVol π x) x y :=
  I417SummedClose.moment_gap_le_markedGapPoly π hπ x y hp hq hχ

/-- Pin of `I417SummedClose.moment_gap_le_markedGapPoly_basepoint`: this variant moves
**both** moment factors to the common basepoint `o`.  It therefore cannot be used to
prove a `y`-dependent pair bound without an extra moment-homogeneity hypothesis. -/
theorem pin_moment_gap_le_markedGapPoly_basepoint {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x y : V)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g o = v)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q ∂(edgeMeasure π)) -
      I417A.rawDiff π x y p q ≤
        I417SummedClose.markedGapPoly π p q (I417.meanVol π x) x y :=
  I417SummedClose.moment_gap_le_markedGapPoly_basepoint π hπ o x y htrans hp hq

/-- Pin of `I420Case3.HasTreeExpansion`: the record constrains only the pairs `y ∈ B`,
carries no non-emptiness or finiteness condition on `B`, no hypothesis on `π` and no
relation between its numeric parameters `a`, `b`, `p`. -/
theorem pin_HasTreeExpansion_field {V : Type*} [Countable V]
    (π : Sym2 V → unitInterval) (o : V) (B : Finset V) (a b p : ℕ)
    (poly : V → ℕ → ℝ≥0∞) (C : ℕ → ℝ)
    (h : I420Case3.HasTreeExpansion π o B a b p poly C) :
    ∀ y ∈ B, I420Case3.pairFactor π o y a b ≤
      I420Case3.pairExcl π o y a b +
        I420Case3.treePoly poly C (I420Case1.powMomentAt π 1 o) p y :=
  h.expansion

/-- Pin of `I420Case3.HasPolygonBound`: non-negativity of the constant plus the uniform
`j`-bound against `(E|K|)^{j-3}`, for `3 ≤ j ≤ p+2`. -/
theorem pin_HasPolygonBound_fields {V : Type*} [Countable V]
    (π : Sym2 V → unitInterval) (o : V) (B : Finset V) (p : ℕ)
    (poly : V → ℕ → ℝ≥0∞) (Bpoly : ℝ)
    (h : I420Case3.HasPolygonBound π o B p poly Bpoly) :
    0 ≤ Bpoly ∧ ∀ y ∈ B, ∀ j ∈ Finset.Icc 3 (p + 2),
      poly y j ≤ ENNReal.ofReal Bpoly * I420Case1.powMomentAt π 1 o ^ (j - 3) :=
  ⟨h.nonneg, h.bound⟩

/-! ## §1. Axiom dependence of the primitive -/

#print axioms I417SummedClose.moment_gap_le_markedPairSum
#print axioms I417SummedClose.markedPairSum_eq_markedGapPoly
#print axioms I417SummedClose.moment_gap_le_markedGapPoly
#print axioms I417SummedClose.moment_gap_le_markedGapPoly_of_transitive
#print axioms I417SummedClose.moment_gap_le_markedGapPoly_basepoint
#print axioms I417SummedClose.momentDiff_nonneg_basepoint_of_transitive
#print axioms TreeExpansion.latticeLongRange_moment_gap_le_markedGapPoly

/-! ## §2. Moment bridges between the I.4.17 vocabulary and the Case 3 vocabulary

`I417A.momentProd`/`I417A.rawDiff` are built from `Percolation.cardFun (cluster ω v)`,
while `I420Case1.powMomentAt`/`I420Case3.pairExcl` are built from `clusterVol ω v`.
These are *different* definitions (`cardFun` is the finite-subset supremum of
`BK/ClusterCardinal`, `clusterVol` is the `encard` of the cluster); they agree only
because `Percolation.cardFun_eq_encard` identifies the two cardinality functionals.
The three lemmas below are the only bridges, and they are what makes the I.4.17
statement usable at the Case 3 interfaces. -/

/-- `clusterVol ω v = cardFun (K_v)`: the Case 1/3 volume notation and the BK
cardinality functional are the same function of the cluster. -/
theorem clusterVol_eq_cardFun {V : Type*} (ω : Config V) (v : V) :
    clusterVol ω v = Percolation.cardFun (cluster ω v) :=
  (Percolation.cardFun_eq_encard (cluster ω v)).symm

/-- `E|K_v|^a` in the Case 1/3 vocabulary equals the `cardFun` integral used inside
I.4.17. -/
theorem powMomentAt_eq_lintegral_cardFun {V : Type*} [Countable V] (π : Sym2 V → unitInterval)
    (a : ℕ) (v : V) :
    I420Case1.powMomentAt π a v =
      ∫⁻ ω, Percolation.cardFun (cluster ω v) ^ a ∂(edgeMeasure π) := by
  rw [I420Case1.powMomentAt]
  exact lintegral_congr fun ω => by rw [clusterVol_eq_cardFun]

/-- `E|K_v|` in the I.4.17 vocabulary (`I417.meanVol`, the τ-row sum) is the first
cluster moment `powMomentAt · 1`.  This is the identity that matches the `χ`-powers of
`markedGapPoly` against the `M`-powers of `I420Case3.treePoly`. -/
theorem meanVol_eq_powMomentAt_one {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (v : V) :
    I417.meanVol π v = I420Case1.powMomentAt π 1 v := by
  rw [I417.meanVol, I417.tsum_connSet_eq_lintegral, I420Case1.powMomentAt]
  exact lintegral_congr fun ω => by rw [pow_one, clusterVol_eq_cardFun]

/-- **The product factor is the I.4.17 product moment.**  `pairFactor π o y a b` and
`I417A.momentProd π o y a b` are the same `ℝ≥0∞` number. -/
theorem pairFactor_eq_momentProd {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (o y : V)
    (a b : ℕ) :
    I420Case3.pairFactor π o y a b = I417A.momentProd π o y a b := by
  rw [I420Case3.pairFactor, I417A.momentProd, powMomentAt_eq_lintegral_cardFun,
    powMomentAt_eq_lintegral_cardFun]

/-- **The pair excluded expectation is `I417A.rawDiff`.**  `pairExcl π o y a b` and
`I417A.rawDiff π o y a b` are the same `ℝ≥0∞` number, including the `¬Connects`
indicator and the order of the two factors. -/
theorem pairExcl_eq_rawDiff {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (o y : V)
    (a b : ℕ) :
    I420Case3.pairExcl π o y a b = I417A.rawDiff π o y a b := by
  rw [I420Case3.pairExcl, I417A.rawDiff, I417A.notConnSet]
  exact lintegral_congr fun ω => by
    simp only [clusterVol_eq_cardFun]

/-! ## §3. The composition's printed normal form against `I420Case3.treePoly`

`markedGapPoly π p q χ x y` is a sum over path lengths `L ∈ [3, p+q+1]` with
`χ`-power `2p+2q+1-L` and the *natural*-number coefficient `composedCoeff p q L`
cast to `ℝ≥0∞`.  `I420Case3.treePoly poly C M p y` is a sum over `j ∈ [3, p+2]`
with `M`-power `2p+3-j` and the *real* coefficient `C j` cast by `ENNReal.ofReal`.

They agree exactly on the Case 3 parameter surface `a = ℓ+1`, `b = p-ℓ`, i.e. at
`p = a+b-1`, `M = χ = E|K|`: the ranges are `[3, a+b+1] = [3, (a+b-1)+2]` and the
exponents are `2a+2b+1-L = 2(a+b-1)+3-L`.  The interval and the exponent are *not*
syntactically equal, so this is proved as an equality of `ℝ≥0∞` numbers below and is
not claimed to be a definitional unfolding. -/

/-- The real coefficient of `treePoly` and the natural coefficient of `markedGapPoly`
agree after `ENNReal.ofReal` resp. the natural cast. -/
theorem ofReal_composedCoeff (a b j : ℕ) :
    ENNReal.ofReal ((I417SummedClose.composedCoeff a b j : ℕ) : ℝ) =
      (I417SummedClose.composedCoeff a b j : ℝ≥0∞) :=
  ENNReal.ofReal_natCast _

/-- The composition coefficients are non-negative, which is the `hC` hypothesis of the
Case 3 assembly (`I420Case3.case3_i421_family`). -/
theorem composedCoeff_nonneg (a b j : ℕ) :
    0 ≤ (I417SummedClose.composedCoeff a b j : ℝ) :=
  Nat.cast_nonneg _

/-- **The printed normal form of I.4.17 is the Case 3 tree polynomial.**  For `a, b ≥ 1`
and `p = a+b-1`, `markedGapPoly` with the `T`-powers
`poly y j = T^j(o,y)` and the integer coefficients `composedCoeff a b` *is*
`I420Case3.treePoly`. -/
theorem markedGapPoly_eq_treePoly {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (M : ℝ≥0∞) (o y : V) :
    I417SummedClose.markedGapPoly π a b M o y =
      I420Case3.treePoly
        (fun y j => I417Base.iterPow (fun u v => (edgeMeasure π) (connSet u v)) j o y)
        (fun j => (I417SummedClose.composedCoeff a b j : ℝ)) M (a + b - 1) y := by
  rw [I417SummedClose.markedGapPoly, I420Case3.treePoly,
    show a + b + 1 = (a + b - 1) + 2 from by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_natCast]
  rw [show 2 * (a + b - 1) + 3 - j = 2 * a + 2 * b + 1 - j from by
    have h : 2 * (a + b - 1) + 3 = 2 * a + 2 * b + 1 := by omega
    rw [h]]
  ring

/-! ## §4. The `HasTreeExpansion.expansion` obligation, discharged -/

/-- `ℝ≥0∞`: `A - B ≤ D ⇒ A ≤ B + D`.  This is the additive conversion the Case 3
interface needs, since I.4.17 is stored subtractively while `HasTreeExpansion` is
additive.  It holds with no side conditions. -/
theorem le_add_of_tsub_le {A B D : ℝ≥0∞} (h : A - B ≤ D) : A ≤ B + D := by
  rw [add_comm]
  exact tsub_le_iff_right.mp h

/-- **I.4.17 discharges the additive pair bound of `I420Case3.HasTreeExpansion`.**

Residual hypotheses, all of them explicit and none of them a finiteness or
subcriticality assumption: `hπ : ∀ e, π e < 1` (Bond--Küneth), `1 ≤ a`, `1 ≤ b`, and
the first-moment row constancy `hχ : ∀ v, meanVol π v = meanVol π o`.  The second
moment factor `E|K_y|^b` is *not* moved to `o`, which is exactly why the plain
`moment_gap_le_markedGapPoly` (and not its `_basepoint` variant) is the right input. -/
theorem pairFactor_le_pairExcl_add_treePoly {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o y : V) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π o) :
    I420Case3.pairFactor π o y a b ≤
      I420Case3.pairExcl π o y a b +
        I420Case3.treePoly
          (fun y j => I417Base.iterPow (fun u v => (edgeMeasure π) (connSet u v)) j o y)
          (fun j => (I417SummedClose.composedCoeff a b j : ℝ))
          (I420Case1.powMomentAt π 1 o) (a + b - 1) y := by
  have h := I417SummedClose.moment_gap_le_markedGapPoly π hπ o y ha hb hχ
  rw [← pairFactor_eq_momentProd, ← pairExcl_eq_rawDiff, meanVol_eq_powMomentAt_one,
    markedGapPoly_eq_treePoly π a b ha hb (I420Case1.powMomentAt π 1 o) o y] at h
  exact le_add_of_tsub_le h

/-- **The `expansion` field of `I420Case3.HasTreeExpansion`, from Lemma I.4.17.**

`B` is an arbitrary finite set: `B = ∅` gives the vacuous record, and the Case 3
assembly supplies its own non-emptiness (`hcard : 0 < (B r).card`).  No condition on
`B` or on `π` beyond `hπ` is used. -/
theorem hasTreeExpansion_of_i417 {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o : V) (B : Finset V) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π o) :
    I420Case3.HasTreeExpansion π o B a b (a + b - 1)
      (fun y j => I417Base.iterPow (fun u v => (edgeMeasure π) (connSet u v)) j o y)
      (fun j => (I417SummedClose.composedCoeff a b j : ℝ)) :=
  ⟨fun y _ => pairFactor_le_pairExcl_add_treePoly π hπ o y ha hb hχ⟩

/-- **The producer at the assembly's own parameter surface.**  The Case 3 assembly
(`I420Case3.case3_hAend_hAmid`) demands `HasTreeExpansion (π r) o (B r) (ℓ+1) (p-ℓ) p`
for *every* `ℓ ≤ p`; the producer supplies it for `ℓ + 1 ≤ p` (so that the second
exponent `b = p-ℓ` is at least `1`), with the record's `p`-slot correctly instantiated
at `a+b-1 = p`.  The instance `ℓ = p` (`b = 0`) is outside the reach of I.4.17, whose
statement needs `1 ≤ q`; it occurs inside the assembly only through the auxiliary
uniform bound `hone : ∀ ℓ, ℓ ≤ p → …`, whose conclusion is used at `ℓ = 0` and
`1 ≤ ℓ ≤ p-2` alone.  See `docs/CRITICAL_LRP_I420.md` for the residual obligation
that this leaves at the existing broader consumer interface. -/
theorem hasTreeExpansion_family {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o : V) (B : Finset V)
    {p ℓ : ℕ} (hℓ : ℓ + 1 ≤ p) (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π o) :
    I420Case3.HasTreeExpansion π o B (ℓ + 1) (p - ℓ) p
      (fun y j => I417Base.iterPow (fun u v => (edgeMeasure π) (connSet u v)) j o y)
      (fun j => (I417SummedClose.composedCoeff (ℓ + 1) (p - ℓ) j : ℝ)) := by
  have hb : 1 ≤ p - ℓ := by omega
  have hsum : ℓ + 1 + (p - ℓ) - 1 = p := by omega
  simpa only [hsum] using
    hasTreeExpansion_of_i417 π hπ o B (a := ℓ + 1) (b := p - ℓ) (by omega) hb hχ

/-! ## §5. The exponent bookkeeping of the tree × polygon collapse -/

/-- In `treePoly`, the `j`-th term carries `M^(2p+3-j)`; in `HasPolygonBound` the same
`j`-th `poly` is bounded by `Bpoly · M^(j-3)`.  Multiplying the two powers therefore
gives exactly `M^(2p)`, independently of `j`, which is the reason the Case 3 assembly's
conclusion `discR ≤ (Σ_j C_j)·Bpoly·(E|K|)^{2p}` has no `j`-dependence left. -/
theorem exponent_split (p j : ℕ) (h3 : 3 ≤ j) (hj : j ≤ p + 2) :
    (2 * p + 3 - j) + (j - 3) = 2 * p := by
  have hle : j - 3 ≤ 2 * p := by omega
  have he : 2 * p + 3 - j = 2 * p - (j - 3) := by omega
  rw [he, Nat.sub_add_cancel hle]

/-- The producer's honest parameter range for the assembly's `ℓ`-indexed tree
hypothesis: the second exponent `b = p-ℓ` is at least `1` exactly for `ℓ ≤ p-1`.
`I420Case3.case3_hAend_hAmid` demands the record for all `ℓ ≤ p`, which includes the
uncovered case `ℓ = p` (`b = 0`). -/
theorem producer_range {p ℓ : ℕ} (h : ℓ + 1 ≤ p) : 1 ≤ p - ℓ := by
  omega

/-- The instance the assembly demands but I.4.17 cannot serve: at `ℓ = p` the second
exponent is `0`. -/
theorem producer_range_excluded (p : ℕ) : ¬ (1 ≤ p - p) := by
  rw [Nat.sub_self]
  omega

/-! ## §6. Axiom audit of the audit, and of the Case 3 consumer chain -/

#print axioms pairFactor_le_pairExcl_add_treePoly
#print axioms hasTreeExpansion_of_i417
#print axioms hasTreeExpansion_family
#print axioms markedGapPoly_eq_treePoly
#print axioms meanVol_eq_powMomentAt_one
#print axioms pairExcl_eq_rawDiff
#print axioms pairFactor_eq_momentProd
#print axioms I420Case3.prodFactor_le_mixedExcl_add_polygon
#print axioms I420Case3.discR_le_polygon
#print axioms I420Case3.case3_i421_family
#print axioms I420Case3.case3_hAend_hAmid_of_hIH

end AuditM1

end PercLib.CriticalLRP
