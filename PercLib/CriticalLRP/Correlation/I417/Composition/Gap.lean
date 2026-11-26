/-
Direction `(D) FINAL COMPOSITION` of swarm `smwxtabcx`, member `m1`: the regrouping of the
un-grouped pair-of-depths normal form `markedPairSum` into the printed single-sum normal form
`∑_{L∈[3,p+q+1]} C_{p,q,L} χ^(2p+2q+1-L) T^L(x,y)` of Lemma I.4.17.

Read-only against production `repo/.scratch/critical-lrp-orchestration`
(HEAD `1cf119aa54facb618600bb09077747b6a3b891f3`, Lean 4.35.0).

`Closure.moment_gap_le_markedPairSum` bounds the two-copy moment gap by the product of the base and
fresh polynomials with the marked vertex summed out, i.e. by
`∑_{ℓ∈[2,p+1]} ∑_{m∈[1,q]} (q · C^{base}_{p,ℓ} · C^{fresh}_{q,m}) χ^(2p+2q+1-(ℓ+m)) T^(ℓ+m)(x,y)`.
The paper writes the same quantity grouped by the composed path length `L = ℓ + m`.  This file
proves the grouping identity (`markedPairSum_eq_markedGapPoly`) and hence the printed form.

The only arithmetic input is that the fresh coefficient `genCoeff q m` *vanishes* for
`m ∉ [1,q]` (`genCoeff_eq_zero_of_not_mem`), which holds because every branch of production's
iterated first-hit cover has pin--mark depth in `[1,q]` (`markDepthK_pos`, `markDepthK_le`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Composition.Pair

/-! Regrouping of the pair-depth polynomial by composed path length. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417SummedClose

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## 1. Vanishing of the fresh coefficient off the printed depth range -/

/-- The fresh coefficient vanishes outside the depth range `[1,q]`: no branch of the iterated
first-hit cover has pin--mark depth `0` or `> q`. -/
theorem genCoeff_eq_zero_of_not_mem {q m : ℕ} (hq : 1 ≤ q) (hm : m ∉ Finset.Icc 1 q) :
    I417FreshDepth.genCoeff q m = 0 := by
  rw [I417FreshDepth.genCoeff, I417FreshDepth.depthCount]
  refine Fintype.card_eq_zero_iff.mpr ⟨fun k => ?_⟩
  have hmem := I417FreshProfile.mem_Icc_markDepthK (n := q - 1) k.1
  rw [k.2, Nat.sub_add_cancel hq] at hmem
  exact hm hmem

/-! ## 2. Collapsing one `if` inside a finite sum -/

/-- A finite sum of `if L = a then F L else 0` over a set containing `a`. -/
theorem sum_ite_eq_single {u : Finset ℕ} {F : ℕ → ℝ≥0∞} {a : ℕ} (ha : a ∈ u) :
    (∑ L ∈ u, (if L = a then F L else 0)) = F a := by
  classical
  rw [Finset.sum_ite_eq']
  simp [ha]

/-! ## 3. The convolution regrouping, in scalar form -/

/-- **Regrouping a double sum by the value of `ℓ + m`.**  For nonnegative weights `A`, `B`, `P`, a
constant `Q`, and finite index sets `s`, `t ⊆ [1,∞)`, `u ⊇ s + t`:

  `∑_{ℓ∈s} ∑_{m∈t} (Q A_ℓ B_m) P(ℓ+m) = ∑_{L∈u} (Q ∑_{ℓ∈s} A_ℓ B_{L-ℓ}) P_L`,

provided `B` vanishes off `t` (so the terms with `L - ℓ ∉ t` vanish on both sides) and
`ℓ + m ∈ u` for `ℓ ∈ s`, `m ∈ t` (so no term is lost).  This is the paper's passage from the pair
of depths `(ℓ, m)` to the composed path length `L = ℓ + m`. -/
theorem sum_sum_group_eq {s t u : Finset ℕ} {A B P : ℕ → ℝ≥0∞} {Q : ℝ≥0∞}
    (hB : ∀ m, m ∉ t → B m = 0)
    (ht1 : ∀ m ∈ t, 1 ≤ m)
    (hu : ∀ ℓ ∈ s, ∀ m ∈ t, ℓ + m ∈ u) :
    (∑ ℓ ∈ s, ∑ m ∈ t, (Q * A ℓ * B m) * P (ℓ + m))
      = ∑ L ∈ u, (Q * ∑ ℓ ∈ s, A ℓ * B (L - ℓ)) * P L := by
  classical
  -- each term sits at the single index `L = ℓ + m`
  have hA : ∀ ℓ ∈ s, ∀ m ∈ t, (Q * A ℓ * B m) * P (ℓ + m)
      = ∑ L ∈ u, (if L = ℓ + m then (Q * A ℓ * B m) * P (ℓ + m) else 0) := by
    intro ℓ hℓ m hm
    exact (sum_ite_eq_single (F := fun _ => (Q * A ℓ * B m) * P (ℓ + m))
      (hu ℓ hℓ m hm)).symm
  rw [Finset.sum_congr rfl fun ℓ hℓ => Finset.sum_congr rfl fun m hm => hA ℓ hℓ m hm]
  rw [Finset.sum_congr rfl fun ℓ _ => Finset.sum_comm, Finset.sum_comm]
  -- the `ℓ`-fibre of the index `L`
  refine Finset.sum_congr rfl fun L _ => ?_
  have hterm : ∀ ℓ ∈ s,
      (∑ m ∈ t, (if L = ℓ + m then (Q * A ℓ * B m) * P (ℓ + m) else 0))
        = Q * (A ℓ * B (L - ℓ)) * P L := by
    intro ℓ hℓ
    by_cases hLt : L - ℓ ∈ t
    · have h1 : 1 ≤ L - ℓ := ht1 (L - ℓ) hLt
      rw [Finset.sum_eq_single (L - ℓ) ?_ ?_]
      · split
        · next h =>
          rw [show ℓ + (L - ℓ) = L from by omega]
          ring
        · next h => exact absurd (by omega : L = ℓ + (L - ℓ)) h
      · intro m _ hne
        split
        · next h => exact absurd (by omega : m = L - ℓ) hne
        · rfl
      · intro hmem
        exact absurd hLt hmem
    · have hzero : (∑ m ∈ t, (if L = ℓ + m then (Q * A ℓ * B m) * P (ℓ + m) else 0)) = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        split
        · next h =>
          exfalso
          refine hLt ?_
          have h1 : 1 ≤ m := ht1 m hm
          have h2 : L - ℓ = m := by omega
          rw [h2]
          exact hm
        · rfl
      rw [hzero, hB (L - ℓ) hLt]
      simp
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ℓ hℓ => hterm ℓ hℓ

/-! ## 4. The printed single-sum normal form -/

/-- **The un-grouped and printed normal forms of Lemma I.4.17 agree.**  Grouping the pair of depths
`(ℓ, m)` by `L = ℓ + m` turns `markedPairSum` into `markedGapPoly`:
`∑_{L∈[3,p+q+1]} C_{p,q,L} χ^(2p+2q+1-L) T^L(x,y)` with the integer coefficients
`C_{p,q,L} = q · ∑_{ℓ+m=L} C^{base}_{p,ℓ} C^{fresh}_{q,m}`. -/
theorem markedPairSum_eq_markedGapPoly (π : Sym2 V → unitInterval) (p q : ℕ) (hq : 1 ≤ q)
    (χ : ℝ≥0∞) (x y : V) :
    markedPairSum π p q χ x y = markedGapPoly π p q χ x y := by
  classical
  set s : Finset ℕ := Finset.Icc 2 (p + 1) with hs
  set t : Finset ℕ := Finset.Icc 1 q with ht
  set u : Finset ℕ := Finset.Icc 3 (p + q + 1) with hu
  have hBzero : ∀ m, m ∉ t → (I417FreshDepth.genCoeff q m : ℝ≥0∞) = 0 := by
    intro m hm
    have h0 : I417FreshDepth.genCoeff q m = 0 :=
      genCoeff_eq_zero_of_not_mem hq (by rwa [ht] at hm)
    rw [h0]
    simp
  have ht1 : ∀ m ∈ t, 1 ≤ m := by
    intro m hm
    rw [ht] at hm
    exact (Finset.mem_Icc.mp hm).1
  have hu' : ∀ ℓ ∈ s, ∀ m ∈ t, ℓ + m ∈ u := by
    intro ℓ hℓ m hm
    rw [hs] at hℓ
    rw [ht] at hm
    rw [hu]
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hℓ
    obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hLHS : markedPairSum π p q χ x y
      = ∑ ℓ ∈ s, ∑ m ∈ t, ((q : ℝ≥0∞) *
          (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (I417FreshDepth.genCoeff q m : ℝ≥0∞)) *
          (χ ^ (2 * p + 2 * q + 1 - (ℓ + m)) *
            I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) (ℓ + m) x y) := by
    rw [markedPairSum, ← hs, ← ht]
    refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  have hRHS : markedGapPoly π p q χ x y
      = ∑ L ∈ u, ((q : ℝ≥0∞) * ∑ ℓ ∈ s,
          (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (I417FreshDepth.genCoeff q (L - ℓ) : ℝ≥0∞)) *
          (χ ^ (2 * p + 2 * q + 1 - L) *
            I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) L x y) := by
    rw [markedGapPoly, ← hu]
    refine Finset.sum_congr rfl fun L _ => ?_
    simp only [composedCoeff]
    rw [← hs]
    push_cast
    ring
  rw [hLHS, hRHS]
  exact sum_sum_group_eq
    (A := fun ℓ => (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞))
    (B := fun m => (I417FreshDepth.genCoeff q m : ℝ≥0∞))
    (P := fun L => χ ^ (2 * p + 2 * q + 1 - L) *
      I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) L x y)
    (Q := (q : ℝ≥0∞)) hBzero ht1 hu'

/-! ## 5. Lemma I.4.17, unconditional, in the printed form -/

/-- **Lemma I.4.17's upper bound at general `p, q`, in the printed normal form, UNCONDITIONAL.**

For every countable vertex set `V`, every edge weight `π : Sym2 V → unitInterval` with `π e < 1`,
every constant row sum `χ = meanVol π x` of the two-point matrix, every `p, q ≥ 1` and every pair of
vertices `x, y`:

  `E|K_x|^p E|K_y|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)] ≤ ∑_{L=3}^{p+q+1} C_{p,q,L} χ^(2p+2q+1−L) T^L(x,y)`,

with integer coefficients `C_{p,q,L} = q · ∑_{ℓ+m=L} C^{base}_{p,ℓ} C^{fresh}_{q,m}` and
`T a b = P(a ↔ b)`.  Every monomial carries exactly `2p + 2q + 1` two-point factors and path depth
`L` in the source's range `[3, p+q+1]`.

There is no fresh-side hypothesis and no further regularity hypothesis beyond `hπ` (BK), `hp`,
`hq` and the constant row sum: the fresh side is `Fresh.tsum_freshMark_le_genFreshProfile`
(`q ≥ 2`) and `Fresh.tsum_freshMark_le_genFreshProfile_one` (`q = 1`), and the base side is
production's `jointPow_le_nonplane_markedDepth`. -/
theorem moment_gap_le_markedGapPoly (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      markedGapPoly π p q (I417.meanVol π x) x y :=
  (moment_gap_le_markedPairSum π hπ x y hp hq hχ).trans
    (le_of_eq (markedPairSum_eq_markedGapPoly π p q hq (I417.meanVol π x) x y))

/-- The same bound with the `L = 1` and `L = 2` coefficients explicitly absent and the total edge
count `2p+2q+1` visible: this is the shape the paper's Lemma I.4.17 displays, and it records that
the composed depth range is exactly `[3, p+q+1]`. -/
theorem moment_gap_le_markedGapPoly_explicit (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      ∑ L ∈ Finset.Icc 3 (p + q + 1),
        ((q * ∑ ℓ ∈ Finset.Icc 2 (p + 1),
            I417MarkedTransversal.nonplaneMarkedCount p ℓ *
              I417FreshDepth.genCoeff q (L - ℓ) : ℕ) : ℝ≥0∞) *
          ((I417.meanVol π x) ^ (2 * p + 2 * q + 1 - L) *
            I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) L x y) :=
  moment_gap_le_markedGapPoly π hπ x y hp hq hχ

end PercLib.CriticalLRP.I417SummedClose
