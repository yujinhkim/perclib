/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Lattice geometry on `ℤ^d`: box counts and sharp summability of the long-range
kernel, for Hutchcroft, "Critical long-range percolation I",
arXiv:2508.18807v1, Definition I.1.3 (normalisation (∗)).

We use the supremum norm `‖y‖_∞ = max_i |y_i|` on `Fin d → ℤ`. The two facts
established here are

* `card_box`: the number of lattice points with `‖y‖_∞ ≤ n` is exactly
  `(2n+1)^d` — the exact form of `|B_r| ~ r^d` in (∗), and
* `summable_one_add_linfNorm_rpow`: `∑_{y ∈ ℤ^d} (1 + ‖y‖_∞)^{-s} < ∞`
  for every `s > d`.

The second is the sharp summability threshold: with `s = d + α` it gives
`∑_{y ≠ 0} ‖y‖^{-d-α} < ∞` for every `α > 0`, the kernel summability
underlying finiteness of the expected degree and of the subcritical
susceptibility. The bound comes from exact layer counting:
`#{y : ‖y‖_∞ = n} = #B_n − #B_{n−1}`, and
`(2n+1)^d − (2n−1)^d ≤ 2d (2n+1)^{d−1}`.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell
public import PercLib.CriticalLRP.KernelGeometry
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.FiniteVolume

/-! ## The supremum norm on `ℤ^d` and boxes -/

/-- The supremum norm of a lattice point, as a natural number. -/
noncomputable def linfNorm {d : ℕ} (y : Fin d → ℤ) : ℕ :=
  Finset.univ.sup fun i => (y i).natAbs

theorem linfNorm_le_iff {d : ℕ} {y : Fin d → ℤ} {n : ℕ} :
    linfNorm y ≤ n ↔ ∀ i, (y i).natAbs ≤ n := by
  unfold linfNorm
  rw [Finset.sup_le_iff]
  simp

theorem linfNorm_nonneg {d : ℕ} (y : Fin d → ℤ) : 0 ≤ linfNorm y := Nat.zero_le _

theorem natAbs_le_iff_int {a : ℤ} {n : ℕ} :
    a.natAbs ≤ n ↔ -(n : ℤ) ≤ a ∧ a ≤ (n : ℤ) := by
  constructor
  · intro h
    constructor
    · omega
    · omega
  · intro h
    omega

theorem linfNorm_eq_zero_iff {d : ℕ} {y : Fin d → ℤ} : linfNorm y = 0 ↔ y = 0 := by
  constructor
  · intro h
    have h' : ∀ i, (y i).natAbs = 0 := by
      intro i
      have h2 : linfNorm y ≤ 0 := by omega
      rw [linfNorm_le_iff] at h2
      exact Nat.le_zero.mp (h2 i)
    funext i
    exact Int.natAbs_eq_zero.mp (h' i)
  · rintro rfl
    apply le_antisymm
    · rw [linfNorm_le_iff]
      simp
    · exact Nat.zero_le _

/-- The lattice box `B_n = {y ∈ ℤ^d : ‖y‖_∞ ≤ n}`. -/
noncomputable def box (d : ℕ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ)

theorem mem_box_iff {d n : ℕ} {y : Fin d → ℤ} :
    y ∈ box d n ↔ linfNorm y ≤ n := by
  rw [linfNorm_le_iff]
  constructor
  · intro h i
    have h' := Fintype.mem_piFinset.mp h i
    rw [Finset.mem_Icc] at h'
    exact natAbs_le_iff_int.mpr h'
  · intro h
    refine Fintype.mem_piFinset.mpr fun i => ?_
    rw [Finset.mem_Icc]
    exact natAbs_le_iff_int.mp (h i)

theorem box_mono {d : ℕ} {n m : ℕ} (h : n ≤ m) : box d n ⊆ box d m := by
  intro y hy
  rw [mem_box_iff] at hy ⊢
  exact le_trans hy h

/-- **The exact box count** `|B_n| = (2n+1)^d` of (∗). -/
theorem card_box {d : ℕ} (n : ℕ) : (box d n).card = (2 * n + 1) ^ d := by
  rw [box, Fintype.card_piFinset]
  have hterm : ∀ _ : Fin d, (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    intro _
    rw [Int.card_Icc]
    have h' : (n : ℤ) + 1 - (-(n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h', Int.toNat_natCast]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **Layer counting**: `#{y : ‖y‖_∞ = n} = |B_n| − |B_{n−1}|`. -/
theorem card_box_sdiff {d n : ℕ} :
    ((box d (n + 1)) \ (box d n)).card = (2 * (n + 1) + 1) ^ d - (2 * n + 1) ^ d := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (box_mono (d := d) (Nat.le_succ n)),
    card_box, card_box]

/-- `(2n+3)^d − (2n+1)^d ≤ 2d (2n+3)^{d−1}`: the layer sizes grow like `n^{d−1}`. -/
theorem layer_le (d n : ℕ) :
    (((2 * (n + 1) + 1) ^ d - (2 * n + 1) ^ d : ℕ) : ℝ)
      ≤ 2 * (d : ℝ) * ((2 * n + 3 : ℕ) : ℝ) ^ (d - 1) := by
  have hkey : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
  rw [hkey]
  set a : ℝ := ((2 * n + 3 : ℕ) : ℝ) with ha
  set b : ℝ := ((2 * n + 1 : ℕ) : ℝ) with hb
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hb0 : (0 : ℝ) ≤ b := by rw [hb]; positivity
  have hba : b ≤ a := by
    rw [ha, hb]; exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * n + 3)
  have hcast : (((2 * n + 3) ^ d - (2 * n + 1) ^ d : ℕ) : ℝ) = a ^ d - b ^ d := by
    rw [ha, hb, Nat.cast_sub (Nat.pow_le_pow_left (by omega : 2 * n + 1 ≤ 2 * n + 3) d)]
    push_cast
    ring
  rw [hcast]
  have hnonneg : (0 : ℝ) ≤ a ^ d - b ^ d := sub_nonneg.mpr (pow_le_pow_left₀ hb0 hba d)
  have habs : a ^ d - b ^ d = |a ^ d - b ^ d| := (abs_of_nonneg hnonneg).symm
  rw [habs]
  have h1 := abs_pow_sub_pow_le a b d
  have hmax : max |a| |b| = a := by
    rw [abs_of_nonneg ha0, abs_of_nonneg hb0, max_eq_left hba]
  have hdiff : |a - b| = 2 := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b), ha, hb]
    push_cast
    ring
  rw [hmax, hdiff] at h1
  calc |a ^ d - b ^ d| ≤ 2 * (d : ℝ) * a ^ (d - 1) := h1


/-! ## Sharp summability of the long-range kernel -/

/-- The radial test function `n ↦ (1 + n)^{-s}` is antitone. -/
theorem antitone_one_add_rpow {s : ℝ} (hs : 0 < s) :
    Antitone (fun n : ℕ => (1 + (n : ℝ)) ^ (-s)) := by
  intro m n hmn
  have hm : (0 : ℝ) < 1 + (m : ℝ) := by positivity
  have hle : 1 + (m : ℝ) ≤ 1 + (n : ℝ) := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  exact Real.rpow_le_rpow_of_nonpos hm hle (by linarith)

/-- `B_0` is the singleton `{0}`. -/
theorem box_zero_eq_singleton (d : ℕ) : box d 0 = {(0 : Fin d → ℤ)} := by
  ext y
  rw [Finset.mem_singleton, mem_box_iff]
  constructor
  · intro h
    have h0 : linfNorm y = 0 := Nat.le_zero.mp h
    exact linfNorm_eq_zero_iff.mp h0
  · rintro rfl
    exact Nat.le_zero.mpr (linfNorm_eq_zero_iff.mpr rfl)

/-- The value of `‖·‖_∞` on a layer `B_{m+1} \ B_m`. -/
theorem linfNorm_eq_of_mem_sdiff {d m : ℕ} {y : Fin d → ℤ}
    (hy : y ∈ box d (m + 1) \ box d m) : linfNorm y = m + 1 := by
  rw [Finset.mem_sdiff, mem_box_iff, mem_box_iff] at hy
  omega

/-- **Layer decomposition of a box sum**:
`∑_{y ∈ B_N} g(‖y‖_∞) = g(0) + ∑_{m<N} #{B_{m+1} \ B_m} · g(m+1)`. -/
theorem sum_box_eq (d N : ℕ) (g : ℕ → ℝ) :
    ∑ y ∈ box d N, g (linfNorm y)
      = g 0 + ∑ m ∈ range N, ((box d (m + 1) \ box d m).card : ℝ) * g (m + 1) := by
  induction N with
  | zero =>
      rw [box_zero_eq_singleton, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
        add_zero, show linfNorm (0 : Fin d → ℤ) = 0 from linfNorm_eq_zero_iff.mpr rfl]
  | succ N ih =>
      have hsub : box d N ⊆ box d (N + 1) := box_mono (Nat.le_succ N)
      have hunion : box d N ∪ (box d (N + 1) \ box d N) = box d (N + 1) :=
        Finset.union_sdiff_of_subset hsub
      rw [← hunion, Finset.sum_union Finset.disjoint_sdiff, ih, Finset.sum_range_succ]
      have hB : ∑ y ∈ box d (N + 1) \ box d N, g (linfNorm y)
          = ((box d (N + 1) \ box d N).card : ℝ) * g (N + 1) := by
        rw [Finset.sum_congr rfl (fun y hy => by rw [linfNorm_eq_of_mem_sdiff hy]),
          Finset.sum_const, nsmul_eq_mul]
      rw [hB]
      ring


/-- One term of the layer sum. -/
theorem layer_bound (d m : ℕ) {s : ℝ} (hs : (d : ℝ) < s) :
    ((box d (m + 1) \ box d m).card : ℝ) * (1 + ((m + 1 : ℕ) : ℝ)) ^ (-s)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s) := by
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt (Nat.cast_nonneg d) hs
  have hbase : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hcard : ((box d (m + 1) \ box d m).card : ℝ)
      ≤ 2 * (d : ℝ) * ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1) := by
    rw [card_box_sdiff]
    exact layer_le d m
  have hg : (0 : ℝ) < (1 + ((m + 1 : ℕ) : ℝ)) ^ (-s) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hstep1 : ((box d (m + 1) \ box d m).card : ℝ) * (1 + ((m + 1 : ℕ) : ℝ)) ^ (-s)
      ≤ (2 * (d : ℝ) * ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1))
          * (1 + ((m + 1 : ℕ) : ℝ)) ^ (-s) :=
    mul_le_mul_of_nonneg_right hcard hg.le
  have h3m : ((2 * m + 3 : ℕ) : ℝ) ≤ 3 * ((m + 1 : ℕ) : ℝ) := by
    have h : 2 * m + 3 ≤ 3 * (m + 1) := by omega
    exact_mod_cast h
  have hpow : ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1)
      ≤ 3 ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (d - 1) := by
    have h0 : (0 : ℝ) ≤ ((2 * m + 3 : ℕ) : ℝ) := by positivity
    calc ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1)
        ≤ (3 * ((m + 1 : ℕ) : ℝ)) ^ (d - 1) := pow_le_pow_left₀ h0 h3m _
      _ = 3 ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (d - 1) := by rw [mul_pow]
  have hrpow : (1 + ((m + 1 : ℕ) : ℝ)) ^ (-s) ≤ ((m + 1 : ℕ) : ℝ) ^ (-s) := by
    refine Real.rpow_le_rpow_of_nonpos hbase ?_ (by linarith : -s ≤ 0)
    linarith
  have hexp : ((m + 1 : ℕ) : ℝ) ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (-s)
      = ((m + 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s) := by
    rw [← Real.rpow_natCast ((m + 1 : ℕ) : ℝ) (d - 1), ← Real.rpow_add hbase, sub_eq_add_neg]
  calc ((box d (m + 1) \ box d m).card : ℝ) * (1 + ((m + 1 : ℕ) : ℝ)) ^ (-s)
      ≤ (2 * (d : ℝ) * ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1))
          * (1 + ((m + 1 : ℕ) : ℝ)) ^ (-s) := hstep1
    _ ≤ (2 * (d : ℝ) * (3 ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (d - 1)))
          * ((m + 1 : ℕ) : ℝ) ^ (-s) := by
        gcongr
    _ = 2 * (d : ℝ) * 3 ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s) := by
        rw [← hexp]; ring

/-- **Sharp summability of the long-range kernel**: for `d ≥ 1` and `s > d`,
`∑_{y ∈ ℤ^d} (1 + ‖y‖_∞)^{-s}` converges. With `s = d + α` this is the kernel
summability `∑_{y ≠ 0} ‖y‖^{-d-α} < ∞` required for every `α > 0`. -/
theorem summable_one_add_linfNorm_rpow {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) :
    Summable (fun y : Fin d → ℤ => (1 + (linfNorm y : ℝ)) ^ (-s)) := by
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt (Nat.cast_nonneg d) hs
  set g : ℕ → ℝ := fun n => (1 + (n : ℝ)) ^ (-s) with hg
  have hgpos : ∀ n, 0 < g n := fun n => Real.rpow_pos_of_pos (by positivity) _
  set T : ℝ := ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s) with hT
  have hdcast : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
    have := Nat.cast_sub hd (R := ℝ)
    simpa using this
  have hTsum : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s)) := by
    have hiff := (summable_nat_add_iff
      (f := fun n : ℕ => (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s)) 1).mpr
      ((Real.summable_nat_rpow (p := (((d - 1 : ℕ) : ℝ) - s))).mpr (by
        rw [hdcast]; linarith))
    exact hiff
  have hTnn : 0 ≤ T :=
    tsum_nonneg (fun m => Real.rpow_nonneg (by positivity) _)
  refine summable_of_sum_le (c := g 0 + 2 * (d : ℝ) * 3 ^ (d - 1) * T)
    (fun y => (hgpos _).le) ?_
  intro u
  set N := u.sup linfNorm with hN
  have huN : u ⊆ box d N := by
    intro y hy
    rw [mem_box_iff]
    exact Finset.le_sup (f := fun y : Fin d → ℤ => linfNorm y) hy
  have h1 : ∑ y ∈ u, g (linfNorm y) ≤ ∑ y ∈ box d N, g (linfNorm y) :=
    Finset.sum_le_sum_of_subset_of_nonneg huN (fun i _ _ => (hgpos _).le)
  have h2 : ∑ y ∈ box d N, g (linfNorm y)
      = g 0 + ∑ m ∈ range N, ((box d (m + 1) \ box d m).card : ℝ) * g (m + 1) :=
    sum_box_eq d N g
  have h3 : ∑ m ∈ range N, ((box d (m + 1) \ box d m).card : ℝ) * g (m + 1)
      ≤ ∑ m ∈ range N,
          2 * (d : ℝ) * 3 ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s) :=
    Finset.sum_le_sum fun m _ => layer_bound d m hs
  have h4 : ∑ m ∈ range N,
        2 * (d : ℝ) * 3 ^ (d - 1) * ((m + 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) - s)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * T := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hTsum.sum_le_tsum (range N) (fun m _ => Real.rpow_nonneg (by positivity) _)
  refine le_trans h1 ?_
  rw [h2]
  linarith



/-- **Summability of the long-range kernel itself**: for `d ≥ 1` and `α > 0`,
`∑_{y} ‖y‖_∞^{-(d+α)} < ∞`. This is the summability of the kernel
`J(0,y) = ‖y‖^{-d-α}` of (I.1.1) at `x = 0`, and hence the finiteness of the
expected degree. -/
theorem summable_linfNorm_rpow {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) :
    Summable (fun y : Fin d → ℤ => (linfNorm y : ℝ) ^ (-s)) := by
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt (Nat.cast_nonneg d) hs
  have hmain := summable_one_add_linfNorm_rpow hd hs
  have hbound : Summable (fun y : Fin d → ℤ => (2 : ℝ) ^ s * (1 + (linfNorm y : ℝ)) ^ (-s)) :=
    hmain.mul_left _
  refine Summable.of_nonneg_of_le (fun y => Real.rpow_nonneg (by positivity) _) ?_ hbound
  intro y
  rcases Nat.eq_zero_or_pos (linfNorm y) with h | h
  · rw [h]
    have hz : ((0 : ℕ) : ℝ) = (0 : ℝ) := by norm_num
    rw [hz, Real.zero_rpow (by linarith : -s ≠ 0)]
    positivity
  · have h1 : (1 : ℝ) ≤ (linfNorm y : ℝ) := by exact_mod_cast h
    have hpos : (0 : ℝ) < (linfNorm y : ℝ) := by linarith
    have h2 : 1 + (linfNorm y : ℝ) ≤ 2 * (linfNorm y : ℝ) := by linarith
    have h3 : (2 * (linfNorm y : ℝ)) ^ (-s) ≤ (1 + (linfNorm y : ℝ)) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
    have h4 : (2 * (linfNorm y : ℝ)) ^ (-s)
        = (2 : ℝ) ^ (-s) * (linfNorm y : ℝ) ^ (-s) := Real.mul_rpow (by norm_num) hpos.le
    have h5 : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
    have h6 : (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s = 1 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      simp
    calc (linfNorm y : ℝ) ^ (-s)
        = 1 * (linfNorm y : ℝ) ^ (-s) := (one_mul _).symm
      _ = ((2 : ℝ) ^ (-s) * (2 : ℝ) ^ s) * (linfNorm y : ℝ) ^ (-s) := by rw [h6]
      _ = (2 : ℝ) ^ s * ((2 : ℝ) ^ (-s) * (linfNorm y : ℝ) ^ (-s)) := by ring
      _ ≤ (2 : ℝ) ^ s * (1 + (linfNorm y : ℝ)) ^ (-s) := by
          refine mul_le_mul_of_nonneg_left ?_ h5.le
          rw [← h4]
          exact h3



/-- **The two-sided box estimate (∗)**: `|B_n| ≍ n^d`, in exact form. -/
theorem card_box_ge (d n : ℕ) : n ^ d ≤ (box d n).card := by
  rw [card_box]
  exact Nat.pow_le_pow_left (by omega : n ≤ 2 * n + 1) d

theorem card_box_le (d n : ℕ) (_hn : 1 ≤ n) : (box d n).card ≤ 3 ^ d * n ^ d := by
  rw [card_box]
  calc (2 * n + 1) ^ d ≤ (3 * n) ^ d := Nat.pow_le_pow_left (by omega : 2 * n + 1 ≤ 3 * n) d
    _ = 3 ^ d * n ^ d := by rw [mul_pow]



/-! ## The lattice distance `‖x − y‖_∞` and its kernel summability

These supply the hypotheses of `cutoffProfile_dominated` and
`cutoffKernel_le_radialKernel` (distinct lattice points are at distance `≥ 1`)
and the kernel summability at an arbitrary base point. -/

/-- The lattice distance `‖x − y‖_∞`, as a real number. -/
noncomputable def latticeDist {d : ℕ} (x y : Fin d → ℤ) : ℝ := (linfNorm (x - y) : ℝ)

theorem linfNorm_congr {d : ℕ} {y y' : Fin d → ℤ}
    (h : ∀ i, (y i).natAbs = (y' i).natAbs) : linfNorm y = linfNorm y' := by
  have key : ∀ n, linfNorm y ≤ n ↔ linfNorm y' ≤ n := by
    intro n
    rw [linfNorm_le_iff, linfNorm_le_iff]
    simp only [h]
  exact le_antisymm ((key (linfNorm y')).mpr le_rfl) ((key (linfNorm y)).mp le_rfl)

theorem linfNorm_neg {d : ℕ} (z : Fin d → ℤ) : linfNorm (-z) = linfNorm z :=
  linfNorm_congr fun i => by simp

theorem latticeDist_self {d : ℕ} (x : Fin d → ℤ) : latticeDist x x = 0 := by
  unfold latticeDist
  rw [sub_self]
  exact_mod_cast (linfNorm_eq_zero_iff.mpr rfl : linfNorm (0 : Fin d → ℤ) = 0)

/-- Distinct lattice points are at distance at least `1`: this is the
normalisation `|B_1| = 1` implicit in (∗). -/
theorem one_le_latticeDist {d : ℕ} {x y : Fin d → ℤ} (h : x ≠ y) : 1 ≤ latticeDist x y := by
  have hne : x - y ≠ 0 := sub_ne_zero.mpr h
  have hpos : 0 < linfNorm (x - y) := by
    rcases Nat.eq_zero_or_pos (linfNorm (x - y)) with h0 | h0
    · exact absurd (linfNorm_eq_zero_iff.mp h0) hne
    · exact h0
  have h1 : (1 : ℕ) ≤ linfNorm (x - y) := hpos
  unfold latticeDist
  exact_mod_cast h1

theorem latticeDist_pos {d : ℕ} {x y : Fin d → ℤ} (h : x ≠ y) : 0 < latticeDist x y :=
  lt_of_lt_of_le zero_lt_one (one_le_latticeDist h)

theorem latticeDist_comm {d : ℕ} (x y : Fin d → ℤ) :
    latticeDist x y = latticeDist y x := by
  unfold latticeDist
  rw [← neg_sub y x, linfNorm_neg]

/-- **Kernel summability at an arbitrary base point**:
`∑_{y} ‖x − y‖_∞^{-s} < ∞` for `d ≥ 1` and `s > d`. -/
theorem summable_latticeDist {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    (x : Fin d → ℤ) : Summable (fun y : Fin d → ℤ => latticeDist x y ^ (-s)) := by
  have hmain : Summable (fun z : Fin d → ℤ => (linfNorm z : ℝ) ^ (-s)) :=
    summable_linfNorm_rpow hd hs
  have h := (Equiv.summable_iff (f := fun z : Fin d → ℤ => (linfNorm z : ℝ) ^ (-s))
    (Equiv.subLeft x)).mpr hmain
  simpa [latticeDist, Function.comp_def, Equiv.subLeft] using h



/-! ## Definition I.1.5 on `ℤ^d` with the model profile -/

theorem modelProfile_one (d : ℕ) {α : ℝ} : modelProfile d α 1 = 1 := by
  unfold modelProfile
  rw [Real.one_rpow]

/-- **Definition I.1.5 on the lattice**: on `ℤ^d` with the sup-norm distance and
the model profile `J(r) = r^{-d-α}`, the cut-off kernel is dominated by the
kernel, and for `r ≥ 1` strictly by `(1 - r^{-d-α})`:

`J_r(x,y) ≤ (1 - r^{-d-α}) J(x,y)` for every `x ≠ y`,

so `P_{β_c,r}` is stochastically dominated by `P_{(1-ε)β_c}` with
`ε = r^{-d-α} > 0`. -/
theorem cutoffKernel_lattice_dominated (d : ℕ) {α : ℝ} (hα : 0 < α)
    {r : ℝ} (hr : 1 ≤ r) {x y : Fin d → ℤ} (hxy : x ≠ y) :
    cutoffKernel (modelProfile d α) (latticeDist (d := d)) r x y
      ≤ (1 - modelProfile d α r) * radialKernel (modelProfile d α) (latticeDist (d := d)) x y := by
  have hαd : (0 : ℝ) ≤ (d : ℝ) + α := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hanti : AntitoneOn (modelProfile d α) (Set.Ioi 0) := modelProfile_antitoneOn d hαd
  have hKnn : ∀ t : ℝ, 0 < t → 0 ≤ modelProfile d α t := fun t ht => (modelProfile_pos ht).le
  have hs : (1 : ℝ) ≤ latticeDist x y := one_le_latticeDist hxy
  have hKr : 0 < modelProfile d α r := modelProfile_pos hr0
  have hK1 : 0 < modelProfile d α 1 := by rw [modelProfile_one]; norm_num
  rw [cutoffKernel_eq_of_ne _ _ r hxy, radialKernel_eq_of_ne _ _ hxy]
  have := cutoffProfile_dominated hanti hKnn hs hr hKr hK1
  simpa [modelProfile_one] using this

end PercLib.CriticalLRP.FiniteVolume
