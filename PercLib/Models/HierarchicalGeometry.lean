/-
Exact hierarchical geometry. New proofs using the existing finite-support lattice
and mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679's finite cardinalities and sums.
No new notion of level, ball, or percolation law is introduced.
-/
module

public import PercLib.Models.Hierarchical
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card

@[expose] public section
noncomputable section
open scoped ENNReal NNReal Classical

namespace PercLib.Models

section Geometry
variable {A : Type*} [AddCommGroup A]

/-- The existing level bound is exactly a support bound. -/
theorem level_le_iff_support (z : ℕ →₀ A) (n : ℕ) :
    z.support.sup Nat.succ ≤ n ↔ ∀ i ∈ z.support, i < n := by
  simp only [Finset.sup_le_iff, Nat.succ_le_iff]

/-- Level zero singles out the zero vector. -/
theorem level_eq_zero_iff (z : ℕ →₀ A) : z.support.sup Nat.succ = 0 ↔ z = 0 := by
  constructor
  · intro h
    ext i
    by_contra hi
    have := (level_le_iff_support z 0).mp h.le i (Finsupp.mem_support_iff.mpr hi)
    omega
  · rintro rfl; simp

/-- The level is ultrametric under addition. -/
theorem level_add_le_max (x y : ℕ →₀ A) :
    (x + y).support.sup Nat.succ ≤ max (x.support.sup Nat.succ) (y.support.sup Nat.succ) := by
  apply (level_le_iff_support _ _).mpr
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_add hi) with hx | hy
  · exact lt_of_lt_of_le ((level_le_iff_support x _).mp le_rfl i hx) (le_max_left _ _)
  · exact lt_of_lt_of_le ((level_le_iff_support y _).mp le_rfl i hy) (le_max_right _ _)

/-- Displacement levels are symmetric. -/
theorem level_sub_comm (x y : ℕ →₀ A) :
    (y - x).support.sup Nat.succ = (x - y).support.sup Nat.succ := by
  rw [← neg_sub x y, Finsupp.support_neg]

/-- Displacement levels vanish precisely on the diagonal. -/
theorem level_sub_eq_zero_iff (x y : ℕ →₀ A) :
    (y - x).support.sup Nat.succ = 0 ↔ x = y := by
  rw [level_eq_zero_iff, sub_eq_zero, eq_comm]

/-- The strong triangle inequality for displacement levels. -/
theorem level_sub_le_max (x y z : ℕ →₀ A) :
    (z - x).support.sup Nat.succ ≤
      max ((y - x).support.sup Nat.succ) ((z - y).support.sup Nat.succ) := by
  have h : (y - x) + (z - y) = z - x := by abel
  simpa only [h] using level_add_le_max (y - x) (z - y)

/-- Translations preserve displacement levels. -/
theorem level_sub_add_right (x y g : ℕ →₀ A) :
    ((y + g) - (x + g)).support.sup Nat.succ = (y - x).support.sup Nat.succ := by
  simp

/-- Level balls carry the inherited additive subgroup structure. -/
theorem exists_addSubgroup_level_ball (n : ℕ) :
    ∃ B : AddSubgroup (ℕ →₀ A), ∀ z, z ∈ B ↔ z.support.sup Nat.succ ≤ n := by
  refine ⟨{ carrier := {z | z.support.sup Nat.succ ≤ n}
            zero_mem' := by simp
            add_mem' := fun hx hy => (level_add_le_max _ _).trans (max_le hx hy)
            neg_mem' := fun hx => by simpa only [Set.mem_ofPred_eq, Finsupp.support_neg] using hx }, fun _ => Iff.rfl⟩

/-- A translated level ball is a coset of its origin ball. -/
theorem level_ball_eq_translate (x : ℕ →₀ A) (n : ℕ) :
    {y | (y - x).support.sup Nat.succ ≤ n} =
      (fun z => x + z) '' {z | z.support.sup Nat.succ ≤ n} := by
  ext y
  constructor
  · intro h; exact ⟨y - x, h, by abel⟩
  · rintro ⟨z, hz, rfl⟩; simpa using hz

/-- Intersecting balls of the same level coincide. -/
theorem level_balls_eq_or_disjoint (x y : ℕ →₀ A) (n : ℕ) :
    {z | (z - x).support.sup Nat.succ ≤ n} = {z | (z - y).support.sup Nat.succ ≤ n} ∨
      Disjoint {z | (z - x).support.sup Nat.succ ≤ n} {z | (z - y).support.sup Nat.succ ≤ n} := by
  by_cases h : (y - x).support.sup Nat.succ ≤ n
  · left
    ext z
    constructor
    · intro hz
      exact (level_sub_le_max y x z).trans (max_le (by simpa [level_sub_comm] using h) hz)
    · intro hz
      exact (level_sub_le_max x y z).trans (max_le h hz)
  · right
    apply Set.disjoint_left.mpr
    intro z hx hy
    exact h ((level_sub_le_max x z y).trans (max_le hx (by simpa [level_sub_comm] using hy)))

/-- Restriction below n is a bijection between a level ball and n coefficient entries. -/
theorem level_ball_restrict_bijective (n : ℕ) :
    Function.Bijective (fun z : {z : ℕ →₀ A // z.support.sup Nat.succ ≤ n} =>
      fun i : Fin n => z.1 i) := by
  constructor
  · rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    apply Subtype.ext
    ext i
    by_cases hi : i < n
    · exact congrFun h ⟨i, hi⟩
    · have hz0 : z i = 0 := by
        by_contra h0; exact hi ((level_le_iff_support z n).mp hz i (Finsupp.mem_support_iff.mpr h0))
      have hw0 : w i = 0 := by
        by_contra h0; exact hi ((level_le_iff_support w n).mp hw i (Finsupp.mem_support_iff.mpr h0))
      rw [hz0, hw0]
  · intro f
    let z : ℕ →₀ A := Finsupp.onFinset (Finset.range n)
      (fun i => if h : i < n then f ⟨i, h⟩ else 0) (by
        intro i hi
        by_contra h
        have hn : ¬ i < n := by simpa using h
        simp [hn] at hi)
    have hz : z.support.sup Nat.succ ≤ n := by
      apply (level_le_iff_support z n).mpr
      intro i hi
      exact Finset.mem_range.mp (Finsupp.support_onFinset_subset hi)
    refine ⟨⟨z, hz⟩, ?_⟩
    funext i
    simp [z, i.isLt]

/-- A level ball has finitely many vectors whenever the coefficient group is finite. -/
theorem finite_level_ball [Finite A] (n : ℕ) : {z : ℕ →₀ A | z.support.sup Nat.succ ≤ n}.Finite := by
  have : Finite {z : ℕ →₀ A // z.support.sup Nat.succ ≤ n} :=
    Finite.of_injective _ (level_ball_restrict_bijective (A := A) n).1
  exact Set.finite_coe_iff.mp this

/-- A ball at the next level is the union of coefficient-indexed smaller balls. -/
theorem level_ball_succ_eq_iUnion (n : ℕ) :
    {z : ℕ →₀ A | z.support.sup Nat.succ ≤ n + 1} =
      ⋃ a : A, {z | (z - Finsupp.single n a).support.sup Nat.succ ≤ n} := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hz
    refine ⟨z n, (level_le_iff_support _ _).mpr ?_⟩
    intro i hi
    have hne : i ≠ n := by
      rintro rfl
      simpa using (Finsupp.mem_support_iff.mp hi)
    have hzi : z i ≠ 0 := by
      simpa [Finsupp.sub_apply, Finsupp.single_apply, Ne.symm hne] using Finsupp.mem_support_iff.mp hi
    have hil := (level_le_iff_support z _).mp hz i (Finsupp.mem_support_iff.mpr hzi)
    omega
  · rintro ⟨a, ha⟩
    have hs : (Finsupp.single n a : ℕ →₀ A).support.sup Nat.succ ≤ n + 1 := by
      apply (level_le_iff_support _ _).mpr
      intro i hi
      have := Finsupp.support_single_subset hi
      simp only [Finset.mem_singleton] at this
      omega
    have heq : (z - Finsupp.single n a) + Finsupp.single n a = z := sub_add_cancel _ _
    have h := (level_add_le_max (z - Finsupp.single n a) (Finsupp.single n a)).trans
      (max_le (ha.trans (Nat.le_succ n)) hs)
    rwa [heq] at h

/-- The smaller balls in that union are pairwise disjoint. -/
theorem pairwise_disjoint_level_ball_succ (n : ℕ) :
    Pairwise (fun a b : A => Disjoint
      {z : ℕ →₀ A | (z - Finsupp.single n a).support.sup Nat.succ ≤ n}
      {z : ℕ →₀ A | (z - Finsupp.single n b).support.sup Nat.succ ≤ n}) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro z ha hb
  have hv (c : A) (hc : (z - Finsupp.single n c).support.sup Nat.succ ≤ n) : z n = c := by
    by_contra h
    have hm : n ∈ (z - Finsupp.single n c).support := by
      simpa [Finsupp.mem_support_iff, sub_eq_zero] using h
    have := (level_le_iff_support _ _).mp hc n hm
    omega
  exact hab ((hv a ha).symm.trans (hv b hb))

end Geometry

variable {d L : ℕ}

/-- Exact ball cardinality; only nonzero L is required for this finite count. -/
theorem card_ball [NeZero L] (n : ℕ) :
    Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ ≤ n} = (L ^ d) ^ n := by
  let e := Equiv.ofBijective _ (level_ball_restrict_bijective (A := Fin d → ZMod L) n)
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The zero shell consists only of the origin. -/
theorem card_shell_zero :
    Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = 0} = 1 := by
  change ({z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ = 0}).ncard = 1
  simp only [level_eq_zero_iff]
  exact Set.ncard_singleton _

/-- Exact cardinality of every positive-level shell. -/
theorem card_shell_succ [NeZero L] (n : ℕ) :
    Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n + 1} =
      (L ^ d) ^ (n + 1) - (L ^ d) ^ n := by
  have heq : {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ = n + 1} =
      {z | z.support.sup Nat.succ ≤ n + 1} \ {z | z.support.sup Nat.succ ≤ n} := by
    ext z; simp only [Set.mem_ofPred_eq, Set.mem_sdiff]; omega
  change ({z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ = n + 1}).ncard = _
  rw [heq]
  refine (Set.ncard_sdiff
    (s := {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n})
    (t := {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ ≤ n + 1})
    (fun z hz => hz.trans (Nat.le_succ n)) (finite_level_ball n)).trans ?_
  exact congrArg₂ (· - ·) (card_ball (d := d) (L := L) (n + 1)) (card_ball n)

/-- Every shell is finite, including the zero shell. -/
theorem finite_level_shell [NeZero L] (n : ℕ) :
    {z : ℕ →₀ (Fin d → ZMod L) | z.support.sup Nat.succ = n}.Finite :=
  (finite_level_ball n).subset (fun _ h => h.le)

/-- Exact radial summation, with the origin separated from positive shells. -/
theorem tsum_radial_eq [NeZero L] (f : ℕ → ℝ≥0∞) :
    (∑' z : ℕ →₀ (Fin d → ZMod L), f (z.support.sup Nat.succ)) =
      f 0 + ∑' n : ℕ, (((L ^ d) ^ (n + 1) - (L ^ d) ^ n : ℕ) : ℝ≥0∞) * f (n + 1) := by
  have hfib : (∑' z : ℕ →₀ (Fin d → ZMod L), f (z.support.sup Nat.succ)) =
      ∑' n : ℕ, (Nat.card {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n} : ℝ≥0∞) * f n := by
    rw [← ENNReal.tsum_fiberwise (fun z : ℕ →₀ (Fin d → ZMod L) => f (z.support.sup Nat.succ))
      (fun z => z.support.sup Nat.succ)]
    apply tsum_congr
    intro n
    let : Fintype {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n} :=
      (finite_level_shell n).fintype
    change (∑' z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n},
      f (z.1.support.sup Nat.succ)) = _
    calc
      _ = ∑' _z : {z : ℕ →₀ (Fin d → ZMod L) // z.support.sup Nat.succ = n}, f n :=
        tsum_congr (fun z => congrArg f z.2)
      _ = _ := by simp [tsum_fintype, Nat.card_eq_fintype_card]
  rw [hfib, tsum_eq_zero_add' ENNReal.summable, card_shell_zero, Nat.cast_one, one_mul]
  congr 1
  apply tsum_congr
  intro n
  rw [card_shell_succ]

/-- Exact geometric radial sum away from the origin. -/
theorem tsum_geometricRadial_eq [NeZero L] (r : ℝ≥0∞) :
    (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else r ^ (z.support.sup Nat.succ)) =
      (((L ^ d - 1 : ℕ) : ℝ≥0∞) * r) * (1 - (L : ℝ≥0∞) ^ d * r)⁻¹ := by
  have h := tsum_radial_eq (d := d) (L := L) (fun n => if n = 0 then 0 else r ^ n)
  simp only [level_eq_zero_iff, ite_true, Nat.succ_ne_zero, ite_false, zero_add] at h
  rw [h]
  have hcard (n : ℕ) : (L ^ d) ^ (n + 1) - (L ^ d) ^ n = (L ^ d - 1) * (L ^ d) ^ n := by
    rw [pow_succ, Nat.mul_sub_right_distrib, one_mul, mul_comm]
  simp_rw [hcard]
  calc
    _ = ∑' n : ℕ, (((L ^ d - 1 : ℕ) : ℝ≥0∞) * r) * (((L : ℝ≥0∞) ^ d * r) ^ n) := by
      apply tsum_congr
      intro n
      push_cast
      ring
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- A nondegenerate hierarchical geometric kernel is summable exactly below its geometric ratio threshold. -/
theorem tsum_geometricRadial_lt_top_iff (hL : 2 ≤ L) (hd : 1 ≤ d) (r : ℝ≥0)
    (hr : 0 < r) :
    (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else (r : ℝ≥0∞) ^ (z.support.sup Nat.succ)) < ⊤ ↔
      (L : ℝ≥0∞) ^ d * r < 1 := by
  have : NeZero L := ⟨by omega⟩
  rw [tsum_geometricRadial_eq]
  have hM : 1 < L ^ d := Nat.one_lt_pow (by omega) (by omega)
  have hc : (((L ^ d - 1 : ℕ) : ℝ≥0∞) * r) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (Nat.sub_pos_of_lt hM).ne'
    · exact_mod_cast hr.ne'
  have hct : (((L ^ d - 1 : ℕ) : ℝ≥0∞) * r) < ⊤ := by finiteness
  have heq : (((L ^ d - 1 : ℕ) : ℝ≥0∞) * r) * (1 - (L : ℝ≥0∞) ^ d * r)⁻¹ < ⊤ ↔
      (1 - (L : ℝ≥0∞) ^ d * r)⁻¹ < ⊤ := by
    rw [ENNReal.mul_lt_top_iff]
    constructor
    · rintro (h | h | h)
      · exact h.2
      · exact (hc h).elim
      · simp [h]
    · exact fun h => Or.inl ⟨hct, h⟩
  rw [heq, ENNReal.inv_lt_top, tsub_pos_iff_lt]

/-- The full hierarchical power-law summability criterion, with no extra lower bound on alpha. -/
theorem tsum_powerLaw_lt_top_iff (hL : 2 ≤ L) (hd : 1 ≤ d) (α : ℝ) :
    (∑' z : ℕ →₀ (Fin d → ZMod L), if z = 0 then 0 else
      ENNReal.ofReal ((L : ℝ) ^ (-((d : ℝ) + α) * ((z.support.sup Nat.succ : ℕ) : ℝ)))) < ⊤ ↔
      0 < α := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hLone : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  let r : ℝ≥0 := ⟨(L : ℝ) ^ (-((d : ℝ) + α)), (Real.rpow_pos_of_pos hLpos _).le⟩
  have hr : 0 < r := Real.rpow_pos_of_pos hLpos _
  have hpow (n : ℕ) : ENNReal.ofReal ((L : ℝ) ^ (-((d : ℝ) + α) * (n : ℝ))) =
      (r : ℝ≥0∞) ^ n := by
    rw [Real.rpow_mul_natCast hLpos.le, ENNReal.ofReal_pow (Real.rpow_pos_of_pos hLpos _).le]
    congr 1
    have hrval : (r : ℝ) = (L : ℝ) ^ (-((d : ℝ) + α)) := rfl
    rw [← hrval]
    exact ENNReal.ofReal_coe_nnreal
  simp_rw [hpow]
  rw [tsum_geometricRadial_lt_top_iff hL hd r hr]
  have hratio : (L : ℝ≥0∞) ^ d * r = ENNReal.ofReal ((L : ℝ) ^ (-α)) := by
    have hreal : (L : ℝ) ^ d * (r : ℝ) = (L : ℝ) ^ (-α) := by
      change (L : ℝ) ^ d * (L : ℝ) ^ (-((d : ℝ) + α)) = _
      rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
      congr 1
      ring
    have h := congrArg ENNReal.ofReal hreal
    simpa only [ENNReal.ofReal_mul (pow_nonneg hLpos.le d), ENNReal.ofReal_pow hLpos.le,
      ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal] using h
  rw [hratio, ENNReal.ofReal_lt_one, Real.rpow_lt_one_iff_of_pos hLpos]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> linarith
  · intro h; exact Or.inl ⟨hLone, by linarith⟩

-- The nondegenerate base example: four binary one-dimensional coefficients below level four.
example : Nat.card {z : ℕ →₀ (Fin 1 → ZMod 2) // z.support.sup Nat.succ ≤ 4} = 16 := by
  rw [card_ball]
  norm_num
example : Nat.card {z : ℕ →₀ (Fin 1 → ZMod 2) // z.support.sup Nat.succ = 4} = 8 := by
  simpa using (card_shell_succ (d := 1) (L := 2) 3)
example : (∑' z : ℕ →₀ (Fin 1 → ZMod 2), if z = 0 then 0 else
    ENNReal.ofReal ((2 : ℝ) ^ (-((1 : ℝ) + 1) * ((z.support.sup Nat.succ : ℕ) : ℝ)))) < ⊤ :=
  by simpa only [Nat.cast_ofNat, Nat.cast_one] using
    (tsum_powerLaw_lt_top_iff (by decide : 2 ≤ 2) (by decide : 1 ≤ 1) 1).mpr (by norm_num)

-- The excluded degeneracies have one point in every ball, so their summability criterion differs.
example (n : ℕ) : Nat.card {z : ℕ →₀ (Fin 1 → ZMod 1) // z.support.sup Nat.succ ≤ n} = 1 := by
  rw [card_ball]
  simp
example [NeZero L] (n : ℕ) :
    Nat.card {z : ℕ →₀ (Fin 0 → ZMod L) // z.support.sup Nat.succ ≤ n} = 1 := by
  rw [card_ball]
  simp

end PercLib.Models
