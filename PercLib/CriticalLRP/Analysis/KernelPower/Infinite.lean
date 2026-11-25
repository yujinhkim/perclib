/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m1/Infinite.lean ; imports migrated only.
-/

module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
From finite submatrices to the infinite lattice: the truncated powers increase to the full
matrix power, and the Cauchy--Schwarz entry bound passes to the limit.
-/
public import PercLib.CriticalLRP.Analysis.KernelPower.Finite

/-!
# Infinite matrix powers: monotone convergence of the truncations

* `KpowS_mono`, `KpowS_succ`: the truncated powers are monotone in the truncation set and obey
  the same recursion as `Kpow`.
* `Kpow_eq_iSup_KpowS`: **monotone convergence.**  For a nonnegative kernel `K`, the infinite
  matrix power is the supremum of its finite submatrix truncations.
* `Kpow_le_diag`: **diagonal maximality.**  If the diagonal of `Kpow n` is constant, then
  `Kpow n x y ≤ Kpow n x x` for every `y`.  This is the "`T^ℓ` is maximized on the diagonal"
  step of the proof of Lemma I.4.18.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.KernelPower

variable {V : Type*}

/-- The truncated power, as an `ℝ≥0∞`-valued quantity, is monotone in the truncation set. -/
theorem KpowS_mono {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b) {S S' : Finset V} (h : S ⊆ S')
    (n : ℕ) (x y : V) : KpowS K S n x y ≤ KpowS K S' n x y :=
  ENNReal.ofReal_le_ofReal (KpowF_mono hK h n x y)

/-- The recursion for the truncated power at the `ℝ≥0∞` level. -/
theorem KpowS_succ {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b) (S : Finset V) (n : ℕ) (x y : V) :
    KpowS K S (n + 1) x y =
      ∑ u ∈ S, KpowS K S n x u * ENNReal.ofReal (K u y) := by
  rw [KpowS_def, KpowF_succ, ENNReal.ofReal_sum_of_nonneg
    (fun u _ => mul_nonneg (KpowF_nonneg hK S n x u) (hK u y))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [KpowS_def, ENNReal.ofReal_mul (KpowF_nonneg hK S n x u)]

/-- **Monotone convergence of the truncations.**  The infinite `n`-fold matrix power of a
nonnegative kernel is the supremum of its restrictions to finite vertex sets. -/
theorem Kpow_eq_iSup_KpowS {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b) (n : ℕ) (x y : V) :
    Kpow (fun a b => ENNReal.ofReal (K a b)) n x y = ⨆ S : Finset V, KpowS K S n x y := by
  induction n generalizing x y with
  | zero =>
    simp only [Kpow_zero, KpowS_def, KpowF_zero]
    rw [ciSup_const, ofReal_delta]
  | succ n ih =>
    rw [Kpow_succ,
      show (⨆ S : Finset V, KpowS K S (n + 1) x y)
          = ⨆ S : Finset V, ∑ u ∈ S, KpowS K S n x u * ENNReal.ofReal (K u y) from
        iSup_congr fun S => KpowS_succ hK S n x y]
    have hstep : ∀ u : V,
        Kpow (fun a b => ENNReal.ofReal (K a b)) n x u * ENNReal.ofReal (K u y)
          = ⨆ S : Finset V, KpowS K S n x u * ENNReal.ofReal (K u y) := by
      intro u
      rw [ih x u]
      exact ENNReal.iSup_mul (fun S => KpowS K S n x u) (ENNReal.ofReal (K u y))
    simp only [hstep, ENNReal.tsum_eq_iSup_sum]
    have hmono : ∀ u : V, Monotone
        (fun S : Finset V => KpowS K S n x u * ENNReal.ofReal (K u y)) := by
      intro u S S' hSS'
      exact mul_le_mul_of_nonneg_right (KpowS_mono hK hSS' n x u) (by simp)
    have hcomm : ∀ s : Finset V,
        (∑ u ∈ s, ⨆ S : Finset V, KpowS K S n x u * ENNReal.ofReal (K u y))
          = ⨆ S : Finset V, ∑ u ∈ s, KpowS K S n x u * ENNReal.ofReal (K u y) := by
      intro s
      refine ENNReal.finsetSum_iSup (s := s)
        (f := fun u S => KpowS K S n x u * ENNReal.ofReal (K u y)) ?_
      intro i j
      exact ⟨i ∪ j, fun u =>
        ⟨hmono u Finset.subset_union_left, hmono u Finset.subset_union_right⟩⟩
    simp only [hcomm]
    refine le_antisymm ?_ (iSup_le fun S => ?_)
    · refine iSup_le fun s => iSup_le fun S => ?_
      have hsub1 : s ⊆ s ∪ S := Finset.subset_union_left
      have hsub2 : S ⊆ s ∪ S := Finset.subset_union_right
      have step1 : ∑ u ∈ s, KpowS K S n x u * ENNReal.ofReal (K u y)
          ≤ ∑ u ∈ s, KpowS K (s ∪ S) n x u * ENNReal.ofReal (K u y) :=
        Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_right (KpowS_mono hK hsub2 n x u) (by simp)
      have step2 : ∑ u ∈ s, KpowS K (s ∪ S) n x u * ENNReal.ofReal (K u y)
          ≤ ∑ u ∈ s ∪ S, KpowS K (s ∪ S) n x u * ENNReal.ofReal (K u y) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun u _ _ => by simp
      exact (step1.trans step2).trans (le_iSup
        (fun S' => ∑ u ∈ S', KpowS K S' n x u * ENNReal.ofReal (K u y)) (s ∪ S))
    · -- the `S`-truncated sum is the `ofReal` of the `(n+1)`-fold truncated power
      exact (le_iSup (fun S' => ∑ u ∈ S, KpowS K S' n x u * ENNReal.ofReal (K u y)) S).trans
        (le_iSup (fun s => ⨆ S', ∑ u ∈ s, KpowS K S' n x u * ENNReal.ofReal (K u y)) S)

/-- Each truncated power is bounded by the full matrix power. -/
theorem KpowS_le_Kpow {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b) (S : Finset V) (n : ℕ)
    (x y : V) : KpowS K S n x y ≤ Kpow (fun a b => ENNReal.ofReal (K a b)) n x y := by
  rw [Kpow_eq_iSup_KpowS hK n x y]
  exact le_iSup (fun S => KpowS K S n x y) S

/-- **Diagonal maximality for a matrix power of a positive semidefinite kernel.**  If the
diagonal of the `n`-th matrix power is constant (as it is under translation invariance), then
that diagonal dominates every entry of the `n`-th power.  No finiteness hypothesis is needed:
an infinite diagonal makes the statement trivial, and the finite case is `KpowF_sq_le` plus
monotone convergence. -/
theorem Kpow_le_diag {K : V → V → ℝ} (hK : ∀ a b, 0 ≤ K a b)
    (hPSD : ∀ S : Finset V, (Matrix.of fun i j : S => K (i : V) (j : V)).PosSemidef)
    (n : ℕ) (x : V)
    (hdiag : ∀ y : V,
      Kpow (fun a b => ENNReal.ofReal (K a b)) n y y = Kpow (fun a b => ENNReal.ofReal (K a b)) n x x) :
    ∀ y : V, Kpow (fun a b => ENNReal.ofReal (K a b)) n x y ≤
      Kpow (fun a b => ENNReal.ofReal (K a b)) n x x := by
  classical
  intro y
  by_cases htop : Kpow (fun a b => ENNReal.ofReal (K a b)) n x x = ⊤
  · rw [htop]; exact le_top
  · set d : ℝ := (Kpow (fun a b => ENNReal.ofReal (K a b)) n x x).toReal with hd
    have hdnn : 0 ≤ d := ENNReal.toReal_nonneg
    have hofd : ENNReal.ofReal d = Kpow (fun a b => ENNReal.ofReal (K a b)) n x x :=
      ENNReal.ofReal_toReal htop
    -- every diagonal entry of every truncation is at most `d`
    have hdiagT : ∀ (T : Finset V) (z : V), KpowF K T n z z ≤ d := by
      intro T z
      have h1 : KpowS K T n z z ≤ Kpow (fun a b => ENNReal.ofReal (K a b)) n x x := by
        rw [← hdiag z]
        exact KpowS_le_Kpow hK T n z z
      rw [KpowS_def, ← hofd] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hdnn).mp h1
    -- consequently every truncation of the `(x,y)` entry is at most `d`
    have key : ∀ S : Finset V, KpowF K S n x y ≤ d := by
      intro S
      have hSsub : S ⊆ insert x (insert y S) := fun z hz =>
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
      have hxT : x ∈ insert x (insert y S) := Finset.mem_insert_self _ _
      have hyT : y ∈ insert x (insert y S) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hsq := KpowF_sq_le K hPSD (insert x (insert y S)) n x y hxT hyT
      have hle : KpowF K S n x y ≤ KpowF K (insert x (insert y S)) n x y :=
        KpowF_mono hK hSsub n x y
      have hxy : 0 ≤ KpowF K S n x y := KpowF_nonneg hK S n x y
      have hxx : KpowF K (insert x (insert y S)) n x x ≤ d :=
        hdiagT (insert x (insert y S)) x
      have hyy : KpowF K (insert x (insert y S)) n y y ≤ d :=
        hdiagT (insert x (insert y S)) y
      have hcnn1 : 0 ≤ KpowF K (insert x (insert y S)) n x x :=
        KpowF_nonneg hK _ n x x
      have hcnn2 : 0 ≤ KpowF K (insert x (insert y S)) n y y :=
        KpowF_nonneg hK _ n y y
      have hmul : KpowF K (insert x (insert y S)) n x x *
          KpowF K (insert x (insert y S)) n y y ≤ d ^ 2 := by
        rw [sq]
        exact mul_le_mul hxx hyy hcnn2 hdnn
      have hb2 : KpowF K (insert x (insert y S)) n x y ^ 2 ≤ d ^ 2 := hsq.trans hmul
      have ha2 : KpowF K S n x y ^ 2 ≤ d ^ 2 := (pow_le_pow_left₀ hxy hle 2).trans hb2
      nlinarith [ha2, hxy, hdnn]
    rw [Kpow_eq_iSup_KpowS hK n x y]
    refine iSup_le fun S => ?_
    rw [KpowS_def, ← hofd]
    exact ENNReal.ofReal_le_ofReal (key S)

end PercLib.CriticalLRP.KernelPower
