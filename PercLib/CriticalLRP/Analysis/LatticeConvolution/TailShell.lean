/-
Weighted tail-shell estimate (A3) for the I.4.3 convolution split.
Accepted from swarm `smwtvrwnn`, member `m5`, direction D7A.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.TailShell.Defs
public import PercLib.CriticalLRP.LatticeGeometry

/-!
# Weighted tail-shell estimate (the `A3` far region of Lemma I.4.3)

Source: arXiv:2508.18807v1, Lemma I.4.3 and the convolution estimates
(I.4.11)/(I.4.12) obtained from the `A1`/`A2`/`A3` region split.

For `d ≥ 1`, `γ > 0`, `c ≥ 0`, a real threshold `S ≥ 0` and any finite set
`F ⊆ {y : ℤ^d | S < ‖y‖_∞}` of lattice points beyond `S`, the weighted tail

`∑_{y ∈ F} (1 + ‖y‖_∞)^{-(d+γ)} (log (2 + ‖y‖_∞))^{-c}`

is bounded by `tailShellConst d γ * (1 + S)^{-γ} (log (2 + S))^{-c}`, with the
explicit, `S`-independent constant `tailShellConst d γ = 2 d 3^{d-1} 2^{1+2γ}/γ`.
The `tsum` form over the whole far region `{y | S < ‖y‖_∞}` is derived from it.

The proof is *not* an integral test: it is a layer decomposition of the lattice
balls (`FiniteVolume.sum_box_eq`), the proved shell-count/profile-gap inequality
`FiniteVolume.layer_bound` for the `n^{d-1}` layer sizes, and a telescoping
comparison for the remaining power tail using the mean-value gap
`CriticalLRPConv.rpow_sub_ge_of_neg`. The logarithm only enters through the
monotonicity of `LamR`, so the log power `c` is preserved exactly and never
replaced by a power series decay.
-/

set_option autoImplicit false

@[expose] public section

open Finset

namespace CriticalLRPConv

open PercLib.CriticalLRP.FiniteVolume (box box_mono card_box_sdiff linfNorm layer_bound layer_le
  mem_box_iff sum_box_eq)

/-! ## §1 The explicit constant -/

lemma tailShellConst_pos {d : ℕ} (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    0 < tailShellConst d γ := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h3 : (0 : ℝ) < 3 ^ (d - 1) := pow_pos (by norm_num) _
  have h2 : (0 : ℝ) < 2 ^ (1 + 2 * γ) := Real.rpow_pos_of_pos (by norm_num) _
  unfold tailShellConst
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hd0) h3) h2) hγ

/-! ## §2 Telescoping the power profile -/

/-- **One-step comparison.** The profile value `(n+1)^{-1-γ}` is controlled by the drop
`(n+1)^{-γ} - (n+2)^{-γ}` of the pure power profile; the factor `2^{1+γ}`, not `1`, is a
doubling loss which is uniform in `n ≥ 0`. -/
lemma one_add_rpow_gap_le {γ : ℝ} (hγ : 0 < γ) (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) ^ (-1 - γ) ≤
      2 ^ (1 + γ) / γ *
        (((m + 1 : ℕ) : ℝ) ^ (-γ) - (((m + 1) + 1 : ℕ) : ℝ) ^ (-γ)) := by
  set x : ℝ := ((m + 1 : ℕ) : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by
    rw [hx]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1' : (0 : ℝ) < x + 1 := by linarith
  have hcast : (((m + 1) + 1 : ℕ) : ℝ) = x + 1 := by
    rw [hx]
    push_cast
    ring
  have hexp : (-γ - 1 : ℝ) = -1 - γ := by ring
  have hkey : γ * (x + 1) ^ (-1 - γ) ≤ x ^ (-γ) - (x + 1) ^ (-γ) := by
    have h := rpow_sub_ge_of_neg (θ := -γ) (by linarith) hx0 (by linarith : x < x + 1)
    rw [hexp] at h
    simpa using h
  have hstep : x ^ (-1 - γ) ≤ 2 ^ (1 + γ) * (x + 1) ^ (-1 - γ) := by
    have h2x : x + 1 ≤ 2 * x := by linarith
    have hmono : (2 * x) ^ (-1 - γ) ≤ (x + 1) ^ (-1 - γ) :=
      Real.rpow_le_rpow_of_nonpos hx1' h2x (by linarith)
    have hmul : (2 * x) ^ (-1 - γ) = 2 ^ (-1 - γ) * x ^ (-1 - γ) :=
      Real.mul_rpow (by norm_num) hx0.le
    have hone : (2 : ℝ) ^ (1 + γ) * (2 : ℝ) ^ (-1 - γ) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have h0 : (1 + γ) + (-1 - γ) = 0 := by ring
      rw [h0, Real.rpow_zero]
    have h2pos : (0 : ℝ) < 2 ^ (1 + γ) := Real.rpow_pos_of_pos (by norm_num) _
    calc x ^ (-1 - γ) = 1 * x ^ (-1 - γ) := (one_mul _).symm
      _ = (2 ^ (1 + γ) * 2 ^ (-1 - γ)) * x ^ (-1 - γ) := by rw [hone]
      _ = 2 ^ (1 + γ) * (2 ^ (-1 - γ) * x ^ (-1 - γ)) := by ring
      _ = 2 ^ (1 + γ) * (2 * x) ^ (-1 - γ) := by rw [hmul]
      _ ≤ 2 ^ (1 + γ) * (x + 1) ^ (-1 - γ) := mul_le_mul_of_nonneg_left hmono h2pos.le
  have hdiv : (x + 1) ^ (-1 - γ) ≤ (x ^ (-γ) - (x + 1) ^ (-γ)) / γ := by
    rw [le_div_iff₀ hγ]
    linarith
  have hmain : x ^ (-1 - γ) ≤ 2 ^ (1 + γ) / γ * (x ^ (-γ) - (x + 1) ^ (-γ)) := by
    calc x ^ (-1 - γ) ≤ 2 ^ (1 + γ) * (x + 1) ^ (-1 - γ) := hstep
      _ ≤ 2 ^ (1 + γ) * ((x ^ (-γ) - (x + 1) ^ (-γ)) / γ) :=
          mul_le_mul_of_nonneg_left hdiv (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = 2 ^ (1 + γ) / γ * (x ^ (-γ) - (x + 1) ^ (-γ)) := by ring
  rw [hcast]
  exact hmain

/-- **Telescoped power tail.** The tail of `(n+1)^{-1-γ}` over the index range `Ico K N` is
controlled by the single profile value at the left end point, with no dependence on `N`. -/
lemma sum_Ico_rpow_tail_le {γ : ℝ} (hγ : 0 < γ) (K N : ℕ) :
    ∑ m ∈ Finset.Ico K N, ((m + 1 : ℕ) : ℝ) ^ (-1 - γ) ≤
      2 ^ (1 + γ) / γ * (((K + 1 : ℕ)) : ℝ) ^ (-γ) := by
  have hstep : ∀ m ∈ Finset.Ico K N,
      ((m + 1 : ℕ) : ℝ) ^ (-1 - γ) ≤
        2 ^ (1 + γ) / γ *
          (((m + 1 : ℕ) : ℝ) ^ (-γ) - (((m + 1) + 1 : ℕ) : ℝ) ^ (-γ)) :=
    fun m _ => one_add_rpow_gap_le hγ m
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  set f : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (-γ) with hf
  have htel : ∀ K' N' : ℕ, K' ≤ N' →
      ∑ m ∈ Finset.Ico K' N', (f m - f (m + 1)) = f K' - f N' := by
    intro K' N' hKN
    have h1 : ∀ L : ℕ, ∑ m ∈ Finset.range L, (f m - f (m + 1)) = f 0 - f L := by
      intro L
      have h := Finset.sum_range_sub (f := f) L
      have h2 : ∑ m ∈ Finset.range L, (f m - f (m + 1))
          = -∑ m ∈ Finset.range L, (f (m + 1) - f m) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [h2, h]
      ring
    rw [Finset.sum_Ico_eq_sub (fun m => f m - f (m + 1)) hKN, h1 N', h1 K']
    ring
  have hk : (0 : ℝ) < 2 ^ (1 + γ) / γ :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) (1 + γ)) hγ
  rcases le_or_gt K N with hKN | hNK
  · rw [htel K N hKN]
    have hfK : f K = (((K + 1 : ℕ)) : ℝ) ^ (-γ) := rfl
    rw [hfK]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    have h0 : 0 ≤ f N :=
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ)) _
    linarith
  · have hempty : Finset.Ico K N = ∅ := by
      rw [Finset.Ico_eq_empty_iff]
      exact not_lt.mpr (le_of_lt hNK)
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero]
    exact mul_nonneg hk.le
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (((K + 1 : ℕ)) : ℝ)) _)

/-! ## §3 The floor of the threshold -/

/-- The telescoping left end point `⌊S⌋₊ + 1` dominates `S`, so its profile value is at most a
factor `2^γ` larger than `(1 + S)^{-γ}`. -/
lemma floor_succ_rpow_le {γ S : ℝ} (hγ : 0 < γ) (hS : 0 ≤ S) :
    (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ) ≤ 2 ^ γ * (1 + S) ^ (-γ) := by
  have hbase : (0 : ℝ) < ((⌊S⌋₊ + 1 : ℕ) : ℝ) := by positivity
  have hle : 1 + S ≤ 2 * ((⌊S⌋₊ + 1 : ℕ) : ℝ) := by
    have h1 : S < ((⌊S⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one S
    push_cast
    linarith
  have h2γ : (0 : ℝ) < 2 ^ γ := Real.rpow_pos_of_pos (by norm_num) _
  have hstep : ((⌊S⌋₊ + 1 : ℕ) : ℝ) ^ (-γ) * 2 ^ (-γ) ≤ (1 + S) ^ (-γ) := by
    have h2 : (2 * ((⌊S⌋₊ + 1 : ℕ) : ℝ)) ^ (-γ) ≤ (1 + S) ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
    rw [Real.mul_rpow (by norm_num) hbase.le, mul_comm] at h2
    exact h2
  have hone : (2 : ℝ) ^ (-γ) * (2 : ℝ) ^ γ = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h0 : -γ + γ = 0 := by ring
    rw [h0, Real.rpow_zero]
  calc (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ)
        = (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ) * 1 := by ring
    _ = (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ) * (2 ^ (-γ) * 2 ^ γ) := by rw [hone]
    _ = (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ) * 2 ^ (-γ) * 2 ^ γ := by ring
    _ ≤ (1 + S) ^ (-γ) * 2 ^ γ := mul_le_mul_of_nonneg_right hstep h2γ.le
    _ = 2 ^ γ * (1 + S) ^ (-γ) := by ring

/-! ## §4 The layer bound of the weighted weight -/

/-- **The `m`-th layer term.** The number of lattice points in the layer
`B_{(m+1)} \ B_m` times the weight `Wt (d+γ) c (m+1)` is bounded by the power profile
`(m+1)^{-1-γ}` times the *frozen* logarithmic factor at the threshold `S`. -/
lemma layer_term_le {d : ℕ} (hd : 1 ≤ d) {γ c S : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c)
    (hS : 0 ≤ S)
    {m : ℕ} (hmS : S ≤ (((m + 1 : ℕ)) : ℝ)) :
    ((box d (m + 1) \ box d m).card : ℝ) * Wt ((d : ℝ) + γ) c (((m + 1 : ℕ)) : ℝ) ≤
      2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ) * LamR S ^ (-c) := by
  have hdS : (d : ℝ) < (d : ℝ) + γ := by linarith
  have hlb := layer_bound d m (s := (d : ℝ) + γ) hdS
  have hexp : (((d - 1 : ℕ)) : ℝ) - ((d : ℝ) + γ) = -1 - γ := by
    rw [Nat.cast_sub hd]
    ring
  rw [hexp] at hlb
  have hmpos : (0 : ℝ) < 1 + (((m + 1 : ℕ)) : ℝ) := by positivity
  have hlog : LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) ≤ LamR S ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (LamR_pos hS) (LamR_mono hS hmS) (by linarith)
  have hWt : Wt ((d : ℝ) + γ) c (((m + 1 : ℕ)) : ℝ)
      = (1 + (((m + 1 : ℕ)) : ℝ)) ^ (-((d : ℝ) + γ)) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) :=
    rfl
  have hnn : (0 : ℝ) ≤ LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) :=
    Real.rpow_nonneg (LamR_nonneg (by positivity)) _
  calc ((box d (m + 1) \ box d m).card : ℝ) * Wt ((d : ℝ) + γ) c (((m + 1 : ℕ)) : ℝ)
      = (((box d (m + 1) \ box d m).card : ℝ)
            * (1 + (((m + 1 : ℕ)) : ℝ)) ^ (-((d : ℝ) + γ)))
          * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := by
        rw [hWt]
        ring
    _ ≤ (2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ))
          * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := mul_le_mul_of_nonneg_right hlb hnn
    _ ≤ (2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ)) * LamR S ^ (-c) :=
        mul_le_mul_of_nonneg_left hlog (by
          have h2 : (0 : ℝ) < 3 ^ (d - 1) := pow_pos (by norm_num) _
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
          have hp : (0 : ℝ) ≤ (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ) :=
            Real.rpow_nonneg (by positivity) _
          positivity)
    _ = 2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ) * LamR S ^ (-c) := by
        ring

/-! ## §5 The finite weighted tail shell -/

/-- **Weighted tail shell (finite form).** For `d ≥ 1`, `γ > 0`, `c ≥ 0`, `S ≥ 0` and a
finite set `F` of lattice points with `S < ‖y‖_∞`,

`∑_{y ∈ F} (1+‖y‖_∞)^{-(d+γ)} (log (2+‖y‖_∞))^{-c}
  ≤ tailShellConst d γ · (1+S)^{-γ} (log (2+S))^{-c}`.

The constant `tailShellConst d γ` does not depend on `F` or on `S`. -/
theorem sum_Wt_tail_le {d : ℕ} (hd : 1 ≤ d) {γ c S : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c)
    (hS : 0 ≤ S) (F : Finset (Fin d → ℤ))
    (hF : ∀ y ∈ F, S < (linfNorm y : ℝ)) :
    ∑ y ∈ F, Wt ((d : ℝ) + γ) c (linfNorm y : ℝ) ≤ tailShellConst d γ * Wt γ c S := by
  classical
  rcases Finset.eq_empty_or_nonempty F with hem | ⟨y₀, hy₀⟩
  · rw [hem, Finset.sum_empty]
    exact mul_nonneg (tailShellConst_pos hd hγ).le (Wt_nonneg hS)
  have hy₀S : S < (linfNorm y₀ : ℝ) := hF y₀ hy₀
  have hKN : ⌊S⌋₊ ≤ F.sup linfNorm := by
    have h1 : linfNorm y₀ ≤ F.sup linfNorm := Finset.le_sup (f := linfNorm) hy₀
    have h2 : ⌊S⌋₊ ≤ linfNorm y₀ := by
      have h3 := Nat.floor_mono (le_of_lt hy₀S)
      rwa [Nat.floor_natCast] at h3
    omega
  have hsub : F ⊆ box d (F.sup linfNorm) \ box d ⌊S⌋₊ := by
    intro y hy
    rw [Finset.mem_sdiff, mem_box_iff]
    refine ⟨Finset.le_sup (f := linfNorm) hy, ?_⟩
    rw [mem_box_iff]
    intro hKmem
    have hyS : S < (linfNorm y : ℝ) := hF y hy
    have hle : (linfNorm y : ℝ) ≤ ((⌊S⌋₊ : ℕ) : ℝ) := by exact_mod_cast hKmem
    have hKS : ((⌊S⌋₊ : ℕ) : ℝ) ≤ S := Nat.floor_le hS
    linarith
  have hstep1 : ∑ y ∈ F, Wt ((d : ℝ) + γ) c (linfNorm y : ℝ)
      ≤ ∑ y ∈ box d (F.sup linfNorm) \ box d ⌊S⌋₊,
          Wt ((d : ℝ) + γ) c (linfNorm y : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Wt_nonneg (by positivity))
  have hstep2 : ∑ y ∈ box d (F.sup linfNorm) \ box d ⌊S⌋₊,
        Wt ((d : ℝ) + γ) c (linfNorm y : ℝ)
      = ∑ y ∈ box d (F.sup linfNorm), Wt ((d : ℝ) + γ) c (linfNorm y : ℝ)
        - ∑ y ∈ box d ⌊S⌋₊, Wt ((d : ℝ) + γ) c (linfNorm y : ℝ) := by
    have h := Finset.sum_sdiff
      (f := fun y : Fin d → ℤ => Wt ((d : ℝ) + γ) c (linfNorm y : ℝ)) (box_mono hKN)
    linarith
  have hstep3 : ∑ y ∈ box d (F.sup linfNorm), Wt ((d : ℝ) + γ) c (linfNorm y : ℝ)
        - ∑ y ∈ box d ⌊S⌋₊, Wt ((d : ℝ) + γ) c (linfNorm y : ℝ)
      = ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
          ((box d (m + 1) \ box d m).card : ℝ)
            * Wt ((d : ℝ) + γ) c (((m + 1 : ℕ)) : ℝ) := by
    rw [sum_box_eq d (F.sup linfNorm) (fun n : ℕ => Wt ((d : ℝ) + γ) c ((n : ℝ))),
      sum_box_eq d ⌊S⌋₊ (fun n : ℕ => Wt ((d : ℝ) + γ) c ((n : ℝ)))]
    have h := Finset.sum_Ico_eq_sub
      (f := fun m : ℕ => ((box d (m + 1) \ box d m).card : ℝ)
        * Wt ((d : ℝ) + γ) c (((m + 1 : ℕ)) : ℝ)) hKN
    rw [h]
    ring
  have hstep4 : ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
        ((box d (m + 1) \ box d m).card : ℝ) * Wt ((d : ℝ) + γ) c (((m + 1 : ℕ)) : ℝ)
      ≤ ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
          2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ) * LamR S ^ (-c) := by
    refine Finset.sum_le_sum fun m hm => layer_term_le hd hγ hc hS ?_
    have hmK : ⌊S⌋₊ ≤ m := (Finset.mem_Ico.mp hm).1
    have hSlt : S < ((⌊S⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one S
    have hmK' : ((⌊S⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmK
    push_cast
    linarith
  have hstep5 : ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
        2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ) * LamR S ^ (-c)
      = (2 * (d : ℝ) * 3 ^ (d - 1) * LamR S ^ (-c))
        * ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
            (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hnonneg : (0 : ℝ) ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * LamR S ^ (-c) := by
    have h3 : (0 : ℝ) < 3 ^ (d - 1) := pow_pos (by norm_num) _
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hl : (0 : ℝ) < LamR S := LamR_pos hS
    have hlc : (0 : ℝ) ≤ LamR S ^ (-c) := Real.rpow_nonneg hl.le _
    positivity
  have hstep6 : (2 * (d : ℝ) * 3 ^ (d - 1) * LamR S ^ (-c))
        * ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm), (((m + 1 : ℕ)) : ℝ) ^ (-1 - γ)
      ≤ (2 * (d : ℝ) * 3 ^ (d - 1) * LamR S ^ (-c))
        * (2 ^ (1 + γ) / γ * (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ)) :=
    mul_le_mul_of_nonneg_left (sum_Ico_rpow_tail_le hγ ⌊S⌋₊ (F.sup linfNorm)) hnonneg
  have hstep7 : (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ) ≤ 2 ^ γ * (1 + S) ^ (-γ) :=
    floor_succ_rpow_le hγ hS
  have hstep8 : (2 * (d : ℝ) * 3 ^ (d - 1) * LamR S ^ (-c))
        * (2 ^ (1 + γ) / γ * (2 ^ γ * (1 + S) ^ (-γ)))
      = tailShellConst d γ * Wt γ c S := by
    have h2id : (2 : ℝ) ^ (1 + γ) * 2 ^ γ = 2 ^ (1 + 2 * γ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have h0 : (1 + γ) + γ = 1 + 2 * γ := by ring
      rw [h0]
    unfold tailShellConst Wt
    rw [← h2id]
    ring
  have hmul : (2 * (d : ℝ) * 3 ^ (d - 1) * LamR S ^ (-c))
        * (2 ^ (1 + γ) / γ * (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (-γ))
      ≤ (2 * (d : ℝ) * 3 ^ (d - 1) * LamR S ^ (-c))
        * (2 ^ (1 + γ) / γ * (2 ^ γ * (1 + S) ^ (-γ))) := by
    have hk : (0 : ℝ) < 2 ^ (1 + γ) / γ :=
      div_pos (Real.rpow_pos_of_pos (by norm_num) (1 + γ)) hγ
    refine mul_le_mul_of_nonneg_left ?_ hnonneg
    exact mul_le_mul_of_nonneg_left hstep7 hk.le
  refine le_trans hstep1 ?_
  rw [hstep2, hstep3]
  refine le_trans hstep4 (le_trans (le_of_eq hstep5) (le_trans hstep6 (le_trans hmul ?_)))
  exact le_of_eq hstep8

/-! ## §6 The infinite far region -/

/-- **Weighted tail shell (summable form).** The whole far region `{y | S < ‖y‖_∞}` carries
finite weighted mass, controlled by the same explicit constant. This is the literal
`∑_{‖y‖_∞ > S}` form of the `A3` estimate: it includes the summability statement. -/
theorem tsum_Wt_tail_le {d : ℕ} (hd : 1 ≤ d) {γ c S : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c)
    (hS : 0 ≤ S) :
    ∑' y : {y : Fin d → ℤ // S < (linfNorm y : ℝ)},
        Wt ((d : ℝ) + γ) c (linfNorm (y : Fin d → ℤ) : ℝ) ≤
      tailShellConst d γ * Wt γ c S := by
  classical
  have hnn : ∀ y : {y : Fin d → ℤ // S < (linfNorm y : ℝ)},
      0 ≤ Wt ((d : ℝ) + γ) c (linfNorm (y : Fin d → ℤ) : ℝ) :=
    fun y => Wt_nonneg (by positivity)
  have hbound : ∀ u : Finset {y : Fin d → ℤ // S < (linfNorm y : ℝ)},
      ∑ y ∈ u, Wt ((d : ℝ) + γ) c (linfNorm (y : Fin d → ℤ) : ℝ)
        ≤ tailShellConst d γ * Wt γ c S := by
    intro u
    have hinj : Set.InjOn (fun y : {y : Fin d → ℤ // S < (linfNorm y : ℝ)} =>
        (y : Fin d → ℤ)) ↑u :=
      fun a _ b _ hab => Subtype.ext hab
    have himg : ∑ y ∈ u, Wt ((d : ℝ) + γ) c (linfNorm (y : Fin d → ℤ) : ℝ)
        = ∑ z ∈ u.image (fun y : {y : Fin d → ℤ // S < (linfNorm y : ℝ)} =>
            (y : Fin d → ℤ)), Wt ((d : ℝ) + γ) c (linfNorm z : ℝ) := by
      rw [Finset.sum_image
        (f := fun z : Fin d → ℤ => Wt ((d : ℝ) + γ) c (linfNorm z : ℝ)) hinj]
    rw [himg]
    exact sum_Wt_tail_le hd hγ hc hS _
      (fun z hz => by
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
        exact y.2)
  exact Summable.tsum_le_of_sum_le (summable_of_sum_le hnn hbound) hbound


/-! ## §7 The pure-logarithmic case `γ = 0`, `c > 1`

With `γ = 0` the power weight is exactly critical and the tail of
`(1 + ‖y‖)^{-d} (log (2 + ‖y‖))^{-c}` is no longer `(log (2+S))^{-c}`: summing `n^{-1}`
against `(log n)^{-c}` costs one logarithm, so the correct far-region bound keeps the log
power `c - 1`. The log factor is *not* frozen here; the decay comes from the telescoped
profile `Λ^{1-c}` via `LamR_gap_lower`. -/

/-- **One-step logarithmic gap.** For `c > 1` the drop of `Λ^{1-c}` controls
`(m+1)^{-1} Λ(m+1)^{-c}`. The factor `8 · 2^c` is the doubling loss of the logarithm
(`LamR_succ_le_two`) times the universal profile gap `LamR_gap_lower`. -/
lemma one_add_log_gap_le {c : ℝ} (hc : 1 < c) (m : ℕ) :
    (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) ≤
      8 * 2 ^ c / (c - 1) *
        (LamR (((m + 1 : ℕ)) : ℝ) ^ (1 - c) -
          LamR ((((m + 1) + 1 : ℕ))) ^ (1 - c)) := by
  have hm1 : (0 : ℝ) < (((m + 1 : ℕ)) : ℝ) := by positivity
  have hcast : ((((m + 1) + 1 : ℕ)) : ℝ) = (((m + 1 : ℕ)) : ℝ) + 1 := by
    push_cast
    ring
  have hX : (0 : ℝ) < ((((m + 1) + 1 : ℕ)) : ℝ) := by positivity
  have hx0 : 0 < LamR (((m + 1 : ℕ)) : ℝ) := LamR_pos hm1.le
  have hxy : LamR ((((m + 1 : ℕ)) : ℝ)) < LamR ((((m + 1) + 1 : ℕ))) := by
    refine LamR_lt hm1.le ?_
    rw [hcast]
    linarith
  have hB : (0 : ℝ) ≤ LamR ((((m + 1) + 1 : ℕ))) ^ (-c) :=
    Real.rpow_nonneg (LamR_pos (by positivity : (0 : ℝ) ≤ ((((m + 1) + 1 : ℕ)) : ℝ))).le _
  have hP : (0 : ℝ) ≤ 1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)) := by positivity
  have hcpos : (0 : ℝ) < c - 1 := by linarith
  -- the universal profile gap
  have hgap : 1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)) ≤
      LamR ((((m + 1) + 1 : ℕ))) - LamR (((m + 1 : ℕ)) : ℝ) := by
    rw [hcast]
    exact LamR_gap_lower (m + 1)
  -- the log profile at most doubles
  have hy2x : LamR ((((m + 1) + 1 : ℕ))) ≤ 2 * LamR (((m + 1 : ℕ)) : ℝ) := by
    rw [hcast]
    exact LamR_succ_le_two (m + 1)
  -- mean value: `(c-1) Λ(n+2)^{-c} (Λ(n+2) - Λ(n+1)) ≤ Λ(n+1)^{1-c} - Λ(n+2)^{1-c}`
  have hkey : (c - 1) * LamR ((((m + 1) + 1 : ℕ))) ^ (-c) *
      (LamR ((((m + 1) + 1 : ℕ))) - LamR (((m + 1 : ℕ)) : ℝ)) ≤
      LamR (((m + 1 : ℕ)) : ℝ) ^ (1 - c) - LamR ((((m + 1) + 1 : ℕ))) ^ (1 - c) := by
    have h := rpow_sub_ge_of_neg (θ := 1 - c) (by linarith : (1 : ℝ) - c < 0) hx0 hxy
    rw [show (1 : ℝ) - c - 1 = -c from by ring] at h
    simpa using h
  -- `x^{-1} ≤ 8 / (4 X) = 2 / X`
  have hstep1 : (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) ≤
      8 * (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ))) := by
    have h8 : 8 * (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ))) =
        2 / ((((m + 1) + 1 : ℕ)) : ℝ) := by
      field_simp
      norm_num
    have hm1' : (1 : ℝ) ≤ (((m + 1 : ℕ)) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    rw [h8, Real.rpow_neg_one, ← one_div, div_le_div_iff₀ hm1 hX]
    rw [hcast]
    linarith
  -- `Λ(n+1)^{-c} ≤ 2^c Λ(n+2)^{-c}`
  have hstep2 : LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) ≤
      2 ^ c * LamR ((((m + 1) + 1 : ℕ))) ^ (-c) := by
    have hy0 : 0 < LamR ((((m + 1) + 1 : ℕ))) := lt_trans hx0 hxy
    have h2x : (2 * LamR (((m + 1 : ℕ)) : ℝ)) ^ (-c) ≤
        LamR ((((m + 1) + 1 : ℕ))) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos hy0 hy2x (by linarith : -c ≤ 0)
    rw [Real.mul_rpow (by norm_num) hx0.le] at h2x
    calc LamR (((m + 1 : ℕ)) : ℝ) ^ (-c)
        = 1 * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := (one_mul _).symm
      _ = (2 ^ c * 2 ^ (-c)) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := by
          rw [show (2 : ℝ) ^ c * 2 ^ (-c) = 1 from by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            have h0 : c + -c = 0 := by ring
            rw [h0, Real.rpow_zero]]
      _ = 2 ^ c * (2 ^ (-c) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c)) := by ring
      _ ≤ 2 ^ c * LamR ((((m + 1) + 1 : ℕ))) ^ (-c) :=
          mul_le_mul_of_nonneg_left h2x (Real.rpow_pos_of_pos (by norm_num) _).le
  have hstep3 : (c - 1) *
        (LamR ((((m + 1) + 1 : ℕ))) ^ (-c) * (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)))) ≤
      LamR (((m + 1 : ℕ)) : ℝ) ^ (1 - c) - LamR ((((m + 1) + 1 : ℕ))) ^ (1 - c) := by
    have h1 : (c - 1) *
          (LamR ((((m + 1) + 1 : ℕ))) ^ (-c) * (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)))) ≤
        (c - 1) * (LamR ((((m + 1) + 1 : ℕ))) ^ (-c) *
          (LamR ((((m + 1) + 1 : ℕ))) - LamR (((m + 1 : ℕ)) : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ hcpos.le
      exact mul_le_mul_of_nonneg_left hgap hB
    have h2 : (c - 1) * (LamR ((((m + 1) + 1 : ℕ))) ^ (-c) *
          (LamR ((((m + 1) + 1 : ℕ))) - LamR (((m + 1 : ℕ)) : ℝ))) ≤
        LamR (((m + 1 : ℕ)) : ℝ) ^ (1 - c) - LamR ((((m + 1) + 1 : ℕ))) ^ (1 - c) := by
      refine le_trans (le_of_eq ?_) hkey
      ring
    exact le_trans h1 h2
  have hA : (0 : ℝ) ≤ LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := Real.rpow_nonneg hx0.le _
  have h8c : (0 : ℝ) ≤ 8 * 2 ^ c := by positivity
  have hmul1 : (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) ≤
      (8 * (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)))) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) :=
    mul_le_mul_of_nonneg_right hstep1 hA
  have hmul2 : LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) *
        (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ))) ≤
      2 ^ c * (LamR ((((m + 1) + 1 : ℕ))) ^ (-c) *
        (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)))) :=
    le_trans (mul_le_mul_of_nonneg_right hstep2 hP) (le_of_eq (by ring))
  calc (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c)
      ≤ (8 * (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)))) *
          LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := hmul1
    _ = 8 * (LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) *
          (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)))) := by ring
    _ ≤ 8 * (2 ^ c * (LamR ((((m + 1) + 1 : ℕ))) ^ (-c) *
          (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ))))) :=
        mul_le_mul_of_nonneg_left hmul2 (by norm_num)
    _ = (8 * 2 ^ c) * (LamR ((((m + 1) + 1 : ℕ))) ^ (-c) *
          (1 / (4 * ((((m + 1) + 1 : ℕ)) : ℝ)))) := by ring
    _ ≤ (8 * 2 ^ c) * ((LamR (((m + 1 : ℕ)) : ℝ) ^ (1 - c) -
          LamR ((((m + 1) + 1 : ℕ))) ^ (1 - c)) / (c - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ h8c
        rw [le_div_iff₀ hcpos]
        exact le_trans (le_of_eq (by ring)) hstep3
    _ = 8 * 2 ^ c / (c - 1) * (LamR (((m + 1 : ℕ)) : ℝ) ^ (1 - c) -
          LamR ((((m + 1) + 1 : ℕ))) ^ (1 - c)) := by ring

/-- **Telescoped logarithmic tail.** -/
lemma sum_Ico_log_tail_le {c : ℝ} (hc : 1 < c) (K N : ℕ) :
    ∑ m ∈ Finset.Ico K N,
        (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) ≤
      8 * 2 ^ c / (c - 1) * LamR (((K + 1 : ℕ)) : ℝ) ^ (1 - c) := by
  have hstep : ∀ m ∈ Finset.Ico K N,
      (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) ≤
        8 * 2 ^ c / (c - 1) *
          (LamR (((m + 1 : ℕ)) : ℝ) ^ (1 - c) -
            LamR ((((m + 1) + 1 : ℕ))) ^ (1 - c)) :=
    fun m _ => one_add_log_gap_le hc m
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  set g : ℕ → ℝ := fun n => LamR (((n + 1 : ℕ)) : ℝ) ^ (1 - c) with hg
  have htel : ∀ K' N' : ℕ, K' ≤ N' →
      ∑ m ∈ Finset.Ico K' N', (g m - g (m + 1)) = g K' - g N' := by
    intro K' N' hKN
    have h1 : ∀ L : ℕ, ∑ m ∈ Finset.range L, (g m - g (m + 1)) = g 0 - g L := by
      intro L
      have h := Finset.sum_range_sub (f := g) L
      have h2 : ∑ m ∈ Finset.range L, (g m - g (m + 1))
          = -∑ m ∈ Finset.range L, (g (m + 1) - g m) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [h2, h]
      ring
    rw [Finset.sum_Ico_eq_sub (fun m => g m - g (m + 1)) hKN, h1 N', h1 K']
    ring
  have hk : (0 : ℝ) ≤ 8 * 2 ^ c / (c - 1) := by
    have : (0 : ℝ) < c - 1 := by linarith
    positivity
  rcases le_or_gt K N with hKN | hNK
  · rw [htel K N hKN]
    have hgK : g K = LamR (((K + 1 : ℕ)) : ℝ) ^ (1 - c) := rfl
    rw [hgK]
    refine mul_le_mul_of_nonneg_left ?_ hk
    have h0 : 0 ≤ g N := Real.rpow_nonneg (LamR_nonneg (by positivity)) _
    linarith
  · have hempty : Finset.Ico K N = ∅ := by
      rw [Finset.Ico_eq_empty_iff]
      exact not_lt.mpr (le_of_lt hNK)
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero]
    exact mul_nonneg hk (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)

/-- The logarithm profile at `⌊S⌋₊ + 1` is at most `Λ S`, so the telescoped tail is
controlled by the threshold. -/
lemma floor_succ_log_rpow_le {c S : ℝ} (hc : 1 ≤ c) (hS : 0 ≤ S) :
    LamR (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (1 - c) ≤ LamR S ^ (1 - c) := by
  have h1 : S ≤ (((⌊S⌋₊ + 1 : ℕ)) : ℝ) := by
    have h2 : S < ((⌊S⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one S
    push_cast
    linarith
  have hx0 : (0 : ℝ) < LamR S := LamR_pos hS
  exact Real.rpow_le_rpow_of_nonpos hx0 (LamR_mono hS h1) (by linarith)

/-- **The `m`-th layer term in the pure-logarithmic case.** -/
lemma layer_term_le_pureLog {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (m : ℕ) :
    ((box d (m + 1) \ box d m).card : ℝ) * Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ) ≤
      2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) *
        LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := by
  have hm1 : (0 : ℝ) < (((m + 1 : ℕ)) : ℝ) := by positivity
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcard : ((box d (m + 1) \ box d m).card : ℝ)
      ≤ 2 * (d : ℝ) * ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1) := by
    rw [card_box_sdiff]
    exact layer_le d m
  have h3m : ((2 * m + 3 : ℕ) : ℝ) ≤ 3 * (((m + 1 : ℕ)) : ℝ) := by
    have h : 2 * m + 3 ≤ 3 * (m + 1) := by omega
    exact_mod_cast h
  have hpow : ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1)
      ≤ 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (d - 1) := by
    calc ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1)
        ≤ (3 * (((m + 1 : ℕ)) : ℝ)) ^ (d - 1) := pow_le_pow_left₀ (by positivity) h3m _
      _ = 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (d - 1) := by rw [mul_pow]
  have hwt : (1 + (((m + 1 : ℕ)) : ℝ)) ^ (-(d : ℝ))
      ≤ (((m + 1 : ℕ)) : ℝ) ^ (-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm1 (by linarith) (by linarith)
  have hexp : (((d - 1 : ℕ)) : ℝ) + (-(d : ℝ)) = -1 := by
    rw [Nat.cast_sub hd]
    ring
  have hmain : ((box d (m + 1) \ box d m).card : ℝ) *
        (1 + (((m + 1 : ℕ)) : ℝ)) ^ (-(d : ℝ)) ≤
      2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) := by
    have hn1 : (0 : ℝ) ≤ (((m + 1 : ℕ)) : ℝ) ^ (-(d : ℝ)) :=
      Real.rpow_nonneg hm1.le _
    have hpos1 : (0 : ℝ) ≤ (1 + (((m + 1 : ℕ)) : ℝ)) ^ (-(d : ℝ)) :=
      Real.rpow_nonneg (by linarith) _
    refine le_trans (mul_le_mul hcard hwt hpos1 (by positivity)) ?_
    have hstep : (2 * (d : ℝ) * ((2 * m + 3 : ℕ) : ℝ) ^ (d - 1)) *
          (((m + 1 : ℕ)) : ℝ) ^ (-(d : ℝ))
        ≤ (2 * (d : ℝ) * (3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (d - 1))) *
          (((m + 1 : ℕ)) : ℝ) ^ (-(d : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ hn1
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    have hx1 : (((m + 1 : ℕ)) : ℝ) ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-(d : ℝ)) =
        (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast (((m + 1 : ℕ)) : ℝ) (d - 1)]
      rw [← Real.rpow_add hm1, hexp]
    calc (2 * (d : ℝ) * (3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (d - 1))) *
          (((m + 1 : ℕ)) : ℝ) ^ (-(d : ℝ))
        = 2 * (d : ℝ) * 3 ^ (d - 1) *
            ((((m + 1 : ℕ)) : ℝ) ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-(d : ℝ))) := by ring
      _ = 2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) := by rw [hx1]
  have hA : (0 : ℝ) ≤ LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) :=
    Real.rpow_nonneg (LamR_nonneg hm1.le) _
  calc ((box d (m + 1) \ box d m).card : ℝ) * Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ)
      = (((box d (m + 1) \ box d m).card : ℝ) *
            (1 + (((m + 1 : ℕ)) : ℝ)) ^ (-(d : ℝ))) *
          LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := by
        unfold Wt
        ring
    _ ≤ (2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ)) *
          LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := mul_le_mul_of_nonneg_right hmain hA
    _ = 2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) *
          LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := by ring

/-- **Weighted tail shell, pure-logarithmic case.** For `d ≥ 1`, `c > 1`, `S ≥ 0` and a
finite set `F` of lattice points with `S < ‖y‖_∞`,

`∑_{y ∈ F} (1+‖y‖_∞)^{-d} (log (2+‖y‖_∞))^{-c}
  ≤ tailShellConstLog d c · (log (2+S))^{-(c-1)}`.

The exponent drop from `c` to `c-1` is not a loss: summing `n^{-1} (log n)^{-c}` over the
lattice costs exactly one logarithm, so `(log (2+S))^{-c}` is *not* attainable here. -/
theorem sum_Wt_tail_le_pureLog {d : ℕ} (hd : 1 ≤ d) {c S : ℝ} (hc : 1 < c) (hS : 0 ≤ S)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, S < (linfNorm y : ℝ)) :
    ∑ y ∈ F, Wt (d : ℝ) c (linfNorm y : ℝ) ≤
      tailShellConstLog d c * Wt (0 : ℝ) (c - 1) S := by
  classical
  have hWt0 : Wt (0 : ℝ) (c - 1) S = LamR S ^ (1 - c) := by
    unfold Wt
    rw [neg_zero, Real.rpow_zero, one_mul]
    rw [show -(c - 1) = 1 - c from by ring]
  rw [hWt0]
  unfold tailShellConstLog
  rcases Finset.eq_empty_or_nonempty F with hem | ⟨y₀, hy₀⟩
  · rw [hem, Finset.sum_empty]
    refine mul_nonneg (by positivity) (Real.rpow_nonneg (LamR_pos hS).le _)
  have hy₀S : S < (linfNorm y₀ : ℝ) := hF y₀ hy₀
  have hKN : ⌊S⌋₊ ≤ F.sup linfNorm := by
    have h1 : linfNorm y₀ ≤ F.sup linfNorm := Finset.le_sup (f := linfNorm) hy₀
    have h2 : ⌊S⌋₊ ≤ linfNorm y₀ := by
      have h3 := Nat.floor_mono (le_of_lt hy₀S)
      rwa [Nat.floor_natCast] at h3
    omega
  have hsub : F ⊆ box d (F.sup linfNorm) \ box d ⌊S⌋₊ := by
    intro y hy
    rw [Finset.mem_sdiff, mem_box_iff]
    refine ⟨Finset.le_sup (f := linfNorm) hy, ?_⟩
    rw [mem_box_iff]
    intro hKmem
    have hyS : S < (linfNorm y : ℝ) := hF y hy
    have hle : (linfNorm y : ℝ) ≤ ((⌊S⌋₊ : ℕ) : ℝ) := by exact_mod_cast hKmem
    have hKS : ((⌊S⌋₊ : ℕ) : ℝ) ≤ S := Nat.floor_le hS
    linarith
  have hstep1 : ∑ y ∈ F, Wt (d : ℝ) c (linfNorm y : ℝ)
      ≤ ∑ y ∈ box d (F.sup linfNorm) \ box d ⌊S⌋₊,
          Wt (d : ℝ) c (linfNorm y : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Wt_nonneg (by positivity))
  have hstep2 : ∑ y ∈ box d (F.sup linfNorm) \ box d ⌊S⌋₊,
        Wt (d : ℝ) c (linfNorm y : ℝ)
      = ∑ y ∈ box d (F.sup linfNorm), Wt (d : ℝ) c (linfNorm y : ℝ)
        - ∑ y ∈ box d ⌊S⌋₊, Wt (d : ℝ) c (linfNorm y : ℝ) := by
    have h := Finset.sum_sdiff
      (f := fun y : Fin d → ℤ => Wt (d : ℝ) c (linfNorm y : ℝ)) (box_mono hKN)
    linarith
  have hstep3 : ∑ y ∈ box d (F.sup linfNorm), Wt (d : ℝ) c (linfNorm y : ℝ)
        - ∑ y ∈ box d ⌊S⌋₊, Wt (d : ℝ) c (linfNorm y : ℝ)
      = ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
          ((box d (m + 1) \ box d m).card : ℝ)
            * Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ) := by
    rw [sum_box_eq d (F.sup linfNorm) (fun n : ℕ => Wt (d : ℝ) c ((n : ℝ))),
      sum_box_eq d ⌊S⌋₊ (fun n : ℕ => Wt (d : ℝ) c ((n : ℝ)))]
    have h := Finset.sum_Ico_eq_sub
      (f := fun m : ℕ => ((box d (m + 1) \ box d m).card : ℝ)
        * Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ)) hKN
    rw [h]
    ring
  have hstep4 : ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
        ((box d (m + 1) \ box d m).card : ℝ) * Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ)
      ≤ ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
          2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) *
            LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) :=
    Finset.sum_le_sum fun m _ => layer_term_le_pureLog hd m
  have hstep5 : ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
        2 * (d : ℝ) * 3 ^ (d - 1) * (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) *
          LamR (((m + 1 : ℕ)) : ℝ) ^ (-c)
      = (2 * (d : ℝ) * 3 ^ (d - 1)) * ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
          (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hstep6 : (2 * (d : ℝ) * 3 ^ (d - 1)) *
        ∑ m ∈ Finset.Ico ⌊S⌋₊ (F.sup linfNorm),
          (((m + 1 : ℕ)) : ℝ) ^ (-1 : ℝ) * LamR (((m + 1 : ℕ)) : ℝ) ^ (-c)
      ≤ (2 * (d : ℝ) * 3 ^ (d - 1)) *
        (8 * 2 ^ c / (c - 1) * LamR (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (1 - c)) := by
    refine mul_le_mul_of_nonneg_left (sum_Ico_log_tail_le hc ⌊S⌋₊ (F.sup linfNorm)) ?_
    positivity
  have hstep7 : LamR (((⌊S⌋₊ + 1 : ℕ)) : ℝ) ^ (1 - c) ≤ LamR S ^ (1 - c) :=
    floor_succ_log_rpow_le hc.le hS
  refine le_trans hstep1 ?_
  rw [hstep2, hstep3]
  refine le_trans hstep4 (le_trans (le_of_eq hstep5) (le_trans hstep6 ?_))
  have hfac : (0 : ℝ) ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (8 * 2 ^ c / (c - 1)) := by
    have h1 : (0 : ℝ) < 2 ^ c := Real.rpow_pos_of_pos (by norm_num) c
    have h2 : (0 : ℝ) < c - 1 := by linarith
    positivity
  refine le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left hstep7 hfac)

/-! ## §8 Non-vacuity: a concrete instance -/
/-- The hypotheses of `sum_Wt_tail_le` are satisfiable and the constant is as claimed:
for `d = 1`, `γ = 1`, `c = 0`, `S = 0` and the single point `y = 1`, the left side is
`(1+1)^{-2} = 1/4` and the right side is `tailShellConst 1 1 = 16`. -/
example : ∑ y ∈ ({(fun _ : Fin 1 => (1 : ℤ))} : Finset (Fin 1 → ℤ)),
      Wt ((1 : ℝ) + 1) 0 (linfNorm y : ℝ) ≤ tailShellConst 1 1 * Wt 1 0 0 := by
  have h1 : linfNorm (fun _ : Fin 1 => (1 : ℤ)) = 1 := by
    simp [PercLib.CriticalLRP.FiniteVolume.linfNorm]
  have h := sum_Wt_tail_le (d := 1) (γ := 1) (c := 0) (S := 0)
    (F := ({(fun _ : Fin 1 => (1 : ℤ))} : Finset (Fin 1 → ℤ)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun y hy => by
      have hy' : y = (fun _ : Fin 1 => (1 : ℤ)) := Finset.mem_singleton.mp hy
      rw [hy', h1]
      norm_num)
  simpa using h

end CriticalLRPConv


set_option linter.hashCommand false
/-! ## §9 Axiom audit (no `sorry`, no custom axioms, no `native_decide`) -/
#print axioms CriticalLRPConv.tailShellConst_pos
#print axioms CriticalLRPConv.one_add_rpow_gap_le
#print axioms CriticalLRPConv.sum_Ico_rpow_tail_le
#print axioms CriticalLRPConv.floor_succ_rpow_le
#print axioms CriticalLRPConv.layer_term_le
#print axioms CriticalLRPConv.sum_Wt_tail_le
#print axioms CriticalLRPConv.tsum_Wt_tail_le
#print axioms CriticalLRPConv.tailShellConstLog
#print axioms CriticalLRPConv.one_add_log_gap_le
#print axioms CriticalLRPConv.sum_Ico_log_tail_le
#print axioms CriticalLRPConv.floor_succ_log_rpow_le
#print axioms CriticalLRPConv.layer_term_le_pureLog
#print axioms CriticalLRPConv.sum_Wt_tail_le_pureLog
