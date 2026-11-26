/-
Moment log-convexity for the canonical independent-edge law
`edgeMeasure π` of `PercLib.CriticalLRP`, at the production interfaces.

Independent Ultramath work (member `m4` of swarm `smwxuymqb`), production base
`6569f9781a4bf1ef35843ff3cd468b1d934c4527`.

Nothing here restates Lemma I.4.17 or Proposition I.4.20.  The content is the
elementary Lyapunov (log-convexity) inequality for the cluster moments
`I420Case1.powMomentAt π m v = ∫⁻ ω, |K_v(ω)|^m ∂(edgeMeasure π)`, proved from a
single Hölder step, together with the resulting comparison
`I420Case3.biasTarget m₁ m₂ p ≤ m_a · m_b` for `a + b = p + 1`.

The comparison is what `I420Case3.Main`/`Compare` carry as the explicit premise
`hcmp`/`hcmp0` in the Case 3 chain; see `MomentLogConvex/Main.lean` for the
resulting theorem-level reduction.

No new definitions are introduced in this file (the swarm rule confines new
definitions to `Defs.lean`); `Defs.lean` is empty for that reason.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Bound

/-!
# Log-convexity of the cluster moment sequence

For a nonnegative random variable the map `m ↦ E[X^m]` is log-convex, i.e.
`(E X^(j+1))^2 ≤ (E X^j) (E X^(j+2))`.  We prove this for `X = |K_v|` under the
canonical independent-edge law, in `ℝ≥0∞` (so infinite clusters are harmless) and
in `ℝ` under the finiteness hypotheses production already carries.

Consequences, all in `ℝ`:

* `momR_succ_sq_le` : `(E|K|^(j+1))^2 ≤ (E|K|^j)(E|K|^(j+2))`;
* `momR_ratio_mono` : `j ↦ E|K|^j / E|K|^(j-1)` is monotone;
* `momR_two_pow_le_mul` : `(E|K|^2)^(j-1) · E|K| ≤ E|K|^j · (E|K|)^(j-1)`;
* `biasTarget_le_mul_momR` : `biasTarget m₁ m₂ p ≤ E|K|^a · E|K|^b` for
  `1 ≤ a`, `1 ≤ b`, `a + b = p + 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

namespace MomentLogConvex

variable {V : Type*} [Countable V]

/-! ## The pointwise half-power identity -/

/-- `(|K_v|^j)^{1/2} (|K_v|^(j+2))^{1/2} = |K_v|^(j+1)` for `j ≥ 1`.

This is the integrand identity of the Cauchy--Schwarz step.  The `ℝ≥0∞` value
`|K_v|` may be `⊤` (an infinite cluster); `ENNReal.rpow_add` needs a finite, nonzero
base, so that case is separated and uses `⊤ ^ y = ⊤` for `y > 0`. -/
theorem clusterVol_rpow_half_mul (ω : Config V) (v : V) {j : ℕ} (hj : 1 ≤ j) :
    (clusterVol ω v ^ j) ^ (1 / 2 : ℝ) * (clusterVol ω v ^ (j + 2)) ^ (1 / 2 : ℝ) =
      clusterVol ω v ^ (j + 1) := by
  rcases eq_or_ne (clusterVol ω v) ⊤ with htop | htop
  · rw [htop]
    simp [show j ≠ 0 by omega]
  · have h0 : clusterVol ω v ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le one_pos (one_le_clusterVol ω v))
    have hA : (clusterVol ω v ^ j) ^ (1 / 2 : ℝ) =
        clusterVol ω v ^ ((j : ℝ) * (1 / 2)) := by
      rw [← ENNReal.rpow_natCast (clusterVol ω v) j, ← ENNReal.rpow_mul]
    have hB : (clusterVol ω v ^ (j + 2)) ^ (1 / 2 : ℝ) =
        clusterVol ω v ^ (((j : ℝ) + 2) * (1 / 2)) := by
      rw [← ENNReal.rpow_natCast (clusterVol ω v) (j + 2), ← ENNReal.rpow_mul]
      push_cast
      ring_nf
    rw [hA, hB, ← ENNReal.rpow_natCast (clusterVol ω v) (j + 1),
      ← ENNReal.rpow_add _ _ h0 htop]
    congr 1
    push_cast
    ring

/-! ## The one-step Cauchy--Schwarz inequality -/

/-- **One-step Cauchy--Schwarz (Hölder) step.**  `E|K_v|^(j+1)` is at most the
geometric mean of `E|K_v|^j` and `E|K_v|^(j+2)`. -/
theorem powMomentAt_succ_le_rpow (π : Sym2 V → unitInterval) (v : V) {j : ℕ} (hj : 1 ≤ j) :
    I420Case1.powMomentAt π (j + 1) v ≤
      (I420Case1.powMomentAt π j v) ^ (1 / 2 : ℝ) *
        (I420Case1.powMomentAt π (j + 2) v) ^ (1 / 2 : ℝ) := by
  have hf : AEMeasurable (fun ω : Config V => clusterVol ω v ^ j) (edgeMeasure π) :=
    ((measurable_clusterVol v).pow_const j).aemeasurable
  have hg : AEMeasurable (fun ω : Config V => clusterVol ω v ^ (j + 2)) (edgeMeasure π) :=
    ((measurable_clusterVol v).pow_const (j + 2)).aemeasurable
  have hcs := ENNReal.lintegral_mul_norm_pow_le (μ := edgeMeasure π) (f :=
      fun ω : Config V => clusterVol ω v ^ j)
    (g := fun ω : Config V => clusterVol ω v ^ (j + 2)) hf hg
    (p := (1 / 2 : ℝ)) (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  refine le_trans (le_of_eq ?_) hcs
  rw [I420Case1.powMomentAt]
  exact lintegral_congr fun ω => (clusterVol_rpow_half_mul ω v hj).symm

/-- `(x^{1/2})^2 = x` in `ℝ≥0∞`. -/
theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **One-step Cauchy--Schwarz, squared form, in `ℝ≥0∞`.**
`(E|K_v|^(j+1))^2 ≤ (E|K_v|^j) (E|K_v|^(j+2))`. -/
theorem powMomentAt_succ_sq_le (π : Sym2 V → unitInterval) (v : V) {j : ℕ} (hj : 1 ≤ j) :
    (I420Case1.powMomentAt π (j + 1) v) ^ 2 ≤
      I420Case1.powMomentAt π j v * I420Case1.powMomentAt π (j + 2) v := by
  have hstep := powMomentAt_succ_le_rpow (π := π) v hj
  calc (I420Case1.powMomentAt π (j + 1) v) ^ 2
      ≤ ((I420Case1.powMomentAt π j v) ^ (1 / 2 : ℝ) *
          (I420Case1.powMomentAt π (j + 2) v) ^ (1 / 2 : ℝ)) ^ 2 := by
        exact ENNReal.pow_le_pow_left hstep
    _ = I420Case1.powMomentAt π j v * I420Case1.powMomentAt π (j + 2) v := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-! ## Transfer to `ℝ` -/

/-- **Log-convexity of the cluster moments in `ℝ`.**
`(E|K_v|^(j+1))^2 ≤ (E|K_v|^j)(E|K_v|^(j+2))`, with the three moments finite. -/
theorem momR_succ_sq_le (π : Sym2 V → unitInterval) (v : V) {j : ℕ} (hj : 1 ≤ j)
    (h0 : I420Case1.powMomentAt π j v ≠ ⊤)
    (h1 : I420Case1.powMomentAt π (j + 1) v ≠ ⊤)
    (h2 : I420Case1.powMomentAt π (j + 2) v ≠ ⊤) :
    (I420Case1.momR π (j + 1) v) ^ 2 ≤
      I420Case1.momR π j v * I420Case1.momR π (j + 2) v := by
  have hsq := powMomentAt_succ_sq_le (π := π) v hj
  have hL : (I420Case1.powMomentAt π (j + 1) v) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top h1
  have hR : I420Case1.powMomentAt π j v * I420Case1.powMomentAt π (j + 2) v ≠ ⊤ :=
    ENNReal.mul_ne_top h0 h2
  have hmain : (I420Case1.powMomentAt π (j + 1) v).toReal ^ 2 ≤
      (I420Case1.powMomentAt π j v).toReal * (I420Case1.powMomentAt π (j + 2) v).toReal := by
    have h := (ENNReal.toReal_le_toReal hL hR).mpr hsq
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul] at h
  simpa only [I420Case1.momR] using hmain

end MomentLogConvex

end I420Case3

end PercLib.CriticalLRP


namespace PercLib.CriticalLRP

namespace I420Case3

namespace MomentLogConvex

variable {V : Type*} [Countable V]

/-! ## The moment ratio is monotone

Everything below works with the real shadow `I420Case1.momR π m o`.  The finiteness
range carried in each statement is exactly the moments used by that statement. -/

/-- **Monotonicity of the moment ratio, division-free.**  For `n ≥ 1`,
`E|K|^n E|K|^2 ≤ E|K|^(n+1) E|K|`, i.e. `m_(n+1)/m_n ≥ m_2/m_1`. -/
theorem momR_mul_one_ge (π : Sym2 V → unitInterval) (o : V) :
    ∀ n : ℕ, 1 ≤ n → (∀ i : ℕ, 1 ≤ i → i ≤ n + 2 → I420Case1.powMomentAt π i o ≠ ⊤) →
      I420Case1.momR π n o * I420Case1.momR π 2 o ≤
        I420Case1.momR π (n + 1) o * I420Case1.momR π 1 o := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ k ih =>
      intro _ hfin
      rcases Nat.eq_zero_or_pos k with hk0 | hk
      · subst hk0
        change I420Case1.momR π 1 o * I420Case1.momR π 2 o ≤
          I420Case1.momR π 2 o * I420Case1.momR π 1 o
        exact le_of_eq (mul_comm _ _)
      · have hfin' : ∀ i : ℕ, 1 ≤ i → i ≤ k + 2 → I420Case1.powMomentAt π i o ≠ ⊤ :=
          fun i hi hik => hfin i hi (by omega)
        have hIH := ih hk hfin'
        have hstep := momR_succ_sq_le (π := π) o hk
          (hfin k (by omega) (by omega)) (hfin (k + 1) (by omega) (by omega))
          (hfin (k + 2) (by omega) (by omega))
        have hkpos : (0 : ℝ) < I420Case1.momR π k o :=
          momR_pos (hfin k (by omega) (by omega))
        have hk1pos : (0 : ℝ) < I420Case1.momR π (k + 1) o :=
          momR_pos (hfin (k + 1) (by omega) (by omega))
        have h1nn : (0 : ℝ) ≤ I420Case1.momR π 1 o :=
          le_of_lt (momR_pos (hfin 1 (by omega) (by omega)))
        have hmul : I420Case1.momR π k o * I420Case1.momR π 2 o *
            I420Case1.momR π (k + 1) o ≤
              I420Case1.momR π k o * I420Case1.momR π (k + 2) o *
                I420Case1.momR π 1 o := by
          calc I420Case1.momR π k o * I420Case1.momR π 2 o *
              I420Case1.momR π (k + 1) o
              ≤ (I420Case1.momR π (k + 1) o * I420Case1.momR π 1 o) *
                  I420Case1.momR π (k + 1) o := by
                exact mul_le_mul_of_nonneg_right hIH (le_of_lt hk1pos)
            _ = (I420Case1.momR π (k + 1) o) ^ 2 * I420Case1.momR π 1 o := by ring
            _ ≤ I420Case1.momR π k o * I420Case1.momR π (k + 2) o *
                  I420Case1.momR π 1 o := by
                exact mul_le_mul_of_nonneg_right hstep h1nn
        rw [show k + 1 + 1 = k + 2 by omega]
        refine le_of_mul_le_mul_left ?_ hkpos
        calc I420Case1.momR π k o *
              (I420Case1.momR π (k + 1) o * I420Case1.momR π 2 o)
            = I420Case1.momR π k o * I420Case1.momR π 2 o *
                I420Case1.momR π (k + 1) o := by ring
          _ ≤ I420Case1.momR π k o * I420Case1.momR π (k + 2) o *
                I420Case1.momR π 1 o := hmul
          _ = I420Case1.momR π k o *
                (I420Case1.momR π (k + 2) o * I420Case1.momR π 1 o) := by ring

/-- **Lyapunov lower bound for the moments.**
`(E|K|^2)^n E|K| ≤ E|K|^(n+1) (E|K|)^n`, the iterated form of the one-step
inequality `(E|K|^(j+1))^2 ≤ E|K|^j E|K|^(j+2)`. -/
theorem momR_two_pow_mul_le (π : Sym2 V → unitInterval) (o : V) :
    ∀ n : ℕ, (∀ i : ℕ, 1 ≤ i → i ≤ n + 2 → I420Case1.powMomentAt π i o ≠ ⊤) →
      (I420Case1.momR π 2 o) ^ n * I420Case1.momR π 1 o ≤
        I420Case1.momR π (n + 1) o * (I420Case1.momR π 1 o) ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
      intro hfin
      have hfin' : ∀ i : ℕ, 1 ≤ i → i ≤ k + 2 → I420Case1.powMomentAt π i o ≠ ⊤ :=
        fun i hi hik => hfin i hi (by omega)
      have hIH := ih hfin'
      have hT := momR_mul_one_ge (π := π) o (k + 1) (by omega)
        (fun i hi hik => hfin i hi (by omega))
      have h1pos : (0 : ℝ) < I420Case1.momR π 1 o :=
        momR_pos (hfin 1 (by omega) (by omega))
      have h2nn : (0 : ℝ) ≤ I420Case1.momR π 2 o :=
        le_of_lt (momR_pos (hfin 2 (by omega) (by omega)))
      have h1nn : (0 : ℝ) ≤ (I420Case1.momR π 1 o) ^ k := by positivity
      calc (I420Case1.momR π 2 o) ^ (k + 1) * I420Case1.momR π 1 o
          = I420Case1.momR π 2 o * ((I420Case1.momR π 2 o) ^ k *
              I420Case1.momR π 1 o) := by rw [pow_succ]; ring
        _ ≤ I420Case1.momR π 2 o *
              (I420Case1.momR π (k + 1) o * (I420Case1.momR π 1 o) ^ k) := by
            exact mul_le_mul_of_nonneg_left hIH h2nn
        _ = (I420Case1.momR π (k + 1) o * I420Case1.momR π 2 o) *
              (I420Case1.momR π 1 o) ^ k := by ring
        _ ≤ (I420Case1.momR π (k + 2) o * I420Case1.momR π 1 o) *
              (I420Case1.momR π 1 o) ^ k := by
            exact mul_le_mul_of_nonneg_right hT h1nn
        _ = I420Case1.momR π (k + 1 + 1) o * (I420Case1.momR π 1 o) ^ (k + 1) := by
            rw [pow_succ]; ring

/-- **The Case 3 denominator comparison, from moment log-convexity.**
For `a, b ≥ 1` with `a + b = p + 1`,
`biasTarget m₁ m₂ p = (m₂/m₁)^(p-1) m₁² ≤ m_a · m_b`.

The moments are the cluster moments at a common base point `o`; all moments up to
order `p + 1` are assumed finite. -/
theorem biasTarget_le_mul_momR (π : Sym2 V → unitInterval) (o : V) {p : ℕ} (hp : 3 ≤ p)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = p + 1)
    (hfin : ∀ i : ℕ, 1 ≤ i → i ≤ p + 1 → I420Case1.powMomentAt π i o ≠ ⊤) :
    biasTarget (I420Case1.momR π 1 o) (I420Case1.momR π 2 o) p ≤
      I420Case1.momR π a o * I420Case1.momR π b o := by
  have hpa : a ≤ p := by omega
  have hpb : b ≤ p := by omega
  have hA : a - 1 + 1 = a := Nat.succ_pred_eq_of_pos ha
  have hB : b - 1 + 1 = b := Nat.succ_pred_eq_of_pos hb
  have hAB : a - 1 + (b - 1) = p - 1 := by omega
  have hIA := momR_two_pow_mul_le (π := π) o (a - 1)
    (fun i hi hik => hfin i hi (by omega))
  have hIB := momR_two_pow_mul_le (π := π) o (b - 1)
    (fun i hi hik => hfin i hi (by omega))
  rw [hA] at hIA
  rw [hB] at hIB
  have h1pos : (0 : ℝ) < I420Case1.momR π 1 o := momR_pos (hfin 1 (by omega) (by omega))
  have hprod0 : (I420Case1.momR π 2 o ^ (a - 1) * I420Case1.momR π 1 o) *
      (I420Case1.momR π 2 o ^ (b - 1) * I420Case1.momR π 1 o) ≤
      (I420Case1.momR π a o * I420Case1.momR π 1 o ^ (a - 1)) *
        (I420Case1.momR π b o * I420Case1.momR π 1 o ^ (b - 1)) :=
    mul_le_mul hIA hIB
      (by
        have h2 := momR_pos (hfin 2 (by omega) (by omega))
        have h1 := momR_pos (hfin 1 (by omega) (by omega))
        positivity)
      (by
        have ha' := momR_pos (hfin a (by omega) (by omega))
        have h1 := momR_pos (hfin 1 (by omega) (by omega))
        positivity)
  have hprod : (I420Case1.momR π 2 o) ^ (p - 1) * (I420Case1.momR π 1 o) ^ 2 ≤
      I420Case1.momR π a o * I420Case1.momR π b o *
        (I420Case1.momR π 1 o) ^ (p - 1) := by
    calc (I420Case1.momR π 2 o) ^ (p - 1) * (I420Case1.momR π 1 o) ^ 2
        = (I420Case1.momR π 2 o ^ (a - 1) * I420Case1.momR π 1 o) *
            (I420Case1.momR π 2 o ^ (b - 1) * I420Case1.momR π 1 o) := by
          rw [← hAB, pow_add]; ring
      _ ≤ (I420Case1.momR π a o * I420Case1.momR π 1 o ^ (a - 1)) *
            (I420Case1.momR π b o * I420Case1.momR π 1 o ^ (b - 1)) := hprod0
      _ = I420Case1.momR π a o * I420Case1.momR π b o *
            (I420Case1.momR π 1 o) ^ (p - 1) := by
          rw [← hAB, pow_add]; ring
  have hbias : biasTarget (I420Case1.momR π 1 o) (I420Case1.momR π 2 o) p =
      (I420Case1.momR π 2 o) ^ (p - 1) * (I420Case1.momR π 1 o) ^ 2 /
        (I420Case1.momR π 1 o) ^ (p - 1) := by
    unfold biasTarget
    rw [div_pow]
    ring
  rw [hbias, div_le_iff₀ (by positivity : (0 : ℝ) < (I420Case1.momR π 1 o) ^ (p - 1))]
  exact hprod

end MomentLogConvex

end I420Case3

end PercLib.CriticalLRP
