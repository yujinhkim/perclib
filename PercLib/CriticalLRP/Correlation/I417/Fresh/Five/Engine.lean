/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m1` Q5 artifact.
Original production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`; review revisions
are confined to strict module lints and explicit branch-lemma aggregation.
-/
/-
Independently built for swarm `smwxb4a1l`, member `m1`, direction Q5-FINITE-EVALUATION.
Read-only against production (`d9a001b7f0a33cf6395158f7621ad4de1fe3c7c8`).
Proofs only in this file; no new definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Engine

/-!
# Engine lemmas for the `q = 5` fresh-diagram evaluation

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (pp. 43--46).

The `q = 4` engine of production (`I417FreshFour.Eval`, `Fresh/Eval/Engine.lean`) supplies
`chain_L1 … chain_L4`, `tsum_arm_four_tuple`, the permutation lemmas `perm12/23/13` and the finite
index-sum expansions `tsum_fin2`, `tsum_fin2_bool`, `tsum_fin2_bool_bool`; all of them are reused
here verbatim.  What is added is exactly what a fourth attachment round and a fifth arm need:

* `iterPow_five_eq` / `chain_L5` — the five-leg chain through four summed attachment vertices is
  worth `T⁵`;
* `tsum_arm_five` / `tsum_arm_five_tuple` — the five labelled arms sum out to `χ⁵`;
* `arms_inner_five` — the five-arm tuple is moved to the innermost position of the branch sum, so
  each of the `384` branch terms can be evaluated with its arm sum inside;
* `tsum_idx3` — expansion of the eight-element index sum `((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool`;
* `swap12`, `swap23`, `swap34` — adjacent transpositions of four nested sums, used to put the four
  attachment vertices in the peel order of each branch (the nested order is *not* the peel order in
  general, and peeling in the wrong order would produce an unbounded two-point moment, which is
  exactly what is not allowed here).

Nothing here uses probability, BK, moment hypotheses or subcriticality: only the constant row sum
`∑_z τ(v,z) = χ`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFive

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417FreshFour.Eval
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The five-leg chain -/

/-- `T⁵(v,w) = ∑_{a,b,c,d} τ(v,a)τ(a,b)τ(b,c)τ(c,d)τ(d,w)`. -/
theorem iterPow_five_eq (π : Sym2 V → unitInterval) (v w : V) :
    iterPow (kernel π) 5 v w =
      ∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        tau π v a * tau π a b * tau π b c * tau π c d * tau π d w := by
  have h5 : iterPow (kernel π) 5 v w =
      ∑' a : V, tau π v a *
        (∑' b : V, ∑' c : V, ∑' d : V,
          tau π a b * tau π b c * tau π c d * tau π d w) := by
    show (∑' a : V, kernel π v a * iterPow (kernel π) 4 a w) = _
    refine tsum_congr fun a => ?_
    rw [iterPow_four_eq, kernel_def]
  rw [h5]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

/-- `y–a–b–c–d–w`: the five-leg chain contributes `T⁵`. -/
theorem chain_L5 (π : Sym2 V → unitInterval) (y w : V) :
    (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        tau π y a * tau π a b * tau π b c * tau π c d * tau π d w) =
      iterPow (kernel π) 5 y w :=
  (iterPow_five_eq π y w).symm

/-! ## The five labelled arms sum out to `χ⁵` -/

/-- **Summing the five labelled arms out.**  Each arm sits in exactly one leg, so the five arm legs
are independent one-variable sums; the constant row sum gives `χ⁵` whatever the five attachment
points `p1, …, p5` are, and whatever else the diagram carries (`C` does not involve the arm
values). -/
theorem tsum_arm_five (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (p1 p2 p3 p4 p5 : V) (C : ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, ∑' e : V,
        C * (tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d * tau π p5 e)) =
      C * χ ^ 5 := by
  have h1 : (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, ∑' e : V,
        C * (tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d * tau π p5 e)) =
      C * (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, ∑' e : V,
        tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d * tau π p5 e) := by
    simp only [ENNReal.tsum_mul_left]
  have h2 : (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, ∑' e : V,
        tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d * tau π p5 e) = χ ^ 5 := by
    rw [show (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, ∑' e : V,
        tau π p1 a * tau π p2 b * tau π p3 c * tau π p4 d * tau π p5 e) =
        χ * χ * χ * χ * χ from by
      simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hχ]]
    ring
  rw [h1, h2]

/-- **Summing the five labelled arms out**, with the arm values carried as a single tuple (the form
the `Fin 5 → V`-sum of the fresh event is reindexed to). -/
theorem tsum_arm_five_tuple (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (p1 p2 p3 p4 p5 : V) (C : ℝ≥0∞) :
    (∑' pa : V × V × V × V × V,
        C * (tau π p1 pa.1 * tau π p2 pa.2.1 * tau π p3 pa.2.2.1 * tau π p4 pa.2.2.2.1 *
          tau π p5 pa.2.2.2.2)) = C * χ ^ 5 := by
  simp only [ENNReal.tsum_prod']
  exact tsum_arm_five π χ hχ p1 p2 p3 p4 p5 C

/-! ## The arm tuple is the innermost sum -/

/-- The five-arm tuple sits in the innermost position of the family sum. -/
theorem arms_inner_five
    (F : V × V × V × V × V → Fin 2 → (Fin 2 ⊕ Bool) → ((Fin 2 ⊕ Bool) ⊕ Bool) →
      (((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool) → V → V → V → V → ℝ≥0∞) :
    (∑' p : V × V × V × V × V, ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool),
        ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool), ∑' (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool),
        ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V), ∑' (z4 : V),
        F p k1 k2 k3 k4 z1 z2 z3 z4) =
      ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
        ∑' (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool), ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
        ∑' (z4 : V), ∑' p : V × V × V × V × V, F p k1 k2 k3 k4 z1 z2 z3 z4 := by
  rw [ENNReal.tsum_comm]
  refine Eq.trans (tsum_congr fun k1 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    tsum_congr fun k4 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    tsum_congr fun k4 => tsum_congr fun z1 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    tsum_congr fun k4 => tsum_congr fun z1 => tsum_congr fun z2 => ENNReal.tsum_comm) ?_
  refine Eq.trans (tsum_congr fun k1 => tsum_congr fun k2 => tsum_congr fun k3 =>
    tsum_congr fun k4 => tsum_congr fun z1 => tsum_congr fun z2 => tsum_congr fun z3 =>
    ENNReal.tsum_comm) ?_
  rfl

/-! ## Expanding the eight-element index sum of the `q = 5` family -/

/-- `((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool` sum expansion, in the order of the family. -/
theorem tsum_idx3 (H : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool → ℝ≥0∞) :
    (∑' k : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool, H k) =
      H (Sum.inl (Sum.inl (Sum.inl 0))) + H (Sum.inl (Sum.inl (Sum.inl 1))) +
        H (Sum.inl (Sum.inl (Sum.inr false))) + H (Sum.inl (Sum.inl (Sum.inr true))) +
        H (Sum.inl (Sum.inr false)) + H (Sum.inl (Sum.inr true)) + H (Sum.inr false) +
        H (Sum.inr true) := by
  rw [tsum_fintype, Fintype.sum_sum_type]
  have h1 : (∑ a : (Fin 2 ⊕ Bool) ⊕ Bool, H (Sum.inl a)) =
      (∑' a : (Fin 2 ⊕ Bool) ⊕ Bool, H (Sum.inl a)) :=
    (tsum_fintype (fun a : (Fin 2 ⊕ Bool) ⊕ Bool => H (Sum.inl a))).symm
  rw [h1, tsum_fin2_bool_bool]
  rw [Fintype.sum_bool]
  ring

/-! ## Adjacent transpositions of four nested sums -/

/-- Swap the two outermost of four nested sums. -/
theorem swap12 (F : V → V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, F a b c d) =
      ∑' b : V, ∑' a : V, ∑' c : V, ∑' d : V, F a b c d :=
  ENNReal.tsum_comm

/-- Swap the two middle ones of four nested sums. -/
theorem swap23 (F : V → V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, F a b c d) =
      ∑' a : V, ∑' c : V, ∑' b : V, ∑' d : V, F a b c d :=
  tsum_congr fun _ => ENNReal.tsum_comm

/-- Swap the two innermost of four nested sums. -/
theorem swap34 (F : V → V → V → V → ℝ≥0∞) :
    (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V, F a b c d) =
      ∑' a : V, ∑' b : V, ∑' d : V, ∑' c : V, F a b c d :=
  tsum_congr fun _ => tsum_congr fun _ => ENNReal.tsum_comm

end PercLib.CriticalLRP.I417FreshFive

namespace PercLib.CriticalLRP.I417FreshFive

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Eval
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The pure `y`--`w` chain lemmas (no off-path vertices) -/

/-- The one-leg path: `τ(y,w) = T¹(w,y)`. -/
theorem chainP1 (π : Sym2 V → unitInterval) (y w : V) :
    tau π y w = iterPow (kernel π) 1 w y := by
  rw [iterPow_one, kernel_def, tau_symm]

/-- The two-leg path. -/
theorem chainP2 (π : Sym2 V → unitInterval) (y w : V) :
    (∑' a : V, tau π y a * tau π a w) = iterPow (kernel π) 2 w y := by
  rw [iterPow_kernel_comm, I417FreshTwo.iterPow_two_eq]

/-- The three-leg path. -/
theorem chainP3 (π : Sym2 V → unitInterval) (y w : V) :
    (∑' a : V, ∑' b : V, tau π y a * tau π a b * tau π b w) =
      iterPow (kernel π) 3 w y := by
  rw [iterPow_kernel_comm, I417FreshTwo.iterPow_three_eq]

/-- The four-leg path. -/
theorem chainP4 (π : Sym2 V → unitInterval) (y w : V) :
    (∑' a : V, ∑' b : V, ∑' c : V,
        tau π y a * tau π a b * tau π b c * tau π c w) =
      iterPow (kernel π) 4 w y := by
  rw [iterPow_kernel_comm, iterPow_four_eq]

/-- The five-leg path (the `q = 5` case with all four attachment vertices on the path). -/
theorem chainP5 (π : Sym2 V → unitInterval) (y w : V) :
    (∑' a : V, ∑' b : V, ∑' c : V, ∑' d : V,
        tau π y a * tau π a b * tau π b c * tau π c d * tau π d w) =
      iterPow (kernel π) 5 w y := by
  rw [iterPow_kernel_comm, iterPow_five_eq]

end PercLib.CriticalLRP.I417FreshFive
