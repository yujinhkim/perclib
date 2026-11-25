/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m5/I417Gen/SourceForm.lean; module path rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.General.Main

/-!
# Lemma I.4.17: the source-shaped forms of the general `p, q` marked expansion

The general marked expansion (`I417Gen.twoCopy_moment_le_marked`) bounds the moment gap by the
marked family indexed by `(terminal, mark) : Fin q × V`.  This file puts it into the two shapes the
paper actually uses.

1. **The paper's single sum over the mark** (`moment_gap_tsub_le_marked_single`): the terminal index
   is summed inside, so the right-hand side is `∑_w jointPow x p w · ∑_j ∑_g P(freshMark …)`,
   i.e. the paper's `∑_w ∑_{x_1…x_p} P(w, x_1,…,x_p ∈ K_x) · P(…)`.  Here
   `jointPow π x p w = E[|K_x|^p 1(w ∈ K_x)]` (`tsum_labelEvent_inter`).

2. **The `q = 1` reduction to two-point functions** (`twoCopy_moment_le_marked_q_one`): for `q = 1`
   the fresh factor is a *single* arm, so the `q`-fold sum over `g` collapses to a sum over that
   arm and BK in the fresh copy (`bk_connSet_ennreal`) bounds every term by `τ(y,w) τ(w,z)`.  The
   result is the paper's shape with the `p`-th-moment factor kept exact:
   `E|K_x|^p E|K_y| ≤ E[1(x↮y)|K_x|^p|K_y|] + ∑_w E[|K_x|^p 1(w∈K_x)] τ(y,w) (E|K|)_w`.
   This is genuinely beyond the `p = 2, q = 1` formalization at HEAD (`Correlation/I417`): the
   base-side moment is the *p*-th one, and only the base factor `jointPow` remains to be evaluated
   by tree diagrams.

What remains for the paper's `C_{p,q,ℓ} T^ℓ(x,y)(E|K|)^{2p+2q+1−ℓ}` is exactly the tree-diagram
bound on `jointPow π x p w` (the `(2p−3)!!` rooted-tree count of Lemma I.4.16) and, for `q ≥ 2`,
the tree-diagram expansion of the fresh factor.  Neither is claimed here.

No `sorry`, no custom axioms; no definitions.
-/


open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Sums over `Fin 1 → V` -/

theorem tsum_fin_one {A : Type*} (f : (Fin 1 → A) → ℝ≥0∞) :
    (∑' g : Fin 1 → A, f g) = ∑' a : A, f (fun _ => a) := by
  rw [← Equiv.tsum_eq (Equiv.funUnique (Fin 1) A) (fun a : A => f (fun _ => a))]
  refine tsum_congr fun g => ?_
  have h : (Equiv.funUnique (Fin 1) A) g = g 0 := rfl
  rw [h]
  congr 1
  funext i
  exact congrArg g (Subsingleton.elim i 0)

/-- Swapping the two coordinates of a product index, for `ℝ≥0∞`-valued sums. -/
theorem tsum_prod_swap {A B : Type*} [Countable A] [Countable B] (F : A → B → ℝ≥0∞) :
    (∑' p : A × B, F p.1 p.2) = ∑' q : B × A, F q.2 q.1 := by
  rw [ENNReal.tsum_prod (f := F), ENNReal.tsum_comm (f := F),
    ← ENNReal.tsum_prod (f := fun (b : B) (a : A) => F a b)]

/-- For a single arm (`q = 1`), the marked fresh family is dominated by the two-point functions:
`∑_g P(freshMark y g j w) ≤ τ(y,w) ∑_z τ(w,z)`.  The first factor is the disjoint `y ↔ w`, the
second the free arm `w ↔ z` which BK makes independent of it. -/
theorem tsum_freshMark_fin_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (y w : V)
    (j : Fin 1) :
    (∑' g : Fin 1 → V, (edgeMeasure π) (freshMark y g j w)) ≤
      (edgeMeasure π) (connSet y w) * (∑' z : V, (edgeMeasure π) (connSet w z)) := by
  rw [tsum_fin_one]
  have hterm : ∀ z : V, (edgeMeasure π) (freshMark y (fun _ => z) j w) ≤
      (edgeMeasure π) (connSet y w) * (edgeMeasure π) (connSet w z) := by
    intro z
    refine le_trans (measure_mono ?_) (bk_connSet_ennreal π hπ y w w z)
    intro ω hω
    exact hω.1
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_mul_left]

/-! ## The paper's single sum over the mark -/

/-- **The marked expansion in the paper's `∑_w` shape**, arbitrary finite `p` and `1 ≤ q`. -/
theorem moment_gap_tsub_le_marked_single (π : Sym2 V → unitInterval) (x y : V) {p q : ℕ}
    (hq : 1 ≤ q) :
    I417A.momentProd π x y p q - I417A.rawDiff π x y p q ≤
      ∑' w : V, jointPow π x p w *
        (∑' j : Fin q, ∑' g : Fin q → V, (edgeMeasure π) (freshMark y g j w)) := by
  refine le_trans (moment_gap_tsub_le_marked π x y hq) ?_
  have h1 : (∑' jw : Fin q × V, jointPow π x p jw.2 *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2))) =
      ∑' w : V, ∑' j : Fin q, jointPow π x p w *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g j w)) := by
    rw [tsum_prod_swap (F := fun (j : Fin q) (w : V) => jointPow π x p w *
      (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g j w)))]
    rw [ENNReal.tsum_prod (f := fun (w : V) (j : Fin q) => jointPow π x p w *
      (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g j w)))]
  rw [h1]
  refine le_of_eq (tsum_congr fun w => ?_)
  exact ENNReal.tsum_mul_left

/-! ## The `q = 1` case: the paper's two-point-function bound with the exact `p`-th moment -/

/-- **Lemma I.4.17 for `q = 1` and arbitrary `p`**, in the additive `ℝ≥0∞` form:
`E|K_x|^p E|K_y| ≤ E[1(x↮y)|K_x|^p|K_y|] + ∑_w E[|K_x|^p 1(w∈K_x)] τ(y,w) ∑_z τ(w,z)`.
The only input beyond the general marked expansion is BK in the fresh copy. -/
theorem twoCopy_moment_le_marked_q_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (p : ℕ) :
    I417A.momentProd π x y p 1 ≤
      I417A.rawDiff π x y p 1 +
        ∑' w : V, jointPow π x p w *
          ((edgeMeasure π) (connSet y w) * (∑' z : V, (edgeMeasure π) (connSet w z))) := by
  refine le_trans (twoCopy_moment_le_marked π x y (p := p) (q := 1) le_rfl) ?_
  refine add_le_add le_rfl ?_
  have h1 : (∑' jw : Fin 1 × V, jointPow π x p jw.2 *
        (∑' g : Fin 1 → V, (edgeMeasure π) (freshMark y g jw.1 jw.2))) =
      ∑' j : Fin 1, ∑' w : V, jointPow π x p w *
        (∑' g : Fin 1 → V, (edgeMeasure π) (freshMark y g j w)) := by
    rw [ENNReal.tsum_prod (f := fun (j : Fin 1) (w : V) => jointPow π x p w *
      (∑' g : Fin 1 → V, (edgeMeasure π) (freshMark y g j w)))]
  rw [h1]
  refine le_trans (ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun w =>
    mul_le_mul' le_rfl (tsum_freshMark_fin_one π hπ y w j)) ?_
  rw [tsum_fintype]
  simp

/-- **The `q = 1` case in the source's subtractive shape.** -/
theorem moment_gap_tsub_le_marked_q_one (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (p : ℕ) :
    I417A.momentProd π x y p 1 - I417A.rawDiff π x y p 1 ≤
      ∑' w : V, jointPow π x p w *
        ((edgeMeasure π) (connSet y w) * (∑' z : V, (edgeMeasure π) (connSet w z))) := by
  refine tsub_le_iff_right.mpr ?_
  rw [add_comm]
  exact twoCopy_moment_le_marked_q_one π hπ x y p

end PercLib.CriticalLRP.I417Gen

namespace PercLib.CriticalLRP.I417Gen

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-! ## `q = 0` is genuinely excluded

The covering `prodSet_subset` is stated with `1 ≤ q` because with no `y`-arm there is no terminal
vertex to end the marked walk on.  This is not an artefact of the formalization: for `q = 0` the
marked family is empty, and every configuration with `y ∈ K_x(ω₁)` lies in the product event but
neither in the diagonal event nor in a marked one. -/

/-- **`q = 0` fails the covering.**  For `x ≠ y` there is no covering of the product event by the
diagonal event and the (empty) marked family. -/
theorem prodSet_not_subset_q_zero (x y : V) (hxy : x ≠ y) :
    ¬ (∀ (f : Fin 0 → V) (g : Fin 0 → V),
        prodSet x y f g ⊆ diagSet x y f g ∪ ⋃ jw : Fin 0 × V, markSet x y f g jw.1 jw.2) := by
  intro hcov
  have hconn : (Set.univ : Config V) ∈ connSet x y :=
    pathConnects_iff.mp ⟨SimpleGraph.Walk.cons (by simpa using hxy) SimpleGraph.Walk.nil,
      fun e _ => Set.mem_univ e⟩
  have hprod : (Set.univ, Set.univ) ∈ prodSet x y (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → V) :=
    ⟨fun j => Fin.elim0 j, fun i => Fin.elim0 i⟩
  rcases hcov (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → V) hprod with hd | hm
  · exact hd.2.1 hconn
  · obtain ⟨jw, -⟩ := Set.mem_iUnion.mp hm
    exact Fin.elim0 jw.1

end PercLib.CriticalLRP.I417Gen

namespace PercLib.CriticalLRP.I417Gen

variable {V : Type*} [Countable V]

/-- **The source's basepoint-free shape** `E|K|^p E|K|^q − E[|K_x|^p|K_y|^q 1(x ↮ y)] ≤ (marked)`.
On the canonical model, "transitive weighted graph" is rendered by `π`-preserving vertex
permutations carrying the basepoint `o` to `x` and to `y`; the two cluster moments at `o` are then
the paper's `E|K|^p` and `E|K|^q`. -/
theorem moment_gap_tsub_le_marked_basepoint (π : Sym2 V → unitInterval) (o x y : V) {p q : ℕ}
    (hq : 1 ≤ q)
    (gx : V ≃ V) (hgx : ∀ e : Sym2 V, π (Sym2.map gx e) = π e) (hx : gx o = x)
    (gy : V ≃ V) (hgy : ∀ e : Sym2 V, π (Sym2.map gy e) = π e) (hy : gy o = y) :
    (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p ∂(edgeMeasure π)) *
        (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q ∂(edgeMeasure π)) -
      I417A.rawDiff π x y p q ≤
      ∑' jw : Fin q × V, jointPow π x p jw.2 *
        (∑' g : Fin q → V, (edgeMeasure π) (freshMark y g jw.1 jw.2)) := by
  have hpx : (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ p ∂(edgeMeasure π)) =
      ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p ∂(edgeMeasure π) := by
    rw [← hx]
    exact (PercLib.CriticalLRP.TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig
      π gx hgx p o).symm
  have hqy : (∫⁻ ω, Percolation.cardFun (cluster ω o) ^ q ∂(edgeMeasure π)) =
      ∫⁻ ω, Percolation.cardFun (cluster ω y) ^ q ∂(edgeMeasure π) := by
    rw [← hy]
    exact (PercLib.CriticalLRP.TreeExpansion.FivePoint.lintegral_cardFun_pow_permConfig
      π gy hgy q o).symm
  rw [hpx, hqy]
  exact moment_gap_tsub_le_marked π x y hq

end PercLib.CriticalLRP.I417Gen
