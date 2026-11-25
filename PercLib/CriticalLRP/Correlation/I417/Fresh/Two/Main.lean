/- Integrated from independently rebuilt Ultramath work.
Production base 37c0efc68ae8ef365d8d155bc931fd784fdfde2b.
Scratch source: ../../.ultramath/smwvnrt0i/m3/M3Main.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Defs

/-!
# The fresh side of Lemma I.4.17 at `q = 2`, with no remaining premise

Source: Tom Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.17 (p. 45).

The fresh-copy factor of the printed proof is `∑_{y₁,…,y_q} P(E)`, where `E` is the event that all
`q` labelled arms lie in the fresh cluster `K̃_y` and the mark `w` lies on an open path from `y` to
them.  Production writes it `∑_g (edgeMeasure π) (I417Gen.freshMark y g j w)` and states the diagram
inequality as the premise `FreshCombBound π q`.  `freshCombBound_holds_one` disposes of `q = 1`.
This file disposes of `q = 2`: `freshCombBound_two` proves `FreshCombBound π 2` for every countable
vertex set and every `π` with `π e < 1` (BK), with no further hypothesis.

The proof is the printed one, in the exact form in which the chain family absorbs it.

* `freshMark_subset_threeTerminal`: the fresh event at `q = 2` implies that the two arms and the
  mark all lie in the cluster of the hub `w`.
* `freshMark_measure_le_leafShape`: hence the checked three-terminal tree-graph inequality
  `I417Example.threeLeaf_treeGraph` applies at `w` (the printed two-level branch-point expansion).
  It produces three diagram shapes.
* `tsum_first_shape`, `tsum_second_shape`, `tsum_third_shape`: summing the two arms out factors each
  shape into `∑_{u,v} sTerm i u v`, with `χ` for each free arm.
* `tsum_sTerm2_eq_sTerm3`: the second and third shapes are the same sum, by the swap `u ↔ v`.
  This is what makes a *single* chain point absorb all three shapes.
* `sTerms_le_chainTerm`: at the chain point `![u,v,v]` the chain monomial is
  `τ(w,u)·τ(u,v)·(χ(u)+τ(u,y))·(χ(v)+τ(v,y))²`, and expanding the square produces
  `τ(w,u)τ(u,v)τ(u,y)χ(v)²` once and `τ(w,u)τ(u,v)τ(v,y)χ(u)χ(v)` twice, i.e. exactly
  `sTerm1 u v + sTerm3 u v + sTerm3 u v` (`key_arith`).
* `chainPt_injective` turns that pointwise comparison into a comparison of sums, and
  `tsum_sTerms_le_chain` concludes `∑_{u,v} (sTerm1 + (sTerm2 + sTerm3)) ≤ freshChainBound π 2 y w`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V]

/-! ## Elementary facts -/

/-- `τ(a,a) = 1`. -/
theorem tau_self_apply (π : Sym2 V → unitInterval) (a : V) : tau π a a = 1 := by
  rw [tau]
  have h : connSet a a = (Set.univ : Set (Config V)) := by
    ext ω
    exact ⟨fun _ => trivial, fun _ => connects_refl ω a⟩
  rw [h, measure_univ]

/-- `1 ≤ χ(a) = ∑_z τ(a,z)`, because the arm may stay at `a`. -/
theorem one_le_hubArmSum (π : Sym2 V → unitInterval) (a : V) : 1 ≤ hubArmSum π a := by
  rw [hubArmSum, ← tau_self_apply π a]
  exact ENNReal.le_tsum a

theorem symm_finTwoArrow_zero (p : V × V) : (finTwoArrowEquiv V).symm p 0 = p.1 := rfl

theorem symm_finTwoArrow_one (p : V × V) : (finTwoArrowEquiv V).symm p 1 = p.2 := by
  simp [finTwoArrowEquiv]

/-- The two labelled arms sum out independently. -/
theorem tsum_fin2_mul (f k : V → ℝ≥0∞) :
    (∑' g : Fin 2 → V, f (g 0) * k (g 1)) = (∑' z, f z) * (∑' z, k z) := by
  have h := Equiv.tsum_eq (finTwoArrowEquiv V).symm
    (fun g : Fin 2 → V => f (g 0) * k (g 1))
  rw [← h]
  simp only [symm_finTwoArrow_zero, symm_finTwoArrow_one]
  rw [ENNReal.tsum_prod']
  rw [show (∑' a : V, ∑' b : V, f a * k b) = ∑' a : V, f a * (∑' b : V, k b) from
    tsum_congr fun a => ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

/-- The canonical form of an iterated sum as a sum over the product. -/
theorem tsum_prod_fst_snd (F : V → V → ℝ≥0∞) :
    (∑' p : V × V, F p.1 p.2) = ∑' u : V, ∑' v : V, F u v := by
  rw [ENNReal.tsum_prod']

/-- The arithmetic content of the absorption step: expanding `(r + s)²` gives `r²` and two copies of
`r·s`, which is `p·r² + (s·(q·r) + s·(q·r))` with the free factors `p`, `q`. -/
theorem key_arith (a p q r s : ℝ≥0∞) :
    a * p * (r * r) + (a * s * (q * r) + a * s * (q * r)) ≤
      a * ((q + p) * ((r + s) * (r + s))) := by
  have hR : a * ((q + p) * ((r + s) * (r + s)))
      = a * (p * ((r + s) * r)) + (a * (q * ((r + s) * r)) +
        (a * (p * ((r + s) * s)) + a * (q * ((r + s) * s)))) := by ring
  rw [hR]
  have hr : r ≤ r + s := self_le_add_right r s
  have hs : s ≤ r + s := self_le_add_left s r
  have b1 : a * p * (r * r) ≤ a * (p * ((r + s) * r)) := by
    have h := mul_le_mul_right (mul_le_mul_left hr r) (a * p)
    simpa [mul_assoc] using h
  have b2 : a * s * (q * r) ≤ a * (q * ((r + s) * r)) := by
    have h1 : s * r ≤ (r + s) * r := mul_le_mul_left hs r
    have h2 := mul_le_mul_right h1 (a * q)
    calc a * s * (q * r) = (a * q) * (s * r) := by ring
      _ ≤ (a * q) * ((r + s) * r) := h2
      _ = a * (q * ((r + s) * r)) := by ring
  have b3 : a * s * (q * r) ≤ a * (q * ((r + s) * s)) := by
    have h1 : r * s ≤ (r + s) * s := mul_le_mul_left hr s
    have h2 := mul_le_mul_right h1 (a * q)
    calc a * s * (q * r) = (a * q) * (r * s) := by ring
      _ ≤ (a * q) * ((r + s) * s) := h2
      _ = a * (q * ((r + s) * s)) := by ring
  refine le_trans (add_le_add b1 (add_le_add b2 b3)) ?_
  exact add_le_add le_rfl (add_le_add le_rfl (self_le_add_left _ _))

/-! ## The fresh event at `q = 2` and the three-terminal diagram -/

/-- At `q = 2` the fresh event implies that both labelled arms and the mark lie in the cluster of
the hub `w`. -/
theorem freshMark_subset_threeTerminal (y w : V) (g : Fin 2 → V) (j : Fin 2) :
    I417Gen.freshMark y g j w ⊆ connSet w (g 0) ∩ connSet w (g 1) ∩ connSet w y := by
  intro ω hω
  obtain ⟨h1, h2⟩ := (mem_hubStar_iff).mp (freshMark_subset_hubStar y w g j hω)
  exact ⟨⟨h2 0, h2 1⟩, connects_symm h1⟩

/-- **The three-terminal tree-graph bound for the fresh event at `q = 2`.** -/
theorem freshMark_measure_le_leafShape (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (g : Fin 2 → V) (j : Fin 2) :
    (edgeMeasure π) (I417Gen.freshMark y g j w) ≤ leafShape π y w g :=
  le_trans (measure_mono (freshMark_subset_threeTerminal y w g j))
    (I417Example.threeLeaf_treeGraph π hπ w y (g 0) (g 1))

/-- The fresh hub event at `q = 2` implies the three-terminal event at `w`. -/
theorem hubStar_subset_threeTerminal (y w : V) (g : Fin 2 → V) :
    hubStar y w g ⊆ connSet w (g 0) ∩ connSet w (g 1) ∩ connSet w y := by
  intro ω hω
  obtain ⟨h1, h2⟩ := (mem_hubStar_iff).mp hω
  exact ⟨⟨h2 0, h2 1⟩, connects_symm h1⟩

/-- **The three-terminal tree-graph bound for the hub event at `q = 2`.** -/
theorem hubStar_measure_le_leafShape (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (g : Fin 2 → V) :
    (edgeMeasure π) (hubStar y w g) ≤ leafShape π y w g :=
  le_trans (measure_mono (hubStar_subset_threeTerminal y w g))
    (I417Example.threeLeaf_treeGraph π hπ w y (g 0) (g 1))

/-! ## Summing the two arms out of each of the three shapes -/

theorem tsum_first_shape (π : Sym2 V → unitInterval) (y w : V) :
    (∑' g : Fin 2 → V, ∑' u : V, ∑' v : V,
        tau π w u * tau π u y * tau π u v * tau π v (g 0) * tau π v (g 1)) =
      ∑' u : V, ∑' v : V, sTerm1 π y w u v := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  have hpull : ∀ g : Fin 2 → V,
      tau π w u * tau π u y * tau π u v * tau π v (g 0) * tau π v (g 1)
        = (tau π w u * tau π u y * tau π u v) * (tau π v (g 0) * tau π v (g 1)) := by
    intro g
    ring
  simp only [hpull]
  rw [ENNReal.tsum_mul_left, tsum_fin2_mul]
  simp only [sTerm1, hubArmSum]

theorem tsum_second_shape (π : Sym2 V → unitInterval) (y w : V) :
    (∑' g : Fin 2 → V, ∑' u : V, ∑' v : V,
        tau π w v * tau π v u * tau π u y * tau π u (g 0) * tau π v (g 1)) =
      ∑' u : V, ∑' v : V, sTerm2 π y w u v := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  have hpull : ∀ g : Fin 2 → V,
      tau π w v * tau π v u * tau π u y * tau π u (g 0) * tau π v (g 1)
        = (tau π w v * tau π v u * tau π u y) * (tau π u (g 0) * tau π v (g 1)) := by
    intro g
    ring
  simp only [hpull]
  rw [ENNReal.tsum_mul_left, tsum_fin2_mul]
  simp only [sTerm2, hubArmSum]

theorem tsum_third_shape (π : Sym2 V → unitInterval) (y w : V) :
    (∑' g : Fin 2 → V, ∑' u : V, ∑' v : V,
        tau π w u * tau π u v * tau π v y * tau π u (g 0) * tau π v (g 1)) =
      ∑' u : V, ∑' v : V, sTerm3 π y w u v := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  have hpull : ∀ g : Fin 2 → V,
      tau π w u * tau π u v * tau π v y * tau π u (g 0) * tau π v (g 1)
        = (tau π w u * tau π u v * tau π v y) * (tau π u (g 0) * tau π v (g 1)) := by
    intro g
    ring
  simp only [hpull]
  rw [ENNReal.tsum_mul_left, tsum_fin2_mul]
  simp only [sTerm3, hubArmSum]

/-- **The summed diagram at `q = 2`**: the three shapes, with the two arms summed out. -/
theorem tsum_leafShape_eq (π : Sym2 V → unitInterval) (y w : V) :
    (∑' g : Fin 2 → V, leafShape π y w g) =
      ∑' u : V, ∑' v : V, (sTerm1 π y w u v + (sTerm2 π y w u v +
        sTerm3 π y w u v)) := by
  have hsplit : (∑' g : Fin 2 → V, leafShape π y w g) =
      (∑' g : Fin 2 → V, ∑' u : V, ∑' v : V,
        tau π w u * tau π u y * tau π u v * tau π v (g 0) * tau π v (g 1)) +
      ((∑' g : Fin 2 → V, ∑' u : V, ∑' v : V,
        tau π w v * tau π v u * tau π u y * tau π u (g 0) * tau π v (g 1)) +
        (∑' g : Fin 2 → V, ∑' u : V, ∑' v : V,
          tau π w u * tau π u v * tau π v y * tau π u (g 0) * tau π v (g 1))) := by
    simp only [leafShape]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, add_assoc]
  rw [hsplit, tsum_first_shape, tsum_second_shape, tsum_third_shape]
  simp only [ENNReal.tsum_add]

/-! ## One chain point absorbs all three shapes -/

/-- The second shape is the third one with the two summed indices exchanged. -/
theorem tsum_sTerm2_eq_sTerm3 (π : Sym2 V → unitInterval) (y w : V) :
    (∑' u : V, ∑' v : V, sTerm2 π y w u v) = ∑' u : V, ∑' v : V, sTerm3 π y w u v := by
  calc (∑' u : V, ∑' v : V, sTerm2 π y w u v)
      = ∑' u : V, ∑' v : V, sTerm3 π y w v u :=
        tsum_congr fun u => tsum_congr fun v => by
          simp only [sTerm2, sTerm3]
          ring
    _ = ∑' v : V, ∑' u : V, sTerm3 π y w v u := ENNReal.tsum_comm
    _ = ∑' u : V, ∑' v : V, sTerm3 π y w u v := rfl

/-- **The absorption inequality.**  At the chain point `![u,v,v]` the chain monomial already carries
`sTerm1 u v` together with two copies of `sTerm3 u v`. -/
theorem sTerms_le_chainTerm (π : Sym2 V → unitInterval) (y w u v : V) :
    sTerm1 π y w u v + (sTerm3 π y w u v + sTerm3 π y w u v) ≤
      chainTerm2 π y w (chainPt u v) := by
  have hkey := key_arith (tau π w u * tau π u v) (tau π u y) (hubArmSum π u)
    (hubArmSum π v) (tau π v y)
  rw [chainTerm2_chainPt, tau_self_apply, mul_one]
  calc sTerm1 π y w u v + (sTerm3 π y w u v + sTerm3 π y w u v)
      = (tau π w u * tau π u v) * tau π u y * (hubArmSum π v * hubArmSum π v) +
        ((tau π w u * tau π u v) * tau π v y * (hubArmSum π u * hubArmSum π v) +
          (tau π w u * tau π u v) * tau π v y * (hubArmSum π u * hubArmSum π v)) := by
        simp only [sTerm1, sTerm3]
        ring
    _ ≤ (tau π w u * tau π u v) *
        ((hubArmSum π u + tau π u y) *
          ((hubArmSum π v + tau π v y) * (hubArmSum π v + tau π v y))) := hkey
    _ = (tau π w u * tau π u v) *
        (((hubArmSum π u + tau π u y) * (hubArmSum π v + tau π v y)) *
          (hubArmSum π v + tau π v y)) := by ring

theorem chainPt_injective : Function.Injective (fun p : V × V => chainPt p.1 p.2) := by
  intro p q h
  have h0 : p.1 = q.1 := congrFun h 0
  have h1 : p.2 = q.2 := congrFun h 1
  exact Prod.ext h0 h1

/-- **The summed fresh diagram is dominated by the chain family at `q = 2`.** -/
theorem tsum_sTerms_le_chain (π : Sym2 V → unitInterval) (y w : V) :
    (∑' u : V, ∑' v : V, (sTerm1 π y w u v + (sTerm2 π y w u v +
        sTerm3 π y w u v))) ≤ freshChainBound π 2 y w := by
  have hswap : (∑' u : V, ∑' v : V, (sTerm1 π y w u v + (sTerm2 π y w u v +
        sTerm3 π y w u v))) =
      ∑' u : V, ∑' v : V, (sTerm1 π y w u v + (sTerm3 π y w u v +
        sTerm3 π y w u v)) := by
    simp only [ENNReal.tsum_add]
    rw [tsum_sTerm2_eq_sTerm3]
  rw [hswap, ← tsum_prod_fst_snd
    (fun u v => sTerm1 π y w u v + (sTerm3 π y w u v + sTerm3 π y w u v)),
    freshChainBound_two_eq]
  refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
    (ENNReal.tsum_comp_le_tsum_of_injective chainPt_injective (chainTerm2 π y w))
  exact sTerms_le_chainTerm π y w p.1 p.2

/-- **The summed three-terminal diagram at `q = 2` is inside the chain family.** -/
theorem tsum_leafShape_le_chain (π : Sym2 V → unitInterval) (y w : V) :
    (∑' g : Fin 2 → V, leafShape π y w g) ≤ freshChainBound π 2 y w :=
  le_trans (le_of_eq (tsum_leafShape_eq π y w)) (tsum_sTerms_le_chain π y w)

/-- **The `q = 2` hub-star diagram sum is inside the chain family.**  This is the form in which a
general-`q` induction would consume the bound: the two fresh arms are summed out without ever
dropping one, and the whole `hubStar` sum is absorbed by `freshCombBound π 2`. -/
theorem tsum_hubStar_le_chain_two (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (y w : V) :
    (∑' g : Fin 2 → V, (edgeMeasure π) (hubStar y w g)) ≤ freshChainBound π 2 y w :=
  le_trans (ENNReal.tsum_le_tsum fun g => hubStar_measure_le_leafShape π hπ y w g)
    (tsum_leafShape_le_chain π y w)

/-- **The exact remaining content of `FreshCombBound`.**  At every `q`, the fresh-side premise
follows from the hub-star diagram bound `HubStarChain π q`; the fresh occurrence `freshMark` is
contained in `hubStar` (production `fresh_factor_le_hubStar`), so nothing but the `q`-arm hub
diagram is left. -/
theorem freshCombBound_of_hubStarChain (π : Sym2 V → unitInterval) {q : ℕ}
    (h : HubStarChain π q) : FreshCombBound π q :=
  fun y w j => le_trans (fresh_factor_le_hubStar π y w j) (h y w)

/-- `HubStarChain` at `q = 2`, unconditionally. -/
theorem hubStarChain_two (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) : HubStarChain π 2 :=
  fun y w => le_trans (tsum_hubStar_le_chain_two π hπ y w)
    (by rw [freshCombBound]; exact self_le_add_right _ _)

/-! ## The fresh side of Lemma I.4.17 at `q = 2` -/

/-- **`FreshCombBound` at `q = 2`, with no hypothesis beyond BK.**  For every countable vertex set
and every `π` with `π e < 1`, the fresh-copy factor at two arms is bounded by the production chain
family `freshCombBound π 2`. -/
theorem freshCombBound_two (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) :
    FreshCombBound π 2 := by
  intro y w j
  refine le_trans (ENNReal.tsum_le_tsum fun g => freshMark_measure_le_leafShape π hπ y w g j)
    (le_trans (tsum_leafShape_le_chain π y w) ?_)
  rw [freshCombBound]
  exact self_le_add_right (freshChainBound π 2 y w) (firstHubBound π 2 y w)

/-! ## Lemma I.4.17 with the fresh side evaluated at `q = 2`

Production `I417Gen.twoCopy_moment_le_marked` reduces the general-`p,q` moment gap to the marked
family `∑_{(j,w)} E[|K_x|^p 1(w ∈ K_x)] · ∑_g P(freshMark y g j w)`.  At `q = 2` the fresh factor is
now known (`freshCombBound_two`), so the gap becomes a base-copy quantity times the production chain
family, with nothing left on the fresh side. -/

/-- **Lemma I.4.17 at `q = 2` with the fresh factor evaluated.**

`E|K_x|^p E|K_y|² ≤ E[1(x ↮ y)|K_x|^p|K_y|²] + ∑_{(j,w)} E[|K_x|^p 1(w ∈ K_x)] · freshCombBound π 2
y w`.

Only BK (`π e < 1`) is used; the sole remaining unevaluated quantity is the base marked moment
`I417Gen.jointPow π x p w = E[|K_x|^p 1(w ∈ K_x)]`. -/
theorem twoCopy_moment_le_marked_two (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) :
    I417A.momentProd π x y p 2 ≤
      I417A.rawDiff π x y p 2 +
        ∑' jw : Fin 2 × V, I417Gen.jointPow π x p jw.2 * freshCombBound π 2 y jw.2 := by
  refine le_trans (I417Gen.twoCopy_moment_le_marked π x y (p := p) (q := 2) (by norm_num)) ?_
  refine add_le_add le_rfl ?_
  exact ENNReal.tsum_le_tsum fun jw =>
    mul_le_mul_right (freshCombBound_two π hπ y jw.2 jw.1) _

/-- **The fresh-side comparison**, used to transfer finiteness to the evaluated family. -/
theorem tsum_marked_fresh_le_two (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (p : ℕ) :
    (∑' jw : Fin 2 × V, I417Gen.jointPow π x p jw.2 *
        (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g jw.1 jw.2))) ≤
      ∑' jw : Fin 2 × V, I417Gen.jointPow π x p jw.2 * freshCombBound π 2 y jw.2 :=
  ENNReal.tsum_le_tsum fun jw =>
    mul_le_mul_right (freshCombBound_two π hπ y jw.2 jw.1) _

/-- **Lemma I.4.17 at `q = 2` in subtractive form, fresh factor evaluated.** -/
theorem moment_gap_tsub_le_marked_two (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) :
    I417A.momentProd π x y p 2 - I417A.rawDiff π x y p 2 ≤
      ∑' jw : Fin 2 × V, I417Gen.jointPow π x p jw.2 * freshCombBound π 2 y jw.2 :=
  le_trans (I417Gen.moment_gap_tsub_le_marked π x y (p := p) (q := 2) (by norm_num))
    (tsum_marked_fresh_le_two π hπ x y p)

/-- **Lemma I.4.17 at `q = 2` in real-valued form, fresh factor evaluated.** -/
theorem moment_gap_le_marked_two_real (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) (hprod : I417A.momentProd π x y p 2 ≠ ⊤)
    (hmark : (∑' jw : Fin 2 × V, I417Gen.jointPow π x p jw.2 * freshCombBound π 2 y jw.2) ≠ ⊤) :
    (I417A.momentProd π x y p 2).toReal - (I417A.rawDiff π x y p 2).toReal ≤
      (∑' jw : Fin 2 × V, I417Gen.jointPow π x p jw.2 * freshCombBound π 2 y jw.2).toReal := by
  have hfresh : (∑' jw : Fin 2 × V, I417Gen.jointPow π x p jw.2 *
      (∑' g : Fin 2 → V, (edgeMeasure π) (I417Gen.freshMark y g jw.1 jw.2))) ≠ ⊤ :=
    ne_top_of_le_ne_top hmark (tsum_marked_fresh_le_two π hπ x y p)
  refine le_trans (I417Gen.moment_gap_le_marked_real π hπ x y (p := p) (q := 2) (by norm_num)
    hprod hfresh) ?_
  exact ENNReal.toReal_mono hmark (tsum_marked_fresh_le_two π hπ x y p)

end PercLib.CriticalLRP.I417Fresh
