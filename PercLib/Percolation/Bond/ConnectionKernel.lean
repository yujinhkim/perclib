/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-85: the connection kernel `τ` is positive semidefinite, with the Cauchy–Schwarz bounds for
the triangle diagram that follow. New for this project; no upstream proof is copied, and no
new definition is introduced: matrix powers of `τ` are written out as sums.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Cylinder
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The connection kernel

Write `T = tau q`, `T²(x,y) = ∑' u, T(x,u) T(u,y)`, `T³(x,y) = ∑' u v, T(x,u) T(u,v) T(v,y)`
and `Δₓ = T³(x,x)` (the triangle diagram at `x`).

* `sum_mul_tau_eq_integral` and `sum_mul_tau_nonneg` (70KD): for every finite family
  `a`, `∑ᵢⱼ aᵢ aⱼ T(xᵢ,xⱼ) = E[∑_C (∑_{xᵢ ∈ C} aᵢ)²] ≥ 0`, the sum over the open clusters
  `C`; `posSemidef_tau` states that every finite (principal) submatrix of `T` is positive
  semidefinite.
* `triangle_sq_le` and `triangle_le_rpow` (UZ7J): `T³(x,y)² ≤ Δₓ Δ_y`, so
  `T³(x,y) ≤ (Δₓ Δ_y)^{1/2}`; and `tsum_tau_sq_le_triangle`: `∑' u, T(x,u)² ≤ Δₓ`.
* `triangle_weighted_le` (C2YT): with `D = ⨆ x, Δₓ`,
  `∑' v, T(o,v) T²(o,v) T³(o,v) ≤ D Δₒ ≤ D²`, finite when `D < ⊤`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### A finite Gram identity -/

/-- Grouping a quadratic form with a block indicator by blocks. -/
theorem sum_sum_mul_ite_eq_sum_sq {ι κ : Type*} [Fintype ι] [DecidableEq κ] (c : ι → κ)
    (a : ι → ℝ) :
    ∑ i, ∑ j, a i * a j * (if c i = c j then 1 else 0) =
      ∑ k ∈ univ.image c, (∑ i ∈ univ.filter (fun i => c i = k), a i) ^ 2 := by
  have h1 : ∀ i, ∑ j, a i * a j * (if c i = c j then (1 : ℝ) else 0) =
      a i * ∑ j ∈ univ.filter (fun j => c j = c i), a j := by
    intro i
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : c i = c j
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [h1]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image c) (g := c)
    (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

/-- Pointwise, the connection indicator quadratic form is the sum over open clusters of the
squared cluster masses. -/
theorem sum_mul_indicator_conn_eq_tsum (ω : Config V) {ι : Type*} [Fintype ι] (f : ι → V)
    (a : ι → ℝ) :
    ∑ i, ∑ j, a i * a j * (conn (f i) (f j)).indicator (fun _ => (1 : ℝ)) ω =
      ∑' C : (openGraph ω).ConnectedComponent,
        (∑ i ∈ univ.filter (fun i => (openGraph ω).connectedComponentMk (f i) = C), a i) ^ 2 := by
  classical
  set c : ι → (openGraph ω).ConnectedComponent := fun i => (openGraph ω).connectedComponentMk (f i)
  have hind : ∀ i j, (conn (f i) (f j)).indicator (fun _ => (1 : ℝ)) ω =
      if c i = c j then 1 else 0 := by
    intro i j
    rw [Set.indicator_apply]
    congr 1
    exact propext (SimpleGraph.ConnectedComponent.eq).symm
  simp_rw [hind]
  rw [sum_sum_mul_ite_eq_sum_sq c a, tsum_eq_sum (s := univ.image c)]
  intro C hC
  have hne : ∀ i, (openGraph ω).connectedComponentMk (f i) ≠ C := fun i hi =>
    hC (hi ▸ Finset.mem_image_of_mem c (Finset.mem_univ i))
  simp [hne]

theorem sum_mul_indicator_conn_nonneg (ω : Config V) {ι : Type*} [Fintype ι] (f : ι → V)
    (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * (conn (f i) (f j)).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  set c : ι → (openGraph ω).ConnectedComponent := fun i => (openGraph ω).connectedComponentMk (f i)
  have hind : ∀ i j, (conn (f i) (f j)).indicator (fun _ => (1 : ℝ)) ω =
      if c i = c j then 1 else 0 := by
    intro i j
    rw [Set.indicator_apply]
    congr 1
    exact propext (SimpleGraph.ConnectedComponent.eq).symm
  simp_rw [hind]
  rw [sum_sum_mul_ite_eq_sum_sq c a]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-! ### Positive semidefiniteness (70KD) -/

theorem sum_mul_tau_eq_integral_indicator [Countable V] (q : Sym2 V → unitInterval)
    {ι : Type*} [Fintype ι] (f : ι → V) (a : ι → ℝ) :
    ∑ i, ∑ j, a i * a j * (tau q (f i) (f j)).toReal =
      ∫ ω, ∑ i, ∑ j, a i * a j * (conn (f i) (f j)).indicator (fun _ => (1 : ℝ)) ω ∂law q := by
  have hint : ∀ i j, Integrable (fun ω => a i * a j *
      (conn (f i) (f j)).indicator (fun _ => (1 : ℝ)) ω) (law q) := fun i j =>
    ((integrable_const (1 : ℝ)).indicator (measurableSet_conn (f i) (f j))).const_mul _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_indicator_const (1 : ℝ) (measurableSet_conn (f i) (f j)),
    smul_eq_mul, mul_one, measureReal_def]
  rfl

/-- **70KD**, identity. For a finite family of vertices `f i` and real weights `a i`,
`∑ᵢⱼ aᵢ aⱼ T(f i, f j) = E[∑_C (∑_{f i ∈ C} aᵢ)²]`, the sum over the open clusters `C`. -/
theorem sum_mul_tau_eq_integral [Countable V] (q : Sym2 V → unitInterval)
    {ι : Type*} [Fintype ι] (f : ι → V) (a : ι → ℝ) :
    ∑ i, ∑ j, a i * a j * (tau q (f i) (f j)).toReal =
      ∫ ω, ∑' C : (openGraph ω).ConnectedComponent,
        (∑ i ∈ univ.filter (fun i => (openGraph ω).connectedComponentMk (f i) = C), a i) ^ 2
        ∂law q := by
  classical
  rw [sum_mul_tau_eq_integral_indicator]
  congr 1
  funext ω
  convert sum_mul_indicator_conn_eq_tsum ω f a

/-- **70KD**, nonnegativity. -/
theorem sum_mul_tau_nonneg [Countable V] (q : Sym2 V → unitInterval)
    {ι : Type*} [Fintype ι] (f : ι → V) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * (tau q (f i) (f j)).toReal := by
  rw [sum_mul_tau_eq_integral_indicator]
  exact integral_nonneg fun ω => sum_mul_indicator_conn_nonneg ω f a

/-- **70KD**, matrix form: every finite submatrix `(T(f i, f j))ᵢⱼ` of the connection kernel
is positive semidefinite. With `f` injective (e.g. `Subtype.val` on a finset) these are the
principal submatrices. -/
theorem posSemidef_tau [Countable V] (q : Sym2 V → unitInterval)
    {ι : Type*} [Fintype ι] (f : ι → V) :
    (Matrix.of fun i j => (tau q (f i) (f j)).toReal).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, tau_comm]
  · have h := sum_mul_tau_nonneg q f x
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    convert h using 2 with i _
    exact Finset.sum_congr rfl fun j _ => by ring

/-- Finset form of 70KD nonnegativity, for a real family on vertices. -/
theorem sum_finset_mul_tau_nonneg [Countable V] (q : Sym2 V → unitInterval) (F : Finset V)
    (a : V → ℝ) :
    0 ≤ ∑ u ∈ F, ∑ v ∈ F, a u * a v * (tau q u v).toReal := by
  have h := sum_mul_tau_nonneg q (fun u : F => (u : V)) (fun u => a u)
  rw [← Finset.sum_coe_sort F]
  convert h using 2 with u
  rw [← Finset.sum_coe_sort F]

/-! ### Cauchy–Schwarz for the triangle (UZ7J) -/

/-- Cauchy–Schwarz for the finite truncations of the kernel, in real numbers. -/
theorem sum_tau_cauchySchwarz [Countable V] (q : Sym2 V → unitInterval) (F : Finset V)
    (α β : V → ℝ) :
    (∑ u ∈ F, ∑ v ∈ F, α u * β v * (tau q u v).toReal) ^ 2 ≤
      (∑ u ∈ F, ∑ v ∈ F, α u * α v * (tau q u v).toReal) *
        (∑ u ∈ F, ∑ v ∈ F, β u * β v * (tau q u v).toReal) := by
  set A := ∑ u ∈ F, ∑ v ∈ F, α u * α v * (tau q u v).toReal
  set B := ∑ u ∈ F, ∑ v ∈ F, α u * β v * (tau q u v).toReal
  set C := ∑ u ∈ F, ∑ v ∈ F, β u * β v * (tau q u v).toReal
  have hswap : ∑ u ∈ F, ∑ v ∈ F, β u * α v * (tau q u v).toReal = B := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [tau_comm q v u]
    ring
  have hq : ∀ s : ℝ, 0 ≤ C * (s * s) + 2 * B * s + A := by
    intro s
    have h := sum_finset_mul_tau_nonneg q F (fun u => α u + s * β u)
    have hexp : ∀ u v, (α u + s * β u) * (α v + s * β v) * (tau q u v).toReal =
        α u * α v * (tau q u v).toReal + s * (α u * β v * (tau q u v).toReal) +
          s * (β u * α v * (tau q u v).toReal) +
          s * s * (β u * β v * (tau q u v).toReal) := fun u v => by ring
    simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hswap] at h
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

private theorem tau_ne_top (q : Sym2 V → unitInterval) (x y : V) : tau q x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q x y)

/-- A finite truncation of the triangle sum, as the real truncation. -/
private theorem sum_triangle_eq_ofReal (q : Sym2 V → unitInterval) (F : Finset V) (x y : V) :
    ∑ u ∈ F, ∑ v ∈ F, tau q x u * tau q u v * tau q v y =
      ENNReal.ofReal (∑ u ∈ F, ∑ v ∈ F,
        (tau q x u).toReal * (tau q v y).toReal * (tau q u v).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun u _ => Finset.sum_nonneg fun v _ => by positivity]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal (tau_ne_top q x u), ENNReal.ofReal_toReal (tau_ne_top q v y),
    ENNReal.ofReal_toReal (tau_ne_top q u v)]
  ring

private theorem sum_triangle_le_tsum (q : Sym2 V → unitInterval) (F : Finset V) (x y : V) :
    ∑ u ∈ F, ∑ v ∈ F, tau q x u * tau q u v * tau q v y ≤
      ∑' u, ∑' v, tau q x u * tau q u v * tau q v y :=
  (Finset.sum_le_sum fun _ _ => ENNReal.sum_le_tsum F).trans (ENNReal.sum_le_tsum F)

/-- Finite truncations of `T³(x,y)` obey Cauchy–Schwarz against `Δₓ Δ_y`. -/
private theorem sum_triangle_sq_le [Countable V] (q : Sym2 V → unitInterval) (F : Finset V)
    (x y : V) :
    (∑ u ∈ F, ∑ v ∈ F, tau q x u * tau q u v * tau q v y) ^ 2 ≤
      (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) *
        ∑' u, ∑' v, tau q y u * tau q u v * tau q v y := by
  have hcs := sum_tau_cauchySchwarz q F (fun u => (tau q x u).toReal) (fun v => (tau q v y).toReal)
  have hxx := sum_triangle_eq_ofReal q F x x
  have hyy := sum_triangle_eq_ofReal q F y y
  have hsym : ∀ a b, (tau q a b).toReal = (tau q b a).toReal := fun a b => by rw [tau_comm]
  rw [sum_triangle_eq_ofReal, ← ENNReal.ofReal_pow (Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ => by positivity)]
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal _ := ENNReal.ofReal_le_ofReal hcs
    _ = (∑ u ∈ F, ∑ v ∈ F, tau q x u * tau q u v * tau q v x) *
          ∑ u ∈ F, ∑ v ∈ F, tau q y u * tau q u v * tau q v y := by
        rw [hxx, hyy, ← ENNReal.ofReal_mul (Finset.sum_nonneg fun u _ =>
          Finset.sum_nonneg fun v _ => by positivity)]
        congr 2
        · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [hsym v x]
        · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [hsym y u]
    _ ≤ _ := mul_le_mul' (sum_triangle_le_tsum q F x x) (sum_triangle_le_tsum q F y y)

/-- **UZ7J**, square-root form: `T³(x,y) ≤ (Δₓ Δ_y)^{1/2}`. No finiteness hypothesis is
needed. -/
theorem triangle_le_rpow [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    ∑' u, ∑' v, tau q x u * tau q u v * tau q v y ≤
      ((∑' u, ∑' v, tau q x u * tau q u v * tau q v x) *
        ∑' u, ∑' v, tau q y u * tau q u v * tau q v y) ^ (1 / 2 : ℝ) := by
  set D := (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) *
    ∑' u, ∑' v, tau q y u * tau q u v * tau q v y
  have hroot : ∀ z : ℝ≥0∞, z ^ 2 ≤ D → z ≤ D ^ (1 / 2 : ℝ) := by
    intro z hz
    have h := ENNReal.rpow_le_rpow hz (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have he : (z ^ 2) ^ (1 / 2 : ℝ) = z := by
      have := ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) z
      simpa [one_div] using this
    rwa [he] at h
  rw [← ENNReal.tsum_prod]
  refine ENNReal.summable.tsum_le_of_sum_le fun s => hroot _ ?_
  set F : Finset V := s.image Prod.fst ∪ s.image Prod.snd
  have hsub : s ⊆ F ×ˢ F := fun p hp => Finset.mem_product.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  have hle : ∑ p ∈ s, tau q x p.1 * tau q p.1 p.2 * tau q p.2 y ≤
      ∑ u ∈ F, ∑ v ∈ F, tau q x u * tau q u v * tau q v y :=
    (Finset.sum_le_sum_of_subset hsub).trans_eq (Finset.sum_product F F
      (fun p : V × V => tau q x p.1 * tau q p.1 p.2 * tau q p.2 y))
  exact (pow_le_pow_left₀ bot_le hle 2).trans (sum_triangle_sq_le q F x y)

/-- **UZ7J**, squared form: `T³(x,y)² ≤ Δₓ Δ_y`. -/
theorem triangle_sq_le [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    (∑' u, ∑' v, tau q x u * tau q u v * tau q v y) ^ 2 ≤
      (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) *
        ∑' u, ∑' v, tau q y u * tau q u v * tau q v y := by
  have h := pow_le_pow_left₀ bot_le (triangle_le_rpow q x y) 2
  refine h.trans_eq ?_
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **UZ7J**, as stated with finite triangles: if `Δₓ, Δ_y < ⊤` then
`T³(x,y) ≤ √(Δₓ Δ_y)` (real square root of the finite product). -/
theorem triangle_le_sqrt [Countable V] (q : Sym2 V → unitInterval) (x y : V)
    (hx : ∑' u, ∑' v, tau q x u * tau q u v * tau q v x < ⊤)
    (hy : ∑' u, ∑' v, tau q y u * tau q u v * tau q v y < ⊤) :
    ∑' u, ∑' v, tau q x u * tau q u v * tau q v y ≤
      ENNReal.ofReal (Real.sqrt ((∑' u, ∑' v, tau q x u * tau q u v * tau q v x).toReal *
        (∑' u, ∑' v, tau q y u * tau q u v * tau q v y).toReal)) := by
  refine (triangle_le_rpow q x y).trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, ← ENNReal.toReal_mul,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top hx.ne hy.ne)]

/-- **UZ7J**, diagonal bound: `∑' u, T(x,u)² ≤ Δₓ`. -/
theorem tsum_tau_sq_le_triangle (q : Sym2 V → unitInterval) (x : V) :
    ∑' u, tau q x u ^ 2 ≤ ∑' u, ∑' v, tau q x u * tau q u v * tau q v x := by
  refine ENNReal.tsum_le_tsum fun u => ?_
  calc tau q x u ^ 2 = tau q x u * tau q u u * tau q u x := by
        rw [tau_self, mul_one, tau_comm q u x, sq]
    _ ≤ ∑' v, tau q x u * tau q u v * tau q v x :=
        ENNReal.le_tsum (f := fun v => tau q x u * tau q u v * tau q v x) u

/-! ### The weighted triangle (C2YT) -/

/-- `Δₒ` regrouped as `∑' v, T(o,v) T²(o,v)`. -/
theorem triangle_eq_tsum_tau_mul (q : Sym2 V → unitInterval) (o : V) :
    ∑' u, ∑' v, tau q o u * tau q u v * tau q v o =
      ∑' v, tau q o v * ∑' u, tau q o u * tau q u v := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun u => ?_
  rw [tau_comm q v o]
  ring

/-- **C2YT.** With `D = ⨆ x, Δₓ`: `∑' v, T(o,v) T²(o,v) T³(o,v) ≤ D Δₒ ≤ D²`. -/
theorem triangle_weighted_le [Countable V] (q : Sym2 V → unitInterval) (o : V) :
    ∑' v, tau q o v * (∑' u, tau q o u * tau q u v) *
        (∑' u, ∑' w, tau q o u * tau q u w * tau q w v) ≤
      (⨆ x, ∑' u, ∑' v, tau q x u * tau q u v * tau q v x) *
        ∑' u, ∑' v, tau q o u * tau q u v * tau q v o ∧
    (⨆ x, ∑' u, ∑' v, tau q x u * tau q u v * tau q v x) *
        ∑' u, ∑' v, tau q o u * tau q u v * tau q v o ≤
      (⨆ x, ∑' u, ∑' v, tau q x u * tau q u v * tau q v x) ^ 2 := by
  set Δ : V → ℝ≥0∞ := fun x => ∑' u, ∑' v, tau q x u * tau q u v * tau q v x with hΔ
  set D := ⨆ x, Δ x
  have hΔD : ∀ x, Δ x ≤ D := fun x => le_iSup Δ x
  have hT3 : ∀ v, ∑' u, ∑' w, tau q o u * tau q u w * tau q w v ≤ D := by
    intro v
    have hDD : (D * D) ^ (1 / 2 : ℝ) = D := by
      have := ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) D
      simpa [one_div, sq] using this
    calc _ ≤ (Δ o * Δ v) ^ (1 / 2 : ℝ) := triangle_le_rpow q o v
      _ ≤ (D * D) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (mul_le_mul' (hΔD o) (hΔD v)) (by norm_num)
      _ = D := hDD
  constructor
  · calc _ ≤ ∑' v, tau q o v * (∑' u, tau q o u * tau q u v) * D :=
          ENNReal.tsum_le_tsum fun v => mul_le_mul' le_rfl (hT3 v)
      _ = D * Δ o := by
          rw [ENNReal.tsum_mul_right, mul_comm]
          congr 1
          exact (triangle_eq_tsum_tau_mul q o).symm
  · rw [sq]
    exact mul_le_mul' le_rfl (hΔD o)

/-- **C2YT**, finiteness: if `D < ⊤` then the weighted triangle is finite. -/
theorem triangle_weighted_lt_top [Countable V] (q : Sym2 V → unitInterval) (o : V)
    (hD : (⨆ x, ∑' u, ∑' v, tau q x u * tau q u v * tau q v x) < ⊤) :
    ∑' v, tau q o v * (∑' u, tau q o u * tau q u v) *
        (∑' u, ∑' w, tau q o u * tau q u w * tau q w v) < ⊤ := by
  have h := triangle_weighted_le q o
  exact (h.1.trans h.2).trans_lt (ENNReal.pow_lt_top hD)

/-! ### Non-vacuity witness (D-5) -/

private theorem tau_bool_half :
    tau (fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) false true =
      1 / 2 := by
  have hset : conn (V := Bool) false true = {ω | s(false, true) ∈ ω} := by
    ext ω
    constructor
    · rintro ⟨w⟩
      cases w with
      | @cons _ x _ hadj _ =>
        obtain ⟨he, hne⟩ := (openGraph_adj_iff ω false x).mp hadj
        cases x
        · exact absurd rfl hne
        · exact he
    · intro h
      exact mem_conn_of_mem (by decide) h
  rw [tau, hset, law, PercLib.Probability.prodBernoulli_setOf_mem]
  refine (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr ?_
  norm_cast
  apply NNReal.eq
  rw [NNReal.coe_mul]
  change (2 : ℝ) * (1 / 2) = 1
  norm_num

/-- The two-vertex model with `q = 1/2`: the `2 × 2` connection matrix is
`[[1, 1/2], [1/2, 1]]`, and it is positive semidefinite. -/
example :
    (Matrix.of fun i j : Bool =>
      (tau (fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) i j).toReal) =
      Matrix.of (fun i j : Bool => if i = j then (1 : ℝ) else 1 / 2) ∧
    (Matrix.of fun i j : Bool =>
      (tau (fun _ : Sym2 Bool => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)) i j).toReal).PosSemidef := by
  refine ⟨?_, posSemidef_tau _ id⟩
  ext i j
  simp only [Matrix.of_apply]
  cases i <;> cases j
  · simp [tau_self]
  · rw [tau_bool_half]; norm_num
  · rw [tau_comm, tau_bool_half]; norm_num
  · simp [tau_self]

end PercLib.Percolation.Bond
