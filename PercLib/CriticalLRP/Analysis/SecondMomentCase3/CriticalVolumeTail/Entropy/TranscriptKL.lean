/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Fibre factorisation and the relative-entropy chain rule for a finite transcript

Source: T. Hutchcroft, *On the derivation of mean-field percolation critical exponents
from the triangle condition* (arXiv:2106.06400), Section 3: Theorem 3.1
(`Generalised Dewan–Muirhead`), its proof, and Lemma 3.3.

The proof of Theorem 3.1 compares, for a fixed decision tree `T`, the law of the observed bit
sequence under two intensities and applies the relative-entropy chain rule with the expectation
taken over the **lower** intensity.  This file formalises the underlying finite combinatorics
for a query plan on a finite weighted edge set, with the model's own product Bernoulli mass
`LRP.evProb`:

* `ans σ ω n` is the answer path of the first `n` queries of the plan `σ` against `ω`, and
  `pre_ans` records the source's `T_n(ω) = S_n[(T_i, ω(T_i))_{i<n}]`: the prefix of the answer
  path is the answer path of the same run;
* `Fresh σ n` is the fresh-query hypothesis at transcript depth `n` (never repeat an edge among
  the first `n` queries along any path); `example_fresh` shows it is satisfiable;
* `fibre_eq_cylinder` and `fibre_mass`: an answer-path fibre is exactly a cylinder of the
  finite product measure, and its mass is the path weight `prefMass` — configuration/cylinder
  probabilities are recovered from the transcript;
* `sum_fibre_mass`, `klPath_eq_fibre_kl`: the fibres form a probability law, and the transcript
  divergence `klPath` is the relative entropy computed from the fibre masses;
* `prefMass_div`, `prefMass_lower`: the exact two-intensity mass ratio of a fibre in exponential
  closed-weight form, and its one-sided likelihood-ratio bound;
* `prefMass_sum`, `klPath_succ`, `klPath_eq_sum`: the transcript law is normalised and the
  relative entropy satisfies the chain rule, step by step and in closed form, with the outer
  expectation over the lower intensity;
* `sum_rev`, `sum_step_weight`: the revealment weights `rev` partition the `n` queries;
* `kl_le`, `kl_le_openProb`: the source's bound `((β₂-β₁)²/(2β₁)) ∑_e J_e Rev_{β₁}(e)`, with the
  per-edge exponential estimate of [2106.06400, Lemma 3.3] as an explicit hypothesis, and
  `klPath_nonneg` showing the transcript divergence is a genuine relative entropy.

Everything is a finite sum identity over `E → Bool` and `Fin n → Bool`; no measure theory, no
`sorry`, no extra axioms.  Nothing here is asserted about the infinite-volume model: the
passage from these finite statements to the canonical long-range model is not formalised, and
the per-edge estimate (Lemma 3.3) is not proved here but named in `kl_le`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Entropy.Pinsker

/-!
# Fibre factorisation and the transcript relative-entropy chain rule
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open Finset

namespace LRP

/-! ## Query plans, answer paths, and the edges queried along a path -/

/-- A query plan on the edge type `E`: the edge queried after the first `n` answers.  This is
the halting-free form of the decision trees of [2106.06400, Section 3]; a halting tree of
depth at most `n` is extended to a plan of depth `n` by querying further edges, which only
enlarges the transcript. -/
def QueryPlan (E : Type*) := (n : ℕ) → (Fin n → Bool) → E

section NoInst

variable {E : Type*}

/-- The answers of the first `n` queries of the plan against the configuration `ω`. -/
def ans (σ : QueryPlan E) (ω : E → Bool) : (n : ℕ) → (Fin n → Bool)
  | 0 => fun i => i.elim0
  | n + 1 => Fin.snoc (ans σ ω n) (ω (σ n (ans σ ω n)))

theorem ans_zero (σ : QueryPlan E) (ω : E → Bool) : ans σ ω 0 = fun i => i.elim0 := rfl

theorem ans_succ (σ : QueryPlan E) (ω : E → Bool) (n : ℕ) :
    ans σ ω (n + 1) = Fin.snoc (ans σ ω n) (ω (σ n (ans σ ω n))) := rfl

theorem init_ans_succ (σ : QueryPlan E) (ω : E → Bool) (n : ℕ) :
    Fin.init (ans σ ω (n + 1)) = ans σ ω n := by
  rw [ans_succ, Fin.init_snoc]

theorem last_ans_succ (σ : QueryPlan E) (ω : E → Bool) (n : ℕ) :
    ans σ ω (n + 1) (Fin.last n) = ω (σ n (ans σ ω n)) := by
  rw [ans_succ, Fin.snoc_last]

/-- The first `j.val` answers of the answer path `y`. -/
def pre {n : ℕ} (y : Fin n → Bool) (j : Fin n) : Fin j.val → Bool :=
  fun i => y ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩

theorem pre_castSucc {n : ℕ} (x : Fin (n + 1) → Bool) (j : Fin n) :
    pre x j.castSucc = pre (Fin.init x) j := by
  funext i
  simp only [pre, Fin.init]
  exact congrArg x (Fin.ext (by simp))

theorem pre_pre {n : ℕ} (x : Fin n → Bool) (j : Fin n) (i : Fin j.val) :
    pre (pre x j) i = pre x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ := by
  funext k
  simp only [pre]

theorem pre_last {n : ℕ} (x : Fin (n + 1) → Bool) : pre x (Fin.last n) = Fin.init x := by
  funext i
  simp only [pre, Fin.init]
  exact congrArg x (Fin.ext (by simp))

/-- The edge queried at step `j` along the answer path `x`. -/
def qe {n : ℕ} (σ : QueryPlan E) (x : Fin n → Bool) (j : Fin n) : E :=
  σ j.val (pre x j)

theorem qe_castSucc {n : ℕ} (σ : QueryPlan E) (x : Fin (n + 1) → Bool) (j : Fin n) :
    qe σ x j.castSucc = qe σ (Fin.init x) j := by
  simp only [qe, Fin.val_castSucc, pre_castSucc]

theorem qe_last {n : ℕ} (σ : QueryPlan E) (x : Fin (n + 1) → Bool) :
    qe σ x (Fin.last n) = σ n (Fin.init x) := by
  simp only [qe, Fin.val_last, pre_last]

theorem qe_pre {n : ℕ} (σ : QueryPlan E) (x : Fin n → Bool) (j : Fin n) (i : Fin j.val) :
    qe σ (pre x j) i = qe σ x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ := by
  simp only [qe, pre_pre]

/-- **Fresh queries up to depth `N`.**  Along every answer path the plan never repeats an
edge among its first `N` queries.  (`N` is the depth of the transcript considered; a plan on a
finite edge set cannot be fresh at every depth, so the depth is part of the hypothesis.) -/
def Fresh (σ : QueryPlan E) (N : ℕ) : Prop :=
  ∀ (n : ℕ), n < N → ∀ (y : Fin n → Bool) (j : Fin n), σ n y ≠ qe σ y j

theorem qe_inj {σ : QueryPlan E} {N : ℕ} (hσ : Fresh σ N) {n : ℕ} (hn : n ≤ N)
    (x : Fin n → Bool) :
    ∀ j j' : Fin n, qe σ x j = qe σ x j' → j = j' := by
  intro j j' he
  rcases lt_trichotomy j j' with h | h | h
  · exfalso
    have hcon := hσ j'.val (lt_of_lt_of_le j'.isLt hn) (pre x j') ⟨j.val, h⟩
    have h1 : qe σ (pre x j') ⟨j.val, h⟩ = qe σ x j := qe_pre σ x j' ⟨j.val, h⟩
    rw [h1] at hcon
    exact hcon he.symm
  · exact h
  · exfalso
    have hcon := hσ j.val (lt_of_lt_of_le j.isLt hn) (pre x j) ⟨j'.val, h⟩
    have h1 : qe σ (pre x j) ⟨j'.val, h⟩ = qe σ x j' := qe_pre σ x j ⟨j'.val, h⟩
    rw [h1] at hcon
    exact hcon he

theorem Fresh.mono {σ : QueryPlan E} {m N : ℕ} (h : Fresh σ N) (hm : m ≤ N) : Fresh σ m :=
  fun n hn => h n (lt_of_lt_of_le hn hm)

theorem qe_injOn {σ : QueryPlan E} {n : ℕ} (hσ : Fresh σ n) (x : Fin n → Bool) :
    Set.InjOn (qe σ x) ↑(univ : Finset (Fin n)) := by
  intro j _ j' _ h
  exact qe_inj hσ le_rfl x j j' h

/-- **An answer path is determined by its own revealed bits.** -/
theorem ans_iff (σ : QueryPlan E) {n : ℕ} (x : Fin n → Bool) (ω : E → Bool) :
    ans σ ω n = x ↔ ∀ j : Fin n, ω (qe σ x j) = x j := by
  induction n with
  | zero =>
    constructor
    · intro _ j
      exact j.elim0
    · intro _
      funext i
      exact i.elim0
  | succ n ih =>
    constructor
    · intro h j
      have hinit : ans σ ω n = Fin.init x := by
        rw [← init_ans_succ σ ω n, h]
      cases j using Fin.lastCases with
      | last => rw [qe_last, ← hinit, ← last_ans_succ σ ω n, h]
      | cast j' =>
        rw [qe_castSucc]
        exact (ih (Fin.init x)).1 hinit j'
    · intro h
      have hinit : ∀ j : Fin n, ω (qe σ (Fin.init x) j) = (Fin.init x) j := by
        intro j
        have hh := h j.castSucc
        rwa [qe_castSucc] at hh
      have hlast : ω (σ n (Fin.init x)) = x (Fin.last n) := by
        have hh := h (Fin.last n)
        rwa [qe_last] at hh
      rw [ans_succ, (ih (Fin.init x)).2 hinit, hlast, Fin.snoc_init_self]

/-- **The weight of a bit path**: the product of the one-edge Bernoulli weights along the
edges the plan queries. -/
noncomputable def prefMass (J : E → ℝ) (β : ℝ) (σ : QueryPlan E) (n : ℕ)
    (x : Fin n → Bool) : ℝ :=
  ∏ j : Fin n, bem J β (qe σ x j) (x j)

theorem prefMass_zero (J : E → ℝ) (β : ℝ) {σ : QueryPlan E} (x : Fin 0 → Bool) :
    prefMass J β σ 0 x = 1 := by
  simp [prefMass]

theorem prefMass_snoc (J : E → ℝ) (β : ℝ) {σ : QueryPlan E} {n : ℕ}
    (y : Fin n → Bool) (v : Bool) :
    prefMass J β σ (n + 1) (Fin.snoc y v) = prefMass J β σ n y * bem J β (σ n y) v := by
  rw [prefMass, Fin.prod_univ_castSucc]
  have h1 : ∀ j : Fin n, qe σ (Fin.snoc y v) j.castSucc = qe σ y j := by
    intro j
    rw [qe_castSucc, Fin.init_snoc]
  have h2 : ∀ j : Fin n, (Fin.snoc y v : Fin (n + 1) → Bool) j.castSucc = y j := by
    intro j
    simp
  have h3 : qe σ (Fin.snoc y v) (Fin.last n) = σ n y := by
    rw [qe_last, Fin.init_snoc]
  have h4 : (Fin.snoc y v : Fin (n + 1) → Bool) (Fin.last n) = v := Fin.snoc_last ..
  simp only [h1, h2, h3, h4, prefMass]

/-- Splitting a path at its last answer. -/
def snocEquiv (n : ℕ) : ((Fin n → Bool) × Bool) ≃ (Fin (n + 1) → Bool) where
  toFun p := Fin.snoc (α := fun _ => Bool) p.1 p.2
  invFun x := (Fin.init x, x (Fin.last n))
  left_inv p := by
    refine Prod.ext ?_ ?_
    · change Fin.init (Fin.snoc (α := fun _ => Bool) p.1 p.2) = p.1
      exact Fin.init_snoc (α := fun _ => Bool) p.2 p.1
    · change Fin.snoc (α := fun _ => Bool) p.1 p.2 (Fin.last n) = p.2
      exact Fin.snoc_last (α := fun _ => Bool) p.2 p.1
  right_inv x := by
    change Fin.snoc (α := fun _ => Bool) (Fin.init x) (x (Fin.last n)) = x
    exact Fin.snoc_init_self (α := fun _ => Bool) (q := x)

/-- **Splitting a sum over paths at the last answer.** -/
theorem sum_snoc (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x : Fin (n + 1) → Bool, f x = ∑ y : Fin n → Bool, ∑ v : Bool, f (Fin.snoc y v) := by
  classical
  rw [← Fintype.sum_equiv (snocEquiv n)
    (fun p : (Fin n → Bool) × Bool => f (Fin.snoc (α := fun _ => Bool) p.1 p.2)) f
    (fun p => rfl),
    Fintype.sum_prod_type]

/-- At every edge the two Bernoulli weights sum to one. -/
theorem bem_sum (J : E → ℝ) (β : ℝ) (e : E) : ∑ v : Bool, bem J β e v = 1 := by
  rw [Fintype.sum_bool, bem_true_add_false]

/-- **The transcript law is a probability measure**: the weights of the `n`-step answer paths
sum to one. -/
theorem prefMass_sum (J : E → ℝ) (β : ℝ) (σ : QueryPlan E) (n : ℕ) :
    ∑ x : Fin n → Bool, prefMass J β σ n x = 1 := by
  induction n with
  | zero => simp [prefMass]
  | succ n ih =>
    rw [sum_snoc (n := n)]
    have hpt : ∀ y : Fin n → Bool,
        (∑ v : Bool, prefMass J β σ (n + 1) (Fin.snoc y v)) = prefMass J β σ n y := by
      intro y
      rw [Finset.sum_congr rfl fun v _ => prefMass_snoc J β y v, ← Finset.mul_sum, bem_sum,
        mul_one]
    rw [Finset.sum_congr rfl fun y _ => hpt y, ih]

theorem prefMass_pos {J : E → ℝ} {β : ℝ} {σ : QueryPlan E} (hJ : ∀ e, 0 < J e)
    (hβ : 0 < β) (n : ℕ) (x : Fin n → Bool) : 0 < prefMass J β σ n x :=
  prod_pos fun _ _ => bem_pos hJ hβ _ _

/-- The per-edge binary divergence, written as the sum over the two values of the bit. -/
theorem sum_bem_bkl (J : E → ℝ) (β₁ β₂ : ℝ) (e : E) :
    (∑ v : Bool, bem J β₁ e v * Real.log (bem J β₁ e v / bem J β₂ e v))
      = bkl (bem J β₁ e true) (bem J β₂ e true) := by
  rw [Fintype.sum_bool]
  simp only [bem, Bool.false_eq_true, ite_false, ite_true, bkl]

end NoInst

section Inst

variable {E : Type*} [DecidableEq E] {σ : QueryPlan E}

/-- The edges queried in the first `n` steps along the answer path `x`. -/
noncomputable def queried (σ : QueryPlan E) {n : ℕ} (x : Fin n → Bool) : Finset E :=
  univ.image (qe σ x)

theorem mem_queried {n : ℕ} {x : Fin n → Bool} {e : E} :
    e ∈ queried σ x ↔ ∃ j : Fin n, qe σ x j = e := by
  simp [queried]

/-- The answer bits recorded along the path `x`. -/
noncomputable def bits {n : ℕ} (σ : QueryPlan E) (x : Fin n → Bool) (e : E) : Bool :=
  if h : ∃ j : Fin n, qe σ x j = e then x (Classical.choose h) else false

theorem bits_qe {n : ℕ} (hσ : Fresh σ n) (x : Fin n → Bool) (j : Fin n) :
    bits σ x (qe σ x j) = x j := by
  unfold bits
  split_ifs with h
  · rw [qe_inj hσ le_rfl x (Classical.choose h) j (Classical.choose_spec h)]
  · exact absurd ⟨j, rfl⟩ h

/-- **The fibre of an answer path is a cylinder.**  The configurations whose first `n`
answers along the plan `σ` are exactly `x` are those agreeing with `x` on the edges the plan
queries along `x`. -/
theorem fibre_eq_cylinder {n : ℕ} (hσ : Fresh σ n) (x : Fin n → Bool) :
    {ω : E → Bool | ans σ ω n = x}
      = {ω : E → Bool | ∀ e ∈ queried σ x, ω e = bits σ x e} := by
  ext ω
  change (ans σ ω n = x) ↔ (∀ e ∈ queried σ x, ω e = bits σ x e)
  rw [ans_iff]
  constructor
  · intro h e he
    obtain ⟨j, rfl⟩ := mem_queried.1 he
    rw [bits_qe hσ, h j]
  · intro h j
    rw [← bits_qe hσ x j]
    exact h _ (mem_queried.2 ⟨j, rfl⟩)


end Inst

section Mass

variable {E : Type*} [Fintype E] [DecidableEq E] {σ : QueryPlan E}

/-- The mass of a cylinder of the finite product measure. -/
theorem evProb_cylinder (J : E → ℝ) (β : ℝ) (S : Finset E) (b : E → Bool) :
    evProb J β {ω : E → Bool | ∀ e ∈ S, ω e = b e} = ∏ e ∈ S, bem J β e (b e) := by
  classical
  simp only [evProb, Set.mem_ofPred_eq, sum_confWeight_cylinder]

/-- **The mass of a fibre is the weight of its bit path.** -/
theorem fibre_mass {n : ℕ} (hσ : Fresh σ n) (J : E → ℝ) (β : ℝ) (x : Fin n → Bool) :
    evProb J β {ω : E → Bool | ans σ ω n = x} = prefMass J β σ n x := by
  classical
  rw [fibre_eq_cylinder hσ, evProb_cylinder]
  rw [prefMass, queried, prod_image (f := fun e => bem J β e (bits σ x e)) (qe_injOn hσ x)]
  exact prod_congr rfl fun j _ => by rw [bits_qe hσ]

end Mass

/-! ## The two transcript laws -/

section Chain

variable {E : Type*} {σ : QueryPlan E}

/-- The relative entropy of the `n`-step transcript law at intensity `β₂` from the one at
intensity `β₁`, computed on the answer paths. -/
noncomputable def klPath (J : E → ℝ) (β₁ β₂ : ℝ) (σ : QueryPlan E) (n : ℕ) : ℝ :=
  ∑ x : Fin n → Bool, prefMass J β₁ σ n x *
    Real.log (prefMass J β₁ σ n x / prefMass J β₂ σ n x)

/-- **One step of the relative-entropy chain rule.**  The divergence of the `(n+1)`-step
transcript laws is the divergence of the `n`-step laws plus the expected binary divergence of
the conditional law of the fresh bit; the expectation is taken over the **lower** intensity
`β₁`, and the fresh edge is the one the plan queries after the prefix.  Both conditional laws
are evaluated at the *same* prefix, which is why the outer weight is the `β₁` transcript law. -/
theorem klPath_succ {J : E → ℝ} {β₁ β₂ : ℝ} (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (n : ℕ) :
    klPath J β₁ β₂ σ (n + 1) = klPath J β₁ β₂ σ n +
      ∑ y : Fin n → Bool, prefMass J β₁ σ n y *
        bkl (bem J β₁ (σ n y) true) (bem J β₂ (σ n y) true) := by
  classical
  rw [klPath, klPath, sum_snoc (n := n), ← Finset.sum_add_distrib]
  simp only [prefMass_snoc]
  refine Finset.sum_congr rfl fun y _ => ?_
  set A := prefMass J β₁ σ n y with hA
  set B := prefMass J β₂ σ n y with hB
  have hA0 : A ≠ 0 := (prefMass_pos hJ hβ₁ n y).ne'
  have hB0 : B ≠ 0 := (prefMass_pos hJ hβ₂ n y).ne'
  have ha0 : ∀ v : Bool, bem J β₁ (σ n y) v ≠ 0 := fun v => (bem_pos hJ hβ₁ _ v).ne'
  have hb0 : ∀ v : Bool, bem J β₂ (σ n y) v ≠ 0 := fun v => (bem_pos hJ hβ₂ _ v).ne'
  have hstep : ∀ v : Bool,
      (A * bem J β₁ (σ n y) v) * Real.log ((A * bem J β₁ (σ n y) v) / (B * bem J β₂ (σ n y) v))
        = (A * bem J β₁ (σ n y) v) * Real.log (A / B)
          + A * (bem J β₁ (σ n y) v * Real.log (bem J β₁ (σ n y) v / bem J β₂ (σ n y) v)) := by
    intro v
    have hrw : (A * bem J β₁ (σ n y) v) / (B * bem J β₂ (σ n y) v)
        = (A / B) * (bem J β₁ (σ n y) v / bem J β₂ (σ n y) v) := by
      field_simp
    rw [hrw, Real.log_mul (div_ne_zero hA0 hB0) (div_ne_zero (ha0 v) (hb0 v)), mul_add]
    ring
  rw [Finset.sum_congr rfl fun v _ => hstep v, Finset.sum_add_distrib]
  have hsum1 : (∑ v : Bool, (A * bem J β₁ (σ n y) v) * Real.log (A / B))
      = A * Real.log (A / B) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, bem_sum, mul_one]
  have hsum2 : (∑ v : Bool,
      A * (bem J β₁ (σ n y) v * Real.log (bem J β₁ (σ n y) v / bem J β₂ (σ n y) v)))
      = A * bkl (bem J β₁ (σ n y) true) (bem J β₂ (σ n y) true) := by
    rw [← Finset.mul_sum, sum_bem_bkl]
  rw [hsum1, hsum2]

/-- **The relative-entropy chain rule for the transcript**, closed form: the divergence of the
`n`-step transcript laws is the sum over the steps of the expected binary divergence of the
fresh bit at that step. -/
theorem klPath_eq_sum {J : E → ℝ} {β₁ β₂ : ℝ} (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (n : ℕ) :
    klPath J β₁ β₂ σ n = ∑ i ∈ Finset.range n,
      ∑ y : Fin i → Bool, prefMass J β₁ σ i y *
        bkl (bem J β₁ (σ i y) true) (bem J β₂ (σ i y) true) := by
  induction n with
  | zero => simp [klPath, prefMass]
  | succ n ih =>
    rw [klPath_succ hJ hβ₁ hβ₂, ih, Finset.sum_range_succ]

end Chain

section ChainRev

variable {E : Type*} [DecidableEq E]

/-- **The revealment weight** of the plan at intensity `β`: the summed transcript mass of the
prefixes after which the plan queries `e`. -/
noncomputable def rev {E : Type*} [DecidableEq E] (J : E → ℝ) (β : ℝ) (σ : QueryPlan E)
    (n : ℕ) (e : E) : ℝ :=
  ∑ i ∈ Finset.range n,
    ∑ y : Fin i → Bool, if σ i y = e then prefMass J β σ i y else 0

theorem rev_nonneg {J : E → ℝ} {β : ℝ} {σ : QueryPlan E} (hJ : ∀ e, 0 < J e) (hβ : 0 < β)
    (n : ℕ) (e : E) : 0 ≤ rev J β σ n e := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun y _ => ?_
  split_ifs
  · exact (prefMass_pos hJ hβ i y).le
  · exact le_rfl

end ChainRev

section ChainFintype

variable {E : Type*} [Fintype E] [DecidableEq E] {σ : QueryPlan E}

/-- The revealment weights form a partition of the `n` queries: they sum to `n`. -/
theorem sum_rev (J : E → ℝ) (β : ℝ) (n : ℕ) :
    ∑ e, rev J β σ n e = n := by
  classical
  unfold rev
  rw [Finset.sum_comm]
  have h1 : ∀ i : ℕ, (∑ e, ∑ y : Fin i → Bool,
      if σ i y = e then prefMass J β σ i y else 0) = 1 := by
    intro i
    rw [Finset.sum_comm]
    have hpt : ∀ y : Fin i → Bool, (∑ e : E,
        if σ i y = e then prefMass J β σ i y else 0) = prefMass J β σ i y := by
      intro y
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    rw [Finset.sum_congr rfl fun y _ => hpt y, prefMass_sum]
  simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- The expected edge weight of the queried edge, as a weighted sum of the revealment
weights. -/
theorem sum_step_weight (J : E → ℝ) (β : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool, prefMass J β σ i y * J (σ i y)
      = ∑ e, J e * rev J β σ n e := by
  classical
  have hL : ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool, prefMass J β σ i y * J (σ i y)
      = ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool, ∑ e : E,
          (if σ i y = e then prefMass J β σ i y * J e else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  have hR : ∑ e, J e * rev J β σ n e
      = ∑ e : E, ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
          (if σ i y = e then prefMass J β σ i y * J e else 0) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold rev
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with h
    · ring
    · simp
  rw [hL, hR, Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]

/-- **The source's two-intensity relative-entropy bound** ([2106.06400, Theorem 3.1], entropy
step).  If every edge satisfies the per-edge exponential estimate of Lemma 3.3 — the precise
premise `bkl (1 - e^{-β₁J_e}) (1 - e^{-β₂J_e}) ≤ ((β₂-β₁)²/(2β₁)) J_e` — then the divergence
of the `n`-step transcript laws is at most `((β₂-β₁)²/(2β₁)) ∑_e J_e Rev_{β₁}(e)`, with the
revealment weights taken at the **lower** intensity `β₁`. -/
theorem kl_le {J : E → ℝ} {β₁ β₂ : ℝ} (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (hEdge : ∀ e : E, bkl (bem J β₁ e true) (bem J β₂ e true) ≤
      (β₂ - β₁) ^ 2 / (2 * β₁) * J e) (n : ℕ) :
    klPath J β₁ β₂ σ n ≤ ((β₂ - β₁) ^ 2 / (2 * β₁)) * ∑ e, J e * rev J β₁ σ n e := by
  classical
  rw [klPath_eq_sum hJ hβ₁ hβ₂]
  have hstep : ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
        prefMass J β₁ σ i y * bkl (bem J β₁ (σ i y) true) (bem J β₂ (σ i y) true)
      ≤ ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
        prefMass J β₁ σ i y * ((β₂ - β₁) ^ 2 / (2 * β₁) * J (σ i y)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun y _ => ?_
    exact mul_le_mul_of_nonneg_left (hEdge (σ i y)) (prefMass_pos hJ hβ₁ i y).le
  have hfac : ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
        prefMass J β₁ σ i y * ((β₂ - β₁) ^ 2 / (2 * β₁) * J (σ i y))
      = ((β₂ - β₁) ^ 2 / (2 * β₁)) * ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
          prefMass J β₁ σ i y * J (σ i y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  calc ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
        prefMass J β₁ σ i y * bkl (bem J β₁ (σ i y) true) (bem J β₂ (σ i y) true)
      ≤ ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
        prefMass J β₁ σ i y * ((β₂ - β₁) ^ 2 / (2 * β₁) * J (σ i y)) := hstep
    _ = ((β₂ - β₁) ^ 2 / (2 * β₁)) * ∑ i ∈ Finset.range n, ∑ y : Fin i → Bool,
          prefMass J β₁ σ i y * J (σ i y) := hfac
    _ = ((β₂ - β₁) ^ 2 / (2 * β₁)) * ∑ e, J e * rev J β₁ σ n e := by rw [sum_step_weight]

end ChainFintype

section Ratio

variable {E : Type*} {σ : QueryPlan E}

/-- The closed-edge Bernoulli weight is the exponential of minus the intensity times the edge
weight. -/
theorem bem_false (J : E → ℝ) (β : ℝ) (e : E) :
    bem J β e false = Real.exp (-(β * J e)) := by
  simp [bem, openProb]

/-- The open-edge Bernoulli weight. -/
theorem bem_true (J : E → ℝ) (β : ℝ) (e : E) :
    bem J β e true = 1 - Real.exp (-(β * J e)) := by
  simp [bem, openProb]

/-- **Two-intensity ratio at one edge, closed bit.** -/
theorem bem_div_false (J : E → ℝ) (β₁ β₂ : ℝ) (e : E) :
    bem J β₂ e false / bem J β₁ e false = Real.exp (-((β₂ - β₁) * J e)) := by
  rw [bem_false, bem_false, ← Real.exp_sub]
  ring_nf

/-- **Two-intensity ratio at one edge, open bit.** -/
theorem bem_div_true (J : E → ℝ) (β₁ β₂ : ℝ) (e : E) :
    bem J β₂ e true / bem J β₁ e true
      = (1 - Real.exp (-(β₂ * J e))) / (1 - Real.exp (-(β₁ * J e))) := by
  rw [bem_true, bem_true]

/-- An open edge is more likely at the larger intensity. -/
theorem one_le_open_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 ≤ (1 - Real.exp (-b)) / (1 - Real.exp (-a)) := by
  have hlt : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hpos : 0 < 1 - Real.exp (-a) := by linarith
  rw [le_div_iff₀ hpos]
  have hmono : Real.exp (-b) ≤ Real.exp (-a) := by
    rw [Real.exp_le_exp]; linarith
  linarith

/-- **The exact two-intensity mass ratio of a transcript fibre.**  The mass of a fibre at
intensity `β₂` is the mass at `β₁` times the product of the per-edge ratios over the revealed
edges of the fibre. -/
theorem prefMass_div {J : E → ℝ} {β₁ β₂ : ℝ} (n : ℕ) (x : Fin n → Bool) :
    prefMass J β₂ σ n x / prefMass J β₁ σ n x
      = ∏ j : Fin n, (bem J β₂ (qe σ x j) (x j) / bem J β₁ (qe σ x j) (x j)) := by
  rw [prefMass, prefMass, ← Finset.prod_div_distrib]

/-- **Per-edge one-sided bound on the two-intensity ratio**: each revealed edge contributes at
least the exponential of minus the intensity increment times its weight. -/
theorem ratio_ge {J : E → ℝ} (hJ : ∀ e, 0 < J e) {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁)
    (hβ₂ : β₁ ≤ β₂) (e : E) (v : Bool) :
    Real.exp (-((β₂ - β₁) * J e)) ≤ bem J β₂ e v / bem J β₁ e v := by
  have hJpos : 0 < J e := hJ e
  have hle : β₁ * J e ≤ β₂ * J e := by nlinarith
  cases v with
  | false => rw [bem_div_false]
  | true =>
    rw [bem_div_true]
    refine le_trans ?_ (one_le_open_div (by positivity) hle)
    rw [Real.exp_le_one_iff]
    nlinarith

/-- **The likelihood-ratio bound for a transcript fibre**: the mass of a fibre grows at least
like the exponential of minus the intensity increment times the total revealed edge weight. -/
theorem prefMass_lower {J : E → ℝ} (hJ : ∀ e, 0 < J e) {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁)
    (hβ₂ : β₁ ≤ β₂) (n : ℕ) (x : Fin n → Bool) :
    prefMass J β₁ σ n x *
        Real.exp (-((β₂ - β₁) * ∑ j : Fin n, J (qe σ x j))) ≤ prefMass J β₂ σ n x := by
  have hb1 : ∀ j : Fin n, 0 < bem J β₁ (qe σ x j) (x j) := fun j => bem_pos hJ hβ₁ _ _
  have htexp : (∏ j : Fin n, Real.exp (-((β₂ - β₁) * J (qe σ x j))))
      = Real.exp (-((β₂ - β₁) * ∑ j : Fin n, J (qe σ x j))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hprod : ∀ s : Finset (Fin n),
      (∏ j ∈ s, Real.exp (-((β₂ - β₁) * J (qe σ x j))))
        ≤ ∏ j ∈ s, (bem J β₂ (qe σ x j) (x j) / bem J β₁ (qe σ x j) (x j)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact mul_le_mul (ratio_ge hJ hβ₁ hβ₂ _ _) ih
        (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
        (le_trans (Real.exp_pos _).le (ratio_ge hJ hβ₁ hβ₂ _ _))
  have hsplit : prefMass J β₂ σ n x
      = prefMass J β₁ σ n x *
        ∏ j : Fin n, (bem J β₂ (qe σ x j) (x j) / bem J β₁ (qe σ x j) (x j)) := by
    rw [← prefMass_div]
    exact (mul_div_cancel₀ (prefMass J β₂ σ n x) (prefMass_pos hJ hβ₁ n x).ne').symm
  rw [hsplit, ← htexp]
  exact mul_le_mul_of_nonneg_left (hprod Finset.univ) (prod_pos (fun j _ => hb1 j)).le

end Ratio


section Corollaries

variable {E : Type*} {σ : QueryPlan E}

/-- The per-edge estimate in the `openProb` form of [2106.06400, Lemma 3.3] is the same
statement as its `bem` form: the one-edge open probability of the model is `1 - e^{-β J_e}`. -/
theorem bkl_openProb (J : E → ℝ) (β₁ β₂ : ℝ) (e : E) :
    bkl (bem J β₁ e true) (bem J β₂ e true)
      = bkl (openProb J β₁ e) (openProb J β₂ e) := rfl

/-- **The transcript divergence is a genuine relative entropy**: it is non-negative. -/
theorem klPath_nonneg {J : E → ℝ} {β₁ β₂ : ℝ} (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (n : ℕ) : 0 ≤ klPath J β₁ β₂ σ n := by
  have hpt : ∀ x : Fin n → Bool,
      prefMass J β₁ σ n x - prefMass J β₂ σ n x
        ≤ prefMass J β₁ σ n x *
          Real.log (prefMass J β₁ σ n x / prefMass J β₂ σ n x) := by
    intro x
    have ha : 0 < prefMass J β₁ σ n x := prefMass_pos hJ hβ₁ n x
    have hb : 0 < prefMass J β₂ σ n x := prefMass_pos hJ hβ₂ n x
    have hlog := one_sub_inv_le_log (x := prefMass J β₁ σ n x / prefMass J β₂ σ n x)
      (by positivity)
    have hmul : prefMass J β₁ σ n x *
        (1 - (prefMass J β₁ σ n x / prefMass J β₂ σ n x)⁻¹)
          = prefMass J β₁ σ n x - prefMass J β₂ σ n x := by
      field_simp
    rw [← hmul]
    exact mul_le_mul_of_nonneg_left hlog ha.le
  rw [klPath]
  have hsum :
      (∑ x : Fin n → Bool, (prefMass J β₁ σ n x - prefMass J β₂ σ n x)) = 0 := by
    rw [Finset.sum_sub_distrib, prefMass_sum, prefMass_sum, sub_self]
  calc 0 = ∑ x : Fin n → Bool, (prefMass J β₁ σ n x - prefMass J β₂ σ n x) := hsum.symm
    _ ≤ ∑ x : Fin n → Bool,
          prefMass J β₁ σ n x * Real.log (prefMass J β₁ σ n x / prefMass J β₂ σ n x) :=
        Finset.sum_le_sum fun x _ => hpt x

/-- **The per-edge premise is exactly the general Lemma 3.3.**  The hypothesis `hEdge` of
`kl_le` is the source's one-dimensional inequality at `a = β₁J_e`, `b = β₂J_e`; this records
that match, including the minimum and the `J e` factor. -/
theorem hEdge_of_lemma33 {J : E → ℝ} {β₁ β₂ : ℝ}
    (h33 : ∀ a b : ℝ, 0 < a → 0 < b →
      bkl (1 - Real.exp (-a)) (1 - Real.exp (-b)) ≤ (b - a) ^ 2 / (2 * min a b))
    (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (e : E) :
    bkl (openProb J β₁ e) (openProb J β₂ e) ≤ (β₂ - β₁) ^ 2 / (2 * β₁) * J e := by
  have hβ₂ : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ
  have ha : 0 < β₁ * J e := mul_pos hβ₁ (hJ e)
  have hb : 0 < β₂ * J e := mul_pos hβ₂ (hJ e)
  have h := h33 (β₁ * J e) (β₂ * J e) ha hb
  have hmin : min (β₁ * J e) (β₂ * J e) = β₁ * J e := by
    rw [min_eq_left (by nlinarith [hJ e, hβ₁.le, hβ])]
  rw [hmin] at h
  have hval : (β₂ * J e - β₁ * J e) ^ 2 / (2 * (β₁ * J e))
      = (β₂ - β₁) ^ 2 / (2 * β₁) * J e := by
    field_simp
  simp only [openProb]
  rw [← hval]
  exact h

end Corollaries

section CorollariesFintype

variable {E : Type*} [Fintype E] [DecidableEq E] {σ : QueryPlan E}

/-- **The two-intensity transcript entropy bound at the model's own parameters.**  This is
`kl_le` with the per-edge premise written as the source's Lemma 3.3 estimate for the weighted
model, `bkl (1 - e^{-β₁J_e}) (1 - e^{-β₂J_e}) ≤ ((β₂-β₁)²/(2β₁)) J_e`. -/
theorem kl_le_openProb {J : E → ℝ} {β₁ β₂ : ℝ} (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂)
    (hEdge : ∀ e : E, bkl (openProb J β₁ e) (openProb J β₂ e) ≤
      (β₂ - β₁) ^ 2 / (2 * β₁) * J e) (n : ℕ) :
    klPath J β₁ β₂ σ n ≤ ((β₂ - β₁) ^ 2 / (2 * β₁)) * ∑ e, J e * rev J β₁ σ n e :=
  kl_le hJ hβ₁ hβ₂ (fun e => by rw [bkl_openProb]; exact hEdge e) n


/-- **The source's constant, literally.**  With `min {β₁, β₂}` written as in [2106.06400,
Theorem 3.1], the per-edge premise is exactly Lemma 3.3 at `a = β₁J_e`, `b = β₂J_e`, and the
conclusion carries the same constant.  The case of interest for the tail comparison is
`β₂ ≥ β₁`, where the minimum is `β₁`. -/
theorem kl_le_of_le {J : E → ℝ} {β₁ β₂ : ℝ} (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂)
    (hEdge : ∀ e : E, bkl (openProb J β₁ e) (openProb J β₂ e) ≤
      (β₂ - β₁) ^ 2 / (2 * min β₁ β₂) * J e) (n : ℕ) :
    klPath J β₁ β₂ σ n ≤ ((β₂ - β₁) ^ 2 / (2 * min β₁ β₂)) * ∑ e, J e * rev J β₁ σ n e := by
  have hβ₂ : 0 < β₂ := lt_of_lt_of_le hβ₁ hβ
  have hmin : min β₁ β₂ = β₁ := min_eq_left hβ
  rw [hmin] at hEdge ⊢
  exact kl_le_openProb hJ hβ₁ hβ₂ hEdge n


/-- **The source's Theorem 3.1 entropy step, conditional on Lemma 3.3 alone.**  For a finite
weighted edge set, a query plan of depth `n`, positive edge weights and `β₂ ≥ β₁ > 0`, the
relative entropy of the two `n`-step transcript laws is at most
`((β₂ - β₁)^2 / (2β₁)) * ∑_e J_e Rev_{β₁}(e)`, granted the one-dimensional estimate
`bkl (1-e^{-a}) (1-e^{-b}) ≤ (b-a)^2/(2 min{a,b})` for `a, b > 0` — the form in which the
per-edge lemma is proved in this swarm (`LRP.bkl_one_sub_exp_le`, direction `d1`). -/
theorem kl_le_of_lemma33 {J : E → ℝ} {β₁ β₂ : ℝ}
    (h33 : ∀ a b : ℝ, 0 < a → 0 < b →
      bkl (1 - Real.exp (-a)) (1 - Real.exp (-b)) ≤ (b - a) ^ 2 / (2 * min a b))
    (hJ : ∀ e, 0 < J e) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    klPath J β₁ β₂ σ n ≤ ((β₂ - β₁) ^ 2 / (2 * β₁)) * ∑ e, J e * rev J β₁ σ n e :=
  kl_le_openProb hJ hβ₁ (lt_of_lt_of_le hβ₁ hβ)
    (fun e => hEdge_of_lemma33 h33 hJ hβ₁ hβ e) n

end CorollariesFintype

section RunConsistency

variable {E : Type*} {σ : QueryPlan E}

/-- **The prefix of an answer path is the answer path of the same run.**  This is [2106.06400,
Section 3]'s `T_n(ω) = S_n[(T_i, ω(T_i))_{i<n}]`: the edge queried at step `j` is a function
of the answers of the first `j` steps. -/
theorem pre_ans (σ : QueryPlan E) (ω : E → Bool) :
    ∀ {n : ℕ} (j : Fin n), pre (ans σ ω n) j = ans σ ω j.val := by
  intro n
  induction n with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    intro j
    cases j using Fin.lastCases with
    | last => rw [pre_last, init_ans_succ]; rfl
    | cast j' => rw [pre_castSucc, init_ans_succ]; exact ih j'

/-- The edge queried at step `j` of the run against `ω` is `qe` at the run's own answer path. -/
theorem qe_ans (σ : QueryPlan E) (ω : E → Bool) {n : ℕ} (j : Fin n) :
    qe σ (ans σ ω n) j = σ j.val (ans σ ω j.val) := by
  rw [qe, pre_ans]

/-- Distinct answer paths have disjoint fibres. -/
theorem fibre_disjoint {n : ℕ} {x x' : Fin n → Bool} (h : x ≠ x') :
    Disjoint {ω : E → Bool | ans σ ω n = x} {ω : E → Bool | ans σ ω n = x'} := by
  refine Set.disjoint_left.2 fun ω hx hx' => ?_
  exact h (hx.symm.trans hx')

/-- The answer-path fibres cover the configuration space. -/
theorem iUnion_fibre {n : ℕ} :
    (⋃ x : Fin n → Bool, {ω : E → Bool | ans σ ω n = x}) = Set.univ := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨ans σ ω n, rfl⟩

end RunConsistency

section TranscriptLaw

variable {E : Type*} [Fintype E] [DecidableEq E] {σ : QueryPlan E}

/-- **The transcript is a probability measure**: the fibre masses sum to one. -/
theorem sum_fibre_mass {n : ℕ} (hσ : Fresh σ n) (J : E → ℝ) (β : ℝ) :
    ∑ x : Fin n → Bool, evProb J β {ω : E → Bool | ans σ ω n = x} = 1 := by
  simp only [fibre_mass hσ]
  exact prefMass_sum J β σ n

/-- **The transcript divergence is the relative entropy of the fibre masses of the model
measure.**  This is the sense in which `klPath` is the relative entropy of the two transcript
laws: it is computed from the masses `evProb` of the answer-path fibres. -/
theorem klPath_eq_fibre_kl {n : ℕ} (hσ : Fresh σ n) (J : E → ℝ) (β₁ β₂ : ℝ) :
    klPath J β₁ β₂ σ n = ∑ x : Fin n → Bool,
      evProb J β₁ {ω : E → Bool | ans σ ω n = x} *
        Real.log (evProb J β₁ {ω : E → Bool | ans σ ω n = x}
          / evProb J β₂ {ω : E → Bool | ans σ ω n = x}) := by
  simp only [klPath, fibre_mass hσ]

end TranscriptLaw

section Examples

/-- The plan on the two-edge set `Fin 2` that queries edge `0` first and edge `1` second. -/
def twoPlan : QueryPlan (Fin 2) := fun n _ => ⟨n % 2, Nat.mod_lt n (by norm_num)⟩

/-- **Non-vacuity of the freshness hypothesis.**  `twoPlan` never repeats an edge among its
first two queries, so `Fresh` is satisfiable at the depths at which the fibre formula is used. -/
theorem example_fresh : Fresh twoPlan 2 := by
  intro n hn y j
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · exact j.elim0
  · have hj : (j : ℕ) = 0 := by omega
    have hqe : qe twoPlan y j = (⟨0, by norm_num⟩ : Fin 2) := by
      simp only [qe, twoPlan, hj]
    intro h
    rw [hqe] at h
    simp only [twoPlan] at h
    exact absurd h (by decide)

/-- **Non-vacuity of the fibre formula.**  On `Fin 2` with the fresh plan `twoPlan`, the mass of
a one-step answer path is the corresponding one-edge Bernoulli weight. -/
theorem example_fibre_mass_two (J : Fin 2 → ℝ) (β : ℝ) (x : Fin 1 → Bool) :
    evProb J β {ω : Fin 2 → Bool | ans twoPlan ω 1 = x}
      = ∏ j : Fin 1, bem J β (qe twoPlan x j) (x j) :=
  fibre_mass (Fresh.mono example_fresh (by norm_num)) J β x

end Examples

end LRP

namespace LRP

set_option linter.hashCommand false in
#print axioms LRP.fibre_eq_cylinder

set_option linter.hashCommand false in
#print axioms LRP.fibre_mass

set_option linter.hashCommand false in
#print axioms LRP.pre_ans

set_option linter.hashCommand false in
#print axioms LRP.sum_fibre_mass

set_option linter.hashCommand false in
#print axioms LRP.klPath_eq_fibre_kl

set_option linter.hashCommand false in
#print axioms LRP.prefMass_sum

set_option linter.hashCommand false in
#print axioms LRP.prefMass_div

set_option linter.hashCommand false in
#print axioms LRP.prefMass_lower

set_option linter.hashCommand false in
#print axioms LRP.klPath_succ

set_option linter.hashCommand false in
#print axioms LRP.klPath_eq_sum

set_option linter.hashCommand false in
#print axioms LRP.sum_rev

set_option linter.hashCommand false in
#print axioms LRP.sum_step_weight

set_option linter.hashCommand false in
#print axioms LRP.kl_le

set_option linter.hashCommand false in
#print axioms LRP.kl_le_openProb

set_option linter.hashCommand false in
#print axioms LRP.kl_le_of_le

set_option linter.hashCommand false in
#print axioms LRP.hEdge_of_lemma33

set_option linter.hashCommand false in
#print axioms LRP.kl_le_of_lemma33

set_option linter.hashCommand false in
#print axioms LRP.klPath_nonneg

set_option linter.hashCommand false in
#print axioms LRP.example_fresh

set_option linter.hashCommand false in
#print axioms LRP.example_fibre_mass_two

end LRP
