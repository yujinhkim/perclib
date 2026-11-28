# Cited literature inputs

This file records literature results explicitly assumed by completed modules in
this continuation. An input is never an `axiom`; it is a property in the Lean
signature of each theorem using it. These inputs do not count as proved source
results.

## `Correlation.Gladkov.GladkovInput`

- **Result:** the three-point Gladkov inequality, Theorem I.2.7 on supplied
  PDF page 24 of Hutchcroft, *Critical long-range percolation I: High effective
  dimension*.
- **Primary source for the result and proof:** Nikita Gladkov,
  *Percolation Inequalities and Decision Trees*, [arXiv:2408.08457v2](https://arxiv.org/abs/2408.08457v2),
  Theorem 6.2 (finite graph implementation, then the infinity limit). License:
  CC BY 4.0.
- **Lean declaration:** `PercLib/CriticalLRP/Correlation/Gladkov/Defs.lean`,
  field `three_point_sq_le`. For all `y,z`, it states that

  ```text
  law π (conn x y ∩ conn x z)^2 ≤
      8 * law π (conn x y) * law π (conn y z) * law π (conn z x).
  ```

  The `^2` applies only to the joint three-point probability. `x` is universally
  quantified in the structure's parameters, so permutations of any intended
  triple can be instantiated.
- **Reason for inclusion:** the user explicitly permitted assuming Gladkov's
  inequality for now.
- **Non-vacuity:** the same file has a compiling singleton-vertex witness,
  including the proof that self-connection has measure one.
- **Still owed:** a proof of this input on the source's arbitrary weighted
  graphs. No decision-tree FKG/BK or DFS proof is claimed. In particular,
  I.2.7 is not thereby formalized as a proved theorem.
- **Consumers:** `mixed_moment_le_of_gladkov` and
  `mixed_moment_le_of_gladkov_cutoff`. These prove conditional I.2.8, not an
  unconditional four-point or higher-k Gladkov-type result.


## `Orchestration.SourceModelData.CriticalVolumeTail`

- **Result:** the uncut critical cluster-volume tail bound
  `P_{β_c}(|K_0| ≥ n) ≤ C n⁻¹ᐟ²` for every `n ≥ 1`, at the infinite-lattice law
  rather than a cutoff or finite-volume substitute.
- **Primary source cited by the supplied paper:** D. J. Barsky and M. Aizenman,
  *Percolation critical exponents under the triangle condition*, Annals of
  Probability 19(4), 1520–1536 (1991); and T. Hutchcroft, *On the derivation
  of mean-field percolation critical exponents from the triangle condition*,
  Journal of Statistical Physics 189(1), article 6 (2022). These are references
  [12] and [75] of the supplied PDF and are cited at p. 47 in its proof of
  Proposition I.4.15, Case 3. Their proofs have not been formalized here.
- **Lean declaration:** `PercLib/CriticalLRP/Analysis/SecondMomentCase3/
  CriticalVolumeTail/Defs.lean`. `CriticalVolumeTail M C` remains an explicit
  hypothesis of the conditional consumers in `Main.lean`; there is no theorem
  producing it from cutoff monotonicity, a finite moment or a triangle tail.
- **Use:** derive the one-sided moment gap with explicit constant and conditional
  Case-3 assemblies. The separate implication from a critical-volume-tail
  asymptotic retains that asymptotic as its premise and imports no frozen sorry
  draft. No non-vacuous canonical-model instantiation of this input is claimed.
